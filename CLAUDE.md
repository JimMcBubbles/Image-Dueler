# Image Duel Ranker — Claude context

## Project shape
- **Single file:** `image_duel_ranker.py` (~6100 lines). All edits go here directly.
- **No worktrees.** User runs the script live; always edit the main working directory.
- **DB:** `.image_ranking.sqlite` (SQLite, same dir as script) — **the only source of truth.**
- **Sidecars:** `.image_duel_sidecars/<filename>.json` — derived per-file score export written async;
  fully regenerable from `images.score` (`--regen-sidecars` / `regenerate_all_sidecars`).
- **Git hygiene:** the DB, sidecars, `backups/`, `__pycache__/`, the bundled python installer,
  `image_duel_report.csv` and the stray `py` file are **git-ignored** (see `.gitignore`). Only code
  is tracked. Rollback/undo is handled in-app (sessions/snapshots), **not** by committing data.
- **CLI:** `python image_duel_ranker.py --backup` (VACUUM INTO `backups/`, rotate) and
  `--regen-sidecars` (rebuild every sidecar from the DB); no args → normal GUI.

## Key constants (top of file)
| Name | Value |
|------|-------|
| `BASE_SCORE` | 1000.0 |
| `K_FACTOR` | 32.0 — Elo K (used by `elo_update`; rollback math relies on stored before/after, not recomputation) |
| `DOWNVOTE_PENALTY` | 12.0 |
| `SESSION_GAP_SECONDS` | 1800 — >30 min between consecutive comparisons starts a new session (backfill grouping) |
| `SNAPSHOT_SCHEMA_VERSION` | 1 — bump if `snapshots.payload` JSON format changes |
| `BACKUP_DIR` | `<script>/backups` — VACUUM-INTO target for `--backup` (git-ignored) |
| `BACKUP_KEEP` | 20 — rotated backups retained by `backup_db` |
| `DB_PREHISTORY_BAK` | `.image_ranking.sqlite.prehistory.bak` — one-time pre-migration copy |
| `TAG_OPTIONS` | `["SFW","MEME","HIDE","CW","FAVORITE"]` — mutable list; custom tags appended at runtime |
| `BLUR_TAGS` | `{"CW","HIDE"}` — tags whose carousel thumbnails are blurred until that duel is selected |
| `FAVORITE_TAG` / `NON_MATCH_TAGS` | `"FAVORITE"` / `{"FAVORITE"}` — marker tag toggled by the heart button; **excluded from duel matchmaking** (`_match_tags`) so favoriting never changes who an image duels |
| `FAVORITE_COLOR` | `#e25555` — heart color when an image is favorited |
| `carousel_size` | 6 slots |
| `ACCENT` / `PENDING_COLOR` / `FUTURE_COLOR` | blue / amber / dark-teal |
| `LOAD_TIMEOUT_MS` | 8000 — ms before showing Retry/Open-File overlay on a slow load |
| `DISLIKE_RATE_PENALTY` | 300.0 — multiplied by `dislikes_n / (n + FOLDER_PRIOR_IMAGES)`; rate-based dislike penalty |
| `VOLUME_BONUS` | 50.0 — max bonus for large like-count; scaled by `n/(n+FOLDER_PRIOR_IMAGES)` |
| `SPARKLINE_WINDOW_DEFAULT` | 60 — default rolling comparisons window for sparklines |
| `SPARKLINE_WINDOWS` | `(20, 40, 60, 100, 200)` — cycle targets for "W: N" button |
| `SPARKLINE_BUCKETS` | 7 — number of segments per sparkline |

## DB schema
```
images(id, path, folder, score, wins, losses, duels, last_seen, hidden, artist, tags)
comparisons(id, left_id, right_id, chosen_id, ts,
            outcome, left_score_before, right_score_before,
            left_score_after, right_score_after, session_id, active)
sessions(id, started_ts, ended_ts, label, start_comparison_id, note)
snapshots(id, ts, label, kind, session_id, max_comparison_id, payload)
```
- `images` also has an `artist` column on disk; the **in-app row tuple is a fixed projection**, NOT
  `SELECT *`. Row tuple indices: `(0=id, 1=path, 2=folder, 3=duels, 4=wins, 5=losses, 6=score, 7=hidden, 8=tags)`.
- **Ties/downvotes are RETIRED** (feature removed): new duels only ever record `left`/`right`. A skip
  (right-click, `7`/`8`, or `0`) never touches scores — it just advances. Existing `tie`/`downvote`
  rows were archived (`active=0`) by `retire_tie_downvote_once` and no longer affect scores. The
  `outcome`/`_outcome_*`/`record_result` code still *understands* tie/downvote for displaying archived
  rows, but no UI path creates them. `DOWNVOTE_PENALTY` is now legacy (historical replay only).
- `comparisons.outcome` ∈ `left|right|tie|downvote` (`tie`/`downvote` only on archived legacy rows now;
  exact, replay-complete; `a`=left, `b`=right).
  before/after scores are stored per duel so any new duel reverses exactly. `active` (default 1) flags
  a duel live; rollbacks set it 0 (**never DELETE**). `session_id` stamps the owning session.
  **Legacy ambiguity:** old rows wrote `chosen_id=NULL` for BOTH tie AND downvote → backfilled as `tie`,
  and their before/after are NULL (so they are not `undo_last`-reversible — only snapshot-restorable).
- `snapshots.kind` ∈ `baseline|auto|manual|pre-rollback`. `payload` = compact JSON
  `{"v":1,"rows":[[id,score,wins,losses,duels],…]}` of **all** images (score state only — tags/hidden/artist
  are NOT rolled back). `max_comparison_id` = highest comparison id at snapshot time.

## Core state (App instance)
```python
self.current          # (row_a, row_b) being displayed right now
self.live_current     # (row_a, row_b) of the active live duel (preserved during edit mode)
self.duel_history     # List[dict] — past voted duels
self.history_index    # None = live mode; int = edit/history mode
self.future_queue     # List[{"a":row,"b":row,"thumb":None}] — pre-rolled upcoming duels
self._missing_ids     # set[int] — image ids whose file is gone from disk; excluded by _pool_rows
self.session_id       # int | None — current live session; stamps every new comparison
self._session_closed  # bool — guards _close_session against double-stamping ended_ts
self._hm_win          # Toplevel | None — History/Rollback manager window (singleton)
self._sd_win          # Toplevel | None — Session drill-in window (singleton)
self._sd_rows         # List[dict] — one per duel row in the open drill-in (cid/ids/paths/scores/widgets)
self._sd_selected_cid # int | None — comparison id selected in the drill-in editor
self._sd_cancel       # threading.Event — set on drill-in close to stop thumbnail workers
```

## duel_history entry shape
```python
{
  "comparison_id": int | None,   # None = sub-duel not yet voted
  "a_id", "b_id": int,
  "a_path", "b_path": str,
  "before_a", "before_b": {"score","wins","losses","duels"},  # snapshot at duel time
  "winner": "a"|"b"|"downvote"|None,
  "sub_label": str | None,       # e.g. "10.1" for sub-duels; None for normal
  "thumb": ImageTk.PhotoImage | None,
}
```

## Important methods & line numbers (approximate — verify with Read before editing)
> Note: many older entries below have drifted; the file is now ~6100 lines. Verify with Read.

### History / sessions / snapshots / rollback / backups (module-level)
| Function | ~Line | Purpose |
|----------|-------|---------|
| `migrate_schema` | 176 | Idempotent migration: one-time `.bak`, adds comparisons columns (outcome/before/after/session_id/active), backfills outcome (NULL→tie) + active, creates `sessions`/`snapshots`, backfills sessions by ts gap, takes a one-time `baseline` snapshot |
| `record_result` | 594 | Now takes `session_id=`; writes outcome + before/after scores + session_id + active=1 |
| `_backup_db_once` | 669 | One-time file copy of the DB → `DB_PREHISTORY_BAK` before first migration (idempotent) |
| `_backfill_sessions` | 679 | Groups existing comparisons into sessions by `SESSION_GAP_SECONDS`; stamps `session_id` |
| `_images_state_payload` | 713 | Compact JSON of all images' (id,score,wins,losses,duels) |
| `_take_snapshot` | 723 | Inserts a snapshot row (kind/label/session_id/max_comparison_id/payload); returns id |
| `_restore_images_from_payload` | 740 | Writes a snapshot payload back into images (score/wins/losses/duels only) |
| `regenerate_all_sidecars` | 752 | Rebuild every sidecar JSON from images.score (bulk; `--regen-sidecars`) |
| `backup_db` | 771 | `VACUUM INTO backups/image_ranking_<UTCts>.sqlite` + rotate to last `keep` |
| `undo_last_comparisons` | 797 | Reverse last n active **fully-logged** comparisons via stored before-scores+outcome; pre-rollback snapshot first; flips `active=0` (exact, O(n)) |
| `restore_snapshot_db` | 840 | Restore a snapshot payload; recompute `active = id<=max_comparison_id`; pre-rollback snapshot first |
| `_session_start_snapshot_id` | 858 | Earliest auto/baseline/manual snapshot for a session (its start point) |
| `rollback_to_session_db` | 869 | Maps session start/end → snapshot, then `restore_snapshot_db` (end = next session's start snapshot) |
| `_outcome_increments` | 913 | (left_w,left_l,right_w,right_l) win/loss increments implied by an outcome |
| `_outcome_after_scores` | 921 | After-scores both sides would have from given before-scores + outcome |
| `_fetch_editable_comparison` | 929 | Loads a comparison row; rejects legacy (NULL before/after) duels |
| `revote_comparison_db` | 942 | Change ONE duel's outcome via **delta** on current scores (works mid-history; never touches `duels`) |
| `undo_comparison_db` | 970 | Remove one duel's (after−before) delta, decrement duels, undo W/L, `active=0` |
| `restore_comparison_db` | 991 | Inverse of `undo_comparison_db`: re-apply delta, re-increment, `active=1` |
| `rebuild_scores_from_log` | 1012 | Replay all active duels (ts,id order) from BASE_SCORE; recompute images + **backfill before/after on every duel** (unlocks legacy editing); keeps `ts`; `dry_run` returns drift stats; optional `recall_map` overrides outcomes |
| `retire_tie_downvote_once` | 1076 | One-time (called from `init_db` after `migrate_schema`): if any active tie/downvote duels exist → `backup_db` + pre-rollback snapshot + archive them (`active=0`) + `rebuild_scores_from_log`. Self-guarding no-op once none remain |

### App methods
| Method | ~Line | Purpose |
|--------|-------|---------|
| `_apply_revote` | 1870 | Edits existing vote — delta wins/losses only, **no duels increment**; now also updates comparisons `outcome`+after-scores (before-scores stay fixed) |
| `choose` | 3349 | Vote handler — `a`/`b` → `record_result` (session-stamped); **any non-`a`/`b` (skip) does nothing to score, just advances** (live) / steps to next entry (edit mode) |
| `downvote_side` | 3515 | **Retired** — neutered to a no-score skip (`_replace_side_keep_other`); no keybind/button/menu calls it anymore |
| `_open_session` | 5671 | Inserts live session row + takes an `auto` start snapshot (called in `__init__` before `load_duel`) |
| `_close_session` | 5690 | Stamps `ended_ts` (idempotent); called from `quit()` |
| `undo_last` | 5706 | Wraps `undo_last_comparisons` + UI refresh + async sidecar rewrite for affected images |
| `restore_snapshot` | 5721 | Wraps `restore_snapshot_db` + UI refresh |
| `rollback_to_session` | 5728 | Wraps `rollback_to_session_db` + UI refresh |
| `rebuild_from_log` | 5904 | Pre-rollback snapshot → `rebuild_scores_from_log` → UI refresh |
| `_hm_rebuild` | 6122 | "Rebuild from log…" handler: dry-run preview in a confirm dialog, then apply |
| `_reload_after_rollback` | 5735 | Drops volatile in-memory duel state (history/future/solo), recomputes ranks, reloads live duel + sidebar |
| `_regen_sidecars_async` | 5759 | Background `regenerate_all_sidecars` (own connection) with status callback |
| `show_history_manager` | 5882 | Toplevel UI: stats, Undo-last-N, Take snapshot, Backup, Regen sidecars, sessions+snapshots lists w/ rollback buttons + "Open / edit duels" (key `h`, sidebar button, context menu). Double-click a session → drill-in |
| `_hm_refresh` / `_hm_*` | 5969 | Manager refresh + button handlers (confirm dialogs before destructive ops) |
| `_hm_open_session_detail` | 6092 | Opens the drill-in for the selected session |
| `show_session_detail` | 6105 | **Drill-in window**: scrollable list of a session's duels (thumbnail every row, async bounded pool) + per-duel editor panel |
| `_sd_build_rows` / `_sd_select` / `_sd_render_editor` / `_sd_build_tag_editor` | 6192 | Build rows from a session-scoped JOIN; select highlights + populates the editor; per-side tag checkbuttons + Hidden + Save/Open |
| `_sd_revote` / `_sd_undo` / `_sd_restore` | 6340 | UI handlers → `revote/undo/restore_comparison_db`; lazy pre-edit snapshot once per drill-in; refresh row + editor |
| `_sd_save_tags` | 6389 | Writes tags via `_write_tags`; refreshes affected rows + live tag controls |
| `_refresh_live_scores_after_edit` | 6426 | Re-fetches on-screen duel rows + leaderboard after a historical edit |
| `_sd_start_thumb_workers` / `_sd_apply_thumb` | 6444 | Bounded (4) worker pool building `_build_duel_thumbnail` per row; posts via `root.after`; stops on the window's cancel `Event` |
| `_open_path` | 6099 | `os.startfile` a path (drill-in "Open" buttons) |
| `show_db_stats` | 5983 | Now also shows active/archived comparison counts, session/snapshot counts, live session id |
| `quit` | 6043 | Now calls `_close_session()` before closing conn; also bound to `WM_DELETE_WINDOW` |

### Older entries (line numbers drifted — verify before editing)
| Method | ~Line | Purpose |
|--------|-------|---------|
| `_create_history_sub_duel` | 1327 | Tag change in edit mode → nullify vote, roll replacement, insert sub-entry |
| `_create_live_sub_duel` | 2530 | Tag change in live mode → replace slot with fresh pick, queue sub-duel for tagged image next in future_queue |
| `_entry_is_sensitive` | 1209 | True if entry's stored a_tags/b_tags intersect BLUR_TAGS |
| `_pair_is_sensitive` | 1214 | True if either row's tags intersect BLUR_TAGS |
| `_entry_sensitive_label` | 1219 | "TAG, TAG" label for blurred history carousel slots |
| `_pair_sensitive_label` | 1226 | "TAG, TAG" label for blurred future/live carousel slots |
| `_tag_usage_counts` | 1233 | Returns {tag: image_count} for all images; used to sort tag menus by usage |
| `_match_tags` | 2841 | Matchmaking tag set: `frozenset(_tags_for_row(row)) - NON_MATCH_TAGS` (strips FAVORITE) |
| `toggle_favorite` | 2869 | Heart-button handler: toggles FAVORITE on the displayed image (no vote, no reroll) |
| `_update_favorite_button` | 2896 | Sets the heart glyph/color (♥ red if favorited, ♡ otherwise); called from `_sync_tag_controls` |
| `_build_action_buttons` | 2765 | Per-side action row: **heart (Favorite)** + Skip + Hide (Upvote/Downvote removed) |
| `_attach_history_thumbs` | 1242 | Builds entry["thumb"]; also builds entry["thumb_blurred"] for sensitive entries |
| `_enter_history_mode` | 1255 | Save live_current, set history_index, show entry |
| `_exit_history_mode` | 1261 | Restore live_current display, clear history_index |
| `_update_carousel` | 1472 | Full carousel repaint — live/edit/future branches |
| `_rebuild_all_tag_menus` | 1637 | Re-sync tag_vars/labels after TAG_OPTIONS changes; rebuilds filter tk.Menu; sorts by usage |
| `_show_custom_tag_menu` | 1662 | Custom overrideredirect popup mimicking tk.Menu; handles toggle + inline edit mode with text field, pending removes/adds, Save, click-outside save prompt; sorts by usage |
| `_fill_future_queue` | 2006 | Top up future_queue to target size via pick_two |
| `_jump_to_future` | 2029 | Skip live+futures[0..i-1], make future[i] the new live duel |
| `pick_two` | 2079 | Groups pool by (frozenset(tags), media_kind); picks two from same group |
| `pick_one` | 2048 | Hard-filters by required_kind + required_tags (exact frozenset match) |
| `load_duel` | 2108 | Pops future_queue[0] or pick_two, sets live, calls _fill_future_queue |
| `choose` | 2136 | Vote handler — edit mode: _apply_revote or record_result; live: record + load_duel |
| `_dismiss_load_timeout` | 2628 | Cancels pending timeout job + destroys overlay for a side |
| `_show_load_timeout` | 2643 | Creates centered overlay on container with Retry + Open-File buttons |
| `_render_image_or_gif` | 3157 | Async image/GIF render — shows "Loading…", starts load_worker thread, schedules 8 s timeout. Timeout now stays armed **through** GIF frame decode (dismissed in `_decode_gif_async`). On a missing-file open error calls `_handle_missing_side` instead of just printing "Failed to load". **Sets `st["last_visual_size"]=(w,h)` up-front** (at render-commit, not decode-completion) so resize/`<Configure>` ticks arriving mid-GIF-decode hit `_refresh_visuals_only`'s size guard and skip — prevents the "Loading…"/"Loading GIF…" flicker loop |
| `_decode_gif_async` | 3269 | Spawns decode_worker thread for GIF frame extraction; `apply_result` dismisses the load-timeout left armed by `_render_image_or_gif` |
| `_pool_rows` | 2552 | Builds the duel pool from DB; **excludes `self._missing_ids`** so deleted/moved files are never picked; applies pool filter |
| `_start_missing_scan` | 2565 | Daemon-thread launcher: runs `audit_file_availability(DB_PATH)`, posts result to `_apply_missing_scan` via root.after. Called at end of `__init__` |
| `_apply_missing_scan` | 2577 | Main-thread: sets `self._missing_ids`, purges missing-referencing entries from `future_queue`, reloads the live duel if it references a missing file |
| `_handle_missing_side` | 2945 | Render-time miss: adds the row id to `_missing_ids`; live mode → `_replace_side_keep_other` (auto-skip); history/solo → shows "File not found (removed from rotation)" |
| `_ffmpeg_exe` | 3803 | Returns ffmpeg path (cached after first call) via imageio-ffmpeg or PATH |
| `_cleanup_waveform_cache` | 3824 | Removes wave PNGs older than 7 days from temp dir; runs once per session on background thread |
| `_maybe_request_waveform` | 3839 | Launches background waveform generation for current media; guards against duplicate jobs per key |
| `_waveform_worker` | 3887 | ffmpeg showwavespic → tinted PIL image; posts result back via root.after |
| `_redraw_waveform_debounced` | 4000 | Debounces `_redraw_waveform` calls (40 ms) to prevent main-thread thrash on window resize |
| `_redraw_waveform` | 4010 | Scales waveform source image to canvas size and draws playhead |
| `_update_playhead` | 4051 | Draws YouTube-style progress track + playhead line on the wave canvas |
| `toggle_sparklines` | ~4238 | Toggles sparkline mode on/off, updates button label/color, refreshes sidebar |
| `cycle_sparkline_window` | ~4246 | Cycles sparkline_window through SPARKLINE_WINDOWS; refreshes sidebar if sparklines on |

## Carousel slot map encoding
`_carousel_slot_map[i]` stores:
- `int >= 0` → history index (click → edit mode)
- `"live"` → live current slot
- `("future", i)` → future_queue[i] (click → _jump_to_future)
- `None` → empty/disabled

## Tag matching rule
Tagged images **only** duel images with the **exact same tag set** (frozenset equality).
Untagged (empty set) images only duel other untagged images. No cross-group fallback.
**Matchmaking uses `_match_tags(row)` = `frozenset(_tags_for_row(row)) - NON_MATCH_TAGS`** — i.e. the
`FAVORITE` marker is stripped before grouping, so favoriting never moves an image between duel groups.
All matchmaking sites (`pick_one`/`pick_two`/sub-duel rerolls) call `_match_tags`, NOT raw `_tags_for_row`.

## Favorite (heart button — replaces "Upvote")
- The per-side action row shows **♡/♥** (`_build_action_buttons`); clicking → `toggle_favorite(side)`
  toggles the `FAVORITE` tag on the displayed image via `_write_tags` (filled red `♥` when set,
  via `_update_favorite_button`, refreshed in `_sync_tag_controls`).
- Favoriting is **not a vote**: no score/duel/win/loss change, and it **does not reroll** the duel
  (`_on_tag_change` short-circuits when the symmetric tag diff ⊆ `NON_MATCH_TAGS`). Winner-picking is
  unchanged (click image / keys `1`/`2`). The right-click menu's "Upvote" item was removed.
- `FAVORITE` is a normal tag elsewhere (tag menu, filters, drill-in editor) — only matchmaking ignores it.

## Revote rule
`_apply_revote` must **never** increment `duels`. It computes delta wins/losses between
old winner and new winner and applies only the difference. Scores are recalculated from
`before_a/before_b` snapshots.

## Sub-duel rule
When tags change in edit mode: parent vote → None (tie), tagged slot gets a fresh pick,
sub-duel entry inserted after parent with `sub_label="N.1"`, `comparison_id=None`.
Carousel highlights sub-duel amber until voted. View stays on parent duel.

## History / rollback model (in-app session rollback — replaces "commit data to git")
- **Source of truth = `images` table.** New duels are fully logged (`outcome` + before/after scores
  + `session_id` + `active`) so they reverse exactly. Snapshots capture the whole images scoring
  state; rollbacks restore a snapshot and flip `active` — **nothing is ever DELETEd**.
- **Session lifecycle:** `_open_session()` (in `__init__`) inserts a `live` session row and takes an
  `auto` start-of-session snapshot; `quit()` calls `_close_session()` (stamps `ended_ts`). `quit` is
  also wired to `WM_DELETE_WINDOW` so the X button closes the session too.
- **`undo_last(n)`** — exact O(n) reversal of the last n active, fully-logged duels using stored
  before-scores + outcome (restore both scores, `duels-1`, undo win/loss), then `active=0`. Skips
  legacy rows (NULL before-scores). Assumes the last n active rows are contiguous (normal flow).
- **`restore_snapshot(id)` / `rollback_to_session(id, where)`** — restore a snapshot's payload into
  images, then recompute `active = (id <= snapshot.max_comparison_id)`. `where='start'` → that
  session's start snapshot; `where='end'` → the next session's start snapshot.
- **Every rollback is itself undoable:** each takes a `pre-rollback` snapshot first, so restoring
  that snapshot reverts the rollback exactly. (Acceptance-tested: undo→re-vote reproduces identical
  scores; session rollback restores prior scores and is reversible.)
- **Migration safety net:** `migrate_schema` copies the DB to `*.prehistory.bak` once and takes a
  one-time `baseline` snapshot before the first feature run; both are idempotent.
- **Known approximation:** the `active` flag is a best-effort log marker (recomputed from
  `max_comparison_id` on snapshot restore). `images` is always exact; legacy tie/downvote rows are
  indistinguishable (backfilled as `tie`). `folder_sparkline` does **not** filter on `active` (by design).

## Session drill-in (edit/undo individual duels + tags)
- Open from the History/Rollback window: select a session → **"Open / edit duels"** or double-click it
  → `show_session_detail(session_id)`. Singleton window (`self._sd_win`); a thumbnail is built for
  **every** row by a bounded (4) background worker pool, posted via `root.after`.
- **Per-duel edits use DELTA math** (`revote/undo/restore_comparison_db`): `score += new_after −
  old_after` (revote) or `score −= after − before` (undo). This is correct for a duel **anywhere** in
  history without re-cascading later duels — the same non-cascading approximation as `_apply_revote`.
  Re-vote **never** changes `duels`; undo decrements it and `restore` re-increments it.
- **Only fully-logged duels are editable.** Legacy (pre-migration) duels have NULL before/after and
  are shown view-only; use snapshot/session rollback for those.
- **Undoability:** the first score-affecting edit in a drill-in lazily takes one `pre-rollback`
  snapshot (`before editing session #N`); individual re-votes are also reversible by re-voting. Undo
  flags `active=0` (never DELETE); **Restore** re-activates and re-applies the delta.
- **Tags** edited here call `_write_tags` on the image's **current global state** (not time-versioned)
  and are **not** captured by the pre-edit snapshot — "undo" a tag = toggle it back.

## Rebuild scores from log (unlock legacy duels for editing)
- **"Rebuild from log…"** in the History/Rollback window (`rebuild_scores_from_log` / App `rebuild_from_log`)
  replays every **active** comparison in `(ts, id)` order from `BASE_SCORE`, recomputes
  `images.score/wins/losses/duels`, and **writes before/after into every comparison row** — so all
  3594 legacy duels become individually editable (re-vote = "recall" them). Original `ts` is kept.
- **Honest tradeoff:** the ~391 unknown legacy tie/downvote duels replay as **ties**, discarding the
  real (unrecoverable) downvote penalties currently baked into scores. On this DB the drift is small
  (~3% of images move >1 pt; mean ~0.4 pt). The handler shows a **dry-run preview** (drift stats) in a
  confirm dialog before applying, takes a `pre-rollback` snapshot first (reversible), and is
  **idempotent** (re-running with the same outcomes changes nothing).
- After a rebuild, "recall a vote" = just re-vote that duel in the drill-in (now fully-logged → exact
  delta edit). `recall_map={cid: outcome}` can pre-seed specific outcomes into the replay.

## Ties/downvotes retired (one-time purge + feature removal)
- **Feature removed:** no keybind/click/button/menu creates a tie or downvote. `4`/`5` and Shift-click
  (downvote) and the Downvote button/menu item are gone; `choose(None)` / `0` and `skip_side` are
  score-neutral skips; the drill-in re-vote offers only Left/Right. `record_result`/`_apply_revote`/
  `_outcome_*` keep tie/downvote branches but they're unreachable (only `a`/`b` is ever passed).
- **One-time data purge:** `retire_tie_downvote_once(conn)` (called from `init_db` after migration)
  backs up the DB (`backup_db`), takes a `pre-rollback` snapshot, archives every active tie/downvote
  comparison (`active=0`, never DELETE), and `rebuild_scores_from_log` → scores reflect decisive duels
  only. On this DB it moved ~277 images >1 pt (max ~26.5, leaderboard barely changes) and is reversible.
  Self-guarding: a permanent no-op once no active tie/downvote rows remain.
- **Note:** old `downvote_side` deducted −12 **without logging**, so the rebuild (log-driven) also drops
  those unlogged penalties. Archived tie/downvote rows still show in the drill-in as `[undone]`.

## Async patterns
- Sidecar writes: daemon thread via `update_image_metadata`
- Thumbnail builds: daemon thread → `root.after(0, _update_carousel)` on completion
- Video snapshot polling: daemon thread
- GIF decode: daemon thread via `_decode_gif_async`
- Static image open+thumbnail: daemon thread via `load_worker` inside `_render_image_or_gif`; 8 s timeout shows Retry/Open-File overlay (timeout now spans GIF frame decode too)
- Missing-file scan: daemon thread via `_start_missing_scan` → `audit_file_availability` → `root.after(0, _apply_missing_scan)`
- Bulk sidecar regen: daemon thread via `_regen_sidecars_async` (own sqlite connection; posts status via `root.after`)

## Backups & off-machine copies
- `backup_db()` does `VACUUM INTO backups/image_ranking_<UTCts>.sqlite` and rotates to the last
  `BACKUP_KEEP`. Run via `python image_duel_ranker.py --backup` or the History/Rollback window.
- `backups/` is git-ignored; point **restic / kopia / OneDrive** at it for off-machine copies.

## Diagnostics & logging (load/file-not-found troubleshooting)
- **`describe_file_state(path)`** (module-level, ~line 185): OneDrive-aware probe. Uses
  `os.stat` (metadata only — never hydrates a placeholder) to return `present (local)`,
  `ONLINE-ONLY (OneDrive placeholder…)`, `offline`, or `MISSING`. Reused by all the log sites.
- **`audit_file_availability(db_path)`** (module-level, ~line 213): one-shot audit launched on a
  daemon thread by the App's `_start_missing_scan` (own sqlite connection — App conn is
  main-thread-bound). Reads all non-hidden `(id, path)`, classifies each, prints an `[audit]`
  summary (local / online-only / MISSING / stat-error counts + example paths), and **returns the
  set of MISSING image ids** (fed into `self._missing_ids`). Safe to call standalone:
  `python -c "import image_duel_ranker as m; m.audit_file_availability(m.DB_PATH)"`.
- **Missing-file skipping**: `_pool_rows` excludes `self._missing_ids` so dead rows never reach a
  duel; `_start_missing_scan`/`_apply_missing_scan` populate it at startup; `_handle_missing_side`
  adds to it lazily when a file fails to open at render time (and auto-skips in live mode).
  Nothing is deleted from the DB — rows persist and re-resolve if the file reappears.
- **OneDrive flag constants** (~line 180): `_FILE_ATTRIBUTE_OFFLINE` 0x1000,
  `_FILE_ATTRIBUTE_RECALL_ON_OPEN` 0x40000, `_FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS` 0x400000.
- **Console log tags**: `[load]` (static-image open failure + timeout, in `_render_image_or_gif`),
  `[gif]` (decode failure / no-frames / success-frame-count, in `_decode_gif_async`),
  `[thumb]` (carousel thumbnail failure, in `_make_thumb_image`), `[audit]` (startup audit).
  Each failure line prints the path, `type(ex).__name__: ex`, and the `describe_file_state` result.
- **Known finding**: "files not found" / failed loads are dominated by **stale DB rows** whose
  files were deleted/moved off disk (DB path no longer resolves) — *not* OneDrive online-only
  files. These are now skipped at runtime (see "Missing-file skipping"); the DB rows are kept,
  not deleted.

## What NOT to do
- Don't increment `duels` in `_apply_revote` or `revote_comparison_db`
- Don't change `left_score_before`/`right_score_before` on a revote — they are fixed at record time
- Don't use absolute-score writes for mid-history edits — use DELTA (`revote/undo_comparison_db`) so later duels aren't clobbered
- Don't let drill-in thumbnail workers outlive the window — they check `self._sd_cancel` / `winfo_exists`
- Don't use worktrees
- Don't fall back across tag groups in `pick_one` when `required_tags` is set
- Don't block the main thread with thumbnail/video/file I/O
- Don't DELETE missing rows from the DB (files may reappear / comparisons reference their ids) — skip them via `_missing_ids` instead
- Don't DELETE comparisons/snapshots on rollback — archive via the `active` flag so every rollback stays undoable
- Don't re-commit derived/heavy data to git (DB, sidecars, backups, installer) — it's `.gitignore`d on purpose; rollback is in-app now
- Don't rely on replaying old `comparisons` rows (legacy tie/downvote both wrote `chosen_id=NULL`) — roll back via snapshots instead
- Don't re-introduce tie/downvote as a scoring outcome — the feature is retired (`choose` skip = no score); skips must stay score-neutral
- Don't put `FAVORITE` (or any `NON_MATCH_TAGS`) into a matchmaking frozenset — always use `_match_tags`; don't route favoriting through the `_on_tag_change` reroll path
- Don't remove the tie/downvote display branches in the drill-in (`mark`/legend) — archived legacy rows still render them

## Claude instructions
- At the end of every response that changes files, provide a **Commit Summary** (short title) and **Description** (body explaining what changed and why) for the user to use if they decide to commit — never run `git commit` yourself
- Keep this file updated as methods are added, removed, or relocated
- Update line numbers in the method table after any significant edits
- If new constants, state variables, or DB columns are added, reflect them here
- Only read files explicitly needed for the current task — do not do broad exploratory searches
- Do not perform sanity checks or verification passes unless explicitly requested
- Before editing any method, verify its actual line number with a Read and correct 
  the table if it has drifted
- After any edit that adds, removes, or relocates a method, update the table 
  before ending the session
- If a method is removed or renamed, delete or update its table entry immediately
- When adding new constants, state vars, or significant methods, add them to the 
  relevant section before closing out the task