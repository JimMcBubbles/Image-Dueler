# Image Duel Ranker — Claude context

## Project shape
- **Single file:** `image_duel_ranker.py` (~4200 lines). All edits go here directly.
- **No worktrees.** User runs the script live; always edit the main working directory.
- **DB:** `.image_ranking.sqlite` (SQLite, same dir as script)
- **Sidecars:** `.image_duel_sidecars/<filename>.json` — per-file score cache written async

## Key constants (top of file)
| Name | Value |
|------|-------|
| `BASE_SCORE` | 1000.0 |
| `DOWNVOTE_PENALTY` | 12.0 |
| `TAG_OPTIONS` | `["SFW","MEME","HIDE","CW"]` — mutable list; custom tags appended at runtime |
| `BLUR_TAGS` | `{"CW","HIDE"}` — tags whose carousel thumbnails are blurred until that duel is selected |
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
images(id, path, folder, score, wins, losses, duels, last_seen, hidden, tags)
comparisons(id, left_id, right_id, chosen_id, ts)
```
Row tuple indices: `(0=id, 1=path, 2=folder, 3=duels, 4=wins, 5=losses, 6=score, 7=hidden, 8=tags)`

## Core state (App instance)
```python
self.current          # (row_a, row_b) being displayed right now
self.live_current     # (row_a, row_b) of the active live duel (preserved during edit mode)
self.duel_history     # List[dict] — past voted duels
self.history_index    # None = live mode; int = edit/history mode
self.future_queue     # List[{"a":row,"b":row,"thumb":None}] — pre-rolled upcoming duels
self._missing_ids     # set[int] — image ids whose file is gone from disk; excluded by _pool_rows
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
| Method | ~Line | Purpose |
|--------|-------|---------|
| `record_result` | 348 | Creates comparison, updates DB, returns history entry dict |
| `_apply_revote` | 1250 | Edits existing vote — delta wins/losses only, **no duels increment** |
| `_create_history_sub_duel` | 1327 | Tag change in edit mode → nullify vote, roll replacement, insert sub-entry |
| `_create_live_sub_duel` | 2530 | Tag change in live mode → replace slot with fresh pick, queue sub-duel for tagged image next in future_queue |
| `_entry_is_sensitive` | 1209 | True if entry's stored a_tags/b_tags intersect BLUR_TAGS |
| `_pair_is_sensitive` | 1214 | True if either row's tags intersect BLUR_TAGS |
| `_entry_sensitive_label` | 1219 | "TAG, TAG" label for blurred history carousel slots |
| `_pair_sensitive_label` | 1226 | "TAG, TAG" label for blurred future/live carousel slots |
| `_tag_usage_counts` | 1233 | Returns {tag: image_count} for all images; used to sort tag menus by usage |
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
| `_render_image_or_gif` | 3157 | Async image/GIF render — shows "Loading…", starts load_worker thread, schedules 8 s timeout. Timeout now stays armed **through** GIF frame decode (dismissed in `_decode_gif_async`). On a missing-file open error calls `_handle_missing_side` instead of just printing "Failed to load" |
| `_decode_gif_async` | 3261 | Spawns decode_worker thread for GIF frame extraction; `apply_result` dismisses the load-timeout left armed by `_render_image_or_gif` |
| `_pool_rows` | 2552 | Builds the duel pool from DB; **excludes `self._missing_ids`** so deleted/moved files are never picked; applies pool filter |
| `_start_missing_scan` | 2565 | Daemon-thread launcher: runs `audit_file_availability(DB_PATH)`, posts result to `_apply_missing_scan` via root.after. Called at end of `__init__` |
| `_apply_missing_scan` | 2577 | Main-thread: sets `self._missing_ids`, purges missing-referencing entries from `future_queue`, reloads the live duel if it references a missing file |
| `_handle_missing_side` | 2945 | Render-time miss: adds the row id to `_missing_ids`; live mode → `_replace_side_keep_other` (auto-skip); history/solo → shows "File not found (removed from rotation)" |
| `_ffmpeg_exe` | 3795 | Returns ffmpeg path (cached after first call) via imageio-ffmpeg or PATH |
| `_cleanup_waveform_cache` | 3816 | Removes wave PNGs older than 7 days from temp dir; runs once per session on background thread |
| `_maybe_request_waveform` | 3831 | Launches background waveform generation for current media; guards against duplicate jobs per key |
| `_waveform_worker` | 3879 | ffmpeg showwavespic → tinted PIL image; posts result back via root.after |
| `_redraw_waveform_debounced` | 3992 | Debounces `_redraw_waveform` calls (40 ms) to prevent main-thread thrash on window resize |
| `_redraw_waveform` | 4002 | Scales waveform source image to canvas size and draws playhead |
| `_update_playhead` | 4043 | Draws YouTube-style progress track + playhead line on the wave canvas |
| `toggle_sparklines` | ~4230 | Toggles sparkline mode on/off, updates button label/color, refreshes sidebar |
| `cycle_sparkline_window` | ~4238 | Cycles sparkline_window through SPARKLINE_WINDOWS; refreshes sidebar if sparklines on |

## Carousel slot map encoding
`_carousel_slot_map[i]` stores:
- `int >= 0` → history index (click → edit mode)
- `"live"` → live current slot
- `("future", i)` → future_queue[i] (click → _jump_to_future)
- `None` → empty/disabled

## Tag matching rule
Tagged images **only** duel images with the **exact same tag set** (frozenset equality).
Untagged (empty set) images only duel other untagged images. No cross-group fallback.

## Revote rule
`_apply_revote` must **never** increment `duels`. It computes delta wins/losses between
old winner and new winner and applies only the difference. Scores are recalculated from
`before_a/before_b` snapshots.

## Sub-duel rule
When tags change in edit mode: parent vote → None (tie), tagged slot gets a fresh pick,
sub-duel entry inserted after parent with `sub_label="N.1"`, `comparison_id=None`.
Carousel highlights sub-duel amber until voted. View stays on parent duel.

## Async patterns
- Sidecar writes: daemon thread via `update_image_metadata`
- Thumbnail builds: daemon thread → `root.after(0, _update_carousel)` on completion
- Video snapshot polling: daemon thread
- GIF decode: daemon thread via `_decode_gif_async`
- Static image open+thumbnail: daemon thread via `load_worker` inside `_render_image_or_gif`; 8 s timeout shows Retry/Open-File overlay (timeout now spans GIF frame decode too)
- Missing-file scan: daemon thread via `_start_missing_scan` → `audit_file_availability` → `root.after(0, _apply_missing_scan)`

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
- Don't increment `duels` in `_apply_revote`
- Don't use worktrees
- Don't fall back across tag groups in `pick_one` when `required_tags` is set
- Don't block the main thread with thumbnail/video/file I/O
- Don't DELETE missing rows from the DB (files may reappear / comparisons reference their ids) — skip them via `_missing_ids` instead

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