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
| `TAG_OPTIONS` | `["SFW","MEME","HIDE","CW"]` |
| `carousel_size` | 6 slots |
| `ACCENT` / `PENDING_COLOR` / `FUTURE_COLOR` | blue / amber / dark-teal |

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
| `_create_history_sub_duel` | 1325 | Tag change in edit mode → nullify vote, roll replacement, insert sub-entry |
| `_enter_history_mode` | 1214 | Save live_current, set history_index, show entry |
| `_exit_history_mode` | 1220 | Restore live_current display, clear history_index |
| `_update_carousel` | 1462 | Full carousel repaint — live/edit/future branches |
| `_fill_future_queue` | 2006 | Top up future_queue to target size via pick_two |
| `_jump_to_future` | 2029 | Skip live+futures[0..i-1], make future[i] the new live duel |
| `pick_two` | 2079 | Groups pool by (frozenset(tags), media_kind); picks two from same group |
| `pick_one` | 2048 | Hard-filters by required_kind + required_tags (exact frozenset match) |
| `load_duel` | 2108 | Pops future_queue[0] or pick_two, sets live, calls _fill_future_queue |
| `choose` | 2136 | Vote handler — edit mode: _apply_revote or record_result; live: record + load_duel |

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
- GIF decode: daemon thread

## What NOT to do
- Don't increment `duels` in `_apply_revote`
- Don't use worktrees
- Don't fall back across tag groups in `pick_one` when `required_tags` is set
- Don't block the main thread with thumbnail/video/file I/O

## Claude instructions
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