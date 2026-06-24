# image_duel_ranker.py
# Image Duel Ranker — Elo-style dueling with artist leaderboard, e621 link export, and in-app VLC video playback.
# Version: 2026-02-26a
# Update: Updating side tags now rerolls that side to a replacement matched against the other side's tags.
# Build: 2026-02-26a (tag-update-reroll)

import os
import io
import sys
import re
import math
import random
import sqlite3
import time
import json
from pathlib import Path
from datetime import datetime, timezone
from collections import deque
from typing import Optional, Tuple, List
from urllib.parse import quote_plus
import webbrowser

import subprocess
import shutil
import tempfile
import threading
import traceback
import hashlib
import tkinter as tk
import tkinter.ttk as ttk
import tkinter.font as tkfont
import tkinter.messagebox as messagebox

from PIL import Image, ImageTk, ImageSequence, ImageFilter, ImageDraw

# Optional chart (only used on exit)
try:
    import matplotlib.pyplot as plt
except Exception:
    plt = None

# Optional EXIF embed
try:
    import piexif
except Exception:
    piexif = None

# Optional "proper" video playback (with audio) via VLC
try:
    import vlc  # type: ignore
    HAVE_VLC = True
except Exception:
    vlc = None
    HAVE_VLC = False

# -------------------- THEME (Dark Mode) --------------------
DARK_BG     = "#1e1e1e"
DARK_PANEL  = "#252526"
DARK_BORDER = "#333333"
TEXT_COLOR  = "#eeeeee"
ACCENT         = "#569cd6"
LINK_COLOR     = "#4ea1ff"
PENDING_COLOR  = "#7a5200"  # amber highlight for sub-duels awaiting a vote
FUTURE_COLOR   = "#1a3a4a"  # dark teal for pre-rolled upcoming duels

# -------------------- CONFIG --------------------
ROOT_DIR = r"I:\OneDrive\Discord Downloader Output\+\Grabber"
DISLIKES_ROOT_DIR = r"G:\-\Grabber"

SCRIPT_DIR = Path(__file__).resolve().parent
DB_PATH = SCRIPT_DIR / ".image_ranking.sqlite"
SIDECAR_DIR = SCRIPT_DIR / ".image_duel_sidecars"
SIDECAR_DIR.mkdir(parents=True, exist_ok=True)

EMBED_JPEG_EXIF = False
WINDOW_SIZE = (1500, 950)

# UI polish
INFO_BAR_HEIGHT = 28
INFO_BAR_BG = "#0f0f0f"
INFO_BAR_FG = "#d0d0d0"
INFO_BAR_FONT = ("Segoe UI", 10)
SEPARATOR_BG = "#242424"
SIDEBAR_WIDTH = 420

IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".bmp", ".tif", ".tiff"}
GIF_EXTS = {".gif"}
VIDEO_EXTS = {
    ".mp4", ".webm", ".mkv", ".avi", ".mov", ".wmv", ".m4v", ".mpg", ".mpeg"
}
SUPPORTED_EXTS = IMAGE_EXTS | GIF_EXTS | VIDEO_EXTS

K_FACTOR = 32.0
BASE_SCORE = 1000.0
DOWNVOTE_PENALTY = 12.0

LEADERBOARD_SIZE = 30
LEAF_MAX = 24

LEADERBOARD_METRIC_DEFAULT = "dislikes_adjusted"  # avg | shrunken_avg | dislikes_adjusted | lcb
FOLDER_MIN_N = 1
FOLDER_PRIOR_IMAGES = 8
LCB_Z = 1.0
DISLIKE_RATE_PENALTY = 300.0  # multiplied by dislike_rate = dislikes/(n+prior); replaces flat per-file penalty
VOLUME_BONUS = 50.0           # max bonus for large like-count; scaled by n/(n+prior)

SPARKLINE_WINDOW_DEFAULT = 60   # comparisons per folder to sample for sparkline
SPARKLINE_WINDOWS = (20, 40, 60, 100, 200)
SPARKLINE_BUCKETS = 7           # number of segments in each sparkline

E621_MAX_TAGS = 40
E621_MAX_OR_TAGS = 37  # max ~ (OR) artist tags per URL; keep a few slots for common tags
DEFAULT_COMMON_TAGS = "order:created_asc date:28_months_ago -voted:everything"

TAG_OPTIONS = ["SFW", "MEME", "HIDE", "CW", "FAVORITE"]
BLUR_TAGS = {"CW", "HIDE"}  # tags whose carousel thumbnails are blurred until the duel is selected
FAVORITE_TAG = "FAVORITE"          # marker tag toggled by the heart button (replaces "Upvote")
NON_MATCH_TAGS = {FAVORITE_TAG}    # tags excluded from duel matchmaking grouping (pure markers)
FAVORITE_COLOR = "#e25555"         # heart color when an image is favorited

# Sentinel row placed in self.current's "b" slot for solo duels (no opponent in tag group).
# id=-1 is never a real DB row; checked via row[0] < 0.
_NO_OPPONENT = (-1, "\x00no_opponent", "\x00no_opponent", 0, 0, 0, 0.0, 0, "[]")
POOL_FILTER_OPTIONS = ["All", "Images", "GIFs", "Videos", "Videos (audio)", "Animated", "Hidden"]

BUILD_STAMP = '2026-02-26a (tag-update-reroll)'

GIF_PRELOAD_MAX_FRAMES = 120
LOAD_TIMEOUT_MS = 8000  # ms before showing Retry/Open-File overlay on a slow load

# -------------------- History / rollback / backups --------------------
SESSION_GAP_SECONDS = 1800        # >30 min between consecutive comparisons => new session (backfill grouping)
SNAPSHOT_SCHEMA_VERSION = 1       # bump if the snapshots.payload JSON format changes
BACKUP_DIR = SCRIPT_DIR / "backups"
BACKUP_KEEP = 20                  # number of rotated VACUUM-INTO backups to retain (--backup)
DB_PREHISTORY_BAK = Path(str(DB_PATH) + ".prehistory.bak")  # one-time copy taken before first history migration

_DISLIKE_COUNTS_BY_REL_FOLDER: dict[str, int] = {}

# -------------------- DB --------------------
def init_db() -> sqlite3.Connection:
    print(f"[build] {BUILD_STAMP} | {Path(__file__).resolve()}")
    print("[init] opening database:", DB_PATH)
    conn = sqlite3.connect(DB_PATH)
    conn.execute(f"""
        CREATE TABLE IF NOT EXISTS images (
            id INTEGER PRIMARY KEY,
            path TEXT UNIQUE,
            folder TEXT,
            score REAL DEFAULT {BASE_SCORE},
            wins INTEGER DEFAULT 0,
            losses INTEGER DEFAULT 0,
            duels INTEGER DEFAULT 0,
            last_seen INTEGER,
            hidden INTEGER DEFAULT 0,
            tags TEXT DEFAULT '[]'
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS comparisons (
            id INTEGER PRIMARY KEY,
            left_id INTEGER,
            right_id INTEGER,
            chosen_id INTEGER,
            ts INTEGER,
            outcome TEXT,
            left_score_before REAL,
            right_score_before REAL,
            left_score_after REAL,
            right_score_after REAL,
            session_id INTEGER,
            active INTEGER DEFAULT 1
        )
    """)
    conn.commit()
    migrate_schema(conn)
    retire_tie_downvote_once(conn)
    return conn

def migrate_schema(conn: sqlite3.Connection) -> None:
    # One-time copy of the live DB before any structural change (idempotent — only if absent).
    _backup_db_once()

    cols = [row[1] for row in conn.execute("PRAGMA table_info(images)")]
    if "hidden" not in cols:
        print("[migrate] adding 'hidden' column to images")
        conn.execute("ALTER TABLE images ADD COLUMN hidden INTEGER DEFAULT 0")
        conn.commit()
        conn.execute("UPDATE images SET hidden=0 WHERE hidden IS NULL")
        conn.commit()
    if "tags" not in cols:
        print("[migrate] adding 'tags' column to images")
        conn.execute("ALTER TABLE images ADD COLUMN tags TEXT DEFAULT '[]'")
        conn.commit()
        conn.execute("UPDATE images SET tags='[]' WHERE tags IS NULL")
        conn.commit()

    # ---- comparisons: make every duel reversible & complete going forward ----
    ccols = [row[1] for row in conn.execute("PRAGMA table_info(comparisons)")]
    for name, decl in (
        ("outcome", "TEXT"),
        ("left_score_before", "REAL"),
        ("right_score_before", "REAL"),
        ("left_score_after", "REAL"),
        ("right_score_after", "REAL"),
        ("session_id", "INTEGER"),
        ("active", "INTEGER DEFAULT 1"),
    ):
        if name not in ccols:
            print(f"[migrate] adding '{name}' column to comparisons")
            conn.execute(f"ALTER TABLE comparisons ADD COLUMN {name} {decl}")
    conn.commit()

    # Backfill outcome for legacy rows from chosen_id. NOTE: chosen_id=NULL was historically
    # written for BOTH 'tie/skip' AND 'downvote', so the two are indistinguishable in old rows;
    # classify every NULL-chosen legacy row as 'tie' (best-effort). New rows store an exact outcome.
    conn.execute("""
        UPDATE comparisons SET outcome =
            CASE
                WHEN chosen_id IS NOT NULL AND chosen_id = left_id  THEN 'left'
                WHEN chosen_id IS NOT NULL AND chosen_id = right_id THEN 'right'
                ELSE 'tie'
            END
        WHERE outcome IS NULL
    """)
    conn.execute("UPDATE comparisons SET active=1 WHERE active IS NULL")
    conn.commit()

    # ---- sessions & snapshots tables (rollback addressing) ----
    conn.execute("""
        CREATE TABLE IF NOT EXISTS sessions (
            id INTEGER PRIMARY KEY,
            started_ts INTEGER,
            ended_ts INTEGER,
            label TEXT,
            start_comparison_id INTEGER,
            note TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS snapshots (
            id INTEGER PRIMARY KEY,
            ts INTEGER,
            label TEXT,
            kind TEXT,
            session_id INTEGER,
            max_comparison_id INTEGER,
            payload TEXT
        )
    """)
    conn.commit()

    # One-time backfill: group existing comparisons into sessions by time gap so old history is
    # rollback-addressable. Runs only while the sessions table is still empty.
    if conn.execute("SELECT COUNT(*) FROM sessions").fetchone()[0] == 0:
        _backfill_sessions(conn)

    # One-time migration baseline snapshot: a guaranteed restore point for the pre-feature scoring
    # state. Runs only while the snapshots table is still empty.
    if conn.execute("SELECT COUNT(*) FROM snapshots").fetchone()[0] == 0:
        _take_snapshot(conn, kind="baseline", label="pre-history-feature migration baseline", session_id=None)

# Windows file-attribute flags relevant to OneDrive "Files On-Demand" placeholders.
# These let us tell a genuinely-missing file apart from one that merely hasn't been
# downloaded yet (present in the directory listing, but not physically on disk).
_FILE_ATTRIBUTE_OFFLINE               = 0x00001000
_FILE_ATTRIBUTE_RECALL_ON_OPEN        = 0x00040000  # dehydrated placeholder (reparse point)
_FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS = 0x00400000  # online-only (OneDrive Files On-Demand)


def describe_file_state(path: str) -> str:
    """Human-readable description of a media file's on-disk state, for diagnostics.

    Distinguishes a genuinely missing file from a OneDrive "online-only" placeholder
    (listed in the folder but not downloaded). Opening such a placeholder triggers a
    network hydration that can be slow or fail — a common cause of both "file not found"
    and "GIF won't load / load times out" symptoms under I:\\OneDrive. os.stat reads
    metadata only and does NOT trigger hydration, so this probe is cheap and safe.
    """
    try:
        st = os.stat(path)
    except FileNotFoundError:
        return "MISSING (not on disk - moved, deleted, or never synced)"
    except OSError as ex:
        return f"STAT-FAILED ({type(ex).__name__}: {ex})"

    attrs = getattr(st, "st_file_attributes", 0)
    flags = []
    if attrs & _FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS:
        flags.append("ONLINE-ONLY (OneDrive placeholder, not downloaded)")
    if attrs & _FILE_ATTRIBUTE_RECALL_ON_OPEN:
        flags.append("dehydrated/recall-on-open")
    if attrs & _FILE_ATTRIBUTE_OFFLINE:
        flags.append("offline")
    state = ", ".join(flags) if flags else "present (local)"
    return f"{state}; {st.st_size} bytes"


def audit_file_availability(db_path) -> set:
    """One-shot startup diagnostic: classify every DB media path as local / online-only /
    missing, print a summary, and return the set of image ids whose file is missing.

    Explains the scope of "some files are not being found" and slow loads in one place, and
    feeds the App's `_missing_ids` so dead rows are skipped when picking duels.

    Opens its OWN sqlite connection (the App's connection is bound to the main thread) and
    uses os.stat, which reads metadata only and never hydrates a OneDrive placeholder, so
    this is safe to run in bulk on a background thread.
    """
    try:
        c = sqlite3.connect(str(db_path))
        rows = list(c.execute("SELECT id, path FROM images WHERE hidden=0 OR hidden IS NULL"))
        c.close()
    except Exception as ex:
        print(f"[audit] could not read image paths: {ex}")
        return set()

    missing_ids: set = set()
    missing: list = []
    online_only: list = []
    errored: list = []
    local = 0
    recall_mask = (_FILE_ATTRIBUTE_RECALL_ON_DATA_ACCESS
                   | _FILE_ATTRIBUTE_RECALL_ON_OPEN
                   | _FILE_ATTRIBUTE_OFFLINE)
    for img_id, p in rows:
        try:
            st = os.stat(p)
        except FileNotFoundError:
            missing.append(p)
            missing_ids.add(img_id)
            continue
        except OSError as ex:
            errored.append((p, f"{type(ex).__name__}: {ex}"))
            continue
        if getattr(st, "st_file_attributes", 0) & recall_mask:
            online_only.append(p)
        else:
            local += 1

    print(f"[audit] checked {len(rows)} active files: "
          f"{local} local, {len(online_only)} online-only (OneDrive, not downloaded), "
          f"{len(missing)} MISSING, {len(errored)} stat-error")
    for p in missing[:15]:
        print(f"[audit]   MISSING: {p}")
    if len(missing) > 15:
        print(f"[audit]   ... and {len(missing) - 15} more missing")
    for p in online_only[:15]:
        print(f"[audit]   ONLINE-ONLY: {p}")
    if len(online_only) > 15:
        print(f"[audit]   ... and {len(online_only) - 15} more online-only")
    for p, err in errored[:15]:
        print(f"[audit]   STAT-ERROR: {p}  ({err})")
    if online_only:
        print("[audit] Tip: online-only files load slowly (and can time out / fail) because "
              "OneDrive must download them on access. Right-click the folder in Explorer -> "
              "'Always keep on this device' to pin them locally.")
    return missing_ids


def scan_images(conn: sqlite3.Connection) -> None:
    cur = conn.cursor()
    existing = {row[0] for row in cur.execute("SELECT path FROM images")}
    to_add = []
    print("[scan] scanning", ROOT_DIR)
    root = Path(ROOT_DIR)
    if not root.exists():
        print("[scan] ROOT_DIR does not exist:", ROOT_DIR)
        return
    for p in root.rglob("*"):
        if p.is_file() and p.suffix.lower() in SUPPORTED_EXTS:
            sp = str(p)
            if sp not in existing:
                to_add.append((sp, str(p.parent)))
    if to_add:
        cur.executemany("INSERT OR IGNORE INTO images(path, folder) VALUES (?, ?)", to_add)
        conn.commit()
        conn.execute("UPDATE images SET hidden=0 WHERE hidden IS NULL")
        conn.commit()
    n = cur.execute("SELECT COUNT(*) FROM images").fetchone()[0]
    print(f"[scan] total images in DB: {n}")


def _normalize_rel_folder_key(path_like: str) -> str:
    text = str(path_like).strip()
    text = text.replace('\\', '/')
    text = text.strip('/')
    return text.lower()


def _build_dislikes_index(dislikes_root: Path) -> dict[str, int]:
    idx: dict[str, int] = {}
    if not dislikes_root.exists():
        return idx
    for p in dislikes_root.rglob('*'):
        if not p.is_file() or p.suffix.lower() not in SUPPORTED_EXTS:
            continue
        try:
            rel_parent = p.parent.relative_to(dislikes_root)
            key = _normalize_rel_folder_key(str(rel_parent))
            idx[key] = idx.get(key, 0) + 1
        except Exception:
            continue
    return idx


def _relative_folder_to_root(folder: str, root: str) -> str:
    try:
        rel = Path(folder).resolve().relative_to(Path(root).resolve())
        return _normalize_rel_folder_key(str(rel))
    except Exception:
        return _normalize_rel_folder_key(Path(folder).name)


def refresh_dislikes_index() -> None:
    global _DISLIKE_COUNTS_BY_REL_FOLDER
    dislikes_root = Path(DISLIKES_ROOT_DIR)
    print('[dislikes] scanning', dislikes_root)
    _DISLIKE_COUNTS_BY_REL_FOLDER = _build_dislikes_index(dislikes_root)
    folders = len(_DISLIKE_COUNTS_BY_REL_FOLDER)
    files = sum(_DISLIKE_COUNTS_BY_REL_FOLDER.values())
    print(f'[dislikes] indexed {files} files across {folders} mirrored folders')

# -------------------- Elo helpers --------------------
def elo_expected(sa: float, sb: float) -> float:
    return 1.0 / (1.0 + 10 ** ((sb - sa) / 400.0))

def elo_update(sa: float, sb: float, winner_is_a: Optional[bool]) -> Tuple[float, float]:
    ea, eb = elo_expected(sa, sb), elo_expected(sb, sa)
    if winner_is_a is None:
        return (sa + K_FACTOR * (0.5 - ea), sb + K_FACTOR * (0.5 - eb))
    if winner_is_a:
        return (sa + K_FACTOR * (1.0 - ea), sb + K_FACTOR * (0.0 - eb))
    return (sa + K_FACTOR * (0.0 - ea), sb + K_FACTOR * (1.0 - eb))

# -------------------- Leaderboard (anti-bias) --------------------
def folder_leaderboard(conn: sqlite3.Connection, metric: str = LEADERBOARD_METRIC_DEFAULT,
                       min_n: int = FOLDER_MIN_N) -> List[dict]:
    mu_row = conn.execute("SELECT AVG(score) FROM images WHERE hidden=0").fetchone()
    global_mu = float(mu_row[0] if mu_row and mu_row[0] is not None else BASE_SCORE)

    rows: List[dict] = []
    if metric in ("avg", "shrunken_avg", "dislikes_adjusted"):
        data = conn.execute("""
            SELECT folder, AVG(score) AS avg_s, COUNT(*) AS n,
                   SUM(wins) AS wins, SUM(losses) AS losses
            FROM images
            WHERE hidden=0
            GROUP BY folder
            HAVING COUNT(*) >= ?
        """, (min_n,)).fetchall()
        for (folder, avg_s, n, wins, losses) in data:
            avg_s = float(avg_s); n = int(n)
            wins = int(wins or 0); losses = int(losses or 0)
            score = ((avg_s * n + global_mu * FOLDER_PRIOR_IMAGES) / (n + FOLDER_PRIOR_IMAGES)
                     if metric in ("shrunken_avg", "dislikes_adjusted") else avg_s)
            rel_key = _relative_folder_to_root(folder, ROOT_DIR)
            dislikes_n = int(_DISLIKE_COUNTS_BY_REL_FOLDER.get(rel_key, 0))
            if metric == "dislikes_adjusted":
                score += (n / (n + FOLDER_PRIOR_IMAGES)) * VOLUME_BONUS
                score -= (dislikes_n / (n + dislikes_n + FOLDER_PRIOR_IMAGES)) * DISLIKE_RATE_PENALTY
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score,
                         "dislikes_n": dislikes_n, "wins": wins, "losses": losses})
    elif metric == "lcb":
        data = conn.execute("""
            SELECT folder, COUNT(*) AS n, AVG(score) AS avg_s, AVG(score*score) AS avg_sq,
                   SUM(wins) AS wins, SUM(losses) AS losses
            FROM images
            WHERE hidden=0
            GROUP BY folder
            HAVING COUNT(*) >= ?
        """, (min_n,)).fetchall()
        for (folder, n, avg_s, avg_sq, wins, losses) in data:
            n = int(n); avg_s = float(avg_s); avg_sq = float(avg_sq)
            wins = int(wins or 0); losses = int(losses or 0)
            var = max(0.0, avg_sq - avg_s * avg_s)
            se = (var ** 0.5) / (n ** 0.5) if n > 0 else 0.0
            score = avg_s - LCB_Z * se
            rel_key = _relative_folder_to_root(folder, ROOT_DIR)
            dislikes_n = int(_DISLIKE_COUNTS_BY_REL_FOLDER.get(rel_key, 0))
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score,
                         "dislikes_n": dislikes_n, "wins": wins, "losses": losses})
    else:
        return folder_leaderboard(conn, metric="avg", min_n=min_n)

    rows.sort(key=lambda r: r["score"], reverse=True)
    out: List[dict] = []
    for i, r in enumerate(rows, start=1):
        out.append({
            "folder": r["folder"], "avg": r["avg"], "n": r["n"],
            "rank": i, "score": r["score"], "metric": metric,
            "dislikes_n": int(r.get("dislikes_n", 0)),
            "wins": r.get("wins", 0), "losses": r.get("losses", 0),
        })
    return out

def find_folder_rank(leader: List[dict], folder_path_str: str) -> Tuple[Optional[int], Optional[float], Optional[int], Optional[float]]:
    for item in leader:
        if item["folder"] == folder_path_str:
            return item["rank"], item["avg"], item["n"], item["score"]
    return None, None, None, None

# -------------------- Sparkline helpers --------------------
_SPARK_CHARS = "▁▂▃▄▅▆▇█"

def folder_sparkline(conn: sqlite3.Connection, folder: str,
                     window: int = SPARKLINE_WINDOW_DEFAULT,
                     buckets: int = SPARKLINE_BUCKETS) -> Optional[List[float]]:
    """Win-rate per bucket over the last `window` comparisons for images in `folder`.
    Returns list of floats in [0,1] of length `buckets`, or None if insufficient data."""
    img_ids = [r[0] for r in conn.execute(
        "SELECT id FROM images WHERE folder=? AND hidden=0", (folder,)
    ).fetchall()]
    if not img_ids:
        return None
    ph = ",".join("?" * len(img_ids))
    rows = conn.execute(f"""
        SELECT chosen_id FROM comparisons
        WHERE (left_id IN ({ph}) OR right_id IN ({ph}))
          AND chosen_id IS NOT NULL
        ORDER BY ts DESC
        LIMIT ?
    """, (*img_ids, *img_ids, window)).fetchall()
    if len(rows) < buckets:
        return None
    rows = list(reversed(rows))
    id_set = set(img_ids)
    results = [1 if r[0] in id_set else 0 for r in rows]
    bucket_size = len(results) / buckets
    rates = []
    for b in range(buckets):
        start = int(b * bucket_size)
        end = max(start + 1, int((b + 1) * bucket_size))
        chunk = results[start:end]
        rates.append(sum(chunk) / len(chunk))
    return rates

def render_sparkline(rates: List[float]) -> str:
    n = len(_SPARK_CHARS)
    return "".join(_SPARK_CHARS[min(int(r * n), n - 1)] for r in rates)

def _spark_tag_for_rate(rate: float) -> str:
    if rate >= 0.72:   return "spark_h"
    elif rate >= 0.58: return "spark_mh"
    elif rate >= 0.42: return "spark_m"
    elif rate >= 0.28: return "spark_ml"
    else:              return "spark_l"

# -------------------- Sidecar metadata --------------------
def update_image_metadata(path: Path, score: float) -> None:
    try:
        side = SIDECAR_DIR / (path.name + ".json")
        data: dict = {}
        if side.exists():
            try:
                data = json.loads(side.read_text(encoding="utf-8"))
            except Exception:
                data = {}
        data.update({
            "path": str(path),
            "rating_score": float(score),
            "updated_utc": datetime.now(tz=timezone.utc).isoformat(),
            "note": "Generated by Image Duel Ranker (Elo).",
        })
        side.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
    except Exception:
        return

    if EMBED_JPEG_EXIF and piexif and path.suffix.lower() in {".jpg", ".jpeg"}:
        try:
            try:
                exif_dict = piexif.load(str(path))
            except Exception:
                exif_dict = {"0th": {}, "Exif": {}, "GPS": {}, "1st": {}, "thumbnail": None}
            comment = f"ImageDuelRanker score={score:.2f}".encode("ascii", errors="ignore")
            exif_dict.setdefault("Exif", {})[piexif.ExifIFD.UserComment] = comment
            exif_bytes = piexif.dump(exif_dict)
            piexif.insert(exif_bytes, str(path))
        except Exception:
            pass

# -------------------- Record results --------------------
def _snapshot_stats(conn: sqlite3.Connection, img_id: int) -> dict:
    row = conn.execute(
        "SELECT score, duels, wins, losses, last_seen FROM images WHERE id=?",
        (img_id,),
    ).fetchone()
    if not row:
        return {"score": BASE_SCORE, "duels": 0, "wins": 0, "losses": 0, "last_seen": 0}
    return {
        "score": float(row[0]),
        "duels": int(row[1]),
        "wins": int(row[2]),
        "losses": int(row[3]),
        "last_seen": int(row[4] or 0),
    }

def record_result(conn: sqlite3.Connection, a: tuple, b: tuple, winner: Optional[str],
                  session_id: Optional[int] = None) -> dict:
    a_id, a_path, a_folder, a_duels, a_wins, a_losses, a_score, a_hidden = a[:8]
    b_id, b_path, b_folder, b_duels, b_wins, b_losses, b_score, b_hidden = b[:8]

    before_a = _snapshot_stats(conn, a_id)
    before_b = _snapshot_stats(conn, b_id)

    a_wins_inc = b_wins_inc = 0
    a_losses_inc = b_losses_inc = 0
    chosen_id = None

    if winner == "a":
        new_a, new_b = elo_update(a_score, b_score, True)
        chosen_id = a_id
        a_wins_inc, b_losses_inc = 1, 1
    elif winner == "b":
        new_a, new_b = elo_update(a_score, b_score, False)
        chosen_id = b_id
        b_wins_inc, a_losses_inc = 1, 1
    elif winner == "downvote":
        new_a, new_b = a_score - DOWNVOTE_PENALTY, b_score - DOWNVOTE_PENALTY
        a_losses_inc, b_losses_inc = 1, 1
    else:  # skip/tie
        new_a, new_b = elo_update(a_score, b_score, None)

    # outcome is the exact, replay-complete record (left/right/tie/downvote); a==left, b==right.
    outcome = {"a": "left", "b": "right", "downvote": "downvote"}.get(winner, "tie")

    ts = int(time.time())
    cur = conn.cursor()
    cur.execute(
        "UPDATE images SET score=?, duels=duels+1, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
        (new_a, a_wins_inc, a_losses_inc, ts, a_id),
    )
    cur.execute(
        "UPDATE images SET score=?, duels=duels+1, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
        (new_b, b_wins_inc, b_losses_inc, ts, b_id),
    )
    cur.execute(
        "INSERT INTO comparisons(left_id, right_id, chosen_id, ts, outcome, "
        "left_score_before, right_score_before, left_score_after, right_score_after, session_id, active) "
        "VALUES (?,?,?,?,?,?,?,?,?,?,1)",
        (a_id, b_id, chosen_id, ts, outcome,
         before_a["score"], before_b["score"], float(new_a), float(new_b), session_id),
    )
    comparison_id = cur.lastrowid
    conn.commit()

    # Sidecars (async-ish, but safe in a short thread)
    try:
        # import threading (moved to top-level)
        threading.Thread(target=update_image_metadata, args=(Path(a_path), float(new_a)), daemon=True).start()
        threading.Thread(target=update_image_metadata, args=(Path(b_path), float(new_b)), daemon=True).start()
    except Exception:
        pass
    return {
        "a_id": a_id,
        "b_id": b_id,
        "a_path": a_path,
        "b_path": b_path,
        "a_tags": a[8] if len(a) > 8 else "",
        "b_tags": b[8] if len(b) > 8 else "",
        "winner": winner,
        "comparison_id": comparison_id,
        "before_a": before_a,
        "before_b": before_b,
    }

# -------------------- History: sessions, snapshots, rollback, backups --------------------
# Design: the `images` table is the exact source of truth. New duels are fully logged in
# `comparisons` (outcome + before/after scores + session_id) so they can be reversed exactly.
# Snapshots store the whole `images` scoring state as JSON; rollbacks restore a snapshot and
# flip the `comparisons.active` flag (never DELETE) so every rollback is itself undoable.

def _backup_db_once() -> None:
    """One-time file copy of the live DB before the first history migration. Idempotent."""
    try:
        if DB_PATH.exists() and not DB_PREHISTORY_BAK.exists():
            shutil.copy2(str(DB_PATH), str(DB_PREHISTORY_BAK))
            print(f"[migrate] one-time pre-history backup written: {DB_PREHISTORY_BAK}")
    except Exception as ex:
        print(f"[migrate] pre-history backup failed (continuing): {ex}")


def _backfill_sessions(conn: sqlite3.Connection) -> int:
    """Group existing comparisons into sessions by ts gap (> SESSION_GAP_SECONDS => new session)."""
    rows = conn.execute("SELECT id, ts FROM comparisons ORDER BY ts, id").fetchall()
    if not rows:
        return 0
    groups: List[list] = []
    cur_group = [rows[0]]
    for prev, row in zip(rows, rows[1:]):
        prev_ts, ts = (prev[1] or 0), (row[1] or 0)
        if ts - prev_ts > SESSION_GAP_SECONDS:
            groups.append(cur_group)
            cur_group = [row]
        else:
            cur_group.append(row)
    groups.append(cur_group)

    cur = conn.cursor()
    for g in groups:
        ids = [r[0] for r in g]
        tss = [r[1] for r in g if r[1] is not None]
        started = min(tss) if tss else None
        ended = max(tss) if tss else None
        cur.execute(
            "INSERT INTO sessions(started_ts, ended_ts, label, start_comparison_id, note) VALUES (?,?,?,?,?)",
            (started, ended, "backfill", min(ids), f"{len(ids)} duels"),
        )
        sid = cur.lastrowid
        ph = ",".join("?" * len(ids))
        cur.execute(f"UPDATE comparisons SET session_id=? WHERE id IN ({ph})", (sid, *ids))
    conn.commit()
    print(f"[migrate] backfilled {len(groups)} sessions from {len(rows)} comparisons")
    return len(groups)


def _images_state_payload(conn: sqlite3.Connection) -> str:
    """Compact JSON of every image's (id, score, wins, losses, duels)."""
    rows = conn.execute("SELECT id, score, wins, losses, duels FROM images").fetchall()
    return json.dumps(
        {"v": SNAPSHOT_SCHEMA_VERSION,
         "rows": [[int(r[0]), float(r[1]), int(r[2]), int(r[3]), int(r[4])] for r in rows]},
        separators=(",", ":"),
    )


def _take_snapshot(conn: sqlite3.Connection, kind: str, label: str = "",
                   session_id: Optional[int] = None) -> int:
    """Insert a snapshot of the full images scoring state. Returns the new snapshot id."""
    ts = int(time.time())
    max_cid = int(conn.execute("SELECT COALESCE(MAX(id), 0) FROM comparisons").fetchone()[0])
    payload = _images_state_payload(conn)
    cur = conn.cursor()
    cur.execute(
        "INSERT INTO snapshots(ts, label, kind, session_id, max_comparison_id, payload) VALUES (?,?,?,?,?,?)",
        (ts, label, kind, session_id, max_cid, payload),
    )
    conn.commit()
    sid = cur.lastrowid
    print(f"[snapshot] #{sid} kind={kind} label={label!r} max_cid={max_cid} bytes={len(payload)}")
    return sid


def _restore_images_from_payload(conn: sqlite3.Connection, payload: str) -> int:
    """Write a snapshot payload back into the images table (score/wins/losses/duels only)."""
    data = json.loads(payload)
    rows = data["rows"] if isinstance(data, dict) else data
    conn.executemany(
        "UPDATE images SET score=?, wins=?, losses=?, duels=? WHERE id=?",
        [(float(r[1]), int(r[2]), int(r[3]), int(r[4]), int(r[0])) for r in rows],
    )
    conn.commit()
    return len(rows)


def regenerate_all_sidecars(conn: sqlite3.Connection, progress=None) -> int:
    """Rebuild every per-file sidecar JSON from images.score. Safe to run anytime (idempotent)."""
    rows = conn.execute("SELECT path, score FROM images").fetchall()
    total = len(rows)
    done = 0
    for path, score in rows:
        try:
            update_image_metadata(Path(path), float(score))
        except Exception:
            pass
        done += 1
        if progress and done % 200 == 0:
            progress(done, total)
    if progress:
        progress(done, total)
    print(f"[sidecars] regenerated {done}/{total} sidecars")
    return done


def backup_db(keep: int = BACKUP_KEEP) -> Optional[Path]:
    """VACUUM INTO a timestamped copy under backups/ and rotate to the last `keep`."""
    try:
        BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now(tz=timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        dest = BACKUP_DIR / f"image_ranking_{stamp}.sqlite"
        src = sqlite3.connect(str(DB_PATH))
        try:
            src.execute("VACUUM INTO ?", (str(dest),))
        finally:
            src.close()
        if keep and keep > 0:
            backups = sorted(BACKUP_DIR.glob("image_ranking_*.sqlite"))
            for old in backups[:-keep]:
                try:
                    old.unlink()
                except Exception:
                    pass
        size = dest.stat().st_size if dest.exists() else 0
        print(f"[backup] wrote {dest} ({size} bytes); retaining last {keep}")
        return dest
    except Exception as ex:
        print(f"[backup] failed: {ex}")
        return None


def undo_last_comparisons(conn: sqlite3.Connection, n: int = 1,
                          session_id: Optional[int] = None) -> dict:
    """Reverse the last `n` fully-logged active comparisons using their stored before-scores +
    outcome. Restores both images' score, decrements duels, undoes win/loss, and flags the rows
    inactive (never DELETE). Exact and O(n). Takes a pre-rollback snapshot first (undoable).

    Only rows with stored before-scores are eligible (legacy rows lack them); reversing newest
    first makes contiguous before-scores chain back to the exact pre-vote state.
    """
    rows = conn.execute(
        "SELECT id, left_id, right_id, outcome, left_score_before, right_score_before "
        "FROM comparisons "
        "WHERE active=1 AND left_score_before IS NOT NULL AND right_score_before IS NOT NULL "
        "ORDER BY id DESC LIMIT ?",
        (int(n),),
    ).fetchall()
    if not rows:
        return {"undone": 0, "pre_snapshot_id": None, "ids": [], "affected": []}

    pre = _take_snapshot(conn, kind="pre-rollback", label=f"before undo_last({n})", session_id=session_id)
    cur = conn.cursor()
    affected: set = set()
    for cid, lid, rid, outcome, lsb, rsb in rows:
        cur.execute("UPDATE images SET score=? WHERE id=?", (float(lsb), lid))
        cur.execute("UPDATE images SET score=? WHERE id=?", (float(rsb), rid))
        cur.execute("UPDATE images SET duels=max(0, duels-1) WHERE id IN (?,?)", (lid, rid))
        if outcome == "left":
            cur.execute("UPDATE images SET wins=max(0, wins-1) WHERE id=?", (lid,))
            cur.execute("UPDATE images SET losses=max(0, losses-1) WHERE id=?", (rid,))
        elif outcome == "right":
            cur.execute("UPDATE images SET wins=max(0, wins-1) WHERE id=?", (rid,))
            cur.execute("UPDATE images SET losses=max(0, losses-1) WHERE id=?", (lid,))
        elif outcome == "downvote":
            cur.execute("UPDATE images SET losses=max(0, losses-1) WHERE id IN (?,?)", (lid, rid))
        # 'tie': no win/loss change
        cur.execute("UPDATE comparisons SET active=0 WHERE id=?", (cid,))
        affected.add(lid)
        affected.add(rid)
    conn.commit()
    return {"undone": len(rows), "pre_snapshot_id": pre,
            "ids": [r[0] for r in rows], "affected": sorted(affected)}


def restore_snapshot_db(conn: sqlite3.Connection, snapshot_id: int,
                        session_id: Optional[int] = None) -> dict:
    """Restore a snapshot's images payload, then recompute comparisons.active as a deterministic
    function of the restored point (active iff id <= snapshot.max_comparison_id). Takes a
    pre-rollback snapshot first so the operation is itself exactly undoable."""
    snap = conn.execute(
        "SELECT id, max_comparison_id, payload FROM snapshots WHERE id=?", (int(snapshot_id),)
    ).fetchone()
    if not snap:
        return {"ok": False, "error": "snapshot not found"}
    pre = _take_snapshot(conn, kind="pre-rollback", label=f"before restore #{snapshot_id}", session_id=session_id)
    restored = _restore_images_from_payload(conn, snap[2])
    max_cid = int(snap[1] or 0)
    conn.execute("UPDATE comparisons SET active = CASE WHEN id <= ? THEN 1 ELSE 0 END", (max_cid,))
    conn.commit()
    return {"ok": True, "restored_rows": restored, "pre_snapshot_id": pre, "max_comparison_id": max_cid}


def _session_start_snapshot_id(conn: sqlite3.Connection, session_id: int) -> Optional[int]:
    """The snapshot representing the start of a session: the earliest auto/baseline/manual snapshot
    stamped with that session_id (smallest max_comparison_id)."""
    row = conn.execute(
        "SELECT id FROM snapshots WHERE session_id=? AND kind IN ('auto','baseline','manual') "
        "ORDER BY max_comparison_id ASC, id ASC LIMIT 1",
        (int(session_id),),
    ).fetchone()
    return int(row[0]) if row else None


def rollback_to_session_db(conn: sqlite3.Connection, session_id: int, where: str = "start",
                           live_session_id: Optional[int] = None) -> dict:
    """Roll the images state back to the start or end of a session by restoring the matching
    snapshot. 'start' = that session's start snapshot; 'end' = the next session's start snapshot.
    Only sessions recorded under the history feature have exact snapshots; backfilled sessions fall
    back to the nearest baseline at/before their start (or report no exact snapshot)."""
    srow = conn.execute(
        "SELECT id, started_ts, start_comparison_id FROM sessions WHERE id=?", (int(session_id),)
    ).fetchone()
    if not srow:
        return {"ok": False, "error": "session not found"}

    snap_id: Optional[int] = None
    if where == "start":
        snap_id = _session_start_snapshot_id(conn, session_id)
        if snap_id is None:
            start_cid = int(srow[2] or 0)
            row = conn.execute(
                "SELECT id FROM snapshots WHERE max_comparison_id <= ? "
                "ORDER BY max_comparison_id DESC, id DESC LIMIT 1",
                (start_cid,),
            ).fetchone()
            snap_id = int(row[0]) if row else None
    else:  # 'end' == start of the next session (by time)
        nxt = conn.execute(
            "SELECT id FROM sessions WHERE started_ts > ? ORDER BY started_ts ASC, id ASC LIMIT 1",
            (srow[1] or 0,),
        ).fetchone()
        if nxt:
            snap_id = _session_start_snapshot_id(conn, int(nxt[0]))

    if snap_id is None:
        return {"ok": False, "error": "no exact snapshot for that session boundary"}
    res = restore_snapshot_db(conn, snap_id, session_id=live_session_id)
    res["snapshot_id"] = snap_id
    return res


# ----- Per-comparison edit (drill into a session, change/undo one vote) -----
# These use DELTA math on the current image scores (score += new_after - old_after), so they are
# correct for a comparison anywhere in history — not just the tail — without re-cascading later
# duels (same non-cascading approximation as the live `_apply_revote`). They NEVER touch `duels`
# on a revote (revote rule). Only fully-logged comparisons (stored before/after) are editable.

def _outcome_increments(outcome: str):
    """win/loss increments (left_w, left_l, right_w, right_l) implied by an outcome."""
    if outcome == "left":     return (1, 0, 0, 1)
    if outcome == "right":    return (0, 1, 1, 0)
    if outcome == "downvote": return (0, 1, 0, 1)
    return (0, 0, 0, 0)  # tie


def _outcome_after_scores(lb: float, rb: float, outcome: str):
    """Scores both sides would have AFTER a duel with the given outcome, from before-scores lb/rb."""
    if outcome == "left":     return elo_update(lb, rb, True)
    if outcome == "right":    return elo_update(lb, rb, False)
    if outcome == "downvote": return (lb - DOWNVOTE_PENALTY, rb - DOWNVOTE_PENALTY)
    return elo_update(lb, rb, None)  # tie


def _fetch_editable_comparison(conn: sqlite3.Connection, comparison_id: int):
    row = conn.execute(
        "SELECT id, left_id, right_id, outcome, left_score_before, right_score_before, "
        "left_score_after, right_score_after, active FROM comparisons WHERE id=?",
        (int(comparison_id),),
    ).fetchone()
    if not row:
        return None, {"ok": False, "error": "comparison not found"}
    if row[4] is None or row[5] is None or row[6] is None or row[7] is None:
        return None, {"ok": False, "error": "legacy duel (no stored scores) — not individually editable"}
    return row, None


def revote_comparison_db(conn: sqlite3.Connection, comparison_id: int, new_outcome: str) -> dict:
    """Change one duel's outcome. Adjusts both images' current score by the delta vs the old
    outcome, fixes win/loss, rewrites the comparison row. Never changes `duels`."""
    row, err = _fetch_editable_comparison(conn, comparison_id)
    if err:
        return err
    cid, lid, rid, old_outcome, lb, rb, la, ra, active = row
    if not active:
        return {"ok": False, "error": "duel is archived (undone) — restore it before re-voting"}
    if new_outcome == old_outcome:
        return {"ok": True, "changed": False, "left_id": lid, "right_id": rid}
    new_la, new_ra = _outcome_after_scores(float(lb), float(rb), new_outcome)
    dL, dR = (new_la - float(la)), (new_ra - float(ra))
    olw, oll, orw, orl = _outcome_increments(old_outcome)
    nlw, nll, nrw, nrl = _outcome_increments(new_outcome)
    chosen = lid if new_outcome == "left" else (rid if new_outcome == "right" else None)
    cur = conn.cursor()
    cur.execute("UPDATE images SET score=score+?, wins=max(0,wins+?), losses=max(0,losses+?) WHERE id=?",
                (dL, nlw - olw, nll - oll, lid))
    cur.execute("UPDATE images SET score=score+?, wins=max(0,wins+?), losses=max(0,losses+?) WHERE id=?",
                (dR, nrw - orw, nrl - orl, rid))
    cur.execute("UPDATE comparisons SET outcome=?, chosen_id=?, left_score_after=?, right_score_after=? WHERE id=?",
                (new_outcome, chosen, float(new_la), float(new_ra), cid))
    conn.commit()
    return {"ok": True, "changed": True, "left_id": lid, "right_id": rid,
            "old_outcome": old_outcome, "new_outcome": new_outcome}


def undo_comparison_db(conn: sqlite3.Connection, comparison_id: int) -> dict:
    """Remove one duel's contribution: subtract its (after-before) score delta from both images,
    decrement `duels`, undo win/loss, flag the row inactive (never DELETE)."""
    row, err = _fetch_editable_comparison(conn, comparison_id)
    if err:
        return err
    cid, lid, rid, old_outcome, lb, rb, la, ra, active = row
    if not active:
        return {"ok": True, "already_undone": True, "left_id": lid, "right_id": rid}
    dL, dR = (float(la) - float(lb)), (float(ra) - float(rb))
    olw, oll, orw, orl = _outcome_increments(old_outcome)
    cur = conn.cursor()
    cur.execute("UPDATE images SET score=score-?, wins=max(0,wins-?), losses=max(0,losses-?), "
                "duels=max(0,duels-1) WHERE id=?", (dL, olw, oll, lid))
    cur.execute("UPDATE images SET score=score-?, wins=max(0,wins-?), losses=max(0,losses-?), "
                "duels=max(0,duels-1) WHERE id=?", (dR, orw, orl, rid))
    cur.execute("UPDATE comparisons SET active=0 WHERE id=?", (cid,))
    conn.commit()
    return {"ok": True, "left_id": lid, "right_id": rid}


def restore_comparison_db(conn: sqlite3.Connection, comparison_id: int) -> dict:
    """Re-activate a previously-undone duel: re-apply its stored (after-before) delta, re-increment
    duels and win/loss, set active=1. Inverse of undo_comparison_db."""
    row, err = _fetch_editable_comparison(conn, comparison_id)
    if err:
        return err
    cid, lid, rid, old_outcome, lb, rb, la, ra, active = row
    if active:
        return {"ok": True, "already_active": True, "left_id": lid, "right_id": rid}
    dL, dR = (float(la) - float(lb)), (float(ra) - float(rb))
    olw, oll, orw, orl = _outcome_increments(old_outcome)
    cur = conn.cursor()
    cur.execute("UPDATE images SET score=score+?, wins=max(0,wins+?), losses=max(0,losses+?), "
                "duels=duels+1 WHERE id=?", (dL, olw, oll, lid))
    cur.execute("UPDATE images SET score=score+?, wins=max(0,wins+?), losses=max(0,losses+?), "
                "duels=duels+1 WHERE id=?", (dR, orw, orl, rid))
    cur.execute("UPDATE comparisons SET active=1 WHERE id=?", (cid,))
    conn.commit()
    return {"ok": True, "left_id": lid, "right_id": rid}


def rebuild_scores_from_log(conn: sqlite3.Connection, dry_run: bool = False,
                            recall_map: Optional[dict] = None) -> dict:
    """Replay every ACTIVE comparison in chronological order (ts, id) from BASE_SCORE, recomputing
    each image's score/wins/losses/duels and **writing before/after scores into every comparison row**
    (so all legacy duels become individually editable). Original timestamps are untouched.

    Each duel uses its stored `outcome`; pass `recall_map={comparison_id: outcome}` to override
    specific ones (e.g. recalling an old NULL tie/downvote). Ambiguous legacy duels whose outcome is
    unknown stay 'tie' (their original downvote penalties are unrecoverable). Returns drift stats;
    when `dry_run` is False, applies the rebuild. Caller should snapshot first (reversible)."""
    recall_map = recall_map or {}
    rows = conn.execute(
        "SELECT id, left_id, right_id, outcome FROM comparisons WHERE active=1 ORDER BY ts, id"
    ).fetchall()
    cur_scores = {int(i): float(s) for (i, s) in conn.execute("SELECT id, score FROM images")}

    scores: dict = {}
    W: dict = {}
    L: dict = {}
    D: dict = {}

    def gs(i):
        return scores.get(i, BASE_SCORE)

    writes = []
    for (cid, lid, rid, outcome) in rows:
        oc = recall_map.get(cid, outcome) or "tie"
        lb, rb = gs(lid), gs(rid)
        la, ra = _outcome_after_scores(lb, rb, oc)
        scores[lid], scores[rid] = la, ra
        lw, ll, rw, rl = _outcome_increments(oc)
        W[lid] = W.get(lid, 0) + lw; L[lid] = L.get(lid, 0) + ll; D[lid] = D.get(lid, 0) + 1
        W[rid] = W.get(rid, 0) + rw; L[rid] = L.get(rid, 0) + rl; D[rid] = D.get(rid, 0) + 1
        writes.append((float(lb), float(rb), float(la), float(ra), oc, cid))

    all_ids = set(cur_scores) | set(scores)
    drift = [abs(scores.get(i, BASE_SCORE) - cur_scores.get(i, BASE_SCORE)) for i in all_ids]
    stats = {
        "duels": len(rows),
        "images": len(all_ids),
        "moved": sum(1 for x in drift if x > 1.0),
        "max_drift": max(drift) if drift else 0.0,
        "mean_drift": (sum(drift) / len(drift)) if drift else 0.0,
        "recalled": len(recall_map),
        "applied": not dry_run,
    }
    if dry_run:
        return stats

    cur = conn.cursor()
    cur.executemany(
        "UPDATE comparisons SET left_score_before=?, right_score_before=?, "
        "left_score_after=?, right_score_after=?, outcome=? WHERE id=?",
        writes,
    )
    cur.executemany(
        "UPDATE images SET score=?, wins=?, losses=?, duels=? WHERE id=?",
        [(scores.get(i, BASE_SCORE), W.get(i, 0), L.get(i, 0), D.get(i, 0), i) for i in all_ids],
    )
    conn.commit()
    return stats


def retire_tie_downvote_once(conn: sqlite3.Connection) -> int:
    """One-time policy change: ties/downvotes are retired as a feature. Archive every active
    tie/downvote comparison (never DELETE — they stay recoverable) and rebuild scores from the
    surviving decisive duels. Backs up the DB first. Self-guarding: once there are no active
    tie/downvote duels it is a permanent no-op (the UI no longer creates any)."""
    n = conn.execute(
        "SELECT COUNT(*) FROM comparisons WHERE active=1 AND outcome IN ('tie','downvote')"
    ).fetchone()[0]
    if n == 0:
        return 0
    print(f"[retire] ties/downvotes retired: archiving {n} active tie/downvote duels")
    try:
        dest = backup_db()
        print(f"[retire] pre-change backup: {dest}")
    except Exception as ex:
        print(f"[retire] backup failed (continuing — snapshot still taken): {ex}")
    _take_snapshot(conn, kind="pre-rollback", label="before retiring tie/downvote duels")
    conn.execute("UPDATE comparisons SET active=0 WHERE active=1 AND outcome IN ('tie','downvote')")
    conn.commit()
    stats = rebuild_scores_from_log(conn)
    print(f"[retire] archived {n} duels; rebuilt scores from decisive duels only "
          f"({stats['moved']} images moved >1pt, max {stats['max_drift']:.1f}). Reversible via the "
          f"'before retiring tie/downvote duels' snapshot or the backup.")
    return n


def set_image_hidden(conn: sqlite3.Connection, img_id: int, hidden: int) -> None:
    conn.execute("UPDATE images SET hidden=?, last_seen=? WHERE id=?", (hidden, int(time.time()), img_id))
    conn.commit()

def hide_image(conn: sqlite3.Connection, row: tuple) -> None:
    set_image_hidden(conn, row[0], 1)
    print(f"[hide] {row[1]}")

def unhide_image(conn: sqlite3.Connection, row: tuple) -> None:
    set_image_hidden(conn, row[0], 0)
    print(f"[unhide] {row[1]}")

# -------------------- e621 helper --------------------
def e621_url_for_path(path: str) -> Optional[str]:
    stem = Path(path).stem
    m = re.search(r"(\d+)$", stem) or re.search(r"(\d+)", stem)
    if not m:
        return None
    try:
        pid = int(m.group(1))
    except Exception:
        return None
    return f"https://e621.net/posts/{pid}"

# -------------------- UI --------------------
class App:
    def __init__(self, root: tk.Tk, conn: sqlite3.Connection):
        self.root = root
        self.conn = conn

        # Restore custom tags that were saved to the DB in prior sessions.
        # TAG_OPTIONS starts with only the 4 defaults; any extra tags stored
        # in images.tags would be silently dropped by _parse_tags/_ordered_tags
        # unless we add them back here before any UI or parsing happens.
        _known: set = set(TAG_OPTIONS)
        for (raw,) in conn.execute(
            "SELECT DISTINCT tags FROM images WHERE tags IS NOT NULL AND tags != '[]'"
        ):
            try:
                for t in json.loads(raw):
                    t = str(t).upper()
                    if t and t not in _known:
                        TAG_OPTIONS.append(t)
                        _known.add(t)
            except Exception:
                pass

        root.title(f"Image Duel Ranker — {BUILD_STAMP.split(' ')[0]}")
        root.geometry(f"{WINDOW_SIZE[0]}x{WINDOW_SIZE[1]}")
        root.configure(bg=DARK_BG)

        # state
        self.current: Optional[Tuple[tuple, tuple]] = None
        self.live_current: Optional[Tuple[tuple, tuple]] = None
        self.prev_artists = deque(maxlen=6)
        self.page = 0
        self.metric = LEADERBOARD_METRIC_DEFAULT
        self.metric_var = tk.StringVar(value=self.metric)
        self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
        self.sparkline_enabled = False
        self.sparkline_window = SPARKLINE_WINDOW_DEFAULT
        self._resize_job = None
        self._audio_cache = {}
        self._ffmpeg_exe_cache: Optional[dict] = None  # None=uncached; {"path": str|None}=cached
        self._waveform_cache_cleaned = False
        self.duel_history: List[dict] = []
        self.history_index: Optional[int] = None
        self.future_queue: List[dict] = []  # pre-rolled upcoming duels {"a":row,"b":row,"thumb":None}
        self._missing_ids: set = set()  # image ids whose file is gone from disk; excluded from picking
        self.session_id: Optional[int] = None   # current live session row; stamps every new comparison
        self._session_closed = True             # guards _close_session against double-stamping
        self._hm_win = None                      # History/Rollback manager Toplevel (singleton)
        self._sd_win = None                      # Session-detail drill-in Toplevel (singleton)
        self.solo_mode = False  # True when the live duel has no opponent (b == _NO_OPPONENT)
        self.carousel_size = 6
        self.carousel_visible = True
        self.carousel_thumb_size = (96, 54)
        self.carousel_height = 140
        self.carousel_default_height = 140
        self.carousel_min_height = 90
        self.carousel_max_height = 320
        self._carousel_drag_start = None
        self._carousel_dragging = False
        self._carousel_drag_start_height = None
        self._carousel_drag_started_visible = False

        # video state per side
        self.vlc_instance = None
        if HAVE_VLC:
            try:
                self.vlc_instance = vlc.Instance("--no-video-title-show", "--quiet")
            except Exception:
                self.vlc_instance = None

        self._side = {
            "a": self._new_side_state(),
            "b": self._new_side_state(),
        }

        # ---- Layout containers ----
        self.container = tk.Frame(root, bg=DARK_BG)
        self.container.pack(side="top", fill="both", expand=True)

        # Left: duel panels
        self.images_frame = tk.Frame(self.container, bg=DARK_BG)
        self.images_frame.pack(side="left", fill="both", expand=True)

        # Each panel is a container with an image label + a video frame + overlay controls.
        self.left_container = tk.Frame(self.images_frame, bg=DARK_PANEL, bd=0, highlightthickness=0)
        self.right_container = tk.Frame(self.images_frame, bg=DARK_PANEL, bd=0, highlightthickness=0)
        self.left_container.pack(side="left", fill="both", expand=True, padx=(6, 3), pady=6)
        self.right_container.pack(side="left", fill="both", expand=True, padx=(3, 6), pady=6)

        
        # Save pack options for fullscreen / layout restores
        self._left_pack_opts = self.left_container.pack_info()
        self._right_pack_opts = self.right_container.pack_info()
# Hover highlight for duel panels
        def _hover_on(c: tk.Frame):
            c.configure(highlightthickness=2, highlightbackground=ACCENT, highlightcolor=ACCENT)

        def _hover_off(c: tk.Frame):
            c.configure(highlightthickness=0)

        for c in (self.left_container, self.right_container):
            c.configure(highlightthickness=0)
        self.left_container.bind("<Enter>", lambda e: _hover_on(self.left_container))
        self.left_container.bind("<Leave>", lambda e: _hover_off(self.left_container))
        self.right_container.bind("<Enter>", lambda e: _hover_on(self.right_container))
        self.right_container.bind("<Leave>", lambda e: _hover_off(self.right_container))

        self.left_panel = tk.Label(self.left_container, bd=0, bg=DARK_PANEL, cursor="hand2")
        self.right_panel = tk.Label(self.right_container, bd=0, bg=DARK_PANEL, cursor="hand2")
        self.left_panel.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.right_panel.place(relx=0, rely=0, relwidth=1, relheight=1)

        # Info bars (top overlay) for each side
        self.left_info_bar = tk.Frame(self.left_container, bg=INFO_BAR_BG, bd=0, highlightthickness=0)
        self.right_info_bar = tk.Frame(self.right_container, bg=INFO_BAR_BG, bd=0, highlightthickness=0)
        self.left_info_bar.place(relx=0, rely=0, relwidth=1, height=INFO_BAR_HEIGHT)
        self.right_info_bar.place(relx=0, rely=0, relwidth=1, height=INFO_BAR_HEIGHT)

        self.left_info_row = tk.Frame(self.left_info_bar, bg=INFO_BAR_BG, bd=0, highlightthickness=0)
        self.right_info_row = tk.Frame(self.right_info_bar, bg=INFO_BAR_BG, bd=0, highlightthickness=0)
        self.left_info_row.pack(fill="both", expand=True)
        self.right_info_row.pack(fill="both", expand=True)

        self.left_info_text = tk.Label(self.left_info_row, text="", font=INFO_BAR_FONT,
                                       fg=INFO_BAR_FG, bg=INFO_BAR_BG, anchor="w")
        self.right_info_text = tk.Label(self.right_info_row, text="", font=INFO_BAR_FONT,
                                        fg=INFO_BAR_FG, bg=INFO_BAR_BG, anchor="w")
        self.left_info_text.grid(row=0, column=0, sticky="w", padx=8)
        self.right_info_text.grid(row=0, column=0, sticky="w", padx=8)

        self._build_tag_menu("a", self.left_info_row)
        self._build_tag_menu("b", self.right_info_row)
        self._build_action_buttons("a", self.left_info_row)
        self._build_action_buttons("b", self.right_info_row)
        self.left_info_row.columnconfigure(0, weight=1)
        self.right_info_row.columnconfigure(0, weight=1)

        # Make info bars behave like the image/video panel for clicks
        for w in (self.left_info_bar, self.left_info_text):
            w.bind("<Button-1>", lambda e: self.choose("a"))
            w.bind("<Control-Button-1>", lambda e: self._on_ctrl_options("a", e))
            w.bind("<Button-3>", lambda e: self.skip_side("a"))
            w.bind("<Button-2>", lambda e: self.hide_side("a"))
            w.bind("<Double-Button-1>", self.open_left)

        for w in (self.right_info_bar, self.right_info_text):
            w.bind("<Button-1>", lambda e: self.choose("b"))
            w.bind("<Control-Button-1>", lambda e: self._on_ctrl_options("b", e))
            w.bind("<Button-3>", lambda e: self.skip_side("b"))
            w.bind("<Button-2>", lambda e: self.hide_side("b"))
            w.bind("<Double-Button-1>", self.open_right)

        self.left_video = tk.Frame(self.left_container, bg="black", bd=0, highlightthickness=0)
        self.right_video = tk.Frame(self.right_container, bg="black", bd=0, highlightthickness=0)
        self.left_video.place_forget()
        self.right_video.place_forget()
        self.left_video_blur = tk.Label(self.left_video, bg="black", bd=0, highlightthickness=0)
        self.right_video_blur = tk.Label(self.right_video, bg="black", bd=0, highlightthickness=0)
        self.left_video_blur.place_forget()
        self.right_video_blur.place_forget()
        self._side["a"]["video_blur_label"] = self.left_video_blur
        self._side["b"]["video_blur_label"] = self.right_video_blur

        # Hover control bars
        self._build_hover_video_controls()

        # Right: sidebar
        self.sidebar = tk.Frame(self.container, bg=DARK_BG, bd=0, highlightthickness=0)
        self._sidebar_pack_opts = dict(side="right", fill="y", padx=(0, 6), pady=6)
        self.sidebar.pack(**self._sidebar_pack_opts)
        self.sidebar.configure(width=SIDEBAR_WIDTH)
        self.sidebar.pack_propagate(False)

        # Floating restore button when sidebar is hidden
        self.sidebar_restore_btn = tk.Button(self.root, text="Show sidebar",
                                             command=self.toggle_sidebar,
                                             bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.sidebar_restore_btn.place_forget()

        # ---- Pool filter ----
        self.pool_filter_var = tk.StringVar(value="All")
        self.pool_filter_row = tk.Frame(self.sidebar, bg=DARK_BG)
        tk.Label(self.pool_filter_row, text="Pool:", font=("Segoe UI", 10, "bold"),
                 fg=ACCENT, bg=DARK_BG).pack(side="left")
        self.pool_filter = tk.Menubutton(
            self.pool_filter_row,
            text=self.pool_filter_var.get(),
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG,
            bg=INFO_BAR_BG,
            activebackground=INFO_BAR_BG,
            activeforeground=INFO_BAR_FG,
            relief="flat",
            cursor="hand2",
            anchor="w",
            width=12,
        )
        self.pool_filter_menu = tk.Menu(self.pool_filter, tearoff=0)
        for pool_value in POOL_FILTER_OPTIONS:
            self.pool_filter_menu.add_radiobutton(
                label=pool_value,
                variable=self.pool_filter_var,
                value=pool_value,
                command=self.on_pool_filter_change,
            )
        self.pool_filter.configure(menu=self.pool_filter_menu)
        self.pool_filter.pack(side="right")
        self.pool_filter.configure(text=self.pool_filter_var.get())

        self.tag_filter_vars: dict = {}
        self.tag_filter_btn = tk.Menubutton(
            self.pool_filter_row,
            text="Tags: (none)",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG,
            bg=INFO_BAR_BG,
            activebackground=INFO_BAR_BG,
            activeforeground=INFO_BAR_FG,
            relief="flat",
            cursor="hand2",
            anchor="w",
        )
        self.tag_filter_btn.pack(side="right", padx=(0, 6))
        self.tag_filter_menu = tk.Menu(self.tag_filter_btn, tearoff=0)
        for tag in TAG_OPTIONS:
            var = tk.BooleanVar(value=False)
            self.tag_filter_vars[tag] = var
            self.tag_filter_menu.add_checkbutton(
                label=tag,
                variable=var,
                command=self.on_tag_filter_change,
            )
        self.tag_filter_btn.configure(menu=self.tag_filter_menu)

        # Sidebar toggle (focus mode)
        self.sidebar_visible = True
        self.sidebar_toggle_btn = tk.Button(self.pool_filter_row, text="Focus",
                                            command=self.toggle_sidebar,
                                            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat", width=7)
        self.sidebar_toggle_btn.pack(side="right", padx=(0, 6))
        self.blur_enabled = False
        self._blur_forced_by_focus = False
        self._window_was_focused = True
        self.blur_toggle_btn = tk.Button(self.pool_filter_row, text="Blur",
                                         command=self.toggle_blur,
                                         bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat", width=7)
        self.blur_toggle_btn.pack(side="right", padx=(0, 6))
        self.pool_filter_row.pack(fill="x", pady=(0, 6))

        # ---- Leaderboard ----
        self.leader_header = tk.Label(self.sidebar, text="Top Artists",
                                      font=("Segoe UI", 12, "bold"), fg=ACCENT, bg=DARK_BG)
        self.leader_controls_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.metric_btn = tk.Menubutton(
            self.leader_controls_row,
            text="Metric: (loading)",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG,
            bg=INFO_BAR_BG,
            activebackground=INFO_BAR_BG,
            activeforeground=INFO_BAR_FG,
            relief="flat",
            cursor="hand2",
            anchor="w",
        )
        self.metric_btn.pack(side="left", fill="x", expand=True)
        self.metric_menu = tk.Menu(self.metric_btn, tearoff=0)
        self._metric_tooltips = {
            "shrunken_avg": f"Shrunken Avg: dampens small-sample folders using prior={FOLDER_PRIOR_IMAGES}.",
            "dislikes_adjusted": (
                f"Shrunken Avg + volume bonus (max {VOLUME_BONUS:g}) "
                f"- dislike rate×{DISLIKE_RATE_PENALTY:g}. "
                f"Rewards large like-counts; penalizes by dislikes÷(likes+dislikes+{FOLDER_PRIOR_IMAGES})."
            ),
            "avg": "Simple Avg: plain mean score by folder.",
            "lcb": f"Lower Confidence Bound: conservative score (mean - z*SE, z={LCB_Z}).",
        }
        for metric_key in ("shrunken_avg", "dislikes_adjusted", "avg", "lcb"):
            self.metric_menu.add_radiobutton(
                label=self._metric_human(metric_key),
                variable=self.metric_var,
                value=metric_key,
                command=self.on_metric_change,
            )
        self.metric_menu.bind("<<MenuSelect>>", self._on_metric_menu_select, add="+")
        self.metric_menu.bind("<Unmap>", self._hide_ui_tooltip, add="+")
        self.metric_btn.configure(menu=self.metric_menu)
        self.metric_btn.configure(text=f"Metric: {self._metric_human(self.metric)}")
        self.page_label = tk.Label(
            self.leader_controls_row,
            text="",
            font=("Segoe UI", 9),
            fg=TEXT_COLOR,
            bg=DARK_BG,
            cursor="question_arrow",
        )
        self.page_label.pack(side="right", padx=(10, 0))

        self.board = tk.Text(self.sidebar, height=20, font=("Consolas", 10),
                             bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                             relief="flat", wrap="none")
        self.board.tag_configure("delta_up", foreground="#7ad97a")
        self.board.tag_configure("delta_down", foreground="#ff7a7a")
        self.board.tag_configure("delta_flat", foreground="#9a9a9a")
        self.board.tag_configure("delta_new", foreground="#9bd6ff")
        self.board.tag_configure("spark_h",  foreground="#5de05d")
        self.board.tag_configure("spark_mh", foreground="#99d499")
        self.board.tag_configure("spark_m",  foreground="#9a9a9a")
        self.board.tag_configure("spark_ml", foreground="#d49999")
        self.board.tag_configure("spark_l",  foreground="#e05d5d")
        self.board.tag_configure("spark_none", foreground="#555555")
        self.board.tag_configure("hl_left",  background=FUTURE_COLOR)
        self.board.tag_configure("hl_right", background=PENDING_COLOR)
        self.nav_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.btn_prev = tk.Button(self.nav_row, text="Prev [ / PgUp", width=14,
                                  command=lambda: self.change_page(-1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.btn_next = tk.Button(self.nav_row, text="Next ] / PgDn", width=14,
                                  command=lambda: self.change_page(+1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.btn_prev.pack(side="left", padx=(0, 6))
        self.btn_next.pack(side="right")

        self.spark_controls_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.spark_toggle_btn = tk.Button(
            self.spark_controls_row,
            text="Sparklines: Off",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG, bg=INFO_BAR_BG, activebackground=INFO_BAR_BG,
            relief="flat", cursor="hand2",
            command=self.toggle_sparklines,
        )
        self.spark_toggle_btn.pack(side="left", fill="x", expand=True)
        self.spark_window_btn = tk.Button(
            self.spark_controls_row,
            text=f"W: {SPARKLINE_WINDOW_DEFAULT}",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG, bg=INFO_BAR_BG, activebackground=INFO_BAR_BG,
            relief="flat", cursor="hand2",
            command=self.cycle_sparkline_window,
        )
        self.spark_window_btn.pack(side="right")

        # ---- Counters ----
        self.counters_header = tk.Label(self.sidebar, text="Counters",
                                        font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.counters_text = tk.Label(self.sidebar, text="", justify="left",
                                      font=("Consolas", 9), fg=TEXT_COLOR, bg=DARK_BG)

        # ---- Current / Previous ----
        self.now_header = tk.Label(self.sidebar, text="Current / Previous",
                                   font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.now = tk.Label(self.sidebar, text="", justify="left",
                            font=("Segoe UI", 10), fg=TEXT_COLOR, bg=DARK_BG)

        # ---- Links ----
        self.links_header = tk.Label(self.sidebar, text="Links",
                                     font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.link_left = tk.Label(self.sidebar, text="Left e621: (n/a)", fg=LINK_COLOR,
                                  bg=DARK_BG, cursor="hand2", font=("Consolas", 9), justify="left")
        self.link_right = tk.Label(self.sidebar, text="Right e621: (n/a)", fg=LINK_COLOR,
                                   bg=DARK_BG, cursor="hand2", font=("Consolas", 9), justify="left")
        self.link_left.url = ""
        self.link_right.url = ""
        self.link_left.bind("<Button-1>", lambda e: self._open_url(getattr(self.link_left, "url", "")))
        self.link_right.bind("<Button-1>", lambda e: self._open_url(getattr(self.link_right, "url", "")))

        # ---- Links tools ----
        self.common_tags_var = tk.StringVar(value=DEFAULT_COMMON_TAGS)

        self.view_links_btn = tk.Button(self.sidebar, text="View/open e621 links",
                                        command=self.show_links_view,
                                        bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.db_stats_btn = tk.Button(self.sidebar, text="DB stats (I)",
                                      command=self.show_db_stats,
                                      bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.history_btn = tk.Button(self.sidebar, text="History / Rollback (H)",
                                     command=self.show_history_manager,
                                     bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")

        self.export_status = tk.Label(self.sidebar, text="", font=("Segoe UI", 9), fg=TEXT_COLOR, bg=DARK_BG)

        # ---- Keybind panel (compact list) ----
        self.keys_header = tk.Label(self.sidebar, text="Keybinds",
                                    font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.keys_text = tk.Label(self.sidebar, text=self._keybind_text(), justify="left",
                                  font=("Consolas", 9), fg=TEXT_COLOR, bg=DARK_BG)

        # Layout (sidebar)
        self.leader_header.pack(anchor="w")
        self.leader_controls_row.pack(fill="x", pady=(2, 4))
        self.board.pack(fill="x", pady=(4, 6))
        self.nav_row.pack(fill="x", pady=(0, 4))
        self.spark_controls_row.pack(fill="x", pady=(0, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.counters_header.pack(anchor="w", pady=(2, 0))
        self.counters_text.pack(anchor="w", pady=(2, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.now_header.pack(anchor="w")
        self.now.pack(anchor="w", pady=(2, 6))

        self.links_header.pack(anchor="w")
        self.link_left.pack(anchor="w")
        self.link_right.pack(anchor="w", pady=(0, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.view_links_btn.pack(fill="x", pady=(0, 2))
        self.db_stats_btn.pack(fill="x", pady=(0, 2))
        self.history_btn.pack(fill="x", pady=(0, 6))
        self.export_status.pack(anchor="w", pady=(0, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.keys_header.pack(anchor="w")
        self.keys_text.pack(anchor="w")

        # ---- Bottom carousel (history) ----
        self.carousel_frame = tk.Frame(self.root, bg=DARK_BG)
        self.carousel_frame.pack(side="bottom", fill="x")

        self.carousel_toggle_bar = tk.Frame(self.carousel_frame, bg=DARK_BG)
        self.carousel_toggle_bar.pack(fill="x", padx=6, pady=(0, 4))
        self.carousel_toggle_label = tk.Label(
            self.carousel_toggle_bar,
            text="History",
            font=("Segoe UI", 9),
            fg=TEXT_COLOR,
            bg=DARK_BG,
        )
        self.carousel_toggle_label.pack(side="left")
        self.carousel_toggle_label.bind("<ButtonPress-1>", self._on_carousel_drag_start)
        self.carousel_toggle_label.bind("<B1-Motion>", self._on_carousel_drag)
        self.carousel_toggle_label.bind("<ButtonRelease-1>", self._on_carousel_release)
        self.carousel_info = tk.Label(
            self.carousel_toggle_bar,
            text="History: 0",
            font=("Segoe UI", 9),
            fg=TEXT_COLOR,
            bg=DARK_BG,
        )
        self.carousel_info.pack(side="right")
        self.carousel_info.bind("<ButtonPress-1>", self._on_carousel_drag_start)
        self.carousel_info.bind("<B1-Motion>", self._on_carousel_drag)
        self.carousel_info.bind("<ButtonRelease-1>", self._on_carousel_release)
        self.carousel_handle_bar = tk.Frame(
            self.carousel_toggle_bar,
            bg="#e4e4e4",
            width=64,
            height=6,
        )
        self.carousel_handle_bar.place(relx=0.5, rely=0.5, anchor="center")
        self.carousel_handle_bar.bind("<ButtonPress-1>", self._on_carousel_drag_start)
        self.carousel_handle_bar.bind("<B1-Motion>", self._on_carousel_drag)
        self.carousel_handle_bar.bind("<ButtonRelease-1>", self._on_carousel_release)
        self.carousel_toggle_bar.bind("<ButtonPress-1>", self._on_carousel_drag_start, add="+")
        self.carousel_toggle_bar.bind("<B1-Motion>", self._on_carousel_drag, add="+")
        self.carousel_toggle_bar.bind("<ButtonRelease-1>", self._on_carousel_release, add="+")
        self.carousel_handle_bar.configure(cursor="sb_v_double_arrow")

        self.carousel_panel = tk.Frame(self.carousel_frame, bg=DARK_BG, height=self.carousel_height)
        self.carousel_panel.pack(side="bottom", fill="x", padx=6, pady=(0, 6))
        self.carousel_panel.pack_propagate(False)

        self.carousel_controls = tk.Frame(self.carousel_panel, bg=DARK_BG)
        self.carousel_controls.pack(fill="x")
        self.carousel_prev_btn = tk.Button(
            self.carousel_controls,
            text="Previous",
            command=self._on_carousel_prev,
            bg=DARK_PANEL,
            fg=TEXT_COLOR,
            activebackground=ACCENT,
            relief="flat",
            width=12,
        )
        self.carousel_prev_btn.pack(side="left")
        self.carousel_next_btn = tk.Button(
            self.carousel_controls,
            text="Next up",
            command=self._on_carousel_next,
            bg=DARK_PANEL,
            fg=TEXT_COLOR,
            activebackground=ACCENT,
            relief="flat",
            width=12,
        )
        self.carousel_next_btn.pack(side="right")

        self.carousel_strip = tk.Frame(self.carousel_panel, bg=DARK_BG)
        self.carousel_strip.pack(fill="x", pady=(4, 0))
        self.carousel_slots: List[tk.Button] = []
        self._carousel_slot_map: List[Optional[int]] = []
        self._carousel_slot_pack_opts = dict(side="left", fill="x", expand=True, padx=0, pady=0)
        for i in range(self.carousel_size):
            btn = tk.Button(
                self.carousel_strip,
                text="--",
                command=lambda idx=i: self._on_carousel_slot(idx),
                bg=DARK_PANEL,
                fg=TEXT_COLOR,
                activebackground=ACCENT,
                relief="flat",
                anchor="center",
                padx=0,
                pady=0,
                compound="top",
                font=("Segoe UI", 8),
                wraplength=180,
            )
            btn.pack(**self._carousel_slot_pack_opts)
            self.carousel_slots.append(btn)
            self._carousel_slot_map.append(None)

        # ---- Mouse controls ----
        self.left_panel.bind("<Button-1>", lambda e: self.choose("a"))
        self.right_panel.bind("<Button-1>", lambda e: self.choose("b"))
        self.left_panel.bind("<Control-Button-1>", lambda e: self._on_ctrl_options("a", e))
        self.right_panel.bind("<Control-Button-1>", lambda e: self._on_ctrl_options("b", e))
        self.left_panel.bind("<Double-Button-1>", self.open_left)
        self.right_panel.bind("<Double-Button-1>", self.open_right)
        self.left_panel.bind("<Button-3>", lambda e: self.skip_side("a"))
        self.right_panel.bind("<Button-3>", lambda e: self.skip_side("b"))

        # Hide: middle click
        self.left_panel.bind("<Button-2>", lambda e: self.hide_side("a"))
        self.right_panel.bind("<Button-2>", lambda e: self.hide_side("b"))

        # Also allow click on video frames
        for w, side in [(self.left_video, "a"), (self.right_video, "b")]:
            w.bind("<Control-Button-1>", lambda e, s=side: self._on_ctrl_options(s, e))
            w.bind("<Double-Button-1>", self.open_left if side == "a" else self.open_right)
            w.bind("<Button-1>", lambda e, s=side: self.choose("a" if s == "a" else "b"))
            w.bind("<Button-3>", lambda e, s=side: self.skip_side(s))
            w.bind("<Button-2>", lambda e, s=side: self.hide_side(s))

        # ---- Keybinds ----
        root.bind("1", lambda e: self.choose("a"))
        root.bind("2", lambda e: self.choose("b"))
        root.bind("3", lambda e: self.focus_side("a"))
        root.bind("6", lambda e: self.focus_side("b"))
        root.bind("7", lambda e: self.skip_side("a"))
        root.bind("8", lambda e: self.skip_side("b"))
        root.bind("9", lambda e: self.toggle_sidebar())
        root.bind("0", lambda e: self.choose(None))
        root.bind(".", lambda e: self.toggle_blur())

        root.bind("q", lambda e: self.quit())
        root.bind("h", lambda e: self.show_history_manager())

        root.bind("<Configure>", self._on_configure)
        root.bind("<FocusOut>", self._on_window_focus_out, add="+")
        root.bind("<FocusIn>", self._on_window_focus_in, add="+")
        # Route the window-close (X) button through quit() so the session is closed cleanly.
        root.protocol("WM_DELETE_WINDOW", self.quit)

        # Start periodic UI tick (scrub/time updates)
        self._tick_job = None
        self._tick()

        # Open a live session (stamps every new comparison) + take an auto start-of-session snapshot.
        self._open_session()

        self._toggle_carousel()
        self.load_duel()

        # Background sweep: find DB rows whose file is gone from disk, log a summary, and
        # populate self._missing_ids so the picker skips them. Off-thread so startup is instant.
        self._start_missing_scan()

    # -------------------- helpers / state --------------------
    def _ensure_ui_tooltip(self):
        if getattr(self, "_ui_tip_win", None) is None:
            self._ui_tip_win = tk.Toplevel(self.root)
            self._ui_tip_win.overrideredirect(True)
            self._ui_tip_win.attributes("-topmost", True)
            self._ui_tip_win.withdraw()
            self._ui_tip = tk.Label(
                self._ui_tip_win,
                text="",
                bg="#111111",
                fg=TEXT_COLOR,
                font=("Segoe UI", 8),
                bd=1,
                relief="solid",
                padx=6,
                pady=2,
            )
            self._ui_tip.pack()

    def _show_ui_tooltip_at_pointer(self, text: str):
        self._ensure_ui_tooltip()
        self._ui_tip.configure(text=text)
        self._ui_tip.update_idletasks()
        x_root = self.root.winfo_pointerx() + 12
        y_root = self.root.winfo_pointery() + 14
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        tw = max(10, self._ui_tip.winfo_reqwidth())
        th = max(10, self._ui_tip.winfo_reqheight())
        x_root = max(4, min(sw - tw - 4, x_root))
        y_root = max(4, min(sh - th - 4, y_root))
        self._ui_tip_win.geometry(f"+{x_root}+{y_root}")
        self._ui_tip_win.deiconify()
        self._ui_tip_win.lift()

    def _hide_ui_tooltip(self, _event=None):
        tip_win = getattr(self, "_ui_tip_win", None)
        if tip_win is not None:
            tip_win.withdraw()

    def _new_side_state(self) -> dict:
        return {
            "row": None,
            "media_kind": None,   # "image" | "gif" | "video"
            "anim_job": None,
            "anim_frames": None,
            "anim_delays": None,
            "anim_index": 0,
            "gif_render_token": 0,
            "last_visual_size": None,

            "vlc_player": None,
            "vlc_media": None,
            "vlc_ready": False,
            "vlc_init_job": None,
            "vlc_play_pending": False,
            "vlc_was_playing_before_seek": False,
            "vlc_total_ms": None,
            "vlc_loop": True,
            "vlc_event_mgr": None,
            "video_blur_label": None,
            "video_blur_image": None,
            "video_blur_logo_path": None,

            "scrubbing": False,
            "tags": [],
            "tag_vars": {},
            "tag_button": None,
            "action_buttons": {},
            "last_replaced_row": None,
        }

    def _toggle_carousel(self) -> None:
        self.carousel_visible = not self.carousel_visible
        if self.carousel_visible:
            if self.carousel_height < self.carousel_min_height:
                self.carousel_height = self.carousel_default_height
            self.carousel_panel.configure(height=self.carousel_height)
            self.carousel_panel.pack(side="bottom", fill="x", padx=6, pady=(0, 6))
        else:
            self.carousel_panel.pack_forget()
        self._update_carousel()

    def _show_carousel(self, height: Optional[int] = None) -> None:
        if height is not None:
            self.carousel_height = max(self.carousel_min_height, min(self.carousel_max_height, height))
            self.carousel_panel.configure(height=self.carousel_height)
        if not self.carousel_visible:
            self.carousel_visible = True
            self.carousel_panel.pack(side="bottom", fill="x", padx=6, pady=(0, 6))
        self._update_carousel()

    def _on_carousel_drag_start(self, event) -> None:
        self._carousel_drag_start = event.y_root
        self._carousel_drag_start_height = self.carousel_height
        self._carousel_drag_started_visible = self.carousel_visible
        self._carousel_dragging = False

    def _on_carousel_drag(self, event) -> None:
        if self._carousel_drag_start is None:
            return
        delta = event.y_root - self._carousel_drag_start
        if abs(delta) < 4:
            return
        self._carousel_dragging = True

        if not self._carousel_drag_started_visible:
            if delta >= 0:
                return
            drag_open_height = min(self.carousel_max_height, max(self.carousel_min_height, int(-delta)))
            if not self.carousel_visible:
                self._show_carousel(drag_open_height)
            elif drag_open_height != self.carousel_height:
                self.carousel_height = drag_open_height
                self.carousel_panel.configure(height=self.carousel_height)
                self._update_carousel()
            return

        base = self._carousel_drag_start_height or self.carousel_height
        new_height = int(base - delta)
        new_height = max(0, min(self.carousel_max_height, new_height))
        if new_height != self.carousel_height:
            self.carousel_height = new_height
            self.carousel_panel.configure(height=self.carousel_height)
            self._update_carousel()

    def _on_carousel_release(self, event) -> None:
        if self._carousel_drag_start is None:
            return
        delta = event.y_root - self._carousel_drag_start
        started_visible = self._carousel_drag_started_visible

        if self._carousel_dragging:
            if started_visible:
                if delta > 60 or self.carousel_height <= 0:
                    self._toggle_carousel()
                elif self.carousel_height < self.carousel_min_height:
                    self.carousel_height = self.carousel_min_height
                    if self.carousel_visible:
                        self.carousel_panel.configure(height=self.carousel_height)
                        self._update_carousel()
            else:
                if not self.carousel_visible:
                    self._toggle_carousel()
        else:
            self._toggle_carousel()

        self._carousel_drag_start = None
        self._carousel_drag_start_height = None
        self._carousel_drag_started_visible = False
        self._carousel_dragging = False

    def _update_carousel_layout(self, slot_count: int) -> None:
        if not self.carousel_visible:
            return
        self.root.update_idletasks()
        panel_width = max(1, self.carousel_panel.winfo_width())
        controls_h = max(1, self.carousel_controls.winfo_height())
        strip_padding = 2
        label_height = 20
        strip_height = max(40, self.carousel_height - controls_h - strip_padding)
        slot_gap = 0
        slot_count = max(1, slot_count)
        slot_width = max(80, int(panel_width / slot_count) - slot_gap)
        thumb_width = max(36, int(slot_width / 2) - 1)
        thumb_height = max(36, strip_height - label_height)
        new_size = (thumb_width, thumb_height)
        if new_size != self.carousel_thumb_size:
            self.carousel_thumb_size = new_size
            for btn in self.carousel_slots:
                btn.configure(image="")
            for entry in self.duel_history:
                entry["thumb"] = None
            for fentry in self.future_queue:
                fentry["thumb"] = None

    def _make_thumb_image(self, path: str) -> Image.Image:
        w, h = self.carousel_thumb_size
        try:
            ext = Path(path).suffix.lower()
            if ext in VIDEO_EXTS:
                ffmpeg = self._ffmpeg_exe()
                if ffmpeg and os.path.exists(path):
                    try:
                        cmd = [
                            ffmpeg,
                            "-hide_banner",
                            "-loglevel",
                            "error",
                            "-ss",
                            "00:00:01",
                            "-i",
                            path,
                            "-frames:v",
                            "1",
                            "-f",
                            "image2pipe",
                            "-vcodec",
                            "png",
                            "-",
                        ]
                        r = subprocess.run(
                            cmd,
                            check=False,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                        )
                        if r.stdout:
                            im = Image.open(io.BytesIO(r.stdout)).convert("RGB")
                            im.thumbnail((w, h))
                            canvas = Image.new("RGB", (w, h), "#111111")
                            offset = ((w - im.width) // 2, (h - im.height) // 2)
                            canvas.paste(im, offset)
                            return canvas
                    except Exception:
                        pass
                img = Image.new("RGB", (w, h), "#111111")
                draw = ImageDraw.Draw(img)
                draw.text((8, h // 2 - 7), "VIDEO", fill="#d0d0d0")
                return img
            im = Image.open(path)
            if ext in GIF_EXTS:
                im.seek(0)
            im = im.convert("RGB")
            im.thumbnail((w, h))
            canvas = Image.new("RGB", (w, h), "#111111")
            offset = ((w - im.width) // 2, (h - im.height) // 2)
            canvas.paste(im, offset)
            return canvas
        except Exception as ex:
            print(f"[thumb] FAILED: {path!r}")
            print(f"[thumb]   error: {type(ex).__name__}: {ex}")
            print(f"[thumb]   file:  {describe_file_state(path)}")
            img = Image.new("RGB", (w, h), "#111111")
            draw = ImageDraw.Draw(img)
            draw.text((8, h // 2 - 7), "N/A", fill="#d0d0d0")
            return img

    def _build_duel_thumbnail(self, left_path: str, right_path: str, sensitive: bool = False) -> ImageTk.PhotoImage:
        w, h = self.carousel_thumb_size
        left = self._make_thumb_image(left_path)
        right = self._make_thumb_image(right_path)
        if sensitive:
            left = self._apply_pixelate(left, pixel_size=50)
            right = self._apply_pixelate(right, pixel_size=50)
        elif self.blur_enabled:
            left = self._apply_pixelate(left, pixel_size=14)
            right = self._apply_pixelate(right, pixel_size=14)
        composite = Image.new("RGB", (w * 2 + 2, h), "#000000")
        composite.paste(left, (0, 0))
        composite.paste(right, (w + 2, 0))
        return ImageTk.PhotoImage(composite)

    def _entry_is_sensitive(self, entry: dict) -> bool:
        a_parsed = set(self._parse_tags(entry.get("a_tags") or ""))
        b_parsed = set(self._parse_tags(entry.get("b_tags") or ""))
        return bool((a_parsed | b_parsed) & BLUR_TAGS)

    def _pair_is_sensitive(self, row_a: tuple, row_b: tuple) -> bool:
        a_tags = set(self._tags_for_row(row_a))
        b_tags = set(self._tags_for_row(row_b))
        return bool((a_tags | b_tags) & BLUR_TAGS)

    def _entry_sensitive_label(self, entry: dict) -> str:
        a_tags = set(self._parse_tags(entry.get("a_tags") or "")) & BLUR_TAGS
        b_tags = set(self._parse_tags(entry.get("b_tags") or "")) & BLUR_TAGS
        left  = ", ".join(sorted(a_tags)) if a_tags else self._truncate_label(Path(entry["a_path"]).name, 18)
        right = ", ".join(sorted(b_tags)) if b_tags else self._truncate_label(Path(entry["b_path"]).name, 18)
        return f"{left}, {right}"

    def _pair_sensitive_label(self, row_a: tuple, row_b: tuple) -> str:
        a_tags = set(self._tags_for_row(row_a)) & BLUR_TAGS
        b_tags = set(self._tags_for_row(row_b)) & BLUR_TAGS
        left  = ", ".join(sorted(a_tags)) if a_tags else self._truncate_label(Path(row_a[1]).name, 18)
        right = ", ".join(sorted(b_tags)) if b_tags else self._truncate_label(Path(row_b[1]).name, 18)
        return f"{left}, {right}"

    def _tag_usage_counts(self) -> dict:
        counts: dict = {t: 0 for t in TAG_OPTIONS}
        for (raw_tags,) in self.conn.execute(
            "SELECT tags FROM images WHERE tags IS NOT NULL AND tags != ''"
        ):
            for t in self._parse_tags(raw_tags):
                counts[t] = counts.get(t, 0) + 1
        return counts

    def _attach_history_thumbs(self, entry: dict) -> None:
        if self._entry_is_sensitive(entry):
            # thumb = clear (used when this slot is the active/selected one),
            # thumb_blurred = heavy pixelation (used when not selected).
            # Build thumb without blur_enabled so it stays clear regardless of focus state.
            saved = self.blur_enabled
            self.blur_enabled = False
            entry["thumb"] = self._build_duel_thumbnail(entry["a_path"], entry["b_path"])
            self.blur_enabled = saved
            entry["thumb_blurred"] = self._build_duel_thumbnail(entry["a_path"], entry["b_path"], sensitive=True)
        else:
            entry["thumb"] = self._build_duel_thumbnail(entry["a_path"], entry["b_path"])

    def _fetch_row(self, img_id: int) -> Optional[tuple]:
        row = self.conn.execute("""
            SELECT id, path, folder, duels, wins, losses, score, hidden, tags
            FROM images
            WHERE id=?
        """, (img_id,)).fetchone()
        return row

    def _truncate_label(self, text: str, limit: int = 26) -> str:
        if len(text) <= limit:
            return text
        return text[: max(0, limit - 1)].rstrip() + "…"

    def _history_label(self, entry: dict) -> str:
        left = self._truncate_label(Path(entry["a_path"]).name, 18)
        right = self._truncate_label(Path(entry["b_path"]).name, 18)
        return f"{left} vs {right}"

    def _pair_label(self, pair: Optional[Tuple[tuple, tuple]]) -> str:
        """Short label for a live or future (row_a, row_b) pair."""
        if not pair:
            return "?"
        a, b = pair
        left  = self._truncate_label(Path(a[1]).name, 18)
        right = self._truncate_label(Path(b[1]).name, 18)
        return f"{left} vs {right}"

    def _enter_history_mode(self, index: int) -> None:
        if self.history_index is None:
            self.live_current = self.current
        self.history_index = index
        self._show_history_entry(index)

    def _exit_history_mode(self) -> None:
        self.history_index = None
        if self.live_current:
            a, b = self.live_current
            self._set_current(a, b)
            self._update_info_bars(a, b)
            self._render_side("a")
            self._render_side("b")
            self.update_sidebar()
        self._update_carousel()

    def _show_history_entry(self, index: int) -> None:
        if index < 0 or index >= len(self.duel_history):
            return
        entry = self.duel_history[index]
        if entry.get("thumb") is None:
            self._attach_history_thumbs(entry)
        a = self._fetch_row(entry["a_id"])
        b = self._fetch_row(entry["b_id"])
        if not a or not b:
            return
        self._stop_video("a")
        self._stop_video("b")
        self._set_current(a, b)
        self._update_info_bars(a, b)
        self._render_side("a")
        self._render_side("b")
        self.update_sidebar()
        self._update_carousel()

    def _apply_revote(self, index: int, winner: Optional[str]) -> None:
        if index < 0 or index >= len(self.duel_history):
            return
        entry = self.duel_history[index]
        a_id = entry["a_id"]
        b_id = entry["b_id"]
        before_a = entry["before_a"]
        before_b = entry["before_b"]

        prev_winner = entry.get("winner")
        chosen_id = None

        # Determine new scores and new stat increments
        if winner == "a":
            new_a, new_b = elo_update(before_a["score"], before_b["score"], True)
            chosen_id = a_id
            new_a_wins, new_a_losses, new_b_wins, new_b_losses = 1, 0, 0, 1
        elif winner == "b":
            new_a, new_b = elo_update(before_a["score"], before_b["score"], False)
            chosen_id = b_id
            new_a_wins, new_a_losses, new_b_wins, new_b_losses = 0, 1, 1, 0
        elif winner == "downvote":
            new_a, new_b = before_a["score"] - DOWNVOTE_PENALTY, before_b["score"] - DOWNVOTE_PENALTY
            new_a_wins, new_a_losses, new_b_wins, new_b_losses = 0, 1, 0, 1
        else:  # tie / None
            new_a, new_b = elo_update(before_a["score"], before_b["score"], None)
            new_a_wins, new_a_losses, new_b_wins, new_b_losses = 0, 0, 0, 0

        # Determine what the previous vote had already credited
        if prev_winner == "a":
            old_a_wins, old_a_losses, old_b_wins, old_b_losses = 1, 0, 0, 1
        elif prev_winner == "b":
            old_a_wins, old_a_losses, old_b_wins, old_b_losses = 0, 1, 1, 0
        elif prev_winner == "downvote":
            old_a_wins, old_a_losses, old_b_wins, old_b_losses = 0, 1, 0, 1
        else:  # tie / None / first vote
            old_a_wins, old_a_losses, old_b_wins, old_b_losses = 0, 0, 0, 0

        # Apply only the delta — never touch duels count on a revote
        a_wins_delta = new_a_wins - old_a_wins
        a_losses_delta = new_a_losses - old_a_losses
        b_wins_delta = new_b_wins - old_b_wins
        b_losses_delta = new_b_losses - old_b_losses

        ts = int(time.time())
        self.conn.execute(
            "UPDATE images SET score=?, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
            (new_a, a_wins_delta, a_losses_delta, ts, a_id),
        )
        self.conn.execute(
            "UPDATE images SET score=?, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
            (new_b, b_wins_delta, b_losses_delta, ts, b_id),
        )
        if entry.get("comparison_id"):
            # Keep the reversible-log columns consistent on a revote. before-scores are fixed at
            # record time and must NOT change here; only outcome + after-scores move. duels is never
            # touched (revote rule).
            outcome = {"a": "left", "b": "right", "downvote": "downvote"}.get(winner, "tie")
            self.conn.execute(
                "UPDATE comparisons SET chosen_id=?, outcome=?, left_score_after=?, right_score_after=?, ts=? WHERE id=?",
                (chosen_id, outcome, float(new_a), float(new_b), ts, entry["comparison_id"]),
            )
        self.conn.commit()
        entry["winner"] = winner

        try:
            threading.Thread(
                target=update_image_metadata,
                args=(Path(entry["a_path"]), float(new_a)),
                daemon=True,
            ).start()
            threading.Thread(
                target=update_image_metadata,
                args=(Path(entry["b_path"]), float(new_b)),
                daemon=True,
            ).start()
        except Exception:
            pass

    def _create_history_sub_duel(self, parent_index: int, tagged_row: tuple, tagged_side: str) -> None:
        """
        Called when a tag is changed on a file that's part of a history/edit-mode entry.

        Actions:
          1. Nullify the parent duel's vote (apply as a tie so scores are adjusted).
          2. Replace the tagged slot in the parent duel with a fresh random pick.
          3. Insert a new sub-duel (e.g. "10.1") immediately after the parent,
             pairing the tagged file against yet another fresh pick.
          4. Navigate to the sub-duel so the user can vote on it.
        """
        entry = self.duel_history[parent_index]
        other_id = entry["b_id"] if tagged_side == "a" else entry["a_id"]
        other_row = self._fetch_row(other_id)
        if not other_row:
            return

        # 1. Nullify the parent vote (convert to tie/skip).
        self._apply_revote(parent_index, None)
        entry["winner"] = None
        entry["thumb"] = None  # force thumbnail refresh

        # 2. Roll replacements from the live pool.
        pool = self._pool_rows()
        tagged_kind = self._media_kind(tagged_row[1])

        # Fresh file for the parent duel's now-vacant slot.
        replacement = self.pick_one(
            exclude_id=other_id,
            pool=pool,
            required_kind=tagged_kind,
            required_tags=self._match_tags(other_row),
        )

        # New opponent for the sub-duel (matched to the tagged file's new tags).
        sub_opponent = self.pick_one(
            exclude_id=tagged_row[0],
            pool=pool,
            required_kind=tagged_kind,
            required_tags=self._match_tags(tagged_row),
        )

        # 3. Patch the parent entry so it shows the replacement instead of the tagged file.
        if replacement:
            if tagged_side == "a":
                entry["a_id"]   = replacement[0]
                entry["a_path"] = replacement[1]
            else:
                entry["b_id"]   = replacement[0]
                entry["b_path"] = replacement[1]
            # Refresh pre-duel snapshots for the updated pair.
            entry["before_a"] = _snapshot_stats(self.conn, entry["a_id"])
            entry["before_b"] = _snapshot_stats(self.conn, entry["b_id"])

        if not sub_opponent:
            # No room for a sub-duel — just refresh the parent.
            self._show_history_entry(parent_index)
            self._update_carousel()
            return

        # 4. Build the sub-label (e.g. "10.1", "10.2" for subsequent tag changes).
        parent_label = entry.get("sub_label") or str(parent_index + 1)
        existing_subs = sum(
            1 for e in self.duel_history
            if str(e.get("sub_label", "")).startswith(f"{parent_label}.")
        )
        sub_label = f"{parent_label}.{existing_subs + 1}"

        if tagged_side == "a":
            sub_a, sub_b = tagged_row, sub_opponent
        else:
            sub_a, sub_b = sub_opponent, tagged_row

        sub_entry: dict = {
            "a_id":          sub_a[0],
            "b_id":          sub_b[0],
            "a_path":        sub_a[1],
            "b_path":        sub_b[1],
            "a_tags":        sub_a[8] if len(sub_a) > 8 else "",
            "b_tags":        sub_b[8] if len(sub_b) > 8 else "",
            "winner":        None,
            "comparison_id": None,   # no DB row yet; created on first vote
            "before_a":      _snapshot_stats(self.conn, sub_a[0]),
            "before_b":      _snapshot_stats(self.conn, sub_b[0]),
            "thumb":         None,
            "sub_label":     sub_label,
        }

        insert_at = parent_index + 1
        self.duel_history.insert(insert_at, sub_entry)

        # If we inserted before the current history cursor, shift it.
        if self.history_index is not None and insert_at <= self.history_index:
            self.history_index += 1

        print(f"[sub-duel] {sub_label}: {Path(sub_a[1]).name} vs {Path(sub_b[1]).name}")

        # Stay on the parent duel so the user can cast their vote first.
        # The sub-duel appears highlighted in the carousel as a pending item.
        self._show_history_entry(parent_index)
        self._update_carousel()

    def _on_carousel_prev(self) -> None:
        if not self.duel_history:
            return
        if self.history_index is None:
            index = len(self.duel_history) - 1
        else:
            index = max(0, self.history_index - 1)
        self._enter_history_mode(index)

    def _on_carousel_next(self) -> None:
        if self.history_index is None:
            # Live mode: advance into the first future duel (skip current)
            if self.future_queue:
                self._jump_to_future(0)
            return
        if self.history_index < len(self.duel_history) - 1:
            self._enter_history_mode(self.history_index + 1)
        else:
            self._exit_history_mode()

    def _on_carousel_slot(self, slot_idx: int) -> None:
        if slot_idx < 0 or slot_idx >= len(self._carousel_slot_map):
            return
        slot_val = self._carousel_slot_map[slot_idx]
        if slot_val is None:
            return
        if isinstance(slot_val, int):
            # Past history entry
            self._enter_history_mode(slot_val)
        elif slot_val == "live":
            # Live current — exit edit mode if we're in it
            if self.history_index is not None:
                self._exit_history_mode()
        elif isinstance(slot_val, tuple) and slot_val[0] == "future":
            # Future pre-rolled duel — jump to it, skipping everything before
            self._jump_to_future(slot_val[1])

    def _update_carousel(self) -> None:
        total = len(self.duel_history)
        if not self.carousel_visible:
            self.carousel_info.configure(text=f"History: {total} (collapsed)")
            self.carousel_prev_btn.configure(state="disabled")
            self.carousel_next_btn.configure(state="disabled")
            return
        # total==0 with no future queue: all slots empty
        if total == 0 and not self.future_queue and self.history_index is None:
            self.carousel_info.configure(text="History: 0")
            self.carousel_prev_btn.configure(state="disabled")
            self.carousel_next_btn.configure(state="disabled")
            for i, btn in enumerate(self.carousel_slots):
                btn.pack_forget()
                btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                self._carousel_slot_map[i] = None
            return

        if self.history_index is None:
            # ---- Live mode ----
            # Virtual timeline: [history 0..total-1] [live★] [future 0..M-1]
            # "live" sits at virtual position = total
            future_count = len(self.future_queue)
            timeline_len = total + 1 + future_count
            live_virtual = total

            half = self.carousel_size // 2
            win_start = max(0, live_virtual - half)
            win_end   = min(timeline_len - 1, win_start + self.carousel_size - 1)
            win_start = max(0, win_end - (self.carousel_size - 1))
            virtual_indices = list(range(win_start, win_end + 1))

            self._update_carousel_layout(len(virtual_indices))

            for i, btn in enumerate(self.carousel_slots):
                btn.configure(image="")
                if i < len(virtual_indices):
                    vi = virtual_indices[i]
                    btn.configure(wraplength=max(120, self.carousel_thumb_size[0] * 2))
                    if vi < total:
                        # Past history slot
                        entry = self.duel_history[vi]
                        display_num = entry.get("sub_label") or str(vi + 1)
                        if entry.get("thumb") is None:
                            self._attach_history_thumbs(entry)
                        is_pending = (entry.get("sub_label") and entry.get("comparison_id") is None)
                        slot_bg = PENDING_COLOR if is_pending else DARK_PANEL
                        if self._entry_is_sensitive(entry):
                            label = f"{display_num}. {self._entry_sensitive_label(entry)}"
                            thumb = entry.get("thumb_blurred") or entry.get("thumb", "")
                        else:
                            label = f"{display_num}. {self._history_label(entry)}"
                            thumb = entry.get("thumb", "")
                        btn.configure(text=label, state="normal", bg=slot_bg, image=thumb)
                        self._carousel_slot_map[i] = vi
                    elif vi == live_virtual:
                        # Live current slot — always revealed (user is actively viewing this duel)
                        if self.solo_mode and self.live_current:
                            solo_a = self.live_current[0]
                            solo_name = self._truncate_label(Path(solo_a[1]).name, 22)
                            label = f"★ {total + 1}. {solo_name} (unmatched)"
                            btn.configure(text=label, state="normal", bg=ACCENT, image="")
                        elif self.live_current:
                            a, b = self.live_current
                            label = f"★ {total + 1}. {self._pair_label(self.live_current)}"
                            if not hasattr(self, "_live_thumb") or self._live_thumb_key != (a[0], b[0]):
                                self._live_thumb = self._build_duel_thumbnail(a[1], b[1])
                                self._live_thumb_key = (a[0], b[0])
                            btn.configure(text=label, state="normal", bg=ACCENT,
                                          image=self._live_thumb)
                        else:
                            label = f"★ {total + 1}. ?"
                            btn.configure(text=label, state="normal", bg=ACCENT, image="")
                        self._carousel_slot_map[i] = "live"
                    else:
                        # Future duel slot
                        fi = vi - total - 1
                        fentry = self.future_queue[fi]
                        fa, fb = fentry["a"], fentry["b"]
                        if fb is None:
                            # Solo placeholder: no opponent in the tag group
                            solo_name = self._truncate_label(Path(fa[1]).name, 22)
                            label = f"~{total + fi + 2}. {solo_name} (unmatched)"
                            btn.configure(text=label, state="normal", bg=FUTURE_COLOR, image="")
                            fentry["thumb"] = ""  # mark as resolved so we don't re-check
                        else:
                            future_sensitive = self._pair_is_sensitive(fa, fb)
                            if future_sensitive:
                                label = f"~{total + fi + 2}. {self._pair_sensitive_label(fa, fb)}"
                            else:
                                label = f"~{total + fi + 2}. {self._pair_label((fa, fb))}"
                            if fentry["thumb"] is None:
                                # Build thumbnail in a daemon thread to avoid blocking the UI
                                def _build_future_thumb(fe=fentry, sens=future_sensitive):
                                    fe["thumb"] = self._build_duel_thumbnail(fe["a"][1], fe["b"][1], sensitive=sens)
                                    self.root.after(0, self._update_carousel)
                                threading.Thread(target=_build_future_thumb, daemon=True).start()
                            btn.configure(text=label, state="normal", bg=FUTURE_COLOR,
                                          image=fentry["thumb"] or "")
                        self._carousel_slot_map[i] = ("future", fi)
                    if not btn.winfo_ismapped():
                        btn.pack(**self._carousel_slot_pack_opts)
                else:
                    btn.pack_forget()
                    btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                    self._carousel_slot_map[i] = None

            upcoming = f" | +{future_count} upcoming" if future_count else ""
            self.carousel_info.configure(text=f"History: {total} (live){upcoming}")
            self.carousel_prev_btn.configure(state="normal" if total > 0 else "disabled")
            self.carousel_next_btn.configure(state="normal" if self.future_queue else "disabled")

        else:
            # ---- Edit mode: center the active duel, history left, newer/sub-duels right ----
            active_index = self.history_index
            half = self.carousel_size // 2
            win_start = max(0, active_index - half)
            # Don't clamp win_end — allow indices past total so the active slot
            # stays centered even when it's the last history entry.
            indices = list(range(win_start, win_start + self.carousel_size))

            self._update_carousel_layout(self.carousel_size)

            for i, btn in enumerate(self.carousel_slots):
                btn.configure(image="")
                if i < len(indices):
                    idx = indices[i]
                    if idx >= total:
                        # Padding slot beyond end of history — keep it visible but empty
                        btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                        self._carousel_slot_map[i] = None
                        if not btn.winfo_ismapped():
                            btn.pack(**self._carousel_slot_pack_opts)
                        continue
                    entry = self.duel_history[idx]
                    display_num = entry.get("sub_label") or str(idx + 1)
                    if entry.get("thumb") is None:
                        self._attach_history_thumbs(entry)
                    btn.configure(wraplength=max(120, self.carousel_thumb_size[0] * 2))
                    is_active  = (idx == active_index)
                    is_pending = (entry.get("sub_label") and entry.get("comparison_id") is None)
                    slot_bg    = ACCENT if is_active else (PENDING_COLOR if is_pending else DARK_PANEL)
                    if not is_active and self._entry_is_sensitive(entry):
                        label = f"{display_num}. {self._entry_sensitive_label(entry)}"
                        thumb = entry.get("thumb_blurred") or entry.get("thumb", "")
                    else:
                        label = f"{display_num}. {self._history_label(entry)}"
                        thumb = entry.get("thumb", "")
                    btn.configure(
                        text=label,
                        state="normal",
                        bg=slot_bg,
                        image=thumb,
                    )
                    self._carousel_slot_map[i] = idx
                    if not btn.winfo_ismapped():
                        btn.pack(**self._carousel_slot_pack_opts)
                else:
                    btn.pack_forget()
                    btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                    self._carousel_slot_map[i] = None

            self.carousel_info.configure(
                text=f"History: {self.history_index + 1}/{total} (edit mode)",
            )
            self.carousel_prev_btn.configure(state="normal" if self.history_index > 0 else "disabled")
            self.carousel_next_btn.configure(state="normal")

    def _build_tag_menu(self, side: str, parent: tk.Frame) -> None:
        button = tk.Button(
            parent,
            text="Tags: (none)",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG,
            bg=INFO_BAR_BG,
            activebackground=INFO_BAR_BG,
            activeforeground=INFO_BAR_FG,
            relief="flat",
            cursor="hand2",
            command=lambda s=side: self._show_custom_tag_menu(s),
        )
        button.grid(row=0, column=2, sticky="e", padx=8, pady=2)
        tag_vars: dict = {}
        for tag in TAG_OPTIONS:
            tag_vars[tag] = tk.BooleanVar(value=False)
        self._side[side]["tag_vars"] = tag_vars
        self._side[side]["tag_button"] = button

    def _rebuild_all_tag_menus(self) -> None:
        usage = self._tag_usage_counts()
        sorted_tags = sorted(TAG_OPTIONS, key=lambda t: (-usage.get(t, 0), t))
        for side in ("a", "b"):
            old_vars = self._side[side].get("tag_vars", {})
            new_vars: dict = {}
            for tag in sorted_tags:
                new_vars[tag] = old_vars.get(tag, tk.BooleanVar(value=False))
            self._side[side]["tag_vars"] = new_vars
            row = self._side[side].get("row")
            if row:
                tags = self._tags_for_row(row)
                for tag, var in new_vars.items():
                    var.set(tag in tags)
                self._side[side]["tags"] = [t for t in tags if t in TAG_OPTIONS]
            self._set_tag_button_label(side)
        new_filter_menu = tk.Menu(self.tag_filter_btn, tearoff=0)
        new_filter_vars: dict = {}
        for tag in sorted_tags:
            var = self.tag_filter_vars.get(tag) or tk.BooleanVar(value=False)
            new_filter_vars[tag] = var
            new_filter_menu.add_checkbutton(
                label=tag,
                variable=var,
                command=self.on_tag_filter_change,
            )
        self.tag_filter_vars = new_filter_vars
        self.tag_filter_menu = new_filter_menu
        self.tag_filter_btn.configure(menu=new_filter_menu)
        self._update_tag_filter_button_label()

    def _show_custom_tag_menu(self, side: str) -> None:
        PROTECTED = {"HIDE", "SFW"}
        MENU_BG    = "#1c1c1e"
        MENU_HOVER = "#094771"
        MENU_SEP   = "#3c3c3c"
        MENU_FG    = "#d4d4d4"
        MENU_FG_DIM = "#666666"

        tag_vars = self._side[side]["tag_vars"]
        edit_mode = [False]
        pending_removes: set = set()
        pending_adds: list = []
        entry_ref = [None]   # holds the live Entry widget so _has_changes can read it

        trigger_btn = self._side[side].get("tag_button")
        if trigger_btn:
            bx = trigger_btn.winfo_rootx()
            by = trigger_btn.winfo_rooty() + trigger_btn.winfo_height()
        else:
            bx = self.root.winfo_pointerx()
            by = self.root.winfo_pointery()

        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.configure(bg=MENU_SEP)

        content = tk.Frame(win, bg=MENU_BG)
        content.pack(fill="both", expand=True, padx=1, pady=1)

        def _hover(row, widgets, on):
            bg = MENU_HOVER if on else MENU_BG
            row.configure(bg=bg)
            for w in widgets:
                try:
                    w.configure(bg=bg)
                except tk.TclError:
                    pass

        def _bind_hover(row, widgets):
            wlist = widgets[:]
            row.bind("<Enter>", lambda e: _hover(row, wlist, True))
            row.bind("<Leave>", lambda e: _hover(row, wlist, False))
            for w in wlist:
                w.bind("<Enter>", lambda e: _hover(row, wlist, True))
                w.bind("<Leave>", lambda e: _hover(row, wlist, False))

        def rebuild():
            entry_ref[0] = None
            for w in content.winfo_children():
                w.destroy()

            # ── tag rows ──────────────────────────────────────────────
            _usage = self._tag_usage_counts()
            _sorted = sorted(TAG_OPTIONS, key=lambda t: (-_usage.get(t, 0), t))
            for tag in _sorted + [t for t in pending_adds if t not in TAG_OPTIONS]:
                is_new      = tag in pending_adds
                is_existing = tag in TAG_OPTIONS
                protected   = is_existing and tag in PROTECTED
                marked      = is_existing and tag in pending_removes

                row = tk.Frame(content, bg=MENU_BG)
                row.pack(fill="x")

                # checkmark column
                if is_existing:
                    var = tag_vars.get(tag)
                    ck = tk.Label(row, text="✓" if (var and var.get()) else " ",
                                  width=2, bg=MENU_BG,
                                  fg=MENU_FG if not marked else MENU_FG_DIM,
                                  font=("Segoe UI", 9), anchor="center")
                else:
                    ck = tk.Label(row, text=" ", width=2, bg=MENU_BG,
                                  font=("Segoe UI", 9), anchor="center")
                ck.pack(side="left", padx=(2, 0))

                if marked:
                    fg, fnt = MENU_FG_DIM, ("Segoe UI", 9, "overstrike")
                elif protected or (is_existing and not is_new):
                    fg, fnt = (MENU_FG_DIM if (protected and edit_mode[0]) else MENU_FG), ("Segoe UI", 9)
                else:
                    fg, fnt = "#4aaa88", ("Segoe UI", 9)

                lbl = tk.Label(row, text=tag, bg=MENU_BG, fg=fg, font=fnt,
                               anchor="w", padx=4, pady=3)
                lbl.pack(side="left", fill="x", expand=True)
                row_ws = [ck, lbl]

                if not edit_mode[0]:
                    if is_existing:
                        def _toggle(e=None, t=tag):
                            v = tag_vars.get(t)
                            if v:
                                v.set(not v.get())
                            self._on_tag_change(side)
                            win.destroy()
                        for w in [row, ck, lbl]:
                            w.bind("<Button-1>", _toggle)
                        _bind_hover(row, [ck, lbl])
                else:
                    if protected:
                        pl = tk.Label(row, text="protected", bg=MENU_BG, fg=MENU_FG_DIM,
                                      font=("Segoe UI", 7), padx=6)
                        pl.pack(side="right")
                        row_ws.append(pl)
                    elif is_existing and not marked:
                        xl = tk.Label(row, text="×", bg=MENU_BG, fg="#cc4444",
                                      font=("Segoe UI", 11, "bold"), cursor="hand2", padx=8)
                        xl.pack(side="right")
                        row_ws.append(xl)
                        xl.bind("<Button-1>", lambda e, t=tag: (pending_removes.add(t), rebuild()))
                    elif is_existing and marked:
                        ul = tk.Label(row, text="undo", bg=MENU_BG, fg="#888",
                                      font=("Segoe UI", 7), cursor="hand2", padx=6)
                        ul.pack(side="right")
                        row_ws.append(ul)
                        ul.bind("<Button-1>", lambda e, t=tag: (pending_removes.discard(t), rebuild()))
                    elif is_new:
                        xl = tk.Label(row, text="×", bg=MENU_BG, fg="#cc4444",
                                      font=("Segoe UI", 11, "bold"), cursor="hand2", padx=8)
                        xl.pack(side="right")
                        row_ws.append(xl)
                        def _rm(e=None, t=tag):
                            if t in pending_adds:
                                pending_adds.remove(t)
                            rebuild()
                        xl.bind("<Button-1>", _rm)
                    _bind_hover(row, row_ws)

            # ── separator ─────────────────────────────────────────────
            tk.Frame(content, bg=MENU_SEP, height=1).pack(fill="x", pady=1)

            if edit_mode[0]:
                # text entry for adding a new tag
                entry = tk.Entry(content, font=("Segoe UI", 9),
                                 bg="#252526", fg=MENU_FG_DIM,
                                 insertbackground=MENU_FG, relief="flat", bd=0,
                                 highlightthickness=1,
                                 highlightbackground=MENU_SEP,
                                 highlightcolor=ACCENT)
                entry.insert(0, "Add Tag")
                entry.pack(fill="x", padx=6, pady=3, ipady=2)
                entry_ref[0] = entry

                def _fin(e):
                    if entry.get() == "Add Tag":
                        entry.delete(0, "end")
                        entry.configure(fg=MENU_FG)
                def _fout(e):
                    if not entry.get():
                        entry.insert(0, "Add Tag")
                        entry.configure(fg=MENU_FG_DIM)
                def _add(e=None):
                    name = entry.get().strip().upper()
                    if not name or name == "ADD TAG":
                        return
                    if name in TAG_OPTIONS or name in pending_adds:
                        return
                    if not all(c.isalnum() or c == "_" for c in name):
                        return
                    pending_adds.append(name)
                    rebuild()
                    if entry_ref[0]:
                        entry_ref[0].focus_set()
                entry.bind("<FocusIn>", _fin)
                entry.bind("<FocusOut>", _fout)
                entry.bind("<Return>", _add)

                tk.Frame(content, bg=MENU_SEP, height=1).pack(fill="x", pady=1)

                save_row = tk.Frame(content, bg=MENU_BG)
                save_row.pack(fill="x")
                save_lbl = tk.Label(save_row, text="Save", bg=MENU_BG, fg=MENU_FG,
                                    font=("Segoe UI", 9), anchor="w", padx=8, pady=3)
                save_lbl.pack(side="left", fill="x", expand=True)
                _bind_hover(save_row, [save_lbl])
                for w in [save_row, save_lbl]:
                    w.bind("<Button-1>", lambda e: (_apply(), win.destroy()))
            else:
                edit_row = tk.Frame(content, bg=MENU_BG)
                edit_row.pack(fill="x")
                edit_lbl = tk.Label(edit_row, text="Edit tags…", bg=MENU_BG, fg=MENU_FG,
                                    font=("Segoe UI", 9), anchor="w", padx=8, pady=3)
                edit_lbl.pack(side="left", fill="x", expand=True)
                _bind_hover(edit_row, [edit_lbl])
                def _open_edit(e=None):
                    edit_mode[0] = True
                    rebuild()
                    if entry_ref[0]:
                        entry_ref[0].focus_set()
                for w in [edit_row, edit_lbl]:
                    w.bind("<Button-1>", _open_edit)

            # ── reposition after content changes ───────────────────────
            win.update_idletasks()
            rw = win.winfo_reqwidth()
            rh = win.winfo_reqheight()
            sw = win.winfo_screenwidth()
            sh = win.winfo_screenheight()
            win.geometry(f"{rw}x{rh}+{min(bx, sw-rw-4)}+{min(by, sh-rh-4)}")

        def _apply():
            if pending_removes:
                rows = list(self.conn.execute(
                    "SELECT id, tags FROM images WHERE tags IS NOT NULL AND tags != ''"
                ))
                updates = []
                for img_id, raw_tags in rows:
                    tags = set(self._parse_tags(raw_tags))
                    new_tags = tags - pending_removes
                    if new_tags != tags:
                        ordered = [t for t in TAG_OPTIONS if t in new_tags and t not in pending_removes]
                        updates.append((json.dumps(ordered, ensure_ascii=False), img_id))
                if updates:
                    self.conn.executemany("UPDATE images SET tags=? WHERE id=?", updates)
                    self.conn.commit()
                for tag in list(pending_removes):
                    if tag in TAG_OPTIONS:
                        TAG_OPTIONS.remove(tag)
                for s in ("a", "b"):
                    old_row = self._side[s].get("row")
                    if old_row:
                        fresh = self._fetch_row(old_row[0])
                        if fresh:
                            self._side[s]["row"] = fresh
            for tag in pending_adds:
                if tag not in TAG_OPTIONS:
                    TAG_OPTIONS.append(tag)
            self._rebuild_all_tag_menus()

        def _has_changes():
            typed = ""
            try:
                if entry_ref[0]:
                    typed = entry_ref[0].get().strip()
            except tk.TclError:
                pass
            return bool(pending_removes or pending_adds or (typed and typed not in ("", "Add Tag")))

        def _maybe_dismiss(e):
            try:
                wx, wy = win.winfo_rootx(), win.winfo_rooty()
                ww, wh = win.winfo_width(), win.winfo_height()
                if not (wx <= e.x_root <= wx + ww and wy <= e.y_root <= wy + wh):
                    if edit_mode[0] and _has_changes():
                        result = messagebox.askyesnocancel(
                            "Save Changes", "Save tag changes?", parent=win)
                        if result is True:
                            _apply()
                            win.destroy()
                        elif result is False:
                            win.destroy()
                    else:
                        win.destroy()
            except tk.TclError:
                pass

        rebuild()
        win.lift()
        bind_id = self.root.bind("<Button-1>", _maybe_dismiss, add="+")
        def _cleanup_bind(e=None):
            try:
                self.root.unbind("<Button-1>", bind_id)
            except tk.TclError:
                pass
        win.bind("<Destroy>", _cleanup_bind)

    def _build_action_buttons(self, side: str, parent: tk.Frame) -> None:
        actions = tk.Frame(parent, bg=INFO_BAR_BG)
        actions.grid(row=0, column=1, sticky="e", padx=(0, 8), pady=2)

        buttons: dict = {}
        # Favorite (heart) — replaces the old "Upvote" button. Toggles the FAVORITE marker tag.
        heart = tk.Button(
            actions,
            text="♡",
            command=lambda s=side: self.toggle_favorite(s),
            bg=INFO_BAR_BG,
            fg=INFO_BAR_FG,
            activebackground=DARK_PANEL,
            activeforeground=FAVORITE_COLOR,
            relief="flat",
            padx=6,
            pady=0,
            font=("Segoe UI", 11),
            cursor="hand2",
        )
        heart.pack(side="left", padx=(0, 2))
        buttons["favorite"] = heart

        for text, cmd in (("Skip", lambda s=side: self.skip_side(s)),
                          ("Hide", lambda s=side: self.hide_side(s))):
            btn = tk.Button(
                actions,
                text=text,
                command=cmd,
                bg=INFO_BAR_BG,
                fg=INFO_BAR_FG,
                activebackground=DARK_PANEL,
                activeforeground=INFO_BAR_FG,
                relief="flat",
                padx=6,
                pady=0,
                font=("Segoe UI", 8),
                cursor="hand2",
            )
            btn.pack(side="left", padx=(0, 2))
            buttons[text.lower()] = btn
        self._side[side]["action_buttons"] = buttons
        self._update_favorite_button(side)


    def _ordered_tags(self, tags: set) -> List[str]:
        return [tag for tag in TAG_OPTIONS if tag in tags]

    def _parse_tags(self, raw: str) -> List[str]:
        if not raw:
            return []
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                return [str(t).upper() for t in data if str(t).upper() in TAG_OPTIONS]
        except Exception:
            pass
        parts = [p.strip().upper() for p in raw.replace(";", ",").split(",") if p.strip()]
        return [p for p in parts if p in TAG_OPTIONS]

    def _tags_for_row(self, row: tuple) -> List[str]:
        raw = row[8] if row and len(row) > 8 else ""
        tags = set(self._parse_tags(raw))
        hidden = int(row[7] or 0) if row and len(row) > 7 else 0
        changed = False
        if hidden == 1 and "HIDE" not in tags:
            tags.add("HIDE")
            changed = True
        if hidden == 0 and "HIDE" in tags:
            tags.remove("HIDE")
            changed = True
        ordered = self._ordered_tags(tags)
        if changed and row and len(row) > 0:
            self._write_tags(row[0], set(ordered), hidden=hidden)
        return ordered

    def _match_tags(self, row: tuple) -> frozenset:
        """Tag set used for DUEL MATCHMAKING — excludes marker tags (FAVORITE) so favoriting an
        image never moves it out of its duel group. Display/filter code uses _tags_for_row."""
        return frozenset(self._tags_for_row(row)) - NON_MATCH_TAGS

    def _write_tags(self, image_id: int, tags: set, hidden: Optional[int] = None) -> None:
        if image_id < 0:
            return
        ordered = self._ordered_tags(tags)
        payload = json.dumps(ordered, ensure_ascii=False)
        if hidden is None:
            self.conn.execute("UPDATE images SET tags=? WHERE id=?", (payload, image_id))
        else:
            self.conn.execute("UPDATE images SET tags=?, hidden=? WHERE id=?", (payload, int(hidden), image_id))
        self.conn.commit()

    def _sync_tag_controls(self, side: str) -> None:
        row = self._side[side].get("row")
        if not row:
            return
        tags = self._tags_for_row(row)
        tag_vars = self._side[side].get("tag_vars", {})
        for tag, var in tag_vars.items():
            var.set(tag in tags)
        self._side[side]["tags"] = tags
        self._set_tag_button_label(side)
        self._update_favorite_button(side)

    def toggle_favorite(self, side: str) -> None:
        """Heart button: toggle the FAVORITE marker tag on the displayed image. Does NOT reroll the
        duel or change scoring — FAVORITE is excluded from matchmaking (see _match_tags)."""
        if not self.current:
            return
        row = self._side[side].get("row")
        if not row or row[0] < 0:
            return
        tags = set(self._tags_for_row(row))
        if FAVORITE_TAG in tags:
            tags.discard(FAVORITE_TAG)
        else:
            tags.add(FAVORITE_TAG)
        self._write_tags(row[0], tags)
        updated = self._fetch_row(row[0])
        if updated:
            self._side[side]["row"] = updated
            if self.current:
                a, b = self.current
                if side == "a" and a and a[0] == row[0]:
                    self.current = (updated, b)
                elif side == "b" and b and b[0] == row[0]:
                    self.current = (a, updated)
                if self.history_index is None:
                    self.live_current = self.current
        self._sync_tag_controls(side)

    def _update_favorite_button(self, side: str) -> None:
        btns = self._side[side].get("action_buttons") or {}
        heart = btns.get("favorite")
        if not heart:
            return
        row = self._side[side].get("row")
        fav = bool(row and row[0] >= 0 and FAVORITE_TAG in set(self._tags_for_row(row)))
        try:
            heart.config(text=("♥" if fav else "♡"), fg=(FAVORITE_COLOR if fav else INFO_BAR_FG))
        except Exception:
            pass

    def _set_tag_button_label(self, side: str) -> None:
        button = self._side[side].get("tag_button")
        if not button:
            return
        tags = self._side[side].get("tags", [])
        label = "Tags: " + (", ".join(tags) if tags else "(none)")
        button.configure(text=label)

    def _on_tag_change(self, side: str) -> None:
        row = self._side[side].get("row")
        if not row or row[0] < 0:
            return
        tag_vars = self._side[side].get("tag_vars", {})
        tags = {tag for tag, var in tag_vars.items() if var.get()}
        prev_tags = set(self._side[side].get("tags", []))
        if tags == prev_tags:
            return
        # Marker-only change (e.g. FAVORITE) doesn't alter the matchmaking group — just persist and
        # refresh the controls; never reroll/sub-duel.
        changed = tags ^ prev_tags
        if changed and changed <= NON_MATCH_TAGS:
            self._write_tags(row[0], tags)
            self._side[side]["tags"] = self._ordered_tags(tags)
            self._set_tag_button_label(side)
            updated = self._fetch_row(row[0])
            if updated:
                self._side[side]["row"] = updated
            self._update_favorite_button(side)
            return
        wants_hide = "HIDE" in tags
        had_hide = "HIDE" in prev_tags
        if wants_hide != had_hide:
            if self.pool_filter_var.get() == "Hidden":
                if wants_hide:
                    self._write_tags(row[0], tags, hidden=1)
                else:
                    self.hide_side(side)
                    return
            else:
                if wants_hide:
                    self.hide_side(side)
                    return
                self._write_tags(row[0], tags, hidden=0)
        else:
            self._write_tags(row[0], tags)
        self._side[side]["tags"] = self._ordered_tags(tags)
        self._set_tag_button_label(side)

        updated = self._fetch_row(row[0])
        if updated:
            self._side[side]["row"] = updated

        # In edit/history mode: nullify the current vote, replace the tagged slot
        # in the parent duel with a fresh pick, and spin up a sub-duel for the
        # tagged file so the user can immediately vote on a new pairing.
        if self.history_index is not None:
            if updated:
                self._create_history_sub_duel(self.history_index, updated, side)
            return

        # In live duel mode: replace the tagged slot with a fresh pick, then queue a
        # new duel for the tagged image (with its new tags) as the next upcoming duel.
        if self.history_index is None and self.current:
            current_row = self.current[0] if side == "a" else self.current[1]
            if current_row and current_row[0] == row[0]:
                if updated:
                    self._create_live_sub_duel(updated, side)
                else:
                    self._replace_side_keep_other(side)
                return

        # Revalidate both sides against active pool/tag filters immediately.
        self.on_pool_filter_change()

    def _on_configure(self, event=None):
        # avoid recreating players on resize; only re-render still images/gifs
        if self._resize_job:
            try:
                self.root.after_cancel(self._resize_job)
            except Exception:
                pass
        self._resize_job = self.root.after(120, self._refresh_visuals_only)

    def _media_kind(self, path: str) -> str:
        ext = Path(path).suffix.lower()
        if ext in VIDEO_EXTS:
            return "video"
        if ext in GIF_EXTS:
            return "gif"
        return "image"

    def _video_has_audio(self, path: str) -> bool:
        try:
            mtime = int(os.path.getmtime(path))
        except Exception:
            mtime = 0
        cache_key = f"{path}|{mtime}"
        cached = self._audio_cache.get(cache_key)
        if cached is not None:
            return bool(cached)

        has_audio = False
        ffmpeg = self._ffmpeg_exe()
        if ffmpeg and os.path.exists(path):
            ffprobe = shutil.which("ffprobe")
            if ffprobe:
                cmd = [
                    ffprobe, "-v", "error",
                    "-select_streams", "a",
                    "-show_entries", "stream=index",
                    "-of", "csv=p=0",
                    path,
                ]
                try:
                    r = subprocess.run(
                        cmd,
                        check=False,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                    )
                    has_audio = bool((r.stdout or "").strip())
                except Exception:
                    has_audio = False
            else:
                # ffprobe not available — fall back to parsing ffmpeg's info banner.
                # Imprecise: "audio:" appears in unrelated output lines; ffprobe is preferred.
                cmd = [ffmpeg, "-hide_banner", "-i", path]
                try:
                    r = subprocess.run(
                        cmd,
                        check=False,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        encoding="utf-8",
                        errors="replace",
                    )
                    has_audio = "audio:" in (r.stderr or "").lower()
                except Exception:
                    has_audio = False

        self._audio_cache[cache_key] = bool(has_audio)
        existing_tag = self._sidecar_audio_tag(path)
        if existing_tag is None or existing_tag != bool(has_audio):
            self._write_sidecar_audio_tag(path, bool(has_audio))
        return bool(has_audio)

    def _sidecar_audio_tag(self, path: str) -> Optional[bool]:
        sidecar_path = SIDECAR_DIR / (Path(path).name + ".json")
        if not sidecar_path.exists():
            return None
        try:
            data = json.loads(sidecar_path.read_text(encoding="utf-8"))
        except Exception:
            return None
        raw_tag = data.get("audio", "")
        if isinstance(raw_tag, bool):
            return raw_tag
        tag = str(raw_tag).strip().upper()
        if tag in {"Y", "YES", "TRUE", "1"}:
            return True
        if tag in {"N", "NO", "FALSE", "0"}:
            return False
        return None

    def _write_sidecar_audio_tag(self, path: str, has_audio: bool) -> None:
        sidecar_path = SIDECAR_DIR / (Path(path).name + ".json")
        data: dict = {}
        if sidecar_path.exists():
            try:
                data = json.loads(sidecar_path.read_text(encoding="utf-8"))
            except Exception:
                data = {}
        data["audio"] = bool(has_audio)
        try:
            sidecar_path.write_text(
                json.dumps(data, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            print(f"[audio] {Path(path).name} -> {data['audio']} ({sidecar_path})")
        except Exception:
            pass

    def _selected_tag_filters(self) -> List[str]:
        selected = []
        for tag in TAG_OPTIONS:
            var = self.tag_filter_vars.get(tag)
            if var and var.get():
                selected.append(tag)
        return selected

    def _update_tag_filter_button_label(self) -> None:
        selected = self._selected_tag_filters()
        label = "Tags: " + (", ".join(selected) if selected else "(none)")
        self.tag_filter_btn.configure(text=label)

    def on_tag_filter_change(self):
        self._update_tag_filter_button_label()
        self.on_pool_filter_change()

    def _tag_filter_matches(self, row: tuple) -> bool:
        selected = set(self._selected_tag_filters())
        if not selected:
            return True
        tags = set(self._parse_tags(row[8] if row and len(row) > 8 else ""))
        return not any(tag in tags for tag in selected)

    def _row_matches_filter(self, row: tuple) -> bool:
        # row: (id, path, folder, duels, wins, losses, score, hidden, tags)
        hidden = int(row[7] or 0)
        f = self.pool_filter_var.get()
        kind = self._media_kind(row[1])

        if f == "Hidden":
            return hidden == 1
        if hidden == 1:
            return False
        if not self._tag_filter_matches(row):
            return False

        if f == "All":
            return True
        if f == "Images":
            return kind == "image"
        if f == "GIFs":
            return kind == "gif"
        if f == "Videos":
            return kind == "video"
        if f == "Videos (audio)":
            if kind != "video":
                return False
            tag = self._sidecar_audio_tag(row[1])
            if tag is not None:
                return tag
            return self._video_has_audio(row[1])
        if f == "Animated":
            return kind in ("gif", "video")
        return True

    def _pool_rows_videos_with_audio(self, rows: List[tuple]) -> List[tuple]:
        tagged: List[tuple] = []
        for row in rows:
            hidden = int(row[7] or 0)
            if hidden == 1 or self._media_kind(row[1]) != "video":
                continue
            tag = self._sidecar_audio_tag(row[1])
            if tag is True:
                tagged.append(row)
            elif tag is None and self._video_has_audio(row[1]):
                tagged.append(row)
            if len(tagged) >= 2:
                break
        return tagged

    def _pool_rows(self) -> List[tuple]:
        rows = list(self.conn.execute("""
            SELECT id, path, folder, duels, wins, losses, score, hidden, tags
            FROM images
        """))
        if self._missing_ids:
            rows = [r for r in rows if r[0] not in self._missing_ids]
        random.shuffle(rows)
        if self.pool_filter_var.get() == "Videos (audio)":
            return self._pool_rows_videos_with_audio(rows)
        rows = [r for r in rows if self._row_matches_filter(r)]
        return rows

    def _start_missing_scan(self) -> None:
        """Spawn a daemon thread that audits the DB for files missing from disk and applies
        the result on the main thread. Uses its own sqlite connection (see audit_file_availability)."""
        def worker():
            try:
                missing = audit_file_availability(DB_PATH)
            except Exception as ex:
                print(f"[audit] missing-file scan failed: {ex}")
                return
            self.root.after(0, lambda: self._apply_missing_scan(missing))
        threading.Thread(target=worker, daemon=True).start()

    def _apply_missing_scan(self, missing_ids: set) -> None:
        """Main-thread: record missing ids and purge them from the live duel / future queue
        so a row whose file is already gone never lingers on screen or in the pre-roll."""
        self._missing_ids = set(missing_ids)
        if not missing_ids:
            return
        # Drop any pre-rolled future duels that reference a now-known-missing file.
        self.future_queue = [
            fe for fe in self.future_queue
            if fe["a"][0] not in missing_ids and (fe["b"] is None or fe["b"][0] not in missing_ids)
        ]
        # If the LIVE duel itself references a missing file, roll a fresh one. (Leave
        # history/edit mode alone — past duels are fixed, and the load will show a notice.)
        if self.history_index is None and self.current:
            a, b = self.current
            if (a[0] >= 0 and a[0] in missing_ids) or (b[0] >= 0 and b[0] in missing_ids):
                self._stop_video("a")
                self._stop_video("b")
                self.load_duel()
                return
        self._fill_future_queue()
        self._update_carousel()

    def on_pool_filter_change(self):
        self.pool_filter.configure(text=self.pool_filter_var.get())
        # if current images are not in the new pool, replace them
        if not self.current:
            self.load_duel()
            return
        a, b = self.current
        pool = self._pool_rows()
        ids = {r[0] for r in pool}
        changed = False
        if a[0] not in ids:
            a = None
        if b[0] not in ids:
            b = None

        if a and b and self._media_kind(a[1]) != self._media_kind(b[1]):
            a = None
            b = None

        if a is None and b is not None:
            na = self.pick_one(
                exclude_id=b[0],
                pool=pool,
                required_kind=self._media_kind(b[1]),
                required_tags=self._match_tags(b),
            )
            if na:
                a = na
                changed = True
        if b is None and a is not None:
            nb = self.pick_one(
                exclude_id=a[0],
                pool=pool,
                required_kind=self._media_kind(a[1]),
                required_tags=self._match_tags(a),
            )
            if nb:
                b = nb
                changed = True

        if not a or not b:
            self.future_queue = []
            self.load_duel()
            return

        if changed:
            if self.solo_mode and b and b[0] >= 0:
                self.solo_mode = False
            self._set_current(a, b)
            self.live_current = self.current
            self._render_side("a")
            self._render_side("b")
        self.future_queue = []
        self._fill_future_queue()
        self.update_sidebar()
        self._update_carousel()

    # -------------------- future queue --------------------
    def _fill_future_queue(self, target: Optional[int] = None) -> None:
        """Pre-roll upcoming duels so the carousel has slots to the right of the live duel."""
        if target is None:
            target = self.carousel_size
        # IDs already committed to (live current + existing future entries)
        used_ids: set = set()
        if self.live_current:
            used_ids.update(r[0] for r in self.live_current if r[0] >= 0)
        for fe in self.future_queue:
            used_ids.add(fe["a"][0])
            if fe["b"] is not None:
                used_ids.add(fe["b"][0])
        attempts = 0
        while len(self.future_queue) < target and attempts < target * 6:
            attempts += 1
            a, b = self.pick_two()
            if not a or not b:
                break
            if a[0] in used_ids or b[0] in used_ids:
                continue
            used_ids.add(a[0])
            used_ids.add(b[0])
            self.future_queue.append({"a": a, "b": b, "thumb": None})

    def _jump_to_future(self, fi: int) -> None:
        """Jump ahead to future_queue[fi], discarding the live duel and any futures before it."""
        if fi < 0 or fi >= len(self.future_queue):
            return
        fentry = self.future_queue[fi]
        # Discard everything up to and including fi; the skipped pairs get no Elo change
        self.future_queue = self.future_queue[fi + 1:]
        a, b = fentry["a"], fentry["b"]
        if b is None:
            self.solo_mode = True
            b = _NO_OPPONENT
        else:
            self.solo_mode = False
        self._set_current(a, b)
        self.live_current = self.current
        self._stop_video("a")
        self._stop_video("b")
        self._update_info_bars(a, b)
        self._render_side("a")
        self._render_side("b")
        self.update_sidebar()
        self._fill_future_queue()
        self._update_carousel()

    # -------------------- picking --------------------
    def pick_one(
        self,
        exclude_id: Optional[int],
        pool: List[tuple],
        required_kind: Optional[str] = None,
        required_tags: Optional[frozenset] = None,
    ) -> Optional[tuple]:
        """Return a random row from *pool* matching all supplied constraints.

        *required_tags* is an **exact** frozenset match — if supplied and no
        candidate shares that exact tag set, ``None`` is returned rather than
        falling back to a differently-tagged image.  Pass ``None`` to skip tag
        filtering entirely.
        """
        if not pool:
            return None
        candidates = pool
        if required_kind is not None:
            candidates = [r for r in candidates if self._media_kind(r[1]) == required_kind]
        if exclude_id is not None:
            candidates = [r for r in candidates if r[0] != exclude_id]
        if not candidates:
            return None
        if required_tags is not None:
            tag_matched = [r for r in candidates if self._match_tags(r) == required_tags]
            if not tag_matched:
                return None  # refuse to pair across different tag groups
            candidates = tag_matched
        return random.choice(candidates)

    def pick_two(self) -> Tuple[Optional[tuple], Optional[tuple]]:
        pool = self._pool_rows()
        if len(pool) < 2:
            return None, None

        # Group by (exact tag set, media kind).  Tagged images must only duel
        # images that share the exact same tag set; untagged images (empty
        # frozenset) form their own group.
        groups: dict = {}
        for row in pool:
            key = (self._match_tags(row), self._media_kind(row[1]))
            groups.setdefault(key, []).append(row)

        eligible_groups = [rows for rows in groups.values() if len(rows) >= 2]
        if not eligible_groups:
            return None, None

        # Weight by group size so each individual image has equal probability
        # of appearing, regardless of how rare or common its tag set is.
        weights = [len(g) for g in eligible_groups]
        group = random.choices(eligible_groups, weights=weights, k=1)[0]
        a, b = random.sample(group, 2)
        return a, b

    # -------------------- duel flow --------------------
    def _set_current(self, a: tuple, b: tuple):
        self.current = (a, b)
        self._side["a"]["row"] = a
        self._side["b"]["row"] = b
        self._side["a"]["media_kind"] = self._media_kind(a[1])
        self._side["b"]["media_kind"] = self._media_kind(b[1])

    def load_duel(self):
        # Consume the first pre-rolled future duel if available, otherwise roll fresh
        if self.future_queue:
            fentry = self.future_queue.pop(0)
            a, b = fentry["a"], fentry["b"]
        else:
            a, b = self.pick_two()
        if not a:
            messagebox.showerror("No images", "Not enough items in the selected pool (need at least 2).")
            self.quit()
            return
        if b is None:
            # Solo duel: no opponent exists in this tag group
            self.solo_mode = True
            b = _NO_OPPONENT
        elif not b:
            messagebox.showerror("No images", "Not enough items in the selected pool (need at least 2).")
            self.quit()
            return
        else:
            self.solo_mode = False

        self._set_current(a, b)
        self.live_current = self.current
        self._update_info_bars(a, b)
        self.prev_artists.appendleft(a[2])
        if b[0] >= 0:
            self.prev_artists.appendleft(b[2])

        print("[duel] showing:")
        print(f"  LEFT:  {a[1]} (score={a[6]:.2f}, duels={a[3]}, W={a[4]}, L={a[5]})")
        if b[0] >= 0:
            print(f"  RIGHT: {b[1]} (score={b[6]:.2f}, duels={b[3]}, W={b[4]}, L={b[5]})")
        else:
            print("  RIGHT: (no opponent — solo duel)")

        self._render_side("a")
        self._render_side("b")
        self.update_sidebar()
        self._fill_future_queue()
        self._update_carousel()

    def choose(self, winner: Optional[str]):
        if not self._window_was_focused:
            return
        if not self.current:
            return
        if self.solo_mode:
            # No opponent — any click just advances to the next duel with no scoring
            self.solo_mode = False
            self._stop_video("a")
            self._stop_video("b")
            self.load_duel()
            return
        # Skip (no winner): ties/downvotes are retired, so a skip never affects score — just advance.
        if winner not in ("a", "b"):
            if self.history_index is not None:
                next_index = self.history_index + 1
                if next_index < len(self.duel_history):
                    self._enter_history_mode(next_index)
                else:
                    self._exit_history_mode()
            else:
                self._stop_video("a")
                self._stop_video("b")
                self.load_duel()
            return
        # snapshot ranks for delta arrows
        prev_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}

        if self.history_index is not None:
            entry = self.duel_history[self.history_index]
            if entry.get("comparison_id") is None:
                # Brand-new sub-duel: create a real comparison record.
                a = self._fetch_row(entry["a_id"])
                b = self._fetch_row(entry["b_id"])
                if a and b:
                    result = record_result(self.conn, a, b, winner, session_id=self.session_id)
                    entry["comparison_id"] = result["comparison_id"]
                    entry["winner"]        = winner
                    entry["before_a"]      = result["before_a"]
                    entry["before_b"]      = result["before_b"]
                    entry["thumb"]         = None
            else:
                self._apply_revote(self.history_index, winner)
            self._last_ranks = prev_ranks
            next_index = self.history_index + 1
            if next_index < len(self.duel_history):
                self._enter_history_mode(next_index)
            else:
                self._exit_history_mode()
            return

        a, b = self.current
        entry = record_result(self.conn, a, b, winner, session_id=self.session_id)
        self._attach_history_thumbs(entry)
        self.duel_history.append(entry)
        self._last_ranks = prev_ranks

        # stop video playback when advancing
        self._stop_video("a")
        self._stop_video("b")
        self.load_duel()

    def _create_live_sub_duel(self, tagged_row: tuple, side: str) -> None:
        """
        Called when a tag is changed on the live duel image.

        1. Replace the tagged slot in the current live duel with a fresh pick
           matched to the other side's tag group.
        2. Roll an opponent for the tagged image matched to its new tag group.
        3. Insert that new duel at the front of future_queue (plays next).
        """
        if not self.current or self.solo_mode:
            return
        a, b = self.current
        other = b if side == "a" else a

        pool = self._pool_rows()
        tagged_kind = self._media_kind(tagged_row[1])

        replacement = self.pick_one(
            exclude_id=other[0],
            pool=pool,
            required_kind=self._media_kind(other[1]),
            required_tags=self._match_tags(other),
        )

        sub_opponent = self.pick_one(
            exclude_id=tagged_row[0],
            pool=pool,
            required_kind=tagged_kind,
            required_tags=self._match_tags(tagged_row),
        )

        if sub_opponent:
            if side == "a":
                sub_entry = {"a": tagged_row, "b": sub_opponent, "thumb": None}
            else:
                sub_entry = {"a": sub_opponent, "b": tagged_row, "thumb": None}
        else:
            # no opponent in the new tag group — queue a solo placeholder so the
            # user can see and skip the image rather than it silently disappearing
            sub_entry = {"a": tagged_row, "b": None, "thumb": None}
        self.future_queue.insert(0, sub_entry)

        if replacement:
            self._side[side]["last_replaced_row"] = a if side == "a" else b
            if side == "a":
                self._set_current(replacement, other)
            else:
                self._set_current(other, replacement)
            self._stop_video(side)
            self._render_side(side)
            self.update_sidebar()
        else:
            self.load_duel()
            return

        self._update_carousel()

    def _replace_side_keep_other(self, side: str) -> None:
        if not self.current or self.solo_mode:
            return
        a, b = self.current
        outgoing = a if side == "a" else b
        other = b if side == "a" else a
        self._side[side]["last_replaced_row"] = outgoing

        pool = self._pool_rows()
        replacement = self.pick_one(
            exclude_id=other[0],
            pool=pool,
            required_kind=self._media_kind(other[1]),
            required_tags=self._match_tags(other),
        )
        if not replacement:
            self.load_duel()
            return

        if side == "a":
            self._set_current(replacement, other)
        else:
            self._set_current(other, replacement)

        self._stop_video(side)
        self._render_side(side)
        self.update_sidebar()

    def _handle_missing_side(self, side: str, source_path: str) -> None:
        """A media file failed to open because it's gone from disk. Mark its DB id so the
        picker skips it from now on; in live mode auto-swap the slot for a fresh pick so the
        user isn't stranded on a 'Failed to load' panel. In history/edit mode (or solo) the
        view is fixed, so just leave a short notice."""
        st = self._side[side]
        row = st.get("row")
        if row and row[0] >= 0:
            self._missing_ids.add(row[0])
        if self.history_index is None and not self.solo_mode and self.current:
            print(f"[load] auto-skipping missing file ({side}): {source_path}")
            self._replace_side_keep_other(side)
        else:
            widget = self.left_panel if side == "a" else self.right_panel
            widget.configure(
                text=f"File not found:\n{source_path}\n\n(removed from rotation)",
                image="", fg=TEXT_COLOR, bg=DARK_PANEL,
            )

    def downvote_side(self, side: str) -> None:
        # Downvote retired as a feature — behaves as a no-score skip if any legacy path reaches it.
        if not self.current:
            return
        self._replace_side_keep_other(side)

    def skip_side(self, side: str) -> None:
        if not self.current:
            return
        self._replace_side_keep_other(side)

    def undo_side_tag_hide(self, side: str) -> None:
        if not self.current or self.solo_mode:
            return
        candidate = self._side[side].get("last_replaced_row") or self._side[side].get("row")
        if not candidate:
            return
        restored = self._fetch_row(candidate[0])
        if not restored:
            return

        tags = set(self._tags_for_row(restored))
        tags.discard("HIDE")
        self._write_tags(restored[0], tags, hidden=0)
        restored = self._fetch_row(restored[0])
        if not restored:
            return

        a, b = self.current
        other = b if side == "a" else a
        if self._media_kind(restored[1]) != self._media_kind(other[1]):
            return

        if side == "a":
            self._set_current(restored, other)
        else:
            self._set_current(other, restored)
        self._side[side]["last_replaced_row"] = None
        self._stop_video(side)
        self._render_side(side)
        self.update_sidebar()

    def hide_side(self, side: str):
        if not self.current or self.solo_mode:
            return
        a, b = self.current
        target = a if side == "a" else b

        # In "Hidden" pool, middle-click acts as UNHIDE (to make recovery easy).
        if self.pool_filter_var.get() == "Hidden":
            unhide_image(self.conn, target)
            tags = set(self._tags_for_row(target))
            tags.discard("HIDE")
            self._write_tags(target[0], tags, hidden=0)
        else:
            hide_image(self.conn, target)
            tags = set(self._tags_for_row(target))
            tags.add("HIDE")
            self._write_tags(target[0], tags, hidden=1)

        self._replace_side_keep_other(side)

    # -------------------- rendering --------------------
    def _apply_pixelate(self, im: Image.Image, pixel_size: int = 50) -> Image.Image:
        if pixel_size <= 1:
            return im
        w, h = im.size
        small_w = max(1, w // pixel_size)
        small_h = max(1, h // pixel_size)
        im_small = im.resize((small_w, small_h), Image.Resampling.BOX)
        return im_small.resize((w, h), Image.Resampling.NEAREST)

    def _get_side_display_size(self, side: str, kind: str) -> tuple[int, int]:
        widget = (self.left_video if side == "a" else self.right_video) if kind == "video" else (self.left_panel if side == "a" else self.right_panel)
        return (max(1, widget.winfo_width()), max(1, widget.winfo_height()))

    def _render_side(self, side: str):
        st = self._side[side]
        row = st["row"]
        if not row:
            return
        kind = self._media_kind(row[1])
        st["media_kind"] = kind

        if side == "a":
            panel = self.left_panel
            container = self.left_container
            vframe = self.left_video
        else:
            panel = self.right_panel
            container = self.right_container
            vframe = self.right_video

        # Solo-duel placeholder: no opponent in this tag group
        if row[0] < 0:
            self._cancel_animation(side)
            self._stop_video(side)
            vframe.place_forget()
            panel.place(relx=0, rely=0, relwidth=1, relheight=1)
            panel.configure(image="", text="No match found\nin this tag group\n\nClick to skip",
                            compound="center", font=("Segoe UI", 14), fg="#666666", bg=DARK_BG)
            self._sync_tag_controls(side)
            return

        # cancel gif animation
        self._cancel_animation(side)

        if kind == "video":
            # show video frame, hide image label
            panel.place_forget()
            vframe.place(relx=0, rely=0, relwidth=1, relheight=1)
            self._render_video(side, vframe, row[1])
            player = st.get("vlc_player")
            if player:
                if st.get("vlc_ready"):
                    try:
                        player.play()
                    except Exception:
                        pass
                else:
                    st["vlc_play_pending"] = True
        else:
            # show image label, hide video frame
            self._stop_video(side)
            vframe.place_forget()
            panel.place(relx=0, rely=0, relwidth=1, relheight=1)
            self._render_image_or_gif(side, panel, row[1])

        self._sync_tag_controls(side)
        self._lift_side_overlays(side)
        self._update_video_controls_state()

    def _lift_side_overlays(self, side: str) -> None:
        if side == "a":
            bars = (self.left_info_bar,)
        else:
            bars = (self.right_info_bar,)
        for bar in bars:
            try:
                bar.lift()
            except Exception:
                pass

    def _dismiss_load_timeout(self, side: str) -> None:
        st = self._side[side]
        job = st.pop("load_timeout_job", None)
        if job:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        overlay = st.pop("load_timeout_overlay", None)
        if overlay:
            try:
                overlay.destroy()
            except Exception:
                pass

    def _show_load_timeout(self, side: str, path: str) -> None:
        st = self._side[side]
        container = self.left_container if side == "a" else self.right_container
        overlay = tk.Frame(container, bg=DARK_PANEL, bd=0, highlightthickness=0)
        overlay.place(relx=0.5, rely=0.5, anchor="center")
        st["load_timeout_overlay"] = overlay

        tk.Label(
            overlay, text="Still loading…\nThe file may be slow or unavailable.",
            bg=DARK_PANEL, fg=TEXT_COLOR, font=("Segoe UI", 10), justify="center",
        ).pack(pady=(0, 10))

        btn_row = tk.Frame(overlay, bg=DARK_PANEL)
        btn_row.pack()

        def _retry():
            self._dismiss_load_timeout(side)
            self._render_side(side)

        tk.Button(
            btn_row, text="Retry", command=_retry,
            bg=ACCENT, fg="white", relief="flat", padx=12, pady=4, cursor="hand2",
        ).pack(side="left", padx=(0, 8))
        tk.Button(
            btn_row, text="Open File", command=lambda: os.startfile(path),
            bg="#444444", fg=TEXT_COLOR, relief="flat", padx=12, pady=4, cursor="hand2",
        ).pack(side="left")

    def _render_image_or_gif(self, side: str, widget: tk.Label, path: str):
        self.root.update_idletasks()
        w = max(1, widget.winfo_width())
        h = max(1, widget.winfo_height())
        if w <= 5 or h <= 5:
            self.root.after(50, lambda: self._render_image_or_gif(side, widget, path))
            return
        target = (max(120, w - 12), max(120, h - 12))

        st = self._side[side]
        st["gif_render_token"] = st.get("gif_render_token", 0) + 1
        render_token = st["gif_render_token"]

        # Record the size we're committing to render NOW, before the (possibly slow, two-stage)
        # async decode. _refresh_visuals_only re-renders a side only when last_visual_size !=
        # current panel size. GIF decode sets last_visual_size only on completion, so a stream of
        # <Configure> ticks (carousel thumbnails arriving, layout settling) arriving mid-decode
        # would each see a stale size, re-render, and cancel the in-flight decode — an endless
        # "Loading…"/"Loading GIF…" flicker. Setting it up-front makes those redundant same-size
        # refreshes skip, so the decode can finish. Static images already settle fast; GIFs didn't.
        st["last_visual_size"] = (w, h)

        self._dismiss_load_timeout(side)
        widget.configure(text="Loading…", image="", fg=TEXT_COLOR, bg=DARK_PANEL)

        def on_timeout():
            st2 = self._side[side]
            if st2.get("gif_render_token") != render_token:
                return
            print(f"[load] TIMEOUT after {LOAD_TIMEOUT_MS} ms ({side}): {path!r}")
            print(f"[load]   file: {describe_file_state(path)}")
            self._show_load_timeout(side, path)

        st["load_timeout_job"] = self.root.after(LOAD_TIMEOUT_MS, on_timeout)

        def load_worker(expected_token: int, source_path: str, size_target: tuple, blur_on: bool):
            result: dict = {}
            try:
                im = Image.open(source_path)
                is_animated = (getattr(im, "is_animated", False) and getattr(im, "n_frames", 1) > 1)
                if not is_animated:
                    try:
                        try:
                            im.seek(0)
                        except Exception:
                            pass
                        if im.mode not in ("RGB", "RGBA"):
                            im = im.convert("RGB")
                        im.thumbnail(size_target, Image.Resampling.LANCZOS)
                        if blur_on:
                            im = self._apply_pixelate(im, pixel_size=50)
                        result["payload"] = (im.tobytes(), im.size, im.mode)
                        result["animated"] = False
                    finally:
                        im.close()
                else:
                    im.close()
                    result["animated"] = True
            except Exception as ex:
                state = describe_file_state(source_path)
                print(f"[load] FAILED ({side}): {source_path!r}")
                print(f"[load]   error: {type(ex).__name__}: {ex}")
                print(f"[load]   file:  {state}")
                missing = isinstance(ex, FileNotFoundError) or state.startswith("MISSING")
                if missing:
                    result["missing"] = True
                    result["error"] = (
                        "File not found.\nIt may have been moved, deleted,\n"
                        "or not yet downloaded (OneDrive)."
                    )
                else:
                    # Genuine decode/corruption error — capture full stack for diagnosis.
                    traceback.print_exc()
                    result["error"] = f"{type(ex).__name__}: {ex}"

            def apply():
                st2 = self._side[side]
                if st2.get("gif_render_token") != expected_token:
                    return
                if "error" in result:
                    self._dismiss_load_timeout(side)
                    if result.get("missing"):
                        # File is gone from disk — mark it so the picker skips it and, in
                        # live mode, auto-swap this slot instead of stranding the user.
                        self._handle_missing_side(side, source_path)
                    else:
                        widget.configure(
                            text=f"Failed to load:\n{source_path}\n\n{result['error']}",
                            image="", fg=TEXT_COLOR, bg=DARK_PANEL,
                        )
                    return
                if result.get("animated"):
                    # Keep the load-timeout armed through GIF frame decode (the slow part);
                    # _decode_gif_async dismisses it once frames are ready or on error.
                    widget.configure(text="Loading GIF…", image="", fg=TEXT_COLOR, bg=DARK_PANEL)
                    self._decode_gif_async(side, widget, source_path, size_target, blur_on, expected_token, w, h)
                    return
                self._dismiss_load_timeout(side)
                payload, payload_size, payload_mode = result["payload"]
                img = Image.frombytes(payload_mode, payload_size, payload)
                tk_im = ImageTk.PhotoImage(img)
                widget.configure(image=tk_im, text="", bg=DARK_PANEL)
                widget.image = tk_im
                st2["last_visual_size"] = (w, h)

            self.root.after(0, apply)

        threading.Thread(
            target=load_worker,
            args=(render_token, path, target, self.blur_enabled),
            daemon=True,
        ).start()

    def _decode_gif_async(
        self, side: str, widget: tk.Label, path: str,
        target: tuple, blur_on: bool, render_token: int, w: int, h: int,
    ) -> None:
        def decode_worker(expected_token: int, source_path: str, size_target: tuple, blur_on: bool):
            frames_payload: List[tuple[bytes, tuple[int, int], str]] = []
            delays: List[int] = []
            error: Optional[str] = None
            try:
                with Image.open(source_path) as gif_im:
                    for frame_i, frame in enumerate(ImageSequence.Iterator(gif_im)):
                        if frame_i >= GIF_PRELOAD_MAX_FRAMES:
                            break
                        delay = frame.info.get("duration", gif_im.info.get("duration", 100))
                        delays.append(int(delay))
                        fr = frame.convert("RGBA") if frame.mode != "RGBA" else frame.copy()
                        fr.thumbnail(size_target, Image.Resampling.LANCZOS)
                        if blur_on:
                            fr = self._apply_pixelate(fr, pixel_size=50)
                        frames_payload.append((fr.tobytes(), fr.size, fr.mode))
            except Exception as ex:
                error = str(ex)
                print(f"[gif] DECODE FAILED ({side}) after {len(frames_payload)} frame(s): {source_path!r}")
                print(f"[gif]   error: {type(ex).__name__}: {ex}")
                print(f"[gif]   file:  {describe_file_state(source_path)}")
                traceback.print_exc()

            def apply_result():
                st2 = self._side[side]
                if st2.get("gif_render_token") != expected_token:
                    return
                # Frames are ready (or failed) — clear the load-timeout/overlay armed by
                # _render_image_or_gif, which we deliberately left running across the decode.
                self._dismiss_load_timeout(side)
                if error:
                    widget.configure(text=f"Failed to load:\n{source_path}\n\n{error}", fg=TEXT_COLOR, bg=DARK_PANEL)
                    return
                if not frames_payload:
                    print(f"[gif] NO FRAMES decoded ({side}): {source_path!r}")
                    print(f"[gif]   file: {describe_file_state(source_path)}")
                    widget.configure(text=f"Failed to load:\n{source_path}\n\nNo GIF frames available.", fg=TEXT_COLOR, bg=DARK_PANEL)
                    return

                print(f"[gif] decoded {len(frames_payload)} frame(s) ({side}): {source_path}")
                frames: List[ImageTk.PhotoImage] = []
                for payload, payload_size, payload_mode in frames_payload:
                    img = Image.frombytes(payload_mode, payload_size, payload)
                    frames.append(ImageTk.PhotoImage(img))

                st2["anim_frames"] = frames
                st2["anim_delays"] = delays
                st2["anim_index"] = 0
                st2["last_visual_size"] = (w, h)

                def step():
                    st3 = self._side[side]
                    if st3.get("gif_render_token") != expected_token:
                        return
                    if not st3.get("anim_frames"):
                        return
                    idx = st3["anim_index"] % len(st3["anim_frames"])
                    widget.configure(image=st3["anim_frames"][idx], text="", bg=DARK_PANEL)
                    widget.image = st3["anim_frames"][idx]
                    st3["anim_index"] = (idx + 1) % len(st3["anim_frames"])
                    delay = max(20, int(st3["anim_delays"][idx] if idx < len(st3["anim_delays"]) else 100))
                    st3["anim_job"] = self.root.after(delay, step)

                st2["anim_job"] = self.root.after(0, step)

            self.root.after(0, apply_result)

        threading.Thread(
            target=decode_worker,
            args=(render_token, path, target, blur_on),
            daemon=True,
        ).start()

    def _cancel_animation(self, side: str):
        st = self._side[side]
        st["gif_render_token"] = st.get("gif_render_token", 0) + 1
        self._dismiss_load_timeout(side)
        if st.get("anim_job"):
            try:
                self.root.after_cancel(st["anim_job"])
            except Exception:
                pass
            st["anim_job"] = None
        st["anim_frames"] = None
        st["anim_delays"] = None
        st["anim_index"] = 0

    # -------------------- video (VLC) --------------------
    def _render_video(self, side: str, video_frame: tk.Frame, path: str):
        st = self._side[side]

        # VLC not available -> placeholder
        if not self.vlc_instance:
            self._show_video_placeholder(video_frame, path, reason="Install VLC + python-vlc for in-app playback.")
            self._update_video_blur_overlay(side, video_frame, path)
            return

        # If already playing this path, do nothing (do not reset on refresh)
        if st.get("vlc_player") and st.get("vlc_media") == path:
            self._update_video_blur_overlay(side, video_frame, path)
            st["last_visual_size"] = self._get_side_display_size(side, "video")
            return

        self._stop_video(side)

        # Create a new player
        try:
            player = self.vlc_instance.media_player_new()
        except Exception as e:
            self._show_video_placeholder(video_frame, path, reason=f"VLC player create failed: {e}")
            return

        st["vlc_player"] = player
        st["vlc_media"] = path
        st["vlc_ready"] = False
        st["vlc_play_pending"] = False
        st["vlc_total_ms"] = None
        st["vlc_event_mgr"] = None
        st["last_visual_size"] = self._get_side_display_size(side, "video")

        try:
            self.root.update_idletasks()
            hwnd = video_frame.winfo_id()
            player.set_hwnd(hwnd)  # Windows
            try:
                player.video_set_mouse_input(False)
                player.video_set_key_input(False)
            except Exception:
                pass
        except Exception:
            pass

        try:
            media = self.vlc_instance.media_new_path(path)
            player.set_media(media)
        except Exception as e:
            self._show_video_placeholder(video_frame, path, reason=f"VLC media set failed: {e}")
            self._stop_video(side)
            self._update_video_blur_overlay(side, video_frame, path)
            return

        # Start muted and "paused on first frame"
        try:
            player.audio_set_mute(True)
            player.audio_set_volume(0)
        except Exception:
            pass

        # Kick playback briefly so VLC has a frame to render, then pause+seek to 0.
        try:
            player.play()
        except Exception:
            self._show_video_placeholder(video_frame, path, reason="VLC play() failed.")
            self._stop_video(side)
            return

        # finalize init after a short delay
        def finalize():
            st2 = self._side[side]
            if st2.get("vlc_player") is not player or st2.get("vlc_media") != path:
                return
            try:
                player.pause()
                # Seek to 0; some media need a second seek
                player.set_time(0)
            except Exception:
                pass
            st2["vlc_ready"] = True
            # If user requested play during init, start now.
            if st2.get("vlc_play_pending"):
                try:
                    player.play()
                except Exception:
                    pass
            self._update_video_controls_state()
            self._update_video_blur_overlay(side, video_frame, path)

        st["vlc_init_job"] = self.root.after(180, finalize)
        self._attach_vlc_events(side)
        self._update_video_blur_overlay(side, video_frame, path)

    def _attach_vlc_events(self, side: str):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not HAVE_VLC:
            return
        try:
            mgr = player.event_manager()
            mgr.event_attach(
                vlc.EventType.MediaPlayerEndReached,
                lambda _evt, s=side: self._on_video_end(s),
            )
            st["vlc_event_mgr"] = mgr
        except Exception:
            st["vlc_event_mgr"] = None
        st["last_visual_size"] = self._get_side_display_size(side, "video")

    def _on_video_end(self, side: str):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            return
        if not bool(st.get("vlc_loop", True)):
            return

        def restart():
            st2 = self._side[side]
            player2 = st2.get("vlc_player")
            if not player2 or not st2.get("vlc_ready"):
                return
            try:
                player2.stop()
            except Exception:
                pass
            try:
                player2.play()
                player2.set_time(0)
            except Exception:
                pass
            self._update_video_controls_state()

        try:
            self.root.after(0, restart)
        except Exception:
            restart()

    def _show_video_placeholder(self, video_frame: tk.Frame, path: str, reason: str):
        # Clear any existing children
        for c in list(video_frame.winfo_children()):
            try:
                c.destroy()
            except Exception:
                pass
        msg = f"VIDEO\n{Path(path).name}\n\n{reason}\n\nDouble-click to open externally."
        lbl = tk.Label(video_frame, text=msg, bg="black", fg=TEXT_COLOR, justify="center")
        lbl.place(relx=0, rely=0, relwidth=1, relheight=1)

    def _stop_video(self, side: str):
        st = self._side[side]
        if st.get("vlc_init_job"):
            try:
                self.root.after_cancel(st["vlc_init_job"])
            except Exception:
                pass
            st["vlc_init_job"] = None
        player = st.get("vlc_player")
        if player:
            try:
                player.stop()
            except Exception:
                pass
        st["vlc_player"] = None
        st["vlc_media"] = None
        st["vlc_ready"] = False
        st["vlc_play_pending"] = False
        st["vlc_total_ms"] = None
        st["vlc_event_mgr"] = None
        st["last_visual_size"] = self._get_side_display_size(side, "video")
        st["scrubbing"] = False
        st["video_blur_image"] = None
        self._clear_vlc_blur_logo(side)
        self._set_video_blur_visible(side, False)

    def toggle_video(self, side: str):
        st = self._side[side]
        row = st.get("row")
        if not row:
            return
        if self._media_kind(row[1]) != "video":
            return

        # Ensure player exists
        if not st.get("vlc_player"):
            vframe = self.left_video if side == "a" else self.right_video
            self._render_video(side, vframe, row[1])
            st["vlc_play_pending"] = True
            self._update_video_controls_state()
            return

        player = st["vlc_player"]
        if not st.get("vlc_ready"):
            # toggle play intent during init
            st["vlc_play_pending"] = not bool(st.get("vlc_play_pending"))
            self._update_video_controls_state()
            return

        try:
            if player.is_playing():
                player.pause()
            else:
                player.play()
        except Exception:
            pass
        self._update_video_controls_state()

    def toggle_mute(self, side: str):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            return
        try:
            muted = bool(player.audio_get_mute())
            player.audio_set_mute(not muted)
            if muted:
                player.audio_set_volume(80)
            else:
                player.audio_set_volume(0)
        except Exception:
            pass
        self._update_video_controls_state()

    def toggle_loop(self, side: str):
        st = self._side[side]
        st["vlc_loop"] = not bool(st.get("vlc_loop", True))
        self._update_video_controls_state()

    def _format_mmss(self, ms: int) -> str:
        ms = max(0, int(ms))
        sec = ms // 1000
        m = sec // 60
        s = sec % 60
        return f"{m:02d}:{s:02d}"

    def _tick(self):
        # periodic update for scrub/time
        self._update_scrub_and_time("a")
        self._update_scrub_and_time("b")
        self._tick_job = self.root.after(200, self._tick)

    def _update_scrub_and_time(self, side: str):
        st = self._side[side]
        ui = st.get("ui")
        if not ui:
            return
        player = st.get("vlc_player")
        ready = bool(st.get("vlc_ready"))
        if not player or not ready:
            ui["time"].configure(text="00:00 / 00:00")
            return

        # Set total length once available
        if st.get("vlc_total_ms") is None:
            try:
                length = int(player.get_length() or -1)
            except Exception:
                length = -1
            if length > 0:
                st["vlc_total_ms"] = length
                # Kick off waveform generation once per media
                self._maybe_request_waveform(side)

        try:
            cur = int(player.get_time() or 0)
        except Exception:
            cur = 0
        total = int(st.get("vlc_total_ms") or 0)

        if total <= 0:
            ui["time"].configure(text=f"{self._format_mmss(cur)} / 00:00")
        else:
            ui["time"].configure(text=f"{self._format_mmss(cur)} / {self._format_mmss(total)}")

        # Update playhead if not dragging
        if not st.get("scrubbing"):
            self._update_playhead(side, cur, total)

        self._update_video_controls_state()

    def _build_hover_video_controls(self):
        # Attach a bottom control bar (hidden) to each side container.
        self._attach_hover_controls("a", self.left_container, self.left_panel, self.left_video)
        self._attach_hover_controls("b", self.right_container, self.right_panel, self.right_video)

    def _attach_hover_controls(self, side: str, container: tk.Frame, image_label: tk.Label, video_frame: tk.Frame):
        """
        Bottom video controls that appear on hover.

        Layout (left -> right):
        Play/Pause | -5s | +5s | Mute | Loop | Waveform/Seek Bar | Time | Speed | Fullscreen
        """
        bar = tk.Frame(container, bg=DARK_PANEL, bd=1, relief="solid")
        bar.place_forget()

        btn_opts = dict(bg=DARK_BG, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat", bd=0)

        play_btn = tk.Button(bar, text="Play", width=7, command=lambda: self.toggle_video(side), **btn_opts)
        back_btn = tk.Button(bar, text="-5s", width=5, command=lambda: self.seek_relative(side, -5000), **btn_opts)
        fwd_btn  = tk.Button(bar, text="+5s", width=5, command=lambda: self.seek_relative(side, +5000), **btn_opts)
        mute_btn = tk.Button(bar, text="Mute", width=7, command=lambda: self.toggle_mute(side), **btn_opts)
        loop_btn = tk.Button(bar, text="Loop On", width=8, command=lambda: self.toggle_loop(side), **btn_opts)

        # Waveform / seek bar (Canvas)
        wave = tk.Canvas(bar, height=26, bg=DARK_BG, highlightthickness=0, bd=0, relief="flat")
        time_lbl = tk.Label(bar, text="00:00 / 00:00", bg=DARK_PANEL, fg=TEXT_COLOR, font=("Consolas", 9))

        speed_var = tk.StringVar(value="1.0x")
        speed_box = ttk.Combobox(
            bar,
            values=["0.25x","0.5x","0.75x","1.0x","1.25x","1.5x","2.0x"],
            textvariable=speed_var,
            width=6,
            state="readonly",
        )
        fs_btn = tk.Button(bar, text="Full", width=6, command=lambda: self.toggle_fullscreen(side), **btn_opts)

        # Grid layout
        bar.columnconfigure(5, weight=1)  # waveform expands
        play_btn.grid(row=0, column=0, padx=(8, 6), pady=6, sticky="w")
        back_btn.grid(row=0, column=1, padx=(0, 6), pady=6, sticky="w")
        fwd_btn.grid(row=0, column=2, padx=(0, 10), pady=6, sticky="w")
        mute_btn.grid(row=0, column=3, padx=(0, 10), pady=6, sticky="w")
        loop_btn.grid(row=0, column=4, padx=(0, 10), pady=6, sticky="w")
        wave.grid(row=0, column=5, padx=(0, 10), pady=6, sticky="ew")
        time_lbl.grid(row=0, column=6, padx=(0, 10), pady=6, sticky="e")
        speed_box.grid(row=0, column=7, padx=(0, 10), pady=6, sticky="e")
        fs_btn.grid(row=0, column=8, padx=(0, 8), pady=6, sticky="e")

        # Save UI handles
        st = self._side[side]
        st["ui"] = {
            "bar": bar,
            "play": play_btn,
            "mute": mute_btn,
            "loop": loop_btn,
            "back": back_btn,
            "fwd": fwd_btn,
            "wave": wave,
            "time": time_lbl,
            "speed_var": speed_var,
            "speed": speed_box,
            "fs": fs_btn,
        }
        st.setdefault("scrubbing", False)
        st.setdefault("waveform_ready", False)
        st.setdefault("waveform_img", None)    # PhotoImage (keep ref)
        st.setdefault("waveform_src", None)    # PIL image source (unscaled)
        st.setdefault("waveform_img_size", None)  # (w,h) of current PhotoImage
        st.setdefault("waveform_status", "")      # "", "loading", "no-audio", "error"
        st.setdefault("waveform_key", None)        # cache key
        st.setdefault("waveform_job", None)        # background thread guard
        st.setdefault("waveform_job_key", None)    # key the running job was launched for
        st.setdefault("waveform_resize_job", None) # after() id for debounced resize redraws
        st.setdefault("pending_seek_frac", None)

        # Hover show/hide
        def show(_e=None):
            if self._side[side].get("media_kind") != "video":
                return
            # bottom overlay
            bar.place(relx=0.02, rely=0.90, relwidth=0.96, height=44)
            self._update_video_controls_state()
            self._redraw_waveform(side)

        def hide(_e=None):
            bar.place_forget()

        for w in (container, image_label, video_frame, bar):
            w.bind("<Enter>", show)
            w.bind("<Leave>", lambda e, b=bar: self._hide_bar_if_left(side, b))

        # Waveform / scrub interactions
        wave.bind("<ButtonPress-1>", lambda e: self._wave_press(side, e))
        wave.bind("<B1-Motion>", lambda e: self._wave_drag(side, e))
        wave.bind("<ButtonRelease-1>", lambda e: self._wave_release(side, e))
        wave.bind("<Motion>", lambda e: self._wave_motion(side, e))
        wave.bind("<Leave>", lambda e: self._hide_wave_tooltip())
        wave.bind("<Configure>", lambda e: self._redraw_waveform_debounced(side))

        # Speed changes
        speed_box.bind("<<ComboboxSelected>>", lambda e: self.set_speed_from_ui(side))

    def _hide_bar_if_left(self, side: str, bar: tk.Frame):
        # hide after short delay if pointer isn't over container/bar
        def do():
            try:
                x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
                w = self.root.winfo_containing(x, y)
                # if pointer is within bar or within the main container, keep shown
                container = self.left_container if side == "a" else self.right_container
                if w and (self._is_descendant(w, bar) or self._is_descendant(w, container)):
                    return
            except Exception:
                pass
            bar.place_forget()
        self.root.after(120, do)

    def _is_descendant(self, widget: tk.Widget, ancestor: tk.Widget) -> bool:
        w = widget
        while w is not None:
            if w == ancestor:
                return True
            try:
                w = w.master
            except Exception:
                break
        return False

    def _begin_scrub(self, side: str):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            return
        st["scrubbing"] = True
        try:
            st["vlc_was_playing_before_seek"] = bool(player.is_playing())
            player.pause()
        except Exception:
            st["vlc_was_playing_before_seek"] = False

    def _end_scrub(self, side: str):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            st["scrubbing"] = False
            return

        frac = st.get("pending_seek_frac")
        total = int(st.get("vlc_total_ms") or 0)
        if frac is not None and total > 0:
            try:
                player.set_time(max(0, min(total, int(frac * total))))
            except Exception:
                pass

        was_playing = bool(st.get("vlc_was_playing_before_seek"))
        st["pending_seek_frac"] = None
        st["scrubbing"] = False
        if was_playing:
            try:
                player.play()
            except Exception:
                pass

    def _update_video_controls_state(self):
        for side in ("a", "b"):
            st = self._side[side]
            ui = st.get("ui")
            if not ui:
                continue

            is_video = (st.get("media_kind") == "video")
            player = st.get("vlc_player")
            ready = bool(st.get("vlc_ready"))

            # Enable/disable controls
            ui["play"].configure(state=("normal" if is_video else "disabled"))
            state_ready = ("normal" if (is_video and player and ready) else "disabled")
            for k in ("mute", "loop", "back", "fwd", "speed", "fs"):
                try:
                    ui[k].configure(state=state_ready)
                except Exception:
                    pass

            # Play label
            if not is_video:
                ui["play"].configure(text="Play")
            elif not player:
                ui["play"].configure(text="Play")
            elif not ready:
                ui["play"].configure(text="Init…")
            else:
                try:
                    playing = bool(player.is_playing())
                except Exception:
                    playing = False
                ui["play"].configure(text=("Pause" if playing else "Play"))

            # Mute label
            if player and ready:
                try:
                    muted = bool(player.audio_get_mute())
                except Exception:
                    muted = True
                ui["mute"].configure(text=("Unmute" if muted else "Mute"))
            else:
                ui["mute"].configure(text="Mute")

            # Loop label
            loop_on = bool(st.get("vlc_loop", True))
            ui["loop"].configure(text=("Loop On" if loop_on else "Loop Off"))

            # Speed label (sync from player if possible)
            if player and ready:
                try:
                    r = float(player.get_rate() or 1.0)
                except Exception:
                    r = 1.0
                known = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0]
                nearest = min(known, key=lambda x: abs(x - r))
                ui["speed_var"].set(f"{nearest:g}x")
            else:
                ui["speed_var"].set("1.0x")



    # -------------------- video control helpers (seek, speed, fullscreen, waveform) --------------------
    def seek_relative(self, side: str, delta_ms: int):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            return
        try:
            cur = int(player.get_time() or 0)
        except Exception:
            cur = 0
        total = int(st.get("vlc_total_ms") or 0)
        new_t = cur + int(delta_ms)
        if total > 0:
            new_t = max(0, min(total, new_t))
        else:
            new_t = max(0, new_t)
        try:
            player.set_time(new_t)
        except Exception:
            return
        self._update_playhead(side, new_t, total)

    def set_speed_from_ui(self, side: str):
        st = self._side[side]
        ui = st.get("ui")
        player = st.get("vlc_player")
        if not ui or not player or not st.get("vlc_ready"):
            return
        s = (ui["speed_var"].get() or "1.0x").strip().lower().replace("×", "x")
        try:
            rate = float(s.replace("x", ""))
        except Exception:
            rate = 1.0
        rate = max(0.25, min(4.0, rate))
        try:
            player.set_rate(rate)
        except Exception:
            pass
        ui["speed_var"].set(f"{rate:g}x")

    def toggle_fullscreen(self, side: str):
        if getattr(self, "_fs_active", False):
            self._exit_fullscreen()
        else:
            self._enter_fullscreen(side)

    def _enter_fullscreen(self, side: str):
        self._fs_active = True
        self._fs_side = side
        try:
            self._fs_prev_geom = self.root.geometry()
        except Exception:
            self._fs_prev_geom = None
        self._fs_prev_sidebar_visible = bool(getattr(self, "sidebar_visible", True))

        # Hide sidebar
        try:
            if getattr(self, "sidebar_visible", True):
                self.toggle_sidebar()
        except Exception:
            pass

        # Hide the other side container
        try:
            if side == "a":
                self.right_container.pack_forget()
            else:
                self.left_container.pack_forget()
        except Exception:
            pass

        # Fullscreen the root
        try:
            self.root.attributes("-fullscreen", True)
        except Exception:
            pass

        # Exit button + ESC binding
        if not hasattr(self, "_fs_exit_btn") or self._fs_exit_btn is None:
            self._fs_exit_btn = tk.Button(
                self.root,
                text="Exit Fullscreen (Esc)",
                bg=DARK_BG,
                fg=TEXT_COLOR,
                activebackground=ACCENT,
                relief="flat",
                command=self._exit_fullscreen,
            )
        try:
            self._fs_exit_btn.place(relx=1.0, x=-10, y=10, anchor="ne")
        except Exception:
            pass
        self.root.bind("<Escape>", lambda e: self._exit_fullscreen())

    def _exit_fullscreen(self):
        try:
            self.root.attributes("-fullscreen", False)
        except Exception:
            pass

        # Restore both containers
        try:
            if not self.left_container.winfo_ismapped():
                self.left_container.pack(**getattr(self, "_left_pack_opts", dict(side="left", fill="both", expand=True, padx=(6, 3), pady=6)))
            if not self.right_container.winfo_ismapped():
                self.right_container.pack(**getattr(self, "_right_pack_opts", dict(side="left", fill="both", expand=True, padx=(3, 6), pady=6)))
        except Exception:
            pass

        # Restore sidebar if it was visible
        try:
            if getattr(self, "_fs_prev_sidebar_visible", True) and not getattr(self, "sidebar_visible", True):
                self.toggle_sidebar()
        except Exception:
            pass

        try:
            if hasattr(self, "_fs_exit_btn") and self._fs_exit_btn is not None:
                self._fs_exit_btn.place_forget()
        except Exception:
            pass

        self._fs_active = False
        self._fs_side = None
        try:
            self.root.unbind("<Escape>")
        except Exception:
            pass

        # Restore geometry
        try:
            if getattr(self, "_fs_prev_geom", None):
                self.root.geometry(self._fs_prev_geom)
        except Exception:
            pass

    # -------------------- waveform + scrub canvas --------------------
    def _ffmpeg_exe(self) -> Optional[str]:
        if self._ffmpeg_exe_cache is not None:
            return self._ffmpeg_exe_cache.get("path")
        result: Optional[str] = None
        try:
            import imageio_ffmpeg
            exe = imageio_ffmpeg.get_ffmpeg_exe()
            if exe and os.path.exists(exe):
                result = exe
        except Exception:
            pass
        if result is None:
            try:
                exe = shutil.which("ffmpeg")
                if exe:
                    result = exe
            except Exception:
                pass
        self._ffmpeg_exe_cache = {"path": result}
        return result

    def _cleanup_waveform_cache(self):
        try:
            out_dir = Path(tempfile.gettempdir()) / "image_duel_ranker_waveforms"
            if not out_dir.exists():
                return
            stamp = out_dir / "cache_v4.stamp"
            if not stamp.exists():
                # One-time wipe: old PNGs were generated with a broken ffmpeg command
                # and a broken blank-detection heuristic; none should be trusted.
                for f in out_dir.glob("wave_*.png"):
                    try:
                        f.unlink(missing_ok=True)
                    except Exception:
                        pass
                stamp.touch()
            else:
                # Ongoing: evict PNGs older than 7 days.
                cutoff = time.time() - 7 * 86400
                for f in out_dir.glob("wave_*.png"):
                    try:
                        if f.stat().st_mtime < cutoff:
                            f.unlink(missing_ok=True)
                    except Exception:
                        pass
        except Exception:
            pass

    def _maybe_request_waveform(self, side: str):
        st = self._side[side]
        ui = st.get("ui")
        if not ui:
            return
        path = st.get("vlc_media")
        if not path:
            row = st.get("row")
            if row:
                path = row[1]
        if not path or not os.path.exists(path):
            return

        try:
            mtime = int(os.path.getmtime(path))
        except Exception:
            mtime = 0
        key = f"{path}|{mtime}"
        if st.get("waveform_key") == key and st.get("waveform_ready"):
            return

        st["waveform_key"] = key
        st["waveform_ready"] = False
        st["waveform_img"] = None
        st["waveform_src"] = None
        st["waveform_img_size"] = None
        st["waveform_status"] = "loading"

        # Clean up stale cached PNGs once per session (runs on a background thread).
        if not self._waveform_cache_cleaned:
            self._waveform_cache_cleaned = True
            threading.Thread(target=self._cleanup_waveform_cache, daemon=True).start()

        # Only skip if the running job is already working on this exact key.
        # If the key changed (new media), fall through and start a new thread; the old
        # thread self-aborts in its done() callback when it sees waveform_key != its key.
        if st.get("waveform_job") is not None and st.get("waveform_job_key") == key:
            return

        exe = self._ffmpeg_exe()
        if not exe:
            return

        t = threading.Thread(target=self._waveform_worker, args=(side, path, key, exe), daemon=True)
        st["waveform_job"] = t
        st["waveform_job_key"] = key
        t.start()

    def _waveform_worker(self, side: str, path: str, key: str, exe: str):
        try:
            out_dir = Path(tempfile.gettempdir()) / "image_duel_ranker_waveforms"
            out_dir.mkdir(parents=True, exist_ok=True)
            h = hashlib.md5(key.encode("utf-8")).hexdigest()
            out_png = out_dir / f"wave_{h}.png"

            r = None
            name = Path(path).name
            if not out_png.exists():
                # [0:a] explicitly routes the first audio stream into showwavespic.
                # Without it, ffmpeg can't always auto-connect for video container inputs
                # and may silently write a blank PNG.
                cmd = [
                    exe, "-hide_banner", "-loglevel", "error",
                    "-i", path,
                    "-filter_complex", "[0:a]showwavespic=s=800x200:split_channels=0:scale=cbrt:draw=full[v]",
                    "-map", "[v]",
                    "-frames:v", "1",
                    "-y", str(out_png)
                ]
                r = subprocess.run(cmd, check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                print(f"[waveform] {name}: rc={r.returncode} png={out_png.exists()}")
                if r.stderr.strip():
                    print(f"[waveform] {name}: stderr={r.stderr.strip()[:300]}")
                # If ffmpeg returned non-zero, delete any partial output so it isn't cached.
                if r.returncode != 0 and out_png.exists():
                    try:
                        out_png.unlink()
                    except Exception:
                        pass

            # If ffmpeg failed (commonly: no audio stream), we still proceed and show a placeholder.
            if not out_png.exists():
                img = None
                status = "error"
                try:
                    err = (getattr(r, "stderr", "") or "").lower()
                    # Heuristic: if ffmpeg complains about missing audio, treat as "no-audio".
                    if ("audio" in err and ("matches no streams" in err or "stream specifier" in err or "no such file or directory" not in err)):
                        status = "no-audio"
                except Exception:
                    pass
                print(f"[waveform] {name}: no png → status={status}")
            else:
                img = Image.open(str(out_png)).convert("RGBA")
                status = ""
                # Blank-detection: showwavespic draws white waveform on black background, so
                # the max pixel value should be near 255 for any video with real audio.
                # Only treat as blank if the max is essentially zero (truly no waveform drawn).
                # NOTE: do NOT use p95 here — for a normal waveform <95% of pixels are
                # non-black, so the 95th-percentile value is always 0 regardless of audio.
                try:
                    gray = img.convert("L")
                    mx = int(gray.getextrema()[1] or 0)
                    print(f"[waveform] {name}: png loaded, max_pixel={mx}")
                    if mx < 8:
                        # Truly blank — evict from cache so next load retries ffmpeg.
                        try:
                            out_png.unlink(missing_ok=True)
                        except Exception:
                            pass
                        img = None
                        status = "no-audio"
                        print(f"[waveform] {name}: blank png evicted")
                    else:
                        hx = ACCENT.lstrip("#")
                        if len(hx) == 3:
                            hx = "".join([c*2 for c in hx])
                        r0, g0, b0 = int(hx[0:2], 16), int(hx[2:4], 16), int(hx[4:6], 16)
                        noise_floor = 4   # suppress near-black background pixels
                        alpha = gray.point(lambda p: 0 if p <= noise_floor else min(255, int((p - noise_floor) * 3)))
                        # Thicken + smooth for better readability at small UI heights.
                        try:
                            alpha = alpha.filter(ImageFilter.MaxFilter(5))
                        except Exception:
                            pass
                        try:
                            alpha = alpha.filter(ImageFilter.GaussianBlur(0.6))
                        except Exception:
                            pass
                        try:
                            if int(alpha.getextrema()[1] or 0) == 0:
                                img = None
                                status = "no-audio"
                        except Exception:
                            pass
                        if status != "no-audio":
                            col = Image.new("RGBA", img.size, (r0, g0, b0, 255))
                            col.putalpha(alpha)
                            img = col
                except Exception:
                    pass


            def done():
                st = self._side.get(side)
                if not st:
                    return
                if st.get("waveform_key") != key:
                    return
                ui = st.get("ui")
                if not ui:
                    return

                # Store source image; scale on-demand in _redraw_waveform
                st["waveform_src"] = img
                st["waveform_img"] = None
                st["waveform_img_size"] = None
                st["waveform_ready"] = True
                st["waveform_status"] = status
                st["waveform_job"] = None
                st["waveform_job_key"] = None
                self._redraw_waveform(side)

            self.root.after(0, done)
        except Exception:
            def clear():
                st = self._side.get(side)
                if st:
                    st["waveform_job"] = None
                    st["waveform_job_key"] = None
            try:
                self.root.after(0, clear)
            except Exception:
                pass

    def _redraw_waveform_debounced(self, side: str):
        st = self._side[side]
        job = st.get("waveform_resize_job")
        if job:
            try:
                self.root.after_cancel(job)
            except Exception:
                pass
        st["waveform_resize_job"] = self.root.after(40, lambda: self._redraw_waveform(side))

    def _redraw_waveform(self, side: str):
        st = self._side[side]
        ui = st.get("ui")
        if not ui:
            return
        c = ui["wave"]
        try:
            c.delete("wave")
            c.delete("playhead")
        except Exception:
            return


        # Ensure waveform PhotoImage matches current canvas size (canvas may have been 1px wide when generated).
        img_to_draw = None
        if st.get("waveform_ready"):
            src = st.get("waveform_src")
            try:
                w = max(1, int(c.winfo_width() or 1))
                h = max(1, int(c.winfo_height() or 1))
            except Exception:
                w, h = 1, 1

            if src is not None:
                try:
                    if st.get("waveform_img") is None or st.get("waveform_img_size") != (w, h):
                        im2 = src.resize((w, h), Image.BILINEAR)
                        st["waveform_img"] = ImageTk.PhotoImage(im2)
                        st["waveform_img_size"] = (w, h)
                    img_to_draw = st.get("waveform_img")
                except Exception:
                    img_to_draw = None

        if img_to_draw is not None:
            try:
                c.create_image(0, 0, anchor="nw", image=img_to_draw, tags="wave")
            except Exception:
                pass
        else:
            try:
                w = max(1, int(c.winfo_width() or 1))
                h = max(1, int(c.winfo_height() or 1))
                c.create_line(0, h // 2, w, h // 2, fill=TEXT_COLOR, stipple="gray50", tags="wave")

                status = (st.get("waveform_status") or "").strip()
                if status == "loading":
                    c.create_text(6, h // 2, anchor="w", text="Waveform…", fill=TEXT_COLOR, font=("Segoe UI", 8), tags="wave")
                elif status == "no-audio":
                    c.create_text(w - 6, h // 2, anchor="e", text="No audio", fill=TEXT_COLOR, font=("Segoe UI", 8), tags="wave")
                elif status == "error":
                    c.create_text(w - 6, h // 2, anchor="e", text="Waveform unavailable", fill=TEXT_COLOR, font=("Segoe UI", 8), tags="wave")
            except Exception:
                pass

        try:
            player = st.get("vlc_player")
            if player and st.get("vlc_ready"):
                cur = int(player.get_time() or 0)
                total = int(st.get("vlc_total_ms") or 0)
                self._update_playhead(side, cur, total)
        except Exception:
            pass

    def _update_playhead(self, side: str, cur_ms: int, total_ms: int):
        st = self._side[side]
        ui = st.get("ui")
        if not ui:
            return
        c = ui["wave"]
        try:
            c.delete("playhead")
        except Exception:
            return
        w = max(1, int(c.winfo_width() or 1))
        h = max(1, int(c.winfo_height() or 1))
        frac = 0.0 if total_ms <= 0 else max(0.0, min(1.0, float(cur_ms) / float(total_ms)))
        x = int(frac * w)
        try:
            # Track + progress line (YouTube-like)
            track_y = max(1, h - 2)
            c.create_line(0, track_y, w, track_y, fill="#40454d", width=2, tags="playhead")
            c.create_line(0, track_y, x, track_y, fill=ACCENT, width=2, tags="playhead")
            # Playhead
            c.create_line(x, 0, x, h, fill=ACCENT, width=2, tags="playhead")
            # Small handle near the track
            c.create_rectangle(max(0, x - 2), max(0, track_y - 4), min(w, x + 2), min(h, track_y + 4), fill=ACCENT, outline="", tags="playhead")
        except Exception:
            pass

    def _wave_event_fraction(self, side: str, event) -> Optional[float]:
        st = self._side[side]
        ui = st.get("ui")
        if not ui:
            return None
        c = ui["wave"]
        w = max(1, int(c.winfo_width() or 1))
        x = max(0, min(w, int(getattr(event, "x", 0))))
        frac = float(x) / float(w)
        return max(0.0, min(1.0, frac))

    def _wave_press(self, side: str, event):
        st = self._side[side]
        player = st.get("vlc_player")
        if not player or not st.get("vlc_ready"):
            return
        self._begin_scrub(side)
        frac = self._wave_event_fraction(side, event)
        if frac is None:
            return
        st["pending_seek_frac"] = frac
        total = int(st.get("vlc_total_ms") or 0)
        self._update_playhead(side, int(frac * total) if total > 0 else 0, total)
        self._wave_motion(side, event)

    def _wave_drag(self, side: str, event):
        st = self._side[side]
        if not st.get("scrubbing"):
            return
        frac = self._wave_event_fraction(side, event)
        if frac is None:
            return
        st["pending_seek_frac"] = frac
        total = int(st.get("vlc_total_ms") or 0)
        self._update_playhead(side, int(frac * total) if total > 0 else 0, total)

    def _wave_release(self, side: str, event):
        st = self._side[side]
        if not st.get("scrubbing"):
            return
        frac = self._wave_event_fraction(side, event)
        if frac is not None:
            st["pending_seek_frac"] = frac
        self._end_scrub(side)

    def _ensure_wave_tooltip(self):
        if getattr(self, "_wave_tip", None) is None:
            self._wave_tip = tk.Label(
                self.root,
                text="",
                bg="#111111",
                fg=TEXT_COLOR,
                font=("Segoe UI", 8),
                bd=1,
                relief="solid",
                padx=6,
                pady=2,
            )
            self._wave_tip.place_forget()

    def _show_wave_tooltip(self, x_root: int, y_root: int, text: str):
        self._ensure_wave_tooltip()
        self._wave_tip.configure(text=text)
        # Keep within window bounds a bit
        rx = self.root.winfo_rootx()
        ry = self.root.winfo_rooty()
        rw = self.root.winfo_width()
        rh = self.root.winfo_height()
        x = (x_root - rx) + 10
        y = (y_root - ry) - 28
        x = max(6, min(rw - 80, x))
        y = max(6, min(rh - 30, y))
        self._wave_tip.place(x=x, y=y)

    def _hide_wave_tooltip(self):
        tip = getattr(self, "_wave_tip", None)
        if tip is not None:
            tip.place_forget()

    def _wave_motion(self, side: str, event):
        st = self._side.get(side)
        if not st:
            return
        frac = self._wave_event_fraction(side, event)
        total = int(st.get("vlc_total_ms") or 0)
        if frac is None or total <= 0:
            self._hide_wave_tooltip()
            return
        target = int(frac * total)
        self._show_wave_tooltip(event.x_root, event.y_root, self._format_mmss(target))

    def _on_metric_menu_select(self, _event=None):
        menu = getattr(self, "metric_menu", None)
        if not menu:
            return
        try:
            active = menu.index("active")
        except Exception:
            active = None
        if active is None:
            self._hide_ui_tooltip()
            return
        try:
            metric_key = menu.entrycget(active, "value")
        except Exception:
            metric_key = None
        if not metric_key:
            self._hide_ui_tooltip()
            return
        text = self._metric_tooltips.get(metric_key, self._metric_human(metric_key))
        self._show_ui_tooltip_at_pointer(text)

    def _metric_human(self, metric_key: Optional[str] = None) -> str:
        key = metric_key or self.metric
        return {
            "avg": "Simple Avg",
            "shrunken_avg": f"Shrunken Avg (prior={FOLDER_PRIOR_IMAGES})",
            "dislikes_adjusted": f"Shrunken Avg + volume − dislike rate",
            "lcb": f"Lower Conf. Bound (z={LCB_Z})"
        }.get(key, key)

    def _set_metric(self, metric_key: str) -> None:
        if metric_key not in {"shrunken_avg", "dislikes_adjusted", "avg", "lcb"}:
            metric_key = "shrunken_avg"
        self.metric = metric_key
        self.metric_var.set(metric_key)
        self.metric_btn.configure(text=f"Metric: {self._metric_human(metric_key)}")
        self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
        self.page = 0
        self.update_sidebar()

    def on_metric_change(self) -> None:
        self._set_metric(self.metric_var.get())

    def toggle_metric(self):
        order = ["shrunken_avg", "dislikes_adjusted", "avg", "lcb"]
        i = order.index(self.metric) if self.metric in order else 0
        self._set_metric(order[(i + 1) % len(order)])

    def change_page(self, delta: int):
        leader = folder_leaderboard(self.conn, metric=self.metric)
        total_pages = max(1, math.ceil(len(leader) / LEADERBOARD_SIZE))
        self.page = (self.page + delta) % total_pages
        self.update_sidebar()

    def toggle_sparklines(self):
        self.sparkline_enabled = not self.sparkline_enabled
        if self.sparkline_enabled:
            self.spark_toggle_btn.configure(text="Sparklines: On", fg=ACCENT)
        else:
            self.spark_toggle_btn.configure(text="Sparklines: Off", fg=INFO_BAR_FG)
        self.update_sidebar()

    def cycle_sparkline_window(self):
        idx = list(SPARKLINE_WINDOWS).index(self.sparkline_window) if self.sparkline_window in SPARKLINE_WINDOWS else 0
        self.sparkline_window = SPARKLINE_WINDOWS[(idx + 1) % len(SPARKLINE_WINDOWS)]
        self.spark_window_btn.configure(text=f"W: {self.sparkline_window}")
        if self.sparkline_enabled:
            self.update_sidebar()

    def _format_delta(self, folder: str, leader: List[dict]) -> str:
        old = self._last_ranks.get(folder)
        now, _, _, _ = find_folder_rank(leader, folder)
        if not now:
            return ""
        if old is None:
            return " (new)"
        d = old - now
        return f"  ↑{d}" if d > 0 else (f"  ↓{abs(d)}" if d < 0 else "  →0")

    def update_sidebar(self):
        if not self.current:
            return
        a, b = self.current
        folder_left = a[2]
        folder_right = b[2] if b[0] >= 0 else None

        leader = folder_leaderboard(self.conn, metric=self.metric)
        total = len(leader)
        total_pages = max(1, math.ceil(total / LEADERBOARD_SIZE))
        self.page = min(self.page, total_pages - 1)
        start = self.page * LEADERBOARD_SIZE
        end = min(start + LEADERBOARD_SIZE, total)

        self.metric_btn.configure(text=f"Metric: {self._metric_human(self.metric)}")
        self.page_label.configure(text=f"Page {self.page+1}/{total_pages}  (total {total})")

        # Leaderboard lines
        def trunc(name: str) -> str:
            return name if len(name) <= LEAF_MAX else (name[:LEAF_MAX - 1] + "…")

        # Build display list — pin off-page current artists to top or bottom based on their rank
        _vis         = int(self.board.cget('height'))  # visible row count in board widget
        page_rows    = list(leader[start:end])
        page_folders = {r["folder"] for r in page_rows}
        pin_left  = folder_left  is not None and folder_left  not in page_folders
        pin_right = folder_right is not None and folder_right not in page_folders
        page_top_rank = page_rows[0]["rank"] if page_rows else 0

        display_rows = list(page_rows)
        if display_rows:
            last_vis = min(len(display_rows) - 1, _vis - 1)
            pins = []
            for folder, do_pin in ((folder_left, pin_left), (folder_right, pin_right)):
                if do_pin:
                    row = next((r for r in leader if r["folder"] == folder), None)
                    if row:
                        pins.append(row)
            # Above-page artists: better rank first → slots 0, 1, …
            above = sorted([r for r in pins if r["rank"] < page_top_rank], key=lambda r: r["rank"])
            for i, row in enumerate(above):
                if i <= last_vis:
                    display_rows[i] = row
            # Below-page artists: worse rank last → slots last_vis, last_vis-1, …
            below = sorted([r for r in pins if r["rank"] >= page_top_rank], key=lambda r: r["rank"], reverse=True)
            for i, row in enumerate(below):
                ri = last_vis - i
                if ri >= 0:
                    display_rows[ri] = row

        lines = []
        deltas: List[Tuple[int, str]] = []
        spark_info: List[Optional[Tuple[int, List[str]]]] = []  # (col_start, per-char tags)

        # First pass: collect raw values so we can compute per-column max widths
        row_parts = []
        for idx, row in enumerate(display_rows):
            leaf = trunc(Path(row["folder"]).name)
            old_rank = self._last_ranks.get(row["folder"])
            if old_rank is None:
                ticker, ticker_tag = "▲", "delta_new"
            else:
                shift = old_rank - row["rank"]
                if shift > 0:
                    ticker, ticker_tag = "▲", "delta_up"
                elif shift < 0:
                    ticker, ticker_tag = "▼", "delta_down"
                else:
                    ticker, ticker_tag = "•", "delta_flat"
            row_parts.append((idx, row, ticker, ticker_tag, leaf))

        def _col_w(p): return len(str(p[1].get("wins", 0)))
        def _col_l(p): return len(str(p[1].get("losses", 0)))
        def _col_d(p): return len(str(p[1].get("dislikes_n", 0)))
        def _col_n(p): return len(str(p[1]["n"]))
        mw    = max((_col_w(p) for p in row_parts), default=1)
        ml    = max((_col_l(p) for p in row_parts), default=1)
        md    = max((_col_d(p) for p in row_parts), default=1)
        mn    = max((_col_n(p) for p in row_parts), default=1)
        mleaf = max((len(p[4]) for p in row_parts), default=1)

        # Second pass: build lines with per-column aligned stats
        highlight_lines: List[Tuple[int, str]] = []  # (line_idx, tag)
        for (idx, row, ticker, ticker_tag, leaf) in row_parts:
            if self.metric == "avg":
                pre = f"{ticker} {row['rank']:>3}. {leaf:<{mleaf}} {row['avg']:6.1f}  "
            else:
                pre = f"{ticker} {row['rank']:>3}. {leaf:<{mleaf}} {row['score']:6.1f}  "
            w  = str(row.get("wins",       0))
            lo = str(row.get("losses",     0))
            d  = str(row.get("dislikes_n", 0))
            n  = str(row["n"])
            if self.metric == "dislikes_adjusted":
                stats = f"▲={w:<{mw}} ▼={lo:<{ml}} d={d:<{md}} n={n:<{mn}}"
            else:
                stats = f"▲={w:<{mw}} ▼={lo:<{ml}} n={n:<{mn}}"
            if self.sparkline_enabled:
                rates = folder_sparkline(self.conn, row["folder"], window=self.sparkline_window)
                if rates:
                    spark_str = render_sparkline(rates)
                    stags     = [_spark_tag_for_rate(r) for r in rates]
                else:
                    spark_str = "·" * SPARKLINE_BUCKETS
                    stags     = ["spark_none"] * SPARKLINE_BUCKETS
                col_start = len(pre) + len(stats) + 1
                line = pre + stats + " " + spark_str
                spark_info.append((col_start, stags))
            else:
                line = pre + stats
                spark_info.append(None)
            lines.append(line)
            deltas.append((idx, ticker_tag))
            if row["folder"] == folder_left:
                highlight_lines.append((idx, "hl_left"))
            elif row["folder"] == folder_right:
                highlight_lines.append((idx, "hl_right"))

        self.board.configure(state="normal")
        self.board.delete("1.0", "end")
        if lines:
            self.board.insert("1.0", "\n".join(lines))
            for row_idx, tag in deltas:
                self.board.tag_add(tag, f"{row_idx + 1}.0", f"{row_idx + 1}.1")
            for row_idx, si in enumerate(spark_info):
                if si is not None:
                    col_start, stags = si
                    for ci, stag in enumerate(stags):
                        self.board.tag_add(stag,
                            f"{row_idx + 1}.{col_start + ci}",
                            f"{row_idx + 1}.{col_start + ci + 1}")
            for line_idx, hl_tag in highlight_lines:
                self.board.tag_add(hl_tag, f"{line_idx + 1}.0", f"{line_idx + 1}.end")
        else:
            self.board.insert("1.0", "No folders yet.")
        self.board.configure(state="disabled")

        # Current / previous rank lines
        l_rank, l_avg, l_n, _ = find_folder_rank(leader, folder_left)
        r_rank, r_avg, r_n, _ = find_folder_rank(leader, folder_right)
        left_leaf = Path(folder_left).name
        right_leaf = Path(folder_right).name

        l_line = (f"Left:  #{l_rank} {left_leaf} — {l_avg:.1f} (n={l_n}){self._format_delta(folder_left, leader)}"
                  if l_rank else f"Left:  {left_leaf} — (unranked)")
        r_line = (f"Right: #{r_rank} {right_leaf} — {r_avg:.1f} (n={r_n}){self._format_delta(folder_right, leader)}"
                  if r_rank else f"Right: {right_leaf} — (unranked)")

        prev_display = []
        seen = {folder_left, folder_right}
        for f in self.prev_artists:
            if f in seen:
                continue
            seen.add(f)
            pr, pa, pn, _ = find_folder_rank(leader, f)
            leaf = Path(f).name
            if pr:
                prev_display.append(f"• Prev: #{pr} {leaf} — {pa:.1f} (n={pn}){self._format_delta(f, leader)}")
            else:
                prev_display.append(f"• Prev: {leaf} — (unranked)")
            if len(prev_display) >= 2:
                break

        self.now.configure(text="\n".join([l_line, r_line] + prev_display))

        # Links for current duel
        left_url = e621_url_for_path(a[1])
        right_url = e621_url_for_path(b[1])
        self.link_left.url = left_url or ""
        self.link_right.url = right_url or ""
        self.link_left.configure(
            text=f"Left e621: {left_url}" if left_url else "Left e621: (n/a)",
            fg=LINK_COLOR if left_url else TEXT_COLOR,
            cursor="hand2" if left_url else "arrow",
        )
        self.link_right.configure(
            text=f"Right e621: {right_url}" if right_url else "Right e621: (n/a)",
            fg=LINK_COLOR if right_url else TEXT_COLOR,
            cursor="hand2" if right_url else "arrow",
        )

        # Counters
        self.counters_text.configure(text=self._counters_block(a, b))


    def _update_info_bars(self, a: tuple, b: tuple):
        """Populate the top overlay info bars for left/right panels."""
        def fmt(row: tuple) -> str:
            if row and row[0] < 0:
                return "(no opponent in this tag group)"
            folder = Path(row[2]).name if row and len(row) > 2 else "(unknown)"
            p = Path(row[1]) if row and len(row) > 1 else Path("")
            ext = p.suffix.lower().lstrip(".")
            score = float(row[6]) if row and len(row) > 6 else 0.0
            duels = int(row[3]) if row and len(row) > 3 else 0
            w = int(row[4]) if row and len(row) > 4 else 0
            losses = int(row[5]) if row and len(row) > 5 else 0
            return f"{folder}   •  {ext.upper()}  •  {score:.1f}  •  W{w} L{losses}  •  shown {duels}"
        try:
            self.left_info_text.configure(text=fmt(a))
            self.right_info_text.configure(text=fmt(b))
        except Exception:
            pass

    def _counters_block(self, a: tuple, b: tuple) -> str:
        def img_line(prefix: str, row: tuple) -> str:
            return f"{prefix}: duels={row[3]:>4}  W={row[4]:>4}  L={row[5]:>4}  score={row[6]:7.2f}"
        if b[0] < 0:
            return f"{img_line('Left ', a)}\nRight: (no opponent)"
        return "\n".join([img_line("Left ", a), img_line("Right", b)])

    def _keybind_text(self) -> str:
        return "\n".join([
            "Keybinds:",
            "L Click: Vote",
            "R Click: Skip",
            "M Click: Hide",
            "",
            "Ctrl + L Click: More Options",
            "",
            "1: Vote Left",
            "2: Vote Right",
            "3: Focus Left",
            "6: Focus Right",
            "7: Skip Left",
            "8: Skip Right",
            "9: Toggle Sidebar",
            "0: Skip Both (no score)",
            ".: Toggle Blur",
            "h: History / Rollback",
        ])

    def _on_ctrl_options(self, side: str, event=None):
        self.show_side_options(side, event)
        return "break"

    def focus_side(self, side: str) -> None:
        """Focus one side by entering fullscreen for that side."""
        try:
            self._enter_fullscreen(side)
        except Exception:
            pass

    def show_side_options(self, side: str, event=None) -> None:
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label="Skip", command=lambda s=side: self.skip_side(s))
        menu.add_command(label="Hide", command=lambda s=side: self.hide_side(s))
        menu.add_command(label="Undo tag/hide", command=lambda s=side: self.undo_side_tag_hide(s))
        menu.add_separator()
        menu.add_command(label="Open image/video", command=self.open_left if side == "a" else self.open_right)
        menu.add_command(label="Reveal folder", command=self.reveal_left_folder if side == "a" else self.reveal_right_folder)
        menu.add_command(label="Focus this side", command=lambda s=side: self.focus_side(s))
        menu.add_separator()
        menu.add_command(label="Toggle leaderboard metric", command=self.toggle_metric)
        menu.add_command(label="View/open e621 links", command=self.show_links_view)
        menu.add_command(label="DB stats", command=self.show_db_stats)
        menu.add_command(label="History / Rollback…", command=self.show_history_manager)
        menu.add_command(label="Toggle blur", command=self.toggle_blur)
        try:
            if event is not None:
                menu.tk_popup(event.x_root, event.y_root)
            else:
                x = self.root.winfo_rootx() + self.root.winfo_width() // 2
                y = self.root.winfo_rooty() + self.root.winfo_height() // 2
                menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    # -------------------- file open / reveal --------------------

    def _update_blur_toggle_style(self) -> None:
        bg = ACCENT if self.blur_enabled else DARK_PANEL
        try:
            self.blur_toggle_btn.configure(bg=bg)
        except Exception:
            pass

    def _set_video_blur_visible(self, side: str, visible: bool) -> None:
        st = self._side.get(side, {})
        label = st.get("video_blur_label")
        if not label:
            return
        if visible:
            label.place(relx=0, rely=0, relwidth=1, relheight=1)
            try:
                label.lift()
            except Exception:
                pass
        else:
            label.place_forget()

    def _clear_vlc_blur_logo(self, side: str) -> None:
        st = self._side.get(side, {})
        player = st.get("vlc_player")
        if player:
            try:
                player.video_set_logo_int(vlc.VideoLogoOption.logo_enable, 0)
            except Exception:
                pass
        logo_path = st.get("video_blur_logo_path")
        if logo_path:
            try:
                os.remove(logo_path)
            except Exception:
                pass
        st["video_blur_logo_path"] = None

    def _set_vlc_blur_logo(self, side: str, image: Image.Image) -> None:
        st = self._side.get(side, {})
        player = st.get("vlc_player")
        if not player:
            return
        self._clear_vlc_blur_logo(side)
        try:
            fd, logo_path = tempfile.mkstemp(suffix=".png")
            os.close(fd)
            image.save(logo_path, format="PNG")
        except Exception:
            return
        st["video_blur_logo_path"] = logo_path
        try:
            player.video_set_logo_string(vlc.VideoLogoOption.logo_file, logo_path)
            player.video_set_logo_int(vlc.VideoLogoOption.logo_enable, 1)
            player.video_set_logo_int(vlc.VideoLogoOption.logo_opacity, 255)
            player.video_set_logo_int(vlc.VideoLogoOption.logo_position, 0)
            player.video_set_logo_int(vlc.VideoLogoOption.logo_x, 0)
            player.video_set_logo_int(vlc.VideoLogoOption.logo_y, 0)
        except Exception:
            pass

    def _capture_video_snapshot(self, side: str, size: Tuple[int, int]) -> Optional[Image.Image]:
        st = self._side.get(side, {})
        player = st.get("vlc_player")
        if not player:
            return None
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(suffix=".png")
            os.close(fd)
            try:
                player.video_take_snapshot(0, tmp_path, size[0], size[1])
            except Exception:
                return None
            for _ in range(6):
                try:
                    if os.path.exists(tmp_path) and os.path.getsize(tmp_path) > 0:
                        break
                except Exception:
                    pass
                time.sleep(0.05)
            try:
                with Image.open(tmp_path) as snap:
                    return snap.convert("RGB").copy()
            except Exception:
                return None
        finally:
            if tmp_path:
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass

    def _update_video_blur_overlay(self, side: str, video_frame: tk.Frame, path: str) -> None:
        if not self.blur_enabled:
            self._set_video_blur_visible(side, False)
            self._clear_vlc_blur_logo(side)
            return
        self.root.update_idletasks()
        frame_w = max(1, video_frame.winfo_width())
        frame_h = max(1, video_frame.winfo_height())
        if frame_w <= 5 or frame_h <= 5:
            self.root.after(50, lambda: self._update_video_blur_overlay(side, video_frame, path))
            return
        st = self._side.get(side, {})
        video_size = None
        if HAVE_VLC and st.get("vlc_player"):
            try:
                video_size = st["vlc_player"].video_get_size(0)
            except Exception:
                video_size = None
        if video_size and video_size[0] > 0 and video_size[1] > 0:
            target_w, target_h = video_size
        else:
            target_w, target_h = frame_w, frame_h

        # Run the blocking snapshot poll on a background thread to avoid
        # stalling the Tkinter event loop (VLC writes the file asynchronously).
        def worker():
            raw = self._capture_video_snapshot(side, (target_w, target_h))

            def apply():
                if not self.blur_enabled:
                    return
                snap = raw
                if snap is None:
                    snap = Image.effect_noise((target_w, target_h), 64).convert("RGB")
                if snap.size != (target_w, target_h):
                    snap = snap.resize((target_w, target_h), Image.Resampling.LANCZOS)
                pixelated = self._apply_pixelate(snap, pixel_size=50)
                st2 = self._side.get(side, {})
                if HAVE_VLC and st2.get("vlc_player"):
                    self._set_video_blur_visible(side, False)
                    self._set_vlc_blur_logo(side, pixelated)
                    return
                tk_im = ImageTk.PhotoImage(pixelated)
                label = st2.get("video_blur_label")
                if not label:
                    return
                label.configure(image=tk_im)
                label.image = tk_im
                st2["video_blur_image"] = tk_im
                self._set_video_blur_visible(side, True)

            try:
                self.root.after(0, apply)
            except Exception:
                pass

        threading.Thread(target=worker, daemon=True).start()

    def _set_blur_enabled(self, enabled: bool) -> None:
        if self.blur_enabled == enabled:
            return
        self.blur_enabled = enabled
        self._update_blur_toggle_style()

        for entry in self.duel_history:
            try:
                if self._entry_is_sensitive(entry):
                    # Sensitive entries keep their clear thumb; nullify so _attach_history_thumbs
                    # rebuilds it correctly (without blur_enabled) on next carousel repaint.
                    entry["thumb"] = None
                else:
                    entry["thumb"] = self._build_duel_thumbnail(entry["a_path"], entry["b_path"])
            except Exception:
                entry["thumb"] = None
        for fentry in self.future_queue:
            fentry["thumb"] = None
        # Force live-slot thumbnail to rebuild so it picks up the new blur state.
        if hasattr(self, "_live_thumb_key"):
            self._live_thumb_key = None
        self._update_carousel()

        for side in ("a", "b"):
            st = self._side.get(side, {})
            row = st.get("row")
            if not row:
                continue
            if st.get("media_kind") == "video":
                vframe = self.left_video if side == "a" else self.right_video
                self._update_video_blur_overlay(side, vframe, row[1])

        # Defer media redraw one tick to avoid transient empty frames.
        self.root.after_idle(lambda: self._refresh_visuals_only(force=True))

    def toggle_blur(self):
        self._blur_forced_by_focus = False
        self._set_blur_enabled(not getattr(self, "blur_enabled", False))

    def _on_window_focus_out(self, event=None):
        # FocusOut fires for every child widget too; only react when the
        # focus is leaving the top-level window entirely.
        if event and str(getattr(event, "widget", "")) != str(self.root):
            return
        self._window_was_focused = False
        if not self.blur_enabled:
            self._blur_forced_by_focus = True
            self._set_blur_enabled(True)

    def _on_window_focus_in(self, event=None):
        if event and str(getattr(event, "widget", "")) != str(self.root):
            return
        # Delay restoring the flag so Button-1 fires first and is ignored.
        self.root.after(0, lambda: setattr(self, "_window_was_focused", True))
        if self._blur_forced_by_focus:
            self._blur_forced_by_focus = False
            self._set_blur_enabled(False)

    def toggle_sidebar(self):
        """Toggle the right sidebar (focus mode)."""
        if getattr(self, "sidebar_visible", True):
            try:
                self.sidebar.pack_forget()
            except Exception:
                pass
            self.sidebar_visible = False
            try:
                self.sidebar_restore_btn.place(relx=1.0, x=-10, y=10, anchor="ne")
            except Exception:
                pass
        else:
            try:
                self.sidebar_restore_btn.place_forget()
            except Exception:
                pass
            try:
                self.sidebar.pack(**getattr(self, "_sidebar_pack_opts", dict(side="right", fill="y", padx=(0, 6), pady=6)))
            except Exception:
                self.sidebar.pack(side="right", fill="y", padx=(0, 6), pady=6)
            self.sidebar_visible = True

        try:
            self.keys_text.configure(text=self._keybind_text())
        except Exception:
            pass

    def open_left(self, ev=None):
        if not self.current:
            return
        os.startfile(self.current[0][1])

    def open_right(self, ev=None):
        if not self.current:
            return
        os.startfile(self.current[1][1])

    def reveal_left_folder(self, ev=None):
        if not self.current:
            return
        os.startfile(str(Path(self.current[0][1]).parent))

    def reveal_right_folder(self, ev=None):
        if not self.current:
            return
        os.startfile(str(Path(self.current[1][1]).parent))

    def _open_url(self, url: str):
        if url and url.startswith("http"):
            try:
                webbrowser.open(url)
            except Exception:
                pass

    # -------------------- e621 link generation --------------------
    def _parse_common_tags(self) -> List[str]:
        raw = (self.common_tags_var.get() or "").strip()
        if not raw:
            return []
        return [t for t in raw.split() if t.strip()]

    def _ranked_artist_tags(self) -> List[str]:
        leader = folder_leaderboard(self.conn, metric=self.metric)
        tags: List[str] = []
        seen = set()
        for row in leader:
            leaf = Path(row["folder"]).name.strip()
            if not leaf:
                continue
            leaf = re.sub(r"\s+", "_", leaf)
            if leaf in seen:
                continue
            seen.add(leaf)
            tags.append(leaf)
        return tags

    def _build_e621_urls(self, common_tags: List[str], artist_tags: List[str]) -> List[str]:
        max_artist = E621_MAX_TAGS - len(common_tags)
        if max_artist <= 0:
            raise ValueError(f"Common tags already use {len(common_tags)} tags; e621 max is {E621_MAX_TAGS}.")
        total_items = len(artist_tags)
        if total_items <= 0:
            return []

        # Spread evenly similar to your Excel LET logic
        num_rows = max(1, math.ceil(total_items / min(E621_MAX_OR_TAGS, max_artist)))
        items_per_row = max(1, math.ceil(total_items / num_rows))

        urls: List[str] = []
        for row in range(num_rows):
            start = row * items_per_row
            end = min(start + items_per_row, total_items)
            chunk = artist_tags[start:end]
            if not chunk:
                continue
            tags = list(common_tags) + [f"~{t}" for t in chunk[:max_artist]]
            tag_str = " ".join(tags)
            encoded = quote_plus(tag_str, safe="~()_-.'")
            urls.append(f"https://e621.net/posts?tags={encoded}")
        return urls

    def _get_e621_urls(self) -> Tuple[List[str], List[str], List[str]]:
        common = self._parse_common_tags()
        artists = self._ranked_artist_tags()
        urls = self._build_e621_urls(common, artists)
        return urls, common, artists

    def export_e621_links(self):
        try:
            urls, _, _ = self._get_e621_urls()
        except Exception as e:
            msg = f"Export failed: {e}"
            self.export_status.configure(text=msg)
            return
        if not urls:
            self.export_status.configure(text="No artist tags found to export.")
            return

        out_path = SCRIPT_DIR / "e621_links.txt"
        try:
            out_path.write_text("\n".join(urls) + "\n", encoding="utf-8")
        except Exception as e:
            self.export_status.configure(text=f"Export failed writing file: {e}")
            return

        # copy to clipboard
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(urls))
            self.root.update()
        except Exception:
            pass

        self.export_status.configure(text=f"Wrote {len(urls)} link(s) to {out_path.name} and clipboard.")

    # ---- links viewer window ----
    def show_links_view(self):
        try:
            urls, common, artists = self._get_e621_urls()
        except Exception as e:
            messagebox.showerror("e621 link generation failed", str(e))
            return

        if hasattr(self, "_links_window") and self._links_window and self._links_window.winfo_exists():
            self._links_window.deiconify()
            self._links_window.lift()
            self._links_window.focus_force()
        else:
            self._create_links_window()

        self._links_set_data(urls, common, len(artists))

    def _create_links_window(self):
        self._links_open_cancel = False

        win = tk.Toplevel(self.root)
        win.title("e621 search links")
        win.geometry("1000x650")
        win.configure(bg=DARK_BG)
        self._links_window = win

        def on_close():
            self._links_open_cancel = True
            try:
                win.destroy()
            except Exception:
                pass

        win.protocol("WM_DELETE_WINDOW", on_close)

        info_frame = tk.Frame(win, bg=DARK_BG)
        info_frame.pack(fill="x", padx=10, pady=(10, 6))

        self._links_count_label = tk.Label(info_frame, text="Links: 0", font=("Segoe UI", 10, "bold"),
                                           fg=ACCENT, bg=DARK_BG, anchor="w")
        self._links_count_label.pack(side="left", fill="x", expand=True)

        self._links_common_label = tk.Label(info_frame, text="", font=("Consolas", 9),
                                            fg=TEXT_COLOR, bg=DARK_BG, anchor="e", justify="right")
        self._links_common_label.pack(side="right")

        tags_frame = tk.Frame(win, bg=DARK_BG)
        tags_frame.pack(fill="x", padx=10, pady=(0, 8))
        tk.Label(tags_frame, text="Search tags", font=("Segoe UI", 10, "bold"),
                 fg=ACCENT, bg=DARK_BG).pack(side="left")
        self.common_tags_entry = tk.Entry(tags_frame, textvariable=self.common_tags_var,
                                          font=("Consolas", 9),
                                          bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                                          relief="flat")
        self.common_tags_entry.pack(side="left", fill="x", expand=True, padx=(8, 0))

        btn_frame = tk.Frame(win, bg=DARK_BG)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))

        tk.Button(btn_frame, text="Refresh", command=self._links_refresh,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Export links (clipboard + file)", command=self.export_e621_links,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Copy all", command=self._links_copy_all,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Open selected", command=self._links_open_selected,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Open all", command=self._links_open_all,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Stop opening", command=self._links_stop_opening,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left", padx=(0, 8))
        tk.Button(btn_frame, text="Open links file", command=self._links_open_file,
                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat").pack(side="left")

        list_frame = tk.Frame(win, bg=DARK_BG)
        list_frame.pack(fill="both", expand=True, padx=10, pady=(0, 8))

        # Use grid to avoid broken horizontal scrollbar
        list_frame.grid_rowconfigure(0, weight=1)
        list_frame.grid_columnconfigure(0, weight=1)

        yscroll = tk.Scrollbar(list_frame, orient="vertical")
        xscroll = tk.Scrollbar(list_frame, orient="horizontal")

        lb = tk.Listbox(list_frame, font=("Consolas", 9),
                        bg=DARK_PANEL, fg=TEXT_COLOR, selectbackground=ACCENT,
                        activestyle="none",
                        yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        yscroll.config(command=lb.yview)
        xscroll.config(command=lb.xview)

        lb.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="ew")

        lb.bind("<Double-Button-1>", lambda e: self._links_open_selected())
        self._links_listbox = lb

        self._links_status_label = tk.Label(win, text="", font=("Segoe UI", 9),
                                            fg=TEXT_COLOR, bg=DARK_BG, anchor="w")
        self._links_status_label.pack(fill="x", padx=10, pady=(0, 10))

    def _links_set_data(self, urls: List[str], common_tags: List[str], artist_count: int):
        self._links_listbox.delete(0, "end")
        for u in urls:
            self._links_listbox.insert("end", u)
        try:
            self._links_listbox.xview_moveto(0)
            self._links_listbox.yview_moveto(0)
        except Exception:
            pass

        self._links_count_label.configure(text=f"Links: {len(urls)}   (artists: {artist_count})")
        common_str = " ".join(common_tags) if common_tags else "(none)"
        if len(common_str) > 140:
            common_str = common_str[:137] + "..."
        self._links_common_label.configure(text=f"Common tags: {common_str}")
        self._links_status_label.configure(text="")

    def _links_refresh(self):
        try:
            urls, common, artists = self._get_e621_urls()
            self._links_set_data(urls, common, len(artists))
        except Exception as e:
            messagebox.showerror("Refresh failed", str(e))

    def _links_get_urls(self) -> List[str]:
        return [self._links_listbox.get(i) for i in range(self._links_listbox.size())]

    def _links_get_selected_urls(self) -> List[str]:
        sel = list(self._links_listbox.curselection())
        if not sel:
            try:
                idx = int(self._links_listbox.index("active"))
                if 0 <= idx < self._links_listbox.size():
                    sel = [idx]
            except Exception:
                sel = []
        return [self._links_listbox.get(i) for i in sel]

    def _open_urls_staggered(self, urls: List[str], delay_ms: int = 150):
        self._links_open_cancel = False
        total = len(urls)

        def step(i: int):
            if self._links_open_cancel:
                return
            if i >= total:
                self._links_status_label.configure(text=f"Opened {total} link(s).")
                return
            try:
                webbrowser.open(urls[i])
            except Exception:
                pass
            self._links_status_label.configure(text=f"Opening {i+1}/{total}...")
            self.root.after(delay_ms, lambda: step(i + 1))

        step(0)

    def _links_open_selected(self):
        urls = self._links_get_selected_urls()
        if not urls:
            messagebox.showinfo("Open selected", "Select a link first.")
            return
        self._open_urls_staggered(urls)

    def _links_open_all(self):
        urls = self._links_get_urls()
        if not urls:
            messagebox.showinfo("Open all", "No links to open.")
            return
        ok = messagebox.askyesno("Open all links", f"This will open {len(urls)} browser tab(s). Continue?")
        if ok:
            self._open_urls_staggered(urls)

    def _links_stop_opening(self):
        self._links_open_cancel = True
        self._links_status_label.configure(text="Stopped.")

    def _links_copy_all(self):
        urls = self._links_get_urls()
        if not urls:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(urls))
            self.root.update()
            self._links_status_label.configure(text=f"Copied {len(urls)} link(s) to clipboard.")
        except Exception as e:
            messagebox.showerror("Copy failed", str(e))

    def _links_open_file(self):
        out_path = SCRIPT_DIR / "e621_links.txt"
        try:
            if not out_path.exists():
                urls, _, _ = self._get_e621_urls()
                out_path.write_text("\n".join(urls) + "\n", encoding="utf-8")
            os.startfile(str(out_path))
        except Exception as e:
            messagebox.showerror("Open file failed", str(e))

    # -------------------- Sessions / snapshots / rollback --------------------
    def _open_session(self) -> None:
        """Open a live session row and take an auto start-of-session snapshot."""
        try:
            ts = int(time.time())
            max_cid = int(self.conn.execute("SELECT COALESCE(MAX(id), 0) FROM comparisons").fetchone()[0])
            cur = self.conn.cursor()
            cur.execute(
                "INSERT INTO sessions(started_ts, ended_ts, label, start_comparison_id, note) VALUES (?,?,?,?,?)",
                (ts, None, "live", max_cid, None),
            )
            self.conn.commit()
            self.session_id = cur.lastrowid
            self._session_closed = False
            _take_snapshot(self.conn, kind="auto", label="session start", session_id=self.session_id)
            print(f"[session] opened #{self.session_id} (after comparison #{max_cid})")
        except Exception as ex:
            print(f"[session] open failed: {ex}")
            self.session_id = None

    def _close_session(self) -> None:
        """Stamp ended_ts on the live session. Idempotent (guards against double-close)."""
        if getattr(self, "_session_closed", True):
            return
        self._session_closed = True
        try:
            if self.session_id is not None:
                self.conn.execute(
                    "UPDATE sessions SET ended_ts=? WHERE id=? AND ended_ts IS NULL",
                    (int(time.time()), self.session_id),
                )
                self.conn.commit()
                print(f"[session] closed #{self.session_id}")
        except Exception as ex:
            print(f"[session] close failed: {ex}")

    def undo_last(self, n: int = 1) -> dict:
        """Reverse the last n duels (exact, via stored before-scores) and refresh the UI."""
        res = undo_last_comparisons(self.conn, n=n, session_id=self.session_id)
        if res["undone"]:
            self._reload_after_rollback()
            for img_id in res.get("affected", []):
                row = self.conn.execute("SELECT path, score FROM images WHERE id=?", (img_id,)).fetchone()
                if row:
                    try:
                        threading.Thread(target=update_image_metadata,
                                         args=(Path(row[0]), float(row[1])), daemon=True).start()
                    except Exception:
                        pass
        return res

    def restore_snapshot(self, snapshot_id: int) -> dict:
        """Restore a snapshot's scoring state and refresh the UI (pre-rollback snapshot taken first)."""
        res = restore_snapshot_db(self.conn, snapshot_id, session_id=self.session_id)
        if res.get("ok"):
            self._reload_after_rollback()
        return res

    def rollback_to_session(self, session_id: int, where: str = "start") -> dict:
        """Roll back to the start/end of a session and refresh the UI."""
        res = rollback_to_session_db(self.conn, session_id, where=where, live_session_id=self.session_id)
        if res.get("ok"):
            self._reload_after_rollback()
        return res

    def rebuild_from_log(self, recall_map: Optional[dict] = None) -> dict:
        """Pre-rollback snapshot, then replay the whole log to recompute scores + backfill before/after
        on every duel (unlocks legacy duels for editing), then refresh the UI."""
        _take_snapshot(self.conn, kind="pre-rollback", label="before rebuild-from-log",
                       session_id=self.session_id)
        stats = rebuild_scores_from_log(self.conn, dry_run=False, recall_map=recall_map)
        self._reload_after_rollback()
        return stats

    def _reload_after_rollback(self) -> None:
        """Scores changed underneath the live duel — drop volatile in-memory state and rebuild."""
        try:
            self._stop_video("a")
            self._stop_video("b")
        except Exception:
            pass
        self.history_index = None
        self.duel_history = []
        self.future_queue = []
        self.solo_mode = False
        try:
            self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
        except Exception:
            pass
        try:
            self.load_duel()
        except Exception as ex:
            print(f"[rollback] load_duel failed: {ex}")
        try:
            self.update_sidebar()
        except Exception:
            pass

    def _regen_sidecars_async(self, status_cb=None) -> None:
        """Rebuild all sidecars from the DB on a background thread (own sqlite connection)."""
        def worker():
            try:
                rconn = sqlite3.connect(str(DB_PATH))
                def prog(done, total):
                    if status_cb:
                        self.root.after(0, lambda d=done, t=total: status_cb(f"Regenerating sidecars… {d}/{t}"))
                regenerate_all_sidecars(rconn, progress=prog)
                rconn.close()
                if status_cb:
                    self.root.after(0, lambda: status_cb("Sidecars regenerated from DB."))
            except Exception as ex:
                if status_cb:
                    self.root.after(0, lambda: status_cb(f"Sidecar regen failed: {ex}"))
        threading.Thread(target=worker, daemon=True).start()

    # -------------------- History / Rollback manager window --------------------
    def show_history_manager(self) -> None:
        if self._hm_win is not None:
            try:
                if self._hm_win.winfo_exists():
                    self._hm_win.lift()
                    self._hm_win.focus_force()
                    self._hm_refresh()
                    return
            except Exception:
                pass
            self._hm_win = None

        win = tk.Toplevel(self.root)
        self._hm_win = win
        win.title("History / Rollback")
        win.configure(bg=DARK_BG)
        win.geometry("840x680")

        def _on_close():
            self._hm_win = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", _on_close)

        self._hm_stats = tk.Label(win, text="", justify="left", anchor="w",
                                  font=("Consolas", 10), fg=TEXT_COLOR, bg=DARK_BG)
        self._hm_stats.pack(fill="x", padx=10, pady=(10, 6))

        actions = tk.Frame(win, bg=DARK_BG)
        actions.pack(fill="x", padx=10, pady=(0, 6))
        tk.Label(actions, text="Undo last", fg=TEXT_COLOR, bg=DARK_BG).pack(side="left")
        self._hm_undo_n = tk.IntVar(value=1)
        tk.Spinbox(actions, from_=1, to=9999, width=5, textvariable=self._hm_undo_n,
                   bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=4)
        tk.Label(actions, text="duel(s)", fg=TEXT_COLOR, bg=DARK_BG).pack(side="left")
        tk.Button(actions, text="Undo", command=self._hm_do_undo,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=(8, 16))
        tk.Button(actions, text="Take snapshot", command=self._hm_take_snapshot,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=4)
        tk.Button(actions, text="Backup DB now", command=self._hm_backup,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=4)
        tk.Button(actions, text="Regenerate sidecars", command=self._hm_regen,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=4)
        tk.Button(actions, text="Rebuild from log…", command=self._hm_rebuild,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=4)

        lists = tk.Frame(win, bg=DARK_BG)
        lists.pack(fill="both", expand=True, padx=10, pady=4)

        sframe = tk.Frame(lists, bg=DARK_BG)
        sframe.pack(side="left", fill="both", expand=True, padx=(0, 5))
        tk.Label(sframe, text="Sessions (newest first)", fg=ACCENT, bg=DARK_BG,
                 font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self._hm_sessions = tk.Listbox(sframe, bg=DARK_PANEL, fg=TEXT_COLOR, selectbackground=ACCENT,
                                       font=("Consolas", 9), activestyle="none", height=16)
        self._hm_sessions.pack(fill="both", expand=True)
        self._hm_sessions.bind("<Double-Button-1>", lambda e: self._hm_open_session_detail())
        srow = tk.Frame(sframe, bg=DARK_BG)
        srow.pack(fill="x", pady=3)
        tk.Button(srow, text="Open / edit duels →", command=self._hm_open_session_detail,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=2)
        tk.Button(srow, text="Roll back to START", command=lambda: self._hm_rollback_session("start"),
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=2)
        tk.Button(srow, text="to END", command=lambda: self._hm_rollback_session("end"),
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=2)

        nframe = tk.Frame(lists, bg=DARK_BG)
        nframe.pack(side="left", fill="both", expand=True, padx=(5, 0))
        tk.Label(nframe, text="Snapshots (newest first)", fg=ACCENT, bg=DARK_BG,
                 font=("Segoe UI", 10, "bold")).pack(anchor="w")
        self._hm_snaps = tk.Listbox(nframe, bg=DARK_PANEL, fg=TEXT_COLOR, selectbackground=ACCENT,
                                    font=("Consolas", 9), activestyle="none", height=16)
        self._hm_snaps.pack(fill="both", expand=True)
        tk.Button(nframe, text="Restore selected snapshot", command=self._hm_restore_snapshot,
                  bg=DARK_PANEL, fg=TEXT_COLOR, relief="flat").pack(fill="x", pady=3)

        self._hm_status = tk.Label(win, text="Tip: every rollback first takes a 'pre-rollback' "
                                   "snapshot, so any rollback can itself be undone.",
                                   justify="left", anchor="w", wraplength=800,
                                   font=("Segoe UI", 9), fg=ACCENT, bg=DARK_BG)
        self._hm_status.pack(fill="x", padx=10, pady=(0, 8))

        self._hm_session_ids: List[int] = []
        self._hm_snap_ids: List[int] = []
        self._hm_refresh()

    def _hm_set_status(self, text: str) -> None:
        if getattr(self, "_hm_status", None) is not None:
            try:
                self._hm_status.config(text=text)
            except Exception:
                pass

    def _hm_refresh(self) -> None:
        if self._hm_win is None:
            return
        fmt = lambda t: "n/a" if not t else datetime.fromtimestamp(int(t)).strftime("%Y-%m-%d %H:%M")
        ni = self.conn.execute("SELECT COUNT(*) FROM images").fetchone()[0]
        nc = self.conn.execute("SELECT COUNT(*) FROM comparisons").fetchone()[0]
        na = self.conn.execute("SELECT COUNT(*) FROM comparisons WHERE active=1").fetchone()[0]
        ns = self.conn.execute("SELECT COUNT(*) FROM sessions").fetchone()[0]
        nsnap = self.conn.execute("SELECT COUNT(*) FROM snapshots").fetchone()[0]
        self._hm_stats.config(text=(
            f"Images: {ni}    Comparisons: {nc}  (active {na}, archived {nc - na})\n"
            f"Sessions: {ns}    Snapshots: {nsnap}    Current live session: #{self.session_id}"
        ))

        self._hm_sessions.delete(0, "end")
        self._hm_session_ids = []
        for (sid, st, et, label, _scid, _note) in self.conn.execute(
            "SELECT id, started_ts, ended_ts, label, start_comparison_id, note FROM sessions ORDER BY id DESC"
        ):
            cnt = self.conn.execute("SELECT COUNT(*) FROM comparisons WHERE session_id=?", (sid,)).fetchone()[0]
            live = " (live)" if sid == self.session_id else ""
            self._hm_sessions.insert("end", f"#{sid:<4} {fmt(st)} – {fmt(et)}  {cnt:>4} duels  [{label}]{live}")
            self._hm_session_ids.append(sid)

        self._hm_snaps.delete(0, "end")
        self._hm_snap_ids = []
        for (sid, ts, label, kind, _ssid, mcid) in self.conn.execute(
            "SELECT id, ts, label, kind, session_id, max_comparison_id FROM snapshots ORDER BY id DESC LIMIT 300"
        ):
            self._hm_snaps.insert("end", f"#{sid:<4} {fmt(ts)}  {kind:<12} cid≤{mcid:<6} {label or ''}")
            self._hm_snap_ids.append(sid)

    def _hm_selected(self, listbox, ids):
        sel = listbox.curselection()
        if not sel:
            return None
        return ids[sel[0]]

    def _hm_do_undo(self) -> None:
        try:
            n = max(1, int(self._hm_undo_n.get() or 1))
        except Exception:
            n = 1
        avail = self.conn.execute(
            "SELECT COUNT(*) FROM comparisons WHERE active=1 AND left_score_before IS NOT NULL"
        ).fetchone()[0]
        if avail == 0:
            self._hm_set_status("Nothing to undo (no fully-logged active comparisons).")
            return
        n = min(n, avail)
        if not messagebox.askyesno(
            "Undo", f"Reverse the last {n} duel(s)?\nA pre-rollback snapshot is taken first (undoable).",
            parent=self._hm_win,
        ):
            return
        res = self.undo_last(n)
        self._hm_refresh()
        self._hm_set_status(f"Undid {res['undone']} duel(s). Pre-rollback snapshot #{res.get('pre_snapshot_id')}.")

    def _hm_take_snapshot(self) -> None:
        sid = _take_snapshot(self.conn, kind="manual", label="manual snapshot", session_id=self.session_id)
        self._hm_refresh()
        self._hm_set_status(f"Snapshot #{sid} taken.")

    def _hm_backup(self) -> None:
        self._hm_set_status("Backing up…")
        if self._hm_win:
            self._hm_win.update_idletasks()
        dest = backup_db()
        self._hm_set_status(f"Backup written: {dest}" if dest else "Backup failed (see console).")

    def _hm_regen(self) -> None:
        self._regen_sidecars_async(status_cb=self._hm_set_status)
        self._hm_set_status("Regenerating sidecars in background…")

    def _hm_rebuild(self) -> None:
        dry = rebuild_scores_from_log(self.conn, dry_run=True)
        amb = self.conn.execute(
            "SELECT COUNT(*) FROM comparisons WHERE active=1 AND left_score_before IS NULL AND chosen_id IS NULL"
        ).fetchone()[0]
        legacy = self.conn.execute(
            "SELECT COUNT(*) FROM comparisons WHERE active=1 AND left_score_before IS NULL"
        ).fetchone()[0]
        msg = (
            f"Replay all {dry['duels']} active duels in time order to recompute scores?\n\n"
            f"• {dry['moved']} of {dry['images']} images would move >1 pt "
            f"(max {dry['max_drift']:.1f}, mean {dry['mean_drift']:.2f} pts).\n"
            f"• {legacy} legacy duels become individually editable afterward (re-vote to 'recall' them).\n"
            f"• {amb} unknown tie/downvote duels replay as TIES — their original downvote\n"
            f"  penalties can't be recovered; recall the ones you remember by re-voting.\n"
            f"• Original dates/times are kept.\n\n"
            f"A pre-rollback snapshot is taken first, so this is fully reversible."
        )
        if not messagebox.askyesno("Rebuild scores from log", msg, parent=self._hm_win):
            return
        self._hm_set_status("Rebuilding… (a pre-rollback snapshot is being taken)")
        if self._hm_win:
            self._hm_win.update_idletasks()
        stats = self.rebuild_from_log()
        self._hm_refresh()
        self._hm_set_status(
            f"Rebuilt from {stats['duels']} duels. {stats['moved']} images moved >1pt "
            f"(max {stats['max_drift']:.1f}). All duels are now editable — re-vote any to recall it. "
            f"Reverse via the latest 'pre-rollback' snapshot."
        )

    def _hm_rollback_session(self, where: str) -> None:
        sid = self._hm_selected(self._hm_sessions, self._hm_session_ids)
        if sid is None:
            self._hm_set_status("Select a session first.")
            return
        if not messagebox.askyesno(
            "Roll back",
            f"Roll back to the {where.upper()} of session #{sid}?\n"
            f"A pre-rollback snapshot is taken first (undoable).",
            parent=self._hm_win,
        ):
            return
        res = self.rollback_to_session(sid, where=where)
        self._hm_refresh()
        if res.get("ok"):
            self._hm_set_status(
                f"Rolled back to {where} of session #{sid} (restored snapshot #{res.get('snapshot_id')}). "
                f"Pre-rollback snapshot #{res.get('pre_snapshot_id')}."
            )
        else:
            self._hm_set_status(f"Rollback failed: {res.get('error')}")

    def _hm_restore_snapshot(self) -> None:
        sid = self._hm_selected(self._hm_snaps, self._hm_snap_ids)
        if sid is None:
            self._hm_set_status("Select a snapshot first.")
            return
        if not messagebox.askyesno(
            "Restore snapshot",
            f"Restore snapshot #{sid}?\nA pre-rollback snapshot is taken first (undoable).",
            parent=self._hm_win,
        ):
            return
        res = self.restore_snapshot(sid)
        self._hm_refresh()
        if res.get("ok"):
            self._hm_set_status(
                f"Restored snapshot #{sid} ({res.get('restored_rows')} images). "
                f"Pre-rollback snapshot #{res.get('pre_snapshot_id')}."
            )
        else:
            self._hm_set_status(f"Restore failed: {res.get('error')}")

    # -------------------- Session drill-in (edit/undo individual duels + tags) --------------------
    def _hm_open_session_detail(self) -> None:
        sid = self._hm_selected(self._hm_sessions, self._hm_session_ids)
        if sid is None:
            self._hm_set_status("Select a session first, then 'Open / edit duels'.")
            return
        self.show_session_detail(sid)

    def _open_path(self, path: str) -> None:
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception as ex:
            self._sd_set_status(f"Open failed: {ex}")

    def show_session_detail(self, session_id: int) -> None:
        """Open a drill-in window listing every duel in a session, with per-duel re-vote / undo /
        restore and per-image tag editing. Thumbnails for every row (built async, bounded pool)."""
        # Close any prior drill-in window (singleton).
        if self._sd_win is not None:
            try:
                self._sd_cancel.set()
            except Exception:
                pass
            try:
                if self._sd_win.winfo_exists():
                    self._sd_win.destroy()
            except Exception:
                pass
            self._sd_win = None

        self._sd_session_id = session_id
        self._sd_selected_cid = None
        self._sd_pre_edit_done = False
        self._sd_cancel = threading.Event()
        self._sd_rows: List[dict] = []
        self._sd_thumb_refs: List = []

        win = tk.Toplevel(self.root)
        self._sd_win = win
        win.title(f"Session #{session_id} — duels")
        win.configure(bg=DARK_BG)
        win.geometry("1100x740")

        def _on_close():
            try:
                self._sd_cancel.set()
            except Exception:
                pass
            self._sd_win = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", _on_close)

        self._sd_header = tk.Label(win, justify="left", anchor="w", font=("Consolas", 10),
                                   fg=TEXT_COLOR, bg=DARK_BG)
        self._sd_header.pack(fill="x", padx=10, pady=(8, 4))

        body = tk.Frame(win, bg=DARK_BG)
        body.pack(fill="both", expand=True, padx=10, pady=4)

        # Left: scrollable list of duel rows
        left = tk.Frame(body, bg=DARK_BG)
        left.pack(side="left", fill="both", expand=True)
        canvas = tk.Canvas(left, bg=DARK_BG, highlightthickness=0)
        vsb = tk.Scrollbar(left, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        inner = tk.Frame(canvas, bg=DARK_BG)
        canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        self._sd_canvas = canvas
        self._sd_inner = inner
        _wheel = lambda e: canvas.yview_scroll(int(-(e.delta) / 120), "units")
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _wheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

        # Right: per-duel editor panel
        editor = tk.Frame(body, bg=DARK_PANEL, width=390)
        editor.pack(side="right", fill="y", padx=(8, 0))
        editor.pack_propagate(False)
        self._sd_editor = editor

        self._sd_status = tk.Label(win, justify="left", anchor="w", wraplength=1060,
                                   font=("Segoe UI", 9), fg=ACCENT, bg=DARK_BG)
        self._sd_status.pack(fill="x", padx=10, pady=(0, 8))

        self._sd_build_rows()
        self._sd_render_editor(None)
        self._sd_start_thumb_workers()

    def _sd_set_status(self, text: str) -> None:
        if getattr(self, "_sd_status", None) is not None:
            try:
                self._sd_status.config(text=text)
            except Exception:
                pass

    def _sd_is_hidden(self, img_id: int) -> bool:
        r = self.conn.execute("SELECT hidden FROM images WHERE id=?", (img_id,)).fetchone()
        return bool(r and r[0])

    def _sd_build_rows(self) -> None:
        sid = self._sd_session_id
        rows = self.conn.execute(
            "SELECT c.id, c.left_id, c.right_id, c.outcome, c.left_score_before, c.right_score_before, "
            "c.left_score_after, c.right_score_after, c.active, c.ts, li.path, ri.path, li.tags, ri.tags "
            "FROM comparisons c "
            "LEFT JOIN images li ON li.id = c.left_id "
            "LEFT JOIN images ri ON ri.id = c.right_id "
            "WHERE c.session_id=? ORDER BY c.id ASC",
            (sid,),
        ).fetchall()
        total = len(rows)
        editable = sum(1 for r in rows if r[4] is not None and r[6] is not None)
        self._sd_header.config(text=(
            f"Session #{sid}: {total} duels  ({editable} editable, {total - editable} legacy/view-only).  "
            f"Click a duel to edit it.\n"
            f"Legend:  ◀L = left won   R▶ = right won   = tie   ⬇ downvote   [undone] = archived"
        ))
        for r in rows:
            (cid, lid, rid, outcome, lb, rb, la, ra, active, ts, lpath, rpath, ltags, rtags) = r
            legacy = (lb is None or rb is None or la is None or ra is None)
            d = {"cid": cid, "lid": lid, "rid": rid, "outcome": outcome,
                 "lb": lb, "rb": rb, "la": la, "ra": ra, "active": active, "ts": ts,
                 "lpath": lpath or "", "rpath": rpath or "",
                 "ltags": ltags or "[]", "rtags": rtags or "[]", "legacy": legacy, "thumb": None}
            frame = tk.Frame(self._sd_inner, bg=DARK_PANEL)
            frame.pack(fill="x", pady=1)
            thumb_lbl = tk.Label(frame, bg="#111111")
            thumb_lbl.pack(side="left", padx=2, pady=2)
            text_lbl = tk.Label(frame, justify="left", anchor="w", font=("Consolas", 9),
                                fg=TEXT_COLOR, bg=DARK_PANEL)
            text_lbl.pack(side="left", fill="x", expand=True, padx=4)
            d["frame"] = frame
            d["thumb_lbl"] = thumb_lbl
            d["text_lbl"] = text_lbl
            for w in (frame, thumb_lbl, text_lbl):
                w.bind("<Button-1>", lambda e, c=cid: self._sd_select(c))
            self._sd_rows.append(d)
            self._sd_update_row_text(d)

    def _sd_update_row_text(self, d: dict) -> None:
        def nm(p):
            n = Path(p).name if p else "(missing)"
            return (n[:22] + "…") if len(n) > 23 else n
        mark = {"left": "◀L ", "right": " R▶", "tie": " =  ", "downvote": " ⬇  "}.get(d["outcome"], " ?  ")
        t = time.strftime("%H:%M", time.localtime(d["ts"])) if d["ts"] else "--:--"
        la = f"{d['la']:.0f}" if d["la"] is not None else "·"
        ra = f"{d['ra']:.0f}" if d["ra"] is not None else "·"
        pre = "" if d["active"] else "[undone] "
        suf = "   (legacy: view only)" if d["legacy"] else ""
        d["text_lbl"].config(
            text=f"{pre}#{d['cid']}  {t}  {mark}  L:{nm(d['lpath'])}({la})  R:{nm(d['rpath'])}({ra}){suf}",
            fg=("#8a8a8a" if (d["legacy"] or not d["active"]) else TEXT_COLOR),
        )
        sel = (d["cid"] == self._sd_selected_cid)
        bg = ACCENT if sel else DARK_PANEL
        try:
            d["frame"].config(bg=bg)
            d["text_lbl"].config(bg=bg)
        except Exception:
            pass

    def _sd_select(self, cid: int) -> None:
        self._sd_selected_cid = cid
        for d in self._sd_rows:
            self._sd_update_row_text(d)
        d = next((x for x in self._sd_rows if x["cid"] == cid), None)
        self._sd_render_editor(d)

    def _sd_render_editor(self, d: Optional[dict]) -> None:
        E = self._sd_editor
        for w in E.winfo_children():
            w.destroy()
        if d is None:
            tk.Label(E, text="Select a duel on the left to re-vote, undo, or edit its tags.",
                     fg=TEXT_COLOR, bg=DARK_PANEL, wraplength=360, justify="left").pack(anchor="w", padx=10, pady=10)
            return
        tk.Label(E, text=f"Duel #{d['cid']}", font=("Segoe UI", 11, "bold"),
                 fg=ACCENT, bg=DARK_PANEL).pack(anchor="w", padx=10, pady=(10, 2))
        if d["legacy"]:
            tk.Label(E, text="Legacy duel (pre-history-feature): no stored before/after scores, so it "
                     "can't be re-voted or undone individually. Use snapshot rollback for coarse changes.",
                     fg="#d0a000", bg=DARK_PANEL, wraplength=360, justify="left").pack(anchor="w", padx=10, pady=4)
        else:
            tk.Label(E, text="Re-vote:", fg=TEXT_COLOR, bg=DARK_PANEL).pack(anchor="w", padx=10, pady=(6, 0))
            orow = tk.Frame(E, bg=DARK_PANEL)
            orow.pack(fill="x", padx=10, pady=2)
            for label, oc in (("◀ Left", "left"), ("Right ▶", "right")):
                cur = (d["outcome"] == oc)
                b = tk.Button(orow, text=label + (" ✓" if cur else ""),
                              command=lambda o=oc: self._sd_revote(o),
                              bg=(ACCENT if cur else DARK_BG), fg=TEXT_COLOR, relief="flat")
                b.pack(side="left", padx=2)
                if not d["active"]:
                    b.config(state="disabled")
            urow = tk.Frame(E, bg=DARK_PANEL)
            urow.pack(fill="x", padx=10, pady=(4, 2))
            if d["active"]:
                tk.Button(urow, text="Undo this duel", command=lambda c=d["cid"]: self._sd_undo(c),
                          bg=DARK_BG, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=2)
            else:
                tk.Label(urow, text="(undone)", fg="#d08000", bg=DARK_PANEL).pack(side="left", padx=2)
                tk.Button(urow, text="Restore this duel", command=lambda c=d["cid"]: self._sd_restore(c),
                          bg=DARK_BG, fg=TEXT_COLOR, relief="flat").pack(side="left", padx=2)
        tk.Frame(E, height=1, bg=SEPARATOR_BG).pack(fill="x", padx=10, pady=8)
        tk.Label(E, text="Tags (apply to the image's current state, globally):",
                 fg="#aaaaaa", bg=DARK_PANEL, wraplength=360, justify="left").pack(anchor="w", padx=10)
        self._sd_tag_vars = {"left": {}, "right": {}}
        self._sd_hidden_vars = {}
        self._sd_build_tag_editor(E, "left", d["lid"], d["lpath"], d["ltags"])
        self._sd_build_tag_editor(E, "right", d["rid"], d["rpath"], d["rtags"])

    def _sd_build_tag_editor(self, parent, side: str, img_id: int, path: str, tags_raw: str) -> None:
        cur_tags = set(self._parse_tags(tags_raw))
        title = ("Left" if side == "left" else "Right") + " — " + (Path(path).name[:28] if path else "(missing)")
        box = tk.LabelFrame(parent, text=title, fg=TEXT_COLOR, bg=DARK_PANEL, labelanchor="nw")
        box.pack(fill="x", padx=10, pady=4)
        grid = tk.Frame(box, bg=DARK_PANEL)
        grid.pack(fill="x", padx=4, pady=2)
        self._sd_tag_vars[side] = {}
        for i, tag in enumerate(TAG_OPTIONS):
            v = tk.BooleanVar(value=(tag in cur_tags))
            self._sd_tag_vars[side][tag] = v
            tk.Checkbutton(grid, text=tag, variable=v, fg=TEXT_COLOR, bg=DARK_PANEL,
                           selectcolor=DARK_BG, activebackground=DARK_PANEL,
                           activeforeground=TEXT_COLOR).grid(row=i // 3, column=i % 3, sticky="w", padx=2)
        hv = tk.BooleanVar(value=self._sd_is_hidden(img_id))
        self._sd_hidden_vars[side] = hv
        brow = tk.Frame(box, bg=DARK_PANEL)
        brow.pack(fill="x", padx=4, pady=2)
        tk.Checkbutton(brow, text="Hidden", variable=hv, fg=TEXT_COLOR, bg=DARK_PANEL, selectcolor=DARK_BG,
                       activebackground=DARK_PANEL, activeforeground=TEXT_COLOR).pack(side="left")
        tk.Button(brow, text="Save tags", command=lambda s=side, iid=img_id: self._sd_save_tags(s, iid),
                  bg=DARK_BG, fg=TEXT_COLOR, relief="flat").pack(side="right", padx=2)
        if path:
            tk.Button(brow, text="Open", command=lambda p=path: self._open_path(p),
                      bg=DARK_BG, fg=TEXT_COLOR, relief="flat").pack(side="right", padx=2)

    def _sd_ensure_pre_edit_snapshot(self) -> None:
        if getattr(self, "_sd_pre_edit_done", False):
            return
        try:
            _take_snapshot(self.conn, kind="pre-rollback",
                           label=f"before editing session #{self._sd_session_id}", session_id=self.session_id)
            self._sd_pre_edit_done = True
        except Exception as ex:
            print(f"[session-edit] pre-edit snapshot failed: {ex}")

    def _sd_revote(self, new_outcome: str) -> None:
        cid = self._sd_selected_cid
        if cid is None:
            return
        self._sd_ensure_pre_edit_snapshot()
        res = revote_comparison_db(self.conn, cid, new_outcome)
        if not res.get("ok"):
            self._sd_set_status(f"Cannot re-vote: {res.get('error')}")
            return
        d = next((x for x in self._sd_rows if x["cid"] == cid), None)
        if d:
            rr = self.conn.execute(
                "SELECT outcome, left_score_after, right_score_after, active FROM comparisons WHERE id=?",
                (cid,)).fetchone()
            d["outcome"], d["la"], d["ra"], d["active"] = rr
            self._sd_update_row_text(d)
            self._sd_render_editor(d)
        self._sd_set_status(f"Re-voted duel #{cid} → {new_outcome}."
                            + ("" if res.get("changed") else " (no change)"))
        self._after_comparison_edit()

    def _sd_undo(self, cid: int) -> None:
        self._sd_ensure_pre_edit_snapshot()
        res = undo_comparison_db(self.conn, cid)
        if not res.get("ok"):
            self._sd_set_status(f"Cannot undo: {res.get('error')}")
            return
        d = next((x for x in self._sd_rows if x["cid"] == cid), None)
        if d:
            d["active"] = 0
            self._sd_update_row_text(d)
            self._sd_render_editor(d)
        self._sd_set_status(f"Undid duel #{cid} (archived; click Restore to re-apply).")
        self._after_comparison_edit()

    def _sd_restore(self, cid: int) -> None:
        self._sd_ensure_pre_edit_snapshot()
        res = restore_comparison_db(self.conn, cid)
        if not res.get("ok"):
            self._sd_set_status(f"Cannot restore: {res.get('error')}")
            return
        d = next((x for x in self._sd_rows if x["cid"] == cid), None)
        if d:
            d["active"] = 1
            self._sd_update_row_text(d)
            self._sd_render_editor(d)
        self._sd_set_status(f"Restored duel #{cid}.")
        self._after_comparison_edit()

    def _sd_save_tags(self, side: str, img_id: int) -> None:
        tags = {t for t, v in self._sd_tag_vars[side].items() if v.get()}
        hidden = 1 if self._sd_hidden_vars[side].get() else 0
        self._write_tags(img_id, tags, hidden=hidden)
        # Re-read canonical stored tags and refresh any row dicts referencing this image.
        row = self.conn.execute("SELECT tags FROM images WHERE id=?", (img_id,)).fetchone()
        raw = row[0] if row else json.dumps(sorted(tags))
        for d in self._sd_rows:
            changed = False
            if d["lid"] == img_id:
                d["ltags"] = raw; changed = True
            if d["rid"] == img_id:
                d["rtags"] = raw; changed = True
            if changed:
                self._sd_update_row_text(d)
        self._sd_set_status(f"Saved tags for image #{img_id}: {', '.join(self._ordered_tags(tags)) or '(none)'}"
                            + ("  [Hidden]" if hidden else ""))
        # If this image is on screen in the live duel, keep its tag controls in sync.
        try:
            for s in ("a", "b"):
                r = self._side[s].get("row")
                if r and r[0] == img_id:
                    fresh = self._fetch_row(img_id)
                    if fresh:
                        self._side[s]["row"] = fresh
                    self._sync_tag_controls(s)
        except Exception:
            pass

    def _after_comparison_edit(self) -> None:
        self._refresh_live_scores_after_edit()
        if self._hm_win is not None:
            try:
                self._hm_refresh()
            except Exception:
                pass

    def _refresh_live_scores_after_edit(self) -> None:
        """A historical edit may have changed an image that's on screen or in the leaderboard."""
        try:
            if self.current and self.history_index is None and not self.solo_mode:
                a, b = self.current
                na, nb = self._fetch_row(a[0]), self._fetch_row(b[0])
                if na and nb:
                    self.current = (na, nb)
                    self.live_current = (na, nb)
                    self._update_info_bars(na, nb)
        except Exception:
            pass
        try:
            self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
            self.update_sidebar()
        except Exception:
            pass

    def _sd_start_thumb_workers(self, n: int = 4) -> None:
        self._sd_thumb_idx = 0
        self._sd_thumb_lock = threading.Lock()
        w2 = self.carousel_thumb_size[0] * 2 + 2
        h = self.carousel_thumb_size[1]
        try:
            self._sd_placeholder = ImageTk.PhotoImage(Image.new("RGB", (w2, h), "#111111"))
            for d in self._sd_rows:
                d["thumb_lbl"].config(image=self._sd_placeholder)
        except Exception:
            pass

        def worker():
            while not self._sd_cancel.is_set():
                with self._sd_thumb_lock:
                    i = self._sd_thumb_idx
                    if i >= len(self._sd_rows):
                        return
                    self._sd_thumb_idx += 1
                d = self._sd_rows[i]
                try:
                    sensitive = bool((set(self._parse_tags(d["ltags"])) | set(self._parse_tags(d["rtags"]))) & BLUR_TAGS)
                    thumb = self._build_duel_thumbnail(d["lpath"], d["rpath"], sensitive=sensitive)
                except Exception:
                    thumb = None
                if thumb is not None and not self._sd_cancel.is_set():
                    self._sd_thumb_refs.append(thumb)
                    d["thumb"] = thumb
                    self.root.after(0, lambda dd=d, th=thumb: self._sd_apply_thumb(dd, th))

        for _ in range(max(1, n)):
            threading.Thread(target=worker, daemon=True).start()

    def _sd_apply_thumb(self, d: dict, thumb) -> None:
        if self._sd_win is None:
            return
        try:
            if d["thumb_lbl"].winfo_exists():
                d["thumb_lbl"].config(image=thumb)
        except Exception:
            pass

    # -------------------- DB stats --------------------
    def show_db_stats(self):
        n_images = self.conn.execute("SELECT COUNT(*) FROM images").fetchone()[0]
        n_hidden = self.conn.execute("SELECT COUNT(*) FROM images WHERE hidden=1").fetchone()[0]
        n_comp = self.conn.execute("SELECT COUNT(*) FROM comparisons").fetchone()[0]
        mn_mx = self.conn.execute("SELECT MIN(ts), MAX(ts) FROM comparisons").fetchone()
        tmin, tmax = mn_mx[0], mn_mx[1]
        fmt = lambda t: "n/a" if t is None else datetime.fromtimestamp(int(t)).strftime("%Y-%m-%d %H:%M:%S")

        sums = self.conn.execute("SELECT COALESCE(SUM(duels),0), COALESCE(SUM(wins),0), COALESCE(SUM(losses),0) FROM images").fetchone()
        sum_duels, sum_wins, sum_losses = int(sums[0]), int(sums[1]), int(sums[2])

        n_active = self.conn.execute("SELECT COUNT(*) FROM comparisons WHERE active=1").fetchone()[0]
        n_sessions = self.conn.execute("SELECT COUNT(*) FROM sessions").fetchone()[0]
        n_snaps = self.conn.execute("SELECT COUNT(*) FROM snapshots").fetchone()[0]

        msg = "\n".join([
            f"Images: {n_images} (hidden: {n_hidden})",
            f"Comparisons: {n_comp}  (active {n_active}, archived {n_comp - n_active})",
            f"First duel: {fmt(tmin)}",
            f"Last duel:  {fmt(tmax)}",
            "",
            f"SUM(images.duels)   = {sum_duels}",
            f"SUM(images.wins)    = {sum_wins}",
            f"SUM(images.losses)  = {sum_losses}",
            f"Comparisons * 2     = {n_comp * 2}",
            "",
            f"Sessions: {n_sessions}    Snapshots: {n_snaps}    Live session: #{self.session_id}",
            "",
            "A reset usually shows as: comparisons near 0 and first/last duel very recent.",
            "Press 'h' (or the History/Rollback button) to undo duels or roll back a session.",
        ])
        messagebox.showinfo("DB stats", msg)

    # -------------------- refresh visuals only --------------------
    def _refresh_visuals_only(self, force: bool = False):
        # Refresh media when panel size changes (or force=True).
        for side in ("a", "b"):
            st = self._side[side]
            row = st.get("row")
            if not row:
                continue
            kind = self._media_kind(row[1])
            current_size = self._get_side_display_size(side, kind)
            if current_size[0] <= 5 or current_size[1] <= 5:
                continue
            if (not force) and st.get("last_visual_size") == current_size:
                continue

            if kind == "video":
                vframe = self.left_video if side == "a" else self.right_video
                self._update_video_blur_overlay(side, vframe, row[1])
                st["last_visual_size"] = current_size
                continue

            panel = self.left_panel if side == "a" else self.right_panel
            self._cancel_animation(side)
            self._render_image_or_gif(side, panel, row[1])
        self._update_carousel()

    # -------------------- quit --------------------
    def quit(self):
        try:
            self._stop_video("a")
            self._stop_video("b")
        except Exception:
            pass
        # Close the live session (stamp ended_ts) BEFORE closing the connection.
        self._close_session()
        try:
            self.conn.close()
        except Exception:
            pass
        self.root.quit()

# -------------------- Report on quit --------------------
def export_csv(conn: sqlite3.Connection, path: Path) -> None:
    import csv
    rows = conn.execute("""
        SELECT path, folder, score, wins, losses, duels, last_seen, hidden
        FROM images ORDER BY score DESC
    """).fetchall()
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["path", "folder", "score", "wins", "losses", "duels", "last_seen_iso", "hidden"])
        for p, folder, score, wins, losses, duels, last_seen, hidden in rows:
            iso = datetime.fromtimestamp(last_seen, tz=timezone.utc).isoformat() if last_seen else ""
            w.writerow([p, folder, f"{score:.2f}", wins, losses, duels, iso, hidden])

def show_folder_chart(conn: sqlite3.Connection) -> None:
    if not plt:
        return
    rows = folder_leaderboard(conn, metric=LEADERBOARD_METRIC_DEFAULT)[:20]
    if not rows:
        return
    names = [Path(r["folder"]).name or r["folder"] for r in rows]
    scores = [r["score"] for r in rows]
    plt.figure(figsize=(10, 6))
    plt.barh(list(reversed(names)), list(reversed(scores)))
    plt.xlabel("Folder ranking score")
    plt.title(f"Top folders (metric: {rows[0]['metric']})")
    plt.tight_layout()
    plt.show()

# -------------------- Run --------------------
def run():
    conn = init_db()
    scan_images(conn)
    refresh_dislikes_index()
    root = tk.Tk()
    app = App(root, conn)
    root.mainloop()

    # optional report — use a fresh connection: App.quit() closes `conn` on exit.
    rconn = None
    try:
        rconn = sqlite3.connect(str(DB_PATH))
        csv_path = Path(ROOT_DIR) / "image_duel_report.csv"
        export_csv(rconn, csv_path)
        print(f"[report] CSV written: {csv_path}")
    except Exception:
        pass
    try:
        if rconn is not None:
            show_folder_chart(rconn)
    except Exception:
        pass
    finally:
        try:
            if rconn is not None:
                rconn.close()
        except Exception:
            pass

if __name__ == "__main__":
    # CLI utilities (no GUI):
    #   python image_duel_ranker.py --backup          -> VACUUM INTO backups/, rotate to last N
    #   python image_duel_ranker.py --regen-sidecars  -> rebuild every sidecar JSON from the DB
    if "--backup" in sys.argv:
        backup_db()
    elif "--regen-sidecars" in sys.argv:
        _c = init_db()
        try:
            regenerate_all_sidecars(_c, progress=lambda d, t: print(f"[sidecars] {d}/{t}"))
        finally:
            _c.close()
    else:
        run()
