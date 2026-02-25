# image_duel_ranker.py
# Image Duel Ranker — Elo-style dueling with artist leaderboard, e621 link export, and in-app VLC video playback.
# Version: 2026-02-25f
# Update: Unified pool dropdown styling, added carousel close gestures, tag-aware pairing, and dislikes-adjusted metric default.
# Build: 2026-02-25f (ui+pairing+metric)

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
from datetime import datetime
from collections import deque
from typing import Optional, Tuple, List
from urllib.parse import quote_plus
import webbrowser

import subprocess
import shutil
import tempfile
import threading
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
ACCENT      = "#569cd6"
LINK_COLOR  = "#4ea1ff"

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
DISLIKES_PER_FILE_PENALTY = 6.0

E621_MAX_TAGS = 40
DEFAULT_COMMON_TAGS = "order:created_asc date:28_months_ago -voted:everything"

TAG_OPTIONS = ["SFW", "MEME", "HIDE", "CW"]
POOL_FILTER_OPTIONS = ["All", "Images", "GIFs", "Videos", "Videos (audio)", "Animated", "Hidden"]

BUILD_STAMP = '2026-02-25f (ui+pairing+metric)'

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
            ts INTEGER
        )
    """)
    conn.commit()
    migrate_schema(conn)
    return conn

def migrate_schema(conn: sqlite3.Connection) -> None:
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
            SELECT folder, AVG(score) AS avg_s, COUNT(*) AS n
            FROM images
            WHERE hidden=0
            GROUP BY folder
            HAVING COUNT(*) >= ?
        """, (min_n,)).fetchall()
        for (folder, avg_s, n) in data:
            avg_s = float(avg_s); n = int(n)
            score = ((avg_s * n + global_mu * FOLDER_PRIOR_IMAGES) / (n + FOLDER_PRIOR_IMAGES)
                     if metric in ("shrunken_avg", "dislikes_adjusted") else avg_s)
            rel_key = _relative_folder_to_root(folder, ROOT_DIR)
            dislikes_n = int(_DISLIKE_COUNTS_BY_REL_FOLDER.get(rel_key, 0))
            if metric == "dislikes_adjusted":
                score -= dislikes_n * DISLIKES_PER_FILE_PENALTY
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score, "dislikes_n": dislikes_n})
    elif metric == "lcb":
        data = conn.execute("""
            SELECT folder, COUNT(*) AS n, AVG(score) AS avg_s, AVG(score*score) AS avg_sq
            FROM images
            WHERE hidden=0
            GROUP BY folder
            HAVING COUNT(*) >= ?
        """, (min_n,)).fetchall()
        for (folder, n, avg_s, avg_sq) in data:
            n = int(n); avg_s = float(avg_s); avg_sq = float(avg_sq)
            var = max(0.0, avg_sq - avg_s * avg_s)
            se = (var ** 0.5) / (n ** 0.5) if n > 0 else 0.0
            score = avg_s - LCB_Z * se
            rel_key = _relative_folder_to_root(folder, ROOT_DIR)
            dislikes_n = int(_DISLIKE_COUNTS_BY_REL_FOLDER.get(rel_key, 0))
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score, "dislikes_n": dislikes_n})
    else:
        return folder_leaderboard(conn, metric="avg", min_n=min_n)

    rows.sort(key=lambda r: r["score"], reverse=True)
    out: List[dict] = []
    for i, r in enumerate(rows, start=1):
        out.append({
            "folder": r["folder"], "avg": r["avg"], "n": r["n"],
            "rank": i, "score": r["score"], "metric": metric,
            "dislikes_n": int(r.get("dislikes_n", 0))
        })
    return out

def find_folder_rank(leader: List[dict], folder_path_str: str) -> Tuple[Optional[int], Optional[float], Optional[int], Optional[float]]:
    for item in leader:
        if item["folder"] == folder_path_str:
            return item["rank"], item["avg"], item["n"], item["score"]
    return None, None, None, None

# -------------------- Sidecar metadata --------------------
def update_image_metadata(path: Path, score: float) -> None:
    try:
        side = SIDECAR_DIR / (path.name + ".json")
        side.write_text(json.dumps({
            "path": str(path),
            "rating_score": float(score),
            "updated_utc": datetime.utcnow().isoformat() + "Z",
            "note": "Generated by Image Duel Ranker (Elo)."
        }, indent=2), encoding="utf-8")
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

def record_result(conn: sqlite3.Connection, a: tuple, b: tuple, winner: Optional[str]) -> dict:
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
        "INSERT INTO comparisons(left_id, right_id, chosen_id, ts) VALUES (?,?,?,?)",
        (a_id, b_id, chosen_id, ts),
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
        "winner": winner,
        "comparison_id": comparison_id,
        "before_a": before_a,
        "before_b": before_b,
    }

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
        self._resize_job = None
        self._audio_cache = {}
        self.duel_history: List[dict] = []
        self.history_index: Optional[int] = None
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
            w.bind("<Shift-Button-1>", lambda e: self._on_shift_downvote("a", e))
            w.bind("<Control-Button-1>", lambda e: self._on_ctrl_options("a", e))
            w.bind("<Button-3>", lambda e: self.skip_side("a"))
            w.bind("<Button-2>", lambda e: self.hide_side("a"))
            w.bind("<Double-Button-1>", self.open_left)

        for w in (self.right_info_bar, self.right_info_text):
            w.bind("<Button-1>", lambda e: self.choose("b"))
            w.bind("<Shift-Button-1>", lambda e: self._on_shift_downvote("b", e))
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
                f"Shrunken Avg - dislikes×{DISLIKES_PER_FILE_PENALTY:g}: applies mirrored dislikes penalty per file."
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
        self.nav_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.btn_prev = tk.Button(self.nav_row, text="Prev [ / PgUp", width=14,
                                  command=lambda: self.change_page(-1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.btn_next = tk.Button(self.nav_row, text="Next ] / PgDn", width=14,
                                  command=lambda: self.change_page(+1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
        self.btn_prev.pack(side="left", padx=(0, 6))
        self.btn_next.pack(side="right")

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
        self.nav_row.pack(fill="x", pady=(0, 6))
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
        self.db_stats_btn.pack(fill="x", pady=(0, 6))
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
        self.carousel_toggle_label.bind("<Button-1>", self._on_carousel_toggle_click)
        self.carousel_info = tk.Label(
            self.carousel_toggle_bar,
            text="History: 0",
            font=("Segoe UI", 9),
            fg=TEXT_COLOR,
            bg=DARK_BG,
        )
        self.carousel_info.pack(side="right")
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
        self.left_panel.bind("<Shift-Button-1>", lambda e: self._on_shift_downvote("a", e))
        self.right_panel.bind("<Shift-Button-1>", lambda e: self._on_shift_downvote("b", e))
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
            w.bind("<Shift-Button-1>", lambda e, s=side: self._on_shift_downvote(s, e))
            w.bind("<Double-Button-1>", self.open_left if side == "a" else self.open_right)
            w.bind("<Button-1>", lambda e, s=side: self.choose("a" if s == "a" else "b"))
            w.bind("<Button-3>", lambda e, s=side: self.skip_side(s))
            w.bind("<Button-2>", lambda e, s=side: self.hide_side(s))

        # ---- Keybinds ----
        root.bind("1", lambda e: self.choose("a"))
        root.bind("2", lambda e: self.choose("b"))
        root.bind("3", lambda e: self.focus_side("a"))
        root.bind("4", lambda e: self.downvote_side("a"))
        root.bind("5", lambda e: self.downvote_side("b"))
        root.bind("6", lambda e: self.focus_side("b"))
        root.bind("7", lambda e: self.skip_side("a"))
        root.bind("8", lambda e: self.skip_side("b"))
        root.bind("9", lambda e: self.toggle_sidebar())
        root.bind("0", lambda e: self.choose(None))
        root.bind(".", lambda e: self.toggle_blur())

        root.bind("q", lambda e: self.quit())

        root.bind("<Configure>", self._on_configure)

        # Start periodic UI tick (scrub/time updates)
        self._tick_job = None
        self._tick()

        self._toggle_carousel()
        self.load_duel()

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

    def _on_carousel_toggle_click(self, _event=None) -> None:
        self._toggle_carousel()

    def _on_carousel_drag_start(self, event) -> None:
        if not self.carousel_visible:
            self._show_carousel(self.carousel_default_height)
        self._carousel_drag_start = event.y_root
        self._carousel_drag_start_height = self.carousel_height
        self._carousel_dragging = False

    def _on_carousel_drag(self, event) -> None:
        if self._carousel_drag_start is None:
            return
        if not self.carousel_visible:
            self._show_carousel(self.carousel_default_height)
        delta = event.y_root - self._carousel_drag_start
        base = self._carousel_drag_start_height or self.carousel_height
        new_height = int(base - delta)
        new_height = max(0, min(self.carousel_max_height, new_height))
        if new_height != self.carousel_height:
            self.carousel_height = new_height
            if self.carousel_height <= 0:
                self._toggle_carousel()
                self._carousel_drag_start = None
                self._carousel_drag_start_height = None
                self._carousel_dragging = False
                return
            self.carousel_panel.configure(height=self.carousel_height)
            self._update_carousel()
        self._carousel_dragging = True

    def _on_carousel_release(self, event) -> None:
        if self._carousel_drag_start is None:
            return
        delta = event.y_root - self._carousel_drag_start
        if self._carousel_dragging:
            if delta > 60:
                self._toggle_carousel()
            elif self.carousel_height < self.carousel_min_height:
                self.carousel_height = self.carousel_min_height
                if self.carousel_visible:
                    self.carousel_panel.configure(height=self.carousel_height)
                    self._update_carousel()
        else:
            self._toggle_carousel()
        self._carousel_drag_start = None
        self._carousel_drag_start_height = None
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
        except Exception:
            img = Image.new("RGB", (w, h), "#111111")
            draw = ImageDraw.Draw(img)
            draw.text((8, h // 2 - 7), "N/A", fill="#d0d0d0")
            return img

    def _build_duel_thumbnail(self, left_path: str, right_path: str) -> ImageTk.PhotoImage:
        w, h = self.carousel_thumb_size
        left = self._make_thumb_image(left_path)
        right = self._make_thumb_image(right_path)
        if self.blur_enabled:
            left = self._apply_pixelate(left, pixel_size=14)
            right = self._apply_pixelate(right, pixel_size=14)
        composite = Image.new("RGB", (w * 2 + 2, h), "#000000")
        composite.paste(left, (0, 0))
        composite.paste(right, (w + 2, 0))
        return ImageTk.PhotoImage(composite)

    def _attach_history_thumbs(self, entry: dict) -> None:
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

        a_wins_inc = b_wins_inc = 0
        a_losses_inc = b_losses_inc = 0
        chosen_id = None

        if winner == "a":
            new_a, new_b = elo_update(before_a["score"], before_b["score"], True)
            chosen_id = a_id
            a_wins_inc, b_losses_inc = 1, 1
        elif winner == "b":
            new_a, new_b = elo_update(before_a["score"], before_b["score"], False)
            chosen_id = b_id
            b_wins_inc, a_losses_inc = 1, 1
        elif winner == "downvote":
            new_a, new_b = before_a["score"] - DOWNVOTE_PENALTY, before_b["score"] - DOWNVOTE_PENALTY
            a_losses_inc, b_losses_inc = 1, 1
        else:
            new_a, new_b = elo_update(before_a["score"], before_b["score"], None)

        ts = int(time.time())
        self.conn.execute(
            "UPDATE images SET score=?, duels=?, wins=?, losses=?, last_seen=? WHERE id=?",
            (
                new_a,
                before_a["duels"] + 1,
                before_a["wins"] + a_wins_inc,
                before_a["losses"] + a_losses_inc,
                ts,
                a_id,
            ),
        )
        self.conn.execute(
            "UPDATE images SET score=?, duels=?, wins=?, losses=?, last_seen=? WHERE id=?",
            (
                new_b,
                before_b["duels"] + 1,
                before_b["wins"] + b_wins_inc,
                before_b["losses"] + b_losses_inc,
                ts,
                b_id,
            ),
        )
        if entry.get("comparison_id"):
            self.conn.execute(
                "UPDATE comparisons SET chosen_id=?, ts=? WHERE id=?",
                (chosen_id, ts, entry["comparison_id"]),
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
            return
        if self.history_index < len(self.duel_history) - 1:
            self._enter_history_mode(self.history_index + 1)
        else:
            self._exit_history_mode()

    def _on_carousel_slot(self, slot_idx: int) -> None:
        if slot_idx < 0 or slot_idx >= len(self._carousel_slot_map):
            return
        history_idx = self._carousel_slot_map[slot_idx]
        if history_idx is None:
            return
        self._enter_history_mode(history_idx)

    def _update_carousel(self) -> None:
        total = len(self.duel_history)
        if not self.carousel_visible:
            self.carousel_info.configure(text=f"History: {total} (collapsed)")
            self.carousel_prev_btn.configure(state="disabled")
            self.carousel_next_btn.configure(state="disabled")
            return
        if total == 0:
            self.carousel_info.configure(text="History: 0")
            self.carousel_prev_btn.configure(state="disabled")
            self.carousel_next_btn.configure(state="disabled")
            for i, btn in enumerate(self.carousel_slots):
                btn.pack_forget()
                btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                self._carousel_slot_map[i] = None
            return

        active_index = total - 1 if self.history_index is None else self.history_index
        window_end = active_index
        window_start = max(0, window_end - (self.carousel_size - 1))
        indices = list(range(window_start, window_end + 1))
        self._update_carousel_layout(len(indices))

        for i, btn in enumerate(self.carousel_slots):
            # Clear stale Tk image handles first to avoid "image ... doesn't exist" on reconfigure.
            btn.configure(image="")
            if i < len(indices):
                idx = indices[i]
                entry = self.duel_history[idx]
                label = f"{idx + 1}. {self._history_label(entry)}"
                if entry.get("thumb") is None:
                    self._attach_history_thumbs(entry)
                btn.configure(wraplength=max(120, self.carousel_thumb_size[0] * 2))
                btn.configure(
                    text=label,
                    state="normal",
                    bg=ACCENT if idx == active_index and self.history_index is not None else DARK_PANEL,
                    image=entry.get("thumb", ""),
                )
                self._carousel_slot_map[i] = idx
                if not btn.winfo_ismapped():
                    btn.pack(**self._carousel_slot_pack_opts)
            else:
                btn.pack_forget()
                btn.configure(text="--", image="", state="disabled", bg=DARK_PANEL)
                self._carousel_slot_map[i] = None

        if self.history_index is None:
            self.carousel_info.configure(text=f"History: {total} (live duel)")
            self.carousel_prev_btn.configure(state="normal")
            self.carousel_next_btn.configure(state="disabled")
        else:
            self.carousel_info.configure(
                text=f"History: {self.history_index + 1}/{total} (edit mode)",
            )
            self.carousel_prev_btn.configure(state="normal" if self.history_index > 0 else "disabled")
            self.carousel_next_btn.configure(state="normal")

    def _build_tag_menu(self, side: str, parent: tk.Frame) -> None:
        button = tk.Menubutton(
            parent,
            text="Tags: (none)",
            font=("Segoe UI", 9),
            fg=INFO_BAR_FG,
            bg=INFO_BAR_BG,
            activebackground=INFO_BAR_BG,
            activeforeground=INFO_BAR_FG,
            relief="flat",
            cursor="hand2",
        )
        button.grid(row=0, column=2, sticky="e", padx=8, pady=2)
        menu = tk.Menu(button, tearoff=0)
        tag_vars: dict = {}
        for tag in TAG_OPTIONS:
            var = tk.BooleanVar(value=False)
            tag_vars[tag] = var
            menu.add_checkbutton(
                label=tag,
                variable=var,
                command=lambda s=side: self._on_tag_change(s),
            )
        button.configure(menu=menu)
        self._side[side]["tag_vars"] = tag_vars
        self._side[side]["tag_button"] = button

    def _build_action_buttons(self, side: str, parent: tk.Frame) -> None:
        actions = tk.Frame(parent, bg=INFO_BAR_BG)
        actions.grid(row=0, column=1, sticky="e", padx=(0, 8), pady=2)

        spec = [
            ("Upvote", lambda s=side: self.choose(s)),
            ("Downvote", lambda s=side: self.downvote_side(s)),
            ("Skip", lambda s=side: self.skip_side(s)),
            ("Hide", lambda s=side: self.hide_side(s)),
        ]
        buttons: dict = {}
        for text, cmd in spec:
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

    def _write_tags(self, image_id: int, tags: set, hidden: Optional[int] = None) -> None:
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

    def _set_tag_button_label(self, side: str) -> None:
        button = self._side[side].get("tag_button")
        if not button:
            return
        tags = self._side[side].get("tags", [])
        label = "Tags: " + (", ".join(tags) if tags else "(none)")
        button.configure(text=label)

    def _on_tag_change(self, side: str) -> None:
        row = self._side[side].get("row")
        if not row:
            return
        tag_vars = self._side[side].get("tag_vars", {})
        tags = {tag for tag, var in tag_vars.items() if var.get()}
        prev_tags = set(self._side[side].get("tags", []))
        if tags == prev_tags:
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
        data["audio"] = "Y" if has_audio else "N"
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
        random.shuffle(rows)
        if self.pool_filter_var.get() == "Videos (audio)":
            return self._pool_rows_videos_with_audio(rows)
        rows = [r for r in rows if self._row_matches_filter(r)]
        return rows

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
                preferred_tags=set(self._tags_for_row(b)),
            )
            if na:
                a = na
                changed = True
        if b is None and a is not None:
            nb = self.pick_one(
                exclude_id=a[0],
                pool=pool,
                required_kind=self._media_kind(a[1]),
                preferred_tags=set(self._tags_for_row(a)),
            )
            if nb:
                b = nb
                changed = True

        if not a or not b:
            self.load_duel()
            return

        if changed:
            self._set_current(a, b)
            self._render_side("a")
            self._render_side("b")
        self.update_sidebar()

    # -------------------- picking --------------------
    def pick_one(
        self,
        exclude_id: Optional[int],
        pool: List[tuple],
        required_kind: Optional[str] = None,
        preferred_tags: Optional[set] = None,
    ) -> Optional[tuple]:
        if not pool:
            return None
        candidates = pool
        if required_kind is not None:
            candidates = [r for r in candidates if self._media_kind(r[1]) == required_kind]
        if exclude_id is not None:
            candidates = [r for r in candidates if r[0] != exclude_id]
        if not candidates:
            return None
        if preferred_tags:
            tag_matched = [r for r in candidates if preferred_tags.issubset(set(self._tags_for_row(r)))]
            if tag_matched:
                candidates = tag_matched
        return random.choice(candidates)

    def pick_two(self) -> Tuple[Optional[tuple], Optional[tuple]]:
        pool = self._pool_rows()
        if len(pool) < 2:
            return None, None
        pool_by_kind = {"image": [], "gif": [], "video": []}
        for row in pool:
            pool_by_kind[self._media_kind(row[1])].append(row)
        eligible_rows = []
        for rows in pool_by_kind.values():
            if len(rows) >= 2:
                eligible_rows.extend(rows)
        if len(eligible_rows) < 2:
            return None, None
        a = self.pick_one(exclude_id=None, pool=eligible_rows)
        if not a:
            return None, None
        required_kind = self._media_kind(a[1])
        b = self.pick_one(exclude_id=a[0], pool=pool, required_kind=required_kind, preferred_tags=set(self._tags_for_row(a)))
        return a, b

    # -------------------- duel flow --------------------
    def _set_current(self, a: tuple, b: tuple):
        self.current = (a, b)
        self._side["a"]["row"] = a
        self._side["b"]["row"] = b
        self._side["a"]["media_kind"] = self._media_kind(a[1])
        self._side["b"]["media_kind"] = self._media_kind(b[1])

    def load_duel(self):
        a, b = self.pick_two()
        if not a or not b:
            messagebox.showerror("No images", "Not enough items in the selected pool (need at least 2).")
            self.quit()
            return

        self._set_current(a, b)
        self.live_current = self.current
        self._update_info_bars(a, b)
        self.prev_artists.appendleft(a[2])
        self.prev_artists.appendleft(b[2])

        print("[duel] showing:")
        print(f"  LEFT:  {a[1]} (score={a[6]:.2f}, duels={a[3]}, W={a[4]}, L={a[5]})")
        print(f"  RIGHT: {b[1]} (score={b[6]:.2f}, duels={b[3]}, W={b[4]}, L={b[5]})")

        self._render_side("a")
        self._render_side("b")
        self.update_sidebar()
        self._update_carousel()

    def choose(self, winner: Optional[str]):
        if not self.current:
            return
        # snapshot ranks for delta arrows
        prev_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}

        if self.history_index is not None:
            self._apply_revote(self.history_index, winner)
            self._last_ranks = prev_ranks
            self._show_history_entry(self.history_index)
            return

        a, b = self.current
        entry = record_result(self.conn, a, b, winner)
        self._attach_history_thumbs(entry)
        self.duel_history.append(entry)
        self._last_ranks = prev_ranks

        # stop video playback when advancing
        self._stop_video("a")
        self._stop_video("b")
        self.load_duel()

    def _replace_side_keep_other(self, side: str) -> None:
        if not self.current:
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
            preferred_tags=set(self._tags_for_row(other)),
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

    def downvote_side(self, side: str) -> None:
        if not self.current:
            return
        a, b = self.current
        target = a if side == "a" else b
        now_ts = int(time.time())
        self.conn.execute(
            "UPDATE images SET score=score-?, duels=duels+1, losses=losses+1, last_seen=? WHERE id=?",
            (DOWNVOTE_PENALTY, now_ts, target[0]),
        )
        self.conn.commit()
        self._replace_side_keep_other(side)

    def skip_side(self, side: str) -> None:
        if not self.current:
            return
        self._replace_side_keep_other(side)

    def undo_side_tag_hide(self, side: str) -> None:
        if not self.current:
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
        if not self.current:
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

    def _render_image_or_gif(self, side: str, widget: tk.Label, path: str):
        self.root.update_idletasks()
        w = max(1, widget.winfo_width())
        h = max(1, widget.winfo_height())
        if w <= 5 or h <= 5:
            self.root.after(50, lambda: self._render_image_or_gif(side, widget, path))
            return
        target = (max(120, w - 12), max(120, h - 12))

        try:
            im = Image.open(path)
        except Exception as e:
            widget.configure(text=f"Failed to load:\n{path}\n\n{e}", fg=TEXT_COLOR, bg=DARK_PANEL)
            return

        is_animated = (getattr(im, "is_animated", False) and getattr(im, "n_frames", 1) > 1)

        if not is_animated:
            try:
                im.seek(0)
            except Exception:
                pass
            if im.mode not in ("RGB", "RGBA"):
                im = im.convert("RGB")
            im.thumbnail(target, Image.Resampling.LANCZOS)
            if self.blur_enabled:
                im = self._apply_pixelate(im, pixel_size=50)
            tk_im = ImageTk.PhotoImage(im)
            widget.configure(image=tk_im, text="", bg=DARK_PANEL)
            widget.image = tk_im
            return

        # GIF animation
        frames: List[ImageTk.PhotoImage] = []
        delays: List[int] = []
        try:
            for frame in ImageSequence.Iterator(im):
                delay = frame.info.get("duration", im.info.get("duration", 100))
                delays.append(int(delay))
                fr = frame.convert("RGBA") if frame.mode != "RGBA" else frame.copy()
                fr.thumbnail(target, Image.Resampling.LANCZOS)
                if self.blur_enabled:
                    fr = self._apply_pixelate(fr, pixel_size=50)
                frames.append(ImageTk.PhotoImage(fr))
        except Exception:
            # fallback: first frame only
            im.seek(0)
            fr = im.convert("RGBA") if im.mode != "RGBA" else im.copy()
            fr.thumbnail(target, Image.Resampling.LANCZOS)
            if self.blur_enabled:
                fr = self._apply_pixelate(fr, pixel_size=50)
            tk_im = ImageTk.PhotoImage(fr)
            widget.configure(image=tk_im, text="", bg=DARK_PANEL)
            widget.image = tk_im
            return

        st = self._side[side]
        st["anim_frames"] = frames
        st["anim_delays"] = delays
        st["anim_index"] = 0

        def step():
            st2 = self._side[side]
            if not st2.get("anim_frames"):
                return
            idx = st2["anim_index"] % len(st2["anim_frames"])
            widget.configure(image=st2["anim_frames"][idx], text="", bg=DARK_PANEL)
            widget.image = st2["anim_frames"][idx]
            st2["anim_index"] = (idx + 1) % len(st2["anim_frames"])
            delay = max(20, int(st2["anim_delays"][idx] if idx < len(st2["anim_delays"]) else 100))
            st2["anim_job"] = self.root.after(delay, step)

        st["anim_job"] = self.root.after(0, step)

    def _cancel_animation(self, side: str):
        st = self._side[side]
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
        st.setdefault("waveform_key", None)    # cache key
        st.setdefault("waveform_job", None)    # background thread guard
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
        wave.bind("<Configure>", lambda e: self._redraw_waveform(side))

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
        # Try imageio-ffmpeg first (recommended), fallback to PATH.
        try:
            import imageio_ffmpeg
            exe = imageio_ffmpeg.get_ffmpeg_exe()
            if exe and os.path.exists(exe):
                return exe
        except Exception:
            pass
        try:
            exe = shutil.which("ffmpeg")
            if exe:
                return exe
        except Exception:
            pass
        return None

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

        # Avoid duplicate jobs
        if st.get("waveform_job") is not None:
            return

        exe = self._ffmpeg_exe()
        if not exe:
            return

        t = threading.Thread(target=self._waveform_worker, args=(side, path, key, exe), daemon=True)
        st["waveform_job"] = t
        t.start()

    def _waveform_worker(self, side: str, path: str, key: str, exe: str):
        try:
            out_dir = Path(tempfile.gettempdir()) / "image_duel_ranker_waveforms"
            out_dir.mkdir(parents=True, exist_ok=True)
            h = hashlib.md5(key.encode("utf-8")).hexdigest()
            out_png = out_dir / f"wave_{h}.png"

            if not out_png.exists():
                cmd = [
                    exe, "-hide_banner", "-loglevel", "error",
                    "-i", path,
                    "-filter_complex", "showwavespic=s=800x60:split_channels=0",
                    "-frames:v", "1",
                    "-y", str(out_png)
                ]
                r = subprocess.run(cmd, check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

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
            else:
                img = Image.open(str(out_png)).convert("RGBA")
                status = ""
                # Detect "blank" waveforms and tint for visibility on dark UI.
                try:
                    gray = img.convert("L")
                    mx = int(gray.getextrema()[1] or 0)
                    hist = gray.histogram()
                    total = sum(hist) or 1
                    cutoff = int(total * 0.95)
                    acc = 0
                    p95 = 0
                    for i, count in enumerate(hist):
                        acc += count
                        if acc >= cutoff:
                            p95 = i
                            break
                    if mx < 8 or p95 < 8:
                        img = None
                        status = "no-audio"
                    else:
                        hx = ACCENT.lstrip("#")
                        if len(hx) == 3:
                            hx = "".join([c*2 for c in hx])
                        r0, g0, b0 = int(hx[0:2], 16), int(hx[2:4], 16), int(hx[4:6], 16)
                        noise_floor = max(10, int(p95 * 0.25))
                        alpha = gray.point(lambda p: 0 if p <= noise_floor else min(255, int((p - noise_floor) * 5)))
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
                self._redraw_waveform(side)

            self.root.after(0, done)
        except Exception:
            def clear():
                st = self._side.get(side)
                if st:
                    st["waveform_job"] = None
            try:
                self.root.after(0, clear)
            except Exception:
                pass

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
            "dislikes_adjusted": f"Shrunken Avg - dislikes×{DISLIKES_PER_FILE_PENALTY:g}",
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
        folder_left, folder_right = a[2], b[2]

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

        lines = []
        deltas: List[Tuple[int, str]] = []
        for idx, row in enumerate(leader[start:end]):
            leaf = trunc(Path(row["folder"]).name)
            marker = "  ◀" if row["folder"] in {folder_left, folder_right} else ""
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
            if self.metric == "avg":
                line = f"{ticker} {row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['avg']:6.1f}  (n={row['n']}){marker}"
            elif self.metric == "dislikes_adjusted":
                line = (
                    f"{ticker} {row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  "
                    f"avg={row['avg']:5.1f} d={row.get('dislikes_n', 0)} (n={row['n']}){marker}"
                )
            elif self.metric == "shrunken_avg":
                line = f"{ticker} {row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']}){marker}"
            else:
                line = f"{ticker} {row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']}){marker}"
            lines.append(line)
            deltas.append((idx, ticker_tag))

        self.board.configure(state="normal")
        self.board.delete("1.0", "end")
        if lines:
            self.board.insert("1.0", "\n".join(lines))
            for row_idx, tag in deltas:
                self.board.tag_add(tag, f"{row_idx + 1}.0", f"{row_idx + 1}.1")
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
            folder = Path(row[2]).name if row and len(row) > 2 else "(unknown)"
            p = Path(row[1]) if row and len(row) > 1 else Path("")
            ext = p.suffix.lower().lstrip(".")
            score = float(row[6]) if row and len(row) > 6 else 0.0
            duels = int(row[3]) if row and len(row) > 3 else 0
            w = int(row[4]) if row and len(row) > 4 else 0
            l = int(row[5]) if row and len(row) > 5 else 0
            return f"{folder}   •  {ext.upper()}  •  {score:.1f}  •  W{w} L{l}  •  shown {duels}"
        try:
            self.left_info_text.configure(text=fmt(a))
            self.right_info_text.configure(text=fmt(b))
        except Exception:
            pass

    def _counters_block(self, a: tuple, b: tuple) -> str:
        # per-image
        def img_line(prefix: str, row: tuple) -> str:
            return (f"{prefix}: duels={row[3]:>4}  W={row[4]:>4}  L={row[5]:>4}  score={row[6]:7.2f}")

        # per-artist
        def artist_totals(folder: str) -> Tuple[int, int, int, int]:
            # (images, shown, wins, losses)
            res = self.conn.execute("""
                SELECT COUNT(*), COALESCE(SUM(duels),0), COALESCE(SUM(wins),0), COALESCE(SUM(losses),0)
                FROM images WHERE folder=?
            """, (folder,)).fetchone()
            imgs, shown, w, l = (int(res[0]), int(res[1]), int(res[2]), int(res[3])) if res else (0, 0, 0, 0)
            return imgs, shown, w, l

        la = Path(a[2]).name
        ra = Path(b[2]).name
        la_imgs, la_shown, la_w, la_l = artist_totals(a[2])
        ra_imgs, ra_shown, ra_w, ra_l = artist_totals(b[2])

        return "\n".join([
            img_line("LeftImg ", a),
            img_line("RightImg", b),
            f"LeftArt : {la}  imgs={la_imgs}  shown={la_shown}  decisions={la_w+la_l}  W={la_w} L={la_l}",
            f"RightArt: {ra}  imgs={ra_imgs}  shown={ra_shown}  decisions={ra_w+ra_l}  W={ra_w} L={ra_l}",
        ])

    def _keybind_text(self) -> str:
        return "\n".join([
            "Keybinds:",
            "L Click: Vote",
            "R Click: Skip",
            "M Click: Hide",
            "",
            "Shift + L Click: Downvote",
            "Ctrl + L Click: More Options",
            "",
            "1: Vote Left",
            "2: Vote Right",
            "3: Focus Left",
            "4: Downvote Left",
            "5: Downvote Right",
            "6: Focus Right",
            "7: Skip Left",
            "8: Skip Right",
            "9: Toggle Focus",
            "0: Skip Both",
            ".: Toggle Blur",
        ])

    def _on_shift_downvote(self, side: str, _event=None):
        self.downvote_side(side)
        return "break"

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
        menu.add_command(label="Upvote", command=lambda s=side: self.choose(s))
        menu.add_command(label="Downvote", command=lambda s=side: self.downvote_side(s))
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
        snapshot = self._capture_video_snapshot(side, (target_w, target_h))
        if snapshot is None:
            snapshot = Image.effect_noise((target_w, target_h), 64).convert("RGB")
        if snapshot.size != (target_w, target_h):
            snapshot = snapshot.resize((target_w, target_h), Image.Resampling.LANCZOS)
        snapshot = self._apply_pixelate(snapshot, pixel_size=50)
        if HAVE_VLC and st.get("vlc_player"):
            self._set_video_blur_visible(side, False)
            self._set_vlc_blur_logo(side, snapshot)
            return
        tk_im = ImageTk.PhotoImage(snapshot)
        label = st.get("video_blur_label")
        if not label:
            return
        label.configure(image=tk_im)
        label.image = tk_im
        st["video_blur_image"] = tk_im
        self._set_video_blur_visible(side, True)

    def toggle_blur(self):
        self.blur_enabled = not getattr(self, "blur_enabled", False)
        self._update_blur_toggle_style()

        for entry in self.duel_history:
            try:
                entry["thumb"] = self._build_duel_thumbnail(entry["a_path"], entry["b_path"])
            except Exception:
                entry["thumb"] = None
        self._update_carousel()

        for side in ("a", "b"):
            st = self._side.get(side, {})
            row = st.get("row")
            if not row:
                continue
            if st.get("media_kind") == "video":
                vframe = self.left_video if side == "a" else self.right_video
                self._update_video_blur_overlay(side, vframe, row[1])

        # Defer still-image re-render one tick to avoid transient empty frames.
        self.root.after_idle(self._refresh_visuals_only)

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
        num_rows = max(1, math.ceil(total_items / min(37, max_artist)))
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

        msg = "\n".join([
            f"Images: {n_images} (hidden: {n_hidden})",
            f"Comparisons: {n_comp}",
            f"First duel: {fmt(tmin)}",
            f"Last duel:  {fmt(tmax)}",
            "",
            f"SUM(images.duels)   = {sum_duels}",
            f"SUM(images.wins)    = {sum_wins}",
            f"SUM(images.losses)  = {sum_losses}",
            f"Comparisons * 2     = {n_comp * 2}",
            "",
            "A reset usually shows as: comparisons near 0 and first/last duel very recent.",
        ])
        messagebox.showinfo("DB stats", msg)

    # -------------------- refresh visuals only --------------------
    def _refresh_visuals_only(self):
        # Only rerender still images/gifs, avoid touching VLC players.
        for side in ("a", "b"):
            st = self._side[side]
            row = st.get("row")
            if not row:
                continue
            kind = self._media_kind(row[1])
            if kind == "video":
                # do nothing; VLC output is independent of Tk size changes
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
            iso = datetime.utcfromtimestamp(last_seen).isoformat() + "Z" if last_seen else ""
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

    # optional report
    try:
        csv_path = Path(ROOT_DIR) / "image_duel_report.csv"
        export_csv(conn, csv_path)
        print(f"[report] CSV written: {csv_path}")
    except Exception:
        pass
    try:
        show_folder_chart(conn)
    except Exception:
        pass

if __name__ == "__main__":
    run()
