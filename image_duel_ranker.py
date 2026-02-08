# image_duel_ranker.py
# Image Duel Ranker — Elo-style dueling with artist leaderboard, e621 link export, and in-app VLC video playback.
# Version: 2026-02-08c
# Update: Make the history drawer framing visibly distinct.
# Build: 2026-01-25c (aligned tag dropdowns)

import os
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

from PIL import Image, ImageTk, ImageSequence, ImageFilter

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
BLUR_RADIUS = 18

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

LEADERBOARD_METRIC_DEFAULT = "shrunken_avg"  # avg | shrunken_avg | lcb
FOLDER_MIN_N = 1
FOLDER_PRIOR_IMAGES = 8
LCB_Z = 1.0

E621_MAX_TAGS = 40
DEFAULT_COMMON_TAGS = "order:created_asc date:28_months_ago -voted:everything"

TAG_OPTIONS = ["SFW", "MEME", "HIDE", "CW"]

BUILD_STAMP = '2026-01-25c (aligned tag dropdowns)'

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
    if metric in ("avg", "shrunken_avg"):
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
                     if metric == "shrunken_avg" else avg_s)
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score})
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
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score})
    else:
        return folder_leaderboard(conn, metric="avg", min_n=min_n)

    rows.sort(key=lambda r: r["score"], reverse=True)
    out: List[dict] = []
    for i, r in enumerate(rows, start=1):
        out.append({
            "folder": r["folder"], "avg": r["avg"], "n": r["n"],
            "rank": i, "score": r["score"], "metric": metric
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
def record_result(conn: sqlite3.Connection, a: tuple, b: tuple, winner: Optional[str]) -> None:
    a_id, a_path, a_folder, a_duels, a_wins, a_losses, a_score, a_hidden = a[:8]
    b_id, b_path, b_folder, b_duels, b_wins, b_losses, b_score, b_hidden = b[:8]

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
    conn.commit()

    # Sidecars (async-ish, but safe in a short thread)
    try:
        # import threading (moved to top-level)
        threading.Thread(target=update_image_metadata, args=(Path(a_path), float(new_a)), daemon=True).start()
        threading.Thread(target=update_image_metadata, args=(Path(b_path), float(new_b)), daemon=True).start()
    except Exception:
        pass

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
        self.prev_artists = deque(maxlen=20)
        self.page = 0
        self.metric = LEADERBOARD_METRIC_DEFAULT
        self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
        self._resize_job = None
        self._audio_cache = {}

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
        self.container.pack(fill="both", expand=True)

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
        self.left_info_row.columnconfigure(0, weight=1)
        self.right_info_row.columnconfigure(0, weight=1)

        # Make info bars behave like the image/video panel for clicks
        for w in (self.left_info_bar, self.left_info_text):
            w.bind("<Button-1>", lambda e: self.choose("a"))
            w.bind("<Button-3>", lambda e: self.choose("downvote"))
            w.bind("<Button-2>", lambda e: self.hide_side("a"))
            w.bind("<Double-Button-1>", self.open_left)
            w.bind("<Control-Button-1>", lambda e: self.toggle_video("a"))

        for w in (self.right_info_bar, self.right_info_text):
            w.bind("<Button-1>", lambda e: self.choose("b"))
            w.bind("<Button-3>", lambda e: self.choose("downvote"))
            w.bind("<Button-2>", lambda e: self.hide_side("b"))
            w.bind("<Double-Button-1>", self.open_right)
            w.bind("<Control-Button-1>", lambda e: self.toggle_video("b"))

        self.left_video = tk.Frame(self.left_container, bg="black", bd=0, highlightthickness=0)
        self.right_video = tk.Frame(self.right_container, bg="black", bd=0, highlightthickness=0)
        self.left_video.place_forget()
        self.right_video.place_forget()

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
        self.pool_filter = ttk.Combobox(
            self.pool_filter_row,
            textvariable=self.pool_filter_var,
            values=["All", "Images", "GIFs", "Videos", "Videos (audio)", "Animated", "Hidden"],
            state="readonly",
            width=12,
        )
        self.pool_filter.pack(side="right")
        self.pool_filter.bind("<<ComboboxSelected>>", lambda e: self.on_pool_filter_change())

        # Sidebar toggle (focus mode)
        self.sidebar_visible = True
        self.sidebar_toggle_btn = tk.Button(self.pool_filter_row, text="Focus",
                                            command=self.toggle_sidebar,
                                            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat", width=7)
        self.sidebar_toggle_btn.pack(side="right")
        self.blur_enabled = False
        self.blur_toggle_btn = tk.Button(self.pool_filter_row, text="Blur: Off",
                                         command=self.toggle_blur,
                                         bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat", width=9)
        self.blur_toggle_btn.pack(side="right", padx=(0, 6))
        self.pool_filter_row.pack(fill="x", pady=(0, 6))

        # ---- Leaderboard ----
        self.leader_header = tk.Label(self.sidebar, text="Top Artists",
                                      font=("Segoe UI", 12, "bold"), fg=ACCENT, bg=DARK_BG)
        self.metric_label = tk.Label(self.sidebar, text="", font=("Segoe UI", 9), fg=TEXT_COLOR, bg=DARK_BG)
        self.page_label = tk.Label(self.sidebar, text="", font=("Segoe UI", 9), fg=TEXT_COLOR, bg=DARK_BG)

        self.board = tk.Text(self.sidebar, height=20, font=("Consolas", 10),
                             bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                             relief="flat", wrap="none")
        # ---- Counters ----
        self.counters_header = tk.Label(self.sidebar, text="Counters",
                                        font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.counters_text = tk.Label(self.sidebar, text="", justify="left",
                                      font=("Consolas", 9), fg=TEXT_COLOR, bg=DARK_BG)

        # ---- Current / Previous ----
        self.now_header = tk.Label(self.sidebar, text="Current / Previous",
                                   font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.now_frame = tk.Frame(self.sidebar, bg=DARK_PANEL, bd=1, relief="solid")
        self.now_handle = tk.Frame(self.now_frame, bg=SEPARATOR_BG, height=6)
        self.now_handle.pack(fill="x", padx=6, pady=(6, 0))
        self.now = tk.Text(self.now_frame, height=6, wrap="word",
                           font=("Segoe UI", 10), fg=TEXT_COLOR, bg=DARK_PANEL,
                           relief="flat", highlightthickness=0, bd=0)
        self.now.configure(state="disabled")
        self.now.bind("<MouseWheel>", self._scroll_now)
        self.now.bind("<Button-4>", self._scroll_now)
        self.now.bind("<Button-5>", self._scroll_now)
        self.now.pack(fill="x", padx=6, pady=(4, 6))

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

        # ---- Search tags + export ----
        self.search_header = tk.Label(self.sidebar, text="Search tags",
                                      font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.common_tags_entry = tk.Entry(self.sidebar, font=("Consolas", 9),
                                          bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                                          relief="flat")
        self.common_tags_entry.insert(0, DEFAULT_COMMON_TAGS)

        self.export_links_btn = tk.Button(self.sidebar, text="Export e621 links (clipboard + file)",
                                          command=self.export_e621_links,
                                          bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat")
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
        self.metric_label.pack(anchor="w")
        self.page_label.pack(anchor="e", pady=(0, 4))
        self.board.pack(fill="x", pady=(4, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.counters_header.pack(anchor="w", pady=(2, 0))
        self.counters_text.pack(anchor="w", pady=(2, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.now_header.pack(anchor="w")
        self.now_frame.pack(fill="x", pady=(2, 6))

        self.links_header.pack(anchor="w")
        self.link_left.pack(anchor="w")
        self.link_right.pack(anchor="w", pady=(0, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.search_header.pack(anchor="w")
        self.common_tags_entry.pack(fill="x", pady=(2, 6))
        self.export_links_btn.pack(fill="x", pady=(0, 2))
        self.view_links_btn.pack(fill="x", pady=(0, 2))
        self.db_stats_btn.pack(fill="x", pady=(0, 6))
        self.export_status.pack(anchor="w", pady=(0, 6))
        tk.Frame(self.sidebar, height=1, bg=SEPARATOR_BG).pack(fill="x", pady=(0, 6))

        self.keys_header.pack(anchor="w")
        self.keys_text.pack(anchor="w")

        # ---- Mouse controls ----
        self.left_panel.bind("<Button-1>", lambda e: self.choose("a"))
        self.right_panel.bind("<Button-1>", lambda e: self.choose("b"))
        self.left_panel.bind("<Double-Button-1>", self.open_left)
        self.right_panel.bind("<Double-Button-1>", self.open_right)
        self.left_panel.bind("<Button-3>", lambda e: self.choose("downvote"))
        self.right_panel.bind("<Button-3>", lambda e: self.choose("downvote"))

        # Hide: middle click
        self.left_panel.bind("<Button-2>", lambda e: self.hide_side("a"))
        self.right_panel.bind("<Button-2>", lambda e: self.hide_side("b"))

        # Ctrl+Click: play/pause that side if video
        self.left_panel.bind("<Control-Button-1>", lambda e: self.toggle_video("a"))
        self.right_panel.bind("<Control-Button-1>", lambda e: self.toggle_video("b"))

        # Also allow click on video frames
        for w, side in [(self.left_video, "a"), (self.right_video, "b")]:
            w.bind("<Control-Button-1>", lambda e, s=side: self.toggle_video(s))
            w.bind("<Double-Button-1>", self.open_left if side == "a" else self.open_right)
            w.bind("<Button-1>", lambda e, s=side: self.choose("a" if s == "a" else "b"))

        # ---- Keybinds ----
        root.bind("1", lambda e: self.choose("a"))
        root.bind("2", lambda e: self.choose("b"))
        root.bind("3", lambda e: self.choose("downvote"))
        root.bind("0", lambda e: self.choose(None))
        root.bind("<space>", lambda e: self.choose(None))

        root.bind("x", lambda e: self.hide_side("a"))
        root.bind("m", lambda e: self.hide_side("b"))

        root.bind("o", self.open_left)
        root.bind("p", self.open_right)
        root.bind("O", self.reveal_left_folder)
        root.bind("P", self.reveal_right_folder)

        root.bind("[", lambda e: self.change_page(-1))
        root.bind("]", lambda e: self.change_page(+1))
        root.bind("<Prior>", lambda e: self.change_page(-1))
        root.bind("<Next>", lambda e: self.change_page(+1))

        root.bind("t", lambda e: self.toggle_metric())
        root.bind("g", lambda e: self.export_e621_links())
        root.bind("G", lambda e: self.export_e621_links())
        root.bind("v", lambda e: self.show_links_view())
        root.bind("V", lambda e: self.show_links_view())
        root.bind("i", lambda e: self.show_db_stats())
        root.bind("I", lambda e: self.show_db_stats())

        # Video (VLC) controls
        root.bind("<Control-1>", lambda e: self.toggle_video("a"))
        root.bind("<Control-2>", lambda e: self.toggle_video("b"))
        root.bind("<Control-Shift-1>", lambda e: self.toggle_mute("a"))
        root.bind("<Control-Shift-2>", lambda e: self.toggle_mute("b"))

        root.bind("q", lambda e: self.quit())

        root.bind("<Configure>", self._on_configure)

        # Start periodic UI tick (scrub/time updates)
        self._tick_job = None
        self._tick()

        self.load_duel()

    # -------------------- helpers / state --------------------
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

            "scrubbing": False,
            "tags": [],
            "tag_vars": {},
            "tag_button": None,
        }

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
        button.grid(row=0, column=1, sticky="e", padx=8, pady=2)
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

    def _row_matches_filter(self, row: tuple) -> bool:
        # row: (id, path, folder, duels, wins, losses, score, hidden, tags)
        hidden = int(row[7] or 0)
        f = self.pool_filter_var.get()
        kind = self._media_kind(row[1])

        if f == "Hidden":
            return hidden == 1
        if hidden == 1:
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
            )
            if na:
                a = na
                changed = True
        if b is None and a is not None:
            nb = self.pick_one(
                exclude_id=a[0],
                pool=pool,
                required_kind=self._media_kind(a[1]),
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
        b = self.pick_one(exclude_id=a[0], pool=pool, required_kind=required_kind)
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
        self._update_info_bars(a, b)
        self.prev_artists.appendleft(a[2])
        self.prev_artists.appendleft(b[2])

        print("[duel] showing:")
        print(f"  LEFT:  {a[1]} (score={a[6]:.2f}, duels={a[3]}, W={a[4]}, L={a[5]})")
        print(f"  RIGHT: {b[1]} (score={b[6]:.2f}, duels={b[3]}, W={b[4]}, L={b[5]})")

        self._render_side("a")
        self._render_side("b")
        self.update_sidebar()

    def choose(self, winner: Optional[str]):
        if not self.current:
            return
        # snapshot ranks for delta arrows
        prev_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}

        a, b = self.current
        record_result(self.conn, a, b, winner)

        self._last_ranks = prev_ranks

        # stop video playback when advancing
        self._stop_video("a")
        self._stop_video("b")
        self.load_duel()

    def hide_side(self, side: str):
        if not self.current:
            return
        a, b = self.current
        target = a if side == "a" else b
        other = b if side == "a" else a

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

        pool = self._pool_rows()  # respects current filter
        replacement = self.pick_one(
            exclude_id=other[0],
            pool=pool,
            required_kind=self._media_kind(other[1]),
        )
        if not replacement:
            # if no replacement in pool, just reload duel
            self.load_duel()
            return

        if side == "a":
            self._set_current(replacement, other)
        else:
            self._set_current(other, replacement)

        # stop old side video
        self._stop_video(side)
        self._render_side(side)
        self.update_sidebar()

    # -------------------- rendering --------------------
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

    def _apply_blur(self, im: Image.Image) -> Image.Image:
        if not getattr(self, "blur_enabled", False):
            return im
        try:
            return im.filter(ImageFilter.GaussianBlur(BLUR_RADIUS))
        except Exception:
            return im

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
            im = self._apply_blur(im)
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
                fr = self._apply_blur(fr)
                frames.append(ImageTk.PhotoImage(fr))
        except Exception:
            # fallback: first frame only
            im.seek(0)
            fr = im.convert("RGBA") if im.mode != "RGBA" else im.copy()
            fr.thumbnail(target, Image.Resampling.LANCZOS)
            fr = self._apply_blur(fr)
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
            return

        # If already playing this path, do nothing (do not reset on refresh)
        if st.get("vlc_player") and st.get("vlc_media") == path:
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

        st["vlc_init_job"] = self.root.after(180, finalize)
        self._attach_vlc_events(side)

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

    def _metric_human(self) -> str:
        return {
            "avg": "Simple Avg",
            "shrunken_avg": f"Shrunken Avg (prior={FOLDER_PRIOR_IMAGES})",
            "lcb": f"Lower Conf. Bound (z={LCB_Z})"
        }.get(self.metric, self.metric)

    def toggle_metric(self):
        order = ["shrunken_avg", "avg", "lcb"]
        i = order.index(self.metric) if self.metric in order else 0
        self.metric = order[(i + 1) % len(order)]
        self._last_ranks = {r["folder"]: r["rank"] for r in folder_leaderboard(self.conn, metric=self.metric)}
        self.page = 0
        self.update_sidebar()

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

        self.metric_label.configure(text=f"[Metric: {self._metric_human()}]")
        self.page_label.configure(text=f"Page {self.page+1}/{total_pages}  (total {total})")

        # Leaderboard lines
        def trunc(name: str) -> str:
            return name if len(name) <= LEAF_MAX else (name[:LEAF_MAX - 1] + "…")

        lines = []
        for row in leader[start:end]:
            leaf = trunc(Path(row["folder"]).name)
            marker = "  ◀" if row["folder"] in {folder_left, folder_right} else ""
            if self.metric == "avg":
                line = f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['avg']:6.1f}  (n={row['n']}){marker}"
            elif self.metric == "shrunken_avg":
                line = f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']}){marker}"
            else:
                line = f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']}){marker}"
            lines.append(line)

        self.board.configure(state="normal")
        self.board.delete("1.0", "end")
        self.board.insert("1.0", "\n".join(lines) if lines else "No folders yet.")
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

        self._set_now_text("\n".join([l_line, r_line] + prev_display))

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
            "L-Click:   Pick LEFT",
            "R-Click:   Pick RIGHT",
            "R-Click(3):Downvote (both)",
            "0 / Space: Skip / tie",
            "",
            "M-Click:   Hide side (replace only that side)",
            "X / M:     Hide LEFT / Hide RIGHT",
            "",
            "Dbl-Click: Open image/video",
            "O / P:     Open LEFT / Open RIGHT",
            "Shift+O/P: Reveal LEFT/RIGHT folder",
            "",
            "[ / PgUp:  Prev leaderboard page",
            "] / PgDn:  Next leaderboard page",
            "T:         Toggle leaderboard metric",
            "G:         Export e621 links",
            "V:         View/open e621 links",
            "I:         DB stats",
            "",
            "Ctrl+1/2:  Play/Pause LEFT/RIGHT video",
            "Ctrl+Shift+1/2: Mute/Unmute LEFT/RIGHT",
            "Ctrl+Click: Play/Pause hovered side",
            "",
            "Ctrl+B:    Toggle sidebar (focus mode)",
            "Q:         Quit",
        ])

    def _scroll_now(self, event):
        if not getattr(self, "now", None):
            return "break"
        if getattr(event, "delta", 0):
            direction = -1 if event.delta > 0 else 1
        else:
            direction = -1 if getattr(event, "num", None) == 4 else 1
        try:
            self.now.yview_scroll(direction, "units")
        except Exception:
            pass
        return "break"

    def _set_now_text(self, text: str) -> None:
        try:
            self.now.configure(state="normal")
            self.now.delete("1.0", "end")
            self.now.insert("1.0", text)
            self.now.configure(state="disabled")
            self.now.yview_moveto(0)
        except Exception:
            pass

    def toggle_blur(self):
        self.blur_enabled = not getattr(self, "blur_enabled", False)
        self._update_blur_toggle()
        self._refresh_visuals_only()

    def _update_blur_toggle(self):
        if not getattr(self, "blur_toggle_btn", None):
            return
        label = "Blur: On" if getattr(self, "blur_enabled", False) else "Blur: Off"
        self.blur_toggle_btn.configure(text=label)

    # -------------------- file open / reveal --------------------

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
        raw = (self.common_tags_entry.get() or "").strip()
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

        btn_frame = tk.Frame(win, bg=DARK_BG)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))

        tk.Button(btn_frame, text="Refresh", command=self._links_refresh,
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
