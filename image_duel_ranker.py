import os
import re
import math
import random
import sqlite3
import time
import json
import threading
import webbrowser
from pathlib import Path
from datetime import datetime
from collections import deque
from typing import Optional
from urllib.parse import quote_plus

from PIL import Image, ImageTk, ImageSequence
import tkinter as tk
import tkinter.font as tkfont
import tkinter.messagebox as messagebox

# Optional: folder chart on quit
try:
    import matplotlib.pyplot as plt
except Exception:
    plt = None

# Optional: embed JPEG EXIF UserComment
try:
    import piexif
except Exception:
    piexif = None


# Optional: in-app video preview (requires: imageio + imageio-ffmpeg)
try:
    import imageio.v2 as imageio
except Exception:
    imageio = None

# -------------------- THEME (Dark Mode) --------------------
DARK_BG    = "#1e1e1e"
DARK_PANEL = "#252526"
DARK_BORDER= "#333333"
TEXT_COLOR = "#eeeeee"
ACCENT     = "#569cd6"
LINK_COLOR = "#4ea1ff"

# -------------------- CONFIG --------------------
DEFAULT_COMMON_TAGS = "order:created_asc date:28_months_ago -voted:everything"

POOL_FILTER_OPTIONS = ["All", "Images", "GIFs", "Videos", "Animated", "Hidden"]

ROOT_DIR = r"I:\OneDrive\Discord Downloader Output\+\Grabber"
SCRIPT_DIR = Path(__file__).resolve().parent
DB_PATH = SCRIPT_DIR / ".image_ranking.sqlite"
SIDEcar_DIR = SCRIPT_DIR / ".image_duel_sidecars"
SIDEcar_DIR.mkdir(parents=True, exist_ok=True)

EMBED_JPEG_EXIF = False
WINDOW_SIZE = (1500, 950)

IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".bmp", ".tif", ".tiff"}
GIF_EXTS = {".gif"}
VIDEO_EXTS = {".mp4", ".m4v", ".webm", ".mkv", ".avi", ".mov", ".wmv"}
SUPPORTED_EXTS = IMAGE_EXTS | GIF_EXTS | VIDEO_EXTS
K_FACTOR   = 32.0
BASE_SCORE = 1000.0

LEADERBOARD_SIZE  = 30
DOWNVOTE_PENALTY  = 12.0
LEAF_MAX          = 24

# Leaderboard anti-bias options
LEADERBOARD_METRIC_DEFAULT = "shrunken_avg"  # 'avg', 'shrunken_avg', 'lcb'
FOLDER_MIN_N        = 1
FOLDER_PRIOR_IMAGES = 8
LCB_Z               = 1.0

# -------------------- DB --------------------
def init_db():
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
            hidden INTEGER DEFAULT 0
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

def migrate_schema(conn):
    cols = [row[1] for row in conn.execute("PRAGMA table_info(images)")]
    if "hidden" not in cols:
        print("[migrate] adding 'hidden' column to images")
        conn.execute("ALTER TABLE images ADD COLUMN hidden INTEGER DEFAULT 0")
        conn.commit()
        conn.execute("UPDATE images SET hidden=0 WHERE hidden IS NULL")
        conn.commit()

def scan_images(conn):
    cur = conn.cursor()
    existing = {row[0] for row in cur.execute("SELECT path FROM images")}
    to_add = []
    print("[scan] scanning", ROOT_DIR)
    for p in Path(ROOT_DIR).rglob("*"):
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
def elo_expected(sa, sb):
    return 1.0 / (1.0 + 10 ** ((sb - sa) / 400.0))

def elo_update(sa, sb, winner_is_a):
    ea, eb = elo_expected(sa, sb), elo_expected(sb, sa)
    if winner_is_a is None:
        return (sa + K_FACTOR * (0.5 - ea), sb + K_FACTOR * (0.5 - eb))
    elif winner_is_a:
        return (sa + K_FACTOR * (1.0 - ea), sb + K_FACTOR * (0.0 - eb))
    else:
        return (sa + K_FACTOR * (0.0 - ea), sb + K_FACTOR * (1.0 - eb))

# -------------------- Leaderboard (anti-bias) --------------------
def folder_leaderboard(conn, metric=LEADERBOARD_METRIC_DEFAULT, min_n=FOLDER_MIN_N):
    mu_row = conn.execute("SELECT AVG(score) FROM images WHERE hidden=0").fetchone()
    global_mu = float(mu_row[0] if mu_row and mu_row[0] is not None else BASE_SCORE)

    rows = []
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
            score = (avg_s * n + global_mu * FOLDER_PRIOR_IMAGES) / (n + FOLDER_PRIOR_IMAGES) \
                    if metric == "shrunken_avg" else avg_s
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
            var = max(0.0, avg_sq - avg_s*avg_s)
            se = (var ** 0.5) / (n ** 0.5) if n > 0 else 0.0
            score = avg_s - LCB_Z * se
            rows.append({"folder": folder, "avg": avg_s, "n": n, "score": score})
    else:
        return folder_leaderboard(conn, metric="avg", min_n=min_n)

    rows.sort(key=lambda r: r["score"], reverse=True)
    out = []
    for i, r in enumerate(rows, start=1):
        out.append({'folder': r['folder'], 'avg': r['avg'], 'n': r['n'], 'rank': i, 'score': r['score'], 'metric': metric})
    return out

def find_folder_rank(leader, folder_path_str):
    for item in leader:
        if item['folder'] == folder_path_str:
            return item['rank'], item['avg'], item['n']
    return None, None, None

# -------------------- Record results --------------------
def update_image_metadata(path: Path, score: float):
    SIDEcar_DIR.mkdir(parents=True, exist_ok=True)
    side = SIDEcar_DIR / (path.name + ".json")
    side.write_text(json.dumps({
        "path": str(path),
        "rating_score": float(score),
        "updated_utc": datetime.utcnow().isoformat() + "Z",
        "note": "Generated by Image Duel Ranker (Elo)."
    }, indent=2), encoding="utf-8")

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
        except Exception as e:
            print(f"[warn] EXIF embed failed for {path.name}: {e}")

def record_result(conn, a, b, winner):
    a_id, a_path, a_folder, a_duels, a_score, _a_wins_cur, _a_losses_cur = a
    b_id, b_path, b_folder, b_duels, b_score, _b_wins_cur, _b_losses_cur = b

    a_wins = b_wins = 0
    a_losses = b_losses = 0
    w_id = None

    if winner == "a":
        new_a, new_b = elo_update(a_score, b_score, True)
        w_id, a_wins, b_losses = a_id, 1, 1
    elif winner == "b":
        new_a, new_b = elo_update(a_score, b_score, False)
        w_id, b_wins, a_losses = b_id, 1, 1
    elif winner == "downvote":
        new_a, new_b = a_score - DOWNVOTE_PENALTY, b_score - DOWNVOTE_PENALTY
        a_losses, b_losses = 1, 1
    else:  # draw/skip
        new_a, new_b = elo_update(a_score, b_score, None)

    ts = int(time.time())
    cur = conn.cursor()
    cur.execute("UPDATE images SET score=?, duels=duels+1, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
                (new_a, a_wins, a_losses, ts, a_id))
    cur.execute("UPDATE images SET score=?, duels=duels+1, wins=wins+?, losses=losses+?, last_seen=? WHERE id=?",
                (new_b, b_wins, b_losses, ts, b_id))
    cur.execute("INSERT INTO comparisons(left_id, right_id, chosen_id, ts) VALUES (?,?,?,?)",
                (a_id, b_id, w_id, ts))
    conn.commit()

    print(f"[result] stored: winner={winner} | {Path(a_path).name} vs {Path(b_path).name}")

    threading.Thread(target=update_image_metadata, args=(Path(a_path), new_a), daemon=True).start()
    threading.Thread(target=update_image_metadata, args=(Path(b_path), new_b), daemon=True).start()

def set_image_hidden(conn, row, hidden: int):
    img_id, img_path = row[0], row[1]
    conn.execute("UPDATE images SET hidden=?, last_seen=? WHERE id=?", (hidden, int(time.time()), img_id))
    conn.commit()
    action = "unhide" if hidden == 0 else "hide"
    print(f"[{action}] set hidden={hidden}: {img_path}")

def hide_image(conn, row):
    set_image_hidden(conn, row, 1)

def unhide_image(conn, row):
    set_image_hidden(conn, row, 0)

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

class VideoPlayer:
    """Tkinter video playback (frames only, no audio).

    - Starts paused on the first frame.
    - Uses imageio (ffmpeg backend) if available.
    - Playback is best-effort; if decoding fails, falls back to a placeholder.
    """

    def __init__(self, root: tk.Tk, widget: tk.Label, path: str, target_size: tuple[int, int]):
        self.root = root
        self.widget = widget
        self.path = path
        self.target_size = target_size

        self.reader = None
        self.iter = None
        self.fps = 24.0
        self.delay_ms = 42

        self.after_job = None
        self.paused = True
        self.ended = False

    def _open(self) -> bool:
        if imageio is None:
            return False
        try:
            self.reader = imageio.get_reader(self.path)
            meta = {}
            try:
                meta = self.reader.get_meta_data() or {}
            except Exception:
                meta = {}
            fps = meta.get("fps")
            if isinstance(fps, (int, float)) and fps and fps > 0:
                self.fps = float(fps)
            self.fps = max(5.0, min(60.0, self.fps))
            self.delay_ms = int(1000.0 / self.fps)
            self.iter = self.reader.iter_data()
            self.ended = False
            return True
        except Exception:
            self.reader = None
            self.iter = None
            return False

    def close(self):
        self._cancel()
        try:
            if self.reader:
                self.reader.close()
        except Exception:
            pass
        self.reader = None
        self.iter = None
        self.paused = True
        self.ended = False

    def _cancel(self):
        if self.after_job:
            try:
                self.root.after_cancel(self.after_job)
            except Exception:
                pass
            self.after_job = None

    def _display_frame(self, frame) -> bool:
        try:
            im = Image.fromarray(frame)
        except Exception:
            return False
        if im.mode not in ("RGB", "RGBA"):
            im = im.convert("RGB")
        im.thumbnail(self.target_size, Image.Resampling.LANCZOS)
        tk_im = ImageTk.PhotoImage(im)
        self.widget.configure(image=tk_im, text="", bg=DARK_PANEL, borderwidth=0, highlightthickness=0)
        self.widget.image = tk_im
        return True

    def show_first_frame(self) -> bool:
        # Always reopen to guarantee frame 0 and reset end-state
        self.close()
        if not self._open():
            return False
        try:
            frame = next(self.iter)
        except Exception:
            self.close()
            return False
        ok = self._display_frame(frame)
        self.paused = True
        return ok

    def toggle(self):
        if self.reader is None or self.iter is None:
            if not self.show_first_frame():
                return

        if self.ended:
            # restart from beginning on next play
            if not self.show_first_frame():
                return
            self.ended = False

        if self.paused:
            self.paused = False
            self._schedule(0)
        else:
            self.paused = True
            self._cancel()

    def _schedule(self, delay_ms: int):
        self._cancel()
        self.after_job = self.root.after(delay_ms, self.step)

    def step(self):
        if self.paused:
            return
        if self.reader is None or self.iter is None:
            self.paused = True
            return
        try:
            frame = next(self.iter)
        except StopIteration:
            self.paused = True
            self.ended = True
            self._cancel()
            return
        except Exception:
            self.paused = True
            self.ended = True
            self._cancel()
            return

        if not self._display_frame(frame):
            self.paused = True
            self.ended = True
            self._cancel()
            return

        self._schedule(self.delay_ms)

class App:
    def __init__(self, root, conn):
        self.root = root
        self.conn = conn
        self.current = None
        self.prev_artists = deque(maxlen=4)
        self.page = 0
        self.metric = LEADERBOARD_METRIC_DEFAULT
        self._last_ranks = {r['folder']: r['rank'] for r in folder_leaderboard(self.conn, metric=self.metric)}
        self._resize_job = None
        self._sidebar_width_px = 420  # set precisely on first sidebar build

        root.title("Image Duel Ranker")
        root.geometry(f"{WINDOW_SIZE[0]}x{WINDOW_SIZE[1]}")
        root.configure(bg=DARK_BG)

        # ----- Main containers (no draggable splitters) -----
        self.container = tk.Frame(root, bg=DARK_BG)
        self.container.pack(fill="both", expand=True)

        # left: images area (expands)
        self.images_frame = tk.Frame(self.container, bg=DARK_BG)
        self.images_frame.pack(side="left", fill="both", expand=True)

        self.left_panel  = tk.Label(self.images_frame,  bd=0, bg=DARK_PANEL, cursor="hand2")
        self.right_panel = tk.Label(self.images_frame,  bd=0, bg=DARK_PANEL, cursor="hand2")
        self.left_panel.pack(side="left",  fill="both", expand=True, padx=(6,3), pady=6)
        self.right_panel.pack(side="left", fill="both", expand=True, padx=(3,6), pady=6)

        # right: sidebar (fixed width)
        self.sidebar = tk.Frame(self.container, bg=DARK_BG, bd=0, highlightthickness=0)

        # ---- Pool filter ----
        self.pool_filter_var = tk.StringVar(value="All")
        self.pool_filter_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.pool_filter_label = tk.Label(self.pool_filter_row, text="Pool:", font=("Segoe UI", 9),
                                          fg=TEXT_COLOR, bg=DARK_BG)
        self.pool_filter_label.pack(side="left")
        self.pool_filter_menu = tk.OptionMenu(self.pool_filter_row, self.pool_filter_var, *POOL_FILTER_OPTIONS,
                                             command=self.on_pool_filter_change)
        self.pool_filter_menu.configure(bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                        relief="flat", highlightthickness=0)
        try:
            self.pool_filter_menu["menu"].configure(bg=DARK_PANEL, fg=TEXT_COLOR)
        except Exception:
            pass
        self.pool_filter_menu.pack(side="right", fill="x", expand=True, padx=(8, 0))


        # -------------------- Mouse controls --------------------
        self.left_panel.bind("<Button-1>",  lambda e: self.choose("a"))
        self.right_panel.bind("<Button-1>", lambda e: self.choose("b"))
        self.left_panel.bind("<Control-Button-1>",  lambda e: (self.toggle_video("a") or "break"))
        self.right_panel.bind("<Control-Button-1>", lambda e: (self.toggle_video("b") or "break"))
        self.left_panel.bind("<Double-Button-1>", self.open_left)
        self.right_panel.bind("<Double-Button-1>", self.open_right)
        self.left_panel.bind("<Button-3>",  lambda e: self.choose("downvote"))
        self.right_panel.bind("<Button-3>", lambda e: self.choose("downvote"))
        self.left_panel.bind("<Button-2>",  lambda e: self.hide("a"))
        self.right_panel.bind("<Button-2>", lambda e: self.hide("b"))

        # -------------------- Sidebar widgets --------------------
        self.leader_header = tk.Label(self.sidebar, text="Top Artists",
                                      font=("Segoe UI", 12, "bold"), fg=ACCENT, bg=DARK_BG)
        self.metric_label  = tk.Label(self.sidebar, text="", font=("Segoe UI", 9),
                                      fg=TEXT_COLOR, bg=DARK_BG)
        self.page_label    = tk.Label(self.sidebar, text="", font=("Segoe UI", 9),
                                      fg=TEXT_COLOR, bg=DARK_BG)

        self.board = tk.Text(self.sidebar, height=28, font=("Consolas", 10),
                             bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                             relief="flat", wrap="none")
        self.nav_row = tk.Frame(self.sidebar, bg=DARK_BG)
        self.btn_prev = tk.Button(self.nav_row, text="◀ Prev [", width=10,
                                  command=lambda: self.change_page(-1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                  relief="flat")
        self.btn_next = tk.Button(self.nav_row, text="Next ] ▶", width=10,
                                  command=lambda: self.change_page(+1),
                                  bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                  relief="flat")
        self.btn_prev.pack(side="left", padx=(0,6))
        self.btn_next.pack(side="right")

        self.now_header = tk.Label(self.sidebar, text="Current / Previous",
                                   font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.now = tk.Label(self.sidebar, text="", justify="left", font=("Segoe UI", 10),
                            fg=TEXT_COLOR, bg=DARK_BG)


        self.stats_header = tk.Label(self.sidebar, text="Counters",
                                     font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.stats = tk.Label(self.sidebar, text="", justify="left", font=("Consolas", 9),
                              fg=TEXT_COLOR, bg=DARK_BG)

        self.links_header = tk.Label(self.sidebar, text="Links",
                                     font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.link_left = tk.Label(self.sidebar, text="Left e621: (n/a)", fg=LINK_COLOR,
                                  bg=DARK_BG, cursor="hand2", font=("Consolas", 9), justify="left")
        self.link_right = tk.Label(self.sidebar, text="Right e621: (n/a)", fg=LINK_COLOR,
                                   bg=DARK_BG, cursor="hand2", font=("Consolas", 9), justify="left")
        self.link_left.url = ""
        self.link_right.url = ""
        self.link_left.bind("<Button-1>",  lambda e, w=self.link_left:  self._open_url(w.url))
        self.link_right.bind("<Button-1>", lambda e, w=self.link_right: self._open_url(w.url))

        # ---- Keys table (4 columns: key | bind | key | bind) ----
        self.search_header = tk.Label(self.sidebar, text="Search tags",
                                      font=("Segoe UI", 11, "bold"), fg=ACCENT, bg=DARK_BG)
        self.common_tags_entry = tk.Entry(self.sidebar, font=("Consolas", 9),
                                          bg=DARK_PANEL, fg=TEXT_COLOR, insertbackground=TEXT_COLOR,
                                          relief="flat")
        self.common_tags_entry.insert(0, DEFAULT_COMMON_TAGS)

        self.export_links_btn = tk.Button(self.sidebar, text="Export e621 links (clipboard + file)",
                                          command=self.export_e621_links,
                                          bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                          relief="flat")

        self.view_links_btn = tk.Button(self.sidebar, text="View/open e621 links",
                                        command=self.show_links_view,
                                        bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                        relief="flat")

        # Links viewer window state
        self._links_window = None
        self._links_listbox = None
        self._links_count_label = None
        self._links_common_label = None
        self._links_status_label = None
        self._links_open_cancel = False
        self.export_status = tk.Label(self.sidebar, text="", font=("Segoe UI", 9),
                                      fg=TEXT_COLOR, bg=DARK_BG)

        self.db_stats_btn = tk.Button(self.sidebar, text="DB stats",
                                     command=self.show_db_stats,
                                     bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT,
                                     relief="flat")

        self.keys_table = tk.Frame(self.sidebar, bg=DARK_PANEL, bd=1, relief="solid")

        # keybinds
        root.bind("1", lambda e: self.choose("a"))
        root.bind("2", lambda e: self.choose("b"))
        root.bind("<Control-Key-1>", lambda e: self.toggle_video("a"))
        root.bind("<Control-Key-2>", lambda e: self.toggle_video("b"))
        root.bind("3", lambda e: self.choose("downvote"))
        root.bind("x", lambda e: self.hide("a"))
        root.bind("m", lambda e: self.hide("b"))
        root.bind("0", lambda e: self.choose(None))
        root.bind("<space>", lambda e: self.choose(None))
        root.bind("q", lambda e: self.quit())

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

        root.bind("<Configure>", self._on_configure)

        self.load_duel()

    # -------- window resize only refreshes images -------
    def _on_configure(self, event=None):
        if self._resize_job:
            try:
                self.root.after_cancel(self._resize_job)
            except Exception:
                pass
        self._resize_job = self.root.after(120, self._refresh_images)

    # ---------- core flow ----------

    def on_pool_filter_change(self, value=None):
        # When filter changes, start a fresh duel from the new pool.
        try:
            self.page = 0
        except Exception:
            pass
        # Clear any export status noise
        try:
            self.export_status.configure(text="")
        except Exception:
            pass
        self.load_duel()

    def _media_kind(self, path: str) -> str:
        ext = Path(path).suffix.lower()
        if ext in VIDEO_EXTS:
            return "video"
        if ext in GIF_EXTS:
            return "gif"
        if ext in IMAGE_EXTS:
            return "image"
        return "other"

    def _row_matches_filter(self, row) -> bool:
        # row: (id, path, folder, duels, score, wins, losses)
        kind = self._media_kind(row[1])
        f = (self.pool_filter_var.get() or "All").strip()
        if f == "All":
            return kind in ("image", "gif", "video")
        if f == "Images":
            return kind == "image"
        if f == "GIFs":
            return kind == "gif"
        if f == "Videos":
            return kind == "video"
        if f == "Animated":
            return kind in ("gif", "video")
        if f == "Hidden":
            return kind in ("image", "gif", "video")
        return kind in ("image", "gif", "video")

    def _pool_rows(self):
        f = (self.pool_filter_var.get() or "All").strip()
        if f == "Hidden":
            q = "SELECT id, path, folder, duels, score, wins, losses FROM images WHERE hidden=1"
        else:
            q = "SELECT id, path, folder, duels, score, wins, losses FROM images WHERE hidden=0"
        rows = list(self.conn.execute(q))
        rows = [r for r in rows if self._row_matches_filter(r)]
        return rows

    def pick_one(self, exclude_ids=None):
        exclude_ids = set(exclude_ids or [])
        rows = [r for r in self._pool_rows() if r[0] not in exclude_ids]
        if not rows:
            return None
        return random.choice(rows)

    def pick_two(self):
        rows = self._pool_rows()
        if len(rows) < 2:
            return None, None
        a = random.choice(rows)
        b = random.choice(rows)
        while b[0] == a[0]:
            b = random.choice(rows)
        return a, b
    def load_duel(self):
        a, b = self.pick_two()
        if not a or not b:
            print("[duel] not enough visible images (need at least 2).")
            self.quit()
            return

        self.current = (a, b)
        self.prev_artists.appendleft(a[2])
        self.prev_artists.appendleft(b[2])

        print("[duel] showing:")
        print("  LEFT: ", a[1], f"(score={a[4]:.2f}, duels={a[3]}, W={a[5]}, L={a[6]})")
        print("  RIGHT:", b[1], f"(score={b[4]:.2f}, duels={b[3]}, W={b[5]}, L={b[6]})")

        self._render_media(self.left_panel, a[1])
        self._render_media(self.right_panel, b[1])

        self.update_sidebar(a[2], b[2])
        self.root.after(50, self._refresh_images)

    # ---------- image display (with GIF support) ----------
    def _render_media(self, widget, path):
        # Stop any prior GIF animation
        if hasattr(widget, "_anim_job") and widget._anim_job:
            try:
                self.root.after_cancel(widget._anim_job)
            except Exception:
                pass
            widget._anim_job = None

        # Stop any prior video playback
        if hasattr(widget, "_video_player") and widget._video_player:
            try:
                widget._video_player.close()
            except Exception:
                pass
            widget._video_player = None

        self.root.update_idletasks()
        w = max(1, widget.winfo_width())
        h = max(1, widget.winfo_height())
        if w <= 5 or h <= 5:
            self.root.after(50, lambda: self._render_media(widget, path))
            return

        target = (max(100, w - 12), max(100, h - 12))
        ext = Path(path).suffix.lower()

        # --- Videos: show first frame (paused), allow play/pause ---
        if ext in VIDEO_EXTS:
            wrap = max(100, w - 24)
            name = Path(path).name

            if imageio is None:
                widget.configure(
                    image="",
                    text=f"[VIDEO]\n{name}\n\n(Install for preview)\npy -m pip install imageio imageio-ffmpeg",
                    fg=TEXT_COLOR,
                    bg=DARK_PANEL,
                    justify="center",
                    font=("Consolas", 11),
                    wraplength=wrap,
                    borderwidth=0,
                    highlightthickness=0,
                )
                widget.image = None
                return

            vp = VideoPlayer(self.root, widget, path, target)
            if vp.show_first_frame():
                widget._video_player = vp
                return

            # Fallback placeholder if decode fails
            widget.configure(
                image="",
                text=f"[VIDEO]\n{name}\n\n(Preview unavailable)\n(Double-click to open)",
                fg=TEXT_COLOR,
                bg=DARK_PANEL,
                justify="center",
                font=("Consolas", 11),
                wraplength=wrap,
                borderwidth=0,
                highlightthickness=0,
            )
            widget.image = None
            return

        # Images / GIFs
        try:
            widget.configure(text="")
        except Exception:
            pass
        self._render_img(widget, path)

    def _render_img(self, widget, path):
        if hasattr(widget, "_anim_job") and widget._anim_job:
            try:
                self.root.after_cancel(widget._anim_job)
            except Exception:
                pass
            widget._anim_job = None

        self.root.update_idletasks()
        w = max(1, widget.winfo_width())
        h = max(1, widget.winfo_height())
        if w <= 5 or h <= 5:
            self.root.after(50, lambda: self._render_img(widget, path))
            return
        target = (max(100, w - 12), max(100, h - 12))

        im = Image.open(path)
        is_animated = getattr(im, "is_animated", False) and getattr(im, "n_frames", 1) > 1

        if not is_animated:
            try: im.seek(0)
            except Exception: pass
            if im.mode not in ("RGB", "RGBA"):
                im = im.convert("RGB")
            im.thumbnail(target, Image.Resampling.LANCZOS)
            tk_im = ImageTk.PhotoImage(im)
            widget.configure(image=tk_im, bg=DARK_PANEL, borderwidth=0, highlightthickness=0)
            widget.image = tk_im
            return

        frames, delays = [], []
        try:
            for frame in ImageSequence.Iterator(im):
                delay = frame.info.get("duration", im.info.get("duration", 100))
                delays.append(delay)
                fr = frame.convert("RGBA") if frame.mode != "RGBA" else frame.copy()
                fr.thumbnail(target, Image.Resampling.LANCZOS)
                frames.append(ImageTk.PhotoImage(fr))
        except Exception:
            im.seek(0)
            if im.mode not in ("RGB", "RGBA"):
                im = im.convert("RGB")
            im.thumbnail(target, Image.Resampling.LANCZOS)
            tk_im = ImageTk.PhotoImage(im)
            widget.configure(image=tk_im, bg=DARK_PANEL, borderwidth=0, highlightthickness=0)
            widget.image = tk_im
            return

        widget._anim_frames = frames
        widget._anim_delays = delays
        widget._anim_index  = 0

        def step():
            if not getattr(widget, "_anim_frames", None):
                return
            idx = widget._anim_index % len(widget._anim_frames)
            widget.configure(image=widget._anim_frames[idx], bg=DARK_PANEL, borderwidth=0, highlightthickness=0)
            widget.image = widget._anim_frames[idx]
            widget._anim_index = (idx + 1) % len(widget._anim_frames)
            delay = max(20, int(widget._anim_delays[idx] if idx < len(widget._anim_delays) else 100))
            widget._anim_job = self.root.after(delay, step)

        widget._anim_job = self.root.after(0, step)

    def _refresh_images(self):
        if self.current:
            a, b = self.current
            self._render_media(self.left_panel, a[1])
            self._render_media(self.right_panel, b[1])

    # ---------- sidebar ----------
    def _metric_human(self):
        return {
            "avg": "Simple Avg",
            "shrunken_avg": f"Shrunken Avg (prior={FOLDER_PRIOR_IMAGES})",
            "lcb": f"Lower Conf. Bound (z={LCB_Z})"
        }.get(self.metric, self.metric)

    def toggle_metric(self):
        order = ["shrunken_avg", "avg", "lcb"]
        i = order.index(self.metric) if self.metric in order else 0
        self.metric = order[(i + 1) % len(order)]
        print("[metric] leaderboard metric changed to:", self.metric)
        self._last_ranks = {r['folder']: r['rank'] for r in folder_leaderboard(self.conn, metric=self.metric)}
        if self.current:
            self.update_sidebar(self.current[0][2], self.current[1][2])

    def change_page(self, delta):
        leader = folder_leaderboard(self.conn, metric=self.metric)
        total_pages = max(1, math.ceil(len(leader) / LEADERBOARD_SIZE))
        self.page = (self.page + delta) % total_pages
        if self.current:
            self.update_sidebar(self.current[0][2], self.current[1][2])

    def _format_delta(self, folder, leader):
        old = self._last_ranks.get(folder)
        now, _, _ = find_folder_rank(leader, folder)
        if not now: return ""
        if old is None: return " (new)"
        d = old - now
        return f"  ↑{d}" if d > 0 else (f"  ↓{abs(d)}" if d < 0 else "  →0")

    def _build_lines_all(self, leader):
        def trunc(name: str) -> str:
            return name if len(name) <= LEAF_MAX else (name[:LEAF_MAX - 1] + "…")
        out = []
        for row in leader:
            leaf = trunc(Path(row['folder']).name)
            if self.metric == "avg":
                out.append(f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['avg']:6.1f}  (n={row['n']})")
            elif self.metric == "shrunken_avg":
                out.append(f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']})")
            else:
                out.append(f"{row['rank']:>3}. {leaf:<{LEAF_MAX}} {row['score']:6.1f}  avg={row['avg']:5.1f} (n={row['n']})")
        return out

    def _ensure_sidebar_width(self, lines_all):
        f = tkfont.Font(family="Consolas", size=10)
        max_px = max((f.measure(s) for s in lines_all), default=320)
        need_px = max(300, min(700, max_px + 32))
        self._sidebar_width_px = int(need_px)

        self.sidebar.pack_forget()
        self.sidebar.pack(side="right", fill="y", padx=(0,6), pady=6)
        self.sidebar.configure(width=self._sidebar_width_px)
        self.sidebar.pack_propagate(False)

        char_w = max(1, f.measure("M"))
        self.board.configure(width=int((self._sidebar_width_px - 24) / char_w))

    def _build_keys_table(self):
        # Clear existing
        for w in self.keys_table.winfo_children():
            w.destroy()

        hdr_font    = ("Segoe UI", 9, "bold")
        key_font    = ("Consolas", 9)
        action_font = ("Segoe UI", 9)

        def header(col, text):
            lbl = tk.Label(
                self.keys_table,
                text=text,
                font=hdr_font,
                fg=ACCENT,
                bg=DARK_PANEL,
                anchor="w",
            )
            lbl.grid(row=0, column=col, sticky="we", padx=(8 if col in (0, 2) else 6), pady=(6, 3))

        header(0, "Key"); header(1, "Action"); header(2, "Key"); header(3, "Action")

        rows = [
            ("L-Click image",    "Pick clicked",        "1",        "Pick LEFT"),
            ("R-Click image",    "Downvote both",       "2",        "Pick RIGHT"),
            ("M-Click image",    "Hide clicked",        "3",        "Downvote both"),
            ("Dbl-Click image",  "Open clicked",        "X",        "Hide LEFT"),
            ("0 / Space",        "Skip/tie",            "M",        "Hide RIGHT"),
            ("Ctrl+1",           "Play/Pause video LEFT", "Ctrl+2",   "Play/Pause video RIGHT"),
            ("O",                "Open LEFT image",     "P",        "Open RIGHT image"),
            ("Shift+O",          "Reveal LEFT folder",  "Shift+P",  "Reveal RIGHT folder"),
            ("[ / PgUp",         "Prev page",           "] / PgDn", "Next page"),
            ("T",                "Toggle metric",       "G",        "Export e621 links"),
            ("V",                "Links viewer",        "I",        "DB stats"),
            ("Q",                "Quit",                "",         ""),
        ]

        for r, (k1, a1, k2, a2) in enumerate(rows, start=1):
            lbl_k1 = tk.Label(self.keys_table, text=k1, font=key_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w")
            lbl_k1.grid(row=r, column=0, sticky="we", padx=(8, 6))

            lbl_a1 = tk.Label(self.keys_table, text=a1, font=action_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w")
            lbl_a1.grid(row=r, column=1, sticky="we", padx=(6, 12))

            lbl_k2 = tk.Label(self.keys_table, text=k2, font=key_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w")
            lbl_k2.grid(row=r, column=2, sticky="we", padx=(8, 6))

            lbl_a2 = tk.Label(self.keys_table, text=a2, font=action_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w")
            lbl_a2.grid(row=r, column=3, sticky="we", padx=(6, 8))

        # Compact layout: keep keys tight; let action columns expand
        self.keys_table.grid_columnconfigure(0, weight=0)
        self.keys_table.grid_columnconfigure(1, weight=1)
        self.keys_table.grid_columnconfigure(2, weight=0)
        self.keys_table.grid_columnconfigure(3, weight=1)

    def update_sidebar(self, folder_left, folder_right):
        leader = folder_leaderboard(self.conn, metric=self.metric)
        total = len(leader)
        total_pages = max(1, math.ceil(len(leader) / LEADERBOARD_SIZE))
        self.page = min(self.page, total_pages - 1)
        start = self.page * LEADERBOARD_SIZE
        end = min(start + LEADERBOARD_SIZE, total)

        lines_all = self._build_lines_all(leader)
        self._ensure_sidebar_width(lines_all)

        for w in (self.leader_header, self.metric_label, self.page_label,
                  self.pool_filter_row,
                  self.board, self.nav_row, self.now_header, self.now,
                  self.stats_header, self.stats,
                  self.links_header, self.link_left, self.link_right,
                  self.search_header, self.common_tags_entry, self.export_links_btn,
                  self.view_links_btn, self.export_status, self.db_stats_btn, self.keys_table):
            w.pack_forget()

        self.leader_header.pack(anchor="w")
        self.metric_label.configure(text=f"[Metric: {self._metric_human()}]")
        self.metric_label.pack(anchor="w")
        self.pool_filter_row.pack(fill="x", pady=(2, 4))
        self.page_label.configure(text=f"Page {self.page+1}/{total_pages}  (total {total})")
        self.page_label.pack(anchor="e", pady=(0,4))

        # leaderboard page
        def trunc(name: str) -> str:
            return name if len(name) <= LEAF_MAX else (name[:LEAF_MAX - 1] + "…")
        lines = []
        for row in leader[start:end]:
            leaf = trunc(Path(row['folder']).name)
            marker = "  ◀" if row['folder'] in {folder_left, folder_right} else ""
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
        self.board.pack(fill="x", pady=(4, 6))

        self.nav_row.pack(fill="x", pady=(0, 6))

        self.now_header.pack(anchor="w")
        l_rank, l_avg, l_n = find_folder_rank(leader, folder_left)
        r_rank, r_avg, r_n = find_folder_rank(leader, folder_right)
        left_leaf = Path(folder_left).name
        right_leaf = Path(folder_right).name

        l_line = f"Left:  #{l_rank} {left_leaf} — {l_avg:.1f} (n={l_n}){self._format_delta(folder_left, leader)}" if l_rank else f"Left:  {left_leaf} — (unranked)"
        r_line = f"Right: #{r_rank} {right_leaf} — {r_avg:.1f} (n={r_n}){self._format_delta(folder_right, leader)}" if r_rank else f"Right: {right_leaf} — (unranked)"

        prev_display = []
        seen = {folder_left, folder_right}
        for f in self.prev_artists:
            if f in seen:
                continue
            seen.add(f)
            pr, pa, pn = find_folder_rank(leader, f)
            leaf = Path(f).name
            if pr:
                prev_display.append(f"• Prev: #{pr} {leaf} — {pa:.1f} (n={pn}){self._format_delta(f, leader)}")
            else:
                prev_display.append(f"• Prev: {leaf} — (unranked)")
            if len(prev_display) >= 2:
                break

        self.now.configure(text="\n".join([l_line, r_line] + prev_display))
        self.now.pack(anchor="w", pady=(2, 6))

        # Counters (helps verify whether the DB has meaningful history)
        if self.current:
            a, b = self.current

            def folder_totals(folder: str):
                row = self.conn.execute(
                    "SELECT COUNT(*), COALESCE(SUM(duels),0), COALESCE(SUM(wins),0), COALESCE(SUM(losses),0) "
                    "FROM images WHERE folder=?",
                    (folder,),
                ).fetchone()
                n = int(row[0] or 0)
                shown = int(row[1] or 0)
                wins = int(row[2] or 0)
                losses = int(row[3] or 0)
                return n, shown, wins, losses

            ln, lshown, lw, ll = folder_totals(folder_left)
            rn, rshown, rw, rl = folder_totals(folder_right)
            ldec = lw + ll
            rdec = rw + rl

            stats_lines = [
                f"L img: shown={a[3]}  W={a[5]}  L={a[6]}  score={a[4]:.1f}",
                f"R img: shown={b[3]}  W={b[5]}  L={b[6]}  score={b[4]:.1f}",
                f"L artist: imgs={ln}  shown={lshown}  decisions={ldec}  (W={lw} L={ll})",
                f"R artist: imgs={rn}  shown={rshown}  decisions={rdec}  (W={rw} L={rl})",
            ]
        else:
            stats_lines = ["(no active duel)"]

        self.stats.configure(text="\n".join(stats_lines))
        self.stats_header.pack(anchor="w")
        self.stats.pack(anchor="w", pady=(2, 6))

        self.links_header.pack(anchor="w")
        if self.current:
            a, b = self.current
            left_url = e621_url_for_path(a[1]); right_url = e621_url_for_path(b[1])
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
        self.link_left.pack(anchor="w")
        self.link_right.pack(anchor="w", pady=(0, 6))

        self.search_header.pack(anchor="w")
        self.common_tags_entry.pack(fill="x", pady=(2, 6))
        self.export_links_btn.pack(fill="x", pady=(0, 2))
        self.view_links_btn.pack(fill="x", pady=(0, 6))
        self.export_status.pack(anchor="w", pady=(0, 6))
        self.db_stats_btn.pack(fill="x", pady=(0, 10))

        # Build keys table and make it match the sidebar width
        self._build_keys_table()
        self.keys_table.pack(side="bottom", fill="x", padx=0, pady=(0, 6))

    # ---------- actions ----------
    def choose(self, winner):
        prev = {r['folder']: r['rank'] for r in folder_leaderboard(self.conn, metric=self.metric)}
        a, b = self.current
        record_result(self.conn, a, b, winner)
        self._last_ranks = prev
        self.load_duel()

    def hide(self, which):
        if not self.current:
            return
        a, b = self.current
        victim = a if which == "a" else b
        survivor = b if which == "a" else a

        # In Hidden mode, M-click acts as "unhide"; otherwise it hides.
        f = (self.pool_filter_var.get() or "All").strip()
        if f == "Hidden":
            unhide_image(self.conn, victim)
        else:
            hide_image(self.conn, victim)

        # Replace only the removed side with a new random item from the current pool.
        replacement = self.pick_one(exclude_ids=[survivor[0], victim[0]])
        if not replacement:
            # Fallback: if we cannot find a replacement, reset the duel.
            self.load_duel()
            return

        if which == "a":
            self.current = (replacement, survivor)
            self.prev_artists.appendleft(replacement[2])
            self._render_media(self.left_panel, replacement[1])
        else:
            self.current = (survivor, replacement)
            self.prev_artists.appendleft(replacement[2])
            self._render_media(self.right_panel, replacement[1])

        self.update_sidebar(self.current[0][2], self.current[1][2])
        self.root.after(50, self._refresh_images)

    def _open_url(self, url):
        if url and url.startswith("http"):
            try: webbrowser.open(url)
            except Exception as e: print("[link] open failed:", e)

    def open_left(self, ev=None):
        if not self.current: return
        a, _ = self.current
        os.startfile(a[1])

    def open_right(self, ev=None):
        if not self.current: return
        _, b = self.current
        os.startfile(b[1])


    def toggle_video(self, which: str):
        """Toggle in-app playback for the given side ('a' or 'b').

        Only applies when that side is currently a video. Playback is frames-only (muted)
        and starts paused on the first frame.
        """
        widget = self.left_panel if which == "a" else self.right_panel
        vp = getattr(widget, "_video_player", None)

        if vp is None:
            if not self.current:
                return
            row = self.current[0] if which == "a" else self.current[1]
            path = row[1]
            if Path(path).suffix.lower() not in VIDEO_EXTS:
                return
            if imageio is None:
                return

            self.root.update_idletasks()
            w = max(1, widget.winfo_width())
            h = max(1, widget.winfo_height())
            target = (max(100, w - 12), max(100, h - 12))

            vp = VideoPlayer(self.root, widget, path, target)
            if not vp.show_first_frame():
                return
            widget._video_player = vp

        try:
            vp.toggle()
        except Exception:
            pass


    def reveal_left_folder(self, ev=None):
        if not self.current: return
        a, _ = self.current
        os.startfile(str(Path(a[1]).parent))

    def reveal_right_folder(self, ev=None):
        if not self.current: return
        _, b = self.current
        os.startfile(str(Path(b[1]).parent))

    def quit(self):
        print("[quit] closing UI")
        self.root.quit()


    def show_db_stats(self):
        """Show summary statistics to help verify whether the DB has been reset."""
        try:
            images_total = int(self.conn.execute("SELECT COUNT(*) FROM images").fetchone()[0] or 0)
            visible_total = int(self.conn.execute("SELECT COUNT(*) FROM images WHERE hidden=0").fetchone()[0] or 0)
            comps_total = int(self.conn.execute("SELECT COUNT(*) FROM comparisons").fetchone()[0] or 0)
            min_ts, max_ts = self.conn.execute("SELECT MIN(ts), MAX(ts) FROM comparisons").fetchone()
            sum_duels, sum_wins, sum_losses = self.conn.execute(
                "SELECT COALESCE(SUM(duels),0), COALESCE(SUM(wins),0), COALESCE(SUM(losses),0) FROM images"
            ).fetchone()

            sum_duels = int(sum_duels or 0)
            sum_wins = int(sum_wins or 0)
            sum_losses = int(sum_losses or 0)

            expected_sum_duels = comps_total * 2
            delta = sum_duels - expected_sum_duels

            def fmt_ts(ts):
                if not ts:
                    return "n/a"
                try:
                    return datetime.fromtimestamp(int(ts)).strftime("%Y-%m-%d %H:%M:%S")
                except Exception:
                    return str(ts)

            db_mtime = "n/a"
            try:
                db_mtime = datetime.fromtimestamp(DB_PATH.stat().st_mtime).strftime("%Y-%m-%d %H:%M:%S")
            except Exception:
                pass

            msg = (
                f"DB file: {DB_PATH}\n"
                f"DB modified: {db_mtime}\n\n"
                f"Images: {images_total} (visible: {visible_total})\n"
                f"Comparisons (duels): {comps_total}\n"
                f"First duel: {fmt_ts(min_ts)}\n"
                f"Last duel:  {fmt_ts(max_ts)}\n\n"
                f"Image counters total:\n"
                f"  shown (SUM duels): {sum_duels}\n"
                f"  decisions (SUM wins+losses): {sum_wins + sum_losses}  [W={sum_wins}, L={sum_losses}]\n\n"
                f"Consistency check:\n"
                f"  expected SUM duels ≈ comparisons*2 = {expected_sum_duels}\n"
                f"  actual   SUM duels = {sum_duels}\n"
                f"  delta           = {delta}\n\n"
                "Notes:\n"
                "• If 'Comparisons' is near 0 and you expected lots of history, the DB was likely replaced/reset.\n"
                "• 'shown' increases even on skips; 'decisions' only increases on wins/losses (including downvotes)."
            )
            try:
                messagebox.showinfo("DB stats", msg)
            except Exception:
                print(msg)
        except Exception as e:
            try:
                messagebox.showerror("DB stats failed", str(e))
            except Exception:
                print("[db] stats failed:", e)



    # ---------- e621 link export ----------
    def _parse_common_tags(self) -> list[str]:
        """Parse the common tags entry into a list of tags."""
        raw = self.common_tags_entry.get().strip() if hasattr(self, "common_tags_entry") else ""
        return [t for t in raw.split() if t.strip()]

    def _ranked_artist_tags(self) -> list[str]:
        """
        Best-effort artist tag source:
        - uses folder leaderboard order
        - converts folder leaf to a tag-like token (spaces -> underscores)
        """
        leader = folder_leaderboard(self.conn, metric=self.metric)
        out: list[str] = []
        seen = set()
        for row in leader:
            folder = row.get("folder", "")
            leaf = Path(folder).name.strip()
            if not leaf:
                continue
            tag = leaf.replace(" ", "_").strip()
            if tag.startswith("~"):
                tag = tag[1:]
            if not tag:
                continue
            tag_norm = tag.lower()
            if tag_norm in seen:
                continue
            seen.add(tag_norm)
            out.append(tag_norm)
        return out

    def _build_e621_urls(self, common_tags: list[str], artist_tags: list[str]) -> list[str]:
        """Build a list of e621 URLs respecting the 40-tag max."""
        max_total = 40
        max_artist = max_total - len(common_tags)
        if max_artist < 1:
            raise ValueError(f"Common tags use {len(common_tags)} tags; e621 max is {max_total}. Remove some common tags.")

        total = len(artist_tags)
        if total == 0:
            return []

        # Match your Excel logic: balanced groups, highest-ranked first
        num_groups = max(1, math.ceil(total / max_artist))
        items_per_group = max(1, math.ceil(total / num_groups))

        urls: list[str] = []
        for g in range(num_groups):
            chunk = artist_tags[g * items_per_group:(g + 1) * items_per_group]
            if not chunk:
                continue

            tags = list(common_tags) + [f"~{t}" for t in chunk[:max_artist]]
            tag_str = " ".join(tags)
            encoded = quote_plus(tag_str, safe="~()_-.'")
            urls.append(f"https://e621.net/posts?tags={encoded}")

        return urls

    def export_e621_links(self):
        """Write ranked e621 search URLs to e621_links.txt and copy to clipboard."""
        try:
            urls, common, artists = self._get_e621_urls()
        except Exception as e:
            msg = f"Export failed: {e}"
            print("[e621] " + msg)
            if hasattr(self, "export_status"):
                self.export_status.configure(text=msg)
            return

        if not urls:
            msg = "No artist tags found to export."
            print("[e621] " + msg)
            if hasattr(self, "export_status"):
                self.export_status.configure(text=msg)
            return

        out_path = SCRIPT_DIR / "e621_links.txt"
        try:
            out_path.write_text("\n".join(urls) + "\n", encoding="utf-8")
        except Exception as e:
            msg = f"Export failed writing file: {e}"
            print("[e621] " + msg)
            if hasattr(self, "export_status"):
                self.export_status.configure(text=msg)
            return

        clip_msg = ""
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(urls))
            self.root.update()
            clip_msg = "Copied to clipboard; "
        except Exception:
            pass

        msg = f"{clip_msg}wrote {len(urls)} link(s) to {out_path.name} (max 40 tags/search)."
        print("[e621] " + msg)
        if hasattr(self, "export_status"):
            self.export_status.configure(text=msg)


    def _get_e621_urls(self):
        """Return (urls, common_tags, artist_tags) for the current settings."""
        common = self._parse_common_tags()
        artists = self._ranked_artist_tags()
        urls = self._build_e621_urls(common, artists)
        return urls, common, artists

    def show_links_view(self):
        """Open a window that shows the generated e621 links and allows opening them."""
        try:
            urls, common, artists = self._get_e621_urls()
        except Exception as e:
            msg = f"Link generation failed: {e}"
            print("[e621] " + msg)
            if hasattr(self, "export_status"):
                self.export_status.configure(text=msg)
            try:
                messagebox.showerror("e621 link generation failed", msg)
            except Exception:
                pass
            return

        if self._links_window and self._links_window.winfo_exists():
            try:
                self._links_window.deiconify()
                self._links_window.lift()
                self._links_window.focus_force()
            except Exception:
                pass
        else:
            self._create_links_window()

        self._links_view_set_data(urls, common, len(artists))

    def _create_links_window(self):
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
            self._links_window = None
            self._links_listbox = None
            self._links_count_label = None
            self._links_common_label = None
            self._links_status_label = None

        win.protocol("WM_DELETE_WINDOW", on_close)

        info_frame = tk.Frame(win, bg=DARK_BG)
        info_frame.pack(fill="x", padx=10, pady=(10, 6))

        self._links_count_label = tk.Label(
            info_frame, text="Links: 0", font=("Segoe UI", 10, "bold"),
            fg=ACCENT, bg=DARK_BG, anchor="w"
        )
        self._links_count_label.pack(side="left", fill="x", expand=True)

        self._links_common_label = tk.Label(
            info_frame, text="", font=("Consolas", 9),
            fg=TEXT_COLOR, bg=DARK_BG, anchor="e", justify="right"
        )
        self._links_common_label.pack(side="right")

        btn_frame = tk.Frame(win, bg=DARK_BG)
        btn_frame.pack(fill="x", padx=10, pady=(0, 8))

        btn_refresh = tk.Button(
            btn_frame, text="Refresh", command=self._links_view_refresh,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )
        btn_copy = tk.Button(
            btn_frame, text="Copy all", command=self._links_view_copy_all,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )
        btn_open_sel = tk.Button(
            btn_frame, text="Open selected", command=self._links_view_open_selected,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )
        btn_open_all = tk.Button(
            btn_frame, text="Open all", command=self._links_view_open_all,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )
        btn_stop = tk.Button(
            btn_frame, text="Stop opening", command=self._links_view_stop_opening,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )
        btn_open_file = tk.Button(
            btn_frame, text="Open links file", command=self._links_view_open_file,
            bg=DARK_PANEL, fg=TEXT_COLOR, activebackground=ACCENT, relief="flat"
        )

        for b in (btn_refresh, btn_copy, btn_open_sel, btn_open_all, btn_stop, btn_open_file):
            b.pack(side="left", padx=(0, 8))

        list_frame = tk.Frame(win, bg=DARK_BG)
        list_frame.pack(fill="both", expand=True, padx=10, pady=(0, 8))

        # Use grid here so the horizontal scrollbar spans the full width and behaves reliably.
        list_frame.grid_rowconfigure(0, weight=1)
        list_frame.grid_columnconfigure(0, weight=1)

        yscroll = tk.Scrollbar(list_frame, orient="vertical")
        xscroll = tk.Scrollbar(list_frame, orient="horizontal")

        lb = tk.Listbox(
            list_frame, font=("Consolas", 9),
            bg=DARK_PANEL, fg=TEXT_COLOR, selectbackground=ACCENT,
            activestyle="none",
            yscrollcommand=yscroll.set, xscrollcommand=xscroll.set
        )
        yscroll.config(command=lb.yview)
        xscroll.config(command=lb.xview)

        lb.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="we")

        lb.bind("<Double-Button-1>", lambda e: self._links_view_open_selected())

        self._links_listbox = lb

        self._links_status_label = tk.Label(
            win, text="", font=("Segoe UI", 9),
            fg=TEXT_COLOR, bg=DARK_BG, anchor="w", justify="left"
        )
        self._links_status_label.pack(fill="x", padx=10, pady=(0, 10))

    def _links_view_set_data(self, urls: list[str], common_tags: list[str], artist_count: int):
        if not (self._links_window and self._links_window.winfo_exists() and self._links_listbox):
            return

        self._links_listbox.delete(0, "end")
        for u in urls:
            self._links_listbox.insert("end", u)

        # Ensure the view starts at the left/top after refresh (helps when long URLs are present).
        try:
            self._links_listbox.yview_moveto(0.0)
            self._links_listbox.xview_moveto(0.0)
        except Exception:
            pass

        if self._links_count_label:
            self._links_count_label.configure(text=f"Links: {len(urls)}   (artists: {artist_count})")

        common_str = " ".join(common_tags) if common_tags else "(none)"
        common_display = (common_str[:137] + "...") if len(common_str) > 140 else common_str
        if self._links_common_label:
            self._links_common_label.configure(text=f"Common tags: {common_display}")

        if self._links_status_label:
            self._links_status_label.configure(text="")

    def _links_view_refresh(self):
        try:
            urls, common, artists = self._get_e621_urls()
            self._links_view_set_data(urls, common, len(artists))
        except Exception as e:
            try:
                messagebox.showerror("Refresh failed", str(e))
            except Exception:
                pass

    def _links_view_get_urls(self) -> list[str]:
        if not self._links_listbox:
            return []
        return [self._links_listbox.get(i) for i in range(self._links_listbox.size())]

    def _links_view_get_selected_urls(self) -> list[str]:
        if not self._links_listbox:
            return []
        sel = list(self._links_listbox.curselection())
        if not sel:
            try:
                idx = int(self._links_listbox.index("active"))
                if 0 <= idx < self._links_listbox.size():
                    sel = [idx]
            except Exception:
                sel = []
        return [self._links_listbox.get(i) for i in sel]

    def _links_view_open_selected(self):
        urls = self._links_view_get_selected_urls()
        if not urls:
            try:
                messagebox.showinfo("Open selected", "Select a link first.")
            except Exception:
                pass
            return
        self._open_urls_staggered(urls)

    def _links_view_open_all(self):
        urls = self._links_view_get_urls()
        if not urls:
            try:
                messagebox.showinfo("Open all", "No links to open.")
            except Exception:
                pass
            return
        try:
            ok = messagebox.askyesno("Open all links", f"This will open {len(urls)} browser tab(s). Continue?")
        except Exception:
            ok = True
        if not ok:
            return
        self._open_urls_staggered(urls)

    def _links_view_stop_opening(self):
        self._links_open_cancel = True
        if self._links_status_label:
            self._links_status_label.configure(text="Stopped.")

    def _open_urls_staggered(self, urls: list[str], delay_ms: int = 150):
        self._links_open_cancel = False
        total = len(urls)

        def step(i: int):
            if self._links_open_cancel:
                return
            if i >= total:
                if self._links_status_label:
                    self._links_status_label.configure(text=f"Opened {total} link(s).")
                return

            url = urls[i]
            try:
                webbrowser.open(url)
            except Exception as e:
                print("[link] open failed:", e)

            if self._links_status_label:
                self._links_status_label.configure(text=f"Opening {i+1}/{total}...")

            self.root.after(delay_ms, lambda: step(i + 1))

        step(0)

    def _links_view_copy_all(self):
        urls = self._links_view_get_urls()
        if not urls:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("\n".join(urls))
            self.root.update()
            if self._links_status_label:
                self._links_status_label.configure(text=f"Copied {len(urls)} link(s) to clipboard.")
        except Exception as e:
            try:
                messagebox.showerror("Copy failed", str(e))
            except Exception:
                pass

    def _links_view_open_file(self):
        out_path = SCRIPT_DIR / "e621_links.txt"
        try:
            if not out_path.exists():
                urls, _, _ = self._get_e621_urls()
                out_path.write_text("\n".join(urls) + "\n", encoding="utf-8")
            os.startfile(str(out_path))
        except Exception as e:
            try:
                messagebox.showerror("Open file failed", str(e))
            except Exception:
                pass


# -------------------- Report on quit --------------------
def export_csv(conn, path: Path):
    import csv
    rows = conn.execute("""
        SELECT path, folder, score, wins, losses, duels, last_seen, hidden
        FROM images ORDER BY score DESC
    """).fetchall()
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["path","folder","score","wins","losses","duels","last_seen_iso","hidden"])
        for p, folder, score, wins, losses, duels, last_seen, hidden in rows:
            iso = datetime.utcfromtimestamp(last_seen).isoformat()+"Z" if last_seen else ""
            w.writerow([p, folder, f"{score:.2f}", wins, losses, duels, iso, hidden])

def show_folder_chart(conn):
    if not plt:
        print("[report] matplotlib not available, skipping chart")
        return
    rows = folder_leaderboard(conn)[:20]
    if not rows:
        return
    names = [Path(r['folder']).name or r['folder'] for r in rows]
    scores = [r['score'] for r in rows]
    plt.figure(figsize=(10, 6))
    plt.barh(list(reversed(names)), list(reversed(scores)))
    plt.xlabel("Folder ranking score")
    plt.title("Top folders (metric: {})".format(rows[0]['metric'] if rows else LEADERBOARD_METRIC_DEFAULT))
    plt.tight_layout()
    plt.show()

# -------------------- Run --------------------
def run():
    conn = init_db()
    scan_images(conn)
    root = tk.Tk()
    app = App(root, conn)
    root.mainloop()
    csv_path = Path(ROOT_DIR) / "image_duel_report.csv"
    export_csv(conn, csv_path)
    print(f"[report] CSV written: {csv_path}")
    try:
        show_folder_chart(conn)
    except Exception as e:
        print("[report] chart skipped:", e)

if __name__ == "__main__":
    run()
