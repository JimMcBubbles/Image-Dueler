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

from PIL import Image, ImageTk, ImageSequence
import tkinter as tk
import tkinter.font as tkfont

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

# -------------------- THEME (Dark Mode) --------------------
DARK_BG    = "#1e1e1e"
DARK_PANEL = "#252526"
DARK_BORDER= "#333333"
TEXT_COLOR = "#eeeeee"
ACCENT     = "#569cd6"
LINK_COLOR = "#4ea1ff"

# -------------------- CONFIG --------------------
ROOT_DIR = r"I:\OneDrive\Discord Downloader Output\+\Grabber"
DB_PATH = Path(ROOT_DIR) / ".image_ranking.sqlite"
SIDEcar_DIR = Path(ROOT_DIR) / ".image_duel_sidecars"
SIDEcar_DIR.mkdir(exist_ok=True)

EMBED_JPEG_EXIF = False
WINDOW_SIZE = (1500, 950)

SUPPORTED_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".tif", ".tiff"}
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
    SIDEcar_DIR.mkdir(exist_ok=True)
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
    a_id, a_path, a_folder, a_duels, a_score = a
    b_id, b_path, b_folder, b_duels, b_score = b

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

def hide_image(conn, row):
    img_id, img_path = row[0], row[1]
    conn.execute("UPDATE images SET hidden=1, last_seen=? WHERE id=?", (int(time.time()), img_id))
    conn.commit()
    print(f"[hide] removed from pool: {img_path}")

# -------------------- e621 link helper --------------------
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

        # -------------------- Mouse controls --------------------
        self.left_panel.bind("<Button-1>",  lambda e: self.choose("a"))
        self.right_panel.bind("<Button-1>", lambda e: self.choose("b"))
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
        self.keys_table = tk.Frame(self.sidebar, bg=DARK_PANEL, bd=1, relief="solid")

        # keybinds
        root.bind("1", lambda e: self.choose("a"))
        root.bind("2", lambda e: self.choose("b"))
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
    def _visible_rows(self):
        return list(self.conn.execute("SELECT id, path, folder, duels, score FROM images WHERE hidden=0"))

    def pick_two(self):
        rows = self._visible_rows()
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
        print("  LEFT: ", a[1], f"(score={a[4]:.2f}, duels={a[3]})")
        print("  RIGHT:", b[1], f"(score={b[4]:.2f}, duels={b[3]})")

        self._render_img(self.left_panel, a[1])
        self._render_img(self.right_panel, b[1])

        self.update_sidebar(a[2], b[2])
        self.root.after(50, self._refresh_images)

    # ---------- image display (with GIF support) ----------
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
            self._render_img(self.left_panel, a[1])
            self._render_img(self.right_panel, b[1])

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

        hdr_font  = ("Segoe UI", 10, "bold")
        key_font  = ("Consolas", 9)
        bind_font = ("Segoe UI Emoji", 10)

        def H(c, text):
            tk.Label(self.keys_table, text=text, font=hdr_font, fg=ACCENT, bg=DARK_PANEL, anchor="w") \
              .grid(row=0, column=c, sticky="we", padx=(8 if c in (0, 2) else 6), pady=(6, 3))

        H(0, "Key"); H(1, "Bind"); H(2, "Key"); H(3, "Bind")

        # ICON-ONLY binds (custom)
        rows = [
            ("L_Mouse",  "🔺",  "R_Mouse, 3", "🔻"),
            ("1, 2",     "🔺",  "0, Space",   "↺"),
            ("M_Mouse",  "✖",  "X/M",        "✖"),
            ("O/P",      "🖼",  "⇪O/⇪P",      "📂"),
            ("Q",        "🚪",  "T",          "⚙"),
        ]

        for r, (k1, b1, k2, b2) in enumerate(rows, start=1):
            tk.Label(self.keys_table, text=k1, font=key_font,  fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w") \
              .grid(row=r, column=0, sticky="we", padx=(8, 6))
            tk.Label(self.keys_table, text=b1, font=bind_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="w") \
              .grid(row=r, column=1, sticky="we", padx=(6, 12))
            tk.Label(self.keys_table, text=k2, font=key_font,  fg=TEXT_COLOR, bg=DARK_PANEL, anchor="e") \
              .grid(row=r, column=2, sticky="we", padx=(8, 6))
            tk.Label(self.keys_table, text=b2, font=bind_font, fg=TEXT_COLOR, bg=DARK_PANEL, anchor="e") \
              .grid(row=r, column=3, sticky="we", padx=(6, 8))

        # stretch columns evenly across the frame width
        for c in range(4):
            self.keys_table.grid_columnconfigure(c, weight=1, uniform="keys")

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
                  self.board, self.nav_row, self.now_header, self.now,
                  self.links_header, self.link_left, self.link_right, self.keys_table):
            w.pack_forget()

        self.leader_header.pack(anchor="w")
        self.metric_label.configure(text=f"[Metric: {self._metric_human()}]")
        self.metric_label.pack(anchor="w")
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
        if not self.current: return
        a, b = self.current
        hide_image(self.conn, a if which == "a" else b)
        self.load_duel()

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
