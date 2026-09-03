"""Tkinter chess: human versus a lightweight Elo-tunable bot, or another
human over the network."""

import asyncio
import json
import math
import os
import queue
import random
import sys
import threading
import unicodedata
import ctypes
import tkinter as tk
from dataclasses import dataclass
from pathlib import Path
from tkinter import ttk

import websockets

SERVER_URL = "wss://servertest-1-w6my.onrender.com"


PIECE_SYMBOLS = {
    "K": "\u2654", "Q": "\u2655", "R": "\u2656", "B": "\u2657", "N": "\u2658", "P": "\u2659",
    "k": "\u265a", "q": "\u265b", "r": "\u265c", "b": "\u265d", "n": "\u265e", "p": "\u265f",
}
VALUES = {"P": 100, "N": 320, "B": 330, "R": 500, "Q": 900, "K": 20_000}
MATERIAL_VALUES = {"P": 1, "N": 3, "B": 3, "R": 5, "Q": 9}
FILES = "abcdefgh"
MIN_ELO = 400
MAX_ELO = 3200


@dataclass(frozen=True)
class Move:
    start: tuple[int, int]
    end: tuple[int, int]
    promotion: str | None = None
    en_passant: bool = False
    castle: bool = False


class Position:
    def __init__(self):
        self.board = self.initial_board()
        self.turn = "w"
        self.castling = "KQkq"
        self.en_passant: tuple[int, int] | None = None

    @staticmethod
    def initial_board():
        return [
            list("rnbqkbnr"), list("pppppppp"), [""] * 8, [""] * 8,
            [""] * 8, [""] * 8, list("PPPPPPPP"), list("RNBQKBNR"),
        ]

    def copy(self):
        other = Position()
        other.board = [row[:] for row in self.board]
        other.turn, other.castling, other.en_passant = self.turn, self.castling, self.en_passant
        return other

    @staticmethod
    def color(piece):
        return "w" if piece.isupper() else "b"

    def find_king(self, color):
        king = "K" if color == "w" else "k"
        for row in range(8):
            for col in range(8):
                if self.board[row][col] == king:
                    return row, col
        raise ValueError("Position has no king")

    def attacked(self, square, by_color):
        row, col = square
        pawn = "P" if by_color == "w" else "p"
        pawn_row = row + 1 if by_color == "w" else row - 1
        for dc in (-1, 1):
            if 0 <= pawn_row < 8 and 0 <= col + dc < 8 and self.board[pawn_row][col + dc] == pawn:
                return True
        knight = "N" if by_color == "w" else "n"
        for dr, dc in ((-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)):
            if 0 <= row + dr < 8 and 0 <= col + dc < 8 and self.board[row + dr][col + dc] == knight:
                return True
        king = "K" if by_color == "w" else "k"
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                if (dr or dc) and 0 <= row + dr < 8 and 0 <= col + dc < 8:
                    if self.board[row + dr][col + dc] == king:
                        return True
        for directions, pieces in (
            (((-1, 0), (1, 0), (0, -1), (0, 1)), "RQ"),
            (((-1, -1), (-1, 1), (1, -1), (1, 1)), "BQ"),
        ):
            for dr, dc in directions:
                rr, cc = row + dr, col + dc
                while 0 <= rr < 8 and 0 <= cc < 8:
                    piece = self.board[rr][cc]
                    if piece:
                        if self.color(piece) == by_color and piece.upper() in pieces:
                            return True
                        break
                    rr, cc = rr + dr, cc + dc
        return False

    def in_check(self, color):
        return self.attacked(self.find_king(color), "b" if color == "w" else "w")

    def pseudo_moves(self, color):
        moves = []
        for row in range(8):
            for col in range(8):
                piece = self.board[row][col]
                if not piece or self.color(piece) != color:
                    continue
                kind = piece.upper()
                if kind == "P":
                    direction, start_row = (-1, 6) if color == "w" else (1, 1)
                    next_row = row + direction
                    if 0 <= next_row < 8 and not self.board[next_row][col]:
                        moves.extend(self.pawn_move_options((row, col), (next_row, col)))
                        two_row = row + 2 * direction
                        if row == start_row and not self.board[two_row][col]:
                            moves.append(Move((row, col), (two_row, col)))
                    for dc in (-1, 1):
                        end = (next_row, col + dc)
                        if not (0 <= end[0] < 8 and 0 <= end[1] < 8):
                            continue
                        target = self.board[end[0]][end[1]]
                        if target and self.color(target) != color and target.upper() != "K":
                            moves.extend(self.pawn_move_options((row, col), end))
                        elif end == self.en_passant:
                            moves.append(Move((row, col), end, en_passant=True))
                elif kind == "N":
                    for dr, dc in ((-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)):
                        self.add_if_valid(moves, (row, col), (row + dr, col + dc), color)
                elif kind in "BRQ":
                    directions = []
                    if kind in "RQ":
                        directions += [(-1, 0), (1, 0), (0, -1), (0, 1)]
                    if kind in "BQ":
                        directions += [(-1, -1), (-1, 1), (1, -1), (1, 1)]
                    for dr, dc in directions:
                        rr, cc = row + dr, col + dc
                        while 0 <= rr < 8 and 0 <= cc < 8:
                            if not self.add_if_valid(moves, (row, col), (rr, cc), color):
                                break
                            if self.board[rr][cc]:
                                break
                            rr, cc = rr + dr, cc + dc
                else:
                    for dr in (-1, 0, 1):
                        for dc in (-1, 0, 1):
                            if dr or dc:
                                self.add_if_valid(moves, (row, col), (row + dr, col + dc), color)
                    self.add_castles(moves, row, col, color)
        return moves

    def add_if_valid(self, moves, start, end, color):
        if not (0 <= end[0] < 8 and 0 <= end[1] < 8):
            return False
        target = self.board[end[0]][end[1]]
        if not target or (self.color(target) != color and target.upper() != "K"):
            moves.append(Move(start, end))
            return True
        return False

    def pawn_move_options(self, start, end):
        if end[0] in (0, 7):
            return [Move(start, end, promotion=p) for p in "QRBN"]
        return [Move(start, end)]

    def add_castles(self, moves, row, col, color):
        if self.in_check(color) or (color == "w" and (row, col) != (7, 4)) or (color == "b" and (row, col) != (0, 4)):
            return
        enemy = "b" if color == "w" else "w"
        rank, king = (7, "K") if color == "w" else (0, "k")
        if king not in self.board[rank][4]:
            return
        if color == "w":
            rights = (("K", 7, (5, 6), (5, 6)), ("Q", 0, (3, 2), (3, 2)))
        else:
            rights = (("k", 7, (5, 6), (5, 6)), ("q", 0, (3, 2), (3, 2)))
        for right, rook_col, transit, _ in rights:
            if right not in self.castling:
                continue
            if self.board[rank][rook_col].upper() != "R":
                continue
            between = range(5, 7) if rook_col == 7 else range(1, 4)
            if any(self.board[rank][c] for c in between):
                continue
            attacked_squares = ((rank, 5), (rank, 6)) if rook_col == 7 else ((rank, 3), (rank, 2))
            if any(self.attacked(square, enemy) for square in attacked_squares):
                continue
            moves.append(Move((rank, 4), (rank, 6 if rook_col == 7 else 2), castle=True))

    def legal_moves(self, color=None):
        color = color or self.turn
        result = []
        for move in self.pseudo_moves(color):
            test = self.copy()
            test.apply(move)
            if not test.in_check(color):
                result.append(move)
        return result

    def apply(self, move):
        start_row, start_col = move.start
        end_row, end_col = move.end
        piece = self.board[start_row][start_col]
        captured = self.board[end_row][end_col]
        self.board[start_row][start_col] = ""
        if move.en_passant:
            self.board[start_row][end_col] = ""
        placed = (move.promotion if move.promotion else piece) if piece.isupper() else (
            move.promotion.lower() if move.promotion else piece
        )
        self.board[end_row][end_col] = placed
        if move.castle:
            rook_start, rook_end = ((start_row, 7), (start_row, 5)) if end_col == 6 else ((start_row, 0), (start_row, 3))
            self.board[rook_end[0]][rook_end[1]] = self.board[rook_start[0]][rook_start[1]]
            self.board[rook_start[0]][rook_start[1]] = ""
        self.update_rights(piece, move.start, move.end, captured)
        self.en_passant = ((start_row + end_row) // 2, start_col) if piece.upper() == "P" and abs(end_row - start_row) == 2 else None
        self.turn = "b" if self.turn == "w" else "w"

    def update_rights(self, piece, start, end, captured):
        rights = self.castling
        for square, chars in (((7, 4), "KQ"), ((0, 4), "kq"), ((7, 0), "Q"), ((7, 7), "K"), ((0, 0), "q"), ((0, 7), "k")):
            is_king_start = square[1] == 4 and piece.upper() == "K"
            if start == square and (is_king_start or square[1] != 4):
                rights = "".join(c for c in rights if c not in chars)
        for square, chars in (((7, 0), "Q"), ((7, 7), "K"), ((0, 0), "q"), ((0, 7), "k")):
            if end == square and captured:
                rights = "".join(c for c in rights if c not in chars)
        self.castling = rights


class NetworkClient:
    """Runs a websocket connection on its own background thread and
    bridges messages to the tkinter main thread through a thread-safe
    queue (the same pattern already used for the bot's search thread)."""

    def __init__(self, url, incoming_queue):
        self.url = url
        self.incoming = incoming_queue
        self.loop = None
        self.ws = None
        self.closed = False
        self.thread = threading.Thread(target=self._run, daemon=True)

    def start(self):
        self.thread.start()

    def _run(self):
        self.loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self.loop)
        try:
            self.loop.run_until_complete(self._connect_and_listen())
        except Exception:
            pass

    async def _connect_and_listen(self):
        try:
            async with websockets.connect(
                self.url, ping_interval=20, ping_timeout=20
            ) as ws:
                self.ws = ws
                self.incoming.put({"type": "_connected"})
                heartbeat = asyncio.ensure_future(self._heartbeat(ws))
                try:
                    async for raw in ws:
                        try:
                            msg = json.loads(raw)
                        except (json.JSONDecodeError, TypeError):
                            continue
                        self.incoming.put(msg)
                finally:
                    heartbeat.cancel()
        except Exception:
            if not self.closed:
                self.incoming.put({"type": "_connection_failed"})
        finally:
            self.connected = False
            if not self.closed:
                self.incoming.put({"type": "_disconnected"})

    async def _heartbeat(self, ws):
        # Extra app-level ping on top of the websocket protocol's own
        # ping/pong, to keep Render's proxy from treating the connection
        # as idle.
        try:
            while True:
                await asyncio.sleep(15)
                await ws.send(json.dumps({"type": "ping"}))
        except Exception:
            pass

    def send(self, payload):
        if self.loop is None or self.ws is None:
            return
        asyncio.run_coroutine_threadsafe(self._send(payload), self.loop)

    async def _send(self, payload):
        try:
            await self.ws.send(json.dumps(payload))
        except Exception:
            pass

    def close(self):
        self.closed = True
        if self.loop is not None and self.ws is not None:
            asyncio.run_coroutine_threadsafe(self.ws.close(), self.loop)


class ChessApp:
    def __init__(self, root):
        self.root = root
        root.title("Tkinter Chess - Elo Bot")
        root.resizable(False, False)
        self.position = Position()
        self.selected = None
        self.thinking = False
        self.last_move = None
        self.in_game = False
        self.game_id = 0
        self.bot_results = queue.Queue()
        self.pulse_job = None
        self.sound_aliases = {}
        self.hover_cell = None
        self.animation_hidden = set()
        self.status = tk.StringVar()
        self.material_text = tk.StringVar(value="Material 0")
        self.settings = self.load_settings()
        self.elo = tk.IntVar(value=self.settings["elo"])
        self.elo_text = tk.StringVar(value=str(self.settings["elo"]))
        self.elo_description = tk.StringVar(value="Club player")
        self.dark_mode = tk.BooleanVar(value=self.settings["dark_mode"])
        self.sound_enabled = tk.BooleanVar(value=self.settings["sound_enabled"])
        self.show_coordinates = tk.BooleanVar(value=self.settings["show_coordinates"])
        self.update_elo(self.settings["elo"])
        self.human_color = "w"
        self.multiplayer = False
        self.spectating = False
        self.connecting = False
        self.connect_attempts = 0
        self.reconnecting = False
        self.reconnect_attempts = 0
        self.flipped = False
        self.player_name = None
        self.requested_name = None
        self.opponent_name = None
        self.spectate_white = None
        self.spectate_black = None
        self.pending_invite_target = None
        self.net = None
        self.net_queue = queue.Queue()
        self.game_subtitle = tk.StringVar(value="Play against an adjustable-strength bot")
        self._window_positioned = False
        self.root.protocol("WM_DELETE_WINDOW", self.confirm_close)
        self.stats = self.load_stats()
        self.stat_vars = {
            "bot": {"wins": tk.StringVar(), "losses": tk.StringVar(), "draws": tk.StringVar()},
            "multiplayer": {"wins": tk.StringVar(), "losses": tk.StringVar(), "draws": tk.StringVar()},
        }
        self.load_sounds()
        self.build_ui()
        self.build_menu()
        self.build_multiplayer_ui()
        self.toggle_theme()
        self.show_menu()
        self.apply_title_bar_theme()
        self.draw()

    def build_ui(self):
        self.root.configure(bg="#202124")
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("App.TFrame", background="#202124")
        style.configure("Panel.TFrame", background="#2b2d31")
        style.configure("Title.TLabel", background="#202124", foreground="#f1f3f4")
        style.configure("Muted.TLabel", background="#202124", foreground="#aeb4bd")
        style.configure("Material.TLabel", background="#202124", foreground="#f1f3f4",
                        font=("Segoe UI", 14, "bold"))
        style.configure("Thinking.TLabel", background="#202124", foreground="#aeb4bd")
        style.configure("Panel.TLabel", background="#2b2d31", foreground="#f1f3f4")
        style.configure("PanelMuted.TLabel", background="#2b2d31", foreground="#aeb4bd")
        style.configure("StatsWin.TLabel", background="#2b2d31", foreground="#4caf50",
                        font=("Segoe UI", 10, "bold"))
        style.configure("StatsLoss.TLabel", background="#2b2d31", foreground="#e5534b",
                        font=("Segoe UI", 10, "bold"))
        style.configure("Status.TLabel", background="#34373d", foreground="#dbe7f5", padding=9)
        style.configure("Accent.TButton", padding=(8, 6), background="#4b78a8",
                        foreground="#ffffff", borderwidth=0)
        style.map("Accent.TButton", background=[("active", "#6196ca")])
        style.configure("Menu.TButton", padding=(7, 3), background="#4a4d52",
                        foreground="#ffffff", borderwidth=0)
        style.map("Menu.TButton", background=[("active", "#5c6067")])
        style.configure("Panel.Horizontal.TScale", background="#2b2d31", troughcolor="#17181a")
        style.configure("Panel.TCheckbutton", background="#2b2d31", foreground="#f1f3f4")
        style.configure("Theme.TCheckbutton", background="#202124", foreground="#f1f3f4")

        self.game_frame = ttk.Frame(self.root, padding=16, style="App.TFrame")
        main = self.game_frame
        main.grid()
        header = ttk.Frame(main, style="App.TFrame")
        header.grid(row=0, column=0, sticky="we")
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text="CHESS", font=("Segoe UI", 24, "bold"),
                  style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(header, textvariable=self.material_text, style="Material.TLabel").grid(
            row=0, column=1, sticky="e", padx=(0, 14))
        self.draw_offer_button = ttk.Button(header, text="Offer Draw", style="Menu.TButton",
                                             command=self.propose_draw)
        self.draw_offer_button.grid(row=0, column=2, sticky="e", padx=(0, 8))
        ttk.Button(header, text="< Menu", style="Menu.TButton",
                   command=self.return_to_menu).grid(row=0, column=3, sticky="e")
        ttk.Label(main, textvariable=self.game_subtitle,
                  style="Muted.TLabel").grid(row=1, column=0, sticky="w", pady=(0, 12))
        self.thinking_label = ttk.Label(main, textvariable=self.status,
                                        style="Thinking.TLabel")
        self.thinking_label.grid(row=2, column=0, sticky="w", pady=(0, 8))
        self.board_frame = tk.Frame(main, bg="#17181a", width=416, height=416)
        self.board_frame.grid(row=3, column=0, sticky="nsew")
        self.board_frame.grid_propagate(False)
        self.board_canvas = tk.Canvas(
            self.board_frame, width=416, height=416, bd=0,
            highlightthickness=0, cursor="hand2",
        )
        self.board_canvas.pack()
        self.board_canvas.bind("<Button-1>", self.click_canvas)
        self.board_canvas.bind("<Motion>", self.motion_canvas)
        self.board_canvas.bind("<Leave>", lambda event: self.clear_hover())
        ttk.Label(main, text="Select a piece, then click a highlighted square.",
                  style="Muted.TLabel").grid(row=4, column=0, pady=(10, 0))

    # ---------- win/loss stats (persisted to a local JSON file) ----------

    def stats_path(self):
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
        folder = os.path.join(base, "MultiChess")
        try:
            os.makedirs(folder, exist_ok=True)
        except OSError:
            folder = os.path.expanduser("~")
        return os.path.join(folder, "stats.json")

    def load_stats(self):
        default = {"bot": {"wins": 0, "losses": 0, "draws": 0},
                   "multiplayer": {"wins": 0, "losses": 0, "draws": 0}}
        try:
            with open(self.stats_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
            for category in default:
                if isinstance(data.get(category), dict):
                    default[category].update({
                        k: v for k, v in data[category].items()
                        if k in default[category] and isinstance(v, int)
                    })
        except (OSError, ValueError):
            pass
        return default

    def save_stats(self):
        try:
            with open(self.stats_path(), "w", encoding="utf-8") as f:
                json.dump(self.stats, f)
        except OSError:
            pass

    def record_result(self, category, result):
        key = {"win": "wins", "loss": "losses", "draw": "draws"}[result]
        self.stats[category][key] += 1
        self.save_stats()
        self.update_stats_display()

    def update_stats_display(self):
        for category in ("bot", "multiplayer"):
            values = self.stats[category]
            self.stat_vars[category]["wins"].set(f"{values['wins']}W")
            self.stat_vars[category]["losses"].set(f"{values['losses']}L")
            self.stat_vars[category]["draws"].set(f"{values['draws']}D")

    # ---------- persisted settings (Elo, dark mode, sound) ----------

    def settings_path(self):
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
        folder = os.path.join(base, "MultiChess")
        try:
            os.makedirs(folder, exist_ok=True)
        except OSError:
            folder = os.path.expanduser("~")
        return os.path.join(folder, "settings.json")

    def load_settings(self):
        default = {"elo": 1200, "dark_mode": True, "sound_enabled": True, "show_coordinates": True}
        try:
            with open(self.settings_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data.get("elo"), int):
                default["elo"] = max(MIN_ELO, min(MAX_ELO, data["elo"]))
            if isinstance(data.get("dark_mode"), bool):
                default["dark_mode"] = data["dark_mode"]
            if isinstance(data.get("sound_enabled"), bool):
                default["sound_enabled"] = data["sound_enabled"]
            if isinstance(data.get("show_coordinates"), bool):
                default["show_coordinates"] = data["show_coordinates"]
        except (OSError, ValueError):
            pass
        return default

    def save_settings(self):
        try:
            with open(self.settings_path(), "w", encoding="utf-8") as f:
                json.dump({
                    "elo": self.elo.get(),
                    "dark_mode": self.dark_mode.get(),
                    "sound_enabled": self.sound_enabled.get(),
                    "show_coordinates": self.show_coordinates.get(),
                }, f)
        except OSError:
            pass

    def build_menu(self):
        self.menu_frame = ttk.Frame(self.root, padding=36, style="App.TFrame")
        header = ttk.Frame(self.menu_frame, style="App.TFrame")
        header.grid(row=0, column=0, sticky="we", pady=(0, 4))
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text="CHESS", font=("Segoe UI", 34, "bold"),
                  style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Button(header, text="Multiplayer", style="Menu.TButton",
                   command=self.open_multiplayer).grid(row=0, column=1, sticky="e")
        ttk.Label(self.menu_frame, text="A quiet game against a customizable bot",
                  style="Muted.TLabel").grid(row=1, column=0, sticky="w", pady=(0, 28))
        card = ttk.Frame(self.menu_frame, padding=24, style="Panel.TFrame")
        card.grid(row=2, column=0)
        ttk.Label(card, text="CHOOSE YOUR OPPONENT", font=("Segoe UI", 11, "bold"),
                  style="Panel.TLabel").grid(sticky="w")
        ttk.Label(card, text="Bot Elo", style="PanelMuted.TLabel").grid(sticky="w", pady=(18, 2))
        ttk.Label(card, textvariable=self.elo_text, font=("Segoe UI", 24, "bold"),
                  style="Panel.TLabel").grid(sticky="w")
        ttk.Label(card, textvariable=self.elo_description,
                  style="PanelMuted.TLabel").grid(sticky="w")
        elo_scale = ttk.Scale(card, from_=MIN_ELO, to=MAX_ELO, variable=self.elo, orient="horizontal",
                               length=260, style="Panel.Horizontal.TScale",
                               command=self.update_elo)
        elo_scale.grid(sticky="we", pady=(4, 0))
        elo_scale.bind("<ButtonRelease-1>", lambda event: self.save_settings())
        range_frame = ttk.Frame(card, style="Panel.TFrame")
        range_frame.grid(sticky="we")
        range_frame.columnconfigure(1, weight=1)
        ttk.Label(range_frame, text=str(MIN_ELO), style="PanelMuted.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(range_frame, text=str(MAX_ELO), style="PanelMuted.TLabel").grid(row=0, column=1, sticky="e")
        ttk.Button(card, text="Start game", style="Accent.TButton",
                   command=self.start_game).grid(sticky="we", pady=(24, 10))
        options = ttk.Frame(self.menu_frame, style="App.TFrame")
        options.grid(row=3, column=0, pady=(16, 0))
        ttk.Checkbutton(options, text="Dark mode", variable=self.dark_mode,
                        style="Theme.TCheckbutton", command=self.toggle_theme).grid(
            row=0, column=0, padx=(0, 18))
        ttk.Checkbutton(options, text="Sound effects", variable=self.sound_enabled,
                        style="Theme.TCheckbutton", command=self.save_settings).grid(
            row=0, column=1, padx=(0, 18))
        ttk.Checkbutton(options, text="Coordinates", variable=self.show_coordinates,
                        style="Theme.TCheckbutton", command=self.save_settings).grid(row=0, column=2)
        stats_card = ttk.Frame(self.menu_frame, padding=(18, 12), style="Panel.TFrame")
        stats_card.grid(row=4, column=0, pady=(16, 0), sticky="we")
        stats_card.columnconfigure(1, weight=1)
        self.build_stats_row(stats_card, 0, "Bot", "bot")
        self.build_stats_row(stats_card, 1, "Multiplayer", "multiplayer")
        self.update_stats_display()

    def build_stats_row(self, parent, row, label, category):
        top_pad = 0 if row == 0 else 8
        ttk.Label(parent, text=label, style="PanelMuted.TLabel").grid(
            row=row, column=0, sticky="w", pady=(top_pad, 0))
        wl = ttk.Frame(parent, style="Panel.TFrame")
        wl.grid(row=row, column=1, sticky="e", pady=(top_pad, 0))
        ttk.Label(wl, textvariable=self.stat_vars[category]["wins"],
                  style="StatsWin.TLabel").pack(side="left", padx=(0, 8))
        ttk.Label(wl, textvariable=self.stat_vars[category]["losses"],
                  style="StatsLoss.TLabel").pack(side="left", padx=(0, 8))
        ttk.Label(wl, textvariable=self.stat_vars[category]["draws"],
                  style="PanelMuted.TLabel").pack(side="left")

    def build_multiplayer_ui(self):
        self.mp_status = tk.StringVar(value="Connecting to server...")

        # --- connecting screen ---
        self.connect_frame = ttk.Frame(self.root, padding=36, style="App.TFrame")
        ttk.Label(self.connect_frame, text="CHESS", font=("Segoe UI", 34, "bold"),
                  style="Title.TLabel").grid(row=0, column=0, pady=(0, 20))
        ttk.Label(self.connect_frame, textvariable=self.mp_status, style="Muted.TLabel",
                  wraplength=280, justify="center", anchor="center", width=36).grid(
            row=1, column=0, pady=(0, 20))
        ttk.Button(self.connect_frame, text="Cancel", style="Menu.TButton",
                   command=self.disconnect_multiplayer).grid(row=2, column=0)

        # --- choose name screen ---
        self.name_frame = ttk.Frame(self.root, padding=36, style="App.TFrame")
        ttk.Label(self.name_frame, text="CHOOSE A NAME", font=("Segoe UI", 20, "bold"),
                  style="Title.TLabel").grid(row=0, column=0, pady=(0, 4))
        ttk.Label(self.name_frame, text="Other players will see this name. It sticks "
                                         "until you leave the lobby or disconnect.",
                  style="Muted.TLabel", wraplength=280, justify="center", anchor="center").grid(
            row=1, column=0, pady=(0, 20))
        self.name_entry_var = tk.StringVar()

        def is_valid_name_input(text):
            if len(text) > 24:
                return False
            # Same combining-mark cap as the server's sanitizer, so stacked
            # diacritics ("zalgo" text) get rejected here too, not just
            # cleaned up after the fact once it reaches the server.
            combining_total = sum(1 for ch in text if unicodedata.combining(ch))
            return combining_total <= 2

        name_validate_cmd = (self.root.register(is_valid_name_input), "%P")
        name_entry = ttk.Entry(self.name_frame, textvariable=self.name_entry_var, width=24,
                                validate="key", validatecommand=name_validate_cmd)
        name_entry.grid(row=2, column=0, pady=(0, 16))
        name_entry.bind("<Return>", lambda event: self.submit_name())
        ttk.Button(self.name_frame, text="Continue", style="Accent.TButton",
                   command=self.submit_name).grid(row=3, column=0, pady=(0, 10))
        ttk.Button(self.name_frame, text="Cancel", style="Menu.TButton",
                   command=self.disconnect_multiplayer).grid(row=4, column=0)

        # --- lobby screen ---
        self.lobby_frame = ttk.Frame(self.root, padding=36, style="App.TFrame")
        header = ttk.Frame(self.lobby_frame, style="App.TFrame")
        header.grid(row=0, column=0, sticky="we", pady=(0, 4))
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text="LOBBY", font=("Segoe UI", 20, "bold"),
                  style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Button(header, text="< Leave", style="Menu.TButton",
                   command=self.disconnect_multiplayer).grid(row=0, column=1, sticky="e")
        self.own_name_text = tk.StringVar(value="")
        ttk.Label(self.lobby_frame, textvariable=self.own_name_text, style="PanelMuted.TLabel",
                  padding=(10, 4)).grid(row=1, column=0, pady=(0, 8))
        ttk.Label(self.lobby_frame, textvariable=self.mp_status, style="Muted.TLabel",
                  wraplength=280, justify="center", anchor="center").grid(
            row=2, column=0, pady=(0, 16))
        list_frame = ttk.Frame(self.lobby_frame, style="Panel.TFrame", padding=8)
        list_frame.grid(row=3, column=0, sticky="we")
        panel_bg = "#2b2d31" if self.dark_mode.get() else "#ffffff"
        self.lobby_canvas = tk.Canvas(list_frame, width=300, height=240, bg=panel_bg,
                                       highlightthickness=0)
        self.lobby_scrollbar = tk.Scrollbar(
            list_frame, orient="vertical", command=self.lobby_canvas.yview,
            troughcolor=panel_bg, bg="#4b78a8", activebackground="#5a8ac0",
            highlightthickness=0, borderwidth=0,
        )
        self.lobby_list_frame = ttk.Frame(self.lobby_canvas, style="Panel.TFrame")
        self.lobby_list_frame.bind("<Configure>", self.update_lobby_scrollregion)
        self.lobby_canvas.create_window((0, 0), window=self.lobby_list_frame, anchor="nw", width=284)
        self.lobby_canvas.configure(yscrollcommand=self.lobby_scrollbar.set)
        self.lobby_canvas.pack(side="left", fill="both", expand=True)
        self.lobby_scrollbar.pack(side="right", fill="y")
        self.lobby_canvas.bind(
            "<MouseWheel>",
            lambda event: self.lobby_canvas.yview_scroll(-1 * (event.delta // 120), "units"),
        )

    def update_lobby_scrollregion(self, event=None):
        # Clamp the scrollable region to at least the canvas's own height, so
        # a short (or empty) lobby list can't be scrolled into blank space.
        bbox = self.lobby_canvas.bbox("all")
        if not bbox:
            return
        canvas_height = self.lobby_canvas.winfo_height()
        content_height = bbox[3] - bbox[1]
        if content_height < canvas_height:
            self.lobby_canvas.configure(scrollregion=(0, 0, bbox[2], canvas_height))
        else:
            self.lobby_canvas.configure(scrollregion=bbox)

    # ---------- multiplayer: connection flow ----------

    def open_multiplayer(self):
        self.menu_frame.grid_remove()
        self.connecting = True
        self.connect_attempts = 0
        self.connect_frame.grid()
        self.root.title("Chess - Connecting")
        self.center_window()
        self.try_connect()
        self.root.after(100, self.poll_network)

    def try_connect(self):
        if not self.connecting:
            return
        self.connect_attempts += 1
        self.mp_status.set(
            "Connecting to server..." if self.connect_attempts == 1
            else f"Connecting to server... (attempt {self.connect_attempts}/3)"
        )
        if self.net is not None:
            self.net.close()
        self.net_queue = queue.Queue()
        self.net = NetworkClient(SERVER_URL, self.net_queue)
        self.net.start()

    def disconnect_multiplayer(self):
        if self.net is not None:
            self.net.close()
            self.net = None
        self.connecting = False
        self.multiplayer = False
        self.spectating = False
        self.reconnecting = False
        self.reconnect_attempts = 0
        self.flipped = False
        self.human_color = "w"
        self.opponent_name = None
        self.spectate_white = None
        self.spectate_black = None
        self.player_name = None
        self.requested_name = None
        self.pending_invite_target = None
        self.connect_frame.grid_remove()
        self.name_frame.grid_remove()
        self.lobby_frame.grid_remove()
        self.show_menu()

    def submit_name(self):
        name = self.name_entry_var.get().strip()
        if not name or self.net is None:
            return
        self.requested_name = name
        self.net.send({"type": "register", "name": name})

    def poll_network(self):
        if self.net is None:
            return
        try:
            while True:
                msg = self.net_queue.get_nowait()
                self.handle_network_message(msg)
        except queue.Empty:
            pass
        self.root.after(100, self.poll_network)

    def handle_network_message(self, msg):
        msg_type = msg.get("type")
        if msg_type == "_connected":
            if self.reconnecting:
                self.status.set("Reconnected — resyncing...")
                self.net.send({"type": "register", "name": self.player_name})
            else:
                self.connecting = False
                self.connect_frame.grid_remove()
                self.name_frame.grid()
                self.root.title("Chess - Choose a name")
                self.center_window()
        elif msg_type == "_connection_failed":
            if self.reconnecting:
                self.schedule_reconnect_retry()
            elif self.connecting and self.connect_attempts < 3:
                self.mp_status.set(f"Connection failed, retrying... ({self.connect_attempts}/3)")
                self.root.after(1500, self.try_connect)
            elif self.connecting:
                self.connecting = False
                self.mp_status.set("Couldn't connect to the server after 3 attempts.")
            else:
                self.mp_status.set("Couldn't connect to the server. Try again in a moment.")
                self.disconnect_multiplayer()
        elif msg_type == "_disconnected":
            if self.in_game and self.multiplayer and not self.reconnecting:
                self.begin_reconnect()
            elif self.reconnecting or self.connecting:
                pass  # already handled by schedule_reconnect_retry / _connection_failed above
            else:
                self.mp_status.set("Disconnected from the server.")
                self.disconnect_multiplayer()
        elif msg_type == "registered":
            if self.reconnecting:
                self.reconnecting = False
                self.player_name = msg["name"]
                self.confirm_dialog(
                    "Game lost", "Your game couldn't be resumed.",
                    self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                    on_cancel=self.disconnect_multiplayer,
                )
            else:
                self.player_name = msg["name"]
                if self.requested_name and self.requested_name != self.player_name:
                    self.own_name_text.set(
                        f"\"{self.requested_name}\" was taken — you're now {self.player_name}"
                    )
                else:
                    self.own_name_text.set(f"You're logged in as {self.player_name}")
                self.connect_frame.grid_remove()
                self.name_frame.grid_remove()
                self.mp_status.set("Invite a free player, or spectate one who's in a game.")
                self.lobby_frame.grid()
                self.root.title("Chess - Lobby")
                self.center_window()
        elif msg_type == "reconnected":
            self.reconnecting = False
            self.resume_after_reconnect(msg)
        elif msg_type == "player_list":
            self.update_lobby_list(msg.get("players", []))
        elif msg_type == "invite_received":
            sender = msg.get("from", "Someone")
            self.confirm_dialog(
                "Game invite", f"{sender} wants to play. Accept?",
                lambda: self.respond_to_invite(sender, True),
                on_cancel=lambda: self.respond_to_invite(sender, False),
            )
        elif msg_type == "invite_failed":
            self.mp_status.set("That player is no longer available.")
        elif msg_type == "invite_declined":
            self.mp_status.set(f"{msg.get('from', 'They')} declined the invite.")
            self.pending_invite_target = None
        elif msg_type == "game_start":
            self.begin_multiplayer_game(msg)
        elif msg_type == "move":
            self.apply_network_move(msg)
        elif msg_type == "opponent_disconnected":
            self.status.set(f"{self.opponent_name} disconnected. Waiting for them to reconnect...")
        elif msg_type == "opponent_reconnected":
            self.draw()
        elif msg_type == "opponent_left":
            self.record_result("multiplayer", "win")
            self.confirm_dialog(
                "Opponent left", "Your opponent disconnected and didn't return.",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "opponent_resigned":
            self.record_result("multiplayer", "win")
            self.confirm_dialog(
                "Opponent resigned", "Your opponent resigned. You win!",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "draw_offered":
            self.confirm_dialog(
                "Draw offer", f"{self.opponent_name} is offering a draw. Accept?",
                lambda: self.respond_to_draw(True),
                on_cancel=lambda: self.respond_to_draw(False),
            )
        elif msg_type == "draw_declined":
            self.status.set(f"{self.opponent_name} declined the draw offer.")
        elif msg_type == "draw_agreed":
            self.record_result("multiplayer", "draw")
            self.finish("Draw agreed.")
        elif msg_type == "rematch_offered":
            self.confirm_dialog(
                "Rematch?", f"{self.opponent_name} wants a rematch. Accept?",
                lambda: self.respond_to_rematch(True),
                on_cancel=lambda: self.respond_to_rematch(False),
            )
        elif msg_type == "rematch_declined":
            self.confirm_dialog(
                "Rematch declined", f"{self.opponent_name} declined the rematch.",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "rematch_failed":
            self.confirm_dialog(
                "Rematch unavailable", "That game is no longer available for a rematch.",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "move_rejected":
            self.confirm_dialog(
                "Out of sync", "The server rejected that move, so this game can't continue safely.",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "kicked_for_cheating":
            self.record_result("multiplayer", "loss")
            self.confirm_dialog(
                "Game ended", msg.get("message", "Too many invalid moves were sent."),
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "opponent_kicked":
            self.record_result("multiplayer", "win")
            self.confirm_dialog(
                "You win", msg.get("message", "Your opponent was removed from the game."),
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
        elif msg_type == "spectate_start":
            self.begin_spectate(msg)
        elif msg_type == "spectate_failed":
            self.mp_status.set("That game is no longer available to watch.")
        elif msg_type == "game_ended":
            if self.spectating:
                self.spectator_finish(msg.get("message", "The game has ended."))

    def update_lobby_list(self, players):
        for widget in self.lobby_list_frame.winfo_children():
            widget.destroy()
        others = [p for p in players if p["name"] != self.player_name]
        if not others:
            self.mp_status.set("Waiting for other players to join...")
            ttk.Label(self.lobby_list_frame, text="\u265f", font=("Segoe UI Symbol", 28),
                      style="PanelMuted.TLabel").pack(pady=(28, 4))
            ttk.Label(self.lobby_list_frame, text="No one else is online right now",
                      style="Panel.TLabel").pack()
            ttk.Label(self.lobby_list_frame, text="Chess is better with two \u2014 invite a friend",
                      style="PanelMuted.TLabel").pack(pady=(2, 28))
        else:
            self.mp_status.set("Invite a free player, or spectate one who's in a game.")
        for entry in others:
            row = ttk.Frame(self.lobby_list_frame, style="Panel.TFrame")
            row.pack(fill="x", pady=2)
            label_text = entry["name"] + ("  (in game)" if entry["in_game"] else "")
            ttk.Label(row, text=label_text, style="Panel.TLabel").pack(side="left", padx=(2, 8))
            if entry["in_game"]:
                ttk.Button(row, text="Spectate", style="Menu.TButton",
                           command=lambda n=entry["name"]: self.start_spectate(n)).pack(side="right")
            else:
                ttk.Button(row, text="Invite", style="Menu.TButton",
                           command=lambda n=entry["name"]: self.confirm_invite(n)).pack(side="right")

    def confirm_invite(self, name):
        self.confirm_dialog(
            "Invite to play", f"Invite {name} to a game?",
            lambda: self.send_invite(name),
        )

    def start_spectate(self, name):
        if self.net is not None:
            self.net.send({"type": "spectate", "target": name})
            self.mp_status.set(f"Joining {name}'s game as a spectator...")

    def send_invite(self, name):
        self.pending_invite_target = name
        self.mp_status.set(f"Invite sent to {name}. Waiting for a response...")
        if self.net is not None:
            self.net.send({"type": "invite", "target": name})

    def respond_to_invite(self, sender, accept):
        if self.net is not None:
            self.net.send({"type": "invite_response", "target": sender, "accept": accept})

    # ---------- multiplayer: game flow ----------

    def begin_multiplayer_game(self, msg):
        self.stop_thinking_pulse()
        self.game_id += 1
        self.in_game = True
        self.multiplayer = True
        self.spectating = False
        self.reconnecting = False
        self.human_color = msg["color"]
        self.opponent_name = msg["opponent"]
        self.flipped = self.human_color == "b"
        self.position, self.selected, self.thinking, self.last_move = Position(), None, False, None
        color_label = "White" if self.human_color == "w" else "Black"
        self.game_subtitle.set(f"Playing {self.opponent_name} \u2014 you are {color_label}")
        self.lobby_frame.grid_remove()
        self.draw_offer_button.grid()
        self.game_frame.grid()
        self.root.title(f"Chess vs {self.opponent_name}")
        self.center_window()
        self.draw()

    def send_move_to_server(self, move):
        if self.net is not None:
            self.net.send({
                "type": "move",
                "start": list(move.start),
                "end": list(move.end),
                "promotion": move.promotion,
                "en_passant": move.en_passant,
                "castle": move.castle,
            })

    def apply_network_move(self, msg):
        if not self.in_game or not (self.multiplayer or self.spectating):
            return
        move = Move(
            start=tuple(msg["start"]),
            end=tuple(msg["end"]),
            promotion=msg.get("promotion"),
            en_passant=bool(msg.get("en_passant")),
            castle=bool(msg.get("castle")),
        )
        captured = self.position.board[move.end[0]][move.end[1]]
        self.position.apply(move)
        self.last_move = (move.start, move.end)
        self.thinking = True
        self.status.set("Moving...")
        self.play_move_sound(move, captured)
        self.animate_move(move, self.after_opponent_animation)

    def after_opponent_animation(self):
        self.thinking = False
        self.draw()

    def is_own(self, piece):
        if not piece:
            return False
        return piece.isupper() if self.human_color == "w" else piece.islower()

    def flip_coord(self, row, col):
        return (7 - row, 7 - col) if self.flipped else (row, col)

    def update_multiplayer_status(self):
        turn = self.position.turn
        moves = self.position.legal_moves(turn)
        if not moves:
            if self.net is not None:
                self.net.send({"type": "game_finished"})
            if self.position.in_check(turn):
                if turn != self.human_color:
                    self.record_result("multiplayer", "win")
                    self.finish("Checkmate! You win!")
                else:
                    self.record_result("multiplayer", "loss")
                    self.finish("Checkmate! You lose.")
            else:
                self.record_result("multiplayer", "draw")
                self.finish("Draw by stalemate.")
            return
        if turn == self.human_color:
            self.status.set("Your turn" + (" - check!" if self.position.in_check(turn) else ""))
        else:
            self.status.set(f"Waiting for {self.opponent_name}...")

    # ---------- multiplayer: reconnect ----------

    def begin_reconnect(self):
        self.reconnecting = True
        self.reconnect_attempts = 0
        self.thinking = True
        self.status.set("Connection lost. Reconnecting...")
        self.try_reconnect()

    def try_reconnect(self):
        if not self.reconnecting:
            return
        if self.net is not None:
            self.net.close()
        self.net_queue = queue.Queue()
        self.net = NetworkClient(SERVER_URL, self.net_queue)
        self.net.start()

    def schedule_reconnect_retry(self):
        self.reconnect_attempts += 1
        if self.reconnect_attempts > 10:
            self.reconnecting = False
            self.confirm_dialog(
                "Connection lost", "Couldn't reconnect to the game.",
                self.disconnect_multiplayer, confirm_text="OK", cancel_text="OK",
                on_cancel=self.disconnect_multiplayer,
            )
            return
        self.status.set(f"Reconnecting... (attempt {self.reconnect_attempts})")
        self.root.after(3000, self.try_reconnect)

    def resume_after_reconnect(self, msg):
        self.opponent_name = msg.get("opponent", self.opponent_name)
        self.human_color = msg["color"]
        self.flipped = self.human_color == "b"
        self.position = Position()
        self.last_move = None
        for mv in msg.get("move_history", []):
            move = Move(
                start=tuple(mv["start"]), end=tuple(mv["end"]),
                promotion=mv.get("promotion"), en_passant=bool(mv.get("en_passant")),
                castle=bool(mv.get("castle")),
            )
            self.position.apply(move)
            self.last_move = (move.start, move.end)
        self.selected = None
        self.thinking = False
        color_label = "White" if self.human_color == "w" else "Black"
        self.game_subtitle.set(f"Playing {self.opponent_name} \u2014 you are {color_label}")
        self.draw()

    # ---------- multiplayer: spectating ----------

    def begin_spectate(self, msg):
        self.stop_thinking_pulse()
        self.game_id += 1
        self.in_game = True
        self.multiplayer = False
        self.spectating = True
        self.human_color = "w"
        self.flipped = False
        self.spectate_white = msg["white"]
        self.spectate_black = msg["black"]
        self.position = Position()
        self.selected = None
        self.thinking = False
        self.last_move = None
        for mv in msg.get("move_history", []):
            move = Move(
                start=tuple(mv["start"]), end=tuple(mv["end"]),
                promotion=mv.get("promotion"), en_passant=bool(mv.get("en_passant")),
                castle=bool(mv.get("castle")),
            )
            self.position.apply(move)
            self.last_move = (move.start, move.end)
        self.game_subtitle.set(f"Watching {self.spectate_white} (White) vs {self.spectate_black} (Black)")
        self.lobby_frame.grid_remove()
        self.draw_offer_button.grid_remove()
        self.game_frame.grid()
        self.root.title(f"Chess - Watching {self.spectate_white} vs {self.spectate_black}")
        self.center_window()
        self.draw()

    def update_spectator_status(self):
        turn = self.position.turn
        moves = self.position.legal_moves(turn)
        if not moves:
            if self.position.in_check(turn):
                winner = "Black" if turn == "w" else "White"
                self.spectator_finish(f"Checkmate! {winner} wins.")
            else:
                self.spectator_finish("Draw by stalemate.")
            return
        to_move = self.spectate_white if turn == "w" else self.spectate_black
        self.status.set(f"{to_move} to move" + (" - check!" if self.position.in_check(turn) else ""))

    def spectator_finish(self, text):
        if not self.in_game:
            return
        self.in_game = False
        self.status.set(text)
        self.confirm_dialog(
            "Game over", text, self.leave_spectate,
            confirm_text="OK", cancel_text="OK", on_cancel=self.leave_spectate,
        )

    def leave_spectate(self):
        if self.net is not None:
            self.net.send({"type": "stop_spectate"})
        self.spectating = False
        self.in_game = False
        self.spectate_white = None
        self.spectate_black = None
        self.game_frame.grid_remove()
        self.lobby_frame.grid()
        self.root.title("Chess - Lobby")
        self.center_window()

    def show_menu(self):
        self.stop_thinking_pulse()
        self.game_id += 1
        self.in_game = False
        self.thinking = False
        self.game_frame.grid_remove()
        self.menu_frame.grid()
        self.root.title("Chess - Main Menu")
        self.center_window()

    def start_game(self):
        self.stop_thinking_pulse()
        self.game_id += 1
        self.in_game = True
        self.multiplayer = False
        self.flipped = False
        self.human_color = "w"
        self.game_subtitle.set("Play against an adjustable-strength bot")
        self.position, self.selected, self.thinking, self.last_move = Position(), None, False, None
        self.menu_frame.grid_remove()
        self.draw_offer_button.grid_remove()
        self.game_frame.grid()
        self.root.title("Tkinter Chess - Elo Bot")
        self.center_window()
        self.draw()

    def load_sounds(self):
        if sys.platform != "win32":
            return
        sound_dir = Path(__file__).resolve().parent / "chess"
        for name in ("move-self", "capture", "castle", "promote", "move-check", "game-end"):
            path = sound_dir / f"{name}.mp3"
            if path.exists():
                alias = name.replace("-", "_")
                command = f'open "{path}" type mpegvideo alias {alias}'
                ctypes.windll.winmm.mciSendStringW(command, None, 0, 0)
                self.sound_aliases[name] = alias

    def play_sound(self, name):
        if self.sound_enabled.get() and sys.platform == "win32" and name in self.sound_aliases:
            alias = self.sound_aliases[name]
            mci = ctypes.windll.winmm.mciSendStringW
            mci(f"stop {alias}", None, 0, 0)
            mci(f"seek {alias} to start", None, 0, 0)
            mci(f"play {alias}", None, 0, 0)

    def play_move_sound(self, move, captured):
        if move.promotion:
            sound = "promote"
        elif move.castle:
            sound = "castle"
        elif captured or move.en_passant:
            sound = "capture"
        elif self.position.in_check(self.position.turn):
            sound = "move-check"
        else:
            sound = "move-self"
        self.play_sound(sound)

    def close_sounds(self):
        if sys.platform == "win32":
            for alias in self.sound_aliases.values():
                ctypes.windll.winmm.mciSendStringW(f"close {alias}", None, 0, 0)

    def return_to_menu(self):
        if self.spectating:
            self.leave_spectate()
        elif self.multiplayer and self.in_game:
            self.confirm_dialog(
                "Leave game", "Resign this game and return to the menu?",
                self.leave_multiplayer_game,
            )
        elif self.multiplayer:
            # Game already concluded (e.g. waiting for a rematch response) -
            # nothing to resign and no result to record, just leave cleanly.
            self.disconnect_multiplayer()
        else:
            self.confirm_dialog(
                "Return to menu", "Leave this game and return to the main menu?", self.show_menu
            )

    def leave_multiplayer_game(self):
        if self.net is not None:
            self.net.send({"type": "resign"})
        self.record_result("multiplayer", "loss")
        self.disconnect_multiplayer()

    def propose_draw(self):
        if self.net is not None and self.multiplayer and self.in_game:
            self.net.send({"type": "draw_offer"})
            self.status.set("Draw offer sent, waiting for a response...")

    def respond_to_draw(self, accept):
        if self.net is not None:
            self.net.send({"type": "draw_response", "accept": accept})

    def propose_rematch(self):
        if self.net is not None:
            self.net.send({"type": "rematch_request"})
        self.status.set("Waiting for opponent to accept a rematch...")

    def respond_to_rematch(self, accept):
        if self.net is not None:
            self.net.send({"type": "rematch_response", "accept": accept})
        if not accept:
            self.disconnect_multiplayer()

    def center_window(self):
        self.root.update_idletasks()
        new_width = self.root.winfo_reqwidth()
        new_height = self.root.winfo_reqheight()
        if not self._window_positioned:
            # First-ever placement: center on the screen.
            self._window_positioned = True
            x = (self.root.winfo_screenwidth() - new_width) // 2
            y = (self.root.winfo_screenheight() - new_height) // 2
        else:
            # Every later resize: keep the window's current center point,
            # whether that's still screen-center or somewhere the user
            # dragged it to, instead of snapping back to the screen middle.
            center_x = self.root.winfo_x() + self.root.winfo_width() // 2
            center_y = self.root.winfo_y() + self.root.winfo_height() // 2
            x = center_x - new_width // 2
            y = center_y - new_height // 2
        self.root.geometry(f"{new_width}x{new_height}+{max(x, 0)}+{max(y, 0)}")

    def confirm_close(self):
        self.confirm_dialog("Exit chess", "Are you sure you want to close the game?", self.close_application)

    def close_application(self):
        self.close_sounds()
        self.root.destroy()

    def draw(self):
        self.update_material()
        size = 52
        offset_x, offset_y = 0, 0
        legal = (self.position.legal_moves(self.human_color)
                  if not self.thinking and self.position.turn == self.human_color else [])
        destinations = {m.end for m in legal if m.start == self.selected}
        check_square = None
        mate_winner_square = None
        for color in ("w", "b"):
            if self.position.in_check(color):
                check_square = self.position.find_king(color)
                if not self.position.legal_moves(color):
                    mate_winner_square = self.position.find_king("b" if color == "w" else "w")
                break
        self.board_canvas.delete("all")
        for r in range(8):
            for c in range(8):
                dr, dc = self.flip_coord(r, c)
                light, dark = (("#f0d9b5", "#b58863") if self.dark_mode.get()
                               else ("#f5f5f5", "#91a6b8"))
                base = light if (r + c) % 2 == 0 else dark
                if self.last_move and (r, c) in self.last_move:
                    base = (("#cdbd86", "#aa9860") if self.dark_mode.get()
                            else ("#ded5b5", "#a9bbc7"))[0 if (r + c) % 2 == 0 else 1]
                if (r, c) == self.selected:
                    base = "#e7c873" if self.dark_mode.get() else "#d8b866"
                elif (r, c) in destinations:
                    base = (
                        ("#d9e1ae", "#a7c27e") if self.dark_mode.get()
                        else ("#e3ead2", "#aec9c1")
                    )[0 if (r + c) % 2 == 0 else 1]
                elif self.hover_cell == (r, c) and self.is_own(self.position.board[r][c]):
                    base = "#f7e2b9" if (r + c) % 2 == 0 else "#c49a72"
                if (r, c) == check_square:
                    base = "#d9534f" if (r + c) % 2 == 0 else "#b5433f"
                if (r, c) == mate_winner_square:
                    base = "#5cb85c" if (r + c) % 2 == 0 else "#4a9d4a"
                self.board_canvas.create_rectangle(
                    offset_x + dc * size, offset_y + dr * size,
                    offset_x + (dc + 1) * size, offset_y + (dr + 1) * size,
                    fill=base, outline=base,
                )
                if self.show_coordinates.get():
                    label_color = dark if (r + c) % 2 == 0 else light
                    if dc == 0:
                        self.board_canvas.create_text(
                            offset_x + dc * size + 5, offset_y + dr * size + 5,
                            text=str(8 - r), anchor="nw",
                            font=("Segoe UI", 8, "bold"), fill=label_color,
                        )
                    if dr == 7:
                        self.board_canvas.create_text(
                            offset_x + (dc + 1) * size - 5, offset_y + (dr + 1) * size - 5,
                            text=chr(ord("a") + c), anchor="se",
                            font=("Segoe UI", 8, "bold"), fill=label_color,
                        )
                piece = self.position.board[r][c]
                if (r, c) not in self.animation_hidden and piece:
                    self.board_canvas.create_text(
                        offset_x + dc * size + size / 2, offset_y + dr * size + size / 2,
                        text=PIECE_SYMBOLS[piece],
                        font=("Segoe UI Symbol", max(18, int(size * 0.58))),
                        fill="#111" if piece.isupper() else "#222",
                    )
        # Force the board to actually repaint now, before a game-over dialog
        # (finish()) can grab focus and cover a canvas that Tk hasn't
        # gotten around to redrawing on screen yet.
        self.board_canvas.update_idletasks()
        if self.spectating:
            self.update_spectator_status()
        elif self.multiplayer:
            self.update_multiplayer_status()
        elif self.position.turn == "w" and not self.thinking:
            moves = self.position.legal_moves("w")
            self.status.set("Your turn" + (" - check!" if self.position.in_check("w") else ""))
            if not moves:
                if self.position.in_check("w"):
                    self.record_result("bot", "loss")
                    self.finish("Checkmate! The bot wins.")
                else:
                    self.record_result("bot", "draw")
                    self.finish("Draw by stalemate.")
        elif self.thinking:
            self.status.set("Bot is thinking...")

    def update_material(self):
        difference = 0
        for row in self.position.board:
            for piece in row:
                if piece and piece.upper() in MATERIAL_VALUES:
                    value = MATERIAL_VALUES[piece.upper()]
                    difference += value if piece.isupper() else -value
        self.material_text.set(f"{difference:+d}")

    def animate_move(self, move, on_complete):
        piece = self.position.board[move.end[0]][move.end[1]]
        self.animation_hidden = {move.start, move.end}
        self.draw()
        size = 52
        offset_x, offset_y = 0, 0
        start_r, start_c = self.flip_coord(*move.start)
        end_r, end_c = self.flip_coord(*move.end)
        flying = self.board_canvas.create_text(
            offset_x + start_c * size + size / 2,
            offset_y + start_r * size + size / 2,
            text=PIECE_SYMBOLS.get(piece, ""),
            font=("Segoe UI Symbol", max(18, int(size * 0.58))),
            fill="#111" if piece.isupper() else "#222",
        )

        def step(number=0):
            if not self.in_game:
                self.board_canvas.delete(flying)
                self.animation_hidden = set()
                return
            if number >= 8:
                self.board_canvas.delete(flying)
                self.animation_hidden = set()
                on_complete()
                return
            raw_progress = (number + 1) / 8
            progress = math.sin(raw_progress * math.pi / 2)
            x = offset_x + (start_c + (end_c - start_c) * progress) * size + size / 2
            y = offset_y + (start_r + (end_r - start_r) * progress) * size + size / 2
            self.board_canvas.coords(flying, x, y)
            self.root.after(12, lambda: step(number + 1))

        step()

    def update_elo(self, value):
        rating = round(float(value) / 100) * 100
        self.elo_text.set(f"{rating:.0f}")
        if rating < 1000:
            description = "Beginner"
        elif rating < 1600:
            description = "Club player"
        elif rating < 2000:
            description = "Advanced player"
        elif rating < 2200:
            description = "Candidate Master"
        elif rating < 2300:
            description = "FIDE Master"
        elif rating < 2400:
            description = "International Master"
        else:
            description = "Grandmaster"
        self.elo_description.set(description)

    def toggle_theme(self):
        dark = self.dark_mode.get()
        self.save_settings()
        colors = {
            "root": "#202124" if dark else "#f3f5f7",
            "panel": "#2b2d31" if dark else "#ffffff",
            "title": "#f1f3f4" if dark else "#1f2933",
            "muted": "#aeb4bd" if dark else "#52606d",
            "status": "#34373d" if dark else "#e8eef3",
            "status_fg": "#dbe7f5" if dark else "#243b53",
        }
        self.root.configure(bg=colors["root"])
        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("App.TFrame", background=colors["root"])
        style.configure("Panel.TFrame", background=colors["panel"])
        style.configure("Title.TLabel", background=colors["root"], foreground=colors["title"])
        style.configure("Muted.TLabel", background=colors["root"], foreground=colors["muted"])
        style.configure("Material.TLabel", background=colors["root"], foreground=colors["title"],
                        font=("Segoe UI", 14, "bold"))
        style.configure("Thinking.TLabel", background=colors["root"], foreground=colors["muted"])
        style.configure("Panel.TLabel", background=colors["panel"], foreground=colors["title"])
        style.configure("PanelMuted.TLabel", background=colors["panel"], foreground=colors["muted"])
        style.configure("StatsWin.TLabel", background=colors["panel"], foreground="#4caf50",
                        font=("Segoe UI", 10, "bold"))
        style.configure("StatsLoss.TLabel", background=colors["panel"], foreground="#e5534b",
                        font=("Segoe UI", 10, "bold"))
        style.configure("Status.TLabel", background=colors["status"], foreground=colors["status_fg"])
        style.configure("Panel.Horizontal.TScale", background=colors["panel"],
                        troughcolor="#17181a" if dark else "#c9d2d9")
        style.configure("Panel.TCheckbutton", background=colors["panel"], foreground=colors["title"])
        if hasattr(self, "lobby_canvas"):
            self.lobby_canvas.configure(bg=colors["panel"])
            self.lobby_scrollbar.configure(troughcolor=colors["panel"])
        style.configure("Theme.TCheckbutton", background=colors["root"], foreground=colors["title"])
        style.configure("Accent.TButton", background="#4b78a8" if dark else "#3d6f9e",
                        foreground="#ffffff", borderwidth=0)
        style.map("Accent.TButton", background=[("active", "#6196ca" if dark else "#578fc2")])
        style.configure("Menu.TButton", background="#4a4d52" if dark else "#e2e5e8",
                        foreground="#ffffff" if dark else "#243b53", borderwidth=0)
        style.map("Menu.TButton", background=[("active", "#5c6067" if dark else "#d2d7dc")])
        self.board_frame.configure(bg="#17181a" if dark else "#c9d2d9")
        self.apply_title_bar_theme()
        self.draw()

    def start_thinking_pulse(self):
        self.stop_thinking_pulse()
        self.pulse_job = self.root.after(0, self.pulse_thinking_label)

    def stop_thinking_pulse(self):
        if self.pulse_job is not None:
            self.root.after_cancel(self.pulse_job)
            self.pulse_job = None
        style = ttk.Style(self.root)
        style.configure("Thinking.TLabel", foreground="#aeb4bd" if self.dark_mode.get() else "#52606d")

    def pulse_thinking_label(self):
        if not self.in_game or not self.thinking or "thinking" not in self.status.get().lower():
            self.stop_thinking_pulse()
            return
        dark = self.dark_mode.get()
        full = (174, 180, 189) if dark else (82, 96, 109)
        dim = (104, 108, 113) if dark else (49, 58, 65)
        milliseconds = int(self.root.tk.call("clock", "milliseconds"))
        phase = (math.sin(milliseconds / 260) + 1) / 2
        color = tuple(round(dim[i] + (full[i] - dim[i]) * phase) for i in range(3))
        ttk.Style(self.root).configure(
            "Thinking.TLabel", foreground="#%02x%02x%02x" % color
        )
        self.pulse_job = self.root.after(35, self.pulse_thinking_label)

    def apply_title_bar_theme(self, window=None):
        if sys.platform != "win32":
            return
        window = window or self.root
        window.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(window.winfo_id())
        if not hwnd:
            hwnd = window.winfo_id()
        dark_value = ctypes.c_int(1 if self.dark_mode.get() else 0)
        attribute = 20
        result = ctypes.windll.dwmapi.DwmSetWindowAttribute(
            hwnd, attribute, ctypes.byref(dark_value), ctypes.sizeof(dark_value)
        )
        if result != 0:
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                hwnd, 19, ctypes.byref(dark_value), ctypes.sizeof(dark_value)
            )

    def hover(self, row, col, entering):
        if self.animation_hidden:
            return
        self.hover_cell = (row, col) if entering else None
        self.draw()

    def click_canvas(self, event):
        col = event.x // 52
        row = event.y // 52
        if 0 <= row < 8 and 0 <= col < 8:
            row, col = self.flip_coord(row, col)
            self.click(row, col)

    def motion_canvas(self, event):
        if self.animation_hidden:
            return
        col = event.x // 52
        row = event.y // 52
        if 0 <= row < 8 and 0 <= col < 8:
            row, col = self.flip_coord(row, col)
            if self.hover_cell != (row, col):
                self.hover(row, col, True)

    def clear_hover(self):
        if self.hover_cell is not None:
            self.hover(None, None, False)

    def click(self, row, col):
        if self.spectating or not self.in_game or self.thinking or self.position.turn != self.human_color:
            return
        piece = self.position.board[row][col]
        legal = self.position.legal_moves(self.human_color)
        if self.selected is None:
            if self.is_own(piece):
                self.selected = (row, col)
        else:
            choices = [m for m in legal if m.start == self.selected and m.end == (row, col)]
            if choices:
                if len(choices) > 1:
                    self.selected = None
                    self.draw()
                    self.show_promotion_picker(choices)
                    return
                self.commit_move(choices[0])
                return
            elif self.is_own(piece):
                self.selected = (row, col)
            else:
                self.selected = None
        self.draw()

    def commit_move(self, move):
        captured = self.position.board[move.end[0]][move.end[1]]
        self.position.apply(move)
        self.last_move = (move.start, move.end)
        self.selected = None
        self.thinking = True
        self.status.set("Moving...")
        self.play_move_sound(move, captured)
        if self.multiplayer:
            self.send_move_to_server(move)
        self.animate_move(move, self.after_human_animation)

    def show_promotion_picker(self, choices):
        dark = self.dark_mode.get()
        dialog = tk.Toplevel(self.root)
        dialog.title("Promote to")
        dialog.configure(bg="#202124" if dark else "#f3f5f7")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        text_color = "#f1f3f4" if dark else "#1f2933"
        tk.Label(dialog, text="Promote to:", bg=dialog.cget("bg"), fg=text_color,
                 font=("Segoe UI", 10), padx=24, pady=(20, 10)).pack()
        buttons = tk.Frame(dialog, bg=dialog.cget("bg"))
        buttons.pack(padx=24, pady=(0, 20))

        button_bg = "#4a4d52" if dark else "#e2e5e8"
        button_active = "#5c6067" if dark else "#d2d7dc"
        piece_color = "#ffffff" if dark else "#1f2933"
        order = {"Q": 0, "R": 1, "B": 2, "N": 3}
        for move in sorted(choices, key=lambda m: order.get(m.promotion, 9)):
            piece_letter = move.promotion if self.human_color == "w" else move.promotion.lower()

            def pick(m=move):
                dialog.grab_release()
                dialog.destroy()
                self.commit_move(m)

            tk.Button(buttons, text=PIECE_SYMBOLS[piece_letter], font=("Segoe UI Symbol", 26),
                      width=2, bg=button_bg, fg=piece_color, activebackground=button_active,
                      activeforeground=piece_color, relief="flat", bd=0,
                      command=pick).pack(side="left", padx=4)

        def close():
            dialog.grab_release()
            dialog.destroy()

        dialog.protocol("WM_DELETE_WINDOW", close)
        dialog.bind("<Escape>", lambda event: close())
        dialog.update_idletasks()
        self.apply_title_bar_theme(dialog)
        x = self.root.winfo_x() + (self.root.winfo_width() - dialog.winfo_width()) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - dialog.winfo_height()) // 2
        dialog.geometry(f"+{max(x, 0)}+{max(y, 0)}")

    def after_human_animation(self):
        if self.multiplayer:
            self.thinking = False
            self.draw()
            return
        self.draw()
        black_moves = self.position.legal_moves("b")
        if black_moves:
            self.status.set("Bot is thinking...")
            self.start_thinking_pulse()
            self.root.after(120, self.bot_move)
        else:
            self.thinking = False
            self.stop_thinking_pulse()
            if self.position.in_check("b"):
                self.record_result("bot", "win")
                self.finish("You win by checkmate!")
            else:
                self.record_result("bot", "draw")
                self.finish("Draw by stalemate.")

    def bot_move(self):
        if not self.in_game:
            return
        moves = self.position.legal_moves("b")
        if not moves:
            self.thinking = False
            self.stop_thinking_pulse()
            if self.position.in_check("b"):
                self.record_result("bot", "win")
                self.finish("You win by checkmate!")
            else:
                self.record_result("bot", "draw")
                self.finish("Draw by stalemate.")
            return
        elo = self.elo.get()
        depth = 1 if elo < 800 else 2 if elo < 1200 else 3 if elo < 2000 else 4
        position = self.position.copy()
        current_game = self.game_id
        threading.Thread(
            target=self.calculate_bot_move,
            args=(position, moves, depth, elo, current_game),
            daemon=True,
        ).start()
        self.root.after(50, self.poll_bot_result)

    def calculate_bot_move(self, position, moves, depth, elo, current_game):
        scored = [(self.search_move(move, depth, position), move) for move in moves]
        scored.sort(key=lambda item: item[0], reverse=True)
        noise = max(0, (1700 - elo) / 5)
        pool = [item for item in scored if item[0] >= scored[0][0] - noise]
        chosen_move = random.choice(pool)[1]
        self.bot_results.put((chosen_move, current_game))

    def poll_bot_result(self):
        if not self.in_game:
            return
        try:
            chosen_move, current_game = self.bot_results.get_nowait()
        except queue.Empty:
            self.root.after(50, self.poll_bot_result)
            return
        self.apply_bot_move(chosen_move, current_game)

    def apply_bot_move(self, chosen_move, current_game):
        if not self.in_game or current_game != self.game_id or self.position.turn != "b":
            return
        self.stop_thinking_pulse()
        captured = self.position.board[chosen_move.end[0]][chosen_move.end[1]]
        self.position.apply(chosen_move)
        self.last_move = (chosen_move.start, chosen_move.end)
        self.status.set("Moving...")
        self.play_move_sound(chosen_move, captured)
        self.animate_move(chosen_move, self.after_bot_animation)

    def after_bot_animation(self):
        self.thinking = False
        self.stop_thinking_pulse()
        self.draw()

    def search_move(self, move, depth, position=None):
        test = (position or self.position).copy()
        test.apply(move)
        return self.minimax(test, depth - 1, -math.inf, math.inf)

    def minimax(self, position, depth, alpha, beta):
        moves = position.legal_moves()
        if not moves:
            if position.in_check(position.turn):
                return -100000 if position.turn == "b" else 100000
            return 0
        if depth == 0:
            return self.quiescence(position, alpha, beta, 0)
        maximizing = position.turn == "b"
        best = -math.inf if maximizing else math.inf
        moves.sort(
            key=lambda move: VALUES.get(
                position.board[move.end[0]][move.end[1]].upper(), 0
            ),
            reverse=True,
        )
        for move in moves:
            child = position.copy()
            child.apply(move)
            score = self.minimax(child, depth - 1, alpha, beta)
            if maximizing:
                best, alpha = max(best, score), max(alpha, best)
            else:
                best, beta = min(best, score), min(beta, best)
            if beta <= alpha:
                break
        return best

    def quiescence(self, position, alpha, beta, depth):
        stand_pat = self.evaluate(position)
        maximizing = position.turn == "b"
        if depth >= 3:
            return stand_pat
        captures = [
            move for move in position.legal_moves()
            if position.board[move.end[0]][move.end[1]] or move.en_passant
        ]
        captures.sort(
            key=lambda move: VALUES.get(
                position.board[move.end[0]][move.end[1]].upper(), 0
            ),
            reverse=True,
        )
        if maximizing:
            if stand_pat >= beta:
                return stand_pat
            alpha = max(alpha, stand_pat)
            for move in captures:
                child = position.copy()
                child.apply(move)
                alpha = max(alpha, self.quiescence(child, alpha, beta, depth + 1))
                if alpha >= beta:
                    break
            return alpha
        if stand_pat <= alpha:
            return stand_pat
        beta = min(beta, stand_pat)
        for move in captures:
            child = position.copy()
            child.apply(move)
            beta = min(beta, self.quiescence(child, alpha, beta, depth + 1))
            if beta <= alpha:
                break
        return beta

    @staticmethod
    def evaluate(position):
        score = 0
        for row_index, row in enumerate(position.board):
            for col_index, piece in enumerate(row):
                if piece:
                    value = VALUES[piece.upper()]
                    score += value if piece.islower() else -value
                    center = 4 - abs(3.5 - col_index) + 4 - abs(3.5 - row_index)
                    if piece.upper() in "N B Q".split():
                        score += round(center * 4) if piece.islower() else -round(center * 4)
                    if piece.upper() == "P":
                        advance = (6 - row_index) if piece.isupper() else (row_index - 1)
                        score += advance * -2 if piece.isupper() else advance * 2
        return score

    def new_game(self):
        self.stop_thinking_pulse()
        self.game_id += 1
        self.position, self.selected, self.thinking, self.last_move = Position(), None, False, None
        self.draw()

    def finish(self, text):
        if not self.in_game:
            return
        self.in_game = False
        self.status.set(text)
        self.play_sound("game-end")
        if self.multiplayer:
            self.confirm_dialog(
                "Game over", f"{text}\n\nRematch, or return to the menu?",
                self.propose_rematch, confirm_text="Rematch", cancel_text="Menu",
                on_cancel=self.disconnect_multiplayer,
            )
        else:
            self.confirm_dialog(
                "Game over", f"{text}\n\nWould you like to exit or return to the menu?",
                self.root.destroy, confirm_text="Exit", cancel_text="Menu",
                on_cancel=self.show_menu,
            )

    def confirm_dialog(self, title, message, on_confirm, confirm_text="Yes",
                       cancel_text="No", on_cancel=None):
        dark = self.dark_mode.get()
        dialog = tk.Toplevel(self.root)
        dialog.title(title)
        dialog.configure(bg="#202124" if dark else "#f3f5f7")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        text_color = "#f1f3f4" if dark else "#1f2933"
        tk.Label(dialog, text=message, justify="left", wraplength=320,
                 bg=dialog.cget("bg"), fg=text_color, font=("Segoe UI", 10),
                 padx=24, pady=20).pack()
        buttons = tk.Frame(dialog, bg=dialog.cget("bg"))
        buttons.pack(fill="x", padx=24, pady=(0, 20))

        def close():
            dialog.grab_release()
            dialog.destroy()

        def cancel():
            close()
            if on_cancel is not None:
                on_cancel()

        def confirm():
            close()
            on_confirm()

        button_bg = "#4a4d52" if dark else "#e2e5e8"
        button_active = "#5c6067" if dark else "#d2d7dc"
        button_fg = "#ffffff" if dark else "#243b53"
        tk.Button(buttons, text=cancel_text, width=9, bg=button_bg, fg=button_fg,
                  activebackground=button_active, activeforeground=button_fg,
                  relief="flat", bd=0, command=cancel).pack(side="right")
        tk.Button(buttons, text=confirm_text, width=9, bg=button_bg, fg=button_fg,
                  activebackground=button_active, activeforeground=button_fg,
                  relief="flat", bd=0, command=confirm).pack(side="right", padx=(0, 8))
        dialog.protocol("WM_DELETE_WINDOW", close)
        dialog.bind("<Escape>", lambda event: close())
        dialog.update_idletasks()
        self.apply_title_bar_theme(dialog)
        x = self.root.winfo_x() + (self.root.winfo_width() - dialog.winfo_width()) // 2
        y = self.root.winfo_y() + (self.root.winfo_height() - dialog.winfo_height()) // 2
        dialog.geometry(f"+{max(x, 0)}+{max(y, 0)}")


if __name__ == "__main__":
    app_root = tk.Tk()
    ChessApp(app_root)
    app_root.mainloop()