import json
import time
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import traceback
import os
import sys


def resource_path(relative_path):
    """Return an absolute path for development and PyInstaller builds."""
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

# --- Input driver (pydirectinput preferred for games) ---
try:
    import pydirectinput as input_driver
    PYDIRECT_AVAILABLE = True
    input_driver.PAUSE = 0
except Exception:
    import pyautogui as input_driver
    PYDIRECT_AVAILABLE = False
    input_driver.PAUSE = 0
    input_driver.MINIMUM_DURATION = 0
    input_driver.MINIMUM_SLEEP = 0

try:
    import keyboard
    KEYBOARD_AVAILABLE = True
except Exception:
    KEYBOARD_AVAILABLE = False

# --- Mouse listener for toggle hotkey/button ---
try:
    from pynput import mouse as pynput_mouse
    MOUSE_AVAILABLE = True
except Exception:
    pynput_mouse = None
    MOUSE_AVAILABLE = False


class MacroApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Simple Macro Recorder")

        # Apply dark theme BEFORE building UI widgets
        self._apply_dark_theme()

        self.recording = False

        # Unlimited macro library. self.events always points to the active macro's list.
        self.macros = [
            {
                "name": "Macro 1",
                "events": [],
                "toggle": "f8",
                "repeat_enabled": False,
                "hold_to_repeat": False,
                "repeat_delay_ms": 0,
                "speed": 1.0,
            }
        ]
        self.active_macro_index = 0
        self.events = self.macros[0]["events"]
        self._last_time = None

        self._play_thread = None
        self._stop_playback = threading.Event()
        self._independent_threads = []

        self._held_keys = set()
        self._held_keys_lock = threading.Lock()

        self._play_session_id = 0

        self._edit_entry = None
        self._edit_iid = None
        self._edit_field = None  # "key" or "delay_ms"

        self.ignore_keys = {"f9", "f10", "esc"}
        self.use_hotkeys = tk.BooleanVar(value=True)
        self.playback_speed = tk.DoubleVar(value=1.0)

        self.play_toggle_key = tk.StringVar(value=self.macros[0]["toggle"])

        self.repeat_enabled = tk.BooleanVar(value=False)
        self.hold_to_repeat = tk.BooleanVar(value=False)
        self.repeat_delay_ms = tk.IntVar(value=0)

        # Index of the macro currently being held for hold-to-repeat playback.
        self._held_toggle_macro_index = None

        self._capturing_toggle_key = False

        self.toggle_scan_code = None
        self.toggle_key_name = None
        self.toggle_mouse_button = None
        self._toggle_pressed_guard = False
        self._mouse_listener = None
        self._mouse_controller = pynput_mouse.Controller() if MOUSE_AVAILABLE else None

        # Prevent the Record/Stop button's own left-click from becoming a macro step.
        self._ignore_next_left_click = False
        self._resolve_toggle_key()

        self._build_ui()
        self._load_active_macro()

        if KEYBOARD_AVAILABLE:
            keyboard.hook(self._on_key_event)
            self._setup_hotkeys()
        else:
            self.use_hotkeys.set(False)
            self._set_status("keyboard module not available. Recording hotkeys disabled.")

        if MOUSE_AVAILABLE:
            self._start_mouse_listener()
        else:
            self._set_status("pynput mouse listener not available. Mouse toggle disabled.")

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------------- Dark theme ----------------

    def _apply_dark_theme(self):
        dark_bg = "#1e1e1e"
        panel_bg = "#252526"
        text_fg = "#e6e6e6"
        accent = "#3a3d41"
        select_bg = "#2d5d9f"
        entry_bg = "#2b2b2b"

        self._dark = {
            "dark_bg": dark_bg,
            "panel_bg": panel_bg,
            "text_fg": text_fg,
            "accent": accent,
            "select_bg": select_bg,
            "entry_bg": entry_bg,
        }

        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        self.root.configure(bg=dark_bg)

        style.configure("TFrame", background=dark_bg)
        style.configure("TLabelframe", background=dark_bg, foreground=text_fg)
        style.configure("TLabelframe.Label", background=dark_bg, foreground=text_fg)
        style.configure("TLabel", background=dark_bg, foreground=text_fg)
        style.configure("TButton", background=accent, foreground=text_fg, borderwidth=1)
        style.map(
            "TButton",
            background=[("active", "#4a4d52")],
            foreground=[("disabled", "#808080")]
        )

        style.configure("TCheckbutton", background=dark_bg, foreground=text_fg)
        style.map(
            "TCheckbutton",
            foreground=[("disabled", "#808080")],
            background=[("active", dark_bg)]
        )

        style.configure("TScale", background=dark_bg)
        style.configure("TEntry", fieldbackground=entry_bg, foreground=text_fg, background=entry_bg)

        style.configure(
            "Treeview",
            background=panel_bg,
            fieldbackground=panel_bg,
            foreground=text_fg,
            rowheight=24,
            bordercolor=accent,
            lightcolor=accent,
            darkcolor=accent
        )

        style.configure(
            "Treeview.Heading",
            background=accent,
            foreground=text_fg,
            relief="flat"
        )

        style.map(
            "Treeview",
            background=[("selected", select_bg)],
            foreground=[("selected", "#ffffff")]
        )
        style.map(
            "Treeview.Heading",
            background=[("active", "#4a4d52")]
        )

    # ---------------- Helpers ----------------

    @staticmethod
    def sec_to_ms_int(seconds: float) -> int:
        return int(round(max(0.0, float(seconds)) * 1000.0))

    @staticmethod
    def ms_int_to_sec(ms: int) -> float:
        return max(0, int(ms)) / 1000.0

    def _resolve_toggle_key(self):
        val = str(self.play_toggle_key.get()).strip().lower()
        self.toggle_scan_code = None
        self.toggle_key_name = None
        self.toggle_mouse_button = None

        if val.startswith("scan:"):
            try:
                self.toggle_scan_code = int(val.split(":", 1)[1])
            except Exception:
                self.toggle_scan_code = None
        elif val.startswith("mouse:"):
            btn = val.split(":", 1)[1].strip()
            # Security limitation: the primary left mouse button is never
            # allowed as a playback toggle because ordinary UI clicks could
            # unexpectedly start or stop the macro.
            if btn in ("right", "middle", "x1", "x2"):
                self.toggle_mouse_button = btn
        elif val:
            self.toggle_key_name = val

    def _mode_label(self, mode: str) -> str:
        return "IND" if mode == "ind" else "SEQ"

    def _log_error(self, where: str, exc: BaseException):
        try:
            with open("macro_errors.log", "a", encoding="utf-8") as f:
                f.write("\n" + "=" * 60 + "\n")
                f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')}  [{where}]\n")
                f.write("".join(traceback.format_exception(type(exc), exc, exc.__traceback__)))
        except Exception:
            pass

    def _mouse_button_name(self, button):
        try:
            s = str(button).lower()
        except Exception:
            return None

        if s.endswith(".left"):
            return "left"
        if s.endswith(".right"):
            return "right"
        if s.endswith(".middle"):
            return "middle"
        if "x1" in s or "button8" in s:
            return "x1"
        if "x2" in s or "button9" in s:
            return "x2"

        return None

    @staticmethod
    def _is_mouse_input(input_name: str) -> bool:
        return str(input_name).lower().startswith("mouse:")

    def _pynput_mouse_button(self, input_name: str):
        if not MOUSE_AVAILABLE:
            return None

        name = str(input_name).lower().split(":", 1)[-1]
        mapping = {
            "left": pynput_mouse.Button.left,
            "right": pynput_mouse.Button.right,
            "middle": pynput_mouse.Button.middle,
        }

        if name == "x1":
            return getattr(pynput_mouse.Button, "x1", None) or getattr(
                pynput_mouse.Button, "button8", None
            )
        if name == "x2":
            return getattr(pynput_mouse.Button, "x2", None) or getattr(
                pynput_mouse.Button, "button9", None
            )

        return mapping.get(name)

    def _record_input_step(self, input_name: str):
        t = time.perf_counter()
        delay_sec = t - (self._last_time if self._last_time is not None else t)
        self._last_time = t

        input_name = str(input_name).strip().lower()
        self.events.append({"key": input_name, "delay": float(delay_sec), "mode": "seq"})
        idx = len(self.events)
        delay_ms = self.sec_to_ms_int(delay_sec)

        self.root.after(
            0,
            lambda i=idx, k=input_name, ms=delay_ms: self.tree.insert(
                "", "end", values=(f"{i:03d}", k, str(ms), "SEQ")
            )
        )

    def _active_macro(self):
        return self.macros[self.active_macro_index]

    def _store_active_macro(self):
        macro = self._active_macro()
        macro["events"] = self.events
        macro["toggle"] = str(self.play_toggle_key.get()).strip().lower() or "none"
        macro["repeat_enabled"] = bool(self.repeat_enabled.get())
        macro["hold_to_repeat"] = bool(self.hold_to_repeat.get())

        try:
            macro["repeat_delay_ms"] = max(0, int(self.repeat_delay_ms.get()))
        except Exception:
            macro["repeat_delay_ms"] = 0

        try:
            macro["speed"] = max(0.25, min(3.0, float(self.playback_speed.get())))
        except Exception:
            macro["speed"] = 1.0

    def _load_active_macro(self):
        macro = self._active_macro()
        self.events = macro["events"]
        self.play_toggle_key.set(macro.get("toggle", "none"))
        self.repeat_enabled.set(bool(macro.get("repeat_enabled", False)))
        self.hold_to_repeat.set(bool(macro.get("hold_to_repeat", False)))
        self.repeat_delay_ms.set(max(0, int(macro.get("repeat_delay_ms", 0))))
        self.playback_speed.set(float(macro.get("speed", 1.0)))

        if hasattr(self, "speed_val"):
            self.speed_val.config(text=f"{float(self.playback_speed.get()):.2f}×")

        self._resolve_toggle_key()
        self._refresh_tree()

    def _refresh_tree(self):
        if not hasattr(self, "tree"):
            return

        for iid in self.tree.get_children():
            self.tree.delete(iid)

        for i, ev in enumerate(self.events, start=1):
            self.tree.insert(
                "",
                "end",
                values=(
                    f"{i:03d}",
                    ev["key"],
                    str(self.sec_to_ms_int(ev["delay"])),
                    self._mode_label(ev.get("mode", "seq")),
                ),
            )

        self._set_status(
            f"Editing {self._active_macro()['name']} — {len(self.events)} step(s)."
        )

    def _refresh_macro_selector(self):
        names = [macro["name"] for macro in self.macros]
        self.macro_selector["values"] = names
        self.macro_selector.current(self.active_macro_index)

    def _next_macro_name(self):
        used = {macro["name"] for macro in self.macros}
        number = 1
        while f"Macro {number}" in used:
            number += 1
        return f"Macro {number}"

    def add_macro(self):
        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before adding a macro.")
            return

        self._store_active_macro()
        new_name = self._next_macro_name()

        self.macros.append(
            {
                "name": new_name,
                "events": [],
                "toggle": "none",
                "repeat_enabled": False,
                "hold_to_repeat": False,
                "repeat_delay_ms": 0,
                "speed": 1.0,
            }
        )

        self.active_macro_index = len(self.macros) - 1
        self._refresh_macro_selector()
        self._load_active_macro()
        self.rename_active_macro()

    def rename_active_macro(self):
        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before renaming a macro.")
            return

        current = self._active_macro()["name"]
        new_name = simpledialog.askstring(
            "Rename macro",
            "Macro name:",
            initialvalue=current,
            parent=self.root,
        )
        if new_name is None:
            return

        new_name = new_name.strip()
        if not new_name:
            messagebox.showerror("Invalid name", "Macro name cannot be empty.")
            return

        if any(
            i != self.active_macro_index and macro["name"].lower() == new_name.lower()
            for i, macro in enumerate(self.macros)
        ):
            messagebox.showerror("Duplicate name", "Another macro already uses that name.")
            return

        self._active_macro()["name"] = new_name
        self._refresh_macro_selector()
        self._set_status(f"Renamed macro to {new_name}.")

    def delete_active_macro(self):
        if len(self.macros) <= 1:
            messagebox.showinfo("Required", "At least one macro must remain.")
            return

        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before deleting a macro.")
            return

        name = self._active_macro()["name"]
        if not messagebox.askyesno("Delete macro", f'Delete "{name}"?'):
            return

        del self.macros[self.active_macro_index]
        self.active_macro_index = min(self.active_macro_index, len(self.macros) - 1)
        self._refresh_macro_selector()
        self._load_active_macro()

    def duplicate_active_macro(self):
        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before duplicating a macro.")
            return

        self._store_active_macro()
        source = self._active_macro()
        base = f"{source['name']} Copy"
        name = base
        suffix = 2
        used = {macro["name"].lower() for macro in self.macros}

        while name.lower() in used:
            name = f"{base} {suffix}"
            suffix += 1

        duplicate = {
            "name": name,
            "events": [dict(ev) for ev in source["events"]],
            "toggle": "none",
            "repeat_enabled": bool(source.get("repeat_enabled", False)),
            "hold_to_repeat": bool(source.get("hold_to_repeat", False)),
            "repeat_delay_ms": int(source.get("repeat_delay_ms", 0)),
            "speed": float(source.get("speed", 1.0)),
        }

        self.macros.append(duplicate)
        self.active_macro_index = len(self.macros) - 1
        self._refresh_macro_selector()
        self._load_active_macro()

    def switch_macro(self, _event=None):
        if self.recording or self._is_playing():
            self.macro_selector.current(self.active_macro_index)
            messagebox.showwarning("Busy", "Stop recording or playback before switching macros.")
            return

        new_index = self.macro_selector.current()
        if new_index < 0 or new_index == self.active_macro_index:
            return

        self._store_active_macro()
        self.active_macro_index = new_index
        self._load_active_macro()

    @staticmethod
    def _parse_toggle(toggle_value: str):
        value = str(toggle_value).strip().lower()

        if value.startswith("scan:"):
            try:
                return "scan", int(value.split(":", 1)[1])
            except Exception:
                return "none", None

        if value.startswith("mouse:"):
            return "mouse", value.split(":", 1)[1].strip()

        if value and value != "none":
            return "key", value

        return "none", None

    def _find_macro_for_keyboard_event(self, event):
        event_name = (event.name or "").lower()
        event_scan = getattr(event, "scan_code", None)

        for index, macro in enumerate(self.macros):
            kind, value = self._parse_toggle(macro.get("toggle", "none"))

            if kind == "scan" and event_scan == value:
                return index

            if kind == "key" and event_name == value:
                return index

        return None

    def _find_macro_for_mouse_button(self, button_name: str):
        wanted = f"mouse:{button_name}"

        if wanted == "mouse:left":
            return None

        for index, macro in enumerate(self.macros):
            if macro.get("toggle", "none") == wanted:
                return index

        return None

    def _macro_uses_hold_to_repeat(self, macro_index: int) -> bool:
        return (
            0 <= macro_index < len(self.macros)
            and bool(self.macros[macro_index].get("hold_to_repeat", False))
        )

    def start_held_macro(self, macro_index: int):
        if not (0 <= macro_index < len(self.macros)):
            return
        if self.recording:
            return

        # Ignore key-repeat/autorepeat down events while the same toggle is held.
        if self._held_toggle_macro_index == macro_index:
            return

        if self._is_playing():
            self.stop_playback()

        if macro_index != self.active_macro_index:
            self._store_active_macro()
            self.active_macro_index = macro_index
            self._refresh_macro_selector()
            self._load_active_macro()

        self._held_toggle_macro_index = macro_index
        self.play_macro()

    def stop_held_macro(self, macro_index: int):
        if self._held_toggle_macro_index != macro_index:
            return
        self._held_toggle_macro_index = None
        self.stop_playback()

    def toggle_macro_by_index(self, macro_index: int):
        if not (0 <= macro_index < len(self.macros)):
            return

        if self._is_playing():
            self.stop_playback()
            return

        if self.recording:
            return

        if macro_index != self.active_macro_index:
            self._store_active_macro()
            self.active_macro_index = macro_index
            self._refresh_macro_selector()
            self._load_active_macro()

        self.play_macro()

    # ---------------- UI ----------------

    def _build_ui(self):
        frm = ttk.Frame(self.root, padding=10)
        frm.grid(row=0, column=0, sticky="nsew")
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)
        frm.rowconfigure(4, weight=1)

        # Main actions: the controls used most often are kept together.
        actions = ttk.LabelFrame(frm, text="Macro controls", padding=8)
        actions.grid(row=0, column=0, sticky="ew")

        self.btn_record = ttk.Button(
            actions,
            text="● Record",
            command=self._record_button_clicked
        )
        self.btn_record.grid(row=0, column=0, padx=(0, 6))

        self.btn_play = ttk.Button(actions, text="▶ Play", command=self.play_macro)
        self.btn_play.grid(row=0, column=1, padx=(0, 6))

        self.btn_stop = ttk.Button(actions, text="■ Stop", command=self.stop_playback)
        self.btn_stop.grid(row=0, column=2, padx=(0, 14))

        ttk.Separator(actions, orient="vertical").grid(row=0, column=3, sticky="ns", padx=(0, 14))

        ttk.Button(actions, text="Load", command=self.load_macro).grid(row=0, column=4, padx=(0, 6))
        ttk.Button(actions, text="Save", command=self.save_macro).grid(row=0, column=5, padx=(0, 6))
        ttk.Button(actions, text="Clear", command=self.clear_macro).grid(row=0, column=6)

        library = ttk.LabelFrame(frm, text="Macro library", padding=8)
        library.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        library.columnconfigure(0, weight=1)

        self.macro_selector = ttk.Combobox(
            library,
            state="readonly",
            values=[macro["name"] for macro in self.macros],
        )
        self.macro_selector.grid(row=0, column=0, sticky="ew", padx=(0, 6))
        self.macro_selector.current(self.active_macro_index)
        self.macro_selector.bind("<<ComboboxSelected>>", self.switch_macro)

        ttk.Button(library, text="+ New", command=self.add_macro).grid(
            row=0, column=1, padx=(0, 6)
        )
        ttk.Button(library, text="Rename", command=self.rename_active_macro).grid(
            row=0, column=2, padx=(0, 6)
        )
        ttk.Button(library, text="Duplicate", command=self.duplicate_active_macro).grid(
            row=0, column=3, padx=(0, 6)
        )
        ttk.Button(library, text="Delete", command=self.delete_active_macro).grid(
            row=0, column=4
        )

        # Playback settings are stored separately for every macro.
        settings = ttk.LabelFrame(frm, text="Playback settings", padding=8)
        settings.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        settings.columnconfigure(1, weight=1)

        ttk.Label(settings, text="Speed").grid(row=0, column=0, sticky="w")
        self.speed = ttk.Scale(
            settings, from_=0.25, to=3.0,
            variable=self.playback_speed, orient="horizontal"
        )
        self.speed.grid(row=0, column=1, sticky="ew", padx=(8, 6))
        self.speed_val = ttk.Label(settings, text="1.00×", width=6, anchor="center")
        self.speed_val.grid(row=0, column=2, sticky="w")
        self.speed.configure(command=lambda value: self.speed_val.config(text=f"{float(value):.2f}×"))

        self.chk_repeat = ttk.Checkbutton(
            settings, text="Repeat sequence", variable=self.repeat_enabled
        )
        self.chk_repeat.grid(row=1, column=0, sticky="w", pady=(8, 0))

        self.chk_hold_repeat = ttk.Checkbutton(
            settings,
            text="Repeat while holding toggle",
            variable=self.hold_to_repeat
        )
        self.chk_hold_repeat.grid(row=2, column=0, sticky="w", pady=(8, 0))

        ttk.Label(settings, text="Repeat delay").grid(row=2, column=1, sticky="e", pady=(8, 0))
        self.repeat_delay_entry = ttk.Entry(settings, textvariable=self.repeat_delay_ms, width=8, justify="center")
        self.repeat_delay_entry.grid(row=2, column=2, sticky="w", padx=(8, 0), pady=(8, 0))
        ttk.Label(settings, text="ms").grid(row=2, column=3, sticky="w", padx=(4, 0), pady=(8, 0))

        hotkeys = ttk.LabelFrame(frm, text="Hotkeys", padding=8)
        hotkeys.grid(row=3, column=0, sticky="ew", pady=(8, 0))
        hotkeys.columnconfigure(1, weight=1)

        self.chk_hotkeys = ttk.Checkbutton(
            hotkeys,
            text="Enable F9 record, F10 play and Esc stop",
            variable=self.use_hotkeys,
            command=self._hotkeys_toggled
        )
        self.chk_hotkeys.grid(row=0, column=0, columnspan=4, sticky="w")

        ttk.Label(hotkeys, text="Play toggle").grid(row=1, column=0, sticky="w", pady=(8, 0))
        self.toggle_entry = ttk.Entry(
            hotkeys,
            textvariable=self.play_toggle_key,
            width=16,
            justify="center",
            state="readonly"
        )
        self.toggle_entry.grid(row=1, column=1, sticky="w", padx=(8, 6), pady=(8, 0))

        ttk.Button(
            hotkeys,
            text="Press a key…",
            command=self.capture_toggle_hotkey
        ).grid(row=1, column=2, pady=(8, 0))

        # Step editor with a dedicated editing toolbar.
        list_frame = ttk.LabelFrame(frm, text="Recorded steps", padding=8)
        list_frame.grid(row=4, column=0, sticky="nsew", pady=(8, 0))
        list_frame.rowconfigure(1, weight=1)
        list_frame.columnconfigure(0, weight=1)

        editbar = ttk.Frame(list_frame)
        editbar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 6))

        ttk.Button(editbar, text="Edit key", command=self.edit_selected_key).grid(row=0, column=0, padx=(0, 5))
        ttk.Button(editbar, text="Edit delay", command=self.edit_selected_delay).grid(row=0, column=1, padx=(0, 5))
        ttk.Button(editbar, text="SEQ / IND", command=self.toggle_selected_mode).grid(row=0, column=2, padx=(0, 12))
        ttk.Button(editbar, text="↑", width=3, command=lambda: self.move_selected_step(-1)).grid(row=0, column=3, padx=(0, 4))
        ttk.Button(editbar, text="↓", width=3, command=lambda: self.move_selected_step(1)).grid(row=0, column=4, padx=(0, 4))
        ttk.Button(editbar, text="Duplicate", command=self.duplicate_selected_step).grid(row=0, column=5, padx=(0, 5))
        ttk.Button(editbar, text="Delete", command=self.delete_selected_step).grid(row=0, column=6)

        columns = ("step", "key", "delay_ms", "mode")
        self.tree = ttk.Treeview(
            list_frame, columns=columns, show="headings",
            selectmode="browse", height=12
        )
        self.tree.heading("step", text="#")
        self.tree.heading("key", text="Key")
        self.tree.heading("delay_ms", text="Delay")
        self.tree.heading("mode", text="Mode")

        self.tree.column("step", width=45, minwidth=45, anchor="center", stretch=False)
        self.tree.column("key", width=120, minwidth=90, anchor="center", stretch=True)
        self.tree.column("delay_ms", width=85, minwidth=75, anchor="center", stretch=False)
        self.tree.column("mode", width=60, minwidth=55, anchor="center", stretch=False)

        self.tree.grid(row=1, column=0, sticky="nsew")
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.tree.yview)
        scrollbar.grid(row=1, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=scrollbar.set)

        self.tree.bind("<Double-1>", self._on_tree_double_click)
        self.tree.bind("<Button-1>", self._on_tree_single_click)
        self.tree.bind("<Button-3>", self._show_step_menu)
        self.tree.bind("<Delete>", lambda _e: self.delete_selected_step())
        self.tree.bind("<BackSpace>", lambda _e: self.delete_selected_step())
        self.tree.bind("<Control-d>", lambda _e: self.duplicate_selected_step())
        self.tree.bind("<Alt-Up>", lambda _e: self.move_selected_step(-1))
        self.tree.bind("<Alt-Down>", lambda _e: self.move_selected_step(1))

        self.step_menu = tk.Menu(self.root, tearoff=False)
        self.step_menu.add_command(label="Edit key", command=self.edit_selected_key)
        self.step_menu.add_command(label="Edit delay", command=self.edit_selected_delay)
        self.step_menu.add_command(label="Toggle SEQ / IND", command=self.toggle_selected_mode)
        self.step_menu.add_separator()
        self.step_menu.add_command(label="Move up", command=lambda: self.move_selected_step(-1))
        self.step_menu.add_command(label="Move down", command=lambda: self.move_selected_step(1))
        self.step_menu.add_command(label="Duplicate", command=self.duplicate_selected_step)
        self.step_menu.add_separator()
        self.step_menu.add_command(label="Delete", command=self.delete_selected_step)

        footer = ttk.Frame(frm)
        footer.grid(row=6, column=0, sticky="ew", pady=(8, 0))
        footer.columnconfigure(0, weight=1)

        self.status = ttk.Label(footer, text="Ready.", anchor="w")
        self.status.grid(row=0, column=0, sticky="ew")

        self.step_count = ttk.Label(footer, text="0 steps", anchor="e")
        self.step_count.grid(row=0, column=1, padx=(12, 0))

        hint = "Double-click a cell to edit • Delete removes • Ctrl+D duplicates • Alt+↑/↓ reorders"
        ttk.Label(frm, text=hint, foreground="#bdbdbd", anchor="center").grid(
            row=5, column=0, sticky="ew", pady=(5, 0)
        )

        if not KEYBOARD_AVAILABLE:
            self.chk_hotkeys.state(["disabled"])
            self._set_status("keyboard module unavailable. Install 'keyboard' for global recording.")
        if not PYDIRECT_AVAILABLE:
            self._set_status("Using pyautogui fallback; pydirectinput is recommended for games.")

    def _set_status(self, msg: str):
        self.status.config(text=msg)
        if hasattr(self, "step_count"):
            count = len(self.events)
            self.step_count.config(text=f"{count} step" if count == 1 else f"{count} steps")

    # ---------------- Recording ----------------

    def _record_button_clicked(self):
        # Tkinter runs this command after the mouse press has already happened,
        # but the global mouse hook may still be processing the same click.
        # Mark one left-click for removal/suppression when stopping by mouse.
        was_recording = self.recording

        if was_recording:
            self._ignore_next_left_click = True

            # In case the global listener already recorded this exact UI click,
            # remove a trailing left-mouse step immediately.
            if self.events and self.events[-1].get("key") == "mouse:left":
                self.events.pop()
                children = list(self.tree.get_children(""))
                if children:
                    self.tree.delete(children[-1])
                self._renumber_steps()

        self.toggle_recording()

        # The listener normally receives the press before this callback. Clear the
        # fallback flag shortly afterward so the next real click is not ignored.
        if was_recording:
            self.root.after(150, self._clear_ignored_left_click)

    def _clear_ignored_left_click(self):
        self._ignore_next_left_click = False

    def toggle_recording(self):
        if not KEYBOARD_AVAILABLE:
            messagebox.showerror("Not available", "Global keystroke recording requires the 'keyboard' module.")
            return
        if self.recording:
            self.stop_recording()
        else:
            self.start_recording()

    def start_recording(self):
        if self._is_playing():
            messagebox.showwarning("Busy", "Stop playback before recording.")
            return

        self._end_inline_edit(commit=True)
        self.events.clear()
        for iid in self.tree.get_children():
            self.tree.delete(iid)

        self.recording = True
        self._last_time = time.perf_counter()

        self.btn_record.config(text="■ Stop recording")

        # Important: after clicking Start Recording, the button keeps keyboard focus.
        # In Tkinter, pressing Space activates the focused button, which would click
        # the same button again and stop recording. Move focus away so Space can be
        # recorded normally instead of cancelling recording.
        try:
            self.root.focus_set()
        except Exception:
            pass

        self._set_status("Recording ON — press keyboard keys or mouse buttons (F9 to stop).")

    def stop_recording(self):
        self.recording = False
        self._last_time = None

        self.btn_record.config(text="● Record")
        self._set_status(f"Recording OFF — captured {len(self.events)} steps.")

    # ---------------- Keyboard / Mouse hooks ----------------

    def _on_key_event(self, e):
        if self._capturing_toggle_key and e.event_type == "down":
            sc = getattr(e, "scan_code", None)

            if sc is not None:
                self.root.after(0, lambda: self._finish_capture_toggle_key(f"scan:{sc}"))
            else:
                name = (e.name or "").lower()
                if name:
                    self.root.after(0, lambda: self._finish_capture_toggle_key(name))
            return

        if self.use_hotkeys.get():
            macro_index = self._find_macro_for_keyboard_event(e)

            if macro_index is not None:
                if self._macro_uses_hold_to_repeat(macro_index):
                    if e.event_type == "down":
                        self.root.after(
                            0,
                            lambda index=macro_index: self.start_held_macro(index),
                        )
                    elif e.event_type == "up":
                        self.root.after(
                            0,
                            lambda index=macro_index: self.stop_held_macro(index),
                        )
                    return

                if e.event_type == "down" and not self._toggle_pressed_guard:
                    self._toggle_pressed_guard = True
                    self.root.after(
                        0,
                        lambda index=macro_index: self.toggle_macro_by_index(index),
                    )
                elif e.event_type == "up":
                    self._toggle_pressed_guard = False
                return

        if not self.recording or e.event_type != "down":
            return

        key = (e.name or "").lower()
        if not key or key in self.ignore_keys:
            return

        self._record_input_step(key)

    def _start_mouse_listener(self):
        if not MOUSE_AVAILABLE:
            return
        try:
            self._mouse_listener = pynput_mouse.Listener(on_click=self._on_mouse_click)
            self._mouse_listener.daemon = True
            self._mouse_listener.start()
        except Exception as ex:
            self._log_error("MOUSE_LISTENER_START", ex)
            self._mouse_listener = None

    def _on_mouse_click(self, x, y, button, pressed):
        btn_name = self._mouse_button_name(button)
        if not btn_name:
            return

        if self._capturing_toggle_key and pressed:
            if btn_name == "left":
                self.root.after(
                    0,
                    lambda: self._set_status(
                        "Left mouse button is not allowed as Play Toggle. "
                        "Press another key or mouse button."
                    )
                )
                return

            self.root.after(0, lambda: self._finish_capture_toggle_key(f"mouse:{btn_name}"))
            return

        macro_index = (
            self._find_macro_for_mouse_button(btn_name)
            if self.use_hotkeys.get()
            else None
        )

        if macro_index is not None:
            if self._macro_uses_hold_to_repeat(macro_index):
                if pressed:
                    self.root.after(
                        0,
                        lambda index=macro_index: self.start_held_macro(index),
                    )
                else:
                    self.root.after(
                        0,
                        lambda index=macro_index: self.stop_held_macro(index),
                    )
                return

            if pressed and not self._toggle_pressed_guard:
                self._toggle_pressed_guard = True
                self.root.after(
                    0,
                    lambda index=macro_index: self.toggle_macro_by_index(index),
                )
            elif not pressed:
                self._toggle_pressed_guard = False
            return

        # Ignore the Record/Stop button's own left-click.
        if pressed and btn_name == "left" and self._ignore_next_left_click:
            self._ignore_next_left_click = False
            return

        # Record every supported mouse button as a macro step.
        # Left mouse remains blocked only as the Play Toggle.
        if self.recording and pressed:
            self._record_input_step(f"mouse:{btn_name}")

    # ---------------- Inline editing ----------------

    def _on_tree_single_click(self, event):
        if self._edit_entry is not None:
            region = self.tree.identify("region", event.x, event.y)
            col = self.tree.identify_column(event.x) if region == "cell" else ""
            active_col = "#2" if self._edit_field == "key" else "#3"
            if region != "cell" or col != active_col:
                self._end_inline_edit(commit=True)

    def _on_tree_double_click(self, event):
        if self.recording:
            return
        row_iid = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        if not row_iid:
            return
        if col == "#2":
            self._begin_edit_key_cell(row_iid)
        elif col == "#3":
            self._begin_edit_delay_cell(row_iid)
        elif col == "#4":
            self._toggle_mode_cell(row_iid)

    def _begin_inline_edit(self, iid: str, field: str):
        self._end_inline_edit(commit=True)
        bbox = self.tree.bbox(iid, column=field)
        if not bbox:
            return

        x, y, w, h = bbox
        current_text = self.tree.set(iid, field)

        self._edit_iid = iid
        self._edit_field = field
        self._edit_entry = ttk.Entry(self.tree)
        self._edit_entry.place(x=x, y=y, width=w, height=h)
        self._edit_entry.insert(0, current_text)
        self._edit_entry.select_range(0, tk.END)
        self._edit_entry.focus_set()

        self._edit_entry.bind("<Return>", lambda _e: self._end_inline_edit(commit=True))
        self._edit_entry.bind("<Escape>", lambda _e: self._end_inline_edit(commit=False))
        self._edit_entry.bind("<FocusOut>", lambda _e: self._end_inline_edit(commit=True))

    def _begin_edit_key_cell(self, iid: str):
        self._begin_inline_edit(iid, "key")

    def _begin_edit_delay_cell(self, iid: str):
        self._begin_inline_edit(iid, "delay_ms")

    def _end_inline_edit(self, commit: bool):
        if self._edit_entry is None or self._edit_iid is None:
            return

        iid = self._edit_iid
        field = self._edit_field
        entry = self._edit_entry
        new_text = entry.get().strip().lower()

        self._edit_entry = None
        self._edit_iid = None
        self._edit_field = None
        entry.destroy()

        if not commit:
            return

        children = list(self.tree.get_children(""))
        try:
            idx = children.index(iid)
        except ValueError:
            return
        if not (0 <= idx < len(self.events)):
            return

        if field == "key":
            if not new_text:
                messagebox.showerror("Invalid key", "Key cannot be empty. Delete the step if it is not needed.")
                return
            self.tree.set(iid, "key", new_text)
            self.events[idx]["key"] = new_text
            self._set_status(f"Step {idx + 1} key changed to: {new_text}")
            return

        if field == "delay_ms":
            try:
                new_ms = int(new_text)
                if new_ms < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Invalid delay", "Enter a non-negative integer milliseconds, e.g. 55 or 5000.")
                return

            self.tree.set(iid, "delay_ms", str(new_ms))
            self.events[idx]["delay"] = self.ms_int_to_sec(new_ms)
            self._set_status(f"Step {idx + 1} delay changed to {new_ms} ms.")

    def _renumber_steps(self):
        for i, iid in enumerate(self.tree.get_children(""), start=1):
            self.tree.set(iid, "step", f"{i:03d}")

    def delete_selected_step(self):
        if self.recording:
            messagebox.showwarning("Recording", "Stop recording before deleting steps.")
            return
        if self._is_playing():
            messagebox.showwarning("Playing", "Stop playback before deleting steps.")
            return

        self._end_inline_edit(commit=True)
        selected = self.tree.selection()
        if not selected:
            messagebox.showinfo("No selection", "Select a step to delete.")
            return

        iid = selected[0]
        children = list(self.tree.get_children(""))
        try:
            idx = children.index(iid)
        except ValueError:
            return

        self.tree.delete(iid)
        if 0 <= idx < len(self.events):
            del self.events[idx]

        self._renumber_steps()

        remaining = list(self.tree.get_children(""))
        if remaining:
            next_idx = min(idx, len(remaining) - 1)
            self.tree.selection_set(remaining[next_idx])
            self.tree.focus(remaining[next_idx])

        self._set_status(f"Deleted step {idx + 1}. {len(self.events)} step(s) remain.")

    def _selected_iid(self):
        selected = self.tree.selection()
        return selected[0] if selected else None

    def edit_selected_key(self):
        iid = self._selected_iid()
        if iid:
            self._begin_edit_key_cell(iid)
        else:
            self._set_status("Select a step first.")

    def edit_selected_delay(self):
        iid = self._selected_iid()
        if iid:
            self._begin_edit_delay_cell(iid)
        else:
            self._set_status("Select a step first.")

    def toggle_selected_mode(self):
        iid = self._selected_iid()
        if iid:
            self._toggle_mode_cell(iid)
            self._set_status("Step mode changed.")
        else:
            self._set_status("Select a step first.")

    def _show_step_menu(self, event):
        iid = self.tree.identify_row(event.y)
        if iid:
            self.tree.selection_set(iid)
            self.tree.focus(iid)
            try:
                self.step_menu.tk_popup(event.x_root, event.y_root)
            finally:
                self.step_menu.grab_release()

    def duplicate_selected_step(self):
        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before editing steps.")
            return

        self._end_inline_edit(commit=True)
        iid = self._selected_iid()
        if not iid:
            self._set_status("Select a step to duplicate.")
            return

        children = list(self.tree.get_children(""))
        idx = children.index(iid)
        duplicate = dict(self.events[idx])
        self.events.insert(idx + 1, duplicate)

        new_iid = self.tree.insert(
            "", idx + 1,
            values=("", duplicate["key"], str(self.sec_to_ms_int(duplicate["delay"])),
                    self._mode_label(duplicate.get("mode", "seq")))
        )
        self._renumber_steps()
        self.tree.selection_set(new_iid)
        self.tree.focus(new_iid)
        self.tree.see(new_iid)
        self._set_status(f"Duplicated step {idx + 1}.")

    def move_selected_step(self, direction: int):
        if self.recording or self._is_playing():
            messagebox.showwarning("Busy", "Stop recording or playback before reordering steps.")
            return

        self._end_inline_edit(commit=True)
        iid = self._selected_iid()
        if not iid:
            self._set_status("Select a step to move.")
            return

        children = list(self.tree.get_children(""))
        old_idx = children.index(iid)
        new_idx = old_idx + direction
        if new_idx < 0 or new_idx >= len(children):
            return

        self.events[old_idx], self.events[new_idx] = self.events[new_idx], self.events[old_idx]
        self.tree.move(iid, "", new_idx)
        self._renumber_steps()
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        self.tree.see(iid)
        self._set_status(f"Moved step to position {new_idx + 1}.")

    def _toggle_mode_cell(self, iid: str):
        children = list(self.tree.get_children(""))
        try:
            idx = children.index(iid)
        except ValueError:
            return
        if not (0 <= idx < len(self.events)):
            return
        current = self.events[idx].get("mode", "seq")
        new_mode = "ind" if current == "seq" else "seq"
        self.events[idx]["mode"] = new_mode
        self.tree.set(iid, "mode", self._mode_label(new_mode))

    # ---------------- Playback ----------------

    def _is_playing(self) -> bool:
        if self._play_thread and self._play_thread.is_alive():
            return True
        for th in self._independent_threads:
            if th.is_alive():
                return True
        with self._held_keys_lock:
            return bool(self._held_keys)

    def toggle_playback(self):
        if self._is_playing():
            self.stop_playback()
        else:
            self.play_macro()

    def play_macro(self):
        self._store_active_macro()
        if self.recording:
            messagebox.showwarning("Recording", "Stop recording before playback.")
            return
        if not self.events:
            messagebox.showinfo("Empty", "No macro recorded.")
            return
        if self._is_playing():
            return

        self._end_inline_edit(commit=True)

        if self.repeat_enabled.get():
            try:
                rd = int(self.repeat_delay_ms.get())
                if rd < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Invalid repeat delay", "Repeat delay must be >= 0 ms.")
                return

        self._stop_playback.clear()
        self._play_session_id += 1
        session_id = self._play_session_id

        self._start_independent_workers(session_id=session_id)

        if any(ev.get("mode", "seq") == "seq" for ev in self.events):
            self._play_thread = threading.Thread(
                target=self._play_worker_sequential_safe,
                args=(session_id,),
                daemon=True
            )
            self._play_thread.start()

        if self.hold_to_repeat.get():
            self._set_status("Playing while toggle is held...")
        else:
            self._set_status("Playing... (toggle key/button stops)")
        self._schedule_watchdog(session_id)

    def _press_key_game_safe(self, key: str):
        HOLD_S = 0.02

        if self._is_mouse_input(key):
            button = self._pynput_mouse_button(key)
            if self._mouse_controller is None or button is None:
                self._log_error(
                    f"MOUSE_CLICK input={key}",
                    RuntimeError(f"Mouse button is unavailable: {key}")
                )
                return
            try:
                self._mouse_controller.press(button)
                time.sleep(HOLD_S)
                self._mouse_controller.release(button)
            except Exception as ex:
                self._log_error(f"MOUSE_CLICK input={key}", ex)
            return

        try:
            input_driver.keyDown(key)
            time.sleep(HOLD_S)
            input_driver.keyUp(key)
        except Exception:
            try:
                input_driver.press(key)
            except Exception as ex:
                self._log_error(f"KEY_PRESS key={key}", ex)

    def _hold_key_game_safe(self, key: str):
        with self._held_keys_lock:
            if key in self._held_keys:
                return
            self._held_keys.add(key)

        try:
            if self._is_mouse_input(key):
                button = self._pynput_mouse_button(key)
                if self._mouse_controller is None or button is None:
                    raise RuntimeError(f"Mouse button is unavailable: {key}")
                self._mouse_controller.press(button)
            else:
                input_driver.keyDown(key)
        except Exception as ex:
            with self._held_keys_lock:
                self._held_keys.discard(key)
            self._log_error(f"HOLD_INPUT input={key}", ex)

    def _release_key_game_safe(self, key: str):
        with self._held_keys_lock:
            if key not in self._held_keys:
                return
            self._held_keys.remove(key)

        try:
            if self._is_mouse_input(key):
                button = self._pynput_mouse_button(key)
                if self._mouse_controller is None or button is None:
                    raise RuntimeError(f"Mouse button is unavailable: {key}")
                self._mouse_controller.release(button)
            else:
                input_driver.keyUp(key)
        except Exception as ex:
            self._log_error(f"RELEASE_INPUT input={key}", ex)


    def _release_all_held_keys(self):
        with self._held_keys_lock:
            keys = list(self._held_keys)
            self._held_keys.clear()

        for key in keys:
            try:
                if self._is_mouse_input(key):
                    button = self._pynput_mouse_button(key)
                    if self._mouse_controller is None or button is None:
                        raise RuntimeError(f"Mouse button is unavailable: {key}")
                    self._mouse_controller.release(button)
                else:
                    input_driver.keyUp(key)
            except Exception as ex:
                self._log_error(f"RELEASE_ALL input={key}", ex)

    def _play_worker_sequential_safe(self, session_id: int):
        try:
            self._play_worker_sequential(session_id)
        except Exception as ex:
            self._log_error("SEQ_THREAD", ex)
            self.root.after(
                0,
                lambda: self._set_status("SEQ thread error (see macro_errors.log). IND may still run.")
            )
        finally:
            self._release_all_held_keys()

    def _play_worker_sequential(self, session_id: int):
        speed = max(0.01, float(self.playback_speed.get()))
        repeat = bool(self.repeat_enabled.get()) or bool(self.hold_to_repeat.get())
        repeat_delay_s = self.ms_int_to_sec(int(self.repeat_delay_ms.get() or 0))

        seq_events = [ev for ev in self.events if ev.get("mode", "seq") == "seq"]
        if not seq_events:
            return

        while True:
            for step in seq_events:
                if self._stop_playback.is_set() or session_id != self._play_session_id:
                    return

                delay = float(step["delay"])

                if delay <= 0.0:
                    # 0ms SEQ means hold key until playback stops.
                    self._hold_key_game_safe(step["key"])
                    continue

                time.sleep(max(0.0, delay / speed))
                self._press_key_game_safe(step["key"])

            if self._stop_playback.is_set() or session_id != self._play_session_id:
                return

            if not repeat:
                # Keep macro alive if a 0ms SEQ key is being held.
                while True:
                    with self._held_keys_lock:
                        has_held_keys = bool(self._held_keys)

                    if not has_held_keys:
                        break

                    if self._stop_playback.is_set() or session_id != self._play_session_id:
                        return

                    time.sleep(0.02)

                break

            if repeat_delay_s > 0:
                end_t = time.time() + repeat_delay_s
                while time.time() < end_t:
                    if self._stop_playback.is_set() or session_id != self._play_session_id:
                        return
                    time.sleep(0.02)

        self.root.after(
            0,
            lambda: self._set_status(
                "SEQ finished (IND may still be running)." if self._any_ind_alive()
                else "Playback finished."
            )
        )

    def _start_independent_workers(self, session_id: int):
        self._independent_threads = []
        ind_events = [ev for ev in self.events if ev.get("mode", "seq") == "ind"]

        for ev in ind_events:
            key = ev["key"]
            period_s = float(ev["delay"])

            if period_s <= 0.0:
                # 0ms IND means hold key until playback stops.
                self._hold_key_game_safe(key)
                continue

            th = threading.Thread(
                target=self._independent_worker_safe,
                args=(key, period_s, session_id),
                daemon=True
            )
            self._independent_threads.append(th)
            th.start()

    def _independent_worker_safe(self, key: str, period_s: float, session_id: int):
        try:
            self._independent_worker(key, period_s, session_id)
        except Exception as ex:
            self._log_error(f"IND_THREAD key={key}", ex)

    def _independent_worker(self, key: str, period_s: float, session_id: int):
        while not self._stop_playback.is_set() and session_id == self._play_session_id:
            speed = max(0.01, float(self.playback_speed.get()))
            sleep_s = max(0.001, period_s / speed)

            end_t = time.time() + sleep_s
            while time.time() < end_t:
                if self._stop_playback.is_set() or session_id != self._play_session_id:
                    return
                time.sleep(0.01)

            if self._stop_playback.is_set() or session_id != self._play_session_id:
                return

            self._press_key_game_safe(key)

    def _any_ind_alive(self) -> bool:
        return any(th.is_alive() for th in self._independent_threads)

    def _schedule_watchdog(self, session_id: int):
        def tick():
            if session_id != self._play_session_id:
                return
            if self._stop_playback.is_set():
                self._set_status("STANDBY")
                return
            if self._any_ind_alive() and (not (self._play_thread and self._play_thread.is_alive())):
                self._set_status("Playing (IND still running)... (toggle key/button stops)")
            self.root.after(500, tick)

        self.root.after(500, tick)

    def stop_playback(self):
        self._held_toggle_macro_index = None
        self._stop_playback.set()
        self._play_session_id += 1
        self._release_all_held_keys()
        self._set_status("STANDBY")

    # ---------------- Hotkey capture ----------------

    def capture_toggle_hotkey(self):
        if not KEYBOARD_AVAILABLE and not MOUSE_AVAILABLE:
            messagebox.showerror("Not available", "Need 'keyboard' and/or 'pynput' to capture a toggle input.")
            return
        self._capturing_toggle_key = True
        self._set_status("Press a keyboard key or mouse button for Play Toggle...")

    def _finish_capture_toggle_key(self, key_id: str):
        key_id = str(key_id).strip().lower()

        if key_id == "mouse:left":
            self._capturing_toggle_key = True
            messagebox.showwarning(
                "Unsafe toggle blocked",
                "The left mouse button cannot be assigned as the Play Toggle.\n\n"
                "Choose a keyboard key, right/middle mouse button, or X1/X2."
            )
            self._set_status("Left mouse is blocked. Press another toggle input.")
            return

        for index, macro in enumerate(self.macros):
            if index != self.active_macro_index and macro.get("toggle", "none") == key_id:
                self._capturing_toggle_key = True
                messagebox.showwarning(
                    "Toggle already used",
                    f"{key_id} is already assigned to {macro['name']}.",
                )
                self._set_status("Choose a different toggle input.")
                return

        self._capturing_toggle_key = False
        self.play_toggle_key.set(key_id)
        self._active_macro()["toggle"] = key_id
        self._resolve_toggle_key()
        self._set_status(
            f"{self._active_macro()['name']} toggle set to: {key_id}"
        )

    # ---------------- Save/Load/Clear ----------------

    def clear_macro(self):
        if self.recording:
            messagebox.showwarning("Recording", "Stop recording first.")
            return
        self._end_inline_edit(commit=True)
        self.events.clear()
        for iid in self.tree.get_children():
            self.tree.delete(iid)
        self._set_status(f"Cleared {self._active_macro()['name']}.")

    def save_macro(self):
        if not self.macros:
            messagebox.showinfo("Empty", "Nothing to save.")
            return
        self._end_inline_edit(commit=True)

        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")],
            title="Save macro"
        )
        if not path:
            return

        self._store_active_macro()
        data = {
            "version": 7,
            "active_macro_index": self.active_macro_index,
            "macros": self.macros,
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        self._set_status(f"Saved to {path}")

    def load_macro(self):
        if self.recording:
            messagebox.showwarning("Recording", "Stop recording first.")
            return
        self._end_inline_edit(commit=True)

        path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json")],
            title="Load macro"
        )
        if not path:
            return

        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)

            loaded_macros = data.get("macros")

            if isinstance(loaded_macros, list) and loaded_macros:
                cleaned_macros = []

                for number, macro in enumerate(loaded_macros, start=1):
                    if not isinstance(macro, dict):
                        continue

                    cleaned_events = []

                    for ev in macro.get("events", []):
                        if not isinstance(ev, dict):
                            continue

                        key = str(ev.get("key", "")).strip().lower()

                        try:
                            delay = max(0.0, float(ev.get("delay", 0.0)))
                        except Exception:
                            delay = 0.0

                        mode = str(ev.get("mode", "seq")).lower()
                        if mode not in ("seq", "ind"):
                            mode = "seq"

                        if key:
                            cleaned_events.append(
                                {"key": key, "delay": delay, "mode": mode}
                            )

                    toggle = str(macro.get("toggle", "none")).strip().lower()

                    if toggle == "mouse:left":
                        toggle = "none"

                    try:
                        repeat_delay = max(
                            0,
                            int(macro.get("repeat_delay_ms", 0)),
                        )
                    except Exception:
                        repeat_delay = 0

                    try:
                        speed = max(
                            0.25,
                            min(3.0, float(macro.get("speed", 1.0))),
                        )
                    except Exception:
                        speed = 1.0

                    cleaned_macros.append(
                        {
                            "name": str(
                                macro.get("name", f"Macro {number}")
                            ).strip()
                            or f"Macro {number}",
                            "events": cleaned_events,
                            "toggle": toggle or "none",
                            "repeat_enabled": bool(
                                macro.get("repeat_enabled", False)
                            ),
                            "hold_to_repeat": bool(
                                macro.get("hold_to_repeat", False)
                            ),
                            "repeat_delay_ms": repeat_delay,
                            "speed": speed,
                        }
                    )

                if not cleaned_macros:
                    raise ValueError("No valid macros found in this file.")

                self.macros = cleaned_macros

                try:
                    requested_index = int(data.get("active_macro_index", 0))
                except Exception:
                    requested_index = 0

                self.active_macro_index = min(
                    max(0, requested_index),
                    len(self.macros) - 1,
                )
            else:
                # Backward compatibility with version 4 single-macro files.
                cleaned_events = []

                for ev in data.get("events", []):
                    if not isinstance(ev, dict):
                        continue

                    key = str(ev.get("key", "")).strip().lower()

                    try:
                        delay = max(0.0, float(ev.get("delay", 0.0)))
                    except Exception:
                        delay = 0.0

                    mode = str(ev.get("mode", "seq")).lower()
                    if mode not in ("seq", "ind"):
                        mode = "seq"

                    if key:
                        cleaned_events.append(
                            {"key": key, "delay": delay, "mode": mode}
                        )

                toggle = str(
                    data.get("play_toggle_key", "f8")
                ).strip().lower()

                if toggle == "mouse:left":
                    toggle = "f8"

                self.macros = [
                    {
                        "name": "Macro 1",
                        "events": cleaned_events,
                        "toggle": toggle or "f8",
                        "repeat_enabled": bool(
                            data.get("repeat_enabled", False)
                        ),
                        "hold_to_repeat": False,
                        "repeat_delay_ms": max(
                            0,
                            int(data.get("repeat_delay_ms", 0)),
                        ),
                        "speed": 1.0,
                    }
                ]
                self.active_macro_index = 0

            self._refresh_macro_selector()
            self._load_active_macro()

            if KEYBOARD_AVAILABLE:
                self._setup_hotkeys()

            self._set_status(f"Loaded {len(self.macros)} macro(s) from {path}")
        except Exception as ex:
            messagebox.showerror("Load failed", str(ex))

    # ---------------- Hotkeys ----------------

    def _setup_hotkeys(self):
        try:
            keyboard.clear_all_hotkeys()
        except Exception:
            pass
        if not self.use_hotkeys.get():
            return
        keyboard.add_hotkey("f9", lambda: self.root.after(0, self.toggle_recording))
        keyboard.add_hotkey("f10", lambda: self.root.after(0, self.play_macro))
        keyboard.add_hotkey("esc", lambda: self.root.after(0, self.stop_playback))

    def _hotkeys_toggled(self):
        if not KEYBOARD_AVAILABLE:
            return
        self._setup_hotkeys()
        self._set_status("Hotkeys enabled." if self.use_hotkeys.get() else "Hotkeys disabled.")

    def on_close(self):
        self._store_active_macro()
        try:
            self.stop_playback()
        except Exception:
            pass
        try:
            if KEYBOARD_AVAILABLE:
                keyboard.unhook_all()
                keyboard.clear_all_hotkeys()
        except Exception:
            pass
        try:
            if self._mouse_listener is not None:
                self._mouse_listener.stop()
        except Exception:
            pass
        self.root.destroy()

def main():
    root = tk.Tk()

    # Set window icon
    try:
        icon = tk.PhotoImage(file=resource_path("macro.png"))
        root.iconphoto(True, icon)
        root._icon = icon      # keep a reference so it isn't garbage collected
    except Exception as e:
        print("Couldn't load icon:", e)

    MacroApp(root)

    root.update_idletasks()
    root.geometry("")
    root.minsize(root.winfo_reqwidth(), root.winfo_reqheight())
    root.mainloop()

if __name__ == "__main__":
    main()
