import json
import time
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import traceback

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
        self.root.title("Simple Macro Recorder (pydirectinput playback)")

        # Apply dark theme BEFORE building UI widgets
        self._apply_dark_theme()

        self.recording = False
        self.events = []  # {"key": str, "delay": float(seconds), "mode": "seq"|"ind"}
        self._last_time = None

        self._play_thread = None
        self._stop_playback = threading.Event()
        self._independent_threads = []

        self._play_session_id = 0

        self._edit_entry = None
        self._edit_iid = None

        self.ignore_keys = {"f9", "f10", "esc"}
        self.use_hotkeys = tk.BooleanVar(value=True)
        self.playback_speed = tk.DoubleVar(value=1.0)

        self.play_toggle_key = tk.StringVar(value="f8")

        self.repeat_enabled = tk.BooleanVar(value=False)
        self.repeat_delay_ms = tk.IntVar(value=250)

        self._capturing_toggle_key = False

        self.toggle_scan_code = None
        self.toggle_key_name = None
        self.toggle_mouse_button = None
        self._toggle_pressed_guard = False
        self._mouse_listener = None
        self._resolve_toggle_key()

        self._build_ui()

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
            if btn in ("left", "right", "middle", "x1", "x2"):
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

    # ---------------- UI ----------------

    def _build_ui(self):
        frm = ttk.Frame(self.root, padding=12)
        frm.grid(row=0, column=0, sticky="nsew")
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)

        btns = ttk.Frame(frm)
        btns.grid(row=0, column=0, sticky="ew")

        self.btn_record = ttk.Button(btns, text="Start Recording", command=self.toggle_recording)
        self.btn_record.grid(row=0, column=0, padx=(0, 8))

        ttk.Button(btns, text="Play", command=self.play_macro).grid(row=0, column=1, padx=(0, 8))
        ttk.Button(btns, text="Stop", command=self.stop_playback).grid(row=0, column=2, padx=(0, 8))
        ttk.Button(btns, text="Clear", command=self.clear_macro).grid(row=0, column=3, padx=(0, 8))
        ttk.Button(btns, text="Save", command=self.save_macro).grid(row=0, column=4, padx=(0, 8))
        ttk.Button(btns, text="Load", command=self.load_macro).grid(row=0, column=5, padx=(0, 8))

        opts = ttk.Frame(frm)
        opts.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        opts.columnconfigure(9, weight=1)

        self.chk_hotkeys = ttk.Checkbutton(
            opts,
            text="Enable hotkeys (F9 record, F10 play, ESC stop playback; toggle supports keyboard or mouse)",
            variable=self.use_hotkeys,
            command=self._hotkeys_toggled
        )
        self.chk_hotkeys.grid(row=0, column=0, sticky="w", columnspan=10)

        ttk.Label(opts, text="Playback speed:").grid(row=1, column=0, sticky="w", pady=(8, 0))
        self.speed = ttk.Scale(opts, from_=0.25, to=3.0, variable=self.playback_speed, orient="horizontal")
        self.speed.grid(row=1, column=1, sticky="ew", pady=(8, 0), padx=(8, 8), columnspan=2)
        self.speed_val = ttk.Label(opts, text="1.00x")
        self.speed_val.grid(row=1, column=3, sticky="w", pady=(8, 0))
        self.speed.bind("<Motion>", lambda _e: self.speed_val.config(text=f"{self.playback_speed.get():.2f}x"))
        self.speed.bind("<ButtonRelease-1>", lambda _e: self.speed_val.config(text=f"{self.playback_speed.get():.2f}x"))

        ttk.Label(opts, text="Play toggle key/button:").grid(row=2, column=0, sticky="w", pady=(8, 0))
        self.toggle_entry = ttk.Entry(opts, textvariable=self.play_toggle_key, width=18)
        self.toggle_entry.grid(row=2, column=1, padx=(8, 8), sticky="w", pady=(8, 0))
        ttk.Button(opts, text="Apply", command=self.apply_toggle_hotkey).grid(row=2, column=2, padx=(0, 8), pady=(8, 0))
        ttk.Button(opts, text="Set (press key)", command=self.capture_toggle_hotkey).grid(row=2, column=3, padx=(0, 12), pady=(8, 0))

        self.chk_repeat = ttk.Checkbutton(opts, text="Repeat SEQ part", variable=self.repeat_enabled)
        self.chk_repeat.grid(row=2, column=4, sticky="w", pady=(8, 0))
        ttk.Label(opts, text="Repeat delay (ms):").grid(row=2, column=5, padx=(8, 0), sticky="w", pady=(8, 0))
        self.repeat_delay_entry = ttk.Entry(opts, textvariable=self.repeat_delay_ms, width=8)
        self.repeat_delay_entry.grid(row=2, column=6, padx=(8, 0), sticky="w", pady=(8, 0))

        list_frame = ttk.LabelFrame(frm, text="Steps (Delay ms: dblclick edit; Mode: dblclick toggle SEQ/IND)")
        list_frame.grid(row=3, column=0, sticky="nsew", pady=(10, 0))
        frm.rowconfigure(3, weight=1)

        columns = ("step", "key", "delay_ms", "mode")
        self.tree = ttk.Treeview(list_frame, columns=columns, show="headings", selectmode="browse")
        self.tree.heading("step", text="#")
        self.tree.heading("key", text="Key")
        self.tree.heading("delay_ms", text="Delay (ms)")
        self.tree.heading("mode", text="Mode")

        self.tree.column("step", width=60, anchor="e", stretch=False)
        self.tree.column("key", width=180, anchor="w", stretch=True)
        self.tree.column("delay_ms", width=120, anchor="e", stretch=False)
        self.tree.column("mode", width=80, anchor="center", stretch=False)

        self.tree.grid(row=0, column=0, sticky="nsew", padx=8, pady=8)
        list_frame.rowconfigure(0, weight=1)
        list_frame.columnconfigure(0, weight=1)

        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.tree.yview)
        scrollbar.grid(row=0, column=1, sticky="ns", pady=8)
        self.tree.configure(yscrollcommand=scrollbar.set)

        self.tree.bind("<Double-1>", self._on_tree_double_click)
        self.tree.bind("<Button-1>", self._on_tree_single_click)

        self.status = ttk.Label(frm, text="Ready.", anchor="w")
        self.status.grid(row=4, column=0, sticky="ew", pady=(10, 0))

        hint = "SEQ = plays in order. IND = repeats on its own timer. Toggle supports keys or mouse:left/right/middle. Errors are logged to macro_errors.log"
        ttk.Label(frm, text=hint, foreground="#bdbdbd", anchor="w", justify="left").grid(
            row=5, column=0, sticky="ew", pady=(8, 0)
        )

        if not KEYBOARD_AVAILABLE:
            self.chk_hotkeys.state(["disabled"])
            self._set_status("keyboard module not installed/usable. Install 'keyboard' to record keystrokes globally.")
        if not PYDIRECT_AVAILABLE:
            self._set_status("NOTE: pydirectinput not installed; using pyautogui fallback (may fail in games).")

    def _set_status(self, msg: str):
        self.status.config(text=msg)

    # ---------------- Recording ----------------

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

        self.btn_record.config(text="Stop Recording")
        self._set_status("Recording ON — press keys now (F9 to stop).")

    def stop_recording(self):
        self.recording = False
        self._last_time = None

        self.btn_record.config(text="Start Recording")
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
            is_toggle = False
            if self.toggle_scan_code is not None and getattr(e, "scan_code", None) == self.toggle_scan_code:
                is_toggle = True
            elif self.toggle_scan_code is None and self.toggle_key_name and (e.name or "").lower() == self.toggle_key_name:
                is_toggle = True

            if is_toggle:
                if e.event_type == "down" and not self._toggle_pressed_guard:
                    self._toggle_pressed_guard = True
                    self.root.after(0, self.toggle_playback)
                elif e.event_type == "up":
                    self._toggle_pressed_guard = False
                return

        if not self.recording or e.event_type != "down":
            return

        key = (e.name or "").lower()
        if not key or key in self.ignore_keys:
            return

        t = time.perf_counter()
        delay_sec = t - (self._last_time if self._last_time is not None else t)
        self._last_time = t

        self.events.append({"key": key, "delay": float(delay_sec), "mode": "seq"})
        idx = len(self.events)
        delay_ms = self.sec_to_ms_int(delay_sec)
        self.root.after(0, lambda: self.tree.insert("", "end", values=(f"{idx:03d}", key, f"{delay_ms}", "SEQ")))

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
            self.root.after(0, lambda: self._finish_capture_toggle_key(f"mouse:{btn_name}"))
            return

        if not self.use_hotkeys.get():
            return

        if self.toggle_mouse_button == btn_name:
            if pressed and not self._toggle_pressed_guard:
                self._toggle_pressed_guard = True
                self.root.after(0, self.toggle_playback)
            elif not pressed:
                self._toggle_pressed_guard = False

    # ---------------- Inline editing ----------------

    def _on_tree_single_click(self, event):
        if self._edit_entry is not None:
            region = self.tree.identify("region", event.x, event.y)
            if region != "cell":
                self._end_inline_edit(commit=True)
            else:
                col = self.tree.identify_column(event.x)
                if col != "#3":
                    self._end_inline_edit(commit=True)

    def _on_tree_double_click(self, event):
        if self.recording:
            return
        row_iid = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        if not row_iid:
            return
        if col == "#3":
            self._begin_edit_delay_cell(row_iid)
        elif col == "#4":
            self._toggle_mode_cell(row_iid)

    def _begin_edit_delay_cell(self, iid: str):
        self._end_inline_edit(commit=True)
        bbox = self.tree.bbox(iid, column="delay_ms")
        if not bbox:
            return
        x, y, w, h = bbox
        current_ms_text = self.tree.set(iid, "delay_ms")

        self._edit_iid = iid
        self._edit_entry = ttk.Entry(self.tree)
        self._edit_entry.place(x=x, y=y, width=w, height=h)
        self._edit_entry.insert(0, current_ms_text)
        self._edit_entry.select_range(0, tk.END)
        self._edit_entry.focus()

        self._edit_entry.bind("<Return>", lambda _e: self._end_inline_edit(commit=True))
        self._edit_entry.bind("<Escape>", lambda _e: self._end_inline_edit(commit=False))
        self._edit_entry.bind("<FocusOut>", lambda _e: self._end_inline_edit(commit=True))

    def _end_inline_edit(self, commit: bool):
        if self._edit_entry is None or self._edit_iid is None:
            return
        iid = self._edit_iid
        entry = self._edit_entry
        new_text = entry.get().strip()

        self._edit_entry = None
        self._edit_iid = None
        entry.destroy()

        if not commit:
            return

        try:
            new_ms = int(new_text)
            if new_ms < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Invalid delay", "Enter a non-negative integer milliseconds, e.g. 55 or 5000.")
            return

        self.tree.set(iid, "delay_ms", str(new_ms))
        children = list(self.tree.get_children(""))
        try:
            idx = children.index(iid)
        except ValueError:
            return
        if 0 <= idx < len(self.events):
            self.events[idx]["delay"] = self.ms_int_to_sec(new_ms)

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
        return False

    def toggle_playback(self):
        if self._is_playing():
            self.stop_playback()
        else:
            self.play_macro()

    def play_macro(self):
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

        for i, ev in enumerate(self.events, start=1):
            if ev.get("mode") == "ind" and float(ev.get("delay", 0.0)) <= 0.0:
                messagebox.showerror("Invalid IND delay", f"Step {i} is IND but has 0ms delay.")
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

        self._set_status("Playing... (toggle key/button stops)")
        self._schedule_watchdog(session_id)

    def _press_key_game_safe(self, key: str):
        HOLD_S = 0.02
        try:
            input_driver.keyDown(key)
            time.sleep(HOLD_S)
            input_driver.keyUp(key)
        except Exception:
            try:
                input_driver.press(key)
            except Exception:
                pass

    def _play_worker_sequential_safe(self, session_id: int):
        try:
            self._play_worker_sequential(session_id)
        except Exception as ex:
            self._log_error("SEQ_THREAD", ex)
            self.root.after(
                0,
                lambda: self._set_status("SEQ thread error (see macro_errors.log). IND may still run.")
            )

    def _play_worker_sequential(self, session_id: int):
        speed = max(0.01, float(self.playback_speed.get()))
        repeat = bool(self.repeat_enabled.get())
        repeat_delay_s = self.ms_int_to_sec(int(self.repeat_delay_ms.get() or 0))

        seq_events = [ev for ev in self.events if ev.get("mode", "seq") == "seq"]
        if not seq_events:
            return

        while True:
            for step in seq_events:
                if self._stop_playback.is_set() or session_id != self._play_session_id:
                    return
                delay = float(step["delay"]) / speed
                time.sleep(max(0.0, delay))
                self._press_key_game_safe(step["key"])

            if self._stop_playback.is_set() or session_id != self._play_session_id:
                return
            if not repeat:
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
        self._stop_playback.set()
        self._set_status("Stopping...")

    # ---------------- Hotkey capture ----------------

    def capture_toggle_hotkey(self):
        if not KEYBOARD_AVAILABLE and not MOUSE_AVAILABLE:
            messagebox.showerror("Not available", "Need 'keyboard' and/or 'pynput' to capture a toggle input.")
            return
        self._capturing_toggle_key = True
        self._set_status("Press a keyboard key or mouse button for Play Toggle...")

    def _finish_capture_toggle_key(self, key_id: str):
        self._capturing_toggle_key = False
        self.play_toggle_key.set(str(key_id).strip().lower())
        self._resolve_toggle_key()
        self._set_status(f"Play toggle hotkey set to: {self.play_toggle_key.get()}")

    # ---------------- Save/Load/Clear ----------------

    def clear_macro(self):
        if self.recording:
            messagebox.showwarning("Recording", "Stop recording first.")
            return
        self._end_inline_edit(commit=True)
        self.events.clear()
        for iid in self.tree.get_children():
            self.tree.delete(iid)
        self._set_status("Cleared.")

    def save_macro(self):
        if not self.events:
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

        data = {
            "version": 4,
            "events": self.events,
            "repeat_enabled": bool(self.repeat_enabled.get()),
            "repeat_delay_ms": int(self.repeat_delay_ms.get()),
            "play_toggle_key": str(self.play_toggle_key.get()).strip().lower() or "f8",
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

            events = data.get("events", [])
            if not isinstance(events, list):
                raise ValueError("Invalid file format")

            cleaned = []
            for ev in events:
                if not isinstance(ev, dict):
                    continue
                k = str(ev.get("key", "")).lower()
                d = float(ev.get("delay", 0.0))
                mode = str(ev.get("mode", "seq")).lower()
                if mode not in ("seq", "ind"):
                    mode = "seq"
                if k:
                    cleaned.append({"key": k, "delay": max(0.0, d), "mode": mode})
            self.events = cleaned

            self.repeat_enabled.set(bool(data.get("repeat_enabled", False)))
            try:
                self.repeat_delay_ms.set(max(0, int(data.get("repeat_delay_ms", 250))))
            except Exception:
                pass

            tkey = str(data.get("play_toggle_key", "f8")).strip().lower()
            if tkey:
                self.play_toggle_key.set(tkey)
            self._resolve_toggle_key()

            for iid in self.tree.get_children():
                self.tree.delete(iid)

            for i, ev in enumerate(self.events, start=1):
                ms = self.sec_to_ms_int(ev["delay"])
                self.tree.insert("", "end", values=(f"{i:03d}", ev["key"], str(ms), self._mode_label(ev["mode"])))

            if KEYBOARD_AVAILABLE:
                self._setup_hotkeys()

            self._set_status(f"Loaded {len(self.events)} steps from {path}")
        except Exception as ex:
            messagebox.showerror("Load failed", str(ex))

    # ---------------- Hotkeys (F9/F10/ESC only) ----------------

    def apply_toggle_hotkey(self):
        key = str(self.play_toggle_key.get()).strip().lower()
        if not key:
            messagebox.showerror("Invalid", "Toggle hotkey cannot be empty.")
            return

        if key.startswith("mouse:") and not MOUSE_AVAILABLE:
            messagebox.showerror("Not available", "Mouse toggle requires 'pynput'.")
            return

        if not key.startswith("mouse:") and not KEYBOARD_AVAILABLE:
            messagebox.showerror("Not available", "Keyboard hotkeys require the 'keyboard' module.")
            return

        self.play_toggle_key.set(key)
        self._resolve_toggle_key()
        self._set_status(f"Applied play toggle hotkey: {key}")

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
    MacroApp(root)
    root.geometry("980x580")
    root.mainloop()


if __name__ == "__main__":
    main()
