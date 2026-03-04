import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, ttk
import struct, os, tempfile, heapq, threading, random, time, shutil
from queue import Queue, Empty

# ==========================================================
# ỨNG DỤNG MINH HOẠ SẮP XẾP NGOẠI (External Merge Sort)
# File nhị phân chứa số thực double 8 bytes
# Mục tiêu: sắp xếp tăng dần/giảm dần và minh hoạ quá trình
#
# GHI CHÚ:
# PHẦN THUẬT TOÁN SẮP XẾP CHÍNH nằm tại:
#     (1) merge_k_runs(...)  : thuật toán trộn k run bằng heap
#     (2) _sort_worker(...)  : External Merge Sort (tạo runs + multi-pass merge)
# Các phần còn lại chủ yếu là giao diện Tkinter (APP/GUI).

# Định dạng nhị phân
FORMAT = "<d"          # little-endian double (8 bytes)
SIZE_OF_FLOAT = 8

# Màu giao diện
BG_DARK = "#0f1117"; BG_CARD = "#1a1d2e"; BG_PANEL = "#12151f"
ACCENT_BLUE = "#4f8ef7"; ACCENT_GREEN = "#27ae60"; ACCENT_GOLD = "#f39c12"
TEXT_MAIN = "#e8eaf6"; TEXT_DIM = "#7986cb"; TEXT_MUTED = "#4a5080"; BORDER = "#2a2d45"
LOG_COLORS = {"phase":"#4f8ef7","run":"#27ae60","merge":"#f39c12","done":"#2ecc71","error":"#e74c3c","info":"#b0bec5"}

# HỖ TRỢ I/O (KHÔNG PHẢI THUẬT TOÁN) 
# Các hàm đọc/ghi 1 double, đếm số phần tử, chia nhóm...
def chunked(lst, k):
    for i in range(0, len(lst), k):
        yield lst[i:i+k]

def file_num_elements(path: str) -> int:
    sz = os.path.getsize(path)
    if sz % SIZE_OF_FLOAT != 0:
        raise ValueError(f"Tệp không hợp lệ: {sz} bytes (không chia hết cho {SIZE_OF_FLOAT}).")
    return sz // SIZE_OF_FLOAT

def read_one_double(f):
    raw = f.read(SIZE_OF_FLOAT)
    if not raw:
        return None
    return struct.unpack(FORMAT, raw)[0]

def write_one_double(f, x: float):
    f.write(struct.pack(FORMAT, x))

def read_all_doubles(path: str, limit=None):
    out = []
    with open(path, "rb") as f:
        while True:
            v = read_one_double(f)
            if v is None:
                break
            out.append(v)
            if limit is not None and len(out) >= limit:
                break
    return out

def validate_sorted(path: str, reverse=False) -> bool:
    with open(path, "rb") as f:
        prev = read_one_double(f)
        if prev is None:
            return True
        while True:
            cur = read_one_double(f)
            if cur is None:
                return True
            if (not reverse and cur < prev) or (reverse and cur > prev):
                return False
            prev = cur

def mktemp_bin_in_dir(work_dir: str) -> str:
    """
    Tạo đường dẫn file tạm .bin trong work_dir (tránh lock trên Windows).
    (Lý do: tempfile.NamedTemporaryFile đôi khi gây lock khi reopen ở Windows)
    """
    fd, path = tempfile.mkstemp(prefix="run_", suffix=".bin", dir=work_dir)
    os.close(fd)
    return path



#  K-WAY MERGE (TRỘN K RUN ĐÃ SẮP XẾP) BẰNG MIN-HEAP
#  Input : danh sách đường dẫn tới các file run (mỗi run đã sắp xếp)
#  Output: 1 file out_path đã sắp xếp (kết quả trộn)

def merge_k_runs(run_paths, out_path, reverse=False):
    files = [open(p, "rb") for p in run_paths]
    heap = []

    # lấy phần tử đầu mỗi run đưa vào heap
    for i, rf in enumerate(files):
        v = read_one_double(rf)
        if v is None:
            continue
        key = -v if reverse else v
        heapq.heappush(heap, (key, i))

    with open(out_path, "wb") as out:
        # pop phần tử nhỏ nhất -> ghi ra output
        while heap:
            key, i = heapq.heappop(heap)
            val = -key if reverse else key
            write_one_double(out, val)

            # đọc tiếp từ run vừa lấy và đẩy vào heap
            nv = read_one_double(files[i])
            if nv is not None:
                nkey = -nv if reverse else nv
                heapq.heappush(heap, (nkey, i))

    for rf in files:
        rf.close()


# APP/GUI (GIAO DIỆN)
class ExternalSortApp:
    def __init__(self, root):
        self.root = root
        self.root.title("External Sort")
        self.root.geometry("920x750")
        self.root.configure(bg=BG_DARK)
        self.root.resizable(False, False)

        # Input
        self.input_path = tk.StringVar()
        self.run_buffer = tk.IntVar(value=10)          # số phần tử trong RAM để tạo 1 run
        self.merge_fanin = tk.IntVar(value=8)          # số run trộn mỗi PASS (>=2)
        self.sort_order = tk.StringVar(value="asc")
        self.num_elements = tk.IntVar(value=50)
        self.do_validate = tk.BooleanVar(value=True)
        self.demo_small = tk.BooleanVar(value=True)

        # State
        self.progress_var = tk.DoubleVar(value=0)
        self._sorting = False

        # Thread-safe queue cho UI
        self.uiq = Queue()

        self._build_ui()
        self._process_ui_queue()

    # UI thread-safe
    def _ui(self, func, *args, **kwargs):
        self.uiq.put((func, args, kwargs))

    def _process_ui_queue(self):
        try:
            while True:
                func, args, kwargs = self.uiq.get_nowait()
                func(*args, **kwargs)
        except Empty:
            pass
        self.root.after(50, self._process_ui_queue)

    # UI build
    def _build_ui(self):
        self._make_header()
        content = tk.Frame(self.root, bg=BG_DARK)
        content.pack(fill="both", expand=True, padx=18, pady=(0,12))

        left = tk.Frame(content, bg=BG_DARK)
        right = tk.Frame(content, bg=BG_DARK)
        left.pack(side="left", fill="both", expand=True, padx=(0,8))
        right.pack(side="right", fill="both", expand=True)

        self._make_file_card(left)
        self._make_config_card(left)
        self._make_buttons(left)
        self._make_stats_card(left)
        self._make_log_panel(right)

    def _make_header(self):
        hdr = tk.Frame(self.root, bg=BG_PANEL, height=56)
        hdr.pack(fill="x"); hdr.pack_propagate(False)
        tk.Label(hdr, text="Minh hoạ Sắp xếp Ngoại", font=("Segoe UI",14,"bold"),
                 bg=BG_PANEL, fg=TEXT_MAIN).pack(side="left", padx=18, pady=10)
        tk.Label(hdr, text="Cấu trúc dữ liệu và giải thuật nâng cao - CS523.Q21", font=("Segoe UI",9),
                 bg=BG_PANEL, fg=TEXT_MUTED).pack(side="right", padx=18)
        tk.Frame(self.root, bg=ACCENT_BLUE, height=2).pack(fill="x")

    def _card(self, parent, title):
        outer = tk.Frame(parent, bg=BG_CARD, highlightbackground=BORDER, highlightthickness=1)
        outer.pack(fill="x", pady=(0,10))
        tk.Label(outer, text=f"  {title}", font=("Segoe UI",9,"bold"),
                 bg=BG_CARD, fg=TEXT_DIM).pack(anchor="w", padx=10, pady=(8,2))
        body = tk.Frame(outer, bg=BG_CARD); body.pack(fill="x", padx=10, pady=(0,10))
        return body

    def _make_file_card(self, parent):
        body = self._card(parent, "TỆP DỮ LIỆU NGUỒN")
        row = tk.Frame(body, bg=BG_CARD); row.pack(fill="x")
        tk.Entry(row, textvariable=self.input_path, width=34, bg="#22253a", fg=TEXT_MAIN,
                 insertbackground=TEXT_MAIN, relief="flat", font=("Consolas",9),
                 highlightbackground=BORDER, highlightthickness=1).pack(side="left", ipady=5, padx=(0,6))
        self._btn(row, "Chọn tệp…", self.browse_file, ACCENT_BLUE).pack(side="left")

    def _make_config_card(self, parent):
        body = self._card(parent, "CẤU HÌNH")

        def row(label, wfn):
            r = tk.Frame(body, bg=BG_CARD); r.pack(fill="x", pady=3)
            tk.Label(r, text=label, font=("Segoe UI",9), bg=BG_CARD, fg=TEXT_MAIN,
                     width=30, anchor="w").pack(side="left")
            wfn(r)

        row("Bộ đệm tạo run (phần tử):", lambda r: tk.Spinbox(
            r, from_=2, to=20000, textvariable=self.run_buffer, width=10,
            bg="#22253a", fg=TEXT_MAIN, buttonbackground=BG_CARD,
            relief="flat", font=("Consolas",9)
        ).pack(side="left"))

        row("Số run trộn mỗi lượt (fan-in):", lambda r: tk.Spinbox(
            r, from_=2, to=64, textvariable=self.merge_fanin, width=10,
            bg="#22253a", fg=TEXT_MAIN, buttonbackground=BG_CARD,
            relief="flat", font=("Consolas",9)
        ).pack(side="left"))

        row("Số phần tử tệp test:", lambda r: tk.Spinbox(
            r, from_=10, to=200000, textvariable=self.num_elements, increment=10,
            width=10, bg="#22253a", fg=TEXT_MAIN, buttonbackground=BG_CARD,
            relief="flat", font=("Consolas",9)
        ).pack(side="left"))

        def make_radios(r):
            for txt, val in [("Tăng dần","asc"),("Giảm dần","desc")]:
                tk.Radiobutton(r, text=txt, variable=self.sort_order, value=val,
                               bg=BG_CARD, fg=TEXT_MAIN, selectcolor=BG_DARK,
                               activebackground=BG_CARD, font=("Segoe UI",9)).pack(side="left", padx=(0,10))
        row("Thứ tự sắp xếp:", make_radios)

        row("Kiểm tra đầu ra đã sắp xếp:", lambda r: tk.Checkbutton(
            r, variable=self.do_validate, bg=BG_CARD, fg=TEXT_MAIN,
            selectcolor=BG_DARK, activebackground=BG_CARD
        ).pack(side="left"))

        row("Minh hoạ chi tiết (file nhỏ):", lambda r: tk.Checkbutton(
            r, variable=self.demo_small, bg=BG_CARD, fg=TEXT_MAIN,
            selectcolor=BG_DARK, activebackground=BG_CARD
        ).pack(side="left"))

    def _make_buttons(self, parent):
        body = tk.Frame(parent, bg=BG_DARK); body.pack(fill="x", pady=(0,10))
        self._btn(body, "Tạo tệp test", self.create_test_file, "#37474f", width=22)\
            .pack(side="left", padx=(0,8))
        self.sort_btn = self._btn(body, "Bắt đầu sắp xếp", self.start_sort_thread,
                                  ACCENT_GREEN, width=18, bold=True)
        self.sort_btn.pack(side="left")

    def _make_stats_card(self, parent):
        body = self._card(parent, "THỐNG KÊ TRỰC TIẾP")
        self._runs_var = tk.StringVar(value="—")
        self._time_var = tk.StringVar(value="—")
        self._elements_var = tk.StringVar(value="—")

        for lbl, var, color in [
            ("Số run đã tạo:", self._runs_var, ACCENT_GOLD),
            ("Tổng phần tử:", self._elements_var, ACCENT_BLUE),
            ("Thời gian chạy:", self._time_var, ACCENT_GREEN)
        ]:
            r = tk.Frame(body, bg=BG_CARD); r.pack(fill="x", pady=2)
            tk.Label(r, text=lbl, bg=BG_CARD, fg=TEXT_MUTED, font=("Segoe UI",9),
                     width=18, anchor="w").pack(side="left")
            tk.Label(r, textvariable=var, bg=BG_CARD, fg=color,
                     font=("Consolas",10,"bold")).pack(side="left")

        tk.Label(body, text="Tiến trình:", bg=BG_CARD, fg=TEXT_MUTED,
                 font=("Segoe UI",9)).pack(anchor="w", pady=(6,2))

        style = ttk.Style(); style.theme_use("clam")
        style.configure("Sort.Horizontal.TProgressbar", troughcolor="#22253a",
                        background=ACCENT_BLUE, bordercolor=BORDER,
                        lightcolor=ACCENT_BLUE, darkcolor=ACCENT_BLUE)

        ttk.Progressbar(body, variable=self.progress_var, maximum=100,
                        length=340, style="Sort.Horizontal.TProgressbar").pack(fill="x", pady=(0,4))

    def _make_log_panel(self, parent):
        tk.Label(parent, text="  NHẬT KÝ HỆ THỐNG", font=("Segoe UI",9,"bold"),
                 bg=BG_DARK, fg=TEXT_DIM).pack(anchor="w")
        frame = tk.Frame(parent, bg=BORDER, padx=1, pady=1)
        frame.pack(fill="both", expand=True)

        self.log_area = scrolledtext.ScrolledText(
            frame, bg=BG_PANEL, fg=TEXT_MAIN, font=("Consolas",9),
            relief="flat", insertbackground=TEXT_MAIN,
            wrap="word", padx=8, pady=8
        )
        self.log_area.pack(fill="both", expand=True)

        for tag, color, bold in [
            ("phase",LOG_COLORS["phase"],True),
            ("run",LOG_COLORS["run"],False),
            ("merge",LOG_COLORS["merge"],False),
            ("done",LOG_COLORS["done"],True),
            ("error",LOG_COLORS["error"],True),
            ("info",LOG_COLORS["info"],False)
        ]:
            self.log_area.tag_configure(tag, foreground=color,
                                        font=("Consolas",9,"bold" if bold else "normal"))

        self._btn(parent, "Xóa nhật ký", lambda: self.log_area.delete("1.0", tk.END), "#2a2d45")\
            .pack(anchor="e", pady=(4,0))

    def _btn(self, parent, text, cmd, color, width=None, bold=False):
        kw = dict(text=text, command=cmd, bg=color, fg="white",
                  activebackground=color, activeforeground="white",
                  relief="flat", bd=0, cursor="hand2", padx=10, pady=5,
                  font=("Segoe UI",9,"bold" if bold else "normal"))
        if width:
            kw["width"] = width
        return tk.Button(parent, **kw)

    def log(self, msg, tag="info"):
        ts = time.strftime("%H:%M:%S")
        self.log_area.insert(tk.END, f"[{ts}] ", "info")
        self.log_area.insert(tk.END, f"{msg}\n", tag)
        self.log_area.see(tk.END)

    def _set_sort_btn(self, enabled: bool):
        self.sort_btn.configure(state="normal" if enabled else "disabled",
                                bg=ACCENT_GREEN if enabled else "#2a4a35")

    # Actions (APP/GUI)
    def browse_file(self):
        fn = filedialog.askopenfilename(filetypes=[("Tệp nhị phân","*.bin"),("Tất cả","*.*")])
        if not fn:
            return
        try:
            n = file_num_elements(fn)
        except Exception as e:
            messagebox.showerror("Tệp không hợp lệ", str(e))
            return
        self.input_path.set(fn)
        self._elements_var.set(str(n))
        self.log(f"Đã tải: {os.path.basename(fn)}  ({os.path.getsize(fn)/1024:.1f} KB · {n} phần tử)")

    def create_test_file(self):
        path = filedialog.asksaveasfilename(defaultextension=".bin", title="Lưu tệp test")
        if not path:
            return
        n = self.num_elements.get()
        with open(path, "wb") as f:
            for _ in range(n):
                write_one_double(f, random.uniform(1.0, 9999.99))
        self.input_path.set(path)
        self._elements_var.set(str(n))
        self.log(f"Đã tạo '{os.path.basename(path)}' ({n} số thực, {n*SIZE_OF_FLOAT} bytes)", "run")

    def start_sort_thread(self):
        if not self.input_path.get():
            messagebox.showwarning("Thiếu tệp", "Bạn hãy chọn (hoặc tạo) tệp dữ liệu nguồn trước.")
            return
        if self._sorting:
            return

        output_f = filedialog.asksaveasfilename(defaultextension=".bin", title="Lưu tệp đầu ra đã sắp xếp")
        if not output_f:
            return

        self._sorting = True
        self._set_sort_btn(False)
        self.progress_var.set(0)
        self._runs_var.set("…")
        self._time_var.set("…")

        threading.Thread(target=self._sort_worker, args=(output_f,), daemon=True).start()

 
    #  EXTERNAL MERGE SORT (SẮP XẾP NGOẠI)
    #  Gồm 2 giai đoạn:
    #   1 TẠO RUNS:
    #       - Đọc từng khối run_buf phần tử (đủ nhỏ để sort trong RAM)
    #       - Sort trong RAM
    #       - Ghi ra file run tạm trên đĩa
    #
    #   2 MULTI-PASS MERGE:
    #       - Mỗi PASS: trộn theo nhóm tối đa fan_in runs
    #       - Dùng merge_k_runs() (PHẦN 1) để trộn từng nhóm
    #       - Lặp cho tới khi chỉ còn 1 run => file đã sắp xếp hoàn toàn
    
    def _sort_worker(self, output_f: str):
        t0 = time.time()
        input_f = self.input_path.get()

        run_buf = self.run_buffer.get()
        fan_in = self.merge_fanin.get()
        reverse = (self.sort_order.get() == "desc")
        do_validate = self.do_validate.get()
        demo_small = self.demo_small.get()

        # Tạo thư mục tạm cùng ổ với OUTPUT để tránh WinError 17 (C: -> D:)
        out_dir = os.path.dirname(os.path.abspath(output_f)) or os.getcwd()
        work_dir = tempfile.mkdtemp(prefix="extsort_", dir=out_dir)

        try:
            if run_buf <= 1:
                raise ValueError("Bộ đệm tạo run phải > 1.")
            if fan_in < 2:
                raise ValueError("Fan-in phải >= 2.")

            total_elements = file_num_elements(input_f)
            self._ui(self._elements_var.set, str(total_elements))
            self._ui(self.log, f"Thư mục tạm (cùng ổ với đầu ra): {work_dir}", "info")

            # Minh hoạ file nhỏ: in dữ liệu đầu vào
            if demo_small and total_elements <= 40:
                arr_in = read_all_doubles(input_f)
                self._ui(self.log, "Minh hoạ (file nhỏ): DỮ LIỆU TRƯỚC SẮP XẾP:", "phase")
                self._ui(self.log, "  " + ", ".join(f"{x:.2f}" for x in arr_in), "info")

            if total_elements == 0:
                open(output_f, "wb").close()
                self._ui(self.progress_var.set, 100)
                self._ui(self._time_var.set, f"{(time.time()-t0):.3f}s")
                self._ui(self.log, "Tệp rỗng: đã tạo đầu ra rỗng.", "done")
                return

            #  GIAI ĐOẠN 1 (CREATE RUNS):
            #   - Đọc từng chunk run_buf phần tử từ file input
            #   - SORT TRONG RAM: data.sort(...)
            #   - Ghi ra file run tạm (mỗi run là 1 file đã sắp xếp)
            self._ui(self.log, "GIAI ĐOẠN 1 - TẠO CÁC RUN ĐÃ SẮP XẾP", "phase")

            runs = []
            processed = 0
            run_idx = 0

            with open(input_f, "rb") as f:
                while True:
                    chunk = f.read(SIZE_OF_FLOAT * run_buf)
                    if not chunk:
                        break
                    if len(chunk) % SIZE_OF_FLOAT != 0:
                        raise ValueError("Dữ liệu bị lỗi: không chia hết cho 8 bytes.")
                    count = len(chunk) // SIZE_OF_FLOAT

                    # --- Đọc chunk vào RAM ---
                    data = list(struct.unpack(f"<{count}d", chunk))

                    # --- SORT TRONG RAM (CỐT LÕI TẠO RUN) ---
                    data.sort(reverse=reverse)   # <===== ĐÂY LÀ BƯỚC SORT TRONG RAM

                    # --- Ghi run ra đĩa ---
                    tmp_path = mktemp_bin_in_dir(work_dir)
                    with open(tmp_path, "wb") as rf:
                        for x in data:
                            write_one_double(rf, x)

                    runs.append(tmp_path)
                    run_idx += 1
                    processed += count

                    self._ui(self.progress_var.set, (processed / total_elements) * 50.0)
                    self._ui(self._runs_var.set, str(run_idx))
                    self._ui(self.log, f"  Run {run_idx:>3} → {count} phần tử  [{data[0]:.2f} … {data[-1]:.2f}]", "run")

            #  GIAI ĐOẠN 2 (MULTI-PASS MERGE):
            #   - Lặp nhiều PASS cho đến khi còn 1 run cuối
            #   - Mỗi PASS: nhóm fan_in runs và trộn bằng merge_k_runs()
            #   - merge_k_runs() chính là THUẬT TOÁN TRỘN (PHẦN 1)

            self._ui(self.log, "GIAI ĐOẠN 2 - TRỘN NHIỀU LƯỢT (MULTI-PASS)", "phase")
            self._ui(self.log, f"  Fan-in = {fan_in} run / lượt (mỗi lượt = 1 PASS)", "merge")

            pass_no = 0
            current_runs = runs[:]

            while len(current_runs) > 1:
                pass_no += 1
                self._ui(self.log, f"  PASS {pass_no}: trộn {len(current_runs)} run …", "merge")
                new_runs = []

                for group in chunked(current_runs, fan_in):
                    if len(group) == 1:
                        new_runs.append(group[0])
                        continue

                    # --- TRỘN K RUN (CỐT LÕI) ---
                    out_run = mktemp_bin_in_dir(work_dir)
                    merge_k_runs(group, out_run, reverse=reverse)  # <===== ĐÂY LÀ BƯỚC TRỘN RUN
                    new_runs.append(out_run)

                    # xóa run cũ sau khi trộn xong
                    for p in group:
                        try:
                            os.remove(p)
                        except OSError:
                            pass

                current_runs = new_runs
                est = 50 + min(49, pass_no * 10)
                self._ui(self.progress_var.set, est)

            # Chỉ còn 1 run cuối => đó là file đã sắp xếp hoàn chỉnh
            final_run = current_runs[0]

            # Ghi file cuối: đảm bảo overwrite an toàn
            if os.path.exists(output_f):
                os.remove(output_f)

            try:
                os.replace(final_run, output_f)  # cùng ổ => OK
            except OSError:
                shutil.move(final_run, output_f)  # fallback

            # ----- Kiểm tra -----
            if do_validate:
                if not validate_sorted(output_f, reverse=reverse):
                    raise RuntimeError("Kiểm tra thất bại: tệp đầu ra CHƯA được sắp xếp!")
                self._ui(self.log, "Kiểm tra: tệp đầu ra đã sắp xếp", "done")

            # Minh hoạ file nhỏ: in dữ liệu đầu ra
            if demo_small and total_elements <= 40:
                arr_out = read_all_doubles(output_f)
                self._ui(self.log, "Minh hoạ (file nhỏ): DỮ LIỆU SAU SẮP XẾP:", "phase")
                self._ui(self.log, "  " + ", ".join(f"{x:.2f}" for x in arr_out), "info")

            elapsed = time.time() - t0
            self._ui(self.progress_var.set, 100)
            self._ui(self._time_var.set, f"{elapsed:.3f}s")

            order_lbl = "giảm dần" if reverse else "tăng dần"
            self._ui(self.log, "HOÀN TẤT", "done")
            self._ui(self.log, f"  Đã sắp xếp {total_elements} phần tử theo {order_lbl} trong {elapsed:.3f}s", "done")
            self._ui(self.log, f"  Tệp đầu ra → {output_f}", "done")
            self._ui(messagebox.showinfo, "Thành công",
                     f"Đã sắp xếp {total_elements} phần tử ({order_lbl}) trong {elapsed:.3f}s\n\nĐầu ra: {os.path.basename(output_f)}")

        except Exception as e:
            self._ui(self.log, f"LỖI: {e}", "error")
            self._ui(messagebox.showerror, "Lỗi", str(e))
        finally:
            # dọn thư mục tạm
            shutil.rmtree(work_dir, ignore_errors=True)
            self._sorting = False
            self._ui(self._set_sort_btn, True)


if __name__ == "__main__":
    root = tk.Tk()
    app = ExternalSortApp(root)
    root.mainloop()