#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
N번째 칸 일괄 삽입 도구 (File N-th Position Inserter)

- 기준: 줄 단위 / 구분자 칸(컬럼) / 문자 위치
- 동작: 삽입 / 바꾸기(덮어쓰기)
- 위치 기준: 앞에서 N번째 / 뒤에서 N번째 (파일마다 마지막 줄을 각각 계산, 1 = 맨 아래)
- 폴더 선택 + 하위 폴더 포함 여부 체크
- 폴더/파일 트리에서 체크·체크해제 (폴더 클릭 시 하위 전체 적용)
- 미리보기(변경 전/후 비교), 원본 백업(.bak), 인코딩 자동 판별(UTF-8 / UTF-8 BOM / CP949)

요구 사항: Python 3.8 이상, 표준 라이브러리만 사용
"""

import codecs
import csv
import datetime
import difflib
import fnmatch
import io
import os
import queue
import shutil
import threading
from dataclasses import dataclass

try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
except ImportError:  # 코어 함수만 import 해서 쓰는 경우
    tk = None


# ════════════════════════════════════════════════════════════
#  코어 로직
# ════════════════════════════════════════════════════════════

MODE_LINE = "line"        # N번째 줄
MODE_COLUMN = "column"    # 각 행의 N번째 칸 (구분자 기준)
MODE_CHAR = "char"        # N번째 문자 위치

ACTION_INSERT = "insert"
ACTION_REPLACE = "replace"

SCOPE_LINE = "line"       # 문자 위치: 각 줄마다
SCOPE_FILE = "file"       # 문자 위치: 파일 전체 기준

PLACEHOLDER_HELP = "치환자: {filename} {stem} {ext} {folder} {row} {date}"


@dataclass
class Options:
    mode: str = MODE_LINE
    action: str = ACTION_INSERT
    n: int = 1
    content: str = ""
    delimiter: str = ","
    use_csv: bool = True
    start_row: int = 1
    skip_empty: bool = True
    char_scope: str = SCOPE_LINE
    interpret_escape: bool = True
    backup: bool = True
    from_end: bool = False               # True: 뒤에서 N번째 (1 = 맨 아래/맨 끝)
    ignore_trailing_blank: bool = True   # 뒤에서 셀 때 파일 끝의 빈 줄은 제외 (줄 단위)


class SkipFile(Exception):
    """처리 대상이 아닌 파일 (바이너리, 인코딩 불명 등)"""


# ── 파일 입출력 ────────────────────────────────────────────

def read_text(path):
    with open(path, "rb") as f:
        raw = f.read()
    if b"\x00" in raw[:8192]:
        raise SkipFile("바이너리 파일")
    if raw.startswith(codecs.BOM_UTF8):
        return raw.decode("utf-8-sig"), "utf-8-sig"
    for enc in ("utf-8", "cp949"):
        try:
            return raw.decode(enc), enc
        except UnicodeDecodeError:
            continue
    raise SkipFile("인코딩 판별 실패 (UTF-8/CP949 아님)")


def write_text(path, text, encoding):
    with open(path, "w", encoding=encoding, newline="") as f:
        f.write(text)


def make_backup(path):
    bak = path + ".bak"
    if os.path.exists(bak):
        ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        bak = f"{path}.{ts}.bak"
    shutil.copy2(path, bak)
    return bak


# ── 텍스트 유틸 ────────────────────────────────────────────

def detect_newline(text):
    if "\r\n" in text:
        return "\r\n"
    if "\r" in text:
        return "\r"
    if "\n" in text:
        return "\n"
    return os.linesep


def split_lines(text, nl):
    if text == "":
        return [], True
    ends = text.endswith(nl)
    body = text[: -len(nl)] if ends else text
    return body.split(nl), ends


def join_lines(lines, nl, ends):
    return nl.join(lines) + (nl if ends and lines else "")


def normalize_nl(s, nl):
    return s.replace("\r\n", "\n").replace("\r", "\n").replace("\n", nl)


def unescape(s):
    """\\n, \\t, \\r, \\\\ 만 해석 (한글 등은 그대로 유지)"""
    table = {"n": "\n", "t": "\t", "r": "\r", "\\": "\\"}
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s) and s[i + 1] in table:
            out.append(table[s[i + 1]])
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def expand(template, path, row):
    base = os.path.basename(path)
    stem, ext = os.path.splitext(base)
    rep = {
        "{filename}": base,
        "{stem}": stem,
        "{ext}": ext.lstrip("."),
        "{folder}": os.path.basename(os.path.dirname(os.path.abspath(path))),
        "{row}": str(row),
        "{date}": datetime.date.today().isoformat(),
    }
    for k, v in rep.items():
        template = template.replace(k, v)
    return template


# ── 모드별 변환 ────────────────────────────────────────────

def _target_index(length, opt):
    """
    값이 들어갈 0부터 시작하는 위치.
    - 앞에서: N-1
    - 뒤에서 + 삽입: 결과적으로 끝에서 N번째가 되는 위치 (N=1 → 맨 뒤에 추가)
    - 뒤에서 + 바꾸기: 끝에서 N번째 항목 (N=1 → 마지막 항목)
    길이를 넘어가면 맨 앞(0)으로 맞춤.
    """
    n = opt.n
    if opt.from_end:
        if opt.action == ACTION_INSERT:
            return max(length - (n - 1), 0)
        return max(length - n, 0)
    return n - 1


def _edit_list(items, opt, value, pad=""):
    """편집 후 값이 들어간 위치(0부터)를 반환"""
    idx = _target_index(len(items), opt)
    if opt.action == ACTION_INSERT:
        while len(items) < idx:
            items.append(pad)
        items.insert(idx, value)
    else:
        while len(items) <= idx:
            items.append(pad)
        items[idx] = value
    return idx


def _edit_chars(s, opt, value):
    idx = _target_index(len(s), opt)
    if len(s) < idx:
        s = s + " " * (idx - len(s))
    if opt.action == ACTION_INSERT:
        return s[:idx] + value + s[idx:]
    return s[:idx] + value + s[idx + len(value):]   # 덮어쓰기


def _transform_line(text, opt, prep):
    nl = detect_newline(text)
    lines, ends = split_lines(text, nl)
    value = normalize_nl(prep(opt.n), nl)
    lines = _edit_list(lines, opt, value)
    return join_lines(lines, nl, ends)


def _transform_column(text, opt, prep):
    nl = detect_newline(text)
    d = opt.delimiter
    if d == "":
        raise ValueError("구분자가 비어 있습니다.")

    if opt.use_csv:
        if len(d) != 1:
            raise ValueError("CSV 규칙 사용 시 구분자는 1글자여야 합니다.")
        rows = list(csv.reader(io.StringIO(text, newline=""), delimiter=d))
        buf = io.StringIO(newline="")
        writer = csv.writer(buf, delimiter=d, lineterminator=nl)
        for i, fields in enumerate(rows, 1):
            empty = not any(f.strip() for f in fields)
            if i >= opt.start_row and not (opt.skip_empty and empty):
                fields = _edit_list(fields, opt, prep(i))
            writer.writerow(fields)
        out = buf.getvalue()
        if text and not text.endswith(("\n", "\r")) and out.endswith(nl):
            out = out[: -len(nl)]
        return out

    lines, ends = split_lines(text, nl)
    for i, line in enumerate(lines):
        row = i + 1
        if row < opt.start_row:
            continue
        if opt.skip_empty and line.strip() == "":
            continue
        lines[i] = d.join(_edit_list(line.split(d), opt, prep(row)))
    return join_lines(lines, nl, ends)


def _transform_char(text, opt, prep):
    nl = detect_newline(text)
    if opt.char_scope == SCOPE_FILE:
        return _edit_chars(text, opt, normalize_nl(prep(1), nl))

    lines, ends = split_lines(text, nl)
    for i, line in enumerate(lines):
        row = i + 1
        if row < opt.start_row:
            continue
        if opt.skip_empty and line.strip() == "":
            continue
        lines[i] = _edit_chars(line, opt, normalize_nl(prep(row), nl))
    return join_lines(lines, nl, ends)


def transform(text, opt, path):
    if opt.n < 1:
        raise ValueError("N은 1 이상이어야 합니다.")
    base = unescape(opt.content) if opt.interpret_escape else opt.content

    def prep(row):
        return expand(base, path, row)

    if opt.mode == MODE_LINE:
        return _transform_line(text, opt, prep)
    if opt.mode == MODE_COLUMN:
        return _transform_column(text, opt, prep)
    if opt.mode == MODE_CHAR:
        return _transform_char(text, opt, prep)
    raise ValueError(f"알 수 없는 모드: {opt.mode}")


def process_file(path, opt):
    """반환: ('changed', encoding, backup_path) 또는 ('same', encoding, None)"""
    text, enc = read_text(path)
    new = transform(text, opt, path)
    if new == text:
        return "same", enc, None
    bak = make_backup(path) if opt.backup else None
    write_text(path, new, enc)
    return "changed", enc, bak


# ── 파일 수집 ──────────────────────────────────────────────

def _split_list(s):
    return [p.strip() for p in s.replace(",", ";").split(";") if p.strip()]


def _match(filename, patterns):
    low = filename.lower()
    if low.endswith(".bak"):
        return False
    return any(fnmatch.fnmatch(low, p.lower()) for p in patterns)


def collect_files(root, recursive, patterns, exclude_dirs):
    pats = _split_list(patterns) or ["*"]
    excl = {e.lower() for e in _split_list(exclude_dirs)}
    result = []
    if recursive:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames if d.lower() not in excl)
            for fn in sorted(filenames):
                if _match(fn, pats):
                    result.append(os.path.join(dirpath, fn))
    else:
        for fn in sorted(os.listdir(root)):
            p = os.path.join(root, fn)
            if os.path.isfile(p) and _match(fn, pats):
                result.append(p)
    return result


def fmt_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n} B"


# ════════════════════════════════════════════════════════════
#  GUI
# ════════════════════════════════════════════════════════════

if tk is not None:

    class App:
        SYM = {0: "☐", 1: "☑", 2: "▣"}   # 해제 / 체크 / 일부 체크

        def __init__(self, root):
            self.root = root
            root.title("N번째 칸 일괄 삽입 도구")
            root.geometry("1040x820")
            root.minsize(900, 680)

            self.q = queue.Queue()
            self.running = False
            self.state = {}   # iid -> 0/1/2
            self.names = {}   # iid -> 표시 이름
            self.paths = {}   # 파일 iid -> 전체 경로
            self.root_iid = None

            self._build_folder_frame()
            self._build_tree_frame()
            self._build_option_frame()
            self._build_action_frame()
            self._on_mode()
            self.root.after(100, self._poll)

        # ── UI 구성 ─────────────────────────────────────

        def _build_folder_frame(self):
            f = ttk.LabelFrame(self.root, text="대상 폴더", padding=8)
            f.pack(fill="x", padx=10, pady=(10, 4))

            self.var_folder = tk.StringVar()
            ttk.Entry(f, textvariable=self.var_folder).grid(
                row=0, column=0, columnspan=6, sticky="ew")
            ttk.Button(f, text="찾아보기…", command=self._browse).grid(
                row=0, column=6, padx=(6, 0))

            self.var_recursive = tk.BooleanVar(value=True)
            ttk.Checkbutton(f, text="하위 폴더 포함", variable=self.var_recursive,
                            command=self._load_files).grid(
                row=1, column=0, sticky="w", pady=(6, 0))

            ttk.Label(f, text="파일 패턴").grid(row=1, column=1, sticky="e", padx=(12, 4), pady=(6, 0))
            self.var_patterns = tk.StringVar(value="*.txt;*.csv")
            ttk.Entry(f, textvariable=self.var_patterns, width=22).grid(
                row=1, column=2, sticky="w", pady=(6, 0))

            ttk.Label(f, text="제외 폴더").grid(row=1, column=3, sticky="e", padx=(12, 4), pady=(6, 0))
            self.var_exclude = tk.StringVar(value=".git;node_modules;__pycache__")
            ttk.Entry(f, textvariable=self.var_exclude, width=30).grid(
                row=1, column=4, sticky="ew", pady=(6, 0))

            ttk.Button(f, text="목록 불러오기", command=self._load_files).grid(
                row=1, column=6, padx=(6, 0), pady=(6, 0))
            f.columnconfigure(4, weight=1)

        def _build_tree_frame(self):
            f = ttk.LabelFrame(
                self.root, padding=8,
                text="파일 목록  (클릭: 체크/해제 · 폴더 클릭 시 하위 전체 적용 · Space: 선택 항목 토글)")
            f.pack(fill="both", expand=True, padx=10, pady=4)

            self.tree = ttk.Treeview(f, columns=("size", "status"),
                                     show="tree headings", selectmode="extended")
            self.tree.heading("#0", text="이름")
            self.tree.heading("size", text="크기")
            self.tree.heading("status", text="결과")
            self.tree.column("#0", width=520, stretch=True)
            self.tree.column("size", width=90, anchor="e", stretch=False)
            self.tree.column("status", width=300, stretch=True)
            self.tree.tag_configure("folder", foreground="#1f4e9e")
            self.tree.tag_configure("ok", foreground="#1a7f37")
            self.tree.tag_configure("err", foreground="#c62828")
            self.tree.tag_configure("same", foreground="#777777")

            vsb = ttk.Scrollbar(f, orient="vertical", command=self.tree.yview)
            self.tree.configure(yscrollcommand=vsb.set)
            self.tree.grid(row=0, column=0, sticky="nsew")
            vsb.grid(row=0, column=1, sticky="ns")
            f.rowconfigure(0, weight=1)
            f.columnconfigure(0, weight=1)

            self.tree.bind("<Button-1>", self._on_click)
            self.tree.bind("<space>", self._on_space)

            b = ttk.Frame(f)
            b.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 0))
            ttk.Button(b, text="전체 체크", command=lambda: self._set_all(1)).pack(side="left")
            ttk.Button(b, text="전체 해제", command=lambda: self._set_all(0)).pack(side="left", padx=4)
            ttk.Button(b, text="모두 펼치기", command=lambda: self._open_all(True)).pack(side="left", padx=(12, 0))
            ttk.Button(b, text="모두 접기", command=lambda: self._open_all(False)).pack(side="left", padx=4)
            self.lbl_count = ttk.Label(b, text="선택 0 / 전체 0")
            self.lbl_count.pack(side="right")

        def _build_option_frame(self):
            f = ttk.LabelFrame(self.root, text="삽입 옵션", padding=8)
            f.pack(fill="x", padx=10, pady=4)

            # 0행: 기준 / N / 동작
            ttk.Label(f, text="기준").grid(row=0, column=0, sticky="w")
            self.var_mode = tk.StringVar(value=MODE_LINE)
            mf = ttk.Frame(f)
            mf.grid(row=0, column=1, columnspan=3, sticky="w")
            for txt, val in (("줄 단위 (N번째 줄)", MODE_LINE),
                             ("구분자 칸 (각 행의 N번째 칸)", MODE_COLUMN),
                             ("문자 위치 (N번째 글자)", MODE_CHAR)):
                ttk.Radiobutton(mf, text=txt, value=val, variable=self.var_mode,
                                command=self._on_mode).pack(side="left", padx=(0, 10))

            ttk.Label(f, text="N번째").grid(row=0, column=4, sticky="e", padx=(10, 4))
            self.var_n = tk.StringVar(value="1")
            ttk.Spinbox(f, from_=1, to=10_000_000, textvariable=self.var_n, width=8).grid(
                row=0, column=5, sticky="w")

            ttk.Label(f, text="동작").grid(row=0, column=6, sticky="e", padx=(14, 4))
            self.var_action = tk.StringVar(value=ACTION_INSERT)
            af = ttk.Frame(f)
            af.grid(row=0, column=7, sticky="w")
            ttk.Radiobutton(af, text="삽입", value=ACTION_INSERT,
                            variable=self.var_action).pack(side="left")
            ttk.Radiobutton(af, text="바꾸기(덮어쓰기)", value=ACTION_REPLACE,
                            variable=self.var_action).pack(side="left", padx=(6, 0))

            # 1행: 구분자 / CSV / 시작 행 / 빈 줄
            ttk.Label(f, text="구분자").grid(row=1, column=0, sticky="w", pady=(8, 0))
            self.var_delim = tk.StringVar(value=",")
            self.cb_delim = ttk.Combobox(f, textvariable=self.var_delim, width=8,
                                         values=[",", ";", "|", "탭", "공백"])
            self.cb_delim.grid(row=1, column=1, sticky="w", pady=(8, 0))

            self.var_csv = tk.BooleanVar(value=True)
            self.chk_csv = ttk.Checkbutton(f, text="CSV 따옴표 규칙 적용", variable=self.var_csv)
            self.chk_csv.grid(row=1, column=2, sticky="w", padx=(10, 0), pady=(8, 0))

            ttk.Label(f, text="적용 시작 행").grid(row=1, column=4, sticky="e", padx=(10, 4), pady=(8, 0))
            self.var_start = tk.StringVar(value="1")
            self.sp_start = ttk.Spinbox(f, from_=1, to=10_000_000, textvariable=self.var_start, width=8)
            self.sp_start.grid(row=1, column=5, sticky="w", pady=(8, 0))

            self.var_skip_empty = tk.BooleanVar(value=True)
            self.chk_skip = ttk.Checkbutton(f, text="빈 줄 건너뛰기", variable=self.var_skip_empty)
            self.chk_skip.grid(row=1, column=6, columnspan=2, sticky="w", padx=(14, 0), pady=(8, 0))

            # 2행: 문자 위치 기준 범위
            ttk.Label(f, text="문자 위치 범위").grid(row=2, column=0, sticky="w", pady=(8, 0))
            self.var_scope = tk.StringVar(value=SCOPE_LINE)
            sf = ttk.Frame(f)
            sf.grid(row=2, column=1, columnspan=4, sticky="w", pady=(8, 0))
            self.rb_scope_line = ttk.Radiobutton(sf, text="각 줄마다", value=SCOPE_LINE,
                                                 variable=self.var_scope, command=self._on_mode)
            self.rb_scope_file = ttk.Radiobutton(sf, text="파일 전체에서 1회", value=SCOPE_FILE,
                                                 variable=self.var_scope, command=self._on_mode)
            self.rb_scope_line.pack(side="left")
            self.rb_scope_file.pack(side="left", padx=(10, 0))

            # 3행: 내용
            ttk.Label(f, text="넣을 내용").grid(row=3, column=0, sticky="w", pady=(8, 0))
            self.var_content = tk.StringVar()
            ttk.Entry(f, textvariable=self.var_content).grid(
                row=3, column=1, columnspan=7, sticky="ew", pady=(8, 0))

            # 4행: 기타
            of = ttk.Frame(f)
            of.grid(row=4, column=1, columnspan=7, sticky="w", pady=(6, 0))
            self.var_escape = tk.BooleanVar(value=True)
            ttk.Checkbutton(of, text="\\t \\n 이스케이프 해석", variable=self.var_escape).pack(side="left")
            self.var_backup = tk.BooleanVar(value=True)
            ttk.Checkbutton(of, text="원본 백업(.bak) 생성", variable=self.var_backup).pack(side="left", padx=(14, 0))
            ttk.Label(of, text=PLACEHOLDER_HELP, foreground="#666").pack(side="left", padx=(14, 0))

            f.columnconfigure(3, weight=1)

        def _build_action_frame(self):
            f = ttk.Frame(self.root, padding=(10, 4))
            f.pack(fill="x")
            self.btn_preview = ttk.Button(f, text="미리보기", command=self._preview)
            self.btn_preview.pack(side="left")
            self.btn_run = ttk.Button(f, text="체크된 파일에 적용", command=self._run)
            self.btn_run.pack(side="left", padx=6)
            self.progress = ttk.Progressbar(f, mode="determinate")
            self.progress.pack(side="left", fill="x", expand=True, padx=(10, 0))

            lf = ttk.LabelFrame(self.root, text="로그", padding=6)
            lf.pack(fill="both", padx=10, pady=(4, 10))
            self.log = tk.Text(lf, height=7, wrap="none", state="disabled")
            lsb = ttk.Scrollbar(lf, orient="vertical", command=self.log.yview)
            self.log.configure(yscrollcommand=lsb.set)
            self.log.pack(side="left", fill="both", expand=True)
            lsb.pack(side="right", fill="y")

        # ── 상태/활성화 ─────────────────────────────────

        def _on_mode(self):
            mode = self.var_mode.get()
            is_col = mode == MODE_COLUMN
            is_char = mode == MODE_CHAR
            per_row = is_col or (is_char and self.var_scope.get() == SCOPE_LINE)

            def en(widget, on):
                widget.state(["!disabled"] if on else ["disabled"])

            en(self.cb_delim, is_col)
            en(self.chk_csv, is_col)
            en(self.sp_start, per_row)
            en(self.chk_skip, per_row)
            en(self.rb_scope_line, is_char)
            en(self.rb_scope_file, is_char)

        def _log(self, msg):
            ts = datetime.datetime.now().strftime("%H:%M:%S")
            self.log.configure(state="normal")
            self.log.insert("end", f"[{ts}] {msg}\n")
            self.log.see("end")
            self.log.configure(state="disabled")

        # ── 폴더/파일 목록 ──────────────────────────────

        def _browse(self):
            d = filedialog.askdirectory(initialdir=self.var_folder.get() or os.getcwd())
            if d:
                self.var_folder.set(os.path.normpath(d))
                self._load_files()

        def _load_files(self):
            if self.running:
                return
            folder = self.var_folder.get().strip()
            if not folder:
                return
            if not os.path.isdir(folder):
                messagebox.showwarning("폴더 오류", "존재하지 않는 폴더입니다.")
                return
            try:
                files = collect_files(folder, self.var_recursive.get(),
                                      self.var_patterns.get(), self.var_exclude.get())
            except OSError as e:
                messagebox.showerror("목록 오류", str(e))
                return

            self.tree.delete(*self.tree.get_children())
            self.state.clear()
            self.names.clear()
            self.paths.clear()

            self.root_iid = "d:"
            root_name = os.path.basename(os.path.normpath(folder)) or folder
            self._add_node("", self.root_iid, root_name + "  (해당 폴더)", folder=True)
            dir_iids = {"": self.root_iid}

            for path in files:
                rel = os.path.relpath(path, folder)
                parts = rel.split(os.sep)
                parent, acc = self.root_iid, ""
                for part in parts[:-1]:
                    acc = os.path.join(acc, part) if acc else part
                    if acc not in dir_iids:
                        iid = "d:" + acc
                        self._add_node(parent, iid, part, folder=True)
                        dir_iids[acc] = iid
                    parent = dir_iids[acc]
                iid = "f:" + rel
                try:
                    size = os.path.getsize(path)
                except OSError:
                    size = 0
                self._add_node(parent, iid, parts[-1], size=size)
                self.paths[iid] = path

            self._update_count()
            scope = "하위 폴더 포함" if self.var_recursive.get() else "해당 폴더만"
            self._log(f"{len(files)}개 파일 불러옴 ({scope})")

        def _add_node(self, parent, iid, name, folder=False, size=None):
            self.state[iid] = 1
            self.names[iid] = name
            self.tree.insert(parent, "end", iid=iid, text=f"{self.SYM[1]} {name}",
                             values=(fmt_size(size) if size is not None else "", ""),
                             open=True, tags=("folder",) if folder else ())

        # ── 체크 처리 ───────────────────────────────────

        def _refresh(self, iid):
            self.tree.item(iid, text=f"{self.SYM[self.state[iid]]} {self.names[iid]}")

        def _set_subtree(self, iid, value):
            self.state[iid] = value
            self._refresh(iid)
            for c in self.tree.get_children(iid):
                self._set_subtree(c, value)

        def _update_parents(self, iid):
            p = self.tree.parent(iid)
            while p:
                states = {self.state[c] for c in self.tree.get_children(p)}
                self.state[p] = 1 if states == {1} else 0 if states == {0} else 2
                self._refresh(p)
                p = self.tree.parent(p)

        def _apply(self, iid, value):
            self._set_subtree(iid, value)
            self._update_parents(iid)

        def _toggle(self, iid):
            self._apply(iid, 0 if self.state.get(iid) == 1 else 1)
            self._update_count()

        def _on_click(self, event):
            if self.running:
                return "break"
            if self.tree.identify("region", event.x, event.y) not in ("tree", "cell"):
                return None
            if "indicator" in self.tree.identify("element", event.x, event.y):
                return None   # 펼치기/접기 화살표는 기본 동작
            iid = self.tree.identify_row(event.y)
            if iid:
                self._toggle(iid)
            return None

        def _on_space(self, _event):
            if self.running:
                return "break"
            sel = self.tree.selection()
            if sel:
                value = 0 if all(self.state[i] == 1 for i in sel) else 1
                for i in sel:
                    self._apply(i, value)
                self._update_count()
            return "break"

        def _set_all(self, value):
            if self.running:
                return
            for iid in self.tree.get_children(""):
                self._set_subtree(iid, value)
            self._update_count()

        def _open_all(self, opened, iid=""):
            for c in self.tree.get_children(iid):
                self.tree.item(c, open=opened)
                self._open_all(opened, c)

        def _checked_files(self):
            return [(iid, p) for iid, p in self.paths.items() if self.state.get(iid) == 1]

        def _update_count(self):
            self.lbl_count.configure(
                text=f"선택 {len(self._checked_files())} / 전체 {len(self.paths)}")

        # ── 옵션 수집 ───────────────────────────────────

        def _collect_options(self):
            try:
                n = int(self.var_n.get())
                start = int(self.var_start.get())
            except ValueError:
                messagebox.showwarning("입력 오류", "N번째 / 적용 시작 행은 숫자여야 합니다.")
                return None
            if n < 1 or start < 1:
                messagebox.showwarning("입력 오류", "N번째 / 적용 시작 행은 1 이상이어야 합니다.")
                return None

            raw = self.var_delim.get()
            delim = {"탭": "\t", "\\t": "\t", "공백": " "}.get(raw, raw)
            mode = self.var_mode.get()
            if mode == MODE_COLUMN:
                if delim == "":
                    messagebox.showwarning("입력 오류", "구분자를 입력하세요.")
                    return None
                if self.var_csv.get() and len(delim) != 1:
                    messagebox.showwarning("입력 오류", "CSV 규칙 사용 시 구분자는 1글자여야 합니다.")
                    return None

            return Options(
                mode=mode,
                action=self.var_action.get(),
                n=n,
                content=self.var_content.get(),
                delimiter=delim,
                use_csv=self.var_csv.get(),
                start_row=start,
                skip_empty=self.var_skip_empty.get(),
                char_scope=self.var_scope.get(),
                interpret_escape=self.var_escape.get(),
                backup=self.var_backup.get(),
            )

        # ── 미리보기 ────────────────────────────────────

        def _preview(self):
            opt = self._collect_options()
            if not opt:
                return
            target = next((i for i in self.tree.selection() if i in self.paths), None)
            if target is None:
                checked = self._checked_files()
                if not checked:
                    messagebox.showinfo("미리보기", "체크된 파일이 없습니다.")
                    return
                target = checked[0][0]
            path = self.paths[target]

            try:
                text, enc = read_text(path)
                new = transform(text, opt, path)
            except SkipFile as e:
                messagebox.showwarning("미리보기", f"건너뛰는 파일: {e}")
                return
            except Exception as e:  # noqa: BLE001
                messagebox.showerror("미리보기 오류", str(e))
                return

            limit = 300
            a = text.splitlines()[:limit]
            b = new.splitlines()[:limit]

            win = tk.Toplevel(self.root)
            win.title(f"미리보기 - {os.path.basename(path)}")
            win.geometry("1100x600")
            changed = "변경됨" if new != text else "변경 없음"
            ttk.Label(win, padding=6,
                      text=f"{path}   |   인코딩: {enc}   |   {changed}   |   앞 {limit}줄까지 표시 (변경 줄 강조, ⇥=탭)"
                      ).pack(fill="x")

            pane = ttk.PanedWindow(win, orient="horizontal")
            pane.pack(fill="both", expand=True, padx=6, pady=(0, 6))
            texts = []
            for title, lines in (("변경 전", a), ("변경 후", b)):
                fr = ttk.LabelFrame(pane, text=title, padding=4)
                t = tk.Text(fr, wrap="none", font=("Consolas", 10))
                ys = ttk.Scrollbar(fr, orient="vertical", command=t.yview)
                xs = ttk.Scrollbar(fr, orient="horizontal", command=t.xview)
                t.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
                t.grid(row=0, column=0, sticky="nsew")
                ys.grid(row=0, column=1, sticky="ns")
                xs.grid(row=1, column=0, sticky="ew")
                fr.rowconfigure(0, weight=1)
                fr.columnconfigure(0, weight=1)
                t.insert("1.0", "\n".join(l.replace("\t", "⇥\t") for l in lines))
                t.tag_configure("old", background="#ffe0e0")
                t.tag_configure("new", background="#d9f7d9")
                pane.add(fr, weight=1)
                texts.append(t)

            sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
            for tag, i1, i2, j1, j2 in sm.get_opcodes():
                if tag == "equal":
                    continue
                for i in range(i1, i2):
                    texts[0].tag_add("old", f"{i + 1}.0", f"{i + 1}.end+1c")
                for j in range(j1, j2):
                    texts[1].tag_add("new", f"{j + 1}.0", f"{j + 1}.end+1c")
            for t in texts:
                t.configure(state="disabled")

        # ── 실행 ────────────────────────────────────────

        def _run(self):
            if self.running:
                return
            opt = self._collect_options()
            if not opt:
                return
            files = self._checked_files()
            if not files:
                messagebox.showinfo("실행", "체크된 파일이 없습니다.")
                return
            backup_msg = "원본은 .bak 으로 백업됩니다." if opt.backup else "백업 없이 원본을 직접 수정합니다!"
            if not messagebox.askyesno("확인", f"{len(files)}개 파일에 적용합니다.\n{backup_msg}\n계속할까요?"):
                return

            self.running = True
            self.btn_run.state(["disabled"])
            self.btn_preview.state(["disabled"])
            self.progress.configure(maximum=len(files), value=0)
            for iid, _ in files:
                self.tree.set(iid, "status", "대기")
            self._log(f"적용 시작: {len(files)}개 파일")
            threading.Thread(target=self._worker, args=(files, opt), daemon=True).start()

        def _worker(self, files, opt):
            cnt = {"changed": 0, "same": 0, "skip": 0, "error": 0}
            for idx, (iid, path) in enumerate(files, 1):
                try:
                    result, enc, bak = process_file(path, opt)
                    cnt[result] += 1
                    if result == "changed":
                        status, tag = f"완료 ({enc})", "ok"
                        msg = f"완료: {path}" + (f"  → 백업 {os.path.basename(bak)}" if bak else "")
                    else:
                        status, tag, msg = "변경 없음", "same", f"변경 없음: {path}"
                except SkipFile as e:
                    cnt["skip"] += 1
                    status, tag, msg = f"건너뜀: {e}", "same", f"건너뜀: {path} ({e})"
                except Exception as e:  # noqa: BLE001
                    cnt["error"] += 1
                    status, tag, msg = f"오류: {e}", "err", f"오류: {path} ({e})"
                self.q.put(("file", iid, status, tag, idx, msg))
            summary = (f"종료 - 변경 {cnt['changed']} / 변경 없음 {cnt['same']} / "
                       f"건너뜀 {cnt['skip']} / 오류 {cnt['error']}")
            self.q.put(("done", summary))

        def _poll(self):
            try:
                while True:
                    item = self.q.get_nowait()
                    if item[0] == "file":
                        _, iid, status, tag, idx, msg = item
                        if self.tree.exists(iid):
                            self.tree.set(iid, "status", status)
                            self.tree.item(iid, tags=(tag,))
                        self.progress.configure(value=idx)
                        self._log(msg)
                    elif item[0] == "done":
                        self.running = False
                        self.btn_run.state(["!disabled"])
                        self.btn_preview.state(["!disabled"])
                        self._log(item[1])
                        messagebox.showinfo("완료", item[1])
            except queue.Empty:
                pass
            self.root.after(100, self._poll)


def main():
    if tk is None:
        print("tkinter 가 필요합니다. (Linux: sudo apt install python3-tk)")
        return
    try:  # Windows 고해상도 화면에서 글자 흐림 방지
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:  # noqa: BLE001
        pass
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()

#Made By Ephinence A. Kwon 2026-10-14, Version 1.2 File Inserter
