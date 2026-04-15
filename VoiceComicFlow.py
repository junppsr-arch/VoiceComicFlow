# ==========================================
# VoiceComicFlow
# ==========================================
# 1. 調整可能パラメータ (グローバル定数)
# 2. キーバインド設定 & ユーティリティ
# 3. 初期化とデータ読み込み (PDF, YOLO, 設定)
# 4. ページ読み込み (load_page)
# 5. 図形データモデル (Shape Classes)
# 6. 描画＆HUDヘルパー
# 7. インタラクション・ホバー判定
# 8. コア描画 (render)
# 9. マウスイベント・HUDクリック判定
# 10. データ保存処理 & エクスポート
# 11. ウィンドウ表示＆メインループ
# ==========================================
"""
VoiceComicFlow.py  ─  オールインPythonアーキテクチャ (ボイスコミック制作向け)
──────────────────────────────────────────────────────────────────────
・PDF直接読み込み対応 (PyMuPDF)
・キャラ・カラーパレットHUD (CSV連携)
・Pillowによる日本語テロップ自動焼き込み
・Shift融合、日本語GIMP出力、キャラクター別登場一覧自動出力
・キャッシュレンダリングによる高速化＆手動レターボックス座標逆算
"""

import cv2
import numpy as np
from ultralytics import YOLO
import os
import csv
import json
import threading
import copy
import math
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
from tkinter import simpledialog
from tkinter import colorchooser
from tkinter import ttk  # 出力設定ダイアログ用
import fitz  # PyMuPDF
from PIL import Image, ImageDraw, ImageFont
import time

# --- PSD Tools ---
try:
    from psd_tools import PSDImage
    from psd_tools.api.layers import PixelLayer
    from psd_tools.constants import BlendMode
except ImportError:
    PSDImage = None
    print("[WARNING] psd-tools が見つかりませんでした。PSD出力機能は無効です。")

# ─────────────────────────────────────────
# ─────────────────────────────────────────
# 1. 調整可能パラメータ (グローバル定数)
# ─────────────────────────────────────────

# 1. 枠（Box / Ellipse）設定
BOX_THICKNESS     = 14      # 枠の太さ
BOX_ALPHA         = 200     # 枠の透過度 (0:透明 ～ 255:不透明)
GLOW_ALPHA        = 100     # 発光（上書き）の強さ (0:無効 ～ 255:不透明)
ERASE_GAP         = 14      # 枠同士が重なった時に削る隙間のピクセル数
YOLO_ALPHA        = 60      # YOLOボックスの透過度 (0~255)
HANDLE_DRAW_SIZE  = 8       # 拡縮ハンドルの四角の大きさ (元は5)


# 2. 直線（Line）設定
LINE_THICKNESS    = 30      # 直線の太さ
LINE_ALPHA        = 150     # 直線の透過度 (0:透明 ～ 255:不透明)
LINE_ERASE_GAP    = 5      # 直線と枠が交差した時に枠を削る隙間のピクセル数 (新規)

# 3. 消しゴム（Eraser）設定
ERASER_RADIUS     = 30      # 消しゴムの基本半径
ERASER_HARDNESS   = 0.8     # 消しゴムの硬さ (0.0:全体がフェード ～ 1.0:境界までクッキリ)

# 4. テキスト・フォント設定
TEXT_SIZE         = 30      # キャラ名
TEXT_PAD_X        = 10      # キャラ名背景の左右余白
TEXT_PAD_Y        = 10      # キャラ名背景の上下余白
TEXT_BG_THICKNESS = 6       # キャラ名背景の枠線太さ

NUMBER_SIZE       = 30      # セリフ番号
NUMBER_PAD        = 10      # セリフ番号背景の余白
NUMBER_MIN_WIDTH       = 30       # ★セリフ番号背景の最低文字幅保証
TEXT_BOLDNESS_STROKE   = 1       # ★キャラ名の文字の太さ(0-5程度)
NUMBER_BOLDNESS_STROKE = 1       # ★セリフ番号の文字の太さ(0-5程度)
PAGE_BOLDNESS_STROKE   = 1       # ★ページ番号の文字の太さ(0-5程度)

PAGE_TEXT_SIZE    = 40      # ページ番号
PAGE_OUTER_STROKE = 4
PAGE_INNER_STROKE = 0
PAGE_POS_MARGIN_X = 20      # 右端からのオフセット
PAGE_POS_MARGIN_Y = 20      # 上端からのオフセット

MANUAL_TEXT_SIZE  = 40      # 自由テキスト
MANUAL_TEXT_COLOR = (255, 255, 255) # BGR(白)

# 5. システム・HUD設定
HANDLE_MARGIN     = 30      # マウス当たり判定の余白
HUD_WIDTH         = 320     # パレットHUD領域の幅
HUD_FONT_SCALE    = 1
HUD_TEXT_OUTER_THICKNESS = 1
HUD_TEXT_INNER_THICKNESS = 2
HUD_TEXT_MARGIN_Y = 30
HUD_TEXT_LINE_SPACING = 40
WIN_NAME          = "VoiceComicFlow"
DISPLAY_MAX_H     = 980

NUMBER_FONT       = cv2.FONT_HERSHEY_SIMPLEX
NUMBER_SCALE      = 1.0
NUMBER_THICK      = 2

# ─────────────────────────────────────────
# ─────────────────────────────────────────
# 2. キーバインド設定 & ユーティリティ
# ─────────────────────────────────────────
KEY_PAGE_PREV     = ord('q')  # 前のページへ
KEY_PAGE_NEXT     = ord('w')  # 次のページへ
KEY_UNDO          = ord('e')  # 元に戻す
KEY_REDO          = ord('r')  # やり直し

KEY_TOGGLE_SHAPE  = ord('a')  # 四角⇔楕円 切り替え 兼 丸付けモード復帰
KEY_MODE_LINE     = ord('s')  # 直線モード (モブ・小セリフ用)
KEY_MODE_ERASER   = ord('d')  # 空白(消しゴム)モード
KEY_MODE_DELETE   = ord('f')  # 削除モード

KEY_MODE_NUMBER   = ord('z')  # 番号振りモード
KEY_MODE_TEXT     = ord('x')  # 自由テキストモード
KEY_RESET_PAGE    = ord('c')  # 本編開始ページ(P1)の設定

KEY_TOGGLE_EXPORT = ord('t')  # 終了時の自動出力(PDF/CSV/JSX)のON/OFF
KEY_LOAD_PALETTE  = ord('g')  # パレット(CSV)の手動読み込み
KEY_TOGGLE_YOLO   = ord('y')  # YOLO検知のON/OFF切り替え
KEY_TOGGLE_HELP   = ord('h')  # ヘルプ表示のON/OFF

export_enabled = False        # 終了時にCSV/PDFを出力するかどうかのフラグ

def get_help_lines():
    """現在のキーバインド設定を読み取り、整形された操作ガイドのテキストリストを返す"""
    return [
        "─── 操作ガイド ───",
        "【ページ・取り消し操作】",
        f" [{chr(KEY_PAGE_NEXT).upper()} / Enter] : 現在のページを次へ",
        f" [{chr(KEY_PAGE_PREV).upper()}]         : 前のページへ戻る",
        f" [{chr(KEY_UNDO).upper()}]         : Undo (最後の操作取消)",
        f" [{chr(KEY_REDO).upper()}]         : Redo (やり直し)",
        "",
        "【描画・編集モード切替】",
        f" [{chr(KEY_TOGGLE_SHAPE).upper()}]         : 四角⇔楕円 切替 (丸付けモードへ)",
        f" [{chr(KEY_MODE_LINE).upper()}]         : 直線モード (モブ・小セリフ用)",
        f" [{chr(KEY_MODE_ERASER).upper()}]         : 空白(消しゴム)モード",
        f" [{chr(KEY_MODE_DELETE).upper()}]         : 削除モード",
        f" [{chr(KEY_MODE_NUMBER).upper()}]         : セリフ番号振りモード",
        f" [{chr(KEY_MODE_TEXT).upper()}]         : 自由テキスト（ルビ・補足）モード",
        "",
        "【システム・設定操作】",
        f" [{chr(KEY_RESET_PAGE).upper()}]         : 本編開始ページ(P1) ＆ 総ページ数の設定",
        f" [{chr(KEY_TOGGLE_EXPORT).upper()}]         : 一括出力(PDF/CSV/JSX)ダイアログの表示",
        f" [{chr(KEY_LOAD_PALETTE).upper()}]         : パレット(CSV)の手動読み込み・上書き",
        f" [{chr(KEY_TOGGLE_YOLO).upper()}]         : YOLO(AI)検知のON/OFF",
        f" [{chr(KEY_TOGGLE_HELP).upper()}]         : 操作ガイドの表示/非表示 (この画面)",
        "─────────────────",
        " [右側パレット] : 左端クリックで色変更(HEX) / 右端[x]で削除",
        " [枠ドラッグ]   : 中心で移動 / 四隅で拡大縮小",
        " [×ボタン]     : 終了してデータ保存"
    ]

# ─────────────────────────────────────────
# フォント読み込み (日本語テロップ用)
# ─────────────────────────────────────────
FONT_BBOX_CACHE = {} # {text: bbox_Size}
try:
    JP_FONT = ImageFont.truetype("C:/Windows/Fonts/msgothic.ttc", TEXT_SIZE)
    NUM_FONT = ImageFont.truetype("C:/Windows/Fonts/msgothic.ttc", NUMBER_SIZE)
    PAGE_FONT = ImageFont.truetype("C:/Windows/Fonts/msgothic.ttc", PAGE_TEXT_SIZE)
except IOError:
    try:
        JP_FONT = ImageFont.truetype("C:/Windows/Fonts/meiryo.ttc", TEXT_SIZE)
        NUM_FONT = ImageFont.truetype("C:/Windows/Fonts/meiryo.ttc", NUMBER_SIZE)
        PAGE_FONT = ImageFont.truetype("C:/Windows/Fonts/meiryo.ttc", PAGE_TEXT_SIZE)
    except IOError:
        print("[WARNING] 日本語フォントが見つからないためデフォルトフォントを使用します")
        JP_FONT = ImageFont.load_default()
        NUM_FONT = ImageFont.load_default()
        PAGE_FONT = ImageFont.load_default()

DYNAMIC_FONT_CACHE = {}

def get_dynamic_font(size):
    global DYNAMIC_FONT_CACHE
    path = "C:/Windows/Fonts/msgothic.ttc"
    key = (path, size)
    if key not in DYNAMIC_FONT_CACHE:
        try:
            DYNAMIC_FONT_CACHE[key] = ImageFont.truetype(path, size)
        except:
            try:
                DYNAMIC_FONT_CACHE[key] = ImageFont.truetype("C:/Windows/Fonts/meiryo.ttc", size)
            except:
                DYNAMIC_FONT_CACHE[key] = ImageFont.load_default()
    return DYNAMIC_FONT_CACHE[key]

HELP_OVERLAY_CACHE = None

def get_help_overlay(w, h):
    global HELP_OVERLAY_CACHE
    if HELP_OVERLAY_CACHE is not None and HELP_OVERLAY_CACHE.shape[:2] == (h, w):
        return HELP_OVERLAY_CACHE
    
    # BGRA形式で初期化 (OpenCV互換)
    overlay = np.zeros((h, w, 4), dtype=np.uint8)
    cv2.rectangle(overlay, (0, 0), (w, h), (0, 0, 0, 190), -1) # 半透明の黒背景
    
    # Pillowに変換して日本語描画
    pil_img = Image.fromarray(overlay)
    draw = ImageDraw.Draw(pil_img)
    fnt = get_dynamic_font(32)  # ★フォントサイズを大きく変更
    
    texts = get_help_lines()
    
    y, x = 60, 60  # ★開始位置を少し内側に調整
    for t in texts:
        draw.text((x, y), t, font=fnt, fill=(255, 255, 255, 255))
        if t == "": y += 20          # 空行の隙間
        elif "───" in t: y += 50   # 区切り線の後の隙間
        else: y += 40                # 通常の行間
        
    HELP_OVERLAY_CACHE = np.array(pil_img)
    return HELP_OVERLAY_CACHE

def get_manual_text_size(text, font_size):
    fnt = get_dynamic_font(font_size)
    dummy_img = Image.new("RGBA", (1, 1))
    d = ImageDraw.Draw(dummy_img)
    try:
        bbox = d.textbbox((0, 0), text, font=fnt)
        return bbox[2] - bbox[0], bbox[3] - bbox[1]
    except Exception:
        return 100, 40

# ─────────────────────────────────────────
# ユーティリティ
# ─────────────────────────────────────────
def load_palette_from_csv(path):
    new_palette = []
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8-sig") as f:
            reader = csv.reader(f)
            for row in reader:
                if not row or row[0].startswith("キャラ名"): continue
                name = row[0].strip()
                color_str = row[1].strip() if len(row) > 1 else ""
                
                # 古いCSVの残骸(4列)にも対応する安全な読み込み
                is_inverted = False
                if len(row) >= 4: is_inverted = (row[3].strip().lower() == "true")
                elif len(row) == 3: is_inverted = (row[2].strip().lower() == "true")

                bgr = (255, 255, 255)
                if color_str.startswith("#"):
                    h_str = color_str.lstrip("#")
                    if len(h_str) == 6:
                        rgb = tuple(int(h_str[i:i+2], 16) for i in (0, 2, 4))
                        bgr = (rgb[2], rgb[1], rgb[0])
                new_palette.append({"name": name, "color": bgr, "is_inverted": is_inverted})
    return new_palette

def save_project_palette(palette, path):
    try:
        with open(path, "w", encoding="utf-8-sig", newline="") as f:
            writer = csv.writer(f, quoting=csv.QUOTE_ALL)
            writer.writerow(["キャラ名", "カラーコード", "反転フラグ"])
            for p in palette:
                b, g, r = p["color"]
                hex_color = f"#{r:02x}{g:02x}{b:02x}"
                writer.writerow([p["name"], hex_color, p.get("is_inverted", False)])
    except Exception as e:
        print(f"パレット保存エラー: {e}")

def imwrite_jp(filename, img, params=None):
    try:
        ext = os.path.splitext(filename)[1]
        result, n = cv2.imencode(ext, img, params)
        if result:
            with open(filename, mode='w+b') as f:
                n.tofile(f)
            return True
        return False
    except Exception as e:
        print(f"Save error: {filename} ({e})")
        return False

def imread_jp(filename, flags=cv2.IMREAD_UNCHANGED):
    try:
        if not os.path.exists(filename): return None
        n = np.fromfile(filename, dtype=np.uint8)
        img = cv2.imdecode(n, flags)
        return img
    except Exception:
        return None

def request_render():
    global need_full_render
    need_full_render = True

# ─────────────────────────────────────────
# デバウンス式ページ遷移管理
# ─────────────────────────────────────────
last_scroll_time  = 0.0
pending_page_load = False

def trigger_page_change(new_idx):
    global page_idx, last_scroll_time, pending_page_load
    global img, h, w_orig, drawn_actions

    # 完全に読み込まれているページから離れる時のみ保存する
    if not pending_page_load:
        save_current_page()

    page_idx = new_idx
    last_scroll_time = time.time()
    pending_page_load = True

    # ▼ 漫画ページだけの即時表示処理（超軽量）
    # 描画枠を一時クリアして合成処理のコストをゼロにする
    drawn_actions = []
    if page_idx in PAGE_CACHE:
        # バックグラウンド先読み済みの画像があれば、メモリから一瞬で表示
        cache_img, ch, cw = PAGE_CACHE[page_idx]
        img = cache_img.copy()
        h, w_orig = ch, cw

    # 新しいインデックス周辺の画像先読みをバックグラウンドで開始
    threading.Thread(target=prefetch_pages, args=(page_idx,), daemon=True).start()

    request_render()  # ベース画像とHUDだけを即時描画

# ─────────────────────────────────────────
# 3. 初期化とデータ読み込み (PDF, YOLO, 設定)
# ─────────────────────────────────────────
_root = tk.Tk()
_root.withdraw()


# 2. PDF読み込み
PDF_PATH = filedialog.askopenfilename(
    title="作業するPDFファイルを選択してください",
    filetypes=[("PDF files", "*.pdf")]
)

if not PDF_PATH:
    print("ファイルが選択されませんでした。終了します。")
    exit()

try:
    doc = fitz.open(PDF_PATH)
except Exception as e:
    messagebox.showerror("エラー", f"PDFを開けませんでした:\n{e}")
    exit()

# 3. 出力設定とプロジェクト設定のロード
raw_total = len(doc)
PDF_DIR = os.path.dirname(PDF_PATH)

base_pdf_name = os.path.splitext(os.path.basename(PDF_PATH))[0]
clean_base_name = base_pdf_name.replace("(全ページ)", "").strip()

EXPORT_DIR  = os.path.join(PDF_DIR, "_exports")
WORK_DIR    = os.path.join(PDF_DIR, "_work_data", clean_base_name)
OUTPUT_BASE = os.path.join(WORK_DIR, "output_layers")

os.makedirs(EXPORT_DIR, exist_ok=True)
os.makedirs(WORK_DIR, exist_ok=True)

# 4. パレットのロード（プロジェクト専用優先、無ければ大元からコピー）
PALETTE = []
proj_csv_path = os.path.join(WORK_DIR, "project_characters.csv")
root_csv_path = "characters.csv"

if os.path.exists(proj_csv_path):
    PALETTE = load_palette_from_csv(proj_csv_path)
    print(f"🎨 プロジェクト専用パレットを読み込みました")
else:
    PALETTE = load_palette_from_csv(root_csv_path)
    if not PALETTE:
        print("[INFO] characters.csvが見つからないため、デフォルトパレットを使用します。")
        PALETTE = [
            {"name": "キャラA", "color": (255, 0, 0), "is_inverted": False},
            {"name": "キャラB", "color": (0, 0, 255), "is_inverted": False},
            {"name": "キャラC", "color": (0, 200, 0), "is_inverted": False},
        ]
    save_project_palette(PALETTE, proj_csv_path)
    print(f"🎨 大元パレットをコピーし、専用パレットを作成しました")

TOTAL_PAGES = raw_total
LOGICAL_PAGE_OFFSET = 0

def load_project_settings():
    global TOTAL_PAGES, LOGICAL_PAGE_OFFSET
    settings_path = os.path.join(WORK_DIR, "project_settings.json")
    if os.path.exists(settings_path):
        try:
            with open(settings_path, "r", encoding="utf-8") as f:
                data = json.load(f)
                if "total_pages" in data: TOTAL_PAGES = data["total_pages"]
                if "logical_page_offset" in data: LOGICAL_PAGE_OFFSET = data["logical_page_offset"]
        except Exception:
            pass

def save_project_settings():
    os.makedirs(WORK_DIR, exist_ok=True)
    settings_path = os.path.join(WORK_DIR, "project_settings.json")
    try:
        with open(settings_path, "w", encoding="utf-8") as f:
            json.dump({
                "total_pages": TOTAL_PAGES,
                "logical_page_offset": LOGICAL_PAGE_OFFSET
            }, f, indent=2)
    except Exception:
        pass

def prefetch_pages(current_idx):
    """前後数ページをバックグラウンドで画像化してキャッシュする"""
    # 前2ページ、後3ページを維持
    keep_range = set(range(max(0, current_idx - 2), min(len(doc), current_idx + 4)))
    
    # 範囲外のキャッシュを削除してメモリ節約
    for k in list(PAGE_CACHE.keys()):
        if k not in keep_range:
            del PAGE_CACHE[k]
            
    # 範囲内の未キャッシュページをレンダリング
    for i in keep_range:
        if i not in PAGE_CACHE:
            try:
                p = doc[i]
                z = 1400 / p.rect.width
                m = fitz.Matrix(z, z)
                px = p.get_pixmap(matrix=m, alpha=False)
                tmp = np.frombuffer(px.samples, dtype=np.uint8).reshape(px.h, px.w, 3)
                p_img = cv2.cvtColor(tmp, cv2.COLOR_RGB2BGR)
                PAGE_CACHE[i] = (p_img, p_img.shape[0], p_img.shape[1])
            except Exception:
                pass

load_project_settings()

print(f"📄 開いたPDF: {os.path.basename(PDF_PATH)} (PDF実体:{raw_total}ページ / プロジェクト設定:{TOTAL_PAGES}ページ)")
print(f"📁 出力先: {OUTPUT_BASE}")

# YOLO初期化 (モデルファイルを中間作業データフォルダのルートに隔離)
SHARED_WORK_DIR = os.path.join(PDF_DIR, "_work_data")
os.makedirs(SHARED_WORK_DIR, exist_ok=True)
yolo_path = os.path.join(SHARED_WORK_DIR, "yolov8n.pt")
model = YOLO(yolo_path)

# グローバル状態
alt_pressed    = False
page_idx       = 0

img            = None
h, w_orig      = 0, 0
bboxes         = []
yolo_running   = False
yolo_enabled   = True
yolo_lock      = threading.Lock()

drawn_actions  = []
undo_stack     = []
redo_stack     = []
number_counter = 1
next_group_id  = 1
global_char_first_page = {}
show_help      = False
PAGE_CACHE     = {}   # {page_idx: (img_bgr, h, w_orig)}
shift_pressed  = False

def save_undo_state():
    global undo_stack, redo_stack
    undo_stack.append((copy.deepcopy(drawn_actions), number_counter))
    redo_stack.clear()

# キャッシュレンダリング用
cached_canvas  = None
need_full_render = True

# キャラ別登場一覧 (ページ単位の登場キャラ名リスト)
page_records = {}  # {page_idx: set(char_names)}

mouseX, mouseY = 0, 0
draw_shape     = "rect"
mode           = "color"
# ▼ 追加：読み込んだ結果パレットが空になっていた場合の自己修復
if not PALETTE:
    print("⚠️ パレットが空のため、初期キャラクターを生成します。")
    PALETTE = [{"name": "新規キャラ", "color": (255, 255, 255), "is_inverted": False}]
    save_project_palette(PALETTE, proj_csv_path)

current_palette_idx = 0
current_color = PALETTE[0]["color"]
current_name  = PALETTE[0]["name"]

dragging       = False
drag_start     = None
drag_end       = None
resizing_action = None
resizing_part   = None
drag_start_region = None
add_new_y_range = (-1, -1)



# ─────────────────────────────────────────
# 4. ページ読み込み (load_page)
# ─────────────────────────────────────────
def load_page(idx: int):
    global img, h, w_orig, bboxes, yolo_running, drawn_actions, number_counter, next_group_id
    
    if idx in PAGE_CACHE:
        cache_img, ch, cw = PAGE_CACHE[idx]
        img = cache_img.copy()
        h, w_orig = ch, cw
    else:
        page = doc[idx]
        zoom = 1400 / page.rect.width
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        temp = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, 3)
        img = cv2.cvtColor(temp, cv2.COLOR_RGB2BGR)
        h, w_orig = img.shape[:2]
        PAGE_CACHE[idx] = (img.copy(), h, w_orig)
    
    # バックグラウンド先読み開始
    threading.Thread(target=prefetch_pages, args=(idx,), daemon=True).start()
    
    # JSONから状態を復元
    global undo_stack
    folder_name = f"Page {idx + 1}"
    state_file = os.path.join(OUTPUT_BASE, folder_name, "state.json")
    drawn_actions = []
    undo_stack = []   # ← 追加：ページ遷移時にUndo履歴を確実に消去
    redo_stack = []
    number_counter = 1
    if os.path.exists(state_file):
        try:
            with open(state_file, "r", encoding="utf-8") as f:
                state = json.load(f)
            drawn_actions_loaded = state.get("drawn_actions", [])
            drawn_actions = []
            for act in drawn_actions_loaded:
                obj = Shape.from_dict(act)
                if obj: drawn_actions.append(obj)
            number_counter = state.get("number_counter", 1)
            print(f"🔄 ページ {idx + 1} の状態を復元しました (actions: {len(drawn_actions)})")
        except Exception as e:
            print(f"状態の復元に失敗しました: {e}")

    next_group_id = 1
    if drawn_actions:
        max_gid = max([getattr(a, "group_id", 0) for a in drawn_actions] + [0])
        next_group_id = max_gid + 1
    
    with yolo_lock:
        bboxes = []
        yolo_running = True

    def _run_yolo(frame, p_idx):
        global bboxes, yolo_running
        if not yolo_enabled:
            with yolo_lock:
                bboxes = []
                yolo_running = False
            request_render()
            return

        new_boxes = []
        try:
            results = model(frame, verbose=False)
            new_boxes = [list(map(int, b[:4])) for b in results[0].boxes.xyxy]
        except Exception:
            pass
        finally:
            with yolo_lock:
                bboxes = new_boxes
                yolo_running = False
        request_render()

    threading.Thread(target=_run_yolo, args=(img.copy(), idx), daemon=True).start()
    request_render()

    # 論理ページ番号初期化時のバグを回避するため load_page内でのウィンドウリサイズ処理を削除



class Shape:
    """
    共通インターフェースおよびファクトリメソッドを提供する基底クラス
    """
    def __init__(self, region, color=None, group_id=0):
        self.region = list(region)
        self.color = color if color is None else tuple(color)
        self.group_id = group_id
        self.shape_type = "base"

    def draw(self, layer):
        pass

    def check_hover(self, mx, my):
        return None, None

    def to_dict(self):
        pass

    @classmethod
    def from_dict(cls, data):
        stype = data.get("type")
        region = data.get("region", [])
        color = data.get("color")
        group_id = data.get("group_id", 0)

        obj = None
        if stype == "box":
            obj = BoxShape(region, color, data.get("shape", "rect"), data.get("op", "add"), group_id)
        elif stype == "line":
            obj = LineShape(region, color, group_id)
        elif stype == "text":
            obj = TextShape(region, data.get("char_name", ""), color)
        elif stype == "number":
            obj = NumberShape(region, data.get("num", 0), group_id)
        elif stype == "manual_text":
            obj = ManualTextShape(region, data.get("text", ""), data.get("font_size", MANUAL_TEXT_SIZE), color)
        elif stype == "eraser":
            obj = EraserShape(region)
        elif stype == "gaya":
            obj = GayaShape(region, data.get("base_name", ""), data.get("num", 0), color, data.get("inverted", False))
            
        # ★追加：どの図形であっても、char_nameを持っていれば一括で復元する
        if obj and "char_name" in data:
            obj.char_name = data["char_name"]
            
        return obj

class BoxShape(Shape):
    def __init__(self, region, color, shape="rect", op="add", group_id=0):
        super().__init__(region, color, group_id)
        self.shape = shape
        self.op = op
        self.shape_type = "box"

    def draw(self, layer, thickness=None, color_override=None):
        if len(self.region) < 4: return
        x1, y1, x2, y2 = self.region
        draw_thick = thickness if thickness is not None else BOX_THICKNESS
        draw_color = color_override if color_override is not None else self.color
        
        if self.shape == "ellipse":
            cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
            axes = (abs(x2 - x1) // 2, abs(y2 - y1) // 2)
            if axes[0] > 0 and axes[1] > 0:
                cv2.ellipse(layer, (cx, cy), axes, 0, 0, 360, draw_color, draw_thick)
        else:
            cv2.rectangle(layer, (x1, y1), (x2, y2), draw_color, draw_thick)

    def check_hover(self, mx, my):
        if len(self.region) < 4: return None, None
        x1, y1, x2, y2 = self.region
        margin = HANDLE_MARGIN
        rx1, ry1 = min(x1, x2), min(y1, y2)
        rx2, ry2 = max(x1, x2), max(y1, y2)
        if abs(mx - rx1) < margin and abs(my - ry1) < margin: return self, 'top-left'
        if abs(mx - rx2) < margin and abs(my - ry1) < margin: return self, 'top-right'
        if abs(mx - rx1) < margin and abs(my - ry2) < margin: return self, 'bottom-left'
        if abs(mx - rx2) < margin and abs(my - ry2) < margin: return self, 'bottom-right'
        if abs(mx - rx1) < margin and ry1 <= my <= ry2: return self, 'left'
        if abs(mx - rx2) < margin and ry1 <= my <= ry2: return self, 'right'
        if abs(my - ry1) < margin and rx1 <= mx <= rx2: return self, 'top'
        if abs(my - ry2) < margin and rx1 <= mx <= rx2: return self, 'bottom'
        if rx1 <= mx <= rx2 and ry1 <= my <= ry2: return self, 'center'
        return None, None

    def to_dict(self):
        return {
            "type": "box", "region": self.region, "color": list(self.color),
            "shape": self.shape, "op": self.op, "group_id": self.group_id,
            "char_name": getattr(self, "char_name", "")  # ★追加：キャラ名を保存
        }

class LineShape(Shape):
    def __init__(self, region, color, group_id=0):
        super().__init__(region, color, group_id)
        self.shape_type = "line"

    def draw(self, layer):
        if len(self.region) < 4: return
        l_color = (*self.color, LINE_ALPHA) if len(layer.shape) > 2 and layer.shape[2] == 4 else self.color
        cv2.line(layer, (self.region[0], self.region[1]), (self.region[2], self.region[3]), l_color, LINE_THICKNESS, cv2.LINE_AA)

    def check_hover(self, mx, my):
        if len(self.region) < 4: return None, None
        x1, y1, x2, y2 = self.region
        margin = HANDLE_MARGIN
        if abs(mx - x1) < margin and abs(my - y1) < margin: return self, 'line_p1'
        if abs(mx - x2) < margin and abs(my - y2) < margin: return self, 'line_p2'
        px, py = x2 - x1, y2 - y1
        l2 = px*px + py*py
        if l2 > 0:
            t = max(0, min(1, ((mx - x1)*px + (my - y1)*py) / l2))
            if math.hypot(mx - (x1 + t * px), my - (y1 + t * py)) < margin:
                return self, 'center'
        return None, None

    def to_dict(self):
        return {
            "type": "line", "region": self.region, "color": list(self.color), 
            "group_id": self.group_id,
            "char_name": getattr(self, "char_name", "")  # ★追加：キャラ名を保存
        }

class TextShape(Shape):
    def __init__(self, region, char_name, color):
        super().__init__(region, color)
        self.char_name = char_name
        self.shape_type = "text"

    def draw(self, draw):
        if len(self.region) < 4: return
        x1, y1 = self.region[0], self.region[1]
        c_rgba = (self.color[2], self.color[1], self.color[0], 255)
        bbox = draw.textbbox((0, 0), self.char_name, font=JP_FONT)
        tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
        draw.rectangle([x1, y1, x1 + tw + TEXT_PAD_X*2, y1 + th + TEXT_PAD_Y*2], fill=(255,255,255,255), outline=c_rgba, width=TEXT_BG_THICKNESS)
        draw.text((x1 + TEXT_PAD_X, y1 + TEXT_PAD_Y - 2), self.char_name, font=JP_FONT, fill=c_rgba, stroke_width=TEXT_BOLDNESS_STROKE, stroke_fill=c_rgba)

    def check_hover(self, mx, my):
        tx, ty = self.region[0], self.region[1]
        if tx - 10 <= mx <= tx + 100 and ty - 10 <= my <= ty + 40:
            return self, 'center'
        return None, None

    def to_dict(self):
        return {"type": "text", "region": self.region, "char_name": self.char_name, "color": list(self.color)}

class NumberShape(Shape):
    def __init__(self, pos, num, group_id=0):
        super().__init__(pos, (255, 255, 255), group_id)
        self.num = num
        self.shape_type = "number"

    def draw(self, draw):
        if len(self.region) < 2: return
        nx, ny = self.region[0], self.region[1]
        num_str = str(self.num)
        bbox = draw.textbbox((nx, ny), num_str, font=NUM_FONT, anchor="mm")
        target_tw = max(bbox[2] - bbox[0], bbox[3] - bbox[1], NUMBER_MIN_WIDTH)
        box_left, box_right = nx - (target_tw / 2) - NUMBER_PAD, nx + (target_tw / 2) + NUMBER_PAD
        box_top, box_bottom = bbox[1] - NUMBER_PAD, bbox[3] + NUMBER_PAD
        draw.rectangle([box_left, box_top, box_right, box_bottom], fill=(0,0,0,255), outline=(255,255,255,255), width=2)

        draw.text((nx, ny), num_str, font=NUM_FONT, fill=(255,255,255,255), anchor="mm", stroke_width=NUMBER_BOLDNESS_STROKE, stroke_fill=(255,255,255,255))

    def check_hover(self, mx, my):
        if math.hypot(mx - self.region[0], my - self.region[1]) <= NUMBER_SIZE + 10:
            return self, 'move_number'
        return None, None

    def to_dict(self):
        return {"type": "number", "region": self.region, "num": self.num, "group_id": self.group_id}

class ManualTextShape(Shape):
    def __init__(self, region, text, font_size, color):
        super().__init__(region, color)
        self.text = text
        self.font_size = font_size
        self.shape_type = "manual_text"

    def draw(self, draw):
        if len(self.region) < 4: return
        tx1, ty1 = self.region[0], self.region[1]
        clr_rgba = (self.color[2], self.color[1], self.color[0], 255)
        fnt = get_dynamic_font(self.font_size)
        draw.text((tx1, ty1), self.text, font=fnt, fill=clr_rgba)

    def check_hover(self, mx, my):
        x1, y1, x2, y2 = self.region
        if min(x1, x2) <= mx <= max(x1, x2) and min(y1, y2) <= my <= max(y1, y2):
            return self, 'center'
        return None, None

    def to_dict(self):
        return {"type": "manual_text", "region": self.region, "text": self.text, "font_size": self.font_size, "color": list(self.color)}

class EraserShape(Shape):
    def __init__(self, region):
        super().__init__(region)
        self.shape_type = "eraser"

    def draw(self, layer):
        if len(self.region) < 2: return
        ex, ey = self.region[0], self.region[1]
        r = self.region[2] if len(self.region) >= 3 else ERASER_RADIUS
        h_l, w_l = layer.shape[:2]
        x1, y1 = max(0, ex - r), max(0, ey - r)
        x2, y2 = min(w_l, ex + r), min(h_l, ey + r)
        if x2 <= x1 or y2 <= y1: return
        Y, X = np.ogrid[y1:y2, x1:x2]
        dist = np.sqrt((X - ex)**2 + (Y - ey)**2)
        core_r = r * ERASER_HARDNESS
        mask = np.clip((dist - core_r) / (r - core_r), 0.0, 1.0) if r > core_r else np.where(dist <= r, 0.0, 1.0)
        layer[y1:y2, x1:x2, 3] = (layer[y1:y2, x1:x2, 3] * mask).astype(np.uint8)

    def check_hover(self, mx, my):
        if len(self.region) < 2: return None, None
        ex, ey = self.region[0], self.region[1]
        r = self.region[2] if len(self.region) >= 3 else ERASER_RADIUS
        dist = math.hypot(mx - ex, my - ey)
        margin = 30 # HANDLE_MARGINの代替
        if abs(dist - r) <= margin: return self, 'edge'
        if dist <= r: return self, 'center'
        return None, None

    def to_dict(self):
        return {"type": "eraser", "region": self.region}

class GayaShape(Shape):
    def __init__(self, pos, base_name, num, color, inverted=False):
        super().__init__(pos, color)
        self.base_name = base_name
        self.char_name = base_name  # CSV集計用
        self.num = num
        self.inverted = inverted
        self.shape_type = "gaya"

    def draw(self, draw):
        if len(self.region) < 2: return
        nx, ny = self.region[0], self.region[1]
        text = f"{self.base_name}{self.num}"
        bbox = draw.textbbox((nx, ny), text, font=JP_FONT, anchor="mm")
        box_left, box_right = bbox[0] - TEXT_PAD_X, bbox[2] + TEXT_PAD_X
        box_top, box_bottom = bbox[1] - TEXT_PAD_Y, bbox[3] + TEXT_PAD_Y
        c_rgba = (self.color[2], self.color[1], self.color[0], 255)
        
        if self.inverted:
            bg_fill, outline_color, text_fill = (255, 255, 255, 255), c_rgba, c_rgba
        else:
            bg_fill, outline_color, text_fill = c_rgba, c_rgba, (255, 255, 255, 255)
            
        draw.rectangle([box_left, box_top, box_right, box_bottom], fill=bg_fill, outline=outline_color, width=TEXT_BG_THICKNESS)
        draw.text((nx, ny), text, font=JP_FONT, fill=text_fill, anchor="mm", stroke_width=TEXT_BOLDNESS_STROKE, stroke_fill=text_fill)

    def check_hover(self, mx, my):
        if math.hypot(mx - self.region[0], my - self.region[1]) <= 40: return self, 'center'
        return None, None

    def to_dict(self):
        return {"type": "gaya", "region": self.region, "base_name": self.base_name, "num": self.num, "color": list(self.color), "inverted": self.inverted, "char_name": self.char_name}


# ─────────────────────────────────────────
# 5. 描画＆HUDヘルパー
# ─────────────────────────────────────────
def draw_shape_on(layer, x1, y1, x2, y2, color_bgra, shape, thickness=BOX_THICKNESS):
    if shape == "ellipse":
        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
        axes   = ((abs(x2 - x1) // 2, abs(y2 - y1) // 2))
        if axes[0] > 0 and axes[1] > 0:
            cv2.ellipse(layer, (cx, cy), axes, 0, 0, 360, color_bgra, thickness)
    else:
        cv2.rectangle(layer, (x1, y1), (x2, y2), color_bgra, thickness)

def erase_region(layer, x1, y1, x2, y2, gap=ERASE_GAP):
    ey1 = max(0, y1 - gap); ey2 = min(h,  y2 + gap)
    ex1 = max(0, x1 - gap); ex2 = min(w_orig, x2 + gap)
    layer[ey1:ey2, ex1:ex2] = (0, 0, 0, 0)

def put_hud_text(display, text, x, y, fg=(255, 255, 255), scale=HUD_FONT_SCALE):
    cv2.putText(display, text, (int(x), int(y)), cv2.FONT_HERSHEY_SIMPLEX, scale, (0, 0, 0), int(HUD_TEXT_OUTER_THICKNESS))
    cv2.putText(display, text, (int(x), int(y)), cv2.FONT_HERSHEY_SIMPLEX, scale, fg, int(HUD_TEXT_INNER_THICKNESS))

def draw_color_swatch(display, bgr_color, x, y, size=14, border=(255,255,255), border_thick=1):
    cv2.rectangle(display, (x, y - size), (x + size, y), bgr_color, -1)
    if border:
        cv2.rectangle(display, (x, y - size), (x + size, y), border, border_thick)

def render_texts_to_layer(layer):
    layer_rgba = cv2.cvtColor(layer, cv2.COLOR_BGRA2RGBA)
    img_pil = Image.fromarray(layer_rgba)
    draw = ImageDraw.Draw(img_pil)
    
    for action in drawn_actions:
        if isinstance(action, (TextShape, NumberShape, ManualTextShape, GayaShape)):
            action.draw(draw)

    logical_num = page_idx - LOGICAL_PAGE_OFFSET + 1
    if 1 <= logical_num <= TOTAL_PAGES:
        page_text = f"{logical_num:02d}/{TOTAL_PAGES:02d}"
        page_tw, _ = get_text_size(page_text)
        px = max(10, w_orig - page_tw - PAGE_POS_MARGIN_X)
        py = PAGE_POS_MARGIN_Y
        draw.text((px, py), page_text, font=PAGE_FONT, fill=(0,0,0,255), stroke_width=PAGE_OUTER_STROKE, stroke_fill=(255,255,255,255))
        draw.text((px, py), page_text, font=PAGE_FONT, fill=(0,0,0,255), stroke_width=PAGE_INNER_STROKE, stroke_fill=(0,0,0,255))
        draw.text((px, py), page_text, font=PAGE_FONT, fill=(0,0,0,255), stroke_width=PAGE_BOLDNESS_STROKE, stroke_fill=(0,0,0,255))

    layer[:] = cv2.cvtColor(np.array(img_pil), cv2.COLOR_RGBA2BGRA)

def get_text_size(text):
    if text in FONT_BBOX_CACHE: return FONT_BBOX_CACHE[text]
    dummy_img = Image.new("RGBA", (10, 10))
    d = ImageDraw.Draw(dummy_img)
    try:
        bbox = d.textbbox((0, 0), text, font=JP_FONT)
        tw = (bbox[2] - bbox[0]) + TEXT_PAD_X * 2
        th = (bbox[3] - bbox[1]) + TEXT_PAD_Y * 2
    except Exception:
        tw, th = 100, 40
    FONT_BBOX_CACHE[text] = (tw, th)
    return tw, th


# ─────────────────────────────────────────
# 6. インタラクション・ホバー判定
# ─────────────────────────────────────────
def get_hovered_handle(x, y, flags=0):
    ignore_shapes = bool(flags & cv2.EVENT_FLAG_ALTKEY)
    for action in reversed(drawn_actions):
        # Z(番号)モードの時は、NumberShapeとGayaShape以外は絶対に掴まない（枠の中へのスタンプ配置を優先）
        if mode == "numbering" and not isinstance(action, (NumberShape, GayaShape)):
            continue
        # Altキー押下時、またはcolor/lineモード以外の時はBox/Lineを掴まない
        if (ignore_shapes or mode not in ["color", "line", "numbering"]) and isinstance(action, (BoxShape, LineShape)):
            continue
        ha, part = action.check_hover(x, y)
        if ha: return ha, part
    return None, None

def get_deletable_action(mx, my, margin=15):
    for action in reversed(drawn_actions):
        t = action.shape_type
        region = action.region
        if t in ["box", "text", "manual_text"] and len(region) >= 4:
            x1, y1, x2, y2 = region[0], region[1], region[2], region[3]
            if min(x1, x2) <= mx <= max(x1, x2) and min(y1, y2) <= my <= max(y1, y2):
                return action
        elif t == "line" and len(region) >= 4:
            x1, y1, x2, y2 = region[0], region[1], region[2], region[3]
            if min(x1, x2) - margin <= mx <= max(x1, x2) + margin and min(y1, y2) - margin <= my <= max(y1, y2) + margin:
                px, py = x2 - x1, y2 - y1
                norm = px*px + py*py
                dist = math.hypot(mx - x1, my - y1) if norm == 0 else math.hypot(mx - (x1 + max(0.0, min(1.0, ((mx - x1) * px + (my - y1) * py) / norm)) * px), my - (y1 + max(0.0, min(1.0, ((mx - x1) * px + (my - y1) * py) / norm)) * py))
                if dist <= margin: return action
        elif t == "number" and len(region) >= 2:
            if math.hypot(mx - region[0], my - region[1]) <= NUMBER_SIZE: return action
        elif t == "eraser" and len(region) >= 2:
            r = region[2] if len(region) >= 3 else getattr(action, "radius", ERASER_RADIUS)
            if math.hypot(mx - region[0], my - region[1]) <= r: return action
        elif t == "gaya" and len(region) >= 2:
            if math.hypot(mx - region[0], my - region[1]) <= 40: return action
    return None

def hovered_yolo_box(mx, my):
    with yolo_lock: snapshot = list(bboxes)
    for box in snapshot:
        if len(box) < 4: continue
        x1, y1, x2, y2 = box[0], box[1], box[2], box[3]
        if x1 <= mx <= x2 and y1 <= my <= y2: return box
    return None

def get_target_group_id(box_region, use_shift, use_ctrl, current_char_name):
    global next_group_id
    if use_shift or use_ctrl:
        bx1, by1, bx2, by2 = box_region
        for action in reversed(drawn_actions):
            if isinstance(action, BoxShape) and getattr(action, "char_name", None) == current_char_name:
                rx1, ry1, rx2, ry2 = action.region
                if not (bx2 < rx1 or bx1 > rx2 or by2 < ry1 or by1 > ry2):
                    return action.group_id
        for action in reversed(drawn_actions):
            if isinstance(action, BoxShape) and getattr(action, "char_name", None) == current_char_name:
                return action.group_id
    g = next_group_id
    next_group_id += 1
    return g

def check_and_add_text_action(region, char_name, color):
    if not char_name: return
    
    # ★ガヤ의 非表示ロジックを撤去（Zキーのスタンプ時に自動削除されるため、ここでは普通に出す）
    if not is_char_name_labeled(char_name):
        tw, th = get_text_size(char_name)
        x1, y1 = region[0], region[1]
        tx1 = x1
        ty1 = y1 - th - 5
        if ty1 < 0: ty1 = y1 + 5
        drawn_actions.append(TextShape([tx1, ty1, tx1 + tw, ty1 + th], char_name, color))

def get_next_gaya_number(base_name):
    """
    現在のページと全保存済みページの中にある同じbase_nameを持つGayaShapeの最大num+1を返す
    """
    max_num = 0
    # 1. メモリ上の現在のページ
    for act in drawn_actions:
        if isinstance(act, GayaShape) and act.base_name == base_name:
            max_num = max(max_num, act.num)
    
    # 2. ファイルに保存された全ページ
    for p in range(len(doc)):
        if p == page_idx: continue
        folder_name = f"Page {p + 1}"
        state_file = os.path.join(OUTPUT_BASE, folder_name, "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                for ad in data.get("drawn_actions", []):
                    if ad.get("type") == "gaya" and ad.get("base_name") == base_name:
                        max_num = max(max_num, ad.get("num", 0))
            except: pass
    return max_num + 1

def recalculate_gaya_numbers():
    """現在のページ内のガヤ連番を詰め直す（他ページ依存を考慮）"""
    gaya_dict = {}
    for act in drawn_actions:
        if isinstance(act, GayaShape):
            gaya_dict.setdefault(act.base_name, []).append(act)
    
    for base_name, shapes in gaya_dict.items():
        base_num = 0
        for p in range(len(doc)):
            if p == page_idx: continue
            state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
            if os.path.exists(state_file):
                try:
                    with open(state_file, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    for ad in data.get("drawn_actions", []):
                        if ad.get("type") == "gaya" and ad.get("base_name") == base_name:
                            base_num = max(base_num, ad.get("num", 0))
                except: pass
        for i, act in enumerate(shapes):
            act.num = base_num + 1 + i


# ─────────────────────────────────────────
# 7. コア描画 (render)
# ─────────────────────────────────────────
def render_boxes_to_layer(target_layer):
    line_mask = np.zeros((h, w_orig), dtype=np.uint8)
    lines = [sh for sh in drawn_actions if isinstance(sh, LineShape)]
    for line in lines:
        if len(line.region) < 4: continue
        lx1, ly1, lx2, ly2 = line.region
        cv2.line(line_mask, (lx1, ly1), (lx2, ly2), 255, LINE_THICKNESS + LINE_ERASE_GAP * 2, cv2.LINE_AA)

    group_order = []
    group_boxes = {}
    for action in drawn_actions:
        if isinstance(action, BoxShape):
            gid = action.group_id
            if gid not in group_boxes:
                group_boxes[gid] = []
                group_order.append(gid)
            group_boxes[gid].append(action)

    final_layer = np.zeros((h, w_orig, 4), dtype=np.uint8)
    kernel = np.ones((ERASE_GAP*2+1, ERASE_GAP*2+1), np.uint8)

    for gid in group_order:
        g_actions = group_boxes[gid]
        color = (*g_actions[0].color, BOX_ALPHA)
        shape_mask = np.zeros((h, w_orig), dtype=np.uint8)
        for act in g_actions:
            fill_val = 255 if act.op == "add" else 0
            act.draw(shape_mask, thickness=-1, color_override=fill_val)

        contours, _ = cv2.findContours(shape_mask, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
        g_layer = np.zeros((h, w_orig, 4), dtype=np.uint8)
        cv2.drawContours(g_layer, contours, -1, color, BOX_THICKNESS, cv2.LINE_AA)

        g_layer[line_mask > 0] = 0

        erase_mask = cv2.dilate(shape_mask, kernel, iterations=1)
        final_layer[erase_mask > 0] = 0
        final_layer = cv2.add(final_layer, g_layer)

    for line in lines:
        line.draw(final_layer)

    for action in drawn_actions:
        if isinstance(action, EraserShape):
            action.draw(final_layer)

    np.copyto(target_layer, final_layer)

def render_glow_to_layer(std_layer):
    if GLOW_ALPHA <= 0: return
    
    line_mask = np.zeros((h, w_orig), dtype=np.uint8)
    lines = [sh for sh in drawn_actions if isinstance(sh, LineShape)]
    for line in lines:
        if len(line.region) < 4: continue
        lx1, ly1, lx2, ly2 = line.region
        cv2.line(line_mask, (lx1, ly1), (lx2, ly2), 255, LINE_THICKNESS + LINE_ERASE_GAP * 2, cv2.LINE_AA)

    group_order = []
    group_boxes = {}
    for action in drawn_actions:
        if isinstance(action, BoxShape):
            gid = action.group_id
            if gid not in group_boxes:
                group_boxes[gid] = []
                group_order.append(gid)
            group_boxes[gid].append(action)

    final_glow = np.zeros((h, w_orig, 4), dtype=np.uint8)
    kernel = np.ones((ERASE_GAP*2+1, ERASE_GAP*2+1), np.uint8)

    for gid in group_order:
        g_actions = group_boxes[gid]
        color = (*g_actions[0].color, GLOW_ALPHA)
        shape_mask = np.zeros((h, w_orig), dtype=np.uint8)
        for act in g_actions:
            fill_val = 255 if act.op == "add" else 0
            act.draw(shape_mask, thickness=-1, color_override=fill_val)

        contours, _ = cv2.findContours(shape_mask, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
        g_layer = np.zeros((h, w_orig, 4), dtype=np.uint8)
        cv2.drawContours(g_layer, contours, -1, color, BOX_THICKNESS, cv2.LINE_AA)

        g_layer[line_mask > 0] = 0

        erase_mask = cv2.dilate(shape_mask, kernel, iterations=1)
        final_glow[erase_mask > 0] = 0
        final_glow = cv2.add(final_glow, g_layer)

    for line in lines:
        if len(line.region) < 4: continue
        lx1, ly1, lx2, ly2 = line.region
        cv2.line(final_glow, (lx1, ly1), (lx2, ly2), (*line.color, GLOW_ALPHA), LINE_THICKNESS, cv2.LINE_AA)

    for action in drawn_actions:
        if isinstance(action, EraserShape):
            action.draw(final_glow)

    std_layer[:] = cv2.add(std_layer, final_glow)

# ─────────────────────────────────────────
# 通信・フラグ用 (スレッド安全なGUI用)
# ─────────────────────────────────────────
pending_gui_action = None
pending_gui_param = None
char_delete_mode = False



def render():
    global cached_canvas, need_full_render
    global curr_scale, pad_x, pad_y
    if img is None: return

    if need_full_render or cached_canvas is None:
        display = np.zeros((h, w_orig + HUD_WIDTH, 3), dtype=np.uint8)
        base_img = img.copy().astype(np.float32)

        mul_layer = np.zeros((h, w_orig, 4), dtype=np.uint8)
        render_boxes_to_layer(mul_layer)
        m_alpha = mul_layer[:, :, 3:4].astype(np.float32) / 255.0
        m_rgb = mul_layer[:, :, :3].astype(np.float32)
        multiplied = (base_img * m_rgb / 255.0)
        base_img = multiplied * m_alpha + base_img * (1.0 - m_alpha)

        std_layer = np.zeros((h, w_orig, 4), dtype=np.uint8)
        render_glow_to_layer(std_layer)
        render_texts_to_layer(std_layer)
        s_alpha = std_layer[:, :, 3:4].astype(np.float32) / 255.0
        s_rgb = std_layer[:, :, :3].astype(np.float32)
        final_img = (s_rgb * s_alpha + base_img * (1.0 - s_alpha)).astype(np.uint8)

        display[:, :w_orig] = final_img
        hud_x = w_orig + 10
        display[:, w_orig:] = (40, 40, 40)
        
        global add_new_y_range, yolo_y_range, export_y_range, trash_icon_y_range, current_palette_regions
        y = HUD_TEXT_MARGIN_Y
        
        logical_num = page_idx - LOGICAL_PAGE_OFFSET + 1
        if 1 <= logical_num <= TOTAL_PAGES: page_text = f"Page: {logical_num:02d} / {TOTAL_PAGES:02d}"
        elif logical_num < 1: page_text = f"Cover (P{page_idx+1})"
        else: page_text = f"Extra (P{logical_num:02d})"
        put_hud_text(display, page_text, hud_x, y, fg=(0, 255, 255)); y+=HUD_TEXT_LINE_SPACING
        
        if mode == "color": m_label = "COLOR MODE"
        elif mode == "numbering": m_label = "NUMBER MODE"
        elif mode == "eraser": m_label = "ERASER MODE"
        elif mode == "delete": m_label = "DELETE MODE"
        elif mode == "manual_text": m_label = "TEXT MODE"
        elif mode == "line": m_label = "LINE MODE"
        else: m_label = str(mode).upper() + " MODE"
        put_hud_text(display, f"Mode : {m_label}", hud_x, y); y+=HUD_TEXT_LINE_SPACING
        put_hud_text(display, f"Shape: {draw_shape.upper()}", hud_x, y); y+=HUD_TEXT_LINE_SPACING
        
        yolo_y_range = (y - 25, y + 5)
        if yolo_running: put_hud_text(display, "YOLO running...", hud_x, y, fg=(80, 200, 255))
        else:
            yolo_status = "ON" if yolo_enabled else "OFF"
            yolo_color = (0, 255, 0) if yolo_enabled else (120, 120, 120)
            put_hud_text(display, f"YOLO: {yolo_status} (Click)", hud_x, y, fg=yolo_color)
        y+=HUD_TEXT_LINE_SPACING
        
        export_y_range = (y - 25, y + 5)
        cv2.rectangle(display, (w_orig+5, y-20), (w_orig+HUD_WIDTH-5, y+5), (60, 60, 60), -1)
        put_hud_text(display, f"[T] EXPORT PANEL", hud_x, y, fg=(255, 200, 100))
        y+=HUD_TEXT_LINE_SPACING
        
        hud_text_img = Image.new("RGBA", (HUD_WIDTH, h), (0, 0, 0, 0))
        d = ImageDraw.Draw(hud_text_img)

        char_header_y = y
        cv2.rectangle(display, (w_orig+5, y-20), (w_orig+HUD_WIDTH-5, y+5), (70, 70, 70), -1)
        d.text((10, y - 18), "キャラクター", font=JP_FONT, fill=(200, 200, 200, 255))
        
        trash_fg = (0, 0, 255, 255) if char_delete_mode else (150, 150, 150, 255)
        trash_text = "[x]削除" if not char_delete_mode else "[DELETE]"
        d.text((HUD_WIDTH - 80, y - 18), trash_text, font=JP_FONT, fill=trash_fg)
        trash_icon_y_range = (y - 20, y + 5)
        y += HUD_TEXT_LINE_SPACING + 5

        if 'current_palette_regions' not in globals(): current_palette_regions = []
        current_palette_regions.clear()
        
        for i in range(len(PALETTE)):
            item_y_range = (y - 25, y + 5)
            current_palette_regions.append((item_y_range, i))

            p_item = PALETTE[i]
            is_gaya = "ガヤ" in p_item["name"]

            # --- 背景色の決定 ---
            bg_color = (60, 60, 60)
            
            # Zモードでまだガヤが選択されていない時だけ、ガヤ全体をうっすら誘導発光
            if mode == "numbering" and is_gaya:
                if "ガヤ" not in current_name:
                    bg_color = (0, 60, 120)  # BGR: 暗めのオレンジ

            if i == current_palette_idx:
                # Zモードでガヤが選択されている場合は、そのガヤだけを強いオレンジに
                if mode == "numbering" and is_gaya:
                    bg_color = (0, 120, 240) # BGR: 強いオレンジ
                else:
                    bg_color = ( p_item["color"][0]//2, p_item["color"][1]//2, p_item["color"][2]//2 )

            cv2.rectangle(display, (w_orig+5, y-25), (w_orig+HUD_WIDTH-5, y+5), bg_color, -1)
            
            # --- 反転表示の決定 ---
            # ★修正: 非ガヤキャラが過去のバグフラグを持っていても強制的にFalseにする
            display_inverted = p_item.get("is_inverted", False) if is_gaya else False

            swatch_color = p_item["color"]
            text_fill = (255, 255, 255, 255)
            if char_delete_mode: text_fill = (150, 150, 150, 255)
            
            if display_inverted:
                cv2.rectangle(display, (hud_x, y-20), (hud_x+30, y), (255, 255, 255), -1)
                cv2.rectangle(display, (hud_x, y-20), (hud_x+30, y), swatch_color, 2)
                text_fill = (swatch_color[2], swatch_color[1], swatch_color[0], 255)
            else:
                cv2.rectangle(display, (hud_x, y-20), (hud_x+30, y), swatch_color, -1)
            
            d.text((40, y - 18), p_item["name"], font=JP_FONT, fill=text_fill, stroke_width=2, stroke_fill=(0,0,0,255))
            
            y += HUD_TEXT_LINE_SPACING + 5
            if y > h - 50: break
            
        hud_text_np = cv2.cvtColor(np.array(hud_text_img), cv2.COLOR_RGBA2BGRA)
        alpha_t = hud_text_np[:, :, 3:4].astype(np.float32) / 255.0
        hud_rgb = hud_text_np[:, :, :3].astype(np.float32)
        disp_hud = display[:, w_orig:].astype(np.float32)
        display[:, w_orig:] = np.clip(disp_hud * (1.0 - alpha_t) + hud_rgb * alpha_t, 0, 255).astype(np.uint8)
            
        if y + 25 <= h:
            cv2.rectangle(display, (w_orig+5, y-20), (w_orig+HUD_WIDTH-5, y+20), (40, 40, 40), -1)
            put_hud_text(display, "+ ADD NEW", hud_x+40, y+5, fg=(150, 255, 150))
            add_new_y_range = (y-20, y+20)
        else:
            add_new_y_range = (-1, -1)

        cached_canvas = display
        need_full_render = False

    display_out = cached_canvas.copy()

    if dragging:
        if not resizing_action and drag_start and drag_end:
            if mode == "line":
                cv2.line(display_out, drag_start, drag_end, current_color, 2, cv2.LINE_AA)
            elif drag_start[0] < w_orig and mode in ["color", "manual_text"]:
                px1, py1 = drag_start
                px2, py2 = drag_end
                x1, y1 = min(px1, px2), min(py1, py2)
                x2, y2 = max(px1, px2), max(py1, py2)
                if (x2 - x1) > 0 and (y2 - y1) > 0 and x2 <= w_orig:
                    if draw_shape == "ellipse":
                        cx, cy = (x1 + x2) // 2, (y1 + y2) // 2
                        axes = ((x2 - x1) // 2, (y2 - y1) // 2)
                        if axes[0] > 0 and axes[1] > 0:
                            cv2.ellipse(display_out, (cx, cy), axes, 0, 0, 360, current_color, 2)
                    else:
                        cv2.rectangle(display_out, (x1, y1), (x2, y2), current_color, 2)

        elif resizing_action:
            r_type = resizing_action.shape_type if not isinstance(resizing_action, dict) else resizing_action.get("type")
            r_region = resizing_action.region if not isinstance(resizing_action, dict) else resizing_action.get("region", [0,0,0,0])
            r_color = getattr(resizing_action, "color", (255, 255, 255)) if not isinstance(resizing_action, dict) else resizing_action.get("color", (255,255,255))
            
            if r_type in ["number", "gaya"] and len(r_region) >= 2:
                nx, ny = r_region[0], r_region[1]
                cv2.rectangle(display_out, (int(nx)-20, int(ny)-20), (int(nx)+20, int(ny)+20), (255,255,255), 2)
            elif r_type == "line" and len(r_region) >= 4:
                cv2.line(display_out, (int(r_region[0]), int(r_region[1])), (int(r_region[2]), int(r_region[3])), r_color, 2, cv2.LINE_AA)
            elif len(r_region) >= 4:
                rx1, ry1, rx2, ry2 = r_region
                rx1, ry1 = int(min(rx1, rx2)), int(min(ry1, ry2))
                rx2, ry2 = int(max(rx1, rx2)), int(max(ry1, ry2))
                if (rx2 - rx1) > 0 and (ry2 - ry1) > 0:
                    shape_val = getattr(resizing_action, "shape", "") if not isinstance(resizing_action, dict) else resizing_action.get("shape")
                    if shape_val == "ellipse":
                        cx, cy = (rx1 + rx2) // 2, (ry1 + ry2) // 2
                        axes = ((rx2 - rx1) // 2, (ry2 - ry1) // 2)
                        if axes[0] > 0 and axes[1] > 0:
                            cv2.ellipse(display_out, (cx, cy), axes, 0, 0, 360, r_color, 2)
                    else:
                        cv2.rectangle(display_out, (rx1, ry1), (rx2, ry2), r_color, 2)

    if mouseX < w_orig:
        ha, part = get_hovered_handle(mouseX, mouseY)
        
        for action in reversed(drawn_actions):
            if action == ha and not dragging:
                region = action.region if not isinstance(action, dict) else action.get("region", [])
                s_type = action.shape_type if not isinstance(action, dict) else action.get("type", "box")
                
                if mode == "eraser":
                    ex, ey = region[0], region[1]
                    r = region[2] if len(region) >= 3 else getattr(action, "radius", 30)
                    cv2.circle(display_out, (int(ex), int(ey)), int(r), (0, 255, 255), 2)
                    if not alt_pressed:
                        c_color = (0, 0, 255) if part == 'center' else (255, 255, 0)
                        cv2.rectangle(display_out, (int(ex)-8, int(ey)-8), (int(ex)+8, int(ey)+8), c_color, -1)
                        e_color = (0, 0, 255) if part == 'edge' else (255, 255, 0)
                        cv2.circle(display_out, (int(ex+r), int(ey)), 8, e_color, -1)
                elif len(region) >= 4 and not alt_pressed:  # Alt押下時はハンドルを出さない
                    if s_type == "line":
                        ex1, ey1, ex2, ey2 = region
                        cv2.line(display_out, (ex1, ey1), (ex2, ey2), (0, 255, 0), 1)
                        cx, cy = (ex1+ex2)//2, (ey1+ey2)//2
                        pts = {'line_p1': (ex1, ey1), 'line_p2': (ex2, ey2), 'center': (cx, cy)}
                        for p_name, (ptx, pty) in pts.items():
                            c = (0, 0, 255) if part == p_name else (255, 255, 0)
                            if not alt_pressed:
                                cv2.rectangle(display_out, (ptx-HANDLE_DRAW_SIZE, pty-HANDLE_DRAW_SIZE), (ptx+HANDLE_DRAW_SIZE, pty+HANDLE_DRAW_SIZE), c, -1)
                    else:
                        x1, y1, x2, y2 = region[0], region[1], region[2], region[3]
                        cv2.rectangle(display_out, (int(min(x1, x2)), int(min(y1, y2))), 
                                      (int(max(x1, x2)), int(max(y1, y2))), (0, 255, 255), 2)
                        
                        handles = [
                            (x1, y1), (x2, y1), (x1, y2), (x2, y2),
                            ((x1+x2)//2, y1), ((x1+x2)//2, y2),
                            (x1, (y1+y2)//2), (x2, (y1+y2)//2)
                        ]
                        if not alt_pressed:
                            for hx, hy in handles:
                                color = (0, 0, 255) if (part and hx == (x1 if 'left' in part else x2 if 'right' in part else (x1+x2)//2) and hy == (y1 if 'top' in part else y2 if 'bottom' in part else (y1+y2)//2)) else (255, 255, 0)
                                cv2.rectangle(display_out, (hx-HANDLE_DRAW_SIZE, hy-HANDLE_DRAW_SIZE), (hx+HANDLE_DRAW_SIZE, hy+HANDLE_DRAW_SIZE), (255, 255, 255), -1)
                                cv2.rectangle(display_out, (hx-HANDLE_DRAW_SIZE, hy-HANDLE_DRAW_SIZE), (hx+HANDLE_DRAW_SIZE, hy+HANDLE_DRAW_SIZE), color, 1)

                        cx, cy = (x1+x2)//2, (y1+y2)//2
                        ccolor = (0, 0, 255) if part == 'center' else (200, 200, 200)
                        cv2.line(display_out, (cx-15, cy), (cx+15, cy), ccolor, 3)
                        cv2.line(display_out, (cx, cy-15), (cx, cy+15), ccolor, 3)
                        
                elif len(region) >= 2 and not alt_pressed:  # Alt押下時はハイライトを出さない
                    tx, ty = region[0], region[1]
                    if s_type in ["number", "gaya"]:
                        cv2.rectangle(display_out, (int(tx)-30, int(ty)-30), (int(tx)+30, int(ty)+30), (0, 255, 255), 2)
                    elif s_type == "text":
                        cv2.rectangle(display_out, (int(tx)-10, int(ty)-10), (int(tx)+100, int(ty)+40), (0, 255, 255), 2)
                break
        else:
            if mode in ["color", "manual_text", "line"] and not dragging:
                hb = hovered_yolo_box(mouseX, mouseY)
                if hb and yolo_enabled and not alt_pressed:
                    x1, y1, x2, y2 = hb
                    if draw_shape == "ellipse":
                        cx_y, cy_y = (x1 + x2) // 2, (y1 + y2) // 2
                        axes_y = ((x2 - x1) // 2, (y2 - y1) // 2)
                        if axes_y[0] > 0 and axes_y[1] > 0:
                            cv2.ellipse(display_out, (cx_y, cy_y), axes_y, 0, 0, 360, current_color, 2)
                    else:
                        cv2.rectangle(display_out, (x1, y1), (x2, y2), current_color, 2)
            elif mode == "numbering":
                cv2.line(display_out, (mouseX-10, mouseY), (mouseX+10, mouseY), (200,200,200), 1)
                cv2.line(display_out, (mouseX, mouseY-10), (mouseX, mouseY+10), (200,200,200), 1)
            elif mode == "eraser":
                if dragging and drag_start:
                    px, py = drag_start
                    r = int(math.hypot(mouseX - px, mouseY - py))
                    if r < 5: r = ERASER_RADIUS
                    cv2.circle(display_out, (px, py), r, (0, 0, 255, 120), 2)
                else:
                    cv2.circle(display_out, (mouseX, mouseY), ERASER_RADIUS, (255, 255, 255), 2)
            elif mode == "delete":
                target_action = get_deletable_action(mouseX, mouseY)
                if target_action:
                    t = target_action.shape_type if not isinstance(target_action, dict) else target_action.get("type", "")
                    region = target_action.region if not isinstance(target_action, dict) else target_action.get("region", [])
                    if t in ["box", "text", "manual_text"] and len(region) >= 4:
                        x1, y1, x2, y2 = region[0], region[1], region[2], region[3]
                        cv2.rectangle(display_out, (min(x1, x2), min(y1, y2)), (max(x1, x2), max(y1, y2)), (0, 0, 255), 3)
                    elif t == "line" and len(region) >= 4:
                        cv2.line(display_out, (region[0], region[1]), (region[2], region[3]), (0, 0, 255), LINE_THICKNESS + 4)
                    elif t in ["number", "gaya"] and len(region) >= 2:
                        cv2.circle(display_out, (region[0], region[1]), NUMBER_SIZE//2 + 5, (0, 0, 255), 3)
                    elif t == "eraser" and len(region) >= 2:
                        r = region[2] if len(region) >= 3 else getattr(target_action, "radius", ERASER_RADIUS) if not isinstance(target_action, dict) else ERASER_RADIUS
                        cv2.circle(display_out, (region[0], region[1]), r, (0, 0, 255), 3)

    if show_help:
        overlay = get_help_overlay(display_out.shape[1], display_out.shape[0])
        alpha = overlay[:, :, 3] / 255.0
        for c in range(3):
            display_out[:, :, c] = (alpha * overlay[:, :, c] + (1 - alpha) * display_out[:, :, c]).astype(np.uint8)

    cv2.imshow(WIN_NAME, display_out)

# ─────────────────────────────────────────
# 8. マウスイベント・HUDクリック判定・補助関数
# ─────────────────────────────────────────
def recalculate_numbers():
    global number_counter
    num = 1
    for action in drawn_actions:
        if isinstance(action, NumberShape):
            action.num = num
            num += 1
    number_counter = num

def is_char_name_labeled(char_name):
    for a in drawn_actions:
        if isinstance(a, TextShape) and getattr(a, "char_name", "") == char_name:
            return True
    for p in range(TOTAL_PAGES):
        state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state = json.load(f)
                    for a in state.get("drawn_actions", []):
                        if a.get("type") == "text" and a.get("char_name") == char_name:
                            return True
            except: pass
    return False

def get_used_characters():
    used = set()
    for p in range(TOTAL_PAGES):
        state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state = json.load(f)
                    for act in state.get("drawn_actions", []):
                        if act.get("char_name"): used.add(act["char_name"])
            except: pass
    for act in drawn_actions:
        cname = getattr(act, "char_name", None)
        if cname: used.add(cname)
    return used

def open_export_dialog():
    dialog = tk.Toplevel(_root)
    dialog.title("一括出力設定")
    dialog.geometry("500x600")
    dialog.attributes('-topmost', True)

    style = ttk.Style(dialog)
    style.configure("TButton", padding=6)
    
    var_pdf = tk.BooleanVar(dialog, value=True)
    var_csv = tk.BooleanVar(dialog, value=True)
    var_psd_layers = tk.BooleanVar(dialog, value=False)
    var_extract = tk.BooleanVar(dialog, value=False)
    char_vars = {}

    main_frame = ttk.Frame(dialog, padding="20 20 20 20")
    main_frame.pack(fill=tk.BOTH, expand=True)

    ttk.Label(main_frame, text="【基本出力項目】", font=("", 12, "bold")).pack(anchor=tk.W, pady=(0, 10))
    ttk.Checkbutton(main_frame, text="完成版PDFを出力", variable=var_pdf).pack(anchor=tk.W, pady=2)
    ttk.Checkbutton(main_frame, text="登場一覧表(CSV)を出力", variable=var_csv).pack(anchor=tk.W, pady=2)
    ttk.Checkbutton(main_frame, text="レイヤー別PSDを出力 (GIMP等で編集可能)", variable=var_psd_layers).pack(anchor=tk.W, pady=2)
    
    ttk.Separator(main_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=15)
    ttk.Checkbutton(main_frame, text="キャラ別抜き台本(PDF)を出力 [未実装]", variable=var_extract, state=tk.DISABLED).pack(anchor=tk.W, pady=(0, 5))
    
    char_frame_container = ttk.LabelFrame(main_frame, text="抜き出し対象キャラクター", padding="10 10 10 10")
    char_frame_container.pack(fill=tk.BOTH, expand=True, padx=20)
    
    btn_frame = ttk.Frame(char_frame_container)
    btn_frame.pack(fill=tk.X, pady=(0, 10))
    
    def set_all_chars(state):
        for v in char_vars.values(): v.set(state)
        
    ttk.Button(btn_frame, text="全選択", command=lambda: set_all_chars(True)).pack(side=tk.LEFT, padx=(0, 5))
    ttk.Button(btn_frame, text="全解除", command=lambda: set_all_chars(False)).pack(side=tk.LEFT)

    char_grid = ttk.Frame(char_frame_container)
    char_grid.pack(fill=tk.BOTH, expand=True)
    
    used_chars = get_used_characters()
    max_rows = 5
    
    for i, p in enumerate(PALETTE):
        name = p["name"]
        is_used = name in used_chars
        c_var = tk.BooleanVar(dialog, value=is_used)
        char_vars[name] = c_var
        
        fg_color = "black" if is_used else "gray"
        cb = tk.Checkbutton(char_grid, text=name, variable=c_var, fg=fg_color)
        
        row = i % max_rows
        col = i // max_rows
        cb.grid(row=row, column=col, sticky=tk.W, padx=5, pady=2)

    exec_frame = ttk.Frame(main_frame)
    exec_frame.pack(fill=tk.X, pady=(20, 0))
    
    progress = ttk.Progressbar(exec_frame, mode='determinate')
    progress.pack(fill=tk.X, pady=(0, 10))
    
    status_label = ttk.Label(exec_frame, text="待機中...")
    status_label.pack(anchor=tk.W, pady=(0, 10))

    def run_export():
        dialog.attributes('-topmost', False)
        os.makedirs(EXPORT_DIR, exist_ok=True)
        progress["value"] = 0
        total_tasks = int(var_pdf.get()) + int(var_csv.get()) + int(var_psd_layers.get())
        if total_tasks == 0:
            messagebox.showinfo("確認", "出力項目が選択されていません。")
            return
            
        progress["maximum"] = total_tasks
        current_task = 0
        
        try:
            if var_csv.get():
                status_label.config(text="登場一覧表(CSV)を出力中...")
                dialog.update()
                export_character_pages_csv()
                current_task += 1
                progress["value"] = current_task
                
            if var_pdf.get():
                status_label.config(text="完成版PDFを出力中... (時間がかかります)")
                dialog.update()
                export_to_pdf()
                current_task += 1
                progress["value"] = current_task
                
            if var_psd_layers.get():
                status_label.config(text="レイヤー別PSDを出力中...")
                dialog.update()
                export_to_psd_layers()
                current_task += 1
                progress["value"] = current_task

            status_label.config(text="出力完了！")
            dialog.update()
            dialog.after(800, dialog.destroy)
        except Exception as e:
            messagebox.showerror("エラー", f"出力中にエラーが発生しました:\n{e}")
            dialog.destroy()

    ttk.Button(exec_frame, text="チェックした項目を出力開始", command=run_export, style="TButton").pack(fill=tk.X)
    dialog.grab_set()
    dialog.wait_window(dialog)

def handle_hud_click(mx, my, flags):
    global current_palette_idx, current_color, current_name, yolo_enabled, char_delete_mode
    global pending_gui_action, pending_gui_param
    hud_x = w_orig + 10
    
    if 'yolo_y_range' in globals() and yolo_y_range[0] <= my <= yolo_y_range[1]:
        yolo_enabled = not yolo_enabled
        request_render(); return

    if 'export_y_range' in globals() and export_y_range[0] <= my <= export_y_range[1]:
        open_export_dialog(); request_render(); return

    if 'current_palette_regions' in globals():
        if 'trash_icon_y_range' in globals() and trash_icon_y_range[0] <= my <= trash_icon_y_range[1]:
            char_delete_mode = not char_delete_mode
            if len(PALETTE) <= 1: char_delete_mode = False
            request_render(); return

        for y_range, i in current_palette_regions:
            if y_range[0] <= my <= y_range[1]:
                if char_delete_mode:
                    delete_character(i)
                else:
                    p_item = PALETTE[i]
                    is_gaya = "ガヤ" in p_item["name"]
                    
                    if mode == "numbering":
                        if not is_gaya:
                            current_palette_idx = i
                            current_color = p_item["color"]
                            current_name = p_item["name"]
                            request_render()
                            return

                    # ★修正: 反転フラグのトグルはガヤのみ許可
                    if (flags & cv2.EVENT_FLAG_SHIFTKEY) and is_gaya:
                        PALETTE[i]["is_inverted"] = not PALETTE[i].get("is_inverted", False)
                        save_project_palette(PALETTE, os.path.join(WORK_DIR, "project_characters.csv"))
                    
                    if mx < hud_x + 35 and not (flags & cv2.EVENT_FLAG_SHIFTKEY):
                        pending_gui_action = "color"
                        pending_gui_param = i
                    else:
                        current_palette_idx = i
                        current_color = p_item["color"]
                        current_name = p_item["name"]
                    request_render()
                return

    if 'add_new_y_range' in globals() and add_new_y_range[0] <= my <= add_new_y_range[1]:
        pending_gui_action = "add"
        char_delete_mode = False
        return

def run_color_chooser(idx):
    global current_color
    b, g, r = PALETTE[idx]["color"]
    init_hex = f"#{r:02x}{g:02x}{b:02x}"
    color_code = colorchooser.askcolor(title=f"{PALETTE[idx]['name']} の色を選択", initialcolor=init_hex, parent=_root)
    if color_code[0] is not None:
        r_new, g_new, b_new = map(int, color_code[0])
        PALETTE[idx]["color"] = (b_new, g_new, r_new)
        if idx == current_palette_idx: current_color = PALETTE[idx]["color"]
        save_project_palette(PALETTE, os.path.join(WORK_DIR, "project_characters.csv"))
        request_render()

def run_add_char_dialog():
    dlg = tk.Toplevel(_root); dlg.title("キャラ一括追加"); dlg.geometry("400x450"); dlg.attributes('-topmost', True)
    tk.Label(dlg, text="キャラ名のみ、または名前[TAB]色コードの形式で入力:").pack(pady=5)
    txt = tk.Text(dlg, width=45, height=15); txt.pack(padx=10, pady=5)
    
    def on_add():
        added = False
        for line in txt.get("1.0", tk.END).strip().split('\n'):
            line = line.strip()
            if not line: continue
            parts = line.split('\t')
            name = parts[0].strip()
            bgr = (255, 255, 255)
            if len(parts) > 1:
                h_val = parts[1].strip().lstrip('#')
                if len(h_val) == 6:
                    rgb = tuple(int(h_val[j:j+2], 16) for j in (0, 2, 4))
                    bgr = (rgb[2], rgb[1], rgb[0])
            PALETTE.append({"name": name, "color": bgr, "is_inverted": False})
            added = True
        if added:
            save_project_palette(PALETTE, os.path.join(WORK_DIR, "project_characters.csv"))
            request_render()
        dlg.destroy()
    tk.Button(dlg, text="一括追加", command=on_add, width=20).pack(pady=10)
    dlg.grab_set(); dlg.wait_window(dlg)

def delete_character(idx):
    global current_palette_idx, current_color, current_name, char_delete_mode
    if len(PALETTE) <= 1:
        print("⚠ エラー: 最後のキャラクターは削除できません。")
        char_delete_mode = False
        return
    del PALETTE[idx]
    if current_palette_idx >= idx:
        current_palette_idx = max(0, current_palette_idx - 1)
    if current_palette_idx < len(PALETTE):
        current_color = PALETTE[current_palette_idx]["color"]
        current_name = PALETTE[current_palette_idx]["name"]
    save_project_palette(PALETTE, os.path.join(WORK_DIR, "project_characters.csv"))
    if len(PALETTE) <= 1:
        char_delete_mode = False
    request_render()

def mouse_callback(event, x, y, flags, param):
    global mouseX, mouseY, dragging, drag_start, drag_end, number_counter, redo_stack, page_idx
    global resizing_action, resizing_part, drag_start_region, shift_pressed

    ix = max(0, min(w_orig + HUD_WIDTH - 1, x))
    iy = max(0, min(h - 1, y))
    mouseX, mouseY = ix, iy
    # ★追加: リアルタイムなキー検知（マウスイベント発生時のみ更新）
    shift_pressed = bool(flags & cv2.EVENT_FLAG_SHIFTKEY)
    global alt_pressed
    alt_pressed = bool(flags & cv2.EVENT_FLAG_ALTKEY)

    if event == cv2.EVENT_LBUTTONDOWN and ix >= w_orig:
        handle_hud_click(ix, iy, flags)
        return

    if ix >= w_orig and dragging:
        ix = w_orig - 1

    if event == cv2.EVENT_LBUTTONDOWN and ix < w_orig:
        if mode == "delete":
            target_action = get_deletable_action(ix, iy)
            if target_action:
                save_undo_state()
                drawn_actions.remove(target_action)
                if isinstance(target_action, NumberShape):
                    recalculate_numbers()
                recalculate_gaya_numbers()
                request_render()
                render()
            return
            
        if mode == "eraser":
            dragging = True
            drag_start = (ix, iy)
            drag_end = (ix, iy)
            return

        dragging   = True
        drag_start = (ix, iy)
        drag_end   = (ix, iy)

        if mode in ["color", "manual_text", "line", "numbering"]:
            ha, part = get_hovered_handle(ix, iy, flags)
            if ha:
                save_undo_state()
                resizing_action = ha
                resizing_part   = part
                drag_start_region = list(ha.region) if not isinstance(ha, dict) else list(ha.get("region", []))
            else:
                resizing_action = None
        
        if mode == "manual_text" and not resizing_action:
            root = tk.Tk()
            root.withdraw()
            txt = simpledialog.askstring("自由テキスト", "表示するテキストを入力してください:")
            root.destroy()
            if txt:
                save_undo_state()
                tw, th = get_manual_text_size(txt, MANUAL_TEXT_SIZE)
                tx1, ty1 = ix, iy
                tx2, ty2 = ix + tw, iy + th
                drawn_actions.append(ManualTextShape([tx1, ty1, tx2, ty2], txt, MANUAL_TEXT_SIZE, MANUAL_TEXT_COLOR))
                request_render()
                render()
            dragging = False
            return

    elif event == cv2.EVENT_MOUSEMOVE:
        if dragging and ix < w_orig:
            drag_end = (ix, iy)
            if mode == "eraser":
                render()
            elif resizing_action and drag_start_region:
                px, py = drag_start
                dx = ix - px
                dy = iy - py
                
                if isinstance(resizing_action, (NumberShape, GayaShape)):
                    if resizing_part in ["move_number", "center"] and len(drag_start_region) >= 2:
                        dx_n = ix - drag_start[0]
                        dy_n = iy - drag_start[1]
                        resizing_action.region = [drag_start_region[0] + dx_n, drag_start_region[1] + dy_n]
                elif isinstance(resizing_action, EraserShape):
                    if resizing_part == 'center':
                        resizing_action.region[0] = drag_start_region[0] + dx
                        resizing_action.region[1] = drag_start_region[1] + dy
                    elif resizing_part == 'edge':
                        new_r = int(math.hypot(ix - drag_start_region[0], iy - drag_start_region[1]))
                        if new_r < 5: new_r = 5
                        if len(resizing_action.region) >= 3:
                            resizing_action.region[2] = new_r
                        else:
                            resizing_action.region.append(new_r)
                else:
                    if len(drag_start_region) >= 4:
                        x1, y1, x2, y2 = drag_start_region
                        if isinstance(resizing_action, LineShape):
                            new_x1, new_y1, new_x2, new_y2 = x1, y1, x2, y2
                            if resizing_part == 'center':
                                new_x1 += dx; new_y1 += dy
                                new_x2 += dx; new_y2 += dy
                            elif resizing_part == 'line_p1':
                                new_x1 += dx; new_y1 += dy
                            elif resizing_part == 'line_p2':
                                new_x2 += dx; new_y2 += dy
                            resizing_action.region = [new_x1, new_y1, new_x2, new_y2]
                        else:
                            if resizing_part == 'center':
                                box_w = x2 - x1; box_h = y2 - y1
                                new_x1 = max(0, x1 + dx); new_y1 = max(0, y1 + dy)
                                new_x2 = min(w_orig, x2 + dx); new_y2 = min(h, y2 + dy)
                                if new_x1 == 0: new_x2 = box_w
                                if new_y1 == 0: new_y2 = box_h
                                if new_x2 == w_orig: new_x1 = w_orig - box_w
                                if new_y2 == h: new_y1 = h - box_h
                                resizing_action.region = [new_x1, new_y1, new_x2, new_y2]
                            else:
                                new_x1, new_y1, new_x2, new_y2 = x1, y1, x2, y2
                                if 'top' in resizing_part:    new_y1 = min(new_y2 - 4, y1 + dy)
                                if 'bottom' in resizing_part: new_y2 = max(new_y1 + 4, y2 + dy)
                                if 'left' in resizing_part:   new_x1 = min(new_x2 - 4, x1 + dx)
                                if 'right' in resizing_part:  new_x2 = max(new_x1 + 4, x2 + dx)
                                resizing_action.region = [new_x1, new_y1, new_x2, new_y2]
            render()
        elif not dragging:
            render()

    elif event == cv2.EVENT_LBUTTONUP:
        if not dragging:
            if ix < w_orig: render()
            return

        drag_end = (ix, iy)
        dragging = False

        if mode == "eraser":
            px, py = drag_start
            r = int(math.hypot(ix - px, iy - py))
            if r < 5: r = ERASER_RADIUS
            save_undo_state()
            drawn_actions.append(EraserShape([px, py, r]))
            request_render()
            render()
            return

        if resizing_action:
            rx1, ry1, rx2, ry2 = resizing_action.region
            if not isinstance(resizing_action, LineShape):
                resizing_action.region = [min(rx1, rx2), min(ry1, ry2), max(rx1, rx2), max(ry1, ry2)]
            
            if isinstance(resizing_action, ManualTextShape):
                new_h = abs(ry2 - ry1)
                resizing_action.font_size = max(5, int(new_h * 0.85))

            resizing_action = None
            request_render()
            render()
            return

        px1, py1 = drag_start
        px2, py2 = drag_end
        x1, y1 = min(px1, px2), min(py1, py2)
        x2, y2 = max(px1, px2), max(py1, py2)
        is_click = (abs(px2 - px1) < 8 and abs(py2 - py1) < 8)

        if mode == "color" and ix < w_orig:
            use_shift = bool(flags & cv2.EVENT_FLAG_SHIFTKEY)
            use_ctrl  = bool(flags & cv2.EVENT_FLAG_CTRLKEY)
            op = "sub" if use_ctrl else "add"

            if is_click:
                ha, _ = get_hovered_handle(ix, iy, flags)
                if not ha:
                    hb = hovered_yolo_box(ix, iy)
                    if hb and yolo_enabled:
                        box_region = list(hb)
                        target_group_id = get_target_group_id(box_region, use_shift, use_ctrl, current_name)
                        save_undo_state()
                        
                        new_box = BoxShape(box_region, current_color, draw_shape, op, target_group_id)
                        new_box.char_name = current_name
                        drawn_actions.append(new_box)
                        
                        if op == "add":
                            check_and_add_text_action(box_region, current_name, current_color)
                        request_render()
            else:
                if (x2 - x1) >= 4 and (y2 - y1) >= 4:
                    box_region = [x1, y1, x2, y2]
                    target_group_id = get_target_group_id(box_region, use_shift, use_ctrl, current_name)
                    save_undo_state()
                    
                    new_box = BoxShape(box_region, current_color, draw_shape, op, target_group_id)
                    new_box.char_name = current_name
                    drawn_actions.append(new_box)
                    
                    if op == "add":
                        check_and_add_text_action(box_region, current_name, current_color)
                    request_render()

        elif mode == "numbering" and ix < w_orig:
            if is_click:
                save_undo_state()
                
                if "ガヤ" in current_name:
                    # a) 現在のページ上の古い名前ラベルをクリーンアップ
                    for act in list(drawn_actions):
                        if isinstance(act, TextShape) and getattr(act, "char_name", "") == current_name:
                            drawn_actions.remove(act)
                            
                    # ★追加: 他の全ページ（セーブデータ）からも古い名前ラベルを消し去る
                    for p in range(len(doc)):
                        if p == page_idx: continue
                        state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
                        if os.path.exists(state_file):
                            try:
                                with open(state_file, "r", encoding="utf-8") as f:
                                    p_state = json.load(f)
                                
                                # TextShapeかつ名前が一致するものを除外してリストを再構築
                                original_len = len(p_state.get("drawn_actions", []))
                                p_state["drawn_actions"] = [
                                    a for a in p_state.get("drawn_actions", []) 
                                    if not (a.get("type") == "text" and a.get("char_name") == current_name)
                                ]
                                
                                # 変更があった場合のみ上書き保存
                                if len(p_state["drawn_actions"]) != original_len:
                                    with open(state_file, "w", encoding="utf-8") as f:
                                        json.dump(p_state, f, ensure_ascii=False, indent=2)
                            except: pass
                    
                    # b) 次の番号を取得
                    next_num = get_next_gaya_number(current_name)
                    
                    # c) GayaShape を追加（現在の反転状態を取得して適用）
                    p_item = PALETTE[current_palette_idx] if current_palette_idx < len(PALETTE) else {}
                    new_gaya = GayaShape([ix, iy], current_name, next_num, current_color, p_item.get("is_inverted", False))
                    drawn_actions.append(new_gaya)
                else:
                    # 通常のセリフ番号
                    drawn_actions.append(NumberShape([ix, iy], number_counter))
                    number_counter += 1
                request_render()

        elif mode == "line" and ix < w_orig:
            if not is_click:
                save_undo_state()
                new_line = LineShape([px1, py1, px2, py2], current_color)
                new_line.char_name = current_name
                drawn_actions.append(new_line)
                
                lx1, ly1 = min(px1, px2), min(py1, py2)
                lx2, ly2 = max(px1, px2), max(py1, py2)
                check_and_add_text_action([lx1, ly1, lx2, ly2], current_name, current_color)
                request_render()

        render()

    elif event == cv2.EVENT_MOUSEWHEEL:
        if flags > 0:
            if page_idx > 0: trigger_page_change(page_idx - 1)
        else:
            if page_idx < len(doc) - 1: trigger_page_change(page_idx + 1)

# ─────────────────────────────────────────
# 9. データ保存処理 & エクスポート
# ─────────────────────────────────────────
def _make_serializable(obj):
    if hasattr(obj, "to_dict"): return _make_serializable(obj.to_dict())
    if isinstance(obj, (np.integer, int)): return int(obj)
    elif isinstance(obj, (np.floating, float)): return float(obj)
    elif isinstance(obj, np.ndarray): return obj.tolist()
    elif isinstance(obj, tuple): return list(obj)
    elif isinstance(obj, list): return [_make_serializable(v) for v in obj]
    elif isinstance(obj, dict): return {k: _make_serializable(v) for k, v in obj.items()}
    return obj

def save_current_page():
    if img is None: return

    used_chars = set(getattr(a, "char_name", None) for a in drawn_actions if getattr(a, "char_name", None))
    page_records[page_idx] = used_chars

    folder_name = f"Page {page_idx + 1}"
    out_dir = os.path.join(OUTPUT_BASE, folder_name)
    os.makedirs(out_dir, exist_ok=True)

    state = {
        "number_counter": number_counter,
        "drawn_actions": _make_serializable(drawn_actions)
    }
    state_file = os.path.join(out_dir, "state.json")
    try:
        with open(state_file, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"JSON保存エラー: {e}")

    print(f"✅ 状態保存完了: {folder_name} (キャラ: {', '.join(used_chars)})")


def compress_page_ranges(page_labels):
    nums = []
    others = []
    for lbl in page_labels:
        if lbl.startswith("P") and lbl[1:].isdigit():
            nums.append(int(lbl[1:]))
        else:
            others.append(lbl)
    
    nums = sorted(list(set(nums)))
    ranges = []
    if nums:
        start = nums[0]
        prev = nums[0]
        for n in nums[1:]:
            if n == prev + 1:
                prev = n
            else:
                if start == prev: ranges.append(f"P{start:02d}")
                else: ranges.append(f"P{start:02d}-{prev:02d}")
                start = n
                prev = n
        if start == prev: ranges.append(f"P{start:02d}")
        else: ranges.append(f"P{start:02d}-{prev:02d}")
        
    return ", ".join(others + ranges)

def export_character_pages_csv():
    char_to_pages = {}
    char_to_count = {}

    for p in range(len(doc)):
        logical_num = p - LOGICAL_PAGE_OFFSET + 1
        if logical_num < 1 or logical_num > TOTAL_PAGES:
            continue
            
        state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state = json.load(f)
                
                page_chars = set()
                processed_groups = set()

                for act in state.get("drawn_actions", []):
                    cname = act.get("char_name")
                    if not cname: continue
                    
                    page_chars.add(cname)
                    t = act.get("type")
                    
                    if t == "box":
                        gid = act.get("group_id", 0)
                        if gid not in processed_groups:
                            char_to_count[cname] = char_to_count.get(cname, 0) + 1
                            processed_groups.add(gid)
                    elif t == "line":
                        char_to_count[cname] = char_to_count.get(cname, 0) + 1
                        
            except Exception:
                pass
            
            for cname in page_chars:
                if cname not in char_to_pages:
                    char_to_pages[cname] = []
                page_label = f"P{logical_num:02d}"
                char_to_pages[cname].append(page_label)
            
    out_csv = os.path.join(EXPORT_DIR, f"_{clean_base_name}_character_pages.csv")
    try:
        with open(out_csv, "w", encoding="utf-8-sig", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["キャラ名", "セリフ数", "登場ページ"])
            
            sorted_chars = sorted(char_to_pages.keys(), key=lambda x: char_to_count.get(x, 0), reverse=True)
            
            for char_name in sorted_chars:
                compressed_pages = compress_page_ranges(char_to_pages[char_name])
                count = char_to_count.get(char_name, 0)
                writer.writerow([char_name, count, compressed_pages])
                
        print(f"📝 キャラ別登場一覧CSVを出力しました: {out_csv}")
    except Exception as e:
        print(f"キャラ別登場一覧出力エラー: {e}")

def export_to_pdf():
    print("🔄 完成版PDFを出力中...")
    import io
    global h, w_orig, drawn_actions, page_idx
    
    new_name = f"{clean_base_name}(丸付け後).pdf"
    output_pdf_path = os.path.join(EXPORT_DIR, new_name)
    out_pdf = fitz.open()
    
    _saved_h = h
    _saved_w = w_orig
    _saved_actions = drawn_actions
    _saved_page_idx = page_idx

    start_idx = LOGICAL_PAGE_OFFSET
    end_idx = min(LOGICAL_PAGE_OFFSET + TOTAL_PAGES, len(doc))
    for i in range(start_idx, end_idx):
        page_idx = i
        page = doc[i]
        zoom = 1400 / page.rect.width
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        base_img = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, 3)
        base_float = base_img.astype(np.float32)
        
        folder_name = f"Page {i + 1}"
        page_dir = os.path.join(OUTPUT_BASE, folder_name)
        state_file = os.path.join(page_dir, "state.json")

        ph, pw = base_img.shape[:2]
        h = ph
        w_orig = pw

        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state_data = json.load(f)
                page_actions = state_data.get("drawn_actions", [])
                drawn_actions = []
                for act in page_actions:
                    obj = Shape.from_dict(act)
                    if obj: drawn_actions.append(obj)
            except Exception as e:
                print(f"  [WARN] state.json 読み込み失敗 Page {i+1}: {e}")
                drawn_actions = []
        else:
            drawn_actions = []

        mul_layer = np.zeros((ph, pw, 4), dtype=np.uint8)
        render_boxes_to_layer(mul_layer)
        m_alpha = mul_layer[:, :, 3:4].astype(np.float32) / 255.0
        m_rgb   = mul_layer[:, :, :3].astype(np.float32)
        multiplied = (base_float * m_rgb / 255.0)
        final_float = multiplied * m_alpha + base_float * (1.0 - m_alpha)

        std_layer = np.zeros((ph, pw, 4), dtype=np.uint8)
        render_glow_to_layer(std_layer)
        render_texts_to_layer(std_layer)
        s_alpha = std_layer[:, :, 3:4].astype(np.float32) / 255.0
        s_rgb   = std_layer[:, :, :3].astype(np.float32)
        final_float = s_rgb * s_alpha + final_float * (1.0 - s_alpha)
        
        final_img_uint8 = final_float.astype(np.uint8)
        final_rgb = cv2.cvtColor(final_img_uint8, cv2.COLOR_BGR2RGB)
        pil_img = Image.fromarray(final_rgb).convert("RGB")
        
        img_byte_arr = io.BytesIO()
        pil_img.save(img_byte_arr, format='JPEG', quality=85)
        img_bytes = img_byte_arr.getvalue()

        rect = fitz.Rect(0, 0, page.rect.width, page.rect.height)
        new_page = out_pdf.new_page(width=page.rect.width, height=page.rect.height)
        new_page.insert_image(rect, stream=img_bytes)

        if (i + 1) % 10 == 0:
            print(f"  ... {i+1} / {len(doc)} ページ処理済み")

    h = _saved_h
    w_orig = _saved_w
    drawn_actions = _saved_actions
    page_idx = _saved_page_idx

    try:
        out_pdf.save(output_pdf_path)
        out_pdf.close()
        print(f"✅ PDF出力完了: {output_pdf_path}")
    except Exception as e:
        print(f"PDF保存エラー: {e}")

def export_to_psd_layers():
    if PSDImage is None:
        print("[ERROR] psd-tools がインストールされていないためPSD出力できません。")
        return

    psd_dir = os.path.join(EXPORT_DIR, f"{clean_base_name}_PSD")
    os.makedirs(psd_dir, exist_ok=True)
    # 絵文字を削除し、安全な出力文字列に変更
    print(f"レイヤー別PSDを出力中: {psd_dir}")

    global h, w_orig, drawn_actions, page_idx
    _saved_h = h
    _saved_w = w_orig
    _saved_actions = drawn_actions
    _saved_page_idx = page_idx

    start_idx = LOGICAL_PAGE_OFFSET
    end_idx = min(LOGICAL_PAGE_OFFSET + TOTAL_PAGES, len(doc))

    for i in range(start_idx, end_idx):
        page_idx = i
        page = doc[i]
        
        # 1. ベース画像の取得
        zoom = 1400 / page.rect.width
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        base_np = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, 3) # RGB
        ph, pw = base_np.shape[:2]
        h, w_orig = ph, pw

        # 2. 状態の復元
        folder_name = f"Page {i + 1}"
        state_file = os.path.join(OUTPUT_BASE, folder_name, "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state_data = json.load(f)
                drawn_actions = [Shape.from_dict(act) for act in state_data.get("drawn_actions", []) if Shape.from_dict(act)]
            except:
                drawn_actions = []
        else:
            drawn_actions = []

        # 3. レイヤー画像の生成
        # a) 背景レイヤー (通常) - Pillow Image
        base_pil = Image.fromarray(base_np).convert("RGB")

        # b) 丸付けレイヤー (乗算)
        mul_layer_np = np.zeros((ph, pw, 4), dtype=np.uint8)
        render_boxes_to_layer(mul_layer_np)
        mul_pil = Image.fromarray(cv2.cvtColor(mul_layer_np, cv2.COLOR_BGRA2RGBA))

        # c) テキスト・発光レイヤー (通常)
        std_layer_np = np.zeros((ph, pw, 4), dtype=np.uint8)
        render_glow_to_layer(std_layer_np)
        render_texts_to_layer(std_layer_np)
        std_pil = Image.fromarray(cv2.cvtColor(std_layer_np, cv2.COLOR_BGRA2RGBA))

        # 4. PSDの組み立て
        psd = PSDImage.new(mode='RGB', size=(pw, ph), depth=8)
        
        # ★修正: レイヤー名を英語に変更（エンコードエラー回避）
        # 背景
        psd.create_pixel_layer(base_pil, name="Background", top=0, left=0)
        
        # 丸付け (乗算)
        l_mul = psd.create_pixel_layer(mul_pil, name="Multiply_Frames", top=0, left=0)
        l_mul.blend_mode = BlendMode.MULTIPLY
        
        # テキスト・発光 (通常)
        psd.create_pixel_layer(std_pil, name="Normal_Text", top=0, left=0)

        # 5. 保存
        logical_num = i - LOGICAL_PAGE_OFFSET + 1
        psd_path = os.path.join(psd_dir, f"Page_{logical_num:03d}.psd")
        psd.save(psd_path)

        if (i + 1) % 10 == 0:
            print(f"  ... PSD出力中: {i+1} ページ経過")

    # 6. 後処理・復元
    h = _saved_h
    w_orig = _saved_w
    drawn_actions = _saved_actions
    page_idx = _saved_page_idx
    print(f"PSD出力完了: {psd_dir}")

# ─────────────────────────────────────────
# 10. ウィンドウ表示＆メインループ
# ─────────────────────────────────────────
cv2.namedWindow(WIN_NAME, cv2.WINDOW_NORMAL)
cv2.setMouseCallback(WIN_NAME, mouse_callback)

def scan_all_pages_for_first_appearances():
    global global_char_first_page
    global_char_first_page.clear()
    for p in range(TOTAL_PAGES):
        state_file = os.path.join(OUTPUT_BASE, f"Page {p + 1}", "state.json")
        if os.path.exists(state_file):
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state = json.load(f)
                for act in state.get("drawn_actions", []):
                    cname = act.get("char_name")
                    if cname and cname not in global_char_first_page:
                        global_char_first_page[cname] = p
            except Exception:
                pass

scan_all_pages_for_first_appearances()
load_page(0)

# 初回起動時のウィンドウサイズ設定
init_w = w_orig + HUD_WIDTH
init_h = h
if init_h > DISPLAY_MAX_H:
    s = DISPLAY_MAX_H / init_h
    init_w = int(init_w * s)
    init_h = int(init_h * s)
try: cv2.resizeWindow(WIN_NAME, init_w, init_h)
except: pass

print("─"*40)
for line in get_help_lines():
    print(line)
print("─"*40)

while True:
    if cv2.getWindowProperty(WIN_NAME, cv2.WND_PROP_VISIBLE) < 1:
        save_current_page()
        break

    if pending_page_load and (time.time() - last_scroll_time > 0.4):
        load_page(page_idx)
        pending_page_load = False
        request_render()

    render()
    key = cv2.waitKey(30) & 0xFF

    if pending_gui_action == "color":
        run_color_chooser(pending_gui_param)
        pending_gui_action = None
    elif pending_gui_action == "add":
        run_add_char_dialog()
        pending_gui_action = None
        
    if char_delete_mode and len(PALETTE) <= 1:
        char_delete_mode = False
        request_render()

    if key in (KEY_PAGE_NEXT, 13):
        if page_idx < len(doc) - 1:
            trigger_page_change(page_idx + 1)
        else:
            print("PDFの物理的な最終ページです。")
    elif key == KEY_PAGE_PREV:
        if page_idx > 0:
            trigger_page_change(page_idx - 1)
        else:
            print("先頭ページです。")
    elif key == KEY_RESET_PAGE:
        dragging = False
        resizing_action = None
        LOGICAL_PAGE_OFFSET = page_idx
        print(f"🔄 現在のページ(Page {page_idx+1})を「本編1ページ目」に設定しました")
        
        root = tk.Tk()
        root.withdraw()
        new_total = simpledialog.askinteger("出力設定", "現在のページをP1に設定しました。\n続けて、出力する最後のページ（総ページ数）を設定してください:", initialvalue=TOTAL_PAGES, minvalue=1)
        root.destroy()
        
        if new_total is not None:
            TOTAL_PAGES = new_total
            print(f"🔄 出力ページ上限を {TOTAL_PAGES} ページに設定しました")
        
        save_project_settings()
        request_render()
    elif key == KEY_UNDO:
        if undo_stack:
            redo_stack.append((copy.deepcopy(drawn_actions), number_counter))
            g_state, n_cnt = undo_stack.pop()
            drawn_actions.clear()
            drawn_actions.extend(g_state)
            recalculate_numbers()
            recalculate_gaya_numbers()
            print("Undo")
            request_render()
    elif key == KEY_REDO:
        if redo_stack:
            undo_stack.append((copy.deepcopy(drawn_actions), number_counter))
            g_state, n_cnt = redo_stack.pop()
            drawn_actions.clear()
            drawn_actions.extend(g_state)
            recalculate_numbers()
            recalculate_gaya_numbers()
            print("Redo")
            request_render()
    elif key == KEY_TOGGLE_SHAPE:
        dragging = False
        resizing_action = None
        if mode != "color":
            mode = "color"
        else:
            draw_shape = "ellipse" if draw_shape == "rect" else "rect"
        request_render()
    elif key == KEY_TOGGLE_YOLO:
        dragging = False
        resizing_action = None
        yolo_enabled = not yolo_enabled
        request_render()
        if yolo_enabled and not bboxes:
            load_page(page_idx)
    elif key == KEY_MODE_DELETE:
        dragging = False
        resizing_action = None
        mode = "delete" if mode != "delete" else "color"
        request_render()
    elif key == KEY_MODE_ERASER:
        dragging = False
        resizing_action = None
        mode = "eraser" if mode != "eraser" else "color"
        request_render()
    elif key == KEY_MODE_NUMBER:
        dragging = False
        resizing_action = None
        mode = "numbering" if mode != "numbering" else "color"
        request_render()
    elif key == KEY_MODE_TEXT:
        dragging = False
        resizing_action = None
        mode = "manual_text" if mode != "manual_text" else "color"
        request_render()
    elif key == KEY_MODE_LINE:
        dragging = False
        resizing_action = None
        mode = "line" if mode != "line" else "color"
        request_render()
    elif key == KEY_TOGGLE_EXPORT:
        dragging = False
        resizing_action = None
        open_export_dialog()
        request_render()
    elif key == KEY_TOGGLE_HELP:
        dragging = False
        resizing_action = None
        show_help = not show_help
        request_render()
    elif key == KEY_LOAD_PALETTE:
        dragging = False
        resizing_action = None
        root = tk.Tk()
        root.withdraw()
        new_csv_path = filedialog.askopenfilename(title="追加・上書きするパレットCSVを選択", filetypes=[("CSV files", "*.csv")])
        root.destroy()
        if new_csv_path:
            loaded_pal = load_palette_from_csv(new_csv_path)
            if loaded_pal:
                PALETTE = loaded_pal
                current_palette_idx = 0
                current_color = PALETTE[0]["color"]
                current_name = PALETTE[0]["name"]
                save_project_palette(PALETTE, os.path.join(WORK_DIR, "project_characters.csv"))
                print(f"🔄 パレットを {os.path.basename(new_csv_path)} の内容で上書き更新しました")
                request_render()

cv2.destroyAllWindows()
cv2.waitKey(1)

if export_enabled:
    export_character_pages_csv()
    export_to_pdf()
else:
    print("⚠️ 終了時エクスポートはOFFのため、CSVとPDFは出力されませんでした。")

try:
    doc.close()
except: pass

import os
os._exit(0)

