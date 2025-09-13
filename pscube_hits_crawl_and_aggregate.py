# pscube_hits_crawl_and_aggregate.py
# v18.5
# - Canvas/ホットスポット専用UI向けにプローブクリックを追加（_probe_canvas_and_hotspots）
# - DOM属性拡張: alt/title/aria-label からも台番候補を収穫
# - フォールバック順: v06直リンク → DOM候補 → （不足なら）プローブ → テキスト候補 → 現在ページ解析
# - ログ強化: probe_targets / probe_clicks / visited_v06(from probe)

from __future__ import annotations
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Union, Set
from datetime import datetime
import re, unicodedata, json, hashlib
from collections import Counter, deque
from urllib.parse import urljoin

import pandas as pd
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright, Page, Frame, Response, Locator

CONFIG = {
    "start_urls": [
        "https://www.pscube.jp/h/a704506/cgi-bin/nc-v13-001.php?cd_ps=2",
    ],
    "auth_state": "auth.json",   # ログイン不要なら None
    "timeout": 60000,
    "headless": True,            # 画面見たいとき False
    "scroll_pause_ms": 800,
    "max_scroll_rounds": 80,
    "max_cards": None,           # デバッグ時 4〜10
    "per_card_dai_limit": 240,   # デバッグ時 80〜150
    "out_dir": "data/processed",
    "raw_dir": "data/raw",
    "detail_wait_ms": 1700,
    "resp_url_keywords": [
        "nc-v02-","nc-v03-","nc-v05-","nc-v06-","nc-v12-","nc-v13-",
        "nc-v05-004.php","nc-v05-006.php","nc-v05-003.php","nc-v06-001.php",
        "bonu","history","detail","data","json","api","ajax","cd_m","cd_dai","no=",
        "slump","graph","daily","day","kikan","hist","replay","list","unit","hall"
    ],
    "resp_max_bytes": 1_800_000,
    "resp_ring_capacity": 2200,
    "detail_click_retries": 2,
    "save_screenshot": False,    # 必要なら True
    "probe_grid_cols": 8,        # Canvasクリックの格子数（横）
    "probe_grid_rows": 4,        # Canvasクリックの格子数（縦）
    "probe_pause_ms": 140,       # クリック間の待機
}

OUT_DIR = Path(CONFIG["out_dir"]); OUT_DIR.mkdir(parents=True, exist_ok=True)
RAW_DIR = Path(CONFIG["raw_dir"]); RAW_DIR.mkdir(parents=True, exist_ok=True)
RESP_DIR = RAW_DIR / "responses"; RESP_DIR.mkdir(parents=True, exist_ok=True)
LOG_PATH = RAW_DIR / "_diag_log.txt"

def log(msg: str):
    t = f"[{datetime.now().strftime('%H:%M:%S')}] {msg}"
    print(t)
    try:
        with LOG_PATH.open("a", encoding="utf-8") as f:
            f.write(t + "\n")
    except Exception:
        pass

# ========= 正規表現 =========
RE_NUM_G = r"(?P<num>[0-9０-９,]{1,6})\s*(?:G|ｇ|Ｇ|ゲーム)?"
RE_KIND = r"(?P<kind>BIG|ＢＩＧ|B\W*B|ビッグ|REG|ＲＥＧ|R\W*B|レギュラ|RB|ＲＢ|BB|ＢＢ)"
RE_HIT_INLINE_1 = re.compile(rf"{RE_NUM_G}\s*{RE_KIND}", re.IGNORECASE)
RE_HIT_INLINE_2 = re.compile(rf"{RE_KIND}\s*{RE_NUM_G}", re.IGNORECASE)

RE_DAI_LABEL   = re.compile(r"(台番|台番号)\s*[:：#]?\s*([0-9０-９]{2,5})")
RE_DAI_ONLYNUM = re.compile(r"(?:\b|^)\s*([0-9０-９]{2,5})\s*(?:台)?\b")
RE_DAI_GENERIC = re.compile(r"(?:台|No\.?|NO\.?|台番|台番号|#)\s*[:：#\- ]*\s*([0-9０-９]{2,5})", re.IGNORECASE)
RE_DAI_NEAR    = re.compile(r"(?:台|だい)[^0-9０-９]{0,8}([0-9０-９]{2,5})|([0-9０-９]{2,5})[^0-9０-９]{0,8}(?:台|だい)")
RE_ONCLICK_DAI = re.compile(r"(?:dai|no|ban|cd_dai|unit|machine)\D{0,3}([0-9]{2,5})", re.IGNORECASE)
RE_CD_DAI_ANY  = re.compile(r"(?:cd_dai|machineNo|unit_no|table_no|台番|台番号)\D*?([0-9]{2,5})", re.IGNORECASE)

DAI_LINK_CSS = ",".join([
    # a系
    "a[href*='cd_dai=']","a[href*='dai=']","a[href*='no=']","a[href*='cd_m=']","a[href*='cd_d=']",
    "a[href*='nc-v06-']",
    # area（イメージマップ）
    "area[href*='cd_dai=']","area[onclick*='cd_dai']","area[href*='nc-v06-']",
    # svg
    "svg a[href*='cd_dai=']","svg a[href*='nc-v06-']","svg [onclick*='cd_dai']",
    # data-* 属性系
    "[data-dai]","[data-no]","[data-unit]","[data-machine]","[data-ban]",
    # onclick系
    "[onclick*='dai']","[onclick*='no']","[onclick*='ban']","[onclick*='cd_dai']","[onclick*='unit']","[onclick*='machine']",
])

DETAIL_CLICK_CANDIDATES = [
    "台データ","台番","台一覧","全台","全台データ","台番号","機種データ",
    "履歴","ボーナス履歴","当たり履歴","当り履歴","日別","詳細","スランプ","グラフ",
    "データ表示","データを見る","データ","本日","当日"
]
DETAIL_LINK_SELECTORS = [
    "a:has-text('{}')","button:has-text('{}')",'role=link[name="{}"]','role=button[name="{}"]',
    "a[href*='nc-v05-']","a[href*='nc-v06-']","a[href*='nc-v12-']","a[href*='nc-v13-']","a[href*='nc-v02-']",
]
TAB_LABELS = ["本日","当日","1日前","2日前","履歴","ボーナス履歴","日別","グラフ","スランプ","詳細","データ","集計"]

# ========= ユーティリティ =========
def _normalize_text(s: str) -> str:
    s = unicodedata.normalize("NFKC", s)
    s = s.replace(",", " ")
    s = re.sub(r"\s+", " ", s)
    return s.strip()

def _num_to_int(num_raw: str) -> Optional[int]:
    try:
        return int(_normalize_text(num_raw).replace(" ", ""))
    except Exception:
        return None

def _kind_to_std(kind_raw: str) -> str:
    k = unicodedata.normalize("NFKC", kind_raw).upper()
    return "REG" if ("REG" in k or ("R" in k and "B" in k) or "レギュ" in k or k == "RB") else "BIG"

def _to_dai_str(s: Optional[str]) -> Optional[str]:
    if not s: return None
    s = _normalize_text(s)
    m = re.search(r"[0-9]{2,5}", s)
    return m.group(0) if m else None

def _extract_dai_from_text(text: str) -> Optional[str]:
    if not text: return None
    t = _normalize_text(text)
    for pat in (RE_DAI_LABEL, RE_DAI_GENERIC, RE_DAI_ONLYNUM, RE_DAI_NEAR):
        m = pat.search(t)
        if m:
            g = None
            if m.groups():
                for grp in m.groups():
                    if grp: g = grp; break
            else:
                g = m.group(1)
            g = _to_dai_str(g)
            if g and 2 <= len(g) <= 5: return g
    return None

def _extract_all_dai_from_text(text: str) -> List[str]:
    if not text: return []
    t = _normalize_text(text)
    cands: List[str] = []
    for pat in (RE_DAI_LABEL, RE_DAI_GENERIC, RE_DAI_NEAR, RE_DAI_ONLYNUM):
        for m in pat.finditer(t):
            gs = [g for g in m.groups() if g] if m.groups() else [m.group(1)]
            for g in gs:
                x = _to_dai_str(g)
                if x and 2 <= len(x) <= 5:
                    cands.append(x)
    seen = set(); out=[]
    for x in cands:
        if x not in seen:
            seen.add(x); out.append(x)
    return out

def _extract_dai_from_url(url: str) -> Optional[str]:
    if not url: return None
    u = _normalize_text(url)
    for key in ["no", "dai", "ban", "cd_m", "cd_dai", "id","unit","machine"]:
        m = re.search(rf"[?&]{key}=([0-9]{{2,5}})", u, re.IGNORECASE)
        if m: return m.group(1)
    m = re.search(r"/([0-9]{2,5})(?:/|$)", u)
    if m: return m.group(1)
    m = re.search(r"(?:NO\.?|No\.?|#)\s*([0-9]{2,5})", u, re.IGNORECASE)
    if m: return m.group(1)
    return None

def _freq_pick(cands: List[Optional[str]]) -> Optional[str]:
    vals = [ _to_dai_str(c) for c in cands if _to_dai_str(c) and 2 <= len(_to_dai_str(c)) <= 5 ]
    if not vals: return None
    best, _ = Counter(vals).most_common(1)[0]
    return best

# ========= Playwright =========
def _new_context(p, headless=True):
    browser = p.chromium.launch(headless=headless)
    context = browser.new_context(
        storage_state=CONFIG["auth_state"] if CONFIG["auth_state"] else None,
        locale="ja-JP",
        viewport={"width": 1400, "height": 900},
        user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/124 Safari/537.36"),
        extra_http_headers={"Accept-Language": "ja,en;q=0.9"},
    )
    page = context.new_page()
    return browser, context, page

def _goto(ctx: Union[Page, Frame], url: str):
    ctx.goto(url, wait_until="domcontentloaded", timeout=CONFIG["timeout"])
    try: ctx.wait_for_load_state("networkidle", timeout=15_000)
    except Exception: pass

def _click_if_exists(ctx: Union[Page, Frame], selector: str, timeout=2400) -> bool:
    try:
        loc = ctx.locator(selector)
        if loc.count() > 0:
            loc.first.click(timeout=timeout)
            return True
    except Exception: pass
    return False

def _infinite_scroll_and_pager(page: Page):
    last_h = 0
    for _ in range(CONFIG["max_scroll_rounds"]):
        try: h = page.evaluate("() => document.body.scrollHeight")
        except Exception: h = last_h
        if h == last_h:
            clicked = False
            for txt in ["もっと見る", "次へ", "次", ">>", "›", ">", "さらに表示", "≫", "→"]:
                if _click_if_exists(page, f"a:has-text('{txt}')") or _click_if_exists(page, f"button:has-text('{txt}')"):
                    page.wait_for_timeout(CONFIG["scroll_pause_ms"]); clicked = True; break
            if not clicked: break
        else:
            page.evaluate("() => window.scrollTo(0, document.body.scrollHeight)")
            page.wait_for_timeout(CONFIG["scroll_pause_ms"]); last_h = h
    try: page.evaluate("() => window.scrollTo(0, 0)")
    except Exception: pass

def _scroll_and_pager_ctx(ctx: Union[Page, Frame], rounds: Optional[int] = None):
    rounds = rounds or CONFIG["max_scroll_rounds"]
    last_h = 0
    for _ in range(rounds):
        try:
            h = ctx.evaluate("() => document.body ? document.body.scrollHeight : 0")
        except Exception:
            h = last_h
        if h == last_h:
            clicked = False
            for txt in ["もっと見る", "次へ", "次", ">>", "›", ">", "さらに表示", "≫", "→"]:
                if _click_if_exists(ctx, f"a:has-text('{txt}')") or _click_if_exists(ctx, f"button:has-text('{txt}')"):
                    try: ctx.wait_for_load_state("domcontentloaded", timeout=4000)
                    except Exception: pass
                    ctx.wait_for_timeout(CONFIG["scroll_pause_ms"]); clicked = True; break
            if not clicked: break
        else:
            try: ctx.evaluate("() => window.scrollTo(0, document.body.scrollHeight)")
            except Exception: pass
            ctx.wait_for_timeout(CONFIG["scroll_pause_ms"]); last_h = h
    try: ctx.evaluate("() => window.scrollTo(0, 0)")
    except Exception: pass

# ========= パース =========
def _scan_line_for_hits(line: str) -> List[Tuple[int, str]]:
    hits: List[Tuple[int,str]] = []
    for m in RE_HIT_INLINE_1.finditer(line):
        gi = _num_to_int(m.group("num"))
        if gi is not None: hits.append((gi, _kind_to_std(m.group("kind"))))
    for m in RE_HIT_INLINE_2.finditer(line):
        gi = _num_to_int(m.group("num"))
        if gi is not None: hits.append((gi, _kind_to_std(m.group("kind"))))
    return hits

def _parse_hit_records_from_html(html: str) -> Tuple[List[Dict], List[str]]:
    soup = BeautifulSoup(html, "lxml")
    dai_cands: List[str] = []
    page_dai = _extract_dai_from_text(soup.get_text(" ", strip=True)) or None
    if page_dai: dai_cands.append(page_dai)

    records: List[Dict] = []
    for tbl in soup.select("table"):
        for tr in tbl.select("tr"):
            cells = [_normalize_text(c.get_text(" ", strip=True)) for c in tr.select("th,td")]
            if not cells: continue
            row_text = " ".join(cells)
            row_dai = _extract_dai_from_text(row_text)
            if row_dai: dai_cands.append(row_dai)
            for gi, k in _scan_line_for_hits(row_text):
                records.append({"dai": _to_dai_str(row_dai), "game": gi, "kind": k})
    if not records:
        full = _normalize_text(soup.get_text(" ", strip=True))
        for line in re.split(r"[ \u3000]*[\r\n]+[ \u3000]*|(?<=G)\s", full):
            line = _normalize_text(line)
            if not line: continue
            row_dai = _extract_dai_from_text(line)
            if row_dai: dai_cands.append(row_dai)
            for gi, k in _scan_line_for_hits(line):
                records.append({"dai": _to_dai_str(row_dai), "game": gi, "kind": k})
    for sel in ["h1","h2",".title",".machine-name",".dai-number",".machineNo",".no",".tit",".head",".header"]:
        el = soup.select_one(sel)
        if el:
            d = _extract_dai_from_text(el.get_text(" ", strip=True))
            if d: dai_cands.append(d)
    return records, [d for d in dai_cands if d]

def _parse_hit_records_from_json_text(txt: str) -> Tuple[List[Dict], List[str]]:
    records: List[Dict] = []
    dai_cands: List[str] = []
    try:
        data = json.loads(txt)
    except Exception:
        for line in re.split(r"[\r\n]+", _normalize_text(txt)):
            row_dai = _extract_dai_from_text(line)
            if row_dai: dai_cands.append(row_dai)
            for gi, k in _scan_line_for_hits(line):
                records.append({"dai": _to_dai_str(row_dai), "game": gi, "kind": k})
        return records, dai_cands
    def walk(obj):
        if isinstance(obj, dict):
            keys = {k.lower(): k for k in obj.keys()}
            gkey = next((obj[keys[k]] for k in ["g","game","spin","games","games_count","total_games"] if k in keys), None)
            kkey = next((obj[keys[k]] for k in ["k","kind","type","bonus","label","name"] if k in keys), None)
            dkey = next((obj[keys[k]] for k in ["dai","no","number","machine","台番","台番号","machine_no","unit_no","table_no","unit","machineNo"] if k in keys), None)
            if dkey is not None:
                d = _to_dai_str(str(dkey))
                if d: dai_cands.append(d)
            if gkey is not None and kkey is not None:
                gi = _num_to_int(str(gkey))
                if gi is not None:
                    records.append({"dai": _to_dai_str(str(dkey)) if dkey is not None else None,
                                    "game": gi, "kind": _kind_to_std(str(kkey))})
            for v in obj.values(): walk(v)
        elif isinstance(obj, list):
            for v in obj: walk(v)
        elif isinstance(obj, str):
            s = _normalize_text(obj)
            row_dai = _extract_dai_from_text(s)
            if row_dai: dai_cands.append(row_dai)
            for gi, k in _scan_line_for_hits(s):
                records.append({"dai": _to_dai_str(row_dai), "game": gi, "kind": k})
    walk(data)
    return records, dai_cands

# ========= レスポンスリング =========
class RespRing:
    def __init__(self, capacity: int):
        self.buf = deque(maxlen=capacity)
        self.counter = 0
    def push(self, url: str, body: bytes, ct: Optional[str]):
        self.buf.append((url, body, ct))
        try:
            h = hashlib.sha1((url+str(len(body))).encode()).hexdigest()[:8]
            self.counter += 1
            ext = ".json" if "json" in (ct or "").lower() or url.endswith(".json") else ".html"
            path = RESP_DIR / f"resp_{self.counter:05d}_{h}{ext}"
            with open(path, "wb") as f: f.write(body)
        except Exception:
            pass
    def snapshot_and_clear(self) -> List[Tuple[str,bytes,Optional[str]]]:
        items = list(self.buf); self.buf.clear(); return items

def attach_global_response_listener(page: Page) -> RespRing:
    ring = RespRing(CONFIG["resp_ring_capacity"])
    def on_response(resp: Response):
        try:
            url = resp.url
            ct = (resp.headers.get("content-type","") or "").lower()
            if any(k in url for k in CONFIG["resp_url_keywords"]) or \
               ("json" in ct or "html" in ct or "xml" in ct or "csv" in ct or \
                "javascript" in ct or ct.startswith("text/") or "plain" in ct):
                body = resp.body()
                if body and len(body) <= CONFIG["resp_max_bytes"]:
                    ring.push(url, body, ct)
        except Exception:
            pass
    page.on("response", on_response)
    return ring

def _gather_all_htmls(ctx: Union[Page, Frame]) -> List[str]:
    blobs: List[str] = []
    try:
        blobs.append(ctx.content())
    except Exception:
        pass
    try:
        it = ctx.evaluate("() => document.body && document.body.innerText || ''")
        if it:
            blobs.append(it)
    except Exception:
        pass
    if isinstance(ctx, Page):
        for fr in ctx.frames:
            try:
                blobs.append(fr.content())
            except Exception:
                try:
                    it = fr.evaluate("() => document.body && document.body.innerText || ''")
                    if it:
                        blobs.append(it)
                except Exception:
                    pass
    return blobs

def _parse_using_ctx_and_ring(ctx: Union[Page, Frame], page: Page, ring: RespRing, href_hint: Optional[str]) -> List[Dict]:
    records: List[Dict] = []
    dai_cands: List[str] = []
    for blob in _gather_all_htmls(ctx):
        recs, cands = _parse_hit_records_from_html(blob)
        records.extend(recs); dai_cands.extend(cands)
    for url, body, ct in ring.snapshot_and_clear():
        if href_hint:
            d = _extract_dai_from_url(href_hint)
            if d: dai_cands.append(d)
        durl = _extract_dai_from_url(url)
        if durl: dai_cands.append(durl)
        txt = None
        try:
            txt = body.decode("utf-8", errors="ignore")
        except Exception:
            try:
                txt = body.decode("shift_jis", errors="ignore")
            except Exception:
                pass
        if not txt:
            continue
        if "json" in (ct or "") or url.endswith(".json"):
            recs, cands = _parse_hit_records_from_json_text(txt)
        else:
            recs, cands = _parse_hit_records_from_html(txt)
        records.extend(recs); dai_cands.extend(cands)
    fallback = _freq_pick(dai_cands)
    for r in records:
        if not r.get("dai"):
            r["dai"] = fallback
    return records

# ========= 詳細/タブ =========
def _open_detail_if_needed(page: Page) -> None:
    for _ in range(CONFIG["detail_click_retries"] + 1):
        for label in DETAIL_CLICK_CANDIDATES:
            for sel_tpl in DETAIL_LINK_SELECTORS[:4]:
                if _click_if_exists(page, sel_tpl.format(label)):
                    log(f"  - click detail: {label}")
                    try: page.wait_for_load_state("domcontentloaded", timeout=4000)
                    except Exception: pass
                    page.wait_for_timeout(CONFIG["detail_wait_ms"])
                    try: page.wait_for_load_state("networkidle", timeout=3000)
                    except Exception: pass
                    return
        for sel in DETAIL_LINK_SELECTORS[4:]:
            if _click_if_exists(page, sel):
                log(f"  - click detail via href pattern: {sel}")
                try: page.wait_for_load_state("domcontentloaded", timeout=4000)
                except Exception: pass
                page.wait_for_timeout(CONFIG["detail_wait_ms"])
                try: page.wait_for_load_state("networkidle", timeout=3000)
                except Exception: pass
                return

def _open_machine_data_if_present(page: Page) -> None:
    for sel in [
        "a:has-text('機種データページへ')",
        "button:has-text('機種データページへ')",
        "a[href*='nc-v05-003.php']",
    ]:
        if _click_if_exists(page, sel, timeout=1600):
            log("  - goto machine data page (v05-003)")
            try: page.wait_for_load_state("domcontentloaded", timeout=4000)
            except Exception: pass
            page.wait_for_timeout(900)
            try: page.wait_for_load_state("networkidle", timeout=2000)
            except Exception: pass
            return

def _click_tabs_variants(ctx: Union[Page, Frame]) -> int:
    ok = 0
    for label in TAB_LABELS:
        for sel in [f"a:has-text('{label}')", f"button:has-text('{label}')",
                    f"role=tab[name='{label}']", f"role=link[name='{label}']",
                    f"role=button[name='{label}']"]:
            if _click_if_exists(ctx, sel, timeout=1400):
                ok += 1
                try:
                    if isinstance(ctx, Page):
                        ctx.wait_for_load_state("domcontentloaded", timeout=3000)
                    ctx.wait_for_timeout(500)
                except Exception:
                    pass
                break
    return ok

# ========= cd_dai 抜き出し & v06 URL 作成 =========
def _extract_cd_dai_candidates_from_blobs(ctx: Union[Page, Frame]) -> List[str]:
    blobs = _gather_all_htmls(ctx)
    cands: Set[str] = set()
    for blob in blobs:
        for m in re.finditer(r"(?:cd_dai\s*=\s*|cd_dai\s*:\s*|cd_dai%5B%5D\s*=\s*|cd_dai%3D|cd_dai=)([0-9]{2,5})", blob, re.IGNORECASE):
            cands.add(m.group(1))
        for m in RE_CD_DAI_ANY.finditer(blob):
            if m.group(1): cands.add(m.group(1))
    return sorted([d for d in cands if 2 <= len(d) <= 5])

def _v06_url(base_url: str, dai: str) -> str:
    return urljoin(base_url, f"./nc-v06-001.php?cd_dai={dai}")

# ========= DOM 全体から台番号候補 =========
def _harvest_dai_candidates_from_dom(ctx: Union[Page, Frame]) -> List[str]:
    try:
        blobs = ctx.evaluate("""
            () => {
              const arr = [];
              const sels = 'a, area, [onclick], [data-dai], [data-no], [data-unit], [data-machine], [data-ban], [value], [title], [alt], [aria-label]';
              const els = document.querySelectorAll(sels);
              els.forEach(e => {
                const h = e.getAttribute('href') || '';
                const oc = e.getAttribute('onclick') || '';
                const v = e.getAttribute('value') || '';
                const id = e.id || '';
                const cls = e.className || '';
                const ds = e.dataset ? JSON.stringify(e.dataset) : '';
                const tx = (e.innerText || e.textContent || '').slice(0, 200);
                const alt = e.getAttribute('alt') || '';
                const title = e.getAttribute('title') || '';
                const aria = e.getAttribute('aria-label') || '';
                arr.push([h, oc, v, id, cls, ds, tx, alt, title, aria].join(' | '));
              });
              return arr;
            }
        """)
    except Exception:
        blobs = []
    cands: Set[str] = set()
    for s in blobs:
        s_norm = unicodedata.normalize("NFKC", s)
        for m in re.finditer(r"(?:dai|unit|machine|no|台|台番|台番号)[^0-9]{0,16}([0-9]{2,5})", s_norm, re.IGNORECASE):
            cands.add(m.group(1))
        for m in re.finditer(r"([0-9]{2,5})[^0-9]{0,16}(?:dai|unit|machine|no|台|台番|台番号)", s_norm, re.IGNORECASE):
            cands.add(m.group(1))
        for m in re.finditer(r"[?&#/](?:cd_dai|dai|no|unit|machine)[=/]*([0-9]{2,5})", s_norm, re.IGNORECASE):
            cands.add(m.group(1))
    out = sorted([d for d in cands if 2 <= len(d) <= 5])
    return out

# ========= DOM 内リンク収集 =========
def _collect_dai_links_all(page: Page) -> List[Tuple[Union[Page, Frame], Dict[str,str]]]:
    items: List[Tuple[Union[Page, Frame], Dict[str,str]]] = []
    def grab(ctx: Union[Page, Frame]):
        _scroll_and_pager_ctx(ctx, rounds=40)
        try:
            links = ctx.eval_on_selector_all(DAI_LINK_CSS, """
                els => els.map(e => ({
                    h: e.getAttribute('href'),
                    t: e.innerText || e.textContent || '',
                    d: e.getAttribute('data-dai') || e.getAttribute('data-no') || e.getAttribute('data-unit') || e.getAttribute('data-machine') || e.getAttribute('data-ban') || '',
                    oc: e.getAttribute('onclick') || ''
                }))
            """)
            for it in links: items.append((ctx, it))
        except Exception:
            pass
    grab(page)
    for fr in page.frames:
        try: grab(fr)
        except Exception: pass
    return items

# ========= プローブ（Canvas/ホットスポット） =========
def _probe_canvas_and_hotspots(ctx: Union[Page, Frame]) -> Tuple[int,int]:
    """Canvas等に対して格子状にclickイベントを投げて、AJAX等のレスポンス発生を促す"""
    targets = []
    try:
        targets = ctx.evaluate("""
            (cols, rows) => {
              const boxes = [];
              const pushGrid = (el) => {
                const r = el.getBoundingClientRect();
                if (!r.width || !r.height) return;
                for (let i=0;i<rows;i++){
                  for (let j=0;j<cols;j++){
                    const x = r.left + (j+0.5)*(r.width/cols);
                    const y = r.top  + (i+0.5)*(r.height/rows);
                    boxes.push({x, y, el});
                  }
                }
              };
              // Canvas と、role=application/graphics-doc っぽい領域、pointer要素
              document.querySelectorAll('canvas, [role=application], [role=graphics-document], .clickable')
                .forEach(pushGrid);
              return boxes.map(b => ({x: Math.floor(b.x), y: Math.floor(b.y)}));
            }
        """, CONFIG["probe_grid_cols"], CONFIG["probe_grid_rows"])
    except Exception:
        targets = []
    clicked = 0
    for pt in targets[:600]:  # 暴走抑制
        try:
            ctx.evaluate("""
                (x, y) => {
                  const el = document.elementFromPoint(x, y);
                  if (!el) return false;
                  const ev = new MouseEvent('click', {bubbles:true, cancelable:true, clientX:x, clientY:y});
                  el.dispatchEvent(ev);
                  return true;
                }
            """, pt["x"], pt["y"])
            clicked += 1
            try: ctx.wait_for_timeout(CONFIG["probe_pause_ms"])
            except Exception: pass
        except Exception:
            pass
    return len(targets), clicked

# ========= 訪問＆解析 =========
def _visit_and_parse_current(page: Page, ring: RespRing) -> List[Dict]:
    _click_tabs_variants(page)
    for fr in page.frames:
        try: _click_tabs_variants(fr)
        except Exception: pass
    _scroll_and_pager_ctx(page, rounds=30)
    for fr in page.frames:
        try: _scroll_and_pager_ctx(fr, rounds=20)
        except Exception: pass
    page.wait_for_timeout(CONFIG["detail_wait_ms"])
    try: page.wait_for_load_state("networkidle", timeout=3000)
    except Exception: pass
    return _parse_using_ctx_and_ring(page, page, ring, href_hint=None)

# ========= 台リンク/候補の巡回 =========
def _drill_dai_links(page: Page, ring: RespRing, per_card_limit: Optional[int]) -> List[Dict]:
    out_records: List[Dict] = []
    visited_hrefs: set = set()
    visited_dais: set = set()

    # 1) DOMからリンク収集
    link_items = _collect_dai_links_all(page)
    log(f"  - link_items: {len(link_items)}")
    if not link_items:
        _open_machine_data_if_present(page)
        link_items = _collect_dai_links_all(page)
        log(f"  - link_items(after v05-003): {len(link_items)}")

    # v06 直URLを優先
    v06_links = [(ctx, it) for (ctx, it) in link_items if (it.get("h") or "").find("nc-v06-") >= 0 or (it.get("h") or "").find("cd_dai=") >= 0]
    ordered = v06_links + [(ctx, it) for (ctx, it) in link_items if (ctx, it) not in v06_links]

    def _visit_href(ctx, href, dai_hint=None):
        nav = False
        try:
            with page.expect_navigation(wait_until="domcontentloaded", timeout=8000):
                ctx.locator(f"a[href='{href}']").first.click(timeout=3000)
            nav = True
        except Exception:
            try:
                ctx.locator(DAI_LINK_CSS).first.click(timeout=2500)
            except Exception:
                if dai_hint:
                    _click_dai_by_text_ctx(ctx, dai_hint)
        recs = _visit_and_parse_current(page, ring)
        if nav:
            try:
                page.go_back(wait_until="domcontentloaded", timeout=CONFIG["timeout"])
                page.wait_for_load_state("networkidle", timeout=3000)
            except Exception: pass
        page.wait_for_timeout(160)
        return recs

    # 1-a) まずは見えているリンクを踏む
    if ordered:
        limit = len(ordered) if per_card_limit is None else min(len(ordered), int(per_card_limit))
        for idx in range(limit):
            ctx, it = ordered[idx]
            href = (it.get("h") or "").strip()
            data_dai = (it.get("d") or "").strip()
            onclick = (it.get("oc") or "").strip()
            dai_hint = _to_dai_str(data_dai) or (_to_dai_str(onclick) if RE_ONCLICK_DAI.search(onclick or "") else None)

            if href and href in visited_hrefs:
                continue
            if dai_hint and dai_hint in visited_dais:
                continue

            if href:
                visited_hrefs.add(href)
                recs = _visit_href(ctx, href, dai_hint=dai_hint)
                out_records.extend(recs)
            else:
                if dai_hint and dai_hint not in visited_dais:
                    _click_dai_by_text_ctx(ctx, dai_hint)
                    recs = _visit_and_parse_current(page, ring)
                    out_records.extend(recs)
                    visited_dais.add(dai_hint)

    # 2) DOM全体からの候補抽出 → v06直叩き
    dom_dai_list = _harvest_dai_candidates_from_dom(page)
    log(f"  - dom_dai_candidates: {len(dom_dai_list)}")
    if dom_dai_list:
        limit = len(dom_dai_list) if per_card_limit is None else min(len(dom_dai_list), int(per_card_limit))
        visited_v06_dom = 0
        for d in dom_dai_list[:limit]:
            if d in visited_dais: continue
            target = _v06_url(page.url, d)
            try:
                with page.expect_navigation(wait_until="domcontentloaded", timeout=8000):
                    page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
            except Exception:
                try:
                    page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
                except Exception:
                    continue
            recs = _visit_and_parse_current(page, ring)
            out_records.extend(recs)
            visited_dais.add(d)
            visited_v06_dom += 1
            try:
                page.go_back(wait_until="domcontentloaded", timeout=CONFIG["timeout"])
                page.wait_for_load_state("networkidle", timeout=3000)
            except Exception: pass
            page.wait_for_timeout(120)
        log(f"  - visited_v06(from dom): {visited_v06_dom}")

    # 3) まだゼロっぽいなら Canvas/ホットスポットにプローブ
    visited_v06_probe = 0
    if (not dom_dai_list) and (len(out_records) == 0):
        try:
            total_targets, clicked = _probe_canvas_and_hotspots(page)
            log(f"  - probe_targets: {total_targets}, probe_clicks: {clicked}")
        except Exception:
            log("  - probe failed (exception)")
        # プローブ後のレスポンスをそのまま解析して台番候補を収穫
        recs_after_probe = _parse_using_ctx_and_ring(page, page, ring, href_hint=None)
        # 台番候補が埋まっていないレコードがあれば、さらにテキストから拾う
        if recs_after_probe:
            out_records.extend(recs_after_probe)
            # 追加で cd_dai 候補を拾って v06 直叩き
            probe_cands = set()
            for r in recs_after_probe:
                if r.get("dai"): probe_cands.add(_to_dai_str(r["dai"]))
            if not probe_cands:
                probe_cands.update(_extract_cd_dai_candidates_from_blobs(page))
            if probe_cands:
                limit = len(probe_cands) if per_card_limit is None else min(len(probe_cands), int(per_card_limit))
                for d in list(probe_cands)[:limit]:
                    if not d: continue
                    target = _v06_url(page.url, d)
                    try:
                        with page.expect_navigation(wait_until="domcontentloaded", timeout=8000):
                            page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
                    except Exception:
                        try:
                            page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
                        except Exception:
                            continue
                    recs = _visit_and_parse_current(page, ring)
                    out_records.extend(recs)
                    visited_v06_probe += 1
                    try:
                        page.go_back(wait_until="domcontentloaded", timeout=CONFIG["timeout"])
                        page.wait_for_load_state("networkidle", timeout=3000)
                    except Exception: pass
                    page.wait_for_timeout(120)
        log(f"  - visited_v06(from probe): {visited_v06_probe}")

    # 4) HTML/JSテキストから cd_dai 候補 → v06直叩き（最後の頼み）
    if per_card_limit is None or len(out_records) == 0:
        cd_dai_list = _extract_cd_dai_candidates_from_blobs(page)
        log(f"  - text_cd_dai_candidates: {len(cd_dai_list)}")
        if cd_dai_list:
            limit = len(cd_dai_list) if per_card_limit is None else min(len(cd_dai_list), int(per_card_limit))
            visited_v06_text = 0
            for d in cd_dai_list[:limit]:
                if d in visited_dais: continue
                target = _v06_url(page.url, d)
                try:
                    with page.expect_navigation(wait_until="domcontentloaded", timeout=8000):
                        page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
                except Exception:
                    try:
                        page.goto(target, timeout=CONFIG["timeout"], wait_until="domcontentloaded")
                    except Exception:
                        continue
                recs = _visit_and_parse_current(page, ring)
                out_records.extend(recs)
                visited_dais.add(d)
                visited_v06_text += 1
                try:
                    page.go_back(wait_until="domcontentloaded", timeout=CONFIG["timeout"])
                    page.wait_for_load_state("networkidle", timeout=3000)
                except Exception: pass
                page.wait_for_timeout(120)
            log(f"  - visited_v06(from text): {visited_v06_text}")

    # 5) 何も取れなければ現在ページを解析
    if not out_records:
        out_records.extend(_visit_and_parse_current(page, ring))

    return out_records

# ========= 一覧→機種カード→巡回 =========
def _collect_from_v13(page: Page, max_cards: Optional[int]) -> pd.DataFrame:
    _infinite_scroll_and_pager(page)
    card_selectors = [
        "a[href].card:visible","a:has(.card):visible",".card:visible",
        "a[href].machine:visible","a[href]:visible",
    ]
    cards: Optional[Locator] = None
    for sel in card_selectors:
        loc = page.locator(sel)
        if loc.count() > 0: cards = loc; break
    if cards is None or cards.count() == 0:
        log("カードが見つかりません（セレクタ要調整）")
        return pd.DataFrame(columns=["台番","game","kind","source_url","scraped_at"])

    total = cards.count()
    if max_cards: total = min(total, max_cards)
    log(f"カード検出: {cards.count()} 件 → 取得対象: {total} 件")

    ring = attach_global_response_listener(page)
    rows = []
    for i in range(total):
        card = cards.nth(i)
        href_card = None
        try: href_card = card.get_attribute("href")
        except Exception: pass

        url_before = page.url
        nav = False
        try:
            with page.expect_navigation(wait_until="domcontentloaded", timeout=8000):
                card.click(timeout=3000)
            nav = True
        except Exception:
            try: card.click(timeout=1500)  # モーダル型
            except Exception: pass
            nav = False

        _open_detail_if_needed(page)
        _scroll_and_pager_ctx(page, rounds=40)
        for fr in page.frames:
            try: _scroll_and_pager_ctx(fr, rounds=20)
            except Exception: pass

        recs = _drill_dai_links(page, ring, CONFIG["per_card_dai_limit"])
        if not recs:
            recs = _visit_and_parse_current(page, ring)

        for r in recs:
            if r.get("game") is None or r.get("kind") is None:
                continue
            rows.append({
                "台番": _to_dai_str(r.get("dai")),
                "game": int(r["game"]),
                "kind": "BIG" if str(r["kind"]).upper().startswith("B") else "REG",
                "source_url": page.url if nav else (href_card or url_before),
                "scraped_at": datetime.now().isoformat()
            })

        if nav:
            try:
                page.go_back(wait_until="domcontentloaded", timeout=CONFIG["timeout"])
                page.wait_for_load_state("networkidle", timeout=3000)
            except Exception: pass
        else:
            for sel in ["button:has-text('閉じる')", ".modal-close", ".close", "button[aria-label='Close']"]:
                if _click_if_exists(page, sel, timeout=900): page.wait_for_timeout(200); break
        page.wait_for_timeout(200)

    return pd.DataFrame(rows)

# ========= メイン =========
def main():
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    try:
        if LOG_PATH.exists():
            LOG_PATH.rename(RAW_DIR / f"_diag_log_{ts}.txt")
    except Exception:
        pass

    all_rows: List[pd.DataFrame] = []

    with sync_playwright() as p:
        browser, context, page = _new_context(p, headless=CONFIG["headless"])
        try:
            for url in CONFIG["start_urls"]:
                log(f"RUN: {url}")
                _goto(page, url)
                df = _collect_from_v13(page, CONFIG["max_cards"])
                if not df.empty: all_rows.append(df)
        finally:
            context.close(); browser.close()

    if not all_rows:
        log("収集できた当たり履歴がありませんでした。デバッグ用のHTML/レスポンスは data/raw に保存します。")
        return

    hits_df = pd.concat(all_rows, ignore_index=True)
    # 正規化＆重複除去
    hits_df["台番"] = hits_df["台番"].astype("string").fillna("").map(lambda s: _to_dai_str(str(s)) if s else None)
    hits_df["kind"] = hits_df["kind"].str.upper().replace({"ＢＩＧ":"BIG","ＲＥＧ":"REG"})
    hits_df = (
        hits_df
        .drop_duplicates(subset=["台番","game","kind"])
        .sort_values(["台番","game","kind"], na_position="last")
        .reset_index(drop=True)
    )

    out_hits = OUT_DIR / f"pscube_hits_{ts}.csv"
    hits_df.to_csv(out_hits, index=False, encoding="utf-8-sig")
    log(f"SAVE: ヒット明細 {out_hits} ({len(hits_df)}行)")

    agg_src = hits_df.dropna(subset=["台番"]).copy()
    if agg_src.empty:
        log("NOTE: 台番が特定できなかったため、集計対象がありません（明細は保存済み）。")
        return

    agg = (
        agg_src.pivot_table(index="台番", columns="kind", values="game", aggfunc=["count","mean"])
        .sort_index().fillna(0)
    )
    agg.columns = [f"{a}_{b}" for a,b in agg.columns]
    out_agg = OUT_DIR / f"pscube_hits_summary_{ts}.csv"
    agg.to_csv(out_agg, encoding="utf-8-sig")
    log(f"SAVE: 集計 {out_agg} ({len(agg)}台)")

if __name__ == "__main__":
    main()

