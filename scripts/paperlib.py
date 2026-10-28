"""paperlib — 로컬 논문 라이브러리 (Zotero·LLM API 없이 동작).

논문 하나 = 라이브러리의 폴더 하나(papers/<citekey>/):
  meta.json     서지 정보 (Crossref·arXiv·OpenAlex, 모두 무료·키 불필요)
  paper.pdf     원문 PDF (--no-pdf 이면 추출 후 삭제)
  text.md       쪽 표시(<!-- page N -->)가 달린 본문
  figures/      fig1.jpg ... (캡션 기준으로 잘라낸 그림)
  figures.json  그림 번호·쪽·캡션·파일
  summary.md    요약 노트 (Claude가 작성, 주장마다 [@citekey, p. N])
라이브러리 루트에는 library.json(목록)과 library.bib(BibTeX)를 자동으로 다시 만든다.

사용:
  python paperlib.py add <DOI | arXiv ID/URL | PDF 경로 | PDF URL | 웹페이지 URL> [--no-pdf] [--key <citekey>]
  python paperlib.py set <citekey> 필드=값 ...     (보고서 서지 보완: type authors year publisher number url date accessed short title)
  python paperlib.py rename <citekey> <새 citekey>
  python paperlib.py list [--pending] | search <단어...> | show <citekey>
  python paperlib.py cite <원고.md> [-o 결과.md] [--style ieee|apa] [--table] [--heading 참고문헌]   (기본: IEEE 번호식 [1])
  python paperlib.py render [citekey]      summary.md → index.html (라이브러리 목록 index.html 포함)
  python paperlib.py rebuild

라이브러리 위치: 환경 변수 PAPER_LIB, 없으면 ~/paper-library
"""
import argparse
import datetime
import html
import json
import os
import re
import shutil
import sys
import unicodedata
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
from pathlib import Path

try:
    import pymupdf as fitz  # PyMuPDF 1.24+
except ImportError:
    import fitz  # 이전 버전 PyMuPDF
import requests

LIB = Path(os.environ.get("PAPER_LIB", Path.home() / "paper-library"))
PAPERS = LIB / "papers"
UA = {"User-Agent": "paperlib/1.0 (personal literature library)"}
STOP = {"a", "an", "the", "on", "of", "for", "in", "to", "and", "with", "via", "from", "towards", "toward", "is", "are", "beyond"}


# ---------------------------------------------------------------- 서지 정보
def http_json(url, **kw):
    r = requests.get(url, headers=UA, timeout=30, **kw)
    r.raise_for_status()
    return r.json()


def split_name(full):
    parts = full.strip().split()
    return {"family": parts[-1], "given": " ".join(parts[:-1])} if parts else {"family": "", "given": ""}


def from_crossref(doi):
    m = http_json(f"https://api.crossref.org/works/{requests.utils.quote(doi)}")["message"]
    abstract = re.sub(r"<[^>]+>", "", m.get("abstract", "") or "").strip()
    date = (m.get("issued") or m.get("published") or {}).get("date-parts", [[None]])[0]
    return {
        "title": html.unescape((m.get("title") or [""])[0]),
        "authors": [{"family": a["family"], "given": a.get("given", "")} if a.get("family") else {"literal": a.get("name", "")}
                    for a in m.get("author", []) if a.get("family") or a.get("name")],
        "year": date[0] if date else None,
        "venue": html.unescape((m.get("container-title") or [""])[0]),
        "volume": m.get("volume", ""), "issue": m.get("issue", ""), "pages": m.get("page", ""),
        "doi": m.get("DOI", doi).lower(), "url": m.get("URL", ""), "type": m.get("type", ""),
        "publisher": m.get("publisher", ""),
        "abstract": html.unescape(abstract), "source": "crossref",
    }


def from_arxiv(aid):
    ns = {"a": "http://www.w3.org/2005/Atom", "x": "http://arxiv.org/schemas/atom"}
    r = requests.get("https://export.arxiv.org/api/query", params={"id_list": aid}, headers=UA, timeout=30)
    r.raise_for_status()
    e = ET.fromstring(r.text).find("a:entry", ns)
    if e is None or e.find("a:title", ns) is None:
        raise SystemExit(f"arXiv에서 {aid}를 찾지 못함")
    t = lambda tag: " ".join((e.findtext(tag, "", ns) or "").split())
    pdf = next((l.get("href") for l in e.findall("a:link", ns) if l.get("title") == "pdf"), f"https://arxiv.org/pdf/{aid}")
    return {
        "title": t("a:title"), "authors": [split_name(a.findtext("a:name", "", ns)) for a in e.findall("a:author", ns)],
        "year": int(t("a:published")[:4]), "venue": "arXiv", "volume": "", "issue": "", "pages": "",
        "doi": t("x:doi").lower(), "arxiv": aid, "url": f"https://arxiv.org/abs/{aid}", "type": "preprint",
        "abstract": t("a:summary"), "pdf_url": pdf, "journal_ref": t("x:journal_ref"), "source": "arxiv",
    }


def oa_pdf_url(doi):
    try:
        w = http_json(f"https://api.openalex.org/works/https://doi.org/{doi}")
    except Exception:
        return ""
    loc = w.get("best_oa_location") or {}
    return loc.get("pdf_url") or (w.get("open_access") or {}).get("oa_url") or ""


def search_title(title):
    """제목으로 Crossref 검색. 제목이 충분히 비슷할 때만 DOI를 돌려준다."""
    items = http_json("https://api.crossref.org/works", params={"query.bibliographic": title, "rows": 3})["message"]["items"]
    norm = lambda s: re.sub(r"[^a-z0-9]", "", s.lower())
    for it in items:
        cand = (it.get("title") or [""])[0]
        a, b = norm(cand), norm(title)
        if a and b and (a in b or b in a):
            return it["DOI"]
    return ""


def norm_title(s):
    return re.sub(r"[\W_]", "", (s or "").lower())  # 한글 제목도 비교되도록 유니코드 글자는 남김


def same_title(a, b):
    """PDF에서 읽은 제목과 검색 결과 제목이 같은 논문인지 (앞 40자 기준)."""
    a, b = norm_title(a), norm_title(b)
    if min(len(a), len(b)) < 8:  # "10" 같은 장 번호를 제목으로 읽으면 엉뚱한 논문과 맞춰짐
        return False
    return a[:40] in b or b[:40] in a


def pdf_title(doc):
    """PDF 메타데이터의 제목, 없으면 1쪽에서 가장 큰 글자 줄들."""
    t = (doc.metadata or {}).get("title", "").strip()
    if len(t) > 15:
        return t
    spans = [(s["size"], s["text"]) for b in doc[0].get_text("dict")["blocks"] for l in b.get("lines", []) for s in l["spans"]
             if s["text"].strip()]
    if not spans:  # 스캔본처럼 1쪽에 글자가 없는 PDF
        return ""
    big = max(sz for sz, _ in spans)
    return " ".join(tx.strip() for sz, tx in spans if sz >= big - 0.5)


def arxiv_by_title(title):
    words = [w for w in re.findall(r"[A-Za-z0-9-]+", title) if w.lower() not in STOP][:8]
    r = requests.get("https://export.arxiv.org/api/query", headers=UA, timeout=30,
                     params={"search_query": " AND ".join(f"ti:{w}" for w in words), "max_results": 5})
    r.raise_for_status()
    ns = {"a": "http://www.w3.org/2005/Atom"}
    for e in ET.fromstring(r.text).findall("a:entry", ns):
        if same_title(" ".join((e.findtext("a:title", "", ns)).split()), title):
            aid = e.findtext("a:id", "", ns).rsplit("/", 1)[-1]
            return from_arxiv(re.sub(r"v\d+$", "", aid))
    return None


ARXIV_RE = re.compile(r"(?:arxiv\.org/(?:abs|pdf)/|arxiv:\s*)?(\d{4}\.\d{4,5})(v\d+)?", re.I)
DOI_RE = re.compile(r"\b(10\.\d{4,9}/[^\s\"<>]+)", re.I)


def resolve(src):
    """입력 하나를 (meta, 로컬 PDF 경로 또는 None)으로."""
    p = Path(src)
    if p.suffix.lower() == ".pdf" and p.exists():
        doc = fitz.open(p)
        head = doc[0].get_text()  # 1쪽만: 2쪽부터는 참고문헌의 DOI·arXiv 번호가 섞일 수 있음
        title = pdf_title(doc)
        meta = None
        d = DOI_RE.search(head)
        m = ARXIV_RE.search(head) if "arxiv" in head.lower() else None
        for get in ((lambda: from_crossref(d.group(1).rstrip(".,;)"))) if d else None,
                    (lambda: from_arxiv(m.group(1))) if m else None,
                    lambda: from_crossref(search_title(title)) if search_title(title) else None,
                    lambda: arxiv_by_title(title)):
            if get is None:
                continue
            try:
                cand = get()
            except Exception:
                cand = None
            if cand and same_title(cand["title"], title):
                meta = cand
                break
        if meta and meta.get("arxiv") and meta.get("doi"):
            try:
                pub = from_crossref(meta["doi"])
                pub.update(arxiv=meta["arxiv"], source="crossref+arxiv")
                meta = pub
            except Exception:
                pass
        meta = meta or {"title": title, "authors": [], "year": None, "venue": "", "doi": "", "url": "",
                        "abstract": "", "source": "pdf", "type": "report"}  # DOI 없는 PDF는 보고서로 가정
        return meta, p
    m = ARXIV_RE.fullmatch(src.strip()) or (ARXIV_RE.search(src) if "arxiv" in src.lower() else None)
    if m:
        meta = from_arxiv(m.group(1))
        if meta["doi"]:  # 출판본이 있으면 서지는 출판본, PDF는 arXiv
            try:
                pub = from_crossref(meta["doi"])
                pub.update(arxiv=meta["arxiv"], pdf_url=meta["pdf_url"], source="crossref+arxiv")
                meta = pub
            except Exception:
                pass
        return meta, None
    d = DOI_RE.search(src)
    if d:
        meta = from_crossref(d.group(1).rstrip(".,;)"))
        meta["pdf_url"] = oa_pdf_url(meta["doi"])
        return meta, None
    if src.lower().startswith("http"):
        r = requests.get(src, headers=UA, timeout=90)
        r.raise_for_status()
        if r.content.startswith(b"%PDF"):
            tmp = LIB / "_download.pdf"
            tmp.parent.mkdir(parents=True, exist_ok=True)
            tmp.write_bytes(r.content)
            meta, pdf = resolve(str(tmp))
            if not meta.get("doi"):  # 웹에서 받은 보고서 PDF: 출처 URL과 접속일 기록
                meta["url"] = meta.get("url") or src
                meta["accessed"] = datetime.date.today().isoformat()
            return meta, pdf
        return from_web(src, r), None
    raise SystemExit(f"알 수 없는 입력: {src}")


class _TextGrab(HTMLParser):
    SKIP = {"script", "style", "noscript", "nav", "footer", "header", "form", "aside", "svg"}
    BLOCK = {"p", "div", "br", "li", "h1", "h2", "h3", "h4", "tr", "section", "article", "table"}

    def __init__(self):
        super().__init__()
        self.out, self.skip, self.meta, self.title = [], 0, {}, ""
        self._in_title = False

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag in self.SKIP:
            self.skip += 1
        elif tag == "title":
            self._in_title = True
        elif tag == "meta" and a.get("content"):
            self.meta[(a.get("property") or a.get("name") or "").lower()] = a["content"]
        if tag in self.BLOCK:
            self.out.append("\n")

    def handle_endtag(self, tag):
        if tag in self.SKIP and self.skip:
            self.skip -= 1
        elif tag == "title":
            self._in_title = False
        if tag in self.BLOCK:
            self.out.append("\n")

    def handle_data(self, data):
        if self._in_title:
            self.title += data
        elif not self.skip:
            self.out.append(data)


def from_web(url, resp):
    """웹페이지(보도자료·정책 페이지 등)의 제목·사이트·날짜와 본문 텍스트."""
    if resp.encoding in (None, "ISO-8859-1"):
        resp.encoding = resp.apparent_encoding
    g = _TextGrab()
    g.feed(resp.text)
    mt = g.meta
    text = "\n".join(l.strip() for l in "".join(g.out).splitlines() if l.strip())
    date = (mt.get("article:published_time") or mt.get("date") or mt.get("dc.date") or "")[:10]
    return {"title": html.unescape(mt.get("og:title") or g.title).strip(), "authors": [],
            "year": int(date[:4]) if date[:4].isdigit() else None, "date": date,
            "venue": "", "publisher": mt.get("og:site_name", ""), "doi": "", "url": url,
            "accessed": datetime.date.today().isoformat(), "type": "webpage",
            "abstract": html.unescape(mt.get("og:description") or mt.get("description") or ""),
            "source": "web", "_text": text}


def download(url, dest):
    r = requests.get(url, headers=UA, timeout=90)
    r.raise_for_status()
    if not r.content.startswith(b"%PDF"):
        raise RuntimeError(f"PDF가 아님 (아마 로그인·유료 페이지): {url}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(r.content)


# ---------------------------------------------------------------- citekey
def ascii_word(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    return re.sub(r"[^A-Za-z0-9]", "", s)


def key_word(s, n=12):
    """한글·한자·가나가 있으면 그대로(기호만 제거), 아니면 ASCII로."""
    clean = re.sub(r"[\W_]", "", s)
    if re.search(r"[가-힣\u3040-\u30ff\u4e00-\u9fff]", clean):
        return clean[:n]
    return ascii_word(s)[:n]


def make_key(meta):
    first = (meta.get("authors") or [{}])[0]
    who = key_word(meta.get("short") or first.get("family") or first.get("literal") or meta.get("publisher") or "", 14)
    word = next((key_word(w) for w in meta["title"].split() if key_word(w) and key_word(w).lower() not in STOP), "doc")
    base = f"{who or 'Anon'}{meta.get('year') or 'nd'}{word.lower() if word.isascii() else word}"
    key, n = base, 0
    # DOI가 둘 다 없으면 다른 논문으로 본다 (같은 키로 덮어쓰지 않도록)
    while (PAPERS / key).exists() and not (meta.get("doi") and json.loads((PAPERS / key / "meta.json").read_text(encoding="utf-8")).get("doi") == meta["doi"]):
        n += 1
        key = base + "abcdefghij"[n - 1]
    return key


def find_existing(meta):
    """DOI·arXiv가 같거나, 없으면 제목이 같은 기존 항목의 citekey."""
    metas = [json.loads(mj.read_text(encoding="utf-8")) for mj in PAPERS.glob("*/meta.json")]
    for m in metas:
        if (meta.get("doi") and m.get("doi") == meta["doi"]) or (meta.get("arxiv") and m.get("arxiv") == meta["arxiv"]):
            return m["key"]
    for m in metas:
        if same_title(m.get("title"), meta.get("title")):
            return m["key"]
    return None


# ---------------------------------------------------------------- 본문·그림
CAP_RE = re.compile(r"^\s*(?:(?:fig(?:ure)?\.?)\s*(\d+)\s*[:.|\u2002\u2003\u2009]"
                    r"|[<\[〈［]\s*그림\s*(\d+(?:[-.]\d+)?)\s*[>\]〉］]"
                    r"|그림\s*(\d+(?:[-.]\d+)?)\s*[:.]\s)", re.I)


def cap_num(text):
    m = CAP_RE.match(text)
    return next((g for g in m.groups() if g), None) if m else None


def num_key(n):
    return tuple(int(x) for x in re.split(r"[-.]", n))


def extract_text(doc, out):
    parts = [f"<!-- page {i + 1} -->\n{pg.get_text('text').strip()}\n" for i, pg in enumerate(doc)]
    out.write_text("\n".join(parts), encoding="utf-8")


def extract_figures(doc, outdir, zoom=2.5):
    """캡션(Figure N: …) 위쪽의 그래픽 요소(이미지·벡터 그림)를 모아 잘라낸다."""
    outdir.mkdir(exist_ok=True)
    figs, seen = [], set()
    for pno, page in enumerate(doc):
        W, H = page.rect.width, page.rect.height
        blocks = [b for b in page.get_text("blocks") if b[6] == 0]
        caps = [b for b in blocks if cap_num(b[4])]
        if not caps:
            continue
        gfx = [fitz.Rect(i["bbox"]) for i in page.get_image_info()]
        gfx += [d["rect"] for d in page.get_drawings() if d["rect"].width * d["rect"].height < 0.8 * W * H]
        gfx = [g for g in gfx if g.width > 1 or g.height > 1]
        for cb in sorted(caps, key=lambda b: b[1]):
            num = cap_num(cb[4])
            if num in seen:
                continue
            cap = fitz.Rect(cb[:4])
            col = (W / 2 - 5, W) if cap.x0 > W * 0.45 else (0, W / 2 + 5) if cap.x1 < W * 0.55 else (0, W)
            above_caps = [b[3] for b in caps if b[3] <= cap.y0 and b is not cb]
            top_limit = max(above_caps, default=0)
            cand = sorted((g for g in gfx if g.y1 <= cap.y0 + 4 and g.y0 >= top_limit - 2
                           and g.x1 > col[0] and g.x0 < col[1]), key=lambda g: -g.y1)
            if not cand or cap.y0 - cand[0].y1 > 60:
                continue
            box = fitz.Rect(cand[0])
            for g in cand[1:]:
                if g.y1 >= box.y0 - 30:
                    box |= g
            if box.height < 25 or box.width < 40:
                continue
            for _ in range(3):  # 그림 안팎의 짧은 글자(축 눈금·축 이름·범례) 포함
                near = box + (-22, -14, 22, 14)
                for b in blocks:
                    r = fitz.Rect(b[:4])
                    short = len(b[4].strip()) < 80 or r.intersects(box)
                    if short and r.intersects(near) and r.y1 <= cap.y0 + 1 and r.y0 >= top_limit and b is not cb:
                        box |= r
            box = (box + (-6, -6, 6, 6)) & page.rect
            name = f"fig{num}.jpg"
            pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom), clip=box)
            pix.save(outdir / name, jpg_quality=85)
            seen.add(num)
            figs.append({"id": f"fig{num}", "label": f"{'그림' if '그림' in cb[4][:6] else 'Figure'} {num}", "page": pno + 1,
                         "caption": " ".join(cb[4].split()), "file": f"figures/{name}"})
    return sorted(figs, key=lambda f: num_key(f["id"][3:]))


# ---------------------------------------------------------------- 저자
def fam(a):
    """개인 저자는 성, 기관·한글 이름(literal)은 이름 전체."""
    return a.get("literal") or a.get("family", "")


def parse_authors(text):
    """'과학기술정책연구원; 홍길동' · 'Smith, John; Lee, K.' · 'John Smith' 형식을 저자 목록으로."""
    out = []
    for part in [x.strip() for x in re.split(r"[;\n]", text) if x.strip()]:
        if "," in part:
            f, g = [x.strip() for x in part.split(",", 1)]
            out.append({"family": f, "given": g})
        elif re.search(r"[가-힣]", part) or " " not in part:
            out.append({"literal": part})  # 기관명·한글 이름은 그대로 표기
        else:
            out.append(split_name(part))
    return out


KIND = {"report": "report", "report-component": "report", "report-series": "report",
        "book": "book", "monograph": "book", "edited-book": "book", "webpage": "web"}


def kind(m):
    return KIND.get(m.get("type", ""), "article")


# ---------------------------------------------------------------- 라이브러리 색인
def bib_entry(m):
    esc = lambda s: str(s).replace("{", "").replace("}", "")
    k = kind(m)
    entry = {"report": "techreport", "book": "book", "web": "misc"}.get(k) or (
        "misc" if m.get("type") in ("preprint", "posted-content") else "inproceedings" if "proceedings" in m.get("type", "") else "article")
    au = " and ".join("{" + a["literal"] + "}" if a.get("literal") else f"{a.get('family', '')}, {a.get('given', '')}".strip(", ")
                      for a in m.get("authors", []))
    f = {"title": "{" + esc(m["title"]) + "}", "author": au, "year": m.get("year") or "",
         ("booktitle" if entry == "inproceedings" else "journal"): m.get("venue", "") if k == "article" else "",
         "institution" if entry == "techreport" else "publisher": m.get("publisher", "") if k != "article" else "",
         "volume": m.get("volume", ""), "number": m.get("number") or m.get("issue", ""), "pages": m.get("pages", ""),
         "doi": m.get("doi", ""), "eprint": m.get("arxiv", ""), "url": m.get("url", ""),
         "urldate": m.get("accessed", "") if k in ("web", "report") else ""}
    body = ",\n".join(f"  {k_} = {{{v}}}" for k_, v in f.items() if v)
    return f"@{entry}{{{m['key']},\n{body}\n}}\n"


def rebuild():
    metas = [json.loads(p.read_text(encoding="utf-8")) for p in sorted(PAPERS.glob("*/meta.json"))]
    idx = [{k: m.get(k) for k in ("key", "title", "year", "venue", "doi", "arxiv", "added")} |
           {"authors": "; ".join(fam(a) for a in m.get("authors", [])), "type": kind(m),
            "has_summary": (PAPERS / m["key"] / "summary.md").exists(),
            "has_text": (PAPERS / m["key"] / "text.md").exists(),
            "figures": len(json.loads((PAPERS / m["key"] / "figures.json").read_text(encoding="utf-8")))
            if (PAPERS / m["key"] / "figures.json").exists() else 0} for m in metas]
    (LIB / "library.json").write_text(json.dumps(idx, ensure_ascii=False, indent=1), encoding="utf-8")
    (LIB / "library.bib").write_text("\n".join(bib_entry(m) for m in metas), encoding="utf-8")
    return metas


def load_meta(key):
    p = PAPERS / key / "meta.json"
    return json.loads(p.read_text(encoding="utf-8")) if p.exists() else None


# ---------------------------------------------------------------- 명령
def cmd_add(a):
    PAPERS.mkdir(parents=True, exist_ok=True)
    note = ""
    if a.key and not load_meta(a.key):  # 새 항목을 원하는 citekey로 (예: STEPI2025혁신)
        meta, local_pdf = resolve(a.source)
        key = a.key
    elif a.key:  # 서지만 등록된 항목에 PDF를 직접 붙이기
        old = load_meta(a.key) or sys.exit(f"없는 citekey: {a.key}")
        src = Path(a.source)
        if not src.exists():
            if not a.source.lower().startswith("http"):
                sys.exit(f"PDF 파일이 없음: {a.source}")
            src = LIB / "_download.pdf"
            download(a.source, src)
        meta, local_pdf, key = old, src, a.key
    else:
        meta, local_pdf = resolve(a.source)
        key = find_existing(meta)
        if key:  # 기존 서지(출판사·Crossref)를 우선하고 빈 칸만 새 값으로 채움
            old = load_meta(key)
            meta = {**meta, **{k: v for k, v in old.items() if v}}
        else:
            key = make_key(meta)
            if local_pdf and meta.get("source") == "pdf":
                note = ("서지 정보를 찾지 못해 PDF 제목으로만 등록함. 이미 등록한 논문의 PDF라면 "
                        "이 폴더를 지우고 --key <citekey>로 다시 추가")
    d = PAPERS / key
    d.mkdir(exist_ok=True)
    meta.update(key=key, added=meta.get("added") or datetime.date.today().isoformat())
    web_text = meta.pop("_text", None)
    if web_text is not None:  # 웹페이지: 본문 텍스트만 저장
        (d / "text.md").write_text(f"<!-- source: {meta['url']} (accessed {meta['accessed']}) -->\n{web_text}\n", encoding="utf-8")
    pdf = d / "paper.pdf"
    if local_pdf:
        if Path(local_pdf).resolve() != pdf.resolve():
            shutil.copyfile(local_pdf, pdf)
        if Path(local_pdf).name == "_download.pdf":
            Path(local_pdf).unlink()
    elif not pdf.exists() and meta.get("pdf_url"):
        try:
            download(meta["pdf_url"], pdf)
        except Exception as e:
            note = (f"PDF 내려받기 실패({e}) — 서지·초록만 저장. PDF를 받으면 "
                    f"'add <PDF 경로>' 또는 'add <PDF 경로> --key {key}'로 본문·그림 추출")
    elif not pdf.exists() and not (d / "text.md").exists() and web_text is None:
        note = (f"공개 PDF 없음(유료일 수 있음) — 서지·초록만 저장. PDF를 받으면 "
                f"'add <PDF 경로>' 또는 'add <PDF 경로> --key {key}'로 본문·그림 추출")
    figs = []
    if pdf.exists():
        doc = fitz.open(pdf)
        extract_text(doc, d / "text.md")
        figs = extract_figures(doc, d / "figures")
        (d / "figures.json").write_text(json.dumps(figs, ensure_ascii=False, indent=1), encoding="utf-8")
        meta["n_pages"] = len(doc)
        doc.close()
        if a.no_pdf:
            pdf.unlink()
    (d / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    rebuild()
    size = sum(f.stat().st_size for f in d.rglob("*") if f.is_file())
    print(json.dumps({"key": key, "dir": str(d), "title": meta["title"], "year": meta.get("year"),
                      "venue": meta.get("venue"), "doi": meta.get("doi"), "text": (d / "text.md").exists(),
                      "figures": [f"{f['label']} (p.{f['page']})" for f in figs], "size_kb": size // 1024,
                      "type": kind(meta), "publisher": meta.get("publisher"), "authors": [fam(x) for x in meta.get("authors", [])],
                      "note": note or ("서지가 빈약함 — 표지·판권면을 읽고 'set'으로 기관·연도·보고서 번호를 채울 것"
                                       if kind(meta) in ("report", "web") and not (meta.get("authors") and meta.get("year")) else "")},
                     ensure_ascii=False, indent=1))


def cmd_list(a):
    rows = json.loads((LIB / "library.json").read_text(encoding="utf-8")) if PAPERS.exists() and rebuild() is not None else []
    if a.pending:
        rows = [r for r in rows if not r.get("has_text")]
    for r in rows:
        body = "본문O " if r.get("has_text") else "PDF대기"
        print(f"{r['key']:32} {r['year'] or '':5} {body} {'요약O' if r['has_summary'] else '요약X'} 그림{r['figures']:<2} {r['title'][:60]}")


def cmd_search(a):
    terms = [t.lower() for t in a.terms]
    for d in sorted(PAPERS.iterdir()):
        m = load_meta(d.name)
        if not m:
            continue
        hay = {"meta": f"{m['title']} {m.get('abstract', '')}".lower()}
        for f in ("summary.md", "text.md"):
            if (d / f).exists():
                hay[f] = (d / f).read_text(encoding="utf-8").lower()
        hits = {k: sum(v.count(t) for t in terms) for k, v in hay.items() if all(t in v for t in terms)}
        if hits:
            print(f"{d.name:32} {m['title'][:60]}  ({', '.join(f'{k}:{n}' for k, n in hits.items())})")


def cmd_show(a):
    m = load_meta(a.key) or sys.exit(f"없는 citekey: {a.key}")
    d = PAPERS / a.key
    print(json.dumps({k: v for k, v in m.items() if k != "abstract"}, ensure_ascii=False, indent=1))
    print("files:", ", ".join(str(p.relative_to(d)) for p in sorted(d.rglob("*")) if p.is_file()))


FIELDS = {"type", "title", "authors", "year", "publisher", "number", "url", "date", "accessed", "short", "venue",
          "volume", "issue", "pages", "doi", "abstract", "lang"}


def cmd_set(a):
    m = load_meta(a.key) or sys.exit(f"없는 citekey: {a.key}")
    for kv in a.pairs:
        k, _, v = kv.partition("=")
        if k not in FIELDS:
            sys.exit(f"알 수 없는 필드: {k} (가능: {', '.join(sorted(FIELDS))})")
        m[k] = parse_authors(v) if k == "authors" else int(v) if k == "year" and v.isdigit() else v
    (PAPERS / a.key / "meta.json").write_text(json.dumps(m, ensure_ascii=False, indent=1), encoding="utf-8")
    rebuild()
    print(json.dumps({"key": a.key, "type": kind(m), "authors": [fam(x) for x in m.get("authors", [])],
                      "year": m.get("year"), "title": m["title"], "publisher": m.get("publisher"),
                      "number": m.get("number"), "url": m.get("url"), "apa": ref_apa(m)}, ensure_ascii=False, indent=1))


def cmd_rename(a):
    m = load_meta(a.old) or sys.exit(f"없는 citekey: {a.old}")
    if (PAPERS / a.new).exists():
        sys.exit(f"이미 있는 citekey: {a.new}")
    shutil.move(str(PAPERS / a.old), str(PAPERS / a.new))
    m["key"] = a.new
    (PAPERS / a.new / "meta.json").write_text(json.dumps(m, ensure_ascii=False, indent=1), encoding="utf-8")
    sm = PAPERS / a.new / "summary.md"
    if sm.exists():
        sm.write_text(sm.read_text(encoding="utf-8").replace(f"@{a.old}", f"@{a.new}"), encoding="utf-8")
    rebuild()
    print(f"{a.old} → {a.new} (요약 노트의 인용 키도 변경. 다른 원고에 쓴 [@{a.old}]는 직접 바꿔야 함)")


# ---------------------------------------------------------------- 인용
CITE_RE = re.compile(r"\[(@[^\[\]]+)\]")


def names_short(m):
    fs = [fam(a) for a in m.get("authors", [])]
    if not fs:
        return m.get("publisher") or m["title"][:30]
    return fs[0] if len(fs) == 1 else f"{fs[0]} & {fs[1]}" if len(fs) == 2 else f"{fs[0]} et al."


MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October",
          "November", "December"]


def fmt_date(d, style):
    """'2025-12-03' → APA '2025, December 3' / IEEE 'Dec. 3, 2025'. 형식이 다르면 그대로."""
    parts = str(d or "").split("-")
    if len(parts) != 3 or not all(x.isdigit() for x in parts):
        return d
    y, mo, dd = int(parts[0]), MONTHS[int(parts[1]) - 1], int(parts[2])
    if style == "apa":
        return f"{y}, {mo} {dd}"
    short = mo if len(mo) <= 4 else mo[:3] + "."
    return f"{short} {dd}, {y}"


def initials(given):
    return " ".join(f"{p[0]}." for p in re.split(r"[\s-]+", given) if p)


def ref_apa(m):
    au = [a["literal"] if a.get("literal") else f"{a['family']}, {initials(a['given'])}".strip(", ") for a in m.get("authors", [])]
    if len(au) > 20:
        au_s = ", ".join(au[:19]) + ", ... " + au[-1]
    else:
        au_s = au[0] if len(au) == 1 else ", ".join(au[:-1]) + ", & " + au[-1] if au else ""
    k = kind(m)
    link = f"https://doi.org/{m['doi']}" if m.get("doi") else m.get("url", "")
    if k != "article":  # 보고서·단행본·웹페이지: 제목 기울임, 발행처
        if not au_s:
            au_s = m.get("publisher", "")
        when = fmt_date(m["date"], "apa") if k == "web" and m.get("date") else (m.get("year") or "n.d.")
        lead = au_s if au_s.endswith(".") else f"{au_s}."
        out = f"{lead} ({when}). *{m['title']}*"
        if m.get("number"):
            out += f" ({m['number']})"
        out += "."
        if m.get("publisher") and m["publisher"] != au_s.rstrip("."):
            out += f" {m['publisher']}."
        if k == "web" and not m.get("date") and not m.get("year") and m.get("accessed"):
            y, _, md = fmt_date(m["accessed"], "apa").partition(", ")
            return f"{out} Retrieved {md + ', ' + y if md else y}, from {link}"
        return f"{out} {link}".strip()
    src = f"*{m['venue']}*" if m.get("venue") else ""
    if m.get("volume"):
        src += f", *{m['volume']}*" + (f"({m['issue']})" if m.get("issue") else "")
    if m.get("pages"):
        src += f", {m['pages']}"
    link = f"https://doi.org/{m['doi']}" if m.get("doi") else m.get("url", "")
    lead = au_s if au_s.endswith(".") else f"{au_s}."
    return f"{lead} ({m.get('year') or 'n.d.'}). {m['title']}. {src}. {link}".replace(" . ", " ").replace("..", ".")


def ref_ieee(m):
    au = [a["literal"] if a.get("literal") else f"{initials(a['given'])} {a['family']}".strip() for a in m.get("authors", [])]
    if not au:
        au_s = ""
    elif len(au) == 1:
        au_s = au[0]
    elif len(au) == 2:
        au_s = f"{au[0]} and {au[1]}"
    elif len(au) <= 6:
        au_s = ", ".join(au[:-1]) + ", and " + au[-1]
    else:
        au_s = au[0] + " et al."
    k = kind(m)
    if k != "article":
        who = au_s or m.get("publisher", "")
        url = f" [Online]. Available: {m['url']}" if m.get("url") and not m.get("doi") else ""
        if k == "web":
            site = ", ".join(x for x in (m.get("publisher") if m.get("publisher") != who else "",
                                         fmt_date(m.get("date"), "ieee")) if x) or str(m.get("year") or "n.d.")
            acc = f" Accessed: {fmt_date(m['accessed'], 'ieee')}." if m.get("accessed") else ""
            return f"{who + ', ' if who else ''}“{m['title']},” {site.rstrip('.')}.{acc}{url}"
        rep = f"Rep. {m['number']}, " if m.get("number") else ""
        pub = f"{m['publisher']}, " if m.get("publisher") and m["publisher"] != who else ""
        doi = f", doi: {m['doi']}." if m.get("doi") else "."
        return f"{who}, “{m['title']},” {pub}{rep}{m.get('year') or 'n.d.'}{doi}{url}"
    vol = f", vol. {m['volume']}" if m.get("volume") else ""
    no = f", no. {m['issue']}" if m.get("issue") else ""
    pp = (f", pp. {m['pages']}" if "-" in str(m["pages"]) else f", Art. no. {m['pages']}") if m.get("pages") else ""
    link = f", doi: {m['doi']}" if m.get("doi") else f", [Online]. Available: {m.get('url')}" if m.get("url") else ""
    return f"{au_s}, “{m['title']},” *{m.get('venue', '')}*{vol}{no}{pp}, {m.get('year') or 'n.d.'}{link}."


def cmd_cite(a):
    src = Path(a.draft)
    text = src.read_text(encoding="utf-8")
    order, missing = [], set()

    def parse(group):
        out = []
        for part in group.split(";"):
            part = part.strip()
            mm = re.match(r"@([\w:.\-]+)\s*(?:,\s*(.+))?$", part)
            if not mm:
                return None
            out.append((mm.group(1), (mm.group(2) or "").strip()))
        return out

    def repl(mt):
        items = parse(mt.group(1))
        if items is None:
            return mt.group(0)
        bits = []
        for key, loc in items:
            m = load_meta(key)
            if not m:
                missing.add(key)
                bits.append(f"??{key}")
                continue
            if key not in order:
                order.append(key)
            if a.style == "ieee":
                bits.append(f"{order.index(key) + 1}" + (f", {loc}" if loc else ""))
            else:
                bits.append(f"{names_short(m)}, {m.get('year') or 'n.d.'}" + (f", {loc}" if loc else ""))
        if a.style != "ieee":
            return f"({'; '.join(bits)})"
        if any(", " in b for b in bits):  # 쪽 번호가 있으면 [2, p. 7], [3]처럼 따로 묶음
            return ", ".join(f"[{b}]" for b in bits)
        return f"[{', '.join(bits)}]"

    body = CITE_RE.sub(repl, text)
    metas = {k: load_meta(k) for k in order}
    keys = order if a.style == "ieee" else sorted(order, key=lambda k: (names_short(metas[k]).lower(), metas[k].get("year") or 0))
    fmt = ref_ieee if a.style == "ieee" else ref_apa
    out = [body.rstrip(), "", f"## {a.heading}", ""]
    if a.table:  # hwpx 스킬용 표
        out += ["<!-- widths: 8,17,37,38 -->", "| 번호 | 저자(연도) | 논문·출처 | DOI·URL |", "|---|---|---|---|"]
        out += [f"| {i} | {names_short(metas[k]).replace(' et al.', ' 외')} ({metas[k].get('year') or 'n.d.'}) | "
                f"{metas[k]['title']}, {metas[k].get('venue') or metas[k].get('publisher', '')}"
                f"{' (' + metas[k]['number'] + ')' if metas[k].get('number') else ''} | {metas[k].get('doi') or metas[k].get('url', '')} |"
                for i, k in enumerate(keys, 1)]
    else:
        out += [f"{f'[{i}] ' if a.style == 'ieee' else ''}{fmt(metas[k])}" + ("" if a.style == "ieee" else "") for i, k in enumerate(keys, 1)]
        out = out[:4] + ["\n".join(out[4:]) if a.style == "ieee" else "\n\n".join(out[4:])]
    dest = Path(a.output) if a.output else src.with_name(src.stem + "_cited.md")
    dest.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(dest), "cited": len(order), "missing": sorted(missing)}, ensure_ascii=False))


# ---------------------------------------------------------------- HTML 보기
CSS = """body{max-width:860px;margin:32px auto;padding:0 16px;font:16px/1.7 'Pretendard','Malgun Gothic',sans-serif;color:#1d1d1f;background:#fff}
h1{font-size:1.5em;line-height:1.35}h2{margin-top:2em;border-bottom:1px solid #e5e5ea;padding-bottom:.2em}
.meta{color:#555;font-size:.92em;background:#f5f5f7;padding:10px 14px;border-radius:8px}
img{max-width:100%;border:1px solid #e5e5ea;border-radius:6px}em{color:#555}
.cite{font-size:.8em;color:#0a66c2;background:#eef4fb;border-radius:4px;padding:0 4px}
code{background:#f5f5f7;padding:0 4px;border-radius:4px}table{border-collapse:collapse}td,th{border:1px solid #ddd;padding:4px 8px}
@media (prefers-color-scheme:dark){body{background:#1c1c1e;color:#eee}.meta,code{background:#2c2c2e;color:#ccc}em{color:#aaa}.cite{background:#1d3550;color:#8cc4ff}}"""


def page_html(title, body):
    return f"<!doctype html><html lang='ko'><head><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'><title>{html.escape(title)}</title><style>{CSS}</style></head><body>{body}</body></html>"


def render_one(key):
    import markdown
    d, m = PAPERS / key, load_meta(key)
    src = (d / "summary.md").read_text(encoding="utf-8") if (d / "summary.md").exists() else "_요약 노트 없음_"
    src = CITE_RE.sub(lambda mt: f"<span class='cite'>{html.escape(mt.group(1))}</span>", src)
    au = ", ".join(a.get("literal") or f"{a['given']} {a['family']}".strip() for a in m.get("authors", [])) or m.get("publisher", "")
    link = f"https://doi.org/{m['doi']}" if m.get("doi") else m.get("url", "")
    head = (f"<p><a href='../../index.html'>← 라이브러리</a></p><h1>{html.escape(m['title'])}</h1>"
            f"<div class='meta'><b>{html.escape(au)}</b><br>{html.escape(str(m.get('venue', '')))} ({m.get('year') or 'n.d.'})"
            f" · <a href='{link}'>{html.escape(link)}</a><br>인용 키: <code>[@{key}]</code></div>")
    (d / "index.html").write_text(page_html(m["title"], head + markdown.markdown(src, extensions=["tables"])), encoding="utf-8")


def cmd_render(a):
    keys = [a.key] if a.key else [p.name for p in sorted(PAPERS.iterdir()) if (p / "meta.json").exists()]
    for k in keys:
        render_one(k)
    rebuild()  # summary.md가 새로 생겼을 수 있으니 목록 갱신
    rows ="".join(f"<tr><td><a href='papers/{r['key']}/index.html'>{html.escape(r['title'])}</a></td><td>{html.escape(r['authors'][:40])}</td>"
                   f"<td>{r['year'] or ''}</td><td><code>{r['key']}</code></td><td>{'✓' if r['has_summary'] else ''}</td></tr>"
                   for r in json.loads((LIB / "library.json").read_text(encoding="utf-8")))
    (LIB / "index.html").write_text(page_html("논문 라이브러리", "<h1>논문 라이브러리</h1><table><tr><th>제목</th><th>저자</th><th>연도</th><th>인용 키</th><th>요약</th></tr>"
                                              + rows + "</table>"), encoding="utf-8")
    print(f"{len(keys)}편 렌더링 → {LIB / 'index.html'}")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("add"); p.add_argument("source"); p.add_argument("--no-pdf", action="store_true")
    p.add_argument("--key", help="이미 있는 citekey면 이 PDF를 붙이고, 없으면 새 항목을 이 citekey로 만듦"); p.set_defaults(f=cmd_add)
    p = sp.add_parser("set"); p.add_argument("key"); p.add_argument("pairs", nargs="+", metavar="필드=값"); p.set_defaults(f=cmd_set)
    p = sp.add_parser("rename"); p.add_argument("old"); p.add_argument("new"); p.set_defaults(f=cmd_rename)
    p = sp.add_parser("list"); p.add_argument("--pending", action="store_true", help="PDF 대기(본문 없음)만"); p.set_defaults(f=cmd_list)
    p = sp.add_parser("search"); p.add_argument("terms", nargs="+"); p.set_defaults(f=cmd_search)
    p = sp.add_parser("show"); p.add_argument("key"); p.set_defaults(f=cmd_show)
    p = sp.add_parser("cite"); p.add_argument("draft"); p.add_argument("-o", "--output")
    p.add_argument("--style", choices=["apa", "ieee"], default="ieee", help="기본 ieee: 본문 [1], 참고문헌 번호순"); p.add_argument("--table", action="store_true")
    p.add_argument("--heading", default="참고문헌"); p.set_defaults(f=cmd_cite)
    p = sp.add_parser("render"); p.add_argument("key", nargs="?"); p.set_defaults(f=cmd_render)
    sp.add_parser("rebuild").set_defaults(f=lambda a: print(f"{len(rebuild())}편 색인"))
    a = ap.parse_args()
    a.f(a)


if __name__ == "__main__":
    main()
