"""Assemble the mass-gap paper into one Markdown file, an HTML page, and a two-column LaTeX source and PDF.

    python research/paper/build_paper.py            # mass-gap.md, .html, .tex and .pdf, from research/paper/v3/
    python research/paper/build_paper.py v3         # the same, naming the source directory
    python research/paper/build_paper.py --no-pdf   # Markdown and HTML only
    python research/paper/build_paper.py --check    # also dump the rendered HTML DOM and report math errors
    python research/paper/build_paper.py companion --name openai-route   # the companion paper

The sections are `SRC/NN-name.md` (two digits, one dot), concatenated in order,
where SRC is the source directory given as the first argument (relative to
research/paper/ or absolute; default `v3`); companion files such as `NN-name.lean-map.md` are not part of the paper.
LaTeX math (`$...$`, `$$...$$`) is replaced by placeholders before the Markdown
conversion and restored afterwards, so Markdown never sees it; KaTeX 0.16.9
renders it in the HTML page (loaded from its CDN). `--check` loads the page in a headless
Chromium-family browser (Edge, Chrome or Chromium, found on PATH or at Edge's Windows location; set
EDGE to choose one) and reports any formula KaTeX could not render.

The two-column `mass-gap.tex` and `mass-gap.pdf` are typeset from `mass-gap.md` by the shared
pipeline in `typeset/` (pandoc 3.x and tectonic; see `typeset/build_paper.py` for how to point at
them). The three files there are byte-identical copies of the canonical ones in the Entroptics
repository's `tools/typeset/`; change them there, not here.
"""

from __future__ import annotations

import argparse
import html
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import markdown

HERE = Path(__file__).resolve().parent
SECTIONS = HERE / "v3"
OUT_MD = HERE / "mass-gap.md"
OUT_HTML = HERE / "mass-gap.html"
TYPESET = HERE / "typeset" / "build_paper.py"
# The browser for --check: the EDGE environment variable, then a Chromium-family browser on PATH,
# then the default Windows install of Edge under %ProgramFiles(x86)%.
EDGE = Path(os.environ.get("EDGE")
            or next((p for p in map(shutil.which, ("msedge", "microsoft-edge", "google-chrome",
                                                  "chromium", "chromium-browser")) if p), None)
            or Path(os.environ.get("ProgramFiles(x86)", "")) / "Microsoft" / "Edge" / "Application"
            / "msedge.exe")
LICENCE = "Text CC BY 4.0; code Apache-2.0"
KATEX = "https://cdn.jsdelivr.net/npm/katex@0.16.9/dist"


def section_files(src: Path = SECTIONS) -> list[Path]:
    # DERIVED: `1` is the one dot of the section naming rule `NN-name.md`; companions carry two.
    files = [p for p in sorted(src.glob("[0-9][0-9]-*.md")) if p.name.count(".") == 1]
    if not files or files[0].name != "00-front.md":
        sys.exit(f"{src / '00-front.md'} not found")
    return files


def relink(text: str) -> str:
    """Image links written from a source directory one level below research/paper/, re-rooted there."""
    return text.replace("](../figures/", "](figures/").replace("](../../data/", "](../data/")


def read(p: Path) -> str:
    return p.read_text(encoding="utf-8").replace("\r\n", "\n")


# --- front matter -----------------------------------------------------------

DATE = re.compile(r"\d{4}-\d{2}-\d{2}")


def parse_front(text: str) -> dict:
    """The title block of 00-front.md: everything before the first `## ` heading.

    Recognized lines: the title (`# `), an optional subtitle (`### `), the author line, the ORCID
    line, the line carrying the date (alone, or inside a status line such as `*Pre-print. DATE.*`),
    an optional licence line, `---` rules, and an optional block quote, which is printed between
    the title block and the abstract.
    """
    lines = text.strip().split("\n")
    if not lines[0].startswith("# "):
        sys.exit("00-front.md must start with the title")
    title = lines[0][2:].strip()
    head, rest, quote = [], [], []
    for i, ln in enumerate(lines[1:], 1):
        if ln.startswith("## "):
            rest = lines[i:]
            break
        if ln.startswith(">"):
            quote.append(ln)
        elif ln.strip() and ln.strip() != "---":
            head.append(ln.strip())
    blocks: dict[str, str] = {}
    name = None
    for ln in rest:
        if ln.startswith("## "):
            name = ln[3:].strip()
            blocks[name] = ""
        elif name is not None:
            blocks[name] += ln + "\n"
    subtitle = next((h[4:].strip() for h in head if h.startswith("### ")), "")
    orcid = next((h for h in head if h.startswith("ORCID")), "")
    dline = next((h for h in head if DATE.search(h)), "")
    date = DATE.search(dline)[0] if dline else ""
    status = re.sub(r"[\s.]+$", "", dline.strip("*").replace(date, "")) if dline else ""
    licence = next((h for h in head if h.rstrip(".") == LICENCE), "")
    author = next((h for h in head if not h.startswith("### ") and h not in (orcid, dline, licence)), "")
    return {"title": title, "subtitle": subtitle, "author": author, "orcid": orcid, "date": date,
            "status": status, "quote": "\n".join(quote).strip(),
            "blocks": {k: v.strip() for k, v in blocks.items()}}


def front_markdown(text: str, front: dict) -> str:
    """00-front.md with the licence line added after the date, unless it carries one."""
    if LICENCE in text:
        return text
    date = front["date"]
    if date and date in text:
        line = next(ln for ln in text.split("\n") if date in ln)
        return text.replace(line, f"{line}\n\n{LICENCE}", 1)
    return text.rstrip() + f"\n\n{LICENCE}\n"


# --- math protection --------------------------------------------------------

TOKEN = re.compile(
    r"(?P<fence>^(?P<fq>```|~~~)[^\n]*\n.*?^(?P=fq)[ \t]*$)"
    r"|(?P<code>(?P<bt>`+).+?(?P=bt))"
    r"|(?P<dmath>\$\$.+?\$\$)"
    r"|(?P<imath>\$(?!\$)(?:\\.|[^$\\])+?\$)",
    re.S | re.M,
)


def protect(text: str, store: list[str]) -> str:
    def sub(m: re.Match) -> str:
        if m.group("fence") or m.group("code"):
            return m.group(0)
        s = m.group(0)
        line_start = text.rfind("\n", 0, m.start()) + 1
        if text[line_start:m.start()].lstrip().startswith(">"):
            # math inside a block quote: the quote markers of its continuation lines are not math
            s = re.sub(r"\n[ \t]*>[ \t]?", "\n", s)
        if "\n\n" in s:
            print(f"warning: math spans a blank line: {s[:60]!r}", file=sys.stderr)
        store.append(s)
        kind = "D" if m.group("dmath") else "I"
        return f"KXMATH{kind}{len(store) - 1:05d}X"
    return TOKEN.sub(sub, text)


def restore(h: str, store: list[str]) -> str:
    def sub(m: re.Match) -> str:
        s = store[int(m.group(2))]
        if m.group(1) == "D":
            s = "$$" + " ".join(s[2:-2].split("\n")).strip() + "$$"
        return html.escape(s, quote=False)
    return re.sub(r"KXMATH([DI])(\d{5})X", sub, h)


# --- Markdown to HTML -------------------------------------------------------

LIST_ITEM = re.compile(r"^(?:[-*+]|\d+\.) ")


def normalize_lists(text: str) -> str:
    """Read lists the way the sections are written (CommonMark).

    Python-Markdown wants four-space continuation and a blank line before a
    list; the sections indent continuations by two spaces and may start a
    list, or a new item after an indented block, without a blank line.
    """
    out: list[str] = []
    in_item = in_fence = False
    for ln in text.split("\n"):
        if re.match(r"^\s*(```|~~~)", ln):
            in_fence = not in_fence
        if in_fence or ln.startswith("```") or ln.startswith("~~~"):
            if in_item and ln.startswith("  ") and not ln.startswith("    "):
                ln = "  " + ln
            out.append(ln)
            continue
        if LIST_ITEM.match(ln):
            prev = out[-1] if out else ""
            if prev.strip() and not LIST_ITEM.match(prev):
                out.append("")
            in_item = True
        elif in_item and ln.startswith("  ") and not ln.startswith("    "):
            ln = "  " + ln
        elif ln.strip() and not ln.startswith(" "):
            in_item = False
        out.append(ln)
    return "\n".join(out)


def md_to_html(text: str, store: list[str], toc: bool = False) -> tuple[str, str]:
    md = markdown.Markdown(
        extensions=["fenced_code", "tables", "footnotes", "toc", "nl2br", "sane_lists"],
        extension_configs={"toc": {"toc_depth": "1", "title": "Contents", "permalink": False}},
    )
    body = md.convert(normalize_lists(protect(text, store)))
    # a soft line break next to display math is spacing the display already gives
    body = re.sub(r"<br />\s*(KXMATHD\d{5}X)", r"\1", body)
    body = re.sub(r"(KXMATHD\d{5}X)\s*<br />", r"\1", body)
    return body, (md.toc if toc else "")


def figures(h: str) -> str:
    pat = re.compile(
        r'<p><img alt="(?P<alt>[^"]*)" src="(?P<src>[^"]+)"\s*/?></p>\s*'
        r"<p>(?P<cap>Figure \d+\.\d+\..*?)</p>",
        re.S,
    )
    return pat.sub(
        lambda m: (f'<figure><img alt="{m["alt"]}" src="{m["src"]}" />'
                   f'<figcaption>{m["cap"]}</figcaption></figure>'),
        h,
    )


def citations(h: str, keys: list[str]) -> str:
    if not keys:
        return h
    alt = "|".join(re.escape(k) for k in sorted(keys, key=len, reverse=True))
    cite = re.compile(r"\[(" + alt + r")((?:,[^\]<]*)?)\]")
    parts = re.split(r"(<pre.*?</pre>|<code.*?</code>)", h, flags=re.S)
    for i in range(0, len(parts), 2):
        parts[i] = cite.sub(lambda m: f'<a class="cite" href="#ref-{m[1]}">[{m[1]}{m[2]}]</a>', parts[i])
    return "".join(parts)


def reference_anchors(h: str) -> tuple[str, list[str]]:
    keys: list[str] = []

    def sub(m: re.Match) -> str:
        keys.append(m[1])
        return f'<p class="ref" id="ref-{m[1]}"><span class="refkey">[{m[1]}]</span>'
    return re.sub(r"<p>\[([A-Za-z][A-Za-z0-9\-]*)\]", sub, h), keys


CSS = r"""
@page { size: A4; margin: 2.2cm; }
:root { --ink: #111; --rule: #888; --soft: #f4f4f4; --link: #1a3d7c; }
html { background: #fff; }
body { background: #fff; color: var(--ink); margin: 0 auto; max-width: 16.6cm;
  font-family: "STIX Two Text", "Cambria", "Times New Roman", Times, serif;
  font-size: 10.5pt; line-height: 1.42; text-align: justify; hyphens: auto; }
@media screen { body { padding: 2cm 1.2cm; } }
a { color: var(--link); text-decoration: none; }
a.cite { color: inherit; }
h1, h2, h3, h4 { font-weight: 600; text-align: left; line-height: 1.25;
  break-after: avoid; page-break-after: avoid; hyphens: none; }
h1 { font-size: 15pt; margin: 1.6em 0 0.6em; }
h2 { font-size: 12pt; margin: 1.3em 0 0.4em; }
h3 { font-size: 10.5pt; margin: 1em 0 0.3em; }
p { margin: 0 0 0.55em; orphans: 3; widows: 3; }
.titleblock { text-align: center; margin: 0 0 1.4em; }
.titleblock h1.title { font-size: 17pt; margin: 0 0 0.9em; text-align: center; }
.titleblock p { margin: 0.15em 0; text-align: center; }
.titleblock .author { font-size: 12pt; }
.titleblock .licence { font-size: 9pt; color: #444; margin-top: 0.5em; }
.titleblock .subtitle { font-size: 11.5pt; font-style: italic; margin: -0.4em 0 0.9em; }
.preamble { margin: 0 1.2cm 1em; font-size: 9.4pt; }
.preamble blockquote { border-left: 0; padding-left: 0; margin: 0; }
.abstract { margin: 0 1.2cm 1em; font-size: 9.8pt; }
.abstract h2 { font-size: 10.5pt; text-align: center; margin: 0.8em 0 0.3em; }
.meta { margin: 0 1.2cm 0.4em; font-size: 9.3pt; text-align: left; }
.meta .label { font-variant: small-caps; letter-spacing: 0.03em; }
nav.toc { margin: 1.2em 0 1.6em; break-inside: avoid; }
nav.toc .toctitle { font-size: 12pt; font-weight: 600; margin-bottom: 0.4em; }
nav.toc ul { list-style: none; padding-left: 0; margin: 0; columns: 2; column-gap: 1.5cm; }
nav.toc li { margin: 0.12em 0; break-inside: avoid; }
main > h1:first-child { break-before: page; page-break-before: always; }
blockquote { margin: 0.7em 0; padding: 0.15em 0 0.15em 0.9em; border-left: 1.5px solid var(--rule); }
blockquote p { margin: 0.2em 0; }
figure { margin: 1em 0 1.2em; text-align: center; break-inside: avoid; page-break-inside: avoid; }
figure img { display: block; margin: 0 auto; width: auto; max-width: 100%; max-height: 10cm; height: auto; }
figcaption { font-size: 9pt; text-align: justify; margin-top: 0.4em; line-height: 1.35; }
img { max-width: 100%; }
table { border-collapse: collapse; margin: 0.8em auto; font-size: 8.8pt; line-height: 1.3;
  border-top: 1.2px solid var(--ink); border-bottom: 1.2px solid var(--ink); text-align: left;
  max-width: 100%; }
thead th { border-bottom: 0.6px solid var(--ink); font-weight: 600; }
th, td { padding: 0.22em 0.5em; vertical-align: top; }
tbody tr + tr td { border-top: 0.4px solid #d4d4d4; }
tr { break-inside: avoid; page-break-inside: avoid; }
td.label { white-space: nowrap; }
td code, th code { overflow-wrap: anywhere; word-break: break-word; }
code { font-family: "Cascadia Mono", Consolas, "DejaVu Sans Mono", monospace; font-size: 0.86em; }
pre { background: var(--soft); padding: 0.5em 0.7em; font-size: 8.4pt; line-height: 1.3;
  white-space: pre-wrap; overflow-wrap: anywhere; break-inside: avoid; text-align: left; }
pre code { font-size: 1em; }
ul, ol { margin: 0.3em 0 0.6em; padding-left: 1.6em; }
li { margin: 0.12em 0; }
.katex { font-size: 1.04em; }
.katex-display { margin: 0.55em 0; }
.katex-display > .katex { max-width: 100%; }
p.ref { padding-left: 1.6em; text-indent: -1.6em; text-align: left; font-size: 9.6pt; margin-bottom: 0.4em;
  overflow-wrap: anywhere; }
.refkey { font-weight: 600; }
hr { border: 0; border-top: 0.6px solid var(--rule); margin: 1.2em 0; }
"""

KATEX_HEAD = f"""<link rel="stylesheet" href="{KATEX}/katex.min.css">
<script defer src="{KATEX}/katex.min.js"></script>
<script defer src="{KATEX}/contrib/auto-render.min.js"></script>
<script>
document.addEventListener("DOMContentLoaded", function () {{
  renderMathInElement(document.body, {{
    delimiters: [
      {{left: "$$", right: "$$", display: true}},
      {{left: "$", right: "$", display: false}}
    ],
    throwOnError: false,
    strict: "ignore"
  }});
  // a display wider than the text column is scaled down to fit it
  document.fonts.ready.then(function () {{
    document.querySelectorAll(".katex-display").forEach(function (d) {{
      var k = d.firstElementChild, w = d.clientWidth, s = k ? k.scrollWidth : 0;
      if (w > 0 && s > w) {{
        d.style.fontSize = (100 * w / s * 0.98).toFixed(1) + "%";
        d.setAttribute("data-scaled", (w / s).toFixed(2));
      }}
    }});
    document.body.setAttribute("data-math", "done");
  }});
}});
</script>"""


def build_html(files: list[Path]) -> tuple[str, str]:
    front_text = read(files[0])
    front = parse_front(front_text)
    store: list[str] = []

    # the Markdown document
    parts = [front_markdown(front_text, front).rstrip()]
    for p in files[1:]:
        parts.append(read(p).rstrip())
    doc_md = relink("\n\n".join(parts)) + "\n"

    # front matter
    def inline(s: str) -> str:
        h, _ = md_to_html(s, store)
        return re.sub(r"^<p>(.*)</p>$", r"\1", h.strip(), flags=re.S)

    title = inline(front["title"])
    orcid = front["orcid"]
    m = re.match(r"ORCID \[([^\]]+)\]\(([^)]+)\)", orcid)
    orcid_html = (f'ORCID <a href="{m[2]}">{m[1]}</a>' if m else html.escape(orcid))
    fb = front["blocks"]
    abstract = md_to_html(fb.get("Abstract", ""), store)[0]
    keywords = inline(fb.get("Keywords", ""))
    msc_name = next((k for k in fb if k.startswith("Mathematics Subject Classification")), None)
    msc = inline(fb[msc_name]) if msc_name else ""
    msc_label = msc_name.replace("Mathematics Subject Classification", "MSC") if msc_name else ""
    subtitle = f'<p class="subtitle">{inline(front["subtitle"])}</p>\n' if front["subtitle"] else ""
    date = f'{html.escape(front["status"])}. {html.escape(front["date"])}' if front["status"] else html.escape(front["date"])
    quote = f'<section class="preamble">{md_to_html(front["quote"], store)[0]}</section>\n' if front["quote"] else ""
    front_html = f"""<header class="titleblock">
<h1 class="title">{title}</h1>
{subtitle}<p class="author">{inline(front["author"])}</p>
<p class="orcid">{orcid_html}</p>
<p class="date">{date}</p>
<p class="licence">{html.escape(LICENCE)}</p>
</header>
{quote}<section class="abstract"><h2>Abstract</h2>
{abstract}
</section>
<p class="meta"><span class="label">Keywords.</span> {keywords}</p>
<p class="meta"><span class="label">{html.escape(msc_label)}.</span> {msc}</p>
"""

    # body
    body_md = relink("\n\n".join(read(p).rstrip() for p in files[1:]))
    body, toc = md_to_html(body_md, store, toc=True)
    body = figures(body)
    # a table cell holding one label ([T x.y] or Theorem x.y) is not broken across lines
    body = re.sub(r"<td>(\[T \d+\.\d+\]|Theorem \d+\.\d+)</td>", r'<td class="label">\1</td>', body)
    split = re.search(r'<h1[^>]*>\s*\d+\.\s*References\s*</h1>', body)
    keys: list[str] = []
    if split:
        refs, keys = reference_anchors(body[split.start():])
        body = citations(body[:split.start()], keys) + refs
        front_html = citations(front_html, keys)
    toc = toc.replace('<div class="toc">', '<nav class="toc">').replace("</div>", "</nav>")
    toc = toc.replace('<span class="toctitle">', '<div class="toctitle">').replace("</span>", "</div>", 1)

    page_title = re.sub(r"\$([^$]*)\$", r"\1", front["title"]).split(":")[0].strip()
    out = f"""<!DOCTYPE html>
<html lang="en-CA">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(page_title)}</title>
<meta name="author" content="{html.escape(front["author"].split(",")[0].replace("`", ""))}">
{KATEX_HEAD}
<style>{CSS}</style>
</head>
<body>
{front_html}
{toc}
<main>
{body}
</main>
</body>
</html>
"""
    out = restore(out, store)
    if "KXMATH" in out:
        sys.exit("a math placeholder was not restored")
    return doc_md, out


# --- printing and checking --------------------------------------------------

# CHOSEN: 180 s is a wall-clock cap on one headless Edge call; a print takes seconds, so the cap
# only stops a hung browser and changes no output.
def edge(args: list[str], timeout: int = 180) -> subprocess.CompletedProcess:
    if not EDGE.exists():
        sys.exit(f"no headless browser found (looked for Edge, Chrome, Chromium; last tried {EDGE}); "
                 "set EDGE to the browser's executable")
    with tempfile.TemporaryDirectory(prefix="edge-paper-") as prof:
        cmd = [str(EDGE), "--headless", "--disable-gpu", "--no-pdf-header-footer",
               "--virtual-time-budget=20000", f"--user-data-dir={prof}", *args, OUT_HTML.as_uri()]
        return subprocess.run(cmd, capture_output=True, timeout=timeout,
                              encoding="utf-8", errors="replace")


def typeset() -> int:
    """mass-gap.tex and mass-gap.pdf from mass-gap.md, by the shared two-column pipeline."""
    return subprocess.run([sys.executable, str(TYPESET), str(OUT_MD)]).returncode


def check_render() -> int:
    dom = edge(["--dump-dom"]).stdout
    if 'data-math="done"' not in dom:
        print("check: KaTeX did not run (no network, or the CDN did not load)")
        return 1
    errors = re.findall(r'<span[^>]*class="katex-error"[^>]*>', dom)
    text = re.sub(r"<(pre|code|script|style|annotation|title)\b.*?</\1>", "", dom, flags=re.S)
    text = re.sub(r"<[^>]+>", " ", text)
    raw = [m.group(0) for m in re.finditer(r".{0,30}(\$|\\frac|\\beta).{0,30}", html.unescape(text))]
    formulas = dom.count('class="katex"')
    scaled = re.findall(r'data-scaled="([\d.]+)"', dom)
    if scaled:
        print(f"check: {len(scaled)} wide displays scaled to fit (smallest factor {min(map(float, scaled)):.2f})")
    print(f"check: {formulas} formulas, {len(errors)} KaTeX errors, "
          f"{len(raw)} raw math fragments outside code")
    for e in errors[:20]:
        print("  error:", html.unescape(e)[:160])
    for s in raw[:20]:
        print("  raw:", s.replace("\n", " "))
    return 1 if errors or raw else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("src", nargs="?", default="v3",
                    help="source directory of NN-name.md files, relative to research/paper/ (default: v3)")
    ap.add_argument("--no-pdf", action="store_true", help="write the Markdown and HTML only (no .tex or .pdf)")
    ap.add_argument("--check", action="store_true", help="dump the rendered DOM and report math errors")
    ap.add_argument("--name", default="mass-gap",
                    help="output stem under research/paper/ (default: mass-gap; the companion uses openai-route)")
    a = ap.parse_args()
    global OUT_MD, OUT_HTML
    OUT_MD, OUT_HTML = HERE / f"{a.name}.md", HERE / f"{a.name}.html"
    src = Path(a.src)
    files = section_files(src if src.is_absolute() else HERE / src)
    doc_md, doc_html = build_html(files)
    OUT_MD.write_text(doc_md, encoding="utf-8", newline="\n")
    OUT_HTML.write_text(doc_html, encoding="utf-8", newline="\n")
    print(f"sections: {', '.join(p.stem for p in files)}")
    print(f"wrote {OUT_MD.name}, {OUT_HTML.name}")
    rc = check_render() if a.check else 0
    if not a.no_pdf:
        rc = typeset() or rc
    return rc


if __name__ == "__main__":
    sys.exit(main())
