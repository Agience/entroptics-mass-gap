"""The paper's figures and markup, and the figure script against the committed data.

- **The paper as a rendered document.** `research/paper/mass-gap.md` is assembled from
  `research/paper/v3/` by `build_paper.py`. Every image it embeds exists, every committed
  figure under `research/paper/figures/` is embedded, each figure is followed by its caption and the
  captions are numbered in document order within each section, no inline math is glued to a word,
  and no table row carries an unescaped pipe. Each of these fails silently in the rendered paper and
  is invisible in the markdown source.
- **The figure script.** `research/code/observer/plot_observer.py` draws the six figures
  `research/data/obs_fig_*.png` from the committed JSON in `research/data/observer/`,
  and nothing else.

A pattern that stops matching passes silently, so every scan states the number of occurrences it
expects and fails when it finds none.
"""
from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
PAPER_DIR = REPO / "research" / "paper"
PAPER = PAPER_DIR / "mass-gap.md"
DATA = REPO / "research" / "data"
#: The script that draws the committed `research/data/obs_fig_*.png`.
FIGURE_SCRIPT = REPO / "research" / "code" / "observer" / "plot_observer.py"

if not PAPER.exists():
    pytest.skip(f"{PAPER} not present (build it with research/paper/build_paper.py)",
                allow_module_level=True)

#: An image embed: `![alt](path)`.
_EMBED = re.compile(r"^!\[[^\]]*\]\(([^)]+)\)", re.M)
#: A caption opens its paragraph with `Figure s.k.`.
_CAPTION = re.compile(r"^Figure (\d+)\.(\d+)\.")


def _embedded() -> list[str]:
    """The image paths the paper embeds, relative to `research/paper/`."""
    return sorted(set(_EMBED.findall(PAPER.read_text(encoding="utf-8"))))


def test_every_embedded_figure_exists_and_every_figure_is_embedded():
    """The paper's images resolve, and no committed paper figure is orphaned.

    Both directions matter: a broken link is a missing figure in the rendered paper, and a figure
    nothing embeds is an artifact kept for no reader.
    """
    embedded = _embedded()
    assert embedded, "the paper embeds no images; the link format may have changed"
    missing = [img for img in embedded if not (PAPER_DIR / img).exists()]
    assert not missing, f"the paper embeds images that do not exist: {missing}"
    figures = sorted(p.relative_to(PAPER_DIR).as_posix() for p in (PAPER_DIR / "figures").glob("*.png"))
    orphans = sorted(set(figures) - set(embedded))
    assert not orphans, f"figures under research/paper/figures that nothing embeds: {orphans}"


def test_figures_are_captioned_and_numbered_in_document_order():
    """Each embed is followed by its caption, and Figure s.k is the k-th caption of section s.

    A renumbering is exactly when a caption keeps an old number or two captions collide, and
    nothing else would catch it: every figure file still exists and every embed still resolves.
    """
    lines = PAPER.read_text(encoding="utf-8").split(chr(10))
    caps = [(i, int(m.group(1)), int(m.group(2)))
            for i, l in enumerate(lines) for m in [_CAPTION.match(l)] if m]
    assert caps, "the paper has no figure captions"
    assert len(caps) == len(_embedded()), (
        f"the paper has {len(caps)} figure captions and embeds {len(_embedded())} images; a figure "
        "is uncaptioned or a caption lost its figure")
    seen: dict[int, int] = {}
    for i, s, k in caps:
        assert k == seen.get(s, 0) + 1, f"Figure {s}.{k} at line {i+1} is out of sequence"
        seen[s] = k
        window = lines[max(0, i - 3):i]
        assert any(_EMBED.match(l) for l in window), \
            f"Figure {s}.{k}'s caption at line {i+1} does not follow an image embed"
    sections = [s for _, s, _ in caps]
    assert sections == sorted(sections), f"figure captions are out of section order: {sections}"


def test_the_caption_pattern_reads_the_papers_form():
    """Positive control: the caption pattern matches `Figure s.k.` at a line start, and not prose."""
    assert _CAPTION.match("Figure 5.2. The proved widths").groups() == ("5", "2")
    assert _CAPTION.match("as Figure 5.2 shows") is None


def test_the_figure_script_draws_exactly_the_committed_figures(tmp_path):
    """`plot_observer.py` runs on the committed data and writes exactly `research/data/obs_fig_*.png`.

    A figure is drawn from files under `research/data/observer/`, so changing one of them breaks the
    drawing silently until someone regenerates. Running the script here turns that into a failing
    test. The committed figures are restored afterwards, and a file the run created is removed.
    """
    import shutil
    import subprocess
    import sys

    before = set(DATA.glob("*.png"))
    targets = {p.resolve() for p in DATA.glob("obs_fig_*.png")}
    assert targets, "no committed research/data/obs_fig_*.png"
    backup = tmp_path / "backup"
    backup.mkdir()
    for p in before:
        shutil.copy2(p, backup / p.name)
    written = set()
    try:
        r = subprocess.run([sys.executable, str(FIGURE_SCRIPT)], cwd=tmp_path,
                           capture_output=True, text=True, timeout=300)
        # DERIVED: `0` is the process exit status for success, not a magnitude.
        assert r.returncode == 0, (f"{FIGURE_SCRIPT.name} failed:\n{r.stdout[-2000:]}\n"
                                   f"{r.stderr[-2000:]}")
        written = {Path(line.split("wrote ", 1)[1].strip()).resolve()
                   for line in r.stdout.splitlines() if line.startswith("wrote ")}
        assert written, f"{FIGURE_SCRIPT.name} reported writing no figure"
        missing = sorted(p.name for p in targets if p not in written)
        assert not missing, f"{FIGURE_SCRIPT.name} does not draw these committed figures: {missing}"
        extra = sorted(str(p) for p in written if p not in targets)
        assert not extra, f"{FIGURE_SCRIPT.name} draws figures that are not committed: {extra}"
    finally:
        for p in before:
            shutil.copy2(backup / p.name, p)
        for p in written:
            if p not in {q.resolve() for q in before} and p.exists():
                p.unlink()


def _without_display_math(text: str) -> str:
    """`text` with every `$$...$$` span blanked, newlines kept so line numbers do not move.

    Display math is delimited by a doubled `$`, which a parity scan over single delimiters reads
    as an opening and a closing `$` glued together, so the spans are removed before that scan.
    """
    return re.sub(r"\$\$.*?\$\$", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)


def test_no_math_delimiter_is_glued_to_a_word():
    r"""No inline-math `$` sits against a word character, which stops it rendering.

    Markdown math needs the delimiters separated from surrounding words. Where they are not, the
    renderer does not just show the source: `closed$+$bounded $\Rightarrow$ compact` comes out as
    "closed$+ => compact" with the word *bounded* swallowed, and `spatial$\times$temporal` prints
    its LaTeX literally.

    Display math (`$$...$$`) is blanked first; parity across what remains decides which single
    delimiters open and which close, so this does not guess.
    """
    raw = PAPER.read_text(encoding="utf-8")
    D, BS = chr(36), chr(92)
    # DERIVED: a parity test -- every `$$` that opens a span has one that closes it.
    assert raw.count(D + D) % 2 == 0, "the paper has an unterminated $$ display-math span"
    text = _without_display_math(raw)
    assert D + D not in text, "a $$ survived the display-math blanking; a span is malformed"
    pos = [i for i in range(len(text)) if text[i] == D and (i == 0 or text[i - 1] != BS)]
    # DERIVED: the paper writes its mathematics inline, so a scan that finds no delimiter is
    # reading the wrong file or a blanked one.
    assert pos, "the paper has no inline math; this test is looking at the wrong file"
    assert len(pos) % 2 == 0, \
        f"the paper has an odd number of unescaped {D} ({len(pos)}); a math span is unterminated"

    bad = []
    for k, p in enumerate(pos):
        prev = text[p - 1] if p else " "
        nxt = text[p + 1] if p + 1 < len(text) else " "
        opening = (k % 2 == 0)
        if (opening and (prev.isalnum() or prev in ")]")) or (not opening and nxt.isalnum()):
            line = text[:p].count(chr(10)) + 1
            ctx = " ".join(text[max(0, p - 40):p + 45].split())
            bad.append(f"line {line}: ...{ctx}...")
    assert not bad, ("inline math is glued to a word and will not render:\n  " + "\n  ".join(bad))


def test_the_display_math_blanking_keeps_inline_math():
    """Positive control: blanking `$$` spans leaves inline delimiters and line numbers in place."""
    src = "a $x$ b\n$$y=\n1$$\nc $z$ d"
    out = _without_display_math(src)
    # DERIVED: the planted source carries two inline spans, so four single delimiters.
    assert out.count("$") == 4, f"inline delimiters were lost or display ones kept: {out!r}"
    assert out.count("\n") == src.count("\n"), "blanking moved the line numbers"
    assert len(out) == len(src), "blanking changed the character positions"


def test_no_table_row_has_an_unescaped_pipe():
    r"""Every markdown table row has the column count its block uses.

    A bare `|` inside a cell is read as a separator, so the row gains cells and the renderer drops
    the surplus -- content vanishes from the rendered paper while the markdown still reads correctly.
    LaTeX norms written `\|C(\tau)\|` inside a table are already the markdown escape for a literal
    pipe, so this counts separators rather than pipes.
    """
    import collections

    lines = PAPER.read_text(encoding="utf-8").split(chr(10))
    BS = chr(92)

    def cells(line: str) -> int:
        """Separator count, ignoring backslash-escaped pipes."""
        n, i = 0, 0
        while i < len(line):
            if line[i] == "|" and (i == 0 or line[i - 1] != BS):
                n += 1
            i += 1
        return n

    blocks, cur = [], []
    for i, l in enumerate(lines, 1):
        if l.lstrip().startswith("|"):
            cur.append((i, l))
        else:
            if cur:
                blocks.append(cur)
            cur = []
    if cur:
        blocks.append(cur)
    assert blocks, "the paper has no markdown tables; this test is looking at the wrong file"

    problems = []
    for b in blocks:
        counts = collections.Counter(cells(l) for _, l in b)
        normal = counts.most_common(1)[0][0]
        for i, l in b:
            n = cells(l)
            if n != normal:
                problems.append(f"line {i}: {n} separators where the block uses {normal} "
                                f"-- an unescaped '|' in a cell: {' '.join(l.split())[:90]}...")
    assert not problems, "table rows will lose cells when rendered:\n  " + "\n  ".join(problems)



def test_the_unfolded_cap_is_never_quoted_as_this_one():
    """`2*pi*sqrt(T/(1-T))` may appear only where it is named as the UNFOLDED-shape constant.

    The criterion reads `rho(d) = lam^circLag d`; `11.1760` belongs to the unfolded `rho(d) =
    lam^d`, equivalently to the periodic `cosh` correlator and to the free-field structure-factor
    inversion. Both live on the same circle -- what separates them is the minimum-image fold in
    `rho`, which contributes `coth(a pi/2) > 1` -- so naming either one after a geometry is what
    makes them confusable. They agree to better than two percent, closer than any simulated
    aperture is to its own limit, so a passage that attaches one formula to the other's numbers
    reads as correct.

    The distinction is maintained here: any file under `research/` carrying `11.176` must also say
    `unfolded` (or `lam^d`, or `cosh`, or give the closed form) within the same paragraph.
    """
    root = REPO / "research"
    # `11.176` catches both the 4- and the 7-decimal spelling, and the notion of "named" covers the
    # closed form and the half-line name as well as the tag words.
    digits = "11.176"
    offenders = []
    for path in list(root.rglob("*.lean")) + list(root.rglob("*.md")) + list(root.rglob("*.py")):
        if ".lake" in path.parts or "__pycache__" in path.parts:
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        # also catch it written as a formula rather than as digits
        for para in re.split(r"\n\s*\n", text):
            has_digits = digits in para
            has_formula = bool(re.search(r"sqrt\s*\{?\s*3\^\{?-?1/4", para)
                               or re.search(r"\\sqrt\{\\tfrac\{3\^\{-1/4\}", para)
                               or ("2\u03c0" in para and "\u221a(3^{\u22121/4}" in para))
            if not (has_digits or has_formula):
                continue
            low = para.lower()
            # Named by a tag word, or by the closed form the number is, or by calling it the
            # half-line constant. `2π/√(3^{1/4}−1)` and `2π√(3^{−1/4}/(1−3^{−1/4}))` are the same
            # value written two ways; a paragraph carrying either has said which constant it means
            # more precisely than any tag word does.
            # Whitespace- and minus-sign-tolerant: the tree writes both `3^{1/4}−1` and
            # `3^{1/4} − 1`, with U+2212 as often as ASCII hyphen.
            named_by_formula = bool(
                re.search(r"3\^\{[-−]?1/4\}\s*[-−]\s*1", para)
                or re.search(r"3\^\{[-−]1/4\}\s*/\s*\(\s*1\s*[-−]\s*3\^\{[-−]1/4\}",
                             para))
            # `structure-factor mass` says the number is a mass rather than an aperture cap, which
            # is exactly the confusion this test exists to prevent. The criterion's own constant is
            # 10.98875 and is never a mass.
            if any(tag in low for tag in ("unfolded", "lam^d", "λ^d", "cosh", "half-line",
                                          "structure-factor mass")):
                continue
            if named_by_formula:
                continue
            offenders.append(f"{path.relative_to(REPO)}: {para.strip()[:110]}")

    assert not offenders, (
        "the unfolded-shape cap constant appears without being named as such -- it is not the "
        "constant this criterion carries (10.98875):\n  " + "\n  ".join(offenders))
