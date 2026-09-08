"""The numbers PAPER.md quotes are the numbers the committed artifacts carry.

A table in the paper is transcribed by hand from a CSV, so it can drift from the artifact it claims
to report: a regenerated measurement moves and the prose keeps the old value, or a digit is mistyped
and nothing objects. These tests re-derive each table from its artifact and compare, so the paper and
the data cannot disagree silently.

Tables are located by their own header row rather than by line number, so editing prose around them
does not break the test. A table the paper does not contain is a failure, not a skip: the point is
that the claim is present AND correct.

Two rules these checks follow, both learned from checks that looked sound and were not:

- **Compare structure, not presence.** "Does this number appear in the paper" is close to vacuous
  here, and scoping to a passage is not enough either: two different quantities can share a value
  inside one sentence. Sec 8.7b lists the published reads (117, 196, 344) beside the variational
  ones (193, 210, 196), and Sec 8.7 states a worst-case bound in the same breath as the list it
  bounds. Read ordered lists positionally, compare `value±error` as a unit, and where a value is
  genuinely repeated across the paper use `assert_every_statement` to check every occurrence.
- **A pattern that stops matching passes silently.** Every sweep states the number of occurrences it
  expects, so a rewording that hides the statements is a failure rather than a vacuous pass.
"""
from __future__ import annotations

import csv
import math
import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
PAPER = REPO / "research" / "PAPER.md"
DATA = REPO / "research" / "data"
BS = chr(92)
TOL = 5e-4                      # the paper quotes 3-4 decimals



def assert_every_statement(text, pattern, expected, what, minimum=2):
    """Every occurrence of `pattern` in `text` states `expected`.

    A value the paper repeats cannot be checked by presence: after one copy drifts the others still
    match, so the assertion passes while the paper disagrees with itself. This compares every
    occurrence and reports the line of each that differs.

    `minimum` guards the other failure: a pattern that stops matching -- because the surrounding
    wording changed -- would find nothing and pass. Give the number of statements the paper is
    expected to carry.

    `pattern` must contain exactly one capturing group, the value.
    """
    hits = [(m.group(1), text[:m.start()].count(chr(10)) + 1)
            for m in re.finditer(pattern, text)]
    assert len(hits) >= minimum, (
        f"{what} is stated {len(hits)} times; the paper carries it at least {minimum} times, so "
        "this pattern is no longer finding the statements it checks")
    bad = [(v, ln) for v, ln in hits if v != expected]
    assert not bad, (
        f"{what} should be {expected!r}, but " +
        "; ".join(f"line {ln} states {v!r}" for v, ln in bad))


def _passage(text: str, marker: str) -> str:
    """The paragraph containing `marker`, so a claim is checked where it is made.

    Substring-matching a number against the whole paper is close to vacuous: PAPER.md quotes hundreds
    of numbers, so any three-decimal value is likely to appear somewhere in it regardless of whether
    the claim under test is still right. Scoping to the paragraph is what makes such a check
    discriminate.
    """
    n = text.count(marker)
    assert n == 1, (f"{marker!r} occurs {n} times in PAPER.md; a passage anchor must be unique or "
                    "the check silently lands on the wrong claim")
    i = text.find(marker)
    start = text.rfind(chr(10) * 2, 0, i)
    end = text.find(chr(10) * 2, i)
    block = text[(0 if start == -1 else start):(len(text) if end == -1 else end)]
    # Returned with whitespace collapsed: PAPER.md hard-wraps its prose, so a phrase the paper
    # states ("eight ensembles", "$L=12$--$20$") can be split across a newline and a plain
    # substring check would miss it -- a false negative, which is the worse direction for a test
    # whose job is to catch drift.
    return " ".join(block.split())

def _cells(line: str) -> list[str]:
    return [c.strip() for c in line.strip().strip("|").split("|")]


def _nums(cell: str) -> list[float]:
    """Numbers in a markdown cell, with LaTeX markup removed."""
    t = cell.replace("$", "")
    for tok in (BS + "pm", BS + "approx", BS + "sigma", BS + "le", BS + "ge", "**"):
        t = t.replace(tok, " ")
    out = []
    for w in t.replace("|", " ").split():
        try:
            out.append(float(w.strip("+()*^, ")))
        except ValueError:
            pass
    return out


def _tau(cell: str) -> int | None:
    """The lag named in a ``... tau=N ...`` cell, whichever way the LaTeX is written."""
    t = cell.replace("$", "").replace(BS + "tau", "tau")
    if "tau=" not in t:
        return None
    tail = t.split("tau=", 1)[1].strip()
    digits = ""
    for ch in tail:
        if not ch.isdigit():
            break
        digits += ch
    return int(digits) if digits else None


def _table_after(header_contains: list[str]) -> list[list[str]]:
    """Rows of the first markdown table whose header row contains every given substring."""
    lines = PAPER.read_text(encoding="utf-8").split("\n")
    for i, line in enumerate(lines):
        if not line.startswith("|"):
            continue
        head = _cells(line)
        if all(any(h in c for c in head) for h in header_contains):
            rows = []
            for l in lines[i + 2:]:                 # skip the |---| separator
                if not l.startswith("|"):
                    break
                rows.append(_cells(l))
            return rows
    return []


def _artifact(name: str) -> list[dict]:
    p = DATA / name
    if not p.exists():
        pytest.skip(f"{name} not present")
    with open(p, newline="") as fh:
        return list(csv.DictReader(fh))


def _variational(rows, L, beta, tol=0.25):
    """The rule PAPER Sec 8.7b states: smallest m_eff resolved to `tol` over the whole basis."""
    def f(v):
        return float(v) if v not in ("", None) else float("nan")
    cand = [(f(r["m_eff"]), f(r["m_eff_err"]), r["operator"], int(r["tau"])) for r in rows
            if int(r["L"]) == L and abs(float(r["beta"]) - beta) < 1e-9
            and r["m_eff"] not in ("", None) and r["m_eff_err"] not in ("", None)]
    cand = [c for c in cand if c[0] == c[0] and c[1] == c[1] and c[0] > 0 and c[1] / c[0] <= tol]
    return min(cand, key=lambda c: c[0]) if cand else None


def test_string_tension_table_matches_artifact():
    """Sec 8.8's per-coupling table is 8_8_dat_string_tension.csv."""
    art = {float(r["beta"]): r for r in _artifact("8_8_dat_string_tension.csv")}
    rows = _table_after(["Creutz", "established", "deviation"])
    assert rows, "Sec 8.8 string-tension table not found in PAPER.md"
    seen = 0
    for cells in rows:
        got = _nums(cells[0])
        if not got or got[0] not in art:
            continue
        beta, r, seen = got[0], art[got[0]], seen + 1
        sig = _nums(cells[1])
        assert len(sig) == 3, f"beta={beta}: expected value/stat/syst, parsed {sig}"
        for name, quoted, actual in zip(("a2sigma", "stat", "syst"), sig,
                                        (r["a2sigma_potential"], r["a2sigma_err"], r["a2sigma_syst"])):
            assert abs(quoted - float(actual)) < TOL, \
                f"beta={beta} {name}: paper {quoted} vs artifact {actual}"
        cre = _nums(cells[2])
        assert cre and abs(cre[0] - float(r["a2sigma_creutz"])) < TOL, \
            f"beta={beta} creutz: paper {cre} vs artifact {r['a2sigma_creutz']}"
    assert seen == len(art), f"paper quotes {seen} couplings, artifact carries {len(art)}"


def test_volume_table_matches_the_variational_rule():
    """Sec 8.7b's volume table is the variational rule applied to 8_7_dat_gap_correlator.csv.

    This pins the SELECTION as well as the values: the paper names the operator and lag chosen at
    each volume, so a change in the rule or in the data shows up here rather than in a stale table.
    """
    rows = _artifact("8_7_dat_gap_correlator.csv")
    table = _table_after(["variational", "selected by"])
    assert table, "Sec 8.7b volume table not found in PAPER.md"
    seen = 0
    for cells in table:
        Ls = _nums(cells[0])
        if not Ls:
            continue
        L = int(Ls[0])
        pick = _variational(rows, L, 2.30)
        assert pick is not None, f"L={L}: nothing resolved in the artifact"
        delta, err, op, tau = pick
        quoted = _nums(cells[1])
        assert len(quoted) == 2, f"L={L}: expected value and error, parsed {quoted}"
        assert abs(quoted[0] - delta) < TOL, f"L={L} Delta: paper {quoted[0]} vs {delta:.4f}"
        assert abs(quoted[1] - err) < TOL, f"L={L} error: paper {quoted[1]} vs {err:.4f}"
        mhi = _nums(cells[2])
        assert mhi and abs(mhi[0] - math.exp(-delta)) < TOL, \
            f"L={L} m_hi: paper {mhi} vs {math.exp(-delta):.4f}"
        assert ("plaquette" in cells[3]) == ("plaquette" in op), \
            f"L={L} operator: paper says {cells[3]!r}, rule selects {op}"
        assert _tau(cells[3]) == tau, \
            f"L={L} lag: paper {cells[3]!r}, rule selects tau={tau}"
        seen += 1
    assert seen >= 4, f"expected four volumes in the table, matched {seen}"


def test_exclusion_table_matches_artifacts():
    """Sec 8.7b compares the PUBLISHED Sec 8.6 read against the variational bound.

    Both sides come from committed artifacts -- the published value from
    8_7_dat_mhi_multicoupling.csv, the bound re-derived from 8_7_dat_gap_correlator.csv -- and the
    significance is recomputed rather than transcribed. The comparison must be like-for-like: a
    bound taken at one lag against a read taken at another inflates the excess, which is the error
    this test exists to prevent.
    """
    gap = _artifact("8_7_dat_gap_correlator.csv")
    published = {float(r["beta"]): (float(r["Delta"]), float(r["Delta_err"]))
                 for r in _artifact("8_7_dat_mhi_multicoupling.csv") if r["L"] == "16"}
    table = _table_after(["published", "variational bound", "excess"])
    assert table, "Sec 8.7b comparison table not found in PAPER.md"
    seen = 0
    for cells in table:
        betas = _nums(cells[0])
        if not betas or betas[0] not in published:
            continue
        beta = betas[0]
        pub, puberr = published[beta]
        var = _variational(gap, 16, beta)
        assert var is not None, f"beta={beta}: no variational bound resolvable"
        bound, berr = var[0], var[1]

        quoted_p, quoted_b = _nums(cells[1]), _nums(cells[2])
        assert abs(quoted_p[0] - pub) < TOL and abs(quoted_p[1] - puberr) < TOL, \
            f"beta={beta} published: paper {quoted_p} vs artifact {pub:.4f}+/-{puberr:.4f}"
        assert abs(quoted_b[0] - bound) < TOL and abs(quoted_b[1] - berr) < TOL, \
            f"beta={beta} bound: paper {quoted_b} vs {bound:.4f}+/-{berr:.4f}"

        excess = (pub - bound) / math.hypot(puberr, berr)
        quoted_x = _nums(cells[3])
        assert quoted_x and abs(quoted_x[0] - excess) < 0.05, \
            f"beta={beta} excess: paper {quoted_x[0]} sigma vs {excess:.2f} sigma"
        seen += 1
    assert seen >= 2, f"expected at least two couplings, matched {seen}"


def test_transfer_pencil_table_matches_artifact():
    """Sec 8.7's Table 1 is 8_7_dat_transfer_pencil.csv, by (smearing, moment order)."""
    art = {(int(r["smearing"]), int(r["n_moment"])): r
           for r in _artifact("8_7_dat_transfer_pencil.csv")}
    table = _table_after(["APE smearing", "lambda"])
    assert table, "Sec 8.7 transfer-pencil table not found in PAPER.md"
    seen = 0
    for cells in table:
        sm = _nums(cells[0])
        if not sm:
            continue
        smear = int(sm[0])
        for order, cell in zip((2, 3, 4), cells[1:4]):
            r = art.get((smear, order))
            if r is None:
                continue
            quoted = _nums(cell.replace("(", " ").replace(")", " ").replace(BS + "dagger", " "))
            assert quoted, f"smearing={smear} n={order}: no number parsed from {cell!r}"
            # Table 1 quotes three decimals where the artifact carries four, so the comparison is
            # at the precision the paper prints rather than the precision the CSV stores.
            assert abs(quoted[0] - float(r["lambda1"])) < 5e-4 + 1e-9, \
                f"smearing={smear} n={order}: paper {quoted[0]} vs artifact {r['lambda1']}"
            seen += 1
    assert seen >= 8, f"expected at least eight lambda_1 entries, matched {seen}"


def test_ksignal_table_matches_artifacts():
    """Sec 8.3's K_signal table is 8_3_dat_nobump.csv plus 8_3_dat_su3_nobump.csv.

    The paper quotes two decimals against four in the artifacts, so the comparison is at the printed
    precision. Each row must also find its (group, beta) in an artifact: a row for an ensemble that
    was never measured is the failure this catches.
    """
    art = {}
    for name in ("8_3_dat_nobump.csv", "8_3_dat_su3_nobump.csv"):
        for r in _artifact(name):
            art[(r["group"], round(float(r["beta"]), 2))] = float(r["confinement"])
    table = _table_after(["group", "lattice", "phase"])
    assert table, "Sec 8.3 K_signal table not found in PAPER.md"
    seen = 0
    for cells in table:
        group = ("su2" if "SU(2)" in cells[0] else
                 "su3" if "SU(3)" in cells[0] else
                 "u1" if "U(1)" in cells[0] else None)
        betas = _nums(cells[1])
        if group is None or not betas:
            continue
        key = (group, round(betas[0], 2))
        assert key in art, f"{key} appears in the paper but not in the artifacts"
        quoted = _nums(cells[3])
        assert quoted, f"{key}: no K_signal parsed from {cells[3]!r}"
        assert abs(quoted[0] - round(art[key], 2)) < 5e-3, \
            f"{key} K_signal: paper {quoted[0]} vs artifact {art[key]:.4f}"
        seen += 1
    assert seen >= 6, f"expected at least six rows, matched {seen}"


def _a_lambda(beta, N=2):
    """a * Lambda_lat at two loops for SU(N), beta = 2N/g^2."""
    b0 = 11 * N / (48 * math.pi ** 2)
    b1 = 34 * N ** 2 / (3 * (16 * math.pi ** 2) ** 2)
    g2 = 2.0 * N / beta
    return (b0 * g2) ** (-b1 / (2 * b0 ** 2)) * math.exp(-1.0 / (2 * b0 * g2))


def _constant_fit(vals):
    """Weighted mean and chi2/dof of (value, error) pairs against a constant."""
    w = [1.0 / e ** 2 for _, e in vals]
    m = sum(v * wi for (v, _), wi in zip(vals, w)) / sum(w)
    chi2 = sum(wi * (v - m) ** 2 for (v, _), wi in zip(vals, w)) / max(1, len(vals) - 1)
    return m, chi2


def test_scaling_claims_in_prose_match_the_artifacts():
    """The derived numbers Sec 8.8 and Sec 8.7b state in prose, recomputed from the CSVs.

    Tables are pinned elsewhere; these are the quantities the argument actually turns on -- whether
    a dimensionless ratio is constant, and by how much the two-loop prediction is missed -- and they
    live in sentences rather than cells, where nothing else would catch them drifting.
    """
    text = PAPER.read_text(encoding="utf-8")
    # Each group is checked inside the sentence that states it. Several of these values occur
    # elsewhere in PAPER.md (the 8.7b chi2/dof and one of the two-loop pulls both do), so a
    # whole-document match would pass on a paper whose claim had drifted.
    tension = _passage(text, "the two-loop ratio test gives")
    variational = _passage(text, "The published action-density read gives")

    # -- Sec 8.8: sqrt(sigma)/Lambda constant, and the two-loop ratio test -----------------------
    ten = {float(r["beta"]): r for r in _artifact("8_8_dat_string_tension.csv")}
    ratios = []
    for beta, r in sorted(ten.items()):
        s = float(r["a2sigma_potential"])
        e = math.hypot(float(r["a2sigma_err"]), float(r["a2sigma_syst"]))
        a = _a_lambda(beta)
        ratios.append((math.sqrt(s) / a, 0.5 * e / math.sqrt(s) / a))
    for value, _ in ratios:
        assert f"{value:.1f}" in tension, f"Sec 8.8 does not quote sqrt(sigma)/Lambda = {value:.1f}"
    _, chi2 = _constant_fit(ratios)
    assert f"{chi2:.2f}" in tension, f"Sec 8.8 constant-fit chi2/dof = {chi2:.2f} is not quoted"

    betas = sorted(ten)
    for lo, hi in zip(betas, betas[1:]):
        slo, shi = float(ten[lo]["a2sigma_potential"]), float(ten[hi]["a2sigma_potential"])
        elo = math.hypot(float(ten[lo]["a2sigma_err"]), float(ten[lo]["a2sigma_syst"]))
        ehi = math.hypot(float(ten[hi]["a2sigma_err"]), float(ten[hi]["a2sigma_syst"]))
        meas = math.sqrt(slo / shi)
        err = meas * 0.5 * math.hypot(elo / slo, ehi / shi)
        pred = _a_lambda(lo) / _a_lambda(hi)
        assert f"{meas:.3f}" in tension, f"ratio a({lo})/a({hi}) = {meas:.3f} is not quoted in Sec 8.8"
        assert f"{pred:.3f}" in tension, f"two-loop ratio {pred:.3f} for {lo}->{hi} is not quoted in Sec 8.8"
        pull = (meas - pred) / err
        assert f"{abs(pull):.2f}" in tension, f"pull {pull:+.2f} sigma for {lo}->{hi} is not quoted in Sec 8.8"

    # -- Sec 8.7b: the variational read is constant in beta ---------------------------------------
    gap = _artifact("8_7_dat_gap_correlator.csv")
    var = []
    for beta in (2.30, 2.40, 2.50):
        pick = _variational(gap, 16, beta)
        assert pick, f"beta={beta}: no variational bound"
        a = _a_lambda(beta)
        var.append((pick[0] / a, pick[1] / a))
    # Both lists are read POSITIONALLY. The variational list (193, 210, 196) and the published one
    # (117, 196, 344) share the value 196, so checking that each number appears in the passage is
    # satisfied by the other list and a drift in either is masked.
    LIST3 = r"[$](\d+)[$], [$](\d+)[$], [$](\d+)[$]"
    mv = re.search(r"variational.{0,24}?read gives " + LIST3, variational)
    assert mv, "Sec 8.7b no longer lists the variational scaled gaps"
    want_var = tuple(format(v, '.0f') for v, _ in var)
    assert mv.groups() == want_var, (
        "Sec 8.7b lists the variational reads as " + str(mv.groups())
        + " but the artifacts give " + str(want_var))
    _, vchi2 = _constant_fit(var)
    assert f"{vchi2:.2f}" in variational, f"Sec 8.7b variational chi2/dof = {vchi2:.2f} is not quoted"

    # -- Sec 8.7b: the published read is not constant ---------------------------------------------
    pub = [(float(r["beta"]), float(r["Delta"])) for r in
           _artifact("8_7_dat_mhi_multicoupling.csv") if r["L"] == "16"]
    scaled = [d / _a_lambda(b) for b, d in sorted(pub)]
    mp = re.search(r"published action-density read gives " + LIST3, variational)
    assert mp, "Sec 8.7b no longer lists the published scaled gaps"
    want_pub = tuple(format(v, '.0f') for v in scaled)
    assert mp.groups() == want_pub, (
        "Sec 8.7b lists the published reads as " + str(mp.groups())
        + " but the artifact gives " + str(want_pub))
    drift = max(scaled) / min(scaled)
    assert f"{drift:.2f}" in variational, f"the published drift factor {drift:.2f} is not quoted"


def test_volume_constant_fit_matches_the_artifact():
    """Sec 8.7b's L-independence claim: the constant fit over L >= 12 and the m_hi it implies."""
    text = PAPER.read_text(encoding="utf-8")
    gap = _artifact("8_7_dat_gap_correlator.csv")
    vals = []
    for L in (12, 16, 20):
        pick = _variational(gap, L, 2.30)
        assert pick, f"L={L}: no variational read"
        vals.append((pick[0], pick[1]))
    mean, chi2 = _constant_fit(vals)
    # chi2/dof = 0.04 occurs several times in PAPER.md, so check it where the claim is made
    where = _passage(text, "the gap is constant at")
    assert f"{chi2:.2f}" in where, \
        f"Sec 8.7b does not state the volume constant-fit chi2/dof as {chi2:.2f}"
    assert f"{math.exp(-mean):.3f}" in where, \
        f"Sec 8.7b does not state the constant fit m_hi as {math.exp(-mean):.3f}"


def test_every_embedded_figure_exists_and_every_figure_is_embedded():
    """The paper's images resolve, and no committed figure is orphaned.

    Both directions matter: a broken link is a missing figure in the rendered paper, and a committed
    figure nothing embeds is an artifact being regenerated and checked for no reader.
    """
    import subprocess

    text = PAPER.read_text(encoding="utf-8")
    embedded = sorted(set(re.findall(r"!\[\]\(([^)]+)\)", text)))
    assert embedded, "the paper embeds no images; the link format may have changed"

    missing = [img for img in embedded if not (REPO / "research" / img).exists()]
    assert not missing, f"PAPER.md embeds images that do not exist: {missing}"

    r = subprocess.run(["git", "ls-files", "research/data/*.png"],
                       cwd=REPO, capture_output=True, text=True)
    if r.returncode != 0:
        pytest.skip("not a git checkout")
    committed = sorted(p.split("research/", 1)[1] for p in r.stdout.split())
    orphans = sorted(set(committed) - set(embedded))
    assert not orphans, f"committed figures nothing embeds: {orphans}"


@pytest.mark.parametrize("script", sorted(p.name for p in DATA.glob("*_fig_*.py")))
def test_figure_script_runs_against_the_committed_artifacts(script, tmp_path):
    """Each figure script still runs on the artifacts as they stand.

    A figure is drawn from a CSV, so changing that CSV's columns breaks the drawing silently until
    someone regenerates. Running the script here turns a schema change into a failing test. The
    figure is written to its normal path (the scripts own that), so this also confirms the committed
    figure can be reproduced from the committed data.
    """
    import shutil
    import subprocess

    target = DATA / script
    png = DATA / (script.replace("_fig_", "_fig_").replace(".py", ".png"))
    backup = tmp_path / png.name if png.exists() else None
    if backup:
        shutil.copy2(png, backup)
    try:
        r = subprocess.run([__import__("sys").executable, str(target)], cwd=DATA,
                           capture_output=True, text=True, timeout=300)
        assert r.returncode == 0, f"{script} failed:\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}"
        assert png.exists(), f"{script} produced no {png.name}"
    finally:
        if backup:
            shutil.copy2(backup, png)


def test_lscan_plateau_claim_matches_artifact():
    """EVERY statement of the m_hi(L) plateau agrees with 8_7_dat_mhi_lscan.csv.

    The paper repeats this claim in its abstract, its summary sections, Sec 8.7 where it is derived,
    the Figure 13 caption and the Sec 13 ledger, so one artifact number backs six sentences. The
    failure that matters is one of them being updated and the rest left behind, so it is not enough
    to find the value somewhere: every place the range is stated is located and checked. The band
    endpoints are two-decimal values that occur 8-12 times each in PAPER.md, so an unscoped match
    would be nearly vacuous.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("8_7_dat_mhi_lscan.csv")
    band = [float(r["m_hi"]) for r in rows if 12 <= int(r["L"]) <= 28]
    assert len(band) >= 4, "the L=12-28 window is not populated in the artifact"
    lo, hi, mean = min(band), max(band), sum(band) / len(band)

    # Every statement of the plateau, located by the phrase that always accompanies it. Anchoring
    # on the range pattern alone over-matches: Sec 12 states two neighbouring ranges (the U(1)
    # Coulomb margin, and the finite-aperture span) that are different quantities.
    dash = "[" + chr(0x2013) + chr(0x2014) + "-]+"
    win = re.compile(r"scaling window " + re.escape("$L=12$") + dash + re.escape("$28$"))
    # the leading number may be introduced by "$", "\approx" or "=", so do not require a "$" before it
    rng = re.compile(r"(\d\.\d\d)\$" + dash + r"\$(\d\.\d\d)\$")
    found = 0
    for w in win.finditer(text):
        ctx = text[max(0, w.start() - 300):w.end() + 300]
        m = rng.search(ctx)
        if not m:
            continue      # names the window without restating the range (Sec 1; the Fig 13 caption,
                          # which states the mean instead) -- not a place the range can go stale
        found += 1
        got = (float(m.group(1)), float(m.group(2)))
        line = text[:w.start()].count(chr(10)) + 1
        assert abs(got[0] - lo) < 5e-3 and abs(got[1] - hi) < 5e-3,             f"PAPER.md line {line} states the m_hi plateau as {got[0]}-{got[1]}, "             f"but 8_7_dat_mhi_lscan.csv gives {lo:.2f}-{hi:.2f}"
    assert found >= 5,         f"the m_hi plateau range is restated in {found} places; the paper carries it in at least 5, "         "so this check is not seeing them all"

    # The mean, wherever it is restated alongside the window. Sec 8.7, the Figure 13 caption and the
    # Sec 12 ledger row all carry it, and the ledger row carries the range and mean but not the edges,
    # so the claims are checked one by one rather than passage by passage.
    # Matched on how the mean is written -- "mean $\approx" / "plateau $\approx" -- rather than on
    # any nearby \approx: the range itself is written "$m_hi\approx0.31$--$0.48$", whose lower
    # endpoint an unanchored pattern reads as the mean.
    means = list(re.finditer(r"(?:mean|plateau) " + re.escape("$" + BS + "approx") + r"(\d\.\d\d)", text))
    assert len(means) >= 3,         f"the plateau mean is stated in {len(means)} places; the paper carries it in at least 3"
    for m in means:
        line = text[:m.start()].count(chr(10)) + 1
        assert abs(float(m.group(1)) - mean) < 5e-3,             f"PAPER.md line {line} states the plateau mean as {m.group(1)}, "             f"but 8_7_dat_mhi_lscan.csv gives {mean:.2f}"

    # The two resolution edges, in the two passages that give their values.
    edges = {int(r["L"]): float(r["m_hi"]) for r in rows if int(r["L"]) in (8, 32)}
    for name, anchor in (("Sec 8.7", "excluded from the plateau"),
                         ("the Figure 13 caption", "**Figure 13.**")):
        blk = _passage(text, anchor)
        for L, v in edges.items():
            assert f"{v:.2f}" in blk, f"{name} does not quote the L={L} resolution edge as {v:.2f}"


def test_quoted_aperture_ceiling_is_the_derived_constant():
    """Every numeric value the paper gives for 3^(-1/4) is that constant, at the precision written.

    The ceiling is stated in several places and at two precisions -- 0.76 in prose, 0.7598 where
    the comparison is tight. Checking that the value appears somewhere cannot tell whether one of
    them has drifted, since the others still match; each occurrence is compared instead, rounded
    to the number of decimals it is written with.
    """
    ceiling = 3.0 ** (-0.25)
    tight = "".join(PAPER.read_text(encoding="utf-8").split())
    kappa = re.escape("=e^{-" + chr(92) + "kappa_0}")
    pat = re.compile(re.escape("3^{-1/4}") + "(?:" + kappa + ")?" + re.escape("=") + r"(\d\.\d+)")
    hits = pat.findall(tight)
    assert len(hits) >= 4, (
        f"the ceiling is given a numeric value in {len(hits)} places; the paper states it in at "
        "least 4")
    for h in hits:
        dp = len(h.split(".")[1])
        assert h == f"{ceiling:.{dp}f}", (
            f"the paper writes 3^(-1/4) = {h}, but the constant to {dp} decimals is "
            f"{ceiling:.{dp}f}")


def test_two_read_agreement_claim_matches_the_artifacts():
    """Sec 8.7's "the two reads agree" numbers are re-derived from both artifacts.

    The paper claims the forward (action-density DMD) read and the Sec 8.7b variational read agree to
    <= 0.013 in m_hi across L = 12-20, and that at L = 16 the agreement is across DIFFERENT operators.
    Both halves are computed here rather than trusted: the per-volume differences, and which operator
    the variational rule actually selects at each volume. The failure this catches is either artifact
    being regenerated -- moving a difference or flipping a selection -- while the prose keeps the old
    claim, which would turn a cross-check into an assertion.

    Every number is checked inside the passage that states it. Matching against the whole paper is
    close to vacuous here: PAPER.md quotes hundreds of values and each of these appears elsewhere in
    it, so an unscoped check passes on a paper whose claim has drifted.
    """
    text = PAPER.read_text(encoding="utf-8")
    fwd = {int(r["L"]): (float(r["m_hi"]), float(r["m_hi_err"]))
           for r in _artifact("8_7_dat_mhi_lscan.csv")}
    rows = _artifact("8_7_dat_gap_correlator.csv")

    REL_TOL = 0.25                                   # the resolution rule Sec 8.7b states
    var = {}
    for r in rows:
        if abs(float(r["beta"]) - 2.30) > 1e-9 or not r["m_eff"] or not r["m_eff_err"]:
            continue
        v, e = float(r["m_eff"]), float(r["m_eff_err"])
        if v <= 0 or e <= 0 or e / v > REL_TOL:
            continue
        L = int(r["L"])
        if L not in var or v < var[L][0]:
            var[L] = (v, e, r["operator"])

    window = sorted(L for L in var if 12 <= L <= 20 and L in fwd)
    assert window == [12, 16, 20], f"the L=12-20 window is not populated: {window}"

    prose = _passage(text, "Both reads are drawn on the same axes")
    caption = _passage(text, "**Figure 13.**")

    # the window each passage states is the window the artifacts populate
    assert "$L=" + ",".join(str(L) for L in window) + "$" in prose,         f"Sec 8.7 does not list the volumes it compares as L={window}"
    assert f"$L={window[0]}$--${window[-1]}$" in caption,         f"the Figure 13 caption does not state the compared range as L={window[0]}-{window[-1]}"

    diffs = {L: abs(math.exp(-var[L][0]) - fwd[L][0]) for L in window}
    # The per-volume list is read POSITIONALLY. Checking that each value appears in the passage is
    # not enough: the worst case is stated in the same sentence, so the largest difference occurs
    # twice and a drift in the list still matches the bound.
    listed = re.search(r"[(]" + r"[$](\d\.\d{3})[$], [$](\d\.\d{3})[$], [$](\d\.\d{3})[$] at",
                       prose)
    assert listed, "Sec 8.7 no longer lists the per-volume differences"
    want = tuple(f"{diffs[L]:.3f}" for L in window)
    assert listed.groups() == want, (
        f"Sec 8.7 lists the per-volume differences as {listed.groups()}, but the artifacts give "
        f"{want} at L={window}")
    worst = max(diffs.values())
    for where, blk in (("Sec 8.7", prose), ("the Figure 13 caption", caption)):
        assert (BS + "le" + f"{worst:.3f}") in blk, \
            f"{where} does not state the worst-case agreement as le{worst:.3f}"

    # the "different operators at L=16" half of the claim
    assert var[16][2] == "plaquette_0pp", \
        f"the variational rule no longer selects the plaquette at L=16 (it selects {var[16][2]}); " \
        "the paper's 'agreement between different operators' claim rests on that selection"
    for L in (12, 20):
        assert var[L][2] == "action_density", \
            f"the variational rule now selects {var[L][2]} at L={L}; the paper says action density, " \
            "and uses that to say the L=12/20 agreement tests the pipeline and not the operator"

    # L=8 is called an edge because the forward read is unresolved there, not because it disagrees
    e8 = fwd[8][1]
    assert e8 > fwd[8][0], "the L=8 forward read is no longer unresolved; the paper says it is"
    m8 = math.exp(-var[8][0])
    for where, blk in (("Sec 8.7", prose), ("the Figure 13 caption", caption)):
        assert f"{e8:.2f}" in blk, f"{where} does not quote the L=8 forward error {e8:.2f}"
        assert f"{m8:.3f}" in blk, f"{where} does not quote the L=8 variational value {m8:.3f}"

    # the sentence contrasting the two reads at L=8 must carry the forward VALUE as well as its
    # error: without it the contrast could quote any number against 0.220 and still check out
    part = _passage(text, "part company")
    assert f"${fwd[8][0]:.2f}" + BS + f"pm{e8:.2f}$" in part, (
        f"the L=8 contrast does not state the forward read as {fwd[8][0]:.2f}+-{e8:.2f}")


def test_aperture_numbers_match_the_margin_artifact():
    """Sec 12's finite-aperture numbers are the ones gap_of_margin.py measured.

    Every value in this passage -- the two Coulomb rows, the confined U(1) row, the SU(2) L=32 row
    and the ensemble count -- reaches PAPER.md by hand from that program's stdout table. It is a
    bigmem read (it was OOM-killed at the 8 GB envelope), so re-running it to check a transcription
    is not cheap; `gap_of_margin.py` therefore persists the table it prints, and this compares the
    two.

    Skips until the artifact is regenerated, which is a pod job, not a local one.
    """
    path = DATA / "9_2_dat_margin_aperture.csv"
    if not path.exists():
        pytest.skip("9_2_dat_margin_aperture.csv not regenerated yet (gap_of_margin.py is bigmem)")
    rows = _artifact("9_2_dat_margin_aperture.csv")
    text = PAPER.read_text(encoding="utf-8")
    passage = _passage(text, "reads a finite aperture **too**")

    # The count is read from the artifact and the paper is required to spell that number, rather
    # than both being written here: a row added to or dropped from the table then shows up as a
    # failure naming the new count, instead of passing against a hard-coded one.
    WORDS = {5: "five", 6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten"}
    word = WORDS.get(len(rows))
    assert word, f"the aperture table has {len(rows)} ensembles; add that number to WORDS"
    assert f"{word} ensembles" in passage, \
        f"the artifact carries {len(rows)} ensembles, but Sec 12 does not say '{word} ensembles'"

    def m_hi(group, beta, L):
        hit = [r for r in rows if r["group"] == group and abs(float(r["beta"]) - beta) < 1e-9
               and int(r["L"]) == L]
        assert len(hit) == 1, f"expected exactly one {group} b{beta} L{L} row, got {len(hit)}"
        return float(hit[0]["m_hi"])

    # The U(1) rows are read at L=8, the volume the released U(1) ensembles are held at and the one
    # Sec 8.3 measures the K_signal transition on. The volume is part of each key so that a row
    # measured on a different one fails here rather than matching by (group, beta) alone.
    for label, (group, beta, L) in (
            ("Coulomb U(1) at beta=1.70", ("u1", 1.70, 8)),
            ("Coulomb U(1) at beta=2.50", ("u1", 2.50, 8)),
            ("confined U(1) at beta=0.90", ("u1", 0.90, 8)),
            ("confined SU(2) at L=24", ("su2", 2.30, 24))):
        v = m_hi(group, beta, L)
        assert f"{v:.3f}" in passage, \
            f"Sec 12 does not quote m_hi = {v:.3f} for the {label} row"

    # the paragraph's point: every row reads finite, so the margin does not discriminate the phases
    ceiling = 3 ** -0.25
    over = [r for r in rows if float(r["m_hi"]) >= ceiling]
    assert not over, \
        "Sec 12 says every row is below the 3^(-1/4) ceiling, but these are not: " \
        + ", ".join(f"{r['group']} b{r['beta']} L{r['L']} = {r['m_hi']}" for r in over)


def test_d2_certificate_claims_match_the_artifact():
    """The d^2 finite-sample certificate: every number the paper states, from 9_1_dat_d2_certified.csv.

    This artifact carries the empirical-Bernstein uppers that discharge the grid interior, and the
    paper leans on it in four places -- the summary, Sec 9, the Figure 11 caption and the Sec 13
    ledger. Nothing pinned it. The joint confidence in particular is a derived quantity
    (0.999^n over the grid), so it moves silently if the grid gains or loses a coupling.

    The threefold margin the paper states belongs to the pinned proof bound: B = 1 sits that far
    under the aperture threshold B_16 ~ 3.52. The uppers clear the threshold by more, so the two
    are separate quantities and the margin attaches to the bound.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("9_1_dat_d2_certified.csv")
    central = [float(r["d2_central"]) for r in rows]
    # The certificate reports at a chosen delta, and the artifact names it in the column heading, so
    # the OPERATIVE column is the tightest confidence it carries and everything below is derived
    # from that name rather than restated here. Re-running the certificate at a different delta then
    # moves this test WITH the artifact instead of against it -- which is the point, because the
    # delta is a choice and the paper must quote whichever one the certificate actually ran at.
    conf_cols = {c: float(c.rsplit("_", 1)[1]) for c in rows[0] if c.startswith("eb_upper_")}
    assert conf_cols, "the certificate carries no eb_upper_* column"
    upper_col = max(conf_cols, key=conf_cols.get)
    confidence = conf_cols[upper_col]                      # e.g. 99.9999
    upper = [float(r[upper_col]) for r in rows]
    bound_col = [c for c in rows[0] if c.startswith("certified_below_")][0]
    proof_bound = float(bound_col.rsplit("_", 1)[1])

    # the grid, and that every coupling clears the pinned proof bound
    assert f"{len(rows)}-point grid" in text, \
        f"the paper does not describe this as a {len(rows)}-point grid"
    failed = [r["beta"] for r in rows if r[bound_col] != "yes"]
    assert not failed, f"couplings not certified below B={proof_bound}: {failed}"

    # the largest cap, at whatever confidence the artifact was produced at
    caps = _passage(text, "caps at most")
    assert f"{max(upper):.2f}" in caps, \
        f"the Figure 11 caption does not state the largest {confidence:g}% cap as {max(upper):.2f}"
    assert f"{confidence:g}" in caps, \
        f"the Figure 11 caption does not state the confidence as {confidence:g}%"

    # the joint confidence over the grid, wherever it is stated
    joint = ((confidence / 100) ** len(rows)) * 100
    stated = list(re.finditer(r"joint " + re.escape("$" + BS + "approx") + r"(\d+\.\d+)" + re.escape(BS + "%"), text))
    assert len(stated) >= 2, f"the joint confidence is stated in {len(stated)} places; expected at least 2"
    for m in stated:
        line = text[:m.start()].count(chr(10)) + 1
        assert abs(float(m.group(1)) - joint) < 0.05, \
            f"PAPER.md line {line} states the joint confidence as {m.group(1)}%, " \
            f"but ({confidence:g}/100)^{len(rows)} over the grid gives {joint:.4f}%"

    # the central band the paper quotes must contain the measured values and be tight to 2 decimals
    band = _passage(text, "Measured central values")
    dash = "[" + chr(0x2013) + chr(0x2014) + "-]+"
    m = re.search(r"(\d\.\d+)\$" + dash + r"\$(\d\.\d+)", band)
    assert m, f"the Figure 11 caption no longer states a central band: {band[:200]}"
    lo_q, hi_q = float(m.group(1)), float(m.group(2))
    assert lo_q <= min(central) + 5e-4 and hi_q >= max(central) - 5e-3, \
        f"the quoted central band {lo_q}-{hi_q} does not contain the measured {min(central):.3f}-{max(central):.3f}"
    assert hi_q - max(central) < 0.01, \
        f"the quoted upper end {hi_q} is loose against the measured maximum {max(central):.3f}"


def test_no_math_delimiter_is_glued_to_a_word():
    r"""No inline-math `$` sits against a word character, which stops it rendering.

    Markdown math needs the delimiters separated from surrounding words. Where they were not, the
    renderer did not just show the source: `closed$+$bounded $\Rightarrow$ compact` came out of the
    PDF as "closed$+ => compact" with the word *bounded* swallowed, and `spatial$\times$temporal`
    printed its LaTeX literally. Both were live in the committed PDF.

    Parity across the file decides which delimiters open and which close, so this does not guess.
    """
    text = PAPER.read_text(encoding="utf-8")
    D, BS = chr(36), chr(92)
    pos = [i for i in range(len(text)) if text[i] == D and (i == 0 or text[i - 1] != BS)]
    assert len(pos) % 2 == 0, \
        f"PAPER.md has an odd number of unescaped {D} ({len(pos)}); a math span is unterminated"

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


def test_no_table_row_has_an_unescaped_pipe():
    r"""Every markdown table row has the column count its block uses.

    A bare `|` inside a cell is read as a separator, so the row gains cells and the renderer drops
    the surplus -- content vanishes from the rendered paper while the markdown still reads correctly.
    The paper writes LaTeX norms as `\|C(\tau)\|` inside these tables, which is already the
    markdown escape for a literal pipe, so this counts SEPARATORS rather than pipes; counting pipes
    flags those rows and they are fine.
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
    assert blocks, "PAPER.md has no markdown tables; this test is looking at the wrong file"

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


def test_figures_are_numbered_sequentially_in_document_order():
    """Figure N's caption is the Nth caption in the file, and each follows its own image embed.

    The figures were renumbered 1-13 during this paper's revision, which is exactly when a caption
    keeps an old number or two captions collide: nothing else would catch it, because every figure
    file still exists and every embed still resolves. Ten of the thirteen are never called out by
    number in the prose -- they sit directly after the passage they support, which is the paper's
    layout -- so a wrong number would be silent.
    """
    import re

    lines = PAPER.read_text(encoding="utf-8").split(chr(10))
    caps = [(i, int(m.group(1)))
            for i, l in enumerate(lines)
            for m in [re.match(r"\*\*Figure (\d+)\.\*\*", l)] if m]
    assert caps, "PAPER.md has no figure captions"

    numbers = [n for _, n in caps]
    assert numbers == sorted(numbers), \
        f"figure captions are out of order in the document: {numbers}"
    assert numbers == list(range(1, len(numbers) + 1)), \
        f"figure numbering is not 1..{len(numbers)} without gaps or repeats: {numbers}"

    for i, n in caps:
        window = lines[max(0, i - 3):i]
        assert any(l.startswith("![](data/") for l in window), \
            f"Figure {n}'s caption at line {i+1} does not follow an image embed"


def test_phase_separation_claim_matches_the_order_parameter_artifact():
    """Sec 8.3's certified phase separation, re-derived from 8_3_dat_confinement_order_parameter.csv.

    the confined ceiling, the Coulomb floor, and the range each phase occupies. The Coulomb range
    is the range over that phase's rows, which is not the value at the last coupling: K_signal is
    non-monotonic there and peaks at beta=1.6, so the largest value sits inside the sweep rather
    than at its end.

    The separation itself is checked, not just quoted: ceiling + 1.96 sigma must sit below
    floor - 1.96 sigma for "at 95%" to mean anything.
    """
    import math

    rows = _artifact("8_3_dat_confinement_order_parameter.csv")
    conf = [r for r in rows if r["phase"] == "confined"]
    coul = [r for r in rows if r["phase"] != "confined"]
    assert conf and coul, "the artifact no longer carries both phases"

    text = PAPER.read_text(encoding="utf-8")
    flat = " ".join(text.split())

    ceiling = max(conf, key=lambda r: float(r["K_signal"]))
    floor = min(coul, key=lambda r: float(r["K_signal"]))
    c, ce = float(ceiling["K_signal"]), float(ceiling["K_signal_err"])
    f, fe = float(floor["K_signal"]), float(floor["K_signal_err"])

    assert c + 1.96 * ce < f - 1.96 * fe, (
        f"the confined ceiling {c:.3f}+-{ce:.3f} and the Coulomb floor {f:.3f}+-{fe:.3f} overlap at "
        "95%; the paper says the phases are distinct at that level")

    # Anchored on the word, not the digits: "0.096" also appears in the confined-phase bound
    # immediately before, and "0.153" in the Coulomb range, so a bare substring check passes when
    # the ceiling or floor alone has drifted.
    for word, value in (("ceiling", c), ("floor", f)):
        assert f"{word} ${value:.3f}" in flat,             f"the paper does not quote the {word} as {value:.3f}"

    lo, hi = min(float(r["K_signal"]) for r in coul), max(float(r["K_signal"]) for r in coul)
    assert f"Coulomb-phase ${lo:.3f}$" in flat and f"${hi:.3f}$" in flat, (
        f"the paper does not state the Coulomb range as {lo:.3f}-{hi:.3f}; the maximum is at "
        f"beta={max(coul, key=lambda r: float(r['K_signal']))['beta']}, not the last coupling")


    conf_hi = max(float(r["K_signal"]) for r in conf)
    # anchored on the spelling: "0.096" also appears as the ceiling value in the same sentence,
    # so a bare match cannot tell the range bound from the ceiling
    assert f"{BS}lesssim{conf_hi:.3f}" in flat, \
        f"the paper does not state the confined range as reaching {conf_hi:.3f}"


def test_su3_second_moment_claims_match_the_artifact():
    """Sec 8.6 and the Figure 12 caption, re-derived from 9_1_dat_d2_su3.csv.

    The SU(3) read is what carries "the finite-correlation-length interior read holds on a second
    gauge group", so the numbers behind it matter: the band the moment occupies, the couplings it
    spans, and the margin to the aperture ceiling. Nothing named this artifact before.

    The margin is checked as a ratio rather than matched as text -- the paper says "a factor
    gtrsim 4 below its aperture ceiling", and 0.60/0.1445 = 4.15 is close enough to the boundary
    that a modest drift in the measurement would make the word wrong while the digits still matched.
    """
    rows = _artifact("9_1_dat_d2_su3.csv")
    vals = [float(r["d2"]) for r in rows]
    betas = [float(r["beta"]) for r in rows]
    text = PAPER.read_text(encoding="utf-8")
    flat = " ".join(text.split())

    # Scoped to the SU(3) sentence: the first "[a, b]" in the document is the SU(2) band
    # [0.014, 0.16], which contains the SU(3) values and would pass while checking nothing.
    where = flat.find("aperture ceiling")
    assert where != -1, "the paper no longer states an SU(3) aperture ceiling"
    window = flat[max(0, where - 320):where + 160]
    band = re.search(r"\[(\d\.\d+),\s*(\d\.\d+)\]", window)
    assert band, "the SU(3) passage no longer quotes a band for the second moment"
    lo, hi = float(band.group(1)), float(band.group(2))
    assert lo <= min(vals) and hi >= max(vals), (
        f"the quoted band {lo}-{hi} does not contain the measured "
        f"{min(vals):.4f}-{max(vals):.4f}")
    assert hi - max(vals) < 0.01, \
        f"the quoted upper end {hi} is loose against the measured maximum {max(vals):.4f}"

    # the coupling range, as the paper states it
    dash = "[" + chr(0x2013) + chr(0x2014) + "-]"
    BS2 = chr(92)          # built, not written: a literal "\\" here is fragile
    beta_pat = "[$]" + BS2 + BS2 + "beta=" + r"(\d\.\d)" + "[$]" + dash + "[$]" + r"(\d\.\d)" + "[$]"
    m = re.search(beta_pat, window)
    assert m, "the paper no longer states the SU(3) coupling range"
    assert (float(m.group(1)), float(m.group(2))) == (min(betas), max(betas)), (
        f"the paper states beta={m.group(1)}-{m.group(2)} but the artifact spans "
        f"{min(betas):.2f}-{max(betas):.2f}")

    # the margin to the ceiling, checked as a ratio
    ceil_m = re.search(r"aperture ceiling \(\$(\d\.\d+)\$ at \$L=(\d+)\$", window)
    assert ceil_m, "the paper no longer states the SU(3) aperture ceiling"
    ceiling = float(ceil_m.group(1))
    factor = ceiling / max(vals)
    claimed = re.search(re.escape(chr(92) + "gtrsim") + r"(\d+)", window)
    assert claimed, "the paper no longer states a margin factor"
    assert factor >= float(claimed.group(1)), (
        f"the paper claims a factor >= {claimed.group(1)} below the ceiling, but "
        f"{ceiling}/{max(vals):.4f} = {factor:.2f}")


def test_disorder_response_separation_matches_the_artifact():
    """Sec 8.4's peak separation, recomputed from 8_4_dat_disorder_response.csv.

    The artifact stores the Shannon entropy H(beta); the quantity the paper reports is the response
    chi_v = -dH/dbeta, so this DERIVES the peaks rather than matching a stored column -- the failure
    it guards against is a regenerated H moving the peak while the prose keeps the old factor.

    Three passages depend on it: Sec 8.4's numbers, the Figure 3 caption, and the Sec 13 ledger row.
    Nothing named this artifact before.
    """
    import collections

    rows = _artifact("8_4_dat_disorder_response.csv")
    by = collections.defaultdict(list)
    for r in rows:
        by[r["group"]].append((float(r["beta"]), float(r["H"])))
    for g in ("u1", "su2"):
        assert len(by[g]) >= 4, f"{g} has too few couplings to differentiate"

    def peak(g):
        pts = sorted(by[g])
        chi = [(0.5 * (pts[i][0] + pts[i + 1][0]),
                -(pts[i + 1][1] - pts[i][1]) / (pts[i + 1][0] - pts[i][0]))
               for i in range(len(pts) - 1)]
        return max(chi, key=lambda z: z[1])

    b_u1, v_u1 = peak("u1")
    _, v_su2 = peak("su2")
    ratio = v_u1 / v_su2

    text = PAPER.read_text(encoding="utf-8")
    flat = " ".join(text.split())
    BS = chr(92)

    assert f"{BS}approx{v_u1:.2f}" in flat, \
        f"the paper does not state the U(1) peak response as {v_u1:.2f}"
    assert f"{BS}approx{v_su2:.2f}" in flat, \
        f"the paper does not state the SU(2) peak response as {v_su2:.2f}"

    # Only occurrences following the word "peak": the same spelling elsewhere names beta_KP, a
    # different quantity that happens to share the value. ".{0,90}?" rather than a class excluding
    # periods, because the reporting sentence puts "0.87" between "peak" and the value.
    # Compared at the precision the paper writes: the peak is a bin midpoint (0.975) rounded to two
    # decimals, so a tolerance of half the last digit would sit exactly on the boundary.
    assert_every_statement(
        flat, r"peak.{0,90}?" + re.escape("$" + BS + "beta" + BS + "approx") + r"(\d\.\d\d)",
        f"{b_u1:.2f}", "the disorder-response peak location", minimum=2)

    # the separation factor, checked as a number rather than matched as text
    stated = re.findall(re.escape(BS + "approx") + r"(\d+)" + re.escape(BS + "times"), flat)
    assert stated, "the paper no longer states a separation factor"
    for s_ in stated:
        assert abs(ratio - float(s_)) < 1.0, (
            f"the paper claims a {s_}x separation, but the artifact gives {ratio:.1f}x")


def test_gap_calibration_states_both_ends():
    """Sec 8.5 and the Figure 4/5 captions quote the free-scalar calibration at BOTH ends.

    8_5_dat_gap_calibration.csv records the relative error of the DMD gap read against the exact
    free-scalar E_0 across m = 0.20-1.10. The paper quoted only the tight end, "0.2% at m=1.10", in
    all three places -- so the instrument read as 0.2%-accurate when it is 8.9% off at the
    small-mass end. The mechanism was explained (the periodic image on a finite L_t) but not the
    size, which is quoting the best point.

    Every passage that states the approach must carry both ends, and both must be the artifact's.
    """
    rows = _artifact("8_5_dat_gap_calibration.csv")
    errs = [abs(float(r["rel_err_pct"])) for r in rows]
    masses = [float(r["m"]) for r in rows]
    loose = max(rows, key=lambda r: abs(float(r["rel_err_pct"])))
    tight = min(rows, key=lambda r: abs(float(r["rel_err_pct"])))
    lo_e, lo_m = abs(float(loose["rel_err_pct"])), float(loose["m"])
    ti_e, ti_m = abs(float(tight["rel_err_pct"])), float(tight["m"])

    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    BS = chr(92)
    sites = [i for i in range(len(flat)) if flat.startswith("setting the approach", i)]
    assert len(sites) >= 3, f"expected the calibration approach to be stated in 3 places, found {len(sites)}"
    for i in sites:
        seg = flat[i:i + 150]
        assert f"{lo_e:.1f}{BS}%" in seg and f"m={lo_m:.2f}" in seg, (
            f"a passage states the calibration without its loose end "
            f"({lo_e:.1f}% at m={lo_m:.2f}): ...{seg[:90]}...")
        assert f"{ti_e:.1f}{BS}%" in seg and f"m={ti_m:.2f}" in seg, (
            f"a passage states the calibration without its tight end "
            f"({ti_e:.1f}% at m={ti_m:.2f}): ...{seg[:90]}...")

    # the mass range the captions quote
    assert f"m{BS}in[{min(masses):.2f},{max(masses):.2f}]" in flat, \
        f"the paper does not state the calibrated mass range as [{min(masses):.2f},{max(masses):.2f}]"


def test_the_two_d2_artifacts_describe_the_same_measurement():
    """9_1_dat_d2_bound.csv and 9_1_dat_d2_certified.csv agree, coupling for coupling.

    They are the same read reported two ways -- a bootstrap band and an empirical-Bernstein
    certificate -- written by two different scripts (9_1_run_d2_bound.py and 9_1_run_d2_certify.py)
    that share the profile functions but run independently. Sec 9 and the Figure 10/11 captions quote
    numbers that appear in both, so a regeneration of one alone would leave the paper describing two
    different measurements with one set of words, and `regen_all --verify` would report only that
    some cells moved.

    Exact agreement is the right bar here: both derive the central value from the same profiles, so
    any difference at all means they were produced from different data.
    """
    bound = {r["beta"]: r for r in _artifact("9_1_dat_d2_bound.csv")}
    cert = {r["beta"]: r for r in _artifact("9_1_dat_d2_certified.csv")}
    assert sorted(bound) == sorted(cert), (
        "the two d2 artifacts cover different couplings: "
        f"{sorted(set(bound) ^ set(cert))}")

    for beta in sorted(bound, key=float):
        x, y = float(bound[beta]["d2"]), float(cert[beta]["d2_central"])
        assert x == y, (
            f"at beta={beta} the bootstrap artifact reads {x} and the certified artifact {y}; "
            "they are the same measurement and were produced from different data")
        nb, nc = int(bound[beta]["nconfigs"]), int(cert[beta]["nconfigs"])
        assert nb == nc, \
            f"at beta={beta} the two artifacts used {nb} and {nc} configurations"

    # the peak the paper quotes is this measurement's, in both
    peak_beta = max(bound, key=lambda k: float(bound[k]["d2"]))
    peak = float(bound[peak_beta]["d2"])
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    assert f"peaks at ${peak:.3f}$" in flat, \
        f"the paper does not state the peak as {peak:.3f} (at beta={peak_beta})"


def test_gap_identity_residual_matches_the_probe_artifact():
    """The DMD gap-identity bound, taken from 8_6_dat_probe.csv's P1_gap residuals.

    The paper stated "~6e-11 nats" in three places. No aggregate of the artifact is 6e-11: the
    maximum absolute residual is 1.9e-11 and the RMS is 6.07e-12 -- the mantissa of the RMS with the
    exponent off by one, propagated to all three. The measured bound is quoted instead.

    The bound is the MAXIMUM, because the sentence reads "returns Delta to X nats", which is a
    statement about the worst case rather than a typical one.
    """
    rows = [r for r in _artifact("8_6_dat_probe.csv") if r["probe"] == "P1_gap"]
    assert rows, "the probe artifact no longer carries a P1_gap block"
    res = [abs(float(r["residual"])) for r in rows]
    xs = [float(r["x"]) for r in rows]
    worst = max(res)

    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    BS = chr(92)
    mant, exp = ("%.1e" % worst).split("e")
    stated = f"${mant}{BS}times10^{{{int(exp)}}}$"
    n = flat.count(stated)
    assert n >= 3, (
        f"the gap-identity bound {stated} appears {n} times; the paper states it in Sec 8.6, the "
        "Figure 6 caption and the Sec 13 ledger")

    # nothing may still quote a bound the artifact does not support
    assert f"{BS}sim6{BS}times10^{{-11}}" not in flat, \
        "a passage still quotes the old ~6e-11 bound, which no aggregate of the artifact gives"

    # the range over which the identity is claimed
    assert f"{BS}Delta{BS}in[{min(xs):.1f},{max(xs):.1f}]" in flat, \
        f"the paper does not state the identity range as [{min(xs):.1f},{max(xs):.1f}]"


def test_the_benchmark_reproduces_the_calibration_it_summarises():
    """8_6_dat_benchmark.csv panel A is 8_5_dat_gap_calibration.csv, value for value.

    The benchmark table is the paper's "reads against the established picture" summary, written by
    8_6_run_benchmark.py; the calibration it summarises is written by 8_5_run_gap_calibration.py.
    Two scripts, one measurement. Regenerating one alone would leave the benchmark asserting a
    correspondence with numbers the calibration no longer produces -- and because the benchmark
    stores the established value alongside, the table would still look internally consistent.

    Panel B's established value is checked against the paper's stated transition, for the same
    reason: it is quoted as an established fact and nothing tied the two together.
    """
    import re

    cal = {float(r["m"]): r for r in _artifact("8_5_dat_gap_calibration.csv")}
    ben = _artifact("8_6_dat_benchmark.csv")
    panel_a = [r for r in ben if r["panel"] == "A"]
    assert panel_a, "the benchmark no longer carries a panel A"
    assert len(panel_a) == len(cal), (
        f"panel A has {len(panel_a)} rows and the calibration {len(cal)}")

    for r in panel_a:
        m = float(re.search(r"m=([0-9.]+)", r["quantity"]).group(1))
        assert m in cal, f"panel A reports m={m}, which the calibration does not cover"
        assert float(r["entroptics"]) == float(cal[m]["mass_gap"]), (
            f"at m={m} the benchmark reads {r['entroptics']} and the calibration "
            f"{cal[m]['mass_gap']}")
        assert float(r["established"]) == float(cal[m]["E0"]), (
            f"at m={m} the benchmark's established value is {r['established']} and the "
            f"calibration's E0 is {cal[m]['E0']}")

    panel_b = [r for r in ben if r["panel"] == "B"]
    if panel_b:
        beta_c = float(panel_b[0]["established"])
        flat = " ".join(PAPER.read_text(encoding="utf-8").split())
        assert_every_statement(flat, re.escape(BS + "beta_c" + BS + "approx") + r"(\d\.\d+)",
                               str(beta_c), "the U(1) transition", minimum=2)


def test_plane_scale_caveat_matches_its_artifact():
    """Sec 8.3's plane-size caveat carries the numbers 8_3_dat_ksignal_planescale.csv measured.

    K_signal is a per-plane resolved-mode count, so its absolute level depends on the plane: the same
    SU(2) beta=2.3 ensemble reads 0.08 on 8^3 and 0.67 on 16^3. That caveat is what keeps the Sec 8.3
    thresholds meaningful -- the confined ceiling of 0.096 and the Coulomb floor of 0.153 are 8^3
    numbers, and without the caveat a reader would take them as absolute and find the 16^3 value
    sitting far above the "Coulomb" range for a confined ensemble.

    So the caveat is load-bearing prose, and this holds its numbers to the artifact.
    """
    rows = _artifact("8_3_dat_ksignal_planescale.csv")
    assert len(rows) >= 2, "the plane-scale artifact needs at least two plane sizes"
    by_plane = {r["plane"]: float(r["K_signal"]) for r in rows}
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())

    small = min(by_plane.items(), key=lambda kv: kv[1])
    large = max(by_plane.items(), key=lambda kv: kv[1])
    # inside the caveat sentence: "0.08" occurs three times in the paper and "0.67" elsewhere too,
    # so the reads are located by the sentence that compares them rather than by their digits
    cav = flat.find("scales with the plane size")
    assert cav != -1, "the plane-size caveat is gone; the Sec 8.3 thresholds would read as absolute"
    sent = flat[cav:cav + 220]
    for label, (plane, value) in (("small-plane", small), ("large-plane", large)):
        assert f"{value:.2f}" in sent, (
            f"the caveat sentence does not carry the {label} read ({plane}) as {value:.2f}")

    # the caveat itself must still be there
    assert "scales with the plane size" in flat, \
        "the plane-size caveat is gone; the Sec 8.3 thresholds would read as absolute"

    # and the two reads must be the same ensemble, or the comparison says nothing
    groups = {r["group"] for r in rows}
    betas = {r["beta"] for r in rows}
    assert len(groups) == 1 and len(betas) == 1, (
        f"the plane-scale rows span {groups} and {betas}; the caveat compares one ensemble at two "
        "plane sizes")


def test_the_string_tension_table_is_the_curve_at_its_read_window():
    """8_8_dat_string_tension.csv's sigma is 8_8_dat_string_tension_curves.csv at t_read.

    The table reports one number per coupling; the curves artifact carries sigma(T) at every time
    extent, with a `used` flag marking the read window. The reported value is the curve at the
    largest used T -- the 3-sigma resolution rule the measurement applies -- so the two are the same
    result at two levels of detail, written by the same run.

    Worth holding because the T-dependence IS the systematic here: Sec 8.8 quotes a systematic from
    "the residual T-dependence across the window". If the table and the curve drifted apart, the
    quoted sigma would no longer be the endpoint of the curve the figure draws, and the systematic
    would describe a window the value does not come from.
    """
    tab = {r["beta"]: r for r in _artifact("8_8_dat_string_tension.csv")}
    cur = _artifact("8_8_dat_string_tension_curves.csv")
    assert tab and cur, "one of the string-tension artifacts is empty"

    for beta, row in sorted(tab.items(), key=lambda kv: float(kv[0])):
        used = [r for r in cur if r["beta"] == beta and r["kind"] == "sigma_T" and r["used"] == "1"]
        assert used, f"the curves artifact marks no read window at beta={beta}"
        tmax = max(used, key=lambda r: int(r["x"]))
        assert row["t_read"] == tmax["x"], (
            f"at beta={beta} the table reads at T={row['t_read']} but the curve's window ends at "
            f"T={tmax['x']}")
        assert abs(float(row["a2sigma_potential"]) - float(tmax["value"])) < 5e-5, (
            f"at beta={beta} the table reports sigma={row['a2sigma_potential']} but the curve at "
            f"T={tmax['x']} is {tmax['value']}")
        assert abs(float(row["a2sigma_err"]) - float(tmax["err"])) < 5e-5, (
            f"at beta={beta} the table's error {row['a2sigma_err']} is not the curve's "
            f"{tmax['err']} at the read window")

    # the window must actually be a window, not a single point, or "residual T-dependence" is empty
    for beta in tab:
        used = [r for r in cur if r["beta"] == beta and r["kind"] == "sigma_T" and r["used"] == "1"]
        assert len(used) >= 2, (
            f"beta={beta} has a one-point read window; Sec 8.8's systematic is the spread across "
            "the window, which needs at least two")


def test_the_gap_scale_quotes_no_imported_coefficient():
    """The bore relation is stated as a scaling, never with an imported coefficient.

    Sec 6 says the relation "fixes the scaling ... It does not fix the coefficient", and every
    measured comparison uses the pi-free 3.59*sqrt(sigma) taken from Sec 8.8. Five passages
    nonetheless asserted the gap's VALUE as Delta ~ pi*sqrt(sigma), including the blockquote titled
    "The gap, stated precisely" -- quoting a constant the paper elsewhere disclaims, and one that
    differs from the measured 3.59 by 14%.

    A coefficient the paper does not read must not reappear on the gap scale.
    """
    BS = chr(92)
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())

    banned = BS + "pi" + BS + "sqrt" + BS + "sigma"
    assert banned not in flat, (
        "the gap scale is quoted with an imported pi coefficient; Sec 6 says the bore relation does "
        "not fix a coefficient, and the measured scale is 3.59*sqrt(sigma)")

    # the scaling statement itself must still be there -- removing the coefficient must not have
    # removed the relation
    scaling = BS + "Delta" + BS + "propto" + BS + "sqrt" + BS + "sigma"
    n = flat.count(scaling)
    assert n >= 5, f"the bore scaling is stated {n} times; it carries the gap's scale in Sec 2, 6, 8 and 12"

    # and the measured pi-free scale must still be named
    assert f"3.59{BS}sqrt{BS}sigma" in flat, \
        "the paper no longer names the measured pi-free scale it compares against"


def test_every_panel_a_figure_draws_is_described_in_its_caption():
    """A caption names every panel its script draws.

    Figure 8's script draws four panels and its caption described three: panel D, the volume scan
    carrying the L-independence the uniform-in-volume argument rests on, had no caption text at all.
    A reader reaching it finds an undescribed panel, and nothing else notices -- the figure exists,
    the embed resolves, and the caption reads as complete.

    Panels are taken from the axis names the script binds (axA, axB, ...), so this follows what is
    drawn rather than what a docstring claims.
    """
    import re

    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    checked = 0
    for script in sorted((REPO / "research" / "data").glob("*_fig_*.py")):
        src = script.read_text(encoding="utf-8", errors="replace")
        drawn = sorted(set(re.findall(r"\bax([A-D])\b", src)))
        if len(drawn) < 2:
            continue                       # single-panel figures carry no panel letters
        png = script.name.replace(".py", ".png")
        i = flat.find(f"(data/{png})")
        assert i != -1, f"{png} is not embedded in the paper"
        j = flat.find("**Figure", i)
        assert j != -1, f"no caption follows {png}"
        cap = flat[j:j + 1400]
        for panel in drawn:
            # both spellings the paper uses: "**A**" / "**A:**" and "**(a)**"
            marks = (r"\*\*" + panel + r"(?:\*\*|[:.])",
                     r"\*\*\(" + panel.lower() + r"\)\*\*")
            assert any(re.search(m, cap) for m in marks), (
                f"{script.name} draws panel {panel} but the caption for {png} does not describe it")
        checked += 1
    assert checked >= 2, f"only {checked} multi-panel figures were checked"


def test_stated_ensemble_sizes_match_their_artifacts():
    """Every ensemble size a caption or ledger row states is the one its artifact records.

    Four claims, three artifacts: Figure 7 and Figure 9 each say 512 configurations, and the Figure
    10 caption and the Sec 13 ledger row both say n >= 96. A configuration count is the first thing
    a reader weighs a measurement by, and it is the number most likely to survive a regeneration
    unchanged in the prose -- the artifacts carry it per row, the paper carries it once.

    The n >= 96 bound is checked as the artifact's MINIMUM, so it stays tight: a bound that is
    merely true would still be satisfied by 96 if the smallest ensemble grew to 120.
    """
    BS = chr(92)
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())

    meta = _artifact("8_7_dat_meta.csv")[0]
    ten = _artifact("8_8_dat_string_tension.csv")
    d2 = _artifact("9_1_dat_d2_certified.csv")

    # Each caption is checked against ITS OWN artifact. Both happen to state 512, so a single
    # "512 configurations appears in the paper" match is satisfied by either and cannot tell that
    # the other has drifted.
    def caption_for(png):
        i = flat.find("(data/" + png + ")")
        assert i != -1, png + " is not embedded in the paper"
        j = flat.find("**Figure", i)
        assert j != -1, "no caption follows " + png
        return flat[j:j + 1200]

    transfer_n = int(meta["nconfigs"])
    assert f"{transfer_n} configurations" in caption_for("8_7_fig_transfer_gap.png"), \
        f"the transfer-gap caption does not state {transfer_n} configurations"
    ten_n = {int(r["ncfg"]) for r in ten}
    assert len(ten_n) == 1, f"the string-tension table spans several ensemble sizes: {sorted(ten_n)}"
    n_ten = ten_n.pop()
    assert f"{n_ten} configurations" in caption_for("8_8_fig_string_tension.png"), \
        f"the string-tension caption does not state {n_ten} configurations"

    # The count is stated four times -- each caption and each section's prose -- and both
    # measurements happen to use the same ensemble size, so every per-ensemble claim in the paper
    # must be that size. The two release totals are the deposit's and are checked elsewhere.
    assert_every_statement(flat, r"(?<![,}])(\d{3}) configurations", str(transfer_n),
                           "the per-ensemble configuration count", minimum=4)

    # the "n >= 96" bound, which must be the artifact's minimum
    lo = min(int(r["nconfigs"]) for r in d2)
    # "$n\ge" with the delimiter: a bare "n\ge" also matches "$w_n\ge0$", the
    # reflection-positivity spectral form, a different statement entirely. The bound must be the
    # artifact's MINIMUM, so it stays tight rather than merely true.
    assert_every_statement(flat, re.escape("$n" + BS + "ge") + r"(\d+)", str(lo),
                           "the d2 read n >= bound", minimum=2)


def test_every_beta_star_interval_is_the_certified_one():
    """The strong-coupling threshold is stated with one interval throughout.

    `beta_star_enclosure.py` brackets it directly -- B(0.749) < kappa_0 < B(0.750) -- and the paper
    states that in five places. A sixth form, kappa_0/(2r) evaluated over the conservative r
    bracket, is looser: its upper end sits above 0.750 and so contradicts the bound the same script
    certifies. The tighter bracket is the one the argument uses, and the margin to beta_KP is
    measured from it.
    """
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    BS = chr(92)
    pat = re.escape(BS + "beta_" + BS + "star") + r".{0,26}?in.?[\[(](\d\.\d+),\s*(\d\.\d+)[\])]"
    hits = [(m.group(1), m.group(2)) for m in re.finditer(pat, flat)]
    assert len(hits) >= 4, f"the threshold is stated {len(hits)} times; the paper carries it at least 4"
    for lo, hi in hits:
        assert (lo, hi) == ("0.749", "0.750"), (
            f"the paper states beta_star in ({lo}, {hi}); beta_star_enclosure.py certifies "
            "(0.749, 0.750), and a looser interval whose upper end exceeds 0.750 contradicts it")


def test_string_tension_pulls_are_computed_from_the_table():
    """Sec 8.8's pull column is what the measurement and the quoted literature value give.

    The table reports, per coupling, the measured a^2 sigma with its statistical and systematic
    errors, the literature value, and the agreement in sigma. The literature value is a citation and
    cannot be derived here, but the PULL can: (measured - literature) / sqrt(stat^2 + syst^2). It is
    the column a referee reads first and the only one that was unchecked.

    Recomputing it also ties the three columns together: a drift in the measurement, in either
    error, or in the quoted literature value changes the pull, so the row cannot be internally
    inconsistent without failing here.
    """
    import math

    rows = {float(r["beta"]): r for r in _artifact("8_8_dat_string_tension.csv")}
    BS = chr(92)
    checked = 0
    for line in PAPER.read_text(encoding="utf-8").split(chr(10)):
        if not line.startswith("| 2."):
            continue
        cells = _cells(line)
        if len(cells) < 5:
            continue
        try:
            beta = float(cells[0])
        except ValueError:
            continue
        if beta not in rows:
            continue
        lit = re.search(r"approx([0-9.]+)", cells[3])
        stated = re.search(r"([+-]?[0-9.]+)" + re.escape(BS + "sigma"), cells[4])
        assert lit and stated, f"the beta={beta} row is missing its literature value or pull"
        r = rows[beta]
        err = math.hypot(float(r["a2sigma_err"]), float(r["a2sigma_syst"]))
        pull = (float(r["a2sigma_potential"]) - float(lit.group(1))) / err
        assert abs(pull - float(stated.group(1))) < 0.06, (
            f"at beta={beta} the row states {stated.group(1)} sigma, but the measurement "
            f"{r['a2sigma_potential']} against {lit.group(1)} with total error {err:.5f} gives "
            f"{pull:+.2f}")
        checked += 1
    assert checked >= 3, f"only {checked} coupling rows were checked; the table carries three"


def test_string_tension_artifact_is_internally_consistent():
    """The columns 8_8_dat_string_tension.csv derives from others agree with them.

    `sqrt_sigma` is sqrt(a2sigma_potential) and `t_read` indexes the curve the value is taken from.
    Neither is quoted in the paper -- `sqrt_sigma` feeds the Sec 8.8 scaling test, which divides it
    by a*Lambda -- so nothing else would notice them disagreeing with the column they come from.

    A full regeneration keeps them consistent because one computation produces both. What this
    catches is the other case: a hand-edited cell, or a partial regeneration that rewrites some
    columns and not others.
    """
    import math

    rows = _artifact("8_8_dat_string_tension.csv")
    assert rows, "the string-tension artifact is empty"
    for r in rows:
        s = float(r["a2sigma_potential"])
        assert s > 0, f"beta={r['beta']}: a2sigma_potential is not positive"
        stated = float(r["sqrt_sigma"])
        assert abs(stated - math.sqrt(s)) < 5e-4, (
            f"beta={r['beta']}: sqrt_sigma is {stated} but sqrt({s}) = {math.sqrt(s):.5f}")
        # the systematic is the spread across the read window, so it cannot be zero where the
        # window holds more than one point
        assert float(r["a2sigma_syst"]) > 0, (
            f"beta={r['beta']}: the systematic is zero; Sec 8.8 derives it from the residual "
            "T-dependence across the read window")
        assert int(r["t_read"]) >= 1, f"beta={r['beta']}: t_read is not a time extent"


def test_transfer_pencil_errors_are_the_artifact_s():
    """The Sec 8.7 pencil table's uncertainties, not just its central values.

    The table writes each entry as `0.356(85)` -- 0.356 with an uncertainty of 85 in the last two
    decimals, so 0.085. The central values were checked; the parenthetical errors were not, and the
    paper's claim is that n=2,3 are ISOLATED below the vacuum, which is a statement about separation
    relative to those errors. An error could double without anything objecting while the isolation
    claim silently weakened.

    Entries marked with a dagger carry no error in the table and are skipped here; the artifact
    records their errors and the isolation column covers them.
    """
    rows = {(r["smearing"], r["n_moment"]): r for r in _artifact("8_7_dat_transfer_pencil.csv")}
    assert rows, "the pencil artifact is empty"

    checked = []
    for line in PAPER.read_text(encoding="utf-8").split(chr(10)):
        if not re.match(r"\|\s*\d+\s*\|.*\(\d+\)", line):
            continue
        cells = _cells(line)
        smear = cells[0].strip()
        for n_moment, cell in zip(("2", "3", "4"), cells[1:4]):
            m = re.search(r"(\d\.\d+)\((\d+)\)", cell)
            if not m:
                continue                      # a dagger entry: no error quoted
            key = (smear, n_moment)
            assert key in rows, f"the table has smearing {smear} n={n_moment}; the artifact does not"
            r = rows[key]
            dec = len(m.group(1).split(".")[1])
            stated_err = int(m.group(2)) * 10 ** (-dec)
            # compared at the precision the table writes: several entries are half-way cases
            # (0.3675 to three decimals), where a tolerance of half the last digit sits exactly on
            # the boundary and the comparison turns on floating-point representation
            assert m.group(1) == format(float(r["lambda1"]), "." + str(dec) + "f"), (
                f"smearing {smear} n={n_moment}: the table states lambda_1 = {m.group(1)}, the "
                f"artifact {r['lambda1']}")
            assert abs(stated_err - float(r["lambda1_err"])) < 6e-4, (
                f"smearing {smear} n={n_moment}: the table states an error of {stated_err:.4f} "
                f"({m.group(2)} in the last {dec} decimals), the artifact {r['lambda1_err']}")
            checked.append(key)
    assert len(checked) >= 6, (
        f"only {len(checked)} value(error) entries were checked; the table carries several per "
        "smearing across four moment orders")


def test_centre_dominance_artifact_carries_what_the_lean_hypothesis_needs():
    """9_7 supplies the runtime evidence for `CentreDominance.string_tension_eq_centre`'s hypothesis.

    The Lean theorem is an assembly: given `P_n/A_n -> 0`, the per-area free energy tends to the
    centre tension, `sigma_SU(N) = sigma_Z`. It carries foundation axioms only -- the physics is the
    hypothesis, and `certify/string_tension_eq_centre.py` is what measures it, through two reads:

      Input 3  rho'_coset(1) < 1  -- the non-centre (coset) contribution is perimeter/short-range,
                                     which is what makes P/A vanish.
      Input 4  sigma_Z/sigma      -- centre dominance, order unity.

    Input 3 is checked at every coupling because the script states it without qualification. Input 4
    is checked only where sigma resolved and only in the scaling window: a chi(R,R) Creutz ratio
    needs Wilson loops the ensemble resolves, and at strong coupling W ~ (beta/4)^area sits under the
    noise, so unresolved rows there are expected rather than a defect. The band on Input 4 is a
    factor of two either side of 1 -- wide enough that it is not a tuned cut, narrow enough to
    separate "the centre carries the tension" from "the two are unrelated" (beta=1.40, outside the
    window, reads 6.5).
    """
    path = DATA / "9_7_dat_centre_dominance.csv"
    if not path.exists():
        pytest.skip("9_7_dat_centre_dominance.csv not regenerated yet (string_tension_eq_centre is gpu)")
    rows = _artifact("9_7_dat_centre_dominance.csv")

    for col in ("beta", "nconfigs", "L", "rho1_coset", "sigma_full", "sigma_Z", "Z_over_full"):
        assert col in rows[0], f"the centre-dominance table has no {col} column"

    # Input 3: stated without qualification, so it must hold everywhere.
    bad = [(r["beta"], r["rho1_coset"]) for r in rows if not 0.0 <= float(r["rho1_coset"]) < 1.0]
    assert not bad, (
        f"rho'_coset must be in [0,1) at every coupling -- the coset being short-range is what makes "
        f"P/A vanish. These are not: {bad}")

    # Input 4: only where it resolved, and only in the scaling window.
    resolved = [r for r in rows if r["Z_over_full"] not in ("", None)]
    assert resolved, (
        "no coupling resolved sigma_Z/sigma: the table carries no centre-dominance measurement, "
        "which is the one thing this certificate exists to supply")

    window = [r for r in resolved if float(r["beta"]) >= 2.0]
    assert len(window) >= 2, (
        f"only {len(window)} scaling-window couplings resolved sigma_Z/sigma; centre dominance is a "
        f"statement about the window, not a single point")
    off = [(r["beta"], r["Z_over_full"]) for r in window
           if not 0.5 <= float(r["Z_over_full"]) <= 2.0]
    assert not off, (
        f"sigma_Z/sigma is not order unity in the scaling window: {off}. Centre dominance says the "
        f"centre carries the string tension; a ratio outside a factor of two says it does not.")
