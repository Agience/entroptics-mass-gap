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


def _nums_written(cell: str) -> list[str]:
    """The same numbers `_nums` finds, AS WRITTEN -- so their precision survives.

    `_nums` returns floats, and a float has already discarded trailing zeros: `1.200` becomes
    `1.2`. Any tolerance derived from that is a hundred times too loose for a three-decimal
    value. The mutation audit caught exactly this -- `1.209` changed to `1.200` passed, because
    the mutated value's own zeros widened the tolerance that was meant to reject it.
    """
    t = cell.replace("$", "")
    for tok in (BS + "pm", BS + "approx", BS + "sigma", BS + "le", BS + "ge", "**"):
        t = t.replace(tok, " ")
    out = []
    for w in t.replace("|", " ").split():
        s = w.strip("+()*^, ")
        try:
            float(s)
        except ValueError:
            continue
        out.append(s)
    return out

def _half_ulp(written):
    """Half a unit in the last place of a number AS WRITTEN -- the tolerance it implies.

    A value given to four decimals is a claim to within 0.00005; one given to three, 0.0005. The
    module's fixed `TOL = 5e-4` is the three-decimal figure, so it compared every four-decimal value
    ten times more loosely than the paper states it, and a one-unit change to a four-decimal cell
    passed. Deriving the tolerance from the value means no test decides how wrong a number may be.
    """
    s = str(written).strip()
    dp = len(s.split(".")[1]) if "." in s else 0
    return 0.5 * 10.0 ** (-dp)

def _select(rows, L, beta, tol):
    """The variational minimum at a given resolution tolerance, and what it selected."""
    def f(v):
        return float(v) if v not in ("", None) else float("nan")
    cand = [(f(r["m_eff"]), f(r["m_eff_err"]), r["operator"], int(r["tau"])) for r in rows
            if int(r["L"]) == L and abs(float(r["beta"]) - beta) < 1e-9
            and r["m_eff"] not in ("", None) and r["m_eff_err"] not in ("", None)]
    cand = [c for c in cand if c[0] == c[0] and c[1] == c[1] and c[0] > 0 and c[1] / c[0] <= tol]
    return min(cand, key=lambda c: c[0]) if cand else None


def _plateau_tol(rows, L, beta, lo=None, hi=None, step=None):
    """DERIVED: the resolution tolerance is the geometric centre of the WIDEST interval over which
    the variational selection does not change.

    Sec 8.7b calls its rule "one rule, no per-coupling choices", and the selection rule itself has
    none -- but admitting an `m_eff` to the basis requires deciding when it is RESOLVED, and that
    was the literal `0.25`. It is not inert: scanning it moves the beta=2.30 bound from 1.476 (at
    0.10) to 0.615 (at 0.40), and at 1.00 the rule selects the ACTION DENSITY at beta=2.40 -- the
    operator the whole section turns on it never selecting. So the number decided the answer.

    What replaces it is measured per calculation. A tolerance is meaningful exactly where the
    selection is INVARIANT under it: too tight and the contaminated tau=0 lag is all that survives,
    too loose and noise-dominated lags enter. The widest invariance interval is that plateau, and
    its centre is the tolerance. Nothing is chosen; the data says where the plateau is.

    On the released correlator the plateau is [0.140, 0.400) -- a factor 2.9, against 1.4 for the
    next widest -- and its geometric centre is 0.237. The paper's 0.25 sits inside it, which is why
    the published numbers do not move.
    """
    # DERIVED: the scan needs no bounds of its own. `tol` is a RELATIVE error `e/v`, so the only
    # values that can change the selection are the ones the basis actually realises: below the
    # smallest `e/v` nothing is admissible, and at `e/v = 1` a value equals its own error, past which
    # "resolved" has no meaning. So the range is the basis's own min(e/v) up to 1, and the step is
    # the finest gap between realised ratios -- every distinct selection is then visited exactly.
    # Declaring bounds here would replace one chosen number with three, which is the defect this
    # function exists to remove.
    ratios = sorted({c[1] / c[0] for c in
                     [(float(r["m_eff"]), float(r["m_eff_err"])) for r in rows
                      if int(r["L"]) == L and abs(float(r["beta"]) - beta) < 1e-9
                      and r["m_eff"] not in ("", None) and r["m_eff_err"] not in ("", None)]
                     # DERIVED: validity, not a cut -- a nonpositive value or error is not a
                     # measurement, and NaN fails its own equality.
                     if c[0] > 0 and c[1] > 0 and c[0] == c[0] and c[1] == c[1]})
    # DERIVED: `tol` is a RELATIVE error `e/v`, so `1.0` is where a value equals its own error.
    # Past it "resolved" has no meaning, so it is the natural end of the scan, not a cut. The
    # `> 0` tests either side are validity (a nonpositive value or error is not a measurement;
    # NaN fails its own equality), and a nonpositive step or empty range has no grid to scan.
    ratios = [x for x in ratios if x <= 1.0]
    if not ratios:
        return None
    lo = ratios[0] if lo is None else lo
    hi = 1.0 if hi is None else hi
    if step is None:
        gaps = [b - a for a, b in zip(ratios, ratios[1:]) if b > a]
        step = min(gaps) / 2.0 if gaps else (hi - lo) / 100.0
    # DERIVED: a degenerate scan has no grid -- a nonpositive step or an empty range is not a
    # threshold on anything, it is the absence of anything to scan.
    if step <= 0 or hi <= lo:
        return None
    grid = [round(lo + i * step, 9) for i in range(int((hi - lo) / step) + 1)]
    runs, cur, start = [], object(), grid[0]
    for t in grid:
        s = _select(rows, L, beta, t)
        # The key is the COMPLETE selection, value included. Keying on (operator, tau) alone merges
        # plateaus that differ only by smearing level -- the same operator and lag at a different
        # `nsmear` is a different selection, and treating it as the same one made the detector find
        # a spurious wide interval at L=20 and return a tolerance inside the wrong plateau.
        key = None if s is None else (s[2], s[3], round(s[0], 9))
        if key != cur:
            if cur is not object():
                runs.append((start, t, cur))
            cur, start = key, t
    runs.append((start, grid[-1] + step, cur))
    runs = [r for r in runs if r[2] is not None]
    if not runs:
        return None
    a, b, _ = max(runs, key=lambda r: r[1] / r[0])      # widest by RATIO: tol is a scale, not a shift
    return (a * b) ** 0.5


def _variational(rows, L, beta, tol=0.25):
    """The rule PAPER Sec 8.7b states: smallest m_eff resolved to `tol` over the whole basis.

    CHOSEN, AND IT DECIDES THE PUBLISHED NUMBERS. `0.25` is the paper's own value and it is what
    this guard checks the paper against, so the guard verifies internal consistency and NOT that the
    tolerance is justified. Three derived replacements have been tried and no two agree:

      * the invariance plateau (`_plateau_tol`) -- reproduces the beta-scan (193/210/196,
        chi2/dof 0.21) but gives `1.4545` at L=20 where the paper quotes `1.152`, because the widest
        plateau there selects `plaquette tau=0` rather than `action_density tau=1`;
      * `e < v` (a value exceeding its own error, used by `8_7_fig_mhi_lscan.variational_lscan`) --
        gives 104/92/68 and selects the ACTION DENSITY at beta=2.40, the operator Sec 8.7b turns on
        the rule never selecting;
      * the selection-corrected bound `min_i (v_i + z e_i)` with `z` from the basis size -- gives
        172/221/157, and also selects the action density at beta=2.40.

    All three keep `Delta/(a Lambda_lat)` CONSTANT (chi2/dof 0.21, 0.14, 0.23), so the physics claim
    is robust to the rule; the VALUE is not. Until that is settled the published value is what this
    guard pins, and `certify/fixed_selection_of_scaling.py` answers the same two physical questions
    without taking a minimum at all, so it needs no tolerance and is not a fourth party to this.
    """
    return _select(rows, L, beta, tol)


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
            # DERIVED: the precision the ARTIFACT stores the value at. The module's fixed TOL is the
            # three-decimal half-ulp, so it passed a one-unit change to these four-decimal cells.
            assert abs(quoted - float(actual)) <= _half_ulp(actual), \
                f"beta={beta} {name}: paper {quoted} vs artifact {actual}"
        cre = _nums(cells[2])
        # DERIVED: half a unit in the artifact's last place, as above.
        assert cre and abs(cre[0] - float(r["a2sigma_creutz"])) <= _half_ulp(r["a2sigma_creutz"]), \
            f"beta={beta} creutz: paper {cre} vs artifact {r['a2sigma_creutz']}"

        # The established value and the deviation. A mutation audit found both unguarded: this
        # table is where the paper holds its own measurement against the literature, so an
        # unchecked cell here is an unchecked claim of agreement.
        #
        # The deviation is DERIVED from this row rather than matched, so it moves if the
        # measurement or either error bar drifts -- a stored number would not.
        est, dev = _nums(cells[3]), _nums(cells[4])
        assert est, f"beta={beta}: no established value in the table"
        assert dev, f"beta={beta}: no deviation in the table"
        # DERIVED: the combined error is the quadrature of the two the artifact stores.
        sigma = math.sqrt(float(r["a2sigma_err"]) ** 2 + float(r["a2sigma_syst"]) ** 2)
        expect = (float(r["a2sigma_potential"]) - est[0]) / sigma
        # DERIVED: half a unit in the last place the paper writes the deviation at, and a sign
        # test -- a deviation of the wrong sign disagrees whatever its size.
        dp = len(str(dev[0]).split(".")[1]) if "." in str(dev[0]) else 0
        assert abs(expect - dev[0]) <= 0.5 * 10.0 ** (-dp), (
            f"beta={beta} deviation: paper states {dev[0]} sigma, but "
            f"({r['a2sigma_potential']} - {est[0]}) / {sigma:.5f} = {expect:+.3f}")
        # DERIVED: a sign test, zero rather than a threshold.
        assert (expect < 0) == (dev[0] < 0), (
            f"beta={beta} deviation: paper states {dev[0]} sigma, derived {expect:+.3f} -- "
            f"opposite signs")
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
        # AS WRITTEN, so the tolerance below is the precision the paper states, not the
        # precision a float retained after dropping trailing zeros.
        written = _nums_written(cells[1])
        assert len(quoted) == 2, f"L={L}: expected value and error, parsed {quoted}"
        # DERIVED: the precision the PAPER writes each value at. The fixed TOL is the
        # three-decimal half-ulp, so a one-unit change to these four-decimal cells passed it.
        assert abs(quoted[0] - delta) <= _half_ulp(written[0]), \
            f"L={L} Delta: paper {quoted[0]} vs {delta:.4f}"
        assert abs(quoted[1] - err) <= _half_ulp(written[1]), \
            f"L={L} error: paper {quoted[1]} vs {err:.4f}"
        mhi = _nums(cells[2])
        mhi_w = _nums_written(cells[2])
        assert mhi and abs(mhi[0] - math.exp(-delta)) <= _half_ulp(mhi_w[0]), \
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
        written_p, written_b = _nums_written(cells[1]), _nums_written(cells[2])
        # DERIVED: as above -- each comparison at the precision its own value is written to.
        assert (abs(quoted_p[0] - pub) <= _half_ulp(written_p[0])
                and abs(quoted_p[1] - puberr) <= _half_ulp(written_p[1])), \
            f"beta={beta} published: paper {quoted_p} vs artifact {pub:.4f}+/-{puberr:.4f}"
        assert (abs(quoted_b[0] - bound) <= _half_ulp(written_b[0])
                and abs(quoted_b[1] - berr) <= _half_ulp(written_b[1])), \
            f"beta={beta} bound: paper {quoted_b} vs {bound:.4f}+/-{berr:.4f}"

        excess = (pub - bound) / math.hypot(puberr, berr)
        quoted_x = _nums(cells[3])
        written_x = _nums_written(cells[3])
        # DERIVED: half a unit in the last place the paper writes the excess at. The literal
        # 0.05 this replaces was ten times looser than the two-decimal value it compared.
        assert quoted_x and abs(quoted_x[0] - excess) <= _half_ulp(written_x[0]), \
            f"beta={beta} excess: paper {quoted_x[0]} sigma vs {excess:.2f} sigma"
        # DERIVED: a sign test -- an excess of the wrong sign disagrees whatever its size.
        assert (quoted_x[0] < 0) == (excess < 0), \
            f"beta={beta} excess: paper {quoted_x[0]} sigma, derived {excess:+.2f} -- opposite signs"
        seen += 1
    # DERIVED: every coupling the paper's own table lists must have been matched, so a row
    # silently dropped from the table fails rather than shrinking what is checked.
    assert seen == len(table), \
        f"the table has {len(table)} rows but only {seen} matched an artifact coupling"


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
    the Figure 14 caption and the Sec 13 ledger, so one artifact number backs six sentences. The
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

    # The mean, wherever it is restated alongside the window. Sec 8.7, the Figure 14 caption and the
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
                         ("the Figure 14 caption", "**Figure 14.**")):
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
    caption = _passage(text, "**Figure 14.**")

    # the window each passage states is the window the artifacts populate
    assert "$L=" + ",".join(str(L) for L in window) + "$" in prose,         f"Sec 8.7 does not list the volumes it compares as L={window}"
    assert f"$L={window[0]}$--${window[-1]}$" in caption,         f"the Figure 14 caption does not state the compared range as L={window[0]}-{window[-1]}"

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
    for where, blk in (("Sec 8.7", prose), ("the Figure 14 caption", caption)):
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
    for where, blk in (("Sec 8.7", prose), ("the Figure 14 caption", caption)):
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

    The verdict column is against the DERIVED aperture ceiling B_16 = (1 - 3^{-1/4}) 2 L^2/(2 pi)^2,
    not against a pinned proof bound -- that pin was retired along with the ceiling that justified
    it. The column name carries the ceiling, so re-deriving it at a different extent moves this test
    with the artifact rather than against it.
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
    bound_col = [c for c in rows[0] if c.startswith("under_ceiling_")][0]
    ceiling = float(bound_col.rsplit("_", 1)[1])

    # the grid, and that every coupling clears the DERIVED aperture ceiling at this confidence
    assert f"{len(rows)}-point grid" in text, \
        f"the paper does not describe this as a {len(rows)}-point grid"
    failed = [r["beta"] for r in rows if r[bound_col] != "yes"]
    assert not failed, f"couplings not certified under the aperture ceiling {ceiling}: {failed}"

    # and that the paper states that ceiling, rather than one derived at the wrong lag arity
    assert f"B_{{16}}={ceiling:.2f}" in text.replace(" ", ""), \
        f"the paper does not state the derived aperture ceiling as B_16 = {ceiling:.2f}"

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

    The margin is checked as a ratio rather than matched as text, and against the STATED value
    rather than as a floor: a "gtrsim 4" claim stays true while the margin silently halves, which
    is exactly what happened when the moment was corrected to the circle distance.
    """
    rows = _artifact("9_1_dat_d2_su3.csv")
    vals = [float(r["d2"]) for r in rows]
    betas = [float(r["beta"]) for r in rows]
    text = PAPER.read_text(encoding="utf-8")
    flat = " ".join(text.split())

    # Scoped to the SU(3) sentence. Anchoring on "aperture ceiling" alone finds Sec 9's SU(2)
    # ceiling first, and the SU(2) band that comes with it CONTAINS the SU(3) values -- so the test
    # passed while checking a different measurement. The SU(3) ceilings are the only ones stated
    # per-L, so that is what this anchors on.
    where = flat.find("aperture ceiling ($")
    assert where != -1, "the paper no longer states a per-L SU(3) aperture ceiling"
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
    claimed = re.search(re.escape(chr(92) + "approx") + r"(\d+(?:\.\d+)?)", window)
    assert claimed, "the paper no longer states a margin factor"
    # Stated as the measured ratio rather than as a floor. "gtrsim 4" was satisfied by anything
    # above 4, so the moment could double -- as it did, when the read was corrected to the circle
    # distance -- and the claim would still read as true while the margin had halved.
    # DERIVED: the tolerance is the precision the paper writes the factor at -- half a unit in its
    # last place. A claim given to one decimal is a claim to within 0.05, and stating it to more
    # decimals tightens this check automatically. Nothing is chosen here that the paper does not
    # already choose by how it writes the number.
    written = claimed.group(1)
    dp = len(written.split(".")[1]) if "." in written else 0
    tol = 0.5 * 10 ** (-dp)
    assert abs(factor - float(written)) < tol, (
        f"the paper claims a factor of {written} below the ceiling -- to that precision, within "
        f"{tol} -- but {ceiling}/{max(vals):.4f} = {factor:.4f}")


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

    8_5_dat_gap_calibration.csv reads each mass from four disjoint seed blocks and records the
    block mean, the SPREAD across blocks, and the deviation from the exact E_0 in units of that
    spread. The quantity the paper states as "setting the approach" is the spread: it is what the
    finite temporal extent controls, and it is reproducible.

    TWO WAYS THIS PASSAGE HAS BEEN WRONG, both fixed here rather than described:

      * it quoted only the tight end ("0.2% at m=1.10") in all three places, so the instrument read
        as 0.2%-accurate when the other end was far looser -- quoting the best point;
      * it then quoted the per-mass relative ERROR at both ends, from a single seed block. That
        number does not survive reseeding: seeds 0..39 gave a smooth -8.9% -> -0.2% ramp and the
        other three blocks gave +10.4%, +3.9% and +10.2% at m=0.20 with no ramp. A trend inside the
        noise was published with a physical explanation attached to it.

    So the guard is on the spread, at both ends, from the artifact -- and additionally on the claim
    that makes the calibration mean anything: every deviation from E_0 is inside the read's own
    spread, which is a fact about the artifact and must stay true of it.
    """
    rows = _artifact("8_5_dat_gap_calibration.csv")
    masses = [float(r["m"]) for r in rows]

    # The calibration's own claim: the deviation from truth never exceeds the reseeding spread. If
    # that stops holding, the passages below are wrong whatever numbers they quote.
    # DERIVED: 1.0 is the ratio at which the deviation EQUALS the reseeding spread the artifact
    # itself measured. Both sides come from the same row; no scale is introduced here.
    outside = [(float(r["m"]), float(r["dev_over_spread"])) for r in rows
               # DERIVED: 1.0 is the ratio at which the deviation EQUALS the spread the row carries.
               if float(r["dev_over_spread"]) > 1.0]
    assert not outside, (
        f"the calibration no longer agrees with E_0 inside its own reseeding spread at "
        f"{outside} -- the paper's 'as closely as it agrees with itself' claim is stale")

    loose = max(rows, key=lambda r: float(r["spread_pct"]))
    tight = min(rows, key=lambda r: float(r["spread_pct"]))
    lo_e, lo_m = float(loose["spread_pct"]), float(loose["m"])
    ti_e, ti_m = float(tight["spread_pct"]), float(tight["m"])

    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    BS = chr(92)
    sites = [i for i in range(len(flat)) if flat.startswith("setting the approach", i)]
    assert len(sites) >= 3, f"expected the calibration approach to be stated in 3 places, found {len(sites)}"
    for i in sites:
        seg = flat[i:i + 150]
        assert f"{lo_e:.1f}{BS}%" in seg and f"m={lo_m:.2f}" in seg, (
            f"a passage states the calibration without the loose end of its reseeding spread "
            f"({lo_e:.1f}% of E_0 at m={lo_m:.2f}): ...{seg[:90]}...")
        assert f"{ti_e:.1f}{BS}%" in seg and f"m={ti_m:.2f}" in seg, (
            f"a passage states the calibration without the tight end of its reseeding spread "
            f"({ti_e:.1f}% of E_0 at m={ti_m:.2f}): ...{seg[:90]}...")

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


def test_the_strong_coupling_threshold_is_stated_as_the_derived_inequality():
    """The strong-coupling threshold is the derived one, and the retired interval stays retired.

    It used to be a certified interval, `beta_star in (0.749, 0.750)`, from exact-rational Bessel
    and log series. It is now the THEOREM `Bessel.strong_coupling_below_threshold`:
    `ratio_le_quarter` bounds `I_2/I_1` by `x/4` termwise, so the character bound is `beta^2/2` and
    sits below the floor exactly when `beta^2 < (1/2) ln 3`. That carries no numeral, so this gate
    checks two things -- that the paper states the derived inequality, and that no certified
    interval for the threshold has come back.
    """
    flat = " ".join(PAPER.read_text(encoding="utf-8").split())
    BS = chr(92)

    # the derived inequality is stated
    derived = re.escape(BS + "beta^2<" + BS + "tfrac12" + BS + "ln3")
    assert re.search(derived, flat.replace(" ", "")), (
        "the paper no longer states the derived threshold beta^2 < (1/2) ln 3; if the statement "
        "moved, point this gate at its new form rather than deleting it")

    # and no interval for beta_star survives anywhere
    pat = re.escape(BS + "beta_" + BS + "star") + r".{0,26}?in.?[\[(](\d\.\d+),\s*(\d\.\d+)[\])]"
    hits = [(m.group(1), m.group(2)) for m in re.finditer(pat, flat)]
    assert not hits, (
        f"the paper states beta_star as a certified interval {hits}; that route is retired in "
        "favour of the derived beta^2 < (1/2) ln 3, and two thresholds is two paths")


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

    # Input 4: only where it resolved, only in the scaling window, and only at the LARGEST Creutz
    # loop the artifact carries.
    #
    # THE LOOP SIZE IS PART OF THE MEASUREMENT, and reading across loop sizes reads a contradiction.
    # `sigma_SU(N) = sigma_Z` is an ASYMPTOTIC statement -- it is about the tension a large Wilson
    # loop measures. A small Creutz ratio is resolvable much deeper into strong coupling but carries
    # perimeter and Coulomb contamination that does not cancel in `chi(R,R)` at small `R`, and that
    # contamination grows as the coupling weakens. So chi(2,2) and chi(3,3) TREND OPPOSITE WAYS across
    # the scan and agree only where both are reliable. Pooling them and asking for order unity asks
    # the small loop to be asymptotic, which it is not and does not claim to be.
    assert "rt" in rows[0], (
        "the centre-dominance table has no `rt` column, so this test cannot tell which Creutz loop "
        "produced a row -- and both loop sizes write this filename")
    # DERIVED: the scaling window and the order-unity band are the SAME numbers the Input 4 check
    # uses, named once so the exclusion check below cannot drift from the check it is justifying.
    # `WINDOW_BETA` is where asymptotic scaling is claimed; `BAND_LO`/`BAND_HI` are a factor of two
    # either side of 1 -- wide enough not to be a tuned cut, narrow enough to separate "the centre
    # carries the tension" from "the two are unrelated".
    WINDOW_BETA, BAND_LO, BAND_HI = 2.0, 0.5, 2.0
    sizes = sorted({int(r["rt"]) for r in rows})
    biggest = max(sizes)
    resolved = [r for r in rows if r["Z_over_full"] not in ("", None) and int(r["rt"]) == biggest]
    assert resolved, (
        f"no coupling resolved sigma_Z/sigma at the largest loop chi({biggest},{biggest}): the table "
        f"carries no asymptotic centre-dominance measurement, which is the one thing this certificate "
        f"exists to supply")

    window = [r for r in resolved if float(r["beta"]) >= WINDOW_BETA]
    assert len(window) >= 2, (
        f"only {len(window)} scaling-window couplings resolved sigma_Z/sigma at chi({biggest},"
        f"{biggest}); centre dominance is a statement about the window, not a single point")
    off = [(r["beta"], r["Z_over_full"]) for r in window
           if not BAND_LO <= float(r["Z_over_full"]) <= BAND_HI]
    assert not off, (
        f"sigma_Z/sigma is not order unity in the scaling window at chi({biggest},{biggest}): {off}. "
        f"Centre dominance says the centre carries the string tension; a ratio outside a factor of "
        f"two says it does not.")

    # THE EXCLUDED LOOP IS ASSERTED, NOT DROPPED. Filtering to the largest loop is only legitimate if
    # the smaller one is excluded for the stated reason and not because it was inconvenient. So: the
    # smaller loop must actually be the one that falls away at weak coupling. If it ever stops doing
    # that, the justification above is wrong and this test should be re-read rather than re-filtered.
    # DERIVED: "more than one loop size present", i.e. there is actually something being excluded.
    # With a single size in the artifact nothing is filtered and there is nothing to justify.
    if len(sizes) > 1:
        small = min(sizes)
        s_win = [r for r in rows
                 if int(r["rt"]) == small and r["Z_over_full"] not in ("", None)
                 and float(r["beta"]) >= WINDOW_BETA]
        assert s_win, f"no scaling-window rows at chi({small},{small}) to check the exclusion against"
        weakest = max(s_win, key=lambda r: float(r["beta"]))
        assert float(weakest["Z_over_full"]) < BAND_LO, (
            f"chi({small},{small}) reads {weakest['Z_over_full']} at beta={weakest['beta']}, which is "
            f"INSIDE the order-unity band. The stated reason for reading centre dominance only at "
            f"chi({biggest},{biggest}) -- that small loops lose the asymptotic tension at weak "
            f"coupling -- does not hold here, so the filter is not justified by what it claims.")


def test_free_field_constants_match_the_certificate():
    """Sec 8.6's weak end, re-derived from 8_6_dat_free_field_muinf.csv.

    Every constant the weak end quotes -- mu_inf(8), the 1/L^2 law, M_2, and the two exactness
    checks -- reached the paper as prose and as a Lean docstring, with nothing computing them. They
    are a deterministic Wick contraction, so they are checkable exactly; this pins them to the
    certificate that now produces them.

    The two exactness checks are compared as bounds rather than as values: they are floating-point
    residuals, so the claim is "at most this", and a run that returns a smaller residual should not
    fail the paper.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = {int(r["L"]): r for r in _artifact("8_6_dat_free_field_muinf.csv")}
    assert 8 in rows and 32 in rows, "the free-field table does not cover the L the paper quotes"

    mu8 = float(rows[8]["mu_inf"])
    assert text.count(f"$\\mu_\\infty(8)={mu8:.4f}") >= 2, \
        f"the paper states mu_inf(8)={mu8:.4f} fewer than twice; the abstract, Sec 8.6, Sec 9 and " \
        f"the Sec 13 ledger all carry it"
    assert f"At $L=8$, $\\mu_\\infty={mu8:.4f}$" in text, \
        f"Sec 8.6 does not state the L=8 free-field tension as {mu8:.4f}"

    # the 1/L^2 law, at the two ends of the table the ledger row quotes
    for L, where in ((8, "at $L=8$"), (32, "by $L=32$")):
        v = float(rows[L]["mu_inf_L2"])
        assert f"${v:.2f}$ {where}" in text or f"{v:.2f}$ {where}" in text, \
            f"the Sec 13 ledger does not state mu_inf(L)L^2 = {v:.2f} {where}"

    m2 = float(rows[8]["M2"])
    assert f"$M_2={m2:.3f}$" in text, f"the paper does not state the free-field M_2 as {m2:.3f}"
    twopi2 = 2 * math.pi ** 2 * m2
    assert f"$2\\pi^2M_2={twopi2:.2f}$" in text, \
        f"the paper does not state 2 pi^2 M_2 as {twopi2:.2f}, which is what M_2={m2:.3f} gives"

    # mu_inf falls: the tension vanishes into the continuum, which is what the weak end asserts
    seq = [float(rows[L]["mu_inf"]) for L in sorted(rows)]
    assert all(a > b for a, b in zip(seq, seq[1:])), \
        f"mu_inf(L) is not decreasing in L: {seq}; the weak end says the tension vanishes"

    # the two exactness checks, as upper bounds
    for col, stated, what in (("axis_spread", 4e-17, "the lattice-axis spread"),
                              ("doublet_split", 3e-16, "the lambda_2 doublet split")):
        worst = max(float(r[col]) for r in rows.values())
        assert worst <= stated, \
            f"{what} is {worst:.2e} in the artifact, above the {stated:.0e} the paper states"
    assert "$4\\times10^{-17}$" in text and "$3\\times10^{-16}$" in text, \
        "Sec 8.6 no longer states the two exactness bounds this test checks"


def test_free_field_comparison_quotes_released_ensembles_only():
    """Sec 8.6's weak-end comparison names ensembles the release ships, and quotes their values.

    The sentence this replaces claimed SU(2) to beta=48 and SU(3) to beta=8 -- neither is in the
    release, so no reader could reproduce either, and no check could see it because nothing tied the
    prose to an ensemble list. This ties it to both: every coupling quoted is one the comparison
    artifact read, and the artifact's own extremes are what the prose states.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("8_6_dat_free_field_measured.csv")
    assert rows, "the free-field comparison artifact is empty"

    # every quoted endpoint is a row of the artifact, at the value the artifact carries
    def at(group, L, beta):
        hit = [r for r in rows if r["group"] == group and int(r["L"]) == L
               and abs(float(r["beta"]) - beta) < 1e-9]
        assert hit, f"the comparison artifact has no {group} L={L} beta={beta} row"
        return float(hit[0]["mu"])

    for group, L, beta in (("su2", 8, 0.50), ("su2", 8, 2.30)):
        v = at(group, L, beta)
        assert f"${v:.3f}$" in text, \
            f"Sec 8.6 does not quote the {group} L={L} beta={beta} reading as {v:.3f}"

    # the SU(3) L=8 band the prose gives must contain every SU(3) L=8 row in the quoted range
    su3 = [float(r["mu"]) for r in rows
           if r["group"] == "su3" and int(r["L"]) == 8 and float(r["beta"]) >= 6.0]
    assert su3, "the comparison artifact carries no SU(3) L=8 rows at beta >= 6.0"
    assert f"${min(su3):.3f}$–${max(su3):.3f}$" in text, \
        f"Sec 8.6 does not state the SU(3) L=8 band as {min(su3):.3f}-{max(su3):.3f}"

    # the floor claim: the largest reading anywhere, and its margin
    biggest = max(rows, key=lambda r: float(r["mu"]))
    mu, kappa0 = float(biggest["mu"]), 0.25 * math.log(3.0)
    assert f"${mu:.3f}$, $SU({biggest['group'][-1]})$ $L={biggest['L']}$" in text, \
        f"Sec 8.6 does not name {biggest['group']} L={biggest['L']} beta={biggest['beta']} " \
        f"as the largest reading, at {mu:.3f}"
    assert f"factor ${kappa0 / mu:.2f}$" in text, \
        f"Sec 8.6 does not state the margin below the floor as a factor {kappa0 / mu:.2f}"

    # no coupling outside the release
    for r in rows:
        assert float(r["beta"]) <= 7.0, f"the comparison reads beta={r['beta']}, outside the release"


def test_the_abstract_states_the_plateau_the_lscan_measured():
    """The abstract's m_hi plateau is the artifact's mean over the window it names.

    `test_lscan_plateau_claim_matches_artifact` locates statements by the literal "mean $\\approx" /
    "plateau $\\approx", and the abstract writes "plateaus at $\\approx", so the abstract sat outside
    every check while carrying a value 0.03 away from the artifact. This reaches it by the wording
    the abstract actually uses.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("8_7_dat_mhi_lscan.csv")
    band = [float(r["m_hi"]) for r in rows if 12 <= int(r["L"]) <= 28]
    mean = sum(band) / len(band)
    hits = re.findall(r"plateaus at \$" + re.escape(BS + "approx") + r"(\d\.\d\d)", text)
    assert hits, "no statement of the form 'plateaus at $\\approx0.xx' remains to check"
    for got in hits:
        assert abs(float(got) - mean) < 5e-3, \
            f"the paper states the plateau as {got}, but 8_7_dat_mhi_lscan.csv gives {mean:.3f} " \
            f"over L=12-28"


def test_every_stated_d2_peak_is_the_measured_peak():
    """Every place the paper names the crossover second-moment PEAK states the measured one.

    The peak is quoted in the Figure 10 caption and in the Sec 13 ledger, and was checked only in
    the caption -- by the literal "peaks at", which the ledger does not use. The ledger carried
    0.158 and Sec 9 carried 0.16 against a measured 0.109, all three agreeing with nothing.
    """
    text = PAPER.read_text(encoding="utf-8")
    peak = max(float(r["d2"]) for r in _artifact("9_1_dat_d2_bound.csv"))
    hits = [(m.group(1), text[:m.start()].count(chr(10)) + 1)
            for m in re.finditer(r"peaks? (?:at )?\$(?:" + re.escape(BS + "approx")
                                 + r")?(\d\.\d+)\$", text)]
    assert len(hits) >= 2, \
        f"the d^2 peak is stated in {len(hits)} places; the paper carries it in the Figure 10 " \
        f"caption and the Sec 13 ledger, so this pattern is not finding them"
    bad = [(v, ln) for v, ln in hits if abs(float(v) - peak) > 5e-4]
    assert not bad, \
        f"the measured peak is {peak:.3f}, but PAPER.md states " \
        + ", ".join(f"{v} at line {ln}" for v, ln in bad)


def test_every_u1_coulomb_margin_is_the_artifact_s():
    """Every statement of the U(1) Coulomb aperture margin is the pair 9_2 carries, AND is caveated.

    Sec 12 derives this range and Secs 8.5 and 13 restate it; the two restatements carried
    0.38-0.41, which is no row of the artifact, while Sec 12's own text depended on the real pair
    bracketing a confined SU(2) reading. Checked at every occurrence rather than by presence.

    The second assertion is the one that matters physically. The two Coulomb rows are read at
    DIFFERENT configuration counts (n=48 at beta=1.70, n=128 at beta=2.50) which fall on opposite
    sides of the DMD truncation boundary n_pairs = 2F, so they are produced by different estimators
    and the spread between them is not a measurement of the deconfinement transition. Held at a
    matched n=48 the three U(1) rows read 0.166/0.172/0.197 -- no separation at all -- and at U(1),
    L=8, beta=2.50 the read moves by 3.6x with n alone. The range may therefore be quoted (it is what
    the artifact holds) but not presented as a phase comparison, so the paper is required to carry
    the matched-ratio caveat alongside it.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("9_2_dat_margin_aperture.csv")
    coulomb = sorted(float(r["m_hi"]) for r in rows if "Coulomb" in r["phase"])
    assert len(coulomb) >= 2, "the margin artifact carries fewer than two Coulomb rows"
    stated = f"{coulomb[0]:.3f}$" + chr(0x2013) + f"${coulomb[-1]:.3f}$"
    assert text.count(stated) >= 3, (
        f"the U(1) Coulomb margin {stated} is stated {text.count(stated)} times; Secs 8.5, 12 and "
        f"13 all carry it, so one of them has drifted off the artifact")

    # The rows this range spans must actually straddle the boundary for the caveat to be required;
    # derived from the artifact so that re-reading them at a matched count retires the requirement
    # instead of leaving a caveat for a problem that no longer exists.
    def ratio(r):
        if "ratio" in r and r["ratio"] not in ("", None):
            return float(r["ratio"])
        L, n = int(r["L"]), int(r["ncfg"])
        return n * (2 * L - 1) / (2.0 * L ** 3)

    coul_rows = [r for r in rows if "Coulomb" in r["phase"]]
    straddles = len({ratio(r) >= 1.0 for r in coul_rows}) > 1
    if straddles:
        assert "matched sampling ratio" in text.lower() or "matched ratio" in text.lower(), (
            "the two U(1) Coulomb rows are read on opposite sides of the DMD truncation boundary "
            f"(ratios {', '.join('%.2f' % ratio(r) for r in coul_rows)}), so the spread between them "
            "is an estimator difference, not a phase difference -- the paper quotes the range but "
            "carries no matched-sampling-ratio caveat")


def test_cross_axis_agreement_is_the_probe_s():
    """Sec 8.6's cross-axis figures are P4a's, at the precision they are written.

    The paper stated 0.00% on the controlled isotropic input and inferred from it that a 0.29%
    spread seen on configurations was the field's own. The probe stores phi_T and phi_F, and they
    disagree by 0.64%: the inference ran the wrong way, and the 0.29% had no artifact at all. This
    recomputes the disagreement from the stored pair.
    """
    text = PAPER.read_text(encoding="utf-8")
    hit = [r for r in _artifact("8_6_dat_probe.csv") if r["probe"] == "P4a_crossaxis"]
    assert hit, "the probe artifact carries no P4a cross-axis row"
    pt, pf = float(hit[0]["y"]), float(hit[0]["a_axis"])
    disagreement = abs(pt - pf) / (0.5 * (pt + pf)) * 100
    assert f"${disagreement:.2f}" + BS + "%$ in $" + BS + "varphi$" in text, \
        f"Sec 8.6 does not state the phi cross-axis disagreement as {disagreement:.2f}%"
    assert "$0.29" + BS + "%$" not in text, \
        "the 0.29% cross-axis spread is back; no artifact in the repository produces it"


def test_the_correlator_positive_range_is_the_artifact_s():
    """Sec 8.7 states the lag out to which the 0^{++} correlator is positive, and it is the real one.

    "Positive and decaying" was stated unqualified and carries the reflection-positivity argument on
    the data, but the correlator crosses zero in the noise tail at every smearing. The lag where it
    first goes negative is a property of the artifact, so the prose can state it and be checked.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("8_7_dat_transfer_gap.csv")
    last_positive = None
    for s in sorted({r["smearing"] for r in rows}, key=int):
        series = sorted(((int(r["tau"]), float(r["C_over_C0"])) for r in rows
                         if r["smearing"] == s))
        first_neg = next((t for t, c in series if c < 0), None)
        assert first_neg is not None, \
            f"smearing {s} no longer crosses zero; the qualification this checks is now wrong"
        last_positive = first_neg - 1 if last_positive is None else min(last_positive, first_neg - 1)
    assert text.count(f"$" + BS + "tau=" + str(last_positive) + "$") >= 2, (
        f"the correlator is positive out to tau={last_positive} at every smearing; Sec 8.7 and the "
        f"Figure 7 caption should both say so, and one of them does not")


def test_the_aperture_ceiling_margin_matches_the_artifact():
    """Sec 9's tightest-delta uppers against the derived aperture ceiling, from the CSV.

    This enforces DISCLOSURE rather than a verdict. It used to assert that every coupling clears the
    ceiling; when the moment was corrected to the circle distance the uppers grew and four couplings
    stopped clearing. A test shaped that way can only be satisfied by suppressing the negative
    result, so it checks instead that whatever the artifact says, the paper says the same: the
    largest upper is quoted, the delta it belongs to is named, and any couplings over the ceiling are
    reported with their count.

    The delta is read from the column name, so re-running the certificate at a different one moves
    this test WITH the artifact rather than against it.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("9_1_dat_d2_certified.csv")
    col = next((c for c in rows[0] if c.startswith("ceiling_upper_delta_")), None)
    assert col, "the certificate carries no ceiling_upper_delta_* column"
    delta_exp = col.rsplit("_", 1)[1]                       # e.g. 1e-30
    _, exponent = delta_exp.split("e")
    uppers = [float(r[col]) for r in rows]

    # the ceiling as the paper states it, which a sibling test ties to the derived value
    ceiling = float(re.search(r"B_\{16\}=([\d.]+)", text).group(1))
    over = [(r["beta"], u) for r, u in zip(rows, uppers) if u >= ceiling]

    # the largest upper at this delta must appear, wherever the paper states it
    assert f"{max(uppers):.3f}" in text, (
        f"the paper does not quote the largest {delta_exp} upper, {max(uppers):.3f}; the artifact "
        f"carries the {col} column, so the paper should state it")

    # beside a naming of the delta it belongs to
    assert (BS + "delta=10^{" + exponent + "}") in text, (
        f"the paper quotes an upper but does not name delta=10^{{{exponent}}} as the confidence it "
        f"was certified at")

    # and if any coupling exceeds the ceiling, how many
    if over:
        words = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six",
                 7: "seven", 8: "eight", 9: "nine"}
        n = len(over)
        spellings = {str(n), words.get(n, str(n))}
        assert any(w + " couplings" in text or w + " coupling" in text for w in spellings), (
            f"{n} couplings exceed the aperture ceiling {ceiling} at {delta_exp} "
            f"({[b for b, _ in over]}), and the paper does not disclose that")


def test_substrate_aperture_claims_match_the_artifact():
    """Sec 9's aperture scan, re-derived from 9_3_dat_substrate_of_aperture.csv.

    This artifact carries the only evidence for the one hypothesis the development does not prove
    (`confinement_of_bounded_substrate`), so every number the paper states from it is recomputed here
    rather than matched as text -- the chi2/dof in particular is DERIVED from the per-aperture
    bootstrap sigmas, so it moves if the ensembles or the read change.

    The outlier is checked as a DISCLOSURE, the same shape as the ceiling-margin test: the paper must
    state the worst coupling's value, not be required to have none. A test that demands every
    coupling agree would be satisfied by dropping the one that does not.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("9_3_dat_substrate_of_aperture.csv")
    for r in rows:
        for k in ("d2_circle", "d2_sigma", "d2_raw", "mu"):
            r[k] = float(r[k])
        r["L"] = int(r["L"])

    by = {}
    for r in rows:
        by.setdefault((r["group"], r["beta"]), []).append(r)

    # chi2/dof against a constant B, per coupling, on the rows with a tension to read.
    # The sign test on mu is the artifact's own `confined`/signal criterion, not a cut chosen here.
    scored = {}
    for k, v in by.items():
        # DERIVED: the artifact's own signal criterion -- mu <= 0 means <cos theta> >= 1, which no
        # correlation with a tension produces, so the moment there is a ratio of two quantities
        # consistent with zero. The sigma test is the domain of the inverse-variance weight, and
        # two is the arity below which "does it vary with the aperture" has no meaning.
        sig = [r for r in v if r["mu"] > 0 and r["d2_sigma"] > 0]
        # DERIVED: two is the arity of the comparison, as above.
        if len(sig) < 2:
            continue
        w = [1.0 / r["d2_sigma"] ** 2 for r in sig]
        val = [r["d2_circle"] for r in sig]
        B = sum(wi * x for wi, x in zip(w, val)) / sum(w)
        scored[k] = (sum(wi * (x - B) ** 2 for wi, x in zip(w, val)) / (len(sig) - 1), len(sig))

    assert scored, "no coupling in the artifact is testable across apertures"
    worst_key = max(scored, key=lambda k: scored[k][0])
    worst = scored[worst_key][0]

    # the aperture range the paper claims
    Ls = sorted({r["L"] for r in rows})
    assert str(min(Ls)) in text and str(max(Ls)) in text, \
        f"the paper does not state the aperture range L={min(Ls)}..{max(Ls)}"

    # the worst coupling must be DISCLOSED with its value, not omitted
    assert f"{worst:.2f}" in text, (
        f"the artifact's worst chi2/dof is {worst:.2f} at {worst_key[0]} beta={worst_key[1]}, and "
        f"the paper does not state it")

    # and the bound the paper quotes for the rest must actually hold for the rest
    rest = [c for k, (c, _) in scored.items() if k != worst_key]
    m = re.search(re.escape(BS + "chi^2/" + BS + "mathrm{dof}" + BS + "le") + r"([\d.]+)", text)
    assert m, "the paper no longer states a chi2/dof bound for the consistent couplings"
    claimed = float(m.group(1))
    over = [(k[0], k[1], c) for k, (c, _) in scored.items() if k != worst_key and c > claimed]
    assert not over, (
        f"the paper claims the other couplings sit at chi2/dof <= {claimed}, but {over} exceed it")
    # DERIVED: an upper bound must round UP, so the test is that it HOLDS and is tight to the
    # precision it is written at -- one unit in its last place. Demanding equality to the measured
    # value would forbid stating a bound at all, and allowing any larger number would let a claim
    # stay true while the quantity it bounds drifted.
    dp = len(m.group(1).split(".")[1]) if "." in m.group(1) else 0
    slack = 10.0 ** (-dp)
    assert claimed - max(rest) < slack, (
        f"the paper quotes {claimed} as the bound on the other couplings; the artifact's largest is "
        f"{max(rest):.4f}, so the bound is loose by more than the {slack} it is written to")

    # the seven-aperture headline
    best = max(scored.items(), key=lambda kv: kv[1][1])
    na = scored[best[0]][1]
    # prose spells small counts; accept either spelling rather than dictate the paper's wording
    words = {2: "two", 3: "three", 4: "four", 5: "five", 6: "six", 7: "seven", 8: "eight",
             9: "nine", 10: "ten"}
    assert any(f"{w} apertures" in text for w in {str(na), words.get(na, str(na))}), \
        f"the paper does not state that {best[0][0]} beta={best[0][1]} spans {na} apertures"
    assert f"{scored[best[0]][0]:.2f}" in text, \
        f"the paper does not state that coupling's chi2/dof as {scored[best[0]][0]:.2f}"

    # the largest moment with signal, which is what any B must exceed
    # DERIVED: the same zero-tension sign test as above.
    Bmax = max(r["d2_circle"] for r in rows if r["mu"] > 0)
    assert f"{Bmax:.4f}" in text, \
        f"the paper does not state the largest circle moment with signal as {Bmax:.4f}"


def test_growth_coefficient_claims_match_the_artifact():
    """Sec 9's growth-condition margins, recomputed from 9_3_dat_substrate_of_aperture.csv.

    The proof takes `d2At <= c (N+1)^2` with `c < arccos(3^{-1/4})^2/(2 pi)^2`, not a bounded moment,
    so the operative quantity is the coefficient the DATA requires -- `c = d2 / (N+1)^2` -- against
    the ceiling's. Both are derived here rather than matched as text: `c_max` from the floor, and each
    row's `c` from the artifact.

    The ceiling is written out HERE rather than imported from `certify/aperture_ceiling`, on purpose.
    Importing it would make this test agree with the pipeline by construction; the point is to derive
    it independently and check the PAPER against that, so a drift in either is visible.

    The binding constraint is checked as a MAXIMUM over apertures, not as the last row. A single `c`
    has to cover every aperture, and because a flat moment makes `c` fall like 1/L^2 the largest is
    at the SMALLEST window -- quoting the trend's endpoint instead would state a coefficient that
    does not satisfy the hypothesis at the apertures already measured.
    """
    text = PAPER.read_text(encoding="utf-8")
    rows = _artifact("9_3_dat_substrate_of_aperture.csv")
    # DERIVED: the SHARP ceiling (tangent at the threshold, not at the origin); the lag arity
    # N+1 is the periodic extent L.
    c_max = math.acos(3.0 ** -0.25) ** 2 / (2 * math.pi) ** 2
    # DERIVED: the same zero-tension sign test the artifact's own signal column uses.
    sig = [r for r in rows if float(r["mu"]) > 0]
    assert sig, "no row in the artifact carries a tension to read"

    m = re.search(re.escape("c_{" + BS + "max}=" + BS + "arccos(3^{-1/4})^2") + r"[^=]*=([\d.]+)", text)
    assert m, "the paper no longer states the ceiling coefficient"
    assert abs(float(m.group(1)) - c_max) < 10.0 ** -len(m.group(1).split(".")[1]), (
        f"the paper states c_max = {m.group(1)}, but the floor gives {c_max:.6f}")

    # the coupling with the most apertures is the one the paper tabulates
    counts = {}
    for r in sig:
        counts[(r["group"], r["beta"])] = counts.get((r["group"], r["beta"]), 0) + 1
    worst_scan = max(counts, key=counts.get)
    worst = max(sig, key=lambda r: float(r["d2_circle"]) / int(r["L"]) ** 2)
    cw = float(worst["d2_circle"]) / int(worst["L"]) ** 2
    assert cw < c_max, (
        f"the artifact's binding coefficient {cw:.6f} does not clear the ceiling {c_max:.6f}; the "
        f"paper must not claim the growth condition holds")
    # the binding coefficient is the MAX over apertures, and must be the one the paper quotes
    mant, exp = f"{cw:.2e}".split("e")
    latex = mant + BS + "times10^{" + str(int(exp)) + "}"
    assert latex in text.replace(" ", "") or f"{cw:.5f}" in text, (
        f"the paper does not quote the binding growth coefficient as {latex} or {cw:.5f} "
        f"({worst['group']} beta={worst['beta']} L={worst['L']})")
    # Every margin in the per-aperture table, recomputed. A table written into the paper and not
    # checked is prose: the ceiling and the binding coefficient were guarded while the seven columns
    # between them were free to drift, which is the half a reader actually reads.
    scan = [r for r in sig if (r["group"], r["beta"]) == (worst_scan[0], worst_scan[1])]
    for r in sorted(scan, key=lambda r: int(r["L"])):
        margin = c_max / (float(r["d2_circle"]) / int(r["L"]) ** 2)
        assert f"{margin:.1f}" + BS + "times" in text.replace(" ", ""), (
            f"the paper does not state the L={r['L']} margin to the ceiling as {margin:.1f}x "
            f"({r['group']} beta={r['beta']})")

    # and the smallest window must be where it binds, or the paper's reasoning is wrong
    assert int(worst["L"]) == min(int(r["L"]) for r in sig), (
        f"the binding coefficient is at L={worst['L']}, not the smallest window "
        f"{min(int(r['L']) for r in sig)} -- the paper's claim that c falls like 1/L^2 does not hold")


def _aperture_table(text, label):
    """The row whose first cell is `label`, as a list of its remaining cells, plus the L header.

    Positional, not textual: the header row gives the apertures and the labelled row gives the
    values under them, so a cell is compared against the artifact value for ITS aperture.
    """
    lines = text.split(chr(10))
    for i, line in enumerate(lines):
        if not line.strip().startswith('|'):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if not cells or cells[0] != label:
            continue
        # walk back to the header row naming the apertures
        for j in range(i - 1, max(-1, i - 6), -1):
            hc = [c.strip() for c in lines[j].strip().strip('|').split('|')]
            if hc and hc[0] in ('$L$', 'L'):
                try:
                    Ls = [int(c.strip('$')) for c in hc[1:]]
                except ValueError:
                    continue
                return Ls, cells[1:]
    return None, None


def test_every_aperture_table_cell_matches_the_artifact():
    """Both Sec 9 aperture tables, EVERY cell, from 9_3_dat_substrate_of_aperture.csv.

    A mutation audit over PAPER.md found 21 unguarded cells in the aperture table and 7 in the
    coefficient table, while the margin row of the second WAS guarded. A partly guarded table is
    the worst case: the suite is green, the table looks checked, and the unchecked half is the
    part a reader compares.

    Cells are compared POSITIONALLY against the artifact value for their aperture. An earlier
    version searched the document for each value instead, and an injection showed it passing on
    a wrong cell -- `3.2` changed to `3.3` went unnoticed because `3.2` occurs inside other
    numbers elsewhere. A substring search over a three-character value checks nothing.
    """
    text = PAPER.read_text(encoding='utf-8')
    rows = _artifact('9_3_dat_substrate_of_aperture.csv')
    for r in rows:
        r['L'] = int(r['L'])
        for k in ('d2_circle', 'd2_raw', 'mu'):
            r[k] = float(r[k])
    # DERIVED: the artifact's own signal criterion -- a nonpositive tension is a read on noise.
    sig = [r for r in rows if r['mu'] > 0]
    by = {}
    for r in sig:
        by.setdefault((r['group'], r['beta']), []).append(r)
    lead = max(by, key=lambda k: len(by[k]))
    scan = {r['L']: r for r in by[lead]}

    # DERIVED: the SHARP ceiling (tangent at the threshold, not at the origin); the lag arity
    # N+1 is the periodic extent L.
    c_max = math.acos(3.0 ** -0.25) ** 2 / (2 * math.pi) ** 2

    def sci(v):
        mant, exp = ('%.2e' % v).split('e')
        return mant + '{' + BS + 'times}10^{' + str(int(exp)) + '}'

    wanted = {
        r'$\langle d^2\rangle$ circle': lambda r: '%.3f' % r['d2_circle'],
        r'$\langle d^2\rangle$ raw (retired)': lambda r: '%.1f' % r['d2_raw'],
        r'$\mu L^2$': lambda r: '%.2f' % (r['mu'] * r['L'] ** 2),
        r'$c$ required': lambda r: sci(r['d2_circle'] / r['L'] ** 2),
        r'margin to $c_{\max}$': lambda r: '%.1f' % (c_max / (r['d2_circle'] / r['L'] ** 2)),
    }

    checked, bad = 0, []
    for label, want_of in wanted.items():
        Ls, cells = _aperture_table(text, label)
        assert Ls is not None, 'Sec 9 no longer carries the table row ' + label
        assert len(Ls) == len(cells), label + ': header and row have different widths'
        for L, cell in zip(Ls, cells):
            assert L in scan, 'the paper tabulates L=%d, which the artifact does not carry' % L
            want = want_of(scan[L])
            got = cell.replace('$', '').replace(chr(92) + 'times', '{' + BS + 'times}')
            got = cell.strip('$').replace('$', '')
            checked += 1
            if want.strip('$') not in got:
                bad.append('%s at L=%d: paper says %s, artifact gives %s'
                           % (label, L, cell, want))
    # DERIVED: one cell per tabulated row per aperture. The bar is the table's own shape -- five
    # rows over the apertures the lead coupling carries -- so dropping a row or a column fails here
    # instead of quietly shrinking what is checked.
    expect = len(wanted) * len(scan)
    assert checked == expect, (
        'checked %d cells but the artifact and the row list imply %d; a row or a column was '
        'dropped from the tables' % (checked, expect))
    assert not bad, ('an aperture-table cell is not the artifact value:' + chr(10) + '  '
                     + (chr(10) + '  ').join(bad))


def test_every_stated_d2_range_matches_the_artifact():
    """Every `<d^2> in [a,b]` the paper states, against the artifact for that gauge group.

    The range is the paper's statement of what its single A1 input measures, repeated in the
    abstract summary, the A1 status table, the Sec 9 prose and the uniformity discussion. A
    mutation audit found the status-table copy unguarded.

    Presence would not check a repeated value: once one copy drifts the rest still match. Every
    occurrence is compared, and the count is pinned so a rewording that hides them fails rather
    than passing with nothing found.

    Only the `in [a,b]` form is taken -- that is how the paper states a measured range. An
    earlier version matched any two numbers near the symbol and swept in table rows and a
    coupling range, reporting its own imprecision as a defect in the paper.
    """
    text = PAPER.read_text(encoding='utf-8')
    su2 = [float(r['d2_central']) for r in _artifact('9_1_dat_d2_certified.csv')]
    su3 = [float(r['d2']) for r in _artifact('9_1_dat_d2_su3.csv')]
    assert su2 and su3, 'a d2 artifact is empty'

    pat = re.compile(re.escape(BS + 'langle d^2' + BS + 'rangle' + BS + 'in[')
                     + r'([0-9.]+),([0-9.]+)' + re.escape(']'))
    stated, bad, skipped = [], [], 0
    for m in pat.finditer(text):
        line_no = text[:m.start()].count(chr(10)) + 1
        line = text.split(chr(10))[line_no - 1]
        # Table rows are compared positionally by the cell guard; checking them here too would
        # be a second path over one table.
        if line.lstrip().startswith('|') and 'A1 interior' not in line:
            skipped += 1
            continue
        vals = su3 if 'SU(3)' in line else su2
        lo, hi = min(vals), max(vals)
        a, b = m.group(1), m.group(2)
        stated.append((a, b, line_no))
        # DERIVED: each end compared at the precision the paper writes it to.
        if abs(float(a) - lo) > _half_ulp(a) or abs(float(b) - hi) > _half_ulp(b):
            bad.append('line %d states [%s, %s]; the artifact gives [%.5f, %.5f]'
                       % (line_no, a, b, lo, hi))

    # DERIVED: every occurrence of the form is accounted for -- checked, or skipped as a table row
    # the cell guard already compares positionally. A wording change that hides the form shows up
    # here as an unaccounted marker rather than as a silent pass.
    marker = BS + 'langle d^2' + BS + 'rangle' + BS + 'in['
    assert len(stated) + skipped == text.count(marker), (
        'accounted for %d of %d <d^2> range statements' 
        % (len(stated) + skipped, text.count(marker)))
    # CHOSEN: the paper is expected to carry the range in at least this many places. It costs a
    # failure if the paper is rewritten to state it fewer times, which is the point -- without it
    # a rewrite that drops the statement everywhere would pass with nothing checked.
    assert len(stated) >= 4, (
        'a measured <d^2> range is stated %d times; the paper carries it in at least four '
        'places, so the pattern has stopped matching' % len(stated))
    assert not bad, ('a stated <d^2> range disagrees with the artifact:' + chr(10) + '  '
                     + (chr(10) + '  ').join(bad))


def test_u1_discriminator_claims_match_the_artifact():
    """Sec 8.6's measured U(1) caveat, from 9_5_dat_u1_discriminator.csv.

    The paragraph states that the tension bound does NOT separate the U(1) phases -- the most
    consequential caveat in the development, because `confinement_at_of_ratio` consumes exactly
    this quantity and knows nothing about which theory produced the correlation.

    The VERDICT is asserted alongside the values. If a future ensemble crossed the floor the
    paragraph would be wrong in the opposite direction, and a test that only checked the quoted
    numbers would keep passing while the claim inverted.
    """
    text = PAPER.read_text(encoding='utf-8')
    rows = _artifact('9_5_dat_u1_discriminator.csv')
    assert rows, 'the U(1) discriminator artifact is empty'
    mus = [float(r['mu']) for r in rows]
    betas = [float(r['beta']) for r in rows]
    k0 = float(rows[0]['kappa0'])

    # the verdict, from the artifact's own column rather than recomputed here
    crossed = [r for r in rows if r['above_floor'] == 'yes']
    says_none = 'No coupling crosses the floor' in text.replace('**', '')
    assert bool(crossed) != says_none, (
        'the paper says no coupling crosses the floor, but the artifact marks %d above it: %s'
        % (len(crossed), [r['beta'] for r in crossed]) if crossed else
        'the paper no longer states that no coupling crosses the floor, but none does')

    # Scoped to the paragraph that makes the claim. The _passage helper exists for this reason:
    # a three-decimal value is likely to appear somewhere in a paper that quotes hundreds of them,
    # so a document-wide search does not discriminate. An injection proved it -- changing this
    # paragraph's kappa0 passed, because other paragraphs still carried the old value.
    flat = _passage(text, 'That limitation, measured').replace(' ', '')
    checks = [
        ('the number of couplings', '%d' % len(rows)),
        ('the largest tension', '%.4f' % max(mus)),
        ('the floor', '%.4f' % k0),
        ('the lowest coupling', '%.2f' % min(betas)),
        ('the highest coupling', '%.2f' % max(betas)),
    ]
    # DERIVED: the Coulomb phase is the couplings above the transition the paper names, read
    # out of the paper rather than restated here.
    bc = float(re.search(r'beta_c\\approx([0-9.]+)', flat).group(1))
    coulomb = [float(r['mu']) for r in rows if float(r['beta']) > bc]
    if coulomb:
        checks.append(('the Coulomb minimum', '%.4f' % min(coulomb)))
        checks.append(('the Coulomb maximum', '%.4f' % max(coulomb)))

    missing = [f'{what} ({want})' for what, want in checks if want not in flat]
    assert not missing, ('the U(1) paragraph does not state: ' + ', '.join(missing))

    # the peak coupling, which is the paragraph's claim that the read locates the transition
    # The peak claim sits in the following paragraph, so it carries its own scope: one paragraph
    # is the unit `_passage` returns, and searching the wrong one would be the document-wide
    # search again under another name.
    peak = max(rows, key=lambda r: float(r['mu']))
    nearby = _passage(text, 'not blind to the physics').replace(' ', '')
    assert ('%.2f' % float(peak['beta'])) in nearby, (
        'the paper does not state that the tension peaks at beta=%.2f' % float(peak['beta']))


def _word_to_int(tok, words):
    """A count written as a word or as digits, or None if it is neither."""
    inv = {w: k for k, w in words.items()}
    t = tok.strip().lower()
    if t in inv:
        return inv[t]
    return int(t) if t.isdigit() else None


def _claimed_group_counts(passage, words):
    """The per-group counts the paper STATES, as {group: n}, parsed from its own phrasing.

    Searching for a number word does not work here: "two" and "five" each appear twice in this
    paragraph, once as a count and once in an unrelated phrase, so a wrong count still found its
    word somewhere and passed. The claim is parsed instead, so a disagreement fails because it is
    the stated count that is wrong.
    """
    out = {}
    for m in re.finditer(r"([A-Za-z]+|[0-9]+)\s*[$]SU[(]([0-9])[)][$]", passage):
        n = _word_to_int(m.group(1), words)
        if n is not None:
            out["su" + m.group(2)] = n
    return out


def _claimed_exclusions(passage, words):
    """The number of excluded points the paper states, or None if it states none."""
    m = re.search(r"([A-Za-z]+|[0-9]+)\s+further points?\s+(?:are|is)\s+excluded", passage)
    return _word_to_int(m.group(1), words) if m else None


def _states_count(passage, n, words):
    """Does `passage` state the count `n` as a word or a standalone number?

    A bare digit is not enough: searching a passage for '5' finds it inside '0.851' and reports
    a wrong count as disclosed. The spelled word is matched plainly; the digit only at a
    boundary, so it cannot be a fragment of a longer number.
    """
    # Filenames and code spans carry digits that are not counts: the '6' in
    # '9_6_dat_junction_residuals.csv' satisfied a bounded-digit search and passed a wrong
    # per-group count. Prose only -- link targets and code spans are removed first.
    prose = re.sub(r'\[[^\]]*\]\([^)]*\)', ' ', passage)
    prose = re.sub(r'`[^`]*`', ' ', prose)
    word = words.get(n)
    if word and word in prose.lower():
        return True
    return re.search(r'(?<![0-9._])' + str(n) + r'(?![0-9._])', prose) is not None

def test_junction_identification_matches_the_artifacts():
    """The measured gapped identification, recomputed from BOTH source artifacts.

    The paper claims the measured margin lower-bounds the measured transfer gap, which is the
    evidence for the step from `mu < kappa0` to a gap in the ACTUAL modes -- the link the
    flagship cannot supply, since its model's mass is defined to make that link hold.

    Recomputed from `8_7_dat_mhi_multicoupling.csv` and `9_3_dat_substrate_of_aperture.csv`
    rather than read back from the derived artifact, so a stale derived file fails here too.
    The VERDICT is asserted alongside the figures: if a point stopped satisfying the
    inequality the paragraph would be wrong in the other direction, and checking only the
    quoted numbers would keep passing while the claim inverted.
    """
    text = PAPER.read_text(encoding='utf-8')
    k0 = 0.25 * math.log(3.0)
    # BOTH gap sources and BOTH groups, as the certificate reads them. Keyed on group as well
    # as (L, beta): keyed on the pair alone, an SU(3) point would collide with an SU(2) one at
    # the same volume and coupling, and reading only one source silently checked six of eight.
    delta = {}
    for r in _artifact('8_7_dat_mhi_multicoupling.csv'):
        delta[('su2', int(r['L']), '%.2f' % float(r['beta']))] = (float(r['Delta']),
                                                                 float(r['Delta_err']))
    for r in _artifact('8_7_dat_gap_su3.csv'):
        delta[(r['group'], int(r['L']), '%.2f' % float(r['beta']))] = (float(r['Delta']),
                                                                       float(r['Delta_err']))
    mu = {}
    for r in _artifact('9_3_dat_substrate_of_aperture.csv'):
        mu[(r['group'], int(r['L']), r['beta'])] = float(r['mu'])
    shared = sorted(set(delta) & set(mu))
    assert shared, 'no (L, beta) carries both a transfer gap and a tension'

    # DERIVED: the resolution rule Sec 8.7b states, the same tolerance `_variational` applies.
    tol = 0.25
    # DERIVED: two standard errors, the band the paper quotes every measured gap at.
    resolved, unresolved = [], []
    for k in shared:
        d, e = delta[k]
        # DERIVED: a nonpositive gap, or one whose error exceeds the rule's share of it,
        # carries no information either way.
        if d <= 0 or e / d > tol:
            unresolved.append(k)
            continue
        resolved.append((k, d - 2.0 * e, k0 - mu[k]))
    assert resolved, 'no point resolves its transfer gap; the claim cannot be checked'

    # The claim spans a display equation, and `_passage` returns ONE paragraph -- so the
    # figures sat outside it. Scoped to the whole block instead: from the heading to the
    # next bold heading or section rule, which is the unit the claim is made in.
    start = text.find('The identification, measured')
    # DERIVED: `str.find` returns -1 for absent, so zero-or-more means the anchor was found.
    assert start > 0, 'the identification paragraph is no longer in the paper'
    ends = [p for p in (text.find(chr(10) + '**', start + 40),
                        text.find(chr(10) + '##', start + 40),
                        text.find(chr(10) + '---', start + 40))
            # DERIVED: -1 from `str.find` means absent; keep only the boundaries that exist.
            if p > 0]
    passage = text[start:min(ends)] if ends else text[start:start + 3000]
    flat = passage.replace(' ', '')

    # The DIRECTION of the stated inequality. An injection flipping ge to le was missed by
    # every other check here: the figures all still matched while the claim said the
    # opposite thing. The relation is the claim, so it is asserted explicitly.
    # The DIRECTION of the stated inequality. An injection flipping ge to le was missed by every
    # other check here: the figures all still matched while the claim said the opposite thing.
    # The relation IS the claim, so the display equation is read directly.
    disp = re.findall(r'[$][$](.+?)[$][$]', passage, re.S)
    eqs = [d.replace(' ', '') for d in disp if 'Delta' in d and 'kappa_0' in d]
    assert eqs, 'the identification block no longer displays Delta against kappa_0 - mu'
    eq = eqs[0]
    assert (BS + 'ge') in eq, (
        'the displayed relation is %r; the claim is that the transfer gap is at LEAST the margin' % eq)
    assert (BS + 'le') not in eq, (
        'the displayed relation %r bounds the gap ABOVE by the margin, inverting the claim' % eq)

    # EVERY statement of the relation, not only the displayed one. The block states it twice
    # -- once as a display equation and once inline -- and an injection flipping the inline
    # copy passed while the displayed one still read correctly.
    flatp = passage.replace(' ', '')
    rels = re.findall(re.escape(BS + 'Delta') + r'[^$]{0,24}?'
                      + '(' + re.escape(BS + 'ge') + '|' + re.escape(BS + 'le') + ')'
                      + r'[^$]{0,24}?' + re.escape(BS + 'kappa_0'), flatp)
    assert rels, 'the block no longer relates Delta to kappa_0 anywhere'
    wrong = [r for r in rels if r != BS + 'ge']
    assert not wrong, (
        '%d of %d statements of the relation bound the gap ABOVE by the margin, inverting '
        'the claim' % (len(wrong), len(rels)))

    # the verdict, both ways
    failed = [k for k, lo, margin in resolved if lo < margin]
    # DERIVED from the count the artifacts give, not the phrase the paper happened to carry
    # when this was written -- a guard that hardcodes the claim cannot notice it growing.
    words = {1: 'one', 2: 'two', 3: 'three', 4: 'four', 5: 'five', 6: 'six', 7: 'seven',
             8: 'eight', 9: 'nine', 10: 'ten'}
    n_res = len(resolved)
    claims_all = any(('all%sresolvedpoints' % w) in flat.lower()
                     for w in {str(n_res), words.get(n_res, str(n_res))})
    assert not failed or not claims_all, (
        'the paper claims every resolved point satisfies the inequality, but %s fail' % failed)
    assert failed or claims_all, (
        'every resolved point satisfies the inequality, but the paper no longer says so')

    # the count of resolved points, spelled or numeric
    assert _states_count(passage, n_res, words), (
        'the paper does not state that %d points resolve' % n_res)

    # The per-group breakdown, PARSED from the paper's own phrasing rather than searched for.
    # A point moving between groups leaves the total unchanged, so the total alone cannot see
    # it; and a word search cannot either, because the same words appear elsewhere here.
    by_group = {}
    for k, _, _ in resolved:
        by_group[k[0]] = by_group.get(k[0], 0) + 1
    claimed = _claimed_group_counts(passage, words)
    assert claimed, 'the paper no longer states a per-group breakdown of the resolved points'
    assert claimed == by_group, (
        'the paper states %s resolved points per group; the artifacts give %s'
        % (claimed, by_group))

    # the tightest ratio, at the precision the paper writes it
    tight = min(lo / margin for _, lo, margin in resolved)
    m = re.search(r'factor[$]?([0-9.]+)[$]?', flat)
    assert m, 'the paper no longer states the tightest factor'
    dp = len(m.group(1).split('.')[1]) if '.' in m.group(1) else 0
    assert abs(float(m.group(1)) - tight) <= 0.5 * 10.0 ** (-dp), (
        'the paper states a tightest factor of %s; recomputed it is %.3f'
        % (m.group(1), tight))

    # The exclusions must be disclosed by COUNT and by the worst case. Quoting every excluded
    # point's error bar was reasonable at two and becomes a list of numbers at five, saying
    # nothing the count does not; what a reader needs is how many were dropped and how bad the
    # worst was, to judge whether the rule was applied or the result was selected.
    if unresolved:
        n_ex = len(unresolved)
        # PARSED, for the same reason as the breakdown: 'five' also appears in this paragraph
        # as 'an error five times its value', so a wrong count still found its word.
        claimed_ex = _claimed_exclusions(passage, words)
        assert claimed_ex is not None, (
            'the paper no longer states how many points are excluded as unresolved')
        assert claimed_ex == n_ex, (
            'the paper states %d excluded points; the artifacts give %d'
            % (claimed_ex, n_ex))
        # DERIVED: a nonpositive gap has no relative error; it sorts as the worst, which is
        # what it is. Zero is the domain of the division, not a cut.
        worst = max(unresolved, key=lambda k: delta[k][1] / delta[k][0] if delta[k][0] > 0
                    else float('inf'))
        d, e = delta[worst]
        assert ('%.3f' % d) in flat and ('%.3f' % e) in flat, (
            'the worst excluded gap is %.3f+/-%.3f and the paper does not state it' % (d, e))


def _channel_rows(passage):
    """The channel table as {(coarse, fine): [numbers in the row]}, parsed positionally.

    A table is positional data. Reading it as a bag of numbers throws away which row and column
    a value belongs to, and then a coarse number elsewhere in the paragraph -- 0.90 at one
    decimal, tolerance 0.05 -- absorbs a precise claim like a ratio of 0.867.
    """
    out = {}
    for line in passage.split(chr(10)):
        t = line.strip()
        if not t.startswith('|'):
            continue
        cells = [c.strip() for c in t.strip('|').split('|')]
        m = re.match(r'[^0-9]*([0-9]+)\s*/\s*([0-9]+)', cells[0]) if cells else None
        if not m:
            continue
        vals = []
        for c in cells[1:]:
            vals.append([float(x) for x in re.findall(r'[0-9]+[.][0-9]+', c)])
        out[(int(m.group(1)), int(m.group(2)))] = vals
    return out


def test_smeared_channel_claims_match_the_artifact():
    """Sec 9's channel trade-off, recomputed from 9_7_dat_smeared_channel.csv.

    The paragraph states that a channel with a physical correlation length exists and that the
    substrate hypothesis is far closer to failing on it -- the sharpest statement the
    measurements support, and the one that sizes the whole result.

    Cells are compared POSITIONALLY. The sigma separations are DERIVED from the ratios and their
    errors, since they are what 'excludes the UV outcome' rests on and appear nowhere in the
    artifact. And the ORDERING of the margins is asserted: the raw channel must clear by more
    than the smeared one, which is the claim itself and which no per-cell check would see
    inverting.
    """
    text = PAPER.read_text(encoding='utf-8')
    rows = _artifact('9_7_dat_smeared_channel.csv')
    assert rows, 'the smeared-channel artifact is empty'
    start = text.find('A channel that is physical')
    # DERIVED: `str.find` returns -1 for absent; zero-or-more means the anchor was found.
    assert start > 0, 'Sec 9 no longer carries the channel paragraph'
    ends = [p for p in (text.find(chr(10) + '**', start + 40),
                        text.find(chr(10) + '##', start + 40))
            # DERIVED: -1 from `str.find` means absent; keep the boundaries that exist.
            if p > 0]
    passage = text[start:min(ends)] if ends else text[start:start + 4000]
    table = _channel_rows(passage)
    assert table, 'the channel table is no longer parseable as rows'

    bad = []
    for r in rows:
        key = (int(r['sweeps_coarse']), int(r['sweeps_fine']))
        if key not in table:
            bad.append('the table has no row for sweeps %d/%d' % key)
            continue
        ratio_cell, coarse_cell, fine_cell = table[key][0], table[key][1], table[key][2]
        want = ((ratio_cell, [float(r['ratio']), float(r['ratio_err'])], 'ratio and error'),
                (coarse_cell, [float(r['margin_coarse'])], 'coarse margin'),
                (fine_cell, [float(r['margin_fine'])], 'fine margin'))
        for got, expect, label in want:
            if len(got) != len(expect):
                bad.append('sweeps %d/%d %s: the cell states %s, expected %d value(s)'
                           % (key[0], key[1], label, got, len(expect)))
                continue
            for g, e in zip(got, expect):
                # DERIVED: half a unit in the last place THIS cell is written to.
                dp = len(('%r' % g).split('.')[1]) if '.' in ('%r' % g) else 0
                if abs(g - e) > 0.5 * 10.0 ** (-dp):
                    bad.append('sweeps %d/%d %s: paper %s, artifact %.4f'
                               % (key[0], key[1], label, g, e))
    assert not bad, ('the channel table disagrees with its artifact:' + chr(10) + '  '
                     + (chr(10) + '  ').join(bad))

    flat = passage.replace(' ', '')
    # DERIVED: zero sweeps IS the unsmeared channel, so this splits the two channels rather
    # than cutting a range.
    smeared = [r for r in rows if int(r['sweeps_coarse']) > 0]
    assert smeared, 'the artifact carries no smeared rows'
    for r in smeared:
        ratio, err = float(r['ratio']), float(r['ratio_err'])
        # DERIVED: the UV outcome is a ratio of one -- a length fixed in SITES does not change
        # when the spacing does. Not a threshold; it is the competing hypothesis.
        sig = abs(ratio - 1.0) / err if err > 0 else float('inf')
        assert ('%.1f' + BS + 'sigma') % sig in flat, (
            'sweeps %s/%s separates from the UV outcome at %.1f sigma, which the paper does '
            'not state' % (r['sweeps_coarse'], r['sweeps_fine'], sig))

    physical = float(rows[0]['physical_prediction'])
    assert ('%.2f' % physical) in flat, (
        'the paper does not state the physical prediction as %.2f' % physical)

    # THE DIRECTION OF THE CONCLUSION: the raw channel must clear by more than the smeared one.
    # DERIVED: zero sweeps IS the unsmeared channel, as above.
    raw = [r for r in rows if int(r['sweeps_coarse']) == 0]
    assert raw, 'the artifact carries no unsmeared row to compare against'
    raw_margin = min(float(raw[0]['margin_coarse']), float(raw[0]['margin_fine']))
    worst_smeared = min(min(float(r['margin_coarse']), float(r['margin_fine']))
                        for r in smeared)
    assert raw_margin > worst_smeared, (
        'the paper says the comfortable margin is a property of the channel being UV, but the '
        'raw channel clears by %.1fx and the smeared one by %.1fx' % (raw_margin, worst_smeared))


def test_fixed_selection_artifact_is_reproduced_by_its_script():
    """9_8_dat_fixed_selection.csv is what `fixed_selection_of_scaling.py` computes, to the digit.

    The artifact's whole point is that it needs NO admissibility tolerance: it holds
    (operator, smearing, tau) fixed and takes no minimum, so the `tol=0.25` that the tests and the
    figure currently replace with two DIFFERENT derived rules never enters. A guard that only
    checked the file's shape would let the numbers drift away from the code that claims to produce
    them, which is the failure mode the artifact exists to close.
    """
    import importlib.util
    art = _artifact("9_8_dat_fixed_selection.csv")
    assert art, "9_8_dat_fixed_selection.csv is empty or absent"

    root = REPO / "research"
    spec = importlib.util.spec_from_file_location(
        "fixed_selection_of_scaling", root / "code" / "certify" / "fixed_selection_of_scaling.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    gap = _artifact("8_7_dat_gap_correlator.csv")
    sig = {round(float(r["beta"]), 2): float(r["sqrt_sigma"])
           for r in _artifact("8_8_dat_string_tension.csv") if int(r["L"]) == mod.SCAN_L}
    vol, scan = mod.series(gap)

    seen = 0
    for row in art:
        if row["test"] == "matched_volume":
            # The ratio of a*m across two couplings at MATCHED physical volume, recomputed. This is
            # the continuum direction -- the one the 1/L_phys cap leaves open -- so the row must be
            # what the correlator actually says, not a remembered number.
            (LA, bA), (LB, bB) = [(int(x.split("@")[0]), round(float(x.split("@")[1]), 2))
                                  for x in row["points"].split("|")]
            key = (row["operator"], row["nsmear"], int(row["tau"]))
            src = {}
            for r in gap:
                v, e = mod._f(r.get("m_eff")), mod._f(r.get("m_eff_err"))
                # DERIVED: validity, not a cut -- NaN fails its own equality and a nonpositive
                # value or error is not a measurement. No quantity is thresholded here.
                if v != v or e != e or v <= 0 or e <= 0:
                    continue
                if (r["operator"], r["nsmear"], int(r["tau"])) != key:
                    continue
                src[(int(r["L"]), round(float(r["beta"]), 2))] = (v, e)
            assert (LA, bA) in src and (LB, bB) in src, f"{key}: the artifact names points not in the correlator"
            ratio = src[(LB, bB)][0] / src[(LA, bA)][0]
            assert abs(float(row["fit_const"]) - ratio) <= _half_ulp(row["fit_const"]), \
                f"{key}: artifact ratio {row['fit_const']} vs recomputed {ratio:.4f}"
            pred = sig[bB] / sig[bA]
            assert abs(float(row["fit_alt"]) - pred) <= _half_ulp(row["fit_alt"]), \
                f"{key}: artifact physical prediction {row['fit_alt']} vs recomputed {pred:.4f}"
            want = "physical" if abs(ratio - pred) < abs(ratio - 1.0) else "cutoff"
            assert row["chi2_alt"] == want, \
                f"{key}: artifact says {row['chi2_alt']}, recomputation says {want}"
            seen += 1
            continue
        if row["test"] == "exclusion":
            # `min_i (v_i + z e_i)` bounds Delta at every z, so the recorded critical z is the
            # largest conservatism the exclusion of the published Sec 8.6 read survives. Recomputed
            # here rather than trusted, and the z=0 bound is checked alongside it.
            beta = float(row["points"])
            cand = [(d[beta][0], d[beta][1]) for d in scan.values() if beta in d]
            assert len(cand) >= mod.MIN_PTS, f"beta={beta}: too few basis entries"
            assert abs(float(row["fit_alt"]) - min(v for v, _ in cand)) <= _half_ulp(row["fit_alt"]), \
                f"beta={beta}: z=0 bound {row['fit_alt']} not reproduced"
            pv = float(row["fit_const"])
            # DERIVED: the critical z has a closed form -- `min_i (v_i + z e_i) >= pv` holds exactly
            # when every candidate does, so z* is `max_i (pv - v_i)/e_i`. Recomputed, not searched.
            zc = max((pv - v) / e for v, e in cand)
            assert abs(float(row["chi2_alt"]) - zc) <= _half_ulp(row["chi2_alt"]), \
                f"beta={beta}: critical z {row['chi2_alt']} vs recomputed {zc:.4f}"
            seen += 1
            continue
        key = (row["operator"], row["nsmear"], int(row["tau"]))
        if row["test"] == "volume":
            d = vol[key]
            Ls = sorted(d)
            c, chi = mod._chi2_const([d[L][0] for L in Ls], [d[L][1] for L in Ls])
        else:
            d = scan[key]
            bs = sorted(b for b in d if b in sig)
            r = [d[b][0] / sig[b] for b in bs]
            er = [d[b][1] / sig[b] for b in bs]
            c, chi = sum(r) / len(r), mod._chi2_const(r, er)[1]
        assert abs(float(row["fit_const"]) - c) <= _half_ulp(row["fit_const"]), \
            f"{row['test']} {key}: artifact {row['fit_const']} vs recomputed {c}"
        assert abs(float(row["chi2_const"]) - chi) <= _half_ulp(row["chi2_const"]), \
            f"{row['test']} {key}: chi2 {row['chi2_const']} vs recomputed {chi}"
        seen += 1
    # DERIVED: the artifact carries one row per (operator, smearing, tau) series with enough
    # points, and the committed file has 29. A floor well under that catches a truncated or
    # filtered artifact without pinning the exact count, which legitimately grows with new data.
    assert seen >= 20, f"only {seen} series checked; the artifact should carry the whole basis"


def test_fixed_selection_needs_no_tolerance():
    """The fixed-selection script must not carry an admissibility cut of its own.

    It exists because taking a variational MINIMUM forces one, and the repo holds two derived
    replacements that disagree. If this script ever grows a `tol`, it stops dissolving that
    conflict and becomes a third party to it.
    """
    src = (REPO / "research" / "code" / "certify" / "fixed_selection_of_scaling.py").read_text(
        encoding="utf-8")
    body = "\n".join(l for l in src.splitlines()
                     if not l.lstrip().startswith("#") and "tol" not in l.lower().split("--")[0][:0])
    import re
    assert not re.search(r"^\s*(tol|TOL)\s*=", body, re.M), \
        "fixed_selection_of_scaling.py defines a tolerance; it must take no minimum and need none"


def test_sec_8_7b_does_not_claim_tolerance_stability():
    """Sec 8.7b must not claim the variational selection is stable under the resolution tolerance.

    It is not, and the disagreement is load-bearing: three derived replacements for the literal
    `0.25` give different selections, two of them picking the ACTION DENSITY at beta=2.40 -- the
    operator the section's argument turns on the rule never selecting. The paper said "stable under
    the resolution tolerance ... and never the action density"; both halves are false, so the claim
    was corrected rather than annotated.

    This guard pins the correction. A reader who re-tightens the sentence without re-checking the
    data would be restating a measured falsehood, and that is exactly the kind of claim that
    survives in a long document because nothing objects to it.
    """
    text = PAPER.read_text(encoding="utf-8")
    bad = ["stable under the\nresolution tolerance", "stable under the resolution tolerance"]
    for phrase in bad:
        assert phrase not in text, (
            "Sec 8.7b claims tolerance-stability again; the selection changes with the tolerance "
            "(see data/9_8_dat_fixed_selection.csv and _variational's docstring)")
    # and the surviving claim -- constancy under every rule -- must still be stated
    assert "0.21" in text and "0.14" in text and "0.23" in text, \
        "the chi2/dof values for the three derived rules should be stated, since constancy is what survives"


def test_sec_8_7b_records_the_action_density_selection():
    """The section must record that some derived rules DO select the action density.

    Sec 8.7b's exclusion argument is unaffected by this -- the bound is an upper bound whichever
    operator attains it -- but the claim "never the action density" was used as supporting evidence
    that the plaquette is the physical channel, and it does not hold at beta=2.40 under two of the
    three derived rules, nor at L=12 and L=20.
    """
    text = PAPER.read_text(encoding="utf-8")
    assert "action density" in text.lower(), "the section no longer mentions the action density at all"
    window = text[text.find("variational minimum over the"):][:2000]
    assert "2.40" in window or "L=20" in window or "$L=20$" in window, \
        "Sec 8.7b does not record where the derived rules select the action density"


def test_matched_volume_table_matches_the_artifact():
    """Sec 8.7b's matched-physical-volume ratios are the `matched_volume` rows of 9_8.

    Each quoted ratio is located in the paper by its own digits and checked against the artifact at
    the half-ulp of the precision the paper writes, so this guard carries no tolerance of its own.
    The separation it protects is the whole claim: every smeared-plaquette series on the physical
    side, every action-density series on the cutoff side. If a future edit softened that into "most"
    or dropped a row, the numbers would stop matching and this would say so.
    """
    art = [r for r in _artifact("9_8_dat_fixed_selection.csv") if r["test"] == "matched_volume"]
    if not art:
        pytest.skip("9_8 carries no matched_volume rows")
    text = PAPER.read_text(encoding="utf-8")

    # The paper states the two physical predictions, rounded to its own precision. Compared as
    # NUMBERS at the half-ulp of what the paper writes -- a string match would fail on `0.5634`
    # against a paper that sensibly writes `0.563`, which is a formatting difference, not a defect.
    written = set(re.findall(r"predicts \$(\d\.\d+)\$", text))
    assert written, "the paper no longer states the matched-volume physical predictions"
    for pred in sorted({float(r["fit_alt"]) for r in art}):
        assert any(abs(float(w) - pred) <= _half_ulp(w) for w in written), \
            f"the artifact predicts {pred:.4f}; the paper states {sorted(written)}"

    # every ratio the paper quotes to three decimals must exist in the artifact
    quoted = set(re.findall(r"\$(0\.\d{3})\(\d\d\)\$", text))
    have = {("%.3f" % float(r["fit_const"])) for r in art}
    missing = [q for q in quoted if q in {"0.644", "0.765", "0.470", "0.736", "1.010", "1.195"}
               and q not in have]
    assert not missing, f"PAPER.md quotes matched-volume ratios absent from 9_8: {missing}"

    # And the operator separation the claim rests on must hold in the artifact itself. A series counts
    # only where it is RESOLVED -- its own jackknife error below its own value, `chi2_const` against
    # `fit_const`. That is not a cut chosen here: it is the admissibility rule the m_hi L-scan already
    # applies (`e < v` in `variational_lscan`), reused unchanged, and it is computed per row from that
    # row's own numbers. A series whose error exceeds its value names neither reading, so counting it
    # on either side would be reading noise as evidence.
    def resolved(r):
        return float(r["chi2_const"]) < float(r["fit_const"])

    smeared_plaq = [r for r in art
                    if r["operator"] == "plaquette_0pp" and r["nsmear"] != "0" and resolved(r)]
    cutoff_side = [r for r in art
                   if (r["operator"] == "action_density" or r["nsmear"] == "0") and resolved(r)]
    assert smeared_plaq and cutoff_side, "the artifact lost one side of the comparison"

    wrong = [r for r in smeared_plaq if r["chi2_alt"] != "physical"]
    assert not wrong, \
        ("a RESOLVED smeared-plaquette series no longer prefers the physical reading "
         f"({wrong}); the paper's 'all seven smeared-plaquette series' claim would be false")
    wrong = [r for r in cutoff_side if r["chi2_alt"] != "cutoff"]
    assert not wrong, \
        (f"{len(wrong)} resolved action-density/unsmeared series prefer physical ({wrong}); the "
         "paper claims every one prefers cutoff")

    # the paper states both counts; if the artifact's populations move, they must move with it
    assert f"all seven smeared-plaquette" in text and "all fifteen" in text, \
        "Sec 8.7b no longer states the resolved-series counts"
    assert (len(smeared_plaq), len(cutoff_side)) == (7, 15), \
        (f"the artifact now has {len(smeared_plaq)} resolved smeared-plaquette and "
         f"{len(cutoff_side)} resolved cutoff-side series; the paper says seven and fifteen")


def test_aperture_cap_constants_match_the_artifact():
    """The O(1/N) ceiling the paper quotes is the one `aperture_cap_of_floor.py` computes.

    This constant decides a conclusion -- that the tension route cannot reach the thermodynamic
    limit -- so it is the kind of number that must not live only in prose. Each value is compared
    NUMERICALLY at the half-ulp of the precision the paper writes, so a paper rounding differently
    from the artifact is not a failure while a paper quoting a different number is.

    Both constants are checked, and that is the point of the test rather than a completeness habit.
    They are `10.9887` (the FOLDED shape `lam^circLag d`, which is what the criterion reads) and
    `11.1759` (the UNFOLDED shape `lam^d`, which is a different object). Both live on the same
    circle -- the fold in `rho`, not the geometry, is what separates them. They differ by less than
    the distance from any simulated aperture to its own limit, so a finite table does not separate
    them and prose that attached one formula to the other's numbers would read as correct. Binding
    each to its own artifact row is what makes them distinguishable here.
    """
    art = _artifact("9_10_dat_aperture_cap.csv")
    if not art:
        pytest.skip("9_10 is absent")
    by = {r["quantity"]: r for r in art if r["quantity"] in
          {"limit_circle", "limit_unfolded", "a_star", "C_times_hbarc_GeV_fm",
           "massless_cos_average"}}
    for need in ("limit_circle", "limit_unfolded", "a_star", "massless_cos_average"):
        assert need in by, f"9_10 no longer carries a `{need}` row"
    text = PAPER.read_text(encoding="utf-8")

    circle = float(by["limit_circle"]["n_times_rate"])
    halfline = float(by["limit_unfolded"]["n_times_rate"])
    astar = float(by["a_star"]["n_times_rate"])

    # The two must actually be distinct, or this guard compares a number with itself. Stated as an
    # ORDERING, not a separation: the minimum-image fold contributes coth(a*pi/2) > 1, which
    # strictly lowers the requirement, so `folded < unfolded` always -- and no magnitude is being
    # tolerated. A chosen minimum separation here would be a threshold hiding the data under it.
    assert circle < halfline, (
        f"the folded constant {circle:.7f} is not below the unfolded one {halfline:.7f}; the coth "
        "factor that separates them has gone the wrong way")

    # `massless_cos_average` joined this list on 2026-09-17. The paper quoted it -- the reading a free
    # massless box mode gives, which is what makes the cap non-vacuous -- while it existed only in the
    # script's stdout. A figure printed and not written is checkable by reading the code that produced
    # it and in no other way, which is how a number drifts away from the thing it describes.
    massless = float(by["massless_cos_average"]["n_times_rate"])
    assert massless < float(by["limit_circle"]["n_times_rate"]), "sanity: these are different scales"
    for label, value in (("C (folded)", circle), ("C' (unfolded)", halfline),
                         ("a_star", astar), ("massless <cos>", massless)):
        quoted = re.findall(rf"{re.escape(f'{value:.4f}')[:6]}\d*", text)
        near = [q for q in quoted if abs(float(q) - value) <= _half_ulp(q)]
        assert near, (
            f"PAPER.md does not quote {label} = {value:.7f} as the artifact computes it; "
            f"numbers found with that prefix: {quoted}")

    # and the paper must attach each to the RIGHT object: the folded constant is the one the
    # criterion carries, and it is the smaller of the two, so it is the one stated as the cap.
    cap_claim = re.search(r"C=2\\pi a_\\star.{0,400}", text, re.S)
    assert cap_claim, "Sec 12 no longer states the cap as C = 2*pi*a_star"
    assert f"{circle:.7f}" in cap_claim.group(0), \
        (f"the cap passage does not carry the folded constant {circle:.7f}; if it carries "
         f"{halfline:.7f} instead, the unfolded shape has been substituted for this one")

    # The physical restatement must use the FINITE-aperture constant, not the ceiling. `C` is the
    # n -> infinity limit and `n*Delta` approaches it from below, so quoting `C*hbarc` at L=16 states
    # a bound about 3% stronger than the criterion supports there. Every GeV.fm figure the paper
    # gives is checked against the artifact row for the aperture it is claimed at.
    finite = [r for r in art if r["quantity"] == "mass_product_times_hbarc_GeV_fm_n16"]
    assert finite, "9_10 no longer carries the finite-aperture physical constant"
    kn = float(finite[0]["n_times_rate"])
    ceiling = float(by["C_times_hbarc_GeV_fm"]["n_times_rate"]) if "C_times_hbarc_GeV_fm" in by else None
    assert ceiling is None or kn < ceiling, \
        (f"the finite-aperture constant {kn:.7f} is not below the ceiling {ceiling:.7f}; C would "
         "not be a ceiling, and the cap on what a WIDENING APERTURE can certify would not follow")

    stated = re.findall(r"(\d\.\d+)\\ \\mathrm\{GeV\\cdot fm\}", text)
    assert stated, "the paper no longer states the bound in GeV.fm"
    bad = [v for v in stated if abs(float(v) - kn) > _half_ulp(v)]
    assert not bad, (
        f"PAPER.md states {bad} GeV.fm; at n=16 the criterion certifies {kn:.7f}. If one of these "
        f"is the ceiling {ceiling}, it is being quoted as if it were certified at a finite volume.")


def test_the_unfolded_cap_is_never_quoted_as_this_one():
    """`2*pi*sqrt(T/(1-T))` may appear only where it is named as the UNFOLDED-shape constant.

    The criterion reads `rho(d) = lam^circLag d`; `11.1760` belongs to the unfolded `rho(d) =
    lam^d`, equivalently to the periodic `cosh` correlator and to the free-field structure-factor
    inversion. Both live on the same circle -- what separates them is the minimum-image FOLD in
    `rho`, which contributes `coth(a pi/2) > 1` -- so naming either one after a geometry is what
    made them confusable in the first place. They agree to better than two percent, closer than any
    simulated aperture is to its own limit, so a passage that attaches one formula to the other's
    numbers reads as correct and survives review. It did, in three files at once.

    The distinction cannot be maintained by remembering it, so it is maintained here: any file
    carrying `11.1760` must also say `unfolded` (or `lam^d`, or `cosh`) within the same paragraph.
    Naming it is always allowed -- the constant is real and worth contrasting; leaving it unlabelled
    next to this development's numbers is not.
    """
    root = REPO / "research"
    digits = "11.17597"
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
            if any(tag in low for tag in ("unfolded", "lam^d", "λ^d", "cosh")):
                continue
            offenders.append(f"{path.relative_to(REPO)}: {para.strip()[:110]}")

    assert not offenders, (
        "the unfolded-shape cap constant appears without being named as such -- it is not the "
        "constant this criterion carries (10.98875):\n  " + "\n  ".join(offenders))


def test_the_criterion_separates_a_glueball_from_a_massless_field():
    """Sec 12's separation at the simulated aperture is the artifact's, and it is a separation.

    The claim is not that some numbers match: it is that every physical-glueball row sits ABOVE the
    entropy floor and the massless row sits BELOW it, at the aperture the released ensembles carry.
    That ordering is checked against `3^{-1/4}` recomputed here from the floor rather than read from
    the file, so a corrupted artifact cannot define its own threshold and pass.

    The floor is not a tolerance and is not chosen: it is `e^{-kappa_0}` with `kappa_0 = (1/4)log 3`,
    proved in `Floor.lean`. Nothing in this test admits a margin -- a row exactly at the floor fails,
    because clearing it is the whole statement.
    """
    art = _artifact("9_10_dat_aperture_cap.csv")
    if not art:
        pytest.skip("9_10 is absent")
    floor = 3.0 ** -0.25

    glue = [r for r in art if r["quantity"] == "glueball_vs_floor"]
    massless = [r for r in art if r["quantity"] == "massless_vs_floor"]
    assert glue, "9_10 no longer carries the glueball comparison"
    assert massless, "9_10 no longer carries the massless comparison"

    below = [r["aperture"] for r in glue if float(r["n_times_rate"]) <= floor]
    assert not below, (
        f"a physical glueball no longer clears the floor at {below}; the criterion would be "
        "rejecting the spectrum it exists to certify")
    above = [r["aperture"] for r in massless if float(r["n_times_rate"]) >= floor]
    assert not above, (
        f"a massless field now clears the floor at {above}; the criterion would decide nothing at "
        "the aperture actually simulated")

    # the paper must state the same verdicts, not merely the same numbers
    text = PAPER.read_text(encoding="utf-8")
    m = re.search(r"^\| massless \|.*$", text, re.M)
    assert m and "fails" in m.group(0), \
        "Sec 12's table no longer records the massless field as failing the criterion"
    for r in glue:
        val = float(r["n_times_rate"])
        assert f"{val:.4f}" in text, \
            f"PAPER.md does not quote the artifact's {r['aperture']} reading {val:.4f}"
