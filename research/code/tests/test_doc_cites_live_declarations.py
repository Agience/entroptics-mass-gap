"""The goal document may not cite a declaration that does not exist.

Five dead citations were found in `CLAY-GOAL.md` on 2026-09-21 — `su3_transferData_T_ne_id`,
`su3ReTr`, `su3ReTr_separating` in row 13, `gapAt_of_finite_volume_pairing` in rows 12 and 17c, and
`iodd_action_ireflConf` in row 17b — every one by accident, while doing something else. A renamed
declaration leaves the chain of record pointing at nothing, and unlike a stale claim a dead citation
cannot even be argued with.

⛔ THIS DOES NOT CHECK THAT ANY CLAIM IS TRUE. It checks that the names resolve. The declaration a
live citation points at may say something entirely different from what the document says it says.
"""
from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
CERTIFY = os.path.join(os.path.dirname(_HERE), "certify")
if CERTIFY not in sys.path:
    sys.path.insert(0, CERTIFY)

import doc_cites_live_declarations as gate  # noqa: E402


def _dead_for(text: str, words: set[str], modules: set[str]) -> list[str]:
    """The gate's classification, applied to one document's text."""
    out: list[str] = []
    for line in text.splitlines():
        for tok in gate.TOKEN.findall(line):
            if tok.lower() in gate.NOT_A_NAME:
                continue
            if "_" not in tok and "." not in tok:
                continue
            if tok.endswith(".lean"):
                continue
            last = tok.rsplit(".", 1)[-1]
            if last in modules:
                continue
            if last not in words:
                out.append(tok)
    return out


@pytest.fixture(scope="module")
def corpus():
    if not os.path.isdir(gate.LEAN):
        pytest.skip("Lean sources absent")
    blob = gate.source_blob()
    words = gate.live_words(blob)
    modules = {fn[:-5] for fn in os.listdir(gate.LEAN) if fn.endswith(".lean")}
    return words, modules


def test_every_cited_name_resolves(corpus):
    """No document may name a declaration the repo does not define.

    THE DOCUMENTS ARE THE POPULATION, so reading none of them is not a clean bill. `gate.DOCS`
    lives in a SIBLING repository (`_scratch/CURRENT`); with that repository absent, or either
    document renamed, the loop below `continue`d on every entry and the test reported PASS having
    scanned nothing — the exact shape this suite exists to refuse. Demonstrated by pointing
    `gate.SCRATCH` at a directory that does not exist: zero documents read, `bad == {}`, green.
    So the count of documents actually opened is asserted first, and an absent sibling repository
    SKIPS visibly rather than passing silently.
    """
    words, modules = corpus
    present = [n for n in gate.DOCS if os.path.exists(os.path.join(gate.SCRATCH, n))]
    if not present:
        if os.path.isdir(gate.SCRATCH):
            pytest.fail(
                f"{gate.SCRATCH} exists but holds none of {gate.DOCS}; the documents have been "
                "renamed or moved and this gate is scanning nothing. Update `DOCS` in "
                "`certify/doc_cites_live_declarations.py`.")
        pytest.skip(f"the sibling planning repository {gate.SCRATCH} is not present")
    bad: dict[str, list[str]] = {}
    for name in present:
        path = os.path.join(gate.SCRATCH, name)
        with open(path, encoding="utf-8", errors="replace") as fh:
            dead = _dead_for(fh.read(), words, modules)
        if dead:
            bad[name] = sorted(set(dead))
    assert not bad, (
        "the goal document cites names the repo does not define: "
        + "; ".join(f"{k}: {', '.join(v)}" for k, v in bad.items())
        + ". Repair the citation or delete the claim — a document that points at nothing "
          "cannot be checked at all.")


def test_the_gate_can_actually_fail(corpus):
    """PROOF the check is not vacuous: a name nothing defines must be reported dead.

    ⛔ THE INVENTED NAME IS ASSEMBLED AT RUNTIME, AND IT HAS TO BE. The corpus includes
    `research/code`, so THIS FILE is part of it — a negative control written as a literal defines
    the very name it claims nothing defines, and the control passes vacuously. That is not
    hypothetical: the literal form of this test failed on its first run, which is the only reason
    the self-reference was noticed.
    """
    words, modules = corpus
    invented = "_".join(["no", "such", "declaration", "anywhere", "in", "this", "repo"])
    assert _dead_for(f"`ReflectionHalfSpace.{invented}`", words, modules) == [
        f"ReflectionHalfSpace.{invented}"]


def test_a_live_name_is_not_reported(corpus):
    """And the converse: a declaration the tree really has must pass.

    `pairing_eq_weighted_square` is `ActionSplit`'s three-block identity and is not going away.
    """
    words, modules = corpus
    assert _dead_for("`ActionSplit.pairing_eq_weighted_square`", words, modules) == []


def test_scanning_no_document_is_not_a_pass(corpus, tmp_path, monkeypatch):
    """POSITIVE CONTROL for the population, not for the classifier.

    Every other control here plants a name and checks the verdict. None of them could tell that the
    gate had read zero documents, because the verdict on an empty corpus is the same word as the
    verdict on a clean one. This drives the gate at a directory holding no document and requires it
    to refuse — and at a missing directory, where a visible skip is the correct answer.
    """
    monkeypatch.setattr(gate, "SCRATCH", str(tmp_path))          # exists, holds nothing
    with pytest.raises(BaseException) as e:
        test_every_cited_name_resolves(corpus)
    assert "holds none of" in str(e.value), (
        f"an empty document directory did not make the gate refuse: {e.value}")

    monkeypatch.setattr(gate, "SCRATCH", str(tmp_path / "absent"))  # not a directory at all
    with pytest.raises(BaseException) as e:
        test_every_cited_name_resolves(corpus)
    assert "is not present" in str(e.value), (
        f"a missing sibling repository did not raise a visible skip: {e.value}")


def test_a_file_name_is_not_a_citation(corpus):
    """`Foo.lean` is a file, not a declaration, and reporting it would drown the real hits."""
    words, modules = corpus
    assert _dead_for("`ReflectionHalfSpace.lean`", words, modules) == []
