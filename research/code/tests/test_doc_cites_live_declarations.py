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

    THE DOCUMENTS ARE THE POPULATION, so reading none of them is not a clean bill: the verdict on an
    empty corpus is the same word as the verdict on a clean one. Every `gate.DOCS` entry is a tracked
    file of THIS repository, so a missing one is a failure rather than a skip — a rename or a move
    that leaves the gate scanning nothing is exactly what this asserts against. `gate._locate`
    searches every directory in `gate.DOC_DIRS`.
    """
    words, modules = corpus
    missing = [n for n in gate.DOCS if gate._locate(n) is None]
    assert not missing, (
        f"{missing} not found in any of {gate.DOC_DIRS}; the documents have been renamed or moved "
        "and this gate is scanning nothing. Update `DOCS` in "
        "`certify/doc_cites_live_declarations.py`.")
    bad: dict[str, list[str]] = {}
    for name in gate.DOCS:
        path = gate._locate(name)
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
    verdict on a clean one. This drives the gate at a directory holding no document, and at a
    directory that does not exist, and requires it to refuse in both cases.

    Both are failures rather than skips because `gate.DOCS` are tracked files of this repository: a
    checkout always has them, so not finding one means a move went unnoticed.
    """
    for where, why in ((str(tmp_path), "a directory holding no document"),
                       (str(tmp_path / "absent"), "a directory that does not exist")):
        monkeypatch.setattr(gate, "DOC_DIRS", [where])
        with pytest.raises(BaseException) as e:
            test_every_cited_name_resolves(corpus)
        assert "scanning nothing" in str(e.value), (
            f"{why} did not make the gate refuse: {e.value}")


def test_a_file_name_is_not_a_citation(corpus):
    """`Foo.lean` is a file, not a declaration, and reporting it would drown the real hits."""
    words, modules = corpus
    assert _dead_for("`ReflectionHalfSpace.lean`", words, modules) == []


def test_a_name_that_lives_only_in_prose_is_not_live():
    """PROOF of tier two, on the exact name that got past tier one.

    `RefinementLaw.refined_isGreatest` does not exist -- the declaration is `isGreatest_refined` --
    and it passed this gate because the docstring citing it put the word into the source blob, and
    the blob was the live set. A word-order swap is the commonest way to get a Lean name wrong, so
    that blind spot covered the likeliest failure.

    BOTH directions are asserted. A name planted in a comment must be absent from the code set, AND
    the real declaration must be present in it: either assertion alone passes vacuously, the first if
    the stripper ate everything and the second if it stripped nothing.
    """
    if not os.path.isdir(gate.LEAN):
        pytest.skip("Lean sources absent")
    planted = gate.strip_lean_comments(
        "/-- see `RefinementLaw." + "refined_isGreatest" + "` for the consumer. -/\n"
        "theorem isGreatest_refined : True := trivial\n")
    words = gate.live_words(planted)
    assert "refined_isGreatest" not in words, (
        "a name occurring only inside a Lean comment survived the stripper, so tier two cannot "
        "see the failure it exists for")
    assert "isGreatest_refined" in words, (
        "the stripper removed a `theorem` line, which would report every real declaration dead")


def test_the_stripper_handles_nested_block_comments():
    """Lean block comments NEST, and `/--` opens one.

    A non-nesting `/-.*?-/` stops at the first `-/` and leaves the tail of the outer comment in the
    code set -- the direction that hides a dead name, so it would not be caught by the test above.
    """
    src = "/- outer /- inner -/ still_commented -/\ntheorem real_one : True := trivial\n"
    words = gate.live_words(gate.strip_lean_comments(src))
    assert "still_commented" not in words, "the scanner closed on the INNER comment's terminator"
    assert "real_one" in words, "the scanner never closed, and ate the code after it"


def test_code_blob_is_smaller_than_source_blob():
    """POSITIVE CONTROL for the corpus, not the classifier.

    Every assertion above is on a planted string, so all of them would pass if `code_blob` read no
    files at all -- an empty code set reports every name prose-only, and the verdict on an empty
    corpus is not distinguishable from a strict one by a planted name.
    """
    if not os.path.isdir(gate.LEAN):
        pytest.skip("Lean sources absent")
    src = gate.live_words(gate.source_blob())
    code = gate.live_words(gate.code_blob())
    assert code, "the code corpus is empty; tier two would report every citation prose-only"
    assert code < src, "stripping comments removed nothing, so tier two is tier one"
