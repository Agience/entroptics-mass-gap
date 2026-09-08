"""Every committed artifact has exactly one owner, and every owner exists.

`research/data/regen_all.py` carries the provenance table as executable data, so it is checked against
the tree rather than trusted. Three properties are pinned:

  * every committed artifact is claimed by a script, so each one can be regenerated;
  * no artifact is claimed twice, so its content does not depend on which owner ran last;
  * every owner named in the table exists on disk.

These are filesystem and git facts, so the test costs milliseconds and needs no ensemble.
"""
from __future__ import annotations

import importlib.util
import subprocess
from collections import Counter
from pathlib import Path

import pytest

# research/code is on sys.path by the time this module is imported (conftest puts it there,
# so that `import entroptics` resolves to the wrapper). `store_path` is the one module that
# knows where the separate lattice ensemble store lives -- the tests below read the release
# itself, so they ask it rather than each carrying a path.
import store_path

REPO = Path(__file__).resolve().parents[3]          # entroptics-mass-gap/
REGEN = REPO / "research" / "data" / "regen_all.py"


def _load_regen():
    spec = importlib.util.spec_from_file_location("regen_all", REGEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _tracked_artifacts() -> list[str]:
    """Committed data artifacts, by basename, straight from git."""
    r = subprocess.run(
        ["git", "ls-files", "research/data/*.csv", "research/data/*.png"],
        cwd=REPO, capture_output=True, text=True)
    if r.returncode != 0:
        pytest.skip("not a git checkout; provenance is defined against the committed tree")
    return [Path(p).name for p in r.stdout.split()]


def test_regen_all_exists_and_loads():
    """The single entry point is importable -- a syntax error here breaks every regeneration."""
    assert REGEN.exists(), f"{REGEN} is missing: there is no way to regenerate anything"
    assert _load_regen().OWNERS, "the provenance table is empty"


def test_every_committed_artifact_has_exactly_one_owner():
    owned = Counter(a for arts, *_ in _load_regen().OWNERS for a in arts)
    tracked = _tracked_artifacts()

    duplicated = {a: n for a, n in owned.items() if n > 1}
    assert not duplicated, (
        f"artifacts claimed by more than one owner: {duplicated}. Two writers means the artifact "
        f"depends on which ran last, and they may not agree about its schema.")

    orphans = sorted(set(tracked) - set(owned))
    assert not orphans, (
        f"committed artifacts with no owner in regen_all.OWNERS: {orphans}. Nothing records how to "
        f"regenerate them.")


def test_no_owner_names_a_script_that_is_gone():
    """An owner entry may carry the arguments it must be run with, so the script is the first word."""
    missing = [(owner, str(d)) for _arts, owner, d, _p, _c in _load_regen().OWNERS
               if not (d / owner.split()[0]).exists()]
    assert not missing, f"OWNERS names scripts that do not exist: {missing}"


def test_every_listed_artifact_is_actually_tracked():
    """The table must not promise an artifact git does not carry."""
    tracked = set(_tracked_artifacts())
    listed = {a for arts, *_ in _load_regen().OWNERS for a in arts}
    untracked = sorted(listed - tracked)
    assert not untracked, (
        f"OWNERS lists artifacts that are not committed: {untracked}. Either commit them or drop "
        f"them from the table.")


def test_no_script_cites_a_file_that_does_not_exist():
    """Filenames mentioned in comments and docstrings resolve to something in the tree.

    A renamed artifact leaves its old name behind in whatever prose referred to it, pointing readers
    at a file that is gone. That is the same drift the owner table above prevents for artifacts,
    applied to the references scripts make in passing.

    Test files are excluded: their prose names example files on purpose.
    """
    import re

    root = REPO / "research"
    have = {p.name for p in root.rglob("*") if p.is_file()}
    pat = re.compile(r"[`\s(]([A-Za-z0-9_./]+\.(?:py|csv|png|lean|md|txt))")
    unresolved = {}
    # A name a program declares in code -- its own output path -- is not a dead reference, even
    # when the file is not in the tree yet because regenerating it is a pod job. What this test is
    # for is the opposite case: a rename that leaves the old name behind in prose, pointing a
    # reader at something gone. Whether a declared artifact is actually committed is a separate
    # invariant, held by test_every_listed_artifact_is_actually_tracked against regen_all.OWNERS.
    quo = chr(34) + chr(39)                     # a filename in a string literal, either quote style
    # `md` is here for the same reason as the rest: a name a program declares in code is a real
    # reference. zenodo_deposit.COMPANIONS lists the release's own documents, which live in the
    # separate ensemble store rather than under research/, so prose in that module naming them
    # resolves to nothing this scan can see -- and the citation pattern below does match `.md`.
    decl = re.compile("[" + quo + "]([A-Za-z0-9_./]+[.](?:csv|png|txt|md))[" + quo + "]")
    declared = set()
    for p in sorted(root.rglob("*.py")):
        # tests are not programs: a test naming an artifact must not exempt it
        if any(x in p.parts for x in (".lake", "__pycache__")) or p.parent.name == "tests":
            continue
        for line in p.read_text(encoding="utf-8", errors="replace").split(chr(10)):
            stripped = line.strip()
            if stripped.startswith("#") or '"""' in line:
                continue
            for m in decl.finditer(line):
                declared.add(m.group(1).split("/")[-1])

    for p in sorted(root.rglob("*.py")):
        if any(x in p.parts for x in (".lake", "__pycache__")) or p.parent.name == "tests":
            continue
        for line in p.read_text(encoding="utf-8", errors="replace").split(chr(10)):
            stripped = line.strip()
            if not (stripped.startswith("#") or '"""' in line or stripped.startswith("*")):
                continue
            for cited in pat.findall(line):
                name = cited.split("/")[-1]
                if name not in have and name not in declared:
                    unresolved.setdefault(name, set()).add(p.name)
    assert not unresolved, (
        "scripts cite files that do not exist: "
        + "; ".join(f"{n} (in {sorted(w)})" for n, w in sorted(unresolved.items())))


def test_no_function_is_implemented_twice():
    """No two scripts carry line-for-line identical implementations of the same function.

    Duplication here is not a style complaint: these functions are the certificates and the reads
    that the paper's numbers come out of -- `eb`/`d2_upper`, the empirical-Bernstein bound behind
    Sec 9, and `a_lambda`, the two-loop a*Lambda_lat that both the Sec 8.7b and Sec 8.8 scaling
    tests divide by. A correction to one copy leaves the other, and the two sections then disagree
    with no single line looking wrong.

    The test tree is excluded on purpose: test_paper_matches_artifacts keeps its own `_a_lambda`
    precisely so that it does not import the module it is checking, which is the one duplicate that
    earns its keep.
    """
    import ast
    import collections

    root = REPO / "research"
    seen = collections.defaultdict(set)
    for p in sorted(root.rglob("*.py")):
        if any(x in p.parts for x in (".lake", "__pycache__", "tests", "_archive")):
            continue
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        for node in ast.walk(tree):
            if not isinstance(node, ast.FunctionDef):
                continue
            body = [s for s in node.body
                    if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                            and isinstance(s.value.value, str))]
            # >= 2, not >= 3: `load` (a for-loop and a return) and `_resolve_device` are two
            # statements each and were duplicated under the old threshold without being seen.
            if len(body) >= 2:
                sig = ast.dump(ast.Module(body=body, type_ignores=[]))
                seen[(node.name, sig)].add(p.relative_to(root).as_posix())

    # Known outstanding duplication, with the reason it has not been collapsed. Anything not on this
    # list is a failure. Shrink this dict; do not grow it.
    KNOWN = {
        "pin": "closes over each module's own load()/ROOT, so sharing it needs a signature change "
               "across four config-reading scripts that cannot be regenerated locally to confirm "
               "the artifacts are unmoved",
        "load": "the group-generic loader, load(group, L, beta, ncap), in six config-reading "
                "scripts. The su2-specific loaders it shadowed ARE collapsed, onto "
                "aperture_reads.load_su2 -- which is why that one takes a dtype: the Sec 8.7 "
                "scripts read float32 for memory and the Sec 9 certificates read float64, and "
                "flattening that would silently change what the certificates compute. Collapsing "
                "these six is the same edit again, but they own committed artifacts and none of "
                "them can be run here, so it waits for a regeneration that can confirm the "
                "artifacts do not move.",
    }

    dupes = {name: sorted(files) for (name, _), files in seen.items() if len(files) > 1}
    unexpected = {n: f for n, f in dupes.items() if n not in KNOWN}
    assert not unexpected, (
        "these functions are implemented identically in more than one file; collapse them to one "
        "copy and import it: "
        + "; ".join(f"{n} in {f}" for n, f in sorted(unexpected.items())))

    stale = [n for n in KNOWN if n not in dupes]
    assert not stale, (
        f"KNOWN lists {stale} as outstanding duplication, but it is no longer duplicated -- "
        "remove the entry so the list keeps meaning something")


def test_committed_pdf_is_not_older_than_the_paper():
    """PAPER.pdf was rebuilt in the last commit that changed PAPER.md.

    The PDF is the form the paper is read in, so a correction that lands in the markdown and not in
    the PDF leaves the stale text in circulation. A correction to Sec 13's
    statement that the empirical-Bernstein uppers clear the aperture threshold "threefold" -- the
    factor belongs to the pinned proof bound, not the uppers -- and the committed PDF, last rebuilt
    in `315400a`, still carries the old wording.

    Compares committed state only, so work in progress does not trip it: it goes red when a commit
    changes the paper and leaves the PDF behind, and green again when the PDF is rebuilt.
    """
    import subprocess

    def last_commit(path):
        r = subprocess.run(["git", "log", "-1", "--format=%H", "--", path],
                           cwd=REPO, capture_output=True, text=True)
        return r.stdout.strip()

    md, pdf = last_commit("research/PAPER.md"), last_commit("research/PAPER.pdf")
    if not md or not pdf:
        pytest.skip("PAPER.md or PAPER.pdf is not tracked")
    if md == pdf:
        return                                        # rebuilt in the same commit

    # is the PDF's commit an ancestor of the paper's? then the paper moved afterwards
    r = subprocess.run(["git", "merge-base", "--is-ancestor", pdf, md], cwd=REPO)
    stale = r.returncode == 0
    subj = subprocess.run(["git", "log", "-1", "--format=%h %s", md], cwd=REPO,
                          capture_output=True, text=True).stdout.strip()
    assert not stale, (
        f"PAPER.pdf was last rebuilt in {pdf[:7]}, but PAPER.md changed afterwards in {subj}. "
        "The PDF is what the paper is read in, so it still shows the pre-correction text; rebuild "
        "and commit it with the paper.")


def test_release_figures_match_the_shipped_manifest():
    """The data-availability figures are the ones manifest.csv actually carries.

    Counts that summarise a growing release drift as collections are added, and the two totals are
    easy to conflate: the density subset is 223 shards and the whole deposit 259, the difference
    being the 36 raw-link shards. Each figure is therefore derived from manifest.csv rather than
    matched as text.

    This is the reproducibility statement and the dataset citation, so it is the paragraph a reader
    checks the archive against. Skips when the store is not mounted; the figures are only verifiable
    against the release itself.
    """
    import csv

    # The store is located by ``store_path``: the CONFIGS environment variable, then the
    # git-ignored local config file at the repository root, then nothing. ``unavailable``
    # hands back the whole actionable message -- which data release this is, that it is a
    # separate multi-gigabyte download, and the two ways to point at it -- so the skip line
    # says WHY. A bare "not mounted at <path>" names one machine and tells a reader on any
    # other nothing at all.
    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = store_path.store_root()
    manifest = Path(root) / "manifest.csv"

    with manifest.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    LINKS = "configs_links_su2"
    dens = [r for r in rows if r["collection"] != LINKS]
    link = [r for r in rows if r["collection"] == LINKS]

    ens = len({(r["group"], r["L"], r["beta"]) for r in dens})
    cfgs = sum(int(r["n_configs"]) for r in dens)
    gb = sum(int(r["bytes"]) for r in dens) / 1024 ** 3
    link_gb = sum(int(r["bytes"]) for r in link) / 1024 ** 3

    text = (REPO / "research" / "PAPER.md").read_text(encoding="utf-8")
    flat = " ".join(text.split())
    thousands = lambda n: f"{n:,}".replace(",", "{,}")

    # The paper states TWO different totals on purpose: the paragraph describes the density subset
    # the Sec 8 reads consume, and the dataset citation names the whole deposit, raw links
    # included. So each is checked in its own context rather than requiring one value everywhere --
    # and each is checked at EVERY occurrence within that context, because the counts appear more
    # than once and a check that finds the value somewhere passes when one copy has drifted.
    import re
    all_cfgs = sum(int(r["n_configs"]) for r in rows)
    cut = flat.find("Zenodo dataset")
    assert cut != -1, "the dataset citation is gone from the paper"
    para, cite = flat[:cut], flat[cut:]

    # only the thousands-separated form: Sec 8.8 says "512 configurations per coupling",
    # which is an ensemble size, not a release total
    CFG = r"(\d{1,3}\{,\}\d{3}) configurations"
    for label, blob, pat, want in (
            ("ensemble count", para, r"(\d+) ensembles", str(ens)),
            ("density configuration count", para, CFG, thousands(cfgs)),
            ("deposit configuration count", cite, CFG, thousands(all_cfgs)),
            ("deposit shard count", cite, r"(\d+) shards", str(len(rows)))):
        hits = re.findall(pat, blob)
        assert hits, f"the paper states no {label}"
        bad = [h for h in hits if h != want]
        assert not bad, (f"the paper states the {label} as {bad} in {len(bad)} of {len(hits)} "
                         f"places; the manifest gives {want}")

    # sizes and shard counts, in the paragraph that states them
    for label, needle in (
            ("density size", f"{gb:.2f} GB"),
            ("density shard count", f"{len(dens)} density shards"),
            ("verified shard count", f"all {len(rows)} shards verified"),
            ("raw-link shard count", f"{len(link)} raw-link shards"),
            ("raw-link size", f"{link_gb:.2f} GB")):
        assert needle in para, \
            f"the paper {label} does not match the manifest; expected to find {needle!r}"


def test_release_coverage_claims_match_the_manifest():
    """The coverage the paper describes is the coverage the release holds.

    Coverage is where a description and an archive part company most quietly: `configs_links_su2`
    holds four volumes (L = 8, 12, 16, 20) and Sec 8.7b's variational read uses all four, so a
    description naming fewer would make the volumes behind that table look unavailable. The
    beta=2.30 tower is seven volumes, which is what the Sec 8.7 L-scan reads.

    Skips when the store is not mounted.
    """
    import csv
    import re

    # The store is located by ``store_path``: the CONFIGS environment variable, then the
    # git-ignored local config file at the repository root, then nothing. ``unavailable``
    # hands back the whole actionable message -- which data release this is, that it is a
    # separate multi-gigabyte download, and the two ways to point at it -- so the skip line
    # says WHY. A bare "not mounted at <path>" names one machine and tells a reader on any
    # other nothing at all.
    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = store_path.store_root()
    manifest = Path(root) / "manifest.csv"
    with manifest.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))

    LINKS = "configs_links_su2"
    dens = [r for r in rows if r["collection"] != LINKS]
    link = [r for r in rows if r["collection"] == LINKS]
    flat = " ".join((REPO / "research" / "PAPER.md").read_text(encoding="utf-8").split())

    # the raw-link volumes, as a comma list
    link_Ls = sorted({int(r["L"]) for r in link})
    # closing "$" included: the tower list "$L=8,12,16,20,24,28,32$" CONTAINS "L=8,12,16,20", so a
    # bare substring check passes even when a volume has been dropped from the raw-link list
    assert "$L=" + ",".join(str(x) for x in link_Ls) + "$" in flat, (
        f"the paper does not list the raw-link volumes as {link_Ls}; "
        "a volume the Sec 8.7b table rests on would look unarchived")

    # the beta=2.30 su2 tower
    tower = sorted({int(r["L"]) for r in dens if r["group"] == "su2" and float(r["beta"]) == 2.30})
    assert f"tower $L={','.join(str(x) for x in tower)}$" in flat, \
        f"the paper does not list the beta=2.30 volume tower as {tower}"

    # per-group L coverage, as the paper states it ("SU(2) at L=8-32"). A group held at a single
    # volume has no range to state, so the bare form "U(1) at L=8" is the correct prose for it and
    # is accepted; the range form is still REQUIRED wherever the release spans more than one volume,
    # which is what stops a dropped volume passing as a narrowed claim.
    dash = "[" + chr(0x2013) + chr(0x2014) + "-]"
    for group, label in (("su2", "SU(2)"), ("su3", "SU(3)"), ("u1", "U(1)")):
        Ls = sorted({int(r["L"]) for r in dens if r["group"] == group})
        lo, hi = min(Ls), max(Ls)
        rng = re.search(re.escape(label) + r"\$ at \$L=(\d+)\$" + dash + r"\$(\d+)\$", flat)
        if lo != hi:
            assert rng, f"the paper states no L range for {label}, but the release holds {lo}-{hi}"
            assert (int(rng.group(1)), int(rng.group(2))) == (lo, hi), (
                f"the paper states {label} at L={rng.group(1)}-{rng.group(2)}, "
                f"but the release holds {lo}-{hi}")
            continue
        assert rng is None, (
            f"the paper states {label} at a range of volumes, but the release holds only L={lo}")
        one = re.search(re.escape(label) + r"\$ at \$L=(\d+)\$(?!" + dash + ")", flat)
        assert one, f"the paper states no L coverage for {label}"
        assert int(one.group(1)) == lo, (
            f"the paper states {label} at L={one.group(1)}, but the release holds L={lo}")

    # the shape and dtype the paragraph promises
    assert {r["dtype"] for r in dens} == {"float32"}, "not every density shard is float32"
    off = [r["filename"] for r in dens if int(r["T"]) != 2 * int(r["L"])]
    assert not off, f"the paper says T=2L for the density shards, but {len(off)} differ: {off[:3]}"


def test_the_release_manifest_and_the_store_agree():
    """Every manifest row has its file at the right size, and no shard on disk is unindexed.

    The paper's reproducibility claim is that a third party regenerates every read from these
    shards, which requires the index and the store to agree in both directions: a row without a
    file is a broken download, a file without a row is data the manifest does not vouch for, and a
    size mismatch is a truncated transfer, which exits 0 on the tools that produce it.

    Sizes only, no hashing: this walks 259 shards and must stay cheap. `SHA256SUMS` is the
    authority on content; a spot check of it is below.

    Skips when the store is not mounted.
    """
    import csv

    # The store is located by ``store_path``: the CONFIGS environment variable, then the
    # git-ignored local config file at the repository root, then nothing. ``unavailable``
    # hands back the whole actionable message -- which data release this is, that it is a
    # separate multi-gigabyte download, and the two ways to point at it -- so the skip line
    # says WHY. A bare "not mounted at <path>" names one machine and tells a reader on any
    # other nothing at all.
    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = store_path.store_root()
    manifest = Path(root) / "manifest.csv"
    with manifest.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    assert rows, "manifest.csv is empty"

    missing, wrong = [], []
    for r in rows:
        p = Path(root) / r["collection"] / r["filename"]
        if not p.exists():
            missing.append(str(p))
        elif p.stat().st_size != int(r["bytes"]):
            wrong.append(f"{r['filename']}: {p.stat().st_size} on disk, {r['bytes']} in the manifest")
    assert not missing, f"{len(missing)} indexed shards are absent: {missing[:4]}"
    assert not wrong, f"{len(wrong)} shards are the wrong size (truncated?): {wrong[:4]}"

    listed = {(r["collection"], r["filename"]) for r in rows}
    extra = []
    for coll in sorted({r["collection"] for r in rows}):
        d = Path(root) / coll
        if d.is_dir():
            extra += [(coll, f.name) for f in d.glob("*.npy") if (coll, f.name) not in listed]
    assert not extra, f"{len(extra)} shards on disk are not in the manifest: {extra[:4]}"

    sums = Path(root) / "SHA256SUMS"
    if sums.exists():
        n = sum(1 for line in sums.read_text(encoding="utf-8").splitlines() if line.strip())
        assert n == len(rows), \
            f"SHA256SUMS lists {n} files but the manifest indexes {len(rows)}"


def test_no_whole_collection_is_missing_from_the_manifest():
    """Every ``configs_*`` directory holding shards is represented in the manifest.

    The check above walks only the collections the manifest already names, so it finds a missing
    FILE and cannot find a missing COLLECTION -- the loop never looks at a directory no row
    mentions. This closes that.

    It matters because the store's ``make_manifest.py`` indexes a hand-maintained list of globs. A
    collection absent from that list ships inside the tarball while ``sha256sum -c`` still passes,
    so the release under-reports its own contents and nothing signals it. The assertion is
    therefore made against the directories on disk rather than against the list.
    """
    import csv

    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = Path(store_path.store_root())
    with (root / "manifest.csv").open(encoding="utf-8", newline="") as fh:
        indexed = {r["collection"] for r in csv.DictReader(fh)}

    on_disk = {d.name for d in root.glob("configs_*") if d.is_dir() and any(d.glob("*.npy"))}
    missing = sorted(on_disk - indexed)
    assert not missing, (
        f"{len(missing)} collection(s) hold shards that the manifest does not index at all, so "
        f"they ship unlisted and unchecksummed: {missing}. Add the glob to make_manifest.py's "
        f"KEEP and rebuild manifest.csv and SHA256SUMS.")


def test_a_sample_of_release_checksums_verify():
    """The manifest's SHA-256 is the file's, on a sample small enough to hash quickly.

    Not every shard: the store is 23 GB. One shard per collection, smallest first, so this stays
    under a few hundred MB and still exercises each collection's transfer.
    """
    import csv
    import hashlib

    # The store is located by ``store_path``: the CONFIGS environment variable, then the
    # git-ignored local config file at the repository root, then nothing. ``unavailable``
    # hands back the whole actionable message -- which data release this is, that it is a
    # separate multi-gigabyte download, and the two ways to point at it -- so the skip line
    # says WHY. A bare "not mounted at <path>" names one machine and tells a reader on any
    # other nothing at all.
    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = store_path.store_root()
    manifest = Path(root) / "manifest.csv"
    with manifest.open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))

    per_coll = {}
    for r in rows:
        c = r["collection"]
        if c not in per_coll or int(r["bytes"]) < int(per_coll[c]["bytes"]):
            per_coll[c] = r
    sample = [r for r in per_coll.values() if int(r["bytes"]) < 120_000_000]
    assert sample, "no shard small enough to sample"

    for r in sample:
        p = Path(root) / r["collection"] / r["filename"]
        h = hashlib.sha256()
        with p.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        assert h.hexdigest() == r["sha256"], \
            f"{r['collection']}/{r['filename']} does not match its manifest SHA-256"


def test_no_source_file_names_a_machine_specific_absolute_path():
    """No file in the tree hardcodes an absolute path on somebody's machine.

    This is the invariant behind `store_path`. A fallback of the form
    `os.environ.get("CONFIGS", <an absolute path>)` is a defect rather than a convenience: on any
    other machine the reads match nothing, and a reader that treats "matched nothing" as "skip this
    coupling" writes a header-only artifact over a committed one and exits 0. A published research
    repository cannot carry one machine's path as the definition of where its data is.

    The store is now named in exactly two places, neither of them source: the `CONFIGS` environment
    variable, and the git-ignored local config file whose committed example carries a placeholder.
    Everything else asks `store_path`.

    What is looked for: a drive-lettered path, and a per-user home directory. Both patterns are
    written so that this file's own source does not match them, and the tests directory is skipped
    anyway -- a test that states the shape it forbids must not be its own first offender.
    """
    import re

    # A drive-lettered path, and a user home directory. The lookbehind is what keeps a URL scheme
    # out of the first one: in "https" + "://x" the letter before the colon is itself preceded by
    # a letter, and in a bare drive letter it is not.
    drive = re.compile(r"(?<![A-Za-z0-9])[A-Za-z]:[\\/]")
    home = re.compile(r"(?<![A-Za-z0-9_.-])/(?:home|Users)/[A-Za-z0-9_.-]+")

    roots = [REPO / "research", REPO / ".github"]
    files = [p for r in roots if r.exists() for p in sorted(r.rglob("*"))
             if p.is_file() and p.suffix in (".py", ".yml", ".yaml", ".cff", ".json", ".env",
                                             ".example", ".md", ".txt")]
    files += [p for p in sorted(REPO.glob("*"))
              if p.is_file() and p.suffix in (".yml", ".yaml", ".cff", ".json", ".md", ".example")]

    offenders = {}
    for p in files:
        if any(x in p.parts for x in (".lake", "__pycache__", ".pytest_cache", "_scratch")):
            continue
        if p.parent.name == "tests":            # this file states the pattern it forbids
            continue
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            if drive.search(line) or home.search(line):
                offenders.setdefault(p.relative_to(REPO).as_posix(), []).append(i)

    assert not offenders, (
        "these files hardcode a machine-specific absolute path; resolve the store through "
        "store_path (CONFIGS, then the git-ignored local config file, then a refusal) instead: "
        + "; ".join(f"{f}:{ls}" for f, ls in sorted(offenders.items())))


def test_nothing_reaches_the_entroptics_library_except_the_adapter():
    """Every read goes through `entroptics_adapter`; nothing imports the library directly.

    The adapter is the front door on purpose: it pins the library version, refuses the library's
    i.i.d.-Gaussian floor for a physics read, and requires an explicitly pinned confined-vacuum null.
    A script that imported `entroptics` directly would bypass all three and could produce a number
    measured against the wrong reference while still looking like every other read in the tree.

    The adapter itself is exempt -- it is what does the importing, via `importlib.import_module`
    rather than a plain import so it does not shadow the installed package.
    """
    import ast

    root = REPO / "research"
    adapter = root / "code" / "entroptics_adapter.py"
    offenders = []
    for p in sorted(root.rglob("*.py")):
        if any(x in p.parts for x in (".lake", "__pycache__", "_archive")) or p == adapter:
            continue
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        for n in ast.walk(tree):
            names = []
            if isinstance(n, ast.Import):
                names = [a.name for a in n.names]
            elif isinstance(n, ast.ImportFrom):
                names = [n.module or ""]
            for name in names:
                head = name.split(".")[0]
                if head == "entroptics":                      # not entroptics_adapter
                    offenders.append(f"{p.relative_to(root).as_posix()}:{n.lineno}: {name}")
            # importlib.import_module("entroptics") outside the adapter is the same bypass
            if isinstance(n, ast.Call) and getattr(n.func, "attr", "") == "import_module":
                for a in n.args:
                    if isinstance(a, ast.Constant) and str(a.value).split(".")[0] == "entroptics":
                        offenders.append(f"{p.relative_to(root).as_posix()}:{n.lineno}: "
                                         f"importlib {a.value}")
    assert not offenders, (
        "these reach the entroptics library directly instead of research/code/entroptics_adapter.py:"
        "\n  " + "\n  ".join(offenders))


def test_no_script_writes_a_committed_artifact_it_does_not_own():
    """The OWNERS invariant, checked from the scripts rather than from the table.

    regen_all states it plainly: each committed artifact is produced by exactly ONE script, because
    running a non-owner overwrites it. `test_every_listed_artifact_is_actually_tracked` checks the
    table against git; nothing checked the other direction, and the tree violates it --
    `8_3_run_nobump_refnull.py` appears nowhere in OWNERS yet writes four committed artifacts, each
    registered to a different script.

    Three of those four carry a different schema, so a stray run shows up as a shape error. The
    fourth, 8_3_dat_confinement_order_parameter.csv, carries the OWNER's exact columns, so it
    overwrites with the same shape and different values -- the case that is hardest to notice.

    Detection is by filename in a write call, not any mention: a script that READS an artifact names
    it too, and reading is not the hazard.
    """
    import ast
    import re

    root = REPO / "research"
    regen = REGEN.read_text(encoding="utf-8")
    owner = {}
    for m in re.finditer(r"\(\s*\[([^\]]*)\]\s*,\s*\"([^\"]+)\"", regen):
        for art in re.findall(r"\"([^\"]+)\"", m.group(1)):
            owner[art] = m.group(2)
    assert owner, "OWNERS could not be parsed"

    committed = {p.name for p in (root / "data").iterdir()
                 if p.suffix in (".csv", ".png") and "_dat_" in p.name or p.suffix == ".png"}
    ART = re.compile(r"([0-9]+_[0-9]+_(?:dat|fig)_[A-Za-z0-9_]+\.(?:csv|png))")

    # Known and documented: an exploratory reader kept deliberately, whose docstring now names all
    # four writes and the same-schema hazard. Shrink this; do not grow it.
    KNOWN = {"8_3_run_nobump_refnull.py"}

    offenders = []
    for p in sorted(root.rglob("*.py")):
        if any(x in p.parts for x in (".lake", "__pycache__", "tests", "_archive")):
            continue
        try:
            tree = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        writes = set()
        for n in ast.walk(tree):
            if not isinstance(n, ast.Call):
                continue
            fname = getattr(n.func, "id", "") or getattr(n.func, "attr", "")
            if fname not in ("open", "write", "savefig", "to_csv", "save"):
                continue
            mode_is_write = fname != "open" or any(
                isinstance(a, ast.Constant) and isinstance(a.value, str) and "w" in a.value
                for a in list(n.args)[1:] + [k.value for k in n.keywords])
            if not mode_is_write:
                continue
            for sub in ast.walk(n):
                if isinstance(sub, ast.Constant) and isinstance(sub.value, str):
                    writes |= set(ART.findall(sub.value))
        for art in sorted(writes):
            if art in committed and owner.get(art) not in (p.name, None):
                if p.name in KNOWN:
                    continue
                offenders.append(f"{p.name} writes {art}, owned by {owner[art]}")
    assert not offenders, (
        "these write a committed artifact they do not own; a stray run replaces it:\n  "
        + "\n  ".join(offenders))


def test_every_committed_artifact_has_a_producer():
    """No artifact in research/data is owned by nobody, and OWNERS claims nothing that is absent.

    The complement of test_every_listed_artifact_is_actually_tracked, which checks the table against
    git. This checks git against the table. An artifact with no owner is data a reader cannot
    regenerate -- the state dataset [D] was in before its producer was identified -- and it is
    invisible to `regen_all --verify`, which iterates OWNERS and would never look at it.

    Both directions read git, so they are satisfiable together. A producer's first output is
    untracked and neither direction sees it; committing it is what asks for the OWNERS row. The
    ghost direction still reads the directory, since an artifact that is committed and listed but
    deleted from the working tree is exactly the drift worth catching.
    """
    import re

    root = REPO / "research"
    regen = REGEN.read_text(encoding="utf-8")
    owned = set()
    for m in re.finditer(r"\(\s*\[([^\]]*)\]\s*,\s*\"([^\"]+)\"", regen):
        owned |= set(re.findall(r"\"([^\"]+)\"", m.group(1)))
    assert owned, "OWNERS could not be parsed"

    present = {p.name for p in (root / "data").iterdir() if p.suffix in (".csv", ".png")}
    committed = set(_tracked_artifacts())
    orphan = sorted(committed - owned)
    ghost = sorted(owned - present)
    assert not orphan, (
        f"{len(orphan)} committed artifacts have no producer in OWNERS: {orphan}. Add each to its"
        f" producer's row in regen_all.OWNERS.")
    assert not ghost, (
        f"OWNERS claims {len(ghost)} artifacts that are not in research/data: {ghost}")


def test_every_lean_module_is_reachable_from_the_root():
    """Every MassGap/*.lean is imported, directly or transitively, from MassGap.lean.

    A module nothing imports is never elaborated: its theorems are not checked, and its
    `#print axioms` never runs, so a footprint the paper cites could come from a file the build does
    not read. Nothing else would notice -- the file exists, it parses, and
    test_cited_lean_declarations_resolve finds its declarations by grep.
    """
    import re

    lean = REPO / "research" / "lean"
    files = {p.stem for p in (lean / "MassGap").glob("*.lean")}
    assert files, "no MassGap modules found"

    imports = {}
    for m in sorted(files):
        src = (lean / "MassGap" / f"{m}.lean").read_text(encoding="utf-8", errors="replace")
        imports[m] = set(re.findall(r"^import MassGap\.([A-Za-z0-9_.]+)", src, re.M))

    root_src = (lean / "MassGap.lean").read_text(encoding="utf-8", errors="replace")
    stack = list(re.findall(r"^import MassGap\.([A-Za-z0-9_.]+)", root_src, re.M))
    assert stack, "MassGap.lean imports nothing"
    seen = set()
    while stack:
        m = stack.pop()
        if m in seen or m not in imports:
            continue
        seen.add(m)
        stack += list(imports[m])

    unreachable = sorted(files - seen)
    assert not unreachable, (
        "these Lean modules are never imported from MassGap.lean, so the build never elaborates "
        f"them and their `#print axioms` never runs: {unreachable}")


def test_the_paper_cites_the_software_version_the_code_pins():
    """The Entroptics version the paper cites is the one requirements.txt pins.

    Every read in Sec 8 goes through a wrapper that refuses to run against a different library
    version, so the pin IS the reproducibility claim. A bump in one place without the other would
    leave the paper citing a release that produces different numbers than the code will accept, and
    nothing else compares the two: the adapter checks the pin against what is installed, not against
    what the paper says.
    """
    import re

    req = (REPO / "research" / "requirements.txt").read_text(encoding="utf-8")
    m = re.search(r"^entroptics==([0-9]+\.[0-9]+\.[0-9]+)", req, re.M)
    assert m, "requirements.txt has no entroptics== pin"
    pinned = m.group(1)

    text = (REPO / "research" / "PAPER.md").read_text(encoding="utf-8")
    cited = re.findall(r"software v([0-9]+\.[0-9]+\.[0-9]+)", text)
    assert cited, "the paper cites no Entroptics software version"
    wrong = [v for v in cited if v != pinned]
    assert not wrong, (
        f"the paper cites Entroptics v{wrong} but research/requirements.txt pins {pinned}; "
        "the wrapper refuses any other version, so the paper names a release the code will not run")


def test_every_doi_the_paper_cites_matches_the_record_that_owns_it():
    """Each Zenodo DOI in the paper is the one the record it names actually carries.

    The paper cites two deposits, and each has an owner elsewhere in the tree:

      * the Entroptics SOFTWARE DOI, whose owner is this repository's CITATION.cff;
      * the lattice DATASET DOI, whose owner is the store's own CITATION.cff, shipped inside the
        deposit.

    Both are stated more than once in PAPER.md -- in the data-availability paragraph and again in
    the reference list -- and a changed digit in one copy points a reader at a different deposit, or
    at nothing. That is invisible to every numeric check in this suite, because a DOI is not a
    quantity: it cannot be recomputed, only compared against the record that owns it.

    Comparing against the owning records rather than against a constant written here is what makes
    this catch the real failure, which is two records disagreeing, not the paper disagreeing with
    the test. Skips the dataset half when the store is not mounted.
    """
    import re

    text = (REPO / "research" / "PAPER.md").read_text(encoding="utf-8")
    cited = set(re.findall(r"10\.5281/zenodo\.(\d+)", text))
    assert cited, "the paper cites no Zenodo DOI"

    def doi_in(path, label):
        """The zenodo id a CITATION.cff carries, from an uncommented `doi:` line."""
        if not path.exists():
            return None
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.strip().startswith("#"):
                continue
            m = re.search(r"doi:\s*\"?10\.5281/zenodo\.(\d+)", line)
            if m:
                return m.group(1)
        pytest.fail(f"{label} names no Zenodo DOI, so the paper's citation has nothing to check")

    expected = {}
    software = doi_in(REPO / "CITATION.cff", "the repository's CITATION.cff")
    if software:
        expected[software] = "the Entroptics software (repository CITATION.cff)"

    # The DATASET's owner of record, for this check, is the repository's .zenodo.json: it names the
    # deposit as a related identifier of resource_type "dataset", and it is in git, so this holds on
    # a runner with no ensemble store attached. Sourcing it from the store's CITATION.cff alone made
    # the dataset DOI unrecognisable wherever the store is absent -- which is every CI run -- and the
    # paper then looked like it cited a deposit nothing claimed.
    import json

    repo_zenodo = REPO / ".zenodo.json"
    if repo_zenodo.exists():
        meta = json.loads(repo_zenodo.read_text(encoding="utf-8"))
        for r in meta.get("related_identifiers", []):
            if r.get("resource_type") == "dataset":
                m = re.search(r"10\.5281/zenodo\.(\d+)", r.get("identifier", ""))
                if m:
                    expected[m.group(1)] = "the lattice dataset (repository .zenodo.json)"

    # When the store IS mounted, its CITATION.cff must agree with what the repository claims: two
    # records naming different deposits is the failure worth catching, and it is invisible otherwise.
    why = store_path.unavailable("CITATION.cff")
    if not why:
        dataset = doi_in(Path(store_path.store_root()) / "CITATION.cff", "the store's CITATION.cff")
        if dataset:
            claimed = {d for d, o in expected.items() if "dataset" in o}
            assert not claimed or dataset in claimed, (
                f"the store's CITATION.cff says the dataset is {dataset}, but the repository's "
                f".zenodo.json points at {sorted(claimed)}")
            expected[dataset] = "the lattice dataset (store CITATION.cff)"

    assert expected, "no record carries a DOI to check the paper against"

    unknown = sorted(cited - set(expected))
    assert not unknown, (
        f"the paper cites Zenodo deposit(s) {unknown} that no CITATION.cff claims; "
        f"the records carry {sorted(expected)}")

    for doi, owner in expected.items():
        if why and "dataset" in owner:
            continue
        assert doi in cited, f"the paper does not cite {doi}, the DOI of {owner}"
        assert len(re.findall(re.escape(doi), text)) >= 2, (
            f"the paper states {doi} ({owner}) only once; it belongs in both the "
            "data-availability paragraph and the reference list, and one copy going stale is "
            "exactly what this checks")


def test_no_job_needs_more_than_its_class_allows():
    """A cost class must be headroom ABOVE every job measured in it, never below one.

    `NEED_GB[cost]` is what a job of that class is sized against when its own peak is unknown, so a
    per-job figure that exceeds its class inverts the safety margin: the unmeasured jobs in the class
    are then sized by a number smaller than a job in the same class has already been watched to
    reach. That is how a preflight admits work onto a host that cannot hold it.

    A class whose ceiling sits below a job it admits cannot schedule that job. If `gap_of_margin` and
    `apriori_A1` 64.2; a host sized by 56 + reserve admitted both and the kernel killed one.
    """
    regen = _load_regen()
    per_job = getattr(regen, "NEED_GB_JOB", {})
    if not per_job:
        pytest.skip("no per-job peaks recorded yet")

    # every job in the table belongs to some owner, and that owner carries the cost class
    cost_of = {}
    for _arts, owner, _d, _phase, cost in regen.OWNERS:
        cost_of[owner.split()[0]] = cost

    unknown = sorted(s for s in per_job if s not in cost_of)
    assert not unknown, (
        f"NEED_GB_JOB names scripts that are not owners: {unknown}. A per-job size for a job "
        f"regen_all never runs is dead weight that will drift.")

    over = [(s, need, regen.NEED_GB[cost_of[s]]) for s, need in sorted(per_job.items())
            if need > regen.NEED_GB[cost_of[s]]]
    assert not over, (
        "a measured job needs more than its class allows for: "
        + "; ".join(f"{s} measured {need} GB but class '{cost_of[s]}' is {cls} GB"
                    for s, need, cls in over)
        + ". Raise the class above the largest job measured in it.")


def test_every_recorded_peak_is_a_positive_number():
    """Sizes are GB, so a zero or negative entry is a transcription error, not a measurement."""
    regen = _load_regen()
    bad = {k: v for k, v in getattr(regen, "NEED_GB_JOB", {}).items()
           if not isinstance(v, (int, float)) or v <= 0}
    assert not bad, f"NEED_GB_JOB carries non-positive sizes: {bad}"
    bad = {k: v for k, v in regen.NEED_GB.items()
           if not isinstance(v, (int, float)) or v <= 0}
    assert not bad, f"NEED_GB carries non-positive sizes: {bad}"


def test_no_artifact_reads_an_ensemble_the_store_no_longer_holds():
    """Every committed artifact that names its ensembles reads ones the store still carries, as they are now.

    An artifact records (group, L, beta) per row, so the ensembles behind it are recoverable from the
    file itself. Two ways it can go stale without any suite noticing, because both sides of every other
    check move together:

      * the ensemble is GONE from the store -- the artifact reports a measurement on configurations
        the release does not ship, so a reader cannot reproduce the row and cannot see why;
      * the ensemble was REGENERATED after the artifact was written -- the row is a measurement on
        configurations that no longer exist, and the paper transcribes it as current.

    Neither is visible to a paper-versus-artifact check: those pin the prose to the artifact and the
    artifact to nothing, so a stale pair agrees with itself. This is the third edge, artifact to store.

    Mtime is the comparison because regeneration rewrites the shard. It is coarse -- copying the store
    moves every shard forward at once -- so the failure names the ensembles and the dates, and a
    wholesale move shows up as every artifact failing rather than one.

    It reaches only the artifacts that carry `group`, `L` and `beta` per row, because those are the
    ones that say which ensembles they read. An artifact whose volume is fixed in its owner script
    instead of written into the row is invisible here, so a green run is evidence about the artifacts
    it counted -- which is why the count is asserted rather than assumed.

    Skips when the store is not mounted; the currency of an artifact is only checkable against it.
    """
    import csv
    import glob
    import time

    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    store = Path(store_path.store_root())

    def shards(group, L, beta):
        """Every shard for one ensemble, across collections; the filename carries beta to 2 places."""
        out = []
        for pat in (f"{group}_L{L}_b{float(beta):.2f}.s*.npy", f"{group}_L{L}_b{beta}.s*.npy"):
            out += glob.glob(str(store / "configs_*" / pat))
        return sorted(set(out))

    stamp = lambda t: time.strftime("%Y-%m-%d", time.localtime(t))
    checked, faults = 0, []
    for path in sorted((REPO / "research" / "data").glob("*_dat_*.csv")):
        with path.open(encoding="utf-8-sig", newline="") as fh:
            rows = list(csv.DictReader(fh))
        if not rows or not {"group", "L", "beta"} <= set(rows[0]):
            continue
        checked += 1
        written = path.stat().st_mtime
        absent, superseded = set(), set()
        for r in rows:
            key = (r["group"], r["L"], r["beta"])
            found = shards(*key)
            if not found:
                absent.add(key)
            elif max(Path(f).stat().st_mtime for f in found) > written:
                superseded.add(key)
        if absent or superseded:
            faults.append((path.name, stamp(written), len(rows), sorted(absent), sorted(superseded)))

    assert checked, "no committed artifact names its ensembles; this gate is checking nothing"
    assert not faults, "artifacts read ensembles the store no longer holds as they were: " + "; ".join(
        f"{name} (written {when}, {n} rows): "
        + (f"{len(a)} absent {a} " if a else "")
        + (f"{len(s)} regenerated since {s}" if s else "")
        for name, when, n, a, s in faults)


def test_the_store_readme_figures_match_its_own_manifest():
    """The release README's headline figures are the ones manifest.csv carries.

    README.md, CITATION.cff and .zenodo.json ship INSIDE the deposit, beside the manifest they
    describe. Nothing in this repository owns them -- they live in the store -- so no paper-versus-
    artifact check reaches them, and a reader who downloads the record gets a README that
    contradicts the index sitting next to it.

    That is not hypothetical: the README stated the pre-correction totals (259 ensembles, 13,548
    configurations, 23.00 GB, six collections) against a manifest holding 216 shards, 77 ensembles,
    11,356 configurations and seven collections.

    Each figure is parsed from the sentence that states it and compared with the manifest, so the
    failure names the one that drifted rather than reporting that some number somewhere is wrong.
    Skips when the store is not mounted.
    """
    import csv
    import re

    why = store_path.unavailable("manifest.csv")
    if why:
        pytest.skip(why)
    root = Path(store_path.store_root())

    readme = root / "README.md"
    assert readme.exists(), f"the release ships no README at {readme}"
    text = " ".join(readme.read_text(encoding="utf-8").split())

    # The repository's own README states the same totals in its Data section, and is a separate file
    # with a separate owner -- it carried 231 ensembles / 11,756 configurations / 11.13 GB against a
    # manifest holding 216 shards and 11,356 configurations, because nothing read it. It is checked
    # here rather than in its own test so that the two READMEs cannot drift apart from each other.
    repo_readme = " ".join((REPO / "README.md").read_text(encoding="utf-8").split())

    with (root / "manifest.csv").open(encoding="utf-8", newline="") as fh:
        rows = list(csv.DictReader(fh))
    shards = len(rows)
    ensembles = len({(r["group"], r["L"], r["beta"]) for r in rows})
    configs = sum(int(r["n_configs"]) for r in rows)
    gb = sum(int(r["bytes"]) for r in rows) / 1024 ** 3
    collections = len({r["collection"] for r in rows})

    # Anchored on the headline sentence rather than on the bare words: the README also states the
    # per-tarball shard counts of the two raw-link scans ("24 shards", "12 shards"), which are
    # different quantities, and an unanchored search reads those as a wrong total.
    TOTALS = (r"([\d,]+) ensembles across ([\d,]+) shards, ([\d,]+) configurations, ([\d.]+) GB")
    num = lambda s: int(s.replace(",", ""))
    for where, blob in (("release README", text), ("the repository README", repo_readme)):
        head = re.search(TOTALS, blob)
        assert head, (f"{where} no longer states its totals in the form "
                      "'N ensembles across N shards, N configurations, N GB'")
        for label, got, want in (("ensemble count", num(head.group(1)), ensembles),
                                 ("shard count", num(head.group(2)), shards),
                                 ("configuration count", num(head.group(3)), configs)):
            assert got == want, (f"{where} states the {label} as {got:,}, "
                                 f"but manifest.csv gives {want:,}")
        assert abs(float(head.group(4)) - gb) < 0.05, (
            f"{where} states {head.group(4)} GB, but manifest.csv totals {gb:.2f} GB")

    # the two raw-link tarballs are described by their own shard counts, and they must add up to
    # the raw-link collection the manifest carries
    link_shards = len([r for r in rows if r["collection"] == "configs_links_su2"])
    parts = [int(x) for x in re.findall(r"(\d+) shards", text)]
    assert parts, "the release README describes no per-tarball shard counts"
    assert link_shards in parts, (
        f"the release README's per-tarball shard counts are {parts}, none of which is the "
        f"{link_shards} raw-link shards manifest.csv carries")

    WORDS = {5: "five", 6: "six", 7: "seven", 8: "eight", 9: "nine"}
    word = WORDS.get(collections)
    assert word, f"the release holds {collections} collections; add that number to WORDS"
    assert f"{word} collections" in text, (
        f"manifest.csv holds {collections} collections, but the release README does not say "
        f"'{word} collections'")


def test_the_repository_record_names_the_dataset_and_its_author_consistently():
    """The repository's own .zenodo.json agrees with the paper and points at the data.

    This file is the metadata for the SOFTWARE record minted from the repository, so it is a fifth
    place the author and the deposit are described -- separate from PAPER.md, the two CITATION.cff
    files, and the dataset's .zenodo.json in the store. Nothing else in this suite reads it, and
    `zenodo_deposit.py` closes by telling an operator to add the dataset identifier here and calls
    that "the readiness gate", which until now did not exist.

    Three things are checked:

      * the creator's affiliation is the organisation, not the author's own given name -- these were
        both "Ikailo", so the field silently read as a person;
      * the ORCID matches the one the paper's byline states, since an ORCID that disagrees across
        records is worse than none at all;
      * a related identifier points at the lattice dataset, marked resource_type "dataset", so the
        software record and the data it was computed from are linked in both directions.
    """
    import json
    import re

    p = REPO / ".zenodo.json"
    assert p.exists(), "the repository has no .zenodo.json, so its Zenodo record has no metadata"
    meta = json.loads(p.read_text(encoding="utf-8"))

    creators = meta.get("creators") or []
    assert creators, ".zenodo.json names no creator"

    paper = (REPO / "research" / "PAPER.md").read_text(encoding="utf-8")
    byline_orcid = re.search(r"(\d{4}-\d{4}-\d{4}-\d{3}[\dX])", paper)

    for c in creators:
        name = c.get("name", "")
        aff = c.get("affiliation", "")
        assert aff, f"{name} has no affiliation"
        # Compared token by token, not against the whole given-name string. "Sessford, Ikailo John"
        # against an affiliation of "Ikailo" passes a whole-string comparison and is exactly the
        # error this catches: the author's first given name standing in for the organisation. An
        # organisation whose name merely CONTAINS a name token ("Ikailo Inc.") is not a single
        # token and is left alone.
        words = lambda s: {t.strip().lower() for t in s.replace(",", " ").split() if t.strip()}
        tokens, aff_tokens = words(name), words(aff)
        assert aff_tokens - tokens, (
            f"the affiliation is {aff!r}, every word of which is part of the author's own name "
            f"({name!r}), so it names the person rather than an organisation. An organisation that "
            "merely shares a word with the name is fine -- it carries something the name does not.")
        if byline_orcid:
            assert c.get("orcid") == byline_orcid.group(1), (
                f"{c.get('name')} carries ORCID {c.get('orcid')!r}, but the paper's byline states "
                f"{byline_orcid.group(1)}")

    datasets = [r for r in meta.get("related_identifiers", [])
                if r.get("resource_type") == "dataset"]
    assert datasets, (
        "no related identifier of resource_type 'dataset': the repository record does not point at "
        "the ensembles its results were computed from")

    why = store_path.unavailable("CITATION.cff")
    if why:
        pytest.skip(why + "  (author fields and the dataset link were checked)")
    store_cff = (Path(store_path.store_root()) / "CITATION.cff").read_text(encoding="utf-8")
    m = re.search(r"^doi:\s*\"?10\.5281/zenodo\.(\d+)", store_cff, flags=re.M)
    if not m:
        pytest.skip("the store's CITATION.cff carries no DOI yet")
    stated = {re.sub(r".*zenodo\.", "", r["identifier"]) for r in datasets}
    assert m.group(1) in stated, (
        f"the repository record links dataset(s) {sorted(stated)}, but the store's CITATION.cff "
        f"says the dataset is {m.group(1)}")


def test_the_release_ships_every_file_its_own_documentation_names():
    """A file the release's docs point at is a file the deposit carries.

    README.md and GENERATION.md are uploaded WITH the data and are what a reader has after
    downloading the record. When one of them names a file, that file has to be in the deposit or the
    reader is holding documentation that points at nothing -- and the deposit is where they cannot
    simply go and look, because it is not a repository they can browse.

    This is not hypothetical: GENERATION.md rests the release's central claim on
    `store_dat_thermalisation.csv` ("in this directory", the evidence that every ensemble is an
    equilibrium sample), and that file was not in COMPANIONS, so the record would have shipped the
    claim with its evidence missing.

    The staged set is `zenodo_deposit.COMPANIONS` plus the tarballs, so COMPANIONS is what is
    checked. Skips when the store is not mounted.
    """
    import importlib.util
    import re

    why = store_path.unavailable("GENERATION.md")
    if why:
        pytest.skip(why)
    root = Path(store_path.store_root())

    spec = importlib.util.spec_from_file_location(
        "zenodo_deposit", REPO / "research" / "code" / "zenodo_deposit.py")
    dep = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(dep)
    shipped = set(dep.COMPANIONS)

    # Names that read as a file in the release: a bare filename with a data/doc extension. Tarballs
    # are staged separately from COMPANIONS, so they count as shipped too.
    tarballs = {p.name for p in root.glob("*.tar")}
    pat = re.compile(r"`([A-Za-z0-9_.\-]+\.(?:csv|md|json|txt|py|cff|tar))`")

    missing = {}
    for doc in ("README.md", "GENERATION.md"):
        p = root / doc
        if not p.exists():
            continue
        for name in set(pat.findall(p.read_text(encoding="utf-8"))):
            if name in shipped or name in tarballs:
                continue
            if not (root / name).exists():
                continue          # names a file that is not in the store either: not a deposit gap
            missing.setdefault(name, []).append(doc)

    assert not missing, (
        "the release ships documentation naming files the deposit does not carry: "
        + "; ".join(f"{n} (named in {', '.join(d)}) exists in the store but is not in COMPANIONS"
                    for n, d in sorted(missing.items())))
