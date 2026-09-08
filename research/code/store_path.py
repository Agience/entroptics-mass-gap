"""Where the lattice ensemble store is -- resolved from configuration, never named in the source.

Every read in ``research/`` runs on a store of frozen Monte-Carlo ensembles that is NOT part of this
repository: it is a separate, multi-gigabyte data release with its own DOI, its own licence and its
own citation. This module is the single place that resolves where it is.

No source file names an absolute path to it. A hardcoded fallback would read nothing on every other
machine, and "reads nothing" is not the same as "fails": a reader that finds no shard for a coupling
can skip it and write a header-only artifact over a committed one, exiting 0. The store is therefore
named in exactly two places, neither of them source -- an environment variable and a git-ignored
local file -- and everything else asks here.

Resolution order, most specific first:

  1. the ``CONFIGS`` environment variable -- a one-off override for a single run, and what CI, a pod
     or a batch job sets;
  2. ``research.local.env`` at the repository root -- git-ignored, written once per machine, so a
     researcher does not have to remember an environment variable on every invocation;
  3. nothing. There is deliberately NO built-in default. A default would have to name somebody's
     filesystem, and being wrong quietly is precisely the failure being removed here.

Nothing resolves at import. Every caller reads the store inside a function, and the certification
scripts are imported (module level and all) by the smoke tests on machines that have no store at
all, so raising at import would turn "the store is not configured" into "the code does not load".
Callers that need a value at module level ask with ``required=False`` and get ``None``; the refusal
happens at the read, where it can say what was actually being looked for.
"""
from __future__ import annotations

import os
from pathlib import Path

#: The environment variable every script in the tree already took; kept, so nothing about how a
#: pod or a CI job is driven changes.
ENV_VAR = "CONFIGS"

#: Machine-local, git-ignored, at the repository root. One line: ``CONFIGS=<store root>``.
LOCAL_FILENAME = "research.local.env"

#: Committed alongside it, documenting the key and where the data comes from.
EXAMPLE_FILENAME = "research.local.env.example"

#: The data release, by the title it is archived under. Named in full in every failure, because a
#: researcher who has just cloned this repository has no other way to know what is missing.
RELEASE_TITLE = "Entroptics lattice gauge-theory action-density ensembles (U(1), SU(2), SU(3))"


class StoreNotConfigured(RuntimeError):
    """Neither the environment variable nor the local config file says where the store is.

    A distinct type so a caller that genuinely wants to continue without a store can catch exactly
    this and nothing else, rather than a ``FileNotFoundError`` raised several frames deeper, which
    is indistinguishable from a corrupt shard.
    """


def repo_root() -> Path:
    """The repository root, from this file's own location.

    Not from the working directory: these scripts are run from at least three of them (the repo
    root, ``research/data``, and ``research/code/certify`` -- ``regen_all`` chdirs into each owner's
    directory), so anything cwd-relative would resolve differently depending on the caller.

    The two config files sit at the repository ROOT, not under ``research/``, and that placement is
    load-bearing. ``test_no_source_file_names_a_machine_specific_absolute_path`` scans ``research/``
    recursively including ``.env`` files, and scans the root only for
    ``.yml/.yaml/.cff/.json/.md/.example`` -- deliberately not ``.env``. The research tree is
    therefore free of machine-specific absolute paths by construction, while the one file whose job
    is to name such a path lives just outside it. The ``research.`` prefix is what pays for that
    separation; keep both files where they are.
    """
    return Path(__file__).resolve().parents[2]


def local_config_path() -> Path:
    """Full path of the git-ignored local config file, whether or not it exists."""
    return repo_root() / LOCAL_FILENAME


def example_config_path() -> Path:
    """Full path of the committed example, which does exist."""
    return repo_root() / EXAMPLE_FILENAME


def local_value(key: str) -> str | None:
    """Any ``KEY`` from the machine-local config file, or None.

    A deliberately small parser -- ``KEY=VALUE``, ``#`` comments, an optional ``export`` prefix and
    optional surrounding quotes -- rather than a dependency on a dotenv package. A format that needs
    a library to read is a format a researcher cannot fix by hand.

    Generic in the key because the file now holds more than the store root: ``ZENODO_TOKEN`` lives
    here too, for the same reason ``CONFIGS`` does -- it is machine-local and must never be
    committed. One git-ignored file, one parser, so a second secret cannot arrive with a second
    ad-hoc reader that quotes or comments differently.
    """
    try:
        text = local_config_path().read_text(encoding="utf-8")
    except OSError:                                   # absent, unreadable: not configured, not fatal
        return None
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.lower().startswith("export "):
            line = line[len("export "):].lstrip()
        name, sep, value = line.partition("=")
        if not sep or name.strip() != key:
            continue
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in ("'", '"'):
            value = value[1:-1]
        if value:
            return value
    return None


def _from_local_file() -> str | None:
    """``CONFIGS`` from the local config file, or None."""
    return local_value(ENV_VAR)


def source() -> str | None:
    """Which of the two mechanisms is supplying the root, in words, or None if neither is.

    Reported in every failure: "the store is at X" is not actionable on its own when the reader is
    trying to work out which of two places to edit.
    """
    if os.environ.get(ENV_VAR, "").strip():
        return f"the {ENV_VAR} environment variable"
    if _from_local_file():
        return str(local_config_path())
    return None


def store_root(required: bool = True) -> str | None:
    """The store root as an absolute path.

    ``required=True`` (the default) raises :class:`StoreNotConfigured` carrying the full, actionable
    message. ``required=False`` returns None instead, for the module-level constants in the reading
    scripts -- see the note on import-time resolution in the module docstring.
    """
    value = os.environ.get(ENV_VAR, "").strip() or _from_local_file()
    if value:
        return os.path.abspath(os.path.expanduser(os.path.expandvars(value)))
    if required:
        raise StoreNotConfigured(help_text())
    return None


def collection(name: str, required: bool = True) -> str | None:
    """``<store root>/<name>`` -- one collection directory, e.g. ``configs_phase1``."""
    root = store_root(required=required)
    return None if root is None else os.path.join(root, name)


def collections(*names: str) -> list[str]:
    """The named collection directories, or an EMPTY LIST when the store is not configured.

    Empty rather than absent-and-raising, because this is what the module-level ``HOPS`` in the
    reading scripts is built from: with no hops every loader reports the ensemble as absent, which
    is the path those scripts already refuse on -- and that refusal now carries :func:`hint`.
    """
    root = store_root(required=False)
    return [] if root is None else [os.path.join(root, n) for n in names]


def help_text() -> str:
    """The whole story, for someone who has just cloned this repository and run a script.

    Names the variable, names the file, names the release and says it is a separate download.
    """
    return (
        f"The lattice ensemble store is not configured, so there is nothing to read.\n"
        f"\n"
        f"These reads run on the data release\n"
        f"\n"
        f"    {RELEASE_TITLE}\n"
        f"\n"
        f"-- a SEPARATE download of about 25 GB of tarballs (roughly 49 GB with the collections\n"
        f"unpacked beside them), CC-BY-4.0, archived with its own DOI and cited separately from\n"
        f"this repository. It is NOT in this repository, it is not fetched by any script here, and\n"
        f"it is far too large to be. Obtain it by downloading the dataset record, or regenerate it\n"
        f"deterministically from the seed manifest with the pinned Entroptics release (the store\n"
        f"documents the per-campaign updater / therm / seed map).\n"
        f"\n"
        f"Then tell this repository where you put it, either way round:\n"
        f"\n"
        f"  1. set the {ENV_VAR} environment variable for one run:\n"
        f"         {ENV_VAR}=/path/to/entroptics-lattice python <script>\n"
        f"\n"
        f"  2. or set it once for this machine, in {local_config_path()}\n"
        f"     (git-ignored; copy {EXAMPLE_FILENAME} to {LOCAL_FILENAME} and edit it):\n"
        f"         {ENV_VAR}=/path/to/entroptics-lattice\n"
        f"\n"
        f"The root is the directory holding the configs_* collections, not one of them."
    )


def hint() -> str:
    """One paragraph to append to a script's own refusal -- adapted to WHICH thing is wrong.

    Two very different failures reach the same ``raise`` in the reading scripts: no store at all,
    and a store that is configured but does not hold what was asked for. Printing the same sentence
    for both sends the reader to the wrong place, so this distinguishes them.
    """
    root = store_root(required=False)
    if root is None:
        return help_text()
    return (
        f"The store IS configured -- to\n"
        f"    {root}\n"
        f"(from {source()}) -- so this is not a missing setting. It is a store that does not hold\n"
        f"what was asked for: an incomplete, partial or wrongly-rooted copy of\n"
        f"    {RELEASE_TITLE}\n"
        f"The root is the directory holding the configs_* collections, not one of them. Check it\n"
        f"against the release's manifest and its SHA256SUMS before trusting anything read from it."
    )


def unavailable(*relparts: str) -> str | None:
    """None when the store (and the named path inside it) is there; otherwise why not, in full.

    The skip reason for tests that read the release. A bare ``f"not mounted at
    {root}"`` where ``root`` was the hardcoded drive letter, which told a reader on any other
    machine nothing at all -- neither that the path was a fallback nor that the data is a separate
    download.
    """
    root = store_root(required=False)
    if root is None:
        return help_text()
    target = os.path.join(root, *relparts) if relparts else root
    if not os.path.exists(target):
        return (
            f"the lattice ensemble store is configured to {root!r} (from {source()}), but "
            f"{target!r} is not there. {RELEASE_TITLE} is a separate multi-gigabyte download; "
            f"see {EXAMPLE_FILENAME} at the repository root."
        )
    return None


if __name__ == "__main__":                                   # pragma: no cover -- a shell entry point
    # `python research/code/store_path.py` prints the store root, so a shell script -- the publish
    # workflow's runner, a batch job -- locates it by the SAME rule the Python readers use instead
    # of re-implementing the lookup in bash and drifting from it.
    import sys as _sys

    try:
        print(store_root())
    except StoreNotConfigured as exc:                        # a clean refusal, not a traceback
        print(exc, file=_sys.stderr)
        raise SystemExit(2)
