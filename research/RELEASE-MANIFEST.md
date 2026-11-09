# Release manifest

What goes into the Zenodo software release of this repository and what stays out. The software record is archived by Zenodo's GitHub integration from a release tag (`.github/workflows/publish.yml`), so it holds the tracked files at that tag minus every path marked `export-ignore` in `.gitattributes`. The lattice ensembles are a separate record, DOI 10.5281/zenodo.22850110, and are not part of this one.

Material that is neither needed by a reader nor used by the maintainer is not in the repository: the long record (`PAPER.md`), its tables and their scripts, and the campaign plumbing for rented GPUs and one compute host are in the workspace archive, `_archive/entroptics-mass-gap-long-record-2026-11-07/`, at their repository paths. The earlier paper versions (`research/paper/sections/`, `v2/`, `mass-gap-draft1.pdf`, `mass-gap-v2.pdf`), the drafting, review and release notes of the paper, and the Lean prune list are in `_archive/2026-11-07-massgap-release/`, at their repository paths.

## Included

| path | reason |
|---|---|
| `README.md`, `LICENSE`, `NOTICE`, `CITATION.cff`, `.zenodo.json`, `CONTRIBUTING.md` | identity, licence (Apache 2.0) and citation of the record |
| `research.local.env.example` | documents the environment variables the scripts read; holds no machine path |
| `research/lean/` (sources, `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`) | the formal development that carries every theorem; every module under `MassGap/` is imported by `MassGap.lean`; not `.lake/` |
| `research/paper/` (`mass-gap.md`, `.html`, `.pdf`, `build_paper.py`, `v3/`, `figures/`) | the paper, one file per section, with its `*.lean-map.md` declaration tables, and the figures with their script |
| `research/FORMALIZATION.md` | the map from the paper's statements to Lean declarations |
| `research/requirements.txt`, `research/requirements-release.txt` | dependencies; the second is the exact pin set |
| `research/code/lattice_generator.py`, `entroptics_adapter.py`, `store_path.py`, `table.py`, `check_driver.py` | the generator every ensemble comes from, and the modules the scripts share |
| `research/code/*_checks.py`, `e8_structure.py` | the exact checks of section 12.5 |
| `research/code/lean_build.py` | the Lean build driver; runs locally when no build host is set |
| `research/code/certify/` | exact checks, the axiom footprints, and the document and Lean consistency checks |
| `research/code/observer/` | the Monte Carlo reads of section 10, their shared step, the generators and checks they rest on, and the figure script; `README.md` lists every script |
| `research/code/tests/` (tests, `conftest.py`, helpers, `*_baseline.txt`) | the physics, paper-against-Lean, paper-against-artifact and hygiene tests; baselines are inputs of the ratchet tests |
| `research/code/README.md`, `research/data/README.md` | layout and how to rerun |
| `research/data/regen_all.py`, `store_run_thermalisation.py` | the entry point and the owner scripts of the committed artifacts not owned under `research/code/` |
| `research/data/13_dat_axiom_footprints.csv`, `store_dat_thermalisation.csv`, `obs_fig_*.png`, `observer/` | the committed tables, figures and section 10 aggregates |
| `.gitattributes`, `.gitignore`, `.github/workflows/tests.yml` | line-ending convention, ignore rules and the test workflow a reader can rerun |

## Excluded (`export-ignore`; maintainer tooling kept in the repository)

| path | reason |
|---|---|
| `research.local.env`, `staged.json`, `research/code/staged.json` | one machine's paths and the Zenodo staging manifest of the data upload; git-ignored already |
| `__pycache__/`, `.pytest_cache/`, `research/code/tests/.ensemble-cache/`, `research/lean/.lake/` | caches, regenerated on demand; git-ignored already |
| `research/code/remote_run.py`, `research/code/tests/test_remote_run.py` | ssh dispatch to `COMPUTE_HOST`, and its test |
| `research/code/zenodo_deposit.py`, `zenodo_open_dataset.py` | deposit of the data record; need `ZENODO_TOKEN` |
| `research/code/tests/test_provenance.py` | checks the release metadata and the ensemble store against each other; needs the store and git history |
| `.github/workflows/publish.yml` | the maintainer's release gate |
| `research/RELEASE-MANIFEST.md` | this manifest |
