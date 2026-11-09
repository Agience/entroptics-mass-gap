# research/code

The Python side of the release: the lattice ensemble generator, the exact checks behind the formalized statements, the Monte Carlo reads of section 10 of the paper, the Lean build driver, the certification scripts and the tests. The committed data these scripts produce are in `research/data/`, and the one entry point that regenerates them is `research/data/regen_all.py` (see `research/data/README.md`).

Two kinds of result come out of this directory, and they are kept apart throughout:

- Exact check: a deterministic computation with no sampling (closed forms, exact character sums, quadrature, or a deterministic map applied to a stated configuration). These support the premises of formalized statements.
- Monte Carlo evidence: an ensemble average with a jackknife error, read from the lattice ensembles. No Monte Carlo number supports a theorem.

## Setup

```bash
pip install -r research/requirements.txt
```

`research/requirements-release.txt` is the exact pin set of the release. Scripts that read ensembles need `CONFIGS`, the root of an ensemble store in the layout of the data record (DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110)). Set it in the environment or in `research.local.env` at the repository root (copy `research.local.env.example`); `store_path.py` resolves it and refuses to run without it. No script downloads the dataset.

## Layout

### Generator and shared modules

| file | what it does |
|---|---|
| `lattice_generator.py` | Wilson-action generator (heat bath and over-relaxation) on numpy or torch, batched; deterministic from its seed; writes shards, `params.json` and `SHA256SUMS` per campaign. Every ensemble comes from it. |
| `entroptics_adapter.py` | typed adapter over the `entroptics` library; refuses an installed release older than the pin (0.2.10) |
| `store_path.py` | resolves the ensemble store root from `CONFIGS` (environment first, then `research.local.env`); no fallback |
| `table.py` | CSV writer used by the data scripts |
| `check_driver.py` | shared driver of the exact checks: runs a script's sections in order, prints each section's time and asserts the run-time budget the script states |

### Exact checks (`*_checks.py`, `e8_structure.py`)

Each prints its numbers and asserts what the corresponding Lean statements use, and exits 0 when every assertion holds. No Monte Carlo; each runs in seconds on a laptop with `python research/code/<name>.py`. Several also assert their own wall-time budget (10 s), so on a loaded machine a check can fail on time alone; run it again by itself.

| scripts | subject |
|---|---|
| `finite_information_checks.py`, `non_abelian_forget_checks.py`, `gap_l2_checks.py`, `aperture_invariance_checks.py`, `no_transition_checks.py`, `fine_end_checks.py`, `fixed_aperture_checks.py`, `relative_gap_checks.py`, `layer_rate_checks.py`, `uniform_aperture_checks.py` | finite-alphabet contraction, maximal correlation over cells, ratio and floor statements, free-photon and Gaussian controls |
| `cond_gap_checks.py`, `fine_links_checks.py`, `cell_links_checks.py`, `match_checks.py`, `one_way_cost_checks.py`, `flux_tube_checks.py`, `vortex_checks.py` | box, cell, matching, flux-tube and centre-vortex statements (two-dimensional exact solutions, character sums) |
| `mk_bound_checks.py`, `no_transition_flow_checks.py` | Migdal–Kadanoff recursions: an exact check of a defined model, not a bound on the four-dimensional Wilson measure |
| `e6_checks.py`, `e7_checks.py`, `e8_structure.py`, `f4_checks.py` | coordinates and structure constants of the exceptional-group modules |

### Certification (`certify/`)

| scripts | kind | needs |
|---|---|---|
| `small_volume_enclosure.py`, `lattice_animal_count.py`, `z2_polymer_hard_core.py` | exact check (small-volume enclosure for the SU(2) Kogut–Susskind Hamiltonian; counts of connected plaquette sets; an exact Z_2 negative control) | nothing |
| `lean_axiom_footprints.py` | exact check of the formalization: `#print axioms` for every declaration, written to `research/data/13_dat_axiom_footprints.csv` | a Lean build |
| `doc_cites_live_declarations.py`, `lean_duplicate_declarations.py`, `lean_vacuous_existentials.py`, `lean_derived_literals.py` | consistency of the documents and the Lean sources: every backticked declaration in `README.md`, `research/FORMALIZATION.md` and the paper's sections resolves; duplicate statements, vacuous existentials and undeclared literals do not grow. `lean_duplicate_declarations.py` and `lean_derived_literals.py` take a subcommand (`scan` for the whole tree) | Lean sources only |
| `structural_numerals.py` | the numerals (`0`, `1`, `2`, `4`) the two Lean numeral ratchets treat as structural, with the reason; read by `lean_derived_literals.py` and `tests/test_no_undeclared_lean_constants.py` | nothing |

### Lean build

`lean_build.py` builds `research/lean` locally, or on the host named by `LEAN_BUILD_HOST` over ssh. The direct route is `cd research/lean; lake exe cache get; lake build`.

### Observer-route reads (`observer/`)

The Monte Carlo reads of section 10 and the figure script. `observer/README.md` lists every script with its inputs and the result file it writes into `research/data/observer/`. The `*_gpu.py` reads, `smear_read.py` and `vis2_read.py` run on CUDA in 32-bit floats through torch; `OBS_DEVICE=numpy` runs them on the CPU. `observer/plot_observer.py` draws the six figures `research/data/obs_fig_*.png` from the committed JSON in `research/data/observer/` and needs neither the ensembles nor a GPU.

### Producers cited by Lean docstrings (`lab/`)

Three numpy-only scripts whose outputs Lean docstrings quote; no Lean proof depends on them. `lab/ds_unit.py` prints the mean boundary influence `ρ_V` of a box for the Gaussian field (`DSBoxFloor`, `DSBlockContract`, `ObserverRegime`: `1` when massless at every size). `lab/lx_threshold.py scalar|gauge` prints the weighted finite-size threshold `t_l` (`WeightedBox`, `WeightedKnabe`). `lab/emit_profile.py 15 0.15` emits the integer sine profile and its correlation sums that `WeightedProfile15` checks by `decide`.

### Tests (`tests/`)

`python -m pytest -q research/code/tests`. The physics tests (`test_generator*.py`, `test_connected_correlator.py`, `test_reads.py`, `test_smearing_chunks_change_nothing.py` and others) generate their own ensembles and cache them in `tests/.ensemble-cache/` (git-ignored, keyed on the generator source); they take several minutes. The paper-and-Lean tests (`test_paper_matches_lean.py`, `test_paper_matches_artifacts.py`, `test_doc_cites_live_declarations.py`, `test_certifications_still_certify.py`) check `research/paper/mass-gap.md`, its section files and `research/FORMALIZATION.md` against the Lean tree, the committed data and the certification scripts. The remaining tests guard the repository's conventions; their `*_baseline.txt` files are ratchets that may only shrink, and a ratchet whose debt reached zero has no baseline file (its retired-debt test then skips). Some tests skip by design where their input is absent: the store checks of `test_ensembles_are_thermalised.py` without `CONFIGS`, and the Mathlib-name check of `test_paper_matches_lean.py` when a cited name resolves neither in the Lean sources nor in a Mathlib it can reach (`research/lean/.lake/packages/mathlib`, where `lake build` in `research/lean` puts it, or the builder named by `LEAN_BUILD_HOST`).

## Supporting files

The paper names no script: section 12 points to this README, and section 10 names the committed result files. The files below produce no result that section 10 quotes; each ships because it is an exact check, a reusable tool, an import dependency of another script, or the generator of shipped data.

| file | why it ships |
|---|---|
| `table.py` | CSV writer imported by `research/data/store_run_thermalisation.py` |
| `certify/doc_cites_live_declarations.py`, `certify/lean_duplicate_declarations.py`, `certify/lean_vacuous_existentials.py`, `certify/lean_derived_literals.py` | consistency checks of the documents and the Lean sources, run by the tests |
| `observer/observer_step.py` | the observer step, plaquette, energy density and shard list every read imports |
| `observer/cap_test.py` | imported by the cited `tail_anatomy.py`; also a Haar-substrate check of the step's scaled energy density |
| `observer/cap_real.py`, `observer/mom_read.py`, `observer/three_point_read.py`, `observer/slice_read_gpu.py`, `observer/leak_cell.py` | producers of the committed `cap_real.jsonl`, `mom_read.jsonl`, `three_point_separated_su2.json`, `su2_L*_k*_c*.json` and `cellview_w1/leak_b2*.json` in `research/data/observer/` |
| `observer/obs4_read_gpu.py`, `observer/slab_cumulants.py` | the Lean-step slice sums behind `obs4_agg_*.json`, and the slab cumulants $\kappa_2/V$, $\kappa_4/V$ (values in `observer/README.md`) |
| `observer/sun_check.py` | exact check of the SU(N) observer step and readers against the SU(2) code |
| `observer/sun_campaign.py`, `observer/sun_launch.sh` | generator of the SU(3) campaigns whose reads are in `research/data/observer/su3/` |
| `observer/gen_su2_links.py` | generator of the SU(2) link campaigns of section 10 in their stored layout |
| `observer/gpu_equiv.py` | gate: the torch paths of `rot_read.py` and `cell_read.py` against their CPU paths |
| `observer/ld_local.py` | the same-box and enlarged-box local forms of the step on $L=4$ |

## Maintainer tooling (in the repository, not in the release archive)

Marked `export-ignore` in `.gitattributes`, so the release archive leaves them out:

- `remote_run.py` (with `tests/test_remote_run.py`): runs heavy Python on `COMPUTE_HOST` over ssh.
- `zenodo_deposit.py`, `zenodo_open_dataset.py`: stage and publish the data record; need `ZENODO_TOKEN`.
- `tests/test_provenance.py`: checks the committed artifacts, the release metadata and the ensemble store against each other.
