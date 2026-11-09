# research/data

The committed data, the scripts that own them, the figures, and the entry point that regenerates all of them. The scripts behind section 10 of the paper live in `research/code/observer/` and write their aggregates into `research/data/observer/` here.

## Entry point: `regen_all.py`

Each committed table and figure has exactly one owner script, recorded in the table `OWNERS` in `regen_all.py`; running a script that is not the owner can overwrite an artifact with a different shape, so regenerate through `regen_all.py`.

```bash
python research/data/regen_all.py --list            # show the owner table and exit
python research/data/regen_all.py                   # regenerate everything runnable here
python research/data/regen_all.py --phase figures   # one phase: data | figures | certify
python research/data/regen_all.py --only plot       # substring match on the owner script name
python research/data/regen_all.py --verify          # compare artifacts to git HEAD; run nothing
python research/data/regen_all.py --include-heavy   # also run the bigmem, gpu and build jobs
```

Two further options: `--reserve-gb` (physical memory left for the host; a job needing more than what remains is refused rather than started, default 6.0) and `--max-threads` (BLAS threads per job, default cores minus 2).

Every job carries a resource class with a wall-time and memory budget:

| class | time budget | memory | meaning |
|---|---|---|---|
| `cpu` | 1800 s | 2 GB | a laptop, seconds to minutes |
| `cpu2h` | 7200 s | 8 GB | CPU-bound, tens of minutes |
| `long` | 28 800 s | 8 GB | CPU-light but hours |
| `bigmem` | 28 800 s | 72 GB | dense operators; no shipped job is in this class |
| `gpu` | 14 400 s | 8 GB | practical on CUDA; runs on the CPU slowly |
| `build` | 28 800 s | 16 GB | a Lean build, not a read |

`bigmem`, `gpu` and `build` run only with `--include-heavy`; skipped jobs are always reported. These are budgets the driver enforces, not timings on a reference machine.

## Artifacts

| artifact(s) | owner | class | basis | read by |
|---|---|---|---|---|
| `13_dat_axiom_footprints.csv` | `research/code/certify/lean_axiom_footprints.py` | build | exact: `#print axioms` on the built Lean tree | section 11; `tests/test_paper_matches_lean.py` |
| `store_dat_thermalisation.csv` | `store_run_thermalisation.py` | gpu | Monte Carlo: equilibrium check of every ensemble in the data record | `tests/test_ensembles_are_thermalised.py`, `tests/test_thermalisation_resume.py` |
| `obs_fig_observer.png`, `obs_fig_bore.png`, `obs_fig_correlator.png`, `obs_fig_cube_moments.png`, `obs_fig_step.png`, `obs_fig_influence_row.png` | `research/code/observer/plot_observer.py` | cpu | drawn from the committed files in `observer/`; the first two are diagrams drawn from the paper's definitions | `tests/test_paper_matches_artifacts.py` (the paper does not embed them) |
| (none; prints a verdict) | `research/code/certify/small_volume_enclosure.py` | cpu | exact check | `tests/test_certifications_still_certify.py` |

`store_run_thermalisation.py` needs `CONFIGS` set to the root of the ensemble data record (DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110)); see `research/code/README.md`. The figures need neither the ensembles nor a GPU: `python research/data/regen_all.py --phase figures`.

## `observer/`

`observer/` holds the aggregated reads behind section 10 of the paper (JSON, JSONL and text, with subdirectories `cellview`, `cellview_w1`, `influence`, `influence2`, `influence3`, `su3`, `u1`, `glue`, `obs4_cube`). Each file is written by a script in `research/code/observer/`, listed with its inputs in `research/code/observer/README.md`. The `su3/su3_L16_b*/` directories are campaign records (`params.json`, `SHA256SUMS`, per-chain plaquette histories `plaq_c*.npy`) written by `sun_launch.sh` and `sun_campaign.py`; the links themselves are not archived. All are Monte Carlo evidence, apart from the observer-step reads of section 10 (the smearing step on stated configurations, from `stepbound.py` and `ld_adv.py`), which are exact checks; the rest of that read evaluates random starts with no ensemble and no statistical error. The per-shard intermediate arrays the reads produce are not archived, apart from those in `obs4_cube/` below, and the ensembles of section 10 are not in the data record (section 12 of the paper), so these aggregates are the published output of those reads.

Copied unchanged from the output of the campaign that produced them:

| files | producer |
|---|---|
| `u1/cell/w1_u1_b{0.8,1.2}_b{4,6,8}.json` (compact U(1) cell-energy W1 row, 24^4, step n = 8) | `cellview_w1.py` on `u1_cell_read.py` cells |
| `u1/joint/a_*.json` (links on links), `ctl_*.json` (raw-link control), `x_*.json` (cross blocks), `d_*.json` (energies on energies), `SHA256SUMS` | `u1_coarse_read.py`, `u1_joint_cross.py`, `cellview_w1.py` |
| `glue/glue2_b2.50_L48_mb10.{txt,json}`, `glue/glue2_b2.50_L32_mb10.{txt,json}`, `glue/glue2_b2.70_mb10.{txt,json}` (0++ effective masses) | `glueball_agg.py` |
| `u1/boxgap/u1_b1.2_n{3,4}_thermal.json` (box-gap upper reading) | `box_gap_read.py` |
| `obs4_cube/obs4_mc/`, `obs4_cube/obs4_mc2/` (slice sums, (chain, T) per measurement, n = 113) | `obs4_read_gpu.py` |
| `obs4_cube/cube_mc/`, `obs4_cube/cube_mc2/` (cube sums, (chain, ncubes) per measurement, n = 105, side 11) | `cube_read_gpu.py` |
| `obs4_cube/scan_b250_4d_c0.15/links_*_4d_c0.15.npz`, `SHA256SUMS` (beta 2.50, 32^4, twelve shards: slice sums S (n, chain, T) and plaquette densities e4, e3 at step counts n = 20..44, four-direction step, c = 0.15) | `leanstep_scan_gpu.py` |

`obs4_cube_agg_270.json` is aggregated from the `obs4_cube/` arrays by `research/code/observer/aggregate_obs4_cube.py`, which runs no simulation: the four-chain beta 2.70 correlator at the beta 2.50 times and the cube moments with their per-p roots against `cube_moments.json`, and (`correlator_beta250`) the beta 2.50 column of the section 10 correlator table, read from `obs4_cube/scan_b250_4d_c0.15/` at step count n = 30 with r0/a = 6.12, the centre of the Sommer range. That column is the one `plot_observer.py` draws as typed values; they agree with this read to the rounding of the last digit (11.675 +- 0.485, 9.744 +- 0.463, 6.296 +- 0.419, 3.506 +- 0.358, 1.765 +- 0.294 at t/r0 = 0 to 0.65).

`u1/joint/joint_rho.json` is aggregated from `u1/joint/a_*`, `x_*` and `d_*` by `research/code/observer/aggregate_u1_joint.py`, which runs no simulation: per coupling and cell side the four blocks of the joint near row (links on links, links from energies, energies from links, energies on energies) and the Perron root of that 2 x 2 matrix, with the cross-fit reads (`rho`: 0.21, 0.34, 0.59 at beta 0.8 and 9.80, 9.92, 15.69 at beta 1.2, cell sides 4, 6, 8) and, beside them, the plug-in suprema (`rho_sup`).
