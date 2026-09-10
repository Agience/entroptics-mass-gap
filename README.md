# The Yang–Mills Mass Gap as a Finite-Aperture Effect

[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](LICENSE)
[![PyPI](https://img.shields.io/pypi/v/entroptics?logo=pypi&logoColor=white&label=entroptics)](https://pypi.org/project/entroptics/)
[![Verified](https://img.shields.io/badge/verified-Lean%204%20%2F%20Mathlib-4B0082)](research/lean)
[![DOI](https://zenodo.org/badge/1342269699.svg)](https://zenodo.org/badge/latestdoi/1342269699)
[![Sponsor](https://img.shields.io/badge/Sponsor-Agience-EA4AAA?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/Agience)

**Pure $SU(N)$ Yang–Mills has a mass gap because the vacuum is read through a finite aperture, which band-limits: the gap is the entropy margin $\Delta = \kappa_0 - \mu > 0$ below the counting floor $\kappa_0 = \tfrac14\ln 3$.**

This repository holds the paper, the formal development, and the analysis behind
*The Mass Gap of Pure $SU(N)$ Gauge Theory as a Finite-Aperture Effect* — the
[Entroptics](https://github.com/Agience/entroptics) reading of Yang–Mills, in which the mass gap is the finite
information capacity of a local observer's extraction screen: a finite aperture band-limits, so its predictive
excess decays at a positive rate.

## Author's note

Entroptics was the original find: a formalisation of an information structure I had long planned, using
entropy to characterize a *local resolution* for information artifacts.

I measured what I could with it — fast radio bursts, radio signals, market data — as calibration and
refinement. FRBs and QCD sit at opposite ends of the scale, the cosmological and the fundamental. Feeding it
QCD data is when I realised Entroptics could read the substrate the universe is built from. This paper is
what came of that.

Review, feedback and fixes are welcome.

## What it establishes

At **every physical coupling $\beta \ge 0$**, pure $SU(N)$ has a positive mass gap, non-triviality (the area law),
and Euclidean $SO(4)$ invariance. The gap is bounded below by the entropy margin, $\Delta(\beta) \ge \kappa_0 - \mu(\beta) > 0$:
the centre-vortex tension $\mu$ stays below the counting floor $\kappa_0 = \tfrac14\ln 3$ at every coupling, and
$\|C(\tau)\| \le M\,e^{-\Delta\tau}$. The result rests on four named inputs, of which three are classical results the development cites rather than
re-derives — the strong-coupling character bound (Osterwalder–Seiler), asymptotic freedom, and reflection
positivity of the Wilson ensemble. The fourth, a finite correlation length $\langle d^2\rangle \le 1$, is not a
cited theorem: it is discharged by measurement rather than by proof. Conditioned on the confinement read, the whole result
follows with reflection positivity as the only structural input.

The confinement read is measured on lattice ensembles and certified at **99.9999%** per coupling (a rigorous empirical-Bernstein
bound). The paper (`research/PAPER.md`) develops the theorem and the method; the reads run through the Entroptics
reader (`research/code/`); the Lean 4 / Mathlib development (`research/lean/`) is the verification — `sorry`-free, on
the three foundational axioms plus the named inputs.

**Existence and the gap, on a constructed object.** Beyond the gap, the finite-spacing Osterwalder–Schrader data is
instantiated for a constructed $SU(N)$ Wilson realisation (`ym_wilson`): `ym_existence_and_gap` delivers the mass gap
and an OS0–OS3-satisfying continuum measure on $\mathbb{R}^4$, and `ym_wightman` the reconstructed Wightman quantum
field theory. `ym_existence_and_gap` is a Lean/Mathlib **reduction** to the **four named cited results** above,
`sorry`-free; `ym_wightman` adds the Osterwalder–Schrader → Wightman reconstruction (two more, six in total). It
*consumes* those results rather than re-deriving them, and the $SU(N)$ ensemble enters through the entropy-matched
reads and the cited §2–§3 modelling identification. The exact axiom footprint of every theorem is stated in the
paper (§13).

## Layout

| path | what |
|---|---|
| [`research/PAPER.md`](research/PAPER.md) | the paper |
| [`research/lean/`](research/lean) | the Lean 4 / Mathlib development (`MassGap.*`), `sorry`-free |
| [`research/data/`](research/data) | analysis and figure scripts that read the frozen ensembles, and `regen_all.py`, which drives them |
| [`research/code/`](research/code) | the Entroptics wrapper + certification code |

## Verify the proofs

Prerequisite: the Lean toolchain manager [`elan`](https://github.com/leanprover/elan) (it reads `lean-toolchain`
and installs the pinned Lean 4 version automatically):

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
cd research/lean
lake exe cache get      # fetch the prebuilt Mathlib olean cache (no full Mathlib compile)
lake build              # builds MassGap.* against the cache — sorry-free
```

Check the axiom footprint yourself. Put this in a file under `research/lean` and run it with
`lake env lean <file>`; the single import brings every theorem below into scope:

```lean
import MassGap

#print axioms MassGap.ym_mass_gap
-- propext, Classical.choice, Quot.sound
-- + ym_character, ym_asymfree, wilson_reflection_positive, d2_le_bound   (the four named inputs)

#print axioms MassGap.ym_mass_gap_certified
-- the three foundational + wilson_reflection_positive only  (conditioned on the confinement read)

#print axioms MassGap.ym_existence_and_gap
-- the three foundational + the four named inputs  (existence and the gap, for a constructed SU(N) realisation)

#print axioms MassGap.ym_wightman
-- + os_reconstruction, WightmanTheory  (the reconstructed Wightman quantum field theory)

#print axioms MassGap.CellEnclosure.ym_volume_gap_cell_grounded
-- the three foundational only  (the volume-uniform gap; radius from the machine-checked single cell)

#print axioms MassGap.WilsonGauge.ym_continuum_gauge
-- the three foundational only  (the OS0-OS3 continuum measure on the genuine SU(N) Haar measure)
```

## Data

The empirical reads run on frozen Monte-Carlo action-density ensembles for compact U(1), SU(2), and SU(3)
— **77 ensembles across 216 shards, 11,356 configurations, 21.97 GB** — on Zenodo under **CC-BY-4.0**, regenerable from the seed
manifest. Every figure and certificate in §8–§9 regenerates from them by the named script in `research/data/`.

The ensembles are a **separate multi-gigabyte data release**, *Entroptics lattice gauge-theory action-density
ensembles (U(1), SU(2), SU(3))* — DOI [10.5281/zenodo.22650079](https://doi.org/10.5281/zenodo.22650079), with
its own citation. The record and its metadata are public; the files are access-by-request. They are not in this
repository and no script here downloads them. Once you have them, point the code at the store — either per run,

```bash
CONFIGS=/path/to/entroptics-lattice python research/data/regen_all.py --only 8_7
```

or once for the machine, by copying `research.local.env.example` to `research.local.env` (git-ignored) and
setting `CONFIGS` there. There is no default: a script run without either refuses, and says which release it
wants and where to put the setting.

## Cite

Cite the software record for this repository (the DOI badge) and the dataset record. The paper's §13 lists the
data-availability details. The lattice ensembles are a separate data release with their own DOI and their own licence.

Security issues: email **connect@agience.ai** rather than opening a public issue.

Licensed under Apache-2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).

## Declaration of generative AI use

The author used Anthropic's Claude Opus (versions 4.8 and 5) in the preparation of this work. Its
contribution was to write code, and to generate and validate content. The ideas, the construction
and the claims are the author's. No other generative AI tool was used. The author reviewed and
edited all output and takes full responsibility for the content of this publication.
