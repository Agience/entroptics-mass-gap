# The Yang–Mills Mass Gap as a Finite-Aperture Effect

[![License](https://img.shields.io/badge/license-Apache%202.0-blue)](LICENSE)
[![PyPI](https://img.shields.io/pypi/v/entroptics?logo=pypi&logoColor=white&label=entroptics)](https://pypi.org/project/entroptics/)
[![Verified](https://img.shields.io/badge/verified-Lean%204%20%2F%20Mathlib-4B0082)](research/lean)
[![Paper](https://img.shields.io/badge/paper-PDF-b31b1b)](research/PAPER.pdf)
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
$\|C(\tau)\| \le M\,e^{-\Delta\tau}$.

**The floor takes no input.** Both of $\kappa_0$'s factors are theorems, not constants written down:
the $\ln 3$ is the branching of a directed cube-path (`Floor.directed_paths_card`) and the $\tfrac14$
is the reciprocal area per step — `CubeArea.boundary_card_eq`, that the surface bounding a $k$-step
path has exactly $4k+6$ faces — with `VortexCount.kappa0_is_the_surface_entropy_density` assembling
the two into $\log(\#\text{surfaces})/\text{area}\to\tfrac14\ln3$. Those surfaces are also closed
(`CubeClosed.edge_parity`, $\partial\partial=0$ over $Z_2$ at every interior edge), all pass through
one fixed face, and distinct paths bound distinct ones. Since pure Yang–Mills carries no dimensionful
parameter, a fitted constant anywhere below the gap would be a smuggled scale; $\kappa_0$ being a
counting number is what makes the transmutation legitimate, and it is now counted rather than quoted.

The result rests on four named inputs, of which three are classical results the development cites rather than
re-derives — the strong-coupling character bound (Osterwalder–Seiler), asymptotic freedom, and reflection
positivity of the Wilson ensemble. The fourth, a finite correlation length $\langle d^2\rangle \le 1$, is not a
cited theorem: it is discharged by measurement rather than by proof. Conditioned on the confinement read, the whole result
follows with reflection positivity as the only structural input.

The confinement read is measured on lattice ensembles and certified at **99.9999%** per coupling (a rigorous empirical-Bernstein
bound). The paper ([`research/PAPER.pdf`](research/PAPER.pdf)) develops the theorem and the method; the reads run through the Entroptics
reader (`research/code/`); the Lean 4 / Mathlib development (`research/lean/`) is the verification — `sorry`-free, on
the three foundational axioms plus the named inputs.

**Existence and the gap, on a constructed object.** Beyond the gap, the finite-spacing Osterwalder–Schrader data is
instantiated for a constructed $SU(N)$ Wilson realisation (`ym_wilson`). Read the two sides at their real strengths,
which are not the same:

* **Gap side** — `ym_existence_and_gap_of_junction` states it over an *arbitrary* mode family, gated on the two named
  open residuals (`hfe`, `hgap`). `ym_existence_and_gap` is its collapsed instance at the definitional single mode
  $m := e^{-(\kappa_0-\mu)}$, whose decay conjunct is therefore arithmetic; it witnesses that the hypotheses are
  satisfiable and is not evidence about the Wilson transfer operator.
* **Measure side** — what `Measure.continuum_of_family` proves is a bounded, nonnegative, invariance-preserving
  **subsequential pointwise limit** $q : J \to \mathbb{R}$ over a countable index set, by a diagonal
  Bolzano–Weierstrass argument. It is not a measure, not on $\mathbb{R}^4$, and not OS0–OS4: there is no Schwinger
  function, no reflection positivity of the limit as a quadratic form, no clustering and no regularity. Its
  invariance is inherited because it was built in — `ymFamily.os_euc` is `rfl`, since `QYM` reads only a label the
  $\mathrm{Perm}(\mathbb{F}_4)$ actions leave fixed. `ymFamily` is a minimal interface witness.

`ym_wightman` adds the Osterwalder–Schrader → Wightman reconstruction (two more axioms, six in total) on top of that
limit. The development *consumes* the cited results rather than re-deriving them, and the $SU(N)$ ensemble enters
through the entropy-matched reads and the cited §2–§3 modelling identification. The exact axiom footprint of every theorem is stated in the
paper (§13).

## Layout

| path | what |
|---|---|
| [`research/PAPER.pdf`](research/PAPER.pdf) | the paper, typeset |
| [`research/PAPER.md`](research/PAPER.md) | the same text in markdown |
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

#print axioms MassGap.ym_mass_gap_spectral
-- the three foundational + the four named inputs  (the gap over an ARBITRARY mode family, gated on the
-- finite-aperture margin as an EXPLICIT hypothesis: the physics is that hypothesis, not the footprint)

#print axioms MassGap.WitnessVacuity.const_witness_conclusion_is_arithmetic
-- the three foundational only  (and the module imports Mathlib ALONE: it reproduces, with no part of this
-- development in scope, the conclusion reached by instantiating the spectral bar at the constant witness
-- m ≡ 1/5 — so that instantiation is arithmetic, whatever its own footprint reads)

#print axioms MassGap.WilsonGauge.ym_continuum_gauge
-- the three foundational only  (the continuum LIMIT OBJECT — the same bounded, invariance-preserving
-- subsequential pointwise limit as above, but on a family whose Euclidean/permutation invariances are
-- DERIVED from Haar via Symmetry.expect_invariant rather than holding by `rfl`. That derivation is the
-- real content here; the limit object itself is still not a measure on R^4)

#print axioms MassGap.WilsonRead.sum_wilsonCorrReal_pos
-- the three foundational only  (the entropy-matched read of a GENUINE SU(2) Wilson Gibbs measure —
-- 8 links, 2 real ordered-loop plaquettes, real Wilson action, Haar — is UNCONDITIONAL: both of
-- Moment.Read's obligations are theorems. Nonnegativity replaces what wilson_reflection_positive
-- asserts for the opaque ensemble; positive total mass follows from the Z2 centre of SU(2). Every
-- declaration in MassGap/WilsonRead.lean carries these three axioms and nothing else)
```

## Data

The empirical reads run on frozen Monte-Carlo action-density ensembles for compact U(1), SU(2), and SU(3)
— **81 ensembles across 265 shards, 22,972 configurations, 22.27 GiB** — on Zenodo under **CC-BY-4.0**, regenerable from the seed
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
