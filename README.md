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

Everything below is a Lean statement that compiles, axiom footprint included; the live account, theorem by
theorem, is [`research/CLAY-CHECKLIST.md`](research/CLAY-CHECKLIST.md) with its companion
[`research/CLAY-DETAIL.md`](research/CLAY-DETAIL.md).

**The lattice gap at every coupling, from one clustering inequality.** `PeriodicState.periodicState` is an
infinite-volume $SU(N)$ Wilson state at every coupling, built as a limit of periodic-lattice states,
reflection positive with a positive transfer operator at every $\beta \ge 0$
(`PeriodicState.periodic_positiveTransfer`). On it, for $2 \le N$ and every $\beta > 0$, one inequality per
gauge-invariant local observable — the connected reflected pairing at one lag $m$ at most $r^m$ times its
lag-zero value — gives the Clay lattice gap at rate $r$: the transfer operator self-adjoint, spectrum in
$\{1\} \cup [0, r]$, the vacuum complement contracted by $r < 1$ and non-zero
(`ChessboardRead.periodic_clayGapAt_of_torusLag`, `PeriodicContent.wilson_gaugeInv_mass_gap_every_coupling_periodic`).
At strong coupling the gap is proved outright, at the free-boundary limit state, for
`coreRate 64 β < 1` (`StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling`).

**The open input, in physical units.** `WeakCouplingWindow.FixedWindowDecay`: one factor $q < 1$, independent
of $\beta$, by which every gauge-invariant local observable's connected reflected pairing drops across a
fixed physical distance at every large $\beta$, with the spacing running as the two-loop
`AsymptoticScaling.aRun N`. It gives the Clay gap with a physical rate bounded below at every large
$\beta$, and holds exactly when that uniform physical gap does (`WeakCouplingWindow.fixedWindowDecay_iff`).
Its non-abelian content is neutral: every gauge-invariant observable is fixed by the centre twists
(`CentreTwist.centre_invisible_SU`), and a bound on the charged flux sectors fixes no neutral rate
(`CentreSector.charged_rate_does_not_reach_neutral`).

**The entropy floor and the reads.** $\kappa_0 = \tfrac14\ln 3$ is counted: the $\ln 3$ is the branching of
a directed cube-path (`Floor.directed_paths_card`) and the $\tfrac14$ the reciprocal area per step —
`CubeArea.boundary_card_eq`, the surface bounding a $k$-step path has exactly $4k+6$ faces — with
`VortexCount.kappa0_is_the_surface_entropy_density` assembling the two into
$\log(\text{number of surfaces})/\text{area}\to\tfrac14\ln3$; those surfaces are closed
(`CubeClosed.edge_parity_all`). The reads clear the floor at a window of physical extent $L$ and bracket
the physical gap there: the reads give at least $2.04/L$, and a gap of $20/L$ gives the reads
(`ReadConverse.readsClear_brackets_physical_gap`). So the reads at a fixed physical window are the uniform
physical gap in entroptic form.

**Non-triviality.** N is the connected three-point function of three separated gauge-invariant composites,
normalised by their two-point functions (`ThreePointN.sepRatio`): renormalisation-invariant, and $0$ in the
free theory. `ThreePointN.WilsonThreePointSeparation` — that ratio bounded below at the periodic state
along $\beta \to \infty$ — gives a non-zero continuum three-point function under every renormalisation
(`ThreePointN.wilson_continuum_threePoint`); it is the open input for N. On the lattice the plaquette's law
is non-Gaussian (`NonGaussian.nu_iplaqObs_law_not_gaussian`).

**Existence.** The continuum Schwinger functions along $\beta \to \infty$, their Osterwalder–Schrader axioms
and reconstruction are the open part of E. `Measure.continuum_of_family` is a bounded, nonnegative,
subsequential pointwise limit over a countable index set, by a diagonal Bolzano–Weierstrass argument; its
Wilson instances index the lattice extent at fixed $\beta$. The Osterwalder–Schrader → Wightman
reconstruction is stated in `WightmanData` as `os_reconstruction_wightman`, from `OSData` — a continuous
bilinear Schwinger form on a normed test space, with a reflection and an $\mathbb{R}^4$ translation
action — to `WightmanQFTData`.

**What the build carries.** Two named axioms beyond Lean's three foundational ones, counted by machine
([`13_dat_axiom_footprints.csv`](research/data/13_dat_axiom_footprints.csv): 5678 printed declarations,
5484 of them foundational-only):

| named axiom | declarations carrying it | status |
|---|---|---|
| `wilson_reflection_positive_at` | 183 | stated at every extent and $\beta\ge0$; **proved** at even lattice extent $\ge4$ (`OddLagSplit.corrClay_reflection_positive`); cited at odd extent and extent two to the positive transfer matrix (Osterwalder–Seiler 1978; Lüscher 1977) |
| `os_reconstruction_wightman` | 11 | cited (Osterwalder–Schrader reconstruction), from `OSData` to `WightmanQFTData` |

The periodic-state chain above — the state, the transfer, the one-lag reduction and the Clay lattice gap —
carries the three foundational axioms only. The paper ([`research/PAPER.pdf`](research/PAPER.pdf); also [HTML](research/PAPER.html) and [Markdown source](research/PAPER.md)) develops
the reading and the method; the reads run through the Entroptics reader (`research/code/`); the Lean 4 /
Mathlib development (`research/lean/`) is the verification — `sorry`-free.

## Layout

| path | what |
|---|---|
| [`research/PAPER.pdf`](research/PAPER.pdf), [`PAPER.html`](research/PAPER.html) | the paper, built from [`PAPER.md`](research/PAPER.md) |
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

#print axioms MassGap.EvenAperture.existence_and_gap_of_substrate_even
-- propext, Classical.choice, Quot.sound  -- and NOTHING else.
-- The gap side with no named axiom at all: reflection positivity is PROVED here, at even lattice
-- extent >= 4 and beta >= 0, rather than cited. This is the strongest statement in the development.

#print axioms MassGap.ym_mass_gap_of_substrate
-- the three foundational + wilson_reflection_positive_at  (the same conclusion at every aperture, odd
-- extents included, where reflection positivity is still cited; below beta = 0 the read is the beta = 0 read)

#print axioms MassGap.ym_mass_gap_certified
-- the three foundational + wilson_reflection_positive_at  (conditioned on the confinement read)

#print axioms MassGap.WilsonGauge.ym_existence_and_gap_gauge_wilson
-- the three foundational + wilson_reflection_positive_at  (existence and the gap, for the constructed
-- SU(N) Wilson realisation ym_wilson_gauge)

#print axioms MassGap.WightmanData.reconstructed_vacuum_energy_zero
-- the three foundational + os_reconstruction_wightman  (a fact read back OUT of the reconstruction's
-- conclusion: the reconstructed Hamiltonian annihilates the vacuum)

#print axioms MassGap.ym_mass_gap_spectral
-- the three foundational + wilson_reflection_positive_at  (the gap over an ARBITRARY mode family,
-- gated on the finite-aperture margin as an EXPLICIT hypothesis: the physics is that hypothesis,
-- not the footprint)

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
ensembles (U(1), SU(2), SU(3))* — DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110) (v0.2.0), with
its own citation. The record and its files are open access. They are not in this
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
