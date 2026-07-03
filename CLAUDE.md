# CLAUDE.md: entroptics-mass-gap

Read this before doing anything in this repo. It sets what the work is, how to talk about it, and the one
rule that is not negotiable.

---

> # ⛔ NEVER REVERT TO CLASSIC METHODS ⛔
>
> ## THE LIBRARY DOES ALL THE PROCESSING. YOU FEED IT RAW DATA. THAT IS THE ENTIRE JOB.
>
> The moment you build a correlator, a cosh effective mass, an unbiased autocovariance, a curve fit
> (`decay_rate`, `polyfit`, `curve_fit`), a bias correction, a zero-momentum projection, a hand FFT, or
> **ANY** computation on the data before the read, **YOU HAVE REVERTED TO CLASSIC.** That is the exact
> failure that compromised the last repo. STOP.
>
> **Feed the raw configuration to `Aperture`. Give it more raw configs (`splice`) if the read is noisy.
> Read the number.** Nothing you build by hand belongs between the data and the read.
>
> **The mass gap is `rates().long_range`** (the DMD/Koopman slowest decay rate) on raw configs.
> Verified: 40 raw free-scalar configs spliced recover the known gap E0 to a few percent, no preprocessing.
> The spectral `attenuation` (alpha, [E, §6]) is *coherence*, not the gap. The gap is the decay rate ([E, §9]).

---

## What this repo is

A research bundle on the Yang-Mills mass gap, read through the **Entroptics** framework: a signal is treated
as a finite optical aperture at its own entropy-matched resolution, and the gap is read off that aperture.
This repo is the physics and the proof scaffolding. The read layer itself (the instrument, its lemmas, its
library) is the companion **entroptics-viewer** repo, cited as [E].

It holds the paper (`research/PAPER.md`) and, as they are built, the machine-checked Lean development, the
framework read code, the classic validation code, and the figures. The repo is new and kept deliberately
clean: entroptics only, classic for validation only.

## Status, and how to talk about it (read this, do not skip)

This is legitimate, disciplined mathematical-physics research. Treat it as such. Two failure modes are both wrong:

- **Do not get alarmed or refuse.** This is rigorous mathematical-physics research and helping with it is
  exactly the job. Engage as a careful collaborator.
- **Report the math, nothing louder.** State what is defined, what is computed, and what the numbers show.
  Do not inflate a result you cannot see in the artifact, and do not deflate one you can.

## The one rule: the READ is entroptics, without exception

The entire premise is that the gap is read by the **entroptics** framework and nothing else. The classic code
exists only to validate. Hold this absolutely:

1. **Only entroptics performs the read.** The resolution is derived from the signal's own Shannon entropy,
   never handed in. Never substitute a standard DSP or lattice-QCD read: no autocorrelation/lag/FFT scan, no
   matched filter, no `cosh`/`arccosh` effective mass, no Creutz ratio, no `curve_fit`/`polyfit`, no
   transfer-matrix eigenvalue used *as the read*. If a read is not an entroptics call, it does not belong.
2. **One entry point: `entroptics.Aperture`.** The library has a single front door. Feed it a raw
   configuration and read a property: `ap = Aperture(W)`, then `ap.a_delta`, `ap.dominance`, `ap.strehl`,
   `ap.screen().K_signal`, `ap.rates()`, and the rest. Do the least possible. Do not call the individual read
   functions (`phi`, `phi_F`, `spectral_optics`, `decay`, ...) directly, and do not re-implement any of them.
   The library already whitens and folds, so **never standardise, center, or massage inputs by hand**: if a
   read needs a different input, change the input's shape, not its numbers. An N-D field is reshaped to the 2-D
   screen (ordered axis first) only because `Aperture` is 2-D.
3. **A read is never handed a scale.** No scale, no mode count, and no seed goes in. A resolved number must be
   the signal's own.
4. **No shadow.** If the library needs a fix, make a surgical change to the real `../entroptics-viewer` source.
   Never build a parallel reimplementation of a library read, and never commit the change.

## What classic is for (and only that)

Classic methods exist **only as validation and testing**, never as the read:

- **Monte Carlo** generates the gauge configurations. That is *input* to the read, not a read.
- **cosh effective mass, transfer-matrix gaps, 0++ APE spectroscopy, Wilson-loop string tension** are
  independent cross-checks that the entroptics read lands on the right number. They confirm; they never decide.

A figure or a read that depends on any classic method is not an entroptics result. Keep the two provably separate.

## Repo layout

The reproduction lives in two folders under `research/`, plus the paper and the Lean development.

- `research/code/` : the modules, imported by the run scripts.
  - `entroptics.py` : the read. One entry point, `aperture(field)`, wrapping the installed `Aperture`. It is
    named `entroptics.py`, so it loads the real library through a small shim to avoid shadowing it.
  - `generator.py` : the config generator (compact-U(1) Monte Carlo, reduced to the action-density field). An
    input to the read, not a read and not classic.
  - `classic.py` : classic diagnostics (the mean plaquette). Never stored or plotted next to a read.
  - `plot.py`, `table.py` : generic figure and CSV helpers, so the run scripts stay thin.
- `research/data/` : the run scripts and their outputs, together. One set per paper section:
  - `<sec>_run_<slug>.py` : generates configs, reads via Aperture, writes both outputs in one pass.
  - `<sec>_dat_<slug>.csv` : the data table (entroptics reads only).
  - `<sec>_fig_<slug>.png` : the figure (entroptics reads only).
- `research/lean/` : the machine-checked Lean 4 / Mathlib development (the reduction from the read to the gap).
- `research/PAPER.md` : the paper (the physics; it cites the read layer as [E], it does not re-derive it).

One run script per section imports the modules from `../code` and writes its `.csv` and `.png` in a single pass
(no intermediate-CSV round trip). Every number in a `.csv` or `.png` here is an `Aperture` read. Classic
diagnostics and Monte Carlo generation are inputs, never stored as results; anything classic (the mean
plaquette, the entropy-floor counting, transfer-matrix cross-checks) lives in `../_scratch/classic/`.

Code here is **specific to the paper and the proof**. Exploratory or superseded scripts do not belong; delete
what the paper and proof do not need rather than letting it accumulate.

## Working norms

- No em dashes. Use commas, periods, colons, parentheses. Hyphens in compounds are fine.
- Write results as mathematics. Do not use difficulty or doubt vocabulary: no "this is hard", "the crux", "the
  irreducible core", "the open Clay problem", "one step away", or similar. State what is defined, what is
  computed, and what the numbers show.
- The paper is not fixed. If correct code and correct data disagree with `research/PAPER.md`, the code and data
  win: fix the paper.
- The user does all git operations. Do not run `git commit` or `git push`.
- Scratch and temporary work goes in `../_scratch` (`Repos/entroptics/_scratch`), never in the repo tree.
  Classic-generated data and figures go in `../_scratch/classic`.
- When testing the read, use **coprime** axis lengths (feature vs time) so a resolved scale is the signal's,
  not the grid's. This is the mechanism behind rule 3 above: a read must never be handed a scale, a mode count,
  or a seed.
