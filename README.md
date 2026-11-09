# The Mass Gap of SU(N) Gauge Theory Seen by an Observer of Fixed Physical Resolution

Release v0.3.1 (2026-11-08) · Ikailo John Sessford (Ikailo Inc.)

Paper: [PDF](research/paper/mass-gap.pdf) (two-column) · [LaTeX source](research/paper/mass-gap.tex) · [HTML](research/paper/mass-gap.html)

The paper applies the frame of [Entroptics](https://github.com/Agience/entroptics) to the continuum limit of four-dimensional $SU(N)$ Wilson lattice gauge theory. In that frame, an observer is a finite aperture whose mode count is read from the signal's spectrum. For $N\ge2$ it proves, in Lean, that an Osterwalder–Schrader form of the $SU(N)$ existence-and-gap statement follows from three open statements:

- (S): the doubling defect $D_\beta(w)=16\log Z_\beta(2^w)-\log Z_\beta(2^{w+1})$ tends to $0$ at arbitrarily large $\beta$;
- (M): the measured tensor mass stays in a band of ratio $2$ along every coupling tower;
- (E): the existence clauses, restated along towers.

Proved without these hypotheses:

- the doubling bootstrap, with a transfer gap uniform in the torus size;
- vanishing of the defect at small $\beta$;
- box gaps for $SU(2)$ and $SU(3)$ at small coupling.

The mass gap itself is not proved, because (S), (M) and (E) are open. Monte Carlo data are used as validation only.

## Author's note

Entroptics was the original find: a formalization of an information structure I had long planned, using
entropy to characterize a *local resolution* for information artifacts.

I measured what I could with it — fast radio bursts, radio signals, market data — as calibration and
refinement. FRBs and QCD sit at opposite ends of the scale, the cosmological and the fundamental. Feeding it
QCD data is when I realized Entroptics could read the substrate the universe is built from. This paper is
what came of that.

## Lean

Toolchain `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0`; install [`elan`](https://github.com/leanprover/elan) first.

```bash
cd research/lean
lake exe cache get
lake build              # every module; prints the #print axioms lines
```

```lean
import MassGap
#print axioms MassGap.OneInput.clayStatement_of_strongEnd   -- the reduction to (S), (M), (E)
```

The development is free of `sorry` and uses only `propext`, `Classical.choice` and `Quot.sound`. [`research/FORMALIZATION.md`](research/FORMALIZATION.md) maps the paper's statements to Lean declarations.

## Layout

| path | what |
|---|---|
| [`research/paper/`](research/paper) | the paper, built by `build_paper.py` from `v3/` (one file per section); `typeset/` sets the two-column PDF |
| [`research/lean/`](research/lean) | the Lean 4 / Mathlib development |
| [`research/code/`](research/code) | generator, exact checks, Monte Carlo reads, certification scripts and tests |
| [`research/data/`](research/data) | committed tables, figures and aggregates; `regen_all.py` regenerates them |

## Reproduce

```bash
pip install -r research/requirements-release.txt   # Python 3.12
python -m pytest -q research/code/tests
python research/paper/build_paper.py               # .md, .html, .tex, .pdf; the PDF needs pandoc 3 + tectonic, --no-pdf skips it
python research/data/regen_all.py --list
```

## Data

The lattice ensembles are a separate record, DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110) (CC BY 4.0): 81 ensembles across 265 shards, 22,972 configurations, 22.27 GiB. They are not part of this repository. Scripts locate them through `CONFIGS`, which you set in `research.local.env`; copy `research.local.env.example` to create it.

## Cite and licence

Sessford, Ikailo John, *The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution*, v0.3.1, 2026, Zenodo, DOI [10.5281/zenodo.22652660](https://doi.org/10.5281/zenodo.22652660). See [`CITATION.cff`](CITATION.cff).

Code is licensed Apache-2.0 ([`LICENSE`](LICENSE)); the paper text is CC BY 4.0.

Review, feedback and fixes are welcome. Report security issues to connect@agience.ai.

Generative AI tools were used in drafting and formalization; the author reviewed all output and is responsible for the content.
