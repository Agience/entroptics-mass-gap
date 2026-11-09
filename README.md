# The Mass Gap of SU(N) Gauge Theory Seen by an Observer of Fixed Physical Resolution

## Release v0.3.0 (2026-11-08)

The paper: *The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution*, by Ikailo John Sessford (Ikailo Inc.). PDF: [`research/paper/mass-gap.pdf`](research/paper/mass-gap.pdf); sources: [`research/paper/v3/`](research/paper/v3), assembled by `research/paper/build_paper.py`.

It takes the frame of the [Entroptics paper](https://github.com/Agience/entroptics) (in the Entroptics v0.2.10 release, DOI [10.5281/zenodo.24063501](https://doi.org/10.5281/zenodo.24063501)), an observer as a finite aperture whose mode count is read from the signal's spectrum, as the method for the continuum limit of four-dimensional $SU(N)$ Wilson lattice gauge theory. On the gap side the theory is read at a window it sets: the doubling defect $D_\beta(w)=16\log Z_\beta(2^w)-\log Z_\beta(2^{w+1})$ of the periodic torus is held at a fixed value along a coupling tower while the window doubles. On the existence side the observer's screen in a box of fixed physical side is a finite family of modes, and every even moment of a reading follows from one variance bound through the Rényi count of order ½; for the Wilson field the count bound is reduced to one fine-scale inequality, which is open. For $N\ge2$ the paper proves that the formalized target $\mathrm{CS}(N)$, an Osterwalder–Schrader form of the $SU(N)$ existence-and-gap statement, follows from three open statements: (S) the defect tends to $0$ along the windows at arbitrarily large $\beta$; (M) at window couplings arbitrarily close to $0$, along every coupling tower, the measured tensor mass stays in a band of ratio $2$ at a level chosen per tower; and (E) the existence clauses restated along towers. Without hypotheses it proves the doubling bootstrap (one window with $D\le1/1000$ forces $D(w+1)\le250\,D(w)^2$ and a transfer gap uniform in the torus size), vanishing on an interval of small $\beta$, at the decoupled end of the anisotropic family and on an explicit strip of mixed couplings, box gaps for $SU(2)$ and $SU(3)$ at small coupling with the one-cube reduction of *Lattice Mass Gaps and Continuum Criteria for Four-Dimensional Yang–Mills Theory* (release v4.42.0, <https://doi.org/10.5281/zenodo.24055064>), and properties that do not separate $SU(N)$ from $U(1)$. The mass gap is not proved: (S), (M) and (E) are open. Monte Carlo data are validation only.

Build the Lean and check the axioms (toolchain `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0`; install [`elan`](https://github.com/leanprover/elan) first):

```bash
cd research/lean
lake exe cache get      # the compiled Mathlib v4.31.0
lake build              # every module of MassGap; prints the #print axioms lines
```

In a file under `research/lean` that imports `MassGap`, run with `lake env lean <file>`:

```lean
import MassGap
#print axioms MassGap.OneInput.clayStatement_of_strongEnd   -- the reduction to (S), (M), (E)
```

Every recorded declaration depends on a subset of `propext`, `Classical.choice` and `Quot.sound`; `python research/code/certify/lean_axiom_footprints.py` regenerates the full table (`research/data/13_dat_axiom_footprints.csv`). The map from the paper's statements to Lean declarations is [`research/FORMALIZATION.md`](research/FORMALIZATION.md).

Licences: code Apache-2.0 ([`LICENSE`](LICENSE), [`NOTICE`](NOTICE)); paper text under `research/paper/` CC BY 4.0; the lattice ensembles (a separate record, DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110)) CC BY 4.0.

How to cite: Sessford, Ikailo John, *The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution*, v0.3.0, 2026, Zenodo, version DOI [10.5281/zenodo.24065397](https://doi.org/10.5281/zenodo.24065397) (all versions: [10.5281/zenodo.22652660](https://doi.org/10.5281/zenodo.22652660)). [`CITATION.cff`](CITATION.cff) carries the same entry.

---

## Author's note

Entroptics was the original find: a formalization of an information structure I had long planned, using
entropy to characterize a *local resolution* for information artifacts.

I measured what I could with it — fast radio bursts, radio signals, market data — as calibration and
refinement. FRBs and QCD sit at opposite ends of the scale, the cosmological and the fundamental. Feeding it
QCD data is when I realized Entroptics could read the substrate the universe is built from. This paper is
what came of that.

Review, feedback and fixes are welcome.

## Layout

| path | what |
|---|---|
| [`research/paper/`](research/paper) | the paper: `mass-gap.pdf`, `mass-gap.html` and `mass-gap.md`, assembled by `build_paper.py` from `v3/` (one file per section, with `*.lean-map.md` theorem-to-declaration tables); figures in `figures/` |
| [`research/FORMALIZATION.md`](research/FORMALIZATION.md) | the map from the paper's statements to Lean declarations |
| [`research/lean/`](research/lean) | the Lean 4 / Mathlib development: root `MassGap.lean`, modules under `MassGap/`, free of `sorry`, on the axioms `propext`, `Classical.choice` and `Quot.sound` only |
| [`research/code/`](research/code) | the ensemble generator, the exact checks, the Monte Carlo reads of section 10 (`observer/`), the Lean build driver, certification scripts and tests; see its `README.md` |
| [`research/data/`](research/data) | the committed tables and figures, the section 10 aggregates (`observer/`) and `regen_all.py`, the entry point that regenerates them; see its `README.md` |
| `research/requirements.txt`, `research/requirements-release.txt` | Python dependencies, and the exact pin set of the release |
| `research.local.env.example` | the environment variables the scripts read |

## Reproduce

The Lean development: see the commands above, or `python research/code/lean_build.py`. The exact checks run in seconds with no data: `python research/code/<name>_checks.py`. The test suite: `pip install -r research/requirements-release.txt` (Python 3.12; the exact pins of this release; `research/requirements.txt` gives the ranges), then `python -m pytest -q research/code/tests`. The paper: `python research/paper/build_paper.py` rebuilds `mass-gap.md`, `mass-gap.html` and `mass-gap.pdf` from `research/paper/v3/`; it needs a network connection for KaTeX and a Chromium-family browser (Edge, Chrome or Chromium) for the PDF, and `--no-pdf` skips the browser. Every committed table and figure regenerates through `python research/data/regen_all.py` (`--list` shows each artifact, its owner script and its resource class).

## Data

The lattice ensembles are a separate record, *Entroptics lattice gauge-theory action-density ensembles (U(1), SU(2), SU(3))*, DOI [10.5281/zenodo.22850110](https://doi.org/10.5281/zenodo.22850110) (v0.2.0, CC BY 4.0, open access), with its own citation: action-density fields for compact U(1), SU(2) and SU(3), 81 ensembles across 265 shards, 22,972 configurations, 22.27 GiB. They are not in this repository and no script downloads them. Scripts that read ensembles locate them through `CONFIGS`, set per run or in `research.local.env` (copy `research.local.env.example`; the file is git-ignored); a script run without it refuses and says what it needs. The ensembles behind the section 10 reads are not in that record (section 12 of the paper); their committed aggregates in `research/data/observer/` are the published output.

## Cite

Cite the paper and the software record by its DOI, as above and in [`CITATION.cff`](CITATION.cff), and the dataset record by its own DOI.

Security issues: email connect@agience.ai rather than opening a public issue.

## Declaration of generative AI use

Generative AI tools were used in drafting the text and in the formalization; the author reviewed all output and is responsible for the content.
