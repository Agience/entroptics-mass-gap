# Figures

All figures are written by one script, from closed forms only (no data files, no network):

```
python research/paper/figures/make_figures.py
```

It writes `fig_*.pdf` (for the paper) and `fig_*.png` (for review) into this directory. Before plotting it checks the reference values of the closed forms below (`check_reference_values`) and the orderings proved in Lean (`tPoly_le_tGlue`, `tGlue_le_tLift`, `tLift_le`, `tGlue_le_tQuart`, `diag_small`) at 2000 points; a failed check stops the run. Matplotlib only; STIX fonts; colours from a colour-blind-safe categorical palette, with line style as a second channel on every curve.

Couplings are in the convention of the formal statements: $\beta = \beta_W/2$, $t = t_W/2$ (section 1.7).

## Closed forms and their Lean sources

Natural logarithms; $\lceil\cdot\rceil$ the ceiling. All in `research/lean/MassGap/`.

| symbol | formula | Lean definition |
|---|---|---|
| $\ell$ | $240 + 150(N+4)\beta$ | `StripGap.gapArea` |
| $K$ | $\lceil 2\sqrt{2N(\beta+1)}\rceil + 1$ | `StripGap.binCount` |
| $L$ | $1 + 2N^2\log K$ | `StripWidth.bulkExp` |
| $A_{\rm glue}$ | $2 + 2\ell(2L + 2\log\ell + 26)$ | `StripWiden.glueArea`, `StripGapThm.areaG` |
| $n_0$ | $2 + 2\ell(2L + 41 + 6\log\ell)$ | `StripWidth.seedSide` |
| $w_0$ | $\lceil\log_4 A_{\rm glue}\rceil$ | `StripGapThm.seedWindow` |
| $t_{\rm low}$ | $e^{-4\beta}/(16192(16\beta+27))$, strict ($t < t_{\rm low}$) | `StripWidth.tLow`, `StripWidth.strip_width` |
| $t_{\rm poly}$ | $1/(16192\,n_0^2)$ | `StripWidth.tPoly`, `strip_width_poly` |
| $t_{\rm glue}$ | $1/(16192\,A_{\rm glue})$ | `StripWiden.tGlue`, `strip_width_glue`; gap `StripGapThm.strip_gap` |
| $t_{\rm lift}$ | $1/(4048\cdot 4^{w_0})$ | `StripLift.tLift`; gap `StripLift.lift_gap` |
| $t_{\rm quart}$ | $1/(524288\cdot 2^{w_0})$ | `CumulantStrip.tQuart`, `strip_width_quartic`; gap `gap_quartic` |
| $t_0$ | $2^{-17} = 1/131072$ | hypothesis of `CumulantStrip.DA_le_quartic` |
| $t_1$, $t_2$ | $e^{-88}/16$, $e^{-128}/16$ | `StripGas.tOne`, `StripOsc.tTwo` |
| diagonal | $t = \beta \le 1/500000$ | `StripWidth.diag_small` |
| gap rate | $m = \log 2/2^{w_0}$ | `StripGapThm.stripMass`, `StripLift.seedMass` |
| bootstrap | $D \le 1/1000 \Rightarrow D' \le 250\,D^2$ | `DoublingSharp.rec_sharp`; section 5, Theorem 5.5 |

Every formula of the figure specification agrees with its Lean definition; none was changed.

## Figure 1.1: the proof route — `fig_proof_route`

Source: sections 1.3, 4.3–4.4 (Theorem 1.1, its inputs and what is proved along a tower), with the supporting results of sections 3, 5, 7, 8 and 9. Lean: `OneInput.clayStatement_of_strongEnd`. Embedded in section 1.3.

Caption. The structure of Theorem 1.1. The formalized target CS($N$) of section 4.1 follows from three open inputs: the bridge (S), the measured-mass band (M) (along each tower the window reading of the tensor mass stays in a band of ratio $2$ at a level chosen per tower) and the existence clauses (E), the last two along every coupling tower at frequently small window coupling. The proof uses the facts proved along a tower (section 4.4, blue): towers exist at every small window coupling given (S), the periodic transfer has a gap at rate $\log 2/2^k$ from the basin, the window reading of the mass is bounded below, and an abelian generator exists at $SU(N)$. A band at a fixed level, the same for every tower, is refuted under (S) (section 4.4, Theorem 4.8). The supporting results (light blue) are proved as stated: the doubling bootstrap (section 5) reduces (S) to a single window with defect at most $1/1000$; the decoupled end and the anisotropic strip (section 7) prove vanishing off the isotropic line and stop short of $t=\beta$; the separators (section 9) are negative results that any proof of (S) must pass; the aperture count (section 3) moves the moment clause of (E) onto two single-observer bounds and discharges none of (E); the box route (section 8) concludes a weaker continuum statement $\mathcal C(L)$ from four open inputs, (UV), (B1), (B2), (B3), and its proved lattice mass at the box couplings is at most $1/508$, at one infinite-volume state. Dashed arrows are relations, not implications.

## Figure 5.1: the doubling bootstrap — `fig_bootstrap`

Source: Theorem 5.6, $D_\beta(w+1) \le 250\,D_\beta(w)^2 \le D_\beta(w)/4$ for $D_\beta(w) \le 1/1000$; the orbit is the iterated bound from $D_\beta(w_0) = 1/1000$. Embedded in section 5.3.

Caption. The doubling bootstrap on logarithmic axes. In the basin $D_\beta(w)\le1/1000$ (shaded) the defect at the next window is at most $250\,D_\beta(w)^2$ (solid), which is at most a quarter of $D_\beta(w)$ (dashed). The cobweb follows the bound from the edge of the basin: $10^{-3}$, $2.5\times10^{-4}$, $1.6\times10^{-5}$, $6.1\times10^{-8}$, $9.3\times10^{-13}$, a doubly exponential decay. Outside the basin no bound is proved (dotted); the fixed point $1/250$ of the map lies there. One window in the basin therefore gives vanishing of the defect, and with it the size-uniform transfer gap at rate $\log2/2^{w_0}$.

## Figure 7.1: the coupling plane — `fig_coupling_plane`

Source: the closed forms above, $N = 2$ and $N = 3$, $\beta$ at 2000 points log-uniform on $[10^{-7}, 10^4]$; step curves drawn as steps; $t_{\rm low}$ stops where it leaves the axis range near $\beta \approx 11$. Embedded in section 7.4.

Caption. The coupling plane of the anisotropic Wilson torus, in-plane coupling $\beta$ and mixed coupling $t$ (both in the convention $\beta = \beta_W/2$), for $SU(2)$ (left) and $SU(3)$ (right). Filled: the proved region of vanishing of the doubling defect, below the upper envelope of the widths $t_{\rm low}$, $t_{\rm poly}$, $t_{\rm glue}$, $t_{\rm lift}$, $t_{\rm quart}$ (closed forms in sections 7.2–7.4; the boundary is open on $t_{\rm low}$ and closed on the others). Hatched: where, in addition, the transfer gap holds at rate $\log 2/2^{w_0}$ uniform in the torus side $2^w$, $w \ge w_0$, in the $L^2$ transfer form. The decoupled axis $t = 0$, not representable on logarithmic axes, is in the vanishing set at every $\beta \ge 0$ (section 7.1, Theorem 7.5). The black line is the isotropic theory $t = \beta$, where (S) lives at large $\beta$; its thick segment $\beta \le 1/500000$ is proved. Every proved width divided by $\beta$ tends to $0$; the region between the proved widths and the diagonal is open. The light region is not gapless: every point of the vanishing set, the filled region included, carries a transfer gap uniform in the torus side at some rate $\log 2/2^w$ (Theorem 7.19); the hatching marks only where the rate $\log 2/2^{w_0}$ is explicit. The width $t_{\rm coh}$ of Theorem 7.13 is not drawn, because it contains the Haar integral $b_N(\beta)$, which has no closed form. The margin $\varepsilon(\beta)$ of Theorem 7.19 and the open neighbourhoods of Theorem 7.10 (ii) exist but are not quantified, so they are not drawn. The horizontal dashed line is the range $2^{-17}$ of the quartic cumulant bound, which is not a vanishing region by itself; the ranges $t_1 = e^{-88}/16$ of the site gas and $t_2 = e^{-128}/16$ of the local terms lie below the axis.

## Figure 7.2: the strip widths — `fig_strip_widths`

Source: the closed forms $t_{\rm low}$, $t_{\rm poly}$, $t_{\rm glue}$, $t_{\rm quart}$ above, $N = 2$ and $N = 3$, $\beta \in [10^{-3}, 10^4]$, log-log, with $t = \beta$ for reference. Embedded in section 7.4.

Caption. The proved widths of the anisotropic strip against the in-plane coupling $\beta$ ($\beta = \beta_W/2$), for $SU(2)$ (left) and $SU(3)$ (right). $t_{\rm low}$ decays like $e^{-4\beta}$ and dominates at small $\beta$; $t_{\rm glue}$ and $t_{\rm quart}$ decay polynomially, $t_{\rm poly}$ faster, and $t_{\rm quart}$ is a step function through the integer seed window $w_0$. The proved orderings $t_{\rm poly} \le t_{\rm glue} \le t_{\rm quart}$ hold at every $\beta \ge 0$. Every width divided by $\beta$ tends to $0$, so none reaches the isotropic line $t = \beta$ (grey).

## Observer figures

The six figures `research/data/obs_fig_*.png` are written by `research/code/observer/plot_observer.py` from the committed JSON in `research/data/observer/`, not by this script. The paper does not embed them; the correlator, cube-moment, step and influence-row figures draw reads summarized in section 10.

## Planned figures

- The decoupled torus, its planes, the mixed plaquettes and the site gas (section 7).
- A Lean cluster map: module groups and capstones (section 11).
- The separators (what is proved, why it does not separate) are a table in section 9, not a figure.
