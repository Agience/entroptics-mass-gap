import MassGap.ReachFreeze
import MassGap.Floor

/-!
# MassGap.Margin — the aperture margin from ONE cited junction (no bare postulate)

The read margin `‖m_hi‖ ≤ e^{−(κ₀−μ)}` (the content of `ym_aperture_margin`) is not a bare postulate. It
decomposes into three inputs, ONE of them already proved:

* **`κ₀ ≤ κ`** — the counting floor, PROVED (`Floor`: the directed-cube-path count `3^{n−1}` gives
  `κ ≥ κ₀ = ¼log3`).
* **`c ≤ Δ`** — the contraction rate lower-bounds the transfer gap. A HYPOTHESIS here.
  `ReachFreeze.gap_from_contraction` proves only that an *abstract* `σ` with an *assumed* contraction decays
  as `e^{−c·n}` — it neither defines `Δ` nor discharges `c ≤ Δ`, and it is not composed here (no call site).
* **`κ − μ ≤ c`** — the self-sourcing contraction rate is at least the vortex free-energy density. One of the
  TWO OPEN inputs (with `c ≤ Δ`): the centre-vortex confinement mechanism, whose qualitative form (vortex
  condensation `F_v = μ−κ < 0 ⇒` area law `⇒` gap) is cited to 't Hooft (Nucl. Phys. B 138, 1978) and
  Greensite (Prog. Part. Nucl. Phys. 51, 2003), and whose quantitative form is the framework's read.

`margin_of_contraction` assembles them: the dominant mode `e^{−Δ}` clears the entropy-floor margin. So the
gap rests on the two open inputs `κ−μ ≤ c` and `c ≤ Δ`, the counting floor being closed and the assembly proved. This is
the forward bridge from the PROVED counting floor to the SPECTRAL gap — the decomposition of
`ym_aperture_margin` the referee report flagged as a bare axiom.

Imported by `MassGap.lean` (part of the aggregate). It derives the read margin
`e^{−Δ} ≤ e^{−(κ₀−μ)}` from the floor junction; the STRONGER spectral ceiling `e^{−Δ} ≤ 3^{−1/4} = e^{−κ₀}`
used by `ym_aperture_margin` (which needs `Δ ≥ κ₀`) is carried by the concrete witness there, not here.
-/

namespace MassGap

/-- **The band-limit step (a consequence, not an input).** A dominant mode of magnitude `e^{−Δ}` whose gap
clears the contraction, `c ≤ Δ` (`ReachFreeze.gap_from_contraction`), decays at least at the contraction rate:
`e^{−Δ} ≤ e^{−c}`. So the band-limit `‖m‖ ≤ e^{−c}` is not an independent assumption. -/
theorem band_of_contraction {Δ c : ℝ} (hgap : c ≤ Δ) : Real.exp (-Δ) ≤ Real.exp (-c) :=
  Real.exp_le_exp.mpr (by linarith)

/-- **The aperture-margin bridge — the read margin from the two open inputs.** From
* `hfloor : κ₀ ≤ κ` (the counting floor, PROVED in `Floor`),
* `hfe : κ − μ ≤ c` (the vortex free-energy / self-sourcing-contraction identification — the centre-vortex
  mechanism, 't Hooft 1978 / Greensite 2003, cited; OPEN), and
* `hgap : c ≤ Δ` (the contraction rate lower-bounds the gap — a HYPOTHESIS; `gap_from_contraction` shows only
  abstract-`σ` decay at rate `c`, it does not supply this; OPEN),

the dominant transfer mode `e^{−Δ}` clears the entropy-floor margin: `e^{−Δ} ≤ e^{−(κ₀−μ)}`. This is the
content of `ym_aperture_margin`, assembled from the two open inputs `hfe` and `hgap` (only the counting floor
is proved; the assembly is one `Real.exp_le_exp` step). -/
theorem margin_of_contraction {κ₀ κ μ c Δ : ℝ}
    (hfloor : κ₀ ≤ κ) (hfe : κ - μ ≤ c) (hgap : c ≤ Δ) :
    Real.exp (-Δ) ≤ Real.exp (-(κ₀ - μ)) :=
  Real.exp_le_exp.mpr (by linarith)

/-! **Scope note.** `margin_of_contraction` derives the READ margin `e^{−Δ} ≤ e^{−(κ₀−μ)}` — exactly the
`hread` field consumed by `gap_of_confinement`, sufficient for the mass gap (`ym_mass_gap`). The
STRONGER spectral-form ceiling `e^{−Δ} ≤ 3^{−1/4} = e^{−κ₀}` (`ym_aperture_margin`) needs `Δ ≥ κ₀`, i.e. the
contraction to clear the FULL multiplicity `c ≥ κ` (not the free-energy density `c ≥ κ−μ`); the bridge does
not supply it, and `ym_mass_gap` does not need it. -/

end MassGap
