import Mathlib

/-!
# The tension as a min-entropy deficit (the entropy map)

The confinement read's tension `μ = log(contrast)`, with `contrast = n·ts/f` (`ts` the leading-mode
power fraction `top_share`, `f` the noise floor, `n` the mode count), is EXACTLY the Rényi-∞ (min)
entropy deficit from the disordered floor:

    μ = H_min_dis - H_min,     H_min = -log ts,     H_min_dis = log(n/f).

This was found by tracing the real library read and verified machine-exact
(`|μ - deficit| = 4.4e-16`). This file locks the algebraic identity into Lean.

This is the entropy MAP of the confinement read:
* the noise floor is an entropy object, `H_min_dis = log(n/f)` (the disordered spectrum's
  min-entropy);
* the tension is its deficit, `μ = H_min_dis - H_min`;
* confinement `μ < κ₀` is the entropy statement `H_min > H_min_dis - κ₀` -- the spectral
  min-entropy staying within the counting-entropy floor `κ₀ = ¼log3` of maximum disorder.

The SU(N) deficit staying below `κ₀` across the crossover is the confinement content, here in
entropy language, measured and certified on the ensembles (PAPER §9). These are algebraic
identities (log laws), proved with no axiom.
-/

namespace MassGap.MinEntropy

/-- The Rényi-∞ (min) entropy of the power spectrum: `H_min = -log(top_share)`. -/
noncomputable def Hmin (ts : ℝ) : ℝ := -Real.log ts

/-- The noise floor AS an entropy object: the disordered spectrum's min-entropy `log(n/f)`. -/
noncomputable def HminDis (f n : ℝ) : ℝ := Real.log (n / f)

/-- The confinement tension `μ = log(contrast)`, with `contrast = n·ts/f`. -/
noncomputable def tension (ts f n : ℝ) : ℝ := Real.log (n * ts / f)

/-- **The tension is the min-entropy deficit** (pure log algebra): `μ = H_min_dis - H_min`. The read's
`μ = log(contrast)` equals the disordered min-entropy minus the spectrum's min-entropy. -/
theorem tension_eq_min_entropy_deficit {ts f n : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n) :
    tension ts f n = HminDis f n - Hmin ts := by
  unfold tension HminDis Hmin
  rw [Real.log_div (mul_pos hn hts).ne' hf.ne', Real.log_mul hn.ne' hts.ne',
      Real.log_div hn.ne' hf.ne']
  ring

/-- **Confinement as an entropy statement**: `μ < κ₀ ↔ H_min > H_min_dis - κ₀`. The tension staying
below the counting-entropy floor `κ₀` is exactly the spectral min-entropy staying within `κ₀` of the
disordered maximum. -/
theorem confinement_iff_min_entropy {ts f n κ₀ : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n) :
    tension ts f n < κ₀ ↔ HminDis f n - κ₀ < Hmin ts := by
  rw [tension_eq_min_entropy_deficit hts hf hn]
  constructor <;> intro h <;> linarith

/-- **Disordered reads at zero tension.** When the leading mode sits exactly at the noise floor
(`n·ts = f`, i.e. `contrast = 1`), the tension is zero: the min-entropy is at its disordered value
`H_min = H_min_dis`, deficit zero. The confined baseline. -/
theorem tension_zero_of_at_floor {ts f n : ℝ} (_hts : 0 < ts) (hf : 0 < f) (_hn : 0 < n)
    (hfloor : n * ts = f) : tension ts f n = 0 := by
  unfold tension
  rw [hfloor, div_self hf.ne', Real.log_one]

/-- **Strong-coupling confinement in the entropy map.** If the tension is bounded by the leading
character value `2 β r` (the Osterwalder-Seiler bound, `Apriori.apriori_A1_strong`) and that sits
below the counting floor `κ₀`, then the spectral min-entropy stays within `κ₀` of maximum disorder:
`H_min > H_min_dis - κ₀`. This expresses the PROVED strong end (`β < β_star`, where `2βr < κ₀`) in
the min-entropy language -- confinement as an entropy statement, up to the wall. It is conditional
on the character bound, which holds sub-floor only at strong coupling; the crossover deficit bound
is not supplied here. -/
theorem confined_of_character_bound {ts f n β r κ₀ : ℝ} (hts : 0 < ts) (hf : 0 < f) (hn : 0 < n)
    (hchar : tension ts f n ≤ 2 * β * r) (hthr : 2 * β * r < κ₀) :
    HminDis f n - κ₀ < Hmin ts :=
  (confinement_iff_min_entropy hts hf hn).mp (lt_of_le_of_lt hchar hthr)

/-! ## The exact read: the tension is the correlation spectral gap

Tracing the library read (`reads.py`, `_spectral_from_cov`) shows the tension is not `log(λ₁/edge)`
in general but the log-ratio of the top TWO correlation eigenvalues, with the noise floor as a
backstop: `μ = log(λ₁ / max(λ₂, edge))`. This is the correlation-operator SPECTRAL GAP -- the
transfer-matrix mass-gap structure itself. The `edge`-branch (`λ₂ ≤ edge`, a single dominant mode)
recovers the min-entropy deficit above; the general form carries the second eigenvalue. Verified
machine-exact against the read (`|μ - log(λ₁/max(λ₂,edge))| = 0`). -/

/-- The exact confinement tension: the correlation spectral gap `μ = log(λ₁ / max(λ₂, edge))`. -/
noncomputable def gapTension (l1 l2 edge : ℝ) : ℝ := Real.log (l1 / max l2 edge)

/-- **The gap tension reduces to the edge form when the second mode is below the floor.** For
`λ₂ ≤ edge` (one dominant mode, the confined branch), `μ = log(λ₁/edge)` -- the `tension` above, whose
value is the min-entropy deficit. -/
theorem gapTension_eq_edge_of_le {l1 l2 edge : ℝ} (h : l2 ≤ edge) :
    gapTension l1 l2 edge = Real.log (l1 / edge) := by
  unfold gapTension; rw [max_eq_right h]

/-- **Confinement for the exact (gap) tension.** `μ < κ₀ ↔ λ₁ < e^{κ₀} · max(λ₂, edge)`: the leading
correlation eigenvalue stays within `e^{κ₀}` (= `3^{1/4}` at `κ₀ = ¼log3`) of the second eigenvalue,
or of the noise floor when the second is below it. The spectral gap staying below the counting floor
`κ₀`, exactly. -/
theorem confinement_iff_gap {l1 l2 edge κ₀ : ℝ} (hr : 0 < max l2 edge) (hl1 : 0 < l1) :
    gapTension l1 l2 edge < κ₀ ↔ l1 < Real.exp κ₀ * max l2 edge := by
  unfold gapTension
  rw [← Real.exp_lt_exp, Real.exp_log (div_pos hl1 hr), div_lt_iff₀ hr]

end MassGap.MinEntropy
