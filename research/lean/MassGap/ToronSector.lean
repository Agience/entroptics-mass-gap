import Mathlib
import MassGap.PhotonStall
import MassGap.ToronDecrement

/-!
# MassGap.ToronSector — the flat-connection sector of SU(2), in closed form

`CouplingTower.StrongEnd N` asks that, frequently as `β → ∞`, the doubling defect `D(β, ·)` tend to `0`
along the windows. `PhotonStall` computes `D` for the Gaussian photon: `D = phRest + (2^d − 1)(d − 1)/2 · log β`,
with the flat directions (holonomies) carrying a `β`-free volume because no photon mode is charged under
them. This module computes what changes for `SU(2)`: the flat connections are commuting holonomies in the
maximal torus, and the off-diagonal (charged) gluons feel them. Declarations are in `MassGap.ToronSector`.

The model here is a Gaussian-plus-toron model: Gaussian fluctuations around a constant abelian holonomy
background, with the toron angles integrated against the charged determinant. It is not the `SU(2)` Wilson
measure, and nothing in this module links the two.

## 1. The charged determinant in a holonomy background (proved)

A mode of charge `q` in the constant background angle `θ_μ` on the periodic torus of side `L` has the twisted
spectrum `ω²_k(qθ) = Σ_μ (2 − 2 cos((2π k_μ + q θ_μ)/L)) = Σ_μ 4 sin²((2π k_μ + q θ_μ)/(2L))` (`omegaQ`,
`two_sub_two_cos`); `chargedDet` is its full determinant and `logDetQ` its `log det′`.

* `omegaQ_zero_charge`, `logDetQ_zero_charge`: at charge `0` the spectrum is `WindowFreq.omega2D 0` and
  `log det′` is `WindowFreq.logDetD 0`, the same for every `θ`. `chargedDet_zero_charge`: the full determinant
  is `0` at every `θ` (the zero mode never lifts). This is the photon: no field is charged under the
  holonomy.
* `chargedDet_nonneg`; `chargedDet_flat`: at `θ = 0` the charged determinant is `0` (the charged constant
  modes become zero modes); `chargedDet_pos`: if some `q θ_μ ∈ (0, 2π)` it is positive.
* `chargedDet_one`: on the ring (`d = 1`), `chargedDet q 1 L θ = 2 − 2 cos(q θ)`, independent of `L`
  (from `ToronDecrement.twisted_det_one_dim`).

## 2. SU(2): the toron potential is not constant (proved)

The holonomy `diag(e^{iθ}, e^{−iθ})` acts on the off-diagonal generator `E₁₂` by `e^{2iθ}`: the root of
`su(2)` gives charge `2` in the fundamental angle. The pair `E₁₂, E₂₁` is one complex field of charge `2`.

* `su2_toron_not_constant` (`d ≥ 1`): `chargedDet 2 d L 0 = 0 < chargedDet 2 d L (π/2)`. The weight
  `det(θ)^{−(d−2)}` of the transverse charged modes depends on `θ`, so the zero-mode integral is not a pure
  volume, in contrast with the photon (`logDetQ_zero_charge`).
* `chargedDet_centre`: the determinant vanishes at every centre point `θ_μ ∈ {0, π}` (holonomy `±1`): the
  `2^d` minima of `det`, where the toron weight is largest, are the centre-symmetric points.
* `su2_ring_weyl`, `vandermonde_su2`: on the ring the charged determinant is `4 sin² θ = |e^{iθ} − e^{−iθ}|²`,
  the Weyl (Vandermonde) density of `SU(2)` class functions. The Haar reduction of the one-dimensional theory
  and the charged one-loop determinant have the same closed form `4 sin²θ`.
* `omegaQ_zero_mode_le`: the charged constant mode has `ω²₀(qθ) ≤ Σ_μ (q θ_μ / L)²`, so near `θ = 0` the
  determinant vanishes at least quadratically in `|θ|` through that factor.

## 3. Where the coupling enters (proved for the model)

* `logDetQβ_eq`, `dbl_volume`: off the zero set of `ω²`, the charged Gaussian factors carry `β` through
  `L^d · log β`, which the doubling cancels exactly. At generic `θ` the charged sector adds no `log β` to `D`.
* `radial_cutoff`, `marginal_iff`: near `θ = 0`, the charged weight `|θ|^{−2(d−2)}` on `d^dθ` has radial
  power `r^{(d−1)−2(d−2)}`, which is `r^{−1}` exactly at `d = 4`. With the constant-mode cutoff at
  `r = β^{−1/4}` (CHOSEN, the quartic scale argued in `ToronDecrement`),
  `∫_{β^{−1/4}}^{R} dr/r = log R + (log β)/4`. So the toron integral is `x + B_L`, `x = (log β)/4`, the shape of
  `ToronDecrement.ToronLaplace`.

## 4. The defect of the Gaussian-plus-toron model (proved)

`toronDefect A c B β w = A w + c log β + 16 log(x + B_w) − log(x + B_{w+1})`, `x = (log β)/4`: a window part
`A`, a power of `β` (`c log β`, any real `c`) and the toron term (`toronTerm`), with toron constants
`B_w → b > 0`.

* `toronTerm_tendsto`: along the windows the toron term tends to `15 log(x + b)`.
* `betaRead_eventually_injective`: `ℓ ↦ c ℓ + 15 log(ℓ/4 + b)` is injective for large `ℓ`, for every real
  `c` (increasing for `c ≥ 0` on `ℓ ≥ 0`; decreasing for `c < 0` on `ℓ ≥ 15/(−c)`).
* `toron_vanishes_unique`, `toron_not_strongEnd`: if `D(β, ·) → 0` at two couplings then their reads agree;
  so the model's `D` does not tend to `0` frequently as `β → ∞`, whatever `A` and `c`.
* `su2_not_strongEnd`: the `SU(2)` model `PhotonStall.defectPh β 4 + R + toronTerm` (Cartan photon, a
  `β`-free charged remainder `R`, the toron term) fails the bridge's shape.

Plainly: the toron sector is a genuine abelian/non-abelian difference (`θ`-dependent charged determinant,
centre minima, Weyl density), and in `D` it contributes `15 log((log β)/4 + b)` in the window limit,
on top of the photon's `(45/2) log β`. In this model it raises the stall; it does not dissolve it. The `log β` coefficient
is unchanged; the new `β`-dependence is `log log β`.

## What does not follow

* Nothing here is a statement about `CouplingTower.windowCoupling`. The Gaussian-plus-toron model is a model;
  no theorem links it to the `SU(2)` Wilson measure.
* The weight `det^{−(d−2)}` (transverse count less Faddeev–Popov, as in `PhotonStall`), the cutoff
  `β^{−1/4}`, the form `log Z_L ∋ log(x + B_L)` and `B_w → b > 0` are CHOSEN model inputs, not derived; the
  constant-mode quartic integral is not computed.
* ARGUED, not proved: if `StrongEnd N` holds, then at large `β`, on a window growing with `β`, the `SU(2)`
  defect is not close to any Gaussian-plus-one-loop-toron model of this shape, and the departure from this
  model would have to come from beyond one loop around the flat connections (for instance windows past the
  scale where the running coupling becomes large), which this module does not reach.
* `StrongEnd N` is neither proved nor refuted.

DERIVED (module-wide): `0` the zero angle, the signs and the limit; `1` the ring dimension and the least
box; `2` from `2 − 2 cos = 4 sin²(·/2)`, the doubling and the `su(2)` root `1 − (−1)`; `2π` the period; `4`
from `(2 sin)²`, the dimension at which `(d − 1) − 2(d − 2) = −1`, and `x = (log β)/4` from `∫ dr/r` at
`β^{−1/4}`; `16 = 2⁴` the copies; `15 = 16 − 1` their window limit; `π/2` the angle at which `2θ = π`; `π` the
centre angle. CHOSEN: the cutoff exponent `1/4` (quartic constant-mode scale), the toron weight and the model
shape of `toronDefect`. Inherited: `45/2 = phCoeff 4` from `PhotonStall`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ToronSector

open Real Filter Topology Finset
open MassGap.WindowFreq (omega2D logDetD)
open MassGap.PhotonStall (dbl defectPh phRest phCoeff defectPh_split)

/-! ## 1. The charged determinant -/

/-- `2 − 2 cos 2x = 4 sin² x`. DERIVED: `2`, `4` from the double angle. -/
theorem two_sub_two_cos (x : ℝ) : 2 - 2 * Real.cos (2 * x) = 4 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq x

/-- **The twisted frequency of a charge-`q` mode** in the constant background angle `θ`:
`Σ_μ (2 − 2 cos((2π k_μ + q θ_μ)/L))`. DERIVED: `2π` the period, `2` from `|1 − e^{iφ}|²`. -/
def omegaQ (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) (k : Fin d → Fin L) : ℝ :=
  ∑ μ, (2 - 2 * Real.cos ((2 * π * ((k μ : ℕ) : ℝ) + q * θ μ) / L))

/-- **The charged determinant** over all `L^d` momenta. -/
def chargedDet (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) : ℝ := ∏ k : Fin d → Fin L, omegaQ q d L θ k

/-- **The charged `log det′`** (zero frequencies removed). DERIVED: `0` the removed frequency. -/
def logDetQ (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Fin d → Fin L)).filter (fun k => omegaQ q d L θ k ≠ 0),
    Real.log (omegaQ q d L θ k)

/-- **Charge zero is the untwisted spectrum**, at every background. DERIVED: `0` the charge. -/
theorem omegaQ_zero_charge (d L : ℕ) (θ : Fin d → ℝ) (k : Fin d → Fin L) :
    omegaQ 0 d L θ k = omega2D 0 d L k := by
  unfold omegaQ omega2D FreqRead.phat2
  rw [zero_pow two_ne_zero, zero_add]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [zero_mul, add_zero]
  have e : (2 * π * ((k μ : ℕ) : ℝ)) / (L : ℝ) = 2 * (π * ((k μ : ℕ) : ℝ) / L) := by ring
  rw [e, two_sub_two_cos]
  ring

/-- **The neutral `log det′` does not see the holonomy**: `logDetQ 0 d L θ = logDetD 0 d L` for every `θ`. -/
theorem logDetQ_zero_charge (d L : ℕ) (θ : Fin d → ℝ) : logDetQ 0 d L θ = logDetD 0 d L := by
  unfold logDetQ logDetD
  simp only [omegaQ_zero_charge]

/-- The frequency is non-negative. DERIVED: `0` the sign. -/
theorem omegaQ_nonneg (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) (k : Fin d → Fin L) : 0 ≤ omegaQ q d L θ k :=
  Finset.sum_nonneg fun μ _ => by
    linarith [Real.cos_le_one ((2 * π * ((k μ : ℕ) : ℝ) + q * θ μ) / L)]

/-- The charged determinant is non-negative. -/
theorem chargedDet_nonneg (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) : 0 ≤ chargedDet q d L θ :=
  Finset.prod_nonneg fun k _ => omegaQ_nonneg q d L θ k

/-- **At the trivial holonomy the charged determinant vanishes**: the constant charged modes are zero
modes. DERIVED: `0` the angle and the constant momentum. -/
theorem chargedDet_flat (q : ℝ) {d L : ℕ} (hL : 0 < L) : chargedDet q d L (fun _ => 0) = 0 := by
  unfold chargedDet
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ => (⟨0, hL⟩ : Fin L))) ?_
  unfold omegaQ
  simp

/-- **The neutral determinant vanishes at every background**: the zero mode of a neutral field never lifts.
DERIVED: `0` the charge. -/
theorem chargedDet_zero_charge {d L : ℕ} (hL : 0 < L) (θ : Fin d → ℝ) : chargedDet 0 d L θ = 0 := by
  unfold chargedDet
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ => (⟨0, hL⟩ : Fin L))) ?_
  unfold omegaQ
  simp

/-- `2 − 2 cos t > 0` on `(0, 2π)`. DERIVED: `2π` the period. -/
theorem two_sub_two_cos_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * π) : 0 < 2 - 2 * Real.cos t := by
  have hle := Real.cos_le_one t
  have hne : Real.cos t ≠ 1 := by
    intro h
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) h1).1 h
    linarith
  have : Real.cos t < 1 := lt_of_le_of_ne hle hne
  linarith

/-- **Off the zero set every charged frequency is positive**: if `q θ_μ ∈ (0, 2π)` for one direction `μ`,
then `ω²_k(qθ) > 0` at every momentum. DERIVED: `1` the step `k_μ + 1 ≤ L`. -/
theorem omegaQ_pos {q : ℝ} {d L : ℕ} {θ : Fin d → ℝ} (μ : Fin d) (h0 : 0 < q * θ μ)
    (h1 : q * θ μ < 2 * π) (k : Fin d → Fin L) : 0 < omegaQ q d L θ k := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (k μ).pos
  have hkN : (k μ : ℕ) + 1 ≤ L := (k μ).isLt
  have hk : ((k μ : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ ((k μ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hA := mul_nonneg h2π hk0
  have hB := mul_le_mul_of_nonneg_left hk h2π
  have ht0 : 0 < (2 * π * ((k μ : ℕ) : ℝ) + q * θ μ) / L := div_pos (by linarith) hL
  have ht1 : (2 * π * ((k μ : ℕ) : ℝ) + q * θ μ) / L < 2 * π := by
    rw [div_lt_iff₀ hL]
    nlinarith
  unfold omegaQ
  exact Finset.sum_pos' (fun ν _ => by
      linarith [Real.cos_le_one ((2 * π * ((k ν : ℕ) : ℝ) + q * θ ν) / L)])
    ⟨μ, Finset.mem_univ _, two_sub_two_cos_pos ht0 ht1⟩

/-- **The charged determinant is positive off the zero set.** -/
theorem chargedDet_pos {q : ℝ} {d L : ℕ} {θ : Fin d → ℝ} (μ : Fin d) (h0 : 0 < q * θ μ)
    (h1 : q * θ μ < 2 * π) : 0 < chargedDet q d L θ :=
  Finset.prod_pos fun k _ => omegaQ_pos μ h0 h1 k

/-- **The ring determinant in closed form**: `chargedDet q 1 L θ = 2 − 2 cos(q θ)`, independent of `L`.
DERIVED: `1` the dimension. -/
theorem chargedDet_one (q : ℝ) {L : ℕ} (hL : 0 < L) (θ : Fin 1 → ℝ) :
    chargedDet q 1 L θ = 2 - 2 * Real.cos (q * θ 0) := by
  unfold chargedDet omegaQ
  simp only [Fin.sum_univ_one]
  rw [show (∏ x : Fin 1 → Fin L, (2 - 2 * Real.cos ((2 * π * ((x 0 : ℕ) : ℝ) + q * θ 0) / L)))
      = ∏ j : Fin L, (2 - 2 * Real.cos ((2 * π * ((j : ℕ) : ℝ) + q * θ 0) / L)) from
      Fintype.prod_equiv (Equiv.funUnique (Fin 1) (Fin L)) _ _ (fun x => rfl)]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => 2 - 2 * Real.cos ((2 * π * (k : ℝ) + q * θ 0) / L)) L]
  exact ToronDecrement.twisted_det_one_dim L hL (q * θ 0)

/-! ## 2. SU(2) -/

/-- **The SU(2) toron weight is not constant** (`d ≥ 1`): the charge-`2` determinant is `0` at the trivial
holonomy and positive at `θ = π/2`. DERIVED: `2` the root of `su(2)`; `π/2` the angle with `2θ = π`. -/
theorem su2_toron_not_constant {d L : ℕ} (hd : 0 < d) (hL : 0 < L) :
    chargedDet 2 d L (fun _ => 0) = 0 ∧ 0 < chargedDet 2 d L (fun _ => π / 2) := by
  refine ⟨chargedDet_flat 2 hL, chargedDet_pos (⟨0, hd⟩ : Fin d) ?_ ?_⟩
  · have := Real.pi_pos; linarith
  · have := Real.pi_pos; linarith

/-- **The centre points are zeros of the SU(2) charged determinant**: if every `θ_μ ∈ {0, π}` (holonomy
`±1`, the centre of `SU(2)`), `chargedDet 2 d L θ = 0`. DERIVED: `π` the centre angle; `1` the step
`L − 1`. -/
theorem chargedDet_centre {d L : ℕ} (hL : 0 < L) {θ : Fin d → ℝ} (hθ : ∀ μ, θ μ = 0 ∨ θ μ = π) :
    chargedDet 2 d L θ = 0 := by
  classical
  unfold chargedDet
  refine Finset.prod_eq_zero (Finset.mem_univ (fun μ =>
    if θ μ = 0 then (⟨0, hL⟩ : Fin L) else (⟨L - 1, by omega⟩ : Fin L))) ?_
  unfold omegaQ
  refine Finset.sum_eq_zero fun μ _ => ?_
  beta_reduce
  rcases hθ μ with h | h
  · rw [if_pos h, h]
    simp
  · have hne : θ μ ≠ 0 := by rw [h]; exact Real.pi_pos.ne'
    rw [if_neg hne, h]
    have hc : (((⟨L - 1, by omega⟩ : Fin L) : ℕ) : ℝ) = (L : ℝ) - 1 := by
      show ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1
      rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    rw [hc]
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    have e : (2 * π * ((L : ℝ) - 1) + 2 * π) / L = 2 * π := by field_simp; ring
    rw [e, Real.cos_two_pi]
    ring

/-- **On the ring the SU(2) charged determinant is the Weyl density** `4 sin² θ`. -/
theorem su2_ring_weyl {L : ℕ} (hL : 0 < L) (θ : Fin 1 → ℝ) :
    chargedDet 2 1 L θ = 4 * Real.sin (θ 0) ^ 2 := by
  rw [chargedDet_one 2 hL, two_sub_two_cos]

/-- **The SU(2) Vandermonde**: `|e^{iθ} − e^{−iθ}|² = 4 sin² θ`. -/
theorem vandermonde_su2 (θ : ℝ) :
    Complex.normSq (Complex.exp (θ * Complex.I) - Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))
      = 4 * Real.sin θ ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

/-- **The charged constant mode vanishes quadratically at the trivial holonomy**:
`ω²₀(qθ) ≤ Σ_μ (q θ_μ / L)²`. DERIVED: `0` the constant momentum; `2` from `1 − x²/2 ≤ cos x`. -/
theorem omegaQ_zero_mode_le (q : ℝ) {d L : ℕ} (hL : 0 < L) (θ : Fin d → ℝ) :
    omegaQ q d L θ (fun _ => ⟨0, hL⟩) ≤ ∑ μ, (q * θ μ / L) ^ 2 := by
  unfold omegaQ
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := Real.one_sub_sq_div_two_le_cos (x := q * θ μ / L)
  have e : (2 * π * (((⟨0, hL⟩ : Fin L) : ℕ) : ℝ) + q * θ μ) / L = q * θ μ / L := by simp
  rw [e]
  linarith

/-! ## 3. Where the coupling enters -/

/-- **The charged Gaussian carries `β` extensively**: if every `ω²_k > 0`,
`Σ_k log(β ω²_k) = Σ_k log ω²_k + L^d log β`. -/
theorem logDetQβ_eq {β : ℝ} (hβ : 0 < β) {q : ℝ} {d L : ℕ} {θ : Fin d → ℝ}
    (hpos : ∀ k, 0 < omegaQ q d L θ k) :
    ∑ k : Fin d → Fin L, Real.log (β * omegaQ q d L θ k)
      = (∑ k : Fin d → Fin L, Real.log (omegaQ q d L θ k)) + (L : ℝ) ^ d * Real.log β := by
  have e : ∀ k : Fin d → Fin L, Real.log (β * omegaQ q d L θ k)
      = Real.log (omegaQ q d L θ k) + Real.log β := fun k => by
    rw [Real.log_mul hβ.ne' (hpos k).ne', add_comm]
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [PhotonStall.card_modes]
  push_cast
  ring

/-- **The doubling cancels an extensive `log β`**: `dbl d (L ↦ L^d log β) = 0`. DERIVED: `2` the doubling. -/
theorem dbl_volume (d : ℕ) (β : ℝ) (L : ℕ) : dbl d (fun n => (n : ℝ) ^ d * Real.log β) L = 0 := by
  unfold dbl
  push_cast
  rw [mul_pow]
  ring

/-- `∫_ε^R dr/r = log R − log ε`. -/
theorem radial_log {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∫ r in ε..R, r⁻¹ = Real.log R - Real.log ε := by
  rw [integral_inv_of_pos hε hR, Real.log_div hR.ne' hε.ne']

/-- **The toron integral at the quartic cutoff**: `∫_{β^{−1/4}}^R dr/r = log R + (log β)/4`.
CHOSEN: the cutoff exponent `1/4`. -/
theorem radial_cutoff {β R : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    ∫ r in β ^ (-(1 / 4 : ℝ))..R, r⁻¹ = Real.log R + Real.log β / 4 := by
  rw [radial_log (Real.rpow_pos_of_pos hβ _) hR, Real.log_rpow hβ]
  ring

/-- **The toron integral is marginal exactly in four dimensions**: the radial power
`(d − 1) − 2(d − 2)` of `|θ|^{−2(d−2)} d^dθ` is `−1` iff `d = 4`. DERIVED: `1` the sphere, `2(d − 2)` the
transverse charged weight. -/
theorem marginal_iff (d : ℕ) : ((d : ℤ) - 1) - 2 * ((d : ℤ) - 2) = -1 ↔ d = 4 := by
  omega

/-! ## 4. The defect of the Gaussian-plus-toron model -/

/-- **The toron term** `16 log(x + B_w) − log(x + B_{w+1})`, `x = (log β)/4`. DERIVED: `16 = 2⁴`, `4`. -/
def toronTerm (B : ℕ → ℝ) (β : ℝ) (w : ℕ) : ℝ :=
  16 * Real.log (Real.log β / 4 + B w) - Real.log (Real.log β / 4 + B (w + 1))

/-- **The Gaussian-plus-toron defect** `A w + c log β + toronTerm B β w`. CHOSEN: the model shape. -/
def toronDefect (A : ℕ → ℝ) (c : ℝ) (B : ℕ → ℝ) (β : ℝ) (w : ℕ) : ℝ :=
  A w + c * Real.log β + toronTerm B β w

/-- **The `β` read of the window limit**: `c ℓ + 15 log(ℓ/4 + b)`. DERIVED: `15 = 16 − 1`. -/
def betaRead (c b l : ℝ) : ℝ := c * l + 15 * Real.log (l / 4 + b)

/-- **The toron term along the windows**: `→ 15 log(x + b)`. DERIVED: `15 = 16 − 1`. -/
theorem toronTerm_tendsto {B : ℕ → ℝ} {b : ℝ} (hB : Tendsto B atTop (𝓝 b)) {β : ℝ}
    (hx : Real.log β / 4 + b ≠ 0) :
    Tendsto (toronTerm B β) atTop (𝓝 (15 * Real.log (Real.log β / 4 + b))) := by
  have h0 : Tendsto (fun w => Real.log (Real.log β / 4 + B w)) atTop
      (𝓝 (Real.log (Real.log β / 4 + b))) := (tendsto_const_nhds.add hB).log hx
  have h1 : Tendsto (fun w => Real.log (Real.log β / 4 + B (w + 1))) atTop
      (𝓝 (Real.log (Real.log β / 4 + b))) := h0.comp (tendsto_add_atTop_nat 1)
  have h := (h0.const_mul 16).sub h1
  have e : 15 * Real.log (Real.log β / 4 + b)
      = 16 * Real.log (Real.log β / 4 + b) - Real.log (Real.log β / 4 + b) := by ring
  rw [e]
  exact h

/-- `c ≥ 0`: the read is strictly increasing on `ℓ ≥ 0`. -/
theorem betaRead_strictMono_of_nonneg {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b) {l₁ l₂ : ℝ} (h1 : 0 ≤ l₁)
    (h12 : l₁ < l₂) : betaRead c b l₁ < betaRead c b l₂ := by
  unfold betaRead
  have hy : 0 < l₁ / 4 + b := by linarith
  have hlog := Real.log_lt_log hy (by linarith : l₁ / 4 + b < l₂ / 4 + b)
  have hm := mul_le_mul_of_nonneg_left h12.le hc
  linarith

/-- `c < 0`: the read is strictly decreasing on `ℓ ≥ 15/(−c)`. -/
theorem betaRead_strictAnti_of_neg {c b : ℝ} (hc : c < 0) (hb : 0 < b) {l₁ l₂ : ℝ} (h1 : 15 / (-c) ≤ l₁)
    (h12 : l₁ < l₂) : betaRead c b l₂ < betaRead c b l₁ := by
  unfold betaRead
  have hc' : 0 < -c := by linarith
  have h15 : 15 ≤ -c * l₁ := by rw [div_le_iff₀ hc'] at h1; linarith
  have hl1 : 0 < l₁ := by nlinarith
  have hy1 : 0 < l₁ / 4 + b := by linarith
  have hy2 : 0 < l₂ / 4 + b := by linarith
  have hlog : Real.log (l₂ / 4 + b) - Real.log (l₁ / 4 + b) ≤ (l₂ / 4 + b) / (l₁ / 4 + b) - 1 := by
    rw [← Real.log_div hy2.ne' hy1.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hy2 hy1)
  have hden : 0 < l₁ + 4 * b := by linarith
  have hq : (l₂ / 4 + b) / (l₁ / 4 + b) - 1 = (l₂ - l₁) / (l₁ + 4 * b) := by
    field_simp
    ring
  rw [hq] at hlog
  have hd : 0 < l₂ - l₁ := by linarith
  have key : 15 * ((l₂ - l₁) / (l₁ + 4 * b)) < -c * (l₂ - l₁) := by
    rw [mul_div_assoc', div_lt_iff₀ hden]
    nlinarith [mul_pos hd (mul_pos hc' hb), mul_le_mul_of_nonneg_left h15 hd.le]
  nlinarith

/-- **The read is eventually injective, for every real `c`.** -/
theorem betaRead_eventually_injective (c : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ l₁ l₂ : ℝ, T ≤ l₁ → T ≤ l₂ → betaRead c b l₁ = betaRead c b l₂ → l₁ = l₂ := by
  rcases le_or_gt 0 c with hc | hc
  · refine ⟨0, le_rfl, fun l₁ l₂ h1 h2 he => ?_⟩
    rcases lt_trichotomy l₁ l₂ with h | h | h
    · exact absurd he (betaRead_strictMono_of_nonneg hc hb h1 h).ne
    · exact h
    · exact absurd he (betaRead_strictMono_of_nonneg hc hb h2 h).ne'
  · refine ⟨15 / (-c), (div_pos (by norm_num) (by linarith)).le, fun l₁ l₂ h1 h2 he => ?_⟩
    rcases lt_trichotomy l₁ l₂ with h | h | h
    · exact absurd he (betaRead_strictAnti_of_neg hc hb h1 h).ne'
    · exact h
    · exact absurd he (betaRead_strictAnti_of_neg hc hb h2 h).ne

/-- **Two vanishing couplings have the same read.** DERIVED: `0` the limit. -/
theorem toron_vanishes_unique {A : ℕ → ℝ} {c : ℝ} {B : ℕ → ℝ} {b : ℝ} (hB : Tendsto B atTop (𝓝 b))
    (hb : 0 < b) {β₁ β₂ : ℝ} (hp1 : 0 ≤ Real.log β₁) (hp2 : 0 ≤ Real.log β₂)
    (t1 : Tendsto (toronDefect A c B β₁) atTop (𝓝 0)) (t2 : Tendsto (toronDefect A c B β₂) atTop (𝓝 0)) :
    betaRead c b (Real.log β₁) = betaRead c b (Real.log β₂) := by
  have hx1 : Real.log β₁ / 4 + b ≠ 0 := by
    have : 0 < Real.log β₁ / 4 + b := by linarith
    exact this.ne'
  have hx2 : Real.log β₂ / 4 + b ≠ 0 := by
    have : 0 < Real.log β₂ / 4 + b := by linarith
    exact this.ne'
  have e1 := toronTerm_tendsto hB hx1
  have e2 := toronTerm_tendsto hB hx2
  have hc : Tendsto (fun _ : ℕ => c * Real.log β₁ - c * Real.log β₂) atTop
      (𝓝 (c * Real.log β₁ - c * Real.log β₂)) := tendsto_const_nhds
  have hlim := hc.add (e1.sub e2)
  have hlim' : Tendsto (fun w => toronDefect A c B β₁ w - toronDefect A c B β₂ w) atTop
      (𝓝 ((c * Real.log β₁ - c * Real.log β₂)
        + (15 * Real.log (Real.log β₁ / 4 + b) - 15 * Real.log (Real.log β₂ / 4 + b)))) :=
    Tendsto.congr (fun w => by simp only [toronDefect]; ring) hlim
  have h0 := t1.sub t2
  rw [sub_zero] at h0
  have := tendsto_nhds_unique hlim' h0
  unfold betaRead
  linarith

/-- **The Gaussian-plus-toron model fails the bridge's shape**, for every window part `A` and every power
`c`: it is not true that frequently as `β → ∞` its defect tends to `0` along the windows. This is a model
statement, not a statement about the Wilson measure. -/
theorem toron_not_strongEnd (A : ℕ → ℝ) (c : ℝ) {B : ℕ → ℝ} {b : ℝ} (hB : Tendsto B atTop (𝓝 b))
    (hb : 0 < b) : ¬ ∃ᶠ β in atTop, Tendsto (toronDefect A c B β) atTop (𝓝 0) := by
  obtain ⟨T, hT0, hT⟩ := betaRead_eventually_injective c hb
  intro h
  obtain ⟨β₁, hb1, p1⟩ := frequently_atTop.1 h (Real.exp T)
  obtain ⟨β₂, hb2, p2⟩ := frequently_atTop.1 h (β₁ + 1)
  have hpos1 : 0 < β₁ := lt_of_lt_of_le (Real.exp_pos T) hb1
  have hpos2 : 0 < β₂ := by linarith
  have hl1 : T ≤ Real.log β₁ := (Real.le_log_iff_exp_le hpos1).2 hb1
  have hl2 : T ≤ Real.log β₂ := (Real.le_log_iff_exp_le hpos2).2 (by linarith)
  have he := toron_vanishes_unique hB hb (by linarith) (by linarith) p1 p2
  have hl := hT _ _ hl1 hl2 he
  have := Real.log_injOn_pos (Set.mem_Ioi.2 hpos1) (Set.mem_Ioi.2 hpos2) hl
  linarith

/-- **The SU(2) Gaussian-plus-toron defect**: the Cartan photon (`PhotonStall.defectPh β 4`), a `β`-free
charged remainder `R` (`dbl_volume`: the charged Gaussian's `β` cancels at generic `θ`), and the toron
term. CHOSEN: the model. DERIVED: `4` the dimension. -/
def su2Defect (R : ℕ → ℝ) (B : ℕ → ℝ) (β : ℝ) (w : ℕ) : ℝ :=
  defectPh β 4 (2 ^ w) + R w + toronTerm B β w

/-- The SU(2) model is a toron defect with `c = phCoeff 4 = 45/2`. -/
theorem su2Defect_eq (R B : ℕ → ℝ) {β : ℝ} (hβ : 0 < β) :
    su2Defect R B β = toronDefect (fun w => phRest 4 (2 ^ w) + R w) (phCoeff 4) B β := by
  funext w
  unfold su2Defect toronDefect
  rw [defectPh_split hβ (by positivity)]
  ring

/-- **The SU(2) Gaussian-plus-toron model fails the bridge's shape.** -/
theorem su2_not_strongEnd (R : ℕ → ℝ) {B : ℕ → ℝ} {b : ℝ} (hB : Tendsto B atTop (𝓝 b)) (hb : 0 < b) :
    ¬ ∃ᶠ β in atTop, Tendsto (su2Defect R B β) atTop (𝓝 0) := by
  intro h
  refine toron_not_strongEnd (fun w => phRest 4 (2 ^ w) + R w) (phCoeff 4) hB hb ?_
  refine (h.and_eventually (eventually_gt_atTop 0)).mono fun β hβ => ?_
  rw [← su2Defect_eq R B hβ.2]
  exact hβ.1

end MassGap.ToronSector

end

#print axioms MassGap.ToronSector.two_sub_two_cos
#print axioms MassGap.ToronSector.omegaQ_zero_charge
#print axioms MassGap.ToronSector.logDetQ_zero_charge
#print axioms MassGap.ToronSector.omegaQ_nonneg
#print axioms MassGap.ToronSector.chargedDet_nonneg
#print axioms MassGap.ToronSector.chargedDet_flat
#print axioms MassGap.ToronSector.chargedDet_zero_charge
#print axioms MassGap.ToronSector.two_sub_two_cos_pos
#print axioms MassGap.ToronSector.omegaQ_pos
#print axioms MassGap.ToronSector.chargedDet_pos
#print axioms MassGap.ToronSector.chargedDet_one
#print axioms MassGap.ToronSector.su2_toron_not_constant
#print axioms MassGap.ToronSector.chargedDet_centre
#print axioms MassGap.ToronSector.su2_ring_weyl
#print axioms MassGap.ToronSector.vandermonde_su2
#print axioms MassGap.ToronSector.omegaQ_zero_mode_le
#print axioms MassGap.ToronSector.logDetQβ_eq
#print axioms MassGap.ToronSector.dbl_volume
#print axioms MassGap.ToronSector.radial_log
#print axioms MassGap.ToronSector.radial_cutoff
#print axioms MassGap.ToronSector.marginal_iff
#print axioms MassGap.ToronSector.toronTerm_tendsto
#print axioms MassGap.ToronSector.betaRead_strictMono_of_nonneg
#print axioms MassGap.ToronSector.betaRead_strictAnti_of_neg
#print axioms MassGap.ToronSector.betaRead_eventually_injective
#print axioms MassGap.ToronSector.toron_vanishes_unique
#print axioms MassGap.ToronSector.toron_not_strongEnd
#print axioms MassGap.ToronSector.su2Defect_eq
#print axioms MassGap.ToronSector.su2_not_strongEnd
