import Mathlib
import MassGap.VortexEntropy
import MassGap.SU2DiskLaw
import MassGap.TwistedTraceBound

/-!
# MassGap.ThickSheetCost — a thickened centre sheet costs the same per coarse cell at every thickness

The proposed separation of `SU(N)` from `U(1)`: a centre-vortex sheet can be thickened, the centre
twist spread over many plaquettes, so its cost per unit area falls below the entropy `¼ ln 3` of
closed surfaces (`VortexEntropy`). This module computes what an abelian (Cartan) thickening gives,
for both groups, and finds the comparison independent of the thickness.

## The section and the coarse cell

A thick sheet is read in sections transverse to it. A section is `m` plaquettes (an `L × L` block,
`m = L²`) carrying angles `φ : Fin m → ℝ` whose total is the flux `θ`. Its Wilson cost is
`spreadCost φ = Σ (1 − cos φᵢ)`. Coarse-graining by the thickness, a coarse plaquette of the sheet
holds `m` sections, so its cost is `cellCost Φ = Σ_s spreadCost (Φ s)`. CHOSEN: the coarse spacing
equals the thickness, so the count of sections per coarse cell equals the count of plaquettes per
section; the surfaces of `VortexEntropy` are then drawn on the coarse lattice.

## What is proved

* `spreadCost_ge`: angles in `[−π, π]` with total `θ` cost at least `2θ²/(π² m)` (cited
  `Real.cos_le_one_sub_mul_cos_sq`, and `sq_sum_le_card_mul_sum_sq`).
* `uniform_spreadCost_le`: the even spread costs at most `θ²/(2m)` (cited
  `Real.one_sub_sq_div_two_le_cos`).
* **`cellCost_ge`**, **`cellCost_uniform_le`**: per coarse cell every admissible profile costs at
  least `2θ²/π²`, and the even one at most `θ²/2`, at every `m`. Neither bound moves with the
  thickness.
* `cellCost_uniform_tendsto`: the even profile's coarse cost tends to `θ²/2` (cited `Real.cos_bound`).
* **`trial_summable`**: if `β > π² ln 3 / (8θ²)` then for every `m` and every admissible profile the
  sum `Σ_k 3^k e^{−β c (4k + 6)}` over the closed coarse surfaces through a plaquette converges,
  `c = cellCost Φ`. **`uniform_trial_not_summable`**: if `β θ²/2 ≤ ¼ ln 3` the even profile's sum
  diverges at every `m`.
* The two groups carry the same sections. `su2_section`: for `SU(2)`, the diagonal elements
  `dmat φᵢ = diag(e^{iφᵢ}, e^{−iφᵢ})` multiply to `dmat θ`, which is the centre element `−1` at
  `θ = π` (`dmat_pi`), and their Wilson densities sum to `spreadCost φ` (`wilsonDensity_dmat`).
  `u1_section`: for `U(1)`, the phases `e^{iφᵢ}` multiply to `e^{iθ}`, `−1` at `θ = π`, and their
  costs `1 − Re e^{iφᵢ}` sum to the same `spreadCost φ`.

## Where the attack stops

The thick-sheet trial gives a cost per coarse cell in `[2θ²/π², θ²/2]` times `β`, the same at every
thickness: classical scale invariance of the four-dimensional action. It beats the entropy only
when `β θ²/2 ≤ ¼ ln 3`, that is `β ≤ ln 3/(2π²)` for the `SU(2)` centre `θ = π`, inside the
strong-coupling regime the tree already holds (`StrongAnchor.strongAnchor`). At larger `β` no
abelian profile of any thickness brings the cost below the entropy (`trial_summable`). The same
numbers hold for `U(1)` with the same `θ`: at this level the two groups are not separated.

What would move the comparison is a coupling that depends on the thickness, the effective coupling
of the field inside a sheet of thickness `L` falling as `L` grows. That is the running of the
coupling, the content excluded here. A Jensen bound on `vortexR` with a thick trial needs a
measure-preserving change of variables carrying the untwisted torus to the twisted one through a
non-central profile; the tree moves only central plaquette patterns
(`VortexStrong.zwP_coboundary`), so for `SU(N)` that bound is not available, while for `U(1)` the
abelian shift is exact and yields the classical cost above.

DERIVED (module-wide): `1 − cos φ` is `wilsonDensity` of `diag(e^{iφ}, e^{−iφ})` and the `U(1)`
plaquette cost; `π` the `SU(2)` centre angle (`dmat π = −1`); `2/π²` cited from
`Real.cos_le_one_sub_mul_cos_sq`; `1/2` from `Real.one_sub_sq_div_two_le_cos`; `5/96` from
`Real.cos_bound`; `3`, `4`, `6`, `¼ ln 3` are `VortexEntropy`'s; `8 = 4 · 2`, the `¼` of the entropy
against the `2` of `2θ²/π²`.

## What does not follow

* Only abelian (Cartan) profiles are bounded below. A non-abelian profile, rotating through
  non-commuting directions across the sheet, is not covered by `cellCost_ge`.
* No link field realizing a given closed profile on the lattice is constructed; the cost is that of
  the plaquette holonomies a section carries.
* No statement about `vortexR`, `FluxConfinedAt` or the bridge follows. Convergence of the surface
  sum at large `β` is the dilute-sheet side, the opposite of what the flux half needs
  (`VortexSheetFlux`).
-/

noncomputable section

namespace MassGap.ThickSheetCost

open Filter Topology Real

/-! ## 1. One section -/

/-- **The Wilson cost of a section** with plaquette angles `φ`. -/
def spreadCost {m : ℕ} (φ : Fin m → ℝ) : ℝ := ∑ i, (1 - Real.cos (φ i))

/-- **Spreading lower bound**: angles in `[−π, π]` with total `θ` cost at least `2θ²/(π² m)`.
Cited: `Real.cos_le_one_sub_mul_cos_sq`, `sq_sum_le_card_mul_sum_sq`. -/
theorem spreadCost_ge {m : ℕ} (hm : 0 < m) {θ : ℝ} {φ : Fin m → ℝ} (hsum : ∑ i, φ i = θ)
    (hπ : ∀ i, |φ i| ≤ π) : 2 * θ ^ 2 / (π ^ 2 * m) ≤ spreadCost φ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hpi : 0 < π ^ 2 := by positivity
  have hterm : ∀ i, 2 / π ^ 2 * φ i ^ 2 ≤ 1 - Real.cos (φ i) := fun i => by
    have := Real.cos_le_one_sub_mul_cos_sq (hπ i); linarith
  have h1 : 2 / π ^ 2 * ∑ i, φ i ^ 2 ≤ spreadCost φ := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hterm i
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := φ)
  rw [hsum, Finset.card_univ, Fintype.card_fin] at hcs
  have h2 : θ ^ 2 / m ≤ ∑ i, φ i ^ 2 := by rw [div_le_iff₀ hm']; linarith
  calc 2 * θ ^ 2 / (π ^ 2 * m) = 2 / π ^ 2 * (θ ^ 2 / m) := by field_simp
    _ ≤ 2 / π ^ 2 * ∑ i, φ i ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ spreadCost φ := h1

/-- **The even spread** costs at most `θ²/(2m)`. Cited: `Real.one_sub_sq_div_two_le_cos`. -/
theorem uniform_spreadCost_le {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    spreadCost (fun _ : Fin m => θ / m) ≤ θ ^ 2 / (2 * m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ / m)
  unfold spreadCost
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (m : ℝ) * (1 - Real.cos (θ / m)) ≤ m * ((θ / m) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hm'.le
    _ = θ ^ 2 / (2 * m) := by field_simp

/-! ## 2. The coarse cell -/

/-- **The cost of a coarse cell**: `m` sections of `m` plaquettes. -/
def cellCost {m : ℕ} (Φ : Fin m → Fin m → ℝ) : ℝ := ∑ s, spreadCost (Φ s)

/-- **Every abelian profile costs at least `2θ²/π²` per coarse cell, at every thickness.**
DERIVED: `2/π²` cited; the `m` sections cancel the `1/m` of `spreadCost_ge`. -/
theorem cellCost_ge {m : ℕ} (hm : 0 < m) {θ : ℝ} {Φ : Fin m → Fin m → ℝ}
    (hsum : ∀ s, ∑ i, Φ s i = θ) (hπ : ∀ s i, |Φ s i| ≤ π) : 2 * θ ^ 2 / π ^ 2 ≤ cellCost Φ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (Fin m))) =>
    spreadCost_ge hm (hsum s) (hπ s)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc 2 * θ ^ 2 / π ^ 2 = m * (2 * θ ^ 2 / (π ^ 2 * m)) := by field_simp
    _ ≤ cellCost Φ := h

/-- **The even profile costs at most `θ²/2` per coarse cell, at every thickness.** -/
theorem cellCost_uniform_le {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    cellCost (fun _ _ : Fin m => θ / m) ≤ θ ^ 2 / 2 := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  unfold cellCost
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (m : ℝ) * spreadCost (fun _ : Fin m => θ / m) ≤ m * (θ ^ 2 / (2 * m)) :=
        mul_le_mul_of_nonneg_left (uniform_spreadCost_le hm θ) hm'.le
    _ = θ ^ 2 / 2 := by field_simp

/-- The even profile's coarse cost is `m² (1 − cos(θ/m))`. -/
theorem cellCost_uniform_eq (m : ℕ) (θ : ℝ) :
    cellCost (fun _ _ : Fin m => θ / m) = (m : ℝ) ^ 2 * (1 - Real.cos (θ / m)) := by
  unfold cellCost spreadCost
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The even profile reaches the scale-invariant value `θ²/2`** as the sheet thickens.
Cited: `Real.cos_bound` (`5/96`). -/
theorem cellCost_uniform_tendsto (θ : ℝ) :
    Tendsto (fun m : ℕ => cellCost (fun _ _ : Fin m => θ / m)) atTop (𝓝 (θ ^ 2 / 2)) := by
  simp_rw [cellCost_uniform_eq]
  have hb : Tendsto (fun m : ℕ => θ ^ 4 * (5 / 96) / ((m : ℝ) ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop (⌈|θ|⌉₊ + 1)] with m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.le_add_left 1 _).trans hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hθ : |θ| ≤ m := by
    have h1 : |θ| ≤ (⌈|θ|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈|θ|⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.le_succ _).trans hm
    linarith
  have hθm : |θ / m| ≤ 1 := by
    rw [abs_div, abs_of_pos hm0, div_le_one hm0]; exact hθ
  have hc := Real.cos_bound hθm
  have hid : (m : ℝ) ^ 2 * (1 - Real.cos (θ / m)) - θ ^ 2 / 2
      = -((m : ℝ) ^ 2 * (Real.cos (θ / m) - (1 - (θ / m) ^ 2 / 2))) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, hid, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  have h4 : |θ / m| ^ 4 = θ ^ 4 / (m : ℝ) ^ 4 := by
    rw [(by decide : Even 4).pow_abs, div_pow]
  calc (m : ℝ) ^ 2 * |Real.cos (θ / m) - (1 - (θ / m) ^ 2 / 2)|
      ≤ (m : ℝ) ^ 2 * (|θ / m| ^ 4 * (5 / 96)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = θ ^ 4 * (5 / 96) / (m : ℝ) ^ 2 := by rw [h4]; field_simp

/-! ## 3. Against the entropy of closed sheets -/

/-- **Above `π² ln 3/(8θ²)` no abelian thickening beats the entropy**: the surface sum at the
per-cell cost `β · cellCost Φ` converges, at every thickness and for every admissible profile.
DERIVED: `8 = 4 · 2`; `¼ ln 3` the entropy density; `2/π²` cited. -/
theorem trial_summable {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ≠ 0) {Φ : Fin m → Fin m → ℝ}
    (hsum : ∀ s, ∑ i, Φ s i = θ) (hπ : ∀ s i, |Φ s i| ≤ π) {β : ℝ}
    (hβ : π ^ 2 * Real.log 3 / (8 * θ ^ 2) < β) :
    Summable (VortexEntropy.floorTerm (β * cellCost Φ)) := by
  rw [VortexEntropy.floorTerm_summable_iff]
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hpi : 0 < π ^ 2 := by positivity
  have hc := cellCost_ge hm hsum hπ
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβ
  have h1 : β * (2 * θ ^ 2 / π ^ 2) ≤ β * cellCost Φ := mul_le_mul_of_nonneg_left hc hβ0.le
  have h2 : 1 / 4 * Real.log 3 < β * (2 * θ ^ 2 / π ^ 2) := by
    rw [div_lt_iff₀ (by positivity)] at hβ
    rw [mul_div_assoc', lt_div_iff₀ hpi]
    nlinarith
  linarith

/-- **Below `ln 3/(2θ²)` the even thickening's surface sum diverges**, at every thickness.
DERIVED: `2` from `θ²/2`; `¼ ln 3` the entropy density. -/
theorem uniform_trial_not_summable {m : ℕ} (hm : 0 < m) (θ : ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β * (θ ^ 2 / 2) ≤ 1 / 4 * Real.log 3) :
    ¬ Summable (VortexEntropy.floorTerm (β * cellCost (fun _ _ : Fin m => θ / m))) :=
  VortexEntropy.not_summable_of_le
    ((mul_le_mul_of_nonneg_left (cellCost_uniform_le hm θ) hβ0).trans hβ)

/-! ## 4. The same sections in `SU(2)` and in `U(1)` -/

open MassGap.SU2DiskLaw (dmat)

/-- `wilsonDensity (diag(e^{it}, e^{−it})) = 1 − cos t`. -/
theorem wilsonDensity_dmat (t : ℝ) : WilsonAction.wilsonDensity (dmat t) = 1 - Real.cos t := by
  have h := SU2DiskLaw.suTau_dmat t
  unfold ChainCoarseSeed.suTau at h
  linarith

/-- The diagonal elements form a one-parameter subgroup. -/
theorem dmat_add (a b : ℝ) : dmat (a + b) = dmat a * dmat b := by
  apply Subtype.ext
  rw [Submonoid.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, SU2DiskLaw.qmat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;>
    apply Complex.ext <;> simp <;> ring

/-- **At the angle `π` the diagonal element is the centre element `−1`.** -/
theorem dmat_pi : dmat π = TwistedTraceBound.negOne := by
  apply Subtype.ext
  rw [TwistedTraceBound.coe_negOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat, SU2DiskLaw.qmat]

/-- The ordered product of the diagonal elements of a section is the diagonal element of the total. -/
theorem prod_dmat : ∀ {m : ℕ} (φ : Fin m → ℝ), (List.ofFn fun i => dmat (φ i)).prod = dmat (∑ i, φ i)
  | 0, φ => by simp [SU2DiskLaw.dmat_zero]
  | m + 1, φ => by
    rw [List.ofFn_succ, List.prod_cons, prod_dmat (fun i => φ i.succ), Fin.sum_univ_succ, dmat_add]

/-- **An `SU(2)` section**: angles with total `π` give plaquette holonomies multiplying to the centre
element `−1`, at Wilson cost `spreadCost φ`. -/
theorem su2_section {m : ℕ} (φ : Fin m → ℝ) (hsum : ∑ i, φ i = π) :
    (List.ofFn fun i => dmat (φ i)).prod = TwistedTraceBound.negOne
      ∧ ∑ i, WilsonAction.wilsonDensity (dmat (φ i)) = spreadCost φ := by
  refine ⟨by rw [prod_dmat, hsum, dmat_pi], ?_⟩
  unfold spreadCost
  exact Finset.sum_congr rfl fun i _ => wilsonDensity_dmat (φ i)

/-- **A `U(1)` section**: the same angles give phases multiplying to `e^{iθ}`, `−1` at `θ = π`,
at the same cost `spreadCost φ`. -/
theorem u1_section {m : ℕ} (φ : Fin m → ℝ) :
    ∏ i, Complex.exp (φ i * Complex.I) = Complex.exp ((∑ i, φ i : ℝ) * Complex.I)
      ∧ ∑ i, (1 - (Complex.exp (φ i * Complex.I)).re) = spreadCost φ := by
  refine ⟨?_, ?_⟩
  · rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · unfold spreadCost
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.exp_ofReal_mul_I_re]

/-- The `U(1)` section of total `π` multiplies to `−1`. -/
theorem u1_section_pi {m : ℕ} (φ : Fin m → ℝ) (hsum : ∑ i, φ i = π) :
    ∏ i, Complex.exp (φ i * Complex.I) = -1 := by
  rw [(u1_section φ).1, hsum, Complex.exp_pi_mul_I]

#print axioms spreadCost_ge
#print axioms uniform_spreadCost_le
#print axioms cellCost_ge
#print axioms cellCost_uniform_le
#print axioms cellCost_uniform_eq
#print axioms cellCost_uniform_tendsto
#print axioms trial_summable
#print axioms uniform_trial_not_summable
#print axioms wilsonDensity_dmat
#print axioms dmat_add
#print axioms dmat_pi
#print axioms prod_dmat
#print axioms su2_section
#print axioms u1_section
#print axioms u1_section_pi

end MassGap.ThickSheetCost

end
