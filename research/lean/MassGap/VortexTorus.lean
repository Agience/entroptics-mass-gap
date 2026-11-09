import Mathlib
import MassGap.VortexCondense

/-!
# MassGap.VortexTorus — the zoom theorems of `VortexCondense` on the `SU(2)` corner tori

`VortexCondense.floor_of_condensation` and `VortexCondense.matchAt_uniform_of_condensation` take an
abstract Wilson loop `W`, electric weight `e` and cross-section `La × Lb`. This module feeds them the
lattice objects: at zoom `j` (coupling `β j`, spacing `a j`) the box family is the corner-step torus
`Lc (nK j K) i` of `GapSideVortexRect`, the loop is `VortexCondense.wloopR` in the plane `(i, ν)`,
the electric weight is `1 − zR`, and condensation is a statement about `vortexR` of those tori.
`a j` is an input; nothing here relates it to `β j`, so the physical-unit uniformity is as strong as
that identification.

## The tiling condition on the corner tori (`Adm`)

`Lc n i` has extent `n` along `i` (`Lc_self`) and `n` or `2n` along every other direction, a multiple
of `n` (`dvd_Lc`, `le_Lc`).

* `adm_Lc_iff`: along a family `Lc (nK K) i`, "every rectangle `m × k` with `m, k ≥ 1` is eventually
  admissible in the plane `(i, b)`" holds exactly when every `m ≥ 1` eventually divides `nK K` and is
  below it. So `Adm` on these tori is a condition on the side sequence and on nothing else.
* `size_factorial`: the sides `nF K = 2 (K+1)!` satisfy it; they are even and at least `2`, the
  conditions under which `zR ≤ 1` is proved (`VortexCondense.zR_Lc_le_one`). So `Adm` is discharged
  for the factorial corner-torus family.
* `not_adm_Lc_doubling`: the doubling sides `2^{K+1}` do not satisfy it (`3` never divides a power of
  `2`; `not_adm_Lc_doubling_three`: the `3 × 1` rectangle is admissible at no `K`). On a doubling
  family only rectangles with power-of-two sides tile the cross-section, so the all-rectangle
  hypothesis `hadm` of `VortexCondense.floor_of_condensation` fails there (power-of-two squares would
  suffice for `HasTension` along a subsequence, but the abstract theorem is not stated that way). The
  discharge above uses a family cofinal in divisibility instead.

## The zoom on the torus

* `floor_of_vortexR_condensation`: for side families `nK j K` (even, at least `2`, eventually divisible
  by and above every `m ≥ 1` at each zoom), the sharpened Tomboulis–Yaffe input `TYBoundR` on every
  torus,
  condensation of `vortexR (Lc (nK j K) i) i ν (β j)` at the lattice rate `ρ₀ (a j)²` per unit area of
  the plane, the thermodynamic limit of `wloopR` and `HasTension` of the limit give
  `NoTransition.Floor (σlat / a²)`. The electric-weight non-negativity and the passage from `vortexR`
  to `1 − zR` are proved (`vortexR_Lc_nonneg`, `one_sub_zR_le_vortexR`); `Adm` comes from `adm_Lc_iff`.
* `floor_of_vortexR_condensation_factorial`: the same on the factorial family, with no size
  hypothesis left.
* `matchAt_uniform_of_vortexR_condensation`: with the count hypothesis of `MatchAt.matchAt_of_count`
  at cost `(σlat j / a j²) f L²`, one `L₀` gives `MatchAt` at every zoom and every `L ≥ L₀`.

## What stays a hypothesis

Stated on the lattice objects, not proved: `TYBoundR` (a prefactor-free strengthening of the
Tomboulis–Yaffe inequality for `wloopR` against `1 − zR`, on all tiling rectangles; the published
form has prefactor `2` and needs power-of-two ratios, `TomboulisYaffe.tyTwo_of_chessboard`), condensation
of `vortexR` uniformly in the zoom in physical units, the limit `K → ∞` of `wloopR`, `HasTension` of
that limit, and the chunk count. `condenses_vortexR_zero`: at `β = 0` the sheet ratio is `1`, so
`vortexR = 0` and the condensation hypothesis holds at every rate; it is satisfiable on these objects.
This witnesses that hypothesis alone (at `β = 0` the loop of a non-wrapping rectangle is expected to
be `0`, so `HasTension` would fail there; no declaration proves this); no declaration exhibits the
hypotheses jointly. At weak coupling it is the open statement of `VortexCondense`.

DERIVED (module-wide): `1` the unit loop side; `2` the factor of the even sides (`zR_Lc_le_one` needs
`n` even, `n ≥ 2`); `K + 1` the shift that makes `(K+1)! ≥ 1`; `3` the least side not a power of `2`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.VortexTorus

open Filter Topology MeasureTheory
open MassGap.MatchAt MassGap.VortexCondense MassGap.GapSideVortexRect

/-! ## 1. The cross-sections of the corner tori -/

/-- **The corner torus has side `n` along its transfer direction.** -/
theorem Lc_self (n : ℕ) (i : Fin 4) : Lc n i i = n := by
  show 2 ^ (CentreSectorSeed.pathV i i) * n = n
  rw [CentreSectorSeed.pathV_self, pow_zero, one_mul]

/-- **Every extent of the corner torus is a multiple of `n`.** -/
theorem dvd_Lc (n : ℕ) (i b : Fin 4) : n ∣ Lc n i b := by
  show n ∣ 2 ^ (CentreSectorSeed.pathV i b) * n
  exact dvd_mul_left n _

theorem le_Lc (n : ℕ) (i b : Fin 4) : n ≤ Lc n i b := by
  show n ≤ 2 ^ (CentreSectorSeed.pathV i b) * n
  calc n = 1 * n := (one_mul n).symm
    _ ≤ 2 ^ (CentreSectorSeed.pathV i b) * n := Nat.mul_le_mul_right n Nat.one_le_two_pow

/-- **`Adm` on a corner-torus family is a condition on the sides.** Every rectangle `m × k`
(`m, k ≥ 1`) is eventually admissible in the plane `(i, b)` of `Lc (nK K) i` iff every `m ≥ 1`
eventually divides `nK K` and is below it. -/
theorem adm_Lc_iff (nK : ℕ → ℕ) (i b : Fin 4) :
    (∀ m k, 1 ≤ m → 1 ≤ k → ∀ᶠ K in atTop, Adm (Lc (nK K) i i) (Lc (nK K) i b) m k) ↔
      ∀ m, 1 ≤ m → ∀ᶠ K in atTop, m ∣ nK K ∧ m < nK K := by
  constructor
  · intro h m hm
    filter_upwards [h m 1 hm le_rfl] with K hK
    rw [Adm, Lc_self] at hK
    exact ⟨hK.1, hK.2.2.1⟩
  · intro h m k hm hk
    filter_upwards [h m hm, h k hk] with K hmK hkK
    rw [Adm, Lc_self]
    exact ⟨hmK.1, hkK.1.trans (dvd_Lc _ i b), hmK.2, hkK.2.trans_le (le_Lc _ i b)⟩

/-- **The factorial sides** `2 (K+1)!`. -/
abbrev nF (K : ℕ) : ℕ := 2 * Nat.factorial (K + 1)

theorem two_le_nF (K : ℕ) : 2 ≤ nF K := by
  have := Nat.factorial_pos (K + 1)
  show 2 ≤ 2 * Nat.factorial (K + 1)
  omega

theorem even_nF (K : ℕ) : Even (nF K) := even_two_mul _

/-- **The factorial sides tile every rectangle eventually.** -/
theorem size_factorial : ∀ m, 1 ≤ m → ∀ᶠ K in atTop, m ∣ nF K ∧ m < nF K := by
  intro m hm
  filter_upwards [eventually_ge_atTop m] with K hK
  have hf := Nat.self_le_factorial (K + 1)
  refine ⟨(Nat.dvd_factorial hm (by omega)).mul_left 2, ?_⟩
  show m < 2 * Nat.factorial (K + 1)
  omega

/-- **`Adm` holds eventually on the factorial corner tori**, every plane `(i, b)`. -/
theorem adm_Lc_factorial (i b : Fin 4) :
    ∀ m k, 1 ≤ m → 1 ≤ k → ∀ᶠ K in atTop, Adm (Lc (nF K) i i) (Lc (nF K) i b) m k :=
  (adm_Lc_iff nF i b).2 size_factorial

/-- **The doubling corner tori do not tile every rectangle**: along `Lc (2^{K+1}) i` the `3 × 1`
rectangle is never admissible. -/
theorem not_adm_Lc_doubling (i b : Fin 4) :
    ¬ ∀ m k, 1 ≤ m → 1 ≤ k → ∀ᶠ K in atTop,
      Adm (Lc (2 ^ (K + 1)) i i) (Lc (2 ^ (K + 1)) i b) m k := by
  intro h
  have h2 := (adm_Lc_iff (fun K => 2 ^ (K + 1)) i b).1 h
  obtain ⟨K, hK⟩ := (h2 3 (by norm_num)).exists
  have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hK.1
  omega

/-- **The `3 × 1` rectangle is admissible on no doubling corner torus.** -/
theorem not_adm_Lc_doubling_three (i b : Fin 4) (K : ℕ) :
    ¬ Adm (Lc (2 ^ (K + 1)) i i) (Lc (2 ^ (K + 1)) i b) 3 1 := by
  intro h
  rw [Adm, Lc_self] at h
  have h3 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h.1
  omega

/-! ## 2. Condensation on the torus objects -/

/-- **At `β = 0` the torus vortex free energy vanishes**, so it condenses at every rate. -/
theorem condenses_vortexR_zero (nK : ℕ → ℕ) (i b : Fin 4) (A : ℕ → ℝ) (ρ : ℝ) :
    Condenses (fun K => vortexR (Lc (nK K) i) i b 0) A ρ := fun _ _ =>
  Eventually.of_forall fun K => by
    simp only [vortexR, zR_zero, Real.log_one, neg_zero]
    exact (Real.exp_pos _).le

/-! ## 3. The zoom on the corner tori -/

/-- **Condensation of the torus vortex free energy gives the floor.** At zoom `j` the boxes are
`Lc (nK j K) i` at coupling `β j`; the sharpened Tomboulis–Yaffe input `TYBoundR` on every torus, condensation
of `vortexR` at the lattice rate `ρ₀ (a j)²` per unit area of the plane `(i, ν)`, the limit of
`wloopR` and `HasTension` give `Floor (σlat / a²)`. The sides enter only through `hsize`. -/
theorem floor_of_vortexR_condensation {nK : ℕ → ℕ → ℕ} {β a σlat : ℕ → ℝ} {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j) (hβ : ∀ j, 0 ≤ β j)
    (hn : ∀ j K, 2 ≤ nK j K) (he : ∀ j K, Even (nK j K))
    (hsize : ∀ j m, 1 ≤ m → ∀ᶠ K in atTop, m ∣ nK j K ∧ m < nK j K)
    (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (o : ∀ j K, RectWilson.RSite (Lc (nK j K) i))
    (hTY : ∀ j K, TYBoundR (Lc (nK j K) i) i ν.1 (o j K) (β j))
    (hcond : ∀ j, Condenses (fun K => vortexR (Lc (nK j K) i) i ν.1 (β j))
      (fun K => ((Lc (nK j K) i i : ℕ) : ℝ) * ((Lc (nK j K) i ν.1 : ℕ) : ℝ)) (ρ₀ * a j ^ 2))
    {Winf : ℕ → ℕ → ℕ → ℝ}
    (hlim : ∀ j m k, Tendsto (fun K => wloopR (Lc (nK j K) i) i ν.1 m k (o j K) (β j)) atTop
      (𝓝 (Winf j m k)))
    (hT : ∀ j, HasTension (Winf j) (σlat j)) :
    NoTransition.Floor (fun j => σlat j / a j ^ 2) :=
  floor_of_condensation (W := fun j K m k => wloopR (Lc (nK j K) i) i ν.1 m k (o j K) (β j))
    (e := fun j K => 1 - zR (Lc (nK j K) i) i ν.1 (β j))
    (La := fun j K => Lc (nK j K) i i) (Lb := fun j K => Lc (nK j K) i ν.1)
    hρ₀ ha hTY (fun j K => (vortexR_Lc_nonneg (hβ j) (hn j K) (he j K) i ν).2)
    (fun j => (hcond j).mono
      (Eventually.of_forall fun K => one_sub_zR_le_vortexR (Lc (nK j K) i) i ν.1 (β j)))
    (fun j => (adm_Lc_iff (nK j) i ν.1).2 (hsize j)) hlim hT

/-- **The floor on the factorial corner tori**: no size hypothesis remains. -/
theorem floor_of_vortexR_condensation_factorial {β a σlat : ℕ → ℝ} {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j) (hβ : ∀ j, 0 ≤ β j)
    (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (o : ∀ _ : ℕ, ∀ K, RectWilson.RSite (Lc (nF K) i))
    (hTY : ∀ j K, TYBoundR (Lc (nF K) i) i ν.1 (o j K) (β j))
    (hcond : ∀ j, Condenses (fun K => vortexR (Lc (nF K) i) i ν.1 (β j))
      (fun K => ((Lc (nF K) i i : ℕ) : ℝ) * ((Lc (nF K) i ν.1 : ℕ) : ℝ)) (ρ₀ * a j ^ 2))
    {Winf : ℕ → ℕ → ℕ → ℝ}
    (hlim : ∀ j m k, Tendsto (fun K => wloopR (Lc (nF K) i) i ν.1 m k (o j K) (β j)) atTop
      (𝓝 (Winf j m k)))
    (hT : ∀ j, HasTension (Winf j) (σlat j)) :
    NoTransition.Floor (fun j => σlat j / a j ^ 2) :=
  floor_of_vortexR_condensation (nK := fun _ K => nF K) hρ₀ ha hβ (fun _ K => two_le_nF K)
    (fun _ K => even_nF K) (fun _ => size_factorial) i ν o hTY hcond hlim hT

/-- **Torus condensation, the count, and one length for every zoom.** On the factorial corner tori:
the hypotheses of `floor_of_vortexR_condensation_factorial` and the count of
`MatchAt.matchAt_of_count` at cost `(σlat j / a j²) f L²` give one `L₀` with `MatchAt` at every zoom
and every `L ≥ L₀`. -/
theorem matchAt_uniform_of_vortexR_condensation {β a σlat : ℕ → ℝ} {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j) (hβ : ∀ j, 0 ≤ β j)
    (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (o : ∀ _ : ℕ, ∀ K, RectWilson.RSite (Lc (nF K) i))
    (hTY : ∀ j K, TYBoundR (Lc (nF K) i) i ν.1 (o j K) (β j))
    (hcond : ∀ j, Condenses (fun K => vortexR (Lc (nF K) i) i ν.1 (β j))
      (fun K => ((Lc (nF K) i i : ℕ) : ℝ) * ((Lc (nF K) i ν.1 : ℕ) : ℝ)) (ρ₀ * a j ^ 2))
    {Winf : ℕ → ℕ → ℕ → ℝ}
    (hlim : ∀ j m k, Tendsto (fun K => wloopR (Lc (nF K) i) i ν.1 m k (o j K) (β j)) atTop
      (𝓝 (Winf j m k)))
    (hT : ∀ j, HasTension (Winf j) (σlat j))
    {V : ℕ → ℝ → Type*} [∀ j L, Fintype (V j L)] [∀ j L, DecidableEq (V j L)]
    (w : ∀ j L, Finset (V j L) → ℝ) {z f κ : ℝ} (hz : 0 ≤ z) (hf : 0 < f) (hκ : 0 ≤ κ)
    (hw0 : ∀ j L, w j L ∅ = 0)
    (hcount : ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(σlat j / a j ^ 2 * f * L ^ 2))) ^ n) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ := by
  have hfl := floor_of_vortexR_condensation_factorial hρ₀ ha hβ i ν o hTY hcond hlim hT
  obtain ⟨L₀, hL₀, h⟩ := NoTransitionFlow.uniform_length_of_floor (κ := κ) hz hf hfl
  exact ⟨L₀, hL₀, fun j L hL => matchAt_of_count (hw0 j L) hz hκ (hcount j L) (h j L hL)⟩

#print axioms Lc_self
#print axioms dvd_Lc
#print axioms le_Lc
#print axioms adm_Lc_iff
#print axioms two_le_nF
#print axioms even_nF
#print axioms size_factorial
#print axioms adm_Lc_factorial
#print axioms not_adm_Lc_doubling
#print axioms condenses_vortexR_zero
#print axioms floor_of_vortexR_condensation
#print axioms floor_of_vortexR_condensation_factorial
#print axioms matchAt_uniform_of_vortexR_condensation

end MassGap.VortexTorus
