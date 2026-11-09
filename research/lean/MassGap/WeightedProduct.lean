import Mathlib
import MassGap.WeightedBox

noncomputable section

/-!
# MassGap.WeightedProduct — product weights on the torus links, their pair weights and multiplicities

`WeightedBox.clay_continuum_of_weightedBox` takes a `WeightedFamilyAt` at every large torus. This
module builds one from two one-dimensional profiles: `f` for the coordinates of a link transverse to
it and `g` for its own direction, both zero from `n` on. The weight of the link `(μ, x)` in the patch
at corner `k` is `∏_ν p_ν((x − k)_ν)` with `p_μ = g`, `p_ν = f` off `μ`.

## What it gives

1. **One dimension.** `corr u v d = Σ_t u(t) v(t + d)` on the circle `Fin (M + 1)`; with `2n ≤ M + 1`
   it is the finite sum at `d = 0`, `d = 1` (`corr_zero`, `corr_one`), it satisfies
   `corr u v (−d) = corr v u d` (`corr_neg`), and it is bounded by any `U ≥ 0` bounding the finite
   forward and backward correlations (`corr_le`, and `corr_le_nz` off `d = 0`).
-/

namespace MassGap.WeightedProduct

open MassGap MassGap.HeatBath MassGap.KnabeCriterion

/-! ## 1. One dimension -/

section OneDim

variable {M : ℕ}

/-- The circular correlation `Σ_t u(t) v(t + d)` on `Fin (M + 1)`.

DERIVED: `1` is the successor writing the extent. -/
def corr (u v : ℕ → ℝ) (d : Fin (M + 1)) : ℝ :=
  ∑ t : Fin (M + 1), u (t : ℕ) * v ((t + d : Fin (M + 1)) : ℕ)

/-- The correlation over the first `n` sites, for `u` zero from `n` on.

DERIVED: `1` is the successor writing the extent; `0` is the profile outside the box. -/
theorem corr_eq_range {n : ℕ} (hnL : n ≤ M + 1) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0)
    (d : Fin (M + 1)) :
    corr u v d = ∑ t ∈ Finset.range n, u t * v ((t + (d : ℕ)) % (M + 1)) := by
  unfold corr
  have h1 : ∑ t : Fin (M + 1), u (t : ℕ) * v ((t + d : Fin (M + 1)) : ℕ)
      = ∑ t : Fin (M + 1), (fun s : ℕ => u s * v ((s + (d : ℕ)) % (M + 1))) (t : ℕ) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Fin.val_add]
  rw [h1, Fin.sum_univ_eq_sum_range (fun s : ℕ => u s * v ((s + (d : ℕ)) % (M + 1))) (M + 1)]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hnL) (fun t ht htn => ?_)
  rw [Finset.mem_range] at htn
  rw [hu t (by omega), zero_mul]

#print axioms corr_eq_range

/-- `corr u v 0 = Σ_{t < n} u(t) v(t)`.

DERIVED: `0` is the zero shift. -/
theorem corr_zero {n : ℕ} (hnL : n ≤ M + 1) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0) :
    corr u v (0 : Fin (M + 1)) = ∑ t ∈ Finset.range n, u t * v t := by
  rw [corr_eq_range hnL u v hu]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [Fin.val_zero, add_zero, Nat.mod_eq_of_lt (by omega)]

#print axioms corr_zero

/-- `corr u v 1 = Σ_{t < n} u(t) v(t + 1)` at `2n ≤ M + 1`.

DERIVED: `1` is the unit shift; `2` the two windows fitting in the circle. -/
theorem corr_one {n : ℕ} (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (u v : ℕ → ℝ)
    (hu : ∀ t, n ≤ t → u t = 0) :
    corr u v (1 : Fin (M + 1)) = ∑ t ∈ Finset.range n, u t * v (t + 1) := by
  rw [corr_eq_range (by omega) u v hu]
  have h1 : ((1 : Fin (M + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 1 by omega)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [h1, Nat.mod_eq_of_lt (by omega)]

#print axioms corr_one

/-- `corr u v (−d) = corr v u d` (reindex `t ↦ t + d`).

DERIVED: no numeral beyond the extent's successor. -/
theorem corr_neg (u v : ℕ → ℝ) (d : Fin (M + 1)) : corr u v (-d) = corr v u d := by
  unfold corr
  rw [← Equiv.sum_comp (Equiv.addRight d)]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Equiv.coe_addRight, add_neg_cancel_right]
  ring

#print axioms corr_neg

/-- **The correlation is bounded by its finite forward and backward correlations.** For `u`, `v`
zero from `n` on, `2n ≤ M + 1`, `0 ≤ U`, every forward correlation `Σ_{t<n} u(t) v(t + D)`
(`D < n`) and every backward one `Σ_{t<n} u(t + r) v(t)` (`1 ≤ r < n`) at most `U`: every
`corr u v d ≤ U`. With `D ≥ 1` in the forward hypothesis the bound holds for every `d ≠ 0`
(`corr_le_nz`).

DERIVED: `2` is the two windows fitting in the circle; `1` the least backward shift; `0` the
profile outside the box. -/
theorem corr_le_aux {n : ℕ} (hL : 2 * n ≤ M + 1) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0)
    (hv : ∀ t, n ≤ t → v t = 0) {U : ℝ} (hU : 0 ≤ U) (d : Fin (M + 1))
    (hfw : (d : ℕ) < n → ∑ t ∈ Finset.range n, u t * v (t + (d : ℕ)) ≤ U)
    (hbw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, u (t + r) * v t ≤ U) :
    corr u v d ≤ U := by
  rw [corr_eq_range (by omega) u v hu]
  set D := (d : ℕ) with hD
  have hDlt : D < M + 1 := d.isLt
  by_cases h1 : D < n
  · have e : ∑ t ∈ Finset.range n, u t * v ((t + D) % (M + 1))
        = ∑ t ∈ Finset.range n, u t * v (t + D) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_range] at ht
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [e]; exact hfw h1
  by_cases h2 : D + n ≤ M + 1
  · have e : ∑ t ∈ Finset.range n, u t * v ((t + D) % (M + 1)) = 0 := by
      refine Finset.sum_eq_zero (fun t ht => ?_)
      rw [Finset.mem_range] at ht
      rw [Nat.mod_eq_of_lt (by omega), hv (t + D) (by omega), mul_zero]
    rw [e]; exact hU
  · -- backward: r = M + 1 − D with 1 ≤ r < n
    set r := M + 1 - D with hr
    have hr1 : 1 ≤ r := by omega
    have hrn : r < n := by omega
    have e1 : ∑ t ∈ Finset.range n, u t * v ((t + D) % (M + 1))
        = ∑ t ∈ Finset.Ico r n, u t * v (t - r) := by
      rw [← Finset.sum_range_add_sum_Ico _ hrn.le]
      have z : ∑ t ∈ Finset.range r, u t * v ((t + D) % (M + 1)) = 0 := by
        refine Finset.sum_eq_zero (fun t ht => ?_)
        rw [Finset.mem_range] at ht
        rw [Nat.mod_eq_of_lt (by omega), hv (t + D) (by omega), mul_zero]
      rw [z, zero_add]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_Ico] at ht
      have : (t + D) % (M + 1) = t - r := by
        rw [show t + D = (t - r) + (M + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [this]
    have e2 : ∑ t ∈ Finset.Ico r n, u t * v (t - r) = ∑ s ∈ Finset.range n, u (s + r) * v s := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [← Finset.sum_range_add_sum_Ico (fun s => u (s + r) * v s) (show n - r ≤ n by omega)]
      have z : ∑ s ∈ Finset.Ico (n - r) n, u (s + r) * v s = 0 := by
        refine Finset.sum_eq_zero (fun s hs => ?_)
        rw [Finset.mem_Ico] at hs
        rw [hu (s + r) (by omega), zero_mul]
      rw [z, add_zero]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [show r + s - r = s by omega, add_comm r s]
    rw [e1, e2]
    exact hbw r hr1 hrn

#print axioms corr_le_aux

theorem corr_le {n : ℕ} (hL : 2 * n ≤ M + 1) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0)
    (hv : ∀ t, n ≤ t → v t = 0) {U : ℝ} (hU : 0 ≤ U)
    (hfw : ∀ D, D < n → ∑ t ∈ Finset.range n, u t * v (t + D) ≤ U)
    (hbw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, u (t + r) * v t ≤ U) (d : Fin (M + 1)) :
    corr u v d ≤ U :=
  corr_le_aux hL u v hu hv hU d (hfw _) hbw

#print axioms corr_le

theorem corr_le_nz {n : ℕ} (hL : 2 * n ≤ M + 1) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0)
    (hv : ∀ t, n ≤ t → v t = 0) {U : ℝ} (hU : 0 ≤ U)
    (hfw : ∀ D, 1 ≤ D → D < n → ∑ t ∈ Finset.range n, u t * v (t + D) ≤ U)
    (hbw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, u (t + r) * v t ≤ U) (d : Fin (M + 1))
    (hd : d ≠ 0) : corr u v d ≤ U := by
  refine corr_le_aux hL u v hu hv hU d (fun h => hfw _ ?_ h) hbw
  rcases Nat.eq_zero_or_pos (d : ℕ) with h0 | h0
  · exact absurd (Fin.ext h0) hd
  · exact h0

#print axioms corr_le_nz

/-- A correlation of non-negative profiles is non-negative.

DERIVED: `0` is the sign of the profiles. -/
theorem corr_nonneg (u v : ℕ → ℝ) (hu : ∀ t, 0 ≤ u t) (hv : ∀ t, 0 ≤ v t) (d : Fin (M + 1)) :
    0 ≤ corr u v d :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hu _) (hv _))

#print axioms corr_nonneg

end OneDim

/-! ## 2. Product weights on the torus links -/

section Product

variable {M : ℕ}

/-- The profile of coordinate `ν` for a link in direction `μ`: `g` along `μ`, `f` across.

DERIVED: no numeral. -/
def pf (f g : ℕ → ℝ) (μ ν : Fin 4) : ℕ → ℝ := if ν = μ then g else f

/-- **The product weight** of the link `l` in the patch at corner `k`:
`∏_ν pf (l.1) ν ((l.2 − k) ν)`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def prodC (f g : ℕ → ℝ) (k : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ℝ :=
  ∏ ν, pf f g l.1 ν (((l.2 - k) ν : Fin (M + 1)) : ℕ)

/-- **The pair weight of product weights factorises**:
`pairWeight (prodC f g) l l' = ∏_ν corr (pf l.1 ν) (pf l'.1 ν) ((l'.2 − l.2) ν)` (reindex the corners
by `k ↦ l.2 − k`, `Fintype.prod_sum`).

DERIVED: `4` is the spacetime dimension. -/
theorem pairWeight_prodC (f g : ℕ → ℝ) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    pairWeight (prodC (M := M) f g) l l'
      = ∏ ν, corr (pf f g l.1 ν) (pf f g l'.1 ν) ((l'.2 - l.2) ν) := by
  unfold pairWeight prodC
  have h1 : ∀ k : WilsonHypercubic.Site 4 (M + 1),
      (∏ ν, pf f g l.1 ν (((l.2 - k) ν : Fin (M + 1)) : ℕ))
        * (∏ ν, pf f g l'.1 ν (((l'.2 - k) ν : Fin (M + 1)) : ℕ))
      = ∏ ν, (pf f g l.1 ν (((l.2 - k) ν : Fin (M + 1)) : ℕ)
          * pf f g l'.1 ν (((l'.2 - k) ν : Fin (M + 1)) : ℕ)) := fun k =>
    (Finset.prod_mul_distrib).symm
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  rw [← Equiv.sum_comp (Equiv.subLeft l.2)]
  have h2 : ∀ v : WilsonHypercubic.Site 4 (M + 1),
      (∏ ν, (pf f g l.1 ν (((l.2 - Equiv.subLeft l.2 v) ν : Fin (M + 1)) : ℕ)
          * pf f g l'.1 ν (((l'.2 - Equiv.subLeft l.2 v) ν : Fin (M + 1)) : ℕ)))
      = ∏ ν, (fun (ν : Fin 4) (t : Fin (M + 1)) => pf f g l.1 ν (t : ℕ)
          * pf f g l'.1 ν ((t + (l'.2 - l.2) ν : Fin (M + 1)) : ℕ)) ν (v ν) := by
    intro v
    refine Finset.prod_congr rfl (fun ν _ => ?_)
    simp only [Equiv.subLeft_apply, Pi.sub_apply]
    congr 3
    · abel
    · abel
  rw [Finset.sum_congr rfl (fun v _ => h2 v)]
  exact (Fintype.prod_sum (fun (ν : Fin 4) (t : Fin (M + 1)) => pf f g l.1 ν (t : ℕ)
    * pf f g l'.1 ν ((t + (l'.2 - l.2) ν : Fin (M + 1)) : ℕ))).symm

#print axioms pairWeight_prodC

/-- **The cover weight of product weights**: `Σ_k prodC k l = ∏_ν Σ_t pf (l.1) ν t` (over the circle).

DERIVED: `4` is the spacetime dimension. -/
theorem cover_prodC (f g : ℕ → ℝ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ k, prodC (M := M) f g k l = ∏ ν, ∑ t : Fin (M + 1), pf f g l.1 ν (t : ℕ) := by
  unfold prodC
  rw [← Equiv.sum_comp (Equiv.subLeft l.2)]
  have h2 : ∀ v : WilsonHypercubic.Site 4 (M + 1),
      (∏ ν, pf f g l.1 ν (((l.2 - Equiv.subLeft l.2 v) ν : Fin (M + 1)) : ℕ))
      = ∏ ν, (fun (ν : Fin 4) (t : Fin (M + 1)) => pf f g l.1 ν (t : ℕ)) ν (v ν) := by
    intro v
    refine Finset.prod_congr rfl (fun ν _ => ?_)
    simp only [Equiv.subLeft_apply, Pi.sub_apply, sub_sub_cancel]
  rw [Finset.sum_congr rfl (fun v _ => h2 v)]
  exact (Fintype.prod_sum (fun (ν : Fin 4) (t : Fin (M + 1)) => pf f g l.1 ν (t : ℕ))).symm

#print axioms cover_prodC

/-- A circle sum of a profile zero from `n` on is its finite sum.

DERIVED: `1` is the successor writing the extent; `0` the profile outside the box. -/
theorem sum_circle {n : ℕ} (hnL : n ≤ M + 1) (u : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0) :
    ∑ t : Fin (M + 1), u (t : ℕ) = ∑ t ∈ Finset.range n, u t := by
  rw [Fin.sum_univ_eq_sum_range u (M + 1)]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hnL) (fun t ht htn => ?_)
  rw [Finset.mem_range] at htn
  exact hu t (by omega)

#print axioms sum_circle

/-- `∏_{ν : Fin 4} (if ν = μ then A else B) = A · B³`.

DERIVED: `4` is the spacetime dimension; `3` the other directions. -/
theorem prod_ite_four (μ : Fin 4) (A B : ℝ) :
    ∏ ν : Fin 4, (if ν = μ then A else B) = A * B ^ 3 := by
  fin_cases μ <;> simp [Fin.prod_univ_four] <;> ring

#print axioms prod_ite_four

end Product

/-! ## 3. Links of a common plaquette -/

section Partners

variable {M : ℕ}

/-- `shift α s = s + e_α`.

DERIVED: `1` is the unit step. -/
theorem shift_eq (α : Fin 4) (s : WilsonHypercubic.Site 4 (M + 1)) :
    WilsonHypercubic.shift α s = s + Pi.single α 1 := by
  funext κ
  simp only [WilsonHypercubic.shift, Function.update_apply, Pi.add_apply, Pi.single_apply]
  split_ifs with h
  · rw [h]
  · rw [add_zero]

#print axioms shift_eq

/-- **Links of a common plaquette, by displacement.** Two distinct links sharing a plaquette (of the
ordered-pair lattice, diagonal plaquettes included) either have the same direction and base sites
one unit step apart, `δ = ±e_ρ`, or different directions `μ = l.1`, `ν = l'.1` and
`δ ∈ {0, e_μ, −e_ν, e_μ − e_ν}`, `δ = l'.2 − l.2`.

DERIVED: `4` is the spacetime dimension; `1` the unit step; `0` the zero displacement. -/
theorem share_cases {l l' : WilsonHypercubic.Link 4 (M + 1)} (h : SharePlaq (bdT M) l l')
    (hne : l ≠ l') :
    (l'.1 = l.1 ∧ ∃ ρ : Fin 4, l'.2 - l.2 = Pi.single ρ 1 ∨ l'.2 - l.2 = -Pi.single ρ 1) ∨
    (l'.1 ≠ l.1 ∧ (l'.2 - l.2 = 0 ∨ l'.2 - l.2 = Pi.single l.1 1 ∨ l'.2 - l.2 = -Pi.single l'.1 1
      ∨ l'.2 - l.2 = Pi.single l.1 1 - Pi.single l'.1 1)) := by
  obtain ⟨⟨⟨α, β⟩, s⟩, hq, hq'⟩ := h
  simp only [bdT, WilsonHypercubic.bd, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_nil_iff, or_false] at hq hq'
  simp only [shift_eq] at hq hq'
  rcases hq with h1 | h1 | h1 | h1 <;> rcases hq' with h2 | h2 | h2 | h2 <;>
    (subst h1; subst h2; dsimp only at hne ⊢) <;>
    (by_cases hab : α = β) <;> (try subst hab) <;>
    first
    | exact absurd rfl hne
    | (refine Or.inl ⟨rfl, α, Or.inl ?_⟩; abel1)
    | (refine Or.inl ⟨rfl, α, Or.inr ?_⟩; abel1)
    | (refine Or.inl ⟨rfl, β, Or.inl ?_⟩; abel1)
    | (refine Or.inl ⟨rfl, β, Or.inr ?_⟩; abel1)
    | (refine Or.inr ⟨hab, Or.inl ?_⟩; abel1)
    | (refine Or.inr ⟨hab, Or.inr (Or.inl ?_)⟩; abel1)
    | (refine Or.inr ⟨hab, Or.inr (Or.inr (Or.inl ?_))⟩; abel1)
    | (refine Or.inr ⟨hab, Or.inr (Or.inr (Or.inr ?_))⟩; abel1)
    | (refine Or.inr ⟨fun h => hab h.symm, Or.inl ?_⟩; abel1)
    | (refine Or.inr ⟨fun h => hab h.symm, Or.inr (Or.inl ?_)⟩; abel1)
    | (refine Or.inr ⟨fun h => hab h.symm, Or.inr (Or.inr (Or.inl ?_))⟩; abel1)
    | (refine Or.inr ⟨fun h => hab h.symm, Or.inr (Or.inr (Or.inr ?_))⟩; abel1)

#print axioms share_cases

end Partners

/-! ## 4. The profile data and the multiplicities -/

/-- **One-dimensional profile data.** Two non-negative profiles `f` (across a link) and `g` (along it),
zero from `n` on and bounded by `fM`, `gM`, with bounds on every finite forward and backward
correlation: `Uff`, `Ugg`, `Ugf`, `Ufg` over all shifts, `Unzff`, `Unzgg` over the non-zero ones.

DERIVED: `1` is the least backward shift and non-zero forward shift; `0` the profiles' sign. -/
structure ProfileData (n : ℕ) where
  f : ℕ → ℝ
  g : ℕ → ℝ
  fM : ℝ
  gM : ℝ
  f_nn : ∀ t, 0 ≤ f t
  g_nn : ∀ t, 0 ≤ g t
  f_le : ∀ t, f t ≤ fM
  g_le : ∀ t, g t ≤ gM
  f_zero : ∀ t, n ≤ t → f t = 0
  g_zero : ∀ t, n ≤ t → g t = 0
  Uff : ℝ
  Ugg : ℝ
  Ugf : ℝ
  Ufg : ℝ
  Unzff : ℝ
  Unzgg : ℝ
  Uff_nn : 0 ≤ Uff
  Ugg_nn : 0 ≤ Ugg
  Ugf_nn : 0 ≤ Ugf
  Ufg_nn : 0 ≤ Ufg
  Unzff_nn : 0 ≤ Unzff
  Unzgg_nn : 0 ≤ Unzgg
  ff_fw : ∀ D, D < n → ∑ t ∈ Finset.range n, f t * f (t + D) ≤ Uff
  ff_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, f (t + r) * f t ≤ Uff
  gg_fw : ∀ D, D < n → ∑ t ∈ Finset.range n, g t * g (t + D) ≤ Ugg
  gg_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, g (t + r) * g t ≤ Ugg
  gf_fw : ∀ D, D < n → ∑ t ∈ Finset.range n, g t * f (t + D) ≤ Ugf
  gf_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, g (t + r) * f t ≤ Ugf
  fg_fw : ∀ D, D < n → ∑ t ∈ Finset.range n, f t * g (t + D) ≤ Ufg
  fg_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, f (t + r) * g t ≤ Ufg
  ffnz_fw : ∀ D, 1 ≤ D → D < n → ∑ t ∈ Finset.range n, f t * f (t + D) ≤ Unzff
  ffnz_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, f (t + r) * f t ≤ Unzff
  ggnz_fw : ∀ D, 1 ≤ D → D < n → ∑ t ∈ Finset.range n, g t * g (t + D) ≤ Unzgg
  ggnz_bw : ∀ r, 1 ≤ r → r < n → ∑ t ∈ Finset.range n, g (t + r) * g t ≤ Unzgg

namespace ProfileData

variable {n : ℕ} (P : ProfileData n)

/-- The finite correlation `Σ_{t<n} u(t) v(t + D)`.

DERIVED: no numeral. -/
def fc (u v : ℕ → ℝ) (D : ℕ) : ℝ := ∑ t ∈ Finset.range n, u t * v (t + D)

/-- The largest pair weight `K = max(Ugf Ufg Uff², Unzgg Uff³, Ugg Unzff Uff²)`.

DERIVED: `2`, `3` count the transverse directions at full overlap. -/
def K : ℝ := max (P.Ugf * P.Ufg * P.Uff ^ 2) (max (P.Unzgg * P.Uff ^ 3) (P.Ugg * P.Unzff * P.Uff ^ 2))

/-- `a₁ = (Σ g)(Σ f)³`. DERIVED: `3` the transverse directions. -/
def a₁ : ℝ := (∑ t ∈ Finset.range n, P.g t) * (∑ t ∈ Finset.range n, P.f t) ^ 3

/-- `a₂ = Cgg(0) Cff(0)³`. DERIVED: `0` the zero shift; `3` the transverse directions. -/
def a₂ : ℝ := fc (n := n) P.g P.g 0 * fc (n := n) P.f P.f 0 ^ 3

/-- The excess `e`: two axial partners, six parallel ones, and three transverse directions with
four partners each.

DERIVED: `2`, `6`, `3` count the partners; `0`, `1` are the shifts; `2`, `3` the exponents. -/
def e : ℝ :=
  2 * (P.K - fc (n := n) P.g P.g 1 * fc (n := n) P.f P.f 0 ^ 3)
  + 6 * (P.K - fc (n := n) P.g P.g 0 * fc (n := n) P.f P.f 1 * fc (n := n) P.f P.f 0 ^ 2)
  + 3 * ((P.K - fc (n := n) P.g P.f 0 * fc (n := n) P.f P.g 0 * fc (n := n) P.f P.f 0 ^ 2)
    + (P.K - fc (n := n) P.g P.f 1 * fc (n := n) P.f P.g 0 * fc (n := n) P.f P.f 0 ^ 2)
    + (P.K - fc (n := n) P.g P.f 0 * fc (n := n) P.g P.f 1 * fc (n := n) P.f P.f 0 ^ 2)
    + (P.K - fc (n := n) P.g P.f 1 * fc (n := n) P.g P.f 1 * fc (n := n) P.f P.f 0 ^ 2))

/-- The profile of coordinate `κ` vanishes from `n` on. -/
theorem pf_zero (μ κ : Fin 4) : ∀ t, n ≤ t → pf P.f P.g μ κ t = 0 := by
  intro t ht; unfold pf; split_ifs
  · exact P.g_zero t ht
  · exact P.f_zero t ht

theorem pf_nn (μ κ : Fin 4) : ∀ t, 0 ≤ pf P.f P.g μ κ t := by
  intro t; unfold pf; split_ifs
  · exact P.g_nn t
  · exact P.f_nn t

/-- The bound on a coordinate's correlation by the directions of the two links. -/
def Ub (μ ν κ : Fin 4) : ℝ :=
  if κ = μ then (if κ = ν then P.Ugg else P.Ugf) else (if κ = ν then P.Ufg else P.Uff)

theorem Ub_nn (μ ν κ : Fin 4) : 0 ≤ P.Ub μ ν κ := by
  unfold Ub; split_ifs
  · exact P.Ugg_nn
  · exact P.Ugf_nn
  · exact P.Ufg_nn
  · exact P.Uff_nn

variable {M : ℕ}

theorem corr_le_Ub (hL : 2 * n ≤ M + 1) (μ ν κ : Fin 4) (d : Fin (M + 1)) :
    corr (pf P.f P.g μ κ) (pf P.f P.g ν κ) d ≤ P.Ub μ ν κ := by
  unfold Ub pf
  split_ifs <;> first
    | exact corr_le hL _ _ P.g_zero P.g_zero P.Ugg_nn P.gg_fw P.gg_bw d
    | exact corr_le hL _ _ P.g_zero P.f_zero P.Ugf_nn P.gf_fw P.gf_bw d
    | exact corr_le hL _ _ P.f_zero P.g_zero P.Ufg_nn P.fg_fw P.fg_bw d
    | exact corr_le hL _ _ P.f_zero P.f_zero P.Uff_nn P.ff_fw P.ff_bw d

theorem corr_le_Unz (hL : 2 * n ≤ M + 1) (μ κ : Fin 4) (d : Fin (M + 1)) (hd : d ≠ 0) :
    corr (pf P.f P.g μ κ) (pf P.f P.g μ κ) d ≤ (if κ = μ then P.Unzgg else P.Unzff) := by
  unfold pf
  split_ifs <;> first
    | exact corr_le_nz hL _ _ P.g_zero P.g_zero P.Unzgg_nn P.ggnz_fw P.ggnz_bw d hd
    | exact corr_le_nz hL _ _ P.f_zero P.f_zero P.Unzff_nn P.ffnz_fw P.ffnz_bw d hd

/-- **Every pair weight of distinct links is at most `K`.**

DERIVED: `4` is the spacetime dimension. -/
theorem pair_le_K (hL : 2 * n ≤ M + 1) {l l' : WilsonHypercubic.Link 4 (M + 1)} (hne : l ≠ l') :
    pairWeight (prodC (M := M) P.f P.g) l l' ≤ P.K := by
  rw [pairWeight_prodC]
  have hnn : ∀ κ, 0 ≤ corr (pf P.f P.g l.1 κ) (pf P.f P.g l'.1 κ) ((l'.2 - l.2) κ) :=
    fun κ => corr_nonneg _ _ (P.pf_nn _ _) (P.pf_nn _ _) _
  by_cases hdir : l'.1 = l.1
  · have hpos : l'.2 ≠ l.2 := fun h => hne (Prod.ext hdir.symm h.symm)
    obtain ⟨κ0, hκ0⟩ : ∃ κ0, (l'.2 - l.2) κ0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hpos (sub_eq_zero.mp (funext hcon))
    rw [hdir]
    calc ∏ κ, corr (pf P.f P.g l.1 κ) (pf P.f P.g l.1 κ) ((l'.2 - l.2) κ)
        ≤ ∏ κ, (if κ = κ0 then (if κ = l.1 then P.Unzgg else P.Unzff) else P.Ub l.1 l.1 κ) := by
          refine Finset.prod_le_prod (fun κ _ => ?_) (fun κ _ => ?_)
          · exact corr_nonneg _ _ (P.pf_nn _ _) (P.pf_nn _ _) _
          · by_cases h : κ = κ0
            · rw [if_pos h]; subst h; exact P.corr_le_Unz hL l.1 κ _ hκ0
            · rw [if_neg h]; exact P.corr_le_Ub hL l.1 l.1 κ _
      _ ≤ P.K := by
          have h2 : P.Unzgg * P.Uff ^ 3 ≤ P.K := le_max_of_le_right (le_max_left _ _)
          have h3 : P.Ugg * P.Unzff * P.Uff ^ 2 ≤ P.K := le_max_of_le_right (le_max_right _ _)
          unfold Ub
          rcases l with ⟨μ, x⟩
          fin_cases μ <;> fin_cases κ0 <;> simp [Fin.prod_univ_four] <;> linarith
  · calc ∏ κ, corr (pf P.f P.g l.1 κ) (pf P.f P.g l'.1 κ) ((l'.2 - l.2) κ)
        ≤ ∏ κ, P.Ub l.1 l'.1 κ :=
          Finset.prod_le_prod (fun κ _ => hnn κ) (fun κ _ => P.corr_le_Ub hL _ _ κ _)
      _ ≤ P.K := by
          have h1 : P.Ugf * P.Ufg * P.Uff ^ 2 ≤ P.K := le_max_left _ _
          unfold Ub
          rcases l with ⟨μ, x⟩
          rcases l' with ⟨ν, y⟩
          simp only at hdir ⊢
          fin_cases μ <;> fin_cases ν <;> simp [Fin.prod_univ_four] at hdir ⊢ <;> linarith

/-- The circle correlation at the shifts `0`, `1`, `−1` in finite sums.

DERIVED: `0`, `1`, `−1` are the shifts; `2` the two windows fitting in the circle. -/
theorem corr_vals (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (u v : ℕ → ℝ) (hu : ∀ t, n ≤ t → u t = 0)
    (hv : ∀ t, n ≤ t → v t = 0) :
    corr u v (0 : Fin (M + 1)) = fc (n := n) u v 0 ∧ corr u v (1 : Fin (M + 1)) = fc (n := n) u v 1
      ∧ corr u v (-1 : Fin (M + 1)) = fc (n := n) v u 1 := by
  refine ⟨?_, corr_one hL hn u v hu, ?_⟩
  · rw [corr_zero (by omega) u v hu]; unfold fc; simp only [add_zero]
  · rw [corr_neg, corr_one hL hn v u hv]; rfl

/-- The pair weight of `l` with the link of direction `ν` at `l.2 + δ`.

DERIVED: `4` is the spacetime dimension. -/
theorem pw_disp (l : WilsonHypercubic.Link 4 (M + 1)) (ν : Fin 4) (δ : WilsonHypercubic.Site 4 (M + 1)) :
    pairWeight (prodC (M := M) P.f P.g) l (ν, l.2 + δ)
      = ∏ κ, corr (pf P.f P.g l.1 κ) (pf P.f P.g ν κ) (δ κ) := by
  rw [pairWeight_prodC]
  simp only [add_sub_cancel_left]

open Classical in
/-- The excess weight of the product weights: `K − pairWeight` on distinct links of a common
plaquette, `0` otherwise.

DERIVED: `0` off the plaquette partners. -/
def wP (l l' : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l ≠ l' ∧ SharePlaq (bdT M) l l' then P.K - pairWeight (prodC (M := M) P.f P.g) l l' else 0

theorem wP_nonneg (hL : 2 * n ≤ M + 1) (l l' : WilsonHypercubic.Link 4 (M + 1)) : 0 ≤ P.wP l l' := by
  unfold wP; split_ifs with h
  · exact sub_nonneg.mpr (P.pair_le_K hL h.1)
  · exact le_refl 0

theorem wP_symm (l l' : WilsonHypercubic.Link 4 (M + 1)) : P.wP l l' = P.wP l' l := by
  unfold wP
  have hpw : pairWeight (prodC (M := M) P.f P.g) l l' = pairWeight (prodC (M := M) P.f P.g) l' l := by
    unfold pairWeight; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hiff : (l ≠ l' ∧ SharePlaq (bdT M) l l') ↔ (l' ≠ l ∧ SharePlaq (bdT M) l' l) :=
    ⟨fun ⟨h1, ⟨p, a, b⟩⟩ => ⟨Ne.symm h1, ⟨p, b, a⟩⟩, fun ⟨h1, ⟨p, a, b⟩⟩ => ⟨Ne.symm h1, ⟨p, b, a⟩⟩⟩
  by_cases h : l ≠ l' ∧ SharePlaq (bdT M) l l'
  · rw [if_pos h, if_pos (hiff.mp h), hpw]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- One indicator term of the partner sum: `K − pairWeight` at the link `c`, if `l' = c`. -/
def ind (l c l' : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l' = c then P.K - pairWeight (prodC (M := M) P.f P.g) l l' else 0

theorem ind_nonneg (hL : 2 * n ≤ M + 1) (l c : WilsonHypercubic.Link 4 (M + 1)) (hc : l ≠ c)
    (l' : WilsonHypercubic.Link 4 (M + 1)) : 0 ≤ P.ind l c l' := by
  unfold ind; split_ifs with h
  · subst h; exact sub_nonneg.mpr (P.pair_le_K hL hc)
  · exact le_refl 0

/-- The partner links of `l`, as a list: eight of the same direction, four in each other direction.

DERIVED: `1` the unit step; `0` the zero displacement. -/
def partners (l : WilsonHypercubic.Link 4 (M + 1)) : List (WilsonHypercubic.Link 4 (M + 1)) :=
  (List.finRange 4).flatMap (fun ρ => [(l.1, l.2 + Pi.single ρ 1), (l.1, l.2 + -Pi.single ρ 1)])
  ++ ((List.finRange 4).filter (fun ν => ν ≠ l.1)).flatMap (fun ν =>
    [(ν, l.2 + 0), (ν, l.2 + Pi.single l.1 1), (ν, l.2 + -Pi.single ν 1),
     (ν, l.2 + (Pi.single l.1 1 - Pi.single ν 1))])

theorem one_ne_zero_fin (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) : (1 : Fin (M + 1)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  exact one_ne_zero this

theorem single_ne_zero (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (ρ : Fin 4) :
    (Pi.single ρ (1 : Fin (M + 1)) : WilsonHypercubic.Site 4 (M + 1)) ≠ 0 := by
  intro h
  have := congrFun h ρ
  rw [Pi.single_eq_same] at this
  exact one_ne_zero_fin hL hn this

theorem partners_ne (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∀ c ∈ partners l, l ≠ c := by
  intro c hc heq
  subst heq
  unfold partners at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
    List.mem_nil_iff, or_false, List.mem_filter, decide_eq_true_eq] at hc
  rcases hc with ⟨ρ, h | h⟩ | ⟨ν, hν, h | h | h | h⟩
  · have := congrArg Prod.snd h
    simp only at this
    exact single_ne_zero hL hn ρ (by
      have h2 : l.2 + Pi.single ρ 1 - l.2 = l.2 - l.2 := by rw [← this]
      simpa using h2)
  · have := congrArg Prod.snd h
    simp only at this
    exact single_ne_zero hL hn ρ (by
      have h2 : l.2 + -Pi.single ρ 1 - l.2 = l.2 - l.2 := by rw [← this]
      simpa using h2)
  all_goals exact hν (congrArg Prod.fst h).symm

/-- **The excess is dominated by the partner sum.** `wP l l' ≤ Σ_{c ∈ partners l} ind l c l'`.

DERIVED: no numeral. -/
theorem wP_le_partners (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (l l' : WilsonHypercubic.Link 4 (M + 1)) :
    P.wP l l' ≤ ((partners l).map (fun c => P.ind l c l')).sum := by
  have hnn : ∀ c ∈ partners l, 0 ≤ P.ind l c l' := fun c hc => P.ind_nonneg hL l c (partners_ne hL hn l c hc) l'
  unfold wP
  split_ifs with h
  · obtain ⟨hne, hs⟩ := h
    have hmem : l' ∈ partners l := by
      rcases share_cases hs hne with ⟨hd, ρ, hδ | hδ⟩ | ⟨hd, hδ | hδ | hδ | hδ⟩
      all_goals
        unfold partners
        simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
          List.mem_nil_iff, or_false, List.mem_filter, decide_eq_true_eq]
      · exact Or.inl ⟨ρ, Or.inl (Prod.ext hd (by dsimp only; rw [← hδ]; abel))⟩
      · exact Or.inl ⟨ρ, Or.inr (Prod.ext hd (by dsimp only; rw [← hδ]; abel))⟩
      · exact Or.inr ⟨l'.1, hd, Or.inl (Prod.ext rfl (by dsimp only; rw [← hδ]; abel))⟩
      · exact Or.inr ⟨l'.1, hd, Or.inr (Or.inl (Prod.ext rfl (by dsimp only; rw [← hδ]; abel)))⟩
      · exact Or.inr ⟨l'.1, hd, Or.inr (Or.inr (Or.inl (Prod.ext rfl (by dsimp only; rw [← hδ]; abel))))⟩
      · exact Or.inr ⟨l'.1, hd, Or.inr (Or.inr (Or.inr (Prod.ext rfl (by dsimp only; rw [← hδ]; abel))))⟩
    have hval : P.ind l l' l' = P.K - pairWeight (prodC (M := M) P.f P.g) l l' := by
      unfold ind; rw [if_pos rfl]
    rw [← hval]
    exact List.single_le_sum (fun c hc => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact hnn c' hc') _ (List.mem_map.mpr ⟨l', hmem, rfl⟩)
  · exact List.sum_nonneg (fun x hx => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
      exact hnn c' hc')

theorem pw_disp' (μ ν : Fin 4) (x δ : WilsonHypercubic.Site 4 (M + 1)) :
    pairWeight (prodC (M := M) P.f P.g) (μ, x) (ν, x + δ)
      = ∏ κ, corr (pf P.f P.g μ κ) (pf P.f P.g ν κ) (δ κ) := by
  rw [pairWeight_prodC]
  simp only [add_sub_cancel_left]

theorem pw_disp0 (μ ν : Fin 4) (x : WilsonHypercubic.Site 4 (M + 1)) :
    pairWeight (prodC (M := M) P.f P.g) (μ, x) (ν, x)
      = ∏ κ, corr (pf P.f P.g μ κ) (pf P.f P.g ν κ) (0 : Fin (M + 1)) := by
  rw [pairWeight_prodC]
  simp only [sub_self, Pi.zero_apply]

theorem sum_list_swap {α : Type*} (L : List α) (G : α → WilsonHypercubic.Link 4 (M + 1) → ℝ) :
    ∑ l', (L.map (fun c => G c l')).sum = (L.map (fun c => ∑ l', G c l')).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **The row sum of the excess is at most `e`.**

DERIVED: `2` the two windows fitting in the circle; `1` the least box side. -/
theorem row_le (hL : 2 * n ≤ M + 1) (hn : 1 ≤ n) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ l', P.wP l l' ≤ P.e := by
  calc ∑ l', P.wP l l' ≤ ∑ l', ((partners l).map (fun c => P.ind l c l')).sum :=
        Finset.sum_le_sum (fun l' _ => P.wP_le_partners hL hn l l')
    _ = ((partners l).map (fun c => ∑ l', P.ind l c l')).sum := sum_list_swap _ _
    _ = ((partners l).map (fun c => P.K - pairWeight (prodC (M := M) P.f P.g) l c)).sum := by
        congr 1
        refine List.map_congr_left (fun c _ => ?_)
        unfold ind
        rw [Finset.sum_ite_eq' Finset.univ c, if_pos (Finset.mem_univ c)]
    _ ≤ P.e := by
        obtain ⟨hff0, hff1, hffm⟩ := corr_vals (M := M) hL hn P.f P.f P.f_zero P.f_zero
        obtain ⟨hgg0, hgg1, hggm⟩ := corr_vals (M := M) hL hn P.g P.g P.g_zero P.g_zero
        obtain ⟨hgf0, hgf1, hgfm⟩ := corr_vals (M := M) hL hn P.g P.f P.g_zero P.f_zero
        obtain ⟨hfg0, hfg1, hfgm⟩ := corr_vals (M := M) hL hn P.f P.g P.f_zero P.g_zero
        rcases l with ⟨μ, x⟩
        unfold partners
        fin_cases μ <;>
          simp [List.finRange, List.flatMap, pw_disp', pw_disp0, Fin.prod_univ_four, pf,
            Pi.single_apply, hff0, hff1, hffm, hgg0, hgg1, hggm, hgf0, hgf1, hfg0, hfgm] <;>
          (unfold e; linarith)

/-- The cover of the profile of coordinate `ν` over the circle: `Σ g` along, `Σ f` across. -/
theorem sum_pf (hL : 2 * n ≤ M + 1) (μ ν : Fin 4) :
    ∑ t : Fin (M + 1), pf P.f P.g μ ν (t : ℕ)
      = if ν = μ then ∑ t ∈ Finset.range n, P.g t else ∑ t ∈ Finset.range n, P.f t := by
  rw [sum_circle (by omega) _ (P.pf_zero μ ν)]
  unfold pf; split_ifs <;> rfl

/-- The weight bound `cm = max(fM, gM)⁴`. DERIVED: `4` the spacetime dimension. -/
def cm : ℝ := max P.fM P.gM ^ 4

theorem cm_nonneg : 0 ≤ P.cm := by
  unfold cm
  exact pow_nonneg ((P.f_nn 0).trans ((P.f_le 0).trans (le_max_left _ _))) 4

theorem prodC_nonneg (k : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    0 ≤ prodC (M := M) P.f P.g k l :=
  Finset.prod_nonneg (fun _ _ => P.pf_nn _ _ _)

theorem prodC_le (k : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    prodC (M := M) P.f P.g k l ≤ P.cm * BoxPatch.boxWeight n k l := by
  unfold BoxPatch.boxWeight
  split_ifs with hin
  · rw [mul_one]
    unfold cm prodC
    calc ∏ ν, pf P.f P.g l.1 ν (((l.2 - k) ν : Fin (M + 1)) : ℕ)
        ≤ ∏ _ν : Fin 4, max P.fM P.gM := by
          refine Finset.prod_le_prod (fun ν _ => P.pf_nn _ _ _) (fun ν _ => ?_)
          unfold pf; split_ifs
          · exact (P.g_le _).trans (le_max_right _ _)
          · exact (P.f_le _).trans (le_max_left _ _)
      _ = max P.fM P.gM ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [mul_zero]
    unfold BoxPatch.InBox at hin
    push Not at hin
    obtain ⟨κ, hκ⟩ := hin
    unfold prodC
    exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ κ) (P.pf_zero _ _ _ hκ))

/-- **The weight family of the profile data** at every torus with `n ≤ j + 1`: weights `prodC`,
cover `a₁`, squared cover `a₂`, `b = K`, excess `wP`, `e`.

DERIVED: `2 * j + 1` is the index of the even-extent family; `1` the least box side. -/
def toFamily {N : ℕ} (hN : N ≠ 0) (β : ℝ) (hn : 1 ≤ n) (j : ℕ) (hnj : n ≤ j + 1) :
    MassGap.WeightedBox.WeightedFamilyAt hN β n j P.a₁ P.a₂ P.K P.e where
  c := prodC (M := 2 * j + 1) P.f P.g
  w := P.wP
  cm := P.cm
  cm_nonneg := P.cm_nonneg
  c_nonneg := P.prodC_nonneg
  c_le := P.prodC_le
  cover := fun l => by
    rw [cover_prodC]
    rw [Finset.prod_congr rfl (fun ν _ => P.sum_pf (M := 2 * j + 1) (by omega) l.1 ν)]
    rw [prod_ite_four]
    rfl
  cover2 := fun l => by
    rw [pairWeight_prodC, sub_self]
    obtain ⟨hff0, -, -⟩ := corr_vals (M := 2 * j + 1) (by omega) hn P.f P.f P.f_zero P.f_zero
    obtain ⟨hgg0, -, -⟩ := corr_vals (M := 2 * j + 1) (by omega) hn P.g P.g P.g_zero P.g_zero
    have : ∀ κ, corr (pf P.f P.g l.1 κ) (pf P.f P.g l.1 κ)
        ((0 : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) κ)
        = if κ = l.1 then fc (n := n) P.g P.g 0 else fc (n := n) P.f P.f 0 := by
      intro κ
      rw [Pi.zero_apply]
      unfold pf; split_ifs
      · exact hgg0
      · exact hff0
    rw [Finset.prod_congr rfl (fun κ _ => this κ), prod_ite_four]
    rfl
  pair := fun l l' hll => by
    by_cases hs : SharePlaq (bdT (2 * j + 1)) l l'
    · right
      have hle := P.pair_le_K (M := 2 * j + 1) (by omega) hll
      unfold wP
      rw [if_pos ⟨hll, hs⟩, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    · exact Or.inl ⟨hs, P.pair_le_K (M := 2 * j + 1) (by omega) hll⟩
  w_nonneg := P.wP_nonneg (M := 2 * j + 1) (by omega)
  row := P.row_le (M := 2 * j + 1) (by omega) hn
  col := fun l' => by
    rw [Finset.sum_congr rfl (fun l _ => P.wP_symm l l')]
    exact P.row_le (M := 2 * j + 1) (by omega) hn l'

end ProfileData

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one box and one-dimensional profile data.** As
`WeightedBox.clay_continuum_of_weightedBox`, with the weights built from `P : ProfileData n`
(`ProfileData.toFamily`): at `2 ≤ N`, `0 < L`, `0 < β₀`, `βUV ≤ β₀`, `1 ≤ n`, `0 < K`, `a₁ ≠ 0`, the box
check `BoxGap.BoxFibreGap hN β₀ n γ` with `γ > (a₂ − K + e) n⁴/a₁²`, the UV step below the rate, and
E, N, Y: `ClayRoutes.ClayContinuum hN Z τ hZ hB L`.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` the excluded colour count, the
reflection plane and the lower ends; `4` the spacetime dimension; `1` the least box side. -/
theorem clay_continuum_of_profile {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (P : ProfileData n) (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hn : 1 ≤ n)
    (hγ : 0 < γ) (hK : 0 < P.K) (ha₁ : P.a₁ ≠ 0)
    (hthr : (P.a₂ - P.K + P.e) * (n : ℝ) ^ 4 / P.a₁ ^ 2 < γ)
    (hbox : BoxGap.BoxFibreGap hN β₀ n γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV
      (MassGap.WeightedBox.weightedRate N β₀
        (MassGap.WeightedBox.weightedConst n P.a₁ P.a₂ P.K P.e γ)))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  MassGap.WeightedBox.clay_continuum_of_weightedBox hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀ hn hγ hK ha₁ hthr
    hbox (fun j hnj => P.toFamily hN β₀ hn j hnj) huv O G hconv hY

#print axioms clay_continuum_of_profile

end MassGap.WeightedProduct
