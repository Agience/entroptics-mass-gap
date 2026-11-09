import Mathlib
import MassGap.ApeLattice
import MassGap.LatticeReflection

/-!
# MassGap.ReflApe — the APE step commutes with the time reflection

`LatticeReflection.ireflConf τ 0` reflects sites `x_τ ↦ −x_τ`, bases `τ`-links at `−x_τ − 1` and inverts
them. For a link not along `τ` the reflected configuration's staples are the original staples at the
reflected site, with the two sides of the `τ`-staple swapped (`apeStaple_refl_ne`); for a `τ`-link they
are the inverses of the original staples at the reflected link, side for side (`apeStaple_refl_eq`).
With `BlockSU2.blockLink_perm` and `BlockSU2.blockLink_inv` the step commutes with the reflection
(`apeConf_refl`).
-/

namespace MassGap.ReflApe

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.BlockSU2 MassGap.BlockLattice
  MassGap.ApeLattice MassGap.LatticeReflection

/-- DERIVED: `1` is one lattice step. -/
theorem iback_ishift (ν : Fin 4) (x : ISite) : iback ν (ishift ν x) = x := by
  funext i
  by_cases h : i = ν
  · subst h; simp [ishift, iback]
  · simp [ishift, iback, Function.update_of_ne h]

/-- A shift transverse to the reflection commutes with it. An alias of
`LatticeReflection.ireflSite_ishift_of_ne`. -/
alias refl_ishift_ne := MassGap.LatticeReflection.ireflSite_ishift_of_ne

/-- DERIVED: `1` is one lattice step. -/
theorem refl_iback_ne {τ ν : Fin 4} (h : ν ≠ τ) (c : ℤ) (x : ISite) :
    ireflSite τ c (iback ν x) = iback ν (ireflSite τ c x) := by
  funext i
  simp only [ireflSite, iback, Function.update_apply]
  split_ifs <;> simp_all

/-- A shift along the reflection is reversed by it.

DERIVED: `1` is one lattice step. -/
theorem refl_ishift_eq (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (ishift τ x) = iback τ (ireflSite τ c x) := by
  funext i
  simp only [ireflSite, ishift, iback, Function.update_apply]
  split_ifs <;> omega

/-- The `τ`-link base offset: `c − 1 − x_τ` is one step back from `c − x_τ`.

DERIVED: `1` is the `τ`-link offset. -/
theorem refl_pred (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ (c - 1) x = iback τ (ireflSite τ c x) := by
  funext i
  simp only [ireflSite, iback, Function.update_apply]
  split_ifs <;> omega

/-- `refl_pred` at `c = 0`, in the normal form `-1` that `simp` produces.

DERIVED: `1` is the `τ`-link offset. -/
theorem refl_pred_neg (τ : Fin 4) (x : ISite) :
    ireflSite τ (-1) x = iback τ (ireflSite τ 0 x) := by
  have h := refl_pred τ 0 x
  simpa using h

/-- A back-shift along the reflection becomes a forward shift.

DERIVED: `1` is one lattice step. -/
theorem refl_iback_eq (τ : Fin 4) (c : ℤ) (x : ISite) :
    ireflSite τ c (iback τ x) = ishift τ (ireflSite τ c x) := by
  funext i
  simp only [ireflSite, ishift, iback, Function.update_apply]
  split_ifs <;> omega

/-- Back-shifts commute.

DERIVED: `1` is one lattice step. -/
theorem iback_comm (a b : Fin 4) (x : ISite) : iback a (iback b x) = iback b (iback a x) := by
  funext i
  by_cases ha : i = a <;> by_cases hb : i = b
  · subst ha; subst hb; rfl
  · subst ha; simp [iback, Function.update_of_ne hb]
  · subst hb; simp [iback, Function.update_of_ne ha]
  · simp [iback, Function.update_of_ne ha, Function.update_of_ne hb]

/-- The side swap of the `τ`-staple: `(j, s) ↦ (j, 1 − s)` when the transverse direction `other μ j`
is `τ`, the identity otherwise. An involution.

DERIVED: `1` swaps the two sides; `3 = 4 − 1` the directions transverse to `μ` (`other μ`). -/
def sideSwap (μ τ : Fin 4) (p : Fin 3 × Fin 2) : Fin 3 × Fin 2 :=
  if other μ p.1 = τ then (p.1, Equiv.swap 0 1 p.2) else p

/-- DERIVED: no numeral. -/
theorem sideSwap_involutive (μ τ : Fin 4) : Function.Involutive (sideSwap μ τ) := by
  intro p
  unfold sideSwap
  by_cases h : other μ p.1 = τ
  · simp [h]
  · simp [h]

/-- **Staples of the reflected configuration at a link not along `τ`**: the original staples at the
reflected site, sides swapped for the `τ` direction.

DERIVED: `0` the reflection constant; `0` names the upper side; `3 = 4 − 1` the directions transverse
to `μ` (`other μ`). -/
theorem apeStaple_refl_ne {τ μ : Fin 4} (hμ : μ ≠ τ) (U : IConf G2) (x : ISite) (p : Fin 3 × Fin 2) :
    apeStaple (ireflConf τ 0 U) μ x p = apeStaple U μ (ireflSite τ 0 x) (sideSwap μ τ p) := by
  obtain ⟨j, sd⟩ := p
  have Rμ : ∀ z, ireflConf τ 0 U (μ, z) = U (μ, ireflSite τ 0 z) := by
    intro z; simp [ireflConf, ireflLink, hμ]
  have Rτ : ∀ z, ireflConf τ 0 U (τ, z) = (U (τ, iback τ (ireflSite τ 0 z)))⁻¹ := by
    intro z; simp [ireflConf, ireflLink, refl_pred_neg]
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · by_cases hν : other μ j = τ
    · simp only [apeStaple, sideSwap, hν, if_true, Equiv.swap_apply_left, Rμ, Rτ, inv_inv,
        refl_ishift_eq, refl_ishift_ne hμ]
      simp [← ishift_iback_comm]
    · have Rν : ∀ z, ireflConf τ 0 U (other μ j, z) = U (other μ j, ireflSite τ 0 z) := by
        intro z; simp [ireflConf, ireflLink, hν]
      simp [apeStaple, sideSwap, hν, Rμ, Rν, refl_ishift_ne hν, refl_ishift_ne hμ]
  · by_cases hν : other μ j = τ
    · simp only [apeStaple, sideSwap, hν, if_true, Equiv.swap_apply_right, Rμ, Rτ, inv_inv,
        refl_iback_eq, refl_ishift_ne hμ]
      simp [← ishift_iback_comm, iback_ishift, ishift_iback]
    · have Rν : ∀ z, ireflConf τ 0 U (other μ j, z) = U (other μ j, ireflSite τ 0 z) := by
        intro z; simp [ireflConf, ireflLink, hν]
      simp [apeStaple, sideSwap, hν, Rμ, Rν, refl_iback_ne hν, refl_ishift_ne hμ]

/-- **Staples of the reflected configuration at a `τ`-link**: the inverses of the original staples at
the reflected link, side for side.

DERIVED: `0` the reflection constant; `3 = 4 − 1` the directions transverse to `τ` (`other τ`). -/
theorem apeStaple_refl_eq (τ : Fin 4) (U : IConf G2) (x : ISite) (p : Fin 3 × Fin 2) :
    apeStaple (ireflConf τ 0 U) τ x p = (apeStaple U τ (ireflSite τ (0 - 1) x) p)⁻¹ := by
  obtain ⟨j, sd⟩ := p
  have hν : other τ j ≠ τ := Fin.succAbove_ne τ j
  have Rτ : ∀ z, ireflConf τ 0 U (τ, z) = (U (τ, iback τ (ireflSite τ 0 z)))⁻¹ := by
    intro z; simp [ireflConf, ireflLink, refl_pred_neg]
  have Rν : ∀ z, ireflConf τ 0 U (other τ j, z) = U (other τ j, ireflSite τ 0 z) := by
    intro z; simp [ireflConf, ireflLink, hν]
  obtain rfl | rfl : sd = 0 ∨ sd = 1 := by fin_cases sd <;> simp
  · simp [apeStaple, Rτ, Rν, refl_pred_neg, refl_ishift_ne hν, refl_ishift_eq, mul_inv_rev,
      ishift_iback, ishift_iback_comm, mul_assoc]
  · simp [apeStaple, Rτ, Rν, refl_pred_neg, refl_iback_ne hν, refl_ishift_eq, mul_inv_rev,
      ishift_iback, ishift_iback_comm, iback_comm, mul_assoc]

/-- The staple reindexing under the reflection, as a permutation of the six staples.

DERIVED: `6 = 3 · 2` staples. -/
def stapleSwap (μ τ : Fin 4) : Equiv.Perm (Fin 6) :=
  (finProdFinEquiv.symm.trans ((sideSwap_involutive μ τ).toPerm _)).trans finProdFinEquiv

/-- **The APE step commutes with the time reflection**: `apeConf (θ U) = θ (apeConf U)`.

DERIVED: `0` is the reflection constant; `1/6` the dominance bound. -/
theorem apeConf_refl {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (τ : Fin 4) (U : IConf G2) :
    apeConf c hc0 hc (ireflConf τ 0 U) = ireflConf τ 0 (apeConf c hc0 hc U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ
  · subst hμ
    have hS : (fun i => apeStaple (ireflConf μ 0 U) μ x (finProdFinEquiv.symm i))
        = fun i => (apeStaple U μ (ireflSite μ (0 - 1) x) (finProdFinEquiv.symm i))⁻¹ :=
      funext (fun i => apeStaple_refl_eq μ U x _)
    have hW : ireflConf μ 0 U (μ, x) = (U (μ, ireflSite μ (0 - 1) x))⁻¹ := by
      simp only [ireflConf, ireflLink, eq_self_iff_true, if_true]
    have hR : ireflConf μ 0 (apeConf c hc0 hc U) (μ, x)
        = (apeConf c hc0 hc U (μ, ireflSite μ (0 - 1) x))⁻¹ := by
      simp only [ireflConf, ireflLink, eq_self_iff_true, if_true]
    show blockLink c hc0 hc (ireflConf μ 0 U (μ, x))
        (fun i => apeStaple (ireflConf μ 0 U) μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, blockLink_inv]
    rfl
  · have hS : (fun i => apeStaple (ireflConf τ 0 U) μ x (finProdFinEquiv.symm i))
        = (fun i => apeStaple U μ (ireflSite τ 0 x) (finProdFinEquiv.symm i)) ∘ stapleSwap μ τ := by
      funext i
      simp only [Function.comp, stapleSwap, Equiv.trans_apply, Equiv.symm_apply_apply,
        Function.Involutive.coe_toPerm]
      exact apeStaple_refl_ne hμ U x _
    have hW : ireflConf τ 0 U (μ, x) = U (μ, ireflSite τ 0 x) := by
      simp only [ireflConf, ireflLink, hμ, if_false]
    have hR : ireflConf τ 0 (apeConf c hc0 hc U) (μ, x) = apeConf c hc0 hc U (μ, ireflSite τ 0 x) := by
      simp only [ireflConf, ireflLink, hμ, if_false]
    show blockLink c hc0 hc (ireflConf τ 0 U (μ, x))
        (fun i => apeStaple (ireflConf τ 0 U) μ x (finProdFinEquiv.symm i)) = _
    rw [hS, hW, hR, blockLink_perm]
    rfl

#print axioms apeConf_refl

#print axioms iback_ishift
#print axioms refl_ishift_ne
#print axioms refl_iback_ne
#print axioms refl_ishift_eq
#print axioms refl_pred
#print axioms refl_pred_neg
#print axioms refl_iback_eq
#print axioms iback_comm
#print axioms sideSwap_involutive
#print axioms apeStaple_refl_ne
#print axioms apeStaple_refl_eq

end MassGap.ReflApe
