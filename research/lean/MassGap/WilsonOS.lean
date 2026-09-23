import Mathlib
import MassGap.WightmanData
import MassGap.ReflectionStrong

/-!
# MassGap.WilsonOS — Osterwalder–Schrader data carrying the Wilson Gibbs reflected form

`WightmanData.OSData` asks for a real normed test space, a continuous bilinear Schwinger form, a
reflection, a translation action of `E4`, and four conditions. Before this module the only term of
that type in the tree was `WightmanData.trivialOSData`, whose form is multiplication on `ℝ`.

This module builds the type from a `Transfer.ReflForm` — the interface
`ReflectionStrong.wilsonGibbsReflForm` produces for the four-dimensional `SU(N)` Wilson lattice, with
`form_nonneg` proved at every real coupling — evaluated on a finite family of slab observables.

## What supplies each field

| field | supplied by |
|---|---|
| `Test` | `EuclideanSpace ℝ (Fin k)`, the coefficients of the chosen observables |
| `S` | `P.form` on the corresponding linear combinations, continuous because the domain is finite-dimensional |
| `os2` | `Transfer.ReflForm.form_nonneg` — reflection positivity of the Wilson Gibbs form |
| `os3` | `Transfer.PreForm.form_symm` |
| `os_nontriv` | one family member on which the form is nonzero; at the Wilson instance this is `wilsonGibbsReflForm_vac_norm`, which reads `1` |
| `theta` | the identity: the reflection is inside `P.form`, which is the pairing `⟨θF, G⟩` |
| `transl` | the identity, which `LatticeTranslNoGo.transl_eq_id_of_finite_order` shows is what a periodic lattice forces |
| `os1` | `rfl`, the case `LatticeTranslNoGo.os1_holds_of_everything_when_transl_trivial` describes |

## What the form carries

`ReflectionStrong.wilsonGibbsReflForm` is the Gibbs pairing of the `SU(N)` Wilson measure on the slab
algebra `localObs (blkS τ a m) (blkR τ a m)` of an even-extent periodic lattice, normalised by the
partition function. Its `form_nonneg` runs through `pairing_nonneg` and holds at every real `β`. The
Schwinger form of `osDataOfReflForm` at the Wilson instance is therefore the Gibbs reflected pairing
of the chosen observables, and `osData_bounded`, `osData_S_ne_zero` and `osData_test_nontrivial`
apply to it.

`transl` is the identity and `E4` is divisible, so `os1` holds of every bilinear form here
(`LatticeTranslNoGo.os1_holds_of_everything_when_transl_trivial`). The Euclidean invariance a
continuum theory carries lives in the limit, not at a finite periodic extent.

## Separation

`os_nontriv` asks that one family member have nonzero self-pairing, which a one-element family
satisfies; at `v = ![1]` the Schwinger form takes the single value `P.form 1 1`, and that is
`WightmanData.trivialOSData` in different clothes. `WightmanData.osData_test_nontrivial` does not
exclude it, because it is about the test space rather than the form.

`osDataOfReflForm_separates` is the statement about the form: two family members with different
self-pairings give two different values of `S`. `osDataOfReflForm_constant_of_no_separation` records
the other case explicitly, so the degenerate family is visible rather than unmentioned. Which
observables separate the Gibbs form is a fact about the measure and stays the caller's.
-/

namespace MassGap.WilsonOS

open MassGap.WightmanData

section Generic

variable {A : Type*} [AddCommGroup A] [Module ℝ A] {k : ℕ}

/-- The linear combination `∑ i, c i • v i` of a finite family `v` with coefficients `c`. The bridge
between the coefficient space an `OSData` can carry a norm on and the module a `Transfer.ReflForm`
lives on.

DERIVED: no numeral. `k` is the family's size, the caller's. -/
noncomputable def combo (v : Fin k → A) (c : EuclideanSpace ℝ (Fin k)) : A := ∑ i, c i • v i

/-- `combo` is additive in the coefficients: the sum splits and `add_smul` distributes.

DERIVED: no numeral. -/
theorem combo_add (v : Fin k → A) (c c' : EuclideanSpace ℝ (Fin k)) :
    combo v (c + c') = combo v c + combo v c' := by
  simp [combo, add_smul, Finset.sum_add_distrib]

/-- `combo` is homogeneous in the coefficients, by `Finset.smul_sum` and `smul_smul`.

DERIVED: no numeral. `r` is the caller's scalar. -/
theorem combo_smul (v : Fin k → A) (r : ℝ) (c : EuclideanSpace ℝ (Fin k)) :
    combo v (r • c) = r • combo v c := by
  simp [combo, Finset.smul_sum, smul_smul]

/-- `combo v (EuclideanSpace.single i 1) = v i`: the family is recovered at the coordinate vectors,
which is what makes the non-degeneracy witness a statement about one family member.

DERIVED: `1` is the coefficient at the single occupied coordinate, so that the combination is the
family member itself rather than a multiple of it. -/
theorem combo_single (v : Fin k → A) (i : Fin k) :
    combo v (EuclideanSpace.single i (1 : ℝ)) = v i := by
  simp [combo, PiLp.single_apply]

/-- The Gram form of a finite family under a `Transfer.ReflForm`, as a bilinear map on the
coefficient space. The four bilinearity obligations come from `combo`'s linearity composed with
`PreForm`'s own, on each side.

DERIVED: no numeral. -/
noncomputable def gram (P : MassGap.Transfer.ReflForm A) (v : Fin k → A) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun c c' => P.form (combo v c) (combo v c'))
    (fun c₁ c₂ c' => by rw [combo_add, P.form_add_left])
    (fun r c c' => by rw [combo_smul, P.form_smul_left]; rfl)
    (fun c c₁ c₂ => by rw [combo_add, P.toPreForm.form_add_right])
    (fun r c c' => by rw [combo_smul, P.toPreForm.form_smul_right]; rfl)

/-- `gram` as a continuous bilinear map. The coefficient space is finite-dimensional, so every linear
map out of it is continuous (`LinearMap.toContinuousLinearMap`) and the conversion is applied once in
each argument.

DERIVED: no numeral. -/
noncomputable def gramL (P : MassGap.Transfer.ReflForm A) (v : Fin k → A) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap (gram P v c)
      map_add' := by
        intro c₁ c₂
        ext c'
        simp [gram, LinearMap.mk₂_apply]
      map_smul' := by
        intro r c
        ext c'
        simp [gram, LinearMap.mk₂_apply] }

/-- `gramL P v c c' = P.form (combo v c) (combo v c')`: the continuous form evaluates to the
underlying pairing, by `rfl`. The alignment check that `gramL` adds continuity and nothing else.

DERIVED: no numeral. -/
theorem gramL_apply (P : MassGap.Transfer.ReflForm A) (v : Fin k → A)
    (c c' : EuclideanSpace ℝ (Fin k)) :
    gramL P v c c' = P.form (combo v c) (combo v c') := rfl

/-- **An `OSData` whose Schwinger form is a `Transfer.ReflForm` evaluated on a finite family.**

`Test` is the coefficient space `EuclideanSpace ℝ (Fin k)`, `S` is `gramL`, `theta` and `transl` are
the identity, `os2` is `P.form_nonneg`, `os3` is `P.form_symm`, and `os_nontriv` is the hypothesis
`hi` transported to the coordinate vector at `i₀` by `combo_single`.

The reflection is inside `P.form`, which is the pairing of a reflected observable against an
unreflected one, so `os2` reads `0 ≤ P.form (combo v f) (combo v f)` — the reflection positivity the
`ReflForm` interface carries.

DERIVED: `1` is the coefficient of the coordinate vector supplied as the non-degeneracy witness, the
value at which `combo_single` returns the family member `v i₀`. `0` is the lower bound in `os2` and
the value `os_nontriv` requires the reflected form to avoid. Both are the structure's own
obligations; `k`, `v` and `i₀` are the caller's. -/
noncomputable def osDataOfReflForm (P : MassGap.Transfer.ReflForm A) (v : Fin k → A) (i₀ : Fin k)
    (hi : P.form (v i₀) (v i₀) ≠ 0) : OSData where
  Test := EuclideanSpace ℝ (Fin k)
  theta := ContinuousLinearMap.id ℝ _
  theta_invol := fun _ => rfl
  S := gramL P v
  transl := fun _ => ContinuousLinearMap.id ℝ _
  transl_zero := fun _ => rfl
  transl_add := fun _ _ _ => rfl
  os1 := fun _ _ _ => rfl
  os2 := fun f => P.form_nonneg (combo v f)
  os3 := fun f g => P.form_symm (combo v f) (combo v g)
  os_nontriv := by
    refine ⟨EuclideanSpace.single i₀ (1 : ℝ), ?_⟩
    simp only [ContinuousLinearMap.id_apply, gramL_apply, combo_single]
    exact hi

#print axioms osDataOfReflForm

/-- The Schwinger form of `osDataOfReflForm` is the `ReflForm`'s own pairing on the combinations, so
the physics the form carries is readable off the constructed data rather than hidden by it.

DERIVED: `0` is the value `hi` requires the self-pairing at `i₀` to differ from, `os_nontriv`'s own
obligation carried in from `osDataOfReflForm`. No other numeral occurs. -/
theorem osDataOfReflForm_S (P : MassGap.Transfer.ReflForm A) (v : Fin k → A) (i₀ : Fin k)
    (hi : P.form (v i₀) (v i₀) ≠ 0) (c c' : EuclideanSpace ℝ (Fin k)) :
    (osDataOfReflForm P v i₀ hi).S c c' = P.form (combo v c) (combo v c') := rfl

#print axioms osDataOfReflForm_S

/-- **The form takes two different values.** If two family members have different self-pairings under
`P`, the Schwinger form of `osDataOfReflForm` separates their coordinate vectors.

`os_nontriv` asks only that one member have nonzero self-pairing, which a one-element family
satisfies; at `v = ![1]` the form takes the single value `P.form 1 1`, and that is
`WightmanData.trivialOSData` in different clothes. `WightmanData.osData_test_nontrivial` does not
exclude it — it says the test space has two elements, which holds whatever the form does.

This says the form is not constant, which is the statement a construction claiming to carry a
measure's content should make. The separating pair `i₀`, `j` is the caller's: which observables
separate the Gibbs form is a fact about the measure, not about this construction.

DERIVED: `1` is the coefficient of each coordinate vector, at which `combo_single` returns the
family member itself. `0` is the value `hi` requires the self-pairing at `i₀` to differ from, which
is `os_nontriv`'s own obligation carried in from `osDataOfReflForm`. -/
theorem osDataOfReflForm_separates (P : MassGap.Transfer.ReflForm A) (v : Fin k → A) (i₀ : Fin k)
    (hi : P.form (v i₀) (v i₀) ≠ 0) (j : Fin k)
    (hne : P.form (v j) (v j) ≠ P.form (v i₀) (v i₀)) :
    (osDataOfReflForm P v i₀ hi).S (EuclideanSpace.single j (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ))
      ≠ (osDataOfReflForm P v i₀ hi).S (EuclideanSpace.single i₀ (1 : ℝ))
        (EuclideanSpace.single i₀ (1 : ℝ)) := by
  rw [osDataOfReflForm_S, osDataOfReflForm_S, combo_single, combo_single]
  exact hne

#print axioms osDataOfReflForm_separates

/-- The contrapositive, as a scope note with a proof: a family on which the form is constant gives
an `OSData` whose Schwinger form carries one number. Stated so the degenerate case is visible rather
than merely unmentioned.

DERIVED: `1` is the coordinate vectors' coefficient, carried from `osDataOfReflForm_separates`. `0`
is the value `hi` requires the self-pairing at `i₀` to differ from, `os_nontriv`'s obligation. -/
theorem osDataOfReflForm_constant_of_no_separation (P : MassGap.Transfer.ReflForm A)
    (v : Fin k → A) (i₀ : Fin k) (hi : P.form (v i₀) (v i₀) ≠ 0)
    (hconst : ∀ j : Fin k, P.form (v j) (v j) = P.form (v i₀) (v i₀)) (j : Fin k) :
    (osDataOfReflForm P v i₀ hi).S (EuclideanSpace.single j (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ))
      = P.form (v i₀) (v i₀) := by
  rw [osDataOfReflForm_S, combo_single]
  exact hconst j

#print axioms osDataOfReflForm_constant_of_no_separation


end Generic

section Wilson

open MassGap.ReflectionStrong MassGap.LogConvex MassGap.ActionSplit MassGap.WilsonHypercubic

variable {d n N : ℕ} [NeZero n]

/-- The slab algebra the Gibbs reflected form lives on: `LogConvex.localObs` at the two blocks
`ActionSplit.blkS` and `blkR` of the reflection plane, as a submodule of the real observables of an
`SU N` configuration. Named with `d`, `n` and `N` explicit so the gauge group is pinned by the type
rather than left to unification.

DERIVED: no numeral. `τ`, `a` and `m` are the reflection geometry's, the caller's. -/
noncomputable abbrev slabMod (d n N : ℕ) [NeZero n] (τ : Fin d) (a : Fin n) (m : ℕ) :
    Submodule ℝ ((Link d n → MassGap.SUN.SU N) → ℝ) :=
  localObs (blkS τ a m) (blkR τ a m)

/-- The constant observable of the slab algebra, the vacuum vector of the Gibbs reflected form.
`wilsonGibbsReflForm_vac_norm` evaluates the form at it.

DERIVED: `1` is the constant's value, which is what makes it the algebra's unit; `one_mem_localObs`
is the membership. -/
noncomputable def slabOne (d n N : ℕ) [NeZero n] (τ : Fin d) (a : Fin n) (m : ℕ) :
    ↥(slabMod d n N τ a m) :=
  ⟨fun _ => (1 : ℝ), one_mem_localObs⟩

/-- **Osterwalder–Schrader data built on the `SU(N)` Wilson Gibbs reflected form.**

`osDataOfReflForm` at `ReflectionStrong.wilsonGibbsReflForm`, on a family of slab observables whose
first member is the constant. Non-degeneracy is `wilsonGibbsReflForm_vac_norm`, which evaluates the
form at the constant and reads `1`.

Every field of the resulting `OSData` is therefore settled by a Wilson theorem or by the identity:
the Schwinger form is the Gibbs pairing of the chosen observables against their reflections, divided
by the partition function; reflection positivity is `wilsonGibbsReflForm`'s `form_nonneg`, which
carries no restriction on the coupling; and `transl` is the identity, the value
`LatticeTranslNoGo.transl_eq_id_of_finite_order` forces on a lattice whose translations have finite
order.

DERIVED: `0` indexes the family member required to be the constant and appears in `0 < m`, the
even-extent condition `wilsonGibbsReflForm` carries. `1` is the value the form takes at the constant
(`wilsonGibbsReflForm_vac_norm`) and the offset in `Fin (k + 1)`, which makes the family nonempty so
that index `0` exists. `2` in `n = 2 * m` is the reflection geometry's, carried from
`wilsonGibbsReflForm` unchanged. `k`, `τ`, `a`, `m`, `β` and `v` are the caller's. -/
noncomputable def wilsonOSData (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (k : ℕ)
    (v : Fin (k + 1) → ↥(slabMod d n N τ a m)) (hv : v 0 = slabOne d n N τ a m) : OSData :=
  osDataOfReflForm (wilsonGibbsReflForm hN τ a m hm hm0 β) v 0
    (by
      have h : (wilsonGibbsReflForm hN τ a m hm hm0 β).form (v 0) (v 0) = 1 := by
        rw [hv]
        exact wilsonGibbsReflForm_vac_norm hN τ a m hm hm0 β
      rw [h]
      exact one_ne_zero)

#print axioms wilsonOSData

/-- The Schwinger form of `wilsonOSData` is the Wilson Gibbs reflected pairing on the combinations of
the chosen observables.

DERIVED: `1` is the offset in `Fin (k + 1)` and `0` the index of the constant member, both carried
from `wilsonOSData`; `2` in `n = 2 * m` is the reflection geometry's. -/
theorem wilsonOSData_S (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (k : ℕ)
    (v : Fin (k + 1) → ↥(slabMod d n N τ a m)) (hv : v 0 = slabOne d n N τ a m) (c c' : EuclideanSpace ℝ (Fin (k + 1))) :
    (wilsonOSData hN τ a m hm hm0 β k v hv).S c c'
      = (wilsonGibbsReflForm hN τ a m hm hm0 β).form (combo v c) (combo v c') := rfl

#print axioms wilsonOSData_S

/-- The test space of `wilsonOSData` has at least two elements — `osData_test_nontrivial` at this
instance, so the construction is not a subsingleton dressed as a theory.

DERIVED: `1` is the offset in `Fin (k + 1)` and `0` the index of the constant member, both carried
from `wilsonOSData`; `2` in `n = 2 * m` is the reflection geometry's. -/
theorem wilsonOSData_test_nontrivial (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (k : ℕ)
    (v : Fin (k + 1) → ↥(slabMod d n N τ a m)) (hv : v 0 = slabOne d n N τ a m) :
    Nontrivial (wilsonOSData hN τ a m hm hm0 β k v hv).Test :=
  osData_test_nontrivial _

#print axioms wilsonOSData_test_nontrivial

/-- **The Wilson measure reaches `WightmanQFTData`.** `os_reconstruction_wightman` applied to
`wilsonOSData`, with `Nontrivial` on both the test space and the reconstructed space from
`os_reconstruction_wightman_is_not_vacuous`.

The axiom is the cited Osterwalder–Schrader reconstruction; what this adds is that its argument is
now the `SU(N)` Wilson Gibbs reflected form rather than a form with no physics in it.

DERIVED: `1` is the offset in `Fin (k + 1)` and `0` the index of the constant member, both carried
from `wilsonOSData`; `2` in `n = 2 * m` is the reflection geometry's. -/
theorem wilson_reconstructed_nontrivial (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (k : ℕ)
    (v : Fin (k + 1) → ↥(slabMod d n N τ a m)) (hv : v 0 = slabOne d n N τ a m) :
    Nontrivial (wilsonOSData hN τ a m hm hm0 β k v hv).Test ∧
      Nontrivial (os_reconstruction_wightman
        (wilsonOSData hN τ a m hm hm0 β k v hv)).Space :=
  os_reconstruction_wightman_is_not_vacuous _

#print axioms wilson_reconstructed_nontrivial

/-- The reconstructed Hamiltonian annihilates the vacuum at the Wilson instance —
`reconstructed_vacuum_energy_zero` read at `wilsonOSData`.

DERIVED: `0` is the value the Hamiltonian takes at the vacuum and the index of the constant member;
`1` is the offset in `Fin (k + 1)`; `2` in `n = 2 * m` is the reflection geometry's. -/
theorem wilson_reconstructed_vacuum_energy_zero (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (k : ℕ)
    (v : Fin (k + 1) → ↥(slabMod d n N τ a m)) (hv : v 0 = slabOne d n N τ a m) :
    (os_reconstruction_wightman (wilsonOSData hN τ a m hm hm0 β k v hv)).qft.ham
        (os_reconstruction_wightman (wilsonOSData hN τ a m hm hm0 β k v hv)).qft.vac = 0 :=
  reconstructed_vacuum_energy_zero _

#print axioms wilson_reconstructed_vacuum_energy_zero

end Wilson

end MassGap.WilsonOS
