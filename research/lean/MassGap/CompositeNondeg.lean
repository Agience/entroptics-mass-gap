import Mathlib
import MassGap.MultiScaleAll

/-!
# MassGap.CompositeNondeg — the off-tensor composites of `CbR 2 z` and `CompNondeg`

## 1. What is proved

* **`ren_off_bR`, `ren_off`**: at an index `i` with `dec i.1 = none` (off the tensor indices) the composite
  field of `CbR 2 z` at step `k` is the bare field `bR 2 i` (`renF_of_none`), so it depends neither on `z` nor
  on `k`.
* **`latC_off`**: a family supported on such indices has the same lattice reading in `CbR 2 z` and
  `CbR 2 z'`, at every step.
* **`not_compNondeg_single`**: for any composites `C`, `CompNondeg C` fails when one index `i` has an on-shell
  classical value (`g^{cnF} cval g A ≠ 0` at an admissible on-shell `A`) and every separated two-point reading
  `contC (![(i, f), (i, h)])` of continuous test functions is `0`.
* **`not_compNondeg_of_vanish`**: for every `z`, `CompNondeg (CbR 2 z)` fails as soon as one off-tensor index
  with an on-shell classical value has separated two-point lattice readings in `CbR 2 zOne` tending to `0`
  along `ultra`.

## 2. What is argued (no declaration)

* **The vanishing.** The off-tensor composites are the bare fields `bR 2 i`: dimensionless lattice operators
  with no renormalisation factor, of size `a^{4}` or smaller (mixing with `tr F²`). Their separated two-point
  functions are expected to vanish as `a → 0` (`a^{d_i + d_j}` times a finite renormalised correlator). With
  that vanishing, `not_compNondeg_of_vanish` makes `CompNondeg` fail for every capstone whose composites are
  `build (rhoD …) (bareD …)`: `MultiScale`, `ScaleControlFull`, `MultiScaleAll`, `ObserverConsistency`,
  `ObserverReads`, `InputsTriage`, `ReflAvg`, `ZCanon`, `NonGaussLink`, `ClaySUBest`. The `comp` input of each
  is then unsatisfiable at every `z`, not only at `zOne`.
* **The target is not at fault.** `RenTri` allows `k`-dependent combinations of `lowSpan`, so a composite
  family whose fields carry the renormalisation is admissible for the target; the defect is in the family
  `build (rhoD …) (bareD …)`, which fixes the off-tensor fields bare.
* **The fix.** A composite family with `ren k i ≈ a_k^{−cdim i} (bare i − lower-dimension mixing)`: the
  physical-unit field with its lower-dimension mixing subtracted, whose separated two-point functions have a
  finite non-zero limit.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)` and the two points of the two-point reading; `1` the coefficient of the
single-index combination; `0` the vanishing limit.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CompositeNondeg

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositesBuild MassGap.ClayData MassGap.ReflAvg
  MassGap.MultiScaleAll MassGap.ObserverEnergyBox
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

/-- **Off the tensor indices the composite field of `CbR 2 z` is the bare field `bR 2 i`**, at every `z` and
every step. -/
theorem ren_off_bR (z : Chan → ℕ → ℝ) {i : Ix0} (hd : dec i.1 = none) (k : ℕ) :
    (CbR 2 z).ren k i = bR 2 i := by
  show renF _ _ k i = _
  rw [renF_of_none _ _ hd]
  show (match dec i.1 with
    | some α => bareT (fR 2) α
    | none => bR 2 i) = _
  rw [hd]

/-- Off the tensor indices the composite field of `CbR 2 z` does not depend on `z` or on `k`. -/
theorem ren_off (z z' : Chan → ℕ → ℝ) {i : Ix0} (hd : dec i.1 = none) (k k' : ℕ) :
    (CbR 2 z).ren k i = (CbR 2 z').ren k' i := by
  show renF _ _ k i = renF _ _ k' i
  rw [renF_of_none _ _ hd, renF_of_none _ _ hd]

/-- **A family on off-tensor indices reads the same in `CbR 2 z` and `CbR 2 z'`**, at every step. -/
theorem latC_off (z z' : Chan → ℕ → ℝ) {ι : Type} [Fintype ι] (F : ι → CDatum (CbR 2 z))
    (hF : ∀ j, dec (F j).1.1 = none) (k : ℕ) :
    latC h2N (CbR 2 z) k F = latC h2N (CbR 2 z') k F := by
  unfold latC cField
  congr 1
  funext j
  rw [ren_off z z' (hF j) k k]

/-- **`CompNondeg C` fails when one index with an on-shell classical value has vanishing separated
two-point readings.** -/
theorem not_compNondeg_single (C : Composites 2) [DecidableEq C.Ix] (i : C.Ix)
    (hon : ∃ (A : GPot 2) (g : ℝ), GPot.Adm A ∧ OnShell g A ∧ g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0)
    (hzero : ∀ f h : TestFn, Continuous f.1 → Continuous h.1 →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h) →
      contC h2N C (![(i, f), (i, h)] : Fin 2 → CDatum C) = 0) :
    ¬ CompNondeg h2N C := by
  intro H
  have hsupp : (Finsupp.single i (1 : ℝ)).support = {i} := Finsupp.support_single _ one_ne_zero
  obtain ⟨A, g, hA, hos, hne⟩ := hon
  obtain ⟨f, h, hf, hh, hsep, hne2⟩ := H (Finsupp.single i 1) ⟨A, g, hA, hos, by
    rw [hsupp, Finset.sup_singleton, Finset.filter_singleton, if_pos rfl, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    exact hne⟩
  apply hne2
  rw [hsupp, Finset.sum_singleton, Finset.sum_singleton, Finsupp.single_eq_same, one_mul, one_mul]
  exact hzero f h hf hh hsep

/-- **`CompNondeg (CbR 2 z)` fails, at every `z`, as soon as one off-tensor index has an on-shell
classical value and its separated two-point readings vanish in the limit.** -/
theorem not_compNondeg_of_vanish (z : Chan → ℕ → ℝ) (i : Ix0) (hd : dec i.1 = none)
    (hon : ∃ (A : GPot 2) (g : ℝ), GPot.Adm A ∧ OnShell g A ∧ g ^ cnF i.1 * cval g A i.1 ≠ 0)
    (hvan : ∀ f h : TestFn, Continuous f.1 → Continuous h.1 →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h) →
      Tendsto (fun k => latC h2N (CbR 2 zOne) k (![(i, f), (i, h)] : Fin 2 → CDatum (CbR 2 zOne)))
        (ultra : Filter ℕ) (𝓝 0)) :
    ¬ CompNondeg h2N (CbR 2 z) := by
  classical
  refine not_compNondeg_single (CbR 2 z) i hon fun f h hf hh hsep => ?_
  have e : (fun k => latC h2N (CbR 2 z) k (![(i, f), (i, h)] : Fin 2 → CDatum (CbR 2 z)))
      = fun k => latC h2N (CbR 2 zOne) k (![(i, f), (i, h)] : Fin 2 → CDatum (CbR 2 zOne)) := by
    funext k
    exact latC_off z zOne _ (fun j => by fin_cases j <;> exact hd) k
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold contC
  rw [e]
  exact (hvan f h hf hh hsep).limUnder_eq

end MassGap.CompositeNondeg

end

#print axioms MassGap.CompositeNondeg.ren_off_bR
#print axioms MassGap.CompositeNondeg.ren_off
#print axioms MassGap.CompositeNondeg.latC_off
#print axioms MassGap.CompositeNondeg.not_compNondeg_single
#print axioms MassGap.CompositeNondeg.not_compNondeg_of_vanish
