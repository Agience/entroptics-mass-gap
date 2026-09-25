import Mathlib
import MassGap.ContinuumField
import MassGap.AsymptoticScaling

noncomputable section

/-!
# MassGap.ContinuumSchwinger — renormalised Schwinger functions of the Wilson theory with running
coupling, and their limit

## The family

`dyBeta hN k` is a coupling at which the two-loop running spacing of `SU(N)` is the dyadic value
`aRun N (dyBeta hN k) = dySpacing N k = aRun N 1 / 2^(k+1)` (`aRun_dyBeta`, from
`AsymptoticScaling.exists_beta_aRun_eq`), with `dyBeta hN k → ∞` (`tendsto_dyBeta`). At step `k` the
state is `stateK hN k = PeriodicState.periodicState hN (dyBeta hN k)` — the periodic infinite-volume
Wilson state, reflection invariant at every constant, shift invariant in all four directions,
reflection positive — and the spacing is `aRun N (dyBeta hN k)`: the coupling runs with the spacing.

## Schwinger functions

For a finite family `F : ι → LField × TestFn`, `latS ν a F = ν (∏ᵢ smear a Oᵢ fᵢ)` and
`latSk hN k F` is it at step `k`. Renormalisation is data: `ρ : Renorm N` gives at each step a
factor `Z k O` and a subtraction `c k O`, and the field `O` enters as `Z k O · (O − c k O · 1)`
(`latSkR`). `Renorm.connected hN Z` subtracts the step-`k` expectation, the composite
`Z(β) · (X − ν X)`; `Renorm.bare` is `Z = 1`, `c = 0`.

`contS hN ρ F` is `limUnder` of `latSkR hN ρ k F` along one non-principal ultrafilter
`ultra ≤ atTop`, the same for every family. It is the limit along `ultra` whenever the sequence is
bounded on some set of `ultra`, and an unspecified real when the sequence diverges along `ultra`;
`UniformBound` rules the second case out for every family.

## The open input, stated

`UniformBound hN ρ`: for every family there is one constant bounding the renormalised lattice
Schwinger functions eventually in the step, whatever dyadic translation is applied to each factor.
`uniformBound_of_bounded` proves it whenever `Z` and `c` are bounded in the step — in particular for
`Renorm.bare` (`uniformBound_bare`) and for `Renorm.connected` at bounded `Z`
(`uniformBound_connected`). At bounded data each smeared field is a Riemann sum of a local field
over about `a⁻⁴` cells, and the limit is expected to be degenerate: constants for the bare
fields, zero for the connected composites (`uniformBound_connected`,
`ContinuumReconstruction.continuum_reconstruction_bare`). A non-degenerate limit needs `Z` growing
with the step, where `UniformBound` is not proved; since it quantifies over every family, including
families whose test functions overlap, it is expected there to need restricting to families with
separated supports (see `UniformBound`).

## What the limit satisfies

* **existence** `tendsto_contS`, under `UniformBound`;
* **bound (OS0)** `exists_abs_contS_le`, under `UniformBound`: a bound per family, uniform over
  dyadic translations of the factors, with no continuity in the test functions stated;
  `abs_contS_le_of_bounded`: the explicit bound `∏ Bᶻ · ∏ (‖O‖ + Bᶜ) M (2R + 3)⁴` at bounded data;
* **symmetry (OS3)** `contS_comp_equiv`, unconditional as an identity of `limUnder` values;
* **translations (OS1)** `contS_translate`, unconditional as an identity of `limUnder` values:
  invariance under translating every test function by `dySpacing N m · n`, `n ∈ ℤ⁴`, `m ∈ ℕ` — the
  dyadic subgroup `aRun N 1 · 2^{-(m+1)} ℤ⁴`, dense in `ℝ⁴`, in all four directions;
  `contS_reflect`: invariance under the reflection of each axis, at reflection-compatible data;
* **reflection positivity (OS2)** `contS_gram_nonneg`, under `UniformBound` and
  `Renorm.ReflCompat`: `∑_{P,Q} c_P c_Q S(θP ∪ Q) ≥ 0` over positive-time monomials; `kern_symm`:
  `S(θP ∪ Q) = S(θQ ∪ P)`;
* **clustering (OS4)** `contS_cluster`, `contS_cluster_tendsto`, under `UniformBound` and
  `UniformClustering` (decay of the lattice connected functions at a physical rate uniform in the
  step); `ContinuumCluster.contS_cluster_of_fixedWindowDecay` derives the reflected form of it from
  `WeakCouplingWindow.FixedWindowDecay`;
* **rotations** `RotationInvariant` is stated, not derived.

The unconditional identities (`contS_comp_equiv`, `contS_translate`, `contS_reflect`, `kern_symm`)
equate `limUnder` values of sequences that agree eventually. They say something about the lattice
functions where `contS` is a limit, which `UniformBound` secures for every family.

## Scope

`UniformBound`, `UniformClustering` and `RotationInvariant` are stated and not proved in general.
Translation invariance is proved on the dyadic subgroup of translations, not on all of `ℝ⁴`.
-/

namespace MassGap.ContinuumSchwinger

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField Filter
open scoped Topology

variable {N : ℕ}

/-- DERIVED: `1` is the least colour count; `0` is the excluded one. -/
theorem one_le_of_ne_zero (hN : N ≠ 0) : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN

/-! ## 1. Couplings at dyadic running spacings -/

section Couplings

/-- The dyadic spacing `aRun N 1 / 2^(k+1)`.

DERIVED: `2` the halving per step; `k + 1` makes step `0` already a halving. CHOSEN: the reference
coupling `1`, where `aRun N` is positive; any positive reference coupling serves. -/
noncomputable def dySpacing (N : ℕ) (k : ℕ) : ℝ := AsymptoticScaling.aRun N 1 / 2 ^ (k + 1)

/-- DERIVED: `0` is the sign; `1` the least colour count. -/
theorem dySpacing_pos (hN : 1 ≤ N) (k : ℕ) : 0 < dySpacing N k :=
  div_pos (AsymptoticScaling.aRun_pos hN one_pos) (by positivity)

/-- DERIVED: `1` is the reference coupling and the least colour count; `2` the halving. -/
theorem dySpacing_lt (hN : 1 ≤ N) (k : ℕ) : dySpacing N k < AsymptoticScaling.aRun N 1 :=
  div_lt_self (AsymptoticScaling.aRun_pos hN one_pos)
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega))

/-- `dySpacing N k · 2^(k-m) = dySpacing N m` for `m ≤ k`.

DERIVED: `2` is the halving. -/
theorem dySpacing_mul_pow (N : ℕ) {m k : ℕ} (hmk : m ≤ k) :
    dySpacing N k * 2 ^ (k - m) = dySpacing N m := by
  unfold dySpacing
  have h : (2 : ℝ) ^ (k + 1) = 2 ^ (k - m) * 2 ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h, div_mul_eq_mul_div, mul_comm (AsymptoticScaling.aRun N 1),
    mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]

/-- DERIVED: `0` is the limit of the spacing. -/
theorem tendsto_dySpacing (N : ℕ) : Tendsto (dySpacing N) atTop (𝓝 0) := by
  have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat 1)
  exact Tendsto.div_atTop tendsto_const_nhds h2

/-- A coupling `≥ 1` at which the running spacing is `dySpacing N k`.

DERIVED: `1` is the reference coupling. -/
theorem exists_coupling (hN : 1 ≤ N) (k : ℕ) :
    ∃ β : ℝ, 1 ≤ β ∧ AsymptoticScaling.aRun N β = dySpacing N k :=
  AsymptoticScaling.exists_beta_aRun_eq hN (dySpacing_pos hN k) (dySpacing_lt hN k)

/-- **The coupling of step `k`.**

DERIVED: `1` is the least colour count. -/
noncomputable def dyBeta (hN : 1 ≤ N) (k : ℕ) : ℝ := (exists_coupling hN k).choose

/-- DERIVED: `1` is the reference coupling. -/
theorem one_le_dyBeta (hN : 1 ≤ N) (k : ℕ) : 1 ≤ dyBeta hN k :=
  (exists_coupling hN k).choose_spec.1

/-- **The spacing runs with the coupling**: `aRun N (dyBeta hN k) = dySpacing N k`.

DERIVED: `1` is the least colour count. -/
theorem aRun_dyBeta (hN : 1 ≤ N) (k : ℕ) :
    AsymptoticScaling.aRun N (dyBeta hN k) = dySpacing N k :=
  (exists_coupling hN k).choose_spec.2

/-- **The couplings tend to infinity.** On `[1, max B 1]` the positive continuous `aRun N` has a
positive minimum, which `dySpacing N k` eventually undercuts.

DERIVED: `1` is the reference coupling and the least colour count. -/
theorem tendsto_dyBeta (hN : 1 ≤ N) : Tendsto (dyBeta hN) atTop atTop := by
  refine Filter.tendsto_atTop.mpr (fun B => ?_)
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max B 1)).exists_isMinOn
    ⟨1, le_refl 1, le_max_right B 1⟩ (AsymptoticScaling.continuous_aRun N).continuousOn
  have hm : 0 < AsymptoticScaling.aRun N x :=
    AsymptoticScaling.aRun_pos hN (lt_of_lt_of_le one_pos hx.1)
  have hev : ∀ᶠ k in atTop, dySpacing N k < AsymptoticScaling.aRun N x :=
    (tendsto_dySpacing N).eventually (gt_mem_nhds hm)
  filter_upwards [hev] with k hk
  by_contra hlt
  push_neg at hlt
  have hmem : dyBeta hN k ∈ Set.Icc (1 : ℝ) (max B 1) :=
    ⟨one_le_dyBeta hN k, hlt.le.trans (le_max_left B 1)⟩
  have h1 := isMinOn_iff.mp hmin _ hmem
  rw [aRun_dyBeta] at h1
  linarith

#print axioms tendsto_dyBeta

/-- The lattice vector `c · n`.

DERIVED: no numeral. -/
def scaleSite (c : ℤ) (n : ISite) : ISite := fun i => c * n i

/-- The site `dySpacing N m · n` is the site `dySpacing N k · (2^(k-m) n)` for `m ≤ k`: a dyadic
physical vector is a lattice vector at every finer step.

DERIVED: `2` is the halving. -/
theorem site_dySpacing (N : ℕ) {m k : ℕ} (hmk : m ≤ k) (n : ISite) :
    site (dySpacing N m) n = site (dySpacing N k) (scaleSite (2 ^ (k - m)) n) := by
  funext i
  simp only [site, scaleSite]
  push_cast
  rw [← dySpacing_mul_pow N hmk]
  ring

end Couplings

/-! ## 2. Lattice Schwinger functions and their bound -/

section Lattice

/-- The configuration space of `SU(N)` on `ℤ⁴`.

DERIVED: no numeral. -/
abbrev Cfg (N : ℕ) : Type := IConf (MassGap.SUN.SU N)

/-- A smeared-field datum: a local gauge-invariant field and a test function.

DERIVED: no numeral. -/
abbrev SField (N : ℕ) : Type := LField (MassGap.SUN.SU N) × TestFn

/-- **The lattice Schwinger function** of the family `F` in the state `ν` at spacing `a`:
`ν (∏ᵢ smear a Oᵢ fᵢ)`.

DERIVED: no numeral. -/
noncomputable def latS (ν : MassGap.DLRLimit.State (Cfg N)) (a : ℝ) {ι : Type} [Fintype ι]
    (F : ι → SField N) : ℝ :=
  ν (∏ i, smear a (F i).1.1 (F i).2)

/-- The state of step `k`: the periodic Wilson state at the coupling `dyBeta k`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def stateK (hN : N ≠ 0) (k : ℕ) : MassGap.DLRLimit.State (Cfg N) :=
  PeriodicState.periodicState hN (dyBeta (one_le_of_ne_zero hN) k)

/-- **The Schwinger function of step `k`**: `stateK hN k` at spacing `aRun N (dyBeta k)`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def latSk (hN : N ≠ 0) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) : ℝ :=
  latS (stateK hN k) (AsymptoticScaling.aRun N (dyBeta (one_le_of_ne_zero hN) k)) F

/-- DERIVED: `0` is the excluded colour count. -/
theorem latSk_eq (hN : N ≠ 0) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSk hN k F = latS (stateK hN k) (dySpacing N k) F := by
  unfold latSk
  rw [aRun_dyBeta]

/-- `‖∏ Pᵢ‖ ≤ ∏ ‖Pᵢ‖` in `C(X, ℝ)`.

DERIVED: `1` is the unit, of norm at most one. -/
theorem norm_prod_le_prod {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}
    (s : Finset ι) (P : ι → C(X, ℝ)) : ‖∏ i ∈ s, P i‖ ≤ ∏ i ∈ s, ‖P i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact (ContinuousMap.norm_le _ zero_le_one).mpr (fun x => by simp)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- **The lattice bound, uniform in the spacing** (OS0 at the lattice level), with every factor
translated by its own lattice vector `a · nᵢ`: at every `0 < a ≤ 1`,
`|latS ν a F'| ≤ ∏ᵢ ‖Oᵢ‖ · Mᵢ (2Rᵢ + 3)⁴`, the bound of the untranslated family.

DERIVED: `0` is the sign of `a`; `2` and `3` are `ContinuumField.norm_smear_le`'s; `4` the
dimension; `1` bounds `a`. -/
theorem abs_latS_translate_le (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) {ι : Type} [Fintype ι] (F : ι → SField N) (n : ι → ISite) (R M : ι → ℝ)
    (hRM : ∀ i, IsTest (F i).2.1 (R i) (M i)) :
    |latS ν a (fun i => ((F i).1, (F i).2.translate (site a (n i))))|
      ≤ ∏ i, ‖(F i).1.1‖ * (M i * (2 * R i + 3) ^ 4) := by
  calc |latS ν a (fun i => ((F i).1, (F i).2.translate (site a (n i))))|
      ≤ ‖∏ i, smear a (F i).1.1 ((F i).2.translate (site a (n i)))‖ := ν.abs_le_norm _
    _ ≤ ∏ i, ‖smear a (F i).1.1 ((F i).2.translate (site a (n i)))‖ := norm_prod_le_prod _ _
    _ ≤ ∏ i, ‖(F i).1.1‖ * (M i * (2 * R i + 3) ^ 4) := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
        rw [smear_translate ha]
        exact (norm_transObs_le _ _).trans (norm_smear_le ha ha1 _ _ (hRM i))

#print axioms abs_latS_translate_le

/-- **Lattice translation invariance**: in a state invariant under the four unit shifts, translating
every test function by the lattice vector `a · n` leaves the Schwinger function unchanged.

DERIVED: `0` is the sign of `a`; `4` in `Fin 4` is the spacetime dimension, one unit shift per
direction. -/
theorem latS_translate (ν : MassGap.DLRLimit.State (Cfg N))
    (hsh : ∀ (τ : Fin 4) (F : C(Cfg N, ℝ)), ν (MassGap.ReflectionShift.ishiftObsL τ F) = ν F)
    {a : ℝ} (ha : 0 < a) {ι : Type} [Fintype ι] (F : ι → SField N) (n : ISite) :
    latS ν a (fun i => ((F i).1, (F i).2.translate (site a n))) = latS ν a F := by
  show ν (∏ i, smear a (F i).1.1 ((F i).2.translate (site a n)))
    = ν (∏ i, smear a (F i).1.1 (F i).2)
  have h : (∏ i, smear a (F i).1.1 ((F i).2.translate (site a n)))
      = transObs n (∏ i, smear a (F i).1.1 (F i).2) := by
    rw [transObs_prod]
    exact Finset.prod_congr rfl (fun i _ => smear_translate ha _ _ n)
  rw [h, state_transObs hsh]

#print axioms latS_translate

/-- Reindexing a family does not change its lattice Schwinger function.

DERIVED: no numeral. -/
theorem latS_comp_equiv (ν : MassGap.DLRLimit.State (Cfg N)) (a : ℝ) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (e : ι' ≃ ι) (F : ι → SField N) : latS ν a (F ∘ e) = latS ν a F := by
  unfold latS
  congr 1
  exact Equiv.prod_comp e (fun i => smear a (F i).1.1 (F i).2)

end Lattice

/-! ## 3. Renormalisation data -/

section Renorm

/-- **Renormalisation data**: at step `k` the field `O` enters as `Z k O · (O − c k O · 1)`.

DERIVED: `1` is the unit observable. -/
structure Renorm (N : ℕ) where
  /-- The field-strength factor at step `k`. -/
  Z : ℕ → LField (MassGap.SUN.SU N) → ℝ
  /-- The constant subtracted at step `k`. -/
  c : ℕ → LField (MassGap.SUN.SU N) → ℝ

/-- The data do not see the time reflection about `x_τ = 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def Renorm.ReflCompat (ρ : Renorm N) (τ : Fin 4) : Prop :=
  ∀ (k : ℕ) (O : LField (MassGap.SUN.SU N)),
    ρ.Z k (O.refl τ) = ρ.Z k O ∧ ρ.c k (O.refl τ) = ρ.c k O

/-- The bare fields: `Z = 1`, `c = 0`.

DERIVED: `1` and `0` are the identity renormalisation. -/
def Renorm.bare (N : ℕ) : Renorm N := ⟨fun _ _ => 1, fun _ _ => 0⟩

/-- **The connected composites** `Z k O · (O − ν_k(O))`, `ν_k = stateK hN k`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def Renorm.connected (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) :
    Renorm N :=
  ⟨Z, fun k O => stateK hN k O.1⟩

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem Renorm.bare_reflCompat (τ : Fin 4) : (Renorm.bare N).ReflCompat τ :=
  fun _ _ => ⟨rfl, rfl⟩

/-- The subtraction `ν_k(O)` is reflection compatible because the periodic state is reflection
invariant.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The reflection
constant enters in the proof, through `PeriodicState.periodicState_reflInvariant`. -/
theorem Renorm.connected_reflCompat (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O) : (Renorm.connected hN Z).ReflCompat τ :=
  fun k O => ⟨hZ k O,
    PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0 O.1⟩

/-- The renormalised field datum of step `k`.

DERIVED: no numeral. -/
def Renorm.field (ρ : Renorm N) (k : ℕ) (p : SField N) : SField N := (p.1.sub (ρ.c k p.1), p.2)

/-- The product of the field-strength factors of a family.

DERIVED: no numeral. -/
noncomputable def Renorm.pref (ρ : Renorm N) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SField N) : ℝ :=
  ∏ i, ρ.Z k (F i).1

/-- **The renormalised lattice Schwinger function of step `k`**:
`∏ᵢ Z k Oᵢ · ν_k (∏ᵢ smear aₖ (Oᵢ − c k Oᵢ) fᵢ)`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def latSkR (hN : N ≠ 0) (ρ : Renorm N) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SField N) : ℝ :=
  ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))

/-- **The uniform bound (stated; proved at bounded data).** For every family one constant bounds
the renormalised lattice Schwinger functions eventually in the step, whatever dyadic translation is
applied to each factor. The quantifier runs over every family, including families whose test
functions overlap, such as `((O, f), (O, f))`.

It holds at bounded `Z` and `c` (`uniformBound_of_bounded`), where the limit is expected to be
degenerate (`uniformBound_connected`, `ContinuumReconstruction.continuum_reconstruction_bare`). A
non-degenerate limit of a local field needs `Z` growing with the step. There the family
`((O, f), (O, f))` reads `Z²` times the second moment of the smeared field, at least `Z²` times its
variance, the two-point function at coincident points; under the short-distance form `r⁻⁸ (log r)⁻²` of
`ShortDistanceY.AFShortDistance`, which is not integrable at `r = 0` in four dimensions, that family
is expected to be unbounded for `f ≥ 0`, `f ≠ 0`. A bound at growing `Z` is expected to need the
families restricted to separated supports.

DERIVED: `0` is the excluded colour count. -/
def UniformBound (hN : N ≠ 0) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
    ∀ᶠ k in atTop,
      |latSkR hN ρ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C

/-- **The explicit bound at bounded data**, eventually in the step.

DERIVED: `0` is the excluded colour count; `2`, `3`, `4` as in `abs_latS_translate_le`. The spacing
bound enters in the proof, where `dySpacing N k` falls below one. -/
theorem eventually_abs_latSkR_le (hN : N ≠ 0) (ρ : Renorm N)
    (BZ Bc : LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, |ρ.Z k O| ≤ BZ O)
    (hc : ∀ k O, |ρ.c k O| ≤ Bc O) {ι : Type} [Fintype ι] (F : ι → SField N) (R M : ι → ℝ)
    (hRM : ∀ i, IsTest (F i).2.1 (R i) (M i)) (m : ℕ) (n : ι → ISite) :
    ∀ᶠ k in atTop,
      |latSkR hN ρ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))|
        ≤ (∏ i, BZ (F i).1) * ∏ i, (‖(F i).1.1‖ + Bc (F i).1) * (M i * (2 * R i + 3) ^ 4) := by
  filter_upwards [Filter.eventually_ge_atTop m,
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  show |ρ.pref k F * latSk hN k (fun i => ((ρ.field k (F i)).1,
      (ρ.field k (F i)).2.translate (site (dySpacing N m) (n i))))| ≤ _
  rw [abs_mul, latSk_eq]
  have hfam : (fun i => ((ρ.field k (F i)).1,
        (ρ.field k (F i)).2.translate (site (dySpacing N m) (n i))))
      = (fun i => ((ρ.field k (F i)).1, (ρ.field k (F i)).2.translate
          (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))) := by
    funext i
    rw [site_dySpacing N hk]
  rw [hfam]
  have hL := abs_latS_translate_le (stateK hN k) ha hk1.le (fun i => ρ.field k (F i))
    (fun i => scaleSite (2 ^ (k - m)) (n i)) R M hRM
  have hP : |ρ.pref k F| ≤ ∏ i, BZ (F i).1 := by
    unfold Renorm.pref
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hZ k _)
  have hQ : ∏ i, ‖(ρ.field k (F i)).1.1‖ * (M i * (2 * R i + 3) ^ 4)
      ≤ ∏ i, (‖(F i).1.1‖ + Bc (F i).1) * (M i * (2 * R i + 3) ^ 4) := by
    refine Finset.prod_le_prod
      (fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hRM i).M_nonneg (by positivity)))
      (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hRM i).M_nonneg (by positivity))
    exact (norm_sub_smul_one_le (F i).1.1 (ρ.c k (F i).1)).trans
      (by linarith [hc k (F i).1])
  exact mul_le_mul hP (hL.trans hQ) (abs_nonneg _)
    (Finset.prod_nonneg (fun i _ => (abs_nonneg _).trans (hZ 0 _)))

#print axioms eventually_abs_latSkR_le

/-- **`UniformBound` holds at bounded renormalisation data.**

DERIVED: `0` is the excluded colour count. -/
theorem uniformBound_of_bounded (hN : N ≠ 0) (ρ : Renorm N)
    (hZ : ∀ O, ∃ B : ℝ, ∀ k, |ρ.Z k O| ≤ B) (hc : ∀ O, ∃ B : ℝ, ∀ k, |ρ.c k O| ≤ B) :
    UniformBound hN ρ := by
  intro ι _ F
  choose BZ hBZ using hZ
  choose Bc hBc using hc
  have hex : ∀ i, ∃ R M : ℝ, IsTest (F i).2.1 R M := fun i => (F i).2.2
  choose R M hRM using hex
  exact ⟨_, fun m n => eventually_abs_latSkR_le hN ρ BZ Bc (fun k O => hBZ O k)
    (fun k O => hBc O k) F R M hRM m n⟩

#print axioms uniformBound_of_bounded

/-- `UniformBound` for the bare fields. The bare limit is described at
`ContinuumReconstruction.continuum_reconstruction_bare`.

DERIVED: `1` and `0` bound the identity data. -/
theorem uniformBound_bare (hN : N ≠ 0) : UniformBound hN (Renorm.bare N) :=
  uniformBound_of_bounded hN _ (fun _ => ⟨1, fun _ => by simp [Renorm.bare]⟩)
    (fun _ => ⟨0, fun _ => by simp [Renorm.bare]⟩)

/-- `UniformBound` for the connected composites at a bounded field-strength factor: the subtraction
`ν_k(O)` is bounded by `‖O‖`.

Each connected smeared field has mean zero by translation invariance, and Cauchy–Schwarz bounds its
variance by `(M (2R + 3)⁴)²` times the single-site variance `ν_k(O²) − ν_k(O)²`. Where those
variances tend to zero along `ultra`, as expected at weak coupling, every non-empty family has
limit `0` at bounded `Z`.

DERIVED: `0` is the excluded colour count. -/
theorem uniformBound_connected (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ O, ∃ B : ℝ, ∀ k, |Z k O| ≤ B) : UniformBound hN (Renorm.connected hN Z) :=
  uniformBound_of_bounded hN _ hZ (fun O => ⟨‖O.1‖, fun k => (stateK hN k).abs_le_norm O.1⟩)

end Renorm

/-! ## 4. The limit along one ultrafilter -/

section Limit

/-- The ultrafilter along which every Schwinger function is taken.

DERIVED: no numeral. -/
noncomputable def ultra : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)

/-- DERIVED: no numeral. -/
theorem ultra_le : ((ultra : Ultrafilter ℕ) : Filter ℕ) ≤ atTop := Ultrafilter.of_le _

/-- A real sequence eventually in `[-C, C]` converges along `ultra`.

DERIVED: no numeral. -/
theorem exists_tendsto_ultra (s : ℕ → ℝ) (C : ℝ) (h : ∀ᶠ k in atTop, |s k| ≤ C) :
    ∃ x, Tendsto s (ultra : Filter ℕ) (𝓝 x) := by
  have hmem : Set.Icc (-C) C ∈ (Ultrafilter.map s ultra : Filter ℝ) := by
    rw [Ultrafilter.coe_map]
    exact Filter.mem_map.mpr ((h.filter_mono ultra_le).mono (fun k hk => abs_le.mp hk))
  obtain ⟨x, _hx, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map s ultra)
    (le_principal_iff.mpr hmem)
  refine ⟨x, ?_⟩
  have hmap : Filter.map s (ultra : Filter ℕ) ≤ 𝓝 x := by
    rw [← Ultrafilter.coe_map]
    exact hlim
  exact hmap

/-- Sequences eventually equal have the same limit value along `ultra`.

DERIVED: no numeral. -/
theorem limUnder_congr_ultra {s t : ℕ → ℝ} (h : ∀ᶠ k in atTop, s k = t k) :
    limUnder (ultra : Filter ℕ) s = limUnder (ultra : Filter ℕ) t := by
  unfold limUnder
  rw [Filter.map_congr (h.filter_mono ultra_le)]

/-- **The continuum Schwinger function** of the family `F`: `limUnder` along `ultra` of the
renormalised lattice Schwinger functions `k ↦ latSkR hN ρ k F`. It is their limit along `ultra`
whenever the sequence is bounded on some set of `ultra` (in particular whenever it is eventually
bounded), and `UniformBound` makes that hold for every family (`tendsto_contS`). When the sequence
diverges to `±∞` along `ultra`, `limUnder` returns an unspecified real and `contS hN ρ F` records
nothing about the lattice functions. `ultra` is non-principal and chosen once (`Ultrafilter.of`), so
`contS` is a cluster point of the sequence, the same choice for every family.

DERIVED: `0` is the excluded colour count. -/
noncomputable def contS (hN : N ≠ 0) (ρ : Renorm N) {ι : Type} [Fintype ι] (F : ι → SField N) :
    ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latSkR hN ρ k F)

/-- **Existence of the limit**: under `UniformBound`, `latSkR hN ρ k F → contS hN ρ F` along
`ultra`, for every finite family.

DERIVED: `0` is the zero translation. -/
theorem tendsto_contS (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    Tendsto (fun k => latSkR hN ρ k F) (ultra : Filter ℕ) (𝓝 (contS hN ρ F)) := by
  obtain ⟨C, hC⟩ := hB ι F
  have h0 := hC 0 (fun _ => 0)
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_contS

/-- **OS0 for the limit, as a bound per family, uniform over dyadic translations of the factors**,
under `UniformBound`. The constant depends on the family; continuity in the test functions is not
stated.

DERIVED: `0` is the excluded colour count. -/
theorem exists_abs_contS_le (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
      |contS hN ρ (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB ι F
  exact ⟨C, fun m n =>
    le_of_tendsto (tendsto_contS hN ρ hB _).abs ((hC m n).filter_mono ultra_le)⟩

#print axioms exists_abs_contS_le

/-- **OS0 for the limit at bounded data, explicitly**: `|contS F| ≤ ∏ Bᶻ · ∏ (‖O‖ + Bᶜ) M (2R + 3)⁴`.

DERIVED: `0` is the excluded colour count; `2`, `3`, `4` as in `abs_latS_translate_le`. -/
theorem abs_contS_le_of_bounded (hN : N ≠ 0) (ρ : Renorm N)
    (BZ Bc : LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, |ρ.Z k O| ≤ BZ O)
    (hc : ∀ k O, |ρ.c k O| ≤ Bc O) {ι : Type} [Fintype ι] (F : ι → SField N) (R M : ι → ℝ)
    (hRM : ∀ i, IsTest (F i).2.1 (R i) (M i)) :
    |contS hN ρ F|
      ≤ (∏ i, BZ (F i).1) * ∏ i, (‖(F i).1.1‖ + Bc (F i).1) * (M i * (2 * R i + 3) ^ 4) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hB : UniformBound hN ρ :=
    uniformBound_of_bounded hN ρ (fun O => ⟨BZ O, fun k => hZ k O⟩)
      (fun O => ⟨Bc O, fun k => hc k O⟩)
  have h0 := eventually_abs_latSkR_le hN ρ BZ Bc hZ hc F R M hRM 0 (fun _ => 0)
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  exact le_of_tendsto (tendsto_contS hN ρ hB F).abs (h0.filter_mono ultra_le)

#print axioms abs_contS_le_of_bounded

/-- Reindexing a family does not change the renormalised lattice Schwinger function.

DERIVED: `0` is the excluded colour count. -/
theorem latSkR_comp_equiv (hN : N ≠ 0) (ρ : Renorm N) (k : ℕ) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (e : ι' ≃ ι) (F : ι → SField N) : latSkR hN ρ k (F ∘ e) = latSkR hN ρ k F := by
  have h1 : ρ.pref k (F ∘ e) = ρ.pref k F := Equiv.prod_comp e (fun i => ρ.Z k (F i).1)
  have h2 : latSk hN k (fun i => ρ.field k ((F ∘ e) i)) = latSk hN k (fun i => ρ.field k (F i)) := by
    rw [latSk_eq, latSk_eq]
    exact latS_comp_equiv _ _ e (fun i => ρ.field k (F i))
  show ρ.pref k (F ∘ e) * latSk hN k (fun i => ρ.field k ((F ∘ e) i))
    = ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))
  rw [h1, h2]

/-- **OS3, symmetry**: reindexing a family does not change its continuum Schwinger function. The
reindexed sequences agree term by term, so the identity needs no hypothesis.

DERIVED: `0` is the excluded colour count. -/
theorem contS_comp_equiv (hN : N ≠ 0) (ρ : Renorm N) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (F : ι → SField N) : contS hN ρ (F ∘ e) = contS hN ρ F := by
  unfold contS
  congr 1
  funext k
  exact latSkR_comp_equiv hN ρ k e F

#print axioms contS_comp_equiv

/-- **OS1, dyadic translations**: translating every test function by `dySpacing N m · n` leaves the
continuum Schwinger function unchanged. At every step `k ≥ m` the translation is the lattice
translation by `2^(k-m) n`, under which the periodic state is invariant. The identity needs no
hypothesis: it equates `limUnder` values of sequences that agree from step `m` on.

DERIVED: `0` is the excluded colour count. The halving enters in the proof, through
`site_dySpacing`. -/
theorem contS_translate (hN : N ≠ 0) (ρ : Renorm N) {ι : Type} [Fintype ι] (F : ι → SField N)
    (m : ℕ) (n : ISite) :
    contS hN ρ (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n)))
      = contS hN ρ F := by
  unfold contS
  refine limUnder_congr_ultra ?_
  filter_upwards [Filter.eventually_ge_atTop m] with k hk
  show ρ.pref k F * latSk hN k (fun i => ((ρ.field k (F i)).1,
      (ρ.field k (F i)).2.translate (site (dySpacing N m) n)))
    = ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))
  rw [latSk_eq, latSk_eq, site_dySpacing N hk n]
  congr 1
  exact latS_translate _ (fun τ => PeriodicState.periodicState_shift hN _ τ)
    (dySpacing_pos (one_le_of_ne_zero hN) k) _ _

#print axioms contS_translate

end Limit

/-! ## 5. Reflection positivity of the limit -/

section Positivity

/-- The time reflection of a smeared-field datum.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def SField.refl (τ : Fin 4) (p : SField N) : SField N := (p.1.refl τ, p.2.reflect τ)

/-- A monomial: a finite family of smeared-field data.

DERIVED: no numeral. -/
abbrev Mono (N : ℕ) : Type := Σ n : ℕ, (Fin n → SField N)

/-- Every test function of the monomial translated by `v`.

DERIVED: `4` in `Fin 4 → ℝ` is the spacetime dimension. -/
def Mono.shift (v : Fin 4 → ℝ) (P : Mono N) : Mono N :=
  ⟨P.1, fun i => ((P.2 i).1, (P.2 i).2.translate v)⟩

/-- Every test function of the monomial has positive-time support.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def Mono.Pos (τ : Fin 4) (P : Mono N) : Prop := ∀ i, PosTime τ (P.2 i).2

/-- Positive-time monomials.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
abbrev PosMono (N : ℕ) (τ : Fin 4) : Type := {P : Mono N // Mono.Pos τ P}

/-- The renormalised monomial of step `k`, and its field-strength factor.

DERIVED: no numeral. -/
abbrev Renorm.mono (ρ : Renorm N) (k : ℕ) (P : Mono N) : Mono N :=
  ⟨P.1, fun i => ρ.field k (P.2 i)⟩

/-- DERIVED: no numeral. -/
noncomputable def Renorm.zmono (ρ : Renorm N) (k : ℕ) (P : Mono N) : ℝ := ∏ i, ρ.Z k (P.2 i).1

/-- The family `θP ∪ Q`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def pairFam (τ : Fin 4) (P Q : Mono N) : Fin P.1 ⊕ Fin Q.1 → SField N :=
  Sum.elim (fun i => SField.refl τ (P.2 i)) Q.2

/-- The product of the smeared fields of a monomial.

DERIVED: no numeral. -/
noncomputable def prodSmear (a : ℝ) (P : Mono N) : C(Cfg N, ℝ) :=
  ∏ i, smear a (P.2 i).1.1 (P.2 i).2

/-- **The reflection kernel** `S(θP ∪ Q)`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def kern (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (P Q : Mono N) : ℝ :=
  contS hN ρ (pairFam τ P Q)

/-- At the lattice, `S(θP ∪ Q) = ν (θ(∏P) · ∏Q)`, `θ = ireflObs τ 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant and the sign of
`a`. -/
theorem latS_pairFam (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a) (τ : Fin 4)
    (P Q : Mono N) :
    latS ν a (pairFam τ P Q)
      = ν (LatticeReflection.ireflObs τ 0 (prodSmear a P) * prodSmear a Q) := by
  have hθ : LatticeReflection.ireflObs τ 0 (prodSmear a P)
      = ∏ i, LatticeReflection.ireflObs τ 0 (smear a (P.2 i).1.1 (P.2 i).2) :=
    (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ 0).theta_prod Finset.univ
      (fun i => smear a (P.2 i).1.1 (P.2 i).2)
  have h1 : (∏ i, smear a (SField.refl τ (P.2 i)).1.1 (SField.refl τ (P.2 i)).2)
      = LatticeReflection.ireflObs τ 0 (prodSmear a P) := by
    rw [hθ]
    exact Finset.prod_congr rfl (fun i _ => (ireflObs_smear ha τ _ _).symm)
  show ν (∏ x : Fin P.1 ⊕ Fin Q.1, smear a (pairFam τ P Q x).1.1 (pairFam τ P Q x).2) = _
  rw [Fintype.prod_sum_type]
  simp only [pairFam, Sum.elim_inl, Sum.elim_inr]
  rw [h1]
  rfl

#print axioms latS_pairFam

/-- With reflection-compatible data the renormalised pairing factorises:
`S_k(θP ∪ Q) = Z_P Z_Q · S_k^{bare}(θ P_k ∪ Q_k)`, `P_k` the renormalised monomial.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSkR_pairFam (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ)
    (P Q : Mono N) :
    latSkR hN ρ k (pairFam τ P Q)
      = ρ.zmono k P * ρ.zmono k Q * latSk hN k (pairFam τ (ρ.mono k P) (ρ.mono k Q)) := by
  have hfam : (fun x => ρ.field k (pairFam τ P Q x)) = pairFam τ (ρ.mono k P) (ρ.mono k Q) := by
    funext x
    cases x with
    | inl i =>
      show (((P.2 i).1.refl τ).sub (ρ.c k ((P.2 i).1.refl τ)), (P.2 i).2.reflect τ)
        = (((P.2 i).1.sub (ρ.c k (P.2 i).1)).refl τ, (P.2 i).2.reflect τ)
      rw [(hR k (P.2 i).1).2, LField.refl_sub]
    | inr j => rfl
  have hpref : ρ.pref k (pairFam τ P Q) = ρ.zmono k P * ρ.zmono k Q := by
    show (∏ x : Fin P.1 ⊕ Fin Q.1, ρ.Z k (pairFam τ P Q x).1)
      = (∏ i, ρ.Z k (P.2 i).1) * ∏ j, ρ.Z k (Q.2 j).1
    rw [Fintype.prod_sum_type]
    have h1 : (∏ i, ρ.Z k (pairFam τ P Q (Sum.inl i)).1) = ∏ i, ρ.Z k (P.2 i).1 :=
      Finset.prod_congr rfl (fun i _ => (hR k (P.2 i).1).1)
    exact congrArg (fun t => t * ∏ j, ρ.Z k (Q.2 j).1) h1
  show ρ.pref k (pairFam τ P Q) * latSk hN k (fun x => ρ.field k (pairFam τ P Q x)) = _
  rw [hpref, hfam]

#print axioms latSkR_pairFam

/-- The Gram expansion `ν(θX · X) = ∑∑ c_P c_Q ν(θA_P · A_Q)` for `X = ∑ c_P A_P`.

DERIVED: no numeral. -/
theorem gram_expand {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (θ : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) {α : Type*} (s : Finset α)
    (c : α → ℝ) (A : α → C(X, ℝ)) :
    ν (θ (∑ P ∈ s, c P • A P) * ∑ Q ∈ s, c Q • A Q)
      = ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * ν (θ (A P) * A Q) := by
  rw [map_sum, Finset.sum_mul_sum, ν.map_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [ν.map_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [map_smul, smul_mul_smul_comm, ν.map_smul]

/-- Reflection positivity of the state of step `k` on the half-space algebra of `x_τ = 0`.

DERIVED: `0` is the excluded colour count, the plane `x_τ = 0`, the reflection constant and the sign
concluded; `4` in `Fin 4` is the spacetime dimension. The proof reads the reflection constant off
`periodicState_reflPositive` as a product with zero. -/
theorem stateK_rp (hN : N ≠ 0) (k : ℕ) (τ : Fin 4) (X : C(Cfg N, ℝ))
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    0 ≤ stateK hN k (LatticeReflection.ireflObs τ 0 X * X) := by
  have h := PeriodicState.periodicState_reflPositive hN (dyBeta (one_le_of_ne_zero hN) k) τ 0
  rw [mul_zero] at h
  exact h X hX

/-- A positive-time smeared field, with any constant subtracted, is eventually in the half-space
algebra.

DERIVED: `1` is the least colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the plane.
-/
theorem eventually_smear_sub_mem (hN1 : 1 ≤ N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (f : TestFn) (hf : PosTime τ f) :
    ∀ᶠ k in atTop, ∀ r : ℝ,
      smear (dySpacing N k) (O.sub r).1 f
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
  obtain ⟨δ, hδ, hsupp⟩ := hf
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth τ S
  have ht : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
  intro r
  exact smear_mem_halfSpaceAlg (dySpacing_pos hN1 k) τ (isLocalOn_sub_const hS r) hD hk.le f
    hsupp

/-- **OS2, reflection positivity of the limit.** Under `UniformBound` and reflection-compatible
data, for every finite set of positive-time monomials and real coefficients,
`0 ≤ ∑_{P,Q} c_P c_Q S(θP ∪ Q)`. At each large step the sum is `ν_k(θX · X)` with
`X = ∑ c_P Z_P ∏P_k` in the half-space algebra, nonnegative by the periodic state's reflection
positivity; `[0, ∞)` is closed.

DERIVED: `0` is the excluded colour count and the sign concluded; `4` in `Fin 4` is the spacetime
dimension. -/
theorem contS_gram_nonneg (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) (τ : Fin 4)
    (hR : ρ.ReflCompat τ) (s : Finset (PosMono N τ)) (c : PosMono N τ → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kern hN ρ τ P.1 Q.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have htend : Tendsto
      (fun k => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kern hN ρ τ P.1 Q.1)) :=
    tendsto_finset_sum _ (fun P _ => tendsto_finset_sum _
      (fun Q _ => (tendsto_contS hN ρ hB (pairFam τ P.1 Q.1)).const_mul (c P * c Q)))
  refine ge_of_tendsto htend ?_
  have hmem : ∀ᶠ k in atTop, ∀ P ∈ s, ∀ i : Fin P.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.2 i).1.sub r).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    (Filter.eventually_all_finset s).mpr (fun P _ =>
      Filter.eventually_all.mpr
        (fun i => eventually_smear_sub_mem (one_le_of_ne_zero hN) τ _ _ (P.2 i)))
  have hev : ∀ᶠ k in atTop,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1) := by
    filter_upwards [hmem] with k hk
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hsum : ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1)
        = ∑ P ∈ s, ∑ Q ∈ s, (c P * ρ.zmono k P.1) * (c Q * ρ.zmono k Q.1) * stateK hN k
            (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (ρ.mono k P.1))
              * prodSmear (dySpacing N k) (ρ.mono k Q.1)) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
      rw [latSkR_pairFam hN ρ τ hR, latSk_eq, latS_pairFam _ ha]
      ring
    have hX : (∑ P ∈ s, (c P * ρ.zmono k P.1) • prodSmear (dySpacing N k) (ρ.mono k P.1))
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
      Submodule.sum_mem _ (fun P hP => Submodule.smul_mem _ _
        (HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
          (fun i _ => hk P hP i (ρ.c k (P.1.2 i).1))))
    rw [hsum]
    exact le_of_le_of_eq (stateK_rp hN k τ _ hX)
      (gram_expand (stateK hN k) (LatticeReflection.ireflObs τ 0) s
        (fun P => c P * ρ.zmono k P.1) (fun P => prodSmear (dySpacing N k) (ρ.mono k P.1)))
  exact hev.filter_mono ultra_le

#print axioms contS_gram_nonneg

/-- In a reflection-invariant state, `ν(θA · B) = ν(θB · A)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant. -/
theorem refl_pair_symm (ν : MassGap.DLRLimit.State (Cfg N)) (τ : Fin 4)
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ 0) ν)
    (A B : C(Cfg N, ℝ)) :
    ν (LatticeReflection.ireflObs τ 0 A * B) = ν (LatticeReflection.ireflObs τ 0 B * A) := by
  calc ν (LatticeReflection.ireflObs τ 0 A * B)
      = ν (LatticeReflection.ireflObs τ 0 (LatticeReflection.ireflObs τ 0 A * B)) :=
        (hinv _).symm
    _ = ν (LatticeReflection.ireflObs τ 0 (LatticeReflection.ireflObs τ 0 A)
          * LatticeReflection.ireflObs τ 0 B) := rfl
    _ = ν (A * LatticeReflection.ireflObs τ 0 B) := by rw [ireflObs_ireflObs]
    _ = ν (LatticeReflection.ireflObs τ 0 B * A) := by rw [mul_comm]

/-- In a state invariant under the reflection about `x_τ = 0`, reflecting every field and test
function leaves the lattice Schwinger function unchanged.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant and the sign of
`a`. -/
theorem latS_refl (ν : MassGap.DLRLimit.State (Cfg N)) (τ : Fin 4)
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ 0) ν)
    {a : ℝ} (ha : 0 < a) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latS ν a (fun i => SField.refl τ (F i)) = latS ν a F := by
  have hθ : LatticeReflection.ireflObs τ 0 (∏ i, smear a (F i).1.1 (F i).2)
      = ∏ i, LatticeReflection.ireflObs τ 0 (smear a (F i).1.1 (F i).2) :=
    (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ 0).theta_prod Finset.univ
      (fun i => smear a (F i).1.1 (F i).2)
  have h1 : (∏ i, smear a (SField.refl τ (F i)).1.1 (SField.refl τ (F i)).2)
      = LatticeReflection.ireflObs τ 0 (∏ i, smear a (F i).1.1 (F i).2) := by
    rw [hθ]
    exact Finset.prod_congr rfl (fun i _ => (ireflObs_smear ha τ _ _).symm)
  show ν (∏ i, smear a (SField.refl τ (F i)).1.1 (SField.refl τ (F i)).2)
    = ν (∏ i, smear a (F i).1.1 (F i).2)
  rw [h1]
  exact hinv _

/-- **OS1, the axis reflections**: reflecting every field and every test function in the time
axis `τ` (`y_τ ↦ -y_τ`) leaves the continuum Schwinger function unchanged, at reflection-compatible
data, for each of the four axes.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The reflection
constant enters through `SField.refl`. -/
theorem contS_reflect (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    contS hN ρ (fun i => SField.refl τ (F i)) = contS hN ρ F := by
  unfold contS
  congr 1
  funext k
  have hpref : ρ.pref k (fun i => SField.refl τ (F i)) = ρ.pref k F :=
    Finset.prod_congr rfl (fun i _ => (hR k (F i).1).1)
  have hfam : (fun i => ρ.field k (SField.refl τ (F i)))
      = fun i => SField.refl τ (ρ.field k (F i)) := by
    funext i
    show (((F i).1.refl τ).sub (ρ.c k ((F i).1.refl τ)), (F i).2.reflect τ)
      = (((F i).1.sub (ρ.c k (F i).1)).refl τ, (F i).2.reflect τ)
    rw [(hR k (F i).1).2, LField.refl_sub]
  show ρ.pref k (fun i => SField.refl τ (F i)) * latSk hN k (fun i => ρ.field k (SField.refl τ (F i)))
    = ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))
  rw [hpref, hfam, latSk_eq, latSk_eq,
    latS_refl (stateK hN k) τ
      (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0)
      (dySpacing_pos (one_le_of_ne_zero hN) k) (fun i => ρ.field k (F i))]

#print axioms contS_reflect

/-- **The reflection kernel is symmetric**: `S(θP ∪ Q) = S(θQ ∪ P)`, from the reflection invariance
of the periodic states, at reflection-compatible data.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The reflection
constant enters through `kern`. -/
theorem kern_symm (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (P Q : Mono N) :
    kern hN ρ τ P Q = kern hN ρ τ Q P := by
  unfold kern contS
  congr 1
  funext k
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [latSkR_pairFam hN ρ τ hR, latSkR_pairFam hN ρ τ hR, latSk_eq, latSk_eq,
    latS_pairFam _ ha, latS_pairFam _ ha,
    refl_pair_symm (stateK hN k) τ
      (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0)
      (prodSmear (dySpacing N k) (ρ.mono k P)) (prodSmear (dySpacing N k) (ρ.mono k Q))]
  ring

#print axioms kern_symm

end Positivity

/-! ## 6. Clustering from a uniform lattice bound, and rotations -/

section Cluster

/-- The family `P ∪ Q`.

DERIVED: no numeral. -/
def concatFam (P Q : Mono N) : Fin P.1 ⊕ Fin Q.1 → SField N := Sum.elim P.2 Q.2

/-- The dyadic time vector `dySpacing N m · n` in direction `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def timeVec (N : ℕ) (m : ℕ) (τ : Fin 4) (n : ℤ) : Fin 4 → ℝ :=
  site (dySpacing N m) (axisVec τ n)

/-- **The uniform clustering hypothesis (stated, not proved).** For all monomials `P`, `Q` and every
dyadic time separation `t = dySpacing N m · n` in direction `τ`, eventually in the step `k`, the
renormalised lattice connected function of `P` and `Q` translated by `t` is at most
`Cst P Q · exp(-mass · t)`, with `mass` and `Cst P Q` independent of `k`: decay at a physical rate
uniform along the running coupling.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def UniformClustering (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (mass : ℝ)
    (Cst : Mono N → Mono N → ℝ) : Prop :=
  ∀ (P Q : Mono N) (m n : ℕ), ∀ᶠ k in atTop,
    |latSkR hN ρ k (concatFam P (Mono.shift (timeVec N m τ n) Q))
        - latSkR hN ρ k P.2 * latSkR hN ρ k (Mono.shift (timeVec N m τ n) Q).2|
      ≤ Cst P Q * Real.exp (-mass * (dySpacing N m * n))

/-- **OS4 bound for the limit**, from `UniformBound` and `UniformClustering`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem contS_cluster (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) (τ : Fin 4)
    {mass : ℝ} {Cst : Mono N → Mono N → ℝ} (h : UniformClustering hN ρ τ mass Cst)
    (P Q : Mono N) (m n : ℕ) :
    |contS hN ρ (concatFam P (Mono.shift (timeVec N m τ n) Q)) - contS hN ρ P.2 * contS hN ρ Q.2|
      ≤ Cst P Q * Real.exp (-mass * (dySpacing N m * n)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hQ : contS hN ρ (Mono.shift (timeVec N m τ n) Q).2 = contS hN ρ Q.2 :=
    contS_translate hN ρ Q.2 m (axisVec τ n)
  rw [← hQ]
  exact le_of_tendsto
    (((tendsto_contS hN ρ hB (concatFam P (Mono.shift (timeVec N m τ n) Q))).sub
      ((tendsto_contS hN ρ hB P.2).mul
        (tendsto_contS hN ρ hB (Mono.shift (timeVec N m τ n) Q).2))).abs)
    ((h P Q m n).filter_mono ultra_le)

#print axioms contS_cluster

/-- **OS4 for the limit**, from `UniformBound` and `UniformClustering` at a positive mass: as the
dyadic time separation grows, `S(P ∪ Q translated) → S(P) S(Q)`.

DERIVED: `0` is the excluded colour count and the sign of the mass; `4` in `Fin 4` is the spacetime
dimension. -/
theorem contS_cluster_tendsto (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) (τ : Fin 4)
    {mass : ℝ} (hmass : 0 < mass) {Cst : Mono N → Mono N → ℝ}
    (h : UniformClustering hN ρ τ mass Cst) (P Q : Mono N) (m : ℕ) :
    Tendsto (fun n : ℕ => contS hN ρ (concatFam P (Mono.shift (timeVec N m τ n) Q))) atTop
      (𝓝 (contS hN ρ P.2 * contS hN ρ Q.2)) := by
  have hexp : Tendsto (fun n : ℕ => Cst P Q * Real.exp (-mass * (dySpacing N m * n))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => mass * dySpacing N m * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (mul_pos hmass (dySpacing_pos (one_le_of_ne_zero hN) m))
        tendsto_natCast_atTop_atTop
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (Cst P Q)
    rw [mul_zero] at h3
    refine h3.congr (fun n => ?_)
    show Cst P Q * Real.exp (-(mass * dySpacing N m * (n : ℝ)))
      = Cst P Q * Real.exp (-mass * (dySpacing N m * n))
    congr 2
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact contS_cluster hN ρ hB τ h P Q m n) hexp

#print axioms contS_cluster_tendsto

/-- **Euclidean rotation invariance (stated, not proved).** For every `R ∈ SO(4)` and every family
whose fields lie in `Φ`, composing every test function with `R` leaves the continuum Schwinger
function unchanged. `Φ` is the caller's set of fields expected to transform as scalars (a single
plaquette is not one); the lattice supplies only the hypercubic subgroup. The content is set by `Φ`:
at `Φ = ∅` only families over an empty index type qualify and the statement holds trivially.

DERIVED: `0` is the excluded colour count; `4` is the dimension, of `SO(4)`. -/
def RotationInvariant (hN : N ≠ 0) (ρ : Renorm N) (Φ : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∀ Rot : Matrix (Fin 4) (Fin 4) ℝ, Rot ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] (F F' : ι → SField N), (∀ i, (F i).1 ∈ Φ) →
      (∀ i, (F' i).1 = (F i).1) → (∀ i y, (F' i).2.1 y = (F i).2.1 (Rot.mulVec y)) →
      contS hN ρ F' = contS hN ρ F

end Cluster

end MassGap.ContinuumSchwinger
