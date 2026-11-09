import Mathlib
import MassGap.ReflPosG

/-!
# MassGap.FlowG — the flowed continuum limit and its reconstruction, over a schedule of `G`

`ContinuumFlow` builds, for a flow `Φ : Flow N` of the `SU(N)` fields under the flowed uniform bound,
the flowed continuum Schwinger functions, their symmetries (OS1, OS3), reflection positivity beyond the
flow's margin (OS2), and at every dyadic step a reconstructed Hilbert space with a positive transfer
operator. This module states and proves the same for every `GaugeGroup G`, over a schedule
`S : ClayTreeG.Sched G` whose states carry four properties, collected in `SchedOS S`:

* `trans : ClayWiringG.SchedTransInv S` (dyadic translation invariance);
* `refl : ReflInvG.SchedReflInv S` (reflection invariance);
* `rp : ReflPosG.SchedRP S` (reflection positivity at the plane `x_τ = 0`);
* `dyadic : SchedDyadic S`: `S.a k · 2^(k−m) = S.a m` for `m ≤ k`.

`schedOS_canonSched` proves all four at `canonSched G`.

| `ContinuumFlow` (`SU(N)`) | here (any `G`, any `S`) | schedule input |
|---|---|---|
| `Flow`, `Flow.field`, `Flow.mono` | `GFlow`, `GFlow.field`, `GFlow.mono` | none |
| `Flow.PhysRange`, `Flow.PosPreserving` | `GFlow.PhysRange`, `GFlow.PosPreserving` | none |
| `ConfFlow.fieldMap_refl`, `refl_scaleField`, `isLocalOn_scale_sub` | `fieldMapG_refl`, `refl_scaleFieldG`, `isLocalOn_scale_subG` | none |
| `ObserverOS.energy0` | `energy0G` (map `ClayTreeG.energyMapG`) | none |
| `SField.refl`, `Mono.shift`, `pairFam`, `prodSmear` | `sreflG`, `monoShiftG`, `pairFamG`, `prodSmearG` | none |
| `latS_pairFam`, `refl_pair_symm`, `latS_refl` | `latSG_pairFamG`, `refl_pair_symmG`, `latSG_reflG` | `refl` (last) |
| `timeVec_*`, `reflR_timeVec`, `pairFam_shift`, `pairFam_shiftN` | `timeVecG_*`, `reflR_timeVecG`, `pairFamG_shift`, `pairFamG_shiftN` | `dyadic` (`timeVecG_one_add`) |
| `tendsto_contSF`, `exists_abs_contSF_le`, `contSF_comp_equiv` | `tendsto_contSFG`, `exists_abs_contSFG_le`, `contSFG_comp_equiv` | none |
| `contSF_translate`, `contSF_reflect` | `contSFG_translate`, `contSFG_reflect` | `trans`, `refl` |
| `kernF`, `kernF_symm`, `kernF_shift` | `kernFG`, `kernFG_symm`, `kernFG_shift` | `refl`, `trans` |
| `Flow.posPreserving_of_physRange` | `posPreserving_of_physRangeG` | none |
| `posAt_shift`, `MarginMono` | `posAtG_shift`, `ClayTreeG.MarginMonoG` | none |
| `contSF_gram_nonneg` (OS2) | `contSFG_gram_nonneg` | `rp` |
| `MarginMono.shift`, `_iterate`, `_half`, `emptyMargin` | `marginShiftG`, `_iterate`, `_half`, `emptyMarginG` | `dyadic` (`_half`) |
| `kernF_iterate_bound`, `kernF_empty` | `kernFG_iterate_bound`, `kernFG_empty` | none |
| `flowTransfer`, `flowTransfer_positive` | `flowTransferG`, `flowTransferG_positive` | `refl`, `rp`, `trans`; `dyadic` (`_positive`) |
| `flow_reconstruction`, `flow_reconstruction_physRange` | `flow_reconstructionG`, `flow_reconstruction_physRangeG` | all four |
| `FlowConnectedNonzero`, `exists_orth_ne_zero_flow` | `FlowConnectedNonzeroG`, `exists_orth_ne_zero_flowG` | none (definition); `exists_orth_ne_zero_flowG` reads the transfer's fields and `refl` |

The flowed lattice and continuum functions are `ClayTreeG.latSFG S Φ.map` and `ClayTreeG.contSFG S Φ.map`,
and the uniform bound is `ClayTreeG.UniformBoundFG S Φ.map`; this module defines no second copy of them.
The kernel-to-Hilbert-space section of `ContinuumFlow` (`gForm`, `gTransfer`, `gPositive`,
`reconstructed_of_positive`, `gVec`, `inner_gVec`) is stated over an arbitrary index type and is used
here as it is, as are `ContinuumSchwinger.gram_expand`, `exists_tendsto_ultra`, `limUnder_congr_ultra`
and the `ContinuumField` lemmas on smearing, reflection and depth.

The reflection positivity used is the even-constant one (`ReflPosG.SchedRP`, mirror plane `x_τ = 0`);
no step here uses the odd constant.

At `SU(N)`: `Flow.toGFlow` carries a `Flow N` to a `GFlow (SU N)` field by field, and `kernFG_SU`
states `kernFG (schedSU N) Φ.toGFlow = kernF`, by definition.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `0` the reflection plane `x_τ = 0`, the reflection constant,
the zero vector and the signs; `1` the unit time step, the unit observable and the vacuum
coefficient; `2` the dyadic halving and the square.
-/

noncomputable section

namespace MassGap.FlowG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.ClayWiringG MassGap.ReflInvG MassGap.ReflPosG
  Filter
open scoped Topology

/-! ## 1. The schedule properties -/

section Sched

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The dyadic spacing identity of a schedule**: `S.a k · 2^(k−m) = S.a m` for `m ≤ k`.

DERIVED: `2` the halving. -/
def SchedDyadic (S : Sched G) : Prop :=
  ∀ m k : ℕ, m ≤ k → S.a k * 2 ^ (k - m) = S.a m

/-- **The canonical schedule is dyadic** (`ShiftInvG.dySpacingG_mul_pow`).

DERIVED: no numeral. -/
theorem schedDyadic_canonSched [GaugeSimple G] : SchedDyadic (canonSched G) :=
  fun _ _ hmk => MassGap.ShiftInvG.dySpacingG_mul_pow G hmk

/-- **The schedule properties the flowed reconstruction reads**: dyadic translation invariance,
reflection invariance, reflection positivity at the plane `x_τ = 0`, and the dyadic spacing identity.

DERIVED: no numeral. -/
structure SchedOS (S : Sched G) : Prop where
  trans : SchedTransInv S
  refl : SchedReflInv S
  rp : SchedRP S
  dyadic : SchedDyadic S

/-- **The canonical schedule of `G` has all four** (`ShiftInvG.schedTransInv_canonSched`,
`ReflInvG.schedReflInv_canonSched`, `ReflPosG.schedRP_canonSched`, `schedDyadic_canonSched`).

DERIVED: no numeral. -/
theorem schedOS_canonSched [GaugeSimple G] : SchedOS (canonSched G) :=
  ⟨MassGap.ShiftInvG.schedTransInv_canonSched, schedReflInv_canonSched, schedRP_canonSched,
    schedDyadic_canonSched⟩

/-- `S.a m = S.a 0 · (1/2)^m` on a dyadic schedule.

DERIVED: `0` the reference step; `1/2` the dyadic ratio; `2` the refinement factor. -/
theorem sched_a_eq_mul (S : Sched G) (hd : SchedDyadic S) (m : ℕ) :
    S.a m = S.a 0 * (1 / 2 : ℝ) ^ m := by
  have h := hd 0 m (Nat.zero_le m)
  rw [Nat.sub_zero] at h
  rw [← h, mul_assoc, ← mul_pow]
  norm_num

end Sched

/-! ## 2. The flow interface over `G` -/

section Interface

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A flow of the local fields of `G`**: at each step `k` a map `map k` on local gauge-invariant
fields, commuting with the time reflection of each axis, of lattice range `range k`: a field local on
`T` flows to a field local on links each within `range k`, in every coordinate of the base site, of a
link of `T`. The fields of `ContinuumFlow.Flow` with `SU N` replaced by `G`.

DERIVED: `4` the dimension; the reflection constant `0` enters through `LField.refl`. -/
structure GFlow (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] where
  /-- The flowed field at step `k`. -/
  map : ℕ → LField G → LField G
  /-- The lattice range of the flow at step `k`. -/
  range : ℕ → ℕ
  /-- The flow commutes with the time reflection of each axis. -/
  map_refl : ∀ (k : ℕ) (τ : Fin 4) (O : LField G), map k (O.refl τ) = (map k O).refl τ
  /-- The flow has finite range. -/
  map_local : ∀ (k : ℕ) (O : LField G) (T : Finset ILink),
    IsLocalOn T (O.1 : IConf G → ℝ) →
      ∃ T' : Finset ILink, IsLocalOn T' ((map k O).1 : IConf G → ℝ) ∧
        ∀ l' ∈ T', ∃ l ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (range k : ℤ)

/-- The flowed field datum of step `k`: the field flowed, the test function kept.

DERIVED: no numeral. -/
def GFlow.field (Φ : GFlow G) (k : ℕ) (p : SFieldG G) : SFieldG G := (Φ.map k p.1, p.2)

/-- The flowed monomial of step `k`.

DERIVED: no numeral. -/
abbrev GFlow.mono (Φ : GFlow G) (k : ℕ) (P : MonoG G) : MonoG G :=
  ⟨P.1, fun i => Φ.field k (P.2 i)⟩

/-- **Physical range `r` over the schedule `S`**: eventually in the step, `S.a k · range k ≤ r`.

DERIVED: no numeral; `r` is the caller's physical range. -/
def GFlow.PhysRange (Φ : GFlow G) (S : Sched G) (r : ℝ) : Prop :=
  ∀ᶠ k in atTop, S.a k * (Φ.range k : ℝ) ≤ r

/-- **The flow keeps the positive half-space beyond the margin `r`**: for every field and every test
function vanishing below a time `δ > 0` with `δ > r` in direction `τ`, eventually in the step the
flowed smeared field at spacing `S.a k` lies in the half-space algebra of the plane `x_τ = 0`.

DERIVED: `4` the dimension; `0` the plane and the sign of `δ`. -/
def GFlow.PosPreserving (Φ : GFlow G) (S : Sched G) (τ : Fin 4) (r : ℝ) : Prop :=
  ∀ (O : LField G) (f : TestFn) (δ : ℝ), 0 < δ → r < δ →
    (∀ y, f.1 y ≠ 0 → δ ≤ y τ) →
      ∀ᶠ k in atTop, smear (S.a k) (Φ.map k O).1 f ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0

/-- The flowed field of a reflected field is the reflected flowed field, for a `ConfFlowG`.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem fieldMapG_refl (W : ConfFlowG G) (k : ℕ) (τ : Fin 4) (O : LField G) :
    W.fieldMap k (O.refl τ) = (W.fieldMap k O).refl τ :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (LatticeReflection.ireflConf τ 0 (W.V k U))
      = O.1 (W.V k (LatticeReflection.ireflConf τ 0 U))
    rw [W.refl]))

/-- Reflection commutes with scaling.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem refl_scaleFieldG (τ : Fin 4) (O : LField G) (s : ℝ) :
    (scaleFieldG O s).refl τ = scaleFieldG (O.refl τ) s :=
  Subtype.ext (map_smul (LatticeReflection.ireflObs (G := G) τ 0) s O.1)

omit [Group G] [MeasurableSpace G] [GaugeGroup G] in
/-- `s · (F − r · 1)` is local wherever `F` is.

DERIVED: `1` the unit observable. -/
theorem isLocalOn_scale_subG {T : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : IsLocalOn T (F : IConf G → ℝ)) (r s : ℝ) :
    IsLocalOn T ((s • (F - r • (1 : C(IConf G, ℝ))) : C(IConf G, ℝ)) : IConf G → ℝ) := by
  intro U V h
  show s * (F U - r * 1) = s * (F V - r * 1)
  rw [hF U V h]

/-- The factor `zOnG` is reflection compatible on a reflection-closed class `D`.

DERIVED: `4` the dimension. -/
theorem zOnG_refl (S : Sched G) {D : Set (LField G)}
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) (k : ℕ) (τ : Fin 4)
    (O : LField G) : zOnG S D k (O.refl τ) = zOnG S D k O := by
  unfold zOnG
  by_cases h : O ∈ D
  · rw [if_pos ((hD τ O).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((hD τ O).mp h')), if_neg h]

/-- The zero subtraction on a class is zero.

DERIVED: `0` the subtraction. -/
theorem sOnG_zero (D : Set (LField G)) (k : ℕ) (O : LField G) :
    sOnG D (fun _ _ => 0) k O = 0 := by
  unfold sOnG
  split_ifs <;> rfl

/-- **The energy density of a configuration flow as a `GFlow`**: the map `ClayTreeG.energyMapG S W D`,
the range of `W`, on a reflection-closed class `D`. The mirror of `ObserverOS.energy0`.

DERIVED: `4` the dimension; `0` the zero subtraction. -/
def energy0G (S : Sched G) (W : ConfFlowG G) (D : Set (LField G))
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) : GFlow G where
  map := energyMapG S W D
  range := W.range
  map_refl k τ O := by
    show scaleFieldG ((W.fieldMap k (O.refl τ)).sub (sOnG D (fun _ _ => 0) k (O.refl τ)))
        (zOnG S D k (O.refl τ))
      = (scaleFieldG ((W.fieldMap k O).sub (sOnG D (fun _ _ => 0) k O)) (zOnG S D k O)).refl τ
    rw [zOnG_refl S hD, sOnG_zero, sOnG_zero, fieldMapG_refl, ← LField.refl_sub,
      ← refl_scaleFieldG]
  map_local k O T hT := by
    obtain ⟨T', h1, h2⟩ := isLocalOn_compG (W.local_V k) hT
    exact ⟨T', isLocalOn_scale_subG (F := (W.fieldMap k O).1) h1 _ _, h2⟩

/-- DERIVED: no numeral. -/
theorem energy0G_map (S : Sched G) (W : ConfFlowG G) (D : Set (LField G))
    (hD : ∀ (τ : Fin 4) (O : LField G), O.refl τ ∈ D ↔ O ∈ D) :
    (energy0G S W D hD).map = energyMapG S W D := rfl

end Interface

/-! ## 3. Monomials, reflected pairs and time steps -/

section Geometry

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The time reflection of a smeared-field datum.

DERIVED: `4` the dimension. -/
def sreflG (τ : Fin 4) (p : SFieldG G) : SFieldG G := (p.1.refl τ, p.2.reflect τ)

/-- Every test function of the monomial translated by `v`.

DERIVED: `4` the dimension. -/
def monoShiftG (v : Fin 4 → ℝ) (P : MonoG G) : MonoG G :=
  ⟨P.1, fun i => ((P.2 i).1, (P.2 i).2.translate v)⟩

/-- The family `θP ∪ Q`.

DERIVED: `4` the dimension. -/
def pairFamG (τ : Fin 4) (P Q : MonoG G) : Fin P.1 ⊕ Fin Q.1 → SFieldG G :=
  Sum.elim (fun i => sreflG τ (P.2 i)) Q.2

/-- The product of the smeared fields of a monomial.

DERIVED: no numeral. -/
def prodSmearG (a : ℝ) (P : MonoG G) : C(IConf G, ℝ) :=
  ∏ i, smear a (P.2 i).1.1 (P.2 i).2

/-- **At the lattice, `S(θP ∪ Q) = ν_k(θ(∏P) · ∏Q)`**, `θ = ireflObs τ 0`, at the spacing `S.a k`.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem latSG_pairFamG (S : Sched G) (k : ℕ) (τ : Fin 4) (P Q : MonoG G) :
    latSG S k (pairFamG τ P Q)
      = S.ν k (LatticeReflection.ireflObs τ 0 (prodSmearG (S.a k) P) * prodSmearG (S.a k) Q) := by
  have ha := S.a_pos k
  have hθ : LatticeReflection.ireflObs τ 0 (prodSmearG (S.a k) P)
      = ∏ i, LatticeReflection.ireflObs τ 0 (smear (S.a k) (P.2 i).1.1 (P.2 i).2) :=
    (LatticeReflection.latticeReflection (G := G) τ 0).theta_prod Finset.univ
      (fun i => smear (S.a k) (P.2 i).1.1 (P.2 i).2)
  have h1 : (∏ i, smear (S.a k) (sreflG τ (P.2 i)).1.1 (sreflG τ (P.2 i)).2)
      = LatticeReflection.ireflObs τ 0 (prodSmearG (S.a k) P) := by
    rw [hθ]
    exact Finset.prod_congr rfl (fun i _ => (ireflObs_smear ha τ _ _).symm)
  show S.ν k (∏ x : Fin P.1 ⊕ Fin Q.1, smear (S.a k) (pairFamG τ P Q x).1.1 (pairFamG τ P Q x).2)
    = _
  rw [Fintype.prod_sum_type]
  simp only [pairFamG, Sum.elim_inl, Sum.elim_inr]
  rw [h1]
  rfl

/-- **In a reflection-invariant state, `ν(θA · B) = ν(θB · A)`**, over `G`.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem refl_pair_symmG (ν : MassGap.DLRLimit.State (IConf G)) (τ : Fin 4)
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection (G := G) τ 0) ν)
    (A B : C(IConf G, ℝ)) :
    ν (LatticeReflection.ireflObs τ 0 A * B) = ν (LatticeReflection.ireflObs τ 0 B * A) := by
  calc ν (LatticeReflection.ireflObs τ 0 A * B)
      = ν (LatticeReflection.ireflObs τ 0 (LatticeReflection.ireflObs τ 0 A * B)) :=
        (hinv _).symm
    _ = ν (LatticeReflection.ireflObs τ 0 (LatticeReflection.ireflObs τ 0 A)
          * LatticeReflection.ireflObs τ 0 B) := rfl
    _ = ν (A * LatticeReflection.ireflObs τ 0 B) := by rw [ireflObs_ireflObs]
    _ = ν (LatticeReflection.ireflObs τ 0 B * A) := by rw [mul_comm]

/-- **On a reflection-invariant schedule, reflecting every field and test function leaves the
lattice Schwinger function unchanged.**

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem latSG_reflG (S : Sched G) (hR : SchedReflInv S) (k : ℕ) (τ : Fin 4) {ι : Type}
    [Fintype ι] (F : ι → SFieldG G) :
    latSG S k (fun i => sreflG τ (F i)) = latSG S k F := by
  have ha := S.a_pos k
  have hθ : LatticeReflection.ireflObs τ 0 (∏ i, smear (S.a k) (F i).1.1 (F i).2)
      = ∏ i, LatticeReflection.ireflObs τ 0 (smear (S.a k) (F i).1.1 (F i).2) :=
    (LatticeReflection.latticeReflection (G := G) τ 0).theta_prod Finset.univ
      (fun i => smear (S.a k) (F i).1.1 (F i).2)
  have h1 : (∏ i, smear (S.a k) (sreflG τ (F i)).1.1 (sreflG τ (F i)).2)
      = LatticeReflection.ireflObs τ 0 (∏ i, smear (S.a k) (F i).1.1 (F i).2) := by
    rw [hθ]
    exact Finset.prod_congr rfl (fun i _ => (ireflObs_smear ha τ _ _).symm)
  show S.ν k (∏ i, smear (S.a k) (sreflG τ (F i)).1.1 (sreflG τ (F i)).2)
    = S.ν k (∏ i, smear (S.a k) (F i).1.1 (F i).2)
  rw [h1]
  exact hR k τ 0 _

/-- DERIVED: `4` the dimension. -/
theorem timeVecG_add (S : Sched G) (m : ℕ) (τ : Fin 4) (a b : ℤ) :
    timeVecG S m τ a + timeVecG S m τ b = timeVecG S m τ (a + b) := by
  unfold timeVecG
  rw [site_add, axisVec_add]

/-- DERIVED: `4` the dimension; `0` the zero vector. -/
theorem timeVecG_zero (S : Sched G) (m : ℕ) (τ : Fin 4) : timeVecG S m τ 0 = 0 := by
  unfold timeVecG
  rw [axisVec_zero, site_zero]

/-- DERIVED: `4` the dimension. -/
theorem timeVecG_self (S : Sched G) (m : ℕ) (τ : Fin 4) (n : ℤ) :
    timeVecG S m τ n τ = S.a m * n := by
  simp [timeVecG, site, axisVec]

/-- DERIVED: `4` the dimension; `0` the sign. -/
theorem timeVecG_nonneg_nat (S : Sched G) (m : ℕ) (τ : Fin 4) (n : ℕ) :
    0 ≤ timeVecG S m τ n τ := by
  rw [timeVecG_self]
  exact mul_nonneg (S.a_pos m).le (by positivity)

/-- The time reflection of a time vector is the opposite time vector.

DERIVED: `4` the dimension. -/
theorem reflR_timeVecG (S : Sched G) (m : ℕ) (τ : Fin 4) (n : ℤ) :
    reflR τ (timeVecG S m τ n) = timeVecG S m τ (-n) := by
  funext i
  by_cases h : i = τ
  · subst h
    simp [reflR, timeVecG, site, axisVec]
  · simp [reflR, timeVecG, site, axisVec, h]

/-- **Two successive half steps are one step**, on a dyadic schedule.

DERIVED: `4` the dimension; `1` the unit time step; the half step is level `m + 1`. -/
theorem timeVecG_one_add (S : Sched G) (hd : SchedDyadic S) (m : ℕ) (τ : Fin 4) :
    timeVecG S (m + 1) τ 1 + timeVecG S (m + 1) τ 1 = timeVecG S m τ 1 := by
  unfold timeVecG
  funext i
  simp only [Pi.add_apply, site]
  rw [← hd m (m + 1) (by omega), Nat.add_sub_cancel_left, pow_one]
  ring

/-- DERIVED: `0` the zero vector. -/
theorem monoShiftG_zero (P : MonoG G) : monoShiftG 0 P = P := by
  obtain ⟨n, F⟩ := P
  exact congrArg (Sigma.mk n) (funext fun i => by
    show ((F i).1, (F i).2.translate 0) = F i
    rw [TestFn.translate_zero])

/-- DERIVED: `4` the dimension. -/
theorem monoShiftG_shift (v w : Fin 4 → ℝ) (P : MonoG G) :
    monoShiftG w (monoShiftG v P) = monoShiftG (v + w) P := by
  obtain ⟨n, F⟩ := P
  exact congrArg (Sigma.mk n) (funext fun i => by
    show ((F i).1, ((F i).2.translate v).translate w) = ((F i).1, (F i).2.translate (v + w))
    rw [TestFn.translate_translate])

/-- The reflected shifted monomial against `Q` is the unshifted pair with `Q` shifted, translated
back by one step.

DERIVED: `4` the dimension; `1` the unit step. -/
theorem pairFamG_shift (S : Sched G) (m : ℕ) (τ : Fin 4) (P Q : MonoG G) :
    pairFamG τ (monoShiftG (timeVecG S m τ 1) P) Q
      = fun x => ((pairFamG τ P (monoShiftG (timeVecG S m τ 1) Q) x).1,
          (pairFamG τ P (monoShiftG (timeVecG S m τ 1) Q) x).2.translate (timeVecG S m τ (-1))) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate (timeVecG S m τ 1)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (timeVecG S m τ (-1)))
    rw [TestFn.reflect_translate, reflR_timeVecG]
  | inr j =>
    show Q.2 j
      = ((Q.2 j).1, ((Q.2 j).2.translate (timeVecG S m τ 1)).translate (timeVecG S m τ (-1)))
    rw [TestFn.translate_translate, timeVecG_add, add_neg_cancel, timeVecG_zero,
      TestFn.translate_zero]

/-- Both monomials shifted by `n` steps: a per-factor dyadic translate of the unshifted pair.

DERIVED: `4` the dimension. -/
theorem pairFamG_shiftN (S : Sched G) (m : ℕ) (τ : Fin 4) (n : ℤ) (P Q : MonoG G) :
    pairFamG τ (monoShiftG (timeVecG S m τ n) P) (monoShiftG (timeVecG S m τ n) Q)
      = fun x => ((pairFamG τ P Q x).1, (pairFamG τ P Q x).2.translate
          (site (S.a m) (Sum.elim (fun _ => axisVec τ (-n)) (fun _ => axisVec τ n) x))) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate (timeVecG S m τ n)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (timeVecG S m τ (-n)))
    rw [TestFn.reflect_translate, reflR_timeVecG]
  | inr j => rfl

/-- A translation forward in time keeps `posAtG`.

DERIVED: `4` the dimension; `0` the sign of the time component. -/
theorem posAtG_shift {τ : Fin 4} {d : ℝ} {P : MonoG G} (h : posAtG τ d P) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v τ) : posAtG τ d (monoShiftG v P) := by
  intro i y hy
  have h1 := h i (y - v) hy
  have h2 : (y - v) τ = y τ - v τ := rfl
  rw [h2] at h1
  linarith

end Geometry

/-! ## 4. The flowed limit and its covariances -/

section Limit

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The flowed lattice function of a `GFlow` is the lattice function of the flowed data.

DERIVED: no numeral. -/
theorem latSFG_eq (S : Sched G) (Φ : GFlow G) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SFieldG G) : latSFG S Φ.map k F = latSG S k (fun i => Φ.field k (F i)) := rfl

/-- **Existence of the flowed limit** along `ultra` under the uniform bound.

DERIVED: `0` the zero translation. -/
theorem tendsto_contSFG (S : Sched G) (Φ : ℕ → LField G → LField G) (hB : UniformBoundFG S Φ)
    {ι : Type} [Fintype ι] (F : ι → SFieldG G) :
    Tendsto (fun k => latSFG S Φ k F) (ultra : Filter ℕ) (𝓝 (contSFG S Φ F)) := by
  obtain ⟨C, hC⟩ := hB ι F
  have h0 := hC 0 (fun _ => 0)
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **OS0 for the flowed limit**: a bound per family, uniform over dyadic translations.

DERIVED: no numeral. -/
theorem exists_abs_contSFG_le (S : Sched G) (Φ : ℕ → LField G → LField G)
    (hB : UniformBoundFG S Φ) {ι : Type} [Fintype ι] (F : ι → SFieldG G) :
    ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
      |contSFG S Φ (fun i => ((F i).1, (F i).2.translate (site (S.a m) (n i))))| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB ι F
  exact ⟨C, fun m n =>
    le_of_tendsto (tendsto_contSFG S Φ hB _).abs ((hC m n).filter_mono ultra_le)⟩

/-- **OS3, symmetry**: reindexing a family does not change its flowed continuum function.

DERIVED: no numeral. -/
theorem contSFG_comp_equiv (S : Sched G) (Φ : ℕ → LField G → LField G) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (F : ι → SFieldG G) :
    contSFG S Φ (F ∘ e) = contSFG S Φ F := by
  unfold contSFG
  congr 1
  funext k
  show latSG S k ((fun i => (Φ k (F i).1, (F i).2)) ∘ e) = latSG S k (fun i => (Φ k (F i).1, (F i).2))
  exact latSG_comp_equiv S k e (fun i => (Φ k (F i).1, (F i).2))

/-- **OS1, dyadic translations**: on a dyadically translation-invariant schedule, translating every
test function by `site (S.a m) n` leaves the flowed continuum function unchanged.

DERIVED: no numeral. -/
theorem contSFG_translate (S : Sched G) (hT : SchedTransInv S) (Φ : ℕ → LField G → LField G)
    {ι : Type} [Fintype ι] (F : ι → SFieldG G) (m : ℕ) (n : ISite) :
    contSFG S Φ (fun i => ((F i).1, (F i).2.translate (site (S.a m) n))) = contSFG S Φ F := by
  unfold contSFG
  refine limUnder_congr_ultra ?_
  filter_upwards [Filter.eventually_ge_atTop m] with k hk
  exact hT ι (fun i => (Φ k (F i).1, (F i).2)) m k hk n

/-- **OS1, the axis reflections**: on a reflection-invariant schedule, reflecting every field and test
function in the axis `τ` leaves the flowed continuum function unchanged.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem contSFG_reflect (S : Sched G) (hR : SchedReflInv S) (Φ : GFlow G) (τ : Fin 4) {ι : Type}
    [Fintype ι] (F : ι → SFieldG G) :
    contSFG S Φ.map (fun i => sreflG τ (F i)) = contSFG S Φ.map F := by
  unfold contSFG
  congr 1
  funext k
  have hfam : (fun i => Φ.field k (sreflG τ (F i))) = fun i => sreflG τ (Φ.field k (F i)) := by
    funext i
    show (Φ.map k ((F i).1.refl τ), (F i).2.reflect τ)
      = ((Φ.map k (F i).1).refl τ, (F i).2.reflect τ)
    rw [Φ.map_refl]
  show latSG S k (fun i => Φ.field k (sreflG τ (F i))) = latSG S k (fun i => Φ.field k (F i))
  rw [hfam]
  exact latSG_reflG S hR k τ _

end Limit

/-! ## 5. Reflection positivity of the flowed limit beyond the margin -/

section Positivity

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The flowed reflected pair is the reflected pair of the flowed monomials.

DERIVED: `4` the dimension. -/
theorem field_pairFamG (Φ : GFlow G) (k : ℕ) (τ : Fin 4) (P Q : MonoG G) :
    (fun x => Φ.field k (pairFamG τ P Q x)) = pairFamG τ (Φ.mono k P) (Φ.mono k Q) := by
  funext x
  cases x with
  | inl i =>
    show (Φ.map k ((P.2 i).1.refl τ), (P.2 i).2.reflect τ)
      = ((Φ.map k (P.2 i).1).refl τ, (P.2 i).2.reflect τ)
    rw [Φ.map_refl]
  | inr j => rfl

/-- DERIVED: `4` the dimension. -/
theorem latSFG_pairFamG (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P Q : MonoG G) :
    latSFG S Φ.map k (pairFamG τ P Q) = latSG S k (pairFamG τ (Φ.mono k P) (Φ.mono k Q)) := by
  show latSG S k (fun x => Φ.field k (pairFamG τ P Q x)) = _
  rw [field_pairFamG Φ k τ P Q]

/-- **The flowed reflection kernel** `S(θP ∪ Q)` over the schedule `S`.

DERIVED: `4` the dimension. -/
def kernFG (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (P Q : MonoG G) : ℝ :=
  contSFG S Φ.map (pairFamG τ P Q)

/-- **The flowed kernel is symmetric** on a reflection-invariant schedule:
`S(θP ∪ Q) = S(θQ ∪ P)`. The mirror of `ContinuumFlow.kernF_symm`.

DERIVED: `4` the dimension; `0` the reflection constant. -/
theorem kernFG_symm (S : Sched G) (hR : SchedReflInv S) (Φ : GFlow G) (τ : Fin 4)
    (P Q : MonoG G) : kernFG S Φ τ P Q = kernFG S Φ τ Q P := by
  unfold kernFG contSFG
  congr 1
  funext k
  rw [latSFG_pairFamG S Φ τ k P Q, latSFG_pairFamG S Φ τ k Q P, latSG_pairFamG, latSG_pairFamG,
    refl_pair_symmG (S.ν k) τ (hR k τ 0)
      (prodSmearG (S.a k) (Φ.mono k P)) (prodSmearG (S.a k) (Φ.mono k Q))]

/-- **A flow of physical range `r` keeps the positive half-space beyond `r`.** For a field local on
`T` of depth `D` below the plane, the flowed field is local on links of depth at most `D + range k`,
and `S.a k (D + range k) ≤ S.a k D + r < δ` eventually, since `S.a k D → 0`. The mirror of
`ContinuumFlow.Flow.posPreserving_of_physRange`.

DERIVED: `0` the plane; `4` the dimension. -/
theorem posPreserving_of_physRangeG (S : Sched G) (Φ : GFlow G) {r : ℝ} (hΦ : Φ.PhysRange S r)
    (τ : Fin 4) : Φ.PosPreserving S τ r := by
  intro O f δ _ hrδ hf
  obtain ⟨T, hT⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth τ T
  have ht : Tendsto (fun k => S.a k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using S.a_lim.mul_const (D : ℝ)
  have hΦ' : ∀ᶠ k in atTop, S.a k * (Φ.range k : ℝ) ≤ r := hΦ
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hrδ)), hΦ'] with k hk hkr
  have hk' : S.a k * (D : ℝ) < δ - r := hk
  obtain ⟨T', hT', hrange⟩ := Φ.map_local k O T hT
  have hD' : ∀ l ∈ T', -(l.2 τ) ≤ ((D + Φ.range k : ℕ) : ℤ) := by
    intro l' hl'
    obtain ⟨l, hl, hll⟩ := hrange l' hl'
    have h1 := hD l hl
    have h2 := (abs_le.mp (hll τ)).1
    have e : ((D + Φ.range k : ℕ) : ℤ) = (D : ℤ) + (Φ.range k : ℤ) := Nat.cast_add _ _
    rw [e]
    omega
  have haD : S.a k * ((D + Φ.range k : ℕ) : ℝ) ≤ δ := by
    have e : ((D + Φ.range k : ℕ) : ℝ) = (D : ℝ) + (Φ.range k : ℝ) := Nat.cast_add _ _
    rw [e, mul_add]
    linarith
  exact smear_mem_halfSpaceAlg (S.a_pos k) τ hT' hD' haD f hf

/-- **OS2 for the flowed limit, beyond the margin.** On a schedule whose states are reflection
positive at the plane `x_τ = 0`, under `UniformBoundFG` and `PosPreserving τ r`, for every finite set of
margin monomials and real coefficients, `0 ≤ ∑_{P,Q} c_P c_Q S(θP ∪ Q)`. The mirror of
`ContinuumFlow.contSF_gram_nonneg`.

DERIVED: `0` the plane and the sign concluded; `4` the dimension. -/
theorem contSFG_gram_nonneg (S : Sched G) (hP : SchedRP S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r)
    (s : Finset (MarginMonoG G τ r)) (c : MarginMonoG G τ r → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernFG S Φ τ P.1 Q.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have htend : Tendsto
      (fun k => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSFG S Φ.map k (pairFamG τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernFG S Φ τ P.1 Q.1)) :=
    tendsto_finsetSum _ (fun P _ => tendsto_finsetSum _
      (fun Q _ => (tendsto_contSFG S Φ.map hB (pairFamG τ P.1 Q.1)).const_mul (c P * c Q)))
  refine ge_of_tendsto htend ?_
  have hmem : ∀ᶠ k in atTop, ∀ P ∈ s, ∀ i : Fin P.1.1,
      smear (S.a k) (Φ.map k (P.1.2 i).1).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 :=
    (Filter.eventually_all_finset s).mpr (fun P _ =>
      Filter.eventually_all.mpr (fun i => by
        obtain ⟨d, hd, hrd, hPd⟩ := P.2
        exact hpos (P.1.2 i).1 (P.1.2 i).2 d hd hrd (hPd i)))
  have hev : ∀ᶠ k in atTop,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSFG S Φ.map k (pairFamG τ P.1 Q.1) := by
    filter_upwards [hmem] with k hk
    have hsum : ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSFG S Φ.map k (pairFamG τ P.1 Q.1)
        = ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * S.ν k
            (LatticeReflection.ireflObs τ 0 (prodSmearG (S.a k) (Φ.mono k P.1))
              * prodSmearG (S.a k) (Φ.mono k Q.1)) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
      rw [latSFG_pairFamG, latSG_pairFamG]
    have hX : (∑ P ∈ s, c P • prodSmearG (S.a k) (Φ.mono k P.1))
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 :=
      Submodule.sum_mem _ (fun P hP => Submodule.smul_mem _ _
        (HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
          (fun i _ => hk P hP i)))
    rw [hsum]
    exact le_of_le_of_eq (hP k τ _ hX)
      (gram_expand (S.ν k) (LatticeReflection.ireflObs τ 0) s c
        (fun P => prodSmearG (S.a k) (Φ.mono k P.1)))
  exact hev.filter_mono ultra_le

end Positivity

/-! ## 6. The flowed reconstruction -/

section FlowReconstruction

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The forward time step of a margin monomial by `S.a m` in direction `τ`.

DERIVED: `4` the dimension; `1` the unit time step. -/
def marginShiftG (S : Sched G) (τ : Fin 4) (m : ℕ) {r : ℝ} (P : MarginMonoG G τ r) :
    MarginMonoG G τ r :=
  ⟨monoShiftG (timeVecG S m τ 1) P.1, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, posAtG_shift hP (timeVecG_nonneg S m τ)⟩⟩

/-- DERIVED: `4` the dimension. -/
theorem marginShiftG_iterate (S : Sched G) (τ : Fin 4) (m n : ℕ) {r : ℝ}
    (P : MarginMonoG G τ r) :
    ((marginShiftG S τ m)^[n] P).1 = monoShiftG (timeVecG S m τ n) P.1 := by
  induction n with
  | zero =>
    show P.1 = monoShiftG (timeVecG S m τ ((0 : ℕ) : ℤ)) P.1
    rw [Nat.cast_zero, timeVecG_zero, monoShiftG_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show monoShiftG (timeVecG S m τ 1) ((marginShiftG S τ m)^[n] P).1 = _
    rw [ih, monoShiftG_shift, timeVecG_add, Nat.cast_succ]

/-- **Two half steps are one step**, on margin monomials of a dyadic schedule.

DERIVED: `4` the dimension; `1` the half-step offset. -/
theorem marginShiftG_half (S : Sched G) (hd : SchedDyadic S) (τ : Fin 4) (m : ℕ) {r : ℝ}
    (P : MarginMonoG G τ r) :
    marginShiftG S τ (m + 1) (marginShiftG S τ (m + 1) P) = marginShiftG S τ m P := by
  apply Subtype.ext
  show monoShiftG (timeVecG S (m + 1) τ 1) (monoShiftG (timeVecG S (m + 1) τ 1) P.1)
    = monoShiftG (timeVecG S m τ 1) P.1
  rw [monoShiftG_shift, timeVecG_one_add S hd]

/-- The empty margin monomial, the vacuum before completion.

DERIVED: `4` the dimension; the body's `0` is the number of factors and the sign of the margin.
CHOSEN: the margin `max r 0 + 1`; the empty family has no factor, so every margin above `max r 0`
serves. -/
def emptyMarginG (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (τ : Fin 4) (r : ℝ) : MarginMonoG G τ r :=
  ⟨⟨0, Fin.elim0⟩, max r 0 + 1, by linarith [le_max_right r 0], by linarith [le_max_left r 0],
    fun i => i.elim0⟩

/-- DERIVED: `4` the dimension. -/
theorem shift_emptyMarginG (S : Sched G) (τ : Fin 4) (m : ℕ) {r : ℝ} :
    marginShiftG S τ m (emptyMarginG G τ r) = emptyMarginG G τ r :=
  Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0))

/-- **The time step is symmetric for the flowed kernel** on a dyadically translation-invariant
schedule: `S(θ(TP) ∪ Q) = S(θP ∪ TQ)`. The mirror of `ContinuumFlow.kernF_shift`.

DERIVED: `4` the dimension; `1` the unit step. -/
theorem kernFG_shift (S : Sched G) (hT : SchedTransInv S) (Φ : GFlow G) (τ : Fin 4) (m : ℕ)
    (P Q : MonoG G) :
    kernFG S Φ τ (monoShiftG (timeVecG S m τ 1) P) Q
      = kernFG S Φ τ P (monoShiftG (timeVecG S m τ 1) Q) := by
  unfold kernFG
  rw [pairFamG_shift]
  exact contSFG_translate S hT Φ.map _ m (axisVec τ (-1))

/-- The flowed kernel of iterated steps is bounded uniformly in the number of steps.

DERIVED: `4` the dimension. -/
theorem kernFG_iterate_bound (S : Sched G) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (m : ℕ) (P Q : MarginMonoG G τ r) :
    ∃ C : ℝ, ∀ n : ℕ,
      |kernFG S Φ τ ((marginShiftG S τ m)^[n] P).1 ((marginShiftG S τ m)^[n] Q).1| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_contSFG_le S Φ.map hB (pairFamG τ P.1 Q.1)
  refine ⟨C, fun n => ?_⟩
  unfold kernFG
  rw [marginShiftG_iterate, marginShiftG_iterate, pairFamG_shiftN]
  exact hC m _

/-- `S(∅) = 1` for the flowed functions: the empty family reads `ν_k(1) = 1` at every step.

DERIVED: `1` the normalisation of a state; `4` the dimension. -/
theorem kernFG_empty (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (r : ℝ) :
    kernFG S Φ τ (emptyMarginG G τ r).1 (emptyMarginG G τ r).1 = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hconst : ∀ k,
      latSFG S Φ.map k (pairFamG τ (emptyMarginG G τ r).1 (emptyMarginG G τ r).1) = 1 := by
    intro k
    show S.ν k (∏ x : Fin 0 ⊕ Fin 0, _) = 1
    rw [Fintype.prod_empty]
    exact (S.ν k).map_one
  have hfun : (fun k => latSFG S Φ.map k
      (pairFamG τ (emptyMarginG G τ r).1 (emptyMarginG G τ r).1)) = fun _ => (1 : ℝ) :=
    funext hconst
  show limUnder (ultra : Filter ℕ)
      (fun k => latSFG S Φ.map k (pairFamG τ (emptyMarginG G τ r).1 (emptyMarginG G τ r).1)) = 1
  rw [hfun]
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨1, tendsto_const_nhds⟩) tendsto_const_nhds

/-- **The flowed transfer data at the step `S.a m`**, on margin monomials, from `gTransfer` with the
flowed kernel. The mirror of `ContinuumFlow.flowTransfer`.

DERIVED: `4` the dimension. -/
def flowTransferG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ) :
    Transfer.TransferData (MarginMonoG G τ r →₀ ℝ) :=
  gTransfer (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1)
    (fun P Q => kernFG_symm S hS.refl Φ τ P.1 Q.1)
    (fun s c => contSFG_gram_nonneg S hS.rp Φ hB τ hpos s c)
    (marginShiftG S τ m) (fun P Q => kernFG_shift S hS.trans Φ τ m P.1 Q.1)
    (fun P Q => kernFG_iterate_bound S Φ hB τ m P Q)
    (emptyMarginG G τ r) (shift_emptyMarginG S τ m) (kernFG_empty S Φ τ r)

/-- **The flowed transfer operator is positive**, the step `m + 1` being the half step.

DERIVED: `1` the half-step offset; `4` the dimension. -/
theorem flowTransferG_positive (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ) :
    GNSHilbert.PositiveTransfer (flowTransferG S hS Φ hB τ hpos m) :=
  gPositive (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1)
    (fun P Q => kernFG_symm S hS.refl Φ τ P.1 Q.1)
    (fun s c => contSFG_gram_nonneg S hS.rp Φ hB τ hpos s c)
    (marginShiftG S τ m) (fun P Q => kernFG_shift S hS.trans Φ τ m P.1 Q.1)
    (fun P Q => kernFG_iterate_bound S Φ hB τ m P Q)
    (emptyMarginG G τ r) (shift_emptyMarginG S τ m) (kernFG_empty S Φ τ r)
    (marginShiftG S τ (m + 1)) (fun P Q => kernFG_shift S hS.trans Φ τ (m + 1) P.1 Q.1)
    (fun P => marginShiftG_half S hS.dyadic τ m P)

/-- **The flowed reconstruction over `G`.** For every flow with the uniform bound over a schedule with
`SchedOS`, keeping the positive half-space beyond a margin `r`, every time direction `τ` and every
step `m`: a complete Hilbert space, a unit vacuum, a self-adjoint transfer operator fixing it with
spectrum in `[0, 1]`, and `⟪gVec P, gVec Q⟫ = S(θP ∪ Q)` on margin monomials. The mirror of
`ContinuumFlow.flow_reconstruction`.

DERIVED: `4` the dimension. -/
theorem flow_reconstructionG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ) :
    Reconstructed (flowTransferG S hS Φ hB τ hpos m)
      ∧ ∀ P Q : MarginMonoG G τ r,
        inner ℂ (gVec (flowTransferG S hS Φ hB τ hpos m) P)
            (gVec (flowTransferG S hS Φ hB τ hpos m) Q)
          = (kernFG S Φ τ P.1 Q.1 : ℂ) :=
  ⟨reconstructed_of_positive _ (flowTransferG_positive S hS Φ hB τ hpos m),
    fun P Q => inner_gVec (flowTransferG S hS Φ hB τ hpos m)
      (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1) (fun _ _ => rfl) P Q⟩

/-- **The reconstruction from a flow of physical range `r`**: `flow_reconstructionG` with
`PosPreserving` from `posPreserving_of_physRangeG`.

DERIVED: `4` the dimension. -/
theorem flow_reconstruction_physRangeG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) {r : ℝ} (hΦ : Φ.PhysRange S r) (τ : Fin 4) (m : ℕ) :
    Reconstructed (flowTransferG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hΦ τ) m) :=
  (flow_reconstructionG S hS Φ hB τ (posPreserving_of_physRangeG S Φ hΦ τ) m).1

/-- **The flowed reconstruction at the canonical schedule of `G`**: `flow_reconstructionG` at
`canonSched G`, with `SchedOS` from `schedOS_canonSched`.

DERIVED: `4` the dimension. -/
theorem flow_reconstruction_canonG [GaugeSimple G] (Φ : GFlow G)
    (hB : UniformBoundFG (canonSched G) Φ.map) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving (canonSched G) τ r) (m : ℕ) :
    Reconstructed (flowTransferG (canonSched G) schedOS_canonSched Φ hB τ hpos m)
      ∧ ∀ P Q : MarginMonoG G τ r,
        inner ℂ (gVec (flowTransferG (canonSched G) schedOS_canonSched Φ hB τ hpos m) P)
            (gVec (flowTransferG (canonSched G) schedOS_canonSched Φ hB τ hpos m) Q)
          = (kernFG (canonSched G) Φ τ P.1 Q.1 : ℂ) :=
  flow_reconstructionG (canonSched G) schedOS_canonSched Φ hB τ hpos m

end FlowReconstruction

/-! ## 7. Non-triviality -/

section Open

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **Non-triviality of the flowed limit (stated, not proved).** Some margin monomial `Q` has
`S(θQ ∪ Q) − S(Q)² ≠ 0`, with `S(Q) = S(θ∅ ∪ Q)`. The mirror of `ContinuumFlow.FlowConnectedNonzero`.

DERIVED: `0` the value excluded; `2` the square; `4` the dimension. -/
def FlowConnectedNonzeroG (S : Sched G) (Φ : GFlow G) (τ : Fin 4) (r : ℝ) : Prop :=
  ∃ Q : MarginMonoG G τ r,
    kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ (emptyMarginG G τ r).1 Q.1 ^ 2 ≠ 0

/-- **Non-triviality of the flowed reconstruction.** Under `FlowConnectedNonzeroG`, at every step the
Hilbert space has a non-zero vector orthogonal to the vacuum and not a complex multiple of it. The
mirror of `ContinuumFlow.exists_orth_ne_zero_flow`.

DERIVED: `0` the vanishing pairing and the zero vector; `1` the vacuum coefficient; `2` the square;
`4` the dimension. -/
theorem exists_orth_ne_zero_flowG (S : Sched G) (hS : SchedOS S) (Φ : GFlow G)
    (hB : UniformBoundFG S Φ.map) (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving S τ r) (m : ℕ)
    (h : FlowConnectedNonzeroG S Φ τ r) :
    ∃ u : GNSHilbert.H (flowTransferG S hS Φ hB τ hpos m).toReflForm,
      inner ℂ (GNSHilbert.Omega (flowTransferG S hS Φ hB τ hpos m).toReflForm
        (flowTransferG S hS Φ hB τ hpos m).vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega (flowTransferG S hS Φ hB τ hpos m).toReflForm
        (flowTransferG S hS Φ hB τ hpos m).vac := by
  obtain ⟨Q, hQ⟩ := h
  have hx : (flowTransferG S hS Φ hB τ hpos m).form (Finsupp.single Q 1) (Finsupp.single Q 1)
      - (flowTransferG S hS Φ hB τ hpos m).form (Finsupp.single Q 1)
          (flowTransferG S hS Φ hB τ hpos m).vac ^ 2 ≠ 0 := by
    show gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1)
        (Finsupp.single Q 1) (Finsupp.single Q 1)
      - gForm (fun P Q : MarginMonoG G τ r => kernFG S Φ τ P.1 Q.1)
        (Finsupp.single Q 1) (Finsupp.single (emptyMarginG G τ r) 1) ^ 2 ≠ 0
    rw [gForm_single, gForm_single]
    simp only [one_mul]
    show kernFG S Φ τ Q.1 Q.1 - kernFG S Φ τ Q.1 (emptyMarginG G τ r).1 ^ 2 ≠ 0
    rw [← kernFG_symm S hS.refl Φ τ (emptyMarginG G τ r).1 Q.1]
    exact hQ
  obtain ⟨u, hu, hu0⟩ := ContinuumSep.exists_orth_ne_zero (flowTransferG S hS Φ hB τ hpos m) _ hx
  exact ⟨u, hu, hu0, ContinuumSep.not_mem_span_vac _ hu hu0⟩

end Open

/-! ## 8. At `SU(N)` -/

section SU

/-- `Flow N` as a `GFlow (SU N)`, field by field.

DERIVED: no numeral. -/
def _root_.MassGap.ContinuumFlow.Flow.toGFlow {N : ℕ} [NeZero N] (Φ : Flow N) : GFlow (MassGap.SUN.SU N) where
  map := Φ.map
  range := Φ.range
  map_refl := Φ.map_refl
  map_local := Φ.map_local

/-- **At `SU(N)` and `schedSU N` the flowed kernel is `ContinuumFlow.kernF`**, by definition.

DERIVED: `0` the excluded colour count. -/
theorem kernFG_SU {N : ℕ} [NeZero N] (Φ : Flow N) (τ : Fin 4) (P Q : MonoG (MassGap.SUN.SU N)) :
    kernFG (schedSU N) Φ.toGFlow τ P Q = kernF (NeZero.ne N) Φ τ P Q := rfl

end SU

end MassGap.FlowG

end

#print axioms MassGap.FlowG.schedDyadic_canonSched
#print axioms MassGap.FlowG.schedOS_canonSched
#print axioms MassGap.FlowG.sched_a_eq_mul
#print axioms MassGap.FlowG.fieldMapG_refl
#print axioms MassGap.FlowG.refl_scaleFieldG
#print axioms MassGap.FlowG.zOnG_refl
#print axioms MassGap.FlowG.energy0G
#print axioms MassGap.FlowG.latSG_pairFamG
#print axioms MassGap.FlowG.refl_pair_symmG
#print axioms MassGap.FlowG.latSG_reflG
#print axioms MassGap.FlowG.timeVecG_one_add
#print axioms MassGap.FlowG.pairFamG_shift
#print axioms MassGap.FlowG.pairFamG_shiftN
#print axioms MassGap.FlowG.tendsto_contSFG
#print axioms MassGap.FlowG.exists_abs_contSFG_le
#print axioms MassGap.FlowG.contSFG_comp_equiv
#print axioms MassGap.FlowG.contSFG_translate
#print axioms MassGap.FlowG.contSFG_reflect
#print axioms MassGap.FlowG.kernFG_symm
#print axioms MassGap.FlowG.posPreserving_of_physRangeG
#print axioms MassGap.FlowG.contSFG_gram_nonneg
#print axioms MassGap.FlowG.marginShiftG_half
#print axioms MassGap.FlowG.kernFG_shift
#print axioms MassGap.FlowG.kernFG_iterate_bound
#print axioms MassGap.FlowG.kernFG_empty
#print axioms MassGap.FlowG.flowTransferG
#print axioms MassGap.FlowG.flowTransferG_positive
#print axioms MassGap.FlowG.flow_reconstructionG
#print axioms MassGap.FlowG.flow_reconstruction_physRangeG
#print axioms MassGap.FlowG.flow_reconstruction_canonG
#print axioms MassGap.FlowG.exists_orth_ne_zero_flowG
#print axioms MassGap.FlowG.kernFG_SU
