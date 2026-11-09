import Mathlib
import MassGap.ShiftInvG

/-!
# MassGap.EnergyBoundG — the uniform bound of the energy density over a schedule of `G`

`ShiftInvG.clayStatementAtG_of_inputsG'` takes `hUB : UniformBoundFG S (energyMapG S W D)` at
`S = canonSched G`. At `SU(N)` the same input is `ObserverOS.uniformBoundF_energy0`, which reduces it
to facts about the class `D`: it is reflection-closed, its fields are non-negative, and the flowed
energy in every physical cube has bounded even moments (`ObserverEnergyBox.CubeMomentBound`); the
`G` form below does not need the reflection closure. This module carries
that reduction to every gauge group `G` and every schedule `S` whose states are invariant under the
dyadic translations (`ClayWiringG.SchedTransInv S`):

| step | `SU(N)` | here (any `G`, `S`) |
|---|---|---|
| cube energy | `ObserverEnergyBox.cubeSum` | `cubeSumG` |
| cube moment input | `ObserverEnergyBox.CubeMomentBound` | `CubeMomentBoundG` |
| smeared scaled field ≤ cube energy | `ObserverEnergyBox.abs_smear_scaled_le` (at `s = 0`) | `abs_smear_scaled_leG` |
| bounded field, bounded smeared moments | `ObserverEnergyMoments.smear_moment_le_of_norm` | `smear_moment_le_of_normG` |
| translated smeared moment | `ObserverEnergyMoments.smear_moment_translate` | `smear_moment_translateG` (from `SchedTransInv S`) |
| smeared moments give the uniform bound | `ObserverEnergyMoments.uniformBoundF_of_smearedMomentBound` | `uniformBoundFG_of_smearedMoments` |
| smeared moments of the energy density | `ObserverEnergyBox.smearedMoments_of_cubeMoments`, `smearedMomentBound_energyOn` | `smearedMoments_energyMapG` |
| the uniform bound | `ObserverOS.uniformBoundF_energy0` | `uniformBoundFG_energy` |

No property of `G` beyond the `GaugeGroup` interface enters: the bound comes from the state
(through the cube moments), not from a pointwise cap on the field. Off `D` the flowed field is
bounded by the sup norm of the field (a continuous function on a compact space).

At `canonSched G` the translation input is `ShiftInvG.schedTransInv_canonSched`
(`uniformBoundFG_energy_canon`); `clayStatementAtG_of_inputsG''` is
`ShiftInvG.clayStatementAtG_of_inputsG'` with `hUB` replaced by `hpos` and `hcube`.
`cubeMomentBoundG_schedSU`: at `schedSU N` the cube moment input is the `SU(N)` one; it reaches the
capstone's `canonSched G` at `SU(N)` through `ClayTreeG.canonSched_SU`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the cell-volume exponent; `2` makes a power even; `1`
the spacing bound and the unit observable; `0` the signs; `3` is `norm_smear_le`'s.
-/

noncomputable section

namespace MassGap.EnergyBoundG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverEnergyBox MassGap.ObserverEnergyMoments
  MassGap.ClayTreeG MassGap.ClayWiringG Filter
open scoped Topology

/-! ## 1. The cube energy and the smeared moments over `G` -/

section Cube

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cube energy over `G`**: `∑_{x ∈ box ⌈R/a⌉} 1_{[-R,R]⁴}(a x) · F ∘ T_x`, the body of
`ObserverEnergyBox.cubeSum` with `SU N` replaced by `G`.

DERIVED: `4` the dimension. -/
def cubeSumG (a R : ℝ) (F : C(IConf G, ℝ)) : C(IConf G, ℝ) :=
  ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) • transObs x F

/-- DERIVED: no numeral. -/
theorem cubeSumG_apply (a R : ℝ) (F : C(IConf G, ℝ)) (U : IConf G) :
    cubeSumG a R F U = ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U) := by
  unfold cubeSumG
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    smul_eq_mul]

/-- The cube energy of a non-negative reading is non-negative.

DERIVED: `0` the sign. -/
theorem cubeSumG_nonneg (a R : ℝ) {F : C(IConf G, ℝ)} (hF : ∀ U, 0 ≤ F U) (U : IConf G) :
    0 ≤ cubeSumG a R F U := by
  rw [cubeSumG_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (cubeInd_nonneg _ _) (hF _))

/-- **The smeared scaled field is dominated by the cube energy**: for `F ≥ 0` and `|g| ≤ M`
supported in `[-R, R]⁴`, `|smear a (a⁻⁴ F) g| ≤ M · cubeSumG a R F` pointwise.

DERIVED: `4` the cell-volume exponent and the canonical dimension; `0` the signs. -/
theorem abs_smear_scaled_leG {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (hF : ∀ U, 0 ≤ F U)
    (g : TestFn) {R M : ℝ} (hg : IsTest g.1 R M) (U : IConf G) :
    |smear a ((a ^ 4)⁻¹ • F) g U| ≤ M * cubeSumG a R F U := by
  rw [smear_eq_sum ha _ g hg (subset_refl _), cubeSumG_apply, Finset.mul_sum]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have h4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha.ne'
  have e : a ^ 4 * g.1 (site a x) * ((a ^ 4)⁻¹ * F (transConf x U))
      = g.1 (site a x) * F (transConf x U) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (hF _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_le_mul_cubeInd hg _) (hF _)

/-- **The smeared moments of a bounded field**: at `0 < a ≤ 1`, `ν((smear a F f)^{2p}) ≤
(B M (2R + 3)⁴)^{2p}` when `‖F‖ ≤ B`, in every state on `IConf G`.

DERIVED: `0` the sign of `a`; `1` bounds `a`; `2`, `3`, `4` are `norm_smear_le`'s and the even
power's. -/
theorem smear_moment_le_of_normG (ν : MassGap.DLRLimit.State (IConf G)) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (F : C(IConf G, ℝ)) {B : ℝ} (hF : ‖F‖ ≤ B) (f : TestFn) {R M : ℝ}
    (hf : IsTest f.1 R M) (p : ℕ) :
    ν (smear a F f ^ (2 * p)) ≤ (B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) := by
  have hn := (norm_smear_le ha ha1 F f hf).trans
    (mul_le_mul_of_nonneg_right hF (mul_nonneg hf.M_nonneg (by have := hf.1; positivity)))
  calc ν (smear a F f ^ (2 * p))
      ≤ ν ((B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) • (1 : C(IConf G, ℝ))) := ν.mono (fun U => by
        rw [ContinuousMap.pow_apply]
        simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
        have hU : |smear a F f U| ≤ B * (M * (2 * R + 3) ^ 4) := by
          have := (smear a F f).norm_coe_le_norm U
          rw [Real.norm_eq_abs] at this
          exact this.trans hn
        rw [← (even_two_mul p).pow_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hU _)
    _ = (B * (M * (2 * R + 3) ^ 4)) ^ (2 * p) := by rw [ν.map_smul, ν.map_one, mul_one]

end Cube

/-! ## 2. The uniform bound from smeared moments, over a translation-invariant schedule -/

section Uniform

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A translated smeared moment is the untranslated one**, for a schedule with `SchedTransInv S`:
translating `f` by `site (S.a j) p` leaves `ν_k((smear a_k P f)^q)` unchanged at every `k ≥ j`.

DERIVED: no numeral. -/
theorem smear_moment_translateG (S : Sched G) (hI : SchedTransInv S) {j k : ℕ} (hjk : j ≤ k)
    (P : LField G) (f : TestFn) (p : ISite) (q : ℕ) :
    S.ν k (smear (S.a k) P.1 (f.translate (site (S.a j) p)) ^ q)
      = S.ν k (smear (S.a k) P.1 f ^ q) := by
  have e : ∀ g : C(IConf G, ℝ), (∏ _i : Fin q, g) = g ^ q := fun g => by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h := hI (Fin q) (fun _ => (P, f)) j k hjk p
  change S.ν k (∏ _i : Fin q, smear (S.a k) P.1 (f.translate (site (S.a j) p)))
    = S.ν k (∏ _i : Fin q, smear (S.a k) P.1 f) at h
  rwa [e, e] at h

/-- **The uniform bound from the smeared moments**, over any schedule with `SchedTransInv S`: if
every even moment `ν_k((smear a_k (Φ_k O) f)^{2p})` is bounded eventually in the step, then
`UniformBoundFG S Φ`. For a family of `n` fields the constant is `1 + ∑ᵢ Cᵢ`, `Cᵢ` the eventual
bound on the `2n`-th moment of the `i`-th smeared field.

DERIVED: `1` and `2` are `abs_prod_le_one_add_sum_pow`'s. -/
theorem uniformBoundFG_of_smearedMoments (S : Sched G) (hI : SchedTransInv S)
    (Φ : ℕ → LField G → LField G)
    (h : ∀ (O : LField G) (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      S.ν k (smear (S.a k) (Φ k O).1 f ^ (2 * p)) ≤ C) :
    UniformBoundFG S Φ := by
  intro ι _ F
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop,
      S.ν k (smear (S.a k) (Φ k (F i).1).1 (F i).2 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => h (F i).1 (F i).2 (Fintype.card ι)
  choose C hC using hC
  refine ⟨1 + ∑ i, C i, fun m n => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop m, Filter.eventually_all.mpr hC] with k hk hCk
  show |S.ν k (∏ i, smear (S.a k) (Φ k (F i).1).1 ((F i).2.translate (site (S.a m) (n i))))| ≤ _
  set T : ι → C(IConf G, ℝ) := fun i => smear (S.a k) (Φ k (F i).1).1
      ((F i).2.translate (site (S.a m) (n i))) with hT
  have hpt := abs_state_le_of_abs_le (S.ν k) (∏ i, T i)
    (1 + ∑ i, T i ^ (2 * Fintype.card ι))
    (fun U => by
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.sum_apply,
        ContinuousMap.prod_apply, ContinuousMap.pow_apply]
      exact abs_prod_le_one_add_sum_pow _)
  rw [(S.ν k).map_add, (S.ν k).map_one, (S.ν k).map_sum] at hpt
  refine hpt.trans (add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_)))
  rw [hT]
  simp only
  rw [smear_moment_translateG S hI hk]
  exact hCk i

end Uniform

/-! ## 3. The energy density -/

section Energy

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cube moment bound over a schedule**: for every `R ≥ 0` and `p`, the `2p`-th moment of the
cube energy `cubeSumG a_k R (O ∘ V_k)` in the state `ν_k` is bounded eventually in the step; the
body of `ObserverEnergyBox.CubeMomentBound` with `stateK`, `dySpacing` replaced by `S.ν`, `S.a`.

DERIVED: `0` the lower end of `R`; `2` makes the power even. -/
def CubeMomentBoundG (S : Sched G) (W : ConfFlowG G) (O : LField G) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
    S.ν k (cubeSumG (S.a k) R (W.fieldMap k O).1 ^ (2 * p)) ≤ C

/-- **The energy density as an observable**: `(energyMapG S W D k O).1 = zOnG S D k O • (O ∘ V_k)`.

DERIVED: `0` the zero subtraction. -/
theorem energyMapG_val (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (k : ℕ)
    (O : LField G) :
    (energyMapG S W D k O).1 = zOnG S D k O • (W.fieldMap k O).1 := by
  have h0 : sOnG D (fun _ _ => (0 : ℝ)) k O = 0 := by
    unfold sOnG
    split_ifs <;> rfl
  show zOnG S D k O • ((W.fieldMap k O).1 - sOnG D (fun _ _ => (0 : ℝ)) k O • (1 : C(IConf G, ℝ)))
    = _
  rw [h0, zero_smul, sub_zero]

/-- **The smeared moments of the energy density**: on a class `D` of non-negative fields with
`CubeMomentBoundG S W` on `D`, every even moment of every smeared `energyMapG S W D k O` is bounded
eventually in the step. On `D` the bound is `2^{2p} (M^{2p} C + 0^{2p})` (`C` the cube bound, `M` the bound of `f`);
off `D` it is `(‖O‖ M (2R + 3)⁴)^{2p}`.

DERIVED: `1` the spacing bound and the unscaled factor; `2`, `3`, `4` as in
`smear_moment_le_of_normG`; `0` the signs. -/
theorem smearedMoments_energyMapG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G))
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) :
    ∀ (O : LField G) (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      S.ν k (smear (S.a k) (energyMapG S W D k O).1 f ^ (2 * p)) ≤ C := by
  intro O f p
  obtain ⟨R, M, hf⟩ := f.2
  have hM := hf.M_nonneg
  by_cases hO : O ∈ D
  · obtain ⟨C, hC⟩ := hcube O hO R hf.1 p
    refine ⟨2 ^ (2 * p) * (M ^ (2 * p) * C + 0 ^ (2 * p)), ?_⟩
    filter_upwards [hC] with k hCk
    have ha := S.a_pos k
    have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
    have hz : zOnG S D k O = (S.a k ^ 4)⁻¹ := by
      unfold zOnG
      rw [if_pos hO]
    rw [energyMapG_val, hz]
    have h1 := state_pow_le_of_abs_le (S.ν k)
      (smear (S.a k) ((S.a k ^ 4)⁻¹ • (W.fieldMap k O).1) f)
      (cubeSumG (S.a k) R (W.fieldMap k O).1) hM le_rfl
      (fun U => by
        rw [abs_of_nonneg (cubeSumG_nonneg _ _ hF U), add_zero]
        exact abs_smear_scaled_leG ha _ hF f hf U) p
    exact h1.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hCk (pow_nonneg hM _)) le_rfl) (pow_nonneg (by norm_num) _))
  · refine ⟨(‖O.1‖ * (M * (2 * R + 3) ^ 4)) ^ (2 * p), ?_⟩
    filter_upwards [S.a_lim.eventually (gt_mem_nhds one_pos)] with k hk1
    have hz : zOnG S D k O = 1 := by
      unfold zOnG
      rw [if_neg hO]
    have hG : ‖(energyMapG S W D k O).1‖ ≤ ‖O.1‖ := by
      rw [energyMapG_val, hz, one_smul]
      exact (ContinuousMap.norm_le _ (norm_nonneg O.1)).mpr
        (fun U => O.1.norm_coe_le_norm (W.V k U))
    exact smear_moment_le_of_normG (S.ν k) (S.a_pos k) hk1.le _ hG f hf p

/-- **The uniform bound of the energy density over a schedule of `G`**: for any schedule with
`SchedTransInv S` and any class `D` of non-negative fields with `CubeMomentBoundG S W` on `D`,
`UniformBoundFG S (energyMapG S W D)`. The `G` mirror of `ObserverOS.uniformBoundF_energy0`.

DERIVED: no numeral. -/
theorem uniformBoundFG_energy (S : Sched G) (hI : SchedTransInv S) (W : ConfFlowG G)
    (D : Set (LField G)) (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBoundG S W O) :
    UniformBoundFG S (energyMapG S W D) :=
  uniformBoundFG_of_smearedMoments S hI _ (smearedMoments_energyMapG S W D hpos hcube)

/-- **The uniform bound of the energy density at the canonical schedule of `G`**:
`uniformBoundFG_energy` with `hI := ShiftInvG.schedTransInv_canonSched`.

DERIVED: no numeral. -/
theorem uniformBoundFG_energy_canon [GaugeSimple G] (W : ConfFlowG G) (D : Set (LField G))
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBoundG (canonSched G) W O) :
    UniformBoundFG (canonSched G) (energyMapG (canonSched G) W D) :=
  uniformBoundFG_energy (canonSched G) ShiftInvG.schedTransInv_canonSched W D hpos hcube

end Energy

/-! ## 4. At `SU(N)` -/

section SU

variable {N : ℕ} [NeZero N]

/-- **At `schedSU N` the cube moment input is the `SU(N)` one**: `CubeMomentBound` of `W` at `O`
holds exactly when `CubeMomentBoundG (schedSU N) W.toG O` does.

DERIVED: no numeral. -/
theorem cubeMomentBoundG_schedSU (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) :
    CubeMomentBound (NeZero.ne N) W O ↔ CubeMomentBoundG (schedSU N) W.toG O :=
  Iff.rfl

end SU

/-! ## 5. The capstone with `hUB` replaced by its two inputs -/

section Capstone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring MassGap.ClayWiringG Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]
variable {τ : Fin 4} {r : ℝ}

/-- **`ClayStatementAtG G W D` with `SchedTransInv` discharged and `hUB` reduced**:
`ShiftInvG.clayStatementAtG_of_inputsG'` with `hUB := uniformBoundFG_energy_canon W D hpos hcube`.
In place of `hUB` it takes `hpos` (every field of `D` is non-negative) and `hcube`
(`CubeMomentBoundG (canonSched G) W` on `D`); every other hypothesis is the same.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_inputsG'' (W : ConfFlowG G) (D : Set (LField G))
    (X : OSDataSLinkedG G D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG (canonSched G) W D O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = symG (plaqFieldG ObserverEnergyMoments.q0))
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG (canonSched G) op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * (canonSched G).a k ^ 4) atTop
      (𝓝 (constsG G).cTr))
    (h0 : OS0OwnG (canonSched G) op Z)
    (hTC : TransContTG (canonSched G) (mixOfZG B op m Z))
    (hCov : TensorCovG (canonSched G) (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) (mixOfZG B op m Z))
    (hND : TensorNondegG (canonSched G) (mixOfZG B op m Z))
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBoundG (canonSched G) W O)
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG (canonSched G) (energyMapG (canonSched G) W D)
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG (canonSched G) W D O g)))
    (w : TSep τ → X.base.H) (hL : LinkHSG (canonSched G) W D X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG (canonSched G) (constsG G) Zc)
    (hWard : WardTG (canonSched G) (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG (canonSched G) C) (hLC : LinkCG (canonSched G) X C wC)
    (hTI : TInG (mixOfZG B op m Z) C X w wC) (hGen : ObsGenG (canonSched G) W D X) :
    ClayStatementAtG G W D :=
  ShiftInvG.clayStatementAtG_of_inputsG' W D X hSM hsa hXO op m Z hBC hRie b0 κ htr hop hZtie h0
    hTC hCov Gk hK hAF hNG hND (uniformBoundFG_energy_canon W D hpos hcube) hCut w hL hnt C wC
    hCT hWard hCD hCO hLC hTI hGen

end Capstone

end MassGap.EnergyBoundG

end

#print axioms MassGap.EnergyBoundG.cubeSumG_nonneg
#print axioms MassGap.EnergyBoundG.abs_smear_scaled_leG
#print axioms MassGap.EnergyBoundG.smear_moment_le_of_normG
#print axioms MassGap.EnergyBoundG.smear_moment_translateG
#print axioms MassGap.EnergyBoundG.uniformBoundFG_of_smearedMoments
#print axioms MassGap.EnergyBoundG.energyMapG_val
#print axioms MassGap.EnergyBoundG.smearedMoments_energyMapG
#print axioms MassGap.EnergyBoundG.uniformBoundFG_energy
#print axioms MassGap.EnergyBoundG.uniformBoundFG_energy_canon
#print axioms MassGap.EnergyBoundG.cubeMomentBoundG_schedSU
#print axioms MassGap.EnergyBoundG.clayStatementAtG_of_inputsG''
