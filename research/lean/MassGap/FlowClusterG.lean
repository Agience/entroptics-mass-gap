import Mathlib
import MassGap.WindowG
import MassGap.TimeGroupG
import MassGap.ContinuumCluster
import MassGap.ClayGFinal

/-!
# MassGap.FlowClusterG — the run seed of `G` gives the observer's transfer gap over `G`

`ContinuumCluster.lattice_cluster`, `FlowCapstone.kernF_cluster_of_fixedWindowDecay`,
`FlowCapstone.flowClusterAbs_of_flowCluster` and `LocalLink.observerGapAt_of_runSeed` with
`SUN.SU N` replaced by a `GaugeGroup G` with `GaugeSimple G`, at the canonical schedule `canonSched G`
(spacing `dySpacingG G`, state `periodicStateG G (dyBetaG G k)`).

* `DkG G τ k`: the gauge-invariant transfer data of `periodicStateG G (dyBetaG G k)` at the plane
  `x_τ = 0`; `lattice_clusterG`: from `GapAt (DkG G τ k) r`, the flowed lattice Schwinger functions of
  two positive-time monomials cluster at `r^{2n}` across `n` lattice steps.
* `kernFG_cluster_of_fixedWindowDecayG`: under `WindowG.FixedWindowDecayG G τ 0 L`, for every `GFlow`
  with the uniform bound that keeps the positive half-space beyond the margin `r`, the flowed kernel
  clusters at the physical rate `c/L` at every dyadic step; `flowClusterAbsG_of_fixedWindowDecayG`: the
  absolute form `TimeGroupG.FlowClusterAbsG`.
* `gapAt_of_runSeedG`: under `WindowG.RunSeedG G`, every such flow with a physical range has, at every
  step `m₀`, `TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched Φ hB 0 hphys m₀) ρ` for
  some `0 < ρ < 1` (`TimeGroupG.flowClusterAbs_iff_gapAtG`).
* `observerGapG_of_runSeedG`: the same at the observer's energy density
  `energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)` with `ClayGFinal.preBG W hU`, at step
  `0`: the input `hρ0`, `hρ1`, `hg` of `ClayGFinal.clayStatementAtG_GS_noNT`.

DERIVED (module-wide): `4` the dimension; `0` the plane, the reflection constant, the time axis and the
reference step; `2` the square and the dyadic refinement; `1` the top of the rate.
-/

noncomputable section

namespace MassGap.FlowClusterG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayTreeG MassGap.FlowG MassGap.TimeGroupG MassGap.ContinuumCluster
  MassGap.PeriodicReduceG MassGap.WindowG MassGap.ObserverLinkedG MassGap.SymPlaqG Filter
open scoped Topology

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-! ## 1. The lattice transfer data of each step, and clustering at each step -/

section Lattice

variable (G) in
/-- The transfer data of step `k`: the gauge-invariant transfer data at
`periodicStateG G (dyBetaG G k)`, plane `x_τ = 0`. -/
abbrev DkG (τ : Fin 4) (k : ℕ) :
    Transfer.TransferData ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) :=
  periodicGaugeInvDataG G τ 0 (dyBetaG G k)

theorem DkG_T_pow (τ : Fin 4) (k n : ℕ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0)) :
    ((((DkG G τ k).T ^ n) x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0))
        : C(IConf G, ℝ))
      = (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] (x : C(IConf G, ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

/-- The product of the smears of the flowed empty monomial is `1`. -/
theorem prodSmearG_mono_empty (Φ : GFlow G) (a : ℝ) (k : ℕ) :
    prodSmearG a (Φ.mono k (emptyMonoG G)) = 1 := by
  unfold prodSmearG
  exact Fintype.prod_empty _

/-- Translating a flowed smeared product by a lattice vector translates every test function. -/
theorem transObs_prodSmearG (Φ : GFlow G) {a : ℝ} (ha : 0 < a) (k : ℕ) (n : ISite) (Q : MonoG G) :
    transObs n (prodSmearG a (Φ.mono k Q))
      = prodSmearG a (Φ.mono k (monoShiftG (site a n) Q)) := by
  unfold prodSmearG
  rw [transObs_prod]
  exact Finset.prod_congr rfl (fun i _ => (smear_translate ha _ _ n).symm)

/-- A flowed monomial whose smeared factors lie in the half-space algebra is a vector of `DkG`. -/
theorem prodSmearG_mem (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P : MonoG G)
    (hk : ∀ i : Fin P.1, smear (dySpacingG G k) (Φ.map k (P.2 i).1).1 (P.2 i).2
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    prodSmearG (dySpacingG G k) (Φ.mono k P)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0 := by
  have h1 : prodSmearG (dySpacingG G k) (Φ.mono k P)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 :=
    HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ (fun i _ => hk i)
  have h2 : GaugeInvariantAlgebra.IsIGaugeInvariant (prodSmearG (dySpacingG G k) (Φ.mono k P)) :=
    isIGaugeInvariant_prod Finset.univ _
      (fun i _ => isIGaugeInvariant_smear (dySpacingG_pos G k) _ _)
  exact Submodule.mem_inf.mpr ⟨h1, h2⟩

/-- The flowed lattice Schwinger function of `θP ∪ Q` at step `k` is the reflected pairing of the
flowed smeared products in the state of step `k`. -/
theorem latSFG_canon (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P Q : MonoG G) :
    latSFG (canonSched G) Φ.map k (pairFamG τ P Q)
      = GaugeWilson.periodicStateG G (dyBetaG G k)
          (LatticeReflection.ireflObs τ 0 (prodSmearG (dySpacingG G k) (Φ.mono k P))
            * prodSmearG (dySpacingG G k) (Φ.mono k Q)) := by
  rw [latSFG_pairFamG, latSG_pairFamG]
  rfl

/-- **Clustering at step `k` from a `GapAt` rate.** -/
theorem lattice_clusterG (Φ : GFlow G) (τ : Fin 4) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hg : TransferGap.GapAt (DkG G τ k) r) (P Q : MonoG G)
    (hP : prodSmearG (dySpacingG G k) (Φ.mono k P)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0)
    (hQ : prodSmearG (dySpacingG G k) (Φ.mono k Q)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) (n : ℕ) :
    (latSFG (canonSched G) Φ.map k
        (pairFamG τ P (monoShiftG (site (dySpacingG G k) (axisVec τ n)) Q))
        - latSFG (canonSched G) Φ.map k (pairFamG τ P (emptyMonoG G))
          * latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q)) ^ 2
      ≤ r ^ (2 * n) * (latSFG (canonSched G) Φ.map k (pairFamG τ P P)
          * (latSFG (canonSched G) Φ.map k (pairFamG τ Q Q)
            - latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2))
    ∧ 0 ≤ latSFG (canonSched G) Φ.map k (pairFamG τ P P)
          * (latSFG (canonSched G) Φ.map k (pairFamG τ Q Q)
            - latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2) := by
  have ha := dySpacingG_pos G k
  set D := DkG G τ k with hD
  set y : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) := ⟨_, hP⟩ with hy
  set x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0) := ⟨_, hQ⟩ with hx
  have h := TransferGap.clustering_sq D hr hg n x y
  have hY := mul_nonneg (D.form_nonneg y) (D.form_nonneg (TransferGap.vacProj D x))
  have e1 : D.form y ((D.T ^ n) x)
      = latSFG (canonSched G) Φ.map k
          (pairFamG τ P (monoShiftG (site (dySpacingG G k) (axisVec τ n)) Q)) := by
    rw [latSFG_canon, ← transObs_prodSmearG Φ ha k _ Q]
    show GaugeWilson.periodicStateG G (dyBetaG G k)
        (LatticeReflection.ireflObs τ (2 * 0) (y : C(IConf G, ℝ))
          * ((((D.T ^ n) x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ 0))
            : C(IConf G, ℝ)))) = _
    rw [hD, DkG_T_pow, ishiftObsL_iterate]
    rfl
  have e2 : D.form y D.vac = latSFG (canonSched G) Φ.map k (pairFamG τ P (emptyMonoG G)) := by
    rw [latSFG_canon, prodSmearG_mono_empty, mul_one]
    show GaugeWilson.periodicStateG G (dyBetaG G k)
        (LatticeReflection.ireflObs τ (2 * 0) (y : C(IConf G, ℝ)) * 1) = _
    rw [mul_one]
    rfl
  have e3 : D.form D.vac x = latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q) := by
    rw [latSFG_canon, prodSmearG_mono_empty]
    rfl
  have e4 : D.form y y = latSFG (canonSched G) Φ.map k (pairFamG τ P P) := by
    rw [latSFG_canon]
    rfl
  have e4' : D.form x x = latSFG (canonSched G) Φ.map k (pairFamG τ Q Q) := by
    rw [latSFG_canon]
    rfl
  have e5 : D.form (TransferGap.vacProj D x) (TransferGap.vacProj D x)
      = latSFG (canonSched G) Φ.map k (pairFamG τ Q Q)
        - latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q) ^ 2 := by
    rw [form_vacProj, D.toPreForm.form_symm _ D.vac, e3, e4']
  rw [e1, e2, e3, e4, e5] at h
  rw [e4, e5] at hY
  exact ⟨h, hY⟩

end Lattice

/-! ## 2. The flowed clustering under `FixedWindowDecayG` -/

section Cluster

/-- **The flowed limit of `G` clusters at a physical rate under `FixedWindowDecayG`.** -/
theorem kernFG_cluster_of_fixedWindowDecayG (Φ : GFlow G)
    (hB : UniformBoundFG (canonSched G) Φ.map) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving (canonSched G) τ r) {L : ℝ} (hL : 0 < L)
    (hW : FixedWindowDecayG G τ 0 L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P Q : MarginMonoG G τ r) (m n : ℕ),
      (kernFG (canonSched G) Φ τ P.1 (monoShiftG (timeVecG (canonSched G) m τ n) Q.1)
          - kernFG (canonSched G) Φ τ P.1 (emptyMonoG G)
            * kernFG (canonSched G) Φ τ (emptyMonoG G) Q.1) ^ 2
        ≤ Real.exp (-(2 * (c / L)) * ((canonSched G).a m * n))
          * (kernFG (canonSched G) Φ τ P.1 P.1
            * (kernFG (canonSched G) Φ τ Q.1 Q.1 - kernFG (canonSched G) Φ τ (emptyMonoG G) Q.1 ^ 2))
      ∧ 0 ≤ kernFG (canonSched G) Φ τ P.1 P.1
            * (kernFG (canonSched G) Φ τ Q.1 Q.1
              - kernFG (canonSched G) Φ τ (emptyMonoG G) Q.1 ^ 2) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨c, hc, hev⟩ := gapAt_physical_of_fixedWindowDecayG G τ 0 hL hW
  have hevk : ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧ TransferGap.GapAt (DkG G τ k) r
      ∧ c / L ≤ -Real.log r / GaugeRunning.aRunG G (dyBetaG G k) :=
    (tendsto_dyBetaG G).eventually hev
  refine ⟨c, hc, fun P Q m n => ?_⟩
  have hmem : ∀ X : MarginMonoG G τ r, ∀ᶠ k in atTop, ∀ i : Fin X.1.1,
      smear (dySpacingG G k) (Φ.map k (X.1.2 i).1).1 (X.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
    intro X
    obtain ⟨d, hd, hrd, hX⟩ := X.2
    exact Filter.eventually_all.mpr
      (fun i => hpos (X.1.2 i).1 (X.1.2 i).2 d hd hrd (fun y hy => hX i y hy))
  have tl : ∀ X Y : MonoG G, Tendsto (fun k => latSFG (canonSched G) Φ.map k (pairFamG τ X Y))
      (ultra : Filter ℕ) (𝓝 (kernFG (canonSched G) Φ τ X Y)) :=
    fun X Y => tendsto_contSFG (canonSched G) Φ.map hB (pairFamG τ X Y)
  have hf := ((tl P.1 (monoShiftG (timeVecG (canonSched G) m τ n) Q.1)).sub
    ((tl P.1 (emptyMonoG G)).mul (tl (emptyMonoG G) Q.1))).pow 2
  have hY := (tl P.1 P.1).mul ((tl Q.1 Q.1).sub ((tl (emptyMonoG G) Q.1).pow 2))
  have hg := hY.const_mul (Real.exp (-(2 * (c / L)) * ((canonSched G).a m * n)))
  have hevLE : ∀ᶠ k in atTop,
      (latSFG (canonSched G) Φ.map k (pairFamG τ P.1 (monoShiftG (timeVecG (canonSched G) m τ n) Q.1))
        - latSFG (canonSched G) Φ.map k (pairFamG τ P.1 (emptyMonoG G))
          * latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q.1)) ^ 2
      ≤ Real.exp (-(2 * (c / L)) * ((canonSched G).a m * n))
        * (latSFG (canonSched G) Φ.map k (pairFamG τ P.1 P.1)
          * (latSFG (canonSched G) Φ.map k (pairFamG τ Q.1 Q.1)
            - latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q.1) ^ 2))
      ∧ 0 ≤ latSFG (canonSched G) Φ.map k (pairFamG τ P.1 P.1)
          * (latSFG (canonSched G) Φ.map k (pairFamG τ Q.1 Q.1)
            - latSFG (canonSched G) Φ.map k (pairFamG τ (emptyMonoG G) Q.1) ^ 2) := by
    filter_upwards [Filter.eventually_ge_atTop m, hevk, hmem P, hmem Q] with k hk hkr hkP hkQ
    obtain ⟨r', hr0, hg', hrate⟩ := hkr
    have ha := dySpacingG_pos G k
    have hvec : timeVecG (canonSched G) m τ n
        = site (dySpacingG G k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ)) := by
      show site (dySpacingG G m) (axisVec τ n) = _
      rw [ShiftInvG.site_dySpacingG G hk, scaleSite_axisVec]
      congr 2
    obtain ⟨hcl, hY0⟩ := lattice_clusterG Φ τ k hr0.le hg' P.1 Q.1
      (prodSmearG_mem Φ τ k _ hkP) (prodSmearG_mem Φ τ k _ hkQ) (2 ^ (k - m) * n)
    rw [← hvec] at hcl
    refine ⟨hcl.trans (mul_le_mul_of_nonneg_right ?_ hY0), hY0⟩
    have hlog : Real.log r' ≤ -(c / L) * dySpacingG G k := by
      have h1 := hrate
      rw [aRunG_dyBetaG, le_div_iff₀ ha] at h1
      linarith
    have hr_le : r' ≤ Real.exp (-(c / L) * dySpacingG G k) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.mpr hlog
    calc r' ^ (2 * (2 ^ (k - m) * n))
        ≤ Real.exp (-(c / L) * dySpacingG G k) ^ (2 * (2 ^ (k - m) * n)) :=
          pow_le_pow_left₀ hr0.le hr_le _
      _ = Real.exp (((2 * (2 ^ (k - m) * n) : ℕ) : ℝ) * (-(c / L) * dySpacingG G k)) :=
          (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(2 * (c / L)) * ((canonSched G).a m * n)) := by
          show _ = Real.exp (-(2 * (c / L)) * (dySpacingG G m * n))
          rw [← ShiftInvG.dySpacingG_mul_pow G hk]
          push_cast
          congr 1
          ring
  have hev1 := hevLE.mono (fun k hk => hk.1)
  have hev2 := hevLE.mono (fun k hk => hk.2)
  exact ⟨le_of_tendsto_of_tendsto hf hg (hev1.filter_mono ultra_le),
    ge_of_tendsto hY (hev2.filter_mono ultra_le)⟩

/-- **The absolute clustering of the flowed limit of `G`** under `FixedWindowDecayG`, with
`C = √(K P P (K Q Q − (K ∅ Q)²))`. -/
theorem flowClusterAbsG_of_fixedWindowDecayG (Φ : GFlow G)
    (hB : UniformBoundFG (canonSched G) Φ.map) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving (canonSched G) τ r) {L : ℝ} (hL : 0 < L)
    (hW : FixedWindowDecayG G τ 0 L) : FlowClusterAbsG (canonSched G) Φ τ r L := by
  obtain ⟨c, hc, hcl⟩ := kernFG_cluster_of_fixedWindowDecayG Φ hB τ hpos hL hW
  refine ⟨c, hc, fun m P Q => ⟨Real.sqrt (kernFG (canonSched G) Φ τ P.1 P.1
    * (kernFG (canonSched G) Φ τ Q.1 Q.1 - kernFG (canonSched G) Φ τ (emptyMonoG G) Q.1 ^ 2)),
    fun n => ?_⟩⟩
  have hE : (0 : ℝ) ≤ Real.exp (-(c / L) * ((canonSched G).a m * n)) := (Real.exp_pos _).le
  have hsq : Real.exp (-(c / L) * ((canonSched G).a m * n)) ^ 2
      = Real.exp (-(2 * (c / L)) * ((canonSched G).a m * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 := (hcl P Q m n).1
  rw [← hsq] at h1
  have h2 := ContinuumSep.abs_le_mul_sqrt_of_sq_le_sep hE h1
  linarith [h2, mul_comm (Real.exp (-(c / L) * ((canonSched G).a m * n)))
    (Real.sqrt (kernFG (canonSched G) Φ τ P.1 P.1
      * (kernFG (canonSched G) Φ τ Q.1 Q.1 - kernFG (canonSched G) Φ τ (emptyMonoG G) Q.1 ^ 2)))]

end Cluster

/-! ## 3. The gap from the run seed -/

section Gap

/-- **The flowed transfer of `G` is gapped at every step from the run seed of `G`.** -/
theorem gapAt_of_runSeedG (hrun : RunSeedG G) (Φ : GFlow G)
    (hB : UniformBoundFG (canonSched G) Φ.map) {r : ℝ} (hphys : Φ.PhysRange (canonSched G) r)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched Φ hB 0 hphys m0) ρ := by
  obtain ⟨L, hL, hW⟩ := fixedWindowDecayG_of_runSeedG G hrun
  have hpos := posPreserving_of_physRangeG (canonSched G) Φ hphys 0
  exact (flowClusterAbs_iff_gapAtG (canonSched G) schedOS_canonSched Φ hB 0 hpos m0 hL).mp
    (flowClusterAbsG_of_fixedWindowDecayG Φ hB 0 hpos hL hW)

/-- **The observer's gap input of `ClayGFinal.clayStatementAtG_GS_noNT` from the run seed of `G`**:
at the energy density `energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)` with the uniform
bound `ClayGFinal.preBG W hU`, some `0 < ρ₀ < 1` has `GapAt` of the transfer at step `0`. -/
theorem observerGapG_of_runSeedG (hrun : RunSeedG G) (W : ConfFlowG G) {t C₀ : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
        (ClayGFinal.preBG W hU) 0 hphys 0) ρ₀ :=
  gapAt_of_runSeedG hrun _ (ClayGFinal.preBG W hU) hphys 0

end Gap

end MassGap.FlowClusterG

#print axioms MassGap.FlowClusterG.lattice_clusterG
#print axioms MassGap.FlowClusterG.kernFG_cluster_of_fixedWindowDecayG
#print axioms MassGap.FlowClusterG.flowClusterAbsG_of_fixedWindowDecayG
#print axioms MassGap.FlowClusterG.gapAt_of_runSeedG
#print axioms MassGap.FlowClusterG.observerGapG_of_runSeedG
