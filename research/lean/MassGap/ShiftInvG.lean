import Mathlib
import MassGap.ClayWiringG

/-!
# MassGap.ShiftInvG — the shift invariance of the periodic Wilson state of a gauge group `G`

`ClayWiringG.SchedTransInv S` asks that, from step `j` on, translating every test function by
`site (S.a j) p` leave `latSG S k` unchanged. At `SU(N)` it is `schedTransInv_SU`, through
`PeriodicState.periodicState_shift`. This module proves it at `canonSched G` for every
`GaugeGroup G` with `GaugeSimple G`, by the same route with `SU N` replaced by `G`:

| step | `SU(N)` | here (any `G`) |
|---|---|---|
| shift as a link permutation | `WilsonTransfer.reflLink_comp_succ` | `shiftLinkPerm`, `shiftLinkPerm_apply` |
| action invariant under a reflection | `Reflect.reflect_action_invariant` | `reflect_action_invariantG` |
| action invariant under the shift | (inside `expect_shift_invariant`) | `shift_action_invariantG` |
| Gibbs expectation invariant under the shift | `WilsonTransfer.expect_shift_invariant` | `expect_shift_invariantG` |
| pullback intertwines the shifts | `PeriodicState.pullback_ishiftConf` | `pullback_ishiftConfG` |
| torus state shift invariant | `PeriodicState.torusState_shift` | `torusStateG_shift` |
| every limit of torus states shift invariant | `PeriodicState.shift_of_tendsto_torus` | `shift_of_tendsto_torusG` |
| infinite-volume state shift invariant | `PeriodicState.periodicState_shift` | `periodicStateG_shift` |
| dyadic sites | `ContinuumSchwinger.site_dySpacing` | `site_dySpacingG` |
| lattice translation invariance | `ContinuumSchwinger.latS_translate` | `latSG_translate` |
| `SchedTransInv` | `schedTransInv_SU` | `schedTransInv_canonSched` |

The measure half of the shift is a relabelling of links by a permutation, so it uses only that
`probHaar G` is a probability measure (`LatticeGauge.Symmetry.reindex_measurePreserving`); no
inversion of link variables enters. The action half is two reflections, each a conjugation of every
plaquette holonomy (`Reflect.hol_reflConf`, group-generic) that `wilsonDensityG_conj` discards.

`periodicStateG G β` is a `Classical.choose` of a limit of the torus states; no uniqueness of that
limit is used, since every limit of shift-invariant states is shift invariant
(`shift_of_tendsto_torusG`).

`clayStatementAtG_of_inputsG'` is `ClayWiringG.clayStatementAtG_of_inputsG` with the input
`SchedTransInv (canonSched G)` discharged by `schedTransInv_canonSched`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `0`, `1` the two reflection constants one apart; `2` the
halving of the dyadic spacing; `2k + 1` the extent index of the torus family.
-/

noncomputable section

namespace MassGap.ShiftInvG

open MeasureTheory MassGap.CompactGauge MassGap.GaugeGroup

/-! ## 1. The shift on the finite periodic lattice -/

section Finite

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n]

/-- **The one-step shift of links as a permutation**: the composite of the link reflections at the
constants `0` and `0 + 1`.

DERIVED: `0`, `1` the two reflection constants one apart. -/
def shiftLinkPerm (τ : Fin d) : Equiv.Perm (MassGap.WilsonHypercubic.Link d n) :=
  (MassGap.Reflect.reflLinkPerm τ (0 : Fin n)).trans (MassGap.Reflect.reflLinkPerm τ ((0 : Fin n) + 1))

/-- `shiftLinkPerm τ l = shiftLink τ l`. DERIVED: no numeral. -/
theorem shiftLinkPerm_apply (τ : Fin d) (l : MassGap.WilsonHypercubic.Link d n) :
    shiftLinkPerm τ l = MassGap.WilsonTransfer.shiftLink τ l :=
  MassGap.WilsonTransfer.reflLink_comp_succ τ 0 l

/-- **The Wilson action of `G` is invariant under every reflection**:
`action (reflConf τ c U) = action U`.

DERIVED: no numeral. -/
theorem reflect_action_invariantG (τ : Fin d) (c : Fin n)
    (U : MassGap.WilsonHypercubic.Link d n → G) :
    (GaugeWilson.sysWilsonG G d n).action (MassGap.Reflect.reflConf τ c U)
      = (GaugeWilson.sysWilsonG G d n).action U := by
  have hact : ∀ V : MassGap.WilsonHypercubic.Link d n → G,
      (GaugeWilson.sysWilsonG G d n).action V
        = ∑ q : MassGap.WilsonHypercubic.Plaq d n, wilsonDensityG G
            (MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := d) (n := n)) q V) :=
    fun _ => rfl
  rw [hact, hact]
  calc ∑ q : MassGap.WilsonHypercubic.Plaq d n, wilsonDensityG G
        (MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := d) (n := n)) q
          (MassGap.Reflect.reflConf τ c U))
      = ∑ q : MassGap.WilsonHypercubic.Plaq d n, wilsonDensityG G
          (MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := d) (n := n))
            (MassGap.Reflect.reflPlaqPerm τ c q) U) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        obtain ⟨g, hg⟩ := MassGap.Reflect.hol_reflConf τ c q U
        rw [MassGap.Reflect.reflPlaqPerm_apply, hg, wilsonDensityG_conj]
    _ = ∑ q : MassGap.WilsonHypercubic.Plaq d n, wilsonDensityG G
          (MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := d) (n := n)) q U) :=
        Equiv.sum_comp (MassGap.Reflect.reflPlaqPerm τ c)
          (fun q => wilsonDensityG G
            (MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := d) (n := n)) q U))

/-- **The Wilson action of `G` is invariant under the one-step shift.**

DERIVED: `0` the reflection constant. -/
theorem shift_action_invariantG (τ : Fin d) (U : MassGap.WilsonHypercubic.Link d n → G) :
    (GaugeWilson.sysWilsonG G d n).action (MassGap.WilsonTransfer.shiftConf τ U)
      = (GaugeWilson.sysWilsonG G d n).action U := by
  rw [MassGap.WilsonTransfer.shiftConf_eq_reflConf_comp τ (0 : Fin n) U,
    reflect_action_invariantG, reflect_action_invariantG]

/-- The relabelling by `shiftLinkPerm τ` is the shift of configurations. DERIVED: no numeral. -/
theorem reindex_shiftLinkPerm (τ : Fin d) (U : MassGap.WilsonHypercubic.Link d n → G) :
    MassGap.LatticeGauge.Symmetry.reindex (sys := GaugeWilson.sysWilsonG G d n) (shiftLinkPerm τ) U
      = MassGap.WilsonTransfer.shiftConf τ U := by
  funext l
  rw [MassGap.LatticeGauge.Symmetry.reindex_apply]
  exact congrArg U (shiftLinkPerm_apply τ l)

/-- **The Wilson Gibbs expectation of `G` is invariant under the one-step shift**:
`EWG G β (O ∘ shiftConf τ) = EWG G β O`, at every real `β` and every observable `O`.

DERIVED: no numeral. -/
theorem expect_shift_invariantG (τ : Fin d) (β : ℝ)
    (O : (MassGap.WilsonHypercubic.Link d n → G) → ℝ) :
    GaugeWilson.EWG G (d := d) (n := n) β (fun U => O (MassGap.WilsonTransfer.shiftConf τ U))
      = GaugeWilson.EWG G (d := d) (n := n) β O := by
  have h := MassGap.LatticeGauge.System.expect_invariant_of_mp (GaugeWilson.sysWilsonG G d n)
    (probHaar G) β O
    (MassGap.LatticeGauge.Symmetry.reindex (sys := GaugeWilson.sysWilsonG G d n) (shiftLinkPerm τ))
    (MassGap.LatticeGauge.Symmetry.reindex_measurePreserving (sys := GaugeWilson.sysWilsonG G d n)
      (probHaar G) (shiftLinkPerm τ))
    (fun U => by
      unfold MassGap.LatticeGauge.System.boltz
      rw [reindex_shiftLinkPerm, shift_action_invariantG])
  have e : (fun U => O (MassGap.LatticeGauge.Symmetry.reindex
        (sys := GaugeWilson.sysWilsonG G d n) (shiftLinkPerm τ) U))
      = fun U => O (MassGap.WilsonTransfer.shiftConf τ U) :=
    funext fun U => congrArg O (reindex_shiftLinkPerm τ U)
  rw [e] at h
  exact h

end Finite

/-! ## 2. The torus states and their limits -/

section Torus

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

omit [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
/-- `ishiftConf μ (pullback M W) = pullback M (shiftConf μ W)`, over any `G`.

DERIVED: `4` the dimension; `1` in `M + 1` the successor of `finMod`. -/
theorem pullback_ishiftConfG (M : ℕ) (μ : Fin 4)
    (W : MassGap.WilsonHypercubic.Link 4 (M + 1) → G) :
    MassGap.InfiniteShift.ishiftConf μ (MassGap.InfiniteLattice.pullback M W)
      = MassGap.InfiniteLattice.pullback M (MassGap.WilsonTransfer.shiftConf μ W) := by
  funext l
  show W (MassGap.InfiniteLattice.linkMod M (MassGap.InfiniteShift.ishiftLink μ l))
    = W (MassGap.WilsonTransfer.shiftLink μ (MassGap.InfiniteLattice.linkMod M l))
  rw [MassGap.PeriodicState.linkMod_ishiftLink]

/-- **Every torus state of `G` is shift invariant**:
`torusStateG G M β (ishiftObsL τ f) = torusStateG G M β f`.

DERIVED: `4` the dimension. -/
theorem torusStateG_shift (M : ℕ) (β : ℝ) (τ : Fin 4)
    (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    GaugeWilson.torusStateG G M β (MassGap.ReflectionShift.ishiftObsL τ f)
      = GaugeWilson.torusStateG G M β f := by
  show GaugeWilson.EWG G (d := 4) (n := M + 1) β
      (GaugeWilson.torusObsG G M (MassGap.ReflectionShift.ishiftObsL τ f))
    = GaugeWilson.EWG G (d := 4) (n := M + 1) β (GaugeWilson.torusObsG G M f)
  have h : GaugeWilson.torusObsG G M (MassGap.ReflectionShift.ishiftObsL τ f)
      = fun W => GaugeWilson.torusObsG G M f (MassGap.WilsonTransfer.shiftConf τ W) := by
    funext W
    show f (MassGap.InfiniteShift.ishiftConf τ (MassGap.InfiniteLattice.pullback M W))
      = f (MassGap.InfiniteLattice.pullback M (MassGap.WilsonTransfer.shiftConf τ W))
    rw [pullback_ishiftConfG]
  rw [h]
  exact expect_shift_invariantG τ β _

/-- **Every limit of the torus states of `G` along a non-trivial filter is shift invariant.**

DERIVED: `2k + 1` the extent index; `4` the dimension. -/
theorem shift_of_tendsto_torusG (β : ℝ) (τ : Fin 4)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G)) {l : Filter ℕ} [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      Filter.Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f) l (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f := by
  intro f
  refine tendsto_nhds_unique (htend (MassGap.ReflectionShift.ishiftObsL τ f)) ?_
  exact (htend f).congr (fun k => (torusStateG_shift G (2 * k + 1) β τ f).symm)

/-- **What `periodicStateG` is**: along the ultrafilter chosen with it,
`torusStateG G (2k + 1) β f → periodicStateG G β f` at every continuous `f`.

DERIVED: `2k + 1` the extent index. -/
theorem tendsto_periodicStateG (β : ℝ) (f : C(MassGap.GibbsSpec.IConf G, ℝ)) :
    Filter.Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f)
      (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) : Filter ℕ)
      (nhds (GaugeWilson.periodicStateG G β f)) :=
  (GaugeWilson.exists_periodic_limit_dvdG G β).choose_spec.choose_spec.2 f

/-- **`periodicStateG G β` is invariant under the unit shift along every direction**, at every real
`β`: the mirror of `PeriodicState.periodicState_shift`.

DERIVED: `4` the dimension. -/
theorem periodicStateG_shift (β : ℝ) (τ : Fin 4) :
    ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      GaugeWilson.periodicStateG G β (MassGap.ReflectionShift.ishiftObsL τ f)
        = GaugeWilson.periodicStateG G β f := by
  haveI : (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) :
      Filter ℕ).NeBot := (GaugeWilson.exists_periodic_limit_dvdG G β).choose.neBot'
  exact shift_of_tendsto_torusG G β τ (GaugeWilson.periodicStateG G β) (tendsto_periodicStateG G β)

end Torus

/-! ## 3. Dyadic translation invariance of the canonical schedule -/

section Sched

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ClayTreeG
  MassGap.ClayWiringG

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- `dySpacingG G k · 2^(k−m) = dySpacingG G m` for `m ≤ k`.

DERIVED: `2` the halving; `1` the first halving. -/
theorem dySpacingG_mul_pow [GaugeSimple G] {m k : ℕ} (hmk : m ≤ k) :
    dySpacingG G k * 2 ^ (k - m) = dySpacingG G m := by
  unfold dySpacingG
  have h : (2 : ℝ) ^ (k + 1) = 2 ^ (k - m) * 2 ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h, div_mul_eq_mul_div, mul_comm (GaugeRunning.aRunG G 1),
    mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]

/-- **A dyadic site of step `m` is a lattice site of every finer step `k`**:
`site (dySpacingG G m) n = site (dySpacingG G k) (2^(k−m) n)`.

DERIVED: `2` the halving. -/
theorem site_dySpacingG [GaugeSimple G] {m k : ℕ} (hmk : m ≤ k) (n : ISite) :
    site (dySpacingG G m) n = site (dySpacingG G k) (scaleSite (2 ^ (k - m)) n) := by
  funext i
  simp only [site, scaleSite]
  push_cast
  rw [← dySpacingG_mul_pow G hmk]
  ring

variable {G}

/-- **Lattice translation invariance over a schedule**: if the state of step `k` is invariant under
the four unit shifts, translating every test function by `site (S.a k) n` leaves `latSG S k`
unchanged.

DERIVED: `4` the dimension. -/
theorem latSG_translate (S : Sched G) (k : ℕ)
    (hsh : ∀ (τ : Fin 4) (F : C(IConf G, ℝ)), S.ν k (MassGap.ReflectionShift.ishiftObsL τ F) = S.ν k F)
    {ι : Type} [Fintype ι] (F : ι → SFieldG G) (n : ISite) :
    latSG S k (fun i => ((F i).1, (F i).2.translate (site (S.a k) n))) = latSG S k F := by
  show S.ν k (∏ i, smear (S.a k) (F i).1.1 ((F i).2.translate (site (S.a k) n)))
    = S.ν k (∏ i, smear (S.a k) (F i).1.1 (F i).2)
  have h : (∏ i, smear (S.a k) (F i).1.1 ((F i).2.translate (site (S.a k) n)))
      = transObs n (∏ i, smear (S.a k) (F i).1.1 (F i).2) := by
    rw [transObs_prod]
    exact Finset.prod_congr rfl (fun i _ => smear_translate (S.a_pos k) _ _ n)
  rw [h, state_transObs hsh]

/-- **The canonical schedule of `G` is dyadically translation invariant**: `SchedTransInv
(canonSched G)`, from the shift invariance of `periodicStateG` (`periodicStateG_shift`).

DERIVED: no numeral. -/
theorem schedTransInv_canonSched [GaugeSimple G] : SchedTransInv (canonSched G) := by
  intro ι _ F j k hk p
  have hs : site ((canonSched G).a j) p
      = site ((canonSched G).a k) (scaleSite (2 ^ (k - j)) p) := site_dySpacingG G hk p
  rw [hs]
  exact latSG_translate (canonSched G) k
    (fun τ f => periodicStateG_shift G (dyBetaG G k) τ f) F _

end Sched

/-! ## 4. The capstone with `SchedTransInv` discharged -/

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

/-- **`ClayStatementAtG G W D` with the wiring and `SchedTransInv (canonSched G)` discharged**:
`ClayWiringG.clayStatementAtG_of_inputsG` with `hI := schedTransInv_canonSched`; every other
hypothesis is the same.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_inputsG' (W : ConfFlowG G) (D : Set (LField G))
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
    (hUB : UniformBoundFG (canonSched G) (energyMapG (canonSched G) W D))
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
  clayStatementAtG_of_inputsG W D X hSM hsa hXO op m Z hBC hRie b0 κ htr hop hZtie h0
    schedTransInv_canonSched hTC hCov Gk hK hAF hNG hND hUB hCut w hL hnt C wC hCT hWard hCD hCO
    hLC hTI hGen

end Capstone

end MassGap.ShiftInvG

end

#print axioms MassGap.ShiftInvG.shiftLinkPerm_apply
#print axioms MassGap.ShiftInvG.reflect_action_invariantG
#print axioms MassGap.ShiftInvG.shift_action_invariantG
#print axioms MassGap.ShiftInvG.expect_shift_invariantG
#print axioms MassGap.ShiftInvG.pullback_ishiftConfG
#print axioms MassGap.ShiftInvG.torusStateG_shift
#print axioms MassGap.ShiftInvG.shift_of_tendsto_torusG
#print axioms MassGap.ShiftInvG.tendsto_periodicStateG
#print axioms MassGap.ShiftInvG.periodicStateG_shift
#print axioms MassGap.ShiftInvG.site_dySpacingG
#print axioms MassGap.ShiftInvG.latSG_translate
#print axioms MassGap.ShiftInvG.schedTransInv_canonSched
#print axioms MassGap.ShiftInvG.clayStatementAtG_of_inputsG'
