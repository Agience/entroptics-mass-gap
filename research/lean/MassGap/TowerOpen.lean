import Mathlib
import MassGap.LinkAlongG

/-!
# MassGap.TowerOpen — the open statement along a coupling tower, with the link and the moments reduced

`ConsolidatedRoot.OpenAlong N βs` asks, along a coupling tower `βs` of `SU(N)`, for the class moments
`hU`, the two-point kernel with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity,
`CompOSG` of the composites, and the composites' link `wC` with `hLC` and the cross reading `hX`. This
module replaces two of them along every tower with `SiteExpG` and `ApproxAlong`:

* `wC`, `hLC`, `hX` from `ApproxK` of the three kernels along `βs` (`LinkAlongG.ApproxAlong`), `ConvCG`
  (the first field of `CompOSG`) and the class moments (`LinkAlongG.linkAlong`);
* `hU` from one exponential moment of the flowed reading at one site, in physical units, along `βs`
  (`SiteExpG`): `classMomentsG_of_siteExpG`, the schedule form of
  `ClaySUFinal.classMoments_of_siteExp` (`FlowUV.classUnitExp_of_siteExp`,
  `ObserverMoments.classMoments_of_classUnitExp`) at any shift-invariant schedule. `SiteExpG` is a
  sufficient condition for `hU`, stronger than it and stated on one local observable.

`OpenAlongR N βs` is `OpenAlong` with those clauses replaced by `SiteExpG` and `ApproxAlong`;
`openAlong_of_reduced` gives `OpenAlong` from it, and `clayStatementOf_of_reduced` gives
`ClayStatementOf (SU N)` from `StrongEnd N`, (UV) and `OpenAlongR` along the towers near `0⁺`.
Declarations are in the namespace `MassGap.TowerOpen`.

DERIVED (module-wide): `0` the lower ends of `t`, `s` and `R`, the signs and the limit `0⁺`; `1` the
unit cube and the spacing bound; `2`, `3`, `4` the site count `(2 · 1 + 3)⁴`; `4` the canonical
dimension; `2` the least rank; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a sufficient bound
on `c`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TowerOpen

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ObserverEnergyBox MassGap.FlowUV MassGap.EnergyBoundG MassGap.ObserverOSG
  MassGap.ObserverLinkedG MassGap.ClayTreeG MassGap.ClayStatementG Filter
open scoped Topology

/-! ## 1. The class moments from one site, at any shift-invariant schedule -/

section Moments

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The cube's exponential moment from one site's**, in a translation-invariant state over `G`:
for `F ≥ 0`, `t ≥ 0`, `0 < a ≤ 1`, `R ≥ 0`, `ν(e^{t · cubeSumG a R F}) ≤ ν(e^{t (2R + 3)⁴ / a⁴ · F})`.
`FlowUV.state_exp_cubeSum_le` over `G`. DERIVED: `2`, `3`, `4` are `sum_cubeInd_le`'s; `0`, `1` the
signs and the spacing bound. -/
theorem state_exp_cubeSumG_le (ν : MassGap.DLRLimit.State (IConf G))
    (htr : ∀ (x : ISite) (F : C(IConf G, ℝ)), ν (transObs x F) = ν F)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {R : ℝ} (hR : 0 ≤ R) (F : C(IConf G, ℝ))
    (hF : ∀ U, 0 ≤ F U) {t : ℝ} (ht : 0 ≤ t) :
    ν (expC (t • cubeSumG a R F)) ≤ ν (expC ((t * ((2 * R + 3) ^ 4 / a ^ 4)) • F)) := by
  set L : ℝ := (2 * R + 3) ^ 4 / a ^ 4 with hL
  set M : ℝ := ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) with hMdef
  have hM1 : 1 ≤ M := one_le_sum_cubeInd hR
  have hM : 0 < M := by linarith
  have hML : M ≤ L := sum_cubeInd_le ha ha1 hR
  set H : C(IConf G, ℝ) := ∑ x ∈ box ⌈R / a⌉₊,
    (cubeInd R (site a x) / M) • transObs x (expC ((t * L) • F)) with hH
  have hpt : ∀ U, expC (t • cubeSumG a R F) U ≤ H U := by
    intro U
    have hHU : H U = ∑ x ∈ box ⌈R / a⌉₊,
        (cubeInd R (site a x) / M) * Real.exp (t * L * F (transConf x U)) := by
      rw [hH]
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
        expC_apply, smul_eq_mul, mul_assoc]
    rw [hHU, expC_apply, ContinuousMap.smul_apply, smul_eq_mul, cubeSumG_apply]
    refine (exp_mul_wsum_le _ (fun x => cubeInd R (site a x)) (fun x => F (transConf x U))
      (fun x _ => cubeInd_nonneg _ _) hM rfl t).trans ?_
    refine Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left ?_
      (div_nonneg (cubeInd_nonneg _ _) hM.le))
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hML ht) (hF _))
  have hνH : ν H = ν (expC ((t * L) • F)) := by
    rw [hH, ν.map_sum]
    simp only [ν.map_smul, htr]
    rw [← Finset.sum_mul, ← Finset.sum_div, ← hMdef, div_self hM.ne', one_mul]
  calc ν (expC (t • cubeSumG a R F)) ≤ ν H := ν.mono hpt
    _ = ν (expC ((t * L) • F)) := hνH

/-- **One exponential moment of the flowed reading at one site, in physical units, over a schedule**:
eventually in the step, `ν_k(exp((s / a_k⁴) · O ∘ V_k)) ≤ C` for every field of `D`. `FlowUV.SiteExp`
with `stateK`, `dySpacing` replaced by `S.ν`, `S.a`. DERIVED: `4` the canonical dimension. -/
def SiteExpG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (s C : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D, S.ν k (expC ((s / S.a k ^ 4) • (W.fieldMap k O).1)) ≤ C

/-- **`ClassMomentsG` from `SiteExpG`** on a non-negative class of a shift-invariant schedule:
`SiteExpG` at `(2·1 + 3)⁴ t` gives `ClassMomentsG` at `t` with the constant `|C|`
(`state_exp_cubeSumG_le` at `R = 1`, `ObserverOSG.state_cubeSumG_pow_le`,
`ObserverEnergyBox.state_pow_le_exp`). DERIVED: `0` the signs; `(2·1 + 3)⁴` the site-count bound of
`sum_cubeInd_le` at the unit cube `R = 1`, the choice absorbed by the existential `s`. -/
theorem classMomentsG_of_siteExpG (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t)
    (h : SiteExpG S W D (t * (2 * 1 + 3) ^ 4) C) : ClassMomentsG S W D t |C| := by
  intro O hO
  filter_upwards [h, S.a_lim.eventually (gt_mem_nhds one_pos)] with k hk hk1
  intro R hR p
  have ha := S.a_pos k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hT := state_transObs (hsh k)
  have hunit : S.ν k (expC (t • cubeSumG (S.a k) 1 (W.fieldMap k O).1)) ≤ C := by
    have hb := state_exp_cubeSumG_le (S.ν k) hT ha hk1.le zero_le_one _ hF ht.le
    have e : t * ((2 * 1 + 3) ^ 4 / S.a k ^ 4) = t * (2 * 1 + 3) ^ 4 / S.a k ^ 4 :=
      (mul_div_assoc _ _ _).symm
    rw [e] at hb
    exact hb.trans (hk O hO)
  refine (state_cubeSumG_pow_le (S.ν k) hT ha hR _ hF p).trans
    (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (pow_nonneg (by linarith) 4) _))
  exact (state_pow_le_exp (S.ν k) _ (cubeSumG_nonneg _ _ hF) ht (2 * p)).trans
    (mul_le_mul_of_nonneg_left (hunit.trans (le_abs_self C))
      (div_nonneg (by positivity) (pow_pos ht _).le))

end Moments

/-! ## 2. The open statement along a tower and the capstone -/

section Along

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedShiftInv_alongG)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.ConsolidatedRoot (obsW rhoZ csZ OpenAlong)
open MassGap.LinkAlongG (ApproxAlong linkAlong)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The clauses along `βs` that remain open**, at the witnesses of `ConsolidatedRoot`: some
block-step observer `obsW N hc0 hc s₀` with range `r > s₀`, one exponential moment `s > 0` of its
flowed reading at one site (`SiteExpG`), channel factors `zri`, `zwe` nowhere zero, an off-tensor mixing
`μ`, a two-point kernel with its asymptotic-freedom coefficient, non-Gaussianity, the Ward identity,
`CompOSG` of the composites, and `ApproxK` of the three kernels (`ApproxAlong`). `ApproxAlong`
carries the link's content in kernel form: each composite's vector is a limit of the observer's flowed
vectors in the joint form (the converse, that vectors in the observer's space give `ApproxK`, is
argued in the module note of `CompositeLink`).

DERIVED: `0` the signs; `2` the least rank; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a
sufficient bound on `c`. -/
def OpenAlongR (βs : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (s C₀ : ℝ) (_ : 0 < s)
    (_ : SiteExpG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) s C₀)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : CompositesRen.OffMix)
    (_ : ∃ Gk : ℝ → ℝ, TwoPointKernelG (schedAlongG _ βs) (rhoZ N zri zwe) Gk
      ∧ AFCoefficientG (constsG (MassGap.SUN.SU N)) Gk)
    (_ : NonGaussianTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : WardTG (schedAlongG _ βs) (rhoZ N zri zwe))
    (_ : CompOSG (schedAlongG _ βs) (csZ N zri zwe μ)),
    ApproxAlong N βs hc0 hc s₀ r zri zwe μ

/-- **`OpenAlongR ⇒ OpenAlong`**: the class moments from `SiteExpG` at `t = s / (2·1 + 3)⁴`
(`classMomentsG_of_siteExpG`, `MeasuredSpacing.schedShiftInv_alongG`), and the link from
`ApproxAlong` (`LinkAlongG.linkAlong`). DERIVED: `2` the least rank. -/
theorem openAlong_of_reduced {βs : ℕ → ℝ} (h : OpenAlongR N βs) : OpenAlong N βs := by
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, s, C₀, hs, hSE, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, hA⟩ :=
    h
  have h625 : (0 : ℝ) < (2 * 1 + 3) ^ 4 := by norm_num
  have ht : 0 < s / (2 * 1 + 3) ^ 4 := div_pos hs h625
  have hSE' : SiteExpG (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))
      (s / (2 * 1 + 3) ^ 4 * (2 * 1 + 3) ^ 4) C₀ := by
    rw [div_mul_cancel₀ s h625.ne']
    exact hSE
  have hU := classMomentsG_of_siteExpG (schedAlongG _ βs) (schedShiftInv_alongG _ βs)
    (obsW N hc0 hc s₀) (SymPlaqG.symPlaqG_nonneg (G := MassGap.SUN.SU N)) ht hSE'
  obtain ⟨wC, hLC, hX⟩ := linkAlong βs hc0 hc hs0 hr hU zri zwe μ hCO.1 hA
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, _, _, ht, hU, zri, zwe, hri, hwe, μ, hK, hNG, hWard, hCO, wC,
    hLC, hX⟩

/-- **The root at `SU(N)` from the strong end, (UV) and `OpenAlongR` along the towers near `0⁺`**
(`ConsolidatedRoot.clayStatementOf_of_open`, `openAlong_of_reduced`). DERIVED: `2` the least rank; `0`
the limit `0⁺`. -/
theorem clayStatementOf_of_reduced (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ∃ μ : ℝ, UVConverges N βs id μ)
    (hO : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → OpenAlongR N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  ConsolidatedRoot.clayStatementOf_of_open hS hUV
    (hO.mono fun _ h βs hT => openAlong_of_reduced (h βs hT))

end Along

end MassGap.TowerOpen

end

#print axioms MassGap.TowerOpen.state_exp_cubeSumG_le
#print axioms MassGap.TowerOpen.classMomentsG_of_siteExpG
#print axioms MassGap.TowerOpen.openAlong_of_reduced
#print axioms MassGap.TowerOpen.clayStatementOf_of_reduced
