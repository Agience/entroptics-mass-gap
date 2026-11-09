import Mathlib
import MassGap.ObserverBlock
import MassGap.PeriodicStateDLR

/-!
# MassGap.BulkBound — the observer's moment condition forces the flowed origin plaquette flat; it fails at `blFam`

`ObserverMultigrid.MW W` asks one rate `t > 0` and one constant `C` with, eventually in the step `k`, for
every index `j : MIx` (every admissible monomial and every plaquette),
`ν_k(exp(t a_k^{−d_j} |O_j ∘ V_k|)) ≤ C`. The index set is infinite and the dimensions `d_j` are unbounded.
This module shows that one `C` over that whole family forces a deterministic bound on every flowed
configuration, and that the ray-averaged observer `ObserverBlock.blFam` violates it. Declarations are in the
namespace `MassGap.BulkBound`.

## 1. A channel tower

`p1 = ([F₀₁], Im)` is the factor `Im((−i) tr(U_p − 1)) = N − Re tr U_p` (`facV_p1`), `U_p` the plaquette
holonomy in the `(0, 1)` plane at the origin. `mono n` is `2(n + 1)` copies of `p1`: an
admissible monomial (`admM_mono`) of dimension `cdim = 4(n + 1)` (`cdim_mono`) and even reflection count
(`ctau_mono`), with lattice value `(N − Re tr U_p)^{2(n+1)}` (`monoV_mono`). Its averaged bare field `bR N (jn n)`
is at least `½ (N − Re tr U_p)^{2(n+1)}` (`chan_ge`): the reflected half is an even power.

## 2. The Wilson state charges every open set (proved)

`periodicState_pos_of_local`: at `β ≥ 0`, a continuous `F ≥ 0`, local on a finite set `S` of links, with
`F(P) > 0` at some configuration has `periodicState hN β F > 0`. The DLR kernel on `S` has weight
`e^{−β · action} ≥ e^{−2β |∂S|}` and partition function at most `1`, so it is at least
`e^{−2β |∂S|}` times the Haar integral of `u ↦ F(splice u P)` (locality makes the boundary condition
irrelevant); that integral is
positive because the product Haar measure charges the open set `{F > 0}`, which contains the restriction of
`P`. `PeriodicStateDLR.periodicState_ge_of_kernel_ge` passes the bound to the state. `stateK_pos_of_local` is
the step-`k` case.

## 3. The reduction (proved)

`facV_le_of_scaleAt_one`: if `ScaleAt Wf t C γ γP k 1` with `t > 0` (any `γ`, `γP`: at `s = 1` the
log factor is `1`), then for every configuration `U`,

  `N − Re tr (V_k U)_p ≤ a_k²`,  `V_k = (Wf 1).V k`.

Proof: if some `U` has `x = N − Re tr (V_k U)_p > a_k²`, take `a_k² < ρ < x` and the continuous local cut-off
`G = min(1, max(0, x(·) − ρ))`, positive at `U`, so `ν_k(G) > 0` (§2). On `{G > 0}` the channel `jn n`
exceeds `½ ρ^{2(n+1)}`, so `exp(L_n) ν_k(G) ≤ C` with `L_n = (t/2)(ρ²/a_k⁴)^{n+1}`, which is unbounded in `n`.

* `facV_le_of_MW`: `MW W → ∀ᶠ k, ∀ U, N − Re tr (W.V k U)_p ≤ a_k²`.
* `facV_le_of_scaleControlAll`: the same for `Wf 1` from `ScaleControlAll b Wf` at any `b ≥ 1`.

So `MW W` holds only at an observer whose every output is flat to within `a_k²` at the origin plaquette,
for all inputs, not on average. No statement about the Wilson measure beyond §2 enters.

## 4. The no-go at the ray-averaged observer (proved)

`fpi y = e^{iπy}` is the staggered slice: on `zeta fpi`, every staple of a direction-`1` link is the link
times a real sign, so the averaged block step returns the link (`Fz_fpi`, `blStep_fpi`); the `π`-flux
configuration `dgConf (zeta fpi)` is a fixed point of every `blMap` (`blMap_fpi`) and of every member of
`blFam` (`blFam_V_fpi`). Its origin plaquette is `diag(−1, −1, 1, …, 1)`, with `N − Re tr = 4`
(`facV_fpi`). Since `a_k → 0`:

* `not_MW_blFam`: `¬ MW (blFam hN c hc0 hc m s)` at every `N ≥ 2`, `c`, `m`, `s` (including `c > 0`,
  `m ≥ 1`, `s > 0`).
* `not_exists_scaleControlAll_blFam`: no family `Wf` with `Wf 1 = blFam …` meets `ScaleControlAll 1`
  (`ObserverBlock.blFam_mw_iff`).
* `not_scaleControlAll_of_one_le`: no `Wf` with `Wf 1 = blFam …` meets `ScaleControlAll b` at any `b ≥ 1`.

## 5. What the no-go leaves open

`ScaleControlAll b Wf` at `b < 1` is not touched. It reads `Wf s` only at `s ≤ b < 1`, never `Wf 1`; the
capstone's `top` field puts the observer at `Wf b`, and there the factor `(1 + |log s|)^{γ_j}` is free per
monomial and can absorb the growth of the tower `jn n` at each fixed step (not, for a fixed monomial, the
growth in `k`). The reduction of the capstone's scale input to `MW` holds at `b = 1` only
(`ScaleSatisfiable.scaleControlAll_one_iff`), and there `γ` is invisible. Read as a consequence of §3 (not a
further theorem): with one `C` over the infinite family `MIx` and no channel-dependent factor, the moment
condition is a sup bound on the flowed origin plaquette over all inputs.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0`, `1` the plane of the plaquette and the origin; `2` the least rank, the halving of
the reflection average, the even power and the squared spacing; `4` the trace defect of
`diag(−1, −1, 1, …)` and the dimension of a pair of `p1` factors; `π` the staggered phase; `6` the staple
directions and sides; `12` the coupling bound of `blFam`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.BulkBound

open MassGap.SUN (SU)
open MassGap.InfiniteLattice MassGap.ContinuumFlow MassGap.ContinuumSchwinger MassGap.MultiScaleAll
  MassGap.ClayStatement MassGap.ClassicalLimit MassGap.CompositesBuild MassGap.ObserverEnergyBox
  MassGap.ObserverMultigrid MassGap.ObserverBlock
open Filter MeasureTheory
open scoped Topology

/-! ## 1. The channel tower -/

section Tower

variable {N : ℕ}

/-- The factor `Im((−i) tr(U_p − 1))` of the plaquette in the `(0, 1)` plane.
DERIVED: `0`, `1` the plane. -/
def p1 : Word × Bool := ([([], 0, 1)], false)

/-- **The factor `p1` is `N − Re tr U_p`.** DERIVED: `0`, `1` the plane and the origin. -/
theorem facV_p1 (U : Cfg N) :
    facV U p1 = N - (Matrix.trace ((plaqG U 0 1 0 : SU N) : Mat N)).re := by
  simp only [facV, p1, Bool.false_eq_true, if_false, List.length_singleton, pow_one, latW,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, latD, Matrix.trace_sub,
    Matrix.trace_one, Fintype.card_fin, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.natCast_re,
    Complex.natCast_im]
  ring

/-- The tower monomial: `2(n + 1)` copies of `p1`. DERIVED: `2` the even power; `1` the shift. -/
def mono (n : ℕ) : CMono := List.replicate (2 * (n + 1)) p1

/-- DERIVED: `2`, `1` as in `mono`. -/
theorem admM_mono (n : ℕ) : AdmM (mono n) := by
  refine ⟨?_, fun p hp => ?_⟩
  · simp [mono]
  · rw [mono, List.mem_replicate] at hp
    rw [hp.2]
    simp [p1]

/-- The tower index. DERIVED: no numeral. -/
def jn (n : ℕ) : Ix0 := ⟨mono n, admM_mono n⟩

/-- DERIVED: `4 = 2 · 2` (two copies of dimension `2` per even pair). -/
theorem cdim_mono (n : ℕ) : cdim (mono n) = 4 * (n + 1) := by
  simp only [cdim, mono, p1, List.map_replicate, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, letDim, List.length_nil, List.sum_replicate, smul_eq_mul]
  ring

/-- DERIVED: `0` the reflected direction; `2` the even power. -/
theorem ctau_mono (n : ℕ) : ctau 0 (mono n) = 2 * (n + 1) := by
  simp [ctau, mono, p1, List.map_replicate, List.sum_replicate]

/-- DERIVED: `2` the even power. -/
theorem monoV_mono (n : ℕ) (U : Cfg N) : monoV (mono n) U = facV U p1 ^ (2 * (n + 1)) := by
  simp [monoV, mono, List.map_replicate, List.prod_replicate]

/-- **The tower channel dominates half the even power of `p1`.**
DERIVED: `1/2` the reflection average; `2` the even power. -/
theorem chan_ge (n : ℕ) (V : Cfg N) :
    (1 / 2 : ℝ) * facV V p1 ^ (2 * (n + 1)) ≤ (MassGap.ReflAvg.bR N (jn n)).1 V := by
  show _ ≤ (MassGap.ReflAvg.reflAvg (ctau 0 (mono n)) (bareF (mono n))).1 V
  rw [MassGap.ReflAvg.reflAvg_apply, MassGap.ReflAvg.refl_apply, bareF_apply, bareF_apply,
    monoV_mono, monoV_mono, ctau_mono]
  have h1 : ((-1 : ℝ)) ^ (2 * (n + 1)) = 1 := by rw [pow_mul]; norm_num
  have h2 : 0 ≤ facV (LatticeReflection.ireflConf 0 0 V) p1 ^ (2 * (n + 1)) :=
    (even_two_mul _).pow_nonneg _
  rw [h1]
  nlinarith

end Tower

/-! ## 2. The Wilson state charges every open set -/

section Positive

open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.WilsonAction
open MassGap.CompactGauge (probHaar)

variable {N : ℕ}

/-- DERIVED: no numeral. -/
theorem continuous_splice_left (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (SU N)) :
    Continuous (fun u : VConf (SU N) Λ => splice Λ u ω) := by
  refine continuous_pi (fun l => ?_)
  by_cases h : l ∈ Λ
  · simp only [splice, dif_pos h]
    exact continuous_apply _
  · simp only [splice, dif_neg h]
    exact continuous_const

/-- **The periodic Wilson state is positive on a non-negative local field that is positive somewhere.**
DERIVED: `0` the signs and `β ≥ 0`; `2` the range of the density; `1` the weight bound. -/
theorem periodicState_pos_of_local (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (F : C(MassGap.GibbsSpec.IConf (SU N), ℝ)) (S : Finset MassGap.InfiniteLattice.ILink)
    (hS : ∀ U V : MassGap.GibbsSpec.IConf (SU N), (∀ l ∈ S, U l = V l) → F U = F V)
    (hF0 : ∀ U, 0 ≤ F U) {P : MassGap.GibbsSpec.IConf (SU N)} (hP : 0 < F P) :
    0 < MassGap.PeriodicState.periodicState hN β F := by
  classical
  set μ : Measure (SU N) := probHaar (SU N) with hμ
  set c0 : ℝ := Real.exp (-(β * (((boundaryPlaqs S).card : ℝ) * 2))) with hc0
  let g : VConf (SU N) S → ℝ := fun u => F (splice S u P)
  have hgc : Continuous g := F.continuous.comp (continuous_splice_left S P)
  have hg0 : ∀ u, 0 ≤ g u := fun u => hF0 _
  have hFb : ∀ U, |F U| ≤ ‖F‖ := fun U => by
    rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm U
  have hgint : Integrable g (vol μ S) := integrable_of_bounded _ hgc.measurable (fun u => hFb _)
  -- the Haar integral of `g` is positive
  have hI : 0 < ∫ u, g u ∂(vol μ S) := by
    haveI : (vol μ S).IsOpenPosMeasure :=
      inferInstanceAs ((Measure.pi fun _ : ↥S => μ).IsOpenPosMeasure)
    rw [integral_pos_iff_support_of_nonneg hg0 hgint]
    let u0 : VConf (SU N) S := fun l => P l.1
    have hu0 : splice S u0 P = P := by
      funext l
      by_cases h : l ∈ S
      · rw [splice_mem h]
      · rw [splice_not_mem h]
    have hopen : IsOpen {u : VConf (SU N) S | 0 < g u} := isOpen_lt continuous_const hgc
    have hne : ({u : VConf (SU N) S | 0 < g u}).Nonempty := ⟨u0, by
      show 0 < F (splice S u0 P); rw [hu0]; exact hP⟩
    exact lt_of_lt_of_le (hopen.measure_pos _ hne)
      (measure_mono fun u hu => Function.mem_support.mpr (ne_of_gt hu))
  have hc0pos : 0 < c0 := Real.exp_pos _
  refine lt_of_lt_of_le (mul_pos hc0pos hI)
    (periodicState_ge_of_kernel_ge hN β S F (c := c0 * ∫ u, g u ∂(vol μ S)) (fun ω => ?_))
  rw [wspec_apply]
  -- the kernel at `ω`
  have hloc : ∀ u, F (splice S u ω) = g u := fun u =>
    hS _ _ (fun l hl => by rw [splice_mem hl, splice_mem hl])
  have hwlo : ∀ u, c0 ≤ wt wilsonDensity β S u ω := fun u => by
    unfold wt
    rw [hc0, Real.exp_le_exp]
    have := actionOn_le (wilsonDensity_le_two hN) (boundaryPlaqs S) (splice S u ω)
    nlinarith
  have hwhi : ∀ u, wt wilsonDensity β S u ω ≤ 1 := fun u =>
    exp_neg_actionOn_le_one (wilsonDensity_nonneg hN) hβ _ _
  have hwint : Integrable (fun u => wt wilsonDensity β S u ω) (vol μ S) :=
    integrable_wt measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β S μ ω
  have hpart := part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN)
    β S μ ω
  have hpart1 : part wilsonDensity β S μ ω ≤ 1 := by
    unfold part
    calc ∫ u, wt wilsonDensity β S u ω ∂(vol μ S) ≤ ∫ _u, (1 : ℝ) ∂(vol μ S) :=
          integral_mono hwint (integrable_const 1) hwhi
      _ = 1 := by simp
  have hnum : c0 * ∫ u, g u ∂(vol μ S) ≤ num wilsonDensity β S μ (⇑F) ω := by
    unfold num
    have hfun : (fun u => F (splice S u ω) * wt wilsonDensity β S u ω)
        = fun u => g u * wt wilsonDensity β S u ω := funext fun u => by rw [hloc u]
    rw [hfun, ← integral_const_mul]
    have hint2 : Integrable (fun u => g u * wt wilsonDensity β S u ω) (vol μ S) :=
      integrable_of_bounded _ (hgc.measurable.mul (measurable_wt_left measurable_wilsonDensity β S ω))
        (fun u => by
          rw [abs_mul, abs_of_pos (wt_pos _ _ _ _ _)]
          calc |g u| * wt wilsonDensity β S u ω ≤ ‖F‖ * 1 :=
                mul_le_mul (hFb _) (hwhi u) (wt_pos _ _ _ _ _).le (norm_nonneg _)
            _ = ‖F‖ := mul_one _)
    refine integral_mono (hgint.const_mul c0) hint2 (fun u => ?_)
    have := mul_le_mul_of_nonneg_left (hwlo u) (hg0 u)
    show c0 * g u ≤ g u * wt wilsonDensity β S u ω
    linarith [mul_comm c0 (g u)]
  have hc0I : 0 ≤ c0 * ∫ u, g u ∂(vol μ S) := (mul_pos hc0pos hI).le
  unfold spec
  rw [le_div_iff₀ hpart]
  calc c0 * (∫ u, g u ∂(vol μ S)) * part wilsonDensity β S μ ω
      ≤ c0 * (∫ u, g u ∂(vol μ S)) * 1 := mul_le_mul_of_nonneg_left hpart1 hc0I
    _ ≤ num wilsonDensity β S μ (⇑F) ω := by rw [mul_one]; exact hnum

/-- **The step-`k` state is positive on a non-negative local field that is positive somewhere.**
DERIVED: `0` the signs. -/
theorem stateK_pos_of_local (hN : N ≠ 0) (k : ℕ) (F : C(Cfg N, ℝ))
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : IsLocalOn S (F : Cfg N → ℝ))
    (hF0 : ∀ U, 0 ≤ F U) {P : Cfg N} (hP : 0 < F P) :
    0 < stateK hN k F :=
  periodicState_pos_of_local hN
    (le_trans zero_le_one (one_le_dyBeta (one_le_of_ne_zero hN) k)) F S hS hF0 hP

end Positive

/-! ## 3. The reduction -/

section Reduction

variable {N : ℕ}

/-- The flowed factor `p1 ∘ V_k` as a local field. DERIVED: no numeral. -/
def flowP (W : ConfFlow N) (k : ℕ) : MassGap.ContinuumField.LField (SU N) := W.fieldMap k (bareF [p1])

/-- The flowed factor is `p1` read at the flowed configuration. DERIVED: no numeral. -/
theorem flowP_apply (W : ConfFlow N) (k : ℕ) (U : Cfg N) : (flowP W k).1 U = facV (W.V k U) p1 := by
  show monoV [p1] (W.V k U) = _
  simp [monoV]

/-- **`ScaleAt` at `s = 1` makes the flowed origin plaquette flat to within `a_k²` at every
configuration.** DERIVED: `1` the scale; `2` the squared spacing and the even power; `1/2` the
reflection average; `0` the signs. -/
theorem facV_le_of_scaleAt_one [NeZero N] {Wf : ℝ → ConfFlow N} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ}
    {k : ℕ} (ht : 0 < t) (h : ScaleAt Wf t C γ γP k 1) (U : Cfg N) :
    facV ((Wf 1).V k U) p1 ≤ dySpacing N k ^ 2 := by
  have hN : N ≠ 0 := NeZero.ne N
  set a : ℝ := dySpacing N k with ha_def
  have ha : 0 < a := dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k
  by_contra hlt
  replace hlt := not_le.mp hlt
  set x0 : ℝ := facV ((Wf 1).V k U) p1 with hx0
  set ρ : ℝ := (x0 + a ^ 2) / 2 with hρ
  have hρa : a ^ 2 < ρ := by rw [hρ]; linarith
  have hρx : ρ < x0 := by rw [hρ]; linarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hρ0 : 0 < ρ := lt_trans ha2 hρa
  -- the cut-off
  set Y := flowP (Wf 1) k with hY
  obtain ⟨S, hS⟩ := Y.2.1
  let G : C(Cfg N, ℝ) := ⟨fun U' => min 1 (max 0 (Y.1 U' - ρ)),
    continuous_const.min (continuous_const.max (Y.1.continuous.sub continuous_const))⟩
  have hG0 : ∀ U', 0 ≤ G U' := fun U' => le_min zero_le_one (le_max_left _ _)
  have hG1 : ∀ U', G U' ≤ 1 := fun U' => min_le_left _ _
  have hGloc : IsLocalOn S (G : Cfg N → ℝ) := fun U' V' hUV => by
    show min 1 (max 0 (Y.1 U' - ρ)) = min 1 (max 0 (Y.1 V' - ρ))
    rw [hS U' V' hUV]
  have hGU : 0 < G U := by
    show 0 < min 1 (max 0 (Y.1 U - ρ))
    rw [hY, flowP_apply, ← hx0]
    exact lt_min one_pos (lt_max_of_lt_right (by linarith))
  have hνG : 0 < stateK hN k G := stateK_pos_of_local hN k G S hGloc hG0 hGU
  -- every channel of the tower
  have hbound : ∀ n : ℕ, Real.exp (t / 2 * (ρ ^ 2 / a ^ 4) ^ (n + 1)) * stateK hN k G ≤ C := by
    intro n
    have hj := h (Sum.inl (jn n))
    have hmu : msMu t γ γP (Sum.inl (jn n)) 1 = t := by
      simp [msMu, afLog]
    have hd : mDim (Sum.inl (jn n)) = 4 * (n + 1) := cdim_mono n
    rw [hmu, hd] at hj
    set L : ℝ := t / 2 * (ρ ^ 2 / a ^ 4) ^ (n + 1) with hL
    have hrate0 : 0 ≤ t / a ^ (4 * (n + 1)) := by positivity
    have hLeq : L = t / a ^ (4 * (n + 1)) * ((1 / 2 : ℝ) * ρ ^ (2 * (n + 1))) := by
      rw [hL, div_pow, pow_mul, pow_mul]
      field_simp
    have hpt : ∀ U', (Real.exp L • G) U' ≤ expC ((t / a ^ (4 * (n + 1))) •
        msAbs ((Wf 1).fieldMap k (mField (Sum.inl (jn n)))).1) U' := by
      intro U'
      simp only [ContinuousMap.smul_apply, smul_eq_mul, expC_apply, msAbs_apply]
      by_cases hc : Y.1 U' ≤ ρ
      · have hG : G U' = 0 := by
          show min 1 (max 0 (Y.1 U' - ρ)) = 0
          rw [max_eq_left (by linarith)]
          exact min_eq_right zero_le_one
        rw [hG, mul_zero]
        exact (Real.exp_pos _).le
      · replace hc := not_le.mp hc
        have hYU : Y.1 U' = facV ((Wf 1).V k U') p1 := by rw [hY, flowP_apply]
        have hX : (1 / 2 : ℝ) * ρ ^ (2 * (n + 1))
            ≤ |((Wf 1).fieldMap k (mField (Sum.inl (jn n)))).1 U'| := by
          have hc' := chan_ge (N := N) n ((Wf 1).V k U')
          have hpow : ρ ^ (2 * (n + 1)) ≤ facV ((Wf 1).V k U') p1 ^ (2 * (n + 1)) :=
            pow_le_pow_left₀ hρ0.le (by rw [← hYU]; exact hc.le) _
          have hval : ((Wf 1).fieldMap k (mField (Sum.inl (jn n)))).1 U'
              = (MassGap.ReflAvg.bR N (jn n)).1 ((Wf 1).V k U') := rfl
          rw [hval]
          exact le_trans (by linarith) (le_abs_self _)
        have hexp : Real.exp L ≤ Real.exp (t / a ^ (4 * (n + 1))
            * |((Wf 1).fieldMap k (mField (Sum.inl (jn n)))).1 U'|) := by
          rw [Real.exp_le_exp, hLeq]
          exact mul_le_mul_of_nonneg_left hX hrate0
        calc Real.exp L * G U' ≤ Real.exp L * 1 :=
              mul_le_mul_of_nonneg_left (hG1 U') (Real.exp_pos _).le
          _ ≤ _ := by rw [mul_one]; exact hexp
    have hmono := (stateK hN k).mono hpt
    rw [(stateK hN k).map_smul] at hmono
    exact hmono.trans hj
  -- the tower is unbounded
  have hq : 1 < ρ ^ 2 / a ^ 4 := by
    rw [one_lt_div (by positivity)]
    have : (a ^ 2) ^ 2 < ρ ^ 2 := pow_lt_pow_left₀ hρa ha2.le two_ne_zero
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ < ρ ^ 2 := this
  set M : ℝ := 2 * |C| / (t * stateK hN k G) with hM
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_ge_atTop M)
  have hqn : M ≤ (ρ ^ 2 / a ^ 4) ^ (n0 + 1) := hn0 _ (Nat.le_succ n0)
  have hb := hbound n0
  have hL0 : |C| ≤ t / 2 * (ρ ^ 2 / a ^ 4) ^ (n0 + 1) * stateK hN k G := by
    have htν : 0 < t * stateK hN k G := mul_pos ht hνG
    have hM' : M * (t * stateK hN k G) = 2 * |C| := by
      rw [hM]; field_simp
    nlinarith
  have hexp := Real.add_one_le_exp (t / 2 * (ρ ^ 2 / a ^ 4) ^ (n0 + 1))
  nlinarith [abs_nonneg C, le_abs_self C, mul_le_mul_of_nonneg_right hexp hνG.le]

/-- **`(M_W)` makes every flowed origin plaquette flat to within `a_k²`, eventually in the step.**
DERIVED: `2` the squared spacing. -/
theorem facV_le_of_MW [NeZero N] {W : ConfFlow N} (hM : MW W) :
    ∀ᶠ k in atTop, ∀ U : Cfg N, facV (W.V k U) p1 ≤ dySpacing N k ^ 2 := by
  obtain ⟨t, C, ht, hev⟩ := hM
  filter_upwards [hev] with k hk U
  exact facV_le_of_scaleAt_one (Wf := fun _ => W) ht hk U

/-- **`ScaleControlAll b Wf` at `b ≥ 1` does the same for `Wf 1`.**
DERIVED: `1` the scale; `2` the squared spacing. -/
theorem facV_le_of_scaleControlAll [NeZero N] {b : ℝ} (hb : 1 ≤ b) {Wf : ℝ → ConfFlow N}
    (h : ScaleControlAll b Wf) :
    ∀ᶠ k in atTop, ∀ U : Cfg N, facV ((Wf 1).V k U) p1 ≤ dySpacing N k ^ 2 := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := h
  filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk ha U
  exact facV_le_of_scaleAt_one ht (hk 1 ha.le hb) U

end Reduction

/-! ## 4. The `π`-flux fixed point of the ray-averaged observer -/

section PiFlux

/-- **The staggered slice** `y ↦ e^{iπy}`. DERIVED: `π` the staggered phase. -/
def fpi (y : ℤ) : Circle := Circle.exp ((y : ℝ) * Real.pi)

/-- DERIVED: no numeral. -/
theorem fpi_add (y o : ℤ) : fpi (y + o) = fpi y * fpi o := by
  unfold fpi
  rw [← Circle.exp_add]
  congr 1
  push_cast
  ring

/-- DERIVED: `0` the imaginary part of a sign. -/
theorem fpi_im (o : ℤ) : ((fpi o : Circle) : ℂ).im = 0 := by
  rw [fpi, Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Real.sin_int_mul_pi]

/-- DERIVED: no numeral. -/
theorem fpi_eq_re (o : ℤ) : ((fpi o : Circle) : ℂ) = ((((fpi o : Circle) : ℂ).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [fpi_im])

/-- **The staggered slice is fixed by the one-dimensional block average**: each staple is the link
times a real sign, and the total weight is below `1`. DERIVED: `1` the weight bound; `0` the signs;
`6 = 3 · 2` the staple directions and sides of `blStaples`. -/
theorem Fz_fpi {e : ℝ} (he0 : 0 ≤ e) {d : ℕ} (he : (Fintype.card (Fin 6 × Fin d) : ℝ) * e < 1) :
    Fz e d fpi = fpi := by
  funext y
  set S : ℝ := ∑ q : Fin 6 × Fin d, ((fpi (off d q) : Circle) : ℂ).re with hS
  have hsum : ∑ q : Fin 6 × Fin d, ((fpi (y + off d q) : Circle) : ℂ)
      = ((fpi y : Circle) : ℂ) * (S : ℂ) := by
    rw [hS, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [fpi_add, Circle.coe_mul, ← fpi_eq_re]
  have hSlo : -(Fintype.card (Fin 6 × Fin d) : ℝ) ≤ S := by
    rw [hS]
    calc -(Fintype.card (Fin 6 × Fin d) : ℝ) = ∑ _q : Fin 6 × Fin d, (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
          have h := Complex.abs_re_le_norm ((fpi (off d q) : Circle) : ℂ)
          rw [Circle.norm_coe] at h
          linarith [neg_abs_le (((fpi (off d q) : Circle) : ℂ).re)]
  set r : ℝ := 1 + e * S with hr
  have hrpos : 0 < r := by nlinarith [mul_le_mul_of_nonneg_left hSlo he0]
  have hw : ((fpi y : Circle) : ℂ) + (e : ℂ) * ∑ q : Fin 6 × Fin d, ((fpi (y + off d q) : Circle) : ℂ)
      = (r : ℂ) * ((fpi y : Circle) : ℂ) := by
    rw [hsum, hr]
    push_cast
    ring
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hne : (r : ℂ) * ((fpi y : Circle) : ℂ) ≠ 0 := mul_ne_zero hr0 (Circle.coe_ne_zero _)
  have hn : ‖(r : ℂ) * ((fpi y : Circle) : ℂ)‖ = r := by
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
  apply Circle.ext
  show ((nz _ : Circle) : ℂ) = _
  rw [hw, coe_nz hne, hn, mul_div_cancel_left₀ _ hr0]

variable {n : ℕ}

/-- **The `π`-flux slice configuration is a fixed point of the ray-averaged block step.**
DERIVED: `2` the least rank; `12` the coupling bound; `1` the sine bound. -/
theorem blStep_fpi (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (d : ℕ) :
    blStep hN c hc0 hc d (dgConf (zeta fpi)) = dgConf (zeta fpi) := by
  have hK := avg_coupling hN hc d
  have hK0 : 0 ≤ (Fintype.card (Fin 6 × Fin d) : ℝ) * (c / d) :=
    mul_nonneg (Nat.cast_nonneg _) (avg_weight_nonneg hc0 d)
  have h1 : (Fintype.card (Fin 6 × Fin d) : ℝ) * (c / d) < 1 := by
    linarith [Real.sin_le_one (Real.pi / ((n + 2 : ℕ) : ℝ))]
  rw [blStep_zeta, Fz_fpi (avg_weight_nonneg hc0 d) h1]

/-- **The `π`-flux slice configuration is a fixed point of every ray-averaged multigrid map.**
DERIVED: `0` no level; `2` the stride ratio; Inherited: `12 = 2 · 6` the coupling bound of
`ObserverBlock.avg_coupling`. -/
theorem blMap_fpi (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m J : ℕ) :
    blMap hN hc0 hc m J (dgConf (zeta fpi)) = dgConf (zeta fpi) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    show (blStep hN c hc0 hc (2 ^ J))^[m] (blMap hN hc0 hc m J (dgConf (zeta fpi))) = _
    rw [ih]
    exact Function.iterate_fixed (blStep_fpi hN hc0 hc _) m

/-- **Every member of `blFam` fixes the `π`-flux slice configuration.** DERIVED: `2` the least rank;
Inherited: `12 = 2 · 6` the coupling bound of `ObserverBlock.avg_coupling`. -/
theorem blFam_V_fpi (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m : ℕ) (s : ℝ) (k : ℕ) :
    (blFam hN c hc0 hc m s).V k (dgConf (zeta fpi)) = dgConf (zeta fpi) :=
  blMap_fpi hN hc0 hc m _

/-- The origin plaquette of the `π`-flux configuration is `D(e^{iπ})`.
DERIVED: `0`, `1` the plane and the origin. -/
theorem plaqG_fpi : plaqG (dgConf (n := n) (zeta fpi)) 0 1 0 = dgHom (fpi 1) := by
  have h0 : ∀ x : ISite, dgConf (n := n) (zeta fpi) ((0 : Fin 4), x) = 1 := fun x => by
    simp [dgConf, zeta]
  have h1 : ∀ x : ISite, dgConf (n := n) (zeta fpi) ((1 : Fin 4), x) = dgHom (fpi (x 0)) := fun x => by
    simp [dgConf, zeta]
  have hs : (ishift 0 (0 : ISite)) 0 = 1 := by simp [ishift_apply']
  have hf0 : fpi 0 = 1 := by simp [fpi]
  unfold plaqG
  rw [h0, h0, h1, h1, hs]
  simp [hf0]

/-- DERIVED: `2` the two phase entries. -/
theorem trace_dgHom_re (z : Circle) :
    (Matrix.trace ((dgHom (n := n) z : SU (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)).re
      = 2 * (z : ℂ).re + n := by
  rw [dgHom_coe, Matrix.trace_diagonal, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [dv]
  ring

/-- **The `π`-flux origin plaquette has `N − Re tr = 4`.** DERIVED: `4 = 2 · 2` the two flipped
entries; `π` the phase. -/
theorem facV_fpi : facV (dgConf (n := n) (zeta fpi)) p1 = 4 := by
  rw [facV_p1, plaqG_fpi]
  have := trace_dgHom_re (n := n) (fpi 1)
  have hre : ((fpi 1 : Circle) : ℂ).re = -1 := by
    rw [fpi, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    simp
  rw [show ((dgHom (n := n) (fpi 1) : SU (n + 2)) : Mat (n + 2))
      = ((dgHom (n := n) (fpi 1) : SU (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) from rfl,
    this, hre]
  push_cast
  ring

end PiFlux

/-! ## 5. The no-go at the ray-averaged observer -/

section NoGo

/-- **`(M_W)` fails at every ray-averaged observer.** DERIVED: `2` the least rank and the squared
spacing; `4` the `π`-flux defect; Inherited: `12` the coupling bound of `ObserverBlock.avg_coupling`. -/
theorem not_MW_blFam {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) :
    ¬ MW (blFam hN c hc0 hc m s) := by
  intro hM
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hev := facV_le_of_MW hM
  have hsmall : ∀ᶠ k in atTop, dySpacing (n + 2) k < 2 :=
    (tendsto_dySpacing (n + 2)).eventually (gt_mem_nhds two_pos)
  obtain ⟨k, hk, hk2⟩ := (hev.and hsmall).exists
  have h := hk (dgConf (zeta fpi))
  rw [blFam_V_fpi hN hc0 hc m s k, facV_fpi] at h
  have ha := dySpacing_pos (by omega : 1 ≤ n + 2) k
  nlinarith

/-- **No family with `Wf 1 = blFam …` meets `ScaleControlAll 1`** (`ObserverBlock.blFam_mw_iff`).
DERIVED: `1` the scale; `2` the least rank; Inherited: `12` the coupling bound of
`ObserverBlock.avg_coupling`. -/
theorem not_exists_scaleControlAll_blFam {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) :
    ¬ ∃ Wf : ℝ → ConfFlow N, Wf 1 = blFam hN c hc0 hc m s ∧ ScaleControlAll 1 Wf :=
  fun h => not_MW_blFam hN hc0 hc m s ((blFam_mw_iff hN hc0 hc m s).mp h)

/-- **No family with `Wf 1 = blFam …` meets `ScaleControlAll b` at any `b ≥ 1`.**
DERIVED: `1` the scale; `2` the least rank and the squared spacing; `4` the `π`-flux defect;
Inherited: `12` the coupling bound of `ObserverBlock.avg_coupling`. -/
theorem not_scaleControlAll_of_one_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) {b : ℝ} (hb : 1 ≤ b)
    {Wf : ℝ → ConfFlow N} (h1 : Wf 1 = blFam hN c hc0 hc m s) : ¬ ScaleControlAll b Wf := by
  intro h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have hev := facV_le_of_scaleControlAll hb h
  have hsmall : ∀ᶠ k in atTop, dySpacing (n + 2) k < 2 :=
    (tendsto_dySpacing (n + 2)).eventually (gt_mem_nhds two_pos)
  obtain ⟨k, hk, hk2⟩ := (hev.and hsmall).exists
  have h' := hk (dgConf (zeta fpi))
  rw [h1, blFam_V_fpi hN hc0 hc m s k, facV_fpi] at h'
  have ha := dySpacing_pos (by omega : 1 ≤ n + 2) k
  nlinarith

end NoGo

end MassGap.BulkBound

end

#print axioms MassGap.BulkBound.facV_p1
#print axioms MassGap.BulkBound.cdim_mono
#print axioms MassGap.BulkBound.ctau_mono
#print axioms MassGap.BulkBound.chan_ge
#print axioms MassGap.BulkBound.periodicState_pos_of_local
#print axioms MassGap.BulkBound.stateK_pos_of_local
#print axioms MassGap.BulkBound.facV_le_of_scaleAt_one
#print axioms MassGap.BulkBound.facV_le_of_MW
#print axioms MassGap.BulkBound.facV_le_of_scaleControlAll
#print axioms MassGap.BulkBound.Fz_fpi
#print axioms MassGap.BulkBound.blMap_fpi
#print axioms MassGap.BulkBound.blFam_V_fpi
#print axioms MassGap.BulkBound.facV_fpi
#print axioms MassGap.BulkBound.not_MW_blFam
#print axioms MassGap.BulkBound.not_exists_scaleControlAll_blFam
#print axioms MassGap.BulkBound.not_scaleControlAll_of_one_le
