import Mathlib
import MassGap.CompositesRenAll

/-!
# MassGap.MultiScaleOS — `OS0C` and `OS1C` of the renormalised composites from the multi-scale control

The target asks `OS0C ∧ OS1C ∧ CovC ∧ CompNondeg` of `CRen 2 z μ`. This module derives `OS1C` from the
`scale` and `expand` clauses of `MultiScaleAllRen`, and derives `OS0C` from them with one added clause on
the expansion coefficients.

Every lemma of §1–§4 that involves the gauge group is stated at every `SU(N)` (`[NeZero N]`, flows
`Wf : ℝ → ConfFlow N`, composites `CRen N z μ`), except the record `MultiScaleAllRen'` and the theorems that
read it or `MultiScaleAllRen` (`os1C_of_ren_all`, `os0C_of_ren_all'`), which are at `SU(2)`.

## 1. Riemann sums (proved)

* `tendsto_riemann`: for a continuous `g` bounded by `M` with support in `[-R, R]⁴`,
  `∑_{x ∈ box ⌈R/a_k⌉} a_k⁴ g(a_k x) → ∫ g` as `k → ∞`, `a_k = dySpacing N k`. The proof rescales
  Mathlib's `tendsto_tsum_div_pow_atTop_integral` (spacing `1/n`, on a cube whose frontier is null by
  `Convex.addHaar_frontier`) to the spacing `a_k = aRun N 1 / 2^(k+1)` (`riemann_nat`,
  `tsum_lattice_eq`, `MeasureTheory.Measure.integral_comp_smul`).
* `tendsto_wS`: hence `wS a_k f = ∑ a_k⁴ |f(a_k x)| → ‖f‖_{L¹}` for every continuous test function.

## 2. Moments of weighted lattice sums (proved)

* `moment_wsum_le`: in a translation-invariant state, `ν((∑_{x ∈ s} wₓ T_x F)^{2p}) ≤ (∑ |wₓ|)^{2p} ν(F^{2p})`
  (the Jensen step of `ObserverEnergyMoments.moment_smear_le`, for arbitrary weights).
* `moment_smear_wS`: `ν(smear a F f ^{2p}) ≤ wS a f ^{2p} ν(F^{2p})`, the `L¹` form of `moment_smear_le`.
* `moment_smear_sub_le`: for `|wᵢ| ≤ 1`, `ν((smear a F (f translated by w) − smear a F f)^{2p})
  ≤ wD a f w ^{2p} ν(F^{2p})`, `wD = ∑ a⁴ |f(a x − w) − f(a x)|`; `wD_tendsto`: `wD a_k f w_k → 0` when
  `|w_k| ≤ a_k` (uniform continuity of a continuous compactly supported `f`).

## 3. `OS1C` (proved from `scale` and `expand`)

`os1C_of_scale_expand` (`scale` and `ExpandR` give `OS1C (CRen N z μ)`, every `SU(N)`),
`os1C_of_ren_all : MultiScaleAllRen W z μ → OS1C (CRen 2 z μ)`. No added
hypothesis. For a translation `v`, at step `k` write `v = a_k n_k + w_k` with `n_k ∈ ℤ⁴`, `0 ≤ w_k < a_k`
componentwise. The lattice translation by `n_k` is exact on the flowed reading (`msLat_translate_lat`:
`smear_translate`, `transObs_prod`, `stateK_transObs`). The residual `w_k` changes the flowed reading by at
most `∑_{T ≠ ∅} (1 + n c) ∏ᵢ L^T_i` (`abs_state_prod_sub_le`: expand `∏(Dᵢ + Yᵢ)` over subsets, Hölder
on each term), with `L^T_i = (wD + a_k) · msPsize` on `T`, which tends to `0` at fixed `s`
(`msLat_translate_sub_tendsto`). `expand` at both families bounds the two remainders by
`Q (s/d)^ε`; choosing `s` small first and `k` large second gives `latC(F + v) − latC(F) → 0`, and `ConvC`
(from `BoundC`) gives the limit `contC F`.

## 4. `OS0C` (proved from `scale`, `expand` and `CoefBound`)

`CoefBound c`: there are finite sets `S i` of indices, `Kᵢ`, `γcᵢ` with, for every `0 < s ≤ 1`,
`supp c(i, s) ⊆ S i` and `|c_{ij}(s)| ≤ Kᵢ s^{d_j} / s^{d_i} · (1 + |log s|)^{γcᵢ}`. It reads only the
expansion coefficients `c` (no lattice reading, no limit, no Schwinger function), so it is not a restatement
of `OS0C`. `MultiScaleAllRen' W z μ` is `MultiScaleAllRen` with `CoefBound` added on the same `c`.

`os0C_of_scale_expand_coef` (`scale`, `ExpandR` and `CoefBound` give `OS0C (CRen N z μ)`, every `SU(N)`),
`os0C_of_ren_all' : MultiScaleAllRen' W z μ → OS0C (CRen 2 z μ)`. At `0 < d ≤ 1` take
`s = θ' d`, `θ' = min(θ, b, 1)`. Each lattice reading is bounded by the flowed reading
(`abs_msLat_le_wS`: factors `(wS a_k fᵢ + a_k) · msPsize`) plus the `expand` remainder; `wS → ‖fᵢ‖_{L¹}`
and `ConvC` pass the bound to `contC` (`abs_contC_le_of`). `CoefBound` gives
`msPsize(s) ≤ Pᵢ (s⁻¹)^{κᵢ}` (`msPsize_le`; `(1 + |log s|)^γ ≤ (s⁻¹)^{γ⁺}`, `afLog_le_inv_rpow`), with
`κᵢ = dᵢ + γcᵢ⁺ + ∑_{j ∈ S i} γ_j⁺`. `n (2n)! ≤ 8ⁿ (n!)²` (`one_add_mul_fact_le`) gives the constants
`α = 1 + (e^C C)⁺ + θ'^ε`, `γ = 8`, `β = 2`, `Cᵢ = Pᵢ θ'^{−κᵢ} + |K_r|`, exponent `max(κᵢ, κrᵢ)`.

## 5. No capstone from the record

No `ClayStatementAt` is stated from `MultiScaleAllRen'`: its `endpoint` field,
`MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 6. What remains as inputs (argued; no declaration)

`CoefBound` (added clause), `CovC`, `CompNondeg`, `ObsLower`, `WardT`, `phys`, `ApproxK`, and the
clauses of `MultiScaleAllRen` itself. `CovC`, `CompNondeg`, `ObsLower`, `WardT` are not size bounds
(`MultiScaleAll` §3); this module does not touch them.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the even moment powers and the exponent of `n!`; `4` the
dimension and the cell-volume exponent; `8 = 2 · 4` from `n ≤ 2ⁿ` and `C(2n, n) ≤ 4ⁿ`; `1` the bound of
the spacing, of the scale and of the residual shift, the floor `1 + |log s|` and the `+ 1` that keeps
sizes positive; `3` the box of `riemann_le`; `0` the signs and limits.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MultiScaleOS

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. Riemann sums -/

/-- The lattice box grows with its radius. DERIVED: `4` the dimension. -/
theorem box_mono {K K' : ℕ} (h : K ≤ K') : box K ⊆ box K' := by
  intro x hx
  unfold box at hx ⊢
  rw [Fintype.mem_piFinset] at hx ⊢
  intro i
  have hi := hx i
  rw [Finset.mem_Icc] at hi ⊢
  constructor <;> omega

/-- The lattice point `x / n` of `ℝ⁴`. -/
def latPt (n : ℕ) (x : ISite) : Fin 4 → ℝ := fun i => (x i : ℝ) / n

theorem latPt_apply (n : ℕ) (x : ISite) (i : Fin 4) : latPt n x i = (x i : ℝ) / n := rfl

/-- **The lattice points of spacing `1/n` in a cube, read at spacing `A/n`**: if `S'` is the set of points
of the cube `[-c, c]⁴` with `n y ∈ ℤ⁴`, `c ≥ R/A + 1`, then `∑'_{y ∈ S'} g(A y) = ∑_{x ∈ box} g((A/n) x)`.
DERIVED: `4` the dimension; `1` the slack of the cube and the least `n`. -/
theorem tsum_lattice_eq {n : ℕ} (hn : 0 < n) {A c R M : ℝ} (hA : 0 < A)
    {g : (Fin 4 → ℝ) → ℝ} (hg : IsTest g R M) (hc : R / A + 1 ≤ c) {S' : Set (Fin 4 → ℝ)}
    (hS : ∀ y, y ∈ S' ↔ (∀ i, |y i| ≤ c) ∧ ∀ i, ∃ m : ℤ, (m : ℝ) = n * y i) :
    ∑' y : S', g (A • (y : Fin 4 → ℝ)) = ∑ x ∈ box ⌈R / (A / n)⌉₊, g (site (A / n) x) := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have ha : 0 < A / n := div_pos hA hnR
  have hφg : ∀ x, g (A • latPt n x) = g (site (A / n) x) := fun x => by
    congr 1
    funext i
    simp only [latPt_apply, Pi.smul_apply, smul_eq_mul, site]
    ring
  have hmemφ : ∀ x ∈ box ⌈R / (A / n)⌉₊, latPt n x ∈ S' := by
    intro x hx
    rw [hS]
    refine ⟨fun i => ?_, fun i => ⟨x i, by rw [latPt_apply, mul_div_cancel₀ _ hnR.ne']⟩⟩
    have hxi : |x i| ≤ (⌈R / (A / n)⌉₊ : ℤ) := by
      unfold box at hx
      rw [Fintype.mem_piFinset] at hx
      have := hx i
      rw [Finset.mem_Icc] at this
      exact abs_le.mpr this
    have hxR : |(x i : ℝ)| ≤ (⌈R / (A / n)⌉₊ : ℝ) := by exact_mod_cast hxi
    have hR0 : 0 ≤ R / (A / n) := div_nonneg hg.1 ha.le
    have hKlt : (⌈R / (A / n)⌉₊ : ℝ) < R / (A / n) + 1 := Nat.ceil_lt_add_one hR0
    have h1 : R / (A / n) = R / A * n := by rw [div_div_eq_mul_div]; ring
    have h2 := mul_le_mul_of_nonneg_right hc hnR.le
    rw [latPt_apply, abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
    nlinarith
  have hinj : ∀ x y : ISite, latPt n x = latPt n y → x = y := by
    intro x y h
    funext i
    have h1 := congrFun h i
    rw [latPt_apply, latPt_apply, div_left_inj' hnR.ne'] at h1
    exact_mod_cast h1
  let e : {x // x ∈ box ⌈R / (A / n)⌉₊} → S' := fun x => ⟨latPt n x.1, hmemφ x.1 x.2⟩
  rw [tsum_eq_sum (s := (box ⌈R / (A / n)⌉₊).attach.image e)]
  · rw [Finset.sum_image (fun x _ y _ hxy => Subtype.ext (hinj _ _ (congrArg Subtype.val hxy)))]
    rw [← Finset.sum_attach (box ⌈R / (A / n)⌉₊) (fun x => g (site (A / n) x))]
    exact Finset.sum_congr rfl fun x _ => hφg x.1
  · intro y hy
    by_contra hne
    apply hy
    obtain ⟨-, hm⟩ := (hS y.1).mp y.2
    choose m hm using hm
    have hφm : latPt n m = y.1 := funext fun i => by
      rw [latPt_apply, hm i, mul_div_cancel_left₀ _ hnR.ne']
    have hbox : m ∈ box ⌈R / (A / n)⌉₊ := mem_box_of_ne ha hg m (by rw [← hφg, hφm]; exact hne)
    exact Finset.mem_image.mpr ⟨⟨m, hbox⟩, Finset.mem_attach _ _, Subtype.ext hφm⟩

/-- **Riemann sums at spacing `A/n`**: for a continuous `g` bounded by `M` with support in `[-R, R]⁴`,
`∑_{x ∈ box} (A/n)⁴ g((A/n) x) → ∫ g` as `n → ∞`. Mathlib's `tendsto_tsum_div_pow_atTop_integral` on the
cube `[-(R/A + 1), R/A + 1]⁴`, rescaled by `A`. DERIVED: `4` the dimension; `1` the cube slack. -/
theorem riemann_nat {A : ℝ} (hA : 0 < A) {g : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (hg : IsTest g R M)
    (hgc : Continuous g) :
    Tendsto (fun n : ℕ => ∑ x ∈ box ⌈R / (A / n)⌉₊, (A / n) ^ 4 * g (site (A / n) x)) atTop
      (𝓝 (∫ y, g y)) := by
  have hs1 : Bornology.IsBounded
      (Set.Icc (fun _ : Fin 4 => -(R / A + 1)) (fun _ => R / A + 1)) := Metric.isBounded_Icc _ _
  have hs2 : MeasurableSet (Set.Icc (fun _ : Fin 4 => -(R / A + 1)) (fun _ => R / A + 1)) :=
    measurableSet_Icc
  have hs3 : MeasureTheory.volume
      (frontier (Set.Icc (fun _ : Fin 4 => -(R / A + 1)) (fun _ => R / A + 1))) = 0 :=
    Convex.addHaar_frontier MeasureTheory.volume (convex_Icc _ _)
  have hhc : Continuous (fun y : Fin 4 → ℝ => g (A • y)) := hgc.comp (continuous_const_smul A)
  have hzero : ∀ y, y ∉ Set.Icc (fun _ : Fin 4 => -(R / A + 1)) (fun _ => R / A + 1) →
      g (A • y) = 0 := by
    intro y hy
    by_contra hne
    apply hy
    have hb : ∀ i, |y i| ≤ R / A + 1 := by
      intro i
      have h1 := hg.2.2 _ hne i
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      rw [abs_mul, abs_of_pos hA] at h1
      have h2 : |y i| ≤ R / A := by
        rw [le_div_iff₀ hA]
        linarith
      linarith
    exact Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i => (abs_le.mp (hb i)).1,
      Pi.le_def.mpr fun i => (abs_le.mp (hb i)).2⟩
  have T := tendsto_tsum_div_pow_atTop_integral
    (s := Set.Icc (fun _ : Fin 4 => -(R / A + 1)) (fun _ => R / A + 1)) (F := fun y => g (A • y))
    hhc hs1 hs2 hs3
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    MeasureTheory.Measure.integral_comp_smul MeasureTheory.volume g A, Module.finrank_fin_fun,
    abs_of_pos (inv_pos.mpr (pow_pos hA 4)), smul_eq_mul] at T
  have T2 := T.const_mul (A ^ 4)
  have hlim : A ^ 4 * ((A ^ 4)⁻¹ * ∫ y, g y) = ∫ y, g y := by
    rw [← mul_assoc, mul_inv_cancel₀ (pow_pos hA 4).ne', one_mul]
  rw [hlim] at T2
  refine T2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  haveI : NeZero n := ⟨by omega⟩
  rw [tsum_lattice_eq (n := n) (by omega) hA hg le_rfl ?_]
  · rw [Fintype.card_fin, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [div_pow]
    ring
  · intro y
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := Set.mem_Icc.mp h1
      refine ⟨fun i => abs_le.mpr ⟨Pi.le_def.mp h1'.1 i, Pi.le_def.mp h1'.2 i⟩, fun i => ?_⟩
      obtain ⟨m, hm⟩ := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).mp h2 i
      exact ⟨m, by simpa using hm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i => (abs_le.mp (h1 i)).1,
        Pi.le_def.mpr fun i => (abs_le.mp (h1 i)).2⟩, ?_⟩
      exact (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).mpr fun i => by
        obtain ⟨m, hm⟩ := h2 i
        exact ⟨m, by simpa using hm⟩

/-- **Riemann sums converge along the dyadic spacings**: for a continuous `g` bounded by `M` with support
in `[-R, R]⁴`, `∑_{x ∈ box ⌈R/a_k⌉} a_k⁴ g(a_k x) → ∫ g`, `a_k = dySpacing N k`. DERIVED: `2` the halving;
`4` the dimension; `1` the step offset. -/
theorem tendsto_riemann [NeZero N] {g : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (hg : IsTest g R M) (hgc : Continuous g) :
    Tendsto (fun k => ∑ x ∈ box ⌈R / dySpacing N k⌉₊,
      dySpacing N k ^ 4 * g (site (dySpacing N k) x)) atTop (𝓝 (∫ y, g y)) := by
  have hA : 0 < AsymptoticScaling.aRun N 1 := AsymptoticScaling.aRun_pos (Nat.pos_of_ne_zero (NeZero.ne N)) one_pos
  have h2 : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k + 1)).le) (tendsto_add_atTop_nat 1)
  have e : ∀ k, dySpacing N k = AsymptoticScaling.aRun N 1 / ((2 ^ (k + 1) : ℕ) : ℝ) := fun k => by
    simp [dySpacing]
  simp_rw [e]
  exact (riemann_nat hA hg hgc).comp h2

/-! ## 2. Moments of weighted lattice sums -/

section Moments

/-- **The even moments of a weighted lattice sum**: in a translation-invariant state,
`ν((∑_{x ∈ s} wₓ T_x F)^{2p}) ≤ (∑ |wₓ|)^{2p} ν(F^{2p})`. Jensen for the convex power with the weights
`|wₓ| / W`, as in `ObserverEnergyMoments.moment_smear_le`. DERIVED: `2` the even power; `1` the Jensen
normalisation; `0` the vanishing weight. -/
theorem moment_wsum_le (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) (s : Finset ISite)
    (w : ISite → ℝ) (F : C(Cfg N, ℝ)) (p : ℕ) :
    ν ((∑ x ∈ s, w x • transObs x F) ^ (2 * p)) ≤ (∑ x ∈ s, |w x|) ^ (2 * p) * ν (F ^ (2 * p)) := by
  classical
  set W : ℝ := ∑ x ∈ s, |w x| with hW
  have hq : Even (2 * p) := even_two_mul p
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have hval : ∀ U : Cfg N, (∑ x ∈ s, w x • transObs x F) U = ∑ x ∈ s, w x * F (transConf x U) := by
    intro U
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
      smul_eq_mul]
  rcases hW0.lt_or_eq with hWpos | hWz
  · have hbound : ν ((∑ x ∈ s, w x • transObs x F) ^ (2 * p))
        ≤ ν (W ^ (2 * p) • ∑ x ∈ s, (|w x| / W) • transObs x (F ^ (2 * p))) := by
      refine ν.mono (fun U => ?_)
      rw [ContinuousMap.pow_apply, hval U]
      simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
        transObs_apply, ContinuousMap.pow_apply, smul_eq_mul]
      have hv0 : ∀ x ∈ s, 0 ≤ |w x| / W := fun x _ => div_nonneg (abs_nonneg _) hWpos.le
      have hv1 : ∑ x ∈ s, |w x| / W = 1 := by
        rw [← Finset.sum_div, ← hW, div_self hWpos.ne']
      have habs : |∑ x ∈ s, w x * F (transConf x U)|
          ≤ ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) := by
        calc |∑ x ∈ s, w x * F (transConf x U)|
            ≤ ∑ x ∈ s, |w x * F (transConf x U)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) :=
              Finset.sum_congr rfl (fun x _ => by
                rw [abs_mul]
                field_simp)
      have hj := Real.pow_arith_mean_le_arith_mean_pow s (fun x => |w x| / W)
        (fun x => W * |F (transConf x U)|) hv0 hv1
        (fun x _ => mul_nonneg hWpos.le (abs_nonneg _)) (2 * p)
      calc (∑ x ∈ s, w x * F (transConf x U)) ^ (2 * p)
          = |∑ x ∈ s, w x * F (transConf x U)| ^ (2 * p) := (hq.pow_abs _).symm
        _ ≤ (∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|)) ^ (2 * p) :=
            pow_le_pow_left₀ (abs_nonneg _) habs _
        _ ≤ ∑ x ∈ s, |w x| / W * (W * |F (transConf x U)|) ^ (2 * p) := hj
        _ = W ^ (2 * p) * ∑ x ∈ s, |w x| / W * F (transConf x U) ^ (2 * p) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [mul_pow, hq.pow_abs]
            ring
    have hrhs : ν (W ^ (2 * p) • ∑ x ∈ s, (|w x| / W) • transObs x (F ^ (2 * p)))
        = W ^ (2 * p) * ν (F ^ (2 * p)) := by
      rw [ν.map_smul, ν.map_sum]
      have : ∀ x ∈ s, ν ((|w x| / W) • transObs x (F ^ (2 * p))) = |w x| / W * ν (F ^ (2 * p)) :=
        fun x _ => by rw [ν.map_smul, htr]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← Finset.sum_div, ← hW,
        div_self hWpos.ne', one_mul]
    exact hbound.trans hrhs.le
  · have hw0 : ∀ x ∈ s, w x = 0 := fun x hx =>
      abs_eq_zero.mp (le_antisymm
        ((Finset.single_le_sum (fun y _ => abs_nonneg (w y)) hx).trans hWz.symm.le)
        (abs_nonneg _))
    have hS0 : ∑ x ∈ s, w x • transObs x F = 0 :=
      Finset.sum_eq_zero (fun x hx => by rw [hw0 x hx, zero_smul])
    rw [hS0, ← hWz]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [zero_pow (by omega), ν.map_zero, zero_pow (by omega), zero_mul]

/-- **The `L¹` weight of a test function at spacing `a`**: `wS a f = ∑_{x ∈ box ⌈R/a⌉} a⁴ |f(a x)|`.
DERIVED: `4` the cell-volume exponent. -/
def wS (a : ℝ) (f : TestFn) : ℝ := ∑ x ∈ box ⌈tR f / a⌉₊, a ^ 4 * |f.1 (site a x)|

theorem wS_nonneg {a : ℝ} (ha : 0 < a) (f : TestFn) : 0 ≤ wS a f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)

/-- **The moments of a smeared field, `L¹` form**: `ν(smear a F f ^{2p}) ≤ wS a f ^{2p} ν(F^{2p})`.
DERIVED: `2` the even power; `4` the cell-volume exponent. -/
theorem moment_smear_wS (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (F : C(Cfg N, ℝ)) (f : TestFn) (p : ℕ) :
    ν (smear a F f ^ (2 * p)) ≤ wS a f ^ (2 * p) * ν (F ^ (2 * p)) := by
  rw [smear_eq_sum ha F f (tIs f) (subset_refl _)]
  have h := moment_wsum_le ν htr (box ⌈tR f / a⌉₊) (fun x => a ^ 4 * f.1 (site a x)) F p
  have e : ∑ x ∈ box ⌈tR f / a⌉₊, |a ^ 4 * f.1 (site a x)| = wS a f :=
    Finset.sum_congr rfl fun x _ => by rw [abs_mul, abs_of_nonneg (pow_nonneg ha.le 4)]
  rw [e] at h
  exact h

/-- **The `L¹` weight of a shift difference**: `wD a f w = ∑_{x ∈ box ⌈(R+1)/a⌉} a⁴ |f(a x − w) − f(a x)|`.
DERIVED: `4` the cell-volume exponent; `1` the bound of the shift. -/
def wD (a : ℝ) (f : TestFn) (w : Fin 4 → ℝ) : ℝ :=
  ∑ x ∈ box ⌈(tR f + 1) / a⌉₊, a ^ 4 * |(f.translate w).1 (site a x) - f.1 (site a x)|

/-- A test function shifted by at most `1` in each coordinate has support in `[-(R+1), R+1]⁴`.
DERIVED: `1` the shift bound. -/
theorem isTest_translate (f : TestFn) {w : Fin 4 → ℝ} (hw : ∀ i, |w i| ≤ 1) :
    IsTest (f.translate w).1 (tR f + 1) (tM f) := by
  have hR := tIs f
  refine ⟨by linarith [hR.1], fun y => hR.2.1 _, fun y hy i => ?_⟩
  have h3 := hR.2.2 _ hy i
  have h4 : (y - w) i = y i - w i := rfl
  rw [h4] at h3
  have h6 : |y i| ≤ |y i - w i| + |w i| := by
    have := abs_add_le (y i - w i) (w i)
    rwa [sub_add_cancel] at this
  linarith [hw i]

/-- **The moments of a shift difference of smeared fields**: for `|wᵢ| ≤ 1`,
`ν((smear a F (f shifted by w) − smear a F f)^{2p}) ≤ wD a f w ^{2p} ν(F^{2p})`.
DERIVED: `2` the even power; `4` the cell-volume exponent; `1` the shift bound. -/
theorem moment_smear_sub_le (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (F : C(Cfg N, ℝ)) (f : TestFn) {w : Fin 4 → ℝ} (hw : ∀ i, |w i| ≤ 1) (p : ℕ) :
    ν ((smear a F (f.translate w) - smear a F f) ^ (2 * p)) ≤ wD a f w ^ (2 * p) * ν (F ^ (2 * p)) := by
  have hR := tIs f
  have hsub : box ⌈tR f / a⌉₊ ⊆ box ⌈(tR f + 1) / a⌉₊ :=
    box_mono (Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith) ha.le))
  rw [smear_eq_sum ha F _ (isTest_translate f hw) (subset_refl _), smear_eq_sum ha F f hR hsub,
    ← Finset.sum_sub_distrib]
  have e : ∀ x ∈ box ⌈(tR f + 1) / a⌉₊,
      (a ^ 4 * (f.translate w).1 (site a x)) • transObs x F - (a ^ 4 * f.1 (site a x)) • transObs x F
        = (a ^ 4 * ((f.translate w).1 (site a x) - f.1 (site a x))) • transObs x F :=
    fun x _ => by rw [← sub_smul, mul_sub]
  rw [Finset.sum_congr rfl e]
  have h := moment_wsum_le ν htr (box ⌈(tR f + 1) / a⌉₊)
    (fun x => a ^ 4 * ((f.translate w).1 (site a x) - f.1 (site a x))) F p
  have e2 : ∑ x ∈ box ⌈(tR f + 1) / a⌉₊, |a ^ 4 * ((f.translate w).1 (site a x) - f.1 (site a x))|
      = wD a f w :=
    Finset.sum_congr rfl fun x _ => by rw [abs_mul, abs_of_nonneg (pow_nonneg ha.le 4)]
  rw [e2] at h
  exact h

end Moments

/-- **`wS a_k f → ‖f‖_{L¹}`** for a continuous test function (`tendsto_riemann` at `|f|`).
DERIVED: no numeral. -/
theorem tendsto_wS [NeZero N] (f : TestFn) (hf : Continuous f.1) :
    Tendsto (fun k => wS (dySpacing N k) f) atTop (𝓝 (l1 f)) := by
  have hR := tIs f
  have hT : IsTest (fun y => |f.1 y|) (tR f) (tM f) :=
    ⟨hR.1, fun y => by simp only [abs_abs]; exact hR.2.1 y,
      fun y hy i => hR.2.2 y (fun h => hy (by simp only [h, abs_zero])) i⟩
  exact tendsto_riemann hT (continuous_abs.comp hf)

/-- **`wD a_k f w_k → 0`** when `|w_k i| ≤ a_k`: `f` is continuous with compact support, hence uniformly
continuous, and `riemann_le` bounds the sum by `sup |f(· − w_k) − f| · (2(R+1) + 3)⁴`.
DERIVED: `2` the half; `3`, `4` the box of `riemann_le`; `1` the shift bound. -/
theorem wD_tendsto [NeZero N] (f : TestFn) (hf : Continuous f.1) (w : ℕ → Fin 4 → ℝ)
    (hw : ∀ k i, |w k i| ≤ dySpacing N k) :
    Tendsto (fun k => wD (dySpacing N k) f (w k)) atTop (𝓝 0) := by
  have hR := tIs f
  have hcs : HasCompactSupport f.1 := by
    refine HasCompactSupport.intro (K := Set.Icc (fun _ => -tR f) (fun _ => tR f)) isCompact_Icc ?_
    intro y hy
    by_contra hne
    exact hy (Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i => (abs_le.mp (hR.2.2 y hne i)).1,
      Pi.le_def.mpr fun i => (abs_le.mp (hR.2.2 y hne i)).2⟩)
  have huc := hcs.uniformContinuous_of_continuous hf
  rw [Metric.tendsto_nhds]
  intro η hη
  have hQ : 0 < (2 * (tR f + 1) + 3) ^ 4 := pow_pos (by linarith [hR.1]) 4
  obtain ⟨ρ, hρ, hρf⟩ := Metric.uniformContinuous_iff.mp huc (η / (2 * (2 * (tR f + 1) + 3) ^ 4))
    (div_pos hη (mul_pos two_pos hQ))
  filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds (lt_min hρ one_pos))] with k hk
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hk1 : dySpacing N k ≤ 1 := (hk.trans_le (min_le_right _ _)).le
  have hkρ : dySpacing N k < ρ := hk.trans_le (min_le_left _ _)
  have hw1 : ∀ i, |w k i| ≤ 1 := fun i => (hw k i).trans hk1
  have hδ : ∀ y, |(f.translate (w k)).1 y - f.1 y| ≤ η / (2 * (2 * (tR f + 1) + 3) ^ 4) := by
    intro y
    have hd : dist (y - w k) y < ρ := by
      rw [dist_pi_lt_iff hρ]
      intro i
      rw [Real.dist_eq]
      simp only [Pi.sub_apply, sub_sub_cancel_left, abs_neg]
      exact (hw k i).trans_lt hkρ
    have := hρf hd
    rw [Real.dist_eq] at this
    exact this.le
  have hT : IsTest (fun y => |(f.translate (w k)).1 y - f.1 y|) (tR f + 1)
      (η / (2 * (2 * (tR f + 1) + 3) ^ 4)) := by
    refine ⟨by linarith [hR.1], fun y => by simp only [abs_abs]; exact hδ y, fun y hy i => ?_⟩
    by_cases h1 : f.1 y = 0
    · have h2 : (f.translate (w k)).1 y ≠ 0 := fun h => hy (by simp only [h, h1, sub_zero, abs_zero])
      exact (isTest_translate f hw1).2.2 y h2 i
    · have := hR.2.2 y h1 i
      linarith
  have h := ContinuumNontrivial.riemann_le ha hk1 hT
  have h0 : 0 ≤ wD (dySpacing N k) f (w k) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  calc wD (dySpacing N k) f (w k) ≤ η / (2 * (2 * (tR f + 1) + 3) ^ 4) * (2 * (tR f + 1) + 3) ^ 4 := h
    _ = η / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hQ.ne']
    _ < η := half_lt_self hη

/-! ## 3. `OS1C` -/

/-- **A product through a state, two families**: if `ν((Xᵢ − Yᵢ)^{2n}) ≤ c LDᵢ^{2n}` and
`ν(Yᵢ^{2n}) ≤ c LYᵢ^{2n}`, then `|ν(∏ X) − ν(∏ Y)| ≤ ∑_{T ≠ ∅} (1 + n c) ∏ᵢ (LDᵢ on T, LYᵢ off T)`.
Expand `∏ (Dᵢ + Yᵢ)` over the subsets `T` (`Fintype.prod_add`); the empty subset is `∏ Y`; each other term
is bounded by `ObserverOS.abs_state_prod_le`. DERIVED: `1`, `2` those of `abs_state_prod_le`. -/
theorem abs_state_prod_sub_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι] [DecidableEq ι] (Xf Yf : ι → C(X, ℝ))
    (LD LY : ι → ℝ) (hLD : ∀ i, 0 < LD i) (hLY : ∀ i, 0 < LY i) {c : ℝ}
    (hD : ∀ i, ν ((Xf i - Yf i) ^ (2 * Fintype.card ι)) ≤ c * LD i ^ (2 * Fintype.card ι))
    (hY : ∀ i, ν (Yf i ^ (2 * Fintype.card ι)) ≤ c * LY i ^ (2 * Fintype.card ι)) :
    |ν (∏ i, Xf i) - ν (∏ i, Yf i)|
      ≤ ∑ T ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
          (1 + Fintype.card ι * c) * ∏ i, (if i ∈ T then LD i else LY i) := by
  have hX : ∏ i, Xf i = ∑ T : Finset ι, ∏ i, T.piecewise (fun i => Xf i - Yf i) Yf i := by
    have h := Fintype.prod_add (fun i => Xf i - Yf i) Yf
    simp only [sub_add_cancel] at h
    rw [h]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_piecewise, Finset.univ_inter, ← Finset.compl_eq_univ_sdiff]
  rw [hX, ν.map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset ι))]
  have h0 : ∏ i, (∅ : Finset ι).piecewise (fun i => Xf i - Yf i) Yf i = ∏ i, Yf i := by
    rw [Finset.piecewise_empty]
  rw [h0, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun T _ => ?_)
  refine abs_state_prod_le ν _ (fun i => if i ∈ T then LD i else LY i) (fun i => ?_) (fun i => ?_)
  · show 0 < (if i ∈ T then LD i else LY i)
    split_ifs
    exacts [hLD i, hLY i]
  · by_cases hi : i ∈ T
    · simp only [Finset.piecewise_eq_of_mem _ _ _ hi, if_pos hi]
      exact hD i
    · simp only [Finset.piecewise_eq_of_notMem _ _ _ hi, if_neg hi]
      exact hY i

/-- **Lattice translations are exact on the flowed reading**: for every `m ∈ ℤ⁴`, the flowed reading of
the family translated by `v` equals that of the family translated by `v − a_k m` (`smear_translate`,
`transObs_prod`, `stateK_transObs`). DERIVED: no numeral. -/
theorem msLat_translate_lat [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    {ι : Type} [Fintype ι] (F : ι → CDatum (CbR N zOne)) (v : Fin 4 → ℝ) (m : ISite) :
    msLat Wf c k s (fun i => translateD v (F i))
      = msLat Wf c k s (fun i => translateD (v - site (dySpacing N k) m) (F i)) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  simp only [translateD]
  have e : ∀ i, smear (dySpacing N k) (msProx Wf c k s (F i).1) ((F i).2.translate v)
      = transObs m (smear (dySpacing N k) (msProx Wf c k s (F i).1)
          ((F i).2.translate (v - site (dySpacing N k) m))) := by
    intro i
    rw [← smear_translate ha, TestFn.translate_translate, sub_add_cancel]
  simp_rw [e]
  rw [← transObs_prod]
  exact ContinuumNontrivial.stateK_transObs (NeZero.ne N) k m _

/-- **The flowed reading is continuous under translations, at fixed `s`**: under `ScaleAt` at `s`
eventually in the step, `msLat(F + v) − msLat(F) → 0`. With `v = a_k n_k + w_k`, `0 ≤ w_k < a_k`, the
lattice part is exact (`msLat_translate_lat`) and the residual is bounded by `abs_state_prod_sub_le`,
whose terms tend to `0` (`wD_tendsto`). DERIVED: `2` the even powers; `1` the
spacing bound; `0` the limit. -/
theorem msLat_translate_sub_tendsto [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ}
    {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s)
    (hS : ∀ᶠ k in atTop, ScaleAt Wf t C γ γP k s) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → CDatum (CbR N zOne)) (hF : ContD F) (v : Fin 4 → ℝ) :
    Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F) atTop
      (𝓝 0) := by
  let nk : ℕ → ISite := fun k i => ⌊v i / dySpacing N k⌋
  let w : ℕ → Fin 4 → ℝ := fun k => v - site (dySpacing N k) (nk k)
  have hwa : ∀ k i, |w k i| ≤ dySpacing N k := by
    intro k i
    have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
    have h1 := Int.floor_le (v i / dySpacing N k)
    have h2 := Int.lt_floor_add_one (v i / dySpacing N k)
    have e : w k i = v i - dySpacing N k * ((⌊v i / dySpacing N k⌋ : ℤ) : ℝ) := rfl
    rw [e, abs_le]
    have h1' := (le_div_iff₀ ha).mp h1
    have h2' := (div_lt_iff₀ ha).mp h2
    constructor <;> nlinarith
  set n := Fintype.card ι with hn
  set c0 : ℝ := ((2 * n).factorial : ℝ) * (Real.exp C * C) with hc0
  have hlim : Tendsto (fun k => ∑ T ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
      (1 + n * c0) * ∏ i, (if i ∈ T then (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k)
        * msPsize t γ γP c s (F i).1 else msTsize (F i).2 * msPsize t γ γP c s (F i).1))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ T ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        (1 + n * c0) * ∏ i, (if i ∈ T then 0 else msTsize (F i).2 * msPsize t γ γP c s (F i).1) := by
      symm
      refine Finset.sum_eq_zero fun T hT => ?_
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (if_pos hi))
    rw [h0]
    refine tendsto_finsetSum _ fun T _ => (tendsto_finsetProd _ fun i _ => ?_).const_mul _
    by_cases hi : i ∈ T
    · simp only [if_pos hi]
      have h1 := ((wD_tendsto (F i).2 (hF i) w hwa).add (tendsto_dySpacing N)).mul_const
        (msPsize t γ γP c s (F i).1)
      rwa [add_zero, zero_mul] at h1
    · simp only [if_neg hi]
      exact tendsto_const_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hS, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hw1 : ∀ i, |w k i| ≤ 1 := fun i => (hwa k i).trans hk1.le
  rw [Real.norm_eq_abs, msLat_translate_lat Wf c k s F v (nk k)]
  unfold msLat
  simp only [translateD]
  have hP0 : ∀ i, 0 ≤ stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := fun i =>
    (stateK (NeZero.ne N) k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]
      exact (even_two_mul n).pow_nonneg _)
  refine abs_state_prod_sub_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) ((F i).2.translate (w k)))
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k) * msPsize t γ γP c s (F i).1)
    (fun i => msTsize (F i).2 * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun x _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)) ha)
      (msPsize_pos ht γ γP c hs _))
    (fun i => mul_pos (msTsize_pos _) (msPsize_pos ht γ γP c hs _)) (c := c0) (fun i => ?_) (fun i => ?_)
  · obtain ⟨hC1, -⟩ := msFlow_moment Wf ht hs hk (Sum.inl (F i).1) 0
    have hK0 : 0 ≤ c0 := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (by linarith))
    have hW0 : 0 ≤ wD (dySpacing N k) (F i).2 (w k) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (pow_nonneg ha.le 4) (abs_nonneg _)
    have h1 := moment_smear_sub_le (stateK (NeZero.ne N) k) (ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha
      (msProx Wf c k s (F i).1) (F i).2 (hw1) n
    have h2 := msProx_moment Wf c ht hs hk (F i).1 n
    calc stateK (NeZero.ne N) k ((smear (dySpacing N k) (msProx Wf c k s (F i).1) ((F i).2.translate (w k))
          - smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2) ^ (2 * n))
        ≤ wD (dySpacing N k) (F i).2 (w k) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
      _ ≤ (wD (dySpacing N k) (F i).2 (w k) + dySpacing N k) ^ (2 * n)
          * (c0 * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
          mul_le_mul (pow_le_pow_left₀ hW0 (by linarith) _) h2 (hP0 i)
            (pow_nonneg (by linarith) _)
      _ = c0 * ((wD (dySpacing N k) (F i).2 (w k) + dySpacing N k)
          * msPsize t γ γP c s (F i).1) ^ (2 * n) := by rw [mul_pow]; ring
  · obtain ⟨hC1, -⟩ := msFlow_moment Wf ht hs hk (Sum.inl (F i).1) 0
    have hK0 : 0 ≤ c0 := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (by linarith))
    have h1 := moment_smear_le (stateK (NeZero.ne N) k) (ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha hk1.le
      (msProx Wf c k s (F i).1) (F i).2 (tIs (F i).2) n
    have h2 := msProx_moment Wf c ht hs hk (F i).1 n
    have hT0 : 0 ≤ tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4 :=
      mul_nonneg (tIs (F i).2).M_nonneg (by have := (tIs (F i).2).1; positivity)
    have hT : (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n) ≤ msTsize (F i).2 ^ (2 * n) :=
      pow_le_pow_left₀ hT0 (by unfold msTsize; linarith) _
    calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
        ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
      _ ≤ msTsize (F i).2 ^ (2 * n) * (c0 * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
          mul_le_mul hT h2 (hP0 i) (pow_nonneg (msTsize_pos _).le _)
      _ = c0 * (msTsize (F i).2 * msPsize t γ γP c s (F i).1) ^ (2 * n) := by rw [mul_pow]; ring

/-- **`OS1C (CRen N z μ)` from the scale clause and `ExpandR`**, at every `SU(N)`. Module docstring, §3.
DERIVED: `2` the halves; `0` the limit. -/
theorem os1C_of_scale_expand [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAll b Wf)
    (hex : ExpandR Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) :=
    (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand hb hsc hex)
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  intro ι _ _ F hF v
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hFv_c : ContD (fun i => translateD v (F i)) :=
    fun i => (hcont i).comp (continuous_id.sub continuous_const)
  have hFv_s : SepD d (fun i => translateD v (F i)) :=
    fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) v
  have hΔ : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
      - latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set A1 : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hA1
    set A2 : ℝ := Kr ^ Fintype.card ι
      * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2) with hA2
    have hφ : Tendsto (fun s : ℝ => (|A1| + |A2|) * (s / d) ^ ε) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => s / d) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := (𝓝 (0 : ℝ)))).div_const d
      have h2 := (h1.rpow_const (Or.inr hε.le)).const_mul (|A1| + |A2|)
      rw [Real.zero_rpow hε.ne', mul_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    obtain ⟨s, hsQ, hsI⟩ := ((hφ.eventually (gt_mem_nhds (half_pos hη))).and
      (Ioo_mem_nhdsGT (lt_min (mul_pos hθ hd) hb) :
        ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (min (θ * d) b))).exists
    have hs : 0 < s := hsI.1
    have hsθ : s ≤ θ * d := hsI.2.le.trans (min_le_left _ _)
    have hsb : s ≤ b := hsI.2.le.trans (min_le_right _ _)
    have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs.le hd.le) _
    have hS : ∀ᶠ k in atTop, ScaleAt Wf t C γ γP k s := by
      filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hs)] with k hk hks
      exact hk s hks.le hsb
    have hmid : Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F)
        atTop (𝓝 0) := msLat_translate_sub_tendsto Wf c ht hs hS F hcont v
    filter_upwards [hE ι F d hd hcont hsep s hs hsθ, hE ι _ d hd hFv_c hFv_s s hs hsθ,
      (Metric.tendsto_nhds.mp hmid) (η / 2) (half_pos hη)] with k h1 h2 h3
    have h1' : |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ |A1| * (s / d) ^ ε := by
      refine h1.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
          = A1 * (s / d) ^ ε := by rw [hA1]; ring
        _ ≤ |A1| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h2' : |latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
        - msLat Wf c k s (fun i => translateD v (F i))| ≤ |A2| * (s / d) ^ ε := by
      refine h2.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε
            * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2)
          = A2 * (s / d) ^ ε := by rw [hA2]; ring
        _ ≤ |A2| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h3' : |msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F| < η / 2 := by
      rw [Real.dist_eq, sub_zero] at h3
      exact h3
    have hsQ' : (|A1| + |A2|) * (s / d) ^ ε < η / 2 := hsQ
    have hsQ'' : |A1| * (s / d) ^ ε + |A2| * (s / d) ^ ε < η / 2 := by rw [← add_mul]; exact hsQ'
    rw [Real.dist_eq, sub_zero]
    obtain ⟨a1l, a1r⟩ := abs_le.mp h1'
    obtain ⟨a2l, a2r⟩ := abs_le.mp h2'
    obtain ⟨a3l, a3r⟩ := abs_lt.mp h3'
    rw [abs_lt]
    constructor <;> linarith
  have h := (hconv ι F ⟨hcont, d, hd, hsep⟩).add (hΔ.mono_left ultra_le)
  rw [add_zero] at h
  refine h.congr fun k => ?_
  ring

/-- **`OS1C (CRen 2 z μ)` from `MultiScaleAllRen`**, with no added hypothesis. -/
theorem os1C_of_ren_all {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : MultiScaleAllRen W z μ) : OS1C h2N (CRen 2 z μ) := by
  obtain ⟨b, Wf, c, H⟩ := h
  exact os1C_of_scale_expand H.b_pos H.scale H.expand

/-! ## 4. `OS0C` -/

/-- **The coefficient bound**: finite index sets `S i`, `Kᵢ`, `γcᵢ` with, at every `0 < s ≤ 1`,
`supp c(i, s) ⊆ S i` and `|c_{ij}(s)| ≤ Kᵢ s^{d_j} / s^{d_i} (1 + |log s|)^{γcᵢ}`. A clause on the
expansion coefficients only; the constants depend on the composite `i`, since anomalous dimensions
grow with operator dimension. `c = 0` satisfies `CoefBound` but then `expand` forces `contC F = 0`
for every nonempty `F`, contradicting `CompNondeg`; a non-trivial witness needs coefficients scaling
like `s^{d_j−d_i}` with log factors (argued). DERIVED: `1` the top of the scale range; `0` its sign. -/
def CoefBound (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (S : Ix0 → Finset MIx) (K γc : Ix0 → ℝ), ∀ (i : Ix0) (s : ℝ), 0 < s → s ≤ 1 →
    (c i s).support ⊆ S i ∧ ∀ j, |c i s j| ≤ K i * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s

/-- **`MultiScaleAllRen` with the coefficient bound** on the same coefficients. -/
def MultiScaleAllRen' (W : ConfFlow 2) (z : Chan → ℕ → ℝ) (μ : OffMix) : Prop :=
  ∃ (b : ℝ) (Wf : ℝ → ConfFlow 2) (c : Ix0 → ℝ → (MIx →₀ ℝ)),
    MultiScaleAllRenAt W z μ b Wf c ∧ CoefBound c

theorem multiScaleAllRen_of' {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : MultiScaleAllRen' W z μ) : MultiScaleAllRen W z μ := by
  obtain ⟨b, Wf, c, H, -⟩ := h
  exact ⟨b, Wf, c, H⟩

/-- The log exponent of an index: `γ i` for a monomial, `γP` for the plaquette class. -/
def gJ (γ : Ix0 → ℝ) (γP : ℝ) : MIx → ℝ
  | Sum.inl i => γ i
  | Sum.inr _ => γP

theorem msMu_eq (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (j : MIx) (s : ℝ) :
    msMu t γ γP j s = t * s ^ mDim j / afLog (gJ γ γP j) s := by
  cases j <;> rfl

/-- **`(1 + |log s|)^g ≤ (s⁻¹)^{g⁺}` on `0 < s ≤ 1`** (`log(s⁻¹) ≤ s⁻¹ − 1`). DERIVED: `1` the floor and
the top of the range; `0` the positive part. -/
theorem afLog_le_inv_rpow {g s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : afLog g s ≤ s⁻¹ ^ max g 0 := by
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hL1 : 1 ≤ 1 + |Real.log s| := by linarith [abs_nonneg (Real.log s)]
  have hLs : 1 + |Real.log s| ≤ s⁻¹ := by
    rw [abs_of_nonpos hlog]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    rw [Real.log_inv] at h
    linarith
  unfold afLog
  rcases le_total 0 g with hg | hg
  · rw [max_eq_left hg]
    exact Real.rpow_le_rpow (by linarith) hLs hg
  · rw [max_eq_right hg, Real.rpow_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1 hg

/-- **The exponent of a composite**: `κᵢ = dᵢ + γcᵢ⁺ + ∑_{j ∈ S i} γ_j⁺`. -/
def kap (γ : Ix0 → ℝ) (γP : ℝ) (γc : Ix0 → ℝ) (S : Ix0 → Finset MIx) (i : Ix0) : ℝ :=
  (cdim i.1 : ℝ) + max (γc i) 0 + ∑ j ∈ S i, max (gJ γ γP j) 0

theorem kap_nonneg (γ : Ix0 → ℝ) (γP : ℝ) (γc : Ix0 → ℝ) (S : Ix0 → Finset MIx) (i : Ix0) :
    0 ≤ kap γ γP γc S i :=
  add_nonneg (add_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
    (Finset.sum_nonneg fun _ _ => le_max_right _ _)

/-- **One term of `msPsize` under the coefficient bound**: `|c_{ij}(s)| / μ_j(s) ≤ (Kᵢ⁺/t) (s⁻¹)^{κᵢ}`
for `j ∈ S i`, `0 < s ≤ 1`. DERIVED: `1` the top of the range; `0` the positive part. -/
theorem coef_term_le {t : ℝ} (ht : 0 < t) (γ : Ix0 → ℝ) (γP : ℝ) {K γc : Ix0 → ℝ}
    {S : Ix0 → Finset MIx} {i : Ix0} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {j : MIx} (hj : j ∈ S i)
    {cij : ℝ} (hc : |cij| ≤ K i * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s) :
    |cij| / msMu t γ γP j s ≤ max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i := by
  have hsj : 0 < s ^ mDim j := pow_pos hs _
  have hsi : 0 < s ^ cdim i.1 := pow_pos hs _
  have hLc := afLog_pos (γc i) s
  have hLj := afLog_pos (gJ γ γP j) s
  have hu : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have hu0 : 0 < s⁻¹ := inv_pos.mpr hs
  have hK : |cij| ≤ max (K i) 0 * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s :=
    hc.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (K i) 0) hsj.le) hsi.le) hLc.le)
  have hK0 : 0 ≤ max (K i) 0 := le_max_right (K i) 0
  have hγc := afLog_le_inv_rpow (g := γc i) hs hs1
  have hγj : afLog (gJ γ γP j) s ≤ s⁻¹ ^ ∑ j' ∈ S i, max (gJ γ γP j') 0 :=
    (afLog_le_inv_rpow hs hs1).trans (Real.rpow_le_rpow_of_exponent_le hu
      (Finset.single_le_sum (f := fun j' => max (gJ γ γP j') 0) (fun _ _ => le_max_right _ _) hj))
  have hpow : s⁻¹ ^ cdim i.1 = s⁻¹ ^ (cdim i.1 : ℝ) := (Real.rpow_natCast _ _).symm
  have e2 : max (K i) 0 * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s * afLog (gJ γ γP j) s
        / (t * s ^ mDim j)
      = max (K i) 0 / t * (s⁻¹ ^ cdim i.1 * (afLog (γc i) s * afLog (gJ γ γP j) s)) := by
    rw [inv_pow]
    field_simp
  calc |cij| / msMu t γ γP j s = |cij| * afLog (gJ γ γP j) s / (t * s ^ mDim j) := by
        rw [msMu_eq, div_div_eq_mul_div]
    _ ≤ max (K i) 0 * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s * afLog (gJ γ γP j) s
          / (t * s ^ mDim j) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hLj.le) (mul_pos ht hsj).le
    _ = max (K i) 0 / t * (s⁻¹ ^ cdim i.1 * (afLog (γc i) s * afLog (gJ γ γP j) s)) := e2
    _ ≤ max (K i) 0 / t * (s⁻¹ ^ (cdim i.1 : ℝ)
          * (s⁻¹ ^ max (γc i) 0 * s⁻¹ ^ ∑ j' ∈ S i, max (gJ γ γP j') 0)) := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul hγc hγj hLj.le (Real.rpow_nonneg hu0.le _)) (pow_nonneg hu0.le _))
          (div_nonneg hK0 ht.le)
    _ = max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i := by
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
        simp only [kap, add_assoc]

/-- **The proxy size under the coefficient bound**: `msPsize(s) ≤ (|S i|² Kᵢ⁺/t + 1) (s⁻¹)^{κᵢ}` on
`0 < s ≤ 1`. DERIVED: `2` the square of the support count; `1` the top of the range and the `+ 1`. -/
theorem msPsize_le {t : ℝ} (ht : 0 < t) (γ : Ix0 → ℝ) (γP : ℝ) (c : Ix0 → ℝ → (MIx →₀ ℝ))
    {S : Ix0 → Finset MIx} {K γc : Ix0 → ℝ}
    (hcb : ∀ (i : Ix0) (s : ℝ), 0 < s → s ≤ 1 →
      (c i s).support ⊆ S i ∧ ∀ j, |c i s j| ≤ K i * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s)
    (i : Ix0) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    msPsize t γ γP c s i
      ≤ (((S i).card : ℝ) ^ 2 * (max (K i) 0 / t) + 1) * s⁻¹ ^ kap γ γP γc S i := by
  obtain ⟨hsub, hc⟩ := hcb i s hs hs1
  have hu1 : 1 ≤ s⁻¹ ^ kap γ γP γc S i :=
    Real.one_le_rpow ((one_le_inv₀ hs).mpr hs1) (kap_nonneg γ γP γc S i)
  have hB : ∑ j ∈ (c i s).support, |c i s j| / msMu t γ γP j s
      ≤ ((S i).card : ℝ) * (max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i) := by
    calc ∑ j ∈ (c i s).support, |c i s j| / msMu t γ γP j s
        ≤ ∑ j ∈ S i, |c i s j| / msMu t γ γP j s :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le)
      _ ≤ ∑ _j ∈ S i, max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i :=
          Finset.sum_le_sum fun j hj => coef_term_le ht γ γP hs hs1 hj (hc j)
      _ = ((S i).card : ℝ) * (max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((c i s).support.card : ℝ) ≤ (S i).card := by exact_mod_cast Finset.card_le_card hsub
  have hB0 : 0 ≤ ∑ j ∈ (c i s).support, |c i s j| / msMu t γ γP j s :=
    Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le
  have hX : 0 ≤ max (K i) 0 / t * s⁻¹ ^ kap γ γP γc S i :=
    mul_nonneg (div_nonneg (le_max_right _ _) ht.le) (by linarith)
  have hm := mul_le_mul hcard hB hB0 (Nat.cast_nonneg _)
  unfold msPsize
  nlinarith

/-- **`1 + n (2n)! e ≤ (1 + e) 8ⁿ (n!)²`** for `e ≥ 0` (`C(2n, n) ≤ 4ⁿ`, `n ≤ 2ⁿ`).
DERIVED: `2`, `4`, `8 = 2 · 4` as stated; `1` the unit. -/
theorem one_add_mul_fact_le (n : ℕ) {e : ℝ} (he : 0 ≤ e) :
    1 + (n : ℝ) * (((2 * n).factorial : ℝ) * e) ≤ (1 + e) * 8 ^ n * (n.factorial : ℝ) ^ 2 := by
  have hc : (2 * n).factorial = (2 * n).choose n * n.factorial * n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    exact this.symm
  have hcb : (2 * n).choose n ≤ 4 ^ n := Nat.centralBinom_le_four_pow n
  have hn : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le
  have h1 : n * (2 * n).factorial ≤ 8 ^ n * n.factorial ^ 2 := by
    rw [hc]
    calc n * ((2 * n).choose n * n.factorial * n.factorial)
        ≤ 2 ^ n * (4 ^ n * n.factorial * n.factorial) := by gcongr
      _ = 8 ^ n * n.factorial ^ 2 := by
          rw [show (8 : ℕ) = 2 * 4 by norm_num, mul_pow]
          ring
  have h2 : 1 ≤ 8 ^ n * n.factorial ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1' : (n : ℝ) * ((2 * n).factorial : ℝ) ≤ 8 ^ n * (n.factorial : ℝ) ^ 2 := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ 8 ^ n * (n.factorial : ℝ) ^ 2 := by exact_mod_cast h2
  have h3 := mul_le_mul_of_nonneg_right h1' he
  nlinarith

/-- **The flowed reading in the `L¹` form**, uniform in the step: under `ScaleAt` at `(k, s)`,
`|msLat| ≤ (1 + n (2n)! e^C C) ∏ᵢ (wS a_k fᵢ + a_k) · msPsize i`. DERIVED: `2` the
even powers. -/
theorem abs_msLat_le_wS [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ} {γ : Ix0 → ℝ}
    {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hS : ScaleAt Wf t C γ γP k s) {ι : Type}
    [Fintype ι] (F : ι → CDatum (CbR N zOne)) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * msPsize t γ γP c s (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => (wS (dySpacing N k) (F i).2 + dySpacing N k) * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (add_pos_of_nonneg_of_pos (wS_nonneg ha _) ha) (msPsize_pos ht γ γP c hs _))
    (fun i => ?_)
  obtain ⟨hC1, -⟩ := msFlow_moment Wf ht hs hS (Sum.inl (F i).1) 0
  have hK0 : 0 ≤ Real.exp C * C := mul_nonneg (Real.exp_pos _).le (by linarith)
  have h1 := moment_smear_wS (stateK (NeZero.ne N) k) (ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha
    (msProx Wf c k s (F i).1) (F i).2 (Fintype.card ι)
  have h2 := msProx_moment Wf c ht hs hS (F i).1 (Fintype.card ι)
  have hW0 := wS_nonneg ha (F i).2
  have hP0 : 0 ≤ stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * Fintype.card ι)) :=
    (stateK (NeZero.ne N) k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]
      exact (even_two_mul _).pow_nonneg _)
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * Fintype.card ι))
      ≤ wS (dySpacing N k) (F i).2 ^ (2 * Fintype.card ι)
        * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * Fintype.card ι)) := h1
    _ ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) ^ (2 * Fintype.card ι)
        * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)
          * msPsize t γ γP c s (F i).1 ^ (2 * Fintype.card ι)) :=
        mul_le_mul (pow_le_pow_left₀ hW0 (by linarith) _) h2 hP0 (pow_nonneg (by linarith) _)
    _ = ((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)
        * ((wS (dySpacing N k) (F i).2 + dySpacing N k) * msPsize t γ γP c s (F i).1)
          ^ (2 * Fintype.card ι) := by rw [mul_pow]; ring

/-- **The continuum reading in the `L¹` form**: under `ScaleAt` at `s` eventually, `ConvC`, and a lattice
remainder `|latC − msLat| ≤ Rm` eventually, `|contC F| ≤ (1 + n (2n)! e^C C) ∏ᵢ ‖fᵢ‖_{L¹} msPsize i + Rm`
(`abs_msLat_le_wS`, `tendsto_wS`). DERIVED: `0` the limit of the spacing. -/
theorem abs_contC_le_of [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s)
    (hS : ∀ᶠ k in atTop, ScaleAt Wf t C γ γP k s) (hconv : ConvC (NeZero.ne N) (CRen N z μ))
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (hF : Adm F) {Rm : ℝ}
    (hrem : ∀ᶠ k in atTop, |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ Rm) :
    |contC (NeZero.ne N) (CRen N z μ) F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, (l1 (F i).2 * msPsize t γ γP c s (F i).1) + Rm := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hlim : Tendsto (fun k =>
      (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * msPsize t γ γP c s (F i).1) + Rm)
      atTop (𝓝 ((1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, (l1 (F i).2 * msPsize t γ γP c s (F i).1) + Rm)) := by
    refine (Tendsto.const_mul _ (tendsto_finsetProd _ fun i _ => ?_)).add_const Rm
    have h1 := ((tendsto_wS (N := N) (F i).2 (hF.1 i)).add (tendsto_dySpacing N)).mul_const
      (msPsize t γ γP c s (F i).1)
    rwa [add_zero] at h1
  have hev : ∀ᶠ k in (ultra : Filter ℕ), |latC (NeZero.ne N) (CRen N z μ) k F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * msPsize t γ γP c s (F i).1) + Rm := by
    refine Filter.Eventually.filter_mono ultra_le ?_
    filter_upwards [hS, hrem] with k hk hr
    have hP := abs_msLat_le_wS Wf c ht hs hk F
    have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F) (msLat Wf c k s F)
    linarith
  exact le_of_tendsto_of_tendsto ((hconv ι F hF).abs) (hlim.mono_left ultra_le) hev

/-- **One factor of the `OS0C` bound**: with `Ps ≤ P (s⁻¹)^κ`, `s = θ' d`, `0 < d ≤ 1`, both the flowed
factor `l · Ps` and the remainder factor `|K_r| d^{−κr} l` are at most `(P θ'^{−κ} + |K_r|) d^{−max(κ, κr)} l`.
DERIVED: `1` the top of `d`; `0` the signs. -/
theorem os0_factor_le {l Ps P κ κr' θ' d Kr s : ℝ} (hl : 0 ≤ l) (hP : 0 < P) (hθ' : 0 < θ')
    (hd : 0 < d) (hd1 : d ≤ 1) (hsd : s = θ' * d) (hPs : Ps ≤ P * s⁻¹ ^ κ) :
    l * Ps ≤ (P * θ'⁻¹ ^ κ + |Kr|) * (d ^ max κ κr')⁻¹ * l ∧
      |Kr| * ((d ^ κr')⁻¹ * l) ≤ (P * θ'⁻¹ ^ κ + |Kr|) * (d ^ max κ κr')⁻¹ * l := by
  have hdinv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).mpr hd1
  have hA0 : 0 ≤ P * θ'⁻¹ ^ κ := mul_nonneg hP.le (Real.rpow_nonneg (inv_nonneg.mpr hθ'.le) _)
  have hB0 : 0 ≤ d⁻¹ ^ κ := Real.rpow_nonneg (inv_nonneg.mpr hd.le) _
  have hdk : d⁻¹ ^ κ ≤ (d ^ max κ κr')⁻¹ := by
    rw [← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow_of_exponent_le hdinv (le_max_left _ _)
  have hdr : (d ^ κr')⁻¹ ≤ (d ^ max κ κr')⁻¹ := by
    rw [← Real.inv_rpow hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow_of_exponent_le hdinv (le_max_right _ _)
  have hsplit : s⁻¹ ^ κ = θ'⁻¹ ^ κ * d⁻¹ ^ κ := by
    rw [hsd, mul_inv, Real.mul_rpow (inv_nonneg.mpr hθ'.le) (inv_nonneg.mpr hd.le)]
  have hM0 : 0 ≤ (d ^ max κ κr')⁻¹ := hB0.trans hdk
  constructor
  · calc l * Ps ≤ l * (P * s⁻¹ ^ κ) := mul_le_mul_of_nonneg_left hPs hl
      _ = l * ((P * θ'⁻¹ ^ κ) * d⁻¹ ^ κ) := by rw [hsplit, mul_assoc]
      _ ≤ l * ((P * θ'⁻¹ ^ κ + |Kr|) * (d ^ max κ κr')⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (le_add_of_nonneg_right (abs_nonneg Kr)) hdk hB0
            (add_nonneg hA0 (abs_nonneg _))) hl
      _ = (P * θ'⁻¹ ^ κ + |Kr|) * (d ^ max κ κr')⁻¹ * l := by ring
  · calc |Kr| * ((d ^ κr')⁻¹ * l) ≤ |Kr| * ((d ^ max κ κr')⁻¹ * l) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdr hl) (abs_nonneg _)
      _ ≤ (P * θ'⁻¹ ^ κ + |Kr|) * ((d ^ max κ κr')⁻¹ * l) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA0) (mul_nonneg hM0 hl)
      _ = (P * θ'⁻¹ ^ κ + |Kr|) * (d ^ max κ κr')⁻¹ * l := by ring

/-- **`OS0C (CRen N z μ)` from the scale clause, `ExpandR` and the coefficient bound**, at every `SU(N)`.
Module docstring, §4. DERIVED: `8` and `2` from `one_add_mul_fact_le`; `1` the top of the scale range. -/
theorem os0C_of_scale_expand_coef [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlAll b Wf)
    (hex : ExpandR Wf c z μ) (hcoef : CoefBound c) : OS0C (NeZero.ne N) (CRen N z μ) := by
  obtain ⟨S, K, γc, hcb⟩ := hcoef
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) :=
    (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand hb hsc hex)
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  set θ' : ℝ := min θ (min b 1) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ (lt_min hb one_pos)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'b : θ' ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hθ'1 : θ' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨1 + max (Real.exp C * C) 0 + θ' ^ ε, 8, 2,
    fun i => (((S i).card : ℝ) ^ 2 * (max (K i) 0 / t) + 1) * θ'⁻¹ ^ kap γ γP γc S i + |Kr|,
    fun i => max (kap γ γP γc S i) (κr i), ?_⟩
  intro n F d hd hd1 hcont hsep
  beta_reduce
  have hs : 0 < θ' * d := mul_pos hθ'0 hd
  have hsθ : θ' * d ≤ θ * d := mul_le_mul_of_nonneg_right hθ'θ hd.le
  have hsθ' : θ' * d ≤ θ' := mul_le_of_le_one_right hθ'0.le hd1
  have hsb : θ' * d ≤ b := hsθ'.trans hθ'b
  have hs1 : θ' * d ≤ 1 := hsθ'.trans hθ'1
  have hS : ∀ᶠ k in atTop, ScaleAt Wf t C γ γP k (θ' * d) := by
    filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds hs)] with k hk hks
    exact hk _ hks.le hsb
  have hA := abs_contC_le_of ht hs hS hconv F ⟨hcont, d, hd, hsep⟩
    (hE (Fin n) F d hd hcont hsep (θ' * d) hs hsθ)
  have hsd : θ' * d / d = θ' := mul_div_cancel_right₀ θ' hd.ne'
  rw [Fintype.card_fin, hsd] at hA
  have hl1 : ∀ i, 0 ≤ l1 (F i).2 := fun i => MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hPpos : ∀ i : Ix0, 0 < ((S i).card : ℝ) ^ 2 * (max (K i) 0 / t) + 1 := fun i => by
    have : 0 ≤ ((S i).card : ℝ) ^ 2 * (max (K i) 0 / t) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (le_max_right _ _) ht.le)
    linarith
  have hfac : ∀ i, l1 (F i).2 * msPsize t γ γP c (θ' * d) (F i).1
      ≤ ((((S (F i).1).card : ℝ) ^ 2 * (max (K (F i).1) 0 / t) + 1) * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
      ∧ |Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ ((((S (F i).1).card : ℝ) ^ 2 * (max (K (F i).1) 0 / t) + 1) * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := fun i =>
    os0_factor_le (hl1 i) (hPpos _) hθ'0 hd hd1 rfl (msPsize_le ht γ γP c hcb (F i).1 hs hs1)
  have hθε : 0 ≤ θ' ^ ε := Real.rpow_nonneg hθ'0.le _
  have hZ0 : 0 ≤ ∏ i, ((((S (F i).1).card : ℝ) ^ 2 * (max (K (F i).1) 0 / t) + 1)
      * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
        * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_nonneg fun i _ => (mul_nonneg (abs_nonneg Kr)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))).trans (hfac i).2
  have hPi1 : ∏ i, (l1 (F i).2 * msPsize t γ γP c (θ' * d) (F i).1)
      ≤ ∏ i, ((((S (F i).1).card : ℝ) ^ 2 * (max (K (F i).1) 0 / t) + 1)
        * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
          * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => mul_nonneg (hl1 i) (msPsize_pos ht γ γP c hs _).le)
      (fun i _ => (hfac i).1)
  have hPi10 : 0 ≤ ∏ i, (l1 (F i).2 * msPsize t γ γP c (θ' * d) (F i).1) :=
    Finset.prod_nonneg fun i _ => mul_nonneg (hl1 i) (msPsize_pos ht γ γP c hs _).le
  have hPi2 : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      ≤ ∏ i, ((((S (F i).1).card : ℝ) ^ 2 * (max (K (F i).1) 0 / t) + 1)
        * θ'⁻¹ ^ kap γ γP γc S (F i).1 + |Kr|)
          * (d ^ max (kap γ γP γc S (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))) (fun i _ => (hfac i).2)
  have hrem : Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ θ' ^ ε * ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by
    have hPi : 0 ≤ ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i)
    have hK : Kr ^ n ≤ |Kr| ^ n := (le_abs_self _).trans (abs_pow Kr n).le
    have e : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
        = |Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e]
    calc Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = θ' ^ ε * (Kr ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by ring
      _ ≤ θ' ^ ε * (|Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hPi) hθε
  have hmain1 : 1 + (n : ℝ) * (((2 * n).factorial : ℝ) * (Real.exp C * C))
      ≤ (1 + max (Real.exp C * C) 0) * 8 ^ n * (n.factorial : ℝ) ^ 2 := by
    refine le_trans ?_ (one_add_mul_fact_le n (le_max_right (Real.exp C * C) 0))
    have h0 : (0 : ℝ) ≤ (n : ℝ) * ((2 * n).factorial : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left (le_max_left (Real.exp C * C) 0) h0
    nlinarith
  have h8 : (1 : ℝ) ≤ 8 ^ n * (n.factorial : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ 8 ^ n := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (n.factorial : ℝ) ^ 2 :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
    nlinarith
  have hX : 0 ≤ (1 + max (Real.exp C * C) 0) * 8 ^ n * (n.factorial : ℝ) ^ 2 := by
    have := le_max_right (Real.exp C * C) 0
    positivity
  have hM := mul_le_mul hmain1 hPi1 hPi10 hX
  have hR2 := mul_le_mul_of_nonneg_left hPi2 hθε
  have hR3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hθε) hZ0
  rw [Real.rpow_two]
  linarith

/-- **`OS0C (CRen 2 z μ)` from `MultiScaleAllRen'`** (`os0C_of_scale_expand_coef`). -/
theorem os0C_of_ren_all' {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : MultiScaleAllRen' W z μ) : OS0C h2N (CRen 2 z μ) := by
  obtain ⟨b, Wf, c, H, hcb⟩ := h
  exact os0C_of_scale_expand_coef H.b_pos H.scale H.expand hcb

end MassGap.MultiScaleOS

end

#print axioms MassGap.MultiScaleOS.box_mono
#print axioms MassGap.MultiScaleOS.tsum_lattice_eq
#print axioms MassGap.MultiScaleOS.riemann_nat
#print axioms MassGap.MultiScaleOS.tendsto_riemann
#print axioms MassGap.MultiScaleOS.moment_wsum_le
#print axioms MassGap.MultiScaleOS.moment_smear_wS
#print axioms MassGap.MultiScaleOS.isTest_translate
#print axioms MassGap.MultiScaleOS.moment_smear_sub_le
#print axioms MassGap.MultiScaleOS.tendsto_wS
#print axioms MassGap.MultiScaleOS.wD_tendsto
#print axioms MassGap.MultiScaleOS.abs_state_prod_sub_le
#print axioms MassGap.MultiScaleOS.msLat_translate_lat
#print axioms MassGap.MultiScaleOS.msLat_translate_sub_tendsto
#print axioms MassGap.MultiScaleOS.os1C_of_scale_expand
#print axioms MassGap.MultiScaleOS.os1C_of_ren_all
#print axioms MassGap.MultiScaleOS.multiScaleAllRen_of'
#print axioms MassGap.MultiScaleOS.msMu_eq
#print axioms MassGap.MultiScaleOS.afLog_le_inv_rpow
#print axioms MassGap.MultiScaleOS.kap_nonneg
#print axioms MassGap.MultiScaleOS.coef_term_le
#print axioms MassGap.MultiScaleOS.msPsize_le
#print axioms MassGap.MultiScaleOS.one_add_mul_fact_le
#print axioms MassGap.MultiScaleOS.abs_msLat_le_wS
#print axioms MassGap.MultiScaleOS.abs_contC_le_of
#print axioms MassGap.MultiScaleOS.os0_factor_le
#print axioms MassGap.MultiScaleOS.os0C_of_scale_expand_coef
#print axioms MassGap.MultiScaleOS.os0C_of_ren_all'
