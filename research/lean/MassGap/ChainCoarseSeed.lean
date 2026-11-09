import Mathlib
import MassGap.HolderBondMoving
import MassGap.ConvolutionTransfer

/-!
# MassGap.ChainCoarseSeed — the chain's coarse lattices carry the seed; one comparison remains

The flat Migdal–Kadanoff chain from the Wilson weight is bundled as `WilsonChain β`. This module
reads what that gives on a coarse lattice gauge theory whose plaquette weight is the chain's `W_k`,
and states the one comparison that would carry it to the Wilson measure.

## Admissible weights are near-constant

A weight admissible at flat time `c` (`ConvolutionTransfer.FlatAdmissible`) is non-decreasing in
`t = cos ψ` on `[−1, 1]` and LR-wider than `e^{−ψ²/4c}`. So on `[−1, 1]`

    U(1) e^{−π²/4c} ≤ U(t) ≤ U(1)                       (admissible_ge, admissible_le_one)

and `−log U` oscillates by at most `π²/4c` (`chainField_le_add`).

## Fields with small oscillation

For a field `φ : G → ℝ` used on every plaquette (`uniformField`), with `m ≤ φ ≤ M`:
* `zF_bounds`: `e^{−P M} ≤ ZF ≤ e^{−P m}`, `P = d² nᵈ` the plaquettes of the tree's torus
  (`card_tplaq`);
* `abs_fieldDefect_le`: the doubling defect `2ᵈ log ZF(n) − log ZF(2n)` is at most `2ᵈ d² nᵈ (M − m)`
  in absolute value; the bulk cancels exactly because `P(2n) = 2ᵈ P(n)`;
* `fieldDefect_add_const`: a constant shift of the field leaves the defect unchanged, so the chain's
  normalisations do not enter;
* `zF_ge_of_le_add`: a twist supported on `T` plaquettes lowers `ZF` by at most `e^{−|T| (M − m)}`.

`defectWG_eq_fieldDefect`: the tree's `defectWG G d φ β n` is `fieldDefect` at the field `β φ`.

## The coarse seed along the chain (`chain_coarse_defect_le`, `chain_coarse_twist_ge`)

Take the `SU(2)` coordinate `τ g = 1 − wilsonDensity g = ½ Re tr g ∈ [−1, 1]` and the coarse field
`g ↦ −log W_k(τ g)`. Along the Wilson chain (`WilsonChain β`), for every `θ > 0` some `k ≤ (1 + bθ)/(b/2β)`, `b = (1/320) min(1, 4/θ)`,
has, on the side-`n` torus in dimension `d`,

    |coarse defect| ≤ 2ᵈ d² nᵈ π²/(4θ),     coarse twist ratio ≥ e^{−|T| π²/(4θ)}.

No cluster expansion is used: a weight with small oscillation makes every finite torus nearly free.
This is the chain's strong-coupling end, which Tomboulis takes from Ito's theorem (V.1), here proved
for the 4D `SU(2)` chain from `FlatGain`.

## The remaining comparison

`DefectChainComparison β C`: for every `k`, the Wilson defect at side `2^{k+1}` is at most the coarse
defect at side `2` with weight `W_k`. At `k = 0` it holds with equality (`defectChainComparison_zero`).

`OneStepDefectComparison C`: for every `k, j`, the coarse defect with weight `W_k` at side `2^{j+1}` is at
most that with weight `W_{k+1}` at side `2ʲ`; one Migdal–Kadanoff step does not lower the doubling defect.
`defectChainComparison_of_oneStep`: by induction from the equality at `k = 0`, it gives the comparison.

Both forms are false at large `k` for every chain (leading strong-coupling terms, read, not built). The
chain maps the fundamental coefficient `a ↦ 256a⁴`, and the side-`8 → 4` step fails once `a < 0.094`;
the coarse side-`2` defect falls like `a_k⁴`, faster than any Wilson defect at side `2^{k+1}`. The field
`−log W` also puts `W²` on each plaquette of the tree's torus, where the chain is a weight per plaquette.
`ChainFirstCrossing` states the form the seed reads: the half field, on the anti-diagonal of the first
crossing.

The chain's flow and the coarse closure are proved for any `C : WilsonChain β`.
`WilsonChainExists.wilsonChainOf β` constructs such a chain for every `β` (its `C¹`-at-`±1`
regularity included), so the open hypothesis is the comparison. For 4D `U(1)` the same
comparison is false: the abelian chain
also flows to a constant weight (Ito), while the `U(1)` defect stays of order one (massless photon).

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ChainCoarseSeed

open MeasureTheory Set Real Filter MassGap.TorusDoubling MassGap.HolderBondMoving
  MassGap.CompactGauge MassGap.ConvolutionTransfer

/-! ## 1. Admissible weights are near-constant -/

section Bounds

variable {U U' : ℝ → ℝ} {c : ℝ}

/-- An admissible weight is non-decreasing in `t` on `[−1, 1]`. -/
theorem admissible_monotoneOn (hU : FlatAdmissible U U' c) : MonotoneOn U (Icc (-1) 1) := by
  have hd : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt U (U' y) y := fun y hy =>
    (hU.deriv y (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hU.cont.continuousOn ?_ ?_
  · rw [interior_Icc]
    exact fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    rw [(hd y hy).deriv]
    exact hU.mono y hy

theorem admissible_le_one (hU : FlatAdmissible U U' c) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    U t ≤ U 1 :=
  admissible_monotoneOn hU ht ⟨by norm_num, le_rfl⟩ ht.2

theorem admissible_one_pos (hU : FlatAdmissible U U' c) : 0 < U 1 :=
  lt_of_lt_of_le (hU.pos 0 ⟨by norm_num, by norm_num⟩)
    (admissible_le_one hU ⟨by norm_num, by norm_num⟩)

/-- **The floor of an admissible weight**: `U(1) e^{−π²/4c} ≤ U(t)` on `[−1, 1]`. From the LR order
against `e^{−ψ²/4c}` on `(0, π)`, extended to `[0, π]` by continuity. DERIVED: `π` the largest class
angle; `4c` the flat Gaussian's variance scale. -/
theorem admissible_ge (hU : FlatAdmissible U U' c) (hc : 0 < c) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : U 1 * Real.exp (-(π ^ 2 / (4 * c))) ≤ U t := by
  set f : ℝ → ℝ := fun ψ => U (cos ψ) / flatG c ψ with hfdef
  have hfc : Continuous f :=
    (hU.cont.comp continuous_cos).div (by unfold flatG; fun_prop) (fun ψ => (flatG_pos c ψ).ne')
  have hmono : MonotoneOn f (Ioo 0 π) := hU.lrWider hc
  have hf0 : f 0 = U 1 := by simp [f, flatG]
  have h1 : ∀ ψ ∈ Ioo 0 π, f 0 ≤ f ψ := by
    intro ψ hψ
    have hcl : (0 : ℝ) ∈ closure (Ioo 0 ψ) := by
      rw [closure_Ioo hψ.1.ne]; exact ⟨le_rfl, hψ.1.le⟩
    exact ContinuousWithinAt.closure_le (f := f) (g := fun _ => f ψ) hcl hfc.continuousWithinAt
      continuousWithinAt_const (fun y hy => hmono ⟨hy.1, hy.2.trans hψ.2⟩ hψ hy.2.le)
  have h2 : ∀ ψ ∈ Icc 0 π, f 0 ≤ f ψ := by
    intro ψ hψ
    rcases eq_or_lt_of_le hψ.1 with h | h
    · exact le_of_eq (congrArg f h)
    rcases eq_or_lt_of_le hψ.2 with h' | h'
    · have hcl : ψ ∈ closure (Ioo 0 π) := by rw [closure_Ioo pi_pos.ne]; exact hψ
      exact ContinuousWithinAt.closure_le (f := fun _ => f 0) (g := f) hcl continuousWithinAt_const
        hfc.continuousWithinAt (fun y hy => h1 y hy)
    · exact h1 ψ ⟨h, h'⟩
  set ψ := arccos t with hψdef
  have hψ : ψ ∈ Icc 0 π := ⟨arccos_nonneg t, arccos_le_pi t⟩
  have hcos : cos ψ = t := cos_arccos ht.1 ht.2
  have key : U 1 ≤ U t / flatG c ψ := by
    have := h2 ψ hψ
    rw [hf0] at this
    simpa only [f, hcos] using this
  rw [le_div_iff₀ (flatG_pos c ψ)] at key
  have hexp : Real.exp (-(π ^ 2 / (4 * c))) ≤ flatG c ψ := by
    unfold flatG
    refine Real.exp_le_exp.mpr ?_
    have hsq : ψ ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ hψ.1 hψ.2 2
    rw [neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right hsq (by positivity))
  calc U 1 * Real.exp (-(π ^ 2 / (4 * c))) ≤ U 1 * flatG c ψ :=
        mul_le_mul_of_nonneg_left hexp (admissible_one_pos hU).le
    _ ≤ U t := key

theorem admissible_pos (hU : FlatAdmissible U U' c) (hc : 0 < c) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : 0 < U t :=
  lt_of_lt_of_le (mul_pos (admissible_one_pos hU) (Real.exp_pos _)) (admissible_ge hU hc ht)

end Bounds

/-! ## 2. Fields with small oscillation -/

section Fields

variable {G : Type} [Group G] [MeasurableSpace G] {d n : ℕ}

/-- The field that puts `φ` on every plaquette. -/
def uniformField (φ : G → ℝ) : TPlaq d n → G → ℝ := fun _ g => φ g

theorem card_tplaq : Fintype.card (TPlaq d n) = d * d * n ^ d := by
  simp [TPlaq, TSite, Fintype.card_prod, Fintype.card_fin]

/-- The doubling defect of a uniform field: `2ᵈ log ZF(n) − log ZF(2n)`. DERIVED: `2ᵈ` the side-`n`
tori in the side-`2n` torus. -/
noncomputable def fieldDefect (d : ℕ) (φ : G → ℝ) (n : ℕ) (μ : Measure G) : ℝ :=
  2 ^ d * Real.log (ZF μ (uniformField (d := d) (n := n) φ))
    - Real.log (ZF μ (uniformField (d := d) (n := 2 * n) φ))

/-- **The tree's defect is a field defect.** -/
theorem defectWG_eq_fieldDefect [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [BorelSpace G] (φ : G → ℝ) (β : ℝ) (n : ℕ) :
    defectWG G d φ β n = fieldDefect d (fun g => β * φ g) n (probHaar G) := by
  unfold defectWG fieldDefect
  rw [ZT_eq_ZF, ZT_eq_ZF]
  rfl

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_fAct {Φ : TPlaq d n → G → ℝ} (hΦ : ∀ q, Measurable (Φ q)) :
    Measurable (fAct Φ) :=
  Finset.measurable_sum _ fun q _ => (hΦ q).comp (measurable_thol q)

/-- **`ZF` between two constants.** For `m ≤ φ ≤ M`, `e^{−P M} ≤ ZF ≤ e^{−P m}`, `P = d² nᵈ`. -/
theorem zF_bounds (μ : Measure G) [IsProbabilityMeasure μ] {φ : G → ℝ} (hφ : Measurable φ)
    {m M : ℝ} (hm : ∀ g, m ≤ φ g) (hM : ∀ g, φ g ≤ M) :
    Real.exp (-((d * d * n ^ d : ℕ) * M)) ≤ ZF μ (uniformField (d := d) (n := n) φ) ∧
      ZF μ (uniformField (d := d) (n := n) φ) ≤ Real.exp (-((d * d * n ^ d : ℕ) * m)) := by
  set P : ℕ := d * d * n ^ d
  have hS : ∀ U : TLink d n → G, (P : ℝ) * m ≤ fAct (uniformField φ) U ∧
      fAct (uniformField φ) U ≤ (P : ℝ) * M := by
    intro U
    unfold fAct uniformField
    have hc : (Finset.univ : Finset (TPlaq d n)).card = P := by
      rw [Finset.card_univ, card_tplaq]
    constructor
    · calc (P : ℝ) * m = ∑ _q : TPlaq d n, m := by
            rw [Finset.sum_const, hc, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun q _ => hm _
    · calc ∑ q : TPlaq d n, φ (thol q U) ≤ ∑ _q : TPlaq d n, M := Finset.sum_le_sum fun q _ => hM _
        _ = (P : ℝ) * M := by rw [Finset.sum_const, hc, nsmul_eq_mul]
  have hmeas : Measurable (fAct (d := d) (N := n) (uniformField φ)) :=
    measurable_fAct fun _ => hφ
  have hint : Integrable (fun U => Real.exp (-fAct (uniformField (d := d) (n := n) φ) U))
      (Measure.pi fun _ : TLink d n => μ) :=
    integrable_exp_neg hmeas (B := -((P : ℝ) * m)) fun U => by linarith [(hS U).1]
  unfold ZF
  constructor
  · calc Real.exp (-((P : ℝ) * M))
        = ∫ _U, Real.exp (-((P : ℝ) * M)) ∂(Measure.pi fun _ : TLink d n => μ) := by
          rw [integral_const, probReal_univ, one_smul]
      _ ≤ _ := integral_mono (integrable_const _) hint fun U =>
          Real.exp_le_exp.mpr (by linarith [(hS U).2])
  · calc ∫ U, Real.exp (-fAct (uniformField φ) U) ∂(Measure.pi fun _ : TLink d n => μ)
        ≤ ∫ _U, Real.exp (-((P : ℝ) * m)) ∂(Measure.pi fun _ : TLink d n => μ) :=
          integral_mono hint (integrable_const _) fun U =>
            Real.exp_le_exp.mpr (by linarith [(hS U).1])
      _ = Real.exp (-((P : ℝ) * m)) := by rw [integral_const, probReal_univ, one_smul]

/-- **The defect of a field with small oscillation.** For `m ≤ φ ≤ M`,
`|2ᵈ log ZF(n) − log ZF(2n)| ≤ 2ᵈ d² nᵈ (M − m)`. The bulk cancels: `P(2n) = 2ᵈ P(n)`. -/
theorem abs_fieldDefect_le (μ : Measure G) [IsProbabilityMeasure μ] {φ : G → ℝ}
    (hφ : Measurable φ) {m M : ℝ} (hm : ∀ g, m ≤ φ g) (hM : ∀ g, φ g ≤ M) (n : ℕ) :
    |fieldDefect d φ n μ| ≤ 2 ^ d * (d * d * n ^ d : ℕ) * (M - m) := by
  obtain ⟨l1, u1⟩ := zF_bounds (d := d) (n := n) μ hφ hm hM
  obtain ⟨l2, u2⟩ := zF_bounds (d := d) (n := 2 * n) μ hφ hm hM
  have p1 := lt_of_lt_of_le (Real.exp_pos _) l1
  have p2 := lt_of_lt_of_le (Real.exp_pos _) l2
  have L1 := Real.log_le_log (Real.exp_pos _) l1
  have U1 := Real.log_le_log p1 u1
  have L2 := Real.log_le_log (Real.exp_pos _) l2
  have U2 := Real.log_le_log p2 u2
  rw [Real.log_exp] at L1 U1 L2 U2
  have hP : ((d * d * (2 * n) ^ d : ℕ) : ℝ) = 2 ^ d * (d * d * n ^ d : ℕ) := by
    push_cast; rw [mul_pow]; ring
  rw [hP] at L2 U2
  unfold fieldDefect
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left L1 h2d]
  · nlinarith [mul_le_mul_of_nonneg_left U1 h2d]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A constant shift of the field multiplies `ZF` by `e^{−P c}`. -/
theorem zF_add_const (μ : Measure G) [IsProbabilityMeasure μ] (φ : G → ℝ) (c : ℝ) :
    ZF μ (uniformField (d := d) (n := n) (fun g => φ g + c))
      = Real.exp (-((d * d * n ^ d : ℕ) * c)) * ZF μ (uniformField (d := d) (n := n) φ) := by
  unfold ZF
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have h : fAct (uniformField (d := d) (n := n) (fun g => φ g + c)) U
      = fAct (uniformField φ) U + (d * d * n ^ d : ℕ) * c := by
    unfold fAct uniformField
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_tplaq, nsmul_eq_mul]
  simp only
  rw [h, ← Real.exp_add]
  congr 1
  ring

/-- **The defect does not see a constant shift of the field.** -/
theorem fieldDefect_add_const (μ : Measure G) [IsProbabilityMeasure μ] {φ : G → ℝ}
    (hφ : Measurable φ) {m M : ℝ} (hm : ∀ g, m ≤ φ g) (hM : ∀ g, φ g ≤ M) (c : ℝ) (n : ℕ) :
    fieldDefect d (fun g => φ g + c) n μ = fieldDefect d φ n μ := by
  unfold fieldDefect
  rw [zF_add_const, zF_add_const]
  have p1 := lt_of_lt_of_le (Real.exp_pos _) (zF_bounds (d := d) (n := n) μ hφ hm hM).1
  have p2 := lt_of_lt_of_le (Real.exp_pos _) (zF_bounds (d := d) (n := 2 * n) μ hφ hm hM).1
  rw [Real.log_mul (Real.exp_pos _).ne' p1.ne', Real.log_mul (Real.exp_pos _).ne' p2.ne',
    Real.log_exp, Real.log_exp]
  push_cast
  rw [mul_pow]
  ring

/-- **A twist lowers `ZF` by at most its oscillation.** If `Φ' q g ≤ Φ q g + ε_q` everywhere, then
`ZF Φ' ≥ e^{−Σ ε} ZF Φ`. -/
theorem zF_ge_of_le_add (μ : Measure G) [IsProbabilityMeasure μ] {Φ Φ' : TPlaq d n → G → ℝ}
    {K : ℝ} (hb : BddField Φ K) (hb' : BddField Φ' K) (ε : TPlaq d n → ℝ)
    (hle : ∀ q g, Φ' q g ≤ Φ q g + ε q) :
    Real.exp (-∑ q, ε q) * ZF μ Φ ≤ ZF μ Φ' := by
  unfold ZF
  rw [← integral_const_mul]
  have hB : ∀ (Ψ : TPlaq d n → G → ℝ), BddField Ψ K → ∀ U : TLink d n → G,
      -(Fintype.card (TPlaq d n) * K) ≤ fAct Ψ U := by
    intro Ψ hΨ U
    unfold fAct
    have := Finset.abs_sum_le_sum_abs (fun q => Ψ q (thol q U)) Finset.univ
    have h2 : ∑ q, |Ψ q (thol q U)| ≤ ∑ _q : TPlaq d n, K :=
      Finset.sum_le_sum fun q _ => hΨ.2 q _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    linarith [neg_abs_le (∑ q, Ψ q (thol q U))]
  have i1 : Integrable (fun U => Real.exp (-fAct Φ U)) (Measure.pi fun _ : TLink d n => μ) :=
    integrable_exp_neg (measurable_fAct hb.1) (hB Φ hb)
  have i2 : Integrable (fun U => Real.exp (-fAct Φ' U)) (Measure.pi fun _ : TLink d n => μ) :=
    integrable_exp_neg (measurable_fAct hb'.1) (hB Φ' hb')
  refine integral_mono (i1.const_mul _) i2 fun U => ?_
  have h : fAct Φ' U ≤ fAct Φ U + ∑ q, ε q := by
    unfold fAct
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun q _ => hle q _
  simp only
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Fields

/-! ## 3. The chain's coarse field -/

section ChainField

variable {G : Type} [Group G] [MeasurableSpace G] {d n : ℕ}

/-- The coarse field of a weight `W` read through a class coordinate `τ`: `g ↦ −log W(τ g)`. -/
noncomputable def chainField (W : ℝ → ℝ) (τ : G → ℝ) (g : G) : ℝ := -Real.log (W (τ g))

variable {W W' : ℝ → ℝ} {c : ℝ} {τ : G → ℝ}

omit [Group G] [MeasurableSpace G] in
theorem chainField_ge (hW : FlatAdmissible W W' c) (hc : 0 < c)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (g : G) : -Real.log (W 1) ≤ chainField W τ g := by
  unfold chainField
  exact neg_le_neg (Real.log_le_log (admissible_pos hW hc (hτ g)) (admissible_le_one hW (hτ g)))

omit [Group G] [MeasurableSpace G] in
/-- The coarse field oscillates by at most `π²/4c`. -/
theorem chainField_le (hW : FlatAdmissible W W' c) (hc : 0 < c)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (g : G) :
    chainField W τ g ≤ -Real.log (W 1) + π ^ 2 / (4 * c) := by
  unfold chainField
  have h := Real.log_le_log (mul_pos (admissible_one_pos hW) (Real.exp_pos _))
    (admissible_ge hW hc (hτ g))
  rw [Real.log_mul (admissible_one_pos hW).ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

omit [Group G] [MeasurableSpace G] in
theorem chainField_le_add (hW : FlatAdmissible W W' c) (hc : 0 < c)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (g g' : G) :
    chainField W τ g' ≤ chainField W τ g + π ^ 2 / (4 * c) := by
  linarith [chainField_le hW hc hτ g', chainField_ge hW hc hτ g]

omit [Group G] in
theorem measurable_chainField (hW : FlatAdmissible W W' c) (hτm : Measurable τ) :
    Measurable (chainField W τ) :=
  (Real.measurable_log.comp (hW.cont.measurable.comp hτm)).neg

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- **The coarse defect of an admissible weight.** On the side-`n` torus in dimension `d`,
`|fieldDefect| ≤ 2ᵈ d² nᵈ π²/(4c)`. -/
theorem chain_coarse_defect_le (μ : Measure G) [IsProbabilityMeasure μ]
    (hW : FlatAdmissible W W' c) (hc : 0 < c) (hτm : Measurable τ)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    |fieldDefect d (chainField W τ) n μ| ≤ 2 ^ d * (d * d * n ^ d : ℕ) * (π ^ 2 / (4 * c)) := by
  have h := abs_fieldDefect_le (d := d) μ (measurable_chainField hW hτm) (chainField_ge hW hc hτ)
    (chainField_le hW hc hτ) n
  have e : -Real.log (W 1) + π ^ 2 / (4 * c) - -Real.log (W 1) = π ^ 2 / (4 * c) := by ring
  rwa [e] at h

/-- **The coarse twist ratio of an admissible weight.** A twist `ζ` that is `1` off a set `T` of
plaquettes satisfies `ZF(twisted) ≥ e^{−|T| π²/(4c)} ZF(untwisted)`. -/
theorem chain_coarse_twist_ge (μ : Measure G) [IsProbabilityMeasure μ]
    (hW : FlatAdmissible W W' c) (hc : 0 < c) (hτm : Measurable τ)
    (hτ : ∀ g, τ g ∈ Icc (-1 : ℝ) 1) (ζ : TPlaq d n → G) (T : Finset (TPlaq d n))
    (hT : ∀ q ∉ T, ζ q = 1) :
    Real.exp (-(T.card * (π ^ 2 / (4 * c)))) * ZF μ (uniformField (d := d) (n := n) (chainField W τ))
      ≤ ZF μ (fun q g => chainField W τ (ζ q * g)) := by
  set K := |Real.log (W 1)| + π ^ 2 / (4 * c)
  have hbd : ∀ g, |chainField W τ g| ≤ K := fun g => by
    have h1 := chainField_ge hW hc hτ g
    have h2 := chainField_le hW hc hτ g
    have h3 := neg_abs_le (Real.log (W 1))
    have h4 := le_abs_self (Real.log (W 1))
    rw [abs_le]; constructor <;> linarith
  have hm := measurable_chainField hW hτm
  have hb : BddField (uniformField (d := d) (n := n) (chainField W τ)) K :=
    ⟨fun _ => hm, fun _ g => hbd g⟩
  have hb' : BddField (fun (q : TPlaq d n) g => chainField W τ (ζ q * g)) K :=
    ⟨fun q => hm.comp (measurable_const_mul (ζ q)), fun q g => hbd _⟩
  have h := zF_ge_of_le_add μ hb hb' (fun q => if q ∈ T then π ^ 2 / (4 * c) else 0)
    (fun q g => by
      by_cases hq : q ∈ T
      · rw [if_pos hq]; exact chainField_le_add hW hc hτ g _
      · rw [if_neg hq, hT q hq, one_mul, add_zero]; exact le_rfl)
  have hs : ∑ q, (if q ∈ T then π ^ 2 / (4 * c) else 0) = T.card * (π ^ 2 / (4 * c)) := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
  rw [hs] at h
  exact h

end ChainField

/-! ## 4. The Wilson chain and the remaining comparison -/

section Wilson

/-- **The flat Migdal–Kadanoff chain from the Wilson weight**: the data and regularity hypotheses
of the chain. The power step `W_k ↦ μ_k convT(W_k⁴)` and the second
self-convolution `P_k ↦ ν_k convT(P_k)`, with `C¹` regularity on `[−1, 1]`. -/
structure WilsonChain (β : ℝ) where
  W : ℕ → ℝ → ℝ
  W' : ℕ → ℝ → ℝ
  P : ℕ → ℝ → ℝ
  P' : ℕ → ℝ → ℝ
  μ : ℕ → ℝ
  ν : ℕ → ℝ
  hμ : ∀ k, 0 < μ k
  hν : ∀ k, 0 < ν k
  hW0 : W 0 = fun t => Real.exp (β * t)
  hW0' : W' 0 = fun t => β * Real.exp (β * t)
  hWc : ∀ k, Continuous (W (k + 1))
  hWd : ∀ k, ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt (W (k + 1)) (W' (k + 1) y) (Icc (-1) 1) y
  hW'c : ∀ k, ContinuousOn (W' (k + 1)) (Icc (-1) 1)
  hPc : ∀ k, Continuous (P k)
  hPd : ∀ k, ∀ y ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt (P k) (P' k y) (Icc (-1) 1) y
  hP'c : ∀ k, ContinuousOn (P' k) (Icc (-1) 1)
  hPeq : ∀ k, ∀ y ∈ Ioo (-1 : ℝ) 1, P k y = μ k * convT (fun t => W k t ^ 4) y
  hWeq : ∀ k, ∀ y ∈ Ioo (-1 : ℝ) 1, W (k + 1) y = ν k * convT (P k) y

/-- The `SU(2)` class coordinate `½ Re tr g = 1 − wilsonDensity g`. -/
noncomputable def suTau (g : SUN.SU 2) : ℝ := 1 - WilsonAction.wilsonDensity g

theorem suTau_mem (g : SUN.SU 2) : suTau g ∈ Icc (-1 : ℝ) 1 := by
  have h0 := WilsonAction.wilsonDensity_nonneg (N := 2) (by norm_num) g
  have h2 := WilsonAction.wilsonDensity_le_two (N := 2) (by norm_num) g
  unfold suTau
  constructor <;> linarith

theorem measurable_suTau : Measurable suTau :=
  measurable_const.sub WilsonAction.measurable_wilsonDensity

/-- **The remaining comparison.** For every `k`, the 4D `SU(2)` Wilson defect at side `2^{k+1}` is at
most the coarse defect at side `2` of the lattice whose plaquette weight is the chain's `W_k`
(`g ↦ W_k(½ Re tr g)`, Haar on the links). False at large `k` (leading strong-coupling terms): the
coarse defect falls like `a_k⁴` with `log(1/a_k)` growing like `4ᵏ`, the Wilson defect at side `2^{k+1}`
at most exponentially in the side. -/
def DefectChainComparison {β : ℝ} (C : WilsonChain β) : Prop :=
  ∀ k : ℕ, ZoomSelfScale.defectW 2 β (2 ^ (k + 1))
    ≤ fieldDefect 4 (chainField (C.W k) suTau) 2 (probHaar (SUN.SU 2))

/-- `|β φ_W| ≤ 2|β|` on `SU(2)`. -/
theorem abs_beta_wilsonDensity_le (β : ℝ) (g : SUN.SU 2) :
    |β * WilsonAction.wilsonDensity g| ≤ |β| * 2 := by
  have h0 := WilsonAction.wilsonDensity_nonneg (N := 2) (by norm_num) g
  have h2 := WilsonAction.wilsonDensity_le_two (N := 2) (by norm_num) g
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
  rw [abs_le]; constructor <;> linarith

/-- **The Wilson defect is the chain's first coarse defect**, at every side: the chain's first weight
is the Wilson weight, and a constant shift of the field does not move the defect. -/
theorem defectW_eq_chainZero {β : ℝ} (C : WilsonChain β) (n : ℕ) :
    ZoomSelfScale.defectW 2 β n
      = fieldDefect 4 (chainField (C.W 0) suTau) n (probHaar (SUN.SU 2)) := by
  have hfield : chainField (C.W 0) suTau = fun g => β * WilsonAction.wilsonDensity g + (-β) := by
    funext g
    simp only [chainField, C.hW0, Real.log_exp, suTau]
    ring
  rw [hfield, fieldDefect_add_const (d := 4) (φ := fun g => β * WilsonAction.wilsonDensity g)
    (probHaar (SUN.SU 2)) (measurable_const.mul WilsonAction.measurable_wilsonDensity)
    (fun g => (abs_le.mp (abs_beta_wilsonDensity_le β g)).1)
    (fun g => (abs_le.mp (abs_beta_wilsonDensity_le β g)).2) (-β) n,
    ← defectWG_four_eq, defectWG_eq_fieldDefect]

/-- **The comparison at `k = 0` is an equality.** -/
theorem defectChainComparison_zero {β : ℝ} (C : WilsonChain β) :
    ZoomSelfScale.defectW 2 β (2 ^ (0 + 1))
      = fieldDefect 4 (chainField (C.W 0) suTau) 2 (probHaar (SUN.SU 2)) :=
  defectW_eq_chainZero C 2

/-- **The one-step comparison**: one Migdal–Kadanoff step does not lower the doubling defect. For
every `k` and `j`, the coarse lattice with weight `W_k` at side `2^{j+1}` has defect at most that of
the lattice with weight `W_{k+1}` at side `2ʲ`. False at large `k` for every chain (leading
strong-coupling terms: the side-`8 → 4` step fails once the fundamental coefficient of `W_k` is below
`0.094`); `ChainFirstCrossing.FirstCrossingComparison` is the form the seed reads.

DERIVED: `8 = 2³` the side whose halving step fails first; `0.094` a read of the leading
strong-coupling terms of that step (not built in Lean; see the module docstring). -/
def OneStepDefectComparison {β : ℝ} (C : WilsonChain β) : Prop :=
  ∀ k j : ℕ, fieldDefect 4 (chainField (C.W k) suTau) (2 ^ (j + 1)) (probHaar (SUN.SU 2))
    ≤ fieldDefect 4 (chainField (C.W (k + 1)) suTau) (2 ^ j) (probHaar (SUN.SU 2))

/-- **The one-step comparison gives the comparison**, by induction from the equality at `k = 0`. -/
theorem defectChainComparison_of_oneStep {β : ℝ} {C : WilsonChain β}
    (h : OneStepDefectComparison C) : DefectChainComparison C := by
  intro k
  rw [defectW_eq_chainZero C]
  have key : ∀ i, i ≤ k → fieldDefect 4 (chainField (C.W 0) suTau) (2 ^ (k + 1))
      (probHaar (SUN.SU 2))
      ≤ fieldDefect 4 (chainField (C.W i) suTau) (2 ^ (k + 1 - i)) (probHaar (SUN.SU 2)) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).trans ?_
      have e1 : k + 1 - i = (k - i) + 1 := by omega
      have e2 : k + 1 - (i + 1) = k - i := by omega
      rw [e1, e2]
      exact h i (k - i)
  have := key k le_rfl
  rwa [show k + 1 - k = 1 by omega, pow_one] at this

end Wilson

end MassGap.ChainCoarseSeed

#print axioms MassGap.ChainCoarseSeed.admissible_ge
#print axioms MassGap.ChainCoarseSeed.zF_bounds
#print axioms MassGap.ChainCoarseSeed.abs_fieldDefect_le
#print axioms MassGap.ChainCoarseSeed.fieldDefect_add_const
#print axioms MassGap.ChainCoarseSeed.defectWG_eq_fieldDefect
#print axioms MassGap.ChainCoarseSeed.zF_ge_of_le_add
#print axioms MassGap.ChainCoarseSeed.chain_coarse_defect_le
#print axioms MassGap.ChainCoarseSeed.chain_coarse_twist_ge
#print axioms MassGap.ChainCoarseSeed.defectChainComparison_zero
#print axioms MassGap.ChainCoarseSeed.defectW_eq_chainZero
#print axioms MassGap.ChainCoarseSeed.defectChainComparison_of_oneStep
