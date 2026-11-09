import Mathlib
import MassGap.StrongAnchor

/-!
# MassGap.BetaAnalytic — the strong end from a uniform zero-free region in complex `β`

`CouplingTower.StrongEnd N` asks: frequently as `β → ∞`, the window coupling `D(β, w) = windowCoupling N β w`
tends to `0` as `w → ∞`. `StrongAnchor.strongAnchor` proves this read on an interval `[0, b)`, `b > 0`. This
module transports the anchor to large `β` along a path in the complex plane, by Vitali's theorem.

## 1. Vitali's theorem, convergence-to-zero form (proved)

`vitali_tendsto_zero`: a family `f w`, holomorphic on a preconnected open `Ω ⊆ ℂ` and bounded on every compact
subset of `Ω` uniformly in `w` (`LocBounded`), that tends to `0` at every point of a set `A ⊆ Ω` accumulating at a
point of `Ω`, tends to `0` at every point of `Ω`. Proof: if not at `z₀`, pass to an ultrafilter on the windows
along which `|f w z₀|` stays above some `ε > 0`. Each `f · z` converges along it (bounded values, compact ball).
The Cauchy estimate gives local equi-Lipschitz bounds (`equicontinuousAt_of_locBounded`); Mathlib's
Arzelà–Ascoli comparison upgrades pointwise to locally uniform convergence; the limit is holomorphic, vanishes on
`A`, hence on `Ω` by the identity theorem, which contradicts `ε ≤ |g z₀|`. `frequently_ofReal_Ioo`: an open real
interval accumulates at each of its points in `ℂ`, so the anchor interval is an admissible `A`.

## 2. The complex extension (a named structure)

`HoloExtensionOf D Ω F`: each `F w` is holomorphic on `Ω` and agrees with `D(β, w)` at every real `β ≥ 0` in
`Ω`. `HoloExtension N` is the case `D = windowCoupling N`. The tree's partition function `RectWilson.ZR` is a real
Bochner integral; its complexification `z ↦ ∫ e^{z S}` and a holomorphic branch of `log` on a zero-free region are
not built here. `HoloExtension` is therefore stated as a structure, and its existence is part of the input below.

## 3. The bridge from `UniformAnalytic` (proved)

`UniformAnalyticOf D`: there are a preconnected open `Ω ⊆ ℂ` containing `(0, ε)` for some `ε > 0` and
containing real points `β → ∞` (frequently), and a `HoloExtensionOf D Ω F` that is `LocBounded` on `Ω`.
`frequently_of_uniformAnalyticOf`: an anchored reading with `UniformAnalyticOf` vanishes frequently at `∞`.
`strongEnd_of_uniformAnalytic`: `UniformAnalytic N → StrongEnd N`, through `StrongAnchor.strongAnchor`.

`UniformAnalytic N` is a named input. It is not proved here, and not proved for `SU(N)` anywhere in the tree.
The definition states only a holomorphic extension of `D`, bounded locally uniformly in `w`, on a connected `Ω`
joining the anchor interval to a sequence of real `β → ∞`. A zero-free region for the Fisher zeros of `Z_{2^w}`
and `Z_{2^{w+1}}`, uniform in the window, is the expected source of such an extension, not part of the
definition. It gives `Vanishes N β` at every real `β ≥ 0` in `Ω`,
so it is likely stronger than `StrongEnd N`. Where the Wilson action has a bulk first-order transition at real
`β_c`, the Fisher zeros pinch the real axis there and are expected to block every corridor; the input is then
expected to fail.

## 4. Load tests (proved)

* `uniformAnalyticOf_zero` (non-vacuity): the zero reading satisfies the input, with `Ω = ℂ`.
* `logisticStall_not_uniformAnalytic`: the CHOSEN analytic stall `D(β, w) = σ(2^w (β − 1))` (`σ` logistic;
  stall onset `1` and height `1` CHOSEN) is anchored on `[0, 1)` and tends to `1` for `β > 1`; it fails
  `UniformAnalyticOf`. Its complex poles `1 ± iπ(2k+1)/2^w` approach the real axis at the onset, which is how
  local boundedness fails; the proof does not compute them, it runs the bridge in reverse.

## What does not follow

* `StrongEnd N` for any `N`: `UniformAnalytic N` is open, and it is not shown to be satisfiable for `SU(N)`. No
  zero-free region for the Wilson partition functions at large `β`, uniform in the volume, is proved in the tree.
* A holomorphic extension of `windowCoupling N · w` itself: the complexified `ZR` and its logarithm are not built.
* Anything about a stall that is not anchored: the bridge transports only the anchor's vanishing read.
* The input is not shown to be weaker than, or equivalent to, `StrongEnd N`.

Namespace `MassGap.BetaAnalytic`.
-/

namespace MassGap.BetaAnalytic

open Filter Topology Set
open MassGap.CouplingTower (windowCoupling StrongEnd)

/-! ## 1. Vitali's theorem -/

section Vitali

/-- **Local boundedness on `Ω`, uniform in the index**: every compact `K ⊆ Ω` carries one bound for all
`f w`. No numeral. -/
def LocBounded (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → ∃ M : ℝ, ∀ w, ∀ z ∈ K, ‖f w z‖ ≤ M

/-- **Local equicontinuity from the Cauchy estimate**: a locally bounded holomorphic family is equicontinuous
at every point of `Ω`. Proof-internal: `3` the radius split (`r = R/3`, so the disc of radius `2r` around the
centre lies in the ball of radius `R`), `2` the doubled radius; `0` the norm floor; `1` the shift that keeps the
Lipschitz constant positive. -/
theorem equicontinuousAt_of_locBounded {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℕ → ℂ → ℂ}
    (hf : ∀ w, DifferentiableOn ℂ (f w) Ω) (hb : LocBounded Ω f) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    EquicontinuousAt f z₀ := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
  set r := R / 3 with hr_def
  have hr : 0 < r := by positivity
  have hK : Metric.closedBall z₀ (2 * r) ⊆ Ω := fun z hz => hRΩ (by
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith)
  obtain ⟨M, hM⟩ := hb _ hK (isCompact_closedBall _ _)
  set C := max M 0 / r with hC_def
  have hC : 0 ≤ C := div_nonneg (le_max_right _ _) hr.le
  have hderiv : ∀ w, ∀ c ∈ Metric.ball z₀ r, ‖deriv (f w) c‖ ≤ C := by
    intro w c hc
    have hsub : Metric.closedBall c r ⊆ Metric.closedBall z₀ (2 * r) := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      rw [Metric.mem_ball] at hc
      linarith [dist_triangle z c z₀]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball c hr.ne']
      exact (hf w).mono (hsub.trans hK)
    · intro z hz
      exact (hM w z (hsub (Metric.sphere_subset_closedBall hz))).trans (le_max_left _ _)
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨min r (ε / (C + 1)), lt_min hr (div_pos hε hC1), fun z hz w => ?_⟩
  have hz' : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_ball]; exact lt_of_lt_of_le hz (min_le_left _ _)
  have hlip : ‖f w z₀ - f w z‖ ≤ C * ‖z₀ - z‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun c hc => (hf w).differentiableAt
        (hΩ.mem_nhds (hRΩ (Metric.ball_subset_ball (by linarith) hc))))
      (hderiv w) (convex_ball z₀ r) hz' (Metric.mem_ball_self hr)
  have h1 : ‖z₀ - z‖ < ε / (C + 1) := by
    rw [← dist_eq_norm, dist_comm]; exact lt_of_lt_of_le hz (min_le_right _ _)
  rw [dist_eq_norm]
  calc ‖f w z₀ - f w z‖ ≤ C * ‖z₀ - z‖ := hlip
    _ ≤ (C + 1) * ‖z₀ - z‖ := by nlinarith [norm_nonneg (z₀ - z)]
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left h1 hC1
    _ = ε := by field_simp

/-- **Vitali's theorem, convergence-to-zero form**: a holomorphic family on a preconnected open `Ω`, locally
bounded uniformly in the index, tending to `0` on a set `A ⊆ Ω` that accumulates at a point of `Ω`, tends to `0`
at every point of `Ω`. DERIVED: `0` the limit; `ε` existential from the failure of convergence. -/
theorem vitali_tendsto_zero {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {f : ℕ → ℂ → ℂ} (hf : ∀ w, DifferentiableOn ℂ (f w) Ω) (hb : LocBounded Ω f)
    {A : Set ℂ} (hAΩ : A ⊆ Ω) (hA : ∀ z ∈ A, Tendsto (fun w => f w z) atTop (𝓝 0))
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) (hacc : ∃ᶠ z in 𝓝[≠] z₁, z ∈ A) :
    ∀ z ∈ Ω, Tendsto (fun w => f w z) atTop (𝓝 0) := by
  intro z₀ hz₀
  by_contra hne
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  set S : Set ℕ := {w | ε ≤ ‖f w z₀‖} with hS_def
  have hfS : ∃ᶠ w in atTop, w ∈ S := hfreq.mono fun w hw => by
    by_contra h
    exact hw (hball (by rw [Metric.mem_ball, dist_zero_right]; exact not_le.mp h))
  haveI : NeBot (atTop ⊓ 𝓟 S) := frequently_iff_neBot.mp hfS
  let U : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 S)
  have hUle : (U : Filter ℕ) ≤ atTop ⊓ 𝓟 S := Ultrafilter.of_le _
  have hUat : (U : Filter ℕ) ≤ atTop := hUle.trans inf_le_left
  have hUS : S ∈ (U : Filter ℕ) := le_principal_iff.mp (hUle.trans inf_le_right)
  have hex : ∀ z ∈ Ω, ∃ a, Tendsto (fun w => f w z) (U : Filter ℕ) (𝓝 a) := by
    intro z hz
    obtain ⟨M, hM⟩ := hb {z} (singleton_subset_iff.mpr hz) isCompact_singleton
    obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) M).ultrafilter_le_nhds'
      (U.map fun w => f w z)
      (Ultrafilter.mem_map.mpr (Filter.univ_mem' fun w => by
        simpa [Metric.mem_closedBall, dist_zero_right] using hM w z rfl))
    exact ⟨a, by rwa [Ultrafilter.coe_map] at ha⟩
  let g : ℂ → ℂ := fun z => limUnder (U : Filter ℕ) (fun w => f w z)
  have hpt : ∀ z ∈ Ω, Tendsto (fun w => f w z) (U : Filter ℕ) (𝓝 (g z)) :=
    fun z hz => tendsto_nhds_limUnder (hex z hz)
  have hloc : TendstoLocallyUniformlyOn f g (U : Filter ℕ) Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo]
    intro K hKΩ hKc
    have heq : EquicontinuousOn f K := fun z hz =>
      (equicontinuousAt_of_locBounded hΩo hf hb (hKΩ hz)).equicontinuousWithinAt K
    have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K})
      (by simpa using hKc) (by simpa using heq) (U : Filter ℕ) g).mpr (by
        rw [tendsto_pi_nhds]
        intro z
        exact hpt z.1 (hKΩ (by simpa using z.2)))
    exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp key) K (mem_singleton K)
  have hdiff : DifferentiableOn ℂ g Ω := hloc.differentiableOn (Eventually.of_forall hf) hΩo
  have hzero : EqOn g 0 Ω :=
    (hdiff.analyticOnNhd hΩo).eqOn_zero_of_preconnected_of_frequently_eq_zero hΩc hz₁
      (hacc.mono fun z hz => tendsto_nhds_unique (hpt z (hAΩ hz)) ((hA z hz).mono_left hUat))
  have hge : ε ≤ ‖g z₀‖ := ge_of_tendsto (hpt z₀ hz₀).norm hUS
  rw [hzero hz₀, Pi.zero_apply, norm_zero] at hge
  linarith

/-- **An open real interval accumulates in `ℂ`**: at each of its points, punctured. No numeral. -/
theorem frequently_ofReal_Ioo {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    ∃ᶠ z in 𝓝[≠] (x : ℂ), z ∈ (fun t : ℝ => (t : ℂ)) '' Ioo a b := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds)
      (eventually_mem_nhdsWithin.mono fun t ht =>
        mem_compl_singleton_iff.mpr (Complex.ofReal_injective.ne ht))
  have hev : ∀ᶠ t in 𝓝[≠] x, t ∈ Ioo a b :=
    eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hax hxb)
  exact ht.frequently (hev.frequently.mono fun t h => ⟨t, h, rfl⟩)

end Vitali

/-! ## 2. The complex extension -/

/-- **A holomorphic extension of a reading** `D(β, w)` to `Ω ⊆ ℂ`: each `F w` is holomorphic on `Ω` and agrees
with `D(·, w)` at every real `β ≥ 0` in `Ω`. DERIVED: `0` the lower end of the couplings. -/
structure HoloExtensionOf (D : ℝ → ℕ → ℝ) (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) : Prop where
  holo : ∀ w, DifferentiableOn ℂ (F w) Ω
  agree : ∀ w (β : ℝ), 0 ≤ β → (β : ℂ) ∈ Ω → F w (β : ℂ) = ((D β w : ℝ) : ℂ)

/-- **The holomorphic extension of the window coupling** `windowCoupling N · w` to `Ω`. A structure, not a
construction: the complexified partition function and its logarithm are not built in the tree. No numeral. -/
def HoloExtension (N : ℕ) (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) : Prop :=
  HoloExtensionOf (fun β w => windowCoupling N β w) Ω F

/-! ## 3. The bridge -/

/-- **Uniform analyticity of a reading** (a named input when applied to the window coupling): a preconnected
open `Ω ⊆ ℂ` containing `(0, ε)`, `ε > 0` existential, and real points `β → ∞` (frequently), with a holomorphic
extension of `D` on `Ω` that is locally bounded uniformly in the window. DERIVED: `0` the lower end. -/
def UniformAnalyticOf (D : ℝ → ℕ → ℝ) : Prop :=
  ∃ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ), IsOpen Ω ∧ IsPreconnected Ω ∧
    (∃ ε > 0, ∀ x : ℝ, 0 < x → x < ε → (x : ℂ) ∈ Ω) ∧
    (∃ᶠ β : ℝ in atTop, (β : ℂ) ∈ Ω) ∧ HoloExtensionOf D Ω F ∧ LocBounded Ω F

/-- **`UniformAnalytic N`, a named input, not proved**: a holomorphic extension of `D`, bounded locally
uniformly in the window, on a connected `Ω` in `ℂ` joining the anchor interval to real `β → ∞`; a zero-free
region for the Fisher zeros, uniform in the window, is its expected source. Likely stronger than `StrongEnd N` (it gives the vanishing read
at every real `β ≥ 0` in `Ω`). Not proved for `SU(N)`; expected to fail for `N` with a bulk first-order
transition, where the zeros pinch the real axis. No numeral. -/
def UniformAnalytic (N : ℕ) : Prop :=
  UniformAnalyticOf (fun β w => windowCoupling N β w)

/-- **An anchored, uniformly analytic reading vanishes frequently at `∞`**. DERIVED: `0` the limit and the lower
end; `2` the midpoint of the anchor interval (any interior point serves). -/
theorem frequently_of_uniformAnalyticOf {D : ℝ → ℕ → ℝ}
    (hanc : ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → Tendsto (D β) atTop (𝓝 0))
    (hU : UniformAnalyticOf D) : ∃ᶠ β in atTop, Tendsto (D β) atTop (𝓝 0) := by
  obtain ⟨b, hb, hanc⟩ := hanc
  obtain ⟨Ω, F, hΩo, hΩc, ⟨ε, hε, hεΩ⟩, hfreq, hE, hbd⟩ := hU
  set e := min ε b with he_def
  have he : 0 < e := lt_min hε hb
  let A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioo 0 e
  have hAΩ : A ⊆ Ω := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    exact hεΩ t h0 (lt_of_lt_of_le h1 (min_le_left _ _))
  have hA : ∀ z ∈ A, Tendsto (fun w => F w z) atTop (𝓝 0) := by
    rintro _ ⟨t, ⟨h0, h1⟩, rfl⟩
    have ht := hanc t h0.le (lt_of_lt_of_le h1 (min_le_right _ _))
    have hagree : (fun w => F w (t : ℂ)) = fun w => ((D t w : ℝ) : ℂ) :=
      funext fun w => hE.agree w t h0.le (hAΩ ⟨t, ⟨h0, h1⟩, rfl⟩)
    rw [hagree]
    have h' := (Complex.continuous_ofReal.tendsto 0).comp ht
    rw [Complex.ofReal_zero] at h'
    exact h'
  have hmid : e / 2 ∈ Ioo 0 e := ⟨half_pos he, half_lt_self he⟩
  have hall := vitali_tendsto_zero hΩo hΩc hE.holo hbd hAΩ hA (hAΩ ⟨e / 2, hmid, rfl⟩)
    (frequently_ofReal_Ioo hmid.1 hmid.2)
  refine (hfreq.and_eventually (eventually_ge_atTop (0 : ℝ))).mono fun β hβ => ?_
  have h := hall _ hβ.1
  have hagree : (fun w => F w (β : ℂ)) = fun w => ((D β w : ℝ) : ℂ) :=
    funext fun w => hE.agree w β hβ.2 hβ.1
  rw [hagree] at h
  have h' := (Complex.continuous_re.tendsto 0).comp h
  simp only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] at h'
  exact h'

/-- **The bridge**: `UniformAnalytic N` gives `StrongEnd N`, through the proved anchor `strongAnchor`.
No numeral. -/
theorem strongEnd_of_uniformAnalytic {N : ℕ} (hN : N ≠ 0) (h : UniformAnalytic N) : StrongEnd N := by
  obtain ⟨b, hb, hanc⟩ := StrongAnchor.strongAnchor hN
  exact frequently_of_uniformAnalyticOf ⟨b, hb, hanc⟩ h

/-! ## 4. Load tests -/

/-- **Non-vacuity**: the zero reading is uniformly analytic, with `Ω = ℂ`. DERIVED: `0` the reading; `1` a
witness width (any positive width serves). -/
theorem uniformAnalyticOf_zero : UniformAnalyticOf (fun _ _ => 0) :=
  ⟨univ, fun _ _ => 0, isOpen_univ, isPreconnected_univ, ⟨1, one_pos, fun _ _ _ => trivial⟩,
    Frequently.of_forall fun _ => trivial,
    ⟨fun _ => differentiableOn_const 0, fun _ _ _ _ => by simp⟩,
    fun _ _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

/-- **The logistic stall**: `D(β, w) = σ(2^w (β − 1)) = (1 + e^{2^w (1 − β)})⁻¹`. CHOSEN: stall onset `1` and
height `1`; `2` the window doubling. -/
noncomputable def logisticStall (β : ℝ) (w : ℕ) : ℝ := (1 + Real.exp (2 ^ w * (1 - β)))⁻¹

/-- **The logistic stall is anchored on `[0, 1)`**. CHOSEN: `1` the onset. DERIVED: `0` the limit; `2` the
doubling. -/
theorem logisticStall_anchor :
    ∀ β : ℝ, 0 ≤ β → β < 1 → Tendsto (logisticStall β) atTop (𝓝 0) := by
  intro β _ hβ
  have h2 : Tendsto (fun w : ℕ => (2 : ℝ) ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have h3 : Tendsto (fun w : ℕ => (2 : ℝ) ^ w * (1 - β)) atTop atTop :=
    h2.atTop_mul_const (by linarith)
  have h4 : Tendsto (fun w : ℕ => 1 + Real.exp ((2 : ℝ) ^ w * (1 - β))) atTop atTop :=
    tendsto_atTop_mono (fun w => le_add_of_nonneg_left zero_le_one) (Real.tendsto_exp_atTop.comp h3)
  exact tendsto_inv_atTop_zero.comp h4

/-- **The logistic stall stalls above the onset**: it tends to `1` for `β > 1`. CHOSEN: `1` the onset and the
height. DERIVED: `0` the limit of the exponential; `2` the doubling. -/
theorem logisticStall_one {β : ℝ} (hβ : 1 < β) : Tendsto (logisticStall β) atTop (𝓝 1) := by
  have h2 : Tendsto (fun w : ℕ => (2 : ℝ) ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have h3 : Tendsto (fun w : ℕ => (2 : ℝ) ^ w * (1 - β)) atTop atBot :=
    h2.atTop_mul_const_of_neg (by linarith)
  have h4 := (tendsto_const_nhds (x := (1 : ℝ))).add (Real.tendsto_exp_atBot.comp h3)
  have h5 := h4.inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have e : logisticStall β = fun x : ℕ => (1 + Real.exp (2 ^ x * (1 - β)))⁻¹ := rfl
  rw [e]
  simpa using h5

/-- **Load test: the logistic stall is not uniformly analytic**. It is anchored, so if it were uniformly analytic
the bridge would make it vanish frequently at `∞`; it tends to `1` above the onset. CHOSEN: `1` the onset.
DERIVED: `0` the limit. -/
theorem logisticStall_not_uniformAnalytic : ¬ UniformAnalyticOf logisticStall := by
  intro h
  have hf := frequently_of_uniformAnalyticOf ⟨1, one_pos, logisticStall_anchor⟩ h
  have hev : ∀ᶠ β in atTop, ¬ Tendsto (logisticStall β) atTop (𝓝 0) :=
    (eventually_gt_atTop (1 : ℝ)).mono fun β hβ h0 => by
      have := tendsto_nhds_unique h0 (logisticStall_one hβ)
      norm_num at this
  obtain ⟨β, h1, h2⟩ := (hf.and_eventually hev).exists
  exact h2 h1

end MassGap.BetaAnalytic

#print axioms MassGap.BetaAnalytic.equicontinuousAt_of_locBounded
#print axioms MassGap.BetaAnalytic.vitali_tendsto_zero
#print axioms MassGap.BetaAnalytic.frequently_ofReal_Ioo
#print axioms MassGap.BetaAnalytic.frequently_of_uniformAnalyticOf
#print axioms MassGap.BetaAnalytic.strongEnd_of_uniformAnalytic
#print axioms MassGap.BetaAnalytic.uniformAnalyticOf_zero
#print axioms MassGap.BetaAnalytic.logisticStall_anchor
#print axioms MassGap.BetaAnalytic.logisticStall_one
#print axioms MassGap.BetaAnalytic.logisticStall_not_uniformAnalytic
