import Mathlib
import MassGap.SlabMeasure
import MassGap.SliceKernelPower
import MassGap.ExistencePosNonnull

/-!
# MassGap.WilsonSlab — the Doob slab of the Wilson slice transfer: `0 < ratio < 1`, semidefiniteness, the box

`SlabMeasure.perronKT μ T N hN β hβ` is the Perron kernel of the slice transfer `RectTransfer.kT μ T N β`
on `L²` of the product Haar measure `hS μ T N` on the spatial links of one slice, and
`SlabMeasure.readsSlabM_wilson` reads the box gap `−log ratio / a_k` from its Doob slab under the
hypothesis `0 < ratio`. This module proves the open facts about that one-step rate at one finite
volume. It proves no gap and no bound uniform in the volume or the spacing.

## 1. Perron–Jentzsch for a strictly positive kernel (proved)

`X` compact, second countable, Borel, `μ` a probability measure, `k` jointly continuous, symmetric,
`c₀ ≤ k ≤ C` with `c₀ > 0`, `K = kernelCLM k` on `L²(μ)`, `λ₀ = ‖K‖`.

* `eigen_of_form_top`: for any bounded operator, `⟪K g, g⟫ ≥ ‖K‖ ‖g‖²` forces `K g = ‖K‖ g`
  (`‖K g − ‖K‖ g‖² ≤ 0`).
* `abs_eigen`: an eigenvector at `±λ₀` has `K |f| = λ₀ |f|` (`JentzschKT.abs_inner_le_inner_abs`).
* `pp f = (|f| + f)/2`, `mm f = (|f| − f)/2`: nonnegative, with product `0` and difference `f`.
  `int_mul_int_eq_zero`: if `K u = λ₀ u'`, `K v = λ₀ v'`, `u, v ≥ 0` and `u' v' = 0`, then
  `(∫ u)(∫ v) = 0`, because `K u ≥ c₀ ∫ u` everywhere (`lower_ae`).
* `top_simple` (**the top eigenvalue is simple**): `K f = λ₀ f` and `⟪f, e⟫ = 0` for some `e > 0`
  a.e. give `f = 0`. Both `pp f` and `mm f` are top eigenvectors, so one of them vanishes and `f`
  has one sign; then `⟪f, e⟫ = 0` kills it.
* `no_neg` (**`−λ₀` is not an eigenvalue**): `K f = −λ₀ f` gives `f = 0`; here `K` swaps `pp f`
  and `mm f`.
* `exists_contr_lt`: for `e > 0` a.e. with `K e = λ₀ e`, some `r < λ₀` has `‖K h‖ ≤ r ‖h‖` on `e⊥`.
  Otherwise unit `gₙ ⊥ e` have `‖K gₙ‖ → λ₀`, so `‖K² gₙ − λ₀² gₙ‖ → 0`;
  `KernelEigen.exists_subseq` (Arzelà–Ascoli) gives a limit `h ⊥ e`, `‖h‖ = 1`, `K² h = λ₀² h`, and
  `K h + λ₀ h` is a top eigenvector in `e⊥`, hence `0`, so `K h = −λ₀ h`, hence `h = 0`.

## 2. The Doob slab (proved)

For a `PerronKernel` `P`: `U_PD`: `U (PD g) = λ₀⁻¹ K (U g)` (the ground-state map intertwines the Doob
operator with `K/λ₀`). `ratio_le_of_contr`: a rate `r` of `K` on `φ⊥` gives `ratio ≤ r/λ₀`;
`ratio_lt_one_of`. `ratio_pos_of_K_ne`: `ratio > 0` as soon as some `h ⊥ φ` has `K h ≠ 0` (no
semidefiniteness used). `cyc_kD`: the closed `n`-cycle of the Doob density is `λ₀⁻ⁿ` times that of
`k` (the factors of `φ` telescope around the cycle).

## 3. Wilson (proved)

* `ratio_lt_one_wilson`: at `N ≠ 0`, `β ≥ 0`, the one-step rate of the Wilson Doob slab is `< 1`.
* `form_nonneg_wilson` (**semidefiniteness on all of `L²(Haar)`**): `⟪u, K u⟫ ≥ 0` for every
  `u ∈ L²`, gauge invariant or not, at `β ≥ 0`. The image `K v` of every `v ∈ L²` is a continuous
  gauge-invariant function (`KernelEigen.continuous_kernelFun`, `SliceKernelPower.Kf_gaugeInv`), on
  which `SliceKernelDefinite.sliceKernel_form_nonneg` applies (`form_nonneg_range`). For general `u`,
  write `u = y + z` with `y` in the closure of the range of `K` and `z` orthogonal to it; then
  `K z = 0`, `⟪u, K u⟫ = ⟪y, K y⟫`, and the closed set `{⟪x, K x⟫ ≥ 0}` contains the range, hence its
  closure. `ratio_eq_lam1_wilson`: `ratio = λ₁/λ₀` with no hypothesis.
* `continuous_φ`, `gaugeInv_φ`: the Perron eigenfunction is continuous and gauge invariant.
* `ratio_pos_wilson_of`: at `N ≠ 0`, `β > 0`, `ratio > 0` given one continuous gauge-invariant
  function taking two values: then `1` or that function has a nonzero continuous gauge-invariant
  part `h ⊥ φ`, and `SliceKernelDefinite.sliceKernel_form_eq_zero_iff` makes `⟪h, K h⟫ > 0`.
* `exists_nonconst`: at `2 ≤ N` and nonzero transverse extents such a function exists: the
  spatial action `spT` when the extent along `μ + 1` is `≥ 2` (one link along `μ + 2` set to an
  element with positive Wilson density, `ExistencePosNonnull.exists_wilsonDensity_pos`, makes one
  plaquette that element, and `spT` of the identity configuration is `0`), the Wilson density of the
  closed link along `μ + 1` when that extent is `1`. `ratio_pos_wilson`: `ratio > 0` at `2 ≤ N`,
  `β > 0`, all transverse extents nonzero.

## 4. The box of `FixedAperture` (proved)

`boxL m k` is the periodic box with `m 2ᵏ` sites on every side (side `L_m = m a₀` at spacing
`a_k = a₀/2ᵏ`, `FixedAperture`'s convention) and `boxT μ m k = tr (boxL m k) μ` its transverse extents
for time direction `μ`. `ZR_box_eq`: the box partition function is
`ZR (boxL m k) = λ₀^{m 2ᵏ} · cyc (Haar) kD (m 2ᵏ)`, the closed cycle of `m 2ᵏ` steps of the Doob chain
of the very kernel whose slab `readsSlabM_wilson` uses at that `(m, k)`; so the slab of `m 2ᵏ` steps
there spans the whole periodic time extent of the box. `ratio_mem_box`: at `m > 0`, `2 ≤ N`, `β > 0`,
`0 < ratio < 1` for that slab. `readsSlabM_wilson_box`, `fixedApertureFloor_wilson_box`:
`SlabMeasure.readsSlabM_wilson` and `fixedApertureFloor_wilson` at `T = boxT`, with the hypothesis
`0 < ratio` discharged.

Scope. `kT` acts on all of `L²` of the spatial links of one slice, and `form_nonneg_wilson` and
`ratio_lt_one_wilson` are stated there; its range lies in the functions invariant under `gact` by the
axis configurations `TT μ T → SU(N)` of one slice (`Kf_gaugeInv`), a condition that involves no
winding of a closed transverse loop. `ratio = λ₁/λ₀` is the top of the Rayleigh quotient of `K` on
`φ⊥` over that whole space. Not proved here: that `−log ratio / a_k` is the gap of the
partition-function sequence `ZR = Σ λᵢ^{L}` (a spectral expansion of `K`); `ZR_box_eq` is the exact
finite-volume identity between the box partition function and the Doob chain. Nothing here bounds
`ratio` away from `1` uniformly in `k` or `m` (`RelFloorM` stays a hypothesis).

DERIVED (module-wide): `0` the sign of every kernel, form and rate and the orthogonality to `φ`;
`1` the norm of the unit vectors, the rate of the Markov operator on constants and the unit extent
of a closed link; `2` the `L²` exponent, the degree of `λ₀²` in `K² = λ₀²` and the least extent
whose transverse step moves a site, and `2⁻¹` in `(|f| ± f)/2`; `1`, `2` in `μ + 1`, `μ + 2` two
distinct directions transverse to `μ` in `Fin 4`; `4` the constant in the residual
bound `4 λ₀³ ε` (`λ₀² − ‖K g‖² ≤ 2 λ₀ ε` times `λ₀²`, doubled); `n + 2` the index shift that keeps
`λ₀/(n + 2) < λ₀` at `n = 0`.
-/

noncomputable section

namespace MassGap.WilsonSlab

open MeasureTheory Filter Topology MassGap.SlabKernelOperator MassGap.SlabTransferAdjoint
  MassGap.SlabMeasure MassGap.JentzschKT MassGap.KernelEigen MassGap.FixedAperture

/-! ## 1. Perron–Jentzsch for a strictly positive kernel -/

section Top

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A vector at the top of the form is an eigenvector**: `‖K‖ ‖g‖² ≤ ⟪K g, g⟫` gives
`K g = ‖K‖ g`. -/
theorem eigen_of_form_top (K : E →L[ℝ] E) {g : E} (hg : ‖K‖ * ‖g‖ ^ 2 ≤ inner ℝ (K g) g) :
    K g = ‖K‖ • g := by
  have h1 : ‖K g‖ ≤ ‖K‖ * ‖g‖ := K.le_opNorm g
  have h3 : ‖K g‖ ^ 2 ≤ (‖K‖ * ‖g‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 := mul_le_mul_of_nonneg_left hg (norm_nonneg K)
  have h2 : ‖K g - ‖K‖ • g‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, norm_smul, norm_norm, real_inner_smul_right]
    nlinarith [h3, h4]
  have h5 : ‖K g - ‖K‖ • g‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

end Top

section Split

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The positive part `(|f| + f)/2` in `L²`. -/
def pp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ := (2⁻¹ : ℝ) • (|f| + f)

/-- The negative part `(|f| − f)/2` in `L²`. -/
def mm (f : Lp ℝ 2 μ) : Lp ℝ 2 μ := (2⁻¹ : ℝ) • (|f| - f)

theorem coeFn_pp (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, (pp f : X → ℝ) x = 2⁻¹ * (|(f : X → ℝ) x| + (f : X → ℝ) x) := by
  filter_upwards [Lp.coeFn_smul (2⁻¹ : ℝ) (|f| + f), Lp.coeFn_add |f| f, Lp.coeFn_abs f]
    with x h1 h2 h3
  rw [pp, h1, Pi.smul_apply, h2, Pi.add_apply, h3, smul_eq_mul]

theorem coeFn_mm (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, (mm f : X → ℝ) x = 2⁻¹ * (|(f : X → ℝ) x| - (f : X → ℝ) x) := by
  filter_upwards [Lp.coeFn_smul (2⁻¹ : ℝ) (|f| - f), Lp.coeFn_sub |f| f, Lp.coeFn_abs f]
    with x h1 h2 h3
  rw [mm, h1, Pi.smul_apply, h2, Pi.sub_apply, h3, smul_eq_mul]

theorem pp_nonneg (f : Lp ℝ 2 μ) : 0 ≤ᵐ[μ] (pp f : X → ℝ) := by
  filter_upwards [coeFn_pp f] with x hx
  rw [hx]
  have := neg_abs_le ((f : X → ℝ) x)
  exact mul_nonneg (by norm_num) (by linarith)

theorem mm_nonneg (f : Lp ℝ 2 μ) : 0 ≤ᵐ[μ] (mm f : X → ℝ) := by
  filter_upwards [coeFn_mm f] with x hx
  rw [hx]
  have := le_abs_self ((f : X → ℝ) x)
  exact mul_nonneg (by norm_num) (by linarith)

theorem pp_mul_mm (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, (pp f : X → ℝ) x * (mm f : X → ℝ) x = 0 := by
  filter_upwards [coeFn_pp f, coeFn_mm f] with x h1 h2
  rw [h1, h2]
  linear_combination (1 / 4 : ℝ) * sq_abs ((f : X → ℝ) x)

theorem pp_sub_mm (f : Lp ℝ 2 μ) : pp f - mm f = f := by
  rw [pp, mm]; module

variable [IsProbabilityMeasure μ]

/-- A nonnegative `L²` function with integral `0` is `0`. -/
theorem eq_zero_of_integral (u : Lp ℝ 2 μ) (hu : 0 ≤ᵐ[μ] (u : X → ℝ))
    (h : ∫ x, (u : X → ℝ) x ∂μ = 0) : u = 0 := by
  have hz := (integral_eq_zero_iff_of_nonneg_ae hu ((Lp.memLp u).integrable one_le_two)).1 h
  refine Lp.ext ?_
  filter_upwards [hz, Lp.coeFn_zero ℝ 2 μ] with x h1 h2
  rw [h1, h2]

omit [IsProbabilityMeasure μ] in
/-- A nonnegative `L²` function orthogonal to an a.e. positive one is `0`. -/
theorem eq_zero_of_nonneg_inner {e g : Lp ℝ 2 μ} (he : ∀ᵐ x ∂μ, 0 < (e : X → ℝ) x)
    (hg : 0 ≤ᵐ[μ] (g : X → ℝ)) (h : inner ℝ g e = 0) : g = 0 := by
  rw [real_inner_Lp] at h
  have hi : Integrable (fun x => (g : X → ℝ) x * (e : X → ℝ) x) μ :=
    (Lp.memLp g).integrable_mul (Lp.memLp e)
  have hnn : 0 ≤ᵐ[μ] fun x => (g : X → ℝ) x * (e : X → ℝ) x := by
    filter_upwards [hg, he] with x h1 h2
    exact mul_nonneg h1 h2.le
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h
  refine Lp.ext ?_
  filter_upwards [hz, he, Lp.coeFn_zero ℝ 2 μ] with x h1 h2 h3
  rw [h3]
  have h4 : (g : X → ℝ) x * (e : X → ℝ) x = 0 := h1
  exact (mul_eq_zero.1 h4).resolve_right h2.ne'

end Split

section Perron

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hkc : Continuous (Function.uncurry k)) {C : ℝ} (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  (hK : K = kernelCLM k C (kmeas hkc) hC0 hkb μ μ)

include hkc hC0 hkb hK in
/-- An eigenvector of a nonnegative kernel at `±‖K‖` has `|f|` as an eigenvector at `‖K‖`. -/
theorem abs_eigen (hk0 : ∀ x y, 0 ≤ k x y) {f : Lp ℝ 2 μ} {c : ℝ} (hc : |c| = ‖K‖)
    (hf : K f = c • f) : K |f| = ‖K‖ • |f| := by
  subst hK
  apply eigen_of_form_top
  have h1 := abs_inner_le_inner_abs (kmeas hkc) hC0 hkb hk0 f
  rw [hf, real_inner_smul_left, real_inner_self_eq_norm_sq, abs_mul, hc,
    abs_of_nonneg (sq_nonneg _)] at h1
  rw [norm_abs_Lp]
  exact h1

include hkc hC0 hkb hK in
/-- `K u ≥ c₀ ∫ u` almost everywhere for `u ≥ 0`, when `k ≥ c₀`. -/
theorem lower_ae {c₀ : ℝ} (hlow : ∀ x y, c₀ ≤ k x y) {u : Lp ℝ 2 μ}
    (hu : 0 ≤ᵐ[μ] (u : X → ℝ)) :
    ∀ᵐ x ∂μ, c₀ * ∫ y, (u : X → ℝ) y ∂μ ≤ ((K u : Lp ℝ 2 μ) : X → ℝ) x := by
  subst hK
  have hui : Integrable (u : X → ℝ) μ := (Lp.memLp u).integrable one_le_two
  filter_upwards [coeFn_kernelCLM k C (kmeas hkc) hC0 hkb μ μ u] with x hx
  rw [hx]
  unfold kernelFun
  rw [← integral_const_mul]
  refine integral_mono_ae (hui.const_mul c₀) (integrable_row_mul (kmeas hkc) hkb hui x) ?_
  filter_upwards [hu] with y hy
  exact mul_le_mul_of_nonneg_right (hlow x y) hy

include hkc hC0 hkb hK in
/-- **Disjoint supports under a strictly positive kernel.** If `K u = ‖K‖ u'`, `K v = ‖K‖ v'`,
`u, v ≥ 0` and `u' v' = 0`, then `(∫ u)(∫ v) = 0`. -/
theorem int_mul_int_eq_zero {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x y, c₀ ≤ k x y)
    {u v u' v' : Lp ℝ 2 μ} (hu : 0 ≤ᵐ[μ] (u : X → ℝ)) (hv : 0 ≤ᵐ[μ] (v : X → ℝ))
    (hKu : K u = ‖K‖ • u') (hKv : K v = ‖K‖ • v')
    (huv : ∀ᵐ x ∂μ, (u' : X → ℝ) x * (v' : X → ℝ) x = 0) :
    (∫ x, (u : X → ℝ) x ∂μ) * (∫ x, (v : X → ℝ) x ∂μ) = 0 := by
  have h1 := lower_ae hkc hC0 hkb K hK hlow hu
  have h2 := lower_ae hkc hC0 hkb K hK hlow hv
  rw [hKu] at h1
  rw [hKv] at h2
  have hI1 : 0 ≤ ∫ x, (u : X → ℝ) x ∂μ := integral_nonneg_of_ae hu
  have hI2 : 0 ≤ ∫ x, (v : X → ℝ) x ∂μ := integral_nonneg_of_ae hv
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := (h1.and (h2.and (huv.and
    ((Lp.coeFn_smul ‖K‖ u').and (Lp.coeFn_smul ‖K‖ v'))))).exists
  rw [hx4, Pi.smul_apply, smul_eq_mul] at hx1
  rw [hx5, Pi.smul_apply, smul_eq_mul] at hx2
  have hA : 0 ≤ c₀ * ∫ x, (u : X → ℝ) x ∂μ := mul_nonneg hc₀.le hI1
  have hB : 0 ≤ c₀ * ∫ x, (v : X → ℝ) x ∂μ := mul_nonneg hc₀.le hI2
  have h3 := mul_le_mul hx1 hx2 hB (hA.trans hx1)
  have e : ‖K‖ * (u' : X → ℝ) x * (‖K‖ * (v' : X → ℝ) x)
      = ‖K‖ ^ 2 * ((u' : X → ℝ) x * (v' : X → ℝ) x) := by ring
  rw [e, hx3, mul_zero] at h3
  have hp : 0 ≤ (∫ x, (u : X → ℝ) x ∂μ) * (∫ x, (v : X → ℝ) x ∂μ) := mul_nonneg hI1 hI2
  have hc2 : 0 < c₀ ^ 2 := by positivity
  refine le_antisymm ?_ hp
  nlinarith [h3, hc2, hp]

include hkc hC0 hkb hK in
theorem norm_K_pos {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x y, c₀ ≤ k x y) : 0 < ‖K‖ := by
  subst hK
  exact norm_pos_iff.mpr (kernelCLM_ne_zero k C (kmeas hkc) hC0 hkb μ μ hc₀ hlow)

include hkc hC0 hkb hK in
/-- A top eigenvector has one sign: `pp f = 0` or `mm f = 0`. -/
theorem top_one_signed {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x y, c₀ ≤ k x y) {f : Lp ℝ 2 μ}
    (hf : K f = ‖K‖ • f) : pp f = 0 ∨ mm f = 0 := by
  have hk0 : ∀ x y, 0 ≤ k x y := fun x y => hc₀.le.trans (hlow x y)
  have habs : K |f| = ‖K‖ • |f| :=
    abs_eigen hkc hC0 hkb K hK hk0 (abs_of_nonneg (norm_nonneg _)) hf
  have hp : K (pp f) = ‖K‖ • pp f := by
    rw [pp, map_smul, map_add, habs, hf]; module
  have hm : K (mm f) = ‖K‖ • mm f := by
    rw [mm, map_smul, map_sub, habs, hf]; module
  have h := int_mul_int_eq_zero hkc hC0 hkb K hK hc₀ hlow (pp_nonneg f) (mm_nonneg f) hp hm
    (pp_mul_mm f)
  rcases mul_eq_zero.1 h with h1 | h1
  · exact Or.inl (eq_zero_of_integral _ (pp_nonneg f) h1)
  · exact Or.inr (eq_zero_of_integral _ (mm_nonneg f) h1)

include hkc hC0 hkb hK in
/-- **The top eigenvalue is simple**: a top eigenvector orthogonal to an a.e. positive `e` is `0`. -/
theorem top_simple {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x y, c₀ ≤ k x y) {e : Lp ℝ 2 μ}
    (he : ∀ᵐ x ∂μ, 0 < (e : X → ℝ) x) {f : Lp ℝ 2 μ} (hf : K f = ‖K‖ • f)
    (hfe : inner ℝ f e = 0) : f = 0 := by
  have e1 : inner ℝ f e = inner ℝ (pp f) e - inner ℝ (mm f) e := by
    rw [← inner_sub_left, pp_sub_mm]
  rcases top_one_signed hkc hC0 hkb K hK hc₀ hlow hf with h | h
  · have hm0 : mm f = 0 := by
      refine eq_zero_of_nonneg_inner he (mm_nonneg f) ?_
      rw [h, inner_zero_left] at e1
      linarith
    rw [← pp_sub_mm f, h, hm0, sub_zero]
  · have hp0 : pp f = 0 := by
      refine eq_zero_of_nonneg_inner he (pp_nonneg f) ?_
      rw [h, inner_zero_left] at e1
      linarith
    rw [← pp_sub_mm f, h, hp0, sub_zero]

include hkc hC0 hkb hK in
/-- **`−‖K‖` is not an eigenvalue** of a strictly positive kernel. -/
theorem no_neg {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x y, c₀ ≤ k x y) {f : Lp ℝ 2 μ}
    (hf : K f = (-‖K‖) • f) : f = 0 := by
  have hk0 : ∀ x y, 0 ≤ k x y := fun x y => hc₀.le.trans (hlow x y)
  have hl : ‖K‖ ≠ 0 := (norm_K_pos hkc hC0 hkb K hK hc₀ hlow).ne'
  have habs : K |f| = ‖K‖ • |f| :=
    abs_eigen hkc hC0 hkb K hK hk0 (by rw [abs_neg, abs_of_nonneg (norm_nonneg _)]) hf
  have hp : K (pp f) = ‖K‖ • mm f := by
    rw [pp, mm, map_smul, map_add, habs, hf]; module
  have hm : K (mm f) = ‖K‖ • pp f := by
    rw [pp, mm, map_smul, map_sub, habs, hf]; module
  have hprod : ∀ᵐ x ∂μ, (mm f : X → ℝ) x * (pp f : X → ℝ) x = 0 := by
    filter_upwards [pp_mul_mm f] with x hx
    rw [mul_comm]; exact hx
  have h := int_mul_int_eq_zero hkc hC0 hkb K hK hc₀ hlow (pp_nonneg f) (mm_nonneg f) hp hm hprod
  rcases mul_eq_zero.1 h with h1 | h1
  · have hp0 := eq_zero_of_integral _ (pp_nonneg f) h1
    have hm0 : mm f = 0 := by
      rw [hp0, map_zero] at hp
      exact (smul_eq_zero.1 hp.symm).resolve_left hl
    rw [← pp_sub_mm f, hp0, hm0, sub_zero]
  · have hm0 := eq_zero_of_integral _ (mm_nonneg f) h1
    have hp0 : pp f = 0 := by
      rw [hm0, map_zero] at hm
      exact (smul_eq_zero.1 hm.symm).resolve_left hl
    rw [← pp_sub_mm f, hp0, hm0, sub_zero]

include hkc hC0 hkb hK in
/-- **A rate strictly below `‖K‖` on the complement of the Perron vector.** For a strictly positive
symmetric continuous kernel and `e > 0` a.e. with `K e = ‖K‖ e`, some `r < ‖K‖` has `‖K h‖ ≤ r ‖h‖`
for every `h ⊥ e`. -/
theorem exists_contr_lt (hsym : ∀ x y, k x y = k y x) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ x y, c₀ ≤ k x y) {e : Lp ℝ 2 μ} (he : ∀ᵐ x ∂μ, 0 < (e : X → ℝ) x)
    (hKe : K e = ‖K‖ • e) :
    ∃ r, 0 ≤ r ∧ r < ‖K‖ ∧ ∀ h : Lp ℝ 2 μ, inner ℝ h e = 0 → ‖K h‖ ≤ r * ‖h‖ := by
  have hpos : 0 < ‖K‖ := norm_K_pos hkc hC0 hkb K hK hc₀ hlow
  have hsa : IsSelfAdjoint K := by
    rw [hK]; exact isSelfAdjoint_kernelCLM_of_symm k C (kmeas hkc) hC0 hkb μ hsym
  have hsy : ∀ u v, inner ℝ (K u) v = inner ℝ u (K v) := hsa.isSymmetric
  by_contra hne
  push Not at hne
  have hchoose : ∀ n : ℕ, ∃ g : Lp ℝ 2 μ, ‖g‖ = 1 ∧ inner ℝ g e = 0 ∧
      ‖K‖ - ‖K‖ / (n + 2) < ‖K g‖ := by
    intro n
    have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hε : 0 < ‖K‖ / ((n : ℝ) + 2) := by positivity
    have hr0 : 0 ≤ ‖K‖ - ‖K‖ / ((n : ℝ) + 2) := by
      have := div_le_self hpos.le hn2; linarith
    obtain ⟨h, hh, hlt⟩ := hne _ hr0 (by linarith)
    have hh0 : h ≠ 0 := by
      rintro rfl
      simp at hlt
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh0
    refine ⟨(‖h‖⁻¹ : ℝ) • h, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rw [real_inner_smul_left, hh, mul_zero]
    · rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_eq_div, lt_div_iff₀ hn]
      exact hlt
  choose g hg1 hge hgr using hchoose
  have hKg_le : ∀ n, ‖K (g n)‖ ≤ ‖K‖ := fun n => by
    have := K.le_opNorm (g n); rw [hg1 n, mul_one] at this; exact this
  -- the residual `K² g − ‖K‖² g`
  have hres_le : ∀ n : ℕ, ‖K (K (g n)) - (‖K‖ ^ 2) • g n‖ ^ 2
      ≤ 4 * ‖K‖ ^ 3 * (‖K‖ / ((n : ℝ) + 2)) := by
    intro n
    have h3 : ‖K (K (g n)) - (‖K‖ ^ 2) • g n‖ ^ 2
        = ‖K (K (g n))‖ ^ 2 - 2 * ‖K‖ ^ 2 * ‖K (g n)‖ ^ 2 + ‖K‖ ^ 4 := by
      rw [norm_sub_sq_real, real_inner_smul_right, hsy, real_inner_self_eq_norm_sq, norm_smul,
        hg1 n, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖K‖ ^ 2)]
      ring
    rw [h3]
    have hε : 0 < ‖K‖ / ((n : ℝ) + 2) := by positivity
    have h4 : ‖K (K (g n))‖ ≤ ‖K‖ * ‖K (g n)‖ := K.le_opNorm _
    have h5 : ‖K (K (g n))‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖K (g n)‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h4 2
    have ha : ‖K‖ - ‖K (g n)‖ ≤ ‖K‖ / ((n : ℝ) + 2) := by linarith [hgr n]
    have ha0 : 0 ≤ ‖K‖ - ‖K (g n)‖ := by linarith [hKg_le n]
    have hb : ‖K‖ + ‖K (g n)‖ ≤ 2 * ‖K‖ := by linarith [hKg_le n]
    have hb0 : 0 ≤ ‖K‖ + ‖K (g n)‖ := by positivity
    have h6 : (‖K‖ - ‖K (g n)‖) * (‖K‖ + ‖K (g n)‖) ≤ ‖K‖ / ((n : ℝ) + 2) * (2 * ‖K‖) :=
      mul_le_mul ha hb hb0 hε.le
    have h7 : ‖K‖ ^ 2 * ((‖K‖ - ‖K (g n)‖) * (‖K‖ + ‖K (g n)‖))
        ≤ ‖K‖ ^ 2 * (‖K‖ / ((n : ℝ) + 2) * (2 * ‖K‖)) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : 0 < ‖K‖ ^ 3 * (‖K‖ / ((n : ℝ) + 2)) := by positivity
    nlinarith [h5, h7, h8]
  have htol : Tendsto (fun n : ℕ => 4 * ‖K‖ ^ 3 * (‖K‖ / ((n : ℝ) + 2))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ‖K‖ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa using this.const_mul (4 * ‖K‖ ^ 3)
  have hres : Tendsto (fun n => K (K (g n)) - (‖K‖ ^ 2) • g n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => Real.sqrt (4 * ‖K‖ ^ 3 * (‖K‖ / ((n : ℝ) + 2)))) atTop
        (𝓝 0) := by
      have h2 := (Real.continuous_sqrt.tendsto _).comp htol
      simp only [Real.sqrt_zero, Function.comp_def] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => norm_nonneg _)
      (fun n => ?_)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (hres_le n)
  -- the subsequence
  obtain ⟨φ, hφ, v, hv⟩ := exists_subseq hkc hC0 hkb g (fun n => (hg1 n).le)
  rw [← hK] at hv
  have hl2 : ‖K‖ ^ 2 ≠ 0 := by positivity
  have hres' : Tendsto (fun i => K (K (g (φ i))) - (‖K‖ ^ 2) • g (φ i)) atTop (𝓝 0) :=
    hres.comp hφ.tendsto_atTop
  have hKK : Tendsto (fun i => K (K (g (φ i)))) atTop (𝓝 (K v)) :=
    (K.continuous.tendsto v).comp hv
  have hgconv : Tendsto (fun i => g (φ i)) atTop (𝓝 ((‖K‖ ^ 2)⁻¹ • K v)) := by
    have h1 : Tendsto (fun i => K (K (g (φ i))) - (K (K (g (φ i))) - (‖K‖ ^ 2) • g (φ i)))
        atTop (𝓝 (K v - 0)) := hKK.sub hres'
    have h2 : Tendsto (fun i => (‖K‖ ^ 2)⁻¹ •
        (K (K (g (φ i))) - (K (K (g (φ i))) - (‖K‖ ^ 2) • g (φ i))))
        atTop (𝓝 ((‖K‖ ^ 2)⁻¹ • (K v - 0))) := h1.const_smul _
    simp only [sub_sub_cancel, sub_zero, smul_smul, inv_mul_cancel₀ hl2, one_smul] at h2
    exact h2
  set h₀ := (‖K‖ ^ 2)⁻¹ • K v with hh₀
  clear_value h₀
  have hh1 : ‖h₀‖ = 1 := by
    have := (continuous_norm.tendsto h₀).comp hgconv
    simp only [Function.comp_def, hg1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hh0e : inner ℝ h₀ e = 0 := by
    have h1 : Tendsto (fun i => inner ℝ (g (φ i)) e) atTop (𝓝 (inner ℝ h₀ e)) :=
      hgconv.inner tendsto_const_nhds
    have hc : (fun i => inner ℝ (g (φ i)) e) = fun _ => (0 : ℝ) := funext fun i => hge (φ i)
    rw [hc] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hKK0 : K (K h₀) = (‖K‖ ^ 2) • h₀ := by
    have h1 : Tendsto (fun i => K (K (g (φ i)))) atTop (𝓝 (K (K h₀))) :=
      ((K.continuous.comp K.continuous).tendsto h₀).comp hgconv
    have h2 : Tendsto (fun i => (K (K (g (φ i))) - (‖K‖ ^ 2) • g (φ i)) + (‖K‖ ^ 2) • g (φ i))
        atTop (𝓝 (0 + (‖K‖ ^ 2) • h₀)) := hres'.add (hgconv.const_smul _)
    simp only [sub_add_cancel, zero_add] at h2
    exact tendsto_nhds_unique h1 h2
  -- `K h₀ + ‖K‖ h₀` is a top eigenvector orthogonal to `e`
  have hw : K (K h₀ + ‖K‖ • h₀) = ‖K‖ • (K h₀ + ‖K‖ • h₀) := by
    rw [map_add, map_smul, hKK0]; module
  have hwe : inner ℝ (K h₀ + ‖K‖ • h₀) e = 0 := by
    rw [inner_add_left, real_inner_smul_left, hsy, hKe, real_inner_smul_right, hh0e]; ring
  have hw0 := top_simple hkc hC0 hkb K hK hc₀ hlow he hw hwe
  have hneg : K h₀ = (-‖K‖) • h₀ := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hw0
  have := no_neg hkc hC0 hkb K hK hc₀ hlow hneg
  rw [this, norm_zero] at hh1
  exact zero_ne_one hh1

end Perron

/-! ## 2. The Doob slab -/

section Doob

/-- **The ground-state map intertwines**: `U (PD g) = λ₀⁻¹ K (U g)`. -/
theorem U_PD (P : PerronKernel) (g : Lp ℝ 2 P.piD) : P.U (P.PD g) = P.lam0⁻¹ • P.K (P.U g) := by
  refine Lp.ext ?_
  filter_upwards [P.coeFn_U (P.PD g), P.ac.ae_eq (P.PD_density g),
    Lp.coeFn_smul P.lam0⁻¹ (P.K (P.U g)),
    coeFn_kernelCLM P.k P.C P.hk P.hC0 P.hkb P.μ P.μ (P.U g)] with x h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul, PerronKernel.K, h4]
  unfold kernelFun
  have e : ∫ y, P.k x y * ((P.U g : Lp ℝ 2 P.μ) : P.X → ℝ) y ∂P.μ
      = ∫ y, P.k x y * (P.φ y * (g : P.X → ℝ) y) ∂P.μ := by
    refine integral_congr_ae ?_
    filter_upwards [P.coeFn_U g] with y hy
    rw [hy]
  rw [e, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have := (P.φ_pos x).ne'
  have := P.lam0_pos.ne'
  show P.φ x * (P.kD x y * (g : P.X → ℝ) y) = P.lam0⁻¹ * (P.k x y * (P.φ y * (g : P.X → ℝ) y))
  unfold PerronKernel.kD
  field_simp

theorem U_zero (P : PerronKernel) : P.U 0 = 0 :=
  norm_eq_zero.1 (by rw [P.norm_U, norm_zero])

/-- **A rate of `K` on `φ⊥` bounds the Doob rate**: `‖K h‖ ≤ r ‖h‖` for `h ⊥ φ` gives
`ratio ≤ r/λ₀`. -/
theorem ratio_le_of_contr (P : PerronKernel) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ h : Lp ℝ 2 P.μ, inner ℝ h P.phiL = 0 → ‖P.K h‖ ≤ r * ‖h‖) :
    P.ratio ≤ r / P.lam0 := by
  have hl := P.lam0_pos
  show rhoH P.PD (oneLp P.piD) ≤ r / P.lam0
  refine rhoH_le ⟨div_nonneg hr hl.le, fun g hg => ?_⟩
  have hUg : inner ℝ (P.U g) P.phiL = 0 := by
    rw [P.inner_U_phiL, ← inner_oneLp]; exact hg
  have e1 : ‖P.PD g‖ = P.lam0⁻¹ * ‖P.K (P.U g)‖ := by
    rw [← P.norm_U (P.PD g), U_PD, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le)]
  rw [e1]
  calc P.lam0⁻¹ * ‖P.K (P.U g)‖ ≤ P.lam0⁻¹ * (r * ‖g‖) :=
        mul_le_mul_of_nonneg_left (by rw [← P.norm_U g]; exact h _ hUg) (inv_nonneg.2 hl.le)
    _ = r / P.lam0 * ‖g‖ := by ring

/-- **`ratio < 1`** when `K` has a rate `r < λ₀` on `φ⊥`. -/
theorem ratio_lt_one_of (P : PerronKernel)
    (h : ∃ r, 0 ≤ r ∧ r < P.lam0 ∧ ∀ h : Lp ℝ 2 P.μ, inner ℝ h P.phiL = 0 → ‖P.K h‖ ≤ r * ‖h‖) :
    P.ratio < 1 := by
  obtain ⟨r, hr0, hrl, hr⟩ := h
  exact (ratio_le_of_contr P hr0 hr).trans_lt ((div_lt_one P.lam0_pos).2 hrl)

/-- **`ratio > 0`** as soon as `K` does not vanish on `φ⊥`. -/
theorem ratio_pos_of_K_ne (P : PerronKernel) {h : Lp ℝ 2 P.μ} (hh : inner ℝ h P.phiL = 0)
    (hKh : P.K h ≠ 0) : 0 < P.ratio := by
  have hl := P.lam0_pos
  have hg : inner ℝ (P.V h) (oneLp P.piD) = 0 := by
    rw [← P.inner_U, P.U_V h]; exact hh
  have hPD : P.PD (P.V h) ≠ 0 := by
    intro h0
    have h1 := U_PD P (P.V h)
    rw [h0, P.U_V h, U_zero] at h1
    exact hKh ((smul_eq_zero.1 h1.symm).resolve_left (inv_ne_zero hl.ne'))
  by_contra hle
  push Not at hle
  have h0 : P.ratio = 0 := le_antisymm hle P.ratio_nonneg
  have hc := (contrH_rhoH P.PD (oneLp P.piD)).2 (P.V h) hg
  change ‖P.PD (P.V h)‖ ≤ P.ratio * ‖P.V h‖ at hc
  rw [h0, zero_mul] at hc
  exact hPD (norm_eq_zero.1 (le_antisymm hc (norm_nonneg _)))

/-- **The closed cycle of the Doob density**: `cyc μ kD n = λ₀⁻ⁿ cyc μ k n`. -/
theorem cyc_kD (P : PerronKernel) (n : ℕ) :
    MassGap.CyclicKernel.cyc P.μ P.kD n = (P.lam0 ^ n)⁻¹ * MassGap.CyclicKernel.cyc P.μ P.k n := by
  unfold MassGap.CyclicKernel.cyc
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show ∏ t, P.kD (W t) (W (finRotate n t)) = (P.lam0 ^ n)⁻¹ * ∏ t, P.k (W t) (W (finRotate n t))
  unfold PerronKernel.kD
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hrot : ∏ t, P.φ (W (finRotate n t)) = ∏ t, P.φ (W t) :=
    Fintype.prod_equiv (finRotate n) _ _ (fun t => rfl)
  rw [hrot, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hφ : ∏ t, P.φ (W t) ≠ 0 := Finset.prod_ne_zero_iff.2 fun t _ => (P.φ_pos _).ne'
  have hl : P.lam0 ^ n ≠ 0 := pow_ne_zero _ P.lam0_pos.ne'
  field_simp

end Doob

/-! ## Continuous functions in `L²` -/

section Cont

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem memLp_cont (F : C(X, ℝ)) : MemLp (F : X → ℝ) 2 μ :=
  MemLp.of_bound F.continuous.aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall fun x => F.norm_coe_le_norm x)

/-- A continuous function as an element of `L²(μ)`. -/
def cLp (F : C(X, ℝ)) : Lp ℝ 2 μ := (memLp_cont (μ := μ) F).toLp _

theorem coeFn_cLp (F : C(X, ℝ)) : (cLp (μ := μ) F : X → ℝ) =ᵐ[μ] F :=
  (memLp_cont (μ := μ) F).coeFn_toLp

end Cont

/-! ## 3. Wilson -/

section Wilson

open MassGap.RectTransfer MassGap.RectWilson MassGap.SliceKernelDefinite MassGap.SliceKernelPower

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- **The Wilson Doob slab contracts**: at `N ≠ 0`, `β ≥ 0`, the one-step rate is `< 1`. -/
theorem ratio_lt_one_wilson (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    (perronKT μ T N hN β hβ).ratio < 1 := by
  have he : ∀ᵐ x ∂(hS μ T N),
      0 < ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ) x := by
    have hphi : ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ)
        =ᵐ[hS μ T N] (perronKT μ T N hN β hβ).φ := (perronKT μ T N hN β hβ).coeFn_phiL
    filter_upwards [hphi] with x hx
    rw [hx]; exact (perronKT μ T N hN β hβ).φ_pos x
  have key := exists_contr_lt (X := SpT μ T → MassGap.SUN.SU N) (μ := hS μ T N)
    (continuous_kT β) zero_le_one (abs_kT_le hN hβ)
    (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N)) rfl (kT_symm β) (kTmin_pos β) (kT_lower hN hβ) he
    (perronKT μ T N hN β hβ).K_phiL
  exact ratio_lt_one_of (perronKT μ T N hN β hβ) key

/-- The image of the slice transfer as a continuous function. -/
def kimg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (v : Lp ℝ 2 (hS μ T N)) :
    C(SpT μ T → MassGap.SUN.SU N, ℝ) :=
  ⟨kernelFun (kT μ T N β) (hS μ T N) (v : (SpT μ T → MassGap.SUN.SU N) → ℝ),
    continuous_kernelFun (continuous_kT β) zero_le_one (abs_kT_le hN hβ) v⟩

theorem kimg_gaugeInv (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (v : Lp ℝ 2 (hS μ T N)) :
    GaugeInv ⇑(kimg hN hβ v) :=
  Kf_gaugeInv β (v : (SpT μ T → MassGap.SUN.SU N) → ℝ)

/-- **The slice transfer lands in continuous functions**: `K v = kimg v` in `L²`. -/
theorem kernel_eq_cLp (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (v : Lp ℝ 2 (hS μ T N)) :
    kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N) v = cLp (μ := hS μ T N) (kimg hN hβ v) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) v, coeFn_cLp (μ := hS μ T N) (kimg hN hβ v)]
    with x h1 h2
  rw [h1, h2]
  rfl

/-- **The form at a continuous function is the double integral**:
`⟪F, K F⟫ = ∫∫ F(V) F(V') kT(V, V')`. -/
theorem inner_cLp_kernel (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (F : C(SpT μ T → MassGap.SUN.SU N, ℝ)) :
    inner ℝ (cLp (μ := hS μ T N) F)
        (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS μ T N) (hS μ T N) (cLp F))
      = ∫ z, F z.1 * F z.2 * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N)) := by
  rw [form_eq_inner, real_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cLp (μ := hS μ T N) F,
    coeFn_kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N) (cLp F)] with x h1 h2
  rw [h1, h2, Kc_apply]
  congr 1
  unfold kernelFun
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cLp (μ := hS μ T N) F] with y hy
  rw [hy]

/-- The form is nonnegative on the range of the slice transfer, at `β ≥ 0`. -/
theorem form_nonneg_range (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (v : Lp ℝ 2 (hS μ T N)) :
    0 ≤ inner ℝ (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
        (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) v)
      (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
        (hS μ T N) (hS μ T N) (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) v)) := by
  rw [kernel_eq_cLp hN hβ v, inner_cLp_kernel hN hβ]
  exact sliceKernel_form_nonneg hβ (kimg hN hβ v).continuous (kimg_gaugeInv hN hβ v)

/-- **The slice transfer is positive semidefinite on all of `L²(Haar)`** at `β ≥ 0`:
`⟪u, K u⟫ ≥ 0` for every `u`, gauge invariant or not. -/
theorem form_nonneg_wilson (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (u : Lp ℝ 2 (hS μ T N)) :
    0 ≤ inner ℝ u (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
      (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) u) := by
  set K := kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (hS μ T N) (hS μ T N) with hKdef
  have hsy : ∀ a b, inner ℝ (K a) b = inner ℝ a (K b) :=
    (isSelfAdjoint_kernelCLM_of_symm (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
      (abs_kT_le hN hβ) (hS μ T N) (kT_symm β)).isSymmetric
  have hrange : ∀ w, K w ∈
      (LinearMap.range (K : Lp ℝ 2 (hS μ T N) →ₗ[ℝ] Lp ℝ 2 (hS μ T N))).topologicalClosure :=
    fun w => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ w)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := (LinearMap.range (K : Lp ℝ 2 (hS μ T N) →ₗ[ℝ] Lp ℝ 2 (hS μ T N))).topologicalClosure) u
  have hKz : K z = 0 := by
    have h1 : inner ℝ z (K (K z)) = 0 := Submodule.inner_left_of_mem_orthogonal (hrange _) hz
    rw [← hsy, real_inner_self_eq_norm_sq] at h1
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h1)
  rw [map_add, hKz, add_zero, inner_add_left,
    Submodule.inner_left_of_mem_orthogonal (hrange y) hz, add_zero]
  have hcl : IsClosed {x : Lp ℝ 2 (hS μ T N) | 0 ≤ inner ℝ x (K x)} :=
    isClosed_le continuous_const (continuous_id.inner K.continuous)
  have hsub : ((LinearMap.range (K : Lp ℝ 2 (hS μ T N) →ₗ[ℝ] Lp ℝ 2 (hS μ T N))) :
      Set (Lp ℝ 2 (hS μ T N))) ⊆ {x : Lp ℝ 2 (hS μ T N) | 0 ≤ inner ℝ x (K x)} := by
    rintro _ ⟨w, rfl⟩
    exact form_nonneg_range hN hβ w
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
  exact closure_minimal hsub hcl hy

/-- **The Wilson one-step rate is `λ₁/λ₀`**, with no hypothesis (`β ≥ 0`, `N ≠ 0`). -/
theorem ratio_eq_lam1_wilson (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    (perronKT μ T N hN β hβ).ratio
      = (perronKT μ T N hN β hβ).lam1 / ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS μ T N) (hS μ T N)‖ :=
  ratio_eq_wilson hN hβ fun h _ => form_nonneg_wilson hN hβ h

/-- The Perron eigenfunction through the kernel: `φ = λ₀⁻¹ K φ` at every point. -/
theorem φ_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (z : SpT μ T → MassGap.SUN.SU N) :
    (perronKT μ T N hN β hβ).φ z = (perronKT μ T N hN β hβ).lam0⁻¹ *
      kernelFun (kT μ T N β) (hS μ T N)
        ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ) z := by
  have hl := (perronKT μ T N hN β hβ).lam0_pos
  have e : kernelFun (kT μ T N β) (hS μ T N)
      ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ) z
      = ∫ y, kT μ T N β z y * (perronKT μ T N hN β hβ).φ y ∂(hS μ T N) := by
    unfold kernelFun
    refine integral_congr_ae ?_
    have hphi : ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ)
        =ᵐ[hS μ T N] (perronKT μ T N hN β hβ).φ := (perronKT μ T N hN β hβ).coeFn_phiL
    filter_upwards [hphi] with y hy
    rw [hy]
  rw [e, show ∫ y, kT μ T N β z y * (perronKT μ T N hN β hβ).φ y ∂(hS μ T N)
      = (perronKT μ T N hN β hβ).lam0 * (perronKT μ T N hN β hβ).φ z
      from (perronKT μ T N hN β hβ).eig z, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]

/-- **The Perron eigenfunction is continuous.** -/
theorem continuous_φ (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (fun z : SpT μ T → MassGap.SUN.SU N => (perronKT μ T N hN β hβ).φ z) := by
  have e : (fun z : SpT μ T → MassGap.SUN.SU N => (perronKT μ T N hN β hβ).φ z)
      = fun z => (perronKT μ T N hN β hβ).lam0⁻¹ *
      kernelFun (kT μ T N β) (hS μ T N)
        ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ) z :=
    funext (φ_eq hN hβ)
  rw [e]
  exact continuous_const.mul (continuous_kernelFun (μ := hS μ T N) (continuous_kT β) zero_le_one
    (abs_kT_le hN hβ) (perronKT μ T N hN β hβ).phiL)

/-- **The Perron eigenfunction is gauge invariant.** -/
theorem gaugeInv_φ (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : TT μ T → MassGap.SUN.SU N)
    (V : SpT μ T → MassGap.SUN.SU N) :
    (perronKT μ T N hN β hβ).φ (gact g V) = (perronKT μ T N hN β hβ).φ V := by
  rw [φ_eq hN hβ, φ_eq hN hβ]
  have h := Kf_gaugeInv β ((perronKT μ T N hN β hβ).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ) g V
  unfold Kf at h
  unfold kernelFun
  rw [h]

/-- The part `f − c φ` of a continuous `f`, as a continuous function. -/
def projC (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (c : ℝ) (f : C(SpT μ T → MassGap.SUN.SU N, ℝ)) :
    C(SpT μ T → MassGap.SUN.SU N, ℝ) :=
  ⟨fun x => f x - c * (perronKT μ T N hN β hβ).φ x,
    f.continuous.sub (continuous_const.mul (continuous_φ hN hβ))⟩

theorem projC_apply (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (c : ℝ)
    (f : C(SpT μ T → MassGap.SUN.SU N, ℝ)) (x : SpT μ T → MassGap.SUN.SU N) :
    projC hN hβ c f x = f x - c * (perronKT μ T N hN β hβ).φ x := rfl

/-- **A nonzero gauge-invariant part orthogonal to `φ` gives `ratio > 0`**, at `N ≠ 0`, `β > 0`:
for continuous gauge-invariant `f` with `f − (∫ f φ) φ ≠ 0`. -/
theorem ratio_pos_of_proj (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) (f : C(SpT μ T → MassGap.SUN.SU N, ℝ))
    (hf : GaugeInv ⇑f)
    (hne : projC hN hβ.le (∫ x, f x * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N)) f ≠ 0) :
    0 < (perronKT μ T N hN β hβ.le).ratio := by
  set c := ∫ x, f x * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N) with hc
  have hφc := continuous_φ (μ := μ) (T := T) (N := N) hN hβ.le
  have hinv : GaugeInv ⇑(projC hN hβ.le c f) := by
    intro g V
    rw [projC_apply, projC_apply, hf g V, gaugeInv_φ hN hβ.le g V]
  have hphi : ((perronKT μ T N hN β hβ.le).phiL : (SpT μ T → MassGap.SUN.SU N) → ℝ)
      =ᵐ[hS μ T N] (perronKT μ T N hN β hβ.le).φ := (perronKT μ T N hN β hβ.le).coeFn_phiL
  have hsq : ∫ x, (perronKT μ T N hN β hβ.le).φ x ^ 2 ∂(hS μ T N) = 1 :=
    (perronKT μ T N hN β hβ.le).φ_sq
  have horth : inner ℝ (cLp (μ := hS μ T N) (projC hN hβ.le c f))
      (perronKT μ T N hN β hβ.le).phiL = 0 := by
    have e2 : ∫ x, (f x * (perronKT μ T N hN β hβ.le).φ x
        - c * (perronKT μ T N hN β hβ.le).φ x ^ 2) ∂(hS μ T N) = 0 := by
      rw [integral_sub, integral_const_mul, hsq, mul_one, ← hc, sub_self]
      · exact KernelInjective.integrable_of_continuous (f.continuous.mul hφc)
      · exact KernelInjective.integrable_of_continuous (continuous_const.mul (hφc.pow 2))
    rw [real_inner_Lp]
    refine Eq.trans (integral_congr_ae ?_) e2
    filter_upwards [coeFn_cLp (μ := hS μ T N) (projC hN hβ.le c f), hphi] with x h1 h2
    rw [h1, projC_apply]
    exact (congrArg (fun t => (f x - c * (perronKT μ T N hN β hβ.le).φ x) * t) h2).trans
      (by ring)
  have hform : 0 < inner ℝ (cLp (μ := hS μ T N) (projC hN hβ.le c f))
      (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ.le)
        (hS μ T N) (hS μ T N) (cLp (projC hN hβ.le c f))) := by
    rw [inner_cLp_kernel hN hβ.le]
    have h0 := sliceKernel_form_nonneg hβ.le (projC hN hβ.le c f).continuous hinv
    have hne0 : ∫ z, projC hN hβ.le c f z.1 * projC hN hβ.le c f z.2
        * kT μ T N β z.1 z.2 ∂((hS μ T N).prod (hS μ T N)) ≠ 0 := fun h' =>
      hne ((sliceKernel_form_eq_zero_iff hN hβ (projC hN hβ.le c f) hinv).1 h')
    exact lt_of_le_of_ne h0 (Ne.symm hne0)
  exact (perronKT μ T N hN β hβ.le).ratio_pos_of_form_pos horth hform

/-- **`ratio > 0` from one nonconstant gauge-invariant function**, at `N ≠ 0` and `β > 0`. -/
theorem ratio_pos_wilson_of (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (u : C(SpT μ T → MassGap.SUN.SU N, ℝ)) (hu : GaugeInv ⇑u)
    {a b : SpT μ T → MassGap.SUN.SU N} (hab : u a ≠ u b) :
    0 < (perronKT μ T N hN β hβ.le).ratio := by
  have hinv1 : GaugeInv ⇑(1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) := fun _ _ => rfl
  have one_ap : ∀ x, (1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) x = 1 := fun _ => rfl
  by_cases h1 : projC (μ := μ) (T := T) hN hβ.le (∫ x, (1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) x
      * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N)) (1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) = 0
  · by_cases h2 : projC hN hβ.le (∫ x, u x * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N)) u = 0
    · exfalso
      set c1 := ∫ x, (1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) x
        * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N)
      set cu := ∫ x, u x * (perronKT μ T N hN β hβ.le).φ x ∂(hS μ T N)
      have p1 : ∀ x, (1 : C(SpT μ T → MassGap.SUN.SU N, ℝ)) x
          - c1 * (perronKT μ T N hN β hβ.le).φ x = 0 := fun x => DFunLike.congr_fun h1 x
      have p2 : ∀ x, u x - cu * (perronKT μ T N hN β hβ.le).φ x = 0 :=
        fun x => DFunLike.congr_fun h2 x
      have hc1 : c1 ≠ 0 := by
        intro h
        have := p1 a
        rw [h, zero_mul, sub_zero, one_ap] at this
        exact one_ne_zero this
      have pa := p1 a
      have pb := p1 b
      rw [one_ap] at pa pb
      have hφab : (perronKT μ T N hN β hβ.le).φ a = (perronKT μ T N hN β hβ.le).φ b :=
        mul_left_cancel₀ hc1 (by linarith)
      have := p2 a
      rw [hφab] at this
      exact hab (by linarith [p2 b])
    · exact ratio_pos_of_proj hN hβ u hu h2
  · exact ratio_pos_of_proj hN hβ 1 hinv1 h1

/-! ### A nonconstant gauge-invariant function on one slice -/

theorem finRotate_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact Equiv.Perm.mem_support.1 (by rw [support_finRotate]; exact Finset.mem_univ i)

/-- A transverse step along an extent `≥ 2` moves every site. -/
theorem tsh_ne_self {ν : {j : Fin 4 // j ≠ μ}} (hν : 2 ≤ T ν) (y : TT μ T) : tsh μ T ν y ≠ y := by
  intro h
  have h1 := congrFun h ν
  simp only [tsh, Function.update_self] at h1
  exact finRotate_ne hν (y ν) h1

/-- A transverse step along an extent `1` fixes every site. -/
theorem tsh_eq_self {ν : {j : Fin 4 // j ≠ μ}} (hν : T ν = 1) (y : TT μ T) : tsh μ T ν y = y := by
  have h : finRotate (T ν) (y ν) = y ν := by
    have : Subsingleton (Fin (T ν)) := by rw [hν]; infer_instance
    exact Subsingleton.elim _ _
  unfold tsh
  rw [h, Function.update_eq_self]

/-- The plaquette `(a, b, y)` of one slice. -/
def plaqT (V : SpT μ T → MassGap.SUN.SU N) (a b : {j : Fin 4 // j ≠ μ}) (y : TT μ T) : ℝ :=
  MassGap.WilsonAction.wilsonDensity
    (V (a, y) * V (b, tsh μ T a y) * (V (a, tsh μ T b y))⁻¹ * (V (b, y))⁻¹)

theorem spT_eq_plaqT (V : SpT μ T → MassGap.SUN.SU N) :
    spT μ T V = ∑ a, ∑ b, ∑ y, plaqT V a b y := rfl

/-- **A continuous gauge-invariant function of one slice with two values**, at `2 ≤ N` and nonzero
transverse extents: `spT` if the extent along `μ + 1` is `≥ 2`, the Wilson density of one closed
link along `μ + 1` if that extent is `1`. -/
theorem exists_nonconst (hN2 : 2 ≤ N) (hT : ∀ j, T j ≠ 0) :
    ∃ u : C(SpT μ T → MassGap.SUN.SU N, ℝ), GaugeInv ⇑u ∧
      ∃ a b : SpT μ T → MassGap.SUN.SU N, u a ≠ u b := by
  have hN : N ≠ 0 := by omega
  obtain ⟨g, hg⟩ := MassGap.ExistencePosNonnull.exists_wilsonDensity_pos hN2
  have y₀ : TT μ T := fun j => ⟨0, Nat.pos_of_ne_zero (hT j)⟩
  have d1 : ∀ m : Fin 4, m + 1 ≠ m := by decide
  have d2 : ∀ m : Fin 4, m + 2 ≠ m := by decide
  have d3 : ∀ m : Fin 4, m + 1 ≠ m + 2 := by decide
  set ν₀ : {j : Fin 4 // j ≠ μ} := ⟨μ + 1, d1 μ⟩
  set ν₁ : {j : Fin 4 // j ≠ μ} := ⟨μ + 2, d2 μ⟩
  have hν : ν₁ ≠ ν₀ := fun h => d3 μ (congrArg Subtype.val h).symm
  by_cases hbig : 2 ≤ T ν₀
  · -- the spatial action: one link along `ν₁` set to `g`
    refine ⟨⟨spT μ T, continuous_sp continuous_id⟩, fun g' V => sp_gact g' V,
      Function.update (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₁, y₀) g,
      fun _ => 1, ?_⟩
    show spT μ T (Function.update (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₁, y₀) g)
      ≠ spT μ T (fun _ : SpT μ T => (1 : MassGap.SUN.SU N))
    set V := Function.update (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₁, y₀) g with hV
    have hzero : spT μ T (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) = 0 := by
      unfold spT
      simp [MassGap.WilsonAction.wilsonDensity_one hN]
    have hv1 : V (ν₁, y₀) = g := Function.update_self _ _ _
    have hv2 : V (ν₀, tsh μ T ν₁ y₀) = 1 :=
      Function.update_of_ne (fun h => hν (congrArg Prod.fst h).symm) _ _
    have hv3 : V (ν₁, tsh μ T ν₀ y₀) = 1 :=
      Function.update_of_ne (fun h => tsh_ne_self hbig y₀ (congrArg Prod.snd h)) _ _
    have hv4 : V (ν₀, y₀) = 1 :=
      Function.update_of_ne (fun h => hν (congrArg Prod.fst h).symm) _ _
    have hterm : plaqT V ν₁ ν₀ y₀ = MassGap.WilsonAction.wilsonDensity g := by
      unfold plaqT
      simp only [hv1, hv2, hv3, hv4, inv_one, mul_one]
    have hnn : ∀ a b y, 0 ≤ plaqT V a b y := fun _ _ _ =>
      MassGap.WilsonAction.wilsonDensity_nonneg hN _
    have hpos : 0 < spT μ T V := by
      rw [spT_eq_plaqT]
      calc (0 : ℝ) < plaqT V ν₁ ν₀ y₀ := by rw [hterm]; exact hg
        _ ≤ ∑ y, plaqT V ν₁ ν₀ y :=
            Finset.single_le_sum (f := fun y => plaqT V ν₁ ν₀ y) (fun y _ => hnn _ _ _)
              (Finset.mem_univ y₀)
        _ ≤ ∑ b, ∑ y, plaqT V ν₁ b y :=
            Finset.single_le_sum (f := fun b => ∑ y, plaqT V ν₁ b y)
              (fun b _ => Finset.sum_nonneg fun y _ => hnn _ _ _) (Finset.mem_univ ν₀)
        _ ≤ ∑ a, ∑ b, ∑ y, plaqT V a b y :=
            Finset.single_le_sum (f := fun a => ∑ b, ∑ y, plaqT V a b y)
              (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => hnn _ _ _)
              (Finset.mem_univ ν₁)
    rw [hzero]
    exact hpos.ne'
  · -- one closed link along `ν₀`
    have h1 : T ν₀ = 1 := by have := hT ν₀; omega
    refine ⟨⟨fun V => MassGap.WilsonAction.wilsonDensity (V (ν₀, y₀)),
      MassGap.WilsonAction.continuous_wilsonDensity.comp (continuous_apply _)⟩, ?_,
      Function.update (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₀, y₀) g,
      fun _ => 1, ?_⟩
    · intro g' V
      show MassGap.WilsonAction.wilsonDensity (gact g' V (ν₀, y₀))
        = MassGap.WilsonAction.wilsonDensity (V (ν₀, y₀))
      simp only [gact]
      rw [tsh_eq_self h1 y₀]
      exact MassGap.WilsonAction.wilsonDensity_conj _ _
    · show MassGap.WilsonAction.wilsonDensity
          (Function.update (fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₀, y₀) g (ν₀, y₀))
        ≠ MassGap.WilsonAction.wilsonDensity ((fun _ : SpT μ T => (1 : MassGap.SUN.SU N)) (ν₀, y₀))
      rw [Function.update_self]
      simp only [MassGap.WilsonAction.wilsonDensity_one hN]
      exact hg.ne'

/-- **The Wilson one-step rate is positive** at `2 ≤ N`, `β > 0` and nonzero transverse
extents. -/
theorem ratio_pos_wilson (hN : N ≠ 0) (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 < β) (hT : ∀ j, T j ≠ 0) :
    0 < (perronKT μ T N hN β hβ.le).ratio := by
  obtain ⟨u, hu, a, b, hab⟩ := exists_nonconst (μ := μ) (T := T) hN2 hT
  exact ratio_pos_wilson_of hN hβ u hu hab

/-! ## 4. The box of `FixedAperture` -/

/-- The periodic box with `m 2ᵏ` sites on every side. -/
def boxL (m k : ℕ) : Fin 4 → ℕ := fun _ => m * 2 ^ k

/-- Its transverse extents for the time direction `μ`. -/
abbrev boxT (μ : Fin 4) (m k : ℕ) : {j : Fin 4 // j ≠ μ} → ℕ := tr (boxL m k) μ

theorem boxT_ne_zero (μ : Fin 4) {m : ℕ} (hm : 0 < m) (k : ℕ) (j : {j : Fin 4 // j ≠ μ}) :
    boxT μ m k j ≠ 0 :=
  show m * 2 ^ k ≠ 0 from Nat.mul_ne_zero hm.ne' (pow_ne_zero _ two_ne_zero)

/-- **The box partition function is the closed Doob cycle of the slab's kernel**:
`ZR (boxL m k) = λ₀^{m 2ᵏ} · cyc (Haar) kD (m 2ᵏ)`, with `kD` the Doob density of
`perronKT μ (boxT μ m k) N`. -/
theorem ZR_box_eq (μ : Fin 4) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (m k : ℕ) :
    ZR (boxL m k) N β = (perronKT μ (boxT μ m k) N hN β hβ).lam0 ^ (m * 2 ^ k)
      * MassGap.CyclicKernel.cyc (perronKT μ (boxT μ m k) N hN β hβ).μ
          (perronKT μ (boxT μ m k) N hN β hβ).kD (m * 2 ^ k) := by
  rw [cyc_kD, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (perronKT μ (boxT μ m k) N hN β hβ).lam0_pos.ne'), one_mul]
  exact ZR_eq_cyc (μ := μ) hN β

/-- **`0 < ratio < 1` on the box** at `m > 0`, `2 ≤ N`, `β > 0`. -/
theorem ratio_mem_box (μ : Fin 4) (hN : N ≠ 0) (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (hm : 0 < m) (k : ℕ) :
    0 < (perronKT μ (boxT μ m k) N hN β hβ.le).ratio ∧
      (perronKT μ (boxT μ m k) N hN β hβ.le).ratio < 1 :=
  ⟨ratio_pos_wilson hN hN2 hβ (boxT_ne_zero μ hm k), ratio_lt_one_wilson hN hβ.le⟩

/-- **`ReadsSlabM` on the box of `FixedAperture`**, with no positivity hypothesis: at `2 ≤ N` and
couplings `β m k > 0`, the box gap `−log ratio / a_k` reads the Doob slab of `m 2ᵏ` steps of the slice
transfer of the box of side `m 2ᵏ`. -/
theorem readsSlabM_wilson_box (μ : Fin 4) (hN : N ≠ 0) (hN2 : 2 ≤ N) (β : ℕ → ℕ → ℝ)
    (hβ : ∀ m k, 0 < β m k) {a₀ : ℝ} (ha : 0 < a₀) :
    ReadsSlabM (fun m k => (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).boxGap (aZ a₀ k))
      (fun m k => (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).slab (m * 2 ^ k)) (LA a₀) :=
  readsSlabM_wilson μ (fun m k => boxT μ m k) N hN β (fun m k => (hβ m k).le) ha
    (fun m k hm => (ratio_mem_box μ hN hN2 (hβ m k) hm k).1)

/-- **The (A)-chain on the box of `FixedAperture`**: `RelFloorM` for the box Doob slabs and an
observer reading in `(0, R]` give `FixedApertureFloor` for the box gap `−log ratio / a_k`, at
`2 ≤ N` and `β m k > 0`. -/
theorem fixedApertureFloor_wilson_box (μ : Fin 4) (hN : N ≠ 0) (hN2 : 2 ≤ N) (β : ℕ → ℕ → ℝ)
    (hβ : ∀ m k, 0 < β m k) {a₀ : ℝ} (ha : 0 < a₀) {rLat : ℕ → ℝ} {ρ : ℕ → ℝ} {K : ℕ → ℕ} {R : ℝ}
    (hA : RelFloorM
      (fun m k => (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).slab (m * 2 ^ k)) ρ K)
    (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) :
    FixedApertureFloor
      (fun m k => (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).boxGap (aZ a₀ k))
      rLat (MassGap.RelativeGap.relValue ρ (LA a₀) R) K :=
  fixedApertureFloor_of_relFloorM (readsSlabM_wilson_box μ hN hN2 β hβ ha) hA hR hr

end Wilson

#print axioms eigen_of_form_top
#print axioms abs_eigen
#print axioms int_mul_int_eq_zero
#print axioms top_simple
#print axioms no_neg
#print axioms exists_contr_lt
#print axioms U_PD
#print axioms ratio_le_of_contr
#print axioms ratio_lt_one_of
#print axioms ratio_pos_of_K_ne
#print axioms cyc_kD
#print axioms ratio_lt_one_wilson
#print axioms kernel_eq_cLp
#print axioms inner_cLp_kernel
#print axioms form_nonneg_wilson
#print axioms ratio_eq_lam1_wilson
#print axioms continuous_φ
#print axioms gaugeInv_φ
#print axioms ratio_pos_of_proj
#print axioms ratio_pos_wilson_of
#print axioms exists_nonconst
#print axioms ratio_pos_wilson
#print axioms ZR_box_eq
#print axioms ratio_mem_box
#print axioms readsSlabM_wilson_box
#print axioms fixedApertureFloor_wilson_box

end MassGap.WilsonSlab
