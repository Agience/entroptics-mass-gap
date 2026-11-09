import Mathlib
import MassGap.ElectricLoops
import MassGap.SliceKernelPower
import MassGap.FiniteReadingFlux

/-!
# MassGap.LoopsGenerate — the loop states generate the excited zero-flux levels

`ElectricLoops.zeroFluxGap_of_loopShells` takes two inputs: (E1), its hypothesis `hgen`, that every
excited level `φ_j` (`j ≠ g₀`) of `trivKN 2 β n i` lies in the `L²` closure of the span of the loop
states `ψ_C = (W_C − ⟨W_C⟩) Ω` of `Ω = φ_{g₀}`; and (E2'), the shell block bounds. This module proves
(E1) at every `β > 0`, side `n`, step `i`, for measurable levels: **`excited_mem_closure_loops`**.
**`zeroFluxGap_of_loopShells_E2`** is `zeroFluxGap_of_loopShells` with `hgen` supplied, so its only
input beyond `EigenLevels` and the kernel data is (E2').

## 1. Stone–Weierstrass through a family (proved, any compact space)

**`exists_adjoin_near`**: on a compact `X`, a continuous `f` constant on the fibres of a family `w` of
continuous real functions is a uniform limit of the algebra `w` generates. No quotient by a group is
formed: the range `K` of `x ↦ (w_c x)_c` in `ℝ^ι` is compact Hausdorff, `X → K` is a closed
continuous surjection hence a quotient map, so `f` factors through a continuous `F` on `K`; the
coordinate functions separate the points of `K`, and Mathlib's
`exists_mem_subalgebra_near_continuous_of_separatesPoints` approximates `F`; composing back gives the
approximant on `X`.

## 2. The Wilson loops at one base span an algebra (proved)

`wlC`, `baseW y₀` (the Wilson loops based at `y₀` as continuous functions). `one_mem_span` (the empty
loop, `W = 2`), `mul_mem_span` (`ElectricLoops.Loop.wl_mul`), **`adjoin_le_span`**: the algebra the
loops at `y₀` generate is their linear span.

## 3. From uniform approximation to the `L²` closure of the loop states (proved)

`stateFn μ Ω g = (g − ∫ g Ω²) Ω`; `stateFn_mem_span`: for `g` in the span of the loops at `y₀` its
`L²` class lies in the span of `ElectricLoops.allLoops μ Ω`. **`mem_closure_span_allLoops`**: for a
probability measure on the slice, `Ω` continuous and nowhere zero with `∫ Ω² = 1`, and `φ`
continuous with `∫ Ω φ = 0`, if `φ / Ω` takes one value on configurations that no Wilson loop at
`y₀` separates, then `φ` is in the `L²` closure of the span of the loop states. The approximant of
`φ/Ω` within `δ` uniformly gives a loop combination within `2δ sup|Ω|` of `φ`: the constant
`∫ p Ω²` equals `∫ (p − φ/Ω) Ω²` because `∫ Ω φ = 0`.

## 4. The zero-flux levels are continuous and gauge invariant (proved)

`iter_gauge_left`, **`trivKN_gauge_left`**: `trivKN(gauge h x, y) = trivKN(x, y)`
(`SliceKernelPower.kT_gact_left` through the kernel powers and the centre average).
`continuous_trivKN_left` (`SliceKernelPower.continuous_iter`). `eigen_ne_zero` (`μ_j² = e^{−E_j t}`),
`level_eq` (`φ_j = μ_j⁻¹ ∫ trivKN(·, y) φ_j(y)`), **`level_gauge`**, **`continuous_level`** (at
`β ≥ 0`, dominated convergence). **`hgen_of_separation`**: (E1) from orbit separation by the loops at
`y₀` and a nowhere-zero ground level.

## 5. Quaternion families with the same traces are conjugate (proved)

In `ℍ[ℝ]`: `pure_mul_self`, `anticomm` (orthogonal pure quaternions anticommute), `comm_real`,
`align_gen` and **`align`** (pure `p, q` of one norm: `g = |p|² − q p`, or `g = Im(p e)` when
`q = −p`, has `g p = q g`), **`align_fix`** (a rotation about a pure `q` carrying `s` to `t`),
`parallel`, **`determined`** (a pure quaternion is fixed by its products with `p`, `t` and `p t` when
`p ∦ t`), `Match` and `Match.conj` (the two- and three-fold invariants survive conjugation),
`exists_conj_of_eq`, **`exists_conj_pure`**, and **`exists_conj`**: families `a, b : κ → ℍ` with
`Re a_k = Re b_k`, `Re(a_k a_l) = Re(b_k b_l)` and `Re(a_k a_l a_m) = Re(b_k b_l b_m)` for all indices
have one `g ≠ 0` with `g a_k = b_k g` for every `k`. `κ` is any type; only products of at most three
letters are used.

## 6. `SU(2)` as the unit quaternions (proved)

`su2_entries` (`X = [[a, b], [−b̄, ā]]`), `toQ`, **`toQ_mul`**, `re_trace_eq` (`Re tr X = 2 Re toQ X`),
`toQ_injective`, `toQ_inv`, `qMat`, `qMat_mem`, `ofQ`, `toQ_ofQ`. **`su2_conj_of_traces`**: `SU(2)`
families with equal real traces of all products of one, two and three letters are simultaneously
conjugate in `SU(2)`.

## 7. Orbit separation on the slice — Giles at `SU(2)` (proved)

`exists_path` (every site of the transverse torus is reached from `y₀` by forward steps), `path`,
`pathHol`, `linkLoop y₀ l` (out along the path to the link's start, across `l`, back from its end),
`linkLoop_hol` (`hol = P(y) V(l) P(y + ν)⁻¹`). **`giles`**: if `W_C(V) = W_C(V')` for every loop `C`
based at `y₀`, then `V' = gauge h V` with `h(z) = P_{V'}(z)⁻¹ G P_V(z)`, `G` the conjugator that
`su2_conj_of_traces` returns for the link-loop holonomies (the traces used are those of the loops
`linkLoop`, their composites of two and of three).

## 8. The form of a kernel against an orthonormal eigenfamily (proved, any probability space)

`BM` (bounded measurable). `integral_sub_sum_sq`, `remS` (the kernel with the levels of a finite
`S` removed), **`hs_remS`** (`hs k = Σ_S c_j² + hs(remS)`), `qform`, `qform_remS`,
**`abs_qform_le`** (`|∫ f · R f| ≤ √hs(R) ∫ f²`), `bessel`, **`qform_le`**: if the squared eigenvalues
sum to `hs k`, the form is at most `M ∫ f²` for every `M ≥ 0` above every eigenvalue.
`summable_sq`. `qform_cross_symm`, `qform_add_smul`, **`integral_defect_sq`**: for a nonnegative
symmetric kernel whose form is at most `|μ₀| ∫ u²`, an eigenfunction `Ω` for `μ₀` has
`∫ (K|Ω| − |μ₀| |Ω|)² = 0` (the form along `|Ω| + t g`, `g = K|Ω| − |μ₀||Ω| ≥ 0`).

## 9. The ground level has no zero, and (E1) (proved)

`continuous_trivKN_row`. **`ground_ne_zero`** (`β > 0`): `φ_{g₀}(x) ≠ 0` at every `x`. `hs_eq` and
`energy` give `Σ μ_j² = hs(trivKN)`; `ground` gives `μ_j ≤ |μ_{g₀}|`; so `qform_le` bounds the form by
`|μ_{g₀}|`, `integral_defect_sq` makes `|φ_{g₀}|` an eigenfunction (continuity, and
`SliceKernelPower.eq_zero_of_integral_eq_zero` for the Haar measure), and
`|μ_{g₀}| |φ_{g₀}(x)| ≥ floor · ∫ |φ_{g₀}| > 0` (`FiniteReadingFlux.low_trivKN`). No Jentzsch theorem
for `trivKN` is used. **`excited_mem_closure_loops`** and **`zeroFluxGap_of_loopShells_E2`** as
above.

## Scope

Everything is at one `(β, n, i)` with `β > 0` and a chosen site `y₀`. The levels enter only through
`TensionFloor.EigenLevels` and their measurability. (E2') is untouched.

DERIVED (module-wide): `2` is `N` for `SU(2)`, the `L²` exponent and the square, `Re tr = 2 Re` of
the quaternion, the empty loop's `W = 2` (so `1 = W/2`), and the `2t` of a cross term; `3` is the
number of letters `exists_conj` needs; `4` in `δ = ε / (4 (B + 1))` makes `2 δ B < ε`; `1` the norm
of a unit quaternion and of `Ω`; `0` the real part of a pure quaternion. `G/(q+1)` is the step
along the line that makes the form negative when `∫ g² > 0`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LoopsGenerate

open MeasureTheory Filter
open scoped Pointwise
open MassGap.ElectricLoops
open MassGap.RectWilson (SpT TT tsh)

/-! ## 1. Stone–Weierstrass through a family of continuous functions -/

section Factor

variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Stone–Weierstrass through a family.** A continuous `f` on a compact space that is constant on
the fibres of a family `w` of continuous functions is a uniform limit of the algebra `w` generates. -/
theorem exists_adjoin_near (w : ι → C(X, ℝ)) (f : X → ℝ) (hf : Continuous f)
    (hfib : ∀ x y, (∀ c, w c x = w c y) → f x = f y) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Algebra.adjoin ℝ (Set.range w), ∀ x, |p x - f x| < ε := by
  let Φ : X → (ι → ℝ) := fun x c => w c x
  have hΦ : Continuous Φ := continuous_pi fun c => (w c).continuous
  haveI : CompactSpace (Set.range Φ) := isCompact_iff_compactSpace.mp (isCompact_range hΦ)
  let Ψ : X → Set.range Φ := fun x => ⟨Φ x, x, rfl⟩
  have hΨ : Continuous Ψ := hΦ.subtype_mk _
  have hsurj : Function.Surjective Ψ := fun ⟨_, x, rfl⟩ => ⟨x, rfl⟩
  have hq : Topology.IsQuotientMap Ψ := hΨ.isClosedMap.isQuotientMap hΨ hsurj
  let F : Set.range Φ → ℝ := fun k => f (Function.surjInv hsurj k)
  have hFΨ : ∀ x, F (Ψ x) = f x := by
    intro x
    apply hfib
    intro c
    have h := congrArg (fun k : Set.range Φ => (k : ι → ℝ) c) (Function.surjInv_eq hsurj (Ψ x))
    exact h
  have hF : Continuous F := by
    rw [hq.continuous_iff]
    have : F ∘ Ψ = f := funext hFΨ
    rw [this]; exact hf
  let coord : ι → C(Set.range Φ, ℝ) := fun c =>
    ⟨fun k => (k : ι → ℝ) c, (continuous_apply c).comp continuous_subtype_val⟩
  let A := Algebra.adjoin ℝ (Set.range coord)
  have hsep : A.SeparatesPoints := by
    intro k k' hne
    have : ∃ c, (k : ι → ℝ) c ≠ (k' : ι → ℝ) c := by
      by_contra h
      push Not at h
      exact hne (Subtype.ext (funext h))
    obtain ⟨c, hc⟩ := this
    exact ⟨coord c, ⟨coord c, Algebra.subset_adjoin ⟨c, rfl⟩, rfl⟩, hc⟩
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep F hF ε hε
  let π := ContinuousMap.compRightAlgHom ℝ ℝ (⟨Ψ, hΨ⟩ : C(X, Set.range Φ))
  refine ⟨π g, ?_, fun x => ?_⟩
  · have hmap : A.map π = Algebra.adjoin ℝ (Set.range w) := by
      rw [AlgHom.map_adjoin, ← Set.range_comp]
      congr 2
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨g, g.2, rfl⟩
  · have h := hg (Ψ x)
    rw [Real.norm_eq_abs, hFΨ] at h
    exact h

end Factor

/-! ## 2. The Wilson loops at one base span a unital algebra -/

section Algebra

variable {i : Fin 4} {T : Dir i → ℕ}

/-- A Wilson loop as a continuous function. -/
def wlC (C : Loop i T) : C(SpT i T → SUN.SU 2, ℝ) := ⟨C.wl, continuous_wl C⟩

/-- The Wilson loops based at `y₀`. -/
def baseW (y₀ : TT i T) : {C : Loop i T // C.base = y₀} → C(SpT i T → SUN.SU 2, ℝ) :=
  fun C => wlC C.1

/-- The span of the Wilson loops at `y₀` contains the constant `1` (the empty loop has `W = 2`). -/
theorem one_mem_span (y₀ : TT i T) :
    (1 : C(SpT i T → SUN.SU 2, ℝ)) ∈ Submodule.span ℝ (Set.range (baseW y₀)) := by
  have h : (1 : C(SpT i T → SUN.SU 2, ℝ)) = (1 / 2 : ℝ) • baseW y₀ ⟨⟨y₀, [], rfl⟩, rfl⟩ := by
    ext V
    simp only [ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul, baseW, wlC,
      ContinuousMap.coe_mk]
    rw [wl_nil]; norm_num
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The span of the Wilson loops at `y₀` is closed under products (`Loop.wl_mul`). -/
theorem mul_mem_span (y₀ : TT i T) {x y : C(SpT i T → SUN.SU 2, ℝ)}
    (hx : x ∈ Submodule.span ℝ (Set.range (baseW y₀)))
    (hy : y ∈ Submodule.span ℝ (Set.range (baseW y₀))) :
    x * y ∈ Submodule.span ℝ (Set.range (baseW y₀)) := by
  have hss : Set.range (baseW y₀) * Set.range (baseW y₀)
      ⊆ (Submodule.span ℝ (Set.range (baseW y₀)) : Set _) := by
    rintro _ ⟨_, ⟨C, rfl⟩, _, ⟨C', rfl⟩, rfl⟩
    have hb : C'.1.base = C.1.base := C'.2.trans C.2.symm
    have he : baseW y₀ C * baseW y₀ C'
        = baseW y₀ ⟨C.1.comp C'.1 hb, C.2⟩ + baseW y₀ ⟨C.1.comp C'.1.inv hb, C.2⟩ := by
      ext V
      simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, baseW, wlC, ContinuousMap.coe_mk]
      exact Loop.wl_mul C.1 C'.1 hb V
    show baseW y₀ C * baseW y₀ C' ∈ _
    rw [he]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hm : x * y ∈ Submodule.span ℝ (Set.range (baseW y₀)) * Submodule.span ℝ (Set.range (baseW y₀)) :=
    Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at hm
  exact (Submodule.span_le.mpr hss) hm

/-- **The algebra generated by the Wilson loops at `y₀` is their span.** -/
theorem adjoin_le_span (y₀ : TT i T) {p : C(SpT i T → SUN.SU 2, ℝ)}
    (hp : p ∈ Algebra.adjoin ℝ (Set.range (baseW y₀))) :
    p ∈ Submodule.span ℝ (Set.range (baseW y₀)) := by
  let S := (Submodule.span ℝ (Set.range (baseW y₀))).toSubalgebra (one_mem_span y₀)
    (fun _ _ hx hy => mul_mem_span y₀ hx hy)
  have hle : Algebra.adjoin ℝ (Set.range (baseW y₀)) ≤ S :=
    Algebra.adjoin_le (Submodule.subset_span (s := Set.range (baseW y₀)))
  exact hle hp

end Algebra

/-! ## 3. From uniform approximation by loop polynomials to the `L²` closure of the loop states -/

section States

variable {i : Fin 4} {T : Dir i → ℕ} {μ : Measure (SpT i T → SUN.SU 2)} [IsProbabilityMeasure μ]

/-- A continuous function on the slice is bounded by its sup norm. -/
theorem abs_le_norm {g : (SpT i T → SUN.SU 2) → ℝ} (hg : Continuous g) (V : SpT i T → SUN.SU 2) :
    |g V| ≤ ‖(⟨g, hg⟩ : C(SpT i T → SUN.SU 2, ℝ))‖ := by
  have h := ContinuousMap.norm_coe_le_norm (⟨g, hg⟩ : C(SpT i T → SUN.SU 2, ℝ)) V
  rwa [Real.norm_eq_abs] at h

/-- A continuous function on the slice is integrable. -/
theorem integrable_of_cont {g : (SpT i T → SUN.SU 2) → ℝ} (hg : Continuous g) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun V => by rw [Real.norm_eq_abs]; exact abs_le_norm hg V)

/-- A continuous function on the slice is in `L²`. -/
theorem memLp_of_cont {g : (SpT i T → SUN.SU 2) → ℝ} (hg : Continuous g) : MemLp g 2 μ :=
  MemLp.of_bound hg.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun V => by rw [Real.norm_eq_abs]; exact abs_le_norm hg V)

/-- The state `(g − ∫ g Ω²) Ω` of a function `g`. -/
def stateFn (μ : Measure (SpT i T → SUN.SU 2)) (Ω g : (SpT i T → SUN.SU 2) → ℝ) :
    (SpT i T → SUN.SU 2) → ℝ :=
  fun V => (g V - ∫ U, g U * Ω U ^ 2 ∂μ) * Ω V

omit [IsProbabilityMeasure μ] in
theorem continuous_stateFn {Ω g : (SpT i T → SUN.SU 2) → ℝ} (hΩ : Continuous Ω) (hg : Continuous g) :
    Continuous (stateFn μ Ω g) :=
  (hg.sub continuous_const).mul hΩ

/-- **Every combination of Wilson loops at `y₀` gives a state in the span of the loop states.** -/
theorem stateFn_mem_span {Ω : (SpT i T → SUN.SU 2) → ℝ} (hΩ : Continuous Ω) (y₀ : TT i T)
    {p : C(SpT i T → SUN.SU 2, ℝ)} (hp : p ∈ Submodule.span ℝ (Set.range (baseW y₀))) :
    (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ p.continuous)).toLp (stateFn μ Ω p)
      ∈ Submodule.span ℝ (allLoops μ Ω) := by
  have hint : ∀ q : C(SpT i T → SUN.SU 2, ℝ), Integrable (fun U => q U * Ω U ^ 2) μ :=
    fun q => integrable_of_cont (q.continuous.mul (hΩ.pow 2))
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨C, rfl⟩ := hx
      refine Submodule.subset_span ⟨C, ?_⟩
      refine (MemLp.coeFn_toLp _).trans (Filter.Eventually.of_forall fun V => ?_)
      rfl
  | zero =>
      have h0 : stateFn μ Ω (0 : C(SpT i T → SUN.SU 2, ℝ)) = 0 := by
        funext V; simp [stateFn]
      have : (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ
          (0 : C(SpT i T → SUN.SU 2, ℝ)).continuous)).toLp (stateFn μ Ω (0 : C(SpT i T → SUN.SU 2, ℝ)))
          = 0 := by
        rw [← MemLp.toLp_zero (memLp_of_cont (μ := μ) (g := (0 : (SpT i T → SUN.SU 2) → ℝ))
          continuous_zero)]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [h0])
      rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      have he : stateFn μ Ω (x + y : C(SpT i T → SUN.SU 2, ℝ))
          = stateFn μ Ω x + stateFn μ Ω y := by
        funext V
        simp only [stateFn, ContinuousMap.add_apply, Pi.add_apply, add_mul]
        rw [integral_add (hint x) (hint y)]
        ring
      have : (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ
          (x + y : C(SpT i T → SUN.SU 2, ℝ)).continuous)).toLp
            (stateFn μ Ω (x + y : C(SpT i T → SUN.SU 2, ℝ)))
          = (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ x.continuous)).toLp
              (stateFn μ Ω x)
            + (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ y.continuous)).toLp
              (stateFn μ Ω y) := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [he])
      rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      have he : stateFn μ Ω (a • x : C(SpT i T → SUN.SU 2, ℝ)) = a • stateFn μ Ω x := by
        funext V
        simp only [stateFn, ContinuousMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]
        rw [integral_const_mul]
        ring
      have : (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ
          (a • x : C(SpT i T → SUN.SU 2, ℝ)).continuous)).toLp
            (stateFn μ Ω (a • x : C(SpT i T → SUN.SU 2, ℝ)))
          = a • (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩ x.continuous)).toLp
              (stateFn μ Ω x) := by
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [he])
      rw [this]; exact Submodule.smul_mem _ _ hx

/-- **(E1) on the slice, from orbit separation.** Let `Ω` be continuous, nowhere zero, with
`∫ Ω² = 1`, and `φ` continuous with `∫ Ω φ = 0`. If `φ / Ω` takes one value on any two
configurations that no Wilson loop at `y₀` tells apart, then `φ` is in the `L²` closure of the span
of the loop states of `Ω`. -/
theorem mem_closure_span_allLoops (y₀ : TT i T) {Ω φ : (SpT i T → SUN.SU 2) → ℝ}
    (hΩc : Continuous Ω) (hΩ0 : ∀ V, Ω V ≠ 0) (h1 : ∫ V, Ω V ^ 2 ∂μ = 1)
    (hφc : Continuous φ) (horth : ∫ V, Ω V * φ V ∂μ = 0)
    (hfib : ∀ V V', (∀ C : Loop i T, C.base = y₀ → C.wl V = C.wl V') → φ V / Ω V = φ V' / Ω V')
    (hφ : MemLp φ 2 μ) :
    hφ.toLp φ ∈ closure (Submodule.span ℝ (allLoops μ Ω) : Set (Lp ℝ 2 μ)) := by
  set f : (SpT i T → SUN.SU 2) → ℝ := fun V => φ V / Ω V with hfdef
  have hfc : Continuous f := hφc.div hΩc hΩ0
  set B := ‖(⟨Ω, hΩc⟩ : C(SpT i T → SUN.SU 2, ℝ))‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have hΩB : ∀ V, |Ω V| ≤ B := abs_le_norm hΩc
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := ε / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hpA, hp⟩ := exists_adjoin_near (baseW y₀) f hfc
    (fun x y h => hfib x y fun C hC => h ⟨C, hC⟩) hδ0
  have hpS := adjoin_le_span y₀ hpA
  have hmem := stateFn_mem_span (μ := μ) hΩc y₀ hpS
  refine ⟨_, hmem, ?_⟩
  -- the constant `∫ p Ω²` is small
  set c := ∫ U, p U * Ω U ^ 2 ∂μ with hc
  have hfΩ : ∀ U, f U * Ω U ^ 2 = Ω U * φ U := by
    intro U; simp only [hfdef]; field_simp [hΩ0 U]
  have hint2 : Integrable (fun U => Ω U ^ 2) μ := integrable_of_cont (hΩc.pow 2)
  have hcf : c = ∫ U, (p U - f U) * Ω U ^ 2 ∂μ := by
    have e : (fun U => (p U - f U) * Ω U ^ 2) = fun U => p U * Ω U ^ 2 - Ω U * φ U := by
      funext U; rw [sub_mul, hfΩ]
    rw [e, integral_sub (f := fun U => p U * Ω U ^ 2) (g := fun U => Ω U * φ U) (integrable_of_cont (p.continuous.mul (hΩc.pow 2)))
      (integrable_of_cont (hΩc.mul hφc)), horth, sub_zero]
  have hcδ : |c| ≤ δ := by
    rw [hcf, ← Real.norm_eq_abs]
    calc ‖∫ U, (p U - f U) * Ω U ^ 2 ∂μ‖ ≤ ∫ U, δ * Ω U ^ 2 ∂μ :=
          norm_integral_le_of_norm_le (hint2.const_mul δ) (Filter.Eventually.of_forall fun U => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Ω U))]
            exact mul_le_mul_of_nonneg_right (hp U).le (sq_nonneg _))
      _ = δ := by rw [integral_const_mul, h1, mul_one]
  -- the pointwise bound
  have hpt : ∀ U, |φ U - stateFn μ Ω p U| ≤ 2 * δ * B := by
    intro U
    have hφU : φ U = f U * Ω U := by simp only [hfdef]; field_simp [hΩ0 U]
    have e : φ U - stateFn μ Ω p U = (f U - p U) * Ω U + c * Ω U := by
      simp only [stateFn]; rw [hφU, ← hc]; ring
    rw [e]
    calc |(f U - p U) * Ω U + c * Ω U| ≤ |(f U - p U) * Ω U| + |c * Ω U| := abs_add_le _ _
      _ = |p U - f U| * |Ω U| + |c| * |Ω U| := by rw [abs_mul, abs_mul, abs_sub_comm]
      _ ≤ δ * B + δ * B := add_le_add
          (mul_le_mul (hp U).le (hΩB U) (abs_nonneg _) hδ0.le)
          (mul_le_mul hcδ (hΩB U) (abs_nonneg _) hδ0.le)
      _ = 2 * δ * B := by ring
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  have hbd := Lp.norm_le_of_ae_bound (μ := μ) (p := 2)
    (f := (hφ.sub (memLp_of_cont (μ := μ) (continuous_stateFn (μ := μ) hΩc p.continuous))).toLp
      (φ - stateFn μ Ω p)) (by positivity : (0 : ℝ) ≤ 2 * δ * B)
    (by
      filter_upwards [(hφ.sub (memLp_of_cont (μ := μ)
        (continuous_stateFn (μ := μ) hΩc p.continuous))).coeFn_toLp] with U hU
      rw [hU, Real.norm_eq_abs]; exact hpt U)
  have hone : (measureUnivNNReal μ : ℝ) = 1 := by simp [measureUnivNNReal]
  have hlt : 2 * δ * B < ε := by
    rw [hδ]
    have hB1 : 0 < B + 1 := by linarith
    rw [div_eq_mul_inv]
    have : 2 * (ε * (4 * (B + 1))⁻¹) * B = ε * (B / (2 * (B + 1))) := by field_simp; ring
    rw [this]
    have : B / (2 * (B + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc _ ≤ (measureUnivNNReal μ : ℝ) ^ ((2 : ENNReal).toReal⁻¹) * (2 * δ * B) := by
        exact_mod_cast hbd
    _ = 2 * δ * B := by rw [hone, Real.one_rpow, one_mul]
    _ < ε := hlt

end States

/-! ## 4. The zero-flux levels are continuous and gauge invariant -/

section Levels

open MassGap.CentreSectorSeedN (trivKN hSN halfKN bdd_trivKN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.KernelPower (iter conv)
open MassGap.RectTransfer (kT)
open MassGap.ZeroFluxSector (zk)

variable {i : Fin 4}

/-- The kernel powers of the slice transfer are gauge invariant in their first argument. -/
theorem iter_gauge_left {T : Dir i → ℕ} (β : ℝ) (h : TT i T → SUN.SU 2) :
    ∀ (m : ℕ) (x y : SpT i T → SUN.SU 2),
      iter (RectTransfer.hS i T 2) (kT i T 2 β) m (gauge h x) y
        = iter (RectTransfer.hS i T 2) (kT i T 2 β) m x y
  | 0, x, y => SliceKernelPower.kT_gact_left β h x y
  | m + 1, x, y => by
      simp only [iter, conv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show kT i T 2 β (gauge h x) z * _ = kT i T 2 β x z * _
      rw [show kT i T 2 β (gauge h x) z = kT i T 2 β x z from SliceKernelPower.kT_gact_left β h x z]

/-- **The zero-flux kernel is gauge invariant in its first argument.** -/
theorem trivKN_gauge_left (β : ℝ) (n : ℕ) (h : TT i (Tr n i) → SUN.SU 2) (x y : Slice n i) :
    trivKN 2 β n i (gauge h x) y = trivKN 2 β n i x y := by
  unfold trivKN zk halfKN
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  exact iter_gauge_left β h _ x _

/-- The zero-flux kernel is continuous in its first argument. -/
theorem continuous_trivKN_left (β : ℝ) (n : ℕ) (y : Slice n i) :
    Continuous fun x => trivKN 2 β n i x y := by
  unfold trivKN zk halfKN
  have hc := SliceKernelPower.continuous_iter (μ := i) (T := Tr n i) (N := 2) β (n / 2 - 1)
  exact continuous_const.mul (continuous_finsetSum _ fun g _ =>
    hc.comp (continuous_id.prodMk continuous_const))

/-- A level's eigenvalue is not zero (`μ_j² = e^{−E_j t} > 0`). -/
theorem eigen_ne_zero {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv) (j : ι) : μv j ≠ 0 := by
  intro h0
  have := hL.energy j
  rw [h0] at this
  have hp := Real.exp_pos (-(E j * ((n : ℝ) * AsymptoticScaling.aRun 2 β)))
  rw [← this] at hp
  norm_num at hp

/-- A level is `μ_j⁻¹ ∫ trivKN(·, y) φ_j(y)`. -/
theorem level_eq {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv) (j : ι) (x : Slice n i) :
    φ j x = (μv j)⁻¹ * ∫ y, trivKN 2 β n i x y * φ j y ∂(hSN 2 n i) := by
  rw [hL.eigen j x, ← mul_assoc, inv_mul_cancel₀ (eigen_ne_zero hL j), one_mul]

/-- **Every zero-flux level is gauge invariant.** -/
theorem level_gauge {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv) (j : ι) (h : TT i (Tr n i) → SUN.SU 2)
    (x : Slice n i) : φ j (gauge h x) = φ j x := by
  rw [level_eq hL j (gauge h x), level_eq hL j x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show trivKN 2 β n i (gauge h x) y * φ j y = trivKN 2 β n i x y * φ j y
  rw [trivKN_gauge_left]

/-- **Every zero-flux level is continuous** (at `β ≥ 0`, for measurable levels). -/
theorem continuous_level {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (j : ι) : Continuous (φ j) := by
  have hb := bdd_trivKN (N := 2) hβ n i
  obtain ⟨C, hC⟩ := hb.bdd
  have hint : Integrable (φ j) (hSN 2 n i) :=
    (memLp_of_norm (hm j) (hL.norm j)).integrable one_le_two
  have hcont : Continuous fun x => ∫ y, trivKN 2 β n i x y * φ j y ∂(hSN 2 n i) := by
    refine continuous_of_dominated (bound := fun y => C * |φ j y|) (fun x => ?_)
      (fun x => Filter.Eventually.of_forall fun y => ?_) (hint.abs.const_mul C)
      (Filter.Eventually.of_forall fun y => ?_)
    · exact ((hb.meas.comp (measurable_const.prodMk measurable_id)).mul (hm j)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x y) (abs_nonneg _)
    · exact (continuous_trivKN_left β n y).mul continuous_const
  have he : φ j = fun x => (μv j)⁻¹ * ∫ y, trivKN 2 β n i x y * φ j y ∂(hSN 2 n i) :=
    funext (level_eq hL j)
  rw [he]
  exact continuous_const.mul hcont

/-- **(E1) of `ElectricLoops.zeroFluxGap_of_loopShells`, from orbit separation and a nowhere-zero
ground level.** If the Wilson loops at `y₀` separate the gauge orbits of the slice and `φ_{g₀}` has
no zero, then every excited level is in the `L²` closure of the span of the loop states of
`Ω = φ_{g₀}`. -/
theorem hgen_of_separation {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (y₀ : TT i (Tr n i))
    (hsep : ∀ V V' : Slice n i, (∀ C : Loop i (Tr n i), C.base = y₀ → C.wl V = C.wl V') →
      ∃ h : TT i (Tr n i) → SUN.SU 2, V' = gauge h V)
    (hΩ : ∀ V, φ g₀ V ≠ 0) :
    ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))) := by
  intro j hj
  have h1 : ∫ V, φ g₀ V ^ 2 ∂(hSN 2 n i) = 1 := by
    simpa only [sq] using hL.norm g₀
  refine mem_closure_span_allLoops y₀ (continuous_level hβ hL hm g₀) hΩ h1
    (continuous_level hβ hL hm j) (hL.orth g₀ j (Ne.symm hj)) (fun V V' hW => ?_) _
  obtain ⟨h, rfl⟩ := hsep V V' hW
  rw [level_gauge hL j h V, level_gauge hL g₀ h V]

end Levels

/-! ## 5. Quaternion families with the same traces are conjugate -/

section Quat

open Quaternion

local notation "Hq" => Quaternion ℝ

theorem re_mul_comm (x y : Hq) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]; ring

theorem re_conj {g : Hq} (hg : g ≠ 0) (x : Hq) : (g * x * g⁻¹).re = x.re := by
  rw [mul_assoc, re_mul_comm, mul_assoc, inv_mul_cancel₀ hg, mul_one]

theorem conj_mul {g : Hq} (hg : g ≠ 0) (x y : Hq) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left₀ hg]

theorem re_coe_mul (r : ℝ) (x : Hq) : ((r : Hq) * x).re = r * x.re := by
  simp [Quaternion.re_mul]

/-- A pure quaternion squares to `−|x|²`. -/
theorem pure_mul_self {x : Hq} (hx : x.re = 0) : x * x = -((normSq x : ℝ) : Hq) := by
  ext <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe,
      Quaternion.normSq_def', hx] <;> ring

theorem normSq_pure {x : Hq} (hx : x.re = 0) : normSq x = -(x * x).re := by
  rw [pure_mul_self hx, Quaternion.re_neg, Quaternion.re_coe, neg_neg]

/-- Orthogonal pure quaternions anticommute. -/
theorem anticomm {x y : Hq} (hx : x.re = 0) (hy : y.re = 0) (h : (x * y).re = 0) :
    y * x = -(x * y) := by
  have h' := h
  simp only [Quaternion.re_mul, hx, hy] at h'
  ext <;>
    simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg, hx, hy] <;>
    linarith

/-- Commuting pure quaternions have a real product. -/
theorem comm_real {x y : Hq} (hx : x.re = 0) (hy : y.re = 0) (h : x * y = y * x) :
    x * y = (((x * y).re : ℝ) : Hq) := by
  have hI := congrArg QuaternionAlgebra.imI h
  have hJ := congrArg QuaternionAlgebra.imJ h
  have hK := congrArg QuaternionAlgebra.imK h
  simp only [Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hx, hy] at hI hJ hK
  ext <;>
    simp only [Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hx, hy] <;>
    linarith

/-- **Alignment, generic case**: `g = |p|² − q p` carries `p` to `q` when `q ≠ −p`. -/
theorem align_gen {p q : Hq} (hp : p.re = 0) (hq : q.re = 0) (hp0 : p ≠ 0)
    (hn : normSq p = normSq q) (hne : q ≠ -p) :
    ((normSq p : ℝ) : Hq) - q * p ≠ 0 ∧
      (((normSq p : ℝ) : Hq) - q * p) * p = q * (((normSq p : ℝ) : Hq) - q * p) := by
  have hpp := pure_mul_self hp
  have hqq := pure_mul_self hq
  have hcomm : ∀ (r : ℝ) (z : Hq), (r : Hq) * z = z * (r : Hq) := fun r z =>
    Quaternion.coe_commutes r z
  have hmain : (((normSq p : ℝ) : Hq) - q * p) * p = ((normSq p : ℝ) : Hq) * (p + q) := by
    rw [sub_mul, mul_assoc, hpp, mul_neg, sub_neg_eq_add, mul_add, hcomm _ q]
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, zero_mul] at hmain
    have hn0 : ((normSq p : ℝ) : Hq) ≠ 0 := by
      rw [Ne, ← Quaternion.coe_zero, Quaternion.coe_inj, Quaternion.normSq_eq_zero]; exact hp0
    have := (mul_eq_zero.mp hmain.symm).resolve_left hn0
    exact hne (eq_neg_of_add_eq_zero_right this)
  · rw [hmain, mul_sub, ← mul_assoc, hqq, ← hn, neg_mul, sub_neg_eq_add, mul_add, hcomm _ q,
      add_comm]

theorem coe_ne_zero {r : ℝ} (hr : r ≠ 0) : ((r : ℝ) : Hq) ≠ 0 := by
  rw [Ne, ← Quaternion.coe_zero, Quaternion.coe_inj]; exact hr

/-- The pure part of `p e` is a pure quaternion orthogonal to `p`. -/
theorem re_im_mul_mul {p e : Hq} (hp : p.re = 0) (he : e.re = 0) : ((p * e).im * p).re = 0 := by
  simp only [Quaternion.re_mul, Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im,
    Quaternion.imK_im, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hp, he]
  ring

/-- **Alignment**: two pure quaternions of one norm are conjugate. -/
theorem align {p q : Hq} (hp : p.re = 0) (hq : q.re = 0) (hp0 : p ≠ 0)
    (hn : normSq p = normSq q) : ∃ g : Hq, g ≠ 0 ∧ g * p = q * g := by
  by_cases hne : q = -p
  · subst hne
    let i' : Hq := ⟨0, 1, 0, 0⟩
    let j' : Hq := ⟨0, 0, 1, 0⟩
    have hor : (p * i').im ≠ 0 ∨ (p * j').im ≠ 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have a1 := congrArg QuaternionAlgebra.imJ h1
      have a2 := congrArg QuaternionAlgebra.imK h1
      have a3 := congrArg QuaternionAlgebra.imK h2
      simp only [Quaternion.imJ_im, Quaternion.imK_im, Quaternion.imJ_mul, Quaternion.imK_mul,
        Quaternion.imJ_zero, Quaternion.imK_zero, i', j'] at a1 a2 a3
      apply hp0
      ext <;> simp only [Quaternion.re_zero, Quaternion.imI_zero, Quaternion.imJ_zero,
        Quaternion.imK_zero, hp] <;> linarith
    have key : ∀ e : Hq, e.re = 0 → (p * e).im ≠ 0 →
        ∃ g : Hq, g ≠ 0 ∧ g * p = -p * g := by
      intro e he hne0
      refine ⟨(p * e).im, hne0, ?_⟩
      rw [anticomm hp (Quaternion.re_im _) (by rw [re_mul_comm]; exact re_im_mul_mul hp he), neg_mul]
    rcases hor with h | h
    · exact key i' rfl h
    · exact key j' rfl h
  · obtain ⟨h1, h2⟩ := align_gen hp hq hp0 hn hne
    exact ⟨_, h1, h2⟩

/-- **Alignment about an axis.** For pure `q ≠ 0` and pure `s, t` with the same component along
`q`, the same norm, and `s` not parallel to `q`, some `g ≠ 0` commutes with `q` and carries `s` to
`t`. -/
theorem align_fix {q s t : Hq} (hq : q.re = 0) (hq0 : q ≠ 0) (hs : s.re = 0) (ht : t.re = 0)
    (hqs : (q * s).re = (q * t).re) (hn : normSq s = normSq t) (hpar : (q * s).im ≠ 0) :
    ∃ g : Hq, g ≠ 0 ∧ g * q = q * g ∧ g * s = t * g := by
  have hcomm : ∀ (r : ℝ) (z : Hq), (r : Hq) * z = z * (r : Hq) := fun r z =>
    Quaternion.coe_commutes r z
  set n := normSq q with hndef
  have hnpos : n ≠ 0 := by rw [hndef, Ne, Quaternion.normSq_eq_zero]; exact hq0
  set α : ℝ := -(q * s).re / n with hα
  obtain ⟨s', hs'⟩ : ∃ x : Hq, x = s - (α : Hq) * q := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ x : Hq, x = t - (α : Hq) * q := ⟨_, rfl⟩
  have hqq := pure_mul_self hq
  have hs'r : s'.re = 0 := by rw [hs', Quaternion.re_sub, re_coe_mul, hs, hq]; ring
  have ht'r : t'.re = 0 := by rw [ht', Quaternion.re_sub, re_coe_mul, ht, hq]; ring
  have hqs'0 : (q * s').re = 0 := by
    rw [hs', mul_sub, ← mul_assoc, ← hcomm, mul_assoc, hqq, Quaternion.re_sub, re_coe_mul,
      Quaternion.re_neg, Quaternion.re_coe, hα]
    field_simp
    ring
  have hqt'0 : (q * t').re = 0 := by
    rw [ht', mul_sub, ← mul_assoc, ← hcomm, mul_assoc, hqq, Quaternion.re_sub, re_coe_mul,
      Quaternion.re_neg, Quaternion.re_coe, hα, ← hqs]
    field_simp
    ring
  have hn' : normSq s' = normSq t' := by
    rw [normSq_pure hs'r, normSq_pure ht'r, hs', ht']
    have e : ∀ x : Hq, ((x - (α : Hq) * q) * (x - (α : Hq) * q)).re
        = (x * x).re - 2 * α * (q * x).re + α ^ 2 * (q * q).re := by
      intro x
      simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
        Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
        Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe]
      ring
    rw [e, e, hqs]
    have hss : (s * s).re = (t * t).re := by
      rw [← neg_neg (s * s).re, ← normSq_pure hs, hn, normSq_pure ht, neg_neg]
    rw [hss]
  have hs'0 : s' ≠ 0 := by
    intro h0
    apply hpar
    have : s = (α : Hq) * q := by rw [← sub_eq_zero, ← hs']; exact h0
    rw [this, ← mul_assoc, ← hcomm, mul_assoc, hqq]
    ext <;> simp
  have hsplit : s = (α : Hq) * q + s' := by rw [hs']; abel
  have htsplit : t = (α : Hq) * q + t' := by rw [ht']; abel
  have hq_s' : s' * q = -(q * s') := anticomm hq hs'r hqs'0
  have hq_t' : t' * q = -(q * t') := anticomm hq ht'r hqt'0
  by_cases hne : t' = -s'
  · refine ⟨q, hq0, rfl, ?_⟩
    rw [hsplit, htsplit, hne, mul_add, add_mul, neg_mul, hq_s', neg_neg, ← mul_assoc, ← hcomm,
      mul_assoc]
  · obtain ⟨hg0, hg⟩ := align_gen hs'r ht'r hs'0 hn' hne
    refine ⟨_, hg0, ?_, ?_⟩
    · rw [sub_mul, mul_sub, ← hcomm, mul_assoc, hq_s', mul_neg, ← mul_assoc, hq_t', neg_mul,
        neg_neg, mul_assoc]
    · have hgq : (((normSq s' : ℝ) : Hq) - t' * s') * q = q * (((normSq s' : ℝ) : Hq) - t' * s') := by
        rw [sub_mul, mul_sub, ← hcomm, mul_assoc, hq_s', mul_neg, ← mul_assoc, hq_t', neg_mul,
          neg_neg, mul_assoc]
      have hαg : (((normSq s' : ℝ) : Hq) - t' * s') * ((α : Hq) * q)
          = (α : Hq) * q * (((normSq s' : ℝ) : Hq) - t' * s') := by
        rw [← mul_assoc, ← hcomm α, mul_assoc, hgq, ← mul_assoc]
      rw [hsplit, htsplit, mul_add, hg, add_mul, hαg]

/-- A pure quaternion with a real product against `q ≠ 0` is fixed by that product and its norm. -/
theorem parallel {q x v : Hq} (hq0 : q ≠ 0) (hpar : (q * x).im = 0)
    (h1 : (q * x).re = (q * v).re) (hn : normSq x = normSq v) : x = v := by
  have hqx : q * x = (((q * x).re : ℝ) : Hq) := by
    conv_lhs => rw [← Quaternion.re_add_im (q * x)]
    rw [hpar, add_zero]
  have hns : normSq (q * v) = normSq (q * x) := by rw [map_mul, map_mul, hn]
  rw [Quaternion.normSq_def', hqx, Quaternion.normSq_coe, ← h1] at hns
  have hI : (q * v).imI = 0 := by nlinarith [sq_nonneg (q * v).imI, sq_nonneg (q * v).imJ, sq_nonneg (q * v).imK]
  have hJ : (q * v).imJ = 0 := by nlinarith [sq_nonneg (q * v).imI, sq_nonneg (q * v).imJ, sq_nonneg (q * v).imK]
  have hK : (q * v).imK = 0 := by nlinarith [sq_nonneg (q * v).imI, sq_nonneg (q * v).imJ, sq_nonneg (q * v).imK]
  have hqv : q * v = q * x := by
    rw [hqx]
    ext
    · simp only [Quaternion.re_coe]; exact h1.symm
    · simp only [Quaternion.imI_coe]; exact hI
    · simp only [Quaternion.imJ_coe]; exact hJ
    · simp only [Quaternion.imK_coe]; exact hK
  exact (mul_left_cancel₀ hq0 hqv).symm

/-- **A pure quaternion is fixed by its products with `p`, `t` and `p t`** when `p`, `t` are not
parallel. -/
theorem determined {p t x v : Hq} (hp : p.re = 0) (ht : t.re = 0) (hx : x.re = 0) (hv : v.re = 0)
    (hpt : (p * t).im ≠ 0) (h1 : (p * x).re = (p * v).re) (h2 : (t * x).re = (t * v).re)
    (h3 : (p * t * x).re = (p * t * v).re) : x = v := by
  have hcomm : ∀ (r : ℝ) (z : Hq), (r : Hq) * z = z * (r : Hq) := fun r z =>
    Quaternion.coe_commutes r z
  obtain ⟨y, hy'⟩ : ∃ y : Hq, y = x - v := ⟨_, rfl⟩
  have hy : y.re = 0 := by rw [hy', Quaternion.re_sub, hx, hv, sub_self]
  have hpy : (p * y).re = 0 := by rw [hy', mul_sub, Quaternion.re_sub, h1, sub_self]
  have hty : (t * y).re = 0 := by rw [hy', mul_sub, Quaternion.re_sub, h2, sub_self]
  have hpty : (p * t * y).re = 0 := by rw [hy', mul_sub, Quaternion.re_sub, h3, sub_self]
  have yp : y * p = -(p * y) := anticomm hp hy hpy
  have yt : y * t = -(t * y) := anticomm ht hy hty
  have hcomm_pt : y * (p * t) = p * t * y := by
    rw [← mul_assoc, yp, neg_mul, mul_assoc, yt, mul_neg, neg_neg, mul_assoc]
  obtain ⟨c, hc'⟩ : ∃ c : Hq, c = (p * t).im := ⟨_, rfl⟩
  have hc : c.re = 0 := by rw [hc']; rfl
  have hcdef : c = p * t - (((p * t).re : ℝ) : Hq) := by rw [hc', Quaternion.sub_re_self]
  have hyc : c * y = y * c := by
    rw [hcdef, sub_mul, mul_sub, hcomm_pt, hcomm]
  have hcy : (c * y).re = 0 := by
    rw [hcdef, sub_mul, Quaternion.re_sub, re_coe_mul, hy, hpty]; ring
  have h0 : c * y = 0 := by
    rw [comm_real hc hy hyc, hcy]; rfl
  have hc0 : c ≠ 0 := by rw [hc']; exact hpt
  have : y = 0 := (mul_eq_zero.mp h0).resolve_left hc0
  rw [hy'] at this
  exact sub_eq_zero.mp this

/-- The invariants of a family of pure quaternions against another. -/
structure Match {κ : Type*} (u v : κ → Hq) : Prop where
  pu : ∀ k, (u k).re = 0
  pv : ∀ k, (v k).re = 0
  two : ∀ k l, (u k * u l).re = (v k * v l).re
  three : ∀ k l m, (u k * u l * u m).re = (v k * v l * v m).re

/-- Conjugating `u` keeps the invariants. -/
theorem Match.conj {κ : Type*} {u v : κ → Hq} (h : Match u v) {g : Hq} (hg : g ≠ 0) :
    Match (fun k => g * u k * g⁻¹) v where
  pu k := by rw [re_conj hg, h.pu k]
  pv := h.pv
  two k l := by
    show (g * u k * g⁻¹ * (g * u l * g⁻¹)).re = _
    rw [← conj_mul hg, re_conj hg, h.two]
  three k l m := by
    show (g * u k * g⁻¹ * (g * u l * g⁻¹) * (g * u m * g⁻¹)).re = _
    rw [← conj_mul hg, ← conj_mul hg, re_conj hg, h.three]

theorem conj_back {κ : Type*} {u v : κ → Hq} {g g' : Hq} (hg : g ≠ 0) (hg' : g' ≠ 0)
    (h : ∀ k, g' * (g * u k * g⁻¹) = v k * g') :
    ∃ g'' : Hq, g'' ≠ 0 ∧ ∀ k, g'' * u k = v k * g'' := by
  refine ⟨g' * g, mul_ne_zero hg' hg, fun k => ?_⟩
  have e : g * u k = g * u k * g⁻¹ * g := by rw [mul_assoc (g * u k), inv_mul_cancel₀ hg, mul_one]
  rw [mul_assoc, e, ← mul_assoc, h k, mul_assoc]

theorem Match.normSq_eq {κ : Type*} {u v : κ → Hq} (h : Match u v) (k : κ) :
    normSq (u k) = normSq (v k) := by
  rw [normSq_pure (h.pu k), normSq_pure (h.pv k), h.two]

/-- The case where `u` and `v` already agree at one nonzero entry. -/
theorem exists_conj_of_eq {κ : Type*} {u v : κ → Hq} (h : Match u v) {k₁ : κ} {q : Hq}
    (hq0 : q ≠ 0) (hu1 : u k₁ = q) (hv1 : v k₁ = q) :
    ∃ g : Hq, g ≠ 0 ∧ ∀ k, g * u k = v k * g := by
  have hq : q.re = 0 := hu1 ▸ h.pu k₁
  have h2q : ∀ k, (q * u k).re = (q * v k).re := fun k => by
    have := h.two k₁ k; rwa [hu1, hv1] at this
  by_cases hpar : ∀ k, (q * u k).im = 0
  · refine ⟨1, one_ne_zero, fun k => ?_⟩
    rw [parallel hq0 (hpar k) (h2q k) (h.normSq_eq k), one_mul, mul_one]
  · push Not at hpar
    obtain ⟨k₂, hk₂⟩ := hpar
    obtain ⟨g, hg0, hgq, hgs⟩ := align_fix hq hq0 (h.pu k₂) (h.pv k₂) (h2q k₂) (h.normSq_eq k₂) hk₂
    have h' := h.conj hg0
    have hgq' : g * q * g⁻¹ = q := by rw [hgq, mul_assoc, mul_inv_cancel₀ hg0, mul_one]
    have hgs' : g * u k₂ * g⁻¹ = v k₂ := by rw [hgs, mul_assoc, mul_inv_cancel₀ hg0, mul_one]
    have hpt : (q * v k₂).im ≠ 0 := by
      intro him
      apply hk₂
      have hqt : q * v k₂ = (((q * v k₂).re : ℝ) : Hq) := by
        conv_lhs => rw [← Quaternion.re_add_im (q * v k₂)]
        rw [him, add_zero]
      have e : g * (q * u k₂) = q * v k₂ * g := by
        rw [← mul_assoc, hgq, mul_assoc, hgs, ← mul_assoc]
      obtain ⟨r, hr⟩ : ∃ r : ℝ, q * v k₂ = (r : Hq) := ⟨_, hqt⟩
      have e2 : g * (q * u k₂) = g * (r : Hq) := by
        rw [e, hr, Quaternion.coe_commutes]
      have := mul_left_cancel₀ hg0 e2
      rw [this, Quaternion.im_coe]
    refine ⟨g, hg0, fun k => ?_⟩
    have hk : g * u k * g⁻¹ = v k := by
      refine determined hq (h.pv k₂) (h'.pu k) (h.pv k) hpt ?_ ?_ ?_
      · have := h'.two k₁ k
        simp only [hu1, hgq', hv1] at this
        exact this
      · have := h'.two k₂ k
        simp only [hgs'] at this
        exact this
      · have := h'.three k₁ k₂ k
        simp only [hu1, hgq', hv1, hgs'] at this
        exact this
    rw [← hk, mul_assoc, inv_mul_cancel₀ hg0, mul_one]

/-- **Pure quaternion families with the same two- and three-fold products are conjugate.** -/
theorem exists_conj_pure {κ : Type*} {u v : κ → Hq} (h : Match u v) :
    ∃ g : Hq, g ≠ 0 ∧ ∀ k, g * u k = v k * g := by
  by_cases h0 : ∀ k, u k = 0
  · refine ⟨1, one_ne_zero, fun k => ?_⟩
    have hv0 : v k = 0 := by
      rw [← Quaternion.normSq_eq_zero, ← h.normSq_eq k, h0 k, map_zero]
    rw [h0 k, hv0, mul_zero, zero_mul]
  · push Not at h0
    obtain ⟨k₁, hk₁⟩ := h0
    obtain ⟨g, hg0, hg⟩ := align (h.pu k₁) (h.pv k₁) hk₁ (h.normSq_eq k₁)
    have h' := h.conj hg0
    have hu1 : g * u k₁ * g⁻¹ = v k₁ := by rw [hg, mul_assoc, mul_inv_cancel₀ hg0, mul_one]
    have hq0 : v k₁ ≠ 0 := by
      rw [← Quaternion.normSq_ne_zero, ← h.normSq_eq k₁, Quaternion.normSq_ne_zero]; exact hk₁
    obtain ⟨g', hg'0, hg'⟩ := exists_conj_of_eq h' hq0 hu1 rfl
    exact conj_back hg0 hg'0 hg'

theorem re_im_mul_im (x y : Hq) : (x.im * y.im).re = (x * y).re - x.re * y.re := by
  simp only [Quaternion.re_mul, Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im,
    Quaternion.imK_im]
  ring

theorem re_im_mul_im_mul_im (x y z : Hq) : (x.im * y.im * z.im).re = (x * y * z).re
    - x.re * y.re * z.re - x.re * (y.im * z.im).re - y.re * (x.im * z.im).re
    - z.re * (x.im * y.im).re := by
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im]
  ring

/-- **Quaternion families with the same one-, two- and three-fold real parts are conjugate.** -/
theorem exists_conj {κ : Type*} {a b : κ → Hq} (h1 : ∀ k, (a k).re = (b k).re)
    (h2 : ∀ k l, (a k * a l).re = (b k * b l).re)
    (h3 : ∀ k l m, (a k * a l * a m).re = (b k * b l * b m).re) :
    ∃ g : Hq, g ≠ 0 ∧ ∀ k, g * a k = b k * g := by
  have hM : Match (fun k => (a k).im) (fun k => (b k).im) := by
    have t2 : ∀ k l, ((a k).im * (a l).im).re = ((b k).im * (b l).im).re := fun k l => by
      rw [re_im_mul_im, re_im_mul_im, h2, h1, h1]
    refine ⟨fun k => Quaternion.re_im _, fun k => Quaternion.re_im _, t2, fun k l m => ?_⟩
    show ((a k).im * (a l).im * (a m).im).re = ((b k).im * (b l).im * (b m).im).re
    rw [re_im_mul_im_mul_im, re_im_mul_im_mul_im, h3, h1, h1, h1, t2, t2, t2]
  obtain ⟨g, hg0, hg⟩ := exists_conj_pure hM
  refine ⟨g, hg0, fun k => ?_⟩
  have hgk : g * (a k).im = (b k).im * g := hg k
  rw [← Quaternion.re_add_im (a k), ← Quaternion.re_add_im (b k), mul_add, add_mul, hgk, h1,
    ← Quaternion.coe_commutes]

end Quat

/-! ## 6. `SU(2)` as the unit quaternions -/

section Bridge

local notation "Hq" => Quaternion ℝ
local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ

/-- The entries of an `SU(2)` matrix: `[[a, b], [−b̄, ā]]`. -/
theorem su2_entries (X : SUN.SU 2) :
    (X : M2) 1 1 = (starRingEnd ℂ) ((X : M2) 0 0) ∧
      (X : M2) 1 0 = -(starRingEnd ℂ) ((X : M2) 0 1) := by
  have h := su2_star_eq_adj X
  have h00 := congrArg (fun M : M2 => M 0 0) h
  have h01 := congrArg (fun M : M2 => M 0 1) h
  simp [Matrix.star_apply, Matrix.adjugate_fin_two] at h00 h01
  refine ⟨h00.symm, ?_⟩
  have := congrArg (starRingEnd ℂ) h01
  simpa using this

/-- The quaternion of an `SU(2)` matrix. -/
def toQ (X : SUN.SU 2) : Hq :=
  ⟨((X : M2) 0 0).re, ((X : M2) 0 0).im, ((X : M2) 0 1).re, ((X : M2) 0 1).im⟩

theorem toQ_mul (X Y : SUN.SU 2) : toQ (X * Y) = toQ X * toQ Y := by
  have hY := su2_entries Y
  have e : ((X * Y : SUN.SU 2) : M2) = (X : M2) * (Y : M2) := rfl
  ext <;> simp only [toQ, e, Matrix.mul_apply, Fin.sum_univ_two, hY.1, hY.2, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im] <;> ring

theorem re_trace_eq (X : SUN.SU 2) : (Matrix.trace (X : M2)).re = 2 * (toQ X).re := by
  rw [Matrix.trace_fin_two, (su2_entries X).1, Complex.add_re, Complex.conj_re]
  simp only [toQ]; ring

theorem toQ_injective : Function.Injective toQ := by
  intro X Y h
  have hr := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  simp only [toQ] at hr hi hj hk
  have h00 : (X : M2) 0 0 = (Y : M2) 0 0 := Complex.ext hr hi
  have h01 : (X : M2) 0 1 = (Y : M2) 0 1 := Complex.ext hj hk
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01
  · show (X : M2) 1 0 = (Y : M2) 1 0
    rw [(su2_entries X).2, (su2_entries Y).2, h01]
  · show (X : M2) 1 1 = (Y : M2) 1 1
    rw [(su2_entries X).1, (su2_entries Y).1, h00]

theorem toQ_one : toQ 1 = 1 := by
  ext <;> simp [toQ] <;> rfl

theorem toQ_inv (X : SUN.SU 2) : toQ X⁻¹ = (toQ X)⁻¹ := by
  have h : toQ X⁻¹ * toQ X = 1 := by rw [← toQ_mul, inv_mul_cancel, toQ_one]
  exact eq_inv_of_mul_eq_one_left h

/-- The matrix of a quaternion. -/
def qMat (g : Hq) : M2 :=
  !![⟨g.re, g.imI⟩, ⟨g.imJ, g.imK⟩; ⟨-g.imJ, g.imK⟩, ⟨g.re, -g.imI⟩]

theorem qMat_mem {g : Hq} (hg : Quaternion.normSq g = 1) :
    qMat g ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Quaternion.normSq_def'] at hg
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [qMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      apply Complex.ext <;> simp <;> first | ring1 | linear_combination hg
  · rw [Matrix.det_fin_two]
    apply Complex.ext <;> simp [qMat] <;> first | ring1 | linear_combination hg

/-- The unit quaternion as an element of `SU(2)`. -/
def ofQ (g : Hq) (hg : Quaternion.normSq g = 1) : SUN.SU 2 := ⟨qMat g, qMat_mem hg⟩

theorem toQ_ofQ (g : Hq) (hg : Quaternion.normSq g = 1) : toQ (ofQ g hg) = g := by
  ext <;> simp [toQ, ofQ, qMat]

/-- **`SU(2)` families with the same traces of all products of one, two and three letters are
simultaneously conjugate.** -/
theorem su2_conj_of_traces {κ : Type*} (A B : κ → SUN.SU 2)
    (h1 : ∀ k, (Matrix.trace (A k : M2)).re = (Matrix.trace (B k : M2)).re)
    (h2 : ∀ k l, (Matrix.trace ((A k * A l : SUN.SU 2) : M2)).re
      = (Matrix.trace ((B k * B l : SUN.SU 2) : M2)).re)
    (h3 : ∀ k l m, (Matrix.trace ((A k * A l * A m : SUN.SU 2) : M2)).re
      = (Matrix.trace ((B k * B l * B m : SUN.SU 2) : M2)).re) :
    ∃ G : SUN.SU 2, ∀ k, B k = G * A k * G⁻¹ := by
  obtain ⟨g, hg0, hg⟩ := exists_conj (a := fun k => toQ (A k)) (b := fun k => toQ (B k))
    (fun k => by have := h1 k; rw [re_trace_eq, re_trace_eq] at this; linarith)
    (fun k l => by have := h2 k l; rw [re_trace_eq, re_trace_eq, toQ_mul, toQ_mul] at this; linarith)
    (fun k l m => by
      have := h3 k l m
      rw [re_trace_eq, re_trace_eq, toQ_mul, toQ_mul, toQ_mul, toQ_mul] at this; linarith)
  have hn : 0 < Quaternion.normSq g := by
    rcases (Quaternion.normSq_nonneg (a := g)).lt_or_eq with h | h
    · exact h
    · exact absurd (Quaternion.normSq_eq_zero.mp h.symm) hg0
  set c : ℝ := (Real.sqrt (Quaternion.normSq g))⁻¹ with hc
  set g' : Hq := (c : Hq) * g with hg'
  have hg'n : Quaternion.normSq g' = 1 := by
    rw [hg', map_mul, Quaternion.normSq_coe, hc, inv_pow, Real.sq_sqrt hn.le,
      inv_mul_cancel₀ hn.ne']
  have hg'0 : g' ≠ 0 := by
    rw [← Quaternion.normSq_ne_zero, hg'n]; exact one_ne_zero
  refine ⟨ofQ g' hg'n, fun k => toQ_injective ?_⟩
  rw [toQ_mul, toQ_mul, toQ_inv, toQ_ofQ]
  have hk : g' * toQ (A k) = toQ (B k) * g' := by
    rw [hg', mul_assoc, hg k, ← mul_assoc, ← mul_assoc, Quaternion.coe_commutes]
  rw [hk, mul_assoc, mul_inv_cancel₀ hg'0, mul_one]

end Bridge

/-! ## 7. Orbit separation on the slice (Giles) -/

section Giles

variable {i : Fin 4} {T : Dir i → ℕ}

/-- **Every site is reached from every other** along forward steps. -/
theorem exists_path (y₀ z : TT i T) : ∃ p : List (Step i), endpt y₀ p = z := by
  have key : ∀ l : List (Dir i), ∃ p : List (Step i), ∀ ν ∈ l, endpt y₀ p ν = z ν := by
    intro l
    induction l with
    | nil => exact ⟨[], fun ν h => absurd h List.not_mem_nil⟩
    | cons ν l ih =>
        obtain ⟨p, hp⟩ := ih
        obtain ⟨w, hw⟩ : ∃ w, w = endpt y₀ p := ⟨_, rfl⟩
        refine ⟨p ++ List.replicate ((z ν).val + T ν - (w ν).val) (ν, true), fun ν' hν' => ?_⟩
        rw [endpt_append, endpt_line, ← hw]
        by_cases hνν : ν' = ν
        · subst hνν
          rw [iterate_tsh_self]
          apply Fin.ext
          rw [iterate_finRotate_val]
          have h1 := (w ν').isLt
          have h2 := (z ν').isLt
          rw [show (w ν').val + ((z ν').val + T ν' - (w ν').val) = (z ν').val + T ν' by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt h2]
        · rw [iterate_tsh_ne ν ν' hνν, hw]
          rcases List.mem_cons.mp hν' with h | h
          · exact absurd h hνν
          · exact hp ν' h
  obtain ⟨p, hp⟩ := key Finset.univ.toList
  exact ⟨p, funext fun ν => hp ν (Finset.mem_toList.mpr (Finset.mem_univ ν))⟩

/-- A chosen path from `y₀` to `z`. -/
def path (y₀ z : TT i T) : List (Step i) := Classical.choose (exists_path y₀ z)

theorem endpt_path (y₀ z : TT i T) : endpt y₀ (path y₀ z) = z :=
  Classical.choose_spec (exists_path y₀ z)

/-- The holonomy along the chosen path from `y₀` to `z`. -/
def pathHol (y₀ z : TT i T) (V : SpT i T → SUN.SU 2) : SUN.SU 2 := wh (walk y₀ (path y₀ z)) V

/-- **The loop at `y₀` through the link `l`**: out along the path to `l`'s start, across `l`,
back along the path from `l`'s end. -/
def linkLoop (y₀ : TT i T) (l : SpT i T) : Loop i T :=
  ⟨y₀, path y₀ l.2 ++ [(l.1, true)] ++ rev (path y₀ (tsh i T l.1 l.2)), by
    rw [endpt_append, endpt_append, endpt_path]
    show endpt (tsh i T l.1 l.2) (rev (path y₀ (tsh i T l.1 l.2))) = y₀
    have h := endpt_rev y₀ (path y₀ (tsh i T l.1 l.2))
    rwa [endpt_path] at h⟩

theorem linkLoop_hol (y₀ : TT i T) (l : SpT i T) (V : SpT i T → SUN.SU 2) :
    (linkLoop y₀ l).hol V = pathHol y₀ l.2 V * V l * (pathHol y₀ (tsh i T l.1 l.2) V)⁻¹ := by
  unfold Loop.hol linkLoop pathHol
  simp only
  rw [walk_append, walk_append, wh_append, wh_append, endpt_append, endpt_path]
  have hr := wh_rev y₀ (path y₀ (tsh i T l.1 l.2)) V
  rw [endpt_path] at hr
  have hm : wh (walk l.2 [(l.1, true)]) V = V l := by simp [walk, letter, wh]
  have he : endpt l.2 [(l.1, true)] = tsh i T l.1 l.2 := by simp [endpt, next]
  rw [hm, he, hr]

/-- **Giles at `SU(2)`: the Wilson loops at one base separate the gauge orbits of the slice.** -/
theorem giles (y₀ : TT i T) (V V' : SpT i T → SUN.SU 2)
    (h : ∀ C : Loop i T, C.base = y₀ → C.wl V = C.wl V') :
    ∃ g : TT i T → SUN.SU 2, V' = gauge g V := by
  let A : SpT i T → SUN.SU 2 := fun l => (linkLoop y₀ l).hol V
  let B : SpT i T → SUN.SU 2 := fun l => (linkLoop y₀ l).hol V'
  have hb : ∀ k l : SpT i T, (linkLoop y₀ l).base = (linkLoop y₀ k).base := fun _ _ => rfl
  obtain ⟨G, hG⟩ := su2_conj_of_traces A B
    (fun k => h (linkLoop y₀ k) rfl)
    (fun k l => by
      have := h ((linkLoop y₀ k).comp (linkLoop y₀ l) (hb k l)) rfl
      unfold Loop.wl at this
      rwa [Loop.hol_comp, Loop.hol_comp] at this)
    (fun k l m => by
      have := h (((linkLoop y₀ k).comp (linkLoop y₀ l) (hb k l)).comp (linkLoop y₀ m) rfl) rfl
      unfold Loop.wl at this
      rwa [Loop.hol_comp, Loop.hol_comp, Loop.hol_comp, Loop.hol_comp] at this)
  refine ⟨fun z => (pathHol y₀ z V')⁻¹ * G * pathHol y₀ z V, funext fun l => ?_⟩
  have hBl : B l = pathHol y₀ l.2 V' * V' l * (pathHol y₀ (tsh i T l.1 l.2) V')⁻¹ :=
    linkLoop_hol y₀ l V'
  have hAl : A l = pathHol y₀ l.2 V * V l * (pathHol y₀ (tsh i T l.1 l.2) V)⁻¹ :=
    linkLoop_hol y₀ l V
  have e : V' l = (pathHol y₀ l.2 V')⁻¹ * B l * pathHol y₀ (tsh i T l.1 l.2) V' := by
    rw [hBl]; group
  rw [e, hG l, hAl]
  unfold ElectricLoops.gauge
  group

end Giles

/-! ## 8. The form of a kernel against an orthonormal eigenfamily -/

section Form

open MeasureTheory Filter
open MassGap.KernelPower (hs Bdd integrable_of_bdd measurable_integral_right sq_integral_mul_le
  abs_integral_le)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Bounded and measurable. -/
def BM (f : X → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C

theorem BM.integrable {f : X → ℝ} (h : BM f) : Integrable f μ := by
  obtain ⟨hm, C, hC⟩ := h; exact integrable_of_bdd hm hC

theorem BM.mul {f g : X → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, Cf * Cg, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCg x) (abs_nonneg _) ((abs_nonneg _).trans (hCf x))

theorem BM.add {f g : X → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun x => (abs_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩

theorem BM.sub {f g : X → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun x => (abs_sub _ _).trans (add_le_add (hCf x) (hCg x))⟩

theorem BM.const (c : ℝ) : BM (fun _ : X => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem BM.const_mul (c : ℝ) {f : X → ℝ} (hf : BM f) : BM (fun x => c * f x) :=
  (BM.const c).mul hf

theorem BM.sum {ι : Type*} (S : Finset ι) {F : ι → X → ℝ} (h : ∀ j, BM (F j)) :
    BM (fun x => ∑ j ∈ S, F j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using BM.const (X := X) 0
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a).add ih

theorem BM.pow2 {f : X → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  have e : (fun x => f x ^ 2) = fun x => f x * f x := funext fun x => _root_.sq (f x)
  rw [e]; exact hf.mul hf

/-- The row integral `x ↦ ∫ k(x, y) f(y)` of a bounded kernel against a bounded function. -/
theorem BM.row {k : X → X → ℝ} (hk : Bdd k) {f : X → ℝ} (hf : BM f) :
    BM (fun x => ∫ y, k x y * f y ∂μ) := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  obtain ⟨hfm, Cf, hCf⟩ := hf
  refine ⟨measurable_integral_right (hk.meas.mul (hfm.comp measurable_snd)), Ck * Cf, fun x => ?_⟩
  refine abs_integral_le fun y => ?_
  rw [abs_mul]
  exact mul_le_mul (hCk x y) (hCf y) (abs_nonneg _) ((abs_nonneg _).trans (hCk x y))

theorem bm_row_fun {k : X → X → ℝ} (hk : Bdd k) (x : X) : BM (k x) := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  exact ⟨hk.row x, Ck, hCk x⟩

/-- **Expansion against an orthonormal family**:
`∫ (F − Σ a_j φ_j)² = ∫ F² − 2 Σ a_j ∫ F φ_j + Σ a_j²`. -/
theorem integral_sub_sum_sq {ι : Type*} [DecidableEq ι] (S : Finset ι) {φ : ι → X → ℝ}
    (hφ : ∀ j, BM (φ j)) (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0)
    {F : X → ℝ} (hF : BM F) (a : ι → ℝ) :
    ∫ x, (F x - ∑ j ∈ S, a j * φ j x) ^ 2 ∂μ
      = ∫ x, F x ^ 2 ∂μ - 2 * ∑ j ∈ S, a j * ∫ x, F x * φ j x ∂μ + ∑ j ∈ S, a j ^ 2 := by
  have e : ∀ x, (F x - ∑ j ∈ S, a j * φ j x) ^ 2
      = F x ^ 2 - 2 * ∑ j ∈ S, a j * (F x * φ j x)
        + ∑ j ∈ S, ∑ l ∈ S, a j * a l * (φ j x * φ l x) := by
    intro x
    have h1 : (F x - ∑ j ∈ S, a j * φ j x) ^ 2 = F x ^ 2 - 2 * (F x * ∑ j ∈ S, a j * φ j x)
        + (∑ j ∈ S, a j * φ j x) * (∑ j ∈ S, a j * φ j x) := by ring
    rw [h1, Finset.mul_sum, Finset.sum_mul_sum]
    congr 1
    · congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
  have hFφ : ∀ j, BM (fun x => F x * φ j x) := fun j => hF.mul (hφ j)
  have hφφ : ∀ j l, BM (fun x => φ j x * φ l x) := fun j l => (hφ j).mul (hφ l)
  have i1 : Integrable (fun x => F x ^ 2) μ := hF.pow2.integrable
  have i2 : Integrable (fun x => 2 * ∑ j ∈ S, a j * (F x * φ j x)) μ :=
    (BM.const_mul 2 (BM.sum S fun j => BM.const_mul (a j) (hFφ j))).integrable
  have i3 : Integrable (fun x => ∑ j ∈ S, ∑ l ∈ S, a j * a l * (φ j x * φ l x)) μ :=
    (BM.sum S fun j => BM.sum S fun l => BM.const_mul (a j * a l) (hφφ j l)).integrable
  simp_rw [e]
  rw [integral_add (f := fun x => F x ^ 2 - 2 * ∑ j ∈ S, a j * (F x * φ j x))
      (g := fun x => ∑ j ∈ S, ∑ l ∈ S, a j * a l * (φ j x * φ l x)) (i1.sub i2) i3,
    integral_sub (f := fun x => F x ^ 2) (g := fun x => 2 * ∑ j ∈ S, a j * (F x * φ j x)) i1 i2,
    integral_const_mul,
    integral_finsetSum _ (fun j _ => (BM.const_mul (a j) (hFφ j)).integrable),
    integral_finsetSum _ (fun j _ => (BM.sum S fun l =>
      BM.const_mul (a j * a l) (hφφ j l)).integrable)]
  congr 1
  · congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_finsetSum _ (fun l _ => (BM.const_mul (a j * a l) (hφφ j l)).integrable)]
    simp_rw [integral_const_mul, horth]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, if_pos hj]
    ring

variable {ι : Type*} [DecidableEq ι] {k : X → X → ℝ} {c : ι → ℝ} {φ : ι → X → ℝ}

/-- The kernel with the levels of `S` removed: `k − Σ_{j ∈ S} c_j φ_j ⊗ φ_j`. -/
def remS (k : X → X → ℝ) (c : ι → ℝ) (φ : ι → X → ℝ) (S : Finset ι) : X → X → ℝ :=
  fun x y => k x y - ∑ j ∈ S, c j * φ j x * φ j y

omit [DecidableEq ι] in
theorem bdd_remS (hk
 : Bdd k) (hφ : ∀ j, BM (φ j)) (S : Finset ι) : Bdd (remS k c φ S) := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  choose B hB using fun j => (hφ j).2
  refine ⟨hk.meas.sub (Finset.measurable_sum S fun j _ =>
      ((measurable_const.mul ((hφ j).1.comp measurable_fst)).mul ((hφ j).1.comp measurable_snd))),
    Ck + ∑ j ∈ S, |c j| * B j * B j, fun x y => ?_⟩
  unfold remS
  refine (abs_sub _ _).trans (add_le_add (hCk x y) ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)))
  rw [abs_mul, abs_mul]
  have h0 : 0 ≤ B j := (abs_nonneg _).trans (hB j x)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hB j x) (abs_nonneg _)) (hB j y) (abs_nonneg _)
    (by positivity)

theorem integral_remS_sq (hk : Bdd k) (hφ : ∀ j, BM (φ j))
    (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0)
    (heig : ∀ j z, ∫ y, k z y * φ j y ∂μ = c j * φ j z) (S : Finset ι) (x : X) :
    ∫ y, remS k c φ S x y ^ 2 ∂μ = ∫ y, k x y ^ 2 ∂μ - ∑ j ∈ S, (c j * φ j x) ^ 2 := by
  unfold remS
  rw [integral_sub_sum_sq S hφ horth (bm_row_fun hk x) (fun j => c j * φ j x)]
  simp_rw [heig]
  have : ∑ j ∈ S, c j * φ j x * (c j * φ j x) = ∑ j ∈ S, (c j * φ j x) ^ 2 :=
    Finset.sum_congr rfl fun j _ => (_root_.sq _).symm
  rw [this]; ring

theorem bm_row_sq (hk : Bdd k) : BM (fun x => ∫ y, k x y ^ 2 ∂μ) := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  refine ⟨measurable_integral_right (hk.meas.pow_const 2), Ck ^ 2, fun x => ?_⟩
  refine abs_integral_le fun y => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hCk x y) 2

/-- **Removing levels from the Hilbert–Schmidt sum**: `hs k = Σ_{j ∈ S} c_j² + hs(k − Σ_S)`. -/
theorem hs_remS (hk : Bdd k) (hφ : ∀ j, BM (φ j))
    (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0)
    (heig : ∀ j z, ∫ y, k z y * φ j y ∂μ = c j * φ j z) (S : Finset ι) :
    hs μ k = ∑ j ∈ S, c j ^ 2 + hs μ (remS k c φ S) := by
  have e : hs μ (remS k c φ S) = ∫ x, (∫ y, k x y ^ 2 ∂μ - ∑ j ∈ S, (c j * φ j x) ^ 2) ∂μ := by
    unfold hs
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      integral_remS_sq hk hφ horth heig S x)
  have hsum : BM (fun x => ∑ j ∈ S, (c j * φ j x) ^ 2) :=
    BM.sum S fun j => (BM.const_mul (c j) (hφ j)).pow2
  rw [e, integral_sub (bm_row_sq hk).integrable hsum.integrable,
    integral_finsetSum _ (fun j _ => (BM.const_mul (c j) (hφ j)).pow2.integrable)]
  have : ∀ j, ∫ x, (c j * φ j x) ^ 2 ∂μ = c j ^ 2 := fun j => by
    have h := horth j j
    rw [if_pos rfl] at h
    simp_rw [mul_pow, _root_.sq (φ j _)]
    rw [integral_const_mul, h, mul_one]
  simp_rw [this]
  unfold hs
  ring

/-- The quadratic form `∫ f(x) ∫ k(x, y) f(y)`. -/
def qform (μ : Measure X) (k : X → X → ℝ) (f : X → ℝ) : ℝ := ∫ x, f x * ∫ y, k x y * f y ∂μ ∂μ

omit [DecidableEq ι] in
theorem qform_remS (hk : Bdd k) (hφ : ∀ j, BM (φ j)) (S : Finset ι) {f : X → ℝ} (hf : BM f) :
    qform μ k f = ∑ j ∈ S, c j * (∫ y, φ j y * f y ∂μ) ^ 2 + qform μ (remS k c φ S) f := by
  have hin : ∀ x, ∫ y, remS k c φ S x y * f y ∂μ
      = ∫ y, k x y * f y ∂μ - ∑ j ∈ S, c j * φ j x * ∫ y, φ j y * f y ∂μ := by
    intro x
    have e : (fun y => remS k c φ S x y * f y)
        = fun y => k x y * f y - ∑ j ∈ S, c j * φ j x * (φ j y * f y) := by
      funext y; unfold remS; rw [sub_mul, Finset.sum_mul]
      congr 1; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_sub ((bm_row_fun hk x).mul hf).integrable
      (BM.sum S fun j => BM.const_mul _ ((hφ j).mul hf)).integrable,
      integral_finsetSum _ (fun j _ => (BM.const_mul _ ((hφ j).mul hf)).integrable)]
    simp_rw [integral_const_mul]
  have hrow : BM (fun x => ∫ y, k x y * f y ∂μ) := BM.row hk hf
  unfold qform
  simp_rw [hin]
  have e2 : (fun x => f x * (∫ y, k x y * f y ∂μ - ∑ j ∈ S, c j * φ j x * ∫ y, φ j y * f y ∂μ))
      = fun x => f x * ∫ y, k x y * f y ∂μ
        - ∑ j ∈ S, (c j * ∫ y, φ j y * f y ∂μ) * (φ j x * f x) := by
    funext x; rw [mul_sub, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e2, integral_sub (hf.mul hrow).integrable
    (BM.sum S fun j => BM.const_mul _ ((hφ j).mul hf)).integrable,
    integral_finsetSum _ (fun j _ => (BM.const_mul _ ((hφ j).mul hf)).integrable)]
  simp_rw [integral_const_mul]
  have : ∑ j ∈ S, c j * (∫ y, φ j y * f y ∂μ) * ∫ x, φ j x * f x ∂μ
      = ∑ j ∈ S, c j * (∫ y, φ j y * f y ∂μ) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

/-- **The form of a kernel is bounded by its Hilbert–Schmidt norm.** -/
theorem abs_qform_le {r : X → X → ℝ} (hr : Bdd r) {f : X → ℝ} (hf : BM f) :
    |qform μ r f| ≤ Real.sqrt (hs μ r) * ∫ x, f x ^ 2 ∂μ := by
  set g : X → ℝ := fun x => ∫ y, r x y * f y ∂μ with hg
  have hgB : BM g := BM.row hr hf
  have hF0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h1 : qform μ r f ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ :=
    sq_integral_mul_le hf.pow2.integrable hgB.pow2.integrable (hf.mul hgB).integrable
  have h2 : ∀ x, g x ^ 2 ≤ (∫ y, r x y ^ 2 ∂μ) * ∫ y, f y ^ 2 ∂μ := fun x =>
    sq_integral_mul_le (bm_row_fun hr x).pow2.integrable hf.pow2.integrable
      ((bm_row_fun hr x).mul hf).integrable
  have h3 : ∫ x, g x ^ 2 ∂μ ≤ hs μ r * ∫ y, f y ^ 2 ∂μ := by
    calc ∫ x, g x ^ 2 ∂μ ≤ ∫ x, (∫ y, r x y ^ 2 ∂μ) * ∫ y, f y ^ 2 ∂μ ∂μ :=
          integral_mono hgB.pow2.integrable
            ((bm_row_sq hr).mul (BM.const _)).integrable h2
      _ = hs μ r * ∫ y, f y ^ 2 ∂μ := by rw [integral_mul_const]; rfl
  have h4 : qform μ r f ^ 2 ≤ (hs μ r * (∫ x, f x ^ 2 ∂μ) ^ 2) := by
    calc qform μ r f ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := h1
      _ ≤ (∫ x, f x ^ 2 ∂μ) * (hs μ r * ∫ y, f y ^ 2 ∂μ) := mul_le_mul_of_nonneg_left h3 hF0
      _ = hs μ r * (∫ x, f x ^ 2 ∂μ) ^ 2 := by ring
  have h5 := Real.abs_le_sqrt h4
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hF0] at h5

/-- **Bessel's inequality** for a finite part of an orthonormal family. -/
theorem bessel (hφ : ∀ j, BM (φ j))
    (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0) (S : Finset ι)
    {f : X → ℝ} (hf : BM f) :
    ∑ j ∈ S, (∫ y, φ j y * f y ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := integral_sub_sum_sq S hφ horth hf (fun j => ∫ y, φ j y * f y ∂μ)
  have h0 : 0 ≤ ∫ x, (f x - ∑ j ∈ S, (∫ y, φ j y * f y ∂μ) * φ j x) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have e : ∑ j ∈ S, (∫ y, φ j y * f y ∂μ) * ∫ x, f x * φ j x ∂μ
      = ∑ j ∈ S, (∫ y, φ j y * f y ∂μ) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      rw [_root_.sq]; congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [h, e] at h0
  linarith

/-- **The top of the form.** For a bounded kernel with an orthonormal family of bounded
eigenfunctions whose squared eigenvalues sum to its Hilbert–Schmidt norm, the form is at most
`M ∫ f²` for every `M ≥ 0` above every eigenvalue. -/
theorem qform_le (hk : Bdd k) (hφ : ∀ j, BM (φ j))
    (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0)
    (heig : ∀ j z, ∫ y, k z y * φ j y ∂μ = c j * φ j z)
    (hsum : HasSum (fun j => c j ^ 2) (hs μ k)) {M : ℝ} (hM0 : 0 ≤ M) (hcM : ∀ j, c j ≤ M)
    {f : X → ℝ} (hf : BM f) : qform μ k f ≤ M * ∫ x, f x ^ 2 ∂μ := by
  set F := ∫ x, f x ^ 2 ∂μ with hFdef
  have hF0 : 0 ≤ F := integral_nonneg fun x => sq_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := (ε / (F + 1)) ^ 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨S, hS⟩ := (hsum.eventually (Metric.ball_mem_nhds (hs μ k) hδ0)).exists
  have hdec := hs_remS hk hφ horth heig S
  have hrem : hs μ (remS k c φ S) < δ := by
    rw [Real.dist_eq] at hS
    have := abs_lt.mp hS
    linarith
  have hq := qform_remS (μ := μ) (c := c) hk hφ S hf
  have hA : ∑ j ∈ S, c j * (∫ y, φ j y * f y ∂μ) ^ 2 ≤ M * F := by
    calc ∑ j ∈ S, c j * (∫ y, φ j y * f y ∂μ) ^ 2
        ≤ ∑ j ∈ S, M * (∫ y, φ j y * f y ∂μ) ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcM j) (sq_nonneg _)
      _ = M * ∑ j ∈ S, (∫ y, φ j y * f y ∂μ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ M * F := mul_le_mul_of_nonneg_left (bessel hφ horth S hf) hM0
  have hB := (le_abs_self _).trans (abs_qform_le (μ := μ) (bdd_remS (c := c) hk hφ S) hf)
  have hsq : Real.sqrt (hs μ (remS k c φ S)) ≤ ε / (F + 1) := by
    rw [show ε / (F + 1) = Real.sqrt δ from by rw [hδ, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hrem.le
  have hC : Real.sqrt (hs μ (remS k c φ S)) * F ≤ ε := by
    calc Real.sqrt (hs μ (remS k c φ S)) * F ≤ ε / (F + 1) * F :=
          mul_le_mul_of_nonneg_right hsq hF0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
  linarith

/-- The squared eigenvalues of an orthonormal eigenfamily are summable (`Σ_S c_j² ≤ hs`). -/
theorem summable_sq (hk : Bdd k) (hφ : ∀ j, BM (φ j))
    (horth : ∀ j l, ∫ x, φ j x * φ l x ∂μ = if j = l then 1 else 0)
    (heig : ∀ j z, ∫ y, k z y * φ j y ∂μ = c j * φ j z) : Summable (fun j => c j ^ 2) :=
  summable_of_sum_le (c := hs μ k) (fun j => sq_nonneg _) fun S => by
    have h := hs_remS hk hφ horth heig S
    have : 0 ≤ hs μ (remS k c φ S) := MassGap.KernelPower.hs_nonneg _
    linarith


omit [DecidableEq ι] in
/-- **The form of a symmetric kernel is symmetric**: `∫ f · K g = ∫ g · K f`. -/
theorem qform_cross_symm (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) {f g : X → ℝ} (hf : BM f)
    (hg : BM g) :
    ∫ x, f x * ∫ y, k x y * g y ∂μ ∂μ = ∫ x, g x * ∫ y, k x y * f y ∂μ ∂μ := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  have hF : Measurable (Function.uncurry fun x y => f x * (k x y * g y)) :=
    (hfm.comp measurable_fst).mul (hk.meas.mul (hgm.comp measurable_snd))
  have hb : ∀ x y, |f x * (k x y * g y)| ≤ Cf * (Ck * Cg) := fun x y => by
    rw [abs_mul, abs_mul]
    have hCk0 : 0 ≤ Ck := (abs_nonneg _).trans (hCk x y)
    exact mul_le_mul (hCf x) (mul_le_mul (hCk x y) (hCg y) (abs_nonneg _) hCk0)
      (by positivity) ((abs_nonneg _).trans (hCf x))
  calc ∫ x, f x * ∫ y, k x y * g y ∂μ ∂μ = ∫ x, ∫ y, f x * (k x y * g y) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, f x * (k x y * g y) ∂μ ∂μ := MassGap.KernelPower.swap_bdd hF hb
    _ = ∫ y, g y * ∫ x, k y x * f x ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show ∫ x, f x * (k x y * g y) ∂μ = g y * ∫ x, k y x * f x ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show f x * (k x y * g y) = g y * (k y x * f x)
        rw [hsym x y]; ring

omit [DecidableEq ι] in
/-- The form along a line: `Q(f + t g) = Q(f) + 2t ∫ g · K f + t² Q(g)`. -/
theorem qform_add_smul (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) {f g : X → ℝ} (hf : BM f)
    (hg : BM g) (t : ℝ) :
    qform μ k (fun x => f x + t * g x) = qform μ k f
      + 2 * t * ∫ x, g x * ∫ y, k x y * f y ∂μ ∂μ + t ^ 2 * qform μ k g := by
  have hin : ∀ x, ∫ y, k x y * (f y + t * g y) ∂μ
      = ∫ y, k x y * f y ∂μ + t * ∫ y, k x y * g y ∂μ := by
    intro x
    have e : (fun y => k x y * (f y + t * g y)) = fun y => k x y * f y + t * (k x y * g y) := by
      funext y; ring
    rw [e, integral_add ((bm_row_fun hk x).mul hf).integrable
      (BM.const_mul t ((bm_row_fun hk x).mul hg)).integrable, integral_const_mul]
  have hRf : BM (fun x => ∫ y, k x y * f y ∂μ) := BM.row hk hf
  have hRg : BM (fun x => ∫ y, k x y * g y ∂μ) := BM.row hk hg
  have hc := qform_cross_symm (μ := μ) hk hsym hf hg
  unfold qform
  simp_rw [hin]
  have e : (fun x => (f x + t * g x) * (∫ y, k x y * f y ∂μ + t * ∫ y, k x y * g y ∂μ))
      = fun x => f x * ∫ y, k x y * f y ∂μ + t * (f x * ∫ y, k x y * g y ∂μ)
        + t * (g x * ∫ y, k x y * f y ∂μ) + t ^ 2 * (g x * ∫ y, k x y * g y ∂μ) := by
    funext x; ring
  rw [e, integral_add (((hf.mul hRf).add (BM.const_mul t (hf.mul hRg))).add
      (BM.const_mul t (hg.mul hRf))).integrable (BM.const_mul _ (hg.mul hRg)).integrable,
    integral_add ((hf.mul hRf).add (BM.const_mul t (hf.mul hRg))).integrable
      (BM.const_mul t (hg.mul hRf)).integrable,
    integral_add (hf.mul hRf).integrable (BM.const_mul t (hf.mul hRg)).integrable,
    integral_const_mul, integral_const_mul, integral_const_mul, hc]
  ring

omit [DecidableEq ι] in
/-- **A top eigenfunction's modulus is an eigenfunction.** For a bounded symmetric nonnegative
kernel whose form is at most `|μ₀| ∫ u²`, and `∫ k(x,y) Ω(y) dy = μ₀ Ω(x)`, the defect
`K|Ω| − |μ₀| |Ω|` has zero square integral. -/
theorem integral_defect_sq (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) (hk0 : ∀ x y, 0 ≤ k x y)
    {Ω : X → ℝ} (hΩ : BM Ω) {μ₀ : ℝ} (heig : ∀ x, ∫ y, k x y * Ω y ∂μ = μ₀ * Ω x)
    (hform : ∀ u : X → ℝ, BM u → qform μ k u ≤ |μ₀| * ∫ x, u x ^ 2 ∂μ) :
    ∫ x, (∫ y, k x y * |Ω y| ∂μ - |μ₀| * |Ω x|) ^ 2 ∂μ = 0 := by
  set f : X → ℝ := fun x => |Ω x| with hfdef
  have hf : BM f := by
    obtain ⟨hm, C, hC⟩ := hΩ
    exact ⟨hm.abs, C, fun x => by simp only [hfdef, abs_abs]; exact hC x⟩
  set h : X → ℝ := fun x => ∫ y, k x y * f y ∂μ with hhdef
  have hh : BM h := BM.row hk hf
  set g : X → ℝ := fun x => h x - |μ₀| * f x with hgdef
  have hg : BM g := hh.sub (BM.const_mul _ hf)
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    simp only [hgdef, hhdef, hfdef, sub_nonneg]
    calc |μ₀| * |Ω x| = |∫ y, k x y * Ω y ∂μ| := by rw [heig, abs_mul]
      _ ≤ ∫ y, |k x y * Ω y| ∂μ := abs_integral_le_integral_abs
      _ = ∫ y, k x y * |Ω y| ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show |k x y * Ω y| = k x y * |Ω y|
          rw [abs_mul, abs_of_nonneg (hk0 x y)]
  set G := ∫ x, g x ^ 2 ∂μ with hGdef
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  have hfg0 : 0 ≤ ∫ x, f x * g x ∂μ :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (hg0 x)
  have hQg := hform g hg
  -- the form along `f + t g`
  have hline : ∀ t : ℝ, 0 ≤ -(∫ x, f x * g x ∂μ) - 2 * t * G
      + t ^ 2 * (|μ₀| * G - qform μ k g) := by
    intro t
    have h1 := hform (fun x => f x + t * g x) (hf.add (BM.const_mul t hg))
    rw [qform_add_smul hk hsym hf hg t] at h1
    have hsq : ∫ x, (f x + t * g x) ^ 2 ∂μ
        = ∫ x, f x ^ 2 ∂μ + 2 * t * ∫ x, f x * g x ∂μ + t ^ 2 * G := by
      have e : (fun x => (f x + t * g x) ^ 2)
          = fun x => f x ^ 2 + 2 * t * (f x * g x) + t ^ 2 * g x ^ 2 := by funext x; ring
      rw [e, integral_add (hf.pow2.add (BM.const_mul _ (hf.mul hg))).integrable
        (BM.const_mul _ hg.pow2).integrable,
        integral_add hf.pow2.integrable (BM.const_mul _ (hf.mul hg)).integrable,
        integral_const_mul, integral_const_mul]
    have hqf : qform μ k f = |μ₀| * ∫ x, f x ^ 2 ∂μ + ∫ x, f x * g x ∂μ := by
      unfold qform
      have e : (fun x => f x * ∫ y, k x y * f y ∂μ)
          = fun x => |μ₀| * f x ^ 2 + f x * g x := by
        funext x; simp only [hgdef, hhdef]; ring
      rw [e, integral_add (BM.const_mul _ hf.pow2).integrable (hf.mul hg).integrable,
        integral_const_mul]
    have hgh : ∫ x, g x * ∫ y, k x y * f y ∂μ ∂μ = G + |μ₀| * ∫ x, f x * g x ∂μ := by
      have e : (fun x => g x * ∫ y, k x y * f y ∂μ)
          = fun x => g x ^ 2 + |μ₀| * (f x * g x) := by
        funext x; simp only [hgdef, hhdef]; ring
      rw [e, integral_add hg.pow2.integrable (BM.const_mul _ (hf.mul hg)).integrable,
        integral_const_mul]
    rw [hsq, hqf, hgh] at h1
    nlinarith
  by_contra hne
  have hGpos : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hne)
  set q := |μ₀| * G - qform μ k g with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have ht := hline (G / (q + 1))
  have htpos : 0 < G / (q + 1) := div_pos hGpos (by linarith)
  have key : (G / (q + 1)) ^ 2 * q ≤ G / (q + 1) * G := by
    rw [sq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ htpos.le
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

end Form

/-! ## 9. The ground level of the zero-flux kernel has no zero, and (E1) -/

section Ground

open MassGap.CentreSectorSeedN (trivKN hSN bdd_trivKN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.KernelPower (hs Bdd)

variable {i : Fin 4}

/-- A row integral of the zero-flux kernel against an integrable function is continuous. -/
theorem continuous_trivKN_row {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) {f : Slice n i → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (hSN 2 n i)) :
    Continuous fun x => ∫ y, trivKN 2 β n i x y * f y ∂(hSN 2 n i) := by
  have hb := bdd_trivKN (N := 2) hβ n i
  obtain ⟨C, hC⟩ := hb.bdd
  refine continuous_of_dominated (bound := fun y => C * |f y|) (fun x => ?_)
    (fun x => Filter.Eventually.of_forall fun y => ?_) (hfi.abs.const_mul C)
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((hb.meas.comp (measurable_const.prodMk measurable_id)).mul hfm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC x y) (abs_nonneg _)
  · exact (continuous_trivKN_left β n y).mul continuous_const

/-- **The ground level of the zero-flux kernel vanishes nowhere** (at `β > 0`). The form of
`trivKN` is at most `|μ_{g₀}| ∫ u²` (`qform_le`: the levels exhaust the Hilbert–Schmidt norm by
`hs_eq`, and `|μ_j| ≤ |μ_{g₀}|` by `ground`); so `|φ_{g₀}|` is an eigenfunction for `|μ_{g₀}|`
(`integral_defect_sq`, continuity, Haar measure positive on open sets), and
`|μ_{g₀}| |φ_{g₀}(x)| = ∫ trivKN(x, y) |φ_{g₀}(y)| dy ≥ floor · ∫ |φ_{g₀}| > 0`. -/
theorem ground_ne_zero {β : ℝ} (hβ : 0 < β) {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (x : Slice n i) : φ g₀ x ≠ 0 := by
  classical
  have hk : Bdd (trivKN 2 β n i) := bdd_trivKN (N := 2) hβ.le n i
  have hsym := MassGap.FiniteReadingFlux.symm_trivKN (N := 2) hβ.le n i
  have hk0 : ∀ x y, 0 ≤ trivKN 2 β n i x y := fun x y =>
    (CentreSectorSeed.floor_pos β n i).le.trans
      (MassGap.FiniteReadingFlux.low_trivKN (N := 2) hβ.le n i x y)
  have hφB : ∀ j, BM (φ j) := fun j =>
    ⟨hm j, _, abs_le_norm (continuous_level hβ.le hL hm j)⟩
  have horth : ∀ j l, ∫ x, φ j x * φ l x ∂(hSN 2 n i) = if j = l then 1 else 0 := by
    intro j l
    split_ifs with h
    · subst h; exact hL.norm j
    · exact hL.orth j l h
  have hen : (fun j => μv j ^ 2)
      = fun j => Real.exp (-(E j * ((n : ℝ) * AsymptoticScaling.aRun 2 β))) :=
    funext hL.energy
  have hsum : HasSum (fun j => μv j ^ 2) (hs (hSN 2 n i) (trivKN 2 β n i)) := by
    have hS := summable_sq (μ := hSN 2 n i) hk hφB horth hL.eigen
    have h := hS.hasSum
    rwa [hen, ← hL.hs_eq, ← hen] at h
  have ht : 0 ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β :=
    mul_nonneg (Nat.cast_nonneg _) (AsymptoticScaling.aRun_pos (by norm_num) hβ).le
  have hM : ∀ j, μv j ≤ |μv g₀| := by
    intro j
    have h1 : μv j ^ 2 ≤ μv g₀ ^ 2 := by
      rw [hL.energy, hL.energy, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right (hL.ground j) ht
      linarith
    exact (le_abs_self _).trans (sq_le_sq.mp h1 |>.trans_eq rfl)
  have hform : ∀ u : Slice n i → ℝ, BM u →
      qform (hSN 2 n i) (trivKN 2 β n i) u ≤ |μv g₀| * ∫ x, u x ^ 2 ∂(hSN 2 n i) :=
    fun u hu => qform_le hk hφB horth hL.eigen hsum (abs_nonneg _) hM hu
  have hdef := integral_defect_sq hk hsym hk0 (hφB g₀) (hL.eigen g₀) hform
  -- continuity and the pointwise identity
  have hΩc := continuous_level hβ.le hL hm g₀
  have hAc : Continuous (fun x => |φ g₀ x|) := hΩc.abs
  have hAint : Integrable (fun x => |φ g₀ x|) (hSN 2 n i) := (hφB g₀).integrable.abs
  have hrow := continuous_trivKN_row hβ.le n (hm g₀).abs hAint
  have hpt : ∀ x, ∫ y, trivKN 2 β n i x y * |φ g₀ y| ∂(hSN 2 n i) = |μv g₀| * |φ g₀ x| := by
    intro x
    have h0 := SliceKernelPower.eq_zero_of_integral_eq_zero (μ := i) (T := Tr n i) (N := 2)
      (f := fun x => (∫ y, trivKN 2 β n i x y * |φ g₀ y| ∂(hSN 2 n i) - |μv g₀| * |φ g₀ x|) ^ 2)
      ((hrow.sub (continuous_const.mul hAc)).pow 2) (fun _ => sq_nonneg _) hdef x
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  -- `∫ |φ_{g₀}| > 0`
  have hApos : 0 < ∫ y, |φ g₀ y| ∂(hSN 2 n i) := by
    rcases (integral_nonneg (fun y => abs_nonneg (φ g₀ y)) :
        0 ≤ ∫ y, |φ g₀ y| ∂(hSN 2 n i)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ y, |φ g₀ y| = 0 := fun y =>
        SliceKernelPower.eq_zero_of_integral_eq_zero (μ := i) (T := Tr n i) (N := 2)
          hAc (fun _ => abs_nonneg _) h.symm y
      have h1 := hL.norm g₀
      have : (fun x => φ g₀ x * φ g₀ x) = fun _ => (0 : ℝ) := by
        funext y; rw [abs_eq_zero.mp (hz y), mul_zero]
      rw [this, integral_const, smul_zero] at h1
      exact zero_ne_one h1
  -- the lower bound
  have hlow : CentreSectorSeed.floor β n i * ∫ y, |φ g₀ y| ∂(hSN 2 n i)
      ≤ ∫ y, trivKN 2 β n i x y * |φ g₀ y| ∂(hSN 2 n i) := by
    rw [← integral_const_mul]
    refine integral_mono (hAint.const_mul _)
      ((bm_row_fun hk x).mul ⟨(hm g₀).abs, _, fun y => by
        rw [abs_abs]; exact abs_le_norm hΩc y⟩).integrable fun y => ?_
    exact mul_le_mul_of_nonneg_right
      (MassGap.FiniteReadingFlux.low_trivKN (N := 2) hβ.le n i x y) (abs_nonneg _)
  have hpos : 0 < |μv g₀| * |φ g₀ x| := by
    rw [← hpt x]
    exact lt_of_lt_of_le (mul_pos (CentreSectorSeed.floor_pos β n i) hApos) hlow
  intro h0
  rw [h0, abs_zero, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-- **(E1) of `ElectricLoops.zeroFluxGap_of_loopShells`.** At `β > 0`, for measurable zero-flux
levels and any site `y₀`, every excited level `φ_j` (`j ≠ g₀`) is in the `L²` closure of the span
of the loop states of `Ω = φ_{g₀}`. -/
theorem excited_mem_closure_loops {β : ℝ} (hβ : 0 < β) {n : ℕ} {ι : Type*} {g₀ : ι}
    {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ} (hL : EigenLevels β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (y₀ : TT i (Tr n i)) :
    ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))) :=
  hgen_of_separation hβ.le hL hm y₀ (fun V V' h => giles y₀ V V' h) (ground_ne_zero hβ hL hm)

open MassGap.AsymptoticScaling (aRun) in
open MassGap.GlueballArea (ZeroFluxGap) in
open MassGap.SlabKernelOperator (kernelCLM) in
/-- **The electric reduction with (E1) discharged**: `ElectricLoops.zeroFluxGap_of_loopShells`
with its hypothesis `hgen` supplied by `excited_mem_closure_loops`; the input left is (E2'). -/
theorem zeroFluxGap_of_loopShells_E2 {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n)
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j)) (y₀ : TT i (Tr n i))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (b : ℕ → ℕ → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k l, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ∀ y ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R l,
      |inner ℝ (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x)
        (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) y)| ≤ b k l * (‖x‖ * ‖y‖))
    {m : ℝ} (hrow : ∀ k (s : Finset ℕ), ∑ l ∈ s, b k l
      ≤ (|μv g₀| * Real.exp (-(m * ((n : ℝ) * aRun 2 β)) / 2)) ^ 2) :
    ZeroFluxGap g₀ E m :=
  zeroFluxGap_of_loopShells hβ hn hL hm hkm hC0 hkb hR hreach
    (excited_mem_closure_loops hβ hL hm y₀) b hb0 hsym hblk hrow

end Ground

end MassGap.LoopsGenerate

#print axioms MassGap.LoopsGenerate.exists_adjoin_near
#print axioms MassGap.LoopsGenerate.adjoin_le_span
#print axioms MassGap.LoopsGenerate.mem_closure_span_allLoops
#print axioms MassGap.LoopsGenerate.level_gauge
#print axioms MassGap.LoopsGenerate.continuous_level
#print axioms MassGap.LoopsGenerate.hgen_of_separation
#print axioms MassGap.LoopsGenerate.exists_conj
#print axioms MassGap.LoopsGenerate.su2_conj_of_traces
#print axioms MassGap.LoopsGenerate.giles
#print axioms MassGap.LoopsGenerate.qform_le
#print axioms MassGap.LoopsGenerate.integral_defect_sq
#print axioms MassGap.LoopsGenerate.ground_ne_zero
#print axioms MassGap.LoopsGenerate.excited_mem_closure_loops
#print axioms MassGap.LoopsGenerate.zeroFluxGap_of_loopShells_E2
