import Mathlib
import MassGap.ClayStatement

/-!
# MassGap.CompositeOS0Test — the separated kernel bound is compatible with asymptotic freedom

`ClayStatement` asks `OS0Sep` (`|S(F)| ≤ α γⁿ (n!)^β d^{−κn} ∏ᵢ ‖cᵢ‖₁ ‖fᵢ‖_{L¹}`) and `OS0C`
(`… ∏ᵢ Cᵢ d^{−κᵢ} ‖fᵢ‖_{L¹}`) only on
families with `ContD F` and `SepD d F`, `0 < d ≤ 1`: distinct members of the family have
`d`-separated supports (`ContinuumSep.sepBy`). `TwoPointKernel` gives the trace two-point function
by a kernel `G` only on separated pairs, and `AFCoefficient` fixes `r⁸ G(r) (log r)²` as `r → 0⁺`.
`G(r) ∼ c/(r⁸ log² r)` is not locally integrable against `r³ dr` at `0`, but no clause reads `G` at
coincident points (`AFCoefficient` reads `G` only on `r > 0`, as a limit). This module proves that the three clauses do not conflict.

## What is proved

* `not_sepD_coincident`: a two-member family whose two test functions are the same non-zero
  function is not `d`-separated for any `d > 0`. The bounds of `OS0Sep`, `OS0C` never read a
  coincident pair.
* `abs_le_of_afCoefficient`: `G` continuous on `(0, ∞)`, `AFCoefficient N G`, and `G` bounded on
  `[1, ∞)` give `A ≥ 0` with `|G r| ≤ A d⁻⁸` for all `0 < d ≤ 1`, `r ≥ d`.
* `twoPoint_sepBound`: under `TwoPointKernel` and the same two conditions on `G`, the trace
  two-point function on `d`-separated continuous test functions satisfies
  `|S(tr f, tr g)| ≤ A d⁻⁸ ‖f‖_{L¹} ‖g‖_{L¹}`, the shape of `OS0Sep` at `n = 2`, `κ = 4`.
* `afWitness_continuousOn`, `afWitness_bounded`, `afCoefficient_afWitness`: the function
  `afConst N / (r⁸ (log² r + 1))` meets all three conditions on `G`, so they are jointly
  satisfiable.

## What is not proved here

The boundedness of `G` on `[1, ∞)` is a hypothesis of `twoPoint_sepBound`. ARGUED, not formalised:
`OS0Sep` at `n = 2`, `d = 1`, together with `TwoPointKernel` and continuity of `G`, forces it
(approximate `δ` at two points at distance `> 1`). Satisfiability of the whole of `ClayData` is not
claimed; the module shows only that `TwoPointKernel`, `AFCoefficient` and the separated kernel
bound are compatible.
-/

noncomputable section

namespace MassGap.CompositeOS0Test

open MassGap MassGap.ContinuumField MassGap.ClayStatement Filter Set MeasureTheory
open scoped Topology

variable {N : ℕ}

/-- **Coincident supports are never separated.** A two-member family with the same test function,
non-zero somewhere, is not `d`-separated for any `d > 0`.

DERIVED: `0`, `1` the two members; `0` the sign of the separation. -/
theorem not_sepD_coincident {Xd : Type} (a b : Xd) (f : TestFn) (hf : ∃ y, f.1 y ≠ 0) {d : ℝ}
    (hd : 0 < d) : ¬ SepD d (![(a, f), (b, f)] : Fin 2 → Xd × TestFn) := by
  intro h
  obtain ⟨y, hy⟩ := hf
  obtain ⟨i, hi⟩ := h 0 1 (by decide) y y hy hy
  simp at hi
  linarith

#print axioms not_sepD_coincident

/-- A test function vanishes off a compact box. DERIVED: no numeral. -/
theorem hasCompactSupport_testFn (f : TestFn) : HasCompactSupport f.1 := by
  obtain ⟨R, M, _, _, hs⟩ := f.2
  refine HasCompactSupport.intro (K := Set.pi univ (fun _ : Fin 4 => Icc (-R) R))
    (isCompact_univ_pi (fun _ => isCompact_Icc)) ?_
  intro x hx
  by_contra hne
  apply hx
  intro i _
  exact abs_le.1 (hs x hne i)

/-- `|f|` of a continuous test function is integrable. DERIVED: no numeral. -/
theorem integrable_abs_testFn (f : TestFn) (hf : Continuous f.1) :
    Integrable (fun x => |f.1 x|) :=
  (continuous_abs.comp hf).integrable_of_hasCompactSupport (hasCompactSupport_testFn f).abs

/-- Separated supports are at Euclidean distance at least `d`.

DERIVED: `2` the square. -/
theorem le_eDist_of_sepBy {d : ℝ} {f g : TestFn} (h : ContinuumSep.sepBy d f g) {x y : Fin 4 → ℝ}
    (hx : f.1 x ≠ 0) (hy : g.1 y ≠ 0) : d ≤ ContinuumNontrivial.eDist x y := by
  obtain ⟨i, hi⟩ := h x y hx hy
  have h1 : (x i - y i) ^ 2 ≤ ∑ j, (x j - y j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc d ≤ |x i - y i| := hi
    _ = Real.sqrt ((x i - y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ ContinuumNontrivial.eDist x y := Real.sqrt_le_sqrt h1

/-- **The kernel off the diagonal.** `G` continuous on `(0, ∞)`, `AFCoefficient N G` and `G`
bounded on `[1, ∞)` give `A ≥ 0` with `|G r| ≤ A d⁻⁸` whenever `0 < d ≤ 1` and `r ≥ d`.

DERIVED: `8` the power of `AFCoefficient`; `1` the unit scale; `2` the square of the logarithm. -/
theorem abs_le_of_afCoefficient {G : ℝ → ℝ} (hc : ContinuousOn G (Ioi 0))
    (hAF : AFCoefficient N G) (hB : ∃ M, ∀ r, 1 ≤ r → |G r| ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d r : ℝ, 0 < d → d ≤ 1 → d ≤ r → |G r| ≤ A * (d ^ 8)⁻¹ := by
  obtain ⟨M, hM⟩ := hB
  set K : ℝ := |afConst N| + 1
  have e1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), |r ^ 8 * G r * Real.log r ^ 2| ≤ K := by
    have := (Metric.tendsto_nhds.1 hAF) 1 one_pos
    filter_upwards [this] with r hr
    rw [Real.dist_eq] at hr
    have := abs_sub_abs_le_abs_sub (r ^ 8 * G r * Real.log r ^ 2) (afConst N)
    simp only [K]; linarith
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log r < -1 :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (-1))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  set δ : ℝ := min u 1
  have hδ0 : 0 < δ := lt_min hu0 one_pos
  have hcomp : IsCompact (Icc δ 1) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hc.mono (fun r hr => lt_of_lt_of_le hδ0 hr.1))
  refine ⟨K + max C 0 + max M 0, by positivity, ?_⟩
  intro d r hd hd1 hdr
  have hr0 : 0 < r := lt_of_lt_of_le hd hdr
  have hd8 : 0 < d ^ 8 := by positivity
  have hinv1 : 1 ≤ (d ^ 8)⁻¹ := one_le_inv_iff₀.2 ⟨hd8, pow_le_one₀ hd.le hd1⟩
  have hK0 : 0 ≤ K := by positivity
  have hCm : 0 ≤ max C 0 := le_max_right _ _
  have hMm : 0 ≤ max M 0 := le_max_right _ _
  have hsplit : ∀ P : ℝ, 0 ≤ P → P ≤ K + max C 0 + max M 0 → |G r| ≤ P * (d ^ 8)⁻¹ →
      |G r| ≤ (K + max C 0 + max M 0) * (d ^ 8)⁻¹ := fun P _ hP h =>
    h.trans (mul_le_mul_of_nonneg_right hP (inv_nonneg.2 hd8.le))
  rcases lt_or_ge r δ with hrδ | hrδ
  · -- near `0`: the asymptotic-freedom coefficient
    have hru : r ∈ Ioo 0 u := ⟨hr0, lt_of_lt_of_le hrδ (min_le_left _ _)⟩
    obtain ⟨hb, hl⟩ := hsub hru
    have hl2 : 1 ≤ Real.log r ^ 2 := by nlinarith
    have hr8 : 0 < r ^ 8 := by positivity
    have h1 : |G r| * r ^ 8 ≤ K := by
      have : |r ^ 8 * G r * Real.log r ^ 2| = |G r| * r ^ 8 * Real.log r ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hr8, abs_of_nonneg (sq_nonneg (Real.log r))]; ring
      rw [this] at hb
      have h0 : 0 ≤ |G r| * r ^ 8 := by positivity
      nlinarith
    have h2 : |G r| ≤ K * (r ^ 8)⁻¹ := by
      rw [le_mul_inv_iff₀ hr8]; exact h1
    have h3 : (r ^ 8)⁻¹ ≤ (d ^ 8)⁻¹ :=
      inv_anti₀ hd8 (pow_le_pow_left₀ hd.le hdr 8)
    refine hsplit K hK0 (by linarith) (h2.trans (mul_le_mul_of_nonneg_left h3 hK0))
  rcases le_or_gt r 1 with hr1 | hr1
  · -- on `[δ, 1]`: continuity on a compact interval
    have h1 : |G r| ≤ max C 0 := (by simpa [Real.norm_eq_abs] using hC r ⟨hrδ, hr1⟩ :
      |G r| ≤ C).trans (le_max_left _ _)
    refine hsplit (max C 0) hCm (by linarith) ?_
    calc |G r| ≤ max C 0 := h1
      _ = max C 0 * 1 := (mul_one _).symm
      _ ≤ max C 0 * (d ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hinv1 hCm
  · -- on `[1, ∞)`: the bound at large distance
    have h1 : |G r| ≤ max M 0 := (hM r hr1.le).trans (le_max_left _ _)
    refine hsplit (max M 0) hMm (by linarith) ?_
    calc |G r| ≤ max M 0 := h1
      _ = max M 0 * 1 := (mul_one _).symm
      _ ≤ max M 0 * (d ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hinv1 hMm

#print axioms abs_le_of_afCoefficient

/-- **The separated trace two-point bound.** Under `TwoPointKernel`, `AFCoefficient` and a bound
on `G` on `[1, ∞)`: `|S(tr f, tr g)| ≤ A d⁻⁸ ‖f‖_{L¹} ‖g‖_{L¹}` on `d`-separated continuous test
functions, `0 < d ≤ 1`. This is the `n = 2` instance of the separated kernel bound with `κ = 4`;
the `r⁻⁸` singularity at coincident points is never read.

DERIVED: `8` the power of `AFCoefficient`; `1` the top of the separation. -/
theorem twoPoint_sepBound (hN : N ≠ 0) (ρ : RenormMix N) {G : ℝ → ℝ}
    (hK : TwoPointKernel hN ρ G) (hAF : AFCoefficient N G) (hB : ∃ M, ∀ r, 1 ≤ r → |G r| ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d : ℝ, 0 < d → d ≤ 1 → ∀ f g : TestFn, Continuous f.1 → Continuous g.1 →
      ContinuumSep.sepBy d f g → |contTr hN ρ ![f, g]| ≤ A * (d ^ 8)⁻¹ * (l1 f * l1 g) := by
  obtain ⟨A, hA, hG⟩ := abs_le_of_afCoefficient hK.1 hAF hB
  refine ⟨A, hA, ?_⟩
  intro d hd hd1 f g hf hg hs
  rw [hK.2 f g hf hg ⟨d, hd, hs⟩]
  set B : ℝ := A * (d ^ 8)⁻¹
  have hB0 : 0 ≤ B := mul_nonneg hA (inv_nonneg.2 (by positivity))
  have hpt : ∀ x y, ‖f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)‖
      ≤ B * |f.1 x| * |g.1 y| := by
    intro x y
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases hx : f.1 x = 0
    · simp [hx]
    by_cases hy : g.1 y = 0
    · simp [hy]
    have hle := hG d _ hd hd1 (le_eDist_of_sepBy hs hx hy)
    have h0 : 0 ≤ |f.1 x| * |g.1 y| := by positivity
    calc |f.1 x| * |g.1 y| * |G (ContinuumNontrivial.eDist x y)|
        ≤ |f.1 x| * |g.1 y| * B := mul_le_mul_of_nonneg_left hle h0
      _ = B * |f.1 x| * |g.1 y| := by ring
  have hfi := integrable_abs_testFn f hf
  have hgi := integrable_abs_testFn g hg
  have hinner : ∀ x, ‖∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)‖
      ≤ B * |f.1 x| * l1 g := by
    intro x
    calc ‖∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)‖
        ≤ ∫ y, B * |f.1 x| * |g.1 y| :=
          norm_integral_le_of_norm_le (hgi.const_mul (B * |f.1 x|))
            (Eventually.of_forall (hpt x))
      _ = B * |f.1 x| * l1 g := by rw [integral_const_mul]; rfl
  have hout : ‖∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)‖
      ≤ ∫ x, B * |f.1 x| * l1 g :=
    norm_integral_le_of_norm_le ((hfi.const_mul B).mul_const (l1 g))
      (Eventually.of_forall hinner)
  have heq : ∫ x, B * |f.1 x| * l1 g = B * (l1 f * l1 g) := by
    rw [integral_mul_const, integral_const_mul]
    simp only [l1]; ring
  rw [← Real.norm_eq_abs]
  exact hout.trans heq.le

#print axioms twoPoint_sepBound

/-- **A kernel with the asymptotic-freedom coefficient**: `afConst N / (r⁸ (log² r + 1))`.

DERIVED: `8`, `2` as in `AFCoefficient`; `1` keeps the denominator off `0` at `r = 1`. -/
def afWitness (N : ℕ) (r : ℝ) : ℝ := afConst N / (r ^ 8 * (Real.log r ^ 2 + 1))

/-- DERIVED: `0` the end of the half-line. -/
theorem afWitness_continuousOn (N : ℕ) : ContinuousOn (afWitness N) (Ioi 0) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuousOn_id.pow 8).mul
      (((Real.continuousOn_log.mono (fun r (hr : r ∈ Ioi (0 : ℝ)) => ne_of_gt hr)).pow 2).add
        continuousOn_const)
  · intro r hr
    have : (0 : ℝ) < r := hr
    positivity

/-- DERIVED: `1` the unit scale. -/
theorem afWitness_bounded (N : ℕ) : ∃ M, ∀ r, 1 ≤ r → |afWitness N r| ≤ M := by
  refine ⟨|afConst N|, fun r hr => ?_⟩
  have h1 : 1 ≤ r ^ 8 * (Real.log r ^ 2 + 1) := by
    have : 1 ≤ r ^ 8 := one_le_pow₀ hr
    have : 1 ≤ Real.log r ^ 2 + 1 := by nlinarith [sq_nonneg (Real.log r)]
    nlinarith
  unfold afWitness
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < r ^ 8 * (Real.log r ^ 2 + 1))]
  exact div_le_self (abs_nonneg _) h1

/-- **The witness has the asymptotic-freedom coefficient.**

DERIVED: `8`, `2` as in `AFCoefficient`; `1` the limit of the ratio. -/
theorem afCoefficient_afWitness (N : ℕ) : AFCoefficient N (afWitness N) := by
  unfold AFCoefficient
  have hL : Tendsto (fun r => Real.log r ^ 2 + 1) (𝓝[>] (0 : ℝ)) atTop := by
    have h1 : Tendsto (fun r => -Real.log r) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have h2 : Tendsto (fun r => (-Real.log r) ^ 2) (𝓝[>] (0 : ℝ)) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    refine tendsto_atTop_add_const_right _ 1 ?_
    simpa [neg_sq] using h2
  have hlim : Tendsto (fun r => afConst N * (1 - (Real.log r ^ 2 + 1)⁻¹)) (𝓝[>] (0 : ℝ))
      (𝓝 (afConst N)) := by
    have := (tendsto_inv_atTop_zero.comp hL)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this |>.const_mul (afConst N)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hr8 : r ^ 8 ≠ 0 := by positivity
  have hl : Real.log r ^ 2 + 1 ≠ 0 := by positivity
  unfold afWitness
  field_simp
  ring

#print axioms afCoefficient_afWitness

/-- **The three conditions on the kernel are jointly satisfiable**, and they give the separated
bound: some `G` is continuous on `(0, ∞)`, bounded on `[1, ∞)`, has the asymptotic-freedom
coefficient, and satisfies `|G r| ≤ A d⁻⁸` for `0 < d ≤ 1`, `r ≥ d`.

DERIVED: `8` the power; `1` the unit scale. -/
theorem kernel_conditions_satisfiable (N : ℕ) :
    ∃ G : ℝ → ℝ, ContinuousOn G (Ioi 0) ∧ AFCoefficient N G ∧ (∃ M, ∀ r, 1 ≤ r → |G r| ≤ M)
      ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ d r : ℝ, 0 < d → d ≤ 1 → d ≤ r → |G r| ≤ A * (d ^ 8)⁻¹ :=
  ⟨afWitness N, afWitness_continuousOn N, afCoefficient_afWitness N, afWitness_bounded N,
    abs_le_of_afCoefficient (afWitness_continuousOn N) (afCoefficient_afWitness N)
      (afWitness_bounded N)⟩

#print axioms kernel_conditions_satisfiable

end MassGap.CompositeOS0Test
