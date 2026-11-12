import Mathlib
import MassGap.OpenAIBridgeCubic
import MassGap.OpenAILink

/-!
# MassGap.OpenAIBridgeCompose — the floored uniform decay (U) from the cubic bound and named inputs

`OpenAILink.UniformDecayFrom` is the open input (U) of `OpenAILink`: for every time floor `δ > 0`
and internal separation `ε > 0` a constant `K(δ, ε)` bounds the smeared lattice connected correlation
of two token groups by `K e^{−μτ} ‖t₁‖₁ ‖t₂‖₁`, eventually along their volume order and then in the
spacing. This module assembles that bound, at the rate `μ = log 2 / ℓ` of the seed with scale
control `n_N · a_N ≤ ℓ`, from the reflection-positivity bound of
`OpenAIBridgeCubic.wilson_slab_conn_cubicG` on their laws.

## 1. Lattice gaps in physical units

* `half_pow_floor_le_exp` — the contraction `(1/2)^⌊(j+1)/n⌋` of `j + 1` transfer steps at a seed
  side `n` with `n a ≤ ℓ` is at most `2 e^{−(log 2/ℓ)(j+1)a}`: the lattice gap read in physical time.

## 2. The cubic bound, assembled at one torus

* `cubicRHS` — the right side of `OpenAIBridgeCubic.connK_rp_cubic`, as a function of the seed side,
  the two gaps, the excited weight `σ₀`, the six reflected moments and the excited–excited term;
* `cubicRHS_le` — if both gaps are at least `τ − δ/2` in physical time, `√σ₀ ≤ e^{−μτ}`, every
  reflected moment of the first group is at most `K₀ ‖t₁‖₁²` (of the second, `K₀ ‖t₂‖₁²`) and the
  excited–excited term is at most `e^{−μτ} ‖t₁‖₁ ‖t₂‖₁`, then
  `cubicRHS ≤ (8 K₀ (e^{μδ/2} + 1) + 1) ‖t₁‖₁ ‖t₂‖₁ e^{−μτ}`.

## 3. On their laws

* `sideP`, `SlabObs`, `readAt`, `reflO`, `excW`, `remW` — the cubic side `2l + 2`, slab observables,
  a slab observable read on their configurations through `configEquiv⁻¹`, its reflection
  (`OpenAIBridgeRP.revG`), the excited weight and the thermal remainder at their coupling;
* `openAI_slab_conn_cubic` — `wilson_slab_conn_cubicG` at `g.image` and `β/2`, every expectation
  carried to their law `wilsonLaw g (2l+2) β` by `OpenAIBridgeGroups.expect_eq_openAILawG`: the
  per-torus inequality on their objects, every constant a moment of their law.

## 4. The composition

* `CubicForm` — the named input that ties their smeared insertions to the per-torus inequality: for
  every admissible tensor test, eventually along their order and then in the spacing, the smeared
  connected correlation is at most a sum of four `cubicRHS` (the pairs of real and imaginary parts)
  at a seed side with `n a ≤ ℓ`, gaps at least `τ − δ/2`
  in physical time, an excited weight below `(1/2)^⌊(l+1)/n⌋` on a torus of physical half-length at
  least `period/2`, reflected moments bounded by `K₀ ‖t‖₁²` and an excited–excited term that vanishes
  relative to `‖t₁‖₁ ‖t₂‖₁`;
* `relVanish_of_thermalRemainderVanishes` — `OpenAIBridgeCubic.ThermalRemainderVanishes` along their
  order gives that relative vanishing for every test of nonzero norm;
* `uniformDecayFrom_of_cubicForm` — with `ℓ > 0` and their order tending to infinity, `CubicForm`
  gives `UniformDecayFrom C order w₁ w₂ (log 2 / ℓ)`;
* `uniformDecayAll_of_cubicForm` — the same for every pair of token groups gives `UniformDecayAll`.

## Scope

`CubicForm` is not proved for their family. What it packages beyond `openAI_slab_conn_cubic` is
glue on their objects that no module builds: the smeared insertion of a time-spread test, split
into real and imaginary parts, as a bounded measurable slab observable of their configuration read
through `configEquiv⁻¹` (stencil locality of their insertions); the transfer direction: their time
axis is `OpenAILink.timeAxis = 3` while the slabs of `wilson_slab_conn_cubicG` are cut along axis
`0`, and `OpenAIConfig.linkEquiv` keeps axes, so an axis permutation symmetry of their law (or the
cubic bound along axis `3`) is needed; time-translation invariance of their law, to place the first
slab at slice `0`; the reflection closure of their tokens, so that the
reflected moments are smeared moments of their family; a bound on those moments at physical
separation at least a floor, uniform over the lattice reflection planes; and the vanishing thermal
remainder. The seed along their couplings with scale control and even sides are inputs of
`openAI_slab_conn_cubic`.
-/

namespace MassGap.OpenAIBridgeCompose

open MeasureTheory Real Filter
open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic
open MassGap.OpenAILink

/-! ## 1. Lattice gaps in physical units -/

section Rate

/-- **A lattice gap in physical time.** At a seed side `n > 0` whose physical length `n a` is at
most `ℓ > 0`, the contraction over `j + 1` transfer steps is at most `2 e^{−(log 2/ℓ)(j+1)a}`:
`⌊(j+1)/n⌋ + 1 > (j+1)/n ≥ (j+1)a/ℓ`.

DERIVED: `1/2` is the contraction of the seed; `2` its inverse and the factor of the dropped floor;
`1` the step offset. -/
theorem half_pow_floor_le_exp {n j : ℕ} {a ℓ : ℝ} (hn : 0 < n) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hna : (n : ℝ) * a ≤ ℓ) :
    (1 / 2 : ℝ) ^ ((j + 1) / n) ≤ 2 * Real.exp (-(Real.log 2 / ℓ) * (((j : ℝ) + 1) * a)) := by
  have hlt : j + 1 < (j + 1) / n * n + n := Nat.lt_div_mul_add hn
  have hltN : j + 1 ≤ ((j + 1) / n + 1) * n := by rw [add_mul, one_mul]; exact hlt.le
  have hltR : (j : ℝ) + 1 ≤ ((((j + 1) / n : ℕ) : ℝ) + 1) * n := by exact_mod_cast hltN
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hkey : ((j : ℝ) + 1) * a ≤ ((((j + 1) / n : ℕ) : ℝ) + 1) * ℓ := by
    calc ((j : ℝ) + 1) * a ≤ ((((j + 1) / n : ℕ) : ℝ) + 1) * n * a :=
          mul_le_mul_of_nonneg_right hltR ha.le
      _ = ((((j + 1) / n : ℕ) : ℝ) + 1) * (n * a) := by ring
      _ ≤ ((((j + 1) / n : ℕ) : ℝ) + 1) * ℓ :=
          mul_le_mul_of_nonneg_left hna (by positivity)
  have h1 : (1 / 2 : ℝ) ^ ((j + 1) / n)
      = Real.exp (-((((j + 1) / n : ℕ) : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, one_div, inv_pow]
  have hm := mul_le_mul_of_nonneg_left hkey (div_pos hl2 hℓ).le
  have he : Real.log 2 / ℓ * (((((j + 1) / n : ℕ) : ℝ) + 1) * ℓ)
      = Real.log 2 * ((((j + 1) / n : ℕ) : ℝ) + 1) := by
    rw [mul_comm ((((j + 1) / n : ℕ) : ℝ) + 1) ℓ, ← mul_assoc, div_mul_cancel₀ _ hℓ.ne']
  rw [h1]
  calc Real.exp (-((((j + 1) / n : ℕ) : ℝ) * Real.log 2))
      ≤ Real.exp (Real.log 2 + -(Real.log 2 / ℓ) * (((j : ℝ) + 1) * a)) := by
        rw [Real.exp_le_exp]; linarith [hm, he]
    _ = 2 * Real.exp (-(Real.log 2 / ℓ) * (((j : ℝ) + 1) * a)) := by
        rw [Real.exp_add, Real.exp_log two_pos]

end Rate

/-! ## 2. The cubic bound, assembled at one torus -/

section Assemble

/-- **The right side of the cubic bound** (`OpenAIBridgeCubic.connK_rp_cubic`,
`OpenAIBridgeCubic.wilson_slab_conn_cubicG`) at seed side `n`, gaps `j`, `j'`, excited weight `σ`,
reflected moments `M₁, …, M₆` and excited–excited term `D`:
`(1/2)^⌊(j+1)/n⌋ √((1+σ)M₁ (1+σ)M₂) + (1/2)^⌊(j'+1)/n⌋ √((1+σ)M₃ (1+σ)M₄) + D
+ 2 √((1+σ)M₅ (1+σ)M₆) (σ + √σ)`.

DERIVED: `1/2` is the contraction of the seed; `2` the two cross pairs of the one-point terms; `1`
the step offset and the vacuum's own weight. -/
noncomputable def cubicRHS (n j j' : ℕ) (σ M₁ M₂ M₃ M₄ D M₅ M₆ : ℝ) : ℝ :=
  (1 / 2) ^ ((j + 1) / n) * √((1 + σ) * M₁ * ((1 + σ) * M₂))
    + (1 / 2) ^ ((j' + 1) / n) * √((1 + σ) * M₃ * ((1 + σ) * M₄))
    + D + 2 * √((1 + σ) * M₅ * ((1 + σ) * M₆)) * (σ + √σ)

/-- **The cubic bound at one torus, in physical units.** With `μ = log 2 / ℓ`: if the seed side
has `n a ≤ ℓ`, both gaps are at least `τ − δ/2` in physical time, `0 ≤ σ ≤ 1` and `√σ ≤ e^{−μτ}`,
the reflected moments `M₁, M₃, M₅` lie in `[0, K₀A²]` and `M₂, M₄, M₆` in `[0, K₀B²]`, and the
excited–excited term is at most `e^{−μτ} A B`, then
`cubicRHS ≤ (8 K₀ (e^{μδ/2} + 1) + 1) A B e^{−μτ}`. Each cross term is at most
`2 e^{μδ/2} e^{−μτ} · 2 K₀ A B` (`half_pow_floor_le_exp`), the one-point term at most
`2 · 2 K₀ A B · 2 e^{−μτ}` (`σ ≤ √σ`).

DERIVED: `8` is `2 · 2 · 2` (two cross terms, each `2 · 2 K₀`; the one-point term `2 · 2 · 2 K₀`);
`2` halves the floor `δ` and is the base of the rate; `1` the moment-free unit of the
excited–excited term and the bound on `σ`; `0` the signs. -/
theorem cubicRHS_le {n j j' : ℕ} {σ M₁ M₂ M₃ M₄ M₅ M₆ D a ℓ τ δ K₀ A B : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hℓ : 0 < ℓ) (hna : (n : ℝ) * a ≤ ℓ)
    (hj : τ - δ / 2 ≤ ((j : ℝ) + 1) * a) (hj' : τ - δ / 2 ≤ ((j' : ℝ) + 1) * a)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hσs : √σ ≤ Real.exp (-(Real.log 2 / ℓ) * τ))
    (hK₀ : 0 ≤ K₀) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : 0 ≤ M₁ ∧ M₁ ≤ K₀ * A ^ 2) (h2 : 0 ≤ M₂ ∧ M₂ ≤ K₀ * B ^ 2)
    (h3 : 0 ≤ M₃ ∧ M₃ ≤ K₀ * A ^ 2) (h4 : 0 ≤ M₄ ∧ M₄ ≤ K₀ * B ^ 2)
    (h5 : 0 ≤ M₅ ∧ M₅ ≤ K₀ * A ^ 2) (h6 : 0 ≤ M₆ ∧ M₆ ≤ K₀ * B ^ 2)
    (hD : D ≤ Real.exp (-(Real.log 2 / ℓ) * τ) * (A * B)) :
    cubicRHS n j j' σ M₁ M₂ M₃ M₄ D M₅ M₆
      ≤ (8 * K₀ * (Real.exp (Real.log 2 / ℓ * (δ / 2)) + 1) + 1) * (A * B)
        * Real.exp (-(Real.log 2 / ℓ) * τ) := by
  have hμ : 0 < Real.log 2 / ℓ := div_pos (Real.log_pos one_lt_two) hℓ
  have hE : 0 < Real.exp (-(Real.log 2 / ℓ) * τ) := Real.exp_pos _
  have he : 0 < Real.exp (Real.log 2 / ℓ * (δ / 2)) := Real.exp_pos _
  have hKAB : 0 ≤ 2 * K₀ * (A * B) := mul_nonneg (mul_nonneg zero_le_two hK₀) (mul_nonneg hA hB)
  have hS : ∀ Mx My : ℝ, 0 ≤ Mx → Mx ≤ K₀ * A ^ 2 → 0 ≤ My → My ≤ K₀ * B ^ 2 →
      √((1 + σ) * Mx * ((1 + σ) * My)) ≤ 2 * K₀ * (A * B) := by
    intro Mx My hMx hMx' hMy hMy'
    have hx : (1 + σ) * Mx ≤ 2 * (K₀ * A ^ 2) := by nlinarith
    have hy : (1 + σ) * My ≤ 2 * (K₀ * B ^ 2) := by nlinarith
    have hprod : (1 + σ) * Mx * ((1 + σ) * My) ≤ (2 * K₀ * (A * B)) ^ 2 := by
      calc (1 + σ) * Mx * ((1 + σ) * My) ≤ (2 * (K₀ * A ^ 2)) * (2 * (K₀ * B ^ 2)) :=
            mul_le_mul hx hy (mul_nonneg (by linarith) hMy)
              (mul_nonneg zero_le_two (mul_nonneg hK₀ (sq_nonneg A)))
        _ = (2 * K₀ * (A * B)) ^ 2 := by ring
    calc √((1 + σ) * Mx * ((1 + σ) * My)) ≤ √((2 * K₀ * (A * B)) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = 2 * K₀ * (A * B) := Real.sqrt_sq hKAB
  have hcross : ∀ i : ℕ, τ - δ / 2 ≤ ((i : ℝ) + 1) * a →
      (1 / 2 : ℝ) ^ ((i + 1) / n)
        ≤ 2 * Real.exp (Real.log 2 / ℓ * (δ / 2)) * Real.exp (-(Real.log 2 / ℓ) * τ) := by
    intro i hi
    refine (half_pow_floor_le_exp hn ha hℓ hna).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    linarith [mul_le_mul_of_nonneg_left hi hμ.le]
  have hs1 : √σ ≤ 1 := by
    have := Real.sqrt_le_sqrt hσ1
    rwa [Real.sqrt_one] at this
  have hσle : σ + √σ ≤ 2 * Real.exp (-(Real.log 2 / ℓ) * τ) := by
    have hss : σ ≤ √σ := by nlinarith [Real.sq_sqrt hσ0, Real.sqrt_nonneg σ]
    linarith
  have t1 := mul_le_mul (hcross j hj) (hS M₁ M₂ h1.1 h1.2 h2.1 h2.2) (Real.sqrt_nonneg _)
    (by positivity)
  have t2 := mul_le_mul (hcross j' hj') (hS M₃ M₄ h3.1 h3.2 h4.1 h4.2) (Real.sqrt_nonneg _)
    (by positivity)
  have t4 : 2 * √((1 + σ) * M₅ * ((1 + σ) * M₆)) * (σ + √σ)
      ≤ 2 * (2 * K₀ * (A * B)) * (2 * Real.exp (-(Real.log 2 / ℓ) * τ)) :=
    mul_le_mul (by linarith [hS M₅ M₆ h5.1 h5.2 h6.1 h6.2]) hσle
      (add_nonneg hσ0 (Real.sqrt_nonneg _)) (mul_nonneg zero_le_two hKAB)
  unfold cubicRHS
  linarith [t1, t2, t4, hD]

end Assemble

/-! ## 3. On their laws -/

section Torus

open MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.CompactGauge
  MassGap.HiddenChain MassGap.OpenAIBridgeGroups

/-- The cubic side `2l + 2` as a positive natural.

DERIVED: `1` is the offset of the side `l + l + 1 + 1`. -/
def sideP (l : ℕ) : ℕ+ := ⟨l + l + 1 + 1, Nat.succ_pos _⟩

/-- A slab observable on the cubic torus of side `2l + 2` of `g.image`: a real function of the
spatial links of the slices and of the time links between them.

DERIVED: `1` is the offset of the transfer chain `l + l + 1`. -/
abbrev SlabObs (g : OpenAIConfig.GaugeGroup) (l : ℕ) : Type :=
  (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
    → (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ

/-- A slab observable read at slice `s` on their configurations of side `2l + 2`, through
`OpenAIConfig.configEquiv⁻¹`.

DERIVED: `0` is the time direction; `1` the offset of the side. -/
noncomputable def readAt {g : OpenAIConfig.GaugeGroup} (l : ℕ) (f : SlabObs g l) (s : ℕ)
    (V : OpenAIConfig.Configuration g (sideP l)) : ℝ :=
  f (slabV (fun _ : Fin 4 => l + l + 1 + 1) 0 s ((OpenAIConfig.configEquiv (sideP l)).symm V))
    (slabA (fun _ : Fin 4 => l + l + 1 + 1) 0 s ((OpenAIConfig.configEquiv (sideP l)).symm V))

/-- The reflection of a slab observable of width `2v + 2` (`OpenAIBridgeRP.revG`, the time links
inverted).

DERIVED: `1` is the offset of the number of steps. -/
noncomputable def reflO {g : OpenAIConfig.GaugeGroup} (l v : ℕ) (f : SlabObs g l) : SlabObs g l :=
  revG (MeasurableEquiv.piCongrRight
    (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv g.image)) (v + v + 1) f

/-- The excited weight `σ₀ = excited (l + 1)` of the transfer kernel of side `2l + 2` at our
coupling `β/2` (their `β`), for the eigenpair `(φ, c)`.

DERIVED: `2` halves their coupling; `0` the time direction; `1` the offsets. -/
noncomputable def excW (g : OpenAIConfig.GaugeGroup) (l : ℕ) (β c : ℝ)
    (φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ) : ℝ :=
  excited (hSG g.image 0 (TorusChain.Tc (l + l + 1))) (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2))
    c φ (l + 1)

/-- The thermal remainder (`OpenAIBridgeCubic.thermRem`) of the slab kernel of a slab observable of
width `2v + 2`, at our coupling `β/2`, for the split `a`, `b`.

DERIVED: `2` halves their coupling and doubles the width; `0` the time direction; `1` the offsets. -/
noncomputable def remW (g : OpenAIConfig.GaugeGroup) (l : ℕ) (β c : ℝ)
    (φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ) (v : ℕ) (f : SlabObs g l)
    (a b : ℕ) : ℝ :=
  thermRem (hSG g.image 0 (TorusChain.Tc (l + l + 1))) (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2))
    c φ (slabKer (hSG g.image 0 (TorusChain.Tc (l + l + 1))) (hAG g.image 0 (TorusChain.Tc (l + l + 1)))
      (TorusChainG.wtG g.image (l + l + 1) (β / 2)) (v + v + 1) f) (v + v + 2) a b

set_option maxHeartbeats 1600000 in
/-- **The per-torus inequality on their laws.** For any of their gauge groups `g` with their Haar
measure `μ`, at their coupling `β ≥ 0`: if a torus of even side `n ≥ 2` carries the seed
`16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β/2`, then on their torus of every side
`2l + 2 ≥ 8n` there is an eigenpair `(φ, c)` of the transfer kernel with excited weight
`0 ≤ σ₀ ≤ (1/2)^⌊(l+1)/n⌋` such that for bounded measurable slab observables `f`, `h` of widths
`2v + 2`, `2v' + 2`, read on their configurations at slices `0` and `2v + 2 + p + 1` with
`p = 2a + j + 2`, the connected correlation under their law `wilsonLaw g (2l+2) β μ` is at most
`cubicRHS n j j' σ₀ M₁ … M₆ √(D_f D_h)`, every `M` a moment of their law of a slab observable and
the reflection of one, at the separations `2a + 2`, `2a_F + 2`, `2a_G + 2`. It is
`OpenAIBridgeCubic.wilson_slab_conn_cubicG` at `g.image` and `β/2`, every expectation carried to
their law by `OpenAIBridgeGroups.expect_eq_openAILawG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `8` the side condition of
`wilson_slab_conn_cubicG`; `4` the spacetime dimension; `2` the halving of the coupling, the doubled
side, widths and separations; `1/2` the contraction; `0` the first slice, the time direction and the
signs; `1` the offsets and the unit norm. -/
theorem openAI_slab_conn_cubic (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure] {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n)
    (h0 : 16 * Real.log (ZRG g.image (fun _ => n) (β / 2))
      - Real.log (ZRG g.image (fun _ => 2 * n) (β / 2)) ≤ 1 / 1000)
    (l : ℕ) (hL : 8 * n ≤ l + l + 2) :
    ∃ φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = 1 ∧
      (∀ z, ∫ y, (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2)) z y * φ y
        ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = c * φ z) ∧
      0 ≤ excW g l β c φ ∧ excW g l β c φ ≤ (1 / 2) ^ ((l + 1) / n) ∧
      ∀ (f h : SlabObs g l),
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
        × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) => f r.1 r.2) →
      Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
        × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) => h r.1 r.2) →
      ∀ A B : ℝ, (∀ V A', |f V A'| ≤ A) → (∀ V A', |h V A'| ≤ B) → ∀ v v' : ℕ,
      LocalUpTo (v + v + 2) f → LocalUpTo (v' + v' + 2) h →
      ∀ a j j' aF bF aG bG cF cG : ℕ,
      a + j + a + 2 = aF + bG + 1 → a + j' + a + 2 = aG + bF + 1 →
      v + v + 2 + aF + bF + 1 = l → v' + v' + 2 + aG + bG + 1 = l →
      v + v + 2 + a + cF + 1 = l → v' + v' + 2 + a + cG + 1 = l →
      |∫ V, readAt l f 0 V * readAt l h (v + v + 2 + (a + j + a + 2 + 1)) V
            ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)
        - (∫ V, readAt l f 0 V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
          * ∫ V, readAt l h (v + v + 2 + (a + j + a + 2 + 1)) V
            ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)|
        ≤ cubicRHS n j j' (excW g l β c φ)
            (∫ V, readAt l f 0 V * readAt l (reflO l v f) (v + v + 2 + (a + a + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            (∫ V, readAt l (reflO l v' h) 0 V * readAt l h (v' + v' + 2 + (a + a + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            (∫ V, readAt l (reflO l v f) 0 V * readAt l f (v + v + 2 + (a + a + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            (∫ V, readAt l h 0 V * readAt l (reflO l v' h) (v' + v' + 2 + (a + a + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            (√(remW g l β c φ v f aF bF * remW g l β c φ v' h aG bG))
            (∫ V, readAt l f 0 V * readAt l (reflO l v f) (v + v + 2 + (aF + aF + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            (∫ V, readAt l h 0 V * readAt l (reflO l v' h) (v' + v' + 2 + (aG + aG + 2)) V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)) := by
  have e : ∀ F : (RLink (fun _ : Fin 4 => l + l + 1 + 1) → g.image) → ℝ,
      (sysRG g.image (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar g.image) (β / 2) F
        = ∫ V, F ((OpenAIConfig.configEquiv (sideP l)).symm V)
            ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) := by
    intro F
    have h1 := expect_eq_openAILawG g μ (sideP l) (β / 2)
      (fun V => F ((OpenAIConfig.configEquiv (sideP l)).symm V))
    simp only [MeasurableEquiv.symm_apply_apply, show 2 * (β / 2) = β by ring] at h1
    exact h1
  obtain ⟨φ, c, hc0, hφ1, heig, hσ, hb⟩ :=
    wilson_slab_conn_cubicG (G := g.image) (div_nonneg hβ zero_le_two) hn he h0 l hL
  refine ⟨φ, c, hc0, hφ1, heig, ?_, hσ,
    fun f h hfm hgm A B hfb hgb v v' hf hg a j j' aF bF aG bG cF cG h1 h2 h3 h4 h5 h6 => ?_⟩
  · unfold excW excited
    exact div_nonneg (hs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  · have hh := hb f h hfm hgm A B hfb hgb v v' hf hg a j j' aF bF aG bG cF cG h1 h2 h3 h4 h5 h6
    simp only [e] at hh
    exact hh

end Torus

/-! ## 4. The composition -/

section Compose

variable {g : OpenAIConfig.GaugeGroup} {n₁ n₂ : ℕ}

/-- **Named input: their smeared connected correlation obeys the cubic bound.** For every time
floor `δ > 0` and internal separation `ε > 0` there is a moment constant `K₀ ≥ 0` such that every
tensor test `t = t₁ ⊗ t₂` whose second factor lies at least `τ ≥ δ` after the first in time and
keep their points `ε` apart
has four excited–excited terms `D i p N` (one per pair of real and imaginary parts of the two
smeared insertions) that vanish relative to `‖t₁‖₁ ‖t₂‖₁` along their order and then in the
spacing, and, eventually along their order and then in the spacing, a seed side `n > 0` with
`n · mesh ≤ ℓ`, gaps `j`, `j'` with `(j+1) · mesh ≥ τ − δ/2` and `(j'+1) · mesh ≥ τ − δ/2`, a torus
half-side `l + 1` with `period ≤ 2 (l+1) · mesh` and excited weight `0 ≤ σ ≤ (1/2)^⌊(l+1)/n⌋`, and
reflected moments `Mf i k ∈ [0, K₀ ‖t₁‖₁²]`, `Mg i k ∈ [0, K₀ ‖t₂‖₁²]`, with the smeared connected
correlation at most the sum over the four pairs `i` of
`cubicRHS n j j' σ (Mf i 0) (Mg i 0) (Mf i 1) (Mg i 1) (D i p N) (Mf i 2) (Mg i 2)`.

`openAI_slab_conn_cubic` is this bound for one pair of real slab observables on their laws; the
connected correlation of `F = f_re + i f_im` and `G = g_re + i g_im` is a sum of the four real
connected correlations with unimodular coefficients. `CubicForm` is not proved for their family:
it asks that the real and imaginary parts of their smeared insertions be such slab observables
(stencil locality, the time axis of their sites against the transfer direction `0`, and
time-translation invariance of their law), that the reflected moments be bounded at physical
separation `≥ δ/4` uniformly over the lattice planes (reflection closure of their tokens and a bound
on the reflected limit correlation), and that the thermal remainders vanish
(`OpenAIBridgeCubic.ThermalRemainderVanishes`).

DERIVED: `4` is the number of pairs of real and imaginary parts; `3` the number of reflected moments
of each insertion in `cubicRHS`; `2` halves the floor `δ`, is the doubled half-side, the square of the
norm and the index of the third moment; `1/2` the contraction; `1` the step offset and the index of
the second moment; `0` the signs and the index of the first moment. -/
def CubicForm (C : WilsonFamily g) (order : ℕ → ℕ) (w₁ : Fin n₁ → C.Token)
    (w₂ : Fin n₂ → C.Token) (ℓ : ℝ) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
      (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
      (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
      (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧ ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
      ∃ D : Fin 4 → ℕ → ℕ → ℝ,
        (∀ i, ∀ η : ℝ, 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          D i p N ≤ η * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) ∧
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∃ n j j' l : ℕ, ∃ σ : ℝ, ∃ Mf Mg : Fin 4 → Fin 3 → ℝ,
            0 < n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
            τ - δ / 2 ≤ ((j : ℝ) + 1) * C.mesh N ∧ τ - δ / 2 ≤ ((j' : ℝ) + 1) * C.mesh N ∧
            0 ≤ σ ∧ σ ≤ (1 / 2) ^ ((l + 1) / n) ∧
            ((C.period p : ℕ) : ℝ) ≤ 2 * (((l : ℝ) + 1) * C.mesh N) ∧
            (∀ i k, 0 ≤ Mf i k ∧ Mf i k ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2) ∧
            (∀ i k, 0 ≤ Mg i k ∧ Mg i k ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2) ∧
            ‖C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂‖
              ≤ ∑ i, cubicRHS n j j' σ (Mf i 0) (Mg i 0) (Mf i 1) (Mg i 1) (D i p N)
                  (Mf i 2) (Mg i 2)

/-- **The thermal remainders give the relative vanishing of `CubicForm`.** If `D` satisfies
`OpenAIBridgeCubic.ThermalRemainderVanishes` along their order and `A > 0`, then for every `η > 0`,
eventually along their order and then in the spacing, `D p N ≤ η A`.

DERIVED: `0` is the sign of `A` and of `η`. -/
theorem relVanish_of_thermalRemainderVanishes {order : ℕ → ℕ} {D : ℕ → ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (h : ThermalRemainderVanishes (fun k N => D (order k) N)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, D p N ≤ η * A :=
  fun η hη => Filter.eventually_map.2 (h (η * A) (mul_pos hη hA))

/-- **The composition: the floored (U) at the seed's rate.** If `ℓ > 0`, their volume order tends
to infinity and `CubicForm C order w₁ w₂ ℓ` holds, then `UniformDecayFrom C order w₁ w₂ (log 2 / ℓ)`:
for every floor `δ`, `ε` the constant `K = 4 (8 K₀(δ, ε) (e^{(log 2/ℓ) δ/2} + 1) + 1)` works.

Eventually along the order the period is at least `4τ + 2ℓ`, so the excited weight satisfies
`σ ≤ 2 e^{−(log 2/ℓ)(l+1)a} ≤ 2 e^{−(log 2/ℓ) period/2} ≤ e^{−2(log 2/ℓ)τ}`
(`half_pow_floor_le_exp`), i.e. `√σ ≤ e^{−(log 2/ℓ)τ}`; the excited–excited term is below
`e^{−(log 2/ℓ)τ} ‖t₁‖₁ ‖t₂‖₁` in the same order; `cubicRHS_le` bounds each of the four pairs.

DERIVED: `2` is the base of the rate and the factor of the doubled period; `4` is `2 · 2`, the
doubled time gap of `√σ` read on half the period, and the number of pairs of real and imaginary
parts; `8` the constant of `cubicRHS_le`; `1` the step offset and the unit of the excited–excited
term; `0` the sign of `ℓ`. -/
theorem uniformDecayFrom_of_cubicForm {C : WilsonFamily g} {order : ℕ → ℕ}
    {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {ℓ : ℝ} (hℓ : 0 < ℓ) (horder : Tendsto order atTop atTop)
    (h : CubicForm C order w₁ w₂ ℓ) : UniformDecayFrom C order w₁ w₂ (Real.log 2 / ℓ) := by
  intro δ ε hδ hε
  obtain ⟨K₀, hK₀, hK⟩ := h δ ε hδ hε
  refine ⟨4 * (8 * K₀ * (Real.exp (Real.log 2 / ℓ * (δ / 2)) + 1) + 1), ?_⟩
  intro t t₁ t₂ τ hτ hs₁ hs₂ ht hg
  obtain ⟨D, hD, hev⟩ := hK t t₁ t₂ τ hτ hs₁ hs₂ ht hg
  have hper : Tendsto (fun k => (((C.period (order k) : ℕ)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (C.periodStrict.tendsto_atTop.comp horder)
  have hP : ∀ᶠ p in Filter.map order atTop, 4 * τ + 2 * ℓ ≤ ((C.period p : ℕ) : ℝ) :=
    Filter.eventually_map.2 (hper.eventually_ge_atTop (4 * τ + 2 * ℓ))
  have hμ : 0 < Real.log 2 / ℓ := div_pos (Real.log_pos one_lt_two) hℓ
  have hμℓ : Real.log 2 / ℓ * ℓ = Real.log 2 := div_mul_cancel₀ _ hℓ.ne'
  have hA : 0 ≤ ∫ y, ‖t₁ y‖ := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ ∫ y, ‖t₂ y‖ := integral_nonneg fun _ => norm_nonneg _
  have hDall : ∀ᶠ p in Filter.map order atTop, ∀ i, ∀ᶠ N in atTop,
      D i p N ≤ Real.exp (-(Real.log 2 / ℓ) * τ) * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) :=
    Filter.eventually_all.2 fun i => hD i _ (Real.exp_pos (-(Real.log 2 / ℓ) * τ))
  filter_upwards [hev, hDall, hP] with p hp hDp hPp
  filter_upwards [hp, Filter.eventually_all.2 hDp] with N hN hDN
  obtain ⟨n, j, j', l, σ, Mf, Mg, hn, hna, hj, hj', hσ0, hσ, hl, hMf, hMg, hc⟩ := hN
  refine hc.trans ?_
  have ha : 0 < C.mesh N := inv_pos.2 (by exact_mod_cast (C.denominator N).pos)
  have hσ1 : σ ≤ 1 := hσ.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have e1 := half_pow_floor_le_exp (j := l) hn ha hℓ hna
  have hlin : Real.log 2 / ℓ * (2 * τ + ℓ) ≤ Real.log 2 / ℓ * (((l : ℝ) + 1) * C.mesh N) :=
    mul_le_mul_of_nonneg_left (by linarith) hμ.le
  have hexp : Real.log 2 / ℓ * (2 * τ + ℓ) = 2 * (Real.log 2 / ℓ * τ) + Real.log 2 := by
    rw [mul_add, hμℓ]; ring
  have key : 2 * Real.exp (-(Real.log 2 / ℓ) * (((l : ℝ) + 1) * C.mesh N))
      ≤ Real.exp (-(Real.log 2 / ℓ) * τ) ^ 2 := by
    rw [sq, ← Real.exp_add]
    calc 2 * Real.exp (-(Real.log 2 / ℓ) * (((l : ℝ) + 1) * C.mesh N))
        = Real.exp (Real.log 2 + -(Real.log 2 / ℓ) * (((l : ℝ) + 1) * C.mesh N)) := by
          rw [Real.exp_add, Real.exp_log two_pos]
      _ ≤ Real.exp (-(Real.log 2 / ℓ) * τ + -(Real.log 2 / ℓ) * τ) := by
          rw [Real.exp_le_exp]; linarith
  have hσs : √σ ≤ Real.exp (-(Real.log 2 / ℓ) * τ) := by
    calc √σ ≤ √(Real.exp (-(Real.log 2 / ℓ) * τ) ^ 2) :=
          Real.sqrt_le_sqrt (hσ.trans (e1.trans key))
      _ = Real.exp (-(Real.log 2 / ℓ) * τ) := Real.sqrt_sq (Real.exp_pos _).le
  calc ∑ i, cubicRHS n j j' σ (Mf i 0) (Mg i 0) (Mf i 1) (Mg i 1) (D i p N) (Mf i 2) (Mg i 2)
      ≤ ∑ _i : Fin 4, (8 * K₀ * (Real.exp (Real.log 2 / ℓ * (δ / 2)) + 1) + 1)
          * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-(Real.log 2 / ℓ) * τ) :=
        Finset.sum_le_sum fun i _ => cubicRHS_le hn ha hℓ hna hj hj' hσ0 hσ1 hσs hK₀ hA hB
          (hMf i 0) (hMg i 0) (hMf i 1) (hMg i 1) (hMf i 2) (hMg i 2) (hDN i)
    _ = 4 * (8 * K₀ * (Real.exp (Real.log 2 / ℓ * (δ / 2)) + 1) + 1)
          * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖) * Real.exp (-(Real.log 2 / ℓ) * τ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **(U) for every pair of token groups from the cubic form.** If `ℓ > 0`, their volume order tends
to infinity and every pair of token groups of at least one token satisfies `CubicForm` at `ℓ`, then
`UniformDecayAll C order`, at the rate `log 2 / ℓ` for every pair.

DERIVED: `2` is the base of the rate; `0` the lower bound of the group sizes, of `ℓ` and of the
rate. -/
theorem uniformDecayAll_of_cubicForm {C : WilsonFamily g} {order : ℕ → ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (horder : Tendsto order atTop atTop)
    (h : ∀ {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token), 0 < n₁ → 0 < n₂ →
      CubicForm C order w₁ w₂ ℓ) :
    UniformDecayAll C order :=
  fun w₁ w₂ h₁ h₂ => ⟨Real.log 2 / ℓ, div_pos (Real.log_pos one_lt_two) hℓ,
    uniformDecayFrom_of_cubicForm hℓ horder (h w₁ w₂ h₁ h₂)⟩

end Compose

end MassGap.OpenAIBridgeCompose

#print axioms MassGap.OpenAIBridgeCompose.half_pow_floor_le_exp
#print axioms MassGap.OpenAIBridgeCompose.cubicRHS_le
#print axioms MassGap.OpenAIBridgeCompose.openAI_slab_conn_cubic
#print axioms MassGap.OpenAIBridgeCompose.relVanish_of_thermalRemainderVanishes
#print axioms MassGap.OpenAIBridgeCompose.uniformDecayFrom_of_cubicForm
#print axioms MassGap.OpenAIBridgeCompose.uniformDecayAll_of_cubicForm
