import Mathlib
import MassGap.StripWiden
import MassGap.MixAnchor
import MassGap.DoublingSharp
import MassGap.KernelGap
import MassGap.TransferGap

/-!
# MassGap.StripGapThm — a transfer gap on the anisotropic torus, inside the glued strip

`StripWiden.strip_width_glue` says the anisotropic doubling defect `DA(β, t, ·)` vanishes along the windows for
`0 ≤ t ≤ t_glue(N, β)`. Its proof goes through one seed window `w₀` with `DA(β, t, w₀) ≤ 1/1000`. This module
reads the same seed as a spectral statement: the transverse transfer operator of the anisotropic torus has a gap,
in each of the four directions, at every window `w ≥ w₀`, with a rate that does not depend on `w`. The argument
is `DoublingSharp.wilson_gap_sharp` with the Wilson kernel `kT` replaced by the orientation-weighted kernel
`MixAnchor.kC (cA β t)`, whose trace facts are `MixAnchor.factRepC`. Declarations are in
`MassGap.StripGapThm`.

## The result

* `areaG N β = A_glue(ℓ, L)`, `seedWindow N β = ⌈log₄ A_glue⌉` (`w₀`), `stripMass N β = log 2 / 2^{w₀}` (`m`).
* `seedWindow_spec`: `1 ≤ w₀`, `A_glue ≤ 4^{w₀} ≤ 4 A_glue`.
* `seed_strip`: `DA(β, t, w₀) ≤ 1/1000` for `0 ≤ t ≤ t_glue`.
* `p_le_Δ_dir`, `excited_le_corner_dir`: the excited-weight bound of `DoublingSharp.excited_le_corner_sharp` in
  every direction `μ`, not only `μ = 0`.
* `gap_core`: from any seed `DA(β, t, w) ≤ 1/1000`, on the torus of side `2^{w+k}` and in direction `μ`, the
  operator `K` of `kC (cA β t)` on `L²` of the transverse slice has a unit eigenvector `ψ` at `|e| = ‖K‖` and
  `‖K^{2^w} f‖ ≤ ½ ‖K‖^{2^w} ‖f‖` for `f ⊥ ψ`; the normalized `2^w`-step transfer is a
  `Transfer.TransferData` with `TransferGap.GapAt` at `1/2`.
* `pow_gap_all`: on a real inner product space, a self-adjoint `K` with `Kψ = eψ` and that `n`-step bound gives
  `‖K^r f‖ ≤ 2 e^{−(log 2/n) r} ‖K‖^r ‖f‖` for every `r` and `f ⊥ ψ`.
* `strip_gap`: for `N ≠ 0`, `β ≥ 0`, `0 ≤ t ≤ t_glue(N, β)`, every direction `μ` and every window `w ≥ w₀`,
  with `K = KA` the transverse transfer operator on the cubic torus of side `2^w`:
  `‖K^{2^{w₀}} f‖ ≤ e^{−m 2^{w₀}} ‖K‖^{2^{w₀}} ‖f‖` and `‖K^r f‖ ≤ 2 e^{−m r} ‖K‖^r ‖f‖` for every lag `r` and
  every `f ⊥ ψ`. So `λ₁/λ₀ ≤ e^{−m}` on the vacuum complement, uniformly in `w`, in lattice units.
* `strip_cluster`: the same as `TransferGap.GapAt` at `e^{−m 2^{w₀}} = 1/2` for the normalized `2^{w₀}`-step
  transfer, and the clustering bound of `TransferGap.clustering_sq` for it: for every `ℓ` and `x, y` in `L²`,
  `(⟨y, T^ℓ x⟩ − ⟨y, Ω⟩⟨Ω, x⟩)² ≤ e^{−2 m 2^{w₀} ℓ} ‖y‖² ‖x − ⟨x, Ω⟩Ω‖²`.
* `stripMass_pos`, `stripMass_ge`: `0 < m` and `m ≥ log 2 / (2 √A_glue)`.

Read off the closed form (not a Lean statement): `A_glue ≍ ℓ L`, `ℓ = 240 + 150 (N + 4) β`, `L ≍ N² log β`, so
`m ≳ c_N^{−1/2} (β log β)^{−1/2}` in lattice units.

DERIVED (module-wide): `2` the doubling, the least side and the excited ratio `½`; `4 = 2²` the area of the
doubling; `8 = 2³` the first step of a four-step path to the diagonal corner; `0` the vacuum and the decoupled
end; `1` the least window and the unit vector. Inherited: `1/1000` the seed and `250` the squaring constant of
`DoublingSharp`; `1/2000`, `8192`, `16192` of `StripWidth`/`StripWiden`. COMPUTED: `4048 = 16192/4`, and
`8192/4048² ≤ 1/2000`.

## What does not follow

* This is a gap for the anisotropic theory (in-plane coupling `β`, mixed coupling `t ≤ t_glue(N, β)`), not for the
  isotropic Wilson theory. `t_glue ≍ c_N⁻¹ (β log β)⁻¹`, so the strip never reaches `t = β`.
* The gap in lattice units shrinks with `β`: `m = log 2 / 2^{w₀}` with `4^{w₀} ≍ A_glue ≍ β log β`. Nothing
  here bounds `m` below uniformly in `β`, and no continuum statement follows.
* The gap is for the operator of `kC` on `L²` of the transverse slice of a finite cubic torus of side `2^w`, at
  every `w ≥ w₀`; no infinite-volume limit of the operator or of the state is built.
* The clustering is of the transfer form on `L²` of slice configurations. Identifying `⟨y, T^ℓ x⟩` with a
  correlation of gauge-invariant lattice observables on the torus is not done here.
-/

namespace MassGap.StripGapThm

open MeasureTheory Filter Topology Set MassGap MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SlabKernelOperator MassGap.DoublingRecursion MassGap.MixAnchor

variable {N : ℕ}

/-! ## 1. The seed window and the rate -/

/-- **The glued seed area** `A_glue(ℓ, L)` at `ℓ = gapArea N β`, `L = bulkExp N β`. No numeral. -/
noncomputable def areaG (N : ℕ) (β : ℝ) : ℝ :=
  StripWiden.glueArea (StripGap.gapArea N β) (StripWidth.bulkExp N β)

/-- **The seed window** `w₀ = ⌈log₄ A_glue⌉`. DERIVED: `4 = 2²` the area of the doubling. -/
noncomputable def seedWindow (N : ℕ) (β : ℝ) : ℕ := ⌈Real.logb 4 (areaG N β)⌉₊

/-- **The strip mass** `m = log 2 / 2^{w₀}`, in lattice units. DERIVED: `2` the excited ratio and the doubling. -/
noncomputable def stripMass (N : ℕ) (β : ℝ) : ℝ := Real.log 2 / 2 ^ seedWindow N β

theorem one_lt_areaG {β : ℝ} (hβ : 0 ≤ β) : 1 < areaG N β := by
  have hl240 : (240 : ℝ) ≤ StripGap.gapArea N β := StripGap.gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (StripGap.gapArea N β) := Real.log_nonneg (by linarith)
  have hL := StripWidth.bulkExp_nonneg (N := N) β
  unfold areaG StripWiden.glueArea
  nlinarith

/-- **The seed window brackets the area**: `1 ≤ w₀` and `A_glue ≤ 4^{w₀} ≤ 4 A_glue`. DERIVED: `4 = 2²`; `1` the
least window. -/
theorem seedWindow_spec {β : ℝ} (hβ : 0 ≤ β) :
    1 ≤ seedWindow N β ∧ areaG N β ≤ (4 : ℝ) ^ seedWindow N β ∧
      (4 : ℝ) ^ seedWindow N β ≤ 4 * areaG N β := by
  have hA := one_lt_areaG (N := N) hβ
  have h4 : (1 : ℝ) < 4 := by norm_num
  have hx : 0 < Real.logb 4 (areaG N β) := Real.logb_pos h4 hA
  have hApos : 0 < areaG N β := by linarith
  unfold seedWindow
  refine ⟨Nat.ceil_pos.2 hx, ?_, ?_⟩
  · calc areaG N β = (4 : ℝ) ^ Real.logb 4 (areaG N β) := (Real.rpow_logb (by norm_num) h4.ne' hApos).symm
      _ ≤ (4 : ℝ) ^ (⌈Real.logb 4 (areaG N β)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h4.le (Nat.le_ceil _)
      _ = _ := Real.rpow_natCast _ _
  · have hc : (⌈Real.logb 4 (areaG N β)⌉₊ : ℝ) ≤ Real.logb 4 (areaG N β) + 1 :=
      (Nat.ceil_lt_add_one hx.le).le
    calc (4 : ℝ) ^ ⌈Real.logb 4 (areaG N β)⌉₊ = (4 : ℝ) ^ (⌈Real.logb 4 (areaG N β)⌉₊ : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (4 : ℝ) ^ (Real.logb 4 (areaG N β) + 1) := Real.rpow_le_rpow_of_exponent_le h4.le hc
      _ = 4 * areaG N β := by
        rw [Real.rpow_add_one (by norm_num), Real.rpow_logb (by norm_num) h4.ne' hApos]
        ring

theorem stripMass_pos (β : ℝ) : 0 < stripMass N β := by
  unfold stripMass
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

/-- `e^{−m 2^{w₀}} = 1/2`. DERIVED: `2` the excited ratio. -/
theorem exp_stripMass (β : ℝ) :
    Real.exp (-(stripMass N β * 2 ^ seedWindow N β)) = 1 / 2 := by
  have hp : (0 : ℝ) < 2 ^ seedWindow N β := by positivity
  have e : stripMass N β * 2 ^ seedWindow N β = Real.log 2 := by
    unfold stripMass; field_simp
  rw [e, Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- **The rate in the area**: `m ≥ log 2 / (2 √A_glue)`. DERIVED: `4 = 2²`, so `2^{w₀} ≤ 2 √A_glue`. -/
theorem stripMass_ge {β : ℝ} (hβ : 0 ≤ β) :
    Real.log 2 / (2 * Real.sqrt (areaG N β)) ≤ stripMass N β := by
  obtain ⟨-, -, h2⟩ := seedWindow_spec (N := N) hβ
  have hA := one_lt_areaG (N := N) hβ
  have e : (4 : ℝ) ^ seedWindow N β = ((2 : ℝ) ^ seedWindow N β) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsq : ((2 : ℝ) ^ seedWindow N β) ^ 2 ≤ (2 * Real.sqrt (areaG N β)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), ← e]; linarith
  have hs : (2 : ℝ) ^ seedWindow N β ≤ 2 * Real.sqrt (areaG N β) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  unfold stripMass
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by positivity) hs

/-- **The seed inside the strip**: `DA(β, t, w₀) ≤ 1/1000` for `0 ≤ t ≤ t_glue(N, β)`. Inherited: `1/2000` of
`StripWiden.seed_glue`, `8192` of `StripWidth.DA_le`. COMPUTED: `4048 = 16192/4`; `8192/4048² ≤ 1/2000`. -/
theorem seed_strip (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ StripWiden.tGlue N β) :
    AnisoTorus.DA N β t (seedWindow N β) ≤ 1 / 1000 := by
  obtain ⟨hw, h1, h2⟩ := seedWindow_spec (N := N) hβ
  have h0 : AnisoTorus.DA N β 0 (seedWindow N β) ≤ 1 / 2000 :=
    StripWiden.seed_glue hN hβ (StripWidth.bulkExp_nonneg β) (StripWidth.one_div_bk_le hN hβ) hw h1
  have hA := one_lt_areaG (N := N) hβ
  have hpos : (0 : ℝ) < (4 : ℝ) ^ seedWindow N β := by positivity
  have hts' : t ≤ 1 / (16192 * areaG N β) := hts
  have ht1 : t * (16192 * areaG N β) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hts'
  have h3 := mul_le_mul_of_nonneg_right h2 ht
  have htw : (4 : ℝ) ^ seedWindow N β * t ≤ 1 / 4048 := by nlinarith
  have hsq : ((4 : ℝ) ^ seedWindow N β * t) ^ 2 ≤ (1 / 4048) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hpos.le ht) htw 2
  have hD := StripWidth.DA_le hN β t hw
  have e : ((4 : ℝ) ^ seedWindow N β) ^ 2 * t ^ 2 = ((4 : ℝ) ^ seedWindow N β * t) ^ 2 := by ring
  nlinarith

/-! ## 2. The excited weight in every direction -/

/-- A four-step path from `a` to `a + 𝟙` starting in direction `μ`: `8 p_μ(a) ≤ Δ(a)`. DERIVED: `8, 4, 2, 1` the
weights `2³, 2², 2, 1` of the four steps. -/
theorem p_le_Δ_path {x : Pt → ℝ} (hx : Positive x) (a : Pt) (μ ν ρ σ : Fin 4)
    (h : E μ + E ν + E ρ + E σ = one) : 8 * p x μ a ≤ Δ x a := by
  have b1 := nn hx μ a (a + E μ) rfl
  have b2 := nn hx ν (a + E μ) (a + E μ + E ν) rfl
  have b3 := nn hx ρ (a + E μ + E ν) (a + E μ + E ν + E ρ) rfl
  have b4 := nn hx σ (a + E μ + E ν + E ρ) (a + one) (by rw [← h]; simp only [add_assoc])
  unfold Δ p
  linarith

/-- **`8 p_μ ≤ Δ` in every direction.** DERIVED: as in `p_le_Δ_path`: `8 = 2³` the weight of the first
of the four steps. -/
theorem p_le_Δ_dir {x : Pt → ℝ} (hx : Positive x) (a : Pt) (μ : Fin 4) : 8 * p x μ a ≤ Δ x a := by
  fin_cases μ
  · exact p_le_Δ_path hx a 0 1 2 3 (by decide)
  · exact p_le_Δ_path hx a 1 0 2 3 (by decide)
  · exact p_le_Δ_path hx a 2 0 1 3 (by decide)
  · exact p_le_Δ_path hx a 3 0 1 2 (by decide)

/-- **The excited weight at corner `k` in direction `μ`** from the sharp seed: `s ≤ (1/2)^{2^k}`. Inherited:
`1/1000`, `250` of `DoublingSharp`. DERIVED: `1/4 = (1/2)²`, `2` the doubling; `1000` the denominator
of the inherited seed `1/1000`. -/
theorem excited_le_corner_dir {x : Pt → ℝ} (hx : DoublingSharp.PositiveS x) (hp : Positive x)
    (h0 : Δ x (corner 0) ≤ 1 / 1000) (μ : Fin 4) (k : ℕ) {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}
    (h : DoublingPower.PowerFacts a lam s m) (h1 : x (corner k) = Real.log (a m))
    (h2 : x (corner k + E μ) = Real.log (a (2 * m))) :
    s ≤ (1 / 2) ^ (2 ^ k) := by
  have hit := DoublingSharp.iterate_sharp hx hp (by linarith) k
  have hpd : p x μ (corner k) = DoublingPower.defect a m := by rw [p, h1, h2]; rfl
  have h8 := p_le_Δ_dir hp (corner k) μ
  have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ (1 / 2) ^ (2 ^ k) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hq1 : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := k))
    simpa using this
  have hpos : 0 ≤ ((1 : ℝ) / 4) ^ (2 ^ k) := by positivity
  have hd : DoublingPower.defect a m ≤ 1 / 4 := by rw [← hpd]; linarith
  have := DoublingPower.excited_le_two_defect h hd
  rw [← hpd] at this
  linarith

/-! ## 3. The anisotropic transfer operator and its gap -/

/-- **The anisotropic transverse transfer operator**: the `L²` operator of `kC (cA β t)` on the slice
transverse to `μ` with extents `T`. DERIVED: `1` the kernel bound, `0` its sign. -/
noncomputable def KA (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (μ : Fin 4)
    (T : {j : Fin 4 // j ≠ μ} → ℕ) : Lp ℝ 2 (hS μ T N) →L[ℝ] Lp ℝ 2 (hS μ T N) :=
  kernelCLM (kC (cA β t) μ T N) 1 (continuous_kC (cA β t)).measurable zero_le_one
    (abs_kC_le hN (cA_nonneg hβ ht)) (hS μ T N) (hS μ T N)

/-- **The gap from one seed**: if `DA(β, t, w) ≤ 1/1000`, then on the torus of side `2^{w+k}` and in direction
`μ` the operator `K = KA` has a unit eigenvector `ψ` at `|e| = ‖K‖`, `‖K^{2^w} f‖ ≤ ½ ‖K‖^{2^w} ‖f‖` for
`f ⊥ ψ`, and the normalized `2^w`-step transfer is a `TransferData` with vacuum `ψ` and `GapAt` at `1/2`.
Inherited: `1/1000` of `DoublingSharp`. DERIVED: `2` the doubling and the excited ratio; `1` the unit vector;
`1000` the denominator of the inherited seed `1/1000`. -/
theorem gap_core (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {w : ℕ} (hw : 1 ≤ w)
    (h0 : AnisoTorus.DA N β t w ≤ 1 / 1000) (μ : Fin 4) (k : ℕ) (T : {j : Fin 4 // j ≠ μ} → ℕ)
    (hT : tr (DoublingWilson.ext (2 ^ w) (corner k)) μ = T) :
    ∃ ψ : Lp ℝ 2 (hS μ T N), ‖ψ‖ = 1 ∧ ∃ e : ℝ, |e| = ‖KA hN hβ ht μ T‖ ∧ KA hN hβ ht μ T ψ = e • ψ ∧
      (∀ f : Lp ℝ 2 (hS μ T N), inner ℝ f ψ = 0 →
        ‖((KA hN hβ ht μ T) ^ (2 ^ w)) f‖ ≤ 1 / 2 * ‖KA hN hβ ht μ T‖ ^ (2 ^ w) * ‖f‖) ∧
      ∃ D : Transfer.TransferData (Lp ℝ 2 (hS μ T N)), (∀ u v, D.form u v = inner ℝ u v) ∧ D.vac = ψ ∧
        (∀ u, D.T u = (‖KA hN hβ ht μ T‖ ^ (2 ^ w))⁻¹ • ((KA hN hβ ht μ T) ^ (2 ^ w)) u) ∧
        TransferGap.GapAt D (1 / 2) := by
  subst hT
  have hn : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have he : Even (2 ^ w) := DeltaLengthTower.even_two_pow hw
  have hc := cA_nonneg hβ ht
  have hsym := cA_symm β t
  have hfr := factRepA hN hβ ht hw
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xC (cA β t) N (2 ^ w)) (corner 0) ≤ 1 / 1000 := by rw [Δ_xA, add_zero]; exact h0
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc', heig⟩ :=
    KernelEigen.exists_eigen (μ := hS μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) N)
      (continuous_kC (cA β t)) zero_le_one (abs_kC_le hN hc) (kC_symm (cA β t))
      (K_posC hN hc μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ))
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc'
    linarith [K_posC hN hc μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ)]
  have he2 := he
  obtain ⟨n', hn'⟩ := he2
  set j := 2 ^ k * n' with hjdef
  have hj : 1 ≤ j := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by rw [hn'] at hn; omega
    rw [hjdef]; exact Nat.mul_le_mul h1 h2
  have hpf := KernelPower.powerFacts
    (μ := hS μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) N) (continuous_kC (cA β t)).measurable
    zero_le_one (abs_kC_le hN hc) (kC_symm (cA β t)) hφm hφb hφ1 heig hc' hc0 j hj
  have hm : DoublingWilson.ext (2 ^ w) (corner k) μ = 2 * j := by
    simp only [DoublingWilson.ext, corner, hjdef, hn']; ring
  have h1 : xC (cA β t) N (2 ^ w) (corner k)
      = Real.log (FC (cA β t) N μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) (2 * j)) := by
    rw [xC_eq hN hc hsym hn he (corner k) μ, hm]
  have h2 : xC (cA β t) N (2 ^ w) (corner k + E μ)
      = Real.log (FC (cA β t) N μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) (2 * (2 * j))) := by
    rw [xC_eq hN hc hsym hn he (corner k + E μ) μ, DoublingWilson.tr_ext_add,
      DoublingWilson.ext_add_self, hm]
  have hexc := excited_le_corner_dir hx hp hΔ μ k hpf h1 h2
  have hidx : 2 ^ k * 2 ^ w / 2 = j := by
    rw [hn', hjdef, show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have hexc' : KernelPower.excited (hS μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) N)
      (kC (cA β t) μ (tr (DoublingWilson.ext (2 ^ w) (corner k)) μ) N) c φ (2 ^ k * 2 ^ w / 2)
      ≤ (1 / 2) ^ (2 ^ k) := by rw [hidx]; exact hexc
  have hnpos : 0 < 2 ^ w := by positivity
  refine ⟨KernelGap.vac hφm hφb, KernelGap.norm_vac hφm hφb hφ1, c, hc',
    KernelGap.K_vac _ _ _ hφm hφb heig, fun f hf => ?_, ?_⟩
  · exact KernelGap.gap_of_excited (continuous_kC (cA β t)).measurable zero_le_one (abs_kC_le hN hc)
      (kC_symm (cA β t)) hφm hφb hφ1 heig hc' hc0 k (2 ^ w) hnpos he hexc' f hf
  · refine ⟨KernelGap.transferData (continuous_kC (cA β t)).measurable zero_le_one (abs_kC_le hN hc)
      (kC_symm (cA β t)) hφm hφb hφ1 heig hc' hc0 (2 ^ w) he, fun u v => rfl, rfl, fun u => rfl,
      KernelGap.gapAt_half (continuous_kC (cA β t)).measurable zero_le_one (abs_kC_le hN hc)
      (kC_symm (cA β t)) hφm hφb hφ1 heig hc' hc0 k (2 ^ w) hnpos he hexc'⟩

/-! ## 4. Every lag from the `n`-step gap -/

/-- **The `n`-step gap at every lag**: for `K` self-adjoint with `Kψ = eψ` and `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖` on `ψ⊥`,
`‖K^r f‖ ≤ 2 e^{−(log 2/n) r} ‖K‖^r ‖f‖` for every `r` and `f ⊥ ψ`. DERIVED: `2` the excited ratio and the
prefactor `2 = e^{log 2}` paid by the remainder `r mod n`; `0` the vacuum. -/
theorem pow_gap_all {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : E →L[ℝ] E}
    (hK : ∀ u v, inner ℝ (K u) v = inner ℝ u (K v)) {ψ : E} {e : ℝ} (hψ : K ψ = e • ψ)
    {n : ℕ} (hn : 0 < n)
    (hg : ∀ f : E, inner ℝ f ψ = 0 → ‖(K ^ n) f‖ ≤ 1 / 2 * ‖K‖ ^ n * ‖f‖)
    (f : E) (hf : inner ℝ f ψ = 0) (r : ℕ) :
    ‖(K ^ r) f‖ ≤ 2 * Real.exp (-(Real.log 2 / n * r)) * ‖K‖ ^ r * ‖f‖ := by
  have horth : ∀ g : E, inner ℝ g ψ = 0 → inner ℝ (K g) ψ = 0 := by
    intro g hg0
    rw [hK, hψ, inner_smul_right, hg0, mul_zero]
  have horthp : ∀ (i : ℕ) (g : E), inner ℝ g ψ = 0 → inner ℝ ((K ^ i) g) ψ = 0 := by
    intro i
    induction i with
    | zero => intro g hg0; simpa using hg0
    | succ i ih =>
      intro g hg0
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact horth _ (ih g hg0)
  have hmul : ∀ (l : ℕ) (g : E), inner ℝ g ψ = 0 →
      ‖(K ^ (n * l)) g‖ ≤ (1 / 2) ^ l * ‖K‖ ^ (n * l) * ‖g‖ := by
    intro l
    induction l with
    | zero => intro g _; simp
    | succ l ih =>
      intro g hg0
      have e1 : n * (l + 1) = n + n * l := by ring
      rw [e1, pow_add, ContinuousLinearMap.mul_apply]
      have a1 := hg _ (horthp (n * l) g hg0)
      have a2 := ih g hg0
      have hKn : 0 ≤ 1 / 2 * ‖K‖ ^ n := by positivity
      calc ‖(K ^ n) ((K ^ (n * l)) g)‖ ≤ 1 / 2 * ‖K‖ ^ n * ‖(K ^ (n * l)) g‖ := a1
        _ ≤ 1 / 2 * ‖K‖ ^ n * ((1 / 2) ^ l * ‖K‖ ^ (n * l) * ‖g‖) :=
            mul_le_mul_of_nonneg_left a2 hKn
        _ = (1 / 2) ^ (l + 1) * ‖K‖ ^ (n + n * l) * ‖g‖ := by rw [pow_succ, pow_add]; ring
  obtain ⟨q, s, hs, hr⟩ : ∃ q s : ℕ, s < n ∧ r = s + n * q :=
    ⟨r / n, r % n, Nat.mod_lt r hn, by rw [add_comm]; exact (Nat.div_add_mod r n).symm⟩
  subst hr
  have hbound : ‖(K ^ (s + n * q)) f‖ ≤ (1 / 2) ^ q * ‖K‖ ^ (s + n * q) * ‖f‖ := by
    rw [pow_add, ContinuousLinearMap.mul_apply]
    have a1 := KernelGap.norm_pow_apply_le K ((K ^ (n * q)) f) s
    have a2 := hmul q f hf
    calc ‖(K ^ s) ((K ^ (n * q)) f)‖ ≤ ‖K‖ ^ s * ‖(K ^ (n * q)) f‖ := a1
      _ ≤ ‖K‖ ^ s * ((1 / 2) ^ q * ‖K‖ ^ (n * q) * ‖f‖) :=
          mul_le_mul_of_nonneg_left a2 (by positivity)
      _ = (1 / 2) ^ q * ‖K‖ ^ (s + n * q) * ‖f‖ := by rw [pow_add]; ring
  have hq : (1 / 2 : ℝ) ^ q ≤ 2 * Real.exp (-(Real.log 2 / n * ((s + n * q : ℕ) : ℝ))) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : (s : ℝ) < n := by exact_mod_cast hs
    have e1 : (1 / 2 : ℝ) ^ q = Real.exp (-(Real.log 2 * q)) := by
      rw [show -(Real.log 2 * q) = (q : ℝ) * Real.log (1 / 2) by rw [one_div, Real.log_inv]; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have e2 : 2 * Real.exp (-(Real.log 2 / n * ((s + n * q : ℕ) : ℝ)))
        = Real.exp (Real.log 2 - Real.log 2 / n * ((s + n * q : ℕ) : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]; ring
    rw [e1, e2]
    apply Real.exp_le_exp.mpr
    have e3 : Real.log 2 / n * ((s + n * q : ℕ) : ℝ) = Real.log 2 * q + Real.log 2 * (s / n) := by
      push_cast; field_simp; ring
    have hsn' : (s : ℝ) / n < 1 := (div_lt_one hnr).mpr hsn
    rw [e3]
    nlinarith
  calc ‖(K ^ (s + n * q)) f‖ ≤ (1 / 2) ^ q * ‖K‖ ^ (s + n * q) * ‖f‖ := hbound
    _ ≤ 2 * Real.exp (-(Real.log 2 / n * ((s + n * q : ℕ) : ℝ))) * ‖K‖ ^ (s + n * q) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (by positivity)) (norm_nonneg _)

/-! ## 5. The gap inside the strip -/

/-- **`strip_gap`: the anisotropic transfer gap inside the glued strip.** For `N ≠ 0`, `β ≥ 0`,
`0 ≤ t ≤ t_glue(N, β)`, every direction `μ` and every window `w ≥ w₀ = seedWindow N β`, the transverse transfer
operator `K` of the anisotropic cubic torus of side `2^w` has a unit eigenvector `ψ` at `|e| = ‖K‖`, and on
`ψ⊥`: `‖K^{2^{w₀}} f‖ ≤ e^{−m 2^{w₀}} ‖K‖^{2^{w₀}} ‖f‖` and `‖K^r f‖ ≤ 2 e^{−m r} ‖K‖^r ‖f‖` at every lag `r`,
with `m = stripMass N β = log 2 / 2^{w₀}`, uniformly in `w`. DERIVED: `2` the doubling and the prefactor. -/
theorem strip_gap (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ StripWiden.tGlue N β)
    (μ : Fin 4) {w : ℕ} (hw : seedWindow N β ≤ w) :
    ∃ ψ : Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ w) μ) N), ‖ψ‖ = 1 ∧
      ∃ e : ℝ, |e| = ‖KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)‖ ∧
        KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ) ψ = e • ψ ∧
        ∀ f : Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ w) μ) N), inner ℝ f ψ = 0 →
          ‖((KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)) ^ (2 ^ seedWindow N β)) f‖
              ≤ Real.exp (-(stripMass N β * 2 ^ seedWindow N β))
                * ‖KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)‖ ^ (2 ^ seedWindow N β) * ‖f‖ ∧
          ∀ r : ℕ, ‖((KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)) ^ r) f‖
              ≤ 2 * Real.exp (-(stripMass N β * r))
                * ‖KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)‖ ^ r * ‖f‖ := by
  obtain ⟨hw1, -, -⟩ := seedWindow_spec (N := N) hβ
  obtain ⟨k, rfl⟩ : ∃ k, w = seedWindow N β + k := ⟨w - seedWindow N β, by omega⟩
  have hT : tr (DoublingWilson.ext (2 ^ seedWindow N β) (corner k)) μ
      = tr (fun _ => 2 ^ (seedWindow N β + k)) μ := by
    congr 1; funext i; simp only [DoublingWilson.ext, corner]; rw [← pow_add, add_comm]
  obtain ⟨ψ, hψ1, e, he, hKψ, hg, -⟩ := gap_core hN hβ ht hw1 (seed_strip hN hβ ht hts) μ k _ hT
  refine ⟨ψ, hψ1, e, he, hKψ, fun f hf => ⟨?_, fun r => ?_⟩⟩
  · rw [exp_stripMass]; exact hg f hf
  · have hK : ∀ u v, inner ℝ (KA hN hβ ht μ (tr (fun _ => 2 ^ (seedWindow N β + k)) μ) u) v
        = inner ℝ u (KA hN hβ ht μ (tr (fun _ => 2 ^ (seedWindow N β + k)) μ) v) := by
      intro u v
      unfold KA
      exact (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ 1 _ zero_le_one _ _
        (kC_symm (cA β t))).isSymmetric u v
    have h := pow_gap_all hK hKψ (by positivity) hg f hf r
    have em : Real.log 2 / ((2 ^ seedWindow N β : ℕ) : ℝ) = stripMass N β := by
      unfold stripMass; push_cast; rfl
    rwa [em] at h

/-- **`strip_cluster`: the strip gap as `GapAt`, and clustering of the transfer form.** Same hypotheses as
`strip_gap`. The normalized `2^{w₀}`-step transfer `‖K‖^{−2^{w₀}} K^{2^{w₀}}` is a `Transfer.TransferData` on
`L²` with the `L²` inner product, `GapAt` at `e^{−m 2^{w₀}}`, and for every `ℓ` and `x, y`:
`(⟨y, T^ℓ x⟩ − ⟨y, Ω⟩⟨Ω, x⟩)² ≤ e^{−2 m 2^{w₀} ℓ} ⟨y, y⟩ ⟨x_⊥, x_⊥⟩`. The inner product is the transfer
inner product on L² of slice configurations of the torus. It is not shown equal to a correlation of gauge-invariant
lattice observables. DERIVED: `2` the form's degree. -/
theorem strip_cluster (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ StripWiden.tGlue N β)
    (μ : Fin 4) {w : ℕ} (hw : seedWindow N β ≤ w) :
    ∃ D : Transfer.TransferData (Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ w) μ) N)),
      (∀ u v, D.form u v = inner ℝ u v) ∧
      (∀ u, D.T u = (‖KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)‖ ^ (2 ^ seedWindow N β))⁻¹ •
          ((KA hN hβ ht μ (tr (fun _ => 2 ^ w) μ)) ^ (2 ^ seedWindow N β)) u) ∧
      TransferGap.GapAt D (Real.exp (-(stripMass N β * 2 ^ seedWindow N β))) ∧
      ∀ (l : ℕ) (x y : Lp ℝ 2 (hS μ (tr (fun _ => 2 ^ w) μ) N)),
        (D.form y ((D.T ^ l) x) - D.form y D.vac * D.form D.vac x) ^ 2
          ≤ Real.exp (-(stripMass N β * 2 ^ seedWindow N β)) ^ (2 * l) *
            (D.form y y * D.form (TransferGap.vacProj D x) (TransferGap.vacProj D x)) := by
  obtain ⟨hw1, -, -⟩ := seedWindow_spec (N := N) hβ
  obtain ⟨k, rfl⟩ : ∃ k, w = seedWindow N β + k := ⟨w - seedWindow N β, by omega⟩
  have hT : tr (DoublingWilson.ext (2 ^ seedWindow N β) (corner k)) μ
      = tr (fun _ => 2 ^ (seedWindow N β + k)) μ := by
    congr 1; funext i; simp only [DoublingWilson.ext, corner]; rw [← pow_add, add_comm]
  obtain ⟨-, -, -, -, -, -, D, hform, -, hDT, hgap⟩ :=
    gap_core hN hβ ht hw1 (seed_strip hN hβ ht hts) μ k _ hT
  rw [exp_stripMass]
  exact ⟨D, hform, hDT, hgap, fun l x y => TransferGap.clustering_sq D (by norm_num) hgap l x y⟩

end MassGap.StripGapThm

#print axioms MassGap.StripGapThm.one_lt_areaG
#print axioms MassGap.StripGapThm.seedWindow_spec
#print axioms MassGap.StripGapThm.stripMass_pos
#print axioms MassGap.StripGapThm.exp_stripMass
#print axioms MassGap.StripGapThm.stripMass_ge
#print axioms MassGap.StripGapThm.seed_strip
#print axioms MassGap.StripGapThm.p_le_Δ_path
#print axioms MassGap.StripGapThm.p_le_Δ_dir
#print axioms MassGap.StripGapThm.excited_le_corner_dir
#print axioms MassGap.StripGapThm.gap_core
#print axioms MassGap.StripGapThm.pow_gap_all
#print axioms MassGap.StripGapThm.strip_gap
#print axioms MassGap.StripGapThm.strip_cluster
