import Mathlib
import MassGap.ApertureGap

/-!
# MassGap.StrongPhys — the far input from one contraction of the slab transfer at a fixed physical length

The cyclic integrals of the slice kernel read the `n`-step slab kernel `kT^{∗n}` on the fine cross-section:
`cyc(kT, n) = ∫ kT^{∗n}(x, x)` and `cyc(kT, 2n) = ∫∫ kT^{∗n}(x, y) kT^{∗n}(y, x)`. The doubling defect is small
when the slab kernel is close to rank one in the cross-ratio sense (`ApertureGap.cyc_double_ge_of`). This
module puts the strong-coupling content of the far input in one single-scale statement on slab kernels and
proves that it gives the far input with a mass in physical units.

## The single-scale statement

`PhysStrong ℓ₀ t₀` (`0 < ℓ₀`, `0 < t₀ < 1`): for every physical size `L ≥ 1` and every `p` with
`2^{p+1} ℓ₀ ≤ L`, eventually in `β`, `p ≤ kPhys L β + 2` and in every direction `s` the slab kernel of
lattice length `2^{kPhys L β + 2 − p}` on the cross-section of the physical side has cross ratio within
`t₀`. That slab has physical thickness in `(L/2^{p+1}, L/2^p]`, so at least `ℓ₀`: every slab of thickness
at least `ℓ₀` of a box of physical size `L` is a strict Birkhoff contraction by the fixed factor `t₀`, at
every lattice spacing. `ℓ₀` is the diffraction length; the clause is the statement that the theory seen
through a slab of that thickness is in the strong-coupling (rank-one up to `t₀`) region.

## What is proved

* `crossRatio_diag`: the cross ratio is invariant under a nonnegative diagonal rescaling
  `K(x, y) ↦ f(x) K(x, y) g(y)`; the boundary self-energies of the two faces drop out.
* `crossRatio_rankOne`: a rank-one kernel `f(x) c g(y)` has cross ratio `0` (the unit: at `β = 0` the slice
  kernel is constant).
* `crossRatio_of_diag_bounds`: a slab kernel `f(x) k(x, y) g(y)` with `e^{−ω} ≤ k ≤ 1` has cross ratio within
  `(1 − e^{−2ω})/(1 + e^{−2ω})`. The oscillation of `log k` after removing the face terms is the strong-coupling
  smallness parameter.
* `crossRatio_iter_mul`: `CrossRatio kT^{∗(i+1)} t₀ ⇒ CrossRatio kT^{∗(r+1)(i+1)} t₀^{r+1}`: stacking slabs
  multiplies the contraction factors (`ApertureGap.crossRatio_conv`).
* `cyc_double_of_crossRatio`: `CrossRatio kT^{∗n} t`, `0 ≤ t ≤ u ≤ 1/2` give
  `e^{−4u} cyc(n)² ≤ cyc(2n)`.
* `kernFar_of_physStrong`: `PhysStrong ℓ₀ t₀` gives `KernFar L (4 e^{−mL})` at every `L ≥ max(1, 2ℓ₀)` with
  `e^{−mL} ≤ 1/2`, where `m = log(1/t₀)/(4ℓ₀)` (`physMass`, positive by `physMass_pos`). The box of physical
  size `L` stacks `2^p > L/(4ℓ₀)` slabs of thickness at least `ℓ₀`, so the cross ratio is within
  `t₀^{2^p} ≤ e^{−mL}`. This is the `FixedDiffraction` inequality with `C = 4`, `d = 0` at every large `L`.
* `physDefect_of_physStrong`, `runSeed_of_physStrong`: `PhysStrong ℓ₀ t₀ ⇒` eventually `PhysDefect L (1/1000)`
  `⇒ WDeltaRun.RunSeed 2`, the `hW` input.

## Unit test (numerical, not formalised): 2D `SU(2)`

On the 2D cylinder the gauge projection leaves the slab kernel a function of the two face holonomy classes,
`k(a, b) = Σ_d ĉ_d^A χ_d(a) χ_d(b)` with `ĉ_d = I_d(β_std)/I_1(β_std)`, `A = Lℓ/a²` plaquettes, continuum
`ĉ_d^A → e^{−(d² − 1)Lℓ/8}` (`g = 1`). The worst slab of `PhysStrong` (thickness `ℓ₀`, side `L = 2ℓ₀`) has
cross ratio, at `β_std = 2, 8, …, 32768`: at `ℓ₀ = 2`, `0.275 … 0.382`, increasing to the continuum `0.382`; at
`ℓ₀ = 4`, `1.2·10⁻⁵ … 4.9·10⁻⁵` (continuum `8 e^{−3Lℓ/8}`); at `ℓ₀ = 1.5`, `≤ 0.928`. So `PhysStrong 2 0.382`
holds uniformly in `β`: the 2D theory is strongly coupled at the length where its string tension acts.
The test is degenerate in one respect: the 2D face carries one gauge-invariant variable.

## Scope of the statement (argued, not formalised)

* The cross ratio is a sup over the four face configurations, not an average. It cannot hold for a
  non-compact field: for a Gaussian slab kernel `exp(−a(x² + y²) + bxy)` the log cross ratio is
  `b(x − x')(y − y')`, unbounded, so no `t < 1` works. For compact links the face configurations are bounded
  and the statement is meaningful.
* For a cross-section of `A` independent cells each with cross ratio `t₁`, the log cross ratios add, so the
  product kernel has cross ratio `tanh(A artanh t₁)`, which tends to `1` with `A`. `PhysStrong` uniform in
  `β` therefore asks that the lattice-scale face data contribute a summable total to the log cross ratio,
  the number of physical cells `(L/ℓ₀)³` being fixed. That summability is the 4D content of the statement.
* Exact decimation does not reduce the cross-section. `GapSideExactDecimation.effIter_spec` keeps the
  partition functions of the symmetric 4-torus of side `2^k n` at every background, as the partition
  functions of a density on the side-`n` torus. The defect compares two tori (`n⁴` and `n³ × 2n`), and the
  effective density is one function of all coarse links, not a product of coarse slice kernels: the slice
  structure survives exactly only as `cyc(kT, n) = cyc(kT^{∗n/4}, 4)` with the slab kernel acting on the
  fine cross-section. A coarse slice kernel on a fixed number of block variables would need the integrated
  variables to drop out of the time chain, which they do not (the marginal of a Markov chain is not Markov).
* Strong-coupling Dobrushin arguments (cited, not in this tree) give uniqueness, spatial covariance decay
  and a volume-uniform global gap for Wilson at small bare coupling times a bounded local potential of
  small local norm. They act on the bare density; the side-`4` effective density
  is in that class only through the one-polymer representation, whose local norm is the number of links of
  the side-`4` torus times the sup of the effective log-density, so it gives nothing beyond the oscillation
  bound itself, and it bounds no doubling defect between two geometries.

DERIVED (module-wide): `4` the factor `e^{−4u} ≤ (1 − t)/(1 + t)` for `0 ≤ t ≤ u ≤ 1/2`
(`(1 − t)(1 + 4u) ≥ 1 + t`); `1/2` its range; `4ℓ₀` from `2^p > L/(4ℓ₀)` (`Nat.lt_pow_succ_log_self` at
`⌊L/(2ℓ₀)⌋₊`); `2` in `kPhys + 2` from `GapAttack.KernFar`; `1/1000`, `1/15000`, `15` as in
`ApertureGap.physDefect_of_fixedDiffraction`; `2` the rank of the slice kernel's group in `RectTransfer`.
-/

noncomputable section

namespace MassGap.StrongPhys

open MeasureTheory Real Filter Topology Set MassGap MassGap.KernelPower MassGap.CyclicKernel
  MassGap.PhysicalScaleSmall MassGap.ApertureNearAll MassGap.RectWilson MassGap.ApertureGap

/-! ## 1. Cross ratios of slab kernels -/

section Kernel

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

omit [MeasurableSpace X] in
/-- **The face terms drop out**: `CrossRatio k t ⇒ CrossRatio (f(x) k(x, y) g(y)) t` for `f, g ≥ 0`. -/
theorem crossRatio_diag {k : X → X → ℝ} {t : ℝ} (hk : CrossRatio k t) {f g : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) : CrossRatio (fun x y => f x * k x y * g y) t := by
  intro x x' y y'
  show |f x * k x y * g y * (f x' * k x' y' * g y') - f x * k x y' * g y' * (f x' * k x' y * g y)|
    ≤ t * (f x * k x y * g y * (f x' * k x' y' * g y') + f x * k x y' * g y' * (f x' * k x' y * g y))
  have hF : 0 ≤ f x * f x' * g y * g y' :=
    mul_nonneg (mul_nonneg (mul_nonneg (hf x) (hf x')) (hg y)) (hg y')
  have e1 : f x * k x y * g y * (f x' * k x' y' * g y') - f x * k x y' * g y' * (f x' * k x' y * g y)
      = (f x * f x' * g y * g y') * (k x y * k x' y' - k x y' * k x' y) := by ring
  have e2 : f x * k x y * g y * (f x' * k x' y' * g y') + f x * k x y' * g y' * (f x' * k x' y * g y)
      = (f x * f x' * g y * g y') * (k x y * k x' y' + k x y' * k x' y) := by ring
  rw [e1, e2, abs_mul, abs_of_nonneg hF]
  calc (f x * f x' * g y * g y') * |k x y * k x' y' - k x y' * k x' y|
      ≤ (f x * f x' * g y * g y') * (t * (k x y * k x' y' + k x y' * k x' y)) :=
        mul_le_mul_of_nonneg_left (hk x x' y y') hF
    _ = t * ((f x * f x' * g y * g y') * (k x y * k x' y' + k x y' * k x' y)) := by ring

omit [MeasurableSpace X] in
/-- **The unit**: a rank-one kernel `f(x) c g(y)` has cross ratio `0`. -/
theorem crossRatio_rankOne (f g : X → ℝ) (c : ℝ) : CrossRatio (fun x y => f x * c * g y) 0 := by
  intro x x' y y'
  show |f x * c * g y * (f x' * c * g y') - f x * c * g y' * (f x' * c * g y)|
    ≤ 0 * (f x * c * g y * (f x' * c * g y') + f x * c * g y' * (f x' * c * g y))
  have e : f x * c * g y * (f x' * c * g y') - f x * c * g y' * (f x' * c * g y) = 0 := by ring
  rw [e, abs_zero, zero_mul]

omit [MeasurableSpace X] in
/-- **The strong-coupling form of a slab kernel**: `f(x) k(x, y) g(y)` with `f, g ≥ 0` and
`e^{−ω} ≤ k ≤ 1` has cross ratio within `(1 − e^{−2ω})/(1 + e^{−2ω})`.

DERIVED: `1` the upper bound of `k`, normalised; `2` from `(e^{−ω})² = e^{−2ω}`. -/
theorem crossRatio_of_diag_bounds {k : X → X → ℝ} {ω : ℝ} (hlo : ∀ x y, Real.exp (-ω) ≤ k x y)
    (hhi : ∀ x y, k x y ≤ 1) {f g : X → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) :
    CrossRatio (fun x y => f x * k x y * g y)
      ((1 - Real.exp (-(2 * ω))) / (1 + Real.exp (-(2 * ω)))) := by
  have h := crossRatio_of_bounds (Real.exp_pos (-ω)) hlo hhi
  have e : Real.exp (-ω) ^ 2 = Real.exp (-(2 * ω)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [one_pow, e] at h
  exact crossRatio_diag h hf hg

/-- **Stacking slabs multiplies the contraction**: `CrossRatio a^{∗(i+1)} t₀` gives
`CrossRatio a^{∗(r+1)(i+1)} t₀^{r+1}`. -/
theorem crossRatio_iter_mul {a : X → X → ℝ} (ha : Bdd a) {i : ℕ} {t₀ : ℝ}
    (h : CrossRatio (iter μ a i) t₀) :
    ∀ r : ℕ, CrossRatio (iter μ a ((r + 1) * (i + 1) - 1)) (t₀ ^ (r + 1))
  | 0 => by simpa using h
  | r + 1 => by
    have ih := crossRatio_iter_mul ha h r
    have hP : 1 ≤ (r + 1) * (i + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have e : (r + 1 + 1) * (i + 1) - 1 = ((r + 1) * (i + 1) - 1) + i + 1 := by
      rw [show (r + 1 + 1) * (i + 1) = (r + 1) * (i + 1) + (i + 1) by ring]
      generalize (r + 1) * (i + 1) = P at hP ⊢
      omega
    rw [e, iter_add ha, pow_succ]
    exact crossRatio_conv (ha.iter _) (ha.iter i) ih h

/-- **The doubling of a contracting slab**: `CrossRatio a^{∗n} t` with `0 ≤ t ≤ u ≤ 1/2` gives
`e^{−4u} cyc(a, n)² ≤ cyc(a, 2n)`.

DERIVED: `4` and `1/2` as in the module note: `(1 − t)(1 + 4u) − (1 + t) = 4u − 2t − 4tu ≥ 0`. -/
theorem cyc_double_of_crossRatio {a : X → X → ℝ} (ha : Bdd a) {n : ℕ} (hn : 1 ≤ n) {t u : ℝ}
    (hc : CrossRatio (iter μ a (n - 1)) t) (ht0 : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ 1 / 2) :
    Real.exp (-(4 * u)) * cyc μ a n ^ 2 ≤ cyc μ a (2 * n) := by
  have h := cyc_double_ge_of (μ := μ) ha (n - 1) hc
  rw [Nat.sub_add_cancel hn] at h
  have hc0 : 0 ≤ cyc μ a n ^ 2 := sq_nonneg _
  have hE : Real.exp (-(4 * u)) * (1 + 4 * u) ≤ 1 := by
    have h1 := Real.add_one_le_exp (4 * u)
    have hp := Real.exp_pos (4 * u)
    rw [Real.exp_neg, inv_mul_le_iff₀ hp, mul_one]
    linarith
  have hE0 := Real.exp_pos (-(4 * u))
  have h1t : 0 ≤ 1 - t := by linarith
  have hkey : Real.exp (-(4 * u)) * (1 + t) ≤ 1 - t := by
    have h1 : 1 + t ≤ (1 - t) * (1 + 4 * u) := by
      nlinarith [mul_le_mul_of_nonneg_right (htu.trans hu) (ht0.trans htu)]
    calc Real.exp (-(4 * u)) * (1 + t) ≤ Real.exp (-(4 * u)) * ((1 - t) * (1 + 4 * u)) :=
          mul_le_mul_of_nonneg_left h1 hE0.le
      _ = (1 - t) * (Real.exp (-(4 * u)) * (1 + 4 * u)) := by ring
      _ ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left hE h1t
      _ = 1 - t := mul_one _
  have hpos : 0 < 1 + t := by linarith
  have hmul : (1 + t) * (Real.exp (-(4 * u)) * cyc μ a n ^ 2) ≤ (1 + t) * cyc μ a (2 * n) :=
    calc (1 + t) * (Real.exp (-(4 * u)) * cyc μ a n ^ 2)
        = (Real.exp (-(4 * u)) * (1 + t)) * cyc μ a n ^ 2 := by ring
      _ ≤ (1 - t) * cyc μ a n ^ 2 := mul_le_mul_of_nonneg_right hkey hc0
      _ ≤ (1 + t) * cyc μ a (2 * n) := h
  exact le_of_mul_le_mul_left hmul hpos

end Kernel

/-! ## 2. The single-scale statement and the far input -/

section Phys

/-- The slab kernel of lattice length `j` (`j ≥ 1`) on the cross-section of the torus of side `n` in
direction `s`: `kT^{∗j}`. -/
def slab (s : Fin 4) (n : ℕ) (β : ℝ) (j : ℕ) :
    (SpT s (tr (Ls n s) s) → SUN.SU 2) → (SpT s (tr (Ls n s) s) → SUN.SU 2) → ℝ :=
  iter (RectTransfer.hS s (tr (Ls n s) s) 2) (RectTransfer.kT s (tr (Ls n s) s) 2 β) (j - 1)

/-- **The effective theory at the diffraction length is strongly coupled**: every slab of physical
thickness at least `ℓ₀` of the box of physical size `L` is a Birkhoff contraction by `t₀ < 1`, at every
fine enough lattice spacing. The slab of lattice length `2^{kPhys L β + 2 − p}` has thickness in
`(L/2^{p+1}, L/2^p]`, at least `ℓ₀` when `2^{p+1} ℓ₀ ≤ L`.

DERIVED: `2` in `kPhys + 2` from `GapAttack.KernFar`; `1` the least `L` of `FixedDiffraction`. -/
def PhysStrong (ℓ₀ t₀ : ℝ) : Prop :=
  0 < ℓ₀ ∧ 0 < t₀ ∧ t₀ < 1 ∧
    ∀ L : ℝ, 1 ≤ L → ∀ p : ℕ, 2 ^ (p + 1) * ℓ₀ ≤ L → ∀ᶠ β in atTop,
      p ≤ kPhys L β + 2 ∧ ∀ s : Fin 4,
        CrossRatio (slab s (2 ^ (kPhys L β + 2)) β (2 ^ (kPhys L β + 2 - p))) t₀

/-- The mass of the contraction: `m = log(1/t₀)/(4ℓ₀)`.

DERIVED: `4` from `2^p > L/(4ℓ₀)`. -/
def physMass (ℓ₀ t₀ : ℝ) : ℝ := -Real.log t₀ / (4 * ℓ₀)

theorem physMass_pos {ℓ₀ t₀ : ℝ} (h : PhysStrong ℓ₀ t₀) : 0 < physMass ℓ₀ t₀ := by
  obtain ⟨hℓ, ht0, ht1, -⟩ := h
  have := Real.log_neg ht0 ht1
  unfold physMass
  exact div_pos (by linarith) (by linarith)

/-- **The contraction over the box**: `t₀^{2^p} ≤ e^{−mL}` when `L/(4ℓ₀) ≤ 2^p`. -/
theorem pow_le_exp_physMass {ℓ₀ t₀ L : ℝ} (ht0 : 0 < t₀) (ht1 : t₀ < 1) {p : ℕ}
    (hp : L / (4 * ℓ₀) ≤ 2 ^ p) : t₀ ^ (2 ^ p) ≤ Real.exp (-(physMass ℓ₀ t₀ * L)) := by
  have hlog := Real.log_neg ht0 ht1
  have e1 : t₀ ^ (2 ^ p) = Real.exp (((2 ^ p : ℕ) : ℝ) * Real.log t₀) := by
    rw [Real.exp_nat_mul, Real.exp_log ht0]
  have e2 : -(physMass ℓ₀ t₀ * L) = L / (4 * ℓ₀) * Real.log t₀ := by
    unfold physMass; ring
  rw [e1, e2, Real.exp_le_exp]
  push_cast
  exact mul_le_mul_of_nonpos_right hp hlog.le

/-- **The far input from the single-scale statement**: `PhysStrong ℓ₀ t₀` gives `KernFar L (4 e^{−mL})` at
every `L ≥ max(1, 2ℓ₀)` with `e^{−mL} ≤ 1/2`, `m = physMass ℓ₀ t₀`. -/
theorem kernFar_of_physStrong {ℓ₀ t₀ : ℝ} (h : PhysStrong ℓ₀ t₀) {L : ℝ} (hL1 : 1 ≤ L) (hL : 2 * ℓ₀ ≤ L)
    (hu : Real.exp (-(physMass ℓ₀ t₀ * L)) ≤ 1 / 2) :
    GapAttack.KernFar L (4 * Real.exp (-(physMass ℓ₀ t₀ * L))) := by
  obtain ⟨hℓ, ht0, ht1, hS⟩ := h
  have h2ℓ : 0 < 2 * ℓ₀ := by linarith
  have hx1 : 1 ≤ L / (2 * ℓ₀) := by rw [le_div_iff₀ h2ℓ]; linarith
  have hfl : ⌊L / (2 * ℓ₀)⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx1).ne'
  have hp1 : 2 ^ Nat.log 2 ⌊L / (2 * ℓ₀)⌋₊ ≤ ⌊L / (2 * ℓ₀)⌋₊ := Nat.pow_log_le_self 2 hfl
  have hp2 : ⌊L / (2 * ℓ₀)⌋₊ < 2 ^ (Nat.log 2 ⌊L / (2 * ℓ₀)⌋₊).succ :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  set p := Nat.log 2 ⌊L / (2 * ℓ₀)⌋₊ with hpdef
  have hpx : (2 : ℝ) ^ p ≤ L / (2 * ℓ₀) := by
    have h' : ((2 ^ p : ℕ) : ℝ) ≤ (⌊L / (2 * ℓ₀)⌋₊ : ℝ) := by exact_mod_cast hp1
    push_cast at h'
    exact h'.trans (Nat.floor_le (by linarith))
  have hxp : L / (2 * ℓ₀) < 2 * (2 : ℝ) ^ p := by
    have h' : (⌊L / (2 * ℓ₀)⌋₊ : ℝ) + 1 ≤ ((2 ^ p.succ : ℕ) : ℝ) := by exact_mod_cast hp2
    push_cast at h'
    have h'' := Nat.lt_floor_add_one (L / (2 * ℓ₀))
    rw [pow_succ] at h'
    linarith
  have hpL : (2 : ℝ) ^ (p + 1) * ℓ₀ ≤ L := by
    have h' := (le_div_iff₀ h2ℓ).1 hpx
    calc (2 : ℝ) ^ (p + 1) * ℓ₀ = 2 ^ p * (2 * ℓ₀) := by ring
      _ ≤ L := h'
  have hq : L / (4 * ℓ₀) ≤ 2 ^ p := by
    have e : L / (4 * ℓ₀) = L / (2 * ℓ₀) / 2 := by field_simp; ring
    rw [e, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have htu := pow_le_exp_physMass ht0 ht1 hq
  have htn : 0 ≤ t₀ ^ (2 ^ p) := pow_nonneg ht0.le _
  unfold GapAttack.KernFar
  filter_upwards [hS L hL1 p hpL, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 s
  obtain ⟨hpk, hcr⟩ := hβ
  have hc := crossRatio_iter_mul (μ := RectTransfer.hS s (tr (Ls (2 ^ (kPhys L β + 2)) s) s) 2)
    (RectTransfer.bdd_kT (μ := s) (T := tr (Ls (2 ^ (kPhys L β + 2)) s) s) (by norm_num) hβ0)
    (hcr s) (2 ^ p - 1)
  have e1 : (2 ^ p - 1 + 1) * (2 ^ (kPhys L β + 2 - p) - 1 + 1) - 1 = 2 ^ (kPhys L β + 2) - 1 := by
    rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.sub_add_cancel Nat.one_le_two_pow, ← pow_add,
      Nat.add_sub_cancel' hpk]
  rw [e1, Nat.sub_add_cancel Nat.one_le_two_pow] at hc
  exact cyc_double_of_crossRatio
    (RectTransfer.bdd_kT (μ := s) (T := tr (Ls (2 ^ (kPhys L β + 2)) s) s) (by norm_num) hβ0)
    Nat.one_le_two_pow hc htn htu hu

/-- **The single-scale statement gives the physical-side defect** at every large enough aperture.

DERIVED: `1/1000`, `1/15000`, `15` as in `ApertureGap.physDefect_of_fixedDiffraction`; `4` the factor of
`kernFar_of_physStrong`; `1/2` its range. -/
theorem physDefect_of_physStrong {ℓ₀ t₀ : ℝ} (h : PhysStrong ℓ₀ t₀) :
    ∀ᶠ L in atTop, ApertureBridge.PhysDefect L (1 / 1000) := by
  have hm := physMass_pos h
  filter_upwards [eventually_poly_exp_le hm 4 0 (ε := 1 / 15000) (by norm_num), eventually_ge_atTop 1,
    eventually_ge_atTop (2 * ℓ₀)] with L hs hL1 hL2
  rw [pow_zero, mul_one] at hs
  have he := Real.exp_pos (-(physMass ℓ₀ t₀ * L))
  have hu : Real.exp (-(physMass ℓ₀ t₀ * L)) ≤ 1 / 2 := by linarith
  have hk := kernFar_of_physStrong h hL1 hL2 hu
  have hk' : GapAttack.KernFar L (1 / 15000) := by
    unfold GapAttack.KernFar at hk ⊢
    filter_upwards [hk] with β hβ s
    refine le_trans ?_ (hβ s)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (sq_nonneg _)
  have := GapAttack.physDefect_of_kernFar hk'
  rwa [show (15 : ℝ) * (1 / 15000) = 1 / 1000 by norm_num] at this

/-- **The single-scale statement gives the run seed**, the `hW` input. -/
theorem runSeed_of_physStrong {ℓ₀ t₀ : ℝ} (h : PhysStrong ℓ₀ t₀) : WDeltaRun.RunSeed 2 := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (physDefect_of_physStrong h)
  exact ApertureBridge.runSeed_of_physDefect (lt_of_lt_of_le one_pos (le_max_right L₀ 1))
    (hL₀ _ (le_max_left _ _))

end Phys

end MassGap.StrongPhys

#print axioms MassGap.StrongPhys.crossRatio_diag
#print axioms MassGap.StrongPhys.crossRatio_rankOne
#print axioms MassGap.StrongPhys.crossRatio_of_diag_bounds
#print axioms MassGap.StrongPhys.crossRatio_iter_mul
#print axioms MassGap.StrongPhys.cyc_double_of_crossRatio
#print axioms MassGap.StrongPhys.physMass_pos
#print axioms MassGap.StrongPhys.pow_le_exp_physMass
#print axioms MassGap.StrongPhys.kernFar_of_physStrong
#print axioms MassGap.StrongPhys.physDefect_of_physStrong
#print axioms MassGap.StrongPhys.runSeed_of_physStrong
