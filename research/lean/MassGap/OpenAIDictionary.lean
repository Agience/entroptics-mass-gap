import Mathlib
import MassGap.GaugeWilson
import MassGap.ClayStatementG
import MassGap.DoublingSharp
import MassGap.TorusIdentify

/-!
# MassGap.OpenAIDictionary — the dictionary between this tree and the OpenAI Yang–Mills construction

The OpenAI submission `yang-mills-group/OpenAI-YM-20261028` (commit `3456e5e`, assessed by the group in
`yang-mills-group/YM` at `55ba9fc`) is built on Lean 4.32 and cannot be imported here (Lean 4.31). The
two objects this module needs from it are restated locally, each docstring citing the source line, and
the dictionary between them and our objects is proved.

## 1. The action

Their energy (`PublicWilson.lean:25`, `wilsonEnergy`) sums `1 − Re tr U_p / D` over sites and
*unordered* planes `μ < ν` (`Directions`, `PublicWilson.lean:13`). Our action
(`LatticeGauge.System.action` of `GaugeWilson.sysWilsonG`) sums `wilsonDensityG = 1 − Re tr ρ(U_p)/d`
over *ordered* pairs `(μ, ν)` (`WilsonHypercubic.Plaq`). The plaquette word is the same
(`PublicWilson.lean:20`, `plaquette`, against `WilsonHypercubic.bd`). Two facts finish the count:

* `wilsonHol_swap`: the plaquette `(ν, μ)` has the inverse holonomy of `(μ, ν)`, in every group;
* `wilsonHol_diag`: the plaquette `(μ, μ)` has holonomy `1`, in every group;

so with `wilsonDensityG_inv` and `wilsonDensityG_one`, `action_eq_two_mul_wilsonEnergy`:
`action U = 2 · wilsonEnergy U`. Hence `boltz_eq_exp_wilsonEnergy` (`e^{−β S} = e^{−2β E}`),
`wilsonLaw_two_mul` (their normalized law at `2β` is our Boltzmann density over product measure), and
`expect_eq_integral_wilsonLaw` (our Gibbs expectation at `β` is the integral against their law at
`2β`). In their units, `β_sub = 2 β_ours`.

The configuration type is ours, `Link d n → G` with `Link d n = Fin d × Site d n`; theirs is indexed
`Site l × Axis` with `Site l = Axis → ZMod l`, `Axis = Fin 4` (`PublicWilson.lean:11–12`,
`PublicTheory.lean:51`). At `d = 4` the two index types differ by the swap of the pair, and `ZMod l`
is `Fin l` at `l > 0`. Their `D = n + 1` is the size of the matrices of their group, which is `dim G`
for the defining representation.

## 2. The asymptotic-freedom coefficient

`afConstG_eq`: our `afConstG G = 12 dim 𝔤 / (π⁴ b₀²)` is `(2/b₀)² · 3 dim 𝔤/π⁴`, where
`3 dim 𝔤/π⁴` is their proved trace coefficient (`TraceBridge.lean:25`, `award_eq`;
`ChallengeSpec.lean:173`, `TraceTest.shortDistance`) and `b₀ = 11 h^∨/(48π²)` in both
(`GaugeRunning.b0G`; their `YM/Pert/Asymptotics/RawAxis.lean:13`).

`afCoefficientG_of_traceLaw`: a real kernel `S` with `r⁸ log²(1/r) S(r) → 3 dim 𝔤/π⁴` as `r → 0⁺`
gives `AFCoefficientG (constsG G)` for `(2/b₀)² S`; the two logarithm conventions agree because
`log(1/r)² = (log r)²`.

`afCoefficientG_of_shortDistance`: their law as stated — a complex two-point function `S`, the scalar
weight acting by `•`, the limit in `ℂ` at the real coefficient — gives `AFCoefficientG (constsG G)` for
the kernel `c² · Re S` whenever `c = ±2/b₀`. This is the field normalization `trC = c Θ`: the
two-point function of `c Θ` is `c²` times that of `Θ`, so the sign of the identification, which is not
fixed by either repository, drops out.

## 3. A uniform gap along a family of tori (Theorem 4.46)

`familyGap_of_seed`: for couplings `β m p` (spacing index `m`, volume index `p`) and base sides `n m`,
eventually even and at least `2`, the seed of `DoublingSharp.wilson_gap_sharp` at `(n m, β m p / 2)`
for all large `m` and all `p` gives that theorem's conclusion — a unit top eigenvector of the transfer
operator and contraction of its orthogonal complement by `1/2` over `n m` steps — on every torus
`ext (n m) (corner k)` (side `2^k · n m`), for all large `m`, all `p` and all `k`. The coupling is
halved because `expect_eq_integral_wilsonLaw` reads their law at `β` as ours at `β / 2`.
`sysR_ext_corner`: the rectangular system `RectWilson.sysR (ext n (corner k))` of that theorem is
`sysWilsonG (SU N) 4 (2^k · n)`, the system of section 1.
`physRate_le`: when `n m · a m ≤ ℓ`, the per-step rate `log 2 / n m` over spacing `a m` is at least
`log 2 / ℓ` in physical units.

## Scope

Nothing here identifies their limit theory, their selected phase or their field `Θ` with ours. The
action and law statements are exact identities on one finite periodic lattice at one coupling. The
asymptotic-freedom statements are theorems about functions `ℝ → ℝ` and `ℝ → ℂ`: they say which kernel
our clause reads off their law, and do not say that our `TwoPointKernelG` kernel is that kernel.
-/

namespace MassGap.OpenAIDictionary

open MeasureTheory Filter Topology
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonHypercubic MassGap.GaugeGroup
open MassGap.GaugeWilson

/-! ## 1. The action dictionary -/

/-- The unordered planes of `Fin d`: ordered pairs `(μ, ν)` with `μ < ν`. Restated from the OpenAI
submission, `PublicWilson.lean:13` (`Directions := {p : Axis × Axis // p.1 < p.2}`, there at
`Axis = Fin 4`), here at every `d`.

DERIVED: no numeral appears in the statement. -/
abbrev Directions (d : ℕ) : Type := {p : Fin d × Fin d // p.1 < p.2}

/-- A sum over ordered pairs of a function that is symmetric and vanishes on the diagonal is twice its
sum over unordered planes: `∑_{(a,b)} f (a, b) = 2 · ∑_{a<b} f (a, b)`. Each pair is below, on or above
the diagonal; the diagonal contributes `0`, and the swap `Equiv.prodComm` carries the pairs above onto
the pairs below.

DERIVED: `2` counts the two orientations `(a, b)` and `(b, a)` of one plane; `0` is the value on the
diagonal. -/
theorem sum_pairs_eq_two_mul {d : ℕ} (f : Fin d × Fin d → ℝ)
    (hsymm : ∀ a b, f (b, a) = f (a, b)) (hdiag : ∀ a, f (a, a) = 0) :
    ∑ p, f p = 2 * ∑ p : Directions d, f p.1 := by
  have hsplit : ∀ p : Fin d × Fin d,
      f p = (if p.1 < p.2 then f p else 0) + (if p.2 < p.1 then f p else 0) := by
    rintro ⟨a, b⟩
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  have hswap : ∑ p : Fin d × Fin d, (if p.2 < p.1 then f p else 0)
      = ∑ p : Fin d × Fin d, (if p.1 < p.2 then f p else 0) := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => ?_)
    obtain ⟨a, b⟩ := p
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hsymm a b]
  have hsub : ∑ p : Fin d × Fin d, (if p.1 < p.2 then f p else 0) = ∑ p : Directions d, f p.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p => by simp) f
  calc ∑ p, f p
      = ∑ p : Fin d × Fin d, ((if p.1 < p.2 then f p else 0) + (if p.2 < p.1 then f p else 0)) :=
        Finset.sum_congr rfl (fun p _ => hsplit p)
    _ = 2 * ∑ p : Directions d, f p.1 := by
        rw [Finset.sum_add_distrib, hswap, hsub]
        ring

section Action

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n]

/-- Reversing the orientation of a plaquette inverts its holonomy, in every group:
`hol ((ν, μ), x) = (hol ((μ, ν), x))⁻¹`. The word of `(ν, μ)` is
`U_ν(x) U_μ(x+ν̂) U_ν(x+μ̂)⁻¹ U_μ(x)⁻¹`, which is the inverse of
`U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹` term by term. No condition on `n` or `d` is needed.

DERIVED: no numeral appears in the statement; `⁻¹` is the group inverse. -/
theorem wilsonHol_swap {H : Type} [Group H] (μ ν : Fin d) (x : Site d n) (U : Link d n → H) :
    wilsonHol (bd (d := d) (n := n)) ((ν, μ), x) U
      = (wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U)⁻¹ := by
  simp [wilsonHol, bd, mul_inv_rev, mul_assoc]

/-- A degenerate plaquette `((μ, μ), x)` has holonomy `1`, in every group: its word traverses
`(μ, x)` and `(μ, shift μ x)` once forwards and once inverted. This is
`WilsonHypercubic.bd_diag_hol_one` with the group `SU 2` replaced by an arbitrary group, and
`PairCount.wilsonHol_diag` with the dimension `4` replaced by an arbitrary `d`.

DERIVED: `1` is the group identity. -/
theorem wilsonHol_diag {H : Type} [Group H] (μ : Fin d) (x : Site d n) (U : Link d n → H) :
    wilsonHol (bd (d := d) (n := n)) ((μ, μ), x) U = 1 := by
  simp [wilsonHol, bd]

/-- The two orientations of a plane carry the same Wilson density:
`wilsonDensityG (hol ((ν, μ), x)) = wilsonDensityG (hol ((μ, ν), x))`, by `wilsonHol_swap` and
`wilsonDensityG_inv` (`Re tr ρ(g⁻¹) = Re tr ρ(g)` for a unitary representation).

DERIVED: no numeral appears in the statement. -/
theorem density_swap (μ ν : Fin d) (x : Site d n) (U : Link d n → G) :
    wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) ((ν, μ), x) U)
      = wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U) := by
  rw [wilsonHol_swap, wilsonDensityG_inv]

/-- A degenerate plaquette carries Wilson density `0`, by `wilsonHol_diag` and `wilsonDensityG_one`.

DERIVED: `0` is the density at the identity holonomy. -/
theorem density_diag (μ : Fin d) (x : Site d n) (U : Link d n → G) :
    wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) ((μ, μ), x) U) = 0 := by
  rw [wilsonHol_diag, wilsonDensityG_one]

/-- The OpenAI Wilson energy, restated on our periodic lattice: the Wilson density
`1 − Re tr ρ(U_p)/d` summed over sites and unordered planes `μ < ν`. Their definition is
`PublicWilson.lean:25` (`wilsonEnergy U = ∑ p : Site l × Directions, (1 − Re tr (plaquette U p.1 i j)
/ (n+1))`), with the plaquette word of `PublicWilson.lean:20`, which is our `WilsonHypercubic.bd`.
Their trace is that of the matrix group itself, so their `n + 1` is our `dim G` for the defining
representation.

DERIVED: no numeral appears in the statement. -/
noncomputable def wilsonEnergy (U : Link d n → G) : ℝ :=
  ∑ p : Site d n × Directions d, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (p.2.1, p.1) U)

/-- **The action dictionary**: our Wilson action, summed over ordered plaquettes, is twice the
OpenAI energy, summed over unordered planes: `(sysWilsonG G d n).action U = 2 · wilsonEnergy U`.
The ordered sum splits by `sum_pairs_eq_two_mul`, using `density_swap` and `density_diag` at each
site.

DERIVED: `2` counts the two orientations of one plane. -/
theorem action_eq_two_mul_wilsonEnergy (U : Link d n → G) :
    (sysWilsonG G d n).action U = 2 * wilsonEnergy U := by
  have hpt : ∀ x : Site d n,
      ∑ q : Fin d × Fin d, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (q, x) U)
        = 2 * ∑ p : Directions d, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (p.1, x) U) :=
    fun x => sum_pairs_eq_two_mul (fun q => wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (q, x) U))
      (fun a b => density_swap a b x U) (fun a => density_diag a x U)
  show ∑ q : Plaq d n, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U) = 2 * wilsonEnergy U
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_congr rfl (fun x _ => hpt x),
    ← Finset.mul_sum]
  unfold wilsonEnergy
  rw [Fintype.sum_prod_type]

/-- **The Boltzmann-weight dictionary**: our weight at coupling `β` is the OpenAI weight at `2β`,
`(sysWilsonG G d n).boltz β U = exp (−(2β) · wilsonEnergy U)`.

DERIVED: `2` is the factor of `action_eq_two_mul_wilsonEnergy`. -/
theorem boltz_eq_exp_wilsonEnergy (β : ℝ) (U : Link d n → G) :
    (sysWilsonG G d n).boltz β U = Real.exp (-(2 * β) * wilsonEnergy U) := by
  unfold System.boltz
  rw [action_eq_two_mul_wilsonEnergy]
  congr 1
  ring

/-- The OpenAI Wilson law, restated on our periodic lattice: product measure `μ` over links with
density `exp (−β E) / ∫ exp (−β E)`, where `E = wilsonEnergy`. Their definition is
`PublicWilson.lean:29` (`wilsonLaw g l β haar`), there with `μ` their probability Haar measure; here
`μ` is any measure on `G`.

DERIVED: no numeral appears in the statement. -/
noncomputable def wilsonLaw (β : ℝ) (μ : Measure G) : Measure (Link d n → G) :=
  (Measure.pi fun _ : Link d n => μ).withDensity fun U =>
    ENNReal.ofReal (Real.exp (-β * wilsonEnergy U) /
      ∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Link d n => μ))

/-- **The law dictionary**: the OpenAI law at coupling `2β` is our product measure with the
normalized Boltzmann density at `β`, `wilsonLaw (2β) μ = (vol μ).withDensity (boltz β / partition β)`,
with `vol μ` written out as the product measure `Measure.pi` on `Link d n → G`.
Both the density and its normalizer are rewritten by `boltz_eq_exp_wilsonEnergy`.

DERIVED: `2` is the factor of `action_eq_two_mul_wilsonEnergy`. -/
theorem wilsonLaw_two_mul (β : ℝ) (μ : Measure G) :
    wilsonLaw (d := d) (n := n) (2 * β) μ
      = (Measure.pi fun _ : Link d n => μ).withDensity fun U =>
          ENNReal.ofReal ((sysWilsonG G d n).boltz β U / (sysWilsonG G d n).partition μ β) := by
  unfold wilsonLaw System.partition
  simp only [boltz_eq_exp_wilsonEnergy]
  rfl

/-- **The expectation dictionary**: our Gibbs expectation at coupling `β` is the integral against the
OpenAI law at `2β`, for every real observable `O` and every measure `μ` on `G`:
`(sysWilsonG G d n).expect μ β O = ∫ O ∂(wilsonLaw (2β) μ)`.

The density `boltz β / partition β` is finite and nonnegative, so integrating against the
`withDensity` measure is integrating `density · O` against `vol μ`
(`integral_withDensity_eq_integral_toReal_smul`), and the constant `partition β` comes out of the
integral (`integral_div`). No integrability of `O` and no nonvanishing of `partition` is used: where
the partition function is `0` both sides are `0`.

DERIVED: `2` is the factor of `action_eq_two_mul_wilsonEnergy`. -/
theorem expect_eq_integral_wilsonLaw (β : ℝ) (μ : Measure G) (O : (sysWilsonG G d n).Config → ℝ) :
    (sysWilsonG G d n).expect μ β O = ∫ U, O U ∂(wilsonLaw (d := d) (n := n) (2 * β) μ) := by
  rw [wilsonLaw_two_mul]
  have hZ : 0 ≤ (sysWilsonG G d n).partition μ β :=
    integral_nonneg fun U => (wilsonSystemG_boltz_pos (bd (d := d) (n := n)) β U).le
  have hmeas : Measurable fun U : Link d n → G =>
      ENNReal.ofReal ((sysWilsonG G d n).boltz β U / (sysWilsonG G d n).partition μ β) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_wilsonSystemG_boltz (bd (d := d) (n := n)) β).div_const _)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  show (∫ U, O U * (sysWilsonG G d n).boltz β U ∂(Measure.pi fun _ : Link d n => μ))
      / (sysWilsonG G d n).partition μ β = _
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  have hnn : 0 ≤ (sysWilsonG G d n).boltz β U / (sysWilsonG G d n).partition μ β :=
    div_nonneg (wilsonSystemG_boltz_pos (bd (d := d) (n := n)) β U).le hZ
  rw [smul_eq_mul, ENNReal.toReal_ofReal hnn]
  ring

end Action

/-! ## 2. The asymptotic-freedom dictionary -/

section AF

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G]

/-- **The coefficient dictionary**: our asymptotic-freedom coefficient is `(2/b₀)²` times the OpenAI
trace coefficient, `afConstG G = (2/b₀)² · (3 dim 𝔤/π⁴)`. Their coefficient `3 dim 𝔤/π⁴` is
`TraceBridge.lean:25` (`award_eq`) and `ChallengeSpec.lean:173` (`TraceTest.shortDistance`); `b₀` is
`GaugeRunning.b0G G = 11 h^∨/(48π²)`, their `YM/Pert/Asymptotics/RawAxis.lean:13`.

DERIVED: `3` is the OpenAI trace coefficient's numerator (`TraceBridge.lean:25`); `2` is the field
normalization `trC = (2/b₀) Θ` and the square; `4` the power of `π`. -/
theorem afConstG_eq :
    ClayStatementG.afConstG G
      = (2 / GaugeRunning.b0G G) ^ 2 * (3 * (GaugeSimple.lieDim (G := G) : ℝ) / Real.pi ^ 4) := by
  have hb : GaugeRunning.b0G G ≠ 0 := (GaugeRunning.b0G_pos (G := G)).ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold ClayStatementG.afConstG
  field_simp
  ring

/-- **The OpenAI trace law read as our clause, for a real kernel**: if `S : ℝ → ℝ` satisfies their
short-distance law `r⁸ log²(1/r) S(r) → 3 dim 𝔤/π⁴` as `r → 0⁺` (`ChallengeSpec.lean:173`), then the
kernel `(2/b₀)² S` satisfies `AFCoefficientG (constsG G)`, our `r⁸ G(r) (log r)² → afConstG G`. The
logarithms agree because `log(1/r) = −log r` (`Real.log_inv`), and the constants by `afConstG_eq`.

DERIVED: `8` is the scaling power of the two-point function of a dimension-`4` field, as in
`AFCoefficientG`; `3` is the OpenAI trace coefficient's numerator; `2` the field normalization and the
square of the logarithm; `4` the power of `π`; `0` the point approached. -/
theorem afCoefficientG_of_traceLaw {S : ℝ → ℝ}
    (hS : Tendsto (fun r => r ^ 8 * Real.log r⁻¹ ^ 2 * S r) (𝓝[>] (0 : ℝ))
      (𝓝 (3 * (GaugeSimple.lieDim (G := G) : ℝ) / Real.pi ^ 4))) :
    ClayStatementG.AFCoefficientG (ClayStatementG.constsG G)
      (fun r => (2 / GaugeRunning.b0G G) ^ 2 * S r) := by
  unfold ClayStatementG.AFCoefficientG
  have h := hS.const_mul ((2 / GaugeRunning.b0G G) ^ 2)
  rw [← afConstG_eq] at h
  show Tendsto _ _ (𝓝 (ClayStatementG.afConstG G))
  refine h.congr fun r => ?_
  dsimp only
  rw [Real.log_inv]
  ring

/-- **The OpenAI short-distance law, in its own form, read as our clause**: let `S : ℝ → ℂ` satisfy
`(r⁸ log²(1/r)) • S(r) → (3 dim 𝔤/π⁴ : ℂ)` as `r → 0⁺`, the form of `TraceTest.shortDistance`
(`ChallengeSpec.lean:173`, with `S = T.traceTwo`, the selected-phase two-point function of the
centred trace `Θ` at time separation `r`). Under the field normalization `trC = c Θ` with
`c = ±2/b₀`, the trace kernel `c² · Re S` satisfies `AFCoefficientG (constsG G)`.

The real part of the limit is the real coefficient, the weight is real so it commutes with `Re`
(`Complex.smul_re`), and `c² = (2/b₀)²` for either sign; then `afCoefficientG_of_traceLaw`. The sign
of the identification is fixed by neither repository and does not enter.

DERIVED: `8` is the scaling power of the two-point function of a dimension-`4` field; `3` is the
OpenAI trace coefficient's numerator; `2` the field normalization and the squares; `4` the power of
`π`; `0` the point approached. -/
theorem afCoefficientG_of_shortDistance {S : ℝ → ℂ} {c : ℝ}
    (hc : c = 2 / GaugeRunning.b0G G ∨ c = -(2 / GaugeRunning.b0G G))
    (hS : Tendsto (fun r : ℝ => (r ^ 8 * Real.log r⁻¹ ^ 2) • S r) (𝓝[>] (0 : ℝ))
      (𝓝 ((3 * (GaugeSimple.lieDim (G := G) : ℝ) / Real.pi ^ 4 : ℝ) : ℂ))) :
    ClayStatementG.AFCoefficientG (ClayStatementG.constsG G) (fun r => c ^ 2 * (S r).re) := by
  have hc2 : c ^ 2 = (2 / GaugeRunning.b0G G) ^ 2 := by
    rcases hc with rfl | rfl <;> ring
  have hre : Tendsto (fun r => r ^ 8 * Real.log r⁻¹ ^ 2 * (S r).re) (𝓝[>] (0 : ℝ))
      (𝓝 (3 * (GaugeSimple.lieDim (G := G) : ℝ) / Real.pi ^ 4)) := by
    have h := (Complex.continuous_re.tendsto _).comp hS
    rw [Complex.ofReal_re] at h
    refine h.congr fun r => ?_
    simp only [Function.comp_apply, Complex.smul_re, smul_eq_mul]
  simpa only [hc2] using afCoefficientG_of_traceLaw G hre

end AF

end MassGap.OpenAIDictionary

/-! ## 3. A uniform gap along a family of tori -/

namespace MassGap.OpenAIDictionary

open Filter MeasureTheory
open Real MassGap.DoublingRecursion MassGap.DoublingPower MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.DoublingWilson MassGap.SlabKernelOperator

/-- **A uniform gap along a family of tori from the seed** (Theorem 4.46 of the paper, at `SU(N)`).

Let `β m p` be couplings indexed by a spacing index `m` and a volume index `p`, in the normalization
of the OpenAI construction, and `n m` base sides. Suppose `β m p ≥ 0`, and that for all large `m` the
side `n m` is even and at least `2` and, for every `p`, the seed of `DoublingSharp.wilson_gap_sharp`
holds at `(n m, β m p / 2)`: `16 log Z(n m) − log Z(2 n m) ≤ 1/1000`. Then for all large `m`, all `p`
and all `k`, the conclusion of `wilson_gap_sharp` holds on the torus `ext (n m) (corner k)` (side
`2^k · n m`) at coupling `β m p / 2`: the transfer operator on `L²` of the slice has a unit
eigenvector `ψ` whose eigenvalue has modulus the operator norm, and its `n m`-th power contracts the
orthogonal complement of `ψ` by `1/2` relative to `‖T‖^(n m)`.

The proof is `wilson_gap_sharp` at each `(m, p, k)`; the content added is only the quantifier order —
one eventual threshold in `m`, uniform in `p` and `k`. The coupling is `β m p / 2` because our action
sums ordered plaquettes: `expect_eq_integral_wilsonLaw` reads the OpenAI law at `β` as our Gibbs
expectation at `β / 2`. The reading on their configuration type goes through that theorem and the
measure-preserving equivalence `OpenAIConfig.measurePreserving_wilsonLaw`; with `physRate_le`, a contraction by `1/2` over `n m`
steps of spacing `a m` with `n m · a m ≤ ℓ` is a gap of at least `log 2 / ℓ` in physical units.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp` (`DoublingSharp`); `2` is the halving of
the coupling (`action_eq_two_mul_wilsonEnergy`), the doubled side, the `L²` exponent and the
contraction `1/2`; `0` is the sign of the coupling and the time direction of the slice; `1` the unit
norm and the kernel exponent. -/
theorem familyGap_of_seed {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ)
    (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      16 * Real.log (ZR (fun _ => n m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) N (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in atTop, ∀ p k,
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ f : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) N), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N)) ^ n m) f‖
          ≤ 1 / 2 * ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
            (continuous_kT (β m p / 2)).measurable zero_le_one
            (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
            (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N)‖ ^ n m
            * ‖f‖ := by
  filter_upwards [hfam] with m hm p k
  obtain ⟨hn, he, h0⟩ := hm
  exact DoublingSharp.wilson_gap_sharp hN (div_nonneg (hβ m p) zero_le_two) hn he (h0 p) k

/-- **The torus of `familyGap_of_seed` is the system of the action dictionary**: the rectangular
Wilson system `RectWilson.sysR` at the extents `ext n (corner k)` (side `2^k · n` in all four
directions), on which `DoublingSharp.wilson_gap_sharp` and `familyGap_of_seed` are stated, is
`GaugeWilson.sysWilsonG (SU N) 4 (2^k · n)`, the system of `action_eq_two_mul_wilsonEnergy` and
`expect_eq_integral_wilsonLaw`. It composes `TorusIdentify.sysR_cubic` (`sysR` at constant extents is
`WilsonHypercubic.sysWilson`) with `GaugeWilson.sysWilsonG_SU` (`sysWilsonG` at `SU N` is
`sysWilson`). So `ZR (ext n (corner k)) N β` is the partition function of that system, and the law
whose transfer operator `wilson_gap_sharp` reads is the OpenAI law at `2β` by Theorem 4.44.

DERIVED: `4` is the spacetime dimension; `2` the dyadic doubling of the side. -/
theorem sysR_ext_corner (N : ℕ) [NeZero N] (n k : ℕ) [NeZero (2 ^ k * n)] :
    sysR (ext n (corner k)) N = GaugeWilson.sysWilsonG (MassGap.SUN.SU N) 4 (2 ^ k * n) := by
  have key : ∀ (L : ℕ) [NeZero L],
      sysR (fun _ : Fin 4 => L) N = GaugeWilson.sysWilsonG (MassGap.SUN.SU N) 4 L := by
    intro L _
    obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
    rw [GaugeWilson.sysWilsonG_SU]
    exact TorusIdentify.sysR_cubic N M
  exact key (2 ^ k * n)

/-- **The physical-units rate**: a contraction by `1/2` over `n` steps of spacing `a` is a rate
`log 2 / (n a)` per unit physical length, and when the physical extent of those steps is at most `ℓ`,
that rate is at least `log 2 / ℓ`: `n · a ≤ ℓ`, `a > 0`, `n ≥ 1` give
`log 2 / ℓ ≤ log 2 / (n · a)`. `ℓ > 0` is not a hypothesis: it follows from the other three. Used in the reading of `familyGap_of_seed` with `n = n m`, `a = a m`.

DERIVED: `2` is the contraction factor `1/2` of `wilson_gap_sharp`, whose logarithm is the rate;
`0` the signs; `1` the least number of steps. -/
theorem physRate_le {n : ℕ} {a ℓ : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (hle : (n : ℝ) * a ≤ ℓ) :
    Real.log 2 / ℓ ≤ Real.log 2 / ((n : ℝ) * a) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (mul_pos hn' ha) hle

end MassGap.OpenAIDictionary
