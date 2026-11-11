import Mathlib
import MassGap.OpenAIDictionary
import MassGap.CyclicKernel
import MassGap.KernelGap
import MassGap.FluxSectorBound
import MassGap.HiddenChain

/-!
# MassGap.OpenAIBridgeCluster — from the transfer gap of Theorem 4.46 to decay of torus correlations

Theorem 4.46 (`OpenAIDictionary.familyGap_of_seed`, from `DoublingSharp.wilson_gap_sharp`) gives, on
the cubic `SU(N)` torus of side `2^k · n` at every even seed side `n ≥ 2`, a unit top eigenvector `ψ`
of the slice transfer operator `K` with `|c| = ‖K‖` and `‖Kⁿ f‖ ≤ ½ ‖K‖ⁿ ‖f‖` for `f ⊥ ψ`. This
module turns that into decay at every time separation, not only at multiples of `n`, and into a bound
on the connected two-slice correlation of the torus written as a trace ratio.

## 1. The operator core

On a real inner product space, for a symmetric `T` with `T ψ = c ψ` and the gap over `n` steps:

* `pow_orth_decay` — `‖T^t f‖ ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖f‖` for `f ⊥ ψ` and every `t`;
* `pow_sub_vac_le` — `‖T^t f − ⟨f,ψ⟩ c^t ψ‖ ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖f‖` for every `f`, with `‖ψ‖ = 1`;
* `inner_pow_sub_le` — the vacuum-sector two-point function:
  `|⟨u, T^t w⟩ − c^t ⟨u,ψ⟩⟨w,ψ⟩| ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖u‖ ‖w‖`;
* `inner_pow_div_sub_le`, `half_pow_div_le_exp` — normalized by `c^t` (`|c| = ‖T‖`):
  `|⟨u, T^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ (1/2)^⌊t/n⌋ ‖u‖ ‖w‖ ≤ 2 e^{−(log 2/n) t} ‖u‖ ‖w‖`.

`wilson_decay_sharp` is `pow_sub_vac_le` on the Wilson torus of `wilson_gap_sharp`.
`wilson_cluster_uniform` is the normalized two-point bound there, with constant `2` and rate
`log 2/n` independent of the torus size, and `familyCluster_of_seed` is it along the family of
Theorem 4.46 in physical units: `2 e^{−(log 2/ℓ) τ} ‖u‖ ‖w‖` at separation `τ = t a_m`, uniform in the
spacing, the volume and the dyadic depth. This is the clustering of the transfer state of each torus
(infinite extent in the transfer direction, finite slice).

## 2. The trace ratio

For a bounded measurable symmetric kernel `k` on a probability space, with `k^{∗(m+1)} = iter k m`:

* `trPow k m = ∫ k^{∗(m+1)}(x,x)` is `Tr K^{m+1}`, the cyclic integral `CyclicKernel.cyc` of `m+1`
  copies (`trPow_eq_cyc`); on the Wilson torus it is the partition function (`ZR_eq_trPow`);
* `trIns k a m = ∫ a(x) k^{∗(m+1)}(x,x)` is `Tr(A K^{m+1})`;
* `trPair k a b p q = ∫∫ a(x) k^{∗(p+1)}(x,y) b(y) k^{∗(q+1)}(y,x)` is `Tr(A K^{p+1} B K^{q+1})`;
* `connTorus k a b p q = trPair/trPow − (trIns a/trPow)(trIns b/trPow)`, the connected correlation
  of the multiplication operators `A`, `B` at time separation `t = p+1` on the torus of time extent
  `L = p+q+2`.

`connTorus_le`: with `σ_j = excited k c φ j = hs(r^{∗j})/|c|^{2j}`, `r = k − c φ⊗φ`, and `L` even,

    |connTorus| ≤ A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋ + (σ_t + σ_{L−t})/2 + 4 σ_{L/2}).

The first two terms are the gap: the vacuum-to-excited cross terms of the trace, each a matrix element
of `K^t − c^t P` or `K^{L−t} − c^{L−t} P`, bounded by `pow_sub_vac_le`. The last two are the
excited–excited wrap-around term and the excited part of the partition function. The gap also
bounds them: `hs_iter_rem_le` gives `hs(r^{∗(m+1)}) ≤ ((1/2)^⌊m/n⌋ |c|^m)² hs(r)`, hence
`σ_{j+1} ≤ (1/2)^⌊j/n⌋ σ_1` (`excited_succ_le`), and `connTorus_decay` is the bound in the form

    |connTorus| ≤ A B (1 + 9 σ_1) ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋),   n ≥ 1,

with `σ_1 = hs(k − c φ⊗φ)/c²`, finite on every torus. `wilson_connTorus_le` and
`wilson_connTorus_decay` are the two statements on the Wilson torus of side `2^k · n`, at every even
`n ≥ 2` and every `k`, with the gap of `wilson_gap_sharp`.

## Scope

The insertions are multiplication operators on `L²` of one slice's spatial links. Identifying
`trPair` with the Wilson expectation of a product of two slab observables at time separation `t` is
not proved here: it is the insertion form of `RectTransfer.ZR_eq_cyc`, which this module proves only
without insertions (`ZR_eq_trPow`). The constant `1 + 9 σ_1` of the periodic trace ratio is finite on
each torus and is not claimed uniform in the spatial volume: the wrap-around term
`Tr(R^{L−t} A R^t B)` is bounded here by Hilbert–Schmidt norms, and a bound by `Tr |R|^L` alone, which
the dyadic excited weight controls, needs the Schatten–Hölder inequality, not formalized here. The
uniform statements are those of the transfer state (`wilson_cluster_uniform`,
`familyCluster_of_seed`).
-/

namespace MassGap.OpenAIBridgeCluster

open MeasureTheory Real
open MassGap.KernelPower MassGap.SlabKernelOperator

/-! ## 1. The operator core -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The gap iterated over `q` blocks of `n` steps: for a symmetric `T` with `T ψ = c ψ` and
`‖Tⁿ f‖ ≤ ½ ‖T‖ⁿ ‖f‖` on `ψ⊥`, `‖T^(n q) f‖ ≤ (1/2)^q ‖T‖^(n q) ‖f‖` on `ψ⊥`. Each block maps `ψ⊥`
into itself (`KernelGap.orth_pow`), so the gap applies again.

DERIVED: `1/2` is the contraction of the gap hypothesis (`wilson_gap_sharp`); `0` is the value of
the inner product on the vacuum complement. -/
theorem pow_mul_orth_le {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    {ψ : E} {c : ℝ} (hψ : T ψ = c • ψ) {n : ℕ}
    (hgap : ∀ f : E, inner ℝ f ψ = 0 → ‖(T ^ n) f‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖f‖) :
    ∀ (q : ℕ) (f : E), inner ℝ f ψ = 0 → ‖(T ^ (n * q)) f‖ ≤ (1 / 2) ^ q * ‖T‖ ^ (n * q) * ‖f‖
  | 0, f, _ => by simp
  | q + 1, f, hf => by
    have h1 : T ^ (n * (q + 1)) = T ^ n * T ^ (n * q) := by
      rw [← pow_add]; congr 1; ring
    rw [h1, ContinuousLinearMap.mul_apply]
    have hq := pow_mul_orth_le hT hψ hgap q f hf
    have horth := KernelGap.orth_pow hT hψ (n * q) hf
    calc ‖(T ^ n) ((T ^ (n * q)) f)‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖(T ^ (n * q)) f‖ := hgap _ horth
      _ ≤ 1 / 2 * ‖T‖ ^ n * ((1 / 2) ^ q * ‖T‖ ^ (n * q) * ‖f‖) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (1 / 2) ^ (q + 1) * ‖T‖ ^ (n * (q + 1)) * ‖f‖ := by
          rw [mul_add, mul_one, pow_add, pow_succ]; ring

/-- **Decay of the vacuum complement at every time**: for a symmetric `T` with `T ψ = c ψ` and the
gap `‖Tⁿ f‖ ≤ ½ ‖T‖ⁿ ‖f‖` on `ψ⊥`, every `f ⊥ ψ` and every `t`,
`‖T^t f‖ ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖f‖`. Write `t = n ⌊t/n⌋ + (t mod n)`: the `⌊t/n⌋` full blocks contract
by `pow_mul_orth_le`, and the remaining `t mod n` steps cost at most `‖T‖` each
(`KernelGap.norm_pow_apply_le`). No condition on `n` is needed: at `n = 0`, `⌊t/0⌋ = 0`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `0` is the value of the inner product on
the vacuum complement. -/
theorem pow_orth_decay {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    {ψ : E} {c : ℝ} (hψ : T ψ = c • ψ) {n : ℕ}
    (hgap : ∀ f : E, inner ℝ f ψ = 0 → ‖(T ^ n) f‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖f‖)
    (t : ℕ) {f : E} (hf : inner ℝ f ψ = 0) :
    ‖(T ^ t) f‖ ≤ (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖f‖ := by
  have ht : t % n + n * (t / n) = t := Nat.mod_add_div t n
  have hsplit : (T ^ t) f = (T ^ (t % n)) ((T ^ (n * (t / n))) f) := by
    rw [← ContinuousLinearMap.mul_apply, ← pow_add, ht]
  have hpow : ‖T‖ ^ t = ‖T‖ ^ (t % n) * ‖T‖ ^ (n * (t / n)) := by
    rw [← pow_add, ht]
  rw [hsplit, hpow]
  calc ‖(T ^ (t % n)) ((T ^ (n * (t / n))) f)‖ ≤ ‖T‖ ^ (t % n) * ‖(T ^ (n * (t / n))) f‖ :=
        KernelGap.norm_pow_apply_le T _ _
    _ ≤ ‖T‖ ^ (t % n) * ((1 / 2) ^ (t / n) * ‖T‖ ^ (n * (t / n)) * ‖f‖) :=
        mul_le_mul_of_nonneg_left (pow_mul_orth_le hT hψ hgap _ f hf) (by positivity)
    _ = (1 / 2) ^ (t / n) * (‖T‖ ^ (t % n) * ‖T‖ ^ (n * (t / n))) * ‖f‖ := by ring

/-- **The vacuum-subtracted power at every time**: with `‖ψ‖ = 1`, for every `f` and every `t`,
`‖T^t f − (⟨f,ψ⟩ c^t) ψ‖ ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖f‖`. The part `g = f − ⟨f,ψ⟩ψ` is orthogonal to `ψ`,
`T^t f − ⟨f,ψ⟩ c^t ψ = T^t g`, and `‖g‖ ≤ ‖f‖` by Pythagoras; then `pow_orth_decay`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the unit norm of `ψ`; `0` the value of
the inner product on the vacuum complement. -/
theorem pow_sub_vac_le {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    {ψ : E} {c : ℝ} (hψ : T ψ = c • ψ) {n : ℕ}
    (hgap : ∀ f : E, inner ℝ f ψ = 0 → ‖(T ^ n) f‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖f‖)
    (hψ1 : ‖ψ‖ = 1) (t : ℕ) (f : E) :
    ‖(T ^ t) f - (inner ℝ f ψ * c ^ t) • ψ‖ ≤ (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖f‖ := by
  have hg : inner ℝ (f - inner ℝ f ψ • ψ) ψ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hψ1]; ring
  have hTψ : (T ^ t) ψ = c ^ t • ψ := by
    induction t with
    | zero => simp
    | succ p ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hψ, smul_smul,
        pow_succ]
  have heq : (T ^ t) f - (inner ℝ f ψ * c ^ t) • ψ = (T ^ t) (f - inner ℝ f ψ • ψ) := by
    rw [map_sub, map_smul, hTψ, smul_smul]
  have hnorm : ‖f - inner ℝ f ψ • ψ‖ ≤ ‖f‖ := by
    have hperp : inner ℝ (f - inner ℝ f ψ • ψ) (inner ℝ f ψ • ψ) = 0 := by
      rw [real_inner_smul_right, hg, mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real hperp
    rw [sub_add_cancel] at hpy
    nlinarith [norm_nonneg (f - inner ℝ f ψ • ψ), norm_nonneg f,
      mul_self_nonneg ‖inner ℝ f ψ • ψ‖]
  rw [heq]
  calc ‖(T ^ t) (f - inner ℝ f ψ • ψ)‖
      ≤ (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖f - inner ℝ f ψ • ψ‖ := pow_orth_decay hT hψ hgap t hg
    _ ≤ (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖f‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)

/-- **The vacuum-sector two-point function decays at every time**: with `‖ψ‖ = 1`,
`|⟨u, T^t w⟩ − c^t ⟨u,ψ⟩⟨w,ψ⟩| ≤ (1/2)^⌊t/n⌋ ‖T‖^t ‖u‖ ‖w‖`. It is `pow_sub_vac_le` paired with `u`
by Cauchy–Schwarz. With `u = A ψ`, `w = B ψ` and `c^t` divided out, it is the connected correlation
of the infinite-time-extent transfer state.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the unit norm of `ψ`; `0` the value of
the inner product on the vacuum complement. -/
theorem inner_pow_sub_le {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    {ψ : E} {c : ℝ} (hψ : T ψ = c • ψ) {n : ℕ}
    (hgap : ∀ f : E, inner ℝ f ψ = 0 → ‖(T ^ n) f‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖f‖)
    (hψ1 : ‖ψ‖ = 1) (t : ℕ) (u w : E) :
    |inner ℝ u ((T ^ t) w) - c ^ t * (inner ℝ u ψ * inner ℝ w ψ)|
      ≤ (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖u‖ * ‖w‖ := by
  have e : inner ℝ u ((T ^ t) w) - c ^ t * (inner ℝ u ψ * inner ℝ w ψ)
      = inner ℝ u ((T ^ t) w - (inner ℝ w ψ * c ^ t) • ψ) := by
    rw [inner_sub_right, real_inner_smul_right]; ring
  rw [e]
  calc |inner ℝ u ((T ^ t) w - (inner ℝ w ψ * c ^ t) • ψ)|
      ≤ ‖u‖ * ‖(T ^ t) w - (inner ℝ w ψ * c ^ t) • ψ‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * ((1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖w‖) :=
        mul_le_mul_of_nonneg_left (pow_sub_vac_le hT hψ hgap hψ1 t w) (norm_nonneg _)
    _ = (1 / 2) ^ (t / n) * ‖T‖ ^ t * ‖u‖ * ‖w‖ := by ring

/-- **The normalized vacuum-sector correlation clusters with constant `1`**: with `|c| = ‖T‖`,
`c ≠ 0` and `‖ψ‖ = 1`, `|⟨u, T^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ (1/2)^⌊t/n⌋ ‖u‖ ‖w‖` at every `t`. It is
`inner_pow_sub_le` divided by `|c|^t = ‖T‖^t`. The bound involves only the gap: no dimension, volume
or norm of `T` enters.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the unit norm of `ψ`; `0` the value of
the inner product on the vacuum complement and the excluded eigenvalue. -/
theorem inner_pow_div_sub_le {T : E →L[ℝ] E} (hT : ∀ u w, inner ℝ (T u) w = inner ℝ u (T w))
    {ψ : E} {c : ℝ} (hψ : T ψ = c • ψ) {n : ℕ}
    (hgap : ∀ f : E, inner ℝ f ψ = 0 → ‖(T ^ n) f‖ ≤ 1 / 2 * ‖T‖ ^ n * ‖f‖)
    (hψ1 : ‖ψ‖ = 1) (hc : |c| = ‖T‖) (hc0 : c ≠ 0) (t : ℕ) (u w : E) :
    |inner ℝ u ((T ^ t) w) / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
      ≤ (1 / 2) ^ (t / n) * ‖u‖ * ‖w‖ := by
  have h := inner_pow_sub_le hT hψ hgap hψ1 t u w
  rw [← hc] at h
  have hct : c ^ t ≠ 0 := pow_ne_zero _ hc0
  have hpos : 0 < |c| ^ t := pow_pos (abs_pos.mpr hc0) _
  have e : inner ℝ u ((T ^ t) w) / c ^ t - inner ℝ u ψ * inner ℝ w ψ
      = (inner ℝ u ((T ^ t) w) - c ^ t * (inner ℝ u ψ * inner ℝ w ψ)) / c ^ t := by
    field_simp
  rw [e, abs_div, abs_pow, div_le_iff₀ hpos]
  exact le_of_le_of_eq h (by ring)

/-- **The floor rate in exponential form**: `(1/2)^⌊t/n⌋ ≤ 2 e^{−(log 2/n) t}` for `n ≥ 1`, since
`⌊t/n⌋ > t/n − 1`.

DERIVED: `1/2` is the contraction of the gap; `2` its inverse, whose logarithm is the rate; `1` the
least `n` and the floor's defect. -/
theorem half_pow_div_le_exp {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    (1 / 2 : ℝ) ^ (t / n) ≤ 2 * Real.exp (-(Real.log 2 / n) * t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : (1 / 2 : ℝ) ^ (t / n) = Real.exp (-(((t / n : ℕ) : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, one_div, inv_pow]
  have e2 : 2 * Real.exp (-(Real.log 2 / n) * t) = Real.exp (Real.log 2 + -(Real.log 2 / n) * t) := by
    rw [Real.exp_add, Real.exp_log two_pos]
  have hq : (t : ℝ) / n ≤ ((t / n : ℕ) : ℝ) + 1 := by
    have h1 : t < t / n * n + n := Nat.lt_div_mul_add (by omega)
    have h2 : (t : ℝ) ≤ ((t / n : ℕ) : ℝ) * n + n := by exact_mod_cast h1.le
    rw [div_le_iff₀ hn0]; linarith
  rw [e1, e2, Real.exp_le_exp]
  have h3 : Real.log 2 / n * t = Real.log 2 * (t / n) := by ring
  have h4 : Real.log 2 * ((t : ℝ) / n) ≤ Real.log 2 * (((t / n : ℕ) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hq hL.le
  nlinarith

end Abstract

/-! ## 2. The trace ratio, at the kernel level -/

section Trace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `Tr K^{m+1}` as a kernel integral: `trPow μ k m = ∫ k^{∗(m+1)}(x, x) dμ(x)`.

DERIVED: no numeral appears in the statement. -/
noncomputable def trPow (μ : Measure X) (k : X → X → ℝ) (m : ℕ) : ℝ := ∫ x, iter μ k m x x ∂μ

/-- `Tr(A K^{m+1})` for the multiplication operator `A` by `a`:
`trIns μ k a m = ∫ a(x) k^{∗(m+1)}(x, x) dμ(x)`.

DERIVED: no numeral appears in the statement. -/
noncomputable def trIns (μ : Measure X) (k : X → X → ℝ) (a : X → ℝ) (m : ℕ) : ℝ :=
  ∫ x, a x * iter μ k m x x ∂μ

/-- `Tr(A K^{p+1} B K^{q+1})` for the multiplication operators `A`, `B` by `a`, `b`:
`trPair μ k a b p q = ∫∫ a(x) k^{∗(p+1)}(x,y) b(y) k^{∗(q+1)}(y,x)`.

DERIVED: no numeral appears in the statement. -/
noncomputable def trPair (μ : Measure X) (k : X → X → ℝ) (a b : X → ℝ) (p q : ℕ) : ℝ :=
  ∫ x, ∫ y, a x * iter μ k p x y * b y * iter μ k q y x ∂μ ∂μ

/-- The connected two-slice correlation on the periodic chain of `L = p + q + 2` copies of `k`, with
`a` at one slice and `b` at time separation `t = p + 1`:
`Tr(A K^t B K^{L−t})/Tr K^L − (Tr(A K^L)/Tr K^L)(Tr(B K^L)/Tr K^L)`. `Tr(B K^L)` is the one-point
reading of `b` at every slice, by cyclicity of the trace.

DERIVED: `1` and `2` are the offsets of `iter` (`iter k m = k^{∗(m+1)}`), so the chain has
`p + q + 2` steps. -/
noncomputable def connTorus (μ : Measure X) (k : X → X → ℝ) (a b : X → ℝ) (p q : ℕ) : ℝ :=
  trPair μ k a b p q / trPow μ k (p + q + 1)
    - trIns μ k a (p + q + 1) / trPow μ k (p + q + 1)
      * (trIns μ k b (p + q + 1) / trPow μ k (p + q + 1))

/-- `trPow` is the cyclic integral: `trPow μ k m = CyclicKernel.cyc μ k (m + 1)`, the integral of
`∏_t k(W_t, W_{t+1})` over `m + 1` points on a cycle (`CyclicKernel.cyc_succ`).

DERIVED: `1` is the offset of `iter`. -/
theorem trPow_eq_cyc {k : X → X → ℝ} (hk : Bdd k) (m : ℕ) :
    trPow μ k m = CyclicKernel.cyc μ k (m + 1) :=
  (CyclicKernel.cyc_succ hk m).symm

/-- A bounded measurable function of the first variable is a bounded kernel.

DERIVED: no numeral appears in the statement. -/
theorem bdd_left {a : X → ℝ} (ham : Measurable a) {A : ℝ} (hab : ∀ x, |a x| ≤ A) :
    Bdd (fun x (_ : X) => a x) :=
  ⟨ham.comp measurable_fst, A, fun x _ => hab x⟩

/-- A bounded measurable function of the second variable is a bounded kernel.

DERIVED: no numeral appears in the statement. -/
theorem bdd_right {a : X → ℝ} (ham : Measurable a) {A : ℝ} (hab : ∀ x, |a x| ≤ A) :
    Bdd (fun (_ : X) y => a y) :=
  ⟨ham.comp measurable_snd, A, fun _ y => hab y⟩

/-- A constant is a bounded kernel.

DERIVED: no numeral appears in the statement. -/
theorem bdd_const (r : ℝ) : Bdd (fun (_ _ : X) => r) :=
  ⟨measurable_const, |r|, fun _ _ => le_refl _⟩

/-- Iterated integrals of bounded kernels add: `∫∫ (F + G) = ∫∫ F + ∫∫ G`.

DERIVED: no numeral appears in the statement. -/
theorem iint_add {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) :
    ∫ x, ∫ y, (F x y + G x y) ∂μ ∂μ = ∫ x, ∫ y, F x y ∂μ ∂μ + ∫ x, ∫ y, G x y ∂μ ∂μ := by
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  have hrow : ∀ x, ∫ y, (F x y + G x y) ∂μ = ∫ y, F x y ∂μ + ∫ y, G x y ∂μ := fun x =>
    integral_add (integrable_of_bdd (hF.row x) (hCF x)) (integrable_of_bdd (hG.row x) (hCG x))
  simp_rw [hrow]
  exact integral_add
    (integrable_of_bdd (measurable_integral_right hF.meas) (fun x => abs_integral_le (hCF x)))
    (integrable_of_bdd (measurable_integral_right hG.meas) (fun x => abs_integral_le (hCG x)))

/-- A pointwise bound `|F| ≤ G` of bounded kernels passes to iterated integrals:
`|∫∫ F| ≤ ∫∫ G`.

DERIVED: no numeral appears in the statement. -/
theorem abs_iint_le {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) (h : ∀ x y, |F x y| ≤ G x y) :
    |∫ x, ∫ y, F x y ∂μ ∂μ| ≤ ∫ x, ∫ y, G x y ∂μ ∂μ := by
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  calc |∫ x, ∫ y, F x y ∂μ ∂μ| ≤ ∫ x, |∫ y, F x y ∂μ| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ∫ y, G x y ∂μ ∂μ := by
        refine integral_mono
          ((integrable_of_bdd (measurable_integral_right hF.meas)
            (fun x => abs_integral_le (hCF x))).abs)
          (integrable_of_bdd (measurable_integral_right hG.meas) (fun x => abs_integral_le (hCG x)))
          (fun x => ?_)
        exact abs_integral_le_integral_abs.trans (integral_mono
          (integrable_of_bdd (hF.row x) (hCF x)).abs (integrable_of_bdd (hG.row x) (hCG x))
          (fun y => h x y))

/-- The weighted arithmetic–geometric mean inequality: for `u, v > 0`,
`|f g| ≤ ((v/u) f² + (u/v) g²)/2`, from `(v|f| − u|g|)² ≥ 0`.

DERIVED: `2` is the square and the halving of the arithmetic mean; `0` the sign of the weights. -/
theorem abs_mul_le_amgm {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (f g : ℝ) :
    |f * g| ≤ (v / u * f ^ 2 + u / v * g ^ 2) / 2 := by
  have key : 2 * (u * v) * |f * g| ≤ v ^ 2 * f ^ 2 + u ^ 2 * g ^ 2 := by
    rw [abs_mul]
    have h := sq_nonneg (v * |f| - u * |g|)
    have hf := sq_abs f
    have hg := sq_abs g
    nlinarith
  have hu' := hu.ne'
  have hv' := hv.ne'
  have e : (v / u * f ^ 2 + u / v * g ^ 2) / 2 = (v ^ 2 * f ^ 2 + u ^ 2 * g ^ 2) / (2 * (u * v)) := by
    field_simp
  rw [e, le_div_iff₀ (mul_pos two_pos (mul_pos hu hv))]
  linarith

/-- The real-number bookkeeping of the trace ratio. With `Z = Λ(1+σ)`, `Tr(A K^L) = Λ(α + e_a)`,
`Tr(B K^L) = Λ(β + e_b)`, `Tr(A K^t B K^{L−t}) = Λ(αβ + e)`, `Λ > 0`, `σ ≥ 0`, `|α| ≤ A`, `|β| ≤ B`,
`|e_a| ≤ Aσ` and `|e_b| ≤ Bσ`, the connected ratio is within `|e| + 4ABσ` of zero.

The difference is `e/(1+σ) + (αβσ − α e_b − β e_a − e_a e_b)/(1+σ)²`; the four terms of the second
numerator are at most `ABσ(3 + σ) ≤ 4ABσ(1+σ)²`.

DERIVED: `4` bounds `3 + σ` by `4(1+σ)²`, where `3` counts the three first-order terms; `1` is the
vacuum's own weight in `Z`; `2` the square of `1+σ`; `0` the signs. -/
theorem conn_alg {Λ σ α β ea eb e A B : ℝ} (hΛ : 0 < Λ) (hσ : 0 ≤ σ)
    (hα : |α| ≤ A) (hβ : |β| ≤ B) (hea : |ea| ≤ A * σ) (heb : |eb| ≤ B * σ) :
    |Λ * (α * β + e) / (Λ * (1 + σ))
        - Λ * (α + ea) / (Λ * (1 + σ)) * (Λ * (β + eb) / (Λ * (1 + σ)))|
      ≤ |e| + 4 * (A * B) * σ := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hα
  have hB : 0 ≤ B := (abs_nonneg _).trans hβ
  have hD : 0 < 1 + σ := by linarith
  have hΛ' : Λ ≠ 0 := hΛ.ne'
  have hD' : 1 + σ ≠ 0 := hD.ne'
  have key : Λ * (α * β + e) / (Λ * (1 + σ))
        - Λ * (α + ea) / (Λ * (1 + σ)) * (Λ * (β + eb) / (Λ * (1 + σ)))
      = e / (1 + σ) + (α * β * σ - α * eb - β * ea - ea * eb) / (1 + σ) ^ 2 := by
    field_simp; ring
  rw [key]
  have h1 : |e / (1 + σ)| ≤ |e| := by
    rw [abs_div, abs_of_pos hD]; exact div_le_self (abs_nonneg _) (by linarith)
  have t1 : |α * β * σ| ≤ A * B * σ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hα hβ (abs_nonneg _) hA) hσ
  have t2 : |α * eb| ≤ A * (B * σ) := by
    rw [abs_mul]; exact mul_le_mul hα heb (abs_nonneg _) hA
  have t3 : |β * ea| ≤ B * (A * σ) := by
    rw [abs_mul]; exact mul_le_mul hβ hea (abs_nonneg _) hB
  have t4 : |ea * eb| ≤ A * σ * (B * σ) := by
    rw [abs_mul]; exact mul_le_mul hea heb (abs_nonneg _) (by positivity)
  have h2 : |α * β * σ - α * eb - β * ea - ea * eb| ≤ 4 * (A * B) * σ * (1 + σ) ^ 2 := by
    have s1 := abs_sub (α * β * σ - α * eb - β * ea) (ea * eb)
    have s2 := abs_sub (α * β * σ - α * eb) (β * ea)
    have s3 := abs_sub (α * β * σ) (α * eb)
    have hAB : 0 ≤ A * B * σ := mul_nonneg (mul_nonneg hA hB) hσ
    nlinarith [mul_nonneg hAB hσ, mul_nonneg (mul_nonneg hAB hσ) hσ]
  have h3 : |(α * β * σ - α * eb - β * ea - ea * eb) / (1 + σ) ^ 2| ≤ 4 * (A * B) * σ := by
    rw [abs_div, abs_of_pos (pow_pos hD 2), div_le_iff₀ (pow_pos hD 2)]
    exact h2
  calc |e / (1 + σ) + (α * β * σ - α * eb - β * ea - ea * eb) / (1 + σ) ^ 2|
      ≤ |e / (1 + σ)| + |(α * β * σ - α * eb - β * ea - ea * eb) / (1 + σ) ^ 2| := abs_add_le _ _
    _ ≤ |e| + 4 * (A * B) * σ := add_le_add h1 h3

/-- An eigenvector in `L²` of a bounded kernel operator gives a bounded measurable pointwise
eigenfunction with the same class: if `K ψ = c ψ`, `‖ψ‖ = 1` and `c ≠ 0`, then
`φ = c⁻¹ ∫ k(·,y) ψ(y) dμ(y)` is measurable, bounded by `|c|⁻¹ C`, has `∫ φ² = 1`, satisfies
`∫ k(z,y) φ(y) dμ(y) = c φ(z)` at every `z`, and `KernelGap.vac φ = ψ`. This is the second half of
`KernelEigen.exists_eigen`, kept with the vector it starts from.

DERIVED: `2` is the `L²` exponent and the square; `1` the unit norm; `0` the excluded eigenvalue. -/
theorem exists_eigenfun {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k))
    (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C) {ψ : Lp ℝ 2 μ} (hψ1 : ‖ψ‖ = 1) {c : ℝ} (hc0 : c ≠ 0)
    (hKψ : kernelCLM k C hkm hC0 hkb μ μ ψ = c • ψ) :
    ∃ φ : X → ℝ, ∃ hφm : Measurable φ, ∃ B : ℝ, ∃ hφb : ∀ x, |φ x| ≤ B,
      ∫ x, φ x ^ 2 ∂μ = 1 ∧ (∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) ∧
        KernelGap.vac (μ := μ) hφm hφb = ψ := by
  set φ : X → ℝ := fun z => c⁻¹ * kernelFun k μ (ψ : X → ℝ) z with hφdef
  have hφψ : φ =ᵐ[μ] (ψ : X → ℝ) := by
    filter_upwards [coeFn_kernelCLM k C hkm hC0 hkb μ μ ψ, Lp.coeFn_smul c ψ] with z h1 h2
    simp only [φ]
    rw [← h1]
    have : ((kernelCLM k C hkm hC0 hkb μ μ ψ : Lp ℝ 2 μ) : X → ℝ) z
        = ((c • ψ : Lp ℝ 2 μ) : X → ℝ) z := by rw [hKψ]
    rw [this, h2]; simp [hc0]
  have hφm : Measurable φ := measurable_const.mul (stronglyMeasurable_kernelFun hkm ψ).measurable
  have hφb : ∀ x, |φ x| ≤ |c|⁻¹ * (C * ‖ψ‖) := fun x => by
    simp only [φ]; rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (abs_kernelFun_le hkm hC0 hkb ψ x) (by positivity)
  refine ⟨φ, hφm, _, hφb, ?_, fun z => ?_, ?_⟩
  · have : ∫ x, φ x ^ 2 ∂μ = ∫ x, (ψ : X → ℝ) x ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with x hx; rw [hx]
    rw [this, ← KernelPower.norm_sq_eq_integral, hψ1, one_pow]
  · have h1 : ∫ y, k z y * φ y ∂μ = kernelFun k μ (ψ : X → ℝ) z := by
      unfold kernelFun
      refine integral_congr_ae ?_
      filter_upwards [hφψ] with y hy; rw [hy]
    rw [h1]; simp only [φ]; field_simp
  · apply Lp.ext
    have hv : ((KernelGap.vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] φ :=
      (KernelGap.memLp_φ (μ := μ) hφm hφb).coeFn_toLp
    exact hv.trans hφψ

section Corr

variable {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
  (hkb : ∀ x y, |k x y| ≤ C) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)
  (hnorm : |c| = ‖kernelCLM k C hkm hC0 hkb μ μ‖) {n : ℕ}
  (hgap : ∀ f : Lp ℝ 2 μ, inner ℝ f (KernelGap.vac (μ := μ) hφm hφb) = 0 →
    ‖((kernelCLM k C hkm hC0 hkb μ μ) ^ n) f‖
      ≤ 1 / 2 * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ n * ‖f‖)

omit [MeasurableSpace X] in
include hsym in
/-- The remainder `r = k − c φ⊗φ` of a symmetric kernel is symmetric.

DERIVED: no numeral appears in the statement. -/
theorem rem_symm (x y : X) : rem k c φ x y = rem k c φ y x := by
  unfold MassGap.KernelPower.rem; rw [hsym]; ring

include hkm hkb hsym hφm hφb in
/-- The diagonal of an even power of the remainder is a square integral:
`r^{∗(2i+2)}(x, x) = ∫ r^{∗(i+1)}(x, y)² dμ(y)`, by `iter_add` and the symmetry of `r^{∗(i+1)}`
(`CyclicKernel.iter_symm`). In particular it is nonnegative and integrates to `hs(r^{∗(i+1)})`.

DERIVED: `1` and `2` are the offsets of `iter`; `2` is also the square. -/
theorem iter_rem_diag (i : ℕ) (x : X) :
    iter μ (rem k c φ) (i + i + 1) x x = ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk hφm hφb (c := c)
  rw [iter_add hr i i]
  unfold conv
  congr 1; funext y
  rw [CyclicKernel.iter_symm hr (rem_symm hsym) i y x, sq]

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **A vacuum-to-excited matrix element of the trace decays**: for bounded measurable `u`, `g` with
`∫ u² ≤ U²` and `∫ g² ≤ G²`,
`|∫ u(x) ∫ r^{∗(m+1)}(x,y) g(y) dμ(y) dμ(x)| ≤ (1/2)^⌊(m+1)/n⌋ |c|^(m+1) U G`.

The inner function is `K^{m+1} g − c^{m+1} ⟨g, φ⟩ φ` almost everywhere (`KernelGap.opPow_coe` and
`iter_decomp`), so the integral is an `L²` pairing bounded by Cauchy–Schwarz and `pow_sub_vac_le`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the `L²`
exponent and the squares; `0` the signs of `U` and `G`. -/
theorem abs_integral_remFun_le (m : ℕ) {u g : X → ℝ} (hum : Measurable u) (hgm : Measurable g)
    {Cu Cg : ℝ} (hub : ∀ x, |u x| ≤ Cu) (hgb : ∀ x, |g x| ≤ Cg) {U G : ℝ} (hU : 0 ≤ U)
    (hG : 0 ≤ G) (hu2 : ∫ x, u x ^ 2 ∂μ ≤ U ^ 2) (hg2 : ∫ x, g x ^ 2 ∂μ ≤ G ^ 2) :
    |∫ x, u x * kernelFun (iter μ (rem k c φ) m) μ g x ∂μ|
      ≤ (1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1) * U * G := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hTs : ∀ u w, inner ℝ (kernelCLM k C hkm hC0 hkb μ μ u) w
      = inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ w) := fun u w =>
    (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C hkm hC0 hkb μ hsym).isSymmetric
      u w
  have hv := KernelGap.K_vac hkm hC0 hkb hφm hφb heig
  have hv1 := KernelGap.norm_vac hφm hφb hφ1
  have hgL : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable Cg
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb x)
  have huL : MemLp u 2 μ := MemLp.of_bound hum.aestronglyMeasurable Cu
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hub x)
  obtain ⟨gL, hgLe⟩ : ∃ G : Lp ℝ 2 μ, (G : X → ℝ) =ᵐ[μ] g := ⟨hgL.toLp g, hgL.coeFn_toLp⟩
  obtain ⟨uL, huLe⟩ : ∃ G : Lp ℝ 2 μ, (G : X → ℝ) =ᵐ[μ] u := ⟨huL.toLp u, huL.coeFn_toLp⟩
  have hdec := pow_sub_vac_le hTs hv hgap hv1 (m + 1) gL
  -- the pointwise identity
  have hpt : ∀ x, kernelFun (iter μ (rem k c φ) m) μ g x
      = kernelFun (iter μ k m) μ g x - c ^ (m + 1) * φ x * ∫ y, φ y * g y ∂μ := by
    intro x
    obtain ⟨Cr, hCr⟩ := ((Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) m).bdd
    unfold kernelFun
    have e : (fun y => iter μ k m x y * g y)
        = fun y => (c ^ (m + 1) * φ x) * (φ y * g y) + iter μ (rem k c φ) m x y * g y := by
      funext y; rw [iter_decomp hk hsym hφm hφb hφ1 heig m x y]; ring
    rw [e, integral_add ((integrable_mul_of_bdd hφm hgm hφb hgb).const_mul _)
      (integrable_mul_of_bdd (((Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) m).row x) hgm
        (fun y => hCr x y) hgb), integral_const_mul]
    ring
  have hφg : inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) = ∫ y, φ y * g y ∂μ := by
    rw [KernelGap.inner_vac hφm hφb gL]
    refine integral_congr_ae ?_
    filter_upwards [hgLe] with y hy
    rw [hy]
  have hvae : ((KernelGap.vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] φ :=
    (KernelGap.memLp_φ (μ := μ) hφm hφb).coeFn_toLp
  have hwae : (((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
      - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        • KernelGap.vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => kernelFun (iter μ (rem k c φ) m) μ g x := by
    filter_upwards [Lp.coeFn_sub ((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL)
        ((inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
          • KernelGap.vac (μ := μ) hφm hφb),
      Lp.coeFn_smul (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        (KernelGap.vac (μ := μ) hφm hφb),
      KernelGap.opPow_coe hkm hC0 hkb gL m, hvae] with x hs hsm hk1 hφx
    rw [hs, Pi.sub_apply, hsm, Pi.smul_apply, hk1, hφx, smul_eq_mul,
      kernelFun_congr hgLe x, hpt, hφg]
    ring
  have hinner : inner ℝ uL ((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
      - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        • KernelGap.vac (μ := μ) hφm hφb)
      = ∫ x, u x * kernelFun (iter μ (rem k c φ) m) μ g x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [huLe, hwae] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hnorm2 : ∀ (F : Lp ℝ 2 μ) (f : X → ℝ) (W : ℝ), 0 ≤ W → (F : X → ℝ) =ᵐ[μ] f →
      ∫ x, f x ^ 2 ∂μ ≤ W ^ 2 → ‖F‖ ≤ W := by
    intro F f W hW hF hf
    have h := KernelPower.norm_sq_eq_integral F
    have h' : ∫ x, (F : X → ℝ) x ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ :=
      integral_congr_ae (by filter_upwards [hF] with x hx; rw [hx])
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hW two_ne_zero).mp (by rw [h, h']; exact hf)
  have hnu : ‖uL‖ ≤ U := hnorm2 uL u U hU huLe hu2
  have hng : ‖gL‖ ≤ G := hnorm2 gL g G hG hgLe hg2
  rw [← hinner]
  calc |inner ℝ uL ((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
        - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
          • KernelGap.vac (μ := μ) hφm hφb)|
      ≤ ‖uL‖ * ‖(kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
        - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
          • KernelGap.vac (μ := μ) hφm hφb‖ := abs_real_inner_le_norm _ _
    _ ≤ U * ((1 / 2) ^ ((m + 1) / n) * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (m + 1) * ‖gL‖) :=
        mul_le_mul hnu hdec (norm_nonneg _) hU
    _ ≤ U * ((1 / 2) ^ ((m + 1) / n) * ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ (m + 1) * G) := by
        gcongr
    _ = (1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1) * U * G := by rw [← hnorm]; ring

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The connected two-slice torus correlation, bounded by the gap**: on the periodic chain of
`L = p + q + 2` copies of `k` (`L` even), with insertions `|a| ≤ A`, `|b| ≤ B` at time separation
`t = p + 1`,

    |connTorus μ k a b p q| ≤ A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋ + (σ_t + σ_{L−t})/2 + 4 σ_{L/2}),

where `σ_j = excited μ k c φ j = hs(r^{∗j})/|c|^{2j}` is the relative excited weight at `j` steps.

Proof. By `iter_decomp`, `k^{∗j} = c^j φ⊗φ + r^{∗j}`. Then `Tr K^L = Λ(1 + σ_{L/2})` with
`Λ = |c|^L` (`iter_rem_diag`), `Tr(A K^L) = Λ(⟨a φ, φ⟩ + e_a)` with `|e_a| ≤ A σ_{L/2}`, and
`Tr(A K^t B K^{L−t}) = Λ(⟨aφ,φ⟩⟨bφ,φ⟩ + e)`, where `Λ e` is the sum of two vacuum-to-excited terms,
bounded by `abs_integral_remFun_le` at `t` and at `L − t`, and the excited–excited term, bounded by
`abs_mul_le_amgm` with weights `|c|^t`, `|c|^{L−t}`. `conn_alg` closes.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` and `2` are the offsets of `iter`, so
`t = p + 1`, `L − t = q + 1` and `L/2 = (p + q)/2 + 1`; the `2` dividing `σ_t + σ_{L−t}` is the
arithmetic mean of `abs_mul_le_amgm`; `4` is the constant of `conn_alg`; `0` the excluded
eigenvalue. -/
theorem connTorus_le (hc0 : c ≠ 0) {a b : X → ℝ} (ham : Measurable a) (hbm : Measurable b)
    {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ) (hpq : Even (p + q)) :
    |connTorus μ k a b p q| ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
      + (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2
      + 4 * excited μ k c φ ((p + q) / 2 + 1)) := by
  obtain ⟨i, hi⟩ := hpq
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2]
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  have hrs : ∀ x y, rem k c φ x y = rem k c φ y x := rem_symm hsym
  have hrp := hr.iter (μ := μ) p
  have hrq := hr.iter (μ := μ) q
  have hri := hr.iter (μ := μ) i
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hu0 : 0 < |c| ^ (p + 1) := pow_pos hc _
  have hv0 : 0 < |c| ^ (q + 1) := pow_pos hc _
  have hΛ : 0 < |c| ^ (p + 1) * |c| ^ (q + 1) := mul_pos hu0 hv0
  have hev : Even (p + 1 + (q + 1)) := ⟨i + 1, by omega⟩
  have hcc : c ^ (p + 1) * c ^ (q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add, ← pow_add, hev.pow_abs c]
  have hune := hu0.ne'
  have hvne := hv0.ne'
  have hσ : ∀ j : ℕ, excited μ k c φ (j + 1) = hs μ (iter μ (rem k c φ) j) / |c| ^ (2 * (j + 1)) :=
    fun j => by unfold excited; rw [Nat.add_sub_cancel]
  have hsqp : |c| ^ (2 * (p + 1)) = (|c| ^ (p + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  have hsqq : |c| ^ (2 * (q + 1)) = (|c| ^ (q + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  have hsqi : |c| ^ (2 * (i + 1)) = |c| ^ (p + 1) * |c| ^ (q + 1) := by
    rw [← pow_add]; congr 1; omega
  have hφsq : Integrable (fun x => φ x ^ 2) μ := integrable_of_bdd (hφm.pow_const 2) (C := Bφ ^ 2)
    (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2)
  have hφφ : Integrable (fun x => φ x * φ x) μ := by simpa [sq] using hφsq
  have hφ1' : ∫ x, φ x * φ x ∂μ = 1 := by simpa [sq] using hφ1
  -- the one-insertion trace
  have hone : ∀ (f : X → ℝ), Measurable f → ∀ F : ℝ, (∀ x, |f x| ≤ F) →
      trIns μ k f (p + q + 1) = |c| ^ (p + 1) * |c| ^ (q + 1) * (∫ x, f x * (φ x * φ x) ∂μ
        + (∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ) / (|c| ^ (p + 1) * |c| ^ (q + 1)))
      ∧ |∫ x, f x * (φ x * φ x) ∂μ| ≤ F
      ∧ |(∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ) / (|c| ^ (p + 1) * |c| ^ (q + 1))|
        ≤ F * excited μ k c φ (i + 1) := by
    intro f hfm F hfb
    obtain ⟨Ci, hCi⟩ := hri.bdd
    have hD0 : ∀ x, 0 ≤ ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      fun x => integral_nonneg fun y => sq_nonneg _
    have hDb : ∀ x, |∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ| ≤ Ci ^ 2 := fun x =>
      abs_integral_le fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCi x y) 2
    have hDm : Measurable fun x => ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      measurable_integral_right (hri.meas.pow_const 2)
    have i1 : Integrable (fun x => f x * (φ x * φ x)) μ :=
      integrable_of_bdd (hfm.mul (hφm.mul hφm)) (C := F * (Bφ * Bφ))
        (fun x => HiddenChain.abs_mul_le_of (hfb x) (HiddenChain.abs_mul_le_of (hφb x) (hφb x)))
    have i2 : Integrable (fun x => f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ) μ :=
      integrable_of_bdd (hfm.mul hDm) (C := F * Ci ^ 2)
        (fun x => HiddenChain.abs_mul_le_of (hfb x) (hDb x))
    have hDint : Integrable (fun x => ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ) μ :=
      integrable_of_bdd hDm hDb
    have hD : ∀ x, iter μ (rem k c φ) (p + q + 1) x x = ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ :=
      fun x => by rw [hi]; exact iter_rem_diag hkm hkb hsym hφm hφb i x
    have e : ∀ x, f x * iter μ k (p + q + 1) x x
        = |c| ^ (p + 1) * |c| ^ (q + 1) * (f x * (φ x * φ x))
          + f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ := by
      intro x
      rw [iter_decomp hk hsym hφm hφb hφ1 heig (p + q + 1) x x, hD x, ← hcc]
      ring
    refine ⟨?_, ?_, ?_⟩
    · unfold trIns
      simp_rw [e]
      rw [integral_add (i1.const_mul _) i2, integral_const_mul]
      field_simp
    · calc |∫ x, f x * (φ x * φ x) ∂μ| ≤ ∫ x, |f x * (φ x * φ x)| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x, F * (φ x * φ x) ∂μ := integral_mono i1.abs (hφφ.const_mul F) (fun x => by
            rw [abs_mul, abs_of_nonneg (mul_self_nonneg (φ x))]
            exact mul_le_mul_of_nonneg_right (hfb x) (mul_self_nonneg _))
        _ = F := by rw [integral_const_mul, hφ1', mul_one]
    · have h1 : |∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ|
          ≤ F * hs μ (iter μ (rem k c φ) i) := by
        calc |∫ x, f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ|
            ≤ ∫ x, |f x * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ x, F * ∫ y, iter μ (rem k c φ) i x y ^ 2 ∂μ ∂μ :=
              integral_mono i2.abs (hDint.const_mul F) (fun x => by
                rw [abs_mul, abs_of_nonneg (hD0 x)]
                exact mul_le_mul_of_nonneg_right (hfb x) (hD0 x))
          _ = F * hs μ (iter μ (rem k c φ) i) := by rw [integral_const_mul]; rfl
      rw [abs_div, abs_of_pos hΛ, hσ i, hsqi, mul_div_assoc']
      exact div_le_div_of_nonneg_right h1 hΛ.le
  obtain ⟨hNa, hα, hea⟩ := hone a ham A hab
  obtain ⟨hNb, hβ', heb⟩ := hone b hbm B hbb
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hα
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hβ'
  -- the partition function
  have hZ : trPow μ k (p + q + 1)
      = |c| ^ (p + 1) * |c| ^ (q + 1) * (1 + excited μ k c φ (i + 1)) := by
    have h := (hone (fun _ => 1) measurable_const 1 (fun _ => by simp)).1
    have h1 : trIns μ k (fun _ => 1) (p + q + 1) = trPow μ k (p + q + 1) := by
      unfold trIns trPow; simp
    rw [← h1, h]
    simp only [one_mul]
    rw [hφ1', hσ i, hsqi]
    rfl
  -- the two-insertion trace, term by term
  have Ba : ∀ x, |a x * φ x| ≤ A * Bφ := fun x => HiddenChain.abs_mul_le_of (hab x) (hφb x)
  have Bb : ∀ x, |b x * φ x| ≤ B * Bφ := fun x => HiddenChain.abs_mul_le_of (hbb x) (hφb x)
  have hG1 : Bdd (fun x y => c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x))
      * (b y * (φ y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul (hφm.mul hφm)))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _)
          (HiddenChain.abs_mul_le_of (hab x) (HiddenChain.abs_mul_le_of (hφb x) (hφb x)))))
      (bdd_right (hbm.mul (hφm.mul hφm))
        (fun y => HiddenChain.abs_mul_le_of (hbb y) (HiddenChain.abs_mul_le_of (hφb y) (hφb y))))
  have hG2 : Bdd (fun x y => c ^ (p + 1) * (a x * φ x)
      * (iter μ (rem k c φ) q x y * (b y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul hφm))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _) (Ba x)))
      (FluxSectorBound.bdd_mul hrq (bdd_right (hbm.mul hφm) Bb))
  have hG3 : Bdd (fun x y => c ^ (q + 1) * (a x * φ x)
      * (iter μ (rem k c φ) p x y * (b y * φ y))) :=
    FluxSectorBound.bdd_mul
      (bdd_left (measurable_const.mul (ham.mul hφm))
        (fun x => HiddenChain.abs_mul_le_of (le_refl _) (Ba x)))
      (FluxSectorBound.bdd_mul hrp (bdd_right (hbm.mul hφm) Bb))
  have hG4 : Bdd (fun x y => a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y) :=
    FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul (FluxSectorBound.bdd_mul
      (bdd_left ham hab) hrp) (bdd_right hbm hbb)) hrq
  have e2 : ∀ x y, a x * iter μ k p x y * b y * iter μ k q y x
      = c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y))
        + c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y))
        + c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y))
        + a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y := by
    intro x y
    rw [iter_decomp hk hsym hφm hφb hφ1 heig p x y, iter_decomp hk hsym hφm hφb hφ1 heig q y x,
      CyclicKernel.iter_symm hr hrs q y x]
    ring
  have hsplit : trPair μ k a b p q
      = ∫ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y)) ∂μ ∂μ
        + ∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ := by
    rw [← iint_add hG1 hG2, ← iint_add (hG1.add hG2) hG3, ← iint_add ((hG1.add hG2).add hG3) hG4]
    unfold trPair
    congr 1; funext x; congr 1; funext y; exact e2 x y
  have v1 : ∫ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ ∂μ
      = |c| ^ (p + 1) * |c| ^ (q + 1) * ((∫ x, a x * (φ x * φ x) ∂μ)
        * ∫ y, b y * (φ y * φ y) ∂μ) := by
    have h1 : ∀ x, ∫ y, c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * (b y * (φ y * φ y)) ∂μ
        = c ^ (p + 1) * c ^ (q + 1) * (a x * (φ x * φ x)) * ∫ y, b y * (φ y * φ y) ∂μ :=
      fun x => integral_const_mul _ _
    simp_rw [h1]
    rw [integral_mul_const, integral_const_mul, hcc]
    ring
  have v2 : ∫ x, ∫ y, c ^ (p + 1) * (a x * φ x) * (iter μ (rem k c φ) q x y * (b y * φ y)) ∂μ ∂μ
      = c ^ (p + 1) * ∫ x, a x * φ x
          * kernelFun (iter μ (rem k c φ) q) μ (fun y => b y * φ y) x ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [integral_const_mul]; simp only [kernelFun]; ring
  have v3 : ∫ x, ∫ y, c ^ (q + 1) * (a x * φ x) * (iter μ (rem k c φ) p x y * (b y * φ y)) ∂μ ∂μ
      = c ^ (q + 1) * ∫ x, a x * φ x
          * kernelFun (iter μ (rem k c φ) p) μ (fun y => b y * φ y) x ∂μ := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [integral_const_mul]; simp only [kernelFun]; ring
  -- the vacuum-to-excited terms
  have hsq2 : ∀ (f : X → ℝ), Measurable f → ∀ F : ℝ, (∀ x, |f x| ≤ F) →
      ∫ x, (f x * φ x) ^ 2 ∂μ ≤ F ^ 2 := by
    intro f hfm F hfb
    calc ∫ x, (f x * φ x) ^ 2 ∂μ ≤ ∫ x, F ^ 2 * φ x ^ 2 ∂μ :=
          integral_mono (integrable_of_bdd ((hfm.mul hφm).pow_const 2) (C := (F * Bφ) ^ 2)
            (fun x => by
              rw [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (HiddenChain.abs_mul_le_of (hfb x) (hφb x)) 2))
            (hφsq.const_mul _) (fun x => by
              rw [mul_pow]
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2)
      _ = F ^ 2 := by rw [integral_const_mul, hφ1, mul_one]
  have I2 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap q
    (ham.mul hφm) (hbm.mul hφm) Ba Bb hA0 hB0 (hsq2 a ham A hab) (hsq2 b hbm B hbb)
  have I3 := abs_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap p
    (ham.mul hφm) (hbm.mul hφm) Ba Bb hA0 hB0 (hsq2 a ham A hab) (hsq2 b hbm B hbb)
  -- the excited–excited term
  have hH : Bdd (fun x y => A * B / 2 * (|c| ^ (q + 1) / |c| ^ (p + 1))
      * (iter μ (rem k c φ) p x y * iter μ (rem k c φ) p x y)
      + A * B / 2 * (|c| ^ (p + 1) / |c| ^ (q + 1))
      * (iter μ (rem k c φ) q x y * iter μ (rem k c φ) q x y)) :=
    (FluxSectorBound.bdd_mul (bdd_const _) (FluxSectorBound.bdd_mul hrp hrp)).add
      (FluxSectorBound.bdd_mul (bdd_const _) (FluxSectorBound.bdd_mul hrq hrq))
  have I4 : |∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ|
      ≤ A * B / 2 * (|c| ^ (q + 1) / |c| ^ (p + 1)) * hs μ (iter μ (rem k c φ) p)
        + A * B / 2 * (|c| ^ (p + 1) / |c| ^ (q + 1)) * hs μ (iter μ (rem k c φ) q) := by
    refine (abs_iint_le hG4 hH (fun x y => ?_)).trans (le_of_eq ?_)
    · have e : a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y
          = (a x * b y) * (iter μ (rem k c φ) p x y * iter μ (rem k c φ) q x y) := by ring
      rw [e, abs_mul]
      calc |a x * b y| * |iter μ (rem k c φ) p x y * iter μ (rem k c φ) q x y|
          ≤ (A * B) * ((|c| ^ (q + 1) / |c| ^ (p + 1) * iter μ (rem k c φ) p x y ^ 2
            + |c| ^ (p + 1) / |c| ^ (q + 1) * iter μ (rem k c φ) q x y ^ 2) / 2) :=
            mul_le_mul (HiddenChain.abs_mul_le_of (hab x) (hbb y))
              (abs_mul_le_amgm hu0 hv0 _ _) (abs_nonneg _) (mul_nonneg hA0 hB0)
        _ = _ := by ring
    · rw [iint_add (FluxSectorBound.bdd_mul (bdd_const (A * B / 2 * (|c| ^ (q + 1) / |c| ^ (p + 1))))
          (FluxSectorBound.bdd_mul hrp hrp))
        (FluxSectorBound.bdd_mul (bdd_const (A * B / 2 * (|c| ^ (p + 1) / |c| ^ (q + 1))))
          (FluxSectorBound.bdd_mul hrq hrq))]
      unfold hs
      simp_rw [integral_const_mul, sq]
  -- assemble
  set I2v := ∫ x, a x * φ x * kernelFun (iter μ (rem k c φ) q) μ (fun y => b y * φ y) x ∂μ
  set I3v := ∫ x, a x * φ x * kernelFun (iter μ (rem k c φ) p) μ (fun y => b y * φ y) x ∂μ
  set T4 := ∫ x, ∫ y, a x * iter μ (rem k c φ) p x y * b y * iter μ (rem k c φ) q x y ∂μ ∂μ
  set Λ := |c| ^ (p + 1) * |c| ^ (q + 1) with hΛdef
  have hΛne : Λ ≠ 0 := hΛ.ne'
  have hN2 : trPair μ k a b p q = Λ * ((∫ x, a x * (φ x * φ x) ∂μ) * ∫ y, b y * (φ y * φ y) ∂μ
      + (c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ) := by
    rw [hsplit, v1, v2, v3]
    field_simp
    ring
  have hsum : |c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4|
      ≤ Λ * (A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2)) := by
    have a2 : |c ^ (p + 1) * I2v| ≤ |c| ^ (p + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * A * B) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I2 hu0.le
    have a3 : |c ^ (q + 1) * I3v| ≤ |c| ^ (q + 1) * ((1 / 2) ^ ((p + 1) / n) * |c| ^ (p + 1) * A * B) := by
      rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left I3 hv0.le
    have eq : |c| ^ (p + 1) * ((1 / 2) ^ ((q + 1) / n) * |c| ^ (q + 1) * A * B)
        + |c| ^ (q + 1) * ((1 / 2) ^ ((p + 1) / n) * |c| ^ (p + 1) * A * B)
        + (A * B / 2 * (|c| ^ (q + 1) / |c| ^ (p + 1)) * hs μ (iter μ (rem k c φ) p)
          + A * B / 2 * (|c| ^ (p + 1) / |c| ^ (q + 1)) * hs μ (iter μ (rem k c φ) q))
        = Λ * (A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
          + (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2)) := by
      rw [hσ p, hσ q, hsqp, hsqq, hΛdef]
      field_simp
      ring
    calc |c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4|
        ≤ |c ^ (p + 1) * I2v| + |c ^ (q + 1) * I3v| + |T4| := abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add a2 a3) I4
      _ = _ := eq
  have he : |(c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ|
      ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
        + (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2) := by
    rw [abs_div, abs_of_pos hΛ, div_le_iff₀ hΛ]
    exact le_of_le_of_eq hsum (mul_comm _ _)
  have hσ0 : 0 ≤ excited μ k c φ (i + 1) := by
    rw [hσ i]; exact div_nonneg (hs_nonneg _) (by positivity)
  have key := conn_alg hΛ hσ0 hα hβ' hea heb
    (e := (c ^ (p + 1) * I2v + c ^ (q + 1) * I3v + T4) / Λ)
  unfold connTorus
  rw [hN2, hZ, hNa, hNb]
  calc _ ≤ _ := key
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
          + (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2)
        + 4 * (A * B) * excited μ k c φ (i + 1) := add_le_add he le_rfl
    _ = _ := by ring

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The excited part of an iterated kernel applied to a function, in `L²`**: for bounded measurable
`g`, `∫ (∫ r^{∗(m+1)}(x,y) g(y) dμ(y))² dμ(x) ≤ ((1/2)^⌊(m+1)/n⌋ |c|^(m+1))² ∫ g²`. The inner
function is `K^{m+1} g − c^{m+1}⟨g, φ⟩ φ` almost everywhere, as in `abs_integral_remFun_le`, and its
`L²` norm is bounded by `pow_sub_vac_le`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter`; `2` the `L²`
exponent and the squares. -/
theorem sq_integral_remFun_le (m : ℕ) {g : X → ℝ} (hgm : Measurable g) {Cg : ℝ}
    (hgb : ∀ x, |g x| ≤ Cg) :
    ∫ x, kernelFun (iter μ (rem k c φ) m) μ g x ^ 2 ∂μ
      ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * ∫ x, g x ^ 2 ∂μ := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hTs : ∀ u w, inner ℝ (kernelCLM k C hkm hC0 hkb μ μ u) w
      = inner ℝ u (kernelCLM k C hkm hC0 hkb μ μ w) := fun u w =>
    (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm k C hkm hC0 hkb μ hsym).isSymmetric
      u w
  have hv := KernelGap.K_vac hkm hC0 hkb hφm hφb heig
  have hv1 := KernelGap.norm_vac hφm hφb hφ1
  have hgL : MemLp g 2 μ := MemLp.of_bound hgm.aestronglyMeasurable Cg
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb x)
  obtain ⟨gL, hgLe⟩ : ∃ G : Lp ℝ 2 μ, (G : X → ℝ) =ᵐ[μ] g := ⟨hgL.toLp g, hgL.coeFn_toLp⟩
  have hdec := pow_sub_vac_le hTs hv hgap hv1 (m + 1) gL
  have hpt : ∀ x, kernelFun (iter μ (rem k c φ) m) μ g x
      = kernelFun (iter μ k m) μ g x - c ^ (m + 1) * φ x * ∫ y, φ y * g y ∂μ := by
    intro x
    obtain ⟨Cr, hCr⟩ := ((Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) m).bdd
    unfold kernelFun
    have e : (fun y => iter μ k m x y * g y)
        = fun y => (c ^ (m + 1) * φ x) * (φ y * g y) + iter μ (rem k c φ) m x y * g y := by
      funext y; rw [iter_decomp hk hsym hφm hφb hφ1 heig m x y]; ring
    rw [e, integral_add ((integrable_mul_of_bdd hφm hgm hφb hgb).const_mul _)
      (integrable_mul_of_bdd (((Bdd.rem hk hφm hφb (c := c)).iter (μ := μ) m).row x) hgm
        (fun y => hCr x y) hgb), integral_const_mul]
    ring
  have hφg : inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) = ∫ y, φ y * g y ∂μ := by
    rw [KernelGap.inner_vac hφm hφb gL]
    refine integral_congr_ae ?_
    filter_upwards [hgLe] with y hy
    rw [hy]
  have hvae : ((KernelGap.vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] φ :=
    (KernelGap.memLp_φ (μ := μ) hφm hφb).coeFn_toLp
  have hwae : (((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
      - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        • KernelGap.vac (μ := μ) hφm hφb : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] fun x => kernelFun (iter μ (rem k c φ) m) μ g x := by
    filter_upwards [Lp.coeFn_sub ((kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL)
        ((inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
          • KernelGap.vac (μ := μ) hφm hφb),
      Lp.coeFn_smul (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        (KernelGap.vac (μ := μ) hφm hφb),
      KernelGap.opPow_coe hkm hC0 hkb gL m, hvae] with x hs hsm hk1 hφx
    rw [hs, Pi.sub_apply, hsm, Pi.smul_apply, hk1, hφx, smul_eq_mul,
      kernelFun_congr hgLe x, hpt, hφg]
    ring
  set w := (kernelCLM k C hkm hC0 hkb μ μ ^ (m + 1)) gL
      - (inner ℝ gL (KernelGap.vac (μ := μ) hφm hφb) * c ^ (m + 1))
        • KernelGap.vac (μ := μ) hφm hφb with hwdef
  have h1 := KernelPower.norm_sq_eq_integral w
  have h2 : ∫ x, (w : X → ℝ) x ^ 2 ∂μ = ∫ x, kernelFun (iter μ (rem k c φ) m) μ g x ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hwae] with x hx; rw [hx])
  have h3 := KernelPower.norm_sq_eq_integral gL
  have h4 : ∫ x, (gL : X → ℝ) x ^ 2 ∂μ = ∫ x, g x ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hgLe] with x hx; rw [hx])
  rw [← h2, ← h1, ← h4, ← h3]
  rw [← hnorm] at hdec
  calc ‖w‖ ^ 2 ≤ ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1) * ‖gL‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdec 2
    _ = ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * ‖gL‖ ^ 2 := by ring

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The excited weight decays with the gap**: `hs(r^{∗(m+1)}) ≤ ((1/2)^⌊m/n⌋ |c|^m)² hs(r)` for
`r = k − c φ⊗φ`. Row `x` of `r^{∗(m+1)}` is `r^{∗m}` applied to row `x` of `r` (symmetry of `r^{∗m}`,
`CyclicKernel.iter_symm`), so `sq_integral_remFun_le` bounds each row; integrate over `x`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `2` the square. -/
theorem hs_iter_rem_le (m : ℕ) :
    hs μ (iter μ (rem k c φ) m) ≤ ((1 / 2) ^ (m / n) * |c| ^ m) ^ 2 * hs μ (rem k c φ) := by
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  obtain ⟨Cr, hCr⟩ := hr.bdd
  cases m with
  | zero => simp [iter]
  | succ m =>
    have hrow : ∀ x z, iter μ (rem k c φ) (m + 1) x z
        = kernelFun (iter μ (rem k c φ) m) μ (rem k c φ x) z := by
      intro x z
      show ∫ y, rem k c φ x y * iter μ (rem k c φ) m y z ∂μ
        = ∫ y, iter μ (rem k c φ) m z y * rem k c φ x y ∂μ
      congr 1; funext y; rw [CyclicKernel.iter_symm hr (rem_symm hsym) m y z, mul_comm]
    have hrm := hr.iter (μ := μ) (m + 1)
    obtain ⟨Cm, hCm⟩ := hrm.bdd
    unfold hs
    calc ∫ x, ∫ z, iter μ (rem k c φ) (m + 1) x z ^ 2 ∂μ ∂μ
        ≤ ∫ x, ((1 / 2) ^ ((m + 1) / n) * |c| ^ (m + 1)) ^ 2 * ∫ z, rem k c φ x z ^ 2 ∂μ ∂μ := by
          refine integral_mono
            (integrable_of_bdd (measurable_integral_right (hrm.meas.pow_const 2)) (C := Cm ^ 2)
              (fun x => abs_integral_le fun z => by
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCm x z) 2))
            ((integrable_of_bdd (measurable_integral_right (hr.meas.pow_const 2)) (C := Cr ^ 2)
              (fun x => abs_integral_le fun z => by
                rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCr x z) 2)).const_mul _)
            (fun x => ?_)
          simp only [hrow x]
          exact sq_integral_remFun_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap m (hr.row x)
            (fun y => hCr x y)
      _ = _ := by rw [integral_const_mul]

/-- One step of the floor costs at most a factor `2`: `(1/2)^⌊p/n⌋ ≤ 2 (1/2)^⌊(p+1)/n⌋` for
`n ≥ 1`, since `⌊(p+1)/n⌋ ≤ ⌊p/n⌋ + 1`.

DERIVED: `1/2` is the contraction of the gap; `2` its inverse; `1` the step and the least `n`. -/
theorem half_pow_div_le {n : ℕ} (hn : 1 ≤ n) (p : ℕ) :
    (1 / 2 : ℝ) ^ (p / n) ≤ 2 * (1 / 2) ^ ((p + 1) / n) := by
  have h1 : (p + 1) / n ≤ p / n + 1 := by
    calc (p + 1) / n ≤ (p + n) / n := Nat.div_le_div_right (by omega)
      _ = p / n + 1 := Nat.add_div_right p (by omega)
  have h2 : (1 / 2 : ℝ) ^ (p / n + 1) ≤ (1 / 2) ^ ((p + 1) / n) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
  rw [pow_succ] at h2
  linarith

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **The relative excited weight decays with the gap**:
`σ_{j+1} ≤ (1/2)^⌊j/n⌋ σ_1`, `σ_j = excited μ k c φ j`. From `hs_iter_rem_le`,
`σ_{j+1} ≤ ((1/2)^⌊j/n⌋)² σ_1`, and `(1/2)^⌊j/n⌋ ≤ 1`.

DERIVED: `1/2` is the contraction of the gap hypothesis; `1` the offset of `iter` and the one-step
weight `σ_1`; `0` the excluded eigenvalue. -/
theorem excited_succ_le (hc0 : c ≠ 0) (j : ℕ) :
    excited μ k c φ (j + 1) ≤ (1 / 2) ^ (j / n) * excited μ k c φ 1 := by
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hcne := hc.ne'
  have hB := hs_iter_rem_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap j
  unfold excited
  simp only [Nat.add_sub_cancel, Nat.sub_self]
  have hs0 : hs μ (iter μ (rem k c φ) 0) = hs μ (rem k c φ) := rfl
  rw [hs0]
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (j / n) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (j / n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hhs : 0 ≤ hs μ (rem k c φ) := hs_nonneg _
  have key : ((1 / 2) ^ (j / n) * |c| ^ j) ^ 2 * hs μ (rem k c φ)
      ≤ (1 / 2) ^ (j / n) * hs μ (rem k c φ) * (|c| ^ j) ^ 2 := by
    have hsq : ((1 / 2 : ℝ) ^ (j / n)) ^ 2 ≤ (1 / 2) ^ (j / n) := by nlinarith
    calc ((1 / 2) ^ (j / n) * |c| ^ j) ^ 2 * hs μ (rem k c φ)
        = ((1 / 2 : ℝ) ^ (j / n)) ^ 2 * (hs μ (rem k c φ) * (|c| ^ j) ^ 2) := by ring
      _ ≤ (1 / 2) ^ (j / n) * (hs μ (rem k c φ) * (|c| ^ j) ^ 2) :=
          mul_le_mul_of_nonneg_right hsq (mul_nonneg hhs (sq_nonneg _))
      _ = _ := by ring
  have eq : (1 / 2) ^ (j / n) * (hs μ (rem k c φ) / |c| ^ (2 * 1)) * |c| ^ (2 * (j + 1))
      = (1 / 2) ^ (j / n) * hs μ (rem k c φ) * (|c| ^ j) ^ 2 := by
    field_simp; ring
  rw [div_le_iff₀ (pow_pos hc _), eq]
  exact hB.trans key

include hkm hC0 hkb hsym hφ1 heig hnorm hgap in
/-- **Exponential clustering of the torus correlation, in the target form**: under the hypotheses of
`connTorus_le` and `n ≥ 1`, at time separation `t = p + 1` on the torus of time extent
`L = p + q + 2` (`L` even),

    |connTorus μ k a b p q| ≤ A B (1 + 9 σ_1) ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋),

with `σ_1 = excited μ k c φ 1 = hs(k − c φ⊗φ)/c²`, the relative Hilbert–Schmidt weight of the excited
part of one step. By `excited_succ_le` and `half_pow_div_le`, `(σ_t + σ_{L−t})/2 ≤ σ_1 S` and
`4 σ_{L/2} ≤ 8 σ_1 S`, `S` the sum of the two decaying terms; the smaller of `p`, `q` is at most
`(p+q)/2`.

DERIVED: `9 = 1 + 8` counts `σ_1 S` from the wrap-around term and `8 σ_1 S` from `4 σ_{L/2}` with
the factor `2` of `half_pow_div_le`; `1/2` is the contraction of the gap hypothesis; `1` the vacuum
term, the offset of `iter` and the least `n`; `0` the excluded eigenvalue. -/
theorem connTorus_decay (hn : 1 ≤ n) (hc0 : c ≠ 0) {a b : X → ℝ} (ham : Measurable a)
    (hbm : Measurable b) {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ)
    (hpq : Even (p + q)) :
    |connTorus μ k a b p q| ≤ A * B * (1 + 9 * excited μ k c φ 1)
      * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  have h := connTorus_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 ham hbm hab hbb p q hpq
  obtain ⟨i, hi⟩ := hpq
  have hi2 : (p + q) / 2 = i := by omega
  rw [hi2] at h
  obtain ⟨x0⟩ := nonempty_of_isProbabilityMeasure μ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hab x0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbb x0)
  have hc : 0 < |c| := abs_pos.mpr hc0
  have hσ1 : 0 ≤ excited μ k c φ 1 := div_nonneg (hs_nonneg _) (pow_pos hc _).le
  have sp := excited_succ_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 p
  have sq := excited_succ_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 q
  have si := excited_succ_le hkm hC0 hkb hsym hφm hφb hφ1 heig hnorm hgap hc0 i
  have cp := half_pow_div_le hn p
  have cq := half_pow_div_le hn q
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ (p / n) := by positivity
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (q / n) := by positivity
  have hmin : (1 / 2 : ℝ) ^ (i / n) ≤ (1 / 2) ^ (p / n) + (1 / 2) ^ (q / n) := by
    rcases le_total p i with h' | h'
    · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (Nat.div_le_div_right (c := n) h')
      linarith
    · have h'' : q ≤ i := by omega
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (Nat.div_le_div_right (c := n) h'')
      linarith
  have hS : (excited μ k c φ (p + 1) + excited μ k c φ (q + 1)) / 2
      + 4 * excited μ k c φ (i + 1)
      ≤ 9 * excited μ k c φ 1 * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
    have e1 := mul_le_mul_of_nonneg_right cp hσ1
    have e2 := mul_le_mul_of_nonneg_right cq hσ1
    have e3 := mul_le_mul_of_nonneg_right hmin hσ1
    have hx0 : 0 ≤ (1 / 2 : ℝ) ^ ((p + 1) / n) := by positivity
    have hy0 : 0 ≤ (1 / 2 : ℝ) ^ ((q + 1) / n) := by positivity
    nlinarith [mul_nonneg hx0 hσ1, mul_nonneg hy0 hσ1]
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB0
  calc |connTorus μ k a b p q| ≤ _ := h
    _ ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
          + 9 * excited μ k c φ 1 * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n))) := by
        refine mul_le_mul_of_nonneg_left ?_ hAB
        linarith
    _ = _ := by ring

end Corr

end Trace

/-! ## 3. On the Wilson torus of Theorem 4.46 -/

section Wilson

open MassGap.RectWilson MassGap.RectTransfer MassGap.DoublingRecursion MassGap.DoublingWilson

/-- **The torus partition function is the trace of the slice kernel**: on the rectangular `SU(N)`
Wilson torus with time extent `L 0 = m + 1`, `ZR L N β = trPow (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β) m`,
`Tr K^{m+1}` of the transfer kernel. It is `RectTransfer.ZR_eq_cyc` read through `trPow_eq_cyc`.

DERIVED: `0` is the time direction of the slice, the excluded rank `N ≠ 0` and the sign of the
coupling; `1` is the offset of `iter`; `4` the spacetime dimension. -/
theorem ZR_eq_trPow {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (L : Fin 4 → ℕ) (m : ℕ)
    (hL : L 0 = m + 1) :
    ZR L N β = trPow (hS 0 (tr L 0) N) (kT 0 (tr L 0) N β) m := by
  rw [ZR_eq_cyc (μ := 0) hN β, hL, trPow_eq_cyc (bdd_kT hN hβ) m]

variable {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hN hβ hn he in
/-- **Decay at every time on the Wilson torus, from the seed** (Theorem 4.46 read at every `t`). At
every even seed side `n ≥ 2` with the seed `16 log Z(n) − log Z(2n) ≤ 1/1000` at `β ≥ 0`, on the
torus `ext n (corner k)` (side `2^k · n`) for every `k`, the slice transfer operator `K` has a unit
eigenvector `ψ` with eigenvalue `c`, `|c| = ‖K‖`, and for every `t` and every `f` on `L²` of the slice,
`‖K^t f − ⟨f,ψ⟩ c^t ψ‖ ≤ (1/2)^⌊t/n⌋ ‖K‖^t ‖f‖`. It is `pow_sub_vac_le` applied to the conclusion of
`DoublingSharp.wilson_gap_sharp`, with the symmetry of `kT`
(`SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm`).

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `1/2` its contraction; `2` the doubled
side, the least seed side and the `L²` exponent; `0` the time direction of the slice and the sign of
the coupling; `1` the kernel bound and the unit norm. -/
theorem wilson_decay_sharp
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ (t : ℕ) (f : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N)),
        ‖((kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)) ^ t) f - (inner ℝ f ψ * c ^ t) • ψ‖
          ≤ (1 / 2) ^ (t / n) * ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1
            (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
            (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N)‖ ^ t * ‖f‖ := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := DoublingSharp.wilson_gap_sharp hN hβ hn he h0 k
  have hTs := fun u w => (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm
    (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (kT_symm β)).isSymmetric u w
  exact ⟨ψ, hψ1, c, hc, hKψ, fun t f => pow_sub_vac_le hTs hKψ hgap hψ1 t f⟩

include hN hβ hn he in
/-- **The connected two-slice correlation on the Wilson torus, from the seed.** At every even seed
side `n ≥ 2` with the seed of `wilson_gap_sharp` at `β ≥ 0`, on the torus `ext n (corner k)` (side
`2^k · n`, time extent `L = 2^k · n`), there are a normalized bounded eigenfunction `φ` of the slice
kernel `kT` and its eigenvalue `c ≠ 0` such that for all bounded measurable functions `a`, `b` of the
slice (`|a| ≤ A`, `|b| ≤ B`) and all `p + q + 2 = L`, at time separation `t = p + 1`,

    |connTorus a b p q| ≤ A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋ + (σ_t + σ_{L−t})/2 + 4 σ_{L/2}),

`σ_j = excited (hS …) (kT …) c φ j`. The denominator of `connTorus` is the partition function of that
torus (`ZR_eq_trPow`). The eigenfunction is the pointwise form (`exists_eigenfun`) of the eigenvector
of `wilson_gap_sharp`, whose gap `connTorus_le` uses.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `1/2` its contraction; `2` the doubled
side, the least seed side, the square, the arithmetic mean of `abs_mul_le_amgm` and the offset of
`iter` on the torus of `p + q + 2` steps; `4` the constant of `conn_alg`; `0` the time direction of
the slice, the sign of the coupling and the excluded eigenvalue; `1` the offset of `iter` and the
unit norm. -/
theorem wilson_connTorus_le
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ φ : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (ext n (corner k)) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (ext n (corner k)) 0) N β z y * φ y ∂(hS 0 (tr (ext n (corner k)) 0) N)
        = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = ext n (corner k) 0 →
        |connTorus (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) a b p q|
          ≤ A * B * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)
            + (excited (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) c φ
                (p + 1)
              + excited (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) c φ
                (q + 1)) / 2
            + 4 * excited (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) c φ
                ((p + q) / 2 + 1)) := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := DoublingSharp.wilson_gap_sharp hN hβ hn he h0 k
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 (tr (ext n (corner k)) 0)]
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, heig, hvac⟩ :=
    exists_eigenfun (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) hψ1 hc0 hKψ
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  have hev : Even (p + q) := by
    obtain ⟨n', hn'⟩ := he
    have h2 : ext n (corner k) 0 = 2 * (2 ^ k * n') := by simp only [ext, corner, hn']; ring
    rw [h2] at hpq
    generalize 2 ^ k * n' = J at hpq
    exact ⟨J - 1, by omega⟩
  refine connTorus_le (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc (fun f hf => ?_) hc0 ham hbm hab hbb p q hev
  rw [hvac] at hf
  exact hgap f hf

include hN hβ hn he in
/-- **Exponential clustering on the Wilson torus, from the seed, at every even seed side.** At every
even `n ≥ 2` with the seed `16 log Z(n) − log Z(2n) ≤ 1/1000` at `β ≥ 0`, on the torus
`ext n (corner k)` (side `2^k · n`, time extent `L = 2^k · n`), there are a normalized bounded
eigenfunction `φ` of the slice kernel `kT` and its eigenvalue `c ≠ 0` such that for all bounded
measurable functions `a`, `b` of the slice (`|a| ≤ A`, `|b| ≤ B`) and all `p + q + 2 = L`, at time
separation `t = p + 1`,

    |connTorus a b p q| ≤ A B (1 + 9 σ_1) ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋),

`σ_1 = excited (hS …) (kT …) c φ 1 = hs(kT − c φ⊗φ)/c²`. It is `connTorus_decay` with the gap of
`wilson_gap_sharp` at the eigenfunction of `exists_eigenfun`; the denominator of `connTorus` is the
partition function of the torus (`ZR_eq_trPow`). The constant `1 + 9 σ_1` depends on the torus
through `σ_1`; the rate `log 2 / n` per step does not.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `1/2` its contraction; `9` the constant
of `connTorus_decay`; `2` the doubled side, the least seed side, the square and the offset of `iter`
on the torus of `p + q + 2` steps; `0` the time direction of the slice, the sign of the coupling and
the excluded eigenvalue; `1` the offset of `iter`, the unit norm and the one-step weight `σ_1`. -/
theorem wilson_connTorus_decay
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ φ : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hS 0 (tr (ext n (corner k)) 0) N) = 1 ∧
      (∀ z, ∫ y, kT 0 (tr (ext n (corner k)) 0) N β z y * φ y ∂(hS 0 (tr (ext n (corner k)) 0) N)
        = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (ext n (corner k)) 0) → SUN.SU N) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = ext n (corner k) 0 →
        |connTorus (hS 0 (tr (ext n (corner k)) 0) N) (kT 0 (tr (ext n (corner k)) 0) N β) a b p q|
          ≤ A * B * (1 + 9 * excited (hS 0 (tr (ext n (corner k)) 0) N)
              (kT 0 (tr (ext n (corner k)) 0) N β) c φ 1)
            * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := DoublingSharp.wilson_gap_sharp hN hβ hn he h0 k
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 (tr (ext n (corner k)) 0)]
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, heig, hvac⟩ :=
    exists_eigenfun (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) hψ1 hc0 hKψ
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  have hev : Even (p + q) := by
    obtain ⟨n', hn'⟩ := he
    have h2 : ext n (corner k) 0 = 2 * (2 ^ k * n') := by simp only [ext, corner, hn']; ring
    rw [h2] at hpq
    generalize 2 ^ k * n' = J at hpq
    exact ⟨J - 1, by omega⟩
  refine connTorus_decay (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ) (kT_symm β)
    hφm hφb hφ1 heig hc (fun f hf => ?_) (by omega) hc0 ham hbm hab hbb p q hev
  rw [hvac] at hf
  exact hgap f hf

include hN hβ hn he in
/-- **Uniform exponential clustering of the transfer state on the Wilson torus, from the seed.** At
every even seed side `n ≥ 2` with the seed `16 log Z(n) − log Z(2n) ≤ 1/1000` at `β ≥ 0`, on the
torus `ext n (corner k)` (side `2^k · n`) for every `k`, the slice transfer operator `K` has a unit
eigenvector `ψ` with eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and for every `t` and all `u`, `w` on `L²` of
the slice,

    |⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/n) t} ‖u‖ ‖w‖.

The constant `2` and the rate `log 2/n` do not depend on `k`, on the coupling or on `u`, `w`: the
bound is uniform in the torus size. It is `inner_pow_div_sub_le` and `half_pow_div_le_exp` at the gap
of `DoublingSharp.wilson_gap_sharp`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the inverse of its contraction
`1/2` (the logarithm of which is the rate), the doubled side, the least seed side and the `L²`
exponent; `0` the time direction of the slice, the sign of the coupling and the excluded eigenvalue;
`1` the kernel bound and the unit norm. -/
theorem wilson_cluster_uniform
    (h0 : 16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1
          (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
          (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
          (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (hS 0 (tr (ext n (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hS 0 (tr (ext n (corner k)) 0) N)),
        |inner ℝ u (((kernelCLM (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N)
          (hS 0 (tr (ext n (corner k)) 0) N)) ^ t) w) / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := DoublingSharp.wilson_gap_sharp hN hβ hn he h0 k
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_pos hN hβ 0 (tr (ext n (corner k)) 0)]
  have hTs := fun u w => (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm
    (kT 0 (tr (ext n (corner k)) 0) N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le hN hβ) (hS 0 (tr (ext n (corner k)) 0) N) (kT_symm β)).isSymmetric u w
  refine ⟨ψ, hψ1, c, hc0, hc, hKψ, fun t u w => ?_⟩
  have h1 := inner_pow_div_sub_le hTs hKψ hgap hψ1 hc hc0 t u w
  have h2 := half_pow_div_le_exp (n := n) (by omega) t
  calc _ ≤ _ := h1
    _ ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
        gcongr


/-- **Uniform exponential clustering along a family of tori, in physical units** (Theorem 4.46 read
as clustering). Under the hypotheses of `OpenAIDictionary.familyGap_of_seed` (couplings `β m p` in the
normalization of the OpenAI construction, base sides `n m` eventually even, at least `2`, with the
seed at `(n m, β m p / 2)` for every `p`), and spacings `a m > 0` with `n m · a m ≤ ℓ`: for all large
`m`, all `p` and all `k`, the transfer operator `K` of the torus `ext (n m) (corner k)` at coupling
`β m p / 2` has a unit eigenvector `ψ`, eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and for every lag `t` and
all `u`, `w`,

    |⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/ℓ) · t a_m} ‖u‖ ‖w‖,

at physical separation `τ = t a_m`. The constant `2` and the rate `log 2/ℓ` are uniform in the
spacing index `m`, the volume index `p` and the dyadic depth `k`: the form `hB` of
`OpenAIBridgeLimits.norm_le_exp_of_iterated_subsequences` reads, with `C = 2 ‖u‖ ‖w‖`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the inverse of its contraction
(the logarithm of which is the rate), the halving of the coupling (`action_eq_two_mul_wilsonEnergy`),
the doubled side, the least seed side and the `L²` exponent; `0` the signs and the time direction of
the slice; `1` the kernel bound and the unit norm. -/
theorem familyCluster_of_seed {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ)
    (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      16 * Real.log (ZR (fun _ => n m) N (β m p / 2))
        - Real.log (ZR (fun _ => 2 * n m) N (β m p / 2)) ≤ 1 / 1000)
    (a : ℕ → ℝ) {ℓ : ℝ} (ha : ∀ m, 0 < a m) (hℓ : ∀ m, (n m : ℝ) * a m ≤ ℓ) :
    ∀ᶠ m in Filter.atTop, ∀ p k,
    ∃ ψ : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) N), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N)‖ ∧
      kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N) ψ
        = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hS 0 (tr (ext (n m) (corner k)) 0) N)),
        |inner ℝ u (((kernelCLM (kT 0 (tr (ext (n m) (corner k)) 0) N (β m p / 2)) 1
          (continuous_kT (β m p / 2)).measurable zero_le_one
          (abs_kT_le hN (div_nonneg (hβ m p) zero_le_two))
          (hS 0 (tr (ext (n m) (corner k)) 0) N) (hS 0 (tr (ext (n m) (corner k)) 0) N)) ^ t) w)
            / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / ℓ) * (t * a m)) * ‖u‖ * ‖w‖ := by
  filter_upwards [hfam] with m hm p k
  obtain ⟨hn, he, h0⟩ := hm
  obtain ⟨ψ, hψ1, c, hc0, hc, hKψ, hcl⟩ :=
    wilson_cluster_uniform hN (div_nonneg (hβ m p) zero_le_two) hn he (h0 p) k
  refine ⟨ψ, hψ1, c, hc0, hc, hKψ, fun t u w => (hcl t u w).trans ?_⟩
  have hn1 : 1 ≤ n m := by omega
  have hr := OpenAIDictionary.physRate_le hn1 (ha m) (hℓ m)
  have hn0 : (0 : ℝ) < n m := by exact_mod_cast hn1
  have hrate : Real.log 2 / ℓ * (t * a m) ≤ Real.log 2 / n m * t := by
    have ht : (0 : ℝ) ≤ t * a m := mul_nonneg (Nat.cast_nonneg t) (ha m).le
    calc Real.log 2 / ℓ * (t * a m) ≤ Real.log 2 / (n m * a m) * (t * a m) :=
          mul_le_mul_of_nonneg_right hr ht
      _ = Real.log 2 / n m * t := by field_simp [(ha m).ne', hn0.ne']
  have hexp : Real.exp (-(Real.log 2 / n m) * t) ≤ Real.exp (-(Real.log 2 / ℓ) * (t * a m)) := by
    rw [Real.exp_le_exp]; linarith
  gcongr

end Wilson

end MassGap.OpenAIBridgeCluster
