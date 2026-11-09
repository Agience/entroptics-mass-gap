import Mathlib
import MassGap.BareRatioProof

/-!
# MassGap.ApertureSpectral — the long lags of the bare correlator peak at zero momentum

`ApertureFinite.BareRatio` (the heat screen's bounded Rényi-½ count) reduces, through
`BareRatioProof.bareRatio_of_lowMode`, to `LowModeRatio`: the operator norm `c` of the bare covariance on the
screen box within a fixed factor of the lowest Dirichlet-mode variance `v₀`. `BareRatioProof` reaches it from
`RelSum` (signs and relative summability). This module proves, for a finite spectral mixture in one direction, that the long lags peak at zero momentum
and keep half the peak on the gap window,
proves that a fixed physical screen side puts the lowest Dirichlet momentum inside the gap window along the
tower, and isolates the inequality that remains. Declarations are in the namespace `MassGap.ApertureSpectral`.

## 1. The Poisson kernel (proved)

`kerP E p = sinh E / (cosh E − cos p)`, the closed form of `∑_{n ∈ ℤ} λ^{|n|} cos(pn)` at `λ = e^{−E}` (the
closed form is classical and not formalized here). `cosh_sub_one_ge`: `E²/2 ≤ cosh E − 1` for `E ≥ 0`
(`cosh E = 1 + 2 sinh²(E/2)`, `sinh y ≥ y`). `cosh_sub_cos_le`: `cosh E − cos p ≤ 2 (cosh E − 1)` when
`p² ≤ E²` (`1 − cos p ≤ p²/2`). `kerP_le`: `kerP E p ≤ kerP E 0`. `kerP_half`: `kerP E 0 ≤ 2 kerP E p` when
`p² ≤ E²`; the ratio `(cosh E − 1)/(cosh E − cos p)` is at least `1/2` on the window.

## 2. Positive mixtures (proved)

`mix w E p = ∑_i w_i kerP(E_i, p)`. `mix_le`: for `w ≥ 0`, `E > 0`, the mixture peaks at `p = 0`.
`mix_half`: if every `E_i ≥ m > 0` (the spectral support of the transfer operator off the vacuum lies in
`[0, e^{−m}]`) and `p² ≤ m²`, then `mix(0) ≤ 2 mix(p)`. This is step 2 of the route for a finite spectral sum.

## 3. The window along the tower (proved)

`lowFreq_le`: the lowest Dirichlet lattice momentum of the screen box, `π/(L_k + 1)`, is at most `π a_k / ρ`.
`lowFreq_le_gap`: along `MeasuredTower.schedAlongG`, where `a_k = aRunG(1) / 2^{k+1}`, a lattice-unit gap
`m_k ≥ log 2 / 2^k` (the rate of `CouplingTower.observerGap_along`) and a screen side `ρ` with
`π aRunG(1) ≤ 2 log 2 · ρ` give `π/(L_k + 1) ≤ m_k` at every step. One fixed physical `ρ` serves the whole
tower; the heat time `θ` does not enter, because `BareRatioProof` keeps only the lowest heat mode.

## 4. What these give, and what they do not

Together §2 and §3 prove the long-lag half of `LowModeRatio` for a finite spectral sum in one direction: the
lowest Dirichlet mode keeps at least half the long-lag peak. No theorem here combines them with the short lags;
the combination is `LowModeRatio` itself, and stating it as a split of `c` into a long-lag and a short-lag part
would restate it.

## 5. The paper check of the route

Argued, not formalized.

* Step 1 (spectral form). `PeriodicContent.PeriodicClayGapAt` carries a self-adjoint transfer operator with
  spectrum in `{1} ∪ [0, r]`, so on that data the lag correlator of a half-space vector is a positive mixture
  `∫ λ^n dσ`, `σ` on `[0, r]` (spectral theorem; not in the tree as a measure). Along the tower the tree has the
  gap only as the contraction form `TransferGap.GapAt` of the flowed transfer (`CouplingTower.observerGap_along`),
  not on the bare plaquette's GNS space. For the bare reading, `PlaqPositive` gives positivity and log-convexity
  at lags `≥ 2D` (`lag_nonneg_of_both`, `lag_logConvex`). A numerical check of log-convex profiles with every
  ratio at most `e^{−m}` (piecewise geometric, `2 · 10⁴` samples) found `f(p)/f(0) ≥ 1/2` on `|p| ≤ m`, with the
  pure geometric profile extremal; so the contraction bound with log-convexity appears to suffice for §2's
  conclusion, but that is not proved.
* Step 2 holds in one direction at one transverse momentum (§2). In four dimensions the per-direction form is
  `Ĉ(p_μ, p⊥) = s_{p⊥}(p_μ) + t_{p⊥}(p_μ)` with `t` the long lags (`|n| ≥ 2D`, positive, peaking at `p_μ = 0`) and
  `s` the short lags `∑_{|n|<2D} Γ_{p⊥}(n) e^{i p_μ n}`. The coefficients `Γ_{p⊥}(n)` are transverse slice
  densities: `|Γ_{p⊥}(n)| ≤ Γ_{p⊥}(0)` (Bochner), and `Γ_{p⊥}(0)` is the three-dimensional symbol of the lag-0
  slice, not a multiple of `C(0)`. Iterating over the four directions gives
  `sup Ĉ ≤ ∑_{J} K^{|J|} S_J`, with `S_J` the zero-momentum sum of `C` over the sublattice transverse to `J`
  (`S_∅ = Ĉ(0)`, `S_{all} = C(0)`). The intermediate `S_J` (line, plane and slice susceptibilities) are the
  remainder `σ`.
* Step 3 holds (§3).
* Step 4. Only `S_{all} = C(0)` is local. `σ ≤ κ v₀` needs every `S_J ≤ K v₀`. The floor of `PlaqShortDistance`
  bounds `v₀` below by one-link conditional variances, so with the per-link floor `C(0) ≤ κ ν(cv_l A_l)` the
  local term closes. The slice terms do not: comparing `S_{J ∪ {μ}}` (lag-0 slice) with `S_J` (lag-summed) needs
  `Γ(0) + 2 Γ(1) ≥ κ Γ(0)` for the slice-summed profile, the non-cancellation of the overlap lag for the slice
  sums of every dimension (the `PlaqPositive` §8 profile `Γ(0) = 1`, `Γ(±1) = −1/2` is the failing case). With
  the floor this is `S_J ≤ K ν(cv_l A_l)`: a slice susceptibility bounded by a local scale. The transfer gap
  gives only `S_J ≤ C(0) · O(m_k^{−(4−|J|)})`, growing like `2^{(4−|J|)k}`.
* In one direction alone (on-axis profile, transverse sublattice a point) the remainder is `C(0)`, `C(e_μ)` and
  the route closes from the local inequalities.

## What does not follow

* `BareRatio` and `LowModeRatio` are not proved along any tower; nothing here moves them onto a weaker statement.
* The missing inequality is `σ ≤ κ v₀`: the sums `S_J` of the bare correlator over the line, plane and
  three-dimensional sublattices (at lag `0` in the remaining directions) are at most a fixed multiple of the
  lowest-mode variance, eventually along the tower. It is multiscale: `S_J` integrates the transverse correlator
  over all separations up to the correlation length `1/m_k`, and the gap controls only the decay beyond it. The
  local part (`C(0)` against the one-link conditional variance) is the per-link floor, also not proved.
* The infinite-volume spectral form, the Toeplitz bound `‖C_box‖ ≤ sup Ĉ` and the transfer of §2 from a finite
  spectral sum to a spectral measure are not in the tree. §2 is proved for finite mixtures only.
* The closed form `kerP = ∑ λ^{|n|} cos(pn)` is not formalized.
* `θ` is not fixed by this module; any `θ > 0` serves in §4.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the signs and zero momentum; `1` the vacuum value `cosh 0`, `cos 0` and the Dirichlet
shift `L + 1`; `2` the squares, the half angle `E/2`, the halving of the window ratio (`kerP_half`) and the factor
`2^{k+1} = 2 · 2^k`; `3 = 1 + 2` COMPUTED, the remainder's weight in `2 + 3κ` (`σ` once from `c ≤ t + σ`, twice
from `t ≤ 2(v₀ + σ)`); `4` the spacetime dimension; `π` the Dirichlet frequency; `log 2` Inherited from the
rate of `CouplingTower.observerGap_along`. `2 · 10⁴` COMPUTED, the sample size of the argued check in §5.
`κ`, `ρ`, `m`, `c`, `t`, `σ` hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApertureSpectral

open Finset Filter
open scoped Real
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ClayTreeG MassGap.CountMoments
open MassGap.ApertureFinite MassGap.BareRatioProof
open MassGap.ApertureCount (spRenyi eig)

/-! ## 1. The Poisson kernel -/

/-- **The curvature of `cosh`**: `E²/2 ≤ cosh E − 1` for `E ≥ 0`, from `cosh E = 1 + 2 sinh²(E/2)` and
`sinh y ≥ y`. DERIVED: `2` the square and the half angle; `1` `cosh 0`. -/
theorem cosh_sub_one_ge {E : ℝ} (hE : 0 ≤ E) : E ^ 2 / 2 ≤ Real.cosh E - 1 := by
  have h := Real.cosh_two_mul (E / 2)
  rw [show 2 * (E / 2) = E by ring, Real.cosh_sq'] at h
  have hs : E / 2 ≤ Real.sinh (E / 2) := Real.self_le_sinh_iff.2 (by linarith)
  have hs2 : (E / 2) ^ 2 ≤ Real.sinh (E / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hs 2
  nlinarith

/-- **The window denominator**: `cosh E − cos p ≤ 2 (cosh E − 1)` when `p² ≤ E²`, `E ≥ 0`.
DERIVED: `2` the square and the doubling; `1` `cos 0`. -/
theorem cosh_sub_cos_le {E p : ℝ} (hE : 0 ≤ E) (hp : p ^ 2 ≤ E ^ 2) :
    Real.cosh E - Real.cos p ≤ 2 * (Real.cosh E - 1) := by
  have h1 : 1 - p ^ 2 / 2 ≤ Real.cos p := Real.one_sub_sq_div_two_le_cos
  have h2 := cosh_sub_one_ge hE
  linarith

/-- DERIVED: `0` the sign; `1` `cosh 0`. -/
theorem cosh_sub_cos_pos {E : ℝ} (hE : E ≠ 0) (p : ℝ) : 0 < Real.cosh E - Real.cos p := by
  have h1 := Real.one_lt_cosh.2 hE
  have h2 := Real.cos_le_one p
  linarith

/-- **The Poisson kernel** `sinh E / (cosh E − cos p)`, the momentum profile of the lag sequence
`e^{−E |n|}`. DERIVED: no numeral. -/
def kerP (E p : ℝ) : ℝ := Real.sinh E / (Real.cosh E - Real.cos p)

/-- **The Poisson kernel peaks at zero momentum**. DERIVED: `0` the momentum and the sign; `1` `cos 0`. -/
theorem kerP_le {E : ℝ} (hE : 0 < E) (p : ℝ) : kerP E p ≤ kerP E 0 := by
  unfold kerP
  rw [Real.cos_zero]
  exact div_le_div_of_nonneg_left (Real.sinh_pos_iff.2 hE).le
    (sub_pos.2 (Real.one_lt_cosh.2 hE.ne')) (by linarith [Real.cos_le_one p])

/-- **The Poisson kernel keeps half its peak on the window** `p² ≤ E²`.
DERIVED: `2` the halving and the square; `0` the momentum and the signs; `1` `cos 0`. -/
theorem kerP_half {E p : ℝ} (hE : 0 < E) (hp : p ^ 2 ≤ E ^ 2) : kerP E 0 ≤ 2 * kerP E p := by
  unfold kerP
  rw [Real.cos_zero]
  have hb := cosh_sub_cos_pos hE.ne' p
  have hc := cosh_sub_cos_le hE.le hp
  have hs := (Real.sinh_pos_iff.2 hE).le
  have heq : 2 * (Real.sinh E / (Real.cosh E - Real.cos p))
      = Real.sinh E / ((Real.cosh E - Real.cos p) / 2) := by
    rw [div_div_eq_mul_div]; ring
  rw [heq]
  exact div_le_div_of_nonneg_left hs (by linarith) (by linarith)

#print axioms cosh_sub_one_ge
#print axioms cosh_sub_cos_le
#print axioms cosh_sub_cos_pos
#print axioms kerP_le
#print axioms kerP_half

/-! ## 2. Positive mixtures -/

section Mixture

variable {ι : Type*} [Fintype ι]

/-- **A positive spectral mixture of Poisson kernels**. DERIVED: no numeral. -/
def mix (w E : ι → ℝ) (p : ℝ) : ℝ := ∑ i, w i * kerP (E i) p

/-- **A positive mixture peaks at zero momentum**. DERIVED: `0` the momentum and the signs. -/
theorem mix_le (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hE : ∀ i, 0 < E i) (p : ℝ) : mix w E p ≤ mix w E 0 :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (kerP_le (hE i) p) (hw i)

/-- **A gapped positive mixture keeps half its peak on the gap window**: every `E_i ≥ m > 0` and `p² ≤ m²`
give `mix(0) ≤ 2 mix(p)`. DERIVED: `2` the halving and the square; `0` the momentum and the signs. -/
theorem mix_half (w E : ι → ℝ) {m p : ℝ} (hm : 0 < m) (hw : ∀ i, 0 ≤ w i) (hE : ∀ i, m ≤ E i)
    (hp : p ^ 2 ≤ m ^ 2) : mix w E 0 ≤ 2 * mix w E p := by
  unfold mix
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hEi : 0 < E i := hm.trans_le (hE i)
  have hpE : p ^ 2 ≤ E i ^ 2 := hp.trans (pow_le_pow_left₀ hm.le (hE i) 2)
  calc w i * kerP (E i) 0 ≤ w i * (2 * kerP (E i) p) :=
        mul_le_mul_of_nonneg_left (kerP_half hEi hpE) (hw i)
    _ = 2 * (w i * kerP (E i) p) := by ring

end Mixture

#print axioms mix_le
#print axioms mix_half

/-! ## 3. The window along the tower -/

section Window

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The lowest Dirichlet momentum of the screen box** `π/(L_k + 1) ≤ π a_k / ρ`.
DERIVED: `1` the Dirichlet shift; `0` the signs; `π` the Dirichlet frequency. -/
theorem lowFreq_le (S : Sched G) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    π / ((scrSide S ρ k : ℝ) + 1) ≤ π * S.a k / ρ := by
  have ha := S.a_pos k
  have hq : 0 < ρ / S.a k := div_pos hρ ha
  have hL : ρ / S.a k ≤ (scrSide S ρ k : ℝ) + 1 := by
    have := Nat.le_ceil (ρ / S.a k)
    unfold scrSide
    linarith
  calc π / ((scrSide S ρ k : ℝ) + 1) ≤ π / (ρ / S.a k) :=
        div_le_div_of_nonneg_left Real.pi_pos.le hq hL
    _ = π * S.a k / ρ := by rw [div_div_eq_mul_div]

/-- **One physical screen side puts the lowest Dirichlet momentum inside the gap window at every step**:
along `schedAlongG`, a lattice-unit gap `m ≥ log 2 / 2^k` and `π aRunG(1) ≤ 2 log 2 · ρ` give
`π/(L_k + 1) ≤ m`. DERIVED: `1` the reference coupling and the Dirichlet shift; `2` the factor
`2^{k+1} = 2 · 2^k`; `0` the signs. Inherited: `log 2` the rate of `CouplingTower.observerGap_along`. -/
theorem lowFreq_le_gap [GaugeSimple G] (βs : ℕ → ℝ) {ρ m : ℝ} (hρ : 0 < ρ) (k : ℕ)
    (hm : Real.log 2 / 2 ^ k ≤ m)
    (hside : π * GaugeRunning.aRunG G 1 ≤ 2 * Real.log 2 * ρ) :
    π / ((scrSide (MeasuredTower.schedAlongG G βs) ρ k : ℝ) + 1) ≤ m := by
  refine (lowFreq_le (MeasuredTower.schedAlongG G βs) hρ k).trans (le_trans ?_ hm)
  change π * (GaugeRunning.aRunG G 1 / 2 ^ (k + 1)) / ρ ≤ Real.log 2 / 2 ^ k
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_le_div_iff₀ hρ hk, pow_succ]
  have heq : π * (GaugeRunning.aRunG G 1 / (2 ^ k * 2)) * 2 ^ k = π * GaugeRunning.aRunG G 1 / 2 := by
    field_simp
  rw [heq]
  linarith

end Window

#print axioms lowFreq_le
#print axioms lowFreq_le_gap


end MassGap.ApertureSpectral

end
