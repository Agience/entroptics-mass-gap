import Mathlib
import MassGap.UVIRSplit
import MassGap.FloorRead
import MassGap.SpectralRep
import MassGap.GNSCompare

noncomputable section

/-!
# MassGap.ZoomStep — the Entroptic zoom as the renormalisation step, and the leftover past the aperture

## The Entroptic statements, reproduced

The MassGap Lake package requires `mathlib` alone (`research/lean/lakefile.lean`,
`research/lean/lake-manifest.json`), and no MassGap file imports `Entroptics.*`. Section 1 therefore
reproduces, with their proofs, the three block-repeat statements of the module
`Entroptics.Diffraction` (`entroptics` repository, `research/lean/Entroptics/Diffraction.lean`,
Proposition 4.5, declared in namespace `Entroptics`), with identical binders and conclusions, at the
same Mathlib pin: `entropy_block_repeat`, `integral_length_block_repeat` and
`gabor_product_scale_invariant`. Block repetition by `s` sends a profile `f : Fin n → ℝ` to
`f' : Fin (n * s) → ℝ` with `f' (s·i + k) = f i`; the integral length `ξ = ∑ f` becomes `s · ξ`, and
with the mass split equally the Gabor product `ξ · e^{−H}` is unchanged.

## What it gives

1. **Sequences at `s = 2`.** `sum_blockRepeat`: `f' (2i) = f' (2i + 1) = f i` gives
   `∑_{j < 2n} f' j = 2 ∑_{i < n} f i`, from `integral_length_block_repeat`. With only the even lags
   matched, `f' (2i) = f i`, and `f'` antitone, `le_sum_evenRepeat` and `sum_evenRepeat_le` bracket
   the fine sum between `2 ∑ f − (f 0 − f n)` and `2 ∑ f`.
2. **Profiles on transfer data.** `ratioProfile D x n = D.form x (Tⁿ x) / D.form x x` is the
   Entroptic ratio profile `C(n)/C(0)` of the reflected pairing (`ChessboardRead.lagProfile`). Under
   `GNSHilbert.PositiveTransfer` the profile is antitone (`lagProfile_succ_le`). `LagRatio D n q`:
   every vacuum-orthogonal observable has profile at lag `n` at most `q` times its lag-zero value.
   `EnvelopeAt D r` is `LagRatio` at `rⁿ` at every lag; `EvenEnvelopeAt D r` asks it at the even
   lags only. Under `PositiveTransfer D` and `0 ≤ r` both are `TransferGap.GapAt D r`
   (`envelopeAt_iff_gapAt`, `evenEnvelopeAt_iff_gapAt`): the odd lags follow from the even ones.
3. **The zoom on profiles.** `ZoomRepeat D D'`: every envelope `q` of the coarse profile at lag `d`
   is an envelope of the fine profile at lag `2d`. `EvenRepeat D D' B`: the per-observable Entroptic
   repeat on the even fine lags, `ratioProfile D' x (2d) = ratioProfile D (B x) d`, through a map
   `B` of fine observables to coarse ones (`B = id` allowed). `zoomRepeat_of_evenRepeat`.
   `gapAt_sqrt_of_zoomRepeat`: under `PositiveTransfer D'` and `0 ≤ r`, `ZoomRepeat` and the lag-one
   envelope `r` at `D` give `GapAt D' (√r)`.
4. **The exact repeat and the gap.** `LiteralRepeat` adds the odd fine lags,
   `ratioProfile D' x (2d + 1) = ratioProfile D (B x) d`. At `d = 0` it reads
   `ratioProfile D' x 1 = 1`, and `literalRepeat_no_gap`: on a vacuum-orthogonal `x` with
   `0 < D'.form x x` it excludes `GapAt D' r` at every `0 ≤ r < 1` (`not_gapAt_of_ratio_one`). The
   odd lags of a gapped fine profile interpolate between the even ones; `integralLength_even_bounds`
   is the integral length under `EvenRepeat`, `integralLength_literal` the exact doubling under
   `LiteralRepeat`.
5. **At the periodic state.** `physStep_of_zoomRepeat`: at `0 ≤ β'` and halved spacing, `ZoomRepeat`
   from `β` to `β'` gives `GapStep.PhysStep τ p hN β β' M` at every `M`; `physStep_iff_evenZoom`,
   `physStep_iff_envelope_zoom`: at `0 ≤ β` and `0 ≤ β'`, `PhysStep` is exactly the even-lag zoom of
   the geometric envelope at the one rate `e^{−M·aRun N β}` — the decay-rate part of the repeat, not
   the whole profile.
   `zoom_keeps_physical_rate` (the physical rate `−log r / a` is unchanged),
   `physLength_literal`, `physLength_even_bounds` (the physical integral length `a·ξ`), and
   `periodic_clay_tower_of_evenRepeat` (one physical gap along a halving sequence).
6. **The Wilson hypothesis.** `ZoomInvariantWith τ p hN βUV ε`: for every two couplings above `βUV`
   one block step apart and every `M`, the coarse envelope at rate `e^{−M·a}` gives the fine
   envelope at the even lags at rate `e^{−(M − ε(a))·a'}`; at exact halving that is the fine profile
   at lag `2d` bounded by the coarse envelope at lag `d`, less the loss
   (`evenEnvelopeAt_half_iff`). `zoomInvariantWith_iff_uvLossStep`: at `0 ≤ βUV` it is
   `UVIRSplit.UVLossStep`. `ZoomInvariant τ p hN` packages it with `UVIRSplit.VanishingLoss`;
   `zoomInvariant_iff_uvInput`. `fixedWindowDecay_of_zoom`, `fixedWindowDecay_of_zoom_zero`: with
   `UVIRSplit.IRGapAt` at one coupling, `WeakCouplingWindow.FixedWindowDecay`
   (`UVIRSplit.fixedWindowDecay_of_uv_ir`).
7. **The leftover past the aperture.** `specMeasure a ha v` is the Riesz–Markov spectral measure of
   `v` (the measure of `SpectralRep.exists_spectral_measure`); `outWeight a ha v s` its weight on
   `(s, 1]`; `LeftoverNull a ha Ω s`: every vector orthogonal to `Ω` has no weight there.
   `contraction_iff_leftoverNull`, `gapAt_iff_leftoverNull`: the contraction, and `GapAt` at rate
   `s`, is `LeftoverNull` at `s`. `readEdge k γ = sup {r ≥ 0 | γ ≤ modeCosAvg k r}` is the edge of the
   aperture `2k + 1` at margin `γ` (`isEdge_readEdge`), and `readsClearWith_iff_leftoverNull`,
   `torusReads_iff_leftoverNull`: the margin read at `(k, γ)` holds exactly when the weight past the
   edge vanishes. `LeftoverInvariant τ p hN L`: at every large `β`, with the window held at physical
   size `L`, the leftover past the window's diffraction rate `q^{1/m}` vanishes;
   `leftoverInvariant_iff_fixedWindowDecay`. `leftoverInvariant_of_zoom` and
   `physStep_eventually_of_leftoverInvariant` relate it to the zoom.

## The open dynamical content

The tree proves each identification above; it proves none of the following inputs at weak coupling.

* `ZoomInvariantWith τ p hN βUV ε` with `UVIRSplit.VanishingLoss ε` (packaged: `ZoomInvariant τ p hN`),
  equivalently `UVIRSplit.UVInput τ p hN`: the signal, read as the decay envelope of the connected
  reflected profile over a fixed physical separation, survives each block step with a summable loss.
* `UVIRSplit.IRGapAt τ p hN β₀ M₀` at one coupling `β₀ ≥ βUV` past the strong-coupling region, with
  `M₀` above the loss budget below `aRun N β₀`.
* Together, and equivalently to them under the first: `LeftoverInvariant τ p hN L`, which is
  `WeakCouplingWindow.FixedWindowDecay τ p hN L`.

`EvenRepeat` and `ZoomRepeat` along every exact halving are sufficient forms of the first input on the
dyadic sequence (`periodic_clay_tower_of_evenRepeat`); the partial steps between dyadic spacings are
part of `ZoomInvariantWith`. `LiteralRepeat`, the Entroptic identity taken verbatim, excludes every
gap `GapAt D' r`, `0 ≤ r < 1`, at the finer coupling as soon as the fine data has one non-null
vacuum-orthogonal observable (`literalRepeat_no_gap`).
-/

namespace MassGap.ZoomStep

open MeasureTheory MassGap MassGap.Transfer MassGap.GNSHilbert

/-! ## 1. The Entroptic block repeat, reproduced from `Entroptics.Diffraction` -/

section Entroptic

/-- **Proposition 4.5, entropy step** (reproduced from `Entroptics.entropy_block_repeat` in
`entroptics/research/lean/Entroptics/Diffraction.lean`). If `q' : Fin (n*s) → ℝ` is `q`
block-repeated `s ≥ 1` times with each mass split equally (`q' (s·i + k) = q i / s`), then the
natural-log Shannon entropy gains exactly `log s`: `H q' = H q + log s`.

DERIVED: `0` is the excluded block factor; `1` is the total mass of `q`. -/
theorem entropy_block_repeat {n s : ℕ} (hs : 0 < s)
    (q : Fin n → ℝ) (hsum : ∑ i, q i = 1)
    (q' : Fin (n * s) → ℝ)
    (hq' : ∀ (i : Fin n) (k : Fin s), q' (finProdFinEquiv (i, k)) = q i / (s : ℝ)) :
    (∑ j, Real.negMulLog (q' j)) = (∑ i, Real.negMulLog (q i)) + Real.log s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
  rw [← Equiv.sum_comp finProdFinEquiv (fun j => Real.negMulLog (q' j)), Fintype.sum_prod_type]
  have hterm : ∀ i : Fin n,
      (∑ k : Fin s, Real.negMulLog (q' (finProdFinEquiv (i, k))))
        = Real.negMulLog (q i) + q i * Real.log s := by
    intro i
    have hnml : Real.negMulLog (q i / (s : ℝ))
        = (s : ℝ)⁻¹ * Real.negMulLog (q i) + q i * ((s : ℝ)⁻¹ * Real.log s) := by
      rw [div_eq_mul_inv, Real.negMulLog_mul]
      congr 1
      rw [show Real.negMulLog ((s : ℝ)⁻¹) = -(s : ℝ)⁻¹ * Real.log ((s : ℝ)⁻¹) from rfl,
        Real.log_inv]; ring
    rw [Finset.sum_congr rfl (fun k _ => by rw [hq' i k]), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hnml]
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.sum_mul,
    hsum, one_mul]

#print axioms entropy_block_repeat

/-- **Proposition 4.5, integral-length step** (reproduced from
`Entroptics.integral_length_block_repeat` in module `Entroptics.Diffraction`). If `f'` is the ratio profile `f`
block-repeated `s` times (`f' (s·i + k) = f i`), then `∑ f' = s · ∑ f`.

DERIVED: no numeral occurs. -/
theorem integral_length_block_repeat {n s : ℕ}
    (f : Fin n → ℝ) (f' : Fin (n * s) → ℝ)
    (hf' : ∀ (i : Fin n) (k : Fin s), f' (finProdFinEquiv (i, k)) = f i) :
    (∑ j, f' j) = (s : ℝ) * ∑ i, f i := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun j => f' j), Fintype.sum_prod_type]
  have hterm : ∀ i : Fin n, (∑ k : Fin s, f' (finProdFinEquiv (i, k))) = (s : ℝ) * f i := by
    intro i
    rw [Finset.sum_congr rfl (fun k _ => hf' i k), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]

#print axioms integral_length_block_repeat

/-- **Proposition 4.5: the Gabor product is exactly scale-invariant** (reproduced from
`Entroptics.gabor_product_scale_invariant` in module `Entroptics.Diffraction`). With `a_δ = exp(−H)` and `ξ = ∑ f`, the
product `ξ · a_δ` is unchanged under block repetition by `s ≥ 1` with the mass split equally:
`ξ' · a_δ' = (s·ξ)·(a_δ / s) = ξ · a_δ`.

DERIVED: `0` is the excluded block factor; `1` is the total mass of `q`. -/
theorem gabor_product_scale_invariant {n s : ℕ} (hs : 0 < s)
    (q : Fin n → ℝ) (hsum : ∑ i, q i = 1)
    (q' : Fin (n * s) → ℝ)
    (hq' : ∀ (i : Fin n) (k : Fin s), q' (finProdFinEquiv (i, k)) = q i / (s : ℝ))
    (f : Fin n → ℝ) (f' : Fin (n * s) → ℝ)
    (hf' : ∀ (i : Fin n) (k : Fin s), f' (finProdFinEquiv (i, k)) = f i) :
    (∑ j, f' j) * Real.exp (-(∑ j, Real.negMulLog (q' j)))
      = (∑ i, f i) * Real.exp (-(∑ i, Real.negMulLog (q i))) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs0
  have hlog : Real.exp (-Real.log s) = (s : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hs0]
  rw [entropy_block_repeat hs q hsum q' hq', integral_length_block_repeat f f' hf',
    neg_add, Real.exp_add, hlog]
  field_simp

#print axioms gabor_product_scale_invariant

/-- **The Gabor product of a profile, at block factor `2`.** For a profile `f : Fin n → ℝ` with
`∑ f ≠ 0` and its block repeat `f'` by `2`, the mass distributions `f / ∑ f` and `f' / ∑ f'` split
equally (`integral_length_block_repeat`), and `gabor_product_scale_invariant` gives
`(∑ f')·e^{−H(f'/∑ f')} = (∑ f)·e^{−H(f/∑ f)}`.

DERIVED: `2` is the block factor, the halving of `GapStep.physStep_iff_lag`; `0` is the excluded total. -/
theorem gabor_blockRepeat_two {n : ℕ} (f : Fin n → ℝ) (f' : Fin (n * 2) → ℝ)
    (hf' : ∀ (i : Fin n) (k : Fin 2), f' (finProdFinEquiv (i, k)) = f i) (hS : ∑ i, f i ≠ 0) :
    (∑ j, f' j) * Real.exp (-(∑ j, Real.negMulLog (f' j / ∑ j', f' j')))
      = (∑ i, f i) * Real.exp (-(∑ i, Real.negMulLog (f i / ∑ i', f i'))) := by
  have hlen := integral_length_block_repeat f f' hf'
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  refine gabor_product_scale_invariant (n := n) (s := 2) (by norm_num)
    (fun i => f i / ∑ i', f i') ?_ (fun j => f' j / ∑ j', f' j') ?_ f f' hf'
  · show ∑ i, f i / ∑ i', f i' = 1
    rw [← Finset.sum_div, div_self hS]
  · intro i k
    show f' (finProdFinEquiv (i, k)) / ∑ j', f' j' = (f i / ∑ i', f i') / ((2 : ℕ) : ℝ)
    rw [hf' i k, hlen, h2]
    ring

#print axioms gabor_blockRepeat_two

end Entroptic

/-! ## 2. Sequences at block factor `2` -/

section Sequence

/-- The block repeat by `2` on `ℕ`-indexed profiles, read on `Fin`: `f' (2i) = f i` and
`f' (2i + 1) = f i` give `f' (finProdFinEquiv (i, k)) = f i`, the value of `finProdFinEquiv (i, k)`
being `k + 2i`.

DERIVED: `2` is the block factor; `1` is the odd offset inside a block. -/
theorem fin_repeat_of_nat {n : ℕ} (f f' : ℕ → ℝ) (he : ∀ i, f' (2 * i) = f i)
    (ho : ∀ i, f' (2 * i + 1) = f i) (i : Fin n) (k : Fin 2) :
    f' ((finProdFinEquiv (i, k) : Fin (n * 2)) : ℕ) = f i := by
  have hv : ((finProdFinEquiv (i, k) : Fin (n * 2)) : ℕ) = (k : ℕ) + 2 * (i : ℕ) := rfl
  have hk : (k : ℕ) < 2 := k.isLt
  have hk' : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by omega
  rw [hv]
  rcases hk' with h0 | h1
  · rw [h0, zero_add]
    exact he i
  · rw [h1, show 1 + 2 * (i : ℕ) = 2 * (i : ℕ) + 1 by omega]
    exact ho i

#print axioms fin_repeat_of_nat

/-- **The integral length doubles under the block repeat by `2`.** `f' (2i) = f i` and
`f' (2i + 1) = f i` give `∑_{j < 2n} f' j = 2 ∑_{i < n} f i`: `integral_length_block_repeat` at
`s = 2`, read on `Finset.range` (`Fin.sum_univ_eq_sum_range`).

DERIVED: `2` is the block factor; `1` is the odd offset inside a block. -/
theorem sum_blockRepeat (f f' : ℕ → ℝ) (he : ∀ i, f' (2 * i) = f i)
    (ho : ∀ i, f' (2 * i + 1) = f i) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), f' j = 2 * ∑ i ∈ Finset.range n, f i := by
  have h := integral_length_block_repeat (n := n) (s := 2) (fun i : Fin n => f i)
    (fun j : Fin (n * 2) => f' j) (fun i k => fin_repeat_of_nat f f' he ho i k)
  rw [Fin.sum_univ_eq_sum_range f' (n * 2), Fin.sum_univ_eq_sum_range f n] at h
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2, mul_comm n 2] at h
  exact h

#print axioms sum_blockRepeat

/-- A sum over `2n` indices, grouped in pairs: `∑_{j < 2n} g j = ∑_{i < n} (g (2i) + g (2i + 1))`.

DERIVED: `2` is the pair size; `1` is the odd offset. -/
theorem sum_two_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), g j = ∑ i ∈ Finset.range n, (g (2 * i) + g (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ g (2 * n + 1),
      Finset.sum_range_succ g (2 * n), ih,
      Finset.sum_range_succ (fun i => g (2 * i) + g (2 * i + 1)) n]
    ring

#print axioms sum_two_mul

/-- **Even lags matched, antitone profile: the fine sum is at most twice the coarse one.** For
`f' (2i) = f i` and `f' (j + 1) ≤ f' j` at every `j`: `∑_{j < 2n} f' j ≤ 2 ∑_{i < n} f i`, each odd
term `f' (2i + 1)` being at most `f' (2i) = f i`.

DERIVED: `2` is the block factor; `1` is the step of the antitone condition. -/
theorem sum_evenRepeat_le (f f' : ℕ → ℝ) (he : ∀ i, f' (2 * i) = f i)
    (hanti : ∀ j, f' (j + 1) ≤ f' j) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), f' j ≤ 2 * ∑ i ∈ Finset.range n, f i := by
  rw [sum_two_mul, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h1 := hanti (2 * i)
  rw [he i] at h1
  rw [he i]
  linarith

#print axioms sum_evenRepeat_le

/-- **Even lags matched, antitone profile: the fine sum is at least twice the coarse one less one
coarse step.** For `f' (2i) = f i` and `f' (j + 1) ≤ f' j` at every `j`:
`2 ∑_{i < n} f i − (f 0 − f n) ≤ ∑_{j < 2n} f' j`, each odd term `f' (2i + 1)` being at least
`f' (2i + 2) = f (i + 1)`.

DERIVED: `2` is the block factor; `1` is the step of the antitone condition (the proof's `1` is also
the odd offset);
`0` is the first lag. -/
theorem le_sum_evenRepeat (f f' : ℕ → ℝ) (he : ∀ i, f' (2 * i) = f i)
    (hanti : ∀ j, f' (j + 1) ≤ f' j) (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, f i - (f 0 - f n) ≤ ∑ j ∈ Finset.range (2 * n), f' j := by
  have hshift : ∑ i ∈ Finset.range n, f (i + 1) = ∑ i ∈ Finset.range n, f i + f n - f 0 := by
    have h1 := Finset.sum_range_succ' f n
    have h2 := Finset.sum_range_succ f n
    linarith
  have hle : ∑ i ∈ Finset.range n, (f i + f (i + 1)) ≤ ∑ j ∈ Finset.range (2 * n), f' j := by
    rw [sum_two_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := hanti (2 * i + 1)
    have h2 : f' (2 * i + 1 + 1) = f (i + 1) := by
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring]
      exact he (i + 1)
    rw [h2] at h1
    rw [he i]
    linarith
  have hsplit : ∑ i ∈ Finset.range n, (f i + f (i + 1))
      = ∑ i ∈ Finset.range n, f i + ∑ i ∈ Finset.range n, f (i + 1) :=
    Finset.sum_add_distrib
  linarith

#print axioms le_sum_evenRepeat

/-- The physical form of the bracket: for `0 ≤ a`, `2ξ − c ≤ ξ' ≤ 2ξ` gives
`a·ξ − (a/2)·c ≤ (a/2)·ξ' ≤ a·ξ`.

DERIVED: `2` is the block factor, the halving of the spacing; `0` is the sign of `a`. -/
theorem half_mul_bounds {a ξ ξ' c : ℝ} (ha : 0 ≤ a) (hlo : 2 * ξ - c ≤ ξ') (hhi : ξ' ≤ 2 * ξ) :
    a * ξ - a / 2 * c ≤ a / 2 * ξ' ∧ a / 2 * ξ' ≤ a * ξ := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo ha]
  · nlinarith [mul_le_mul_of_nonneg_left hhi ha]

#print axioms half_mul_bounds

end Sequence

/-! ## 3. Profiles on transfer data -/

section Profile

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- `ChessboardRead.lagProfile D x 0 = D.form x x`.

DERIVED: `0` is the contact lag. -/
theorem lagProfile_zero (D : TransferData A) (x : A) :
    ChessboardRead.lagProfile D x 0 = D.form x x := by
  show D.form x ((D.T ^ 0) x) = D.form x x
  rw [pow_zero, Module.End.one_apply]

#print axioms lagProfile_zero

/-- **One step does not raise the diagonal.** `D.form y (T y) ≤ D.form y y`, for every transfer data.
Cauchy–Schwarz gives `D.form y (T y)² ≤ D.form y y · D.form (T y) (T y)`, contractivity bounds the
last factor by `D.form y y`, and `D.form y y ≥ 0`.

DERIVED: no numeral occurs in the statement. -/
theorem form_T_le (D : TransferData A) (y : A) :
    D.form y (D.T y) ≤ D.form y y := by
  have hcs := D.toReflForm.cauchy_schwarz y (D.T y)
  have hc := D.T_contract y
  have hb : 0 ≤ D.form y y := D.form_nonneg y
  have hsq : D.form y (D.T y) ^ 2 ≤ D.form y y ^ 2 := by
    calc D.form y (D.T y) ^ 2 ≤ D.form y y * D.form (D.T y) (D.T y) := hcs
      _ ≤ D.form y y * D.form y y := mul_le_mul_of_nonneg_left hc hb
      _ = D.form y y ^ 2 := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero hb hsq

#print axioms form_T_le

/-- **The next step does not raise it either.** Under `PositiveTransfer D`:
`D.form (T y) (T y) ≤ D.form y (T y)`. Cauchy–Schwarz for `ChessboardRead.tForm` at `(y, T y)` gives
`D.form (T y) (T y)² ≤ D.form y (T y) · D.form (T y) (T² y)`, and `form_T_le` at `T y` bounds the last
factor by `D.form (T y) (T y)`.

DERIVED: no numeral occurs in the statement. -/
theorem form_TT_le (D : TransferData A) (hP : PositiveTransfer D) (y : A) :
    D.form (D.T y) (D.T y) ≤ D.form y (D.T y) := by
  have hcs := (ChessboardRead.tForm D hP).cauchy_schwarz y (D.T y)
  have e1 : (ChessboardRead.tForm D hP).form y (D.T y) = D.form (D.T y) (D.T y) :=
    (D.T_symm y (D.T y)).symm
  have e2 : (ChessboardRead.tForm D hP).form y y = D.form y (D.T y) := rfl
  have e3 : (ChessboardRead.tForm D hP).form (D.T y) (D.T y) = D.form (D.T y) (D.T (D.T y)) := rfl
  rw [e1, e2, e3] at hcs
  have h3 : D.form (D.T y) (D.T (D.T y)) ≤ D.form (D.T y) (D.T y) := form_T_le D (D.T y)
  have hc0 : 0 ≤ D.form (D.T y) (D.T y) := D.form_nonneg _
  have hb0 : 0 ≤ D.form y (D.T y) := hP y
  have h4 : D.form (D.T y) (D.T y) ^ 2 ≤ D.form y (D.T y) * D.form (D.T y) (D.T y) :=
    le_trans hcs (mul_le_mul_of_nonneg_left h3 hb0)
  rcases eq_or_lt_of_le hc0 with h0 | h0
  · rw [← h0]
    exact hb0
  · have h5 : D.form (D.T y) (D.T y) * D.form (D.T y) (D.T y)
        ≤ D.form y (D.T y) * D.form (D.T y) (D.T y) := by
      rw [← sq]
      exact h4
    exact le_of_mul_le_mul_right h5 h0

#print axioms form_TT_le

/-- **The transfer profile is antitone.** Under `PositiveTransfer D`:
`lagProfile D x (n + 1) ≤ lagProfile D x n` at every `n`. At `n = 2j` it is `form_T_le` at `Tʲ x`
(`ChessboardRead.lagProfile_even`, `ChessboardRead.lagProfile_odd`); at `n = 2j + 1` it is
`form_TT_le` at `Tʲ x`.

DERIVED: `1` is one further lag. -/
theorem lagProfile_succ_le (D : TransferData A) (hP : PositiveTransfer D) (x : A) (n : ℕ) :
    ChessboardRead.lagProfile D x (n + 1) ≤ ChessboardRead.lagProfile D x n := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
  · subst hj
    rw [ChessboardRead.lagProfile_odd D x j, ChessboardRead.lagProfile_even D x j]
    exact form_T_le D _
  · subst hj
    have e2 : ChessboardRead.lagProfile D x (2 * j + 1 + 1)
        = D.form (D.T ((D.T ^ j) x)) (D.T ((D.T ^ j) x)) := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, ChessboardRead.lagProfile_even D x (j + 1),
        ChessboardRead.T_pow_succ_apply D j x]
    rw [e2, ChessboardRead.lagProfile_odd D x j]
    exact form_TT_le D hP _

#print axioms lagProfile_succ_le

/-- **The Entroptic ratio profile** of an observable: `ratioProfile D x n = D.form x (Tⁿ x) / D.form x x`,
the reflected pairing at lag `n` over its lag-zero value, `C(n)/C(0)`.

DERIVED: no numeral occurs. -/
def ratioProfile (D : TransferData A) (x : A) (n : ℕ) : ℝ :=
  ChessboardRead.lagProfile D x n / D.form x x

/-- At a non-null observable the ratio profile is `1` at lag `0`.

DERIVED: `0` is the contact lag and the sign of the lag-zero value; `1` is the ratio. -/
theorem ratioProfile_zero (D : TransferData A) {x : A} (hpos : 0 < D.form x x) :
    ratioProfile D x 0 = 1 := by
  unfold ratioProfile
  rw [lagProfile_zero]
  exact div_self hpos.ne'

#print axioms ratioProfile_zero

/-- Under `PositiveTransfer D` the ratio profile is antitone: `lagProfile_succ_le` over the
nonnegative `D.form x x`.

DERIVED: `1` is one further lag. -/
theorem ratioProfile_succ_le (D : TransferData A) (hP : PositiveTransfer D) (x : A) (n : ℕ) :
    ratioProfile D x (n + 1) ≤ ratioProfile D x n :=
  div_le_div_of_nonneg_right (lagProfile_succ_le D hP x n) (D.form_nonneg x)

#print axioms ratioProfile_succ_le

/-- **The integral correlation length in lattice units** over a window of `n` lags:
`integralLength D x n = ∑_{j < n} ratioProfile D x j`, the Entroptic `ξ = ∑_τ C(τ)/C(0)`.

DERIVED: no numeral occurs. -/
def integralLength (D : TransferData A) (x : A) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ratioProfile D x j

/-- **The envelope of the profile at one lag.** Every observable orthogonal to the vacuum has its
profile at lag `n` at most `q` times its lag-zero value: `lagProfile D x n ≤ q · D.form x x`.

DERIVED: `0` is the vacuum pairing. -/
def LagRatio (D : TransferData A) (n : ℕ) (q : ℝ) : Prop :=
  ∀ x : A, D.form x D.vac = 0 → ChessboardRead.lagProfile D x n ≤ q * D.form x x

/-- **The geometric envelope at rate `r`**: `LagRatio D n (rⁿ)` at every lag `n`.

DERIVED: no numeral occurs. -/
def EnvelopeAt (D : TransferData A) (r : ℝ) : Prop :=
  ∀ n : ℕ, LagRatio D n (r ^ n)

/-- **The geometric envelope at the even lags**: `LagRatio D (2d) (r^{2d})` at every `d`; the odd
lags are not asked.

DERIVED: `2` is the doubling of the lag, the block factor. -/
def EvenEnvelopeAt (D : TransferData A) (r : ℝ) : Prop :=
  ∀ d : ℕ, LagRatio D (2 * d) (r ^ (2 * d))

/-- `GapAt D r` at `0 ≤ r` gives `EnvelopeAt D r` (`ChessboardRead.lag_of_gapAt`).

DERIVED: `0` is the lower end of `r`. -/
theorem envelopeAt_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : TransferGap.GapAt D r) : EnvelopeAt D r := by
  intro n x hx
  exact ChessboardRead.lag_of_gapAt D hr hg n x hx

#print axioms envelopeAt_of_gapAt

/-- `GapAt D r` at `0 ≤ r` gives `EvenEnvelopeAt D r` (`ChessboardRead.lag_of_gapAt` at `2d`).

DERIVED: `0` is the lower end of `r`. -/
theorem evenEnvelopeAt_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : TransferGap.GapAt D r) : EvenEnvelopeAt D r := by
  intro d x hx
  exact ChessboardRead.lag_of_gapAt D hr hg (2 * d) x hx

#print axioms evenEnvelopeAt_of_gapAt

/-- Under `PositiveTransfer D` and `0 ≤ r`, `EvenEnvelopeAt D r` gives `GapAt D r`: its lag-`2`
bound is the single lag of `ChessboardRead.gapAt_of_lag`.

DERIVED: `0` is the lower end of `r`. The proof's lag `2 * 1` is the first even lag past contact. -/
theorem gapAt_of_evenEnvelopeAt (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 ≤ r) (h : EvenEnvelopeAt D r) : TransferGap.GapAt D r :=
  ChessboardRead.gapAt_of_lag D hP (m := 2 * 1) (by norm_num) hr (fun x hx => h 1 x hx)

#print axioms gapAt_of_evenEnvelopeAt

/-- Under `PositiveTransfer D` and `0 ≤ r`, `EnvelopeAt D r` gives `GapAt D r` (its lag-`1` bound,
`ChessboardRead.gapAt_of_lag`).

DERIVED: `0` is the lower end of `r`. The proof's lag `1` is the first lag past contact. -/
theorem gapAt_of_envelopeAt (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 ≤ r) (h : EnvelopeAt D r) : TransferGap.GapAt D r :=
  ChessboardRead.gapAt_of_lag D hP (m := 1) one_ne_zero hr (fun x hx => h 1 x hx)

#print axioms gapAt_of_envelopeAt

/-- **The envelope is the gap.** Under `PositiveTransfer D` and `0 ≤ r`: `EnvelopeAt D r ↔ GapAt D r`.

DERIVED: `0` is the lower end of `r`. -/
theorem envelopeAt_iff_gapAt (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 ≤ r) : EnvelopeAt D r ↔ TransferGap.GapAt D r :=
  ⟨gapAt_of_envelopeAt D hP hr, envelopeAt_of_gapAt D hr⟩

#print axioms envelopeAt_iff_gapAt

/-- **The even lags carry the gap; the odd lags follow.** Under `PositiveTransfer D` and `0 ≤ r`:
`EvenEnvelopeAt D r ↔ GapAt D r`.

DERIVED: `0` is the lower end of `r`. -/
theorem evenEnvelopeAt_iff_gapAt (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 ≤ r) : EvenEnvelopeAt D r ↔ TransferGap.GapAt D r :=
  ⟨gapAt_of_evenEnvelopeAt D hP hr, evenEnvelopeAt_of_gapAt D hr⟩

#print axioms evenEnvelopeAt_iff_gapAt

/-- `(e^{−K·(a/2)})²  = e^{−K·a}`.

DERIVED: `2` is the halving and the square. -/
theorem exp_half_sq (K a : ℝ) : Real.exp (-(K * (a / 2))) ^ 2 = Real.exp (-(K * a)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

#print axioms exp_half_sq

/-- **At halved spacing the even fine lags read the coarse lags.** For any rate `K` and spacing `a`:
the even envelope at `e^{−K·(a/2)}` holds exactly when the profile at every lag `2d` is at most
`(e^{−K·a})^d` times its lag-zero value — the coarse geometric envelope at lag `d`, over the same
physical separation `2d·(a/2) = d·a`.

DERIVED: `2` is the halving of the spacing and the doubling of the lag. -/
theorem evenEnvelopeAt_half_iff (D' : TransferData A) (K a : ℝ) :
    EvenEnvelopeAt D' (Real.exp (-(K * (a / 2)))) ↔
      ∀ d : ℕ, LagRatio D' (2 * d) (Real.exp (-(K * a)) ^ d) := by
  have e : ∀ d : ℕ, Real.exp (-(K * (a / 2))) ^ (2 * d) = Real.exp (-(K * a)) ^ d := by
    intro d
    rw [pow_mul, exp_half_sq]
  constructor
  · intro h d
    rw [← e d]
    exact h d
  · intro h d
    rw [e d]
    exact h d

#print axioms evenEnvelopeAt_half_iff

/-- **The zoom on envelopes.** Every envelope `q` of the coarse profile at lag `d` is an envelope of
the fine profile at lag `2d`: `LagRatio D d q → LagRatio D' (2d) q`.

DERIVED: `2` is the block factor. -/
def ZoomRepeat (D D' : TransferData A) : Prop :=
  ∀ (d : ℕ) (q : ℝ), LagRatio D d q → LagRatio D' (2 * d) q

/-- **The Entroptic block repeat on the even fine lags.** Through a map `B` of fine observables to
coarse ones, every observable `x` orthogonal to the fine vacuum has `B x` orthogonal to the coarse
vacuum, `B x` non-null whenever `x` is, and `ratioProfile D' x (2d) = ratioProfile D (B x) d` at every
`d`. The odd fine lags are not asked.

DERIVED: `2` is the block factor; `0` is the vacuum pairing and the sign of the lag-zero values. -/
def EvenRepeat (D D' : TransferData A) (B : A → A) : Prop :=
  ∀ x : A, D'.form x D'.vac = 0 →
    D.form (B x) D.vac = 0 ∧ (0 < D'.form x x → 0 < D.form (B x) (B x)) ∧
      ∀ d : ℕ, ratioProfile D' x (2 * d) = ratioProfile D (B x) d

/-- **The Entroptic block repeat, verbatim.** `EvenRepeat D D' B` together with the odd fine lags,
`ratioProfile D' x (2d + 1) = ratioProfile D (B x) d`: the fine ratio profile of `x` is the coarse
ratio profile of `B x` block-repeated by `2`.

DERIVED: `2` is the block factor; `1` is the odd offset; `0` is the vacuum pairing. -/
def LiteralRepeat (D D' : TransferData A) (B : A → A) : Prop :=
  EvenRepeat D D' B ∧
    ∀ x : A, D'.form x D'.vac = 0 → ∀ d : ℕ, ratioProfile D' x (2 * d + 1) = ratioProfile D (B x) d

/-- **The even repeat gives the zoom on envelopes.** `EvenRepeat D D' B → ZoomRepeat D D'`. At a
null `x` the fine profile at every lag is at most its lag-zero value `0` (`ChessboardRead.lag_of_gapAt`
at rate `1`, `TransferGap.gapAt_of_one_le_sq`); at a non-null `x` the coarse bound divided by the
positive `D.form (B x) (B x)` is the fine ratio at lag `2d`.

DERIVED: no numeral occurs in the statement. The proof's rate `1` is the rate at which `GapAt` is
automatic, and its `0` the null lag-zero value. -/
theorem zoomRepeat_of_evenRepeat (D D' : TransferData A) (B : A → A) (h : EvenRepeat D D' B) :
    ZoomRepeat D D' := by
  intro d q hq x hx
  obtain ⟨hBx, hpos, hrat⟩ := h x hx
  have hb0 : 0 ≤ D'.form x x := D'.form_nonneg x
  rcases eq_or_lt_of_le hb0 with h0 | h0
  · have hle := ChessboardRead.lag_of_gapAt D' (r := 1) zero_le_one
      (TransferGap.gapAt_of_one_le_sq D' (r := 1) (by norm_num)) (2 * d) x hx
    rw [one_pow, one_mul, ← h0] at hle
    rw [← h0, mul_zero]
    exact hle
  · have hB0 : 0 < D.form (B x) (B x) := hpos h0
    have hq' : ChessboardRead.lagProfile D (B x) d ≤ q * D.form (B x) (B x) := hq (B x) hBx
    have h1 : ratioProfile D (B x) d ≤ q := (div_le_iff₀ hB0).mpr hq'
    rw [← hrat d] at h1
    have h2 : ChessboardRead.lagProfile D' x (2 * d) / D'.form x x ≤ q := h1
    exact (div_le_iff₀ h0).mp h2

#print axioms zoomRepeat_of_evenRepeat

/-- `GapAt D r` at `0 ≤ r` gives `LagRatio D 1 r`.

DERIVED: `0` is the lower end of `r`; `1` is the lag. -/
theorem lagRatio_one_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (hg : TransferGap.GapAt D r) : LagRatio D 1 r := by
  intro x hx
  have h := ChessboardRead.lag_of_gapAt D hr hg 1 x hx
  have e : r ^ 1 = r := pow_one r
  rw [e] at h
  exact h

#print axioms lagRatio_one_of_gapAt

/-- **The zoom halves the step.** Under `PositiveTransfer D'`, `ZoomRepeat D D'`, `0 ≤ r` and the
coarse lag-one envelope `LagRatio D 1 r`: `GapAt D' (√r)`. The zoom puts the fine lag-`2` envelope at
`r`, and `GapStep.gapAt_sqrt_iff_lag_double` at `m = 1` reads it as `GapAt` at `√r`.

DERIVED: `0` is the lower end of `r`; `1` is the coarse lag. The proof's fine lag `2 * 1` is its
double. -/
theorem gapAt_sqrt_of_zoomRepeat (D D' : TransferData A) (hP' : PositiveTransfer D')
    (hz : ZoomRepeat D D') {r : ℝ} (hr : 0 ≤ r) (h1 : LagRatio D 1 r) :
    TransferGap.GapAt D' (Real.sqrt r) := by
  have h2 : LagRatio D' (2 * 1) r := hz 1 r h1
  refine (GapStep.gapAt_sqrt_iff_lag_double D' hP' (m := 1) one_ne_zero hr).mpr ?_
  intro x hx
  have h := h2 x hx
  rw [show r ^ 1 = r from pow_one r]
  exact h

#print axioms gapAt_sqrt_of_zoomRepeat

/-- **A ratio of one at lag one excludes a gap.** For `x` orthogonal to the vacuum with
`0 < D.form x x` and `ratioProfile D x 1 = 1`, no `0 ≤ r < 1` has `GapAt D r`:
`ChessboardRead.lag_of_gapAt` at lag `1` would give `D.form x x ≤ r · D.form x x`.

DERIVED: `1` is the lag, the ratio and the upper end of `r`; `0` is the vacuum pairing, the sign of
the lag-zero value and the lower end of `r`. -/
theorem not_gapAt_of_ratio_one (D : TransferData A) {x : A} (hx : D.form x D.vac = 0)
    (hpos : 0 < D.form x x) (h1 : ratioProfile D x 1 = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ¬ TransferGap.GapAt D r := by
  intro hg
  have h := ChessboardRead.lag_of_gapAt D hr0 hg 1 x hx
  have e1 : ChessboardRead.lagProfile D x 1 = D.form x x := by
    have e : ChessboardRead.lagProfile D x 1 / D.form x x = 1 := h1
    exact (div_eq_one_iff_eq hpos.ne').mp e
  have h' : ChessboardRead.lagProfile D x 1 ≤ r * D.form x x := by
    have e : r ^ 1 = r := pow_one r
    rw [e] at h
    exact h
  rw [e1] at h'
  nlinarith [mul_lt_mul_of_pos_right hr1 hpos]

#print axioms not_gapAt_of_ratio_one

/-- **The verbatim block repeat excludes a gap at the finer coupling.** Under
`LiteralRepeat D D' B`, every `x` orthogonal to the fine vacuum with `0 < D'.form x x` excludes
`GapAt D' r` at every `0 ≤ r < 1`. The odd lag at `d = 0` reads
`ratioProfile D' x 1 = ratioProfile D (B x) 0 = 1` (`ratioProfile_zero`, `B x` non-null), and
`not_gapAt_of_ratio_one` applies. The Entroptic identity `f' (2i + k) = f i` therefore holds on the
connected reflected profile of a gapped finer lattice only at null observables.

DERIVED: `1` is the upper end of `r`; `0` is the vacuum pairing, the sign of the lag-zero value and
the lower end of `r`. The proof's `2 * 0 + 1` is the odd lag of the first block. -/
theorem literalRepeat_no_gap (D D' : TransferData A) (B : A → A) (h : LiteralRepeat D D' B)
    {x : A} (hx : D'.form x D'.vac = 0) (hpos : 0 < D'.form x x) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : ¬ TransferGap.GapAt D' r := by
  obtain ⟨hev, hodd⟩ := h
  obtain ⟨_, hB, _⟩ := hev x hx
  have h1 : ratioProfile D' x (2 * 0 + 1) = ratioProfile D (B x) 0 := hodd x hx 0
  rw [ratioProfile_zero D (hB hpos), show (2 * 0 + 1 : ℕ) = 1 by norm_num] at h1
  exact not_gapAt_of_ratio_one D' hx hpos h1 hr0 hr1

#print axioms literalRepeat_no_gap

/-- **The verbatim repeat doubles the integral length.** Under `LiteralRepeat D D' B` and `x`
orthogonal to the fine vacuum: `integralLength D' x (2n) = 2 · integralLength D (B x) n`
(`sum_blockRepeat`, from `integral_length_block_repeat`).

DERIVED: `2` is the block factor; `0` is the vacuum pairing. -/
theorem integralLength_literal (D D' : TransferData A) (B : A → A) (h : LiteralRepeat D D' B)
    {x : A} (hx : D'.form x D'.vac = 0) (n : ℕ) :
    integralLength D' x (2 * n) = 2 * integralLength D (B x) n :=
  sum_blockRepeat (ratioProfile D (B x)) (ratioProfile D' x) ((h.1 x hx).2.2) (h.2 x hx) n

#print axioms integralLength_literal

/-- **The even repeat brackets the integral length.** Under `EvenRepeat D D' B`,
`PositiveTransfer D'` and `x` orthogonal to the fine vacuum:
`2ξ − (f 0 − f n) ≤ ξ' ≤ 2ξ`, with `ξ = integralLength D (B x) n`, `f = ratioProfile D (B x)` and
`ξ' = integralLength D' x (2n)`. The fine ratio profile is antitone (`ratioProfile_succ_le`), so each
odd fine lag lies between its even neighbours (`le_sum_evenRepeat`, `sum_evenRepeat_le`).

DERIVED: `2` is the block factor; `0` is the vacuum pairing and the first lag. -/
theorem integralLength_even_bounds (D D' : TransferData A) (B : A → A) (h : EvenRepeat D D' B)
    (hP' : PositiveTransfer D') {x : A} (hx : D'.form x D'.vac = 0) (n : ℕ) :
    2 * integralLength D (B x) n - (ratioProfile D (B x) 0 - ratioProfile D (B x) n)
        ≤ integralLength D' x (2 * n) ∧
      integralLength D' x (2 * n) ≤ 2 * integralLength D (B x) n := by
  have he : ∀ i, ratioProfile D' x (2 * i) = ratioProfile D (B x) i := (h x hx).2.2
  have hanti : ∀ j, ratioProfile D' x (j + 1) ≤ ratioProfile D' x j :=
    fun j => ratioProfile_succ_le D' hP' x j
  exact ⟨le_sum_evenRepeat (ratioProfile D (B x)) (ratioProfile D' x) he hanti n,
    sum_evenRepeat_le (ratioProfile D (B x)) (ratioProfile D' x) he hanti n⟩

#print axioms integralLength_even_bounds

end Profile

/-! ## 4. The leftover past the aperture, on a Hilbert space -/

section Leftover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The spectral measure of a vector**: the Riesz–Markov measure of
`SpectralRep.momentFunctional a ha v`, the measure `SpectralRep.exists_spectral_measure` produces.

DERIVED: `0` and `1` are the interval's ends. -/
def specMeasure (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E) : Measure (Set.Icc (0 : ℝ) 1) :=
  RealRMK.rieszMeasure (SpectralRep.momentFunctional a ha v)

/-- `specMeasure a ha v` is finite.

DERIVED: no numeral occurs in the statement. -/
theorem specMeasure_isFinite (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E) :
    IsFiniteMeasure (specMeasure a ha v) := by
  unfold specMeasure
  infer_instance

#print axioms specMeasure_isFinite

/-- **`specMeasure` represents the functional calculus.** For `a` self-adjoint with spectrum in
`[0, 1]`: `re ⟪v, h(a) v⟫ = ∫ h d(specMeasure a ha v)` at every continuous `h` (the proof of
`SpectralRep.exists_spectral_measure`).

DERIVED: `0` and `1` are the interval's ends. -/
theorem specMeasure_rep (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (v : E) :
    ∀ h : ℝ → ℝ, Continuous h →
      RCLike.re (inner ℂ v (cfc h a v)) = ∫ t, h (t : ℝ) ∂(specMeasure a ha v) := by
  intro h hh
  have hI := RealRMK.integral_rieszMeasure (SpectralRep.momentFunctional a ha v)
    (SpectralRep.restr h hh)
  have hval : SpectralRep.momentFunctional a ha v (SpectralRep.restr h hh)
      = RCLike.re (inner ℂ v (cfc h a v)) := by
    show RCLike.re (inner ℂ v (cfc (SpectralRep.ext01 (SpectralRep.restr h hh)) a v)) = _
    rw [SpectralRep.cfc_ext01_restr a hspec h hh]
  rw [← hval, ← hI]
  rfl

#print axioms specMeasure_rep

/-- **The out-of-aperture weight** of `v` past the edge `s`: the spectral weight of `v` on `(s, 1]`.

DERIVED: `0` and `1` are the interval's ends. -/
def outWeight (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (v : E) (s : ℝ) : ENNReal :=
  specMeasure a ha v {t : Set.Icc (0 : ℝ) 1 | s < (t : ℝ)}

/-- **The leftover vanishes past `s`**: every vector orthogonal to `Ω` has out-of-aperture weight `0`
past `s`.

DERIVED: `0` is the orthogonality and the vanishing weight. -/
def LeftoverNull (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (Ω : E) (s : ℝ) : Prop :=
  ∀ v : E, inner ℂ Ω v = 0 → outWeight a ha v s = 0

/-- **No weight above `s` contracts.** For a finite measure `w` representing `u`'s functional
calculus with `w {s < t} = 0` and `0 ≤ s`: `‖aᵐ u‖ ≤ sᵐ ‖u‖` (the computation closing
`FloorRead.norm_pow_le_of_reads_gt`).

DERIVED: `0` and `1` are the interval's ends; `0` is the sign of `s` and the null weight. -/
theorem norm_pow_le_of_null_above (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (u : E) {s : ℝ}
    (hs0 : 0 ≤ s) (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (hint : ∀ h : ℝ → ℝ, Continuous h → RCLike.re (inner ℂ u (cfc h a u)) = ∫ t, h (t : ℝ) ∂w)
    (hnull : w {t : Set.Icc (0 : ℝ) 1 | s < (t : ℝ)} = 0) (m : ℕ) :
    ‖(a ^ m) u‖ ≤ s ^ m * ‖u‖ := by
  have hae : ∀ᵐ t : Set.Icc (0 : ℝ) 1 ∂w, (t : ℝ) ≤ s := by
    rw [ae_iff]
    simpa only [not_le] using hnull
  have hA : ‖(a ^ m) u‖ ^ 2 = ∫ t, (t : ℝ) ^ m * (t : ℝ) ^ m ∂w := by
    have h1' := SpectralRep.norm_sq_cfc a ha (fun x : ℝ => x ^ m) (continuous_pow m) u
    have h2' := hint (fun x : ℝ => x ^ m * x ^ m) ((continuous_pow m).mul (continuous_pow m))
    beta_reduce at h1' h2'
    rw [cfc_pow_id (R := ℝ) a m ha] at h1'
    rw [h1', h2']
  have hu2 : ‖u‖ ^ 2 = ∫ _t, (1 : ℝ) ∂w := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    have h := hint (fun _ => 1) continuous_const
    rw [cfc_const_one ℝ a ha, ContinuousLinearMap.one_apply] at h
    exact h
  have hsq : ‖(a ^ m) u‖ ^ 2 ≤ (s ^ m * ‖u‖) ^ 2 := by
    rw [hA, mul_pow, hu2, ← integral_const_mul]
    refine integral_mono_ae
      (SpectralRep.integrable_of_continuous w
        ((continuous_subtype_val.pow m).mul (continuous_subtype_val.pow m)))
      (integrable_const _) ?_
    filter_upwards [hae] with t ht
    have hp := pow_le_pow_left₀ t.2.1 ht m
    have hp0 := pow_nonneg t.2.1 m
    show (t : ℝ) ^ m * (t : ℝ) ^ m ≤ (s ^ m) ^ 2 * 1
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

#print axioms norm_pow_le_of_null_above

/-- **A contraction leaves nothing past its rate.** For `a` self-adjoint with spectrum in `[0, 1]`,
`a Ω = Ω`, `0 ≤ s` and `‖a u‖ ≤ s ‖u‖` on `Ω⊥`: `LeftoverNull a ha Ω s`
(`ReadConverse.ae_le_of_contraction` at `specMeasure`).

DERIVED: `0` and `1` are the interval's ends; `0` is the sign of `s` and the orthogonality. -/
theorem leftoverNull_of_contraction (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) {s : ℝ} (hs0 : 0 ≤ s)
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ s * ‖u‖) : LeftoverNull a ha Ω s := by
  intro v hv
  haveI := specMeasure_isFinite a ha v
  have hsupp := ReadConverse.ae_le_of_contraction a ha hspec Ω hΩ s hs0 hcon v hv
    (specMeasure a ha v) (specMeasure_rep a ha hspec v)
  have h0 := ae_iff.mp hsupp
  show specMeasure a ha v {t : Set.Icc (0 : ℝ) 1 | s < (t : ℝ)} = 0
  simpa only [not_le] using h0

#print axioms leftoverNull_of_contraction

/-- **Nothing past the rate contracts.** For `a` self-adjoint with spectrum in `[0, 1]`, `0 ≤ s` and
`LeftoverNull a ha Ω s`: `‖a u‖ ≤ s ‖u‖` on `Ω⊥` (`norm_pow_le_of_null_above` at `m = 1`).

DERIVED: `0` and `1` are the interval's ends; `0` is the sign of `s` and the orthogonality. -/
theorem contraction_of_leftoverNull (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) {s : ℝ} (hs0 : 0 ≤ s)
    (h : LeftoverNull a ha Ω s) : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ s * ‖u‖ := by
  intro u hu
  haveI := specMeasure_isFinite a ha u
  have h1 := norm_pow_le_of_null_above a ha u hs0 (specMeasure a ha u)
    (specMeasure_rep a ha hspec u) (h u hu) 1
  rw [pow_one, pow_one] at h1
  exact h1

#print axioms contraction_of_leftoverNull

/-- **The contraction is the vanishing leftover.** For `a` self-adjoint with spectrum in `[0, 1]`,
`a Ω = Ω` and `0 ≤ s`: `‖a u‖ ≤ s ‖u‖` on `Ω⊥` holds exactly when `LeftoverNull a ha Ω s`.

DERIVED: `0` and `1` are the interval's ends; `0` is the sign of `s` and the orthogonality. -/
theorem contraction_iff_leftoverNull (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) {s : ℝ} (hs0 : 0 ≤ s) :
    (∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ s * ‖u‖) ↔ LeftoverNull a ha Ω s :=
  ⟨leftoverNull_of_contraction a ha hspec Ω hΩ hs0, contraction_of_leftoverNull a ha hspec Ω hs0⟩

#print axioms contraction_iff_leftoverNull

/-- **A leftover vanishing past every point above `e` vanishes past `e`.** `(e, 1]` is the countable
union of the `(e + 1/(n+1), 1]` (`measure_iUnion_null_iff`).

DERIVED: no numeral occurs in the statement. The proof's `1 / (n + 1)` is the slice width of the
countable union. -/
theorem leftoverNull_of_forall_gt (a : E →L[ℂ] E) (ha : IsSelfAdjoint a) (Ω : E) (e : ℝ)
    (h : ∀ s : ℝ, e < s → LeftoverNull a ha Ω s) : LeftoverNull a ha Ω e := by
  intro v hv
  have hU : {t : Set.Icc (0 : ℝ) 1 | e < (t : ℝ)}
      = ⋃ n : ℕ, {t : Set.Icc (0 : ℝ) 1 | e + 1 / ((n : ℝ) + 1) < (t : ℝ)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  show specMeasure a ha v {t : Set.Icc (0 : ℝ) 1 | e < (t : ℝ)} = 0
  rw [hU, measure_iUnion_null_iff]
  intro n
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact h (e + 1 / ((n : ℝ) + 1)) (by linarith) v hv

#print axioms leftoverNull_of_forall_gt

/-- **The edge of the aperture `2k + 1` at margin `γ`**: `e ≥ 0` reads at least `γ`
(`γ ≤ modeCosAvg k e`), and every point above it reads below `γ`.

DERIVED: `0` is the lower end of the edge. -/
def IsEdge (k : ℕ) (γ e : ℝ) : Prop :=
  0 ≤ e ∧ γ ≤ ReadConverse.modeCosAvg k e ∧ ∀ s : ℝ, e < s → ReadConverse.modeCosAvg k s < γ

/-- The rates at or below the aperture's resolution: `{r ≥ 0 | γ ≤ modeCosAvg k r}`.

DERIVED: `0` is the lower end of the rate. -/
def edgeSet (k : ℕ) (γ : ℝ) : Set ℝ :=
  Set.Ici 0 ∩ ReadConverse.modeCosAvg k ⁻¹' Set.Ici γ

/-- Membership in `edgeSet`.

DERIVED: `0` is the lower end of the rate. -/
theorem mem_edgeSet {k : ℕ} {γ r : ℝ} :
    r ∈ edgeSet k γ ↔ 0 ≤ r ∧ γ ≤ ReadConverse.modeCosAvg k r :=
  Iff.rfl

#print axioms mem_edgeSet

/-- **The edge `r_γ(k)`**: the supremum of `edgeSet k γ`.

DERIVED: no numeral occurs. -/
def readEdge (k : ℕ) (γ : ℝ) : ℝ := sSup (edgeSet k γ)

/-- **The edge exists and lies below `1`.** At `0 < γ ≤ modeCosAvg k 0`, `readEdge k γ` is an edge
(`IsEdge`) and `readEdge k γ < 1`. `edgeSet k γ` is closed (`modeCosAvg k` is continuous on
`[0, ∞)`, `ContinuousOn.preimage_isClosed_of_isClosed`), contains `0`, and lies below `1`
(`ReadConverse.modeCosAvg_antitone`, `FloorRead.modeCosAvg_one`), so it contains its supremum
(`IsClosed.csSup_mem`); a point above the supremum is outside the set. At every
`γ ≤ 3^{−1/4}` the hypothesis `γ ≤ modeCosAvg k 0` holds (`ReadConverse.modeCosAvg_gt_at_zero`).

DERIVED: `0` is the sign of `γ` and the rate at which `modeCosAvg k` is largest; `1` is the massless
mode (in the proof, `modeCosAvg k` reads `0` there). -/
theorem isEdge_readEdge (k : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ0 : γ ≤ ReadConverse.modeCosAvg k 0) :
    IsEdge k γ (readEdge k γ) ∧ readEdge k γ < 1 := by
  have hcont : ContinuousOn (ReadConverse.modeCosAvg k) (Set.Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    have hfun : ReadConverse.modeCosAvg k
        = fun s => ReadConverse.modeCos k s / ReadConverse.modeMass k s := rfl
    rw [hfun]
    exact ((ReadConverse.continuous_modeCos k).continuousAt.div
      (ReadConverse.continuous_modeMass k).continuousAt
      (ne_of_gt (ReadConverse.modeMass_pos k ht0))).continuousWithinAt
  have hclosed : IsClosed (edgeSet k γ) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
  have hlt1 : ∀ r ∈ edgeSet k γ, r < 1 := by
    intro r hr
    rw [mem_edgeSet] at hr
    by_contra h1
    push_neg at h1
    have hanti := ReadConverse.modeCosAvg_antitone k (Set.mem_Ici.mpr (zero_le_one : (0 : ℝ) ≤ 1))
      (Set.mem_Ici.mpr hr.1) h1
    rw [FloorRead.modeCosAvg_one] at hanti
    linarith [hr.2]
  have hne : (edgeSet k γ).Nonempty := ⟨0, mem_edgeSet.mpr ⟨le_rfl, hγ0⟩⟩
  have hbdd : BddAbove (edgeSet k γ) := ⟨1, fun r hr => (hlt1 r hr).le⟩
  have hmem : readEdge k γ ∈ edgeSet k γ := hclosed.csSup_mem hne hbdd
  have hlt : readEdge k γ < 1 := hlt1 _ hmem
  rw [mem_edgeSet] at hmem
  refine ⟨⟨hmem.1, hmem.2, fun s hs => ?_⟩, hlt⟩
  by_contra hns
  push_neg at hns
  have hsS : s ∈ edgeSet k γ := mem_edgeSet.mpr ⟨le_trans hmem.1 hs.le, hns⟩
  have hle : s ≤ readEdge k γ := le_csSup hbdd hsS
  linarith

#print axioms isEdge_readEdge

/-- **The margin read is the vanishing leftover past the edge.** For `a` self-adjoint with spectrum
in `[0, 1]`, `a Ω = Ω` and an edge `e` of the aperture `2k + 1` at margin `γ`:
`ReadReduce.ReadsClearWith a Ω k γ` holds exactly when `LeftoverNull a ha Ω e`. Forward:
`FloorRead.contraction_of_readsClearWith` contracts at every `s > e`, `leftoverNull_of_contraction`
there, and `leftoverNull_of_forall_gt`. Back: `contraction_of_leftoverNull` at `e` and
`FloorRead.readsClearWith_of_contraction`.

DERIVED: `0` and `1` are the interval's ends. -/
theorem readsClearWith_iff_leftoverNull (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) {γ e : ℝ}
    (he : IsEdge k γ e) :
    ReadReduce.ReadsClearWith a Ω k γ ↔ LeftoverNull a ha Ω e := by
  constructor
  · intro h
    refine leftoverNull_of_forall_gt a ha Ω e (fun s hs => ?_)
    have hs0 : 0 ≤ s := le_trans he.1 hs.le
    refine leftoverNull_of_contraction a ha hspec Ω hΩ hs0 (fun u hu => ?_)
    have h1 := FloorRead.contraction_of_readsClearWith a ha hspec Ω hΩ k γ h s hs0
      (he.2.2 s hs) u hu 1
    rw [pow_one, pow_one] at h1
    exact h1
  · intro h
    exact FloorRead.readsClearWith_of_contraction a ha hspec Ω hΩ k γ e he.1
      (contraction_of_leftoverNull a ha hspec Ω he.1 h) he.2.1

#print axioms readsClearWith_iff_leftoverNull

end Leftover

/-! ## 5. The leftover on transfer data -/

section LeftoverTransfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- Under `PositiveTransfer D` the spectrum of `opT D` lies in `[0, 1]`
(`GNSHilbert.spectrum_opT_nonneg`, `GNSHilbert.spectrum_opT_subset_unit_interval`).

DERIVED: `0` and `1` are the interval's ends. -/
theorem spec_unit_of_positive (D : TransferData A) (hP : PositiveTransfer D) :
    spectrum ℝ (opT D) ⊆ Set.Icc 0 1 := by
  intro x hx
  exact ⟨spectrum_opT_nonneg D hP hx, (spectrum_opT_subset_unit_interval D hx).2⟩

#print axioms spec_unit_of_positive

/-- **The gap is the vanishing leftover.** Under `PositiveTransfer D` and `0 ≤ r`: `GapAt D r` holds
exactly when every vector of the GNS space orthogonal to the vacuum has no spectral weight of `opT D`
on `(r, 1]` (`GNSCompare.gapAt_iff_opT_contracts`, `contraction_iff_leftoverNull`).

DERIVED: `0` is the lower end of `r`. -/
theorem gapAt_iff_leftoverNull (D : TransferData A) (hP : PositiveTransfer D) {r : ℝ}
    (hr : 0 ≤ r) :
    TransferGap.GapAt D r ↔
      LeftoverNull (opT D) (isSelfAdjoint_opT D) (Omega D.toReflForm D.vac) r :=
  (GNSCompare.gapAt_iff_opT_contracts D hr).trans
    (contraction_iff_leftoverNull (opT D) (isSelfAdjoint_opT D) (spec_unit_of_positive D hP)
      (Omega D.toReflForm D.vac) (opT_Omega D) hr)

#print axioms gapAt_iff_leftoverNull

end LeftoverTransfer

/-! ## 6. The zoom at the periodic state -/

section Wilson

open MassGap.AsymptoticScaling MassGap.PeriodicState

/-- The gauge-invariant half-space observables at rank `N`, the carrier of
`PeriodicState.periodicGaugeInvData τ p hN β` at every `β`.

DERIVED: `4` is the spacetime dimension. -/
abbrev Obs (N : ℕ) (τ : Fin 4) (p : ℤ) :=
  ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)

variable {N : ℕ}

/-- **The zoom is the renormalisation step.** At `0 ≤ β'`, halved spacing
`aRun N β' = aRun N β / 2` and `ZoomRepeat` from the periodic data at `β` to that at `β'`:
`GapStep.PhysStep τ p hN β β' M` at every `M`. The gap at rate `ρ = e^{−M·aRun N β}` gives the coarse
lag-one envelope `ρ` (`lagRatio_one_of_gapAt`), the zoom gives `GapAt` at `√ρ = e^{−M·aRun N β'}`
(`gapAt_sqrt_of_zoomRepeat`, `exp_half_sq`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β'`; `2` is the
halving. -/
theorem physStep_of_zoomRepeat (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' M : ℝ} (hβ' : 0 ≤ β')
    (hhalf : aRun N β' = aRun N β / 2)
    (hz : ZoomRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β')) :
    GapStep.PhysStep τ p hN β β' M := by
  intro hg
  have hsq : Real.exp (-(M * aRun N β')) = Real.sqrt (Real.exp (-(M * aRun N β))) := by
    rw [hhalf, ← exp_half_sq M (aRun N β), Real.sqrt_sq (Real.exp_pos _).le]
  rw [hsq]
  exact gapAt_sqrt_of_zoomRepeat _ _ (periodic_positiveTransfer τ p hN hβ') hz
    (Real.exp_pos _).le (lagRatio_one_of_gapAt _ (Real.exp_pos _).le hg)

#print axioms physStep_of_zoomRepeat

/-- **The per-observable Entroptic repeat on the even lags is the renormalisation step.** At
`0 ≤ β'`, `aRun N β' = aRun N β / 2` and `EvenRepeat` from `β` to `β'` through any `B`:
`GapStep.PhysStep τ p hN β β' M` at every `M` (`zoomRepeat_of_evenRepeat`, `physStep_of_zoomRepeat`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β'`; `2` is the
halving. -/
theorem physStep_of_evenRepeat (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' M : ℝ} (hβ' : 0 ≤ β')
    (hhalf : aRun N β' = aRun N β / 2) (B : Obs N τ p → Obs N τ p)
    (hrep : EvenRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β') B) :
    GapStep.PhysStep τ p hN β β' M :=
  physStep_of_zoomRepeat τ p hN hβ' hhalf (zoomRepeat_of_evenRepeat _ _ B hrep)

#print axioms physStep_of_evenRepeat

/-- **The zoom keeps the physical rate.** At `0 ≤ β'`, `aRun N β' = aRun N β / 2`, `ZoomRepeat` from
`β` to `β'`, `0 < r` and `GapAt` at `r` at `β`: `GapAt` at `√r` at `β'`, and
`−log √r / aRun N β' = −log r / aRun N β` (`GapStep.phys_rate_sqrt_half`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β'` and of `r`;
`2` is the halving. -/
theorem zoom_keeps_physical_rate (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' : ℝ} (hβ' : 0 ≤ β')
    (hhalf : aRun N β' = aRun N β / 2)
    (hz : ZoomRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β'))
    {r : ℝ} (hr : 0 < r) (hg : TransferGap.GapAt (periodicGaugeInvData τ p hN β) r) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β') (Real.sqrt r) ∧
      -Real.log (Real.sqrt r) / aRun N β' = -Real.log r / aRun N β := by
  refine ⟨gapAt_sqrt_of_zoomRepeat _ _ (periodic_positiveTransfer τ p hN hβ') hz hr.le
    (lagRatio_one_of_gapAt _ hr.le hg), ?_⟩
  rw [hhalf]
  exact GapStep.phys_rate_sqrt_half hr (aRun N β)

#print axioms zoom_keeps_physical_rate

/-- **`PhysStep` is the even-lag zoom of the envelope at one rate.** At `0 ≤ β` and `0 ≤ β'`:
`GapStep.PhysStep τ p hN β β' M` holds exactly when the coarse envelope at `e^{−M·aRun N β}` gives the
fine envelope at the even lags at `e^{−M·aRun N β'}` (`envelopeAt_iff_gapAt`,
`evenEnvelopeAt_iff_gapAt`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β` and `β'`. -/
theorem physStep_iff_evenZoom (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' M : ℝ} (hβ : 0 ≤ β)
    (hβ' : 0 ≤ β') :
    GapStep.PhysStep τ p hN β β' M ↔
      (EnvelopeAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
        EvenEnvelopeAt (periodicGaugeInvData τ p hN β') (Real.exp (-(M * aRun N β')))) := by
  rw [envelopeAt_iff_gapAt (periodicGaugeInvData τ p hN β) (periodic_positiveTransfer τ p hN hβ)
      (Real.exp_pos (-(M * aRun N β))).le,
    evenEnvelopeAt_iff_gapAt (periodicGaugeInvData τ p hN β') (periodic_positiveTransfer τ p hN hβ')
      (Real.exp_pos (-(M * aRun N β'))).le]
  rfl

#print axioms physStep_iff_evenZoom

/-- **At halved spacing, `PhysStep` is the decay-rate part of the block repeat.** At `0 ≤ β`,
`0 ≤ β'` and `aRun N β' = aRun N β / 2`, with `ρ = e^{−M·aRun N β}`:
`GapStep.PhysStep τ p hN β β' M` holds exactly when the coarse envelope `ρ^d` at every lag `d` gives the
fine envelope `ρ^d` at every lag `2d` (`physStep_iff_evenZoom`, `evenEnvelopeAt_half_iff`). It is
`ZoomRepeat` restricted to the one geometric envelope; it constrains no odd fine lag and no profile
beyond its envelope.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β`, `β'`; `2`
is the halving and the doubled lag. -/
theorem physStep_iff_envelope_zoom (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' M : ℝ} (hβ : 0 ≤ β)
    (hβ' : 0 ≤ β') (hhalf : aRun N β' = aRun N β / 2) :
    GapStep.PhysStep τ p hN β β' M ↔
      (EnvelopeAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
        ∀ d : ℕ, LagRatio (periodicGaugeInvData τ p hN β') (2 * d)
          (Real.exp (-(M * aRun N β)) ^ d)) := by
  rw [physStep_iff_evenZoom τ p hN hβ hβ', hhalf, evenEnvelopeAt_half_iff]

#print axioms physStep_iff_envelope_zoom

/-- **One physical gap along a halving sequence from the even-lag repeat.** At `2 ≤ N`, `0 < M`,
couplings `β_j > 0` with `aRun N β_{j+1} = aRun N β_j / 2`, maps `B j` with `EvenRepeat` from `β_j`
to `β_{j+1}`, and the gap at rate `e^{−M·aRun N β_0}` at `β_0`: at every `j`,
`PeriodicContent.PeriodicClayGapAt τ p hN β_j (e^{−M·aRun N β_j})` with physical rate `M`
(`physStep_of_evenRepeat`, `GapStep.periodic_clay_tower`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance and the
halving; `0` is the excluded rank, the base index and the sign of `M` and of each `β_j`; `1` is the
step to the next index. -/
theorem periodic_clay_tower_of_evenRepeat (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j) (M : ℝ) (hM : 0 < M)
    (hhalf : ∀ j, aRun N (β (j + 1)) = aRun N (β j) / 2) (B : ℕ → Obs N τ p → Obs N τ p)
    (hrep : ∀ j, EvenRepeat (periodicGaugeInvData τ p hN (β j))
      (periodicGaugeInvData τ p hN (β (j + 1))) (B j))
    (hbase : TransferGap.GapAt (periodicGaugeInvData τ p hN (β 0))
      (Real.exp (-(M * aRun N (β 0))))) :
    ∀ j, PeriodicContent.PeriodicClayGapAt τ p hN (β j) (Real.exp (-(M * aRun N (β j))))
      ∧ -Real.log (Real.exp (-(M * aRun N (β j)))) / aRun N (β j) = M :=
  GapStep.periodic_clay_tower τ p hN2 hN β hβ M hM hbase
    (fun j => physStep_of_evenRepeat τ p hN (hβ (j + 1)).le (hhalf j) (B j) (hrep j))

#print axioms periodic_clay_tower_of_evenRepeat

/-- **The physical integral length under the verbatim repeat.** At `aRun N β' = aRun N β / 2`,
`LiteralRepeat` from `β` to `β'` and `x` orthogonal to the fine vacuum:
`aRun N β' · integralLength D' x (2n) = aRun N β · integralLength D (B x) n`
(`integralLength_literal`). `literalRepeat_no_gap` restricts its instances at a gapped `β'` to null `x`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the vacuum pairing; `2` is the
halving and the block factor. -/
theorem physLength_literal (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' : ℝ}
    (hhalf : aRun N β' = aRun N β / 2) (B : Obs N τ p → Obs N τ p)
    (h : LiteralRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β') B)
    {x : Obs N τ p}
    (hx : (periodicGaugeInvData τ p hN β').form x (periodicGaugeInvData τ p hN β').vac = 0)
    (n : ℕ) :
    aRun N β' * integralLength (periodicGaugeInvData τ p hN β') x (2 * n)
      = aRun N β * integralLength (periodicGaugeInvData τ p hN β) (B x) n := by
  rw [hhalf, integralLength_literal _ _ B h hx n]
  ring

#print axioms physLength_literal

/-- **The verbatim Entroptic repeat excludes a gap at the finer coupling, at the periodic state.**
Under `LiteralRepeat` from the periodic data at `β` to that at `β'` through any `B`, an observable `x`
orthogonal to the vacuum at `β'` with `0 < D'.form x x` excludes `GapAt` at `β'` at every
`0 ≤ r < 1` (`literalRepeat_no_gap`): the block identity `f' (2i + k) = f i` puts the lag-one ratio at
`β'` at its lag-zero value `1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the vacuum pairing, the sign of the
lag-zero value and the lower end of `r`; `1` is the upper end of `r`. -/
theorem periodic_literalRepeat_no_gap (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' : ℝ}
    (B : Obs N τ p → Obs N τ p)
    (h : LiteralRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β') B)
    {x : Obs N τ p}
    (hx : (periodicGaugeInvData τ p hN β').form x (periodicGaugeInvData τ p hN β').vac = 0)
    (hpos : 0 < (periodicGaugeInvData τ p hN β').form x x) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ¬ TransferGap.GapAt (periodicGaugeInvData τ p hN β') r :=
  literalRepeat_no_gap _ _ B h hx hpos hr0 hr1

#print axioms periodic_literalRepeat_no_gap

/-- **The physical integral length under the even repeat.** At `0 ≤ β'`, `0 ≤ aRun N β`,
`aRun N β' = aRun N β / 2`, `EvenRepeat` from `β` to `β'` and `x` orthogonal to the fine vacuum,
with `ξ = integralLength D (B x) n`, `f = ratioProfile D (B x)` and `ξ' = integralLength D' x (2n)`:
`aRun N β · ξ − (aRun N β / 2)·(f 0 − f n) ≤ aRun N β' · ξ' ≤ aRun N β · ξ`
(`integralLength_even_bounds`, `half_mul_bounds`). The physical integral length is unchanged up to
half a coarse spacing times `f 0 − f n`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β'` and of the
spacing, the vacuum pairing and the first lag; `2` is the halving and the block factor. -/
theorem physLength_even_bounds (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' : ℝ} (hβ' : 0 ≤ β')
    (ha : 0 ≤ aRun N β) (hhalf : aRun N β' = aRun N β / 2) (B : Obs N τ p → Obs N τ p)
    (h : EvenRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β') B)
    {x : Obs N τ p}
    (hx : (periodicGaugeInvData τ p hN β').form x (periodicGaugeInvData τ p hN β').vac = 0)
    (n : ℕ) :
    aRun N β * integralLength (periodicGaugeInvData τ p hN β) (B x) n
        - aRun N β / 2 * (ratioProfile (periodicGaugeInvData τ p hN β) (B x) 0
          - ratioProfile (periodicGaugeInvData τ p hN β) (B x) n)
        ≤ aRun N β' * integralLength (periodicGaugeInvData τ p hN β') x (2 * n) ∧
      aRun N β' * integralLength (periodicGaugeInvData τ p hN β') x (2 * n)
        ≤ aRun N β * integralLength (periodicGaugeInvData τ p hN β) (B x) n := by
  obtain ⟨hlo, hhi⟩ := integralLength_even_bounds _ _ B h
    (periodic_positiveTransfer τ p hN hβ') hx n
  rw [hhalf]
  exact half_mul_bounds ha hlo hhi

#print axioms physLength_even_bounds

/-- **THE WILSON HYPOTHESIS: the signal is the same under zoom, up to a loss.** For every two couplings
`β, β' ≥ βUV` one block step apart (`aRun N β / 2 ≤ aRun N β' ≤ aRun N β`) and every `M`: the coarse
envelope at rate `e^{−M·aRun N β}` gives the fine envelope at the even lags at rate
`e^{−(M − ε(aRun N β))·aRun N β'}`. The odd fine lags are free. At exact halving the fine profile at
lag `2d` is bounded by the coarse envelope at lag `d` less the loss (`evenEnvelopeAt_half_iff`); in
between, by the coarse envelope transported to the same physical separation.

This is an input: the tree proves no instance of it past the strong-coupling region. At `0 ≤ βUV` it
is `UVIRSplit.UVLossStep τ p hN βUV ε` (`zoomInvariantWith_iff_uvLossStep`). Its content is carried
together with `UVIRSplit.VanishingLoss ε` or a loss budget below the IR rate: with `ε(a)` at least
the largest physical rate attainable at spacing `a`, every conclusion is a rate at least one and holds
for every transfer data.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank; `2` is the block factor of
`UVIRSplit.LossStep`. -/
def ZoomInvariantWith (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (βUV : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
    ∀ M : ℝ, EnvelopeAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
      EvenEnvelopeAt (periodicGaugeInvData τ p hN β')
        (Real.exp (-((M - ε (aRun N β)) * aRun N β')))

/-- **The zoom hypothesis is the UV block step.** At `0 ≤ βUV`:
`ZoomInvariantWith τ p hN βUV ε ↔ UVIRSplit.UVLossStep τ p hN βUV ε` (`envelopeAt_iff_gapAt`,
`evenEnvelopeAt_iff_gapAt`, positivity of the transfer at every `β ≥ 0`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `βUV`. -/
theorem zoomInvariantWith_iff_uvLossStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {βUV : ℝ}
    (hUV : 0 ≤ βUV) (ε : ℝ → ℝ) :
    ZoomInvariantWith τ p hN βUV ε ↔ UVIRSplit.UVLossStep τ p hN βUV ε := by
  constructor
  · intro h β β' h1 h2 h3 h4 M hg
    exact gapAt_of_evenEnvelopeAt (periodicGaugeInvData τ p hN β')
      (periodic_positiveTransfer τ p hN (hUV.trans h2)) (Real.exp_pos _).le
      (h β β' h1 h2 h3 h4 M
        (envelopeAt_of_gapAt (periodicGaugeInvData τ p hN β) (Real.exp_pos _).le hg))
  · intro h β β' h1 h2 h3 h4 M he
    exact evenEnvelopeAt_of_gapAt (periodicGaugeInvData τ p hN β') (Real.exp_pos _).le
      (h β β' h1 h2 h3 h4 M
        (gapAt_of_envelopeAt (periodicGaugeInvData τ p hN β)
          (periodic_positiveTransfer τ p hN (hUV.trans h1)) (Real.exp_pos _).le he))

#print axioms zoomInvariantWith_iff_uvLossStep

/-- **The Entroptic zoom supplies the exact-halving clause at zero loss.** At halved spacing
`aRun N β' = aRun N β / 2` and `ZoomRepeat` from `β` to `β'`: the coarse envelope at
`e^{−M·aRun N β}` gives the fine even envelope at `e^{−M·aRun N β'}`, lag by lag
(`evenEnvelopeAt_half_iff`): `ZoomInvariantWith`'s clause at that pair with `ε(aRun N β) = 0`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank; `2` is the halving. -/
theorem evenEnvelope_of_zoomRepeat (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β β' : ℝ}
    (hhalf : aRun N β' = aRun N β / 2)
    (hz : ZoomRepeat (periodicGaugeInvData τ p hN β) (periodicGaugeInvData τ p hN β')) (M : ℝ)
    (he : EnvelopeAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β)))) :
    EvenEnvelopeAt (periodicGaugeInvData τ p hN β') (Real.exp (-(M * aRun N β'))) := by
  rw [hhalf]
  exact (evenEnvelopeAt_half_iff _ M (aRun N β)).mpr (fun d => hz d _ (he d))

#print axioms evenEnvelope_of_zoomRepeat

/-- **The zoom hypothesis with its IR base gives the uniform physical gap.** At `2 ≤ N`, `0 < L`,
`0 ≤ βUV ≤ β₀`, `0 < β₀`, a loss budget `E < M₀` below `aRun N β₀`, `ZoomInvariantWith τ p hN βUV ε`
and `UVIRSplit.IRGapAt τ p hN β₀ M₀`: `WeakCouplingWindow.FixedWindowDecay τ p hN L`
(`zoomInvariantWith_iff_uvLossStep`, `UVIRSplit.fixedWindowDecay_of_uv_ir`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L`, `βUV` and `β₀`. -/
theorem fixedWindowDecay_of_zoom (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV β₀ M₀ E : ℝ} {ε : ℝ → ℝ} (hUV : 0 ≤ βUV) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hbudget : UVIRSplit.LossBudget ε (aRun N β₀) E) (hEM : E < M₀)
    (hz : ZoomInvariantWith τ p hN βUV ε) (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L :=
  UVIRSplit.fixedWindowDecay_of_uv_ir τ p hN2 hN hL hβ₀ hUVβ₀ hbudget hEM
    ((zoomInvariantWith_iff_uvLossStep τ p hN hUV ε).mp hz) hir

#print axioms fixedWindowDecay_of_zoom

/-- The zero loss has budget `0` below every spacing.

DERIVED: `0` is the loss and the budget. -/
theorem lossBudget_zero (a₀ : ℝ) : UVIRSplit.LossBudget (fun _ : ℝ => (0 : ℝ)) a₀ 0 := by
  intro n
  simp

#print axioms lossBudget_zero

/-- **The lossless zoom with its IR base.** At `2 ≤ N`, `0 < L`, `0 ≤ βUV ≤ β₀`, `0 < β₀`, `0 < M₀`,
`ZoomInvariantWith τ p hN βUV 0` and `UVIRSplit.IRGapAt τ p hN β₀ M₀`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L` (`fixedWindowDecay_of_zoom` at `E = 0`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank, the loss, and the sign of `L`, `βUV`, `β₀` and `M₀`. -/
theorem fixedWindowDecay_of_zoom_zero (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV β₀ M₀ : ℝ} (hUV : 0 ≤ βUV) (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hM₀ : 0 < M₀) (hz : ZoomInvariantWith τ p hN βUV (fun _ => 0))
    (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L :=
  fixedWindowDecay_of_zoom τ p hN2 hN hL hUV hβ₀ hUVβ₀ (lossBudget_zero (aRun N β₀)) hM₀ hz hir

#print axioms fixedWindowDecay_of_zoom_zero

/-- **THE OPEN UV INPUT, as zoom invariance.** Some threshold `βUV ≥ 0` and loss `ε` with
`UVIRSplit.VanishingLoss ε` have `ZoomInvariantWith τ p hN βUV ε`: the signal survives every block
step above `βUV`, and the losses of the dyadic tower below a spacing tend to zero with it.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `βUV`. -/
def ZoomInvariant (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  ∃ βUV : ℝ, 0 ≤ βUV ∧ ∃ ε : ℝ → ℝ, UVIRSplit.VanishingLoss ε ∧ ZoomInvariantWith τ p hN βUV ε

/-- **Zoom invariance is the UV input.** `ZoomInvariant τ p hN ↔ UVIRSplit.UVInput τ p hN`. Back:
`UVLossStep` above `βUV` holds above `max βUV 0`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. The proof's `max βUV 0` puts the
threshold at or above `0`. -/
theorem zoomInvariant_iff_uvInput (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ZoomInvariant τ p hN ↔ UVIRSplit.UVInput τ p hN := by
  constructor
  · rintro ⟨βUV, hUV, ε, hvan, hz⟩
    exact ⟨βUV, ε, hvan, (zoomInvariantWith_iff_uvLossStep τ p hN hUV ε).mp hz⟩
  · rintro ⟨βUV, ε, hvan, huv⟩
    refine ⟨max βUV 0, le_max_right _ _, ε, hvan,
      (zoomInvariantWith_iff_uvLossStep τ p hN (le_max_right _ _) ε).mpr ?_⟩
    intro β β' h1 h2 h3 h4 M hg
    exact huv β β' ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) h3 h4 M hg

#print axioms zoomInvariant_iff_uvInput

/-- **Under zoom invariance, the uniform gap is the gap at one coupling.** At `2 ≤ N`, `0 < L` and
`ZoomInvariant τ p hN`: some `βUV`, `ε` have `ZoomInvariantWith τ p hN βUV ε`, and
`FixedWindowDecay τ p hN L` holds exactly when some `β₀ ≥ βUV`, `β₀ > 0`, has
`UVIRSplit.IRGapAt τ p hN β₀ M₀` with a loss budget `E < M₀` below `aRun N β₀`
(`UVIRSplit.fixedWindowDecay_iff_irGapAt`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L` and `β₀`. -/
theorem fixedWindowDecay_iff_irGapAt_of_zoom (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) (h : ZoomInvariant τ p hN) :
    ∃ βUV : ℝ, ∃ ε : ℝ → ℝ, ZoomInvariantWith τ p hN βUV ε ∧
      (WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
        ∃ β₀ M₀ E : ℝ, 0 < β₀ ∧ βUV ≤ β₀ ∧ UVIRSplit.LossBudget ε (aRun N β₀) E ∧ E < M₀ ∧
          UVIRSplit.IRGapAt τ p hN β₀ M₀) := by
  obtain ⟨βUV, hUV, ε, hvan, hz⟩ := h
  exact ⟨βUV, ε, hz, UVIRSplit.fixedWindowDecay_iff_irGapAt τ p hN2 hN hL hvan
    ((zoomInvariantWith_iff_uvLossStep τ p hN hUV ε).mp hz)⟩

#print axioms fixedWindowDecay_iff_irGapAt_of_zoom

/-! ## 7. The leftover at the periodic state -/

/-- **The leftover at the periodic state vanishes past `s`**: every vector of the gauge-invariant GNS
space at coupling `β` orthogonal to the vacuum has no spectral weight of `opT` on `(s, 1]`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
abbrev PeriodicLeftoverNull (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β s : ℝ) : Prop :=
  LeftoverNull (opT (periodicGaugeInvData τ p hN β)) (isSelfAdjoint_opT (periodicGaugeInvData τ p hN β))
    (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) s

/-- **At the periodic state the gap is the vanishing leftover.** At `0 ≤ β` and `0 ≤ r`:
`GapAt (periodicGaugeInvData τ p hN β) r ↔ PeriodicLeftoverNull τ p hN β r`
(`gapAt_iff_leftoverNull`, `PeriodicState.periodic_positiveTransfer`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β` and `r`. -/
theorem periodic_gapAt_iff_leftoverNull (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    {r : ℝ} (hr : 0 ≤ r) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) r ↔ PeriodicLeftoverNull τ p hN β r :=
  gapAt_iff_leftoverNull _ (periodic_positiveTransfer τ p hN hβ) hr

#print axioms periodic_gapAt_iff_leftoverNull

/-- **The torus read at an aperture is the vanishing leftover past its edge.** At `0 ≤ β` and an edge
`e` of the aperture `2k + 1` at margin `γ`: `PeriodicReduce.TorusReadsClearWith τ p hN β k γ` holds
exactly when `PeriodicLeftoverNull τ p hN β e`. Forward: `FloorRead.periodic_contraction_of_torusReads`
at every `s > e`, then `leftoverNull_of_forall_gt`. Back: `FloorRead.periodic_torusReads_of_contraction`
at `e`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β`. -/
theorem torusReads_iff_leftoverNull (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (k : ℕ) {γ e : ℝ} (he : IsEdge k γ e) :
    PeriodicReduce.TorusReadsClearWith τ p hN β k γ ↔ PeriodicLeftoverNull τ p hN β e := by
  constructor
  · intro ht
    refine leftoverNull_of_forall_gt _ _ _ e (fun s hs => ?_)
    have hs0 : 0 ≤ s := le_trans he.1 hs.le
    have hcon : ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
        inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
          (periodicGaugeInvData τ p hN β).vac) u = (0 : ℂ) →
        ‖opT (periodicGaugeInvData τ p hN β) u‖ ≤ s * ‖u‖ := by
      intro u hu
      have h1 := FloorRead.periodic_contraction_of_torusReads τ p hN hβ k γ ht s hs0
        (he.2.2 s hs) u hu 1
      rw [pow_one, pow_one] at h1
      exact h1
    exact (periodic_gapAt_iff_leftoverNull τ p hN hβ hs0).mp
      ((GNSCompare.gapAt_iff_opT_contracts _ hs0).mpr hcon)
  · intro h
    have hg := (periodic_gapAt_iff_leftoverNull τ p hN hβ he.1).mpr h
    exact FloorRead.periodic_torusReads_of_contraction τ p hN hβ k γ e he.1
      ((GNSCompare.gapAt_iff_opT_contracts _ he.1).mp hg) he.2.1

#print axioms torusReads_iff_leftoverNull

/-- **The torus read at `(k, γ)` is the leftover past `r_γ(k)`.** At `0 ≤ β` and
`0 < γ ≤ modeCosAvg k 0`: `PeriodicReduce.TorusReadsClearWith τ p hN β k γ` holds exactly when
`PeriodicLeftoverNull τ p hN β (readEdge k γ)`, and `readEdge k γ < 1` (`isEdge_readEdge`,
`torusReads_iff_leftoverNull`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β`, the sign of
`γ` and the rate at which `modeCosAvg k` is largest; `1` is the massless mode. -/
theorem torusReads_iff_leftoverNull_readEdge (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (k : ℕ) {γ : ℝ} (hγ : 0 < γ) (hγ0 : γ ≤ ReadConverse.modeCosAvg k 0) :
    (PeriodicReduce.TorusReadsClearWith τ p hN β k γ ↔
      PeriodicLeftoverNull τ p hN β (readEdge k γ)) ∧ readEdge k γ < 1 :=
  ⟨torusReads_iff_leftoverNull τ p hN hβ k (isEdge_readEdge k hγ hγ0).1,
    (isEdge_readEdge k hγ hγ0).2⟩

#print axioms torusReads_iff_leftoverNull_readEdge

/-- **THE LEFTOVER IS INVARIANT UNDER ZOOM.** There is one factor `q ∈ (0, 1)` such that at every
large `β` a window of `m ≥ 1` lattice steps of physical length `m · aRun N β ≤ L` has diffraction rate
`q^{1/m}` (`WeakCouplingWindow.stepRate`), past which every vacuum-orthogonal vector of the
gauge-invariant GNS space at `β` carries no spectral weight of `opT`: what lies outside the aperture
held at physical size `L` is empty at every zoom. `q` and `L` do not depend on `β`.

It is the weak-coupling input `WeakCouplingWindow.FixedWindowDecay τ p hN L` in spectral form:
`leftoverInvariant_iff_fixedWindowDecay` identifies the two.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `q` and the
excluded lag; `1` is the upper end of `q`. `L` is the caller's window. -/
def LeftoverInvariant (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ β in Filter.atTop, ∃ m : ℕ, m ≠ 0 ∧
    (m : ℝ) * aRun N β ≤ L ∧ PeriodicLeftoverNull τ p hN β (WeakCouplingWindow.stepRate q m)

/-- **The invariant leftover is the fixed-window decay.**
`LeftoverInvariant τ p hN L ↔ WeakCouplingWindow.FixedWindowDecay τ p hN L`. At each large `β ≥ 0`
and window `m`, `PeriodicLeftoverNull` at `q^{1/m}` is `GapAt` at `q^{1/m}`
(`periodic_gapAt_iff_leftoverNull`), which is `ChessboardRead.TorusLagClear` at `q^{1/m}`
(`WeakCouplingWindow.torusLagClear_iff_gapAt`, `WeakCouplingWindow.torusLagClear_of_gapAt`), whose
factor `(q^{1/m})ᵐ` is `q` (`WeakCouplingWindow.stepRate_pow`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. The proof's `0` is the lower end
of `β`. -/
theorem leftoverInvariant_iff_fixedWindowDecay (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) :
    LeftoverInvariant τ p hN L ↔ WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  constructor
  · rintro ⟨q, hq0, hq1, hev⟩
    refine ⟨q, hq0, hq1, ?_⟩
    filter_upwards [hev, Filter.eventually_ge_atTop (0 : ℝ)] with β hβ hβ0
    obtain ⟨m, hm, hwin, hnull⟩ := hβ
    refine ⟨m, hm, hwin, ?_⟩
    have hr : 0 ≤ WeakCouplingWindow.stepRate q m := (WeakCouplingWindow.stepRate_pos hq0 m).le
    have hg := (periodic_gapAt_iff_leftoverNull τ p hN hβ0 hr).mpr hnull
    have ht := WeakCouplingWindow.torusLagClear_of_gapAt τ p hN β hr hg m
    intro x hx ε hε
    have h := ht x hx ε hε
    rw [WeakCouplingWindow.stepRate_pow hq0.le hm] at h
    exact h
  · rintro ⟨q, hq0, hq1, hev⟩
    refine ⟨q, hq0, hq1, ?_⟩
    filter_upwards [hev, Filter.eventually_ge_atTop (0 : ℝ)] with β hβ hβ0
    obtain ⟨m, hm, hwin, hlag⟩ := hβ
    refine ⟨m, hm, hwin, ?_⟩
    have hr : 0 ≤ WeakCouplingWindow.stepRate q m := (WeakCouplingWindow.stepRate_pos hq0 m).le
    exact (periodic_gapAt_iff_leftoverNull τ p hN hβ0 hr).mp
      ((WeakCouplingWindow.torusLagClear_iff_gapAt τ p hN hβ0 hm hr).mp
        (WeakCouplingWindow.torusLagClear_stepRate τ p hN β hq0.le hm hlag))

#print axioms leftoverInvariant_iff_fixedWindowDecay

/-- **The invariant leftover is the physical gap.** At `2 ≤ N` and `0 < L`:
`LeftoverInvariant τ p hN L` holds exactly when some `c > 0` has, at every large `β`, a rate `r` with
`PeriodicContent.PeriodicClayGapAt τ p hN β r` and `c / L ≤ −log r / aRun N β`
(`leftoverInvariant_iff_fixedWindowDecay`, `WeakCouplingWindow.fixedWindowDecay_iff`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the lower end of `L` and `c`. -/
theorem leftoverInvariant_iff_physical_gap (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    LeftoverInvariant τ p hN L ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ β in Filter.atTop, ∃ r : ℝ,
      PeriodicContent.PeriodicClayGapAt τ p hN β r ∧ c / L ≤ -Real.log r / aRun N β :=
  (leftoverInvariant_iff_fixedWindowDecay τ p hN L).trans
    (WeakCouplingWindow.fixedWindowDecay_iff τ p hN2 hN hL)

#print axioms leftoverInvariant_iff_physical_gap

/-- **Zoom invariance with its IR base leaves the leftover invariant.** Under the hypotheses of
`fixedWindowDecay_of_zoom`: `LeftoverInvariant τ p hN L`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L`, `βUV` and `β₀`. -/
theorem leftoverInvariant_of_zoom (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV β₀ M₀ E : ℝ} {ε : ℝ → ℝ} (hUV : 0 ≤ βUV) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hbudget : UVIRSplit.LossBudget ε (aRun N β₀) E) (hEM : E < M₀)
    (hz : ZoomInvariantWith τ p hN βUV ε) (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) :
    LeftoverInvariant τ p hN L :=
  (leftoverInvariant_iff_fixedWindowDecay τ p hN L).mpr
    (fixedWindowDecay_of_zoom τ p hN2 hN hL hUV hβ₀ hUVβ₀ hbudget hEM hz hir)

#print axioms leftoverInvariant_of_zoom

/-- **An invariant leftover gives the step at one physical rate between large couplings.** At
`2 ≤ N`, `0 < L` and `LeftoverInvariant τ p hN L`: some `M > 0` and `β₁` have
`GapStep.PhysStep τ p hN β β' M` for every `β, β' ≥ β₁`, the conclusion `UVIRSplit.IRGapAt τ p hN β' M`
holding outright (`UVIRSplit.irGapAt_of_fixedWindowDecay`). This is the decay-rate part of the zoom at
the one rate `M`; `ZoomInvariantWith` asks the step at every `M`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L` and `M`. -/
theorem physStep_eventually_of_leftoverInvariant (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) (h : LeftoverInvariant τ p hN L) :
    ∃ M : ℝ, 0 < M ∧ ∃ β₁ : ℝ, ∀ β β' : ℝ, β₁ ≤ β → β₁ ≤ β' → GapStep.PhysStep τ p hN β β' M := by
  obtain ⟨M, hM, hev⟩ := UVIRSplit.irGapAt_of_fixedWindowDecay τ p hN2 hN hL
    ((leftoverInvariant_iff_fixedWindowDecay τ p hN L).mp h)
  obtain ⟨β₁, hβ₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨M, hM, β₁, ?_⟩
  intro β β' _ hβ' _
  exact hβ₁ β' hβ'

#print axioms physStep_eventually_of_leftoverInvariant

end Wilson

end MassGap.ZoomStep
