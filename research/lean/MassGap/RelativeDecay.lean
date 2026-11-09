import Mathlib
import MassGap.TorusPassageProof
import MassGap.ContinuumCluster

noncomputable section

/-!
# MassGap.RelativeDecay — the gap's decay measured against the reading, and where a torus needs more

## Where the sup norm enters the tree's torus decay

`TorusDecay.dyadic_torus_decay` closes through `ChainDecay.chain_decay`. Its gap step
(`ChainDecay.gap_ineq`, read as `hgv`) is already relative: the vacuum sandwich of the pairing at lag `n`
is at most `½` times the vacuum sandwich at contact, with no constant. The sup norm `B` of `x` enters only
in `ChainDecay.E_close` / `ChainDecay.ratio_close`, which replace each closed-chain (trace) expectation on
the torus by its vacuum sandwich: the excited part of the trace with insertion `G` is bounded by
`B_G · Λ · √(2s)`, `B_G` a bound of `|G|`, i.e. the operator norm of multiplication by `G` on the excited
states, and `s` the excited weight of the torus. `ChainDecay.combine` then assembles `100 B² √(2s)`.

## Relative decay where the state is a vector state (proved)

On any `Transfer.TransferData D` with `TransferGap.GapAt D r`, `0 ≤ r`, and `y = vacProj D x`:

* `conn_eq_vacProj`: the connected pairing `form x (Tⁿ x) − form x Ω · form Ω x` is `form y (Tⁿ y)`.
* `conn_abs_le`: `|form y (Tⁿ y)| ≤ rⁿ · form y y`: decay relative to the contact value, every `n`.
* `conn_rel_step`: `form y (T^{2(m+d)} y) ≤ r^{2d} · form y (T^{2m} y)`: decay relative to the reading
  at the smaller separation itself; `conn_even_nonneg`: those readings are `≥ 0`.

No sup norm and no additive term occurs. `RelDecayAt D r` bundles the two bounds;
`relDecayAt_of_gapAt` proves it.

## The gap in relative form, from `WDelta2`, in infinite volume (proved)

`relDecay_of_WDelta2`: at `2 ≤ N`, `ℓ₀ > 0` and `WDelta2 N ℓ₀`, there is `c > 0` such that eventually in
`k` the transfer data `Dk hN k` of the infinite-volume periodic state at `dyBeta k` (whose form is the
reflected pairing in `stateK hN k`, `ContinuumCluster.DkAlong_form`) has a rate `r > 0` with
`rⁿ ≤ exp(−(c/(5ℓ₀)) · dySpacing N k · n)` and `RelDecayAt (Dk hN k) r`. The absolute `ε` of
`FixedWindowDecay` is removed by its own ultralimit (`gapAt_physical_of_fixedWindowDecay`), so the gap is
available relatively in infinite volume. It is not available on any single finite torus.

## On a finite torus the trace state carries a floor no relative bound removes (proved, witness)

`wTorusConn μ L n` is the connected pairing of the closed chain of length `L` for the two-level kernel
`diag(1, μ)` and the insertion `diag(0, 1)`; `wVacConn μ n` is its vacuum sandwich. At every `0 < μ`
(every gap `1 − μ`) and `n ≤ L`:

* `wTorusConn_eq`: `wTorusConn μ L n = p − p²`, `p = μᴸ/(1 + μᴸ)`, the same at every lag;
* `wVacConn_eq`: `wVacConn μ n = 0`;
* `wTorus_no_relative_decay`: `rⁿ · wTorusConn μ L 0 < wTorusConn μ L n` at `1 ≤ n`, `0 ≤ r < 1`;
* `wTorus_not_vacuum_relative`: no `δ` has `|wTorusConn − wVacConn| ≤ δ · wVacConn`.

So the trace-to-vacuum step on a finite torus cannot be bounded relative to the vacuum reading or by a
decaying multiple of the torus's own contact reading: it needs a quantity on the excited states, which
`chain_decay` supplies as the sup norm and `Zh_close_rel` (section 6) as the torus second moment. The witness has no gauge content; it shows the gap hypothesis
alone does not give the relative bound.

## A dyadic torus of exactly fixed physical side (proved)

`stateTD hN c k = torusState hN (2(2^{c+k} − 1) + 1) (dyBeta k)` has extent `2^{c+k+1}`
(`stateTD_extent`, `stateTD_isPow2`), physical side exactly `2^c · aRun N 1` (`stateTD_physical_side`),
and its index lies in every dyadic seed set of `PeriodicDyadic.periodicUltra_seed_mem` with `a ≤ c + k`
(`stateTD_seed`). This removes `TorusPassageProof.stateT_extent_not_pow2` as a constraint. It does not
put `dyadic_torus_decay` on that torus: that theorem holds eventually along `periodicUltra`, which
contains no single index.

## `hpos` against any per-step state

`hpos_of_relS`: for any `σ`, `0 < refReadingS σ` eventually and
`|refReading − refReadingS σ| ≤ ε · refReadingS σ` eventually at `ε < 1` give the pinned `hpos`.
`clay_canonical_relS` is `ExistenceReduce.clay_canonical` with `hpos` so replaced; at `σ = stateT hN M₀`
the two inputs are `TorusRefPos` and `RefPassage`, at `σ = stateTD hN c` they are the same on the dyadic
torus. `refRel_of_relInf`: a bound `|refReading − refReadingS σ| ≤ δ · refReading` measured against the
infinite-volume reading, at `0 ≤ δ < 1`, gives the bound against the torus reading at `δ/(1 − δ)`.

## The closing error with second moments in place of the sup norm (proved)

The sup norm's one root is `ChainClosing.Ins F B` used as `B²` in `ChainClosing.insert_sq_le`. Here the
same closing is bounded in the chain measure:

* `chain_cs_L2`: `(∫ₓ chain (F · g(V, x)) x)² ≤ (∫ₓ chain (F² |g(V, x)|) x) · ∫ₓ∫_z k^{∗m}(x,z) |g(z,x)|`,
  Cauchy–Schwarz for the positive functional `∫ₓ chain (·) x`;
* `iter_abs_sq_le`: the last factor squared is at most `hs(k^{∗m}) · ∫∫ g²`;
* `Zh_decomp_L2`: the closing error `Zh F − c^{m+1} Ih F` squared is at most the chain second moment of `F`
  weighted by `|r^{∗m}|` times that factor;
* `secondMoment_le`: the weighted second moment is at most `Zh(F²) + |c|^{m+1} Ih_{|φ|}(F²)`
  (`iter_kern_nonneg`: the kernel powers are nonnegative);
* `Zh_close_rel`: `(Zh F − c^{m+1} Ih F)⁴ ≤ (Zh(F²) + |c|^{m+1} Ih_{|φ|}(F²))² · hs(k^{∗m}) · hs(r^{∗m})`.

`B` enters these only through integrability. After normalising by `|c|^{2(m+1)}` the closing error is at
most the square root of the torus and `|φ|`-vacuum second moments of `F` times
`(s (1 + s))^{1/4}` (argued from `hs(k^{∗m}) = |c|^{2(m+1)} + hs(r^{∗m})`), against `√(2s) · 6B` in
`ChainDecay.E_close`.

## What stays open

`RefPassage` (and its dyadic analogue) is not proved here. Two comparisons separate the infinite-volume
reading from a torus reading:

1. trace state to the vacuum of the torus's own slice: `Zh_close_rel` makes this relative to the second
   moments of the insertion. Relative to the reading it needs `√(second moment) · s^{1/4} ≤ ε · reading`,
   i.e. a lower bound on the reading against the insertion's second moment; with `s ≤ (1/2)^{2^d}` at
   dyadic depth `d` (`DoublingSharp.excited_le_corner_sharp`), a polynomial lower bound `reading ≥ aᵖ ·
   second moment` would suffice at depth `2^d ≳ p log₂(1/a)` (argued);
2. the vacuum of the torus's slice (`hS 0 (Tc M) N`, a spatial torus of side `M`) to the infinite-volume
   state `stateK`: the tree has no comparison of two slices, so no bound of either kind exists here.
-/

namespace MassGap.RelativeDecay

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.TransferGap Filter

/-! ## 1. Relative decay on a transfer form -/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The connected pairing is the pairing of the vacuum-orthogonal part.** -/
theorem conn_eq_vacProj (D : Transfer.TransferData A) (n : ℕ) (x : A) :
    D.form x ((D.T ^ n) x) - D.form x D.vac * D.form D.vac x
      = D.form (vacProj D x) ((D.T ^ n) (vacProj D x)) := by
  have hsplit : (D.T ^ n) x = (D.form x D.vac) • D.vac + (D.T ^ n) (vacProj D x) := by
    conv_lhs => rw [← vacProj_add D x]
    rw [map_add, map_smul, pow_vac D n]
  have hvy : D.form D.vac ((D.T ^ n) (vacProj D x)) = 0 := by
    rw [← form_pow_symm D n D.vac (vacProj D x), pow_vac D n, D.toPreForm.form_symm]
    exact vacProj_orth D x
  have hx : D.form x ((D.T ^ n) (vacProj D x))
      = D.form (vacProj D x) ((D.T ^ n) (vacProj D x)) := by
    calc D.form x ((D.T ^ n) (vacProj D x))
        = D.form ((D.form x D.vac) • D.vac + vacProj D x) ((D.T ^ n) (vacProj D x)) := by
          rw [vacProj_add D x]
      _ = D.form (vacProj D x) ((D.T ^ n) (vacProj D x)) := by
          rw [D.toPreForm.form_add_left, D.toPreForm.form_smul_left, hvy, mul_zero, zero_add]
  rw [hsplit, D.toPreForm.form_add_right, D.toPreForm.form_smul_right, hx,
    D.toPreForm.form_symm D.vac x]
  ring

/-- `vacProj` of a vacuum-orthogonal vector is itself. -/
theorem vacProj_vacProj (D : Transfer.TransferData A) (x : A) :
    vacProj D (vacProj D x) = vacProj D x := by
  show vacProj D x - (D.form (vacProj D x) D.vac) • D.vac = vacProj D x
  rw [vacProj_orth D x, zero_smul, sub_zero]

/-- **Decay relative to the contact value**: `|form y (Tⁿ y)| ≤ rⁿ · form y y`, `y = vacProj D x`. -/
theorem conn_abs_le (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) (n : ℕ)
    (x : A) :
    |D.form (vacProj D x) ((D.T ^ n) (vacProj D x))|
      ≤ r ^ n * D.form (vacProj D x) (vacProj D x) := by
  set y := vacProj D x with hy
  have h := clustering_sq D hr hg n y y
  have hy0 : D.form y D.vac = 0 := vacProj_orth D x
  rw [hy0, zero_mul, sub_zero, hy, vacProj_vacProj D x, ← hy] at h
  have hyy : 0 ≤ D.form y y := D.form_nonneg y
  have hb : 0 ≤ r ^ n * D.form y y := mul_nonneg (pow_nonneg hr n) hyy
  have h2 : (D.form y ((D.T ^ n) y)) ^ 2 ≤ (r ^ n * D.form y y) ^ 2 := by
    calc (D.form y ((D.T ^ n) y)) ^ 2 ≤ r ^ (2 * n) * (D.form y y * D.form y y) := h
      _ = (r ^ n * D.form y y) ^ 2 := by rw [pow_mul']; ring
  exact (sq_le_sq.mp h2).trans_eq (abs_of_nonneg hb)

/-- The connected readings at even separations are nonnegative. -/
theorem conn_even_nonneg (D : Transfer.TransferData A) (m : ℕ) (x : A) :
    0 ≤ D.form (vacProj D x) ((D.T ^ (2 * m)) (vacProj D x)) := by
  rw [← form_pow_diag D m (vacProj D x)]
  exact D.form_nonneg _

/-- **Decay relative to the reading itself**: the connected reading at separation `2(m + d)` is at most
`r^{2d}` times the connected reading at separation `2m`. -/
theorem conn_rel_step (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (m d : ℕ) (x : A) :
    D.form (vacProj D x) ((D.T ^ (2 * (m + d))) (vacProj D x))
      ≤ r ^ (2 * d) * D.form (vacProj D x) ((D.T ^ (2 * m)) (vacProj D x)) := by
  set y := vacProj D x with hy
  have horth : D.form ((D.T ^ m) y) D.vac = 0 := by
    rw [form_pow_symm D m y D.vac, pow_vac D m]
    exact vacProj_orth D x
  have hsplit : (D.T ^ (m + d)) y = (D.T ^ d) ((D.T ^ m) y) := by
    rw [add_comm, pow_add, Module.End.mul_apply]
  rw [← form_pow_diag D (m + d) y, ← form_pow_diag D m y, hsplit]
  exact gap_pow D hr hg d ((D.T ^ m) y) horth

/-- **Relative decay at rate `r`**: both bounds, for every `x`. -/
def RelDecayAt (D : Transfer.TransferData A) (r : ℝ) : Prop :=
  (∀ (n : ℕ) (x : A), |D.form (vacProj D x) ((D.T ^ n) (vacProj D x))|
      ≤ r ^ n * D.form (vacProj D x) (vacProj D x)) ∧
    ∀ (m d : ℕ) (x : A), D.form (vacProj D x) ((D.T ^ (2 * (m + d))) (vacProj D x))
      ≤ r ^ (2 * d) * D.form (vacProj D x) ((D.T ^ (2 * m)) (vacProj D x))

theorem relDecayAt_of_gapAt (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r) :
    RelDecayAt D r :=
  ⟨fun n x => conn_abs_le D hr hg n x, fun m d x => conn_rel_step D hr hg m d x⟩

/-- A rate with `M a ≤ −log r` has `rⁿ ≤ exp(−M a n)`. -/
theorem pow_le_exp_of_log {r M a : ℝ} (hr : 0 < r) (h : M * a ≤ -Real.log r) (n : ℕ) :
    r ^ n ≤ Real.exp (-(M * (a * n))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := mul_le_mul_of_nonneg_left h hn
  calc r ^ n = Real.exp (Real.log r) ^ n := by rw [Real.exp_log hr]
    _ = Real.exp (n * Real.log r) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(M * (a * n))) := Real.exp_le_exp.mpr (by nlinarith)

end Abstract

/-! ## 2. The gap in relative form, from `WDelta2` -/

section Tower

variable {N : ℕ}

/-- The transfer data of step `k`: the infinite-volume periodic state at `dyBeta k`, plane `x₀ = 0`. -/
abbrev Dk (hN : N ≠ 0) (k : ℕ) :
    Transfer.TransferData
      ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :=
  ContinuumCluster.DkAlong hN (dyBeta (one_le_of_ne_zero hN)) 0 k

/-- **The relative gap from `WDelta2`.** Eventually in `k`, the step-`k` transfer data has a rate
`r > 0` with `rⁿ ≤ exp(−(c/(5ℓ₀)) · dySpacing N k · n)` and relative decay at `r`. -/
theorem relDecay_of_WDelta2 (hN2 : 2 ≤ N) (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∃ r : ℝ, 0 < r ∧
      (∀ n : ℕ, r ^ n ≤ Real.exp (-(c / (5 * ℓ₀) * (dySpacing N k * n)))) ∧
      RelDecayAt (Dk hN k) r := by
  obtain ⟨c, hc, hT⟩ := ContinuumCluster.towerGapAt_dyBeta_of_fixedWindowDecay hN2 hN 0
    (by positivity : (0 : ℝ) < 5 * ℓ₀) (DoublingClay2.fixedWindowDecay_of_WDelta2 hN hℓ hW)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hT] with k hk
  obtain ⟨r, hr, hg, hrate⟩ := hk
  exact ⟨r, hr, fun n => pow_le_exp_of_log hr hrate n, relDecayAt_of_gapAt _ hr.le hg⟩

end Tower

/-! ## 3. The floor of a trace state: a two-level witness -/

section Witness

/-- The two-level kernel `diag(1, μ)`: vacuum eigenvalue `1`, excited eigenvalue `μ`. -/
def wK (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, μ]

/-- The insertion `diag(0, 1)`. -/
def wX : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 1]

/-- The trace state of the closed chain of length `L`. -/
def wState (μ : ℝ) (L : ℕ) (Y : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ((wK μ) ^ L * Y).trace / ((wK μ) ^ L).trace

/-- The connected pairing at lag `n` on the closed chain of length `L` (the torus pairing). -/
def wTorusConn (μ : ℝ) (L n : ℕ) : ℝ :=
  ((wK μ) ^ (L - n) * wX * (wK μ) ^ n * wX).trace / ((wK μ) ^ L).trace - wState μ L wX ^ 2

/-- The vacuum sandwich of the same pairing (the vector-state reading). -/
def wVacConn (μ : ℝ) (n : ℕ) : ℝ := (wX * (wK μ) ^ n * wX) 0 0 - (wX 0 0) ^ 2

theorem wTorusConn_eq (μ : ℝ) {L n : ℕ} (hn : n ≤ L) :
    wTorusConn μ L n = μ ^ L / (1 + μ ^ L) - (μ ^ L / (1 + μ ^ L)) ^ 2 := by
  have hp : μ ^ (L - n) * μ ^ n = μ ^ L := by rw [← pow_add, Nat.sub_add_cancel hn]
  simp only [wTorusConn, wState, wK, wX, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Fin.sum_univ_two, Pi.pow_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_pow, mul_zero, mul_one, zero_add]
  rw [hp]

theorem wVacConn_eq (μ : ℝ) (n : ℕ) : wVacConn μ n = 0 := by
  simp [wVacConn, wK, wX, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]

theorem wTorusConn_pos {μ : ℝ} (hμ : 0 < μ) {L n : ℕ} (hn : n ≤ L) : 0 < wTorusConn μ L n := by
  rw [wTorusConn_eq μ hn]
  have h0 : 0 < μ ^ L := pow_pos hμ L
  have hp0 : 0 < μ ^ L / (1 + μ ^ L) := div_pos h0 (by linarith)
  have hp1 : μ ^ L / (1 + μ ^ L) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  nlinarith

/-- **The torus pairing does not decay relative to its contact value**, at any gap `1 − μ`. -/
theorem wTorus_no_relative_decay {μ : ℝ} (hμ : 0 < μ) {L n : ℕ} (hn : n ≤ L) (hn1 : 1 ≤ n)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    r ^ n * wTorusConn μ L 0 < wTorusConn μ L n := by
  have he : wTorusConn μ L n = wTorusConn μ L 0 := by
    rw [wTorusConn_eq μ hn, wTorusConn_eq μ (Nat.zero_le L)]
  have hpos := wTorusConn_pos hμ (Nat.zero_le L)
  have hrn : r ^ n < 1 := pow_lt_one₀ hr0 hr (by omega)
  rw [he]
  nlinarith

/-- **The torus pairing is not within any relative distance of the vacuum reading.** -/
theorem wTorus_not_vacuum_relative {μ : ℝ} (hμ : 0 < μ) {L n : ℕ} (hn : n ≤ L) (δ : ℝ) :
    ¬ |wTorusConn μ L n - wVacConn μ n| ≤ δ * wVacConn μ n := by
  rw [wVacConn_eq, mul_zero, sub_zero, abs_of_pos (wTorusConn_pos hμ hn)]
  exact not_le.mpr (wTorusConn_pos hμ hn)

end Witness

/-! ## 4. A dyadic torus of fixed physical side -/

section DyadicTorus

variable {N : ℕ}

/-- The state of step `k` on the dyadic torus of extent `2^{c+k+1}` at the coupling `dyBeta k`. -/
def stateTD (hN : N ≠ 0) (c k : ℕ) : MassGap.DLRLimit.State (Cfg N) :=
  PeriodicState.torusState hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k)

theorem stateTD_extent (c k : ℕ) : 2 * (2 ^ (c + k) - 1) + 1 + 1 = 2 ^ (c + k + 1) := by
  have h := Nat.one_le_two_pow (n := c + k)
  rw [pow_succ]
  omega

theorem stateTD_isPow2 (c k : ℕ) : PeriodicState.IsPow2 (2 * (2 ^ (c + k) - 1) + 1 + 1) :=
  ⟨c + k + 1, stateTD_extent c k⟩

/-- **The physical side is exactly `2^c · aRun N 1`.** -/
theorem stateTD_physical_side (c k : ℕ) :
    ((2 * (2 ^ (c + k) - 1) + 1 + 1 : ℕ) : ℝ) * dySpacing N k
      = 2 ^ c * AsymptoticScaling.aRun N 1 := by
  rw [stateTD_extent]
  unfold dySpacing
  push_cast
  rw [show c + k + 1 = c + (k + 1) by omega, pow_add]
  field_simp

/-- The index of `stateTD` lies in every dyadic seed set with `a ≤ c + k`. -/
theorem stateTD_seed (c k a : ℕ) (ha : a ≤ c + k) :
    2 ^ (c + k) - 1 ∈ {j : ℕ | ∃ k' : ℕ, 2 * j + 2 = 2 ^ k' * 2 ^ (a + 1)} := by
  refine ⟨c + k - a, ?_⟩
  rw [← pow_add, show c + k - a + (a + 1) = c + k + 1 by omega, ← stateTD_extent c k]

theorem stateTD_shift (hN : N ≠ 0) (c k : ℕ) (τ : Fin 4) (f : C(Cfg N, ℝ)) :
    stateTD hN c k (MassGap.ReflectionShift.ishiftObsL τ f) = stateTD hN c k f :=
  PeriodicState.torusState_shift hN _ _ τ f

end DyadicTorus

/-! ## 5. `hpos` against any per-step state -/

section Hpos

variable {N : ℕ}

/-- **`hpos` from a relative bound against any state's reading.** -/
theorem hpos_of_relS (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) {t ℓ ε : ℝ} (hε : ε < 1)
    (hposS : ∀ᶠ k in atTop, 0 < refReadingS σ O t ℓ k)
    (hrel : ∀ᶠ k in atTop, |ExistenceReduce.refReading hN O t ℓ k - refReadingS σ O t ℓ k|
      ≤ ε * refReadingS σ O t ℓ k) :
    ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k := by
  filter_upwards [hposS, hrel] with k hk hp
  have h2 := (abs_sub_le_iff.mp hp).2
  have h3 : 0 < (1 - ε) * refReadingS σ O t ℓ k := mul_pos (by linarith) hk
  nlinarith

/-- **A bound against the infinite-volume reading gives one against the torus reading.** At
`0 ≤ δ < 1`, `|R − R_σ| ≤ δ R` gives `|R − R_σ| ≤ δ/(1 − δ) · R_σ`. -/
theorem refRel_of_relInf {R Rσ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1) (h : |R - Rσ| ≤ δ * R) :
    |R - Rσ| ≤ δ / (1 - δ) * Rσ := by
  have h1 : 0 < 1 - δ := by linarith
  have hab := abs_nonneg (R - Rσ)
  have hlo := (abs_sub_le_iff.mp h).1
  have hhi := (abs_sub_le_iff.mp h).2
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  rcases le_or_gt R 0 with hR | hR
  · have hδR : δ * R = 0 := le_antisymm (mul_nonpos_of_nonneg_of_nonpos hδ0 hR) (hab.trans h)
    have hz : |R - Rσ| = 0 := le_antisymm (h.trans hδR.le) hab
    have hRR : R = Rσ := sub_eq_zero.mp (abs_eq_zero.mp hz)
    rw [hz, zero_mul, ← hRR, hδR]
  · have hRσ : R * (1 - δ) ≤ Rσ := by linarith
    have e1 := mul_le_mul_of_nonneg_right h h1.le
    have e2 := mul_le_mul_of_nonneg_left hRσ hδ0
    nlinarith

/-- **The pinned path with `hpos` read against any per-step state `σ`.** -/
theorem clay_canonical_relS (hN2 : 2 ≤ N) (hN : N ≠ 0) (σ : ℕ → MassGap.DLRLimit.State (Cfg N))
    (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t) {ε : ℝ} (hε : ε < 1)
    (hposS : ∀ᶠ k in atTop, 0 < refReadingS σ O t ℓ k)
    (hrel : ∀ᶠ k in atTop, |ExistenceReduce.refReading hN O t ℓ k - refReadingS σ O t ℓ k|
      ≤ ε * refReadingS σ O t ℓ k)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0 (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ExistenceReduce.clay_canonical hN2 hN O ht (hpos_of_relS hN σ O hε hposS hrel) hD hℓ hW

end Hpos

/-! ## 6. The closing error without the sup norm -/

section ChainL2

open MeasureTheory MassGap.KernelPower MassGap.HiddenChain MassGap.ChainClosing

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {w : X → Y → X → ℝ}

omit [Nonempty X] [Nonempty Y] in
theorem ins_const (t : ℝ) : Ins (X := X) (Y := Y) (fun _ _ => t) |t| :=
  ⟨measurable_const, fun _ _ => le_rfl⟩

omit [Nonempty X] [Nonempty Y] in
theorem ins_add {F G : (ℕ → X) → (ℕ → Y) → ℝ} {B C : ℝ} (hF : Ins F B) (hG : Ins G C) :
    Ins (fun V A => F V A + G V A) (B + C) :=
  ⟨hF.meas.add hG.meas, fun V A => (abs_add_le _ _).trans (add_le_add (hF.bdd V A) (hG.bdd V A))⟩

omit [Nonempty X] [Nonempty Y] in
theorem ins_abs {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B) :
    Ins (fun V A => |F V A|) B :=
  ⟨hF.meas.abs, fun V A => by rw [abs_abs]; exact hF.bdd V A⟩

/-- **Cauchy–Schwarz in the chain measure.** For an insertion `F` and a closing kernel `g`,

    (∫ₓ chain (F · g(V_{m+1}, x)) x)² ≤ (∫ₓ chain (F² · |g(V_{m+1}, x)|) x) · ∫ₓ∫_z k^{∗m}(x,z) |g(z,x)|.

The bound of `|F|` is used for integrability only and does not occur on the right. -/
theorem chain_cs_L2 (hS : Step w) (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B)
    {g : X → X → ℝ} (hg : Measurable (Function.uncurry g)) {Cg : ℝ} (hgb : ∀ z x, |g z x| ≤ Cg) :
    (∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ) ^ 2
      ≤ (∫ x, chain μ ν w (m + 1) (fun V A => F V A * F V A * |g (V (m + 1)) x|) x ∂μ)
        * ∫ x, ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ := by
  have hgx : ∀ x, Measurable (fun z => g z x) := fun x => mcomp2 hg measurable_id measurable_const
  have iG : ∀ x, Ins (fun V (_ : ℕ → Y) => |g (V (m + 1)) x|) Cg := fun x =>
    Ins.endpt (m + 1) (hgx x).abs (fun z => by rw [abs_abs]; exact hgb z x)
  have iA : ∀ x, Ins (fun V A => F V A * F V A * |g (V (m + 1)) x|) (B * B * Cg) := fun x =>
    (hF.mul hF).mul (iG x)
  have iB : ∀ x, Ins (fun V A => |F V A| * |g (V (m + 1)) x|) (B * Cg) := fun x =>
    (ins_abs hF).mul (iG x)
  -- measurability in `x`
  have mF : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => F q.2.1 q.2.2) := mcomp hF.meas measurable_snd
  have mg : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => g (q.2.1 (m + 1)) q.1) :=
    mcomp2 hg ((measurable_pi_apply (m + 1)).comp (measurable_fst.comp measurable_snd)) measurable_fst
  set Pa := fun x => chain μ ν w (m + 1) (fun V A => F V A * F V A * |g (V (m + 1)) x|) x with hPa
  set Pb := fun x => chain μ ν w (m + 1) (fun V A => |F V A| * |g (V (m + 1)) x|) x with hPb
  set Pc := fun x => chain μ ν w (m + 1) (fun V (_ : ℕ → Y) => |g (V (m + 1)) x|) x with hPc
  have mPa : Measurable Pa := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * F V A * |g (V (m + 1)) x|) ((mF.mul mF).mul mg.abs)
  have mPb : Measurable Pb := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => |F V A| * |g (V (m + 1)) x|) (mF.abs.mul mg.abs)
  have mPc : Measurable Pc := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V (_ : ℕ → Y) => |g (V (m + 1)) x|) mg.abs
  have intA : Integrable Pa μ := integrable_of_bdd mPa (C := 1 ^ (m + 1) * (B * B * Cg))
    (fun x => abs_chain_le hS.le_one (m + 1) (iA x).bdd x)
  have intB : Integrable Pb μ := integrable_of_bdd mPb (C := 1 ^ (m + 1) * (B * Cg))
    (fun x => abs_chain_le hS.le_one (m + 1) (iB x).bdd x)
  have intC : Integrable Pc μ := integrable_of_bdd mPc (C := 1 ^ (m + 1) * Cg)
    (fun x => abs_chain_le hS.le_one (m + 1) (iG x).bdd x)
  -- the quadratic is nonnegative
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, Pa x ∂μ) * (t * t) + (2 * ∫ x, Pb x ∂μ) * t + ∫ x, Pc x ∂μ := by
    intro t
    have hpt : ∀ x, 0 ≤ t * t * Pa x + (2 * t * Pb x + Pc x) := by
      intro x
      have i1 := (ins_const (X := X) (Y := Y) (t * t)).mul (iA x)
      have i2 := (ins_const (X := X) (Y := Y) (2 * t)).mul (iB x)
      have i23 := ins_add i2 (iG x)
      have e : chain μ ν w (m + 1) (fun V A => t * t * (F V A * F V A * |g (V (m + 1)) x|)
          + (2 * t * (|F V A| * |g (V (m + 1)) x|) + |g (V (m + 1)) x|)) x
          = t * t * Pa x + (2 * t * Pb x + Pc x) := by
        rw [chain_add hS.meas hS.le_one (m + 1) i1.meas i23.meas i1.bdd i23.bdd x,
          chain_add hS.meas hS.le_one (m + 1) i2.meas (iG x).meas i2.bdd (iG x).bdd x,
          chain_const_mul, chain_const_mul]
      rw [← e]
      have i0 := ins_const (X := X) (Y := Y) (0 : ℝ)
      have h0 : chain μ ν w (m + 1) (fun _ _ => (0 : ℝ)) x = 0 := by
        have := chain_const_mul (μ := μ) (ν := ν) (w := w) 0 (m + 1) (fun _ _ => (0 : ℝ)) x
        simpa using this
      rw [← h0]
      refine chain_mono hS.meas hS.le_one hS.nonneg (m + 1) i0.meas (ins_add i1 i23).meas i0.bdd
        (ins_add i1 i23).bdd (fun V A => ?_) x
      have hga := abs_nonneg (g (V (m + 1)) x)
      have : t * t * (F V A * F V A * |g (V (m + 1)) x|)
          + (2 * t * (|F V A| * |g (V (m + 1)) x|) + |g (V (m + 1)) x|)
          = |g (V (m + 1)) x| * (t * |F V A| + 1) ^ 2 := by
        have hFF : F V A * F V A = |F V A| * |F V A| := (abs_mul_abs_self _).symm
        rw [hFF]; ring
      rw [this]
      positivity
    have hI := integral_nonneg (μ := μ) (f := fun x => t * t * Pa x + (2 * t * Pb x + Pc x)) hpt
    have i2c : Integrable (fun x => 2 * t * Pb x + Pc x) μ := (intB.const_mul (2 * t)).add intC
    rw [integral_add (f := fun x => t * t * Pa x) (g := fun x => 2 * t * Pb x + Pc x)
      (intA.const_mul (t * t)) i2c,
      integral_add (f := fun x => 2 * t * Pb x) (g := Pc) (intB.const_mul (2 * t)) intC,
      integral_const_mul, integral_const_mul] at hI
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  have hBA : (∫ x, Pb x ∂μ) ^ 2 ≤ (∫ x, Pa x ∂μ) * ∫ x, Pc x ∂μ := by nlinarith
  -- the pairing is below `∫ Pb`
  have hmc : Measurable (fun x => chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x) :=
    measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
      (G := fun x V A => F V A * g (V (m + 1)) x) (mF.mul mg)
  have iFg : ∀ x, Ins (fun V A => F V A * g (V (m + 1)) x) (B * Cg) := fun x =>
    hF.mul (Ins.endpt (m + 1) (hgx x) (fun z => hgb z x))
  have hint : Integrable (fun x => chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x) μ :=
    integrable_of_bdd hmc (C := 1 ^ (m + 1) * (B * Cg))
      (fun x => abs_chain_le hS.le_one (m + 1) (iFg x).bdd x)
  have hpt : ∀ x, |chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x| ≤ Pb x := by
    intro x
    have h := abs_chain_le_chain_abs (μ := μ) (ν := ν) hS.meas hS.le_one hS.nonneg (m + 1)
      (iFg x).meas (iFg x).bdd x
    simp_rw [abs_mul] at h
    exact h
  have habs : |∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ|
      ≤ ∫ x, Pb x ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono hint.abs intB hpt)
  have hC : ∫ x, Pc x ∂μ = ∫ x, ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ := by
    congr 1; funext x
    exact chain_end_iter hS.meas hS.le_one (g := fun z => |g z x|) (hgx x).abs
      (fun z => by rw [abs_abs]; exact hgb z x) m x
  rw [← hC]
  calc (∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ) ^ 2
      = |∫ x, chain μ ν w (m + 1) (fun V A => F V A * g (V (m + 1)) x) x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, Pb x ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hBA

/-- The kernel factor of `chain_cs_L2` is bounded by the two Hilbert–Schmidt weights. -/
theorem iter_abs_sq_le (hS : Step w) (m : ℕ) {g : X → X → ℝ} (hg : Measurable (Function.uncurry g))
    {Cg : ℝ} (hgb : ∀ z x, |g z x| ≤ Cg) :
    (∫ x, ∫ z, iter μ (kern ν w) m x z * |g z x| ∂μ ∂μ) ^ 2
      ≤ hs μ (iter μ (kern ν w) m) * ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ := by
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hki := hk.iter (μ := μ) m
  obtain ⟨Ci, hCi⟩ := hki.bdd
  have hgs : Measurable (fun p : X × X => g p.2 p.1) := mcomp2 hg measurable_snd measurable_fst
  have hcs := cs_iter (μ := μ) (P := fun x z => iter μ (kern ν w) m x z) (Q := fun x z => |g z x|)
    hki.meas hgs.abs hCi (fun x z => by rw [abs_abs]; exact hgb z x)
  have e2 : ∫ x, ∫ z, |g z x| ^ 2 ∂μ ∂μ = ∫ x, ∫ z, g z x ^ 2 ∂μ ∂μ := by simp_rw [sq_abs]
  rw [e2] at hcs
  unfold hs
  exact hcs

variable (hS : Step w) (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν)
  (hsym : ∀ x a y, w x a y = w y (ι a) x)
  {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ} (hφb : ∀ x, |φ x| ≤ Bφ)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z)

include hS ι hι hsym hφm hφb hφ1 heig in
/-- **The closing error of the torus in the chain measure.** With `r = rem (kern ν w) c φ`:

    (Zh F − c^{m+1} Ih F)² ≤ (∫ₓ chain (F² · |r^{∗m}(V_{m+1}, x)|) x) · ∫ₓ∫_z k^{∗m}(x,z) |r^{∗m}(z,x)|,

and the second factor squared is at most `hs(k^{∗m}) · hs(r^{∗m})` (`iter_abs_sq_le`). The bound `B`
of `|F|` does not occur on the right. -/
theorem Zh_decomp_L2 (m : ℕ) {L : ℕ} (hL : L = m + 1 + m) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}
    (hF : Ins F B) (hl : LocalUpTo (m + 1) F) :
    (Zh μ ν w L F - c ^ (m + 1) * Ih μ ν w φ m F) ^ 2
      ≤ (∫ x, chain μ ν w (m + 1)
            (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|) x ∂μ)
        * ∫ x, ∫ z, iter μ (kern ν w) m x z * |iter μ (rem (kern ν w) c φ) m z x| ∂μ ∂μ := by
  subst hL
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hks := kern_symm hS ι hι hsym
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hri := hr.iter (μ := μ) m
  obtain ⟨Cr, hCr⟩ := hri.bdd
  have hsplit : ∀ x, chain μ ν w (m + 1 + m) (fun V A => F V A * kern ν w (V (m + 1 + m)) x) x
      = chain μ ν w (m + 1) (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x) x := by
    intro x
    have e : (fun V A => F V A * kern ν w (V (m + 1 + m)) x)
        = fun V A => F V A * kern ν w (sshift V (m + 1) m) x := by
      funext V A; simp only [sshift]; rw [show m + (m + 1) = m + 1 + m by omega]
    rw [e, chain_split (m + 1) m (fun (V' : ℕ → X) (_ : ℕ → Y) => kern ν w (V' m) x) x hl]
    simp_rw [chain_end_kern]
  have hdec : ∀ x, chain μ ν w (m + 1) (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x) x
      = (c ^ (m + 1) * φ x) * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x
        + chain μ ν w (m + 1) (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x := by
    intro x
    have e : (fun V A => F V A * iter μ (kern ν w) m (V (m + 1)) x)
        = fun V A => (c ^ (m + 1) * φ x) * (F V A * φ (V (m + 1)))
          + F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x := by
      funext V A
      rw [iter_decomp hk hks hφm hφb hφ1 heig m]; ring
    have i1 : Ins (fun V A => (c ^ (m + 1) * φ x) * (F V A * φ (V (m + 1)))) (|c ^ (m + 1) * φ x| * (B * Bφ)) :=
      ⟨measurable_const.mul (hF.mul (Ins.endpt (m + 1) hφm hφb)).meas, fun V A => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hF.mul (Ins.endpt (m + 1) hφm hφb)).bdd V A)
          (abs_nonneg _)⟩
    have i2 : Ins (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) (B * Cr) :=
      hF.mul (Ins.endpt (m + 1) (hri.col x) (fun z => hCr z x))
    rw [e, chain_add hS.meas hS.le_one (m + 1) i1.meas i2.meas i1.bdd i2.bdd x, chain_const_mul]
  have hm1 : Measurable (fun x => (c ^ (m + 1) * φ x)
      * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x) :=
    (measurable_const.mul hφm).mul (measurable_chain' hS.meas (m + 1)
      (hF.mul (Ins.endpt (m + 1) hφm hφb)).meas)
  have hGr : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) =>
      F q.2.1 q.2.2 * iter μ (rem (kern ν w) c φ) m (q.2.1 (m + 1)) q.1) :=
    (mcomp hF.meas measurable_snd).mul (mcomp2 hri.meas
      ((measurable_pi_apply (m + 1)).comp (measurable_fst.comp measurable_snd)) measurable_fst)
  have hm2 := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) hGr
  have hB := hF.nonneg
  have int1 : Integrable (fun x => (c ^ (m + 1) * φ x)
      * chain μ ν w (m + 1) (fun V A => F V A * φ (V (m + 1))) x) μ :=
    integrable_of_bdd hm1 (C := (|c ^ (m + 1)| * Bφ) * (1 ^ (m + 1) * (B * Bφ))) (fun x => by
      refine abs_mul_le_of ?_ (abs_chain_le hS.le_one (m + 1)
        (hF.mul (Ins.endpt (m + 1) hφm hφb)).bdd x)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg _))
  have int2 : Integrable (fun x => chain μ ν w (m + 1)
      (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x) μ :=
    integrable_of_bdd hm2 (C := 1 ^ (m + 1) * (B * Cr)) (fun x =>
      abs_chain_le hS.le_one (m + 1) (fun V A => abs_mul_le_of (hF.bdd V A) (hCr _ _)) x)
  have hZ : Zh μ ν w (m + 1 + m) F = c ^ (m + 1) * Ih μ ν w φ m F
      + ∫ x, chain μ ν w (m + 1) (fun V A => F V A * iter μ (rem (kern ν w) c φ) m (V (m + 1)) x) x ∂μ := by
    unfold Zh Ih
    simp_rw [hsplit, hdec]
    rw [integral_add int1 int2, ← integral_const_mul]
    congr 1; congr 1; funext x; ring
  rw [hZ, add_sub_cancel_left]
  exact chain_cs_L2 hS m hF hri.meas hCr

omit [Nonempty X] [Nonempty Y] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include hS in
/-- The powers of the step kernel are nonnegative. -/
theorem iter_kern_nonneg : ∀ (m : ℕ) (x z : X), 0 ≤ iter μ (kern ν w) m x z
  | 0, x, z => integral_nonneg fun a => hS.nonneg x a z
  | m + 1, x, z => integral_nonneg fun y =>
      mul_nonneg (integral_nonneg fun a => hS.nonneg x a y) (iter_kern_nonneg m y z)

include hS ι hι hsym hφm hφb hφ1 heig in
/-- **The second-moment factor is read in the torus and in the vacuum.** With `r = rem (kern ν w) c φ`,

    ∫ₓ chain (F² · |r^{∗m}(V_{m+1}, x)|) x ≤ Zh (F²) + |c|^{m+1} · Ih_{|φ|} (F²),

the torus trace of `F²` and its vacuum sandwich with `|φ|`. -/
theorem secondMoment_le (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B)
    (hl : LocalUpTo (m + 1) F) :
    ∫ x, chain μ ν w (m + 1)
        (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|) x ∂μ
      ≤ Zh μ ν w (m + 1 + m) (fun V A => F V A * F V A)
        + |c| ^ (m + 1) * Ih μ ν w (fun z => |φ z|) m (fun V A => F V A * F V A) := by
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hks := kern_symm hS ι hι hsym
  have hki := hk.iter (μ := μ) m
  obtain ⟨Ci, hCi⟩ := hki.bdd
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hri := hr.iter (μ := μ) m
  obtain ⟨Cr, hCr⟩ := hri.bdd
  have hFF := hF.mul hF
  have hφa : Ins (fun V (_ : ℕ → Y) => |φ (V (m + 1))|) Bφ :=
    Ins.endpt (m + 1) hφm.abs (fun z => by rw [abs_abs]; exact hφb z)
  have iG : ∀ x, Ins (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|)
      (B * B * Cr) := fun x =>
    hFF.mul (Ins.endpt (m + 1) (hri.col x).abs (fun z => by rw [abs_abs]; exact hCr z x))
  have iH1 : ∀ x, Ins (fun V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x) (B * B * Ci) :=
    fun x => hFF.mul (Ins.endpt (m + 1) (hki.col x) (fun z => hCi z x))
  have iH2 : ∀ x, Ins (fun V A => (|c| ^ (m + 1) * |φ x|) * (F V A * F V A * |φ (V (m + 1))|))
      (|(|c| ^ (m + 1) * |φ x|)| * (B * B * Bφ)) := fun x =>
    (ins_const (X := X) (Y := Y) _).mul (hFF.mul hφa)
  -- measurability in `x`
  have mF : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => F q.2.1 q.2.2) := mcomp hF.meas measurable_snd
  have mV : Measurable (fun q : X × (ℕ → X) × (ℕ → Y) => q.2.1 (m + 1)) :=
    (measurable_pi_apply (m + 1)).comp (measurable_fst.comp measurable_snd)
  have mG := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|)
    ((mF.mul mF).mul (mcomp2 hri.meas mV measurable_fst).abs)
  have mH1 := measurable_chain_diag (μ := μ) (ν := ν) hS (m + 1)
    (G := fun x V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x)
    ((mF.mul mF).mul (mcomp2 hki.meas mV measurable_fst))
  have mH2 : Measurable (fun x => (|c| ^ (m + 1) * |φ x|)
      * chain μ ν w (m + 1) (fun V A => F V A * F V A * |φ (V (m + 1))|) x) :=
    (measurable_const.mul hφm.abs).mul (measurable_chain' hS.meas (m + 1) (hFF.mul hφa).meas)
  have intG : Integrable (fun x => chain μ ν w (m + 1)
      (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|) x) μ :=
    integrable_of_bdd mG (C := 1 ^ (m + 1) * (B * B * Cr))
      (fun x => abs_chain_le hS.le_one (m + 1) (iG x).bdd x)
  have intH1 : Integrable (fun x => chain μ ν w (m + 1)
      (fun V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x) x) μ :=
    integrable_of_bdd mH1 (C := 1 ^ (m + 1) * (B * B * Ci))
      (fun x => abs_chain_le hS.le_one (m + 1) (iH1 x).bdd x)
  have intH2 : Integrable (fun x => (|c| ^ (m + 1) * |φ x|)
      * chain μ ν w (m + 1) (fun V A => F V A * F V A * |φ (V (m + 1))|) x) μ :=
    integrable_of_bdd mH2 (C := (|c| ^ (m + 1) * Bφ) * (1 ^ (m + 1) * (B * B * Bφ))) (fun x => by
      refine abs_mul_le_of ?_ (abs_chain_le hS.le_one (m + 1) (hFF.mul hφa).bdd x)
      rw [abs_mul, abs_abs, abs_of_nonneg (pow_nonneg (abs_nonneg c) _)]
      exact mul_le_mul_of_nonneg_left (hφb x) (pow_nonneg (abs_nonneg c) _))
  -- the pointwise bound
  have hpt : ∀ x, chain μ ν w (m + 1)
      (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|) x
      ≤ chain μ ν w (m + 1) (fun V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x) x
        + (|c| ^ (m + 1) * |φ x|)
          * chain μ ν w (m + 1) (fun V A => F V A * F V A * |φ (V (m + 1))|) x := by
    intro x
    have hsum := ins_add (iH1 x) (iH2 x)
    rw [← chain_const_mul, ← chain_add hS.meas hS.le_one (m + 1) (iH1 x).meas (iH2 x).meas
      (iH1 x).bdd (iH2 x).bdd x]
    refine chain_mono hS.meas hS.le_one hS.nonneg (m + 1) (iG x).meas hsum.meas (iG x).bdd
      hsum.bdd (fun V A => ?_) x
    have hrz : |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|
        ≤ iter μ (kern ν w) m (V (m + 1)) x + |c| ^ (m + 1) * |φ (V (m + 1))| * |φ x| := by
      have e := iter_decomp hk hks hφm hφb hφ1 heig m (V (m + 1)) x
      have e' : iter μ (rem (kern ν w) c φ) m (V (m + 1)) x
          = iter μ (kern ν w) m (V (m + 1)) x - c ^ (m + 1) * φ (V (m + 1)) * φ x := by
        rw [e]; ring
      rw [e']
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (iter_kern_nonneg hS m _ _), abs_mul, abs_mul, abs_pow]
    have hff : 0 ≤ F V A * F V A := mul_self_nonneg _
    have := mul_le_mul_of_nonneg_left hrz hff
    nlinarith [this]
  -- integrate
  have hsplit : ∀ x, chain μ ν w (m + 1 + m)
      (fun V A => F V A * F V A * kern ν w (V (m + 1 + m)) x) x
      = chain μ ν w (m + 1) (fun V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x) x := by
    intro x
    have e : (fun V A => F V A * F V A * kern ν w (V (m + 1 + m)) x)
        = fun V A => F V A * F V A * kern ν w (sshift V (m + 1) m) x := by
      funext V A; simp only [sshift]; rw [show m + (m + 1) = m + 1 + m by omega]
    rw [e, chain_split (m + 1) m (fun (V' : ℕ → X) (_ : ℕ → Y) => kern ν w (V' m) x) x (hl.mul hl)]
    simp_rw [chain_end_kern]
  have hZ : Zh μ ν w (m + 1 + m) (fun V A => F V A * F V A)
      = ∫ x, chain μ ν w (m + 1)
          (fun V A => F V A * F V A * iter μ (kern ν w) m (V (m + 1)) x) x ∂μ := by
    unfold Zh
    congr 1; funext x
    exact hsplit x
  have hI : |c| ^ (m + 1) * Ih μ ν w (fun z => |φ z|) m (fun V A => F V A * F V A)
      = ∫ x, (|c| ^ (m + 1) * |φ x|)
          * chain μ ν w (m + 1) (fun V A => F V A * F V A * |φ (V (m + 1))|) x ∂μ := by
    unfold Ih
    rw [← integral_const_mul]
    congr 1; funext x
    ring
  rw [hZ, hI, ← integral_add intH1 intH2]
  exact integral_mono intG (intH1.add intH2) hpt

include hS ι hι hsym hφm hφb hφ1 heig in
/-- **The closing of the torus, with second moments in place of the sup norm.**

    (Zh F − c^{m+1} Ih F)⁴ ≤ (Zh (F²) + |c|^{m+1} Ih_{|φ|} (F²))² · hs(k^{∗m}) · hs(r^{∗m}).

Divided by `|c|^{4(m+1)}`, the right side is the square of the normalised torus and `|φ|`-vacuum second
moments of `F` times `hs(k^{∗m}) hs(r^{∗m}) / |c|^{4(m+1)}`, which carries the excited weight
`s = hs(r^{∗m})/|c|^{2(m+1)}` to the first power. The bound `B` of `|F|` enters only through
integrability. -/
theorem Zh_close_rel (m : ℕ) {F : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ} (hF : Ins F B)
    (hl : LocalUpTo (m + 1) F) :
    (Zh μ ν w (m + 1 + m) F - c ^ (m + 1) * Ih μ ν w φ m F) ^ 4
      ≤ (Zh μ ν w (m + 1 + m) (fun V A => F V A * F V A)
          + |c| ^ (m + 1) * Ih μ ν w (fun z => |φ z|) m (fun V A => F V A * F V A)) ^ 2
        * hs μ (iter μ (kern ν w) m) * hs μ (iter μ (rem (kern ν w) c φ) m) := by
  have hk := bdd_kern (ν := ν) hS.meas hS.le_one
  have hr := Bdd.rem hk hφm hφb (c := c)
  have hri := hr.iter (μ := μ) m
  obtain ⟨Cr, hCr⟩ := hri.bdd
  set M := ∫ x, chain μ ν w (m + 1)
      (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|) x ∂μ with hM
  set K := ∫ x, ∫ z, iter μ (kern ν w) m x z * |iter μ (rem (kern ν w) c φ) m z x| ∂μ ∂μ with hK
  set S := Zh μ ν w (m + 1 + m) (fun V A => F V A * F V A)
      + |c| ^ (m + 1) * Ih μ ν w (fun z => |φ z|) m (fun V A => F V A * F V A) with hS'
  have he := Zh_decomp_L2 hS ι hι hsym hφm hφb hφ1 heig m rfl hF hl
  have hMS : M ≤ S := secondMoment_le hS ι hι hsym hφm hφb hφ1 heig m hF hl
  have hM0 : 0 ≤ M := by
    refine integral_nonneg fun x => ?_
    have iG : Ins (fun V A => F V A * F V A * |iter μ (rem (kern ν w) c φ) m (V (m + 1)) x|)
        (B * B * Cr) :=
      (hF.mul hF).mul (Ins.endpt (m + 1) (hri.col x).abs (fun z => by rw [abs_abs]; exact hCr z x))
    have i0 := ins_const (X := X) (Y := Y) (0 : ℝ)
    have h0 : chain μ ν w (m + 1) (fun _ _ => (0 : ℝ)) x = 0 := by
      have := chain_const_mul (μ := μ) (ν := ν) (w := w) 0 (m + 1) (fun _ _ => (0 : ℝ)) x
      simpa using this
    show (0 : ℝ) ≤ _
    rw [← h0]
    exact chain_mono hS.meas hS.le_one hS.nonneg (m + 1) i0.meas iG.meas i0.bdd iG.bdd
      (fun V A => mul_nonneg (mul_self_nonneg _) (abs_nonneg _)) x
  have hK0 : 0 ≤ K := integral_nonneg fun x => integral_nonneg fun z =>
    mul_nonneg (iter_kern_nonneg hS m x z) (abs_nonneg _)
  have hK2 := iter_abs_sq_le (μ := μ) (ν := ν) hS m hri.meas hCr
  have hswap : ∫ x, ∫ z, iter μ (rem (kern ν w) c φ) m z x ^ 2 ∂μ ∂μ
      = hs μ (iter μ (rem (kern ν w) c φ) m) := by
    unfold hs
    exact (swap_bdd (F := fun x z => iter μ (rem (kern ν w) c φ) m z x ^ 2)
      ((hri.meas.comp measurable_swap).pow_const 2) (C := Cr ^ 2) (fun x z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCr _ _) 2))
  rw [hswap] at hK2
  set e := Zh μ ν w (m + 1 + m) F - c ^ (m + 1) * Ih μ ν w φ m F
  have h1 : (e ^ 2) ^ 2 ≤ (M * K) ^ 2 := pow_le_pow_left₀ (sq_nonneg e) he 2
  have h2 : M ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hM0 hMS 2
  have h3 : (M * K) ^ 2 ≤ S ^ 2 * K ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right h2 (sq_nonneg K)
  have h4 : S ^ 2 * K ^ 2 ≤ S ^ 2 * (hs μ (iter μ (kern ν w) m) * hs μ (iter μ (rem (kern ν w) c φ) m)) :=
    mul_le_mul_of_nonneg_left hK2 (sq_nonneg S)
  calc e ^ 4 = (e ^ 2) ^ 2 := by ring
    _ ≤ _ := h1.trans (h3.trans h4)
    _ = _ := by ring

end ChainL2

end MassGap.RelativeDecay

#print axioms MassGap.RelativeDecay.conn_eq_vacProj
#print axioms MassGap.RelativeDecay.conn_abs_le
#print axioms MassGap.RelativeDecay.conn_even_nonneg
#print axioms MassGap.RelativeDecay.conn_rel_step
#print axioms MassGap.RelativeDecay.relDecayAt_of_gapAt
#print axioms MassGap.RelativeDecay.pow_le_exp_of_log
#print axioms MassGap.RelativeDecay.relDecay_of_WDelta2
#print axioms MassGap.RelativeDecay.wTorusConn_eq
#print axioms MassGap.RelativeDecay.wVacConn_eq
#print axioms MassGap.RelativeDecay.wTorusConn_pos
#print axioms MassGap.RelativeDecay.wTorus_no_relative_decay
#print axioms MassGap.RelativeDecay.wTorus_not_vacuum_relative
#print axioms MassGap.RelativeDecay.stateTD_extent
#print axioms MassGap.RelativeDecay.stateTD_physical_side
#print axioms MassGap.RelativeDecay.stateTD_seed
#print axioms MassGap.RelativeDecay.hpos_of_relS
#print axioms MassGap.RelativeDecay.refRel_of_relInf
#print axioms MassGap.RelativeDecay.clay_canonical_relS
#print axioms MassGap.RelativeDecay.chain_cs_L2
#print axioms MassGap.RelativeDecay.iter_abs_sq_le
#print axioms MassGap.RelativeDecay.Zh_decomp_L2
#print axioms MassGap.RelativeDecay.iter_kern_nonneg
#print axioms MassGap.RelativeDecay.secondMoment_le
#print axioms MassGap.RelativeDecay.Zh_close_rel
