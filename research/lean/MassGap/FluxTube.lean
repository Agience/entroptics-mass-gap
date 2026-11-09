import Mathlib
import MassGap.SUN

/-!
# MassGap.FluxTube — classically, centre flux spreads in `SU(N)` as `U(1)` flux does

The owner's route: "flux can't spread: non-abelian flux can't dilute into many weak fields the way
`U(1)` does — it stays a tube, so its cost stays proportional to length at every zoom (finite proper
centre)." This module makes the classical form of that statement precise and decides it.

The classical statement, modelled as a list of plaquette holonomies whose product is the flux
(no lattice or surface appears in the Lean statements), is: *a list with product a non-trivial
centre element has a total Wilson action bounded below independently of its length.* It holds for a
finite gauge group and fails for `SU(N)`; for `U(1)`, a real flux `Φ` spread evenly over `n`
plaquettes costs at most `Φ²/2/n`. The centre of `SU(N)` quantises the total holonomy of a loop, not
the holonomy of each plaquette inside it: `ω · 1` is reached by a path in the maximal torus, and `n`
plaquettes each carrying `1/n` of that path multiply to `ω · 1` at a total Wilson action at most
`vortexConst / n`.

Both directions are elementary: the floor is a one-factor bound plus a minimum over a finite set; its
failure for `SU(N)` is continuity of `wilson` at `1` with `n`-th roots of `ω^k` approaching `1`. The
content is the discrete-versus-connected dichotomy, not anything specific to non-abelian groups.

Wilson plaquette action `wilson U = 1 − Re tr U / N` (it is `0` at `U = 1`).

## 1. `U(1)`: quadratic energy and spreading

* `quad_split_ge`: any split `Φ = Σ φᵢ` into `n` parts has `Σ φᵢ² ≥ Φ²/n` (Cauchy–Schwarz);
  `quad_split_equal`: the equal split attains `Φ²/n`; `quad_split_tendsto`: `Φ²/n → 0`. A
  continuously divisible flux with quadratic energy dilutes.
* `u1Spread Φ n = n (1 − cos (Φ/n))`, the `U(1)` Wilson action of a flux `Φ` spread evenly over `n`
  plaquettes. `u1Spread_nonneg`, `u1Spread_le` (`≤ Φ²/2/n`), `u1Spread_tendsto_zero`.

## 2. The maximal torus of `SU(N)`

* `torus φ = diag (e^{iφ₀}, …, e^{iφ_{N−1}})`; `torus_mem`: in `SU(N)` when `Σ φₖ = 0`;
  `torus_mul`, `torus_zero`, `torus_pow` (`torus φ ^ n = torus (n • φ)`).
* `wilson_torus`: `wilson (torus φ) = Σₖ (1 − cos φₖ) / N`; `wilson_torus_nonneg`;
  `wilson_torus_le`: `≤ Σₖ φₖ² / (2N)`.

## 3. The centre element as a torus element

`N = m + 1`. `centreScalar m k = e^{2πik/N}`; `centreAngles m k` has entry `2πk/N` at every index
but the last and `2πk/N − 2πk` at the last.

* `sum_centreAngles`: the angles sum to `0`. `torus_centreAngles`: `torus (centreAngles m k) =
  e^{2πik/N} · 1`. `centreScalar_one_ne_one`, `centre_ne_one` (`m ≥ 1`): the generator `ω · 1` is not
  the identity. `centre_commutes`: it commutes with every matrix.
* `thin_vortex_action`: one plaquette carrying the whole flux, `wilson (ω^k · 1) = 1 − cos (2πk/N)`
  (`= 2` for `SU(2)`, `k = 1`).

## 4. The thick vortex

`vortexPlaq m k n = torus ((1/n) • centreAngles m k)`: one plaquette carrying `1/n` of the flux.

* `vortexPlaq_mem`, `vortexPlaq_pow`: it lies in `SU(N)` and its `n`-th power is `ω^k · 1`.
* Lattice realisation (`stripLink`): on a strip of `n` plaquettes in one plane, horizontal links `1`
  and vertical link `j` equal to `torus ((j/n) • centreAngles m k)`. `stripLink_zero`,
  `stripLink_succ` (`link (j+1) = vortexPlaq · link j`, so every plaquette of the strip has holonomy
  `vortexPlaq`), `stripLink_last` (`link n = ω^k · 1`, the holonomy of the loop around the strip).
  The configuration is abelian (all links in the torus), so it is a configuration of the `U(1)ᴺ⁻¹`
  subgroup; nothing about the non-abelian structure is used.
* `vortexConst m k = Σ (centreAngles m k)² / (2N)`; `vortexConst_eq`: it equals
  `2π² k² m / (m+1)²` (`π²/2` for `SU(2)`, `k = 1`).
* `vortex_action_le`: the total Wilson action of the `n` plaquettes is at most `vortexConst / n`.
  `thick_vortex_action_tendsto_zero`: it tends to `0`. Reading, not a Lean statement: on a vortex
  sheet in 4D, `n` is the number of transverse plaquettes the flux is spread over (`n = w²` for a
  core of side `w`), the configuration is constant along the sheet, and the action per unit area of
  the sheet is the action of one cross-section, `≤ vortexConst / w²` (the `w × w` core is built and
  checked in `flux_tube_checks.py`).
* `su2_vortex_eq_u1`: for `SU(2)`, `k = 1`, the thick vortex action is exactly `u1Spread π n`: the
  `ℤ₂` centre flux of `SU(2)` is the `U(1)` flux `π` of the diagonal subgroup, and spreads exactly
  as it does.
* `centre_flux_spreads`, `su_flux_no_floor`: for every `ε > 0` some list of `SU(N)` plaquette
  holonomies multiplies to `ω^k · 1` with total Wilson action below `ε` (non-trivial when
  `(m+1) ∤ k`; for `(m+1) ∣ k`, `ω^k = 1` and the empty list is a witness; `centre_ne_one`
  certifies `k = 1`, `m ≥ 1`).

## 5. A finite gauge group: the floor holds

* `flux_floor`: in any monoid, if a cost `s ≥ 0` is at least `δ` off the identity, every list of
  group elements whose product is not `1` costs at least `δ`, whatever its length (some factor is
  not `1`, and that factor alone costs `δ`).
* `exists_gap`: a finite group with `s > 0` off the identity has such a `δ > 0`.
  `finite_flux_cannot_spread`: so in a finite gauge group (e.g. `ℤ_N`) every list with non-trivial
  product costs at least `δ`. Read on a cross-section (for a non-abelian `G` the boundary holonomy
  is a product of conjugated plaquette holonomies; that form is not stated here, though the same
  argument applies since a conjugate of `g` is `1` only if `g` is), a non-trivial flux costs at
  least `δ` per cross-section, uniformly in how many plaquettes it is spread over.

## What this decides

Classically, "flux can't spread" is true for a finite gauge group (`finite_flux_cannot_spread`) and
false for `SU(N)` (`su_flux_no_floor`, `thick_vortex_action_tendsto_zero`). For `SU(2)` the failure
is exactly the `U(1)` one (`su2_vortex_eq_u1`); for every `SU(N)` the same `1/n` bound holds through
the abelian torus (`vortex_action_le`). The finite centre of `SU(N)` does not separate it from `U(1)`
at the level of the classical action. Read on a 4D sheet constant along its plane (not a Lean
statement), the action per unit sheet area of a centre vortex can be made `≤ vortexConst / w²`, the
same scaling as a spread `U(1)` flux; no lower bound is proved.

What is left for the route is not classical. What the finite centre does label is the twisted
sectors: the 't Hooft twists of a periodic box are indexed by `ℤ_N`, and the statement that a thick
centre vortex still costs a free energy proportional to its area is a statement about the quantum
measure — the entropy of vortex sheets against their `1/w²` action, equivalently the decay of the
twisted partition-function ratio `Z_twist / Z` ('t Hooft's vortex free energy,
`FluxShareSquaring.twistRatio`) at a rate proportional to the area, uniformly in the zoom. No
declaration here addresses it.

## Numerics (`research/code/flux_tube_checks.py`, under 10 s, no Monte Carlo)

* The strip configurations of `stripLink` built as matrices for `SU(2)`, `SU(3)` (`k = 1, 2`),
  `SU(4)`: unitary, determinant `1`, plaquette holonomy `vortexPlaq`, loop holonomy `ω^k · 1`, total
  action `≤ vortexConst / n`; for `SU(2)` equal to `u1Spread π n` (`2, 0.307, 0.0193` at
  `n = 1, 16, 256`).
* A `w × w` core on a `40 × 40` plaquette grid in axial gauge (`SU(2)`): boundary holonomy `−1`,
  action `w² (1 − cos (π/w²))`: `2, 1.17, 0.307, 0.0771, 0.0193` at `w = 1, 2, 4, 8, 16`, so
  `w² · action → π²/2`; the closed form `w² (1 − cos (π/w²))` has log-log slope `−2.000` at
  `w = 24..32`, as for a `U(1)` flux.
* Within the torus of `SU(2)`, `n = 2, 3, 4, 6`: a constrained minimisation from a grid of starts
  finds no split with `Σ φᵢ = π`, `φᵢ ∈ [−π, π]`, below the equal split (a check only).
* `ℤ₂`, `ℤ₃` with cost `1 − Re z`: exhaustive enumeration, `n ≤ 12` and `n ≤ 8` plaquettes; the
  minimum action of a non-trivial flux is the one-plaquette gap (`2`, `1.5`) at every `n`.

DERIVED (module-wide): `1` the trace normalisation `Re tr 1 / N = 1`; `2` in `x²/2` the second
Taylor coefficient of `cos`; `2π` the period of `e^{iθ}`; `m + 1 = N` the matrix size, written so that
the last diagonal index `Fin.last m` exists; `0` the sum of angles making the determinant `1`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FluxTube

open Filter Topology Finset

/-! ## 1. `U(1)`: quadratic energy and spreading -/

/-- **A split flux has quadratic energy at least `Φ²/n`** (Cauchy–Schwarz): for `n ≠ 0` and any
`φ : Fin n → ℝ`, `(Σ φᵢ)² / n ≤ Σ φᵢ²`. -/
theorem quad_split_ge {n : ℕ} (hn : n ≠ 0) (φ : Fin n → ℝ) :
    (∑ i, φ i) ^ 2 / n ≤ ∑ i, φ i ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := φ)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [div_le_iff₀ hn']
  linarith

/-- **The equal split attains `Φ²/n`.** -/
theorem quad_split_equal {n : ℕ} (hn : n ≠ 0) (Φ : ℝ) :
    ∑ _i : Fin n, (Φ / n) ^ 2 = Φ ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The minimal quadratic energy of a flux split `n` ways tends to `0`.** -/
theorem quad_split_tendsto (Φ : ℝ) :
    Tendsto (fun n : ℕ => Φ ^ 2 / n) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

/-- The `U(1)` Wilson action of a flux `Φ` spread evenly over `n` plaquettes. -/
def u1Spread (Φ : ℝ) (n : ℕ) : ℝ := n * (1 - Real.cos (Φ / n))

theorem u1Spread_nonneg (Φ : ℝ) (n : ℕ) : 0 ≤ u1Spread Φ n :=
  mul_nonneg n.cast_nonneg (by linarith [Real.cos_le_one (Φ / n)])

/-- **The spread `U(1)` action is at most `Φ²/2/n`.** -/
theorem u1Spread_le (Φ : ℝ) {n : ℕ} (hn : n ≠ 0) : u1Spread Φ n ≤ Φ ^ 2 / 2 / n := by
  unfold u1Spread
  have hc := Real.one_sub_sq_div_two_le_cos (x := Φ / n)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc (n : ℝ) * (1 - Real.cos (Φ / n)) ≤ n * ((Φ / n) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hn'.le
    _ = Φ ^ 2 / 2 / n := by field_simp

/-- **A `U(1)` flux spread over `n` plaquettes costs an action tending to `0`.** -/
theorem u1Spread_tendsto_zero (Φ : ℝ) :
    Tendsto (fun n : ℕ => u1Spread Φ n) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (Φ ^ 2 / 2)) ?_ ?_
  · exact Eventually.of_forall fun n => u1Spread_nonneg Φ n
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact u1Spread_le Φ hn

/-! ## 2. The maximal torus of `SU(N)` -/

/-- The diagonal matrix `diag (e^{iφₖ})`. -/
def torus {N : ℕ} (φ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun k => Complex.exp ((φ k : ℂ) * Complex.I)

/-- The Wilson plaquette action `1 − Re tr U / N`. -/
def wilson {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ := 1 - (Matrix.trace U).re / N

theorem torus_mul {N : ℕ} (φ ψ : Fin N → ℝ) : torus φ * torus ψ = torus (φ + ψ) := by
  unfold torus
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  rw [← Complex.exp_add, Pi.add_apply, Complex.ofReal_add, add_mul]

theorem torus_zero {N : ℕ} : torus (0 : Fin N → ℝ) = 1 := by
  unfold torus
  simp

theorem torus_pow {N : ℕ} (φ : Fin N → ℝ) (n : ℕ) : torus φ ^ n = torus ((n : ℝ) • φ) := by
  induction n with
  | zero => simp [torus_zero]
  | succ n ih => rw [pow_succ, ih, torus_mul, Nat.cast_succ, add_smul, one_smul]

/-- **A torus element with angles summing to `0` lies in `SU(N)`.** -/
theorem torus_mem {N : ℕ} (φ : Fin N → ℝ) (h : ∑ k, φ k = 0) :
    torus φ ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  have h1 : ∀ k, Complex.exp ((φ k : ℂ) * Complex.I)
      * star (Complex.exp ((φ k : ℂ) * Complex.I)) = 1 := by
    intro k
    have hs : star (Complex.exp ((φ k : ℂ) * Complex.I))
        = (starRingEnd ℂ) (Complex.exp ((φ k : ℂ) * Complex.I)) := rfl
    rw [hs, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    simp
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, torus,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    have hfun : (fun k => Complex.exp ((φ k : ℂ) * Complex.I)
        * (star fun k => Complex.exp ((φ k : ℂ) * Complex.I) : Fin N → ℂ) k) = (1 : Fin N → ℂ) := by
      funext k
      rw [Pi.star_apply]
      exact h1 k
    rw [hfun]
    simp
  · rw [torus, Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, h]
    simp

/-- **The Wilson action of a torus element**: `Σₖ (1 − cos φₖ) / N`. -/
theorem wilson_torus {N : ℕ} (hN : N ≠ 0) (φ : Fin N → ℝ) :
    wilson (torus φ) = (∑ k, (1 - Real.cos (φ k))) / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold wilson torus
  rw [Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.exp_ofReal_mul_I_re]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sub_div, div_self hN']

theorem wilson_torus_nonneg {N : ℕ} (hN : N ≠ 0) (φ : Fin N → ℝ) : 0 ≤ wilson (torus φ) := by
  rw [wilson_torus hN]
  exact div_nonneg (Finset.sum_nonneg fun k _ => by linarith [Real.cos_le_one (φ k)])
    (Nat.cast_nonneg N)

/-- **The Wilson action of a torus element is at most `Σₖ φₖ² / (2N)`.** -/
theorem wilson_torus_le {N : ℕ} (hN : N ≠ 0) (φ : Fin N → ℝ) :
    wilson (torus φ) ≤ (∑ k, φ k ^ 2) / (2 * N) := by
  rw [wilson_torus hN]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hs : ∑ k, (1 - Real.cos (φ k)) ≤ (∑ k, φ k ^ 2) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro k _
    have := Real.one_sub_sq_div_two_le_cos (x := φ k)
    linarith
  calc (∑ k, (1 - Real.cos (φ k))) / N ≤ ((∑ k, φ k ^ 2) / 2) / N := by gcongr
    _ = (∑ k, φ k ^ 2) / (2 * N) := by rw [div_div]

/-! ## 3. The centre element as a torus element -/

/-- The centre phase `e^{2πik/N}`, `N = m + 1`. -/
def centreScalar (m k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * k / (m + 1) : ℝ) : ℂ) * Complex.I)

/-- Torus angles of `e^{2πik/N} · 1`: `2πk/N` at every index but the last, `2πk/N − 2πk` there. -/
def centreAngles (m k : ℕ) : Fin (m + 1) → ℝ := fun i =>
  2 * Real.pi * k / (m + 1) - (if i = Fin.last m then 2 * Real.pi * k else 0)

theorem sum_centreAngles (m k : ℕ) : ∑ i, centreAngles m k i = 0 := by
  unfold centreAngles
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The centre element is a torus element**: `torus (centreAngles m k) = e^{2πik/N} · 1`. -/
theorem torus_centreAngles (m k : ℕ) :
    torus (centreAngles m k) = centreScalar m k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  rw [Matrix.smul_one_eq_diagonal]
  unfold torus
  congr 1
  funext i
  unfold centreAngles centreScalar
  split_ifs with h
  · have h2 : Complex.exp (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) by
        ring]
      exact Complex.exp_nat_mul_two_pi_mul_I k
    push_cast
    rw [sub_mul, Complex.exp_sub, h2, div_one]
  · rw [sub_zero]

theorem centreScalar_one_ne_one {m : ℕ} (hm : 1 ≤ m) : centreScalar m 1 ≠ 1 := by
  have hp := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  have h : centreScalar m 1 = Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ)) := by
    unfold centreScalar
    congr 1
    push_cast
    ring
  rw [h]
  exact hp.ne_one (by omega)

/-- **The generator of the centre is not the identity** (`N = m + 1 ≥ 2`). -/
theorem centre_ne_one {m : ℕ} (hm : 1 ≤ m) :
    centreScalar m 1 • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  exact centreScalar_one_ne_one hm h00

/-- The centre element commutes with every matrix. -/
theorem centre_commutes (m k : ℕ) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    (centreScalar m k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * M
      = M * (centreScalar m k • 1) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **The thin vortex**: one plaquette carrying the whole centre flux has Wilson action
`1 − cos (2πk/N)`. -/
theorem thin_vortex_action (m k : ℕ) :
    wilson (centreScalar m k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ))
      = 1 - Real.cos (2 * Real.pi * k / (m + 1)) := by
  rw [← torus_centreAngles, wilson_torus (Nat.succ_ne_zero m)]
  have hc : ∀ i, Real.cos (centreAngles m k i) = Real.cos (2 * Real.pi * k / (m + 1)) := by
    intro i
    unfold centreAngles
    split_ifs
    · rw [show 2 * Real.pi * (k : ℝ) / ((m : ℝ) + 1) - 2 * Real.pi * k
          = 2 * Real.pi * k / ((m : ℝ) + 1) - (k : ℕ) * (2 * Real.pi) by ring,
        Real.cos_sub_nat_mul_two_pi]
    · rw [sub_zero]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## 4. The thick vortex -/

/-- One plaquette carrying `1/n` of the centre flux. -/
def vortexPlaq (m k n : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  torus ((1 / (n : ℝ)) • centreAngles m k)

theorem vortexPlaq_mem (m k n : ℕ) :
    vortexPlaq m k n ∈ Matrix.specialUnitaryGroup (Fin (m + 1)) ℂ := by
  refine torus_mem _ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_centreAngles, mul_zero]

/-- **`n` plaquettes of `1/n` of the flux multiply to the centre element.** -/
theorem vortexPlaq_pow (m k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    vortexPlaq m k n ^ n = centreScalar m k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [vortexPlaq, torus_pow, smul_smul, mul_one_div_cancel hn', one_smul, torus_centreAngles]

/-- The vertical link `j` of the strip: `torus ((j/n) • centreAngles m k)`. -/
def stripLink (m k n j : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  torus (((j : ℝ) / n) • centreAngles m k)

theorem stripLink_zero (m k n : ℕ) : stripLink m k n 0 = 1 := by
  simp [stripLink, torus_zero]

/-- **Each plaquette of the strip has holonomy `vortexPlaq`**: `link (j+1) = vortexPlaq · link j`. -/
theorem stripLink_succ (m k n j : ℕ) :
    stripLink m k n (j + 1) = vortexPlaq m k n * stripLink m k n j := by
  rw [stripLink, stripLink, vortexPlaq, torus_mul, ← add_smul,
    show (1 : ℝ) / n + (j : ℝ) / n = ((j + 1 : ℕ) : ℝ) / n by push_cast; ring]

/-- **The loop around the strip has holonomy `ω^k · 1`.** -/
theorem stripLink_last (m k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    stripLink m k n n = centreScalar m k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [stripLink, div_self hn', one_smul, torus_centreAngles]

/-- The constant of the thick-vortex bound: `Σ (centreAngles m k)² / (2N)`. -/
def vortexConst (m k : ℕ) : ℝ := (∑ i, centreAngles m k i ^ 2) / (2 * ((m + 1 : ℕ) : ℝ))

/-- **The constant in closed form**: `2π² k² m / (m+1)²`. -/
theorem vortexConst_eq (m k : ℕ) :
    vortexConst m k = 2 * Real.pi ^ 2 * (k : ℝ) ^ 2 * m / ((m : ℝ) + 1) ^ 2 := by
  unfold vortexConst centreAngles
  rw [Fin.sum_univ_castSucc]
  have hne : ∀ i : Fin m, (Fin.castSucc i = Fin.last m) = False := fun i =>
    eq_false (Fin.castSucc_lt_last i).ne
  simp only [hne, ↓reduceIte, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The thick vortex costs at most `vortexConst / n`**: `n` plaquettes each carrying `1/n` of the
centre flux have total Wilson action at most `vortexConst m k / n`. -/
theorem vortex_action_le (m k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * wilson (vortexPlaq m k n) ≤ vortexConst m k / n := by
  have h := wilson_torus_le (Nat.succ_ne_zero m) ((1 / (n : ℝ)) • centreAngles m k)
  have hs : ∑ i, ((1 / (n : ℝ)) • centreAngles m k) i ^ 2
      = (1 / (n : ℝ)) ^ 2 * ∑ i, centreAngles m k i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.mul_sum]
  rw [hs] at h
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold vortexPlaq vortexConst
  calc (n : ℝ) * wilson (torus ((1 / (n : ℝ)) • centreAngles m k))
      ≤ n * (((1 / (n : ℝ)) ^ 2 * ∑ i, centreAngles m k i ^ 2) / (2 * ((m + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left h hn'.le
    _ = (∑ i, centreAngles m k i ^ 2) / (2 * ((m + 1 : ℕ) : ℝ)) / n := by
        field_simp

/-- **The classical action of a thick centre vortex tends to `0`**: spread over `n` plaquettes,
the centre flux `ω^k · 1` of `SU(m+1)` costs a total Wilson action tending to `0` as `n → ∞`. -/
theorem thick_vortex_action_tendsto_zero (m k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * wilson (vortexPlaq m k n)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (vortexConst m k)) ?_ ?_
  · exact Eventually.of_forall fun n =>
      mul_nonneg n.cast_nonneg (wilson_torus_nonneg (Nat.succ_ne_zero m) _)
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact vortex_action_le m k hn

/-- **For `SU(2)` the thick `ℤ₂` vortex is the spread `U(1)` flux `π`**: its total Wilson action
over `n` plaquettes is exactly `u1Spread π n`. -/
theorem su2_vortex_eq_u1 (n : ℕ) :
    (n : ℝ) * wilson (vortexPlaq 1 1 n) = u1Spread Real.pi n := by
  have h0 : centreAngles 1 1 0 = Real.pi := by
    unfold centreAngles
    rw [if_neg (by decide)]
    push_cast
    ring
  have h1 : centreAngles 1 1 1 = -Real.pi := by
    unfold centreAngles
    rw [if_pos (by decide)]
    push_cast
    ring
  unfold vortexPlaq u1Spread
  rw [wilson_torus (by norm_num), Fin.sum_univ_two]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h0, h1, mul_neg, Real.cos_neg, show (1 : ℝ) / n * Real.pi = Real.pi / n by ring]
  push_cast
  ring

/-- **Centre flux spreads in `SU(N)`**: for every `ε > 0` there are `n > 0` and `U ∈ SU(m+1)` with
`Uⁿ = ω^k · 1` and `n · wilson U < ε`. -/
theorem centre_flux_spreads (m k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ U : MassGap.SUN.SU (m + 1),
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ^ n = centreScalar m k • 1
        ∧ (n : ℝ) * wilson (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) < ε := by
  obtain ⟨n, hlt, hn⟩ :=
    (((thick_vortex_action_tendsto_zero m k).eventually (gt_mem_nhds hε)).and
      (eventually_gt_atTop 0)).exists
  exact ⟨n, hn, ⟨vortexPlaq m k n, vortexPlaq_mem m k n⟩, vortexPlaq_pow m k hn.ne', hlt⟩

/-- **No floor on the action of a centre flux in `SU(N)`**: for every `δ > 0` some list of `SU(m+1)`
plaquette holonomies multiplies to `ω^k · 1` with total Wilson action below `δ`. -/
theorem su_flux_no_floor (m k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ l : List (MassGap.SUN.SU (m + 1)),
      ((l.prod : MassGap.SUN.SU (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
          = centreScalar m k • 1
        ∧ (l.map fun U : MassGap.SUN.SU (m + 1) => wilson U.1).sum < δ := by
  obtain ⟨n, _, U, hU, hlt⟩ := centre_flux_spreads m k hδ
  refine ⟨List.replicate n U, ?_, ?_⟩
  · rw [List.prod_replicate]
    exact (SubmonoidClass.coe_pow U n).trans hU
  · rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
    exact hlt

/-! ## 5. A finite gauge group: the floor holds -/

/-- **A non-trivial product costs at least the gap**: if `s ≥ 0` and `s g ≥ δ` for `g ≠ 1`, every
list whose product is not `1` has `Σ s ≥ δ`, whatever its length. -/
theorem flux_floor {G : Type*} [Monoid G] (s : G → ℝ) (hs : ∀ g, 0 ≤ s g) {δ : ℝ}
    (hδ : ∀ g, g ≠ 1 → δ ≤ s g) (l : List G) (h : l.prod ≠ 1) : δ ≤ (l.map s).sum := by
  induction l with
  | nil => exact absurd List.prod_nil h
  | cons g l ih =>
    rw [List.map_cons, List.sum_cons]
    have hl : 0 ≤ (l.map s).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact hs y
    by_cases hg : g = 1
    · rw [hg, List.prod_cons, one_mul] at h
      have := ih h
      linarith [hs g]
    · linarith [hδ g hg]

/-- **A finite group has a gap**: a cost positive off the identity is at least some `δ > 0` there. -/
theorem exists_gap {G : Type*} [Fintype G] [DecidableEq G] [One G] (s : G → ℝ)
    (hs : ∀ g, g ≠ 1 → 0 < s g) : ∃ δ > 0, ∀ g, g ≠ 1 → δ ≤ s g := by
  by_cases hne : (Finset.univ.filter fun g : G => g ≠ 1).Nonempty
  · obtain ⟨g₀, hg₀, hmin⟩ := Finset.exists_min_image _ s hne
    exact ⟨s g₀, hs g₀ (Finset.mem_filter.mp hg₀).2,
      fun g hg => hmin g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)⟩
  · exact ⟨1, one_pos, fun g hg =>
      absurd ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩⟩ hne⟩

/-- **In a finite gauge group flux cannot spread**: for a cost `s ≥ 0` positive off the identity
there is one `δ > 0` with `Σ s ≥ δ` for every list of plaquette holonomies whose product is not `1`,
of every length. -/
theorem finite_flux_cannot_spread {G : Type*} [Group G] [Fintype G] [DecidableEq G] (s : G → ℝ)
    (hs0 : ∀ g, 0 ≤ s g) (hs : ∀ g, g ≠ 1 → 0 < s g) :
    ∃ δ > 0, ∀ l : List G, l.prod ≠ 1 → δ ≤ (l.map s).sum := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap s hs
  exact ⟨δ, hδ, fun l h => flux_floor s hs0 hgap l h⟩

end MassGap.FluxTube

#print axioms MassGap.FluxTube.quad_split_ge
#print axioms MassGap.FluxTube.quad_split_equal
#print axioms MassGap.FluxTube.u1Spread_le
#print axioms MassGap.FluxTube.u1Spread_tendsto_zero
#print axioms MassGap.FluxTube.torus_mem
#print axioms MassGap.FluxTube.wilson_torus
#print axioms MassGap.FluxTube.wilson_torus_le
#print axioms MassGap.FluxTube.torus_centreAngles
#print axioms MassGap.FluxTube.centre_ne_one
#print axioms MassGap.FluxTube.thin_vortex_action
#print axioms MassGap.FluxTube.vortexPlaq_pow
#print axioms MassGap.FluxTube.stripLink_succ
#print axioms MassGap.FluxTube.stripLink_last
#print axioms MassGap.FluxTube.vortexConst_eq
#print axioms MassGap.FluxTube.vortex_action_le
#print axioms MassGap.FluxTube.thick_vortex_action_tendsto_zero
#print axioms MassGap.FluxTube.su2_vortex_eq_u1
#print axioms MassGap.FluxTube.centre_flux_spreads
#print axioms MassGap.FluxTube.su_flux_no_floor
#print axioms MassGap.FluxTube.flux_floor
#print axioms MassGap.FluxTube.finite_flux_cannot_spread
