import Mathlib
import MassGap.ApertureFinite

/-!
# MassGap.BareRatioProof — `BareRatio` from a positive, relatively summable bare correlator

`ApertureFinite.BareRatio S D ρ θ` asks, eventually along the tower and for every `O ∈ D`, for one `c ≥ 0` that
bounds the bare covariance `C_{xy} = ν_k(P_x P_y)` of the screen box in operator norm and has
`c ∑_β heatW_β ≤ Q ∑_y ν_k(F_y²)` for the heat screen `F`. This module proves `BareRatio` from one condition on
the bare correlator on the box (`RelSum`): every entry `C_{xy}` is non-negative, and every row sum is at most
`K₀` times a common lower bound `d` of the diagonal. With translation invariance, `d = C(0)` and the condition
reads `∑_z C(z) ≤ K₀ C(0)`, `C ≥ 0`. Declarations are in the namespace `MassGap.BareRatioProof`.

## 1. The Schur test (proved)

`state_sq_expand`: `ν((∑ u_x P_x)²) = ∑_x ∑_y u_x u_y ν(P_x P_y)`. `schur_rowSum`: if every absolute row sum
`∑_y |ν(P_x P_y)|` is at most `A`, then `ν((∑ u_x P_x)²) ≤ A ∑ u_x²`, for any state and any readings. This is the
operator-norm half of `BareRatio` from a row-sum bound. `diag_le_state_sq`: for non-negative coefficients and
non-negative entries, `∑_x v_x² ν(P_x²) ≤ ν((∑ v_x P_x)²)`.

## 2. The heat spectrum peaks at the lowest Dirichlet mode (proved)

`rheat_nonneg`, `sv_one_nonneg`: the helper signs used below.

`heatW_le_bot`: `heatW K θ β ≤ heatW K θ bot` for the lowest mode `bot = (0, 0, 0, 0)`, from
`FreeLevels.lev1_mono`. `sum_le_mul_spRenyi`: for `0 ≤ w ≤ M`, `∑ w ≤ M · spRenyi w`. Together with
`ApertureFinite.spRenyi_heatW_le`: `sum_heatW_le`, `∑_β heatW_β ≤ Rheat θ · heatW_bot`. `boxF_bot_nonneg`: the
lowest Dirichlet mode of the box is non-negative at every site.

## 3. One mode of a linear screen is at most its trace (proved)

`single_mode_le_trace`: `f_β² ν((∑_x w_{xβ} P_x)²) ≤ ∑_y ν(F_y²)` for the linear screen `F = linScreen P w f`.

## 4. `BareRatio` from the lowest mode, and from `RelSum` (proved)

`ratio_of_lowMode`: on one box, if `c ≥ 0` bounds the bare covariance in operator norm and
`c ≤ Q' ν((∑_x boxF_{x,bot} P_x)²)` (the operator norm within `Q'` of the lowest Dirichlet-mode variance), then
`c ∑_β heatW_β ≤ Q' Rheat θ ∑_y ν(F_y²)`. `bareRatio_of_lowMode` is the tower form: `LowModeRatio S D ρ Q'`
gives `BareRatio S D ρ θ` at `Q = Q' Rheat θ`, for every `θ > 0`. `relSum_lowMode`: on one box, non-negative
entries, diagonal at least `d` and row sums at most `K₀ d` give the lowest-mode inequality at `c = K₀ d`, `Q' = K₀`
(Schur for the operator norm; the lowest mode's non-negativity and the entries' signs for the lower bound).
`bareRatio_of_relSum`: `RelSum S D ρ K₀` with `K₀ ≥ 0` gives `BareRatio S D ρ θ` at `Q = K₀ Rheat θ`.

## 5. The paper tests

Every item below is argued on paper; none is formalized.

* Free field, linear plaquette angle (compact `U(1)` reading `sin θ_p` at Gaussian order). The field-strength
  correlator is `C(z) ∝ −(∂_μ² + ∂_ν²)|z|^{−2} = 4|z|^{−4} − 8(z_μ² + z_ν²)|z|^{−6}`: positive for `z` transverse to
  the plane, negative (`−4|z|^{−4}`) in the plane, and `∑_z |C(z)|` diverges logarithmically. `RelSum` fails
  here, while `BareRatio` holds (`Q → 2`, `ApertureFinite` §6). The class `SymPlaqG.SymPlaqClassG` has no linear
  term: a real class function of an `SU(N)` plaquette starts at `tr F²` (`tr F = 0`), and the symmetrised members
  are even.
* Free field, composite reading (the Gaussian order of the class). By Wick, `Cov(∑ F_a², ∑ F_b²) =
  2 ∑_{a,b} Cov(F_a, F_b)² ≥ 0`, so `C ≥ 0`; `C(z) ~ |z|^{−8}` is summable in four dimensions; and
  `C(z)/C(0) = ∑ G_{ab}(z)² / ∑ G_{ab}(0)²` with `G` the field-strength correlator in lattice units, independent of
  the coupling. So `RelSum` holds at Gaussian order with one `K₀` along every tower.
* Compact `U(1)`, Wilson action, `cos` readings: `C(z) ≥ 0` at every coupling is Ginibre's inequality; it is not
  in the tree. Relative summability: as in the composite free case at weak coupling.
* The transfer gap along a tower (`CouplingTower.observerGap_along`, rate `log 2 / 2^k`) gives decay
  `C(z) ≤ C(0) e^{−m_k |z|}` with `m_k → 0` in lattice units, so `∑_z C(z) ≤ C(0) · O(m_k^{−4})`, which grows like
  `2^{4k}`. The gap alone does not give a uniform `K₀`. The expected behaviour has a fixed `K₀`: the short-distance
  part (perturbative, `|z|^{−8}`) carries `C(0)` and the row sum at the same order in the coupling, and the
  glueball part contributes `O((a_k Λ)⁴ / g_k⁴)` relative to `C(0)`, which tends to `0`. Proving that is
  short-distance control of the plaquette two-point function along the tower.
* Strong coupling: at fixed small `β` the decay rate `~ log(1/β)` is large and `K₀` is finite, but a tower with
  `β_k → ∞` leaves that regime, so it does not enter "eventually".
* `SU(N)`, `N ≥ 2`: non-negativity of `C(z)` for all `z` is not known to follow from reflection positivity, which
  gives `⟨θ(A) A⟩ ≥ 0` for reflected pairs only. No example of a negative entry for the class is known here either.

## What does not follow

* `BareRatio` is not proved along any tower.
* `RelSum` is not proved for the Wilson measure at any coupling of the interacting theory; §5 checks it on paper
  at Gaussian order only. `bareRatio_of_relSum` moves `BareRatio` onto `RelSum`; it discharges neither.
* The missing inequalities are exactly the two clauses of `RelSum` beyond the diagonal: `0 ≤ ν_k(P_x P_y)` for all
  sites of the box, and `∑_y ν_k(P_x P_y) ≤ K₀ d` with `d ≤ ν_k(P_x²)`, one `K₀` eventually along the tower.
  The weaker `LowModeRatio` (operator norm within `Q'` of the lowest Dirichlet-mode variance) also suffices.
* Neither the transfer gap along the tower nor reflection positivity gives either clause (§5).
* `RelSum` is sufficient, not necessary: it fails for the linear angle reading, where `BareRatio` holds.
* The factor `Rheat θ` in `Q` comes from keeping only the lowest heat mode in the lower bound; it is not optimal.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the signs, the lowest mode and the empty case; `1` the unit column norm, the unit
weights of `heatW` and the lowest frequency; `2` the squares and the AM–GM halving `|ab| ≤ (a² + b²)/2`; `4` the
spacetime dimension; `π` the Dirichlet frequencies. CHOSEN: none beyond `ApertureFinite`'s box side `1` and
ladder `1/2` (Inherited through `heatW`, `Rheat`). `θ`, `ρ`, `K₀`, `Q'`, `c`, `d` hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.BareRatioProof

open Finset Filter
open scoped Real
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ClayTreeG MassGap.CountMoments
open MassGap.ApertureFinite
open MassGap.ApertureCount (spRenyi)

/-! ## 1. The Schur test -/

section Schur

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι]

/-- **The second moment of a combination, expanded**: `ν((∑ u_x P_x)²) = ∑_x ∑_y u_x u_y ν(P_x P_y)`.
DERIVED: `2` the square. -/
theorem state_sq_expand (P : ι → C(X, ℝ)) (u : ι → ℝ) :
    ν ((∑ x, u x • P x) ^ 2) = ∑ x, ∑ y, u x * u y * ν (P x * P y) := by
  rw [sq, Finset.sum_mul_sum, ν.map_sum]
  simp only [ν.map_sum, smul_mul_smul_comm, ν.map_smul]

/-- **The Schur test**: if every absolute row sum `∑_y |ν(P_x P_y)|` is at most `A`, then
`ν((∑ u_x P_x)²) ≤ A ∑ u_x²`. DERIVED: `2` the squares and the halving `|ab| ≤ (a² + b²)/2`. -/
theorem schur_rowSum (P : ι → C(X, ℝ)) {A : ℝ} (hA : ∀ x, ∑ y, |ν (P x * P y)| ≤ A) (u : ι → ℝ) :
    ν ((∑ x, u x • P x) ^ 2) ≤ A * ∑ x, u x ^ 2 := by
  rw [state_sq_expand]
  have hsym : ∀ x y, |ν (P y * P x)| = |ν (P x * P y)| := fun x y => by rw [mul_comm]
  have hterm : ∀ x y, u x * u y * ν (P x * P y)
      ≤ u x ^ 2 / 2 * |ν (P x * P y)| + u y ^ 2 / 2 * |ν (P y * P x)| := by
    intro x y
    rw [hsym x y]
    have h1 : u x * u y * ν (P x * P y) ≤ |u x * u y| * |ν (P x * P y)| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |u x * u y| ≤ (u x ^ 2 + u y ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|u x| - |u y|), sq_abs (u x), sq_abs (u y)]
    have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (ν (P x * P y)))
    linarith
  have e1 : ∑ x, ∑ y, u x ^ 2 / 2 * |ν (P x * P y)| = ∑ x, u x ^ 2 / 2 * ∑ y, |ν (P x * P y)| :=
    Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
  have e2 : ∑ x, ∑ y, u y ^ 2 / 2 * |ν (P y * P x)| = ∑ y, u y ^ 2 / 2 * ∑ x, |ν (P y * P x)| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  have b1 : ∑ x, u x ^ 2 / 2 * ∑ y, |ν (P x * P y)| ≤ A / 2 * ∑ x, u x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => by nlinarith [hA x, sq_nonneg (u x)]
  have b2 : ∑ y, u y ^ 2 / 2 * ∑ x, |ν (P y * P x)| ≤ A / 2 * ∑ y, u y ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => by nlinarith [hA y, sq_nonneg (u y)]
  have hsplit : ∑ x, ∑ y, (u x ^ 2 / 2 * |ν (P x * P y)| + u y ^ 2 / 2 * |ν (P y * P x)|)
      = ∑ x, ∑ y, u x ^ 2 / 2 * |ν (P x * P y)| + ∑ x, ∑ y, u y ^ 2 / 2 * |ν (P y * P x)| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib
  calc ∑ x, ∑ y, u x * u y * ν (P x * P y)
      ≤ ∑ x, ∑ y, (u x ^ 2 / 2 * |ν (P x * P y)| + u y ^ 2 / 2 * |ν (P y * P x)|) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ ≤ A * ∑ x, u x ^ 2 := by rw [hsplit, e1, e2]; linarith

/-- **The diagonal under non-negative entries**: for `v ≥ 0` and `ν(P_x P_y) ≥ 0`,
`∑_x v_x² ν(P_x P_x) ≤ ν((∑ v_x P_x)²)`. DERIVED: `2` the square; `0` the signs. -/
theorem diag_le_state_sq (P : ι → C(X, ℝ)) (v : ι → ℝ) (hv : ∀ x, 0 ≤ v x)
    (hC : ∀ x y, 0 ≤ ν (P x * P y)) :
    ∑ x, v x ^ 2 * ν (P x * P x) ≤ ν ((∑ x, v x • P x) ^ 2) := by
  rw [state_sq_expand]
  refine Finset.sum_le_sum fun x _ => ?_
  have h := Finset.single_le_sum (f := fun y => v x * v y * ν (P x * P y))
    (fun y _ => mul_nonneg (mul_nonneg (hv x) (hv y)) (hC x y)) (Finset.mem_univ x)
  calc v x ^ 2 * ν (P x * P x) = v x * v x * ν (P x * P x) := by ring
    _ ≤ _ := h

end Schur

#print axioms state_sq_expand
#print axioms schur_rowSum
#print axioms diag_le_state_sq

/-! ## 2. The heat spectrum peaks at the lowest Dirichlet mode -/

/-- **The lowest Dirichlet mode of the box**. DERIVED: `0` the lowest frequency index. -/
def bot0 (K : ℕ) (hK : 0 < K) : Fin 4 → Fin K := fun _ => ⟨0, hK⟩

/-- **The heat weight is largest at the lowest mode**: `heatW K θ β ≤ heatW K θ bot` for `θ ≥ 0`.
DERIVED: `1` the box side of `heatW`; `0` the sign of `θ`. -/
theorem heatW_le_bot {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 0 ≤ θ) (β : Fin 4 → Fin K) :
    heatW K θ β ≤ heatW K θ (bot0 K hK) := by
  simp only [heatW, Function.comp_apply, FreeLevels.heatSpec, one_mul]
  apply Real.exp_le_exp.2
  apply neg_le_neg
  unfold FreeLevels.boxU
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact Finset.sum_le_sum fun μ _ => FreeLevels.lev1_mono hK one_pos _

/-- **A sum is at most its maximum times its Rényi-½ count**: for `0 ≤ w ≤ M`, `∑ w ≤ M · spRenyi w`.
DERIVED: `2` the square; `0` the signs and the empty case. -/
theorem sum_le_mul_spRenyi {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw : ∀ α, 0 ≤ w α) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ α, w α ≤ M) : ∑ α, w α ≤ M * spRenyi w := by
  have hS : 0 ≤ ∑ α, w α := Finset.sum_nonneg fun α _ => hw α
  rw [spRenyi_eq_sq_div w hw]
  rcases hS.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, mul_zero]
  · have hlin : ∑ α, w α ≤ Real.sqrt M * ∑ α, Real.sqrt (w α) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ => ?_
      calc w α = Real.sqrt (w α) * Real.sqrt (w α) := (Real.mul_self_sqrt (hw α)).symm
        _ ≤ Real.sqrt M * Real.sqrt (w α) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hM α)) (Real.sqrt_nonneg _)
    have hsq : (∑ α, w α) ^ 2 ≤ M * (∑ α, Real.sqrt (w α)) ^ 2 := by
      have := pow_le_pow_left₀ hS hlin 2
      rwa [mul_pow, Real.sq_sqrt hM0] at this
    rw [mul_div_assoc', le_div_iff₀ hpos]
    nlinarith [hsq]

/-- **The heat trace is at most `Rheat θ` lowest weights**: `∑_β heatW_β ≤ heatW_bot · Rheat θ`.
DERIVED: `0` the sign of `θ`. -/
theorem sum_heatW_le {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 0 < θ) :
    ∑ β, heatW K θ β ≤ heatW K θ (bot0 K hK) * Rheat θ := by
  have hM0 := (heatW_pos K θ (bot0 K hK)).le
  exact (sum_le_mul_spRenyi _ (fun β => (heatW_pos K θ β).le) hM0 (heatW_le_bot hK hθ.le)).trans
    (mul_le_mul_of_nonneg_left (spRenyi_heatW_le K hK hθ) hM0)

/-- **`Rheat θ` is non-negative**. DERIVED: `1` the box size; `0` the sign. -/
theorem rheat_nonneg {θ : ℝ} (hθ : 0 < θ) : 0 ≤ Rheat θ := by
  have hR := spRenyi_heatW_le 1 one_pos hθ
  have h0 : 0 ≤ spRenyi (heatW 1 θ) := by unfold spRenyi; positivity
  exact h0.trans hR

/-- **The lowest Dirichlet sine is non-negative**: `sin(π (n + 1)/(K + 1)) ≥ 0` for `n < K`.
DERIVED: `1` the lowest frequency and the site shift; `π` the frequency. -/
theorem sv_one_nonneg (K : ℕ) (n : Fin K) : 0 ≤ sv K 1 n := by
  unfold sv
  have hn : ((n : ℕ) : ℝ) + 1 ≤ (K : ℝ) + 1 := by
    have := n.isLt
    have : ((n : ℕ) : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast this
    linarith
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ (by positivity), Nat.cast_one, mul_one]
    exact mul_le_mul_of_nonneg_left hn Real.pi_pos.le

/-- **The lowest Dirichlet mode of the box is non-negative at every site**. DERIVED: `0` the sign. -/
theorem boxF_bot_nonneg {K : ℕ} (hK : 0 < K) (x : Fin 4 → Fin K) : 0 ≤ boxF K x (bot0 K hK) := by
  unfold boxF
  refine Finset.prod_nonneg fun μ _ => ?_
  show 0 ≤ Real.sqrt (2 / ((K : ℝ) + 1)) * sv K 1 (x μ)
  exact mul_nonneg (Real.sqrt_nonneg _) (sv_one_nonneg K (x μ))

/-- **The lowest Dirichlet mode has unit norm**. DERIVED: `1` the norm; `2` the square. -/
theorem boxF_bot_sq {K : ℕ} (hK : 0 < K) : ∑ x, boxF K x (bot0 K hK) ^ 2 = 1 := by
  have h := boxF_cols K (bot0 K hK) (bot0 K hK)
  rw [if_pos rfl] at h
  simpa only [sq] using h

#print axioms heatW_le_bot
#print axioms sum_le_mul_spRenyi
#print axioms sum_heatW_le
#print axioms rheat_nonneg
#print axioms sv_one_nonneg
#print axioms boxF_bot_nonneg
#print axioms boxF_bot_sq

/-! ## 3. One mode of a linear screen is at most its trace -/

section Mode

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **One mode is at most the trace**: `f_β² ν((∑_x w_{xβ} P_x)²) ≤ ∑_y ν(F_y²)` for `F = linScreen P w f`.
DERIVED: `2` the squares; `0` the signs. -/
theorem single_mode_le_trace (P : ι → C(X, ℝ)) (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0) (β : ι) :
    f β ^ 2 * ν ((∑ x, w x β • P x) ^ 2) ≤ ∑ y, ν (linScreen P w f y ^ 2) := by
  rw [← sum_frame_eq_trace ν (linScreen P w f) w hrows]
  have hβ : ν ((∑ y, w y β • linScreen P w f y) ^ 2) = f β ^ 2 * ν ((∑ x, w x β • P x) ^ 2) := by
    rw [frame_comb_lin P w f hcols β, state_sq_expand, state_sq_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [← hβ]
  exact Finset.single_le_sum (f := fun β => ν ((∑ y, w y β • linScreen P w f y) ^ 2))
    (fun β _ => ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity)
    (Finset.mem_univ β)

end Mode

#print axioms single_mode_le_trace

/-! ## 4. `BareRatio` from the lowest mode, and from `RelSum` -/

section Box

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)

/-- **The heat ratio from the lowest mode, on one box**: if `c ≥ 0`, `Q' ≥ 0` and
`c ≤ Q' ν((∑_x boxF_{x,bot} P_x)²)`, then `c ∑_β heatW_β ≤ Q' Rheat θ ∑_y ν(F_y²)` for the heat screen
`F = linScreen P boxF heatF`. DERIVED: `2` the square; `0` the signs. -/
theorem ratio_of_lowMode {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 0 < θ) (P : (Fin 4 → Fin K) → C(X, ℝ))
    {c Q' : ℝ} (hc : 0 ≤ c) (hQ : 0 ≤ Q')
    (hlo : c ≤ Q' * ν ((∑ x, boxF K x (bot0 K hK) • P x) ^ 2)) :
    c * ∑ β, heatW K θ β ≤ Q' * Rheat θ * ∑ y, ν (linScreen P (boxF K) (heatF K θ) y ^ 2) := by
  have hM0 := heatW_pos K θ (bot0 K hK)
  have hR0 := rheat_nonneg hθ
  have hlow := single_mode_le_trace ν P (boxF K) (heatF K θ) (boxF_cols K) (boxF_rows K) (bot0 K hK)
  rw [show heatF K θ (bot0 K hK) ^ 2 = heatW K θ (bot0 K hK) from Real.sq_sqrt hM0.le] at hlow
  calc c * ∑ β, heatW K θ β ≤ c * (heatW K θ (bot0 K hK) * Rheat θ) :=
        mul_le_mul_of_nonneg_left (sum_heatW_le hK hθ) hc
    _ = Rheat θ * heatW K θ (bot0 K hK) * c := by ring
    _ ≤ Rheat θ * heatW K θ (bot0 K hK) * (Q' * ν ((∑ x, boxF K x (bot0 K hK) • P x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hlo (mul_nonneg hR0 hM0.le)
    _ = Q' * Rheat θ * (heatW K θ (bot0 K hK) * ν ((∑ x, boxF K x (bot0 K hK) • P x) ^ 2)) := by ring
    _ ≤ Q' * Rheat θ * ∑ y, ν (linScreen P (boxF K) (heatF K θ) y ^ 2) :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg hQ hR0)

/-- **A positive, relatively summable correlator on one box**: if every entry `ν(P_x P_y)` is non-negative,
every diagonal entry is at least `d` and every row sum is at most `K₀ d`, then `c = K₀ d ≥ 0` bounds the
covariance in operator norm and `c ≤ K₀ ν((∑_x boxF_{x,bot} P_x)²)`. DERIVED: `2` the square; `0` the signs;
`1` the unit norm of the lowest mode. -/
theorem relSum_lowMode {K : ℕ} (hK : 0 < K) (P : (Fin 4 → Fin K) → C(X, ℝ)) {K₀ d : ℝ} (hK₀ : 0 ≤ K₀)
    (hpos : ∀ x y, 0 ≤ ν (P x * P y)) (hdiag : ∀ x, d ≤ ν (P x * P x))
    (hrow : ∀ x, ∑ y, ν (P x * P y) ≤ K₀ * d) :
    0 ≤ K₀ * d ∧ (∀ u : (Fin 4 → Fin K) → ℝ, ν ((∑ x, u x • P x) ^ 2) ≤ K₀ * d * ∑ x, u x ^ 2) ∧
      K₀ * d ≤ K₀ * ν ((∑ x, boxF K x (bot0 K hK) • P x) ^ 2) := by
  refine ⟨(Finset.sum_nonneg fun y _ => hpos (bot0 K hK) y).trans (hrow (bot0 K hK)), fun u => ?_, ?_⟩
  · exact schur_rowSum ν P
      (fun x => (Finset.sum_congr rfl fun y _ => abs_of_nonneg (hpos x y)).trans_le (hrow x)) u
  · refine mul_le_mul_of_nonneg_left ?_ hK₀
    have h := diag_le_state_sq ν P (fun x => boxF K x (bot0 K hK)) (boxF_bot_nonneg hK) hpos
    calc d = ∑ x, boxF K x (bot0 K hK) ^ 2 * d := by rw [← Finset.sum_mul, boxF_bot_sq hK, one_mul]
      _ ≤ ∑ x, boxF K x (bot0 K hK) ^ 2 * ν (P x * P x) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hdiag x) (sq_nonneg _)
      _ ≤ _ := h

end Box

#print axioms ratio_of_lowMode
#print axioms relSum_lowMode

section Tower

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The operator norm within a fixed factor of the lowest Dirichlet-mode variance**: one `Q' ≥ 0` with,
eventually, for every `O ∈ D`, some `c ≥ 0` bounding the bare covariance on the box in operator norm and
`c ≤ Q' ν_k((∑_x boxF_{x,bot} P_x)²)`. DERIVED: `2` the squares; `0` the signs. -/
def LowModeRatio (S : Sched G) (D : Set (LField G)) (ρ Q' : ℝ) : Prop :=
  0 ≤ Q' ∧ ∀ᶠ k in atTop, ∀ O ∈ D, ∀ hK : 0 < scrSide S ρ k, ∃ c : ℝ, 0 ≤ c ∧
    (∀ u : (Fin 4 → Fin (scrSide S ρ k)) → ℝ,
      S.ν k ((∑ x, u x • bareScreen S ρ k O x) ^ 2) ≤ c * ∑ x, u x ^ 2) ∧
    c ≤ Q' * S.ν k ((∑ x, boxF (scrSide S ρ k) x (bot0 _ hK) • bareScreen S ρ k O x) ^ 2)

/-- **A positive, relatively summable bare correlator along the zoom**: eventually, for every `O ∈ D`, some
`d` with every entry `ν_k(P_x P_y)` of the screen box non-negative, every diagonal entry at least `d`, and every
row sum at most `K₀ d`. With translation invariance: `C ≥ 0` and `∑_z C(z) ≤ K₀ C(0)` on the box.
DERIVED: `0` the signs. -/
def RelSum (S : Sched G) (D : Set (LField G)) (ρ K₀ : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D, ∃ d : ℝ,
    (∀ x y, 0 ≤ S.ν k (bareScreen S ρ k O x * bareScreen S ρ k O y)) ∧
    (∀ x, d ≤ S.ν k (bareScreen S ρ k O x * bareScreen S ρ k O x)) ∧
    (∀ x, ∑ y, S.ν k (bareScreen S ρ k O x * bareScreen S ρ k O y) ≤ K₀ * d)

/-- **`BareRatio` from the lowest mode**: `LowModeRatio S D ρ Q'` gives `BareRatio S D ρ θ` at
`Q = Q' Rheat θ`, for every `θ > 0`. DERIVED: `0` the signs of `ρ`, `θ`. -/
theorem bareRatio_of_lowMode (S : Sched G) (D : Set (LField G)) {ρ θ Q' : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    (h : LowModeRatio S D ρ Q') : BareRatio S D ρ θ := by
  obtain ⟨hQ, hev⟩ := h
  refine ⟨Q' * Rheat θ, ?_⟩
  filter_upwards [hev] with k hk O hO
  have hK : 0 < scrSide S ρ k := Nat.ceil_pos.2 (div_pos hρ (S.a_pos k))
  obtain ⟨c, hc, hC, hlo⟩ := hk O hO hK
  exact ⟨c, hc, hC, ratio_of_lowMode (S.ν k) hK hθ (bareScreen S ρ k O) hc hQ hlo⟩

/-- **`LowModeRatio` from `RelSum`**: `RelSum S D ρ K₀` with `K₀ ≥ 0` gives `LowModeRatio S D ρ K₀`.
DERIVED: `0` the sign of `K₀`. -/
theorem lowMode_of_relSum (S : Sched G) (D : Set (LField G)) {ρ K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (h : RelSum S D ρ K₀) : LowModeRatio S D ρ K₀ := by
  refine ⟨hK₀, ?_⟩
  filter_upwards [h] with k hk O hO hK
  obtain ⟨d, hpos, hdiag, hrow⟩ := hk O hO
  obtain ⟨hc, hC, hlo⟩ := relSum_lowMode (S.ν k) hK (bareScreen S ρ k O) hK₀ hpos hdiag hrow
  exact ⟨K₀ * d, hc, hC, hlo⟩

/-- **`BareRatio` from a positive, relatively summable bare correlator**: `RelSum S D ρ K₀` with `K₀ ≥ 0`
gives `BareRatio S D ρ θ` at `Q = K₀ Rheat θ`, for every `θ > 0`. DERIVED: `0` the signs. -/
theorem bareRatio_of_relSum (S : Sched G) (D : Set (LField G)) {ρ θ K₀ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    (hK₀ : 0 ≤ K₀) (h : RelSum S D ρ K₀) : BareRatio S D ρ θ :=
  bareRatio_of_lowMode S D hρ hθ (lowMode_of_relSum S D hK₀ h)

/-- **A finite aperture holds a finite count, from `RelSum`**: the heat screen's Rényi-½ count is bounded along
the zoom. DERIVED: `0` the signs. -/
theorem count_heatScreen_of_relSum (S : Sched G) (D : Set (LField G)) {ρ θ K₀ : ℝ} (hρ : 0 < ρ)
    (hθ : 0 < θ) (hK₀ : 0 ≤ K₀) (h : RelSum S D ρ K₀) :
    ∃ Rb : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, spRenyi (MassGap.ApertureCount.eig (S.ν k) (heatScreen S θ ρ k O)) ≤ Rb :=
  count_heatScreen S D hρ hθ (bareRatio_of_relSum S D hρ hθ hK₀ h)

end Tower

#print axioms bareRatio_of_lowMode
#print axioms lowMode_of_relSum
#print axioms bareRatio_of_relSum
#print axioms count_heatScreen_of_relSum

end MassGap.BareRatioProof

end
