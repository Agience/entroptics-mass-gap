import Mathlib
import MassGap.PlaqShortDistance
import MassGap.CountMoments

/-!
# MassGap.ModeAzuma — sub-Gaussian moments along the link martingale of the Wilson state, and the ratio H1 needs

`CountMoments.ModeHyperG` (H1) asks one `C ≥ 0` with, eventually along the tower, for every unit eigenvector `v` of
the screen's Gram matrix, `ν_k((∑_y v_y F_y)^{2p}) ≤ (2p)! (C λ)^p`, `λ` the eigenvalue. This module proves the
moment bound that the DLR structure of the Wilson state gives through the martingale of
`PlaqShortDistance.chain`, at every `N ≠ 0`, every real `β` and every observable, with explicit constants, and
states the inequality that remains between it and H1. Declarations are in the namespace `MassGap.ModeAzuma`.

Throughout, `ν = periodicState hN β`, `γ_Λ = wspec hN β Λ`, `l_0, l_1, …` a sequence of links,
`Λ_i = past l i = {l_j : j < i}`, `h_i = γ_{Λ_i} F` (`lev`) and `D_i = h_i − h_{i+1}` (`incr`).

## 1. One conditional step on a state (proved)

`exp_le_chord`: on `[−c, c]` the exponential lies under its chord. `state_ex_le`: for any state `μ` and `D` with
`μ D = 0` and `|D| ≤ c` pointwise, `μ(e^{sD}) ≤ cosh(sc) ≤ e^{s²c²/2}`. `state_pow_le_of_mgf`: if
`μ(e^{sG}) ≤ e^{s²V/2}` at every real `s` and `V > 0`, then `μ(G^{2p}) ≤ (2p)! (4V)^p`
(from `|y|^{2p}/(2p)! ≤ e^{|y|} ≤ e^y + e^{−y}` at `s = V^{−1/2}`, and `2 e^{1/2} ≤ 4`).

## 2. The link martingale (proved)

`box_incr`: `γ_{Λ_{i+1}} D_i = 0` at every boundary condition (DLR consistency). `outside_wspec`: `h_j` does not
read `Λ_i` for `i ≤ j`. `mgf_chain`: if `|D_i| ≤ c_i` pointwise for `i < m`, then
`ν(e^{s(F − h_m)}) ≤ exp(s² ∑_{i<m} c_i² / 2)` at every real `s`: peel the finest increment, pull the coarser
factor out of `γ_{Λ_{i+1}}` (`FocusZoom.wspec_mul_outside`), bound the conditional exponential moment by §1 at the
box state of each boundary condition, and close with the DLR equation. `moment_chain`: with
`∑_{i<m} c_i² ≤ V`, `V > 0`, `ν((F − h_m)^{2p}) ≤ (2p)! (4V)^p`. This is Azuma–Hoeffding for the reversed
filtration that releases one link at a time; no product structure of the kernel and no coupling enters.

## 3. The increment bound on a sparse chain (proved)

`incr_eq_of_split`: on a `PlaqShortDistance.SparseSplit` (`F = f_i + r_i`, `f_i` off the earlier links, `r_i` off
`l_i`, `l_i` off the boundary links of `Λ_i`), `D_i = f_i − γ_{Λ_{i+1}} f_i`. `abs_incr_le_of_split`:
`|f_i| ≤ M_i` gives `|D_i| ≤ 2 M_i`. `abs_lin_le`: for `f_i = ∑_{y ∈ S_i} v_y G_y` with `|G_y| ≤ b`,
`|f_i| ≤ b ∑_{y ∈ S_i} |v_y|`: the increment is bounded by twice the bound of the readings times the sum of the
coefficients of the readings that touch `l_i`. `moment_sparse`: `ν((F − h_m)^{2p}) ≤ (2p)! (4V)^p` with
`∑_{i<m} (2 M_i)² ≤ V`.

## 4. The centred moment and the H1 shape (proved, conditional)

`moment_centred`: if moreover `|h_m − c₀| ≤ δ` pointwise and `δ² ≤ V`, then
`ν((F − c₀)^{2p}) ≤ (2p)! (32 V)^p`. `modeMoment_of_azuma`: if `32 V ≤ C λ`, this is the H1 bound
`ν((F − c₀)^{2p}) ≤ (2p)! (C λ)^p` for `F = ∑_y v_y F_y`. So along this route H1 at an eigenvector `(v, λ)` is
exactly the comparison

    32 · max(∑_{i<m} ‖D_i‖_∞², ‖h_m − c₀‖_∞²) ≤ C λ,

one `C` for every unit eigenvector, every field of the class and every step of the tower.

## 5. The paper test

Argued, not formalized. Write `ρ(v) = ∑_i ‖D_i‖_∞² / λ(v)`. For a centred `F`, the increments are
orthogonal and telescope, `ν(F²) − ν(h_m²) = ∑_i ν(D_i²)`, so `λ ≥ ∑_i ν(D_i²)`, so `ρ` is a ratio of sup norms to `ν`-averages of the same increments; it is at least `1`, and
H1 by this route needs `ρ` bounded.

* The increment bound "sum of the coefficients touching the link" holds only on a sparse chain (§3). On a sparse
  chain `h_m` is not constant: `F − h_m` is the fluctuation given the links off a sparse set, and the remainder
  `h_m − ν(F)` needs a uniform boundary-influence bound (`BoxFocusTest.KernelNear`), which is not proved at any
  coupling of the tower. On a chain that releases every link of a region, `γ_{Λ_i} F_y` reads `l_i` through the
  kernel whenever `l_i` is a boundary link of `Λ_i`, and `‖D_i‖_∞` is a Dobrushin influence sum
  `∑_y |v_y| b ∑_n (α^n)_{y, l_i}`; it is summable only under Dobrushin's condition `α < 1`
  (`BoxDobrushin`: Lean `β ≤ 1/40`). There, by Schur's test on the influence matrix,
  `∑_i ‖D_i‖_∞² ≤ (2 b z / (1 − α))² ∑_y v_y² = (2 b z / (1 − α))²`, `z` the number of links per reading.
* Coupling. At large `β` the plaquette reading fluctuates by `O(1/β)` in `ν` while its sup-norm oscillation over
  `SU(N)` is `O(N)`; so `ρ ≳ β²` already for unflowed bare readings on a fixed lattice box. Along the tower
  `β_k → ∞`, and `ρ` grows.
* Units. `PhysVarG` puts `ν_k(cRead²)` at `(σ a_k⁴)²`, while a flowed reading is bounded by an `O(1)` constant in
  lattice units. Spreading a link's influence over the `(√t / a_k)⁴` links of one flow radius (linearized flow,
  argued) gives `∑_l ‖D_l‖_∞² ~ a_k⁴ / t²` per reading against `λ ~ σ² a_k⁸`, so `ρ ~ a_k^{−4}`: a power of the
  screen side `L_k`.
* Small eigenvalues. The Azuma proxy of a unit vector does not decrease with `λ`, so `ρ(v) ≤ C` at every
  eigenvector forces `λ_min ≥ (proxy)/C`, a flat spectrum, while H3 (`CountBoundG`) needs a concentrated one.

So the ratio grows along the tower, by `β_k²` and by a power of `L_k`. It is bounded in one regime: small `β`
(Dobrushin, `α < 1`) on a fixed lattice box, unflowed readings, and an eigenvalue floor `λ ≥ κ b²`. That is the
strong-coupling end, not the tower.

## What does not follow

* H1 (`CountMoments.ModeHyperG`) is not proved at any tower or any coupling. `modeMoment_of_azuma` moves it onto
  the comparison of §4, which is the missing inequality of this route: one `C` with
  `32 · max(∑_i ‖D_i‖_∞², ‖h_m − ν(F)‖_∞²) ≤ C λ` for every unit eigenvector of every screen along the tower. §5
  argues that it fails there, by `β_k²` and by a power of the screen side; restating it is not discharging it.
* The increment bound is proved only on a sparse chain (`abs_incr_le_of_split`); no Dobrushin influence bound for
  a full release is proved here, and `BoxDobrushin` covers only `β ≤ 1/40`.
* The remainder `|h_m − c₀| ≤ δ` is a hypothesis; it is `BoxFocusTest.KernelNear`, not proved.
* The route reads sup norms of increments. A form-level replacement (a Freedman/Bernstein bound with the
  conditional quadratic variation `∑_i γ_{Λ_{i+1}}(D_i²)` in place of `∑_i ‖D_i‖_∞²`, or a log-Sobolev inequality
  with Herbst's argument) still needs a pointwise bound on a carré du champ, and none is in the tree for the
  Wilson measure at any `β > 0`; `BoxGap`, `KnabeEngine` and `HeatBathGapDecay` give spectral (Poincaré-type)
  gaps, which bound the second moment only.
* The flowed screen `cScreen` of H1 is not a finite combination of local readings of `periodicState`; §2–§4 apply
  to it only after the flow is truncated to a finite support, which is not done here.
* `ModeHyper` (Bonami on the spin cube) is a different measure; nothing here transfers it to the Wilson state.

`#print axioms` follows each section.

DERIVED (module-wide): `0` the signs, the empty past and `p = 0`; `1` the unit observable, the index step and
`(2p)! ≥ 1`; `2` the squares, the chord's two endpoints, the two tails `e^{±sG}` and the increment
`|f − γ f| ≤ 2M`; `1/2` the exponent `s²V/2` at `s² = 1/V`; `4 ≥ 2 e^{1/2}` the moment constant
(from `e < 2.7182818286`, inherited from `Real.exp_one_lt_d9`); `16 = 4 · 4` and `32 = 2 · 16` the centred
constant (the `2^{2p}` of `CountMoments.add_pow_even_le` times `4^p`, and the two summands). `1/40`, `α`, `z`, `κ`,
`σ`, `t` and the exponents of §5 appear only in the argued text. `c_i`, `M_i`, `V`, `δ`, `C`, `λ` are hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ModeAzuma

open Finset
open MassGap.GibbsSpec
open MassGap.DLRLimit (State IsLocalOnC)
open MassGap.PeriodicStateDLR (wspec wspec_add periodicState_dlr periodicState_dlr_nested wspec_empty)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.BoxFocusTest (boxState boxState_apply wspec_splice_self)
open MassGap.FocusZoom (wspec_mul_outside abs_state_le)
open MassGap.PlaqShortDistance (Outside past past_zero past_mono SparseSplit wspec_of_outside outside_of_local
  local_wspec)
open MassGap.CountMoments (add_pow_even_le)

/-! ## 1. One conditional step on a state -/

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The exponential of a scaled observable**: `x ↦ e^{s h(x)}`. DERIVED: no numeral. -/
def ex (s : ℝ) (h : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => Real.exp (s * h x), Real.continuous_exp.comp (continuous_const.mul h.continuous)⟩

theorem ex_apply (s : ℝ) (h : C(X, ℝ)) (x : X) : ex s h x = Real.exp (s * h x) := rfl

/-- `e^{s(f + g)} = e^{sf} e^{sg}`. DERIVED: no numeral. -/
theorem ex_add (s : ℝ) (f g : C(X, ℝ)) : ex s (f + g) = ex s f * ex s g := by
  ext x
  simp only [ex_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply, mul_add, Real.exp_add]

/-- `e^{s · 0} = 1`. DERIVED: `0`, `1`. -/
theorem ex_zero (s : ℝ) : ex s (0 : C(X, ℝ)) = 1 := by
  ext x
  simp [ex_apply]

/-- **The exponential lies under its chord on `[−c, c]`**: for `|x| ≤ c`, `c > 0`,
`e^{sx} ≤ (e^{sc} + e^{−sc})/2 + ((e^{sc} − e^{−sc})/(2c)) x`. DERIVED: `2` the two endpoints. -/
theorem exp_le_chord {s c x : ℝ} (hc : 0 < c) (hx : |x| ≤ c) :
    Real.exp (s * x) ≤ (Real.exp (s * c) + Real.exp (-(s * c))) / 2
      + (Real.exp (s * c) - Real.exp (-(s * c))) / (2 * c) * x := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  have ha : 0 ≤ (c + x) / (2 * c) := div_nonneg (by linarith) hc2.le
  have hb : 0 ≤ (c - x) / (2 * c) := div_nonneg (by linarith) hc2.le
  have hab : (c + x) / (2 * c) + (c - x) / (2 * c) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hc2.ne']
    ring
  have hconv := convexOn_exp.2 (Set.mem_univ (s * c)) (Set.mem_univ (-(s * c))) ha hb hab
  simp only [smul_eq_mul] at hconv
  have e1 : (c + x) / (2 * c) * (s * c) + (c - x) / (2 * c) * -(s * c) = s * x := by
    field_simp
    ring
  have e2 : (c + x) / (2 * c) * Real.exp (s * c) + (c - x) / (2 * c) * Real.exp (-(s * c))
      = (Real.exp (s * c) + Real.exp (-(s * c))) / 2
        + (Real.exp (s * c) - Real.exp (-(s * c))) / (2 * c) * x := by
    field_simp
    ring
  rw [e1, e2] at hconv
  exact hconv

/-- **The conditional Hoeffding step on a state**: `μ D = 0` and `|D| ≤ c` give `μ(e^{sD}) ≤ e^{s²c²/2}`, at every
real `s`. DERIVED: `0` the mean; `2` the square and the half of `cosh ≤ e^{x²/2}`. -/
theorem state_ex_le (μ : State X) (D : C(X, ℝ)) (hD : μ D = 0) {c : ℝ} (hc : 0 ≤ c)
    (hDc : ∀ x, |D x| ≤ c) (s : ℝ) : μ (ex s D) ≤ Real.exp (s ^ 2 * c ^ 2 / 2) := by
  rcases hc.eq_or_lt with h0 | hpos
  · have hD0 : ex s D = 1 := by
      ext x
      have h := abs_nonpos_iff.mp ((hDc x).trans h0.symm.le)
      rw [ex_apply, h, mul_zero, Real.exp_zero, ContinuousMap.one_apply]
    rw [hD0, μ.map_one]
    exact Real.one_le_exp (by positivity)
  · have hle : ∀ x, ex s D x ≤ (((Real.exp (s * c) + Real.exp (-(s * c))) / 2) • (1 : C(X, ℝ))
        + ((Real.exp (s * c) - Real.exp (-(s * c))) / (2 * c)) • D) x := fun x => by
      rw [ex_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, smul_eq_mul, mul_one]
      exact exp_le_chord hpos (hDc x)
    have h1 := μ.mono hle
    rw [μ.map_add, μ.map_smul, μ.map_smul, μ.map_one, hD, mul_zero, add_zero, mul_one] at h1
    calc μ (ex s D) ≤ (Real.exp (s * c) + Real.exp (-(s * c))) / 2 := h1
      _ = Real.cosh (s * c) := (Real.cosh_eq _).symm
      _ ≤ Real.exp ((s * c) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = Real.exp (s ^ 2 * c ^ 2 / 2) := by rw [mul_pow]

/-- **An even power under the two exponential tails**: `s^{2p} G(x)^{2p} ≤ (2p)! (e^{sG(x)} + e^{−sG(x)})`.
DERIVED: `2` the even power and the two tails. -/
theorem pow_le_ex (s : ℝ) (G : C(X, ℝ)) (p : ℕ) (x : X) :
    s ^ (2 * p) * (G ^ (2 * p)) x ≤ ((2 * p).factorial : ℝ) * (ex s G x + ex (-s) G x) := by
  rw [ContinuousMap.pow_apply, ex_apply, ex_apply, ← mul_pow, ← (even_two_mul p).pow_abs (s * G x)]
  have h1 := Real.pow_div_factorial_le_exp _ (abs_nonneg (s * G x)) (2 * p)
  have hf : (0 : ℝ) < ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : Real.exp |s * G x| ≤ Real.exp (s * G x) + Real.exp (-s * G x) := by
    rcases abs_cases (s * G x) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-s * G x)]
    · rw [h, neg_mul]; linarith [Real.exp_pos (s * G x)]
  rw [div_le_iff₀ hf] at h1
  calc |s * G x| ^ (2 * p) ≤ Real.exp |s * G x| * ((2 * p).factorial : ℝ) := h1
    _ = ((2 * p).factorial : ℝ) * Real.exp |s * G x| := mul_comm _ _
    _ ≤ ((2 * p).factorial : ℝ) * (Real.exp (s * G x) + Real.exp (-s * G x)) :=
      mul_le_mul_of_nonneg_left h2 hf.le

/-- `e^{1/2} < 2`. DERIVED: `1/2`, `2`; Inherited: `2.7182818286` from `Real.exp_one_lt_d9`. -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

/-- **Sub-Gaussian moments from the exponential moment**: if `μ(e^{sG}) ≤ e^{s²V/2}` at every real `s` and `V > 0`,
then `μ(G^{2p}) ≤ (2p)! (4V)^p`. DERIVED: `4 ≥ 2 e^{1/2}`; `1/2` at `s² = 1/V`; `2` the two tails. -/
theorem state_pow_le_of_mgf (μ : State X) (G : C(X, ℝ)) {V : ℝ} (hV : 0 < V)
    (hmgf : ∀ s : ℝ, μ (ex s G) ≤ Real.exp (s ^ 2 * V / 2)) (p : ℕ) :
    μ (G ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (4 * V) ^ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [μ.map_one]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (Real.sqrt V)⁻¹ := ⟨_, rfl⟩
  have hs2 : s ^ 2 = V⁻¹ := by rw [hs, inv_pow, Real.sq_sqrt hV.le]
  have hsp : s ^ (2 * p) = (V ^ p)⁻¹ := by rw [pow_mul, hs2, inv_pow]
  have hpt : ∀ x, (s ^ (2 * p) • G ^ (2 * p)) x
      ≤ (((2 * p).factorial : ℝ) • (ex s G + ex (-s) G)) x := fun x => by
    rw [ContinuousMap.smul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
      smul_eq_mul]
    exact pow_le_ex s G p x
  have h1 := μ.mono hpt
  rw [μ.map_smul, μ.map_smul, μ.map_add, hsp] at h1
  have hm1 := hmgf s
  have hm2 := hmgf (-s)
  rw [neg_sq, hs2, inv_mul_cancel₀ hV.ne'] at hm2
  rw [hs2, inv_mul_cancel₀ hV.ne'] at hm1
  have he := exp_half_lt_two
  have hVp : 0 < V ^ p := pow_pos hV p
  have hf : (0 : ℝ) ≤ ((2 * p).factorial : ℝ) := by positivity
  have h4 : (4 : ℝ) ≤ 4 ^ p := by
    calc (4 : ℝ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have h5 : μ (G ^ (2 * p)) = V ^ p * ((V ^ p)⁻¹ * μ (G ^ (2 * p))) := by
    rw [← mul_assoc, mul_inv_cancel₀ hVp.ne', one_mul]
  have key : μ (G ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (4 * V ^ p) := by
    rw [h5]
    calc V ^ p * ((V ^ p)⁻¹ * μ (G ^ (2 * p)))
        ≤ V ^ p * (((2 * p).factorial : ℝ) * (μ (ex s G) + μ (ex (-s) G))) :=
          mul_le_mul_of_nonneg_left h1 hVp.le
      _ ≤ V ^ p * (((2 * p).factorial : ℝ) * 4) := by
          apply mul_le_mul_of_nonneg_left _ hVp.le
          apply mul_le_mul_of_nonneg_left _ hf
          linarith
      _ = ((2 * p).factorial : ℝ) * (4 * V ^ p) := by ring
  calc μ (G ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (4 * V ^ p) := key
    _ ≤ ((2 * p).factorial : ℝ) * (4 ^ p * V ^ p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hVp.le) hf
    _ = ((2 * p).factorial : ℝ) * (4 * V) ^ p := by rw [mul_pow]

/-- **A linear combination of bounded readings is bounded by the sum of its coefficients**:
`|∑_{y ∈ S} v_y G_y| ≤ b ∑_{y ∈ S} |v_y|` when `|G_y| ≤ b`. DERIVED: no numeral. -/
theorem abs_lin_le {ι : Type*} (S : Finset ι) (v : ι → ℝ) (G : ι → C(X, ℝ)) {b : ℝ}
    (hG : ∀ y ∈ S, ∀ x, |G y x| ≤ b) (x : X) :
    |(∑ y ∈ S, v y • G y) x| ≤ b * ∑ y ∈ S, |v y| := by
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc |∑ y ∈ S, v y * G y x| ≤ ∑ y ∈ S, |v y * G y x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ S, |v y| * b := Finset.sum_le_sum fun y hy => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hG y hy x) (abs_nonneg _)
    _ = b * ∑ y ∈ S, |v y| := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Generic

#print axioms ex_apply
#print axioms ex_add
#print axioms ex_zero
#print axioms exp_le_chord
#print axioms state_ex_le
#print axioms pow_le_ex
#print axioms exp_half_lt_two
#print axioms state_pow_le_of_mgf
#print axioms abs_lin_le

/-! ## 2. The link martingale -/

section Wilson

variable {N : ℕ}

/-- **An observable not reading `A` takes one value on configurations that agree off `A`**. DERIVED: no
numeral. -/
theorem agree_of_outside {A : Finset ILink} {g : C(IConf (SU N), ℝ)} (hA : Outside A g)
    {ω ω' : IConf (SU N)} (h : ∀ l, l ∉ A → ω' l = ω l) : g ω' = g ω := by
  have e : ω' = splice A (fun x : ↥A => ω' (x : ILink)) ω := by
    funext l
    by_cases hl : l ∈ A
    · rw [splice_mem hl]
    · rw [splice_not_mem hl, h l hl]
  rw [e]
  exact hA _ ω

/-- **The box kernel does not read its box**. DERIVED: no numeral. -/
theorem outside_self (hN : N ≠ 0) (β : ℝ) (B : Finset ILink) (g : C(IConf (SU N), ℝ)) :
    Outside B (wspec hN β B g) := fun u ω => wspec_splice_self hN β B g u ω

/-- **The box kernel does not read a sub-box**: for `A ⊆ B`, `γ_B g` does not read `A`. DERIVED: no numeral. -/
theorem outside_wspec (hN : N ≠ 0) (β : ℝ) {A B : Finset ILink} (hAB : A ⊆ B) (g : C(IConf (SU N), ℝ)) :
    Outside A (wspec hN β B g) := fun _ _ =>
  agree_of_outside (outside_self hN β B g) fun _ hl => splice_not_mem fun hlA => hl (hAB hlA)

/-- **Not reading two sets is not reading their union**. DERIVED: no numeral. -/
theorem outside_union {A S : Finset ILink} {g : C(IConf (SU N), ℝ)} (hA : Outside A g)
    (hS : Outside S g) : Outside (A ∪ S) g := fun u ω => by
  classical
  have h1 : g (fun l => if l ∈ S then splice (A ∪ S) u ω l else ω l) = g (splice (A ∪ S) u ω) :=
    agree_of_outside hA fun l hl => by
      by_cases hlS : l ∈ S
      · rw [if_pos hlS]
      · rw [if_neg hlS, splice_not_mem (by simp [hl, hlS])]
  have h2 : g (fun l => if l ∈ S then splice (A ∪ S) u ω l else ω l) = g ω :=
    agree_of_outside hS fun l hl => by
      rw [if_neg hl]
  exact h1.symm.trans h2

/-- Not reading `A` is kept by differences. DERIVED: no numeral. -/
theorem outside_sub {A : Finset ILink} {f g : C(IConf (SU N), ℝ)} (hf : Outside A f) (hg : Outside A g) :
    Outside A (f - g) := fun u ω => by
  rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hf u ω, hg u ω]

/-- Not reading `A` is kept by the exponential. DERIVED: no numeral. -/
theorem outside_ex {A : Finset ILink} {g : C(IConf (SU N), ℝ)} (hg : Outside A g) (s : ℝ) :
    Outside A (ex s g) := fun u ω => by
  rw [ex_apply, ex_apply, hg u ω]

/-- **The level `i` of the link martingale**: `h_i = γ_{Λ_i} F`. DERIVED: no numeral. -/
def lev (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (i : ℕ) : C(IConf (SU N), ℝ) :=
  wspec hN β (past l i) F

/-- **The increment released with `l_i`**: `D_i = h_i − h_{i+1}`. DERIVED: `1` the index step. -/
def incr (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (i : ℕ) : C(IConf (SU N), ℝ) :=
  lev hN β l F i - lev hN β l F (i + 1)

/-- `h_0 = F`. DERIVED: `0` the empty past. -/
theorem lev_zero (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) : lev hN β l F 0 = F := by
  rw [lev, past_zero, wspec_empty]

/-- `γ_{Λ_{i+1}} h_i = h_{i+1}`. DERIVED: `1` the index step. -/
theorem lev_succ (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (i : ℕ) :
    wspec hN β (past l (i + 1)) (lev hN β l F i) = lev hN β l F (i + 1) :=
  (periodicState_dlr_nested hN β (past_mono l i) F).1

/-- The pasts are nested. DERIVED: no numeral. -/
theorem past_le (l : ℕ → ILink) {i j : ℕ} (h : i ≤ j) : past l i ⊆ past l j :=
  image_subset_image (range_subset_range.2 h)

/-- **The increment has conditional mean zero at every boundary condition**: `γ_{Λ_{i+1}} D_i = 0`. DERIVED:
`0`; `1` the index step. -/
theorem box_incr (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (i : ℕ) (ω : IConf (SU N)) :
    boxState hN β (past l (i + 1)) ω (incr hN β l F i) = 0 := by
  have e2 : wspec hN β (past l (i + 1)) (lev hN β l F (i + 1)) = lev hN β l F (i + 1) :=
    (periodicState_dlr_nested hN β (Finset.Subset.refl _) F).1
  rw [incr, (boxState hN β (past l (i + 1)) ω).map_sub, boxState_apply, boxState_apply, lev_succ, e2,
    sub_self]

/-- **Azuma along the link martingale, from step `i`**: if `|D_j| ≤ c_j` for `j < m`, then for `i ≤ m`,
`ν(e^{s(h_i − h_m)}) ≤ exp(s² ∑_{i ≤ j < m} c_j² / 2)`. DERIVED: `0`; `1` the index step; `2` the squares. -/
theorem mgf_tail (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (c : ℕ → ℝ) (m : ℕ)
    (hc0 : ∀ i < m, 0 ≤ c i) (hc : ∀ i < m, ∀ ω, |incr hN β l F i ω| ≤ c i) (s : ℝ) (n : ℕ) :
    ∀ i, i + n = m → periodicState hN β (ex s (lev hN β l F i - lev hN β l F m))
      ≤ Real.exp (s ^ 2 * (∑ j ∈ Ico i m, c j ^ 2) / 2) := by
  induction n with
  | zero =>
    intro i hi
    rw [add_zero] at hi
    subst hi
    rw [sub_self, ex_zero, (periodicState hN β).map_one, Ico_self, sum_empty, mul_zero, zero_div,
      Real.exp_zero]
  | succ n ih =>
    intro i hi
    have him : i < m := by omega
    have hrest := ih (i + 1) (by omega)
    have hdec : lev hN β l F i - lev hN β l F m
        = incr hN β l F i + (lev hN β l F (i + 1) - lev hN β l F m) := by
      rw [incr]; abel
    have hR : Outside (past l (i + 1)) (ex s (lev hN β l F (i + 1) - lev hN β l F m)) :=
      outside_ex (outside_sub (outside_wspec hN β (Finset.Subset.refl _) F)
        (outside_wspec hN β (past_le l (by omega : i + 1 ≤ m)) F)) s
    have e1 : periodicState hN β (ex s (lev hN β l F i - lev hN β l F m))
        = periodicState hN β (wspec hN β (past l (i + 1)) (ex s (incr hN β l F i))
            * ex s (lev hN β l F (i + 1) - lev hN β l F m)) := by
      rw [hdec, ex_add, ← periodicState_dlr hN β (past l (i + 1))
        (ex s (incr hN β l F i) * ex s (lev hN β l F (i + 1) - lev hN β l F m)),
        wspec_mul_outside hN β _ _ _ hR]
    have hpt : ∀ ω, (wspec hN β (past l (i + 1)) (ex s (incr hN β l F i))
          * ex s (lev hN β l F (i + 1) - lev hN β l F m)) ω
        ≤ (Real.exp (s ^ 2 * c i ^ 2 / 2) • ex s (lev hN β l F (i + 1) - lev hN β l F m)) ω := fun ω => by
      rw [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by rw [ex_apply]; exact (Real.exp_pos _).le)
      rw [← boxState_apply]
      exact state_ex_le (boxState hN β (past l (i + 1)) ω) _ (box_incr hN β l F i ω) (hc0 i him)
        (hc i him) s
    have h2 := (periodicState hN β).mono hpt
    rw [(periodicState hN β).map_smul] at h2
    rw [e1]
    calc _ ≤ _ := h2
      _ ≤ Real.exp (s ^ 2 * c i ^ 2 / 2) * Real.exp (s ^ 2 * (∑ j ∈ Ico (i + 1) m, c j ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hrest (Real.exp_pos _).le
      _ = Real.exp (s ^ 2 * (∑ j ∈ Ico i m, c j ^ 2) / 2) := by
          rw [← Real.exp_add, Finset.sum_eq_sum_Ico_succ_bot him]
          congr 1
          ring

/-- **Azuma along the link martingale**: if `|D_i| ≤ c_i` pointwise for `i < m`, then
`ν(e^{s(F − h_m)}) ≤ exp(s² ∑_{i<m} c_i² / 2)` at every real `s`, every `N ≠ 0` and every real `β`.
DERIVED: `0` the start of the chain; `2` the squares. -/
theorem mgf_chain (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (c : ℕ → ℝ) (m : ℕ)
    (hc0 : ∀ i < m, 0 ≤ c i) (hc : ∀ i < m, ∀ ω, |incr hN β l F i ω| ≤ c i) (s : ℝ) :
    periodicState hN β (ex s (F - lev hN β l F m)) ≤ Real.exp (s ^ 2 * (∑ i ∈ range m, c i ^ 2) / 2) := by
  have h := mgf_tail hN β l F c m hc0 hc s m 0 (zero_add m)
  rw [lev_zero, ← Finset.range_eq_Ico] at h
  exact h

/-- **Sub-Gaussian moments along the link martingale**: with `|D_i| ≤ c_i` for `i < m`, `∑_{i<m} c_i² ≤ V` and
`V > 0`, `ν((F − h_m)^{2p}) ≤ (2p)! (4V)^p`. DERIVED: `4` from `state_pow_le_of_mgf`; `2` the squares. -/
theorem moment_chain (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (c : ℕ → ℝ) (m : ℕ)
    (hc0 : ∀ i < m, 0 ≤ c i) (hc : ∀ i < m, ∀ ω, |incr hN β l F i ω| ≤ c i) {V : ℝ} (hV : 0 < V)
    (hcV : ∑ i ∈ range m, c i ^ 2 ≤ V) (p : ℕ) :
    periodicState hN β ((F - lev hN β l F m) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (4 * V) ^ p :=
  state_pow_le_of_mgf _ _ hV (fun s => (mgf_chain hN β l F c m hc0 hc s).trans
    (Real.exp_le_exp.2 (by gcongr))) p

#print axioms agree_of_outside
#print axioms outside_self
#print axioms outside_wspec
#print axioms outside_union
#print axioms outside_sub
#print axioms outside_ex
#print axioms lev_zero
#print axioms lev_succ
#print axioms past_le
#print axioms box_incr
#print axioms mgf_tail
#print axioms mgf_chain
#print axioms moment_chain

/-! ## 3. The increment bound on a sparse chain -/

/-- `Λ_{i+1} = {l_i} ∪ Λ_i`. DERIVED: `1` the index step. -/
theorem past_succ (l : ℕ → ILink) (i : ℕ) : past l (i + 1) = {l i} ∪ past l i := by
  rw [past, past, range_add_one, image_insert, insert_eq]

/-- **On a sparse split the increment is the local piece minus its kernel**: `D_i = f_i − γ_{Λ_{i+1}} f_i`.
DERIVED: `1` the index step. -/
theorem incr_eq_of_split (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m)
    {i : ℕ} (hi : i < m) :
    incr hN β sp.l F i = sp.f i - wspec hN β (past sp.l (i + 1)) (sp.f i) := by
  have hfo : Outside (past sp.l i) (sp.f i) := outside_of_local (sp.locf i hi) fun x hx hxp => by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hxp
    exact sp.early i hi j (mem_range.mp hj) hx
  have hro : Outside {sp.l i} (wspec hN β (past sp.l i) (sp.r i)) :=
    outside_of_local (local_wspec hN β _ (sp.locr i hi)) fun x hx hxl => by
      rw [mem_singleton] at hxl
      subst hxl
      rcases mem_union.mp hx with h1 | h1
      · exact sp.own i hi h1
      · exact sp.apart i hi h1
  have hρB : Outside (past sp.l (i + 1)) (wspec hN β (past sp.l i) (sp.r i)) := by
    rw [past_succ]
    exact outside_union hro (outside_self hN β _ _)
  have e : wspec hN β (past sp.l i) F = sp.f i + wspec hN β (past sp.l i) (sp.r i) := by
    rw [congrArg (wspec hN β (past sp.l i)) (sp.dec i hi), wspec_add, wspec_of_outside hN β _ _ hfo]
  unfold incr
  rw [← lev_succ hN β sp.l F i]
  unfold lev
  rw [e, wspec_add, wspec_of_outside hN β _ _ hρB]
  abel

/-- **The increment bound on a sparse chain**: `|f_i| ≤ M_i` gives `|D_i| ≤ 2 M_i`. DERIVED: `2` the two
terms. -/
theorem abs_incr_le_of_split (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m)
    (M : ℕ → ℝ) (hM : ∀ i < m, ∀ ω, |sp.f i ω| ≤ M i) : ∀ i < m, ∀ ω, |incr hN β sp.l F i ω| ≤ 2 * M i := by
  intro i hi ω
  rw [incr_eq_of_split hN β sp hi, ContinuousMap.sub_apply]
  have h2 : |wspec hN β (past sp.l (i + 1)) (sp.f i) ω| ≤ M i :=
    abs_state_le (boxState hN β (past sp.l (i + 1)) ω) (sp.f i) ω (hM i hi)
  obtain ⟨a1, a2⟩ := abs_le.1 (hM i hi ω)
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Sub-Gaussian moments on a sparse chain**: with `|f_i| ≤ M_i`, `∑_{i<m} (2 M_i)² ≤ V` and `V > 0`,
`ν((F − h_m)^{2p}) ≤ (2p)! (4V)^p`. DERIVED: `2` the increment bound; `4` from `moment_chain`. -/
theorem moment_sparse (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m)
    (M : ℕ → ℝ) (hM : ∀ i < m, ∀ ω, |sp.f i ω| ≤ M i) {V : ℝ} (hV : 0 < V)
    (hMV : ∑ i ∈ range m, (2 * M i) ^ 2 ≤ V) (p : ℕ) :
    periodicState hN β ((F - lev hN β sp.l F m) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (4 * V) ^ p :=
  moment_chain hN β sp.l F (fun i => 2 * M i) m
    (fun i hi => by
      have h := (abs_nonneg _).trans (hM i hi 1)
      show 0 ≤ 2 * M i
      linarith)
    (abs_incr_le_of_split hN β sp M hM) hV hMV p

#print axioms past_succ
#print axioms incr_eq_of_split
#print axioms abs_incr_le_of_split
#print axioms moment_sparse

/-! ## 4. The centred moment and the H1 shape -/

/-- **The centred moment**: with the hypotheses of `moment_chain` and a remainder `|h_m − c₀| ≤ δ`, `δ² ≤ V`,
`ν((F − c₀)^{2p}) ≤ (2p)! (32 V)^p`. DERIVED: `32 = 2 · 16`, `16 = 4 · 4` (the `2^{2p}` of `add_pow_even_le`
and the `4^p` of `moment_chain`, then the two summands); `1` the floor `(2p)! ≥ 1`. -/
theorem moment_centred (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (c : ℕ → ℝ) (m : ℕ)
    (hc0 : ∀ i < m, 0 ≤ c i) (hc : ∀ i < m, ∀ ω, |incr hN β l F i ω| ≤ c i) {V : ℝ} (hV : 0 < V)
    (hcV : ∑ i ∈ range m, c i ^ 2 ≤ V) (c₀ δ : ℝ) (hδ : ∀ ω, |lev hN β l F m ω - c₀| ≤ δ) (hδV : δ ^ 2 ≤ V)
    (p : ℕ) :
    periodicState hN β ((F - c₀ • (1 : C(IConf (SU N), ℝ))) ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) * (32 * V) ^ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [(periodicState hN β).map_one]
  have hmom := moment_chain hN β l F c m hc0 hc hV hcV p
  have hpt : ∀ ω, ((F - c₀ • (1 : C(IConf (SU N), ℝ))) ^ (2 * p)) ω
      ≤ ((2 : ℝ) ^ (2 * p) • (F - lev hN β l F m) ^ (2 * p)
        + ((2 : ℝ) ^ (2 * p) * V ^ p) • (1 : C(IConf (SU N), ℝ))) ω := fun ω => by
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.pow_apply,
      ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    have e : F ω - c₀ = (F ω - lev hN β l F m ω) + (lev hN β l F m ω - c₀) := by ring
    rw [e]
    have h1 := add_pow_even_le (F ω - lev hN β l F m ω) (lev hN β l F m ω - c₀) p
    have h2 : (lev hN β l F m ω - c₀) ^ (2 * p) ≤ V ^ p := by
      rw [← (even_two_mul p).pow_abs, pow_mul]
      exact pow_le_pow_left₀ (by positivity)
        ((pow_le_pow_left₀ (abs_nonneg _) (hδ ω) 2).trans hδV) p
    have h3 : (0 : ℝ) ≤ 2 ^ (2 * p) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have h1 := (periodicState hN β).mono hpt
  rw [(periodicState hN β).map_add, (periodicState hN β).map_smul, (periodicState hN β).map_smul,
    (periodicState hN β).map_one, mul_one] at h1
  have e4 : (2 : ℝ) ^ (2 * p) = 4 ^ p := by rw [pow_mul]; norm_num
  rw [e4] at h1
  have hW : 0 ≤ V ^ p := pow_nonneg hV.le p
  have hx : (1 : ℝ) ≤ 4 ^ p := one_le_pow₀ (by norm_num)
  have hA : (1 : ℝ) ≤ ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have ht : (2 : ℝ) ≤ 2 ^ p := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have e5 : (4 * V) ^ p = 4 ^ p * V ^ p := mul_pow _ _ _
  have e6 : (32 * V) ^ p = 2 ^ p * (4 ^ p * (4 ^ p * V ^ p)) := by
    rw [mul_pow, show (32 : ℝ) = 2 * (4 * 4) by norm_num, mul_pow, mul_pow]; ring
  rw [e5] at hmom
  rw [e6]
  set x : ℝ := 4 ^ p
  set A : ℝ := ((2 * p).factorial : ℝ)
  set W : ℝ := V ^ p
  have hx0 : 0 ≤ x := by linarith
  have k1 : 0 ≤ x * W * (x * A - 1) :=
    mul_nonneg (mul_nonneg hx0 hW) (sub_nonneg.2 (one_le_mul_of_one_le_of_one_le hx hA))
  have k2 : 2 * (A * (x * (x * W))) ≤ 2 ^ p * (A * (x * (x * W))) :=
    mul_le_mul_of_nonneg_right ht (by positivity)
  have k3 : x * periodicState hN β ((F - lev hN β l F m) ^ (2 * p)) ≤ x * (A * (x * W)) :=
    mul_le_mul_of_nonneg_left hmom hx0
  nlinarith [k1, k2, k3]

/-- **The H1 shape from the link martingale**: with the hypotheses of `moment_centred` and the comparison
`32 V ≤ C λ`, `ν((F − c₀)^{2p}) ≤ (2p)! (C λ)^p`. This is the bound `CountMoments.ModeHyperG` asks at one
eigenvector `(v, λ)` with `F = ∑_y v_y F_y`; the comparison is the input it does not supply. DERIVED: `32` from
`moment_centred`. -/
theorem modeMoment_of_azuma (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (c : ℕ → ℝ)
    (m : ℕ) (hc0 : ∀ i < m, 0 ≤ c i) (hc : ∀ i < m, ∀ ω, |incr hN β l F i ω| ≤ c i) {V : ℝ} (hV : 0 < V)
    (hcV : ∑ i ∈ range m, c i ^ 2 ≤ V) (c₀ δ : ℝ) (hδ : ∀ ω, |lev hN β l F m ω - c₀| ≤ δ) (hδV : δ ^ 2 ≤ V)
    {C lam : ℝ} (hcmp : 32 * V ≤ C * lam) (p : ℕ) :
    periodicState hN β ((F - c₀ • (1 : C(IConf (SU N), ℝ))) ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) * (C * lam) ^ p :=
  (moment_centred hN β l F c m hc0 hc hV hcV c₀ δ hδ hδV p).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcmp p) (by positivity))

#print axioms moment_centred
#print axioms modeMoment_of_azuma

end Wilson

end MassGap.ModeAzuma

end
