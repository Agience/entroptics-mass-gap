import Mathlib
import MassGap.ProxyGenObserver
import MassGap.ApproxFromExpand
import MassGap.ContinuumNontrivial

/-!
# MassGap.ApertureThing — what the aperture reads fixes what lies outside it (a lower bound)

The author's step 4: the diffraction limit lets the observer infer what is outside the aperture, so it can tell
whether what it is looking at is a thing or not. `ApertureModes` and `ApertureCount` bound every moment
from above. This module proves the opposite direction: a lower bound on reflected reads at every gap
beyond the aperture, from two reads inside it. Declarations are in the namespace `MassGap.ApertureThing`.

## 1. Log-convex reads (proved)

A sequence of reads `g : ℕ → ℝ`, non-negative, with `g(n+1)² ≤ g(n) g(n+2)` (`LogConvexSeq`):

* `null_propagates`: a null read stays null at every larger gap;
* `pos_of_logConvex`: one positive read at a gap `m₁ ≥ 1` makes every read positive;
* `far_log`, `far_ge_pow_pos`, **`far_ge_pow`**: for `m₁ ≤ m`, `g(m₁)^m ≤ g(m)^{m₁} g(0)^{m−m₁}` (at
  `m₁ = 0` both sides are `g(0)^m`; at a null inner read the left side is `0`);
* `far_ge_rpow_pos`, `far_ge_rpow`: for `1 ≤ m₁ ≤ m`, `g(0) (g(m₁)/g(0))^{m/m₁} ≤ g(m)`, the read at gap
  `m` is at least the geometric extrapolation of the two inner reads, the contact `g(0)` and the inner
  gap `g(m₁)` (`m₁ ≥ 1` is needed: at `m₁ = 0` the exponent is `0`);
* `far_ge_floor`: with floors `v ≤ g(0)` and `ρ g(0) ≤ g(m₁)` and `m/m₁ ≤ X`,
  `v · min(ρ, 1)^X ≤ g(m)`.

No constant enters: the rate is the measured ratio `g(m₁)/g(0)`, the exponent the ratio of gaps.

## 2. Reflection positivity makes the reads log-convex (proved)

`ReflShift B H S`: a symmetric bilinear form `B`, non-negative on a submodule `H` (the half-space
algebra), a linear shift `S` mapping `H` into `H` and symmetric for `B` (`B(Sx, y) = B(x, Sy)`).
`gapRead B S v m = B(Sᵐv, Sᵐv)`.

* `cs_on`: Cauchy–Schwarz on `H` (`B(x,y)² ≤ B(x,x) B(y,y)`, the discriminant of `t ↦ B(x+ty, x+ty)`);
* `shift_pow`: `B(Sᵃx, y) = B(x, Sᵃy)`;
* `gapRead_logConvex`: `gapRead(m+1)² = B(Sᵐv, S^{m+2}v)² ≤ gapRead(m) gapRead(m+2)`;
* **`gapRead_far_ge`**, `gapRead_far_floor`: §1 applied to `gapRead`;
* `gapRead_dichotomy`: either every gap read is positive, or every read at gap `≥ 1` is zero. The one-step
  read decides: a thing is seen at every distance, or at none beyond the aperture.

## 3. The lattice instance (proved)

At the state `stateK k` of every step, `B = rform (stateK k) (ireflObs 0 0)` (the time-reflection form
about the plane `x₀ = 0`), `H` the positive half-space algebra and `S = transObs e₀` (one lattice step
forward in time) form a `ReflShift` (`reflShiftK`): positivity is `stateK_rp`, symmetry
`ApproxFromExpand.rform_symm_k`, the shift symmetry is `ireflObs_transObs` (the reflection turns `e₀` into
`−e₀`) with translation invariance `ContinuumNontrivial.stateK_transObs`. The gap read is
`gapRead = gK k X m = stateK k (θX · T_{2m e₀} X)` (`gapRead_eq_K`): the reflected two-point read of `X`
at time gap `2m` lattice steps beyond its own reflected contact.

* **`stateK_far_ge`**: for `X` in the half-space algebra and `m₁ ≤ m`,
  `gK k X m₁ ^ m ≤ gK k X m ^ m₁ · gK k X 0 ^ (m − m₁)`, at every step `k` and every `SU(N)`;
* `stateK_far_ge_conn`: the same for the connected observable `connObs k X = X − stateK k X · 1`
  (`connObs_mem`: it stays in the half-space algebra, the constant reading no link), so the reads are
  those of the fluctuation of `X`, not of its vacuum constant;
* `stateK_far_floor`, `stateK_far_floor_eventually`: the floor form, and its form along any filter of
  steps (the floors `w`, `ρ` and the gap ratio `R` uniform in the step);
* `stateK_dichotomy`: at every step, every reflected read is positive or every read at gap `≥ 1` vanishes.

## 4. The load-bearing tests (proved)

* `rp_load_bearing`: drop positivity (keep symmetry and the shift symmetry): on `ℝ²` with
  `B(x, y) = x₁y₁ − x₂y₂`, `S = [[2, 1], [−1, 2]]`, `v = (1, 0)` the reads are `1, 3, −7`, and
  `g(1)² ≤ g(2) g(0)` fails (`9 ≤ −7`). Reflection positivity is what lets the inside fix the outside.
* `ultralocal`, `inner_load_bearing`: drop the inner read: on `ℝ` with `B(x, y) = xy` and `S = 0` (an
  ultralocal field) the contact read is `1` and every read at gap `≥ 1` is `0`. So no function `F`
  positive on positive contact reads gives `F(g(0)) ≤ g(m)` at every gap `m ≥ 1` for every `ReflShift`
  of the product form; in particular no floor `w · ρ^R` with `w, ρ > 0` follows from the contact read
  alone. The floor of `far_ge_floor` needs the inner read.
* `geom_sharp`: `S = c · id` on `ℝ` meets every hypothesis with positive reads (`c ≠ 0`) and gives
  equality in `far_ge_pow` at every `m₁ ≤ m`: the bound is attained, so the hypotheses are not vacuous and
  no constant factor can improve it.

## 5. What the three non-triviality inputs get (argued; no declaration)

* `ProxyNondeg`: not discharged. `ProxyCov.proxRead_refl_split` identifies the reading
  `proxRead c (θg) (T_{2m} g)` with `gK k X₊ m − gK k X₋ m`, `X± = ∑ᵢ cᵢ smear(msProx i, g)` over the indices
  of `c` of reflection sign `±1`, from the reflection covariance of the flowed proxies
  (`ProxyCov.msFlow_refl`, the sign of the electric channels included) under the coefficients' parity
  `ProxyCov.CfParity`. For a combination of one sign, `ProxyCov.gapRead_far` carries non-degeneracy at one
  gap to every larger resolved gap with the floor of §3; it does not remove the separated read, and a
  combination of both signs does not propagate (`ProxyCov.mixed_no_propagate`). The bound cannot replace the inner read by the contact read
  alone as `s → 0`: the contact read of a proxy grows like a power of `1/s` and its one-step ratio tends to
  `0`, so `g(0) (g(m₁)/g(0))^{m/m₁}` tends to `0` for `m > m₁` (the spectral weight of a point-like
  composite sits at high energy; Jensen on that measure is loose there).
* `ProxyGenLimGerm`: a density statement (the composites in the closure of the margin monomials), not a
  lower bound; §3 does not touch it.
* `ThreePointAtScale`: an odd read; reflection positivity gives a sign and a lower bound only to
  diagonal reflected reads `B(X, X)`, never to a three-point read. §3 does not touch it.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the contact gap, the signs, the plane `x₀ = 0` and the null read; `1` the unit
gap, the least inner gap, the unit time step `e₀` and the cap of `min(ρ, 1)`; `2` the square of
Cauchy–Schwarz, the two steps of one gap (`B(Sᵐv, Sᵐv)` reads `2m`), the discriminant factor `4 = 2²`, and
the test entries; `3`, `−7`, `9` the values of the indefinite test; `v`/`w`, `ρ`, `X`/`R`, `c` the
floors, the gap ratio and the test's scale, each a read or a hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApertureThing

open Filter

/-! ## 1. Log-convex reads -/

/-- **Log-convexity of a sequence of reads**: `g(n+1)² ≤ g(n) g(n+2)`. DERIVED: `2` the square. -/
def LogConvexSeq (g : ℕ → ℝ) : Prop := ∀ n, g (n + 1) ^ 2 ≤ g n * g (n + 1 + 1)

/-- **A null read stays null at every larger gap.** DERIVED: `0` the null read; `2` the square. -/
theorem null_propagates {g : ℕ → ℝ} (hL : LogConvexSeq g) {j : ℕ}
    (hj : g j = 0) : ∀ i, g (j + i) = 0 := by
  intro i
  induction i with
  | zero => simpa using hj
  | succ i ih =>
    have h := hL (j + i)
    rw [ih, zero_mul] at h
    have hsq : g (j + i + 1) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    exact (pow_eq_zero_iff two_ne_zero).mp hsq

/-- **One positive read at a gap `m₁ ≥ 1` makes every read positive.** DERIVED: `0` the sign; `1` the
least inner gap; `2` the square. -/
theorem pos_of_logConvex {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ : ℕ}
    (hm₁ : 1 ≤ m₁) (hpos : 0 < g m₁) : ∀ n, 0 < g n := by
  have hne : ∀ j, j ≤ m₁ → 0 < g j := by
    intro j hj
    rcases (h0 j).lt_or_eq with h | h
    · exact h
    · exfalso
      have := null_propagates hL h.symm (m₁ - j)
      rw [Nat.add_sub_cancel' hj] at this
      linarith
  have key : ∀ n, 0 < g n ∧ 0 < g (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨hne 0 (Nat.zero_le _), hne 1 hm₁⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := hL n
      have hsq : 0 < g (n + 1) ^ 2 := pow_pos ih.2 2
      have hp : 0 < g n * g (n + 1 + 1) := lt_of_lt_of_le hsq h
      exact pos_of_mul_pos_right hp ih.1.le
  exact fun n => (key n).1

/-- **The far read from the two inner reads, in logarithms**:
`m log g(m₁) ≤ m₁ log g(m) + (m − m₁) log g(0)`. DERIVED: `1` the least inner gap; `2` the square. -/
theorem far_log {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m) (hpos : 0 < g m₁) :
    (m : ℝ) * Real.log (g m₁) ≤ m₁ * Real.log (g m) + ((m : ℝ) - m₁) * Real.log (g 0) := by
  have hp := pos_of_logConvex h0 hL hm₁ hpos
  obtain ⟨D, hDe⟩ : ∃ D : ℕ → ℝ, ∀ n, D n = Real.log (g (n + 1)) - Real.log (g n) :=
    ⟨fun n => Real.log (g (n + 1)) - Real.log (g n), fun _ => rfl⟩
  have hDmono : Monotone D := by
    refine monotone_nat_of_le_succ fun n => ?_
    have h := Real.log_le_log (pow_pos (hp (n + 1)) 2) (hL n)
    rw [Real.log_pow, Real.log_mul (hp n).ne' (hp (n + 1 + 1)).ne'] at h
    push_cast at h
    rw [hDe n, hDe (n + 1)]
    linarith
  have ha : ∀ n : ℕ, Real.log (g n) - Real.log (g 0) ≤ n * D n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : D n ≤ D (n + 1) := hDmono (Nat.le_succ n)
      have h2 := hDe n
      have h3 : (n : ℝ) * D n ≤ n * D (n + 1) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
      push_cast
      linarith
  have hb : ∀ j : ℕ, (j : ℝ) * D m₁ ≤ Real.log (g (m₁ + j)) - Real.log (g m₁) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : D m₁ ≤ D (m₁ + j) := hDmono (Nat.le_add_right m₁ j)
      have h2 := hDe (m₁ + j)
      push_cast
      show (j + 1 : ℝ) * D m₁ ≤ Real.log (g (m₁ + j + 1)) - Real.log (g m₁)
      linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  have p1 := mul_le_mul_of_nonneg_left (ha m₁) (Nat.cast_nonneg j)
  have p2 := mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg m₁)
  push_cast
  linarith

/-- The far read from the two inner reads when the inner read is positive. DERIVED: `1` the least
inner gap; `0` the contact gap. -/
theorem far_ge_pow_pos {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m) (hpos : 0 < g m₁) :
    g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁) := by
  have hp := pos_of_logConvex h0 hL hm₁ hpos
  have hlog := far_log h0 hL hm₁ hm hpos
  rw [← Real.log_le_log_iff (pow_pos (hp m₁) m) (mul_pos (pow_pos (hp m) m₁) (pow_pos (hp 0) _)),
    Real.log_mul (pow_pos (hp m) m₁).ne' (pow_pos (hp 0) _).ne', Real.log_pow, Real.log_pow,
    Real.log_pow, Nat.cast_sub hm]
  linarith

/-- **The far read from the two inner reads**: for `m₁ ≤ m`, `g(m₁)^m ≤ g(m)^{m₁} g(0)^{m−m₁}`. At
`m₁ = 0` both sides are `g(0)^m`; at a null inner read the left side is `0`. DERIVED: `0` the contact gap
and the null read; `1` the least positive gap. -/
theorem far_ge_pow {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm : m₁ ≤ m) : g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁) := by
  rcases Nat.eq_zero_or_pos m₁ with rfl | hm₁
  · simp
  rcases (h0 m₁).lt_or_eq with hpos | hz
  · exact far_ge_pow_pos h0 hL hm₁ hm hpos
  · rw [← hz, zero_pow (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le hm₁ hm))]
    exact mul_nonneg (pow_nonneg (h0 m) _) (pow_nonneg (h0 0) _)

/-- The geometric extrapolation when the inner read is positive. DERIVED: `0` the contact gap; `1`
the least inner gap. -/
theorem far_ge_rpow_pos {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m) (hpos : 0 < g m₁) :
    g 0 * (g m₁ / g 0) ^ ((m : ℝ) / m₁) ≤ g m := by
  have hp := pos_of_logConvex h0 hL hm₁ hpos
  have hlog := far_log h0 hL hm₁ hm hpos
  have hq : 0 < g m₁ / g 0 := div_pos (hp m₁) (hp 0)
  have hm1 : (0 : ℝ) < m₁ := Nat.cast_pos.mpr (lt_of_lt_of_le one_pos hm₁)
  rw [← Real.log_le_log_iff (mul_pos (hp 0) (Real.rpow_pos_of_pos hq _)) (hp m),
    Real.log_mul (hp 0).ne' (Real.rpow_pos_of_pos hq _).ne', Real.log_rpow hq,
    Real.log_div (hp m₁).ne' (hp 0).ne']
  have key : (m : ℝ) / m₁ * (Real.log (g m₁) - Real.log (g 0)) ≤ Real.log (g m) - Real.log (g 0) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
    linarith
  linarith

/-- **The far read is at least the geometric extrapolation of the inner reads**: for `1 ≤ m₁ ≤ m`,
`g(0) (g(m₁)/g(0))^{m/m₁} ≤ g(m)`; at a null inner read the left side is `0`. The gap `m₁ ≥ 1` is
needed: at `m₁ = 0` the exponent `m/0` is `0` and the left side is `g(0)`. DERIVED: `0` the contact gap
and the null read; `1` the least inner gap. -/
theorem far_ge_rpow {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m) : g 0 * (g m₁ / g 0) ^ ((m : ℝ) / m₁) ≤ g m := by
  rcases (h0 m₁).lt_or_eq with hpos | hz
  · exact far_ge_rpow_pos h0 hL hm₁ hm hpos
  · have hm1 : (0 : ℝ) < m₁ := Nat.cast_pos.mpr (lt_of_lt_of_le one_pos hm₁)
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le (lt_of_lt_of_le one_pos hm₁) hm)
    rw [← hz, zero_div, Real.zero_rpow (div_pos hmpos hm1).ne', mul_zero]
    exact h0 m

/-- **The floor form**: with `v ≤ g(0)`, `ρ g(0) ≤ g(m₁)` and `m/m₁ ≤ X`, `v · min(ρ, 1)^X ≤ g(m)`.
DERIVED: `0` the signs and the contact gap; `1` the least inner gap and the cap of `min(ρ, 1)`. -/
theorem far_ge_floor {g : ℕ → ℝ} (h0 : ∀ n, 0 ≤ g n) (hL : LogConvexSeq g) {m₁ m : ℕ}
    (hm₁ : 1 ≤ m₁) (hm : m₁ ≤ m) {v ρ X : ℝ} (hv : 0 < v) (hv0 : v ≤ g 0) (hρ : 0 < ρ)
    (hρr : ρ * g 0 ≤ g m₁) (hX : (m : ℝ) / m₁ ≤ X) : v * min ρ 1 ^ X ≤ g m := by
  have hg0 : 0 < g 0 := lt_of_lt_of_le hv hv0
  have hfar := far_ge_rpow h0 hL hm₁ hm
  have hm1 : (0 : ℝ) < m₁ := Nat.cast_pos.mpr (lt_of_lt_of_le one_pos hm₁)
  have hmin0 : 0 < min ρ 1 := lt_min hρ one_pos
  have hq : ρ ≤ g m₁ / g 0 := (le_div_iff₀ hg0).mpr hρr
  have he : (0 : ℝ) ≤ (m : ℝ) / m₁ := div_nonneg (Nat.cast_nonneg m) hm1.le
  have s1 : min ρ 1 ^ ((m : ℝ) / m₁) ≤ (g m₁ / g 0) ^ ((m : ℝ) / m₁) :=
    Real.rpow_le_rpow hmin0.le ((min_le_left ρ 1).trans hq) he
  have s2 : min ρ 1 ^ X ≤ min ρ 1 ^ ((m : ℝ) / m₁) :=
    Real.rpow_le_rpow_of_exponent_ge hmin0 (min_le_right ρ 1) hX
  calc v * min ρ 1 ^ X ≤ g 0 * (g m₁ / g 0) ^ ((m : ℝ) / m₁) :=
        mul_le_mul hv0 (s2.trans s1) (Real.rpow_pos_of_pos hmin0 X).le hg0.le
    _ ≤ g m := hfar

/-! ## 2. Reflection positivity and a shift -/

section Form

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A reflection form with a shift**: `B` symmetric, non-negative on `H`, `S` maps `H` into `H` and is
`B`-symmetric. DERIVED: `0` the sign. -/
structure ReflShift (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (H : Submodule ℝ V) (S : Module.End ℝ V) : Prop where
  symm : ∀ x y, B x y = B y x
  pos : ∀ x ∈ H, 0 ≤ B x x
  maps : ∀ x ∈ H, S x ∈ H
  shift : ∀ x y, B (S x) y = B x (S y)

/-- **The gap read** `B(Sᵐv, Sᵐv)`. DERIVED: no numeral. -/
def gapRead (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (S : Module.End ℝ V) (v : V) (m : ℕ) : ℝ :=
  B ((S ^ m) v) ((S ^ m) v)

/-- DERIVED: `1` the step. -/
theorem pow_succ_apply (S : Module.End ℝ V) (m : ℕ) (v : V) : (S ^ (m + 1)) v = S ((S ^ m) v) := by
  rw [pow_succ', Module.End.mul_apply]

variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {H : Submodule ℝ V} {S : Module.End ℝ V}

/-- **Cauchy–Schwarz on `H`.** DERIVED: `2` the square and the cross-term factor; `4` the discriminant
factor. -/
theorem cs_on (R : ReflShift B H S) {x y : V} (hx : x ∈ H) (hy : y ∈ H) :
    B x y ^ 2 ≤ B x x * B y y := by
  have hq : ∀ t : ℝ, 0 ≤ B y y * (t * t) + (2 * B x y) * t + B x x := by
    intro t
    have h := R.pos (x + t • y) (H.add_mem hx (H.smul_mem t hy))
    have e : B (x + t • y) (x + t • y) = B y y * (t * t) + (2 * B x y) * t + B x x := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [R.symm y x]
      ring
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have e2 : (2 * B x y) ^ 2 = 4 * B x y ^ 2 := by ring
  rw [e2] at hd
  linarith

/-- The iterates of the shift stay in `H`. DERIVED: no numeral. -/
theorem pow_mem (R : ReflShift B H S) {v : V} (hv : v ∈ H) : ∀ m : ℕ, (S ^ m) v ∈ H
  | 0 => by simpa using hv
  | m + 1 => by rw [pow_succ_apply]; exact R.maps _ (pow_mem R hv m)

/-- **The shift moves across the form**: `B(Sᵃx, y) = B(x, Sᵃy)`. DERIVED: `1` the step. -/
theorem shift_pow (R : ReflShift B H S) (x y : V) : ∀ a : ℕ, B ((S ^ a) x) y = B x ((S ^ a) y)
  | 0 => by simp
  | a + 1 => by
    rw [pow_succ_apply S a x, R.shift, shift_pow R x (S y) a, pow_succ, Module.End.mul_apply]

/-- The gap reads are non-negative. DERIVED: `0` the sign. -/
theorem gapRead_nonneg (R : ReflShift B H S) {v : V} (hv : v ∈ H) (m : ℕ) : 0 ≤ gapRead B S v m :=
  R.pos _ (pow_mem R hv m)

/-- **Reflection positivity makes the gap reads log-convex.** DERIVED: `2` the square. -/
theorem gapRead_logConvex (R : ReflShift B H S) {v : V} (hv : v ∈ H) :
    LogConvexSeq (gapRead B S v) := by
  intro n
  have e : gapRead B S v (n + 1) = B ((S ^ n) v) ((S ^ (n + 1 + 1)) v) := by
    unfold gapRead
    rw [pow_succ_apply S (n + 1) v, pow_succ_apply S n v, R.shift]
  rw [e]
  exact cs_on R (pow_mem R hv n) (pow_mem R hv (n + 1 + 1))

/-- **The outside from the inside**: for `m₁ ≤ m`, `gapRead(m₁)^m ≤ gapRead(m)^{m₁} gapRead(0)^{m−m₁}`.
DERIVED: `0` the contact gap. -/
theorem gapRead_far_ge (R : ReflShift B H S) {v : V} (hv : v ∈ H) {m₁ m : ℕ} (hm : m₁ ≤ m) :
    gapRead B S v m₁ ^ m ≤ gapRead B S v m ^ m₁ * gapRead B S v 0 ^ (m - m₁) :=
  far_ge_pow (gapRead_nonneg R hv) (gapRead_logConvex R hv) hm

/-- **The floor form on the gap reads.** DERIVED: as in `far_ge_floor`. -/
theorem gapRead_far_floor (R : ReflShift B H S) {v : V} (hv : v ∈ H) {m₁ m : ℕ} (hm₁ : 1 ≤ m₁)
    (hm : m₁ ≤ m) {w ρ X : ℝ} (hw : 0 < w) (hw0 : w ≤ gapRead B S v 0) (hρ : 0 < ρ)
    (hρr : ρ * gapRead B S v 0 ≤ gapRead B S v m₁) (hX : (m : ℝ) / m₁ ≤ X) :
    w * min ρ 1 ^ X ≤ gapRead B S v m :=
  far_ge_floor (gapRead_nonneg R hv) (gapRead_logConvex R hv) hm₁ hm hw hw0 hρ hρr hX

/-- **A thing or not**: either every gap read is positive, or every read at gap `≥ 1` vanishes.
DERIVED: `0` the sign and the null read; `1` the unit gap. -/
theorem gapRead_dichotomy (R : ReflShift B H S) {v : V} (hv : v ∈ H) :
    (∀ m, 0 < gapRead B S v m) ∨ (∀ m, 1 ≤ m → gapRead B S v m = 0) := by
  rcases (gapRead_nonneg R hv 1).lt_or_eq with h | h
  · exact Or.inl (pos_of_logConvex (gapRead_nonneg R hv) (gapRead_logConvex R hv) le_rfl h)
  · refine Or.inr fun m hm => ?_
    have := null_propagates (gapRead_logConvex R hv) h.symm (m - 1)
    rwa [Nat.add_sub_cancel' hm] at this

end Form

/-! ## 3. The lattice instance -/

section Lattice

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.JointRP

variable {N : ℕ} [NeZero N]

/-- **One lattice step forward in time**: the unit vector of the axis `0`. DERIVED: `0` the time axis;
`1` the unit step. -/
def eT : ISite := Pi.single 0 1

/-- **The time step on observables**. DERIVED: no numeral. -/
def tStep : Module.End ℝ C(Cfg N, ℝ) := transObs eT

/-- **The time-reflection form of step `k`** about the plane `x₀ = 0`. DERIVED: `0` the plane and the
axis. -/
abbrev bK (k : ℕ) : C(Cfg N, ℝ) →ₗ[ℝ] C(Cfg N, ℝ) →ₗ[ℝ] ℝ :=
  rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)

/-- The reflection about `x₀ = 0` turns the forward step into the backward step. DERIVED: `0` the
plane and the axis. -/
theorem ireflSite_eT : LatticeReflection.ireflSite 0 0 eT = -eT := by
  funext i
  fin_cases i <;> simp [LatticeReflection.ireflSite, eT]

/-- **The time step is symmetric for the reflection form.** DERIVED: `0` the plane. -/
theorem bK_shift (k : ℕ) (x y : C(Cfg N, ℝ)) : bK k (tStep x) y = bK k x (tStep y) := by
  simp only [bK, rform_apply, tStep]
  rw [ireflObs_transObs, ireflSite_eT]
  have e : transObs (-eT) (LatticeReflection.ireflObs 0 0 x) * y
      = transObs (-eT) (LatticeReflection.ireflObs 0 0 x * transObs eT y) := by
    rw [transObs_mul, transObs_transObs, neg_add_cancel, transObs_zero]
  rw [e, MassGap.ContinuumNontrivial.stateK_transObs]

omit [NeZero N] in
/-- **The time step keeps the positive half-space algebra.** DERIVED: `0` the plane and the axis; `1`
the step. -/
theorem tStep_mem {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    tStep X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  obtain ⟨S, hS, hloc⟩ := HalfSpaceAlgebra.mem_halfSpaceAlg.mp hX
  refine transObs_mem_halfSpaceAlg hloc 0 eT (fun l hl => ?_)
  have h1 : (0 : ℤ) ≤ l.2 0 := hS (Finset.mem_coe.mpr hl)
  have h2 : eT 0 = 1 := by simp [eT]
  rw [h2]
  omega

/-- **The lattice reflection form with the time step is a `ReflShift`**, at every step. DERIVED: `0`
the plane. -/
theorem reflShiftK (k : ℕ) :
    ReflShift (bK (N := N) k) (HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) tStep where
  symm x y := MassGap.ApproxFromExpand.rform_symm_k k x y
  pos x hx := stateK_rp (NeZero.ne N) k 0 x hx
  maps _ hx := tStep_mem hx
  shift x y := bK_shift k x y

omit [NeZero N] in
/-- The iterated time step is the translation by `n e₀`. DERIVED: `0` the zero step; `1` the step. -/
theorem tStep_pow (n : ℕ) (X : C(Cfg N, ℝ)) : (tStep (N := N) ^ n) X = transObs (n • eT) X := by
  induction n with
  | zero => simp [transObs_zero]
  | succ n ih =>
    rw [pow_succ_apply, ih]
    show transObs eT (transObs (n • eT) X) = _
    rw [transObs_transObs, succ_nsmul, add_comm]

/-- **The reflected read at gap `2m`**: `stateK k (θX · T_{2m e₀} X)`. DERIVED: `0` the plane; `2` the
two steps of one gap. -/
def gK (k : ℕ) (X : C(Cfg N, ℝ)) (m : ℕ) : ℝ :=
  stateK (NeZero.ne N) k (LatticeReflection.ireflObs 0 0 X * transObs ((2 * m) • eT) X)

/-- **The gap read is the reflected read at gap `2m`.** DERIVED: `2` the two steps. -/
theorem gapRead_eq_K (k : ℕ) (X : C(Cfg N, ℝ)) (m : ℕ) : gapRead (bK k) tStep X m = gK k X m := by
  unfold gapRead
  rw [shift_pow (reflShiftK k) X ((tStep ^ m) X) m]
  have e : (tStep (N := N) ^ m) ((tStep ^ m) X) = (tStep ^ (2 * m)) X := by
    rw [two_mul, pow_add, Module.End.mul_apply]
  rw [e, tStep_pow]
  rfl

/-- **The outside from the inside, at every step**: for `X` in the positive half-space algebra and
`m₁ ≤ m`, `gK k X m₁ ^ m ≤ gK k X m ^ m₁ · gK k X 0 ^ (m − m₁)`. DERIVED: `0` the plane and the contact
gap. -/
theorem stateK_far_ge (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) {m₁ m : ℕ} (hm : m₁ ≤ m) :
    gK k X m₁ ^ m ≤ gK k X m ^ m₁ * gK k X 0 ^ (m - m₁) := by
  have h := gapRead_far_ge (reflShiftK k) hX hm
  simpa only [gapRead_eq_K] using h

omit [NeZero N] in
/-- The constant observable lies in the positive half-space algebra (it reads no link). DERIVED: `0`
the plane; `1` the constant. -/
theorem one_mem_halfSpace :
    (1 : C(Cfg N, ℝ)) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
  HalfSpaceAlgebra.mem_halfSpaceAlg.mpr ⟨∅, by simp, fun _ _ _ => rfl⟩

/-- **The connected observable** `X − stateK k X · 1`: the reading with the vacuum constant removed.
DERIVED: `1` the constant observable. -/
def connObs (k : ℕ) (X : C(Cfg N, ℝ)) : C(Cfg N, ℝ) := X - stateK (NeZero.ne N) k X • (1 : C(Cfg N, ℝ))

/-- The connected observable of a half-space observable is a half-space observable. DERIVED: `0` the
plane. -/
theorem connObs_mem (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    connObs k X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
  Submodule.sub_mem _ hX (Submodule.smul_mem _ _ one_mem_halfSpace)

/-- **The outside from the inside, connected**: the bound of `stateK_far_ge` for the connected
observable, so the reads are those of the fluctuation of `X` and not of its vacuum constant. DERIVED:
`0` the plane and the contact gap. -/
theorem stateK_far_ge_conn (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) {m₁ m : ℕ} (hm : m₁ ≤ m) :
    gK k (connObs k X) m₁ ^ m ≤ gK k (connObs k X) m ^ m₁ * gK k (connObs k X) 0 ^ (m - m₁) :=
  stateK_far_ge k (connObs_mem k hX) hm

/-- **The floor form at every step.** DERIVED: as in `far_ge_floor`. -/
theorem stateK_far_floor (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) {m₁ m : ℕ} (hm₁ : 1 ≤ m₁)
    (hm : m₁ ≤ m) {w ρ R : ℝ} (hw : 0 < w) (hw0 : w ≤ gK k X 0) (hρ : 0 < ρ)
    (hρr : ρ * gK k X 0 ≤ gK k X m₁) (hR : (m : ℝ) / m₁ ≤ R) : w * min ρ 1 ^ R ≤ gK k X m := by
  have h := gapRead_far_floor (reflShiftK k) hX hm₁ hm hw (by rwa [gapRead_eq_K]) hρ
    (by rwa [gapRead_eq_K, gapRead_eq_K]) hR
  rwa [gapRead_eq_K] at h

/-- **The floor form along a filter of steps**: floors `w`, `ρ` and the gap ratio `R` uniform in the step
give the far floor eventually. DERIVED: as in `far_ge_floor`. -/
theorem stateK_far_floor_eventually {l : Filter ℕ} (X : ℕ → C(Cfg N, ℝ)) (m₁ m : ℕ → ℕ) {w ρ R : ℝ}
    (hw : 0 < w) (hρ : 0 < ρ)
    (h : ∀ᶠ k in l, X k ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ 1 ≤ m₁ k ∧ m₁ k ≤ m k ∧ w ≤ gK k (X k) 0 ∧ ρ * gK k (X k) 0 ≤ gK k (X k) (m₁ k)
      ∧ (m k : ℝ) / m₁ k ≤ R) :
    ∀ᶠ k in l, w * min ρ 1 ^ R ≤ gK k (X k) (m k) :=
  h.mono fun k ⟨hX, h1, h2, h3, h4, h5⟩ => stateK_far_floor k hX h1 h2 hw h3 hρ h4 h5

/-- **A thing or not, at every step**: every reflected read of `X` is positive, or every read at gap
`≥ 1` vanishes. DERIVED: `0` the sign and the null read; `1` the unit gap. -/
theorem stateK_dichotomy (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    (∀ m, 0 < gK k X m) ∨ (∀ m, 1 ≤ m → gK k X m = 0) := by
  have h := gapRead_dichotomy (reflShiftK k) hX
  simpa only [gapRead_eq_K] using h

end Lattice

/-! ## 4. The load-bearing tests -/

section Tests

/-- The indefinite form `x₁y₁ − x₂y₂` on `ℝ²`. DERIVED: no numeral. -/
def tB : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 - x.2 * y.2)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

/-- The shift `[[2, 1], [−1, 2]]`, symmetric for `tB`. DERIVED: `2`, `1` the entries. -/
def tS : Module.End ℝ (ℝ × ℝ) where
  toFun x := (2 * x.1 + x.2, -x.1 + 2 * x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 1 <;> ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]
    congr 1 <;> ring

theorem tS_apply (x : ℝ × ℝ) : tS x = (2 * x.1 + x.2, -x.1 + 2 * x.2) := rfl

theorem tB_apply (x y : ℝ × ℝ) : tB x y = x.1 * y.1 - x.2 * y.2 := rfl

/-- **Reflection positivity is load-bearing**: symmetry and the shift symmetry hold, positivity fails,
the reads are `1, 3, −7`, and the far bound `g(1)² ≤ g(2) g(0)` fails. DERIVED: `0`, `1`, `2` the gaps;
`3`, `−7`, `9` the reads and the square. -/
theorem rp_load_bearing :
    (∀ x y, tB x y = tB y x) ∧ (∀ x y, tB (tS x) y = tB x (tS y)) ∧ ¬ (∀ x, 0 ≤ tB x x)
      ∧ gapRead tB tS (1, 0) 0 = 1 ∧ gapRead tB tS (1, 0) 1 = 3 ∧ gapRead tB tS (1, 0) 2 = -7
      ∧ ¬ (gapRead tB tS (1, 0) 1 ^ 2 ≤ gapRead tB tS (1, 0) 2 ^ 1 * gapRead tB tS (1, 0) 0 ^ (2 - 1)) := by
  have g0 : gapRead tB tS (1, 0) 0 = 1 := by
    simp [gapRead, tB_apply]
  have g1 : gapRead tB tS (1, 0) 1 = 3 := by
    norm_num [gapRead, pow_one, tS_apply, tB_apply]
  have g2 : gapRead tB tS (1, 0) 2 = -7 := by
    norm_num [gapRead, sq, Module.End.mul_apply, tS_apply, tB_apply]
  refine ⟨fun x y => ?_, fun x y => ?_, fun h => ?_, g0, g1, g2, ?_⟩
  · simp only [tB_apply]; ring
  · simp only [tB_apply, tS_apply]; ring
  · have := h (0, 1)
    simp only [tB_apply] at this
    norm_num at this
  · rw [g0, g1, g2]
    norm_num

/-- The product form on `ℝ`. DERIVED: no numeral. -/
def mB : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := LinearMap.mul ℝ ℝ

theorem mB_apply (x y : ℝ) : mB x y = x * y := rfl

/-- The ultralocal shift `S = 0`: a `ReflShift` for the product form, contact read `1`, every read at
gap `≥ 1` equal to `0`. DERIVED: `0` the shift and the null reads; `1` the contact read and the unit
gap. -/
theorem ultralocal :
    ReflShift mB ⊤ (0 : Module.End ℝ ℝ) ∧ gapRead mB 0 1 0 = 1
      ∧ ∀ m, 1 ≤ m → gapRead mB 0 1 m = 0 := by
  refine ⟨⟨fun x y => ?_, fun x _ => ?_, fun _ _ => Submodule.mem_top, fun x y => ?_⟩, ?_, ?_⟩
  · simp only [mB_apply]; ring
  · simp only [mB_apply]; exact mul_self_nonneg x
  · simp [mB_apply]
  · simp [gapRead, mB_apply]
  · intro m hm
    simp [gapRead, zero_pow (Nat.one_le_iff_ne_zero.mp hm)]

/-- **The inner read is load-bearing**: no positive floor on a far read follows from the contact read
alone. There is no function `F`, positive on positive contact reads, with `F(g(0)) ≤ g(m)` at every gap
`m ≥ 1` for every `ReflShift` of the product form on `ℝ`; in particular no `w · ρ^R` with `w, ρ > 0`
(`ultralocal` refutes it). DERIVED: `0` the sign; `1` the unit gap and the contact read. -/
theorem inner_load_bearing :
    ¬ ∃ F : ℝ → ℝ, (∀ x, 0 < x → 0 < F x) ∧ ∀ (S : Module.End ℝ ℝ) (v : ℝ) (m : ℕ),
        ReflShift mB ⊤ S → 1 ≤ m → F (gapRead mB S v 0) ≤ gapRead mB S v m := by
  rintro ⟨F, hF, hfl⟩
  obtain ⟨hR, h0, hm⟩ := ultralocal
  have h := hfl 0 1 1 hR le_rfl
  rw [h0, hm 1 le_rfl] at h
  linarith [hF 1 one_pos]

/-- The scaled identity `c · id` on `ℝ`. DERIVED: no numeral. -/
def cS (c : ℝ) : Module.End ℝ ℝ := c • LinearMap.id

theorem cS_pow_one (c : ℝ) (m : ℕ) : (cS c ^ m) 1 = c ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ_apply, ih]
    simp [cS, pow_succ, mul_comm]

/-- **The bound is attained**: `S = c · id` on `ℝ` is a `ReflShift` for the product form, its reads are
positive for `c ≠ 0`, and `far_ge_pow` holds with equality at every `m₁ ≤ m`. DERIVED: `0` the excluded
scale; `1` the reading vector. -/
theorem geom_sharp (c : ℝ) (hc : c ≠ 0) :
    ReflShift mB ⊤ (cS c) ∧ (∀ m, 0 < gapRead mB (cS c) 1 m)
      ∧ ∀ m₁ m : ℕ, m₁ ≤ m → gapRead mB (cS c) 1 m₁ ^ m
          = gapRead mB (cS c) 1 m ^ m₁ * gapRead mB (cS c) 1 0 ^ (m - m₁) := by
  have hg : ∀ m, gapRead mB (cS c) 1 m = c ^ m * c ^ m := fun m => by
    simp only [gapRead, cS_pow_one, mB_apply]
  refine ⟨⟨fun x y => ?_, fun x _ => ?_, fun _ _ => Submodule.mem_top, fun x y => ?_⟩, ?_, ?_⟩
  · simp only [mB_apply]; ring
  · simp only [mB_apply]; exact mul_self_nonneg x
  · simp only [mB_apply, cS, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]; ring
  · intro m
    rw [hg]
    exact mul_self_pos.mpr (pow_ne_zero m hc)
  · intro m₁ m _
    rw [hg, hg, hg, pow_zero, one_mul, one_pow, mul_one, ← pow_add, ← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    ring

end Tests

end MassGap.ApertureThing

end

#print axioms MassGap.ApertureThing.null_propagates
#print axioms MassGap.ApertureThing.pos_of_logConvex
#print axioms MassGap.ApertureThing.far_log
#print axioms MassGap.ApertureThing.far_ge_pow_pos
#print axioms MassGap.ApertureThing.far_ge_pow
#print axioms MassGap.ApertureThing.far_ge_rpow_pos
#print axioms MassGap.ApertureThing.far_ge_rpow
#print axioms MassGap.ApertureThing.far_ge_floor
#print axioms MassGap.ApertureThing.cs_on
#print axioms MassGap.ApertureThing.shift_pow
#print axioms MassGap.ApertureThing.gapRead_logConvex
#print axioms MassGap.ApertureThing.gapRead_far_ge
#print axioms MassGap.ApertureThing.gapRead_far_floor
#print axioms MassGap.ApertureThing.gapRead_dichotomy
#print axioms MassGap.ApertureThing.ireflSite_eT
#print axioms MassGap.ApertureThing.bK_shift
#print axioms MassGap.ApertureThing.tStep_mem
#print axioms MassGap.ApertureThing.reflShiftK
#print axioms MassGap.ApertureThing.tStep_pow
#print axioms MassGap.ApertureThing.gapRead_eq_K
#print axioms MassGap.ApertureThing.stateK_far_ge
#print axioms MassGap.ApertureThing.one_mem_halfSpace
#print axioms MassGap.ApertureThing.connObs_mem
#print axioms MassGap.ApertureThing.stateK_far_ge_conn
#print axioms MassGap.ApertureThing.stateK_far_floor
#print axioms MassGap.ApertureThing.stateK_far_floor_eventually
#print axioms MassGap.ApertureThing.stateK_dichotomy
#print axioms MassGap.ApertureThing.rp_load_bearing
#print axioms MassGap.ApertureThing.ultralocal
#print axioms MassGap.ApertureThing.inner_load_bearing
#print axioms MassGap.ApertureThing.geom_sharp
