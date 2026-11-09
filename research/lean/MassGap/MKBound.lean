import Mathlib
import MassGap.MatchAt

/-!
# MassGap.MKBound — the Migdal–Kadanoff sandwich as a one-sided bound, and its residual

The intermediate stretch (from where `BalabanUV` ends to where `MatchAt` holds) is attacked here by
the route of Tomboulis, *Confinement for all values of the coupling in four-dimensional SU(2) gauge
theory*, arXiv:0707.2179 (2007): bound the true partition function after each blocking `a → ba`
between an upper decimation (Migdal–Kadanoff bond moving, `ζ = b^{d−2}`) and a lower one, interpolate,
and carry the vortex ratio `Z⁺/Z` (`Z⁺ = (Z + Z⁽⁻⁾)/2`, `Z⁽⁻⁾` twisted by the centre on a coclosed
plaquette set) down the flow to strong coupling. The critique is Ito–Seiler, *On the recent paper on
quark confinement by Tomboulis*, arXiv:0711.4930, and *Further discussion of Tomboulis' approach to the
confinement problem*, arXiv:0803.3019; Tomboulis' reply is arXiv:0712.2620; Kanazawa, arXiv:0805.2742,
derives an exact relation between vortex ratios on two lattices whose numerator and denominator
couplings differ. The MK recursion is Migdal (Zh. Eksp. Teor. Fiz. 69 (1975) 810 [Sov. Phys. JETP 42
(1976) 413]) and Kadanoff (Ann. Phys. 100 (1976) 359); the statement that the MK coefficients flow to `0` in `D ≤ 4` for `SU(N)` and `U(N)` is Ito,
Phys. Rev. Lett. 55 (1985) 558 (as cited in 0711.4930).

## 1. The upper bound from bond moving (`bondMove_upper`, `move_balanced`, `bondMove_upper_of_translation`)

`bondMove_upper` (Jensen through `e^x ≥ 1 + x`): for a measure `μ`, an action `A` and a change `D` with
`∫ D e^A dμ = 0`, `∫ e^A ≤ ∫ e^{A+D}`. `moveObs Ap Q⁺ Q⁻ b = Σ_{Q⁺} (b − 1) A_p − Σ_{Q⁻} A_q` is the
change of action when the `b − 1` plaquettes of each fibre of `π : Q⁻ → Q⁺` are moved onto the
receiving plaquette (`ζ = b` per elementary move). `move_balanced`: if the expectations `e` are
constant along the fibres and every fibre has `b − 1` elements, `Σ_{Q⁺} (b−1) e_p − Σ_{Q⁻} e_q = 0`.
`bondMove_upper_of_translation`: with `e_p = ∫ A_p e^A` constant along the move (translation
invariance in the direction of the move, Tomboulis Appendix A, (A.14)–(A.17)), the partition function
before the move is at most the one after. Successive moves compose by transitivity, each with its
own translation hypothesis for the action left by the earlier moves (Tomboulis' Figure 2 argument);
assembling the moves into his III.1, (3.4), the upper bound for a whole decimation step, is not
formalised here.

`pow_integral_ge_one` (Bernoulli): `f ≥ 0`, `∫ f = 1` on a probability space give `∫ f^ζ ≥ 1`; so the
bulk factor `mkUpperF0 = (∫ f^ζ)^{b²}` of the upper decimation is `≥ 1` (`mkUpperF0_ge_one`). The
coefficient maps are defined (`charCoeff`, `mkUpper`: `c^U_j = (∫ f^ζ χ_j/d_j / ∫ f^ζ)^{b²}`, Tomboulis
(2.19)–(2.22) at `r = 1`), with the interpolation `interpCoeff α c = α c` (Ito–Seiler (2.6b)).
`interp_dev`, `abs_interp_dev_le`: the interpolated weight `1 + Σ α c_j d_j χ_j` has
`f̃ − 1 = α (f − 1)`, so `|f̃ − 1| ≤ |f − 1|` for `α ∈ [0, 1]`: every interpolated coefficient set is
no farther from the strong-coupling point than the upper one, in the sup norm the count route of
`MatchAt` uses. The exactness of the 2-dimensional integration (`ĉ_j ↦ ĉ_j^{b²}`, character
orthogonality), the lower bound `Z(c^L) ≤ Z` and the monotonicity of `Z` in `c` (reflection
positivity, Tomboulis II.1, III.2, IV.2) are not proved here; they enter below only as the
inequalities `lo ≤ Z ≤ hi` of `ratio_window` and as the equalities of `SandwichMatch`.

## 2. Interpolation (`exists_interp`, `interp_unique`, `sandwichMatch_of_crossing`)

`exists_interp`: a function continuous on `[0, 1]` with `Φ 0 ≤ z ≤ Φ 1` takes the value `z` (Tomboulis
(3.22)–(3.24): the interpolating partition function hits the true one). `interp_unique`: strictly
monotone gives one such `α` (his III.3). Each of `Z` and `Z⁺` thus has its own parameter, `α(t)` and
`α⁺(t)`, for each value `t` of the parametrisation of the bulk factor. `sandwichMatch_of_crossing`: if
`α − α⁺` is continuous on `[t_a, t_b]`, `≤ 0` at `t_a` and `≥ 0` at `t_b`, some `t*` gives one
`(α, t)` that reproduces both `Z` and `Z⁺` — Ito–Seiler (3.2), the existence of `t*` with
`α(t*) = α⁺(t*)`. Its conclusion is the content of `SandwichMatch` in the `(α, t)` parametrisation
(bulk factor a function of `(α, t)`, no `bulk ≠ 0` clause), not the predicate itself; the sign
conditions at `t_a, t_b` are what Ito–Seiler's inequality (3.5) would supply.

## 3. The residual: `SandwichMatch`

`SandwichMatch Zf Zfp bulk next c θ`: `bulk c θ ≠ 0`, `Zf c = bulk c θ · Zf (next c θ)` and
`Zfp c = bulk c θ · Zfp (next c θ)`. One parameter `θ` — one bulk factor and one set of coarse
coefficients `next c θ` — reproduces both the untwisted and the flux partition function after one
blocking. This is the step the critique says is not established: Ito–Seiler 0711.4930 §3, eqs.
(3.2)–(3.5) (the existence of `t*` reduced to `A(α) > A⁺(α)`, proved only where the strong-coupling
expansion converges) and 0803.3019 §3.2, Problems 1–3 (the bulk-matching `t_m` of Tomboulis (5.9), the
final `α(n) = α⁺(n)`, and the continuation of the implicit-function branch). Matching only the bulk
factors at the intermediate steps, as Tomboulis does, leaves the numerator and the denominator on two
different coefficient flows; `SandwichMatch` at every step is what removes that.

`ratio_eq_of_match`: `SandwichMatch` gives `Zfp c / Zf c = Zfp (next c θ) / Zf (next c θ)` (the bulk
factor cancels). `ratio_orbit_of_match`: along `mkOrbit next θs c` with `SandwichMatch` at each of `n`
steps the ratio at the start equals the ratio after `n` steps. `exists_matched_orbit`: `SandwichMatch`
at every coefficient set gives a matched orbit of every length. `log_ratio_orbit`: the quantitative
form — per-step log-ratio errors `ε m` add up, `|log R c − log R (orbit n)| ≤ Σ_{m<n} ε m`.

## 4. The strong-coupling end (`vortex_bound`, `StrongEnd`, `log_ratio_end`)

`vortex_bound`, in the polymer systems of `MatchAt`: `w` satisfies `MatchAt w a κ`, `w'` has
`|w'| = |w|` and `w' = w` off a set `B` of polymers each of size `≥ A` and meeting a site set `W`
(the twisted gas changes the sign of the polymers winding through the vortex sheet only). Then
`|log Z(w) − log Z(w')| ≤ 2 |W| a e^{−κA}`. Proof: `Z(w)` and `Z(w')` agree on the polymers off `B`
(`Z_congr`), removing `B` costs at most `Σ_B c` either way (`abs_log_sdiff_le`, from Dobrushin), and
`Σ_B c ≤ |W| a e^{−κA}` because every polymer of `B` meets `W` and carries the decay weight
`|X| e^{κ|X|} ≥ e^{κA}` of `MatchAt`. With `A` the cross-section area and `W` a cross-section of
sites, this is the area-law form of the vortex free energy of the polymer gas.

`StrongEnd Zf Zfp a κ A W c`: the coarse pair at `c` is such a polymer pair, `Zf c = Z(w)` and
`Zfp c = (Z(w) + Z(w'))/2`. It is the input "the flow has reached the strong-coupling region": the
polymer representation of the coarse plaquette gas, with `MatchAt`, is assumed, not derived from
the character expansion. A real `w'` with `|w'| = |w|` and `Z⁺ = (Z + Z⁽⁻⁾)/2` is the `ℤ₂` centre
twist (SU(2), or U(1) at angle `π`); the `ℤ₃` twist of SU(3) has complex activities and is not this
pair. `log_ratio_end`: `StrongEnd` gives `|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA}`.

## 5. The chain (`vortex_of_sandwich`, `vortex_of_sandwichMatch`, `thooft_of_sandwichMatch`)

* `vortex_of_sandwich`: log-ratio errors `ε m` along the orbit and `StrongEnd` after `n` steps give
  `|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA} + Σ_{m<n} ε m` at the start.
* `vortex_of_sandwichMatch`: `SandwichMatch` at each of the `n` steps and `StrongEnd` after them give
  `|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA}`.
* `thooft_of_sandwichMatch`: the same in the twisted form,
  `|Z⁽⁻⁾/Z − 1| ≤ 2 (e^{2|W| a e^{−κA}} − 1)` with `Z⁽⁻⁾ = 2 Zfp − Zf`.

## 6. Against the critique: the window and U(1)

* `ratio_window`: without `SandwichMatch`, `lo ≤ Z ≤ hi` and `lo⁺ ≤ Z⁺ ≤ hi⁺` place the ratio in
  `[lo⁺/hi, hi⁺/lo]`. `window_extensive`: when `hi = F^N Z_c(c^U)`, `lo = Z_c(c^L)` with `F ≥ 1` and
  `Z_c(c^L) ≤ Z_c(c^U)`, `log hi − log lo ≥ N log F`: the window is extensive (`N` the number of coarse
  plaquettes), while the quantity it must resolve, `log (Z⁺/Z)`, is bounded by `2 |W| a e^{−κA}` at the
  strong end. The bounds alone do not determine the ratio; `SandwichMatch` (or `ε`-errors summing below
  the vortex scale) carries the whole content.
* `not_sandwichMatch_of_vortex`: if every orbit of length `n` reaches `StrongEnd` and the true
  `|log (Z⁺/Z)|` exceeds `2 |W| a e^{−κA}`, there is no orbit along which `SandwichMatch` holds at all
  `n` steps. For `U(1)` the vortex free energy has no area-law decay at weak coupling:
  `(1/L₃L₄) F ~ const/(L₁L₂)` (the Coulomb phase; Ito–Seiler 0803.3019 Theorem 2.2(2)), while the MK
  coefficients flow to `0` (Ito 1985): wherever the `U(1)` flow does reach `StrongEnd`,
  `SandwichMatch` fails at some step. Ito–Seiler say this directly: no `t*` exists for `U(1)`
  (0711.4930 §4; 0803.3019 §4, for large `β` and `r = 1`).
  Any proof of `SandwichMatch` must use a property `U(1)` lacks; reflection positivity, positivity of
  the coefficients and the bounds of §1 hold for `U(1)` as well.

## Strength

Proved: the bond-moving upper bound in the Jensen form, its fibre cancellation, the bulk factor
`≥ 1`, the interpolation's existence and uniqueness, the crossing criterion, the bulk-factor
cancellation under `SandwichMatch`, the telescoping along the orbit, the vortex bound of a polymer
pair under `MatchAt`, and the chain from `SandwichMatch` plus `StrongEnd` to the decay of the vortex
ratio; the window inequality and the contrapositive. Not proved: `SandwichMatch` at any step (the
residual), `StrongEnd` for the MK coarse theory (the polymer representation of the plaquette gas and
its `MatchAt`), and the reflection-positivity inequalities of Tomboulis II.1/III.2/IV.2. Relation to
(B): `StrongEnd` uses the same `MatchAt` as `MatchAt.lean`, but what `SandwichMatch` transfers from the
coarse theory to the original lattice is the single number `Z⁺/Z` per volume; it does not transfer
correlations, so it gives no `MatchAt.PolymerCross` for the Wilson slab, and the fields (A), (B) of
`OneBridgeData` are untouched by this module. Nothing here proves confinement or a mass gap.

`SandwichMatch Zf Zfp bulk next c θ` is stated over arbitrary `Zf`, `Zfp`, `bulk`, `next`: with
`next c θ = c` and `bulk = 1` it holds trivially, and the chain reduces to `StrongEnd` at `c`. Its
content as the disputed Ito–Seiler step exists only once `next`, `bulk` are the MK interpolated
blocking with its bulk factor (`mkUpper`, `mkUpperF0`, `interpCoeff`) and `Zf` the lattice partition
function; that instantiation is not built here, `C` carries the lattice size implicitly, the
`StrongEnd` constants (`a`, `κ`, `A`, `W`) are not tied to the flow, and the reflection-positivity
inequalities enter only `ratio_window`. For a `ℤ₂` twist the polymers that change sign wind through
the sheet, so `W` is of the size of the transverse volume. Distances to strong coupling here are in
the sup norm `u = sup |f − 1|`.

## Numerics (`research/code/mk_bound_checks.py`, under 10 s, no Monte Carlo)

Upper flow `ζ = 4, b = 2, r = 1`, KP test `match_checks.direct_kp_ok` on `u = sup |f − 1|`. SU(2)
from `β_std = 1, 2, 4, 6` enters the KP region after `4, 8, 15, 23` steps, SU(3) from
`β_std = 1, 2, 4, 6` after `2, 3, 7, 10`; both stay. U(1) from `β = 1, 2, 4` does not enter in 40
steps (`u` decreases by `7·10⁻⁵`, `3·10⁻¹¹`, `0` per step). The lower flow `t ↦ t⁶` enters after
`1–3` steps for every group. Each of 24 sampled interpolated flows per group (`α_m ∈ [0,1]`, seeded
random) stays below the upper flow at every step. So the coefficient window between upper and lower
flows meets the KP condition on `u` for SU(2) and SU(3) within the steps above (and does not for U(1)
at `β ≥ 1`); this is a necessary input of `StrongEnd`, not `StrongEnd`, and the Lean pair models the
`ℤ₂` twist (SU(2)), not the `ℤ₃` twist of SU(3). The partition-function window does not shrink to
what it must resolve: with the lower bound `c^L = 0` (Tomboulis (3.9)), at the KP entry step `log F0U`
per plaquette is `8·10⁻²⁰ … 1.7·10⁻⁴`, giving a log-width `N_p log F0U` on a coarse `8⁴` box of
`e^{−34} … e^{1.4}` (up to `e^{7}` at `L = 32`) against a vortex scale `L² t_F^{L²}` of `e^{−419}` or
below at `L = 8`, the gap growing with `L`.

DERIVED (module-wide): `0`, `1` the units of the sums, products and the interpolation interval; `2`
the two removals (`w` and `w'`) in `vortex_bound` and the halving in `Z⁺ = (Z + Z⁽⁻⁾)/2`; `−2` the
range of Bernoulli's inequality.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MKBound

open MeasureTheory Finset MassGap.MatchAt

/-! ## 1. The upper bound from bond moving -/

section BondMoving

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bond moving gives an upper bound** (Jensen through `e^x ≥ 1 + x`): if the change of action `D`
has `∫ D e^A = 0`, then `∫ e^A ≤ ∫ e^{A+D}`. -/
theorem bondMove_upper (μ : Measure Ω) (A D : Ω → ℝ)
    (hA : Integrable (fun ω => Real.exp (A ω)) μ)
    (hAD : Integrable (fun ω => Real.exp (A ω + D ω)) μ)
    (hDA : Integrable (fun ω => D ω * Real.exp (A ω)) μ)
    (h0 : ∫ ω, D ω * Real.exp (A ω) ∂μ = 0) :
    ∫ ω, Real.exp (A ω) ∂μ ≤ ∫ ω, Real.exp (A ω + D ω) ∂μ := by
  have key : ∀ ω, Real.exp (A ω) + D ω * Real.exp (A ω) ≤ Real.exp (A ω + D ω) := by
    intro ω
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (D ω), Real.exp_pos (A ω)]
  have hsum : Integrable (fun ω => Real.exp (A ω) + D ω * Real.exp (A ω)) μ := hA.add hDA
  calc ∫ ω, Real.exp (A ω) ∂μ = ∫ ω, Real.exp (A ω) ∂μ + ∫ ω, D ω * Real.exp (A ω) ∂μ := by
        rw [h0, add_zero]
    _ = ∫ ω, (Real.exp (A ω) + D ω * Real.exp (A ω)) ∂μ := (integral_add hA hDA).symm
    _ ≤ ∫ ω, Real.exp (A ω + D ω) ∂μ := integral_mono hsum hAD key

variable {P : Type*}

/-- **The change of action of a move**: the `b − 1` moved plaquettes `Q⁻` removed, each receiving
plaquette of `Q⁺` multiplied by `ζ = b`. -/
def moveObs (Ap : P → Ω → ℝ) (Qp Qm : Finset P) (b : ℕ) (ω : Ω) : ℝ :=
  ∑ p ∈ Qp, ((b : ℝ) - 1) * Ap p ω - ∑ q ∈ Qm, Ap q ω

/-- **The move is balanced**: expectations constant along the fibres of `π : Q⁻ → Q⁺`, fibres of size
`b − 1`, give `Σ_{Q⁺} (b − 1) e_p − Σ_{Q⁻} e_q = 0`. -/
theorem move_balanced [DecidableEq P] (Qp Qm : Finset P) (π : P → P) (e : P → ℝ) {b : ℕ}
    (hb : 1 ≤ b) (hπ : ∀ q ∈ Qm, π q ∈ Qp)
    (hfib : ∀ p ∈ Qp, (Qm.filter fun q => π q = p).card = b - 1)
    (he : ∀ q ∈ Qm, e q = e (π q)) :
    ∑ p ∈ Qp, ((b : ℝ) - 1) * e p - ∑ q ∈ Qm, e q = 0 := by
  have h1 : ∑ q ∈ Qm, e q = ∑ p ∈ Qp, ∑ q ∈ Qm.filter (fun q => π q = p), e q :=
    (sum_fiberwise_of_maps_to hπ e).symm
  have h2 : ∀ p ∈ Qp, ∑ q ∈ Qm.filter (fun q => π q = p), e q = ((b : ℝ) - 1) * e p := by
    intro p hp
    calc ∑ q ∈ Qm.filter (fun q => π q = p), e q
        = ∑ _q ∈ Qm.filter (fun q => π q = p), e p := by
          refine sum_congr rfl fun q hq => ?_
          obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
          rw [he q hq1, hq2]
      _ = ((b : ℝ) - 1) * e p := by
          rw [sum_const, nsmul_eq_mul, hfib p hp, Nat.cast_sub hb, Nat.cast_one]
  rw [h1, sum_congr rfl h2, sub_self]

/-- **The bond-moving upper bound under translation invariance** (Tomboulis Appendix A): if the
weighted expectations `∫ A_p e^A` are constant along the move, the partition function before the
move is at most the one after. -/
theorem bondMove_upper_of_translation [DecidableEq P] (μ : Measure Ω) (A : Ω → ℝ)
    (Ap : P → Ω → ℝ) (Qp Qm : Finset P) (π : P → P) {b : ℕ} (hb : 1 ≤ b)
    (hπ : ∀ q ∈ Qm, π q ∈ Qp) (hfib : ∀ p ∈ Qp, (Qm.filter fun q => π q = p).card = b - 1)
    (hA : Integrable (fun ω => Real.exp (A ω)) μ)
    (hAp : ∀ p, Integrable (fun ω => Ap p ω * Real.exp (A ω)) μ)
    (hAD : Integrable (fun ω => Real.exp (A ω + moveObs Ap Qp Qm b ω)) μ)
    (htr : ∀ q ∈ Qm, ∫ ω, Ap q ω * Real.exp (A ω) ∂μ = ∫ ω, Ap (π q) ω * Real.exp (A ω) ∂μ) :
    ∫ ω, Real.exp (A ω) ∂μ ≤ ∫ ω, Real.exp (A ω + moveObs Ap Qp Qm b ω) ∂μ := by
  have hfun : (fun ω => moveObs Ap Qp Qm b ω * Real.exp (A ω)) = fun ω =>
      ∑ p ∈ Qp, ((b : ℝ) - 1) * (Ap p ω * Real.exp (A ω)) - ∑ q ∈ Qm, Ap q ω * Real.exp (A ω) := by
    funext ω
    unfold moveObs
    rw [sub_mul, sum_mul, sum_mul]
    congr 1
    exact sum_congr rfl fun p _ => by ring
  have hI1 : Integrable (fun ω => ∑ p ∈ Qp, ((b : ℝ) - 1) * (Ap p ω * Real.exp (A ω))) μ :=
    integrable_finsetSum _ fun p _ => (hAp p).const_mul ((b : ℝ) - 1)
  have hI2 : Integrable (fun ω => ∑ q ∈ Qm, Ap q ω * Real.exp (A ω)) μ :=
    integrable_finsetSum _ fun q _ => hAp q
  have hDA : Integrable (fun ω => moveObs Ap Qp Qm b ω * Real.exp (A ω)) μ := by
    rw [hfun]; exact hI1.sub hI2
  refine bondMove_upper μ A (moveObs Ap Qp Qm b) hA hAD hDA ?_
  rw [hfun, integral_sub hI1 hI2,
    integral_finsetSum _ fun p _ => (hAp p).const_mul ((b : ℝ) - 1),
    integral_finsetSum _ fun q _ => hAp q]
  simp only [integral_const_mul]
  exact move_balanced Qp Qm π (fun p => ∫ ω, Ap p ω * Real.exp (A ω) ∂μ) hb hπ hfib htr

end BondMoving

section Coefficients

variable {G J : Type*} [MeasurableSpace G]

/-- **The bulk factor is at least one** (Bernoulli): `f ≥ 0`, `∫ f = 1` on a probability space give
`∫ f^ζ ≥ 1`. -/
theorem pow_integral_ge_one {μ : Measure G} [IsProbabilityMeasure μ] {f : G → ℝ}
    (hf0 : ∀ U, 0 ≤ f U) (hf : Integrable f μ) (ζ : ℕ) (hfz : Integrable (fun U => f U ^ ζ) μ)
    (h1 : ∫ U, f U ∂μ = 1) : 1 ≤ ∫ U, f U ^ ζ ∂μ := by
  have hpt : ∀ U, 1 + (ζ : ℝ) * (f U - 1) ≤ f U ^ ζ := fun U => by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ f U - 1 by linarith [hf0 U]) ζ
    simpa using this
  have hi : Integrable (fun U => (ζ : ℝ) * (f U - 1)) μ := (hf.sub (integrable_const 1)).const_mul _
  have hi1 : Integrable (fun U => 1 + (ζ : ℝ) * (f U - 1)) μ := (integrable_const 1).add hi
  have hlin : ∫ U, (1 + (ζ : ℝ) * (f U - 1)) ∂μ = 1 := by
    rw [integral_add (integrable_const 1) hi, integral_const_mul,
      integral_sub hf (integrable_const 1), h1]
    simp
  calc (1 : ℝ) = ∫ U, (1 + (ζ : ℝ) * (f U - 1)) ∂μ := hlin.symm
    _ ≤ ∫ U, f U ^ ζ ∂μ := integral_mono hi1 hfz hpt

/-- The character coefficient `∫ F χ_j / d_j`. -/
def charCoeff (μ : Measure G) (χ : J → G → ℝ) (d : J → ℝ) (F : G → ℝ) (j : J) : ℝ :=
  (∫ U, F U * χ j U ∂μ) / d j

/-- **The upper-decimation coefficients** (`r = 1`): `c^U_j = (∫ f^ζ χ_j / d_j / ∫ f^ζ)^{b²}`. -/
def mkUpper (μ : Measure G) (χ : J → G → ℝ) (d : J → ℝ) (ζ b2 : ℕ) (f : G → ℝ) (j : J) : ℝ :=
  (charCoeff μ χ d (fun U => f U ^ ζ) j / ∫ U, f U ^ ζ ∂μ) ^ b2

/-- **The upper-decimation bulk factor** per coarse plaquette: `(∫ f^ζ)^{b²}`. -/
def mkUpperF0 (μ : Measure G) (ζ b2 : ℕ) (f : G → ℝ) : ℝ := (∫ U, f U ^ ζ ∂μ) ^ b2

/-- The bulk factor of the upper decimation is at least one. -/
theorem mkUpperF0_ge_one {μ : Measure G} [IsProbabilityMeasure μ] {f : G → ℝ}
    (hf0 : ∀ U, 0 ≤ f U) (hf : Integrable f μ) (ζ b2 : ℕ)
    (hfz : Integrable (fun U => f U ^ ζ) μ) (h1 : ∫ U, f U ∂μ = 1) : 1 ≤ mkUpperF0 μ ζ b2 f :=
  one_le_pow₀ (pow_integral_ge_one hf0 hf ζ hfz h1)

end Coefficients

section Interp

variable {G J : Type*}

/-- The interpolated coefficients `α c` (Ito–Seiler (2.6b)). -/
def interpCoeff (α : ℝ) (c : J → ℝ) : J → ℝ := fun j => α * c j

/-- The plaquette weight `1 + Σ_{j∈s} c_j d_j χ_j`. -/
def plaqWeight (s : Finset J) (c d : J → ℝ) (χ : J → G → ℝ) (U : G) : ℝ :=
  1 + ∑ j ∈ s, c j * d j * χ j U

/-- **The interpolated weight**: `f̃ − 1 = α (f − 1)`. -/
theorem interp_dev (s : Finset J) (α : ℝ) (c d : J → ℝ) (χ : J → G → ℝ) (U : G) :
    plaqWeight s (interpCoeff α c) d χ U - 1 = α * (plaqWeight s c d χ U - 1) := by
  have h : ∑ j ∈ s, α * c j * d j * χ j U = α * ∑ j ∈ s, c j * d j * χ j U := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp only [plaqWeight, interpCoeff]
  rw [h]
  ring

/-- **Interpolation does not leave the sup-norm ball**: `|f̃ − 1| ≤ |f − 1|` for `α ∈ [0, 1]`. -/
theorem abs_interp_dev_le (s : Finset J) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (c d : J → ℝ)
    (χ : J → G → ℝ) (U : G) :
    |plaqWeight s (interpCoeff α c) d χ U - 1| ≤ |plaqWeight s c d χ U - 1| := by
  rw [interp_dev, abs_mul, abs_of_nonneg hα0]
  exact mul_le_of_le_one_left (abs_nonneg _) hα1

end Interp

/-! ## 2. Interpolation -/

/-- **The interpolation hits the partition function**: continuous on `[0, 1]` with
`Φ 0 ≤ z ≤ Φ 1` gives `α ∈ [0, 1]` with `Φ α = z`. -/
theorem exists_interp {Φ : ℝ → ℝ} (hc : ContinuousOn Φ (Set.Icc 0 1)) {z : ℝ} (h0 : Φ 0 ≤ z)
    (h1 : z ≤ Φ 1) : ∃ α ∈ Set.Icc (0 : ℝ) 1, Φ α = z :=
  intermediate_value_Icc zero_le_one hc ⟨h0, h1⟩

/-- **The interpolation parameter is unique** for a strictly monotone interpolation. -/
theorem interp_unique {Φ : ℝ → ℝ} (hm : StrictMonoOn Φ (Set.Icc 0 1)) {α β : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (h : Φ α = Φ β) : α = β :=
  hm.injOn hα hβ h

/-- **The crossing criterion** (Ito–Seiler (3.2)): if `α − α⁺` is continuous on `[t_a, t_b]`, `≤ 0`
at `t_a` and `≥ 0` at `t_b`, one `(α, t)` reproduces both `Z` and `Z⁺`. -/
theorem sandwichMatch_of_crossing {α αp : ℝ → ℝ} {ta tb : ℝ} (hab : ta ≤ tb)
    (hcont : ContinuousOn (fun t => α t - αp t) (Set.Icc ta tb))
    (hlo : α ta - αp ta ≤ 0) (hhi : 0 ≤ α tb - αp tb)
    {Z Zp : ℝ} {bulk : ℝ → ℝ → ℝ} {Zc Zcp : ℝ → ℝ}
    (hZ : ∀ t ∈ Set.Icc ta tb, Z = bulk (α t) t * Zc (α t))
    (hZp : ∀ t ∈ Set.Icc ta tb, Zp = bulk (αp t) t * Zcp (αp t)) :
    ∃ t ∈ Set.Icc ta tb, Z = bulk (α t) t * Zc (α t) ∧ Zp = bulk (α t) t * Zcp (α t) := by
  obtain ⟨t, ht, h0⟩ := intermediate_value_Icc hab hcont ⟨hlo, hhi⟩
  have h0' : α t - αp t = 0 := h0
  have he : αp t = α t := by linarith
  refine ⟨t, ht, hZ t ht, ?_⟩
  rw [← he]
  exact hZp t ht

/-! ## 3. The residual `SandwichMatch` and the orbit -/

section Chain

variable {C Θ : Type*}

/-- The orbit of a coefficient set under the interpolated decimations with parameters `θs`. -/
def mkOrbit (next : C → Θ → C) (θs : ℕ → Θ) (c : C) : ℕ → C
  | 0 => c
  | m + 1 => next (mkOrbit next θs c m) (θs m)

/-- The flux ratio `Z⁺ / Z`. -/
def fluxRatio (Zf Zfp : C → ℝ) (c : C) : ℝ := Zfp c / Zf c

/-- **`SandwichMatch`** — the residual: one parameter `θ` (one bulk factor, one coarse coefficient
set) reproduces both the untwisted and the flux partition function after one blocking. -/
def SandwichMatch (Zf Zfp : C → ℝ) (bulk : C → Θ → ℝ) (next : C → Θ → C) (c : C) (θ : Θ) :
    Prop :=
  bulk c θ ≠ 0 ∧ Zf c = bulk c θ * Zf (next c θ) ∧ Zfp c = bulk c θ * Zfp (next c θ)

variable {Zf Zfp : C → ℝ} {bulk : C → Θ → ℝ} {next : C → Θ → C}

/-- **The bulk factor cancels** under `SandwichMatch`. -/
theorem ratio_eq_of_match {c : C} {θ : Θ} (h : SandwichMatch Zf Zfp bulk next c θ) :
    fluxRatio Zf Zfp c = fluxRatio Zf Zfp (next c θ) := by
  unfold fluxRatio
  rw [h.2.1, h.2.2, mul_div_mul_left _ _ h.1]

/-- **The ratio is carried down a matched orbit.** -/
theorem ratio_orbit_of_match {c : C} {θs : ℕ → Θ} {n : ℕ}
    (h : ∀ m < n, SandwichMatch Zf Zfp bulk next (mkOrbit next θs c m) (θs m)) :
    fluxRatio Zf Zfp c = fluxRatio Zf Zfp (mkOrbit next θs c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ih fun m hm => h m (Nat.lt_succ_of_lt hm)]
    exact ratio_eq_of_match (h n (Nat.lt_succ_self n))

/-- **A pointwise `SandwichMatch` gives matched orbits.** -/
theorem exists_matched_orbit (h : ∀ c, ∃ θ, SandwichMatch Zf Zfp bulk next c θ) (c : C) :
    ∃ θs : ℕ → Θ, ∀ m, SandwichMatch Zf Zfp bulk next (mkOrbit next θs c m) (θs m) := by
  choose pol hpol using h
  let o : ℕ → C := fun m => Nat.rec (motive := fun _ => C) c (fun _ x => next x (pol x)) m
  refine ⟨fun m => pol (o m), fun m => ?_⟩
  have ho : ∀ m, mkOrbit next (fun m => pol (o m)) c m = o m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      show next (mkOrbit next (fun m => pol (o m)) c m) (pol (o m)) = o (m + 1)
      rw [ih]
  rw [ho]
  exact hpol (o m)

/-- **Errors add along the orbit**: per-step log-ratio errors `ε m` give
`|log R c − log R (orbit n)| ≤ Σ_{m<n} ε m`. -/
theorem log_ratio_orbit {R : C → ℝ} {c : C} {θs : ℕ → Θ} {ε : ℕ → ℝ} (n : ℕ)
    (h : ∀ m < n, |Real.log (R (mkOrbit next θs c m)) - Real.log (R (mkOrbit next θs c (m + 1)))|
      ≤ ε m) :
    |Real.log (R c) - Real.log (R (mkOrbit next θs c n))| ≤ ∑ m ∈ range n, ε m := by
  induction n with
  | zero =>
    show |Real.log (R c) - Real.log (R c)| ≤ ∑ m ∈ range 0, ε m
    simp
  | succ n ih =>
    have h1 := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    have h2 := h n (Nat.lt_succ_self n)
    rw [sum_range_succ]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Chain

/-! ## 4. The strong-coupling end -/

section PolymerExtra

variable {Pol : Type*} [Fintype Pol] [DecidableEq Pol] {inc : Pol → Pol → Prop} [DecidableRel inc]

/-- The partition function of `S` depends only on the activities in `S`. -/
theorem Z_congr {w w' : Pol → ℝ} {S : Finset Pol} (h : ∀ γ ∈ S, w γ = w' γ) :
    Z inc w S = Z inc w' S := by
  unfold Z
  refine sum_congr rfl fun T hT => prod_congr rfl fun γ hγ => h γ ?_
  exact (mem_powerset.1 (mem_filter.1 hT).1) hγ

variable {w : Pol → ℝ}

/-- **Adding a set back costs at most its weights**: `Z S ≤ e^{Σ_B c} Z (S∖B)`. -/
theorem Z_le_exp_sdiff (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S B : Finset Pol) :
    Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B) := by
  refine Finset.induction_on B (by simp) ?_
  intro b B hb ih
  rw [sdiff_insert, sum_insert hb, Real.exp_add]
  by_cases hbm : b ∈ S \ B
  · have h2 := ((dob_bounds hs hD (S \ B)).2 b hbm).2
    calc Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B) := ih
      _ ≤ Real.exp (∑ δ ∈ B, c δ) * (Real.exp (c b) * Z inc w ((S \ B).erase b)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (c b) * Real.exp (∑ δ ∈ B, c δ) * Z inc w ((S \ B).erase b) := by ring
  · rw [erase_eq_of_notMem hbm]
    have hp := Z_pos hs hD (S \ B)
    have he := Real.one_le_exp (hD b).1
    have h0 : 0 ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B) :=
      mul_nonneg (Real.exp_pos _).le hp.le
    calc Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B) := ih
      _ ≤ Real.exp (c b) * (Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B)) :=
          le_mul_of_one_le_left h0 he
      _ = Real.exp (c b) * Real.exp (∑ δ ∈ B, c δ) * Z inc w (S \ B) := by ring

/-- **Removing a set moves `log Z` by at most its weights.** -/
theorem abs_log_sdiff_le (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S B : Finset Pol) :
    |Real.log (Z inc w S) - Real.log (Z inc w (S \ B))| ≤ ∑ δ ∈ B, c δ := by
  have hc : ∀ γ, 0 ≤ c γ := fun γ => (hD γ).1
  have h1 : Z inc w (S \ B) ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w S :=
    Z_sdiff_le (s := S) hc (fun T _ => Z_pos hs hD T) (fun T _ δ hδ => erase_le hs hD T δ hδ) B
  have h2 := Z_le_exp_sdiff hs hD S B
  have hp := Z_pos hs hD S
  have hq := Z_pos hs hD (S \ B)
  have l1 := Real.log_le_log hq h1
  have l2 := Real.log_le_log hp h2
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at l1
  rw [Real.log_mul (Real.exp_pos _).ne' hq.ne', Real.log_exp] at l2
  rw [abs_le]
  constructor <;> linarith

end PolymerExtra

section Vortex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `MatchAt` depends only on `|w|`. -/
theorem matchAt_of_abs {w w' : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt w a κ)
    (h : ∀ X, |w' X| = |w X|) : MatchAt w' a κ := by
  refine ⟨?_, hM.2.1, hM.2.2.1, hM.2.2.2.1, fun v => ?_⟩
  · have h0 := h ∅
    rw [hM.1, abs_zero] at h0
    exact abs_eq_zero.1 h0
  · simp only [h]
    exact hM.2.2.2.2 v

/-- **A large polymer's weight is damped by the decay rate**: `|X| ≥ A` gives
`|w X| e^{a|X|} ≤ kp X · e^{−κA}`. -/
theorem eps_le_of_large {w : Finset V → ℝ} {a κ A : ℝ} (hκ : 0 ≤ κ) {X : Finset V}
    (hX : X.Nonempty) (hA : A ≤ X.card) : eps w a X ≤ kp w a κ X * Real.exp (-(κ * A)) := by
  have hk : kp w a κ X = eps w a X * (1 + X.card * Real.exp (κ * X.card)) := rfl
  have h1 : (1 : ℝ) ≤ X.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (card_pos.2 hX).ne'
  have h2 : Real.exp (κ * A) ≤ Real.exp (κ * X.card) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hA hκ)
  have h3 : Real.exp (κ * A) ≤ 1 + X.card * Real.exp (κ * X.card) := by
    nlinarith [Real.exp_pos (κ * X.card)]
  have he := eps_nonneg w a X
  rw [hk]
  calc eps w a X = eps w a X * Real.exp (κ * A) * Real.exp (-(κ * A)) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ eps w a X * (1 + X.card * Real.exp (κ * X.card)) * Real.exp (-(κ * A)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 he) (Real.exp_pos _).le

/-- **The vortex bound of a polymer pair**: `MatchAt w a κ`, `|w'| = |w|`, `w' = w` off `B`, every
polymer of `B` of size `≥ A` and meeting `W`, give `|log Z(w) − log Z(w')| ≤ 2 |W| a e^{−κA}`. -/
theorem vortex_bound {w w' : Finset V → ℝ} {a κ A : ℝ} {B : Finset (Finset V)} {W : Finset V}
    (hM : MatchAt w a κ) (habs : ∀ X, |w' X| = |w X|) (hagree : ∀ X, X ∉ B → w' X = w X)
    (hB : ∀ X ∈ B, A ≤ X.card ∧ (W ∩ X).Nonempty) :
    |Real.log (Z meet w univ) - Real.log (Z meet w' univ)|
      ≤ 2 * (W.card * a * Real.exp (-(κ * A))) := by
  have hM' := matchAt_of_abs hM habs
  have hcK : cKP w' a = cKP w a := funext fun X => by unfold cKP eps; rw [habs X]
  have hD := dob_of_matchAt hM
  have hD' : Dob meet w' (cKP w a) := by
    have := dob_of_matchAt hM'
    rwa [hcK] at this
  have h1 := abs_log_sdiff_le meet_symm hD univ B
  have h2 := abs_log_sdiff_le meet_symm hD' univ B
  have hcong : Z meet w (univ \ B) = Z meet w' (univ \ B) :=
    Z_congr fun X hX => (hagree X (mem_sdiff.1 hX).2).symm
  have hsum : ∑ X ∈ B, cKP w a X ≤ W.card * a * Real.exp (-(κ * A)) := by
    calc ∑ X ∈ B, cKP w a X ≤ ∑ X ∈ B, kp w a κ X * Real.exp (-(κ * A)) := by
          refine sum_le_sum fun X hX => ?_
          have hc : cKP w a X ≤ eps w a X := by
            unfold cKP
            have := Real.log_le_sub_one_of_pos (by linarith [eps_nonneg w a X] : 0 < 1 + eps w a X)
            linarith
          exact hc.trans (eps_le_of_large hM.2.2.2.1 ((hB X hX).2.mono inter_subset_right)
            (hB X hX).1)
      _ = (∑ X ∈ B, kp w a κ X) * Real.exp (-(κ * A)) := by rw [sum_mul]
      _ ≤ (W.card * a) * Real.exp (-(κ * A)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          calc ∑ X ∈ B, kp w a κ X ≤ ∑ v ∈ W, ∑ Y ∈ site v, kp w a κ Y :=
                sum_meet_le _ (kp_nonneg w a κ) W B fun Y hY => (hB Y hY).2
            _ ≤ W.card * a := sum_site_le hM W
  rw [hcong] at h1
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

variable {C Θ : Type*}

/-- **`StrongEnd`** — the flow has reached the strong-coupling region at `c`: the coarse pair is a
polymer pair `(w, w')` with `MatchAt w a κ`, `|w'| = |w|`, `w' = w` off polymers of size `≥ A` meeting
`W`, and `Zf c = Z(w)`, `Zfp c = (Z(w) + Z(w'))/2`. -/
def StrongEnd (Zf Zfp : C → ℝ) (a κ A : ℝ) (W : Finset V) (c : C) : Prop :=
  ∃ (w w' : Finset V → ℝ) (B : Finset (Finset V)), MatchAt w a κ ∧ (∀ X, |w' X| = |w X|) ∧
    (∀ X, X ∉ B → w' X = w X) ∧ (∀ X ∈ B, A ≤ X.card ∧ (W ∩ X).Nonempty) ∧
    Zf c = Z meet w univ ∧ Zfp c = (Z meet w univ + Z meet w' univ) / 2

variable {Zf Zfp : C → ℝ} {bulk : C → Θ → ℝ} {next : C → Θ → C}

/-- **The vortex ratio at the strong end**: `|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA}`. -/
theorem log_ratio_end {a κ A : ℝ} {W : Finset V} {c : C} (hend : StrongEnd Zf Zfp a κ A W c) :
    |Real.log (fluxRatio Zf Zfp c)| ≤ 2 * (W.card * a * Real.exp (-(κ * A))) := by
  obtain ⟨w, w', B, hM, habs, hagree, hB, hZ, hZp⟩ := hend
  set δ := 2 * (W.card * a * Real.exp (-(κ * A)))
  have hv : |Real.log (Z meet w univ) - Real.log (Z meet w' univ)| ≤ δ := vortex_bound hM habs hagree hB
  have hδ0 : 0 ≤ δ :=
    mul_nonneg zero_le_two (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM.2.1) (Real.exp_pos _).le)
  have hD := dob_of_matchAt hM
  have hD' : Dob meet w' (cKP w' a) := dob_of_matchAt (matchAt_of_abs hM habs)
  have hP := Z_pos meet_symm hD univ
  have hP' := Z_pos meet_symm hD' univ
  set P := Z meet w univ
  set P' := Z meet w' univ
  rw [abs_le] at hv
  have hup : P' ≤ Real.exp δ * P := by
    calc P' = Real.exp (Real.log P') := (Real.exp_log hP').symm
      _ ≤ Real.exp (Real.log P + δ) := Real.exp_le_exp.2 (by linarith [hv.1])
      _ = Real.exp δ * P := by rw [Real.exp_add, Real.exp_log hP, mul_comm]
  have hlo : Real.exp (-δ) * P ≤ P' := by
    calc Real.exp (-δ) * P = Real.exp (Real.log P - δ) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hP, mul_comm]
      _ ≤ Real.exp (Real.log P') := Real.exp_le_exp.2 (by linarith [hv.2])
      _ = P' := Real.exp_log hP'
  have he1 : 1 ≤ Real.exp δ := Real.one_le_exp hδ0
  have he2 : Real.exp (-δ) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
  have hr : fluxRatio Zf Zfp c = ((P + P') / 2) / P := by
    unfold fluxRatio; rw [hZ, hZp]
  have hrup : fluxRatio Zf Zfp c ≤ Real.exp δ := by
    rw [hr, div_le_iff₀ hP]
    have := le_mul_of_one_le_left hP.le he1
    linarith
  have hrlo : Real.exp (-δ) ≤ fluxRatio Zf Zfp c := by
    rw [hr, le_div_iff₀ hP]
    have := mul_le_of_le_one_left hP.le he2
    linarith
  have hrpos : 0 < fluxRatio Zf Zfp c := lt_of_lt_of_le (Real.exp_pos _) hrlo
  have l1 := Real.log_le_log hrpos hrup
  have l2 := Real.log_le_log (Real.exp_pos _) hrlo
  rw [Real.log_exp] at l1 l2
  rw [abs_le]
  exact ⟨l2, l1⟩

/-! ## 5. The chain -/

/-- **The chain with errors**: log-ratio errors `ε m` along the orbit and `StrongEnd` after `n` steps
give `|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA} + Σ_{m<n} ε m`. -/
theorem vortex_of_sandwich {a κ A : ℝ} {W : Finset V} {c : C} {θs : ℕ → Θ} {n : ℕ} {ε : ℕ → ℝ}
    (hmatch : ∀ m < n, |Real.log (fluxRatio Zf Zfp (mkOrbit next θs c m))
      - Real.log (fluxRatio Zf Zfp (mkOrbit next θs c (m + 1)))| ≤ ε m)
    (hend : StrongEnd Zf Zfp a κ A W (mkOrbit next θs c n)) :
    |Real.log (fluxRatio Zf Zfp c)|
      ≤ 2 * (W.card * a * Real.exp (-(κ * A))) + ∑ m ∈ range n, ε m := by
  have h1 := log_ratio_orbit (R := fluxRatio Zf Zfp) n hmatch
  have h2 := log_ratio_end hend
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The chain**: `SandwichMatch` at each of `n` steps and `StrongEnd` after them give
`|log (Zfp c / Zf c)| ≤ 2 |W| a e^{−κA}`. -/
theorem vortex_of_sandwichMatch {a κ A : ℝ} {W : Finset V} {c : C} {θs : ℕ → Θ} {n : ℕ}
    (hmatch : ∀ m < n, SandwichMatch Zf Zfp bulk next (mkOrbit next θs c m) (θs m))
    (hend : StrongEnd Zf Zfp a κ A W (mkOrbit next θs c n)) :
    |Real.log (fluxRatio Zf Zfp c)| ≤ 2 * (W.card * a * Real.exp (-(κ * A))) := by
  rw [ratio_orbit_of_match hmatch]
  exact log_ratio_end hend

/-- **The 't Hooft form**: under the chain's hypotheses, with `Z⁽⁻⁾ = 2 Zfp − Zf`,
`|Z⁽⁻⁾ / Z − 1| ≤ 2 (e^{2|W| a e^{−κA}} − 1)`. -/
theorem thooft_of_sandwichMatch {a κ A : ℝ} {W : Finset V} {c : C} {θs : ℕ → Θ} {n : ℕ}
    (hmatch : ∀ m < n, SandwichMatch Zf Zfp bulk next (mkOrbit next θs c m) (θs m))
    (hend : StrongEnd Zf Zfp a κ A W (mkOrbit next θs c n)) (hZ : 0 < Zf c) (hZp : 0 < Zfp c) :
    |(2 * Zfp c - Zf c) / Zf c - 1|
      ≤ 2 * (Real.exp (2 * (W.card * a * Real.exp (-(κ * A)))) - 1) := by
  have hb := vortex_of_sandwichMatch hmatch hend
  have hr : 0 < fluxRatio Zf Zfp c := div_pos hZp hZ
  have hid : (2 * Zfp c - Zf c) / Zf c - 1 = 2 * (fluxRatio Zf Zfp c - 1) := by
    unfold fluxRatio
    first | (field_simp; done) | (field_simp; ring)
  rw [hid, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have he := abs_exp_sub_one_le hb
  rw [Real.exp_log hr] at he
  linarith

/-! ## 6. The window and the contrapositive -/

/-- **The window**: `lo ≤ Z ≤ hi`, `lo⁺ ≤ Z⁺ ≤ hi⁺` place `Z⁺/Z` in `[lo⁺/hi, hi⁺/lo]`. -/
theorem ratio_window {Z Zp lo hi lop hip : ℝ} (hlo : 0 < lo) (h1 : lo ≤ Z) (h2 : Z ≤ hi)
    (hlop : 0 ≤ lop) (h3 : lop ≤ Zp) (h4 : Zp ≤ hip) : lop / hi ≤ Zp / Z ∧ Zp / Z ≤ hip / lo := by
  have hZ : 0 < Z := hlo.trans_le h1
  have hhi : 0 < hi := hZ.trans_le h2
  constructor
  · rw [div_le_div_iff₀ hhi hZ]
    nlinarith [mul_le_mul_of_nonneg_left h2 hlop, mul_le_mul_of_nonneg_right h3 hhi.le]
  · rw [div_le_div_iff₀ hZ hlo]
    nlinarith [mul_le_mul_of_nonneg_left h1 (hlop.trans h3), mul_le_mul_of_nonneg_right h4 hZ.le]

/-- **The window is extensive**: `hi = F^N Z_c(c^U)`, `lo = Z_c(c^L)` with `F ≥ 1` and
`Z_c(c^L) ≤ Z_c(c^U)` give `log hi − log lo ≥ N log F`. -/
theorem window_extensive {F Zu Zl : ℝ} (hF : 1 ≤ F) (hl : 0 < Zl) (hlu : Zl ≤ Zu) (N : ℕ) :
    (N : ℝ) * Real.log F ≤ Real.log (F ^ N * Zu) - Real.log Zl := by
  have hF0 : 0 < F := by linarith
  have hu : 0 < Zu := hl.trans_le hlu
  rw [Real.log_mul (pow_pos hF0 N).ne' hu.ne', Real.log_pow]
  linarith [Real.log_le_log hl hlu]

/-- **The contrapositive** (the form of the `U(1)` objection): if every orbit of length `n` reaches
`StrongEnd` and `|log (Zfp c / Zf c)| > 2 |W| a e^{−κA}`, no orbit carries `SandwichMatch` at all `n`
steps. -/
theorem not_sandwichMatch_of_vortex {a κ A : ℝ} {W : Finset V} {c : C} {n : ℕ}
    (hreach : ∀ θs : ℕ → Θ, StrongEnd Zf Zfp a κ A W (mkOrbit next θs c n))
    (hbig : 2 * (W.card * a * Real.exp (-(κ * A))) < |Real.log (fluxRatio Zf Zfp c)|) :
    ¬ ∃ θs : ℕ → Θ, ∀ m < n, SandwichMatch Zf Zfp bulk next (mkOrbit next θs c m) (θs m) := by
  rintro ⟨θs, hθ⟩
  exact absurd (vortex_of_sandwichMatch hθ (hreach θs)) (not_le.2 hbig)

end Vortex

#print axioms bondMove_upper
#print axioms move_balanced
#print axioms bondMove_upper_of_translation
#print axioms pow_integral_ge_one
#print axioms mkUpperF0_ge_one
#print axioms interp_dev
#print axioms abs_interp_dev_le
#print axioms exists_interp
#print axioms interp_unique
#print axioms sandwichMatch_of_crossing
#print axioms ratio_eq_of_match
#print axioms ratio_orbit_of_match
#print axioms exists_matched_orbit
#print axioms log_ratio_orbit
#print axioms Z_congr
#print axioms Z_le_exp_sdiff
#print axioms abs_log_sdiff_le
#print axioms matchAt_of_abs
#print axioms eps_le_of_large
#print axioms vortex_bound
#print axioms log_ratio_end
#print axioms vortex_of_sandwich
#print axioms vortex_of_sandwichMatch
#print axioms thooft_of_sandwichMatch
#print axioms ratio_window
#print axioms window_extensive
#print axioms not_sandwichMatch_of_vortex

end MassGap.MKBound
