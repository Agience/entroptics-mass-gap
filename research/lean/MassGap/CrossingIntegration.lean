import Mathlib
import MassGap.CharacterExpansion

/-!
# MassGap.CrossingIntegration — two obstructions to a pointwise pairing, and an integration
that avoids them

## Part 1 — the straddling word is not a paired form

`CharacterExpansion.crossweight_pairing_nonneg` consumes a weight of the form
`∑ k, c k * hsRe (X k U) (X k (Θ U))` with `c k ≥ 0`. `paired_sum_nonneg_at_fixed` observes that any
such sum is nonnegative at a reflection-fixed configuration, since the two arguments coincide there
and each term is a coefficient times `hsRe A A`, which `hsRe_self_nonneg` makes a sum of squares.
`no_paired_expansion_of_neg_at_fixed`, `no_paired_word_of_neg_at_fixed` and
`no_half_paired_of_neg_at_fixed` are the contrapositives, for the trace, for the matrix word
`W = X * (ΘX)ᴴ`, and for an `X` reading only one half.

The witness is `cfgWitness l₀`: the identity on every link except one reflection-fixed axis link,
which carries `gNeg = diag (1, -1, -1)`. That element lies in `SU 3` (`NegControl.cA_mem_SU`) and is
its own inverse (`gNeg_inv`), which is what makes the configuration `reflConf`-fixed
(`reflConf_cfgWitness`), since the reflection inverts that link. The straddling plaquette through it
has holonomy `gNeg` (`hol_cfgWitness`), whose `Re trace` is `-1` (`trace_gNeg`).

`straddling_word_not_paired_at_odd_lag` and `straddling_word_not_matrix_paired_at_odd_lag` are the
conclusions at even extent and odd reflection constant.
`straddling_not_paired_four_dim` instantiates the first at `d = 4`, extent `4`, axis `0`, transverse
direction `1`, constant `1`.

`no_paired_after_equivariant_reparam` repeats the argument after a reparametrisation commuting with
the reflection; the commutation is a hypothesis and is not discharged here. `invLink` is the
substitution `g ↦ g⁻¹` on a chosen set of links, which `Reflect.isInvInvariant_probHaar` licenses,
and `invLink_cfgWitness` shows it fixes this witness, since every link of the witness carries a
self-inverse element.

## Part 2 — the straddling word is not a function of the two halves

`crossweight_pairing_nonneg` reads its word through `X : (S → Ω) → Matrix`, a function of the
positive half's restriction. A reflection-fixed axis link lies in neither half, since `S` and `T`
are disjoint and the reflection carries `S` into `T` while fixing that link.
`straddling_word_not_determined_by_halves` exhibits two configurations agreeing on `S` and whose
reflections agree on `S`, with different `Re trace` at one straddling plaquette, and
`no_half_function_for_straddling_word` refutes every `Φ : (S → SU 3) → (S → SU 3) → ℝ`, which
includes `Φ u v = κ + c * hsRe (X u) (X v)` with any constant and any rescaling.

## Part 3 — the crossing-link integration

The plane links act on the transverse links beside them as a gauge field acts on link variables,
`(F^G)_x = G_x * F_x * G_{x+ν̂}⁻¹`, so a straddling plaquette word is `hsRe (X (act g x)) (X y)`.
`gaugeAvg lam act a x = ∫ g, a (act g x)` is the average over the plane links; `gaugeAvg_act` shows
it is gauge-invariant, using right invariance of the plane measure, and
`integral_gaugeAvg_mul_invariant` moves it from one factor of a pairing to another against an
invariant partner. `kernel_arg_shift` moves a gauge from the kernel's first argument onto the
integration variable, using measure-preservation of the action and invariance of the kernel.
`crossing_gauge_integral_eq` is the resulting identity

    ∫ g ∫ x ∫ y, a x * a y * K (act g x) y  =  ∫ x ∫ y, (P a) x * (P a) y * K x y,

and `crossing_gauge_pairing_nonneg` concludes nonnegativity from a positive-semidefiniteness
hypothesis on `K`.

That hypothesis is discharged for the Wilson kernel by `wilson_kernel_integral_psd`:
`0 ≤ ∫∫ f x * f y * exp (β * hsRe (X x) (X y))` for `0 ≤ β`, bounded measurable `f`, and a word
whose coordinates are bounded by `1`. The proof is `hasSum_wilsonWeight_paired` order by order,
`MeasureTheory.integral_prod_mul` turning each order into a square, and dominated convergence
summing them. `wilson_crossing_pairing_nonneg` composes the two.

`hsRe_coe_eq` identifies `hsRe a b` with `Re trace (a * b⁻¹)` for unitary arguments, and
`hsRe_conj` proves `hsRe (g a h⁻¹) (g b h⁻¹) = hsRe a b` by cyclicity of the trace, which is the
invariance hypothesis the integration consumes.
`negctl_hsRe_one_sided_not_invariant` shows the two-sided shape is required.

## Scope

* Both obstructions in Parts 1 and 2 are about one straddling plaquette. The Boltzmann weight's
  straddling factor is the exponential of a sum over all straddling plaquettes and both fixed
  planes, and neither theorem rules out that the sum is a paired form. At `cfgWitness` the sum is
  positive: only the plaquettes through the one modified link read `-1` and every other straddling
  plaquette reads `3`, so this witness does not lift to the sum. A witness intended to lift — `gNeg`
  on every fixed axis link whose transverse coordinates have even sum — is not built here.
* Neither obstruction says reflection positivity fails at odd lags; they say it is not pointwise.
* Part 3 is stated for an abstract half `Ω`, plane group `Γ` and word `X`. Nothing ties `X` to
  `wilsonHol`, ties `Γ` to the fixed axis links, or discharges `hXinv` on the lattice.
  `hsRe_conj` is one matrix pair under one gauge pair; the direct-sum form needed when several
  straddling plaquettes are read together is not proved here. The odd-lag action split — that at a
  link-reflection plane every plaquette reads one half, the other, or straddles, that the straddling
  ones aggregate to the gauge-transformed cross form, and that the reflected half's weight is the
  same function of the transported variables — is not in this module; `ActionSplit` does the
  even-lag counterpart.
* `crossing_gauge_pairing_nonneg`'s `hPSD` cannot be dropped:
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refutes it for the `SU 3` Wilson kernel at
  `β < 0` on two explicit group elements.
* Mathlib v4.31 carries no compact-group representation theory —
  `RepresentationTheory.Character.char_orthonormal` is stated for a finite group — so Schur
  orthogonality is not available; the route here does not use it.
  `MassGap.HaarMoments` computes the `SU 2` fundamental's second moment exactly
  (`haar_su2_second_moment`) and reaches order four only as bounds
  (`haar_su2_fourth_moment_diag_bounds`); the crossing weight is of every order in the plane links,
  so that route would need balanced moments at all orders. The argument here expands in the plane
  links at no order.
-/

namespace MassGap.CrossingIntegration

open MeasureTheory
open MassGap MassGap.ActionSplit MassGap.CharacterExpansion
open MassGap.WilsonLattice MassGap.WilsonHypercubic
open MassGap.CompactGauge MassGap.Reflect

/-! ## Part 1 — a paired form is a square at a reflection-fixed configuration -/

/-- **`hsRe A A` is a sum of squares.** `hsRe` is the Euclidean inner product of the `2N²` real
coordinates (`hsRe_eq_sum`), so its diagonal is `‖A‖²_F`.

DERIVED: the only numeral is the `0` of `0 ≤ ·`, which is the property. -/
theorem hsRe_self_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ hsRe A A := by
  rw [hsRe_eq_sum]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- `0 ≤ ∑ k, c k * hsRe (X k U₀) (X k (Θ U₀))` whenever `Θ U₀ = U₀` and `0 ≤ c k` at every `k`.
Rewriting by the fixed-point hypothesis makes both arguments of each `hsRe` equal, so each term is a
nonnegative coefficient times `hsRe_self_nonneg`.

Scope: `X` may read the entire configuration, including the reflection plane, and `K` may be any
finite index type.

DERIVED: the one numeral is `0`, the lower bound on each coefficient and on the sum. -/
theorem paired_sum_nonneg_at_fixed {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    {K : Type} [Fintype K] {Nc : ℕ} (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (X : K → γ → Matrix (Fin Nc) (Fin Nc) ℂ) :
    0 ≤ ∑ k, c k * hsRe (X k U₀) (X k (Θ U₀)) := by
  rw [hfix]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (hsRe_self_nonneg _)

/-- The contrapositive of `paired_sum_nonneg_at_fixed`: if `(trace (W U₀)).re < 0` at a
reflection-fixed `U₀`, then `(trace (W U)).re` is not `∑ k, c k * hsRe (X k U) (X k (Θ U))` for any
finite family `X` and nonnegative coefficients `c`.

DERIVED: the one numeral is `0`, the upper bound on the trace at the fixed point and the lower bound
on each coefficient. -/
theorem no_paired_expansion_of_neg_at_fixed {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    {N : ℕ} (W : γ → Matrix (Fin N) (Fin N) ℂ) (hW : (Matrix.trace (W U₀)).re < 0)
    {K : Type} [Fintype K] {Nc : ℕ} (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (X : K → γ → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ¬ ∀ U, (Matrix.trace (W U)).re = ∑ k, c k * hsRe (X k U) (X k (Θ U)) := by
  intro h
  have h0 := paired_sum_nonneg_at_fixed Θ hfix c hc X
  rw [← h U₀] at h0
  exact absurd hW (not_lt.mpr h0)

/-- The same at the level of the matrix word: with `(trace (W U₀)).re < 0` at a reflection-fixed
`U₀`, no `X` satisfies `W U = X U * (X (Θ U))ᴴ` at every `U`, since at `U₀` the right-hand side's
trace would be `hsRe (X U₀) (X U₀) ≥ 0`.

DERIVED: the one numeral is `0`, the upper bound on the trace at the fixed point. -/
theorem no_paired_word_of_neg_at_fixed {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    {N : ℕ} (W : γ → Matrix (Fin N) (Fin N) ℂ) (hW : (Matrix.trace (W U₀)).re < 0)
    (X : γ → Matrix (Fin N) (Fin N) ℂ) :
    ¬ ∀ U, W U = X U * Matrix.conjTranspose (X (Θ U)) := by
  intro h
  have heq : (Matrix.trace (W U₀)).re = hsRe (X U₀) (X (Θ U₀)) := by rw [h U₀]; rfl
  rw [hfix] at heq
  exact absurd hW (not_lt.mpr (heq ▸ hsRe_self_nonneg (X U₀)))

/-- The same with `X` reading only the restriction of the configuration to one half `S`, which is
the shape `CharacterExpansion.crossweight_pairing_nonneg` consumes. A half-reading `X` is a special
case of an arbitrary one, so this follows from `no_paired_expansion_of_neg_at_fixed`.

DERIVED: the one numeral is `0`, the upper bound on the trace at the fixed point. -/
theorem no_half_paired_of_neg_at_fixed {ι : Type} [Fintype ι] {Ω : Type} (S : Finset ι)
    (Θ : (ι → Ω) → (ι → Ω)) {U₀ : ι → Ω} (hfix : Θ U₀ = U₀)
    {N : ℕ} (W : (ι → Ω) → Matrix (Fin N) (Fin N) ℂ)
    (hW : (Matrix.trace (W U₀)).re < 0)
    {Nc : ℕ} (X : (S → Ω) → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ¬ ∀ U, (Matrix.trace (W U)).re
        = hsRe (X fun i : S => U (i : ι)) (X fun i : S => Θ U (i : ι)) := by
  intro h
  have h0 : (Matrix.trace (W U₀)).re
      = hsRe (X fun i : S => U₀ (i : ι)) (X fun i : S => U₀ (i : ι)) := by
    rw [h U₀, hfix]
  exact absurd hW (not_lt.mpr (h0 ▸ hsRe_self_nonneg _))

/-- The same refutation after a reparametrisation `T : Equiv.Perm γ` commuting with the involution:
`(trace (W (T U))).re` is not a nonnegative combination of paired forms either. At `T.symm U₀` the
commutation makes the configuration reflection-fixed and the reparametrised word takes the same
negative value.

Scope: the commutation `hTΘ` is a hypothesis and is not discharged here for any substitution.

DERIVED: the one numeral is `0`, the upper bound on the trace at the fixed point and the lower bound
on each coefficient. -/
theorem no_paired_after_equivariant_reparam {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    (T : Equiv.Perm γ) (hTΘ : ∀ U, T (Θ U) = Θ (T U))
    {N : ℕ} (W : γ → Matrix (Fin N) (Fin N) ℂ) (hW : (Matrix.trace (W U₀)).re < 0)
    {K : Type} [Fintype K] {Nc : ℕ} (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (X : K → γ → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ¬ ∀ U, (Matrix.trace (W (T U))).re = ∑ k, c k * hsRe (X k U) (X k (Θ U)) := by
  have hstep : T (Θ (T.symm U₀)) = T (T.symm U₀) := by
    rw [hTΘ (T.symm U₀), T.apply_symm_apply, hfix]
  have hfix' : Θ (T.symm U₀) = T.symm U₀ := T.injective hstep
  have hW' : (Matrix.trace ((fun U => W (T U)) (T.symm U₀))).re < 0 := by
    show (Matrix.trace (W (T (T.symm U₀)))).re < 0
    rw [T.apply_symm_apply]
    exact hW
  exact no_paired_expansion_of_neg_at_fixed Θ hfix' (fun U => W (T U)) hW' c hc X

/-! ## The witness on the Wilson lattice

An `SU(3)` element that is its own inverse, sitting on a reflection-fixed axis link. The reflection
inverts that link, so inverting nothing is what makes the configuration fixed; and the element is
far enough from the identity that the plaquette through it has negative `Re tr`. -/

section Witness

variable {d n : ℕ}

/-- `diag(1, −1, −1)` as an element of the group `SU(3)` — `NegControl.cA 1` with its membership
proof, which `NegControl.cA_mem_SU` already supplies.

DERIVED: `3` is the degree of `SU(3)`, its matrix dimension; `1` selects the non-identity control element, whose square is the identity -- which is exactly why a configuration carrying it on a fixed axis link is reflection-fixed. -/
noncomputable def gNeg : MassGap.SUN.SU 3 := ⟨NegControl.cA 1, NegControl.cA_mem_SU 1⟩

/-- `gNeg * gNeg = 1`, checked entrywise on the diagonal matrix.

DERIVED: `1` is the group identity on the right and the index selecting `NegControl.cA 1` on the
left; the squared entries are `1` and `(-1) ^ 2`. -/
theorem gNeg_mul_self : gNeg * gNeg = 1 := by
  refine Subtype.ext ?_
  rw [Submonoid.coe_mul, Submonoid.coe_one]
  show NegControl.cA 1 * NegControl.cA 1 = (1 : Matrix (Fin 3) (Fin 3) ℂ)
  simp only [NegControl.cA, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num [NegControl.dvec]

/-- `gNeg⁻¹ = gNeg`, from `gNeg_mul_self` through `inv_eq_of_mul_eq_one_right`. This is what makes
a configuration carrying `gNeg` on a reflection-fixed axis link invariant under the reflection's
dagger.

DERIVED: no numeral occurs in the statement. -/
theorem gNeg_inv : gNeg⁻¹ = gNeg := inv_eq_of_mul_eq_one_right gNeg_mul_self

/-- `(trace gNeg).re = -1`, computed as `1 + (-1) + (-1)` over the diagonal.

DERIVED: `3` is the matrix size, so the diagonal has three entries; `1` is the index selecting
`NegControl.cA 1`; `-1` is the computed value of the trace's real part, not a chosen magnitude. -/
theorem trace_gNeg : (Matrix.trace (gNeg : Matrix (Fin 3) (Fin 3) ℂ)).re = -1 := by
  show (Matrix.trace (NegControl.cA 1)).re = -1
  simp only [NegControl.cA, Matrix.trace_diagonal, Complex.re_sum]
  norm_num [NegControl.dvec, Fin.sum_univ_succ]

/-- **The witness configuration**: the identity on every link but `l₀`, where it is `gNeg`.

DERIVED: `3` is the degree of `SU(3)`, its matrix dimension, `1` the identity on every link but one. The single exceptional link is the argument; nothing about it is a tunable. -/
noncomputable def cfgWitness [NeZero n] (l₀ : Link d n) : Link d n → MassGap.SUN.SU 3 :=
  Function.update (fun _ => 1) l₀ gNeg

@[simp] theorem cfgWitness_at [NeZero n] (l₀ : Link d n) : cfgWitness l₀ l₀ = gNeg := by
  simp [cfgWitness]

theorem cfgWitness_of_ne [NeZero n] {l₀ l : Link d n} (h : l ≠ l₀) : cfgWitness l₀ l = 1 := by
  simp [cfgWitness, Function.update_of_ne h]

/-- `reflConf τ c (cfgWitness l₀) = cfgWitness l₀`, given that `l₀` is an axis link (`l₀.1 = τ`)
fixed by `reflLink τ c`. On `l₀` the reflection inverts and `gNeg_inv` makes that inert; every other
link carries the identity, which the reflection permutes among the identities.

DERIVED: no numeral occurs in the statement; the group elements are inside `cfgWitness`. -/
theorem reflConf_cfgWitness [NeZero n] {τ : Fin d} {c : Fin n} {l₀ : Link d n}
    (h1 : l₀.1 = τ) (hfix : reflLink τ c l₀ = l₀) :
    reflConf τ c (cfgWitness l₀) = cfgWitness l₀ := by
  funext l
  show (if l.1 = τ then (cfgWitness l₀ (reflLink τ c l))⁻¹ else cfgWitness l₀ (reflLink τ c l))
      = cfgWitness l₀ l
  by_cases hl : l = l₀
  · rw [hl, if_pos h1, hfix, cfgWitness_at, gNeg_inv]
  · have h2 : reflLink τ c l ≠ l₀ := by
      intro hcon
      have hback := congrArg (reflLink τ c) hcon
      rw [reflLink_involutive τ c l, hfix] at hback
      exact hl hback
    rw [cfgWitness_of_ne hl, cfgWitness_of_ne h2]
    simp

/-- `wilsonHol bd ((τ, ν), x) (cfgWitness (τ, x)) = gNeg`. Three of the plaquette's four links
carry the identity: the two transverse ones because their direction is not `τ`, and the second axis
link because it is a different fixed axis link from `l₀` — the two-fixed-link geometry
`CharacterExpansion.odd_lag_straddling_plaq_two_fixed_axis_links` establishes.

DERIVED: no numeral occurs in the statement. -/
theorem hol_cfgWitness [NeZero n] {τ ν : Fin d} (hν : ν ≠ τ) {x : Site d n}
    (hne : ((τ, x) : Link d n) ≠ (τ, WilsonHypercubic.shift ν x)) :
    wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) (cfgWitness ((τ, x) : Link d n))
      = gNeg := by
  have h2 : cfgWitness ((τ, x) : Link d n) ((ν, WilsonHypercubic.shift τ x) : Link d n) = 1 :=
    cfgWitness_of_ne (fun hc => hν (congrArg Prod.fst hc))
  have h3 : cfgWitness ((τ, x) : Link d n) ((τ, WilsonHypercubic.shift ν x) : Link d n) = 1 :=
    cfgWitness_of_ne (fun hc => hne hc.symm)
  have h4 : cfgWitness ((τ, x) : Link d n) ((ν, x) : Link d n) = 1 :=
    cfgWitness_of_ne (fun hc => hν (congrArg Prod.fst hc))
  simp [wilsonHol, bd, h2, h3, h4]

end Witness

/-! ## The refutation, on the lattice -/

section Answer

variable {d n : ℕ}

/-- At even extent `n` with `2 ≤ n` and an odd reflection constant, there is a plaquette `q₀` whose
`Re trace` is not `∑ k, cf k * hsRe (X k U) (X k (reflConf τ c U))` at every `U`, for any finite
family `X` with nonnegative coefficients. The witness is `cfgWitness` at a fixed axis link, where
the holonomy is `gNeg` and the trace's real part is `-1`, while any paired form is a square there.

Scope: this is about one straddling plaquette's word. It does not say the sum over all straddling
plaquettes fails to be a paired form; see the module header.

DERIVED: `2` is the lower bound on the extent, which is what makes a transverse step move the site;
`3` is the gauge group's matrix size, `SU 3`; `0` is the lower bound on each coefficient. The value
`-1` is the computed trace of `gNeg` and appears in the proof. -/
theorem straddling_word_not_paired_at_odd_lag [NeZero n] (hn : Even n) (h2 : 2 ≤ n)
    {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} (hc : ¬ Even c.val)
    {K : Type} [Fintype K] {Nc : ℕ} (cf : K → ℝ) (hcf : ∀ k, 0 ≤ cf k)
    (X : K → (Link d n → MassGap.SUN.SU 3) → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ∃ q₀ : Plaq d n, ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q₀ U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re
        = ∑ k, cf k * hsRe (X k U) (X k (reflConf τ c U)) := by
  obtain ⟨x, hne, -, -, hfix1, -⟩ :=
    odd_lag_straddling_plaq_two_fixed_axis_links (d := d) (n := n) hn h2 hν hc
  refine ⟨((τ, ν), x), ?_⟩
  have hwitfix : reflConf τ c (cfgWitness ((τ, x) : Link d n)) = cfgWitness ((τ, x) : Link d n) :=
    reflConf_cfgWitness rfl hfix1
  have hneg : (Matrix.trace
      ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n)
          (cfgWitness ((τ, x) : Link d n)) : MassGap.SUN.SU 3)
        : Matrix (Fin 3) (Fin 3) ℂ)).re < 0 := by
    rw [hol_cfgWitness hν hne, trace_gNeg]
    norm_num
  exact no_paired_expansion_of_neg_at_fixed (reflConf τ c) hwitfix
    (fun U => ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)) hneg cf hcf X

/-- The same for a single matrix word: at even extent with `2 ≤ n` and an odd reflection constant
there is a plaquette whose holonomy is not `X U * (X (reflConf τ c U))ᴴ` at every `U`, for any `X`.

DERIVED: `2` is the lower bound on the extent; `3` is the gauge group's matrix size. -/
theorem straddling_word_not_matrix_paired_at_odd_lag [NeZero n] (hn : Even n) (h2 : 2 ≤ n)
    {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} (hc : ¬ Even c.val)
    (X : (Link d n → MassGap.SUN.SU 3) → Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ q₀ : Plaq d n, ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      ((wilsonHol (bd (d := d) (n := n)) q₀ U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)
        = X U * Matrix.conjTranspose (X (reflConf τ c U)) := by
  obtain ⟨x, hne, -, -, hfix1, -⟩ :=
    odd_lag_straddling_plaq_two_fixed_axis_links (d := d) (n := n) hn h2 hν hc
  refine ⟨((τ, ν), x), ?_⟩
  have hwitfix : reflConf τ c (cfgWitness ((τ, x) : Link d n)) = cfgWitness ((τ, x) : Link d n) :=
    reflConf_cfgWitness rfl hfix1
  have hneg : (Matrix.trace
      ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n)
          (cfgWitness ((τ, x) : Link d n)) : MassGap.SUN.SU 3)
        : Matrix (Fin 3) (Fin 3) ℂ)).re < 0 := by
    rw [hol_cfgWitness hν hne, trace_gNeg]
    norm_num
  exact no_paired_word_of_neg_at_fixed (reflConf τ c) hwitfix
    (fun U => ((wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n) U : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)) hneg X

end Answer

/-! ## A second, independent obstruction: the word is not a function of the two halves

`straddling_word_not_matrix_paired_at_odd_lag` rules out the paired form, for an `X` allowed to read
anything. There is a second obstruction, independent of it and immune to rescaling and to additive
constants: `CharacterExpansion.crossweight_pairing_nonneg` reads its word through
`X : (S → Ω) → Matrix`, a function of the positive half's restriction, and the straddling word is not
determined by that data at all.

The reason is the geometry the odd lag forces. A fixed axis link lies in neither half — it cannot,
because the reflection fixes it while `S` and `T` are disjoint and the reflection carries `S` into
`T`. Moving one of them moves the straddling word and leaves both half-restrictions exactly where
they were. -/

section NotAHalfFunction

variable {d n : ℕ}

/-- For disjoint `S, T` with `reflLink τ c` carrying `S` into `T`, at even extent with `2 ≤ n` and
an odd reflection constant, there are a plaquette `q₀` and configurations `U, U'` agreeing on `S`,
whose reflections also agree on `S`, with different `Re trace` at `q₀`. The two are the all-identity
configuration and `cfgWitness` at a fixed axis link, which lies in neither half because the
reflection fixes it while `S` and `T` are disjoint.

DERIVED: `2` is the lower bound on the extent; `3` is the gauge group's matrix size. The two traces
compared in the proof are `3` for the identity and `-1` for `gNeg`, both computed. -/
theorem straddling_word_not_determined_by_halves [NeZero n] (hn : Even n) (h2 : 2 ≤ n)
    {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} (hc : ¬ Even c.val)
    (S T : Finset (Link d n)) (hST : Disjoint S T)
    (hSmap : ∀ l ∈ S, reflLink τ c l ∈ T) :
    ∃ (q₀ : Plaq d n) (U U' : Link d n → MassGap.SUN.SU 3),
      (∀ l ∈ S, U l = U' l)
      ∧ (∀ l ∈ S, reflConf τ c U l = reflConf τ c U' l)
      ∧ (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q₀ U : MassGap.SUN.SU 3)
            : Matrix (Fin 3) (Fin 3) ℂ)).re
          ≠ (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q₀ U' : MassGap.SUN.SU 3)
            : Matrix (Fin 3) (Fin 3) ℂ)).re := by
  classical
  obtain ⟨x, hne, -, -, hfix1, -⟩ :=
    odd_lag_straddling_plaq_two_fixed_axis_links (d := d) (n := n) hn h2 hν hc
  -- the fixed axis link is in neither half
  have hl0S : ((τ, x) : Link d n) ∉ S := by
    intro hmem
    have hT : ((τ, x) : Link d n) ∈ T := by
      have := hSmap _ hmem
      rwa [hfix1] at this
    exact (Finset.disjoint_left.mp hST) hmem hT
  have hlink : ∀ l ∈ S, l ≠ ((τ, x) : Link d n) := by
    intro l hl hcon
    exact hl0S (hcon ▸ hl)
  have hrefl : ∀ l ∈ S, reflLink τ c l ≠ ((τ, x) : Link d n) := by
    intro l hl hcon
    have hback := congrArg (reflLink τ c) hcon
    rw [reflLink_involutive τ c l, hfix1] at hback
    exact hlink l hl hback
  refine ⟨((τ, ν), x), (fun _ => 1), cfgWitness ((τ, x) : Link d n), ?_, ?_, ?_⟩
  · intro l hl
    exact (cfgWitness_of_ne (hlink l hl)).symm
  · intro l hl
    show (if l.1 = τ then (1 : MassGap.SUN.SU 3)⁻¹ else 1)
        = (if l.1 = τ then (cfgWitness ((τ, x) : Link d n) (reflLink τ c l))⁻¹
            else cfgWitness ((τ, x) : Link d n) (reflLink τ c l))
    rw [cfgWitness_of_ne (hrefl l hl)]
  · have hid : wilsonHol (bd (d := d) (n := n)) (((τ, ν), x) : Plaq d n)
        (fun _ => (1 : MassGap.SUN.SU 3)) = 1 := by
      simp [wilsonHol, bd]
    rw [hid, hol_cfgWitness hν hne, trace_gNeg]
    show (Matrix.trace ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re ≠ -1
    rw [Submonoid.coe_one, Matrix.trace_one]
    norm_num

/-- No `Φ : (S → SU 3) → (S → SU 3) → ℝ` represents the straddling word: for any such `Φ` there is a
plaquette whose `Re trace` is not `Φ (U|_S) ((reflConf τ c U)|_S)` at every `U`. Immediate from
`straddling_word_not_determined_by_halves`.

Scope: `Φ` is arbitrary, so this includes `Φ u v = κ + c * hsRe (X u) (X v)` with any constant and
rescaling. It depends only on where the fixed axis links sit, not on the paired form.

DERIVED: `2` is the lower bound on the extent; `3` is the gauge group's matrix size. -/
theorem no_half_function_for_straddling_word [NeZero n] (hn : Even n) (h2 : 2 ≤ n)
    {τ ν : Fin d} (hν : ν ≠ τ) {c : Fin n} (hc : ¬ Even c.val)
    (S T : Finset (Link d n)) (hST : Disjoint S T)
    (hSmap : ∀ l ∈ S, reflLink τ c l ∈ T)
    (Φ : (S → MassGap.SUN.SU 3) → (S → MassGap.SUN.SU 3) → ℝ) :
    ∃ q₀ : Plaq d n, ¬ ∀ U : Link d n → MassGap.SUN.SU 3,
      (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q₀ U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re
        = Φ (fun l : S => U (l : Link d n)) (fun l : S => reflConf τ c U (l : Link d n)) := by
  obtain ⟨q₀, U, U', hS, hΘS, hne⟩ :=
    straddling_word_not_determined_by_halves hn h2 hν hc S T hST hSmap
  refine ⟨q₀, ?_⟩
  intro h
  refine hne ?_
  rw [h U, h U']
  congr 1
  · funext l
    exact hS (l : Link d n) l.2
  · funext l
    exact hΘS (l : Link d n) l.2

end NotAHalfFunction

/-! ## An instance at `d = 4` -/

section NonVacuous

/-- **The hypotheses are satisfiable, at `d = 4` and `SU(3)`.**

`d = 4`, extent `4` (even), axis `0`, transverse direction `1`, reflection constant `1` (odd) is a
concrete instance of `straddling_word_not_paired_at_odd_lag`. So the refutation is about a case that
actually occurs on the four-dimensional lattice the development is built on, not a vacuous
quantification.

DERIVED: `4` is the problem's dimension and an even extent that admits an odd constant; `3` is
`SU(3)`; `0` and `1` are two distinct directions. -/
theorem straddling_not_paired_four_dim
    {K : Type} [Fintype K] {Nc : ℕ} (cf : K → ℝ) (hcf : ∀ k, 0 ≤ cf k)
    (X : K → (Link 4 4 → MassGap.SUN.SU 3) → Matrix (Fin Nc) (Fin Nc) ℂ) :
    ∃ q₀ : Plaq 4 4, ¬ ∀ U : Link 4 4 → MassGap.SUN.SU 3,
      (Matrix.trace ((wilsonHol (bd (d := 4) (n := 4)) q₀ U : MassGap.SUN.SU 3)
          : Matrix (Fin 3) (Fin 3) ℂ)).re
        = ∑ k, cf k * hsRe (X k U) (X k (reflConf (0 : Fin 4) (1 : Fin 4) U)) :=
  straddling_word_not_paired_at_odd_lag (by decide) (by norm_num)
    (by decide : (1 : Fin 4) ≠ (0 : Fin 4)) (by decide) cf hcf X

end NonVacuous

/-! ## The change of variables the reflection suggests, and why it is inert

`Reflect.isInvInvariant_probHaar` licenses substituting `g ↦ g⁻¹` on any link. On the fixed axis
links that is the one substitution the reflection's own dagger suggests. This file does not prove
that it commutes with `reflConf`, so `no_paired_after_equivariant_reparam` is never actually fed it;
what is proved is only that on this witness the substitution does nothing at all, because the witness
carries only self-inverse elements. -/

section InvChange

variable {d n : ℕ}

/-- The change of variables `g ↦ g⁻¹` on a chosen `Finset` of links, as a permutation of
configurations. It is its own inverse, which is what makes both `left_inv` and `right_inv` the same
computation.

DERIVED: no numeral occurs. -/
def invLink [NeZero n] {G : Type} [Group G] [DecidableEq (Link d n)] (R : Finset (Link d n)) :
    Equiv.Perm (Link d n → G) where
  toFun U := fun l => if l ∈ R then (U l)⁻¹ else U l
  invFun U := fun l => if l ∈ R then (U l)⁻¹ else U l
  left_inv := by intro U; funext l; by_cases h : l ∈ R <;> simp [h]
  right_inv := by intro U; funext l; by_cases h : l ∈ R <;> simp [h]

/-- `invLink R (cfgWitness l₀) = cfgWitness l₀` for any `R`: every link of the witness carries
either the identity or `gNeg`, and both are self-inverse.

Scope: this says the witness is blind to the substitution, not that the substitution cannot help.
Whether `invLink` commutes with `reflConf`, which is what
`no_paired_after_equivariant_reparam` would need, is not proved here.

DERIVED: no numeral occurs in the statement. -/
theorem invLink_cfgWitness [NeZero n] [DecidableEq (Link d n)] (R : Finset (Link d n))
    (l₀ : Link d n) : invLink R (cfgWitness l₀) = cfgWitness l₀ := by
  funext l
  show (if l ∈ R then (cfgWitness l₀ l)⁻¹ else cfgWitness l₀ l) = cfgWitness l₀ l
  by_cases hl : l = l₀
  · rw [hl, cfgWitness_at]
    by_cases hR : l₀ ∈ R
    · rw [if_pos hR, gNeg_inv]
    · rw [if_neg hR]
  · rw [cfgWitness_of_ne hl]
    by_cases hR : l ∈ R
    · rw [if_pos hR, inv_one]
    · rw [if_neg hR]

end InvChange

/-! ## Negative controls

The obstruction argument must be capable of not firing, or it proves nothing about this geometry in
particular. Both controls below are on the same machinery. -/

section NegControls

variable {d n : ℕ}

/-- `0 ≤ (trace (X U₀ * (X (Θ U₀))ᴴ)).re` at any reflection-fixed `U₀`: on a word that is a paired
form, the quantity the refutations look at is nonnegative, so
`no_paired_word_of_neg_at_fixed` has no hypothesis to consume. The obstruction detects the absence
of a paired form, not the presence of a reflection.

DERIVED: the one numeral is `0`, the lower bound asserted. -/
theorem negctl_paired_word_is_nonneg {γ : Type} (Θ : γ → γ) {U₀ : γ} (hfix : Θ U₀ = U₀)
    {N : ℕ} (X : γ → Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (Matrix.trace (X U₀ * Matrix.conjTranspose (X (Θ U₀)))).re := by
  rw [hfix]
  exact hsRe_self_nonneg (X U₀)

/-- The all-identity configuration is reflection-fixed at every `τ` and `c`, and every plaquette
has holonomy `1` there with `Re trace = 3`. So the negative value the obstructions use comes from
`gNeg` sitting on a fixed axis link, not from the straddling geometry alone.

DERIVED: `3` is the matrix size and, equal to it, the value of `Re trace` at the identity; `1` is
the group identity carried on every link. -/
theorem negctl_identity_config [NeZero n] (τ : Fin d) (c : Fin n) (q : Plaq d n) :
    reflConf τ c (fun _ : Link d n => (1 : MassGap.SUN.SU 3)) = (fun _ => 1)
      ∧ (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q (fun _ => (1 : MassGap.SUN.SU 3))
          : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re = 3 := by
  constructor
  · funext l
    show (if l.1 = τ then (1 : MassGap.SUN.SU 3)⁻¹ else 1) = 1
    simp
  · have hone : wilsonHol (bd (d := d) (n := n)) q (fun _ => (1 : MassGap.SUN.SU 3)) = 1 := by
      simp [wilsonHol, bd]
    rw [hone]
    show (Matrix.trace ((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)).re = 3
    rw [Submonoid.coe_one, Matrix.trace_one]
    norm_num

end NegControls

/-! ## The crossing-link integration, without representation theory

The obstruction above says the straddling weight is not positive pointwise. Osterwalder and Seiler
recover positivity by integrating the fixed axis links out, and do it with Schur orthogonality of
matrix coefficients: the crossing integral becomes a Gram matrix. This section does the same
integration and needs no irreducible representations at all.

## The mechanism

Read the straddling weight as a gauge transformation. The links of the reflection plane act on the
transverse links beside it exactly as a gauge field acts on link variables,

    (F^G)_x = G_x · F_x · G_{x+ν̂}⁻¹,

so the straddling plaquette word `G_x · F₊ · G_{x+ν̂}⁻¹ · F₋⁻¹` is `Re tr ((F₊^G) · F₋⁻¹)` — the same
`hsRe` cross form the Wilson weight already has, with the plane links absorbed into one argument.
The crossing weight is therefore `K (act g x) y` with `K a b = exp (β · ⟨a, b⟩)`, and `K` has two
properties that are elementary here:

* it is a positive-semidefinite kernel — `CharacterExpansion.wilson_kernel_nonneg`, proved from the
  coordinate expansion with no representation theory; and
* it is gauge-invariant, `K (act g a) (act g b) = K a b` — `hsRe_conj`, which is cyclicity of the
  trace.

Those two are enough. Averaging over the plane links is `P a = ∫ a(·^g) dg`, which lands in the
gauge-invariant observables (`gaugeAvg_act`), and the identity proved is

    ∫dg ⟨a, K (act g ·) ·⟩  =  ⟨P a, K (P a)⟩  ≥  0.

The proof does not run through idempotence of `P` or commutation of operators — neither is proved
here. It runs through `integral_gaugeAvg_mul_invariant`: the partner `x ↦ ∫ (P a)(y) K x y` is itself
gauge-invariant, and against an invariant partner `P` may be moved from one factor to the other.

`crossing_gauge_integral_eq` is the identity and `crossing_gauge_pairing_nonneg` the conclusion. The
identity is where the invariances of Haar are spent: measure-preservation of the gauge action on the
half, and right invariance of the plane measure — which for `probHaar` is
`CompactGauge.isMulRightInvariant_probHaar`.

## What this replaces

Schur orthogonality, and therefore Peter-Weyl, for this application. Mathlib v4.31 has neither:
`RepresentationTheory.Character.char_orthonormal` is stated for a finite group, and the library has
no compact-group representation theory.

`MassGap.HaarMoments` builds part of the tower by hand for `SU(2)`, by invariance under two explicit
group elements, and gets the fundamental's second moment exactly
(`haar_su2_second_moment`, `∫ U_ij conj(U_kl) = ½ δ δ`). That is one irreducible representation at
one order. The crossing weight `exp(β · Re tr W)` reaches every order in the plane links — its
order-`k` term is degree `k` in their coordinates — so the moment route needs the balanced moments
at all orders, and `HaarMoments` reaches order four only as bounds
(`haar_su2_fourth_moment_diag_bounds`), with its own docstring naming the balanced fourth moment the
remaining deep piece. Truncating at the second moment is a strong-coupling expansion of the weight,
not the weight.

The projection argument below needs no moment of any order: it never expands in the plane links at
all.

## What it does not do

It is stated for an abstract half `Ω`, plane group `Γ` and invariant kernel `K`. Pointing it at the
Wilson lattice needs the odd-lag action split — that at a link-reflection plane every plaquette reads
one half, the other half, or straddles; that the straddling ones are exactly the gauge-transformed
cross form above, aggregated over all of them and over both fixed planes at once (which wants `X`
block-diagonal, and the direct-sum form of `hsRe_conj` that goes with it); and that the reflected
half's weight is the same function of the transported variables. `ActionSplit` does that work for the
even-lag case in two thousand lines; the odd-lag case is not done here. So this is the crossing
integration, not the discharge of the axiom. -/

section Crossing

variable {Γ Ω : Type} [Group Γ] [MeasurableSpace Γ] [MeasurableSpace Ω]

/-- The gauge average `gaugeAvg lam act a x = ∫ g, a (act g x) ∂lam`: the plane links integrated
out of an observable of the half.

DERIVED: no numeral occurs. -/
noncomputable def gaugeAvg (lam : Measure Γ) (act : Γ → Ω → Ω) (a : Ω → ℝ) : Ω → ℝ :=
  fun x => ∫ g, a (act g x) ∂lam

theorem measurable_gaugeAvg (lam : Measure Γ) [SFinite lam] {act : Γ → Ω → Ω}
    (hactm : Measurable (Function.uncurry act)) {a : Ω → ℝ} (ham : Measurable a) :
    Measurable (gaugeAvg lam act a) :=
  ((ham.comp (hactm.comp measurable_swap)).stronglyMeasurable.integral_prod_right').measurable

theorem abs_gaugeAvg_le (lam : Measure Γ) [IsProbabilityMeasure lam] {act : Γ → Ω → Ω}
    {a : Ω → ℝ} {C : ℝ} (hC : ∀ x, |a x| ≤ C) (x : Ω) : |gaugeAvg lam act a x| ≤ C := by
  have hb : ∀ᵐ g ∂lam, ‖a (act g x)‖ ≤ C :=
    Filter.Eventually.of_forall (fun g => by simpa [Real.norm_eq_abs] using hC (act g x))
  have h := norm_integral_le_of_norm_le_const hb
  simpa [gaugeAvg, Real.norm_eq_abs, probReal_univ] using h

/-- `gaugeAvg lam act a (act h x) = gaugeAvg lam act a x`: the gauge average is invariant under the
action. The proof rewrites `act h (act g x)` as `act (h * g) x` and uses right invariance of `lam`.

DERIVED: no numeral occurs in the statement. -/
theorem gaugeAvg_act (lam : Measure Γ) [MeasurableMul Γ] [IsProbabilityMeasure lam]
    [lam.IsMulRightInvariant]
    {act : Γ → Ω → Ω} (hactm : Measurable (Function.uncurry act))
    (hmul : ∀ (g h : Γ) (x : Ω), act h (act g x) = act (h * g) x)
    {a : Ω → ℝ} (ham : Measurable a) (h : Γ) (x : Ω) :
    gaugeAvg lam act a (act h x) = gaugeAvg lam act a x := by
  have hmeas : Measurable (fun g : Γ => a (act g x)) :=
    ham.comp (hactm.comp (measurable_id.prodMk measurable_const))
  have hshift := MassGap.ActionSplit.integral_comp_of_mp
    (measurePreserving_mul_right lam h) hmeas
  show (∫ g, a (act g (act h x)) ∂lam) = ∫ g, a (act g x) ∂lam
  simp only [hmul]
  exact hshift

/-- `∫ y, f y * K (act g x) y = ∫ y, f (act g y) * K x y`: a gauge on the kernel's first argument
moves onto the integration variable. Uses measure-preservation of `act g` on `nu` and invariance of
`K` under the action.

DERIVED: no numeral occurs in the statement. -/
theorem kernel_arg_shift (nu : Measure Ω) {act : Γ → Ω → Ω}
    (hmp : ∀ g, MeasurePreserving (act g) nu nu)
    {K : Ω → Ω → ℝ} (hKsec : ∀ x : Ω, Measurable (K x))
    (hKinv : ∀ (g : Γ) (x y : Ω), K (act g x) (act g y) = K x y)
    {f : Ω → ℝ} (hfm : Measurable f) (g : Γ) (x : Ω) :
    (∫ y, f y * K (act g x) y ∂nu) = ∫ y, f (act g y) * K x y ∂nu := by
  have hF : Measurable (fun y => f y * K (act g x) y) := hfm.mul (hKsec (act g x))
  have hc := MassGap.ActionSplit.integral_comp_of_mp (hmp g) hF
  rw [← hc]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  show f (act g y) * K (act g x) (act g y) = f (act g y) * K x y
  rw [hKinv]

/-- `∫ x, gaugeAvg lam act a x * H x = ∫ x, a x * H x` when `H` is invariant under the action: the
gauge average may be dropped from one factor against an invariant partner.

DERIVED: the one numeral is `0`, the lower bound on the constant `Ca` bounding `a`, which the
integrability estimates use. -/
theorem integral_gaugeAvg_mul_invariant (lam : Measure Γ) [IsProbabilityMeasure lam]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    {act : Γ → Ω → Ω} (hactm : Measurable (Function.uncurry act))
    (hmp : ∀ g, MeasurePreserving (act g) nu nu)
    {a : Ω → ℝ} (ham : Measurable a) {Ca : ℝ} (hCa : 0 ≤ Ca) (hab : ∀ x, |a x| ≤ Ca)
    {H : Ω → ℝ} (hHm : Measurable H) {CH : ℝ} (hHb : ∀ x, |H x| ≤ CH)
    (hHinv : ∀ (g : Γ) (x : Ω), H (act g x) = H x) :
    (∫ x, gaugeAvg lam act a x * H x ∂nu) = ∫ x, a x * H x ∂nu := by
  have hpm : Measurable (fun p : Ω × Γ => a (act p.2 p.1) * H p.1) :=
    (ham.comp (hactm.comp measurable_swap)).mul (hHm.comp measurable_fst)
  have hpb : ∀ p : Ω × Γ, |a (act p.2 p.1) * H p.1| ≤ Ca * CH := by
    intro p
    rw [abs_mul]
    exact mul_le_mul (hab _) (hHb _) (abs_nonneg _) hCa
  have hint : Integrable
      (Function.uncurry (fun (x : Ω) (g : Γ) => a (act g x) * H x)) (nu.prod lam) :=
    MassGap.ActionSplit.integrable_of_bounded (nu.prod lam) hpm hpb
  have hL : (∫ x, gaugeAvg lam act a x * H x ∂nu)
      = ∫ x, (∫ g, a (act g x) * H x ∂lam) ∂nu := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show gaugeAvg lam act a x * H x = ∫ g, a (act g x) * H x ∂lam
    rw [integral_mul_const]
    rfl
  rw [hL, integral_integral_swap hint]
  have hfib : ∀ g : Γ, (∫ x, a (act g x) * H x ∂nu) = ∫ x, a x * H x ∂nu := by
    intro g
    have hF : Measurable (fun x => a x * H x) := ham.mul hHm
    have hc := MassGap.ActionSplit.integral_comp_of_mp (hmp g) hF
    rw [← hc]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show a (act g x) * H x = a (act g x) * H (act g x)
    rw [hHinv]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfib), integral_const]
  simp

/-- The crossing-link integration as an identity:

    ∫ g ∫ x ∫ y, a x * a y * K (act g x) y  =  ∫ x ∫ y, (P a) x * (P a) y * K x y

with `P = gaugeAvg lam act`. Integrating the plane links out replaces the observable by its gauge
average on both factors. The proof builds the invariant partner `x ↦ ∫ y, (P a) y * K x y`, uses
`kernel_arg_shift` to move the gauge, and `integral_gaugeAvg_mul_invariant` to move the average
across. It does not go through idempotence of `P` or commutation of operators, neither of which is
proved here.

DERIVED: the one numeral is `0`, the lower bound on the constant `Ca` bounding `a`. The bounds `CK`
and `Ca` are the caller's. -/
theorem crossing_gauge_integral_eq
    (lam : Measure Γ) [MeasurableMul Γ] [IsProbabilityMeasure lam] [lam.IsMulRightInvariant]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    {act : Γ → Ω → Ω} (hactm : Measurable (Function.uncurry act))
    (hmp : ∀ g, MeasurePreserving (act g) nu nu)
    (hmul : ∀ (g h : Γ) (x : Ω), act h (act g x) = act (h * g) x)
    {K : Ω → Ω → ℝ} (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2))
    {CK : ℝ} (hKb : ∀ x y, |K x y| ≤ CK)
    (hKinv : ∀ (g : Γ) (x y : Ω), K (act g x) (act g y) = K x y)
    {a : Ω → ℝ} (ham : Measurable a) {Ca : ℝ} (hCa : 0 ≤ Ca) (hab : ∀ x, |a x| ≤ Ca) :
    (∫ g, (∫ x, (∫ y, a x * a y * K (act g x) y ∂nu) ∂nu) ∂lam)
      = ∫ x, (∫ y, gaugeAvg lam act a x * gaugeAvg lam act a y * K x y ∂nu) ∂nu := by
  classical
  have hKsec : ∀ x : Ω, Measurable (K x) := fun x =>
    hKm.comp (measurable_const.prodMk measurable_id)
  have hbm : Measurable (gaugeAvg lam act a) := measurable_gaugeAvg lam hactm ham
  have hbb : ∀ x, |gaugeAvg lam act a x| ≤ Ca := fun x => abs_gaugeAvg_le lam hab x
  -- the invariant partner `H x = ∫ y, (P a) y * K x y`
  have hHm : Measurable (fun x => ∫ y, gaugeAvg lam act a y * K x y ∂nu) := by
    have hq : Measurable (fun p : Ω × Ω => gaugeAvg lam act a p.2 * K p.1 p.2) :=
      (hbm.comp measurable_snd).mul hKm
    exact (hq.stronglyMeasurable.integral_prod_right').measurable
  have hHb : ∀ x, |∫ y, gaugeAvg lam act a y * K x y ∂nu| ≤ Ca * CK := by
    intro x
    have hb2 : ∀ᵐ y ∂nu, ‖gaugeAvg lam act a y * K x y‖ ≤ Ca * CK :=
      Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbb y) (hKb x y) (abs_nonneg _) hCa)
    have h := norm_integral_le_of_norm_le_const hb2
    simpa [Real.norm_eq_abs, probReal_univ] using h
  have hHinv : ∀ (g : Γ) (x : Ω),
      (∫ y, gaugeAvg lam act a y * K (act g x) y ∂nu)
        = ∫ y, gaugeAvg lam act a y * K x y ∂nu := by
    intro g x
    rw [kernel_arg_shift nu hmp hKsec hKinv hbm g x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show gaugeAvg lam act a (act g y) * K x y = gaugeAvg lam act a y * K x y
    rw [gaugeAvg_act lam hactm hmul ham g y]
  -- Step 1: push the gauge off the kernel's first argument
  have step1 : ∀ g : Γ, (∫ x, (∫ y, a x * a y * K (act g x) y ∂nu) ∂nu)
      = ∫ x, a x * (∫ y, a (act g y) * K x y ∂nu) ∂nu := by
    intro g
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (∫ y, a x * a y * K (act g x) y ∂nu) = a x * ∫ y, a (act g y) * K x y ∂nu
    have hrw : (∫ y, a x * a y * K (act g x) y ∂nu)
        = a x * ∫ y, a y * K (act g x) y ∂nu := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      show a x * a y * K (act g x) y = a x * (a y * K (act g x) y)
      ring
    rw [hrw, kernel_arg_shift nu hmp hKsec hKinv ham g x]
  rw [integral_congr_ae (Filter.Eventually.of_forall step1)]
  -- Step 2: swap the plane integral past the two half integrals
  have hQm : Measurable (fun p : Γ × Ω => ∫ y, a (act p.1 y) * K p.2 y ∂nu) := by
    have hq : Measurable (fun p : (Γ × Ω) × Ω => a (act p.1.1 p.2) * K p.1.2 p.2) :=
      (ham.comp (hactm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul
        (hKm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact (hq.stronglyMeasurable.integral_prod_right').measurable
  have hQb : ∀ p : Γ × Ω, |∫ y, a (act p.1 y) * K p.2 y ∂nu| ≤ Ca * CK := by
    intro p
    have hb2 : ∀ᵐ y ∂nu, ‖a (act p.1 y) * K p.2 y‖ ≤ Ca * CK :=
      Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hab _) (hKb _ _) (abs_nonneg _) hCa)
    have h := norm_integral_le_of_norm_le_const hb2
    simpa [Real.norm_eq_abs, probReal_univ] using h
  have hint1 : Integrable (Function.uncurry
      (fun (g : Γ) (x : Ω) => a x * (∫ y, a (act g y) * K x y ∂nu))) (lam.prod nu) := by
    refine MassGap.ActionSplit.integrable_of_bounded (lam.prod nu)
      ((ham.comp measurable_snd).mul hQm) (C := Ca * (Ca * CK)) (fun p => ?_)
    show |a p.2 * (∫ y, a (act p.1 y) * K p.2 y ∂nu)| ≤ Ca * (Ca * CK)
    rw [abs_mul]
    exact mul_le_mul (hab _) (hQb p) (abs_nonneg _) hCa
  rw [integral_integral_swap hint1]
  -- Step 3: the inner plane integral IS the gauge average
  have hA : ∀ x : Ω, (∫ g, a x * (∫ y, a (act g y) * K x y ∂nu) ∂lam)
      = a x * ∫ y, gaugeAvg lam act a y * K x y ∂nu := by
    intro x
    rw [integral_const_mul]
    congr 1
    have hint2 : Integrable (Function.uncurry
        (fun (g : Γ) (y : Ω) => a (act g y) * K x y)) (lam.prod nu) := by
      refine MassGap.ActionSplit.integrable_of_bounded (lam.prod nu)
        ((ham.comp hactm).mul ((hKsec x).comp measurable_snd)) (C := Ca * CK) (fun p => ?_)
      show |a (act p.1 p.2) * K x p.2| ≤ Ca * CK
      rw [abs_mul]
      exact mul_le_mul (hab _) (hKb _ _) (abs_nonneg _) hCa
    rw [integral_integral_swap hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show (∫ g, a (act g y) * K x y ∂lam) = gaugeAvg lam act a y * K x y
    rw [integral_mul_const]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hA)]
  -- Step 4: the right-hand side pairs `P a` against the same invariant partner
  have hB : ∀ x : Ω, (∫ y, gaugeAvg lam act a x * gaugeAvg lam act a y * K x y ∂nu)
      = gaugeAvg lam act a x * ∫ y, gaugeAvg lam act a y * K x y ∂nu := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show gaugeAvg lam act a x * gaugeAvg lam act a y * K x y
        = gaugeAvg lam act a x * (gaugeAvg lam act a y * K x y)
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hB)]
  -- Step 5: and the projection moves across an invariant partner
  exact (integral_gaugeAvg_mul_invariant lam nu hactm hmp ham hCa hab hHm hHb hHinv).symm

/-- `0 ≤ ∫ g ∫ x ∫ y, a x * a y * K (act g x) y`, given that `K` is invariant under the action and
positive-semidefinite in the integral sense (`hPSD`). `crossing_gauge_integral_eq` followed by
`hPSD` at the gauge average.

Scope: `hPSD` is a hypothesis here; `wilson_kernel_integral_psd` discharges it for the Wilson
kernel. It cannot be dropped —
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` refutes it for the `SU 3` Wilson kernel at
`β < 0` on two explicit group elements.

DERIVED: `0` is the lower bound on `Ca`, the lower bound in `hPSD`, and the lower bound
asserted. -/
theorem crossing_gauge_pairing_nonneg
    (lam : Measure Γ) [MeasurableMul Γ] [IsProbabilityMeasure lam] [lam.IsMulRightInvariant]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    {act : Γ → Ω → Ω} (hactm : Measurable (Function.uncurry act))
    (hmp : ∀ g, MeasurePreserving (act g) nu nu)
    (hmul : ∀ (g h : Γ) (x : Ω), act h (act g x) = act (h * g) x)
    {K : Ω → Ω → ℝ} (hKm : Measurable (fun p : Ω × Ω => K p.1 p.2))
    {CK : ℝ} (hKb : ∀ x y, |K x y| ≤ CK)
    (hKinv : ∀ (g : Γ) (x y : Ω), K (act g x) (act g y) = K x y)
    {a : Ω → ℝ} (ham : Measurable a) {Ca : ℝ} (hCa : 0 ≤ Ca) (hab : ∀ x, |a x| ≤ Ca)
    (hPSD : ∀ f : Ω → ℝ, Measurable f → (∀ x, |f x| ≤ Ca) →
      0 ≤ ∫ x, (∫ y, f x * f y * K x y ∂nu) ∂nu) :
    0 ≤ ∫ g, (∫ x, (∫ y, a x * a y * K (act g x) y ∂nu) ∂nu) ∂lam := by
  rw [crossing_gauge_integral_eq lam nu hactm hmp hmul hKm hKb hKinv ham hCa hab]
  exact hPSD _ (measurable_gaugeAvg lam hactm ham) (fun x => abs_gaugeAvg_le lam hab x)

end Crossing

/-! ## The kernel really is positive-semidefinite, in the integral sense

`crossing_gauge_pairing_nonneg` takes positive-semidefiniteness of the crossing kernel as a
hypothesis, and that hypothesis is exactly where the classical argument reaches for Peter-Weyl: "the
class function `exp(β Re tr g)` is positive-definite" is the statement whose usual proof expands it
in irreducible characters. So leaving it as a hypothesis would leave the representation theory
hidden rather than removed.

It is proved here instead, from the coordinate expansion, for the `SU(N)` Wilson weight against any
probability measure: `wilson_kernel_integral_psd`. The proof is `hasSum_wilsonWeight_paired` order by
order, `MeasureTheory.integral_prod_mul` turning each order into a square, and dominated convergence
summing them — the same three steps `CharacterExpansion.crossweight_pairing_nonneg` uses, on a
product measure instead of a reflection.

`wilson_crossing_pairing_nonneg` is the two halves composed: the crossing-link integration for a
cross weight of the Wilson functional form, with positivity proved rather than assumed. It is stated
over an abstract half `Ω`, plane group `Γ` and word `X`; nothing here ties `X` to `wilsonHol`, ties
`Γ` to the fixed axis links, or discharges its invariance hypothesis on the lattice. -/

section WilsonPSD

/-- `|hsRe A B| ≤ Fintype.card (Coord N)` when every real coordinate of `A` and of `B` has absolute
value at most one, which holds for every `SU N` element by `SUN.unitary_entry_norm_le_one`. Each of
the `Fintype.card (Coord N)` terms of `hsRe_eq_sum` is bounded by one.

DERIVED: `1` is the bound on each coordinate, so each product of two coordinates is bounded by `1`
and the sum by the coordinate count `Fintype.card (Coord N)`, which is `2 * N ^ 2`. That count is
read off the type, not chosen. -/
theorem abs_hsRe_le_card {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ p : Coord N, |coord p A| ≤ 1) (hB : ∀ p : Coord N, |coord p B| ≤ 1) :
    |hsRe A B| ≤ (Fintype.card (Coord N) : ℝ) := by
  rw [hsRe_eq_sum]
  calc |∑ q : Coord N, coord q A * coord q B|
      ≤ ∑ q : Coord N, |coord q A * coord q B| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Coord N, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [abs_mul]
        exact (mul_le_mul (hA q) (hB q) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = (Fintype.card (Coord N) : ℝ) := by simp

/-- `0 ≤ ∫ x ∫ y, f x * f y * exp (β * hsRe (X x) (X y))` against any probability measure, for
`0 ≤ β`, bounded measurable `f`, and a matrix-valued `X` whose real coordinates are bounded by one.
The proof takes `hasSum_wilsonWeight_paired` order by order, turns each order into a square by
`MeasureTheory.integral_prod_mul`, and sums by dominated convergence. This is the integral form of
`CharacterExpansion.wilson_kernel_nonneg` and the hypothesis `crossing_gauge_pairing_nonneg`
consumes.

Scope: `NegControl.su3_kernel_nonneg_iff` shows `0 ≤ β` cannot be dropped.

DERIVED: `0` is the lower bound on `β`, on the bound `C` for `f`, and the lower bound asserted; `1`
is the bound on each coordinate of `X`, which holds for unitary matrices. -/
theorem wilson_kernel_integral_psd {γ : Type} [MeasurableSpace γ] (m : Measure γ)
    [IsProbabilityMeasure m] {Nc : ℕ} (X : γ → Matrix (Fin Nc) (Fin Nc) ℂ)
    (hXm : ∀ p : Coord Nc, Measurable (fun v => coord p (X v)))
    (hXb : ∀ (p : Coord Nc) (v : γ), |coord p (X v)| ≤ 1)
    (f : γ → ℝ) (hfm : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hfb : ∀ v, |f v| ≤ C)
    {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ x, (∫ y, f x * f y * Real.exp (β * hsRe (X x) (X y)) ∂m) ∂m := by
  classical
  have hαm : ∀ {k : ℕ} (α : Fin k → Coord Nc), Measurable (halfFun f X α) :=
    fun α => measurable_halfFun hfm hXm α
  have hαb : ∀ {k : ℕ} (α : Fin k → Coord Nc) (v : γ), |halfFun f X α v| ≤ C :=
    fun α v => abs_halfFun_le hC0 hfb hXb α v
  -- the full integrand is bounded and measurable, so the double integral is a product integral
  have hhsm : Measurable (fun p : γ × γ => hsRe (X p.1) (X p.2)) := by
    have hrw : (fun p : γ × γ => hsRe (X p.1) (X p.2))
        = fun p : γ × γ => ∑ q : Coord Nc, coord q (X p.1) * coord q (X p.2) := by
      funext p
      exact hsRe_eq_sum _ _
    rw [hrw]
    exact Finset.measurable_sum _ (fun q _ =>
      ((hXm q).comp measurable_fst).mul ((hXm q).comp measurable_snd))
  have hFm : Measurable
      (fun p : γ × γ => f p.1 * f p.2 * Real.exp (β * hsRe (X p.1) (X p.2))) :=
    ((hfm.comp measurable_fst).mul (hfm.comp measurable_snd)).mul
      ((measurable_const.mul hhsm).exp)
  have hFb : ∀ p : γ × γ, |f p.1 * f p.2 * Real.exp (β * hsRe (X p.1) (X p.2))|
      ≤ C * C * Real.exp (β * (Fintype.card (Coord Nc) : ℝ)) := by
    intro p
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    refine mul_le_mul (mul_le_mul (hfb _) (hfb _) (abs_nonneg _) hC0) ?_
      (Real.exp_nonneg _) (mul_nonneg hC0 hC0)
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hβ)
    exact (abs_le.mp (abs_hsRe_le_card (fun q => hXb q p.1) (fun q => hXb q p.2))).2
  have hFint : Integrable
      (fun p : γ × γ => f p.1 * f p.2 * Real.exp (β * hsRe (X p.1) (X p.2))) (m.prod m) :=
    MassGap.ActionSplit.integrable_of_bounded (m.prod m) hFm hFb
  rw [← integral_prod _ hFint]
  -- the order-`k` term of the expansion, on the product space
  set Fk : ℕ → γ × γ → ℝ := fun k p => wilsonCoef β k *
    ∑ α : Fin k → Coord Nc, halfFun f X α p.1 * halfFun f X α p.2 with hFk
  have hFkm : ∀ k, Measurable (Fk k) := by
    intro k
    rw [hFk]
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun α _ =>
      ((hαm α).comp measurable_fst).mul ((hαm α).comp measurable_snd))
  have hint : ∀ {k : ℕ} (α : Fin k → Coord Nc), Integrable
      (fun p : γ × γ => halfFun f X α p.1 * halfFun f X α p.2) (m.prod m) := by
    intro k α
    refine MassGap.ActionSplit.integrable_of_bounded (m.prod m)
      (((hαm α).comp measurable_fst).mul ((hαm α).comp measurable_snd))
      (C := C * C) (fun p => ?_)
    rw [abs_mul]
    exact mul_le_mul (hαb α _) (hαb α _) (abs_nonneg _) hC0
  -- each order integrates to a nonnegative number: a nonnegative coefficient times squares
  have hFknn : ∀ k, 0 ≤ ∫ p, Fk k p ∂(m.prod m) := by
    intro k
    have hsplit : (∫ p, Fk k p ∂(m.prod m))
        = wilsonCoef β k * ∑ α : Fin k → Coord Nc,
            ∫ p : γ × γ, halfFun f X α p.1 * halfFun f X α p.2 ∂(m.prod m) := by
      rw [hFk]
      rw [integral_const_mul, integral_finset_sum _ (fun α _ => hint α)]
    rw [hsplit]
    refine mul_nonneg (wilsonCoef_nonneg hβ k) (Finset.sum_nonneg (fun α _ => ?_))
    rw [integral_prod_mul]
    exact mul_self_nonneg _
  -- the pointwise expansion of the integrand
  have hlim : ∀ p : γ × γ, HasSum (fun k => Fk k p)
      (f p.1 * f p.2 * Real.exp (β * hsRe (X p.1) (X p.2))) := by
    intro p
    have hbase := (hasSum_wilsonWeight_paired (N := Nc) β (X p.1) (X p.2)).mul_left
      (f p.1 * f p.2)
    have heq : (fun k : ℕ => (f p.1 * f p.2) *
        (wilsonCoef β k * ∑ α : Fin k → Coord Nc, mono α (X p.1) * mono α (X p.2)))
        = fun k : ℕ => Fk k p := by
      funext k
      rw [hFk]
      simp only [halfFun]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    rw [heq] at hbase
    exact hbase
  -- dominated convergence, with a bound independent of the point
  have hcard : ∀ k : ℕ,
      (Finset.univ : Finset (Fin k → Coord Nc)).card = (Fintype.card (Coord Nc)) ^ k := by
    intro k
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hbd : ∀ (k : ℕ) (p : γ × γ),
      ‖Fk k p‖ ≤ C * C * (((Fintype.card (Coord Nc) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)) := by
    intro k p
    rw [Real.norm_eq_abs, hFk]
    simp only
    rw [abs_mul, abs_of_nonneg (wilsonCoef_nonneg hβ k)]
    have hs : |∑ α : Fin k → Coord Nc, halfFun f X α p.1 * halfFun f X α p.2|
        ≤ ((Fintype.card (Coord Nc) : ℝ) ^ k) * (C * C) := by
      calc |∑ α : Fin k → Coord Nc, halfFun f X α p.1 * halfFun f X α p.2|
          ≤ ∑ α : Fin k → Coord Nc, |halfFun f X α p.1 * halfFun f X α p.2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _α : Fin k → Coord Nc, C * C := by
            refine Finset.sum_le_sum (fun α _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (hαb α _) (hαb α _) (abs_nonneg _) hC0
        _ = ((Fintype.card (Coord Nc) : ℝ) ^ k) * (C * C) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard k]
            push_cast
            ring
    calc wilsonCoef β k * |∑ α : Fin k → Coord Nc, halfFun f X α p.1 * halfFun f X α p.2|
        ≤ wilsonCoef β k * (((Fintype.card (Coord Nc) : ℝ) ^ k) * (C * C)) :=
          mul_le_mul_of_nonneg_left hs (wilsonCoef_nonneg hβ k)
      _ = C * C * (((Fintype.card (Coord Nc) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)) := by
          rw [wilsonCoef, mul_pow]
          have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
            exact_mod_cast Nat.factorial_pos k
          field_simp
  have hsummable : Summable
      (fun k : ℕ => C * C * (((Fintype.card (Coord Nc) : ℝ) * β) ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial ((Fintype.card (Coord Nc) : ℝ) * β)).mul_left (C * C)
  have hdct := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := m.prod m) (F := Fk)
    (fun k (_ : γ × γ) =>
      C * C * (((Fintype.card (Coord Nc) : ℝ) * β) ^ k / (Nat.factorial k : ℝ)))
    (fun k => (hFkm k).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (fun p => hbd k p))
    (Filter.Eventually.of_forall (fun _ => hsummable))
    (integrable_const _)
    (Filter.Eventually.of_forall hlim)
  rw [← hdct.tsum_eq]
  exact tsum_nonneg hFknn

end WilsonPSD

/-! ## The crossing-link integration for the actual Wilson weight -/

section WilsonCrossing

variable {Γ Ω : Type} [Group Γ] [MeasurableSpace Γ] [MeasurableSpace Ω]

/-- `0 ≤ ∫ g ∫ x ∫ y, a x * a y * exp (β * hsRe (X (act g x)) (X y))`: the crossing-link
integration for a cross weight of the Wilson functional form, with positivity proved rather than
assumed. `crossing_gauge_pairing_nonneg` at `K x y = exp (β * hsRe (X x) (X y))`, whose
positive-semidefiniteness comes from `wilson_kernel_integral_psd` and whose invariance is the
hypothesis `hXinv`.

Scope: stated over an abstract half `Ω`, plane group `Γ` and word `X`. Nothing here ties `X` to
`wilsonHol` or discharges `hXinv` on the lattice.

DERIVED: `0` is the lower bound on `β`, on the bound `Ca` for `a`, and the lower bound asserted;
`1` is the bound on each coordinate of `X`, which holds for unitary matrices. -/
theorem wilson_crossing_pairing_nonneg
    (lam : Measure Γ) [MeasurableMul Γ] [IsProbabilityMeasure lam] [lam.IsMulRightInvariant]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    {act : Γ → Ω → Ω} (hactm : Measurable (Function.uncurry act))
    (hmp : ∀ g, MeasurePreserving (act g) nu nu)
    (hmul : ∀ (g h : Γ) (x : Ω), act h (act g x) = act (h * g) x)
    {Nc : ℕ} (X : Ω → Matrix (Fin Nc) (Fin Nc) ℂ)
    (hXm : ∀ p : Coord Nc, Measurable (fun v => coord p (X v)))
    (hXb : ∀ (p : Coord Nc) (v : Ω), |coord p (X v)| ≤ 1)
    (hXinv : ∀ (g : Γ) (x y : Ω), hsRe (X (act g x)) (X (act g y)) = hsRe (X x) (X y))
    {a : Ω → ℝ} (ham : Measurable a) {Ca : ℝ} (hCa : 0 ≤ Ca) (hab : ∀ x, |a x| ≤ Ca)
    {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ g, (∫ x, (∫ y, a x * a y
        * Real.exp (β * hsRe (X (act g x)) (X y)) ∂nu) ∂nu) ∂lam := by
  have hhsm : Measurable (fun p : Ω × Ω => hsRe (X p.1) (X p.2)) := by
    have hrw : (fun p : Ω × Ω => hsRe (X p.1) (X p.2))
        = fun p : Ω × Ω => ∑ q : Coord Nc, coord q (X p.1) * coord q (X p.2) := by
      funext p
      exact hsRe_eq_sum _ _
    rw [hrw]
    exact Finset.measurable_sum _ (fun q _ =>
      ((hXm q).comp measurable_fst).mul ((hXm q).comp measurable_snd))
  refine crossing_gauge_pairing_nonneg lam nu hactm hmp hmul
    (K := fun x y => Real.exp (β * hsRe (X x) (X y)))
    ((measurable_const.mul hhsm).exp)
    (CK := Real.exp (β * (Fintype.card (Coord Nc) : ℝ))) (fun x y => ?_)
    (fun g x y => by rw [hXinv]) ham hCa hab (fun f hfm hfb => ?_)
  · rw [abs_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hβ)
    exact (abs_le.mp (abs_hsRe_le_card (fun q => hXb q x) (fun q => hXb q y))).2
  · exact wilson_kernel_integral_psd nu X hXm hXb f hfm hCa hfb hβ

end WilsonCrossing


/-! ## The Wilson cross form really is gauge-invariant

The abstract theorem above is worth nothing if its invariance hypothesis is empty. It is not: the
Wilson cross form `hsRe` is invariant under the gauge action of the plane links, by cyclicity of the
trace, and that is the one property of the straddling geometry the crossing integration consumes. -/

section GaugeInvariance

variable {N : ℕ}

/-- `(u⁻¹ : SU N) = (u : Matrix _ _ ℂ)ᴴ`: the group inverse of a special unitary element is its
conjugate transpose, from `Matrix.mem_unitaryGroup_iff'`.

DERIVED: no numeral occurs in the statement. -/
theorem coe_inv_eq_conjTranspose (u : MassGap.SUN.SU N) :
    ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by
  have hu : (u : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp u.2).1
  have h1 : Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)
      * (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : (u : Matrix (Fin N) (Fin N) ℂ)
      * Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have h3 : (u : Matrix (Fin N) (Fin N) ℂ)
      * ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    exact Submonoid.coe_one _
  calc ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = 1 * ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := (Matrix.one_mul _).symm
    _ = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ)
          * ((u : Matrix (Fin N) (Fin N) ℂ)
            * ((u⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [← Matrix.mul_assoc, h1]
    _ = Matrix.conjTranspose (u : Matrix (Fin N) (Fin N) ℂ) := by rw [h3, Matrix.mul_one]

/-- `hsRe a b = (trace (a * b⁻¹)).re` for `a b : SU N`, by `coe_inv_eq_conjTranspose`. So the cross
form is the real trace of the word a straddling plaquette contributes.

DERIVED: no numeral occurs in the statement. -/
theorem hsRe_coe_eq (a b : MassGap.SUN.SU N) :
    hsRe (a : Matrix (Fin N) (Fin N) ℂ) (b : Matrix (Fin N) (Fin N) ℂ)
      = (Matrix.trace ((a * b⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold hsRe
  rw [← coe_inv_eq_conjTranspose b, ← Submonoid.coe_mul]

/-- `hsRe (g * a * h⁻¹) (g * b * h⁻¹) = hsRe a b` at every `g, h, a, b` in `SU N`. Through
`hsRe_coe_eq` the word becomes `g * (a * b⁻¹) * g⁻¹`, the two `h`s having cancelled, and the trace
is invariant under conjugation.

Scope: one matrix pair under one gauge pair. `wilson_crossing_pairing_nonneg`'s `hXinv` quantifies
over the whole half at once, and the direct-sum form needed when several straddling plaquettes are
read together is not proved here.

DERIVED: no numeral occurs in the statement. -/
theorem hsRe_conj (g h a b : MassGap.SUN.SU N) :
    hsRe ((g * a * h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
        ((g * b * h⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = hsRe (a : Matrix (Fin N) (Fin N) ℂ) (b : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hsRe_coe_eq, hsRe_coe_eq]
  have hword : (g * a * h⁻¹) * (g * b * h⁻¹)⁻¹ = g * (a * b⁻¹) * g⁻¹ := by
    group
  rw [hword]
  have hinv : ((g⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      * ((g : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    exact Submonoid.coe_one _
  have hcoe3 : ((g * (a * b⁻¹) * g⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (g : Matrix (Fin N) (Fin N) ℂ)
          * ((a * b⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * ((g⁻¹ : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
  rw [hcoe3, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

/-- `hsRe (cA 1 * cA 0) (cA 0) ≠ hsRe (cA 0) (cA 0)`: multiplying only one argument changes the
cross form, so `hsRe_conj`'s two-sided shape is required. On these two control elements the value
moves from `3` to `-1`.

DERIVED: `1` and `0` are the two indices of `NegControl.cA`, selecting the non-identity control
element and the identity; the values `3` and `-1` are the computed traces and appear in the
proof. -/
theorem negctl_hsRe_one_sided_not_invariant :
    hsRe (NegControl.cA 1 * NegControl.cA 0) (NegControl.cA 0)
      ≠ hsRe (NegControl.cA 0) (NegControl.cA 0) := by
  have h1 : NegControl.cA 1 * NegControl.cA 0 = NegControl.cA 1 := by
    simp only [NegControl.cA, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num [NegControl.dvec]
  rw [h1, NegControl.hsRe_cA_one_zero, NegControl.hsRe_cA_zero_zero]
  norm_num

end GaugeInvariance


section Audit
#print axioms hsRe_self_nonneg
#print axioms paired_sum_nonneg_at_fixed
#print axioms no_paired_expansion_of_neg_at_fixed
#print axioms no_paired_word_of_neg_at_fixed
#print axioms no_half_paired_of_neg_at_fixed
#print axioms no_paired_after_equivariant_reparam
#print axioms gNeg_inv
#print axioms trace_gNeg
#print axioms reflConf_cfgWitness
#print axioms hol_cfgWitness
#print axioms straddling_word_not_paired_at_odd_lag
#print axioms straddling_word_not_matrix_paired_at_odd_lag
#print axioms straddling_not_paired_four_dim
#print axioms straddling_word_not_determined_by_halves
#print axioms no_half_function_for_straddling_word
#print axioms invLink_cfgWitness
#print axioms negctl_paired_word_is_nonneg
#print axioms negctl_identity_config
#print axioms measurable_gaugeAvg
#print axioms gaugeAvg_act
#print axioms kernel_arg_shift
#print axioms integral_gaugeAvg_mul_invariant
#print axioms crossing_gauge_integral_eq
#print axioms crossing_gauge_pairing_nonneg
#print axioms coe_inv_eq_conjTranspose
#print axioms hsRe_conj
#print axioms negctl_hsRe_one_sided_not_invariant
#print axioms abs_hsRe_le_card
#print axioms wilson_kernel_integral_psd
#print axioms wilson_crossing_pairing_nonneg
end Audit

end MassGap.CrossingIntegration
