import Mathlib
import MassGap.CellSpectrum
import MassGap.Transfer

/-!
# MassGap.VolumeRate — exponential decay bounds carrying an explicit rate

Six groups of statements about a family of finite exponential sums
`∑ k ∈ s F, P F k * (μ F k) ^ τ` indexed by a volume `F : ℕ`, and about the transfer operator of a
`Transfer.TransferData`.

## §1 Quantifier shapes

`exists_pos_and_iff`, `forall_nat_const_iff` and `vacuous_uniform_shape` are propositional
equivalences: `∃ κ : ℝ, 0 < κ ∧ Q` is equivalent to `Q`, and `∀ _F : ℕ, Q` is equivalent to `Q`, when
`Q` is a `Prop` parameter and so contains neither bound variable.
`ym_gap_uniform_in_volume_shape_is_vacuous` instantiates the pair at a specific `Tendsto` statement
whose summand mentions neither `κ` nor `F`.

## §2–§3 The rate bound, at one volume and uniformly

`finite_sum_rate_bound` is `Aperture.finite_sum_margin_bound` with the margin written as
`Real.exp (-κ)` and the exponent moved inside: `‖∑ k ∈ s, P k * (μ k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) *
exp (-κ * τ)`. `gap_rate_uniform_in_volume` takes `Aperture.UniformSpectralMargin μ₁` — which
carries a volume-independent `κ` — plus a dominance read, and produces one `κ > 0` bounding every
volume's sum; `κ` occurs in the body after the `∧`.
`gap_rate_and_decay_uniform_in_volume` adds the `Tendsto` conclusion at the same `κ`, and
`gap_rate_uniform_in_volume_of_intensive` obtains the margin from a single `r < 1` bounding `μ₁` at
every volume, through `Aperture.uniform_margin_of_intensive_radius`.

## §4–§5 The rate as a named constant

`cell_ceiling_eq_exp_neg_floor` is the identity `3 ^ (-(1:ℝ)/4) = exp (-κ₀YM)`.
`gap_rate_at_floor_uniform_in_volume` states the bound at `κ₀YM` with no existential, given
`mHi F ≤ 3 ^ (-(1:ℝ)/4)` at every volume. `product_volume_gap_rate` derives that input for a
product spectrum: `CellEnclosure.product_subvacuum_le` says a product of factors in `[0, 1]` with one
factor at most `3 ^ (-(1:ℝ)/4)` is itself at most `3 ^ (-(1:ℝ)/4)`, independently of how many factors
there are. `product_volume_gap_rate_concrete` and `product_volume_gap_rate_concrete_one` instantiate
that at `CellEnclosure.ceilFac`.

## §6 The geometric law on the vacuum complement

`inner_vac_Tq` uses `TransferData.Tq_isSymmetric` and `Tq_vacGNS` to show the vacuum-orthogonal
subspace is `Tq`-invariant; `inner_vac_Tq_pow` iterates it. `norm_Tq_pow_le` then turns a per-step
bound `‖Tq y‖ ≤ ρ₁ ‖y‖` on that subspace into `‖Tq^n x‖ ≤ ρ₁^n ‖x‖`, and `rp_sub_geometric` restates
it in the form `Mixing.gap_of_maximal_correlation` consumes. `rp_gap_of_one_cut` applies
that theorem to conclude `‖Tq^n x‖ → 0` when `ρ₁ < 1`.

Scope: the prefactor `∑ k ∈ s F, ‖P F k‖` depends on `F` and is written out explicitly; no statement
here claims a volume-independent prefactor. In §6 the index `n` is the number of applications of
`Tq`, not a volume, and `ρ₁` is a per-step bound for the given `D` — nothing makes it independent of
anything. The intensive hypotheses `hint`, `hbound` and `hdom` are supplied by the caller except in
`product_volume_gap_rate`, where the product structure supplies them. Axiom footprints are printed at
the end of the file.
-/

namespace MassGap.VolumeRate

open MassGap MassGap.CellEnclosure

/-! ## §1 Quantifiers over variables that do not occur in the body

Three propositional equivalences and one instance of them, so that the relation between a shape like
`∃ κ, 0 < κ ∧ Q` and `Q` itself is a theorem rather than a remark. -/

/-- `(∃ κ : ℝ, 0 < κ ∧ Q) ↔ Q`, for `Q : Prop` a parameter. Since `Q` is a parameter it cannot
mention `κ`, so the forward direction discards the witness and the reverse supplies `κ = 1`.

Scope: the equivalence holds because `Q` is a parameter of the theorem. A statement whose body does
mention the bound `κ` is not an instance of it.

DERIVED: `0` is the positivity threshold on the bound variable `κ`. -/
theorem exists_pos_and_iff (Q : Prop) : (∃ κ : ℝ, 0 < κ ∧ Q) ↔ Q := by
  constructor
  · rintro ⟨_, _, hq⟩
    exact hq
  · intro hq
    exact ⟨1, one_pos, hq⟩

/-- `(∀ _F : ℕ, Q) ↔ Q`, for `Q : Prop` a parameter. The forward direction instantiates at `0`, which
`ℕ` provides; the reverse ignores the argument.

DERIVED: no numeral appears in the statement; the `0` used to instantiate lives in the proof. -/
theorem forall_nat_const_iff (Q : Prop) : (∀ _F : ℕ, Q) ↔ Q :=
  ⟨fun h => h 0, fun h _ => h⟩

/-- `(∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ, Q) ↔ Q`, for `Q : Prop` a parameter — `exists_pos_and_iff` composed
with `forall_nat_const_iff`. Neither binder occurs in `Q`.

DERIVED: `0` is the positivity threshold on the bound variable `κ`. -/
theorem vacuous_uniform_shape (Q : Prop) : (∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ, Q) ↔ Q :=
  (exists_pos_and_iff _).trans (forall_nat_const_iff Q)

/-- `vacuous_uniform_shape` instantiated at a concrete decay statement: for `n : ℕ` and `x : ℝ`,

    (∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ, Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * (x : ℂ) ^ τ‖) atTop (nhds 0))
      ↔ Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * (x : ℂ) ^ τ‖) atTop (nhds 0)

The summand on either side mentions neither `κ` nor `F`, so both binders are discharged.

DERIVED: `0` occurs three times — the positivity threshold on `κ`, and the limit point `nhds 0` on
each side of the equivalence. `1` occurs four times — the `+ 1` in the index type `Fin (n + 1)` and
the coefficient `(1 : ℂ)`, once on each side. -/
theorem ym_gap_uniform_in_volume_shape_is_vacuous (n : ℕ) (x : ℝ) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ,
        Filter.Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖)
          Filter.atTop (nhds 0))
      ↔ Filter.Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖)
          Filter.atTop (nhds 0) :=
  vacuous_uniform_shape _

/-! ## §2 The rate form at one mode family

`Aperture.finite_sum_margin_bound` bounds a finite exponential sum by `(∑ ‖P k‖) * ρ ^ τ`. Writing
`ρ = exp (-κ)` and moving the exponent inside gives the form used throughout the rest of the file.
`GapRate.mass_gap_exponential_decay` performs the same step for a single `LatticeYM`. -/

/-- If `‖μ k‖ ≤ Real.exp (-κ)` at every `k ∈ s`, then
`‖∑ k ∈ s, P k * (μ k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * Real.exp (-κ * τ)` at every `τ : ℕ`. It is
`Aperture.finite_sum_margin_bound` at `ρ = Real.exp (-κ)`, with `Real.exp_nat_mul` moving the power
into the exponent.

Scope: `κ` is not assumed positive — for `κ ≤ 0` the bound still holds but does not decay. The
prefactor is the total spectral weight `∑ k ∈ s, ‖P k‖`, given explicitly.

DERIVED: no numeral appears in the statement. -/
theorem finite_sum_rate_bound {ι : Type*} (s : Finset ι) (P μ : ι → ℂ) {κ : ℝ}
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ Real.exp (-κ)) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * Real.exp (-κ * τ) := by
  have h := finite_sum_margin_bound s P μ (Real.exp (-κ)) hμ τ
  rw [← Real.exp_nat_mul] at h
  rwa [mul_comm (τ : ℝ) (-κ)] at h

/-! ## §3 One rate for every volume

`Aperture.UniformSpectralMargin μ₁` unfolds to `∃ κ, 0 < κ ∧ ∀ F, μ₁ F ≤ exp (-κ)`, so it already
carries a `κ` that does not depend on `F`. The three theorems below extract that `κ` and keep it in
the conclusion, as the rate of every volume's bound. -/

/-- From `UniformSpectralMargin μ₁` and `‖μ F k‖ ≤ μ₁ F` at every volume `F` and every active mode
`k ∈ s F`, there is a single `κ > 0` with

    ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ)

at every `F` and `τ`. The proof takes `κ` from the margin and applies `finite_sum_rate_bound` at each
volume.

Scope: `κ` occurs in the body after the `∧`, so it is not eliminable by `exists_pos_and_iff`. The
prefactor `∑ k ∈ s F, ‖P F k‖` does depend on `F` and is written out explicitly; the statement makes
no claim that it is bounded in `F`.

DERIVED: `0` is the positivity threshold on `κ`, inherited from `UniformSpectralMargin`. -/
theorem gap_rate_uniform_in_volume {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ)
    (hmargin : UniformSpectralMargin μ₁)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F τ : ℕ,
      ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ) := by
  obtain ⟨κ, hκ, hbnd⟩ := hmargin
  exact ⟨κ, hκ, fun F τ => finite_sum_rate_bound (s F) (P F) (μ F)
    (fun k hk => le_trans (hdom F k hk) (hbnd F)) τ⟩

/-- The same hypotheses as `gap_rate_uniform_in_volume`, with a conclusion conjoining two statements
at one `κ > 0`: the rate bound
`‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * exp (-κ * τ)` at every `F` and `τ`, and
`Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) atTop (nhds 0)` at every `F`. The second
conjunct is `Aperture.gap_at_finite_F` applied volume by volume.

Scope: `κ` occurs in the first conjunct but not in the second, so only the first is sensitive to the
value of the rate.

DERIVED: `0` occurs twice — the positivity threshold on `κ`, and the limit point in the `Tendsto`
conjunct. -/
theorem gap_rate_and_decay_uniform_in_volume {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ)
    (hmargin : UniformSpectralMargin μ₁)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ F τ : ℕ, ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖
          ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ)) ∧
      (∀ F : ℕ, Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖)
          Filter.atTop (nhds 0)) := by
  obtain ⟨κ, hκ, hbnd⟩ := hmargin
  refine ⟨κ, hκ, fun F τ => finite_sum_rate_bound (s F) (P F) (μ F)
    (fun k hk => le_trans (hdom F k hk) (hbnd F)) τ, fun F => ?_⟩
  exact gap_at_finite_F (s F) (P F) (μ F) hκ (fun k hk => le_trans (hdom F k hk) (hbnd F))

/-- `gap_rate_uniform_in_volume` with the margin hypothesis replaced by a single `r` with `0 < r`,
`r < 1` and `μ₁ F ≤ r` at every volume. `Aperture.uniform_margin_of_intensive_radius` converts that
to a `UniformSpectralMargin`, whose rate is `-Real.log r`.

Scope: `0 < r` is needed for the logarithm and `r < 1` for the rate to be positive.

DERIVED: `0` occurs twice, as the positivity threshold on `r` and on the produced `κ`; `1` is the
upper bound on `r`, the point at which the rate would vanish. -/
theorem gap_rate_uniform_in_volume_of_intensive {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hbound : ∀ F, μ₁ F ≤ r)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F τ : ℕ,
      ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ) :=
  gap_rate_uniform_in_volume s P μ μ₁
    (uniform_margin_of_intensive_radius μ₁ r hr0 hr1 hbound) hdom

/-! ## §4 The rate as the named constant `κ₀YM`

The ceiling `3 ^ (-(1:ℝ)/4)` equals `exp (-κ₀YM)`, with `κ₀YM = (1/4) log 3` the directed-path
counting constant of `Floor.lean`. With that identity the bound can be stated at `κ₀YM` outright,
with no existential quantifier over the rate. -/

/-- `(3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM)`. `Real.rpow_def_of_pos` rewrites the left side as
`exp ((-(1)/4) * log 3)`, and unfolding `κ₀YM` to `(1/4) * log 3` makes the exponents equal by `ring`.

DERIVED: `3` is the base, the directed-path branching count; `1` and `4` are the numerator and
denominator of the exponent `-(1)/4`, matching `κ₀YM`'s own `1/4`. -/
theorem cell_ceiling_eq_exp_neg_floor : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  unfold κ₀YM
  congr 1
  ring

/-- Given `mHi F ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)` at every volume and `‖μ F k‖ ≤ mHi F` at every active
mode, then at every `F` and `τ`

    ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ₀YM * τ).

The proof rewrites the ceiling as `exp (-κ₀YM)` by `cell_ceiling_eq_exp_neg_floor` and applies
`finite_sum_rate_bound`.

Scope: the rate is the named constant `κ₀YM`, so there is no existential quantifier over it;
positivity of `κ₀YM` is the separate `κ₀YM_pos`. The hypothesis `hint` is supplied by the caller.

DERIVED: `3` is the base of the ceiling, the directed-path branching count; `1` and `4` are the
numerator and denominator of its exponent `-(1)/4`, which is what makes the ceiling `exp (-κ₀YM)`. -/
theorem gap_rate_at_floor_uniform_in_volume {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (mHi : ℕ → ℝ)
    (hint : ∀ F, mHi F ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ mHi F) :
    ∀ F τ : ℕ, ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖
      ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ₀YM * τ) := by
  intro F τ
  refine finite_sum_rate_bound (s F) (P F) (μ F) (fun k hk => ?_) τ
  rw [← cell_ceiling_eq_exp_neg_floor]
  exact le_trans (hdom F k hk) (hint F)

/-! ## §5 A product spectrum, where the ceiling hypothesis is derived

`CellEnclosure.product_subvacuum_le` says a product of factors in `[0, 1]` carrying one factor at
most `3 ^ (-(1:ℝ)/4)` is itself at most `3 ^ (-(1:ℝ)/4)`, whatever the number of factors. Adding
factors equal to `1` therefore leaves the bound unchanged, so the hypothesis `hint` of
`gap_rate_at_floor_uniform_in_volume` can be discharged rather than assumed for such a spectrum. -/

/-- Suppose every active mode is a product of per-cell factors: `μ F k = ∏ i, fac F k i` with each
factor in `[0, 1]` (`h01`) and at least one factor at most `(3 : ℝ) ^ (-(1 : ℝ) / 4)` (`hexc`). Then
`0 < κ₀YM` and, at every cell count `F` and every `τ`,

    ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ₀YM * τ).

The ceiling hypothesis of `gap_rate_at_floor_uniform_in_volume` is discharged by
`CellEnclosure.product_subvacuum_le`, which does not see the number of cells, so the same rate serves
every `F`.

Scope: the modes are products of independent per-cell factors; the statement says nothing about a
spectrum that is not of that form. The prefactor still depends on `F`.

DERIVED: `0` occurs twice, as the lower bound on each factor and as the positivity threshold on
`κ₀YM`; `1` occurs twice, as the upper bound on each factor (the vacuum value) and as the exponent
numerator in `-(1)/4`; `3` is the base of the ceiling and `4` its root. -/
theorem product_volume_gap_rate {ι : Type*} {ncell : ℕ → ℕ}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (fac : ∀ F, ι → Fin (ncell F) → ℝ)
    (h01 : ∀ F, ∀ k ∈ s F, ∀ i, 0 ≤ fac F k i ∧ fac F k i ≤ 1)
    (hexc : ∀ F, ∀ k ∈ s F, ∃ j, fac F k j ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hμ : ∀ F, ∀ k ∈ s F, μ F k = ((∏ i, fac F k i : ℝ) : ℂ)) :
    0 < κ₀YM ∧ ∀ F τ : ℕ, ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖
      ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ₀YM * τ) := by
  refine ⟨κ₀YM_pos, gap_rate_at_floor_uniform_in_volume s P μ
    (fun _ => (3 : ℝ) ^ (-(1 : ℝ) / 4)) (fun _ => le_refl _) (fun F k hk => ?_)⟩
  rw [hμ F k hk, Complex.norm_of_nonneg (Finset.prod_nonneg (fun i _ => (h01 F k hk i).1))]
  obtain ⟨j, hj⟩ := hexc F k hk
  exact product_subvacuum_le (fac F k) (by positivity) (fun i => h01 F k hk i) j hj

/-- `product_volume_gap_rate` instantiated at `ι := Unit`, `ncell F := F + 1`, unit projections and
factors `CellEnclosure.ceilFac F` — one cell at the ceiling and the rest at `1`. The conclusion has
no hypotheses: `0 < κ₀YM`, and at every `F` and `τ`,
`‖∑ _ : Unit, (1 : ℂ) * ((∏ i, ceilFac F i : ℝ) : ℂ) ^ τ‖ ≤ (∑ _ : Unit, ‖(1 : ℂ)‖) * exp (-κ₀YM * τ)`.
The excited-cell hypothesis is met at index `0` by `simp [ceilFac]`.

Scope: the index type is `Unit`, so the sum has one term; the cell count `F` is universally
quantified while the rate stays `κ₀YM`.

DERIVED: `0` is the positivity threshold on `κ₀YM`; `1` occurs twice, as the projection coefficient
`(1 : ℂ)` on the left and inside the prefactor `‖(1 : ℂ)‖` on the right. -/
theorem product_volume_gap_rate_concrete :
    0 < κ₀YM ∧ ∀ F τ : ℕ,
      ‖∑ _ : Unit, (1 : ℂ) * (((∏ i, ceilFac F i : ℝ)) : ℂ) ^ τ‖
        ≤ (∑ _ : Unit, ‖(1 : ℂ)‖) * Real.exp (-κ₀YM * τ) :=
  product_volume_gap_rate (ι := Unit) (ncell := fun F => F + 1) (fun _ => Finset.univ)
    (fun _ _ => 1) (fun F _ => (((∏ i, ceilFac F i : ℝ)) : ℂ)) (fun F _ i => ceilFac F i)
    (fun F _ _ i => ceilFac_mem F i) (fun F _ _ => ⟨0, by simp [ceilFac]⟩) (fun _ _ _ => rfl)

/-- `product_volume_gap_rate_concrete` with the prefactor evaluated: at every `F` and `τ`,
`‖∑ _ : Unit, (1 : ℂ) * ((∏ i, ceilFac F i : ℝ) : ℂ) ^ τ‖ ≤ Real.exp (-κ₀YM * τ)`. The sum
`∑ _ : Unit, ‖(1 : ℂ)‖` is `1`, so the prefactor drops out.

Scope: the same rate `κ₀YM` appears at every `F`; the statement quantifies over both `F` and `τ` and
involves no existential.

DERIVED: `1` is the projection coefficient `(1 : ℂ)`; no other numeral appears in the statement, the
prefactor having been evaluated away. -/
theorem product_volume_gap_rate_concrete_one (F τ : ℕ) :
    ‖∑ _ : Unit, (1 : ℂ) * (((∏ i, ceilFac F i : ℝ)) : ℂ) ^ τ‖ ≤ Real.exp (-κ₀YM * τ) := by
  have h := product_volume_gap_rate_concrete.2 F τ
  have hpre : (∑ _ : Unit, ‖(1 : ℂ)‖) = (1 : ℝ) := by simp
  rw [hpre] at h
  linarith [h]

/-! ## §6 The geometric law on the vacuum complement of a `TransferData`

`Transfer.TransferData` carries `T_symm` (self-adjointness of the operator for the reflection form),
`T_contract`, and `T_vac` with `vac_norm`. From the first and the third, the vacuum-orthogonal
subspace is invariant under `Tq`; a per-step bound `‖Tq y‖ ≤ ρ₁ ‖y‖` on that subspace then iterates
to `‖Tq^n x‖ ≤ ρ₁^n ‖x‖`, which is the hypothesis `Mixing.gap_of_maximal_correlation` consumes.

Scope: `n` counts applications of `Tq`, not a volume, and `ρ₁` is whatever per-step bound the caller
supplies for the given `D`. Nothing in this section makes `ρ₁` independent of anything, and nothing
here states an equality `‖Tq^n‖ = ‖Tq‖^n`. -/

open MassGap.Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- If `inner ℝ D.vacGNS x = 0` then `inner ℝ D.vacGNS (D.Tq x) = 0`: the vacuum-orthogonal subspace
is `Tq`-invariant. The proof moves `Tq` across the inner product with `D.Tq_isSymmetric` and uses
`D.Tq_vacGNS` (`Tq` fixes the vacuum) to return to the hypothesis.

Scope: both ingredients are fields of `TransferData` — symmetry of `Tq` and the vacuum being fixed.
Neither is established here.

DERIVED: `0` occurs twice, as the value of the inner product assumed and as the value concluded. -/
theorem inner_vac_Tq (D : TransferData A) {x : GNS D.toReflForm}
    (hx : inner ℝ D.vacGNS x = (0 : ℝ)) :
    inner ℝ D.vacGNS (D.Tq x) = (0 : ℝ) := by
  have h := D.Tq_isSymmetric D.vacGNS x
  rw [D.Tq_vacGNS] at h
  rw [← h]
  exact hx

/-- `inner ℝ D.vacGNS ((D.Tq ^ n) x) = 0` at every `n : ℕ`, given `inner ℝ D.vacGNS x = 0`. Induction
on `n`, with `inner_vac_Tq` at each step and `pow_succ'` to peel off one application.

DERIVED: `0` occurs twice, as the value of the inner product assumed and as the value concluded at
every power. -/
theorem inner_vac_Tq_pow (D : TransferData A) {x : GNS D.toReflForm}
    (hx : inner ℝ D.vacGNS x = (0 : ℝ)) :
    ∀ n : ℕ, inner ℝ D.vacGNS ((D.Tq ^ n) x) = (0 : ℝ) := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hstep : (D.Tq ^ (n + 1)) x = D.Tq ((D.Tq ^ n) x) := by
        rw [pow_succ']; rfl
      rw [hstep]
      exact inner_vac_Tq D ih

/-- Given `0 ≤ ρ₁` and a per-step bound `‖D.Tq y‖ ≤ ρ₁ * ‖y‖` for every vacuum-orthogonal `y`, a
vacuum-orthogonal `x` satisfies `‖(D.Tq ^ n) x‖ ≤ ρ₁ ^ n * ‖x‖` at every `n`. Induction on `n`; the
per-step bound applies at each stage because `inner_vac_Tq_pow` keeps the iterate
vacuum-orthogonal.

Scope: the per-step bound `hρ` is a hypothesis, required only on the vacuum-orthogonal subspace. `ρ₁`
is not assumed below `1`, so the conclusion need not decay.

DERIVED: `0` occurs three times — the lower bound on `ρ₁`, and the inner-product value in the
orthogonality hypothesis of `hρ` and in that of `x`. -/
theorem norm_Tq_pow_le (D : TransferData A) {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) (n : ℕ) :
    ‖(D.Tq ^ n) x‖ ≤ ρ₁ ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (D.Tq ^ (n + 1)) x = D.Tq ((D.Tq ^ n) x) := by
        rw [pow_succ']; rfl
      rw [hstep]
      calc ‖D.Tq ((D.Tq ^ n) x)‖
          ≤ ρ₁ * ‖(D.Tq ^ n) x‖ := hρ _ (inner_vac_Tq_pow D hx n)
        _ ≤ ρ₁ * (ρ₁ ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ₁ ^ (n + 1) * ‖x‖ := by ring

/-- `norm_Tq_pow_le` rewritten as `‖(D.Tq ^ n) x‖ ≤ ‖(D.Tq ^ 0) x‖ * ρ₁ ^ n`, which is the shape
`Mixing.gap_of_maximal_correlation` consumes for `σ n = ‖(D.Tq ^ n) x‖`. `D.Tq ^ 0` is the identity,
so the prefactor is `‖x‖` and the two statements have the same content.

DERIVED: `0` occurs four times — the lower bound on `ρ₁`, the inner-product value in the
orthogonality hypothesis of `hρ` and in that of `x`, and the exponent `0` in `D.Tq ^ 0`, which names
the sequence's initial value. -/
theorem rp_sub_geometric (D : TransferData A) {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) (n : ℕ) :
    ‖(D.Tq ^ n) x‖ ≤ ‖(D.Tq ^ 0) x‖ * ρ₁ ^ n := by
  rw [show (D.Tq ^ 0) x = x from by simp, mul_comm]
  exact norm_Tq_pow_le D hρ0 hρ hx n

/-- With `0 ≤ ρ₁ < 1` and a per-step bound `‖D.Tq y‖ ≤ ρ₁ * ‖y‖` on the vacuum-orthogonal subspace, a
vacuum-orthogonal `x` satisfies `Tendsto (fun n => ‖(D.Tq ^ n) x‖) atTop (nhds 0)`. It is
`Mixing.gap_of_maximal_correlation` with its geometric hypothesis supplied by `rp_sub_geometric` and
nonnegativity of the norms.

Scope: `n` counts applications of `Tq`. There is no volume index in the statement, and `ρ₁` is the
per-step bound for the given `D`; nothing here relates it to any other `D`.

DERIVED: `0` occurs four times — the lower bound on `ρ₁`, the inner-product value in `hρ` and in
`hx`, and the limit point `nhds 0`; `1` is the upper bound on `ρ₁`, the contraction threshold that
makes the powers vanish. -/
theorem rp_gap_of_one_cut (D : TransferData A) {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) :
    Filter.Tendsto (fun n => ‖(D.Tq ^ n) x‖) Filter.atTop (nhds 0) := by
  refine gap_of_maximal_correlation hρ0 hρ1 (fun _ => norm_nonneg _) (fun n => ?_)
  exact rp_sub_geometric D hρ0 hρ hx n

/-! ## Axiom footprints

Foundational-only is exactly `{propext, Classical.choice, Quot.sound}`. Every declaration above is
printed below. -/

#print axioms exists_pos_and_iff
#print axioms forall_nat_const_iff
#print axioms vacuous_uniform_shape
#print axioms ym_gap_uniform_in_volume_shape_is_vacuous
#print axioms finite_sum_rate_bound
#print axioms gap_rate_uniform_in_volume
#print axioms gap_rate_and_decay_uniform_in_volume
#print axioms gap_rate_uniform_in_volume_of_intensive
#print axioms cell_ceiling_eq_exp_neg_floor
#print axioms gap_rate_at_floor_uniform_in_volume
#print axioms product_volume_gap_rate
#print axioms product_volume_gap_rate_concrete
#print axioms product_volume_gap_rate_concrete_one
#print axioms inner_vac_Tq
#print axioms inner_vac_Tq_pow
#print axioms norm_Tq_pow_le
#print axioms rp_sub_geometric
#print axioms rp_gap_of_one_cut

end MassGap.VolumeRate
