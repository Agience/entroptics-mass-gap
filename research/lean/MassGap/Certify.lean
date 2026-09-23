import Mathlib
import MassGap.ReachFreeze
import MassGap.Aperture

/-!
# MassGap.Certify — feeding interval bounds into `gap_of_confinement`

Every declaration here is an inequality between real variables, or an application of
`MassGap.Aperture`'s `gap_of_confinement` / `gap_at_finite_F` with one hypothesis replaced by a
two-step chain. `κ₀`, `μ`, `αhi`, `mhi`, `contrast` and `r` are free reals throughout: no counting
floor, tension, attenuation interval or spectral read is defined in this file, and no numeric value
is fixed except where `κ₀` is written out as `¼ log 3`.

The pattern is the same in each case. An enclosure `μ ≤ αhi` with `αhi < κ₀` gives `μ < κ₀`
(`confinement_of_certified`); a single margin `mhi` with `‖m k‖ ≤ mhi ≤ e^{-(κ₀-μ)}` gives the
per-mode hypothesis (`finite_aperture_of_certified`); and `gap_of_margin_certified` composes both
into the `Tendsto ... (nhds 0)` conclusion.

Later sections restate the comparison `μ < κ₀` in three other forms: as a contrast inequality
`contrast < 3^{1/4}` when `μ = log contrast` (`confinement_iff_contrast_lt_rpow`), as a spacing-uniform
margin (`UniformConfinement`), and as a Lipschitz-plus-cover bound on a compact interval
(`le_of_lipschitz_grid`).
-/

namespace MassGap

/-- Transitivity on three reals: `μ ≤ αhi` and `αhi < κ₀` give `μ < κ₀`. `lt_of_le_of_lt`. The
shape a certified upper enclosure of `μ` takes when its upper endpoint is compared against `κ₀`.

DERIVED: no numeral. -/
theorem confinement_of_certified {μ αhi κ₀ : ℝ} (hμ : μ ≤ αhi) (hcert : αhi < κ₀) :
    μ < κ₀ := lt_of_le_of_lt hμ hcert

/-- `gap_of_confinement` with its `μ < κ₀` hypothesis supplied by `confinement_of_certified`. Given
an enclosure `μ ≤ αhi < κ₀` and `‖m k‖ ≤ exp (-(κ₀ - μ))` on the finite index set `s`, the norm of
`∑ k ∈ s, P k * (m k)^τ` tends to `0` as `τ → ∞`. The conclusion is convergence, with no rate.

DERIVED: `0` is the limit the sum's norm reaches. -/
theorem gap_of_certified {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ αhi : ℝ)
    (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement s P m κ₀ μ (confinement_of_certified hμ hcert) hread

/-- Transitivity under the binder: from `‖m k‖ ≤ mhi` for every `k ∈ s` and a single
`mhi ≤ exp (-(κ₀ - μ))`, every `k ∈ s` satisfies `‖m k‖ ≤ exp (-(κ₀ - μ))`. `mhi` is one real bound
covering the whole index set, so one inequality replaces the per-mode family that
`gap_of_confinement` asks for. `mhi` need not be the supremum of `‖m k‖`, only an upper bound.

DERIVED: no numeral. -/
theorem finite_aperture_of_certified {ι : Type*} (s : Finset ι) (m : ι → ℂ) (κ₀ μ mhi : ℝ)
    (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi) (hcertm : mhi ≤ Real.exp (-(κ₀ - μ))) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hmargin k hk) hcertm

/-- `gap_of_certified` with its per-mode hypothesis supplied by `finite_aperture_of_certified`. Both
of `gap_of_confinement`'s hypotheses are then given by two-endpoint chains: `μ ≤ αhi < κ₀` and
`‖m k‖ ≤ mhi ≤ exp (-(κ₀ - μ))`. The conclusion is that the norm of `∑ k ∈ s, P k * (m k)^τ` tends to
`0`. All of `κ₀`, `μ`, `αhi` and `mhi` are free reals.

DERIVED: `0` is the limit the sum's norm reaches. -/
theorem gap_of_margin_certified {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ αhi mhi : ℝ)
    (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi) (hcertm : mhi ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_certified s P m κ₀ μ αhi hμ hcert (finite_aperture_of_certified s m κ₀ μ mhi hmargin hcertm)

/-- From `μ ≤ αhi`, `αhi < κ₀` and `κ₀ ≤ κ`, the difference `μ - κ` is negative.
`confinement_of_certified` chained into `ReachFreeze.confines_of_tension_lt_floor`. The conclusion is
a sign, not a magnitude: no lower bound on `κ - μ` is given.

DERIVED: `0` is the sign threshold the difference `μ - κ` falls below. -/
theorem confines_of_certified {μ αhi κ₀ κ : ℝ} (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hfloor : κ₀ ≤ κ) : μ - κ < 0 :=
  confines_of_tension_lt_floor hfloor (confinement_of_certified hμ hcert)

/-! ## The coupling-indexed form

`gap_of_confinement` applied pointwise in a parameter `β : ℝ`. The index set, weights and mode
magnitudes all become functions of `β`, and both hypotheses are asked at every `β`. -/

/-- `gap_of_confinement` applied at each `β : ℝ` separately. Given `μ β < κ₀` at every `β` and
`‖m β k‖ ≤ exp (-(κ₀ - μ β))` for every `β` and every `k ∈ s β`, the conclusion is that at every `β`
the norm of `∑ k ∈ s β, P β k * (m β k)^τ` tends to `0` as `τ → ∞`.

`κ₀` is a single real fixed before `β`, while `μ` varies with `β`. The conclusion is pointwise
convergence in `β`; it states no rate and no uniformity in `β`. Neither hypothesis is established
here.

DERIVED: `0` is the limit each sum's norm reaches. -/
theorem gap_of_confinement_read {ι : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ)
    (κ₀ : ℝ) (μ : ℝ → ℝ) (hconf : ∀ β, μ β < κ₀)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    ∀ β, Filter.Tendsto
      (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0) :=
  fun β => gap_of_confinement (s β) (P β) (m β) κ₀ (μ β) (hconf β) (hread β)

/-! ## The geometric envelope, and a spacing-uniform margin

`contraction_ge_margin` records the envelope `finite_sum_margin_bound` gives at the margin
`exp (-(κ₀ - μ))`. `UniformConfinement` is the predicate that one `ε > 0` separates `μ a` from `κ₀`
at every spacing `a`; `uniform_gap_of_uniformConfinement` rearranges it, and `weak_uniform_margin`
supplies it eventually from `μ → 0`. -/

/-- `finite_sum_margin_bound` at the margin `exp (-(κ₀ - μ))`: if every mode on `s` satisfies
`‖m k‖ ≤ exp (-(κ₀ - μ))`, then `‖∑ k ∈ s, P k * (m k)^τ‖ ≤ (∑ k ∈ s, ‖P k‖) * exp (-(κ₀ - μ))^τ`,
at every `τ`. `κ₀` and `μ` are free reals; the bound is an envelope for every `τ` and decays only if
a caller makes `κ₀ - μ` positive.

DERIVED: no numeral. -/
theorem contraction_ge_margin {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ : ℝ)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * (Real.exp (-(κ₀ - μ))) ^ τ :=
  finite_sum_margin_bound s P m (Real.exp (-(κ₀ - μ))) hread τ

/-- The predicate `∃ ε, 0 < ε ∧ ∀ a, μ a ≤ κ₀ - ε`: one positive margin, chosen before `a`,
separating `μ a` from `κ₀` at every `a`. Strictly stronger than `∀ a, μ a < κ₀`, in which the gap may
shrink with `a`.

DERIVED: `0` is the strict positivity the margin `ε` must have; without it the predicate would follow
from `μ a ≤ κ₀` alone. -/
def UniformConfinement (μ : ℝ → ℝ) (κ₀ : ℝ) : Prop := ∃ ε : ℝ, 0 < ε ∧ ∀ a, μ a ≤ κ₀ - ε

/-- `UniformConfinement μ κ₀` rearranged: the same `ε` satisfies `ε ≤ κ₀ - μ a` at every `a`. One
`linarith` per `a`, with the witness carried through unchanged.

DERIVED: `0` is the strict positivity of `ε`, carried from the hypothesis to the conclusion
unchanged. -/
theorem uniform_gap_of_uniformConfinement {μ : ℝ → ℝ} {κ₀ : ℝ}
    (h : UniformConfinement μ κ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, ε ≤ κ₀ - μ a := by
  obtain ⟨ε, hε, hbound⟩ := h
  exact ⟨ε, hε, fun a => by linarith [hbound a]⟩

/-- If `μ β → 0` as `β → ∞` and `ε < κ₀`, then `μ β ≤ κ₀ - ε` eventually. `Set.Iio (κ₀ - ε)` is a
neighbourhood of `0` precisely because `ε < κ₀`, and `Tendsto.eventually` transports it. The
conclusion is eventual in `β` with no threshold named, and it is weaker than `UniformConfinement`,
which asks the bound at every `a` rather than eventually.

DERIVED: `0` is the limit of `μ`, and is the point that has to lie inside `Iio (κ₀ - ε)` — which is
what `hε` supplies. -/
theorem weak_uniform_margin {μ : ℝ → ℝ} {κ₀ ε : ℝ} (hε : ε < κ₀)
    (hlim : Filter.Tendsto μ Filter.atTop (nhds 0)) :
    ∀ᶠ β in Filter.atTop, μ β ≤ κ₀ - ε := by
  have h : ∀ᶠ y in nhds (0 : ℝ), y ≤ κ₀ - ε := by
    have hmem : Set.Iio (κ₀ - ε) ∈ nhds (0 : ℝ) :=
      isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith)
    filter_upwards [hmem] with y hy
    exact le_of_lt (Set.mem_Iio.mp hy)
  filter_upwards [hlim.eventually h] with β hβ
  exact hβ

/-! ## The comparison rewritten in terms of `contrast`, where `μ = log contrast`

Four lemmas of real arithmetic. Substituting `μ = log contrast` turns `μ < κ₀` into
`contrast < exp κ₀`, and at `κ₀ = ¼ log 3` into `contrast < 3^{1/4}`. `contrast` is an arbitrary
positive real; nothing here defines it or evaluates it. -/

/-- `Real.exp ((1/4) * Real.log 3) = (3 : ℝ) ^ (1/4 : ℝ)`, by `Real.rpow_def_of_pos` and `ring` on
the exponent. The `rpow` form of the same real number.

DERIVED: `3` is the base, and `1 / 4` its exponent, on both sides — the left writes the power as
`exp (¼ log 3)` and the right as an `rpow`. -/
theorem exp_floor_eq_rpow : Real.exp ((1 / 4 : ℝ) * Real.log 3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- For `0 < contrast` and any real `κ₀`, `Real.log contrast < κ₀ ↔ contrast < Real.exp κ₀`. Both
directions, by `Real.exp_lt_exp` with `Real.exp_log`, and `Real.log_lt_log` with `Real.log_exp`.
Positivity of `contrast` is what makes `exp` and `log` mutually inverse here.

DERIVED: `0` is the positivity `Real.exp_log` and `Real.log_lt_log` need of `contrast`. -/
theorem tension_lt_floor_iff_contrast {contrast κ₀ : ℝ} (hc : 0 < contrast) :
    Real.log contrast < κ₀ ↔ contrast < Real.exp κ₀ := by
  constructor
  · intro h
    have h2 : Real.exp (Real.log contrast) < Real.exp κ₀ := Real.exp_lt_exp.mpr h
    rwa [Real.exp_log hc] at h2
  · intro h
    have h2 := Real.log_lt_log hc h
    rwa [Real.log_exp] at h2

/-- `tension_lt_floor_iff_contrast` at `κ₀ = ¼ log 3`, with the right-hand side rewritten by
`exp_floor_eq_rpow`: for `0 < contrast`,
`Real.log contrast < (1/4) * Real.log 3 ↔ contrast < (3 : ℝ) ^ (1/4 : ℝ)`.

DERIVED: `0` is the positivity of `contrast`; `1 / 4` and `3` are the two sides of the same value,
`¼ log 3` on the left and `3^{1/4}` on the right, identified by `exp_floor_eq_rpow`. -/
theorem confinement_iff_contrast_lt_rpow {contrast : ℝ} (hc : 0 < contrast) :
    Real.log contrast < (1 / 4 : ℝ) * Real.log 3 ↔ contrast < (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [tension_lt_floor_iff_contrast hc, exp_floor_eq_rpow]

/-- For `0 < contrast ≤ 1` and `0 < κ₀`, `Real.log contrast < κ₀`. `Real.log_nonpos` puts the
logarithm at most `0`, and `κ₀` is strictly above it. `κ₀` is any positive real; no floor value is
fixed.

DERIVED: `0` in `hc` is the positivity `Real.log_nonpos` needs; `1` in `h1` is the argument below
which the logarithm is nonpositive; `0` in `hκ` is what puts `κ₀` strictly above that. -/
theorem confined_of_contrast_le_one {contrast κ₀ : ℝ} (hc : 0 < contrast) (h1 : contrast ≤ 1)
    (hκ : 0 < κ₀) : Real.log contrast < κ₀ :=
  lt_of_le_of_lt (Real.log_nonpos hc.le h1) hκ

/-- `gap_of_confinement` at `κ₀ = ¼ log 3` and `μ = log contrast`, with the comparison hypothesis
supplied by `confinement_iff_contrast_lt_rpow`. Given `0 < contrast < 3^{1/4}` and
`‖m k‖ ≤ exp (-((1/4) * log 3 - log contrast))` on `s`, the norm of `∑ k ∈ s, P k * (m k)^τ` tends to
`0`. This is the one declaration in the file where `κ₀` is a fixed number rather than a variable.

DERIVED: `0` is the positivity of `contrast` and, separately, the limit the sum's norm reaches; `3`
and `1 / 4` are the fixed floor, appearing as the ceiling `3^{1/4}` in `hcrit` and as `¼ log 3` inside
the margin in `hread`, the two being identified by `exp_floor_eq_rpow`. -/
theorem gap_of_contrast_criterion {ι : Type*} (s : Finset ι) (P m : ι → ℂ) {contrast : ℝ}
    (hc : 0 < contrast) (hcrit : contrast < (3 : ℝ) ^ (1 / 4 : ℝ))
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-((1 / 4 : ℝ) * Real.log 3 - Real.log contrast))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement s P m ((1 / 4 : ℝ) * Real.log 3) (Real.log contrast)
    ((confinement_iff_contrast_lt_rpow hc).mpr hcrit) hread

/-! ## A pointwise bound on a compact interval from a cover and a Lipschitz modulus

One lemma of real analysis on `Set.Icc a b`. Its `hcover` hypothesis is stated for every point of the
interval, each requiring a nearby point where the value clears `B` by the margin `L·δ`; the lemma
itself does not mention a finite set, so finiteness of any grid is the caller's business. -/

/-- If `f` satisfies `|f x - f y| ≤ L |x - y|` on `Set.Icc a b` with `0 ≤ L`, and every `β` in that
interval has some `γ` in it with `|β - γ| ≤ δ` and `f γ ≤ B - L·δ`, then `f β ≤ B` throughout. Three
inequalities and `linarith`: the Lipschitz modulus transports the value at `γ` to `β` at a cost of at
most `L·δ`, which the margin in `hcover` has already absorbed.

`hcover` quantifies over every `β` in the interval, not over a finite set, and `δ` may be any real;
nothing in the statement requires a net, a grid, or `δ > 0`.

DERIVED: `0` is the sign `L` must have for `mul_le_mul_of_nonneg_left` to carry `|β - γ| ≤ δ` through
the Lipschitz constant. -/
theorem le_of_lipschitz_grid {f : ℝ → ℝ} {a b B L δ : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧ f γ ≤ B - L * δ) :
    ∀ β ∈ Set.Icc a b, f β ≤ B := by
  intro β hβ
  obtain ⟨γ, hγ, hd, hval⟩ := hcover β hβ
  have h1 : f β - f γ ≤ |f β - f γ| := le_abs_self _
  have h2 : |f β - f γ| ≤ L * |β - γ| := hlip β hβ γ hγ
  have h3 : L * |β - γ| ≤ L * δ := mul_le_mul_of_nonneg_left hd hL
  linarith

/-! ## The volume-indexed form

`Aperture.gap_uniform_in_F` with its `UniformSpectralMargin` hypothesis supplied from a single
`r < 1` bounding `μ₁ F` at every `F`. -/

/-- `Aperture.gap_uniform_in_F` with `UniformSpectralMargin μ₁` supplied by
`uniform_margin_of_intensive_radius` from a single `r` with `0 < r < 1` bounding `μ₁ F` at every `F`.
The conclusion is `∃ κ, 0 < κ ∧ ∀ F, Tendsto ... (nhds 0)`.

⛔ The bound variable `κ` occurs only in the conjunct `0 < κ`, not in the `Tendsto` clause after the
`∧`. So the statement gives convergence at each `F` together with the existence of some positive `κ`;
it does not assert a decay rate common to all `F`.

DERIVED: `0` in `hr0` and `1` in `hr1` are the range `r` must lie in for `-log r` to be a positive
rate; `0` in `0 < κ` is that rate's positivity; `0` in `nhds 0` is the limit each sum's norm
reaches. -/
theorem gap_uniform_in_volume_of_intensive {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hbound : ∀ F, μ₁ F ≤ r)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_uniform_in_F s P μ μ₁ (uniform_margin_of_intensive_radius μ₁ r hr0 hr1 hbound) hdom

#print axioms gap_uniform_in_volume_of_intensive

end MassGap
