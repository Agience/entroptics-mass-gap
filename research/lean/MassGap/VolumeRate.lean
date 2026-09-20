import Mathlib
import MassGap.CellSpectrum
import MassGap.Transfer

/-!
# MassGap.VolumeRate — Clay row B7: the gap is uniform in volume, WITH A RATE

## The defect this file exists to repair

Every "uniform in volume" conclusion in the tree before this file has the shape

    ∃ κ : ℝ, 0 < κ ∧ ∀ F, Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) atTop (nhds 0)

and `κ` does not occur anywhere after the `∧`. A bound variable that does not occur in the body it
binds carries no content: `∃ κ : ℝ, 0 < κ ∧ Q` is logically `Q` (`exists_pos_and_iff` below,
machine-checked, discharged with `κ = 1`). So that shape says *"for each volume the correlator tends
to zero"*, which is `gap_at_finite_F` quantified over `F`, and NOT *"at a common rate"*. The
uniformity lived only in the hypothesis `Aperture.UniformSpectralMargin`; `gap_uniform_in_F` extracts
its `κ`, uses it to build one `Tendsto` per `F`, and then discards it.

Two occurrences are weaker still: the `∀ _F : ℕ` there binds a summand containing no `F` at all
(`forall_nat_const_iff`, `vacuous_uniform_shape`), so the volume index is vacuous on both sides.

DO NOT REINTRODUCE THE PATTERN. A conclusion claims uniformity in `F` only if `κ` occurs to the right
of the quantifier that binds it AND the quantity being bounded actually depends on `F`. Before adding
a `∃ κ, 0 < κ ∧ …` theorem, check that deleting `∃ κ, 0 < κ ∧` changes the statement.

## What is proved here

* `finite_sum_rate_bound` — the single-volume rate form, `‖C τ‖ ≤ (∑‖P k‖) · e^{−κτ}`. It is
  `Aperture.finite_sum_margin_bound` with `ρ = e^{−κ}` and the exponent moved into the exponential,
  the same step `GapRate.mass_gap_exponential_decay` performs for one `LatticeYM`.
* `gap_rate_uniform_in_volume` — the repair. From `UniformSpectralMargin μ₁` (which already carries a
  volume-independent `κ`) and the dominance read, ONE `κ > 0` bounds EVERY volume's correlator by
  `(∑ k ∈ s F, ‖P F k‖) · e^{−κτ}`. Here `κ` occurs after the `∧`, so the statement is not the
  `∃`-free one.
* `gap_rate_and_decay_uniform_in_volume` — the same `κ` delivering both the rate and the old
  `Tendsto` conclusion, so it supersedes `Aperture.gap_uniform_in_F` and
  `Certify.gap_uniform_in_volume_of_intensive` rather than sitting beside them.
* `gap_rate_at_floor_uniform_in_volume` — the rate at the DERIVED constant `κ₀ = ¼log3`, with no
  existential at all. A statement with no `∃ κ` cannot be vacuous in `κ`.
* `product_volume_gap_rate` / `product_volume_gap_rate_concrete` — the decoupled product-of-cells
  transfer closed at that explicit rate. This is the case where the intensive input is DERIVED
  (`CellEnclosure.product_subvacuum_le`: a product of factors in `[0,1]` with one factor
  `≤ 3^{−1/4}` is `≤ 3^{−1/4}`, uniformly in the cell count), so nothing here is measured.

## The prefactor depends on the volume, and that is the correct statement

`M F := ∑ k ∈ s F, ‖P F k‖` is the total spectral weight at volume `F`; it grows with the number of
modes and pretending otherwise would be the same defect in a new place. What "uniform in volume"
means for a mass gap is that the EXPONENTIAL RATE is volume-independent — the correlation length
`1/κ` does not grow with the box — while the amplitude may not be. That is exactly the shape proved
here: `M` is given explicitly as a function of `F`, `κ` is a single constant. No theorem in this file
claims a volume-independent prefactor.

## What remains open

* **The coupled (physical) transfer.** Not open — closed NEGATIVELY, and that is a theorem.
  `CellCouple.form_perturbation_reaches_finitely_many` with `CellCouple.chain_coupling_extensive`
  show the operator-norm budget `2δ < μ` is unsatisfiable past some cell count at ANY budget, so the
  decoupled-plus-perturbation route cannot reach the thermodynamic limit. Nothing here routes around
  it. The surviving route is `LocalGap.lean`'s Knabe criterion, which does not bind to Yang–Mills:
  the Kogut–Susskind terms do not commute and `Transfer.TransferData` carries a positive contraction,
  not a sum of projectors.
* **The physical intensive input.** `∀ F, m_hi(F) ≤ 3^{−1/4}` for the `SU(N)` ensemble read is a
  measured continuum statement, not proved anywhere. Everything in this file that mentions the volume
  either takes it as a hypothesis (`gap_rate_uniform_in_volume`) or derives it for the decoupled
  product (`product_volume_gap_rate`).

## The `ρ'(n) = ρ'(1)^n` claim, and what is actually reachable

`MassGap.lean`'s `CellSpectrum` import line and `CellSpectrum`'s §"volume-uniform gap from the single
cell" both say `gap_uniform_of_cell` "wires Mixing S1 — RP ⟹ ρ'(n)=ρ'(1)^n exactly, one cut controls
every volume". That is not what those declarations do. `Mixing.gap_of_maximal_correlation` TAKES
`∀ n, σ n ≤ σ 0 * ρ₁ ^ n` as the hypothesis `hsub`; nothing derives it. And `gap_uniform_of_cell`'s
`σ : ℕ → ℝ` is indexed by the SEPARATION `n`, not by a volume — there is no volume index in its
statement, so it cannot be uniform in one.

The reachable part is proved here, and it is the INEQUALITY, which is all `hsub` needs:
`rp_sub_geometric` derives `‖T^n x‖ ≤ ‖x‖ · ρ₁^n` on the vacuum-orthogonal subspace from reflection
positivity alone. RP enters as `TransferData.T_symm`; with `T_vac` it makes the vacuum-orthogonal
subspace `T`-invariant (`inner_vac_Tq`), after which submultiplicativity of the per-step bound gives
the geometric law by induction. `rp_gap_of_one_cut` then feeds it straight into
`Mixing.gap_of_maximal_correlation`, so S1's hypothesis is DERIVED rather than assumed.

The EQUALITY `ρ'(n) = ρ'(1)^n` is a different statement and is not proved here. It would need
`‖T^n‖ = ‖T‖^n` for a self-adjoint operator — true, and reachable through the C*-identity — plus an
identification of the Dobrushin–Shlosman `ρ'(n)` with `‖T^n‖` restricted to the vacuum complement,
which requires the time-Markov property of the measure and has no object in this tree. It is also not
needed: every consumer wants the upper bound.

NEITHER DIRECTION GIVES UNIFORMITY IN VOLUME. `rp_sub_geometric` says one cut controls every
SEPARATION at a fixed volume. Volume-uniformity is the separate statement that `ρ₁` does not depend on
the volume — the intensive input again. The claim that RP makes the volume-uniform gap free is false,
and correcting it is part of this file's purpose.

No `sorry`, no new axiom; every declaration's footprint is printed at the end of the file.
-/

namespace MassGap.VolumeRate

open MassGap MassGap.CellEnclosure

/-! ## §1 The vacuous-`κ` pattern, stated formally

These three are the defect written as theorems, so that the claim "the old shape carries no
uniformity" is machine-checked rather than asserted in prose. -/

/-- **`∃ κ, 0 < κ ∧ Q` is `Q`** when `κ` does not occur in `Q`. The forward direction drops the
witness; the reverse supplies `κ = 1`. This is the shape of `Aperture.gap_uniform_in_F`,
`Certify.gap_uniform_in_volume_of_intensive`, `CellEnclosure.gap_uniform_of_cell_intensive`,
`CellEnclosure.product_volume_gap` and `Complete.ym_gap_uniform_in_volume`: in each of them the
conclusion after the `∧` mentions no `κ`, so each is equivalent to its own `∃`-free body and asserts
nothing about a common rate. -/
theorem exists_pos_and_iff (Q : Prop) : (∃ κ : ℝ, 0 < κ ∧ Q) ↔ Q := by
  constructor
  · rintro ⟨_, _, hq⟩
    exact hq
  · intro hq
    exact ⟨1, one_pos, hq⟩

/-- **`∀ _F : ℕ, Q` is `Q`** when `F` does not occur in `Q`. `ℕ` is inhabited, so the quantifier is
discharged at `F = 0`. -/
theorem forall_nat_const_iff (Q : Prop) : (∀ _F : ℕ, Q) ↔ Q :=
  ⟨fun h => h 0, fun h _ => h⟩

/-- **The doubly-vacuous shape.** `∃ κ, 0 < κ ∧ ∀ _F : ℕ, Q` is `Q`. Both binders are inert, so the
statement is about neither a rate nor a volume. -/
theorem vacuous_uniform_shape (Q : Prop) : (∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ, Q) ↔ Q :=
  (exists_pos_and_iff _).trans (forall_nat_const_iff Q)

/-- **`Complete.ym_gap_uniform_in_volume`'s conclusion, shown equivalent to a single decay statement
with neither a rate nor a volume in it.** The literal conclusion of that theorem (and, with the same
summand, of `CellEnclosure.cell_volume_bar_nonvacuous`) is reproduced on the left. The `∃ κ, 0 < κ ∧`
and the `∀ _F : ℕ` are both discharged, leaving `gap_at_finite_F` at one fixed mode family. Nothing
in it is uniform in anything. -/
theorem ym_gap_uniform_in_volume_shape_is_vacuous (n : ℕ) (x : ℝ) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ,
        Filter.Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖)
          Filter.atTop (nhds 0))
      ↔ Filter.Tendsto (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖)
          Filter.atTop (nhds 0) :=
  vacuous_uniform_shape _

/-! ## §2 The rate form at one volume

`Aperture.finite_sum_margin_bound` already bounds the finite exponential sum by `(∑‖P k‖) · ρ^τ`.
Writing `ρ = e^{−κ}` and moving the exponent inside turns it into the geometric-decay form the mass
gap is stated in. This is the same step `GapRate.mass_gap_exponential_decay` performs for a single
`LatticeYM`, reused here in the free-standing form the volume family needs. -/

/-- **The rate bound at one mode family.** Every active mode inside the margin `e^{−κ}` gives
`‖∑ₖ Pₖ μₖ^τ‖ ≤ (∑ₖ ‖Pₖ‖) · e^{−κτ}`: exponential decay at rate `κ`, with the total spectral weight
as prefactor. Reuses `Aperture.finite_sum_margin_bound`. -/
theorem finite_sum_rate_bound {ι : Type*} (s : Finset ι) (P μ : ι → ℂ) {κ : ℝ}
    (hμ : ∀ k ∈ s, ‖μ k‖ ≤ Real.exp (-κ)) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (μ k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * Real.exp (-κ * τ) := by
  have h := finite_sum_margin_bound s P μ (Real.exp (-κ)) hμ τ
  rw [← Real.exp_nat_mul] at h
  rwa [mul_comm (τ : ℝ) (-κ)] at h

/-! ## §3 The repair: one rate for every volume

The input `Aperture.UniformSpectralMargin μ₁ = ∃ κ, 0 < κ ∧ ∀ F, μ₁ F ≤ e^{−κ}` already carries a
volume-independent `κ`. `gap_uniform_in_F` obtains it and then states a conclusion it does not appear
in. Here it is obtained once and kept: it is the rate in every volume's bound. -/

/-- **THE GAP IS UNIFORM IN VOLUME, WITH A RATE.** From a volume-independent spectral margin
(`hmargin`) and the read that every active mode at volume `F` sits under `μ₁ F` (`hdom`), there is a
SINGLE `κ > 0` such that at EVERY volume `F` and every separation `τ`

    ‖∑ k ∈ s F, P F k · (μ F k)^τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) · e^{−κτ}.

`κ` occurs to the right of the `∧`, so deleting `∃ κ, 0 < κ ∧` changes the statement — this is the
content `gap_uniform_in_F` was missing. The prefactor `∑ k ∈ s F, ‖P F k‖` is volume-dependent and is
given explicitly rather than existentially: the correlation length `1/κ` is what does not grow with
the box, the amplitude may. -/
theorem gap_rate_uniform_in_volume {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ)
    (hmargin : UniformSpectralMargin μ₁)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F τ : ℕ,
      ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ) := by
  obtain ⟨κ, hκ, hbnd⟩ := hmargin
  exact ⟨κ, hκ, fun F τ => finite_sum_rate_bound (s F) (P F) (μ F)
    (fun k hk => le_trans (hdom F k hk) (hbnd F)) τ⟩

/-- **The rate AND the decay, at the same `κ`.** The rate bound above together with the qualitative
conclusion the older declarations stop at. One theorem supersedes `Aperture.gap_uniform_in_F`: its
`Tendsto` half is literally that theorem's conclusion, and the extra conjunct is the uniformity the
name promises. -/
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

/-- **The rate form from an intensive spectral radius.** The `Certify.gap_uniform_in_volume_of_intensive`
input — one `r < 1` bounding the dominant magnitude at every volume — delivered as a volume-uniform
RATE rather than a per-volume limit. The rate is `κ = −log r`, supplied by
`Aperture.uniform_margin_of_intensive_radius`. -/
theorem gap_rate_uniform_in_volume_of_intensive {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hbound : ∀ F, μ₁ F ≤ r)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F τ : ℕ,
      ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) * Real.exp (-κ * τ) :=
  gap_rate_uniform_in_volume s P μ μ₁
    (uniform_margin_of_intensive_radius μ₁ r hr0 hr1 hbound) hdom

/-! ## §4 The rate named outright: `κ₀ = ¼log3`

An `∃ κ` can be vacuous; a named constant cannot. The single-cell ceiling `3^{−1/4}` IS `e^{−κ₀}`
with `κ₀` the directed-path counting floor of `Floor.lean`, so the intensive input pins the rate to a
derived constant and the existential can be removed entirely. -/

/-- **The single-cell ceiling is `e^{−κ₀}`.** `3^{−1/4} = exp(−¼log3)`. The identity is used inline in
five places in the tree (`CellEnclosure.lean:53,68`, `Complete.lean:2487,2541,2564`); named here
because §4 needs it as a rewrite. -/
theorem cell_ceiling_eq_exp_neg_floor : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  unfold κ₀YM
  congr 1
  ring

/-- **THE VOLUME-UNIFORM RATE AT THE COUNTING FLOOR — no existential.** With the intensive input
`m_hi(F) ≤ 3^{−1/4}` at every volume, every volume's correlator obeys

    ‖∑ k ∈ s F, P F k · (μ F k)^τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) · e^{−κ₀ τ},   κ₀ = ¼log3,

with `κ₀` a DERIVED constant (`Floor.lean`), the same at every `F`. There is no `∃ κ` to be vacuous
in, and `κ₀YM_pos` gives `κ₀ > 0` separately. The remaining input is the intensive read `hint`, which
for the physical `SU(N)` ensemble is measured, and for the decoupled product is derived in §5. -/
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

/-! ## §5 The decoupled product of cells, closed at the explicit rate

`CellEnclosure.product_volume_gap` is the one place in the tree where the intensive input is DERIVED
rather than assumed: `product_subvacuum_le` shows a product of factors in `[0,1]` carrying one factor
`≤ 3^{−1/4}` is itself `≤ 3^{−1/4}`, with no dependence on how many factors there are. Adding cells
adds vacuum factors `1`, so the dominant sub-vacuum magnitude stays at the single-plaquette ceiling.
That is a genuine volume-uniformity mechanism — but `product_volume_gap` spends it on the vacuous
shape. Here it is spent on the rate. -/

/-- **THE DECOUPLED PRODUCT-OF-CELLS TRANSFER HAS A VOLUME-INDEPENDENT RATE.** A mode family whose
every active mode at volume `F` is a product `∏ᵢ fac F k i` of per-cell magnitudes in `[0,1]` with at
least one cell excited below the machine-checked single-cell ceiling `3^{−1/4}`
(`CellEnclosure.Hcell2_clears_floor`) satisfies

    ‖∑ k ∈ s F, P F k · (μ F k)^τ‖ ≤ (∑ k ∈ s F, ‖P F k‖) · e^{−κ₀ τ}

at EVERY cell count `F`, with `κ₀ = ¼log3 > 0` derived and volume-independent. This is
`CellEnclosure.product_volume_gap` upgraded from "each volume forgets" to "every volume forgets at
one rate", and the rate is named rather than existentially quantified. The intensive input is proved,
not measured: `product_subvacuum_le` does not see the cell count.

This closes B7 for the DECOUPLED transfer. The physical coupled transfer is a different object, and
`CellCouple.form_perturbation_reaches_finitely_many` / `chain_coupling_extensive` show the
perturbative route to it terminates. -/
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

/-- **The product rate is non-vacuous — the extremal constructed model.** The `F+1`-cell product with
one cell at the machine-checked ceiling `3^{−1/4}` and the rest at the vacuum `1`
(`CellEnclosure.ceilFac`) obeys the `κ₀` rate at every cell count. The magnitude is an actual
constructed spectrum, not a constant witness, and the cell count is universally quantified while the
rate is fixed. -/
theorem product_volume_gap_rate_concrete :
    0 < κ₀YM ∧ ∀ F τ : ℕ,
      ‖∑ _ : Unit, (1 : ℂ) * (((∏ i, ceilFac F i : ℝ)) : ℂ) ^ τ‖
        ≤ (∑ _ : Unit, ‖(1 : ℂ)‖) * Real.exp (-κ₀YM * τ) :=
  product_volume_gap_rate (ι := Unit) (ncell := fun F => F + 1) (fun _ => Finset.univ)
    (fun _ _ => 1) (fun F _ => (((∏ i, ceilFac F i : ℝ)) : ℂ)) (fun F _ i => ceilFac F i)
    (fun F _ _ i => ceilFac_mem F i) (fun F _ _ => ⟨0, by simp [ceilFac]⟩) (fun _ _ _ => rfl)

/-- The same bound with the prefactor evaluated: the extremal product's correlator is at most
`e^{−κ₀τ}` at every cell count `F`. Reading the constant off the statement is the point — `κ₀` is
`¼log3 ≈ 0.2747`, and it is the same number at `F = 0` and at `F = 10¹⁰`. -/
theorem product_volume_gap_rate_concrete_one (F τ : ℕ) :
    ‖∑ _ : Unit, (1 : ℂ) * (((∏ i, ceilFac F i : ℝ)) : ℂ) ^ τ‖ ≤ Real.exp (-κ₀YM * τ) := by
  have h := product_volume_gap_rate_concrete.2 F τ
  have hpre : (∑ _ : Unit, ‖(1 : ℂ)‖) = (1 : ℝ) := by simp
  rw [hpre] at h
  linarith [h]

/-! ## §6 What reflection positivity actually gives: one cut controls every SEPARATION

The tree's prose says RP gives `ρ'(n) = ρ'(1)^n` and hence the volume-uniform gap for free. It does
not, and `Mixing.gap_of_maximal_correlation` assumes the geometric law rather than deriving it. The
part that IS derivable from RP is derived here.

`Transfer.TransferData` carries exactly the Osterwalder–Seiler data: `T_symm` (self-adjointness of
time translation for the reflection form — this IS reflection positivity's payload), `T_contract`,
and `T_vac` with `vac_norm`. From `T_symm` and `T_vac`, the vacuum-orthogonal subspace is
`T`-invariant; a per-step contraction factor `ρ₁` on that subspace then iterates, giving the
geometric law `‖T^n x‖ ≤ ρ₁^n ‖x‖` — the `hsub` hypothesis of S1, now discharged.

SCOPE. This is uniformity in the SEPARATION `n` at one volume. It says nothing about the volume, and
`ρ₁` here is whatever the per-step bound is at that volume. Volume-uniformity is the separate claim
that `ρ₁` can be chosen independently of the volume, i.e. the intensive input of §3–§5. -/

open MassGap.Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The vacuum-orthogonal subspace is transfer-invariant.** `⟨Ω, Tx⟩ = ⟨TΩ, x⟩ = ⟨Ω, x⟩ = 0`, using
self-adjointness (`TransferData.T_symm`, which is what reflection positivity supplies) and the vacuum
eigenvector `TΩ = Ω`. Without self-adjointness this fails, so the step is genuinely RP's. -/
theorem inner_vac_Tq (D : TransferData A) {x : GNS D.toReflForm}
    (hx : inner ℝ D.vacGNS x = (0 : ℝ)) :
    inner ℝ D.vacGNS (D.Tq x) = (0 : ℝ) := by
  have h := D.Tq_isSymmetric D.vacGNS x
  rw [D.Tq_vacGNS] at h
  rw [← h]
  exact hx

/-- Iterating `inner_vac_Tq`: every power of the transfer operator keeps a vacuum-orthogonal vector
vacuum-orthogonal. -/
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

/-- **`‖T^n x‖ ≤ ρ₁^n ‖x‖` on the vacuum complement.** A single-step bound `‖Ty‖ ≤ ρ₁‖y‖` on
vacuum-orthogonal `y` iterates, because the subspace it holds on is invariant (`inner_vac_Tq_pow`).
This is the geometric law `Mixing.gap_of_maximal_correlation` assumes; here it is a consequence of
reflection positivity plus the per-step bound. -/
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

/-- **S1's hypothesis, DERIVED.** In the exact form `Mixing.gap_of_maximal_correlation` consumes:
`σ n ≤ σ 0 · ρ₁^n` for `σ n = ‖T^n x‖`. The tree previously took this as an assumption and credited
it to RP in prose; this is the proof. -/
theorem rp_sub_geometric (D : TransferData A) {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) (n : ℕ) :
    ‖(D.Tq ^ n) x‖ ≤ ‖(D.Tq ^ 0) x‖ * ρ₁ ^ n := by
  rw [show (D.Tq ^ 0) x = x from by simp, mul_comm]
  exact norm_Tq_pow_le D hρ0 hρ hx n

/-- **One cut controls every separation — from reflection positivity, at one volume.** A per-step
contraction `ρ₁ < 1` on the vacuum complement sends `‖T^n x‖ → 0`. `Mixing.gap_of_maximal_correlation`
with its `hsub` now supplied rather than assumed.

NOT A VOLUME STATEMENT. `n` is the Euclidean-time separation. `ρ₁` is the per-step bound at whatever
volume `D` describes, and nothing here makes it volume-independent; that is §3–§5's intensive input.
The equality `ρ'(n) = ρ'(1)^n` asserted in `MassGap.lean`'s `CellSpectrum` import line is neither
proved nor needed — the inequality above is what every consumer uses. -/
theorem rp_gap_of_one_cut (D : TransferData A) {ρ₁ : ℝ} (hρ0 : 0 ≤ ρ₁) (hρ1 : ρ₁ < 1)
    (hρ : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ ρ₁ * ‖y‖)
    {x : GNS D.toReflForm} (hx : inner ℝ D.vacGNS x = (0 : ℝ)) :
    Filter.Tendsto (fun n => ‖(D.Tq ^ n) x‖) Filter.atTop (nhds 0) := by
  refine gap_of_maximal_correlation hρ0 hρ1 (fun _ => norm_nonneg _) (fun n => ?_)
  exact rp_sub_geometric D hρ0 hρ hx n

/-! ## Axiom footprints

Foundational-only is exactly `{propext, Classical.choice, Quot.sound}`. Every declaration above is
printed; nothing in this file introduces an axiom. -/

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
