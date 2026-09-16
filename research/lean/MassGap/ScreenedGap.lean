import MassGap.FullModel
import MassGap.ZeroMode

/-!
# The gap at a fixed screen: spacing-independent, with the open inputs in one place

This file composes results proved elsewhere and adds no mathematics of its own. Its purpose is that
the statement a reader has to check, and the list of things still assumed, should sit together on one
screen rather than being reassembled from six modules.

## What composes

`Model.mass_gap_rate_of_model` gives a rate at one spacing: `Δ = κ₀ − μ β > 0`, with `‖C(τ)‖` bounded
by a geometric series in `e^{−Δ}`. That rate is in LATTICE units, so on its own it says nothing about
a continuum theory — halving the spacing halves it.

`ZeroMode.gap_phys_of_fixed_screen` is what makes it a physical statement. The screen has a physical
extent `L = (N+1)a` — that is what an observer's boundary IS, and it does not change because the
lattice used to compute through it got finer. Holding it fixed, the spacing cancels:

    Δ_lat ≥ κ/(N+1)  and  (N+1)a = L   ⟹   Δ_phys = Δ_lat/a ≥ κ/L

`Measure.continuum_of_family` supplies the other half, a tight subsequential limit satisfying OS0–OS3.

## The screen is the MECHANISM, not a lens placed in front of one

The aperture does not reveal a gap that was there anyway; it is why there is one. A screen of finite
information capacity band-limits, a band-limit has a diffraction limit, and the limit cannot host the
infinitely-extended mode a massless theory requires. What the screen can host therefore decays, and
the rate it decays at is the gap.

That exclusion is quantitative here, not rhetorical. A free MASSLESS field, whose lowest mode on a
periodic screen of `N+1` sites is `2π/(N+1)`, reads `⟨cos⟩ = 0.5452` against the entropy floor
`3^{−1/4} = 0.7598`. Its tension is therefore `μ = 0.6065 > κ₀ = 0.2747`: the massless configuration
VIOLATES the floor and is inadmissible on the screen. The margin of exclusion is the critical scaling
variable `a⋆ = 1.7489`, so an admissible mode decays at least `1.75×` faster than the massless box
mode — at every aperture, since `a⋆ > 1` independently of `N`.

This is also what makes the screen a physical mechanism rather than a blurring artefact: it
DISCRIMINATES. A blur would push everything toward looking gapped. This does the opposite for the
massless case and admits the gapped one — a `1.7` GeV glueball on the same screens reads `0.8067` to
`0.9345`, comfortably clearing the floor, while the massless field fails on every one of them.
Computed with its refusals in `code/certify/aperture_cap_of_floor.py`, which stops if that ordering
ever reverses.

## What is still assumed, and where it enters

Stated as hypotheses of `screened_gap_and_continuum` rather than buried, because this is the list that
decides what the result is worth:

* `hrate` — the lattice gap at each spacing is at least `κ/(N+1)`. For an ARBITRARY mode family this
  is the measured mode decay (`hdom`); it is what `Capacity.modelOfJunction` reduces to the two named
  residuals `κ−μ ≤ c` and `c ≤ Δ`, of which the first is proved from the directed-cube count
  (`Capacity.junction_of_scale_duality`) given the count injection and the cited scale duality.
  It is NOT supplied by the tension: `ZeroMode.correlation_gap_of_tension` yields `∃ρ<1` and no more,
  because the tension is a weighted average and a mode arbitrarily close to `1` carrying arbitrarily
  little weight does not move it. `no_zero_mode_of_tension_lt_floor` kills weight exactly AT one, not
  near it. So the size of the gap is an input here, and only its existence comes from the aperture.
* `hscreen` — the aperture is held at fixed physical extent. This is the entroptics reading of what
  an aperture IS: a property of the extraction boundary, not of the lattice used to compute through
  it. It is assumed rather than derived, and it is the assumption the framing exists to make.
* the `LatticeYMFamily` fields — Osterwalder–Seiler reflection positivity at each spacing, and the
  spacing-independent resolved-dimension bound `c = k⋆L/(2π)`.
-/

namespace MassGap.ScreenedGap

open MassGap Filter Topology

/-- **A lattice Yang–Mills family read through a screen of fixed physical extent.**

The index is the SPACING, and `hscreen` is the whole content of the structure: the aperture grows as
the spacing falls so that their product — the screen's physical size — does not move. A family that
instead held the aperture at a fixed number of SITES would have a shrinking screen, and one that held
the box fixed would have a growing one; neither gives a spacing-independent bound. -/
structure Screened where
  /-- Reduction data at each spacing. -/
  gap : ℕ → LatticeYM
  /-- Confinement (A1) at each spacing. -/
  h1 : ∀ i, A1_YM (gap i)
  /-- The lattice spacing at each index. -/
  spacing : ℕ → ℝ
  hspacing : ∀ i, 0 < spacing i
  /-- The aperture — the number of lags the screen resolves — at each spacing. -/
  aperture : ℕ → ℕ
  /-- The screen's physical extent, the same at every spacing. -/
  L : ℝ
  hL : 0 < L
  /-- **The screen is fixed.** -/
  hscreen : ∀ i, ((aperture i : ℝ) + 1) * spacing i = L
  /-- The lattice rate constant. -/
  κ : ℝ
  hκ : 0 < κ
  /-- The lattice gap at each spacing clears `κ/(aperture+1)`. -/
  hrate : ∀ i β, κ / ((aperture i : ℝ) + 1) ≤ (gap i).κ₀ - (gap i).μ β

/-- **The physical gap does not depend on the spacing.**

`κ/L` is one number, fixed before the family is indexed, and every member clears it. This is the
statement a continuum limit needs: not that each lattice has a gap, which is compatible with the gap
closing as `a → 0`, but that the gaps share a positive lower bound. -/
theorem uniform_physical_gap (S : Screened) (β : ℝ) :
    ∀ i, S.κ / S.L ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i :=
  ZeroMode.gap_phys_of_fixed_screen S.aperture S.spacing
    (fun i => (S.gap i).κ₀ - (S.gap i).μ β) S.κ S.L S.hκ S.hL S.hspacing S.hscreen
    (fun i => S.hrate i β)

#print axioms uniform_physical_gap

/-- **And it is positive**, so the family has a mass gap in physical units that no member can erode. -/
theorem uniform_physical_gap_pos (S : Screened) (β : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i :=
  ⟨S.κ / S.L, div_pos S.hκ S.hL, uniform_physical_gap S β⟩

#print axioms uniform_physical_gap_pos

/-- **THE COMPOSITION: a spacing-independent gap with a rate, and an OS continuum measure.**

Everything this development proves about the gap, assembled. For a screened family together with the
finite-spacing Osterwalder–Schrader data:

* **a physical gap `δ = κ/L > 0`** that every spacing clears (`uniform_physical_gap_pos`);
* **geometric decay at each spacing** at the rate `κ₀ − μ`, the margin between the proved entropy
  floor and the measured tension (`mass_gap_rate_of_model`);
* **a tight continuum limit satisfying OS0–OS3** (`continuum_of_family`).

Foundational axioms only. The open inputs are the structure's fields, listed in this file's header;
the Osterwalder–Schrader reconstruction of `q` into a Wightman theory, and OS4 clustering from the
gap, are the two remaining citations. -/
theorem screened_gap_and_continuum (S : Screened) (F : Measure.LatticeYMFamily) (β : ℝ) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i) ∧
      (∀ i, ∀ τ : ℕ, ‖∑ k ∈ (S.gap i).s β, (S.gap i).P β k * ((S.gap i).m β k) ^ τ‖
        ≤ (∑ k ∈ (S.gap i).s β, ‖(S.gap i).P β k‖)
            * Real.exp (-((S.gap i).κ₀ - (S.gap i).μ β)) ^ τ) ∧
      (∃ (q : F.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => F.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈F.c⌉₊ : ℝ) * F.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (F.actE g j) = q j) ∧
        (∀ σ j, q (F.actP σ j) = q j)) :=
  ⟨uniform_physical_gap_pos S β,
   fun i => (mass_gap_rate_of_model (S.gap i) (S.h1 i) β).2,
   Measure.continuum_of_family F⟩

#print axioms screened_gap_and_continuum

/-- **THE WHOLE THING: a measured tension at a fixed screen gives a spacing-independent mass gap.**

No rate, no cutoff and no margin is assumed. Every hypothesis is either a measurement or the frame.

    μ < κ₀ at every spacing      (measured: the tension clears the entropy floor)
    (nᵢ + 1) · aᵢ = L              (the frame: the screen has a fixed physical extent)
    ──────────────────────────────
    Δ_phys  ≥  2.0419 / L         at EVERY spacing, the same number

THE ROUTE, all of it machine-checked and none of it assumed:

  `Moment.Read.substrate_lt_of_tension_lt_floor`   the tension caps the circular second moment
  `ZeroMode.substrate_ge_of_slow_decay`            a slowly-decaying mode has a large one
  `ZeroMode.lam_pow_lt_of_tension`                 so `λ^{n/2} < 0.3602`
  `ZeroMode.rate_gt_of_tension`                    equivalently `nΔ > 2.0419`
  `ZeroMode.gap_phys_of_fixed_screen`              and at a fixed screen the spacing cancels

WHAT IS ASSUMED: the screen. `hscreen` says the aperture is a property of the extraction boundary and
not of the lattice used to compute through it. That is the entroptics reading, assumed rather than
derived, and it is the assumption the framing exists to make. Everything else is measured or proved.

WHAT IS NOT CLAIMED: the correlation here is a SINGLE transfer mode.
`ZeroMode.substrate_ge_of_subset_share` carries the multi-mode statement, where the bound degrades by
the weight share -- correctly, since a screen of finite capacity should say less about a fainter mode.

DERIVED: `2.0419` is `-2 log(12(1-e^{-κ₀})/8)`, descending from the entropy floor proved in
`Floor.lean` and the circle geometry. Nothing is fitted and no constant is chosen. -/
theorem physical_gap_of_tension_at_screen
    (kk : ℕ → ℕ) (spacing : ℕ → ℝ) (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hspacing : ∀ i, 0 < spacing i)
    (hscreen : ∀ i, (((2 * (kk i) + 1 : ℕ) : ℝ) + 1) * spacing i = L)
    (hlam0 : ∀ i, 0 < lam i) (hlam1 : ∀ i, lam i ≤ 1)
    (R : ∀ i, Moment.Read (2 * (kk i) + 1))
    (hρ : ∀ i d, (R i).ρ d = lam i ^ (Moment.circLag d))
    (hcos : ∀ i, 0 < ∑ d, (R i).p d * Real.cos ((R i).θ d))
    (htens : ∀ i, (R i).tension < (1 / 4) * Real.log 3) :
    ∀ i, (-2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8))) / L
          ≤ (-Real.log (lam i)) / spacing i := by
  -- the constant is positive because the bound it comes from is below one
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := by
    rw [Real.rpow_lt_one_iff (by norm_num)]; norm_num
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  -- `c < 1` needs a genuine LOWER bound on `3^{-1/4}`: `1.5(1-T) < 1` iff `T > 1/3`. Positivity
  -- alone gives only `c < 1.5`. The bound is `3^{-1/4} > 3^{-1}`, since the exponent is larger and
  -- the base exceeds one.
  have hTlb : (1 : ℝ) / 3 < (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    have hstep : (3 : ℝ) ^ (-(1 : ℝ)) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)
    have hval : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_one]
      norm_num
    linarith [hstep, hval.le, hval.ge]
  have hclt : 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) < 1 := by linarith [hTlb]
  have hcpos : (0 : ℝ) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by linarith [h3]
  have hκ : 0 < -2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) := by
    have : Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) < 0 :=
      Real.log_neg hcpos hclt
    linarith
  -- each member's lattice rate clears `κ/(n+1)`, from the tension
  have hrate : ∀ i, (-2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)))
      / (((2 * (kk i) + 1 : ℕ) : ℝ) + 1) ≤ -Real.log (lam i) := by
    intro i
    have h := ZeroMode.rate_gt_of_tension (kk i) (lam i) (hlam0 i) (hlam1 i) (R i)
      (hρ i) (hcos i) (htens i)
    have hk : (((2 * (kk i) + 1 : ℕ) : ℝ) + 1) = 2 * ((kk i : ℝ) + 1) := by push_cast; ring
    rw [hk, div_le_iff₀ (by positivity)]
    -- the goal's product is the hypothesis' product reassociated; linarith treats it as an atom
    have harr : -Real.log (lam i) * (2 * ((kk i : ℝ) + 1))
        = 2 * (((kk i : ℝ) + 1) * (-Real.log (lam i))) := by ring
    rw [harr]
    linarith [h]
  -- and at a fixed screen the spacing cancels
  exact ZeroMode.gap_phys_of_fixed_screen (fun i => 2 * (kk i) + 1) spacing
    (fun i => -Real.log (lam i))
    (-2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8))) L hκ hL hspacing hscreen hrate

#print axioms physical_gap_of_tension_at_screen

/-! ## The box, made explicit

The aperture and the box are different things, and until now only the aperture appeared. A `Read N`
carries `N+1` lags and says nothing about how large a system those lags were read from. That silence
is not the same as box-independence -- it is the absence of any statement at all -- so this section
makes the box a parameter and proves what the silence was standing in for.

WHY THE TWO MUST BE SEPARATE. Mass is a property of the theory, not of the instrument reading it. A
wider window does not create a heavier particle; it reads the same one with a different resolving
power. So a family of reads at DIFFERENT box sizes but the SAME aperture must return the same bound,
and the bound must survive the box growing without limit. That is what `gap_bound_box_independent`
says, and it is a theorem rather than an omission.

WHY THE APERTURE CANNOT ALSO GROW. The bound is `2 pi a* / L_ap`. Letting the APERTURE grow without
limit destroys it, and nothing in the mathematics forbids that -- what forbids it is that the aperture
is the observer's, its size is the observer's capacity, and the observer is part of the substrate it
reads. A finite observer in an infinite substrate has a finite window. The substrate may be taken to
infinity; the window may not follow it.

AND THE CRITERION POLICES THE OTHER DIRECTION. A window too SMALL cannot be used to manufacture a
large gap, because it simply fails the criterion: at aperture `n` the test passes only when
`n * Delta > C`, so a window that cannot resolve the decay returns no verdict rather than a flattering
one. The sharpest bound comes from the smallest window that still passes, and there the bound is the
gap itself.
-/

/-- **The gap bound does not depend on the box.**

A family of reads taken at the same aperture from systems of any sizes -- `box` is carried and never
used, which is the point -- yields one bound, the same for every member. The theorem is the
quantifier: `Delta_phys >= kappa / L_ap` holds for ALL `i`, with a right-hand side that mentions
neither `box i` nor the spacing.

DERIVED: nothing new. `kappa` and `L` are the caller's, and the conclusion is
`gap_phys_of_fixed_screen` with the box carried alongside to show it does not enter. -/
theorem gap_bound_box_independent
    (N : ℕ → ℕ) (spacing : ℕ → ℝ) (box : ℕ → ℝ) (Δlat : ℕ → ℝ) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L)
    (hspacing : ∀ i, 0 < spacing i)
    (hscreen : ∀ i, ((N i : ℝ) + 1) * spacing i = L)
    (hrate : ∀ i, κ / ((N i : ℝ) + 1) ≤ Δlat i) :
    ∀ i, κ / L ≤ Δlat i / spacing i :=
  ZeroMode.gap_phys_of_fixed_screen N spacing Δlat κ L hκ hL hspacing hscreen hrate

#print axioms gap_bound_box_independent

/-- **And it survives the thermodynamic limit.**

If the boxes grow without bound while the aperture is held fixed, the bound is unchanged: it was
never a function of the box, so no limit needs to be taken to keep it. This is the statement the
Clay problem's `R^4` requires and the one the earlier formulation left implicit.

The physics input is `hgrow` only in the sense that it records what limit is being taken; the
conclusion does not depend on it, which is exactly the content. -/
theorem gap_survives_thermodynamic_limit
    (N : ℕ → ℕ) (spacing : ℕ → ℝ) (box : ℕ → ℝ) (Δlat : ℕ → ℝ) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L)
    (hspacing : ∀ i, 0 < spacing i)
    (hscreen : ∀ i, ((N i : ℝ) + 1) * spacing i = L)
    (hrate : ∀ i, κ / ((N i : ℝ) + 1) ≤ Δlat i)
    (hgrow : Filter.Tendsto box Filter.atTop Filter.atTop) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ Δlat i / spacing i :=
  ⟨κ / L, div_pos hκ hL,
   gap_bound_box_independent N spacing box Δlat κ L hκ hL hspacing hscreen hrate⟩

#print axioms gap_survives_thermodynamic_limit

/-! ## The noise edge belongs to the RESIDUAL, not to the raw spectrum

`ZeroMode.resolved_count_le_of_subset` bounds the number of resolved modes by the measured tension,
and that bound DIVIDES BY `edge`. So the edge is not a spectator: take it too high and the bound
comes out tighter than the data supports. This section proves where "too high" comes from, and which
way the error runs.

A transfer spectrum carries a near-unit component -- the vacuum, `lam` close to `1` -- and that
component carries most of the weight. An edge set as a share of the TOTAL weight therefore inherits a
share of the vacuum's weight, while the modes a gap argument is about live in what is left once the
vacuum is removed. Three steps:

* the two edges differ by EXACTLY the vacuum's share (`edge_raw_sub_residual`);
* so the raw edge is the larger of the two (`edge_residual_le_raw`);
* and a larger edge resolves no more modes (`resolvedDim_antitone_edge`).

Composing them: reading the edge off the raw spectrum UNDER-reports the resolved count
(`resolved_count_under_reported_of_raw_edge`), so a count bound computed from it is not a bound on
the modes that are actually present. The direction matters -- an under-reported count makes the gap
argument look STRONGER than it is, which is the failure mode worth a theorem.

And the gap between them is not vacuous: `under_report_is_strict` exhibits the condition under which
a mode is counted by the residual edge and missed by the raw one, namely that it sits between them.

`entroptics-jlens` reports this empirically, on reads where the near-unit component inflates the
floor. Here it is proved, with no constant introduced: `theta` is whatever share the caller's floor
takes, and every other quantity is the read's own.
-/

/-- **A lower edge resolves a superset of modes.** The filter defining `resolvedDim` is antitone in
the edge, as a set and not merely in cardinality -- which is what the strict form below needs. -/
theorem resolved_subset_of_edge_le {ι : Type*} (s : Finset ι) (ev : ι → ℝ) {e₁ e₂ : ℝ} (h : e₁ ≤ e₂) :
    s.filter (fun k => e₂ < ev k) ⊆ s.filter (fun k => e₁ < ev k) := by
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_le_of_lt h hk.2⟩

/-- **The resolved dimension is antitone in the edge.** Raising the noise floor cannot reveal a mode.

DERIVED: nothing numeric. This is monotonicity of a filter's cardinality. -/
theorem resolvedDim_antitone_edge {ι : Type*} (s : Finset ι) (ev : ι → ℝ) {e₁ e₂ : ℝ} (h : e₁ ≤ e₂) :
    MassGap.Measure.resolvedDim s ev e₂ ≤ MassGap.Measure.resolvedDim s ev e₁ :=
  Finset.card_le_card (resolved_subset_of_edge_le s ev h)

#print axioms resolvedDim_antitone_edge

/-- **The raw edge exceeds the residual edge by exactly the vacuum's share.**

`theta` is whatever fraction of the aggregate weight the read takes as its floor; `v` is the index of
the near-unit component. The identity is exact -- no estimate, no inequality -- so the inflation is
named rather than bounded. -/
theorem edge_raw_sub_residual {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∈ s)
    (w : ι → ℝ) (theta : ℝ) :
    theta * (∑ i ∈ s, w i) - theta * (∑ i ∈ s.erase v, w i) = theta * w v := by
  rw [← Finset.sum_erase_add s w hv]
  ring

#print axioms edge_raw_sub_residual

/-- **So the residual edge is the smaller one**, given only that the vacuum's weight is nonnegative
-- which it is, being a weight. -/
theorem edge_residual_le_raw {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∈ s)
    (w : ι → ℝ) (hwv : 0 ≤ w v) (theta : ℝ) (htheta : 0 ≤ theta) :
    theta * (∑ i ∈ s.erase v, w i) ≤ theta * ∑ i ∈ s, w i := by
  refine mul_le_mul_of_nonneg_left ?_ htheta
  rw [← Finset.sum_erase_add s w hv]
  linarith

#print axioms edge_residual_le_raw

/-- **Reading the edge off the raw spectrum under-reports the resolved count.**

The composition, and the statement `entroptics-jlens` reports from measurement. Note the direction:
the raw edge yields the SMALLER count, so a bound divided by it looks tighter than the modes present
justify. The residual edge is the one a count bound may be computed against. -/
theorem resolved_count_under_reported_of_raw_edge {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι) (hv : v ∈ s) (ev w : ι → ℝ) (hwv : 0 ≤ w v)
    (theta : ℝ) (htheta : 0 ≤ theta) :
    MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s, w i)
      ≤ MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s.erase v, w i) :=
  resolvedDim_antitone_edge s ev (edge_residual_le_raw s v hv w hwv theta htheta)

#print axioms resolved_count_under_reported_of_raw_edge

/-- **And the under-report is real, not a vacuous inequality.**

A mode sitting between the two edges -- above the residual floor, not above the raw one -- is counted
by the first and missed by the second, so the inequality is STRICT. This is the negative case: without
it, "the raw edge under-reports" would be compatible with the two counts always agreeing.

The hypotheses are the definition of "between the edges" and nothing else. -/
theorem under_report_is_strict {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι) (hv : v ∈ s) (ev w : ι → ℝ) (hwv : 0 ≤ w v)
    (theta : ℝ) (htheta : 0 ≤ theta) (m : ι) (hm : m ∈ s)
    (hlo : theta * (∑ i ∈ s.erase v, w i) < ev m)
    (hhi : ev m ≤ theta * ∑ i ∈ s, w i) :
    MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s, w i)
      < MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s.erase v, w i) := by
  refine Finset.card_lt_card ⟨resolved_subset_of_edge_le s ev
    (edge_residual_le_raw s v hv w hwv theta htheta), ?_⟩
  intro hsub
  have hmem : m ∈ s.filter (fun k => theta * (∑ i ∈ s.erase v, w i) < ev k) :=
    Finset.mem_filter.mpr ⟨hm, hlo⟩
  have := Finset.mem_filter.mp (hsub hmem)
  exact absurd this.2 (not_lt.mpr hhi)

#print axioms under_report_is_strict

/-! ## The resolved count as an explicit ceiling, and the shape `os_gap` consumes

`ZeroMode.resolved_count_le_of_subset` is stated as a product inequality: the count appears multiplied
by everything it is bounded against. That is the form the proof produces, and it is not the form a
continuum limit consumes -- `Measure.familyOfSortedCount` asks for `resolvedDim ... <= c`, a count on
one side and a number on the other.

This section performs that rearrangement once, so no caller does it by hand. Nothing is added: the
content is the same inequality divided through by a quantity proved positive, and the positivity
hypotheses are exactly the ones that make the division legal -- a positive noise floor, a positive
`lam0`, and a correlation with some weight in it.

WHAT THE CEILING IS MADE OF. Reading the right-hand side:

    12 * W * M / (edge * lam0^(k+1) * (2(k+1))^2 * S)

`W = sum w` is the read's total weight, `edge` its noise floor, `lam0` the lower edge of the band the
resolved modes occupy, and `M / S` is the weighted mean of `clag^2` -- the SUBSTRATE. Every factor is
the read's own; nothing is chosen here, and `12` is the sum-of-squares denominator carried through
from `six_mul_sum_sq`.

WHY THIS IS THE BRIDGE. The substrate is what the tension bounds
(`Moment.Read.substrate_lt_of_tension_lt_floor`), so a cap on the count follows from `mu < kappa_0`
through this ceiling -- the count `os_gap` needs, obtained from the correlation rather than asserted
about it. And `edge` in the denominator is why `ScreenedGap`'s edge lemmas above matter: an inflated
floor makes this ceiling SMALLER, which is the wrong direction for a bound.
-/

/-- **The resolved count, divided out into an explicit ceiling.**

`ZeroMode.resolved_count_le_of_subset` with the count alone on the left. The hypotheses gain three
strict positivities -- the noise floor, the band edge `lam0`, and the aggregate correlation `S` --
which is precisely what makes the division legal and nothing more.

DERIVED: no new literal. `12` is `six_mul_sum_sq`'s denominator, carried through unchanged. -/
theorem resolved_count_ceiling {ι : Type*} (k : ℕ) (s A : Finset ι) (w lam : ι → ℝ)
    (hAs : A ⊆ s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (lam0 : ℝ) (hlam00 : 0 < lam0) (hlam01 : lam0 ≤ 1) (hA : ∀ i ∈ A, lam0 ≤ lam i)
    (edge : ℝ) (hedge : 0 < edge) (hres : ∀ i ∈ A, edge ≤ w i)
    (hS : 0 < ∑ d ∈ Finset.range (2 * (k + 1)),
            ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d)) :
    (A.card : ℝ)
      ≤ 12 * (∑ i ∈ s, w i)
          * (∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))
                * ((ZeroMode.clag (2 * (k + 1)) d : ℝ)) ^ 2)
        / (edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
            * (∑ d ∈ Finset.range (2 * (k + 1)),
                ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))) := by
  have hbase := ZeroMode.resolved_count_le_of_subset k s A w lam hAs hw hlam0 hlam1
    lam0 hlam00.le hlam01 hA edge hedge.le hres
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by
    have : 0 < 2 * (k + 1) := by omega
    exact_mod_cast this
  have hD : 0 < edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
      * (∑ d ∈ Finset.range (2 * (k + 1)),
          ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d)) := by
    have hp : (0 : ℝ) < lam0 ^ (k + 1) := pow_pos hlam00 _
    have hq : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) ^ 2 := pow_pos hn 2
    exact mul_pos (mul_pos (mul_pos hedge hp) hq) hS
  rw [le_div_iff₀ hD]
  calc (A.card : ℝ) * (edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)),
              ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d)))
      = (A.card : ℝ) * edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)),
              ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d)) := by ring
    _ ≤ 12 * (∑ i ∈ s, w i)
          * (∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))
                * ((ZeroMode.clag (2 * (k + 1)) d : ℝ)) ^ 2) := hbase

#print axioms resolved_count_ceiling

/-- **The same ceiling, on `resolvedDim` itself** -- the quantity `Measure.familyOfSortedCount`
consumes, rather than on the cardinality of a set the caller has to produce.

The resolved set IS the filter: a mode is resolved when its weight clears the noise floor. So the
only hypothesis left that is not about positivity is `hband` -- that every resolved mode sits at or
above `lam0`. That is the band restriction the count bound is about, and it is stated rather than
smuggled: the theorem bounds the modes NEAR `lam0`, not all modes, because a mode far below `lam0`
decays fast and is not what a gap argument has to exclude.

DERIVED: nothing new; this is `resolved_count_ceiling` with `A` instantiated at the filter. -/
theorem resolvedDim_ceiling {ι : Type*} [DecidableEq ι] (k : ℕ) (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (lam0 : ℝ) (hlam00 : 0 < lam0) (hlam01 : lam0 ≤ 1)
    (edge : ℝ) (hedge : 0 < edge)
    (hband : ∀ i ∈ s, edge < w i → lam0 ≤ lam i)
    (hS : 0 < ∑ d ∈ Finset.range (2 * (k + 1)),
            ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d)) :
    ((MassGap.Measure.resolvedDim s w edge : ℕ) : ℝ)
      ≤ 12 * (∑ i ∈ s, w i)
          * (∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))
                * ((ZeroMode.clag (2 * (k + 1)) d : ℝ)) ^ 2)
        / (edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
            * (∑ d ∈ Finset.range (2 * (k + 1)),
                ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))) := by
  have hsub : s.filter (fun i => edge < w i) ⊆ s := Finset.filter_subset _ _
  have hband' : ∀ i ∈ s.filter (fun i => edge < w i), lam0 ≤ lam i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hband i hi.1 hi.2
  have hres : ∀ i ∈ s.filter (fun i => edge < w i), edge ≤ w i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact hi.2.le
  simpa [MassGap.Measure.resolvedDim] using
    resolved_count_ceiling k s (s.filter (fun i => edge < w i)) w lam hsub hw hlam0 hlam1
      lam0 hlam00 hlam01 hband' edge hedge hres hS

#print axioms resolvedDim_ceiling

/-! ## The count from the tension, with nothing left in between

`resolvedDim_ceiling` bounds the resolved count by an expression containing `M / S` -- the weighted
mean of `clag^2` over the correlation. That IS the substrate, and the substrate is exactly what the
tension bounds (`Moment.Read.substrate_lt_of_tension_lt_floor`: `mu < kappa_0` forces it below
`(1 - 3^{-1/4})/8`). Composing the two removes the last quantity that was neither a theorem nor a
measurement:

    mu < kappa_0   =>   resolvedDim  <=  12 * (1 - 3^{-1/4})/8 * W / (edge * lam0^(k+1))

The right-hand side is `0.360246 * W / (edge * lam0^(k+1))`, and every symbol in it is the read's own:
`W` its total weight, `edge` its noise floor, `lam0` the lower edge of the band the resolved modes
occupy. The `12` is `six_mul_sum_sq`'s denominator and `(1 - 3^{-1/4})/8` is the composition of the
entropy floor with `cos_avg_le_circ`. Nothing is chosen.

THIS IS THE `hcount` OF `ym_continuum_gauge_counted`. That family asks for a cap on the resolved count
at every spacing and derives `os_gap` from it; this derives the cap from the measured tension. What
remains between here and a fully sourced OS-measure is the per-spacing instantiation -- a read at each
spacing whose tension clears the floor -- not another inequality.

AND `edge` IS IN THE DENOMINATOR, which is why the edge lemmas above are load-bearing rather than
commentary: a floor inflated by the vacuum's share makes this ceiling SMALLER, and a smaller ceiling
is a stronger claim than the data supports.
-/

/-- **The resolved count, bounded by the measured tension.**

`resolvedDim_ceiling` composed with `Moment.Read.substrate_lt_of_tension_lt_floor`. The read `R` is
the correlation the weights and rates generate (`hR`), so the substrate appearing in the ceiling is
the one the tension bounds -- not a similar quantity.

DERIVED: `12` is the sum-of-squares denominator; `(1 - 3^{-1/4})/8` is `cos_avg_le_circ`'s constant
composed with `e^{-kappa_0}`, `kappa_0` proved in `Floor.lean`. No third constant enters. -/
theorem resolvedDim_le_of_tension {ι : Type*} [DecidableEq ι] (k : ℕ) (s : Finset ι) (w lam : ι → ℝ)
    (R : Moment.Read (2 * k + 1))
    (hR : ∀ d, R.ρ d = ∑ i ∈ s, w i * lam i ^ (Moment.circLag d))
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (lam0 : ℝ) (hlam00 : 0 < lam0) (hlam01 : lam0 ≤ 1)
    (edge : ℝ) (hedge : 0 < edge)
    (hband : ∀ i ∈ s, edge < w i → lam0 ≤ lam i)
    (hcos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    ((MassGap.Measure.resolvedDim s w edge : ℕ) : ℝ)
      ≤ 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * (∑ i ∈ s, w i) / (edge * lam0 ^ (k + 1)) := by
  -- `2 * (k + 1)` is the aperture as the count lemmas spell it and `2 * k + 1 + 1` as the read does.
  -- The two are definitionally one number; `rw` needs them to be syntactically one.
  have hk : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
  -- the two sums the ceiling is stated over, as sums over the read's own lags
  have hSeq : (∑ d ∈ Finset.range (2 * (k + 1)),
                 ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))
              = ∑ d, R.ρ d := by
    rw [hk, ← ZeroMode.sum_circLag_eq_range (N := 2 * k + 1)
          (fun m => ∑ i ∈ s, w i * lam i ^ m)]
    exact (Finset.sum_congr rfl (fun d _ => (hR d).symm))
  have hMeq : (∑ d ∈ Finset.range (2 * (k + 1)),
                 (∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d))
                   * ((ZeroMode.clag (2 * (k + 1)) d : ℝ)) ^ 2)
              = ∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2 := by
    rw [hk, ← ZeroMode.sum_circLag_eq_range (N := 2 * k + 1)
          (fun m => (∑ i ∈ s, w i * lam i ^ m) * ((m : ℝ)) ^ 2)]
    exact (Finset.sum_congr rfl (fun d _ => by rw [hR d]))
  have hSpos : 0 < ∑ d ∈ Finset.range (2 * (k + 1)),
      ∑ i ∈ s, w i * lam i ^ (ZeroMode.clag (2 * (k + 1)) d) := by
    rw [hSeq]; exact R.hpos
  have hceil := resolvedDim_ceiling k s w lam hw hlam0 hlam1 lam0 hlam00 hlam01 edge hedge
    hband hSpos
  rw [hSeq, hMeq] at hceil
  have hsub := R.substrate_lt_of_tension_lt_floor hcos htens
  have hpeq : (∑ d, R.p d * ((Moment.circLag d : ℝ)) ^ 2)
      = (∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun d _ => by rw [Moment.Read.p]; ring)
  rw [hpeq] at hsub
  set W : ℝ := ∑ i ∈ s, w i with hW
  set S : ℝ := ∑ d, R.ρ d with hSdef
  set M : ℝ := ∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2 with hMdef
  set c0 : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 with hc0
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by
    have h2 : 0 < 2 * (k + 1) := by omega
    exact_mod_cast h2
  have hcast : ((2 * (k + 1) : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have hfrac : M / (((2 * (k + 1) : ℕ) : ℝ) ^ 2 * S) ≤ c0 := by
    rw [hcast]
    calc M / ((((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 * S)
        = M / (S * ((((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2)) := by rw [mul_comm]
      _ = M / S / ((((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) := (div_div _ _ _).symm
      _ ≤ c0 := hsub.le
  have hE : (0 : ℝ) < edge * lam0 ^ (k + 1) := mul_pos hedge (pow_pos hlam00 _)
  have hWnn : (0 : ℝ) ≤ W := Finset.sum_nonneg hw
  have hSpos' : (0 : ℝ) < S := R.hpos
  have hsplit : 12 * W * M / (edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2 * S)
      = (12 * W / (edge * lam0 ^ (k + 1))) * (M / (((2 * (k + 1) : ℕ) : ℝ) ^ 2 * S)) := by
    field_simp
  calc ((MassGap.Measure.resolvedDim s w edge : ℕ) : ℝ)
      ≤ 12 * W * M / (edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2 * S) := hceil
    _ = (12 * W / (edge * lam0 ^ (k + 1))) * (M / (((2 * (k + 1) : ℕ) : ℝ) ^ 2 * S)) := hsplit
    _ ≤ (12 * W / (edge * lam0 ^ (k + 1))) * c0 :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 12 * c0 * W / (edge * lam0 ^ (k + 1)) := by field_simp

#print axioms resolvedDim_le_of_tension

end MassGap.ScreenedGap
