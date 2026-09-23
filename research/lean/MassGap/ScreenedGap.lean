import MassGap.FullModel
import MassGap.ZeroMode

/-!
# The gap at a fixed screen: spacing-independent, with the open inputs in one place

This file composes results proved elsewhere and adds no mathematics of its own. Its purpose is that
the statement a reader has to check, and the list of things assumed, sit together rather than being
reassembled from six modules.

## What composes

`Model.mass_gap_rate_of_model` gives a rate at one spacing: `Δ = κ₀ − μ β > 0`, with `‖C(τ)‖` bounded
by a geometric series in `e^{−Δ}`. That rate is in lattice units, so halving the spacing halves it.

`ZeroMode.gap_phys_of_fixed_screen` converts it. The screen has a physical extent `L = (N+1)a`;
holding that fixed makes the spacing cancel:

    Δ_lat ≥ κ/(N+1)  and  (N+1)a = L   ⟹   Δ_phys = Δ_lat/a ≥ κ/L

`Measure.continuum_of_family` supplies a tight subsequential limit satisfying OS0–OS3.

## What the screen excludes

A screen of finite information capacity band-limits, a band-limit has a diffraction limit, and the
limit cannot host the infinitely-extended mode a massless theory requires.

`code/certify/aperture_cap_of_floor.py` computes that exclusion. A free massless field, whose lowest
mode on a periodic screen of `N+1` sites is `2π/(N+1)`, reads `⟨cos⟩ = 0.5452` against the entropy
floor `3^{−1/4} = 0.7598`, so its tension is `μ = 0.6065 > κ₀ = 0.2747` and the massless
configuration is inadmissible on the screen. The margin of exclusion is the critical scaling variable
`a⋆ = 1.7489`, which does not depend on `N`, so an admissible mode decays at least `1.75×` faster
than the massless box mode at every aperture. A `1.7` GeV glueball on the same screens reads `0.8067`
to `0.9345`, clearing the floor, while the massless field fails on every one of them; the script
refuses to report if that ordering reverses.

## What is assumed, and where it enters

These are hypotheses — fields of `Screened`, or arguments of `screened_gap_and_continuum` — rather
than facts proved in this development:

* `hrate` — the lattice gap at each spacing is at least `κ/(N+1)`. For an arbitrary mode family this
  is the measured mode decay; `Capacity.modelOfJunction` reduces it to the two named residuals
  `κ−μ ≤ c` and `c ≤ Δ`, of which the first follows from the directed-cube count
  (`Capacity.junction_of_scale_duality`) given the count injection and the cited scale duality.
  The tension does not supply it: `ZeroMode.correlation_gap_of_tension` yields `∃ρ<1` and no more,
  because the tension is a weighted average and a mode arbitrarily close to `1` carrying arbitrarily
  little weight does not move it, while `ZeroMode.no_zero_mode_of_tension_lt_floor` removes weight
  at one rather than near it. So the size of the gap is an input, and its existence is what the
  aperture gives.
* `hscreen` — the aperture is held at fixed physical extent, a property of the extraction boundary
  rather than of the lattice used to compute through it.
* the `Measure.LatticeYMFamily` fields — Osterwalder–Seiler reflection positivity at each spacing,
  and the spacing-independent resolved-dimension bound `c = k⋆L/(2π)`.
-/

namespace MassGap.ScreenedGap

open MassGap Filter Topology

/-- A lattice Yang–Mills family read through a screen of fixed physical extent.

The index is the spacing. `hscreen` is what distinguishes the structure: the aperture grows as the
spacing falls so that their product, the screen's physical size `L`, does not move. A family holding
the aperture at a fixed number of sites would have a shrinking screen, and one holding the box fixed
a growing one; neither gives a spacing-independent bound.

`gap i` is `LatticeYM` reduction data at each index, with confinement `h1` assumed there; `hrate`
assumes a lattice gap of at least `κ / (aperture i + 1)` at every index and every coupling. Both are
fields, so a caller supplies them. -/
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
  /-- The screen's extent is the same at every spacing. -/
  hscreen : ∀ i, ((aperture i : ℝ) + 1) * spacing i = L
  /-- The lattice rate constant. -/
  κ : ℝ
  hκ : 0 < κ
  /-- The lattice gap at each spacing clears `κ/(aperture+1)`. -/
  hrate : ∀ i β, κ / ((aperture i : ℝ) + 1) ≤ (gap i).κ₀ - (gap i).μ β

/-- The physical gap does not depend on the spacing:
`S.κ / S.L ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i` at every index `i`. The right-hand side is
the lattice rate divided by the spacing; the left-hand side is fixed before the family is indexed,
so the members share a lower bound rather than each merely having one.

Proved by `ZeroMode.gap_phys_of_fixed_screen` from the structure's `hrate` and `hscreen`. -/
theorem uniform_physical_gap (S : Screened) (β : ℝ) :
    ∀ i, S.κ / S.L ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i :=
  ZeroMode.gap_phys_of_fixed_screen S.aperture S.spacing
    (fun i => (S.gap i).κ₀ - (S.gap i).μ β) S.κ S.L S.hκ S.hL S.hspacing S.hscreen
    (fun i => S.hrate i β)

#print axioms uniform_physical_gap

/-- The bound of `uniform_physical_gap` is positive: there is a `δ` with `0 < δ` below
`((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i` at every `i`. The witness is `S.κ / S.L`, positive by
the structure's `hκ` and `hL`.

DERIVED: `0` is the strict positivity of `δ`. The value is `S.κ / S.L`, two fields of `Screened`;
nothing is chosen here. -/
theorem uniform_physical_gap_pos (S : Screened) (β : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ((S.gap i).κ₀ - (S.gap i).μ β) / S.spacing i :=
  ⟨S.κ / S.L, div_pos S.hκ S.hL, uniform_physical_gap S β⟩

#print axioms uniform_physical_gap_pos

/-- The composition: a spacing-independent gap with a rate, and an OS continuum measure.

For a `Screened` family `S`, a `Measure.LatticeYMFamily` `F` and a coupling `β`, the conjunction of
three statements:

* a physical gap `δ = S.κ / S.L > 0` cleared at every spacing (`uniform_physical_gap_pos`);
* at each spacing, `‖∑ k ∈ (S.gap i).s β, P β k * m β k ^ τ‖ ≤ (∑ k, ‖P β k‖) * exp (−(κ₀ − μ β)) ^ τ`
  (`Model.mass_gap_rate_of_model`, second component);
* a subsequential limit `q` of `F.Q` along a `StrictMono φ`, bounded by `⌈F.c⌉₊ * F.B`, nonnegative,
  and invariant under `F.actE` and `F.actP` (`Measure.continuum_of_family`).

`S` and `F` are independent arguments: the third conjunct is about `F` alone and mentions neither `S`
nor `β`, so the gap half and the measure half are statements about different objects, conjoined. The
open inputs are the fields of `Screened` and of `Measure.LatticeYMFamily`, listed in this file's
header.

DERIVED: `0` is the strict positivity of `δ` and the nonnegativity `0 ≤ q j`; every other quantity
in the statement is a field of `S` or of `F`. -/
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

/-- A measured tension at a fixed screen gives a spacing-independent gap bound.

The hypotheses: the read `R i` at aperture `2 * kk i + 1` is a single geometric mode,
`(R i).ρ d = lam i ^ (Moment.circLag d)` with `0 < lam i` and `lam i ≤ 1` (`hρ`, `hlam0`, `hlam1`);
its cosine average is positive (`hcos`); its tension clears the entropy floor,
`(R i).tension < (1 / 4) * Real.log 3` (`htens`); and the screen has a fixed physical extent,
`((2 * kk i + 1 : ℕ) + 1) * spacing i = L` (`hscreen`). The conclusion, at every `i`:

    (-2 * log (12 * ((1 - 3 ^ (-1/4)) / 8))) / L  ≤  (-log (lam i)) / spacing i

The left-hand side is one expression in `L` alone, the same at every spacing. Numerically its
numerator is about `2.0419`; the statement carries the symbolic form, not that decimal.

The route, by name:

  `Moment.Read.substrate_lt_of_tension_lt_floor`   the tension caps the circular second moment
  `ZeroMode.substrate_ge_of_slow_decay`            a slowly-decaying mode has a large one
  `ZeroMode.lam_pow_lt_of_tension`                 so `lam ^ (k + 1) < 12 * ((1 - 3 ^ (-1/4)) / 8)`
  `ZeroMode.rate_gt_of_tension`                    equivalently `(k + 1) * (-log lam)` exceeds
                                                   `-log (12 * ((1 - 3 ^ (-1/4)) / 8))`
  `ZeroMode.gap_phys_of_fixed_screen`              and at a fixed screen the spacing cancels

The doubling between `rate_gt_of_tension`'s constant and the one in this conclusion is the lag count
`2 * (kk i + 1)`, which is the aperture `2 * kk i + 1` plus one.

`hscreen` is a hypothesis: the aperture is a property of the extraction boundary rather than of the
lattice computed through. The correlation is a single transfer mode, `hρ` being an equation rather
than a bound; `ZeroMode.substrate_ge_of_subset_share` carries the multi-mode statement, where the
bound degrades by the weight share.

DERIVED: the conclusion's constant is `-2 * log (12 * ((1 - 3 ^ (-1/4)) / 8))`. The `12` is
`ZeroMode.six_mul_sum_sq`'s denominator and the `8` is `Moment.Read.cos_avg_le_circ`'s; `3 ^ (-1/4)`
is `e^{-κ₀}` for the entropy floor `κ₀ = (1 / 4) * Real.log 3`, whose positivity is `Floor.floor_pos`
and which is also the bound in `htens`; the `2` is the lag count `2 * (kk i + 1)` against
`rate_gt_of_tension`'s `kk i + 1`, and the `1` of `2 * kk i + 1` makes the aperture odd. `0 < L`,
`0 < spacing i` and `0 < lam i` are the positivity the divisions and the logarithm need. Nothing is
fitted and no constant is chosen. -/
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
  -- `c < 1` needs a genuine lower bound on `3^{-1/4}`: `1.5(1-T) < 1` iff `T > 1/3`. Positivity
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

The aperture and the box are different things, and elsewhere in this tree only the aperture appears.
A `Moment.Read N` carries `N+1` lags and says nothing about how large a system those lags were read
from. This section makes the box a parameter and states what follows.

The two are separate because a family of reads at different box sizes but the same aperture returns
the same bound, and that bound survives the box growing without limit:
`gap_bound_box_independent` carries `box` as an argument and never uses it.

The aperture is not treated the same way. The bound is `kappa / L`, with `L` the screen's extent, so
letting the aperture grow without limit while `hscreen` holds drives `L` up and the bound down.
Nothing in these statements forbids that; what fixes the aperture is the reading that its size is
the observer's capacity.

In the other direction the criterion refuses a window too small to resolve the decay: at aperture
`n` it passes only when `n * Delta > C`, so such a window returns no verdict rather than a
flattering one. The sharpest bound comes from the smallest window that still passes.
-/

/-- The gap bound does not depend on the box.

`box` is an argument of the theorem and appears nowhere in its conclusion: `κ / L ≤ Δlat i / spacing i`
holds at every `i`, with a right-hand side mentioning neither `box i` nor the box at any other index.
The hypotheses are the same as `uniform_physical_gap`'s, stated on bare functions rather than on a
`Screened`: a fixed screen `hscreen`, a positive spacing, and a lattice rate clearing
`κ / (N i + 1)`.

DERIVED: `0 < κ`, `0 < L` and `0 < spacing i` are the positivity `ZeroMode.gap_phys_of_fixed_screen`
needs for its divisions, and the `+ 1` of `N i + 1` is the lag count at aperture `N i`. `κ` and `L`
are the caller's, and no constant is introduced. -/
theorem gap_bound_box_independent
    (N : ℕ → ℕ) (spacing : ℕ → ℝ) (box : ℕ → ℝ) (Δlat : ℕ → ℝ) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L)
    (hspacing : ∀ i, 0 < spacing i)
    (hscreen : ∀ i, ((N i : ℝ) + 1) * spacing i = L)
    (hrate : ∀ i, κ / ((N i : ℝ) + 1) ≤ Δlat i) :
    ∀ i, κ / L ≤ Δlat i / spacing i :=
  ZeroMode.gap_phys_of_fixed_screen N spacing Δlat κ L hκ hL hspacing hscreen hrate

#print axioms gap_bound_box_independent

/-- The same bound, with the boxes growing without bound.

`hgrow : Tendsto box atTop atTop` is an argument and the conclusion does not mention `box`, so the
statement is `gap_bound_box_independent` packaged as `∃ δ > 0` with `hgrow` recording which limit is
being taken. No limit is computed; the witness is `κ / L`, the same number as without `hgrow`.

DERIVED: `0 < κ`, `0 < L`, `0 < spacing i` and `0 < δ` are the positivity conditions, and the `+ 1`
of `N i + 1` is the lag count at aperture `N i`. -/
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

/-! ## The noise edge taken on the residual rather than the raw spectrum

`ZeroMode.resolved_count_le_of_subset` bounds the number of resolved modes by the measured tension,
and that bound divides by `edge`, so the edge's value moves the bound. This section states where the
two candidate edges differ and which way the difference runs.

A transfer spectrum carries a near-unit component, `lam` close to `1`, holding most of the weight.
An edge set as a share `theta` of the total weight therefore includes a share of that component's
weight, while a gap argument concerns the modes left once it is removed. Three steps:

* the two edges differ by exactly the removed component's share (`edge_raw_sub_residual`);
* so the raw edge is the larger of the two (`edge_residual_le_raw`);
* and a larger edge resolves no more modes (`resolvedDim_antitone_edge`).

Composing them, the raw edge yields the smaller resolved count
(`resolved_count_under_reported_of_raw_edge`), so a count bound computed against it is smaller than
the modes present justify. `under_report_is_strict` gives the condition under which the inequality
is strict: a mode sitting between the two edges.

`entroptics-jlens` reports this from measurement, on reads where the near-unit component inflates
the floor. No constant is introduced here: `theta` is whatever share the caller's floor takes and
every other quantity is the read's own.
-/

/-- A lower edge resolves a superset of modes: `s.filter (e₂ < ev ·) ⊆ s.filter (e₁ < ev ·)` when
`e₁ ≤ e₂`. Stated as a set inclusion rather than a cardinality inequality, which is what
`under_report_is_strict` needs. `ev` and `s` are arbitrary; no order on `ι` is used. -/
theorem resolved_subset_of_edge_le {ι : Type*} (s : Finset ι) (ev : ι → ℝ) {e₁ e₂ : ℝ} (h : e₁ ≤ e₂) :
    s.filter (fun k => e₂ < ev k) ⊆ s.filter (fun k => e₁ < ev k) := by
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_le_of_lt h hk.2⟩

/-- `MassGap.Measure.resolvedDim s ev` is antitone in the edge: raising the noise floor cannot
reveal a mode. The cardinality form of `resolved_subset_of_edge_le`.

DERIVED: the statement carries no numeral. It is monotonicity of a filtered set's cardinality. -/
theorem resolvedDim_antitone_edge {ι : Type*} (s : Finset ι) (ev : ι → ℝ) {e₁ e₂ : ℝ} (h : e₁ ≤ e₂) :
    MassGap.Measure.resolvedDim s ev e₂ ≤ MassGap.Measure.resolvedDim s ev e₁ :=
  Finset.card_le_card (resolved_subset_of_edge_le s ev h)

#print axioms resolvedDim_antitone_edge

/-- The raw edge exceeds the residual edge by exactly the removed component's share:
`theta * ∑ i ∈ s, w i - theta * ∑ i ∈ s.erase v, w i = theta * w v`.

`theta` is whatever fraction of the aggregate weight the read takes as its floor and `v` is the
index removed. An identity, not an estimate: `w` is an arbitrary function and no sign condition on
it or on `theta` is required. -/
theorem edge_raw_sub_residual {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∈ s)
    (w : ι → ℝ) (theta : ℝ) :
    theta * (∑ i ∈ s, w i) - theta * (∑ i ∈ s.erase v, w i) = theta * w v := by
  rw [← Finset.sum_erase_add s w hv]
  ring

#print axioms edge_raw_sub_residual

/-- The residual edge is the smaller one:
`theta * ∑ i ∈ s.erase v, w i ≤ theta * ∑ i ∈ s, w i`. The only hypotheses beyond `v ∈ s` are that
the removed weight and `theta` are nonnegative.

DERIVED: `0 ≤ w v` and `0 ≤ theta` are those two sign conditions; the statement carries no other
numeral. -/
theorem edge_residual_le_raw {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∈ s)
    (w : ι → ℝ) (hwv : 0 ≤ w v) (theta : ℝ) (htheta : 0 ≤ theta) :
    theta * (∑ i ∈ s.erase v, w i) ≤ theta * ∑ i ∈ s, w i := by
  refine mul_le_mul_of_nonneg_left ?_ htheta
  rw [← Finset.sum_erase_add s w hv]
  linarith

#print axioms edge_residual_le_raw

/-- Reading the edge off the raw spectrum gives the smaller resolved count:
`resolvedDim s ev (theta * ∑ i ∈ s, w i) ≤ resolvedDim s ev (theta * ∑ i ∈ s.erase v, w i)`.

`edge_residual_le_raw` composed with `resolvedDim_antitone_edge`. The direction is the content: the
raw edge under-reports, so a count bound computed against it is smaller than the modes present
justify.

DERIVED: `0 ≤ w v` and `0 ≤ theta` are `edge_residual_le_raw`'s sign conditions, carried
unchanged. -/
theorem resolved_count_under_reported_of_raw_edge {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι) (hv : v ∈ s) (ev w : ι → ℝ) (hwv : 0 ≤ w v)
    (theta : ℝ) (htheta : 0 ≤ theta) :
    MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s, w i)
      ≤ MassGap.Measure.resolvedDim s ev (theta * ∑ i ∈ s.erase v, w i) :=
  resolvedDim_antitone_edge s ev (edge_residual_le_raw s v hv w hwv theta htheta)

#print axioms resolved_count_under_reported_of_raw_edge

/-- The under-report is strict when a mode sits between the two edges.

`hlo` and `hhi` place `ev m` above the residual edge and at or below the raw one, for some `m ∈ s`.
Then `resolvedDim s ev (theta * ∑ i ∈ s, w i) < resolvedDim s ev (theta * ∑ i ∈ s.erase v, w i)`.
Without this, `resolved_count_under_reported_of_raw_edge` would be compatible with the two counts
always agreeing.

DERIVED: `0 ≤ w v` and `0 ≤ theta` are the sign conditions `edge_residual_le_raw` needs inside the
proof; the two bracketing hypotheses carry no numeral of their own. -/
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

/-! ## The resolved count as an explicit ceiling

`ZeroMode.resolved_count_le_of_subset` is stated as a product inequality: the count appears
multiplied by everything it is bounded against. `Measure.familyOfSortedCount` asks instead for
`resolvedDim ... ≤ c`, a count on one side and a number on the other.

This section performs that rearrangement. The content is the same inequality divided through by a
quantity proved positive, and the added hypotheses are the ones that make the division legal: a
positive noise floor, a positive `lam0`, and a correlation with some weight in it.

Reading the right-hand side:

    12 * W * M / (edge * lam0^(k+1) * (2(k+1))^2 * S)

`W = ∑ w` is the read's total weight, `edge` its noise floor, `lam0` the lower edge of the band the
resolved modes occupy, and `M / S` is the weighted mean of `clag^2`, the substrate. Every factor is
the read's own, and `12` is `ZeroMode.six_mul_sum_sq`'s denominator carried through.

The substrate is what the tension bounds (`Moment.Read.substrate_lt_of_tension_lt_floor`), so a cap
on the count follows from `mu < kappa_0` through this ceiling — that is
`resolvedDim_le_of_tension` below. `edge` sits in the denominator, which is where the edge lemmas
above bear: a floor inflated by the near-unit component's share makes this ceiling smaller.
-/

/-- The resolved count, divided out into an explicit ceiling: `ZeroMode.resolved_count_le_of_subset`
with `(A.card : ℝ)` alone on the left.

`A ⊆ s` is the resolved set, supplied by the caller. Beyond that lemma's hypotheses this one adds
three strict positivities — the noise floor `edge`, the band edge `lam0`, and the aggregate
correlation `S` — which is what makes the division legal.

DERIVED: `12` is `ZeroMode.six_mul_sum_sq`'s denominator, carried through unchanged; `2 * (k + 1)`
is the even lag count the `ZeroMode.clag` sums run over and `^ 2` its square in the same lemma;
`lam0 ^ (k + 1)` is the antipodal power. `0 ≤ w i`, `lam i ≤ 1`, `0 < lam0`, `lam0 ≤ 1`, `0 < edge`
and `0 < S` are the range and positivity conditions. No new literal enters. -/
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

/-- The same ceiling on `MassGap.Measure.resolvedDim s w edge`, the quantity
`Measure.familyOfSortedCount` consumes, rather than on the cardinality of a set the caller produces.

`resolved_count_ceiling` with `A` instantiated at `s.filter (fun i => edge < w i)`: a mode is
resolved when its weight clears the noise floor. The only hypothesis left that is not a positivity
or range condition is `hband`, that every resolved mode sits at or above `lam0`. The theorem
therefore bounds the modes in that band, not all modes.

DERIVED: nothing new. `12`, `2 * (k + 1)`, `^ 2` and `lam0 ^ (k + 1)` are `resolved_count_ceiling`'s,
and `0 ≤ w i`, `lam i ≤ 1`, `0 < lam0`, `lam0 ≤ 1`, `0 < edge` and `0 < S` are its range and
positivity conditions. -/
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

/-! ## The count from the tension

`resolvedDim_ceiling` bounds the resolved count by an expression containing `M / S`, the weighted
mean of `clag^2` over the correlation. That is the substrate, and the substrate is what the tension
bounds: `Moment.Read.substrate_lt_of_tension_lt_floor` takes `mu < kappa_0` and forces it below
`(1 - 3^{-1/4})/8`. Composing the two:

    mu < kappa_0   =>   resolvedDim  <=  12 * (1 - 3^{-1/4})/8 * W / (edge * lam0^(k+1))

The right-hand side is about `0.360246 * W / (edge * lam0^(k+1))`, and every symbol in it is the
read's own: `W` its total weight, `edge` its noise floor, `lam0` the lower edge of the band the
resolved modes occupy. The `12` is `ZeroMode.six_mul_sum_sq`'s denominator and `(1 - 3^{-1/4})/8` is
the entropy floor composed with `Moment.Read.cos_avg_le_circ`. Nothing is chosen.

This is the shape of the count hypothesis `WilsonGauge.ym_continuum_gauge_counted` takes: that
family asks for a cap on the resolved count at every spacing, and this derives such a cap from the
measured tension at one. The per-spacing instantiation — a read at each spacing whose tension clears
the floor — is a hypothesis a caller supplies.

`edge` is in the denominator, which is where the edge lemmas above bear: a floor inflated by the
near-unit component's share makes this ceiling smaller.
-/

/-- The resolved count, bounded by the measured tension:
`resolvedDim s w edge ≤ 12 * ((1 - 3 ^ (-1/4)) / 8) * (∑ i ∈ s, w i) / (edge * lam0 ^ (k + 1))`.

`resolvedDim_ceiling` composed with `Moment.Read.substrate_lt_of_tension_lt_floor`. `hR` ties the
read `R : Moment.Read (2 * k + 1)` to the weights and rates — `R.ρ d = ∑ i ∈ s, w i * lam i ^ circLag d`
— so the substrate appearing in the ceiling is the one the tension bounds rather than a similar
quantity. The aperture is odd, `2 * k + 1`, so the lag count `2 * (k + 1)` is even.

DERIVED: `12` is `ZeroMode.six_mul_sum_sq`'s denominator and `8` is `Moment.Read.cos_avg_le_circ`'s;
`3 ^ (-1/4)` is `e^{-kappa_0}` for the entropy floor `(1 / 4) * Real.log 3`, whose positivity is
`Floor.floor_pos` and which is also the bound in `htens`. The `2` of `2 * k + 1` is the even lag
count the `ZeroMode.clag` sums run over, and `lam0 ^ (k + 1)` is the antipodal power. `0 ≤ w i`,
`lam i ≤ 1`, `0 < lam0`, `lam0 ≤ 1`, `0 < edge` and `0 < ∑ d, R.p d * cos (R.θ d)` are the range and
positivity conditions. No third constant enters. -/
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
