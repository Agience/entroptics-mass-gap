import Mathlib
import MassGap.WeakCouplingWindow
import MassGap.KnabeCriterion
import MassGap.BoxPatch
import MassGap.PeriodicStrongCoupling
import MassGap.ContinuumSep

noncomputable section

/-!
# MassGap.ConstantPhysics — the line of constant physics: the spacing read off the lattice mass

## The lattice mass

For transfer data `D`, `rateSet D = {m > 0 : GapAt D (e^{−m})}` is the set of gap rates per lattice
step, and `latMass D = sSup (rateSet D)`. `rateSet_eq_image`: `rateSet D` is the image of
`{r : 0 < r < 1, GapAt D r}` under `r ↦ −log r`, so `latMass D` is the supremum of `−log r` over the
rates at which `D` has a gap. `e^{−latMass D}` is always a gap rate: `gapAt_exp_neg_latMass` gives
`GapAt D (e^{−latMass D})` for every `D` (at `latMass D = 0`, the value of `sSup` on an empty or
unbounded set, that rate is `1`). `latMass_pos_iff`: `0 < latMass D` exactly when `rateSet D`
is non-empty and bounded above; `bddAbove_rateSet_iff`: bounded above exactly when `T` moves some
vector of the vacuum complement to a vector of positive form (`MovesComplement`). With both,
`gapAt_exp_neg_iff_le_latMass` makes `rateSet D = (0, latMass D]`.

## The constant-physics spacing

At the periodic state `latMassP τ p hN β = latMass (periodicGaugeInvData τ p hN β)`, and for a
chosen physical mass `mphys > 0`, `aPhys τ p hN mphys β = latMassP τ p hN β / mphys`: the spacing
at which the lattice mass is `mphys` in physical units. `constant_physics_gap`: at `2 ≤ N`, `β ≥ 0`
and `latMassP β > 0` the periodic Clay gap holds at the rate `e^{−mphys·aPhys β}`, its physical rate
`−log r / aPhys β` is exactly `mphys`, and no rate with a gap at `β` has a physical rate above
`mphys`. So along `aPhys` the physical gap is `mphys` at every coupling where the lattice mass is
positive, by construction; where `latMassP β = 0`, `aPhys β = 0` and the rate is `1`.
`latMassPositive_iff`: positivity of `latMassP` at every `β > 0` is `LatticeGapEvery` (a gap at each
coupling) together with `MovesComplementEvery`. `latticeGapEvery_of_boxes`: `LatticeGapEvery` follows
from the proved strong-coupling gap below some `β₀ > 0` and, from `β₀` on, the finite box check
`BoxPatch.BoxPatchGap` with `KnabeCriterion.HeatBathDecay`.

## The uniformity, and the bridge to `aRun`

`FixedWindowDecayAlong τ p hN a L` is `WeakCouplingWindow.FixedWindowDecay` with the spacing `aRun N`
replaced by a spacing function `a`; at `a = aRun N` it is `FixedWindowDecay` (`fixedWindowDecayAlong_aRun`).
`MassDominates τ p hN a`: some `M > 0` has `M · a β ≤ latMassP β` at every large `β`.

* `fixedWindowDecay_iff_massDominates`: at `2 ≤ N`, `L > 0` and `MovesComplement` at every large `β`,
  `FixedWindowDecay τ p hN L ↔ MassDominates τ p hN (aRun N)`; `fixedWindowDecay_iff_spacing_comparable`
  states it as `κ · aRun N β ≤ aPhys β` for some `κ > 0` at every large `β`. This is the uniformity
  `FixedWindowDecay` asks beyond a gap at each coupling: the lattice mass bounded below by a multiple
  of the two-loop spacing.
* `fixedWindowDecayAlong_aPhys`: along `aPhys` the same window statement holds from
  `latMassP > 0` eventually and `latMassP → 0` (`LatMassVanishes`); `massDominates_aPhys` holds at
  every `mphys > 0`.
* `asymptoticScaling_iff_aPhys_ratio`: `AsymptoticScalingAt N latMassP` holds exactly when
  `aPhys β / aRun N β → 1` for some `mphys > 0`. `fixedWindowDecay_of_asymptoticScaling`: it gives
  `FixedWindowDecay` at every window. `dominance_does_not_give_scaling`: the dominance that
  `FixedWindowDecay` is equivalent to is strictly weaker than asymptotic scaling, as constraints on a
  mass function `m : ℝ → ℝ`; the witness is a function built from `aRun N`, not `latMassP`.
* `clay_M_split`: `LatticeGapEvery` and `AsymptoticScalingAt N latMassP` give the periodic Clay gap at
  every `β > 0` and `FixedWindowDecay` at every window.

## Existence along the constant-physics spacing

`exists_physFamily`: continuity of `latMassP` on `[β₁, ∞)` (`LatMassContinuousFrom`), positivity
there, `LatMassVanishes`, and `aPhys β₁` at least the first dyadic spacing give couplings
`βs k → ∞` with `aPhys (βs k) = ContinuumSchwinger.dySpacing N k` (`PhysFamily`); along them the gap
is `e^{−mphys·dySpacing N k}` at every step (`physFamily_gapAt`). `latSkRAlong hN ρ βs s k F` is the
renormalised lattice Schwinger function at the coupling `βs k` and smearing spacing `s k`;
`ContinuumSchwinger.latSkR` is it at `(dyBeta, dySpacing)` (`latSkR_eq_along`).
`SignalConvergesSep hN ρ βs s`: every separated family converges along `atTop`. `ConstantPhysicsE`:
some `PhysFamily` along which `SignalConvergesSep` holds at the spacing `aPhys`.
`contS_of_constantPhysics`: for a `PhysFamily` `βs` with `SignalConvergesSep` at the spacing
`aPhys (βs k)` and `StateShiftInvisibleSep` between `βs` and `dyBeta` (the two smear at the same
spacing `dySpacing N k`), the separated lattice functions of
`ContinuumSchwinger` converge along `atTop` and `ContinuumSchwinger.contS` is that limit. The
comparison of the two coupling sequences is carried by `StateShiftInvisibleSep`, which asks that
their separated lattice functions at the same spacing differ by an amount tending to `0`.
`aRun_ratio_physFamily`: under `aPhys / aRun → 1` the two coupling sequences have two-loop spacings
with ratio tending to `1`. `physFamily_dyBeta_iff`: `dyBeta` is itself a constant-physics family
exactly when `latMassP (dyBeta k) = dySpacing N k · mphys` at every `k`.

## Open, as named propositions

`LatticeGapEvery`, `MovesComplementEvery`, `LatMassVanishes`, `LatMassContinuousFrom`,
`AsymptoticScaling.AsymptoticScalingAt N (latMassP τ p hN)`, `MassDominates`, `SignalConvergesSep`,
`StateShiftInvisibleSep`, `ConstantPhysicsE`, and `KnabeCriterion.HeatBathDecay` with
`BoxPatch.BoxPatchGap` from `β₀` on.

DERIVED (module-wide): `4` in `Fin 4` is the spacetime dimension; `0` in `hN : N ≠ 0` is the excluded
colour count; `2` in `2 ≤ N` is the least rank with a non-zero Haar variance of the real trace, the
hypothesis of `GapStep.periodic_clayGapAt_of_gapAt`; `1` in `1 ≤ N` is the least colour count, for
`AsymptoticScaling.aRun_pos`. CHOSEN: `mphys`, the physical unit in which the lattice mass is read,
is the caller's.
-/

namespace MassGap.ConstantPhysics

open MassGap MassGap.PeriodicState MassGap.AsymptoticScaling Filter
open scoped Topology

/-! ## 1. The lattice mass of transfer data -/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- `(e^{−m})² = e^{−2m}`.

DERIVED: `2` is the square, the degree of `GapAt`'s form. -/
theorem exp_neg_sq (m : ℝ) : Real.exp (-m) ^ 2 = Real.exp (-(2 * m)) := by
  rw [sq, ← Real.exp_add, show -m + -m = -(2 * m) by ring]

#print axioms exp_neg_sq

/-- At `0 < g` and `0 < f`, `g ≤ (e^{−m})² · f` gives `m ≤ (log f − log g)/2`.

DERIVED: `0` is the sign of `f` and `g`; `2` is the square of the rate. -/
theorem le_half_log_ratio {f g m : ℝ} (hg : 0 < g) (hf : 0 < f)
    (h : g ≤ Real.exp (-m) ^ 2 * f) : m ≤ (Real.log f - Real.log g) / 2 := by
  rw [exp_neg_sq] at h
  have hlog := Real.log_le_log hg h
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hlog
  linarith

#print axioms le_half_log_ratio

/-- At `0 < g` and `0 < f`, `m ≤ (log f − log g)/2` gives `g ≤ (e^{−m})² · f`.

DERIVED: `0` is the sign of `f` and `g`; `2` is the square of the rate. -/
theorem le_of_le_half_log_ratio {f g m : ℝ} (hg : 0 < g) (hf : 0 < f)
    (h : m ≤ (Real.log f - Real.log g) / 2) : g ≤ Real.exp (-m) ^ 2 * f := by
  rw [exp_neg_sq, ← Real.exp_log hg, ← Real.exp_log hf, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

#print axioms le_of_le_half_log_ratio

/-- **The gap rates per lattice step.** `{m : 0 < m ∧ GapAt D (e^{−m})}`.

DERIVED: `0` is the sign of the rate; `m` is the exponent of the contraction factor `e^{−m}`. -/
def rateSet (D : Transfer.TransferData A) : Set ℝ :=
  {m : ℝ | 0 < m ∧ TransferGap.GapAt D (Real.exp (-m))}

#print axioms rateSet

/-- Membership in `rateSet D`, unfolded.

DERIVED: `0` is the sign of the rate. -/
theorem mem_rateSet {D : Transfer.TransferData A} {m : ℝ} :
    m ∈ rateSet D ↔ 0 < m ∧ TransferGap.GapAt D (Real.exp (-m)) :=
  Iff.rfl

#print axioms mem_rateSet

/-- **The lattice mass**: `sSup (rateSet D)`. Where it is positive it is the largest gap rate per
lattice step (`latMass_pos_iff`, `gapAt_exp_neg_iff_le_latMass`); on an empty or unbounded
`rateSet D` it is `0`.

DERIVED: no numeral. -/
noncomputable def latMass (D : Transfer.TransferData A) : ℝ := sSup (rateSet D)

#print axioms latMass

/-- `T` moves some vector of the vacuum complement to a vector of positive form:
`∃ x, D.form x D.vac = 0 ∧ 0 < D.form (D.T x) (D.T x)`.

DERIVED: `0` is the vacuum pairing selecting the complement and the sign of the form. -/
def MovesComplement (D : Transfer.TransferData A) : Prop :=
  ∃ x : A, D.form x D.vac = 0 ∧ 0 < D.form (D.T x) (D.T x)

#print axioms MovesComplement

/-- At `0 < r < 1` with `GapAt D r`, `−log r ∈ rateSet D`.

DERIVED: `0` and `1` are the ends of the rate interval. -/
theorem neg_log_mem_rateSet (D : Transfer.TransferData A) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hg : TransferGap.GapAt D r) : -Real.log r ∈ rateSet D := by
  refine mem_rateSet.mpr ⟨neg_pos.mpr (Real.log_neg hr0 hr1), ?_⟩
  rw [neg_neg, Real.exp_log hr0]
  exact hg

#print axioms neg_log_mem_rateSet

/-- **The lattice mass is the supremum of `−log r` over the gapped rates.**
`rateSet D = (fun r => −log r) '' {r | 0 < r ∧ r < 1 ∧ GapAt D r}`.

DERIVED: `0` and `1` are the ends of the rate interval. -/
theorem rateSet_eq_image (D : Transfer.TransferData A) :
    rateSet D = (fun r => -Real.log r) '' {r : ℝ | 0 < r ∧ r < 1 ∧ TransferGap.GapAt D r} := by
  ext m
  constructor
  · intro hm
    obtain ⟨hm0, hg⟩ := mem_rateSet.mp hm
    refine ⟨Real.exp (-m), ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm0), hg⟩, ?_⟩
    show -Real.log (Real.exp (-m)) = m
    rw [Real.log_exp, neg_neg]
  · rintro ⟨r, ⟨hr0, hr1, hg⟩, rfl⟩
    exact neg_log_mem_rateSet D hr0 hr1 hg

#print axioms rateSet_eq_image

/-- `rateSet D` is non-empty exactly when `D` has a gap at some rate in `(0, 1)`.

DERIVED: `0` and `1` are the ends of the rate interval. -/
theorem rateSet_nonempty_iff (D : Transfer.TransferData A) :
    (rateSet D).Nonempty ↔ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ TransferGap.GapAt D r := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨hm0, hg⟩ := mem_rateSet.mp hm
    exact ⟨Real.exp (-m), Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hm0), hg⟩
  · rintro ⟨r, hr0, hr1, hg⟩
    exact ⟨_, neg_log_mem_rateSet D hr0 hr1 hg⟩

#print axioms rateSet_nonempty_iff

/-- **`e^{−latMass D}` is a gap rate.** `GapAt D (e^{−latMass D})` for every `D`. On an empty
`rateSet`, `latMass D = 0` and the rate `1` is automatic (`TransferGap.gapAt_of_one_le_sq`).
Otherwise, at `x` orthogonal to the vacuum: where `g = form (T x) (T x) = 0` the inequality is
`0 ≤ (e^{−latMass D})² · form x x`; where `g > 0`, every member of `rateSet D` is at most
`(log f − log g)/2`, `f = form x x ≥ g`, so the supremum is, and that bound is the gap inequality at
`x`. On an unbounded `rateSet` only the first case occurs.

DERIVED: `1` is the rate at which `GapAt` is automatic; `2` is `GapAt`'s square. -/
theorem gapAt_exp_neg_latMass (D : Transfer.TransferData A) :
    TransferGap.GapAt D (Real.exp (-latMass D)) := by
  by_cases hne : (rateSet D).Nonempty
  · intro x hx
    rcases (D.form_nonneg (D.T x)).lt_or_eq with hgpos | hgz
    · have hf : 0 < D.form x x := lt_of_lt_of_le hgpos (D.T_contract x)
      have hL : latMass D
          ≤ (Real.log (D.form x x) - Real.log (D.form (D.T x) (D.T x))) / 2 :=
        csSup_le hne (fun m hm => le_half_log_ratio hgpos hf ((mem_rateSet.mp hm).2 x hx))
      exact le_of_le_half_log_ratio hgpos hf hL
    · rw [← hgz]
      exact mul_nonneg (sq_nonneg _) (D.form_nonneg x)
  · have h0 : latMass D = 0 := by
      unfold latMass
      rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    rw [h0, neg_zero, Real.exp_zero]
    exact TransferGap.gapAt_of_one_le_sq D (by norm_num)

#print axioms gapAt_exp_neg_latMass

/-- **Every gapped rate is at most the lattice mass.** With `rateSet D` bounded above, `0 < r < 1`
and `GapAt D r`: `−log r ≤ latMass D`.

DERIVED: `0` and `1` are the ends of the rate interval. -/
theorem neg_log_le_latMass (D : Transfer.TransferData A) (hb : BddAbove (rateSet D)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hg : TransferGap.GapAt D r) : -Real.log r ≤ latMass D :=
  le_csSup hb (neg_log_mem_rateSet D hr0 hr1 hg)

#print axioms neg_log_le_latMass

/-- `0 < latMass D` when `rateSet D` is non-empty and bounded above.

DERIVED: `0` is the sign of the mass. -/
theorem latMass_pos (D : Transfer.TransferData A) (hne : (rateSet D).Nonempty)
    (hb : BddAbove (rateSet D)) : 0 < latMass D := by
  obtain ⟨m, hm⟩ := hne
  exact lt_of_lt_of_le (mem_rateSet.mp hm).1 (le_csSup hb hm)

#print axioms latMass_pos

/-- `MovesComplement D` bounds `rateSet D` above by `(log f − log g)/2` at the moved vector.

DERIVED: `2` is `GapAt`'s square. -/
theorem bddAbove_rateSet_of_moves (D : Transfer.TransferData A) (h : MovesComplement D) :
    BddAbove (rateSet D) := by
  obtain ⟨x, hx, hgpos⟩ := h
  have hf : 0 < D.form x x := lt_of_lt_of_le hgpos (D.T_contract x)
  exact bddAbove_def.mpr ⟨(Real.log (D.form x x) - Real.log (D.form (D.T x) (D.T x))) / 2,
    fun m hm => le_half_log_ratio hgpos hf ((mem_rateSet.mp hm).2 x hx)⟩

#print axioms bddAbove_rateSet_of_moves

/-- A bounded `rateSet D` gives `MovesComplement D`: were `form (T x) (T x) ≤ 0` on the whole
complement, every `m > 0` would lie in `rateSet D`.

DERIVED: `0` is the vacuum pairing and the sign of the form; `1` is added to a maximum to pass the
bound strictly. -/
theorem moves_of_bddAbove (D : Transfer.TransferData A) (hb : BddAbove (rateSet D)) :
    MovesComplement D := by
  by_contra hno
  obtain ⟨b, hb⟩ := bddAbove_def.mp hb
  have hall : ∀ x : A, D.form x D.vac = 0 → D.form (D.T x) (D.T x) ≤ 0 := by
    intro x hx
    by_contra hlt
    exact hno ⟨x, hx, not_le.mp hlt⟩
  have hb0 : (0 : ℝ) ≤ max b 0 := le_max_right b 0
  have hmem : max b 0 + 1 ∈ rateSet D := by
    refine mem_rateSet.mpr ⟨by linarith, ?_⟩
    intro x hx
    exact (hall x hx).trans (mul_nonneg (sq_nonneg _) (D.form_nonneg x))
  have h1 := hb _ hmem
  have h2 := le_max_left b 0
  linarith

#print axioms moves_of_bddAbove

/-- `BddAbove (rateSet D) ↔ MovesComplement D`.

DERIVED: no numeral. -/
theorem bddAbove_rateSet_iff (D : Transfer.TransferData A) :
    BddAbove (rateSet D) ↔ MovesComplement D :=
  ⟨moves_of_bddAbove D, bddAbove_rateSet_of_moves D⟩

#print axioms bddAbove_rateSet_iff

/-- **The lattice mass is positive exactly when it is a genuine finite gap rate.**
`0 < latMass D ↔ (rateSet D).Nonempty ∧ BddAbove (rateSet D)`: on an empty set and on an unbounded
set `sSup` is `0` (`Real.sSup_empty`, `Real.sSup_of_not_bddAbove`).

DERIVED: `0` is the sign of the mass and `sSup`'s value off its domain. -/
theorem latMass_pos_iff (D : Transfer.TransferData A) :
    0 < latMass D ↔ (rateSet D).Nonempty ∧ BddAbove (rateSet D) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hne
      have h0 : latMass D = 0 := by
        unfold latMass
        rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      linarith
    · by_contra hb
      have h0 : latMass D = 0 := Real.sSup_of_not_bddAbove hb
      linarith
  · rintro ⟨hne, hb⟩
    exact latMass_pos D hne hb

#print axioms latMass_pos_iff

/-- **The gapped rates are `(0, latMass D]`.** With `rateSet D` bounded above and `0 < m`:
`GapAt D (e^{−m}) ↔ m ≤ latMass D`. Forward `le_csSup`; back `gapAt_exp_neg_latMass` and
`GapStep.gapAt_mono`.

DERIVED: `0` is the sign of the rate. -/
theorem gapAt_exp_neg_iff_le_latMass (D : Transfer.TransferData A) (hb : BddAbove (rateSet D))
    {m : ℝ} (hm : 0 < m) : TransferGap.GapAt D (Real.exp (-m)) ↔ m ≤ latMass D := by
  constructor
  · intro hg
    exact le_csSup hb (mem_rateSet.mpr ⟨hm, hg⟩)
  · intro hle
    exact GapStep.gapAt_mono D (Real.exp_pos _).le (Real.exp_le_exp.mpr (neg_le_neg hle))
      (gapAt_exp_neg_latMass D)

#print axioms gapAt_exp_neg_iff_le_latMass

end Abstract

/-! ## 2. The lattice mass at the periodic state, and the constant-physics spacing -/

section Periodic

variable {N : ℕ}

/-- **The lattice mass at coupling `β`**: `latMass (periodicGaugeInvData τ p hN β)`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
noncomputable def latMassP (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) : ℝ :=
  latMass (periodicGaugeInvData τ p hN β)

#print axioms latMassP

/-- **The gap at each coupling (open).** At every `β > 0` some `0 < r < 1` has `GapAt` at the
periodic data. Weaker than a uniform physical gap: no relation between couplings.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count, the sign of `β` and the
lower end of `r`; `1` is the upper end of `r`. -/
def LatticeGapEvery (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  ∀ β : ℝ, 0 < β → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) r

#print axioms LatticeGapEvery

/-- **A finite correlation length at each coupling (open).** At every `β > 0` the transfer operator
moves some vector of the vacuum complement to a vector of positive form.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `β`. -/
def MovesComplementEvery (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  ∀ β : ℝ, 0 < β → MovesComplement (periodicGaugeInvData τ p hN β)

#print axioms MovesComplementEvery

/-- `0 < latMassP τ p hN β` at every `β > 0`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `β` and of
the mass. -/
def LatMassPositive (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  ∀ β : ℝ, 0 < β → 0 < latMassP τ p hN β

#print axioms LatMassPositive

/-- **The lattice mass vanishes at weak coupling (open)**: `latMassP τ p hN β → 0` as `β → ∞`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the limit. -/
def LatMassVanishes (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  Tendsto (latMassP τ p hN) atTop (𝓝 0)

#print axioms LatMassVanishes

/-- **The lattice mass is continuous in the coupling from `β₁` on (open).**

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
def LatMassContinuousFrom (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₁ : ℝ) : Prop :=
  ContinuousOn (latMassP τ p hN) (Set.Ici β₁)

#print axioms LatMassContinuousFrom

/-- **The constant-physics spacing**: `aPhys τ p hN mphys β = latMassP τ p hN β / mphys`, the
spacing at which the lattice mass at `β` is `mphys` in physical units.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
noncomputable def aPhys (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (mphys β : ℝ) : ℝ :=
  latMassP τ p hN β / mphys

#print axioms aPhys

/-- `aPhys τ p hN mphys β = latMassP τ p hN β / mphys`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
theorem aPhys_def (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (mphys β : ℝ) :
    aPhys τ p hN mphys β = latMassP τ p hN β / mphys :=
  rfl

#print axioms aPhys_def

/-- `GapAt` at `e^{−latMassP β}`, at every coupling.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
theorem gapAt_exp_neg_latMassP (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-latMassP τ p hN β)) :=
  gapAt_exp_neg_latMass _

#print axioms gapAt_exp_neg_latMassP

/-- **`LatticeGapEvery` is the periodic Clay gap at every coupling.** At `2 ≤ N`:
`LatticeGapEvery τ p hN ↔ ∀ β > 0, ∃ r, PeriodicClayGapAt τ p hN β r`
(`GapStep.periodic_clayGapAt_of_gapAt`, `WeakCouplingWindow.gapAt_of_periodicClayGapAt`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `β` and `r`; `1` is the upper end of `r`. -/
theorem latticeGapEvery_iff_clay (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) :
    LatticeGapEvery τ p hN ↔
      ∀ β : ℝ, 0 < β → ∃ r : ℝ, PeriodicContent.PeriodicClayGapAt τ p hN β r := by
  constructor
  · intro h β hβ
    obtain ⟨r, hr0, hr1, hg⟩ := h β hβ
    exact ⟨r, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ.le hr0 hr1 hg⟩
  · intro h β hβ
    obtain ⟨r, hc⟩ := h β hβ
    have hg := WeakCouplingWindow.gapAt_of_periodicClayGapAt τ p hN hc
    obtain ⟨hr0, hr1, -, -, -, -, -⟩ := hc
    exact ⟨r, hr0, hr1, hg⟩

#print axioms latticeGapEvery_iff_clay

/-- **Positivity of the lattice mass is the gap at each coupling with a finite correlation length.**
`LatMassPositive τ p hN ↔ LatticeGapEvery τ p hN ∧ MovesComplementEvery τ p hN`
(`latMass_pos_iff`, `rateSet_nonempty_iff`, `bddAbove_rateSet_iff`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
theorem latMassPositive_iff (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    LatMassPositive τ p hN ↔ LatticeGapEvery τ p hN ∧ MovesComplementEvery τ p hN := by
  constructor
  · intro h
    refine ⟨fun β hβ => ?_, fun β hβ => ?_⟩
    · exact (rateSet_nonempty_iff (periodicGaugeInvData τ p hN β)).mp
        ((latMass_pos_iff (periodicGaugeInvData τ p hN β)).mp (h β hβ)).1
    · exact moves_of_bddAbove (periodicGaugeInvData τ p hN β)
        ((latMass_pos_iff (periodicGaugeInvData τ p hN β)).mp (h β hβ)).2
  · rintro ⟨hg, hmv⟩ β hβ
    exact latMass_pos (periodicGaugeInvData τ p hN β)
      ((rateSet_nonempty_iff (periodicGaugeInvData τ p hN β)).mpr (hg β hβ))
      (bddAbove_rateSet_of_moves (periodicGaugeInvData τ p hN β) (hmv β hβ))

#print axioms latMassPositive_iff

/-- **The gap at each coupling from strong coupling and a finite box check.** There is `β₀ > 0`
such that, if at every `β ≥ β₀` `KnabeCriterion.HeatBathDecay τ p hN β` holds and some box size `n`
and patch gap `γ` satisfy `BoxPatch.BoxPatchGap hN β n γ`, then `LatticeGapEvery τ p hN`. Below `β₀`
the gap is `PeriodicStrongCoupling.periodic_gapAt_strong_coupling`; from `β₀` on it is
`KnabeCriterion.gapAt_of_patchGapCheck` through `BoxPatch.patchGapCheck_of_boxPatchGap`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `β₀`. -/
theorem latticeGapEvery_of_boxes (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₀ > 0, ((∀ β : ℝ, β₀ ≤ β → KnabeCriterion.HeatBathDecay τ p hN β ∧
      ∃ n : ℕ, ∃ γ : ℝ, BoxPatch.BoxPatchGap hN β n γ) → LatticeGapEvery τ p hN) := by
  obtain ⟨β₀, hβ₀, hsc⟩ := PeriodicStrongCoupling.periodic_gapAt_strong_coupling τ p hN
  refine ⟨β₀, hβ₀, fun hbox => ?_⟩
  intro β hβ
  by_cases hlt : β < β₀
  · obtain ⟨h0, h1, hg⟩ := hsc β hβ hlt
    exact ⟨_, h0, h1, hg⟩
  · obtain ⟨hdec, n, γ, hbp⟩ := hbox β (not_lt.mp hlt)
    exact KnabeCriterion.gapAt_of_patchGapCheck τ p hN hβ.le hdec
      (BoxPatch.patchGapCheck_of_boxPatchGap hN hbp)

#print axioms latticeGapEvery_of_boxes

/-- `0 < aPhys τ p hN mphys β` at `0 < mphys` and `0 < latMassP τ p hN β`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the signs. -/
theorem aPhys_pos (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys β : ℝ} (hm : 0 < mphys)
    (hL : 0 < latMassP τ p hN β) : 0 < aPhys τ p hN mphys β :=
  div_pos hL hm

#print axioms aPhys_pos

/-- **The gap along the constant-physics spacing, at every coupling.** At `mphys ≠ 0`:
`GapAt (periodicGaugeInvData τ p hN β) (e^{−mphys·aPhys β})`, since `mphys · aPhys β = latMassP β`.
It is a gap where `latMassP β > 0`; where `latMassP β = 0` the rate is `1`, at which `GapAt` holds for
every transfer data (`TransferGap.gapAt_of_one_le_sq`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the excluded unit. -/
theorem gapAt_aPhys (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} (hm : mphys ≠ 0) (β : ℝ) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β)
      (Real.exp (-(mphys * aPhys τ p hN mphys β))) := by
  have e : mphys * aPhys τ p hN mphys β = latMassP τ p hN β := mul_div_cancel₀ _ hm
  rw [e]
  exact gapAt_exp_neg_latMassP τ p hN β

#print axioms gapAt_aPhys

/-- **THE CONSTANT-PHYSICS GAP.** At `2 ≤ N`, `0 < mphys`, `0 ≤ β` and `0 < latMassP τ p hN β`:
the periodic Clay gap holds at `r = e^{−mphys·aPhys β}`; its physical rate `−log r / aPhys β` is
`mphys`; and every `0 < r' < 1` with `GapAt` at `β` has `−log r' / aPhys β ≤ mphys`. The physical gap
along `aPhys` is `mphys`, attained and best, at every coupling where the lattice mass is positive.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the signs; `1` is the upper end of the rate. -/
theorem constant_physics_gap (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {mphys : ℝ}
    (hm : 0 < mphys) {β : ℝ} (hβ : 0 ≤ β) (hL : 0 < latMassP τ p hN β) :
    PeriodicContent.PeriodicClayGapAt τ p hN β (Real.exp (-(mphys * aPhys τ p hN mphys β)))
      ∧ -Real.log (Real.exp (-(mphys * aPhys τ p hN mphys β))) / aPhys τ p hN mphys β = mphys
      ∧ ∀ r : ℝ, 0 < r → r < 1 → TransferGap.GapAt (periodicGaugeInvData τ p hN β) r →
          -Real.log r / aPhys τ p hN mphys β ≤ mphys := by
  have ha : 0 < aPhys τ p hN mphys β := aPhys_pos τ p hN hm hL
  have e : mphys * aPhys τ p hN mphys β = latMassP τ p hN β := mul_div_cancel₀ _ hm.ne'
  have hr0 : 0 < Real.exp (-(mphys * aPhys τ p hN mphys β)) := Real.exp_pos _
  have hr1 : Real.exp (-(mphys * aPhys τ p hN mphys β)) < 1 := by
    rw [e]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hL)
  refine ⟨GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ hr0 hr1
      (gapAt_aPhys τ p hN hm.ne' β), ?_, ?_⟩
  · rw [Real.log_exp, neg_neg, mul_div_cancel_right₀ _ ha.ne']
  · intro r hr0' hr1' hg
    have hb : BddAbove (rateSet (periodicGaugeInvData τ p hN β)) :=
      ((latMass_pos_iff (periodicGaugeInvData τ p hN β)).mp hL).2
    have h1 : -Real.log r ≤ latMassP τ p hN β :=
      neg_log_le_latMass (periodicGaugeInvData τ p hN β) hb hr0' hr1' hg
    rw [div_le_iff₀ ha]
    linarith

#print axioms constant_physics_gap

/-- `aPhys τ p hN mphys → 0` under `LatMassVanishes`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the limit. -/
theorem tendsto_aPhys_zero (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (hvan : LatMassVanishes τ p hN)
    (mphys : ℝ) : Tendsto (aPhys τ p hN mphys) atTop (𝓝 0) := by
  have hv : Tendsto (latMassP τ p hN) atTop (𝓝 0) := hvan
  have h := hv.div_const mphys
  rw [zero_div] at h
  exact h

#print axioms tendsto_aPhys_zero

end Periodic

/-! ## 3. The window statement along any spacing -/

section Along

variable {N : ℕ}

/-- **`FixedWindowDecay` along a spacing function `a`.** `WeakCouplingWindow.FixedWindowDecay` with
`aRun N` replaced by `a`: one factor `q ∈ (0, 1)` such that at every large `β` some lag `m ≠ 0` with
`m · a β ≤ L` has the connected reflected pairing of every gauge-invariant half-space observable on
the periodic lattices at most `q` times its lag-zero value, with every slack.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count, the lower end of `q`, the
excluded lag, the sign of the slack and the contact lag; `1` is the upper end of `q`. -/
def FixedWindowDecayAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (a : ℝ → ℝ) (L : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ β in Filter.atTop, ∃ m : ℕ, m ≠ 0 ∧
    (m : ℝ) * a β ≤ L ∧
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x m
            ≤ q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε

#print axioms FixedWindowDecayAlong

/-- At `a = aRun N` it is `WeakCouplingWindow.FixedWindowDecay`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
theorem fixedWindowDecayAlong_aRun (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) :
    FixedWindowDecayAlong τ p hN (aRun N) L ↔ WeakCouplingWindow.FixedWindowDecay τ p hN L :=
  Iff.rfl

#print axioms fixedWindowDecayAlong_aRun

/-- **The uniform physical gap along `a`**: some `M > 0` such that at every large `β` a rate `r` has
the periodic Clay gap and physical rate `−log r / a β ≥ M`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `M`. -/
def UniformPhysGapAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (a : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ᶠ β in atTop, ∃ r : ℝ,
    PeriodicContent.PeriodicClayGapAt τ p hN β r ∧ M ≤ -Real.log r / a β

#print axioms UniformPhysGapAlong

/-- **The lattice mass dominates the spacing (open at `a = aRun N`)**: some `M > 0` has
`M · a β ≤ latMassP τ p hN β` at every large `β`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `M`. -/
def MassDominates (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (a : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ᶠ β in atTop, M * a β ≤ latMassP τ p hN β

#print axioms MassDominates

/-- **The window gives the uniform physical gap along `a`.** At `2 ≤ N`, `0 < L`, `a` eventually
positive: `FixedWindowDecayAlong τ p hN a L → UniformPhysGapAlong τ p hN a`, with `M = −log q / L`.
The proof of `WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay` with `a` in place of `aRun N`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `L` and `a`. -/
theorem uniformPhysGapAlong_of_fixedWindowDecayAlong (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N)
    (hN : N ≠ 0) {a : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hapos : ∀ᶠ β in atTop, 0 < a β)
    (h : FixedWindowDecayAlong τ p hN a L) : UniformPhysGapAlong τ p hN a := by
  obtain ⟨q, hq0, hq1, hev⟩ := h
  refine ⟨-Real.log q / L, div_pos (neg_pos.mpr (Real.log_neg hq0 hq1)) hL, ?_⟩
  filter_upwards [hev, hapos, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ ha hβ0
  obtain ⟨m, hm, hwin, hlag⟩ := hβ
  have hr0 := WeakCouplingWindow.stepRate_pos hq0 m
  have hr1 := WeakCouplingWindow.stepRate_lt_one hq0.le hq1 hm
  have hg : TransferGap.GapAt (periodicGaugeInvData τ p hN β) (WeakCouplingWindow.stepRate q m) :=
    (WeakCouplingWindow.torusLagClear_iff_gapAt τ p hN hβ0.le hm hr0.le).mp
      (WeakCouplingWindow.torusLagClear_stepRate τ p hN β hq0.le hm hlag)
  exact ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0.le hr0 hr1 hg,
    WeakCouplingWindow.physical_rate_ge hq0 hq1 hm ha hL hwin⟩

#print axioms uniformPhysGapAlong_of_fixedWindowDecayAlong

/-- **The uniform physical gap along `a` gives the window.** At `0 < L`, `a` eventually positive
and eventually below every positive bound: `UniformPhysGapAlong τ p hN a → FixedWindowDecayAlong
τ p hN a L`, with the factor `e^{−M·L/2}` at the lag `⌊L / a β⌋₊`
(`WeakCouplingWindow.window_lag_exists`, `WeakCouplingWindow.torusLag_le_of_gapAt`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the signs. The `2` of
`L/2` is `WeakCouplingWindow.window_lag_exists`'s CHOSEN half-window. -/
theorem fixedWindowDecayAlong_of_uniformPhysGapAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {a : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hapos : ∀ᶠ β in atTop, 0 < a β)
    (hsmall : ∀ b : ℝ, 0 < b → ∀ᶠ β in atTop, a β ≤ b) (h : UniformPhysGapAlong τ p hN a) :
    FixedWindowDecayAlong τ p hN a L := by
  obtain ⟨M, hM, hev⟩ := h
  have hML : 0 < M * L / 2 := by positivity
  refine ⟨Real.exp (-(M * L / 2)), Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  filter_upwards [hev, hsmall (L / 2) (half_pos hL), hapos] with β hβ ha2 ha
  obtain ⟨r, hgap, hrate⟩ := hβ
  obtain ⟨m, hm, hwin, hhalf⟩ := WeakCouplingWindow.window_lag_exists ha ha2
  have hg := WeakCouplingWindow.gapAt_of_periodicClayGapAt τ p hN hgap
  obtain ⟨hr0, -, -, -, -, -, -⟩ := hgap
  have hA : M * a β ≤ -Real.log r := (le_div_iff₀ ha).mp hrate
  have h1 : M * (L / 2) ≤ M * ((m : ℝ) * a β) := mul_le_mul_of_nonneg_left hhalf hM.le
  have h2 : (m : ℝ) * (M * a β) ≤ (m : ℝ) * (-Real.log r) :=
    mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg m)
  have h4 : M * L / 2 ≤ (m : ℝ) * -Real.log r := by linarith
  have hq : r ^ m ≤ Real.exp (-(M * L / 2)) := by
    rw [← Real.exp_log hr0, ← Real.exp_nat_mul, Real.exp_le_exp]
    linarith
  exact ⟨m, hm, hwin, WeakCouplingWindow.torusLag_le_of_gapAt τ p hN β hr0.le hg m hq⟩

#print axioms fixedWindowDecayAlong_of_uniformPhysGapAlong

/-- **Dominance gives the uniform physical gap along `a`.** At `2 ≤ N` and `a` eventually positive:
`MassDominates τ p hN a → UniformPhysGapAlong τ p hN a`, at the rate `e^{−M·a β}`, which the attained
rate `e^{−latMassP β}` beats (`gapAt_exp_neg_latMassP`, `GapStep.gapAt_mono`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the signs. -/
theorem uniformPhysGapAlong_of_massDominates (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {a : ℝ → ℝ} (hapos : ∀ᶠ β in atTop, 0 < a β) (h : MassDominates τ p hN a) :
    UniformPhysGapAlong τ p hN a := by
  obtain ⟨M, hM, hev⟩ := h
  refine ⟨M, hM, ?_⟩
  filter_upwards [hev, hapos, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ ha hβ0
  have hMa : 0 < M * a β := mul_pos hM ha
  have hr0 : 0 < Real.exp (-(M * a β)) := Real.exp_pos _
  have hr1 : Real.exp (-(M * a β)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hMa)
  have hg : TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * a β))) :=
    GapStep.gapAt_mono _ (Real.exp_pos _).le (Real.exp_le_exp.mpr (neg_le_neg hβ))
      (gapAt_exp_neg_latMassP τ p hN β)
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0.le hr0 hr1 hg, ?_⟩
  have e : -Real.log (Real.exp (-(M * a β))) / a β = M := by
    rw [Real.log_exp, neg_neg, mul_div_cancel_right₀ _ ha.ne']
  exact e.ge

#print axioms uniformPhysGapAlong_of_massDominates

/-- **The uniform physical gap along `a` gives dominance**, where the correlation length is finite:
at `a` eventually positive and `MovesComplement` at every large `β`,
`UniformPhysGapAlong τ p hN a → MassDominates τ p hN a` (`neg_log_le_latMass`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `a`. -/
theorem massDominates_of_uniformPhysGapAlong (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {a : ℝ → ℝ}
    (hapos : ∀ᶠ β in atTop, 0 < a β)
    (hmov : ∀ᶠ β in atTop, MovesComplement (periodicGaugeInvData τ p hN β))
    (h : UniformPhysGapAlong τ p hN a) : MassDominates τ p hN a := by
  obtain ⟨M, hM, hev⟩ := h
  refine ⟨M, hM, ?_⟩
  filter_upwards [hev, hapos, hmov] with β hβ ha hmv
  obtain ⟨r, hgap, hrate⟩ := hβ
  have hg := WeakCouplingWindow.gapAt_of_periodicClayGapAt τ p hN hgap
  obtain ⟨hr0, hr1, -, -, -, -, -⟩ := hgap
  have h1 : M * a β ≤ -Real.log r := (le_div_iff₀ ha).mp hrate
  exact h1.trans (neg_log_le_latMass (periodicGaugeInvData τ p hN β)
    (bddAbove_rateSet_of_moves (periodicGaugeInvData τ p hN β) hmv) hr0 hr1 hg)

#print axioms massDominates_of_uniformPhysGapAlong

/-- `UniformPhysGapAlong τ p hN a ↔ MassDominates τ p hN a` at `2 ≤ N`, `a` eventually positive and
`MovesComplement` at every large `β`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `a`. -/
theorem uniformPhysGapAlong_iff_massDominates (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {a : ℝ → ℝ} (hapos : ∀ᶠ β in atTop, 0 < a β)
    (hmov : ∀ᶠ β in atTop, MovesComplement (periodicGaugeInvData τ p hN β)) :
    UniformPhysGapAlong τ p hN a ↔ MassDominates τ p hN a :=
  ⟨massDominates_of_uniformPhysGapAlong τ p hN hapos hmov,
    uniformPhysGapAlong_of_massDominates τ p hN2 hN hapos⟩

#print axioms uniformPhysGapAlong_iff_massDominates

/-- **Along `aPhys` dominance holds by construction**: `MassDominates τ p hN (aPhys τ p hN mphys)`
at `0 < mphys`, with `M = mphys` and equality at every coupling. It asks nothing of the lattice mass:
where `latMassP β = 0`, `aPhys β = 0` and the inequality is `0 ≤ 0`. The content along `aPhys` is
`aPhys` eventually positive, which `fixedWindowDecayAlong_aPhys` takes as a hypothesis.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `mphys`. -/
theorem massDominates_aPhys (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} (hm : 0 < mphys) :
    MassDominates τ p hN (aPhys τ p hN mphys) :=
  ⟨mphys, hm, Filter.Eventually.of_forall (fun β =>
    (mul_div_cancel₀ (latMassP τ p hN β) hm.ne').le)⟩

#print axioms massDominates_aPhys

/-- **Dominance of `a` is comparability of `a` with `aPhys`.** At `0 < mphys`:
`MassDominates τ p hN a ↔ ∃ κ > 0, ∀ᶠ β, κ · a β ≤ aPhys τ p hN mphys β` (`κ = M / mphys`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the signs. -/
theorem massDominates_iff_spacing (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} (hm : 0 < mphys)
    (a : ℝ → ℝ) :
    MassDominates τ p hN a ↔
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ β in atTop, κ * a β ≤ aPhys τ p hN mphys β := by
  constructor
  · rintro ⟨M, hM, hev⟩
    refine ⟨M / mphys, div_pos hM hm, hev.mono (fun β hβ => ?_)⟩
    rw [aPhys_def, le_div_iff₀ hm]
    have e : M / mphys * a β * mphys = M * a β := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hm.ne']
    rw [e]
    exact hβ
  · rintro ⟨κ, hκ, hev⟩
    refine ⟨κ * mphys, mul_pos hκ hm, hev.mono (fun β hβ => ?_)⟩
    rw [aPhys_def, le_div_iff₀ hm] at hβ
    have e : κ * mphys * a β = κ * a β * mphys := by ring
    rw [e]
    exact hβ

#print axioms massDominates_iff_spacing

/-- **Along `aPhys` the window statement holds from positivity and vanishing.** At `2 ≤ N`,
`0 < mphys`, `0 < L`, `latMassP` eventually positive, and `LatMassVanishes`:
`FixedWindowDecayAlong τ p hN (aPhys τ p hN mphys) L`. The physical gap along `aPhys` is `mphys`
(`constant_physics_gap`), and `aPhys → 0` fits a lag in the window.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the signs. -/
theorem fixedWindowDecayAlong_aPhys (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {mphys L : ℝ}
    (hm : 0 < mphys) (hL : 0 < L) (hpos : ∀ᶠ β in atTop, 0 < latMassP τ p hN β)
    (hvan : LatMassVanishes τ p hN) :
    FixedWindowDecayAlong τ p hN (aPhys τ p hN mphys) L := by
  have hapos : ∀ᶠ β in atTop, 0 < aPhys τ p hN mphys β :=
    hpos.mono (fun β h => aPhys_pos τ p hN hm h)
  refine fixedWindowDecayAlong_of_uniformPhysGapAlong τ p hN hL hapos (fun b hb => ?_) ?_
  · exact (tendsto_aPhys_zero τ p hN hvan mphys).eventually (ge_mem_nhds hb)
  · refine ⟨mphys, hm, ?_⟩
    filter_upwards [hpos, Filter.eventually_gt_atTop (0 : ℝ)] with β hL' hβ
    obtain ⟨hc, he, -⟩ := constant_physics_gap τ p hN2 hN hm hβ.le hL'
    exact ⟨_, hc, he.ge⟩

#print axioms fixedWindowDecayAlong_aPhys

end Along

/-! ## 4. The bridge to the two-loop spacing -/

section Bridge

variable {N : ℕ}

/-- `aRun N → 0` at `1 ≤ N`.

DERIVED: `1` is the least colour count; `0` is the limit; `2` in the proof's `b / 2` is a halving
that makes the bound strict. -/
theorem tendsto_aRun_zero (hN1 : 1 ≤ N) : Tendsto (aRun N) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun b hb => ?_⟩
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
    exact lt_trans ha' (aRun_pos hN1 hβ)
  · filter_upwards [WeakCouplingWindow.eventually_aRun_le hN1 (half_pos hb)] with β hβ
    exact lt_of_le_of_lt hβ (half_lt_self hb)

#print axioms tendsto_aRun_zero

/-- **`FixedWindowDecay` is dominance of the two-loop spacing by the lattice mass.** At `2 ≤ N`,
`0 < L` and `MovesComplement` at every large `β`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L ↔ MassDominates τ p hN (aRun N)`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `L`. -/
theorem fixedWindowDecay_iff_massDominates (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L)
    (hmov : ∀ᶠ β in atTop, MovesComplement (periodicGaugeInvData τ p hN β)) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L ↔ MassDominates τ p hN (aRun N) := by
  have hN1 : 1 ≤ N := by omega
  have hapos : ∀ᶠ β in atTop, 0 < aRun N β :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (fun β hβ => aRun_pos hN1 hβ)
  constructor
  · intro h
    exact massDominates_of_uniformPhysGapAlong τ p hN hapos hmov
      (uniformPhysGapAlong_of_fixedWindowDecayAlong τ p hN2 hN (a := aRun N) hL hapos h)
  · intro h
    exact fixedWindowDecayAlong_of_uniformPhysGapAlong τ p hN (a := aRun N) hL hapos
      (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb)
      (uniformPhysGapAlong_of_massDominates τ p hN2 hN hapos h)

#print axioms fixedWindowDecay_iff_massDominates

/-- **`FixedWindowDecay` is comparability of the two spacings.** At `2 ≤ N`, `0 < L`, `0 < mphys`
and `MovesComplement` at every large `β`: `FixedWindowDecay τ p hN L` holds exactly when some
`κ > 0` has `κ · aRun N β ≤ aPhys τ p hN mphys β` at every large `β`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the signs. -/
theorem fixedWindowDecay_iff_spacing_comparable (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L mphys : ℝ} (hL : 0 < L) (hm : 0 < mphys)
    (hmov : ∀ᶠ β in atTop, MovesComplement (periodicGaugeInvData τ p hN β)) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ β in atTop, κ * aRun N β ≤ aPhys τ p hN mphys β :=
  (fixedWindowDecay_iff_massDominates τ p hN2 hN hL hmov).trans
    (massDominates_iff_spacing τ p hN hm (aRun N))

#print axioms fixedWindowDecay_iff_spacing_comparable

/-- **Asymptotic scaling gives dominance.** At `1 ≤ N`, `AsymptoticScalingAt N m` gives
`M = mphys / 2 > 0` with `M · aRun N β ≤ m β` at every large `β`.

DERIVED: `1` is the least colour count; `0` is the sign of `M`; `2` in `mphys / 2` is a CHOSEN
fraction of the limit, any fraction in `(0, 1)` serves. -/
theorem dominates_of_asymptoticScaling (hN1 : 1 ≤ N) {m : ℝ → ℝ}
    (h : AsymptoticScalingAt N m) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ β in atTop, M * aRun N β ≤ m β := by
  obtain ⟨mphys, hpos, hlim⟩ := h
  refine ⟨mphys / 2, half_pos hpos, ?_⟩
  filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hpos)),
    Filter.eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
  exact ((lt_div_iff₀ (aRun_pos hN1 hβ0)).mp hβ).le

#print axioms dominates_of_asymptoticScaling

/-- **Dominance is strictly weaker than asymptotic scaling.** At `1 ≤ N`, `m β = aRun N β · β` has
`1 · aRun N β ≤ m β` for `β ≥ 1` and `m / aRun N = β → ∞`, so no finite limit. The comparison is of
the two properties on an arbitrary function `m : ℝ → ℝ`; the statement says nothing about
`latMassP`.

DERIVED: `1` is the least colour count, the witness `M` and the coupling from which `β ≥ 1`; `0` is
the sign. CHOSEN: the factor `β`, any factor bounded below and unbounded serves. -/
theorem dominance_does_not_give_scaling (hN1 : 1 ≤ N) :
    ∃ m : ℝ → ℝ, (∃ M : ℝ, 0 < M ∧ ∀ᶠ β in atTop, M * aRun N β ≤ m β)
      ∧ ¬ AsymptoticScalingAt N m := by
  refine ⟨fun β => aRun N β * β, ⟨1, one_pos, ?_⟩, ?_⟩
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with β hβ
    have ha := aRun_pos hN1 (lt_of_lt_of_le one_pos hβ)
    show 1 * aRun N β ≤ aRun N β * β
    rw [one_mul]
    exact le_mul_of_one_le_right ha.le hβ
  · rintro ⟨mphys, -, hlim⟩
    have hub : ∀ᶠ β in atTop, aRun N β * β / aRun N β < mphys + 1 :=
      hlim.eventually (gt_mem_nhds (by linarith))
    obtain ⟨β, hβ1, hβ2, hβ0⟩ := (hub.and ((Filter.eventually_ge_atTop (mphys + 1)).and
      (Filter.eventually_gt_atTop (0 : ℝ)))).exists
    rw [mul_div_cancel_left₀ β (aRun_pos hN1 hβ0).ne'] at hβ1
    linarith

#print axioms dominance_does_not_give_scaling

/-- **Asymptotic scaling of the lattice mass is `aPhys / aRun → 1`.**
`AsymptoticScalingAt N (latMassP τ p hN) ↔ ∃ mphys > 0, aPhys τ p hN mphys β / aRun N β → 1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `mphys`;
`1` is the limit ratio. -/
theorem asymptoticScaling_iff_aPhys_ratio (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    AsymptoticScalingAt N (latMassP τ p hN) ↔
      ∃ mphys : ℝ, 0 < mphys ∧
        Tendsto (fun β => aPhys τ p hN mphys β / aRun N β) atTop (𝓝 1) := by
  constructor
  · rintro ⟨mphys, hm, hlim⟩
    refine ⟨mphys, hm, ?_⟩
    have h := hlim.div_const mphys
    rw [div_self hm.ne'] at h
    refine Filter.Tendsto.congr (fun β => ?_) h
    show latMassP τ p hN β / aRun N β / mphys = latMassP τ p hN β / mphys / aRun N β
    exact div_right_comm _ _ _
  · rintro ⟨mphys, hm, hlim⟩
    refine ⟨mphys, hm, ?_⟩
    have h := hlim.mul_const mphys
    rw [one_mul] at h
    refine Filter.Tendsto.congr (fun β => ?_) h
    show latMassP τ p hN β / mphys / aRun N β * mphys = latMassP τ p hN β / aRun N β
    rw [div_right_comm, div_mul_cancel₀ _ hm.ne']

#print axioms asymptoticScaling_iff_aPhys_ratio

/-- **Asymptotic scaling gives `FixedWindowDecay` at every window.** At `2 ≤ N`, `0 < L` and
`AsymptoticScalingAt N (latMassP τ p hN)`: `WeakCouplingWindow.FixedWindowDecay τ p hN L`
(`dominates_of_asymptoticScaling`, `uniformPhysGapAlong_of_massDominates`,
`fixedWindowDecayAlong_of_uniformPhysGapAlong`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `L`. -/
theorem fixedWindowDecay_of_asymptoticScaling (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) (h : AsymptoticScalingAt N (latMassP τ p hN)) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  have hN1 : 1 ≤ N := by omega
  have hapos : ∀ᶠ β in atTop, 0 < aRun N β :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (fun β hβ => aRun_pos hN1 hβ)
  have hdom : MassDominates τ p hN (aRun N) := dominates_of_asymptoticScaling hN1 h
  exact fixedWindowDecayAlong_of_uniformPhysGapAlong τ p hN (a := aRun N) hL hapos
    (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb)
    (uniformPhysGapAlong_of_massDominates τ p hN2 hN hapos hdom)

#print axioms fixedWindowDecay_of_asymptoticScaling

/-- **Asymptotic scaling makes the lattice mass vanish.** At `N ≠ 0`,
`AsymptoticScalingAt N (latMassP τ p hN) → LatMassVanishes τ p hN`: `latMassP = (latMassP / aRun) ·
aRun → mphys · 0`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the limit. -/
theorem latMassVanishes_of_asymptoticScaling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    (h : AsymptoticScalingAt N (latMassP τ p hN)) : LatMassVanishes τ p hN := by
  have hN1 : 1 ≤ N := ContinuumSchwinger.one_le_of_ne_zero hN
  obtain ⟨mphys, -, hlim⟩ := h
  have h1 := hlim.mul (tendsto_aRun_zero hN1)
  rw [mul_zero] at h1
  show Tendsto (latMassP τ p hN) atTop (𝓝 0)
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
  exact div_mul_cancel₀ _ (aRun_pos hN1 hβ).ne'

#print axioms latMassVanishes_of_asymptoticScaling

/-- **THE SPLIT OF THE M INPUT.** At `2 ≤ N`, `LatticeGapEvery τ p hN` and
`AsymptoticScalingAt N (latMassP τ p hN)` give the periodic Clay gap at every `β > 0` and
`WeakCouplingWindow.FixedWindowDecay τ p hN L` at every `L > 0`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded colour count and the sign of `β` and `L`. -/
theorem clay_M_split (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (hgap : LatticeGapEvery τ p hN) (hAS : AsymptoticScalingAt N (latMassP τ p hN)) :
    (∀ β : ℝ, 0 < β → ∃ r : ℝ, PeriodicContent.PeriodicClayGapAt τ p hN β r)
      ∧ ∀ L : ℝ, 0 < L → WeakCouplingWindow.FixedWindowDecay τ p hN L :=
  ⟨(latticeGapEvery_iff_clay τ p hN2 hN).mp hgap,
    fun _ hL => fixedWindowDecay_of_asymptoticScaling τ p hN2 hN hL hAS⟩

#print axioms clay_M_split

end Bridge

/-! ## 5. Couplings at dyadic constant-physics spacings -/

section Family

variable {N : ℕ}

/-- **A level is reached.** For `f` continuous on `[β₁, ∞)` with `f → 0` and `0 < a ≤ f β₁`, some
`β ≥ β₁` has `f β = a` (`intermediate_value_Icc'`).

DERIVED: `0` is the limit and the sign of `a`. -/
theorem exists_level {f : ℝ → ℝ} {β₁ a : ℝ} (hcont : ContinuousOn f (Set.Ici β₁))
    (hvan : Tendsto f atTop (𝓝 0)) (ha : 0 < a) (hle : a ≤ f β₁) :
    ∃ β : ℝ, β₁ ≤ β ∧ f β = a := by
  obtain ⟨β₂, hβ₂a, hβ₂⟩ :=
    ((hvan.eventually (gt_mem_nhds ha)).and (Filter.eventually_ge_atTop β₁)).exists
  have hmem : a ∈ Set.Icc (f β₂) (f β₁) := ⟨hβ₂a.le, hle⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hβ₂ (hcont.mono Set.Icc_subset_Ici_self) hmem
  exact ⟨x, hx.1, hfx⟩

#print axioms exists_level

/-- **Couplings realising vanishing levels tend to infinity.** For `f` continuous and positive on
`[β₁, ∞)`, couplings `βs k ≥ β₁` with `f (βs k) = t k` and `t → 0` have `βs → ∞`: on `[β₁, B]` the
positive minimum of `f` is eventually undercut. The argument of `ContinuumSchwinger.tendsto_dyBeta`.

DERIVED: `0` is the sign of `f` and the limit of `t`. -/
theorem tendsto_atTop_of_level {f : ℝ → ℝ} {β₁ : ℝ} (hcont : ContinuousOn f (Set.Ici β₁))
    (hpos : ∀ β : ℝ, β₁ ≤ β → 0 < f β) {βs t : ℕ → ℝ} (hβs : ∀ k, β₁ ≤ βs k)
    (hf : ∀ k, f (βs k) = t k) (ht : Tendsto t atTop (𝓝 0)) : Tendsto βs atTop atTop := by
  refine Filter.tendsto_atTop.mpr (fun B => ?_)
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := β₁) (b := max B β₁)).exists_isMinOn
    ⟨β₁, le_refl β₁, le_max_right B β₁⟩ (hcont.mono Set.Icc_subset_Ici_self)
  have hm : 0 < f x := hpos x hx.1
  have hev : ∀ᶠ k in atTop, t k < f x := ht.eventually (gt_mem_nhds hm)
  filter_upwards [hev] with k hk
  by_contra hlt
  push_neg at hlt
  have hmem : βs k ∈ Set.Icc β₁ (max B β₁) := ⟨hβs k, hlt.le.trans (le_max_left B β₁)⟩
  have h1 := isMinOn_iff.mp hmin _ hmem
  rw [hf k] at h1
  linarith

#print axioms tendsto_atTop_of_level

/-- `dySpacing N k ≤ dySpacing N 0` at `1 ≤ N`.

DERIVED: `1` is the least colour count and the lower bound of `2 ^ k`; `0` is the first step; `2` is
the halving. -/
theorem dySpacing_le_dySpacing_zero (hN1 : 1 ≤ N) (k : ℕ) :
    ContinuumSchwinger.dySpacing N k ≤ ContinuumSchwinger.dySpacing N 0 := by
  have h := ContinuumSchwinger.dySpacing_mul_pow N (Nat.zero_le k)
  have hpos := ContinuumSchwinger.dySpacing_pos hN1 k
  calc ContinuumSchwinger.dySpacing N k
      ≤ ContinuumSchwinger.dySpacing N k * 2 ^ (k - 0) :=
        le_mul_of_one_le_right hpos.le (one_le_pow₀ (by norm_num))
    _ = ContinuumSchwinger.dySpacing N 0 := h

#print axioms dySpacing_le_dySpacing_zero

/-- **A constant-physics family (open to construct).** Couplings `βs k → ∞` at which the
constant-physics spacing is the dyadic spacing of `ContinuumSchwinger`:
`aPhys τ p hN mphys (βs k) = dySpacing N k`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
def PhysFamily (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (mphys : ℝ) (βs : ℕ → ℝ) : Prop :=
  Tendsto βs atTop atTop ∧ ∀ k : ℕ, aPhys τ p hN mphys (βs k) = ContinuumSchwinger.dySpacing N k

#print axioms PhysFamily

/-- **A constant-physics family exists from continuity, positivity and vanishing.** At `0 < mphys`,
`LatMassContinuousFrom τ p hN β₁`, `0 < latMassP β` on `[β₁, ∞)`, `LatMassVanishes τ p hN` and
`dySpacing N 0 ≤ aPhys β₁`: some `βs` has `PhysFamily τ p hN mphys βs` (`exists_level`,
`tendsto_atTop_of_level`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count, the first dyadic step and
the signs. -/
theorem exists_physFamily (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys β₁ : ℝ} (hm : 0 < mphys)
    (hcont : LatMassContinuousFrom τ p hN β₁)
    (hpos : ∀ β : ℝ, β₁ ≤ β → 0 < latMassP τ p hN β) (hvan : LatMassVanishes τ p hN)
    (hstart : ContinuumSchwinger.dySpacing N 0 ≤ aPhys τ p hN mphys β₁) :
    ∃ βs : ℕ → ℝ, PhysFamily τ p hN mphys βs := by
  have hN1 : 1 ≤ N := ContinuumSchwinger.one_le_of_ne_zero hN
  have hc : ContinuousOn (latMassP τ p hN) (Set.Ici β₁) := hcont
  have hcA : ContinuousOn (aPhys τ p hN mphys) (Set.Ici β₁) := hc.div_const mphys
  have hvA := tendsto_aPhys_zero τ p hN hvan mphys
  have hex : ∀ k : ℕ, ∃ β : ℝ, β₁ ≤ β ∧
      aPhys τ p hN mphys β = ContinuumSchwinger.dySpacing N k :=
    fun k => exists_level hcA hvA (ContinuumSchwinger.dySpacing_pos hN1 k)
      ((dySpacing_le_dySpacing_zero hN1 k).trans hstart)
  choose βs hβ₁ hβs using hex
  exact ⟨βs, tendsto_atTop_of_level hcA (fun β hβ => aPhys_pos τ p hN hm (hpos β hβ)) hβ₁ hβs
    (ContinuumSchwinger.tendsto_dySpacing N), hβs⟩

#print axioms exists_physFamily

/-- **Along a constant-physics family the gap is `e^{−mphys·dySpacing N k}` at every step.** At
`mphys ≠ 0` (`gapAt_aPhys`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the excluded unit. -/
theorem physFamily_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} (hm : mphys ≠ 0)
    {βs : ℕ → ℝ} (h : PhysFamily τ p hN mphys βs) (k : ℕ) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN (βs k))
      (Real.exp (-(mphys * ContinuumSchwinger.dySpacing N k))) := by
  rw [← h.2 k]
  exact gapAt_aPhys τ p hN hm (βs k)

#print axioms physFamily_gapAt

/-- **`dyBeta` is a constant-physics family exactly when the lattice mass scales exactly on it.**
At `0 < mphys`: `PhysFamily τ p hN mphys (dyBeta _) ↔
∀ k, latMassP τ p hN (dyBeta _ k) = dySpacing N k · mphys`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `mphys`. -/
theorem physFamily_dyBeta_iff (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} (hm : 0 < mphys) :
    PhysFamily τ p hN mphys
        (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN)) ↔
      ∀ k : ℕ, latMassP τ p hN
          (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k)
        = ContinuumSchwinger.dySpacing N k * mphys := by
  constructor
  · intro h k
    have hk := h.2 k
    rw [aPhys_def] at hk
    exact (div_eq_iff hm.ne').mp hk
  · intro h
    refine ⟨ContinuumSchwinger.tendsto_dyBeta _, fun k => ?_⟩
    rw [aPhys_def]
    exact (div_eq_iff hm.ne').mpr (h k)

#print axioms physFamily_dyBeta_iff

/-- **Under `aPhys / aRun → 1` the constant-physics couplings and `dyBeta` have asymptotically equal
two-loop spacings.** For `PhysFamily τ p hN mphys βs`:
`aRun N (βs k) / aRun N (dyBeta _ k) → 1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count; `1` is the limit ratio. -/
theorem aRun_ratio_physFamily (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} {βs : ℕ → ℝ}
    (hfam : PhysFamily τ p hN mphys βs)
    (hratio : Tendsto (fun β => aPhys τ p hN mphys β / aRun N β) atTop (𝓝 1)) :
    Tendsto (fun k => aRun N (βs k)
        / aRun N (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k))
      atTop (𝓝 1) := by
  have h := (hratio.comp hfam.1).inv₀ one_ne_zero
  rw [inv_one] at h
  refine Filter.Tendsto.congr (fun k => ?_) h
  show (aPhys τ p hN mphys (βs k) / aRun N (βs k))⁻¹
    = aRun N (βs k) / aRun N (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k)
  rw [hfam.2 k, ContinuumSchwinger.aRun_dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN) k,
    inv_div]

#print axioms aRun_ratio_physFamily

end Family

/-! ## 6. E along the constant-physics spacing -/

section Signal

variable {N : ℕ}

/-- **The renormalised lattice Schwinger function at coupling `βs k` and smearing spacing `s k`**:
`∏ᵢ Z k Oᵢ · periodicState hN (βs k) (∏ᵢ smear (s k) (Oᵢ − c k Oᵢ) fᵢ)`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def latSkRAlong (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) (βs s : ℕ → ℝ)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) : ℝ :=
  ρ.pref k F * ContinuumSchwinger.latS (PeriodicState.periodicState hN (βs k)) (s k)
    (fun i => ρ.field k (F i))

#print axioms latSkRAlong

/-- **`ContinuumSchwinger`'s family is the one at `(dyBeta, dySpacing)`.**
`ContinuumSchwinger.latSkR hN ρ k F = latSkRAlong hN ρ (dyBeta _) (dySpacing N) k F`
(`ContinuumSchwinger.latSk_eq`).

DERIVED: `0` is the excluded colour count. -/
theorem latSkR_eq_along (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) (k : ℕ) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) :
    ContinuumSchwinger.latSkR hN ρ k F
      = latSkRAlong hN ρ (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN))
          (ContinuumSchwinger.dySpacing N) k F := by
  unfold ContinuumSchwinger.latSkR latSkRAlong
  exact congrArg (fun t => ρ.pref k F * t)
    (ContinuumSchwinger.latSk_eq hN k (fun i => ρ.field k (F i)))

#print axioms latSkR_eq_along

/-- **A limit along `atTop` is the continuum Schwinger function.** If the `(dyBeta, dySpacing)`
family of `F` converges to `S` along `atTop`, then `ContinuumSchwinger.contS hN ρ F = S`, whatever the
ultrafilter `ContinuumSchwinger.ultra` (`ContinuumSchwinger.ultra_le`,
`Filter.Tendsto.limUnder_eq`).

DERIVED: `0` is the excluded colour count. -/
theorem contS_eq_of_tendsto_along (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) {S : ℝ}
    (h : Tendsto (fun k => latSkRAlong hN ρ
        (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN))
        (ContinuumSchwinger.dySpacing N) k F) atTop (𝓝 S)) :
    ContinuumSchwinger.contS hN ρ F = S := by
  haveI : ((ContinuumSchwinger.ultra : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    Ultrafilter.neBot' ContinuumSchwinger.ultra
  have h' : Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 S) :=
    Filter.Tendsto.congr (fun k => (latSkR_eq_along hN ρ k F).symm) h
  exact (h'.mono_left ContinuumSchwinger.ultra_le).limUnder_eq

#print axioms contS_eq_of_tendsto_along

/-- **The signal converges along a family (open).** For every finite family `F` of smeared fields
whose test-function supports are pairwise `d`-separated for some `d > 0`
(`ContinuumSep.FamSep`), the renormalised lattice Schwinger functions at couplings `βs k` and spacing
`s k` converge along `atTop`. Every separated correlation scales, not only the mass.

DERIVED: `0` is the excluded colour count and the sign of `d`. -/
def SignalConvergesSep (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) (βs s : ℕ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → ContinuumSchwinger.SField N) (d : ℝ), 0 < d →
    ContinuumSep.FamSep d F → ∃ S : ℝ, Tendsto (fun k => latSkRAlong hN ρ βs s k F) atTop (𝓝 S)

#print axioms SignalConvergesSep

/-- **E along the constant-physics spacing (open).** Some constant-physics family `βs` along which
the separated renormalised Schwinger functions, smeared at the spacing `aPhys (βs k)`, converge.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
def ConstantPhysicsE (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (mphys : ℝ)
    (ρ : ContinuumSchwinger.Renorm N) : Prop :=
  ∃ βs : ℕ → ℝ, PhysFamily τ p hN mphys βs ∧
    SignalConvergesSep hN ρ βs (fun k => aPhys τ p hN mphys (βs k))

#print axioms ConstantPhysicsE

/-- **Two coupling sequences read the same signal at the dyadic spacing (open).** For every
separated family, the difference of the renormalised Schwinger functions at couplings `βs k` and
`βs' k`, both smeared at `dySpacing N k`, tends to `0`.

DERIVED: `0` is the excluded colour count, the sign of `d` and the limit. -/
def StateShiftInvisibleSep (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N)
    (βs βs' : ℕ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → ContinuumSchwinger.SField N) (d : ℝ), 0 < d →
    ContinuumSep.FamSep d F →
      Tendsto (fun k => latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F
        - latSkRAlong hN ρ βs' (ContinuumSchwinger.dySpacing N) k F) atTop (𝓝 0)

#print axioms StateShiftInvisibleSep

/-- `StateShiftInvisibleSep hN ρ βs βs`.

DERIVED: `0` is the excluded colour count and the limit. -/
theorem stateShiftInvisible_self (hN : N ≠ 0) (ρ : ContinuumSchwinger.Renorm N) (βs : ℕ → ℝ) :
    StateShiftInvisibleSep hN ρ βs βs := by
  intro ι _ F d _ _
  simp only [sub_self]
  exact tendsto_const_nhds

#print axioms stateShiftInvisible_self

/-- Along a constant-physics family the spacing `aPhys (βs k)` is `dySpacing N k`, so the two
families of lattice functions coincide.

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count. -/
theorem latSkRAlong_physFamily (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {mphys : ℝ} {βs : ℕ → ℝ}
    (hfam : PhysFamily τ p hN mphys βs) (ρ : ContinuumSchwinger.Renorm N) (k : ℕ) {ι : Type}
    [Fintype ι] (F : ι → ContinuumSchwinger.SField N) :
    latSkRAlong hN ρ βs (fun k => aPhys τ p hN mphys (βs k)) k F
      = latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F := by
  show ρ.pref k F * ContinuumSchwinger.latS (PeriodicState.periodicState hN (βs k))
      (aPhys τ p hN mphys (βs k)) (fun i => ρ.field k (F i))
    = ρ.pref k F * ContinuumSchwinger.latS (PeriodicState.periodicState hN (βs k))
      (ContinuumSchwinger.dySpacing N k) (fun i => ρ.field k (F i))
  rw [hfam.2 k]

#print axioms latSkRAlong_physFamily

/-- **E along `aPhys` gives `ContinuumSchwinger`'s limit.** For a constant-physics family `βs` with
`SignalConvergesSep` at the spacing `aPhys (βs k)` and `StateShiftInvisibleSep` between `βs` and
`dyBeta`: every separated family `F` has `ContinuumSchwinger.latSkR hN ρ k F → S` along `atTop` and
`ContinuumSchwinger.contS hN ρ F = S`. The step from `βs` to `dyBeta` is `hshift` alone; the
constant-physics family supplies the spacing (`latSkRAlong_physFamily`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded colour count and the sign of `d`. -/
theorem contS_of_constantPhysics (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    (ρ : ContinuumSchwinger.Renorm N) {mphys : ℝ} {βs : ℕ → ℝ}
    (hfam : PhysFamily τ p hN mphys βs)
    (hsig : SignalConvergesSep hN ρ βs (fun k => aPhys τ p hN mphys (βs k)))
    (hshift : StateShiftInvisibleSep hN ρ βs
      (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN)))
    {ι : Type} [Fintype ι] (F : ι → ContinuumSchwinger.SField N) {d : ℝ} (hd : 0 < d)
    (hF : ContinuumSep.FamSep d F) :
    ∃ S : ℝ, Tendsto (fun k => ContinuumSchwinger.latSkR hN ρ k F) atTop (𝓝 S)
      ∧ ContinuumSchwinger.contS hN ρ F = S := by
  obtain ⟨S, hS⟩ := hsig ι F d hd hF
  have h1 : Tendsto (fun k => latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F)
      atTop (𝓝 S) :=
    Filter.Tendsto.congr (fun k => latSkRAlong_physFamily τ p hN hfam ρ k F) hS
  have h2 : Tendsto (fun k => latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F
      - (latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F
        - latSkRAlong hN ρ
            (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN))
            (ContinuumSchwinger.dySpacing N) k F)) atTop (𝓝 (S - 0)) :=
    h1.sub (hshift ι F d hd hF)
  rw [sub_zero] at h2
  have h3 : Tendsto (fun k => latSkRAlong hN ρ
      (ContinuumSchwinger.dyBeta (ContinuumSchwinger.one_le_of_ne_zero hN))
      (ContinuumSchwinger.dySpacing N) k F) atTop (𝓝 S) :=
    Filter.Tendsto.congr (fun k => sub_sub_cancel
      (latSkRAlong hN ρ βs (ContinuumSchwinger.dySpacing N) k F) _) h2
  exact ⟨S, Filter.Tendsto.congr (fun k => (latSkR_eq_along hN ρ k F).symm) h3,
    contS_eq_of_tendsto_along hN ρ F h3⟩

#print axioms contS_of_constantPhysics

end Signal

end MassGap.ConstantPhysics
