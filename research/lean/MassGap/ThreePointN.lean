import Mathlib
import MassGap.NonGaussFromScale

/-!
# MassGap.ThreePointN — what the three-point clause `ThreePointAtScale` reads, in its narrowest form

`SUNFromScale.clayStatement_of_flow` takes, at every `N ≥ 2`, the input
`∃ ℓ > 0, NonGaussFromScale.ThreePointAtScale hN ℓ` (equivalent to `InputsTriage.ObsLower` at `zFix`,
`NonGaussFromScale.obsLower_zFix_iff`). This module states which couplings and which quantity the clause
reads, and puts it in the form with no constant. Declarations are in the namespace `MassGap.ThreePointN`.

## 1. The normalised reading

`bareNorm3 hN k a b c = bareRead3 hN k a b c / a_k¹²`, `a_k = dySpacing N k`: the connected three-point
reading of the observer's field `obs N` in the Wilson state at `dyBeta k`, divided by the canonical
scaling of three dimension-`4` insertions. `obsRead_zFix_eq_norm`: the renormalised reading at `zFix` is
`8 · bareNorm3`.

## 2. The clause reads only weak coupling (proved)

* `ultra_dyBeta_ge`: for every `B`, the steps with `B ≤ dyBeta k` form a set of `ultra`.
* `ultra_ge`: for every `K`, the steps `k ≥ K` form a set of `ultra`.
* `threePointAtScale_iff_above`: for every `B`, `ThreePointAtScale hN ℓ` holds exactly when its bound
  holds on a set of `ultra` contained in `{k | B ≤ dyBeta k}`.

So the clause is not a statement at one lattice spacing or one coupling: it is unchanged by the readings
at any finite set of steps, and in particular at every coupling below any bound `B`, including the
strong-coupling ranges `|β| ≤ 1/65536` of `StrongKernelNear` and `β ≤ β₀` of `VortexStrong`
(`NonGaussFromScale.dyBeta_outside_strong`: every step is outside them). It is a statement about the
`ultra` limit of `bareNorm3` as `β = dyBeta k → ∞` at fixed physical separation `ℓ`, i.e. lattice
separation `ℓ / a_k → ∞`. A strong-coupling computation at a fixed `β` does not enter it.

## 3. The form with no constant (proved)

* **`threePointAtScale_iff_not_tendsto`**: `ThreePointAtScale hN ℓ` holds exactly when some continuous,
  pairwise `ℓ`-separated triple has `bareNorm3 hN k a b c` not tending to `0` along `ultra`. The constant
  `κ` is removed by the ultrafilter dichotomy: a sequence that does not tend to `0` along an ultrafilter is
  bounded away from `0` on a set of it.
* `threePointAtScale_anti`: the clause at `ℓ` gives it at every `ℓ' ≤ ℓ` (separation is antitone).
* **`exists_threePointAtScale_iff`**: `∃ ℓ > 0, ThreePointAtScale hN ℓ` holds exactly when some
  continuous triple, pairwise separated by some `d > 0`, has `bareNorm3` not tending to `0` along `ultra`.

So the open input at each `N` is: the normalised connected three-point reading of `obs N` at one
separated triple does not vanish in the weak-coupling limit along `ultra`. It is the continuum clause
`NonGaussianT` (`InputsTriage.nonGaussianT_rhoD_iff_lower` under `SepConv`) with the normalisation
`z_sc = 2/a_k⁴` divided out; a statement about finitely many steps, or about couplings below any bound, does
not determine it (`threePointAtScale_iff_above`). Nothing here discharges the clause: every result is an
equivalence or a restriction, and `∃ ℓ > 0, ThreePointAtScale hN ℓ` stays an input of
`SUNFromScale.clayStatement_of_flow` at every `N ≥ 2`.

## 4. Relation to the other inputs (argued, not formalised)

`SubstrateCoreAt.scale` (`ScaleControlAll`) bounds moments from above, and `SubstrateCoreAt.af` is a
two-point statement (`TwoPointKernel` with `AFCoefficient`: `r⁸ G(r) log² r → afConst N` as `r → 0`).
Neither bounds a connected function of order three from below, and no declaration of the tree derives a
three-point lower bound from them. The link that would connect them is the lattice identity
`∂_β ν_β(O_y O_z)ᶜ = Σ_x ν_β(P_x O_y O_z)ᶜ` (a three-point function with one insertion summed over the
volume) together with the running `a(β)`: a two-point function that is not a pure power of `r` (which
`AFCoefficient` asserts through its `log² r`) has a non-zero scale derivative, and with contact terms
at `x = y`, `x = z` subtracted that derivative is a separated three-point reading. The tree has no
`β`-derivative of `PeriodicState.periodicState` and no bound on the contact terms; each is a separate
statement. `ShortDistance.treeThreeTr_eq_zero` makes the tree value of the trace three-point function
vanish, so the short-distance expansion at leading order gives no lower bound either.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `3` the number of insertions; `4` the dimension of the field; `12 = 3 · 4`;
`8 = 2³` as in `NonGaussFromScale.obsRead_zFix`; `0` the limit value and the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ThreePointN

open Filter
open scoped Topology
open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.NonGaussFromScale

variable {N : ℕ}

/-! ## 1. The normalised reading -/

/-- **The normalised bare three-point reading**: `bareRead3 / a_k¹²`. DERIVED: `12 = 3 · 4`. -/
def bareNorm3 (hN : N ≠ 0) (k : ℕ) (a b c : TestFn) : ℝ :=
  bareRead3 hN k a b c / dySpacing N k ^ 12

/-- **The renormalised reading at `zFix` is `8 · bareNorm3`.** DERIVED: `8 = 2³`. -/
theorem obsRead_zFix_eq_norm (hN : N ≠ 0) (zri zwe : ℕ → ℝ) (k : ℕ) (a b c : TestFn) :
    NonGaussLink.obsRead hN (ZCanon.zFix N zri zwe) k ![a, b, c] = 8 * bareNorm3 hN k a b c := by
  rw [obsRead_zFix, bareNorm3, mul_div_assoc', div_mul_eq_mul_div]

/-- `|bareNorm3| · a_k¹² = |bareRead3|`. DERIVED: `12` as in `bareNorm3`. -/
theorem abs_bareNorm3_mul (hN : N ≠ 0) (k : ℕ) (a b c : TestFn) :
    |bareNorm3 hN k a b c| * dySpacing N k ^ 12 = |bareRead3 hN k a b c| := by
  have h12 := dySpacing_pow12_pos hN k
  rw [bareNorm3, abs_div, abs_of_pos h12, div_mul_cancel₀ _ h12.ne']

/-! ## 2. The clause reads only weak coupling -/

/-- **Every tail of steps is a set of `ultra`.** DERIVED: no numeral. -/
theorem ultra_ge (K : ℕ) : ∀ᶠ k in (ultra : Filter ℕ), K ≤ k :=
  ultra_le (eventually_ge_atTop K)

/-- **The couplings above any bound form a set of `ultra`.** DERIVED: `1` the least colour count. -/
theorem ultra_dyBeta_ge (hN : 1 ≤ N) (B : ℝ) : ∀ᶠ k in (ultra : Filter ℕ), B ≤ dyBeta hN k :=
  ultra_le ((tendsto_dyBeta hN).eventually (eventually_ge_atTop B))

/-- **The clause is its restriction to couplings above any bound `B`.** DERIVED: `12` as in
`bareNorm3`; `0` the sign of `κ`. -/
theorem threePointAtScale_iff_above (hN : N ≠ 0) (ℓ B : ℝ) :
    ThreePointAtScale hN ℓ ↔
      ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
        ∧ ContinuumSep.sepBy ℓ a b ∧ ContinuumSep.sepBy ℓ a c ∧ ContinuumSep.sepBy ℓ b c
        ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k in (ultra : Filter ℕ),
            B ≤ dyBeta (one_le_of_ne_zero hN) k
              ∧ κ * dySpacing N k ^ 12 ≤ |bareRead3 hN k a b c| := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc, κ, hκ, hev⟩
    exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc, κ, hκ,
      (ultra_dyBeta_ge (one_le_of_ne_zero hN) B).and hev⟩
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc, κ, hκ, hev⟩
    exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc, κ, hκ, hev.mono fun _ hk => hk.2⟩

/-! ## 3. The form with no constant -/

/-- **The bound at one triple is the non-vanishing of the normalised limit.** For a fixed triple,
`∃ κ > 0, κ a_k¹² ≤ |bareRead3|` on a set of `ultra` holds exactly when `bareNorm3` does not tend to `0`
along `ultra`. DERIVED: `12` as in `bareNorm3`; `0` the limit and the sign of `κ`. -/
theorem lower_iff_not_tendsto (hN : N ≠ 0) (a b c : TestFn) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k in (ultra : Filter ℕ),
        κ * dySpacing N k ^ 12 ≤ |bareRead3 hN k a b c|)
      ↔ ¬ Tendsto (fun k => bareNorm3 hN k a b c) (ultra : Filter ℕ) (𝓝 0) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  constructor
  · rintro ⟨κ, hκ, hev⟩ ht
    have hsmall : ∀ᶠ k in (ultra : Filter ℕ), |bareNorm3 hN k a b c| < κ := by
      have := (Metric.tendsto_nhds.mp ht) κ hκ
      exact this.mono fun k hk => by simpa [Real.dist_eq] using hk
    obtain ⟨k, hk1, hk2⟩ := (hev.and hsmall).exists
    have h12 := dySpacing_pow12_pos hN k
    rw [← abs_bareNorm3_mul] at hk1
    have := (mul_le_mul_iff_left₀ h12).mp hk1
    linarith
  · intro ht
    rw [Metric.tendsto_nhds] at ht
    obtain ⟨ε, hε, hnot⟩ : ∃ ε : ℝ, 0 < ε
        ∧ ¬ ∀ᶠ k in (ultra : Filter ℕ), dist (bareNorm3 hN k a b c) 0 < ε := by
      by_contra hc
      exact ht fun ε hε => by
        by_contra hn
        exact hc ⟨ε, hε, hn⟩
    have hbig : ∀ᶠ k in (ultra : Filter ℕ), ¬ dist (bareNorm3 hN k a b c) 0 < ε :=
      Ultrafilter.eventually_not.mpr hnot
    refine ⟨ε, hε, hbig.mono fun k hk => ?_⟩
    have h12 := dySpacing_pow12_pos hN k
    rw [Real.dist_eq, sub_zero, not_lt] at hk
    rw [← abs_bareNorm3_mul]
    exact mul_le_mul_of_nonneg_right hk h12.le

/-- **`ThreePointAtScale` with no constant**: some continuous, pairwise `ℓ`-separated triple whose
normalised reading does not tend to `0` along `ultra`. DERIVED: `0` the limit. -/
theorem threePointAtScale_iff_not_tendsto (hN : N ≠ 0) (ℓ : ℝ) :
    ThreePointAtScale hN ℓ ↔
      ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
        ∧ ContinuumSep.sepBy ℓ a b ∧ ContinuumSep.sepBy ℓ a c ∧ ContinuumSep.sepBy ℓ b c
        ∧ ¬ Tendsto (fun k => bareNorm3 hN k a b c) (ultra : Filter ℕ) (𝓝 0) := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc, h⟩
    exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc, (lower_iff_not_tendsto hN a b c).mp h⟩
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc, h⟩
    exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc, (lower_iff_not_tendsto hN a b c).mpr h⟩

/-- Separation is antitone in the distance. DERIVED: no numeral. -/
theorem sepBy_anti {d d' : ℝ} (h : d' ≤ d) {f g : TestFn} (hfg : ContinuumSep.sepBy d f g) :
    ContinuumSep.sepBy d' f g := fun y z hy hz =>
  let ⟨i, hi⟩ := hfg y z hy hz
  ⟨i, h.trans hi⟩

/-- **The clause at `ℓ` gives it at every `ℓ' ≤ ℓ`.** DERIVED: no numeral. -/
theorem threePointAtScale_anti (hN : N ≠ 0) {ℓ ℓ' : ℝ} (h : ℓ' ≤ ℓ)
    (h3 : ThreePointAtScale hN ℓ) : ThreePointAtScale hN ℓ' := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, hrest⟩ := h3
  exact ⟨a, b, c, ha, hb, hc, sepBy_anti h hab, sepBy_anti h hac, sepBy_anti h hbc, hrest⟩

/-- **The input of `SUNFromScale` in its narrowest form**: `∃ ℓ > 0, ThreePointAtScale hN ℓ` holds
exactly when some continuous triple, pairwise separated by some `d > 0`, has its normalised connected
three-point reading not tending to `0` along `ultra`. DERIVED: `0` the limit and the sign of `d`. -/
theorem exists_threePointAtScale_iff (hN : N ≠ 0) :
    (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale hN ℓ) ↔
      ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
        ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
            ∧ ContinuumSep.sepBy d b c)
        ∧ ¬ Tendsto (fun k => bareNorm3 hN k a b c) (ultra : Filter ℕ) (𝓝 0) := by
  constructor
  · rintro ⟨ℓ, hℓ, h⟩
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, ht⟩ :=
      (threePointAtScale_iff_not_tendsto hN ℓ).mp h
    exact ⟨a, b, c, ha, hb, hc, ⟨ℓ, hℓ, hab, hac, hbc⟩, ht⟩
  · rintro ⟨a, b, c, ha, hb, hc, ⟨d, hd, hab, hac, hbc⟩, ht⟩
    exact ⟨d, hd, (threePointAtScale_iff_not_tendsto hN d).mpr
      ⟨a, b, c, ha, hb, hc, hab, hac, hbc, ht⟩⟩

end MassGap.ThreePointN

end

#print axioms MassGap.ThreePointN.obsRead_zFix_eq_norm
#print axioms MassGap.ThreePointN.abs_bareNorm3_mul
#print axioms MassGap.ThreePointN.ultra_ge
#print axioms MassGap.ThreePointN.ultra_dyBeta_ge
#print axioms MassGap.ThreePointN.threePointAtScale_iff_above
#print axioms MassGap.ThreePointN.lower_iff_not_tendsto
#print axioms MassGap.ThreePointN.threePointAtScale_iff_not_tendsto
#print axioms MassGap.ThreePointN.sepBy_anti
#print axioms MassGap.ThreePointN.threePointAtScale_anti
#print axioms MassGap.ThreePointN.exists_threePointAtScale_iff
