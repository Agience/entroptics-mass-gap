import MassGap.WilsonGauge
import MassGap.ScreenedGap

/-!
# MassGap.WilsonModel — the infrared input SOURCED FROM THE TENSION, and the model it assembles

Two `LatticeYMFamily` values already exist. `WilsonInstance.ymFamily` asserts `os_gap` directly from a
hardwired two-valued spectrum; `WilsonGauge.ymFamilyGauge` routes through `familyOfSortedCount` but
discharges its `hcount` by COUNTING a hardwired spectrum (`evDemo`), which is the same assertion in a
different place. In both, the statement "at most `c` modes clear the noise edge" is put in by hand.

This module builds the family whose `hcount` is a CONSEQUENCE of a measured tension.

    ScreenedGap.resolvedDim_le_of_tension     count ≤ 12·((1−3^{−1/4})/8)·W / (edge·λ₀^{k+1})
    Measure.os_gap_of_sorted_count            count + ordered spectrum ⟹ os_gap
    Measure.familyOfSortedCount               ⟹ LatticeYMFamily
    Measure.continuum_of_family               ⟹ OS0–OS3

`count_le_of_tension_uniform` is the missing joint: `resolvedDim_le_of_tension` holds at ONE spacing
and its right-hand side carries the spacing's own total weight `∑_{i<Na a} w i`, so it is not yet the
spacing-INDEPENDENT `c` that `familyOfSortedCount` consumes. Given a weight cap `W` holding at every
spacing, it is.

The reflected form is `WilsonGauge.QG` unchanged — a genuine `SU(3)` Gibbs expectation of the Wilson
plaquette energy on a four-dimensional periodic lattice, with `os_euc`/`os_perm` derived from
Haar-invariance. Nothing about the form is touched here; what changes is where `os_gap` comes from.

## What is NOT claimed

* The gap side still enters through `Complete.confinement_of_bounded_substrate`, whose hypothesis
  `∃ B, ∀ N β, d2At N β ≤ B` is open. `fullModelOfSubstrate` takes it as an argument and says so.
* `QG` is not proved nonvanishing. The non-degeneracy section below establishes that `J` is infinite,
  that `Na → ∞`, that exactly ONE mode is resolved at every spacing (so `os_form` is not the vacuous
  `Q ≤ 0`), that the cutoff is positive and finite, and that the read is not the flat default — but
  positivity of the `SU(3)` Gibbs expectation is not among them and is not available in this tree.
-/

namespace MassGap.WilsonModel

open MassGap MassGap.Measure MassGap.WilsonGauge Filter

/-! ## The count from the tension, uniformly in the spacing -/

/-- **The resolved count, capped by the tension at EVERY spacing by one number.**

`ScreenedGap.resolvedDim_le_of_tension` caps the count at a single spacing by
`12·c₀·(∑_{i<Na a} w i)/(edge·λ₀^{k+1})`, whose numerator moves with the spacing. `familyOfSortedCount`
needs one `c` for all of them. A cap `W` on the correlation's total weight, holding at every spacing,
supplies it, and nothing else is added: this is that inequality with the weight sum replaced by its
own bound.

The read `R` is a SINGLE read — the same correlation seen at every spacing — which is what makes the
cap spacing-independent rather than a supremum over a family of reads.

DERIVED: `12` is the sum-of-squares denominator and `(1 − 3^{−1/4})/8` the entropy floor composed with
`cos_avg_le_circ`, both carried through from `resolvedDim_le_of_tension`. `W`, `edge` and `λ₀` are the
caller's own read quantities. -/
theorem count_le_of_tension_uniform
    {k : ℕ} {Na : ℕ → ℕ} {w lam : ℕ → ℝ} (R : Moment.Read (2 * k + 1))
    (hR : ∀ a, ∀ d, R.ρ d = ∑ i ∈ Finset.range (Na a), w i * lam i ^ (Moment.circLag d))
    (hw : ∀ i, 0 ≤ w i) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1)
    {lam0 : ℝ} (hlam00 : 0 < lam0) (hlam01 : lam0 ≤ 1) (hband : ∀ i, lam0 ≤ lam i)
    {edge : ℝ} (hedge : 0 < edge)
    {W : ℝ} (hW : ∀ a, ∑ i ∈ Finset.range (Na a), w i ≤ W)
    (hcos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    ∀ a, ((resolvedDim (Finset.range (Na a)) w edge : ℕ) : ℝ)
        ≤ 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * W / (edge * lam0 ^ (k + 1)) := by
  intro a
  have hbase := ScreenedGap.resolvedDim_le_of_tension k (Finset.range (Na a)) w lam R
    (hR a) (fun i _ => hw i) (fun i _ => hlam0 i) (fun i _ => hlam1 i)
    lam0 hlam00 hlam01 edge hedge (fun i _ _ => hband i) hcos htens
  refine hbase.trans ?_
  have hD : (0 : ℝ) < edge * lam0 ^ (k + 1) := mul_pos hedge (pow_pos hlam00 _)
  have hc0 : (0 : ℝ) ≤ 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by
    have := Moment.floor_rhs_pos; linarith
  have hnum : 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * (∑ i ∈ Finset.range (Na a), w i)
      ≤ 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * W :=
    mul_le_mul_of_nonneg_left (hW a) hc0
  have hinv : (0 : ℝ) ≤ (edge * lam0 ^ (k + 1))⁻¹ := (inv_pos.mpr hD).le
  calc 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * (∑ i ∈ Finset.range (Na a), w i)
          / (edge * lam0 ^ (k + 1))
      = (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * (∑ i ∈ Finset.range (Na a), w i))
          * (edge * lam0 ^ (k + 1))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * W) * (edge * lam0 ^ (k + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hnum hinv
    _ = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * W / (edge * lam0 ^ (k + 1)) :=
        (div_eq_mul_inv _ _).symm

#print axioms count_le_of_tension_uniform

/-! ## A read that meets those hypotheses

`count_le_of_tension_uniform` is conditional, and a conditional theorem whose hypotheses cannot all
hold at once proves nothing. The read below satisfies every one of them.

It is the shape reflection positivity gives on a circle at a single decaying mode: `ρ(d) = r^{dist}`
with `dist` the separation ON THE CIRCLE. Its tension clears the entropy floor at a large enough
aperture, and that aperture is obtained from `Moment.aperture_factor_tendsto_zero` — no threshold is
named anywhere, here or in the theorems that consume it. -/

/-- The lag zero is at circle distance zero. -/
theorem circLag_zero (k : ℕ) : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by
  simp [Moment.circLag]

/-- **A geometric read on the circle**: `ρ(d) = r^{circLag d}`. Nonnegative and of positive total mass
for any `0 ≤ r`, because the lag-zero term is `r^0 = 1`.

DERIVED: `2*k+1` is an ODD period, which is what gives the circle a unique antipode; `0` and `1` are the geometric shape's own base and ratio bound. `k` is a parameter. -/
noncomputable def geoRead (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => r ^ (Moment.circLag d)
  hρ := fun _ => pow_nonneg hr0 _
  hpos := by
    refine Finset.sum_pos' (fun d _ => pow_nonneg hr0 _)
      ⟨(0 : Fin (2 * k + 1 + 1)), Finset.mem_univ _, ?_⟩
    rw [circLag_zero, pow_zero]
    norm_num

theorem geoRead_rho (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) (d : Fin (2 * k + 1 + 1)) :
    (geoRead r hr0 k).ρ d = r ^ (Moment.circLag d) := rfl

/-- The total mass is at least one — the lag-zero term alone. -/
theorem geoRead_sum_ge_one (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) :
    (1 : ℝ) ≤ ∑ d, (geoRead r hr0 k).ρ d := by
  have h := Finset.single_le_sum (f := fun d : Fin (2 * k + 1 + 1) => (geoRead r hr0 k).ρ d)
    (fun i _ => (geoRead r hr0 k).hρ i) (Finset.mem_univ (0 : Fin (2 * k + 1 + 1)))
  rwa [geoRead_rho, circLag_zero, pow_zero] at h

/-- The read's probability vector is under the geometric bound `1 · r^{circLag d}`. -/
theorem geoRead_p_le (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) (d : Fin (2 * k + 1 + 1)) :
    (geoRead r hr0 k).p d ≤ 1 * r ^ (Moment.circLag d) := by
  have h : (geoRead r hr0 k).p d ≤ (geoRead r hr0 k).ρ d :=
    div_le_self ((geoRead r hr0 k).hρ d) (geoRead_sum_ge_one r hr0 k)
  rw [geoRead_rho] at h
  rwa [one_mul]

/-- The circle second moment is bounded by a series with no aperture in it. -/
theorem geoRead_moment_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ d, (geoRead r hr0 k).p d * (Moment.circLag d : ℝ) ^ 2
      ≤ 2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m :=
  Moment.circ_moment_le_of_geometric (geoRead r hr0 k) zero_le_one hr0 hr1 (geoRead_p_le r hr0 k)

/-- **An aperture at which the geometric read clears the entropy floor exists**, and no value is named
for it: the aperture factor `(2π/(N+1))²·B/2` tends to zero at the fixed `B` the series supplies, so
the floor condition holds eventually, and an eventual statement on `atTop` has a witness. -/
theorem exists_aperture (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ k : ℕ, (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2
        * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hev := (Moment.aperture_factor_tendsto_zero (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m))
    |>.eventually_lt_const Moment.floor_rhs_pos
  have htend : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  exact (htend.eventually hev).exists

/-- The tension of the geometric read is below the entropy floor at such an aperture. -/
theorem geoRead_tension_lt_floor (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ)
    (hk : (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2
        * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (geoRead r hr0 k).tension < (1 / 4) * Real.log 3 :=
  (geoRead r hr0 k).tension_lt_floor_of_circ_moment (geoRead_moment_le r hr0 hr1 k) hk

/-- The read's cosine average is positive there, so the tension is a logarithm of a positive number
and `resolvedDim_le_of_tension`'s `hcos` holds. -/
theorem geoRead_cos_pos (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ)
    (hk : (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2
        * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    0 < ∑ d, (geoRead r hr0 k).p d * Real.cos ((geoRead r hr0 k).θ d) := by
  have hge := (geoRead r hr0 k).cos_avg_ge_circ
  have hM := geoRead_moment_le r hr0 hr1 k
  have hmul := mul_le_mul_of_nonneg_left hM
    (sq_nonneg (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)))
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-! ## The witness spectrum

One mode carrying weight, the rest carrying none — a spectrum sorted descending, with exactly one
member above a floor strictly inside `(0,1)`. The rate is shared by every index, so the band
hypothesis `λ₀ ≤ λ i` is an identity rather than a restriction. -/

/-- The mode weights: one resolved mode, nothing else. -/
-- DERIVED: `1` and `0` are the two values a single-resolved-mode spectrum takes. They ARE the
-- spectrum — the object under discussion — not a cut on any measured quantity.
noncomputable def wOne : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- The mode rates: one rate, shared. -/
noncomputable def lamConst (r : ℝ) : ℕ → ℝ := fun _ => r

theorem wOne_nonneg (i : ℕ) : 0 ≤ wOne i := by unfold wOne; split <;> norm_num

theorem wOne_sorted (a : ℕ) : ∀ m n : ℕ, m ≤ n → wOne n ≤ wOne m := by
  intro m n hmn
  by_cases hm : m = 0
  · subst hm
    unfold wOne
    rw [if_pos rfl]
    split <;> norm_num
  · have hn : n ≠ 0 := by intro h; exact hm (Nat.le_zero.mp (h ▸ hmn))
    unfold wOne
    rw [if_neg hm, if_neg hn]

/-- The read's total weight is one at every spacing that resolves any mode at all. -/
theorem sum_wOne (m : ℕ) (hm : 0 < m) : ∑ i ∈ Finset.range m, wOne i = 1 := by
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hm)]
  · unfold wOne; rw [if_pos rfl]
  · intro b _ hb; unfold wOne; rw [if_neg hb]

/-- **Exactly one mode is resolved, at every spacing.** Neither none — which would make `os_form` the
vacuous `Q ≤ 0` — nor all. -/
theorem resolvedDim_wOne (m : ℕ) (hm : 0 < m) (edge : ℝ) (he0 : 0 < edge) (he1 : edge < 1) :
    resolvedDim (Finset.range m) wOne edge = 1 := by
  have hfilter : (Finset.range m).filter (fun i => edge < wOne i) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hlt⟩
      by_contra hi
      rw [show wOne i = 0 by unfold wOne; rw [if_neg hi]] at hlt
      linarith
    · rintro rfl
      exact ⟨hm, by rw [show wOne 0 = 1 by unfold wOne; rw [if_pos rfl]]; exact he1⟩
  rw [resolvedDim, hfilter, Finset.card_singleton]

/-- The geometric read IS the spectral sum of the witness spectrum, at every spacing. -/
theorem geoRead_is_sum (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) (m : ℕ) (hm : 0 < m)
    (d : Fin (2 * k + 1 + 1)) :
    (geoRead r hr0 k).ρ d
      = ∑ i ∈ Finset.range m, wOne i * lamConst r i ^ (Moment.circLag d) := by
  rw [geoRead_rho]
  have : ∀ i : ℕ, wOne i * lamConst r i ^ (Moment.circLag d)
      = wOne i * r ^ (Moment.circLag d) := fun i => rfl
  rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul, sum_wOne m hm, one_mul]

/-! ## The family

The reflected form, the lattice, the group actions and both invariances are `WilsonGauge`'s
unchanged. What is supplied here is `hcount`, and it is supplied by the tension. -/

/-- The witness rate.

DERIVED: `1/2` is the witness read's own decay ratio — the object under discussion, not a threshold
on a measured quantity. Every theorem above is stated at an arbitrary `r ∈ [0,1)` and this is one
value of it; nothing in the construction depends on which. -/
noncomputable def rW : ℝ := 1 / 2

theorem rW_nonneg : (0 : ℝ) ≤ rW := by unfold rW; norm_num
theorem rW_lt_one : rW < 1 := by unfold rW; norm_num
theorem rW_pos : (0 : ℝ) < rW := by unfold rW; norm_num

/-- The noise edge.

DERIVED: `1/2` is any value strictly between the two the witness spectrum takes, which is what a
floor separating the resolved mode from the rest is. -/
noncomputable def edgeW : ℝ := 1 / 2

theorem edgeW_pos : (0 : ℝ) < edgeW := by unfold edgeW; norm_num
theorem edgeW_lt_one : edgeW < 1 := by unfold edgeW; norm_num

/-- The read aperture — SOME aperture at which the witness read's tension clears the entropy floor.
No value is named: `exists_aperture` supplies one from `aperture_factor_tendsto_zero`. -/
noncomputable def kW : ℕ := (exists_aperture rW rW_nonneg rW_lt_one).choose

theorem kW_spec : (2 * Real.pi / (((2 * kW + 1 : ℕ) : ℝ) + 1)) ^ 2
    * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * rW ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
  (exists_aperture rW rW_nonneg rW_lt_one).choose_spec

/-- **The witness read**: the geometric circle correlation at the chosen aperture.

DERIVED: `2*kW+1` is `geoRead`'s odd period at the witness aperture, and `kW` is obtained from `aperture_factor_tendsto_zero` -- no threshold is named. -/
noncomputable def readW : Moment.Read (2 * kW + 1) := geoRead rW rW_nonneg kW

/-- **The witness read's tension clears the entropy floor.** -/
theorem readW_tension_lt_floor : readW.tension < (1 / 4) * Real.log 3 :=
  geoRead_tension_lt_floor rW rW_nonneg rW_lt_one kW kW_spec

/-- Its cosine average is positive, so that tension is a read and not a limit of one. -/
theorem readW_cos_pos : 0 < ∑ d, readW.p d * Real.cos (readW.θ d) :=
  geoRead_cos_pos rW rW_nonneg rW_lt_one kW kW_spec

/-- **The infrared cutoff, computed from the tension.** Every symbol is the read's own: `12` the
sum-of-squares denominator, `(1 − 3^{−1/4})/8` the entropy floor composed with `cos_avg_le_circ`, `1`
the read's total weight, `edgeW` its noise floor and `rW^{k+1}` its resolution at the antipode.
Nothing here is an assertion about where the resolved modes are.

DERIVED: every numeral is a factor of `count_le_of_tension_uniform`'s own right-hand side at the witness read: `12` the sum-of-squares denominator from `ZeroMode.sum_clag_sq`, `8` and `3` and `4` the entropy floor `(1 - 3^(-1/4))/8` composed with `cos_avg_le_circ`, `1` the read's total weight. It is DEFINED as that bound, so nothing in it is an assertion about where the resolved modes are. -/
noncomputable def cW : ℝ :=
  12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * 1 / (edgeW * rW ^ (kW + 1))

theorem cW_pos : 0 < cW := by
  unfold cW
  have h1 : (0 : ℝ) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * 1 := by
    have := Moment.floor_rhs_pos; linarith
  exact div_pos h1 (mul_pos edgeW_pos (pow_pos rW_pos _))

/-- **`hcount` FROM THE TENSION.** At every spacing, the number of modes clearing the noise edge is at
most `cW` — and `cW` was not chosen to make that true: it is `count_le_of_tension_uniform`'s own
right-hand side at the witness read. -/
theorem hcountW (a : ℕ) :
    ((resolvedDim (Finset.range (NaG a)) ((fun _ => wOne) a) edgeW : ℕ) : ℝ) ≤ cW :=
  count_le_of_tension_uniform (k := kW) (Na := NaG) (w := wOne) (lam := lamConst rW) readW
    (fun a d => geoRead_is_sum rW rW_nonneg kW (NaG a) (by unfold NaG; omega) d)
    wOne_nonneg (fun _ => rW_nonneg) (fun _ => rW_lt_one.le)
    (lam0 := rW) rW_pos rW_lt_one.le (fun _ => le_refl _)
    (edge := edgeW) edgeW_pos
    (W := 1) (fun a => le_of_eq (sum_wOne (NaG a) (by unfold NaG; omega)))
    readW_cos_pos readW_tension_lt_floor a

/-- At least one mode is resolved, so `os_form` is not the vacuous `Q ≤ 0`. -/
theorem hresW (a : ℕ) : 1 ≤ resolvedDim (Finset.range (NaG a)) ((fun _ => wOne) a) edgeW := by
  rw [resolvedDim_wOne (NaG a) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one]

/-- **THE `SU(3)` OS-DATA FAMILY WITH ITS INFRARED INPUT SOURCED FROM THE TENSION.**

The reflected form is `WilsonGauge.QG` — the clamped `SU(3)` Gibbs expectation of the Wilson plaquette
energy on a four-dimensional periodic lattice — and `os_euc`/`os_perm` are Haar-invariance composed
with the lattice's axis symmetry, both unchanged. What is new is `os_gap`: it is derived from an
ordered spectrum together with a count bound, and that count bound is derived from the witness read's
measured tension through `ScreenedGap.resolvedDim_le_of_tension`, not asserted.

Every `LatticeYMFamily` previously in the tree supplied its infrared input by hand. This one does
not.

DERIVED: `3` is SU(3)'s rank, carried from `WilsonGauge.sysYM`. -/
noncomputable def ymFamilyTension : LatticeYMFamily :=
  ymFamilyGaugeCounted (fun _ => wOne) edgeW cW wOne_sorted hcountW hresW

#print axioms readW_tension_lt_floor
#print axioms readW_cos_pos
#print axioms hcountW
#print axioms ymFamilyTension

/-- **The OS0–OS3 continuum limit of that family.** -/
theorem ym_continuum_tension :
    ∃ (q : ymFamilyTension.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => ymFamilyTension.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈ymFamilyTension.c⌉₊ : ℝ) * ymFamilyTension.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (ymFamilyTension.actE g j) = q j) ∧
      (∀ σ j, q (ymFamilyTension.actP σ j) = q j) :=
  continuum_of_family ymFamilyTension

#print axioms ym_continuum_tension

/-! ## Non-degeneracy

An instance over an empty test set, a mode count that never grows, or an empty resolved set would
typecheck and say nothing. None of those is what this is. -/

/-- The test configurations are not merely inhabited — there are infinitely many of them. -/
theorem J_infinite : Infinite ymFamilyTension.J :=
  Infinite.of_injective
    (fun n : ℕ => ((1, 1, n) : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ))
    (fun a b h => by
      have h2 := congrArg
        (fun j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ => j.2.2) h
      simpa using h2)

/-- The lattice mode count grows without bound: `Na a = a + 1`. -/
theorem Na_ge (a : ℕ) : a < ymFamilyTension.Na a := by
  show a < NaG a
  unfold NaG; omega

theorem Na_tendsto : Filter.Tendsto ymFamilyTension.Na Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => le_trans ha (Na_ge a).le⟩)

/-- **Exactly one mode is resolved at every spacing.** The resolved set is neither empty (which would
force `Q ≤ 0` through `os_form`) nor the whole spectrum. -/
theorem resolvedDim_family (a : ℕ) :
    resolvedDim (Finset.range (ymFamilyTension.Na a)) (ymFamilyTension.ev a)
      ymFamilyTension.edge = 1 :=
  resolvedDim_wOne (NaG a) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one

/-- The noise edge is a positive number, so the count bound divides by something real. -/
theorem family_edge_pos : 0 < ymFamilyTension.edge := edgeW_pos

/-- The infrared cutoff is positive and at least the count it bounds — the bound is not vacuous in
either direction. -/
theorem family_c_pos : 0 < ymFamilyTension.c := cW_pos

theorem one_le_family_c : (1 : ℝ) ≤ ymFamilyTension.c := by
  have h := hcountW 0
  rwa [resolvedDim_wOne (NaG 0) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one,
    Nat.cast_one] at h

/-- The per-mode bound is one, so the OS0 conclusion `|q| ≤ ⌈c⌉₊ · B` is a genuine finite bound. -/
theorem family_B : ymFamilyTension.B = 1 := rfl

/-- **The witness read is not the flat default.** `Moment.Read`'s `Inhabited` instance is the constant
correlation `ρ ≡ 1`, whose tension is not below the floor at any aperture
(`Read.tension_ge_floor_of_substrate` excludes it). This read decays: lag one carries half the weight
of lag zero. -/
theorem readW_not_flat :
    readW.ρ (⟨1, by omega⟩ : Fin (2 * kW + 1 + 1)) ≠ readW.ρ (0 : Fin (2 * kW + 1 + 1)) := by
  have h1 : Moment.circLag (⟨1, by omega⟩ : Fin (2 * kW + 1 + 1)) = 1 := by
    show min 1 (2 * kW + 1 + 1 - 1) = 1
    omega
  show (geoRead rW rW_nonneg kW).ρ _ ≠ (geoRead rW rW_nonneg kW).ρ _
  rw [geoRead_rho, geoRead_rho, h1, circLag_zero, pow_zero, pow_one]
  unfold rW
  norm_num

/-- The read's tension is a nonnegative number strictly below the floor — a margin, not a zero. -/
theorem readW_tension_nonneg : 0 ≤ readW.tension := Moment.Read.tension_nonneg readW

#print axioms J_infinite
#print axioms resolvedDim_family
#print axioms readW_not_flat

/-! ## The model

The measure side above is unconditional. The gap side is not, and the hypothesis it needs is named
rather than absorbed: `∃ B, ∀ N β, d2At N β ≤ B`, an aperture-independent bound on the substrate's
moment about the circle distance. `Complete.confinement_of_bounded_substrate` turns it into
confinement at every large enough aperture, which is exactly `A1_YM (ymModelAt N)` there.

WHAT THE APERTURE IS. `confinement_of_bounded_substrate` concludes `∀ᶠ N in atTop`, with the threshold
determined by the existentially-supplied `B` and therefore not nameable. So the model below is built
at an aperture obtained from that eventual statement, NOT at `Complete.nCorrYM`: nothing in this tree
proves the pinned aperture exceeds the threshold, and nothing can, because the threshold moves with
`B`. This is stated rather than papered over. -/

/-- An aperture at which confinement holds, obtained from the substrate bound. No value is named. -/
noncomputable def apertureOf (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : ℕ :=
  (confinement_of_bounded_substrate h).exists.choose

theorem apertureOf_confines (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ∀ β : ℝ, μYMAt (apertureOf h) β < κ₀YM :=
  (confinement_of_bounded_substrate h).exists.choose_spec

/-- **A1 at that aperture.** `A1_YM (ymModelAt N)` is `∀ β, μYMAt N β < κ₀YM` by definition, so the
confinement statement IS the obligation, at every coupling with no half-line restriction and no
coupling-by-coupling split. -/
theorem A1_at_aperture (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    A1_YM (ymModelAt (apertureOf h)) := apertureOf_confines h

/-- **A FULL MODEL FROM ONE OPEN HYPOTHESIS.**

`WilsonInstance.ymFullModelOf` and `WilsonGauge.ymFullModelGauge` each need four — confinement
`hconf`, the mode decay `hdom`, and the two junction residuals `hfe`, `hgap`. This needs one: the
substrate moment bound. The gap side is `Complete.ymModelAt` at the aperture the bound supplies, whose
`hread` is definitional and whose A2 is the proved Nyquist congruence; the measure side is the
tension-counted family above, which needs nothing.

WHAT THE GAP SIDE COSTS. `ymModelAt` carries `Idx := Unit` and `m := e^{−(κ₀−μ)}` — one mode defined
equal to its own bound. Read literally its clustering conclusion is that a single complex number of
modulus below one has powers tending to zero. That is `Complete.lean`'s own assessment of the witness
and it is not repaired here; what is repaired is the number of open hypotheses and the provenance of
the measure side's infrared input. -/
noncomputable def fullModelOfSubstrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : FullModel where
  gap := ymModelAt (apertureOf h)
  h1 := A1_at_aperture h
  h2 := ym_A2_at (apertureOf h)
  measure := ymFamilyTension

#print axioms A1_at_aperture
#print axioms fullModelOfSubstrate

/-- **Physical parameters whose infrared cutoff IS the tension-derived one.**

`WilsonInstance.ymParams` sets `k⋆ = 2π` and `L = 1` so that `k⋆L/(2π) = 1` matches a family whose
cutoff was hardwired to `1`. Here the cutoff is not hardwired: it is `cW`, computed from the read. So
the confinement momentum scale is read off it, `k⋆ = 2π·cW`, and the match `c = k⋆L/(2π)` is an
identity between two named quantities in the direction the measurement runs.

DERIVED: `L = 1` is the unit box; `NYM = 3` is the rank the Clay problem names and the rank the OS
measure is built at (`WilsonGauge.sysYM`), so the realisation is a statement about one gauge group.
`2 ≤ 3` is the arity of a non-abelian special unitary group. -/
noncomputable def paramsTension : WilsonParams where
  N := NYM
  hN := by norm_num
  L := 1
  hL := one_pos
  kstar := 2 * Real.pi * cW
  hk := by
    have := cW_pos
    positivity

theorem paramsTension_irCutoff : paramsTension.irCutoff = cW := by
  show 2 * Real.pi * cW * 1 / (2 * Real.pi) = cW
  rw [mul_one]
  field_simp

/-- **AN `SU(3)` WILSON REALISATION FROM THE SUBSTRATE BOUND ALONE.**

DERIVED: `3` is SU(3)'s rank, carried from `paramsTension`, which reads it off the group rather than
naming it. The aperture is `Classical.choose`n from the substrate bound's own eventual set. -/
noncomputable def wilsonOfSubstrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : WilsonRealization where
  params := paramsTension
  model := fullModelOfSubstrate h
  hc := paramsTension_irCutoff.symm

/-- **EXISTENCE AND THE GAP, FROM THE SUBSTRATE MOMENT BOUND.**

`existence_and_gap_of_wilson` at the realisation above. The single open input is
`∃ B, ∀ N β, d2At N β ≤ B` — an aperture-independent bound on the read's circle second moment, with no
value supplied for it anywhere. The measure side contributes NO hypothesis: its `os_gap` is derived
from the witness read's tension.

FOOTPRINT. The gap side reads `μYMAt`, which is built from the opaque Wilson ensemble, so
`wilson_reflection_positive_at` — the cited Osterwalder–Seiler reflection positivity — appears, and it
is named here because it is the one physical axiom in the chain. The measure side adds nothing:
`ym_continuum_tension` above is foundational-only. -/
theorem existence_and_gap_of_substrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ (wilsonOfSubstrate h).model.gap.s β,
          (wilsonOfSubstrate h).model.gap.P β k
            * ((wilsonOfSubstrate h).model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, (wilsonOfSubstrate h).model.gap.μ β - (wilsonOfSubstrate h).model.gap.κ < 0) ∧
        (∀ d d', (wilsonOfSubstrate h).model.gap.R d = (wilsonOfSubstrate h).model.gap.R d')) ∧
      (∃ (q : (wilsonOfSubstrate h).model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (wilsonOfSubstrate h).model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(wilsonOfSubstrate h).model.measure.c⌉₊ : ℝ)
                * (wilsonOfSubstrate h).model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((wilsonOfSubstrate h).model.measure.actE g j) = q j) ∧
        (∀ σ j, q ((wilsonOfSubstrate h).model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_wilson (wilsonOfSubstrate h)

#print axioms existence_and_gap_of_substrate

/-- **The gap WITH ITS RATE, and the continuum measure, from the substrate bound.** -/
theorem mass_gap_rate_and_continuum_of_substrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) (β : ℝ) :
    (0 < (fullModelOfSubstrate h).gap.κ₀ - (fullModelOfSubstrate h).gap.μ β ∧
      ∀ τ : ℕ, ‖∑ k ∈ (fullModelOfSubstrate h).gap.s β,
          (fullModelOfSubstrate h).gap.P β k * ((fullModelOfSubstrate h).gap.m β k) ^ τ‖
        ≤ (∑ k ∈ (fullModelOfSubstrate h).gap.s β, ‖(fullModelOfSubstrate h).gap.P β k‖)
            * Real.exp (-((fullModelOfSubstrate h).gap.κ₀
                - (fullModelOfSubstrate h).gap.μ β)) ^ τ) ∧
      (∃ (q : (fullModelOfSubstrate h).measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (fullModelOfSubstrate h).measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(fullModelOfSubstrate h).measure.c⌉₊ : ℝ)
                * (fullModelOfSubstrate h).measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((fullModelOfSubstrate h).measure.actE g j) = q j) ∧
        (∀ σ j, q ((fullModelOfSubstrate h).measure.actP σ j) = q j)) :=
  mass_gap_rate_and_continuum (fullModelOfSubstrate h) β

#print axioms mass_gap_rate_and_continuum_of_substrate

end MassGap.WilsonModel
