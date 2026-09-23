import MassGap.WilsonGauge
import MassGap.ScreenedGap

/-!
# MassGap.WilsonModel — a `LatticeYMFamily` whose count bound is read off a tension

Two `LatticeYMFamily` values already exist. `WilsonInstance.ymFamily` supplies `os_gap` from a
two-valued spectrum written into its own definition; `WilsonGauge.ymFamilyGauge` routes through
`familyOfSortedCount` and discharges `hcount` by counting the fixed spectrum `evDemo`. In both, the
bound "at most `c` modes clear the noise edge" is supplied as data.

The family assembled here discharges `hcount` from a tension read instead, along

    ScreenedGap.resolvedDim_le_of_tension     count ≤ 12·((1−3^{−1/4})/8)·W / (edge·λ₀^{k+1})
    Measure.os_gap_of_sorted_count            count + ordered spectrum ⟹ os_gap
    Measure.familyOfSortedCount               ⟹ LatticeYMFamily
    Measure.continuum_of_family               ⟹ the continuum conclusions

`count_le_of_tension_uniform` is the joint between the first two. `resolvedDim_le_of_tension` holds at
one spacing and its right-hand side carries that spacing's own total weight `∑_{i<Na a} w i`, while
`familyOfSortedCount` consumes one spacing-independent `c`. A cap `W` on the total weight, holding at
every spacing, supplies that `c`.

The reflected form is `WilsonGauge.QG` and is taken over unchanged, together with `os_euc` and
`os_perm`. What this module supplies is `os_gap`.

Scope. The gap side enters through `Complete.confinement_of_bounded_substrate`, whose hypothesis
`∃ B, ∀ N β, d2At N β ≤ B` is an argument of `fullModelOfSubstrate` and is not discharged here.
Nothing here states that `QG` is nonvanishing. The non-degeneracy section establishes that `J` is
infinite, that `Na → ∞`, that one mode is resolved at every spacing, that the noise edge and the
cutoff are positive, and that the witness read takes different values at lag zero and lag one.
-/

namespace MassGap.WilsonModel

open MassGap MassGap.Measure MassGap.WilsonGauge Filter

/-! ## The count from the tension, uniformly in the spacing -/

/-- One number caps the resolved count at every spacing.

Given a read `R : Moment.Read (2 * k + 1)` whose correlation is the spectral sum
`ρ d = ∑_{i < Na a} w i · lam i ^ circLag d` at every spacing `a`, with nonnegative weights, rates in
`[lam0, 1]` for a positive `lam0 ≤ 1`, a positive noise edge, a cap `W` on the total weight holding at
every spacing, a positive cosine average and a tension below `(1/4)·log 3`, the count of modes above
the edge satisfies `resolvedDim ≤ 12·((1 − 3^{−1/4})/8)·W / (edge·lam0^{k+1})` at every spacing.

`ScreenedGap.resolvedDim_le_of_tension` supplies the same bound at a single spacing with
`∑_{i < Na a} w i` in place of `W`; the content here is that `hW` replaces that spacing-dependent
numerator, so the right-hand side no longer mentions `a`. The read `R` is one read, shared by every
spacing through `hR`, not a family of reads.

DERIVED: `2 * k + 1` is the read's odd period, inherited from `Moment.Read`; the `0` and `1` in `hw`,
`hlam0`, `hlam1`, `hlam00`, `hlam01`, `hedge` and `hcos` are the ends of the weight and rate ranges
and the sign conditions; `(1/4)·log 3` is the entropy floor `κ₀` that `resolvedDim_le_of_tension`
compares the tension against; `12` is the sum-of-squares denominator and `(1 − 3^{−1/4})/8` the
entropy floor composed with `cos_avg_le_circ`, both carried through from that theorem, and the `1` in
`lam0^(k+1)` is the antipodal lag at aperture `k`. `W`, `edge` and `lam0` are the caller's own read
quantities. -/
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

`count_le_of_tension_uniform` is conditional. The read below satisfies each of its hypotheses, so the
 theorem is not vacuous.

The read is geometric in the circle distance, `ρ(d) = r^{circLag d}`, for a ratio `r ∈ [0, 1)`. Its
tension is below the entropy floor at a large enough aperture, and that aperture is obtained from
`Moment.aperture_factor_tendsto_zero` rather than named. -/

/-- The lag-zero index of the circle is at circle distance zero.

DERIVED: the `0` on the left is the zero index of `Fin (2 * k + 1 + 1)` and the `0` on the right is
its circle distance; `2 * k + 1` is the read's odd period and the outer `+ 1` is the number of lags
such a period carries. -/
theorem circLag_zero (k : ℕ) : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by
  simp [Moment.circLag]

/-- A geometric read on the circle: `ρ d = r ^ circLag d`, for any `r` with `0 ≤ r`. Its `hρ` field is
nonnegativity of a power and its `hpos` field is positivity of the total mass, which holds because the
lag-zero term is `r ^ 0 = 1`.

DERIVED: the `0` is the lower end of the ratio's range, all `geoRead` asks of `r`; `2 * k + 1` is the
period, odd so that the circle has a unique antipode, and `k` is the caller's aperture. -/
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

/-- The read's total mass over the lags is at least one, from the lag-zero term alone.

DERIVED: the `0` is the lower end of the ratio's range and the `1` is the lag-zero term `r ^ 0`. -/
theorem geoRead_sum_ge_one (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) :
    (1 : ℝ) ≤ ∑ d, (geoRead r hr0 k).ρ d := by
  have h := Finset.single_le_sum (f := fun d : Fin (2 * k + 1 + 1) => (geoRead r hr0 k).ρ d)
    (fun i _ => (geoRead r hr0 k).hρ i) (Finset.mem_univ (0 : Fin (2 * k + 1 + 1)))
  rwa [geoRead_rho, circLag_zero, pow_zero] at h

/-- The read's normalised weight at each lag is at most `1 * r ^ circLag d`, because the total mass it
is divided by is at least one (`geoRead_sum_ge_one`). The shape `A * r ^ circLag d` is what
`Moment.circ_moment_le_of_geometric` consumes.

DERIVED: the `0` is the lower end of the ratio's range; the `1` is the amplitude `A` of that geometric
shape, which is one here because the numerator is `r ^ circLag d` itself; `2 * k + 1` is the read's
period and the outer `+ 1` the number of lags. -/
theorem geoRead_p_le (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) (d : Fin (2 * k + 1 + 1)) :
    (geoRead r hr0 k).p d ≤ 1 * r ^ (Moment.circLag d) := by
  have h : (geoRead r hr0 k).p d ≤ (geoRead r hr0 k).ρ d :=
    div_le_self ((geoRead r hr0 k).hρ d) (geoRead_sum_ge_one r hr0 k)
  rw [geoRead_rho] at h
  rwa [one_mul]

/-- The read's second moment in the circle distance is at most `2 * 1 * ∑' m, m² r^m`, a bound with no
`k` in it, so one bound serves every aperture. It is `Moment.circ_moment_le_of_geometric` at the
geometric shape `geoRead_p_le` supplies.

DERIVED: the `0` and `1` are the ends of the ratio's range, `0 ≤ r` and `r < 1`, the second of which
is what makes the series converge; the exponents `2` are the second moment and the `m²` of the
series; `2 * 1` is the circle's two arcs per lag times the amplitude of the geometric shape. -/
theorem geoRead_moment_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ d, (geoRead r hr0 k).p d * (Moment.circLag d : ℝ) ^ 2
      ≤ 2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m :=
  Moment.circ_moment_le_of_geometric (geoRead r hr0 k) zero_le_one hr0 hr1 (geoRead_p_le r hr0 k)

/-- Some aperture makes the geometric read's aperture factor smaller than the entropy floor, and no
value is named for it. The factor `(2π/(N+1))²·B/2` tends to zero at the fixed `B` the moment series
supplies (`Moment.aperture_factor_tendsto_zero`), so the inequality holds eventually along `atTop`,
and an eventual statement has a witness.

DERIVED: the `0` and `1` are the ends of the ratio's range; `2 * π` is the circle's circumference and
the `+ 1` under it is the lag count of period `2 * k + 1`; the exponent `2` and the division by `2`
are the second moment and its halving in the aperture factor; `2 * 1 * ∑' m, m² r^m` is the moment
bound carried in from `geoRead_moment_le`; `1 − 3^{−1/4}` is the entropy floor. -/
theorem exists_aperture (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ k : ℕ, (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2
        * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hev := (Moment.aperture_factor_tendsto_zero (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m))
    |>.eventually_lt_const Moment.floor_rhs_pos
  have htend : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  exact (htend.eventually hev).exists

/-- At an aperture `k` satisfying `exists_aperture`'s inequality, the geometric read's tension is below
the entropy floor `(1/4)·log 3`. It is `Moment.Read.tension_lt_floor_of_circ_moment` fed the moment
bound `geoRead_moment_le` and the hypothesis `hk`.

DERIVED: the `0` and `1` are the ends of the ratio's range; the numerals inside `hk` are
`exists_aperture`'s, quoted unchanged — the `2` of `2 * π`, the `2` of the aperture `2 * k + 1`, the
squaring exponent `2` and the halving `/ 2`, and the `3` and `4` of `3 ^ (-1/4)`; `(1/4)·log 3` is
the entropy floor `κ₀`. -/
theorem geoRead_tension_lt_floor (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ)
    (hk : (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2
        * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (geoRead r hr0 k).tension < (1 / 4) * Real.log 3 :=
  (geoRead r hr0 k).tension_lt_floor_of_circ_moment (geoRead_moment_le r hr0 hr1 k) hk

/-- At the same aperture the read's cosine average is positive, which is
`resolvedDim_le_of_tension`'s `hcos` and `count_le_of_tension_uniform`'s.

DERIVED: the `0` and `1` are the ends of the ratio's range; the numerals inside `hk` are
`exists_aperture`'s, quoted unchanged — the `2` of `2 * π`, the `2` of the aperture `2 * k + 1`, the
squaring exponent `2` and the halving `/ 2`, and the `3` and `4` of `3 ^ (-1/4)`; the `0` in the
conclusion is the sign asserted of the average.
-/
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

One mode carrying weight one, every other carrying zero: a spectrum sorted descending, with one member
above a floor strictly inside `(0,1)`. The rate is shared by every index, so the band hypothesis
`λ₀ ≤ λ i` holds by reflexivity. -/

/-- The mode weights: weight one at index zero, weight zero at every other index.

DERIVED: the `0` is the index carrying the weight and the `1` and the trailing `0` are the two values
the spectrum takes. They are the spectrum itself, not a cut on a measured quantity. -/
noncomputable def wOne : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- The mode rates: the constant function at `r`, so every index carries the same rate.

DERIVED: no numeral. -/
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

/-- The weights sum to one over any nonempty initial range, because index zero lies in the range and
carries all of the weight. This is the `W = 1` that `count_le_of_tension_uniform`'s `hW` consumes.

DERIVED: the `0` is the lower bound on the range's length, the condition that index zero is in it, and
the `1` is the weight that index carries. -/
theorem sum_wOne (m : ℕ) (hm : 0 < m) : ∑ i ∈ Finset.range m, wOne i = 1 := by
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hm)]
  · unfold wOne; rw [if_pos rfl]
  · intro b _ hb; unfold wOne; rw [if_neg hb]

/-- Over a nonempty initial range and at a noise edge strictly between zero and one, exactly one weight
clears the edge: `resolvedDim = 1`. The edge separates the two values `wOne` takes, so the filtered
set is the singleton `{0}`.

DERIVED: the two `0`s are the lower bound on the range's length and the lower bound on the edge, and
the `1`s are the upper bound on the edge and the resulting count. -/
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

/-- The geometric read's correlation equals the spectral sum of the witness spectrum over any nonempty
initial range: `ρ d = ∑_{i < m} wOne i · lamConst r i ^ circLag d`. This is `count_le_of_tension_uniform`'s
hypothesis `hR`, at every range length at once.

DERIVED: the `0`s are the lower bound on the ratio and the lower bound on the range's length;
`2 * k + 1` is the read's period and the outer `+ 1` the number of lags. -/
theorem geoRead_is_sum (r : ℝ) (hr0 : 0 ≤ r) (k : ℕ) (m : ℕ) (hm : 0 < m)
    (d : Fin (2 * k + 1 + 1)) :
    (geoRead r hr0 k).ρ d
      = ∑ i ∈ Finset.range m, wOne i * lamConst r i ^ (Moment.circLag d) := by
  rw [geoRead_rho]
  have : ∀ i : ℕ, wOne i * lamConst r i ^ (Moment.circLag d)
      = wOne i * r ^ (Moment.circLag d) := fun i => rfl
  rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul, sum_wOne m hm, one_mul]

/-! ## The family

The reflected form, the lattice, the group actions and both invariances are `WilsonGauge`'s,
unchanged. What is supplied here is `hcount`, from the tension. -/

/-- The witness read's decay ratio.

CHOSEN: `1/2` is one value of the ratio `r`. Every theorem above is stated at an arbitrary `r` with
`0 ≤ r < 1`, and nothing below depends on which value is taken. -/
noncomputable def rW : ℝ := 1 / 2

theorem rW_nonneg : (0 : ℝ) ≤ rW := by unfold rW; norm_num
theorem rW_lt_one : rW < 1 := by unfold rW; norm_num
theorem rW_pos : (0 : ℝ) < rW := by unfold rW; norm_num

/-- The noise edge the resolved count is taken at.

CHOSEN: `1/2` is one value strictly between the two values `wOne` takes, which is what
`resolvedDim_wOne` asks of the edge; any other such value serves. -/
noncomputable def edgeW : ℝ := 1 / 2

theorem edgeW_pos : (0 : ℝ) < edgeW := by unfold edgeW; norm_num
theorem edgeW_lt_one : edgeW < 1 := by unfold edgeW; norm_num

/-- The read aperture: the witness supplied by `exists_aperture` at the ratio `rW`, through
`Classical.choose`. No value is named for it.

DERIVED: no numeral. -/
noncomputable def kW : ℕ := (exists_aperture rW rW_nonneg rW_lt_one).choose

theorem kW_spec : (2 * Real.pi / (((2 * kW + 1 : ℕ) : ℝ) + 1)) ^ 2
    * (2 * 1 * ∑' m : ℕ, (m : ℝ) ^ 2 * rW ^ m) / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
  (exists_aperture rW rW_nonneg rW_lt_one).choose_spec

/-- The witness read: `geoRead` at the ratio `rW` and the aperture `kW`.

DERIVED: `2 * kW + 1` is `geoRead`'s odd period at the witness aperture, and `kW` comes from
`exists_aperture` rather than from a named value. -/
noncomputable def readW : Moment.Read (2 * kW + 1) := geoRead rW rW_nonneg kW

/-- The witness read's tension is below the entropy floor `(1/4)·log 3`. It is
`geoRead_tension_lt_floor` at `rW` and `kW`, with `kW_spec` discharging the aperture hypothesis.

DERIVED: `(1/4)·log 3` is the entropy floor `κ₀`, the value `Moment.Read.tension_lt_floor_of_circ_moment`
compares against. -/
theorem readW_tension_lt_floor : readW.tension < (1 / 4) * Real.log 3 :=
  geoRead_tension_lt_floor rW rW_nonneg rW_lt_one kW kW_spec

/-- The witness read's cosine average is positive. It is `geoRead_cos_pos` at `rW` and `kW`, and it
discharges `count_le_of_tension_uniform`'s `hcos`.

DERIVED: the `0` is the sign asserted of the average. -/
theorem readW_cos_pos : 0 < ∑ d, readW.p d * Real.cos (readW.θ d) :=
  geoRead_cos_pos rW rW_nonneg rW_lt_one kW kW_spec

/-- The infrared cutoff: `count_le_of_tension_uniform`'s right-hand side evaluated at the witness read,
with `W = 1` from `sum_wOne`, `edge = edgeW` and `lam0 = rW`. It is defined as that bound, so it
asserts nothing on its own about where the resolved modes are.

DERIVED: every numeral is a factor of that right-hand side. `12` is the sum-of-squares denominator
from `ZeroMode.sum_clag_sq`; `1 − 3^{−1/4}` over `8` is the entropy floor composed with
`cos_avg_le_circ`; the standalone `1` in the numerator is the read's total weight; the `1` in
`rW ^ (kW + 1)` is the antipodal lag at aperture `kW`. -/
noncomputable def cW : ℝ :=
  12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * 1 / (edgeW * rW ^ (kW + 1))

theorem cW_pos : 0 < cW := by
  unfold cW
  have h1 : (0 : ℝ) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) * 1 := by
    have := Moment.floor_rhs_pos; linarith
  exact div_pos h1 (mul_pos edgeW_pos (pow_pos rW_pos _))

/-- The `hcount` field, from the tension. At every spacing `a`, the number of `wOne` weights clearing
`edgeW` is at most `cW`. It is `count_le_of_tension_uniform` applied to the witness read, with `wOne`
as the weights, `lamConst rW` as the rates, `rW` as the band floor, `1` as the weight cap and the
tension and cosine hypotheses discharged by `readW_tension_lt_floor` and `readW_cos_pos`. `cW` is that
theorem's own right-hand side at those arguments.

DERIVED: no numeral. -/
theorem hcountW (a : ℕ) :
    ((resolvedDim (Finset.range (NaG a)) ((fun _ => wOne) a) edgeW : ℕ) : ℝ) ≤ cW :=
  count_le_of_tension_uniform (k := kW) (Na := NaG) (w := wOne) (lam := lamConst rW) readW
    (fun a d => geoRead_is_sum rW rW_nonneg kW (NaG a) (by unfold NaG; omega) d)
    wOne_nonneg (fun _ => rW_nonneg) (fun _ => rW_lt_one.le)
    (lam0 := rW) rW_pos rW_lt_one.le (fun _ => le_refl _)
    (edge := edgeW) edgeW_pos
    (W := 1) (fun a => le_of_eq (sum_wOne (NaG a) (by unfold NaG; omega)))
    readW_cos_pos readW_tension_lt_floor a

/-- The `hres` field: at every spacing the resolved count is at least one. It is `resolvedDim_wOne`,
which gives the count exactly.

DERIVED: the `1` is the lower bound asserted on the count. -/
theorem hresW (a : ℕ) : 1 ≤ resolvedDim (Finset.range (NaG a)) ((fun _ => wOne) a) edgeW := by
  rw [resolvedDim_wOne (NaG a) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one]

/-- The `LatticeYMFamily` this module assembles: `WilsonGauge.ymFamilyGaugeCounted` at the constant
weight family `fun _ => wOne`, the noise edge `edgeW` and the cutoff `cW`, with its three obligations
discharged by `wOne_sorted`, `hcountW` and `hresW`.

The reflected form, `os_euc` and `os_perm` come from `ymFamilyGaugeCounted` unchanged. `os_gap` is
built from the sorted spectrum together with the count bound, and that count bound is `hcountW`, which
runs back through `count_le_of_tension_uniform` to `ScreenedGap.resolvedDim_le_of_tension` and the
witness read's tension.

DERIVED: no numeral. -/
noncomputable def ymFamilyTension : LatticeYMFamily :=
  ymFamilyGaugeCounted (fun _ => wOne) edgeW cW wOne_sorted hcountW hresW

#print axioms readW_tension_lt_floor
#print axioms readW_cos_pos
#print axioms hcountW
#print axioms ymFamilyTension

/-- `Measure.continuum_of_family` at `ymFamilyTension`: there is a strictly monotone `φ : ℕ → ℕ` and a
limit `q : J → ℝ` such that `Q j` converges along `φ` to `q j` at every `j`, with `|q j|` bounded by
`⌈c⌉₊ · B`, `q j` nonnegative, and `q` invariant under both `actE` and `actP`.

DERIVED: the `0` is the lower bound asserted on each limit value. -/
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
typecheck. The theorems here record that `ymFamilyTension` is none of those. -/

/-- The family's index type `J` is infinite: `n ↦ (1, 1, n)` injects `ℕ` into it, so `J` contains a
copy of `ℕ`.

DERIVED: no numeral. -/
theorem J_infinite : Infinite ymFamilyTension.J :=
  Infinite.of_injective
    (fun n : ℕ => ((1, 1, n) : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ))
    (fun a b h => by
      have h2 := congrArg
        (fun j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ => j.2.2) h
      simpa using h2)

/-- The family's mode count at spacing `a` exceeds `a`, which with `Na_tendsto` is what makes it grow
without bound. The statement is the strict inequality only; the definition of `NaG` is what the proof
unfolds.

DERIVED: no numeral. -/
theorem Na_ge (a : ℕ) : a < ymFamilyTension.Na a := by
  show a < NaG a
  unfold NaG; omega

theorem Na_tendsto : Filter.Tendsto ymFamilyTension.Na Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => le_trans ha (Na_ge a).le⟩)

/-- The family's resolved count is one at every spacing, so the resolved set is a singleton and in
particular not empty. The statement fixes the count and says nothing about how it compares with the
length of the mode range.

DERIVED: the `1` is the count, carried from `resolvedDim_wOne`. -/
theorem resolvedDim_family (a : ℕ) :
    resolvedDim (Finset.range (ymFamilyTension.Na a)) (ymFamilyTension.ev a)
      ymFamilyTension.edge = 1 :=
  resolvedDim_wOne (NaG a) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one

/-- The family's noise edge is positive: it is `edgeW`.

DERIVED: the `0` is the sign asserted of the edge. -/
theorem family_edge_pos : 0 < ymFamilyTension.edge := edgeW_pos

/-- The family's infrared cutoff is positive: it is `cW`. That the cutoff is also at least the count
it bounds is the separate `one_le_family_c`.

DERIVED: the `0` is the sign asserted of the cutoff. -/
theorem family_c_pos : 0 < ymFamilyTension.c := cW_pos

theorem one_le_family_c : (1 : ℝ) ≤ ymFamilyTension.c := by
  have h := hcountW 0
  rwa [resolvedDim_wOne (NaG 0) (by unfold NaG; omega) edgeW edgeW_pos edgeW_lt_one,
    Nat.cast_one] at h

/-- The family's per-mode bound `B` is one, by definitional unfolding. It is the `B` appearing in the
continuum conclusion `|q j| ≤ ⌈c⌉₊ · B`.

DERIVED: the `1` is the value of `B`. -/
theorem family_B : ymFamilyTension.B = 1 := rfl

/-- The witness read is not constant in the lag: its correlation at the lag-one index differs from its
correlation at the lag-zero index. At `rW = 1/2` the two values are `1/2` and `1`.

DERIVED: the `1` is the lag-one index of `Fin (2 * kW + 1 + 1)` and the `0` is its lag-zero index;
`2 * kW + 1` is the read's period and the outer `+ 1` the number of lags. -/
theorem readW_not_flat :
    readW.ρ (⟨1, by omega⟩ : Fin (2 * kW + 1 + 1)) ≠ readW.ρ (0 : Fin (2 * kW + 1 + 1)) := by
  have h1 : Moment.circLag (⟨1, by omega⟩ : Fin (2 * kW + 1 + 1)) = 1 := by
    show min 1 (2 * kW + 1 + 1 - 1) = 1
    omega
  show (geoRead rW rW_nonneg kW).ρ _ ≠ (geoRead rW rW_nonneg kW).ρ _
  rw [geoRead_rho, geoRead_rho, h1, circLag_zero, pow_zero, pow_one]
  unfold rW
  norm_num

/-- The witness read's tension is nonnegative, by `Moment.Read.tension_nonneg`. The strict inequality
against the floor is the separate `readW_tension_lt_floor`; this statement does not exclude zero.

DERIVED: the `0` is the lower bound asserted on the tension. -/
theorem readW_tension_nonneg : 0 ≤ readW.tension := Moment.Read.tension_nonneg readW

#print axioms J_infinite
#print axioms resolvedDim_family
#print axioms readW_not_flat

/-! ## The model

The measure side above carries no hypothesis. The gap side carries one: `∃ B, ∀ N β, d2At N β ≤ B`,
an aperture-independent bound on the substrate's moment about the circle distance, which every
declaration below takes as an argument. `Complete.confinement_of_bounded_substrate` turns it into
confinement at every large enough aperture, which is `A1_YM (ymModelAt N)` there.

The aperture is not a named value. `confinement_of_bounded_substrate` concludes `∀ᶠ N in atTop`, with
the threshold determined by the existentially supplied `B`, so the model below is built at an aperture
taken from that eventual statement by `Classical.choose` rather than at `Complete.nCorrYM`. Nothing
here relates the two. -/

/-- An aperture at which confinement holds: the witness taken from
`Complete.confinement_of_bounded_substrate`'s eventual statement, given the substrate bound. No value
is named for it.

DERIVED: no numeral. -/
noncomputable def apertureOf (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : ℕ :=
  (confinement_of_bounded_substrate h).exists.choose

theorem apertureOf_confines (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ∀ β : ℝ, μYMAt (apertureOf h) β < κ₀YM :=
  (confinement_of_bounded_substrate h).exists.choose_spec

/-- A1 holds at that aperture. `A1_YM (ymModelAt N)` unfolds to `∀ β, μYMAt N β < κ₀YM`, which is what
`apertureOf_confines` supplies, so the proof is that theorem itself. The coupling is quantified over
all of `ℝ`.

DERIVED: no numeral. -/
theorem A1_at_aperture (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    A1_YM (ymModelAt (apertureOf h)) := apertureOf_confines h

/-- A `FullModel` from the substrate moment bound. Its gap side is `Complete.ymModelAt` at the aperture
`apertureOf h`, with `h1` the A1 obligation discharged by `A1_at_aperture` and `h2` by `ym_A2_at`; its
measure side is `ymFamilyTension`, which carries no hypothesis. The substrate bound `h` is the only
argument.

Scope. `ymModelAt` carries `Idx := Unit` and `m := e^{−(κ₀−μ)}`, so its index set is a single point
and its mode magnitude is defined equal to its own bound.

DERIVED: no numeral. -/
noncomputable def fullModelOfSubstrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : FullModel where
  gap := ymModelAt (apertureOf h)
  h1 := A1_at_aperture h
  h2 := ym_A2_at (apertureOf h)
  measure := ymFamilyTension

#print axioms A1_at_aperture
#print axioms fullModelOfSubstrate

/-- The `WilsonParams` the realisation is built at: the gauge rank `NYM`, box size `L = 1` and
confinement momentum scale `kstar = 2π·cW`. The scale is set from `cW` so that the parameters' own
`irCutoff = kstar·L/(2π)` comes out equal to `cW`, which `paramsTension_irCutoff` proves.

DERIVED: `L = 1` is the unit box; the `2` in `2 * Real.pi * cW` is the `2π` that `irCutoff` divides
back out, so `kstar` is `cW` in momentum units. `NYM` is a named rank carried in, not a numeral here,
and `hN` is discharged by `norm_num` on it. -/
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

/-- A `WilsonRealization` from the substrate moment bound: `paramsTension` as its parameters,
`fullModelOfSubstrate h` as its model, and `paramsTension_irCutoff` discharging the field `hc` that
ties the parameters' infrared cutoff to the measure side's `c`. The gauge rank is whatever
`paramsTension` carries, and the aperture is `Classical.choose`n inside `fullModelOfSubstrate`.

DERIVED: no numeral. -/
noncomputable def wilsonOfSubstrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) : WilsonRealization where
  params := paramsTension
  model := fullModelOfSubstrate h
  hc := paramsTension_irCutoff.symm

/-- `existence_and_gap_of_wilson` at `wilsonOfSubstrate h`. It gives, at every coupling, that the
model's correlator norm tends to zero, that `μ β - κ < 0`, and that the model's read `R` is
direction-independent; together with the continuum conclusions of the measure side.

The only argument is `h : ∃ B, ∀ N β, d2At N β ≤ B`, a bound on the read's circle second moment
holding at every aperture and coupling; no value is supplied for `B` anywhere. The measure side adds
no hypothesis, since its `os_gap` comes from the witness read's tension.

The gap side reads `μYMAt`, which is built from the Wilson ensemble, so the axiom footprint printed
below includes `wilson_reflection_positive_at`, the cited Osterwalder–Seiler reflection positivity.

DERIVED: the `0` in `nhds 0` is the limit of the correlator norm, the `0` in `μ β - κ < 0` is the sign
of the free-energy difference, and the `0` in `0 ≤ q j` is the lower bound on each continuum limit
value. -/
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

/-- `mass_gap_rate_and_continuum` at `fullModelOfSubstrate h` and a coupling `β`. It gives a positive
margin `κ₀ - μ β`, the exponential bound `‖∑ P m^τ‖ ≤ (∑ ‖P‖)·exp(-(κ₀ - μ β))^τ` at every `τ : ℕ`,
and the continuum conclusions of the measure side. The rate in the exponential is the margin itself.

DERIVED: the `0` is the sign asserted of the margin, and the `0` in `0 ≤ q j` is the lower bound on
each continuum limit value. -/
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
