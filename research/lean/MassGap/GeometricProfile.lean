import Mathlib
import MassGap.MomentArms

/-!
# MassGap.GeometricProfile — a geometric profile bounds the far share uniformly in the aperture

`MomentArms.flagship_of_geometric_far_share` consumes a geometric bound on the FAR SHARE. This file
supplies that bound from a geometric bound on the PROFILE, `ρ(d) ≤ M·r^{circLag d}`, the far share
being a sum of the profile over the lags whose circle distance exceeds a cutoff.

The step is a counting fact. `circLag d = min d (N+1−d)` equals `j` only when `d = j` or
`d = N+1−j`, so at most two lags sit at any one circle distance. The far share past `m` is therefore
at most twice a geometric tail, and `2·M·r^{m+1}/(1−r)` bounds it with no `N` in it, which is what
lets the bound survive the aperture limit; a bound by the far set's cardinality would carry an `N+1`
instead.

Sections 2, 3 and 5 take the profile bound back to a spectral hypothesis on the transfer operator —
a finite complex spectrum, the periodic real form with its image term, and a countable spectrum.
Section 4 checks the periodic hypothesis in both directions. Section 6 states the single-cut case,
one number rather than a spectrum, and section 7 identifies what
`ApertureRoute.ConfinesAtAnAperture` is a statement about.
-/

namespace MassGap.GeometricProfile

open Finset

/-- At most two lags share a circle distance: the fibre of `Moment.circLag` over `j` inside
`Fin (N + 1)` has at most two elements. The proof injects the fibre into `{j, N + 1 - j}` by
`Fin.val`.

DERIVED: `2` counts the two ways round the circle — `min d (N + 1 - d) = j` forces `d = j` or
`d = N + 1 - j`. The `1` is the `N + 1` of the lag index type, the number of lags a `Moment.Read N`
carries. Neither is chosen. -/
theorem card_circLag_fiber_le_two (N j : ℕ) :
    ((univ : Finset (Fin (N + 1))).filter (fun d => Moment.circLag d = j)).card ≤ 2 := by
  classical
  have hsub : ((univ : Finset (Fin (N + 1))).filter (fun d => Moment.circLag d = j)).card
      ≤ ({j, N + 1 - j} : Finset ℕ).card := by
    refine Finset.card_le_card_of_injOn (fun d => (d : ℕ)) (fun d hd => ?_) ?_
    · have hj : Moment.circLag d = j := (Finset.mem_filter.mp hd).2
      unfold Moment.circLag at hj
      have hlt : (d : ℕ) < N + 1 := d.isLt
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff]
      rcases min_cases (d : ℕ) (N + 1 - (d : ℕ)) with ⟨he, _⟩ | ⟨he, _⟩
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · intro a _ b _ hab
      exact Fin.val_injective hab
  exact le_trans hsub (Finset.card_insert_le _ _ |>.trans (by simp))

#print axioms card_circLag_fiber_le_two

/-- A geometric tail in closed form: `∑ j ∈ Finset.Ico a K, r ^ j ≤ r ^ a / (1 - r)`, for any
`a` and `K`. No relation between `a` and `K` is required; the empty range is covered.

DERIVED: `0 ≤ r` and `r < 1` are the geometric series' own range, and the `1` of `1 - r` is its
denominator. Nothing is chosen. -/
theorem geom_Ico_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a K : ℕ) :
    ∑ j ∈ Finset.Ico a K, r ^ j ≤ r ^ a / (1 - r) := by
  have hden : 0 < 1 - r := by linarith
  have hrange : ∑ i ∈ Finset.range (K - a), r ^ i ≤ 1 / (1 - r) := by
    rw [geom_sum_eq (by linarith : r ≠ 1)]
    have heq : (r ^ (K - a) - 1) / (r - 1) = (1 - r ^ (K - a)) / (1 - r) := by
      rw [div_eq_div_iff (by linarith : r - 1 ≠ 0) (by linarith : (1 : ℝ) - r ≠ 0)]
      ring
    rw [heq, div_le_div_iff₀ hden hden]
    nlinarith [pow_nonneg hr0 (K - a)]
  calc ∑ j ∈ Finset.Ico a K, r ^ j
      = ∑ i ∈ Finset.range (K - a), r ^ (a + i) := by
        rw [Finset.sum_Ico_eq_sum_range]
    _ = r ^ a * ∑ i ∈ Finset.range (K - a), r ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [pow_add])
    _ ≤ r ^ a * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hrange (pow_nonneg hr0 a)
    _ = r ^ a / (1 - r) := by ring

#print axioms geom_Ico_le

/-- A geometric profile has a geometric far share, with no aperture in the constant.

`R.p d ≤ M * r ^ (Moment.circLag d)` at every lag gives
`ContactDominance.farShare R m ≤ (2 * M / (1 - r)) * r ^ (m + 1)`. The constant depends on `M` and
`r` only; the extent `N` does not appear in it.

The proof groups the far set `ContactDominance.farSet N m` by circle distance, bounds each fibre
with `card_circLag_fiber_le_two`, and sums the geometric tail with `geom_Ico_le`.

DERIVED: `2` is the fibre bound of `card_circLag_fiber_le_two`, the two ways round the circle.
`1 - r` is the geometric denominator from `geom_Ico_le`, and `0 ≤ M`, `0 ≤ r`, `r < 1` are the range
those two lemmas need. The `m + 1` is the first circle distance past the cutoff `m`. -/
theorem farShare_le_of_geometric_profile {N : ℕ} (R : Moment.Read N) {M r : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ d : Fin (N + 1), R.p d ≤ M * r ^ (Moment.circLag d)) (m : ℕ) :
    MassGap.ContactDominance.farShare R m ≤ (2 * M / (1 - r)) * r ^ (m + 1) := by
  classical
  have hden : 0 < 1 - r := by linarith
  -- every far lag lands in `[m+1, N+2)`
  have hmaps : ∀ d ∈ MassGap.ContactDominance.farSet N m,
      Moment.circLag d ∈ Finset.Ico (m + 1) (N + 2) := by
    intro d hd
    have hgt : m < Moment.circLag d := (Finset.mem_filter.mp hd).2
    have hle : Moment.circLag d ≤ (d : ℕ) := min_le_left _ _
    have hlt : (d : ℕ) < N + 1 := d.isLt
    exact Finset.mem_Ico.mpr ⟨hgt, by omega⟩
  -- bound the profile, then group by circle distance
  have hstep : MassGap.ContactDominance.farShare R m
      ≤ ∑ d ∈ MassGap.ContactDominance.farSet N m, M * r ^ (Moment.circLag d) :=
    Finset.sum_le_sum (fun d _ => hprof d)
  have hfib : ∑ d ∈ MassGap.ContactDominance.farSet N m, M * r ^ (Moment.circLag d)
      = ∑ j ∈ Finset.Ico (m + 1) (N + 2),
          ∑ d ∈ (MassGap.ContactDominance.farSet N m).filter (fun d => Moment.circLag d = j),
            M * r ^ (Moment.circLag d) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hinner : ∀ j ∈ Finset.Ico (m + 1) (N + 2),
      ∑ d ∈ (MassGap.ContactDominance.farSet N m).filter (fun d => Moment.circLag d = j),
        M * r ^ (Moment.circLag d) ≤ 2 * (M * r ^ j) := by
    intro j _
    have hconst : ∀ d ∈ (MassGap.ContactDominance.farSet N m).filter
        (fun d => Moment.circLag d = j), M * r ^ (Moment.circLag d) = M * r ^ j := by
      intro d hd
      rw [(Finset.mem_filter.mp hd).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((MassGap.ContactDominance.farSet N m).filter
        (fun d => Moment.circLag d = j)).card : ℝ) ≤ 2 := by
      have h := card_circLag_fiber_le_two N j
      have hsub : ((MassGap.ContactDominance.farSet N m).filter
          (fun d => Moment.circLag d = j)).card
          ≤ ((univ : Finset (Fin (N + 1))).filter (fun d => Moment.circLag d = j)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      exact_mod_cast le_trans hsub h
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hM (pow_nonneg hr0 j))
  calc MassGap.ContactDominance.farShare R m
      ≤ ∑ d ∈ MassGap.ContactDominance.farSet N m, M * r ^ (Moment.circLag d) := hstep
    _ = _ := hfib
    _ ≤ ∑ j ∈ Finset.Ico (m + 1) (N + 2), 2 * (M * r ^ j) := Finset.sum_le_sum hinner
    _ = 2 * M * ∑ j ∈ Finset.Ico (m + 1) (N + 2), r ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 2 * M * (r ^ (m + 1) / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_Ico_le hr0 hr1 _ _) (by positivity)
    _ = (2 * M / (1 - r)) * r ^ (m + 1) := by ring

#print axioms farShare_le_of_geometric_profile

/-- Confinement at an aperture, from a geometric profile.

If at every even aperture past `N₀` and every coupling `β` the profile of
`EvenAperture.readEven` obeys `p d ≤ M * r ^ (Moment.circLag d)`, then
`ApertureRoute.ConfinesAtAnAperture` holds. The envelope handed to
`MomentArms.confines_of_geometric_far_share` is `(2 * M * r / (1 - r)) * r ^ m`, which is
`farShare_le_of_geometric_profile`'s bound with `r ^ (m + 1)` split; no aperture appears in it.

Stated for even apertures: the hypothesis quantifies over `EvenAperture.EvenAp`, a natural number
with a parity proof, not over `ℕ`. `M` and `r` are bound outside that quantifier and outside the
quantifier over `β`.

DERIVED: `0 ≤ M`, `0 ≤ r` and `r < 1` are the range `farShare_le_of_geometric_profile` needs; the
`+ 1` of `Fin (p.1 + 1)` is the lag count of the read at aperture `p`. The cutoff passed downward
is `m₀ := 0`, so the envelope is asserted at every `m`. -/
theorem confines_of_geometric_profile {N₀ : ℕ} {M r : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ M * r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine MassGap.MomentArms.confines_of_geometric_far_share (N₀ := N₀) (m₀ := 0)
    (C := 2 * M * r / (1 - r)) (r := r) (by positivity) hr0 hr1 ?_
  intro p hp β m _
  have h := farShare_le_of_geometric_profile (MassGap.EvenAperture.readEven p β) hM hr0 hr1
    (hprof p hp β) m
  calc MassGap.ContactDominance.farShare (MassGap.EvenAperture.readEven p β) m
      ≤ (2 * M / (1 - r)) * r ^ (m + 1) := h
    _ = 2 * M * r / (1 - r) * r ^ m := by
        rw [pow_succ]
        ring

#print axioms confines_of_geometric_profile

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_geometric_profile`, under the same
hypotheses. The proof is `ApertureRoute.flagship_of_confinement_at_an_aperture`; the hypotheses are
discharged in `confines_of_geometric_profile`.

DERIVED: `0 ≤ M`, `0 ≤ r`, `r < 1` and the `+ 1` of `Fin (p.1 + 1)` are
`confines_of_geometric_profile`'s, carried unchanged. -/
theorem flagship_of_geometric_profile {N₀ : ℕ} {M r : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ M * r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_geometric_profile hM hr0 hr1 hprof) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_geometric_profile


/-! ## 2. A spectral representation with a margin

§1 takes a geometric profile to a geometric far share. This section supplies the profile bound from
a spectral hypothesis: that the profile is a finite exponential sum in the circle distance,

    ρ(d) = ∑ₖ Pₖ · μₖ^{circLag d},

which is the transfer-matrix spectral decomposition on a periodic extent. Given that,
`Aperture.finite_sum_margin_bound` evaluated at `circLag d` bounds the sum by the total weight times
`r^{circLag d}` whenever every mode satisfies `‖μₖ‖ ≤ r`.

`circLag` rather than the raw index is what makes the statement one about the circle;
`MomentShape.wilsonCorrAt_circLag_congr` proves the Wilson correlation reads the lag only through
`circLag`.

The operator such a representation would come from is `SliceTransferSelfAdjoint.transferCLM`, which
is positive (`TransferGaussian.transferKernel_posDef`) and injective
(`TransferGaussian.transferCLM_injective`). The representation and the margin enter the theorems
below as the hypotheses `hrep` and `hmargin`.
-/

/-- A represented profile with a margin is geometric in the circle distance.

If `((R.p d : ℝ) : ℂ) = ∑ k ∈ s, P k * μ k ^ (Moment.circLag d)` and `‖μ k‖ ≤ r` on `s`, then
`R.p d ≤ (∑ k ∈ s, ‖P k‖) * r ^ (Moment.circLag d)`. The profile is nonnegative (`Moment.Read`'s
`p_nonneg`), so it equals its own norm and `Aperture.finite_sum_margin_bound` applies directly. The
index type `ι` is arbitrary; `s` is a `Finset`, so the mode set is finite here, and the modes may be
complex.

DERIVED: the only numeral in the statement is the `1` of `Fin (N + 1)`, the lag count of a
`Moment.Read N`. The constant `∑ k ∈ s, ‖P k‖` is the representation's own total weight, not a
chosen bound. -/
theorem profile_geometric_of_margin {N : ℕ} (R : Moment.Read N) {ι : Type*} (s : Finset ι)
    (P μ : ι → ℂ) {r : ℝ} (hr : ∀ k ∈ s, ‖μ k‖ ≤ r)
    (hrep : ∀ d : Fin (N + 1), ((R.p d : ℝ) : ℂ) = ∑ k ∈ s, P k * (μ k) ^ (Moment.circLag d))
    (d : Fin (N + 1)) :
    R.p d ≤ (∑ k ∈ s, ‖P k‖) * r ^ (Moment.circLag d) := by
  have hself : R.p d = ‖((R.p d : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (R.p_nonneg d)]
  rw [hself, hrep d]
  exact MassGap.finite_sum_margin_bound s P μ r hr (Moment.circLag d)

#print axioms profile_geometric_of_margin

/-- Confinement at an aperture, from a finite spectral representation with a margin.

At every even aperture past `N₀` and every coupling `β`: `s p β` is a finite mode set, `hrep` writes
the profile of `EvenAperture.readEven` as `∑ k ∈ s p β, P p β k * μ p β k ^ (Moment.circLag d)`,
`hmargin` bounds every `‖μ p β k‖` by `r`, and `hweight` bounds the total weight by `M`. The
conclusion is `ApertureRoute.ConfinesAtAnAperture`, via `profile_geometric_of_margin` and
`confines_of_geometric_profile`.

`M` and `r` are bound outside the quantifiers over apertures and couplings, so the weight cap and
the margin are uniform in both. `hrep` and `hmargin` are hypotheses of the statement.

DERIVED: `0 ≤ M`, `0 ≤ r` and `r < 1` are `confines_of_geometric_profile`'s range; the `+ 1` of
`Fin (p.1 + 1)` is the lag count at aperture `p`. -/
theorem confines_of_spectral_representation {N₀ : ℕ} {ι : Type*} {r : ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), Finset ι)
    (P μ : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℂ)
    (hmargin : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      ∀ k ∈ s p β, ‖μ p β k‖ ≤ r)
    (hweight : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      ∑ k ∈ s p β, ‖P p β k‖ ≤ M)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (((MassGap.EvenAperture.readEven p β).p d : ℝ) : ℂ)
        = ∑ k ∈ s p β, P p β k * (μ p β k) ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_geometric_profile (N₀ := N₀) hM hr0 hr1 ?_
  intro p hp β d
  refine le_trans (profile_geometric_of_margin (MassGap.EvenAperture.readEven p β) (s p β)
    (P p β) (μ p β) (hmargin p hp β) (hrep p hp β) d) ?_
  exact mul_le_mul_of_nonneg_right (hweight p hp β) (pow_nonneg hr0 _)

#print axioms confines_of_spectral_representation

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_spectral_representation`, under the same
hypotheses.

DERIVED: `0 ≤ M`, `0 ≤ r`, `r < 1` and the `+ 1` of `Fin (p.1 + 1)` are carried unchanged from
`confines_of_spectral_representation`. -/
theorem flagship_of_spectral_representation {N₀ : ℕ} {ι : Type*} {r : ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), Finset ι)
    (P μ : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℂ)
    (hmargin : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      ∀ k ∈ s p β, ‖μ p β k‖ ≤ r)
    (hweight : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      ∑ k ∈ s p β, ‖P p β k‖ ≤ M)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (((MassGap.EvenAperture.readEven p β).p d : ℝ) : ℂ)
        = ∑ k ∈ s p β, P p β k * (μ p β k) ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.FlagshipAt
      (confines_of_spectral_representation hM hr0 hr1 s P μ hmargin hweight hrep) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_spectral_representation


/-! ## 3. The periodic form

§2's hypothesis writes the profile as a function of the circle distance already. On a periodic
extent the transfer-matrix spectral form is

    ρ(d) = ∑ₙ wₙ e^{−Eₙ d},   wₙ ≥ 0

— the form `Complete.wilson_reflection_positive_at`'s docstring cites — and closing it into a ring
adds an image term:

    ρ(d) = ∑ₙ wₙ (mₙ^{d} + mₙ^{N+1−d}),   mₙ = e^{−Eₙ}.

Written as an exponential in `d` alone the image term has base `mₙ^{-1}`, outside the unit disc, so
§2's hypothesis does not cover it. `circLag d = min d (N+1−d)` is at most both exponents, and
`0 ≤ m ≤ 1` gives `m^a ≤ m^{circLag d}` for either, so each mode contributes at most
`2·m^{circLag d}` and the profile is geometric in the circle distance with `M = 2∑ₙwₙ`:

    ρ(d) ≤ (2∑ₙ wₙ) · r^{circLag d}.

The image term costs a factor of two. Everything in this section is real and nonnegative: real
modes, no complex weights, no cancellation, and `wₙ ≥ 0` is what reflection positivity supplies.
-/

/-- The image term is bounded by the direct term. For `0 ≤ m ≤ 1`,
`m ^ d + m ^ (N + 1 - d) ≤ 2 * m ^ (Moment.circLag d)`, because `Moment.circLag d` is at most both
`d` and `N + 1 - d` and `m ^ ·` is antitone in the exponent on that range.

DERIVED: `2` is the two terms, direct and image. `0 ≤ m` and `m ≤ 1` are the range that makes
`pow_le_pow_of_le_one` apply; the `1` of `N + 1 - d` is the periodic extent's own arithmetic. -/
theorem periodic_pair_le {N : ℕ} (d : Fin (N + 1)) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    m ^ ((d : ℕ)) + m ^ (N + 1 - (d : ℕ)) ≤ 2 * m ^ (Moment.circLag d) := by
  have hdir : m ^ ((d : ℕ)) ≤ m ^ (Moment.circLag d) :=
    pow_le_pow_of_le_one hm0 hm1 (min_le_left _ _)
  have himg : m ^ (N + 1 - (d : ℕ)) ≤ m ^ (Moment.circLag d) :=
    pow_le_pow_of_le_one hm0 hm1 (min_le_right _ _)
  linarith

#print axioms periodic_pair_le

/-- The periodic spectral form is geometric in the circle distance.

`R.p d = ∑ k ∈ s, w k * (m k ^ d + m k ^ (N + 1 - d))` with `0 ≤ w k`, `0 ≤ m k` and `m k ≤ r < 1`
gives `R.p d ≤ (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d)`. Each summand is handled by
`periodic_pair_le` and then by monotonicity of `· ^ (Moment.circLag d)` in the base. The index type
`ι` is arbitrary and `s` is a `Finset`; weights and modes are real.

DERIVED: `2` is `periodic_pair_le`'s factor, the direct and image terms. `0 ≤ w k`, `0 ≤ m k` and
`r < 1` are the range those two steps need, and the `1` of `N + 1 - d` is the periodic
arithmetic. -/
theorem profile_geometric_of_periodic_spectral {N : ℕ} (R : Moment.Read N) {ι : Type*}
    (s : Finset ι) (w m : ι → ℝ) {r : ℝ} (hr1 : r < 1)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hm0 : ∀ k ∈ s, 0 ≤ m k) (hmr : ∀ k ∈ s, m k ≤ r)
    (hrep : ∀ d : Fin (N + 1), R.p d
      = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))
    (d : Fin (N + 1)) :
    R.p d ≤ (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d) := by
  have hstep : ∀ k ∈ s,
      w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ)))
        ≤ w k * (2 * r ^ (Moment.circLag d)) := by
    intro k hk
    have hm1 : m k ≤ 1 := le_trans (hmr k hk) (le_of_lt hr1)
    have hpair := periodic_pair_le d (hm0 k hk) hm1
    have hmono : m k ^ (Moment.circLag d) ≤ r ^ (Moment.circLag d) :=
      pow_le_pow_left₀ (hm0 k hk) (hmr k hk) _
    refine mul_le_mul_of_nonneg_left ?_ (hw k hk)
    linarith
  calc R.p d = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))) := hrep d
    _ ≤ ∑ k ∈ s, w k * (2 * r ^ (Moment.circLag d)) := Finset.sum_le_sum hstep
    _ = (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d) := by
        rw [← Finset.sum_mul]
        ring

#print axioms profile_geometric_of_periodic_spectral

/-- Confinement at an aperture, from the periodic spectral form.

The hypotheses are the shape a real transfer spectrum on a ring supplies: nonnegative weights `hw`,
nonnegative modes `hm0` bounded by `r` in `hmr`, a cap `htot` on `2 * ∑ k ∈ s p β, w p β k` by `W`,
and `hrep` writing the profile of `EvenAperture.readEven` with its image term. The conclusion is
`ApertureRoute.ConfinesAtAnAperture`, via `profile_geometric_of_periodic_spectral`.

`W` and `r` are bound outside the quantifiers over apertures and couplings. `hrep` and `hmr` are
hypotheses of the statement.

DERIVED: `2` is the direct-and-image factor, already inside `htot`; `0 ≤ W`, `0 ≤ r` and `r < 1`
are the range; the `+ 1` in `p.1 + 1 - d` is the periodic extent at aperture `p`. -/
theorem confines_of_periodic_spectral {N₀ : ℕ} {ι : Type*} {r W : ℝ}
    (hW : 0 ≤ W) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), Finset ι)
    (w m : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℝ)
    (hw : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, 0 ≤ w p β k)
    (hm0 : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, 0 ≤ m p β k)
    (hmr : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, m p β k ≤ r)
    (htot : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      2 * ∑ k ∈ s p β, w p β k ≤ W)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d
        = ∑ k ∈ s p β, w p β k
            * ((m p β k) ^ ((d : ℕ)) + (m p β k) ^ (p.1 + 1 - (d : ℕ)))) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_geometric_profile (N₀ := N₀) hW hr0 hr1 ?_
  intro p hp β d
  refine le_trans (profile_geometric_of_periodic_spectral (MassGap.EvenAperture.readEven p β)
    (s p β) (w p β) (m p β) hr1 (hw p hp β) (hm0 p hp β) (hmr p hp β) (hrep p hp β) d) ?_
  exact mul_le_mul_of_nonneg_right (htot p hp β) (pow_nonneg hr0 _)

#print axioms confines_of_periodic_spectral

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_periodic_spectral`, under the same
hypotheses.

DERIVED: the `2` of `htot`, the `0 ≤ W`, `0 ≤ r`, `r < 1` range, and the `+ 1` of `p.1 + 1 - d` are
`confines_of_periodic_spectral`'s, carried unchanged. -/
theorem flagship_of_periodic_spectral {N₀ : ℕ} {ι : Type*} {r W : ℝ}
    (hW : 0 ≤ W) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), Finset ι)
    (w m : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℝ)
    (hw : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, 0 ≤ w p β k)
    (hm0 : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, 0 ≤ m p β k)
    (hmr : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), ∀ k ∈ s p β, m p β k ≤ r)
    (htot : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      2 * ∑ k ∈ s p β, w p β k ≤ W)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d
        = ∑ k ∈ s p β, w p β k
            * ((m p β k) ^ ((d : ℕ)) + (m p β k) ^ (p.1 + 1 - (d : ℕ)))) :
    MassGap.ApertureRoute.FlagshipAt
      (confines_of_periodic_spectral hW hr0 hr1 s w m hw hm0 hmr htot hrep) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_periodic_spectral


/-! ## 4. The periodic hypothesis is satisfiable, and it excludes a flat profile

§3's `hrep` is checked in both directions here.

A single mode gives a `Moment.Read` whose profile is exactly the periodic spectral form,
`ρ(d) = r^d + r^{N+1−d}`, nonnegative with positive total, so `readA` accepts it and the
normalisation is the weight.

In the other direction §3 bounds `p d` by `W·r^{circLag d}` at every lag, so at the antipode — where
`circLag` is largest — the profile is exponentially small in the extent. A flat profile has
`p d = 1/(N+1)` everywhere, which is polynomially small, so at large extent it does not admit the
periodic spectral form. That is the profile `FlatProfileAllApertures` carries; it fails the
hypothesis rather than the conclusion.
-/

/-- A single-mode periodic profile on `Fin (N + 1)`: `r ^ d + r ^ (N + 1 - d)`, the direct term and
its image round the ring.

DERIVED: the `1` is the `N + 1` of the periodic extent the lag index runs over, so `N + 1 - d` is
the same separation measured the other way round the circle — `Moment.circLag`'s own arithmetic,
carried unchanged. It is an index, not a magnitude. -/
noncomputable def singleModeProfile (N : ℕ) (r : ℝ) (d : Fin (N + 1)) : ℝ :=
  r ^ ((d : ℕ)) + r ^ (N + 1 - (d : ℕ))

#print axioms singleModeProfile

/-- `singleModeProfile N r` is nonnegative and has a positive total, which is what `readA` requires.
The positivity comes from lag zero, where the direct term is `r ^ 0 = 1` and the image term is
nonnegative.

DERIVED: `0 ≤ r` is the only hypothesis, and the `0` of the conclusion's
`0 < ∑ d, singleModeProfile N r d` is positivity of the total. -/
theorem singleModeProfile_valid (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    (∀ d, 0 ≤ singleModeProfile N r d) ∧ 0 < ∑ d, singleModeProfile N r d := by
  have hnn : ∀ d : Fin (N + 1), 0 ≤ singleModeProfile N r d := by
    intro d
    unfold singleModeProfile
    positivity
  refine ⟨hnn, ?_⟩
  have hzero : 0 < singleModeProfile N r (0 : Fin (N + 1)) := by
    unfold singleModeProfile
    have : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
    rw [this, pow_zero]
    have : (0 : ℝ) ≤ r ^ (N + 1 - 0) := pow_nonneg hr0 _
    linarith
  exact lt_of_lt_of_le hzero
    (Finset.single_le_sum (fun d _ => hnn d) (Finset.mem_univ (0 : Fin (N + 1))))

#print axioms singleModeProfile_valid

/-- §3's representation hypothesis is satisfiable. For `0 ≤ r` there is a `Moment.Read N` and a
weight `0 ≤ w` with `R.p d = w * (r ^ d + r ^ (N + 1 - d))` at every lag. The witness is
`readA (singleModeProfile N r)`, with `w` the reciprocal of that profile's total — one mode, and the
normalisation as its weight.

DERIVED: `0 ≤ r` and `0 ≤ w` are the nonnegativity the witness carries; the `1` of `N + 1 - d` is
the periodic extent, matching `singleModeProfile`. -/
theorem periodic_spectral_is_satisfiable (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    ∃ (R : Moment.Read N) (w : ℝ), 0 ≤ w ∧
      ∀ d : Fin (N + 1), R.p d = w * (r ^ ((d : ℕ)) + r ^ (N + 1 - (d : ℕ))) := by
  obtain ⟨hnn, hpos⟩ := singleModeProfile_valid N hr0
  refine ⟨MassGap.readA (singleModeProfile N r) ⟨hnn, hpos⟩,
    (∑ d, singleModeProfile N r d)⁻¹, by positivity, fun d => ?_⟩
  show singleModeProfile N r d / (∑ d, singleModeProfile N r d)
      = (∑ d, singleModeProfile N r d)⁻¹ * (r ^ ((d : ℕ)) + r ^ (N + 1 - (d : ℕ)))
  unfold singleModeProfile
  rw [div_eq_inv_mul]

#print axioms periodic_spectral_is_satisfiable

/-- §3's conclusion restated at an arbitrary lag: a profile admitting the periodic spectral form
satisfies `R.p d ≤ (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d)`, so at the largest circle distance
it is exponentially small in the extent. The statement is `profile_geometric_of_periodic_spectral`'s
and the proof applies that theorem directly.

A flat profile is `1/(N+1)` at every lag, which is polynomially small, so at large extent it fails
the hypothesis. That is the profile `FlatProfileAllApertures` carries.

DERIVED: `2` is the direct-and-image factor of `periodic_pair_le`; `0 ≤ w k`, `0 ≤ m k` and `r < 1`
are the range; the `1` of `N + 1 - d` is the periodic extent. -/
theorem periodic_spectral_forces_antipodal_decay {N : ℕ} (R : Moment.Read N) {ι : Type*}
    (s : Finset ι) (w m : ι → ℝ) {r : ℝ} (hr1 : r < 1)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hm0 : ∀ k ∈ s, 0 ≤ m k) (hmr : ∀ k ∈ s, m k ≤ r)
    (hrep : ∀ d : Fin (N + 1), R.p d
      = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))
    (d : Fin (N + 1)) :
    R.p d ≤ (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d) :=
  profile_geometric_of_periodic_spectral R s w m hr1 hw hm0 hmr hrep d

#print axioms periodic_spectral_forces_antipodal_decay


/-! ## 5. A countable spectrum

§2 and §3 both write the spectral sum over a `Finset`.
`SliceTransferSelfAdjoint.transferCLM` is an integral operator with a bounded continuous kernel on a
compact configuration space against a finite measure, hence Hilbert–Schmidt and compact; the
spectrum of a compact operator on an infinite-dimensional space is a countable sequence accumulating
only at zero. `L²(sliceHaar)` is infinite-dimensional because the coordinate monomials are
infinitely many independent functions — `TransferGaussian.coordAlgebra_dense_in_L2` is about that
algebra.

This section restates §3 with `∑'` in place of `∑`. The one added hypothesis is `Summable w`, and
`Summable.tsum_le_tsum` replaces `Finset.sum_le_sum`. The conclusion is unchanged:

    ρ(d) ≤ (2 ∑' w) · r^{circLag d}.

§3 is kept: on a finite mode set it is the same statement without the summability side condition.
-/

/-- The countable periodic spectral form is geometric in the circle distance.

§3 with `∑'` in place of `∑`: `R.p d = ∑' k, w k * (m k ^ d + m k ^ (N + 1 - d))` with `0 ≤ w k`,
`0 ≤ m k`, `m k ≤ r < 1` and `Summable w` gives
`R.p d ≤ (2 * ∑' k, w k) * r ^ (Moment.circLag d)`. The mode index `ι` ranges over a whole type
rather than a `Finset`; summability is what makes the tsum comparison legal.

DERIVED: `2` is `periodic_pair_le`'s direct-and-image factor. `0 ≤ r`, `0 ≤ w k`, `0 ≤ m k` and
`r < 1` are the range; the `1` of `N + 1 - d` is the periodic extent. -/
theorem profile_geometric_of_countable_spectral {N : ℕ} (R : Moment.Read N) {ι : Type*}
    (w m : ι → ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hw : ∀ k, 0 ≤ w k) (hm0 : ∀ k, 0 ≤ m k) (hmr : ∀ k, m k ≤ r)
    (hsum : Summable w)
    (hrep : ∀ d : Fin (N + 1), R.p d
      = ∑' k, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))
    (d : Fin (N + 1)) :
    R.p d ≤ (2 * ∑' k, w k) * r ^ (Moment.circLag d) := by
  have hle : ∀ k, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ)))
      ≤ w k * (2 * r ^ (Moment.circLag d)) := by
    intro k
    have hm1 : m k ≤ 1 := le_trans (hmr k) (le_of_lt hr1)
    have hpair := periodic_pair_le d (hm0 k) hm1
    have hmono : m k ^ (Moment.circLag d) ≤ r ^ (Moment.circLag d) :=
      pow_le_pow_left₀ (hm0 k) (hmr k) _
    refine mul_le_mul_of_nonneg_left ?_ (hw k)
    linarith
  have hg : Summable (fun k => w k * (2 * r ^ (Moment.circLag d))) := hsum.mul_right _
  have hf : Summable (fun k => w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ)))) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) hle hg
    have h1 : (0 : ℝ) ≤ (m k) ^ ((d : ℕ)) := pow_nonneg (hm0 k) _
    have h2 : (0 : ℝ) ≤ (m k) ^ (N + 1 - (d : ℕ)) := pow_nonneg (hm0 k) _
    exact mul_nonneg (hw k) (by linarith)
  calc R.p d = ∑' k, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))) := hrep d
    _ ≤ ∑' k, w k * (2 * r ^ (Moment.circLag d)) := Summable.tsum_le_tsum hle hf hg
    _ = (2 * ∑' k, w k) * r ^ (Moment.circLag d) := by
        rw [tsum_mul_right]
        ring

#print axioms profile_geometric_of_countable_spectral

/-- Confinement at an aperture, from a countable periodic spectrum.

`confines_of_periodic_spectral`'s hypotheses with the mode `Finset` removed and `Summable (w p β)`
added, so `hw`, `hm0` and `hmr` quantify over all of `ι`. The conclusion is
`ApertureRoute.ConfinesAtAnAperture`, via `profile_geometric_of_countable_spectral`.

DERIVED: the `2` of `htot` is the direct-and-image factor; `0 ≤ W`, `0 ≤ r` and `r < 1` are the
range; the `+ 1` in `p.1 + 1 - d` is the periodic extent at aperture `p`. -/
theorem confines_of_countable_spectral {N₀ : ℕ} {ι : Type*} {r W : ℝ}
    (hW : 0 ≤ W) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (w m : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℝ)
    (hw : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), 0 ≤ w p β k)
    (hm0 : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), 0 ≤ m p β k)
    (hmr : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), m p β k ≤ r)
    (hsum : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), Summable (w p β))
    (htot : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      2 * ∑' k, w p β k ≤ W)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d
        = ∑' k, w p β k
            * ((m p β k) ^ ((d : ℕ)) + (m p β k) ^ (p.1 + 1 - (d : ℕ)))) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_geometric_profile (N₀ := N₀) hW hr0 hr1 ?_
  intro p hp β d
  refine le_trans (profile_geometric_of_countable_spectral (MassGap.EvenAperture.readEven p β)
    (w p β) (m p β) hr0 hr1 (hw p hp β) (hm0 p hp β) (hmr p hp β) (hsum p hp β)
    (hrep p hp β) d) ?_
  exact mul_le_mul_of_nonneg_right (htot p hp β) (pow_nonneg hr0 _)

#print axioms confines_of_countable_spectral

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_countable_spectral`, under the same
hypotheses. Two of them are about the transfer operator's spectrum rather than about any estimate of
the correlation:

* `hrep` with `hsum` — a convergent periodic spectral decomposition with nonnegative weights, of the
  kind `SliceTransferSelfAdjoint.transferCLM` would supply;
* `hmr` — the modes share a margin `r < 1`.

Both are hypotheses of the statement. The rest are the range conditions and the weight cap `htot`.

DERIVED: the `2` of `htot`; `0 ≤ W`, `0 ≤ r` and `r < 1`; and the `+ 1` of `p.1 + 1 - d`, all
carried from `confines_of_countable_spectral`. -/
theorem flagship_of_countable_spectral {N₀ : ℕ} {ι : Type*} {r W : ℝ}
    (hW : 0 ≤ W) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (w m : ∀ (p : MassGap.EvenAperture.EvenAp) (β : ℝ), ι → ℝ)
    (hw : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), 0 ≤ w p β k)
    (hm0 : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), 0 ≤ m p β k)
    (hmr : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (k : ι), m p β k ≤ r)
    (hsum : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ), Summable (w p β))
    (htot : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ),
      2 * ∑' k, w p β k ≤ W)
    (hrep : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d
        = ∑' k, w p β k
            * ((m p β k) ^ ((d : ℕ)) + (m p β k) ^ (p.1 + 1 - (d : ℕ)))) :
    MassGap.ApertureRoute.FlagshipAt
      (confines_of_countable_spectral hW hr0 hr1 w m hw hm0 hmr hsum htot hrep) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_countable_spectral


/-! ## 6. The single-cut form

`PAPER.md`'s abstract states the structure this section formalises: reflection positivity makes the
transfer operator self-adjoint, giving `ρ'(n) = ρ'(1)^n`, so a single-cut magnitude `ρ'(1) < 1`
carries the gap uniformly in volume. That is one number rather than a spectrum.

`Mixing.gap_of_maximal_correlation` carries the single-cut statement at a different endpoint: it
takes `σ n ≤ σ 0 · ρ₁^n` with `ρ₁ < 1`, concludes `σ → 0`, and lands on `ReachFreeze`'s excess. The
theorems below state the single-cut case at this file's endpoint, `d2Even` and thence
`ApertureRoute.FlagshipAt`.

§2 to §5 quantify over a mode set; the theorems below take one number instead, so each extra mode of
the general form is an extra hypothesis a caller supplies.
-/

/-- The single-cut profile bound reaches `ApertureRoute.ConfinesAtAnAperture`.

`(EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)` at every even aperture past `N₀` and
every coupling — one number, no mode set, no weights — gives the confinement predicate. This is
`confines_of_geometric_profile` instantiated at `M := 1`.

DERIVED: `1` is that instantiated total weight, the normalisation of a single-cut profile; `0 ≤ r`
and `r < 1` are `confines_of_geometric_profile`'s range, with `r` in the part of `ρ'(1)`. The `+ 1`
of `Fin (p.1 + 1)` is the lag count at aperture `p`. -/
theorem confines_of_single_cut {N₀ : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_geometric_profile (N₀ := N₀) (M := 1) zero_le_one hr0 hr1 ?_
  intro p hp β d
  simpa using hprof p hp β d

#print axioms confines_of_single_cut

/-- `ApertureRoute.FlagshipAt` applied to `confines_of_single_cut`.

The hypothesis is the narrowest in the file: `(EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)`
with `r < 1`, at every even aperture past `N₀` and every coupling. `r` is bound outside both
quantifiers, so the margin is uniform in aperture and coupling. It is a hypothesis of the statement.

DERIVED: `0 ≤ r`, `r < 1` and the `+ 1` of `Fin (p.1 + 1)` are `confines_of_single_cut`'s, carried
unchanged. -/
theorem flagship_of_single_cut {N₀ : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_single_cut hr0 hr1 hprof) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_single_cut



/-! ## 7. What `ConfinesAtAnAperture` is a statement about

`ApertureRoute.ConfinesAtAnAperture` quantifies over `EvenAperture.EvenAp`, a natural number with a
parity proof, and its body names `ApertureRoute.cosAvgEven`, which unfolds to `MassGap.wilsonCorrAt`.
No structure is instantiated, so there is no field a caller chooses — which is what
`FlagshipScope.flagship_for_bogus` exploits one level up, where `LatticeYM` is a structure and its
tension is a field.

`cosAvgEven_is_a_wilson_ratio` states this as an equation: the cosine average is a ratio of two sums
of `MassGap.wilsonCorrAt`, with the read's lag angle as the only other ingredient.

`FlatProfileAllApertures` exhibits a profile satisfying every β-uniform shape fact the tree states
and failing the criterion at every even aperture, so the condition can be met and can fail, and both
are theorems.
-/

/-- `ApertureRoute.cosAvgEven a β` is a ratio of two sums of `MassGap.wilsonCorrAt` at the clamped
coupling:
`(∑ d, wilsonCorrAt a.1 (max β 0) d * cos θ d) / (∑ d, wilsonCorrAt a.1 (max β 0) d)`, with `θ` the
read's lag angle. The denominator identity is `NonnegArm.readEven_rho`.

DERIVED: `0` is the clamp `max β 0`, which is `EvenAperture.readEven`'s own; no constant is
introduced here. -/
theorem cosAvgEven_is_a_wilson_ratio (a : MassGap.EvenAperture.EvenAp) (β : ℝ) :
    MassGap.ApertureRoute.cosAvgEven a β
      = (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d
            * Real.cos ((MassGap.EvenAperture.readEven a β).θ d))
        / (∑ d, MassGap.wilsonCorrAt a.1 (max β 0) d) := by
  have hden : (∑ d', (MassGap.EvenAperture.readEven a β).ρ d')
      = ∑ d', MassGap.wilsonCorrAt a.1 (max β 0) d' :=
    Finset.sum_congr rfl (fun d' _ => MassGap.NonnegArm.readEven_rho a β d')
  show (∑ d, (MassGap.EvenAperture.readEven a β).p d
      * Real.cos ((MassGap.EvenAperture.readEven a β).θ d)) = _
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  show (MassGap.EvenAperture.readEven a β).ρ d / (∑ d', (MassGap.EvenAperture.readEven a β).ρ d')
      * Real.cos ((MassGap.EvenAperture.readEven a β).θ d) = _
  rw [MassGap.NonnegArm.readEven_rho, hden]
  ring

#print axioms cosAvgEven_is_a_wilson_ratio

/-! ## What `FlagshipAt` covers

Every `flagship_of_…` in this file ends at `ApertureRoute.flagship_of_confinement_at_an_aperture`.
`MassGap.FlagshipScope`, deliberately not imported, records what that endpoint says:

* `flagship_for_bogus` derives the whole flagship conclusion — a gap, non-triviality `μ − κ < 0`,
  `SO(4)`, and the OS0–OS3 continuum measure — for `bogusWilson`, a `LatticeYM` with no read, no
  correlation, no gauge group and no lattice in it, whose tension is the constant `0`.
* `gap_summand_is_manufactured`: the correlation the gap clause is about is `exp(−(κ₀ − μ))^τ`, one
  mode of weight `1` whose magnitude is its own bound.
* `flagship_measure_half_needs_no_hypothesis`: the measure half takes no hypothesis.
* `Q_is_constant_in_the_test_configuration`: OS1 and OS3 hold because the reflected form is
  independent of the components those actions move.

`ApertureRoute.ConfinesAtAnAperture` is the step the hypotheses attach to, and it is a statement
about `cosAvgEven` of `EvenAperture.readEven`, hence about `MassGap.wilsonCorrAt` at an even
aperture. Each `confines_of_…` here is that statement; each `flagship_of_…` packages it for the
assembly, adding the clauses above.
-/
end MassGap.GeometricProfile
