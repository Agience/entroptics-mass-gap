import Mathlib
import MassGap.MomentArms

/-!
# MassGap.GeometricProfile — a geometric profile has a geometric far share, uniformly in the aperture

`MomentArms.flagship_of_geometric_far_share` reaches the Clay flagship from a geometric bound on the
FAR SHARE. What a mass gap actually gives is a geometric bound on the PROFILE — `ρ(d) ≤ M·r^{circLag d}`
— and the far share is a sum of the profile over a set whose size grows with the aperture. The step
between them is the one arrow that was not a theorem.

**It is a counting fact.** At most TWO lags sit at any one circle distance: `circLag d = min d (N+1−d)`
equals `j` only if `d = j` or `d = N+1−j`. So the far share past `m` is at most `2` times a geometric
tail, and `2·M·r^{m+1}/(1−r)` bounds it **with no `N` in it**. That is what makes the bound survive
the aperture limit, and it is exactly what a bound by the far set's CARDINALITY would not do — that
would carry an `N+1` and be useless.

## What this closes and what it does not

It closes `geometric profile ⟹ geometric far share`. It does not close `spectral margin ⟹ geometric
profile`: that is the relation between a Koopman spectrum and a lag profile, and nothing here
establishes it. The remaining arrow is smaller and more specific than it was, and it is named.
-/

namespace MassGap.GeometricProfile

open Finset

/-- **AT MOST TWO LAGS SHARE A CIRCLE DISTANCE.**

`circLag d = min d (N+1−d) = j` forces `d = j` or `d = N+1−j`, so the fibre injects into a two-element
set of naturals.

DERIVED: the `2` is the two ways round a circle, not a chosen constant. -/
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

/-- The geometric tail, in closed form: `∑_{j ∈ [a, K)} r^j ≤ r^a/(1−r)`.

DERIVED: `1 − r` is the geometric series' own denominator; nothing is chosen. -/
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

/-- **A GEOMETRIC PROFILE HAS A GEOMETRIC FAR SHARE, WITH NO APERTURE IN THE CONSTANT.**

`p d ≤ M·r^{circLag d}` gives `farShare R m ≤ (2M/(1−r))·r^{m+1}`. The `2` is the counting fact; the
geometric tail supplies the rest. **Bounding by the far set's cardinality instead would carry an
`N+1` and be useless in the aperture limit** — the counting is the whole content.

DERIVED: `2` is the two ways round the circle; `1 − r` is the geometric denominator. -/
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

/-- **AND THEREFORE CONFINEMENT AT AN APERTURE, FROM A GEOMETRIC PROFILE.**

`ρ(d) ≤ M·r^{circLag d}` at every even aperture past `N₀` and every coupling — the exact form
`‖C(τ)‖ ≤ M e^{−Δτ}` takes on the circle.

The envelope handed on is `(2Mr/(1−r))·r^m`, which is `farShare_le_of_geometric_profile`'s bound
rewritten with the `r^{m+1}` split; no aperture appears in it. -/
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

/-- **AND THE CLAY FLAGSHIP FROM IT.** -/
theorem flagship_of_geometric_profile {N₀ : ℕ} {M r : ℝ}
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ M * r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_geometric_profile hM hr0 hr1 hprof) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_geometric_profile


/-! ## 2. The other half: a spectral representation with a margin

§1 closes `geometric profile ⟹ geometric far share`. The remaining arrow was
`spectral margin ⟹ geometric profile`, and **once the representation is written down it is
`Aperture.finite_sum_margin_bound` evaluated at `circLag d`** — the bound on a finite exponential sum
whose modes share a margin.

So the arrow was never the hard part. **The hard part is the REPRESENTATION**: that the profile IS a
finite exponential sum in the circle distance,

    ρ(d) = ∑ₖ Pₖ · μₖ^{circLag d},

which is the transfer-matrix spectral decomposition on a periodic extent. `circLag` rather than the
raw index is what makes it a statement about the circle, and `MomentShape.wilsonCorrAt_circLag_congr`
already proves the Wilson correlation reads the lag only through `circLag`, so the shape is right.

**That representation is what C1's transfer operator is FOR.** `SliceTransferSelfAdjoint.transferCLM`
is positive (`TransferGaussian.transferKernel_posDef`) and injective
(`TransferGaussian.transferCLM_injective`); a spectral decomposition of it with modes inside the disc
is exactly `hrep` and `hmargin` below. **So the two halves of this effort meet here**: the operator
side supplies the representation, the margin supplies the decay, and B5 follows.

Neither is discharged. What this section does is make the join explicit and one step wide.
-/

/-- **A REPRESENTED PROFILE WITH A MARGIN IS GEOMETRIC.**

`ρ(d) = ∑ₖ Pₖ μₖ^{circLag d}` with `‖μₖ‖ ≤ r` gives `ρ(d) ≤ (∑ₖ‖Pₖ‖)·r^{circLag d}`. The profile is
nonnegative, so it is its own absolute value and the norm bound applies directly.

DERIVED: no numeral. `M = ∑ₖ‖Pₖ‖` is the representation's own total weight. -/
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

/-- **AND THE CLAY FLAGSHIP FROM A SPECTRAL REPRESENTATION WITH A MARGIN.**

The join, in one statement: if at every even aperture past `N₀` and every coupling the profile is a
finite exponential sum in the circle distance whose modes share a margin `r < 1`, then
`ApertureRoute.FlagshipAt`.

**Both hypotheses are named and neither is discharged.** `hrep` is the transfer-matrix spectral
decomposition — what C1's operator is for — and `hmargin` is the gap itself. What is proved is that
together they suffice, with no further estimate of any kind. -/
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

/-- **AND THE FLAGSHIP.** -/
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


/-! ## 3. The PERIODIC form, which is the one the physics gives

§2 assumes `ρ(d) = ∑ₖ Pₖ μₖ^{circLag d}` — already a function of the circle distance. **On a periodic
extent that is an idealisation.** The transfer-matrix spectral form is

    ρ(d) = ∑ₙ wₙ e^{−Eₙ d},   wₙ ≥ 0

— which is what `Complete.wilson_reflection_positive_at`'s own docstring cites — and closing it into a
ring adds the IMAGE term:

    ρ(d) = ∑ₙ wₙ (mₙ^{d} + mₙ^{N+1−d}),   mₙ = e^{−Eₙ}.

The image term is not a function of `d` alone in any obvious geometric way, and its base `mₙ^{-1}`
lies OUTSIDE the unit disc if one insists on writing it as an exponential in `d`. So §2's hypothesis
does not literally hold.

**It does not need to.** `circLag d = min d (N+1−d)` is by construction at most BOTH exponents, and
`0 ≤ m ≤ 1` makes `m^a ≤ m^{circLag d}` for either. So each mode contributes at most `2·m^{circLag d}`
and the whole profile is geometric in the circle distance with `M = 2∑ₙwₙ`:

    ρ(d) ≤ (2∑ₙ wₙ) · r^{circLag d}.

**The image term costs a factor of two and nothing else.** That is the content of this section, and it
is why `circLag` is the right variable rather than a convenience.

Everything here is REAL and NONNEGATIVE, as the spectral form is — no complex modes, no cancellation,
and the weights are the `wₙ ≥ 0` reflection positivity supplies.
-/

/-- **THE IMAGE TERM IS BOUNDED BY THE DIRECT TERM.** `circLag d` is at most both `d` and `N+1−d`, so
for `0 ≤ m ≤ 1` each of `m^d` and `m^{N+1−d}` is at most `m^{circLag d}`.

DERIVED: the `2` is the two terms, direct and image; not a chosen constant. -/
theorem periodic_pair_le {N : ℕ} (d : Fin (N + 1)) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    m ^ ((d : ℕ)) + m ^ (N + 1 - (d : ℕ)) ≤ 2 * m ^ (Moment.circLag d) := by
  have hdir : m ^ ((d : ℕ)) ≤ m ^ (Moment.circLag d) :=
    pow_le_pow_of_le_one hm0 hm1 (min_le_left _ _)
  have himg : m ^ (N + 1 - (d : ℕ)) ≤ m ^ (Moment.circLag d) :=
    pow_le_pow_of_le_one hm0 hm1 (min_le_right _ _)
  linarith

#print axioms periodic_pair_le

/-- **THE PERIODIC SPECTRAL FORM IS GEOMETRIC IN THE CIRCLE DISTANCE.**

`ρ(d) = ∑ₙ wₙ (mₙ^d + mₙ^{N+1−d})` with `wₙ ≥ 0` and `0 ≤ mₙ ≤ r < 1` gives
`ρ(d) ≤ (2∑ₙwₙ)·r^{circLag d}`. The image term costs the factor `2`.

DERIVED: `2` is the two terms; `r` and the weights are the caller's. -/
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

/-- **AND THE CLAY FLAGSHIP FROM THE PERIODIC SPECTRAL FORM.**

This is the join in the shape the physics actually supplies it: nonnegative weights, real modes inside
the disc, and the image term the ring closure adds. Nothing complex, nothing idealised.

**The two hypotheses are `hrep` — the transfer-matrix spectral decomposition, which is what C1's
operator is for — and `hmr`, the margin, which is the gap. Neither is discharged here.** -/
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

/-- **AND THE FLAGSHIP.** -/
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


/-! ## 4. The obligation is satisfiable, and it has teeth

A named hypothesis is worth stating only if something can meet it and something can fail it. §3's
`hrep` is checked both ways here.

**Satisfiable.** A single mode gives a genuine `Moment.Read` whose profile is exactly the periodic
spectral form: `ρ(d) = r^d + r^{N+1−d}`, nonnegative with positive total, so `readA` accepts it, and
the normalisation is the weight. Nothing is approximated.

**And it has teeth.** §3 forces `p d ≤ W·r^{circLag d}` at every lag, so at the ANTIPODE — where
`circLag` is largest — the profile is exponentially small in the EXTENT. A flat profile has
`p d = 1/(N+1)` everywhere, which is polynomially small, so **no flat profile admits the periodic
spectral form at large extent.** That is the same witness `FlatProfileAllApertures` uses to close the
shape-facts route, failing the hypothesis rather than the conclusion — the two agree.
-/

/-- A single-mode periodic profile: the direct term and its image round the ring.

DERIVED: the `N + 1` is the periodic extent the lag index runs over, so `N + 1 - d` is the same
separation measured the other way round the circle -- `Moment.circLag`'s own arithmetic, carried
unchanged. Neither is a magnitude. -/
noncomputable def singleModeProfile (N : ℕ) (r : ℝ) (d : Fin (N + 1)) : ℝ :=
  r ^ ((d : ℕ)) + r ^ (N + 1 - (d : ℕ))

#print axioms singleModeProfile

/-- It is nonnegative with positive total, so `readA` accepts it. The positivity comes from lag zero,
where the direct term is `r^0 = 1`. -/
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

/-- **THE OBLIGATION IS SATISFIABLE.** A genuine `Moment.Read` whose profile is exactly the periodic
spectral form of §3, with one mode and the normalisation as its weight.

This is the check a named hypothesis has to pass before the reduction counts as one. -/
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

/-- **AND IT HAS TEETH: the profile is exponentially small at the antipode.**

§3's conclusion at any lag, stated so the consequence is visible: a profile admitting the periodic
spectral form is bounded by `W·r^{circLag d}`, which at the largest circle distance is exponentially
small in the EXTENT.

A flat profile is `1/(N+1)` everywhere — polynomially small — so at large extent it cannot admit the
form. **The hypothesis fails on the same witness `FlatProfileAllApertures` uses to close the
shape-facts route**, which is the consistency one wants: the witness that breaks the conclusion also
breaks the hypothesis. -/
theorem periodic_spectral_forces_antipodal_decay {N : ℕ} (R : Moment.Read N) {ι : Type*}
    (s : Finset ι) (w m : ι → ℝ) {r : ℝ} (hr1 : r < 1)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hm0 : ∀ k ∈ s, 0 ≤ m k) (hmr : ∀ k ∈ s, m k ≤ r)
    (hrep : ∀ d : Fin (N + 1), R.p d
      = ∑ k ∈ s, w k * ((m k) ^ ((d : ℕ)) + (m k) ^ (N + 1 - (d : ℕ))))
    (d : Fin (N + 1)) :
    R.p d ≤ (2 * ∑ k ∈ s, w k) * r ^ (Moment.circLag d) :=
  profile_geometric_of_periodic_spectral R s w m hr1 hw hm0 hmr hrep d

#print axioms periodic_spectral_forces_antipodal_decay


/-! ## 5. The spectrum is COUNTABLE, not finite — and that is the second idealisation

§3 fixed one idealisation in §2: the periodic image term. **There is a second, and it is in §3 too.**
Both write the spectral sum over a `Finset`, and the genuine operator does not have finitely many
modes.

`SliceTransferSelfAdjoint.transferCLM` is an integral operator with a bounded continuous kernel on a
COMPACT configuration space against a finite measure. Such an operator is Hilbert–Schmidt, hence
compact, and a compact operator on an infinite-dimensional space has a spectrum that is a countable
sequence accumulating only at zero — **infinitely many modes, not finitely many.** `L²(sliceHaar)` is
infinite-dimensional because the coordinate monomials are infinitely many independent functions
(`TransferGaussian.coordAlgebra_dense_in_L2` is about exactly that algebra).

So a `Finset` spectral sum is not what the operator supplies, and a hypothesis written that way would
be met by nothing.

**The fix costs one summability hypothesis.** `∑' w` in place of `∑ w`, `tsum_le_tsum` in place of
`Finset.sum_le_sum`, and `Summable w` — which is exactly trace-class-ness of the weights and is what a
convergent spectral decomposition gives anyway. The conclusion is unchanged:

    ρ(d) ≤ (2 ∑' w) · r^{circLag d}.

§3 is kept: on a finite mode set it is the same statement without the summability side condition, and
the finite case is the one a numerical spectrum actually presents.
-/

/-- **THE COUNTABLE PERIODIC SPECTRAL FORM IS GEOMETRIC IN THE CIRCLE DISTANCE.**

§3 with `∑'` in place of `∑`. The summability of the weights is the one added hypothesis, and it is
what any convergent spectral decomposition supplies.

DERIVED: `2` is the direct and image terms, as in §3. -/
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

/-- **CONFINEMENT FROM A COUNTABLE SPECTRUM.** The form the genuine compact operator supplies. -/
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

/-- **AND THE FLAGSHIP, FROM THE FORM THE GENUINE OPERATOR SUPPLIES.**

The sharpest statement of B5 in this tree. Two hypotheses, and both are about the transfer operator's
spectrum rather than about any estimate of the correlation:

* `hrep` + `hsum` — a convergent periodic spectral decomposition with nonnegative weights. This is
  what C1's operator is for, and `transferCLM` being positive and injective is progress toward it.
* `hmr` — the modes share a margin `r < 1`. **This is the mass gap.**

Everything between them and `ApertureRoute.FlagshipAt` is proved, foundational-only, with the
negative half-line discharged, small extents never consulted and small lags never consulted. -/
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


/-! ## 6. ⚠ THE SINGLE CUT — and this section exists because §2–§5 are more general than the theory

`PAPER.md`'s abstract states the structure plainly:

> Reflection positivity makes the transfer operator self-adjoint, giving `ρ'(n) = ρ'(1)^n`, so a
> single-cut magnitude `ρ'(1) < 1` carries the gap uniform in volume.

**That is ONE number, not a spectrum.** `MassGap.Mixing` already carries it —
`gap_of_maximal_correlation` takes `σ n ≤ σ 0 · ρ₁^n` with `ρ₁ < 1` and concludes `σ → 0`, and its
header says why: *"one cut controls every separation and every volume, so `ρ'(1) < 1` gives the
uniform-in-volume gap for free — no separate intensive-margin companion."*

§2–§5 of this file reconstruct a multi-mode spectral route to the same place. **They are more general
than the theory needs**, and generality is not free: each extra mode is an extra hypothesis someone
has to supply. The single-cut case is the one the physics asserts and the one a measurement reports
(`m_hi(L) = ρ'(1)(L)`, plateau `≈ 0.33` against the ceiling `3^{-1/4} = 0.76`).

**The two are different ENDPOINTS, which is why both are kept.** `Mixing` lands on
`ReachFreeze`'s excess; this file lands on `d2Even` and thence `ApertureRoute.FlagshipAt`. What was
missing was the single-cut statement at THIS endpoint, and that is all §6 is.
-/

/-- **THE SINGLE-CUT PROFILE BOUND REACHES THE FLAGSHIP.**

`ρ(d) ≤ r^{circLag d}` — one number, no spectrum, no weights — delivers
`ApertureRoute.ConfinesAtAnAperture`. This is `confines_of_geometric_profile` at `M = 1`, stated
separately because it is the form `PAPER.md` and `Mixing` both use and the form a measurement
reports.

DERIVED: `1` is the total weight of a normalised single-cut profile; `r` is `ρ'(1)`. -/
theorem confines_of_single_cut {N₀ : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.ConfinesAtAnAperture := by
  refine confines_of_geometric_profile (N₀ := N₀) (M := 1) zero_le_one hr0 hr1 ?_
  intro p hp β d
  simpa using hprof p hp β d

#print axioms confines_of_single_cut

/-- **AND THE CLAY FLAGSHIP FROM ONE NUMBER.**

`ρ'(1) < 1` at every even aperture past `N₀` and every coupling gives `ApertureRoute.FlagshipAt`.

**This is the narrowest hypothesis in the file**, and it is the one the paper's `ρ'(n) = ρ'(1)^n`
supplies and the one `research/` measures. It is not discharged: `ρ'(1) < 1` uniformly in coupling
and aperture IS the mass gap. -/
theorem flagship_of_single_cut {N₀ : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprof : ∀ (p : MassGap.EvenAperture.EvenAp), N₀ ≤ p.1 → ∀ (β : ℝ) (d : Fin (p.1 + 1)),
      (MassGap.EvenAperture.readEven p β).p d ≤ r ^ (Moment.circLag d)) :
    MassGap.ApertureRoute.FlagshipAt (confines_of_single_cut hr0 hr1 hprof) :=
  MassGap.ApertureRoute.flagship_of_confinement_at_an_aperture _

#print axioms flagship_of_single_cut



/-! ## 7. And the check one level down: `ConfinesAtAnAperture` IS about the Wilson correlation

§6's note says the content of every chain here sits at `ApertureRoute.ConfinesAtAnAperture` rather
than at the `FlagshipAt` packaging. **That claim deserves the same treatment `FlagshipScope` gave the
flagship**: stated as a theorem, not asserted in prose.

`flagship_for_bogus` works because `LatticeYM` is a STRUCTURE — anyone can instantiate it with a
tension of their choosing, and the flagship's clauses are about the fields of whatever was
instantiated. `ConfinesAtAnAperture` has no such freedom: it quantifies over `EvenAp`, which is a
natural number with a parity proof, and its body names `cosAvgEven`, which unfolds to the genuine
`wilsonCorrAt`. There is nothing to fabricate.

`cosAvgEven_is_a_wilson_ratio` makes that visible in one line — the cosine average is a ratio of two
sums of `MassGap.wilsonCorrAt`, and the only other ingredient is the read's lag angle, which is
lattice geometry rather than a free parameter.

**And the hypothesis is FALSIFIABLE**, which is the other half of not being vacuous:
`FlatProfileAllApertures` exhibits a profile satisfying every β-uniform shape fact the tree states and
failing the criterion at every even aperture. So the condition can be met and can fail, and both are
theorems.
-/

/-- **THE CONFINEMENT HYPOTHESIS IS A STATEMENT ABOUT THE WILSON CORRELATION.**

`cosAvgEven` is a ratio of two sums of `MassGap.wilsonCorrAt` at the clamped coupling. No structure is
instantiated, nothing is opaque, and there is no field a counterexample could choose — which is
exactly what `FlagshipScope.flagship_for_bogus` exploits one level up and cannot do here.

DERIVED: no numeral. The clamp `max β 0` is `readEven`'s own. -/
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

/-! ## ⚠ WHAT `FlagshipAt` IS WORTH, AND IT IS LESS THAN ITS NAME

Every `flagship_of_…` in this file ends at `ApertureRoute.flagship_of_confinement_at_an_aperture`, and
`MassGap.FlagshipScope` — the tree's own adversarial audit, deliberately not imported — shows what
that endpoint does and does not say:

* **`flagship_for_bogus`** proves the WHOLE flagship conclusion — mass gap, non-triviality
  (`μ − κ < 0`), `SO(4)`, and the OS0–OS3 continuum measure — for `bogusWilson`, an object with **no
  read, no correlation, no gauge group and no lattice in it**, whose tension is the constant `0`.
* **`gap_summand_is_manufactured`**: the "correlation" the gap clause is about is
  `exp(−(κ₀ − μ))^τ` — one mode, weight `1`, and **its magnitude DEFINED as its own bound**.
* **`flagship_measure_half_needs_no_hypothesis`**: the measure half takes no hypothesis at all.
* **`Q_is_constant_in_the_test_configuration`**: OS1 and OS3 hold because the reflected form is
  independent of the components those actions move.

**So "reaches the Clay flagship" is not the claim it sounds like.** What carries content in these
chains is the step BEFORE it — `ApertureRoute.ConfinesAtAnAperture`, which is a statement about
`cosAvgEven` of `readEven`, hence about the genuine `wilsonCorrAt` at an even aperture. The
`FlagshipAt` corollaries add the manufactured clauses and nothing else.

Each `confines_of_…` here is therefore the theorem; each `flagship_of_…` is its packaging, kept
because the packaging is what the assembly consumes, and labelled so it is not mistaken for more.
-/
end MassGap.GeometricProfile
