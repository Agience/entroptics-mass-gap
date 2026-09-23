import MassGap.GappedExample
import MassGap.YMGap

/-!
# MassGap.MassFinite — Clay's admissible gaps, their supremum, and two witnesses attaining it

Jaffe–Witten define the mass of a quantum theory as a supremum: *"A quantum field theory has a mass
gap `Δ` if `H` has no spectrum in the interval `(0, Δ)` for some `Δ > 0`. The supremum of such `Δ`
is the mass `m`, and we require `m < ∞`."*

A containment `spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ` says `Δ` is admissible and leaves the admissible set
possibly unbounded above — it is unbounded for `H = 0` on a one-dimensional space. Bounding the
supremum therefore requires a strictly positive point of `spectrum ℝ H`, exhibited.

`AdmissibleGaps H` is the set of such `Δ` and `clayMass H` its supremum. The membership direction of
the spectral mapping equality `cfc_map_spectrum` is what produces the required point:

* `lam_mem_spectrum_diagOp` — every value of `lam` lies in `spectrum ℝ (diagOp lam)`, with no
  hypothesis. With `GapOfDecay.mem_spectrum_diagOp` this makes the spectrum equal to the range.
* `hamiltonian_mem_spectrum` — for self-adjoint `T` with strictly positive spectrum, each
  `x ∈ spectrum ℝ T` gives `-Real.log x ∈ spectrum ℝ (hamiltonian T)`.
* `isGreatest_admissibleGaps` — a spectral point `Δ > 0` together with
  `spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ` makes `Δ` the greatest admissible gap, so the set is bounded
  above and `clayMass H = Δ`.

## Scope of the two witnesses

The two instantiations are `concreteGapped`, whose transfer operator is `Tc = diag(1, 3^(-1/4))` on
`Fin 2 → ℂ`, and `ymGapped N β hconf`, whose transfer datum is `diag(1, exp (-(ΔYMAt N β)))` on the
same two-point index. For both, the mass is exact: `clayMass concreteGapped.ham = κ0 = ¼ log 3` and
`clayMass (ymGapped N β hconf).ham = ΔYMAt N β`.

Both are statements about those two-mode operators. No Wilson transfer operator is constructed in
this development, so `ymGapped` carries the number `ΔYMAt N β` on a two-dimensional carrier rather
than being built from the Wilson action.

The generic lemmas and the concrete witness carry foundational axioms only; the Yang–Mills
statements carry the reduction's existing footprint and add no axiom of their own.

DERIVED: `0` is the vacuum energy that Clay's interval `(0, Δ)` has as its left endpoint, the
positivity threshold on `Δ` and on spectral values, and the singleton in the containment; `1` is the
vacuum eigenvalue of both transfer data; `2` is the carrier's mode count, `Fin 2`; `3` and `4` are
the base and root order in `3 ^ (-(1:ℝ) / 4)`, the excited eigenvalue of `Tc`, whose energy is
`κ0 = ¼ log 3`.
-/

namespace MassGap.Reconstruction

open scoped ComplexOrder

/-! ## Clay's admissible gaps and the mass `m` -/

variable {A : Type*} [CStarAlgebra A]

/-- The set of admissible gaps of `H`: those `Δ : ℝ` with `0 < Δ` and
`spectrum ℝ H ∩ Set.Ioo 0 Δ = ∅`. This transcribes the Jaffe–Witten condition "`H` has no spectrum
in the interval `(0, Δ)` for some `Δ > 0`". Stated for any `A` with a `CStarAlgebra` instance.

DERIVED: `0` is the positivity threshold on `Δ` and the left endpoint of Clay's interval `(0, Δ)`,
where the vacuum sits. Neither is chosen here. -/
def AdmissibleGaps (H : A) : Set ℝ := {Δ : ℝ | 0 < Δ ∧ spectrum ℝ H ∩ Set.Ioo 0 Δ = ∅}

/-- The mass `m` of Clay row B3: `sSup (AdmissibleGaps H)`. Row B3 asks that this be finite, which
in `ℝ` is `BddAbove (AdmissibleGaps H)` — `sSup` of a set unbounded above returns a junk value, so
`clayMass` carries information only together with that boundedness.

DERIVED: no numeral appears in the statement. -/
noncomputable def clayMass (H : A) : ℝ := sSup (AdmissibleGaps H)

/-- `IsGreatest (AdmissibleGaps H) Δ` from three inputs: `0 < Δ`, `Δ ∈ spectrum ℝ H`, and
`spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ`. Membership of `Δ` in the set uses the containment, since any
spectral point in `Set.Ioo 0 Δ` would be neither `0` nor at least `Δ`. Upper-boundedness uses the
exhibited spectral point: an admissible `δ > Δ` would place `Δ` in `spectrum ℝ H ∩ Set.Ioo 0 δ`,
which is empty.

Both directions are needed, and the spectral point is what supplies the upper bound; a containment
alone leaves the set possibly unbounded.

DERIVED: `0` is the positivity threshold on `Δ`, the left endpoint of Clay's interval, and the
singleton in the containment. -/
theorem isGreatest_admissibleGaps {H : A} {Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : Δ ∈ spectrum ℝ H) (hsub : spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ) :
    IsGreatest (AdmissibleGaps H) Δ := by
  constructor
  · refine ⟨hΔ, ?_⟩
    refine Set.subset_empty_iff.mp ?_
    rintro x ⟨hx, hx0, hxΔ⟩
    rcases hsub hx with h | h
    · exact absurd (Set.mem_singleton_iff.mp h) hx0.ne'
    · exact absurd (Set.mem_Ici.mp h) (not_le.mpr hxΔ)
  · rintro δ ⟨-, hempty⟩
    by_contra hc
    rw [not_le] at hc
    have hin : Δ ∈ spectrum ℝ H ∩ Set.Ioo 0 δ := ⟨hmem, hΔ, hc⟩
    rw [hempty] at hin
    simp at hin

/-- `BddAbove (AdmissibleGaps H)` under the same three hypotheses, as the `bddAbove` field of
`isGreatest_admissibleGaps`. This is Clay row B3's `m < ∞` for `H`.

DERIVED: `0` is the positivity threshold on `Δ` and the singleton in the containment. -/
theorem bddAbove_admissibleGaps {H : A} {Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : Δ ∈ spectrum ℝ H) (hsub : spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ) :
    BddAbove (AdmissibleGaps H) :=
  (isGreatest_admissibleGaps hΔ hmem hsub).bddAbove

/-- `clayMass H = Δ` under the same three hypotheses, as `csSup_eq` applied to
`isGreatest_admissibleGaps`. The mass is not merely finite but equal to the exhibited spectral
point.

DERIVED: `0` is the positivity threshold on `Δ` and the singleton in the containment. -/
theorem clayMass_eq {H : A} {Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : Δ ∈ spectrum ℝ H) (hsub : spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ) :
    clayMass H = Δ :=
  (isGreatest_admissibleGaps hΔ hmem hsub).csSup_eq

#print axioms isGreatest_admissibleGaps

/-! ## The spectral mapping equality, in its membership direction -/

/-- `-Real.log x ∈ spectrum ℝ (hamiltonian T)` for every `x ∈ spectrum ℝ T`, given that `T` is
self-adjoint and every spectral value is strictly positive. Positivity is what makes `-Real.log`
continuous on `spectrum ℝ T`, which is the side condition of `cfc_map_spectrum`; the conclusion is
that equality read from right to left.

`Reconstruction.hamiltonian_vacuum_energy` is the same statement at the vacuum eigenvalue `1`. The
membership direction is what gives an upper bound on the mass; a containment `⊆` would bound the gap
only from below.

DERIVED: `0` is the positivity threshold every spectral value of `T` is required to exceed. -/
theorem hamiltonian_mem_spectrum (T : A) (hT : IsSelfAdjoint T)
    (hpos : ∀ x ∈ spectrum ℝ T, 0 < x) {x : ℝ} (hx : x ∈ spectrum ℝ T) :
    -Real.log x ∈ spectrum ℝ (hamiltonian T) := by
  have hcont : ContinuousOn (fun x : ℝ => -Real.log x) (spectrum ℝ T) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.mono
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hpos y hy).ne'
  unfold hamiltonian
  rw [cfc_map_spectrum (fun x : ℝ => -Real.log x) T]
  exact ⟨x, hx, rfl⟩

#print axioms hamiltonian_mem_spectrum

/-! ## The diagonal operator: the reverse spectral inclusion -/

variable {ι : Type*}

/-- `lam k ∈ spectrum ℝ (diagOp lam)` for every index `k`, with no hypothesis on `lam`. At index `k`
the element `algebraMap (lam k) - diagOp lam` has component `lam k - lam k = 0`, and `Pi.isUnit_iff`
reads unithood componentwise, so the element is not a unit.

Together with `GapOfDecay.mem_spectrum_diagOp`, which gives the other inclusion, the spectrum of
`diagOp lam` is the range of `lam`.

DERIVED: no numeral appears in the statement. -/
theorem lam_mem_spectrum_diagOp {lam : ι → ℝ} (k : ι) : lam k ∈ spectrum ℝ (diagOp lam) := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu k
  rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero,
    sub_ne_zero] at h0
  exact h0 (by simp [diagOp])

/-- `-Real.log (lam k) ∈ spectrum ℝ (hamiltonian (diagOp lam))` for every mode `k`, given a finite
index type and `0 < lam k` at every `k`. It feeds `lam_mem_spectrum_diagOp` and
`diagOp_selfAdjoint` to `hamiltonian_mem_spectrum`, the positivity of the whole spectrum coming from
`mem_spectrum_diagOp` and `hlam`.

DERIVED: `0` is the positivity threshold on each eigenvalue, required so that `-Real.log` is
continuous on the spectrum. -/
theorem neg_log_mem_spectrum_hamiltonian_diagOp [Fintype ι] {lam : ι → ℝ} (hlam : ∀ k, 0 < lam k)
    (k : ι) : -Real.log (lam k) ∈ spectrum ℝ (hamiltonian (diagOp lam)) := by
  refine hamiltonian_mem_spectrum _ (diagOp_selfAdjoint lam) ?_ (lam_mem_spectrum_diagOp k)
  intro x hx
  obtain ⟨j, rfl⟩ := mem_spectrum_diagOp hx
  exact hlam j

#print axioms neg_log_mem_spectrum_hamiltonian_diagOp

/-! ## The concrete witness: `m = κ₀ = ¼ log 3` -/

/-- `(3 : ℝ) ^ (-(1 : ℝ) / 4) ∈ spectrum ℝ Tc`, the excited eigenvalue of the concrete transfer
operator. Proved at index `1`, where `Tc_one` makes the component of
`algebraMap (3 ^ (-(1:ℝ)/4)) - Tc` zero, so `Pi.isUnit_iff` refutes unithood. It is
`GappedExample.one_mem` at index `1` in place of index `0`, with `Tc_one` for `Tc_zero`.

DERIVED: `3` and `4` are the base and root order of `Tc`'s excited eigenvalue `3 ^ (-1/4)`, which is
`exp (-κ0)`; `1` is the numerator of that exponent. -/
theorem rpow_mem : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ∈ spectrum ℝ Tc := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h1 := hu 1
  rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero, sub_ne_zero,
    Tc_one] at h1
  exact h1 rfl

/-- `0 < x` for every `x ∈ spectrum ℝ Tc`. By `spectrum_subset`, a spectral value is either `1` or
lies in an interval whose lower endpoint is `3 ^ (-(1:ℝ)/4)`, and `rpow_pos` makes that positive.
This is the side condition `hamiltonian_mem_spectrum` requires of `Tc`.

DERIVED: `0` is the level every spectral value is shown to exceed. -/
theorem Tc_spectrum_pos : ∀ x ∈ spectrum ℝ Tc, 0 < x := by
  intro x hx
  rcases spectrum_subset hx with h | h
  · rw [Set.mem_singleton_iff] at h; rw [h]; norm_num
  · exact lt_of_lt_of_le rpow_pos (Set.mem_Icc.mp h).1

/-- `concreteGapped.ham = hamiltonian Tc`, by `rfl`: the concrete theory's Hamiltonian field is the
continuous functional calculus of `-Real.log` applied to `Tc`.

DERIVED: no numeral appears in the statement. -/
theorem concreteGapped_ham : concreteGapped.ham = hamiltonian Tc := rfl

/-- `κ0 ∈ spectrum ℝ concreteGapped.ham`. The excited eigenvalue `3 ^ (-(1:ℝ)/4)` of `Tc` is sent
to `-Real.log (3 ^ (-(1:ℝ)/4))` by `hamiltonian_mem_spectrum`, and `Real.log_rpow` evaluates that to
`κ0`; the identification is computed rather than matched by hand.

DERIVED: no numeral appears in the statement. The `3` and `4` of the eigenvalue and of
`κ0 = ¼ log 3` occur in the proof. -/
theorem κ0_mem_spectrum_concrete : κ0 ∈ spectrum ℝ concreteGapped.ham := by
  have hval : -Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = κ0 := by
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    unfold κ0; ring
  have h := hamiltonian_mem_spectrum Tc Tc_selfAdjoint Tc_spectrum_pos rpow_mem
  rw [hval] at h
  rw [concreteGapped_ham]
  exact h

/-- `IsGreatest (AdmissibleGaps concreteGapped.ham) κ0`. It is `isGreatest_admissibleGaps` at
`Δ := κ0`, with `κ0_pos`, the attained point `κ0_mem_spectrum_concrete`, and the containment from
`concreteGapped.spectral_gap` rewritten by `concreteGapped_gap`.

DERIVED: no numeral appears in the statement; the `0` of `κ0` is part of that identifier, the
entropy floor ¼ log 3. -/
theorem isGreatest_admissibleGaps_concrete :
    IsGreatest (AdmissibleGaps concreteGapped.ham) κ0 := by
  refine isGreatest_admissibleGaps κ0_pos κ0_mem_spectrum_concrete ?_
  have h := concreteGapped.spectral_gap
  rwa [concreteGapped_gap] at h

/-- `BddAbove (AdmissibleGaps concreteGapped.ham)`: Clay row B3 for the concrete witness, whose
Hamiltonian is `-Real.log` of `Tc = diag(1, 3 ^ (-1/4))` on `Fin 2 → ℂ`. It is the `bddAbove` field
of `isGreatest_admissibleGaps_concrete`.

DERIVED: no numeral appears in the statement. -/
theorem mass_finite_concrete : BddAbove (AdmissibleGaps concreteGapped.ham) :=
  isGreatest_admissibleGaps_concrete.bddAbove

/-- `clayMass concreteGapped.ham = κ0`, the `csSup_eq` of `isGreatest_admissibleGaps_concrete`. The
lower bound comes from the spectral gap and the upper bound from the attained excited eigenvalue, so
the two meet at `κ0 = ¼ log 3`.

DERIVED: no numeral appears in the statement; the `0` of `κ0` is part of that identifier. -/
theorem clayMass_concrete : clayMass concreteGapped.ham = κ0 :=
  isGreatest_admissibleGaps_concrete.csSup_eq

#print axioms mass_finite_concrete
#print axioms clayMass_concrete

/-! ## The Yang–Mills witness: `m = ΔYMAt N β` -/

/-- `(ymGapped N β hconf).ham = hamiltonian (diagOp ![1, Real.exp (-(ΔYMAt N β))])` on
`Fin 2 → ℝ`, by `rfl`: the witness's Hamiltonian field is `-Real.log` of the two-mode diagonal
transfer datum.

DERIVED: `1` is the vacuum eigenvalue of the transfer datum; `2` is the mode count of the carrier,
`Fin 2`. -/
theorem ymGapped_ham (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    (ymGapped N β hconf).ham
      = hamiltonian (diagOp (![1, Real.exp (-(ΔYMAt N β))] : Fin 2 → ℝ)) := rfl

/-- `ΔYMAt N β ∈ spectrum ℝ (ymGapped N β hconf).ham`. The excited mode `exp (-(ΔYMAt N β))` at
index `1` of the transfer datum is carried to `ΔYMAt N β` by
`neg_log_mem_spectrum_hamiltonian_diagOp` and `Real.log_exp`. The membership direction comes from
`lam_mem_spectrum_diagOp`; a vacuum-only lemma exhibits the eigenvalue `1` and so cannot supply an
excited point.

DERIVED: no numeral appears in the statement. The index `1`, the vacuum eigenvalue `1` and the mode
count `2` occur in the proof, through `ymGapped_ham`. -/
theorem ΔYM_mem_spectrum_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    ΔYMAt N β ∈ spectrum ℝ (ymGapped N β hconf).ham := by
  have hlam : ∀ k : Fin 2, 0 < (![1, Real.exp (-(ΔYMAt N β))] : Fin 2 → ℝ) k := by
    intro k
    fin_cases k
    · simp
    · simpa using Real.exp_pos (-(ΔYMAt N β))
  have h := neg_log_mem_spectrum_hamiltonian_diagOp hlam 1
  have hval : (![1, Real.exp (-(ΔYMAt N β))] : Fin 2 → ℝ) 1 = Real.exp (-(ΔYMAt N β)) := by simp
  rw [hval, Real.log_exp, neg_neg] at h
  rw [ymGapped_ham]
  exact h

/-- `IsGreatest (AdmissibleGaps (ymGapped N β hconf).ham) (ΔYMAt N β)`. It is
`isGreatest_admissibleGaps` with positivity from `gap_pos_iff_confinement_at` applied to `hconf`,
the attained point `ΔYM_mem_spectrum_ym`, and the containment from `ym_spectral_gap`.

DERIVED: no numeral appears in the statement. -/
theorem isGreatest_admissibleGaps_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    IsGreatest (AdmissibleGaps (ymGapped N β hconf).ham) (ΔYMAt N β) :=
  isGreatest_admissibleGaps ((gap_pos_iff_confinement_at N β).mpr hconf)
    (ΔYM_mem_spectrum_ym N β hconf) (ym_spectral_gap N β hconf).2.2.2

/-- `BddAbove (AdmissibleGaps (ymGapped N β hconf).ham)`: Clay row B3 for the Yang–Mills witness,
the `bddAbove` field of `isGreatest_admissibleGaps_ym`. The bound is `ΔYMAt N β` itself.

The object is the two-mode transfer datum `diag(1, exp (-(ΔYMAt N β)))` that `ymGapped` builds; no
Wilson transfer operator is constructed in this development.

DERIVED: no numeral appears in the statement. -/
theorem mass_finite_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    BddAbove (AdmissibleGaps (ymGapped N β hconf).ham) :=
  (isGreatest_admissibleGaps_ym N β hconf).bddAbove

/-- `clayMass (ymGapped N β hconf).ham = ΔYMAt N β`, the `csSup_eq` of
`isGreatest_admissibleGaps_ym`. The lower bound is the reconstruction's spectral gap and the upper
bound the attained excited eigenvalue, so the mass equals the surplus
`ΔYMAt N β = κ₀YM - μYMAt N β` exactly, for this two-mode witness.

DERIVED: no numeral appears in the statement. -/
theorem clayMass_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    clayMass (ymGapped N β hconf).ham = ΔYMAt N β :=
  (isGreatest_admissibleGaps_ym N β hconf).csSup_eq

#print axioms mass_finite_ym
#print axioms clayMass_ym

end MassGap.Reconstruction
