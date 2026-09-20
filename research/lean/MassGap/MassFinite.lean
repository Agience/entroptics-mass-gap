import MassGap.GappedExample
import MassGap.YMGap

/-!
# Clay row B3: the mass `m` is finite — for the constructed witnesses

Jaffe–Witten define the mass of a quantum theory as a supremum, not a lower bound: *"A quantum field
theory has a mass gap `Δ` if `H` has no spectrum in the interval `(0, Δ)` for some `Δ > 0`. The
supremum of such `Δ` is the mass `m`, and we require `m < ∞`."*

Everything upstream in this development bounds the gap from BELOW: `spectrum H ⊆ {0} ∪ [Δ, ∞)` says
`Δ` is admissible, and nothing says the admissible set stops. A set of admissible `Δ` that is
unbounded above is the theory `H = 0` on a one-dimensional space — a vacuum and nothing else — for
which `m = ∞` and row B3 fails. Bounding `m` above therefore needs a point of `spectrum H` that is
strictly positive: one excited state, exhibited.

`AdmissibleGaps H` is Clay's set, `clayMass H` its supremum. The bridge is that the spectral mapping
theorem `cfc_map_spectrum` is an EQUALITY, so an eigenvalue of the transfer operator `T` produces a
genuine point of `spectrum (-log T)`, not merely a constraint on it. Concretely:

* `lam_mem_spectrum_diagOp` — the converse of `GapOfDecay.mem_spectrum_diagOp`: every eigenvalue of
  `diag(λ)` really is in the `ℝ`-spectrum. That direction was missing; it needs no hypothesis.
* `hamiltonian_mem_spectrum` — the membership form of `Reconstruction.hamiltonian_vacuum_energy`,
  with the vacuum eigenvalue `1` replaced by an arbitrary spectral point.
* `isGreatest_admissibleGaps` — one exhibited spectral point `Δ > 0` together with the upstream
  containment `spectrum H ⊆ {0} ∪ [Δ, ∞)` pins the supremum exactly: `m = Δ`, hence `m < ∞`.

## What this gives, and what it does not

It closes `m < ∞` for the CONSTRUCTED WITNESSES — `concreteGapped`, whose transfer operator is the
hand-set `Tc = diag(1, 3^{-1/4})` on `ℂ²`, and `ymGapped`, whose transfer datum is the hand-set
`diag(1, e^{-ΔYMAt N β})` on `ℂ²`. For those objects the mass is not merely finite but exact:
`m = κ₀ = ¼ log 3` and `m = ΔYMAt N β`. That is the same strength at which the gap bounds B1 and B2
hold for those objects, on the same operators — no more and no less.

It does NOT give `m < ∞` for the Wilson theory. No Wilson transfer operator is constructed anywhere
in this development, so there is no Wilson `H` whose spectrum could be exhibited; `ymGapped` is a
two-dimensional stand-in carrying the derived number `ΔYMAt N β`, not a transfer operator built from
the Wilson action. The upper bound proved here is a statement about the stand-in.

Foundational axioms only for the generic lemmas and the concrete witness; the Yang–Mills statements
carry the reduction's own footprint, unchanged (they add no axiom of their own).
-/

namespace MassGap.Reconstruction

open scoped ComplexOrder

/-! ## Clay's admissible gaps and the mass `m` -/

variable {A : Type*} [CStarAlgebra A]

/-- **Clay's admissible gaps.** `Δ` is admissible for `H` when `Δ > 0` and `H` has no spectrum in the
open interval `(0, Δ)` — verbatim the Jaffe–Witten condition "`H` has no spectrum in the interval
`(0, Δ)` for some `Δ > 0`".

DERIVED: the `0` is the vacuum energy, fixed by the Clay statement's own wording -- the
interval is `(0, Δ)` and the vacuum sits at its left endpoint. Nothing here chooses it. -/
def AdmissibleGaps (H : A) : Set ℝ := {Δ : ℝ | 0 < Δ ∧ spectrum ℝ H ∩ Set.Ioo 0 Δ = ∅}

/-- **The mass `m`** of Clay row B3: the supremum of the admissible gaps. Row B3 is the requirement
that this is finite, i.e. that `AdmissibleGaps H` is bounded above (a supremum of an unbounded-above
set is junk in `ℝ`, so `BddAbove` is the content, and `clayMass` is only meaningful with it). -/
noncomputable def clayMass (H : A) : ℝ := sSup (AdmissibleGaps H)

/-- **The mass is exactly `Δ` when `Δ` is both attained and the floor of the excited spectrum.** One
exhibited spectral point `Δ > 0` makes every admissible gap `≤ Δ` (an admissible gap `δ > Δ` would
put `Δ` inside the forbidden interval `(0, δ)`), and the upstream containment
`spectrum H ⊆ {0} ∪ [Δ, ∞)` makes `Δ` itself admissible. So `Δ` is the GREATEST admissible gap: the
set is bounded above and its supremum is `Δ`. This is the step that turns a lower bound on the gap
into the finiteness of the mass. -/
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

/-- **`m < ∞`**, from an exhibited excited spectral point at the gap. -/
theorem bddAbove_admissibleGaps {H : A} {Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : Δ ∈ spectrum ℝ H) (hsub : spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ) :
    BddAbove (AdmissibleGaps H) :=
  (isGreatest_admissibleGaps hΔ hmem hsub).bddAbove

/-- **`m = Δ`**, the exact Clay mass. -/
theorem clayMass_eq {H : A} {Δ : ℝ} (hΔ : 0 < Δ)
    (hmem : Δ ∈ spectrum ℝ H) (hsub : spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ) :
    clayMass H = Δ :=
  (isGreatest_admissibleGaps hΔ hmem hsub).csSup_eq

#print axioms isGreatest_admissibleGaps

/-! ## The spectral mapping equality, in its membership direction -/

/-- **Every spectral point of `T` produces one of `H = -log T`.** `Reconstruction.hamiltonian_vacuum_energy`
is this at the vacuum eigenvalue `1`; the `1` plays no role there beyond `map_one`, and dropping it
costs nothing. The proof is the forward reading of the spectral mapping EQUALITY
`spectrum (cfc f T) = f '' spectrum T` (`cfc_map_spectrum`), which is what makes an upper bound on
the mass available at all: the containment `⊆` alone would only ever bound the gap below. -/
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

/-- **Every eigenvalue of `diag(λ)` is in its `ℝ`-spectrum** — the converse of
`GapOfDecay.mem_spectrum_diagOp`, which had only `⊆`. No hypothesis is needed: at index `k` the
element `algebraMap (λ_k) - diag(λ)` is `λ_k - λ_k = 0`, and `Pi.isUnit_iff` reads unithood
componentwise. Together with `mem_spectrum_diagOp` this makes `spectrum ℝ (diag λ) = range λ`. -/
theorem lam_mem_spectrum_diagOp {lam : ι → ℝ} (k : ι) : lam k ∈ spectrum ℝ (diagOp lam) := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h0 := hu k
  rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero,
    sub_ne_zero] at h0
  exact h0 (by simp [diagOp])

/-- `-log λ_k` is in the spectrum of the reconstructed `H = -log diag(λ)`, for every mode `k`, once
every eigenvalue is positive (which `-log` needs to be continuous there). -/
theorem neg_log_mem_spectrum_hamiltonian_diagOp [Fintype ι] {lam : ι → ℝ} (hlam : ∀ k, 0 < lam k)
    (k : ι) : -Real.log (lam k) ∈ spectrum ℝ (hamiltonian (diagOp lam)) := by
  refine hamiltonian_mem_spectrum _ (diagOp_selfAdjoint lam) ?_ (lam_mem_spectrum_diagOp k)
  intro x hx
  obtain ⟨j, rfl⟩ := mem_spectrum_diagOp hx
  exact hlam j

#print axioms neg_log_mem_spectrum_hamiltonian_diagOp

/-! ## The concrete witness: `m = κ₀ = ¼ log 3` -/

/-- `3^{-1/4}` is in the spectrum of `Tc` — the EXCITED eigenvalue. This is `GappedExample.one_mem`
at index `1` instead of index `0`, with `Tc_one` for `Tc_zero`; `one_mem` could use `map_one` where
this goes through `Pi.algebraMap_apply`, and that is the whole difference. -/
theorem rpow_mem : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ∈ spectrum ℝ Tc := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Pi.isUnit_iff] at hu
  have h1 := hu 1
  rw [Pi.sub_apply, Pi.algebraMap_apply, Complex.coe_algebraMap, isUnit_iff_ne_zero, sub_ne_zero,
    Tc_one] at h1
  exact h1 rfl

/-- Both spectral points of `Tc` are strictly positive, so `-log` is continuous on `spectrum Tc`. -/
theorem Tc_spectrum_pos : ∀ x ∈ spectrum ℝ Tc, 0 < x := by
  intro x hx
  rcases spectrum_subset hx with h | h
  · rw [Set.mem_singleton_iff] at h; rw [h]; norm_num
  · exact lt_of_lt_of_le rpow_pos (Set.mem_Icc.mp h).1

/-- The concrete theory's Hamiltonian is `-log Tc`. -/
theorem concreteGapped_ham : concreteGapped.ham = hamiltonian Tc := rfl

/-- **`κ₀` is attained in the spectrum of the concrete Hamiltonian.** The excited eigenvalue
`3^{-1/4}` of `Tc` maps to `-log 3^{-1/4} = ¼ log 3 = κ₀` under the spectral mapping equality. The
value is derived from `Real.log_rpow`, not matched to `κ₀`'s definition by hand. -/
theorem κ0_mem_spectrum_concrete : κ0 ∈ spectrum ℝ concreteGapped.ham := by
  have hval : -Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = κ0 := by
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    unfold κ0; ring
  have h := hamiltonian_mem_spectrum Tc Tc_selfAdjoint Tc_spectrum_pos rpow_mem
  rw [hval] at h
  rw [concreteGapped_ham]
  exact h

/-- **`κ₀` is the greatest admissible gap of the concrete theory.** Below: the reconstructed spectrum
misses `(0, κ₀)` (`concreteGapped.spectral_gap`). Above: `κ₀` is itself in the spectrum, so no larger
`Δ` is admissible. -/
theorem isGreatest_admissibleGaps_concrete :
    IsGreatest (AdmissibleGaps concreteGapped.ham) κ0 := by
  refine isGreatest_admissibleGaps κ0_pos κ0_mem_spectrum_concrete ?_
  have h := concreteGapped.spectral_gap
  rwa [concreteGapped_gap] at h

/-- **Clay row B3 for the concrete witness: `m < ∞`.** The set of admissible gaps of the
reconstructed Hamiltonian `-log diag(1, 3^{-1/4})` is bounded above. -/
theorem mass_finite_concrete : BddAbove (AdmissibleGaps concreteGapped.ham) :=
  isGreatest_admissibleGaps_concrete.bddAbove

/-- **The concrete mass is exactly the entropy floor: `m = κ₀ = ¼ log 3`.** Both Clay inequalities on
one object: `m ≥ κ₀` is the spectral gap (B1/B2), `m ≤ κ₀` is the attained excited state (B3). -/
theorem clayMass_concrete : clayMass concreteGapped.ham = κ0 :=
  isGreatest_admissibleGaps_concrete.csSup_eq

#print axioms mass_finite_concrete
#print axioms clayMass_concrete

/-! ## The Yang–Mills witness: `m = ΔYMAt N β` -/

/-- The Yang–Mills theory's Hamiltonian is `-log diag(1, e^{-ΔYMAt N β})`. -/
theorem ymGapped_ham (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    (ymGapped N β hconf).ham
      = hamiltonian (diagOp (![1, Real.exp (-(ΔYMAt N β))] : Fin 2 → ℝ)) := rfl

/-- **`ΔYMAt N β` is attained in the spectrum of the reconstructed Yang–Mills Hamiltonian.** The
excited mode `e^{-Δ}` of the transfer datum maps to `-log e^{-Δ} = Δ`. This uses the reverse spectral
inclusion `lam_mem_spectrum_diagOp`; the vacuum-only lemma `one_mem_spectrum_diagOp` upstream cannot
supply it, because its `1` is what makes the vacuum, not an excited state. -/
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

/-- **`ΔYMAt N β` is the greatest admissible gap of the Yang–Mills witness.** -/
theorem isGreatest_admissibleGaps_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    IsGreatest (AdmissibleGaps (ymGapped N β hconf).ham) (ΔYMAt N β) :=
  isGreatest_admissibleGaps ((gap_pos_iff_confinement_at N β).mpr hconf)
    (ΔYM_mem_spectrum_ym N β hconf) (ym_spectral_gap N β hconf).2.2.2

/-- **Clay row B3 for the Yang–Mills witness: `m < ∞`.** The admissible gaps of the reconstructed
Hamiltonian are bounded above — by the entropy surplus itself. This is a statement about the
constructed two-mode transfer datum `diag(1, e^{-ΔYMAt N β})` that `ymGapped` builds, not about a
Wilson transfer operator; none exists in this development. -/
theorem mass_finite_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    BddAbove (AdmissibleGaps (ymGapped N β hconf).ham) :=
  (isGreatest_admissibleGaps_ym N β hconf).bddAbove

/-- **The Yang–Mills witness has mass exactly the entropy surplus: `m = ΔYMAt N β = κ₀YM - μYMAt N β`.**
The gap is bounded below by the surplus (the reconstruction) and above by it (the attained excited
state), so the two meet. -/
theorem clayMass_ym (N : ℕ) (β : ℝ) (hconf : μYMAt N β < κ₀YM) :
    clayMass (ymGapped N β hconf).ham = ΔYMAt N β :=
  (isGreatest_admissibleGaps_ym N β hconf).csSup_eq

#print axioms mass_finite_ym
#print axioms clayMass_ym

end MassGap.Reconstruction
