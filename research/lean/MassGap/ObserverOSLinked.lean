import Mathlib
import MassGap.ObserverOSEuclidS

noncomputable section

/-!
# MassGap.ObserverOSLinked — decaying monomials in the reconstructed Hilbert space

The observer's flowed reconstruction (`ContinuumFlow.flow_reconstruction`) builds the Hilbert space
`FlowH` from margin monomials with compactly supported test functions: `gvecT Q`, with
`⟪gvecT P, gvecT Q⟫ = S(θP ∪ Q)`. Here a margin monomial `P` of decaying functions
(`ObserverOSEuclidS.DMarginMono`, fields in `D`) gets a vector `vecD P`, the limit of the vectors of
its cut-offs `gvecT (cutM R P)`, and `⟪vecD P, vecD Q⟫ = schwSFM(θP ∪ Q)` (`inner_vecD`).

## Why the limit exists

`k(R, S) = S(θ cutM R P ∪ cutM S Q)`. For `R, S ≥ M` the families differ from the one at `M, M` by
cut-offs that agree on the ball of radius `M`, so the Lipschitz estimate
`ObserverOSEuclidS.abs_contSF_sub_le_M` gives `|k(R, S) − k(M, M)| ≤ b(M) → 0`
(`exists_kern_cauchy`). Then `‖gvecT (cutM R P) − gvecT (cutM M P)‖² = k(R,R) − 2k(R,M) + k(M,M)
≤ 3 b(M)`, the vectors are Cauchy (`cauchySeq_cutVec`), and `FlowH` is complete. The inner product
passes to the limit, and the kernel entries converge to `schwSFM` (`tendsto_schwSFM`).

## Compact monomials and density

A compactly supported margin monomial is a decaying one (`ofMarginD`), its cut-offs are eventually
itself, and `vecD (ofMarginD Q) = gvecT Q` (`vecD_ofMarginD`). Every `vecD P` is a limit of compact
vectors, so the closure of the decaying vectors equals the closure of the compact ones
(`closure_range_vecD`).

## `OSDataSLinked`

`OSDataSLinked` extends `OSDataS` by a Schwinger functional on families of fields and decaying
functions, a distinguished field with `S n φ = SM(O, …, O; φ ∘ toLp)`, a vector map of decaying margin
monomials into the Hilbert space with `⟪vec P, vec Q⟫ = SM(θP ∪ Q)`, the compact vectors, and the
closure identity. The type itself carries the link between the Hilbert space and the Schwinger
functions. `observerOSDataSLinked` inhabits it.
-/

namespace MassGap.ObserverOSLinked

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ObserverEnergyBox MassGap.ObserverOSEuclidS
  MassGap.ObserverOSReconstructionS MassGap.ContinuumTimeGroup Filter
open scoped Topology

/-! ## 1. Convergence of the kernel along cut-offs -/

section Kernel

variable {N : ℕ}

/-- The reflected pair of cut-off monomials at two radii.

DERIVED: no numeral. -/
theorem pairFam_cutM2 {τ : Fin 4} {r : ℝ} (R S : ℕ) (P Q : DMarginMono N τ r) :
    pairFam τ (cutM R P).1 (cutM S Q).1
      = fun x => (pairFields τ P.1 Q.1 x,
          cut (pairFuns τ P.1 Q.1 x) (Sum.elim (fun _ => R) (fun _ => S) x)) := by
  funext x
  cases x with
  | inl i =>
    refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
    show chi R (reflR τ y) * (P.1.2 i).2.1 (reflR τ y) = chi R y * (P.1.2 i).2.1 (reflR τ y)
    rw [chi_reflR]
  | inr j => rfl

#print axioms pairFam_cutM2

/-- **The kernel converges along the cut-offs, uniformly in two radii**: there is `b(M) → 0` with
`|k(R, S) − k(M, M)| ≤ b(M)` for `R, S ≥ M`.

DERIVED: `0` the limit; `5`, `6` the orders; `1` the shift; `8192` the gauge. -/
theorem exists_kern_cauchy (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {τ : Fin 4} {r : ℝ} (P Q : DMarginMono N τ r)
    (hPQ : ∀ x, pairFields τ P.1 Q.1 x ∈ D) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ M R S : ℕ, M ≤ R → M ≤ S →
      |kernF hN (energy0 W D hD) τ (cutM R P).1 (cutM S Q).1
        - kernF hN (energy0 W D hD) τ (cutM M P).1 (cutM M Q).1| ≤ b M := by
  classical
  have hex : ∀ x, ∃ B : ℝ, DecayBound 6 (pairFuns τ P.1 Q.1 x).1 B :=
    fun x => (pairFuns τ P.1 Q.1 x).2
  choose B hB using hex
  have hB5 : ∀ (S : ℕ) x, DecayBound 5 (cut (pairFuns τ P.1 Q.1 x) S).1 (B x) :=
    fun S x => decayBound_cut ((hB x).mono (by norm_num)) S
  refine ⟨fun M => (1 + Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1)
      * cN t C (Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1)))
      * ∑ a, 8192 * (0 + B a / ((M : ℝ) + 1)) * ∏ i ∈ Finset.univ \ {a}, 8192 * B i,
    tendsto_lip_bound _ B _ tendsto_const_nhds, fun M R S hMR hMS => ?_⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin P.1.1 ⊕ Fin Q.1.1 → ℕ, ρ = Sum.elim (fun _ => R) (fun _ => S) :=
    ⟨_, rfl⟩
  have hρM : ∀ x, M ≤ ρ x := by
    intro x
    cases x with
    | inl i => rw [hρ]; exact hMR
    | inr j => rw [hρ]; exact hMS
  show |contSF hN (energy0 W D hD) (pairFam τ (cutM R P).1 (cutM S Q).1)
    - contSF hN (energy0 W D hD) (pairFam τ (cutM M P).1 (cutM M Q).1)| ≤ _
  rw [pairFam_cutM2, pairFam_cutM, ← hρ]
  refine (abs_contSF_sub_le_M hN W hD hpos ht hC0 hU (pairFields τ P.1 Q.1) hPQ
    (fun x => cut (pairFuns τ P.1 Q.1 x) M) (fun x => cut (pairFuns τ P.1 Q.1 x) (ρ x)) B
    (fun x => B x / ((M : ℝ) + 1)) (fun x => hB5 M x) (fun x => hB5 (ρ x) x)
    (fun x y => ?_)).trans (le_of_eq ?_)
  · refine decayBound_of_vanish
      (h := fun y => chi (ρ x) y * (pairFuns τ P.1 Q.1 x).1 y - chi M y * (pairFuns τ P.1 Q.1 x).1 y)
      (hB x) (Nat.cast_nonneg M) (fun y hy => ?_) (fun y => ?_) y
    · have h1 := chi_eq_one hy
      have h2 : chi (ρ x) y = 1 := chi_eq_one (hy.trans (by exact_mod_cast hρM x))
      simp only [h1, h2, sub_self]
    · show |chi (ρ x) y * (pairFuns τ P.1 Q.1 x).1 y - chi M y * (pairFuns τ P.1 Q.1 x).1 y|
        ≤ |(pairFuns τ P.1 Q.1 x).1 y|
      rw [← sub_mul, abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith [chi_le_one (ρ x) y, chi_nonneg (ρ x) y, chi_le_one M y,
        chi_nonneg M y]
  · simp only [zero_add]

#print axioms exists_kern_cauchy

/-- **The kernel entries of the cut-offs converge to the extended kernel**:
`k(R, R) → schwSFM(θP ∪ Q) = kernS P Q`.

DERIVED: no numeral. -/
theorem tendsto_kernF_cutM (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W D t C) {τ : Fin 4} {r : ℝ} (P Q : DMarginMono N τ r)
    (hPQ : ∀ x, pairFields τ P.1 Q.1 x ∈ D) :
    Tendsto (fun R : ℕ => kernF hN (energy0 W D hD) τ (cutM R P).1 (cutM R Q).1) atTop
      (𝓝 (kernS hN W D hD τ P.1 Q.1)) := by
  refine (tendsto_schwSFM hN W hD hpos ht hC0 hU (pairFields τ P.1 Q.1) hPQ
    (pairFuns τ P.1 Q.1)).congr (fun R => ?_)
  show contSF hN (energy0 W D hD) (fun x => (pairFields τ P.1 Q.1 x, cut (pairFuns τ P.1 Q.1 x) R))
    = contSF hN (energy0 W D hD) (pairFam τ (cutM R P).1 (cutM R Q).1)
  rw [pairFam_cutM]
  rfl

#print axioms tendsto_kernF_cutM

end Kernel

/-! ## 2. The vectors -/

section Vectors

variable {N : ℕ}

/-- **Decaying margin monomials with fields in `D`.**

DERIVED: no numeral. -/
abbrev DMarginMonoD (N : ℕ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) : Type :=
  {P : DMarginMono N τ r // ∀ i, (P.1.2 i).1 ∈ D}

/-- **Compact margin monomials with fields in `D`.**

DERIVED: no numeral. -/
abbrev MarginMonoD (N : ℕ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) : Type :=
  {Q : MarginMono N τ r // ∀ i, (Q.1.2 i).1 ∈ D}

/-- The fields of a reflected pair of monomials with fields in `D` lie in `D`.

DERIVED: no numeral. -/
theorem pairFields_mem {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4}
    {r : ℝ} (P Q : DMarginMonoD N D τ r) (x : Fin P.1.1.1 ⊕ Fin Q.1.1.1) :
    pairFields τ P.1.1 Q.1.1 x ∈ D := by
  cases x with
  | inl i => exact (hD τ _).mpr (P.2 i)
  | inr j => exact Q.2 j

#print axioms pairFields_mem

/-- The reconstruction reads the kernel on compact margin monomials
(`ContinuumFlow.flow_reconstruction` at step `0`).

DERIVED: `0` the reference step. -/
theorem inner_gvecT_eq (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpp : Φ.PosPreserving τ r) (A B : MarginMono N τ r) :
    inner ℂ (gvecT hN Φ hB τ hpp A) (gvecT hN Φ hB τ hpp B) = (kernF hN Φ τ A.1 B.1 : ℂ) :=
  (flow_reconstruction hN Φ hB τ hpp 0).2 A B

#print axioms inner_gvecT_eq

/-- **The vectors of the cut-offs are Cauchy**: `‖gvecT (cutM R P) − gvecT (cutM M P)‖² ≤ 3 b(M)` for
`R ≥ M`.

DERIVED: `2` the square and the cross term; `3` collects the three kernel differences; `0` the
sign of `ε`. -/
theorem cauchySeq_cutVec (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) (P : DMarginMonoD N D τ r) :
    CauchySeq (fun R : ℕ => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
      τ (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) (cutM R P.1)) := by
  obtain ⟨b, hb, hbd⟩ := exists_kern_cauchy hN W hD hpos ht hC0 hU P.1 P.1
    (pairFields_mem hD P P)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hε2 : (3 : ℝ) * 0 < ε ^ 2 := by rw [mul_zero]; positivity
  obtain ⟨M, hM⟩ := ((hb.const_mul 3).eventually (gt_mem_nhds hε2)).exists_forall_of_atTop
  refine ⟨M, fun R hR => ?_⟩
  rw [dist_eq_norm]
  set u := fun S : ℕ => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
    (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) (cutM S P.1) with hudef
  have hin : ∀ S S' : ℕ, inner ℂ (u S) (u S')
      = (kernF hN (energy0 W D hD) τ (cutM S P.1).1 (cutM S' P.1).1 : ℂ) := fun S S' =>
    inner_gvecT_eq hN _ _ τ _ _ _
  have e : ‖u R - u M‖ ^ 2 = kernF hN (energy0 W D hD) τ (cutM R P.1).1 (cutM R P.1).1
      - 2 * kernF hN (energy0 W D hD) τ (cutM R P.1).1 (cutM M P.1).1
      + kernF hN (energy0 W D hD) τ (cutM M P.1).1 (cutM M P.1).1 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      hin, hin, hin]
    simp
  have h1 := hbd M R R hR hR
  have h2 := hbd M R M hR le_rfl
  have hsq : ‖u R - u M‖ ^ 2 ≤ 3 * b M := by
    rw [e]
    rw [abs_le] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hsq.trans_lt (hM M le_rfl))

#print axioms cauchySeq_cutVec

/-- **The vector of a decaying margin monomial**: the limit of the vectors of its cut-offs.

DERIVED: no numeral. -/
def vecD (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (P : DMarginMonoD N D τ r) :
    FlowH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
      (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) :=
  limUnder atTop (fun R : ℕ => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
    τ (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) (cutM R P.1))

/-- DERIVED: no numeral. -/
theorem tendsto_vecD (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) (P : DMarginMonoD N D τ r) :
    Tendsto (fun R : ℕ => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
      τ (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) (cutM R P.1)) atTop
      (𝓝 (vecD hN W hD hpos hcube τ hphys P)) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_cutVec hN W hD hpos hcube ht hC0 hU τ hphys P)
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_vecD

/-- **The reconstruction reads the extended kernel**: `⟪vecD P, vecD Q⟫ = schwSFM(θP ∪ Q)`.

DERIVED: no numeral. -/
theorem inner_vecD (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) (P Q : DMarginMonoD N D τ r) :
    inner ℂ (vecD hN W hD hpos hcube τ hphys P) (vecD hN W hD hpos hcube τ hphys Q)
      = (kernS hN W D hD τ P.1.1 Q.1.1 : ℂ) := by
  have hT := (tendsto_vecD hN W hD hpos hcube ht hC0 hU τ hphys P).inner
    (tendsto_vecD hN W hD hpos hcube ht hC0 hU τ hphys Q) (𝕜 := ℂ)
  have hK := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_kernF_cutM hN W hD hpos ht hC0 hU P.1 Q.1 (pairFields_mem hD P Q))
  refine tendsto_nhds_unique hT (hK.congr (fun R => ?_))
  exact (inner_gvecT_eq hN _ _ τ _ _ _).symm

#print axioms inner_vecD

end Vectors

/-! ## 3. Compact monomials and density -/

section Compact

variable {N : ℕ}

/-- A test function supported in `[-R, R]⁴` with `|f| ≤ M` has `‖f‖₆ ≤ (1 + R)⁶ M`.

DERIVED: `6` the order; `1` the weight's unit term; `0` the vanishing value. -/
theorem decayBound6_of_isTest {f : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (h : IsTest f R M) :
    DecayBound 6 f ((1 + R) ^ 6 * M) := by
  intro y
  have hR := h.1
  have hM := h.M_nonneg
  have hy0 := norm_nonneg y
  by_cases h0 : f y = 0
  · rw [h0, abs_zero, mul_zero]
    exact mul_nonneg (pow_nonneg (by linarith) 6) hM
  · have hy : ‖y‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr
      (fun i => by rw [Real.norm_eq_abs]; exact h.2.2 y h0 i)
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 6) (h.2.1 y) (abs_nonneg _)
      (pow_nonneg (by linarith) 6)

#print axioms decayBound6_of_isTest

/-- A test function as a decaying function.

DERIVED: `6` the order. -/
def decOfTest (f : TestFn) : Decaying :=
  ⟨f.1, by
    obtain ⟨R, M, h⟩ := f.2
    exact ⟨_, decayBound6_of_isTest h⟩⟩

/-- **A compact margin monomial as a decaying one.**

DERIVED: no numeral. -/
def ofMarginD {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ} (Q : MarginMonoD N D τ r) :
    DMarginMonoD N D τ r :=
  ⟨⟨⟨Q.1.1.1, fun i => ((Q.1.1.2 i).1, decOfTest (Q.1.1.2 i).2)⟩, by
      obtain ⟨d, hd, hrd, hQ⟩ := Q.1.2
      exact ⟨d, hd, hrd, fun i y hy => hQ i y hy⟩⟩, Q.2⟩

/-- **The cut-offs of a compact monomial are eventually the monomial itself.**

DERIVED: `1` the cut-off on the ball. -/
theorem eventually_cutM_ofMarginD {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (Q : MarginMonoD N D τ r) : ∀ᶠ R : ℕ in atTop, cutM R (ofMarginD Q).1 = Q.1 := by
  have hex : ∀ i, ∃ R M : ℝ, IsTest (Q.1.1.2 i).2.1 R M := fun i => (Q.1.1.2 i).2.2
  choose R0 M hRM using hex
  filter_upwards [Filter.eventually_ge_atTop ⌈∑ i, R0 i⌉₊] with R hR
  refine Subtype.ext (Sigma.ext rfl (heq_of_eq (funext (fun i => ?_))))
  refine Prod.ext rfl (Subtype.ext (funext (fun y => ?_)))
  show chi R y * (Q.1.1.2 i).2.1 y = (Q.1.1.2 i).2.1 y
  by_cases h0 : (Q.1.1.2 i).2.1 y = 0
  · rw [h0, mul_zero]
  · have hy : ‖y‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg R)).mpr (fun j => ?_)
      rw [Real.norm_eq_abs]
      have h1 := (hRM i).2.2 y h0 j
      have h2 : R0 i ≤ ∑ i, R0 i :=
        Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
      have h3 : ∑ i, R0 i ≤ (⌈∑ i, R0 i⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : (⌈∑ i, R0 i⌉₊ : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    rw [chi_eq_one hy, one_mul]

#print axioms eventually_cutM_ofMarginD

/-- **A compact monomial's vector is its reconstructed vector**: `vecD (ofMarginD Q) = gvecT Q`.

DERIVED: no numeral. -/
theorem vecD_ofMarginD (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) (Q : MarginMonoD N D τ r) :
    vecD hN W hD hpos hcube τ hphys (ofMarginD Q)
      = gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
          (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) Q.1 :=
  tendsto_nhds_unique (tendsto_vecD hN W hD hpos hcube ht hC0 hU τ hphys (ofMarginD Q))
    (tendsto_const_nhds.congr' ((eventually_cutM_ofMarginD Q).mono (fun R hR =>
      (congrArg (gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) hR).symm)))

#print axioms vecD_ofMarginD

/-- **The decaying vectors and the compact vectors have the same closure.**

DERIVED: no numeral. -/
theorem closure_range_vecD (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4) {r : ℝ}
    (hphys : (energy0 W D hD).PhysRange r) :
    closure (Set.range (vecD hN W hD hpos hcube τ hphys))
      = closure (Set.range (fun Q : MarginMonoD N D τ r =>
          gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
            (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) Q.1)) := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨P, rfl⟩
    refine mem_closure_of_tendsto (tendsto_vecD hN W hD hpos hcube ht hC0 hU τ hphys P)
      (Eventually.of_forall (fun R => ⟨⟨cutM R P.1, fun i => P.2 i⟩, rfl⟩))
  · rintro _ ⟨Q, rfl⟩
    exact ⟨ofMarginD Q, vecD_ofMarginD hN W hD hpos hcube ht hC0 hU τ hphys Q⟩

#print axioms closure_range_vecD

end Compact

/-! ## 4. The linked structure -/

/-- DERIVED: no numeral. -/
instance instNormedAddCommGroupOSDataSH (X : OSDataS) : NormedAddCommGroup X.H := X.nH

/-- DERIVED: no numeral. -/
instance instInnerProductSpaceOSDataSH (X : OSDataS) : InnerProductSpace ℂ X.H := X.iH

/-- **Schwartz-indexed Euclidean data linked to their reconstruction.** An `OSDataS`, a Schwinger
functional `SM` on families of fields and decaying functions, a field `O` with
`S n φ = SM(O, …, O; φ ∘ toLp)`, a vector map of decaying margin monomials with fields in `D` into
the Hilbert space whose inner products are `SM` on the reflected pairs, the compact vectors `cvec`,
with `vec ∘ ofMarginD = cvec` and the two images of equal closure.

DERIVED: `2` the Euclidean exponent; `4` in `Fin 4` is the spacetime dimension. -/
structure OSDataSLinked (N : ℕ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) where
  /-- The Euclidean data and the reconstructed space. -/
  base : OSDataS
  /-- The Schwinger functional on families of fields and decaying functions. -/
  SM : {ι : Type} → [Fintype ι] → (ι → LField (MassGap.SUN.SU N)) → (ι → Decaying) → ℝ
  /-- The field of the Schwartz-class Schwinger functions. -/
  O : LField (MassGap.SUN.SU N)
  /-- The Schwartz-class Schwinger functions are `SM` at the field `O`. -/
  S_eq : ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
    base.S n φ = SM (fun _ : Fin n => O) (fun i => ofE4 (φ i))
  /-- The vectors of decaying margin monomials. -/
  vec : DMarginMonoD N D τ r → base.H
  /-- **The link**: the inner products are the Schwinger functional on the reflected pairs. -/
  inner_vec : ∀ P Q : DMarginMonoD N D τ r,
    inner ℂ (vec P) (vec Q) = (SM (pairFields τ P.1.1 Q.1.1) (pairFuns τ P.1.1 Q.1.1) : ℂ)
  /-- The vectors of compact margin monomials. -/
  cvec : MarginMonoD N D τ r → base.H
  /-- A compact monomial's vector is its compact vector. -/
  vec_compact : ∀ Q : MarginMonoD N D τ r, vec (ofMarginD Q) = cvec Q
  /-- The decaying vectors and the compact vectors have the same closure. -/
  closure_eq : closure (Set.range vec) = closure (Set.range cvec)

section Observer

variable {N : ℕ}

/-- **The observer inhabits `OSDataSLinked`.** Inputs: those of `observerOSDataS` and the class
moments. `SM = schwSFM`, `vec = vecD`, `cvec = gvecT`.

DERIVED: `0` the excluded colour count, the signs and the reference step; `1` the top of `ρ`; `4` in
`Fin 4` the spacetime dimension. -/
def observerOSDataSLinked (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) : OSDataSLinked N D τ r where
  base := observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT
  SM := fun O g => schwSFM hN W D hD O g
  O := O
  S_eq := fun n φ => by
    show schwCML hN W hD hpos hO h n φ = schwSFM hN W D hD (fun _ : Fin n => O) (fun i => ofE4 (φ i))
    rw [schwCML_apply]
    exact schwSF_eq_schwSFM hN W hD hpos ht hC0 hU hO _
  vec := vecD hN W hD hpos hcube τ hphys
  inner_vec := inner_vecD hN W hD hpos hcube ht hC0 hU τ hphys
  cvec := fun Q => gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
    (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) Q.1
  vec_compact := vecD_ofMarginD hN W hD hpos hcube ht hC0 hU τ hphys
  closure_eq := closure_range_vecD hN W hD hpos hcube ht hC0 hU τ hphys

/-- The observer's linked data: the inner products of the decaying vectors are the observer's
extended Schwinger functions of the reflected pairs.

DERIVED: no numeral. -/
theorem observerOSDataSLinked_inner (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) (P Q : DMarginMonoD N D τ r) :
    let X := observerOSDataSLinked hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT
    inner ℂ (X.vec P) (X.vec Q) = (kernS hN W D hD τ P.1.1 Q.1.1 : ℂ) :=
  (observerOSDataSLinked hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT).inner_vec P Q

#print axioms observerOSDataSLinked_inner

end Observer

end MassGap.ObserverOSLinked
