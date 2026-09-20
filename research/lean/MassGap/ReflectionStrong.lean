import Mathlib
import MassGap.LogConvex
import MassGap.OddLagSplit

/-!
# MassGap.ReflectionStrong — reflection positivity as a quadratic form on the half-space ALGEBRA

The strongest reflection-positivity statement this development supports, on the genuine Wilson
measure, and the corollary chain that shows it IMPLIES the one-plaquette statement the rest of the
tree consumes.

## The statement

At a lattice of even extent `n = 2m`, for every axis `τ`, every plane position `a`, and **every real
coupling `β` with no sign condition**:

    0 ≤ ⟨ F · (F ∘ Θ) ⟩,    Θ = Reflect.reflConf τ (a + a),

for EVERY `F` in `LogConvex.localObs (blkS τ a m) (blkR τ a m)` — every bounded measurable observable
determined by the link variables of the slab `blkS` together with the two fixed planes `blkR`. That
is `wilson_expect_nonneg_module`. The Gram form of it, `wilson_expect_gram_nonneg`, is the same
statement for an arbitrary finite family and arbitrary real coefficients: the Gram matrix
`G_ij = ⟨F_i · (F_j ∘ Θ)⟩` is positive semidefinite.

`localObs` is closed under products (`mul_mem_localObs`) as well as under linear combination, so the
set the Gram matrix ranges over is a unital subalgebra, not merely a subspace.

## What this is NOT — it is not OS3

Osterwalder–Schrader positivity is positive semidefiniteness of `⟨θF̄ · F⟩` over the algebra of all
observables supported in the positive-time half-space of the INFINITE-VOLUME CONTINUUM Euclidean
measure. Six things separate the statement here from that one, and none of them is cosmetic.

1. **Finite volume, finite lattice spacing, no limit.** Everything here is the periodic `SU(N)`
   Wilson lattice at a fixed extent `n = 2m`. No thermodynamic limit and no continuum limit exists
   anywhere in this development, so no statement here is about a continuum measure.

2. **A SLAB, not a half-space.** `ActionSplit.blkS τ a m` is the links strictly between the plane at
   level `0` and the plane at level `m`, and `blkR` is the two planes themselves. On a periodic
   lattice there is no half-space: the region the algebra reads is bounded ABOVE by the second
   reflection plane as well as below by the first. The algebra is the slab algebra.

3. **Real, not complex.** The form is `ℝ`-bilinear on real observables. OS3 is sesquilinear on
   complex observables; conjugation does not appear here.

4. **One family of reflections.** `Θ = reflConf τ (a + a)` is the SITE reflection — reflection
   constant even. The LINK reflections (`reflConf τ (a + a + 1)`, constant odd) are not covered by
   anything in this file; they are `OddLagSplit`'s, they use a different three-block decomposition,
   and they genuinely need `0 ≤ β` (see the section on the coupling below).

5. **Positivity only.** Regularity, Euclidean invariance and ergodicity — the other
   Osterwalder–Schrader axioms — are not addressed.

6. **No time translation.** OS3 is useful because positivity plus a time shift reconstructs a
   Hilbert space with a self-adjoint contraction on it. The shift is absent; see the last section.

## What is new here relative to `LogConvex`

`LogConvex.pairing_nonneg` is positivity of the SPLIT pairing `∫ wPlane · F · (F ∘ Θ)`, in which the
half-space Boltzmann factors have been absorbed into the observables by hand. That is the object
Cauchy–Schwarz was run on there. What is added here is the passage back to the GIBBS state: the map
`F ↦ F · e^{−β·actPlus}` is a linear self-map of `localObs` (`dressed_mem`), and it turns the split
pairing into the Gibbs expectation (`corrNum_refl_eq_pairing`). So the inequality can be stated about
`⟨F · (F ∘ Θ)⟩` — the physical two-point function — rather than about an auxiliary integral.

## The coupling's sign: what can be lifted and what cannot

`Complete.wilson_reflection_positive_at_even` carries `0 ≤ β`. That hypothesis is NOT removable, and
the reason is visible in exactly one place: the ODD lags. `corrClay_nonneg_even_lag` below is the
even-lag half at EVERY real `β`, and `corrClay_even_sum_pos` is its positive-mass companion, also at
every real `β`. The odd lags go through `OddLagSplit.odd_crossing_integral_nonneg`, whose integrand
is the cross kernel `exp(β · hsRe A B)`, and
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` proves that kernel positive semidefinite on two
explicit `SU(3)` elements IF AND ONLY IF `0 ≤ β`.

There is no contradiction between that IFF and the sign-free statement here, because the two are
about different objects. The site reflection used here never forms a cross kernel at all: the plane
weight `wPlane` factors out of the integral and what remains is a conditional square against a
strictly positive Boltzmann weight, which reads no sign. The link reflection inverts the gauge
variable on the fixed axis link, the plane cannot be conditioned on, and the straddling factor
survives as the kernel the negative control refutes at `β < 0`.

## The transfer operator

`wilsonGibbsReflForm` is a `Transfer.ReflForm` built on `Transfer.reflForm` itself — the concrete
Gibbs reflection form that file defines — with `form_nonneg` proved rather than assumed, and
`wilsonGibbsReflForm_vac_norm` supplies `TransferData.vac_norm`. That is the `ReflForm` parent and
one of the four extra fields of `Transfer.TransferData`.

It does not finish the construction, and the missing piece is structural rather than unproved. A
`TransferData` needs `T : A →ₗ[ℝ] A`, a time translation that is an ENDOMORPHISM of the algebra. One
lattice step along `τ` sends a transverse link at level `m` — which is in `blkR`, inside the algebra
— to level `m + 1`, which is in `blkT` and outside it. So the one-step shift does not map
`localObs (blkS τ a m) (blkR τ a m)` into itself, and `T_symm`, `T_contract` and `T_vac` cannot even
be stated on this module. That is point 2 above: a slab of width `m` is not a half-line, and a
transfer operator wants a half-line.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.ReflectionStrong`.
-/

namespace MassGap.ReflectionStrong

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity
open MassGap.WilsonLattice MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonAction
open MassGap.ActionSplit MassGap.ReflectPositive MassGap.WilsonBridge MassGap.LogConvex

/-! ## Part 1 — `localObs` is an ALGEBRA, not merely a module

`LogConvex.localObs` is built as a `Submodule`, so linear combinations were already available. The
three defining clauses are each stable under multiplication too — measurability, a product of bounds,
and reading the same block — so the set the Gram matrix below ranges over is a unital subalgebra.
This is what makes the statement "positive semidefinite over the half-space ALGEBRA" rather than
"over a subspace of observables".
-/

section Algebra

variable {ι : Type} {Ω : Type} [MeasurableSpace Ω]

/-- **THE MODULE IS CLOSED UNDER PRODUCTS.** Measurability multiplies, the bounds multiply, and two
observables reading `S ∪ R` have a product reading `S ∪ R`.

DERIVED: no numeral. `CF * CG` is read off the operation, exactly as `LogConvex.localObs`'s own
`add_mem'` reads `CF + CG`. -/
theorem mul_mem_localObs {S R : Finset ι} {F G : (ι → Ω) → ℝ}
    (hF : F ∈ localObs S R) (hG : G ∈ localObs S R) :
    (fun U => F U * G U) ∈ localObs S R := by
  obtain ⟨hFm, ⟨CF, hFb⟩, hFl⟩ := hF
  obtain ⟨hGm, ⟨CG, hGb⟩, hGl⟩ := hG
  refine mem_localObs.mpr ⟨hFm.mul hGm, ⟨CF * CG, fun U => ?_⟩, fun U V hS hR => ?_⟩
  · show |F U * G U| ≤ CF * CG
    rw [abs_mul]
    exact mul_le_mul (hFb U) (hGb U) (abs_nonneg _) (le_trans (abs_nonneg _) (hFb U))
  · show F U * G U = F V * G V
    rw [hFl U V hS hR, hGl U V hS hR]

/-- **THE CONSTANT OBSERVABLE IS IN THE MODULE**, which makes the subalgebra unital and supplies the
vacuum vector a transfer construction would need.

DERIVED: the `1`s are the constant observable's own value and its own bound. -/
theorem one_mem_localObs {S R : Finset ι} :
    (fun _ : ι → Ω => (1 : ℝ)) ∈ localObs S R :=
  mem_localObs.mpr ⟨measurable_const, ⟨1, fun _ => by norm_num⟩, fun _ _ _ _ => rfl⟩

end Algebra

/-! ## Part 2 — the half-space Boltzmann factor is an observable of the half-space

The split pairing of `LogConvex` carries only the PLANE weight `wPlane`; the two half-space
Boltzmann factors were absorbed into `obsPlus` by hand, one plaquette at a time. Naming the factor
and proving it a member of the module is what lets the absorption be done for an ARBITRARY observable
rather than for the single plaquette energy.
-/

section Dress

variable {d n N : ℕ} [NeZero n]

/-- **The Boltzmann factor of the positive half.** `ActionSplit.obsPlus` is the plaquette energy
times exactly this.

DERIVED: no numeral; `τ`, `a`, `m` and `β` are the caller's. -/
noncomputable def halfBoltz (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-β * actPlus τ a m U)

/-- **An observable DRESSED by the half-space Boltzmann factor.** This is the map that carries the
Gibbs pairing to the split pairing. It is linear in `F`, which is what makes the Gram statement
transfer between the two. -/
noncomputable def dressed (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) : (Link d n → MassGap.SUN.SU N) → ℝ :=
  fun U => F U * halfBoltz τ a m β U

/-- **The half-space action READS `S ∪ R`.** This is the step inside `ActionSplit.obsPlus_local`
that concerns the action rather than the plaquette, extracted so that it can be used at an arbitrary
observable. -/
theorem actPlus_local (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    (U V : Link d n → MassGap.SUN.SU N)
    (hS : ∀ l ∈ blkS τ a m, U l = V l) (hR : ∀ l ∈ blkR τ a m, U l = V l) :
    actPlus (N := N) τ a m U = actPlus τ a m V := by
  have hUV : ∀ l ∈ blkS τ a m ∪ blkR τ a m, U l = V l := by
    intro l hl
    rcases Finset.mem_union.mp hl with h | h
    · exact hS l h
    · exact hR l h
  exact action_on_congr_of_support (bd (d := d) (n := n)) (wilsonDensity (N := N))
    (plqPlus τ a m) (blkS τ a m ∪ blkR τ a m)
    (fun p hp => plaq_links_le τ a m hm hm0 ((mem_plqPlus τ a m p).mp hp).1
      ((mem_plqPlus τ a m p).mp hp).2.2) U V hUV

/-- **THE HALF-SPACE BOLTZMANN FACTOR IS AN OBSERVABLE OF THE HALF-SPACE.**

DERIVED: the `2` is the range of the Wilson density and the cardinality is the half-space's own
plaquette count, both `ActionSplit.abs_exp_actSum_le`'s. -/
theorem halfBoltz_mem (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    halfBoltz (N := N) τ a m β ∈ localObs (blkS τ a m) (blkR τ a m) := by
  refine mem_localObs.mpr ⟨?_, ⟨Real.exp (|β| * (2 * ((plqPlus (d := d) (n := n) τ a m).card : ℝ))),
    ?_⟩, fun U V hS hR => ?_⟩
  · unfold halfBoltz actPlus
    exact Real.measurable_exp.comp ((measurable_actSum _).const_mul _)
  · intro U
    unfold halfBoltz actPlus
    exact abs_exp_actSum_le hN β _ U
  · show Real.exp (-β * actPlus τ a m U) = Real.exp (-β * actPlus τ a m V)
    rw [actPlus_local τ a m hm hm0 U V hS hR]

/-- **THE DRESSED OBSERVABLE IS STILL AN OBSERVABLE OF THE HALF-SPACE.** -/
theorem dressed_mem (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    dressed τ a m β F ∈ localObs (blkS τ a m) (blkR τ a m) :=
  mul_mem_localObs hF (halfBoltz_mem hN τ a m hm hm0 β)

/-- Dressing is additive. -/
theorem dressed_add (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    dressed τ a m β (F + G) = dressed τ a m β F + dressed τ a m β G := by
  funext U
  show (F U + G U) * halfBoltz τ a m β U
    = F U * halfBoltz τ a m β U + G U * halfBoltz τ a m β U
  ring

/-- Dressing is homogeneous. -/
theorem dressed_smul (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ) (r : ℝ)
    (F : (Link d n → MassGap.SUN.SU N) → ℝ) :
    dressed τ a m β (r • F) = r • dressed τ a m β F := by
  funext U
  show (r * F U) * halfBoltz τ a m β U = r * (F U * halfBoltz τ a m β U)
  ring

end Dress

/-! ## Part 3 — the factorisation, for an ARBITRARY pair of observables

`LogConvex.integrand_eq_paired_pair` is this identity at two PLAQUETTE observables. Nothing in its
proof reads the observable: the mirror identity `actPlus ∘ Θ = actMinus` is a statement about the
action alone. Rerun with two arbitrary functions and the dressing named.
-/

section Factor

variable {d n N : ℕ} [NeZero n]

/-- **THE FACTORISATION, AT ARBITRARY OBSERVABLES.** The full Gibbs weight splits into the plane
weight times the two dressings, one of them carried through the reflection.

DERIVED: no numeral. -/
theorem integrand_eq_paired_obs (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (F G : (Link d n → MassGap.SUN.SU N) → ℝ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    F U * G (reflConf τ (a + a) U) * (sysWilson N d n).boltz β U
      = wPlane τ a m β U * dressed τ a m β F U
          * dressed τ a m β G (reflConf τ (a + a) U) := by
  have hmir : actPlus τ a m (reflConf τ (a + a) U) = actMinus (N := N) τ a m U :=
    (sum_plqMinus_eq_plus_refl τ a m hm hm0 U).symm
  show F U * G (reflConf τ (a + a) U) * Real.exp (-β * (sysWilson N d n).action U) = _
  rw [action_eq_split τ a m hN U]
  unfold wPlane dressed halfBoltz
  rw [hmir]
  rw [show -β * (actPlus τ a m U + actMinus τ a m U + actZero τ a m U)
      = (-β * actZero τ a m U) + ((-β * actPlus τ a m U) + (-β * actMinus τ a m U)) by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **THE GIBBS NUMERATOR IS THE SPLIT PAIRING OF THE DRESSED OBSERVABLES.**

This is the bridge the rest of the file runs on. No membership hypothesis is needed: it is the
pointwise identity above, integrated. -/
theorem corrNum_refl_eq_pairing (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
        (fun U => F U * G (reflConf τ (a + a) U))
      = pairing τ a m β (dressed τ a m β F) (dressed τ a m β G) := by
  symm
  show (∫ U, wPlane τ a m β U * dressed τ a m β F U
          * dressed τ a m β G (reflConf τ (a + a) U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
    = ∫ U, (F U * G (reflConf τ (a + a) U)) * (sysWilson N d n).boltz β U
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  exact (integrand_eq_paired_obs hN τ a m hm hm0 F G β U).symm

end Factor

/-! ## Part 4 — REFLECTION POSITIVITY ON THE GIBBS STATE, over the whole half-space algebra -/

section Positive

variable {d n N : ℕ} [NeZero n]

/-- **THE UNNORMALISED FORM IS NONNEGATIVE ON THE DIAGONAL, FOR EVERY OBSERVABLE OF THE SLAB
ALGEBRA, AT EVERY REAL COUPLING.**

DERIVED: the `0` of `0 ≤ …` IS positive semidefiniteness — the property, not a threshold. The `2` in
`n = 2 * m` is the reflection geometry's: a reflection plane and its opposite are half the extent
apart. -/
theorem wilson_pairing_nonneg_module (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    0 ≤ (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
      (fun U => F U * F (reflConf τ (a + a) U)) := by
  rw [corrNum_refl_eq_pairing hN τ a m hm hm0 β F F]
  exact pairing_nonneg hN τ a m hm hm0 β (dressed_mem hN τ a m hm hm0 β hF)

/-- **REFLECTION POSITIVITY OF THE WILSON GIBBS STATE, OVER THE HALF-SPACE ALGEBRA, AT EVERY REAL
COUPLING.**

`0 ≤ ⟨F · (F ∘ Θ)⟩` for every bounded measurable `F` determined by the slab `blkS τ a m` together
with the two fixed planes `blkR τ a m`, at the site reflection `Θ = reflConf τ (a + a)`, with NO sign
condition on `β`.

This is the strongest form of reflection positivity in the tree. What separates it from OS3 is set
out in the module docstring; the short version is that it is one site reflection of a finite periodic
lattice, real-linear, on a slab rather than a half-space, with no limit taken. -/
theorem wilson_expect_nonneg_module (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    0 ≤ EW N β (fun U => F U * F (reflConf τ (a + a) U)) := by
  have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
    wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  show 0 ≤ (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
      (fun U => F U * F (reflConf τ (a + a) U))
    / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β
  exact div_nonneg (wilson_pairing_nonneg_module hN τ a m hm hm0 β hF) (le_of_lt hZ)

end Positive

/-! ## Part 5 — the GRAM MATRIX

Positivity on the diagonal plus bilinearity is positive semidefiniteness of the whole Gram matrix,
because the module is closed under the linear combinations the quadratic form is taken over. Stated
for an arbitrary finite family and arbitrary real coefficients, which is the shape OS3 is stated in.
-/

section Gram

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **A symmetric bilinear form on a finite linear combination, left slot.** -/
theorem form_sum_left (P : MassGap.Transfer.PreForm A) {ι : Type*} (c : ι → ℝ) (x : ι → A) (y : A)
    (s : Finset ι) :
    P.form (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * P.form (x i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact P.form_zero_left y
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, P.form_add_left, P.form_smul_left, ih]

/-- **The quadratic form of a finite linear combination IS the Gram sum.** -/
theorem form_sum_sum (P : MassGap.Transfer.PreForm A) {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (x : ι → A) :
    P.form (∑ i, c i • x i) (∑ j, c j • x j)
      = ∑ i, ∑ j, c i * c j * P.form (x i) (x j) := by
  rw [form_sum_left P c x _ Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [P.form_symm (x i) (∑ j, c j • x j), form_sum_left P c x (x i) Finset.univ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [P.form_symm (x j) (x i)]
  ring

end Gram

section GramWilson

variable {d n N : ℕ} [NeZero n]

/-- **THE SPLIT PAIRING'S GRAM MATRIX IS POSITIVE SEMIDEFINITE.**

DERIVED: the `0` of `0 ≤ …` is positive semidefiniteness itself. -/
theorem pairing_gram_nonneg (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) {ι : Type} [Fintype ι]
    (F : ι → (Link d n → MassGap.SUN.SU N) → ℝ)
    (hF : ∀ i, F i ∈ localObs (blkS τ a m) (blkR τ a m)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * pairing τ a m β (F i) (F j) := by
  have h := (wilsonReflForm hN τ a m hm hm0 β).form_nonneg
    (∑ i, c i • (⟨F i, hF i⟩ :
      ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m))))
  exact le_of_le_of_eq h
    (form_sum_sum (wilsonReflForm hN τ a m hm hm0 β).toPreForm c
      (fun i => (⟨F i, hF i⟩ :
        ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m)))))

/-- **THE GIBBS REFLECTION FORM'S GRAM MATRIX IS POSITIVE SEMIDEFINITE, AT EVERY REAL COUPLING.**

`0 ≤ Σ_ij c_i c_j ⟨F_i · (F_j ∘ Θ)⟩` for every finite family of observables of the slab algebra and
every family of real coefficients. This is reflection positivity in the form OS3 states it — as a
statement about a matrix rather than about one observable — restricted to the slab algebra of a
finite periodic lattice at one site reflection. -/
theorem wilson_expect_gram_nonneg (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) {ι : Type} [Fintype ι]
    (F : ι → (Link d n → MassGap.SUN.SU N) → ℝ)
    (hF : ∀ i, F i ∈ localObs (blkS τ a m) (blkR τ a m)) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j
        * EW N β (fun U => F i U * F j (reflConf τ (a + a) U)) := by
  have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
    wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  have hsum : (∑ i, ∑ j, c i * c j
        * EW N β (fun U => F i U * F j (reflConf τ (a + a) U)))
      = (∑ i, ∑ j, c i * c j
          * pairing τ a m β (dressed τ a m β (F i)) (dressed τ a m β (F j)))
        / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show c i * c j * ((sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
        (fun U => F i U * F j (reflConf τ (a + a) U))
      / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β) = _
    rw [corrNum_refl_eq_pairing hN τ a m hm hm0 β (F i) (F j)]
    ring
  rw [hsum]
  exact div_nonneg
    (pairing_gram_nonneg hN τ a m hm hm0 β (fun i => dressed τ a m β (F i))
      (fun i => dressed_mem hN τ a m hm hm0 β (hF i)) c) (le_of_lt hZ)

end GramWilson

/-! ## Part 6 — `Transfer.reflForm` itself carries a `ReflForm`

`Transfer`'s own header says no `ReflForm` can be built from the Wilson measure until the reflection
positivity axiom is discharged. `LogConvex.wilsonReflForm` already built one on the SPLIT pairing;
this one is built on `Transfer.reflForm` — the file's own concrete Gibbs form — restricted to the
slab algebra. Its `form_nonneg` is `wilson_expect_nonneg_module`, proved, at every real `β`.
-/

section GibbsForm

variable {d n N : ℕ} [NeZero n]

/-- The reflection form of `Transfer`, as the split pairing of the dressed observables over `Z`. -/
theorem reflForm_eq_pairing (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    MassGap.Transfer.reflForm N τ (a + a) β F G
      = pairing τ a m β (dressed τ a m β G) (dressed τ a m β F)
        / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
  calc MassGap.Transfer.reflForm N τ (a + a) β F G
      = (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
            (fun U => G U * F (reflConf τ (a + a) U))
          / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
        MassGap.Transfer.expect_congr N β (fun U => mul_comm _ _)
    _ = pairing τ a m β (dressed τ a m β G) (dressed τ a m β F)
          / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
        congrArg
          (fun x : ℝ => x / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β)
          (corrNum_refl_eq_pairing hN τ a m hm hm0 β G F)

/-- Additivity of the split pairing in the RIGHT slot, from symmetry. -/
theorem pairing_add_right (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (β : ℝ)
    {F₁ F₂ G : (Link d n → MassGap.SUN.SU N) → ℝ}
    (h₁ : F₁ ∈ localObs (blkS τ a m) (blkR τ a m))
    (h₂ : F₂ ∈ localObs (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObs (blkS τ a m) (blkR τ a m)) :
    pairing τ a m β G (F₁ + F₂) = pairing τ a m β G F₁ + pairing τ a m β G F₂ := by
  rw [pairing_symm τ a m hm β hG ((localObs (blkS τ a m) (blkR τ a m)).add_mem h₁ h₂),
    pairing_add_left hN τ a m β h₁ h₂ hG,
    pairing_symm τ a m hm β h₁ hG, pairing_symm τ a m hm β h₂ hG]

/-- Homogeneity of the split pairing in the RIGHT slot, from symmetry. -/
theorem pairing_smul_right (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (β r : ℝ)
    {F G : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObs (blkS τ a m) (blkR τ a m)) :
    pairing τ a m β G (r • F) = r * pairing τ a m β G F := by
  rw [pairing_symm τ a m hm β hG ((localObs (blkS τ a m) (blkR τ a m)).smul_mem r hF),
    pairing_smul_left, pairing_symm τ a m hm β hF hG]

/-- **THE GIBBS REFLECTION FORM OF THE WILSON LATTICE, BUILT.**

A `Transfer.ReflForm` on `Transfer.reflForm` itself — the Gibbs form that file defines — carried on
the slab algebra of an even-extent lattice, with every field proved and `form_nonneg` holding at
EVERY REAL `β`. Symmetry is `Transfer.reflForm_symm`; bilinearity and positivity come through the
split pairing.

DERIVED: no numeral. `τ`, `a`, `m` and `β` are the caller's; `hm` and `hm0` are the extent's. -/
noncomputable def wilsonGibbsReflForm (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    MassGap.Transfer.ReflForm
      ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m)) where
  form F G := MassGap.Transfer.reflForm N τ (a + a) β F.1 G.1
  form_symm F G := MassGap.Transfer.reflForm_symm N τ (a + a) β F.1 G.1
  form_add_left F₁ F₂ G := by
    show MassGap.Transfer.reflForm N τ (a + a) β (F₁.1 + F₂.1) G.1
      = MassGap.Transfer.reflForm N τ (a + a) β F₁.1 G.1
        + MassGap.Transfer.reflForm N τ (a + a) β F₂.1 G.1
    rw [reflForm_eq_pairing hN τ a m hm hm0 β, reflForm_eq_pairing hN τ a m hm hm0 β,
      reflForm_eq_pairing hN τ a m hm hm0 β, dressed_add,
      pairing_add_right hN τ a m hm β (dressed_mem hN τ a m hm hm0 β F₁.2)
        (dressed_mem hN τ a m hm hm0 β F₂.2) (dressed_mem hN τ a m hm hm0 β G.2),
      add_div]
  form_smul_left r F G := by
    show MassGap.Transfer.reflForm N τ (a + a) β (r • F.1) G.1
      = r * MassGap.Transfer.reflForm N τ (a + a) β F.1 G.1
    rw [reflForm_eq_pairing hN τ a m hm hm0 β, reflForm_eq_pairing hN τ a m hm hm0 β,
      dressed_smul,
      pairing_smul_right τ a m hm β r (dressed_mem hN τ a m hm hm0 β F.2)
        (dressed_mem hN τ a m hm hm0 β G.2),
      mul_div_assoc]
  form_nonneg F := by
    show 0 ≤ MassGap.Transfer.reflForm N τ (a + a) β F.1 F.1
    have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
      wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
    rw [reflForm_eq_pairing hN τ a m hm hm0 β]
    exact div_nonneg (pairing_nonneg hN τ a m hm hm0 β (dressed_mem hN τ a m hm hm0 β F.2))
      (le_of_lt hZ)

/-- **THE VACUUM IS NORMALISED** — `⟨1, 1⟩ = 1` on the form just built. This is
`Transfer.TransferData.vac_norm`, the one field of a transfer construction that this form settles
outright.

DERIVED: the `1`s are the constant observable and the total mass of a probability measure, both
`Transfer.reflForm_one_one`'s. -/
theorem wilsonGibbsReflForm_vac_norm (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    (wilsonGibbsReflForm hN τ a m hm hm0 β).form
        ⟨fun _ => (1 : ℝ), one_mem_localObs⟩ ⟨fun _ => (1 : ℝ), one_mem_localObs⟩ = 1 :=
  MassGap.Transfer.reflForm_one_one N hN τ (a + a) β

end GibbsForm

/-! ## Part 7 — the corollary chain down to `corrClay`

The strong form IMPLIES the weak one. `ReflectPositive.PlaqReflPositive` tests the pairing on affine
functions of ONE plaquette's energy; that observable is a member of the module
(`plaqObs_sub_const_mem`), so the module statement specialises to it and the one-plaquette predicate
follows with nothing further assumed.
-/

section Weak

variable {d n N : ℕ} [NeZero n]

/-- **THE CENTRED PLAQUETTE ENERGY IS AN OBSERVABLE OF THE SLAB ALGEBRA.**

DERIVED: the `2` is the range of the Wilson density; `aC` is the caller's centring constant. -/
theorem plaqObs_sub_const_mem (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (q₀ : Plaq d n)
    (hdeg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (hlv : lv a (q₀.2 τ) < m) (aC : ℝ) :
    (fun U : Link d n → MassGap.SUN.SU N =>
        wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
      ∈ localObs (blkS τ a m) (blkR τ a m) := by
  refine mem_localObs.mpr ⟨(measurable_density_hol q₀).sub measurable_const,
    ⟨2 + |aC|, fun U => ?_⟩, fun U V hS hR => ?_⟩
  · have h1 : 0 ≤ wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) :=
      wilsonDensity_nonneg hN _
    have h2 : wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) ≤ 2 :=
      wilsonDensity_le_two hN _
    have h3 : -|aC| ≤ aC := neg_abs_le _
    have h4 : aC ≤ |aC| := le_abs_self _
    show |wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC| ≤ 2 + |aC|
    rw [abs_le]
    constructor <;> linarith
  · have hUV : ∀ l ∈ blkS τ a m ∪ blkR τ a m, U l = V l := by
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact hS l h
      · exact hR l h
    show wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ V) - aC
    rw [hol_congr_on_support (bd (d := d) (n := n)) q₀ U V
      (fun l hl => hUV l (plaq_links_le τ a m hm hm0 hdeg hlv l hl))]

/-- **THE STRONG FORM IMPLIES THE WEAK PREDICATE, at a named plane.**
`ReflectPositive.PlaqReflPositive` is the module statement read at one member of the module. -/
theorem plaqReflPositive_of_module (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (q₀ : Plaq d n)
    (hdeg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (hlv : lv a (q₀.2 τ) < m) (β : ℝ) :
    MassGap.ReflectPositive.PlaqReflPositive N τ (a + a) β q₀ := by
  intro aC
  exact wilson_expect_nonneg_module hN τ a m hm hm0 β
    (plaqObs_sub_const_mem hN τ a m hm hm0 q₀ hdeg hlv aC)

/-- **THE WEAK PREDICATE AT EVERY EVEN LAG**, from the module statement, at every real coupling. -/
theorem plaqReflPositive_even_lag_of_module (hN : N ≠ 0) (τ : Fin d) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) {c : Fin n} (hc : Even c.val) (q₀ : Plaq d n)
    (hdeg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (β : ℝ) :
    MassGap.ReflectPositive.PlaqReflPositive N τ c β q₀ := by
  obtain ⟨a', ha', hlv⟩ := exists_half_below m hm hm0 hc (q₀.2 τ)
  intro aC
  rw [← ha']
  exact plaqReflPositive_of_module hN τ a' m hm hm0 q₀ hdeg hlv β aC

/-- **THE LAG CORRELATION IS NONNEGATIVE AT EVERY EVEN LAG, AT EVERY REAL COUPLING**, derived from
the module statement rather than from the one-plaquette weld. -/
theorem corrHyper_nonneg_even_lag_of_module (hN : N ≠ 0) (τ : Fin d) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {lag : Fin n} (hlag : Even lag.val) :
    0 ≤ MassGap.WilsonBridge.corrHyper (d := d) N n μ ν τ β lag :=
  MassGap.ReflectPositive.corrHyper_nonneg_of_reflPositive hN hμ hν β lag
    (plaqReflPositive_even_lag_of_module hN τ m hm hm0 hlag _ (fun h => hμ h.1) β)

end Weak

/-! ## Part 8 — at the Clay problem's own parameters, with NO sign condition on the coupling -/

section Clay

/-- **THE CLAY CORRELATION IS NONNEGATIVE AT EVERY EVEN LAG, AT EVERY REAL COUPLING.**

`Complete.wilson_reflection_positive_at_even` carries `0 ≤ β`; on the even lags that hypothesis is
not needed and this is the statement without it. What still needs it is the odd lags — see the module
docstring.

DERIVED: `3` is the gauge group's rank and `4` the dimension, both `WilsonBridge.corrClay`'s own; `m`
is half the extent, the reflection geometry's own. -/
theorem corrClay_nonneg_even_lag (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {lag : Fin (Nap + 1)} (hlag : Even lag.val) :
    0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β lag :=
  corrHyper_nonneg_even_lag_of_module (N := 3) (d := 4) (by norm_num) (2 : Fin 4) m hm hm0
    (by decide) (by decide) β hlag

/-- **POSITIVE MASS ON THE EVEN SUBLATTICE OF LAGS, AT EVERY REAL COUPLING.**

The even-lag companion of the axiom's second conjunct. Lag zero is even and its correlation is the
plaquette-energy VARIANCE, strictly positive at every real coupling
(`PlaqVariance.corrClay_zero_pos`); every other even lag is nonnegative by the theorem above. The
full sum over ALL lags is not reachable this way at negative coupling, because the odd lags are not
controlled there.

DERIVED: the `0` of `0 < …` is positive mass; the filter is the parity the site reflection covers. -/
theorem corrClay_even_sum_pos (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    0 < ∑ lag ∈ Finset.univ.filter (fun l : Fin (Nap + 1) => Even l.val),
      MassGap.WilsonBridge.corrClay (Nap + 1) β lag := by
  classical
  refine Finset.sum_pos' (fun lag hlag => ?_) ⟨0, ?_, ?_⟩
  · exact corrClay_nonneg_even_lag Nap m hm hm0 β (Finset.mem_filter.mp hlag).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
  · exact MassGap.PlaqVariance.corrClay_zero_pos Nap β

/-- **ROW A4, WITH ITS EVEN HALF SUPPLIED BY THE MODULE STATEMENT.**

The same conjunction as `OddLagSplit.corrClay_reflection_positive` and
`Complete.wilson_reflection_positive_at_even`, on the same domain, assembled so that the even lags
come from `plaqReflPositive_even_lag_of_module` — the half-space ALGEBRA statement at every real
coupling — and only the odd lags from `OddLagSplit.plaqReflPositive_odd`, which is where `0 ≤ β`
enters and cannot be removed.

So the strong form is shown to IMPLY the weak one rather than to sit beside it: every hypothesis this
theorem carries beyond the extent's parity belongs to the odd lags.

DERIVED: `3` is the gauge group's rank, `4` the dimension, `(0, 1)` the base plaquette's plane and
`2` the lag axis — all `WilsonBridge.corrClay`'s own; `2 ≤ m` and `0 ≤ β` are the odd-lag route's,
named in `OddLagSplit.plaqReflPositive_odd`. -/
theorem corrClay_reflection_positive_via_module (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm2 : 2 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∀ lag, 0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β lag)
      ∧ 0 < ∑ lag, MassGap.WilsonBridge.corrClay (Nap + 1) β lag := by
  classical
  refine MassGap.ReflectPositive.corrClay_rp_of Nap β (fun lag => ?_)
    (MassGap.PlaqVariance.corrClay_zero_pos Nap β)
  by_cases h : Even lag.val
  · exact plaqReflPositive_even_lag_of_module (N := 3) (d := 4) (by norm_num) (2 : Fin 4) m
      hm (by omega) h
      ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))
      (by
        intro hc
        have hzero : (0 : Fin 4) = 2 := hc.1
        exact absurd hzero (by decide)) β
  · obtain ⟨a, ha, hlv0, hlvm⟩ :=
      MassGap.OddLagSplit.exists_odd_lag_plane_in_half m ⟨m, by omega⟩ hm (by omega) h
        (0 : Fin (Nap + 1))
    have hloc : ∀ l ∈ (bd ((((0 : Fin 4), (1 : Fin 4)),
        (fun _ => 0 : Site 4 (Nap + 1))) : Plaq 4 (Nap + 1))).map Prod.fst,
        l ∈ MassGap.OddLagSplit.oblkS (2 : Fin 4) a m :=
      MassGap.OddLagSplit.transverse_plaq_links_in_oblkS m (2 : Fin 4) a hm (by omega)
        (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) (by decide : (1 : Fin 4) ≠ (2 : Fin 4))
        hlv0 hlvm
    have hRP := MassGap.OddLagSplit.plaqReflPositive_odd (N := 3) (2 : Fin 4) a m
      (by norm_num) hm hm2 hβ _ hloc
    rwa [ha] at hRP

/-- **NON-VACUITY — the even-lag statement at the smallest even extent, at a NEGATIVE coupling.**

`corrClay_nonneg_even_lag` would be an empty strengthening if it only ever ran where `0 ≤ β` already
holds. Here it is at `β = −1`, where `OddLagSplit.corrClay_reflection_positive` says nothing and
`CharacterExpansion.NegControl.su3_kernel_neg_of_neg` says the odd-lag kernel is strictly negative.

DERIVED: `3` is the aperture whose extent `3 + 1` is the smallest even extent, `2` its half, and
`−1` a coupling of the sign the odd-lag route excludes. -/
theorem corrClay_nonneg_even_lag_at_negative_coupling :
    0 ≤ MassGap.WilsonBridge.corrClay (3 + 1) (-1 : ℝ) (0 : Fin 4)
      ∧ 0 ≤ MassGap.WilsonBridge.corrClay (3 + 1) (-1 : ℝ) (2 : Fin 4) :=
  ⟨corrClay_nonneg_even_lag 3 2 (by norm_num) (by norm_num) (-1 : ℝ) (by decide),
    corrClay_nonneg_even_lag 3 2 (by norm_num) (by norm_num) (-1 : ℝ) (by decide)⟩

end Clay

section Audit
#print axioms mul_mem_localObs
#print axioms one_mem_localObs
#print axioms halfBoltz
#print axioms dressed
#print axioms actPlus_local
#print axioms halfBoltz_mem
#print axioms dressed_mem
#print axioms dressed_add
#print axioms dressed_smul
#print axioms integrand_eq_paired_obs
#print axioms corrNum_refl_eq_pairing
#print axioms wilson_pairing_nonneg_module
#print axioms wilson_expect_nonneg_module
#print axioms form_sum_left
#print axioms form_sum_sum
#print axioms pairing_gram_nonneg
#print axioms wilson_expect_gram_nonneg
#print axioms reflForm_eq_pairing
#print axioms pairing_add_right
#print axioms pairing_smul_right
#print axioms wilsonGibbsReflForm
#print axioms wilsonGibbsReflForm_vac_norm
#print axioms plaqObs_sub_const_mem
#print axioms plaqReflPositive_of_module
#print axioms plaqReflPositive_even_lag_of_module
#print axioms corrHyper_nonneg_even_lag_of_module
#print axioms corrClay_nonneg_even_lag
#print axioms corrClay_even_sum_pos
#print axioms corrClay_reflection_positive_via_module
#print axioms corrClay_nonneg_even_lag_at_negative_coupling
end Audit

end MassGap.ReflectionStrong
