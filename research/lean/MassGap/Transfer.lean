import Mathlib
import MassGap.Reflect
import MassGap.Spectral

/-!
# MassGap.Transfer — the Osterwalder–Seiler reflection form, its GNS quotient, and the transfer
operator that acts on it

**WHY THIS FILE EXISTS.** The flagship `Complete.ym_mass_gap_of_decay_at_floor` rests on one
remaining hypothesis, `hdecay`: the modes `m β k` are bounded by `e^{−(κ₀−μ)}`. Read literally that
is a bound on a family the caller supplies, and `ymModel` supplies it at `Idx := Unit`,
`m := e^{−(κ₀−μ)}` — a number defined equal to its own bound. `Spectral.PeriodicSpectralForm` names
what the modes would have to BE for the hypothesis to say something about Yang–Mills: the spectrum
of a transfer operator. **There was no transfer operator anywhere in the tree** (`WilsonRead` says so
for its two-plaquette cell, and a tree-wide search says so generally), so `hdecay` could not be
attacked at all.

This file builds one. `Reflect` supplied the missing geometry — the coordinate reflection with its
dagger, and the invariance of the Gibbs expectation under it. What is added here is the operator
theory that geometry is FOR.

## What is proved, and what is assumed — the line matters

**Proved with no hypothesis beyond what `Reflect` already established:** the Wilson reflection form
`⟨F, G⟩ := ⟨(F ∘ θ) · G⟩` is SYMMETRIC (`reflForm_symm`), and `⟨1, 1⟩ = 1` (`reflForm_one_one`).
Symmetry is not a triviality about the definition — it is `Reflect.expect_reflect_invariant` together
with `θ² = id`, and it is the first property of the form that is a statement about the Wilson measure.

**Assumed, and carried as an explicit field so nothing can assume it silently:** POSITIVE
SEMIDEFINITENESS, `0 ≤ ⟨F, F⟩`. That is reflection positivity, it is an open axiom in this
development (`Complete.wilson_reflection_positive_at`), and `ReflectionPositivity` sets out which
half of Osterwalder–Seiler carries it. It appears here as the field `ReflForm.form_nonneg`. **No
`ReflForm` is constructed from the Wilson measure in this file, and none can be until that axiom is
discharged.** Everything downstream is a theorem about any form that has it.

**Assumed separately, because it does not follow from contractivity:** POSITIVITY OF THE TRANSFER
OPERATOR, `0 ≤ ⟨x, T x⟩`. Contractivity gives `|λ| ≤ 1`; it says nothing about the SIGN of `λ`, and a
negative eigenvalue is a real possibility for a transfer matrix — it is what an oscillating
correlator looks like. `λ ≥ 0` is reflection positivity about a HALF-INTEGER time plane, a second
application of the same physics rather than a consequence of the first. It is a named hypothesis of
`eigenvalue_nonneg` and of `periodicSpectralForm_of_transfer`, never a field.

## The construction

`ReflForm` → Cauchy–Schwarz → the null space is a submodule → the quotient carries a genuine
`InnerProductSpace ℝ` (through `InnerProductSpace.Core`) → the time translation descends to it
because it is contractive → it is self-adjoint, fixes the vacuum, and has operator norm at most one
→ in finite dimension its eigen-expansion of `⟨v, T^k v⟩` is a nonnegative-weight sum of `λ^k`, which
is `Spectral.PeriodicSpectralForm` once the two ends of the circle are added.

`T Ω = Ω` and `‖T‖ ≤ 1` are NORMALISATION, not gap: they come from `⟨1,1⟩ = 1` and from `T` being an
expectation. Nothing here proves a gap, and nothing here supplies `hdecay`. What it supplies is the
object `hdecay` would have to be about.

## WHAT BUILDING THE OBJECT IMMEDIATELY SHOWS: `hdecay` IS FALSE OVER THE FULL SPECTRUM

`one_le_of_eigenvalues_le`: if every transfer eigenvalue is at most `r`, then `r ≥ 1`. The vacuum is
a unit eigenvector at eigenvalue exactly one, so no bound below one can hold for every mode.

That is a statement about the flagship's hypothesis. `Complete.ym_mass_gap_at_floor`'s `hdecay` asks
`‖m β k‖ ≤ e^{−(κ₀−μ)} < 1` for every `k ∈ ymModel.s β`, and `Spectral.periodic_decay_le` asks
`∀ k, lam k ≤ r`. Read over the whole transfer spectrum, both are unsatisfiable — and the proof needs
neither positivity of `T` nor a gap, only normalisation. The spectrum they can be about is the one on
`Ω^⊥`: the CONNECTED correlator, vacuum subtracted. `Spectral.PeriodicSpectralForm` carries no field
excluding the vacuum mode, so every form built here by `periodicSpectralForm_of_transfer` contains it
and falsifies `periodic_decay_le`'s hypothesis. `periodicCorr_vac` is the same point concretely: the
vacuum's own correlator is the constant `2`.

This does not break anything downstream — `GapOfDecay` already separates a vacuum term (`hvac`) — but
it does say that the vacuum projection has to be part of the statement of `hdecay`, not left implicit
in a free mode family.

## What is NOT here

The bridge from the Wilson measure to a `TransferData` instance. Three things are missing and each is
named where it would enter: reflection positivity itself (the open axiom); the half-space splitting
of the observable algebra, which needs the links partitioned by the reflection plane and the cross
term handled; and the identification of the lattice time shift as an operator on half-space
observables. This file is the target those three would land in, not a claim that they have landed.

A fourth, smaller gap is inside `periodicCorr`: it is the ground-state periodic shape
`⟨v,T^d v⟩ + ⟨v,T^{n−d} v⟩`, which is what `PeriodicSpectralForm` has room for. The exact finite-`n`
thermal correlator `Tr(A T^d A T^{n−d})/Tr(T^n)` is a DOUBLE spectral sum and does not fit that
one-index shape at all; either the shape widens or the identification is asymptotic in `n`.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.Transfer`.
-/

namespace MassGap.Transfer

open MassGap MassGap.LatticeGauge MassGap.WilsonHypercubic MassGap.CompactGauge

/-! ## Part 1 — the reflection form on the Wilson measure

The concrete object. Two of its properties are proved outright; the third, positivity, is the open
axiom and is deliberately absent.
-/

section Wilson

variable {d n : ℕ}

/-- **The Osterwalder–Seiler reflection form of the `d`-dimensional `SU(N)` Wilson system**:
`⟨F, G⟩ := ⟨(F ∘ θ) · G⟩`, where `θ = Reflect.reflConf τ c` is the coordinate reflection with its
dagger and `⟨·⟩` is the Gibbs expectation.

This is the pairing reflection positivity is a statement about. It is written for observables of the
WHOLE configuration rather than of a half-space, because nothing claimed here needs the split:
symmetry and normalisation hold for any observable, and positivity — the property that does need the
split — is not claimed at all.

DERIVED: nothing numeric. `τ`, `c`, `β` and the observables are the caller's. -/
noncomputable def reflForm (N : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) : ℝ :=
  (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
    (fun U => F (Reflect.reflConf τ c U) * G U)

/-- Congruence for the Gibbs expectation: pointwise-equal observables have equal expectations. Stated
here so the reflection identities can be closed without rewriting under a binder whose type is
`Config` on one side and `Link d n → SU N` on the other. -/
theorem expect_congr (N : ℕ) [NeZero n] (β : ℝ) {O O' : (sysWilson N d n).Config → ℝ}
    (h : ∀ U, O U = O' U) :
    (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  rw [funext h]

/-- **THE REFLECTION FORM IS SYMMETRIC.** Not a triviality about the definition: it is the Gibbs
expectation's invariance under the reflection (`Reflect.expect_reflect_invariant`, which needed the
dagger, the conjugated holonomy and the inversion-invariance of Haar) together with `θ² = id`.

Applying the invariance to the observable `U ↦ F(θU)·G(U)` moves the reflection off `F` and onto `G`,
and involutivity cancels the double reflection that leaves behind. -/
theorem reflForm_symm (N : ℕ) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    reflForm N τ c β F G = reflForm N τ c β G F := by
  have hinv : ∀ U : Link d n → MassGap.SUN.SU N,
      Reflect.reflConf τ c (Reflect.reflConf τ c U) = U := Reflect.reflConf_involutive τ c
  have h := Reflect.expect_reflect_invariant N τ c β
    (fun U => F (Reflect.reflConf τ c U) * G U)
  simp only [hinv] at h
  exact Eq.trans h.symm (expect_congr N β (fun U => mul_comm _ _))

/-- **THE CONSTANT OBSERVABLE IS NORMALISED**: `⟨1, 1⟩ = 1`.

The Gibbs state is a probability state, so the constant observable pairs with itself to one. This is
where the transfer operator's eigenvalue `1` comes from, and it is why `T Ω = Ω` is normalisation
rather than a spectral claim.

DERIVED: the `1`s are the constant observable and the total mass of a probability measure. -/
theorem reflForm_one_one (N : ℕ) (hN : N ≠ 0) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ) :
    reflForm N τ c β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 :=
  calc reflForm N τ c β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β (fun _ => (1 : ℝ)) :=
        expect_congr N β (fun _ => one_mul 1)
    _ = 1 := MassGap.WilsonReal.wilsonSystem_expect_one (N := N) hN (bd (d := d) (n := n)) β

end Wilson

/-! ## Part 2 — a symmetric form, its Cauchy–Schwarz, and its null space -/

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **A symmetric bilinear form on a real module** — the shape of `⟨F, G⟩`, with no positivity. -/
structure PreForm (A : Type*) [AddCommGroup A] [Module ℝ A] where
  /-- The form itself. -/
  form : A → A → ℝ
  /-- Symmetry, which `reflForm_symm` proves for the Wilson form. -/
  form_symm : ∀ x y, form x y = form y x
  /-- Additivity in the first slot; with symmetry that gives it in both. -/
  form_add_left : ∀ x y z, form (x + y) z = form x z + form y z
  /-- Homogeneity in the first slot. -/
  form_smul_left : ∀ (r : ℝ) (x y), form (r • x) y = r * form x y

/-- **A REFLECTION FORM: symmetric, bilinear, and POSITIVE SEMIDEFINITE.**

The last field is the whole of reflection positivity, and it is a field precisely so that it cannot
be assumed silently: every theorem below that uses positivity takes a `ReflForm`, and producing one
for the Wilson measure is the open axiom `Complete.wilson_reflection_positive_at`. Nothing in this
file constructs a `ReflForm` from `reflForm`. -/
structure ReflForm (A : Type*) [AddCommGroup A] [Module ℝ A] extends PreForm A where
  /-- **REFLECTION POSITIVITY**, assumed. See the module docstring. -/
  form_nonneg : ∀ x, 0 ≤ form x x

namespace PreForm

variable (P : PreForm A)

theorem form_zero_left (y : A) : P.form 0 y = 0 := by
  have h := P.form_smul_left 0 0 y
  simpa using h

theorem form_zero_right (x : A) : P.form x 0 = 0 := by
  rw [P.form_symm]; exact P.form_zero_left x

theorem form_add_right (x y z : A) : P.form x (y + z) = P.form x y + P.form x z := by
  rw [P.form_symm x (y + z), P.form_add_left, P.form_symm y x, P.form_symm z x]

theorem form_smul_right (r : ℝ) (x y : A) : P.form x (r • y) = r * P.form x y := by
  rw [P.form_symm x (r • y), P.form_smul_left, P.form_symm y x]

/-- **The quadratic expansion** `⟨tx + y, tx + y⟩ = ⟨x,x⟩t² + 2⟨x,y⟩t + ⟨y,y⟩`, which is what
Cauchy–Schwarz reads the discriminant of.

DERIVED: the `2` is the number of cross terms a symmetric form produces. Nothing is chosen. -/
theorem form_quad (x y : A) (t : ℝ) :
    P.form (t • x + y) (t • x + y)
      = P.form x x * (t * t) + (2 * P.form x y) * t + P.form y y := by
  have h1 : P.form (t • x + y) (t • x + y)
      = P.form (t • x) (t • x + y) + P.form y (t • x + y) := P.form_add_left _ _ _
  have h2 : P.form (t • x) (t • x + y) = t * P.form x (t • x + y) := P.form_smul_left _ _ _
  have h3 : P.form x (t • x + y) = P.form x (t • x) + P.form x y := P.form_add_right _ _ _
  have h4 : P.form x (t • x) = t * P.form x x := P.form_smul_right _ _ _
  have h5 : P.form y (t • x + y) = P.form y (t • x) + P.form y y := P.form_add_right _ _ _
  have h6 : P.form y (t • x) = t * P.form y x := P.form_smul_right _ _ _
  have h7 : P.form y x = P.form x y := P.form_symm _ _
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

/-- DERIVED: the `2` is the cross-term count of `form_quad` at `t = 1`. -/
theorem form_add_self (x y : A) :
    P.form (x + y) (x + y) = P.form x x + 2 * P.form x y + P.form y y := by
  have h := P.form_quad x y 1
  rw [one_smul] at h
  rw [h]; ring

end PreForm

namespace ReflForm

variable (P : ReflForm A)

/-- **CAUCHY–SCHWARZ FOR THE REFLECTION FORM.** The first real consequence of positivity, and the one
everything else needs: it makes the null space a subspace and makes the form descend to the quotient.

Proved the elementary way — the quadratic `t ↦ ⟨tx+y, tx+y⟩` is nonnegative, so its discriminant is
not positive.

DERIVED: the exponent `2` is the degree of that quadratic and the `4` is the `4` of `b² − 4ac`. -/
theorem cauchy_schwarz (x y : A) : (P.form x y) ^ 2 ≤ P.form x x * P.form y y := by
  have hq : ∀ t : ℝ, 0 ≤ P.form x x * (t * t) + (2 * P.form x y) * t + P.form y y := by
    intro t
    rw [← P.form_quad]
    exact P.form_nonneg _
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [hd]

/-- **THE NULL SPACE `N = {F : ⟨F,F⟩ = 0}` IS A SUBMODULE.**

Closure under addition is not formal — it is Cauchy–Schwarz: a null vector is orthogonal to
everything, so the cross term in `⟨x+y, x+y⟩` vanishes.

DERIVED: the `0` is the definition of the null space. -/
def nullSpace : Submodule ℝ A where
  carrier := {x | P.form x x = 0}
  zero_mem' := P.form_zero_left 0
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hcs := P.cauchy_schwarz x y
    rw [hx, zero_mul] at hcs
    have hxy : P.form x y = 0 := by nlinarith [sq_nonneg (P.form x y)]
    rw [P.form_add_self, hx, hy, hxy]; ring
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [P.form_smul_left, P.form_smul_right, hx]; ring

@[simp] theorem mem_nullSpace {x : A} : x ∈ P.nullSpace ↔ P.form x x = 0 := Iff.rfl

/-- **A NULL VECTOR IS ORTHOGONAL TO EVERYTHING** — Cauchy–Schwarz again, and the reason the form
descends to the quotient at all. -/
theorem form_eq_zero_of_mem_null {x : A} (hx : x ∈ P.nullSpace) (y : A) : P.form x y = 0 := by
  have hcs := P.cauchy_schwarz x y
  rw [P.mem_nullSpace.mp hx, zero_mul] at hcs
  nlinarith [sq_nonneg (P.form x y)]

/-- The form as a bilinear map, so the quotient can be taken with `Submodule.liftQ`.

DERIVED: nothing numeric. -/
def bil : A →ₗ[ℝ] A →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => P.form x y
      map_add' := fun y z => P.form_add_right x y z
      map_smul' := fun r y => by simpa using P.form_smul_right r x y }
  map_add' x z := by ext y; exact P.form_add_left x z y
  map_smul' r x := by ext y; simpa using P.form_smul_left r x y

@[simp] theorem bil_apply (x y : A) : P.bil x y = P.form x y := rfl

end ReflForm

/-! ## Part 3 — the GNS quotient is a genuine inner product space -/

/-- **THE GNS SPACE**: observables modulo the null space of the reflection form.

`Submodule.Quotient` supplies the module; what is supplied below is the inner product, and the point
is that `definite` — the one field that separates a form from an inner product — holds by
CONSTRUCTION once the null space is quotiented out.

DERIVED: nothing numeric. -/
def GNS (P : ReflForm A) : Type _ := A ⧸ P.nullSpace

namespace GNS

variable {P : ReflForm A}

/-- DERIVED: nothing numeric; inherited from the quotient module. -/
instance instAddCommGroup (P : ReflForm A) : AddCommGroup (GNS P) :=
  inferInstanceAs (AddCommGroup (A ⧸ P.nullSpace))

/-- DERIVED: nothing numeric; inherited from the quotient module. -/
instance instModule (P : ReflForm A) : Module ℝ (GNS P) :=
  inferInstanceAs (Module ℝ (A ⧸ P.nullSpace))

/-- The class of an observable in the GNS space.

DERIVED: nothing numeric. -/
def mk (P : ReflForm A) (x : A) : GNS P := Submodule.Quotient.mk x

/-- Every element of the GNS space is the class of an observable. -/
theorem exists_mk (q : GNS P) : ∃ x : A, mk P x = q :=
  Submodule.Quotient.mk_surjective _ q

@[simp] theorem mk_add (x y : A) : mk P (x + y) = mk P x + mk P y := rfl

@[simp] theorem mk_smul (r : ℝ) (x : A) : mk P (r • x) = r • mk P x := rfl

@[simp] theorem mk_zero : mk P (0 : A) = 0 := rfl

/-- **The quotient is exactly by the null vectors**: a class is zero iff its representative is null.
This is the `definite` field of an inner product, before it is packaged as one. -/
theorem mk_eq_zero_iff (x : A) : mk P x = 0 ↔ P.form x x = 0 := by
  constructor
  · intro h
    exact P.mem_nullSpace.mp ((Submodule.Quotient.mk_eq_zero _).mp h)
  · intro h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (P.mem_nullSpace.mpr h)

/-- The form, descended in its FIRST slot.

DERIVED: nothing numeric. -/
noncomputable def toDual (P : ReflForm A) : GNS P →ₗ[ℝ] (A →ₗ[ℝ] ℝ) :=
  Submodule.liftQ P.nullSpace P.bil (by
    intro x hx
    simp only [LinearMap.mem_ker]
    ext y
    simpa using P.form_eq_zero_of_mem_null hx y)

@[simp] theorem toDual_mk (x y : A) : toDual P (mk P x) y = P.form x y := rfl

/-- **The reflection form on the GNS space**, descended in BOTH slots — well defined because a null
vector is orthogonal to everything.

DERIVED: nothing numeric. -/
noncomputable def bilQ (P : ReflForm A) : GNS P →ₗ[ℝ] GNS P →ₗ[ℝ] ℝ :=
  Submodule.liftQ P.nullSpace (toDual P).flip (by
    intro y hy
    simp only [LinearMap.mem_ker]
    ext q
    obtain ⟨x, rfl⟩ := exists_mk q
    rw [LinearMap.flip_apply, toDual_mk, P.form_symm]
    exact P.form_eq_zero_of_mem_null hy x)

/-- The descended form, read on representatives. Note the `flip`: `bilQ` lifts the SECOND slot last,
so on representatives it lands on `P.form y x`, and symmetry is what turns that into `P.form x y`. -/
@[simp] theorem bilQ_mk (x y : A) : bilQ P (mk P x) (mk P y) = P.form x y := by
  have h : bilQ P (mk P x) (mk P y) = P.form y x := rfl
  rw [h, P.form_symm]

/-- **THE GNS INNER PRODUCT.** Symmetry is the form's; nonnegativity is reflection positivity; and
definiteness — the one field that is not inherited — holds because the null space was quotiented out.

DERIVED: the `0`s state nonnegativity and definiteness; they are not magnitudes. -/
@[reducible] noncomputable def core (P : ReflForm A) : InnerProductSpace.Core ℝ (GNS P) where
  inner q r := bilQ P q r
  conj_inner_symm := by
    intro q r
    obtain ⟨x, rfl⟩ := exists_mk q
    obtain ⟨y, rfl⟩ := exists_mk r
    show (starRingEnd ℝ) (bilQ P (mk P y) (mk P x)) = bilQ P (mk P x) (mk P y)
    simpa using P.form_symm y x
  re_inner_nonneg := by
    intro q
    obtain ⟨x, rfl⟩ := exists_mk q
    show 0 ≤ RCLike.re (bilQ P (mk P x) (mk P x))
    simpa using P.form_nonneg x
  add_left := by
    intro q r s
    show bilQ P (q + r) s = bilQ P q s + bilQ P r s
    simp
  smul_left := by
    intro q r c
    show bilQ P (c • q) r = (starRingEnd ℝ) c * bilQ P q r
    simp
  definite := by
    intro q
    obtain ⟨x, rfl⟩ := exists_mk q
    intro hq
    refine (mk_eq_zero_iff x).mpr ?_
    have h : bilQ P (mk P x) (mk P x) = 0 := hq
    simpa using h

/-- The GNS space's norm, `‖F‖ = √⟨F,F⟩`.

DERIVED: nothing numeric; the norm is the one `InnerProductSpace.Core` derives from the form. -/
noncomputable instance instNormedAddCommGroup (P : ReflForm A) : NormedAddCommGroup (GNS P) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (GNS P) _ _ _ (core P)

/-- **THE GNS SPACE IS A REAL INNER PRODUCT SPACE.** The target of item 2 of the construction: not a
form on a vector space but a genuine `InnerProductSpace ℝ`, so Mathlib's spectral theory applies to
operators on it.

DERIVED: nothing numeric. -/
noncomputable instance instInnerProductSpace (P : ReflForm A) : InnerProductSpace ℝ (GNS P) :=
  InnerProductSpace.ofCore (core P).toCore

@[simp] theorem inner_mk (x y : A) : inner ℝ (mk P x) (mk P y) = P.form x y := bilQ_mk x y

/-- **The GNS norm squared is the form.** -/
theorem norm_mk_mul_norm_mk (x : A) : ‖mk P x‖ * ‖mk P x‖ = P.form x x := by
  rw [← real_inner_self_eq_norm_mul_norm, inner_mk]

end GNS

/-! ## Part 4 — the transfer operator -/

/-- **THE DATA OF A TRANSFER OPERATOR ON A REFLECTION FORM.**

`T` is one step of time translation, acting on the observables before the quotient; `vac` is the
constant observable. The four conditions are exactly what the Osterwalder–Seiler construction gives
and no more:

* `T_symm` — self-adjointness of the time translation with respect to the reflection form. **This is
  what reflection positivity is FOR**: the reflection exchanges the two half-lines, so translating
  one is the same as translating the other.
* `T_contract` — the translation does not increase the form. NORMALISATION: the Gibbs measure is a
  probability measure, so the transfer operator is an expectation and cannot expand. It is NOT a gap.
* `T_vac` and `vac_norm` — the constant observable is translation-invariant and normalised, which is
  where the eigenvalue exactly `1` comes from. Again normalisation, not spectrum.

There is no positivity of `T` here (`0 ≤ ⟨x, Tx⟩`): it does not follow from these and is carried as
a separate named hypothesis where it is needed. -/
structure TransferData (A : Type*) [AddCommGroup A] [Module ℝ A] extends ReflForm A where
  /-- One step of time translation. -/
  T : A →ₗ[ℝ] A
  /-- The constant observable — the vacuum before the quotient. -/
  vac : A
  /-- Self-adjointness with respect to the reflection form. -/
  T_symm : ∀ x y, form (T x) y = form x (T y)
  /-- Contractivity: an expectation cannot expand the form. -/
  T_contract : ∀ x, form (T x) (T x) ≤ form x x
  /-- The vacuum is translation-invariant. -/
  T_vac : T vac = vac
  /-- The vacuum is normalised — this is `reflForm_one_one`. -/
  vac_norm : form vac vac = 1

namespace TransferData

variable {D : TransferData A}

/-- **The translation preserves the null space**, which is what lets it descend: a null vector goes
to something the form cannot see, by contractivity and positivity together. -/
theorem T_mem_null {x : A} (hx : x ∈ D.toReflForm.nullSpace) :
    D.T x ∈ D.toReflForm.nullSpace := by
  simp only [ReflForm.mem_nullSpace] at hx ⊢
  have h1 := D.T_contract x
  have h2 := D.form_nonneg (D.T x)
  linarith

/-- **THE TRANSFER OPERATOR `T : H → H`** — one step of time translation on the GNS space.

DERIVED: nothing numeric. -/
noncomputable def Tq (D : TransferData A) : GNS D.toReflForm →ₗ[ℝ] GNS D.toReflForm :=
  Submodule.mapQ _ _ D.T (by
    intro x hx
    simpa using T_mem_null (D := D) hx)

@[simp] theorem Tq_mk (D : TransferData A) (x : A) :
    Tq D (GNS.mk D.toReflForm x) = GNS.mk D.toReflForm (D.T x) := rfl

/-- **THE TRANSFER OPERATOR IS SELF-ADJOINT.** This is what reflection positivity is for, and it is
the hypothesis Mathlib's spectral theorem consumes. -/
theorem Tq_isSymmetric (D : TransferData A) : (Tq D).IsSymmetric := by
  intro q r
  obtain ⟨x, rfl⟩ := GNS.exists_mk q
  obtain ⟨y, rfl⟩ := GNS.exists_mk r
  simp only [Tq_mk, GNS.inner_mk]
  exact D.T_symm x y

/-- **THE VACUUM** `Ω = [1]`.

DERIVED: nothing numeric. -/
noncomputable def vacGNS (D : TransferData A) : GNS D.toReflForm := GNS.mk D.toReflForm D.vac

/-- **`T Ω = Ω` — THE VACUUM IS AN EIGENVECTOR AT EIGENVALUE EXACTLY ONE.**

From translation invariance of the constant observable, not from any gap. -/
theorem Tq_vacGNS (D : TransferData A) : Tq D (vacGNS D) = vacGNS D := by
  simp only [vacGNS, Tq_mk, D.T_vac]

/-- **`‖Ω‖ = 1`** — so the vacuum is not the zero vector and the eigenvalue one is genuinely attained.

DERIVED: the `1` is the total mass of a probability measure, carried through `vac_norm`. -/
theorem norm_vacGNS (D : TransferData A) : ‖vacGNS D‖ = 1 := by
  have h : ‖vacGNS D‖ * ‖vacGNS D‖ = 1 := by
    rw [vacGNS, GNS.norm_mk_mul_norm_mk]
    exact D.vac_norm
  nlinarith [norm_nonneg (vacGNS D)]

/-- **`T` IS A CONTRACTION**, pointwise. Normalisation, not gap. -/
theorem Tq_norm_le (D : TransferData A) (q : GNS D.toReflForm) : ‖Tq D q‖ ≤ ‖q‖ := by
  obtain ⟨x, rfl⟩ := GNS.exists_mk q
  have h : ‖Tq D (GNS.mk D.toReflForm x)‖ * ‖Tq D (GNS.mk D.toReflForm x)‖
      ≤ ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ := by
    rw [Tq_mk, GNS.norm_mk_mul_norm_mk, GNS.norm_mk_mul_norm_mk]
    exact D.T_contract x
  nlinarith [norm_nonneg (Tq D (GNS.mk D.toReflForm x)), norm_nonneg (GNS.mk D.toReflForm x)]

/-- The transfer operator as a bounded operator.

DERIVED: the `1` is the contraction constant `Tq_norm_le` proves, not a chosen bound. -/
noncomputable def TqL (D : TransferData A) : GNS D.toReflForm →L[ℝ] GNS D.toReflForm :=
  LinearMap.mkContinuous (Tq D) 1 (fun q => by simpa using Tq_norm_le D q)

/-- **`‖T‖ ≤ 1`.** Contractivity again, now as an operator-norm bound.

DERIVED: the `1` is `Tq_norm_le`'s constant. -/
theorem norm_TqL_le_one (D : TransferData A) : ‖TqL D‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TransferData

/-! ## Part 5 — the spectral decomposition, in finite dimension -/

/-- **A POWER OF A SELF-ADJOINT OPERATOR IS SELF-ADJOINT.** -/
theorem isSymmetric_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : E →ₗ[ℝ] E} (hS : S.IsSymmetric) : ∀ k : ℕ, (S ^ k).IsSymmetric := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      have h1 : (S ^ (k + 1)) x = S ((S ^ k) x) := by
        rw [pow_succ']; rfl
      have h2 : (S ^ (k + 1)) y = (S ^ k) (S y) := by
        rw [pow_succ]; rfl
      rw [h1, h2, hS, ih]

namespace TransferData

variable (D : TransferData A) [FiniteDimensional ℝ (GNS D.toReflForm)] {m : ℕ}

/-- `T^k` acts on an eigenvector by the `k`-th power of its eigenvalue. -/
theorem Tq_pow_eigenvectorBasis (hm : Module.finrank ℝ (GNS D.toReflForm) = m)
    (i : Fin m) (k : ℕ) :
    ((Tq D) ^ k) ((Tq_isSymmetric D).eigenvectorBasis hm i)
      = (((Tq_isSymmetric D).eigenvalues hm i) ^ k) • ((Tq_isSymmetric D).eigenvectorBasis hm i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : ((Tq D) ^ (k + 1)) ((Tq_isSymmetric D).eigenvectorBasis hm i)
          = Tq D (((Tq D) ^ k) ((Tq_isSymmetric D).eigenvectorBasis hm i)) := by
        rw [pow_succ']; rfl
      rw [hstep, ih, map_smul, (Tq_isSymmetric D).apply_eigenvectorBasis hm i, smul_smul]
      simp [pow_succ, mul_comm]

/-- **THE SPECTRAL EXPANSION OF THE CORRELATOR.**

`⟨v, T^k v⟩ = ∑ᵢ wᵢ λᵢ^k` with `wᵢ = ⟨eᵢ, v⟩² ≥ 0`. The weights are squares — that is the content of
"reflection positivity gives nonnegative weights" — and the decay factors are the eigenvalues of the
transfer operator. This is the half-line shape, and `Spectral.flat_of_aperiodic` is the reason it
cannot be the finite-volume correlator on its own. -/
theorem inner_pow_expand (hm : Module.finrank ℝ (GNS D.toReflForm) = m)
    (v : GNS D.toReflForm) (k : ℕ) :
    inner ℝ v (((Tq D) ^ k) v)
      = ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) v) ^ 2
          * ((Tq_isSymmetric D).eigenvalues hm i) ^ k := by
  have hb := ((Tq_isSymmetric D).eigenvectorBasis hm).sum_inner_mul_inner v (((Tq D) ^ k) v)
  rw [← hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : inner ℝ (((Tq_isSymmetric D).eigenvectorBasis hm) i) (((Tq D) ^ k) v)
      = inner ℝ (((Tq D) ^ k) (((Tq_isSymmetric D).eigenvectorBasis hm) i)) v :=
    (isSymmetric_pow (Tq_isSymmetric D) k _ v).symm
  rw [h1, Tq_pow_eigenvectorBasis, real_inner_smul_left,
    real_inner_comm v (((Tq_isSymmetric D).eigenvectorBasis hm) i)]
  ring

/-- **EVERY TRANSFER EIGENVALUE IS AT MOST ONE IN MODULUS** — contractivity, which is normalisation.

DERIVED: the `1` is the contraction constant. -/
theorem abs_eigenvalue_le_one (hm : Module.finrank ℝ (GNS D.toReflForm) = m) (i : Fin m) :
    |(Tq_isSymmetric D).eigenvalues hm i| ≤ 1 := by
  have hnorm : ‖((Tq_isSymmetric D).eigenvectorBasis hm) i‖ = 1 :=
    ((Tq_isSymmetric D).eigenvectorBasis hm).orthonormal.1 i
  have h := Tq_norm_le D (((Tq_isSymmetric D).eigenvectorBasis hm) i)
  rw [(Tq_isSymmetric D).apply_eigenvectorBasis hm i, hnorm] at h
  simpa [norm_smul, hnorm] using h

/-- **EVERY TRANSFER EIGENVALUE IS NONNEGATIVE — GIVEN POSITIVITY OF `T`, WHICH IS A SEPARATE
HYPOTHESIS.**

`hpos` is `0 ≤ ⟨x, Tx⟩`: reflection positivity about a HALF-INTEGER time plane. It does not follow
from `T_contract`, which bounds `|λ|` and says nothing about its sign, and a negative eigenvalue is a
perfectly good transfer operator — it is an oscillating correlator. Stated as an explicit hypothesis
so that the second application of the physics is visible. -/
theorem eigenvalue_nonneg (hm : Module.finrank ℝ (GNS D.toReflForm) = m)
    (hpos : ∀ x : A, 0 ≤ D.form x (D.T x)) (i : Fin m) :
    0 ≤ (Tq_isSymmetric D).eigenvalues hm i := by
  have hq : ∀ q : GNS D.toReflForm, 0 ≤ inner ℝ q (Tq D q) := by
    intro q
    obtain ⟨x, rfl⟩ := GNS.exists_mk q
    simpa using hpos x
  have h := hq (((Tq_isSymmetric D).eigenvectorBasis hm) i)
  rw [(Tq_isSymmetric D).apply_eigenvectorBasis hm i, real_inner_smul_right,
    real_inner_self_eq_norm_mul_norm,
    ((Tq_isSymmetric D).eigenvectorBasis hm).orthonormal.1 i] at h
  simpa using h

end TransferData

/-! ## Part 6 — the periodic spectral form

`Spectral.PeriodicSpectralForm` is the object the flagship's `hdecay` would have to be a statement
about. This section builds one out of a transfer operator, which is what was missing.
-/

namespace TransferData

variable (D : TransferData A) [FiniteDimensional ℝ (GNS D.toReflForm)] {m : ℕ}

/-- **THE PERIODIC CORRELATOR OF A VECTOR**, `ρ(d) = ⟨v, T^d v⟩ + ⟨v, T^{per−d} v⟩`.

**Read this definition for exactly what it is.** With `v = A Ω` the first term is
`⟨Ω, A T^d A Ω⟩`, the zero-temperature correlator, and the second is its image under `d ↦ per − d`.
Adding them makes `ρ` symmetric under the torus reflection, which is the property
`Spectral.flat_of_aperiodic` shows the half-line shape `⟨Ω, A T^d A Ω⟩` cannot have on its own
without going flat.

It is NOT the exact finite-volume thermal correlator. That is `Tr(A T^d A T^{per−d}) / Tr(T^{per})`,
which in the eigenbasis is a DOUBLE sum `∑_{i,j} |A_{ij}|² λ_i^d λ_j^{per−d}` — two spectral indices,
not one — and so is not of `PeriodicSpectralForm`'s shape at all. This definition is the
ground-state-dominant term of that double sum (the `j = vacuum` row, where `λ_j = 1`), symmetrised.
Closing that gap is named in the module docstring as the next obligation.

DERIVED: nothing numeric. `per` is the caller's period and the two terms are the two ways round the
circle. -/
noncomputable def periodicCorr (D : TransferData A) (v : GNS D.toReflForm) (per : ℕ)
    (d : Fin per) : ℝ :=
  inner ℝ v (((Tq D) ^ (d : ℕ)) v) + inner ℝ v (((Tq D) ^ (per - (d : ℕ))) v)

/-- **THE TRANSFER OPERATOR SUPPLIES A `Spectral.PeriodicSpectralForm`.**

This is the object the flagship's `hdecay` quantifies over, no longer free: `w` is a square of an
inner product (reflection positivity's content), `lam` is the transfer spectrum, and `hrep` says the
correlator IS the form at every lag the period resolves. `P` and `m` of `ym_mass_gap_at_floor` are
not supplied to it — they ARE `w` and `lam`.

What it costs: finite dimension of the GNS space, and `hpos` — positivity of the transfer operator,
which is a SECOND application of reflection positivity and does not follow from contractivity.

What it does NOT do: prove any bound on `lam`. `hdecay` is the statement `lam k ≤ e^{−(κ₀−μ)}` about
THIS family, and nothing here establishes it.

DERIVED: nothing numeric; every field is read off the spectral decomposition. -/
noncomputable def periodicSpectralForm_of_transfer
    (hm : Module.finrank ℝ (GNS D.toReflForm) = m)
    (hpos : ∀ x : A, 0 ≤ D.form x (D.T x)) (per : ℕ) (v : GNS D.toReflForm) :
    Spectral.PeriodicSpectralForm per (periodicCorr D v per) where
  Idx := Fin m
  w i := (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) v) ^ 2
  lam i := (Tq_isSymmetric D).eigenvalues hm i
  hw i := sq_nonneg _
  hlam0 i := eigenvalue_nonneg D hm hpos i
  hlam1 i := le_of_abs_le (abs_eigenvalue_le_one D hm i)
  hrep d := by
    rw [periodicCorr, inner_pow_expand D hm v (d : ℕ), inner_pow_expand D hm v (per - (d : ℕ)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **PARSEVAL**: the spectral weights of `v` sum to `‖v‖²`. It is `inner_pow_expand` at `k = 0`.

DERIVED: the exponents are `0` and `2`; nothing is chosen. -/
theorem sum_weights (hm : Module.finrank ℝ (GNS D.toReflForm) = m) (v : GNS D.toReflForm) :
    ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) v) ^ 2 = ‖v‖ * ‖v‖ := by
  have h := inner_pow_expand D hm v 0
  simp only [pow_zero, mul_one] at h
  rw [← h]
  exact real_inner_self_eq_norm_mul_norm v

omit [FiniteDimensional ℝ (GNS D.toReflForm)] in
/-- **THE VACUUM CORRELATOR DOES NOT DECAY**: `ρ(d) = 2` at every lag.

`T Ω = Ω` and `‖Ω‖ = 1`, so both terms of the periodic shape are one. A correlator with a perfectly
good `PeriodicSpectralForm` and no decay at all — which is why the form on its own carries no gap,
and why a gap statement has to be about the CONNECTED correlator.

DERIVED: the `2` is the two terms of the periodic shape, each equal to `⟨Ω,Ω⟩ = 1`. -/
theorem periodicCorr_vac (per : ℕ) (d : Fin per) :
    periodicCorr D (vacGNS D) per d = 2 := by
  have hpow : ∀ k : ℕ, ((Tq D) ^ k) (vacGNS D) = vacGNS D := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : ((Tq D) ^ (k + 1)) (vacGNS D) = Tq D (((Tq D) ^ k) (vacGNS D)) := by
          rw [pow_succ']; rfl
        rw [hstep, ih, Tq_vacGNS]
  have hnorm : inner ℝ (vacGNS D) (vacGNS D) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_mul_norm, norm_vacGNS]; ring
  rw [periodicCorr, hpow, hpow, hnorm]
  ring

/-- **ONE IS ALWAYS IN THE TRANSFER SPECTRUM, SO `hdecay` CANNOT BE READ OVER THE WHOLE SPECTRUM.**

If every eigenvalue is at most `r`, then `r ≥ 1`. The vacuum is an eigenvector at eigenvalue exactly
one (`Tq_vacGNS`) and it is a unit vector (`norm_vacGNS`), so its weight cannot be pushed below `r`.

**What this says about the flagship.** `Complete.ym_mass_gap_at_floor`'s `hdecay` asks
`‖m β k‖ ≤ e^{−(κ₀−μ)} < 1` for every mode `k`, and `Spectral.periodic_decay_le` asks
`∀ k, lam k ≤ r`. Read over the FULL transfer spectrum both are unsatisfiable — not hard, but FALSE,
by this theorem. The spectrum they can be about is the one on `Ω^⊥`: the connected correlator, with
the vacuum subtracted. `Spectral.PeriodicSpectralForm` as it stands carries no field excluding the
vacuum mode, so a form built from a genuine transfer operator (`periodicSpectralForm_of_transfer`)
always contains it and always falsifies `periodic_decay_le`'s hypothesis.

Proving this needed no positivity of `T` and no gap — only normalisation.

DERIVED: the `1` is the vacuum eigenvalue, which is the total mass of a probability measure. -/
theorem one_le_of_eigenvalues_le (hm : Module.finrank ℝ (GNS D.toReflForm) = m) {r : ℝ}
    (hgap : ∀ i : Fin m, (Tq_isSymmetric D).eigenvalues hm i ≤ r) : 1 ≤ r := by
  have hTv : ((Tq D) ^ 1) (vacGNS D) = vacGNS D := by simpa using Tq_vacGNS D
  have hv := inner_pow_expand D hm (vacGNS D) 1
  rw [hTv] at hv
  have hnorm : inner ℝ (vacGNS D) (vacGNS D) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_mul_norm, norm_vacGNS]; ring
  have hsum : ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) (vacGNS D)) ^ 2 = 1 := by
    rw [sum_weights D hm (vacGNS D), norm_vacGNS]; ring
  rw [hnorm] at hv
  calc (1 : ℝ) = ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) (vacGNS D)) ^ 2
          * ((Tq_isSymmetric D).eigenvalues hm i) ^ 1 := hv
    _ ≤ ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) (vacGNS D)) ^ 2 * r := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hw := sq_nonneg (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) (vacGNS D))
        have := hgap i
        nlinarith
    _ = r := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **AND THIS IS EXACTLY WHERE `hdecay` WOULD ENTER.**

Given a bound `r` on the transfer spectrum, the correlator decays geometrically out to half the
period — `Spectral.periodic_decay_le` applied to the form just built. Taking `r = e^{−(κ₀−μ)}` makes
the hypothesis `hgap` the flagship's `hdecay`, now a statement about the eigenvalues of a DEFINED
operator rather than about a free family.

Nothing here proves `hgap`. It names it.

DERIVED: the `2` is the two terms of the periodic shape, inherited from `Spectral.periodic_decay_le`;
the halving of the period is where a torus correlator turns back up. -/
theorem periodic_decay_of_transfer
    (hm : Module.finrank ℝ (GNS D.toReflForm) = m)
    (hpos : ∀ x : A, 0 ≤ D.form x (D.T x)) (per : ℕ) (v : GNS D.toReflForm)
    {r : ℝ} (hr : 0 ≤ r) (hgap : ∀ i : Fin m, (Tq_isSymmetric D).eigenvalues hm i ≤ r)
    (d : Fin per) (hhalf : 2 * (d : ℕ) ≤ per) :
    periodicCorr D v per d
      ≤ 2 * (∑ i : Fin m, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) v) ^ 2)
          * r ^ (d : ℕ) :=
  -- the gap is now required only on modes that CONTRIBUTE (a zero-weight vacuum mode is harmless),
  -- so a bound on every eigenvalue is more than enough
  Spectral.periodic_decay_le (periodicSpectralForm_of_transfer D hm hpos per v)
    (fun k _ => hgap k) hr d hhalf

end TransferData

#print axioms reflForm_symm
#print axioms reflForm_one_one
#print axioms ReflForm.cauchy_schwarz
#print axioms ReflForm.form_eq_zero_of_mem_null
#print axioms GNS.mk_eq_zero_iff
#print axioms GNS.norm_mk_mul_norm_mk
#print axioms TransferData.Tq_isSymmetric
#print axioms TransferData.Tq_vacGNS
#print axioms TransferData.norm_vacGNS
#print axioms TransferData.Tq_norm_le
#print axioms TransferData.norm_TqL_le_one
#print axioms isSymmetric_pow
#print axioms TransferData.inner_pow_expand
#print axioms TransferData.abs_eigenvalue_le_one
#print axioms TransferData.eigenvalue_nonneg
#print axioms TransferData.sum_weights
#print axioms TransferData.periodicCorr_vac
#print axioms TransferData.one_le_of_eigenvalues_le
#print axioms TransferData.periodicSpectralForm_of_transfer
#print axioms TransferData.periodic_decay_of_transfer

end MassGap.Transfer
