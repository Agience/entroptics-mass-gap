import Mathlib

/-!
# MassGap.WightmanData — Osterwalder–Schrader reconstruction, stated between two structures

`OSData` is Euclidean reconstruction input as a structure: a normed real space of test configurations, a
reflection, a **continuous bilinear** Schwinger form, a translation action, OS1/OS2/OS3 stated about that
form, and non-degeneracy. `WightmanQFT` is Gårding–Wightman output as a structure: a complex Hilbert space,
a unit vacuum vector, a unitary representation of the translation group `ℝ⁴` fixing the vacuum, a bounded
self-adjoint Hamiltonian annihilating the vacuum with spectrum in the closed right half-plane, and a family
of field operators on a dense common domain indexed by Schwartz test functions on `ℝ⁴`.
`os_reconstruction_wightman` is the reconstruction stated between the two, and it is the tree's only
reconstruction axiom.

Both sides are stated as data rather than as propositions, and the structures are checked at both
ends. `osData_test_nontrivial` derives `Nontrivial D.Test` from bilinearity together with
`os_nontriv`, and `osData_S_ne_zero` that the form is not the zero map; `reconstructed_space_nontrivial`,
`reconstructed_vacuum_energy_zero` and `reconstructed_ham_not_injective` read facts back out of the
conclusion. `trivialOSData` and `trivialWightmanQFT` are one-dimensional inhabitants of the two
structures, and `wightmanQFTData_nonempty` records that the axiom's target type is not empty, so the
axiom cannot on its own prove `False`.

Scope.
* This module does not prove Osterwalder–Schrader reconstruction; `os_reconstruction_wightman` is an
  axiom.
* `WightmanQFT` is not the Wightman axioms. Its docstring lists what it carries and what it omits.
* The axiom's type is `OSData → WightmanQFTData` and mentions `D` once, so nothing in it relates the
  input to the output. `reconstruction_type_is_inhabited` exhibits `fun _ => trivialWightmanQFTData`
  at that exact type. A consumer of the axiom learns that some `WightmanQFTData` exists, not that a
  particular Euclidean datum yields a particular quantum theory; a linking clause relating `D.S` to
  the output's expectation values would change that, and would make
  `reconstruction_type_is_inhabited` stop typechecking.
* `reconstructed_vacuum_energy_zero` and `reconstructed_space_nontrivial` are theorems about an
  arbitrary `WightmanQFTData`, so they hold of the constant term as well.
* `MassGap.WilsonOS` constructs `OSData`: `osDataOfReflForm` from any `Transfer.ReflForm` on a real
  module evaluated on a finite family, and `wilsonOSData` from that at
  `ReflectionStrong.wilsonGibbsReflForm`, the `SU(N)` Wilson Gibbs reflected pairing on the slab
  algebra, at every real `β`. `wilsonOSData_S` and `osDataOfReflForm_S` are `rfl` identities giving
  `D.S c c' = P.form (combo v c) (combo v c')`, so the Schwinger form IS the Wilson form.
  `wilson_reconstructed_nontrivial` and `wilson_reconstructed_vacuum_energy_zero` carry that datum
  through the axiom.

  Two features of `Transfer.ReflForm` shape how: it carries no norm, and `ReflectionStrong` shows a
  one-step time translation is not an endomorphism of the slab algebra, the shift carrying a
  transverse link out of the module. `osDataOfReflForm` takes `Test` to be the coefficient space
  `EuclideanSpace ℝ (Fin k)` of a finite family rather than the module, which supplies the norm, and
  sets `transl` to the identity, which `LatticeTranslNoGo.transl_eq_id_of_finite_order` shows is
  forced on a lattice. What is still absent is the linking clause above.

  `Measure.continuum_of_family` supplies an index type and none of the other twelve fields;
  `LatticeYMFamily`'s `os_rp` is nonnegativity of a real-valued function and its `os_euc`/`os_perm`
  are invariance of that function under a group action instantiated at the finite
  `Equiv.Perm (Fin 4)`, which are different statements from `os2`, `os1` and `os3`.
-/

namespace MassGap.WightmanData

/-! ## Part 1 — Euclidean data and Wightman data as structures

Euclidean spacetime, and the test functions the field operators are smeared with. -/

/-- Euclidean spacetime `ℝ⁴`.

DERIVED: `4` is the dimension of spacetime — the Clay problem's own, the same `d` the lattice side
is instantiated at (`bd (d := 4)` in `AreaLaw`). It is the number of coordinates, not a cutoff or a
resolution; `EuclideanSpace ℝ (Fin 4)` is all of `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Real Schwartz test functions on `E4`, the index set of the smeared field operators of
`WightmanQFT`.

DERIVED: no numeral occurs; the dimension is inside `E4`. -/
abbrev TestFn : Type := SchwartzMap E4 ℝ

/-- **Euclidean Osterwalder–Schrader data.** What a reconstruction consumes, as data rather than as four
inequalities about an arbitrary real-valued function.

`Test` is the space of smeared field arrangements. It is a real normed space, so `S`'s continuity IS the
temperedness bound (OS0): `S : Test →L[ℝ] Test →L[ℝ] ℝ` bounds a bilinear form, and `osData_bounded` reads
that bound back out.

`S f g` is the Schwinger pairing; `os2` is reflection positivity of the reflected form `S (θ f) f`, which
is a Gram condition because `S` is bilinear — a condition on a form, which a one-argument real-valued
function on an index set cannot express.

`os_nontriv` is the non-degeneracy that makes the structure refuse a subsingleton instance
(`osData_test_nontrivial`).

DERIVED: the one numeral is `0`, appearing three times: as the vector at which `transl` is required
to act as the identity (`transl_zero`), as the lower bound in the reflection-positivity field `os2`,
and as the value the reflected form is required to avoid in `os_nontriv`. -/
structure OSData where
  /-- Test configurations: smeared field arrangements, a real normed space. -/
  Test : Type
  [normedTest : NormedAddCommGroup Test]
  [spaceTest : NormedSpace ℝ Test]
  /-- Euclidean time reflection `θ` on test configurations. -/
  theta : Test →L[ℝ] Test
  /-- `θ` is an involution. -/
  theta_invol : ∀ f, theta (theta f) = f
  /-- The Schwinger form. Continuity IS the temperedness bound (OS0). -/
  S : Test →L[ℝ] Test →L[ℝ] ℝ
  /-- The translation action of `ℝ⁴` on test configurations. -/
  transl : E4 → (Test →L[ℝ] Test)
  /-- The action is unital. -/
  transl_zero : ∀ f, transl 0 f = f
  /-- The action is additive. -/
  transl_add : ∀ a b f, transl (a + b) f = transl a (transl b f)
  /-- **OS1 — Euclidean invariance** (translations). -/
  os1 : ∀ a f g, S (transl a f) (transl a g) = S f g
  /-- **OS2 — reflection positivity**: the reflected quadratic form is nonnegative. -/
  os2 : ∀ f, 0 ≤ S (theta f) f
  /-- **OS3 — symmetry** of the Schwinger form. -/
  os3 : ∀ f g, S f g = S g f
  /-- **Non-degeneracy**: the theory is not the zero theory. -/
  os_nontriv : ∃ f, S (theta f) f ≠ 0

/-- `NormedAddCommGroup D.Test`, from the instance-implicit field `D.normedTest`. Registered as an
 instance because the projection of an instance-implicit structure field is not found by instance
resolution on its own.

DERIVED: no numeral occurs. -/
instance instNormedAddCommGroupOSDataTest (D : OSData) : NormedAddCommGroup D.Test := D.normedTest

/-- `NormedSpace ℝ D.Test`, from the instance-implicit field `D.spaceTest`, registered for the same
reason as the previous instance.

DERIVED: no numeral occurs. -/
instance instNormedSpaceOSDataTest (D : OSData) : NormedSpace ℝ D.Test := D.spaceTest

/-- `|D.S (D.theta f) f| ≤ ‖D.S‖ * ‖D.theta f‖ * ‖f‖`: the reflected form is bounded by the operator
norm of `S`. Two applications of `ContinuousLinearMap.le_opNorm`, one in each argument. The bound is
a consequence of `S` being a continuous bilinear map, so it is not a separate field of the structure.

DERIVED: no numeral occurs in the statement. -/
theorem osData_bounded (D : OSData) (f : D.Test) :
    |D.S (D.theta f) f| ≤ ‖D.S‖ * ‖D.theta f‖ * ‖f‖ := by
  have h1 : ‖D.S (D.theta f) f‖ ≤ ‖D.S (D.theta f)‖ * ‖f‖ :=
    (D.S (D.theta f)).le_opNorm f
  have h2 : ‖D.S (D.theta f)‖ ≤ ‖D.S‖ * ‖D.theta f‖ := D.S.le_opNorm (D.theta f)
  calc |D.S (D.theta f) f| = ‖D.S (D.theta f) f‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖D.S (D.theta f)‖ * ‖f‖ := h1
    _ ≤ ‖D.S‖ * ‖D.theta f‖ * ‖f‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg f)

/-- `D.S ≠ 0` for every `OSData D`. If `S` were zero, the reflected form would vanish at every test
function, contradicting `os_nontriv`.

DERIVED: the one numeral is `0`, the zero continuous bilinear map the form is shown to differ
from. -/
theorem osData_S_ne_zero (D : OSData) : D.S ≠ 0 := by
  intro h
  obtain ⟨f, hf⟩ := D.os_nontriv
  exact hf (by rw [h]; simp)

/-- `Nontrivial D.Test` for every `OSData D`: the test space has at least two elements, so no
`OSData` is built on `Unit`, on a subsingleton, or on the zero module. Bilinearity gives
`S (θ 0) 0 = 0`, while `os_nontriv` supplies an `f` at which the reflected form is nonzero, so that
`f` differs from `0`.

DERIVED: no numeral occurs in the statement; the `0` the proof compares against is the zero of
`D.Test`. -/
theorem osData_test_nontrivial (D : OSData) : Nontrivial D.Test := by
  obtain ⟨f, hf⟩ := D.os_nontriv
  refine ⟨⟨f, 0, ?_⟩⟩
  rintro rfl
  exact hf (by simp)

/-- `¬ Subsingleton D.Test`: the previous fact in the form that names what a subsingleton
instantiation would have to supply, an `f` with `S (θ f) f ≠ 0` inside a type all of whose elements
are equal.

DERIVED: no numeral occurs in the statement. -/
theorem osData_test_not_subsingleton (D : OSData) : ¬ Subsingleton D.Test := by
  intro h
  obtain ⟨f, hf⟩ := D.os_nontriv
  rw [h.allEq f 0] at hf
  simp at hf

/-- **`OSData` IS inhabited, by a one-dimensional form with no physics in it.** `Test := ℝ`, `θ = id`,
`S f g = f·g`, translations acting trivially. This is the limit of what the structure refuses: it rules out
every subsingleton instantiation (`osData_test_nontrivial`), and it does not rule out a finite-dimensional
toy.

Recorded so the claim made about the structure stays the claim that is checked. What `OSData` demands is
that reflection positivity be a condition on a bilinear form and that the form be nonzero — not that only a
Yang–Mills theory satisfies it.

DERIVED: neither digit describes a theory; both are the structure's own obligations read at
`Test := ℝ`. `0` is the zero of `ℝ` in the reflection-positivity field `os2`, where `0 ≤ f * f` is
`mul_self_nonneg`. `1` is the unit of `ℝ` supplied as the witness in `os_nontriv`, which asks for some
test function with `S (θ f) f ≠ 0` — the reflected form, not `S f f`. Here `θ` is the identity and
`S f g = f * g`, so the obligation collapses to `1 * 1 ≠ 0` and any nonzero real would serve; the
unit is the one at hand. Nothing is tuned, because the point of this definition is that it has
no physics in it. -/
noncomputable def trivialOSData : OSData where
  Test := ℝ
  theta := ContinuousLinearMap.id ℝ ℝ
  theta_invol := fun _ => rfl
  S := ContinuousLinearMap.mul ℝ ℝ
  transl := fun _ => ContinuousLinearMap.id ℝ ℝ
  transl_zero := fun _ => rfl
  transl_add := fun _ _ _ => rfl
  os1 := fun _ f g => by show f * g = f * g; rfl
  os2 := fun f => by show (0 : ℝ) ≤ f * f; exact mul_self_nonneg f
  os3 := fun f g => by show f * g = g * f; exact mul_comm f g
  os_nontriv := ⟨1, by show (1 : ℝ) * 1 ≠ 0; norm_num⟩

/-- `Nonempty OSData`, witnessed by `trivialOSData`: the reconstruction axiom's hypothesis type is
inhabited.

DERIVED: no numeral occurs in the statement. -/
theorem osData_nonempty : Nonempty OSData := ⟨trivialOSData⟩

/-- **Gårding–Wightman data on a fixed Hilbert space `H`**, at the fidelity Mathlib v4.31 supports, in the
shape `Reconstruction.GappedQuantumTheory` uses for the operator-theoretic side: a quantum theory as data.

What is carried. A complex Hilbert space `H` (the parameter, with completeness); a vacuum `vac` that is a
unit vector; a representation `U` of the translation group `ℝ⁴` by surjective linear isometries, unital and
additive, fixing the vacuum; a Hamiltonian `ham`, self-adjoint, annihilating the vacuum, with every spectral
value in the closed right half-plane (`H ≥ 0`); and field operators `field`, indexed by real Schwartz test
functions on `ℝ⁴`, acting on a dense common domain `dom` that contains the vacuum, additive in the test
function.

What is not carried, and is therefore not claimed. (i) `ham` is bounded (`H →L[ℂ] H`); a Wightman
Hamiltonian is unbounded, and Mathlib v4.31 has no unbounded self-adjoint operator theory to state this in.
(ii) There is no Lorentz or Euclidean rotation subgroup — only translations. (iii) `ham` is not tied to `U`:
the statement that `ham` generates the time translation is absent. (iv) The fields are additive in the test
function but not stated ℝ-linear, not stated symmetric, not stated covariant under `U`, and not stated local
(no spacelike commutativity). (v) Uniqueness of the vacuum and cyclicity of the vacuum for the field algebra
are absent, as are the Wightman distributions themselves and their positivity and spectral conditions.

So this is a Hilbert space with a vacuum, a translation representation, a nonnegative Hamiltonian and fields
on a dense domain. It is not the Wightman axioms.

DERIVED: two numerals. `1` is the norm of the vacuum in `vac_norm`, which is what makes it a unit
vector. `0` is the translation vector at which `U` acts as the identity (`U_zero`), the value of
`ham vac` (`ham_vac`), and the lower bound on the real part of every spectral value
(`ham_spectrum_nonneg`). -/
structure WightmanQFT (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The vacuum vector. -/
  vac : H
  /-- The vacuum is a unit vector. -/
  vac_norm : ‖vac‖ = 1
  /-- The unitary representation of the translation group `ℝ⁴`. -/
  U : E4 → (H ≃ₗᵢ[ℂ] H)
  /-- `U 0 = 1`. -/
  U_zero : ∀ x, U 0 x = x
  /-- `U (a + b) = U a ∘ U b`. -/
  U_add : ∀ a b x, U (a + b) x = U a (U b x)
  /-- The vacuum is translation invariant. -/
  U_vac : ∀ a, U a vac = vac
  /-- The Hamiltonian. Bounded — see the structure docstring. -/
  ham : H →L[ℂ] H
  /-- The Hamiltonian is self-adjoint. -/
  ham_selfAdjoint : IsSelfAdjoint ham
  /-- The vacuum has energy zero: `H Ω = 0`. -/
  ham_vac : ham vac = 0
  /-- The spectral condition `H ≥ 0`: every spectral value lies in the closed right half-plane. -/
  ham_spectrum_nonneg : ∀ z ∈ spectrum ℂ ham, 0 ≤ z.re
  /-- The Gårding domain: a common dense domain for the field operators. -/
  dom : Submodule ℂ H
  /-- The common domain is dense. -/
  dom_dense : Dense (dom : Set H)
  /-- The vacuum lies in the common domain. -/
  vac_mem_dom : vac ∈ dom
  /-- The smeared field operators, indexed by Schwartz test functions on `ℝ⁴`, as operators on the common
  domain. -/
  field : TestFn → (dom →ₗ[ℂ] dom)
  /-- The fields are additive in the test function. -/
  field_add : ∀ f g, field (f + g) = field f + field g

/-- A `WightmanQFT` with its Hilbert space bundled as a field, so the space is part of the value
rather than a parameter. This is the form a reconstruction produces, since the Hilbert space is an
output of the construction.

DERIVED: no numeral occurs. -/
structure WightmanQFTData where
  /-- The Hilbert space of states. -/
  Space : Type
  [normed : NormedAddCommGroup Space]
  [hilb : InnerProductSpace ℂ Space]
  [complete : CompleteSpace Space]
  /-- The theory on it. -/
  qft : WightmanQFT Space

/-- `NormedAddCommGroup Q.Space`, from the instance-implicit field `Q.normed`, registered so that
 instance resolution finds it.

DERIVED: no numeral occurs. -/
instance instNormedAddCommGroupWightmanSpace (Q : WightmanQFTData) :
    NormedAddCommGroup Q.Space := Q.normed

/-- `InnerProductSpace ℂ Q.Space`, from the instance-implicit field `Q.hilb`.

DERIVED: no numeral occurs. -/
instance instInnerProductSpaceWightmanSpace (Q : WightmanQFTData) :
    InnerProductSpace ℂ Q.Space := Q.hilb

/-- `CompleteSpace Q.Space`, from the instance-implicit field `Q.complete`.

DERIVED: no numeral occurs. -/
instance instCompleteSpaceWightmanSpace (Q : WightmanQFTData) : CompleteSpace Q.Space := Q.complete

/-- **`WightmanQFT` is inhabited**, by the one-dimensional theory on `ℂ`: vacuum `1`, trivial translation
representation, zero Hamiltonian, fields all zero on the whole space.

Two things follow, and they pull in opposite directions. (i) The target type of
`os_reconstruction_wightman` is not empty, so that axiom cannot on its own prove `False` — the check a
data-valued axiom needs and a `Prop`-valued one does not. (ii) Satisfying `WightmanQFT` is not by itself
evidence of a Yang–Mills theory: the structure carries a vacuum, a positive Hamiltonian and a dense field
domain, and this witness has all three with nothing in them.

DERIVED: both digits are the units of `ℂ`, not physical quantities. `1` is the multiplicative unit
serving as the vacuum, and it is forced rather than picked: `vac_norm` demands a unit vector, and in
`ℂ` the unit is a unit vector. `0` is the additive identity, used three times for the same reason —
the Hamiltonian is the zero operator, so `ham_vac` and `ham_spectrum_nonneg` hold with the spectrum
`{0}`, and the fields are the zero operator. That is the content of the witness: it is the theory
with nothing in it, so every number in it is an identity element. -/
noncomputable def trivialWightmanQFT : WightmanQFT ℂ where
  vac := 1
  vac_norm := by simp
  U := fun _ => LinearIsometryEquiv.refl ℂ ℂ
  U_zero := by simp
  U_add := by simp
  U_vac := by simp
  ham := 0
  ham_selfAdjoint := by simp [IsSelfAdjoint]
  ham_vac := by simp
  ham_spectrum_nonneg := by
    intro z hz
    have hz0 : z = 0 := by
      by_contra h
      refine spectrum.mem_iff.mp hz ?_
      simpa using (isUnit_iff_ne_zero.mpr h).map (algebraMap ℂ (ℂ →L[ℂ] ℂ))
    simp [hz0]
  dom := ⊤
  dom_dense := by simp
  vac_mem_dom := by simp
  field := fun _ => 0
  field_add := by simp

/-- `trivialWightmanQFT` bundled with its space `ℂ` as a `WightmanQFTData`.

DERIVED: no numeral occurs. -/
noncomputable def trivialWightmanQFTData : WightmanQFTData where
  Space := ℂ
  qft := trivialWightmanQFT

/-- `Nonempty WightmanQFTData`, witnessed by `trivialWightmanQFTData`: the axiom's target type is
inhabited, so `os_reconstruction_wightman` cannot on its own prove `False`.

DERIVED: no numeral occurs in the statement. -/
theorem wightmanQFTData_nonempty : Nonempty WightmanQFTData := ⟨trivialWightmanQFTData⟩

/-! ## Part 2 — the reconstruction -/

/-- **Osterwalder–Schrader reconstruction, stated between the two structures (named axiom).**
K. Osterwalder, R. Schrader, Commun. Math. Phys. **31** (1973) 83 and **42** (1975) 281; textbook form
J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed. (Springer 1987).

This is an axiom, not a proof; the theorem it names is research-level and is not formalised here. What it
states, on each side:

* its hypothesis is a structure that no subsingleton inhabits (`osData_test_nontrivial`), whose form is
  bilinear and continuous, and whose reflection positivity is therefore a Gram condition rather than
  nonnegativity of an arbitrary function;
* its conclusion is data, from which a vacuum, a translation representation, a Hamiltonian and a dense
  field domain can be read (`reconstructed_vacuum_energy_zero`, `reconstructed_space_nontrivial`), rather
  than an opaque `Prop`.

Scope. The type `(D : OSData) : WightmanQFTData` mentions `D` once, so nothing in it relates the
input to the output. `trivialWightmanQFTData` is a term of the conclusion's type, so
`fun _ => trivialWightmanQFTData` has this exact type; `reconstruction_type_is_inhabited` below
exhibits it. `wightmanQFTData_nonempty` is the corresponding soundness check for a data-valued
axiom, and it passes. A field or hypothesis relating `D.S` to the output's expectation values would
be what ties the two ends together; none is present.

DERIVED: bibliographic. The statement `(D : OSData) : WightmanQFTData` contains no numeral at all.
Every digit in this doc comment — `31`, `1973`, `83`, `42`, `1975`, `281`, `1987` — is part of the
citation at the top: volume, year and first page of the two Osterwalder–Schrader papers, and the
year of the Glimm–Jaffe edition. They are not constants, nothing is decided by them, and they are
left in ordinary citation form because a reader needs to be able to follow them to the papers. -/
axiom os_reconstruction_wightman (D : OSData) : WightmanQFTData

/-- A term of `os_reconstruction_wightman`'s exact type, `OSData → WightmanQFTData`, built as the
constant function at `trivialWightmanQFTData`.

Scope: this bounds what the axiom can deliver — nothing in `OSData → WightmanQFTData` relates the
input to the output. It is not a statement about the axiom's soundness, for which
`wightmanQFTData_nonempty` is the check. Stated as a declaration rather than a remark so that adding
a field tying `D.S` to the output's expectation values would make this term stop typechecking.

DERIVED: no numeral occurs. -/
noncomputable def reconstruction_type_is_inhabited : OSData → WightmanQFTData :=
  fun _ => trivialWightmanQFTData

#print axioms reconstruction_type_is_inhabited


/-- `Q.qft.vac ≠ 0` for every `WightmanQFTData Q`: the vacuum is nonzero, since `vac_norm` makes its
norm `1` and the zero vector has norm `0`.

DERIVED: `0` is the vector the vacuum is shown to differ from; the `1` of `vac_norm` and the `0` of
`norm_zero` are in the proof. -/
theorem reconstructed_vac_ne_zero (Q : WightmanQFTData) : Q.qft.vac ≠ 0 := by
  intro h
  have hn : ‖Q.qft.vac‖ = 1 := Q.qft.vac_norm
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- `Nontrivial Q.Space` for every `WightmanQFTData Q`, witnessed by the vacuum and `0` through
`reconstructed_vac_ne_zero`.

DERIVED: no numeral occurs in the statement. -/
theorem reconstructed_space_nontrivial (Q : WightmanQFTData) : Nontrivial Q.Space :=
  ⟨⟨Q.qft.vac, 0, reconstructed_vac_ne_zero Q⟩⟩

/-- `(os_reconstruction_wightman D).qft.ham (os_reconstruction_wightman D).qft.vac = 0`, the
`ham_vac` field of the axiom's output read back out.

DERIVED: the one numeral is `0`, the value of the Hamiltonian on the vacuum. -/
theorem reconstructed_vacuum_energy_zero (D : OSData) :
    (os_reconstruction_wightman D).qft.ham (os_reconstruction_wightman D).qft.vac = 0 :=
  (os_reconstruction_wightman D).qft.ham_vac

/-- `¬ Function.Injective Q.qft.ham` for every `WightmanQFTData Q`: the Hamiltonian annihilates the
vacuum (`ham_vac`) and the vacuum is nonzero (`reconstructed_vac_ne_zero`), so it is not injective.
The `ham_spectrum_nonneg` field is not used.

DERIVED: no numeral occurs in the statement. -/
theorem reconstructed_ham_not_injective (Q : WightmanQFTData) :
    ¬ Function.Injective Q.qft.ham := by
  intro hinj
  refine reconstructed_vac_ne_zero Q (hinj ?_)
  rw [Q.qft.ham_vac, map_zero]

/-- Both ends of the axiom are non-degenerate: `Nontrivial D.Test` and
`Nontrivial (os_reconstruction_wightman D).Space`, from `osData_test_nontrivial` and
`reconstructed_space_nontrivial`. Neither end is met by a one-point object.

DERIVED: no numeral occurs in the statement. -/
theorem os_reconstruction_wightman_is_not_vacuous (D : OSData) :
    Nontrivial D.Test ∧ Nontrivial (os_reconstruction_wightman D).Space :=
  ⟨osData_test_nontrivial D, reconstructed_space_nontrivial _⟩

#print axioms OSData
#print axioms trivialOSData
#print axioms osData_nonempty
#print axioms trivialWightmanQFT
#print axioms trivialWightmanQFTData
#print axioms wightmanQFTData_nonempty
#print axioms osData_bounded
#print axioms osData_S_ne_zero
#print axioms osData_test_nontrivial
#print axioms osData_test_not_subsingleton
#print axioms WightmanQFT
#print axioms WightmanQFTData
#print axioms os_reconstruction_wightman
#print axioms reconstructed_vac_ne_zero
#print axioms reconstructed_space_nontrivial
#print axioms reconstructed_vacuum_energy_zero
#print axioms reconstructed_ham_not_injective
#print axioms os_reconstruction_wightman_is_not_vacuous

end MassGap.WightmanData
