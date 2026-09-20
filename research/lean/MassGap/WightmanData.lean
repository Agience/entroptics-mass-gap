import Mathlib
import MassGap.FullModel

/-!
# MassGap.WightmanData — the OS→Wightman row, and what its axiom actually asserts

Two things live here, and they are independent of each other.

## Part 1 — what `FullModel.os_reconstruction` proves today, machine-checked

`FullModel.lean:177` declares `WightmanTheory : Prop` as an axiom with no fields, and `FullModel.lean:192`
declares `os_reconstruction`, whose hypotheses are about an arbitrary `q : J → ℝ` for an arbitrary type `J`.
Nothing in the TYPE of `os_reconstruction` ties `q` to a Schwinger function, to a reflected form, or to
Yang–Mills. `wightmanTheory_of_zero_form` below discharges all four hypotheses at `q ≡ 0`, at arbitrary
`J`, `G`, `Pm` and arbitrary actions, so `WightmanTheory` follows from the axiom with no input whatever;
`wightman_of_model_is_the_trivial_proof` then closes the circle by `rfl`, since proof irrelevance makes
`MassGap.wightman_of_model M` and that zero-form discharge the same term.

This part adds no axiom of its own beyond the two it is measuring.

## Part 2 — a conclusion that carries information, and a hypothesis that refuses `Unit`

`OSData` is Euclidean reconstruction input as a STRUCTURE: a normed real space of test configurations, a
reflection, a **continuous bilinear** Schwinger form, a translation action, OS1/OS2/OS3 stated about that
form, and non-degeneracy. `WightmanQFT` is Gårding–Wightman output as a structure: a complex Hilbert space,
a unit vacuum vector, a unitary representation of the translation group `ℝ⁴` fixing the vacuum, a bounded
self-adjoint Hamiltonian annihilating the vacuum with spectrum in the closed right half-plane, and a family
of field operators on a dense common domain indexed by Schwartz test functions on `ℝ⁴`.
`os_reconstruction_wightman` is the reconstruction restated between the two.

**What this is NOT.** It is not a proof of Osterwalder–Schrader reconstruction, and `WightmanQFT` is not
the Wightman axioms. Read `WightmanQFT`'s field list for exactly what is carried; the omissions are listed
in its docstring and none of them is claimed here.

**Why the restatement is worth having even as an axiom.** `osData_test_nontrivial` proves that every
`OSData` has a test space with at least two elements, and `osData_S_ne_zero` that its form is not the zero
map — so the instantiation that discharges `os_reconstruction` cannot be repeated against this one. On the
other side `reconstructed_space_nontrivial`, `reconstructed_vacuum_energy_zero` and
`reconstructed_ham_not_injective` read facts back OUT of the conclusion, which an opaque `Prop` cannot
supply.

**And the limit of that claim, also checked.** `trivialOSData` and `trivialWightmanQFT` are one-dimensional
witnesses with no physics in them: `OSData` and `WightmanQFT` are both inhabited. So the restatement refuses
the subsingleton discharge and nothing stronger, and `wightmanQFTData_nonempty` is the check a DATA-valued
axiom needs — its target type is not empty, so it cannot on its own prove `False`.

Not imported by `MassGap.lean`; build it by name.
-/

namespace MassGap.WightmanData

/-! ## Part 1 — the standing axiom's conclusion follows from nothing -/

/-- **`WightmanTheory` is provable from `os_reconstruction` with no Yang–Mills input.** `J`, `G` and `Pm` are
instantiated at `Unit`, `q` at the constant `0`, and both group actions at the identity; all four
Osterwalder–Schrader hypotheses then close by `simp`/`rfl`/`le_refl`.

This is a statement about the axiom's TYPE, not about its docstring. Nothing in that type relates `q` to a
reflected Schwinger form. -/
theorem wightmanTheory_of_nothing : WightmanTheory :=
  os_reconstruction (J := Unit) (G := Unit) (Pm := Unit)
    (fun _ => (0 : ℝ)) (fun _ j => j) (fun _ j => j)
    ⟨0, fun _ => by simp⟩ (fun _ _ => rfl) (fun _ => le_refl (0 : ℝ)) (fun _ _ => rfl)

/-- **The vacuity is not an artefact of choosing `Unit`.** At an ARBITRARY test type, arbitrary Euclidean and
permutation types, and arbitrary actions, the zero form satisfies OS0–OS3 as `os_reconstruction` states them.
So it is the zero function that discharges the axiom, not the smallness of the index type: `hOS2 : ∀ j, 0 ≤ q j`
is nonnegativity of a function, which the zero function has, and not positive semidefiniteness of a form,
which the type cannot express because `q` has no second argument. -/
theorem wightmanTheory_of_zero_form (J G Pm : Type) (actE : G → J → J) (actP : Pm → J → J) :
    WightmanTheory :=
  os_reconstruction (fun _ : J => (0 : ℝ)) actE actP
    ⟨0, fun _ => by simp⟩ (fun _ _ => rfl) (fun _ => le_refl (0 : ℝ)) (fun _ _ => rfl)

/-- **Every proposition implies `WightmanTheory`.** A corollary of `wightmanTheory_of_nothing`, recorded
because it is the precise sense in which the conclusion carries no information: no hypothesis can be
load-bearing for it. -/
theorem wightmanTheory_of_anything (P : Prop) : P → WightmanTheory :=
  fun _ => wightmanTheory_of_nothing

/-- **`wightman_of_model` IS the trivial discharge.** Proof irrelevance is definitional in Lean 4, so the
theorem at `FullModel.lean:202` — the one that consumes `continuum_of_family`'s OS0–OS3 output — is the same
term as the `Unit` witness. `rfl` checks it. Whatever the model contributes, it does not contribute to this
proposition. -/
theorem wightman_of_model_is_the_trivial_proof (M : FullModel) :
    wightman_of_model M = wightmanTheory_of_nothing := rfl

/-! ## Part 2 — Euclidean data and Wightman data as structures

Euclidean spacetime, and the test functions the field operators are smeared with. -/

/-- Euclidean spacetime `ℝ⁴`.

DERIVED: `4` is the dimension of spacetime — the Clay problem's own, the same `d` the lattice side
is instantiated at (`bd (d := 4)` in `AreaLaw`). It is the number of coordinates, not a cutoff or a
resolution; `EuclideanSpace ℝ (Fin 4)` is all of `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Real Schwartz test functions on `ℝ⁴` — the index set of the smeared field operators. -/
abbrev TestFn : Type := SchwartzMap E4 ℝ

/-- **Euclidean Osterwalder–Schrader data.** What a reconstruction consumes, as data rather than as four
inequalities about an arbitrary real-valued function.

`Test` is the space of smeared field arrangements. It is a real normed space, so `S`'s continuity is the
temperedness bound (OS0) — where `os_reconstruction`'s `hOS0 : ∃ C, ∀ j, |q j| ≤ C` bounds a function
pointwise on an index set with no structure, `S : Test →L[ℝ] Test →L[ℝ] ℝ` bounds a BILINEAR FORM, and
`osData_bounded` reads that bound back out.

`S f g` is the Schwinger pairing; `os2` is reflection positivity of the reflected form `S (θ f) f`, which
is a Gram condition because `S` is bilinear — this is the field `os_reconstruction` cannot state, since its
`q` has no second argument.

`os_nontriv` is the non-degeneracy that makes the whole structure refuse a trivial instance
(`osData_test_nontrivial`). -/
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

/-- The test space of an `OSData` is a normed group. The projection of an instance-implicit field is not
picked up by instance resolution on its own, so it is registered here. -/
instance instNormedAddCommGroupOSDataTest (D : OSData) : NormedAddCommGroup D.Test := D.normedTest

/-- The test space of an `OSData` is a real normed space. -/
instance instNormedSpaceOSDataTest (D : OSData) : NormedSpace ℝ D.Test := D.spaceTest

/-- **OS0, read back out of the structure.** The reflected form is bounded by the operator norm of `S` —
the content `os_reconstruction`'s `hOS0` asserted about an arbitrary function is here a consequence of `S`
being a continuous bilinear form. -/
theorem osData_bounded (D : OSData) (f : D.Test) :
    |D.S (D.theta f) f| ≤ ‖D.S‖ * ‖D.theta f‖ * ‖f‖ := by
  have h1 : ‖D.S (D.theta f) f‖ ≤ ‖D.S (D.theta f)‖ * ‖f‖ :=
    (D.S (D.theta f)).le_opNorm f
  have h2 : ‖D.S (D.theta f)‖ ≤ ‖D.S‖ * ‖D.theta f‖ := D.S.le_opNorm (D.theta f)
  calc |D.S (D.theta f) f| = ‖D.S (D.theta f) f‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖D.S (D.theta f)‖ * ‖f‖ := h1
    _ ≤ ‖D.S‖ * ‖D.theta f‖ * ‖f‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg f)

/-- **The Schwinger form of any `OSData` is not the zero map.** -/
theorem osData_S_ne_zero (D : OSData) : D.S ≠ 0 := by
  intro h
  obtain ⟨f, hf⟩ := D.os_nontriv
  exact hf (by rw [h]; simp)

/-- **Every `OSData` has a test space with at least two elements** — so no `OSData` can be built on `Unit`,
on any subsingleton, or on the zero module. This is the exact property `os_reconstruction`'s hypotheses lack:
there, `J := Unit` and `q := fun _ => 0` satisfy everything (`wightmanTheory_of_nothing`).

The proof is the whole point: `S` is bilinear, so `S (θ 0) 0 = 0`, and `os_nontriv` supplies an `f` at which
the reflected form is nonzero. That `f` is therefore not `0`. -/
theorem osData_test_nontrivial (D : OSData) : Nontrivial D.Test := by
  obtain ⟨f, hf⟩ := D.os_nontriv
  refine ⟨⟨f, 0, ?_⟩⟩
  rintro rfl
  exact hf (by simp)

/-- **No `OSData` on a subsingleton.** The same fact in the form that names what a trivial instantiation
would have had to supply: an `f` with `S (θ f) f ≠ 0` inside a type all of whose elements are equal. -/
theorem osData_test_not_subsingleton (D : OSData) : ¬ Subsingleton D.Test := by
  intro h
  obtain ⟨f, hf⟩ := D.os_nontriv
  rw [h.allEq f 0] at hf
  simp at hf

/-- **`OSData` IS inhabited, by a one-dimensional form with no physics in it.** `Test := ℝ`, `θ = id`,
`S f g = f·g`, translations acting trivially. This is the limit of what the structure refuses: it rules out
the subsingleton instantiation that discharges `os_reconstruction` (`osData_test_nontrivial`), and it does
not rule out a finite-dimensional toy.

Recorded so the claim made about the restatement stays the claim that is checked. What `OSData` buys over
`os_reconstruction`'s hypotheses is that reflection positivity is a condition on a bilinear form and that
the form is nonzero — not that only a Yang–Mills theory satisfies it.

DERIVED: neither digit describes a theory; both are the structure's own obligations read at
`Test := ℝ`. `0` is the zero of `ℝ` in the reflection-positivity field `os2`, where `0 ≤ f * f` is
`mul_self_nonneg`. `1` is the unit of `ℝ` supplied as the witness in `os_nontriv`, which asks for SOME
test function with `S (θ f) f ≠ 0` — the REFLECTED form, not `S f f`. Here `θ` is the identity and
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

/-- `OSData` has an inhabitant, so the restated reconstruction axiom's hypothesis is satisfiable. -/
theorem osData_nonempty : Nonempty OSData := ⟨trivialOSData⟩

/-- **Gårding–Wightman data on a fixed Hilbert space `H`**, at the fidelity Mathlib v4.31 supports, in the
shape `Reconstruction.GappedQuantumTheory` uses for the operator-theoretic side: a quantum theory as DATA.

WHAT IS CARRIED. A complex Hilbert space `H` (the parameter, with completeness); a vacuum `vac` that is a
unit vector; a representation `U` of the translation group `ℝ⁴` by surjective linear isometries, unital and
additive, fixing the vacuum; a Hamiltonian `ham`, self-adjoint, annihilating the vacuum, with every spectral
value in the closed right half-plane (`H ≥ 0`); and field operators `field`, indexed by real Schwartz test
functions on `ℝ⁴`, acting on a DENSE common domain `dom` that contains the vacuum, additive in the test
function.

WHAT IS NOT CARRIED, and is therefore not claimed. (i) `ham` is BOUNDED (`H →L[ℂ] H`); a Wightman
Hamiltonian is unbounded, and Mathlib v4.31 has no unbounded self-adjoint operator theory to state this in.
(ii) There is no Lorentz or Euclidean rotation subgroup — only translations. (iii) `ham` is not tied to `U`:
the statement that `ham` generates the time translation is absent. (iv) The fields are additive in the test
function but not stated ℝ-linear, not stated symmetric, not stated covariant under `U`, and not stated local
(no spacelike commutativity). (v) Uniqueness of the vacuum and cyclicity of the vacuum for the field algebra
are absent, as are the Wightman distributions themselves and their positivity and spectral conditions.

So this is a Hilbert space with a vacuum, a translation representation, a nonnegative Hamiltonian and fields
on a dense domain. It is not the Wightman axioms. -/
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
  /-- The Hamiltonian. BOUNDED — see the structure docstring. -/
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

/-- **A Wightman theory with its Hilbert space bundled** — what a reconstruction has to PRODUCE, since the
Hilbert space is an output of the construction and not an input to it. -/
structure WightmanQFTData where
  /-- The Hilbert space of states. -/
  Space : Type
  [normed : NormedAddCommGroup Space]
  [hilb : InnerProductSpace ℂ Space]
  [complete : CompleteSpace Space]
  /-- The theory on it. -/
  qft : WightmanQFT Space

/-- The state space of a `WightmanQFTData` is a normed group. As with `OSData`, the instance-implicit
field's projection has to be registered to be found. -/
instance instNormedAddCommGroupWightmanSpace (Q : WightmanQFTData) :
    NormedAddCommGroup Q.Space := Q.normed

/-- The state space is a complex inner product space. -/
instance instInnerProductSpaceWightmanSpace (Q : WightmanQFTData) :
    InnerProductSpace ℂ Q.Space := Q.hilb

/-- The state space is complete. -/
instance instCompleteSpaceWightmanSpace (Q : WightmanQFTData) : CompleteSpace Q.Space := Q.complete

/-- **`WightmanQFT` is inhabited**, by the one-dimensional theory on `ℂ`: vacuum `1`, trivial translation
representation, zero Hamiltonian, fields all zero on the whole space.

Two things follow, and they pull in opposite directions. (i) The target type of
`os_reconstruction_wightman` is not empty, so that axiom cannot on its own prove `False` — the check a
DATA-valued axiom needs and a `Prop`-valued one does not. (ii) Satisfying `WightmanQFT` is not by itself
evidence of a Yang–Mills theory: the structure carries a vacuum, a positive Hamiltonian and a dense field
domain, and this witness has all three with nothing in them.

DERIVED: both digits are the units of `ℂ`, not physical quantities. `1` is the multiplicative unit
serving as the vacuum, and it is forced rather than picked: `vac_norm` demands a UNIT vector, and in
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

/-- The bundled form of `trivialWightmanQFT`. -/
noncomputable def trivialWightmanQFTData : WightmanQFTData where
  Space := ℂ
  qft := trivialWightmanQFT

/-- **The restated axiom's target type is inhabited.** So `os_reconstruction_wightman` is an assumption
about which Euclidean data yields which quantum theory, not a way of asserting a proposition that has no
model. -/
theorem wightmanQFTData_nonempty : Nonempty WightmanQFTData := ⟨trivialWightmanQFTData⟩

/-! ## Part 3 — the reconstruction, restated -/

/-- **Osterwalder–Schrader reconstruction, restated between the two structures (NEW NAMED AXIOM).**
K. Osterwalder, R. Schrader, Commun. Math. Phys. **31** (1973) 83 and **42** (1975) 281; textbook form
J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed. (Springer 1987).

This is an AXIOM, not a proof; the theorem it names is research-level and is not formalised here. What
changes against `FullModel.os_reconstruction` is the statement, in both directions:

* its hypothesis is a structure that no subsingleton inhabits (`osData_test_nontrivial`), whose form is
  bilinear and continuous, and whose reflection positivity is therefore a Gram condition rather than
  nonnegativity of an arbitrary function;
* its conclusion is data, from which a vacuum, a translation representation, a Hamiltonian and a dense
  field domain can be read (`reconstructed_vacuum_energy_zero`, `reconstructed_space_nontrivial`), rather
  than an opaque `Prop` that every proposition implies (`wightmanTheory_of_anything`).

It is not dischargeable from nothing: producing a term of this type requires producing a Hilbert space with
a unit vector, a translation representation fixing it, and a self-adjoint operator annihilating it whose
spectrum lies in the closed right half-plane — and `reconstructed_space_nontrivial` shows that space cannot
be the zero space. The trivial instantiation that closes `os_reconstruction` supplies none of it.

DERIVED: bibliographic. The statement `(D : OSData) : WightmanQFTData` contains no numeral at all.
Every digit in this doc comment — `31`, `1973`, `83`, `42`, `1975`, `281`, `1987` — is part of the
citation at the top: volume, year and first page of the two Osterwalder–Schrader papers, and the
year of the Glimm–Jaffe edition. They are not constants, nothing is decided by them, and they are
left in ordinary citation form because a reader needs to be able to follow them to the papers. -/
axiom os_reconstruction_wightman (D : OSData) : WightmanQFTData

/-- The vacuum of a reconstructed theory is a nonzero vector — it is a unit vector by `vac_norm`. -/
theorem reconstructed_vac_ne_zero (Q : WightmanQFTData) : Q.qft.vac ≠ 0 := by
  intro h
  have hn : ‖Q.qft.vac‖ = 1 := Q.qft.vac_norm
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- **The reconstructed Hilbert space is not the zero space.** Something `WightmanTheory : Prop` cannot
say. -/
theorem reconstructed_space_nontrivial (Q : WightmanQFTData) : Nontrivial Q.Space :=
  ⟨⟨Q.qft.vac, 0, reconstructed_vac_ne_zero Q⟩⟩

/-- **The reconstructed Hamiltonian has a kernel vector — the vacuum, at energy zero.** Read straight out of
the axiom's conclusion. -/
theorem reconstructed_vacuum_energy_zero (D : OSData) :
    (os_reconstruction_wightman D).qft.ham (os_reconstruction_wightman D).qft.vac = 0 :=
  (os_reconstruction_wightman D).qft.ham_vac

/-- **The reconstructed Hamiltonian is not injective.** The spectral condition plus a genuine vacuum: `ham`
kills a nonzero vector, so `0` is an eigenvalue and the bottom of the spectrum is attained. -/
theorem reconstructed_ham_not_injective (Q : WightmanQFTData) :
    ¬ Function.Injective Q.qft.ham := by
  intro hinj
  refine reconstructed_vac_ne_zero Q (hinj ?_)
  rw [Q.qft.ham_vac, map_zero]

/-- **The reconstruction's hypothesis refuses the instantiation that discharges the standing axiom.** Side
by side: `wightmanTheory_of_nothing` builds `WightmanTheory` from `Unit`; here the input's test space is
provably not a subsingleton, and the output's Hilbert space is provably not the zero space. -/
theorem os_reconstruction_wightman_is_not_vacuous (D : OSData) :
    Nontrivial D.Test ∧ Nontrivial (os_reconstruction_wightman D).Space :=
  ⟨osData_test_nontrivial D, reconstructed_space_nontrivial _⟩

#print axioms wightmanTheory_of_nothing
#print axioms wightmanTheory_of_zero_form
#print axioms wightmanTheory_of_anything
#print axioms wightman_of_model_is_the_trivial_proof
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
