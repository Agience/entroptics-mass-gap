import Mathlib
import MassGap.WightmanData

/-!
# MassGap.LatticeTranslNoGo — a translation of finite exponent on an `OSData` is the identity

`WightmanData.OSData` carries a field `transl : E4 → (Test →L[ℝ] Test)` together with `transl_zero`
and `transl_add`, and no continuity requirement in the vector argument. `transl` is therefore an
additive homomorphism from `E4 = EuclideanSpace ℝ (Fin 4)` into the composition monoid of continuous
linear endomorphisms of `Test`. This module derives what that forces when the homomorphism's image
has finite exponent, and the parallel statement for an integer-valued target.

The arithmetic input is that `E4` is a divisible additive group: for every `m` with `0 < m` and
every `a : E4`, `a = m • ((m : ℝ)⁻¹ • a)` (`exists_nsmul_eq`).

Contents:
* `transl_nsmul` — `D.transl (k • a) f` is the `k`-fold iterate of `fun g => D.transl a g` at `f`.
  The only place the `OSData` fields are used.
* `exists_nsmul_eq` — divisibility of `E4`.
* `transl_eq_id_of_finite_order` — if `(fun h => D.transl x h)^[m] g = g` for one `0 < m`, every `x`
  and every `g`, then `D.transl a f = f` for every `a` and `f`.
* `os1_holds_of_everything_when_transl_trivial` — under the same finite-exponent hypothesis, an
  arbitrary continuous bilinear `T` satisfies `T (transl a f) (transl a g) = T f g`.
* `no_finite_order_of_transl_ne_id` — the contrapositive: if `transl` moves even one test function,
  no `0 < m` makes `(transl x)^[m]` the identity.
* `image_divisible`, `int_eq_zero_of_forall_dvd`, `addHom_to_int_lattice_eq_zero` — the same
  divisibility argument against an integer lattice: every additive homomorphism
  `E4 →+ (Fin 4 → ℤ)` is zero, with no finite-order hypothesis, since a nonzero integer is not
  divisible by every positive integer.

Scope. The finite-exponent hypothesis `hfin` is carried as a hypothesis throughout; no `OSData` is
constructed here, and nothing in this module derives `hfin` from a lattice construction.
`HalfLineTransfer.shiftObs_pow_period` is one statement of the tree that has that shape. These
theorems say nothing about the `os2`, `os3` or `os_nontriv` fields of `OSData`, and they do not
assert that `OSData` is uninhabited — `WightmanData.trivialOSData` inhabits it, and
`os1_holds_of_everything_when_transl_trivial` records that with a trivial `transl` the invariance
field holds of every bilinear form, so it constrains nothing.
-/

namespace MassGap.LatticeTranslNoGo

open MassGap.WightmanData

/-- `D.transl (k • a) f = (fun g => D.transl a g)^[k] f`, for an `OSData` `D`, a vector `a : E4`, a
natural `k` and a test function `f`. Proved by induction on `k`, peeling `a` off the front of
`(k + 1) • a = a + k • a` so that the inductive hypothesis, which is stated at `f`, applies. The
only declaration here that uses the `OSData` fields `transl_zero` and `transl_add`.

DERIVED: no numeral occurs in the statement. `k` is the multiple and the iterate count; the base
case `0` and the successor's `1` are in the proof. -/
theorem transl_nsmul (D : OSData) (a : E4) (k : ℕ) (f : D.Test) :
    D.transl (k • a) f = (fun g => D.transl a g)^[k] f := by
  induction k with
  | zero => simpa using D.transl_zero f
  | succ k ih =>
      -- `a` FIRST, so that `transl_add` peels the outer step and leaves `transl (k • a) f`, which is
      -- exactly what `ih` is about. Peeling the other way leaves `transl (k • a) (transl a f)`, and
      -- `ih` is stated at `f` alone, so it would not apply.
      have hsucc : (k + 1) • a = a + k • a := by rw [succ_nsmul, add_comm]
      rw [hsucc, D.transl_add, ih, Function.iterate_succ_apply']

/-- `E4` is divisible as an additive group: for `0 < m` and any `a : E4`, there is `y` with
`m • y = a`. The witness is `(m : ℝ)⁻¹ • a`, and the proof turns the `ℕ`-scalar action into the
`ℝ`-scalar one with `Nat.cast_smul_eq_nsmul` before cancelling.

DERIVED: the one numeral is the `0` in `0 < m`, which is what makes `(m : ℝ)` invertible in the
scalars. `m` is the caller's. -/
theorem exists_nsmul_eq (m : ℕ) (hm : 0 < m) (a : E4) : ∃ y : E4, m • y = a := by
  refine ⟨(m : ℝ)⁻¹ • a, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hm', one_smul]

/-- A translation of finite exponent on an `OSData` is the identity. Given `0 < m` and
`hfin : ∀ x : E4, ∀ g : D.Test, (fun h => D.transl x h)^[m] g = g`, the conclusion is
`D.transl a f = f` for every `a : E4` and every `f : D.Test`. The proof writes `a = m • y` by
`exists_nsmul_eq`, converts `D.transl (m • y) f` into the `m`-fold iterate by `transl_nsmul`, and
applies `hfin` at `y`.

Scope: `hfin` is a hypothesis and is not established here. Nothing in the statement refers to a
Hilbert space, a measure, a coupling or a gauge group; the argument is about the index group `E4`
and the exponent `m` alone. The same `m` must work at every `x`.

DERIVED: the one numeral is the `0` in `0 < m`, which `exists_nsmul_eq` requires. `m` is the
exponent, carried from the hypothesis unchanged. -/
theorem transl_eq_id_of_finite_order (D : OSData) (m : ℕ) (hm : 0 < m)
    (hfin : ∀ x : E4, ∀ g : D.Test, (fun h => D.transl x h)^[m] g = g)
    (a : E4) (f : D.Test) : D.transl a f = f := by
  obtain ⟨y, hy⟩ := exists_nsmul_eq m hm a
  calc D.transl a f = D.transl (m • y) f := by rw [hy]
    _ = (fun h => D.transl y h)^[m] f := transl_nsmul D y m f
    _ = f := hfin y f

/-- Translation invariance holds of every bilinear form when `transl` has finite exponent. Under the
same hypotheses as `transl_eq_id_of_finite_order`, and for an arbitrary continuous bilinear
`T : D.Test →L[ℝ] D.Test →L[ℝ] ℝ`, `T (D.transl a f) (D.transl a g) = T f g`. The proof rewrites
both arguments with `transl_eq_id_of_finite_order`.

Scope: `T` is unconstrained, so the invariance identity carries no information about `T`. This is
the shape of the `os1` field of `OSData`, instantiated at an arbitrary form rather than at a
Schwinger form.

DERIVED: the one numeral is the `0` in `0 < m`, inherited from
`transl_eq_id_of_finite_order`. -/
theorem os1_holds_of_everything_when_transl_trivial (D : OSData) (m : ℕ) (hm : 0 < m)
    (hfin : ∀ x : E4, ∀ g : D.Test, (fun h => D.transl x h)^[m] g = g)
    (T : D.Test →L[ℝ] D.Test →L[ℝ] ℝ) (a : E4) (f g : D.Test) :
    T (D.transl a f) (D.transl a g) = T f g := by
  rw [transl_eq_id_of_finite_order D m hm hfin a f,
      transl_eq_id_of_finite_order D m hm hfin a g]

/-- The contrapositive. If there exist `a : E4` and `f : D.Test` with `D.transl a f ≠ f`, then for
every `m` with `0 < m` the finite-exponent property
`∀ x g, (fun h' => D.transl x h')^[m] g = g` fails. Proved by feeding any such `m` and hypothesis to
`transl_eq_id_of_finite_order` and contradicting the witness.

Scope: the statement quantifies over all `0 < m`, so it excludes every exponent at once; it says
nothing about which representations of a translation group could supply one.

DERIVED: the one numeral is the `0` in `0 < m`, which fixes the range of exponents excluded. -/
theorem no_finite_order_of_transl_ne_id (D : OSData)
    (h : ∃ a : E4, ∃ f : D.Test, D.transl a f ≠ f) :
    ∀ m : ℕ, 0 < m → ¬ (∀ x : E4, ∀ g : D.Test, (fun h' => D.transl x h')^[m] g = g) := by
  obtain ⟨a, f, haf⟩ := h
  intro m hm hfin
  exact haf (transl_eq_id_of_finite_order D m hm hfin a f)

/-! ## The integer lattice, where no exponent is available

On `ℤ⁴` the translation group is torsion-free, so `transl_eq_id_of_finite_order` has no exponent to
apply and says nothing. The three results below reach the same conclusion from divisibility alone:
an integer lying in `m * ℤ` for every positive `m` is zero, so every additive homomorphism
`E4 →+ (Fin 4 → ℤ)` is the zero map. The hypothesis traded away is finite exponent; what replaces
it is the failure of divisibility in `ℤ`. -/

/-- The image of an additive homomorphism out of `E4` is divisible: for any additive commutative
group `A`, any `φ : E4 →+ A`, any `0 < m` and any `a : E4`, there is `b : A` with `φ a = m • b`.
The witness is `φ y` for the `y` supplied by `exists_nsmul_eq`, using `map_nsmul`.

DERIVED: the one numeral is the `0` in `0 < m`, which `exists_nsmul_eq` requires. -/
theorem image_divisible {A : Type*} [AddCommGroup A] (φ : E4 →+ A) (m : ℕ) (hm : 0 < m) (a : E4) :
    ∃ b : A, φ a = m • b := by
  obtain ⟨y, hy⟩ := exists_nsmul_eq m hm a
  exact ⟨φ y, by rw [← hy, map_nsmul]⟩

/-- An integer divisible by every positive natural is zero. Given `k : ℤ` and
`h : ∀ m : ℕ, 0 < m → ∃ t : ℤ, k = (m : ℤ) * t`, the conclusion is `k = 0`. The proof instantiates
`h` at `m = k.natAbs + 1`; if the cofactor is nonzero then `k.natAbs = (k.natAbs + 1) * t.natAbs` is
at least `k.natAbs + 1`, which `omega` refutes.

Scope: `h` must hold at every positive `m`, not merely at arbitrarily large ones in a chosen family.

DERIVED: `0` is the strict lower bound on `m` in the hypothesis and the value of `k` in the
conclusion. `1` is the increment in the instantiating exponent `k.natAbs + 1`, chosen because it is
the least exponent strictly larger than `|k|`; any larger one would serve. -/
theorem int_eq_zero_of_forall_dvd (k : ℤ)
    (h : ∀ m : ℕ, 0 < m → ∃ t : ℤ, k = (m : ℤ) * t) : k = 0 := by
  obtain ⟨t, ht⟩ := h (k.natAbs + 1) (Nat.succ_pos _)
  rcases eq_or_ne t 0 with rfl | ht0
  · simpa using ht
  · exfalso
    have h1 : 0 < t.natAbs := Int.natAbs_pos.mpr ht0
    -- `conv_lhs` so the rewrite touches the bare `k` and NOT the `k` inside `k.natAbs`, which would
    -- otherwise loop the exponent back into its own definition.
    have hcast : ((k.natAbs + 1 : ℕ) : ℤ).natAbs = k.natAbs + 1 := by omega
    have h2 : k.natAbs = (k.natAbs + 1) * t.natAbs := by
      conv_lhs => rw [ht]
      rw [Int.natAbs_mul, hcast]
    have h3 : k.natAbs + 1 ≤ (k.natAbs + 1) * t.natAbs := Nat.le_mul_of_pos_right _ h1
    omega

theorem addHom_to_int_lattice_eq_zero (φ : E4 →+ (Fin 4 → ℤ)) (a : E4) : φ a = 0 := by
  funext i
  refine int_eq_zero_of_forall_dvd _ (fun m hm => ?_)
  obtain ⟨b, hb⟩ := image_divisible φ m hm a
  refine ⟨b i, ?_⟩
  have h := congrFun hb i
  simpa [nsmul_eq_mul] using h

#print axioms transl_nsmul
#print axioms exists_nsmul_eq
#print axioms image_divisible
#print axioms int_eq_zero_of_forall_dvd
#print axioms addHom_to_int_lattice_eq_zero
#print axioms transl_eq_id_of_finite_order
#print axioms os1_holds_of_everything_when_transl_trivial
#print axioms no_finite_order_of_transl_ne_id

end MassGap.LatticeTranslNoGo
