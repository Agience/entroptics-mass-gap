import Mathlib
import MassGap.WightmanData

/-!
# MassGap.LatticeTranslNoGo — an `OSData` on a FIXED lattice has a trivial translation, and that is
group theory rather than a missing construction

`WightmanData.os_reconstruction_wightman` is the one axiom the Clay statement itself names as a route,
and it consumes an `OSData`. `WightmanData` records that no `OSData` is constructed anywhere in this
tree. Of its six substantive fields, four are already theorems about the genuine Wilson measure:
`GNSHilbert.ym_inner_eq_osPairing` gives the Schwinger form `S` as one Gibbs expectation,
`ReflectionStrong.wilsonGibbsReflForm`'s positivity gives `os2`, its symmetry gives `os3`, and
`wilsonGibbsReflForm_vac_norm`'s `⟨1,1⟩ = 1` gives `os_nontriv`. The fields that remain are `transl`
and `os1`.

This file settles what `transl` can be while the lattice spacing is held fixed, and the answer is:
the identity, always.

## The statement

`OSData.transl : E4 → (Test →L[ℝ] Test)` with `transl_zero` and `transl_add`. There is no continuity
requirement in `a`, so `transl` is exactly an additive-group homomorphism from `E4` into the
composition monoid of continuous linear endomorphisms. Two facts then collide:

* `E4 = EuclideanSpace ℝ (Fin 4)` is a real vector space, hence DIVISIBLE as an additive group:
  every `a` is `m • ((m:ℝ)⁻¹ • a)` for every `m ≥ 1`.
* A lattice translation on a periodic lattice of extent `n` has ORDER DIVIDING `n`. That is
  `HalfLineTransfer.shiftObs_pow_period` — `(shiftObs τ)ⁿ = id` on every observable, with no
  hypothesis on the module, the coupling or the reflection.

`transl_eq_id_of_finite_order` is the collision: a homomorphism out of a divisible group into
anything of finite exponent is trivial. Write `a = m • y`, push the `m` through `transl_add`, and the
finite order eats it.

## Why this is not the same statement as the shift no-gos already in the tree

`HalfLineTransfer.no_rate_below_one_of_finite_order` says a finite-order `T` admits no per-step
contraction, which is about DECAY. `GNSHilbert.shiftSlab_eq_id` says the slab shift is the identity
on `SlabShiftStable`'s own premise, which is about that premise. Both are statements about the
transfer operator.

This one is about the INDEX GROUP, and it does not care what the operator is. Even granting a
transfer operator with everything `GNSHilbert` says is missing — bounded, self-adjoint, positive,
with `0 ∉ spectrum` — it still could not serve as `transl`, because `transl` is indexed by `ℝ⁴` and
the lattice supplies only a finite group of translations to represent. The obstruction survives every
improvement to the operator.

## What this does NOT claim

* It does not claim `OSData` is unsatisfiable. `WightmanData.trivialOSData` inhabits it, and
  `os1_holds_of_everything_when_transl_trivial` is the reason that inhabitant is cheap: once `transl`
  is the identity, `os1` holds for EVERY bilinear `S` whatsoever, so the Euclidean-invariance field
  constrains nothing and an `OSData` built this way carries no invariance content. This is the
  `WitnessVacuity` idiom of `GNSHilbert.ym_target_discharged_trivially`, applied to the OS side.
* It does not claim the continuum limit is unreachable. It says the ORDER is forced: the `a → 0`
  limit of `OSFamily.osFamily` has to exist before an `OSData` with content can be written down, so
  C6 cannot be closed before C2. The route in the goal document has C1 and C6 as one step taken
  before the continuum; that is right for C1, whose Hilbert space `GNSHilbert.ymH` already exists at
  fixed spacing, and wrong for C6.
* It proves nothing about `os2`, `os3` or `os_nontriv`, which are the fields already discharged.
* The finite-order hypothesis is carried as a HYPOTHESIS rather than derived from a Wilson
  construction, because no `OSData` exists here to derive it of. It is discharged by any
  representation of the lattice translations, and `shiftObs_pow_period` is the tree's instance.

Foundational footprint only (`#print axioms` on every declaration).
Build: `python research/code/lean_build.py build MassGap.LatticeTranslNoGo`.
-/

namespace MassGap.LatticeTranslNoGo

open MassGap.WightmanData

/-- **The translation of an `n`-fold multiple is the `n`-fold composite.** Pure `transl_add`
bookkeeping, and the only place the `OSData` axioms are used at all.

DERIVED: no numeral. `k` is the induction variable and the `0` case is `transl_zero`. -/
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

/-- **`E4` IS DIVISIBLE**, stated as the one arithmetic fact the no-go turns on: every vector is an
`m`-fold multiple of another, for every `m ≥ 1`.

DERIVED: no numeral. `m` is the exponent supplied by the caller; `(m:ℝ)⁻¹` is its inverse in the
scalars, which exists precisely because `E4` is a real vector space and `m ≠ 0`. -/
theorem exists_nsmul_eq (m : ℕ) (hm : 0 < m) (a : E4) : ∃ y : E4, m • y = a := by
  refine ⟨(m : ℝ)⁻¹ • a, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hm', one_smul]

/-- **THE NO-GO: a translation of finite exponent on an `OSData` is the identity.**

If every `transl x` satisfies `(transl x)^m = id` for one fixed `m ≥ 1` — which is what a
representation of the translations of a periodic lattice of extent `m` gives, by
`HalfLineTransfer.shiftObs_pow_period` — then `transl a = id` at EVERY `a : E4`, with no further
hypothesis.

The proof is three lines and they are the whole content: `E4` is divisible, so `a = m • y`;
`transl_add` turns `transl (m • y)` into the `m`-fold composite of `transl y`; the finite order makes
that composite the identity. Nothing about the Hilbert space, the measure, the coupling or the gauge
group enters, which is why no improvement to the transfer operator can evade it.

DERIVED: no numeral. `m` is the exponent, carried from the hypothesis to the conclusion unchanged. -/
theorem transl_eq_id_of_finite_order (D : OSData) (m : ℕ) (hm : 0 < m)
    (hfin : ∀ x : E4, ∀ g : D.Test, (fun h => D.transl x h)^[m] g = g)
    (a : E4) (f : D.Test) : D.transl a f = f := by
  obtain ⟨y, hy⟩ := exists_nsmul_eq m hm a
  calc D.transl a f = D.transl (m • y) f := by rw [hy]
    _ = (fun h => D.transl y h)^[m] f := transl_nsmul D y m f
    _ = f := hfin y f

/-- **AND THEN `os1` IS SATISFIED BY EVERY BILINEAR FORM, so it constrains nothing.**

Stated separately from the no-go because it is the part that matters for what an `OSData` is WORTH.
`os1` is Euclidean invariance, the field that makes the Schwinger form a function of differences
rather than of positions. Once `transl` is the identity it holds of an ARBITRARY `S`, including one
with no relation to Yang–Mills, so producing an `OSData` this way and feeding it to
`os_reconstruction_wightman` would yield a `WightmanQFTData` whose invariance content is empty.

The same shape as `GNSHilbert.ym_target_discharged_trivially`: the target is met, and meeting it
conveys nothing. -/
theorem os1_holds_of_everything_when_transl_trivial (D : OSData) (m : ℕ) (hm : 0 < m)
    (hfin : ∀ x : E4, ∀ g : D.Test, (fun h => D.transl x h)^[m] g = g)
    (T : D.Test →L[ℝ] D.Test →L[ℝ] ℝ) (a : E4) (f g : D.Test) :
    T (D.transl a f) (D.transl a g) = T f g := by
  rw [transl_eq_id_of_finite_order D m hm hfin a f,
      transl_eq_id_of_finite_order D m hm hfin a g]

/-- **THE CONTRAPOSITIVE, which is the usable direction.** An `OSData` whose translation acts
non-trivially at even one vector has NO finite exponent — so it cannot be carried by the translations
of a lattice at fixed spacing, at any extent whatever.

This is the statement to discharge when the continuum limit arrives: it names exactly what the limit
has to supply that a fixed lattice cannot. -/
theorem no_finite_order_of_transl_ne_id (D : OSData)
    (h : ∃ a : E4, ∃ f : D.Test, D.transl a f ≠ f) :
    ∀ m : ℕ, 0 < m → ¬ (∀ x : E4, ∀ g : D.Test, (fun h' => D.transl x h')^[m] g = g) := by
  obtain ⟨a, f, haf⟩ := h
  intro m hm hfin
  exact haf (transl_eq_id_of_finite_order D m hm hfin a f)

/-! ## The infinite lattice, where the translations do NOT have finite order

`WilsonGibbs.exists_wilson_isGibbsMeasure` puts a DLR Gibbs measure on the infinite lattice `ℤ⁴`,
and there the translation group is `ℤ⁴` itself — torsion-free, so `transl_eq_id_of_finite_order` has
no exponent to work with and says nothing. The no-go survives anyway, and by the same divisibility
fact, because `ℤ⁴` is not divisible either: the only element of `ℤ` divisible by every positive
integer is `0`.

So neither horn of C2 escapes. At fixed finite extent the translations have finite order and the
first theorem applies; on `ℤ⁴` they have infinite order and the second does. An `OSData` with a
non-trivial `transl` requires a translation group that is itself divisible, which is what `ℝ⁴` is and
what no lattice at any spacing supplies. -/

/-- **THE DIVISIBILITY, ABSTRACTLY**: the image of an additive homomorphism out of `E4` is divisible.
Every value is an `m`-fold multiple, at every `m ≥ 1`. This is the single fact both no-gos spend. -/
theorem image_divisible {A : Type*} [AddCommGroup A] (φ : E4 →+ A) (m : ℕ) (hm : 0 < m) (a : E4) :
    ∃ b : A, φ a = m • b := by
  obtain ⟨y, hy⟩ := exists_nsmul_eq m hm a
  exact ⟨φ y, by rw [← hy, map_nsmul]⟩

/-- **THE NO-GO AT INFINITE EXTENT**: every additive homomorphism `E4 →+ (Fin 4 → ℤ)` is zero.

So a `transl` that acts by translations of the INFINITE lattice `ℤ⁴` is the identity too, for the
same reason and with no finite order anywhere in the argument. `ℤ` is torsion-free, so the exponent
route is unavailable; what does the work is that `ℤ` is not DIVISIBLE, and an integer lying in
`m·ℤ` for every `m` is zero.

DERIVED: `k.natAbs + 1` is the one exponent the proof needs — strictly larger than `|k|`, so a
multiple of it that is smaller in absolute value than it can only be zero. Nothing is chosen; any
`m > |k|` does the same job and this is the least one. -/
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
