import Mathlib
import MassGap.GNSHilbert
import MassGap.GapToOperator
import MassGap.VolumeRate
import MassGap.SecondEigenvalue

/-!
# MassGap.GNSCompare — relating the two Hilbert spaces built from one `TransferData`

`Transfer.TransferData` supports two Hilbert-space constructions in this tree:

* the real quotient `Transfer.GNS P = A ⧸ P.nullSpace`, with step maps `Tq` and `TqL`, used by
  `VolumeRate`, `SecondEigenvalue`, `PeriodicRayleigh` and `HalfLineTransfer`;
* the complex completion `GNSHilbert.H P = Completion (Pre P)`, with `opT`, used by `OpTBridge`,
  `GapToOperator`, `B2Locality` and `ClayAssembly`.

This module relates them, and states the contraction property on each side as an equivalence with
`TransferGap.GapAt`.

## The embedding

`toH P x` is the class of the pair `(x, 0)` — the observable in the real component, `0` in the
imaginary one. It is defined as `GNSHilbert.Omega P x`, whose body takes an arbitrary vector and is
named for the vacuum; `toH_vac` records that the two agree at the vacuum by `rfl`. Along it:

* `inner_coe_ofPair` — the complex pairing of two such classes is the real form `P.form x y`, cast
  into `ℂ` with zero imaginary part;
* `norm_coe_ofPair` — the norm agrees with `‖GNS.mk P x‖`, both squares being `P.form x x`;
* `opT_coe_ofPair` — `opT D` acts on such a class as `D.T` acts on the observable, which with
  `Transfer.Tq_mk` gives `intertwines`;
* `coe_ofPair_eq_zero_iff` — the class is zero exactly when `P.form x x = 0`, the condition defining
  the null space `GNS` quotients by.

`opT_coe_ofPair` and `norm_coe_ofPair` are the statements `GNSHilbert.opT_Omega` and
`GNSHilbert.norm_Omega` make at the vacuum, here at an arbitrary vector; neither of those is
rederived from these.

## The two equivalences

`gapAt_iff_opT_contracts` — `GapAt D r` holds exactly when `opT D` contracts the vacuum's orthogonal
complement in the completion by `r`. Forward is `GapToOperator.norm_opT_le_of_orth`, which carries
the density argument; backward is `gapAt_of_opT_contracts`, which goes through the three lemmas
above.

`gapAt_iff_tq_contracts` — the same equivalence on the real quotient, from `tq_contracts_of_gapAt`
and `gapAt_of_tq_contracts`. `norm_Tq_pow_le_of_gapAt` composes the first with
`VolumeRate.norm_Tq_pow_le`, whose own hypothesis is the per-step bound.

`gapAt_of_rayleigh` and `gapAt_of_positiveTransfer_of_rayleigh` reach `GapAt` from a Rayleigh-quotient
estimate on the vacuum complement, using `SecondEigenvalue.norm_Tq_le_of_rayleigh`. The second takes
the positivity input in the form of `GNSHilbert.PositiveTransfer`, via
`inner_Tq_nonneg_of_positiveTransfer`.

## Scope

The embedding is not bundled as a `LinearIsometry`; the crossings use `Transfer.GNS.exists_mk`,
`inner_mk`, `norm_mk_mul_norm_mk` and this module's own lemmas, with no restriction of scalars.

Every statement below takes its bound (`r` or `Λ`) and its positivity hypotheses as arguments. No
declaration here produces a numerical bound, and none consumes one.
-/

namespace MassGap.GNSCompare

open MassGap.GNSHilbert MassGap.Transfer MassGap.TransferGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A real observable in the complex completion: the class with `x` in the real component and zero
in the imaginary one.

Defined as `GNSHilbert.Omega P x`. That definition already takes an arbitrary vector and is named for
the vacuum; this name is for the case where the argument is not the vacuum, and the two are the same
map.

DERIVED: the statement carries no numeral — the imaginary component is fixed inside `Omega`, not in
the type. -/
noncomputable def toH (P : ReflForm A) (x : A) : H P := Omega P x

/-- The unfolded form, for rewriting: `toH P x` is the completion class of the pair `(x, 0)` in
`Pre P`. Holds by `rfl`.

DERIVED: `0` is the imaginary component of a real observable, and is the only numeral in the
statement. -/
theorem toH_def (P : ReflForm A) (x : A) :
    toH P x = ((Pre.ofPair P x 0 : Pre P) : H P) := rfl

/-- The complex pairing of two embedded observables is the real form cast into `ℂ`:
`inner ℂ (toH P x) (toH P y) = (P.form x y : ℂ)`.

The imaginary part vanishes because both cross terms of the pre-inner product carry a zero component.
So the embedding preserves the inner product, not only the norm.

DERIVED: the statement carries no numeral. -/
@[simp] theorem inner_coe_ofPair (P : ReflForm A) (x y : A) :
    inner ℂ (toH P x) (toH P y) = ((P.form x y : ℝ) : ℂ) := by
  rw [toH_def, toH_def, inner_coe]
  simp [MassGap.OSPositivity.cform, Transfer.PreForm.form_zero_left,
    Transfer.PreForm.form_zero_right]

/-- `‖toH P x‖ = ‖GNS.mk P x‖`: the completion norm of an embedded observable equals its norm in the
real quotient.

Both squares are `P.form x x`, and both norms are non-negative. `P` is an arbitrary `ReflForm`; no
positivity of the form beyond what `ReflForm` carries is used.

DERIVED: the statement carries no numeral. -/
theorem norm_coe_ofPair (P : ReflForm A) (x : A) :
    ‖toH P x‖ = ‖GNS.mk P x‖ := by
  have h1 : ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
    rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
    simp [Transfer.PreForm.form_zero_left]
  have h2 : ‖GNS.mk P x‖ * ‖GNS.mk P x‖ = P.form x x := GNS.norm_mk_mul_norm_mk x
  nlinarith [norm_nonneg (toH P x), norm_nonneg (GNS.mk P x)]

/-- `toH P x = 0` exactly when `P.form x x = 0` — the condition defining the null space that `GNS`
quotients by.

Both directions go through `norm_coe_ofPair` and `GNS.norm_mk_mul_norm_mk`. The kernel of the
embedding is therefore the same submodule the real quotient divides by.

DERIVED: `0` is the zero vector of the completion on the left and the form's value on the right. It
is the only numeral in the statement. -/
theorem coe_ofPair_eq_zero_iff (P : ReflForm A) (x : A) :
    toH P x = 0 ↔ P.form x x = 0 := by
  constructor
  · intro h
    have hn : ‖toH P x‖ = 0 := by rw [h, norm_zero]
    have := norm_coe_ofPair P x
    rw [hn] at this
    have h2 : ‖GNS.mk P x‖ * ‖GNS.mk P x‖ = P.form x x := GNS.norm_mk_mul_norm_mk x
    rw [← this] at h2
    simpa using h2.symm
  · intro h
    have hn : ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
      rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
      simp [Transfer.PreForm.form_zero_left]
    rw [h] at hn
    have : ‖toH P x‖ = 0 := by nlinarith [norm_nonneg (toH P x)]
    exact norm_eq_zero.mp this

/-- `opT D (toH D.toReflForm x) = toH D.toReflForm (D.T x)`: the completion's step map acts on an
embedded observable as `D.T` acts on the observable.

The imaginary component stays zero because `D.T` is linear and so sends `0` to `0`. With
`Transfer.Tq_mk` this gives the intertwining stated in `intertwines`.

DERIVED: the statement carries no numeral. -/
@[simp] theorem opT_coe_ofPair (D : TransferData A) (x : A) :
    opT D (toH D.toReflForm x) = toH D.toReflForm (D.T x) := by
  rw [toH_def, opT_coe, cTL_apply]
  congr 1
  refine Pre.ext ?_ ?_
  · rw [cT_fst]; simp [Pre.ofPair]
  · rw [cT_snd]; simp [Pre.ofPair, map_zero]

/-- The two step maps stated together: `opT D` moves the embedded class as `D.T` moves the
observable, and `D.Tq` moves the quotient class the same way.

The conjunction of `opT_coe_ofPair` and `D.Tq_mk`; it adds no content beyond pairing them.

DERIVED: the statement carries no numeral. -/
theorem intertwines (D : TransferData A) (x : A) :
    opT D (toH D.toReflForm x) = toH D.toReflForm (D.T x) ∧
      D.Tq (GNS.mk D.toReflForm x) = GNS.mk D.toReflForm (D.T x) :=
  ⟨opT_coe_ofPair D x, D.Tq_mk x⟩

/-- `toH D.toReflForm D.vac = Omega D.toReflForm D.vac`, by `rfl`: at the vacuum the embedding is
the completion's own vacuum vector.

DERIVED: the statement carries no numeral. -/
theorem toH_vac (D : TransferData A) :
    toH D.toReflForm D.vac = Omega D.toReflForm D.vac := rfl

/-! ## From an operator bound on the completion to `GapAt` -/

/-- `‖toH P x‖ * ‖toH P x‖ = P.form x x`: the embedded observable's norm squares to the form.

Extracted from `norm_coe_ofPair`'s proof so the statements below can use it without going through the
quotient norm.

DERIVED: the statement carries no numeral. -/
theorem norm_toH_mul_norm_toH (P : ReflForm A) (x : A) :
    ‖toH P x‖ * ‖toH P x‖ = P.form x x := by
  rw [toH_def, UniformSpace.Completion.norm_coe, Pre.norm_mul_norm]
  simp [Transfer.PreForm.form_zero_left]

#print axioms norm_toH_mul_norm_toH

/-- `inner ℂ (Omega P v) (toH P x) = 0` exactly when `P.form x v = 0`.

`inner_coe_ofPair` identifies the pairing with `(P.form v x : ℂ)` and `P.form_symm` exchanges the
arguments, so the completion's orthogonality condition and the one `TransferGap.GapAt` states on the
form are the same condition. The vector `v` is arbitrary — it is the vacuum only at the call sites.

DERIVED: `0` is the vanishing pairing on the left and the vanishing form on the right. It is the only
numeral in the statement. -/
theorem inner_vac_toH_eq_zero_iff (P : ReflForm A) (v x : A) :
    inner ℂ (Omega P v) (toH P x) = (0 : ℂ) ↔ P.form x v = 0 := by
  have h : inner ℂ (Omega P v) (toH P x) = ((P.form v x : ℝ) : ℂ) := inner_coe_ofPair P v x
  rw [h, P.form_symm v x]
  constructor
  · intro hz; exact_mod_cast hz
  · intro hz; exact_mod_cast congrArg (fun y : ℝ => (y : ℂ)) hz

#print axioms inner_vac_toH_eq_zero_iff

/-- `GapAt D r` from a contraction bound on the completion: if `‖opT D y‖ ≤ r * ‖y‖` for every `y`
orthogonal to the vacuum vector, and `0 ≤ r`, then `GapAt D r`.

The converse of `GapToOperator.norm_opT_le_of_orth`. `GapAt` is stated on the form over `A`, so the
proof embeds an observable, transfers its orthogonality (`inner_vac_toH_eq_zero_iff`), applies the
hypothesis there (`opT_coe_ofPair`), and converts both norms back to form values
(`norm_toH_mul_norm_toH`).

Scope: `r` is a parameter and `0 ≤ r` is required; nothing here supplies a value for it, and no
strict bound `r < 1` is assumed or concluded.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition in the
hypothesis. It is the only numeral in the statement; the form's degree lives inside `GapAt`. -/
theorem gapAt_of_opT_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : H D.toReflForm, inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ) →
      ‖opT D y‖ ≤ r * ‖y‖) :
    GapAt D r := by
  intro x hx
  have hperp : inner ℂ (Omega D.toReflForm D.vac) (toH D.toReflForm x) = (0 : ℂ) :=
    (inner_vac_toH_eq_zero_iff D.toReflForm D.vac x).2 hx
  have hb := h (toH D.toReflForm x) hperp
  rw [opT_coe_ofPair] at hb
  have hTx : ‖toH D.toReflForm (D.T x)‖ * ‖toH D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := norm_toH_mul_norm_toH D.toReflForm (D.T x)
  have hxx : ‖toH D.toReflForm x‖ * ‖toH D.toReflForm x‖ = D.form x x :=
    norm_toH_mul_norm_toH D.toReflForm x
  have hnn : 0 ≤ ‖toH D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖toH D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms gapAt_of_opT_contracts

/-- `GapAt D r` holds exactly when `opT D` contracts the vacuum's orthogonal complement in the
completion by `r`, for `0 ≤ r`.

Forward is `GapToOperator.norm_opT_le_of_orth`, which carries the density extension from the dense
image to the whole completion; backward is `gapAt_of_opT_contracts`.

Scope: `0 ≤ r` is required in both directions, and `r` is otherwise arbitrary.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition. It is
the only numeral in the statement. -/
theorem gapAt_iff_opT_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) :
    GapAt D r ↔ ∀ y : H D.toReflForm,
      inner ℂ (Omega D.toReflForm D.vac) y = (0 : ℂ) → ‖opT D y‖ ≤ r * ‖y‖ :=
  ⟨fun hg y hy => MassGap.GapToOperator.norm_opT_le_of_orth D hr hg y hy,
   gapAt_of_opT_contracts D hr⟩

#print axioms gapAt_iff_opT_contracts

/-! ## The same, on the real quotient -/

/-- From `GapAt D r` to the per-step bound on the quotient: `‖D.Tq y‖ ≤ r * ‖y‖` for every class `y`
orthogonal to the vacuum class, given `0 ≤ r`.

This is the hypothesis `VolumeRate.norm_Tq_pow_le` assumes, derived from `GapAt`. Every class is an
`mk x` (`Transfer.GNS.exists_mk`), orthogonality to the vacuum class is the form against the vacuum
(`inner_mk`), `Tq` moves the class as `D.T` moves the observable (`Tq_mk`), and the norm squares to
the form (`norm_mk_mul_norm_mk`).

Scope: stated at one class at a time, with `y` and its orthogonality as binders rather than as a
universally quantified hypothesis.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition `hy`. It
is the only numeral in the statement. -/
theorem tq_contracts_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (y : GNS D.toReflForm) (hy : inner ℝ D.vacGNS y = (0 : ℝ)) :
    ‖D.Tq y‖ ≤ r * ‖y‖ := by
  obtain ⟨x, rfl⟩ := GNS.exists_mk y
  have hform : D.form x D.vac = 0 := by
    have h : D.form D.vac x = 0 := by
      simpa [TransferData.vacGNS] using hy
    rw [D.form_symm]
    exact h
  have hgap := hg x hform
  rw [D.Tq_mk]
  have hTx : ‖GNS.mk D.toReflForm (D.T x)‖ * ‖GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := GNS.norm_mk_mul_norm_mk _
  have hxx : ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ = D.form x x :=
    GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hgap, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms tq_contracts_of_gapAt

/-- The iterate bound on the quotient from `GapAt` alone: `‖(D.Tq ^ n) y‖ ≤ r ^ n * ‖y‖` at every
`n : ℕ`, for `y` orthogonal to the vacuum class and `0 ≤ r`.

`VolumeRate.norm_Tq_pow_le` with its per-step hypothesis supplied by `tq_contracts_of_gapAt`.

Scope: the bound is geometric in `r`, which is a parameter. Nothing here makes `r` smaller than `1`,
so the conclusion is a bound rather than a decay unless the caller's `r` is.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition `hy`. It
is the only numeral in the statement; `n` is a binder and `r` is a parameter. -/
theorem norm_Tq_pow_le_of_gapAt (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) (hg : GapAt D r)
    (y : GNS D.toReflForm) (hy : inner ℝ D.vacGNS y = (0 : ℝ)) (n : ℕ) :
    ‖(D.Tq ^ n) y‖ ≤ r ^ n * ‖y‖ :=
  MassGap.VolumeRate.norm_Tq_pow_le D hr (tq_contracts_of_gapAt D hr hg) hy n

#print axioms norm_Tq_pow_le_of_gapAt

/-! ## From a quotient bound back to `GapAt` -/

/-- `GapAt D r` from a contraction bound on the quotient: if `‖D.Tq y‖ ≤ r * ‖y‖` for every class
`y` orthogonal to the vacuum class, and `0 ≤ r`, then `GapAt D r`.

The converse of `tq_contracts_of_gapAt`. Every class is an `mk x`, so the hypothesis applied at
`mk x` becomes a statement about the form at `x`, which is what `GapAt` asserts.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition in the
hypothesis. It is the only numeral in the statement. -/
theorem gapAt_of_tq_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : GNS D.toReflForm, inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ r * ‖y‖) :
    GapAt D r := by
  intro x hx
  have hvx : D.form D.vac x = 0 := by rw [D.form_symm]; exact hx
  have hy : inner ℝ D.vacGNS (GNS.mk D.toReflForm x) = (0 : ℝ) := by
    simpa [TransferData.vacGNS] using hvx
  have hb := h (GNS.mk D.toReflForm x) hy
  rw [D.Tq_mk] at hb
  have hTx : ‖GNS.mk D.toReflForm (D.T x)‖ * ‖GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := GNS.norm_mk_mul_norm_mk _
  have hxx : ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ = D.form x x :=
    GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms gapAt_of_tq_contracts

/-- `GapAt D r` holds exactly when `D.Tq` contracts the vacuum's orthogonal complement in the real
quotient by `r`, for `0 ≤ r`. The two directions are `tq_contracts_of_gapAt` and
`gapAt_of_tq_contracts`.

DERIVED: `0` is the lower bound in `hr : 0 ≤ r` and the value of the orthogonality condition. It is
the only numeral in the statement. -/
theorem gapAt_iff_tq_contracts (D : TransferData A) {r : ℝ} (hr : 0 ≤ r) :
    GapAt D r ↔ ∀ y : GNS D.toReflForm,
      inner ℝ D.vacGNS y = (0 : ℝ) → ‖D.Tq y‖ ≤ r * ‖y‖ :=
  ⟨tq_contracts_of_gapAt D hr, gapAt_of_tq_contracts D hr⟩

#print axioms gapAt_iff_tq_contracts

/-- `GapAt D Λ` from a Rayleigh-quotient estimate on the vacuum complement.

The two hypotheses are `hpos`, that `0 ≤ ⟪D.Tq y, y⟫` for every class `y` orthogonal to the vacuum
class, and `hray`, that `⟪D.Tq y, y⟫ ≤ Λ * ‖y‖ ^ 2` on the same set, with `0 ≤ Λ`.
`SecondEigenvalue.norm_Tq_le_of_rayleigh` turns the pair into a norm bound on `D.Tq`, and
`gapAt_of_tq_contracts` carries that to `GapAt`.

Scope: `hpos` and `hray` are both inputs. Nothing here establishes either, and `Λ` is a parameter
with no upper bound imposed — the conclusion is `GapAt D Λ` at whatever `Λ` the caller supplies.

DERIVED: `0` is the lower bound in `hΛ : 0 ≤ Λ`, the value of the orthogonality conditions, and the
lower bound in `hpos`. `2` is the exponent in `‖y‖ ^ 2` of the Rayleigh quotient. -/
theorem gapAt_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpos : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ))
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    GapAt D Λ :=
  gapAt_of_tq_contracts D hΛ
    (fun _y hy => MassGap.SecondEigenvalue.norm_Tq_le_of_rayleigh D hΛ hpos hray hy)

#print axioms gapAt_of_rayleigh

/-- `0 ≤ ⟪D.Tq y, y⟫` for every class `y`, given `GNSHilbert.PositiveTransfer D`.

That predicate is `∀ x, 0 ≤ form x (T x)`; writing `y` as `mk x` and applying `Tq_mk`, `inner_mk` and
`form_symm` turns it into the statement above. No orthogonality to the vacuum is needed, so this is
stronger than the `hpos` hypothesis of `gapAt_of_rayleigh` requires.

DERIVED: `0` is the lower bound of the pairing, and is the only numeral in the statement. -/
theorem inner_Tq_nonneg_of_positiveTransfer (D : TransferData A)
    (hP : MassGap.GNSHilbert.PositiveTransfer D) (y : GNS D.toReflForm) :
    (0 : ℝ) ≤ (inner ℝ (D.Tq y) y : ℝ) := by
  obtain ⟨x, rfl⟩ := GNS.exists_mk y
  rw [D.Tq_mk, GNS.inner_mk, D.form_symm]
  exact hP x

#print axioms inner_Tq_nonneg_of_positiveTransfer

/-- `GapAt D Λ` from `GNSHilbert.PositiveTransfer D` together with a single Rayleigh bound
`⟪D.Tq y, y⟫ ≤ Λ * ‖y‖ ^ 2` on the vacuum's orthogonal complement, with `0 ≤ Λ`.

`gapAt_of_rayleigh` with its positivity hypothesis supplied by
`inner_Tq_nonneg_of_positiveTransfer`.

Scope: `PositiveTransfer` is not a consequence of `TransferData`'s fields, and both it and `hray` are
inputs here. `Λ` is a parameter with no upper bound imposed, so the conclusion is `GapAt D Λ` at
whatever value the caller supplies.

DERIVED: `0` is the lower bound in `hΛ : 0 ≤ Λ` and the value of the orthogonality condition in
`hray`. `2` is the exponent in `‖y‖ ^ 2` of the Rayleigh quotient. -/
theorem gapAt_of_positiveTransfer_of_rayleigh (D : TransferData A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    GapAt D Λ :=
  gapAt_of_rayleigh D hΛ (fun y _ => inner_Tq_nonneg_of_positiveTransfer D hP y) hray

#print axioms gapAt_of_positiveTransfer_of_rayleigh

/-- **The chain from positivity to the spectrum, composed.** Every link below is proved elsewhere and
each one's conclusion supplies the next one's hypotheses; nothing wrote the composition, so the route
existed as five statements in three modules and as no theorem.

```
  GNSHilbert.PositiveTransfer D
    → inner_Tq_nonneg_of_positiveTransfer
    → SecondEigenvalue.norm_Tq_le_of_rayleigh      [through norm_le_of_rayleigh_le]
    → gapAt_of_positiveTransfer_of_rayleigh        ⇒ TransferGap.GapAt D Λ
    → GapToOperator.spectrum_opT_subset
```

**The two hypotheses are the two open inputs, and naming them together is the point.** `hray` is the
vacuum Rayleigh ceiling. `hP` is not a consequence of `TransferData`'s fields:
`GNSHilbert.positiveTransfer_trivial` discharges it only where `T = id`, and for the Wilson data
`WilsonTransferReduction.positiveTransfer_of_state_facts` needs reflection positivity about the
**odd** plane, which `WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` shows is not
merely sufficient but equivalent — so it cannot be weakened away.

Scope: nothing on this chain uses compactness, completeness, finite dimension or the spectral
theorem; `SecondEigenvalue.norm_le_of_rayleigh_le` is elementary. And it does not reach
`OpTBridge.reconstruct_from_opT`, whose `hsp` is `{1} ∪ Set.Icc ε (Real.exp (-Δ))` with `0 < ε`:
`Set.Icc (-Λ) Λ` admits `0`, and excluding `0` is `IsUnit (opT D)` by
`TransferInvertibility.isUnit_of_spectral_hypothesis`.

DERIVED: `0` is the lower bound in `hΛ` and the value of the orthogonality condition in `hray`; `2`
is the Rayleigh quotient's exponent; `1` is the vacuum eigenvalue, from `GNSHilbert.opT_Omega`. -/
theorem spectrum_opT_subset_of_positiveTransfer_of_rayleigh (D : TransferData A) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    spectrum ℝ (MassGap.GNSHilbert.opT D) ⊆ {1} ∪ Set.Icc (-Λ) Λ :=
  MassGap.GapToOperator.spectrum_opT_subset D hΛ
    (gapAt_of_positiveTransfer_of_rayleigh D hΛ hP hray)

#print axioms spectrum_opT_subset_of_positiveTransfer_of_rayleigh

/-- The same chain where it carries content: **`Λ < 1`**, with the gap `−log Λ` it buys.

At `1 ≤ Λ` the containment says nothing new — `GNSHilbert.spectrum_opT_subset_unit_interval` already
puts the spectrum inside `Set.Icc (-1) 1` with no hypothesis at all, and
`TransferGap.gapAt_of_one_le_sq` makes `GapAt D Λ` automatic there. So `Λ < 1` is the entire content
of the supply half, and this states the chain in the form that carries it: the spectrum is the vacuum
eigenvalue, which `isGreatest_one_spectrum_opT` shows is its maximum, together with a band strictly
inside the unit interval, and the gap `−log Λ` is positive exactly because the band is strict.

`0 < Λ` and not `0 ≤ Λ`: `Real.log 0` is the junk value `0`, so `0 < −Real.log Λ` is false at
`Λ = 0`. That degenerate case — the vacuum-orthogonal spectrum collapsing to a point — is carried by
`spectrum_opT_subset_of_positiveTransfer_of_rayleigh`, which holds at every nonnegative `Λ`.

DERIVED: `1` is both the vacuum eigenvalue and the contraction constant — the same number, which is
why `Λ < 1` is the content rather than a choice; `0` and `2` are as above. -/
theorem spectrum_opT_strict_band (D : TransferData A) {Λ : ℝ}
    (hΛ : 0 < Λ) (h1 : Λ < 1) (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    spectrum ℝ (MassGap.GNSHilbert.opT D) ⊆ {1} ∪ Set.Icc (-Λ) Λ
      ∧ 0 < -Real.log Λ
      ∧ IsGreatest (spectrum ℝ (MassGap.GNSHilbert.opT D)) 1 :=
  ⟨spectrum_opT_subset_of_positiveTransfer_of_rayleigh D hΛ.le hP hray,
    by simpa using Real.log_neg hΛ h1,
    MassGap.GNSHilbert.isGreatest_one_spectrum_opT D⟩

#print axioms spectrum_opT_strict_band

/-- **The gap, in the spectral form Clay asks for, with no `ε`.**

Clay asks for `spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ` at some `Δ > 0`. Under `T = exp (-H)` that is
`spectrum ℝ T ⊆ {1} ∪ Set.Icc 0 (Real.exp (-Δ))` — **with `0` admitted**, because a theory whose
energies are unbounded has a transfer spectrum accumulating at zero. This is that statement, and it
follows from the Rayleigh ceiling and `PositiveTransfer` alone: the band from
`spectrum_opT_subset_of_positiveTransfer_of_rayleigh` cuts the top, and
`GNSHilbert.spectrum_opT_nonneg` cuts the bottom, leaving `{1} ∪ Icc 0 Λ`.

**Why this is the right form, and `reconstruct_qm_core`'s `hsp` is not.** That one asks for
`Set.Icc ε (Real.exp (-Δ))` with `0 < ε`, which excludes `0` from the spectrum — by
`TransferInvertibility.isUnit_of_spectral_hypothesis`, exactly `IsUnit T`, and by
`energies_bounded_of_spectral_hypothesis`, exactly a ceiling on the energies. A quantum field theory
has no such ceiling, so `ε` is not an obligation waiting to be discharged; it is a hypothesis the
intended model does not satisfy. `TransferInvertibility.spectral_hypothesis_fails_for_compact` says
the same thing from the other side: on an infinite-dimensional space a compact `T` meets `hsp` at no
`ε` at all.

The Lean side agrees and says why. `Reconstruction.hamiltonian T := cfc (fun x => -Real.log x) T`
needs `-Real.log` continuous on the spectrum, and it is not continuous at `0`. So `ε` is what buys
the bounded-operator functional calculus its continuity — not what buys the gap. An unbounded
Hamiltonian is outside what `cfc` on a `→L` can express, and stating the gap on `T` avoids needing
it: `Δ = -Real.log Λ` is a real number either way, and
`TransferInvertibility.gap_pos_of_lt_one` makes it positive.

Scope: this is the spectral containment, not `MassFinite.clayMass`. Turning it into a statement about
a Hamiltonian still needs an unbounded functional calculus, and that is a separate development from
the one `Reconstruction` carries.

DERIVED: `1` is the vacuum eigenvalue and the contraction constant; `0` is the bottom of the
spectrum, which `spectrum_opT_nonneg` supplies, and the lower end of the coupling range in `hΛ`;
`Δ = -Real.log Λ` is the band's own width read logarithmically. The `2` is the Rayleigh quotient's exponent in `hray`. Nothing is chosen. -/
theorem spectrum_opT_gap_form (D : TransferData A) {Λ : ℝ}
    (hΛ : 0 < Λ) (h1 : Λ < 1) (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    0 < -Real.log Λ ∧
      spectrum ℝ (MassGap.GNSHilbert.opT D)
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log Λ))) := by
  refine ⟨by simpa using Real.log_neg hΛ h1, ?_⟩
  rw [neg_neg, Real.exp_log hΛ]
  intro x hx
  rcases spectrum_opT_subset_of_positiveTransfer_of_rayleigh D hΛ.le hP hray hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Set.mem_Ici.mp (MassGap.GNSHilbert.spectrum_opT_nonneg D hP hx), h.2⟩

#print axioms spectrum_opT_gap_form

/-! ## Footprints -/

section Audit
#print axioms toH
#print axioms toH_def
#print axioms inner_coe_ofPair
#print axioms norm_coe_ofPair
#print axioms coe_ofPair_eq_zero_iff
#print axioms opT_coe_ofPair
#print axioms intertwines
#print axioms toH_vac
end Audit

end MassGap.GNSCompare
