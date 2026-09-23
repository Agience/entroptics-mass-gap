import Mathlib
import MassGap.Reflect
import MassGap.Spectral

/-!
# MassGap.Transfer — the reflection form, its GNS quotient, and a transfer operator on it

Four layers, each abstract over a real module `A`:

1. `reflForm N τ c β F G = ⟨(F ∘ θ) * G⟩`, the Osterwalder–Seiler pairing of the `d`-dimensional
   `SU(N)` Wilson system at the coordinate reflection `θ = Reflect.reflConf τ c`.
   `reflForm_symm` proves it symmetric, from `Reflect.expect_reflect_invariant` and `θ ∘ θ = id`;
   `reflForm_one_one` proves `⟨1, 1⟩ = 1`.
2. `PreForm A` — a symmetric bilinear form. `ReflForm A` extends it with one further field,
   `form_nonneg : ∀ x, 0 ≤ form x x`. From that field: `cauchy_schwarz`,
   `abs_form_le_sqrt_mul`, and `nullSpace` as a `Submodule`.
   `le_zero_of_halving` and `le_of_iterated_schwarz` are the arithmetic of an iterated Schwarz
   step: if `s k ≤ √(s (k+1)) * √M` at every `k` and the sequence is bounded above at all, then
   `s 0 ≤ M`, with no dependence on the number of steps or on the crude bound.
3. `GNS P = A ⧸ P.nullSpace`, carrying `bilQ` as an `InnerProductSpace ℝ`. Definiteness holds by
   construction, the null space having been quotiented out.
4. `TransferData A` extends `ReflForm A` with a translation `T`, a vacuum `vac`, and four fields:
   `T_symm` (self-adjointness for the form), `T_contract`, `T_vac` and `vac_norm`. From these,
   `Tq` descends `T` to the quotient, `Tq_isSymmetric`, `Tq_vacGNS`, `norm_vacGNS` and
   `norm_TqL_le_one` follow, and in finite dimension `inner_pow_expand` gives
   `⟨v, T^k v⟩ = ∑ᵢ ⟨eᵢ, v⟩ ^ 2 * λᵢ ^ k`. `periodicCorr` symmetrises that into
   `⟨v, T^d v⟩ + ⟨v, T^(per-d) v⟩`, and `periodicSpectralForm_of_transfer` presents it as a
   `Spectral.PeriodicSpectralForm`.

## Scope

* No `ReflForm` is constructed from `reflForm` in this module; `form_nonneg` is a field, so a
  caller supplies it. Two `ReflForm`s built from the Wilson measure do exist elsewhere and are
  foundational-only: `ReflectionStrong.wilsonGibbsReflForm` and `LogConvex.wilsonReflForm`, each on
  the finite periodic torus at one plane. `Complete.wilson_reflection_positive_at` is a different
  statement — componentwise nonnegativity of a lag-correlation vector together with a positive sum,
  naming no plane, reflection or form — whose body is proved at even extent at least four and
  `0 ≤ β` by `Complete.wilson_reflection_positive_at_even`. A `ReflForm` at a family of planes for
  one state is not in this tree, and `ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` shows no
  finite region is stable under two mirrors of such a family.
* Positivity of the transfer operator, `0 ≤ form x (T x)`, is not a field of `TransferData` and
  does not follow from its fields: `T_contract` bounds `|λ|` and says nothing about the sign of
  `λ`. It is carried as a named hypothesis of `eigenvalue_nonneg` and
  `periodicSpectralForm_of_transfer`.
* `T_vac`, `vac_norm`, `Tq_vacGNS`, `norm_vacGNS` and `norm_TqL_le_one` are normalisation: the
  Gibbs state is a probability state, so the vacuum has norm one and `T` is an expectation. None of
  them is a gap statement, and nothing here proves a bound on the spectrum.
* `one_le_of_eigenvalues_le` states that `∀ i, λ i ≤ r` forces `1 ≤ r`, because the vacuum is a unit
  eigenvector at eigenvalue one. So a hypothesis of the form `∀ k, lam k ≤ r` with `r < 1` — as in
  `Complete.ym_mass_gap_at_floor`'s `hdecay` and `Spectral.periodic_decay_le` — has no instance when
  read over the full transfer spectrum. `Spectral.PeriodicSpectralForm` carries no field excluding
  the vacuum mode, so every form produced by `periodicSpectralForm_of_transfer` contains it;
  `periodicCorr_vac` computes the vacuum's own correlator as the constant `2`. The proof of
  `one_le_of_eigenvalues_le` uses neither positivity of `T` nor any gap.
* `periodicCorr` is `⟨v, T^d v⟩ + ⟨v, T^(per-d) v⟩`, the ground-state periodic shape, which is what
  `PeriodicSpectralForm`'s one-index form has room for. The finite-`per` thermal correlator
  `Tr (A T^d A T^(per-d)) / Tr (T^per)` is a double spectral sum
  `∑_{i,j} |A_{ij}| ^ 2 * λ i ^ d * λ j ^ (per - d)` and is not of that shape; `periodicCorr` is
  its `j = vacuum` row, symmetrised.
* Nothing here identifies the Wilson measure with a `TransferData`. That would need reflection
  positivity as above, a half-space splitting of the observable algebra with the cross term handled,
  and the lattice time shift as an operator on half-space observables.
* The engine in Part 2a knows nothing about a lattice, a reflection plane, or how a product over a
  region splits into two reflected halves; `ReflForm.cauchy_schwarz` is the single step it would
  iterate.
-/

namespace MassGap.Transfer

open MassGap MassGap.LatticeGauge MassGap.WilsonHypercubic MassGap.CompactGauge

/-! ## Part 1 — the reflection form on the Wilson measure

The concrete object. Two of its properties are proved outright; the third, positivity, is the open
axiom and is deliberately absent.
-/

section Wilson

variable {d n : ℕ}

/-- The Osterwalder–Seiler reflection pairing of the `d`-dimensional `SU N` Wilson system:
`reflForm N τ c β F G` is the Gibbs expectation of `fun U => F (reflConf τ c U) * G U`, with
`reflConf τ c` the coordinate reflection carrying its dagger.

Scope: written for observables of the whole configuration, not of a half-space. Symmetry and
normalisation, the two properties proved here, hold for any observable; positivity, which would need
the split, is not claimed.

DERIVED: nothing numeric. `τ`, `c`, `β` and the observables are the caller's. -/
noncomputable def reflForm (N : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) : ℝ :=
  (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
    (fun U => F (Reflect.reflConf τ c U) * G U)

/-- Congruence for the Gibbs expectation: pointwise-equal observables have equal expectations, by
`funext`. Stated separately so the reflection identities can be closed without rewriting under a
binder whose type is `Config` on one side and `Link d n → SU N` on the other.

DERIVED: no numeral occurs. -/
theorem expect_congr (N : ℕ) [NeZero n] (β : ℝ) {O O' : (sysWilson N d n).Config → ℝ}
    (h : ∀ U, O U = O' U) :
    (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  rw [funext h]

/-- `reflForm N τ c β F G = reflForm N τ c β G F` at every pair of observables. Applying
`Reflect.expect_reflect_invariant` to `fun U => F (θ U) * G U` moves the reflection from `F` to `G`,
and `Reflect.reflConf_involutive` cancels the double reflection left behind. The invariance itself
rests on the dagger, the conjugated holonomy and inversion-invariance of Haar.

DERIVED: no numeral occurs. -/
theorem reflForm_symm (N : ℕ) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    reflForm N τ c β F G = reflForm N τ c β G F := by
  have hinv : ∀ U : Link d n → MassGap.SUN.SU N,
      Reflect.reflConf τ c (Reflect.reflConf τ c U) = U := Reflect.reflConf_involutive τ c
  have h := Reflect.expect_reflect_invariant N τ c β
    (fun U => F (Reflect.reflConf τ c U) * G U)
  simp only [hinv] at h
  exact Eq.trans h.symm (expect_congr N β (fun U => mul_comm _ _))

/-- `reflForm N τ c β 1 1 = 1` for `N ≠ 0`: the constant observable pairs with itself to the total
mass, which is one because the Gibbs state is a probability state
(`WilsonReal.wilsonSystem_expect_one`). This is where the transfer operator's eigenvalue one comes
from.

DERIVED: `0` is the value `N` must differ from, which is what makes the gauge group nonempty and the
partition function positive; the `1`s are the constant observable in each slot and the total mass of
a probability measure. -/
theorem reflForm_one_one (N : ℕ) (hN : N ≠ 0) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ) :
    reflForm N τ c β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 :=
  calc reflForm N τ c β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β (fun _ => (1 : ℝ)) :=
        expect_congr N β (fun _ => one_mul 1)
    _ = 1 := MassGap.WilsonReal.wilsonSystem_expect_one (N := N) hN (bd (d := d) (n := n)) β

end Wilson

/-! ## Part 2 — a symmetric form, its Cauchy–Schwarz, and its null space -/

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A symmetric bilinear form on a real module: a function `form : A → A → ℝ` with symmetry,
additivity and homogeneity in the first slot. No positivity.

DERIVED: no numeral occurs in the fields. -/
structure PreForm (A : Type*) [AddCommGroup A] [Module ℝ A] where
  /-- The form itself. -/
  form : A → A → ℝ
  /-- Symmetry, which `reflForm_symm` proves for the Wilson form. -/
  form_symm : ∀ x y, form x y = form y x
  /-- Additivity in the first slot; with symmetry that gives it in both. -/
  form_add_left : ∀ x y z, form (x + y) z = form x z + form y z
  /-- Homogeneity in the first slot. -/
  form_smul_left : ∀ (r : ℝ) (x y), form (r • x) y = r * form x y

/-- A `PreForm` together with one further field, `form_nonneg : ∀ x, 0 ≤ form x x`. Every theorem
below that uses positivity takes a `ReflForm`, so the property cannot enter without being named.

Scope: nothing in this module constructs a `ReflForm` from `reflForm`. Three producers elsewhere do.

`ReflectionStrong.wilsonGibbsReflForm` and `LogConvex.wilsonReflForm` build one from the Wilson
measure, each on the finite periodic torus at one plane, and both are foundational-only.

`InfiniteReflection.stateReflForm R ν A hinv hpos` builds one for a state `ν` on any
`A : Submodule ℝ C(X, ℝ)`, with `form_nonneg` supplied by `hpos : ReflPositiveOn R A ν`. Taken at
`A := HalfSpaceAlgebra.halfSpaceAlg τ p`, this is a `ReflForm` on the infinite-volume `ℤ⁴`
half-space algebra, and `ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto` discharges its
`hpos` for a limit of Wilson box states at every real coupling. `WilsonTransferReduction.transferData_of_state_facts`
carries it to a full `TransferData` there.

`Complete.wilson_reflection_positive_at` is a different statement, about a lag-correlation vector
rather than a form.

A `ReflForm` at a FAMILY of planes for one state is not in this tree, and
`ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` shows no finite region is stable under two
mirrors of such a family. That is a statement about a family; the single-plane forms above exist.

DERIVED: the one numeral is the `0` of `form_nonneg`, the lower bound on the diagonal. -/
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

/-! ## Part 2a — the multiple-reflection engine

A chessboard estimate bounds a quantity over a whole region by a single-block quantity, with no
factor counting the blocks. The mechanism is one Schwarz step applied over and over: each step
halves the region and doubles what sits in it, so the exponent on the unknown halves while the
single-block bound accumulates. In the limit the unknown drops out entirely.

On the logarithms it is linear arithmetic, which is what the first theorem is; the second puts it
back in the multiplicative form a reflection-positive state presents.

**⛔ THIS IS THE ENGINE, NOT AN ESTIMATE.** Nothing here knows about a lattice, a reflection plane,
or how a product over a region splits into two reflected halves. Supplying that geometry for the
Wilson state is the open work; `ReflForm.cauchy_schwarz` below, reachable for a state through
`InfiniteReflection.stateReflForm`, is the single step it would iterate. -/

/-- **HALVING, ITERATED, KILLS THE UNKNOWN.** If each term is at most half the next, and the
sequence is bounded above BY ANYTHING, then the first term is at most zero.

`D` may be any real — it is not assumed small, positive, or related to the sequence. That is the
content: `d 0 · 2^n ≤ D` for every `n`, which a positive `d 0` cannot survive.

DERIVED: the `2` is the halving of one Schwarz step — a square root on the multiplicative side. The
`0` is what the iterated bound forces, and the `1` is the index shift to the next term. None is
chosen. -/
theorem le_zero_of_halving {d : ℕ → ℝ} {D : ℝ} (hstep : ∀ k, d k ≤ d (k + 1) / 2)
    (hbd : ∀ k, d k ≤ D) : d 0 ≤ 0 := by
  have hiter : ∀ n : ℕ, d 0 * 2 ^ n ≤ d n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hk := hstep k
      have hrw : d 0 * 2 ^ (k + 1) = 2 * (d 0 * 2 ^ k) := by ring
      rw [hrw]
      linarith
  have hle : ∀ n : ℕ, d 0 * 2 ^ n ≤ D := fun n => le_trans (hiter n) (hbd n)
  by_contra hcon
  push_neg at hcon
  have hgrow : Filter.Tendsto (fun n : ℕ => d 0 * 2 ^ n) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hcon
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  obtain ⟨n, hn⟩ := (hgrow.eventually_gt_atTop D).exists
  exact absurd (hle n) (not_le.mpr hn)

#print axioms le_zero_of_halving

/-- **⭐ AND MULTIPLICATIVELY: THE ITERATED SCHWARZ BOUND.** If every term is at most the geometric
mean of the next and a fixed `M`, and the sequence is bounded above at all, then the FIRST term is
at most `M`.

This is what a chessboard estimate concludes. `M` is the single-block quantity; `s 0` is the one
over the whole region; and `B`, the crude bound the sequence never exceeds, does not appear in the
conclusion. **The number of halvings does not appear either** — that is the volume-independence.

DERIVED: the `0`s are the positivity hypotheses — `M` and each `s k` must be positive for their
logarithms to exist — and the `1` is the index shift to the next term. The square roots are one
Schwarz step, and `le_zero_of_halving` carries the `2` they become on the logarithms. -/
theorem le_of_iterated_schwarz {s : ℕ → ℝ} {M B : ℝ} (hM : 0 < M) (hs : ∀ k, 0 < s k)
    (hB : ∀ k, s k ≤ B)
    (hstep : ∀ k, s k ≤ Real.sqrt (s (k + 1)) * Real.sqrt M) : s 0 ≤ M := by
  have hlog : ∀ k, Real.log (s k) - Real.log M
      ≤ (Real.log (s (k + 1)) - Real.log M) / 2 := by
    intro k
    have hsq : Real.log (Real.sqrt (s (k + 1)) * Real.sqrt M)
        = Real.log (s (k + 1)) / 2 + Real.log M / 2 := by
      rw [Real.log_mul (Real.sqrt_pos.mpr (hs (k + 1))).ne' (Real.sqrt_pos.mpr hM).ne',
        Real.log_sqrt (hs (k + 1)).le,
        Real.log_sqrt hM.le]
    have hmono : Real.log (s k) ≤ Real.log (Real.sqrt (s (k + 1)) * Real.sqrt M) :=
      Real.log_le_log (hs k) (hstep k)
    rw [hsq] at hmono
    linarith
  have hbd : ∀ k, Real.log (s k) - Real.log M ≤ Real.log B - Real.log M := by
    intro k
    have := Real.log_le_log (hs k) (hB k)
    linarith
  have h0 := le_zero_of_halving hlog hbd
  have : Real.log (s 0) ≤ Real.log M := by linarith
  exact (Real.log_le_log_iff (hs 0) hM).mp this

#print axioms le_of_iterated_schwarz


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

/-- `|P.form x y| ≤ √(P.form x x) * √(P.form y y)`: the square-root form of Cauchy–Schwarz, which
`le_of_iterated_schwarz` consumes. Obtained from `cauchy_schwarz` by `Real.sqrt_le_sqrt`,
`Real.sqrt_sq_eq_abs` and `Real.sqrt_mul`, the last needing `0 ≤ P.form x x` from `form_nonneg`.

DERIVED: no numeral occurs in the statement; the exponent `2` that `cauchy_schwarz` produces is
undone by the square roots in the proof. -/
theorem abs_form_le_sqrt_mul (x y : A) :
    |P.form x y| ≤ Real.sqrt (P.form x x) * Real.sqrt (P.form y y) := by
  have hcs := P.cauchy_schwarz x y
  have hx : 0 ≤ P.form x x := P.form_nonneg x
  have hstep : Real.sqrt ((P.form x y) ^ 2) ≤ Real.sqrt (P.form x x * P.form y y) :=
    Real.sqrt_le_sqrt hcs
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul hx] at hstep

#print axioms abs_form_le_sqrt_mul

/-- `P.form x y = 0` for every `y`, when `x` lies in the null space. Cauchy–Schwarz bounds the
square of the pairing by zero. This is what makes the form descend to the quotient.

DERIVED: the one numeral is `0`, the value of the pairing. -/
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

/-- Every element of `GNS P` is `mk P x` for some `x : A`, by surjectivity of the quotient map.

DERIVED: no numeral occurs. -/
theorem exists_mk (q : GNS P) : ∃ x : A, mk P x = q :=
  Submodule.Quotient.mk_surjective _ q

@[simp] theorem mk_add (x y : A) : mk P (x + y) = mk P x + mk P y := rfl

@[simp] theorem mk_smul (r : ℝ) (x : A) : mk P (r • x) = r • mk P x := rfl

@[simp] theorem mk_zero : mk P (0 : A) = 0 := rfl

/-- `mk P x = 0 ↔ P.form x x = 0`: a class vanishes exactly when its representative is null. This
is the `definite` field of an inner product, before it is packaged as one.

DERIVED: `0` is the zero of the quotient on the left and the value of the form on the right. -/
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

/-- `bilQ P (mk P x) (mk P y) = P.form x y`. `bilQ` lifts the second slot last, so on
representatives it lands on `P.form y x`, and `form_symm` turns that into `P.form x y`.

DERIVED: no numeral occurs. -/
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

/-- `‖mk P x‖ * ‖mk P x‖ = P.form x x`, from `real_inner_self_eq_norm_mul_norm` and `inner_mk`.

DERIVED: no numeral occurs. -/
theorem norm_mk_mul_norm_mk (x : A) : ‖mk P x‖ * ‖mk P x‖ = P.form x x := by
  rw [← real_inner_self_eq_norm_mul_norm, inner_mk]

end GNS

/-! ## Part 4 — the transfer operator -/

/-- A `ReflForm A` together with a linear `T : A →ₗ[ℝ] A`, a vector `vac : A`, and four fields:

* `T_symm : ∀ x y, form (T x) y = form x (T y)` — self-adjointness for the reflection form;
* `T_contract : ∀ x, form (T x) (T x) ≤ form x x` — the translation does not increase the form;
* `T_vac : T vac = vac`;
* `vac_norm : form vac vac = 1`.

Scope: `T_contract`, `T_vac` and `vac_norm` are normalisation — the Gibbs measure is a probability
measure, so the transfer operator is an expectation and the constant observable is invariant and of
unit form. None of them is a spectral bound. Positivity of `T`, `0 ≤ form x (T x)`, is not a field
here; it does not follow from these and is carried as a named hypothesis where it is used.

DERIVED: the one numeral in the fields is the `1` of `vac_norm`, the total mass of a probability
measure. -/
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

/-- `D.T x` lies in the null space whenever `x` does: `T_contract` puts `form (T x) (T x)` at or
below `0` and `form_nonneg` at or above it. This is what lets `T` descend to the quotient.

DERIVED: no numeral occurs in the statement; the `0` of the null space is inside `nullSpace`. -/
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

/-- `(Tq D).IsSymmetric`, directly from the structure field `T_symm` read on representatives. This
is the hypothesis Mathlib's finite-dimensional spectral theorem consumes.

DERIVED: no numeral occurs. -/
theorem Tq_isSymmetric (D : TransferData A) : (Tq D).IsSymmetric := by
  intro q r
  obtain ⟨x, rfl⟩ := GNS.exists_mk q
  obtain ⟨y, rfl⟩ := GNS.exists_mk r
  simp only [Tq_mk, GNS.inner_mk]
  exact D.T_symm x y

/-- **THE VACUUM** `Ω = [1]`.

DERIVED: nothing numeric. -/
noncomputable def vacGNS (D : TransferData A) : GNS D.toReflForm := GNS.mk D.toReflForm D.vac

/-- `Tq D (vacGNS D) = vacGNS D`, from the structure field `T_vac`. So the vacuum is an eigenvector
at eigenvalue one, by translation invariance of the constant observable rather than by any spectral
argument.

DERIVED: no numeral occurs in the statement. -/
theorem Tq_vacGNS (D : TransferData A) : Tq D (vacGNS D) = vacGNS D := by
  simp only [vacGNS, Tq_mk, D.T_vac]

/-- **`‖Ω‖ = 1`** — so the vacuum is not the zero vector and the eigenvalue one is genuinely attained.

DERIVED: the `1` is the total mass of a probability measure, carried through `vac_norm`. -/
theorem norm_vacGNS (D : TransferData A) : ‖vacGNS D‖ = 1 := by
  have h : ‖vacGNS D‖ * ‖vacGNS D‖ = 1 := by
    rw [vacGNS, GNS.norm_mk_mul_norm_mk]
    exact D.vac_norm
  nlinarith [norm_nonneg (vacGNS D)]

/-- `‖Tq D q‖ ≤ ‖q‖` at every `q`, from the structure field `T_contract` through
`GNS.norm_mk_mul_norm_mk`.

DERIVED: no numeral occurs in the statement. -/
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

/-- `(S ^ k).IsSymmetric` at every `k : ℕ`, for a symmetric `S` on a real inner product space. By
induction on `k`.

DERIVED: no numeral occurs in the statement; `k` is the caller's power. -/
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

/-- `((Tq D) ^ k) (eigenvectorBasis i) = (eigenvalues i ^ k) • eigenvectorBasis i`, by induction on
`k` from `apply_eigenvectorBasis`.

DERIVED: no numeral occurs in the statement; `k` is the power and `m` the finite dimension. -/
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

/-- In finite dimension `m`, `⟨v, (Tq D) ^ k v⟩ = ∑ i, ⟨eᵢ, v⟩ ^ 2 * λᵢ ^ k`, where `eᵢ` and `λᵢ`
are the eigenvector basis and eigenvalues of `Tq_isSymmetric D`. Expands `v` in the orthonormal
eigenbasis and applies `Tq_pow_eigenvectorBasis`.

Scope: this is the half-line shape. `Spectral.flat_of_aperiodic` is why it is not a finite-volume
correlator on its own.

DERIVED: the one numeral is the exponent `2` on the inner product, which is what makes the weights
nonnegative. -/
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

/-- `0 ≤ (Tq_isSymmetric D).eigenvalues hm i` at every `i`, given
`hpos : ∀ x : A, 0 ≤ D.form x (D.T x)`. The hypothesis descends to the quotient and is read at the
eigenvector basis.

Scope: `hpos` does not follow from `T_contract`, which bounds `|λ|` and says nothing about its sign.
It is reflection positivity about a half-integer time plane, and is carried here as an explicit
hypothesis.

DERIVED: the one numeral is `0`, the lower bound in the hypothesis and in the conclusion. -/
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

/-- `periodicCorr D v per d = ⟨v, (Tq D) ^ d v⟩ + ⟨v, (Tq D) ^ (per - d) v⟩`, the half-line
correlator symmetrised under `d ↦ per - d`. That symmetry is the property
`Spectral.flat_of_aperiodic` shows the half-line shape cannot have on its own without going flat.

Scope: this is not the finite-`per` thermal correlator, which is
`Tr (A T^d A T^(per-d)) / Tr (T^per)` and in the eigenbasis is a double sum
`∑_{i,j} |A_{ij}| ^ 2 * λ i ^ d * λ j ^ (per - d)`, carrying two spectral indices rather than one.
`periodicCorr` is that sum's `j = vacuum` row, where `λ j = 1`, symmetrised.

DERIVED: nothing numeric. `per` is the caller's period and the two terms are the two ways round the
circle. -/
noncomputable def periodicCorr (D : TransferData A) (v : GNS D.toReflForm) (per : ℕ)
    (d : Fin per) : ℝ :=
  inner ℝ v (((Tq D) ^ (d : ℕ)) v) + inner ℝ v (((Tq D) ^ (per - (d : ℕ))) v)

/-- A `Spectral.PeriodicSpectralForm per (periodicCorr D v per)` built from the transfer operator:
`Idx := Fin m`, `w i := ⟨eᵢ, v⟩ ^ 2`, `lam i := λᵢ`, with `hw` from `sq_nonneg`, `hlam0` from
`eigenvalue_nonneg` and `hlam1` from `abs_eigenvalue_le_one`, and `hrep` from `inner_pow_expand` at
both lags.

Scope: takes finite dimension of the GNS space and `hpos : ∀ x, 0 ≤ D.form x (D.T x)`, the latter
not following from contractivity. It proves no bound on `lam`.

DERIVED: the one numeral in the statement is the `0` of `hpos`, positivity of the transfer operator.
Every field is read off the spectral decomposition. -/
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

/-- `∑ i, ⟨eᵢ, v⟩ ^ 2 = ‖v‖ * ‖v‖`: the spectral weights of `v` sum to its squared norm.
`inner_pow_expand` at `k = 0`, where every `λᵢ ^ 0` is one, followed by
`real_inner_self_eq_norm_mul_norm`.

DERIVED: the one numeral in the statement is the exponent `2` on the inner product, the weight's own
degree. The power `0` at which `inner_pow_expand` is applied is in the proof. -/
theorem sum_weights (hm : Module.finrank ℝ (GNS D.toReflForm) = m) (v : GNS D.toReflForm) :
    ∑ i, (inner ℝ ((Tq_isSymmetric D).eigenvectorBasis hm i) v) ^ 2 = ‖v‖ * ‖v‖ := by
  have h := inner_pow_expand D hm v 0
  simp only [pow_zero, mul_one] at h
  rw [← h]
  exact real_inner_self_eq_norm_mul_norm v

omit [FiniteDimensional ℝ (GNS D.toReflForm)] in
/-- `periodicCorr D (vacGNS D) per d = 2` at every lag. `Tq_vacGNS` makes every power fix the
vacuum and `norm_vacGNS` makes each inner product one, so both terms of the periodic shape are one.

Scope: this is a correlator with a `PeriodicSpectralForm` and no decay, so that structure alone
carries no gap.

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

/-- `(∀ i, (Tq_isSymmetric D).eigenvalues hm i ≤ r) → 1 ≤ r`, in finite dimension `m`. The vacuum is
an eigenvector at eigenvalue one (`Tq_vacGNS`) and a unit vector (`norm_vacGNS`), so
`inner_pow_expand` at `k = 1` puts `1 = ∑ wᵢ λᵢ ≤ r * ∑ wᵢ = r`.

Scope: a hypothesis `∀ k, lam k ≤ r` with `r < 1` — the shape of
`Complete.ym_mass_gap_at_floor`'s `hdecay` and of `Spectral.periodic_decay_le` — therefore has no
 instance when read over the full transfer spectrum. `Spectral.PeriodicSpectralForm` carries no field
excluding the vacuum mode, so every form built by `periodicSpectralForm_of_transfer` contains it.
The proof uses neither positivity of `T` nor any gap, only normalisation.

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

/-- Given `0 ≤ r` and `∀ i, λᵢ ≤ r`, and a lag `d` with `2 * d ≤ per`,
`periodicCorr D v per d ≤ 2 * (∑ i, ⟨eᵢ, v⟩ ^ 2) * r ^ d`. `Spectral.periodic_decay_le` applied to
`periodicSpectralForm_of_transfer`.

Scope: `hgap` here is the hypothesis of `one_le_of_eigenvalues_le`, which concludes `1 ≤ r`, so in
every instance `r ^ d` is non-decreasing in `d` and this is a bound rather than a decay statement.
Nothing here proves `hgap`.

DERIVED: `0` is the lower bound on `r`; `2` is the two terms of the periodic shape, inherited from
`Spectral.periodic_decay_le`, and the doubling in `2 * d ≤ per`, which restricts the lag to the
half-period where a torus correlator has not yet turned back up; the exponent `2` is the weight's
degree. -/
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
