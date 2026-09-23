import Mathlib
import MassGap.Certify

/-!
# MassGap.Apriori — two named propositions, and what follows from them

This file names two propositions on the framework's own objects and derives consequences from them as
hypotheses. Neither is proved here.

`A1 μ κ₀` is `∀ β, μ β < κ₀`: the tension read stays below the counting floor at every coupling.

`A2 R` is `∀ d d', R d = R d'` for a read `R : D → ℝ` on an arbitrary type `D` of orientations: the
read takes the same value in every direction.

What the file contains:

* consequences of `A1` — decay of a finite sum of powers to zero (`gap_of_A1`), and the sign
  statement `μ β - κ < 0` for any `κ` at or above the floor (`nontrivial_of_A1`);
* the restatement of `A2` as direction-independence (`euclidean_of_A2`), and
  `existence_and_gap_from_apriori`, which assembles the three conclusions from the two hypotheses;
* a real-number identity `-(s/δ)·log(m^{1/s}) = -(1/δ)·log m` (`continuum_well_defined`), quantified
  over a bare positive real `m`;
* partial results towards `A1`: an arithmetic threshold lemma at strong coupling
  (`apriori_A1_strong`), a limit argument at weak coupling (`apriori_A1_weak`), and two lemmas
  relating the read hypothesis to a dominant-magnitude bound;
* partial results towards `A2`: invariance of a symmetric functional of per-axis reads under axis
  permutations (`read_hypercubic_invariant`), invariance of a spectral functional under orthogonal
  congruence (`read_orthogonal_invariant`), and a chain reducing `A2` for a Gram-valued correlation to
  the orthogonality of a resample-after-rotation operator (`A2_continuum_of_sampling`).

Scope. The matrix results are stated over an arbitrary finite index type, and no rotation group
appears in any statement: what is proved of an orthogonal `P` is proved of every orthogonal `P`.
Several declarations cite external results by name; nothing here proves them.
-/

namespace MassGap

open scoped Matrix

/-- A1, confinement, as a proposition about a function `μ : ℝ → ℝ` and a real `κ₀`: `μ β < κ₀` at
every `β`. The coupling ranges over all of `ℝ`, with no restriction to a half-line.

DERIVED: no numeral. -/
def A1 (μ : ℝ → ℝ) (κ₀ : ℝ) : Prop := ∀ β, μ β < κ₀

/-- A2, isotropy, as a proposition about a read `R : D → ℝ`: `R d = R d'` for every pair of
orientations. `D` is an arbitrary type and carries no group structure, so the statement is
constancy of `R`.

DERIVED: no numeral. -/
def A2 {D : Type*} (R : D → ℝ) : Prop := ∀ d d', R d = R d'

/-- From `A1 μ κ₀` and a per-mode bound `‖m β k‖ ≤ exp(-(κ₀ - μ β))` on the finite index set `s β`, the
norm `‖∑_{k ∈ s β} P β k · (m β k)^τ‖` tends to zero as `τ → ∞`, at every coupling. It is
`gap_of_confinement_read`; `A1` is what makes the exponent negative, so each `‖m β k‖` is below one.
The conclusion is convergence to zero, not a rate.

DERIVED: the `0` is the limit the norm converges to. -/
theorem gap_of_A1 {ι : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ) (κ₀ : ℝ) (μ : ℝ → ℝ)
    (h1 : A1 μ κ₀)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    ∀ β, Filter.Tendsto
      (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement_read s P m κ₀ μ h1 hread

/-- From `A1 μ κ₀` and any `κ` at or above the floor, `μ β - κ < 0` at every coupling. It is
`confines_of_tension_lt_floor` applied pointwise: the content is the transitivity
`μ β < κ₀ ≤ κ`. The statement is about the sign of a difference of reals and mentions no observable.

DERIVED: the `0` is the sign asserted of `μ β - κ`. -/
theorem nontrivial_of_A1 {κ₀ κ : ℝ} {μ : ℝ → ℝ} (hfloor : κ₀ ≤ κ) (h1 : A1 μ κ₀) :
    ∀ β, μ β - κ < 0 :=
  fun β => confines_of_tension_lt_floor hfloor (h1 β)

/-- `A2 R` unfolded: the hypothesis and the conclusion are the same proposition, and the proof is the
hypothesis itself. It records the definitional content of `A2` and adds nothing to it.

DERIVED: no numeral. -/
theorem euclidean_of_A2 {D : Type*} (R : D → ℝ) (h2 : A2 R) : ∀ d d', R d = R d' := h2

/-- A real-number identity: `-(s/δ)·log(m^{1/s}) = -(1/δ)·log m` for positive `δ`, `s` and `m`. It is
`gap_refinement_invariant`. The quantification is over bare positive reals; `m` is not tied to the
spectrum of anything, and `hδ` and `hs` enter as side conditions on the division.

DERIVED: the three `0`s are the positivity conditions on `δ`, `s` and `m`; the `1` in `m ^ (1/s)` is
the numerator of the refinement exponent and the `1` in `1/δ` is the single step the rate is read
per. -/
theorem continuum_well_defined {δ m s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hm : 0 < m) :
    -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m :=
  gap_refinement_invariant hδ hs hm

/-- The three conclusions together, from `A1`, `A2`, the floor comparison `κ₀ ≤ κ` and the per-mode
bound `hread`: the correlator norm tends to zero at every coupling, `μ β - κ < 0` at every coupling,
and `R` is direction-independent. The proof is the triple of `gap_of_A1`, `nontrivial_of_A1` and
`euclidean_of_A2`.

The decay conclusion is convergence to zero; a rate is a different statement, proved elsewhere as
`MassGap.mass_gap_rate_of_model`.

DERIVED: the `0` in `nhds 0` is the limit of the correlator norm and the `0` in `μ β - κ < 0` is the
sign of that difference. -/
theorem existence_and_gap_from_apriori
    {ι D : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ) (κ₀ κ : ℝ) (μ : ℝ → ℝ) (R : D → ℝ)
    (hfloor : κ₀ ≤ κ) (h1 : A1 μ κ₀) (h2 : A2 R)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, μ β - κ < 0) ∧
      (∀ d d', R d = R d') :=
  ⟨gap_of_A1 s P m κ₀ μ h1 hread, nontrivial_of_A1 hfloor h1, euclidean_of_A2 R h2⟩

/-! ## Partial results towards A1 and A2

The sections below prove statements that bear on `A1` and `A2` without proving either.

* A1, strong coupling. Taking as given the character bound `μ β ≤ 2 β r`, with `r` the leading
  character ratio `I₂(β)/I₁(β)` cited to Osterwalder-Seiler, `apriori_A1_strong` gives `μ β < κ₀` for
  every coupling below the threshold `β_c` defined by `2 β_c r = κ₀`. The content is an inequality
  between reals; the character bound itself is a hypothesis of the theorem.
* A1, weak coupling. `apriori_A1_weak` gives `μ β < κ₀` eventually in `β`, from convergence of `μ` to
  a limit strictly below the floor.
* A2, axis permutations. A read that is a functional of the multiset of per-axis reads is unchanged
  when the axes are permuted (`read_hypercubic_invariant`, `A2_hypercubic_holds`). The permutation
  group is `Equiv.Perm (Fin d)` for an arbitrary `d`.
-/

/-- With `r > 0` and `βc` defined by `2·βc·r = κ₀`, every `β < βc` satisfies `2·β·r < κ₀`. An
inequality between reals: multiplying a strict inequality by the positive `2r` and rewriting by `hc`.

DERIVED: the `0` is the sign required of `r`, which is what lets the product keep the inequality's
direction; the two `2`s are the factor the character bound carries and are the same factor on both
sides of `hc`. -/
theorem strong_below_threshold {r κ₀ β βc : ℝ} (hr : 0 < r)
    (hc : 2 * βc * r = κ₀) (hlt : β < βc) : 2 * β * r < κ₀ := by
  rw [← hc]; nlinarith

/-- Given the character bound `μ β ≤ 2·β·r` as a hypothesis, a positive `r`, and a coupling below the
threshold `βc` defined by `2·βc·r = κ₀`, the tension is below the floor: `μ β < κ₀`. It is
`strong_below_threshold` composed with `hbound`.

The statement is at one coupling and requires `β < βc`; it says nothing at or above the threshold, and
it does not prove the character bound it consumes.

DERIVED: the `0` is the sign required of `r`; the two `2`s are the factor the character bound carries,
the same factor that defines `βc` in `hc`. -/
theorem apriori_A1_strong {μ : ℝ → ℝ} {r κ₀ β βc : ℝ} (hr : 0 < r)
    (hc : 2 * βc * r = κ₀) (hlt : β < βc) (hbound : μ β ≤ 2 * β * r) : μ β < κ₀ :=
  lt_of_le_of_lt hbound (strong_below_threshold hr hc hlt)

/-! ### A1 at weak coupling, and the per-mode bound `hread`

`apriori_A1_weak` takes convergence of `μ` to a limit below the floor and returns `μ β < κ₀` eventually
in `β`. The limit and its position below the floor are both hypotheses.

`hread` (`‖m k‖ ≤ e^{-(κ₀-μ)}`) is related below to a bound on a single dominant magnitude:
`hread_of_dominant` derives the per-mode bound from a bound `r` on every mode together with
`r ≤ e^{-(κ₀-μ)}`, and `margin_of_dominant_rate` restates that second inequality as
`κ₀ - μ ≤ -log r`. -/

/-- If `μ` converges along `atTop` to a limit `L` with `L < κ₀`, then `μ β < κ₀` holds eventually in
`β`. It is convergence into the open set `Iio κ₀`. Both the limit and the strict inequality `L < κ₀`
are hypotheses, and the conclusion is eventual, so it names no coupling from which it holds.

DERIVED: no numeral. -/
theorem apriori_A1_weak {μ : ℝ → ℝ} {κ₀ L : ℝ} (hL : L < κ₀)
    (hlim : Filter.Tendsto μ Filter.atTop (nhds L)) :
    ∀ᶠ β in Filter.atTop, μ β < κ₀ :=
  hlim.eventually (isOpen_Iio.mem_nhds hL)

/-- If every mode magnitude on `s` is at most `r`, and `r ≤ e^{-(κ₀-μ)}`, then every mode magnitude is
at most `e^{-(κ₀-μ)}`, which is the `hread` that `gap_of_confinement` consumes. The proof is
transitivity. `r` is any upper bound, not necessarily the maximum.

DERIVED: no numeral. -/
theorem hread_of_dominant {ι : Type*} (s : Finset ι) (m : ι → ℂ) {κ₀ μ r : ℝ}
    (hdom : ∀ k ∈ s, ‖m k‖ ≤ r) (hr : r ≤ Real.exp (-(κ₀ - μ))) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hdom k hk) hr

/-- For positive `r`, the bound `r ≤ e^{-(κ₀-μ)}` and the inequality `κ₀ - μ ≤ -log r` are equivalent.
Taking logarithms in one direction and exponentials in the other. Read with `-log r` as a rate, it
says a bound on a magnitude and a lower bound on the corresponding rate are the same statement.

DERIVED: the `0` is the positivity of `r`, which is what makes `log r` and `exp (log r)` behave. -/
theorem margin_of_dominant_rate {κ₀ μ r : ℝ} (hr : 0 < r) :
    r ≤ Real.exp (-(κ₀ - μ)) ↔ κ₀ - μ ≤ -Real.log r := by
  constructor
  · intro h
    have hlog := Real.log_le_log hr h
    rw [Real.log_exp] at hlog; linarith
  · intro h
    have hlog : Real.log r ≤ -(κ₀ - μ) := by linarith
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp (-(κ₀ - μ)) := Real.exp_le_exp.mpr hlog

/-! ### The strong-coupling threshold

`apriori_A1_strong` takes the threshold `βc` as a hypothesis, through `2·βc·r = κ₀` with `r = I₂/I₁`
the leading character ratio and `κ₀ = ¼ log 3`.

`Bessel.strong_coupling_below_threshold`, in another file, gives `μ β < κ₀` for every `β` with
`β² < ½ log 3`. It rests on `Bessel.ratio_le_quarter` (`r(x) ≤ x/4`), which is termwise: the `I₂` and
`I₁` terms differ by one factor of `x/2` in the numerator and one factor of `k+2 ≥ 2` in the
denominator. Substituted into `2·β·r(β)` that gives `β²/2`, which is below `¼ log 3` exactly when
`β² < ½ log 3`. The bound is tight as `β → 0`. -/

/-- A read `R : Multiset ℝ → ℝ` applied to the multiset of per-axis values `a : Fin d → ℝ` is unchanged
when the axes are permuted by any `σ : Equiv.Perm (Fin d)`. The content is that permuting a `Fin d`
leaves `Finset.univ.val` alone as a multiset, so the two arguments of `R` are equal before `R` is
applied. `d` is arbitrary and no rotation group appears.

DERIVED: no numeral. -/
theorem read_hypercubic_invariant {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ)
    (σ : Equiv.Perm (Fin d)) :
    R (Finset.univ.val.map (fun i => a (σ i))) = R (Finset.univ.val.map a) := by
  have hperm : Finset.univ.val.map (⇑σ) = (Finset.univ.val : Multiset (Fin d)) := by
    have h := congrArg Finset.val (Finset.map_univ_equiv (σ : Fin d ≃ Fin d))
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  have key : Finset.univ.val.map (fun i => a (σ i)) = Finset.univ.val.map a := by
    change Finset.univ.val.map (a ∘ ⇑σ) = Finset.univ.val.map a
    rw [← Multiset.map_map, hperm]
  rw [key]

/-- The product over axes is unchanged by permuting them: `∏ i, a (σ i) = ∏ i, a i`. It is
`Equiv.prod_comp`, and it is the product read (étendue `φ_F φ_T`, space-bandwidth `n_F n_T`) stated
directly rather than through `read_hypercubic_invariant`.

DERIVED: no numeral. -/
theorem etendue_hypercubic_invariant {d : ℕ} (a : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    ∏ i, a (σ i) = ∏ i, a i := Equiv.prod_comp σ a

/-- `A2` restricted to axis permutations, as a proposition about a read `R : Multiset ℝ → ℝ` and
per-axis values `a : Fin d → ℝ`: `R` takes the same value on the permuted and unpermuted multisets,
for every `σ : Equiv.Perm (Fin d)`.

DERIVED: no numeral. -/
def A2_hypercubic {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d),
    R (Finset.univ.val.map (fun i => a (σ i))) = R (Finset.univ.val.map a)

/-- `A2_hypercubic` holds for every `R` and every `a`, with no hypothesis: it is
`read_hypercubic_invariant` at each `σ`. It is a statement about axis permutations only.

DERIVED: no numeral. -/
theorem A2_hypercubic_holds {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) :
    A2_hypercubic R a := fun σ => read_hypercubic_invariant R a σ

/-- `read_hypercubic_invariant` at a transposition: exchanging two axes `i` and `j` leaves the read
unchanged. The exchange of the ordered and feature axes is such a transposition, so it is covered;
a rotation through an arbitrary angle is not a permutation and is not covered.

DERIVED: no numeral. -/
theorem A2_axis_role_swap {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) (i j : Fin d) :
    R (Finset.univ.val.map (fun k => a (Equiv.swap i j k))) = R (Finset.univ.val.map a) :=
  read_hypercubic_invariant R a (Equiv.swap i j)

/-! ### Invariance of a spectral read under orthogonal congruence

`A2_hypercubic_holds` covers axis permutations. The lemmas below cover any congruence `C ↦ P C Pᵀ`
with `Pᵀ P = 1`: a read that is a function of the characteristic polynomial, hence of the eigenvalue
multiset, takes the same value on the two operators. Permutation matrices are one case, so this
subsumes the permutation statement at the spectral level. The reading of the congruence as a rotation
is not part of the statements. -/

/-- A read `f` of the characteristic polynomial takes the same value on `P C Pᵀ` as on `C`, whenever
`Pᵀ P = 1`. The content is `Matrix.charpoly_mul_comm`: the two operators have the same characteristic
polynomial, so `f` cannot distinguish them. `P` is any orthogonal matrix over a finite index type.

DERIVED: the `1` is the identity matrix, the value of `Pᵀ * P` that makes `P` orthogonal. -/
theorem read_orthogonal_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (P C : Matrix n n ℝ) (hP : Pᵀ * P = 1) :
    f ((P * C * Pᵀ).charpoly) = f (C.charpoly) := by
  have hcong : (P * C * Pᵀ).charpoly = C.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [hcong]

/-! ### The congruence hypothesis, and A2 from it

`read_orthogonal_invariant` gives invariance under any orthogonal congruence. Naming the hypothesis
that the orientation dependence of the correlation operator is by such a congruence,
`A2_continuum_of_congruence` then gives `A2` for every spectral read. The hypothesis is discharged in
turn by `continuumRotationCongruence_of_gram` for a Gram-valued correlation, and by
`A2_continuum_of_sampling` when the congruence is a product of isometries. -/

/-- The hypothesis that the correlation operator's dependence on orientation is by orthogonal
congruence: for every pair `d, d'` there is a `P` with `Pᵀ P = 1` and `C d' = P (C d) Pᵀ`. The
orientation type `D` is arbitrary; `P` may depend on both orientations.

DERIVED: the `1` is the identity matrix, the value of `Pᵀ * P` that makes `P` orthogonal. -/
def ContinuumRotationCongruence {D n : Type*} [Fintype n] [DecidableEq n]
    (C : D → Matrix n n ℝ) : Prop :=
  ∀ d d', ∃ P : Matrix n n ℝ, Pᵀ * P = 1 ∧ C d' = P * C d * Pᵀ

/-- Given `ContinuumRotationCongruence C`, the read `fun d => f (C d).charpoly` satisfies `A2`: it takes
the same value at every orientation. The proof takes the congruence at the two orientations and
applies `read_orthogonal_invariant`. It holds for every `f`, with no condition on `f`.

DERIVED: no numeral. -/
theorem A2_continuum_of_congruence {D n : Type*} [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (C : D → Matrix n n ℝ)
    (h : ContinuumRotationCongruence C) :
    A2 (fun d => f (C d).charpoly) := by
  intro d d'
  obtain ⟨P, hP, hC⟩ := h d d'
  show f (C d).charpoly = f (C d').charpoly
  rw [hC, read_orthogonal_invariant f P (C d) hP]

/-! ### The congruence hypothesis for a Gram-valued correlation

When the correlation operator is a Gram `C = Xᵀ X` and orientations relate by `X ↦ X Q` with
`Qᵀ Q = 1`, the congruence hypothesis is exhibited rather than assumed, with `P = Qᵀ`: the Gram
transforms as `(X Q)ᵀ (X Q) = Qᵀ (Xᵀ X) Q`. The reads cited in [E, §3, §10] (`φ`, étendue, Strehl,
`a_δ`, contrast, dominance) are functions of the eigenvalue multiset of a correlation operator; that
they are is not proved here. What remains as hypothesis is that the correlation operator is such a
Gram and that orientations relate by a coordinate change of one field. -/

/-- Rotating a field's coordinates sends its Gram to an orthogonal congruence of the original:
`(X Q)ᵀ (X Q) = Qᵀ (Xᵀ X) Q`. Matrix algebra, with no hypothesis on `Q` at all — the identity holds
for every `Q`.

DERIVED: no numeral. -/
theorem gram_rotation_congruence {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℝ) (Q : Matrix n n ℝ) :
    (X * Q)ᵀ * (X * Q) = Qᵀ * (Xᵀ * X) * Q := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- A read `f ∘ charpoly` of the Gram `Xᵀ X` is unchanged under `X ↦ X Q` for orthogonal `Q`. The proof
rewrites by `gram_rotation_congruence` and applies `read_orthogonal_invariant` at `Qᵀ`, which is
orthogonal because `Qᵀ Q = 1` gives `Q Qᵀ = 1`.

DERIVED: the `1` is the identity matrix, the value of `Qᵀ * Q` that makes `Q` orthogonal. -/
theorem gram_read_rotation_invariant {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (X : Matrix m n ℝ) (Q : Matrix n n ℝ) (hQ : Qᵀ * Q = 1) :
    f (((X * Q)ᵀ * (X * Q)).charpoly) = f ((Xᵀ * X).charpoly) := by
  rw [gram_rotation_congruence]
  have hP : (Qᵀ)ᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hQ
  have key := read_orthogonal_invariant f Qᵀ (Xᵀ * X) hP
  rw [Matrix.transpose_transpose] at key
  exact key

/-- If the correlation operator at orientation `d` is the Gram `(F d)ᵀ (F d)`, and the fields relate by
`F d' = (F d) (Q d d')` with each `Q d d'` orthogonal, then `ContinuumRotationCongruence` holds for
that Gram-valued correlation, with `P = (Q d d')ᵀ`. Both the Gram form and the relation between fields
are hypotheses.

DERIVED: the `1` is the identity matrix, the value of `(Q d d')ᵀ * (Q d d')` that makes each `Q d d'`
orthogonal. -/
theorem continuumRotationCongruence_of_gram {D m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : D → Matrix m n ℝ) (Q : D → D → Matrix n n ℝ)
    (hQ : ∀ d d', (Q d d')ᵀ * (Q d d') = 1)
    (hrot : ∀ d d', F d' = F d * Q d d') :
    ContinuumRotationCongruence (fun d => (F d)ᵀ * F d) := by
  intro d d'
  refine ⟨(Q d d')ᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp (hQ d d')
  · show (F d')ᵀ * F d' = (Q d d')ᵀ * ((F d)ᵀ * F d) * ((Q d d')ᵀ)ᵀ
    rw [hrot d d', gram_rotation_congruence, Matrix.transpose_transpose]

/-! ### The congruence as a product of isometries

`continuumRotationCongruence_of_gram` needs the orientations to relate by an orthogonal `Q`. The
lemmas below build one as a product: if a reconstruction map `Rc`, a coordinate change `Um` and a
sampling map `Sm` are each orthogonal, then so is `Rc Um Sm`, and `A2` follows for every Gram spectral
read. Orthogonality of the three factors is a hypothesis in every statement here; the appeal to the
Nyquist-Shannon sampling theorem is what would supply it, and is not formalised. -/

/-- A product of two orthogonal matrices is orthogonal.

DERIVED: the `1`s are the identity matrix, the value of `Mᵀ * M` that makes a matrix `M` orthogonal —
twice as hypothesis and once as conclusion. -/
theorem orthogonal_mul {n : Type*} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) : (P * Q)ᵀ * (P * Q) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P Q, hP, Matrix.one_mul, hQ]

/-- If `Rc`, `Um` and `Sm` are each orthogonal, so is `Rc Um Sm`. Two applications of
`orthogonal_mul`. Read as reconstruction, coordinate change and sampling, it says the
resample-after-rotation operator is orthogonal; the orthogonality of the three factors is supplied by
the caller.

DERIVED: the `1`s are the identity matrix, the value of `Mᵀ * M` that makes a matrix `M` orthogonal —
three times as hypothesis and once as conclusion. -/
theorem resampling_orthogonal {n : Type*} [Fintype n] [DecidableEq n] {Rc Um Sm : Matrix n n ℝ}
    (hR : Rcᵀ * Rc = 1) (hU : Umᵀ * Um = 1) (hS : Smᵀ * Sm = 1) :
    (Rc * Um * Sm)ᵀ * (Rc * Um * Sm) = 1 :=
  orthogonal_mul (orthogonal_mul hR hU) hS

/-- If the fields at two orientations relate by `F d' = F d · (Rc d d' · Um d d' · Sm d d')` with the
three factors orthogonal at every pair, then the Gram spectral read `fread ∘ charpoly ∘ (Fᵀ F)`
satisfies `A2`. It composes `resampling_orthogonal`, `continuumRotationCongruence_of_gram` and
`A2_continuum_of_congruence`. The orthogonality of `Rc`, `Um` and `Sm`, and the relation `hrot`
between the fields, are the hypotheses; nothing here establishes them.

DERIVED: the `1`s are the identity matrix, the value of `Mᵀ * M` that makes each of the three factors
orthogonal. -/
theorem A2_continuum_of_sampling {D m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (fread : Polynomial ℝ → ℝ) (F : D → Matrix m n ℝ) (Rc Um Sm : D → D → Matrix n n ℝ)
    (hR : ∀ d d', (Rc d d')ᵀ * (Rc d d') = 1)
    (hU : ∀ d d', (Um d d')ᵀ * (Um d d') = 1)
    (hS : ∀ d d', (Sm d d')ᵀ * (Sm d d') = 1)
    (hrot : ∀ d d', F d' = F d * (Rc d d' * Um d d' * Sm d d')) :
    A2 (fun d => fread ((F d)ᵀ * F d).charpoly) :=
  A2_continuum_of_congruence fread (fun d => (F d)ᵀ * F d)
    (continuumRotationCongruence_of_gram F (fun d d' => Rc d d' * Um d d' * Sm d d')
      (fun d d' => resampling_orthogonal (hR d d') (hU d d') (hS d d')) hrot)

/-- If `Q` preserves the Euclidean dot product of every pair of vectors, `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`,
then `Qᵀ Q = 1`. The entries are recovered by testing on the standard basis vectors. This is the form
in which a map that preserves the sample inner product can be fed to `resampling_orthogonal` and
`A2_continuum_of_sampling`.

DERIVED: the `1` is the identity matrix, the conclusion's value for `Qᵀ * Q`. -/
theorem orthogonal_of_preserves_dotProduct {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℝ}
    (h : ∀ x y : n → ℝ, (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y) :
    Qᵀ * Q = 1 := by
  have h2 : ∀ x y : n → ℝ, ((Qᵀ * Q) *ᵥ x) ⬝ᵥ y = x ⬝ᵥ y := fun x y => by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, h]
  ext i j
  have hk := h2 (Pi.single j 1) (Pi.single i 1)
  simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, eq_comm] using hk

end MassGap
