import Mathlib
import MassGap.HolonomyLadder
import MassGap.SUN

/-!
# MassGap.ChargedWordTrace — nearly commuting unitaries have a charged word of large trace

For `N × N` unitaries `X`, `Y` and `q = (b', a', a, b) ∈ (Fin N)⁴` the word is
`w_q(X, Y) = Y^{b'} X^{a'} (X*)^a (Y*)^b`. Multiplying `X` by `z₁` and `Y` by `z₂`, both of modulus one,
multiplies `w_q` by `z₁^{a' − a} z₂^{b' − b}`. With `z₁, z₂` in `Z_N` this is the trivial character
exactly when `a' = a` and `b' = b` (`0 ≤ a, a', b, b' < N`). The word is **charged** otherwise.

* `exists_common_eigenvector`: commuting matrices have a common eigenvector.
* `norm_eigenvalue_eq_one`: an eigenvalue of a unitary has modulus one.
* `fejer_norm_ge`: for a common eigenvector `X v = λ v`, `Y v = μ v`, the matrix
  `M = (Σ_{a<N} (λ X*)^a)(Σ_{b<N} (μ Y*)^b)` sends `v` to `N² v`, so `‖M‖ ≥ N²` in the Frobenius norm.
* `conjTranspose_mul_self_eq`: `M* M = Σ_q c_q w_q(X, Y)` with `|c_q| = 1`. So
  `N⁴ ≤ Re tr(M* M) ≤ Σ_q |tr w_q|`.
* **`exists_charged_of_commute`**: for commuting unitaries and `N ≥ 2`, some charged word has
  `|tr w_q| > 1/2`. The `N²` uncharged words are `1`, with trace `N`, and contribute `N³`. If every
  one of the at least `N⁴ − N²` charged words had trace at most `1/2`, the sum would be at most
  `N⁴/2 + (N − 1/2) N² < N⁴`.
* **`exists_commutator_floor`**: for `N ≥ 2` there is `δ > 0` such that any `X, Y ∈ SU(N)` whose
  charged words all have `|tr w_q| ≤ 1/2` satisfy `‖XY − YX‖ ≥ δ`. The set of such pairs is closed
  in the compact `SU(N)²`; the entrywise size of the commutator is continuous and, by the previous
  item, positive on it, so it has a positive minimum there.

The full centre `Z_N` is needed, not `−1` alone. For `SU(4)` with `−1` alone the
flat commuting pair `diag(1,−1,1,−1)`, `diag(1,1,−1,−1)` has every odd word traceless; with the full
`Z_N × Z_N` the words with charge `(a' − a, b' − b) ≠ 0` include those that see it.

DERIVED (module-wide): `1/2` is the trace window; `N²` is `F_N(1)²`, the value of the squared
Fejér-type sum at a common eigenvector; `N⁴ = (N²)²`; `N` is `tr 1`.
-/

open scoped Matrix ComplexConjugate ComplexOrder

namespace MassGap.ChargedWordTrace

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

open MassGap.FrobeniusUnitary MassGap.HolonomyLadder

variable {N : ℕ}

/-- The index of a word: `(b', a', a, b)`. -/
abbrev Idx (N : ℕ) : Type := Fin N × Fin N × Fin N × Fin N

/-- **The word** `Y^{b'} X^{a'} (X*)^a (Y*)^b`. -/
def word (X Y : Matrix (Fin N) (Fin N) ℂ) (q : Idx N) : Matrix (Fin N) (Fin N) ℂ :=
  Y ^ (q.1 : ℕ) * X ^ (q.2.1 : ℕ) * star X ^ (q.2.2.1 : ℕ) * star Y ^ (q.2.2.2 : ℕ)

/-- **A charged word**: `a' ≠ a` or `b' ≠ b`. -/
def Charged (q : Idx N) : Prop := q.2.1 ≠ q.2.2.1 ∨ q.1 ≠ q.2.2.2

theorem pow_mul_star_pow {X : Matrix (Fin N) (Fin N) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∀ k : ℕ, X ^ k * star X ^ k = 1
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ', Matrix.mul_assoc, ← Matrix.mul_assoc X, mul_star_self hX,
      Matrix.one_mul, pow_mul_star_pow hX k]

/-- An uncharged word is `1`. -/
theorem word_of_not_charged {X Y : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ) {q : Idx N}
    (hq : ¬ Charged q) : word X Y q = 1 := by
  unfold Charged at hq
  push_neg at hq
  obtain ⟨h1, h2⟩ := hq
  unfold word
  rw [h1, h2, Matrix.mul_assoc (Y ^ _) (X ^ _), pow_mul_star_pow hX, Matrix.mul_one,
    pow_mul_star_pow hY]

/-! ## A common eigenvector -/

/-- **Commuting matrices have a common eigenvector.** -/
theorem exists_common_eigenvector (hN : 0 < N) {X Y : Matrix (Fin N) (Fin N) ℂ}
    (hXY : X * Y = Y * X) :
    ∃ v : Fin N → ℂ, v ≠ 0 ∧ ∃ l m : ℂ, X *ᵥ v = l • v ∧ Y *ᵥ v = m • v := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' X)
  set E := Module.End.eigenspace (Matrix.toLin' X) l with hE
  have hmaps : ∀ w ∈ E, Matrix.toLin' Y w ∈ E := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    simp only [Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.mulVec_mulVec, hXY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hl
  obtain ⟨m, hm⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' Y).restrict hmaps)
  obtain ⟨w, hw⟩ := hm.exists_hasEigenvector
  have hw' := Module.End.hasEigenvector_iff.mp hw
  have hw1 := hw.apply_eq_smul
  refine ⟨(w : Fin N → ℂ), fun h => hw'.2 ((Submodule.coe_eq_zero).mp h), l, m, ?_, ?_⟩
  · have := w.2
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
    exact this
  · have h1 : (((Matrix.toLin' Y).restrict hmaps w : E) : Fin N → ℂ) = ((m • w : E) : Fin N → ℂ) := by
      rw [hw1]
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using h1

/-- **An eigenvalue of a unitary has modulus one.** -/
theorem norm_eigenvalue_eq_one {X : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) {v : Fin N → ℂ} (hv : v ≠ 0) {l : ℂ}
    (h : X *ᵥ v = l • v) : ‖l‖ = 1 := by
  have hXX : Xᴴ * X = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact star_mul_self hX
  have hs : star v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_star_self_eq_zero.mp h0)
  have e1 : star (X *ᵥ v) ⬝ᵥ (X *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hXX,
      Matrix.one_mulVec]
  rw [h, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc] at e1
  have e2 : (star l * l - 1) * (star v ⬝ᵥ v) = 0 := by rw [sub_mul, e1, one_mul, sub_self]
  have e3 : star l * l = 1 := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hs)
  have e4 : l * conj l = 1 := by rw [mul_comm]; exact e3
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at e4
  have e5 : ‖l‖ ^ 2 = 1 := by exact_mod_cast e4
  have := norm_nonneg l
  nlinarith [sq_nonneg (‖l‖ - 1), sq_nonneg (‖l‖ + 1)]

/-! ## The Fejér-type matrix at a common eigenvector -/

/-- `Σ_{a<N} (c A)^a`. -/
noncomputable def fsum (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ a : Fin N, (c • A) ^ (a : ℕ)

theorem fsum_mulVec {c : ℂ} {A : Matrix (Fin N) (Fin N) ℂ} {v : Fin N → ℂ}
    (h : (c • A) *ᵥ v = v) : fsum c A *ᵥ v = (N : ℂ) • v := by
  have hp : ∀ k : ℕ, (c • A) ^ k *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]
  unfold fsum
  rw [Matrix.sum_mulVec]
  simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]

/-- `(λ X*) v = v` when `X v = λ v` and `X` is unitary. -/
theorem smul_star_mulVec {X : Matrix (Fin N) (Fin N) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {v : Fin N → ℂ} {l : ℂ} (h : X *ᵥ v = l • v) : (l • star X) *ᵥ v = v := by
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, ← h, Matrix.mulVec_mulVec, star_mul_self hX,
    Matrix.one_mulVec]

theorem norm_replicateCol (w : Fin N → ℂ) :
    ‖Matrix.replicateCol (Fin 1) w‖ = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin N))‖ :=
  Matrix.frobenius_norm_replicateCol w

/-- **At a common eigenvector the Fejér-type matrix has norm at least `N²`.** -/
theorem fejer_norm_ge {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ) {v : Fin N → ℂ} (hv : v ≠ 0) {l m : ℂ}
    (hl : X *ᵥ v = l • v) (hm : Y *ᵥ v = m • v) :
    (N : ℝ) ^ 2 ≤ ‖fsum l (star X) * fsum m (star Y)‖ := by
  have hMv : (fsum l (star X) * fsum m (star Y)) *ᵥ v = ((N : ℂ) ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, fsum_mulVec (smul_star_mulVec hY hm), Matrix.mulVec_smul,
      fsum_mulVec (smul_star_mulVec hX hl), smul_smul, sq]
  have hMC : (fsum l (star X) * fsum m (star Y)) * Matrix.replicateCol (Fin 1) v
      = Matrix.replicateCol (Fin 1) (((N : ℂ) ^ 2) • v) := by
    rw [← hMv, Matrix.replicateCol_mulVec]
  have hn := Matrix.frobenius_norm_mul (fsum l (star X) * fsum m (star Y))
    (Matrix.replicateCol (Fin 1) v)
  rw [hMC, norm_replicateCol, norm_replicateCol, WithLp.toLp_smul, norm_smul, norm_pow, Complex.norm_natCast] at hn
  have hpos : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hv
    have := congrArg (WithLp.ofLp (p := 2)) h0
    simpa using this
  exact le_of_mul_le_mul_right hn hpos

/-- **The expansion of `M* M` into words.** -/
theorem conjTranspose_mul_self_eq (X Y : Matrix (Fin N) (Fin N) ℂ) (l m : ℂ) :
    (fsum l (star X) * fsum m (star Y))ᴴ * (fsum l (star X) * fsum m (star Y))
      = ∑ q : Idx N, (conj m ^ (q.1 : ℕ) * conj l ^ (q.2.1 : ℕ) * l ^ (q.2.2.1 : ℕ)
          * m ^ (q.2.2.2 : ℕ)) • word X Y q := by
  rw [← Matrix.star_eq_conjTranspose, star_mul]
  unfold fsum
  simp only [star_sum, star_pow, star_smul, star_star]
  simp only [Matrix.mul_assoc]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold word
  simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
  congr 1
  simp only [starRingEnd_apply]
  ring

/-- **The words' traces dominate `N⁴`** at a common eigenvector. -/
theorem sum_norm_trace_ge {X Y : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {v : Fin N → ℂ} (hv : v ≠ 0) {l m : ℂ} (hl : X *ᵥ v = l • v) (hm : Y *ᵥ v = m • v) :
    (N : ℝ) ^ 4 ≤ ∑ q : Idx N, ‖Matrix.trace (word X Y q)‖ := by
  have hl1 := norm_eigenvalue_eq_one hX hv hl
  have hm1 := norm_eigenvalue_eq_one hY hv hm
  have h1 := fejer_norm_ge hX hY hv hl hm
  have h2 : (N : ℝ) ^ 4 ≤ ‖fsum l (star X) * fsum m (star Y)‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    calc (N : ℝ) ^ 4 = ((N : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ _ := this
  rw [frob_sq, conjTranspose_mul_self_eq, Matrix.trace_sum] at h2
  refine h2.trans ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun q _ => ?_)))
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul]
  have hc : ‖conj m ^ (q.1 : ℕ) * conj l ^ (q.2.1 : ℕ) * l ^ (q.2.2.1 : ℕ) * m ^ (q.2.2.2 : ℕ)‖
      = 1 := by
    simp only [norm_mul, norm_pow, Complex.norm_conj, hl1, hm1, one_pow, mul_one]
  rw [hc, one_mul]

/-- **Commuting unitaries have a charged word of trace above `1/2`**, for `N ≥ 2`. -/
theorem exists_charged_of_commute (hN : 2 ≤ N) {X Y : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hXY : X * Y = Y * X) : ∃ q : Idx N, Charged q ∧ 1 / 2 < ‖Matrix.trace (word X Y q)‖ := by
  classical
  obtain ⟨v, hv, l, m, hl, hm⟩ := exists_common_eigenvector (by omega) hXY
  have hsum := sum_norm_trace_ge hX hY hv hl hm
  by_contra hcon
  push_neg at hcon
  set S := (Finset.univ : Finset (Idx N)).filter Charged
  set D := (Finset.univ : Finset (Idx N)).filter (fun q => ¬ Charged q)
  have hsplit : ∑ q ∈ S, ‖Matrix.trace (word X Y q)‖ + ∑ q ∈ D, ‖Matrix.trace (word X Y q)‖
      = ∑ q : Idx N, ‖Matrix.trace (word X Y q)‖ :=
    Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Idx N)) Charged
      (fun q => ‖Matrix.trace (word X Y q)‖)
  have hS : ∑ q ∈ S, ‖Matrix.trace (word X Y q)‖ ≤ S.card * (1 / 2) := by
    have := Finset.sum_le_sum (s := S) (fun q hq => hcon q (Finset.mem_filter.mp hq).2)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hD : ∑ q ∈ D, ‖Matrix.trace (word X Y q)‖ = ∑ _q ∈ D, (N : ℝ) :=
    Finset.sum_congr rfl fun q hq => by
      rw [word_of_not_charged hX hY (Finset.mem_filter.mp hq).2, Matrix.trace_one,
        Fintype.card_fin, Complex.norm_natCast]
  rw [Finset.sum_const, nsmul_eq_mul] at hD
  have hcard : S.card + D.card = N ^ 4 := by
    have h : S.card + D.card = (Finset.univ : Finset (Idx N)).card :=
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Idx N))) Charged
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin] at h
    rw [h]; ring
  have hDle : D.card ≤ N ^ 2 := by
    have hsub : D ⊆ (Finset.univ : Finset (Fin N × Fin N)).image
        (fun p => ((p.1, p.2, p.2, p.1) : Idx N)) := by
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      unfold Charged at hq'
      push_neg at hq'
      refine Finset.mem_image.mpr ⟨(q.1, q.2.1), Finset.mem_univ _, ?_⟩
      obtain ⟨b', a', a, b⟩ := q
      simp only at hq' ⊢
      rw [hq'.1, hq'.2]
    calc D.card ≤ ((Finset.univ : Finset (Fin N × Fin N)).image
          (fun p => ((p.1, p.2, p.2, p.1) : Idx N))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_image_le
      _ = N ^ 2 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
          ring
  have hcardR : (S.card : ℝ) + D.card = (N : ℝ) ^ 4 := by exact_mod_cast hcard
  have hDleR : (D.card : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hDle
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have e1 : (N : ℝ) ^ 4 ≤ S.card * (1 / 2) + D.card * N := by
    rw [← hsplit] at hsum
    linarith
  have key : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 2 * (2 * N - 1) := by
    have e2 : (S.card : ℝ) = N ^ 4 - D.card := by linarith
    rw [e2] at e1
    nlinarith [mul_le_mul_of_nonneg_left hDleR (by linarith : (0 : ℝ) ≤ 2 * N - 1)]
  have h1 : (1 : ℝ) ≤ ((N : ℝ) - 1) ^ 2 := by nlinarith
  have h2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul h2 h1 (by norm_num) (by positivity)]

/-! ## Nearly commuting pairs -/

theorem continuous_word (q : Idx N) :
    Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
      word ((p.1 : Matrix (Fin N) (Fin N) ℂ)) ((p.2 : Matrix (Fin N) (Fin N) ℂ)) q := by
  have h1 : Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
      ((p.1 : Matrix (Fin N) (Fin N) ℂ)) := continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
      ((p.2 : Matrix (Fin N) (Fin N) ℂ)) := continuous_subtype_val.comp continuous_snd
  unfold word
  exact (((h2.pow _).mul (h1.pow _)).mul (h1.matrix_conjTranspose.pow _)).mul
    (h2.matrix_conjTranspose.pow _)

/-- The entrywise size of the commutator. -/
noncomputable def commSize (X Y : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖(X * Y - Y * X) i j‖

theorem commSize_le (X Y : Matrix (Fin N) (Fin N) ℂ) :
    commSize X Y ≤ (N : ℝ) ^ 2 * ‖X * Y - Y * X‖ := by
  unfold commSize
  calc ∑ i, ∑ j, ‖(X * Y - Y * X) i j‖ ≤ ∑ _i : Fin N, ∑ _j : Fin N, ‖X * Y - Y * X‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_entry_le _ i j
    _ = (N : ℝ) ^ 2 * ‖X * Y - Y * X‖ := by simp [Finset.sum_const]; ring

/-- **A pair of `SU(N)` matrices whose charged words all have small trace is a definite distance
from commuting**, for `N ≥ 2`. -/
theorem exists_commutator_floor (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : MassGap.SUN.SU N,
      (∀ q : Idx N, Charged q →
        ‖Matrix.trace (word (X : Matrix (Fin N) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ) q)‖
          ≤ 1 / 2) →
      δ ≤ ‖(X : Matrix (Fin N) (Fin N) ℂ) * Y - Y * X‖ := by
  classical
  set K : Set (MassGap.SUN.SU N × MassGap.SUN.SU N) := {p | ∀ q : Idx N, Charged q →
    ‖Matrix.trace (word (p.1 : Matrix (Fin N) (Fin N) ℂ) (p.2 : Matrix (Fin N) (Fin N) ℂ) q)‖
      ≤ 1 / 2} with hKdef
  have hKc : IsClosed K := by
    simp only [hKdef, Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_le (continuous_norm.comp (continuous_word q).matrix_trace) continuous_const
  have hNR : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun X Y h => ?_⟩
    have : (X, Y) ∈ K := h
    rw [hK] at this
    exact absurd this (Set.notMem_empty _)
  · set f : MassGap.SUN.SU N × MassGap.SUN.SU N → ℝ := fun p =>
      commSize (p.1 : Matrix (Fin N) (Fin N) ℂ) (p.2 : Matrix (Fin N) (Fin N) ℂ) with hfdef
    have hfc : Continuous f := by
      have h1 : Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
          ((p.1 : Matrix (Fin N) (Fin N) ℂ)) := continuous_subtype_val.comp continuous_fst
      have h2 : Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
          ((p.2 : Matrix (Fin N) (Fin N) ℂ)) := continuous_subtype_val.comp continuous_snd
      have hc : Continuous fun p : MassGap.SUN.SU N × MassGap.SUN.SU N =>
          ((p.1 : Matrix (Fin N) (Fin N) ℂ)) * (p.2 : Matrix (Fin N) (Fin N) ℂ)
            - (p.2 : Matrix (Fin N) (Fin N) ℂ) * (p.1 : Matrix (Fin N) (Fin N) ℂ) :=
        (h1.mul h2).sub (h2.mul h1)
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_norm.comp (hc.matrix_elem i j)
    obtain ⟨p₀, hp₀, hmin⟩ := hKc.isCompact.exists_isMinOn hK hfc.continuousOn
    have hpos : 0 < f p₀ := by
      rcases (show 0 ≤ f p₀ from Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        norm_nonneg _).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ i j, ((p₀.1 : Matrix (Fin N) (Fin N) ℂ) * p₀.2 - p₀.2 * p₀.1) i j = 0 := by
          intro i j
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
            norm_nonneg _)).mp h.symm i (Finset.mem_univ _)
          have h00 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg _)).mp h0 j
            (Finset.mem_univ _)
          exact norm_eq_zero.mp h00
        have hcomm : (p₀.1 : Matrix (Fin N) (Fin N) ℂ) * p₀.2 = p₀.2 * p₀.1 := by
          have : (p₀.1 : Matrix (Fin N) (Fin N) ℂ) * p₀.2 - p₀.2 * p₀.1 = 0 := by
            ext i j; exact hz i j
          exact sub_eq_zero.mp this
        obtain ⟨q, hq, hlt⟩ := exists_charged_of_commute hN
          (Matrix.mem_specialUnitaryGroup_iff.mp p₀.1.2).1
          (Matrix.mem_specialUnitaryGroup_iff.mp p₀.2.2).1 hcomm
        exact absurd (hp₀ q hq) (not_le.mpr hlt)
    refine ⟨f p₀ / (N : ℝ) ^ 2, div_pos hpos hNR, fun X Y h => ?_⟩
    have hmem : (X, Y) ∈ K := h
    have h1 : f p₀ ≤ f (X, Y) := hmin hmem
    have h2 := commSize_le (X : Matrix (Fin N) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ)
    rw [div_le_iff₀ hNR]
    simp only [hfdef] at h1
    linarith

end MassGap.ChargedWordTrace

#print axioms MassGap.ChargedWordTrace.exists_common_eigenvector
#print axioms MassGap.ChargedWordTrace.norm_eigenvalue_eq_one
#print axioms MassGap.ChargedWordTrace.fejer_norm_ge
#print axioms MassGap.ChargedWordTrace.conjTranspose_mul_self_eq
#print axioms MassGap.ChargedWordTrace.exists_charged_of_commute
#print axioms MassGap.ChargedWordTrace.exists_commutator_floor
