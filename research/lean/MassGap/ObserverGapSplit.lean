import Mathlib
import MassGap.ContinuumSep
import MassGap.OneCubeShims

/-!
# MassGap.ObserverGapSplit — what a coarse view's gap says about the finer observer, and what it cannot

Three statements on a transfer `Transfer.TransferData A` (a reflection-positive form, a symmetric
contraction `T`, a normalised vacuum), the setting of the observer's reconstruction.

1. **One finite time is enough** (`gapAt_of_iterate`): if `T^k` contracts the vacuum's complement by
   `ρ ≤ 1` (in the form), then `T` is `GapAt ρ^{1/k}`. With `ObserverGapScale.flowClusterAbs_iff_gapAt`, M
   for the observer is the statement that at one finite physical time every vacuum-orthogonal state
   has lost a fixed fraction of its norm.
2. **The gap splits exactly across an invariant coarse span** (`gapAt_of_split`,
   `gapAt_iff_split`): for a submodule `C` containing the vacuum, mapped into itself by `T`, along
   which every vector splits as `c + d` with `d` orthogonal to `C`, `GapAt D ρ` holds if and only if
   `T` contracts `C ∩ Ω^⊥` by `ρ` (the coarse gap) and contracts `C^⊥` by `ρ` (the residual gap). Two
   rates combine at their maximum. The residual needs a gap of its own, at any rate below one; it need
   not decay as fast as the coarse span.
3. **The coarse gap does not give the residual gap** (`coarse_gap_does_not_lift`): a three-dimensional
   transfer, positive, with an invariant coarse span along which every vector splits, the coarse
   span gapped at `1/2`, and no gap at any rate below one. Symmetry, positivity, contraction,
   invariance and the split are all present; the residual carries a second invariant state. So
   visibility (the residual gap) is an input of its own: it cannot come from the operator structure
   the observer's reconstruction has.
-/

namespace MassGap.ObserverGapSplit

open MassGap

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. One finite time is enough -/

/-- The vacuum's complement is invariant under every power of `T`.

DERIVED: `0` is the value of the form against the vacuum. -/
theorem form_pow_orth (D : Transfer.TransferData A) (j : ℕ) {x : A} (hx : D.form x D.vac = 0) :
    D.form ((D.T ^ j) x) D.vac = 0 := by
  rw [TransferGap.form_pow_symm D j x D.vac, TransferGap.pow_vac D j]
  exact hx

#print axioms form_pow_orth

/-- Every power of `T` contracts the form on the vacuum's complement.

DERIVED: `0` is the value of the form against the vacuum; `1` the contraction rate. -/
theorem form_pow_contract (D : Transfer.TransferData A) (s : ℕ) {y : A}
    (hy : D.form y D.vac = 0) : D.form ((D.T ^ s) y) ((D.T ^ s) y) ≤ D.form y y := by
  have h := TransferGap.gap_pow D zero_le_one (TransferGap.gapAt_of_one_le_sq D (by norm_num)) s y hy
  simpa using h

#print axioms form_pow_contract

/-- The contraction of `T^k` iterates: `T^{kq}` contracts by `ρ^{2q}`.

DERIVED: `2` is the form's degree; `0` the value against the vacuum and the base of the induction. -/
theorem form_iterate_block (D : Transfer.TransferData A) {k : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ x, D.form x D.vac = 0 → D.form ((D.T ^ k) x) ((D.T ^ k) x) ≤ ρ ^ 2 * D.form x x) :
    ∀ (q : ℕ) (x : A), D.form x D.vac = 0 →
      D.form ((D.T ^ (k * q)) x) ((D.T ^ (k * q)) x) ≤ ρ ^ (2 * q) * D.form x x := by
  intro q
  induction q with
  | zero => intro x _; simp
  | succ q ih =>
    intro x hx
    have he : (D.T ^ (k * (q + 1))) x = (D.T ^ (k * q)) ((D.T ^ k) x) := by
      rw [Nat.mul_succ, pow_add, Module.End.mul_apply]
    rw [he]
    calc D.form ((D.T ^ (k * q)) ((D.T ^ k) x)) ((D.T ^ (k * q)) ((D.T ^ k) x))
        ≤ ρ ^ (2 * q) * D.form ((D.T ^ k) x) ((D.T ^ k) x) := ih _ (form_pow_orth D k hx)
      _ ≤ ρ ^ (2 * q) * (ρ ^ 2 * D.form x x) :=
          mul_le_mul_of_nonneg_left (h x hx) (pow_nonneg hρ _)
      _ = ρ ^ (2 * (q + 1)) * D.form x x := by ring

#print axioms form_iterate_block

/-- **A contraction at one finite time is a gap.** If `T^k` (`k ≥ 1`) contracts the vacuum's
complement by `ρ` with `0 < ρ ≤ 1`, then `GapAt D (ρ^{1/k})`: a time `n = kq + s` costs at most one
extra block, absorbed in the constant `‖x‖²/ρ²` of `ContinuumSep.gapAt_of_per_vector_form_decay`.

DERIVED: `0` and `1` bracket the rate and `0` is the vacuum value and the lower end of `k`; `2` is the
form's degree and the doubled separation. -/
theorem gapAt_of_iterate (D : Transfer.TransferData A) {k : ℕ} (hk : 0 < k) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : ∀ x, D.form x D.vac = 0 → D.form ((D.T ^ k) x) ((D.T ^ k) x) ≤ ρ ^ 2 * D.form x x) :
    TransferGap.GapAt D (ρ ^ (1 / (k : ℝ))) := by
  refine ContinuumSep.gapAt_of_per_vector_form_decay D (Real.rpow_nonneg hρ0.le _)
    (fun x hx => ⟨D.form x x / ρ ^ 2, fun n => ?_⟩)
  rw [← TransferGap.form_pow_diag]
  obtain ⟨q, s, hn, hs⟩ : ∃ q s : ℕ, n = k * q + s ∧ s < k :=
    ⟨n / k, n % k, (Nat.div_add_mod n k).symm, Nat.mod_lt n hk⟩
  have hsplit : (D.T ^ n) x = (D.T ^ s) ((D.T ^ (k * q)) x) := by
    rw [hn, add_comm, pow_add, Module.End.mul_apply]
  rw [hsplit]
  have hxx : 0 ≤ D.form x x := D.form_nonneg x
  have h1 := form_pow_contract D s (form_pow_orth D (k * q) hx)
  have h2 := form_iterate_block D hρ0.le h q x hx
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hrp : (ρ ^ (1 / (k : ℝ))) ^ (2 * n) = ρ ^ (1 / (k : ℝ) * ((2 * n : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
  have hcmp : ρ ^ (2 * (q + 1)) ≤ (ρ ^ (1 / (k : ℝ))) ^ (2 * n) := by
    rw [hrp, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hnk : (n : ℝ) ≤ k * q + k := by
      have : n ≤ k * q + k := by omega
      exact_mod_cast this
    rw [one_div, inv_mul_le_iff₀ hkR]
    push_cast
    nlinarith
  have heq : ρ ^ (2 * q) * D.form x x = D.form x x / ρ ^ 2 * ρ ^ (2 * (q + 1)) := by
    have hp : ρ ^ (2 * (q + 1)) = ρ ^ (2 * q) * ρ ^ 2 := by ring
    rw [hp, div_mul_eq_mul_div, eq_div_iff hρ2.ne']
    ring
  calc D.form ((D.T ^ s) ((D.T ^ (k * q)) x)) ((D.T ^ s) ((D.T ^ (k * q)) x))
      ≤ D.form ((D.T ^ (k * q)) x) ((D.T ^ (k * q)) x) := h1
    _ ≤ ρ ^ (2 * q) * D.form x x := h2
    _ = D.form x x / ρ ^ 2 * ρ ^ (2 * (q + 1)) := heq
    _ ≤ D.form x x / ρ ^ 2 * (ρ ^ (1 / (k : ℝ))) ^ (2 * n) :=
        mul_le_mul_of_nonneg_left hcmp (div_nonneg hxx hρ2.le)

#print axioms gapAt_of_iterate

/-! ## 2. The gap splits exactly across an invariant coarse span -/

/-- **The gap of the finer observer from the coarse gap and the residual gap.** `C` contains the
vacuum and is mapped into itself by `T`; every vector is `c + d` with `c ∈ C` and `d` orthogonal to
`C`. If `T` contracts `C ∩ Ω^⊥` by `ρc` and the complement of `C` by `ρr`, with both squares at most
`ρ²`, then `GapAt D ρ`. The cross terms vanish: `⟨c, d⟩ = 0`, and `⟨T c, T d⟩ = ⟨T² c, d⟩ = 0` since
`T² c ∈ C`.

DERIVED: `0` is orthogonality; `2` is the form's degree. -/
theorem gapAt_of_split (D : Transfer.TransferData A) (C : Submodule ℝ A) (hvac : D.vac ∈ C)
    (hTC : ∀ z ∈ C, D.T z ∈ C)
    (hsplit : ∀ x : A, ∃ c ∈ C, ∃ d : A, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
    {ρ ρc ρr : ℝ}
    (hcoarse : ∀ c ∈ C, D.form c D.vac = 0 → D.form (D.T c) (D.T c) ≤ ρc ^ 2 * D.form c c)
    (hres : ∀ d : A, (∀ z ∈ C, D.form z d = 0) → D.form (D.T d) (D.T d) ≤ ρr ^ 2 * D.form d d)
    (hc : ρc ^ 2 ≤ ρ ^ 2) (hr : ρr ^ 2 ≤ ρ ^ 2) : TransferGap.GapAt D ρ := by
  intro x hx
  obtain ⟨c, hcC, d, hd, rfl⟩ := hsplit x
  have hdv : D.form d D.vac = 0 := by rw [D.form_symm]; exact hd _ hvac
  have hcv : D.form c D.vac = 0 := by
    have := hx
    rw [D.form_add_left, hdv, add_zero] at this
    exact this
  have hcd : D.form c d = 0 := hd c hcC
  have hTcd : D.form (D.T c) (D.T d) = 0 := by
    rw [← D.T_symm]; exact hd _ (hTC _ (hTC c hcC))
  have hxx : D.form (c + d) (c + d) = D.form c c + D.form d d := by
    rw [D.form_add_left, D.toPreForm.form_add_right, D.toPreForm.form_add_right, hcd,
      D.form_symm d c, hcd]
    ring
  have hTxx : D.form (D.T (c + d)) (D.T (c + d)) = D.form (D.T c) (D.T c) + D.form (D.T d) (D.T d) := by
    rw [map_add, D.form_add_left, D.toPreForm.form_add_right, D.toPreForm.form_add_right, hTcd,
      D.form_symm (D.T d) (D.T c), hTcd]
    ring
  rw [hTxx, hxx]
  have h1 := hcoarse c hcC hcv
  have h2 := hres d hd
  have hcc : 0 ≤ D.form c c := D.form_nonneg c
  have hdd : 0 ≤ D.form d d := D.form_nonneg d
  nlinarith [mul_le_mul_of_nonneg_right hc hcc, mul_le_mul_of_nonneg_right hr hdd]

#print axioms gapAt_of_split

/-- **The split is exact**: under the hypotheses of `gapAt_of_split`, `GapAt D ρ` holds if and only if
`T` contracts both the coarse vacuum complement and the residual by `ρ`. The residual is orthogonal
to the vacuum because the vacuum lies in `C`.

DERIVED: `0` is orthogonality; `2` is the form's degree. -/
theorem gapAt_iff_split (D : Transfer.TransferData A) (C : Submodule ℝ A) (hvac : D.vac ∈ C)
    (hTC : ∀ z ∈ C, D.T z ∈ C)
    (hsplit : ∀ x : A, ∃ c ∈ C, ∃ d : A, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d) (ρ : ℝ) :
    TransferGap.GapAt D ρ ↔
      (∀ c ∈ C, D.form c D.vac = 0 → D.form (D.T c) (D.T c) ≤ ρ ^ 2 * D.form c c)
        ∧ (∀ d : A, (∀ z ∈ C, D.form z d = 0) → D.form (D.T d) (D.T d) ≤ ρ ^ 2 * D.form d d) := by
  constructor
  · intro hg
    refine ⟨fun c _ hcv => hg c hcv, fun d hd => hg d ?_⟩
    rw [D.form_symm]
    exact hd _ hvac
  · rintro ⟨h1, h2⟩
    exact gapAt_of_split D C hvac hTC hsplit h1 h2 le_rfl le_rfl

#print axioms gapAt_iff_split

/-! ## 3. The coarse gap does not give the residual gap -/

/-- A diagonal step on `ℝ³`: coordinate `0` fixed (the vacuum), coordinate `1` scaled by `μ` (the
coarse excitation), coordinate `2` scaled by `lam` (the residual).

DERIVED: `3` is the least dimension holding a vacuum, a coarse excitation and a residual; `0`, `1`,
`2` index them. -/
def triStep (μ lam : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := fun i => if i = 0 then x 0 else if i = 1 then μ * x 1 else lam * x 2
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The three-dimensional transfer: the standard inner product, the vacuum at coordinate `0`, the
step `triStep μ lam`.

DERIVED: `3`, `0`, `1`, `2` as in `triStep`; `2` in the squares is the form's degree; `1` is the
contraction bound and the vacuum's norm. -/
noncomputable def triTransfer (μ lam : ℝ) (hμ : μ ^ 2 ≤ 1) (hl : lam ^ 2 ≤ 1) :
    Transfer.TransferData (Fin 3 → ℝ) where
  form x y := x 0 * y 0 + x 1 * y 1 + x 2 * y 2
  form_symm x y := by ring
  form_add_left x y z := by simp only [Pi.add_apply]; ring
  form_smul_left r x y := by simp only [Pi.smul_apply, smul_eq_mul]; ring
  form_nonneg x := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  T := triStep μ lam
  vac := fun i => if i = 0 then 1 else 0
  T_symm x y := by simp [triStep]; ring
  T_contract x := by
    simp [triStep]
    nlinarith [mul_le_mul_of_nonneg_right hμ (sq_nonneg (x 1)),
      mul_le_mul_of_nonneg_right hl (sq_nonneg (x 2))]
  T_vac := by
    funext i
    fin_cases i <;> simp [triStep]
  vac_norm := by simp

/-- The coarse span: the vectors with no residual component.

DERIVED: `2` is the residual coordinate; `0` its value; `3` the dimension, as in `triStep`. -/
def triCoarse : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {x | x 2 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [hx, mul_zero]

/-- **A positive transfer whose coarse span is gapped at `1/2` has no gap at any rate below one.** For
`triTransfer (1/2) 1`: the transfer is positive (`⟨x, T x⟩ ≥ 0`), the coarse span `triCoarse` holds
the vacuum and is mapped into itself, every vector splits as coarse plus orthogonal residual, `T`
contracts the coarse vacuum complement by `1/2`, and yet `GapAt D ρ` fails at every `ρ` with
`ρ² < 1`: the residual coordinate is a second invariant state. By `gapAt_iff_split` the failure is
the residual's. No property of the operator alone supplies visibility.

DERIVED: `3` the dimension; `1/2` the coarse rate and `1` the residual's (any `1/2 < lam ≤ 1`
separates the two gaps, `1` removes the fine one); `0`, `1`, `2` index the coordinates; `2` in the
squares is the form's degree. -/
theorem coarse_gap_does_not_lift :
    ∃ (D : Transfer.TransferData (Fin 3 → ℝ)) (C : Submodule ℝ (Fin 3 → ℝ)),
      GNSHilbert.PositiveTransfer D ∧ D.vac ∈ C ∧ (∀ z ∈ C, D.T z ∈ C)
        ∧ (∀ x, ∃ c ∈ C, ∃ d, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
        ∧ (∀ c ∈ C, D.form c D.vac = 0 → D.form (D.T c) (D.T c) ≤ (1 / 2) ^ 2 * D.form c c)
        ∧ ∀ ρ : ℝ, ρ ^ 2 < 1 → ¬ TransferGap.GapAt D ρ := by
  refine ⟨triTransfer (1 / 2) 1 (by norm_num) (by norm_num), triCoarse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show 0 ≤ x 0 * triStep (1 / 2) 1 x 0 + x 1 * triStep (1 / 2) 1 x 1
      + x 2 * triStep (1 / 2) 1 x 2
    simp [triStep]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  · show (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    simp
  · intro z hz
    have hz2 : z 2 = 0 := hz
    show triStep (1 / 2) 1 z 2 = 0
    simp [triStep, hz2]
  · intro x
    refine ⟨fun i => if i = 2 then 0 else x i, by show (if (2 : Fin 3) = 2 then (0 : ℝ) else x 2) = 0; simp,
      fun i => if i = 2 then x 2 else 0, fun z hz => ?_, ?_⟩
    · have hz2 : z 2 = 0 := hz
      show z 0 * (if (0 : Fin 3) = 2 then x 2 else 0) + z 1 * (if (1 : Fin 3) = 2 then x 2 else 0)
        + z 2 * (if (2 : Fin 3) = 2 then x 2 else 0) = 0
      simp [hz2]
    · funext i
      fin_cases i <;> simp
  · intro c hc hcv
    have hc2 : c 2 = 0 := hc
    have hc0 : c 0 = 0 := by
      have h : c 0 * (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
          + c 1 * (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
          + c 2 * (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0 := hcv
      simpa using h
    show triStep (1 / 2) 1 c 0 * triStep (1 / 2) 1 c 0 + triStep (1 / 2) 1 c 1 * triStep (1 / 2) 1 c 1
        + triStep (1 / 2) 1 c 2 * triStep (1 / 2) 1 c 2
      ≤ (1 / 2) ^ 2 * (c 0 * c 0 + c 1 * c 1 + c 2 * c 2)
    simp [triStep, hc0, hc2]
    nlinarith [sq_nonneg (c 1)]
  · intro ρ hρ hg
    have h := hg (fun i => if i = 2 then 1 else 0) (by
      show (if (0 : Fin 3) = 2 then (1 : ℝ) else 0) * (if (0 : Fin 3) = 0 then (1 : ℝ) else 0)
        + (if (1 : Fin 3) = 2 then (1 : ℝ) else 0) * (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
        + (if (2 : Fin 3) = 2 then (1 : ℝ) else 0) * (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
      simp)
    have hT : triStep (1 / 2) 1 (fun i => if i = 2 then (1 : ℝ) else 0)
        = fun i => if i = 2 then (1 : ℝ) else 0 := by
      funext i
      fin_cases i <;> simp [triStep]
    have hform : ∀ y : Fin 3 → ℝ,
        (triTransfer (1 / 2) 1 (by norm_num) (by norm_num)).form y y
          = y 0 * y 0 + y 1 * y 1 + y 2 * y 2 := fun _ => rfl
    change (triTransfer (1 / 2) 1 (by norm_num) (by norm_num)).form
        (triStep (1 / 2) 1 (fun i => if i = 2 then (1 : ℝ) else 0))
        (triStep (1 / 2) 1 (fun i => if i = 2 then (1 : ℝ) else 0))
      ≤ ρ ^ 2 * (triTransfer (1 / 2) 1 (by norm_num) (by norm_num)).form
        (fun i => if i = 2 then (1 : ℝ) else 0) (fun i => if i = 2 then (1 : ℝ) else 0) at h
    rw [hT, hform] at h
    simp at h
    nlinarith [sq_abs ρ, abs_nonneg ρ]

#print axioms coarse_gap_does_not_lift

end MassGap.ObserverGapSplit
