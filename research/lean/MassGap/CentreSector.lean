import Mathlib
import MassGap.ChessboardRead

/-!
# MassGap.CentreSector — flux sectors of transfer data, and what a charged-sector bound cannot reach

A centre (flux) symmetry of transfer data splits the observables into a neutral part and a charged
part. `NeutralProjection D` is the projection onto the neutral part, stated by what the splitting
needs: idempotent, symmetric for the reflection form, commuting with `T`, fixing the vacuum. For a
`Z_N` centre acting by form-preserving linear maps that commute with `T` and fix the vacuum, the group
average satisfies these four fields; for `Z_2` it is `(1 + σ)/2`. This module constructs neither.

## What it gives

1. `form_pow_split`: every lag profile is the sum of the neutral one and the charged one — the
   cross terms vanish (`form_cross_eq_zero`, `form_cross_eq_zero'`).
2. `gapAt_iff_sectors`: under `PositiveTransfer D`, `TransferGap.GapAt D r` holds exactly when the
   single-lag bound at lag `m ≠ 0` holds on the neutral vectors orthogonal to the vacuum AND on the
   charged vectors. A bound on the charged sector is the second conjunct alone.
3. `gapAt_iff_neutral_of_trivial`: when the projection is the identity the charged conjunct holds
   only at `0`, and `GapAt` is the single-lag bound of `ChessboardRead.gapAt_iff_lag`. Every transfer
   data carries the identity projection (`NeutralProjection.trivial`).
4. `charged_rate_does_not_reach_neutral`: for every rate `0 ≤ r < 1` there is transfer data on
   `Fin 3 → ℝ` with a neutral projection, positive transfer, the charged sector annihilated after one
   step (rate `0`, the strongest possible flux-sector bound), a gap at some rate `s < 1` — so the
   vacuum is simple — and no gap at rate `r`. So no bound on the charged sector, at any rate, gives a
   rate on the neutral sector.

## Scope

The no-go is abstract: it shows the three inputs a centre argument supplies (reflection positivity,
positivity of `T`, a bound on the non-zero flux sectors) do not determine the neutral rate. It says
nothing about whether the Wilson neutral sector is gapped.
-/

namespace MassGap.CentreSector

open MassGap MassGap.Transfer MassGap.GNSHilbert

/-! ## 1. The neutral projection and the sector split -/

section Sectors

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **A neutral projection of transfer data**: the projection onto the centre-neutral observables.
Idempotent, symmetric for the reflection form, commuting with the transfer operator, fixing the
vacuum.

DERIVED: no numeral occurs in the fields. -/
structure NeutralProjection (D : TransferData A) where
  /-- The projection. -/
  P : A →ₗ[ℝ] A
  /-- Idempotence. -/
  P_idem : ∀ x, P (P x) = P x
  /-- Symmetry for the reflection form. -/
  P_symm : ∀ x y, D.form (P x) y = D.form x (P y)
  /-- The centre commutes with the transfer operator. -/
  P_T : ∀ x, P (D.T x) = D.T (P x)
  /-- The vacuum is neutral. -/
  P_vac : P D.vac = D.vac

/-- The identity is a neutral projection of every transfer data: the centre acting trivially.

DERIVED: no numeral occurs. -/
def NeutralProjection.trivial (D : TransferData A) : NeutralProjection D where
  P := LinearMap.id
  P_idem _ := rfl
  P_symm _ _ := rfl
  P_T _ := rfl
  P_vac := rfl

/-- The projection commutes with every power of `T`. Induction from `P_T`.

DERIVED: no numeral occurs in the statement. -/
theorem P_T_pow {D : TransferData A} (Q : NeutralProjection D) (n : ℕ) (x : A) :
    Q.P ((D.T ^ n) x) = (D.T ^ n) (Q.P x) := by
  induction n generalizing x with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, Q.P_T]

#print axioms P_T_pow

/-- The charged part `x − P x` has no neutral component.

DERIVED: `0` is the zero vector concluded. -/
theorem P_sub_self {D : TransferData A} (Q : NeutralProjection D) (x : A) :
    Q.P (x - Q.P x) = 0 := by
  rw [map_sub, Q.P_idem, sub_self]

#print axioms P_sub_self

/-- A charged vector pairs to zero with every neutral one: `D.form x (P y) = 0` when `P x = 0`.

DERIVED: `0` is the charged condition and the pairing concluded. -/
theorem form_P_left_eq_zero {D : TransferData A} (Q : NeutralProjection D) (x : A)
    (hx : Q.P x = 0) (y : A) : D.form x (Q.P y) = 0 := by
  rw [← Q.P_symm, hx, PreForm.form_zero_left]

#print axioms form_P_left_eq_zero

/-- A charged vector is orthogonal to the vacuum: `P vac = vac`.

DERIVED: `0` is the charged condition and the pairing concluded. -/
theorem form_vac_of_P_eq_zero {D : TransferData A} (Q : NeutralProjection D) {x : A}
    (hx : Q.P x = 0) : D.form x D.vac = 0 := by
  rw [← Q.P_vac]
  exact form_P_left_eq_zero Q x hx D.vac

#print axioms form_vac_of_P_eq_zero

/-- The neutral part pairs with the vacuum as the whole vector does.

DERIVED: no numeral occurs. -/
theorem form_vac_P {D : TransferData A} (Q : NeutralProjection D) (x : A) :
    D.form (Q.P x) D.vac = D.form x D.vac := by
  rw [Q.P_symm, Q.P_vac]

#print axioms form_vac_P

/-- The first cross term vanishes: `D.form (P x) (Tᵐ (x − P x)) = 0`.

DERIVED: `0` is the value concluded. -/
theorem form_cross_eq_zero {D : TransferData A} (Q : NeutralProjection D) (m : ℕ) (x : A) :
    D.form (Q.P x) ((D.T ^ m) (x - Q.P x)) = 0 := by
  rw [Q.P_symm, P_T_pow, P_sub_self, map_zero, PreForm.form_zero_right]

#print axioms form_cross_eq_zero

/-- The second cross term vanishes: `D.form (x − P x) (Tᵐ (P x)) = 0`.

DERIVED: `0` is the value concluded. -/
theorem form_cross_eq_zero' {D : TransferData A} (Q : NeutralProjection D) (m : ℕ) (x : A) :
    D.form (x - Q.P x) ((D.T ^ m) (Q.P x)) = 0 := by
  rw [← P_T_pow, D.form_symm, Q.P_symm, P_sub_self, PreForm.form_zero_right]

#print axioms form_cross_eq_zero'

/-- **The lag profile splits over the sectors.** `D.form x (Tᵐ x)` is the neutral profile of `P x`
plus the charged profile of `x − P x`.

DERIVED: no numeral occurs in the statement. -/
theorem form_pow_split {D : TransferData A} (Q : NeutralProjection D) (m : ℕ) (x : A) :
    D.form x ((D.T ^ m) x)
      = D.form (Q.P x) ((D.T ^ m) (Q.P x))
        + D.form (x - Q.P x) ((D.T ^ m) (x - Q.P x)) := by
  have hx : Q.P x + (x - Q.P x) = x := by abel
  calc D.form x ((D.T ^ m) x)
      = D.form (Q.P x + (x - Q.P x)) ((D.T ^ m) (Q.P x + (x - Q.P x))) := by rw [hx]
    _ = D.form (Q.P x) ((D.T ^ m) (Q.P x)) + D.form (Q.P x) ((D.T ^ m) (x - Q.P x))
        + (D.form (x - Q.P x) ((D.T ^ m) (Q.P x))
          + D.form (x - Q.P x) ((D.T ^ m) (x - Q.P x))) := by
        rw [map_add, D.form_add_left, PreForm.form_add_right, PreForm.form_add_right]
    _ = D.form (Q.P x) ((D.T ^ m) (Q.P x))
        + D.form (x - Q.P x) ((D.T ^ m) (x - Q.P x)) := by
        rw [form_cross_eq_zero, form_cross_eq_zero']
        ring

#print axioms form_pow_split

/-- **Two sector bounds give the whole bound.** A single-lag bound at rate `r` on the neutral part
and on the charged part gives it on `x`.

DERIVED: no numeral occurs in the statement. -/
theorem lag_split_le {D : TransferData A} (Q : NeutralProjection D) {m : ℕ} {r : ℝ} (x : A)
    (hN : D.form (Q.P x) ((D.T ^ m) (Q.P x)) ≤ r ^ m * D.form (Q.P x) (Q.P x))
    (hC : D.form (x - Q.P x) ((D.T ^ m) (x - Q.P x))
      ≤ r ^ m * D.form (x - Q.P x) (x - Q.P x)) :
    D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x := by
  have h0 := form_pow_split Q 0 x
  simp only [pow_zero, Module.End.one_apply] at h0
  rw [form_pow_split Q m x, h0, mul_add]
  exact add_le_add hN hC

#print axioms lag_split_le

/-- **THE GAP IS THE TWO SECTOR BOUNDS.** Under `PositiveTransfer D`, `m ≠ 0` and `0 ≤ r`:
`TransferGap.GapAt D r` holds exactly when every neutral `x` orthogonal to the vacuum and every
charged `x` satisfy `D.form x (Tᵐ x) ≤ rᵐ · D.form x x`. `ChessboardRead.gapAt_iff_lag`, then the
split. A bound on a charged sector is the second conjunct alone and constrains nothing in the
first.

DERIVED: `0` is the excluded lag, the lower end of `r`, the vacuum pairing and the charged condition. -/
theorem gapAt_iff_sectors (D : TransferData A) (hP : PositiveTransfer D)
    (Q : NeutralProjection D) {m : ℕ} (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    MassGap.TransferGap.GapAt D r ↔
      ((∀ x : A, Q.P x = x → D.form x D.vac = 0 →
          D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x) ∧
        (∀ x : A, Q.P x = 0 → D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x)) := by
  rw [MassGap.ChessboardRead.gapAt_iff_lag D hP hm hr]
  constructor
  · intro h
    exact ⟨fun x _ hx => h x hx, fun x hx => h x (form_vac_of_P_eq_zero Q hx)⟩
  · rintro ⟨hN, hC⟩ x hx
    refine lag_split_le Q x (hN (Q.P x) (Q.P_idem x) ?_) (hC (x - Q.P x) (P_sub_self Q x))
    rw [form_vac_P, hx]

#print axioms gapAt_iff_sectors

/-- Under the trivial action the charged sector is zero.

DERIVED: `0` is the charged condition and the vector concluded. -/
theorem charged_eq_zero_of_trivial {D : TransferData A} (Q : NeutralProjection D)
    (hid : ∀ x, Q.P x = x) {x : A} (hx : Q.P x = 0) : x = 0 :=
  (hid x).symm.trans hx

#print axioms charged_eq_zero_of_trivial

/-- **Under the trivial action the gap is the neutral bound alone.** When the centre acts as the
identity, `GapAt D r` is the single-lag bound on the vectors orthogonal to the vacuum — every one of
them neutral — and the charged conjunct of `gapAt_iff_sectors` holds with nothing in it.

DERIVED: `0` is the excluded lag, the lower end of `r`, the vacuum pairing and the charged
condition. -/
theorem gapAt_iff_neutral_of_trivial (D : TransferData A) (hP : PositiveTransfer D)
    (Q : NeutralProjection D) (hid : ∀ x, Q.P x = x) {m : ℕ} (hm : m ≠ 0) {r : ℝ}
    (hr : 0 ≤ r) :
    MassGap.TransferGap.GapAt D r ↔
      ∀ x : A, Q.P x = x → D.form x D.vac = 0 →
        D.form x ((D.T ^ m) x) ≤ r ^ m * D.form x x := by
  rw [gapAt_iff_sectors D hP Q hm hr]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun x hx => ?_⟩
    rw [charged_eq_zero_of_trivial Q hid hx]
    simp only [map_zero, PreForm.form_zero_left, mul_zero, le_refl]

#print axioms gapAt_iff_neutral_of_trivial

end Sectors

/-! ## 2. A charged-sector bound at every rate does not give the neutral rate -/

section NoGo

/-- The coordinate form on `Fin 3 → ℝ`.

DERIVED: `3` is the number of coordinates of the example — the vacuum, one neutral excitation and
one charged excitation. -/
noncomputable def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ i, x i * y i

/-- The diagonal linear map with entries `d`.

DERIVED: `3` is the number of coordinates of the example. -/
noncomputable def diag3 (d : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := d i * x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- `diag3 d x i = d i * x i`, by definition.

DERIVED: `3` is the number of coordinates of the example. -/
theorem diag3_apply (d x : Fin 3 → ℝ) (i : Fin 3) : diag3 d x i = d i * x i := rfl

/-- The vacuum: the first coordinate vector.

DERIVED: `3` is the number of coordinates; `0` is the vacuum's index; `1` and `0` are its entries. -/
noncomputable def vac3 (i : Fin 3) : ℝ := if i = 0 then 1 else 0

/-- The transfer entries: `1` on the vacuum, `s` on the neutral excitation, `0` on the charged one.

DERIVED: `3` is the number of coordinates; `0`, `1` index the vacuum and the neutral excitation; the
entry `1` fixes the vacuum and the entry `0` annihilates the charged excitation — the rate-zero
charged sector the no-go grants. -/
noncomputable def rate3 (s : ℝ) (i : Fin 3) : ℝ := if i = 0 then 1 else if i = 1 then s else 0

/-- The neutral projection's entries: `0` on the charged coordinate, `1` elsewhere.

DERIVED: `3` is the number of coordinates; `2` is the charged coordinate's index; `0` and `1` are
the entries of a coordinate projection. -/
noncomputable def proj3 (i : Fin 3) : ℝ := if i = 2 then 0 else 1

/-- The neutral excitation.

DERIVED: `3` is the number of coordinates; `1` is the neutral excitation's index and its entry;
`0` the other entries. -/
noncomputable def unit1 (i : Fin 3) : ℝ := if i = 1 then 1 else 0

/-- `rate3 s 0 = 1`.

DERIVED: `0` is the vacuum index; `1` its entry. -/
theorem rate3_zero (s : ℝ) : rate3 s 0 = 1 := if_pos rfl

/-- `rate3 s 1 = s`.

DERIVED: `1` is the neutral index. -/
theorem rate3_one (s : ℝ) : rate3 s 1 = s := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  unfold rate3
  rw [if_neg h10, if_pos (rfl : (1 : Fin 3) = 1)]

/-- `rate3 s 2 = 0`.

DERIVED: `2` is the charged index; `0` its entry. -/
theorem rate3_two (s : ℝ) : rate3 s 2 = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  unfold rate3
  rw [if_neg h20, if_neg h21]

/-- `unit1 0 = 0`. DERIVED: `0` is the vacuum index and the entry there; `3` is the dimension. -/
theorem unit1_zero : unit1 0 = 0 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  unfold unit1
  rw [if_neg h01]

/-- `unit1 1 = 1`. DERIVED: indices and entries of `unit1`. -/
theorem unit1_one : unit1 1 = 1 := if_pos rfl

/-- `unit1 2 = 0`. DERIVED: `2` is the charged index; `0` is the entry there. -/
theorem unit1_two : unit1 2 = 0 := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  unfold unit1
  rw [if_neg h21]

/-- The transfer entries are nonnegative at `0 ≤ s`.

DERIVED: `0` is the lower bound; `3` is the dimension of the example. -/
theorem rate3_nonneg (s : ℝ) (hs0 : 0 ≤ s) (i : Fin 3) : 0 ≤ rate3 s i := by
  unfold rate3
  split_ifs <;> linarith

/-- The transfer entries have square at most `1` at `0 ≤ s ≤ 1`.

DERIVED: `0` and `1` are the ends of the range of `s` and the bound; `3` is the dimension of the example. -/
theorem rate3_sq_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin 3) :
    rate3 s i * rate3 s i ≤ 1 := by
  unfold rate3
  split_ifs <;> nlinarith

/-- A vector's pairing with the vacuum is its first coordinate.

DERIVED: `0`, `1`, `2` are the coordinate indices; `3` the number of coordinates. -/
theorem dot3_vac (x : Fin 3 → ℝ) : dot3 x vac3 = x 0 := by
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp [dot3, vac3, Fin.sum_univ_three, h1, h2]

/-- **The example's transfer data**, at `0 ≤ s ≤ 1`: the coordinate form on `Fin 3 → ℝ`, the vacuum
`vac3`, and `T = diag(1, s, 0)`.

DERIVED: `3` is the number of coordinates; `0` and `1` bound `s`, the range in which `T` contracts;
`1` is the vacuum's norm. -/
noncomputable def noGoData (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : TransferData (Fin 3 → ℝ) where
  form := dot3
  form_symm x y := by
    show dot3 x y = dot3 y x
    unfold dot3
    exact Finset.sum_congr rfl (fun i _ => mul_comm (x i) (y i))
  form_add_left x y z := by
    show dot3 (x + y) z = dot3 x z + dot3 y z
    simp only [dot3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  form_smul_left c x y := by
    show dot3 (c • x) y = c * dot3 x y
    simp only [dot3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  form_nonneg x := by
    show 0 ≤ dot3 x x
    unfold dot3
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  T := diag3 (rate3 s)
  vac := vac3
  T_symm x y := by
    show dot3 (diag3 (rate3 s) x) y = dot3 x (diag3 (rate3 s) y)
    unfold dot3
    exact Finset.sum_congr rfl (fun i _ => by simp only [diag3_apply]; ring)
  T_contract x := by
    show dot3 (diag3 (rate3 s) x) (diag3 (rate3 s) x) ≤ dot3 x x
    unfold dot3
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [diag3_apply]
    have h := rate3_sq_le s hs0 hs1 i
    nlinarith [mul_self_nonneg (x i)]
  T_vac := by
    show diag3 (rate3 s) vac3 = vac3
    funext i
    rw [diag3_apply]
    by_cases hi : i = 0
    · rw [hi, rate3_zero, one_mul]
    · have hv : vac3 i = 0 := if_neg hi
      rw [hv, mul_zero]
  vac_norm := by
    show dot3 vac3 vac3 = 1
    rw [dot3_vac]
    exact if_pos rfl

/-- The example's neutral projection: `diag(1, 1, 0)`, which commutes with `T`.

DERIVED: `3` is the number of coordinates; `0`, `1`, `2` the indices. -/
noncomputable def noGoProj (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    NeutralProjection (noGoData s hs0 hs1) where
  P := diag3 proj3
  P_idem x := by
    show diag3 proj3 (diag3 proj3 x) = diag3 proj3 x
    funext i
    simp only [diag3_apply]
    unfold proj3
    split_ifs <;> ring
  P_symm x y := by
    show dot3 (diag3 proj3 x) y = dot3 x (diag3 proj3 y)
    unfold dot3
    exact Finset.sum_congr rfl (fun i _ => by simp only [diag3_apply]; ring)
  P_T x := by
    show diag3 proj3 (diag3 (rate3 s) x) = diag3 (rate3 s) (diag3 proj3 x)
    funext i
    simp only [diag3_apply]
    ring
  P_vac := by
    show diag3 proj3 vac3 = vac3
    funext i
    rw [diag3_apply]
    by_cases hi : i = 0
    · have h02 : (0 : Fin 3) ≠ 2 := by decide
      have hp : proj3 i = 1 := by rw [hi]; exact if_neg h02
      rw [hp, one_mul]
    · have hv : vac3 i = 0 := if_neg hi
      rw [hv, mul_zero]

/-- `PositiveTransfer` for the example at `0 ≤ s`.

DERIVED: `0` and `1` are the ends of the range of `s`. -/
theorem noGo_positive (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    PositiveTransfer (noGoData s hs0 hs1) := by
  intro x
  show 0 ≤ dot3 x (diag3 (rate3 s) x)
  unfold dot3
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [diag3_apply, show x i * (rate3 s i * x i) = rate3 s i * (x i * x i) by ring]
  exact mul_nonneg (rate3_nonneg s hs0 i) (mul_self_nonneg (x i))

#print axioms noGo_positive

/-- `T` annihilates every charged vector of the example.

DERIVED: `0` is the charged condition and the image; `2` the charged index; `1` the neutral entry of
`proj3`. -/
theorem noGo_T_charged (s : ℝ) (x : Fin 3 → ℝ) (hx : diag3 proj3 x = 0) :
    diag3 (rate3 s) x = 0 := by
  funext i
  have hxi := congrFun hx i
  rw [diag3_apply, Pi.zero_apply] at hxi
  rw [diag3_apply, Pi.zero_apply]
  by_cases h2 : i = 2
  · rw [h2, rate3_two, zero_mul]
  · have hp : proj3 i = 1 := if_neg h2
    rw [hp, one_mul] at hxi
    rw [hxi, mul_zero]

#print axioms noGo_T_charged

/-- **The charged sector is annihilated after one step**: every charged `x` has
`D.form x (T^{k+1} x) = 0` — the single-lag bound on the charged sector at rate `0`, every lag.

DERIVED: `0` is the charged condition, the value and the lower end of `s`; `1` is the one step and the upper end of `s`; `3` is the dimension of the example. -/
theorem noGo_charged_lag (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) (x : Fin 3 → ℝ)
    (hx : (noGoProj s hs0 hs1).P x = 0) :
    (noGoData s hs0 hs1).form x (((noGoData s hs0 hs1).T ^ (k + 1)) x) = 0 := by
  have hT : (noGoData s hs0 hs1).T x = 0 := noGo_T_charged s x hx
  rw [pow_succ, Module.End.mul_apply, hT, map_zero]
  exact PreForm.form_zero_right _ x

#print axioms noGo_charged_lag

/-- **The example is gapped at rate `s`**: `TransferGap.GapAt (noGoData s _ _) s`. A vector
orthogonal to the vacuum has first coordinate `0`, and `T` scales the rest by `s` and `0`.

DERIVED: `0` is the vacuum coordinate and the lower end of `s`; `1` is the upper end of `s`; `3` is
the number of coordinates. -/
theorem noGo_gapAt (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    MassGap.TransferGap.GapAt (noGoData s hs0 hs1) s := by
  intro x hx
  have hx0 : x 0 = 0 := (dot3_vac x).symm.trans hx
  show dot3 (diag3 (rate3 s) x) (diag3 (rate3 s) x) ≤ s ^ 2 * dot3 x x
  simp only [dot3, Fin.sum_univ_three, diag3_apply, rate3_zero, rate3_one, rate3_two, hx0]
  nlinarith [mul_self_nonneg (x 1), mul_self_nonneg (x 2), mul_self_nonneg s,
    mul_nonneg (mul_self_nonneg s) (mul_self_nonneg (x 2))]

#print axioms noGo_gapAt

/-- **The example has no gap below `s`**: at `0 ≤ r < s`, `¬ GapAt (noGoData s _ _) r`. The neutral
excitation `unit1` is orthogonal to the vacuum and `T` scales it by `s`.

DERIVED: `0` is the lower end of `r` and `s`; `1` is the upper end of `s`; `3` is the number of
coordinates. -/
theorem noGo_not_gapAt (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hrs : r < s) :
    ¬ MassGap.TransferGap.GapAt (noGoData s hs0 hs1) r := by
  intro hg
  have horth : (noGoData s hs0 hs1).form unit1 (noGoData s hs0 hs1).vac = 0 := by
    show dot3 unit1 vac3 = 0
    rw [dot3_vac, unit1_zero]
  have h' : dot3 (diag3 (rate3 s) unit1) (diag3 (rate3 s) unit1) ≤ r ^ 2 * dot3 unit1 unit1 :=
    hg unit1 horth
  simp only [dot3, Fin.sum_univ_three, diag3_apply, rate3_zero, rate3_one, rate3_two, unit1_zero,
    unit1_one, unit1_two] at h'
  nlinarith [mul_self_lt_mul_self hr0 hrs]

#print axioms noGo_not_gapAt

/-- **NO CHARGED-SECTOR BOUND GIVES THE NEUTRAL RATE.** For every `0 ≤ r < 1` there is `s` with
`r < s < 1` and transfer data carrying a neutral projection (`noGoProj`) such that: `T` is positive;
the data has a gap at rate `s`, so the vacuum is simple; the charged sector is annihilated after one
step, at every lag — a flux-sector bound at rate `0`; and there is no gap at rate `r`.

So reflection positivity, positivity of `T`, a neutral projection commuting with `T`, and a rate-`0`
bound on its charged part together fix no rate on the neutral part.

DERIVED: `0` and `1` bound `r` and `s`; `1` is also the one step `k + 1`; `0` is the charged condition
and the annihilated pairing; `3` is the example's coordinate count. -/
theorem charged_rate_does_not_reach_neutral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1), r < s ∧ s < 1 ∧
      PositiveTransfer (noGoData s hs0 hs1) ∧
      MassGap.TransferGap.GapAt (noGoData s hs0 hs1) s ∧
      (∀ (k : ℕ) (x : Fin 3 → ℝ), (noGoProj s hs0 hs1).P x = 0 →
        (noGoData s hs0 hs1).form x (((noGoData s hs0 hs1).T ^ (k + 1)) x) = 0) ∧
      ¬ MassGap.TransferGap.GapAt (noGoData s hs0 hs1) r :=
  ⟨(1 + r) / 2, by linarith, by linarith, by linarith, by linarith,
    noGo_positive _ _ _, noGo_gapAt _ _ _, fun k x hx => noGo_charged_lag _ _ _ k x hx,
    noGo_not_gapAt _ _ _ hr0 (by linarith)⟩

#print axioms charged_rate_does_not_reach_neutral

end NoGo

end MassGap.CentreSector
