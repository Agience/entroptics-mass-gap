import Mathlib
import MassGap.ClayStatement

/-!
# MassGap.CompositesObserver — why `RepTie` reads admissible potentials only

`Composites.RepTie` asks, for every orthogonal `R`, every index `i`, every coupling `g` and every
admissible `A : GPot N` (`GPot.Adm A`),

  `cval g (rotPot R A) (cl i) = ∑_{j ∈ supp (rep R i)} rep R i j · cval g A (cl j)`.

`RepTieAll` is the same identity on every function `(Fin 4 → ℝ) → Fin 4 → Fin N → Fin N → ℂ`.
`covDF` reads `A` through `fderiv`, which is `0` at a point where its argument is not
differentiable, and `fderiv` of a sum is not the sum of the `fderiv`s there. This module builds a
potential on which `RepTieAll` fails for every `rep`, as soon as the family contains the monomial
`Re tr F₂₀` — which `Covers` asks of it. The potential is not admissible (`badPot_not_adm`), so
`RepTie` does not read it.

## The witness

* `dirich`: `0` on the irrationals, `1` on the rationals; continuous nowhere
  (`dirich_not_continuousAt`).
* `badPot t`: `A₀ = t (4 χ(y₀) + y₂) · 𝟙`, `A₁ = −3 t χ(y₀) · 𝟙`, `A₂ = A₃ = 0`, `χ = dirich`, `𝟙` the
  all-ones matrix. For `t ≠ 0` the components `A₀`, `A₁` are differentiable nowhere
  (`badPot_not_differentiableAt`), so every `fderiv` of every component is `0`
  (`fderiv_badPot`), every `covDF 0 (badPot t)` is `0` (`covDF_badPot`), and
  `cval 0 (badPot t) m` does not depend on `t ≠ 0` (`cval_badPot`).
* `rot`: the rotation by the `3-4-5` angle in the `(0, 1)` plane (`rot_orth`). Under it the
  `χ` terms cancel in the rotated `A′₀ = (3/5) A₀ + (4/5) A₁ = (3/5) t y₂ · 𝟙`, and `A′₂ = 0`
  (`rotPot_badPot_zero`, `rotPot_badPot_two`). So `Re tr F′₂₀(0) = (3/5) t N`
  (`cval_rot_badPot`), linear in `t`.

At `g = 0` the right side of `RepTieAll` takes the same value at `t = 1` and `t = 2`, and the left
side takes `(3/5) N` and `(6/5) N`.

## The theorems

* `not_covers_and_repTieAll` — for `N ≠ 0`, no `Composites N` has both `Covers` and `RepTieAll`.
* `badPot_not_adm` — the witness is not `GPot.Adm`: it is not differentiable.
* `repTie_of_repTieAll` — `RepTieAll` implies `RepTie`. `RepTie` reads the class `GPot.Adm` that
  `Tied` and `CompNondeg` read; the same holds over `G` (`CompositesG.RepTie`, `AdmPot`).

DERIVED (module-wide): `3`, `4`, `5` the Pythagorean triple of the rotation; `0`, `1`, `2`, `3` the
directions; `1`, `2` the two values of `t`; `0` the coupling and the excluded colour count.
-/

noncomputable section

namespace MassGap.CompositesObserver

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. A function continuous nowhere -/

open Classical in
/-- `0` on the irrationals, `1` on the rationals. DERIVED: `0`, `1` the two values. -/
def dirich (s : ℝ) : ℝ := if Irrational s then 0 else 1

/-- `dirich` is continuous at no point.

DERIVED: `1/2` half the gap between the two values. -/
theorem dirich_not_continuousAt (s : ℝ) : ¬ ContinuousAt dirich s := by
  intro h
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hδ'⟩ := h (1 / 2) (by norm_num)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + δ by linarith)
  obtain ⟨r, hr, hr1, hr2⟩ := exists_irrational_btwn (show s < s + δ by linarith)
  have h1 := @hδ' (q : ℝ) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h2 := @hδ' r (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have e1 : dirich (q : ℝ) = 1 := by simp [dirich, Rat.not_irrational]
  have e2 : dirich r = 0 := by simp [dirich, hr]
  rw [e1, Real.dist_eq, abs_lt] at h1
  rw [e2, Real.dist_eq, abs_lt] at h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- `a · dirich (y 0) + b y`, `a ≠ 0`, `b` continuous, is continuous at no point of `ℝ⁴`.

DERIVED: `0` the first direction and the excluded coefficient; `4` the dimension. -/
theorem not_continuousAt_dirich_add {a : ℝ} (ha : a ≠ 0) {b : (Fin 4 → ℝ) → ℝ}
    (hb : Continuous b) (x : Fin 4 → ℝ) :
    ¬ ContinuousAt (fun y : Fin 4 → ℝ => a * dirich (y 0) + b y) x := by
  intro h
  have h2 : ContinuousAt (fun y : Fin 4 → ℝ => dirich (y 0)) x := by
    have e : (fun y : Fin 4 → ℝ => dirich (y 0))
        = fun y => (a * dirich (y 0) + b y - b y) / a := by
      funext y
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ ha]
    rw [e]
    exact (h.sub hb.continuousAt).div_const a
  have hg : Continuous fun s : ℝ => Function.update x 0 s :=
    continuous_const.update 0 continuous_id
  have h3 : ContinuousAt (fun s : ℝ => dirich ((Function.update x 0 s) 0)) (x 0) :=
    ContinuousAt.comp_of_eq h2 hg.continuousAt (by simp)
  have e : (fun s : ℝ => dirich ((Function.update x 0 s) 0)) = dirich := by
    funext s
    simp
  rw [e] at h3
  exact dirich_not_continuousAt _ h3

/-! ## 2. The witness potential -/

/-- The all-ones matrix. DERIVED: `1` its entries. -/
def oneM : Fin N → Fin N → ℂ := fun _ _ => 1

/-- **The witness**: `A₀ = t (4 χ(y₀) + y₂) 𝟙`, `A₁ = −3 t χ(y₀) 𝟙`, `A₂ = A₃ = 0`.

DERIVED: `0`, `1`, `2` the directions; `4`, `3` the legs of the triple. -/
def badPot (t : ℝ) : GPot N := fun y ν =>
  if ν = 0 then (t * (4 * dirich (y 0) + y 2)) • (oneM : Fin N → Fin N → ℂ)
  else if ν = 1 then (t * (-3 * dirich (y 0))) • (oneM : Fin N → Fin N → ℂ) else 0

/-- **The components `A₀`, `A₁` are differentiable nowhere**, `t ≠ 0`, `N ≠ 0`.

DERIVED: `0`, `1` the two directions; `4`, `3` the legs; `0` the excluded values. -/
theorem badPot_not_differentiableAt (hN : N ≠ 0) {t : ℝ} (ht : t ≠ 0) (x : Fin 4 → ℝ)
    {ν : Fin 4} (hν : ν = 0 ∨ ν = 1) :
    ¬ DifferentiableAt ℝ (fun y => badPot (N := N) t y ν) x := by
  intro hd
  set i0 : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩
  have hcont : Continuous (fun M : Fin N → Fin N → ℂ => (M i0 i0).re) := by fun_prop
  have hc : ContinuousAt (fun y => ((badPot (N := N) t y ν) i0 i0).re) x :=
    hcont.continuousAt.comp hd.continuousAt
  rcases hν with rfl | rfl
  · have e : (fun y => ((badPot (N := N) t y 0) i0 i0).re)
        = fun y : Fin 4 → ℝ => (4 * t) * dirich (y 0) + t * y 2 := by
      funext y
      simp [badPot, oneM]
      ring
    rw [e] at hc
    exact not_continuousAt_dirich_add (mul_ne_zero (by norm_num) ht)
      (continuous_const.mul (continuous_apply 2)) x hc
  · have e : (fun y => ((badPot (N := N) t y 1) i0 i0).re)
        = fun y : Fin 4 → ℝ => (-3 * t) * dirich (y 0) + (fun _ => (0 : ℝ)) y := by
      funext y
      simp [badPot, oneM]
      ring
    rw [e] at hc
    exact not_continuousAt_dirich_add (mul_ne_zero (by norm_num) ht) continuous_const x hc

/-- **Every `fderiv` of every component of the witness is `0`**, `t ≠ 0`, `N ≠ 0`.

DERIVED: `0`, `1` the non-differentiable directions; `0` the derivative. -/
theorem fderiv_badPot (hN : N ≠ 0) {t : ℝ} (ht : t ≠ 0) (x : Fin 4 → ℝ) (ν : Fin 4) :
    fderiv ℝ (fun y => badPot (N := N) t y ν) x = 0 := by
  by_cases h01 : ν = 0 ∨ ν = 1
  · exact fderiv_zero_of_not_differentiableAt (badPot_not_differentiableAt hN ht x h01)
  · have h01' := not_or.mp h01
    have e : (fun y => badPot (N := N) t y ν) = fun _ => 0 := by
      funext y
      simp [badPot, h01'.1, h01'.2]
    rw [e]
    simp

/-- **Every `covDF 0` of the witness is `0`**, `t ≠ 0`, `N ≠ 0`.

DERIVED: `0` the coupling and the value. -/
theorem covDF_badPot (hN : N ≠ 0) {t : ℝ} (ht : t ≠ 0) (ρ σ : Fin 4) (ds : List (Fin 4))
    (x : Fin 4 → ℝ) : covDF 0 (badPot (N := N) t) ρ σ ds x = 0 := by
  induction ds generalizing x with
  | nil => simp [covDF, fderiv_badPot hN ht]
  | cons μ ds ih =>
    have e : covDF 0 (badPot (N := N) t) ρ σ ds = fun _ => 0 := funext ih
    simp only [covDF]
    rw [e]
    simp

/-- **`cval 0 (badPot t)` does not depend on `t ≠ 0`.**

DERIVED: `0` the coupling; `1` the reference value of `t`. -/
theorem cval_badPot (hN : N ≠ 0) {t : ℝ} (ht : t ≠ 0) (m : CMono) :
    cval 0 (badPot (N := N) t) m = cval 0 (badPot (N := N) 1) m := by
  simp only [cval, wordTr, covDF_badPot hN ht, covDF_badPot hN one_ne_zero]

/-- The witness is not `GPot.Adm`. DERIVED: `1` the order of smoothness; `0` the direction. -/
theorem badPot_not_adm (hN : N ≠ 0) {t : ℝ} (ht : t ≠ 0) : ¬ GPot.Adm (badPot (N := N) t) := by
  intro h
  have hd : Differentiable ℝ (badPot (N := N) t) := (h.1 1).differentiable (by norm_num)
  have hd0 : DifferentiableAt ℝ (fun y => badPot (N := N) t y 0) 0 :=
    differentiableAt_pi.1 (hd 0) 0
  exact badPot_not_differentiableAt hN ht 0 (Or.inl rfl) hd0

/-! ## 3. The rotation -/

/-- **The rotation by the `3-4-5` angle in the `(0, 1)` plane.**

DERIVED: `3`, `4`, `5` the triple; `0`, `1` the entries. -/
def rot : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3 / 5, -4 / 5, 0, 0; 4 / 5, 3 / 5, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `rot` is orthogonal. DERIVED: `4` the dimension. -/
theorem rot_orth : rot ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- `rot` fixes the direction `2`. DERIVED: `2` the direction. -/
theorem rot_mulVec_two (y : Fin 4 → ℝ) : (rot *ᵥ y) 2 = y 2 := by
  simp [rot, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- **The rotated `A′₀`**: the `χ` terms cancel, `A′₀(y) = y₂ · ((3/5) t 𝟙)`.

DERIVED: `0`, `2` the directions; `3`, `5` the triple. -/
theorem rotPot_badPot_zero (t : ℝ) (y : Fin 4 → ℝ) :
    rotPot rot (badPot (N := N) t) y 0 = y 2 • ((3 / 5 * t) • (oneM : Fin N → Fin N → ℂ)) := by
  funext i j
  simp only [rotPot, Fin.sum_univ_four, Finset.sum_apply, Pi.smul_apply, badPot, rot_mulVec_two]
  simp [rot, oneM]
  ring

/-- **The rotated `A′₂` is `0`.** DERIVED: `2` the direction. -/
theorem rotPot_badPot_two (t : ℝ) (y : Fin 4 → ℝ) : rotPot rot (badPot (N := N) t) y 2 = 0 := by
  funext i j
  simp only [rotPot, Fin.sum_univ_four, Finset.sum_apply, Pi.smul_apply, badPot]
  simp [rot]

/-- **`F′₂₀(0) = (3/5) t 𝟙`** at `g = 0`.

DERIVED: `0`, `2` the directions; `3`, `5` the triple; `0` the coupling and the origin. -/
theorem covDF_rot_badPot (t : ℝ) :
    covDF 0 (rotPot rot (badPot (N := N) t)) 2 0 [] 0
      = (3 / 5 * t) • (oneM : Fin N → Fin N → ℂ) := by
  have e0 : (fun y => rotPot rot (badPot (N := N) t) y 0)
      = fun y : Fin 4 → ℝ => y 2 • ((3 / 5 * t) • (oneM : Fin N → Fin N → ℂ)) :=
    funext (rotPot_badPot_zero t)
  have e2 : (fun y => rotPot rot (badPot (N := N) t) y 2) = fun _ => 0 :=
    funext (rotPot_badPot_two t)
  have hd : fderiv ℝ (fun y : Fin 4 → ℝ => y 2 • ((3 / 5 * t) • (oneM : Fin N → Fin N → ℂ))) 0
      = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2).smulRight
          ((3 / 5 * t) • (oneM : Fin N → Fin N → ℂ)) :=
    ((hasFDerivAt_apply 2 (0 : Fin 4 → ℝ)).smul_const _).fderiv
  simp only [covDF]
  rw [e0, e2, hd]
  simp [dir]

/-- The monomial `Re tr F₂₀`. DERIVED: `2`, `0` the directions. -/
def m0 : CMono := [([([], 2, 0)], true)]

/-- **`cval 0 (rotPot rot (badPot t)) (Re tr F₂₀) = (3/5) t N`.**

DERIVED: `3`, `5` the triple; `0` the coupling. -/
theorem cval_rot_badPot (t : ℝ) :
    cval 0 (rotPot rot (badPot (N := N) t)) m0 = 3 / 5 * t * N := by
  simp only [cval, wordTr, m0, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, if_pos, covDF_rot_badPot]
  simp [Matrix.trace, oneM]
  ring

/-! ## 4. The exclusion -/

/-- **The rotation tie on every potential**: `Composites.RepTie` without its `GPot.Adm` clause.

DERIVED: `4` the dimension. -/
def RepTieAll (C : Composites N) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (i : C.Ix) (A : GPot N) (g : ℝ),
      cval g (rotPot R A) (C.cl i) = ∑ j ∈ (C.rep R i).support, C.rep R i j * cval g A (C.cl j)

/-- **No family of composites has both `Covers` and `RepTieAll`**, `N ≠ 0`.

DERIVED: `1`, `2` the two values of `t`; `0` the coupling and the excluded colour count. -/
theorem not_covers_and_repTieAll (hN : N ≠ 0) (C : Composites N) :
    ¬ (C.Covers ∧ RepTieAll C) := by
  rintro ⟨hcov, hrep⟩
  obtain ⟨i, hi⟩ := hcov m0 (by simp [m0]) (by simp [m0])
  have h1 := hrep rot rot_orth i (badPot 1) 0
  have h2 := hrep rot rot_orth i (badPot 2) 0
  rw [hi, cval_rot_badPot] at h1 h2
  have e : ∀ j, cval 0 (badPot (N := N) 2) (C.cl j) = cval 0 (badPot (N := N) 1) (C.cl j) :=
    fun j => cval_badPot hN two_ne_zero _
  simp only [e] at h2
  have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  linarith

/-! ## 5. The restriction -/

/-- `RepTieAll` implies `Composites.RepTie`, which asks the identity only at `GPot.Adm A`.
DERIVED: no numeral. -/
theorem repTie_of_repTieAll (C : Composites N) (h : RepTieAll C) : C.RepTie :=
  fun R hR i A _ g => h R hR i A g

end MassGap.CompositesObserver

end

#print axioms MassGap.CompositesObserver.dirich_not_continuousAt
#print axioms MassGap.CompositesObserver.cval_badPot
#print axioms MassGap.CompositesObserver.badPot_not_adm
#print axioms MassGap.CompositesObserver.rot_orth
#print axioms MassGap.CompositesObserver.cval_rot_badPot
#print axioms MassGap.CompositesObserver.not_covers_and_repTieAll
#print axioms MassGap.CompositesObserver.repTie_of_repTieAll
