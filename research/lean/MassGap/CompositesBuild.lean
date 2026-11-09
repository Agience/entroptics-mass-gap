import Mathlib
import MassGap.ClaySUFinal

/-!
# MassGap.CompositesBuild — the family of all composites, and its rotation tie

`ClaySUFinal.clayStatementAt_SU_final` takes a family `Cs : Composites N` with an index map `e`,
`he1`, `he2`, `hCD : CompData Cs`, `hCO`, `hrep`, `hLC`, `hX`. This module builds `Cs` from a mixing
`ρ` and a bare lattice field per monomial, and proves the clauses that do not depend on the bare
fields or the limit.

## The family `build ρ bare`

* Index: `Ix0`, the classical monomials `m ≠ []` with every word non-empty (the monomials `Covers`
  asks for); `cl = Subtype.val`.
* `e = eI`, `eI α = [([([], α₀, α₁), ([], α₂, α₃)], true)]`, read back by `dec`.
* `ren k i`: at `i = eI α` the mixing `∑_b M k α b • op b` (`mixF`, an `LField` by `lfSub`);
  elsewhere `bare i`.
* `rep R i`: at `i = eI α` the tensor coefficients `∑_β tcoef R α β • single (eI β) 1`; elsewhere
  `repGen R i`, the expansion of the rotated monomial (`rotM`).

## The rotation tie

For a potential with `ContDiff ℝ ∞ A`, `covDF g (rotPot R A) ρ σ ds x` is the finite combination
`rotL R ρ σ ds` of the `covDF g A ρ' σ' ds' (R x)` (`covDF_rotPot`, the chain rule through
`R *ᵥ ·` and bilinearity of the commutator; no orthogonality is used). Traces of products and real
and imaginary parts carry the expansion to the monomials: `cval g (rotPot R A) m` is the combination
`rotM R m` of the `cval g A m'` (`cval_rotPot`), and every `m'` has the shape of `m`
(`rotM_shape`), so it lies in `Ix0`. At `eI α` the combination is `∑_β tcoef R α β · cval g A (eI β)`
(`eval_rotM_emono`).

## The theorems

* `build_he1`, `build_he2`, `build_hrep`, `build_covers`, `build_repTie` — proved for every `ρ`,
  `bare`.
* `build_tied_iff` — `Tied` is `TiedB bare`, a statement about `bare` alone.
* `build_renTri` — `RenTri` from `RenTensor ρ bare`: the mixing of each component lies in the span of
  `1` and the bare fields of dimension `≤ 4`, and each bare tensor component lies in the span of `1`,
  the mixing components and the other bare fields of dimension `≤ 4`.
* `build_compData` — `CompData (build ρ bare)` from `TiedB bare` and `RenTensor ρ bare`.
* `clayStatementAt_SU_build` — `clayStatementAt_SU_final` at `Cs = build ρ bare`, `e = eI`: the
  composite inputs left are `TiedB bare`, `RenTensor ρ bare`, `CompOS`, `LinkCPre` and the cross
  reading `hX`.

DERIVED (module-wide): `4` the dimension and the dimension of `tr F F`; `0`–`3` the tensor slots; `1`
the unit coefficient and the unit field; `2` the dimension of a field strength; `0` the origin and
the empty sums.
-/

noncomputable section

namespace MassGap.CompositesBuild

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
  MassGap.PreObserver
open scoped Topology Matrix ContDiff

variable {N : ℕ}

/-! ## 1. Finite formal combinations -/

/-- A finite formal combination: a list of coefficients and terms. DERIVED: no numeral. -/
abbrev FC (X : Type) : Type := List (ℝ × X)

namespace FC

variable {X Y Z : Type}

/-- The value of a combination under `f`. DERIVED: `0` the empty sum. -/
def eval {M : Type*} [AddCommMonoid M] [Module ℝ M] (f : X → M) : FC X → M
  | [] => 0
  | p :: L => p.1 • f p.2 + eval f L

/-- Substitution of a combination for each term. DERIVED: no numeral. -/
def bind : FC X → (X → FC Y) → FC Y
  | [], _ => []
  | p :: L, g => (g p.2).map (fun q => (p.1 * q.1, q.2)) ++ bind L g

/-- The expansion of a product of combinations. DERIVED: `1` the empty product. -/
def prodL : List (FC X) → FC (List X)
  | [] => [(1, [])]
  | L :: Ls => bind L fun x => (prodL Ls).map fun q => (q.1, x :: q.2)

section Mod

variable {M M' : Type*} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid M'] [Module ℝ M']

@[simp] theorem eval_nil (f : X → M) : eval f [] = 0 := rfl

@[simp] theorem eval_cons (f : X → M) (p : ℝ × X) (L : FC X) :
    eval f (p :: L) = p.1 • f p.2 + eval f L := rfl

theorem eval_append (f : X → M) (L L' : FC X) : eval f (L ++ L') = eval f L + eval f L' := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih, add_assoc]

theorem eval_map_scale (f : X → M) (c : ℝ) (L : FC X) :
    eval f (L.map fun q => (c * q.1, q.2)) = c • eval f L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih, mul_smul, smul_add]

theorem eval_bind (f : Y → M) (L : FC X) (g : X → FC Y) :
    eval f (bind L g) = eval (fun x => eval f (g x)) L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [bind, eval_append, eval_map_scale, ih]

theorem eval_mapSnd (f : Y → M) (h : X → Y) (L : FC X) :
    eval f (L.map fun q => (q.1, h q.2)) = eval (fun x => f (h x)) L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [ih]

theorem eval_zero (L : FC X) : eval (fun _ => (0 : M)) L = 0 := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [ih]

theorem eval_add (f f' : X → M) (L : FC X) :
    eval (fun x => f x + f' x) L = eval f L + eval f' L := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [eval_cons, ih, smul_add]
    abel

theorem eval_smul (c : ℝ) (f : X → M) (L : FC X) :
    eval (fun x => c • f x) L = c • eval f L := by
  induction L with
  | nil => simp
  | cons p L ih => simp only [eval_cons, ih, smul_add, smul_comm p.1 c]

theorem eval_comm (F : X → Z → M) (L1 : FC X) (L2 : FC Z) :
    eval (fun x => eval (fun z => F x z) L2) L1 = eval (fun z => eval (fun x => F x z) L1) L2 := by
  induction L1 with
  | nil => simp [eval_zero]
  | cons p L ih => simp only [eval_cons, ih, eval_add, eval_smul]

theorem eval_linear (T : M →ₗ[ℝ] M') (f : X → M) (L : FC X) :
    T (eval f L) = eval (fun x => T (f x)) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem eval_eq_sum (f : X → M) (L : FC X) : eval f L = (L.map fun p => p.1 • f p.2).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

end Mod

theorem eval_sub {M : Type*} [AddCommGroup M] [Module ℝ M] (f f' : X → M) (L : FC X) :
    eval (fun x => f x - f' x) L = eval f L - eval f' L := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [eval_cons, ih, smul_sub]
    abel

theorem eval_csmul {M : Type*} [AddCommMonoid M] [Module ℝ M] [Module ℂ M] [SMulCommClass ℝ ℂ M]
    (c : ℂ) (f : X → M) (L : FC X) : c • eval f L = eval (fun x => c • f x) L := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [eval_cons, smul_add, ih]
    rw [smul_comm p.1 c (f p.2)]

section Ring

variable {M : Type*} [Ring M] [Algebra ℝ M]

theorem eval_mul_right (f : X → M) (L : FC X) (y : M) :
    eval f L * y = eval (fun x => f x * y) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [add_mul, ih]

theorem eval_mul_left (f : X → M) (L : FC X) (y : M) :
    y * eval f L = eval (fun x => y * f x) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [mul_add, ih]

/-- **A product of combinations is the combination of the products.** DERIVED: no numeral. -/
theorem eval_prodL (f : X → M) (Ls : List (FC X)) :
    (Ls.map (eval f)).prod = eval (fun xs => (xs.map f).prod) (prodL Ls) := by
  induction Ls with
  | nil => simp [prodL]
  | cons L Ls ih =>
    rw [List.map_cons, List.prod_cons, ih, prodL, eval_bind, eval_mul_right]
    congr 1
    funext x
    rw [eval_mapSnd, eval_mul_left]
    simp

end Ring

section Calc

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem hasFDerivAt_eval (L : FC X) {F : X → V → E} {F' : X → V →L[ℝ] E} {y : V}
    (h : ∀ x, HasFDerivAt (F x) (F' x) y) :
    HasFDerivAt (fun z => eval (fun x => F x z) L) (eval F' L) y := by
  induction L with
  | nil => simpa using hasFDerivAt_const (0 : E) y
  | cons p L ih => exact ((h p.2).const_smul p.1).add ih

theorem eval_clm_apply (F' : X → V →L[ℝ] E) (L : FC X) (v : V) :
    eval F' L v = eval (fun x => F' x v) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem contDiff_eval {n : WithTop ℕ∞} (L : FC X) {F : X → V → E}
    (h : ∀ x, ContDiff ℝ n (F x)) : ContDiff ℝ n (fun z => eval (fun x => F x z) L) := by
  induction L with
  | nil => simpa using (contDiff_const : ContDiff ℝ n fun _ : V => (0 : E))
  | cons p L ih => exact ((h p.2).const_smul p.1).add ih

end Calc

/-- The column `μ` of `R`: `∑_ν R ν μ · ν`. DERIVED: `4` the dimension. -/
def colR (R : Matrix (Fin 4) (Fin 4) ℝ) (μ : Fin 4) : FC (Fin 4) :=
  (List.finRange 4).map fun ν => (R ν μ, ν)

theorem eval_colR {M : Type*} [AddCommMonoid M] [Module ℝ M] (R : Matrix (Fin 4) (Fin 4) ℝ)
    (μ : Fin 4) (f : Fin 4 → M) : eval f (colR R μ) = ∑ ν, R ν μ • f ν := by
  rw [eval_eq_sum, Fin.sum_univ_def, colR, List.map_map]
  rfl

end FC

open FC

/-! ## 2. The commutator and the smoothness of `covDF` -/

/-- The matrix space. DERIVED: no numeral. -/
abbrev Mt (N : ℕ) : Type := Fin N → Fin N → ℂ

theorem mcomm_apply (X Y : Mt N) (i j : Fin N) :
    mcomm X Y i j = ∑ k, X i k * Y k j - ∑ k, Y i k * X k j := by
  simp [mcomm, Matrix.mul_apply]

theorem mcomm_add_left (X X' Y : Mt N) : mcomm (X + X') Y = mcomm X Y + mcomm X' Y := by
  funext i j
  simp only [mcomm_apply, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem mcomm_add_right (X Y Y' : Mt N) : mcomm X (Y + Y') = mcomm X Y + mcomm X Y' := by
  funext i j
  simp only [mcomm_apply, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem mcomm_smul_left (c : ℝ) (X Y : Mt N) : mcomm (c • X) Y = c • mcomm X Y := by
  funext i j
  simp only [mcomm_apply, Pi.smul_apply, Complex.real_smul, mul_sub, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

theorem mcomm_smul_right (c : ℝ) (X Y : Mt N) : mcomm X (c • Y) = c • mcomm X Y := by
  funext i j
  simp only [mcomm_apply, Pi.smul_apply, Complex.real_smul, mul_sub, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

theorem mcomm_zero_left (Y : Mt N) : mcomm 0 Y = 0 := by
  funext i j
  simp [mcomm_apply]

theorem mcomm_zero_right (X : Mt N) : mcomm X 0 = 0 := by
  funext i j
  simp [mcomm_apply]

theorem mcomm_eval_left {X : Type} (f : X → Mt N) (L : FC X) (Y : Mt N) :
    mcomm (eval f L) Y = eval (fun x => mcomm (f x) Y) L := by
  induction L with
  | nil => simp [mcomm_zero_left]
  | cons p L ih => simp [mcomm_add_left, mcomm_smul_left, ih]

theorem mcomm_eval_right {X : Type} (f : X → Mt N) (L : FC X) (Y : Mt N) :
    mcomm Y (eval f L) = eval (fun x => mcomm Y (f x)) L := by
  induction L with
  | nil => simp [mcomm_zero_right]
  | cons p L ih => simp [mcomm_add_right, mcomm_smul_right, ih]

theorem contDiff_mcomm {n : WithTop ℕ∞} {f h : (Fin 4 → ℝ) → Mt N} (hf : ContDiff ℝ n f)
    (hh : ContDiff ℝ n h) : ContDiff ℝ n (fun x => mcomm (f x) (h x)) := by
  have hf' : ∀ i k, ContDiff ℝ n (fun x => f x i k) := fun i k =>
    contDiff_pi.1 (contDiff_pi.1 hf i) k
  have hh' : ∀ i k, ContDiff ℝ n (fun x => h x i k) := fun i k =>
    contDiff_pi.1 (contDiff_pi.1 hh i) k
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun x => mcomm (f x) (h x) i j)
      = fun x => ∑ k, f x i k * h x k j - ∑ k, h x i k * f x k j :=
    funext fun x => mcomm_apply _ _ i j
  rw [e]
  exact (ContDiff.sum fun k _ => (hf' i k).mul (hh' k j)).sub
    (ContDiff.sum fun k _ => (hh' i k).mul (hf' k j))

/-- **`covDF g A ρ σ ds` is smooth** for a smooth potential. DERIVED: no numeral. -/
theorem contDiff_covDF {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (ρ σ : Fin 4) :
    ∀ ds : List (Fin 4), ContDiff ℝ ∞ (covDF g A ρ σ ds)
  | [] => by
    have hc : ∀ ν, ContDiff ℝ ∞ (fun y => A y ν) := fun ν => contDiff_pi.1 hA ν
    have hd : ∀ ν μ, ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => A y ν) x (dir μ)) :=
      fun ν μ => (contDiff_infty_iff_fderiv.1 (hc ν)).2.clm_apply contDiff_const
    exact ((hd σ ρ).sub (hd ρ σ)).add ((contDiff_mcomm (hc ρ) (hc σ)).const_smul _)
  | μ :: ds => by
    have hc : ContDiff ℝ ∞ (fun y => A y μ) := contDiff_pi.1 hA μ
    have ih := contDiff_covDF hA g ρ σ ds
    exact ((contDiff_infty_iff_fderiv.1 ih).2.clm_apply contDiff_const).add
      ((contDiff_mcomm hc ih).const_smul _)

/-! ## 3. The chain rule through `R *ᵥ ·` -/

/-- `R e_μ = ∑_ν R ν μ e_ν`. DERIVED: `4` the dimension. -/
theorem mulVec_dir (R : Matrix (Fin 4) (Fin 4) ℝ) (μ : Fin 4) :
    R *ᵥ dir μ = ∑ ν, R ν μ • dir ν := by
  ext i
  simp [dir, Finset.sum_apply, Pi.single_apply]

/-- `R *ᵥ ·` as a continuous linear map. DERIVED: `4` the dimension. -/
def rotL4 (R : Matrix (Fin 4) (Fin 4) ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)

theorem rotL4_apply (R : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : rotL4 R v = R *ᵥ v := rfl

/-- **The derivative of a combination composed with `R`**, in the direction `e_μ`.

DERIVED: `4` the dimension. -/
theorem fderiv_rot_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Type}
    (R : Matrix (Fin 4) (Fin 4) ℝ) (L : FC X) (F : X → (Fin 4 → ℝ) → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (x : Fin 4 → ℝ) (μ : Fin 4) :
    fderiv ℝ (fun y => eval (fun a => F a (R *ᵥ y)) L) x (dir μ)
      = eval (fun ν => eval (fun a => fderiv ℝ (F a) (R *ᵥ x) (dir ν)) L) (colR R μ) := by
  have hG : HasFDerivAt (fun z => eval (fun a => F a z) L)
      (eval (fun a => fderiv ℝ (F a) (R *ᵥ x)) L) (R *ᵥ x) :=
    hasFDerivAt_eval L fun a => (hF a _).hasFDerivAt
  have hc : HasFDerivAt (fun y => eval (fun a => F a (R *ᵥ y)) L)
      ((eval (fun a => fderiv ℝ (F a) (R *ᵥ x)) L).comp (rotL4 R)) x :=
    hG.comp x (rotL4 R).hasFDerivAt
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, rotL4_apply, mulVec_dir, map_sum, eval_colR]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, eval_clm_apply]

theorem rotPot_eq_eval (R : Matrix (Fin 4) (Fin 4) ℝ) (A : GPot N) (y : Fin 4 → ℝ) (μ : Fin 4) :
    rotPot R A y μ = eval (fun ν => A (R *ᵥ y) ν) (colR R μ) := by
  rw [eval_colR]
  rfl

/-! ## 4. The covariance of `covDF` -/

/-- **The rotation of a letter** `D_{ds} F_{ρσ}`: one factor `R ν μ` per index.

DERIVED: `4` the dimension. -/
def rotL (R : Matrix (Fin 4) (Fin 4) ℝ) (ρ σ : Fin 4) : List (Fin 4) → FC Letter
  | [] => FC.bind (colR R ρ) fun ρ' => (colR R σ).map fun q => (q.1, ([], ρ', q.2))
  | μ :: ds => FC.bind (colR R μ) fun ν => (rotL R ρ σ ds).map fun q => (q.1, (ν :: q.2.1, q.2.2))

/-- **`covDF` of the rotated potential**: for a smooth `A`,
`covDF g (rotPot R A) ρ σ ds x = ∑_{(c, l) ∈ rotL R ρ σ ds} c • covDF g A l (R x)`.

DERIVED: `4` the dimension. -/
theorem covDF_rotPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (R : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (ρ σ : Fin 4) : ∀ ds : List (Fin 4),
    covDF g (rotPot R A) ρ σ ds
      = fun x => eval (fun l : Letter => covDF g A l.2.1 l.2.2 l.1 (R *ᵥ x)) (rotL R ρ σ ds)
  | [] => by
    funext x
    have hc : ∀ ν, Differentiable ℝ (fun y => A y ν) := fun ν =>
      (contDiff_pi.1 hA ν).differentiable (by simp)
    have hA' : ∀ μ, (fun y => rotPot R A y μ)
        = fun y => eval (fun ν => (fun z => A z ν) (R *ᵥ y)) (colR R μ) :=
      fun μ => funext fun y => rotPot_eq_eval R A y μ
    have hder : ∀ μ ρ0, fderiv ℝ (fun y => rotPot R A y μ) x (dir ρ0)
        = eval (fun ρ' => eval (fun ν => fderiv ℝ (fun z => A z ν) (R *ᵥ x) (dir ρ'))
            (colR R μ)) (colR R ρ0) := by
      intro μ ρ0
      rw [hA' μ]
      exact fderiv_rot_eval R (colR R μ) (fun ν z => A z ν) hc x ρ0
    show fderiv ℝ (fun y => rotPot R A y σ) x (dir ρ) - fderiv ℝ (fun y => rotPot R A y ρ) x (dir σ)
        + (Complex.I * (g : ℂ)) • mcomm (rotPot R A x ρ) (rotPot R A x σ) = _
    rw [hder σ ρ, hder ρ σ, rotPot_eq_eval R A x ρ, rotPot_eq_eval R A x σ, mcomm_eval_left,
      eval_csmul]
    simp only [mcomm_eval_right, eval_csmul]
    simp only [rotL, eval_bind]
    show _ = eval (fun ρ' => eval (fun σ' => fderiv ℝ (fun y => A y σ') (R *ᵥ x) (dir ρ')
        - fderiv ℝ (fun y => A y ρ') (R *ᵥ x) (dir σ')
        + (Complex.I * (g : ℂ)) • mcomm (A (R *ᵥ x) ρ') (A (R *ᵥ x) σ')) (colR R σ)) (colR R ρ)
    simp only [eval_add, eval_sub]
    rw [eval_comm (fun σ' ρ' => fderiv ℝ (fun z => A z ρ') (R *ᵥ x) (dir σ')) (colR R σ)
      (colR R ρ)]
  | μ :: ds => by
    funext x
    have ih := covDF_rotPot hA R g ρ σ ds
    have hcd : ∀ l : Letter, Differentiable ℝ (covDF g A l.2.1 l.2.2 l.1) := fun l =>
      (contDiff_covDF hA g l.2.1 l.2.2 l.1).differentiable (by simp)
    show fderiv ℝ (covDF g (rotPot R A) ρ σ ds) x (dir μ)
        + (Complex.I * (g : ℂ)) • mcomm (rotPot R A x μ) (covDF g (rotPot R A) ρ σ ds x) = _
    rw [ih, fderiv_rot_eval R (rotL R ρ σ ds) (fun l z => covDF g A l.2.1 l.2.2 l.1 z) hcd x μ,
      rotPot_eq_eval R A x μ, mcomm_eval_left, eval_csmul]
    simp only [mcomm_eval_right, eval_csmul]
    rw [← eval_add]
    simp only [← eval_add]
    simp only [rotL, eval_bind]
    congr 1
    funext ν
    rw [eval_mapSnd _ (fun l : Letter => ((ν :: l.1, l.2.1, l.2.2) : Letter))]
    rfl

/-! ## 5. Traces, products and monomials -/

theorem of_eval {X : Type} (f : X → Mt N) (L : FC X) :
    Matrix.of (eval f L) = eval (fun x => Matrix.of (f x)) L := by
  induction L with
  | nil => rfl
  | cons p L ih => rw [eval_cons, eval_cons, ← ih]; rfl

theorem trace_eval {X : Type} (f : X → Matrix (Fin N) (Fin N) ℂ) (L : FC X) :
    Matrix.trace (eval f L) = eval (fun x => Matrix.trace (f x)) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [Matrix.trace_add, Matrix.trace_smul, ih]

theorem re_eval {X : Type} (f : X → ℂ) (L : FC X) : (eval f L).re = eval (fun x => (f x).re) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

theorem im_eval {X : Type} (f : X → ℂ) (L : FC X) : (eval f L).im = eval (fun x => (f x).im) L := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

/-- The rotation of a word: the product of the rotations of its letters. DERIVED: no numeral. -/
def rotW (R : Matrix (Fin 4) (Fin 4) ℝ) (W : Word) : FC Word :=
  prodL (W.map fun l => rotL R l.2.1 l.2.2 l.1)

/-- **`tr W` of the rotated potential** at the origin. DERIVED: `0` the origin. -/
theorem wordTr_rotPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (R : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (W : Word) : wordTr g (rotPot R A) W = eval (wordTr g A) (rotW R W) := by
  have hl : ∀ l : Letter, Matrix.of (covDF g (rotPot R A) l.2.1 l.2.2 l.1 0)
      = eval (fun l' : Letter => Matrix.of (covDF g A l'.2.1 l'.2.2 l'.1 0))
          (rotL R l.2.1 l.2.2 l.1) := by
    intro l
    rw [covDF_rotPot hA R g, of_eval]
    simp only [Matrix.mulVec_zero]
  unfold wordTr rotW
  rw [List.map_congr_left (fun l _ => hl l)]
  have hm : (W.map fun l : Letter => eval (fun l' : Letter => Matrix.of (covDF g A l'.2.1 l'.2.2 l'.1 0))
        (rotL R l.2.1 l.2.2 l.1))
      = (W.map fun l : Letter => rotL R l.2.1 l.2.2 l.1).map
          (eval fun l' : Letter => Matrix.of (covDF g A l'.2.1 l'.2.2 l'.1 0)) := by
    rw [List.map_map]
    rfl
  rw [hm, eval_prodL, trace_eval]

/-- The value of a pair `Re/Im tr W`. DERIVED: no numeral. -/
def pval (g : ℝ) (A : GPot N) (p : Word × Bool) : ℝ :=
  if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im

/-- The rotation of a pair. DERIVED: no numeral. -/
def rotP (R : Matrix (Fin 4) (Fin 4) ℝ) (p : Word × Bool) : FC (Word × Bool) :=
  (rotW R p.1).map fun q => (q.1, (q.2, p.2))

/-- **The rotation of a monomial**: the product of the rotations of its pairs.

DERIVED: no numeral. -/
def rotM (R : Matrix (Fin 4) (Fin 4) ℝ) (m : CMono) : FC CMono := prodL (m.map (rotP R))

theorem pval_rotPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (R : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (p : Word × Bool) : pval g (rotPot R A) p = eval (pval g A) (rotP R p) := by
  obtain ⟨W, b⟩ := p
  unfold rotP
  rw [eval_mapSnd (pval g A) (fun w => (w, b))]
  cases b
  · simp only [pval, wordTr_rotPot hA, im_eval]
    rfl
  · simp only [pval, wordTr_rotPot hA, re_eval]
    rfl

/-- **The classical value of a rotated monomial** is the combination `rotM R m` of classical
values, for a smooth `A`.

DERIVED: no numeral. -/
theorem cval_rotPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (R : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ)
    (m : CMono) : cval g (rotPot R A) m = eval (cval g A) (rotM R m) := by
  have e : ∀ B : GPot N, cval g B = fun m' => (m'.map (pval g B)).prod := fun B => rfl
  rw [e, e]
  show (m.map (pval g (rotPot R A))).prod = _
  rw [List.map_congr_left (fun p _ => pval_rotPot hA R g p)]
  have hm : (m.map fun p => eval (pval g A) (rotP R p)) = (m.map (rotP R)).map (eval (pval g A)) := by
    rw [List.map_map]
    rfl
  rw [hm, eval_prodL]
  rfl

/-! ## 6. The shape of the expansion -/

variable {X' Y' : Type}

theorem mem_bind {L : FC X'} {g : X' → FC Y'} {q : ℝ × Y'} (h : q ∈ FC.bind L g) :
    ∃ p ∈ L, ∃ r ∈ g p.2, q = (p.1 * r.1, r.2) := by
  induction L with
  | nil => simp [FC.bind] at h
  | cons p L ih =>
    simp only [FC.bind, List.mem_append, List.mem_map] at h
    rcases h with ⟨r, hr, rfl⟩ | h
    · exact ⟨p, List.mem_cons_self .., r, hr, rfl⟩
    · obtain ⟨p', hp', r, hr, e⟩ := ih h
      exact ⟨p', List.mem_cons_of_mem _ hp', r, hr, e⟩

theorem mem_prodL {Ls : List (FC X')} {q : ℝ × List X'} (h : q ∈ prodL Ls) :
    List.Forall₂ (fun x L => ∃ c, (c, x) ∈ L) q.2 Ls := by
  induction Ls generalizing q with
  | nil =>
    simp only [prodL, List.mem_singleton] at h
    subst h
    exact List.Forall₂.nil
  | cons L Ls ih =>
    obtain ⟨p, hp, r, hr, rfl⟩ := mem_bind h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact List.Forall₂.cons ⟨p.1, hp⟩ (ih hs)

theorem forall₂_exists {α β : Type} {Rel : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ Rel l1 l2) {x : α} (hx : x ∈ l1) : ∃ y ∈ l2, Rel x y := by
  induction h with
  | nil => simp at hx
  | cons hab _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem rotP_length {R : Matrix (Fin 4) (Fin 4) ℝ} {p : Word × Bool} {c : ℝ} {p' : Word × Bool}
    (h : (c, p') ∈ rotP R p) : p'.1.length = p.1.length := by
  obtain ⟨q, hq, e⟩ := List.mem_map.1 h
  have hf := mem_prodL hq
  have hl := hf.length_eq
  simp only [Prod.mk.injEq] at e
  rw [← e.2]
  simpa using hl

/-- **The admissible monomials**: non-empty, with non-empty words. DERIVED: no numeral. -/
def AdmM (m : CMono) : Prop := m ≠ [] ∧ ∀ p ∈ m, p.1 ≠ []

/-- **Every monomial of the expansion of an admissible monomial is admissible.**

DERIVED: no numeral. -/
theorem rotM_shape {R : Matrix (Fin 4) (Fin 4) ℝ} {m : CMono} (hm : AdmM m) {q : ℝ × CMono}
    (hq : q ∈ rotM R m) : AdmM q.2 := by
  have hf := mem_prodL hq
  refine ⟨?_, fun p' hp' => ?_⟩
  · intro h0
    have hl := hf.length_eq
    rw [h0, List.length_map] at hl
    exact hm.1 (List.length_eq_zero_iff.1 hl.symm)
  · obtain ⟨L, hL, c, hc⟩ := forall₂_exists hf hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hL
    have := rotP_length hc
    intro h0
    rw [h0, List.length_nil] at this
    exact hm.2 p hp (List.length_eq_zero_iff.1 this.symm)

/-! ## 7. The tensor monomials -/

/-- `Re tr F_{α₀α₁} F_{α₂α₃}`. DERIVED: `0`–`3` the slots. -/
def emono (α : Idx4) : CMono := [([([], α 0, α 1), ([], α 2, α 3)], true)]

/-- Reading back the tensor index of `emono`. DERIVED: `0`–`3` the slots. -/
def dec : CMono → Option Idx4
  | [([([], a, b), ([], c, d)], true)] => some ![a, b, c, d]
  | _ => none

theorem dec_emono (α : Idx4) : dec (emono α) = some α := by
  simp only [emono, dec, Option.some.injEq]
  funext i
  fin_cases i <;> rfl

theorem eq_emono_of_dec {m : CMono} {α : Idx4} (h : dec m = some α) : m = emono α := by
  unfold dec at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact absurd h (by simp)

theorem sum_idx4 {M : Type*} [AddCommMonoid M] (f : Idx4 → M) :
    ∑ β, f β = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
  rw [← (Fin.consEquiv fun _ : Fin 4 => Fin 4).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ : Fin 3 => Fin 4).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (Fin.consEquiv fun _ : Fin 2 => Fin 4).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← (Fin.consEquiv fun _ : Fin 1 => Fin 4).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  exact congrArg f (by ext i; fin_cases i <;> rfl)

/-- **The rotation of a field-strength letter**: `eval f (rotL R a b [])` is
`∑_{ρ'σ'} R ρ' a R σ' b · f ([], ρ', σ')`. DERIVED: `4` the dimension. -/
theorem eval_rotL_nil {M : Type*} [AddCommMonoid M] [Module ℝ M] (R : Matrix (Fin 4) (Fin 4) ℝ)
    (a b : Fin 4) (f : Letter → M) :
    eval f (rotL R a b []) = ∑ ρ', R ρ' a • ∑ σ', R σ' b • f ([], ρ', σ') := by
  simp only [rotL, eval_bind, eval_colR]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [eval_mapSnd f (fun σ' => (([], ν, σ') : Letter)), eval_colR]

theorem eval_prodL_one {M : Type*} [AddCommMonoid M] [Module ℝ M] {X : Type} (F : List X → M)
    (L : FC X) : eval F (prodL [L]) = eval (fun x => F [x]) L := by
  simp only [prodL, eval_bind, eval_mapSnd, eval_cons, eval_nil, one_smul, add_zero]

theorem eval_prodL_two {M : Type*} [AddCommMonoid M] [Module ℝ M] {X : Type} (F : List X → M)
    (L1 L2 : FC X) : eval F (prodL [L1, L2]) = eval (fun x => eval (fun y => F [x, y]) L2) L1 := by
  simp only [prodL, eval_bind, eval_mapSnd, eval_cons, eval_nil, one_smul, add_zero]

theorem tcoef_cons4 (R : Matrix (Fin 4) (Fin 4) ℝ) (α : Idx4) (a b c d : Fin 4) :
    tcoef R α ![a, b, c, d] = R a (α 0) * R b (α 1) * R c (α 2) * R d (α 3) := by
  simp only [tcoef, Fin.prod_univ_four]
  rfl

/-- **The expansion at a tensor monomial** is `∑_β tcoef R α β · cval g A (emono β)`.

DERIVED: `0`–`3` the slots. -/
theorem eval_rotM_emono (R : Matrix (Fin 4) (Fin 4) ℝ) (g : ℝ) (A : GPot N) (α : Idx4) :
    eval (cval g A) (rotM R (emono α)) = ∑ β, tcoef R α β * cval g A (emono β) := by
  have e1 : rotM R (emono α) = prodL [rotP R ([([], α 0, α 1), ([], α 2, α 3)], true)] := rfl
  have e2 : rotW R [([], α 0, α 1), ([], α 2, α 3)]
      = prodL [rotL R (α 0) (α 1) [], rotL R (α 2) (α 3) []] := rfl
  rw [e1, eval_prodL_one]
  unfold rotP
  rw [eval_mapSnd (fun x => cval g A [x]) (fun w => (w, true))]
  rw [e2, eval_prodL_two, eval_rotL_nil]
  simp only [eval_rotL_nil, sum_idx4, tcoef_cons4, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  show _ = _ * cval g A [([([], a, b), ([], c, d)], true)]
  ring

/-! ## 8. Linear combinations of local fields -/

/-- **The local gauge-invariant observables form a real subspace.** DERIVED: `0` the zero field. -/
def lfSub (N : ℕ) : Submodule ℝ C(Cfg N, ℝ) where
  carrier := {O | (∃ S : Finset ILink, IsLocalOn S (O : Cfg N → ℝ))
    ∧ GaugeInvariantAlgebra.IsIGaugeInvariant O}
  zero_mem' := ⟨⟨∅, fun _ _ _ => rfl⟩, fun _ _ => rfl⟩
  add_mem' := by
    classical
    rintro O O' ⟨⟨S, hS⟩, hO⟩ ⟨⟨S', hS'⟩, hO'⟩
    refine ⟨⟨S ∪ S', fun U V h => ?_⟩, fun g U => ?_⟩
    · show O U + O' U = O V + O' V
      rw [hS U V (fun l hl => h l (Finset.mem_union_left _ hl)),
        hS' U V (fun l hl => h l (Finset.mem_union_right _ hl))]
    · show O _ + O' _ = O U + O' U
      rw [hO g U, hO' g U]
  smul_mem' := by
    rintro c O ⟨⟨S, hS⟩, hO⟩
    refine ⟨⟨S, fun U V h => ?_⟩, fun g U => ?_⟩
    · show c * O U = c * O V
      rw [hS U V h]
    · show c * O _ = c * O U
      rw [hO g U]

theorem mem_lfSub (O : LField (MassGap.SUN.SU N)) : O.1 ∈ lfSub N := O.2

/-- **The mixing component `∑_b M k α b • op b`** as a local field. DERIVED: no numeral. -/
def mixF (ρ : RenormMix N) (k : ℕ) (α : Idx4) : LField (MassGap.SUN.SU N) :=
  ⟨∑ b, ρ.M k α b • (ρ.op b).1,
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (mem_lfSub (ρ.op b))⟩

/-! ## 9. The family -/

/-- The index type: the admissible monomials. DERIVED: no numeral. -/
abbrev Ix0 : Type := {m : CMono // AdmM m}

/-- The tensor index. DERIVED: no numeral. -/
def eI (α : Idx4) : Ix0 := ⟨emono α, by simp [emono], by simp [emono]⟩

/-- The renormalised field. DERIVED: no numeral. -/
def renF (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (k : ℕ) (i : Ix0) :
    LField (MassGap.SUN.SU N) :=
  match dec i.1 with
  | some α => mixF ρ k α
  | none => bare i

open Classical in
/-- The general rotation representation: the expansion `rotM`, on `Ix0`. DERIVED: no numeral. -/
def repGen (R : Matrix (Fin 4) (Fin 4) ℝ) (i : Ix0) : Ix0 →₀ ℝ :=
  ((rotM R i.1).map fun q => if h : AdmM q.2 then Finsupp.single (⟨q.2, h⟩ : Ix0) q.1 else 0).sum

/-- The rotation representation. DERIVED: `1` the unit coefficient. -/
def repF (R : Matrix (Fin 4) (Fin 4) ℝ) (i : Ix0) : Ix0 →₀ ℝ :=
  match dec i.1 with
  | some α => ∑ β : Idx4, tcoef R α β • Finsupp.single (eI β) (1 : ℝ)
  | none => repGen R i

/-- **The family of all composites** at the mixing `ρ` and the bare fields `bare`.

DERIVED: no numeral. -/
def build (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) : Composites N where
  Ix := Ix0
  cl := Subtype.val
  bare := bare
  ren := renF ρ bare
  rep := repF

variable (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N))

theorem renF_of_some {i : Ix0} {α : Idx4} (h : dec i.1 = some α) (k : ℕ) :
    renF ρ bare k i = mixF ρ k α := by
  simp only [renF, h]

theorem renF_of_none {i : Ix0} (h : dec i.1 = none) (k : ℕ) : renF ρ bare k i = bare i := by
  simp only [renF, h]

theorem eI_of_dec {i : Ix0} {α : Idx4} (h : dec i.1 = some α) : i = eI α :=
  Subtype.ext (eq_emono_of_dec h)

/-- `he1`. DERIVED: `0`–`3` the slots. -/
theorem build_he1 (α : Idx4) :
    (build ρ bare).cl (eI α) = [([([], α 0, α 1), ([], α 2, α 3)], true)] := rfl

/-- `he2`. DERIVED: no numeral. -/
theorem build_he2 (k : ℕ) (α : Idx4) :
    ((build ρ bare).ren k (eI α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1 := by
  show (renF ρ bare k (eI α)).1 = _
  rw [renF_of_some ρ bare (dec_emono α)]
  rfl

/-- `hrep`. DERIVED: `1` the unit coefficient. -/
theorem build_hrep (R : Matrix (Fin 4) (Fin 4) ℝ) (α : Idx4) :
    (build ρ bare).rep R (eI α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (eI β) (1 : ℝ) := by
  show repF R (eI α) = _
  simp only [repF, eI, dec_emono]

/-- `Covers`. DERIVED: no numeral. -/
theorem build_covers : (build ρ bare).Covers := fun m h1 h2 => ⟨⟨m, h1, h2⟩, rfl⟩

theorem sum_support_eq_lc (c : Ix0 →₀ ℝ) (v : Ix0 → ℝ) :
    ∑ j ∈ c.support, c j * v j = Finsupp.linearCombination ℝ v c := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rfl

/-- **`RepTie`** on `build ρ bare`. DERIVED: no numeral. -/
theorem build_repTie : (build ρ bare).RepTie := by
  intro R _ i A hA g
  change Ix0 at i
  have hA' : ContDiff ℝ ∞ A := contDiff_infty.2 hA.1
  show cval g (rotPot R A) i.1 = ∑ j ∈ (repF R i).support, repF R i j * cval g A j.1
  rw [sum_support_eq_lc (repF R i) (fun j => cval g A j.1), cval_rotPot hA']
  cases h : dec i.1 with
  | some α =>
    have hi := eq_emono_of_dec h
    simp only [repF, h, map_sum, map_smul, Finsupp.linearCombination_single, smul_eq_mul]
    rw [hi, eval_rotM_emono]
    simp only [one_mul]
    rfl
  | none =>
    simp only [repF, h, repGen]
    rw [map_list_sum, List.map_map, eval_eq_sum]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    have hs := rotM_shape i.2 hq
    simp only [Function.comp_apply, dif_pos hs, Finsupp.linearCombination_single, smul_eq_mul]

/-! ## 10. `Tied` and `RenTri` -/

/-- **The bare fields discretise their monomials**: `Tied` of `build ρ bare`, a statement about
`bare` alone.

DERIVED: no numeral. -/
def TiedB (bare : Ix0 → LField (MassGap.SUN.SU N)) : Prop :=
  ∀ i : Ix0, ClassicalLead (bare i).1 (cdim i.1) (fun A g => g ^ cnF i.1 * cval g A i.1)

theorem build_tied_iff : (build ρ bare).Tied ↔ TiedB bare := Iff.rfl

/-- The span of `1` and the bare fields of dimension `≤ d`. DERIVED: `1` the unit field. -/
def bareSpan (d : ℕ) : Submodule ℝ C(Cfg N, ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range fun i : {i : Ix0 // cdim i.1 ≤ d} => (bare i.1).1))

/-- The span of `1`, the mixing components at step `k`, and the bare fields of dimension `≤ 4`
outside the tensor indices.

DERIVED: `1` the unit field; `4` the dimension of `tr F F`. -/
def mixSpan (k : ℕ) : Submodule ℝ C(Cfg N, ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range (fun β : Idx4 => (mixF ρ k β).1)
    ∪ Set.range fun i : {i : Ix0 // cdim i.1 ≤ 4 ∧ dec i.1 = none} => (bare i.1).1))

/-- **The renormalisation of the tensor block is triangular and invertible**: at every step the
mixing components lie in the span of `1` and the bare fields of dimension `≤ 4`, and each bare
tensor component lies in `mixSpan`.

DERIVED: `4` the dimension of `tr F F`. -/
def RenTensor : Prop :=
  ∀ k α, (mixF ρ k α).1 ∈ bareSpan bare 4 ∧ (bare (eI α)).1 ∈ mixSpan ρ bare k

theorem cdim_emono (α : Idx4) : cdim (emono α) = 4 := rfl

/-- **`RenTri`** from `RenTensor`. DERIVED: `4` the dimension of `tr F F`. -/
theorem build_renTri (h : RenTensor ρ bare) : (build ρ bare).RenTri := by
  refine ⟨fun k i => ?_, fun k d => ?_⟩
  · show (renF ρ bare k i).1 ∈ bareSpan bare (cdim i.1)
    cases hd : dec i.1 with
    | some α =>
      rw [renF_of_some ρ bare hd, eI_of_dec hd]
      exact (h k α).1
    | none =>
      rw [renF_of_none ρ bare hd]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨i, le_rfl⟩, rfl⟩)
  · show bareSpan bare d ≤ Submodule.span ℝ (insert 1 (Set.range fun i :
      {i : Ix0 // cdim i.1 ≤ d} => (renF ρ bare k i.1).1))
    set T := Submodule.span ℝ (insert 1 (Set.range fun i :
      {i : Ix0 // cdim i.1 ≤ d} => (renF ρ bare k i.1).1)) with hT
    have h1 : (1 : C(Cfg N, ℝ)) ∈ T := Submodule.subset_span (Set.mem_insert _ _)
    have hren : ∀ i : Ix0, cdim i.1 ≤ d → (renF ρ bare k i).1 ∈ T := fun i hi =>
      Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨i, hi⟩, rfl⟩)
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | ⟨⟨i, hi⟩, rfl⟩)
    · exact h1
    · cases hd : dec i.1 with
      | none =>
        have := hren i hi
        rwa [renF_of_none ρ bare hd] at this
      | some α =>
        have h4 : 4 ≤ d := by rw [eq_emono_of_dec hd, cdim_emono] at hi; exact hi
        have hi' := eI_of_dec hd
        subst hi'
        refine (Submodule.span_le.2 ?_) (h k α).2
        rintro _ (rfl | ⟨β, rfl⟩ | ⟨⟨j, hj, hjd⟩, rfl⟩)
        · exact h1
        · have := hren (eI β) (by rw [show (eI β).1 = emono β from rfl, cdim_emono]; exact h4)
          rwa [renF_of_some ρ bare (dec_emono β)] at this
        · have := hren j (hj.trans h4)
          rwa [renF_of_none ρ bare hjd] at this

/-- **`RenTri` on the built family is `RenTensor`.** DERIVED: `4` the tensor dimension. -/
theorem build_renTri_iff : (build ρ bare).RenTri ↔ RenTensor ρ bare := by
  refine ⟨fun h k α => ⟨?_, ?_⟩, build_renTri ρ bare⟩
  · have := h.1 k (eI α)
    have e : ((build ρ bare).ren k (eI α)).1 = (mixF ρ k α).1 := by
      show (renF ρ bare k (eI α)).1 = _
      rw [renF_of_some ρ bare (dec_emono α)]
    rw [e] at this
    exact this
  · have hb : (bare (eI α)).1 ∈ (build ρ bare).lowSpan (build ρ bare).bare 4 :=
      Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨eI α, le_of_eq (cdim_emono α)⟩, rfl⟩)
    refine (Submodule.span_le.2 ?_) (h.2 k 4 hb)
    rintro _ (rfl | ⟨⟨i, hi⟩, rfl⟩)
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · show (renF ρ bare k i).1 ∈ _
      cases hd : dec i.1 with
      | some β =>
        rw [renF_of_some ρ bare hd]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Or.inl ⟨β, rfl⟩))
      | none =>
        rw [renF_of_none ρ bare hd]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Or.inr ⟨⟨i, hi, hd⟩, rfl⟩))

/-- **`CompData (build ρ bare)`** from `TiedB bare` and `RenTensor ρ bare`.

DERIVED: no numeral. -/
theorem build_compData (hT : TiedB bare) (hR : RenTensor ρ bare) : CompData (build ρ bare) :=
  ⟨hT, build_covers ρ bare, build_renTri ρ bare hR, build_repTie ρ bare⟩

/-! ## 11. The capstone at `build ρ bare` -/

/-- **`ClaySUFinal.clayStatementAt_SU_final` at `Cs = build ρ bare`, `e = eI`.** `he1`, `he2`,
`hrep`, `Covers` and `RepTie` are proved (`build_he1`, `build_he2`, `build_hrep`, `build_covers`,
`build_repTie`); `Tied` is `hT : TiedB bare` and `RenTri` comes from `hR : RenTensor ρ bare`. The
composite inputs left: `hT`, `hR`, `hCO : CompOS`, `hLC : LinkCPre`, `hX`.

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`. -/
theorem clayStatementAt_SU_build (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (bare : Ix0 → LField (MassGap.SUN.SU N)) (hT : TiedB bare) (hR : RenTensor ρ bare)
    (hCO : CompOS (ne_zero_of_two_le hN2) (build ρ bare))
    (wC : TSepG (build ρ bare).Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) (build ρ bare) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  ClaySUFinal.clayStatementAt_SU_final hN2 W ht hU hphys hfar ρ hRie hTie hCT G hK hAF hNG hWard
    (build ρ bare) wC eI (build_he1 ρ bare) (build_he2 ρ bare) (build_compData ρ bare hT hR) hCO
    (fun R _ α => build_hrep ρ bare R α) hLC hX

end MassGap.CompositesBuild

end

#print axioms MassGap.CompositesBuild.covDF_rotPot
#print axioms MassGap.CompositesBuild.cval_rotPot
#print axioms MassGap.CompositesBuild.rotM_shape
#print axioms MassGap.CompositesBuild.eval_rotM_emono
#print axioms MassGap.CompositesBuild.build_he1
#print axioms MassGap.CompositesBuild.build_he2
#print axioms MassGap.CompositesBuild.build_hrep
#print axioms MassGap.CompositesBuild.build_covers
#print axioms MassGap.CompositesBuild.build_repTie
#print axioms MassGap.CompositesBuild.build_renTri
#print axioms MassGap.CompositesBuild.build_renTri_iff
#print axioms MassGap.CompositesBuild.build_compData
#print axioms MassGap.CompositesBuild.clayStatementAt_SU_build
