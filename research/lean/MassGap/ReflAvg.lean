import Mathlib
import MassGap.JointRP
import MassGap.NonGaussLink

/-!
# MassGap.ReflAvg — reflection-averaged composites, and the SU capstone without `hJ`

`JointRP.not_reflCovLat` shows that the bare composites of the SU capstone are not reflection
covariant on the lattice. This module averages every bare field over the reflection `θ = ireflObs 0 0`
of the plane `x₀ = 0`, proves that the averaged composites are reflection covariant on the lattice at
every step, proves that they discretise the same classical monomials, and so gives the SU capstone at
the averaged composites without the input `hJ : JointRPK` of `CompositeLink.clayStatementAt_SU_link`;
its other composite inputs are read at the averaged composites.

## 1. The average

`reflAvg n O = ½ (O + (−1)ⁿ θO)`, a local gauge-invariant field. `reflAvg_refl`:
`θ (reflAvg n O) = (−1)ⁿ reflAvg n O` (`ireflConf_involutive`).

## 2. The classical lead of a reflected monomial

`classicalLead_refl_bareF`: for every admissible monomial `m`, `θ (bareF m)` has classical lead
`(−1)^{ctau τ m} g^{cnF m} cval g A m` at dimension `cdim m`. The steps:

* on a classical configuration `U` of `A`, `θU` reads the reflected potential
  `A^R_μ(y) = s_μ A_μ(R y)` (`reflPot`, `s_μ = −1` at `μ = τ`), but its `τ`-links read `A^R` at
  their far endpoint (`classCfgO_refl`). `IsClassCfgO` is the classical configuration with a
  per-direction offset of the evaluation point; `ord_baseO`, `ord_stepO`, `word_ordO`, `mono_ordO`
  are `ClassicalLimit.ord_base`, `ord_step`, `word_ord`, `mono_ord` at the offset links. The offset
  vanishes at `a = 0`, so the leading term is that of `A^R`;
* `covDF_reflPot`: `D_{ds}F_{ρσ}[A^R](y) = s_ρ s_σ ∏ s_{ds} · D_{ds}F_{ρσ}[A](R y)` (chain rule), so
  `cval g A^R m = (−1)^{ctau τ m} cval g A m` (`cval_reflPot`).

## 3. The averaged composites

* `bareR m = reflAvg (ctau 0 m) (bareF m)`, `fR N δ = bareR (emono δ)`, `bR N i = bareR i.1`,
  `CbR N z = build (rhoD (fR N) z) (bareD (fR N) (bR N))`.
* `reflCovLat_CbR`: `JointRP.ReflCovLat (CbR N z) 0`. Off the tensor indices the renormalised field
  is `bareR`, covariant by `reflAvg_refl`. At `eI α` it is `Ecomb (fR N) z_k α`: the observer's field
  is reflection invariant (`sym_hypScalar`), `t_α ≠ 0` only at an even number of indices `0`
  (`tv_parity`, from `Tl_tv` at `A = diag(−1, 1, 1, 1)`), `Pm c α δ ≠ 0` only at equal parities
  (`Pm_parity`, from `Pm_Tm`), and the constant shifts of the channel fields cancel because every
  row of `Pm c` sums to `0` (`Pm_rowsum`: `P c` factors through `Rl`, which kills the constant
  tensor) and `fR(1) = 0`.
* `tiedB_R`: `TiedB (bareD (fR N) (bR N))`, from `classicalLead_obs` and the lead of `bareR`
  (`lead_bareR`), as in `ClayData.tiedB_bareD_of_obs`.

## 4. The capstone

`linkCPre_of_kernelsF`, `jointRPK_of_reflLimF`, `reflLim_of_covF` are
`CompositeLink.linkCPre_of_kernels`, `JointRP.jointRPK_of_reflLim`, `JointRP.reflLim_of_cov` at any
tensor fields `f` and bare fields `bareO`. `clayStatementAt_SU_reflAvg` is the SU capstone at
`fR`, `bR`: `hJ` is `jointRPK_of_reflLimF (reflLim_of_covF reflCovLat_CbR hCO hMC)`, `TiedB` is
`tiedB_R`, `NonGaussianT` is `NonGaussLink.nonGaussianT_rhoD_of_obs`. Its inputs are those of
`ClaySUBest.clayStatementAt_SU_best` without `hJ`, with `hK`, `hWard`, `hCO`, `hA`, `hMC` read at
`fR`, `bR`. `hK` at `rhoD (fR N) z` is equivalent to `hK` at `rhoD (fT N) z`
(`WardKernel.twoPointKernel_rhoD_congr`), so only `hWard`, `hCO`, `hA`, `hMC` differ from
`clayStatementAt_SU_best`: a trade (`hJ` for those four at the averaged composites), not a strict
improvement.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reflection constant and the origin; `1/2` the average;
`−1`, `1` the reflection signs; `2`, `4`, `16` as in `ClassicalLimit`, `ClayData` and `ObsLead`.
-/

noncomputable section

namespace MassGap.ReflAvg

open Filter
open scoped Topology Matrix ContDiff

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.ClassicalLimit

variable {N : ℕ}

/-! ## 1. The reflection on `ℝ⁴` and the reflected potential -/

section Potential

/-- The sign of the direction `μ` under the reflection of the axis `τ`. DERIVED: `−1`, `1` the
signs. -/
def rsg (τ μ : Fin 4) : ℝ := (-1) ^ (if μ = τ then 1 else 0)

theorem rsg_mul_self (τ μ : Fin 4) : rsg τ μ * rsg τ μ = 1 := by
  unfold rsg; split_ifs <;> norm_num

theorem rsg_self (τ : Fin 4) : rsg τ τ = -1 := by simp [rsg]

theorem rsg_ne {τ μ : Fin 4} (h : μ ≠ τ) : rsg τ μ = 1 := by simp [rsg, h]

/-- The reflection of the axis `τ` on `ℝ⁴`, as a continuous linear map. DERIVED: `4` the
dimension. -/
def rRL (τ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun i => rsg τ i • ContinuousLinearMap.proj i

theorem rRL_apply (τ : Fin 4) (y : Fin 4 → ℝ) (i : Fin 4) : rRL τ y i = rsg τ i * y i := rfl

theorem rRL_dir (τ μ : Fin 4) : rRL τ (dir μ) = rsg τ μ • dir μ := by
  funext i
  rw [rRL_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = μ
  · subst h; rfl
  · simp [dir, h]

/-- The lattice reflection of the plane `x_τ = 0` read on the sites: `site a (θx) = R (site a x)`.
DERIVED: `0` the reflection constant. -/
theorem rRL_site (τ : Fin 4) (a : ℝ) (x : ISite) :
    rRL τ (site a x) = site a (LatticeReflection.ireflSite τ 0 x) := by
  funext i
  rw [rRL_apply]
  simp only [site, LatticeReflection.ireflSite]
  by_cases h : i = τ
  · subst h; rw [rsg_self, Function.update_self]; push_cast; ring
  · rw [rsg_ne h, Function.update_of_ne h]; ring

/-- The far endpoint of a `τ`-link, reflected. DERIVED: `−1` the reflection constant of the
`τ`-links; `1` the link length. -/
theorem rRL_site_dir (τ : Fin 4) (a : ℝ) (x : ISite) :
    rRL τ (site a x + a • dir τ) = site a (LatticeReflection.ireflSite τ (-1) x) := by
  funext i
  rw [rRL_apply]
  simp only [site, LatticeReflection.ireflSite, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dir]
  by_cases h : i = τ
  · subst h; rw [rsg_self, Function.update_self, Pi.single_eq_same]; push_cast; ring
  · rw [rsg_ne h, Function.update_of_ne h, Pi.single_eq_of_ne h]; ring

/-- **The reflected potential** `A^R_μ(y) = s_μ A_μ(R y)`. DERIVED: no numeral. -/
def reflPot (τ : Fin 4) (A : GPot N) : GPot N := fun y μ => rsg τ μ • A (rRL τ y) μ

theorem contDiff_reflPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (τ : Fin 4) :
    ContDiff ℝ ∞ (reflPot τ A) := by
  have h := hA.comp (rRL τ).contDiff
  exact contDiff_pi.2 fun μ => (contDiff_pi.1 h μ).const_smul (rsg τ μ)

/-- The chain rule through the reflection. DERIVED: no numeral. -/
theorem fderiv_refl {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (τ : Fin 4)
    {F : (Fin 4 → ℝ) → M} (hF : Differentiable ℝ F) (c : ℝ) (y v : Fin 4 → ℝ) :
    fderiv ℝ (fun x => c • F (rRL τ x)) y v = c • fderiv ℝ F (rRL τ y) (rRL τ v) := by
  have h : HasFDerivAt (fun x => c • F (rRL τ x)) (c • (fderiv ℝ F (rRL τ y)).comp (rRL τ)) y :=
    (((hF (rRL τ y)).hasFDerivAt).comp y (rRL τ).hasFDerivAt).const_smul c
  rw [h.fderiv]
  rfl

theorem mcomm_smul (a b : ℝ) (X Y : Fin N → Fin N → ℂ) :
    mcomm (a • X) (b • Y) = (a * b) • mcomm X Y := by
  funext i j
  simp only [mcomm, Matrix.of_symm_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Pi.smul_apply, Complex.real_smul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring

theorem of_smul (r : ℝ) (X : Fin N → Fin N → ℂ) :
    (Matrix.of (r • X) : Mat N) = r • Matrix.of X := rfl

/-- **The covariant derivatives of the reflected potential**:
`D_{ds}F_{ρσ}[A^R](y) = s_ρ s_σ ∏ s_{ds} · D_{ds}F_{ρσ}[A](R y)`.

DERIVED: no numeral. -/
theorem covDF_reflPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (τ ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (y : Fin 4 → ℝ), covDF g (reflPot τ A) ρ σ ds y
      = (rsg τ ρ * rsg τ σ * (ds.map (rsg τ)).prod) • covDF g A ρ σ ds (rRL τ y)
  | [], y => by
    have hd : ∀ ν, Differentiable ℝ (fun z => A z ν) :=
      fun ν => (contDiff_pi.1 hA ν).differentiable (by simp)
    have h1 := fderiv_refl τ (hd σ) (rsg τ σ) y (dir ρ)
    have h2 := fderiv_refl τ (hd ρ) (rsg τ ρ) y (dir σ)
    simp only [covDF, reflPot]
    rw [h1, h2, rRL_dir, rRL_dir, map_smul, map_smul, mcomm_smul]
    funext i j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      List.map_nil, List.prod_nil]
    push_cast
    ring
  | μ :: ds, y => by
    have ih : covDF g (reflPot τ A) ρ σ ds
        = fun x => (rsg τ ρ * rsg τ σ * (ds.map (rsg τ)).prod) • covDF g A ρ σ ds (rRL τ x) :=
      funext (covDF_reflPot hA g τ ρ σ ds)
    have hdc : Differentiable ℝ (covDF g A ρ σ ds) :=
      (MassGap.CompositesBuild.contDiff_covDF hA g ρ σ ds).differentiable (by simp)
    have h1 := fderiv_refl τ hdc (rsg τ ρ * rsg τ σ * (ds.map (rsg τ)).prod) y (dir μ)
    simp only [covDF]
    rw [ih, h1]
    simp only [reflPot]
    rw [rRL_dir, map_smul, mcomm_smul]
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, List.map_cons,
      List.prod_cons]
    push_cast
    ring

/-- The count of indices `τ` in a letter, as in `ctau`. DERIVED: `1`, `0` the counts. -/
def ltau (τ : Fin 4) (l : Letter) : ℕ :=
  l.1.count τ + (if l.2.1 = τ then 1 else 0) + (if l.2.2 = τ then 1 else 0)

theorem prod_rsg (τ : Fin 4) : ∀ ds : List (Fin 4), (ds.map (rsg τ)).prod = (-1 : ℝ) ^ ds.count τ
  | [] => by simp
  | d :: ds => by
    rw [List.map_cons, List.prod_cons, prod_rsg τ ds, List.count_cons]
    by_cases h : d = τ
    · subst h; simp [rsg, pow_succ, mul_comm]
    · simp [rsg, h]

/-- **A letter of the reflected potential at the origin.** DERIVED: `0` the origin. -/
theorem covDF_reflPot_zero {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (τ : Fin 4) (l : Letter) :
    covDF g (reflPot τ A) l.2.1 l.2.2 l.1 0
      = ((-1 : ℝ) ^ ltau τ l) • covDF g A l.2.1 l.2.2 l.1 0 := by
  rw [covDF_reflPot hA g τ, map_zero, prod_rsg]
  congr 1
  simp only [ltau, rsg, pow_add]
  ring

theorem wordProd_reflPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (τ : Fin 4) :
    ∀ W : Word,
      (W.map fun l => (Matrix.of (covDF g (reflPot τ A) l.2.1 l.2.2 l.1 0) : Mat N)).prod
        = ((-1 : ℝ) ^ (W.map (ltau τ)).sum)
          • (W.map fun l => (Matrix.of (covDF g A l.2.1 l.2.2 l.1 0) : Mat N)).prod
  | [] => by simp
  | l :: W => by
    rw [List.map_cons, List.prod_cons, wordProd_reflPot hA g τ W, covDF_reflPot_zero hA g τ,
      of_smul, smul_mul_smul_comm, List.map_cons, List.sum_cons, pow_add, List.map_cons,
      List.prod_cons]

theorem wordTr_reflPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (τ : Fin 4) (W : Word) :
    wordTr g (reflPot τ A) W = ((-1 : ℝ) ^ (W.map (ltau τ)).sum) • wordTr g A W := by
  unfold wordTr
  rw [wordProd_reflPot hA g τ W, Matrix.trace_smul]

/-- **The value of a monomial at the reflected potential** is `(−1)^{ctau τ m}` times its value.

DERIVED: no numeral. -/
theorem cval_reflPot {A : GPot N} (hA : ContDiff ℝ ∞ A) (g : ℝ) (τ : Fin 4) :
    ∀ m : CMono, cval g (reflPot τ A) m = (-1 : ℝ) ^ ctau τ m * cval g A m
  | [] => by simp [cval, ctau]
  | p :: m => by
    have e1 : ∀ B : GPot N, cval g B (p :: m)
        = (if p.2 then (wordTr g B p.1).re else (wordTr g B p.1).im) * cval g B m := fun _ => rfl
    have e2 : ctau τ (p :: m) = (p.1.map (ltau τ)).sum + ctau τ m := rfl
    rw [e1, e1, e2, cval_reflPot hA g τ m, wordTr_reflPot hA g τ, pow_add]
    split_ifs
    · rw [Complex.smul_re, smul_eq_mul]; ring
    · rw [Complex.smul_im, smul_eq_mul]; ring

end Potential

/-! ## 2. Classical configurations with offset links -/

section Offset

open scoped Matrix.Norms.Operator

attribute [local instance] completeMat

/-- The continuum link `exp(a s A_μ(z + a c_μ))` with the offset `c_μ`. DERIVED: no numeral. -/
def exO (A : GPot N) (c : Fin 4 → Fin 4 → ℝ) (s : ℂ) (μ : Fin 4) (p : Par) : Mat N :=
  ex A s μ (shf (c μ) p)

theorem exO_mul_neg (A : GPot N) (c : Fin 4 → Fin 4 → ℝ) (s : ℂ) (μ : Fin 4) (p : Par) :
    exO A c s μ p * exO A c (-s) μ p = 1 :=
  ex_mul_neg A s μ _

theorem contDiff_exO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (s : ℂ)
    (μ : Fin 4) : ContDiff ℝ ∞ (exO A c s μ) :=
  (contDiff_ex hA s μ).comp (contDiff_shf _)

theorem exO_zero (A : GPot N) (c : Fin 4 → Fin 4 → ℝ) (s : ℂ) (μ : Fin 4) (z : Fin 4 → ℝ) :
    exO A c s μ ((0 : ℝ), z) = 1 := by
  simp [exO, ex, shf]

/-- **An offset link is `1 + a L`** with `L(0, z) = s A_μ(z)`: the offset vanishes at `a = 0`.
DERIVED: `1` the unit matrix; `0` the point `a = 0`. -/
theorem exO_ord {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (s : ℂ) (μ : Fin 4) :
    ∃ L : Par → Mat N, ContDiff ℝ ∞ L ∧ (∀ p, exO A c s μ p = 1 + p.1 • L p) ∧
      ∀ z, L (0, z) = s • Matrix.of (A z μ) := by
  obtain ⟨L, hL, eL, zL⟩ := ex_ord hA s μ
  refine ⟨fun p => L (shf (c μ) p), hL.comp (contDiff_shf _), fun p => eL _, fun z => ?_⟩
  have h : shf (c μ) ((0 : ℝ), z) = (0, z) := by simp [shf]
  simp only [h]
  exact zL z

/-- **The continuum letter with offset links.** DERIVED: `1` the unit matrix; `4` the
dimension. -/
def phiDO (g : ℝ) (A : GPot N) (c : Fin 4 → Fin 4 → ℝ) (ρ σ : Fin 4) :
    List (Fin 4) → Par → Mat N
  | [] => fun p =>
      exO A c (Complex.I * g) ρ p * exO A c (Complex.I * g) σ (shf (dir ρ) p)
        * exO A c (-(Complex.I * g)) ρ (shf (dir σ) p) * exO A c (-(Complex.I * g)) σ p - 1
  | μ :: ds => fun p =>
      exO A c (Complex.I * g) μ p * phiDO g A c ρ σ ds (shf (dir μ) p)
        * exO A c (-(Complex.I * g)) μ p - phiDO g A c ρ σ ds p

set_option backward.isDefEq.respectTransparency false in
/-- `ClassicalLimit.ord_base` at offset links. DERIVED: `2` the dimension of `F`. -/
theorem ord_baseO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ)
    (ρ σ : Fin 4) :
    OrdA 2 (phiDO g A c ρ σ []) (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ [] z)) := by
  obtain ⟨Lρ, hLρ, eρ, zρ⟩ := exO_ord hA c (Complex.I * g) ρ
  obtain ⟨Lσ, hLσ, eσ, zσ⟩ := exO_ord hA c (Complex.I * g) σ
  obtain ⟨Sσ, hSσ, eSσ, zSσ⟩ := shift_ord hLσ (dir ρ)
  obtain ⟨Sρ, hSρ, eSρ, zSρ⟩ := shift_ord hLρ (dir σ)
  refine ⟨fun p => (Sσ p - Sρ p + Lρ p * Lσ (shf (dir ρ) p) - Lσ p * Lρ (shf (dir σ) p))
      * (exO A c (-(Complex.I * g)) ρ (shf (dir σ) p) * exO A c (-(Complex.I * g)) σ p),
    ?_, fun p => ?_, fun z => ?_⟩
  · exact ((((hSσ.sub hSρ).add (hLρ.mul (hLσ.comp (contDiff_shf _)))).sub
      (hLσ.mul (hLρ.comp (contDiff_shf _)))).mul
      (((contDiff_exO hA c _ ρ).comp (contDiff_shf _)).mul (contDiff_exO hA c _ σ)))
  · have hfac : phiDO g A c ρ σ [] p
        = (exO A c (Complex.I * g) ρ p * exO A c (Complex.I * g) σ (shf (dir ρ) p)
            - exO A c (Complex.I * g) σ p * exO A c (Complex.I * g) ρ (shf (dir σ) p))
          * (exO A c (-(Complex.I * g)) ρ (shf (dir σ) p) * exO A c (-(Complex.I * g)) σ p) := by
      simp only [phiDO, sub_mul, mul_assoc]
      congr 1
      rw [← mul_assoc (exO A c (Complex.I * g) ρ (shf (dir σ) p)), exO_mul_neg, one_mul,
        exO_mul_neg]
    rw [hfac, ← smul_mul_assoc]
    congr 1
    have h2 : Lσ (shf (dir ρ) p) = Lσ p + p.1 • Sσ p := by rw [← eSσ p]; abel
    have h4 : Lρ (shf (dir σ) p) = Lρ p + p.1 • Sρ p := by rw [← eSρ p]; abel
    have hs : ∀ v, (shf v p).1 = p.1 := fun v => rfl
    rw [eρ p, eσ (shf (dir ρ) p), eσ p, eρ (shf (dir σ) p), hs, hs, h2, h4]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_sub, smul_smul, mul_assoc]
    module
  · have hs0 : ∀ v, shf v ((0 : ℝ), z) = (0, z) := fun v => by simp [shf]
    simp only []
    rw [hs0, hs0, exO_zero, exO_zero, mul_one, zSσ, zSρ, zρ, zσ]
    have hfσ : (fun y => Lσ (0, y)) = fun y => (Complex.I * g) • (Matrix.of (A y σ) : Mat N) :=
      funext zσ
    have hfρ : (fun y => Lρ (0, y)) = fun y => (Complex.I * g) • (Matrix.of (A y ρ) : Mat N) :=
      funext zρ
    have hdA : ∀ ν, Differentiable ℝ (fun y => A y ν) :=
      fun ν => (contDiff_pi.1 hA ν).differentiable (by simp)
    rw [hfσ, hfρ, fderiv_cof (hdA σ z), fderiv_cof (hdA ρ z)]
    simp only [covDF, ← Matrix.of_add_of, ← Matrix.of_sub_of, ← Matrix.smul_of, of_mcomm,
      smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
    try abel

set_option backward.isDefEq.respectTransparency false in
/-- `ClassicalLimit.ord_step` at offset links. DERIVED: `1` the extra power of `a`. -/
theorem ord_stepO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ)
    (ρ σ μ : Fin 4) (ds : List (Fin 4)) (k : ℕ)
    (h : OrdA k (phiDO g A c ρ σ ds) (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ ds z))) :
    OrdA (k + 1) (phiDO g A c ρ σ (μ :: ds))
      (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ (μ :: ds) z)) := by
  obtain ⟨G, hG, eG, zG⟩ := h
  obtain ⟨LV, hLV, eV, zV⟩ := exO_ord hA c (Complex.I * g) μ
  obtain ⟨LW, hLW, eW, zW⟩ := exO_ord hA c (-(Complex.I * g)) μ
  obtain ⟨S, hS, eS, zS⟩ := shift_ord hG (dir μ)
  refine ⟨fun p => S p + LV p * G (shf (dir μ) p) + G (shf (dir μ) p) * LW p
      + p.1 • (LV p * G (shf (dir μ) p) * LW p), ?_, fun p => ?_, fun z => ?_⟩
  · have hGs := hG.comp (contDiff_shf (dir μ))
    exact ((hS.add (hLV.mul hGs)).add (hGs.mul hLW)).add
      (contDiff_fst.smul ((hLV.mul hGs).mul hLW))
  · simp only [phiDO]
    have h1 : G (shf (dir μ) p) = G p + p.1 • S p := by rw [← eS p]; abel
    have hs : (shf (dir μ) p).1 = p.1 := rfl
    rw [eG (shf (dir μ) p), eG p, eV p, eW p, hs, h1]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_smul, mul_assoc, pow_succ]
    module
  · have hs0 : shf (dir μ) ((0 : ℝ), z) = (0, z) := by simp [shf]
    simp only [hs0, zero_smul, add_zero]
    rw [zS, zV, zW, zG]
    have hf : (fun y => G (0, y))
        = fun y => (Complex.I * g) • (Matrix.of (covDF g A ρ σ ds y) : Mat N) :=
      funext zG
    have hd : Differentiable ℝ (covDF g A ρ σ ds) :=
      (MassGap.CompositesBuild.contDiff_covDF hA g ρ σ ds).differentiable (by simp)
    rw [hf, fderiv_cof (hd z)]
    simp only [covDF, ← Matrix.of_add_of, ← Matrix.smul_of, of_mcomm, smul_add, smul_sub,
      smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul, mul_neg]
    abel

/-- `ClassicalLimit.ord_covDF` at offset links. DERIVED: `2` the dimension of `F`. -/
theorem ord_covDFO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ)
    (ρ σ : Fin 4) :
    ∀ ds : List (Fin 4), OrdA (ds.length + 2) (phiDO g A c ρ σ ds)
      (fun z => (Complex.I * g) • Matrix.of (covDF g A ρ σ ds z))
  | [] => ord_baseO hA c g ρ σ
  | μ :: ds => by
    have := ord_stepO hA c g ρ σ μ ds _ (ord_covDFO hA c g ρ σ ds)
    rwa [show ds.length + 2 + 1 = (μ :: ds).length + 2 by simp] at this

/-- **A classical configuration with offset links**: `U_μ(x) = exp(i a g A_μ(a x + a c_μ))`.
DERIVED: no numeral. -/
def IsClassCfgO (a g : ℝ) (A : GPot N) (c : Fin 4 → Fin 4 → ℝ) (U : Cfg N) : Prop :=
  ∀ (μ : Fin 4) (x : ISite), lk U (μ, x) = exO A c (Complex.I * g) μ (a, site a x)

theorem lkiO {a g : ℝ} {A : GPot N} {c : Fin 4 → Fin 4 → ℝ} {U : Cfg N}
    (hU : IsClassCfgO a g A c U) (μ : Fin 4) (x : ISite) :
    lki U (μ, x) = exO A c (-(Complex.I * g)) μ (a, site a x) := by
  have h1 : lki U (μ, x) * lk U (μ, x) = 1 := coe_inv_mul _
  have h2 : lk U (μ, x) * exO A c (-(Complex.I * g)) μ (a, site a x) = 1 := by
    rw [hU μ x, exO_mul_neg]
  calc lki U (μ, x)
      = lki U (μ, x) * (lk U (μ, x) * exO A c (-(Complex.I * g)) μ (a, site a x)) := by
        rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

/-- `ClassicalLimit.latD_classCfg` at offset links. DERIVED: no numeral. -/
theorem latD_classCfgO {a g : ℝ} {A : GPot N} {c : Fin 4 → Fin 4 → ℝ} {U : Cfg N}
    (hU : IsClassCfgO a g A c U) (ρ σ : Fin 4) :
    ∀ (ds : List (Fin 4)) (x : ISite), latD U ρ σ ds x = phiDO g A c ρ σ ds (a, site a x)
  | [], x => by
    simp only [latD, phiDO, plaqG, coe_mulSU]
    rw [show ((U (ρ, x) : MassGap.SUN.SU N) : Mat N) = lk U (ρ, x) from rfl,
      show ((U (σ, ishift ρ x) : MassGap.SUN.SU N) : Mat N) = lk U (σ, ishift ρ x) from rfl,
      show (((U (ρ, ishift σ x))⁻¹ : MassGap.SUN.SU N) : Mat N) = lki U (ρ, ishift σ x) from rfl,
      show (((U (σ, x))⁻¹ : MassGap.SUN.SU N) : Mat N) = lki U (σ, x) from rfl,
      hU, hU, lkiO hU, lkiO hU, site_ishift, site_ishift]
    rfl
  | μ :: ds, x => by
    simp only [latD, phiDO]
    rw [hU, lkiO hU, latD_classCfgO hU ρ σ ds, latD_classCfgO hU ρ σ ds, site_ishift]
    rfl

/-- `ClassicalLimit.word_ord` at offset links. DERIVED: `0` the origin. -/
theorem word_ordO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ) :
    ∀ W : Word, ∃ Q : ℝ → Mat N, Continuous Q ∧
      (∀ a (U : Cfg N), IsClassCfgO a g A c U → latW U W = a ^ (W.map letDim).sum • Q a) ∧
      Q 0 = (Complex.I * g) ^ W.length •
        (W.map fun l => (Matrix.of (covDF g A l.2.1 l.2.2 l.1 0) : Mat N)).prod
  | [] => ⟨fun _ => 1, continuous_const, fun a U _ => by simp [latW], by simp⟩
  | l :: W => by
    obtain ⟨Q, hQ, eQ, zQ⟩ := word_ordO hA c g W
    obtain ⟨G, hG, eG, zG⟩ := ord_covDFO hA c g l.2.1 l.2.2 l.1
    refine ⟨fun a => G (a, 0) * Q a, (hG.continuous.comp
      (continuous_id.prodMk continuous_const)).mul hQ, fun a U hU => ?_, ?_⟩
    · have hW := eQ a U hU
      simp only [latW, List.map_cons, List.prod_cons, List.sum_cons] at hW ⊢
      rw [hW, latD_classCfgO hU, site_zero, eG]
      simp only [letDim, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
      rw [Nat.add_comm (List.map letDim W).sum]
    · simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [zG, zQ, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

/-- `ClassicalLimit.fac_ord` at offset links. DERIVED: no numeral. -/
theorem fac_ordO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ)
    (p : Word × Bool) :
    ∃ q : ℝ → ℝ, Continuous q ∧
      (∀ a (U : Cfg N), IsClassCfgO a g A c U → facV U p = a ^ (p.1.map letDim).sum * q a) ∧
      q 0 = g ^ p.1.length *
        (if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im) := by
  obtain ⟨Q, hQ, eQ, zQ⟩ := word_ordO hA c g p.1
  have htr : Continuous fun a => (-Complex.I) ^ p.1.length * Matrix.trace (Q a) :=
    continuous_const.mul
      (((Matrix.traceLinearMap (Fin N) ℝ ℂ).continuous_of_finiteDimensional).comp hQ)
  have hz : (-Complex.I) ^ p.1.length * Matrix.trace (Q 0)
      = ((g ^ p.1.length : ℝ) : ℂ) * wordTr g A p.1 := by
    rw [zQ, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, negI_mul_pow, wordTr]
  have hfa : ∀ a (U : Cfg N), IsClassCfgO a g A c U →
      (-Complex.I) ^ p.1.length * Matrix.trace (latW U p.1)
        = ((a ^ (p.1.map letDim).sum : ℝ) : ℂ)
          * ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)) := by
    intro a U hU
    rw [eQ a U hU, Matrix.trace_smul, Complex.real_smul]
    ring
  cases hb : p.2
  · refine ⟨fun a => ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)).im,
      Complex.continuous_im.comp htr, fun a U hU => ?_, ?_⟩
    · simp only [facV, hb, Bool.false_eq_true, if_false]
      rw [hfa a U hU, Complex.im_ofReal_mul]
    · simp only [hz, Complex.im_ofReal_mul, Bool.false_eq_true, if_false]
  · refine ⟨fun a => ((-Complex.I) ^ p.1.length * Matrix.trace (Q a)).re,
      Complex.continuous_re.comp htr, fun a U hU => ?_, ?_⟩
    · simp only [facV, hb, if_true]
      rw [hfa a U hU, Complex.re_ofReal_mul]
    · simp only [hz, Complex.re_ofReal_mul, if_true]

/-- `ClassicalLimit.mono_ord` at offset links. DERIVED: no numeral. -/
theorem mono_ordO {A : GPot N} (hA : ContDiff ℝ ∞ A) (c : Fin 4 → Fin 4 → ℝ) (g : ℝ) :
    ∀ m : CMono, ∃ q : ℝ → ℝ, Continuous q ∧
      (∀ a (U : Cfg N), IsClassCfgO a g A c U → monoV m U = a ^ cdim m * q a) ∧
      q 0 = g ^ cnF m * cval g A m
  | [] => ⟨fun _ => 1, continuous_const, fun a U _ => by simp [monoV, cdim],
      by simp [cnF, cval]⟩
  | p :: m => by
    obtain ⟨q, hq, eq, zq⟩ := mono_ordO hA c g m
    obtain ⟨f, hf, ef, zf⟩ := fac_ordO hA c g p
    refine ⟨fun a => f a * q a, hf.mul hq, fun a U hU => ?_, ?_⟩
    · have hc : cdim (p :: m) = (p.1.map letDim).sum + cdim m := rfl
      rw [monoV_cons, ef a U hU, eq a U hU, hc, pow_add]
      ring
    · have hn : cnF (p :: m) = p.1.length + cnF m := rfl
      have hv : cval g A (p :: m)
          = (if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im) * cval g A m := rfl
      show f 0 * q 0 = _
      rw [zf, zq, hn, hv, pow_add]
      ring

end Offset

/-! ## 3. The reflected classical configuration -/

section ReflCfg

/-- The offsets of the reflected configuration: `dir τ` on the `τ`-links, `0` on the others.
DERIVED: `0` the zero offset. -/
def cR (τ : Fin 4) : Fin 4 → Fin 4 → ℝ := fun μ => if μ = τ then dir τ else 0

/-- **The reflection of a classical configuration of `A` is an offset classical configuration of
the reflected potential**: its `τ`-links read `A^R` at the far endpoint. DERIVED: `0` the
reflection constant; `−1` that of the `τ`-links. -/
theorem classCfgO_refl {a g : ℝ} {A : GPot N} {U : Cfg N} (hU : IsClassCfg a g A U) (τ : Fin 4) :
    IsClassCfgO a g (reflPot τ A) (cR τ) (LatticeReflection.ireflConf τ 0 U) := by
  intro μ x
  by_cases h : μ = τ
  · subst h
    have e1 : lk (LatticeReflection.ireflConf μ 0 U) (μ, x)
        = lki U (μ, LatticeReflection.ireflSite μ (-1) x) := by
      simp [lk, lki, LatticeReflection.ireflConf, LatticeReflection.ireflLink]
    have hc : cR μ μ = dir μ := if_pos rfl
    rw [e1, lki_classCfg hU, exO, hc]
    show NormedSpace.exp (a • ((-(Complex.I * g)) • Matrix.of
        (A (site a (LatticeReflection.ireflSite μ (-1) x)) μ)))
      = NormedSpace.exp (a • ((Complex.I * g) • Matrix.of
        (reflPot μ A (site a x + a • dir μ) μ)))
    rw [show reflPot μ A (site a x + a • dir μ) μ
        = rsg μ μ • A (rRL μ (site a x + a • dir μ)) μ from rfl, rsg_self, rRL_site_dir,
      of_smul, neg_one_smul, smul_neg, neg_smul]
  · have e1 : lk (LatticeReflection.ireflConf τ 0 U) (μ, x)
        = lk U (μ, LatticeReflection.ireflSite τ 0 x) := by
      simp [lk, LatticeReflection.ireflConf, LatticeReflection.ireflLink, h]
    have hc : cR τ μ = 0 := if_neg h
    rw [e1, lk_classCfg hU, exO, hc]
    show NormedSpace.exp (a • ((Complex.I * g) • Matrix.of
        (A (site a (LatticeReflection.ireflSite τ 0 x)) μ)))
      = NormedSpace.exp (a • ((Complex.I * g) • Matrix.of
        (reflPot τ A (site a x + a • (0 : Fin 4 → ℝ)) μ)))
    rw [smul_zero, add_zero, show reflPot τ A (site a x) μ
        = rsg τ μ • A (rRL τ (site a x)) μ from rfl, rsg_ne h, one_smul, rRL_site]

theorem ireflConf_one (τ : Fin 4) :
    LatticeReflection.ireflConf τ 0 (fun _ => (1 : MassGap.SUN.SU N)) = fun _ => 1 := by
  funext l
  simp [LatticeReflection.ireflConf]

theorem refl_apply (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (V : Cfg N) :
    (O.refl τ).1 V = O.1 (LatticeReflection.ireflConf τ 0 V) := rfl

/-- **The classical lead of a reflected monomial**: `θ (bareF m)` has lead
`(−1)^{ctau τ m} g^{cnF m} cval g A m` at dimension `cdim m`, for every admissible `m`.

DERIVED: `0` the reflection constant and the point `a = 0`. -/
theorem classicalLead_refl_bareF (τ : Fin 4) (m : CMono) (hm : m ≠ []) (hw : ∀ p ∈ m, p.1 ≠ []) :
    ClassicalLead (N := N) ((bareF m).refl τ).1 (cdim m)
      (fun A g => (-1 : ℝ) ^ ctau τ m * (g ^ cnF m * cval g A m)) := by
  intro A hAdm g U hU
  have hA : ContDiff ℝ ∞ A := contDiff_infty.2 hAdm.1
  obtain ⟨q, hq, eq, zq⟩ := mono_ordO (contDiff_reflPot hA τ) (cR τ) g m
  have hval : q 0 = (-1 : ℝ) ^ ctau τ m * (g ^ cnF m * cval g A m) := by
    rw [zq, cval_reflPot hA g τ m]; ring
  beta_reduce
  rw [← hval]
  have hlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (q 0)) :=
    hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : (0 : ℝ) < a := ha
  rw [refl_apply, refl_apply, ireflConf_one, bareF_apply, bareF_apply, monoV_one hm hw,
    eq a _ (classCfgO_refl (hU a ha') τ), sub_zero,
    mul_div_cancel_left₀ _ (pow_ne_zero _ ha'.ne')]

end ReflCfg

/-! ## 4. The average -/

section Average

/-- **The reflection average** `½ (O + (−1)ⁿ θO)`, `θ = ireflObs 0 0`.

DERIVED: `1/2` the average; `0` the plane. -/
def reflAvg (n : ℕ) (O : LField (MassGap.SUN.SU N)) : LField (MassGap.SUN.SU N) :=
  ⟨(1 / 2 : ℝ) • (O.1 + ((-1 : ℝ) ^ n) • (O.refl 0).1),
    Submodule.smul_mem _ _ (Submodule.add_mem _ (MassGap.CompositesBuild.mem_lfSub O)
      (Submodule.smul_mem _ _ (MassGap.CompositesBuild.mem_lfSub (O.refl 0))))⟩

theorem reflAvg_apply (n : ℕ) (O : LField (MassGap.SUN.SU N)) (V : Cfg N) :
    (reflAvg n O).1 V = (1 / 2 : ℝ) * (O.1 V + (-1 : ℝ) ^ n * (O.refl 0).1 V) := rfl

theorem ireflObs_ireflObs (F : C(Cfg N, ℝ)) :
    LatticeReflection.ireflObs 0 0 (LatticeReflection.ireflObs 0 0 F) = F := by
  ext U
  simp only [LatticeReflection.ireflObs_apply]
  rw [LatticeReflection.ireflConf_involutive]

/-- **The average is reflection covariant**: `θ (reflAvg n O) = (−1)ⁿ reflAvg n O`.

DERIVED: `0` the plane; `2` the square of the sign. -/
theorem reflAvg_refl (n : ℕ) (O : LField (MassGap.SUN.SU N)) :
    ((reflAvg n O).refl 0).1 = ((-1 : ℝ) ^ n) • (reflAvg n O).1 := by
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  show LatticeReflection.ireflObs 0 0 ((1 / 2 : ℝ) • (O.1 + ((-1 : ℝ) ^ n)
      • LatticeReflection.ireflObs 0 0 O.1))
    = ((-1 : ℝ) ^ n) • ((1 / 2 : ℝ) • (O.1 + ((-1 : ℝ) ^ n) • LatticeReflection.ireflObs 0 0 O.1))
  rw [map_smul, map_add, map_smul, ireflObs_ireflObs]
  ext U
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul]
  linear_combination (-(1 / 2 : ℝ) * (LatticeReflection.ireflObs 0 0 O.1) U) * hs

/-- The average vanishes at the unit configuration when `O` does. DERIVED: `1` the unit. -/
theorem reflAvg_one (n : ℕ) (O : LField (MassGap.SUN.SU N))
    (h : O.1 (fun _ => 1) = 0) : (reflAvg n O).1 (fun _ => 1) = 0 := by
  rw [reflAvg_apply, refl_apply, ireflConf_one, h]
  ring

/-- **The averaged bare field of a monomial** `reflAvg (ctau 0 m) (bareF m)`.

DERIVED: `0` the plane. -/
def bareR (m : CMono) : LField (MassGap.SUN.SU N) := reflAvg (ctau 0 m) (bareF m)

/-- **The averaged field has the lead of the bare field**:
`½ (P + (−1)ⁿ (−1)ⁿ P) = P` (`classicalLead_bareF`, `classicalLead_refl_bareF`).

DERIVED: `1/2` the average; `0` the plane. -/
theorem lead_bareR (m : CMono) (hm : m ≠ []) (hw : ∀ p ∈ m, p.1 ≠ []) :
    ClassicalLead (N := N) (bareR m).1 (cdim m) (fun A g => g ^ cnF m * cval g A m) := by
  intro A hA g U hU
  have h1 := classicalLead_bareF (N := N) m hm hw A hA g U hU
  have h2 := classicalLead_refl_bareF (N := N) 0 m hm hw A hA g U hU
  have hs : (-1 : ℝ) ^ ctau 0 m * (-1 : ℝ) ^ ctau 0 m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h3 := (h1.add (h2.const_mul ((-1 : ℝ) ^ ctau 0 m))).const_mul (1 / 2 : ℝ)
  have hv : (1 / 2 : ℝ) * (g ^ cnF m * cval g A m + (-1 : ℝ) ^ ctau 0 m
      * ((-1 : ℝ) ^ ctau 0 m * (g ^ cnF m * cval g A m))) = g ^ cnF m * cval g A m := by
    rw [← mul_assoc ((-1 : ℝ) ^ ctau 0 m), hs]; ring
  rw [hv] at h3
  refine h3.congr fun a => ?_
  simp only [bareR, reflAvg_apply]
  ring

end Average

/-! ## 5. The channels under the reflection -/

section Channels

open MassGap.ClayData MassGap.CompositesBuild MassGap.ObserverNontrivial

theorem P_Rl (c : Chan) : P c * Rl = P c := by
  cases c <;> simp [P, Pw, sub_mul, Rl_idem, PS_Rl, PE_Rl, Ql_Rl]

theorem Rl_const : Rl (fun _ => (1 : ℝ)) = 0 := by
  funext α
  simp only [Rl_apply, rsym]
  norm_num

/-- **Every row of `Pm c` sums to `0`**: `P c` factors through `Rl`, which kills the constant
tensor. DERIVED: `0` the sum. -/
theorem Pm_rowsum (c : Chan) (α : Idx4) : ∑ γ, Pm c α γ = 0 := by
  have h1 : P c (fun _ => (1 : ℝ)) = 0 := by
    have := congrArg (fun F : Module.End ℝ V4 => F (fun _ => 1)) (P_Rl c)
    simp only [Module.End.mul_apply, Rl_const, map_zero] at this
    exact this.symm
  have h2 := congrFun (Pm_mulVec c (fun _ => 1)) α
  rw [h1] at h2
  simpa [Matrix.mulVec, dotProduct] using h2

/-- The reflection of the axis `0` as a matrix. DERIVED: `0` the axis. -/
def Aθ : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal (rsg 0)

theorem Aθ_orth1 : Aθᵀ * Aθ = 1 := by
  rw [Aθ, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact rsg_mul_self 0 i

theorem Aθ_orth2 : Aθ * Aθᵀ = 1 := mul_eq_one_comm.mp Aθ_orth1

theorem tcoef_diag (d : Fin 4 → ℝ) (α β : Idx4) :
    tcoef (Matrix.diagonal d) α β = if α = β then ∏ j, d (α j) else 0 := by
  unfold tcoef
  split_ifs with h
  · subst h; simp [Matrix.diagonal_apply_eq]
  · obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Matrix.diagonal_apply_ne _ (Ne.symm hj))

/-- The reflection sign of a tensor index. DERIVED: no numeral. -/
def sθ (α : Idx4) : ℝ := ∏ j, rsg 0 (α j)

theorem sign_emono (α : Idx4) : (-1 : ℝ) ^ ctau 0 (emono α) = sθ α := by
  simp only [ctau, emono, sθ, rsg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.count_nil, Fin.prod_univ_four, pow_add, zero_add, add_zero]
  ring

theorem tcoef_Aθ (α β : Idx4) : tcoef Aθ α β = if α = β then sθ α else 0 := tcoef_diag _ α β

/-- **The channel projectors preserve the reflection parity**: `Pm c α δ s_δ = s_α Pm c α δ`
(`Pm_Tm` at `Aθ`). DERIVED: no numeral. -/
theorem Pm_parity (c : Chan) (α δ : Idx4) : Pm c α δ * sθ δ = sθ α * Pm c α δ := by
  have h := congrFun (congrFun (Pm_Tm Aθ Aθ_orth1 Aθ_orth2 c) α) δ
  simp only [Matrix.mul_apply, Tm, Matrix.of_apply, tcoef_Aθ, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

/-- **`t_α` vanishes at odd reflection parity**: `s_α t_α = t_α` (`Tl_tv` at `Aθ`).
DERIVED: no numeral. -/
theorem tv_parity (α : Idx4) : sθ α * tv α = tv α := by
  have h := congrFun (Tl_tv Aθ Aθ_orth1) α
  rw [Tl_apply] at h
  simp only [tcoef_Aθ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h

variable (f : Idx4 → LField (MassGap.SUN.SU N))

theorem Fv_u1 (hf0 : ∀ δ, (f δ).1 (u1 N) = 0) (c : Chan) (γ : Idx4) :
    (Fv f c γ).1 (u1 N) = 0 := by
  rw [Fv_val]
  simp [hf0]

theorem sum_Pm_opT_eq (hf0 : ∀ δ, (f δ).1 (u1 N) = 0) (c : Chan) (α : Idx4) :
    ∑ γ, Pm c α γ • (opT f c γ).1 = (Fv f c α).1 := by
  have hsT : ∀ γ, sT f c γ = -vtag N c := fun γ => by rw [sT_def, Fv_u1 f hf0]; ring
  have h0 : ∑ γ, Pm c α γ * sT f c γ = 0 := by
    simp only [hsT]
    rw [← Finset.sum_mul, Pm_rowsum, zero_mul]
  rw [sum_Pm_opT, h0, zero_smul, sub_zero]

/-- **The mixing component in terms of the channel fields** when every `f δ` vanishes at the unit
configuration: the constant shifts cancel (`Pm_rowsum`). DERIVED: no numeral. -/
theorem Ecomb_Fv (hf0 : ∀ δ, (f δ).1 (u1 N) = 0) (ζ : Chan → ℝ) (β : Idx4) :
    Ecomb f ζ β = (wD N * tv β * ζ .sc) • (obs N).1
      + ∑ c, (if c = .sc then 0 else ζ c • (Fv f c β).1) := by
  unfold Ecomb
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c = .sc
  · simp [hc]
  · simp only [hc, if_false]
    rw [← sum_Pm_opT_eq f hf0 c β, Finset.smul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_smul, mul_comm]

theorem refl_Fv (hfθ : ∀ δ, LatticeReflection.ireflObs 0 0 (f δ).1 = sθ δ • (f δ).1)
    (c : Chan) (β : Idx4) :
    LatticeReflection.ireflObs 0 0 (Fv f c β).1 = sθ β • (Fv f c β).1 := by
  rw [Fv_val, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [map_smul, hfθ, smul_smul, smul_smul, Pm_parity]

theorem obs_refl : LatticeReflection.ireflObs 0 0 (obs N).1 = (obs N).1 := by
  have h : (obs N).refl 0 = obs N := by
    rw [obs_def]
    exact (ObserverSymField.sym_hypScalar _).2 0
  exact congrArg Subtype.val h

/-- **The mixing component is reflection covariant** when the tensor fields are:
`θ (Ecomb f ζ β) = s_β Ecomb f ζ β`. DERIVED: no numeral. -/
theorem refl_Ecomb (hf0 : ∀ δ, (f δ).1 (u1 N) = 0)
    (hfθ : ∀ δ, LatticeReflection.ireflObs 0 0 (f δ).1 = sθ δ • (f δ).1) (ζ : Chan → ℝ)
    (β : Idx4) :
    LatticeReflection.ireflObs 0 0 (Ecomb f ζ β) = sθ β • Ecomb f ζ β := by
  rw [Ecomb_Fv f hf0, map_add, map_smul, obs_refl, map_sum, smul_add, smul_smul,
    Finset.smul_sum]
  congr 1
  · congr 1
    calc wD N * tv β * ζ .sc = wD N * (sθ β * tv β) * ζ .sc := by rw [tv_parity]
      _ = sθ β * (wD N * tv β * ζ .sc) := by ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = .sc
    · simp [hc]
    · simp only [hc, if_false]
      rw [map_smul, refl_Fv f hfθ, smul_comm]

end Channels

/-! ## 6. The averaged composites -/

section Composites

open MassGap.ClayData MassGap.CompositesBuild

/-- The averaged tensor fields `bareR (emono δ)`. DERIVED: no numeral. -/
abbrev fR (N : ℕ) : Idx4 → LField (MassGap.SUN.SU N) := fun δ => bareR (emono δ)

/-- The averaged bare fields `bareR i.1`. DERIVED: no numeral. -/
abbrev bR (N : ℕ) : Ix0 → LField (MassGap.SUN.SU N) := fun i => bareR i.1

/-- The averaged composites. DERIVED: no numeral. -/
abbrev CbR (N : ℕ) (z : Chan → ℕ → ℝ) : Composites N := build (rhoD (fR N) z) (bareD (fR N) (bR N))

theorem fR_u1 (δ : Idx4) : (fR N δ).1 (u1 N) = 0 :=
  reflAvg_one _ _ (monoV_one (by simp [emono]) (by simp [emono]))

theorem fR_refl (δ : Idx4) :
    LatticeReflection.ireflObs 0 0 (fR N δ).1 = sθ δ • (fR N δ).1 := by
  rw [← sign_emono]
  exact reflAvg_refl _ _

/-- **The averaged composites are reflection covariant on the lattice** at every step.

DERIVED: `0` the plane. -/
theorem reflCovLat_CbR (z : Chan → ℕ → ℝ) : JointRP.ReflCovLat (CbR N z) 0 := by
  intro k i
  show ((renF (rhoD (fR N) z) (bareD (fR N) (bR N)) k i).refl 0).1
    = ((-1 : ℝ) ^ ctau 0 i.1) • (renF (rhoD (fR N) z) (bareD (fR N) (bR N)) k i).1
  cases hd : dec i.1 with
  | none =>
    rw [renF_of_none _ _ hd]
    have e : bareD (fR N) (bR N) i = bareR i.1 := by
      show (match dec i.1 with | some α => bareT (fR N) α | none => bR N i) = _
      rw [hd]
    rw [e]
    exact reflAvg_refl _ _
  | some α =>
    have hi : i = eI α := eI_of_dec hd
    subst hi
    rw [renF_of_some _ _ hd]
    show LatticeReflection.ireflObs 0 0 (mixF (rhoD (fR N) z) k α).1
      = ((-1 : ℝ) ^ ctau 0 (emono α)) • (mixF (rhoD (fR N) z) k α).1
    rw [mixF_rhoD, sign_emono]
    exact refl_Ecomb (fR N) fR_u1 fR_refl _ α

/-- **`TiedB` at the averaged fields**, from the lead of the observer's field
(`ObsLead.classicalLead_obs`) and the leads of the averaged fields (`lead_bareR`), as in
`ClayData.tiedB_bareD_of_obs`.

DERIVED: `4` the dimension; `2` the power of the coupling; `16` as in `lead_alg`; `0` the excluded
colour count. -/
theorem tiedB_R (hN : N ≠ 0) : TiedB (bareD (fR N) (bR N)) := by
  intro i
  cases hd : dec i.1 with
  | none =>
    have : bareD (fR N) (bR N) i = bareR i.1 := by
      show (match dec i.1 with | some α => _ | none => _) = _
      rw [hd]
    rw [this]
    exact lead_bareR i.1 i.2.1 i.2.2
  | some β =>
    have hi : i = eI β := eI_of_dec hd
    subst hi
    rw [bareD_eI]
    have e1 : cdim (eI β).1 = 4 := cdim_emono β
    have e2 : cnF (eI β).1 = 2 := rfl
    rw [e1, e2]
    simp only [show (eI β).1 = emono β from rfl, cval_emono]
    let cf : BD → ℝ := fun i => match i with
      | none => wD N * tv β
      | some p => if p.1 = Chan.sc then 0 else Pm p.1 β p.2
    let L : BD → Cfg N → ℝ := fun i => match i with
      | none => (obs N).1
      | some p => (fR N p.2).1
    let Pl : BD → GPot N → ℝ → ℝ := fun i => match i with
      | none => fun A g => (16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A))
      | some p => fun A g => g ^ 2 * ffT g A p.2
    have hall : ∀ i ∈ (Finset.univ : Finset BD), ClassicalLead (L i) 4 (Pl i) := by
      intro i _
      cases i with
      | none => exact ObsLead.classicalLead_obs
      | some p =>
        have h := lead_bareR (N := N) (emono p.2) (by simp [emono]) (by simp [emono])
        rw [cdim_emono, show cnF (emono p.2) = 2 from rfl] at h
        simp only [cval_emono] at h
        exact h
    have hs := ClassicalLimit.classicalLead_sum Finset.univ cf L Pl 4 hall
    have hP : (fun A g => ∑ i ∈ (Finset.univ : Finset BD), cf i * Pl i A g)
        = fun (A : GPot N) (g : ℝ) => g ^ 2 * ffT g A β := by
      funext A g
      rw [sum_BD]
      have := lead_alg hN (ffT g A) (ffT_riemann g A) β
      simp only [cf, Pl]
      rw [← this]
      simp only [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun δ _ => by ring
    rw [hP] at hs
    refine classicalLead_add_const 0 (fun U => ?_) hs
    rw [add_zero, sum_BD]
    simp only [cf, L]
    rw [bareT_val]
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.coe_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = Chan.sc
    · simp [hc]
    · simp only [hc, if_false, Fv_val, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul]

end Composites

/-! ## 7. The chain at any tensor and bare fields -/

section Generic

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData
  MassGap.CompositeLink MassGap.JointRP

/-- The composites at the tensor fields `f` and the bare fields `bareO`. DERIVED: no numeral. -/
abbrev CbF (f : Idx4 → LField (MassGap.SUN.SU N)) (bareO : Ix0 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) : Composites N :=
  build (rhoD f z) (bareD f bareO)

/-- `CompositeLink.mixK` at `CbF f bareO z`. DERIVED: `0` the plane. -/
abbrev mixKF (hN2 : 2 ≤ N) (W : ConfFlow N) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (r : ℝ)
    (P : TSepG (CbF f bareO z).Ix 0) (Q : MarginMono N 0 r) : ℝ :=
  mixKC (ne_zero_of_two_le hN2) (CbF f bareO z) (Φ0 W) 0 P Q.1

/-- `CompositeLink.MixConv` at `CbF f bareO z`. DERIVED: `0` the plane. -/
def MixConvF (hN2 : 2 ≤ N) (W : ConfFlow N) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ (P : TSepG (CbF f bareO z).Ix 0) (Q : MarginMono N 0 r),
    ∃ x, Tendsto (fun k => mixLatC (ne_zero_of_two_le hN2) (CbF f bareO z) (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 x)

/-- `JointRP.ReflLim` at `CbF f bareO z`. DERIVED: `0` the plane. -/
def ReflLimF (hN2 : 2 ≤ N) (W : ConfFlow N) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (r : ℝ) : Prop :=
  (∀ P P' : TSepG (CbF f bareO z).Ix 0,
    Tendsto (fun k => rReadC (ne_zero_of_two_le hN2) (CbF f bareO z) 0 k P.1 P'.1)
      (ultra : Filter ℕ) (𝓝 (kernC (ne_zero_of_two_le hN2) (CbF f bareO z) 0 P P')))
  ∧ ∀ (P : TSepG (CbF f bareO z).Ix 0) (Q : MarginMono N 0 r),
    Tendsto (fun k => rMixC (ne_zero_of_two_le hN2) (CbF f bareO z) (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 (mixKF hN2 W f bareO z r P Q))

/-- `JointRP.jointRPK_of_reflLim` at `CbF f bareO z`. DERIVED: `0` the plane. -/
theorem jointRPK_of_reflLimF (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (hRL : ReflLimF hN2 W f bareO z r) :
    JointRPK (kernC (ne_zero_of_two_le hN2) (CbF f bareO z) 0) (mixKF hN2 W f bareO z r)
      (gramF hN2 W r) := by
  have hN := ne_zero_of_two_le hN2
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  refine jointRPK_of_tendsto
    (fun k P P' => rReadC hN (CbF f bareO z) 0 k P.1 P'.1)
    (fun k P Q => rMixC hN (CbF f bareO z) (Φ0 W) 0 k P.1 Q.1)
    (fun k Q Q' => latSF hN (Φ0 W) k (pairFam 0 Q.1 Q'.1))
    hRL.1 hRL.2
    (fun Q Q' => tendsto_contSF hN (Φ0 W) (ClaySUGap.uB hN W hU) (pairFam 0 Q.1 Q'.1))
    fun P P' s c => ?_
  have hUL := build_unifLocal (rhoD f z) (bareD f bareO)
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ c.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset c.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  filter_upwards [eventually_cMono_mem hN (CbF f bareO z) hUL P,
    eventually_cMono_mem hN (CbF f bareO z) hUL P', hQ] with k hP hP' hQk
  exact latJointC hN (CbF f bareO z) (Φ0 W) 0 k (fun Q : MarginMono N 0 r => Q.1) P.1 P'.1 s c
    hP hP' hQk

/-- `JointRP.reflLim_of_cov` at `CbF f bareO z`. DERIVED: `0` the plane. -/
theorem reflLim_of_covF (hN2 : 2 ≤ N) (W : ConfFlow N) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ) (r : ℝ)
    (hcov : ReflCovLat (CbF f bareO z) 0)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbF f bareO z)) (hMC : MixConvF hN2 W f bareO z r) :
    ReflLimF hN2 W f bareO z r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine ⟨fun P P' => ?_, fun P Q => ?_⟩
  · have h := (hCO.1 _ _ (adm_pairC (CbF f bareO z) P P')).const_mul
      (sgnC (CbF f bareO z) 0 P.1)
    refine h.congr fun k => ?_
    exact (rReadC_of_cov _ _ 0 hcov k P.1 P'.1).symm
  · obtain ⟨x, hx⟩ := hMC P Q
    have h := hx.const_mul (sgnC (CbF f bareO z) 0 P.1)
    have hlim : mixKF hN2 W f bareO z r P Q = sgnC (CbF f bareO z) 0 P.1 * x := by
      show sgnC (CbF f bareO z) 0 P.1 * limUnder (ultra : Filter ℕ) _ = _
      rw [hx.limUnder_eq]
    rw [hlim]
    refine h.congr fun k => ?_
    exact (rMixC_of_cov _ _ _ 0 hcov k P.1 Q.1).symm

/-- `CompositeLink.linkCPre_of_kernels` at `CbF f bareO z`. DERIVED: `0` the plane. -/
theorem linkCPre_of_kernelsF (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbF f bareO z))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (CbF f bareO z) 0) (mixKF hN2 W f bareO z r)
      (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CbF f bareO z) 0) (mixKF hN2 W f bareO z r)
      (gramF hN2 W r))
    (hMC : MixConvF hN2 W f bareO z r) :
    ∃ wC : TSepG (CbF f bareO z).Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys,
      LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
        (preTime (ne_zero_of_two_le hN2) W hU hphys) (CbF f bareO z) wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
        Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD f z) (Φ0 W) 0 k P.1 Q.1.1)
            (ultra : Filter ℕ) (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD f z) (Φ0 W) 0 P.1 Q.1.1))
          ∧ inner ℂ (LinkReduce.wOfC eI wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
            = (mixT (ne_zero_of_two_le hN2) (rhoD f z) (Φ0 W) 0 P.1 Q.1.1 : ℂ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨hG1, hG2, hG3⟩ := obsGen_flow (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)
  have hG : ∀ Q Q' : MarginMono N 0 r, inner ℂ (vO hN2 W hU hphys Q) (vO hN2 W hU hphys Q')
      = (gramF hN2 W r Q Q' : ℂ) := hG1
  have hG2' : ∀ (m : ℕ) (Q : MarginMono N 0 r),
      vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)
        = preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (vO hN2 W hU hphys Q) :=
    fun m Q => hG2 m Q _ rfl
  obtain ⟨w, hwX, hwK⟩ := exists_link (gramF hN2 W r) hG ((jointRP_iff_K _ hG).mpr hJ)
    ((approx_iff_K _ hG).mpr hA)
  refine ⟨w, ⟨fun P Q => ⟨hCO.1 _ _ (adm_pairC (CbF f bareO z) P Q), hwK P Q⟩, fun m P => ?_, ?_⟩,
    fun P Q => ?_⟩
  · refine eq_of_inner_eq hG3 fun Q => ?_
    calc inner ℂ (w (shiftT (ne_zero_of_two_le hN2) 0 m P)) (vO hN2 W hU hphys Q)
        = (mixKF hN2 W f bareO z r P (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q) : ℂ) := by
          rw [hwX]
          exact congrArg Complex.ofReal (mixKC_shift _ _ _ 0 m P Q.1)
      _ = inner ℂ (w P) (vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)) :=
          (hwX _ _).symm
      _ = inner ℂ (w P) (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m)
            (vO hN2 W hU hphys Q)) := by
          rw [hG2' m Q]
      _ = inner ℂ (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (w P))
            (vO hN2 W hU hphys Q) :=
          ((isSelfAdjoint_powT (a := stepT (ne_zero_of_two_le hN2) (Φ0 W)
            (preB (ne_zero_of_two_le hN2) W hU) 0
            (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0) 0)
            (dySpacing N m / dySpacing N 0)).isSymmetric (w P) (vO hN2 W hU hphys Q)).symm
  · have hvac : preVac (ne_zero_of_two_le hN2) W hU hphys
        = vO hN2 W hU hphys (emptyMargin N 0 r) := rfl
    refine eq_of_inner_eq hG3 fun Q => ?_
    rw [hvac, hG, hwX]
    exact congrArg Complex.ofReal (mixKC_empty _ _ _ 0 r Q.1)
  · have hT := tendsto_mixLatT (ne_zero_of_two_le hN2) (rhoD f z) (CbF f bareO z) eI
      (build_he1 _ _) (fun k α => build_he2 _ _ k α) (Φ0 W) 0 P Q.1.1
      (fun α => hMC (LinkReduce.monoAt eI P α) Q.1)
    have hmix : mixT (ne_zero_of_two_le hN2) (rhoD f z) (Φ0 W) 0 P.1 Q.1.1
        = ∑ α : Fin P.1.1 → Idx4, LinkReduce.coefAt P α
            * mixKC (ne_zero_of_two_le hN2) (CbF f bareO z) (Φ0 W) 0
              (LinkReduce.monoAt eI P α) Q.1.1 :=
      hT.limUnder_eq
    refine ⟨by rw [hmix]; exact hT, ?_⟩
    rw [hmix]
    unfold LinkReduce.wOfC
    rw [sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
    exact congrArg (fun x => ((LinkReduce.coefAt P α : ℝ) : ℂ) * x) (hwX _ Q.1)

end Generic

/-! ## 8. The capstone -/

section Capstone

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData
  MassGap.CompositeLink MassGap.JointRP

/-- The composites' mixed kernel at the averaged composites. DERIVED: `0` the plane. -/
abbrev mixKR (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) :
    TSepG (CbR N z).Ix 0 → MarginMono N 0 r → ℝ :=
  mixKF hN2 W (fR N) (bR N) z r

/-- **`JointRPK` at the averaged composites, from `CompOS` and `MixConvF` alone**: the lattice
covariance `reflCovLat_CbR` gives `ReflLimF` (`reflLim_of_covF`), which gives `JointRPK`
(`jointRPK_of_reflLimF`). DERIVED: `0` the plane. -/
theorem jointRPK_R (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z)) (hMC : MixConvF hN2 W (fR N) (bR N) z r) :
    JointRPK (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (mixKR hN2 W z r) (gramF hN2 W r) :=
  jointRPK_of_reflLimF hN2 W hU hphys (fR N) (bR N) z
    (reflLim_of_covF hN2 W (fR N) (bR N) z r (reflCovLat_CbR z) hCO hMC)

/-- **The SU capstone at the reflection-averaged composites, without `hJ`.** The tensor fields are
`fR N δ = reflAvg (ctau 0 (emono δ)) (bareF (emono δ))` and the bare fields
`bR N i = reflAvg (ctau 0 i.1) (bareF i.1)`. Discharged: `JointRPK` (`jointRPK_R`), `TiedB`
(`tiedB_R`), `NonGaussianT` from `hObs` (`NonGaussLink.nonGaussianT_rhoD_of_obs`), and the
composites' vectors with `LinkCPre` and the cross reading (`linkCPre_of_kernelsF`).

The inputs: `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hObs`,
`hWard`, `hCO`, `hA`, `hMC`; `hK`, `hWard` read `rhoD (fR N) z`, and `hCO`, `hA`, `hMC` the averaged
composites `CbR N z`. `hK` there is equivalent to `hK` at `fT` (`WardKernel.twoPointKernel_rhoD_congr`);
`hWard`, `hCO`, `hA`, `hMC` are different statements from those of `clayStatementAt_SU_best`, so this
capstone is an alternative to it.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_reflAvg (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (mixKR hN2 W z r) (gramF hN2 W r))
    (hMC : MixConvF hN2 W (fR N) (bR N) z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  obtain ⟨wC, hLC, hX⟩ := linkCPre_of_kernelsF hN2 W hU hphys (fR N) (bR N) z hCO
    (jointRPK_R hN2 W hU hphys z hCO hMC) hA hMC
  exact clayStatementAt_SU_data hN2 W ht hU hphys hfar (fR N) (bR N) z hz hzS hzP G hK hAF
    (NonGaussLink.nonGaussianT_rhoD_of_obs (ne_zero_of_two_le hN2) (fR N) z hObs) hWard
    (tiedB_R (ne_zero_of_two_le hN2)) hCO wC hLC hX

end Capstone

end MassGap.ReflAvg

end

#print axioms MassGap.ReflAvg.covDF_reflPot
#print axioms MassGap.ReflAvg.cval_reflPot
#print axioms MassGap.ReflAvg.ord_baseO
#print axioms MassGap.ReflAvg.ord_stepO
#print axioms MassGap.ReflAvg.mono_ordO
#print axioms MassGap.ReflAvg.classCfgO_refl
#print axioms MassGap.ReflAvg.classicalLead_refl_bareF
#print axioms MassGap.ReflAvg.reflAvg_refl
#print axioms MassGap.ReflAvg.lead_bareR
#print axioms MassGap.ReflAvg.Pm_rowsum
#print axioms MassGap.ReflAvg.Pm_parity
#print axioms MassGap.ReflAvg.tv_parity
#print axioms MassGap.ReflAvg.refl_Ecomb
#print axioms MassGap.ReflAvg.reflCovLat_CbR
#print axioms MassGap.ReflAvg.tiedB_R
#print axioms MassGap.ReflAvg.jointRPK_of_reflLimF
#print axioms MassGap.ReflAvg.reflLim_of_covF
#print axioms MassGap.ReflAvg.linkCPre_of_kernelsF
#print axioms MassGap.ReflAvg.jointRPK_R
#print axioms MassGap.ReflAvg.clayStatementAt_SU_reflAvg
