import Mathlib
import MassGap.ClayData

/-!
# MassGap.ObsLead — the classical lead of the observer's field, and the capstone at the bare tensors

`obs N = sym (plaqField q0)` is the plaquette density `1 − Re tr U_p / N` summed over the `384`
images of the plaquette `q0` under the axis permutations and reflections. This module proves its
classical leading term,

  `ClassicalLead (obs N).1 4 (fun A g => (16/N) · g² · ⟨trC, ffT g A⟩)`  (`classicalLead_obs`),

with `⟨trC, ffT g A⟩ = ∑_{μν} Re tr F_{μν}(0) F_{μν}(0)` (`trC_dot_ffT`), and from it the capstone
`clayStatementAt_SU_obs`.

## The plaquettes read by `obs`

* A reflection carries the plaquette density at `q` to the density at `ireflPlaq τ 0 q`
  (`GaugeInvariantAlgebra.ireflObs_iplaqObs`); so `plaqField q0 (reflAll s V)` is the density of the
  plaquette `rq s q0` of `V` (`plaqField_reflAll`).
* An axis permutation `e` carries the plaquette `((ρ, σ), x)` to `((e ρ, e σ), iaxisSite e x)`
  (`plaqG_iaxis`).
* So each of the `384` terms of `obs` is the density of a plaquette of `U` whose base site and
  ordered plane depend only on the group element (`obs_apply`). A reflection keeps the plane or
  transposes it (`plane_rq`), and `Re tr F_{σρ}F_{σρ} = Re tr F_{ρσ}F_{ρσ}` (`pFF_swap`).

## One plaquette on the classical configurations

`lead_plaqG`: for every ordered plane `(ρ, σ)` and base site `x`, the density of `U_p(x)` has
classical lead `g² Re tr F_{ρσ}(0)F_{ρσ}(0) / (2N)` at dimension `4`. The steps:

* unitarity: `wilsonDensity P − wilsonDensity 1 = Re tr((P − 1)ᴴ(P − 1)) / (2N)` (`density_sub`);
* `ClassicalLimit.latD_classCfg` and `ClassicalLimit.ord_covDF` at `ds = []`:
  `U_p(x) − 1 = a² G(a, a x)` with `G` smooth and `G(0, z) = i g F_{ρσ}(z)`;
* `F_{ρσ}(0)` is Hermitian for an admissible potential (`herm_F`), so
  `(i g F)ᴴ (i g F) = g² F F`, and the point `(a, a x) → (0, 0)` is the origin for every base
  site.

## The count

Each ordered pair `(μ, ν)`, `μ ≠ ν`, is `(e 0, e 1)` for two permutations `e` (`sum_perm01`), and
there are `16` reflection sets, so each ordered pair takes `32` of the `384` terms, each with lead
weight `1/(2N)`: `32/(2N) = 16/N` gives `(16/N) ∑_{μν}`.

## The capstone

`clayStatementAt_SU_obs` is `ClayData.clayStatementAt_SU_data` at the tensor fields
`fT N δ = bareF (emono δ)` and the bare fields `bT N i = bareF i.1`, with `TiedB` discharged by
`ClayData.tiedB_bareD_of_obs'` and `classicalLead_obs`. Its inputs are `hU`, `hphys` at one `r`,
`hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hNG`, `hWard`, `hCO`, `wC`, `hLC`, `hX`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the dimension of `tr F F`; `2` the power of `g` and the
two permutations per ordered plane; `16` the reflection sets and the normalisation of `ScalarTie`;
`0`, `1` the plane of `q0`, the origin and `a = 0`; `1/(2N)` from unitarity and the density's `1/N`.
-/

noncomputable section

namespace MassGap.ObsLead

open MassGap MassGap.ClayStatement MassGap.ClassicalLimit MassGap.InfiniteLattice
  MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments Filter
open scoped Topology Matrix ContDiff

variable {N : ℕ}

/-! ## 1. The plaquettes read by `obs` -/

section Plaquettes

/-- The plaquette density is the Wilson density of `plaqG`. DERIVED: no numeral. -/
theorem plaqField_eq (q : MassGap.GibbsSpec.IPlaq) (V : Cfg N) :
    (plaqField (N := N) q).1 V
      = MassGap.WilsonAction.wilsonDensity (plaqG V q.1.1 q.1.2 q.2) := by
  show MassGap.WilsonAction.wilsonDensity
      (MassGap.WilsonLattice.wilsonHol MassGap.GibbsSpec.ibd q V) = _
  congr 1
  simp only [MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, plaqG, mul_assoc]
  rfl

/-- The plaquette reflected in axis `τ` if `b`. DERIVED: `0` the reflection constant. -/
def rpq : Bool → Fin 4 → MassGap.GibbsSpec.IPlaq → MassGap.GibbsSpec.IPlaq
  | true, τ, q => MassGap.LatticeReflection.ireflPlaq τ 0 q
  | false, _, q => q

/-- DERIVED: `0` the reflection constant. -/
theorem plaqField_rpow (b : Bool) (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) (V : Cfg N) :
    (plaqField (N := N) q).1 (rpow b τ V) = (plaqField (rpq b τ q)).1 V := by
  cases b
  · rfl
  · show GaugeInvariantAlgebra.iplaqObs q (MassGap.LatticeReflection.ireflConf τ 0 V)
      = GaugeInvariantAlgebra.iplaqObs (MassGap.LatticeReflection.ireflPlaq τ 0 q) V
    rw [← GaugeInvariantAlgebra.ireflObs_iplaqObs]
    rfl

/-- The plaquette read through the reflections of `s`. DERIVED: `0`–`3` the axes. -/
def rq (s : Fin 4 → Bool) (q : MassGap.GibbsSpec.IPlaq) : MassGap.GibbsSpec.IPlaq :=
  rpq (s 3) 3 (rpq (s 2) 2 (rpq (s 1) 1 (rpq (s 0) 0 q)))

/-- **A reflected configuration reads the reflected plaquette.** DERIVED: no numeral. -/
theorem plaqField_reflAll (s : Fin 4 → Bool) (q : MassGap.GibbsSpec.IPlaq) (V : Cfg N) :
    (plaqField (N := N) q).1 (reflAll s V) = (plaqField (rq s q)).1 V := by
  unfold reflAll
  rw [plaqField_rpow, plaqField_rpow, plaqField_rpow, plaqField_rpow]
  rfl

/-- **A relabelled configuration reads the relabelled plaquette.** DERIVED: no numeral. -/
theorem plaqG_iaxis (e : Equiv.Perm (Fin 4)) (U : Cfg N) (ρ σ : Fin 4) (x : ISite) :
    plaqG (iaxisConf e U) ρ σ x = plaqG U (e ρ) (e σ) (iaxisSite e x) := by
  simp only [plaqG, iaxisConf, iaxisLink]
  rw [← ishift_iaxisSite, ← ishift_iaxisSite]

/-- **Each of the `384` terms of `obs` is the density of one plaquette of `U`**, its plane and base
site fixed by the group element. DERIVED: `384` terms. -/
theorem obs_apply (U : Cfg N) :
    (ClayData.obs N).1 U = ∑ gg : Equiv.Perm (Fin 4) × (Fin 4 → Bool),
      MassGap.WilsonAction.wilsonDensity (plaqG U (gg.1 (rq gg.2 q0).1.1) (gg.1 (rq gg.2 q0).1.2)
        (iaxisSite gg.1 (rq gg.2 q0).2)) := by
  rw [ClayData.obs_def, sym_apply]
  refine Finset.sum_congr rfl fun gg _ => ?_
  rw [plaqField_reflAll, plaqField_eq, plaqG_iaxis]

/-- A reflection keeps the plane of a plaquette or transposes it. DERIVED: no numeral. -/
theorem plane_irefl (pf : Fin 4 → Fin 4 → ℝ) (hpf : ∀ a b, pf a b = pf b a) (τ : Fin 4) (c : ℤ)
    (q : MassGap.GibbsSpec.IPlaq) :
    pf (MassGap.LatticeReflection.ireflPlaq τ c q).1.1 (MassGap.LatticeReflection.ireflPlaq τ c q).1.2
      = pf q.1.1 q.1.2 := by
  unfold MassGap.LatticeReflection.ireflPlaq
  split_ifs with h1 h2
  · rw [← h1]; exact hpf _ _
  · rw [← h2]; exact hpf _ _
  · rfl

/-- DERIVED: no numeral. -/
theorem plane_rpq (pf : Fin 4 → Fin 4 → ℝ) (hpf : ∀ a b, pf a b = pf b a) (b : Bool) (τ : Fin 4)
    (q : MassGap.GibbsSpec.IPlaq) : pf (rpq b τ q).1.1 (rpq b τ q).1.2 = pf q.1.1 q.1.2 := by
  cases b
  · rfl
  · exact plane_irefl pf hpf τ 0 q

/-- **The reflections of `s` keep the plane up to transposition.** DERIVED: no numeral. -/
theorem plane_rq (pf : Fin 4 → Fin 4 → ℝ) (hpf : ∀ a b, pf a b = pf b a) (s : Fin 4 → Bool)
    (q : MassGap.GibbsSpec.IPlaq) : pf (rq s q).1.1 (rq s q).1.2 = pf q.1.1 q.1.2 := by
  unfold rq
  rw [plane_rpq pf hpf, plane_rpq pf hpf, plane_rpq pf hpf, plane_rpq pf hpf]

end Plaquettes

/-! ## 2. The classical tensor on one plane -/

section Tensor

/-- `Re tr F_{ρσ}(0) F_{ρσ}(0)`. DERIVED: `0` the origin. -/
def pFF (g : ℝ) (A : GPot N) (ρ σ : Fin 4) : ℝ :=
  (Matrix.trace (Matrix.of (covDF g A ρ σ [] 0) * Matrix.of (covDF g A ρ σ [] 0))).re

/-- DERIVED: no numeral. -/
theorem pFF_swap (g : ℝ) (A : GPot N) (ρ σ : Fin 4) : pFF g A σ ρ = pFF g A ρ σ := by
  unfold pFF
  rw [ClayData.covDF_swap g A ρ σ 0,
    show ∀ X : Fin N → Fin N → ℂ, Matrix.of (-X) = -Matrix.of X from fun _ => rfl, neg_mul_neg]

/-- `F_{ρρ} = 0`. DERIVED: `0` the origin and the value. -/
theorem pFF_self (g : ℝ) (A : GPot N) (ρ : Fin 4) : pFF g A ρ ρ = 0 := by
  have h : covDF g A ρ ρ [] 0 = 0 := by
    simp [covDF, mcomm, show Matrix.of.symm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 from rfl]
  unfold pFF
  rw [h]
  simp

/-- **`⟨trC, ffT g A⟩ = ∑_{μν} Re tr F_{μν}(0) F_{μν}(0)`.** DERIVED: `0`–`3` the slots. -/
theorem trC_dot_ffT (g : ℝ) (A : GPot N) : trC ⬝ᵥ ffT g A = ∑ a, ∑ b, pFF g A a b := by
  unfold dotProduct
  rw [CompositesBuild.sum_idx4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [trC, ffT, pFF]
    · intro d _ hd
      simp [trC, hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [trC, hc]
  · simp

/-- **Each ordered pair of distinct axes is `(e 0, e 1)` for two permutations `e`.**

DERIVED: `2 = 2!` the permutations fixing `0` and `1`; `0`, `1` the first two axes. -/
theorem sum_perm01 (f : Fin 4 → Fin 4 → ℝ) (hf : ∀ a, f a a = 0) :
    ∑ e : Equiv.Perm (Fin 4), f (e 0) (e 1) = 2 * ∑ a, ∑ b, f a b := by
  rw [Fintype.sum_equiv (Equiv.Perm.decomposeFin (n := 3)) _
    (fun pq => f (Equiv.Perm.decomposeFin.symm pq 0) (Equiv.Perm.decomposeFin.symm pq 1))
    (fun e => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : ∀ σ : Equiv.Perm (Fin 3),
      Equiv.Perm.decomposeFin.symm (p, σ) (1 : Fin 4) = Equiv.swap 0 p (σ 0).succ :=
    fun σ => Equiv.Perm.decomposeFin_symm_apply_succ σ p 0
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, h1]
  rw [Fintype.sum_equiv (Equiv.Perm.decomposeFin (n := 2)) _
    (fun pq => f p (Equiv.swap 0 p (Equiv.Perm.decomposeFin.symm pq 0).succ))
    (fun e => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  have h2 : ∑ b, f p b = ∑ q : Fin 3, f p (Equiv.swap 0 p q.succ) := by
    rw [← Equiv.sum_comp (Equiv.swap 0 p) (f p), Fin.sum_univ_succ, Equiv.swap_apply_left, hf, zero_add]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Nat.factorial]

end Tensor

/-! ## 3. One plaquette on the classical configurations -/

section Analysis

open scoped Matrix.Norms.Operator

/-- **Unitarity**: `wilsonDensity P − wilsonDensity 1 = Re tr((P − 1)ᴴ(P − 1)) / (2N)`.

DERIVED: `2` from `(P − 1)ᴴ(P − 1) = 2 − P − Pᴴ`; `1` the unit. -/
theorem density_sub (P : MassGap.SUN.SU N) :
    MassGap.WilsonAction.wilsonDensity P - MassGap.WilsonAction.wilsonDensity (1 : MassGap.SUN.SU N)
      = (1 / (2 * (N : ℝ))) * (Matrix.trace (((P : Mat N) - 1)ᴴ * ((P : Mat N) - 1))).re := by
  have hu : star (P : Mat N) * (P : Mat N) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 P.2).1
  have e : ((P : Mat N) - 1)ᴴ * ((P : Mat N) - 1) = 1 + 1 - star (P : Mat N) - (P : Mat N) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, ← Matrix.star_eq_conjTranspose,
      sub_mul, mul_sub, mul_sub, hu]
    simp only [mul_one, one_mul]
    abel
  have ht : (Matrix.trace (star (P : Mat N))).re = (Matrix.trace (P : Mat N)).re := by
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
  rw [e]
  unfold MassGap.WilsonAction.wilsonDensity
  simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re, ht]
  rw [show ((1 : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = 1 from rfl]
  ring

/-- The conjugate transpose on `Fin N → Fin N → ℂ`, as a continuous real-linear map.

DERIVED: no numeral. -/
def cT : (Fin N → Fin N → ℂ) →L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X j i)
      map_add' := fun X Y => by
        funext i j
        simp [star_add]
      map_smul' := fun r X => by
        funext i j
        simp }

theorem of_cT (Z : Fin N → Fin N → ℂ) : Matrix.of (cT Z) = (Matrix.of Z)ᴴ := by
  ext i j
  rfl

/-- The derivative of a Hermitian-valued map is Hermitian. DERIVED: no numeral. -/
theorem cT_fderiv {f : (Fin 4 → ℝ) → Fin N → Fin N → ℂ} (hf : Differentiable ℝ f)
    (hc : ∀ y, cT (f y) = f y) (z v : Fin 4 → ℝ) : cT (fderiv ℝ f z v) = fderiv ℝ f z v := by
  have h1 : HasFDerivAt (fun y => cT (f y)) (cT.comp (fderiv ℝ f z)) z :=
    cT.hasFDerivAt.comp z (hf z).hasFDerivAt
  have h2 : (fun y => cT (f y)) = f := funext hc
  rw [h2] at h1
  have h3 := h1.fderiv
  calc cT (fderiv ℝ f z v) = (cT.comp (fderiv ℝ f z)) v := rfl
    _ = fderiv ℝ f z v := by rw [← h3]

/-- **`F_{ρσ}(0)` is Hermitian** for an admissible potential. DERIVED: `0` the origin. -/
theorem herm_F {A : GPot N} (hAdm : GPot.Adm A) (g : ℝ) (ρ σ : Fin 4) :
    (Matrix.of (covDF g A ρ σ [] 0))ᴴ = Matrix.of (covDF g A ρ σ [] 0) := by
  have hA : ContDiff ℝ ∞ A := contDiff_infty.2 hAdm.1
  have hdA : ∀ ν, Differentiable ℝ (fun y => A y ν) :=
    fun ν => (contDiff_pi.1 hA ν).differentiable (by simp)
  have hcA : ∀ ν y, cT (A y ν) = A y ν := fun ν y => by
    apply Matrix.of.injective
    rw [of_cT]
    exact (hAdm.2 y ν).1
  have hD : ∀ μ ν, (Matrix.of (fderiv ℝ (fun y => A y ν) 0 (dir μ)) : Mat N)ᴴ
      = Matrix.of (fderiv ℝ (fun y => A y ν) 0 (dir μ)) := fun μ ν => by
    rw [← of_cT, cT_fderiv (hdA ν) (hcA ν)]
  have hX : ∀ ν, (Matrix.of (A 0 ν) : Mat N)ᴴ = Matrix.of (A 0 ν) := fun ν => (hAdm.2 0 ν).1
  have hI : star (Complex.I * (g : ℂ)) = -(Complex.I * g) := by
    simp
  simp only [covDF, ← Matrix.of_add_of, ← Matrix.of_sub_of, ← Matrix.smul_of, of_mcomm,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hD, hX, hI]
  module

/-- `(i g F)ᴴ (i g F) = g² F F` for Hermitian `F`. DERIVED: `2` the power of `g`. -/
theorem igF_sq (g : ℝ) (M : Mat N) (hM : Mᴴ = M) :
    ((Complex.I * g) • M)ᴴ * ((Complex.I * g) • M) = ((g ^ 2 : ℝ) : ℂ) • (M * M) := by
  rw [Matrix.conjTranspose_smul, hM, smul_mul_smul_comm]
  congr 1
  apply Complex.ext <;> simp [pow_two]

/-- **The classical lead of one plaquette**: for every ordered plane `(ρ, σ)` and base site `x`,
`wilsonDensity U_p(x)` has lead `g² Re tr F_{ρσ}(0)F_{ρσ}(0)/(2N)` at dimension `4`.

DERIVED: `4` the dimension; `2` the power of `g` and of `a` in `U_p − 1`; `0` the origin. -/
theorem lead_plaqG (ρ σ : Fin 4) (x : ISite) :
    ClassicalLead (N := N) (fun U => MassGap.WilsonAction.wilsonDensity (plaqG U ρ σ x)) 4
      (fun A g => (1 / (2 * (N : ℝ))) * (g ^ 2 * pFF g A ρ σ)) := by
  intro A hAdm g U hU
  have hA : ContDiff ℝ ∞ A := contDiff_infty.2 hAdm.1
  obtain ⟨G, hG, eG, zG⟩ := ord_covDF hA g ρ σ []
  have hs : Continuous fun a : ℝ => site a x :=
    continuous_pi fun i => continuous_id.mul continuous_const
  have hGc : Continuous fun a : ℝ => G (a, site a x) := hG.continuous.comp (continuous_id.prodMk hs)
  let cTM : Mat N →ₗ[ℝ] Mat N :=
    { toFun := fun M => Mᴴ
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r M => by simp [Matrix.conjTranspose_smul] }
  let qf : Mat N → ℝ := fun M => (1 / (2 * (N : ℝ))) * (Matrix.trace (Mᴴ * M)).re
  have hqf : Continuous qf := by
    have h1 : Continuous fun M : Mat N => Mᴴ := cTM.continuous_of_finiteDimensional
    have h2 : Continuous fun M : Mat N => Mᴴ * M := h1.mul continuous_id
    have h3 := ((Matrix.traceLinearMap (Fin N) ℝ ℂ).continuous_of_finiteDimensional).comp h2
    exact continuous_const.mul (Complex.continuous_re.comp h3)
  have hlim : Tendsto (fun a => qf (G (a, site a x))) (𝓝[>] (0 : ℝ))
      (𝓝 (qf (G (0, site 0 x)))) :=
    ((hqf.comp hGc).tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : qf (G (0, site 0 x)) = (1 / (2 * (N : ℝ))) * (g ^ 2 * pFF g A ρ σ) := by
    have hz : site 0 x = 0 := by
      funext i
      simp [site]
    rw [hz, zG]
    simp only [qf]
    rw [igF_sq g _ (herm_F hAdm g ρ σ), Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rfl
  beta_reduce
  rw [← h0]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : (0 : ℝ) < a := ha
  have hP : ((plaqG (U a) ρ σ x : MassGap.SUN.SU N) : Mat N) - 1 = (a ^ 2) • G (a, site a x) := by
    have h := latD_classCfg (hU a ha') ρ σ [] x
    rw [eG] at h
    exact h
  have hone : plaqG (fun _ => (1 : MassGap.SUN.SU N)) ρ σ x = 1 := by
    simp [plaqG]
  rw [hone, density_sub, hP]
  simp only [qf, Matrix.conjTranspose_smul, star_trivial, smul_mul_smul_comm, Matrix.trace_smul,
    Complex.real_smul, Complex.re_ofReal_mul]
  field_simp

end Analysis

/-! ## 4. The classical lead of `obs` -/

/-- **The count**: the `384` plaquette leads sum to `(16/N) g² ⟨trC, ffT g A⟩`.

DERIVED: `16` the reflection sets; `2` the permutations per ordered plane; `1/(2N)` as in
`lead_plaqG`. -/
theorem sum_leads (A : GPot N) (g : ℝ) :
    ∑ gg : Equiv.Perm (Fin 4) × (Fin 4 → Bool), (1 / (2 * (N : ℝ))) *
        (g ^ 2 * pFF g A (gg.1 (rq gg.2 q0).1.1) (gg.1 (rq gg.2 q0).1.2))
      = (16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A)) := by
  have hplane : ∀ gg : Equiv.Perm (Fin 4) × (Fin 4 → Bool),
      pFF g A (gg.1 (rq gg.2 q0).1.1) (gg.1 (rq gg.2 q0).1.2) = pFF g A (gg.1 0) (gg.1 1) :=
    fun gg => plane_rq (fun a b => pFF g A (gg.1 a) (gg.1 b)) (fun a b => pFF_swap g A _ _) gg.2 q0
  simp only [hplane]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_perm01 (fun a b => pFF g A a b) (pFF_self g A), trC_dot_ffT]
  push_cast
  ring

/-- **The classical lead of the observer's field**: `(obs N)(U)` has lead
`(16/N) g² ⟨trC, ffT g A⟩ = (16/N) g² ∑_{μν} Re tr F_{μν}(0) F_{μν}(0)` at dimension `4`.

DERIVED: `4` the dimension; `2` the power of `g`; `16` as in `sum_leads`. -/
theorem classicalLead_obs :
    ClassicalLead (ClayData.obs N).1 4
      (fun A g => (16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A))) := by
  have hs := classicalLead_sum (N := N)
    (Finset.univ : Finset (Equiv.Perm (Fin 4) × (Fin 4 → Bool))) (fun _ => 1)
    (fun gg U => MassGap.WilsonAction.wilsonDensity (plaqG U (gg.1 (rq gg.2 q0).1.1)
      (gg.1 (rq gg.2 q0).1.2) (iaxisSite gg.1 (rq gg.2 q0).2)))
    (fun gg A g => (1 / (2 * (N : ℝ))) *
      (g ^ 2 * pFF g A (gg.1 (rq gg.2 q0).1.1) (gg.1 (rq gg.2 q0).1.2))) 4
    (fun gg _ => lead_plaqG _ _ _)
  intro A hA g U hU
  have h := hs A hA g U hU
  simp only [one_mul, sum_leads] at h
  refine h.congr fun a => ?_
  simp only [obs_apply]

/-! ## 5. The capstone at the bare tensor fields -/

section Capstone

open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayWiring
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ClayData

/-- The tensor fields `bareF (emono δ)`, `−Re tr(latD δ₀δ₁ · latD δ₂δ₃)` at the origin.

DERIVED: no numeral. -/
abbrev fT (N : ℕ) : Idx4 → LField (MassGap.SUN.SU N) := fun δ => ClassicalLimit.bareF (emono δ)

/-- The bare fields `bareF i.1` of the classical monomials. DERIVED: no numeral. -/
abbrev bT (N : ℕ) : Ix0 → LField (MassGap.SUN.SU N) := fun i => ClassicalLimit.bareF i.1

/-- **`TiedB` at the bare tensor fields**, from `classicalLead_obs`
(`ClayData.tiedB_bareD_of_obs'`). DERIVED: `0` the excluded colour count. -/
theorem tiedB_obs (hN : N ≠ 0) : TiedB (bareD (fT N) (bT N)) :=
  tiedB_bareD_of_obs' hN classicalLead_obs

/-- **`ClayData.clayStatementAt_SU_data` at the bare tensor fields**: `f = fT N`
(`f δ = bareF (emono δ)`), `bareO = bT N` (`bareF i.1`), with `TiedB (bareD f bareO)` discharged by
`tiedB_obs`.

The inputs left: `hU`, `hphys` at one `r`, `hfar : RunSeed N`, the channel factors `z` with `hz`,
`hzS`, `hzP`, the kernel `G` with `hK`, `hAF`, `hNG`, `hWard`, `hCO`, `wC`, `hLC`, `hX`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_obs (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (wC : TSepG (build (rhoD (fT N) z) (bareD (fT N) (bT N))).Ix 0 →
      preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys)
      (build (rhoD (fT N) z) (bareD (fT N) (bT N))) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P)
            (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_data hN2 W ht hU hphys hfar (fT N) (bT N) z hz hzS hzP G hK hAF hNG
    hWard (tiedB_obs (ne_zero_of_two_le hN2)) hCO wC hLC hX

end Capstone

end MassGap.ObsLead

end

#print axioms MassGap.ObsLead.obs_apply
#print axioms MassGap.ObsLead.sum_perm01
#print axioms MassGap.ObsLead.density_sub
#print axioms MassGap.ObsLead.herm_F
#print axioms MassGap.ObsLead.lead_plaqG
#print axioms MassGap.ObsLead.sum_leads
#print axioms MassGap.ObsLead.classicalLead_obs
#print axioms MassGap.ObsLead.tiedB_obs
#print axioms MassGap.ObsLead.clayStatementAt_SU_obs
