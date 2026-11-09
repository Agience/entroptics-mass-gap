import Mathlib
import MassGap.ConsolidatedRoot

/-!
# MassGap.LinkAlongG — the composites' link at any reflection-positive schedule

`CompositesRen.linkCPreG_of_kernels` builds the composites' vectors in the pre-observer's space, with
`LinkCPre` and the cross reading, at `SU(N)` and the state `stateK` of the two-loop schedule. Its proof
reads the state only through four properties: reflection positivity at the plane `x_τ = 0`, reflection
invariance, dyadic translation invariance and the dyadic spacing identity, the four fields of
`FlowG.SchedOS`. This module states the chain over any gauge group `G` and any schedule `S` with
`SchedOS S`, and instantiates it along every coupling tower of `SU(N)` (`MeasuredSpacing.schedOS_alongG`).
Declarations are in the namespace `MassGap.LinkAlongG`.

Each `SU(N)` declaration on the left has the schedule form on the right:

* `JointRP.latJoint_nonneg`, `latJointC`: `latJoint_nonnegG`, `latJointCG`;
* `JointRP.cMono`, `rReadC`, `rMixC`, `CompositeLink.mixLatC`, `mixKC`: `cMonoG`, `rReadCG`, `rMixCG`,
  `mixLatCG`, `mixKCG`;
* `JointRP.UnifLocal`, `eventually_cMono_mem`, `eventually_flow_mem`: `UnifLocalG`,
  `eventually_cMono_memG`, `eventually_flow_memG`;
* `JointRP.ReflCovLat`, `rReadC_of_cov`, `rMixC_of_cov`: `ReflCovLatG`, `rReadCG_of_cov`,
  `rMixCG_of_cov`; `MixConvRP.mixLatC_sq_le`: `mixLatCG_sq_le`;
* `CompositeLink.mixKC_shift`, `mixKC_empty`, `tendsto_mixLatT`, `adm_pairC`: `mixKCG_shift`,
  `mixKCG_empty`, `tendsto_mixLatTG`, `adm_pairCG`;
* `CompositesRen.mixConvG_of_cov`, `reflLimG_of_cov`, `jointRPKG_of_reflLim`, `linkCPreG_of_kernels`:
  `mixConvCG_of_cov`, `reflLimCG_of_cov`, `jointRPKCG_of_reflLim`, `linkCPreG_of_kernelsG`;
  `linkCPreG_of_approx` composes the four.

The observer side is the flowed reconstruction `TimeGroupG.FlowHG` of any flow `Φ` with a uniform bound
and positivity beyond the margin `r`: its vectors `gvecTG` have Gram matrix `kernFG`
(`ObserverLinkedG.inner_gvecTG_eq`), are moved by `timeTG (S.a m)` (`TimeGroupG.timeTG_dyadic`,
`stepTG_gvecTG`) and span a dense subspace (`ClayStatement.span_single_dense`).

## Along a tower

`linkAlong`: along every coupling tower `βs` of `SU(N)`, at the witnesses of `ConsolidatedRoot`
(observer `obsW`, mixing `rhoZ`, composites `csZ`), the class moments `hU`, the physical range,
`ConvCG` of the composites and `ApproxK` of the three kernels along `βs` (`ApproxAlong`) give the link
`wC` with `LinkCPreG` and the cross reading: the clauses `wC`, `hLC`, `hX` of
`ConsolidatedRoot.OpenAlong`. Uniform locality and lattice reflection covariance of the composites are
state-free (`CompositesRen.unifLocal_buildRen`, `CompositesRen.reflCovLat_CRen`).

DERIVED (module-wide): `0` the plane, the reflection constant and the signs; `1` the unit, the unit step
and the sign; `2` the cross-term factor, the square and the least rank; `0`, `1`, `2`, `3` the index
slots of `he1`; `4` the dimension; `π` in `π/N` the angle of the centre of `SU(N)`; `12` a sufficient
bound on `c`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LinkAlongG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG MassGap.TimeGroupG
  MassGap.ObserverLinkedG MassGap.CompReduceG MassGap.ClayGFinal Filter
open MassGap.CompositeLink (JointRPK ApproxK exists_link jointRP_iff_K approx_iff_K eq_of_inner_eq xL
  xL_single)
open MassGap.ContinuumFlow (gForm gForm_single)
open MassGap.JointRP (rform rform_expand jointRPK_of_tendsto)
open scoped Topology

/-! ## 1. The lattice joint inequality and the readings -/

section Readings

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable (S : Sched G)

/-- **The lattice joint inequality** at step `k` of a schedule with `SchedOS S`: for `A`, `A'` and
the `V_Q` in the half-space algebra of `x_τ = 0`, the joint form of `rform (S.ν k) θ` is
non-negative. DERIVED: `0` the plane, the reflection constant and the sign; `2` the cross-term
factor and the square. -/
theorem latJoint_nonnegG (hS : SchedOS S) (k : ℕ) (τ : Fin 4) {M : Type} (A A' : C(IConf G, ℝ))
    (V : M → C(IConf G, ℝ)) (t : ℝ) (c : M →₀ ℝ)
    (hA : A ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hA' : A' ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hV : ∀ Q ∈ c.support, V Q ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    let B := rform (S.ν k) (LatticeReflection.ireflObs τ 0)
    0 ≤ B A A + 2 * t * B A A' + t ^ 2 * B A' A' - 2 * xL (fun Q => B A (V Q)) c
        - 2 * t * xL (fun Q => B A' (V Q)) c + gForm (fun Q Q' => B (V Q) (V Q')) c c := by
  intro B
  have hs : ∀ x y, B x y = B y x := fun x y => refl_pair_symmG (S.ν k) τ (hS.refl k τ 0) x y
  rw [← rform_expand B hs]
  have hY : A + t • A' - c.sum (fun Q a => a • V Q)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
    refine Submodule.sub_mem _ (Submodule.add_mem _ hA (Submodule.smul_mem _ _ hA')) ?_
    exact Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hV Q hQ)
  exact hS.rp k τ _ hY

/-- **A monomial of composites as a monomial of smeared fields** at step `k`: the fields `cFieldG`.
DERIVED: no numeral. -/
def cMonoG (C : CompositesG G) (k : ℕ) (P : TMonoG C.Ix) : MonoG G :=
  ⟨P.1, fun i => cFieldG S C k (P.2 i)⟩

/-- **The reading with the composites of `P` reflected as lattice fields.** DERIVED: no numeral. -/
def rReadCG (C : CompositesG G) (τ : Fin 4) (k : ℕ) (P P' : TMonoG C.Ix) : ℝ :=
  latSG S k (pairFamG τ (cMonoG S C k P) (cMonoG S C k P'))

/-- **The mixed reading with `P` reflected as lattice fields** against the flowed fields of `Q`.
DERIVED: no numeral. -/
def rMixCG (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P : TMonoG C.Ix) (Q : MonoG G) :
    ℝ :=
  latSG S k (pairFamG τ (cMonoG S C k P) (Φ.mono k Q))

/-- **The mixed lattice reading of the composites**: test functions of `P` reflected, fields of `Q`
flowed by `Φ`. DERIVED: no numeral. -/
def mixLatCG (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P : TMonoG C.Ix)
    (Q : MonoG G) : ℝ :=
  latSG S k (Sum.elim (fun i => cFieldG S C k ((P.2 i).1, (P.2 i).2.reflect τ))
    (fun j => Φ.field k (Q.2 j)))

/-- **The mixed kernel of the composites** `sgn(P) · lim_ultra mixLatCG(P, Q)`. DERIVED: no numeral. -/
def mixKCG (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (P : TSepG C.Ix τ) (Q : MonoG G) : ℝ :=
  sgnCG C τ P.1 * limUnder (ultra : Filter ℕ) (fun k => mixLatCG S C Φ τ k P.1 Q)

/-- DERIVED: no numeral. -/
theorem rReadCG_eq (C : CompositesG G) (τ : Fin 4) (k : ℕ) (P P' : TMonoG C.Ix) :
    rReadCG S C τ k P P' = rform (S.ν k) (LatticeReflection.ireflObs τ 0)
      (prodSmearG (S.a k) (cMonoG S C k P)) (prodSmearG (S.a k) (cMonoG S C k P')) :=
  latSG_pairFamG S k τ _ _

/-- DERIVED: no numeral. -/
theorem rMixCG_eq (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (P : TMonoG C.Ix)
    (Q : MonoG G) :
    rMixCG S C Φ τ k P Q = rform (S.ν k) (LatticeReflection.ireflObs τ 0)
      (prodSmearG (S.a k) (cMonoG S C k P)) (prodSmearG (S.a k) (Φ.mono k Q)) :=
  latSG_pairFamG S k τ _ _

/-- DERIVED: no numeral. -/
theorem latSFG_pair_eq (Φ : GFlow G) (τ : Fin 4) (k : ℕ) (Q Q' : MonoG G) :
    latSFG S Φ.map k (pairFamG τ Q Q') = rform (S.ν k) (LatticeReflection.ireflObs τ 0)
      (prodSmearG (S.a k) (Φ.mono k Q)) (prodSmearG (S.a k) (Φ.mono k Q')) :=
  (latSFG_pairFamG S Φ τ k Q Q').trans (latSG_pairFamG S k τ _ _)

/-- **The lattice joint inequality of the mixed family** at step `k`, under half-space membership.
DERIVED: `0` the plane and the sign; `2` the cross-term factor and the square. -/
theorem latJointCG (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ)
    {M : Type} (q : M → MonoG G) (P P' : TMonoG C.Ix) (t : ℝ) (c : M →₀ ℝ)
    (hP : prodSmearG (S.a k) (cMonoG S C k P) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hP' : prodSmearG (S.a k) (cMonoG S C k P') ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hQ : ∀ Q ∈ c.support, prodSmearG (S.a k) (Φ.mono k (q Q))
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    0 ≤ rReadCG S C τ k P P + 2 * t * rReadCG S C τ k P P' + t ^ 2 * rReadCG S C τ k P' P'
      - 2 * xL (fun Q => rMixCG S C Φ τ k P (q Q)) c - 2 * t * xL (fun Q => rMixCG S C Φ τ k P' (q Q)) c
      + gForm (fun Q Q' => latSFG S Φ.map k (pairFamG τ (q Q) (q Q'))) c c := by
  simp only [rReadCG_eq, rMixCG_eq, latSFG_pair_eq]
  exact latJoint_nonnegG S hS k τ _ _ (fun Q => prodSmearG (S.a k) (Φ.mono k (q Q))) t c hP hP' hQ

/-- **Uniform locality of the renormalized composites**: each `ren k i` is local on one set of links
for every `k`. DERIVED: no numeral. -/
def UnifLocalG (C : CompositesG G) : Prop :=
  ∀ i, ∃ T : Finset ILink, ∀ k, IsLocalOn T ((C.ren k i).1 : IConf G → ℝ)

/-- **A separated positive-time monomial of uniformly local composites is eventually in the
half-space algebra.** DERIVED: `0` the plane. -/
theorem eventually_cMono_memG (C : CompositesG G) (hUL : UnifLocalG C) {τ : Fin 4}
    (P : TSepG C.Ix τ) :
    ∀ᶠ k in atTop, prodSmearG (S.a k) (cMonoG S C k P.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
  obtain ⟨-, d, hd, hpos, -⟩ := P.2
  have hall : ∀ᶠ k in atTop, ∀ i : Fin P.1.1,
      smear (S.a k) (cFieldG S C k (P.1.2 i)).1.1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
    refine Filter.eventually_all.mpr fun i => ?_
    obtain ⟨T, hT⟩ := hUL (P.1.2 i).1
    obtain ⟨D, hD⟩ := exists_depth τ T
    have ht : Tendsto (fun k => S.a k * (D : ℝ)) atTop (𝓝 0) := by
      simpa using S.a_lim.mul_const (D : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds hd)] with k hk
    exact smear_mem_halfSpaceAlg (S.a_pos k) τ (isLocalOn_sub_const (hT k) _) hD hk.le _ (hpos i)
  filter_upwards [hall] with k hk
  exact HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ fun i _ => hk i

/-- **A margin monomial is eventually in the half-space algebra** under `PosPreserving`.
DERIVED: `0` the plane. -/
theorem eventually_flow_memG (Φ : GFlow G) {τ : Fin 4} {r : ℝ} (hpos : Φ.PosPreserving S τ r)
    (Q : MarginMonoG G τ r) :
    ∀ᶠ k in atTop, prodSmearG (S.a k) (Φ.mono k Q.1) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
  obtain ⟨d, hd, hrd, hP⟩ := Q.2
  have hall : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1,
      smear (S.a k) (Φ.map k (Q.1.2 i).1).1 (Q.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 :=
    Filter.eventually_all.mpr fun i => hpos (Q.1.2 i).1 (Q.1.2 i).2 d hd hrd (hP i)
  filter_upwards [hall] with k hk
  exact HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ fun i _ => hk i

end Readings

/-! ## 2. Lattice reflection covariance and the Cauchy–Schwarz bound -/

section Covariance

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable (S : Sched G)

/-- **Lattice reflection covariance of the renormalized composites**:
`θ (ren k i) = (−1)^{ctau τ (cl i)} · ren k i` at every step. DERIVED: `1` the sign. -/
def ReflCovLatG (C : CompositesG G) (τ : Fin 4) : Prop :=
  ∀ k i, ((C.ren k i).refl τ).1 = ((-1 : ℝ) ^ ctau τ (C.cl i)) • (C.ren k i).1

/-- Smearing is homogeneous in the field. DERIVED: `0` the sign of `a`. -/
theorem smear_smulG {a : ℝ} (ha : 0 < a) (s : ℝ) (F : C(IConf G, ℝ)) (f : TestFn) :
    smear a (s • F) f = s • smear a F f := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha (s • F) f hf (Finset.Subset.refl _),
    smear_eq_sum ha F f hf (Finset.Subset.refl _), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_smul, smul_comm]

/-- **The connected field inherits the covariance** in a reflection-invariant state.
DERIVED: `1` the sign. -/
theorem refl_sub_covG (hS : SchedOS S) (k : ℕ) (τ : Fin 4) (O : LField G) (n : ℕ)
    (h : (O.refl τ).1 = ((-1 : ℝ) ^ n) • O.1) :
    ((O.sub (S.ν k O.1)).refl τ).1 = ((-1 : ℝ) ^ n) • (O.sub (S.ν k O.1)).1 := by
  have hinv : S.ν k (LatticeReflection.ireflObs τ 0 O.1) = S.ν k O.1 := hS.refl k τ 0 O.1
  rw [show LatticeReflection.ireflObs τ 0 O.1 = (O.refl τ).1 from rfl, h,
    MassGap.DLRLimit.State.map_smul] at hinv
  rw [LField.refl_sub]
  show (O.refl τ).1 - S.ν k O.1 • (1 : C(IConf G, ℝ))
    = ((-1 : ℝ) ^ n) • (O.1 - S.ν k O.1 • (1 : C(IConf G, ℝ)))
  rw [h, smul_sub, smul_smul, hinv]

/-- **A reading with factorwise scalars.** DERIVED: no numeral. -/
theorem latSG_scale (k : ℕ) {ι : Type} [Fintype ι] (F F' : ι → SFieldG G) (σ : ι → ℝ)
    (hF : ∀ x, smear (S.a k) (F x).1.1 (F x).2 = σ x • smear (S.a k) (F' x).1.1 (F' x).2) :
    latSG S k F = (∏ x, σ x) * latSG S k F' := by
  unfold latSG
  rw [Finset.prod_congr rfl (fun x _ => hF x), ContinuumFlow.prod_smul_eq, (S.ν k).map_smul]

/-- The smeared reflected connected composite under covariance. DERIVED: `1` the sign. -/
theorem smear_refl_cFieldG (hS : SchedOS S) (C : CompositesG G) (τ : Fin 4)
    (hcov : ReflCovLatG C τ) (k : ℕ) (p : CDatumG C) :
    smear (S.a k) (sreflG τ (cFieldG S C k p)).1.1 (sreflG τ (cFieldG S C k p)).2
      = ((-1 : ℝ) ^ ctau τ (C.cl p.1))
        • smear (S.a k) (cFieldG S C k (p.1, p.2.reflect τ)).1.1 (p.2.reflect τ) := by
  show smear (S.a k) (((C.ren k p.1).sub (S.ν k (C.ren k p.1).1)).refl τ).1 (p.2.reflect τ) = _
  rw [refl_sub_covG S hS k τ _ _ (hcov k p.1), smear_smulG (S.a_pos k)]
  rfl

/-- **Under lattice covariance the reflected reading is the tree's**: `rReadCG = sgnCG · latCG`.
DERIVED: no numeral. -/
theorem rReadCG_of_cov (hS : SchedOS S) (C : CompositesG G) (τ : Fin 4) (hcov : ReflCovLatG C τ)
    (k : ℕ) (P P' : TMonoG C.Ix) :
    rReadCG S C τ k P P' = sgnCG C τ P * latCG S C k (pairCG C τ P P') := by
  unfold rReadCG latCG
  rw [latSG_scale S k (pairFamG τ (cMonoG S C k P) (cMonoG S C k P'))
      (fun x => cFieldG S C k (pairCG C τ P P' x))
      (Sum.elim (fun i => (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)) fun _ => 1) ?_]
  · rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
    rfl
  · rintro (i | j)
    · exact smear_refl_cFieldG S hS C τ hcov k (P.2 i)
    · exact (one_smul ℝ _).symm

/-- **Under lattice covariance the reflected mixed reading is the tree's**:
`rMixCG = sgnCG · mixLatCG`. DERIVED: no numeral. -/
theorem rMixCG_of_cov (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4)
    (hcov : ReflCovLatG C τ) (k : ℕ) (P : TMonoG C.Ix) (Q : MonoG G) :
    rMixCG S C Φ τ k P Q = sgnCG C τ P * mixLatCG S C Φ τ k P Q := by
  unfold rMixCG mixLatCG
  rw [latSG_scale S k (pairFamG τ (cMonoG S C k P) (Φ.mono k Q))
      (Sum.elim (fun i => cFieldG S C k ((P.2 i).1, (P.2 i).2.reflect τ))
        (fun j => Φ.field k (Q.2 j)))
      (Sum.elim (fun i => (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)) fun _ => 1) ?_]
  · rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
    rfl
  · rintro (i | j)
    · exact smear_refl_cFieldG S hS C τ hcov k (P.2 i)
    · exact (one_smul ℝ _).symm

/-- `sgnCG² = 1`. DERIVED: `1` the unit; `2` the square. -/
theorem sgnCG_sq (C : CompositesG G) (τ : Fin 4) (P : TMonoG C.Ix) : sgnCG C τ P ^ 2 = 1 := by
  unfold sgnCG
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  simp

/-- `|sgnCG| = 1`. DERIVED: `1` the unit. -/
theorem abs_sgnCG (C : CompositesG G) (τ : Fin 4) (P : TMonoG C.Ix) : |sgnCG C τ P| = 1 := by
  have h := sgnCG_sq C τ P
  have h2 : |sgnCG C τ P| ^ 2 = 1 := by rw [sq_abs, h]
  have h0 := abs_nonneg (sgnCG C τ P)
  exact le_antisymm (by nlinarith) (by nlinarith)

/-- **The reflected Cauchy–Schwarz bound at one step.** DERIVED: `0` the plane; `2` the square. -/
theorem rMixCG_sq_le (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (k : ℕ)
    (P : TMonoG C.Ix) (Q : MonoG G)
    (hP : prodSmearG (S.a k) (cMonoG S C k P) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hQ : prodSmearG (S.a k) (Φ.mono k Q) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    rMixCG S C Φ τ k P Q ^ 2 ≤ latSFG S Φ.map k (pairFamG τ Q Q) * rReadCG S C τ k P P := by
  have h : ∀ s : ℝ, 0 ≤ rReadCG S C τ k P P + 2 * s * (-rMixCG S C Φ τ k P Q)
      + s ^ 2 * latSFG S Φ.map k (pairFamG τ Q Q) := fun s => by
    have hJ := latJointCG S hS C Φ τ k (fun _ : Unit => Q) P P 0 (Finsupp.single () s) hP hP
      (fun _ _ => hQ)
    simp only [xL_single, gForm_single] at hJ
    linarith
  have := CompositeLink.sq_le_of_quad h
  rwa [neg_sq] at this

/-- **The lattice Cauchy–Schwarz bound of the mixed reading** for reflection-covariant composites.
DERIVED: `0` the plane; `2` the square. -/
theorem mixLatCG_sq_le (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4)
    (hcov : ReflCovLatG C τ) (k : ℕ) (P : TMonoG C.Ix) (Q : MonoG G)
    (hP : prodSmearG (S.a k) (cMonoG S C k P) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0)
    (hQ : prodSmearG (S.a k) (Φ.mono k Q) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    mixLatCG S C Φ τ k P Q ^ 2
      ≤ |latCG S C k (pairCG C τ P P)| * |latSFG S Φ.map k (pairFamG τ Q Q)| := by
  have h := rMixCG_sq_le S hS C Φ τ k P Q hP hQ
  rw [rMixCG_of_cov S hS C Φ τ hcov k P Q, rReadCG_of_cov S hS C τ hcov k P P, mul_pow,
    sgnCG_sq, one_mul] at h
  calc mixLatCG S C Φ τ k P Q ^ 2
      ≤ latSFG S Φ.map k (pairFamG τ Q Q) * (sgnCG C τ P * latCG S C k (pairCG C τ P P)) := h
    _ ≤ |latSFG S Φ.map k (pairFamG τ Q Q) * (sgnCG C τ P * latCG S C k (pairCG C τ P P))| :=
        le_abs_self _
    _ = |latCG S C k (pairCG C τ P P)| * |latSFG S Φ.map k (pairFamG τ Q Q)| := by
        rw [abs_mul, abs_mul, abs_sgnCG, one_mul, mul_comm]

end Covariance

/-! ## 3. The mixed kernel: shift, vacuum and the sector -/

section Mixed

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable (S : Sched G)

/-- **The dyadic step is symmetric for the mixed reading** from step `m` on.
DERIVED: `1` the unit step. -/
theorem mixLatCG_shift (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) {m k : ℕ}
    (hk : m ≤ k) (P : TSepG C.Ix τ) (Q : MonoG G) :
    mixLatCG S C Φ τ k (shiftTG S τ m P).1 Q
      = mixLatCG S C Φ τ k P.1 (monoShiftG (timeVecG S m τ 1) Q) := by
  have hT := hS.trans _ (Sum.elim (fun i => cFieldG S C k ((P.1.2 i).1, (P.1.2 i).2.reflect τ))
      (fun j => Φ.field k ((Q.2 j).1, (Q.2 j).2.translate (timeVecG S m τ 1)))) m k hk
    (axisVec τ (-1))
  unfold mixLatCG
  refine Eq.trans ?_ hT
  refine congrArg (latSG S k) (funext fun s => ?_)
  rcases s with i | j
  · refine Prod.ext rfl ?_
    show ((P.1.2 i).2.translate (timeVecG S m τ 1)).reflect τ
      = ((P.1.2 i).2.reflect τ).translate (timeVecG S m τ (-1))
    rw [TestFn.reflect_translate, reflR_timeVecG]
  · refine Prod.ext rfl ?_
    show (Q.2 j).2 = ((Q.2 j).2.translate (timeVecG S m τ 1)).translate (timeVecG S m τ (-1))
    rw [TestFn.translate_translate, timeVecG_add, add_neg_cancel, timeVecG_zero,
      TestFn.translate_zero]

/-- **The dyadic step is symmetric for the mixed kernel.** DERIVED: `1` the unit step. -/
theorem mixKCG_shift (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (m : ℕ)
    (P : TSepG C.Ix τ) (Q : MonoG G) :
    mixKCG S C Φ τ (shiftTG S τ m P) Q = mixKCG S C Φ τ P (monoShiftG (timeVecG S m τ 1) Q) := by
  unfold mixKCG
  have hs : sgnCG C τ (shiftTG S τ m P).1 = sgnCG C τ P.1 := rfl
  rw [hs]
  congr 1
  exact limUnder_congr_ultra ((eventually_ge_atTop m).mono fun k hk =>
    mixLatCG_shift S hS C Φ τ hk P Q)

/-- **The empty composite monomial reads the flowed kernel.** DERIVED: no numeral. -/
theorem mixKCG_empty (C : CompositesG G) (Φ : GFlow G) (τ : Fin 4) (r : ℝ) (Q : MonoG G) :
    mixKCG S C Φ τ (emptyG C.Ix τ) Q = kernFG S Φ τ (emptyMarginG G τ r).1 Q := by
  have hs : sgnCG C τ (emptyG C.Ix τ).1 = 1 := Fin.prod_univ_zero _
  unfold mixKCG kernFG contSFG
  rw [hs, one_mul]
  congr 1
  funext k
  unfold mixLatCG latSFG
  refine congrArg (latSG S k) (funext fun s => ?_)
  rcases s with i | j
  · exact i.elim0
  · rfl

/-- **A reading with composites and other fields expands over the basis** of the composites'
fields. DERIVED: no numeral. -/
theorem latSG_elim_expand (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ)
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] (α : ι → Idx4) (f : ι → TestFn)
    (F : κ → SFieldG G) :
    latSG S k (Sum.elim (fun i => cFieldG S C k (e (α i), f i)) F)
      = ∑ b : ι → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSG S k (Sum.elim (fun i => locFieldG S ρ k (b i) (f i)) F) := by
  have h1 : ∀ i, smear (S.a k) (cFieldG S C k (e (α i), f i)).1.1 (f i)
      = ∑ b, ρ.M k (α i) b • smear (S.a k) (locFieldG S ρ k b (f i)).1.1 (f i) :=
    fun i => smear_cFieldG S ρ C e hren k (α i) (f i)
  have hc : ∀ i, (cFieldG S C k (e (α i), f i)).2 = f i := fun _ => rfl
  have hl : ∀ i b, (locFieldG S ρ k b (f i)).2 = f i := fun _ _ => rfl
  simp only [latSG, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hc, hl]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Fintype.prod_sum, Finset.sum_mul, (S.ν k).map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_smul, smul_mul_assoc, (S.ν k).map_smul]

/-- **The sector's mixed reading as a combination of the composites' mixed readings.**
DERIVED: no numeral. -/
theorem mixLatTG_eq_sum (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix) (Φ : GFlow G)
    (τ : Fin 4) (k : ℕ) (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (P : TMono) (Q : MonoG G) :
    mixLatTG S ρ Φ.map τ k P Q
      = ∑ α : Fin P.1 → Idx4, (∏ i, reflC τ (P.2 i).1 (α i))
          * mixLatCG S C Φ τ k ⟨P.1, fun i => (e (α i), (P.2 i).2)⟩ Q := by
  have h2 : ∀ α : Fin P.1 → Idx4, mixLatCG S C Φ τ k ⟨P.1, fun i => (e (α i), (P.2 i).2)⟩ Q
      = ∑ b : Fin P.1 → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSG S k (Sum.elim (fun i => locFieldG S ρ k (b i) ((P.2 i).2.reflect τ))
              (fun j => (Φ.map k (Q.2 j).1, (Q.2 j).2))) :=
    fun α => latSG_elim_expand S ρ C e hren k α (fun i => (P.2 i).2.reflect τ)
      (fun j => (Φ.map k (Q.2 j).1, (Q.2 j).2))
  unfold mixLatTG
  simp only [h2, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin P.1 → Idx4)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h3 : (∏ i, mixCG ρ k (reflC τ (P.2 i).1) (b i))
      = ∑ α : Fin P.1 → Idx4, ∏ i, (reflC τ (P.2 i).1 (α i) * ρ.M k (α i) (b i)) :=
    Fintype.prod_sum (fun i α' => reflC τ (P.2 i).1 α' * ρ.M k α' (b i))
  rw [h3, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- **The reflection signs** from the first clause of the index map. DERIVED: `0`, `1`, `2`, `3` the
index slots of `he1`. -/
theorem prod_reflCG (C : CompositesG G) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)]) (τ : Fin 4)
    (P : TSep τ) (α : Fin P.1.1 → Idx4) :
    ∏ i, reflC τ (P.1.2 i).1 (α i)
      = sgnCG C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α := by
  have hS : sgnCG C τ (LinkReduce.monoAt e P α).1 = ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) := rfl
  rw [hS, LinkReduce.coefAt, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [he1 (α i), LinkReduce.ctau_tensor τ (α i)]
  rfl

/-- **The sector's mixed reading converges to the combination of the composites' mixed kernels.**
DERIVED: `0`, `1`, `2`, `3` the index slots of `he1`. -/
theorem tendsto_mixLatTG (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (Φ : GFlow G) (τ : Fin 4)
    (P : TSep τ) (Q : MonoG G)
    (hMC : ∀ α : Fin P.1.1 → Idx4, ∃ x, Tendsto
      (fun k => mixLatCG S C Φ τ k (LinkReduce.monoAt e P α).1 Q) (ultra : Filter ℕ) (𝓝 x)) :
    Tendsto (fun k => mixLatTG S ρ Φ.map τ k P.1 Q) (ultra : Filter ℕ)
      (𝓝 (∑ α : Fin P.1.1 → Idx4,
        LinkReduce.coefAt P α * mixKCG S C Φ τ (LinkReduce.monoAt e P α) Q)) := by
  have hk : (fun k => mixLatTG S ρ Φ.map τ k P.1 Q)
      = fun k => ∑ α : Fin P.1.1 → Idx4,
          (sgnCG C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α)
            * mixLatCG S C Φ τ k (LinkReduce.monoAt e P α).1 Q := funext fun k => by
    rw [mixLatTG_eq_sum S ρ C e Φ τ k hren]
    exact Finset.sum_congr rfl fun α _ => by rw [prod_reflCG C e he1 τ P α]; rfl
  have hlim : (∑ α : Fin P.1.1 → Idx4,
        LinkReduce.coefAt P α * mixKCG S C Φ τ (LinkReduce.monoAt e P α) Q)
      = ∑ α : Fin P.1.1 → Idx4,
          (sgnCG C τ (LinkReduce.monoAt e P α).1 * LinkReduce.coefAt P α)
            * limUnder (ultra : Filter ℕ)
                (fun k => mixLatCG S C Φ τ k (LinkReduce.monoAt e P α).1 Q) :=
    Finset.sum_congr rfl fun α _ => by unfold mixKCG; ring
  rw [hk, hlim]
  exact tendsto_finsetSum _ fun α _ => (tendsto_nhds_limUnder (hMC α)).const_mul _

/-- **`ΘP ∪ Q` of composites is admissible.** The proof of `CompositeLink.adm_pairC`.
DERIVED: `4` the dimension. -/
theorem adm_pairCG (C : CompositesG G) {τ : Fin 4} (P Q : TSepG C.Ix τ) :
    Adm (pairCG C τ P.1 Q.1) := by
  obtain ⟨hcP, dP, hdP, hP⟩ := P.2
  obtain ⟨hcQ, dQ, hdQ, hQ⟩ := Q.2
  let O0 : LField (MassGap.SUN.SU 2) :=
    ObserverSymField.sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)
  let P' : Mono 2 := ⟨P.1.1, fun i => (O0, (P.1.2 i).2)⟩
  let Q' : Mono 2 := ⟨Q.1.1, fun i => (O0, (Q.1.2 i).2)⟩
  obtain ⟨d, hd, hs⟩ := ContinuumSep.famSep_pairFam_exists (τ := τ) (P := P') (Q := Q')
    ⟨dP, hdP, hP⟩ ⟨dQ, hdQ, hQ⟩
  have hr : Continuous (reflR τ) := continuous_id.update τ (continuous_apply τ).neg
  refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
  · rcases i with a | a
    · exact (hcP a).comp hr
    · exact hcQ a
  · have h := hs i j hij
    rcases i with a | a <;> rcases j with b | b <;> exact h

end Mixed

/-! ## 4. The chain at any reflection-positive schedule -/

section Chain

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable (S : Sched G)

/-- **Convergence of the composites' mixed readings** against the margin monomials, at the plane `0`.
DERIVED: `0` the plane. -/
def MixConvCG (C : CompositesG G) (Φ : GFlow G) (r : ℝ) : Prop :=
  ∀ (P : TSepG C.Ix 0) (Q : MarginMonoG G 0 r),
    ∃ x, Tendsto (fun k => mixLatCG S C Φ 0 k P.1 Q.1) (ultra : Filter ℕ) (𝓝 x)

/-- **The limits of the readings with the composites reflected as lattice fields** are the
composites' kernels, at the plane `0`. DERIVED: `0` the plane. -/
def ReflLimCG (C : CompositesG G) (Φ : GFlow G) (r : ℝ) : Prop :=
  (∀ P P' : TSepG C.Ix 0,
    Tendsto (fun k => rReadCG S C 0 k P.1 P'.1) (ultra : Filter ℕ) (𝓝 (kernCG S C 0 P P')))
  ∧ ∀ (P : TSepG C.Ix 0) (Q : MarginMonoG G 0 r),
    Tendsto (fun k => rMixCG S C Φ 0 k P.1 Q.1) (ultra : Filter ℕ) (𝓝 (mixKCG S C Φ 0 P Q.1))

/-- **`MixConvCG` from lattice covariance, uniform locality, `ConvCG` and the flow's bound.**
DERIVED: `0` the plane. -/
theorem mixConvCG_of_cov (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) {r : ℝ}
    (hpp : Φ.PosPreserving S 0 r) (C : CompositesG G) (hUL : UnifLocalG C)
    (hcov : ReflCovLatG C 0) (hCO : ConvCG S C) : MixConvCG S C Φ r := by
  intro P Q
  have hL := hCO _ _ (adm_pairCG C P P)
  set x := contCG S C (pairCG C 0 P.1 P.1)
  have hLb : ∀ᶠ k in (ultra : Filter ℕ), |latCG S C k (pairCG C 0 P.1 P.1)| ≤ |x| + 1 := by
    have hball := hL.eventually (Metric.ball_mem_nhds x one_pos)
    filter_upwards [hball] with k hk
    rw [Real.dist_eq] at hk
    calc |latCG S C k (pairCG C 0 P.1 P.1)|
        = |(latCG S C k (pairCG C 0 P.1 P.1) - x) + x| := by rw [sub_add_cancel]
      _ ≤ |latCG S C k (pairCG C 0 P.1 P.1) - x| + |x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  obtain ⟨D, hD⟩ := hB (Fin Q.1.1 ⊕ Fin Q.1.1) (pairFamG 0 Q.1 Q.1)
  have hDb : ∀ᶠ k in atTop, |latSFG S Φ.map k (pairFamG 0 Q.1 Q.1)| ≤ D := by
    have h0 := hD 0 (fun _ => 0)
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
    exact h0
  have hev : ∀ᶠ k in atTop,
      prodSmearG (S.a k) (cMonoG S C k P.1) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) 0 0
        ∧ prodSmearG (S.a k) (Φ.mono k Q.1) ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) 0 0
        ∧ |latSFG S Φ.map k (pairFamG 0 Q.1 Q.1)| ≤ D :=
    (eventually_cMono_memG S C hUL P).and ((eventually_flow_memG S Φ hpp Q).and hDb)
  refine MixConvRP.exists_tendsto_ultra_of_ultra _ (Real.sqrt ((|x| + 1) * D)) ?_
  filter_upwards [hev.filter_mono ultra_le, hLb] with k hk hLk
  obtain ⟨hPk, hQk, hDk⟩ := hk
  refine Real.abs_le_sqrt ?_
  have hsq := mixLatCG_sq_le S hS C Φ 0 hcov k P.1 Q.1 hPk hQk
  exact hsq.trans (mul_le_mul hLk hDk (abs_nonneg _) (by positivity))

/-- **`ReflLimCG` from lattice covariance, `ConvCG` and `MixConvCG`.** DERIVED: `0` the plane. -/
theorem reflLimCG_of_cov (hS : SchedOS S) (C : CompositesG G) (Φ : GFlow G) (r : ℝ)
    (hcov : ReflCovLatG C 0) (hCO : ConvCG S C) (hMC : MixConvCG S C Φ r) :
    ReflLimCG S C Φ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine ⟨fun P P' => ?_, fun P Q => ?_⟩
  · have h := (hCO _ _ (adm_pairCG C P P')).const_mul (sgnCG C 0 P.1)
    refine h.congr fun k => ?_
    exact (rReadCG_of_cov S hS C 0 hcov k P.1 P'.1).symm
  · obtain ⟨x, hx⟩ := hMC P Q
    have h := hx.const_mul (sgnCG C 0 P.1)
    have hlim : mixKCG S C Φ 0 P Q.1 = sgnCG C 0 P.1 * x := by
      show sgnCG C 0 P.1 * limUnder (ultra : Filter ℕ) _ = _
      rw [hx.limUnder_eq]
    rw [hlim]
    refine h.congr fun k => ?_
    exact (rMixCG_of_cov S hS C Φ 0 hcov k P.1 Q.1).symm

/-- **`JointRPK` of the three kernels from `ReflLimCG`**, by the lattice joint inequality.
DERIVED: `0` the plane. -/
theorem jointRPKCG_of_reflLim (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) {r : ℝ}
    (hpp : Φ.PosPreserving S 0 r) (C : CompositesG G) (hUL : UnifLocalG C)
    (hRL : ReflLimCG S C Φ r) :
    JointRPK (kernCG S C 0) (fun P (Q : MarginMonoG G 0 r) => mixKCG S C Φ 0 P Q.1)
      (fun Q Q' : MarginMonoG G 0 r => kernFG S Φ 0 Q.1 Q'.1) := by
  refine jointRPK_of_tendsto
    (fun k P P' => rReadCG S C 0 k P.1 P'.1)
    (fun k P (Q : MarginMonoG G 0 r) => rMixCG S C Φ 0 k P.1 Q.1)
    (fun k Q Q' => latSFG S Φ.map k (pairFamG 0 Q.1 Q'.1))
    hRL.1 hRL.2
    (fun Q Q' => tendsto_contSFG S Φ.map hB (pairFamG 0 Q.1 Q'.1))
    fun P P' s c => ?_
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ c.support, prodSmearG (S.a k) (Φ.mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) 0 0 :=
    (Filter.eventually_all_finset c.support).mpr fun Q _ => eventually_flow_memG S Φ hpp Q
  filter_upwards [eventually_cMono_memG S C hUL P, eventually_cMono_memG S C hUL P', hQ]
    with k hP hP' hQk
  exact latJointCG S hS C Φ 0 k (fun Q : MarginMonoG G 0 r => Q.1) P.1 P'.1 s c hP hP' hQk

/-- **The composites' vectors in the flowed reconstruction, with `LinkCPreG` and the cross reading**,
from `JointRPK`, `ApproxK` and `MixConvCG` of the three kernels, `ConvCG` of the composites and an
index map `e` with the two clauses of `TIn`. `CompositesRen.linkCPreG_of_kernels` at any schedule with
`SchedOS S` and any flow `Φ`. DERIVED: `0` the plane; `0`, `1`, `2`, `3` the index slots of `he1`. -/
theorem linkCPreG_of_kernelsG (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) {r : ℝ}
    (hpp : Φ.PosPreserving S 0 r) (ρ : RenormMixG G) (Cs : CompositesG G) (e : Idx4 → Cs.Ix)
    (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hCO : ConvCG S Cs)
    (hJ : JointRPK (kernCG S Cs 0) (fun P (Q : MarginMonoG G 0 r) => mixKCG S Cs Φ 0 P Q.1)
      (fun Q Q' : MarginMonoG G 0 r => kernFG S Φ 0 Q.1 Q'.1))
    (hA : ApproxK (kernCG S Cs 0) (fun P (Q : MarginMonoG G 0 r) => mixKCG S Cs Φ 0 P Q.1)
      (fun Q Q' : MarginMonoG G 0 r => kernFG S Φ 0 Q.1 Q'.1))
    (hMC : MixConvCG S Cs Φ r) :
    ∃ wC : TSepG Cs.Ix 0 → FlowHG S hS Φ hB 0 hpp,
      LinkCPreG S 0 (vacTG S hS Φ hB 0 hpp) (timeTG S hS Φ hB 0 hpp) Cs wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoG G 0 r),
        Tendsto (fun k => mixLatTG S ρ Φ.map 0 k P.1 Q.1) (ultra : Filter ℕ)
            (𝓝 (mixTG S ρ Φ.map 0 P.1 Q.1))
          ∧ inner ℂ (LinkReduce.wOfC e wC P) (gvecTG S hS Φ hB 0 hpp Q)
            = (mixTG S ρ Φ.map 0 P.1 Q.1 : ℂ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hG : ∀ Q Q' : MarginMonoG G 0 r,
      inner ℂ (gvecTG S hS Φ hB 0 hpp Q) (gvecTG S hS Φ hB 0 hpp Q')
        = ((fun Q Q' : MarginMonoG G 0 r => kernFG S Φ 0 Q.1 Q'.1) Q Q' : ℂ) :=
    inner_gvecTG_eq S hS Φ hB 0 hpp
  have hG2 : ∀ (m : ℕ) (Q : MarginMonoG G 0 r),
      gvecTG S hS Φ hB 0 hpp (marginShiftG S 0 m Q)
        = timeTG S hS Φ hB 0 hpp (S.a m) (gvecTG S hS Φ hB 0 hpp Q) := by
    intro m Q
    have ht := timeTG_dyadic S hS Φ hB 0 hpp m 1
    rw [Nat.cast_one, one_mul, pow_one] at ht
    rw [ht, stepTG_gvecTG]
  have hG3 : (Submodule.span ℂ (Set.range (gvecTG S hS Φ hB 0 hpp))).topologicalClosure = ⊤ :=
    MassGap.ClayStatement.span_single_dense _
  obtain ⟨w, hwX, hwK⟩ := exists_link _ hG ((jointRP_iff_K _ hG).mpr hJ) ((approx_iff_K _ hG).mpr hA)
  refine ⟨w, ⟨fun P Q => ⟨hCO _ _ (adm_pairCG Cs P Q), hwK P Q⟩, fun m P => ?_, ?_⟩,
    fun P Q => ?_⟩
  · refine eq_of_inner_eq hG3 fun Q => ?_
    calc inner ℂ (w (shiftTG S 0 m P)) (gvecTG S hS Φ hB 0 hpp Q)
        = (mixKCG S Cs Φ 0 P (marginShiftG S 0 m Q).1 : ℂ) := by
          rw [hwX]
          exact congrArg Complex.ofReal (mixKCG_shift S hS Cs Φ 0 m P Q.1)
      _ = inner ℂ (w P) (gvecTG S hS Φ hB 0 hpp (marginShiftG S 0 m Q)) := (hwX _ _).symm
      _ = inner ℂ (w P) (timeTG S hS Φ hB 0 hpp (S.a m) (gvecTG S hS Φ hB 0 hpp Q)) := by
          rw [hG2 m Q]
      _ = inner ℂ (timeTG S hS Φ hB 0 hpp (S.a m) (w P)) (gvecTG S hS Φ hB 0 hpp Q) :=
          ((ContinuumTimeGroup.isSelfAdjoint_powT (a := stepTG S hS Φ hB 0 hpp 0)
            (S.a m / S.a 0)).isSymmetric (w P) (gvecTG S hS Φ hB 0 hpp Q)).symm
  · have hvac : vacTG S hS Φ hB 0 hpp = gvecTG S hS Φ hB 0 hpp (emptyMarginG G 0 r) := rfl
    refine eq_of_inner_eq hG3 fun Q => ?_
    rw [hvac, hG, hwX]
    exact congrArg Complex.ofReal (mixKCG_empty S Cs Φ 0 r Q.1)
  · have hT := tendsto_mixLatTG S ρ Cs e he1 he2 Φ 0 P Q.1
      (fun α => hMC (LinkReduce.monoAt e P α) Q)
    have hmix : mixTG S ρ Φ.map 0 P.1 Q.1
        = ∑ α : Fin P.1.1 → Idx4, LinkReduce.coefAt P α
            * mixKCG S Cs Φ 0 (LinkReduce.monoAt e P α) Q.1 :=
      hT.limUnder_eq
    refine ⟨by rw [hmix]; exact hT, ?_⟩
    rw [hmix]
    unfold LinkReduce.wOfC
    rw [sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
    exact congrArg (fun x => ((LinkReduce.coefAt P α : ℝ) : ℂ) * x) (hwX _ Q)

/-- **The link from `ApproxK` alone**: `JointRPK` and `MixConvCG` from uniform locality, lattice
covariance and `ConvCG` (`mixConvCG_of_cov`, `reflLimCG_of_cov`, `jointRPKCG_of_reflLim`).
DERIVED: `0` the plane; `0`, `1`, `2`, `3` the index slots of `he1`. -/
theorem linkCPreG_of_approx (hS : SchedOS S) (Φ : GFlow G) (hB : UniformBoundFG S Φ.map) {r : ℝ}
    (hpp : Φ.PosPreserving S 0 r) (ρ : RenormMixG G) (Cs : CompositesG G) (e : Idx4 → Cs.Ix)
    (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hUL : UnifLocalG Cs) (hcov : ReflCovLatG Cs 0) (hCO : ConvCG S Cs)
    (hA : ApproxK (kernCG S Cs 0) (fun P (Q : MarginMonoG G 0 r) => mixKCG S Cs Φ 0 P Q.1)
      (fun Q Q' : MarginMonoG G 0 r => kernFG S Φ 0 Q.1 Q'.1)) :
    ∃ wC : TSepG Cs.Ix 0 → FlowHG S hS Φ hB 0 hpp,
      LinkCPreG S 0 (vacTG S hS Φ hB 0 hpp) (timeTG S hS Φ hB 0 hpp) Cs wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoG G 0 r),
        Tendsto (fun k => mixLatTG S ρ Φ.map 0 k P.1 Q.1) (ultra : Filter ℕ)
            (𝓝 (mixTG S ρ Φ.map 0 P.1 Q.1))
          ∧ inner ℂ (LinkReduce.wOfC e wC P) (gvecTG S hS Φ hB 0 hpp Q)
            = (mixTG S ρ Φ.map 0 P.1 Q.1 : ℂ) := by
  have hMC := mixConvCG_of_cov S hS Φ hB hpp Cs hUL hcov hCO
  exact linkCPreG_of_kernelsG S hS Φ hB hpp ρ Cs e he1 he2 hCO
    (jointRPKCG_of_reflLim S hS Φ hB hpp Cs hUL (reflLimCG_of_cov S hS Cs Φ r hcov hCO hMC)) hA hMC

end Chain

/-! ## 5. Along every coupling tower of `SU(N)` -/

section Along

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedOS_alongG)
open MassGap.ConsolidatedRoot (obsW rhoZ csZ physRange_sunFam he1_csZ he2_csZ)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **`ApproxK` of the three kernels along `βs`**: the composites' kernel `kernCG`, the mixed kernel
`mixKCG` against the flowed margin monomials of the observer `obsW N hc0 hc s₀`, and the observer's
flowed kernel, at the schedule `schedAlongG (SU N) βs`. DERIVED: `0` the plane; `2` the least rank;
`π` in `π/N` the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
def ApproxAlong (βs : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ)
    (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) : Prop :=
  ApproxK (kernCG (schedAlongG _ βs) (csZ N zri zwe μ) 0)
    (fun P (Q : MarginMonoG (MassGap.SUN.SU N) 0 r) =>
      mixKCG (schedAlongG _ βs) (csZ N zri zwe μ)
        (energy0G (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))
          (SymPlaqG.symPlaqG_refl (MassGap.SUN.SU N))) 0 P Q.1)
    (fun Q Q' : MarginMonoG (MassGap.SUN.SU N) 0 r =>
      kernFG (schedAlongG _ βs)
        (energy0G (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))
          (SymPlaqG.symPlaqG_refl (MassGap.SUN.SU N))) 0 Q.1 Q'.1)

omit [Fact (2 ≤ N)] in
/-- **Uniform locality of the composites `csZ`** (`CompositesRen.unifLocal_buildRen`).
DERIVED: no numeral. -/
theorem unifLocal_csZ (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) : UnifLocalG (csZ N zri zwe μ) :=
  CompositesRen.unifLocal_buildRen (ClayData.rhoD (ReflAvg.fR N) (ZCanon.zFix N zri zwe))
    (ClayData.bareD (ReflAvg.fR N) (ReflAvg.bR N)) μ

omit [Fact (2 ≤ N)] in
/-- **Lattice reflection covariance of the composites `csZ`** (`CompositesRen.reflCovLat_CRen`).
DERIVED: `0` the plane. -/
theorem reflCovLat_csZ (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix) :
    ReflCovLatG (csZ N zri zwe μ) 0 :=
  CompositesRen.reflCovLat_CRen (N := N) (ZCanon.zFix N zri zwe) μ

/-- **The link along every coupling tower**: at the witnesses of `ConsolidatedRoot`, the class
moments, the physical range, `ConvCG` of the composites and `ApproxAlong` give the composites'
vectors `wC` in `preHGAlong` with `LinkCPreG` and the cross reading: the clauses `wC`, `hLC`, `hX` of
`ConsolidatedRoot.OpenAlong`. DERIVED: `0` the plane and the signs; `2` the least rank; `π` in `π/N`
the angle of the centre of `SU(N)`; `12` a sufficient bound on `c`. -/
theorem linkAlong (βs : ℕ → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r) {t C₀ : ℝ}
    (hU : ObserverLinkedG.ClassMomentsG (schedAlongG _ βs) (obsW N hc0 hc s₀)
      (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) t C₀)
    (zri zwe : ℕ → ℝ) (μ : CompositesRen.OffMix)
    (hCO : ConvCG (schedAlongG _ βs) (csZ N zri zwe μ))
    (hA : ApproxAlong N βs hc0 hc s₀ r zri zwe μ) :
    ∃ wC : TSepG (csZ N zri zwe μ).Ix 0
        → preHGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr),
      LinkCPreG (schedAlongG _ βs) 0
          (preVacGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr))
          (preTimeGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr))
          (csZ N zri zwe μ) wC
        ∧ ∀ (P : TSep 0)
          (Q : MarginMonoDG (MassGap.SUN.SU N) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) 0 r),
          Tendsto (fun k => mixLatTG (schedAlongG _ βs) (rhoZ N zri zwe)
              (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀)
                (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))) 0 k P.1 Q.1.1)
              (ultra : Filter ℕ)
              (𝓝 (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
                (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀)
                  (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))) 0 P.1 Q.1.1))
            ∧ inner ℂ (LinkReduce.wOfC CompositesBuild.eI wC P)
                (preCvecGAlong βs (obsW N hc0 hc s₀) hU (physRange_sunFam βs hc0 hc hs0 hr) Q)
              = (mixTG (schedAlongG _ βs) (rhoZ N zri zwe)
                  (energyMapG (schedAlongG _ βs) (obsW N hc0 hc s₀)
                    (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))) 0 P.1 Q.1.1 : ℂ) := by
  obtain ⟨wC, hLC, hX⟩ := linkCPreG_of_approx (schedAlongG _ βs) (schedOS_alongG _ βs)
    (energy0G (schedAlongG _ βs) (obsW N hc0 hc s₀) (SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))
      (SymPlaqG.symPlaqG_refl (MassGap.SUN.SU N)))
    (preBGAlong βs (obsW N hc0 hc s₀) hU)
    (posPreserving_of_physRangeG _ _ (physRange_sunFam βs hc0 hc hs0 hr) 0)
    (rhoZ N zri zwe) (csZ N zri zwe μ) CompositesBuild.eI (he1_csZ zri zwe μ) (he2_csZ zri zwe μ)
    (unifLocal_csZ zri zwe μ) (reflCovLat_csZ zri zwe μ) hCO hA
  exact ⟨wC, hLC, fun P Q => hX P Q.1⟩

end Along

end MassGap.LinkAlongG

end

#print axioms MassGap.LinkAlongG.latJoint_nonnegG
#print axioms MassGap.LinkAlongG.rReadCG_eq
#print axioms MassGap.LinkAlongG.rMixCG_eq
#print axioms MassGap.LinkAlongG.latSFG_pair_eq
#print axioms MassGap.LinkAlongG.latJointCG
#print axioms MassGap.LinkAlongG.eventually_cMono_memG
#print axioms MassGap.LinkAlongG.eventually_flow_memG
#print axioms MassGap.LinkAlongG.smear_smulG
#print axioms MassGap.LinkAlongG.refl_sub_covG
#print axioms MassGap.LinkAlongG.latSG_scale
#print axioms MassGap.LinkAlongG.smear_refl_cFieldG
#print axioms MassGap.LinkAlongG.rReadCG_of_cov
#print axioms MassGap.LinkAlongG.rMixCG_of_cov
#print axioms MassGap.LinkAlongG.sgnCG_sq
#print axioms MassGap.LinkAlongG.abs_sgnCG
#print axioms MassGap.LinkAlongG.rMixCG_sq_le
#print axioms MassGap.LinkAlongG.mixLatCG_sq_le
#print axioms MassGap.LinkAlongG.mixLatCG_shift
#print axioms MassGap.LinkAlongG.mixKCG_shift
#print axioms MassGap.LinkAlongG.mixKCG_empty
#print axioms MassGap.LinkAlongG.latSG_elim_expand
#print axioms MassGap.LinkAlongG.mixLatTG_eq_sum
#print axioms MassGap.LinkAlongG.prod_reflCG
#print axioms MassGap.LinkAlongG.tendsto_mixLatTG
#print axioms MassGap.LinkAlongG.adm_pairCG
#print axioms MassGap.LinkAlongG.mixConvCG_of_cov
#print axioms MassGap.LinkAlongG.reflLimCG_of_cov
#print axioms MassGap.LinkAlongG.jointRPKCG_of_reflLim
#print axioms MassGap.LinkAlongG.linkCPreG_of_kernelsG
#print axioms MassGap.LinkAlongG.linkCPreG_of_approx
#print axioms MassGap.LinkAlongG.unifLocal_csZ
#print axioms MassGap.LinkAlongG.reflCovLat_csZ
#print axioms MassGap.LinkAlongG.linkAlong
