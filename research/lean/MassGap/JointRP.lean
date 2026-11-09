import Mathlib
import MassGap.CompositeLink
import MassGap.ClaySUGap
import MassGap.EdgeCost

/-!
# MassGap.JointRP — the joint reflection positivity of composites and flowed readings

`CompositeLink.clayStatementAt_SU_link` takes `hJ : JointRPK (kernC …) (mixK …) (gramF …)`. This
module proves the lattice joint reflection positivity of the mixed family (composites ∪ flowed
observer fields) at every step from the reflection positivity of the periodic Wilson state, passes
it to the limit along `ultra`, and replaces `hJ` in the capstone by a statement about the limits of
the readings with the composites reflected as lattice fields.

## 1. The reflection form

`rform ν θ A B = ν(θA · B)`, a bilinear form. `rform_expand`: when it is symmetric, its value at
`A + tA' − ∑ c_Q V_Q` is the expression of `JointRPK` with blocks `rform A A'`, `rform A V_Q`,
`rform V_Q V_Q'`. `latJoint_nonneg`: at `ν = stateK hN k`, `θ = ireflObs τ 0` and `A`, `A'`, `V_Q`
in the half-space algebra, that value is non-negative (`stateK_rp`; symmetry from
`refl_pair_symm` and `periodicState_reflInvariant`).

## 2. The lattice readings with the composites reflected as fields

* `cMono`: a monomial of composites as a monomial of smeared fields, the fields `cField`.
* `rReadC k P P' = latSk (pairFam τ (cMono P) (cMono P'))`: the composites of `P` reflected as lattice
  fields (`SField.refl`: field `θ O`, test function reflected), those of `P'` not.
* `rMixC k P Q = latSk (pairFam τ (cMono P) (Φ.mono k Q))`: the same against the flowed fields of `Q`.
* `latJointC`: the lattice joint inequality for `rReadC`, `rMixC` and the flowed readings
  `latSF (pairFam τ Q Q')`, under half-space membership.
* `eventually_cMono_mem`: if the renormalised fields `ren k i` are local on a set independent of `k`
  (`UnifLocal`), a separated positive-time composite monomial is eventually in the half-space
  algebra. `build_unifLocal`: every `build ρ bare` is `UnifLocal`.
* `eventually_flow_mem`: the same for margin monomials under `PosPreserving`.
* `jointRPK_of_tendsto`: lattice inequalities eventually in `k` and convergence along `ultra` of the
  three blocks give `JointRPK` of the limits.

## 3. The capstone

* `ReflLim`: along `ultra`, `rReadC → kernC` and `rMixC → mixK` (composites of the SU capstone,
  plane `0`).
* `jointRPK_of_reflLim`: `ReflLim` gives `JointRPK (kernC …) (mixK …) (gramF …)`. The flowed block
  converges by `tendsto_contSF` with the uniform bound `ClaySUGap.uB`.
* `clayStatementAt_SU_rp`: `clayStatementAt_SU_link` with `hJ` replaced by `ReflLim`.

## 4. Lattice reflection covariance, and why it does not hold for the bare composites

* `ReflCovLat C τ`: `θ (ren k i) = (−1)^{ctau τ (cl i)} · ren k i` as lattice observables, at every
  step. `rReadC_of_cov`, `rMixC_of_cov`: under it `rReadC = sgnC · latC(pairC)` and
  `rMixC = sgnC · mixLatC` exactly. `reflLim_of_cov`: `ReflCovLat`, `CompOS` and `MixConv` give
  `ReflLim`. `clayStatementAt_SU_rpLat`: the capstone with `hJ` replaced by `ReflCovLat`.
* `not_reflCovLat`: for `N ≥ 2`, `ReflCovLat (Cb N z) 0` is false. The witness is the composite
  `Im((−i) tr(U_{01} − 1))`, the forward plaquette in the `(0,1)` plane at the origin (`ctau = 1`):
  on the configuration with `U(0, 0) = ω·1` (`ω = e^{2πi/N}`) and every other link `1`, the field is
  `N(1 − Re ω) ≠ 0`, while its reflection reads the links of the backward plaquette, all `1`, and
  vanishes. The reflection `ireflConf τ 0` moves a forward `τ`-plaquette at the origin to a
  backward one, so the bare composites are not reflection covariant on the lattice; `clayStatementAt_SU_rpLat`
  has an unsatisfiable hypothesis for the SU capstone's composites, and `clayStatementAt_SU_rp`
  with `ReflLim` is the form that remains open.

## What is not proved here

* `ReflLim`. It is the continuum reflection covariance of the composites in the mixed readings:
  the limit of the reading with `θ` applied to the composite fields equals the limit with only the
  test functions reflected, times `sgnC`. ARGUED: the difference `θ O − sgn · O` of a bare composite is
  a lattice field whose classical leading term vanishes (the backward and forward plaquettes have
  the same leading term up to the sign), so it is of higher dimension at tree level. Beyond tree
  level the reflection-odd difference can mix at order `g²` into reflection-odd operators of
  dimension `4`, so it vanishes only through `g(a_k) → 0`, logarithmically (asymptotic freedom), not by
  power counting; that its renormalised contribution vanishes in the limit, against the divergent
  channel factors (`CompositeLink.tendsto_abs_z_atTop`), is a renormalisation statement not proved in
  the tree. Composites averaged over the reflection satisfy `ReflCovLat` exactly
  (`ReflAvg.reflCovLat_CbR`), which gives the capstone `ReflAvg.clayStatementAt_SU_reflAvg` without
  `hJ`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reflection constant, the origin and the signs; `1` the unit
coefficient, the unit observable and the unit configuration; `2` the cross-term factor, the square
and the least colour count; `4` the dimension.
-/

noncomputable section

namespace MassGap.JointRP

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink

/-! ## 1. The reflection form -/

section Form

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The reflection form** `(A, B) ↦ ν(θA · B)`, bilinear. DERIVED: no numeral. -/
def rform (ν : MassGap.DLRLimit.State X) (θ : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) :
    C(X, ℝ) →ₗ[ℝ] C(X, ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun A B => ν (θ A * B))
    (fun A A' B => by rw [map_add, add_mul, ν.map_add])
    (fun s A B => by rw [map_smul, smul_mul_assoc, ν.map_smul, smul_eq_mul])
    (fun A B B' => by rw [mul_add, ν.map_add])
    (fun s A B => by rw [mul_smul_comm, ν.map_smul, smul_eq_mul])

/-- DERIVED: no numeral. -/
theorem rform_apply (ν : MassGap.DLRLimit.State X) (θ : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) (A B : C(X, ℝ)) :
    rform ν θ A B = ν (θ A * B) := rfl

omit [CompactSpace X] in
/-- **The joint form of a symmetric bilinear form**: its value at `A + tA' − ∑ c_Q V_Q` is
`B(A,A) + 2t B(A,A') + t² B(A',A') − 2 ∑ c_Q B(A,V_Q) − 2t ∑ c_Q B(A',V_Q) + ∑ c_Q c_Q' B(V_Q,V_Q')`.

DERIVED: `2` the cross-term factor and the square. -/
theorem rform_expand {M : Type} (B : C(X, ℝ) →ₗ[ℝ] C(X, ℝ) →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (A A' : C(X, ℝ)) (V : M → C(X, ℝ)) (t : ℝ) (c : M →₀ ℝ) :
    B (A + t • A' - c.sum (fun Q a => a • V Q)) (A + t • A' - c.sum (fun Q a => a • V Q))
      = B A A + 2 * t * B A A' + t ^ 2 * B A' A' - 2 * xL (fun Q => B A (V Q)) c
        - 2 * t * xL (fun Q => B A' (V Q)) c + gForm (fun Q Q' => B (V Q) (V Q')) c c := by
  set y := c.sum (fun Q a => a • V Q) with hy
  have h1 : ∀ x, B x y = xL (fun Q => B x (V Q)) c := by
    intro x
    rw [hy, map_finsuppSum]
    unfold xL
    refine Finsupp.sum_congr fun Q _ => ?_
    rw [map_smul, smul_eq_mul]
  have hyy : B y y = gForm (fun Q Q' => B (V Q) (V Q')) c c := by
    rw [h1 y]
    unfold xL gForm
    refine Finsupp.sum_congr fun Q _ => ?_
    show c Q * B y (V Q) = c.sum fun Q' b => c Q * b * B (V Q) (V Q')
    rw [hs y (V Q), h1 (V Q)]
    unfold xL
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun Q' _ => ?_
    ring
  have e1 : B A' A = B A A' := hs _ _
  have e2 : B y A = xL (fun Q => B A (V Q)) c := (hs _ _).trans (h1 A)
  have e3 : B y A' = xL (fun Q => B A' (V Q)) c := (hs _ _).trans (h1 A')
  have e4 : B A y = xL (fun Q => B A (V Q)) c := h1 A
  have e5 : B A' y = xL (fun Q => B A' (V Q)) c := h1 A'
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, e1, e2, e3, e4, e5, hyy]
  ring

end Form

variable {N : ℕ}

/-- **The lattice joint inequality** at step `k`: for `A`, `A'` and the `V_Q` (`Q` in the support of
`c`) in the half-space algebra of `x_τ = 0`, the joint form of `rform (stateK hN k) θ` is
non-negative.

DERIVED: `0` the plane, the reflection constant and the sign concluded; `2` the cross-term factor
and the square. -/
theorem latJoint_nonneg (hN : N ≠ 0) (k : ℕ) (τ : Fin 4) {M : Type} (A A' : C(Cfg N, ℝ))
    (V : M → C(Cfg N, ℝ)) (t : ℝ) (c : M →₀ ℝ)
    (hA : A ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hA' : A' ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hV : ∀ Q ∈ c.support, V Q ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    let B := rform (stateK hN k) (LatticeReflection.ireflObs τ 0)
    0 ≤ B A A + 2 * t * B A A' + t ^ 2 * B A' A' - 2 * xL (fun Q => B A (V Q)) c
        - 2 * t * xL (fun Q => B A' (V Q)) c + gForm (fun Q Q' => B (V Q) (V Q')) c c := by
  intro B
  have hs : ∀ x y, B x y = B y x := fun x y =>
    refl_pair_symm (stateK hN k) τ
      (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0) x y
  rw [← rform_expand B hs]
  have hY : A + t • A' - c.sum (fun Q a => a • V Q)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
    refine Submodule.sub_mem _ (Submodule.add_mem _ hA (Submodule.smul_mem _ _ hA')) ?_
    exact Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hV Q hQ)
  exact stateK_rp hN k τ _ hY

/-! ## 2. The lattice readings -/

section Readings

/-- **A monomial of composites as a monomial of smeared fields** at step `k`: the fields `cField`.
DERIVED: no numeral. -/
def cMono (hN : N ≠ 0) (C : Composites N) (k : ℕ) (P : TMonoG C.Ix) : Mono N :=
  ⟨P.1, fun i => cField hN C k (P.2 i)⟩

/-- **The reading of the composites with `P` reflected as lattice fields**:
`latSk (pairFam τ (cMono P) (cMono P'))` (field `θ O` and test function reflected on `P`).
DERIVED: no numeral. -/
def rReadC (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) (k : ℕ) (P P' : TMonoG C.Ix) : ℝ :=
  latSk hN k (pairFam τ (cMono hN C k P) (cMono hN C k P'))

/-- **The mixed reading with `P` reflected as lattice fields** against the flowed fields of `Q`.
DERIVED: no numeral. -/
def rMixC (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (P : TMonoG C.Ix)
    (Q : Mono N) : ℝ :=
  latSk hN k (pairFam τ (cMono hN C k P) (Φ.mono k Q))

/-- DERIVED: no numeral. -/
theorem rReadC_eq (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) (k : ℕ) (P P' : TMonoG C.Ix) :
    rReadC hN C τ k P P' = rform (stateK hN k) (LatticeReflection.ireflObs τ 0)
      (prodSmear (dySpacing N k) (cMono hN C k P)) (prodSmear (dySpacing N k) (cMono hN C k P')) := by
  unfold rReadC
  rw [latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  rfl

/-- DERIVED: no numeral. -/
theorem rMixC_eq (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (k : ℕ)
    (P : TMonoG C.Ix) (Q : Mono N) :
    rMixC hN C Φ τ k P Q = rform (stateK hN k) (LatticeReflection.ireflObs τ 0)
      (prodSmear (dySpacing N k) (cMono hN C k P)) (prodSmear (dySpacing N k) (Φ.mono k Q)) := by
  unfold rMixC
  rw [latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  rfl

/-- DERIVED: no numeral. -/
theorem latSF_pair_eq (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (Q Q' : Mono N) :
    latSF hN Φ k (pairFam τ Q Q') = rform (stateK hN k) (LatticeReflection.ireflObs τ 0)
      (prodSmear (dySpacing N k) (Φ.mono k Q)) (prodSmear (dySpacing N k) (Φ.mono k Q')) := by
  rw [latSF_pairFam, latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  rfl

/-- **The lattice joint inequality of the mixed family** at step `k`: composites `P`, `P'` reflected
as lattice fields, flowed monomials `q Q`, under half-space membership of every product.

DERIVED: `0` the plane and the sign concluded; `2` the cross-term factor and the square. -/
theorem latJointC (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4) (k : ℕ)
    {M : Type} (q : M → Mono N) (P P' : TMonoG C.Ix) (t : ℝ) (c : M →₀ ℝ)
    (hP : prodSmear (dySpacing N k) (cMono hN C k P)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hP' : prodSmear (dySpacing N k) (cMono hN C k P')
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : ∀ Q ∈ c.support, prodSmear (dySpacing N k) (Φ.mono k (q Q))
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    0 ≤ rReadC hN C τ k P P + 2 * t * rReadC hN C τ k P P' + t ^ 2 * rReadC hN C τ k P' P'
      - 2 * xL (fun Q => rMixC hN C Φ τ k P (q Q)) c - 2 * t * xL (fun Q => rMixC hN C Φ τ k P' (q Q)) c
      + gForm (fun Q Q' => latSF hN Φ k (pairFam τ (q Q) (q Q'))) c c := by
  simp only [rReadC_eq, rMixC_eq, latSF_pair_eq]
  exact latJoint_nonneg hN k τ _ _ (fun Q => prodSmear (dySpacing N k) (Φ.mono k (q Q))) t c hP hP' hQ

/-- **Uniform locality of the renormalised composites**: each `ren k i` is local on one set of links
for every `k`. DERIVED: no numeral. -/
def UnifLocal (C : Composites N) : Prop :=
  ∀ i, ∃ S : Finset ILink, ∀ k, IsLocalOn S ((C.ren k i).1 : Cfg N → ℝ)

/-- **Every `build ρ bare` is uniformly local**: `ren k i` is the bare field (`dec = none`) or
`∑_b M k α b • op b`, local on the union of the supports of the basis. DERIVED: no numeral. -/
theorem build_unifLocal (ρ : RenormMix N) (bare : CompositesBuild.Ix0 → LField (MassGap.SUN.SU N)) :
    UnifLocal (CompositesBuild.build ρ bare) := by
  intro i
  cases h : CompositesBuild.dec i.1 with
  | none =>
    obtain ⟨S, hS⟩ := (bare i).2.1
    refine ⟨S, fun k => ?_⟩
    rw [show (CompositesBuild.build ρ bare).ren k i = bare i from
      CompositesBuild.renF_of_none ρ bare h k]
    exact hS
  | some α =>
    choose S hS using fun b => (ρ.op b).2.1
    refine ⟨Finset.univ.biUnion S, fun k => ?_⟩
    rw [show (CompositesBuild.build ρ bare).ren k i = CompositesBuild.mixF ρ k α from
      CompositesBuild.renF_of_some ρ bare h k]
    intro U V hUV
    show (∑ b, ρ.M k α b • (ρ.op b).1) U = (∑ b, ρ.M k α b • (ρ.op b).1) V
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hS b U V fun l hl => hUV l (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hl⟩)]

/-- **A separated positive-time monomial of uniformly local composites is eventually in the
half-space algebra.** DERIVED: `0` the plane. -/
theorem eventually_cMono_mem (hN : N ≠ 0) (C : Composites N) (hUL : UnifLocal C) {τ : Fin 4}
    (P : TSepG C.Ix τ) :
    ∀ᶠ k in atTop, prodSmear (dySpacing N k) (cMono hN C k P.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
  obtain ⟨-, d, hd, hpos, -⟩ := P.2
  have hall : ∀ᶠ k in atTop, ∀ i : Fin P.1.1,
      smear (dySpacing N k) (cField hN C k (P.1.2 i)).1.1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
    refine Filter.eventually_all.mpr fun i => ?_
    obtain ⟨S, hS⟩ := hUL (P.1.2 i).1
    obtain ⟨D, hD⟩ := exists_depth τ S
    have ht : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
    filter_upwards [ht.eventually (gt_mem_nhds hd)] with k hk
    exact smear_mem_halfSpaceAlg (dySpacing_pos (one_le_of_ne_zero hN) k) τ
      (isLocalOn_sub_const (hS k) _) hD hk.le _ (hpos i)
  filter_upwards [hall] with k hk
  exact HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ fun i _ => hk i

/-- **A margin monomial is eventually in the half-space algebra** under `PosPreserving`.
DERIVED: `0` the plane. -/
theorem eventually_flow_mem (Φ : Flow N) {τ : Fin 4} {r : ℝ} (hpos : Φ.PosPreserving τ r)
    (Q : MarginMono N τ r) :
    ∀ᶠ k in atTop, prodSmear (dySpacing N k) (Φ.mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
  obtain ⟨d, hd, hrd, hP⟩ := Q.2
  have hall : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1,
      smear (dySpacing N k) (Φ.map k (Q.1.2 i).1).1 (Q.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr fun i => hpos (Q.1.2 i).1 (Q.1.2 i).2 d hd hrd (hP i)
  filter_upwards [hall] with k hk
  exact HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _ fun i _ => hk i

end Readings

/-! ### The limit -/

section Limit

/-- DERIVED: no numeral. -/
theorem tendsto_xL {M : Type} {l : Filter ℕ} {g : ℕ → M → ℝ} {g0 : M → ℝ}
    (h : ∀ Q, Tendsto (fun k => g k Q) l (𝓝 (g0 Q))) (c : M →₀ ℝ) :
    Tendsto (fun k => xL (g k) c) l (𝓝 (xL g0 c)) := by
  unfold xL Finsupp.sum
  exact tendsto_finsetSum _ fun Q _ => (h Q).const_mul _

/-- DERIVED: no numeral. -/
theorem tendsto_gForm {M : Type} {l : Filter ℕ} {G : ℕ → M → M → ℝ} {G0 : M → M → ℝ}
    (h : ∀ Q Q', Tendsto (fun k => G k Q Q') l (𝓝 (G0 Q Q'))) (c : M →₀ ℝ) :
    Tendsto (fun k => gForm (G k) c c) l (𝓝 (gForm G0 c c)) := by
  unfold gForm Finsupp.sum
  exact tendsto_finsetSum _ fun Q _ => tendsto_finsetSum _ fun Q' _ => (h Q Q').const_mul _

/-- **Joint positivity passes to the limit**: lattice joint inequalities eventually in `k` and the
convergence along `ultra` of the three blocks give `JointRPK` of the limits.

DERIVED: `0` the sign; `2` the cross-term factor and the square. -/
theorem jointRPK_of_tendsto {I M : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}
    (Kk : ℕ → I → I → ℝ) (Xk : ℕ → I → M → ℝ) (Gk : ℕ → M → M → ℝ)
    (hK : ∀ P P', Tendsto (fun k => Kk k P P') (ultra : Filter ℕ) (𝓝 (Kc P P')))
    (hX : ∀ P Q, Tendsto (fun k => Xk k P Q) (ultra : Filter ℕ) (𝓝 (X P Q)))
    (hG : ∀ Q Q', Tendsto (fun k => Gk k Q Q') (ultra : Filter ℕ) (𝓝 (G Q Q')))
    (hlat : ∀ (P P' : I) (t : ℝ) (c : M →₀ ℝ), ∀ᶠ k in atTop,
      0 ≤ Kk k P P + 2 * t * Kk k P P' + t ^ 2 * Kk k P' P' - 2 * xL (Xk k P) c
        - 2 * t * xL (Xk k P') c + gForm (Gk k) c c) :
    JointRPK Kc X G := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro P P' t c
  have hT := (((((hK P P).add ((hK P P').const_mul (2 * t))).add
    ((hK P' P').const_mul (t ^ 2))).sub ((tendsto_xL (hX P) c).const_mul 2)).sub
    ((tendsto_xL (hX P') c).const_mul (2 * t))).add (tendsto_gForm hG c)
  exact ge_of_tendsto hT ((hlat P P' t c).filter_mono ultra_le)

end Limit

/-! ## 3. The capstone -/

section Capstone

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData

/-- **The limits of the readings with the composites reflected as lattice fields** are the kernels
of the SU capstone: `rReadC → kernC` and `rMixC → mixK` along `ultra`, at the plane `0`.

DERIVED: `0` the plane. -/
def ReflLim (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) : Prop :=
  (∀ P P' : TSepG (Cb N z).Ix 0,
    Tendsto (fun k => rReadC (ne_zero_of_two_le hN2) (Cb N z) 0 k P.1 P'.1) (ultra : Filter ℕ)
      (𝓝 (kernC (ne_zero_of_two_le hN2) (Cb N z) 0 P P')))
  ∧ ∀ (P : TSepG (Cb N z).Ix 0) (Q : MarginMono N 0 r),
    Tendsto (fun k => rMixC (ne_zero_of_two_le hN2) (Cb N z) (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 (mixK hN2 W z r P Q))

/-- **`JointRPK` from the reflection positivity of the Wilson state.** At every step the lattice
joint inequality holds eventually (`latJointC`, `eventually_cMono_mem` with `build_unifLocal`,
`eventually_flow_mem` with `Flow.posPreserving_of_physRange`); the flowed block converges to
`gramF` (`tendsto_contSF`, `ClaySUGap.uB`), the other two by `ReflLim`.

DERIVED: `0` the plane. -/
theorem jointRPK_of_reflLim (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ) (hRL : ReflLim hN2 W z r) :
    JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r) := by
  have hN := ne_zero_of_two_le hN2
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  refine jointRPK_of_tendsto
    (fun k P P' => rReadC hN (Cb N z) 0 k P.1 P'.1)
    (fun k P Q => rMixC hN (Cb N z) (Φ0 W) 0 k P.1 Q.1)
    (fun k Q Q' => latSF hN (Φ0 W) k (pairFam 0 Q.1 Q'.1))
    hRL.1 hRL.2
    (fun Q Q' => tendsto_contSF hN (Φ0 W) (ClaySUGap.uB hN W hU) (pairFam 0 Q.1 Q'.1))
    fun P P' s c => ?_
  have hUL := build_unifLocal (rhoD (fT N) z) (bareD (fT N) (bT N))
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ c.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset c.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  filter_upwards [eventually_cMono_mem hN (Cb N z) hUL P,
    eventually_cMono_mem hN (Cb N z) hUL P', hQ] with k hP hP' hQk
  exact latJointC hN (Cb N z) (Φ0 W) 0 k (fun Q : MarginMono N 0 r => Q.1) P.1 P'.1 s c hP hP' hQk

/-- **The SU capstone without `hJ`**: `CompositeLink.clayStatementAt_SU_link` with the joint
reflection positivity `hJ` replaced by `ReflLim` (`jointRPK_of_reflLim`). The other inputs are those
of `clayStatementAt_SU_link`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_rp (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (hRL : ReflLim hN2 W z r)
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hMC : MixConv hN2 W z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_link hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF hObs hWard hCO
    (jointRPK_of_reflLim hN2 W hU hphys z hRL) hA hMC

end Capstone

/-! ## 4. Lattice reflection covariance -/

section Covariance

/-- **Lattice reflection covariance of the renormalised composites**:
`θ (ren k i) = (−1)^{ctau τ (cl i)} · ren k i`, `θ = ireflObs τ 0`, at every step.
DERIVED: `1` the sign. -/
def ReflCovLat (C : Composites N) (τ : Fin 4) : Prop :=
  ∀ k i, ((C.ren k i).refl τ).1 = ((-1 : ℝ) ^ ctau τ (C.cl i)) • (C.ren k i).1

/-- `∏ σᵢ • gᵢ = (∏ σᵢ) • ∏ gᵢ`. DERIVED: no numeral. -/
theorem prod_smul_eq {ι : Type*} (s : Finset ι) (σ : ι → ℝ) (g : ι → C(Cfg N, ℝ)) :
    ∏ i ∈ s, σ i • g i = (∏ i ∈ s, σ i) • ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih,
      smul_mul_smul_comm]

/-- **The connected field inherits the covariance**: if `θ O = (−1)ⁿ O`, then
`θ(O − ν_k(O)) = (−1)ⁿ (O − ν_k(O))`, since `ν_k(O) = ν_k(θO) = (−1)ⁿ ν_k(O)` by the reflection
invariance of the periodic state. DERIVED: `0` the reflection constant; `1` the sign. -/
theorem refl_sub_cov (hN : N ≠ 0) (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (n : ℕ)
    (h : (O.refl τ).1 = ((-1 : ℝ) ^ n) • O.1) :
    ((O.sub (stateK hN k O.1)).refl τ).1 = ((-1 : ℝ) ^ n) • (O.sub (stateK hN k O.1)).1 := by
  have hinv : stateK hN k (LatticeReflection.ireflObs τ 0 O.1) = stateK hN k O.1 :=
    PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0 O.1
  rw [show LatticeReflection.ireflObs τ 0 O.1 = (O.refl τ).1 from rfl, h,
    MassGap.DLRLimit.State.map_smul] at hinv
  rw [LField.refl_sub]
  show (O.refl τ).1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))
    = ((-1 : ℝ) ^ n) • (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ)))
  rw [h, smul_sub, smul_smul, hinv]

/-- **A reading with factorwise scalars**: if each smeared factor of `F` is `σ x` times that of `F'`,
`latS ν a F = (∏ σ x) · latS ν a F'`. DERIVED: no numeral. -/
theorem latS_scale (ν : MassGap.DLRLimit.State (Cfg N)) (a : ℝ) {ι : Type} [Fintype ι]
    (F F' : ι → SField N) (σ : ι → ℝ)
    (hF : ∀ x, smear a (F x).1.1 (F x).2 = σ x • smear a (F' x).1.1 (F' x).2) :
    latS ν a F = (∏ x, σ x) * latS ν a F' := by
  unfold latS
  rw [Finset.prod_congr rfl (fun x _ => hF x), prod_smul_eq, ν.map_smul]

/-- The smeared reflected connected composite under covariance. DERIVED: `1` the sign. -/
theorem smear_refl_cField (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) (hcov : ReflCovLat C τ)
    (k : ℕ) (p : CDatum C) :
    smear (dySpacing N k) (SField.refl τ (cField hN C k p)).1.1 (SField.refl τ (cField hN C k p)).2
      = ((-1 : ℝ) ^ ctau τ (C.cl p.1))
        • smear (dySpacing N k) (cField hN C k (p.1, p.2.reflect τ)).1.1 (p.2.reflect τ) := by
  show smear (dySpacing N k) (((C.ren k p.1).sub (stateK hN k (C.ren k p.1).1)).refl τ).1
      (p.2.reflect τ) = _
  rw [refl_sub_cov hN k τ _ _ (hcov k p.1), smear_smul (dySpacing_pos (one_le_of_ne_zero hN) k)]
  rfl

/-- **Under lattice covariance the reflected reading is the tree's**:
`rReadC = sgnC · latC(pairC)`. DERIVED: `1` the unit factor. -/
theorem rReadC_of_cov (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) (hcov : ReflCovLat C τ)
    (k : ℕ) (P P' : TMonoG C.Ix) :
    rReadC hN C τ k P P' = sgnC C τ P * latC hN C k (pairC C τ P P') := by
  unfold rReadC latC
  rw [latSk_eq, latSk_eq,
    latS_scale (stateK hN k) (dySpacing N k) (pairFam τ (cMono hN C k P) (cMono hN C k P'))
      (fun x => cField hN C k (pairC C τ P P' x))
      (Sum.elim (fun i => (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)) fun _ => 1) ?_]
  · rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
    rfl
  · rintro (i | j)
    · exact smear_refl_cField hN C τ hcov k (P.2 i)
    · exact (one_smul ℝ _).symm

/-- **Under lattice covariance the reflected mixed reading is the tree's**:
`rMixC = sgnC · mixLatC`. DERIVED: `1` the unit factor. -/
theorem rMixC_of_cov (hN : N ≠ 0) (C : Composites N) (Φ : Flow N) (τ : Fin 4)
    (hcov : ReflCovLat C τ) (k : ℕ) (P : TMonoG C.Ix) (Q : Mono N) :
    rMixC hN C Φ τ k P Q = sgnC C τ P * mixLatC hN C Φ τ k P Q := by
  unfold rMixC mixLatC
  rw [latSk_eq, latSk_eq,
    latS_scale (stateK hN k) (dySpacing N k) (pairFam τ (cMono hN C k P) (Φ.mono k Q))
      (Sum.elim (fun i => cField hN C k ((P.2 i).1, (P.2 i).2.reflect τ))
        (fun j => Φ.field k (Q.2 j)))
      (Sum.elim (fun i => (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)) fun _ => 1) ?_]
  · rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
    rfl
  · rintro (i | j)
    · exact smear_refl_cField hN C τ hcov k (P.2 i)
    · exact (one_smul ℝ _).symm

open MassGap.ClayData MassGap.ObsLead in
/-- **Lattice covariance gives `ReflLim`**, with `CompOS` (convergence of `latC(pairC)`,
`adm_pairC`) and `MixConv`. DERIVED: `0` the plane. -/
theorem reflLim_of_cov (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ)
    (hcov : ReflCovLat (Cb N z) 0)
    (hCO : CompOS (ne_zero_of_two_le hN2) (Cb N z)) (hMC : MixConv hN2 W z r) :
    ReflLim hN2 W z r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine ⟨fun P P' => ?_, fun P Q => ?_⟩
  · have h := (hCO.1 _ _ (adm_pairC (Cb N z) P P')).const_mul (sgnC (Cb N z) 0 P.1)
    refine h.congr fun k => ?_
    exact (rReadC_of_cov _ _ 0 hcov k P.1 P'.1).symm
  · obtain ⟨x, hx⟩ := hMC P Q
    have h := hx.const_mul (sgnC (Cb N z) 0 P.1)
    have hlim : mixK hN2 W z r P Q = sgnC (Cb N z) 0 P.1 * x := by
      show sgnC (Cb N z) 0 P.1 * limUnder (ultra : Filter ℕ) _ = _
      rw [hx.limUnder_eq]
    rw [hlim]
    refine h.congr fun k => ?_
    exact (rMixC_of_cov _ _ _ 0 hcov k P.1 Q.1).symm

end Covariance

section CapstoneLat

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData

/-- **The SU capstone from lattice covariance**: `clayStatementAt_SU_rp` with `ReflLim` replaced by
`ReflCovLat (Cb N z) 0` (`reflLim_of_cov`). For the SU capstone's composites this hypothesis is false
(`not_reflCovLat`).

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_rpLat (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (hcov : ReflCovLat (Cb N z) 0)
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hMC : MixConv hN2 W z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_rp hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF hObs hWard hCO
    (reflLim_of_cov hN2 W z r hcov hCO hMC) hA hMC

end CapstoneLat

/-! ## 5. The bare composites are not reflection covariant on the lattice -/

section NoGo

open MassGap.ClassicalLimit MassGap.CompositesBuild MassGap.ClayData MassGap.ObsLead

/-- The witness monomial `Im((−i) tr(U_{01} − 1))`: one word, one plaquette letter in the `(0,1)`
plane. DERIVED: `0`, `1` the two directions. -/
def m0 : CMono := [([([], 0, 1)], false)]

/-- DERIVED: no numeral. -/
theorem admM_m0 : AdmM m0 := ⟨by simp [m0], by simp [m0]⟩

/-- The witness index. DERIVED: no numeral. -/
def i0 : Ix0 := ⟨m0, admM_m0⟩

/-- DERIVED: no numeral. -/
theorem dec_m0 : dec m0 = none := rfl

/-- One index equal to the plane `0`. DERIVED: `0` the plane; `1` the count. -/
theorem ctau_m0 : ctau 0 m0 = 1 := by decide

/-- The witness link `(0, origin)`. DERIVED: `0` the direction and the origin. -/
def l0 : ILink := (0, 0)

/-- The configuration with `g` on `l0` and `1` elsewhere. DERIVED: `1` the unit. -/
def cfg0 (g : MassGap.SUN.SU N) : Cfg N := Function.update (fun _ => 1) l0 g

/-- The links of `m0`, none of which the reflection sends to `l0`. DERIVED: `0`, `1` the
directions; `0` the plane. -/
theorem ireflLink_ne_l0 : ∀ l ∈ linksM m0, LatticeReflection.ireflLink 0 0 l ≠ l0 := by
  intro l hl
  simp only [m0, linksM, linksW, linksD, Finset.union_empty, Finset.mem_insert,
    Finset.mem_singleton] at hl
  intro h
  have h2 := congrArg (fun l : ILink => l.2 0) h
  have h1 := congrArg Prod.fst h
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp_all [LatticeReflection.ireflLink, LatticeReflection.ireflSite, l0, ishift]
  have h3 := congrFun h 0
  simp at h3

/-- The reflected configuration is `1` on the links of `m0`. DERIVED: `1` the unit. -/
theorem refl_cfg0 (g : MassGap.SUN.SU N) :
    ∀ l ∈ linksM m0, LatticeReflection.ireflConf 0 0 (cfg0 g) l = (fun _ => (1 : MassGap.SUN.SU N)) l := by
  intro l hl
  have hne := ireflLink_ne_l0 l hl
  simp only [LatticeReflection.ireflConf, cfg0, Function.update_of_ne hne, inv_one, ite_self]

/-- The reflected field vanishes at `cfg0 g`. DERIVED: `0` the value. -/
theorem monoV_refl_cfg0 (g : MassGap.SUN.SU N) :
    monoV m0 (LatticeReflection.ireflConf 0 0 (cfg0 g)) = 0 := by
  rw [monoV_local m0 _ _ (refl_cfg0 g)]
  exact monoV_one (by simp [m0]) (by simp [m0])

/-- The field at `cfg0 g` is `N − Re tr g`. DERIVED: `0`, `1` the directions. -/
theorem monoV_cfg0 (g : MassGap.SUN.SU N) :
    monoV m0 (cfg0 g) = (N : ℝ) - (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re := by
  have hp : plaqG (cfg0 g) 0 1 0 = g := by
    have e1 : ((1 : Fin 4), ishift 0 (0 : ISite)) ≠ l0 := by simp [l0]
    have e2 : ((0 : Fin 4), ishift 1 (0 : ISite)) ≠ l0 := by
      intro h
      have := congrArg (fun l : ILink => l.2 1) h
      simp [l0, ishift] at this
    have e3 : ((1 : Fin 4), (0 : ISite)) ≠ l0 := by simp [l0]
    simp only [plaqG, cfg0, Function.update_of_ne e1, Function.update_of_ne e2,
      Function.update_of_ne e3]
    rw [show ((0 : Fin 4), (0 : ISite)) = l0 from rfl, Function.update_self]
    simp
  simp only [monoV, m0, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    facV, latW, latD, hp]
  simp [Matrix.trace_sub, Matrix.trace_one, Complex.mul_im]

/-- **`ReflCovLat` fails for the SU capstone's composites** (`N ≥ 2`): at the witness `i0`
(`ren k i0 = bareF m0`, `ctau 0 m0 = 1`) covariance would give `bareF m0 (θU) = −bareF m0 U`; at
`U = cfg0 (ω·1)`, `ω = e^{2πi/N}`, the left side is `0` and the right side `−N(1 − Re ω) ≠ 0`.

DERIVED: `2` the least colour count; `0` the plane and the step; `1` the count and the sign. -/
theorem not_reflCovLat (hN2 : 2 ≤ N) (z : Chan → ℕ → ℝ) : ¬ ReflCovLat (Cb N z) 0 := by
  intro hcov
  have hN : N ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hprim : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN
  have hω : ω ^ N = 1 := hprim.pow_eq_one
  have hω1 : ω ≠ 1 := hprim.ne_one (by omega)
  let g : MassGap.SUN.SU N := ⟨ω • (1 : Matrix (Fin N) (Fin N) ℂ), EdgeCost.scalar_mem_SU hN hω⟩
  have hren : (Cb N z).ren 0 i0 = bareF m0 := by
    show renF (rhoD (fT N) z) (bareD (fT N) (bT N)) 0 i0 = _
    rw [renF_of_none _ _ dec_m0]
    show (match dec m0 with
      | some α => bareT (fT N) α
      | none => bT N i0) = _
    rw [dec_m0]
    rfl
  have h := congrArg (fun F : C(Cfg N, ℝ) => F (cfg0 g)) (hcov 0 i0)
  rw [hren, show (Cb N z).cl i0 = m0 from rfl, ctau_m0] at h
  have hL : ((bareF (N := N) m0).refl 0).1 (cfg0 g) = 0 := monoV_refl_cfg0 g
  have hR : ((-1 : ℝ) ^ 1 • (bareF (N := N) m0).1) (cfg0 g)
      = -((N : ℝ) - (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re) := by
    rw [ContinuousMap.smul_apply, pow_one, neg_one_smul, bareF_apply, monoV_cfg0]
  rw [hL, hR] at h
  have htr : (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re = N * ω.re := by
    show (Matrix.trace (ω • (1 : Matrix (Fin N) (Fin N) ℂ))).re = _
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, Complex.mul_re]
    simp [mul_comm]
  rw [htr] at h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hre : ω.re = 1 := by
    have : (N : ℝ) * (1 - ω.re) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hNpos.ne'
    · linarith
  have hnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hN
  have him : ω.im = 0 := by
    have hn2 : Complex.normSq ω = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
    rw [Complex.normSq_apply, hre] at hn2
    nlinarith [sq_nonneg ω.im]
  exact hω1 (Complex.ext (by simp [hre]) (by simp [him]))

end NoGo

end MassGap.JointRP

end

#print axioms MassGap.JointRP.rform_expand
#print axioms MassGap.JointRP.latJoint_nonneg
#print axioms MassGap.JointRP.latJointC
#print axioms MassGap.JointRP.build_unifLocal
#print axioms MassGap.JointRP.eventually_cMono_mem
#print axioms MassGap.JointRP.eventually_flow_mem
#print axioms MassGap.JointRP.jointRPK_of_tendsto
#print axioms MassGap.JointRP.jointRPK_of_reflLim
#print axioms MassGap.JointRP.clayStatementAt_SU_rp
#print axioms MassGap.JointRP.refl_sub_cov
#print axioms MassGap.JointRP.rReadC_of_cov
#print axioms MassGap.JointRP.rMixC_of_cov
#print axioms MassGap.JointRP.reflLim_of_cov
#print axioms MassGap.JointRP.clayStatementAt_SU_rpLat
#print axioms MassGap.JointRP.monoV_refl_cfg0
#print axioms MassGap.JointRP.monoV_cfg0
#print axioms MassGap.JointRP.not_reflCovLat
