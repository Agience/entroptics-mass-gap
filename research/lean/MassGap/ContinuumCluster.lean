import Mathlib
import MassGap.ContinuumSchwinger
import MassGap.WeakCouplingWindow

noncomputable section

/-!
# MassGap.ContinuumCluster — clustering of the limit Schwinger functions from `FixedWindowDecay`

OS4 for the continuum Schwinger functions of `ContinuumSchwinger`, derived from the weak-coupling
input `WeakCouplingWindow.FixedWindowDecay τ 0 hN L` instead of assumed.

## The route

At step `k` the renormalised monomial `P` is the observable `Yv ρ k P = Z_P · ∏ smear(Oᵢ − cᵢ) fᵢ`.
For positive-time `P` it lies, eventually in `k`, in the gauge-invariant half-space algebra
(`Yv_mem`), so it is a vector of the transfer data `Dk hN τ k =
PeriodicState.periodicGaugeInvData τ 0 hN (dyBeta k)`, whose form is the state's reflected pairing
(`Dk_form`) and whose `n`-th power is the `n`-fold lattice shift (`Dk_T_pow`). Every renormalised
reflected Schwinger function is a value of that form (`latSkR_pairFam_eq`), so
`TransferGap.clustering_sq` at a `GapAt` rate `r` is (`lattice_cluster`)

    (S_k(θP ∪ TⁿQ) − S_k(θP) S_k(Q))² ≤ r^{2n} · S_k(θP ∪ P) · (S_k(θQ ∪ Q) − S_k(Q)²).

`WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay` supplies, at every large coupling, a rate
with physical rate at least `c/L`; along the dyadic couplings a dyadic time `t = dySpacing N m · n` is
`2^{k-m} n` lattice steps, so `r^{2 · 2^{k-m} n} ≤ exp(−2 (c/L) t)` uniformly in `k`. Under
`UniformBound` the limit exists and (`contS_cluster_of_fixedWindowDecay`)

    (S(θP ∪ T_t Q) − S(θP) S(Q))² ≤ exp(−2 (c/L) t) · S(θP ∪ P) · (S(θQ ∪ Q) − S(Q)²),

exponential clustering at physical rate `c/L`, with `S(θP) = kern P ∅` and `S(Q) = kern ∅ Q`.

## Scope

`FixedWindowDecay` and `UniformBound` are the hypotheses; `2 ≤ N` is
`gapAt_physical_of_fixedWindowDecay`'s. Nothing here proves either hypothesis.

The bound is on the reflected form: positive-time monomials, translations along `τ`, dyadic times
`t ≥ 0`. It has content where `S(θQ ∪ Q) − S(Q)²` is non-zero; at bounded renormalisation data, the
only data at which `UniformBound` is proved, the limit is expected to be degenerate and both sides
zero (`ContinuumReconstruction.continuum_reconstruction_bare`).
-/

namespace MassGap.ContinuumCluster

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Gauge invariance and shifts of smeared fields -/

section Gauge

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- DERIVED: no numeral. -/
theorem isIGaugeInvariant_mul {F H : C(IConf G, ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant F)
    (hH : GaugeInvariantAlgebra.IsIGaugeInvariant H) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (F * H) := by
  intro g U
  show F (GaugeInvariantAlgebra.igaugeTransform g U) * H (GaugeInvariantAlgebra.igaugeTransform g U)
    = F U * H U
  rw [hF g U, hH g U]

/-- DERIVED: `1` is the empty product. -/
theorem isIGaugeInvariant_prod {ι : Type*} (s : Finset ι) (F : ι → C(IConf G, ℝ))
    (h : ∀ i ∈ s, GaugeInvariantAlgebra.IsIGaugeInvariant (F i)) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact GaugeInvariantAlgebra.isIGaugeInvariant_one
  | insert b s hb ih =>
    rw [Finset.prod_insert hb]
    exact isIGaugeInvariant_mul (h b (Finset.mem_insert_self b s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A smeared gauge-invariant field is gauge invariant.

DERIVED: `0` is the sign of `a`. -/
theorem isIGaugeInvariant_smear {a : ℝ} (ha : 0 < a) (O : LField G) (f : TestFn) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (smear a O.1 f) := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha O.1 f hf (Finset.Subset.refl _)]
  have h : (∑ x ∈ box ⌈R / a⌉₊, (a ^ 4 * f.1 (site a x)) • transObs x O.1)
      ∈ GaugeInvariantAlgebra.igaugeInv (G := G) :=
    Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (isIGaugeInvariant_transObs O.2.2 x))
  exact h

/-- `n` unit shifts in direction `τ` are the translation by `n` along `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. Each iterate is one unit step, through
`ishiftObsL_eq_transObs` in the proof. -/
theorem ishiftObsL_iterate (τ : Fin 4) (n : ℕ) (F : C(IConf G, ℝ)) :
    (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] F = transObs (axisVec τ n) F := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, axisVec_zero, transObs_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ishiftObsL_eq_transObs, transObs_transObs,
      ← axisVec_add, Nat.cast_succ, add_comm]

end Gauge

/-! ## 2. The renormalised monomial as a vector of the lattice transfer data -/

section Vector

/-- The empty monomial.

DERIVED: `0` factors. -/
abbrev emptyMono (N : ℕ) : Mono N := ⟨0, Fin.elim0⟩

/-- **The renormalised monomial of step `k`** as an observable: `Z_P · ∏ᵢ smear(Oᵢ − cᵢ) fᵢ`.

DERIVED: no numeral. -/
noncomputable def Yv (ρ : Renorm N) (k : ℕ) (P : Mono N) : C(Cfg N, ℝ) :=
  ρ.zmono k P • prodSmear (dySpacing N k) (ρ.mono k P)

/-- **Every renormalised reflected Schwinger function is a reflected pairing of vectors.**

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
reflection constant. -/
theorem latSkR_pairFam_eq (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ)
    (P Q : Mono N) :
    latSkR hN ρ k (pairFam τ P Q)
      = stateK hN k (LatticeReflection.ireflObs τ 0 (Yv ρ k P) * Yv ρ k Q) := by
  rw [latSkR_pairFam hN ρ τ hR, latSk_eq,
    latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  unfold Yv
  rw [map_smul, smul_mul_smul_comm, (stateK hN k).map_smul]

/-- DERIVED: `1` is the empty product. -/
theorem Yv_empty (ρ : Renorm N) (k : ℕ) : Yv ρ k (emptyMono N) = 1 := by
  unfold Yv Renorm.zmono prodSmear
  rw [Fintype.prod_empty, Fintype.prod_empty, one_smul]

/-- Translating a smeared product by a lattice vector translates every test function.

DERIVED: `0` is the sign of `a`. -/
theorem transObs_prodSmear {a : ℝ} (ha : 0 < a) (n : ISite) (P : Mono N) :
    transObs n (prodSmear a P) = prodSmear a (Mono.shift (site a n) P) := by
  unfold prodSmear
  rw [transObs_prod]
  exact Finset.prod_congr rfl (fun i _ => (smear_translate ha _ _ n).symm)

/-- DERIVED: `0` is the sign of the spacing. -/
theorem Yv_shift (ρ : Renorm N) (k : ℕ) (hk : 0 < dySpacing N k) (n : ISite) (Q : Mono N) :
    transObs n (Yv ρ k Q) = Yv ρ k (Mono.shift (site (dySpacing N k) n) Q) := by
  unfold Yv
  rw [map_smul, transObs_prodSmear hk]
  rfl

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem scaleSite_axisVec (c : ℤ) (τ : Fin 4) (n : ℤ) :
    scaleSite c (axisVec τ n) = axisVec τ (c * n) := by
  funext j
  by_cases h : j = τ <;> simp [scaleSite, axisVec, h]

/-- A positive-time renormalised monomial lies in the gauge-invariant half-space algebra once its
smeared factors lie in the half-space algebra.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
plane. -/
theorem Yv_mem (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (k : ℕ) (P : Mono N)
    (hk : ∀ i : Fin P.1, ∀ r : ℝ, smear (dySpacing N k) ((P.2 i).1.sub r).1 (P.2 i).2
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
  have h1 : prodSmear (dySpacing N k) (ρ.mono k P)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
      (fun i _ => hk i (ρ.c k (P.2 i).1))
  have h2 : GaugeInvariantAlgebra.IsIGaugeInvariant (prodSmear (dySpacing N k) (ρ.mono k P)) :=
    isIGaugeInvariant_prod Finset.univ _
      (fun i _ => isIGaugeInvariant_smear (dySpacing_pos (one_le_of_ne_zero hN) k) _ _)
  have h3 : prodSmear (dySpacing N k) (ρ.mono k P)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Submodule.mem_inf.mpr ⟨h1, h2⟩
  exact Submodule.smul_mem _ _ h3

/-- The transfer data of step `k`: the gauge-invariant transfer data at the periodic state of the
coupling `dyBeta k`, for the plane `x_τ = 0`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
plane. -/
noncomputable def Dk (hN : N ≠ 0) (τ : Fin 4) (k : ℕ) :
    Transfer.TransferData
      ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :=
  PeriodicState.periodicGaugeInvData τ 0 hN (dyBeta (one_le_of_ne_zero hN) k)

/-- The form of `Dk` is the reflected pairing in the state of step `k`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
plane and the reflection constant. -/
theorem Dk_form (hN : N ≠ 0) (τ : Fin 4) (k : ℕ)
    (y x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)) :
    (Dk hN τ k).form y x
      = stateK hN k (LatticeReflection.ireflObs τ 0 (y : C(Cfg N, ℝ)) * (x : C(Cfg N, ℝ))) :=
  rfl

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
plane; `1` is the unit observable. -/
theorem Dk_vac (hN : N ≠ 0) (τ : Fin 4) (k : ℕ) :
    (((Dk hN τ k).vac : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0))
      : C(Cfg N, ℝ)) = 1 :=
  rfl

/-- The `n`-th power of the transfer operator is the `n`-fold unit shift.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `0` is the
plane. -/
theorem Dk_T_pow (hN : N ≠ 0) (τ : Fin 4) (k n : ℕ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)) :
    ((((Dk hN τ k).T ^ n) x
        : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0))
        : C(Cfg N, ℝ))
      = (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] (x : C(Cfg N, ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

/-- The form of the vacuum-orthogonal part.

DERIVED: `2` is the square of the vacuum coefficient. -/
theorem form_vacProj {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    (x : A) :
    D.form (TransferGap.vacProj D x) (TransferGap.vacProj D x)
      = D.form x x - D.form x D.vac ^ 2 := by
  have hs := D.toPreForm.form_symm D.vac x
  unfold TransferGap.vacProj
  simp only [FiniteOrderTransfer.form_sub_left, FiniteOrderTransfer.form_sub_right,
    Transfer.PreForm.form_smul_left, Transfer.PreForm.form_smul_right, D.vac_norm]
  linear_combination (-(D.form x D.vac)) * hs

end Vector

/-! ## 3. Clustering at each step, and in the limit -/

section Cluster

/-- **Clustering at step `k` from a `GapAt` rate** (`TransferGap.clustering_sq` read on the
renormalised Schwinger functions): with `S_k = latSkR hN ρ k`,

    (S_k(θP ∪ TⁿQ) − S_k(θP ∪ ∅) S_k(θ∅ ∪ Q))² ≤ r^{2n} · Y,   0 ≤ Y,

`Y = S_k(θP ∪ P) · (S_k(θQ ∪ Q) − S_k(θ∅ ∪ Q)²)`, `Tⁿ` the translation by `n` lattice steps.

DERIVED: `0` is the excluded colour count, the plane and the sign of `r` and of `Y`; `4` in `Fin 4`
is the spacetime dimension; `2` is the square. -/
theorem lattice_cluster (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hg : TransferGap.GapAt (Dk hN τ k) r) (P Q : Mono N)
    (hP : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : Yv ρ k Q ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (n : ℕ) :
    (latSkR hN ρ k (pairFam τ P (Mono.shift (site (dySpacing N k) (axisVec τ n)) Q))
        - latSkR hN ρ k (pairFam τ P (emptyMono N)) * latSkR hN ρ k (pairFam τ (emptyMono N) Q))
          ^ 2
      ≤ r ^ (2 * n) * (latSkR hN ρ k (pairFam τ P P)
          * (latSkR hN ρ k (pairFam τ Q Q) - latSkR hN ρ k (pairFam τ (emptyMono N) Q) ^ 2))
    ∧ 0 ≤ latSkR hN ρ k (pairFam τ P P)
          * (latSkR hN ρ k (pairFam τ Q Q) - latSkR hN ρ k (pairFam τ (emptyMono N) Q) ^ 2) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have h := TransferGap.clustering_sq (Dk hN τ k) hr hg n ⟨Yv ρ k Q, hQ⟩ ⟨Yv ρ k P, hP⟩
  have hY := mul_nonneg ((Dk hN τ k).form_nonneg ⟨Yv ρ k P, hP⟩)
    ((Dk hN τ k).form_nonneg (TransferGap.vacProj (Dk hN τ k) ⟨Yv ρ k Q, hQ⟩))
  have e1 : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ (((Dk hN τ k).T ^ n) ⟨Yv ρ k Q, hQ⟩)
      = latSkR hN ρ k (pairFam τ P (Mono.shift (site (dySpacing N k) (axisVec τ n)) Q)) := by
    rw [Dk_form, Dk_T_pow, ishiftObsL_iterate, Yv_shift ρ k ha _ Q,
      latSkR_pairFam_eq hN ρ τ hR k P (Mono.shift (site (dySpacing N k) (axisVec τ n)) Q)]
  have e2 : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ (Dk hN τ k).vac
      = latSkR hN ρ k (pairFam τ P (emptyMono N)) := by
    rw [Dk_form, Dk_vac, latSkR_pairFam_eq hN ρ τ hR k P (emptyMono N), Yv_empty]
  have e3 : (Dk hN τ k).form (Dk hN τ k).vac ⟨Yv ρ k Q, hQ⟩
      = latSkR hN ρ k (pairFam τ (emptyMono N) Q) := by
    rw [Dk_form, Dk_vac, latSkR_pairFam_eq hN ρ τ hR k (emptyMono N) Q, Yv_empty]
  have e4 : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k P, hP⟩ = latSkR hN ρ k (pairFam τ P P) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k P P]
  have e5 : (Dk hN τ k).form (TransferGap.vacProj (Dk hN τ k) ⟨Yv ρ k Q, hQ⟩)
        (TransferGap.vacProj (Dk hN τ k) ⟨Yv ρ k Q, hQ⟩)
      = latSkR hN ρ k (pairFam τ Q Q) - latSkR hN ρ k (pairFam τ (emptyMono N) Q) ^ 2 := by
    rw [form_vacProj, (Dk hN τ k).toPreForm.form_symm _ (Dk hN τ k).vac, e3, Dk_form,
      latSkR_pairFam_eq hN ρ τ hR k Q Q]
  rw [e1, e2, e3, e4, e5] at h
  rw [e4, e5] at hY
  exact ⟨h, hY⟩

#print axioms lattice_cluster

/-- **OS4 for the limit, derived from `FixedWindowDecay`.** At `2 ≤ N`, a window `L > 0`,
`FixedWindowDecay τ 0 hN L`, `UniformBound` and reflection-compatible data, there is `c > 0` such that
for all positive-time monomials `P`, `Q` and every dyadic time `t = dySpacing N m · n`, `n ∈ ℕ`,
along `τ`,

    (S(θP ∪ T_t Q) − S(θP) S(Q))² ≤ exp(−2 (c/L) t) · S(θP ∪ P) · (S(θQ ∪ Q) − S(Q)²),

with `S(θP) = kern P ∅`, `S(Q) = kern ∅ Q`: exponential clustering at physical rate `c/L`.

DERIVED: `2 ≤ N` is `gapAt_physical_of_fixedWindowDecay`'s, the least rank with a non-zero Haar
variance of the real trace; `2` is also the square; `0` is the excluded colour count, the plane of
`FixedWindowDecay τ 0`, and the sign of `c` and of `L`; `4` in `Fin 4` is the spacetime dimension.
-/
theorem contS_cluster_of_fixedWindowDecay (hN2 : 2 ≤ N) (hN : N ≠ 0) (ρ : Renorm N)
    (hB : UniformBound hN ρ) (τ : Fin 4) (hR : ρ.ReflCompat τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P Q : PosMono N τ) (m n : ℕ),
      (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2
        ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
          * (kern hN ρ τ P.1 P.1
            * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hN1 := one_le_of_ne_zero hN
  obtain ⟨c, hc, hev⟩ := WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay τ 0 hN2 hN hL hW
  have hevk : ∀ᶠ k in atTop, ∃ r : ℝ, TransferGap.GapAt (Dk hN τ k) r
      ∧ PeriodicContent.PeriodicClayGapAt τ 0 hN (dyBeta hN1 k) r
      ∧ c / L ≤ -Real.log r / AsymptoticScaling.aRun N (dyBeta hN1 k) :=
    (tendsto_dyBeta hN1).eventually hev
  refine ⟨c, hc, fun P Q m n => ?_⟩
  have hmemP : ∀ᶠ k in atTop, ∀ i : Fin P.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.2 i).1.sub r).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (P.2 i))
  have hmemQ : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((Q.1.2 i).1.sub r).1 (Q.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (Q.2 i))
  have hf : Tendsto (fun k => (latSkR hN ρ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
        - latSkR hN ρ k (pairFam τ P.1 (emptyMono N))
          * latSkR hN ρ k (pairFam τ (emptyMono N) Q.1)) ^ 2) (ultra : Filter ℕ)
      (𝓝 ((kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2)) :=
    ((tendsto_contS hN ρ hB _).sub
      ((tendsto_contS hN ρ hB _).mul (tendsto_contS hN ρ hB _))).pow 2
  have hg : Tendsto (fun k => Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (latSkR hN ρ k (pairFam τ P.1 P.1)
          * (latSkR hN ρ k (pairFam τ Q.1 Q.1)
            - latSkR hN ρ k (pairFam τ (emptyMono N) Q.1) ^ 2))) (ultra : Filter ℕ)
      (𝓝 (Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)))) :=
    ((tendsto_contS hN ρ hB _).mul
      ((tendsto_contS hN ρ hB _).sub ((tendsto_contS hN ρ hB _).pow 2))).const_mul _
  refine le_of_tendsto_of_tendsto hf hg ?_
  have hevLE : ∀ᶠ k in atTop,
      (latSkR hN ρ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
        - latSkR hN ρ k (pairFam τ P.1 (emptyMono N))
          * latSkR hN ρ k (pairFam τ (emptyMono N) Q.1)) ^ 2
      ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (latSkR hN ρ k (pairFam τ P.1 P.1)
          * (latSkR hN ρ k (pairFam τ Q.1 Q.1)
            - latSkR hN ρ k (pairFam τ (emptyMono N) Q.1) ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop m, hevk, hmemP, hmemQ] with k hk hkr hkP hkQ
    obtain ⟨r, hg, hclay, hrate⟩ := hkr
    have ha := dySpacing_pos hN1 k
    have hr0 : 0 < r := hclay.1
    have hvec : site (dySpacing N k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ))
        = timeVec N m τ n := by
      unfold timeVec
      rw [site_dySpacing N hk, scaleSite_axisVec]
      congr 2
    obtain ⟨hcl, hY⟩ := lattice_cluster hN ρ τ hR k hr0.le hg P.1 Q.1
      (Yv_mem hN ρ τ k P.1 hkP) (Yv_mem hN ρ τ k Q.1 hkQ) (2 ^ (k - m) * n)
    rw [hvec] at hcl
    have hlog : Real.log r ≤ -(c / L) * dySpacing N k := by
      have h1 := hrate
      rw [aRun_dyBeta, le_div_iff₀ ha] at h1
      linarith
    have hr_le : r ≤ Real.exp (-(c / L) * dySpacing N k) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.mpr hlog
    have hpow : r ^ (2 * (2 ^ (k - m) * n)) ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n)) := by
      calc r ^ (2 * (2 ^ (k - m) * n))
          ≤ Real.exp (-(c / L) * dySpacing N k) ^ (2 * (2 ^ (k - m) * n)) :=
            pow_le_pow_left₀ hr0.le hr_le _
        _ = Real.exp (((2 * (2 ^ (k - m) * n) : ℕ) : ℝ) * (-(c / L) * dySpacing N k)) :=
            (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(2 * (c / L)) * (dySpacing N m * n)) := by
            rw [← dySpacing_mul_pow N hk]
            push_cast
            congr 1
            ring
    exact hcl.trans (mul_le_mul_of_nonneg_right hpow hY)
  exact hevLE.filter_mono ultra_le

#print axioms contS_cluster_of_fixedWindowDecay

end Cluster

end MassGap.ContinuumCluster
