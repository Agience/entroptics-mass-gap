import Mathlib
import MassGap.ContinuumHypercubic
import MassGap.ObserverEnergyReductionsN

noncomputable section

/-!
# MassGap.ObserverOS — the Osterwalder–Schrader axioms of the observer's energy-density theory

The observer's energy density at step `k` is `energyOn W D hD s hs`, for any `W : ConfFlow N`, a
reflection-closed class `D` of non-negative fields and a subtraction `s`. Here `s = 0` (`energy0`), the
paper's plaquette-class choice. Its limit Schwinger functions are `contSF hN (energy0 W D hD) F`, for
families `F : ι → SField N` of a field and a bounded test function of bounded support.

## OS0 in the sup norm, from the cube moments

`abs_state_prod_le` is the arithmetic–geometric form of Hölder's inequality in a state: if every
factor has `ν(Gᵢ^{2n}) ≤ c Lᵢ^{2n}`, `n` the number of factors, then `|ν(∏ Gᵢ)| ≤ (1 + n c) ∏ Lᵢ`.
At step `k` the smeared energy density against `g` with `|g| ≤ M`, support in `[-R, R]⁴`, is at most
`M` times the cube energy `cubeSum a_k R (O ∘ V_k)` (`ObserverEnergyBox.abs_smear_scaled_le` at
`s = 0`), so its `2n`-th moment is at most `M^{2n}` times the cube moment. Hence
`abs_contSF_energy0_le`: if the cube moments of order `2n` of the family's fields are at most `c`
eventually, `|S_n(g₁, …, gₙ)| ≤ (1 + n c) ∏ Mᵢ`. With (E) in its cube form (`CubeMomentBound`),
`exists_os0_const` gives for each tuple of fields and each cube one constant `K` with
`|S_n| ≤ K ∏ ‖gᵢ‖_∞` for every family of test functions supported in that cube. With one exponential
cube moment (`CubeExpBound`) the constant is explicit in `n`: `os0_factorial` gives
`K_n = 1 + n (2n)! t^{-2n} C`, the factorial growth of the Osterwalder–Schrader linear growth
condition, on each cube.

## Multilinearity and continuity in the test functions

`testAdd`, `testSmul` are the vector operations on test functions. `contSF_update_add`,
`contSF_update_smul`: for any flow under its uniform bound the limit is additive and homogeneous in
each test function. With the sup-norm bound, `abs_contSF_energy0_sub_le`: two families with the same
fields, test functions in one cube within `δ` of each other in sup norm, have Schwinger functions within
`(1 + n c) ∑ₐ δ ∏_{i ≠ a} Mᵢ`.

## OS1 on all of ℝ⁴

`contSF_energy0_translate_real`: given (E), translating every test function of a family of energy
densities with uniformly continuous test functions by any `v ∈ ℝ⁴` leaves the limit unchanged. No
separation of supports is needed. The dyadic translations (`ContinuumFlow.contSF_translate`) are
dense (`ContinuumHypercubic.exists_dyadic_of_eventually`), and the sup-norm continuity above carries
the invariance to their closure.

## The package

`observer_os`: given (E) on a non-negative reflection-closed class, the observer's energy-density
theory has OS0 in the sup norm on each cube, multilinearity, OS1 for every real translation (uniformly
continuous test functions) and every axis reflection, OS3, and OS2 on margin monomials beyond the
flow's range. OS4 (clustering) is `ObserverEnergyReductionsN.flowN_clay_of_gap` given (M).

## What remains, stated

`TemperedGrowth`: one bound uniform in the cube, `|S_n| ≤ α γⁿ (n!)^β ∏ Mᵢ (2Rᵢ + 3)⁴`, which with
continuity would extend the Schwinger functions to Schwartz test functions. (E) gives a constant per
cube and per `n`; the dependence on the cube is not controlled by (E) as stated.
-/

namespace MassGap.ObserverOS

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox Filter
open scoped Topology

/-! ## 1. Hölder's inequality in a state, arithmetic–geometric form -/

section Holder

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **A product of `n` observables through a state**: if `ν(Gᵢ^{2n}) ≤ c Lᵢ^{2n}` with `Lᵢ > 0`, `n` the
number of factors, then `|ν(∏ Gᵢ)| ≤ (1 + n c) ∏ Lᵢ`. Rescale `Yᵢ = Gᵢ / Lᵢ`; pointwise
`|∏ Yᵢ| ≤ 1 + ∑ Yᵢ^{2n}` (`ObserverEnergyMoments.abs_prod_le_one_add_sum_pow`), and each
`ν(Yᵢ^{2n}) ≤ c`.

DERIVED: `1` and `2` are `abs_prod_le_one_add_sum_pow`'s; `0` the sign of `Lᵢ`. -/
theorem abs_state_prod_le (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι]
    (G : ι → C(X, ℝ)) (L : ι → ℝ) (hL : ∀ i, 0 < L i) {c : ℝ}
    (h : ∀ i, ν (G i ^ (2 * Fintype.card ι)) ≤ c * L i ^ (2 * Fintype.card ι)) :
    |ν (∏ i, G i)| ≤ (1 + Fintype.card ι * c) * ∏ i, L i := by
  set Y : ι → C(X, ℝ) := fun i => (L i)⁻¹ • G i with hY
  have hprod : ∏ i, G i = (∏ i, L i) • ∏ i, Y i := by
    have h1 : ∏ i, Y i = (∏ i, (L i)⁻¹) • ∏ i, G i := prod_smul_eq Finset.univ _ G
    rw [h1, smul_smul, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun i _ => mul_inv_cancel₀ (hL i).ne'), Finset.prod_const_one,
      one_smul]
  have hY2 : ∀ i, ν (Y i ^ (2 * Fintype.card ι)) ≤ c := by
    intro i
    have hLp : 0 < L i ^ (2 * Fintype.card ι) := pow_pos (hL i) _
    have e : Y i ^ (2 * Fintype.card ι)
        = ((L i)⁻¹ ^ (2 * Fintype.card ι)) • G i ^ (2 * Fintype.card ι) := smul_pow _ _ _
    rw [e, ν.map_smul, inv_pow]
    calc (L i ^ (2 * Fintype.card ι))⁻¹ * ν (G i ^ (2 * Fintype.card ι))
        ≤ (L i ^ (2 * Fintype.card ι))⁻¹ * (c * L i ^ (2 * Fintype.card ι)) :=
          mul_le_mul_of_nonneg_left (h i) (inv_nonneg.mpr hLp.le)
      _ = c := by field_simp
  have hpt := abs_state_le_of_abs_le ν (∏ i, Y i) (1 + ∑ i, Y i ^ (2 * Fintype.card ι))
    (fun U => by
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.sum_apply,
        ContinuousMap.prod_apply, ContinuousMap.pow_apply]
      exact abs_prod_le_one_add_sum_pow _)
  rw [ν.map_add, ν.map_one, ν.map_sum] at hpt
  have hsum : ∑ i, ν (Y i ^ (2 * Fintype.card ι)) ≤ Fintype.card ι * c := by
    calc ∑ i, ν (Y i ^ (2 * Fintype.card ι)) ≤ ∑ _i : ι, c :=
          Finset.sum_le_sum (fun i _ => hY2 i)
      _ = Fintype.card ι * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP : 0 ≤ ∏ i, L i := Finset.prod_nonneg (fun i _ => (hL i).le)
  rw [hprod, ν.map_smul, abs_mul, abs_of_nonneg hP]
  calc (∏ i, L i) * |ν (∏ i, Y i)| ≤ (∏ i, L i) * (1 + Fintype.card ι * c) :=
        mul_le_mul_of_nonneg_left (hpt.trans (by linarith)) hP
    _ = (1 + Fintype.card ι * c) * ∏ i, L i := mul_comm _ _

#print axioms abs_state_prod_le

end Holder

/-! ## 2. OS0 in the sup norm on each cube -/

section OS0

variable {N : ℕ}

/-- The zero subtraction.

DERIVED: `0` is the subtraction. -/
def s0 (N : ℕ) : ℕ → LField (MassGap.SUN.SU N) → ℝ := fun _ _ => 0

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem s0_refl (N : ℕ) :
    ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s0 N k (O.refl τ) = s0 N k O :=
  fun _ _ _ => rfl

#print axioms s0_refl

/-- **The observer's energy density on the class `D`**: `a_k⁻⁴ (O ∘ V_k)` for `O ∈ D`, `O ∘ V_k`
otherwise (`ObserverEnergyMoments.energyOn` at `s = 0`).

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def energy0 (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) : Flow N :=
  energyOn W D hD (s0 N) (s0_refl N)

/-- A test function bounded by `M` is bounded by every `M' ≥ M`.

DERIVED: no numeral. -/
theorem isTest_mono {f : (Fin 4 → ℝ) → ℝ} {R M M' : ℝ} (h : IsTest f R M) (hM : M ≤ M') :
    IsTest f R M' :=
  ⟨h.1, fun y => (h.2.1 y).trans hM, h.2.2⟩

#print axioms isTest_mono

/-- **The smeared energy density is dominated by the cube energy**: for `O ∈ D` non-negative, `|g| ≤ M`
supported in `[-R, R]⁴` and `a_k ≤ 1`, `|smear a_k (a_k⁻⁴ O ∘ V_k) g| ≤ M · cubeSum a_k R (O ∘ V_k)`
pointwise (`ObserverEnergyBox.abs_smear_scaled_le` at `s = 0`).

DERIVED: `0` is the excluded colour count; `1` the spacing bound. -/
theorem abs_smear_energy0_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) {k : ℕ}
    (hk1 : dySpacing N k ≤ 1) (f : TestFn) {R M : ℝ} (hf : IsTest f.1 R M) (U : Cfg N) :
    |smear (dySpacing N k) ((energy0 W D hD).map k O).1 f U|
      ≤ M * cubeSum (dySpacing N k) R (W.fieldMap k O).1 U := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [energy0, energyOn_map_of_mem W hD (s0_refl N) hO k]
  have h := abs_smear_scaled_le ha hk1 (W.fieldMap k O).1 (fun U => hpos O hO (W.V k U))
    (s0 N k O) f hf U
  have hz : M * (2 * R + 3) ^ 4 * (|s0 N k O| / dySpacing N k ^ 4) = 0 := by
    simp [s0]
  rw [hz, add_zero] at h
  exact h

#print axioms abs_smear_energy0_le

/-- **The moments of the smeared energy density from the cube moments**:
`ν_k((smear a_k (a_k⁻⁴ O ∘ V_k) g)^{2p}) ≤ M^{2p} ν_k(cubeSum^{2p})`.

DERIVED: `0` is the excluded colour count; `1` the spacing bound; `2` makes the power even. -/
theorem moment_smear_energy0_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) {k : ℕ}
    (hk1 : dySpacing N k ≤ 1) (f : TestFn) {R M : ℝ} (hf : IsTest f.1 R M) (p : ℕ) :
    stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * p))
      ≤ M ^ (2 * p) * stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p)) := by
  have hq : Even (2 * p) := even_two_mul p
  rw [← (stateK hN k).map_smul]
  refine (stateK hN k).mono (fun U => ?_)
  simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← hq.pow_abs, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_smear_energy0_le hN W hD hpos hO hk1 f hf U) _

#print axioms moment_smear_energy0_le

/-- **OS0 at one step**: a family of `n` smeared energy densities with `|gᵢ| ≤ Lᵢ`, `Lᵢ > 0`, supports in
`[-R, R]⁴`, whose cube moments of order `2n` are at most `c`, has `|S_n| ≤ (1 + n c) ∏ Lᵢ` at that step.

DERIVED: `0` is the excluded colour count and the sign of `Lᵢ`; `1` the spacing bound and
`abs_state_prod_le`'s; `2` makes the power even. -/
theorem abs_latSF_energy0_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] (G : ι → SField N)
    (hG : ∀ i, (G i).1 ∈ D) {R c : ℝ} {k : ℕ} (hk1 : dySpacing N k ≤ 1)
    (hc : ∀ i, stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (G i).1).1
      ^ (2 * Fintype.card ι)) ≤ c)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (hT : ∀ i, IsTest (G i).2.1 R (L i)) :
    |latSF hN (energy0 W D hD) k G| ≤ (1 + Fintype.card ι * c) * ∏ i, L i := by
  show |latSk hN k (fun i => (energy0 W D hD).field k (G i))| ≤ _
  rw [latSk_eq]
  show |stateK hN k (∏ i, smear (dySpacing N k) ((energy0 W D hD).map k (G i).1).1 (G i).2)| ≤ _
  refine abs_state_prod_le (stateK hN k) _ L hL (fun i => ?_)
  calc stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k (G i).1).1 (G i).2
        ^ (2 * Fintype.card ι))
      ≤ L i ^ (2 * Fintype.card ι) * stateK hN k (cubeSum (dySpacing N k) R
          (W.fieldMap k (G i).1).1 ^ (2 * Fintype.card ι)) :=
        moment_smear_energy0_le hN W hD hpos (hG i) hk1 (G i).2 (hT i) _
    _ ≤ L i ^ (2 * Fintype.card ι) * c :=
        mul_le_mul_of_nonneg_left (hc i) (pow_nonneg (hL i).le _)
    _ = c * L i ^ (2 * Fintype.card ι) := mul_comm _ _

#print axioms abs_latSF_energy0_le

/-- **OS0 for the limit, in the sup norm on one cube**: if the fields of the family have cube moments
of order `2n` at most `c` eventually, then the limit Schwinger function exists (the sequence is
bounded) and `|S_n(g₁, …, gₙ)| ≤ (1 + n c) ∏ Mᵢ` for `|gᵢ| ≤ Mᵢ` supported in `[-R, R]⁴`. The bound
holds at `Mᵢ + ε` for every `ε > 0` and passes to `ε = 0` by continuity.

DERIVED: `0` is the excluded colour count, the lower end of `ε` and the limit point; `1` the spacing
bound and `abs_state_prod_le`'s; `2` makes the power even. -/
theorem abs_contSF_energy0_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ι : Type} [Fintype ι] (G : ι → SField N)
    (hG : ∀ i, (G i).1 ∈ D) {R c : ℝ}
    (hc : ∀ i, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (G i).1).1
      ^ (2 * Fintype.card ι)) ≤ c)
    (M : ι → ℝ) (hM : ∀ i, IsTest (G i).2.1 R (M i)) :
    |contSF hN (energy0 W D hD) G| ≤ (1 + Fintype.card ι * c) * ∏ i, M i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hM i).M_nonneg
  have key : ∀ ε : ℝ, 0 < ε →
      |contSF hN (energy0 W D hD) G| ≤ (1 + Fintype.card ι * c) * ∏ i, (M i + ε) := by
    intro ε hε
    have hev : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k G|
        ≤ (1 + Fintype.card ι * c) * ∏ i, (M i + ε) := by
      filter_upwards [Filter.eventually_all.mpr hc,
        (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hck hk1
      exact abs_latSF_energy0_le hN W hD hpos G hG hk1.le hck (fun i => M i + ε)
        (fun i => by linarith [hM0 i]) (fun i => isTest_mono (hM i) (by linarith))
    obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hev
    have hlim : contSF hN (energy0 W D hD) G = x := hx.limUnder_eq
    rw [hlim]
    exact le_of_tendsto hx.abs (hev.filter_mono ultra_le)
  have hcont : Continuous (fun ε : ℝ => (1 + Fintype.card ι * c) * ∏ i, (M i + ε)) :=
    continuous_const.mul (continuous_finset_prod _ (fun i _ => continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ => (1 + Fintype.card ι * c) * ∏ i, (M i + ε)) (𝓝[>] 0)
      (𝓝 ((1 + Fintype.card ι * c) * ∏ i, (M i + 0))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun ε hε => key ε hε))
  simpa only [add_zero] using h

#print axioms abs_contSF_energy0_le

/-- **OS0 from (E)**: for every tuple of fields of `D` and every cube `[-R, R]⁴` one constant `K > 0`
bounds every limit Schwinger function of those fields smeared against test functions supported in the
cube: `|S_n(g₁, …, gₙ)| ≤ K ∏ ‖gᵢ‖_∞`. `K = 1 + n ∑ᵢ |Cᵢ|`, `Cᵢ` the cube bound of order `2n`.

DERIVED: `0` is the excluded colour count, the lower end of `R` and of `K`; `1` and `2` as in
`abs_contSF_energy0_le`. -/
theorem exists_os0_const (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, O i ∈ D)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ G : ι → SField N, (∀ i, (G i).1 = O i) → ∀ M : ι → ℝ,
      (∀ i, IsTest (G i).2.1 R (M i)) → |contSF hN (energy0 W D hD) G| ≤ K * ∏ i, M i := by
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (O i)).1 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => hcube (O i) (hO i) R hR (Fintype.card ι)
  choose C hC using hC
  have hc0 : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1 + Fintype.card ι * ∑ i, |C i|, by positivity, fun G hGO M hM => ?_⟩
  refine abs_contSF_energy0_le hN W hD hpos G (fun i => by rw [hGO i]; exact hO i)
    (fun i => ?_) M hM
  rw [hGO i]
  exact (hC i).mono (fun k hk => hk.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))))

#print axioms exists_os0_const

/-- **OS0 with factorial growth from one exponential cube moment**: for one field `O ∈ D` with
`CubeExpBound`, on each cube there are `t > 0` and `C` such that for every `n`,
`|S_n(g₁, …, gₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ ‖gᵢ‖_∞` (`ObserverEnergyBox.state_pow_le_exp`:
`x^{2n} ≤ (2n)! t^{-2n} e^{tx}`). Since `(2n)! ≤ 4ⁿ (n!)²`, the `n`-dependence is that of the
Osterwalder–Schrader linear growth condition.

DERIVED: `0` is the excluded colour count, the lower end of `R`, `t` and the sign of the field; `1`
and `2` as in `abs_contSF_energy0_le`. -/
theorem os0_factorial (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (hexp : CubeExpBound hN W O) {R : ℝ} (hR : 0 ≤ R) :
    ∃ t C : ℝ, 0 < t ∧ ∀ (n : ℕ) (f : Fin n → TestFn) (M : Fin n → ℝ),
      (∀ i, IsTest (f i).1 R (M i)) →
        |contSF hN (energy0 W D hD) (fun i => (O, f i))|
          ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, M i := by
  obtain ⟨t, C, ht, hC⟩ := hexp R hR
  refine ⟨t, C, ht, fun n f M hM => ?_⟩
  have hc : ∀ i : Fin n, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k ((fun i : Fin n => (O, f i)) i).1).1 ^ (2 * Fintype.card (Fin n)))
        ≤ ((2 * n).factorial : ℝ) / t ^ (2 * n) * C := by
    intro i
    filter_upwards [hC] with k hk
    have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
    rw [Fintype.card_fin]
    exact (state_pow_le_exp (stateK hN k) _ (cubeSum_nonneg _ _ hF) ht (2 * n)).trans
      (mul_le_mul_of_nonneg_left hk (div_nonneg (by positivity) (pow_pos ht _).le))
  have h := abs_contSF_energy0_le hN W hD hpos (fun i : Fin n => (O, f i)) (fun _ => hO) hc M hM
  rw [Fintype.card_fin] at h
  exact h

#print axioms os0_factorial

end OS0

/-! ## 3. Multilinearity in the test functions -/

section Linear

variable {N : ℕ}

/-- The sum of two test functions.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` the vanishing value. -/
def testAdd (f g : TestFn) : TestFn :=
  ⟨fun y => f.1 y + g.1 y, by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    obtain ⟨R', M', _hR', hM', hs'⟩ := g.2
    refine ⟨max R R', M + M', le_max_of_le_left hR,
      fun y => (abs_add_le _ _).trans (add_le_add (hM y) (hM' y)), fun y hy i => ?_⟩
    by_cases hf : f.1 y = 0
    · have hg : g.1 y ≠ 0 := by
        intro hg
        exact hy (show f.1 y + g.1 y = 0 by rw [hf, hg, add_zero])
      exact (hs' y hg i).trans (le_max_right _ _)
    · exact (hs y hf i).trans (le_max_left _ _)⟩

/-- A real multiple of a test function.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` the vanishing value. -/
def testSmul (c : ℝ) (f : TestFn) : TestFn :=
  ⟨fun y => c * f.1 y, by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    exact ⟨R, |c| * M, hR, fun y => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg c),
      fun y hy i => hs y (fun h => hy (show c * f.1 y = 0 by rw [h, mul_zero])) i⟩⟩

/-- **Smearing is additive in the test function.** Both sides are sums over one box containing the
three supports.

DERIVED: `0` is the sign of `a`; `4` the cell-volume exponent. -/
theorem smear_testAdd {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (f g : TestFn) :
    smear a F (testAdd f g) = smear a F f + smear a F g := by
  obtain ⟨R, M, hf⟩ := f.2
  obtain ⟨R', M', hg⟩ := g.2
  obtain ⟨R'', M'', hfg⟩ := (testAdd f g).2
  rw [smear_eq_sum ha F (testAdd f g) hfg
      (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊) Finset.subset_union_right,
    smear_eq_sum ha F f hf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊)
      (Finset.subset_union_left.trans Finset.subset_union_left),
    smear_eq_sum ha F g hg (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊ ∪ box ⌈R'' / a⌉₊)
      (Finset.subset_union_right.trans Finset.subset_union_left),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← add_smul]
  congr 1
  show a ^ 4 * (f.1 (site a x) + g.1 (site a x)) = a ^ 4 * f.1 (site a x) + a ^ 4 * g.1 (site a x)
  ring

#print axioms smear_testAdd

/-- **Smearing is homogeneous in the test function.**

DERIVED: `0` is the sign of `a`; `4` the cell-volume exponent. -/
theorem smear_testSmul {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (c : ℝ) (f : TestFn) :
    smear a F (testSmul c f) = c • smear a F f := by
  obtain ⟨R, M, hf⟩ := f.2
  obtain ⟨R', M', hcf⟩ := (testSmul c f).2
  rw [smear_eq_sum ha F (testSmul c f) hcf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊)
      Finset.subset_union_right,
    smear_eq_sum ha F f hf (s := box ⌈R / a⌉₊ ∪ box ⌈R' / a⌉₊) Finset.subset_union_left,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_smul]
  congr 1
  show a ^ 4 * (c * f.1 (site a x)) = c * (a ^ 4 * f.1 (site a x))
  ring

#print axioms smear_testSmul

/-- **The lattice function of a family with one slot replaced** is the state of the replaced factor
times the product of the others.

DERIVED: no numeral. -/
theorem latSF_update (hN : N ≠ 0) (Φ : Flow N) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → SField N) (j : ι) (x : SField N) :
    latSF hN Φ k (Function.update B j x)
      = stateK hN k (smear (dySpacing N k) (Φ.map k x.1).1 x.2
          * ∏ i ∈ Finset.univ.erase j, smear (dySpacing N k) (Φ.map k (B i).1).1 (B i).2) := by
  show latSk hN k (fun i => Φ.field k (Function.update B j x i)) = _
  rw [latSk_eq]
  show stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (Function.update B j x i).1).1
    (Function.update B j x i).2) = _
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

#print axioms latSF_update

/-- **The limit is additive in each test function**, for any flow under its uniform bound.

DERIVED: `0` is the excluded colour count. -/
theorem contSF_update_add (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (B : ι → SField N) (j : ι) (O : LField (MassGap.SUN.SU N))
    (f g : TestFn) :
    contSF hN Φ (Function.update B j (O, testAdd f g))
      = contSF hN Φ (Function.update B j (O, f)) + contSF hN Φ (Function.update B j (O, g)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have h2 := (tendsto_contSF hN Φ hB (Function.update B j (O, f))).add
    (tendsto_contSF hN Φ hB (Function.update B j (O, g)))
  refine tendsto_nhds_unique (tendsto_contSF hN Φ hB (Function.update B j (O, testAdd f g)))
    (h2.congr (fun k => ?_))
  rw [latSF_update, latSF_update, latSF_update]
  show _ = stateK hN k (smear (dySpacing N k) (Φ.map k O).1 (testAdd f g) * _)
  rw [smear_testAdd (dySpacing_pos (one_le_of_ne_zero hN) k), add_mul, (stateK hN k).map_add]

#print axioms contSF_update_add

/-- **The limit is homogeneous in each test function**, for any flow under its uniform bound.

DERIVED: `0` is the excluded colour count. -/
theorem contSF_update_smul (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (B : ι → SField N) (j : ι) (O : LField (MassGap.SUN.SU N))
    (c : ℝ) (f : TestFn) :
    contSF hN Φ (Function.update B j (O, testSmul c f))
      = c * contSF hN Φ (Function.update B j (O, f)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have h2 := (tendsto_contSF hN Φ hB (Function.update B j (O, f))).const_mul c
  refine tendsto_nhds_unique (tendsto_contSF hN Φ hB (Function.update B j (O, testSmul c f)))
    (h2.congr (fun k => ?_))
  rw [latSF_update, latSF_update]
  show _ = stateK hN k (smear (dySpacing N k) (Φ.map k O).1 (testSmul c f) * _)
  rw [smear_testSmul (dySpacing_pos (one_le_of_ne_zero hN) k), smul_mul_assoc,
    (stateK hN k).map_smul]

#print axioms contSF_update_smul

/-- **E gives the uniform bound of `energy0`** (`ObserverEnergyBox.smearedMoments_of_cubeMoments` at
the zero subtraction, `ObserverEnergyReductionsN.energyBoundN`).

DERIVED: `0` is the excluded colour count. -/
theorem uniformBoundF_energy0 (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) :
    UniformBoundF hN (energy0 W D hD) :=
  ObserverEnergyReductionsN.energyBoundN hN W D hD (s0 N) (s0_refl N)
    (smearedMoments_of_cubeMoments hN W D hD (s0 N) (s0_refl N) hpos
      (fun O _ => scaledSubtraction_zero N O) hcube)

#print axioms uniformBoundF_energy0

end Linear

/-! ## 4. Continuity in the test functions and OS1 on all of ℝ⁴ -/

section Continuity

variable {N : ℕ}

/-- **Sup-norm continuity of the energy-density Schwinger functions.** Two families with the same fields
of `D`, test functions bounded by `Mᵢ` in `[-R, R]⁴` and within `δ` of each other in sup norm, have
limits within `(1 + n c) ∑ₐ δ ∏_{i ≠ a} Mᵢ`, `c` the cube bound of order `2n`. The families are joined
through the hybrids that take the first `s` slots from `F'`; each step changes one slot by a test
function of sup norm at most `δ` (`contSF_update_add`, `abs_contSF_energy0_le`).

DERIVED: `0` is the excluded colour count and the lower end of `R`; `1` is the coefficient of the
replaced test function and `-1` of the subtracted one; `2` makes the power even. -/
theorem abs_contSF_energy0_sub_le (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hB : UniformBoundF hN (energy0 W D hD)) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F F' : ι → SField N) (hfield : ∀ i, (F' i).1 = (F i).1)
    (hG : ∀ i, (F i).1 ∈ D) {R c δ : ℝ} (hR : 0 ≤ R)
    (hc : ∀ i, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k (F i).1).1
      ^ (2 * Fintype.card ι)) ≤ c)
    (M : ι → ℝ) (hF : ∀ i, IsTest (F i).2.1 R (M i)) (hF' : ∀ i, IsTest (F' i).2.1 R (M i))
    (hclose : ∀ i y, |(F' i).2.1 y - (F i).2.1 y| ≤ δ) :
    |contSF hN (energy0 W D hD) F' - contSF hN (energy0 W D hD) F|
      ≤ (1 + Fintype.card ι * c) * ∑ a, δ * ∏ i ∈ Finset.univ \ {a}, M i := by
  let hyb : Finset ι → ι → SField N := fun s i => if i ∈ s then F' i else F i
  have hyb_field : ∀ s i, (hyb s i).1 = (F i).1 := by
    intro s i
    by_cases h : i ∈ s
    · simp only [hyb, if_pos h]; exact hfield i
    · simp only [hyb, if_neg h]
  have hyb_test : ∀ s i, IsTest (hyb s i).2.1 R (M i) := by
    intro s i
    by_cases h : i ∈ s
    · simp only [hyb, if_pos h]; exact hF' i
    · simp only [hyb, if_neg h]; exact hF i
  have step : ∀ s : Finset ι, |contSF hN (energy0 W D hD) (hyb s) - contSF hN (energy0 W D hD) F|
      ≤ (1 + Fintype.card ι * c) * ∑ a ∈ s, δ * ∏ i ∈ Finset.univ \ {a}, M i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : hyb ∅ = F := funext (fun i => by simp [hyb])
      rw [e, sub_self, abs_zero, Finset.sum_empty, mul_zero]
    | insert a s ha ih =>
      let d : TestFn := testAdd (F' a).2 (testSmul (-1) (F a).2)
      have hd : IsTest d.1 R δ := by
        refine ⟨hR, fun y => ?_, fun y hy j => ?_⟩
        · show |(F' a).2.1 y + -1 * (F a).2.1 y| ≤ δ
          have := hclose a y
          rwa [neg_one_mul, ← sub_eq_add_neg]
        · by_cases h1 : (F' a).2.1 y = 0
          · have h2 : (F a).2.1 y ≠ 0 := by
              intro h2
              exact hy (show (F' a).2.1 y + -1 * (F a).2.1 y = 0 by rw [h1, h2]; ring)
            exact (hF a).2.2 y h2 j
          · exact (hF' a).2.2 y h1 j
      have e1 : hyb (insert a s) = Function.update (hyb s) a ((F a).1, testAdd (F a).2 d) := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp only [hyb, if_pos (Finset.mem_insert_self i s)]
          refine Prod.ext (hfield i) (Subtype.ext (funext (fun y => ?_)))
          show (F' i).2.1 y = (F i).2.1 y + ((F' i).2.1 y + -1 * (F i).2.1 y)
          ring
        · rw [Function.update_of_ne hi]
          simp only [hyb, Finset.mem_insert, hi, false_or]
      have e2 : Function.update (hyb s) a ((F a).1, (F a).2) = hyb s := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp only [hyb, if_neg ha]
        · rw [Function.update_of_ne hi]
      have hadd := contSF_update_add hN (energy0 W D hD) hB (hyb s) a (F a).1 (F a).2 d
      have hfu : ∀ i, (Function.update (hyb s) a ((F a).1, d) i).1 = (F i).1 := by
        intro i
        by_cases hi : i = a
        · subst hi; rw [Function.update_self]
        · rw [Function.update_of_ne hi]; exact hyb_field s i
      have hbound := abs_contSF_energy0_le hN W hD hpos (Function.update (hyb s) a ((F a).1, d))
        (fun i => by rw [hfu i]; exact hG i) (R := R) (c := c)
        (fun i => by rw [hfu i]; exact hc i) (Function.update M a δ)
        (fun i => by
          by_cases hi : i = a
          · subst hi; rw [Function.update_self, Function.update_self]; exact hd
          · rw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hyb_test s i)
      rw [Finset.prod_update_of_mem (Finset.mem_univ a)] at hbound
      rw [e1, hadd, e2, Finset.sum_insert ha, mul_add]
      have htri : |contSF hN (energy0 W D hD) (hyb s)
            + contSF hN (energy0 W D hD) (Function.update (hyb s) a ((F a).1, d))
            - contSF hN (energy0 W D hD) F|
          ≤ |contSF hN (energy0 W D hD) (Function.update (hyb s) a ((F a).1, d))|
            + |contSF hN (energy0 W D hD) (hyb s) - contSF hN (energy0 W D hD) F| := by
        have := abs_add_le (contSF hN (energy0 W D hD) (Function.update (hyb s) a ((F a).1, d)))
          (contSF hN (energy0 W D hD) (hyb s) - contSF hN (energy0 W D hD) F)
        calc _ = |contSF hN (energy0 W D hD) (Function.update (hyb s) a ((F a).1, d))
              + (contSF hN (energy0 W D hD) (hyb s) - contSF hN (energy0 W D hD) F)| := by
              congr 1; ring
          _ ≤ _ := this
      exact htri.trans (add_le_add hbound ih)
  have e : hyb Finset.univ = F' := funext (fun i => by simp [hyb])
  have := step Finset.univ
  rwa [e] at this

#print axioms abs_contSF_energy0_sub_le

/-- **OS1 on all of ℝ⁴ for the energy density, given (E).** For a family of fields of `D` with
uniformly continuous test functions, translating every test function by any `v ∈ ℝ⁴` leaves the limit
Schwinger function unchanged. No separation of supports is assumed. For `ε > 0` take a dyadic `w` near
`v` (`ContinuumHypercubic.exists_dyadic_of_eventually`): the two translates are within `δ` in sup
norm in one cube, so their limits are within `ε` (`abs_contSF_energy0_sub_le`), and the translate by
`w` has the limit of the family (`ContinuumFlow.contSF_translate`).

DERIVED: `0` is the excluded colour count and the sign of `ε`, `δ`; `1` bounds the distance of `w` to
`v`, keeping both translates in one cube, and makes `A + 1` positive; `2` makes the power even; `4` in
`Fin 4` is the spacetime dimension. -/
theorem contSF_energy0_translate_real (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {ι : Type}
    [Fintype ι] (F : ι → SField N) (hG : ∀ i, (F i).1 ∈ D)
    (hU : ∀ i, UniformContinuous (F i).2.1) (v : Fin 4 → ℝ) :
    contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate v))
      = contSF hN (energy0 W D hD) F := by
  classical
  have hN1 := one_le_of_ne_zero hN
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i + ∑ j, |v j| + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    have h1 : 0 ≤ ∑ i, R0 i := Finset.sum_nonneg (fun i _ => (hRM i).1)
    have h2 : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg (fun j _ => abs_nonneg (v j))
    rw [hRdef]; linarith
  have hbox : ∀ u : Fin 4 → ℝ, dist u v < 1 →
      ∀ i y, ((F i).2.translate u).1 y ≠ 0 → ∀ j, |y j| ≤ R := by
    intro u hu i y hy j
    have h1 : |y j - u j| ≤ R0 i := (hRM i).2.2 (y - u) hy j
    have h2 : dist (u j) (v j) < 1 := (dist_le_pi_dist u v j).trans_lt hu
    rw [Real.dist_eq] at h2
    have h3 : |u j| - |v j| ≤ |u j - v j| := abs_sub_abs_le_abs_sub (u j) (v j)
    have h4 : R0 i ≤ ∑ i, R0 i :=
      Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
    have h5 : |v j| ≤ ∑ j, |v j| :=
      Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j)) (Finset.mem_univ j)
    have h6 : |y j| ≤ |y j - u j| + |u j| := by
      have h7 := abs_add_le (y j - u j) (u j)
      rwa [sub_add_cancel] at h7
    rw [hRdef]
    linarith
  have hTu : ∀ u : Fin 4 → ℝ, dist u v < 1 → ∀ i, IsTest ((F i).2.translate u).1 R (M i) :=
    fun u hu i => ⟨hR0, fun y => (hRM i).2.1 _, fun y hy j => hbox u hu i y hy j⟩
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => hcube _ (hG i) R hR0 _
  choose C hC using hC
  have hc : ∀ i, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ ∑ i, |C i| := fun i =>
    (hC i).mono (fun k hk => hk.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))))
  have hc0 : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => (hRM i).M_nonneg)))
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  rw [Real.dist_eq]
  have hA1 : 0 < A + 1 := by linarith
  have hδ : 0 < ε / (A + 1) := div_pos hε hA1
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      ∀ a b : Fin 4 → ℝ, dist a b < η → dist ((F i).2.1 a) ((F i).2.1 b) < ε / (A + 1) := by
    intro i
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp (hU i) _ hδ
    exact ⟨η, hη, fun a b hab => h hab⟩
  choose η hη0 hηf using hη
  have hev1 : ∀ i, ∀ᶠ w in 𝓝 v, dist w v < η i := fun i =>
    Metric.eventually_nhds_iff.mpr ⟨η i, hη0 i, by intro w hw; exact hw⟩
  have hev2 : ∀ᶠ w in 𝓝 v, dist w v < 1 :=
    Metric.eventually_nhds_iff.mpr ⟨1, one_pos, by intro w hw; exact hw⟩
  have hev : ∀ᶠ w in 𝓝 v, (∀ i, dist w v < η i) ∧ dist w v < 1 :=
    (Filter.eventually_all.mpr hev1).and hev2
  obtain ⟨m, n, hw, hw1⟩ := ContinuumHypercubic.exists_dyadic_of_eventually hN1 hev
  have hdiff := abs_contSF_energy0_sub_le hN W hD hpos hB
    (fun i => ((F i).1, (F i).2.translate v))
    (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n))) (fun i => rfl) hG hR0 hc M
    (hTu v (by rw [dist_self]; exact one_pos)) (hTu _ hw1)
    (fun i y => by
      have h := hηf i (y - site (dySpacing N m) n) (y - v) (by rw [dist_sub_left]; exact hw i)
      rw [Real.dist_eq] at h
      exact h.le)
  rw [contSF_translate hN (energy0 W D hD) F m n] at hdiff
  have hsum : (1 + Fintype.card ι * ∑ i, |C i|)
      * ∑ a, ε / (A + 1) * ∏ i ∈ Finset.univ \ {a}, M i = ε / (A + 1) * A := by
    rw [hAdef, ← Finset.mul_sum]
    ring
  rw [hsum] at hdiff
  rw [abs_sub_comm] at hdiff
  calc |contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate v))
        - contSF hN (energy0 W D hD) F| ≤ ε / (A + 1) * A := hdiff
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hA1]
      nlinarith

#print axioms contSF_energy0_translate_real

end Continuity

/-! ## 5. The package and what remains -/

section Package

variable {N : ℕ}

/-- **The Osterwalder–Schrader structure of the observer's energy-density theory, given (E).** On a
reflection-closed class `D` of non-negative fields with bounded cube moments:

1. (OS0, sup norm on each cube) for every tuple of fields and cube, one constant bounds every limit
   Schwinger function by the product of the sup norms of its test functions;
2. (linearity) the limit is additive in each test function;
3. (OS1, translations) it is unchanged when every uniformly continuous test function is translated by
   any `v ∈ ℝ⁴`;
4. (OS1, reflections) it is unchanged when every field and test function is reflected in an axis;
5. (OS3) it is unchanged under a permutation of the family;
6. (OS2) its reflected Gram sums on margin monomials are non-negative for a flow keeping the
   positive half-space beyond `r`.

DERIVED: `0` is the excluded colour count, the lower end of `R`, `K` and the Gram sum; `4` in `Fin 4`
is the spacetime dimension. -/
theorem observer_os (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) :
    (∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)), (∀ i, O i ∈ D) →
      ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ, 0 < K ∧ ∀ G : ι → SField N, (∀ i, (G i).1 = O i) →
        ∀ M : ι → ℝ, (∀ i, IsTest (G i).2.1 R (M i)) →
          |contSF hN (energy0 W D hD) G| ≤ K * ∏ i, M i)
    ∧ (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : ι → SField N) (j : ι)
        (O : LField (MassGap.SUN.SU N)) (f g : TestFn),
        contSF hN (energy0 W D hD) (Function.update B j (O, testAdd f g))
          = contSF hN (energy0 W D hD) (Function.update B j (O, f))
            + contSF hN (energy0 W D hD) (Function.update B j (O, g)))
    ∧ (∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ D) →
        (∀ i, UniformContinuous (F i).2.1) → ∀ v : Fin 4 → ℝ,
          contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate v))
            = contSF hN (energy0 W D hD) F)
    ∧ (∀ (τ : Fin 4) (ι : Type) [Fintype ι] (F : ι → SField N),
        contSF hN (energy0 W D hD) (fun i => SField.refl τ (F i)) = contSF hN (energy0 W D hD) F)
    ∧ (∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (F : ι → SField N),
        contSF hN (energy0 W D hD) (F ∘ e) = contSF hN (energy0 W D hD) F)
    ∧ (∀ (τ : Fin 4) (r : ℝ), (energy0 W D hD).PosPreserving τ r →
        ∀ (s : Finset (MarginMono N τ r)) (c : MarginMono N τ r → ℝ),
          0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernF hN (energy0 W D hD) τ P.1 Q.1) := by
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  refine ⟨fun ι _ O hO R hR => exists_os0_const hN W hD hpos hcube O hO hR,
    fun ι _ _ B j O f g => contSF_update_add hN _ hB B j O f g,
    fun ι _ F hG hU v => contSF_energy0_translate_real hN W hD hpos hcube F hG hU v,
    fun τ ι _ F => contSF_reflect hN _ τ F,
    fun ι ι' _ _ e F => contSF_comp_equiv hN _ e F,
    fun τ r hpp s c => contSF_gram_nonneg hN _ hB τ hpp s c⟩

#print axioms observer_os

/-- **The growth condition uniform in the cube (stated).** One `α, γ, β` bound every Schwinger
function of the field `O` by `α γⁿ (n!)^β ∏ᵢ Mᵢ (2Rᵢ + 3)⁴` for `|gᵢ| ≤ Mᵢ` supported in
`[-Rᵢ, Rᵢ]⁴`. `exists_os0_const` and `os0_factorial` give a constant per cube; this asks the constant
to grow with the cube no faster than its volume per factor, the bound that extends the Schwinger
functions to Schwartz test functions.

DERIVED: `2`, `3`, `4` are `ContinuumField.norm_smear_le`'s volume factor. -/
def TemperedGrowth (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ α γ β : ℝ, ∀ (n : ℕ) (f : Fin n → TestFn) (R M : Fin n → ℝ),
    (∀ i, IsTest (f i).1 (R i) (M i)) →
      |contSF hN Φ (fun i => (O, f i))|
        ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * ∏ i, M i * (2 * R i + 3) ^ 4

end Package

end MassGap.ObserverOS
