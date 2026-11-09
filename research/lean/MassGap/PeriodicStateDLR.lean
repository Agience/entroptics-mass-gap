import Mathlib
import MassGap.PeriodicState
import MassGap.HeatBath
import MassGap.WilsonDLR
import MassGap.ContinuumSchwinger

noncomputable section

/-!
# MassGap.PeriodicStateDLR — the periodic infinite-volume state satisfies the DLR equations

`PeriodicState.periodicState hN β` is the limit, along `PeriodicState.periodicUltra hN β`, of the
periodic Wilson Gibbs states `torusState hN (2k + 1) β` read on `ℤ⁴` observables. This module proves
that it is a DLR state of the Wilson specification `GibbsSpec.spec` with boundary condition, at every
`N ≠ 0`, every real `β` and every finite volume `Λ`:

* `periodicState_dlr`: `periodicState hN β (wspec hN β Λ f) = periodicState hN β f` for every
  continuous `f`, where `wspec hN β Λ f` is the kernel `ω ↦ spec wilsonDensity β Λ probHaar f ω` as a
  continuous observable (`WilsonDLR.specCM`). This is the functional form.

## The mechanism

1. **Integrating out a block of torus links** (`integral_eq_integral_extend`). For an injection
   `e : ι → Lk` of finite types, `(W, v) ↦ Function.extend e v W` carries `(Π μ) ⊗ (Π μ)` to `Π μ`
   (`measurePreserving_extend`, by `Measure.pi_eq` on boxes).
2. **The block heat bath** (`kern`, `integral_kern_mul`). If the torus weight factors as `a · r` with
   `r` not reading the block, then `∫ kern F · a r = ∫ F · a r`, where `kern F` averages `F` over the
   block against `a`. No positivity of `r` and no Wilson structure enter.
3. **The Wilson factorisation on the torus** (`boltz_eq`). For `a` the boundary weight
   `exp(-β · actionOn (boundaryPlaqs Λ))` read through `pullback M`, and `r` the weight of the torus
   plaquettes outside `plaqMod M '' boundaryPlaqs Λ`, the torus Boltzmann weight is `a · r` once
   `plaqMod M` is injective on `boundaryPlaqs Λ` (`InfiniteLattice.wilsonHol_periodic`). Every torus
   plaquette reading a link of `linkMod M '' Λ` lies in that image (`mem_image_of_reads`), so `r` does
   not read the block.
4. **The kernel is `spec`** (`kern_eq_spec`). Once `linkMod M` is injective on `S ∪ Λ ∪ bdLinks Λ`,
   with `f` local on `S`, `pullback M (extend e v W)` and `splice Λ v (pullback M W)` agree on that set,
   so `kern` at the torus reading of `f` is `spec Λ f ∘ pullback M`.
5. **Torus DLR** (`torusState_dlr`): steps 2–4 give `torusState hN M β (wspec Λ f) = torusState hN M β f`
   for `f` local on `S`, at every extent with the two injectivities, which hold for all large `M`
   (`exists_inj_bound`).
6. **The limit** (`periodicState_dlr_local`): along `periodicUltra`, finer than `atTop`, both sides
   converge (`tendsto_periodicState`) and agree eventually.
7. **All continuous observables** (`periodicState_dlr`): `specComp` is the state `f ↦ ν (wspec Λ f)`;
   it agrees with `ν` on the local observables, hence everywhere
   (`DLRLimit.State.eq_of_eqOn_localObs`, Stone–Weierstrass).

## Controls

`wspec_one` (the constant `1`), `wspec_empty` (`Λ = ∅`: the kernel is evaluation at the boundary
condition, so the equation is trivial), `periodicState_dlr_nested` (two nested volumes, read against
`GibbsSpec.wilson_dlr_consistent` through `WilsonDLR.dlr_general`).

## Box conditioning

`ContinuumSchwinger.stateK hN k` is `periodicState hN (dyBeta k)` by definition, and `stateK_dlr`
restates the functional form there. With it, any expectation `stateK hN k F` is `stateK hN k` of the
box kernel `wspec Λ F`, i.e. `F` conditioned on the configuration outside a box `Λ`, and
`periodicState_ge_of_kernel_ge` passes to the state a lower bound on the kernel that holds at every
boundary condition. No such bound on a particular kernel is proved here, and the box kernel of a
reflected pairing is not pointwise positive in general.
-/

namespace MassGap.PeriodicStateDLR

open MeasureTheory
open MassGap.GibbsSpec
open MassGap.LatticeGauge
open MassGap.WilsonLattice (wilsonSystem wilsonHol)
open MassGap.WilsonAction (wilsonDensity continuous_wilsonDensity measurable_wilsonDensity
  wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.PeriodicState (torusObs torusState periodicState periodicUltra tendsto_periodicState)
open MassGap.InfiniteLattice (siteMod linkMod plaqMod pullback finMod)

variable {N : ℕ}

/-! ## 1. Reduction modulo the extent is injective on a bounded set -/

section Inj

/-- Two integers of absolute value at most `B` with the same residue modulo `M + 1 > 2B` are equal. -/
theorem finMod_inj_of_abs_le {M B : ℕ} (hB : 2 * B < M + 1) {x y : ℤ}
    (hx : |x| ≤ B) (hy : |y| ≤ B) (h : finMod M x = finMod M y) : x = y := by
  have hpos : (0 : ℤ) < (M : ℤ) + 1 := by positivity
  have h0x : (0 : ℤ) ≤ x % ((M : ℤ) + 1) := Int.emod_nonneg x hpos.ne'
  have h0y : (0 : ℤ) ≤ y % ((M : ℤ) + 1) := Int.emod_nonneg y hpos.ne'
  have hv : (x % ((M : ℤ) + 1)).toNat = (y % ((M : ℤ) + 1)).toNat := congrArg Fin.val h
  have hmod : x % ((M : ℤ) + 1) = y % ((M : ℤ) + 1) := by
    calc x % ((M : ℤ) + 1) = ((x % ((M : ℤ) + 1)).toNat : ℤ) := (Int.toNat_of_nonneg h0x).symm
      _ = ((y % ((M : ℤ) + 1)).toNat : ℤ) := by rw [hv]
      _ = y % ((M : ℤ) + 1) := Int.toNat_of_nonneg h0y
  obtain ⟨c, hc⟩ := Int.ModEq.dvd (show Int.ModEq ((M : ℤ) + 1) x y from hmod)
  have hxa := abs_le.mp hx
  have hya := abs_le.mp hy
  have hB' : 2 * (B : ℤ) < (M : ℤ) + 1 := by exact_mod_cast hB
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · have hc1 : (0 : ℤ) ≤ -1 - c := by omega
    have := mul_nonneg hpos.le hc1
    nlinarith
  · rw [hc0, mul_zero] at hc
    linarith
  · have hc1 : (0 : ℤ) ≤ c - 1 := by omega
    have := mul_nonneg hpos.le hc1
    nlinarith

#print axioms finMod_inj_of_abs_le

/-- The largest absolute value of a coordinate of a site of `X`. -/
def siteBound (X : Finset ISite) : ℕ :=
  X.sup (fun x => Finset.univ.sup (fun i : Fin 4 => (x i).natAbs))

theorem abs_le_siteBound {X : Finset ISite} {x : ISite} (hx : x ∈ X) (i : Fin 4) :
    |x i| ≤ (siteBound X : ℤ) := by
  have h1 : (x i).natAbs ≤ Finset.univ.sup (fun i : Fin 4 => (x i).natAbs) :=
    Finset.le_sup (f := fun i : Fin 4 => (x i).natAbs) (Finset.mem_univ i)
  have h2 : Finset.univ.sup (fun i : Fin 4 => (x i).natAbs) ≤ siteBound X :=
    Finset.le_sup (f := fun x : ISite => Finset.univ.sup (fun i : Fin 4 => (x i).natAbs)) hx
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans h2

#print axioms abs_le_siteBound

theorem siteMod_injOn {X : Finset ISite} {M : ℕ} (hM : 2 * siteBound X < M + 1) :
    Set.InjOn (siteMod M) (X : Set ISite) := by
  intro x hx y hy h
  funext i
  exact finMod_inj_of_abs_le hM (abs_le_siteBound (Finset.mem_coe.mp hx) i)
    (abs_le_siteBound (Finset.mem_coe.mp hy) i) (congrFun h i)

#print axioms siteMod_injOn

/-- For all large extents, `linkMod M` is injective on a finite link set `T` and `plaqMod M` on a
finite plaquette set `Q`. -/
theorem exists_inj_bound (T : Finset ILink) (Q : Finset IPlaq) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Set.InjOn (linkMod M) (T : Set ILink) ∧ Set.InjOn (plaqMod M) (Q : Set IPlaq) := by
  refine ⟨2 * siteBound (T.image Prod.snd) + 2 * siteBound (Q.image Prod.snd), fun M hM => ⟨?_, ?_⟩⟩
  · have hb : 2 * siteBound (T.image Prod.snd) < M + 1 := by omega
    intro l hl l' hl' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (siteMod_injOn hb
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hl)))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hl'))) h2)
  · have hb : 2 * siteBound (Q.image Prod.snd) < M + 1 := by omega
    intro q hq q' hq' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (siteMod_injOn hb
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hq)))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hq'))) h2)

#print axioms exists_inj_bound

end Inj

/-! ## 2. Integrating out a block of coordinates -/

section Extend

variable {Lk ι Ω : Type} [Fintype Lk] [Fintype ι]

omit [Fintype Lk] in
theorem extend_extend {e : ι → Lk} (he : Function.Injective e) (W : Lk → Ω) (v v' : ι → Ω) :
    Function.extend e v' (Function.extend e v W) = Function.extend e v' W := by
  funext k
  by_cases hk : ∃ a, e a = k
  · obtain ⟨a, rfl⟩ := hk
    rw [he.extend_apply, he.extend_apply]
  · rw [Function.extend_apply' v' (Function.extend e v W) k hk, Function.extend_apply' v W k hk,
      Function.extend_apply' v' W k hk]

#print axioms extend_extend

variable [MeasurableSpace Ω]

omit [Fintype Lk] in
theorem measurable_extend_pair (e : ι → Lk) :
    Measurable (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1) := by
  classical
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h : ∃ a, e a = k
  · have hfun : (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1 k)
        = fun p => p.2 (Classical.choose h) := by
      funext p
      rw [Function.extend_def, dif_pos h]
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_snd
  · have hfun : (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1 k) = fun p => p.1 k := by
      funext p
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_fst

#print axioms measurable_extend_pair

/-- **Overwriting a block of coordinates preserves the product measure.** For a probability measure
`μ` and an injection `e : ι → Lk`, `(W, v) ↦ Function.extend e v W` carries `(Π μ) ⊗ (Π μ)` to
`Π μ`: the preimage of a box is a box with `univ` on the range of `e`, times the box `s ∘ e`. -/
theorem measurePreserving_extend (μ : Measure Ω) [IsProbabilityMeasure μ] {e : ι → Lk}
    (he : Function.Injective e) :
    MeasurePreserving (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1)
      ((Measure.pi fun _ : Lk => μ).prod (Measure.pi fun _ : ι => μ))
      (Measure.pi fun _ : Lk => μ) := by
  classical
  refine ⟨measurable_extend_pair e, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  let t : Lk → Set Ω := fun k => if ∃ a, e a = k then Set.univ else s k
  have hpre : (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi t) ×ˢ (Set.univ.pi fun i => s (e i)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · by_cases hk : ∃ a, e a = k
        · simp only [t, if_pos hk]
          exact Set.mem_univ _
        · simp only [t, if_neg hk]
          have hk' := h k
          rwa [Function.extend_apply' _ _ _ hk] at hk'
      · have hi := h (e i)
        rwa [he.extend_apply] at hi
    · rintro ⟨h1, h2⟩ k
      by_cases hk : ∃ a, e a = k
      · obtain ⟨a, rfl⟩ := hk
        rw [he.extend_apply]
        exact h2 a
      · rw [Function.extend_apply' _ _ _ hk]
        have hk' := h1 k
        simp only [t, if_neg hk] at hk'
        exact hk'
  rw [Measure.map_apply (measurable_extend_pair e) (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  have h1 : ∏ k, μ (t k) = ∏ k, (if ∃ a, e a = k then 1 else μ (s k)) := by
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases hk : ∃ a, e a = k
    · simp only [t, if_pos hk, measure_univ]
    · simp only [t, if_neg hk]
  have h2 : ∏ i, μ (s (e i)) = ∏ k, (if ∃ a, e a = k then μ (s k) else 1) :=
    Fintype.prod_of_injective e he _ _
      (fun k hk => if_neg (fun h => hk (Set.mem_range.mpr h)))
      (fun i => (if_pos ⟨i, rfl⟩).symm)
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  by_cases hk : ∃ a, e a = k
  · rw [if_pos hk, if_pos hk, one_mul]
  · rw [if_neg hk, if_neg hk, mul_one]

#print axioms measurePreserving_extend

/-- **Integrating out a block.** `∫ F d(Π μ) = ∫ W, ∫ v, F (extend e v W) d(Π μ) d(Π μ)` for a bounded
measurable `F` (`measurePreserving_extend`, Fubini). -/
theorem integral_eq_integral_extend (μ : Measure Ω) [IsProbabilityMeasure μ] {e : ι → Lk}
    (he : Function.Injective e) (F : (Lk → Ω) → ℝ) (hF : Measurable F) {C : ℝ}
    (hC : ∀ W, |F W| ≤ C) :
    ∫ W, F W ∂(Measure.pi fun _ : Lk => μ)
      = ∫ W, ∫ v, F (Function.extend e v W) ∂(Measure.pi fun _ : ι => μ)
          ∂(Measure.pi fun _ : Lk => μ) := by
  have hmp := measurePreserving_extend μ he
  have hint : Integrable (fun p : (Lk → Ω) × (ι → Ω) => F (Function.extend e p.2 p.1))
      ((Measure.pi fun _ : Lk => μ).prod (Measure.pi fun _ : ι => μ)) :=
    MassGap.HeatBath.integrable_of_abs_le _ (hF.comp (measurable_extend_pair e)) (fun p => hC _)
  calc ∫ W, F W ∂(Measure.pi fun _ : Lk => μ)
      = ∫ W, F W ∂(Measure.map (fun p : (Lk → Ω) × (ι → Ω) => Function.extend e p.2 p.1)
          ((Measure.pi fun _ : Lk => μ).prod (Measure.pi fun _ : ι => μ))) := by rw [hmp.map_eq]
    _ = ∫ p, F (Function.extend e p.2 p.1)
          ∂((Measure.pi fun _ : Lk => μ).prod (Measure.pi fun _ : ι => μ)) :=
        integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable
    _ = _ := integral_prod _ hint

#print axioms integral_eq_integral_extend

end Extend

/-! ## 3. The block heat bath of a factorised weight -/

section Kernel

variable {Lk ι : Type} [Fintype Lk] [Fintype ι]

omit [Fintype Lk] in
theorem continuous_extend_left (e : ι → Lk) (W : Lk → SU N) :
    Continuous (fun v : ι → SU N => Function.extend e v W) := by
  classical
  refine continuous_pi (fun k => ?_)
  by_cases h : ∃ a, e a = k
  · have hfun : (fun v : ι → SU N => Function.extend e v W k) = fun v => v (Classical.choose h) := by
      funext v
      rw [Function.extend_def, dif_pos h]
    rw [hfun]
    exact continuous_apply _
  · have hfun : (fun v : ι → SU N => Function.extend e v W k) = fun _ => W k := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact continuous_const

#print axioms continuous_extend_left

/-- **The block heat bath**: the average of `F` over the coordinates in the range of `e`, against the
weight `a`, the other coordinates held at `W`. -/
def kern (e : ι → Lk) (a F : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  (∫ v, F (Function.extend e v W) * a (Function.extend e v W)
      ∂(Measure.pi fun _ : ι => probHaar (SU N)))
    / ∫ v, a (Function.extend e v W) ∂(Measure.pi fun _ : ι => probHaar (SU N))

omit [Fintype Lk] in
theorem kern_extend {e : ι → Lk} (he : Function.Injective e) (a F : (Lk → SU N) → ℝ)
    (W : Lk → SU N) (v : ι → SU N) : kern e a F (Function.extend e v W) = kern e a F W := by
  simp only [kern, extend_extend he]

#print axioms kern_extend

omit [Fintype Lk] in
theorem kern_part_pos (e : ι → Lk) {a : (Lk → SU N) → ℝ} (ha : Continuous a)
    (hapos : ∀ W, 0 < a W) (W : Lk → SU N) :
    0 < ∫ v, a (Function.extend e v W) ∂(Measure.pi fun _ : ι => probHaar (SU N)) := by
  have hc : Continuous (fun v : ι → SU N => a (Function.extend e v W)) :=
    ha.comp (continuous_extend_left e W)
  obtain ⟨C, hC⟩ := MassGap.HeatBath.exists_abs_le hc
  have hint : Integrable (fun v : ι → SU N => a (Function.extend e v W))
      (Measure.pi fun _ : ι => probHaar (SU N)) :=
    MassGap.HeatBath.integrable_of_abs_le _ hc.measurable hC
  rw [integral_pos_iff_support_of_nonneg (fun v => (hapos _).le) hint]
  have hsupp : Function.support (fun v : ι → SU N => a (Function.extend e v W)) = Set.univ :=
    Set.eq_univ_of_forall (fun v => Function.mem_support.mpr (hapos _).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms kern_part_pos

/-- **The block DLR identity.** If the weight factors as `a · r` with `a > 0` and `r` not reading the
coordinates in the range of `e`, then `∫ kern F · a r = ∫ F · a r` against the product Haar
measure. -/
theorem integral_kern_mul {e : ι → Lk} (he : Function.Injective e) {F a r : (Lk → SU N) → ℝ}
    (hF : Continuous F) (ha : Continuous a) (hr : Continuous r) (hapos : ∀ W, 0 < a W)
    (hrinv : ∀ W v, r (Function.extend e v W) = r W) (hK : Continuous (kern e a F)) :
    ∫ W, kern e a F W * (a W * r W) ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, F W * (a W * r W) ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hc1 : Continuous (fun W => kern e a F W * (a W * r W)) := hK.mul (ha.mul hr)
  have hc2 : Continuous (fun W => F W * (a W * r W)) := hF.mul (ha.mul hr)
  obtain ⟨C1, hC1⟩ := MassGap.HeatBath.exists_abs_le hc1
  obtain ⟨C2, hC2⟩ := MassGap.HeatBath.exists_abs_le hc2
  rw [integral_eq_integral_extend (probHaar (SU N)) he _ hc1.measurable hC1,
    integral_eq_integral_extend (probHaar (SU N)) he _ hc2.measurable hC2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show ∫ v, kern e a F (Function.extend e v W)
        * (a (Function.extend e v W) * r (Function.extend e v W))
        ∂(Measure.pi fun _ : ι => probHaar (SU N))
      = ∫ v, F (Function.extend e v W) * (a (Function.extend e v W) * r (Function.extend e v W))
        ∂(Measure.pi fun _ : ι => probHaar (SU N))
  simp only [kern_extend he, hrinv]
  have hL : ∫ v, kern e a F W * (a (Function.extend e v W) * r W)
        ∂(Measure.pi fun _ : ι => probHaar (SU N))
      = kern e a F W * r W
        * ∫ v, a (Function.extend e v W) ∂(Measure.pi fun _ : ι => probHaar (SU N)) := by
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  have hR : ∫ v, F (Function.extend e v W) * (a (Function.extend e v W) * r W)
        ∂(Measure.pi fun _ : ι => probHaar (SU N))
      = r W * ∫ v, F (Function.extend e v W) * a (Function.extend e v W)
        ∂(Measure.pi fun _ : ι => probHaar (SU N)) := by
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [hL, hR]
  have hZ := kern_part_pos e ha hapos W
  unfold kern
  rw [mul_right_comm, div_mul_cancel₀ _ hZ.ne']
  ring

#print axioms integral_kern_mul

omit [Fintype Lk] [Fintype ι] in
/-- A holonomy whose boundary word visits no coordinate in the range of `e` does not read them. -/
theorem wilsonHol_extend_of_not_mem {Pq : Type} (bd : Pq → List (Lk × Bool)) (p : Pq)
    {e : ι → Lk} (h : ∀ lo ∈ bd p, ¬∃ a, e a = lo.1) (W : Lk → SU N) (v : ι → SU N) :
    wilsonHol bd p (Function.extend e v W) = wilsonHol bd p W := by
  unfold wilsonHol
  congr 1
  apply List.map_congr_left
  intro lo hlo
  simp only [Function.extend_apply' _ _ _ (h lo hlo)]

#print axioms wilsonHol_extend_of_not_mem

end Kernel

/-! ## 4. The Wilson weight on the torus, factorised at a finite volume of `ℤ⁴` -/

section Torus

/-- `ishift` undoes `iunshift`. -/
theorem ishift_iunshift (μ : Fin 4) (x : ISite) : ishift μ (iunshift μ x) = x := by
  funext j
  by_cases h : j = μ
  · subst h
    simp [ishift, iunshift]
  · simp [ishift, iunshift, Function.update_of_ne h]

#print axioms ishift_iunshift

/-- The periodic shift is injective. -/
theorem shift_injective {M : ℕ} (μ : Fin 4) {x y : WilsonHypercubic.Site 4 (M + 1)}
    (h : WilsonHypercubic.shift μ x = WilsonHypercubic.shift μ y) : x = y := by
  funext j
  have hj := congrFun h j
  by_cases hjμ : j = μ
  · subst hjμ
    simp only [WilsonHypercubic.shift, Function.update_self] at hj
    exact add_right_cancel hj
  · simp only [WilsonHypercubic.shift, Function.update_of_ne hjμ] at hj
    exact hj

#print axioms shift_injective

/-- `siteMod M (iunshift μ y) = x` whenever `siteMod M y = shift μ x`. -/
theorem siteMod_iunshift {M : ℕ} (μ : Fin 4) {y : ISite} {x : WilsonHypercubic.Site 4 (M + 1)}
    (h : siteMod M y = WilsonHypercubic.shift μ x) : siteMod M (iunshift μ y) = x := by
  apply shift_injective μ
  rw [← MassGap.InfiniteLattice.siteMod_ishift]
  have hy : MassGap.InfiniteLattice.ishift μ (iunshift μ y) = y := ishift_iunshift μ y
  rw [hy, h]

#print axioms siteMod_iunshift

/-- The finite volume's links, placed on the torus. -/
def eΛ (M : ℕ) (Λ : Finset ILink) : ↥Λ → WilsonHypercubic.Link 4 (M + 1) :=
  fun l => linkMod M l.1

theorem eΛ_injective {M : ℕ} {Λ T : Finset ILink} (hΛT : Λ ⊆ T)
    (hinj : Set.InjOn (linkMod M) (T : Set ILink)) : Function.Injective (eΛ M Λ) :=
  fun a b h => Subtype.ext (hinj (Finset.mem_coe.mpr (hΛT a.2)) (Finset.mem_coe.mpr (hΛT b.2)) h)

#print axioms eΛ_injective

/-- The boundary weight of `Λ`, read through the pullback: `exp(-β · actionOn (boundaryPlaqs Λ))`. -/
def aΛ (β : ℝ) (M : ℕ) (Λ : Finset ILink) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) : ℝ :=
  Real.exp (-β * actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) (pullback M W))

/-- The torus plaquettes that are reductions of plaquettes of `boundaryPlaqs Λ`. -/
def PΛ (M : ℕ) (Λ : Finset ILink) : Finset (WilsonHypercubic.Plaq 4 (M + 1)) :=
  (boundaryPlaqs Λ).image (plaqMod M)

/-- The weight of the other torus plaquettes. -/
def rΛ (β : ℝ) (M : ℕ) (Λ : Finset ILink) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) : ℝ :=
  Real.exp (-β * ∑ p ∈ Finset.univ \ PΛ M Λ,
    wilsonDensity (wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) p W))

theorem continuous_aΛ (β : ℝ) (M : ℕ) (Λ : Finset ILink) : Continuous (aΛ (N := N) β M Λ) :=
  Real.continuous_exp.comp (continuous_const.mul
    ((MassGap.WilsonDLR.continuous_actionOn continuous_wilsonDensity (boundaryPlaqs Λ)).comp
      (MassGap.InfiniteLattice.continuous_pullback (m := M))))

#print axioms continuous_aΛ

theorem continuous_rΛ (β : ℝ) (M : ℕ) (Λ : Finset ILink) : Continuous (rΛ (N := N) β M Λ) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ (fun p _ =>
    continuous_wilsonDensity.comp
      (MassGap.PlaqVariance.continuous_wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) p))))

#print axioms continuous_rΛ

/-- The `ℤ⁴` holonomy of a pulled-back configuration is the torus holonomy of the reduced plaquette
(`InfiniteLattice.wilsonHol_periodic`). -/
theorem ihol_pullback (M : ℕ) (q : IPlaq) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    ihol q (pullback M W) = wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) (plaqMod M q) W :=
  MassGap.InfiniteLattice.wilsonHol_periodic q W

#print axioms ihol_pullback

/-- **The torus weight factorises at `Λ`**, once `plaqMod M` is injective on `boundaryPlaqs Λ`. -/
theorem boltz_eq (β : ℝ) {M : ℕ} {Λ : Finset ILink}
    (hP : Set.InjOn (plaqMod M) (boundaryPlaqs Λ : Set IPlaq))
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    (wilsonSystem (WilsonHypercubic.bd (d := 4) (n := M + 1)) (wilsonDensity (N := N))).boltz β W
      = aΛ β M Λ W * rΛ β M Λ W := by
  unfold aΛ rΛ
  show Real.exp (-β * ∑ p, wilsonDensity (wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) p W))
    = _
  rw [← Real.exp_add]
  congr 1
  have hsum := (Finset.sum_sdiff (Finset.subset_univ (PΛ M Λ))
    (f := fun p => wilsonDensity (wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) p W))).symm
  have hPsum : ∑ p ∈ PΛ M Λ,
        wilsonDensity (wilsonHol (WilsonHypercubic.bd (d := 4) (n := M + 1)) p W)
      = actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) (pullback M W) := by
    unfold PΛ
    rw [Finset.sum_image (fun x hx y hy h => hP (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)]
    unfold actionOn
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [ihol_pullback]
  rw [hsum, hPsum]
  ring

#print axioms boltz_eq

/-- **Every torus plaquette reading a link of the placed volume is a reduction of a plaquette of
`boundaryPlaqs Λ`.** No largeness of `M` is needed. -/
theorem mem_image_of_reads {M : ℕ} {Λ : Finset ILink} {l : ILink} (hl : l ∈ Λ)
    (p : WilsonHypercubic.Plaq 4 (M + 1))
    (h : linkMod M l ∈ (WilsonHypercubic.bd (d := 4) (n := M + 1) p).map Prod.fst) :
    p ∈ PΛ M Λ := by
  obtain ⟨⟨μ, ν⟩, x⟩ := p
  obtain ⟨l1, l2⟩ := l
  simp only [WilsonHypercubic.bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h
  unfold PΛ
  rw [Finset.mem_image]
  rcases h with h | h | h | h
  · have h1 : l1 = μ := congrArg Prod.fst h
    have h2 : siteMod M l2 = x := congrArg Prod.snd h
    subst h1
    refine ⟨((l1, ν), l2), mem_boundaryPlaqs.mpr ⟨(l1, l2), ?_, hl⟩, ?_⟩
    · rw [ilinks_eq]; simp
    · show ((l1, ν), siteMod M l2) = ((l1, ν), x)
      rw [h2]
  · have h1 : l1 = ν := congrArg Prod.fst h
    have h2 : siteMod M l2 = WilsonHypercubic.shift μ x := congrArg Prod.snd h
    subst h1
    refine ⟨((μ, l1), iunshift μ l2), mem_boundaryPlaqs.mpr ⟨(l1, l2), ?_, hl⟩, ?_⟩
    · rw [ilinks_eq]; simp [ishift_iunshift]
    · show ((μ, l1), siteMod M (iunshift μ l2)) = ((μ, l1), x)
      rw [siteMod_iunshift μ h2]
  · have h1 : l1 = μ := congrArg Prod.fst h
    have h2 : siteMod M l2 = WilsonHypercubic.shift ν x := congrArg Prod.snd h
    subst h1
    refine ⟨((l1, ν), iunshift ν l2), mem_boundaryPlaqs.mpr ⟨(l1, l2), ?_, hl⟩, ?_⟩
    · rw [ilinks_eq]; simp [ishift_iunshift]
    · show ((l1, ν), siteMod M (iunshift ν l2)) = ((l1, ν), x)
      rw [siteMod_iunshift ν h2]
  · have h1 : l1 = ν := congrArg Prod.fst h
    have h2 : siteMod M l2 = x := congrArg Prod.snd h
    subst h1
    refine ⟨((μ, l1), l2), mem_boundaryPlaqs.mpr ⟨(l1, l2), ?_, hl⟩, ?_⟩
    · rw [ilinks_eq]; simp
    · show ((μ, l1), siteMod M l2) = ((μ, l1), x)
      rw [h2]

#print axioms mem_image_of_reads

/-- The weight of the other plaquettes does not read the placed volume. -/
theorem rΛ_extend (β : ℝ) (M : ℕ) (Λ : Finset ILink) (W : WilsonHypercubic.Link 4 (M + 1) → SU N)
    (v : ↥Λ → SU N) : rΛ β M Λ (Function.extend (eΛ M Λ) v W) = rΛ β M Λ W := by
  unfold rΛ
  congr 2
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpP : p ∉ PΛ M Λ := (Finset.mem_sdiff.mp hp).2
  rw [wilsonHol_extend_of_not_mem _ p (fun lo hlo => ?_) W v]
  rintro ⟨a, ha⟩
  apply hpP
  refine mem_image_of_reads a.2 p ?_
  show linkMod M a.1 ∈ _
  rw [show linkMod M a.1 = lo.1 from ha]
  exact List.mem_map.mpr ⟨lo, hlo, rfl⟩

#print axioms rΛ_extend

/-- On `S ∪ Λ ∪ bdLinks Λ`, where `linkMod M` is injective, overwriting the placed volume on the torus
and pulling back is the splice. -/
theorem pullback_extend_eq_splice {M : ℕ} {Λ T : Finset ILink} (hΛT : Λ ⊆ T)
    (hinj : Set.InjOn (linkMod M) (T : Set ILink)) (v : ↥Λ → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) {l : ILink} (hl : l ∈ T) :
    pullback M (Function.extend (eΛ M Λ) v W) l = splice Λ v (pullback M W) l := by
  show Function.extend (eΛ M Λ) v W (linkMod M l) = _
  by_cases hlΛ : l ∈ Λ
  · rw [splice_mem hlΛ]
    exact (eΛ_injective hΛT hinj).extend_apply v W ⟨l, hlΛ⟩
  · rw [splice_not_mem hlΛ]
    have hne : ¬∃ a, eΛ M Λ a = linkMod M l := by
      rintro ⟨a, ha⟩
      have hal : a.1 = l :=
        hinj (Finset.mem_coe.mpr (hΛT a.2)) (Finset.mem_coe.mpr hl) ha
      exact hlΛ (hal ▸ a.2)
    rw [Function.extend_apply' _ _ _ hne]
    rfl

#print axioms pullback_extend_eq_splice

/-- The Wilson kernel `spec` at `Λ`, as a continuous observable (`WilsonDLR.specCM`). -/
def wspec (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    (f : C(IConf (SU N), ℝ)) : C(IConf (SU N), ℝ) :=
  MassGap.WilsonDLR.specCM continuous_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β (probHaar (SU N)) Λ f

theorem wspec_apply (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ))
    (ω : IConf (SU N)) :
    wspec hN β Λ f ω = spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (⇑f) ω := rfl

/-- **The block heat bath at the torus reading of a local `f` is `spec Λ f` read through the
pullback**, once `linkMod M` is injective on `S ∪ Λ ∪ bdLinks Λ`. -/
theorem kern_eq_spec (β : ℝ) {M : ℕ} {Λ S : Finset ILink} {f : C(IConf (SU N), ℝ)}
    (hf : MassGap.DLRLimit.IsLocalOnC S f)
    (hinj : Set.InjOn (linkMod M) ((S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ : Finset ILink) : Set ILink))
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    kern (eΛ M Λ) (aΛ β M Λ) (torusObs M f) W
      = spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (⇑f) (pullback M W) := by
  have hΛT : Λ ⊆ S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ :=
    fun l hl => Finset.mem_union_left _ (Finset.mem_union_right _ hl)
  have hT : ∀ (v : ↥Λ → SU N) (l : ILink), l ∈ S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ →
      pullback M (Function.extend (eΛ M Λ) v W) l = splice Λ v (pullback M W) l :=
    fun v l hl => pullback_extend_eq_splice hΛT hinj v W hl
  have hF : ∀ v : ↥Λ → SU N,
      torusObs M f (Function.extend (eΛ M Λ) v W) = f (splice Λ v (pullback M W)) := fun v =>
    hf _ _ (fun l hl => hT v l (Finset.mem_union_left _ (Finset.mem_union_left _ hl)))
  have ha : ∀ v : ↥Λ → SU N,
      aΛ β M Λ (Function.extend (eΛ M Λ) v W)
        = wt (wilsonDensity (N := N)) β Λ v (pullback M W) := by
    intro v
    unfold aΛ wt
    rw [actionOn_congr _ _ _ _ (fun q hq l hl =>
      hT v l (Finset.mem_union_right _ (MassGap.WilsonDLR.mem_bdLinks hq hl)))]
  unfold kern spec num part
  simp only [hF, ha]
  rfl

#print axioms kern_eq_spec

/-- **Torus DLR.** For `f` local on `S`, at every extent where `linkMod M` is injective on
`S ∪ Λ ∪ bdLinks Λ` and `plaqMod M` on `boundaryPlaqs Λ`, the periodic Wilson state reads the box
kernel of `f` as it reads `f`. -/
theorem torusState_dlr (hN : N ≠ 0) (M : ℕ) (β : ℝ) (Λ S : Finset ILink) (f : C(IConf (SU N), ℝ))
    (hf : MassGap.DLRLimit.IsLocalOnC S f)
    (hinj : Set.InjOn (linkMod M) ((S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ : Finset ILink) : Set ILink))
    (hP : Set.InjOn (plaqMod M) (boundaryPlaqs Λ : Set IPlaq)) :
    torusState hN M β (wspec hN β Λ f) = torusState hN M β f := by
  have hΛT : Λ ⊆ S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ :=
    fun l hl => Finset.mem_union_left _ (Finset.mem_union_right _ hl)
  have he := eΛ_injective hΛT hinj
  have hk : ∀ W, torusObs M (wspec hN β Λ f) W = kern (eΛ M Λ) (aΛ β M Λ) (torusObs M f) W :=
    fun W => (kern_eq_spec β hf hinj W).symm
  have hKc : Continuous (kern (eΛ M Λ) (aΛ β M Λ) (torusObs M f)) := by
    have hfun : kern (eΛ M Λ) (aΛ β M Λ) (torusObs M f) = torusObs M (wspec hN β Λ f) :=
      funext fun W => (hk W).symm
    rw [hfun]
    exact MassGap.HeatBath.continuous_torusObs M _
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M (wspec hN β Λ f))
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M f)
  unfold MassGap.ReflectPositive.EW System.expect System.corrNum
  congr 1
  simp only [hk, boltz_eq β hP]
  exact integral_kern_mul he (MassGap.HeatBath.continuous_torusObs M f) (continuous_aΛ β M Λ)
    (continuous_rΛ β M Λ) (fun W => Real.exp_pos _) (fun W v => rΛ_extend β M Λ W v) hKc

#print axioms torusState_dlr

end Torus

/-! ## 5. The limit -/

section Limit

/-- **DLR for `periodicState` at a local observable.** -/
theorem periodicState_dlr_local (hN : N ≠ 0) (β : ℝ) (Λ S : Finset ILink)
    (f : C(IConf (SU N), ℝ)) (hf : MassGap.DLRLimit.IsLocalOnC S f) :
    periodicState hN β (wspec hN β Λ f) = periodicState hN β f := by
  obtain ⟨M₀, hM₀⟩ := exists_inj_bound (S ∪ Λ ∪ MassGap.WilsonDLR.bdLinks Λ) (boundaryPlaqs Λ)
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  have hbig : ∀ᶠ k in Filter.atTop, M₀ ≤ 2 * k + 1 :=
    Filter.eventually_atTop.mpr ⟨M₀, fun k hk => by omega⟩
  have hev : (fun k : ℕ => torusState hN (2 * k + 1) β (wspec hN β Λ f))
      =ᶠ[((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ)]
        (fun k : ℕ => torusState hN (2 * k + 1) β f) := by
    filter_upwards [hbig.filter_mono (MassGap.PeriodicState.periodicUltra_le hN β)] with k hk
    obtain ⟨h1, h2⟩ := hM₀ (2 * k + 1) hk
    exact torusState_dlr hN (2 * k + 1) β Λ S f hf h1 h2
  exact tendsto_nhds_unique ((tendsto_periodicState hN β (wspec hN β Λ f)).congr' hev)
    (tendsto_periodicState hN β f)

#print axioms periodicState_dlr_local

/-- The kernel is additive on continuous observables (`WilsonDLR.spec_add`). -/
theorem wspec_add (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (f g : C(IConf (SU N), ℝ)) :
    wspec hN β Λ (f + g) = wspec hN β Λ f + wspec hN β Λ g := by
  ext ω
  obtain ⟨Cf, hCf⟩ := MassGap.WilsonDLR.bounded_of_continuous f.continuous
  obtain ⟨Cg, hCg⟩ := MassGap.WilsonDLR.bounded_of_continuous g.continuous
  show spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (fun U => f U + g U) ω
    = spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) f ω
      + spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) g ω
  exact MassGap.WilsonDLR.spec_add measurable_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β Λ _ f.continuous.measurable hCf g.continuous.measurable hCg ω

#print axioms wspec_add

/-- The kernel is homogeneous (`WilsonDLR.spec_smul`). -/
theorem wspec_smul (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (c : ℝ) (f : C(IConf (SU N), ℝ)) :
    wspec hN β Λ (c • f) = c • wspec hN β Λ f := by
  ext ω
  show spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (fun U => c * f U) ω
    = c * spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) f ω
  exact MassGap.WilsonDLR.spec_smul _ β Λ _ c _ ω

#print axioms wspec_smul

/-- **Control: the constant `1`.** The kernel fixes it (`GibbsSpec.spec_one`). -/
theorem wspec_one (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) :
    wspec hN β Λ (1 : C(IConf (SU N), ℝ)) = 1 := by
  ext ω
  show spec (wilsonDensity (N := N)) β Λ (probHaar (SU N)) (fun _ => (1 : ℝ)) ω = 1
  exact spec_one measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β Λ _ ω

#print axioms wspec_one

/-- The state `f ↦ ν (wspec Λ f)`: a state composed with the box kernel. -/
def specComp (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    (ν : MassGap.DLRLimit.State (IConf (SU N))) : MassGap.DLRLimit.State (IConf (SU N)) where
  toFun f := ν (wspec hN β Λ f)
  map_add' f g := by
    show ν (wspec hN β Λ (f + g)) = ν (wspec hN β Λ f) + ν (wspec hN β Λ g)
    rw [wspec_add, ν.map_add]
  map_smul' c f := by
    show ν (wspec hN β Λ (c • f)) = c * ν (wspec hN β Λ f)
    rw [wspec_smul, ν.map_smul]
  nonneg' f hf := ν.nonneg _ (fun ω =>
    MassGap.WilsonDLR.spec_nonneg measurable_wilsonDensity (wilsonDensity_nonneg hN)
      (wilsonDensity_le_two hN) β Λ _ (fun U => hf U) ω)
  one' := by
    show ν (wspec hN β Λ 1) = 1
    rw [wspec_one, ν.map_one]

/-- **The DLR equations for `periodicState`, functional form.** At every `N ≠ 0`, every real `β`,
every finite volume `Λ` and every continuous observable `f`:
`periodicState hN β (ω ↦ spec wilsonDensity β Λ probHaar f ω) = periodicState hN β f`. -/
theorem periodicState_dlr (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ)) :
    periodicState hN β (wspec hN β Λ f) = periodicState hN β f :=
  MassGap.DLRLimit.State.eq_of_eqOn_localObs (ν₁ := specComp hN β Λ (periodicState hN β))
    (ν₂ := periodicState hN β) (fun F hF => by
      obtain ⟨S, hS⟩ := MassGap.DLRLimit.mem_localObsAlg.mp hF
      exact periodicState_dlr_local hN β Λ S F hS) f

#print axioms periodicState_dlr

/-- `periodicState_dlr` in the form `DLRLimit.IsDLR` takes. -/
theorem periodicState_isDLR (hN : N ≠ 0) (β : ℝ) :
    MassGap.DLRLimit.IsDLR (wspec hN β) (periodicState hN β) :=
  fun Λ f => periodicState_dlr hN β Λ f

#print axioms periodicState_isDLR

/-- **Box conditioning passes a uniform lower bound to the state.** If the box kernel of `F` is at
least `c` at every boundary condition, then `periodicState hN β F ≥ c`. -/
theorem periodicState_ge_of_kernel_ge (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink)
    (F : C(IConf (SU N), ℝ)) {c : ℝ} (h : ∀ ω, c ≤ wspec hN β Λ F ω) :
    c ≤ periodicState hN β F := by
  rw [← periodicState_dlr hN β Λ F]
  have hmono := (periodicState hN β).mono (f := c • (1 : C(IConf (SU N), ℝ)))
    (g := wspec hN β Λ F) (fun x => by simpa using h x)
  rwa [(periodicState hN β).map_smul, (periodicState hN β).map_one, mul_one] at hmono

#print axioms periodicState_ge_of_kernel_ge

end Limit

/-! ## 6. Controls -/

section Controls

/-- **Control: `Λ = ∅`.** The kernel at the empty volume is evaluation at the boundary condition, so
the equation is `ν f = ν f`. -/
theorem wspec_empty (hN : N ≠ 0) (β : ℝ) (f : C(IConf (SU N), ℝ)) :
    wspec hN β ∅ f = f := by
  ext ω
  have hsplice : ∀ u : VConf (SU N) (∅ : Finset ILink), splice ∅ u ω = ω := by
    intro u
    funext l
    exact splice_not_mem (Finset.notMem_empty l)
  show num (wilsonDensity (N := N)) β ∅ (probHaar (SU N)) f ω
      / part (wilsonDensity (N := N)) β ∅ (probHaar (SU N)) ω = f ω
  unfold num
  simp only [hsplice]
  rw [integral_const_mul]
  exact mul_div_cancel_right₀ _ (wilson_part_pos hN β ∅ ω).ne'

#print axioms wspec_empty

/-- **Control: the constant observable.** `periodicState_dlr` at `f = 1` reads `1 = 1`. -/
theorem periodicState_dlr_one (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) :
    periodicState hN β (wspec hN β Λ 1) = 1 := by
  rw [periodicState_dlr, (periodicState hN β).map_one]

#print axioms periodicState_dlr_one

/-- **Control: consistency with `GibbsSpec.wilson_dlr_consistent`.** For `Λ ⊆ Λ'`, the kernel at `Λ'`
of the kernel at `Λ` is the kernel at `Λ'` (`WilsonDLR.dlr_general`, the unbounded form of
`wilson_dlr_consistent`), and `periodicState` reads all three the same. -/
theorem periodicState_dlr_nested (hN : N ≠ 0) (β : ℝ) {Λ Λ' : Finset ILink} (hsub : Λ ⊆ Λ')
    (f : C(IConf (SU N), ℝ)) :
    wspec hN β Λ' (wspec hN β Λ f) = wspec hN β Λ' f
      ∧ periodicState hN β (wspec hN β Λ' (wspec hN β Λ f)) = periodicState hN β f := by
  have hcons : wspec hN β Λ' (wspec hN β Λ f) = wspec hN β Λ' f := by
    ext ω
    obtain ⟨C, hC⟩ := MassGap.WilsonDLR.bounded_of_continuous f.continuous
    exact MassGap.WilsonDLR.dlr_general measurable_wilsonDensity (wilsonDensity_nonneg hN)
      (wilsonDensity_le_two hN) β (probHaar (SU N)) hsub f.continuous.measurable hC ω
  refine ⟨hcons, ?_⟩
  rw [hcons, periodicState_dlr]

#print axioms periodicState_dlr_nested

end Controls

/-! ## 7. The step-`k` states of the continuum family -/

section StateK

/-- **DLR for `stateK hN k`, functional form**: `stateK hN k` is `periodicState` at the coupling
`dyBeta k`, so `periodicState_dlr` applies at that coupling. -/
theorem stateK_dlr (hN : N ≠ 0) (k : ℕ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ)) :
    MassGap.ContinuumSchwinger.stateK hN k
        (wspec hN (MassGap.ContinuumSchwinger.dyBeta
          (MassGap.ContinuumSchwinger.one_le_of_ne_zero hN) k) Λ f)
      = MassGap.ContinuumSchwinger.stateK hN k f :=
  periodicState_dlr hN _ Λ f

#print axioms stateK_dlr

end StateK

end MassGap.PeriodicStateDLR
