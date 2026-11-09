import Mathlib
import MassGap.TwoSliceBridge
import MassGap.ExistencePosNonnull

/-!
# MassGap.RectTorusState — the rectangular Wilson torus state and the two-slice law at every step

`rectState hN L β` is the `SU(N)` Wilson Gibbs state of the periodic 4-torus with extents `L : Fin 4 → ℕ`
(`RectWilson.sysR L N`), read on `ℤ⁴` observables through the rectangular pullback `rpull L` that reduces
coordinate `k` modulo `L k`. With it, `FluxDuality.CapturesReadTorus` holds for a family of Wilson states:
`capR hN β n i = rectState hN (ext n (pathV i)) β`, the Wilson state of the corner torus of step `i`.
Declarations are in the namespace `MassGap.RectTorusState`.

## Proved

* **The state.** `rpull L` (`1` on every link when some extent is `0`), `rectObs L f = f ∘ rpull L`, and
  `rectState hN L β f = ⟨sysR L N⟩_β (rectObs L f)`: linear, positive and normalized, by the same
  `WilsonReal` lemmas as `PeriodicState.torusState`. `rectState_cubic`: at cubic extents
  `rectState hN (Lc M) β = torusState hN M β` (`TorusChain.expect_cubic`, and `rpull` is `pullback` there).
* **Slicing along any direction** (`corrNumR`). For `L μ = M + 1`, the Wilson correlation numerator of `O` is
  the closed chain `ZcR μ (tr L μ) N β M F` whenever `O (Φ L μ W)` is `F` read on the slices and steps of `W`;
  the proof is that of `TorusChain.corrNum_eq` with direction `0` and cubic extents replaced by `μ` and `L`
  (`RectWilson.measurePreserving_Φ`, `RectWilson.action_Φ`), the time extent `L μ` moved to `M + 1` inside
  `slice_integral`.
* **Window observables** (`rectState_winF`): for `f` reading only the links of the time window `[0, w]` along
  `μ` (`WinLocalR μ w f`), `w ≤ M`, every extent positive: `rectState hN L β f = ZcR (winFR f) / ZcR 1`.
* **The two-slice factorization** (`Zc_pairR`, `Zc_oneR`), for any direction and transverse extents:
  `ZcR (g (V 0, V (j+1))) = ∫∫ a² g` with `a = kT^{∗(j+1)}`, and `ZcR 1 = hs(a)`; the proof is
  `TwoSliceBridge.Zc_pair`'s.
* **`twoSliceLaw_rectState`** (the bridge at every step): for `β ≥ 0`, even `n ≥ 2` and every `i : Fin 4`,
  `TwoSliceLaw (rectState hN (ext n (pathV i)) β) β n i`.
* **`capturesReadTorus_capR`**: `CapturesReadTorus (capR hN)`. `capR_zero`: at step `0` and `n ≥ 1` the family
  is `torusState hN (n − 1) β`.
* **The seed.** `sectorSeedMeasured_of_readR`: `SectorSeedRead hN (capR hN) → SectorSeedMeasured hN`.
  `sectorSeedRead_capR_iff` (`N ≥ 2`): the two are equivalent.
* **The period tie** (`N ≥ 2`). `torusState_linkGap_pos`: for `0 < L' < M + 1` the torus state reads
  `linkGap L' 0 (0, 0)` strictly positive: the observable is continuous, nonnegative, and positive at the
  configuration with one link at an element of positive Wilson density
  (`ExistencePosNonnull.exists_wilsonDensity_pos`); the Gibbs weight is positive and product Haar charges open
  sets (`expect_pos_of_continuous`, the argument of `GibbsPositive.corrNum_plaqObs_pos`). Hence
  `measPeriod_torusState`: `measPeriod (torusState hN M β) = M + 1`, and `measPeriod_capR`:
  `measPeriod (capR hN β n 0) = n` for `n ≥ 1`. No Haar integral of a trace is used.
* **The strong-coupling witness at every step.** `reads_strong_rect`: at `0 ≤ β ≤ 2^{-16}` and the side conditions
  of `SubstrateFluxRead.sectors_strong`, both reads hold on `capR hN β n i` for every `i`, at any `ε` at least the two bounds of `sectors_strong`;
  `eventually_reads_strong_rect`: at every large even side both hold at `1/80000`.

## Argued, not built

Nothing is argued here. `SectorSeedRead hN (capR hN)` is not proved: it is equivalent (`N ≥ 2`) to
`SubstrateFluxRead.SectorSeedMeasured hN`, which remains open; its clauses at weak coupling are the open input.

## Assumed

Nothing beyond the imported modules. The period tie is proved at `n ≥ 1`; at `n = 0` the family is the point
state at the identity configuration, which reads period `1` (argued), and no clause of `SectorSeedRead` uses it.

DERIVED (module-wide): `0` the first slice and step `0`; `j + 1 = n/2` the second slice and half side,
`M + 1` the time extent; `2` the square in the density, the least side and the halving, and the least rank
with an element of positive Wilson density; `1` the identity link of `rpull`'s degenerate case;
`1/80000`, `65536`, `4 + N⁶`, `N³/2` the constants of `SubstrateFluxRead.sectors_strong`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.RectTorusState

open MeasureTheory Filter Topology
open MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.HiddenChain MassGap.KernelPower
  MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice
open MassGap.FluxDuality (readSlice siteOf siteOf_self siteOf_ne slicePair pairExp TwoSliceLaw FluxReadOf
  DefectReadOf fluxReadOf_iff defectReadOf_iff CapturesReadTorus SectorSeedRead)
open MassGap.CentreSectorSeedN (hSN halfKN fluxShareN trivialDefectN)
open MassGap.SubstrateFluxRead (measPeriod SectorSeedMeasured linkGap lineSite)
open MassGap.DLRLimit (State)
open MassGap.ContinuumSchwinger (Cfg)

variable {N : ℕ}

/-! ## 1. The rectangular pullback and the state -/

/-- **Reduction of an integer modulo a positive extent.** DERIVED: `0` the lower bound of the extent. -/
def rmod (m : ℕ) (hm : 0 < m) (z : ℤ) : Fin m :=
  ⟨(z % (m : ℤ)).toNat, by
    have hpos : (0 : ℤ) < m := by exact_mod_cast hm
    exact FluxDuality.toNat_lt (Int.emod_nonneg z hpos.ne') (Int.emod_lt_of_pos z hpos)⟩

/-- Reduction fixes a coordinate already inside the extent. DERIVED: no numeral. -/
theorem rmod_natCast {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k < m) : rmod m hm (k : ℤ) = ⟨k, hk⟩ := by
  apply Fin.ext
  show ((k : ℤ) % (m : ℤ)).toNat = k
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg k) (by exact_mod_cast hk), Int.toNat_natCast]

/-- **The rectangular pullback**: a link of `ℤ⁴` reads the torus link with coordinate `k` reduced modulo
`L k`; when some extent is `0` (no torus link exists) every link reads `1`. DERIVED: `0` the extent bound; `1`
the identity. -/
def rpull {G : Type} [One G] (L : Fin 4 → ℕ) (U : RLink L → G) (l : GibbsSpec.ILink) : G :=
  if h : ∀ k, 0 < L k then U (l.1, fun k => rmod (L k) (h k) (l.2 k)) else 1

/-- DERIVED: no numeral. -/
theorem measurable_rpull (L : Fin 4 → ℕ) :
    Measurable (fun U : RLink L → SUN.SU N => (rpull L U : GibbsSpec.IConf (SUN.SU N))) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h : ∀ k, 0 < L k
  · simp only [rpull, dif_pos h]; exact measurable_pi_apply _
  · simp only [rpull, dif_neg h]; exact measurable_const

/-- **An observable of `ℤ⁴` read on the rectangular torus.** DERIVED: no numeral. -/
def rectObs (L : Fin 4 → ℕ) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) : (RLink L → SUN.SU N) → ℝ :=
  fun U => f (rpull L U)

/-- DERIVED: no numeral. -/
theorem measurable_rectObs (L : Fin 4 → ℕ) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    Measurable (rectObs L f) :=
  f.continuous.measurable.comp (measurable_rpull L)

/-- **The rectangular Wilson torus state**: `f ↦ ⟨rectObs L f⟩` under the Wilson Gibbs measure of
`sysR L N` at coupling `β`. Additivity, homogeneity, positivity and normalization are the `WilsonReal` lemmas
used for `PeriodicState.torusState`. DERIVED: `0` the excluded rank in `hN`. -/
def rectState (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) : State (GibbsSpec.IConf (SUN.SU N)) where
  toFun f := (sysR L N).expect (probHaar (SUN.SU N)) β (rectObs L f)
  map_add' f g := by
    obtain ⟨Cf, hCf⟩ := InfiniteLattice.bounded_of_continuous f.continuous
    obtain ⟨Cg, hCg⟩ := InfiniteLattice.bounded_of_continuous g.continuous
    exact WilsonReal.wilsonSystem_expect_add (rbd L) β (rectObs L f) (rectObs L g)
      (WilsonReal.wilsonSystem_mul_boltz_integrable hN _ β _ (measurable_rectObs L f) Cf (fun W => hCf _))
      (WilsonReal.wilsonSystem_mul_boltz_integrable hN _ β _ (measurable_rectObs L g) Cg (fun W => hCg _))
  map_smul' c f := WilsonReal.wilsonSystem_expect_smul (rbd L) β c (rectObs L f)
  nonneg' f hf := WilsonReal.wilsonSystem_expect_nonneg hN (rbd L) β (rectObs L f) (fun W => hf _)
  one' := WilsonReal.wilsonSystem_expect_one hN (rbd L) β

/-- Two states that agree on every observable are equal. DERIVED: no numeral. -/
theorem state_ext {ν ν' : State (GibbsSpec.IConf (SUN.SU N))} (h : ∀ f, ν f = ν' f) : ν = ν' := by
  cases ν; cases ν'
  congr 1
  funext f; exact h f

/-- At cubic extents the rectangular pullback is `InfiniteLattice.pullback`. DERIVED: `1` the successor. -/
theorem rpull_cubic (M : ℕ) (W : RLink (TorusChain.Lc M) → SUN.SU N) :
    (rpull (TorusChain.Lc M) W : GibbsSpec.IConf (SUN.SU N)) = InfiniteLattice.pullback M W := by
  funext l
  have h : ∀ k, 0 < TorusChain.Lc M k := fun _ => Nat.succ_pos M
  rw [rpull, dif_pos h]
  have e : (fun k : Fin 4 => rmod (TorusChain.Lc M k) (h k) (l.2 k)) = InfiniteLattice.siteMod M l.2 := by
    funext k
    apply Fin.ext
    show ((l.2 k) % (((M + 1 : ℕ)) : ℤ)).toNat = ((l.2 k) % ((M : ℤ) + 1)).toNat
    rw [Nat.cast_succ]
  show W (l.1, _) = W (l.1, InfiniteLattice.siteMod M l.2)
  rw [e]

/-- **At cubic extents the rectangular state is the periodic state.** DERIVED: `1` the successor. -/
theorem rectState_cubic (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    rectState hN (TorusChain.Lc M) β = PeriodicState.torusState hN M β := by
  apply state_ext; intro f
  show (sysR (TorusChain.Lc M) N).expect (probHaar (SUN.SU N)) β (rectObs (TorusChain.Lc M) f)
    = ReflectPositive.EW (d := 4) (n := M + 1) N β (PeriodicState.torusObs M f)
  rw [show ReflectPositive.EW (d := 4) (n := M + 1) N β (PeriodicState.torusObs M f)
      = (sysR (TorusChain.Lc M) N).expect (probHaar (SUN.SU N)) β (PeriodicState.torusObs M f) from
    TorusChain.expect_cubic β _]
  congr 1

/-! ## 2. Slicing along a direction -/

section Slicing

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- Spatial links of one slice. -/
abbrev SlR (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) : Type := SpT μ T → SUN.SU N

/-- Axis links of one step. -/
abbrev AxR (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) : Type := TT μ T → SUN.SU N

/-- **The symmetric step weight** of direction `μ` and transverse extents `T`. DERIVED: `2` the halving of the
spatial action between the two ends and the double count of the temporal plaquettes. -/
def wtR (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (β : ℝ) (V : SlR μ T N) (A : AxR μ T N) (V' : SlR μ T N) : ℝ :=
  Real.exp (-β * spT μ T V / 2) * Real.exp (-β * (2 * tpT μ T A V V')) * Real.exp (-β * spT μ T V' / 2)

/-- DERIVED: no numeral. -/
theorem continuous_wtR' (β : ℝ) {Z : Type*} [TopologicalSpace Z] {f h : Z → SlR μ T N}
    {g : Z → AxR μ T N} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun q => wtR μ T N β (f q) (g q) (h q)) := by
  unfold wtR
  have h1 : Continuous (fun q => spT μ T (f q)) := continuous_sp hf
  have h2 : Continuous (fun q => spT μ T (h q)) := continuous_sp hh
  have h3 : Continuous (fun q => tpT μ T (g q) (f q) (h q)) := continuous_tp hg hf hh
  exact ((Real.continuous_exp.comp ((continuous_const.mul h1).div_const _)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul h3)))).mul
    (Real.continuous_exp.comp ((continuous_const.mul h2).div_const _))

/-- DERIVED: no numeral. -/
theorem wmeas_wtR (β : ℝ) : WMeas (wtR μ T N β) :=
  (continuous_wtR' β continuous_fst (continuous_fst.comp continuous_snd)
    (continuous_snd.comp continuous_snd)).measurable

/-- DERIVED: `0`. -/
theorem wtR_nonneg (β : ℝ) (V : SlR μ T N) (A : AxR μ T N) (V' : SlR μ T N) : 0 ≤ wtR μ T N β V A V' := by
  unfold wtR; positivity

/-- DERIVED: `0` the excluded rank and the coupling bound; `1` the bound. -/
theorem wtR_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V : SlR μ T N) (A : AxR μ T N) (V' : SlR μ T N) :
    wtR μ T N β V A V' ≤ 1 := by
  unfold wtR
  have a1 := sp_nonneg hN V
  have a2 := sp_nonneg hN V'
  have a3 := tp_nonneg hN A V V'
  have e1 : Real.exp (-β * spT μ T V / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-β * (2 * tpT μ T A V V')) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : Real.exp (-β * spT μ T V' / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have p1 := Real.exp_pos (-β * spT μ T V / 2)
  have p2 := Real.exp_pos (-β * (2 * tpT μ T A V V'))
  have h12 : Real.exp (-β * spT μ T V / 2) * Real.exp (-β * (2 * tpT μ T A V V')) ≤ 1 := by nlinarith
  nlinarith [mul_pos p1 p2]

/-- DERIVED: `0`, `1`. -/
theorem abs_wtR_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (V : SlR μ T N) (A : AxR μ T N) (V' : SlR μ T N), |wtR μ T N β V A V'| ≤ 1 := fun V A V' => by
  rw [abs_of_nonneg (wtR_nonneg β V A V')]; exact wtR_le_one hN hβ V A V'

/-- **The hidden-variable integral of the step weight is the transfer kernel.** DERIVED: no numeral. -/
theorem kern_wtR (β : ℝ) : kern (hA μ T N) (wtR μ T N β) = kT μ T N β := by
  funext x y
  simp only [kern, wtR, kT, gk]
  rw [integral_mul_const, integral_const_mul]

/-- **The torus integral of an insertion, closed by one transfer kernel.** DERIVED: no numeral. -/
def ZcR (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (β : ℝ) (M : ℕ) (F : (ℕ → SlR μ T N) → (ℕ → AxR μ T N) → ℝ) : ℝ :=
  ∫ x, chain (hS μ T N) (hA μ T N) (wtR μ T N β) M (fun V A => F V A * kT μ T N β (V M) x) x ∂(hS μ T N)

/-- A cyclic sequence of slice configurations from its axis and spatial parts. DERIVED: no numeral. -/
def joinR {K : ℕ} (A : Fin K → AxR μ T N) (V : Fin K → SlR μ T N) :
    Fin K → (TT μ T ⊕ SpT μ T) → SUN.SU N := fun t => Sum.elim (A t) (V t)

/-- DERIVED: no numeral. -/
theorem measurable_joinR {K : ℕ} :
    Measurable (fun p : (Fin K → AxR μ T N) × (Fin K → SlR μ T N) => joinR p.1 p.2) := by
  refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun s => ?_
  cases s with
  | inl y => exact (measurable_pi_apply y).comp ((measurable_pi_apply t).comp measurable_fst)
  | inr q => exact (measurable_pi_apply q).comp ((measurable_pi_apply t).comp measurable_snd)

/-- **The Gibbs weight of a cyclic sequence of slices.** DERIVED: `2` the double count of temporal
plaquettes. -/
def boltzW (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (β : ℝ) {K : ℕ} (W : Fin K → (TT μ T ⊕ SpT μ T) → SUN.SU N) : ℝ :=
  ∏ t, Real.exp (-β * (spT μ T (fun p => W t (Sum.inr p))
    + 2 * tpT μ T (fun y => W t (Sum.inl y)) (fun p => W t (Sum.inr p))
      (fun p => W (finRotate K t) (Sum.inr p))))

/-- DERIVED: `2`. -/
theorem prod_exp_wtR (β : ℝ) {K : ℕ} (A : Fin K → AxR μ T N) (V : Fin K → SlR μ T N) :
    ∏ t, Real.exp (-β * (spT μ T (V t) + 2 * tpT μ T (A t) (V t) (V (finRotate K t))))
      = ∏ t, wtR μ T N β (V t) (A t) (V (finRotate K t)) := by
  have h1 : ∀ t, Real.exp (-β * (spT μ T (V t) + 2 * tpT μ T (A t) (V t) (V (finRotate K t))))
      = Real.exp (-β * spT μ T (V t) / 2)
        * Real.exp (-β * (2 * tpT μ T (A t) (V t) (V (finRotate K t))))
        * Real.exp (-β * spT μ T (V t) / 2) := fun t => by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hrot : ∏ t, Real.exp (-β * spT μ T (V (finRotate K t)) / 2)
      = ∏ t, Real.exp (-β * spT μ T (V t) / 2) :=
    Fintype.prod_equiv (finRotate K) _ _ (fun t => rfl)
  simp only [h1, wtR, Finset.prod_mul_distrib, hrot]

/-- DERIVED: no numeral. -/
theorem continuous_prod_wtR (β : ℝ) {K : ℕ} :
    Continuous (fun p : (Fin K → AxR μ T N) × (Fin K → SlR μ T N) =>
      ∏ t, wtR μ T N β (p.2 t) (p.1 t) (p.2 (finRotate K t))) := by
  refine continuous_finsetProd _ fun t _ => ?_
  exact continuous_wtR' β ((continuous_apply t).comp continuous_snd)
    ((continuous_apply t).comp continuous_fst)
    ((continuous_apply (finRotate K t)).comp continuous_snd)

/-- DERIVED: `1`. -/
theorem abs_prod_wtR_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {K : ℕ} (A : Fin K → AxR μ T N)
    (V : Fin K → SlR μ T N) : |∏ t, wtR μ T N β (V t) (A t) (V (finRotate K t))| ≤ 1 := by
  have := CyclicKernel.abs_prod_le (u := fun t => wtR μ T N β (V t) (A t) (V (finRotate K t)))
    (C := 1) (fun t => abs_wtR_le hN hβ _ _ _)
  simpa using this

/-- **Peel the last axis slice**, which no insertion reads. DERIVED: `1` the successor. -/
theorem peelR (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (V : Fin (M + 1) → SlR μ T N)
    {g : (Fin M → AxR μ T N) → ℝ} (hg : Measurable g) {Bg : ℝ} (hgb : ∀ A, |g A| ≤ Bg) :
    ∫ A : Fin (M + 1) → AxR μ T N, g (fun t : Fin M => A t.castSucc)
        * ∏ t, wtR μ T N β (V t) (A t) (V (finRotate (M + 1) t)) ∂(Measure.pi fun _ => hA μ T N)
      = ∫ A' : Fin M → AxR μ T N, g A' * pathW (wtR μ T N β) V A'
          * kT μ T N β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hA μ T N) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => hA μ T N) (Fin.last M)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => AxR μ T N) (Fin.last M)
  set f : (Fin (M + 1) → AxR μ T N) → ℝ := fun A => g (fun t : Fin M => A t.castSucc)
    * ∏ t, wtR μ T N β (V t) (A t) (V (finRotate (M + 1) t))
  have hfm : Measurable f := by
    simp only [f]
    have hc : Measurable (fun A : Fin (M + 1) → AxR μ T N => fun t : Fin M => A t.castSucc) :=
      measurable_pi_lambda _ fun t => measurable_pi_apply t.castSucc
    have hp : Measurable (fun A : Fin (M + 1) → AxR μ T N =>
        ∏ t, wtR μ T N β (V t) (A t) (V (finRotate (M + 1) t))) :=
      Finset.measurable_prod _ fun t _ =>
        (continuous_wtR' β continuous_const (continuous_apply t) continuous_const).measurable
    exact (hg.comp hc).mul hp
  have hfb : ∀ A, |f A| ≤ Bg := fun A => by
    simp only [f]
    have := abs_mul_le_of (hgb (fun t : Fin M => A t.castSucc)) (abs_prod_wtR_le hN hβ A V)
    rwa [mul_one] at this
  have he : ∀ (a : AxR μ T N) (A' : Fin M → AxR μ T N), e.symm (a, A') = Fin.snoc A' a :=
    fun a A' => Fin.insertNth_last' a A'
  have h1 : ∫ A, f A ∂(Measure.pi fun _ => hA μ T N)
      = ∫ q, f (e.symm q) ∂((hA μ T N).prod (Measure.pi fun _ : Fin M => hA μ T N)) := by
    rw [← hmp.integral_comp' (g := fun q => f (e.symm q))]
    simp
  have hint : Integrable (fun q => f (e.symm q))
      ((hA μ T N).prod (Measure.pi fun _ : Fin M => hA μ T N)) :=
    integrable_of_bdd (hfm.comp e.symm.measurable) (fun q => hfb _)
  have hpt : ∀ (A' : Fin M → AxR μ T N) (a : AxR μ T N),
      f (Fin.snoc A' a) = (g A' * pathW (wtR μ T N β) V A') * wtR μ T N β (V (Fin.last M)) a (V 0) := by
    intro A' a
    simp only [f]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, finRotate_last]
    have hrot : ∀ t : Fin M, finRotate (M + 1) t.castSucc = t.succ := fun t => by
      rw [finRotate_apply, Fin.coeSucc_eq_succ]
    simp only [hrot]
    unfold pathW; ring
  change ∫ A, f A ∂(Measure.pi fun _ => hA μ T N) = _
  rw [h1, integral_prod_symm _ hint]
  congr 1; funext A'
  simp_rw [he, hpt]
  rw [integral_const_mul]
  congr 1
  exact congrFun (congrFun (kern_wtR (μ := μ) (T := T) (N := N) β) _) _

set_option maxHeartbeats 800000 in
/-- **The sliced Wilson integral as a closed chain.** The time extent `K` is a variable here, so that it can be
identified with `M + 1`. DERIVED: `1` the successor. -/
theorem slice_integral (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {K M : ℕ} (hK : K = M + 1)
    {P : (Fin K → (TT μ T ⊕ SpT μ T) → SUN.SU N) → ℝ} (hP : Measurable P) {BP : ℝ}
    (hPb : ∀ W, |P W| ≤ BP)
    {F : (ℕ → SlR μ T N) → (ℕ → AxR μ T N) → ℝ}
    (hF : Measurable (fun q : (ℕ → SlR μ T N) × (ℕ → AxR μ T N) => F q.1 q.2)) {BF : ℝ}
    (hFb : ∀ V A, |F V A| ≤ BF)
    (hPF : ∀ (A : Fin K → AxR μ T N) (V : Fin K → SlR μ T N), P (joinR A V)
      = F (extX (fun t : Fin (M + 1) => V (Fin.cast hK.symm t)))
          (extY (fun t : Fin M => A (Fin.cast hK.symm t.castSucc)))) :
    ∫ W, P W * boltzW μ T N β W
      ∂(Measure.pi fun _ : Fin K => Measure.pi fun _ : (TT μ T ⊕ SpT μ T) => probHaar (SUN.SU N))
      = ZcR μ T N β M F := by
  subst hK
  have hPF' : ∀ (A : Fin (M + 1) → AxR μ T N) (V : Fin (M + 1) → SlR μ T N),
      P (joinR A V) = F (extX V) (extY (fun t : Fin M => A t.castSucc)) := fun A V => hPF A V
  set φ := (⇑(MeasurableEquiv.arrowProdEquivProdArrow (TT μ T → SUN.SU N)
      (SpT μ T → SUN.SU N) (Fin (M + 1)))) ∘
    fun (W : Fin (M + 1) → (TT μ T ⊕ SpT μ T) → SUN.SU N) t =>
      MeasurableEquiv.sumPiEquivProdPi (fun _ : (TT μ T ⊕ SpT μ T) => SUN.SU N) (W t) with hφdef
  have hφ : MeasurePreserving φ
      (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : (TT μ T ⊕ SpT μ T) => probHaar (SUN.SU N))
      ((Measure.pi fun _ : Fin (M + 1) => hA μ T N).prod
        (Measure.pi fun _ : Fin (M + 1) => hS μ T N)) := by
    have hmp1 : MeasurePreserving
        (fun (W : Fin (M + 1) → (TT μ T ⊕ SpT μ T) → SUN.SU N) t =>
          MeasurableEquiv.sumPiEquivProdPi (fun _ : (TT μ T ⊕ SpT μ T) => SUN.SU N) (W t))
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : (TT μ T ⊕ SpT μ T) => probHaar (SUN.SU N))
        (Measure.pi fun _ : Fin (M + 1) => (hA μ T N).prod (hS μ T N)) :=
      measurePreserving_pi _ _ fun _ => measurePreserving_sumPiEquivProdPi _
    have hmp2 := measurePreserving_arrowProdEquivProdArrow (TT μ T → SUN.SU N)
      (SpT μ T → SUN.SU N) (Fin (M + 1)) (fun _ => hA μ T N) (fun _ => hS μ T N)
    exact hmp2.comp hmp1
  set H : (Fin (M + 1) → AxR μ T N) × (Fin (M + 1) → SlR μ T N) → ℝ :=
    fun p => P (joinR p.1 p.2) * ∏ t, wtR μ T N β (p.2 t) (p.1 t) (p.2 (finRotate (M + 1) t))
  have hHm : Measurable H := by
    simp only [H]
    exact (TorusChain.meas_comp' hP measurable_joinR).mul (continuous_prod_wtR β).measurable
  have hHb : ∀ p, |H p| ≤ BP := fun p => by
    simp only [H]
    have := abs_mul_le_of (hPb (joinR p.1 p.2)) (abs_prod_wtR_le hN hβ p.1 p.2)
    rwa [mul_one] at this
  have hjoin : ∀ W, joinR (φ W).1 (φ W).2 = W := by
    intro W; funext t s; cases s <;> rfl
  have hHW : ∀ W, P W * boltzW μ T N β W = H (φ W) := by
    intro W
    simp only [H]
    rw [hjoin W]
    congr 1
    exact prod_exp_wtR β _ _
  have step1 : ∫ W, P W * boltzW μ T N β W
      ∂(Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : (TT μ T ⊕ SpT μ T) => probHaar (SUN.SU N))
      = ∫ p, H p ∂((Measure.pi fun _ : Fin (M + 1) => hA μ T N).prod
          (Measure.pi fun _ : Fin (M + 1) => hS μ T N)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hHW)]
    rw [← hφ.map_eq, integral_map hφ.measurable.aemeasurable hHm.aestronglyMeasurable]
  rw [step1, integral_prod_symm H (integrable_of_bdd hHm hHb)]
  have hFV : ∀ V : Fin (M + 1) → SlR μ T N,
      Measurable (fun A' : Fin M → AxR μ T N => F (extX V) (extY A')) :=
    fun V => hF.comp (measurable_const.prodMk measurable_extY)
  have step2 : ∀ V : Fin (M + 1) → SlR μ T N, ∫ A, H (A, V) ∂(Measure.pi fun _ => hA μ T N)
      = ∫ A' : Fin M → AxR μ T N, F (extX V) (extY A') * pathW (wtR μ T N β) V A'
          * kT μ T N β (V (Fin.last M)) (V 0) ∂(Measure.pi fun _ => hA μ T N) := by
    intro V
    simp only [H, hPF']
    exact peelR hN hβ V (hFV V) (fun A' => hFb _ _)
  simp_rw [step2]
  have hG : Measurable (fun q : (ℕ → SlR μ T N) × (ℕ → AxR μ T N) =>
      F q.1 q.2 * kT μ T N β (q.1 M) (q.1 0)) := by
    refine hF.mul ?_
    have hk : Measurable (Function.uncurry (kT μ T N β)) :=
      (continuous_kT (μ := μ) (T := T) (N := N) β).measurable
    exact TorusChain.meas_comp2 hk ((measurable_pi_apply M).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_fst)
  have hGb : ∀ V A, |F V A * kT μ T N β (V M) (V 0)| ≤ BF * 1 := fun V A =>
    abs_mul_le_of (hFb V A) (abs_kT_le hN hβ _ _)
  have hbr := bridge (μ := hS μ T N) (ν := hA μ T N) (wmeas_wtR β)
    (fun V A V' => abs_wtR_le hN hβ V A V') M
    (G := fun V A => F V A * kT μ T N β (V M) (V 0)) hG hGb
  unfold ZcR
  have hcl : ∀ x, chain (hS μ T N) (hA μ T N) (wtR μ T N β) M
      (fun V A => F V A * kT μ T N β (V M) x) x
      = chain (hS μ T N) (hA μ T N) (wtR μ T N β) M
        (fun V A => F V A * kT μ T N β (V M) (V 0)) x :=
    fun x => chain_congr M (fun V A hV => by rw [hV])
  simp_rw [hcl]
  rw [← hbr]
  congr 1; funext V; congr 1; funext A'
  rw [extX_last, extX_zero]; ring

end Slicing

/-- **The Wilson correlation numerator of the rectangular torus as a closed chain along `μ`.**
DERIVED: `1` the successor. -/
theorem corrNumR (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {μ : Fin 4} {M : ℕ}
    (hL : L μ = M + 1) {O : (RLink L → SUN.SU N) → ℝ} (hO : Measurable O) {BO : ℝ}
    (hOb : ∀ U, |O U| ≤ BO)
    {F : (ℕ → SlR μ (tr L μ) N) → (ℕ → AxR μ (tr L μ) N) → ℝ}
    (hF : Measurable (fun q : (ℕ → SlR μ (tr L μ) N) × (ℕ → AxR μ (tr L μ) N) => F q.1 q.2)) {BF : ℝ}
    (hFb : ∀ V A, |F V A| ≤ BF)
    (hOF : ∀ (A : Fin (L μ) → AxR μ (tr L μ) N) (V : Fin (L μ) → SlR μ (tr L μ) N),
      O (Φ L μ (joinR A V)) = F (extX (fun t : Fin (M + 1) => V (Fin.cast hL.symm t)))
        (extY (fun t : Fin M => A (Fin.cast hL.symm t.castSucc)))) :
    (sysR L N).corrNum (probHaar (SUN.SU N)) β O = ZcR μ (tr L μ) N β M F := by
  have hmp := measurePreserving_Φ (L := L) (μ := μ) N
  unfold System.corrNum System.vol
  change ∫ U : RLink L → SUN.SU N, O U * (sysR L N).boltz β U
      ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) = _
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (hO.mul (measurable_boltzR (L := L) N β)).aestronglyMeasurable]
  have e : ∀ W : Fin (L μ) → SlIdx L μ → SUN.SU N,
      O (Φ L μ W) * (sysR L N).boltz β (Φ L μ W) = O (Φ L μ W) * boltzW μ (tr L μ) N β W := by
    intro W
    congr 1
    unfold System.boltz
    rw [action_Φ hN W, Finset.mul_sum, Real.exp_sum]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  exact slice_integral hN hβ hL (P := fun W => O (Φ L μ W)) (hO.comp hmp.measurable)
    (fun W => hOb _) hF hFb hOF

/-! ## 3. Observables read on a time window along `μ` -/

section Window

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

variable (μ) in
/-- Transverse coordinates of a site, reduced modulo the transverse extents. DERIVED: `0`. -/
def perpR (hT : ∀ j, 0 < T j) (s : Fin 4 → ℤ) : TT μ T := fun j => rmod (T j) (hT j) (s j.1)

/-- **The `ℤ⁴` configuration with slices `V` and steps `A` along `μ`** at non-negative times, `1` elsewhere.
DERIVED: `0` the first time; `1` the identity. -/
def cfgR (hT : ∀ j, 0 < T j) (V : ℕ → SlR μ T N) (A : ℕ → AxR μ T N) : GibbsSpec.IConf (SUN.SU N) :=
  fun l => if 0 ≤ l.2 μ then
      (if h : l.1 = μ then A (l.2 μ).toNat (perpR μ hT l.2)
        else V (l.2 μ).toNat (⟨l.1, h⟩, perpR μ hT l.2))
    else 1

/-- DERIVED: `0`. -/
theorem cfgR_axis {hT : ∀ j, 0 < T j} {V : ℕ → SlR μ T N} {A : ℕ → AxR μ T N} {l : GibbsSpec.ILink}
    (h : l.1 = μ) (h0 : 0 ≤ l.2 μ) : cfgR hT V A l = A (l.2 μ).toNat (perpR μ hT l.2) := by
  simp only [cfgR, if_pos h0, dif_pos h]

/-- DERIVED: `0`. -/
theorem cfgR_sp {hT : ∀ j, 0 < T j} {V : ℕ → SlR μ T N} {A : ℕ → AxR μ T N} {l : GibbsSpec.ILink}
    (h : l.1 ≠ μ) (h0 : 0 ≤ l.2 μ) : cfgR hT V A l = V (l.2 μ).toNat (⟨l.1, h⟩, perpR μ hT l.2) := by
  simp only [cfgR, if_pos h0, dif_neg h]

/-- DERIVED: `0`. -/
theorem measurable_cfgR (hT : ∀ j, 0 < T j) :
    Measurable (fun q : (ℕ → SlR μ T N) × (ℕ → AxR μ T N) => cfgR hT q.1 q.2) := by
  refine measurable_pi_lambda _ fun l => ?_
  by_cases h0 : 0 ≤ l.2 μ
  · by_cases h : l.1 = μ
    · simp only [cfgR, if_pos h0, dif_pos h]
      exact (measurable_pi_apply (perpR μ hT l.2)).comp
        ((measurable_pi_apply (l.2 μ).toNat).comp measurable_snd)
    · simp only [cfgR, if_pos h0, dif_neg h]
      exact (measurable_pi_apply ((⟨l.1, h⟩ : {j : Fin 4 // j ≠ μ}), perpR μ hT l.2)).comp
        ((measurable_pi_apply (l.2 μ).toNat).comp measurable_fst)
  · simp only [cfgR, if_neg h0]; exact measurable_const

/-- **An observable read on the chain variables of direction `μ`.** DERIVED: no numeral. -/
def winFR (hT : ∀ j, 0 < T j) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    (ℕ → SlR μ T N) → (ℕ → AxR μ T N) → ℝ :=
  fun V A => f (cfgR hT V A)

/-- DERIVED: no numeral. -/
theorem measurable_winFR (hT : ∀ j, 0 < T j) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    Measurable (fun q : (ℕ → SlR μ T N) × (ℕ → AxR μ T N) => winFR hT f q.1 q.2) :=
  f.continuous.measurable.comp (measurable_cfgR hT)

/-- DERIVED: no numeral. -/
theorem winFR_bdd (hT : ∀ j, 0 < T j) (f : C(GibbsSpec.IConf (SUN.SU N), ℝ)) :
    ∃ B, ∀ V A, |winFR (μ := μ) (T := T) hT f V A| ≤ B := by
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  exact ⟨C, fun V A => hC _⟩

end Window

/-- A link of the time window `[0, w]` along `μ`: spatial at times `0..w`, axis at times `0..w−1`.
DERIVED: `0` the first time. -/
def InWinR (μ : Fin 4) (w : ℕ) (l : GibbsSpec.ILink) : Prop :=
  0 ≤ l.2 μ ∧ l.2 μ ≤ w ∧ (l.1 = μ → l.2 μ < w)

/-- `f` reads only links of the time window `[0, w]` along `μ`. DERIVED: no numeral. -/
def WinLocalR (μ : Fin 4) (w : ℕ) (f : GibbsSpec.IConf (SUN.SU N) → ℝ) : Prop :=
  ∀ U U' : GibbsSpec.IConf (SUN.SU N), (∀ l, InWinR μ w l → U l = U' l) → f U = f U'

/-- **A window observable read on the torus is read on the chain.** DERIVED: `0`, `1`. -/
theorem rect_window {L : Fin 4 → ℕ} {μ : Fin 4} {M : ℕ} (hL : L μ = M + 1) (hpos : ∀ k, 0 < L k) {w : ℕ}
    {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)} (hf : WinLocalR μ w f) (hwM : w ≤ M)
    (A : Fin (L μ) → AxR μ (tr L μ) N) (V : Fin (L μ) → SlR μ (tr L μ) N) :
    f (rpull L (Φ L μ (joinR A V)))
      = winFR (fun j => hpos j.1) f (extX (fun t : Fin (M + 1) => V (Fin.cast hL.symm t)))
          (extY (fun t : Fin M => A (Fin.cast hL.symm t.castSucc))) := by
  apply hf
  rintro ⟨d0, s⟩ ⟨h0, h1, h2⟩
  dsimp only at h0 h1 h2
  have hp : rpull L (Φ L μ (joinR A V)) (d0, s)
      = joinR A V (rmod (L μ) (hpos μ) (s μ)) (sIdx d0 (perpR μ (fun j => hpos j.1) s)) := by
    rw [rpull, dif_pos hpos]
    rfl
  rw [hp]
  have hlt : s μ < ((L μ : ℕ) : ℤ) := by rw [hL]; push_cast; omega
  have hfm : rmod (L μ) (hpos μ) (s μ) = Fin.cast hL.symm ⟨(s μ).toNat, by omega⟩ := by
    apply Fin.ext
    show ((s μ) % ((L μ : ℕ) : ℤ)).toNat = (s μ).toNat
    rw [Int.emod_eq_of_lt h0 hlt]
  rw [hfm]
  by_cases h : d0 = μ
  · have ht := h2 h
    rw [cfgR_axis (l := (d0, s)) h h0]
    have hs : sIdx (L := L) (μ := μ) d0 (perpR μ (fun j => hpos j.1) s)
        = Sum.inl (perpR μ (fun j => hpos j.1) s) := by simp [sIdx, h]
    rw [hs]
    show A (Fin.cast hL.symm ⟨(s μ).toNat, _⟩) (perpR μ _ s)
      = extY (fun t : Fin M => A (Fin.cast hL.symm t.castSucc)) (s μ).toNat (perpR μ _ s)
    simp only [extY, dif_pos (show (s μ).toNat < M by omega)]
    rfl
  · rw [cfgR_sp (l := (d0, s)) h h0]
    have hs : sIdx (L := L) (μ := μ) d0 (perpR μ (fun j => hpos j.1) s)
        = Sum.inr (⟨d0, h⟩, perpR μ (fun j => hpos j.1) s) := by simp [sIdx, h]
    rw [hs]
    show V (Fin.cast hL.symm ⟨(s μ).toNat, _⟩) (⟨d0, h⟩, perpR μ _ s)
      = extX (fun t : Fin (M + 1) => V (Fin.cast hL.symm t)) (s μ).toNat (⟨d0, h⟩, perpR μ _ s)
    simp only [extX, dif_pos (show (s μ).toNat < M + 1 by omega)]

/-- **The rectangular Wilson state on a window observable is a ratio of closed chains.**
DERIVED: `0` the extent bound. -/
theorem rectState_winF (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {μ : Fin 4} {M : ℕ}
    (hL : L μ = M + 1) (hpos : ∀ k, 0 < L k) {w : ℕ} {f : C(GibbsSpec.IConf (SUN.SU N), ℝ)}
    (hf : WinLocalR μ w f) (hwM : w ≤ M) :
    rectState hN L β f
      = ZcR μ (tr L μ) N β M (winFR (fun j => hpos j.1) f) / ZcR μ (tr L μ) N β M (fun _ _ => 1) := by
  obtain ⟨Bf, hBf⟩ := InfiniteLattice.bounded_of_continuous f.continuous
  obtain ⟨BF, hBF⟩ := winFR_bdd (μ := μ) (T := tr L μ) (fun j => hpos j.1) f
  have hnum := corrNumR hN hβ hL (O := rectObs L f) (measurable_rectObs L f) (fun U => hBf _)
    (measurable_winFR _ f) hBF (fun A V => rect_window hL hpos hf hwM A V)
  have hden := corrNumR (L := L) (μ := μ) hN hβ hL (O := fun _ => 1) measurable_const (BO := 1)
    (fun _ => by simp) (F := fun _ _ => 1) measurable_const (BF := 1) (fun _ _ => by simp)
    (fun _ _ => rfl)
  show (sysR L N).expect (probHaar (SUN.SU N)) β (rectObs L f) = _
  rw [System.expect, hnum, ← hden]
  congr 1
  simp [System.partition, System.corrNum]

/-! ## 4. The two-slice law at every step -/

section TwoSlice

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

variable (μ T) in
/-- **The two-slice observable along `μ`**: `h` read on the spatial links at times `0` and `t`.
DERIVED: `0` the first slice. -/
def pairObsR (t : ℕ) (h : C((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N), ℝ)) :
    C(GibbsSpec.IConf (SUN.SU N), ℝ) :=
  h.comp ((readSlice μ T 0).prodMk (readSlice μ T (t : ℤ)))

/-- **The two-slice observable reads the window `[0, t]`.** DERIVED: `0`. -/
theorem winLocal_pairObsR (t : ℕ) (h : C((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N), ℝ)) :
    WinLocalR μ t (pairObsR μ T t h) := by
  intro U U' hUU
  have e : ∀ s : ℤ, 0 ≤ s → s ≤ t → readSlice (N := N) μ T s U = readSlice μ T s U' := by
    intro s h0 h1
    funext l
    show U (l.1.1, siteOf μ s l.2) = U' (l.1.1, siteOf μ s l.2)
    exact hUU _ ⟨by show 0 ≤ siteOf μ s l.2 μ; rw [siteOf_self]; exact h0,
      by show siteOf μ s l.2 μ ≤ (t : ℤ); rw [siteOf_self]; exact h1, fun hl => absurd hl l.1.2⟩
  show h (readSlice μ T 0 U, readSlice μ T (t : ℤ) U) = h (readSlice μ T 0 U', readSlice μ T (t : ℤ) U')
  rw [e 0 le_rfl (Int.natCast_nonneg t), e (t : ℤ) (Int.natCast_nonneg t) le_rfl]

/-- The transverse site of a slice point, reduced, is the slice point. DERIVED: no numeral. -/
theorem perpR_siteOf (hT : ∀ j, 0 < T j) (t : ℤ) (y : TT μ T) : perpR μ hT (siteOf μ t y) = y := by
  funext k
  show rmod (T k) (hT k) (siteOf μ t y k.1) = y k
  rw [siteOf_ne]
  exact rmod_natCast (hT k) (y k).2

/-- **A slice read on the chain configuration is the chain's slice.** DERIVED: `0`. -/
theorem readSlice_cfgR (hT : ∀ j, 0 < T j) (V : ℕ → SlR μ T N) (A : ℕ → AxR μ T N) {s : ℤ}
    (hs : 0 ≤ s) : readSlice μ T s (cfgR hT V A) = V s.toNat := by
  funext l
  show cfgR hT V A (l.1.1, siteOf μ s l.2) = V s.toNat l
  rw [cfgR_sp (l := (l.1.1, siteOf μ s l.2)) l.1.2
    (by show 0 ≤ siteOf μ s l.2 μ; rw [siteOf_self]; exact hs)]
  show V (siteOf μ s l.2 μ).toNat (⟨l.1.1, l.1.2⟩, perpR μ hT (siteOf μ s l.2)) = V s.toNat l
  rw [siteOf_self, perpR_siteOf]

/-- **The two-slice observable in chain variables.** DERIVED: `0`. -/
theorem winFR_pairObsR (hT : ∀ j, 0 < T j) {t : ℕ} (h : C(SlR μ T N × SlR μ T N, ℝ))
    (V : ℕ → SlR μ T N) (A : ℕ → AxR μ T N) :
    winFR hT (pairObsR μ T t h) V A = h (V 0, V t) := by
  show h (readSlice μ T 0 (cfgR hT V A), readSlice μ T (t : ℤ) (cfgR hT V A)) = h (V 0, V t)
  rw [readSlice_cfgR hT V A le_rfl, readSlice_cfgR hT V A (Int.natCast_nonneg t), Int.toNat_natCast,
    Int.toNat_zero]

/-- **The closed chain with the two slices inserted**, in any direction:
`ZcR (g (V 0, V (j+1))) = ∫∫ a(x, z)² g(x, z)` with `a = kT^{∗(j+1)}`. DERIVED: `2` the square; `j + 1` the
half side. -/
theorem Zc_pairR (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (g : C(SlR μ T N × SlR μ T N, ℝ)) :
    ZcR μ T N β (j + 1 + j) (fun V _ => g (V 0, V (j + 1)))
      = ∫ x, ∫ z, iter (hS μ T N) (kT μ T N β) j x z ^ 2 * g (x, z) ∂hS μ T N ∂hS μ T N := by
  have hac : Continuous (Function.uncurry (iter (hS μ T N) (kT μ T N β) j)) :=
    SliceKernelPower.continuous_iter (μ := μ) (T := T) (N := N) β j
  unfold ZcR
  congr 1; funext x
  have step1 : chain (hS μ T N) (hA μ T N) (wtR μ T N β) (j + 1 + j)
      (fun V _ => g (V 0, V (j + 1)) * kT μ T N β (V (j + 1 + j)) x) x
      = chain (hS μ T N) (hA μ T N) (wtR μ T N β) (j + 1 + j)
      (fun V _ => g (V 0, V (j + 1)) * kern (hA μ T N) (wtR μ T N β) (sshift V (j + 1) j) x) x := by
    congr 1; funext V A
    rw [kern_wtR]
    show _ = g (V 0, V (j + 1)) * kT μ T N β (V (j + (j + 1))) x
    rw [show j + (j + 1) = j + 1 + j by omega]
  have hsplit := chain_split (μ := hS μ T N) (ν := hA μ T N) (w := wtR μ T N β) (j + 1) j
    (G1 := fun V (_ : ℕ → AxR μ T N) => g (V 0, V (j + 1)))
    (fun V (_ : ℕ → AxR μ T N) => kern (hA μ T N) (wtR μ T N β) (V j) x) x
    (fun V V' A A' hV _ => by
      show g (V 0, V (j + 1)) = g (V' 0, V' (j + 1))
      rw [hV 0 (Nat.zero_le _), hV (j + 1) le_rfl])
  refine step1.trans (hsplit.trans ?_)
  have hend : ∀ z, chain (hS μ T N) (hA μ T N) (wtR μ T N β) j
      (fun V (_ : ℕ → AxR μ T N) => kern (hA μ T N) (wtR μ T N β) (V j) x) z
      = iter (hS μ T N) (kT μ T N β) j z x := by
    intro z; rw [chain_end_kern x j z, kern_wtR]
  simp only [hend]
  set g' : SlR μ T N → ℝ := fun z => g (x, z) * iter (hS μ T N) (kT μ T N β) j z x with hg'
  have hg'c : Continuous g' :=
    (g.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hac.comp (continuous_id.prodMk continuous_const))
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg'c.continuousOn
  have hg'b : ∀ z, |g' z| ≤ B := fun z => by
    simpa [Real.norm_eq_abs] using hB z (Set.mem_univ z)
  have step3 : chain (hS μ T N) (hA μ T N) (wtR μ T N β) (j + 1)
      (fun V _ => g (V 0, V (j + 1)) * iter (hS μ T N) (kT μ T N β) j (V (j + 1)) x) x
      = chain (hS μ T N) (hA μ T N) (wtR μ T N β) (j + 1) (fun V _ => g' (V (j + 1))) x :=
    chain_congr (j + 1) (fun V A hV => by rw [hg']; dsimp only; rw [hV])
  refine step3.trans ?_
  rw [chain_end_iter (μ := hS μ T N) (ν := hA μ T N) (wmeas_wtR β) (abs_wtR_le hN hβ)
    hg'c.measurable hg'b j x, kern_wtR]
  congr 1; funext z
  rw [hg']
  dsimp only
  rw [CyclicKernel.iter_symm (μ := hS μ T N) (bdd_kT hN hβ) (kT_symm β) j z x]
  ring

/-- **The closed chain is the trace**: `ZcR 1 = hs(a)`. DERIVED: no numeral. -/
theorem Zc_oneR (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    ZcR μ T N β (j + 1 + j) (fun _ _ => 1) = hs (hS μ T N) (iter (hS μ T N) (kT μ T N β) j) := by
  have e := Zc_pairR hN hβ j (1 : C(SlR μ T N × SlR μ T N, ℝ))
  simp only [ContinuousMap.one_apply, mul_one] at e
  exact e

end TwoSlice

/-- **The rectangular state on the two-slice observable**: at time extent `2j + 2` along `μ`,
`rectState (pairObsR h) = (∫∫ a² h) / hs(a)`. DERIVED: `j + 1` the half side; `0` the extent bound. -/
theorem rectState_pairObs (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : Fin 4 → ℕ} {μ : Fin 4} (j : ℕ)
    (hL : L μ = j + 1 + j + 1) (hpos : ∀ k, 0 < L k)
    (h : C(SlR μ (tr L μ) N × SlR μ (tr L μ) N, ℝ)) :
    rectState hN L β (pairObsR μ (tr L μ) (j + 1) h)
      = pairExp (hS μ (tr L μ) N) (iter (hS μ (tr L μ) N) (kT μ (tr L μ) N β) j) ⇑h := by
  rw [rectState_winF hN hβ hL hpos (winLocal_pairObsR (j + 1) h) (by omega)]
  have e : winFR (fun j => hpos j.1) (pairObsR μ (tr L μ) (j + 1) h) = fun V _ => h (V 0, V (j + 1)) := by
    funext V A; exact winFR_pairObsR _ h V A
  rw [e, Zc_pairR hN hβ j h, Zc_oneR hN hβ j]
  all_goals rfl

/-- The time extent of step `i` is the side. DERIVED: `2` the doubling base. -/
theorem ext_pathV_self (n : ℕ) (i : Fin 4) : DoublingWilson.ext n (CentreSectorSeed.pathV i) i = n := by
  show 2 ^ (CentreSectorSeed.pathV i i) * n = n
  rw [CentreSectorSeed.pathV_self, pow_zero, one_mul]

/-- Every extent of a corner torus of positive side is positive. DERIVED: `0`, `2`. -/
theorem ext_pos {n : ℕ} (hn : 0 < n) (v : Fin 4 → ℕ) (k : Fin 4) :
    0 < DoublingWilson.ext n v k := by
  show 0 < 2 ^ (v k) * n
  positivity

/-- **The bridge at every step**: the Wilson state of the corner torus of step `i` has the two-slice law
`a²/A`. DERIVED: `2` the least side; `1` in `n/2 − 1`. -/
theorem twoSliceLaw_rectState [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (i : Fin 4) :
    TwoSliceLaw (rectState hN (DoublingWilson.ext n (CentreSectorSeed.pathV i)) β) β n i := by
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 2 := by
    obtain ⟨k, rfl⟩ := he
    exact ⟨k - 1, by omega⟩
  intro h
  have hL : DoublingWilson.ext n (CentreSectorSeed.pathV i) i = j + 1 + j + 1 := by
    rw [ext_pathV_self]; omega
  have hpos : ∀ k, 0 < DoublingWilson.ext n (CentreSectorSeed.pathV i) k :=
    fun k => ext_pos (by omega) _ k
  have e1 : h.comp (slicePair n i) = pairObsR i (CentreSectorSeed.Tr n i) (n / 2) h := rfl
  have e2 : n / 2 = j + 1 := by omega
  have e3 : halfKN N β n i = iter (hS i (CentreSectorSeed.Tr n i) N) (kT i (CentreSectorSeed.Tr n i) N β) j := by
    unfold halfKN
    rw [e2, Nat.add_sub_cancel]
  rw [e1, e2, e3]
  exact rectState_pairObs hN hβ j hL hpos h

/-! ## 5. The family of Wilson captures -/

/-- **The Wilson capture of step `i` at side `n`**: the rectangular Wilson state of the corner torus
`ext n (pathV i)`. DERIVED: no numeral. -/
def capR (hN : N ≠ 0) (β : ℝ) (n : ℕ) (i : Fin 4) : State (Cfg N) :=
  rectState hN (DoublingWilson.ext n (CentreSectorSeed.pathV i)) β

/-- **The bridge along the Wilson family.** DERIVED: no numeral. -/
theorem capturesReadTorus_capR [NeZero N] (hN : N ≠ 0) : CapturesReadTorus (capR hN) :=
  fun _ hβ _ hn he i => twoSliceLaw_rectState hN hβ hn he i

/-- **At step `0` the family is the periodic state of side `n`.** DERIVED: `1` the least side and the successor;
`0` the step. -/
theorem capR_zero (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    capR hN β n 0 = PeriodicState.torusState hN (n - 1) β := by
  unfold capR
  rw [GapSideTwistBridge.ext_pathV_zero]
  have e : (fun _ : Fin 4 => n) = TorusChain.Lc (n - 1) := by
    funext k; show n = n - 1 + 1; omega
  rw [e, rectState_cubic]

/-- **The read seed on the Wilson family gives the measured seed.** DERIVED: no numeral. -/
theorem sectorSeedMeasured_of_readR [NeZero N] (hN : N ≠ 0) (h : SectorSeedRead hN (capR hN)) :
    SectorSeedMeasured hN :=
  FluxDuality.sectorSeedMeasured_of_read hN (capturesReadTorus_capR hN) h

/-! ## 6. The period tie -/

/-- **A Wilson expectation of a continuous nonnegative observable, positive somewhere, is positive.**
The argument of `GibbsPositive.corrNum_plaqObs_pos` with a general observable. DERIVED: `0`. -/
theorem expect_pos_of_continuous (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    {O : (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).Config → ℝ} (hc : Continuous O)
    (hO : ∀ U, 0 ≤ O U) {B : ℝ} (hB : ∀ U, |O U| ≤ B)
    (U₀ : (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).Config) (hU₀ : 0 < O U₀) :
    0 < (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).expect (probHaar (SUN.SU N)) β O := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).vol
      (probHaar (SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Lk => probHaar (SUN.SU N))))
  haveI : ((wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).vol
      (probHaar (SUN.SU N))).IsOpenPosMeasure :=
    inferInstanceAs ((Measure.pi (fun _ : Lk => probHaar (SUN.SU N))).IsOpenPosMeasure)
  have hwpos : ∀ U, 0 < (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).boltz β U :=
    fun U => WilsonReal.wilsonSystem_boltz_pos bd β U
  have hnn : (0 : (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).Config → ℝ)
      ≤ fun U => O U * (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).boltz β U :=
    fun U => mul_nonneg (hO U) (hwpos U).le
  have hint : Integrable (fun U => O U * (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).vol (probHaar (SUN.SU N))) :=
    WilsonReal.wilsonSystem_mul_boltz_integrable hN bd β O hc.measurable B hB
  unfold System.expect
  refine div_pos ?_ (WilsonReal.wilsonSystem_partition_pos hN bd β)
  unfold System.corrNum
  refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => ?_)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
  have hcont : Continuous (fun U => O U * (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).boltz β U) :=
    hc.mul (GibbsPositive.continuous_boltz bd β)
  have hzero := (Continuous.ae_eq_iff_eq
    ((wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).vol (probHaar (SUN.SU N)))
    hcont continuous_const).mp hae
  have hU : O U₀ * (wilsonSystem bd (WilsonAction.wilsonDensity (N := N))).boltz β U₀ = 0 :=
    congrFun hzero U₀
  exact hU₀.ne' ((mul_eq_zero.mp hU).resolve_right (hwpos U₀).ne')

/-- **One link at `g`, every other link `1`.** DERIVED: `0` the link; `1` the identity. -/
def spike (M : ℕ) (g : SUN.SU N) (l : WilsonHypercubic.Link 4 (M + 1)) : SUN.SU N :=
  if l = InfiniteLattice.linkMod M ((0 : Fin 4), (0 : GibbsSpec.ISite)) then g else 1

/-- **The torus state separates a link from its translate by less than the extent** (`N ≥ 2`): it reads
`linkGap L' 0 (0, 0)` strictly positive for `0 < L' < M + 1`. DERIVED: `2` the least rank; `0` the direction,
the link and the bound. -/
theorem torusState_linkGap_pos (hN : N ≠ 0) (hN2 : 2 ≤ N) (M : ℕ) (β : ℝ) {L' : ℕ} (h0 : 0 < L')
    (hlt : L' < M + 1) :
    0 < PeriodicState.torusState hN M β (linkGap L' 0 ((0 : Fin 4), (0 : GibbsSpec.ISite))) := by
  obtain ⟨g, hg⟩ := ExistencePosNonnull.exists_wilsonDensity_pos (N := N) hN2
  have hne : InfiniteLattice.linkMod M ((0 : Fin 4), lineSite 0 (0 : GibbsSpec.ISite) (L' : ℤ))
      ≠ InfiniteLattice.linkMod M ((0 : Fin 4), (0 : GibbsSpec.ISite)) := by
    intro heq
    have h1 := congrArg (fun l : WilsonHypercubic.Link 4 (M + 1) => ((l.2 0 : Fin (M + 1)) : ℕ)) heq
    have e1 : lineSite 0 (0 : GibbsSpec.ISite) (L' : ℤ) 0 = ((L' : ℕ) : ℤ) := by
      rw [SubstrateFluxRead.lineSite_self]; simp
    have e2 : (0 : GibbsSpec.ISite) 0 = ((0 : ℕ) : ℤ) := by simp
    simp only [InfiniteLattice.linkMod, InfiniteLattice.siteMod] at h1
    rw [e1, e2, TwoSliceBridge.finMod_natCast hlt, TwoSliceBridge.finMod_natCast (Nat.succ_pos M)] at h1
    exact h0.ne' h1
  have hval : PeriodicState.torusObs M (linkGap L' 0 ((0 : Fin 4), (0 : GibbsSpec.ISite))) (spike M g)
      = WilsonAction.wilsonDensity g := by
    show WilsonAction.wilsonDensity
        ((spike M g (InfiniteLattice.linkMod M ((0 : Fin 4), (0 : GibbsSpec.ISite))))⁻¹
          * spike M g (InfiniteLattice.linkMod M ((0 : Fin 4), lineSite 0 (0 : GibbsSpec.ISite) (L' : ℤ))))
      = _
    rw [spike, spike, if_neg hne, if_pos rfl, mul_one, RectWilson.wilsonDensity_inv]
  show 0 < ReflectPositive.EW (d := 4) (n := M + 1) N β
    (PeriodicState.torusObs M (linkGap L' 0 ((0 : Fin 4), (0 : GibbsSpec.ISite))))
  unfold ReflectPositive.EW
  have hb : ∀ W : WilsonHypercubic.Link 4 (M + 1) → SUN.SU N,
      |PeriodicState.torusObs M (linkGap (N := N) L' 0 ((0 : Fin 4), (0 : GibbsSpec.ISite))) W| ≤ 2 := by
    intro W
    set X := ((InfiniteLattice.pullback M W) ((0 : Fin 4), (0 : GibbsSpec.ISite)))⁻¹
      * (InfiniteLattice.pullback M W) ((0 : Fin 4), lineSite 0 (0 : GibbsSpec.ISite) (L' : ℤ)) with hX
    have a0 := WilsonAction.wilsonDensity_nonneg hN X
    have a1 := WilsonAction.wilsonDensity_le_two hN X
    show |WilsonAction.wilsonDensity X| ≤ 2
    exact abs_le.mpr ⟨by linarith, a1⟩
  refine expect_pos_of_continuous hN _ β
    ((linkGap L' 0 ((0 : Fin 4), (0 : GibbsSpec.ISite))).continuous.comp
      (InfiniteLattice.continuous_pullback (m := M)))
    (fun W => WilsonAction.wilsonDensity_nonneg hN _) hb (spike M g) ?_
  rw [hval]; exact hg

/-- **The measured period of the torus state is its extent** (`N ≥ 2`). DERIVED: `2` the least rank; `1` the
successor. -/
theorem measPeriod_torusState (hN : N ≠ 0) (hN2 : 2 ≤ N) (M : ℕ) (β : ℝ) :
    measPeriod (PeriodicState.torusState hN M β) = M + 1 :=
  SubstrateFluxRead.measPeriod_eq (SubstrateFluxRead.torusState_isPeriod hN M β)
    fun _ h0 hlt hP => (torusState_linkGap_pos hN hN2 M β h0 hlt).ne' (hP.2 0 _)

/-- **The period tie on the Wilson family** (`N ≥ 2`, `n ≥ 1`): `measPeriod (capR hN β n 0) = n`.
DERIVED: `2` the least rank; `1` the least side; `0` the step. -/
theorem measPeriod_capR (hN : N ≠ 0) (hN2 : 2 ≤ N) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    measPeriod (capR hN β n 0) = n := by
  rw [capR_zero hN β hn, measPeriod_torusState hN hN2]
  omega

/-- **On the Wilson family the read seed is the measured seed** (`N ≥ 2`). DERIVED: `2` the least rank and
the least side; `0` the threshold of the eventual coupling. -/
theorem sectorSeedRead_capR_iff [NeZero N] (hN : N ≠ 0) (hN2 : 2 ≤ N) :
    SectorSeedRead hN (capR hN) ↔ SectorSeedMeasured hN := by
  refine ⟨sectorSeedMeasured_of_readR hN, fun h => ?_⟩
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hm, n, hp, hn2, hnm, hcl⟩ := hβS
  have he := FluxDuality.even_of_pow2 hp hn2
  exact ⟨hm, n, hp, hn2, hnm, measPeriod_capR hN hN2 β (by omega), fun i =>
    ⟨(fluxReadOf_iff hβ (capturesReadTorus_capR hN β hβ n hn2 he i)).mpr (hcl i).1,
      (defectReadOf_iff hβ (capturesReadTorus_capR hN β hβ n hn2 he i)).mpr (hcl i).2⟩⟩

/-! ## 7. The strong-coupling witness at every step -/

/-- **Both reads hold on the Wilson capture of every step at strong coupling.** DERIVED: `65536 = 2^{16}`;
`4 + N⁶`, `N³/2`, `2` from `sectors_strong`; `3` the spatial directions of a time slice, `N³ = |Z_N³|`;
`6 = 2 · 3`, `N⁶` the square of `N³`. -/
theorem reads_strong_rect [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n)
    (hδ : (4 + (N : ℝ) ^ 6) * (β * StrongFiniteSize.strongBound n) ≤ 2) (i : Fin 4) {ε : ℝ}
    (hεf : (N : ℝ) ^ 3 * (β * StrongFiniteSize.strongBound n) / 2 ≤ ε)
    (hεd : 2 * (β * StrongFiniteSize.strongBound n) ≤ ε) :
    FluxReadOf (capR hN β n i) n i ε ∧ DefectReadOf (capR hN β n i) n i ε := by
  obtain ⟨hf, hd⟩ := SubstrateFluxRead.sectors_strong (N := N) hβ0 hβ hn he hδ i
  exact ⟨(fluxReadOf_iff hβ0 (twoSliceLaw_rectState hN hβ0 hn he i)).mpr (hf.trans hεf),
    (defectReadOf_iff hβ0 (twoSliceLaw_rectState hN hβ0 hn he i)).mpr (hd.trans hεd)⟩

/-- **At strong coupling both reads hold on every step's Wilson capture at `1/80000` at every large even
side.** DERIVED: `2` the least side; `1/80000` the threshold; `1/65536` the coupling ceiling of
`reads_strong_rect`, `65536 = 2^{16}`. -/
theorem eventually_reads_strong_rect [NeZero N] (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ i : Fin 4,
      FluxReadOf (capR hN β n i) n i (1 / 80000) ∧ DefectReadOf (capR hN β n i) n i (1 / 80000) := by
  have h1 := SubstrateFluxRead.eventually_sector_condition (N := N) β
  have h2 := (tendsto_order.mp (SubstrateFluxRead.tendsto_fluxBound (N := N) β)).2 (1 / 80000)
    (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, 2 * (β * StrongFiniteSize.strongBound n) < 1 / 80000 := by
    have h := (StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul 2
    rw [mul_zero, mul_zero] at h
    exact (tendsto_order.mp h).2 _ (by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2] with n hn1 hn2 hn3 hn4 he i
  exact reads_strong_rect hN hβ0 hβ hn4 he hn1 i hn2.le hn3.le

end MassGap.RectTorusState

end

#print axioms MassGap.RectTorusState.rectState
#print axioms MassGap.RectTorusState.rectState_cubic
#print axioms MassGap.RectTorusState.corrNumR
#print axioms MassGap.RectTorusState.rectState_winF
#print axioms MassGap.RectTorusState.Zc_pairR
#print axioms MassGap.RectTorusState.rectState_pairObs
#print axioms MassGap.RectTorusState.twoSliceLaw_rectState
#print axioms MassGap.RectTorusState.capturesReadTorus_capR
#print axioms MassGap.RectTorusState.capR_zero
#print axioms MassGap.RectTorusState.sectorSeedMeasured_of_readR
#print axioms MassGap.RectTorusState.torusState_linkGap_pos
#print axioms MassGap.RectTorusState.measPeriod_torusState
#print axioms MassGap.RectTorusState.measPeriod_capR
#print axioms MassGap.RectTorusState.sectorSeedRead_capR_iff
#print axioms MassGap.RectTorusState.reads_strong_rect
#print axioms MassGap.RectTorusState.eventually_reads_strong_rect
