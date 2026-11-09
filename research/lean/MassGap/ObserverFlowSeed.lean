import Mathlib
import MassGap.ObserverRunSeed
import MassGap.TorusIdentify
import MassGap.PeriodicContent
import MassGap.HeatBath

/-!
# MassGap.ObserverFlowSeed — the run seed on the observer's torus readings, bare and flowed

`ObserverRunSeed.obsRunSeedW_iff` makes `WDeltaRun.RunSeed N` a weighted budget on the doubling change of
`boxRead N n β = meanAction/n⁴`, read on `RectWilson.sysR`. This module puts that reading on the observer's
state, `PeriodicState.torusState`, defines the same budget on the observer's flowed reading, and isolates the
one comparison between the two as a named hypothesis.

## 1. The bridge: `boxRead` is the torus state's energy at one site (proved)

* `bareRead hN n β = ∑_{p ∈ Fin 4 × Fin 4} torusState hN (n − 1) β (plaqField (p, 0))`: the plaquette
  densities of every ordered plane at the origin, read in the periodic Gibbs state of side `n` on `ℤ⁴`
  observables. The diagonal planes `(μ, μ)` have holonomy `1` and read `0`; no statement here uses it.
* `torusState_plaqField_site`: the reading at the site `x` equals the reading at the origin
  (`transObs_plaqField` and `ContinuumField.state_transObs` with `PeriodicState.torusState_shift`).
* `meanAction_eq_torus`: `meanAction N (fun _ => M + 1) β = (M + 1)⁴ · bareRead hN (M + 1) β`
  (`TorusIdentify.sysR_cubic`, `WilsonAnalytic.expect_finset_sum`, `PeriodicContent.torusObs_iplaqObs`
  at the lift `HeatBath.liftSite`, and `torusState_plaqField_site`).
* **`boxRead_eq_bareRead`**: `boxRead N n β = bareRead hN n β` at `n ≠ 0`, and
  `finiteSize_eq_bareDelta`: `EnergySeed.finiteSize N n β = bareDelta hN n β`, the doubling change
  `16 n⁴ (bareRead (2n) − bareRead n)`.

## 2. The flowed reading and the flowed seed (defined)

* `flowRead hN W k n β`: `bareRead` with each plaquette density replaced by its flowed field
  `W.fieldMap k (plaqField (p, 0))`, at the origin. `ConfFlow` carries no translation covariance, so the
  reading is taken at the origin and is not identified with a box average.
* `flowDelta hN W k n β = 16 n⁴ (flowRead (2n) − flowRead n)`.
* `Budget β δ g`: `Φ 0 = 0`, `Φ β ≤ δ`, `Φ' = φ` on `[0, β]`, `g ≤ φ` on `[0, β)`. `ObserverRunSeed.ZoomSelfW`
  is `Budget β (1/1000)` of the bare change (`zoomSelfW_of_budget`); `budget_add` adds budgets.
* `InWin N C β n`: `n` a power of two, `n ≥ 2`, `C/2 < n · aRun N β ≤ C`. This is `RunSeed`'s window with the
  lower edge `C/2` added, so the side is within a factor `2` of `C/a`.
* **`ObsRunSeedFlowW hN W κ C δ`**: eventually in `β`, some `n` in the window has the flowed doubling change
  within a budget `δ`, at the step `κ β`. `κ : ℝ → ℕ` is the observer's step at coupling `β`.

## 3. The comparison (named hypothesis) and the reduction (proved)

* **`FlowEnergyComp hN W κ C K η`**: eventually in `β`, at every side `n` in the window, the excess
  `bareDelta − K · flowDelta` is within a budget `η` over the couplings `[0, β]`.
* **`runSeed_of_flowSeed`**: `0 < C`, `0 ≤ K`, `K δ + η ≤ 1/1000`, `ObsRunSeedFlowW hN W κ C δ` and
  `FlowEnergyComp hN W κ C K η` give `WDeltaRun.RunSeed N`.
* At the unit (`ConfFlow.identity`): `flowRead_identity` (the flowed reading is the bare one),
  `flowEnergyComp_identity` (the comparison holds with `K = 1`, `η = 0`), and `runSeed_of_identitySeed`.

## Analysis of the comparison (argued, not declarations)

* Direction. `FlowEnergyComp` bounds the bare change by the flowed one. The bare plaquette is not a function
  of the flowed fields, so this is the direction no locality argument supplies. The converse direction (the
  flowed change bounded by bare changes of observables within the flow's reach) follows from locality and
  is not what `RunSeed` consumes.
* At `K = 0` the comparison is `Budget β η` of the bare change itself: with `η = 1/1000` it is the bare seed on
  the window, a restatement. The content is `K > 0` with `η` below `1/1000 − K δ`.
* Free massive field (Gaussian action `β S`). `⟨S⟩` is the mode count over `2β` at every side, so the bare
  doubling change is `0` at every coupling and the defect is constant in `β`. The flowed change is the image
  sum `∑_{w ≠ 0}` of the heat kernel at `w L`, of relative size `e^{−L²/(8t)}`, `√(8t)` the flow radius, and
  it is negative, `flowDelta(x) = −c_n/x` with `c_n > 0`. The Gaussian test meets the budget only at `K = 0`:
  for `K > 0` the excess `K c_n/x` is not integrable at `x → 0`, because the Gaussian has no compact
  strong-coupling end. So the test does not inform the Wilson case, where the plaquette density lies in
  `[0, 2]` and the excess stays bounded near `0`.
* Scaling regime. At fixed step `κ β` the flow's lattice reach is fixed, so its physical reach at `x < β`
  is `(reach/n) · L(x)` with `L(x) = n · aRun N x ≥ L(β) > C/2`: the ratio of reach to side is the same at
  every coupling below `β`. The bare change is `(−d log a/dx) · L ∂_L f(L)` of the physical free-energy
  density `f`, the flowed change `16 L⁴` times the change of the flowed energy density; `−d log a/dx` tends
  to a constant and both tend to functions of `L m` and `r/L` alone. A constant `K` fixed before `β`, with
  `n ≈ C/a(β)` growing, then meets a ratio with a limit; it is not the pattern of a constant fixed before a
  growing quantity, provided the ratio is bounded over `L m ≥ C m/2`. Both changes decay like the lightest
  wrapping state at large `L m`. In the strong-coupling part of `[0, β)` both are exponentially small in `n`
  (wrapping surfaces of area `∝ n`), so their contribution to `η` vanishes as `n` grows.
* What `η` must carry: sign crossings (the two changes need not change sign at the same coupling) and the
  part of the bare change not seen by the flowed density at reach `r` (higher-dimension operators in the
  small-flow-time expansion), of relative size `(r/C)²`. Both are bounded by a fraction of the bare budget
  only when `C ≫ r`.

## What is open

`ObsRunSeedFlowW` (the observer's flowed seed) and `FlowEnergyComp` (the comparison) for a `ConfFlow` of
physical reach `r` with `C ≫ r`, `K > 0`, `η < 1/1000 − K δ`. Neither is proved for any non-identity flow.

DERIVED (module-wide): `4` the dimension; `16 = 2⁴` the copies of the side-`n` box in the side-`2n` box;
`2` the doubling, the least side and the window's lower edge `C/2`; `1/1000` the sharp seed; `0` the
origin, the lower coupling and the excluded colour count; `1` the successor writing the extent and the unit
comparison constant.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverFlowSeed

open Real Filter Set
open MassGap MassGap.ObserverRunSeed MassGap.EffectiveCoupling MassGap.EnergySeed
open MassGap.PeriodicState MassGap.ContinuumField MassGap.ContinuumFlow MassGap.ObserverEnergyMoments

variable {N : ℕ}

/-! ## 1. The bridge -/

/-- A unit step then a translation is a translation then the unit step. DERIVED: `4` the dimension;
`1` the unit step. -/
theorem ishift_add (μ : Fin 4) (y x : MassGap.GibbsSpec.ISite) :
    MassGap.GibbsSpec.ishift μ y + x = MassGap.GibbsSpec.ishift μ (y + x) := by
  funext i
  by_cases h : i = μ
  · subst h
    simp only [MassGap.GibbsSpec.ishift, Pi.add_apply, Function.update_self]
    ring
  · simp only [MassGap.GibbsSpec.ishift, Pi.add_apply, Function.update_of_ne h]

/-- The holonomy of a plaquette on a translated configuration is the holonomy of the translated plaquette.
DERIVED: no numeral. -/
theorem ihol_transConf (q : MassGap.GibbsSpec.IPlaq) (x : MassGap.GibbsSpec.ISite)
    (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.GibbsSpec.ihol q (transConf x U) = MassGap.GibbsSpec.ihol (q.1, q.2 + x) U := by
  rw [MassGap.PlaneVariance.ihol_eq_head_mul, MassGap.PlaneVariance.ihol_eq_head_mul]
  show U (q.1.1, q.2 + x) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2 + x)
      * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2 + x))⁻¹ * (U (q.1.2, q.2 + x))⁻¹)) = _
  rw [ishift_add, ishift_add]

/-- **Translating a plaquette density moves its plaquette.** DERIVED: no numeral. -/
theorem transObs_plaqField (p : Fin 4 × Fin 4) (y x : MassGap.GibbsSpec.ISite) :
    transObs x (plaqField (N := N) (p, y)).1 = (plaqField (N := N) (p, y + x)).1 := by
  ext U
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (p, y) (transConf x U))
    = MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (p, y + x) U)
  rw [ihol_transConf]

/-- **The torus state reads the same plaquette density at every site** (translation invariance).
DERIVED: `0` the origin and the excluded colour count. -/
theorem torusState_plaqField_site (hN : N ≠ 0) (M : ℕ) (β : ℝ) (p : Fin 4 × Fin 4)
    (x : MassGap.GibbsSpec.ISite) :
    torusState hN M β (plaqField (N := N) (p, x)).1 = torusState hN M β (plaqField (N := N) (p, 0)).1 := by
  have h := state_transObs (ν := torusState hN M β) (fun τ F => torusState_shift hN M β τ F) x
    (plaqField (N := N) (p, 0)).1
  rw [transObs_plaqField, zero_add] at h
  exact h

/-- **The observer's bare energy reading**: the plaquette densities of the ordered planes at the origin in
the periodic Gibbs state of side `n`. DERIVED: `4` the dimension; `1` the successor writing the extent;
`0` the origin. -/
def bareRead (hN : N ≠ 0) (n : ℕ) (β : ℝ) : ℝ :=
  ∑ p : Fin 4 × Fin 4, torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1

/-- **The mean action on the cubic box is the site count times the torus reading at the origin.**
DERIVED: `4` the dimension; `1` the successor; `2` the bound on a plaquette density. -/
theorem meanAction_eq_torus (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    meanAction N (fun _ => M + 1) β = ((M + 1 : ℕ) : ℝ) ^ 4 * bareRead hN (M + 1) β := by
  have h1 : meanAction N (fun _ => M + 1) β
      = (MassGap.WilsonLattice.wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.WilsonAction.wilsonDensity (N := N))).expect
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) β
          (fun U => ∑ q ∈ Finset.univ, MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q U) := by
    unfold meanAction
    rw [MassGap.TorusIdentify.sysR_cubic]
    rfl
  have h2 : ∀ q : MassGap.WilsonHypercubic.Plaq 4 (M + 1),
      (MassGap.WilsonLattice.wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.WilsonAction.wilsonDensity (N := N))).expect
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) β
          (MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q)
        = torusState hN M β (plaqField (N := N) (q.1, 0)).1 := by
    intro q
    rw [← torusState_plaqField_site hN M β q.1 (MassGap.HeatBath.liftSite M q.2)]
    have hq : MassGap.InfiniteLattice.plaqMod M (q.1, MassGap.HeatBath.liftSite M q.2) = q := by
      show (q.1, MassGap.InfiniteLattice.siteMod M (MassGap.HeatBath.liftSite M q.2)) = q
      rw [MassGap.HeatBath.siteMod_liftSite]
    have ht : torusObs M (plaqField (N := N) (q.1, MassGap.HeatBath.liftSite M q.2)).1
        = MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q := by
      funext W
      show torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N)
          (q.1, MassGap.HeatBath.liftSite M q.2)) W = _
      rw [MassGap.PeriodicContent.torusObs_iplaqObs, hq]
    show _ = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
      (torusObs M (plaqField (N := N) (q.1, MassGap.HeatBath.liftSite M q.2)).1)
    rw [ht]
    rfl
  have hb : ∀ (q : MassGap.WilsonHypercubic.Plaq 4 (M + 1)) U,
      |MassGap.WilsonReal.wilsonPlaqObs (N := N)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q U| ≤ 2 := by
    intro q U
    have h0 := MassGap.WilsonReal.wilsonPlaqObs_nonneg hN
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q U
    have h2' := MassGap.WilsonReal.wilsonPlaqObs_le_two hN
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q U
    exact abs_le.mpr ⟨by linarith, h2'⟩
  rw [h1, MassGap.WilsonAnalytic.expect_finset_sum hN _ β _
    (fun q => MassGap.WilsonReal.measurable_wilsonPlaqObs _ q) 2 hb Finset.univ]
  rw [Finset.sum_congr rfl (fun q _ => h2 q), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  unfold bareRead
  simp only [Nat.add_sub_cancel]
  congr 1
  simp [Fintype.card_fin]

/-- **The bridge**: `boxRead N n β = bareRead hN n β` at `n ≠ 0`.
DERIVED: `4` the dimension; `0` the excluded side; `1` the successor. -/
theorem boxRead_eq_bareRead (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    boxRead N n β = bareRead hN n β := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  unfold boxRead
  rw [meanAction_eq_torus hN M β]
  have h : ((M + 1 : ℕ) : ℝ) ^ 4 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ h]

/-- The bare doubling change on the torus readings. DERIVED: `16 = 2⁴`; `2` the doubling; `4` the
dimension. -/
def bareDelta (hN : N ≠ 0) (n : ℕ) (β : ℝ) : ℝ :=
  16 * (n : ℝ) ^ 4 * (bareRead hN (2 * n) β - bareRead hN n β)

/-- **`finiteSize` is the bare doubling change of the torus reading.** DERIVED: `2` the doubling; `0` the
excluded side. -/
theorem finiteSize_eq_bareDelta (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) (β : ℝ) :
    finiteSize N n β = bareDelta hN n β := by
  rw [finiteSize_eq_boxRead hn, boxRead_eq_bareRead hN hn, boxRead_eq_bareRead hN (by omega)]
  rfl

/-! ## 2. The flowed reading and the flowed seed -/

/-- **The observer's flowed energy reading**: `bareRead` with each plaquette density flowed by `W` at step
`k`. DERIVED: `4` the dimension; `1` the successor; `0` the origin. -/
def flowRead (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) : ℝ :=
  ∑ p : Fin 4 × Fin 4, torusState hN (n - 1) β (W.fieldMap k (plaqField (N := N) (p, 0))).1

/-- The flowed doubling change. DERIVED: `16 = 2⁴`; `2` the doubling; `4` the dimension. -/
def flowDelta (hN : N ≠ 0) (W : ConfFlow N) (k n : ℕ) (β : ℝ) : ℝ :=
  16 * (n : ℝ) ^ 4 * (flowRead hN W k (2 * n) β - flowRead hN W k n β)

/-- **A budget**: `Φ 0 = 0`, `Φ β ≤ δ`, `Φ' = φ` on `[0, β]`, `g ≤ φ` on `[0, β)`.
DERIVED: `0` the lower coupling. -/
def Budget (β δ : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ Φ φ : ℝ → ℝ, Φ 0 = 0 ∧ Φ β ≤ δ ∧ (∀ x ∈ Icc (0 : ℝ) β, HasDerivAt Φ (φ x) x) ∧
    ∀ x ∈ Ico (0 : ℝ) β, g x ≤ φ x

/-- **Budgets add**: `K · (budget δ for g) + (budget η for e)` is a budget `K δ + η` for `K g + e`.
DERIVED: `0` the sign of `K`. -/
theorem budget_add {β δ η K : ℝ} {g e : ℝ → ℝ} (hK : 0 ≤ K) (h1 : Budget β δ g) (h2 : Budget β η e) :
    Budget β (K * δ + η) (fun x => K * g x + e x) := by
  obtain ⟨Φ, φ, h0, hβ, hd, hg⟩ := h1
  obtain ⟨E, ψ, e0, eβ, ed, he⟩ := h2
  refine ⟨fun x => K * Φ x + E x, fun x => K * φ x + ψ x, by simp [h0, e0], ?_,
    fun x hx => ((hd x hx).const_mul K).add (ed x hx), fun x hx => ?_⟩
  · have := mul_le_mul_of_nonneg_left hβ hK
    show K * Φ β + E β ≤ K * δ + η
    linarith
  · have := mul_le_mul_of_nonneg_left (hg x hx) hK
    have := he x hx
    show K * g x + e x ≤ K * φ x + ψ x
    linarith

/-- **A budget for a larger function and a smaller bound is a budget.** DERIVED: `0` the lower coupling. -/
theorem budget_mono {β δ δ' : ℝ} {g g' : ℝ → ℝ} (h : Budget β δ g) (hle : ∀ x ∈ Ico (0 : ℝ) β, g' x ≤ g x)
    (hδ : δ ≤ δ') : Budget β δ' g' := by
  obtain ⟨Φ, φ, h0, hβ, hd, hg⟩ := h
  exact ⟨Φ, φ, h0, hβ.trans hδ, hd, fun x hx => (hle x hx).trans (hg x hx)⟩

/-- **`ZoomSelfW` is the sharp budget for the bare change.** DERIVED: `1/1000` the sharp seed; `0` the
excluded side. -/
theorem zoomSelfW_of_budget (hN : N ≠ 0) {n : ℕ} (hn : n ≠ 0) {β : ℝ}
    (h : Budget β (1 / 1000) (bareDelta hN n)) : ZoomSelfW N n β := by
  obtain ⟨Φ, φ, h0, hβ, hd, hg⟩ := h
  refine ⟨Φ, φ, h0, hβ, hd, fun x hx => ?_⟩
  rw [← finiteSize_eq_boxRead hn, finiteSize_eq_bareDelta hN hn]
  exact hg x hx

/-- **The window**: `n` a power of two, `n ≥ 2`, `C/2 < n · aRun N β ≤ C`. DERIVED: `2` the least side
and the lower edge. -/
def InWin (N : ℕ) (C β : ℝ) (n : ℕ) : Prop :=
  PeriodicState.IsPow2 n ∧ 2 ≤ n ∧ C / 2 < (n : ℝ) * AsymptoticScaling.aRun N β ∧
    (n : ℝ) * AsymptoticScaling.aRun N β ≤ C

/-- **The observer's flowed run seed**: eventually in `β`, some side in the window has its flowed doubling
change within the budget `δ`, at the observer's step `κ β`. DERIVED: no numeral. -/
def ObsRunSeedFlowW (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∃ n : ℕ, InWin N C β n ∧ Budget β δ (flowDelta hN W (κ β) n)

/-! ## 3. The comparison and the reduction -/

/-- **The bare–flowed comparison**: eventually in `β`, at every side in the window, the excess
`bareDelta − K · flowDelta` is within a budget `η`. At `K = 0` this is `Budget β η` of the bare change at
every side in the window, which restates the bare seed when `η ≤ 1/1000`; the content is `K > 0`.
DERIVED: no numeral. -/
def FlowEnergyComp (hN : N ≠ 0) (W : ConfFlow N) (κ : ℝ → ℕ) (C K η : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, InWin N C β n →
    Budget β η (fun x => bareDelta hN n x - K * flowDelta hN W (κ β) n x)

/-- **The run seed from the flowed seed and the comparison.**
DERIVED: `1/1000` the sharp seed; `0` the signs and the excluded side. -/
theorem runSeed_of_flowSeed (hN : N ≠ 0) {W : ConfFlow N} {κ : ℝ → ℕ} {C K δ η : ℝ} (hC : 0 < C)
    (hK : 0 ≤ K) (hsum : K * δ + η ≤ 1 / 1000) (hS : ObsRunSeedFlowW hN W κ C δ)
    (hc : FlowEnergyComp hN W κ C K η) : WDeltaRun.RunSeed N := by
  refine ⟨C, hC, ?_⟩
  filter_upwards [hS, hc, eventually_ge_atTop (0 : ℝ)] with β ⟨n, hw, hb⟩ hcb hβ
  obtain ⟨hp, h2, hlo, hna⟩ := hw
  have hB : Budget β (1 / 1000) (bareDelta hN n) :=
    budget_mono (budget_add hK hb (hcb n ⟨hp, h2, hlo, hna⟩))
      (fun x _ => by
        show bareDelta hN n x
          ≤ K * flowDelta hN W (κ β) n x + (bareDelta hN n x - K * flowDelta hN W (κ β) n x)
        linarith) hsum
  exact ⟨n, hp, h2, hna, defectW_le_of_zoomSelfW hN (by omega) hβ (zoomSelfW_of_budget hN (by omega) hB)⟩

/-! ## 4. The unit: the identity flow -/

/-- **The identity flow reads the bare field.** DERIVED: no numeral. -/
theorem fieldMap_identity (k : ℕ) (O : MassGap.ContinuumField.LField (MassGap.SUN.SU N)) :
    ((ConfFlow.identity N).fieldMap k O).1 = O.1 :=
  ContinuousMap.ext fun _ => rfl

/-- **At the identity flow the flowed reading is the bare reading.** DERIVED: no numeral. -/
theorem flowRead_identity (hN : N ≠ 0) (k n : ℕ) (β : ℝ) :
    flowRead hN (ConfFlow.identity N) k n β = bareRead hN n β := by
  unfold flowRead bareRead
  simp only [fieldMap_identity]

/-- **At the identity flow the comparison holds with `K = 1`, `η = 0`.**
DERIVED: `1` the unit constant; `0` the slack. -/
theorem flowEnergyComp_identity (hN : N ≠ 0) (κ : ℝ → ℕ) (C : ℝ) :
    FlowEnergyComp hN (ConfFlow.identity N) κ C 1 0 :=
  Eventually.of_forall fun β n _ => ⟨fun _ => 0, fun _ => 0, rfl, le_rfl,
    fun x _ => hasDerivAt_const x (0 : ℝ), fun x _ => by
      show bareDelta hN n x - 1 * flowDelta hN (ConfFlow.identity N) (κ β) n x ≤ 0
      unfold flowDelta
      rw [flowRead_identity, flowRead_identity]
      unfold bareDelta
      linarith⟩

/-- **At the identity flow the flowed seed at the sharp budget is a run seed.**
DERIVED: `1/1000` the sharp seed; `0` the sign. -/
theorem runSeed_of_identitySeed (hN : N ≠ 0) {κ : ℝ → ℕ} {C : ℝ} (hC : 0 < C)
    (hS : ObsRunSeedFlowW hN (ConfFlow.identity N) κ C (1 / 1000)) : WDeltaRun.RunSeed N :=
  runSeed_of_flowSeed hN hC zero_le_one (by norm_num) hS (flowEnergyComp_identity hN κ C)

end MassGap.ObserverFlowSeed

end

#print axioms MassGap.ObserverFlowSeed.ishift_add
#print axioms MassGap.ObserverFlowSeed.ihol_transConf
#print axioms MassGap.ObserverFlowSeed.transObs_plaqField
#print axioms MassGap.ObserverFlowSeed.torusState_plaqField_site
#print axioms MassGap.ObserverFlowSeed.meanAction_eq_torus
#print axioms MassGap.ObserverFlowSeed.boxRead_eq_bareRead
#print axioms MassGap.ObserverFlowSeed.finiteSize_eq_bareDelta
#print axioms MassGap.ObserverFlowSeed.budget_add
#print axioms MassGap.ObserverFlowSeed.budget_mono
#print axioms MassGap.ObserverFlowSeed.zoomSelfW_of_budget
#print axioms MassGap.ObserverFlowSeed.runSeed_of_flowSeed
#print axioms MassGap.ObserverFlowSeed.fieldMap_identity
#print axioms MassGap.ObserverFlowSeed.flowRead_identity
#print axioms MassGap.ObserverFlowSeed.flowEnergyComp_identity
#print axioms MassGap.ObserverFlowSeed.runSeed_of_identitySeed
