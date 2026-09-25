import Mathlib
import MassGap.ContinuumClay
import MassGap.HeatBathGapDecay
import MassGap.HeatBathLocal
import MassGap.BoxPatch
import MassGap.ChiForest

noncomputable section

/-!
# MassGap.ClayRoutes — the continuum Clay statement from each route to the uniform physical gap

`ContinuumClay.continuum_gap_nontrivial` concludes, at every dyadic step `m`, that the reconstructed
continuum transfer data `ContinuumClay.contD hN Z τ hZ hB m` is `ContinuumClay.GappedAt` a rate of
physical mass at least `c/L` and is `ContinuumClay.NontrivialVacuum`. `ClayContinuum hN Z τ hZ hB L`
names that conclusion. Its requirement M input is `WeakCouplingWindow.FixedWindowDecay τ 0 hN L`;
this module reaches it by two routes and assembles each into `ClayContinuum`.

* `clay_continuum_of_fixedWindowDecay`: the capstone with M as the single Prop `FixedWindowDecay`.
* `clay_continuum_of_irGap`: the IR gap at `β₀` at a named rate `M₀` and the UV step below `M₀`.
  `UVBelowIR τ p hN β₀ βUV M₀` states the UV step against one rate: a non-negative loss function with a
  budget below `M₀` along the dyadic tower from `β₀`, and the UV step from `βUV` on.
* `clay_continuum_of_boxPatchGap`: the finite-size route at the explicit rate of the box. Its middle
  is `BoxPatch.BoxPatchGap` at one coupling, which gives the IR gap at
  `HeatBathLocal.boxRate N β₀ n γ = min(boxKnabe n γ, 1)/(508 · aRun N β₀)`
  (`HeatBathLocal.irGapAt_boxRate`, `HeatBathLocal.boxRate_eq`); its UV input is `UVBelowIR` at that rate.
* `clay_continuum_of_chiForest`: the `χ²` route. Along a sequence of observer laws `m` with
  `ChiForest.ChiForest m δ`, a class of observable pairs indexed by `S`, with window pairs
  `(aw i, bw i)` and lag-zero pairs `(a0 i, b0 i)`, has step-`n` connected pairings `stepConn` and
  limit pairings `limConn`. `ClassKappa` asks the variance-relative remainder of
  `ChiForest.ChiForest.abs_conn_sub_le` to be at most `κ` times the step-`n` lag-zero pairing, with
  one `κ` for the class; `LimitFactor` asks the limit to decay by `q₀ < 1` at the window. Then
  `eventually_window_factor` gives every `q > q₀` as a step factor, uniformly on the class, for all
  large `n` (`ChiForest.eventually_factor_of_relative`). The forest runs along dyadic steps of
  infinite-volume observer laws; `FixedWindowDecay` reads periodic tori along
  `PeriodicState.periodicUltra` at every large real `β` on `gaugeInvHalfSpaceAlg`. `ChiCarrierBridge`
  is the carrier match between the two, and `fixedWindowDecay_of_chiForest` proves
  `FixedWindowDecay` from the forest data and the bridge.

## Open inputs of the Clay continuum statement, by requirement

Fixed data: a colour count `2 ≤ N`, a field-strength factor `Z` with its reflection invariance
`hZ`, a time direction `τ : Fin 4`, a window `0 < L`, a field `O` and a radial profile `G`.

* **E** — `ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)`: for every family and every
  `d > 0`, one constant bounding, eventually in the step, the renormalised lattice Schwinger function
  of every dyadic translate of the family whose supports are pairwise `d`-separated.
* **N** — `ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
  (fun p q => G (ContinuumNontrivial.eDist p q))`: the renormalised lattice kernel of `O` converging
  to `G(|p − q|)` uniformly on every separated box `ContinuumNontrivial.sepBoxSet d R`, `d > 0`.
* **Y** — `ShortDistanceY.AFShortDistance G`: `r⁸ · G(r) · (log r)² → C` as `r → 0⁺`, some `C > 0`.
* **M-middle**, finite-size route — `BoxPatch.BoxPatchGap hN β₀ n γ` (`2 ≤ n`,
  `(40n − 36)/n² < γ`, and the local gap `γ` at every box patch operator, uniformly in the extent),
  at one coupling `0 < β₀`. Its companion `HeatBathGapDecay.HeatBathLocality τ 0 hN β₀` (local
  commutation, separated supports, norm bounds, and the ergodic limit
  `HeatBathGapDecay.ErgodicLimit` of the lazy heat bath reproducing the torus pairing) is proved at
  every coupling (`HeatBathLocal.heatBathLocality_holds`), so `clay_continuum_of_boxPatchGap`
  carries `BoxPatchGap` alone.
* **M-UV**, finite-size route — `UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ)` at some
  `βUV ≤ β₀`: the block step `UVIRSplit.UVLossStep τ 0 hN βUV ε` with non-negative losses and a budget
  `UVIRSplit.LossBudget ε (aRun N β₀) E` below the box's rate
  `min(boxKnabe n γ, 1)/(508 · aRun N β₀)` (`HeatBathLocal.boxRate_eq`).
* **M**, `χ²` route, middle and UV together — the producer `ChiForest.ChiForest m δ` of the
  observer laws, `ClassKappa m S aw bw a0 b0 κ`, `LimitFactor m S aw bw a0 b0 q₀`, and the carrier
  bridge `ChiCarrierBridge τ 0 hN L m S aw bw a0 b0`.
* **M**, as one Prop — `WeakCouplingWindow.FixedWindowDecay τ 0 hN L`; equivalently
  `ZoomStep.LeftoverInvariant τ 0 hN L` (`ZoomStep.leftoverInvariant_iff_fixedWindowDecay`), and,
  under `∀ᶠ β in atTop, ConstantPhysics.MovesComplement (periodicGaugeInvData τ 0 hN β)`,
  `ConstantPhysics.MassDominates τ 0 hN (aRun N)` (`ConstantPhysics.fixedWindowDecay_iff_massDominates`).

Outside the statement: rotation invariance off the hypercubic group,
`ContinuumHypercubic.RotationOpen`; and the choice of ultrafilter behind `ContinuumSchwinger.contS`,
which `Beacon.SchwingerBeaconSep` removes on separated families
(`Beacon.tendsto_contS_atTop_of_schwingerBeaconSep`).
-/

namespace MassGap.ClayRoutes

variable {N : ℕ}

/-! ## 1. The conclusion, named -/

section Capstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **The Clay continuum conclusion at window `L`.** Some `c > 0` has, at every dyadic step `m`, the
reconstructed transfer data `ContinuumClay.contD hN Z τ hZ hB m` `ContinuumClay.GappedAt` the rate
`e^{−(c/L)·dySpacing N m}` and `ContinuumClay.NontrivialVacuum` — the conclusion of
`ContinuumClay.continuum_gap_nontrivial`.

DERIVED: `0` is the excluded colour count and the lower end of `c`; `4` in `Fin 4` is the spacetime
dimension. -/
def ClayContinuum (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) (L : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
    ContinuumClay.GappedAt (ContinuumClay.contD hN Z τ hZ hB m) (Real.exp (-(c / L) * dySpacing N m))
      ∧ ContinuumClay.NontrivialVacuum (ContinuumClay.contD hN Z τ hZ hB m)

/-- **The capstone with requirement M as one Prop.** At `2 ≤ N`, a reflection-invariant `Z`, the
separated uniform bound `hB` (E), a window `L > 0`, `WeakCouplingWindow.FixedWindowDecay τ 0 hN L`
(M), `ContinuumNontrivial.KernelConvergesSep` towards a radial `G` (N) and
`ShortDistanceY.AFShortDistance G` (Y): `ClayContinuum hN Z τ hZ hB L`
(`ContinuumClay.continuum_gap_nontrivial`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
lower end of `L`, and the reflection plane offset `p = 0` that `continuum_gap_nontrivial` reads
`FixedWindowDecay` at; `4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_of_fixedWindowDecay (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L :=
  ContinuumClay.continuum_gap_nontrivial hN2 hN Z τ hZ hB hL hW O G hconv hY

#print axioms clay_continuum_of_fixedWindowDecay

end Capstone

/-! ## 2. The finite-size route -/

section FiniteSize

open MassGap

/-- **The UV step below the rate `M₀`.** Some non-negative loss function `ε` and budget `E` have
`UVIRSplit.LossBudget ε (aRun N β₀) E`, `E < M₀` and `UVIRSplit.UVLossStep τ p hN βUV ε`: the losses of the
dyadic tower from `β₀` sum below `M₀`. The losses are non-negative: a negative loss would assert a gap
outright, and with `0 ≤ ε` the step holds on gapless families (`UVIRSplit.lossStep_of_no_gap`), so it
carries no IR content. This is the UV hypothesis of `KnabeCriterion.fixedWindowDecay_of_patchGapCheck`
at its IR rate `M₀`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the sign of the losses. -/
def UVBelowIR (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₀ βUV M₀ : ℝ) : Prop :=
  ∃ (ε : ℝ → ℝ) (E : ℝ), (∀ s, 0 ≤ ε s) ∧
    UVIRSplit.LossBudget ε (MassGap.AsymptoticScaling.aRun N β₀) E ∧
    E < M₀ ∧ UVIRSplit.UVLossStep τ p hN βUV ε

/-- **A UV step at zero budget is below every positive rate.** A non-negative loss function `ε`,
`UVIRSplit.UVLossStep τ p hN βUV ε` and `UVIRSplit.LossBudget ε (aRun N β₀) E` with `E ≤ 0` give
`UVBelowIR τ p hN β₀ βUV M₀` at every `M₀ > 0`. `LossBudget` at no terms gives `0 ≤ E`, so `E = 0`: the
degenerate, loss-free case.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the bound on `E` and the sign of
`M₀`. -/
theorem uvBelowIR_of_nonpos_budget (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV E M₀ : ℝ}
    {ε : ℝ → ℝ} (hε : ∀ s, 0 ≤ ε s) (hstep : UVIRSplit.UVLossStep τ p hN βUV ε)
    (hbud : UVIRSplit.LossBudget ε (MassGap.AsymptoticScaling.aRun N β₀) E) (hE : E ≤ 0)
    (hM₀ : 0 < M₀) :
    UVBelowIR τ p hN β₀ βUV M₀ :=
  ⟨ε, E, hε, hbud, lt_of_le_of_lt hE hM₀, hstep⟩

#print axioms uvBelowIR_of_nonpos_budget

end FiniteSize

section FiniteSizeCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **The continuum Clay statement from an IR gap and the UV step below it.** At `2 ≤ N`, `0 < L`,
`0 < β₀`, `βUV ≤ β₀`, the IR gap `UVIRSplit.IRGapAt τ 0 hN β₀ M₀` at a rate `M₀`, the UV step below it
(`UVBelowIR τ 0 hN β₀ βUV M₀`), and E, N, Y: `ClayContinuum hN Z τ hZ hB L`
(`UVIRSplit.fixedWindowDecay_of_uv_ir`, `clay_continuum_of_fixedWindowDecay`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_of_irGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV M₀ : ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hir : UVIRSplit.IRGapAt τ 0 hN β₀ M₀)
    (huv : UVBelowIR τ 0 hN β₀ βUV M₀)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L := by
  obtain ⟨ε, E, -, hbud, hEM, hstep⟩ := huv
  exact clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL
    (UVIRSplit.fixedWindowDecay_of_uv_ir τ 0 hN2 hN hL hβ₀ hUVβ₀ hbud hEM hstep hir) O G hconv hY

#print axioms clay_continuum_of_irGap

/-- **The continuum Clay statement from one box.** At `2 ≤ N`, `0 < L`, `0 < β₀`, `βUV ≤ β₀`,
`BoxPatch.BoxPatchGap hN β₀ n γ` (M-middle), the UV step below the box's rate
`HeatBathLocal.boxRate N β₀ n γ = min(boxKnabe n γ, 1)/(508 · aRun N β₀)` (`HeatBathLocal.boxRate_eq`)
from `βUV` on, the budget along the dyadic tower from `β₀` (`UVBelowIR`, M-UV), with `βUV` past the peak
`17N²/(88π²)` of `aRun N`, and E, N, Y: `ClayContinuum hN Z τ hZ hB L`. The box gives the IR gap
at that rate (`HeatBathLocal.irGapAt_boxRate`), and `clay_continuum_of_irGap` concludes.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension; `1` in
the proof is the least colour count; `17N²/(88π²)` is the peak of `aRun N` (`AsymptoticScaling.aRun`, the peak `17N²/(44π²)` of `aRunStd` at
`β_std = 2β`). CHOSEN: the scope restriction `_hpeak`, not used by the proof, keeps every coupling of the UV step where `aRun N` decreases, so each step of the tower refines the spacing. The peak lies deep in strong coupling (about `0.078` at `N = 2`); the physical crossover (Lean `β ≈ 1.1` at `N = 2`, `≈ 2.85` at `N = 3`) lies at larger `β`, inside the UV step unless `β₀` is past it. -/
theorem clay_continuum_of_boxPatchGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (huv : UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_irGap hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀
    (HeatBathLocal.irGapAt_boxRate τ 0 (by omega) hN hβ₀ hbox).2 huv O G hconv hY

#print axioms clay_continuum_of_boxPatchGap

end FiniteSizeCapstone

/-! ## 3. The `χ²` route -/

section Chi

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type*}

/-- **The step-`n` connected pairing** of `a`, `b` under the law `m n`:
`E_n[a b] − E_n a · E_n b`.

DERIVED: no numeral. -/
def stepConn (m : ℕ → MeasureTheory.Measure Ω) (n : ℕ) (a b : Ω → ℝ) : ℝ :=
  ∫ x, a x * b x ∂(m n) - (∫ x, a x ∂(m n)) * ∫ x, b x ∂(m n)

/-- **The limit connected pairing** of `a`, `b` along `m`:
`L(a b) − L(a) L(b)`, `L = ZoomForest.forestLimit m`.

DERIVED: no numeral. -/
def limConn (m : ℕ → MeasureTheory.Measure Ω) (a b : Ω → ℝ) : ℝ :=
  ZoomForest.forestLimit m (fun x => a x * b x)
    - ZoomForest.forestLimit m a * ZoomForest.forestLimit m b

/-- **A relative remainder for one pair.** `a`, `b` and `a b` are square-integrable along `m`, with
variance bounds `Va`, `Vb`, `Vab` at every step and `|forestLimit m a| ≤ A`, and at every step `n`
some `B ≥ |E_n b|` has `√Vab + B √Va + A √Vb ≤ κ · s n`: the coefficient of
`ChiForest.ChiForest.abs_conn_sub_le` is at most `κ` times the scale `s n`.

DERIVED: no numeral. -/
def RelRemainder (m : ℕ → MeasureTheory.Measure Ω) (a b : Ω → ℝ) (s : ℕ → ℝ) (κ : ℝ) : Prop :=
  ChiForest.SqIntAlong m a ∧ ChiForest.SqIntAlong m b ∧ ChiForest.SqIntAlong m (fun x => a x * b x) ∧
    ∃ Va Vb Vab A : ℝ, (∀ k, ChiForest.obsVar (m k) a ≤ Va) ∧ (∀ k, ChiForest.obsVar (m k) b ≤ Vb) ∧
      (∀ k, ChiForest.obsVar (m k) (fun x => a x * b x) ≤ Vab) ∧
      |ZoomForest.forestLimit m a| ≤ A ∧
      ∀ n : ℕ, ∃ B : ℝ, |∫ x, b x ∂(m n)| ≤ B ∧
        Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb ≤ κ * s n

/-- **THE CLASS-UNIFORM `κ`.** For every `i ∈ S`: the step-`n` lag-zero pairing
`stepConn m n (a0 i) (b0 i)` is non-negative at every `n`, and both the window pair `(aw i, bw i)`
and the lag-zero pair `(a0 i, b0 i)` have a `RelRemainder` at the scale of that lag-zero pairing,
with the one constant `κ`.

DERIVED: `0` is the sign of the lag-zero pairing. -/
def ClassKappa (m : ℕ → MeasureTheory.Measure Ω) (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ)
    (κ : ℝ) : Prop :=
  ∀ i ∈ S, (∀ n, 0 ≤ stepConn m n (a0 i) (b0 i)) ∧
    RelRemainder m (aw i) (bw i) (fun n => stepConn m n (a0 i) (b0 i)) κ ∧
    RelRemainder m (a0 i) (b0 i) (fun n => stepConn m n (a0 i) (b0 i)) κ

/-- **THE LIMIT FACTOR AT THE WINDOW.** `0 ≤ q₀ < 1` and, for every `i ∈ S`, the limit window pairing
is at most `q₀` times the limit lag-zero pairing.

DERIVED: `0` is the lower end of `q₀`; `1` is the factor the decay must beat. -/
def LimitFactor (m : ℕ → MeasureTheory.Measure Ω) (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ)
    (q₀ : ℝ) : Prop :=
  0 ≤ q₀ ∧ q₀ < 1 ∧ ∀ i ∈ S, limConn m (aw i) (bw i) ≤ q₀ * limConn m (a0 i) (b0 i)

/-- **The step pairing is within the relative remainder of the limit's.** Under
`ChiForest.ChiForest m δ` at probability laws and `RelRemainder m a b s κ`:
`|stepConn m n a b − limConn m a b| ≤ (∑' i, δ (n + i)) · κ · s n` at every `n`
(`ChiForest.ChiForest.abs_conn_sub_le`, with the tail sum non-negative by `ChiForest.ChiForest.nonneg`).

DERIVED: no numeral. -/
theorem abs_stepConn_sub_le {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {a b : Ω → ℝ} {s : ℕ → ℝ} {κ : ℝ} (hR : RelRemainder m a b s κ) (n : ℕ) :
    |stepConn m n a b - limConn m a b| ≤ (∑' i, δ (n + i)) * (κ * s n) := by
  obtain ⟨ha, hb, hab, Va, Vb, Vab, A, hVa, hVb, hVab, hA, hB⟩ := hR
  obtain ⟨B, hBn, hcoef⟩ := hB n
  have h1 := h.abs_conn_sub_le hprob ha hb hab hVa hVb hVab hA n hBn
  have hT : 0 ≤ ∑' i, δ (n + i) := tsum_nonneg (fun i => h.nonneg (n + i))
  calc |stepConn m n a b - limConn m a b|
      ≤ (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) * ∑' i, δ (n + i) := h1
    _ = (∑' i, δ (n + i)) * (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) := mul_comm _ _
    _ ≤ (∑' i, δ (n + i)) * (κ * s n) := mul_le_mul_of_nonneg_left hcoef hT

#print axioms abs_stepConn_sub_le

/-- **Every factor above the limit's is a step factor, uniformly on the class.** Under
`ChiForest.ChiForest m δ` at probability laws, `ClassKappa m S aw bw a0 b0 κ` and
`LimitFactor m S aw bw a0 b0 q₀`: for every `q > q₀`, for all large `n`, every `i ∈ S` has
`stepConn m n (aw i) (bw i) ≤ q · stepConn m n (a0 i) (b0 i)`. The tail sums `∑' i, δ (n + i)` tend
to `0` (`tendsto_sum_nat_add`), `abs_stepConn_sub_le` gives the two relative remainders, and
`ChiForest.eventually_factor_of_relative` concludes.

DERIVED: no numeral in the statement. -/
theorem eventually_window_factor {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) {q : ℝ} (hqq : q₀ < q) :
    ∀ᶠ n in atTop, ∀ i ∈ S, stepConn m n (aw i) (bw i) ≤ q * stepConn m n (a0 i) (b0 i) := by
  obtain ⟨hq0, -, hlim⟩ := hq
  have hT : Tendsto (fun n => ∑' i, δ (n + i)) atTop (𝓝 0) := by
    refine (tendsto_sum_nat_add δ).congr (fun n => ?_)
    exact tsum_congr (fun i => congrArg δ (add_comm i n))
  have hc : ∀ n, ∀ i ∈ S, stepConn m n (aw i) (bw i)
      ≤ limConn m (aw i) (bw i) + (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := by
    intro n i hi
    obtain ⟨-, hRw, -⟩ := hK i hi
    have h1 : |stepConn m n (aw i) (bw i) - limConn m (aw i) (bw i)|
        ≤ (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := abs_stepConn_sub_le h hprob hRw n
    linarith [le_abs_self (stepConn m n (aw i) (bw i) - limConn m (aw i) (bw i))]
  have hs : ∀ n, ∀ i ∈ S, limConn m (a0 i) (b0 i)
      ≤ stepConn m n (a0 i) (b0 i) + (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := by
    intro n i hi
    obtain ⟨-, -, hR0⟩ := hK i hi
    have h1 : |stepConn m n (a0 i) (b0 i) - limConn m (a0 i) (b0 i)|
        ≤ (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := abs_stepConn_sub_le h hprob hR0 n
    linarith [neg_abs_le (stepConn m n (a0 i) (b0 i) - limConn m (a0 i) (b0 i))]
  have hsn : ∀ n, ∀ i ∈ S, 0 ≤ stepConn m n (a0 i) (b0 i) := by
    intro n i hi
    obtain ⟨hnn, -, -⟩ := hK i hi
    exact hnn n
  exact ChiForest.eventually_factor_of_relative S (fun n i => stepConn m n (aw i) (bw i))
    (fun n i => stepConn m n (a0 i) (b0 i)) (fun i => limConn m (aw i) (bw i))
    (fun i => limConn m (a0 i) (b0 i)) hT hq0 hqq hlim hc hs hsn

#print axioms eventually_window_factor

/-- **One step factor strictly below `1`.** Under the hypotheses of `eventually_window_factor`:
some `0 < q < 1` has, for all large `n`, `stepConn m n (aw i) (bw i) ≤ q · stepConn m n (a0 i) (b0 i)`
at every `i ∈ S`.

DERIVED: `0` and `1` are the ends of `q`. CHOSEN: `q = (1 + q₀)/2` in the proof; any `q ∈ (q₀, 1)`
serves. -/
theorem exists_window_factor {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n in atTop, ∀ i ∈ S, stepConn m n (aw i) (bw i) ≤ q * stepConn m n (a0 i) (b0 i) := by
  obtain ⟨hq0, hq1, hlim⟩ := hq
  exact ⟨(1 + q₀) / 2, by linarith, by linarith,
    eventually_window_factor h hprob hK ⟨hq0, hq1, hlim⟩ (by linarith)⟩

#print axioms exists_window_factor

/-- **THE CARRIER BRIDGE.** A step assignment `step : ℝ → ℕ` tending to `∞` with the coupling such
that, for all large `β`, some lag `lag ≠ 0` inside the window (`lag · aRun N β ≤ L`) has: every
`x ∈ gaugeInvHalfSpaceAlg τ p` is read by some `i ∈ S`, in the sense that for every `ε > 0`, along
`PeriodicState.periodicUltra hN β`, the torus pairing of `x` at `lag` is at most the forest's window
pairing at step `step β` plus `ε`, and the forest's lag-zero pairing at step `step β` is at most the
torus pairing of `x` at lag `0` plus `ε`.

It matches the two carriers: the forest's dyadic steps of infinite-volume observer laws and the
periodic tori along `periodicUltra` at every large real `β`; and the forest's class `S` of coarse
observables and the lattice class `gaugeInvHalfSpaceAlg`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the excluded lag, the sign of `ε`
and the lag-zero pairing. -/
def ChiCarrierBridge (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (L : ℝ) (m : ℕ → MeasureTheory.Measure Ω)
    (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ) : Prop :=
  ∃ step : ℝ → ℕ, Tendsto step atTop atTop ∧ ∀ᶠ β in atTop, ∃ lag : ℕ, lag ≠ 0 ∧
    (lag : ℝ) * MassGap.AsymptoticScaling.aRun N β ≤ L ∧
    ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∃ i ∈ S, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in ((MassGap.PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
          MassGap.PeriodicReduce.torusConn τ p hN β j x lag
              ≤ stepConn m (step β) (aw i) (bw i) + ε ∧
            stepConn m (step β) (a0 i) (b0 i)
              ≤ MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε

/-- **`FixedWindowDecay` from the `χ²` forest, modulo the carrier bridge.** Under
`ChiForest.ChiForest m δ` at probability laws, `ClassKappa m S aw bw a0 b0 κ`,
`LimitFactor m S aw bw a0 b0 q₀` and `ChiCarrierBridge τ p hN L m S aw bw a0 b0`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L`. `exists_window_factor` gives `0 < q < 1` at all
large steps; the bridge's step assignment carries it to all large `β`, and at each `x` and `ε`
the torus pairing at `lag` is at most `q ·` (torus pairing at lag `0` `+ ε/2`) `+ ε/2`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. CHOSEN: `ε/2` in the proof, the
slack handed to the bridge; any split of `ε` serves. -/
theorem fixedWindowDecay_of_chiForest (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {L : ℝ}
    {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ} (h : ChiForest.ChiForest m δ)
    (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) (hbr : ChiCarrierBridge τ p hN L m S aw bw a0 b0) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨q, hq0, hq1, hev⟩ := exists_window_factor h hprob hK hq
  obtain ⟨step, hstep, hbev⟩ := hbr
  refine ⟨q, hq0, hq1, ?_⟩
  filter_upwards [hstep.eventually hev, hbev] with β hfac hb
  obtain ⟨lag, hlag0, hlagL, hx⟩ := hb
  refine ⟨lag, hlag0, hlagL, fun x hxS ε hε => ?_⟩
  obtain ⟨i, hi, hij⟩ := hx x hxS
  filter_upwards [hij (ε / 2) (half_pos hε)] with j hj
  obtain ⟨h1, h2⟩ := hj
  have h3 : stepConn m (step β) (aw i) (bw i) ≤ q * stepConn m (step β) (a0 i) (b0 i) := hfac i hi
  have h4 : q * stepConn m (step β) (a0 i) (b0 i)
      ≤ q * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε / 2) :=
    mul_le_mul_of_nonneg_left h2 hq0.le
  have h5 : q * (ε / 2) ≤ ε / 2 := mul_le_of_le_one_left (half_pos hε).le hq1.le
  have h6 : q * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε / 2)
      = q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + q * (ε / 2) := mul_add _ _ _
  linarith

#print axioms fixedWindowDecay_of_chiForest

end Chi

section ChiCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **THE CLAY CONTINUUM STATEMENT FROM THE `χ²` ROUTE.** At `2 ≤ N`, a reflection-invariant `Z`, the
separated uniform bound `hB` (E), a window `L > 0`, observer laws `m` with `ChiForest.ChiForest m δ`
at probability laws, `ClassKappa m S aw bw a0 b0 κ`, `LimitFactor m S aw bw a0 b0 q₀` and
`ChiCarrierBridge τ 0 hN L m S aw bw a0 b0` (M), `ContinuumNontrivial.KernelConvergesSep` towards a
radial `G` (N) and `ShortDistanceY.AFShortDistance G` (Y): `ClayContinuum hN Z τ hZ hB L`
(`fixedWindowDecay_of_chiForest`, `clay_continuum_of_fixedWindowDecay`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
lower end of `L`, and the reflection plane offset `p = 0` of `ContinuumClay.continuum_gap_nontrivial`;
`4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_of_chiForest (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {Ω : Type} [MeasurableSpace Ω] {ι : Type*} {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) (hbr : ChiCarrierBridge τ 0 hN L m S aw bw a0 b0)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL
    (fixedWindowDecay_of_chiForest τ 0 hN h hprob hK hq hbr) O G hconv hY

#print axioms clay_continuum_of_chiForest

end ChiCapstone

end MassGap.ClayRoutes
