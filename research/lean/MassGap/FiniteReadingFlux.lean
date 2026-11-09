import Mathlib
import MassGap.FluxCost

/-!
# MassGap.FiniteReadingFlux — the hidden cost as one reading, and a neutral factor no flux deficit sees

`ObserverTheory.HiddenCostAt N σ A ℓ` bounds the zero-flux doubling defect
`trivialDefectN N β n i = dd(trivKN) = 2 log hs(trivKN) − log hs(trivKN ∗ trivKN)` by `A e^{−σ n a}` at the
window `n a ∈ [2ℓ, 5ℓ]`. This module tests two readings of that statement.

## 1. One reading (generic kernels)

For a bounded kernel `a` on a probability space and a bounded reading `φ` with `∫ φ² = 1`:
`kapply a φ = aφ`, `readWeight a φ = ‖aφ‖²`, and `hiddenShare a φ = 1 − ‖aφ‖²/hs(a)`, the share of the trace
`hs(a)` that the reading `φ` does not carry.

* `readWeight_le_hs`: `‖aφ‖² ≤ hs(a)`, so `hiddenShare ≥ 0`.
* `sq_readWeight_le`: for symmetric `a`, `‖aφ‖⁴ ≤ hs(a ∗ a)` (Cauchy–Schwarz twice, no spectral theory).
* `dd_le_reading`: `dd(a) ≤ 2 (log hs(a) − log ‖aφ‖²)`.
* `dd_le_four_share`: at `hiddenShare ≤ 1/2`, `dd(a) ≤ 4 · hiddenShare`.
* `exists_reading`: conversely, for bounded `a` with a floor `c > 0`, some normalised bounded reading (a
  normalised column `a(·, x₀)`, `x₀` chosen by the first-moment method) has `hiddenShare ≤ dd(a)`.

So the doubling defect is small exactly when one reading carries all but a small share of the trace.

## 2. The hidden cost is a one-reading statement (lattice)

* `ReadingCostAt N σ A ℓ`: at every window side and step, some bounded normalised reading `φ` of the slice
  has `hiddenShare(trivKN, φ) ≤ A e^{−σ n a}`.
* `readingCostAt_of_hiddenCostAt`: `HiddenCostAt N σ A ℓ ⇒ ReadingCostAt N σ A ℓ`.
* `hiddenCostAt_of_readingCostAt`: at `σ, A ≥ 0` and `A e^{−2σℓ} ≤ 1/2`,
  `ReadingCostAt N σ A ℓ ⇒ HiddenCostAt N σ (4A) ℓ`.
* `runSeed_iff_bindingRead`: `WDeltaRun.RunSeed N ↔ ∃ σ A, 0 < σ ∧ ∃ᶠ ℓ, FluxCostAt ∧ ReadingCostAt`.

So "the box reads a finite amount", stated at the transfer as "some reading, chosen at each step, carries the zero-flux trace up to
`A e^{−σ n a}`", is `HiddenCostAt` itself, up to the factor `4`; it restates (T), it does not discharge it.

## 3. A neutral factor (generic kernels)

On `Y × Z` with the product measure, `tensor b k ((y,z),(y',z')) = b(y,y') k(z,z')`, and the centre acts on `Y`
only (`prodAct act g = Prod.map (act g) id`).

* `conv_tensor`, `hs_tensor`, `twist_tensor`, `zk_tensor`: composition, trace, twisted trace and zero-flux
  kernel factor.
* `centreAction_prod`: the action on the first factor is again a `CentreAction`.
* `twistRatio_tensor`, `fluxShare_tensor`: every twisted ratio `twist/hs` and the flux share of `b ⊗ k` are
  those of `b`; `twistRatio_conv_tensor`: the same for the doubled kernel.
* `zeroDefect_tensor`: `dd(zk(b ⊗ k)) = dd(zk b) + dd(k)`.
* `kapply_tensor_fst`: a reading of the `Y` factor, `f ∘ Prod.fst`, is carried by `b ⊗ k` to `(b f) ∘ Prod.fst`
  times the row integral of `k`; for a kernel with row integrals `1` the `Y` readings see `b` exactly.

## 4. A two-state neutral factor

`νB = ½ · count` on `Bool`, `kB t x y = 1 + t s(x) s(y)` with `s = ±1`.
`conv_kB`: `kB t ∗ kB s = kB (t s)`; `hs_kB`: `hs(kB t) = 1 + t²`; `dd_kB_half`: `dd(kB ½) = log(25/17) > 0`;
`kB_floor`: `kB ½ ≥ 1/2`; `integral_kB`: its rows integrate to `1`.

## 5. The neutral factor on the Wilson slice

`wilson_neutral`: at `β ≥ 0`, the kernel `halfKN N β n i ⊗ kB ½` on `slice × Bool`, with the centre `Z_N³` acting
on the slice, is bounded, symmetric, centre-invariant, bounded below by a positive constant, and has

* every twisted ratio equal to that of the Wilson slice: `twistRatioN N β n i g` at the half extent,
  `twistRatio (halfKN ∗ halfKN)` at the doubled extent;
* flux share equal to `fluxShareN N β n i`;
* zero-flux defect equal to `trivialDefectN N β n i + log(25/17)`.

So every quantity built from centre twists of the kernel (all `g`, both extents) takes the same value on two
kernels of the class the sector machinery uses (the class of `Adm [] c` kernels with a `CentreAction` and centre
invariance, on any probability space: `CentreSectorSeedN.adm_halfKN`, `ZeroFluxSector`), whose zero-flux defects
differ by `log(25/17)`. No inequality `T ≤ F(twisted ratios)` with `F` finite-valued holds uniformly on that
class: since `twistRatio_tensor` and `zeroDefect_tensor` are stated for every `Y`, applying them `m` times adds
`m log(25/17)` to `T` with the twisted ratios unchanged (an iteration of the two lemmas, not a separate
declaration). This is a statement about the class at fixed `(β, n)`; it does not bound or refute any inequality
specific to the Wilson `halfKN`, and `kB ½` is not an `n`-th power of a fixed step factor, so bounds using the
transfer semigroup in `n` are refuted only by the variant `(kT ⊗ kB e^{−M a})^{n/2−1}` with neutral mass
`M < σ/2` (argued, not a declaration).

## Evaluation (argued, not declarations)

* (d) "a closed loop is two opposite flux lines": the twisted traces `Z_g/Z` count only flux that winds the
  torus; a contractible loop crosses each twisted cut a net zero times and carries weight `1` under every twist,
  so it lies in the zero-flux sector with every twist deficit blind to it. Section 5 is the formal form: the
  zero-flux defect is not a function of the twist data. A bound of `T` by flux must use dynamics coupling the
  neutral modes to the flux (Yang–Mills specific), not the centre-sector structure. Dimensionally, a winding
  line costs `σ · (n a)` while a small contractible loop costs a fixed physical energy, so "twice the flux
  cost" holds only for loops of size `n a`.
* (c) "the box reads a finite amount": the neutral factor commutes with every reading of the first factor
  (`kapply_tensor_fst`, `integral_kB`), so if `b` passes a finite reading `π` to `K` (`FiniteInformation.Passes`),
  `b ⊗ kB ½` passes `π ∘ Prod.fst` to the same `K` (argued from those two lemmas, not a declaration), and still
  adds `log(25/17)` to the defect. At the transfer level section 2 shows the needed
  statement is a trace statement: the hidden share of the zero-flux trace off one reading, uniformly in the
  zoom. No declaration of the tree supplies it: `CondGap` states the conditional UV gap and does not prove it,
  `FineLinks` reduces it to a Bałaban-type `NearFree` input, `BalabanUV` is a hypothesis.

DERIVED (module-wide): `2` the square in `hs` and the two Cauchy–Schwarz steps; `1/2` the share at which
`−2 log(1 − η) ≤ 4η` is used, and `4 = 2 · 2`; `2ℓ`, `5ℓ` the window of `ObserverTheory.HiddenCostAt`;
`½`, `1 ± t` the two-state factor, so `5/4 = 1 + (½)²`, `17/16 = 1 + (½)⁴`, `25/17 = (5/4)²/(17/16)`,
`1/2 = 1 − ½` the floor of `kB ½`.
-/

noncomputable section

namespace MassGap.FiniteReadingFlux

open MeasureTheory Filter MassGap MassGap.KernelPower MassGap.SectorDefect MassGap.ZeroFluxSector
open MassGap.FluxSectorFourier (CentreAction)

/-! ## 1. One reading -/

section Reading

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable (μ) in
/-- The kernel applied to a reading: `(aφ)(y) = ∫ a(y,z) φ(z)`. -/
def kapply (a : X → X → ℝ) (φ : X → ℝ) (y : X) : ℝ := ∫ z, a y z * φ z ∂μ

variable (μ) in
/-- **The weight carried by a reading**: `‖aφ‖²`. -/
def readWeight (a : X → X → ℝ) (φ : X → ℝ) : ℝ := ∫ y, kapply μ a φ y ^ 2 ∂μ

variable (μ) in
/-- **The hidden share**: the share of the trace `hs(a)` not carried by the reading `φ`. -/
def hiddenShare (a : X → X → ℝ) (φ : X → ℝ) : ℝ := 1 - readWeight μ a φ / hs μ a

variable {a : X → X → ℝ} {φ : X → ℝ} {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)

theorem integrable_sq_of_bdd {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun x => f x ^ 2) μ :=
  integrable_of_bdd (hf.pow_const 2) (C := C ^ 2) (fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)

theorem integrable_rowsq {F : X → X → ℝ} (hF : Bdd F) :
    Integrable (fun x => ∫ z, F x z ^ 2 ∂μ) μ := by
  obtain ⟨C, hC⟩ := hF.bdd
  exact integrable_of_bdd (measurable_integral_right (hF.meas.pow_const 2)) (C := C ^ 2)
    (fun x => abs_integral_le fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x z) 2)

theorem measurable_kapply (ha : Bdd a) (hφm : Measurable φ) : Measurable (kapply μ a φ) :=
  measurable_integral_right (F := fun y z => a y z * φ z) (ha.meas.mul (hφm.comp measurable_snd))

theorem abs_kapply_le {B' : ℝ} (hb : ∀ x, |φ x| ≤ B') {C : ℝ} (hC : ∀ x y, |a x y| ≤ C) (y : X) :
    |kapply μ a φ y| ≤ |C| * |B'| :=
  abs_integral_le fun z => by
    rw [abs_mul]
    exact mul_le_mul ((hC y z).trans (le_abs_self C)) ((hb z).trans (le_abs_self B')) (abs_nonneg _)
      (abs_nonneg _)

include hφb in
/-- **A reading carries at most the trace**: `‖aφ‖² ≤ hs(a)`. -/
theorem readWeight_le_hs (ha : Bdd a) (hφm : Measurable φ) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) :
    readWeight μ a φ ≤ hs μ a := by
  obtain ⟨C, hC⟩ := ha.bdd
  have hpt : ∀ y, kapply μ a φ y ^ 2 ≤ ∫ z, a y z ^ 2 ∂μ := by
    intro y
    have h := sq_integral_mul_le (ν := μ) (f := a y) (g := φ)
      (integrable_sq_of_bdd (ha.row y) (hC y)) (integrable_sq_of_bdd hφm hφb)
      (integrable_mul_of_bdd (ha.row y) hφm (hC y) hφb)
    rw [hφ1, mul_one] at h
    exact h
  exact integral_mono (integrable_sq_of_bdd (measurable_kapply ha hφm) (abs_kapply_le hφb hC))
    (integrable_rowsq ha) hpt

include hφb in
/-- **The reading bounds the doubled trace from below**: `‖aφ‖⁴ ≤ hs(a ∗ a)`. -/
theorem sq_readWeight_le (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hφm : Measurable φ)
    (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) : readWeight μ a φ ^ 2 ≤ hs μ (conv μ a a) := by
  obtain ⟨C, hC⟩ := ha.bdd
  have hC' : ∀ x y, |a x y| ≤ |C| := fun x y => (hC x y).trans (le_abs_self C)
  have hB' : ∀ x, |φ x| ≤ |B| := fun x => (hφb x).trans (le_abs_self B)
  set v := kapply μ a φ with hv
  have hvm : Measurable v := measurable_kapply ha hφm
  have hvb : ∀ y, |v y| ≤ |C| * |B| := abs_kapply_le hφb hC
  -- `u = a v = (a ∗ a) φ`
  set u : X → ℝ := fun x => ∫ y, a x y * v y ∂μ with hu
  have hum : Measurable u :=
    measurable_integral_right (F := fun x y => a x y * v y) (ha.meas.mul (hvm.comp measurable_snd))
  have hub : ∀ x, |u x| ≤ |C| * (|C| * |B|) := fun x => abs_integral_le fun y => by
    rw [abs_mul]; exact mul_le_mul (hC' x y) (hvb y) (abs_nonneg _) (abs_nonneg _)
  have hcc := Bdd.conv (μ := μ) ha ha
  obtain ⟨Cc, hCc⟩ := hcc.bdd
  -- `u x = ∫ z, (a ∗ a)(x, z) φ z`
  have hu_conv : ∀ x, u x = ∫ z, conv μ a a x z * φ z ∂μ := by
    intro x
    have e1 : u x = ∫ y, ∫ z, a x y * (a y z * φ z) ∂μ ∂μ := by
      simp only [hu, hv, kapply]
      exact integral_congr_ae (Eventually.of_forall fun y => (integral_const_mul _ _).symm)
    have hF : Measurable (Function.uncurry (fun y z => a x y * (a y z * φ z))) :=
      ((ha.row x).comp measurable_fst).mul (ha.meas.mul (hφm.comp measurable_snd))
    have e2 := swap_bdd (μ := μ) hF (C := |C| * (|C| * |B|)) (fun y z => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hC' x y) (mul_le_mul (hC' y z) (hB' z) (abs_nonneg _) (abs_nonneg _))
        (by positivity) (abs_nonneg _))
    rw [e1, e2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [conv]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  -- `∫ φ u = ‖v‖²`
  have hφu : ∫ x, φ x * u x ∂μ = readWeight μ a φ := by
    have e1 : ∫ x, φ x * u x ∂μ = ∫ x, ∫ y, φ x * (a x y * v y) ∂μ ∂μ := by
      exact integral_congr_ae (Eventually.of_forall fun x => (integral_const_mul _ _).symm)
    have hF : Measurable (Function.uncurry (fun x y => φ x * (a x y * v y))) :=
      (hφm.comp measurable_fst).mul (ha.meas.mul (hvm.comp measurable_snd))
    have e2 := swap_bdd (μ := μ) hF (C := |B| * (|C| * (|C| * |B|))) (fun x y => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hB' x) (mul_le_mul (hC' x y) (hvb y) (abs_nonneg _) (abs_nonneg _))
        (by positivity) (abs_nonneg _))
    rw [e1, e2]
    unfold readWeight
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e3 : ∫ x, φ x * (a x y * v y) ∂μ = (∫ x, a y x * φ x ∂μ) * v y := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Eventually.of_forall fun x => by beta_reduce; rw [hsym x y]; ring)
    beta_reduce
    rw [e3]
    simp only [hv, kapply]
    ring
  -- Cauchy–Schwarz twice
  have h1 : readWeight μ a φ ^ 2 ≤ ∫ x, u x ^ 2 ∂μ := by
    have h := sq_integral_mul_le (ν := μ) (f := φ) (g := u) (integrable_sq_of_bdd hφm hφb)
      (integrable_sq_of_bdd hum hub) (integrable_mul_of_bdd hφm hum hφb hub)
    rw [hφu, hφ1, one_mul] at h
    exact h
  have h2 : ∀ x, u x ^ 2 ≤ ∫ z, conv μ a a x z ^ 2 ∂μ := by
    intro x
    have h := sq_integral_mul_le (ν := μ) (f := conv μ a a x) (g := φ)
      (integrable_sq_of_bdd (hcc.row x) (hCc x)) (integrable_sq_of_bdd hφm hφb)
      (integrable_mul_of_bdd (hcc.row x) hφm (hCc x) hφb)
    rw [hφ1, mul_one, ← hu_conv x] at h
    exact h
  exact h1.trans (integral_mono (integrable_sq_of_bdd hum hub) (integrable_rowsq hcc) h2)

include hφb in
/-- **One reading bounds the doubling defect**: `dd(a) ≤ 2 (log hs(a) − log ‖aφ‖²)`. -/
theorem dd_le_reading (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hφm : Measurable φ)
    (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) (hpos : 0 < readWeight μ a φ) :
    dd μ a ≤ 2 * (Real.log (hs μ a) - Real.log (readWeight μ a φ)) := by
  have h := sq_readWeight_le hφb ha hsym hφm hφ1
  have hl := Real.log_le_log (pow_pos hpos 2) h
  rw [Real.log_pow] at hl
  unfold dd
  push_cast at hl
  linarith

include hφb in
/-- **At a hidden share at most `1/2`, the defect is at most four times the share.** -/
theorem dd_le_four_share (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hφm : Measurable φ)
    (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) (hhs : 0 < hs μ a) (hη : hiddenShare μ a φ ≤ 1 / 2) :
    dd μ a ≤ 4 * hiddenShare μ a φ := by
  set r := readWeight μ a φ with hr
  set h := hs μ a with hh
  have hrle : r ≤ h := readWeight_le_hs hφb ha hφm hφ1
  have hh0 : h ≠ 0 := hhs.ne'
  have hηdef : hiddenShare μ a φ = (h - r) / h := by
    unfold hiddenShare; rw [← hr, ← hh, sub_div, div_self hh0]
  rw [hηdef] at hη ⊢
  have hhalf : h / 2 ≤ r := by
    rw [div_le_iff₀ hhs] at hη; linarith
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := hrpos.ne'
  have hdd := dd_le_reading hφb ha hsym hφm hφ1 hrpos
  rw [← hr, ← hh] at hdd
  have hlog : Real.log h - Real.log r ≤ (h - r) / r := by
    rw [← Real.log_div hhs.ne' hrpos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hhs hrpos)
    have e : h / r - 1 = (h - r) / r := by rw [sub_div, div_self hr0]
    linarith
  have hcmp : (h - r) / r ≤ (h - r) / (h / 2) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hhalf
  have e2 : (h - r) / (h / 2) = 2 * ((h - r) / h) := by rw [div_div_eq_mul_div]; ring
  linarith

/-- **Some normalised column carries all but `dd(a)` of the trace**: for bounded `a` with a floor `c > 0`,
there is a bounded normalised reading with `hiddenShare ≤ dd(a)`. -/
theorem exists_reading (ha : Bdd a) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x y, c ≤ a x y) :
    ∃ φ : X → ℝ, Measurable φ ∧ (∃ B, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂μ = 1 ∧
      hiddenShare μ a φ ≤ dd μ a := by
  obtain ⟨C, hC⟩ := ha.bdd
  have hcc := Bdd.conv (μ := μ) ha ha
  obtain ⟨Cc, hCc⟩ := hcc.bdd
  set F : X → ℝ := fun x₀ => ∫ y, conv μ a a y x₀ ^ 2 ∂μ with hFdef
  set G : X → ℝ := fun x₀ => ∫ x, a x x₀ ^ 2 ∂μ with hGdef
  have hFm : Measurable F := measurable_integral_right (F := fun x₀ y => conv μ a a y x₀ ^ 2)
    ((hcc.meas.comp measurable_swap).pow_const 2)
  have hGm : Measurable G := measurable_integral_right (F := fun x₀ x => a x x₀ ^ 2)
    ((ha.meas.comp measurable_swap).pow_const 2)
  have hFb : ∀ x₀, |F x₀| ≤ Cc ^ 2 := fun x₀ => abs_integral_le fun y => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCc y x₀) 2
  have hGb : ∀ x₀, |G x₀| ≤ C ^ 2 := fun x₀ => abs_integral_le fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x x₀) 2
  have hFint : ∫ x₀, F x₀ ∂μ = hs μ (conv μ a a) := by
    unfold hs
    refine (swap_bdd (μ := μ) (F := fun y x₀ => conv μ a a y x₀ ^ 2) (hcc.meas.pow_const 2)
      (C := Cc ^ 2) (fun y x₀ => ?_)).symm
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCc y x₀) 2
  have hGint : ∫ x₀, G x₀ ∂μ = hs μ a := by
    unfold hs
    refine (swap_bdd (μ := μ) (F := fun x x₀ => a x x₀ ^ 2) (ha.meas.pow_const 2)
      (C := C ^ 2) (fun x x₀ => ?_)).symm
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x x₀) 2
  have hGlow : ∀ x₀, c ^ 2 ≤ G x₀ := by
    intro x₀
    have hm := integral_mono (μ := μ) (integrable_const (c ^ 2))
      (integrable_sq_of_bdd (ha.col x₀) (fun x => hC x x₀))
      (fun x => pow_le_pow_left₀ hc.le (hlow x x₀) 2)
    show c ^ 2 ≤ ∫ x, a x x₀ ^ 2 ∂μ
    simpa using hm
  have hhs : 0 < hs μ a := by
    have := sq_le_hs (μ := μ) ha hc.le hlow
    have : 0 < c ^ 2 := pow_pos hc 2
    linarith
  have hhss : 0 < hs μ (conv μ a a) := by
    have := sq_le_hs (μ := μ) hcc (mul_nonneg hc.le hc.le) (conv_low (μ := μ) ha hc.le hlow)
    have : 0 < (c * c) ^ 2 := pow_pos (mul_pos hc hc) 2
    linarith
  set ρ := hs μ (conv μ a a) / hs μ a with hρ
  have hHint : Integrable (fun x₀ => F x₀ - ρ * G x₀) μ :=
    (integrable_of_bdd hFm hFb).sub ((integrable_of_bdd hGm hGb).const_mul ρ)
  have hH0 : ∫ x₀, (F x₀ - ρ * G x₀) ∂μ = 0 := by
    rw [integral_sub (integrable_of_bdd hFm hFb) ((integrable_of_bdd hGm hGb).const_mul ρ),
      integral_const_mul, hFint, hGint, hρ, div_mul_cancel₀ _ hhs.ne', sub_self]
  obtain ⟨x₀, hx₀'⟩ := exists_integral_le hHint
  have hx₀ : 0 ≤ F x₀ - ρ * G x₀ := by rw [← hH0]; exact hx₀'
  have hGpos : 0 < G x₀ := lt_of_lt_of_le (pow_pos hc 2) (hGlow x₀)
  set s := Real.sqrt (G x₀) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr hGpos
  have hss : s ^ 2 = G x₀ := Real.sq_sqrt hGpos.le
  refine ⟨fun x => a x x₀ / s, (ha.col x₀).div_const _, ⟨|C| / s, fun x => ?_⟩, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hspos]
    exact div_le_div_of_nonneg_right ((hC x x₀).trans (le_abs_self C)) hspos.le
  · simp_rw [div_pow]
    rw [integral_div, hss]
    exact div_self hGpos.ne'
  · have hk : ∀ y, kapply μ a (fun x => a x x₀ / s) y = conv μ a a y x₀ / s := by
      intro y
      simp only [kapply, conv]
      rw [← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    have hrw : readWeight μ a (fun x => a x x₀ / s) = F x₀ / G x₀ := by
      calc readWeight μ a (fun x => a x x₀ / s) = ∫ y, (conv μ a a y x₀ / s) ^ 2 ∂μ := by
            unfold readWeight; simp_rw [hk]
        _ = (∫ y, conv μ a a y x₀ ^ 2 ∂μ) / s ^ 2 := by simp_rw [div_pow]; exact integral_div _ _
        _ = F x₀ / G x₀ := by rw [hss]
    have hFG : ρ ≤ F x₀ / G x₀ := by
      rw [le_div_iff₀ hGpos]; linarith
    unfold hiddenShare
    rw [hrw]
    have hq : 1 - F x₀ / G x₀ / hs μ a ≤ 1 - ρ / hs μ a := by
      have := div_le_div_of_nonneg_right hFG hhs.le
      linarith
    refine hq.trans ?_
    -- `1 − hs(a∗a)/hs(a)² ≤ dd(a)`
    have hq2 : 0 < ρ / hs μ a := div_pos (div_pos hhss hhs) hhs
    have hlog := Real.log_le_sub_one_of_pos hq2
    have e : Real.log (ρ / hs μ a) = -dd μ a := by
      rw [hρ, Real.log_div (div_pos hhss hhs).ne' hhs.ne', Real.log_div hhss.ne' hhs.ne']
      unfold dd; ring
    linarith

end Reading

/-! ## 2. The hidden cost is a one-reading statement -/

section Lattice

open MassGap.CentreSectorSeedN MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
open MassGap.CentreSectorSeed (Tr)
open MassGap.SliceCentreAction (act centreAction)
open MassGap.ObserverTheory (HiddenCostAt FluxCostAt BindingSU)

variable (N : ℕ) [NeZero N]

/-- **The zero-flux trace is read by one reading, up to `A e^{−σ n a}`**, at every window side and step.
DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `ObserverTheory.HiddenCostAt` (`5` leaves room for the power of
two at or above `⌈2ℓ/a⌉`, which is below `4ℓ + 2a`); `2` also the least side. -/
def ReadingCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ 5 * ℓ →
    ∀ i : Fin 4, ∃ φ : (SpT i (Tr n i) → SUN.SU N) → ℝ, Measurable φ ∧ (∃ B, ∀ x, |φ x| ≤ B) ∧
      ∫ x, φ x ^ 2 ∂(hSN N n i) = 1 ∧
      hiddenShare (hSN N n i) (trivKN N β n i) φ
        ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun N β)))

variable {N}

theorem symm_trivKN {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    ∀ x y, trivKN N β n i x y = trivKN N β n i y x := fun x y =>
  zk_symm (centreAction (μ := i) (T := Tr n i) (N := N)) (symm_halfKN hβ n i) (inv_halfKN n i) x y

theorem low_trivKN {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    ∀ x y, CentreSectorSeed.floor β n i ≤ trivKN N β n i x y := fun x y =>
  zk_low (low_halfKN hβ n i) x y

/-- **The hidden cost gives the one-reading form**, with the same constant. -/
theorem readingCostAt_of_hiddenCostAt {σ A ℓ : ℝ} (h : HiddenCostAt N σ A ℓ) :
    ReadingCostAt N σ A ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i
  obtain ⟨φ, hφm, hφb, hφ1, hφ⟩ := exists_reading (μ := hSN N n i) (bdd_trivKN hβ0 n i)
    (CentreSectorSeed.floor_pos β n i) (low_trivKN hβ0 n i)
  exact ⟨φ, hφm, hφb, hφ1, hφ.trans (hβ n hn h2 hlo hup i)⟩

/-- **The one-reading form gives the hidden cost**, with the constant multiplied by `4`, once
`A e^{−2σℓ} ≤ 1/2`. -/
theorem hiddenCostAt_of_readingCostAt {σ A ℓ : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A)
    (hsmall : A * Real.exp (-(2 * σ * ℓ)) ≤ 1 / 2) (h : ReadingCostAt N σ A ℓ) :
    HiddenCostAt N σ (4 * A) ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, hφ⟩ := hβ n hn h2 hlo hup i
  set x := (n : ℝ) * AsymptoticScaling.aRun N β
  have hexp : Real.exp (-(σ * x)) ≤ Real.exp (-(2 * σ * ℓ)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlo hσ])
  have hη : hiddenShare (hSN N n i) (trivKN N β n i) φ ≤ 1 / 2 :=
    hφ.trans ((mul_le_mul_of_nonneg_left hexp hA).trans hsmall)
  have hd := dd_le_four_share hφb (bdd_trivKN hβ0 n i) (symm_trivKN hβ0 n i) hφm hφ1
    (hs_trivKN_pos hβ0 n i) hη
  unfold trivialDefectN
  linarith

/-- **The run seed of `SU(N)` is the flux half with the one-reading form of the hidden half.** -/
theorem runSeed_iff_bindingRead :
    WDeltaRun.RunSeed N ↔
      ∃ σ A : ℝ, 0 < σ ∧ ∃ᶠ ℓ in atTop, FluxCostAt N σ A ℓ ∧ ReadingCostAt N σ A ℓ := by
  rw [ObserverTheory.runSeed_iff_bindingSU]
  constructor
  · rintro ⟨σ, A, hσ, hfr⟩
    exact ⟨σ, A, hσ, hfr.mono fun ℓ hℓ => ⟨hℓ.1, readingCostAt_of_hiddenCostAt hℓ.2⟩⟩
  · rintro ⟨σ, A, hσ, hfr⟩
    set A' := max A 0
    have hσ2 : 0 < 2 * σ := by linarith
    refine ⟨σ, max A (4 * A'), hσ, ?_⟩
    refine (hfr.and_eventually (ObserverTheory.eventually_small (c := A') hσ2
      (by norm_num : (0 : ℝ) < 1 / 2))).mono ?_
    rintro ℓ ⟨⟨hF, hR⟩, -, hs⟩
    have hR' : ReadingCostAt N σ A' ℓ := by
      filter_upwards [hR] with β hβ n hn h2 hlo hup i
      obtain ⟨φ, h1, h2', h3, h4⟩ := hβ n hn h2 hlo hup i
      exact ⟨φ, h1, h2', h3, h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.exp_pos _).le)⟩
    have hH := hiddenCostAt_of_readingCostAt hσ.le (le_max_right _ _) hs hR'
    exact ⟨FluxCost.fluxCostAt_mono (le_max_left _ _) hF,
      FluxCost.hiddenCostAt_mono (le_max_right _ _) hH⟩

end Lattice

/-! ## 3. A neutral factor -/

section Tensor

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] {μ : Measure Y} {ν : Measure Z}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **The product kernel** `(b ⊗ k)((y,z),(y',z')) = b(y,y') k(z,z')`. -/
def tensor (b : Y → Y → ℝ) (k : Z → Z → ℝ) : Y × Z → Y × Z → ℝ := fun x w => b x.1 w.1 * k x.2 w.2

/-- The centre acting on the first factor only. -/
def prodAct {G : Type*} (act : G → Y → Y) (g : G) : Y × Z → Y × Z := Prod.map (act g) id

theorem conv_tensor (b b' : Y → Y → ℝ) (k k' : Z → Z → ℝ) :
    conv (μ.prod ν) (tensor b k) (tensor b' k') = tensor (conv μ b b') (conv ν k k') := by
  funext x z
  simp only [conv, tensor]
  have e : ∀ w : Y × Z, b x.1 w.1 * k x.2 w.2 * (b' w.1 z.1 * k' w.2 z.2)
      = (b x.1 w.1 * b' w.1 z.1) * (k x.2 w.2 * k' w.2 z.2) := fun w => by ring
  simp_rw [e]
  exact integral_prod_mul (fun y => b x.1 y * b' y z.1) (fun w => k x.2 w * k' w z.2)

theorem hs_tensor (b : Y → Y → ℝ) (k : Z → Z → ℝ) :
    hs (μ.prod ν) (tensor b k) = hs μ b * hs ν k := by
  simp only [hs, tensor]
  have e : ∀ x : Y × Z, ∫ w, (b x.1 w.1 * k x.2 w.2) ^ 2 ∂(μ.prod ν)
      = (∫ y, b x.1 y ^ 2 ∂μ) * ∫ z, k x.2 z ^ 2 ∂ν := fun x => by
    simp_rw [mul_pow]
    exact integral_prod_mul (fun y => b x.1 y ^ 2) (fun z => k x.2 z ^ 2)
  simp_rw [e]
  exact integral_prod_mul (fun y => ∫ y', b y y' ^ 2 ∂μ) (fun z => ∫ z', k z z' ^ 2 ∂ν)

theorem twist_tensor (b : Y → Y → ℝ) (k : Z → Z → ℝ) (σ : Y → Y) :
    FluxSectorBound.twist (μ.prod ν) (tensor b k) (Prod.map σ id)
      = FluxSectorBound.twist μ b σ * hs ν k := by
  simp only [FluxSectorBound.twist, hs, tensor, Prod.map_fst, Prod.map_snd, id_eq]
  have e : ∀ x : Y × Z, ∫ w, b x.1 w.1 * k x.2 w.2 * (b x.1 (σ w.1) * k x.2 w.2) ∂(μ.prod ν)
      = (∫ y, b x.1 y * b x.1 (σ y) ∂μ) * ∫ z, k x.2 z ^ 2 ∂ν := fun x => by
    have e' : ∀ w : Y × Z, b x.1 w.1 * k x.2 w.2 * (b x.1 (σ w.1) * k x.2 w.2)
        = (b x.1 w.1 * b x.1 (σ w.1)) * k x.2 w.2 ^ 2 := fun w => by ring
    simp_rw [e']
    exact integral_prod_mul (fun y => b x.1 y * b x.1 (σ y)) (fun z => k x.2 z ^ 2)
  simp_rw [e]
  exact integral_prod_mul (fun y => ∫ y', b y y' * b y (σ y') ∂μ) (fun z => ∫ z', k z z' ^ 2 ∂ν)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {act : G → Y → Y}

omit [MeasurableSpace Y] [MeasurableSpace Z] [AddCommGroup G] [DecidableEq G] in
theorem zk_tensor (b : Y → Y → ℝ) (k : Z → Z → ℝ) :
    zk (tensor b k) (prodAct (Z := Z) act) = tensor (zk b act) k := by
  funext x w
  simp only [zk, tensor, prodAct, Prod.map_fst, Prod.map_snd, id_eq]
  rw [← Finset.sum_mul]
  ring

omit [Fintype G] [DecidableEq G] in
theorem centreAction_prod (hA : CentreAction μ act) :
    CentreAction (μ.prod ν) (prodAct (Z := Z) act) where
  meas g := (hA.meas g).prodMap measurable_id
  zero x := Prod.ext (hA.zero x.1) rfl
  add g h x := Prod.ext (hA.add g h x.1) rfl
  mp g := (hA.mp g).prod (MeasurePreserving.id ν)

/-- The twisted ratio `twist/hs` of a kernel at one centre element. -/
def twistRatio {X : Type*} [MeasurableSpace X] (μ : Measure X) (a : X → X → ℝ) (σ : X → X) : ℝ :=
  FluxSectorBound.twist μ a σ / hs μ a

/-- The flux share `(hs(a) − hs(zk a))/hs(a)`. -/
def fluxShare {X : Type*} [MeasurableSpace X] (μ : Measure X) (a : X → X → ℝ) (act : G → X → X) : ℝ :=
  (hs μ a - hs μ (zk a act)) / hs μ a

theorem twistRatio_tensor (b : Y → Y → ℝ) {k : Z → Z → ℝ} (hk : hs ν k ≠ 0) (σ : Y → Y) :
    twistRatio (μ.prod ν) (tensor b k) (Prod.map σ id) = twistRatio μ b σ := by
  unfold twistRatio
  rw [twist_tensor, hs_tensor, mul_div_mul_right _ _ hk]

theorem twistRatio_conv_tensor (b : Y → Y → ℝ) {k : Z → Z → ℝ} (hk : hs ν (conv ν k k) ≠ 0)
    (σ : Y → Y) :
    twistRatio (μ.prod ν) (conv (μ.prod ν) (tensor b k) (tensor b k)) (Prod.map σ id)
      = twistRatio μ (conv μ b b) σ := by
  rw [conv_tensor]; exact twistRatio_tensor _ hk σ

omit [AddCommGroup G] [DecidableEq G] in
theorem fluxShare_tensor (b : Y → Y → ℝ) {k : Z → Z → ℝ} (hk : hs ν k ≠ 0) :
    fluxShare (μ.prod ν) (tensor b k) (prodAct (Z := Z) act) = fluxShare μ b act := by
  unfold fluxShare
  rw [zk_tensor, hs_tensor, hs_tensor, ← sub_mul, mul_div_mul_right _ _ hk]

theorem dd_tensor {b : Y → Y → ℝ} {k : Z → Z → ℝ} (hb : 0 < hs μ b) (hbb : 0 < hs μ (conv μ b b))
    (hk : 0 < hs ν k) (hkk : 0 < hs ν (conv ν k k)) :
    dd (μ.prod ν) (tensor b k) = dd μ b + dd ν k := by
  unfold dd
  rw [conv_tensor, hs_tensor, hs_tensor, Real.log_mul hb.ne' hk.ne', Real.log_mul hbb.ne' hkk.ne']
  ring

omit [AddCommGroup G] [DecidableEq G] in
/-- **The neutral factor adds its own defect to the zero-flux defect.** -/
theorem zeroDefect_tensor {b : Y → Y → ℝ} {k : Z → Z → ℝ} (hb : 0 < hs μ (zk b act))
    (hbb : 0 < hs μ (conv μ (zk b act) (zk b act))) (hk : 0 < hs ν k) (hkk : 0 < hs ν (conv ν k k)) :
    dd (μ.prod ν) (zk (tensor b k) (prodAct (Z := Z) act)) = dd μ (zk b act) + dd ν k := by
  rw [zk_tensor]; exact dd_tensor hb hbb hk hkk

/-- **A reading of the first factor is carried by `b`**, times the row integral of `k`. -/
theorem kapply_tensor_fst (b : Y → Y → ℝ) (k : Z → Z → ℝ) (f : Y → ℝ) (x : Y × Z) :
    kapply (μ.prod ν) (tensor b k) (fun w => f w.1) x
      = kapply μ b f x.1 * ∫ z, k x.2 z ∂ν := by
  simp only [kapply, tensor]
  have e : ∀ w : Y × Z, b x.1 w.1 * k x.2 w.2 * f w.1 = (b x.1 w.1 * f w.1) * k x.2 w.2 :=
    fun w => by ring
  simp_rw [e]
  exact integral_prod_mul (fun y => b x.1 y * f y) (fun z => k x.2 z)

end Tensor

/-! ## 4. A two-state neutral factor -/

section TwoState

open scoped ENNReal

/-- The uniform probability on `Bool`. -/
def νB : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

theorem integral_νB (f : Bool → ℝ) : ∫ x, f x ∂νB = (f true + f false) / 2 := by
  have e : ((2 : ℝ≥0∞)⁻¹).toReal = 1 / 2 := by simp
  rw [νB, integral_smul_measure, integral_count, Fintype.sum_bool, e, smul_eq_mul]
  ring

instance : IsProbabilityMeasure νB := by
  constructor
  have h : ∫ _x, (1 : ℝ) ∂νB = 1 := by rw [integral_νB]; norm_num
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

/-- The sign `±1`. -/
def sgn (x : Bool) : ℝ := if x then 1 else -1

/-- **The two-state kernel** `1 + t s(x) s(y)`. -/
def kB (t : ℝ) (x y : Bool) : ℝ := 1 + t * sgn x * sgn y

theorem conv_kB (t s : ℝ) : conv νB (kB t) (kB s) = kB (t * s) := by
  funext x z
  simp only [conv]
  rw [integral_νB]
  cases x <;> cases z <;> simp [kB, sgn] <;> ring

theorem hs_kB (t : ℝ) : hs νB (kB t) = 1 + t ^ 2 := by
  simp only [hs, integral_νB]
  simp [kB, sgn]
  ring

theorem integral_kB (t : ℝ) (x : Bool) : ∫ z, kB t x z ∂νB = 1 := by
  rw [integral_νB]; cases x <;> simp [kB, sgn] <;> ring

theorem kB_symm (t : ℝ) (x y : Bool) : kB t x y = kB t y x := by
  simp only [kB]; ring

theorem kB_floor (x y : Bool) : (1 / 2 : ℝ) ≤ kB (1 / 2) x y := by
  cases x <;> cases y <;> simp [kB, sgn] <;> norm_num

theorem abs_kB_le (t : ℝ) (x y : Bool) : |kB t x y| ≤ 1 + |t| := by
  have hs : ∀ b, |sgn b| = 1 := by intro b; cases b <;> simp [sgn]
  calc |kB t x y| ≤ |(1 : ℝ)| + |t * sgn x * sgn y| := abs_add_le _ _
    _ = 1 + |t| := by rw [abs_mul, abs_mul, hs, hs, abs_one, mul_one, mul_one]

theorem bdd_kB (t : ℝ) : Bdd (kB t) := ⟨measurable_of_countable _, 1 + |t|, abs_kB_le t⟩

theorem hs_kB_half : hs νB (kB (1 / 2)) = 5 / 4 := by rw [hs_kB]; norm_num

theorem hs_conv_kB_half : hs νB (conv νB (kB (1 / 2)) (kB (1 / 2))) = 17 / 16 := by
  rw [conv_kB, hs_kB]; norm_num

/-- **The two-state factor has defect `log(25/17)`.** -/
theorem dd_kB_half : dd νB (kB (1 / 2)) = Real.log (25 / 17) := by
  unfold dd
  rw [hs_kB_half, hs_conv_kB_half]
  have h1 : 2 * Real.log (5 / 4 : ℝ) = Real.log ((5 / 4 : ℝ) ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [h1, ← Real.log_div (x := (5 / 4 : ℝ) ^ 2) (y := 17 / 16) (by norm_num) (by norm_num)]
  norm_num

theorem log_25_17_pos : 0 < Real.log (25 / 17 : ℝ) := Real.log_pos (by norm_num)

end TwoState

/-! ## 5. The neutral factor on the Wilson slice -/

section Wilson

open MassGap.CentreSectorSeedN MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
open MassGap.CentreSectorSeed (Tr)
open MassGap.SliceCentreAction (Cen act centreAction)

variable {N : ℕ} [NeZero N]

/-- **The Wilson slice with a neutral two-state factor.** At `β ≥ 0` the kernel `halfKN ⊗ kB ½` on
`slice × Bool`, with the centre acting on the slice, is bounded, symmetric, centre-invariant and bounded below by
`floor · 1/2 > 0`; every twisted ratio (half and doubled extent) and the flux share are those of the Wilson slice;
the zero-flux defect is `trivialDefectN + log(25/17)`. -/
theorem wilson_neutral {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    let μ' := (hSN N n i).prod νB
    let a := tensor (halfKN N β n i) (kB (1 / 2))
    let A := prodAct (Z := Bool) (act (μ := i) (T := Tr n i) (N := N))
    CentreAction μ' A ∧ Bdd a ∧ (∀ x y, a x y = a y x) ∧ (∀ g x y, a (A g x) (A g y) = a x y) ∧
      (∀ x y, CentreSectorSeed.floor β n i * (1 / 2) ≤ a x y) ∧
      (∀ g : Cen i N, twistRatio μ' a (A g) = twistRatioN N β n i g) ∧
      (∀ g : Cen i N, twistRatio μ' (conv μ' a a) (A g)
        = twistRatio (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i))
            (act (μ := i) (T := Tr n i) (N := N) g)) ∧
      fluxShare μ' a A = fluxShareN N β n i ∧
      dd μ' (zk a A) = trivialDefectN N β n i + Real.log (25 / 17) := by
  intro μ' a A
  have hk : hs νB (kB (1 / 2)) ≠ 0 := by rw [hs_kB_half]; norm_num
  have hkk : hs νB (conv νB (kB (1 / 2)) (kB (1 / 2))) ≠ 0 := by rw [hs_conv_kB_half]; norm_num
  have hbH := bdd_halfKN (N := N) hβ n i
  obtain ⟨Cb, hCb⟩ := hbH.bdd
  refine ⟨centreAction_prod centreAction, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(hbH.meas.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).mul ((bdd_kB (1 / 2)).meas.comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))),
      |Cb| * (1 + |1 / 2|), fun x y => ?_⟩
    simp only [a, tensor]
    rw [abs_mul]
    exact mul_le_mul ((hCb _ _).trans (le_abs_self _)) (abs_kB_le _ _ _) (abs_nonneg _) (abs_nonneg _)
  · intro x y
    simp only [a, tensor]
    rw [symm_halfKN hβ n i x.1 y.1, kB_symm]
  · intro g x y
    simp only [a, A, tensor, prodAct, Prod.map_fst, Prod.map_snd, id_eq]
    rw [inv_halfKN n i g x.1 y.1]
  · intro x y
    simp only [a, tensor]
    exact mul_le_mul (low_halfKN hβ n i x.1 y.1) (kB_floor x.2 y.2) (by norm_num)
      ((CentreSectorSeed.floor_pos β n i).le.trans (low_halfKN hβ n i x.1 y.1))
  · intro g
    simp only [μ', a, A, prodAct]
    rw [twistRatio_tensor _ hk]
    rfl
  · intro g
    simp only [μ', a, A, prodAct]
    exact twistRatio_conv_tensor _ hkk _
  · simp only [μ', a, A]
    rw [fluxShare_tensor _ hk]
    rfl
  · simp only [μ', a, A]
    rw [zeroDefect_tensor (hs_trivKN_pos hβ n i) (hs_conv_trivKN_pos hβ n i)
      (by rw [hs_kB_half]; norm_num) (by rw [hs_conv_kB_half]; norm_num), dd_kB_half]
    rfl

end Wilson

end MassGap.FiniteReadingFlux

end

#print axioms MassGap.FiniteReadingFlux.readWeight_le_hs
#print axioms MassGap.FiniteReadingFlux.sq_readWeight_le
#print axioms MassGap.FiniteReadingFlux.dd_le_reading
#print axioms MassGap.FiniteReadingFlux.dd_le_four_share
#print axioms MassGap.FiniteReadingFlux.exists_reading
#print axioms MassGap.FiniteReadingFlux.readingCostAt_of_hiddenCostAt
#print axioms MassGap.FiniteReadingFlux.hiddenCostAt_of_readingCostAt
#print axioms MassGap.FiniteReadingFlux.runSeed_iff_bindingRead
#print axioms MassGap.FiniteReadingFlux.zeroDefect_tensor
#print axioms MassGap.FiniteReadingFlux.fluxShare_tensor
#print axioms MassGap.FiniteReadingFlux.twistRatio_conv_tensor
#print axioms MassGap.FiniteReadingFlux.kapply_tensor_fst
#print axioms MassGap.FiniteReadingFlux.dd_kB_half
#print axioms MassGap.FiniteReadingFlux.wilson_neutral
