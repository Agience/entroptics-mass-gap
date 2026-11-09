import Mathlib
import MassGap.ElectricStep
import MassGap.ChainCoarseSeed
import MassGap.ChainFirstCrossing
import MassGap.ConvolutionTransfer
import MassGap.WilsonChainExists

/-!
# MassGap.ElectricStepChain — the electric decimation and the magnetic Hölder excess of a Wilson chain

One Migdal–Kadanoff step compares the side-`2^{j+1}` torus at weight `W_i` with the side-`2ʲ` torus at
weight `W_{i+1}`, one weight per plaquette (`ChainFirstCrossing.halfField`). It has two halves.

* **The magnetic half** is the bond-moving inequality `HolderBondMoving.zF_le_moveIter`: on an even side `m`,
  `ZF(halfField W_i) ≤ ZF(mkField(halfField W_i))`. Its excess is
  `holderExcess C i m = log ZF(mkField(halfField W_i), m) − log ZF(halfField W_i, m) ≥ 0`
  (`holderExcess_nonneg`).
* **The electric half** is the decimation of the moved torus: integrating the links inside each coarse face
  gives the side-`n` torus at weight `W_{i+1}`, up to a constant per coarse site. `ElectricExact C i` states it
  as `log ZF(mkField(halfField W_i), 2n) = log ZF(halfField W_{i+1}, n) + κ n⁴` for every `n ≥ 1`.
  `ElectricStep.gkW_comp` is this identity for one slice along one axis: a slice with no spatial plaquettes left
  joins its neighbours only through the time-like kernel, and integrating it composes the kernel by the per-link
  convolution.

## What is proved

* `elecWeight_eq_chainW0` (**β against 2β**). The per-link weight of `RectTransfer.gk` at the tree's `β`,
  `e^{−2β·wilsonDensity g}`, is `e^{−2β} · W₀(½ Re tr g)` for every chain started at `2β`. This is the coupling of
  `ChainFirstCrossing.defectW_eq_halfZero`, read on the transfer kernel.
* `MagneticStep C i j` is `holderExcess C i (2·2^{j+1}) ≤ 16 · holderExcess C i (2^{j+1})`; under
  `ElectricExact C i` the constants `κ n⁴` cancel, since `16 · n⁴ = (2n)⁴`.
* `excessGap_of_extensive`: if the excess is `e·m⁴ + r(m)`, the gap is `r(2·2^{j+1}) − 16·r(2^{j+1})`. The
  extensive part cancels exactly. `MagneticStep` is a statement about the excess beyond its bulk term.
* `MagneticSlack C k`: the slack form, the coarse defect plus the positive parts of the excess gaps.

## What is open

* `ElectricExact` is not proved here. It is proved for every chain in `ElectricExactProof.electricExact`, from
  `MovedTorusDecimation.decimation` and `SU2DiskLaw.convT_eq_pi_conv`.
* `MagneticStep` (or its slack form). Nothing here bounds the excess.

## Controls

`ElectricStep.gkW_comp` holds for every compact group, and the reduction is
algebra. All dependence on the group
therefore sits in `holderExcess` and in the chain. For `U(1)` the seed is false at large `β` (the Coulomb phase), so an
argument for `MagneticStep` that would apply verbatim to `U(1)`, together with a `U(1)` chain that crosses, proves too
much. Nothing here moves `U(1)` toward the seed.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.ElectricStepChain

open MeasureTheory Set Real Filter MassGap.CompactGauge MassGap.TorusDoubling MassGap.HolderBondMoving
  MassGap.ConvolutionTransfer MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing
  MassGap.WilsonChainExists

/-! ## 1. β against 2β on the transfer kernel -/

/-- **The electric weight is the chain's `W₀` at twice the coupling.** -/
theorem elecWeight_eq_chainW0 {β : ℝ} (C : WilsonChain (2 * β)) (g : SUN.SU 2) :
    ElectricStep.elecWeight 2 β g = Real.exp (-(2 * β)) * C.W 0 (suTau g) := by
  rw [C.hW0]
  unfold ElectricStep.elecWeight suTau
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## 2. The two halves of the step -/

/-- The side-`n` partition function at weight `W_i`, one weight per plaquette. -/
def Zh {β : ℝ} (C : WilsonChain β) (i n : ℕ) : ℝ :=
  ZF (probHaar (SUN.SU 2)) (uniformField (d := 4) (n := n) (halfField (C.W i) suTau))

/-- The side-`n` partition function of the moved field at weight `W_i`. -/
def Zmk {β : ℝ} (C : WilsonChain β) (i n : ℕ) : ℝ :=
  ZF (probHaar (SUN.SU 2)) (mkField (uniformField (d := 4) (n := n) (halfField (C.W i) suTau)))

/-- **The magnetic (Hölder) excess** of the bond moves at side `m`. -/
def holderExcess {β : ℝ} (C : WilsonChain β) (i m : ℕ) : ℝ :=
  Real.log (Zmk C i m) - Real.log (Zh C i m)

/-- **The electric half is exact**: the moved side-`2n` torus at `W_i` is the side-`n` torus at `W_{i+1}`, up to a
constant per coarse site. DERIVED: `4` the dimension; `n⁴` the coarse sites. -/
def ElectricExact {β : ℝ} (C : WilsonChain β) (i : ℕ) : Prop :=
  ∃ κ : ℝ, ∀ n : ℕ, 1 ≤ n →
    Real.log (Zmk C i (2 * n)) = Real.log (Zh C (i + 1) n) + κ * (n : ℝ) ^ 4

/-- **The magnetic step**: the excess at side `2·2^{j+1}` is at most `16` times the excess at side `2^{j+1}`.
DERIVED: `16 = 2⁴` the side-`2^{j+1}` tori in the side-`2·2^{j+1}` torus. -/
def MagneticStep {β : ℝ} (C : WilsonChain β) (i j : ℕ) : Prop :=
  holderExcess C i (2 * 2 ^ (j + 1)) ≤ 16 * holderExcess C i (2 ^ (j + 1))

theorem fieldDefect_eq_Zh {β : ℝ} (C : WilsonChain β) (i n : ℕ) :
    fieldDefect 4 (halfField (C.W i) suTau) n (probHaar (SUN.SU 2))
      = 16 * Real.log (Zh C i n) - Real.log (Zh C i (2 * n)) := by
  unfold fieldDefect Zh
  norm_num

/-- **The magnetic excess is non-negative** at an admissible weight on an even side. -/
theorem holderExcess_nonneg {β : ℝ} (C : WilsonChain β) (i : ℕ) {m : ℕ} (hm : Even m) {c : ℝ}
    (hW : FlatAdmissible (C.W i) (C.W' i) c) (hc : 0 < c) : 0 ≤ holderExcess C i m := by
  have hmeas := measurable_halfField hW measurable_suTau
  have hlo := halfField_ge hW hc suTau_mem
  have hhi := halfField_le hW hc suTau_mem
  obtain ⟨l, -⟩ := zF_bounds (d := 4) (n := m) (probHaar (SUN.SU 2)) hmeas hlo hhi
  have hpos := lt_of_lt_of_le (Real.exp_pos _) l
  have hle : Zh C i m ≤ Zmk C i m := by
    unfold Zh Zmk mkField
    refine zF_le_moveIter (probHaar (SUN.SU 2)) hm
      (K := |-Real.log (C.W i 1) / 2| + π ^ 2 / (8 * c)) ⟨fun _ => hmeas, fun _ g => ?_⟩
      (fun _ _ _ _ => rfl) 4
    have a1 := neg_abs_le (-Real.log (C.W i 1) / 2)
    have a2 := le_abs_self (-Real.log (C.W i 1) / 2)
    have a3 : 0 ≤ π ^ 2 / (8 * c) := by positivity
    have b1 := hlo g
    have b2 := hhi g
    show |halfField (C.W i) suTau g| ≤ _
    rw [abs_le]
    constructor <;> linarith
  unfold holderExcess
  have := Real.log_le_log (show 0 < Zh C i m from hpos) hle
  linarith

/-! ## 3. The step gap is the doubling defect of the excess -/

/-- **The extensive part of the excess cancels.** If `holderExcess C i m = e m⁴ + r m` at the two sides, the
excess gap is `r(2·2^{j+1}) − 16 r(2^{j+1})`. -/
theorem excessGap_of_extensive {β : ℝ} {C : WilsonChain β} {i : ℕ} (e : ℝ) (r : ℕ → ℝ) (j : ℕ)
    (h1 : holderExcess C i (2 * 2 ^ (j + 1)) = e * ((2 * 2 ^ (j + 1) : ℕ) : ℝ) ^ 4 + r (2 * 2 ^ (j + 1)))
    (h2 : holderExcess C i (2 ^ (j + 1)) = e * ((2 ^ (j + 1) : ℕ) : ℝ) ^ 4 + r (2 ^ (j + 1))) :
    holderExcess C i (2 * 2 ^ (j + 1)) - 16 * holderExcess C i (2 ^ (j + 1))
      = r (2 * 2 ^ (j + 1)) - 16 * r (2 ^ (j + 1)) := by
  rw [h1, h2]
  push_cast
  ring

/-! ## 4. The slack form and the seed -/

/-- **The slack form, magnetic only**: the coarse defect plus the positive parts of the excess gaps along the
anti-diagonal ending at `k`. DERIVED: `1/1000` the doubling-defect seed. -/
def MagneticSlack {β : ℝ} (C : WilsonChain β) (k : ℕ) : Prop :=
  coarseDefect C k + ∑ i ∈ Finset.range k,
    max 0 (holderExcess C i (2 * 2 ^ (k - i + 1)) - 16 * holderExcess C i (2 ^ (k - i + 1)))
    ≤ 1 / 1000

end MassGap.ElectricStepChain

end

#print axioms MassGap.ElectricStepChain.elecWeight_eq_chainW0
#print axioms MassGap.ElectricStepChain.holderExcess_nonneg
#print axioms MassGap.ElectricStepChain.excessGap_of_extensive
