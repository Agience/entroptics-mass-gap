import Mathlib
import MassGap.ApertureOne

/-!
# MassGap.GapAttack — the far input as a statement about the slice kernels, and its single-scale reading

`ApertureNearAll.Far L ε` asks, eventually in `β` and at the physical side `n = 2^{kPhys L β + 2}`, that each of
the four one-direction doubling defects `D_s = 2 log cyc(kT_s, n) − log cyc(kT_s, 2n)` be at most `ε`;
`physDefect_of_far` turns it into `ApertureBridge.PhysDefect L (15 ε)`. This module states that input as a
statement about the slice kernels themselves, reads it against a relative spectral gap, and separates what
asymptotic freedom carries from what the gap carries.

## 1. The kernel form (proved, eigen-free)

* `log_step_le_iff`: for `a, b > 0`, `2 log a − log b ≤ ε ↔ e^{−ε} a² ≤ b`.
* `stepD_le_iff`: at every dyadic side `2^{k+2}` and `β ≥ 0`, `D_s ≤ ε ↔ e^{−ε} cyc(kT_s, n)² ≤ cyc(kT_s, 2n)`
  (positivity from `ApertureWindow.cycT_pos_le`).
* `KernFar L ε`: eventually in `β`, at the physical side, `cyc(kT_s, 2n) ≥ e^{−ε} cyc(kT_s, n)²` for every `s`.
  The cycle of length `2n` carries at least `e^{−ε}` of the square of the cycle of length `n`: the slice kernel
  on its own cycle is rank one up to `ε`.
* `far_iff_kernFar`: `Far L ε ↔ KernFar L ε`.
* `physDefect_of_kernFar`: `KernFar L ε ⇒ PhysDefect L (15 ε)`; `kernFar_of_physDefect`: `PhysDefect L δ ⇒
  KernFar L δ` (each `D_s ≥ 0`, `ApertureWindow.stepD_phys_nonneg`). So `KernFar` is the far input within the
  factor `15`, in both directions.

## 2. The kernel form read against a relative spectral gap (proved, in the eigenvalue model of `ApertureTwo`)

Ratios `r`, `r 0 = 1`, `0 ≤ r`; `τ_n = Σ_{i ≥ 1} r_iⁿ`.

* `tau_le_gap`: a relative gap `r_i ≤ ρ` (`i ≥ 1`) gives `τ_n ≤ ρ^{n − m₀} τ_{m₀}` at `m₀ ≤ n`.
* `stepDefect_le_gap`: so the defect at length `n` is at most `2 ρ^{n − m₀} τ_{m₀}`.
* `excited_le_of_stepDefect`: a defect at most `ε` at length `n` forces every excited ratio to satisfy
  `r_iⁿ ≤ eᵋ − 1`: a relative gap at least `log(1/(eᵋ − 1))/n` per unit length.

A uniform relative gap alone does not give the far input: `τ_{m₀}` counts every excited level of a kernel whose
cross-section has `n³` sites, so the reference weight must be read at a length where it is finite in physical
units. The sharp form is `τ_n ≤ eᵋ − 1` at the physical side itself, which is `KernFar` within the factor `2`
(`ApertureNearAll.stepDefect_ge`, `ApertureTwo.stepDefect_le`).

## 3. The single-scale reading (proved)

`physLen L β = 2^{kPhys L β + 2} · aRun 2 β` is the physical side of the torus `PhysDefect` reads; it lies in
`(L/2, L]` eventually (`physLen_mem`).

* `Scales L Ψ`: the defect at the physical side is, eventually in `β` and within every `η > 0`, a function `Ψ`
  of the physical side alone. This is the renormalization clause: the coupling dependence of the finite-volume
  doubling free energy is carried by the running `aRun` and nothing else.
* `OneScale L Ψ δ`: `Ψ ≤ δ` on `(L/2, L]`. This is the gap at the one physical scale `L`.
* `physDefect_of_oneScale`: `Scales L Ψ`, `OneScale L Ψ δ'`, `δ' < δ` give `PhysDefect L δ`, with no reference
  to any coupling below `β` (`DimFar` is not used).
* `not_scales_of_coulomb`: a massless (Coulomb `κ/x`) finite-size part admits no `Ψ` bounded on `(L/2, L]`
  with `Scales L Ψ`. The massless unit fails `Scales`, not only `OneScale`: its defect at fixed physical side
  grows like `κ log β`, the zero-mode count, which no function of the physical side reproduces.

So the gap follows from two typed clauses at one physical scale: `Scales` (the continuum limit of the doubling free
energy of the torus of physical side in `(L/2, L]`, uniformly on that interval, where asymptotic freedom enters)
and `OneScale` (that continuum number is below `1/1000`). Together they are strictly stronger than `PhysDefect`
(which bounds the limsup and asks no convergence): a sufficient condition, not a reduction of content. `OneScale` holds only at `L` many correlation lengths; `Scales` is a
perturbative (small-field) statement only at `L` small against the generated scale. The two clauses are needed at
the same `L`, and at that `L` neither is perturbative.

DERIVED (module-wide): `2` the doubling and `SU(2)`; `2` in `kPhys + 2` from `ApertureBridge.PhysDefect`; `15` from
`ApertureNearAll.physDefect_of_far`; `4` the directions; `1` the vacuum weight `r 0`; `L/2` from
`PhysicalScaleSmall.physSide_spec`.
-/

noncomputable section

namespace MassGap.GapAttack

open Real Filter Set MassGap MassGap.PhysicalScaleSmall MassGap.ApertureNearAll MassGap.RectWilson

/-! ## 1. The kernel form -/

section Kernel

/-- `2 log a − log b ≤ ε ↔ e^{−ε} a² ≤ b` for `a, b > 0`. -/
theorem log_step_le_iff {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * Real.log a - Real.log b ≤ ε ↔ Real.exp (-ε) * a ^ 2 ≤ b := by
  have e : Real.log (Real.exp (-ε) * a ^ 2) = -ε + 2 * Real.log a := by
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos ha 2).ne', Real.log_exp, Real.log_pow]
    push_cast; ring
  rw [← Real.log_le_log_iff (by positivity) hb, e]
  constructor <;> intro h <;> linarith

/-- The cyclic integral of a slice kernel at a length `2(2j)`, `j ≥ 1`, is positive. -/
theorem cycT_pos (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) {j : ℕ} (hj : 1 ≤ j) :
    0 < cycT s T β (2 * (2 * j)) :=
  (ApertureWindow.cycT_pos_le s T hβ hj).1

/-- **The one-direction defect in kernel form**: at the side `n = 2^{k+2}`,
`D_s ≤ ε ↔ e^{−ε} cyc(kT_s, n)² ≤ cyc(kT_s, 2n)`. -/
theorem stepD_le_iff (s : Fin 4) {β ε : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    stepD (2 ^ (k + 2)) s β ≤ ε ↔
      Real.exp (-ε) * cycT s (tr (Ls (2 ^ (k + 2)) s) s) β (2 ^ (k + 2)) ^ 2
        ≤ cycT s (tr (Ls (2 ^ (k + 2)) s) s) β (2 * 2 ^ (k + 2)) := by
  have h1 : 0 < cycT s (tr (Ls (2 ^ (k + 2)) s) s) β (2 ^ (k + 2)) := by
    have h := cycT_pos s (tr (Ls (2 ^ (k + 2)) s) s) hβ (j := 2 ^ k) Nat.one_le_two_pow
    rwa [show 2 * (2 * 2 ^ k) = 2 ^ (k + 2) by ring] at h
  have h2 : 0 < cycT s (tr (Ls (2 ^ (k + 2)) s) s) β (2 * 2 ^ (k + 2)) := by
    have h := cycT_pos s (tr (Ls (2 ^ (k + 2)) s) s) hβ (j := 2 ^ (k + 1)) Nat.one_le_two_pow
    rwa [show 2 * (2 * 2 ^ (k + 1)) = 2 * 2 ^ (k + 2) by ring] at h
  exact log_step_le_iff h1 h2

/-- **The far input as a statement about the slice kernels**: eventually in `β`, at the physical side
`n = 2^{kPhys L β + 2}`, `cyc(kT_s, 2n) ≥ e^{−ε} cyc(kT_s, n)²` in every direction `s`. -/
def KernFar (L ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ s : Fin 4,
    Real.exp (-ε) * cycT s (tr (Ls (2 ^ (kPhys L β + 2)) s) s) β (2 ^ (kPhys L β + 2)) ^ 2
      ≤ cycT s (tr (Ls (2 ^ (kPhys L β + 2)) s) s) β (2 * 2 ^ (kPhys L β + 2))

/-- **`Far` is the kernel form.** -/
theorem far_iff_kernFar {L ε : ℝ} : Far L ε ↔ KernFar L ε := by
  unfold Far KernFar
  constructor
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ h0 s
    exact (stepD_le_iff s h0 _).1 (hβ s)
  · intro h
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ h0 s
    exact (stepD_le_iff s h0 _).2 (hβ s)

/-- **The kernel form gives the physical-side defect**, at `15 ε`. -/
theorem physDefect_of_kernFar {L ε : ℝ} (h : KernFar L ε) : ApertureBridge.PhysDefect L (15 * ε) :=
  physDefect_of_far (far_iff_kernFar.2 h)

/-- **The physical-side defect gives the kernel form**, at the same `δ`: each `D_s` is nonnegative and at most
the weighted sum `8 D₀ + 4 D₁ + 2 D₂ + D₃`. -/
theorem kernFar_of_physDefect {L δ : ℝ} (h : ApertureBridge.PhysDefect L δ) : KernFar L δ := by
  refine far_iff_kernFar.1 ?_
  unfold ApertureBridge.PhysDefect at h
  unfold Far
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ h0 s
  rw [defectW_eq] at hβ
  have n0 := ApertureWindow.stepD_phys_nonneg L 0 h0
  have n1 := ApertureWindow.stepD_phys_nonneg L 1 h0
  have n2 := ApertureWindow.stepD_phys_nonneg L 2 h0
  have n3 := ApertureWindow.stepD_phys_nonneg L 3 h0
  fin_cases s
  · show stepD _ 0 β ≤ δ; linarith
  · show stepD _ 1 β ≤ δ; linarith
  · show stepD _ 2 β ≤ δ; linarith
  · show stepD _ 3 β ≤ δ; linarith

end Kernel

/-! ## 2. The kernel form against a relative spectral gap -/

section Gap

variable {m : ℕ} (r : Fin (m + 1) → ℝ)

/-- **A relative gap bounds the excited weight**: `r_i ≤ ρ` for `i ≥ 1` gives `τ_n ≤ ρ^{n − m₀} τ_{m₀}`. -/
theorem tau_le_gap (hr : ∀ i, 0 ≤ r i) {ρ : ℝ} (hρ : ∀ i : Fin m, r i.succ ≤ ρ) {m₀ n : ℕ} (hn : m₀ ≤ n) :
    ApertureTwo.tau r n ≤ ρ ^ (n - m₀) * ApertureTwo.tau r m₀ := by
  unfold ApertureTwo.tau
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : r i.succ ^ n = r i.succ ^ (n - m₀) * r i.succ ^ m₀ := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hr _) (hρ i) _) (pow_nonneg (hr _) _)

/-- **A relative gap bounds the defect**: `2 log Z_n − log Z_{2n} ≤ 2 ρ^{n − m₀} τ_{m₀}`. -/
theorem stepDefect_le_gap (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) {ρ : ℝ} (hρ : ∀ i : Fin m, r i.succ ≤ ρ)
    {m₀ n : ℕ} (hn : m₀ ≤ n) :
    2 * Real.log (ApertureTwo.trZ r n) - Real.log (ApertureTwo.trZ r (2 * n))
      ≤ 2 * (ρ ^ (n - m₀) * ApertureTwo.tau r m₀) := by
  have h1 := ApertureTwo.stepDefect_le r hr0 hr n
  have h0 := ApertureTwo.tau_nonneg r hr n
  have h2 : Real.log (1 + ApertureTwo.tau r n) ≤ ApertureTwo.tau r n := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ApertureTwo.tau r n by linarith)
    linarith
  have h3 := tau_le_gap r hr hρ hn
  linarith

/-- **The defect forces a relative gap at its length**: a defect at most `ε` at length `n` gives
`r_iⁿ ≤ eᵋ − 1` for every excited level. -/
theorem excited_le_of_stepDefect (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) {n : ℕ} {ε : ℝ}
    (h : 2 * Real.log (ApertureTwo.trZ r n) - Real.log (ApertureTwo.trZ r (2 * n)) ≤ ε) (i : Fin m) :
    r i.succ ^ n ≤ Real.exp ε - 1 := by
  have ht := ApertureNearAll.tau_le_of_step r hr0 hr hr1 h
  have hs : r i.succ ^ n ≤ ApertureTwo.tau r n :=
    Finset.single_le_sum (f := fun j : Fin m => r j.succ ^ n) (fun j _ => pow_nonneg (hr _) _)
      (Finset.mem_univ i)
  linarith

end Gap

/-! ## 3. The single-scale reading -/

section OneScale

/-- The physical side of the torus `PhysDefect` reads at `β`. -/
def physLen (L β : ℝ) : ℝ := (2 : ℝ) ^ (kPhys L β + 2) * AsymptoticScaling.aRun 2 β

/-- The physical side lies in `(L/2, L]`, eventually in `β`. -/
theorem physLen_mem {L : ℝ} (hL : 0 < L) : ∀ᶠ β in atTop, physLen L β ∈ Ioc (L / 2) L := by
  filter_upwards [WeakCouplingWindow.eventually_aRun_le (N := 2) (by norm_num) (b := L / 4)
    (by positivity), eventually_gt_atTop (0 : ℝ)] with β ha hβ
  obtain ⟨h1, h2⟩ := physSide_spec (L := L) hβ (by linarith)
  exact ⟨by unfold physLen; linarith, h1⟩

/-- **The renormalization clause**: the defect at the physical side is, within every `η > 0` and eventually in
`β`, a function of the physical side alone. -/
def Scales (L : ℝ) (Ψ : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ β in atTop,
    |ZoomSelfScale.defectW 2 β (2 ^ (kPhys L β + 2)) - Ψ (physLen L β)| ≤ η

/-- **The single-scale clause**: the continuum defect is at most `δ` at every physical side in `(L/2, L]`. -/
def OneScale (L : ℝ) (Ψ : ℝ → ℝ) (δ : ℝ) : Prop := ∀ ℓ ∈ Ioc (L / 2) L, Ψ ℓ ≤ δ

/-- **The far input from one physical scale**: `Scales` and `OneScale` at `δ' < δ` give `PhysDefect L δ`. -/
theorem physDefect_of_oneScale {L : ℝ} (hL : 0 < L) {Ψ : ℝ → ℝ} {δ' δ : ℝ} (hlt : δ' < δ)
    (hS : Scales L Ψ) (h1 : OneScale L Ψ δ') : ApertureBridge.PhysDefect L δ := by
  unfold ApertureBridge.PhysDefect
  filter_upwards [hS (δ - δ') (by linarith), physLen_mem hL] with β hβ hm
  have hΨ := h1 _ hm
  have hb := (abs_le.1 hβ).2
  linarith

/-- **The massless unit fails the renormalization clause**: a Coulomb finite-size part admits no `Ψ` bounded on
`(L/2, L]` with `Scales L Ψ`. -/
theorem not_scales_of_coulomb {L κ a : ℝ} (hL : 0 < L) (hκ : 0 < κ) (ha : 0 < a)
    (h : ∀ (n : ℕ), 1 ≤ n → ∀ (x : ℝ), a ≤ x → κ * x⁻¹ ≤ EnergySeed.finiteSize 2 n x) {Ψ : ℝ → ℝ} {B : ℝ}
    (hB : OneScale L Ψ B) : ¬ Scales L Ψ := fun hS =>
  ApertureOne.not_physDefect_of_coulomb (δ := B + 1) hκ ha h
    (physDefect_of_oneScale hL (lt_add_one B) hS hB)

end OneScale

end MassGap.GapAttack

end

#print axioms MassGap.GapAttack.log_step_le_iff
#print axioms MassGap.GapAttack.stepD_le_iff
#print axioms MassGap.GapAttack.far_iff_kernFar
#print axioms MassGap.GapAttack.physDefect_of_kernFar
#print axioms MassGap.GapAttack.kernFar_of_physDefect
#print axioms MassGap.GapAttack.tau_le_gap
#print axioms MassGap.GapAttack.stepDefect_le_gap
#print axioms MassGap.GapAttack.excited_le_of_stepDefect
#print axioms MassGap.GapAttack.physLen_mem
#print axioms MassGap.GapAttack.physDefect_of_oneScale
#print axioms MassGap.GapAttack.not_scales_of_coulomb
