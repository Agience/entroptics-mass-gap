import Mathlib
import MassGap.ApertureNearAll

/-!
# MassGap.ApertureWindow — the near bound in every torus state inside a window, and the doubling defect is nonnegative

Two objects against `ApertureNearAll`: the torus statement of the near bound with the window that makes it a
statement about the torus, and the sign of the four slice-kernel doubling defects.

## 1. The window (proved)

`ApertureNearAll.NearAll` reads a monomial at sites `p i : ℤ⁴` in `torusState hN (2j + 1)`. That state reads an
observable of `ℤ⁴` through `PeriodicState.torusObs` and `InfiniteLattice.pullback`, so every coordinate is taken
mod the extent `E = 2j + 2`. `ContinuumSep.sepPos` measures the separation of the supports in `ℤ⁴`. Over all
`p : Fin n → ISite` the two disagree: `p₂ = p₁ + E e₁` is separated in `ℤ⁴` and is the same torus site as `p₁`,
and a point at time `j + 1` is its own time reflection on the torus. At such `p` the torus reading is a
coincident-point reading, so `NearAll` with one constant `C` is false.

`NearAllW hN βs M₀ s₀`: `NearAll` with a window clause. For each list `L` and margin `d` there are a constant `C`
and a depth `D k` (the lattice-unit depth of the field supports at level `k`), and the bound is asked only at
sites with `4 (|p i ν| + D k) ≤ j` in every direction `ν`. Then every support and its time reflection lie in the
box `|x_ν| ≤ j/4`, whose differences are at most `j/2 < E/2`, so the box embeds in the torus and the torus
distance between any two of its points is their `ℤ⁴` distance: `sepPos` is the separation in the torus metric.

* `nearAllW_of_nearAll`: `NearAll ⇒ NearAllW` (at `D = 0`), so the window only weakens the hypothesis.
* `nearOwn_of_nearAllW`: `NearAllW ⇒ ApertureTwo.NearOwn`. For fixed `k` and `p` the window holds for all
  large `j`, so eventually along `periodicUltra` (finer than `atTop`, `periodicUltra_le`), and the limit
  `tendsto_periodicState` carries the bound to the periodic state.
* `nearAllW_stateT`: at `βs = dyBeta` the bound holds in `stateT hN M₀ k` itself, at the sites of the window
  `4 (|p i ν| + D k) ≤ M₀ 2ᵏ`.

At the free unit `NearAllW` is plausible (argued, not built). Inside the window a finite torus reading differs
from the infinite-volume one by images at distance at least `E/2` and by the vacuum subtraction, which adds
`(⟨O⟩_T − ⟨O⟩_∞)²`-type terms. At fixed physical side these scale like the reading itself: for a massive free
field they are exponentially small in `m E a`; for a massless field with the zero mode removed they are `O(1)`
relative to the reading, which a constant `C` absorbs.

## 2. The sign of the doubling defect (proved)

`ApertureNearAll.stepD n s β = 2 log cyc(kT_s, n) − log cyc(kT_s, 2n)`, no eigenbasis. At `n = 2j`, `j ≥ 1`,
`β ≥ 0`, with `kT` symmetric (`kT_symm`) and bounded (`bdd_kT`):

* `cyc(kT, 2j) = hs(kT^{∗j})` (`CyclicKernel.cyc_even`);
* `cyc(kT, 4j) = hs(kT^{∗2j}) = hs(kT^{∗j} ∗ kT^{∗j})` (`KernelPower.iter_add`) `≤ hs(kT^{∗j})²`
  (`KernelPower.hs_conv_le_mul`);
* `cyc(kT, 4j) > 0`: `kT ≥ kTmin > 0` (`kT_lower`, `kTmin_pos`) gives `kT^{∗i} ≥ kTminⁱ` pointwise
  (`iter_ge`), so `hs ≥ kTmin^{4j} > 0` (`hs_ge`).

So `stepD_nonneg`: `0 ≤ stepD (2j) s β`; `stepD_phys_nonneg` at the physical side `n = 2^{kPhys L β + 2}`;
`defectW_nonneg`: `0 ≤ defectW 2 β (2^{kPhys L β + 2})` (`ApertureNearAll.defectW_eq`). The converse of
`ApertureNearAll.physDefect_of_far`, `far_of_physDefect : PhysDefect L δ ⇒ Far L δ`, holds because each weight
of `8 D₀ + 4 D₁ + 2 D₂ + D₃` is at least `1` and every `D_s ≥ 0`. With `physDefect_of_far`, `Far` and
`PhysDefect` are equivalent up to the factor `15` (`far_iff_physDefect`).

DERIVED (module-wide): `4` in the window is the quarter, so the box `|x_ν| ≤ j/4` has diameter `j/2 < E/2`, and
`4` in `Fin 4` is the spacetime dimension; `0` the depth that recovers `NearAll`; `2` the doubling and the even length `2j`; `1` the least `j`
and the least weight; `8, 4, 2, 1` and `15` from `ApertureNearAll.defectW_eq`; `0, 1, 2, 3` the four directions.
-/

noncomputable section

namespace MassGap.ApertureWindow

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint
  MassGap.PhysicalScaleSmall MassGap.ApertureNearAll

/-! ## 1. The window -/

section Window

variable {N : ℕ}

/-- **The near bound in every torus state, inside the window.** `NearAll` asked only at sites `p` with
`4 (|p i ν| + D k) ≤ j` in every direction, `D k` the lattice-unit depth of the field supports at level `k`.
The window is needed because `torusState hN (2j + 1)` reads `ℤ⁴` observables mod the extent `2j + 2`, while
`sepPos` separates in `ℤ⁴`: without it, translates by the extent and points reflecting onto their own slice
are separated in `ℤ⁴` and coincide on the torus. Inside the window the supports and their reflections lie in a
box of half-width `j/4`, which embeds isometrically in the torus.

DERIVED: `8` in `8 * n` inherited from `ApertureNearAll.NearAll`, `a⁸ = a⁴ · a⁴`, one cell volume per
smeared field of a reflected pair; `4` the quarter of the window; `2` the doubling. -/
def NearAllW (hN : N ≠ 0) (βs : ℕ → ℝ) (M₀ : ℕ) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ (C : ℝ) (D : ℕ → ℕ),
    ∀ᶠ k in atTop, ∀ j : ℕ, M₀ * 2 ^ k ≤ j → ∀ p : Fin n → ISite,
      (∀ i ν, 4 * (|p i ν| + (D k : ℤ)) ≤ (j : ℤ)) →
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      TorusCapstone.latSkRS (torusAlong hN βs j) (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k

/-- The window only weakens the hypothesis: `NearAll ⇒ NearAllW`, at depth `0`. -/
theorem nearAllW_of_nearAll (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ} (h : NearAll hN βs M₀ s₀) :
    NearAllW hN βs M₀ s₀ := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  exact ⟨C, fun _ => 0, hC.mono fun k hk j hj p _ hp => hk j hj p hp⟩

/-- For fixed `k` and sites `p`, the window holds for all large extents. -/
theorem window_eventually {n : ℕ} (p : Fin n → ISite) (D : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ i ν, 4 * (|p i ν| + (D : ℤ)) ≤ (j : ℤ) := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro ν
  filter_upwards [eventually_ge_atTop (4 * (|p i ν| + (D : ℤ))).toNat] with j hj
  exact (Int.self_le_toNat _).trans (by exact_mod_cast hj)

/-- **The near bound inside the window gives `NearOwn`.** -/
theorem nearOwn_of_nearAllW (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ} (h : NearAllW hN βs M₀ s₀) :
    ApertureTwo.NearOwn hN βs s₀ := by
  intro n L d hd
  obtain ⟨C, D, hC⟩ := h n L d hd
  refine ⟨C, ?_⟩
  filter_upwards [hC] with k hk p hp
  have hev : ∀ᶠ j in ((PeriodicState.periodicUltra hN (βs k) : Ultrafilter ℕ) : Filter ℕ),
      M₀ * 2 ^ k ≤ j ∧ ∀ i ν, 4 * (|p i ν| + (D k : ℤ)) ≤ (j : ℤ) :=
    ((eventually_ge_atTop _).and (window_eventually p (D k))).filter_mono
      (PeriodicState.periodicUltra_le hN (βs k))
  exact le_of_tendsto ((PeriodicState.tendsto_periodicState hN (βs k) _).const_mul _)
    (hev.mono fun j hj => hk j hj.1 p hj.2 hp)

/-- At `βs = dyBeta`, `NearAllW` holds in the volume clause's own torus `stateT hN M₀ k`, at the sites of the
window of extent `M₀ 2ᵏ`. -/
theorem nearAllW_stateT (hN : N ≠ 0) {M₀ : ℕ} {s₀ : ℝ}
    (h : NearAllW hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀) (n : ℕ)
    (L : Fin n → LField (MassGap.SUN.SU N)) {d : ℝ} (hd : 0 < d) :
    ∃ (C : ℝ) (D : ℕ → ℕ), ∀ᶠ k in atTop, ∀ p : Fin n → ISite,
      (∀ i ν, 4 * (|p i ν| + (D k : ℤ)) ≤ ((M₀ * 2 ^ k : ℕ) : ℤ)) →
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      TorusCapstone.latSkRS (TorusCapstone.stateT hN M₀)
          (rho1Along hN (dyBeta (one_le_of_ne_zero hN))) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n)
          * ∏ i, refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) (L i) s₀ s₀ k := by
  obtain ⟨C, D, hC⟩ := h n L d hd
  exact ⟨C, D, hC.mono fun k hk p hw hp => hk (M₀ * 2 ^ k) le_rfl p hw hp⟩

end Window

/-! ## 2. The sign of the doubling defect -/

section KernelPos

open MeasureTheory MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **A kernel bounded below by `c ≥ 0` has its `(i+1)`-fold power bounded below by `c^{i+1}`.** -/
theorem iter_ge {k : X → X → ℝ} (hk : Bdd k) {c : ℝ} (hc : 0 ≤ c) (hkc : ∀ x y, c ≤ k x y) :
    ∀ i x z, c ^ (i + 1) ≤ iter μ k i x z
  | 0, x, z => by simpa [iter] using hkc x z
  | i + 1, x, z => by
    obtain ⟨Ck, hCk⟩ := hk.bdd
    obtain ⟨Ci, hCi⟩ := (hk.iter (μ := μ) i).bdd
    have hg : Integrable (fun y => k x y * iter μ k i y z) μ := by
      refine integrable_of_bdd ((hk.row x).mul ((hk.iter (μ := μ) i).col z)) (C := Ck * Ci) (fun y => ?_)
      rw [abs_mul]
      exact mul_le_mul (hCk x y) (hCi y z) (abs_nonneg _) ((abs_nonneg _).trans (hCk x y))
    have hm : (fun _ : X => c ^ (i + 1 + 1)) ≤ fun y => k x y * iter μ k i y z := fun y => by
      have h1 := hkc x y
      have h2 := iter_ge hk hc hkc i y z
      calc c ^ (i + 1 + 1) = c * c ^ (i + 1) := by ring
        _ ≤ k x y * iter μ k i y z := mul_le_mul h1 h2 (by positivity) (hc.trans h1)
    have hint := integral_mono (integrable_const (c ^ (i + 1 + 1))) hg hm
    have hconst : ∫ _ : X, c ^ (i + 1 + 1) ∂μ = c ^ (i + 1 + 1) := by simp
    rw [hconst] at hint
    exact hint

/-- **A kernel bounded below by `c ≥ 0` has squared Hilbert–Schmidt norm at least `c²`.** -/
theorem hs_ge {h : X → X → ℝ} (hh : Bdd h) {c : ℝ} (hc : 0 ≤ c) (hhc : ∀ x z, c ≤ h x z) :
    c ^ 2 ≤ hs μ h := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hsq : ∀ x z, |h x z ^ 2| ≤ C ^ 2 := fun x z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x z) 2
  have hin : ∀ x, c ^ 2 ≤ ∫ z, h x z ^ 2 ∂μ := fun x => by
    have hint := integral_mono (integrable_const (μ := μ) (c ^ 2))
      (integrable_of_bdd ((hh.row x).pow_const 2) (hsq x))
      (fun z => pow_le_pow_left₀ hc (hhc x z) 2)
    have hconst : ∫ _ : X, c ^ 2 ∂μ = c ^ 2 := by simp
    rw [hconst] at hint
    exact hint
  have hAm : Measurable (fun x => ∫ z, h x z ^ 2 ∂μ) :=
    measurable_integral_right (μ := μ) (F := fun x z => h x z ^ 2) (hh.meas.pow_const 2)
  have hint := integral_mono (integrable_const (μ := μ) (c ^ 2))
    (integrable_of_bdd hAm (fun x => abs_integral_le fun z => hsq x z)) hin
  have hconst : ∫ _ : X, c ^ 2 ∂μ = c ^ 2 := by simp
  rw [hconst] at hint
  exact hint

end KernelPos

section Defect

open MassGap.RectWilson MassGap.KernelPower MassGap.CyclicKernel

/-- **The cyclic integral at `4j` is positive and at most the square of the one at `2j`.** -/
theorem cycT_pos_le (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) {β : ℝ} (hβ : 0 ≤ β) {j : ℕ}
    (hj : 1 ≤ j) :
    0 < cycT s T β (2 * (2 * j)) ∧ cycT s T β (2 * (2 * j)) ≤ cycT s T β (2 * j) ^ 2 := by
  have hN : (2 : ℕ) ≠ 0 := by norm_num
  have hk := RectTransfer.bdd_kT (μ := s) (T := T) hN hβ
  unfold cycT
  rw [cyc_even hk (RectTransfer.kT_symm β) (2 * j) (by omega),
    cyc_even hk (RectTransfer.kT_symm β) j hj]
  unfold traceSeq
  rw [show 2 * (2 * j) / 2 - 1 = (j - 1) + (j - 1) + 1 by omega, show 2 * j / 2 - 1 = j - 1 by omega]
  have hc := RectTransfer.kTmin_pos (μ := s) (T := T) β
  refine ⟨?_, ?_⟩
  · have hge := hs_ge (μ := RectTransfer.hS s T 2) (hk.iter (μ := RectTransfer.hS s T 2) _) (pow_nonneg hc.le _)
      (iter_ge hk hc.le (RectTransfer.kT_lower hN hβ) ((j - 1) + (j - 1) + 1))
    exact lt_of_lt_of_le (by positivity) hge
  · rw [iter_add hk, sq]
    exact hs_conv_le_mul (hk.iter _) (hk.iter _)

/-- **The one-direction doubling defect is nonnegative** at even length `2j`, `β ≥ 0`, without an eigenbasis. -/
theorem stepD_nonneg (s : Fin 4) {β : ℝ} (hβ : 0 ≤ β) {j : ℕ} (hj : 1 ≤ j) : 0 ≤ stepD (2 * j) s β := by
  obtain ⟨hpos, hle⟩ := cycT_pos_le s (tr (Ls (2 * j) s) s) hβ hj
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  unfold stepD
  push_cast at hlog
  linarith

/-- The one-direction defect at the physical side `n = 2^{kPhys L β + 2}` is nonnegative. -/
theorem stepD_phys_nonneg (L : ℝ) (s : Fin 4) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ stepD (2 ^ (kPhys L β + 2)) s β := by
  have e : 2 ^ (kPhys L β + 2) = 2 * 2 ^ (kPhys L β + 1) := by ring
  rw [e]
  exact stepD_nonneg s hβ Nat.one_le_two_pow

/-- **The Wilson doubling defect at the physical side is nonnegative.** -/
theorem defectW_nonneg (L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ZoomSelfScale.defectW 2 β (2 ^ (kPhys L β + 2)) := by
  rw [defectW_eq]
  linarith [stepD_phys_nonneg L 0 hβ, stepD_phys_nonneg L 1 hβ, stepD_phys_nonneg L 2 hβ,
    stepD_phys_nonneg L 3 hβ]

/-- **The physical-side defect gives `Far`**, at the same `δ`: each weight is at least `1` and every one-direction
defect is nonnegative. -/
theorem far_of_physDefect {L δ : ℝ} (h : ApertureBridge.PhysDefect L δ) : Far L δ := by
  filter_upwards [h, eventually_ge_atTop 0] with β hβ hβ0
  rw [defectW_eq] at hβ
  have h0 := stepD_phys_nonneg L 0 hβ0
  have h1 := stepD_phys_nonneg L 1 hβ0
  have h2 := stepD_phys_nonneg L 2 hβ0
  have h3 := stepD_phys_nonneg L 3 hβ0
  intro s
  have key : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
    rcases s with ⟨v, hv⟩
    interval_cases v <;> simp
  rcases key with rfl | rfl | rfl | rfl <;> linarith

/-- **`Far` and `PhysDefect` are equivalent up to the factor `15`.** -/
theorem far_iff_physDefect (L ε : ℝ) :
    (Far L ε → ApertureBridge.PhysDefect L (15 * ε)) ∧ (ApertureBridge.PhysDefect L ε → Far L ε) :=
  ⟨physDefect_of_far, far_of_physDefect⟩

end Defect

end MassGap.ApertureWindow

end

#print axioms MassGap.ApertureWindow.nearAllW_of_nearAll
#print axioms MassGap.ApertureWindow.window_eventually
#print axioms MassGap.ApertureWindow.nearOwn_of_nearAllW
#print axioms MassGap.ApertureWindow.nearAllW_stateT
#print axioms MassGap.ApertureWindow.iter_ge
#print axioms MassGap.ApertureWindow.hs_ge
#print axioms MassGap.ApertureWindow.cycT_pos_le
#print axioms MassGap.ApertureWindow.stepD_nonneg
#print axioms MassGap.ApertureWindow.stepD_phys_nonneg
#print axioms MassGap.ApertureWindow.defectW_nonneg
#print axioms MassGap.ApertureWindow.far_of_physDefect
#print axioms MassGap.ApertureWindow.far_iff_physDefect
