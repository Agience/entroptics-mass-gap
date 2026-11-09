import Mathlib
import MassGap.ApertureFinal
import MassGap.TorusCapstone
import MassGap.RectTransfer

/-!
# MassGap.ApertureNearAll — the near bound read in every state, and the far side as four slice doublings

`ApertureFinal.clay_final` takes three remainders: `ApertureTwo.NearOwn` (near), `∃ c > 0, RefPassageLow` (far,
volume) and `PhysDefect L (1/1000)` (far, defect). This module places three objects against them.

## 1. The model: the excited rows, the cyclic sector, the eigen-free defect (proved)

Eigenvalue ratios `r`, `r 0 = 1`, `0 ≤ r ≤ 1`; `q i j = |⟨i|Q|j⟩|²` (`ApertureFinal`).

* `exRead i b = Σ_{j ≥ 1} q_ij r_jᵇ`: the reading of the insertion pair at separation `b` started in state `i`,
  through the excited intermediate states. `NearAllModel K b`: `exRead i b ≤ K · vac b` in every state `i`.
* `nearAll_iff_rowBound`: at `1 ≤ K`, `NearAllModel K b ↔ RowBound K b`, the row bound of
  `ApertureFinal.lowSide_pair`. The vacuum row `i = 0` holds at every `K ≥ 1` (`exRead_zero_le`), so `K` is the
  near bound read in the excited states.
* `stepDefect_ge`: `log(1 + τ_n) ≤ 2 log Z_n − log Z_{2n}`. With `ApertureTwo.stepDefect_le` the eigen-free
  one-direction doubling defect and the excited weight `τ_n` bound each other within a factor `2`.
  `tau_le_of_step`: a defect at most `ε` gives `τ_n ≤ eᵋ − 1`.
* `model_low_of_step`: the one-direction defect at the long side `a` at most `ε` and `NearAllModel K b` give the
  lower side `(2 + K(eᵋ − 1))⁻¹ R_T ≤ R_∞` at `b ≤ a`. The model's readings here are not connected (`q 0 0`
  sits in `vac` and in `trW`); the volume clause of the pinned path reads connected readings.

The checker's question, whether `K` already follows from vacuum readings of higher order. In the amplitude form
(`Q` real symmetric) the vacuum four-point reading `⟨Ω|Q Tᵇ Q Tᶜ Q Tᵇ Q|Ω⟩` is the reflection-positive sum
`W4 = Σ_j r_jᶜ ψ_j²`, `ψ_j = Σ_i Q_ji Q_i0 r_iᵇ` (`W4`, `psi`).

* `W4_ge`: every excited component is bounded by it, `r_kᶜ ψ_k² ≤ W4`. At two levels
  `ψ_1 = Q_10 (Q_00 + Q_11 μᵇ)`, so once `Q_10 ≠ 0` a bound on vacuum four-point readings bounds `Q_11`, which is
  what `ApertureFinal.overlap_blind` (two-point only) left free.
* `sector_blind`: at three levels with the third state outside the vacuum's sector (`Q_02 = Q_12 = 0`), every
  vacuum reading at every list of gaps (`vacN`) is independent of `Q_22`. A computation (`numpy`, not proved)
  at `r = (1, 0.5, 0.6)`, `(a, b) = (12, 4)` gives connected torus over connected vacuum `1.004, 1.076, 9.18` at
  `Q_22 = 0.3, 3, 30`, unbounded in `Q_22`, while the vacuum readings do not move.

So the excited-row bound is a vacuum (near) statement on the sector the insertion generates from the vacuum, and
is not one on the states the insertion does not reach. What is left (argued, not built) is the weight of the
unreached sectors on the torus times their insertion matrix elements; for a bounded insertion the latter are at
most its norm, so that residue is a spectral (far) statement. `exRead 0 b` is the connected vacuum reading
`vac b − q_00`; a connected form of the torus side, `R_T − ⟨Q⟩_T²`, is not built here.

## 2. The tree: the near bound in every torus state (proved)

`NearAll hN βs M₀ s₀`: `NearOwn`'s bound, with its constant, holding in every periodic torus state
`torusState hN (2j + 1) (βs k)` of extent at least that of `stateT hN M₀ k` (`j ≥ M₀ 2ᵏ`), read against the same
vacuum own readings. `nearOwn_of_nearAll`: `NearAll ⇒ NearOwn`, by the limit `PeriodicState.tendsto_periodicState`
along `periodicUltra`, which is finer than `atTop`. `nearAll_stateT`: at `βs = dyBeta` the bound holds in
`stateT hN M₀ k` itself.

## 3. The tree: the far side as four slice-kernel doublings (proved)

`Ls n s`: extent `2n` in the directions below `s`, `n` in the others. The one-direction doubling in direction `s`
compares `Ls n s` with `Ls n (s + 1)`; both have the cross-section `tr (Ls n s) s` (`tr_Ls_succ`), so by
`RectTransfer.ZR_eq_cyc` both are cyclic integrals of the one slice kernel `kT s (tr (Ls n s) s)` at lengths `n`
and `2n` (`ZR_Ls`, `ZR_Ls_succ`). `stepD n s β = 2 log cyc(kT_s, n) − log cyc(kT_s, 2n)`, no eigenbasis.

* `defectW_eq`: `defectW 2 β n = 8 D₀ + 4 D₁ + 2 D₂ + D₃`, `D_s = stepD n s β`.
* `Far L ε`: eventually in `β`, at `n = 2^{kPhys L β + 2}`, every `D_s ≤ ε`.
* `physDefect_of_far`: `Far L ε ⇒ PhysDefect L (15 ε)`.

The cross-section changes with `s`: four slice kernels, one per direction, on four different slices.

## What is not built

`Far ∧ NearAll ⇒ RefPassageLow` is not built. Missing, typed: (i) the reference reading on `stateT` written as a
trace of `kT`-powers with two insertions in an eigenbasis of `kT` (an `L²`-spectral decomposition of a positive
continuous symmetric kernel on a compact group, with the trace formula `cyc kT n = Σ λᵢⁿ`): bookkeeping against
Mathlib; (ii) the infinite-volume reading `refReading` as the vacuum matrix element of one fixed kernel: the
periodic state is a limit of cubic tori whose cross-section grows with the extent, so no single `kT` carries it,
which is substantive; (iii) the connected form, the reference reading of `RefPassageLow` subtracts each state's own
one-point function (`TorusCapstone.connectedS`), while `NearAll` subtracts the vacuum's.

DERIVED (module-wide): `0`, `1` the vacuum index and its weight; `2` the doubling; `8, 4, 2, 1` the powers of `2`
weighting the four one-direction doublings in `16 = 2⁴`, summing to `15`; `3` the levels of the sector model.
-/

noncomputable section

namespace MassGap.ApertureNearAll

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint
  MassGap.PhysicalScaleSmall

/-! ## 1. The model -/

section Model

variable {m : ℕ} (r : Fin (m + 1) → ℝ) (q : Fin (m + 1) → Fin (m + 1) → ℝ)

/-- The reading started in state `i` through the excited intermediate states: `Σ_{j ≥ 1} q_ij r_jᵇ`. -/
def exRead (i : Fin (m + 1)) (b : ℕ) : ℝ := ∑ j : Fin m, q i j.succ * r j.succ ^ b

/-- The row bound of `ApertureFinal.lowSide_pair`. -/
def RowBound (K : ℝ) (b : ℕ) : Prop :=
  ∀ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b ≤ K * ApertureFinal.vac r q b

/-- **The near bound in every state**: the excited reading started in any state is at most `K` times the vacuum
reading. -/
def NearAllModel (K : ℝ) (b : ℕ) : Prop := ∀ i, exRead r q i b ≤ K * ApertureFinal.vac r q b

/-- The vacuum row: the excited part of the vacuum reading is at most the vacuum reading. -/
theorem exRead_zero_le (hr0 : r 0 = 1) (hq0 : ∀ i j, 0 ≤ q i j) (b : ℕ) :
    exRead r q 0 b ≤ ApertureFinal.vac r q b := by
  have h : ApertureFinal.vac r q b = q 0 0 + exRead r q 0 b := by
    simp [ApertureFinal.vac, exRead, Fin.sum_univ_succ, hr0]
  linarith [hq0 0 0]

/-- **The near bound in every state is the row bound.** -/
theorem nearAll_iff_rowBound (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hq0 : ∀ i j, 0 ≤ q i j) {K : ℝ}
    (hK : 1 ≤ K) (b : ℕ) : NearAllModel r q K b ↔ RowBound r q K b := by
  constructor
  · intro h i
    exact h i.succ
  · intro h i
    refine Fin.cases ?_ (fun i => h i) i
    have h1 := exRead_zero_le r q hr0 hq0 b
    have hv := ApertureFinal.vac_nonneg r q hr hq0 b
    nlinarith

/-- **The eigen-free defect bounds the excited weight**: `log(1 + τ_n) ≤ 2 log Z_n − log Z_{2n}`. -/
theorem stepDefect_ge (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) (n : ℕ) :
    Real.log (1 + ApertureTwo.tau r n)
      ≤ 2 * Real.log (ApertureTwo.trZ r n) - Real.log (ApertureTwo.trZ r (2 * n)) := by
  rw [ApertureTwo.trZ_eq r hr0, ApertureTwo.trZ_eq r hr0]
  have h2 : ApertureTwo.tau r (2 * n) ≤ ApertureTwo.tau r n :=
    ApertureFinal.tau_anti r hr hr1 (by omega)
  have h0 := ApertureTwo.tau_nonneg r hr (2 * n)
  have hl : Real.log (1 + ApertureTwo.tau r (2 * n)) ≤ Real.log (1 + ApertureTwo.tau r n) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- A defect at most `ε` gives the excited weight at most `eᵋ − 1`. -/
theorem tau_le_of_step (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) {n : ℕ} {ε : ℝ}
    (h : 2 * Real.log (ApertureTwo.trZ r n) - Real.log (ApertureTwo.trZ r (2 * n)) ≤ ε) :
    ApertureTwo.tau r n ≤ Real.exp ε - 1 := by
  have hg := stepDefect_ge r hr0 hr hr1 n
  have h0 := ApertureTwo.tau_nonneg r hr n
  have hl : Real.log (1 + ApertureTwo.tau r n) ≤ ε := hg.trans h
  have := (Real.log_le_iff_le_exp (by linarith)).mp hl
  linarith

/-- **The lower side from the eigen-free defect and the near bound in every state.** -/
theorem model_low_of_step (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hq : ∀ i j, q i j = q j i) (hq0 : ∀ i j, 0 ≤ q i j) {K ε : ℝ} (hK : 1 ≤ K) {a b : ℕ}
    (hab : b ≤ a)
    (hstep : 2 * Real.log (ApertureTwo.trZ r a) - Real.log (ApertureTwo.trZ r (2 * a)) ≤ ε)
    (hN : NearAllModel r q K b) :
    (2 + K * (Real.exp ε - 1))⁻¹ * (ApertureFinal.trW r q a b / ApertureTwo.trZ r (a + b))
      ≤ ApertureFinal.vac r q b :=
  ApertureFinal.lowSide_pair_of_tau r q hr0 hr hr1 hq hq0 (by linarith) hab
    ((nearAll_iff_rowBound r q hr0 hr hq0 hK b).mp hN) (tau_le_of_step r hr0 hr hr1 hstep)

end Model

section Amplitude

variable {m : ℕ} (Q : Fin (m + 1) → Fin (m + 1) → ℝ) (r : Fin (m + 1) → ℝ)

/-- The excited components of `Q Tᵇ Q |Ω⟩`: `ψ_j = Σ_i Q_ji Q_i0 r_iᵇ`. -/
def psi (b : ℕ) (j : Fin (m + 1)) : ℝ := ∑ i, Q j i * Q i 0 * r i ^ b

/-- The vacuum four-point reading `⟨Ω|Q Tᵇ Q Tᶜ Q Tᵇ Q|Ω⟩` in its reflection-positive form `Σ_j r_jᶜ ψ_j²`. -/
def W4 (b c : ℕ) : ℝ := ∑ j, r j ^ c * psi Q r b j ^ 2

/-- **Every excited component is bounded by the vacuum four-point reading.** -/
theorem W4_ge (hr : ∀ i, 0 ≤ r i) (b c : ℕ) (k : Fin (m + 1)) :
    r k ^ c * psi Q r b k ^ 2 ≤ W4 Q r b c :=
  Finset.single_le_sum (f := fun j => r j ^ c * psi Q r b j ^ 2)
    (fun j _ => mul_nonneg (pow_nonneg (hr j) c) (sq_nonneg _)) (Finset.mem_univ k)

/-- At two levels the excited component is `Q_10 (Q_00 + Q_11 μᵇ)`. -/
theorem psi_two (u v t μ : ℝ) (b : ℕ) :
    psi ![![u, v], ![v, t]] ![1, μ] b 1 = v * (u + t * μ ^ b) := by
  simp [psi, Fin.sum_univ_two]
  ring

end Amplitude

section Sector

/-- Three levels, the third outside the vacuum's sector.

DERIVED: `3` the levels of the sector model: the vacuum, one excited level in its sector, and one level outside
it, the fewest that show sector blindness. -/
def Q3 (u v s g : ℝ) : Fin 3 → Fin 3 → ℝ := ![![u, v, 0], ![v, s, 0], ![0, 0, g]]

/-- One insertion after a gap `g`: `w ↦ Q Tᵍ w`. DERIVED: `3` the levels of the sector model (`Q3`). -/
def stepV (Q : Fin 3 → Fin 3 → ℝ) (r : Fin 3 → ℝ) (g : ℕ) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ j, Q i j * (r j ^ g * w j)

/-- The insertions after a list of gaps. DERIVED: `3` the levels of the sector model (`Q3`). -/
def runV (Q : Fin 3 → Fin 3 → ℝ) (r : Fin 3 → ℝ) : List ℕ → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  | [], w => w
  | g :: gs, w => runV Q r gs (stepV Q r g w)

/-- The vacuum reading `⟨Ω|Q T^{g_k} Q ⋯ T^{g_1} Q|Ω⟩` at a list of gaps.
DERIVED: `3` the levels of the sector model (`Q3`); `0` the vacuum index. -/
def vacN (Q : Fin 3 → Fin 3 → ℝ) (r : Fin 3 → ℝ) (gs : List ℕ) : ℝ := runV Q r gs (fun i => Q i 0) 0

theorem stepV_sector (u v s g : ℝ) (r : Fin 3 → ℝ) (k : ℕ) {w : Fin 3 → ℝ} (hw : w 2 = 0) :
    stepV (Q3 u v s g) r k w = stepV (Q3 u v s 0) r k w ∧ stepV (Q3 u v s g) r k w 2 = 0 := by
  refine ⟨funext fun i => ?_, ?_⟩
  · fin_cases i <;> simp [stepV, Q3, Fin.sum_univ_three, hw]
  · simp [stepV, Q3, Fin.sum_univ_three, hw]

theorem runV_sector (u v s g : ℝ) (r : Fin 3 → ℝ) (gs : List ℕ) :
    ∀ w : Fin 3 → ℝ, w 2 = 0 → runV (Q3 u v s g) r gs w = runV (Q3 u v s 0) r gs w := by
  induction gs with
  | nil => intro w _; rfl
  | cons k gs ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := stepV_sector u v s g r k hw
    show runV _ r gs (stepV _ r k w) = runV _ r gs (stepV _ r k w)
    rw [h1]
    exact ih _ (h1 ▸ h2)

/-- **The vacuum readings do not see a state outside the vacuum's sector**: at every list of gaps the vacuum
reading is independent of `Q_22`. -/
theorem sector_blind (u v s g : ℝ) (r : Fin 3 → ℝ) (gs : List ℕ) :
    vacN (Q3 u v s g) r gs = vacN (Q3 u v s 0) r gs := by
  have h0 : (fun i => Q3 u v s g i 0) = fun i => Q3 u v s 0 i 0 := by
    funext i; fin_cases i <;> rfl
  unfold vacN
  rw [h0]
  exact congrFun (runV_sector u v s g r gs _ (by simp [Q3])) 0

end Sector

/-! ## 2. The tree: the near bound in every torus state -/

section TreeNear

variable {N : ℕ}

/-- The periodic torus state of extent `2(j + 1)` at the couplings `βs`. -/
def torusAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (j : ℕ) : ℕ → MassGap.DLRLimit.State (Cfg N) :=
  fun k => PeriodicState.torusState hN (2 * j + 1) (βs k)

/-- **The near bound in every torus state**: `NearOwn`'s bound, with one constant per list and margin, in every
periodic torus state of extent at least that of `stateT hN M₀ k`, against the vacuum own readings.

DERIVED: `8` in `8 * n` is `a⁸ = a⁴ · a⁴`, one cell volume per smeared field of a reflected pair
(`ScaleNorm`), one pair per insertion, as in `PointReadingRatio.PointRatioAlong`; `2` the doubling. -/
def NearAll (hN : N ≠ 0) (βs : ℕ → ℝ) (M₀ : ℕ) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ C : ℝ,
    ∀ᶠ k in atTop, ∀ j : ℕ, M₀ * 2 ^ k ≤ j → ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      TorusCapstone.latSkRS (torusAlong hN βs j) (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k

/-- **The near bound in every torus state gives `NearOwn`.** -/
theorem nearOwn_of_nearAll (hN : N ≠ 0) (βs : ℕ → ℝ) {M₀ : ℕ} {s₀ : ℝ} (h : NearAll hN βs M₀ s₀) :
    ApertureTwo.NearOwn hN βs s₀ := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  refine ⟨C, ?_⟩
  filter_upwards [hC] with k hk p hp
  have hev : ∀ᶠ j in ((PeriodicState.periodicUltra hN (βs k) : Ultrafilter ℕ) : Filter ℕ),
      M₀ * 2 ^ k ≤ j :=
    (eventually_ge_atTop _).filter_mono (PeriodicState.periodicUltra_le hN (βs k))
  exact le_of_tendsto ((PeriodicState.tendsto_periodicState hN (βs k) _).const_mul _)
    (hev.mono fun j hj => hk j hj p hp)

/-- At `βs = dyBeta`, `NearAll` holds in the volume clause's own torus `stateT hN M₀ k`. -/
theorem nearAll_stateT (hN : N ≠ 0) {M₀ : ℕ} {s₀ : ℝ}
    (h : NearAll hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀) (n : ℕ)
    (L : Fin n → LField (MassGap.SUN.SU N)) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, ∀ᶠ k in atTop, ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      TorusCapstone.latSkRS (TorusCapstone.stateT hN M₀)
          (rho1Along hN (dyBeta (one_le_of_ne_zero hN))) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n)
          * ∏ i, refReadingAlong hN (dyBeta (one_le_of_ne_zero hN)) (L i) s₀ s₀ k := by
  obtain ⟨C, hC⟩ := h n L d hd
  exact ⟨C, hC.mono fun k hk p hp => hk (M₀ * 2 ^ k) le_rfl p hp⟩

end TreeNear

/-! ## 3. The tree: the far side as four slice-kernel doublings -/

section TreeFar

open MassGap.RectWilson

/-- Extent `2n` in the directions below `s`, `n` in the others. -/
def Ls (n s : ℕ) : Fin 4 → ℕ := fun i => if (i : ℕ) < s then 2 * n else n

theorem Ls_zero (n : ℕ) : Ls n 0 = fun _ => n := by
  funext i; simp [Ls]

theorem Ls_four (n : ℕ) : Ls n 4 = fun _ => 2 * n := by
  funext i; simp [Ls, i.isLt]

theorem Ls_self (n : ℕ) (s : Fin 4) : Ls n s s = n := by simp [Ls]

theorem Ls_succ_self (n : ℕ) (s : Fin 4) : Ls n ((s : ℕ) + 1) s = 2 * n := by simp [Ls]

/-- **The two tori of a one-direction doubling share their cross-section.** -/
theorem tr_Ls_succ (n : ℕ) (s : Fin 4) : tr (Ls n ((s : ℕ) + 1)) s = tr (Ls n s) s := by
  funext j
  have h : (j.1 : ℕ) ≠ (s : ℕ) := fun h => j.2 (Fin.ext h)
  simp only [tr, Ls]
  split_ifs <;> omega

/-- The cyclic integral of the slice kernel of cross-section `T` in direction `s`, at length `m`. -/
def cycT (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) (β : ℝ) (m : ℕ) : ℝ :=
  CyclicKernel.cyc (RectTransfer.hS s T 2) (RectTransfer.kT s T 2 β) m

theorem cycT_congr {s : Fin 4} {T T' : {j : Fin 4 // j ≠ s} → ℕ} (h : T = T') (β : ℝ) (m : ℕ) :
    cycT s T β m = cycT s T' β m := by
  subst h; rfl

theorem ZR_Ls (n : ℕ) (s : Fin 4) (β : ℝ) : ZR (Ls n s) 2 β = cycT s (tr (Ls n s) s) β n := by
  rw [RectTransfer.ZR_eq_cyc (μ := s) (by norm_num) β, Ls_self]
  rfl

theorem ZR_Ls_succ (n : ℕ) (s : Fin 4) (β : ℝ) :
    ZR (Ls n ((s : ℕ) + 1)) 2 β = cycT s (tr (Ls n s) s) β (2 * n) := by
  rw [RectTransfer.ZR_eq_cyc (μ := s) (by norm_num) β, Ls_succ_self]
  exact cycT_congr (tr_Ls_succ n s) β (2 * n)

/-- **The one-direction doubling defect of the slice kernel**: `2 log cyc(kT_s, n) − log cyc(kT_s, 2n)` on the
cross-section `tr (Ls n s) s`. -/
def stepD (n : ℕ) (s : Fin 4) (β : ℝ) : ℝ :=
  2 * Real.log (cycT s (tr (Ls n s) s) β n) - Real.log (cycT s (tr (Ls n s) s) β (2 * n))

theorem step_eq (n : ℕ) (β : ℝ) (s : Fin 4) :
    2 * Real.log (ZR (Ls n s) 2 β) - Real.log (ZR (Ls n ((s : ℕ) + 1)) 2 β) = stepD n s β := by
  rw [ZR_Ls, ZR_Ls_succ]
  rfl

/-- **The Wilson doubling defect is four slice doublings**: `defectW = 8 D₀ + 4 D₁ + 2 D₂ + D₃`. -/
theorem defectW_eq (n : ℕ) (β : ℝ) :
    ZoomSelfScale.defectW 2 β n
      = 8 * stepD n 0 β + 4 * stepD n 1 β + 2 * stepD n 2 β + stepD n 3 β := by
  have h0 : 2 * Real.log (ZR (Ls n 0) 2 β) - Real.log (ZR (Ls n 1) 2 β) = stepD n 0 β := step_eq n β 0
  have h1 : 2 * Real.log (ZR (Ls n 1) 2 β) - Real.log (ZR (Ls n 2) 2 β) = stepD n 1 β := step_eq n β 1
  have h2 : 2 * Real.log (ZR (Ls n 2) 2 β) - Real.log (ZR (Ls n 3) 2 β) = stepD n 2 β := step_eq n β 2
  have h3 : 2 * Real.log (ZR (Ls n 3) 2 β) - Real.log (ZR (Ls n 4) 2 β) = stepD n 3 β := step_eq n β 3
  have e0 : ZR (fun _ => n) 2 β = ZR (Ls n 0) 2 β := by rw [Ls_zero]
  have e4 : ZR (fun _ => 2 * n) 2 β = ZR (Ls n 4) 2 β := by rw [Ls_four]
  unfold ZoomSelfScale.defectW
  rw [e0, e4, ← h0, ← h1, ← h2, ← h3]
  ring

/-- **The far statement**: eventually in `β`, at the physical side `n = 2^{kPhys L β + 2}`, each of the four
slice-kernel doubling defects is at most `ε`. -/
def Far (L ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ s : Fin 4, stepD (2 ^ (kPhys L β + 2)) s β ≤ ε

/-- **`Far` gives the physical-side defect**, at `15 ε`. -/
theorem physDefect_of_far {L ε : ℝ} (h : Far L ε) : ApertureBridge.PhysDefect L (15 * ε) := by
  filter_upwards [h] with β hβ
  rw [defectW_eq]
  linarith [hβ 0, hβ 1, hβ 2, hβ 3]

end TreeFar

end MassGap.ApertureNearAll

end

#print axioms MassGap.ApertureNearAll.exRead_zero_le
#print axioms MassGap.ApertureNearAll.nearAll_iff_rowBound
#print axioms MassGap.ApertureNearAll.stepDefect_ge
#print axioms MassGap.ApertureNearAll.tau_le_of_step
#print axioms MassGap.ApertureNearAll.model_low_of_step
#print axioms MassGap.ApertureNearAll.W4_ge
#print axioms MassGap.ApertureNearAll.psi_two
#print axioms MassGap.ApertureNearAll.sector_blind
#print axioms MassGap.ApertureNearAll.nearOwn_of_nearAll
#print axioms MassGap.ApertureNearAll.nearAll_stateT
#print axioms MassGap.ApertureNearAll.tr_Ls_succ
#print axioms MassGap.ApertureNearAll.ZR_Ls_succ
#print axioms MassGap.ApertureNearAll.defectW_eq
#print axioms MassGap.ApertureNearAll.physDefect_of_far
