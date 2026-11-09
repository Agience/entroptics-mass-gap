import Mathlib
import MassGap.OneInput
import MassGap.WindowFreq

/-!
# MassGap.ReadSaturates — a reading is readable only if the shared free-energy read of a window saturates

The author's principle: "Entropy of neighbourhoods correlate … a window that is related to its neighbour will not have a
significant divergence", and "In RF, the signal is only readable if it saturates." This module formalises it on
the tree's window read and composes it with the capstone `OneInput.clayStatement_of_noCriticalPoint`.
Declarations are in the namespace `MassGap.ReadSaturates`.

## 1. The read: the free-energy form of the information the 16 sub-windows share

`freeI_XY N β w = log ZR((2n)⁴) − 16 log ZR(n⁴)`, `n = 2^w`, is `− windowCoupling N β w`: the free energy the
doubled window carries beyond its `16` sub-windows read as independent copies. The name follows the entroptics
library (`entropy.joint_entropies`, whose mutual information is `I_XY = H(X) + H(Y) − H(X,Y)`, never a bare `I`);
the prefix `free` marks that this is the free-energy (Gibbs-variational) form of a shared information, not the
Shannon `I_XY` of the block marginals.

What is exactly true, and what is proved here:

* Proved (`freeI_XY_eq`, `freeI_XY_zero`, `hasDerivAt_freeI_XY`): the closed form above; at the ultralocal
  coupling `β = 0` every window shares nothing (`freeI_XY N 0 w = 0`); its `β`-derivative is the cut energy,
  `16 ⟨S⟩_n − ⟨S⟩_{2n}` with the sign of `EffectiveCoupling.meanAction` (from
  `CouplingTower.hasDerivAt_windowCoupling`). So the read is the cut energy accumulated from the ultralocal point:
  the thermodynamic-integration form of the shared free energy.
* Not proved here, stated plainly: the relative-entropy form. With `μ` the Gibbs state on the doubled torus and `ν`
  the product of `16` side-`n` Gibbs states on the blocks of links (each block re-wrapped as a side-`n` torus), and
  `ΔS = S_{2n} − Σ_b S_n(U_b)` the cut action, the Gibbs variational principle gives the identity
  `− freeI_XY = D(μ ‖ ν) + β ⟨ΔS⟩_μ`, and `D(μ ‖ ν) = TC_μ + Σ_b D(μ_b ‖ μ_n)` with `TC_μ` the total correlation of
  the `16` blocks (the many-part `I_XY`). So the read equals the Shannon shared information only up to the cut
  energy and the marginal mismatch; between the two Gibbs states one has the two-sided Bogoliubov bound
  `−β ⟨ΔS⟩_ν ≤ freeI_XY ≤ −β ⟨ΔS⟩_μ`. The block factorisation `ZR(n⁴)^16 = ∫ e^{β Σ_b S_n(U_b)} dHaar_{2n}` that
  these need is not in the tree, so none of these is a theorem here.
* The read is nonpositive for `β ≥ 0` (`CouplingTower.windowCoupling_nonneg`), so it is a free-energy deficit, not a
  Shannon information.

## 2. The principle

* `SaturatesSeq r`: the read has a finite limit as the window opens.
* `ReadableSeq r`: it saturates at a level `c ≥ 0`. The `0` is the value of the ultralocal read (`freeI_XY_zero`); since
  `freeI_XY ≤ 0` for `β ≥ 0` and `w ≥ 1` (`CouplingTower.windowCoupling_nonneg`), a nonnegative level is exactly the
  level `0`. It is derived, not chosen.
* `Readable N β := ReadableSeq (freeI_XY N β)`, `ReadabilityPrinciple N := ∀ β ≥ 0, Readable N β`.

Mere saturation is not enough, plainly. A constant offset in the free energy, `log Z(2^w) = 16^w f + k`, has the
read `freeI_XY = −15 k` at every window (`offset_read`): it saturates, and for `k > 0` (a component shared across
all scales: long-range order, degenerate vacua) at a negative level. The tree does not exclude a saturation at a
level `≤ −1/1000` (`level_le_of_not_vanishes`). Saturation at any level above `−1/1000` gives the vanishing read
(`vanishes_of_tendsto_gt`, via the inherited seed); the form that works without an inherited constant in its
statement is saturation at a nonnegative level, `ReadableSeq`.

## 3. The proved chain

`Readable N β ⇒ Vanishes N β` at `β ≥ 0` (`vanishes_of_readable`; the seed basin forces the level to `0`), and the
converse (`readable_iff_vanishes`). Hence `ReadabilityPrinciple N ↔ StrongAnchor.NoStall N`
(`readabilityPrinciple_iff_noStall`), `ReadabilityPrinciple N ⇒ DisclosureFloor.NoCriticalPoint N`
(`noCriticalPoint_of_readabilityPrinciple`), and `clayStatement_of_readable`: the principle and the residual `hR` of
`OneInput` give `ClayStatementOf (SU N)`.

Plainly: `readable_iff_vanishes` is an equivalence, so the readability principle is the bridge `NoStall N` stated
as a saturation of the shared read. Restating it is not discharging it. The principle is a postulate about which
signals are readable (the observer's aperture principle), not a theorem about the Wilson measure; the Clay
statement needs it proved for the lattice measure at every `β ≥ 0`, and nothing in this module or the tree proves
it at `β` beyond the strong-coupling anchor.

## 4. Load tests

* Free massive chain (`free_massive_readable`): the shared read `−WindowFreq.defect m` saturates at `0`.
* Free massless chain (`free_massless_closed`, `free_massless_diverges`, `free_massless_not_readable`): the shared
  read is `log L − log 2`; it grows without bound, logarithmically, and is not readable. Critical = not readable (the free chain's read diverges upward; the Wilson read is
  nonpositive, so a failure there is a negative level or divergence to `−∞`).
* Offset (`offset_read`, `offset_readable_iff`): saturates at `−15 k`; readable exactly when `k ≤ 0`.
* Strong-coupling anchor (`readable_zero`, `readable_anchor`): readable at `β = 0` and on some `[0, β₀)`.

DERIVED (module-wide): `0` the ultralocal coupling, the ultralocal value and the upper bound of the read; `16 = 2⁴` the copies and `2` the doubling; `15 = 16 − 1` the offset's count; `1` the least window
index. Inherited, not derived here: `1/1000` the seed of `DoublingSharp` (through `StrongAnchor.vanishes_iff_seed`),
which enters `vanishes_of_tendsto_gt` and `level_le_of_not_vanishes` and no statement of the principle.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ReadSaturates

open Filter Topology
open MassGap.StrongAnchor (Vanishes)
open MassGap.CouplingTower (windowCoupling)

/-! ## 1. The read -/

/-- **The shared read**: the free energy the doubled window carries beyond its `16` sub-windows,
`log ZR((2n)⁴) − 16 log ZR(n⁴)`, `n = 2^w`. The free-energy form of a shared information (module docstring).
DERIVED: `16 = 2⁴` the copies; `2` the doubling. -/
def freeI_XY (N : ℕ) (β : ℝ) (w : ℕ) : ℝ := - windowCoupling N β w

/-- **Closed form.** DERIVED: `16 = 2⁴` the copies; `2` the doubling. -/
theorem freeI_XY_eq (N : ℕ) (β : ℝ) (w : ℕ) :
    freeI_XY N β w = Real.log (RectWilson.ZR (fun _ => 2 * 2 ^ w) N β)
      - 16 * Real.log (RectWilson.ZR (fun _ => 2 ^ w) N β) := by
  unfold freeI_XY windowCoupling ZoomSelfScale.defectW
  ring

/-- **The ultralocal window shares nothing.** DERIVED: `0` the ultralocal coupling. -/
theorem freeI_XY_zero (N w : ℕ) : freeI_XY N 0 w = 0 := by
  simp [freeI_XY, CouplingTower.windowCoupling_zero]

/-- **The `β`-derivative of the shared read is the cut energy** `16 ⟨S⟩_n − ⟨S⟩_{2n}` (in the sign of
`EffectiveCoupling.meanAction`). DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem hasDerivAt_freeI_XY {N : ℕ} (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (fun x => freeI_XY N x w)
      (16 * EffectiveCoupling.meanAction N (fun _ => 2 ^ w) β
        - EffectiveCoupling.meanAction N (fun _ => 2 * 2 ^ w) β) β := by
  have h : HasDerivAt (fun x => freeI_XY N x w)
      (-(EffectiveCoupling.meanAction N (fun _ => 2 * 2 ^ w) β
        - 16 * EffectiveCoupling.meanAction N (fun _ => 2 ^ w) β)) β :=
    (CouplingTower.hasDerivAt_windowCoupling hN w β).neg
  convert h using 1
  ring

/-! ## 2. The principle -/

/-- **Saturation**: the read has a finite limit as the window opens. DERIVED: no numeral. -/
def SaturatesSeq (r : ℕ → ℝ) : Prop := ∃ c : ℝ, Tendsto r atTop (𝓝 c)

/-- **Readable**: the shared read saturates at a nonnegative level. DERIVED: `0` the ultralocal value and the upper
bound of the read. -/
def ReadableSeq (r : ℕ → ℝ) : Prop := ∃ c : ℝ, 0 ≤ c ∧ Tendsto r atTop (𝓝 c)

/-- **The window read is readable at `β`.** DERIVED: no numeral. -/
def Readable (N : ℕ) (β : ℝ) : Prop := ReadableSeq (freeI_XY N β)

/-- **The readability principle**: the shared read saturates at every coupling. A postulate about which signals
are readable (the observer's aperture principle), not a theorem about the Wilson measure.
DERIVED: `0` the lower end. -/
def ReadabilityPrinciple (N : ℕ) : Prop := ∀ β : ℝ, 0 ≤ β → Readable N β

theorem ReadableSeq.saturates {r : ℕ → ℝ} (h : ReadableSeq r) : SaturatesSeq r :=
  let ⟨c, _, hc⟩ := h
  ⟨c, hc⟩

/-! ## 3. The chain -/

variable {N : ℕ}

/-- **Saturation above the seed's negative gives the vanishing read**: the seed basin then forces the level to `0`.
Inherited: `1/1000` the seed of `DoublingSharp`. DERIVED: `1` the least window index; `1/1000` the
sharp seed threshold of `DoublingSharp.rec_sharp`. -/
theorem vanishes_of_tendsto_gt (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {c : ℝ}
    (h : Tendsto (freeI_XY N β) atTop (𝓝 c)) (hc : -(1 / 1000) < c) : Vanishes N β := by
  have hw : Tendsto (windowCoupling N β) atTop (𝓝 (-c)) := by
    have h' := h.neg
    have e : (fun x => -freeI_XY N β x) = windowCoupling N β := funext fun x => by simp [freeI_XY]
    rw [e] at h'
    exact h'
  have hlt : -c < 1 / 1000 := by linarith
  obtain ⟨w, hwlt, hw1⟩ :=
    ((hw.eventually (eventually_lt_nhds hlt)).and (eventually_ge_atTop (1 : ℕ))).exists
  exact (StrongAnchor.vanishes_iff_seed hN hβ).mpr ⟨w, hw1, hwlt⟩

/-- **Where the read fails, any saturation is at a level `≤ −1/1000`**: the only escape left by the tree.
Inherited: `1/1000` the seed. -/
theorem level_le_of_not_vanishes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (hv : ¬ Vanishes N β) {c : ℝ}
    (h : Tendsto (freeI_XY N β) atTop (𝓝 c)) : c ≤ -(1 / 1000) :=
  le_of_not_gt fun hc => hv (vanishes_of_tendsto_gt hN hβ h hc)

/-- **Readable gives the vanishing read.** DERIVED: `0` the lower end. -/
theorem vanishes_of_readable (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : Readable N β) : Vanishes N β := by
  obtain ⟨c, hc0, hc⟩ := h
  exact vanishes_of_tendsto_gt hN hβ hc (by linarith)

/-- **The vanishing read is readable (at level `0`).** DERIVED: `0` the level. -/
theorem readable_of_vanishes {β : ℝ} (h : Vanishes N β) : Readable N β :=
  ⟨0, le_rfl, by
    have h' := h.neg
    rw [neg_zero] at h'
    exact h'⟩

/-- **Readable is the vanishing read**, at `β ≥ 0`. So the principle restates the bridge; it does not discharge
it. DERIVED: `0` the lower end. -/
theorem readable_iff_vanishes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : Readable N β ↔ Vanishes N β :=
  ⟨vanishes_of_readable hN hβ, readable_of_vanishes⟩

/-- **The principle is no stall.** DERIVED: `0` the lower end. -/
theorem readabilityPrinciple_iff_noStall (hN : N ≠ 0) : ReadabilityPrinciple N ↔ StrongAnchor.NoStall N := by
  rw [StrongAnchor.noStall_iff hN]
  exact forall₂_congr fun β hβ => readable_iff_vanishes hN hβ

/-- **The principle gives no critical point.** DERIVED: `0` the lower end. -/
theorem noCriticalPoint_of_readabilityPrinciple (hN : N ≠ 0) (h : ReadabilityPrinciple N) :
    DisclosureFloor.NoCriticalPoint N :=
  (DisclosureFloor.noStall_iff_noCriticalPoint hN).mp ((readabilityPrinciple_iff_noStall hN).mp h)

/-- **The root at `SU(N)` from the readability principle and the residual of `OneInput`.** The principle is a
postulate (the observer's aperture principle), equivalent to `StrongAnchor.NoStall N`; the residual carries the
ultraviolet and existence inputs (`OneInput` docstring). DERIVED: `0` the limit `0⁺`; `2` the least rank. -/
theorem clayStatement_of_readable [NeZero N] [Fact (2 ≤ N)] (hP : ReadabilityPrinciple N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower.CouplingTower N u₀ βs id →
      MeasuredTower.MeasTowerG (MassGap.SUN.SU N) βs ∧ ConstantPhysicsLine.ExistAlong N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  OneInput.clayStatement_of_noCriticalPoint (noCriticalPoint_of_readabilityPrinciple (NeZero.ne N) hP) hR

/-! ## 4. Load tests -/

/-- **Free massive chain: readable** (saturates at `0`). DERIVED: `0` the level and the mass sign. -/
theorem free_massive_readable {m : ℝ} (hm : 0 < m) : ReadableSeq (fun L => - WindowFreq.defect m L) :=
  ⟨0, le_rfl, by simpa using (WindowFreq.tendsto_defect_massive hm).neg⟩

/-- **Free massless chain: the shared read is `log L − log 2`**, logarithmic growth. DERIVED: `0` the mass;
`1` the shift to `L = n + 1`; `2` the doubling. -/
theorem free_massless_closed (n : ℕ) :
    - WindowFreq.defect 0 (n + 1) = Real.log ((n : ℝ) + 1) - Real.log 2 := by
  rw [WindowFreq.defect_massless]
  ring

/-- **Free massless chain: the shared read grows without bound.** DERIVED: `0` the mass. -/
theorem free_massless_diverges : Tendsto (fun L => - WindowFreq.defect 0 L) atTop atTop :=
  tendsto_neg_atBot_atTop.comp WindowFreq.tendsto_defect_massless

/-- **Free massless chain: not saturating, hence not readable.** Critical = not readable. DERIVED: `0` the mass. -/
theorem free_massless_not_readable :
    ¬ SaturatesSeq (fun L => - WindowFreq.defect 0 L) ∧ ¬ ReadableSeq (fun L => - WindowFreq.defect 0 L) := by
  have hS : ¬ SaturatesSeq (fun L => - WindowFreq.defect 0 L) := fun ⟨c, hc⟩ =>
    not_tendsto_nhds_of_tendsto_atTop free_massless_diverges c hc
  exact ⟨hS, fun h => hS h.saturates⟩

/-- **Offset: a constant `k` in the free energy, `log Z(2^w) = 16^w f + k`, reads `−15 k` at every window.**
DERIVED: `16 = 2⁴` the copies; `15 = 16 − 1`. -/
theorem offset_read (f k : ℝ) (w : ℕ) :
    (((16 : ℝ) ^ (w + 1) * f + k) - 16 * ((16 : ℝ) ^ w * f + k)) = -(15 * k) := by
  ring

/-- **Offset: it saturates, and is readable exactly when `k ≤ 0`.** Saturation alone does not give the vanishing
read. DERIVED: `0` the sign; `15 = 16 − 1`. -/
theorem offset_readable_iff (k : ℝ) :
    SaturatesSeq (fun _ : ℕ => -(15 * k)) ∧ (ReadableSeq (fun _ : ℕ => -(15 * k)) ↔ k ≤ 0) := by
  refine ⟨⟨_, tendsto_const_nhds⟩, ⟨fun ⟨c, hc0, hc⟩ => ?_, fun hk => ⟨_, by linarith, tendsto_const_nhds⟩⟩⟩
  have := tendsto_nhds_unique tendsto_const_nhds hc
  linarith

/-- **Strong coupling: readable at `β = 0`.** DERIVED: `0` the ultralocal coupling. -/
theorem readable_zero : Readable N 0 :=
  ⟨0, le_rfl, by
    have e : freeI_XY N 0 = fun _ => 0 := funext (freeI_XY_zero N)
    rw [e]
    exact tendsto_const_nhds⟩

/-- **Strong-coupling anchor: readable on some `[0, β₀)`** (`StrongAnchor.strongAnchor`).
DERIVED: `0` the lower end. -/
theorem readable_anchor (hN : N ≠ 0) : ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → Readable N β := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongAnchor.strongAnchor hN
  exact ⟨β₀, hβ₀, fun β h0 hlt => readable_of_vanishes (h β h0 hlt)⟩

end MassGap.ReadSaturates

end

#print axioms MassGap.ReadSaturates.freeI_XY_eq
#print axioms MassGap.ReadSaturates.freeI_XY_zero
#print axioms MassGap.ReadSaturates.hasDerivAt_freeI_XY
#print axioms MassGap.ReadSaturates.ReadableSeq.saturates
#print axioms MassGap.ReadSaturates.vanishes_of_tendsto_gt
#print axioms MassGap.ReadSaturates.level_le_of_not_vanishes
#print axioms MassGap.ReadSaturates.vanishes_of_readable
#print axioms MassGap.ReadSaturates.readable_of_vanishes
#print axioms MassGap.ReadSaturates.readable_iff_vanishes
#print axioms MassGap.ReadSaturates.readabilityPrinciple_iff_noStall
#print axioms MassGap.ReadSaturates.noCriticalPoint_of_readabilityPrinciple
#print axioms MassGap.ReadSaturates.clayStatement_of_readable
#print axioms MassGap.ReadSaturates.free_massive_readable
#print axioms MassGap.ReadSaturates.free_massless_closed
#print axioms MassGap.ReadSaturates.free_massless_diverges
#print axioms MassGap.ReadSaturates.free_massless_not_readable
#print axioms MassGap.ReadSaturates.offset_read
#print axioms MassGap.ReadSaturates.offset_readable_iff
#print axioms MassGap.ReadSaturates.readable_zero
#print axioms MassGap.ReadSaturates.readable_anchor
