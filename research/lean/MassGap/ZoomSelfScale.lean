import Mathlib
import MassGap.AsymptoticScaling
import MassGap.PeriodicContent
import MassGap.RectWilson

/-!
# MassGap.ZoomSelfScale — the doubling route along the theory's own scale

(W_Δ) along `aRun` (`DoublingClay2.WDelta2` at the power-of-two seed): the doubling defect on the torus of physical side `ℓ₀`,
measured in units of `aRun`, is below the seed. This module moves the scale into the theory.

* `defectW N β n = 16 log ZR(n⁴) − log ZR((2n)⁴)`.
* **(A)** `SeedExists N`: eventually in `β`, some even `n ≥ 2` has `defectW N β n ≤ 1/1000`. One
  finite-volume statement per coupling, with no scale in it.
* `nStar N β`: the least such `n` (`0` where none exists); `aSelf ℓ₀ (nStar N) β = ℓ₀ / nStar N β` is
  the self-defined spacing.
* **R** `RatioBound N ℓ₀ nS`: `nS β · aRun N β ≤ C ℓ₀` eventually.
* **(B)** `ScaleToZero nS` is the continuum-side condition of the self-scaled form, stated as a named
  proposition; `tendsto_aSelf` is (B) ⇒ `aSelf → 0`.
-/

namespace MassGap.ZoomSelfScale

open Filter Real MassGap MassGap.RectWilson

variable {N : ℕ}

/-- The doubling defect `16 log ZR(n⁴) − log ZR((2n)⁴)` at coupling `β`. DERIVED: `16 = 2⁴`, the
number of copies of the side-`n` torus in the side-`2n` torus; `2` the doubling. -/
noncomputable def defectW (N : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  16 * Real.log (ZR (fun _ => n) N β) - Real.log (ZR (fun _ => 2 * n) N β)

/-- The seed at side `n`: even, at least `2`, defect at most `1/1000`. DERIVED: `2` the least even
side; `1/1000` the sharp seed of `DoublingSharp`. -/
def Seed (N : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  Even n ∧ 2 ≤ n ∧ defectW N β n ≤ 1 / 1000

/-- **(A)**: eventually in `β`, the seed holds at some side. -/
def SeedExists (N : ℕ) : Prop := ∀ᶠ β in atTop, ∃ n : ℕ, Seed N β n

/-- The seed along a chosen side function. -/
def SeedAt (N : ℕ) (nS : ℝ → ℕ) : Prop := ∀ᶠ β in atTop, Seed N β (nS β)

open Classical in
/-- **The Δ-length** `n*(β)`: the least side meeting the seed, `0` where none does. -/
noncomputable def nStar (N : ℕ) (β : ℝ) : ℕ :=
  if h : ∃ n : ℕ, Seed N β n then Nat.find h else 0

theorem seedAt_nStar (hA : SeedExists N) : SeedAt N (nStar N) := by
  filter_upwards [hA] with β h
  classical
  have := Nat.find_spec h
  simpa [nStar, h] using this

/-- The self-defined spacing `ℓ₀ / nS β`. -/
noncomputable def aSelf (ℓ₀ : ℝ) (nS : ℝ → ℕ) (β : ℝ) : ℝ := ℓ₀ / nS β

/-- **R**: the Δ-length in units of `aRun` is bounded, `nS β · aRun N β ≤ C ℓ₀` eventually. -/
def RatioBound (N : ℕ) (ℓ₀ : ℝ) (nS : ℝ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, (nS β : ℝ) * AsymptoticScaling.aRun N β ≤ C * ℓ₀

/-- **(B)**: the Δ-length diverges, so the self-defined spacing goes to `0`. -/
def ScaleToZero (nS : ℝ → ℕ) : Prop := Tendsto (fun β => (nS β : ℝ)) atTop atTop

theorem tendsto_aSelf {ℓ₀ : ℝ} {nS : ℝ → ℕ} (hB : ScaleToZero nS) :
    Tendsto (aSelf ℓ₀ nS) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop hB

end MassGap.ZoomSelfScale

#print axioms MassGap.ZoomSelfScale.tendsto_aSelf
