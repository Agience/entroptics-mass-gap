import Mathlib
import MassGap.AttractCost

/-!
# MassGap.TensionFloor — tension per level and the localisation floor, each against a fixed extent

At `SU(2)` the run seed is `FluxCost.runSeed_two_iff_vortex`: (V) `VortexCostAt` and (T) `HiddenCostAt`.
`GlueballArea.hiddenCostAt_of_uniformGlueball` gives (T) from a gap clause and a count clause on the spectral
levels of the real zero-flux kernel `trivKN 2 β n i`. `AttractCost.levelsCost_iff_gap` shows that tension plus
localisation with the size `R` chosen per level is the gap clause. This module states the two costs against an
extent `R_j` that is read off the eigenfunction `φ_j` by a functional fixed in advance, and measures what each
of them, and the pair, is.

## 1. The two costs on a family of levels (defined; the gap proved)

`R : ι → ℝ` is an extent per level, `g₀` the ground level, `d_j = E_j − E_{g₀}`.

* `TensionCost g₀ E R c σ` (A): `c σ R_j ≤ d_j` for every excited `j`.
* `LocalFloor g₀ E R c'` (B): `R_j > 0` and `c'/R_j ≤ d_j` for every excited `j`.
* **`gap_of_tensionFloor`**: `c, c', σ ≥ 0`, (A) and (B) give `ZeroFluxGap g₀ E (√(c c' σ))`
  (`d_j² ≥ (c σ R_j)(c'/R_j) = c c' σ`; the extent cancels).
* `levelsCost_of_tensionFloor`: (A) and (B) give `AttractCost.LevelsCost g₀ E (c/2) (c'/2) σ` with the size of
  each level its extent, so the attraction form is the average of the two costs.
* `gap_of_floor_box`: (B) alone with `R_j ≤ L` gives `ZeroFluxGap g₀ E (c'/L)`.
  `gap_of_tension_min`: (A) alone with `r ≤ R_j` gives `ZeroFluxGap g₀ E (c σ r)`.
  Each alone gives a gap at the scale bounding the extent; the product `(c σ R)(c'/R)` is the only combination
  in which the extent drops out.

## 2. A free extent restates the gap (proved)

* `tensionFloor_const_of_gap`: for `c, c', σ > 0`, `ZeroFluxGap g₀ E (√(c c' σ))` gives (A) and (B) at the
  constant extent `R* = √c'/√(c σ)` (both costs equal `√(c c' σ)` there).
* **`exists_extent_iff_gap`**: `(∃ R, (A) ∧ (B)) ↔ ZeroFluxGap g₀ E (√(c c' σ))`.

Check against `ZeroFluxGap`: with the extent existentially quantified, (A) ∧ (B) is equivalent to it. The pair
carries content beyond the gap only through the choice of the extent functional.

## 3. The real objects: eigenlevels with their eigenfunctions, and the decay extent (proved)

* `EigenLevels β n i g₀ E φ μ`: the clauses of `GlueballArea.ZeroFluxLevels 2 β n i g₀ E` with the
  eigenfunctions `φ_j` of `trivKN 2 β n i` and eigenvalues `μ_j` named. `zeroFluxLevels_iff`:
  `ZeroFluxLevels 2 β n i g₀ E ↔ ∃ φ μ, EigenLevels β n i g₀ E φ μ`.
* `Extent`: a functional that reads a physical length off a pair (ground eigenfunction, level eigenfunction) at
  each `(β, n, i)`. `extentOf X β n i φ g₀ j = X β n i (φ g₀) (φ j)`.
* `rq β n i φ = ∫ φ (trivKN φ)`: the quadratic form of the real kernel (the Rayleigh quotient on a
  normalised `φ`). `rq_eigen`: on a normalised eigenfunction it is the eigenvalue.
* `decayExtent β n i φ₀ φ = t / (log rq(φ₀)² − log rq(φ)²)`, `t = n · aRun 2 β`: the physical length over
  which the level's weight `rq(φ)²/rq(φ₀)²` falls by `e`, a functional of the eigenfunctions alone.
  `decayExtent_eq`: on `EigenLevels` at `n > 0`, `β > 0` it is `1/(E_j − E_{g₀})`.
* `localFloor_decay`: on `EigenLevels` with a strict ground, (B) holds at `c' = 1` for the decay extent, at
  every `β`, with no input beyond the strict ground.
* **`tension_decay_iff_gap`**: on the same, for `c σ ≥ 0`, (A) for the decay extent is
  `ZeroFluxGap g₀ E (√(c σ))`.

Check against `ZeroFluxGap`: for the decay extent, (B) is automatic and (A) is the gap clause itself. The decay
extent is the spectral extent the tree has (the doubling machinery reads only `μ_j²`); with it the pair restates
the gap.

## 4. On the window (proved, conditional on `TensionFloorAt`)

* `TensionFloorAt X σ A c c' ℓ`: eventually in `β`, at every power-of-two side `n ≥ 2` with
  `n a ∈ [2ℓ, 5ℓ]` (`a = aRun 2 β`) and every step `i`: if the box's vortex deficits certify the rate `σ`
  (the antecedent of `AttractCost.AttractAt`), the real zero-flux kernel has `EigenLevels` on which (A) and
  (B) hold with `R_j = extentOf X β n i φ g₀ j`. `c`, `c'` and `X` are fixed before `β`.
  `TensionFloorCountAt X σ A c c' t₀ C ℓ` adds `ZeroFluxCount g₀ E t₀ C` on the same levels.
* `GlueballGapAt m ℓ`: the gap clause of `GlueballArea.UniformGlueball 2` alone.
  `glueballGapAt_of_uniformGlueball`.
* **`glueballGapAt_of_tensionFloor`**: `VortexCostAt σ A ℓ ∧ TensionFloorAt X σ A c c' ℓ` give
  `GlueballGapAt (√(c c' σ)) ℓ`. The count is not used.
* `uniformGlueball_of_tensionFloorCount`, `attractAt_of_tensionFloorCount`
  (`TensionFloorCountAt X σ A c c' t₀ C ℓ ⇒ AttractCost.AttractAt σ A (c/2) (c'/2) t₀ C ℓ`). No run-seed
  capstone is stated from `VortexCostAt σ A ℓ ∧ TensionFloorCountAt X σ A c c' t₀ C ℓ` frequently in `ℓ` at one
  `t₀` and one `C`: `InputAudit.not_tensionFloorRun` refutes that hypothesis under the argued growth of the
  zero-flux level count.
* `tensionFloorAt_const_of_glueballGap` and **`exists_extent_tensionFloorAt_iff`**: under (V),
  `(∃ X, TensionFloorAt X σ A c c' ℓ) ↔ GlueballGapAt (√(c c' σ)) ℓ` (the constant extent `R*` is an `Extent`).

## Evaluation

* Search: no declaration in the live tree, in the pruned archive (tainted modules skipped), or in the
  Entroptics Lean library bounds an excited level of `trivKN` below by a length read off its eigenfunction, in
  either direction. The nearest objects: `JentzschKT.exists_pos_eigen_kT` (the top eigenfunction of one slice
  transfer is positive; no second eigenvalue), the archive's `HeatBathLocal.torus_poincare` (a Poincaré
  inequality whose constant depends on the lattice extent), `VortexAperture`/`TomboulisYaffe` (vortex deficits to
  loops, not to levels), `Entroptics.gabor_product_scale_invariant` (the extent-times-width product is
  invariant under block rescaling: an identity, not a lower bound). (A) and (B) are not in the tree for any
  extent functional.
* What the module settles about the inputs (proved): (A) ∧ (B) imply the gap clause at `√(c c' σ)` for every
  extent; with the extent free, or with the decay extent, they are equivalent to it (§2, §3). So neither the
  free-size form (`AttractCost`) nor the spectral extent discharges anything: they restate `ZeroFluxGap`.
* The extent that would make the pair a derivation, argued, not a declaration. It must be neither the decay
  extent (which turns (A) into the gap) nor the support of `φ_j` (the set of links it reads). `trivKN` commutes
  with the slice translations, so its eigenfunctions can be chosen as translation eigenfunctions, which read
  every link; their support extent is the box, `R_j ≈ L = n a`. Then (B) is `d_j ≥ c'/L`, the finite-volume
  floor a massless theory also has (photons in a box); one rate for the whole window is `m = c'/(5ℓ)`
  (`gap_of_floor_box` at `L = 5ℓ`), and the bound `A e^{−m n a}` of `HiddenCostAt` then has exponent
  `m n a ≤ c'`, constant in `ℓ`, so it does not give the fixed rate `RunSeed` asks for at large `ℓ`; and (A) is `d_j ≥ c σ L`, which grows with the box and fails for
  a zero-momentum glueball in a large box. The extent in the author's picture is the relative size of a level at
  rest, which an exact eigenfunction does not expose. Making it a functional needs a localisation of the slice's
  configuration space by loop size (an IMS-type partition of unity `Σ_R J_R² = 1`, `d_j ≥ Σ_R ⟨J_R φ_j, (H −
  E₀) J_R φ_j⟩ − (localisation error)`), and then two inequalities on the Wilson transfer at fixed physical
  length: on each size-`R` piece the converse Tomboulis–Yaffe bound (a closed flux configuration of extent `R`
  costs at least `c σ R`, `σ` the rate (V) certifies), and a kinetic bound in which the localisation error is
  at most `c'/R` in physical units uniformly as `β → ∞` (where `aRun` enters). That is the extra structure;
  no declaration constructs any part of it.
* Finite volume (argued): at fixed `(β, n)`, `trivKN ≥ floor β n i > 0` (`CentreSectorSeedN.low_halfKN`
  averaged), so Jentzsch–Doeblin gives a positive finite-volume gap and hence (B) with the box extent at some
  `c'(β, n) > 0`. The floor is `kTmin^{n/2}` and goes to `0` as `β → ∞` at `n a` fixed, so this `c'` is not
  uniform in the zoom; not formalised here.

DERIVED (module-wide): `√(c c' σ)` is the geometric mean of the two costs (`(c σ R)(c'/R) = c c' σ`); the `1/2`
in `c/2`, `c'/2` turns two separate bounds into one bound on their sum; `R* = √c'/√(c σ)` equates the two costs;
`1` in `localFloor_decay` is the decay extent's own normalisation (`(E_j − E_{g₀}) · R_j = 1`); `[2ℓ, 5ℓ]`,
powers of two and `n ≥ 2` are the window of `FluxCost.VortexCostAt`; `c' = (c'/(5ℓ)) · 5ℓ`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TensionFloor

open Filter MassGap MeasureTheory
open MassGap.KernelPower
open MassGap.GapSideVortexRect (zR Lc)
open MassGap.GlueballArea (ZeroFluxLevels ZeroFluxGap ZeroFluxCount UniformGlueball)
open MassGap.FluxCost (VortexCostAt)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.CentreSectorSeedN (trivKN hSN)

/-! ## 1. The two costs on a family of levels -/

section Levels

variable {ι : Type*}

/-- **(A) Tension per level**: every excited level lies at least `c σ R_j` above the ground. -/
def TensionCost (g₀ : ι) (E R : ι → ℝ) (c σ : ℝ) : Prop :=
  ∀ j, j ≠ g₀ → c * σ * R j ≤ E j - E g₀

/-- **(B) Localisation floor**: every excited level has a positive extent `R_j` and lies at least `c'/R_j`
above the ground. -/
def LocalFloor (g₀ : ι) (E R : ι → ℝ) (c' : ℝ) : Prop :=
  ∀ j, j ≠ g₀ → 0 < R j ∧ c' / R j ≤ E j - E g₀

/-- **(A) and (B) give the gap** at the geometric mean `√(c c' σ)`; the extent cancels. -/
theorem gap_of_tensionFloor {g₀ : ι} {E R : ι → ℝ} {c c' σ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hσ : 0 ≤ σ) (hA : TensionCost g₀ E R c σ) (hB : LocalFloor g₀ E R c') :
    ZeroFluxGap g₀ E (Real.sqrt (c * c' * σ)) := by
  intro j hj
  obtain ⟨hR, hb⟩ := hB j hj
  have ha := hA j hj
  have hq : 0 ≤ c' / R j := div_nonneg hc' hR.le
  have hd0 : 0 ≤ E j - E g₀ := hq.trans hb
  have hcs : 0 ≤ c * σ * R j := mul_nonneg (mul_nonneg hc hσ) hR.le
  have h1 : c * σ * R j * (c' / R j) ≤ (E j - E g₀) * (E j - E g₀) := mul_le_mul ha hb hq hd0
  have h2 : c * σ * R j * (c' / R j) = c * c' * σ := by
    have hRne : R j ≠ 0 := hR.ne'
    field_simp
  have hprod : c * c' * σ ≤ (E j - E g₀) ^ 2 := by rw [sq]; linarith
  have hs := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_sq hd0] at hs
  linarith

/-- **The attraction form is the average of the two costs**: (A) and (B) give
`AttractCost.LevelsCost g₀ E (c/2) (c'/2) σ`, each level's size being its extent. -/
theorem levelsCost_of_tensionFloor {g₀ : ι} {E R : ι → ℝ} {c c' σ : ℝ}
    (hA : TensionCost g₀ E R c σ) (hB : LocalFloor g₀ E R c') :
    AttractCost.LevelsCost g₀ E (c / 2) (c' / 2) σ := by
  intro j hj
  obtain ⟨hR, hb⟩ := hB j hj
  have ha := hA j hj
  refine ⟨R j, hR, ?_⟩
  have e1 : c / 2 * σ * R j = c * σ * R j / 2 := by ring
  have e2 : c' / 2 / R j = c' / R j / 2 := by ring
  rw [e1, e2]
  linarith

/-- **(B) alone with a bounded extent**: `R_j ≤ L` gives the gap `c'/L`. -/
theorem gap_of_floor_box {g₀ : ι} {E R : ι → ℝ} {c' L : ℝ} (hc' : 0 ≤ c')
    (hB : LocalFloor g₀ E R c') (hL : ∀ j, j ≠ g₀ → R j ≤ L) : ZeroFluxGap g₀ E (c' / L) := by
  intro j hj
  obtain ⟨hR, hb⟩ := hB j hj
  have : c' / L ≤ c' / R j := div_le_div_of_nonneg_left hc' hR (hL j hj)
  linarith

/-- **(A) alone with an extent bounded below**: `r ≤ R_j` gives the gap `c σ r`. -/
theorem gap_of_tension_min {g₀ : ι} {E R : ι → ℝ} {c σ r : ℝ} (hcσ : 0 ≤ c * σ)
    (hA : TensionCost g₀ E R c σ) (hr : ∀ j, j ≠ g₀ → r ≤ R j) : ZeroFluxGap g₀ E (c * σ * r) := by
  intro j hj
  have : c * σ * r ≤ c * σ * R j := mul_le_mul_of_nonneg_left (hr j hj) hcσ
  linarith [hA j hj]

/-! ## 2. A free extent restates the gap -/

/-- The two costs at the constant extent `R* = √c'/√(c σ)` both equal `√(c c' σ)`. -/
theorem costs_at_const {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ) :
    0 < Real.sqrt c' / Real.sqrt (c * σ) ∧
      c * σ * (Real.sqrt c' / Real.sqrt (c * σ)) = Real.sqrt (c * c' * σ) ∧
      c' / (Real.sqrt c' / Real.sqrt (c * σ)) = Real.sqrt (c * c' * σ) := by
  have ha : 0 < Real.sqrt (c * σ) := Real.sqrt_pos.mpr (mul_pos hc hσ)
  have hb : 0 < Real.sqrt c' := Real.sqrt_pos.mpr hc'
  have ha2 : Real.sqrt (c * σ) ^ 2 = c * σ := Real.sq_sqrt (mul_pos hc hσ).le
  have hb2 : Real.sqrt c' ^ 2 = c' := Real.sq_sqrt hc'.le
  have hai : Real.sqrt (c * σ) * (Real.sqrt (c * σ))⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hbi : Real.sqrt c' * (Real.sqrt c')⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  rw [AttractCost.sqrt_split hc.le hσ.le]
  refine ⟨div_pos hb ha, ?_, ?_⟩
  · linear_combination (-(Real.sqrt c' * (Real.sqrt (c * σ))⁻¹)) * ha2
      + (Real.sqrt (c * σ) * Real.sqrt c') * hai
  · rw [div_div_eq_mul_div]
    linear_combination (-(Real.sqrt (c * σ) * (Real.sqrt c')⁻¹)) * hb2
      + (Real.sqrt (c * σ) * Real.sqrt c') * hbi

/-- **The gap gives (A) and (B) at a constant extent.** -/
theorem tensionFloor_const_of_gap {g₀ : ι} {E : ι → ℝ} {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hσ : 0 < σ) (h : ZeroFluxGap g₀ E (Real.sqrt (c * c' * σ))) :
    TensionCost g₀ E (fun _ => Real.sqrt c' / Real.sqrt (c * σ)) c σ ∧
      LocalFloor g₀ E (fun _ => Real.sqrt c' / Real.sqrt (c * σ)) c' := by
  obtain ⟨hR, e1, e2⟩ := costs_at_const hc hc' hσ
  refine ⟨fun j hj => ?_, fun j hj => ⟨hR, ?_⟩⟩
  · rw [e1]; linarith [h j hj]
  · rw [e2]; linarith [h j hj]

/-- **With the extent free, (A) ∧ (B) is the gap clause** at `√(c c' σ)`. -/
theorem exists_extent_iff_gap {g₀ : ι} {E : ι → ℝ} {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hσ : 0 < σ) :
    (∃ R : ι → ℝ, TensionCost g₀ E R c σ ∧ LocalFloor g₀ E R c') ↔
      ZeroFluxGap g₀ E (Real.sqrt (c * c' * σ)) :=
  ⟨fun ⟨_, hA, hB⟩ => gap_of_tensionFloor hc.le hc'.le hσ.le hA hB,
    fun h => ⟨_, tensionFloor_const_of_gap hc hc' hσ h⟩⟩

/-! ### The decay extent on a family of levels -/

/-- **The decay extent of a level**: `1/(E_j − E_{g₀})`. -/
def decayExt (g₀ : ι) (E : ι → ℝ) (j : ι) : ℝ := 1 / (E j - E g₀)

/-- **(B) is automatic for the decay extent** at `c' = 1`, given a strict ground. -/
theorem localFloor_decayExt {g₀ : ι} {E : ι → ℝ} (hstrict : ∀ j, j ≠ g₀ → E g₀ < E j) :
    LocalFloor g₀ E (decayExt g₀ E) 1 := by
  intro j hj
  have hd : 0 < E j - E g₀ := sub_pos.2 (hstrict j hj)
  refine ⟨one_div_pos.2 hd, ?_⟩
  unfold decayExt
  rw [one_div_one_div]

/-- **(A) for the decay extent is the gap clause** at `√(c σ)`, given a strict ground. -/
theorem tensionCost_decayExt_iff {g₀ : ι} {E : ι → ℝ} {c σ : ℝ} (hcσ : 0 ≤ c * σ)
    (hstrict : ∀ j, j ≠ g₀ → E g₀ < E j) :
    TensionCost g₀ E (decayExt g₀ E) c σ ↔ ZeroFluxGap g₀ E (Real.sqrt (c * σ)) := by
  have key : ∀ j, j ≠ g₀ →
      (c * σ * decayExt g₀ E j ≤ E j - E g₀ ↔ E g₀ + Real.sqrt (c * σ) ≤ E j) := by
    intro j hj
    have hd : 0 < E j - E g₀ := sub_pos.2 (hstrict j hj)
    have e : c * σ * decayExt g₀ E j = c * σ / (E j - E g₀) := by unfold decayExt; ring
    rw [e, div_le_iff₀ hd]
    constructor
    · intro h
      have h2 : c * σ ≤ (E j - E g₀) ^ 2 := by rw [sq]; exact h
      have := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq hd.le] at this
      linarith
    · intro h
      have h1 : Real.sqrt (c * σ) ≤ E j - E g₀ := by linarith
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt hcσ] at h2
      rw [sq] at h2
      exact h2
  exact ⟨fun h j hj => (key j hj).1 (h j hj), fun h j hj => (key j hj).2 (h j hj)⟩

end Levels

/-! ## 3. The real objects -/

section Real

/-- The slice of step `i` at side `n`. -/
abbrev Slice (n : ℕ) (i : Fin 4) : Type :=
  RectWilson.SpT i (CentreSectorSeed.Tr n i) → SUN.SU 2

/-- **The zero-flux levels with their eigenfunctions named**: the clauses of
`GlueballArea.ZeroFluxLevels 2 β n i g₀ E`, with `φ` and `μ` explicit. -/
structure EigenLevels (β : ℝ) (n : ℕ) (i : Fin 4) {ι : Type*} (g₀ : ι) (E : ι → ℝ)
    (φ : ι → Slice n i → ℝ) (μ : ι → ℝ) : Prop where
  ground : ∀ j, E g₀ ≤ E j
  norm : ∀ j, ∫ x, φ j x * φ j x ∂(hSN 2 n i) = 1
  orth : ∀ j k, j ≠ k → ∫ x, φ j x * φ k x ∂(hSN 2 n i) = 0
  eigen : ∀ j x, ∫ y, trivKN 2 β n i x y * φ j y ∂(hSN 2 n i) = μ j * φ j x
  energy : ∀ j, μ j ^ 2 = Real.exp (-(E j * ((n : ℝ) * aRun 2 β)))
  hs_eq : hs (hSN 2 n i) (trivKN 2 β n i) = ∑' j, Real.exp (-(E j * ((n : ℝ) * aRun 2 β)))
  hs_conv_eq : hs (hSN 2 n i) (conv (hSN 2 n i) (trivKN 2 β n i) (trivKN 2 β n i))
      = ∑' j, Real.exp (-(E j * (2 * ((n : ℝ) * aRun 2 β))))

theorem zeroFluxLevels_iff {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ} :
    ZeroFluxLevels 2 β n i g₀ E ↔ ∃ (φ : ι → Slice n i → ℝ) (μ : ι → ℝ), EigenLevels β n i g₀ E φ μ := by
  constructor
  · rintro ⟨hg, ⟨φ, μ, h1, h2, h3, h4⟩, h5, h6⟩
    exact ⟨φ, μ, ⟨hg, h1, h2, h3, h4, h5, h6⟩⟩
  · rintro ⟨φ, μ, h⟩
    exact ⟨h.ground, ⟨φ, μ, h.norm, h.orth, h.eigen, h.energy⟩, h.hs_eq, h.hs_conv_eq⟩

/-- **An extent functional**: a physical length read off (ground eigenfunction, level eigenfunction) at each
`(β, n, i)`. -/
abbrev Extent : Type :=
  ℝ → ∀ (n : ℕ) (i : Fin 4), (Slice n i → ℝ) → (Slice n i → ℝ) → ℝ

/-- The extent of level `j`. -/
def extentOf (X : Extent) (β : ℝ) (n : ℕ) (i : Fin 4) {ι : Type*} (φ : ι → Slice n i → ℝ) (g₀ j : ι) :
    ℝ :=
  X β n i (φ g₀) (φ j)

/-- **The quadratic form of the real zero-flux kernel** (the Rayleigh quotient on a normalised `φ`):
`∫ φ (trivKN φ)`. -/
def rq (β : ℝ) (n : ℕ) (i : Fin 4) (φ : Slice n i → ℝ) : ℝ :=
  ∫ x, φ x * ∫ y, trivKN 2 β n i x y * φ y ∂(hSN 2 n i) ∂(hSN 2 n i)

/-- On a normalised eigenfunction the Rayleigh quotient is the eigenvalue. -/
theorem rq_eigen {β : ℝ} {n : ℕ} {i : Fin 4} {φ : Slice n i → ℝ} {μ : ℝ}
    (hnorm : ∫ x, φ x * φ x ∂(hSN 2 n i) = 1)
    (heig : ∀ x, ∫ y, trivKN 2 β n i x y * φ y ∂(hSN 2 n i) = μ * φ x) : rq β n i φ = μ := by
  unfold rq
  have hf : (fun x => φ x * ∫ y, trivKN 2 β n i x y * φ y ∂(hSN 2 n i))
      = fun x => μ * (φ x * φ x) := by
    funext x; rw [heig x]; ring
  rw [hf, integral_const_mul, hnorm, mul_one]

/-- **The decay extent**: `t / (log rq(φ₀)² − log rq(φ)²)` with `t = n · aRun 2 β`, the physical length over
which the level's relative weight `rq(φ)²/rq(φ₀)²` falls by `e`. -/
def decayExtent : Extent := fun β n i φ₀ φ =>
  ((n : ℝ) * aRun 2 β) / (Real.log (rq β n i φ₀ ^ 2) - Real.log (rq β n i φ ^ 2))

/-- **The decay extent of a real eigenlevel** is `1/(E_j − E_{g₀})` (`n > 0`, `β > 0`). -/
theorem decayExtent_eq {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μ : ι → ℝ} (h : EigenLevels β n i g₀ E φ μ) (hn : 0 < n) (hβ : 0 < β)
    (j : ι) : extentOf decayExtent β n i φ g₀ j = decayExt g₀ E j := by
  have ht : 0 < (n : ℝ) * aRun 2 β :=
    mul_pos (Nat.cast_pos.2 hn) (aRun_pos (N := 2) (by norm_num) hβ)
  have hr : ∀ k, Real.log (rq β n i (φ k) ^ 2) = -(E k * ((n : ℝ) * aRun 2 β)) := by
    intro k
    rw [rq_eigen (h.norm k) (h.eigen k), h.energy k, Real.log_exp]
  unfold extentOf decayExtent decayExt
  rw [hr g₀, hr j]
  set t := (n : ℝ) * aRun 2 β
  have e : -(E g₀ * t) - -(E j * t) = t * (E j - E g₀) := by ring
  rw [e, ← div_div, div_self ht.ne']

/-- **(B) is automatic for the decay extent** on a real eigenlevel family with a strict ground, at `c' = 1`. -/
theorem localFloor_decay {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μ : ι → ℝ} (h : EigenLevels β n i g₀ E φ μ) (hn : 0 < n) (hβ : 0 < β)
    (hstrict : ∀ j, j ≠ g₀ → E g₀ < E j) :
    LocalFloor g₀ E (extentOf decayExtent β n i φ g₀) 1 := by
  have he : extentOf decayExtent β n i φ g₀ = decayExt g₀ E := funext (decayExtent_eq h hn hβ)
  rw [he]
  exact localFloor_decayExt hstrict

/-- **(A) for the decay extent is the gap clause** on a real eigenlevel family with a strict ground. -/
theorem tension_decay_iff_gap {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → Slice n i → ℝ} {μ : ι → ℝ} (h : EigenLevels β n i g₀ E φ μ) (hn : 0 < n) (hβ : 0 < β)
    (hstrict : ∀ j, j ≠ g₀ → E g₀ < E j) {c σ : ℝ} (hcσ : 0 ≤ c * σ) :
    TensionCost g₀ E (extentOf decayExtent β n i φ g₀) c σ ↔
      ZeroFluxGap g₀ E (Real.sqrt (c * σ)) := by
  have he : extentOf decayExtent β n i φ g₀ = decayExt g₀ E := funext (decayExtent_eq h hn hβ)
  rw [he]
  exact tensionCost_decayExt_iff hcσ hstrict

end Real

/-! ## 4. On the window -/

section Window

/-- **(A) and (B) at the window, against the extent `X`**: if the box's vortex deficits certify the rate `σ`,
the real zero-flux kernel has eigenlevels paying tension and the localisation floor at the extents
`X β n i (φ g₀) (φ j)`. DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `FluxCost.VortexCostAt` (`5` leaves
room for the power of two at or above `⌈2ℓ/a⌉`, which is below `4ℓ + 2a`); `2` also the rank and the least side. -/
def TensionFloorAt (X : Extent) (σ A c c' ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4,
      (∀ ν : {j : Fin 4 // j ≠ i},
        1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β)))) →
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ) (φ : ι → Slice n i → ℝ) (μ : ι → ℝ),
        EigenLevels β n i g₀ E φ μ ∧ TensionCost g₀ E (extentOf X β n i φ g₀) c σ ∧
          LocalFloor g₀ E (extentOf X β n i φ g₀) c'

/-- `TensionFloorAt` with the count clause on the same levels. DERIVED: `2`, `5` as in `TensionFloorAt`, the
window `[2ℓ, 5ℓ]` of `FluxCost.VortexCostAt`. -/
def TensionFloorCountAt (X : Extent) (σ A c c' t₀ C ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4,
      (∀ ν : {j : Fin 4 // j ≠ i},
        1 - zR (Lc n i) i ν.1 β ≤ A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β)))) →
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ) (φ : ι → Slice n i → ℝ) (μ : ι → ℝ),
        EigenLevels β n i g₀ E φ μ ∧ TensionCost g₀ E (extentOf X β n i φ g₀) c σ ∧
          LocalFloor g₀ E (extentOf X β n i φ g₀) c' ∧ ZeroFluxCount g₀ E t₀ C

/-- **The gap clause of `UniformGlueball 2` alone.** DERIVED: `2` the rank and the least side; `5` with `2` the
window `[2ℓ, 5ℓ]` of `UniformGlueball`. -/
def GlueballGapAt (m ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ → ∀ i : Fin 4,
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ), ZeroFluxLevels 2 β n i g₀ E ∧ ZeroFluxGap g₀ E m

theorem glueballGapAt_of_uniformGlueball {m t₀ C ℓ : ℝ} (h : UniformGlueball 2 m t₀ C ℓ) :
    GlueballGapAt m ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, hL, hg, -⟩ := hβ n hn h2 hlo hhi i
  exact ⟨ι, g₀, E, hL, hg⟩

/-- **(V) with (A) and (B) give the gap clause** at `√(c c' σ)`, uniformly in the zoom. -/
theorem glueballGapAt_of_tensionFloor {X : Extent} {σ A c c' ℓ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hσ : 0 ≤ σ) (hV : VortexCostAt σ A ℓ) (hT : TensionFloorAt X σ A c c' ℓ) :
    GlueballGapAt (Real.sqrt (c * c' * σ)) ℓ := by
  filter_upwards [hV, hT] with β hVβ hTβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, φ, μ, hL, hA, hB⟩ :=
    hTβ n hn h2 hlo hhi i (fun ν => hVβ n hn h2 hlo hhi i ν)
  exact ⟨ι, g₀, E, zeroFluxLevels_iff.2 ⟨φ, μ, hL⟩, gap_of_tensionFloor hc hc' hσ hA hB⟩

/-- **(V) with (A), (B) and the count give the uniform glueball statement** at `√(c c' σ)`. -/
theorem uniformGlueball_of_tensionFloorCount {X : Extent} {σ A c c' t₀ C ℓ : ℝ} (hc : 0 ≤ c)
    (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hV : VortexCostAt σ A ℓ)
    (hT : TensionFloorCountAt X σ A c c' t₀ C ℓ) :
    UniformGlueball 2 (Real.sqrt (c * c' * σ)) t₀ C ℓ := by
  filter_upwards [hV, hT] with β hVβ hTβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, φ, μ, hL, hA, hB, hC⟩ :=
    hTβ n hn h2 hlo hhi i (fun ν => hVβ n hn h2 hlo hhi i ν)
  exact ⟨ι, g₀, E, zeroFluxLevels_iff.2 ⟨φ, μ, hL⟩, gap_of_tensionFloor hc hc' hσ hA hB, hC⟩

/-- **(A), (B) and the count give `AttractCost.AttractAt`** at `(c/2, c'/2)`. -/
theorem attractAt_of_tensionFloorCount {X : Extent} {σ A c c' t₀ C ℓ : ℝ}
    (hT : TensionFloorCountAt X σ A c c' t₀ C ℓ) :
    AttractCost.AttractAt σ A (c / 2) (c' / 2) t₀ C ℓ := by
  filter_upwards [hT] with β hTβ n hn h2 hlo hhi i hV
  obtain ⟨ι, g₀, E, φ, μ, hL, hA, hB, hC⟩ := hTβ n hn h2 hlo hhi i hV
  exact ⟨ι, g₀, E, zeroFluxLevels_iff.2 ⟨φ, μ, hL⟩, levelsCost_of_tensionFloor hA hB, hC⟩

/-- The constant extent `R* = √c'/√(c σ)`. -/
def constExtent (c c' σ : ℝ) : Extent := fun _ _ _ _ _ => Real.sqrt c' / Real.sqrt (c * σ)

/-- **The gap clause gives (A) and (B) at the constant extent.** -/
theorem tensionFloorAt_const_of_glueballGap {σ A c c' ℓ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ)
    (h : GlueballGapAt (Real.sqrt (c * c' * σ)) ℓ) :
    TensionFloorAt (constExtent c c' σ) σ A c c' ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i _
  obtain ⟨ι, g₀, E, hL, hg⟩ := hβ n hn h2 hlo hhi i
  obtain ⟨φ, μ, hE⟩ := zeroFluxLevels_iff.1 hL
  exact ⟨ι, g₀, E, φ, μ, hE, tensionFloor_const_of_gap hc hc' hσ hg⟩

/-- **Under (V), (A) ∧ (B) at some extent functional is the gap clause** at `√(c c' σ)`. -/
theorem exists_extent_tensionFloorAt_iff {σ A c c' ℓ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ)
    (hV : VortexCostAt σ A ℓ) :
    (∃ X : Extent, TensionFloorAt X σ A c c' ℓ) ↔ GlueballGapAt (Real.sqrt (c * c' * σ)) ℓ :=
  ⟨fun ⟨_, hT⟩ => glueballGapAt_of_tensionFloor hc.le hc'.le hσ.le hV hT,
    fun h => ⟨_, tensionFloorAt_const_of_glueballGap hc hc' hσ h⟩⟩

end Window

end MassGap.TensionFloor

end

#print axioms MassGap.TensionFloor.gap_of_tensionFloor
#print axioms MassGap.TensionFloor.levelsCost_of_tensionFloor
#print axioms MassGap.TensionFloor.gap_of_floor_box
#print axioms MassGap.TensionFloor.gap_of_tension_min
#print axioms MassGap.TensionFloor.costs_at_const
#print axioms MassGap.TensionFloor.tensionFloor_const_of_gap
#print axioms MassGap.TensionFloor.exists_extent_iff_gap
#print axioms MassGap.TensionFloor.localFloor_decayExt
#print axioms MassGap.TensionFloor.tensionCost_decayExt_iff
#print axioms MassGap.TensionFloor.zeroFluxLevels_iff
#print axioms MassGap.TensionFloor.rq_eigen
#print axioms MassGap.TensionFloor.decayExtent_eq
#print axioms MassGap.TensionFloor.localFloor_decay
#print axioms MassGap.TensionFloor.tension_decay_iff_gap
#print axioms MassGap.TensionFloor.glueballGapAt_of_uniformGlueball
#print axioms MassGap.TensionFloor.glueballGapAt_of_tensionFloor
#print axioms MassGap.TensionFloor.uniformGlueball_of_tensionFloorCount
#print axioms MassGap.TensionFloor.attractAt_of_tensionFloorCount
#print axioms MassGap.TensionFloor.tensionFloorAt_const_of_glueballGap
#print axioms MassGap.TensionFloor.exists_extent_tensionFloorAt_iff
