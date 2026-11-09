import Mathlib
import MassGap.ClayRoutes

noncomputable section

/-!
# MassGap.ClayReduce — the Clay capstone on the inputs it consumes

`ClayRoutes.ClayContinuumPair` is reached through `ContinuumSep.continuum_gap_sep` and
`ContinuumSep.exists_orth_ne_zero_sep`. The chain reads N (`ContinuumNontrivial.KernelConvergesSep`)
and Y (`ShortDistanceY.AFShortDistance`) only through `ContinuumNontrivial.connectedTwoPointNonzero_of_af`,
which reads them only as a positive lower bound on the lattice two-point function of one reflected cube
pair, and it reads E only as `ContinuumSep.PairBoundSep`: bounds on the reflected pairs `pairFam τ P Q`
of separated positive-time monomials at common dyadic time shifts. This module states each of those
inputs at that strength.

## Non-triviality: `PairLowerBound`

`PairLowerBound hN Z τ`: for some field `O`, margin `t > 0`, side `ℓ` and `c > 0`, eventually in the
step, `c ≤ latSkR(θQ ∪ Q)` for the cube monomial `Q = mono1 (O, cubeTest t ℓ)` at the connected
renormalisation `Renorm.connected hN Z`.

* `pairLowerBound_of_af`: N and Y give it (`ContinuumNontrivial.eventually_bounds`,
  `ContinuumNontrivial.af_bounds_on_interval`).
* `connectedTwoPointNonzero_of_pairLowerBound`: with `PairBoundSep` it gives
  `ContinuumSep.ConnectedTwoPointNonzero` (`ContinuumSep.tendsto_pair_sep_of_pairBound`,
  `ge_of_tendsto`, `ContinuumNontrivial.kern_empty_mono1`).

## The capstones

E enters in three strengths, `ContinuumSep.UniformBoundSep → ContinuumSep.DiagBoundSep →
ContinuumSep.PairBoundSep` (`ContinuumSep.diagBoundSep_of_uniformBoundSep`,
`ContinuumSep.pairBoundSep_of_diagBoundSep`, the second under the reflection compatibility
`Renorm.connected_reflCompat hN Z τ hZ`).

* `clay_continuum_pair_of_pairLowerBound`: `ClayContinuumPair` from `PairBoundSep`, M and
  `PairLowerBound`.
* `clay_continuum_of_diagBoundSep`: the same with E as `DiagBoundSep`, the bound on the unshifted
  reflection diagonal `θP ∪ P` alone.
* `clay_continuum_of_pairLowerBound`: `ClayContinuum` with E as `UniformBoundSep`.

## The field-independent renormalisation

`ContinuumNontrivial.rhoA hN` is `Renorm.connected hN (zA N)`, `zA N k O = a_k⁻⁴`, the same factor for
every field (`rhoA_eq`). `pairLowerBound_rhoA` gives `PairLowerBound` from N and Y at `rhoA`.

## Scope

`PairLowerBound`, `DiagBoundSep` (or `PairBoundSep`, or `UniformBoundSep`), M and the UV step are
hypotheses. `ClayContinuumPair` takes its `PairBoundSep` witness only in proof fields
(`ClayRoutes.clayContinuum_iff_pair`), so the `DiagBoundSep` capstones conclude the same proposition as
the `UniformBoundSep` ones.
-/

namespace MassGap.ClayReduce

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The lower bound on one reflected cube pair -/

section Lower

/-- **The lower bound on one reflected cube pair along the coupling tower `βs` (stated, not proved).**
For some local gauge-invariant field `O`, margin `t > 0`, side `ℓ` and `c > 0`, eventually in the
step, `c ≤ latSkRAlong(θQ ∪ Q)` for `Q = mono1 (O, cubeTest t ℓ)` at the connected renormalisation
`Renorm.connectedAlong hN βs Z`. A negative `ℓ` gives the empty cube and `latSkR = 0`, which `c > 0` excludes.

DERIVED: `0` is the excluded colour count and the lower end of `t` and `c`; `4` in `Fin 4` is the
spacetime dimension. -/
def PairLowerBoundAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) : Prop :=
  ∃ (O : LField (MassGap.SUN.SU N)) (t ℓ c : ℝ), 0 < t ∧ 0 < c ∧
    ∀ᶠ k in atTop, c ≤ latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k
      (pairFam τ (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
        (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)))

/-- **The lower bound on one reflected cube pair (stated, not proved)**: `PairLowerBoundAlong` at the
couplings `dyBeta`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def PairLowerBound (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) : Prop :=
  PairLowerBoundAlong hN (dyBeta (one_le_of_ne_zero hN)) Z τ

/-- **N and Y give the lower bound.** At `N ≠ 0`, a reflection-invariant `Z`, a field `O` whose
renormalised kernel converges on separated pairs to `G(|p − q|)` (`KernelConvergesSep`) with
`ShortDistanceY.AFShortDistance G`: `PairLowerBound hN Z τ`, at the cube `t = ℓ = δ/16` of
`ContinuumNontrivial.connectedTwoPointNonzero_of_af` and `c = (g₀/2)(ℓ/2)⁸`
(`ContinuumNontrivial.eventually_bounds`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The proof's `2`
and `4` in `[2t, 4(|t| + |ℓ|)]` are `ContinuumNontrivial.eDist_ge`'s and `eDist_le`'s; the `4`s in
`(g₀/2)(ℓ/2)⁴(ℓ/2)⁴` are the cube volume exponents of `eventually_bounds`. CHOSEN: the halvings `g₀/2` and
`ℓ/2`, as in `eventually_bounds`; `16`, as in
`connectedTwoPointNonzero_of_af`: at `t = ℓ = δ/16` the separations lie in `[δ/8, δ/2] ⊂ (0, δ)`; any
divisor above `8` serves. -/
theorem pairLowerBound_of_af (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    PairLowerBound hN Z τ := by
  obtain ⟨δ, hδ, -, hbd⟩ := ContinuumNontrivial.af_bounds_on_interval hY
  have hs : 0 < δ / 16 := by linarith
  have habs : |δ / 16| = δ / 16 := abs_of_pos hs
  obtain ⟨g₀, g₁, hg₀, hG⟩ := hbd (2 * (δ / 16)) (4 * (|δ / 16| + |δ / 16|)) (by linarith)
    (by rw [habs]; linarith) (by rw [habs]; linarith)
  have hev := ContinuumNontrivial.eventually_bounds hN Z τ hZ O _ hconv hs hs hg₀
    (fun _ _ h => hG _ (ContinuumNontrivial.eDist_ge h) (ContinuumNontrivial.eDist_le h))
  exact ⟨O, δ / 16, δ / 16, g₀ / 2 * ((δ / 16 / 2) ^ 4 * (δ / 16 / 2) ^ 4), hs,
    mul_pos (half_pos hg₀) (mul_pos (pow_pos (half_pos hs) 4) (pow_pos (half_pos hs) 4)),
    hev.mono (fun _ hk => hk.1)⟩

#print axioms pairLowerBound_of_af

/-- **The lower bound and E give a non-zero connected two-point function.** Under
`ContinuumSep.PairBoundSep`, the cube pair converges along `ultra`
(`ContinuumSep.tendsto_pair_sep_of_pairBound`), so `c ≤ S(θQ ∪ Q)` (`ge_of_tendsto`); `S(Q) = 0`
(`ContinuumNontrivial.kern_empty_mono1`), so `S(θQ ∪ Q) − S(Q)² ≥ c > 0`.

DERIVED: `0` is the excluded colour count; `2` is the square; `4` in `Fin 4` is the spacetime
dimension. -/
theorem connectedTwoPointNonzero_of_pairLowerBound_along (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) τ) (hP : PairLowerBoundAlong hN βs Z τ) :
    ContinuumSep.ConnectedTwoPointNonzeroAlong hN βs (Renorm.connectedAlong hN βs Z) τ := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨O, t, ℓ, c, ht, hc, hev⟩ := hP
  have hQ : ∃ d : ℝ, 0 < d ∧ ContinuumSep.sepPos τ d
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) :=
    ⟨t, ht, ContinuumNontrivial.sepPos_mono1 τ O t ℓ⟩
  have htend := ContinuumSep.tendsto_pair_sep_of_pairBound_along hN βs (Renorm.connectedAlong hN βs Z) τ hB hQ hQ
  have hge : c ≤ kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) :=
    ge_of_tendsto htend (hev.filter_mono ultra_le)
  refine ⟨ContinuumNontrivial.sepCube τ O ht ℓ, ?_⟩
  show kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
    - kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ (emptyMono N)
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) ^ 2 ≠ 0
  rw [ContinuumNontrivial.kern_empty_mono1_along hN βs Z τ hZ O (ContinuumNontrivial.cubeTest t ℓ),
    zero_pow two_ne_zero, sub_zero]
  exact (lt_of_lt_of_le hc hge).ne'

#print axioms connectedTwoPointNonzero_of_pairLowerBound_along

/-- **The lower bound and E give a non-zero connected two-point function**, at the couplings `dyBeta`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem connectedTwoPointNonzero_of_pairLowerBound (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (hP : PairLowerBound hN Z τ) :
    ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ :=
  connectedTwoPointNonzero_of_pairLowerBound_along hN (dyBeta (one_le_of_ne_zero hN)) Z τ hZ hB hP

#print axioms connectedTwoPointNonzero_of_pairLowerBound

end Lower

/-! ## 2. The capstones on the lower bound -/

section Capstone

/-- **The Clay continuum statement along a coupling tower, from the pair bound, the tower gap and the
pair lower bound.** Under `ContinuumSep.PairBoundSepAlong` at `Renorm.connectedAlong hN βs Z` (E),
`ContinuumCluster.TowerGapAt hN τ βs M` at `M > 0` (the gap along the tower) and
`PairLowerBoundAlong hN βs Z τ`: `ClayRoutes.ClayContinuumPairAlong hN βs Z τ hZ hB L` at every window
`L > 0`, with `c = M L` (`ContinuumSep.continuum_gap_sep_of_towerGapAt`,
`connectedTwoPointNonzero_of_pairLowerBound_along`, `ContinuumSep.exists_orth_ne_zero_sep_along`).

DERIVED: `0` is the excluded colour count, the lower end of `M` and `L`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem clay_continuum_pair_of_towerGapAt (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) τ) {M : ℝ}
    (hM : 0 < M) (hG : ContinuumCluster.TowerGapAt hN τ βs M) {L : ℝ} (hL : 0 < L)
    (hP : PairLowerBoundAlong hN βs Z τ) :
    ClayRoutes.ClayContinuumPairAlong hN βs Z τ hZ hB L := by
  have hne := connectedTwoPointNonzero_of_pairLowerBound_along hN βs Z τ hZ hB hP
  have e : M * L / L = M := mul_div_cancel_right₀ M hL.ne'
  refine ⟨M * L, mul_pos hM hL, fun m => ?_⟩
  rw [e]
  exact ⟨ContinuumSep.continuum_gap_sep_of_towerGapAt hN βs (Renorm.connectedAlong hN βs Z) τ hB
      (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) hM hG m,
    ContinuumSep.exists_orth_ne_zero_sep_along hN βs (Renorm.connectedAlong hN βs Z) τ hB
      (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m hne⟩

#print axioms clay_continuum_pair_of_towerGapAt

/-- **The Clay continuum statement along a coupling tower from the reflection-diagonal bound**: as
`clay_continuum_pair_of_towerGapAt`, with E as `ContinuumSep.DiagBoundSepAlong` at
`Renorm.connectedAlong hN βs Z` (`ContinuumSep.pairBoundSep_of_diagBoundSep_along`).

DERIVED: `0` is the excluded colour count, the lower end of `M` and `L`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem clay_continuum_of_diagBoundSep_towerGapAt (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hD : ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) τ) {M : ℝ}
    (hM : 0 < M) (hG : ContinuumCluster.TowerGapAt hN τ βs M) {L : ℝ} (hL : 0 < L)
    (hP : PairLowerBoundAlong hN βs Z τ) :
    ClayRoutes.ClayContinuumPairAlong hN βs Z τ hZ
      (ContinuumSep.pairBoundSep_of_diagBoundSep_along hN βs (Renorm.connectedAlong hN βs Z) τ
        (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) hD) L :=
  clay_continuum_pair_of_towerGapAt hN βs Z τ hZ _ hM hG hL hP

#print axioms clay_continuum_of_diagBoundSep_towerGapAt

/-- **The Clay continuum statement from the pair bound, M and the pair lower bound.** At `2 ≤ N`, a
reflection-invariant `Z`, `ContinuumSep.PairBoundSep` at `Renorm.connected hN Z` (E), a window
`L > 0`, `WeakCouplingWindow.FixedWindowDecay τ 0 hN L` (M) and `PairLowerBound hN Z τ`:
`ClayRoutes.ClayContinuumPair hN Z τ hZ hB L` (`ContinuumSep.continuum_gap_sep`,
`connectedTwoPointNonzero_of_pairLowerBound`, `ContinuumSep.exists_orth_ne_zero_sep`).

DERIVED: `2` is the least rank with a non-zero Haar variance
(`WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay`'s); `0` is the excluded colour count, the
lower end of `L` and the reflection plane offset of `FixedWindowDecay τ 0`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem clay_continuum_pair_of_pairLowerBound (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuumPair hN Z τ hZ hB L := by
  obtain ⟨c, hc, hG⟩ := ContinuumCluster.towerGapAt_dyBeta_of_fixedWindowDecay hN2 hN τ hL hW
  exact clay_continuum_pair_of_towerGapAt hN _ Z τ hZ hB (div_pos hc hL) hG hL hP

#print axioms clay_continuum_pair_of_pairLowerBound

/-- **The Clay continuum statement from E, M and the pair lower bound.** As
`clay_continuum_pair_of_pairLowerBound`, with E as `ContinuumSep.UniformBoundSep` at
`Renorm.connected hN Z` (`ContinuumSep.pairBoundSep_of_uniformBoundSep`):
`ClayRoutes.ClayContinuum hN Z τ hZ hB L`. `ClayRoutes.clay_continuum_of_fixedWindowDecay` is this with
`PairLowerBound` from N and Y (`pairLowerBound_of_af`).

DERIVED: `2` is the least rank with a non-zero Haar variance
(`WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay`'s); `0` is the excluded colour count, the
lower end of `L` and the reflection plane offset of `FixedWindowDecay τ 0`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem clay_continuum_of_pairLowerBound (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_pair_of_pairLowerBound hN2 hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_uniformBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hB) hL hW hP

#print axioms clay_continuum_of_pairLowerBound

/-- **The Clay continuum statement from the reflection-diagonal bound, M and the pair lower bound.** As
`clay_continuum_pair_of_pairLowerBound`, with E as `ContinuumSep.DiagBoundSep` at
`Renorm.connected hN Z`: each separated positive-time monomial `P` has one constant bounding
`latSkR(θP ∪ P)` eventually in the step. `ContinuumSep.pairBoundSep_of_diagBoundSep`, under
`Renorm.connected_reflCompat hN Z τ hZ`, gives the pair bound the capstone reads.

DERIVED: `2` is the least rank with a non-zero Haar variance
(`WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay`'s); `0` is the excluded colour count, the
lower end of `L` and the reflection plane offset of `FixedWindowDecay τ 0`; `4` in `Fin 4` is the
spacetime dimension. -/
theorem clay_continuum_of_diagBoundSep (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuumPair hN Z τ hZ
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) τ
        (Renorm.connected_reflCompat hN Z τ hZ) hD) L :=
  clay_continuum_pair_of_pairLowerBound hN2 hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hD) hL hW hP

#print axioms clay_continuum_of_diagBoundSep

end Capstone

/-! ## 3. The field-independent renormalisation `rhoA` -/

section RhoA

/-- **The field-strength factor of `ContinuumNontrivial.rhoA`**: `a_k⁻⁴` at `a_k = dySpacing N k`,
the same for every field.

DERIVED: `4` is the canonical dimension of `tr F²` in four dimensions, as in
`ContinuumNontrivial.rhoA`. CHOSEN: the constant `1` in front of `a⁻⁴`, as in `ContinuumNontrivial.rhoA`;
`PairLowerBound` and `UniformBoundSep` are unchanged under `Z ↦ λZ`, `λ ≠ 0`. -/
def zA (N : ℕ) : ℕ → LField (MassGap.SUN.SU N) → ℝ := fun j _ => (dySpacing N j ^ 4)⁻¹

/-- `rhoA` is the connected renormalisation at `zA`.

DERIVED: `0` is the excluded colour count. -/
theorem rhoA_eq (hN : N ≠ 0) : ContinuumNontrivial.rhoA hN = Renorm.connected hN (zA N) := rfl

#print axioms rhoA_eq

/-- `zA` does not depend on the field, so in particular not on its reflection.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem zA_refl (τ : Fin 4) :
    ∀ (k : ℕ) (O : LField (MassGap.SUN.SU N)), zA N k (O.refl τ) = zA N k O :=
  fun _ _ => rfl

#print axioms zA_refl

/-- **N and Y at `rhoA` give the lower bound at `zA`.**

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem pairLowerBound_rhoA (hN : N ≠ 0) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (ContinuumNontrivial.rhoA hN) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    PairLowerBound hN (zA N) τ :=
  pairLowerBound_of_af hN (zA N) τ (zA_refl τ) O G hconv hY

#print axioms pairLowerBound_rhoA

end RhoA

end MassGap.ClayReduce
