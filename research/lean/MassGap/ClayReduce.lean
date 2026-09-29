import Mathlib
import MassGap.ClayRoutes
import MassGap.PairCorrSharp

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
  `PairLowerBound`; `clay_continuum_pair_of_boxPatchGap_pairLowerBound`, the finite-size route.
* `clay_continuum_of_diagBoundSep`, `clay_continuum_of_boxPatchGap_diagBoundSep`: the same with E as
  `DiagBoundSep`, the bound on the unshifted reflection diagonal `θP ∪ P` alone.
* `clay_continuum_of_pairLowerBound`, `clay_continuum_of_boxPatchGap_pairLowerBound`: `ClayContinuum`
  with E as `UniformBoundSep`.

## The field-independent renormalisation

`ContinuumNontrivial.rhoA hN` is `Renorm.connected hN (zA N)`, `zA N k O = a_k⁻⁴`, the same factor for
every field (`rhoA_eq`). `clay_continuum_floor_su2_rhoA` and `clay_continuum_floor_su3_rhoA` are the
floor capstones at `Z = zA N` with E as `UniformBoundSep`;
`clay_continuum_floor_su2_rhoA_diagBoundSep` and `clay_continuum_floor_su3_rhoA_diagBoundSep` with E as
`DiagBoundSep`. `pairLowerBound_rhoA` gives their `PairLowerBound` from N and Y at `rhoA`.

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

/-- **The lower bound on one reflected cube pair (stated, not proved).** For some local
gauge-invariant field `O`, margin `t > 0`, side `ℓ` and `c > 0`, eventually in the step,
`c ≤ latSkR(θQ ∪ Q)` for `Q = mono1 (O, cubeTest t ℓ)` at the connected renormalisation
`Renorm.connected hN Z`. A negative `ℓ` gives the empty cube and `latSkR = 0`, which `c > 0` excludes.

DERIVED: `0` is the excluded colour count and the lower end of `t` and `c`; `4` in `Fin 4` is the
spacetime dimension. -/
def PairLowerBound (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) : Prop :=
  ∃ (O : LField (MassGap.SUN.SU N)) (t ℓ c : ℝ), 0 < t ∧ 0 < c ∧
    ∀ᶠ k in atTop, c ≤ latSkR hN (Renorm.connected hN Z) k
      (pairFam τ (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
        (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)))

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
theorem connectedTwoPointNonzero_of_pairLowerBound (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (hP : PairLowerBound hN Z τ) :
    ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨O, t, ℓ, c, ht, hc, hev⟩ := hP
  have hQ : ∃ d : ℝ, 0 < d ∧ ContinuumSep.sepPos τ d
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) :=
    ⟨t, ht, ContinuumNontrivial.sepPos_mono1 τ O t ℓ⟩
  have htend := ContinuumSep.tendsto_pair_sep_of_pairBound hN (Renorm.connected hN Z) τ hB hQ hQ
  have hge : c ≤ kern hN (Renorm.connected hN Z) τ
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) :=
    ge_of_tendsto htend (hev.filter_mono ultra_le)
  refine ⟨ContinuumNontrivial.sepCube τ O ht ℓ, ?_⟩
  show kern hN (Renorm.connected hN Z) τ
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ))
    - kern hN (Renorm.connected hN Z) τ (emptyMono N)
      (ContinuumNontrivial.mono1 (O, ContinuumNontrivial.cubeTest t ℓ)) ^ 2 ≠ 0
  rw [ContinuumNontrivial.kern_empty_mono1 hN Z τ hZ O (ContinuumNontrivial.cubeTest t ℓ),
    zero_pow two_ne_zero, sub_zero]
  exact (lt_of_lt_of_le hc hge).ne'

#print axioms connectedTwoPointNonzero_of_pairLowerBound

end Lower

/-! ## 2. The capstones on the lower bound -/

section Capstone

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
  obtain ⟨c, hc, hgap⟩ := ContinuumSep.continuum_gap_sep hN2 hN (Renorm.connected hN Z) τ hB
    (Renorm.connected_reflCompat hN Z τ hZ) hL hW
  have hne := connectedTwoPointNonzero_of_pairLowerBound hN Z τ hZ hB hP
  exact ⟨c, hc, fun m =>
    ⟨hgap m, ContinuumSep.exists_orth_ne_zero_sep hN (Renorm.connected hN Z) τ hB
      (Renorm.connected_reflCompat hN Z τ hZ) m hne⟩⟩

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

/-- **The finite-size route with the pair bound and the pair lower bound.** As
`ClayRoutes.clay_continuum_of_boxPatchGap`, with E as `ContinuumSep.PairBoundSep` and N and Y replaced
by `PairLowerBound hN Z τ`: `BoxPatch.BoxPatchGap hN β₀ n γ` gives the IR gap at
`HeatBathLocal.boxRate N β₀ n γ` (`HeatBathLocal.irGapAt_boxRate`), the UV step below it gives
`FixedWindowDecay` (`UVIRSplit.fixedWindowDecay_of_uv_ir_below`), and
`clay_continuum_pair_of_pairLowerBound` concludes.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension; `1` in
the proof is the least colour count; `17N²/(88π²)` is the peak of `aRun N`, as in
`ClayRoutes.clay_continuum_of_boxPatchGap`. CHOSEN: the scope restriction `_hpeak`, not used by the
proof, as in `ClayRoutes.clay_continuum_of_boxPatchGap`. -/
theorem clay_continuum_pair_of_boxPatchGap_pairLowerBound (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ))
    (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuumPair hN Z τ hZ hB L := by
  obtain ⟨ε, E, hε, hbud, hEM, hstep⟩ := huv
  exact clay_continuum_pair_of_pairLowerBound hN2 hN Z τ hZ hB hL
    (UVIRSplit.fixedWindowDecay_of_uv_ir_below τ 0 hN2 hN hL hβ₀ hUVβ₀ hbud hEM hε hstep
      (HeatBathLocal.irGapAt_boxRate τ 0 (by omega) hN hβ₀ hbox).2) hP

#print axioms clay_continuum_pair_of_boxPatchGap_pairLowerBound

/-- **The finite-size route with the pair lower bound.** As
`clay_continuum_pair_of_boxPatchGap_pairLowerBound`, with E as `ContinuumSep.UniformBoundSep`
(`ContinuumSep.pairBoundSep_of_uniformBoundSep`): `ClayRoutes.ClayContinuum hN Z τ hZ hB L`.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension;
`17N²/(88π²)` is the peak of `aRun N`, as in `ClayRoutes.clay_continuum_of_boxPatchGap`. CHOSEN: the
scope restriction `_hpeak`, not used by the proof, as in `ClayRoutes.clay_continuum_of_boxPatchGap`. -/
theorem clay_continuum_of_boxPatchGap_pairLowerBound (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ))
    (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_pair_of_boxPatchGap_pairLowerBound hN2 hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_uniformBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hB) hL hβ₀ hUVβ₀ _hpeak hbox huv hP

#print axioms clay_continuum_of_boxPatchGap_pairLowerBound

/-- **The finite-size route with the reflection-diagonal bound and the pair lower bound.** As
`clay_continuum_pair_of_boxPatchGap_pairLowerBound`, with E as `ContinuumSep.DiagBoundSep`
(`ContinuumSep.pairBoundSep_of_diagBoundSep` under `Renorm.connected_reflCompat hN Z τ hZ`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension;
`17N²/(88π²)` is the peak of `aRun N`, as in `ClayRoutes.clay_continuum_of_boxPatchGap`. CHOSEN: the
scope restriction `_hpeak`, not used by the proof, as in `ClayRoutes.clay_continuum_of_boxPatchGap`. -/
theorem clay_continuum_of_boxPatchGap_diagBoundSep (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) τ) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ))
    (hP : PairLowerBound hN Z τ) :
    ClayRoutes.ClayContinuumPair hN Z τ hZ
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) τ
        (Renorm.connected_reflCompat hN Z τ hZ) hD) L :=
  clay_continuum_pair_of_boxPatchGap_pairLowerBound hN2 hN Z τ hZ
    (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN Z) τ
      (Renorm.connected_reflCompat hN Z τ hZ) hD) hL hβ₀ hUVβ₀ _hpeak hbox huv hP

#print axioms clay_continuum_of_boxPatchGap_diagBoundSep

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

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(2)`, AT `rhoA`.** As
`PairCorrSharp.clay_continuum_floor_su2`, at the field-independent factor `Z = zA 2`
(`Renorm.connected h2 (zA 2) = ContinuumNontrivial.rhoA h2`, `rhoA_eq`), with N and Y replaced by
`PairLowerBound`: E (`hB`), the UV step below the box's rate (`huv`) and `PairLowerBound` (`hP`) are
carried. `pairLowerBound_rhoA` gives `hP` from N and Y at `rhoA`.

DERIVED: `2` is the rank; `0` is the excluded colour count, the reflection plane and the lower end of
`L`; `4` in `Fin 4` is the spacetime dimension; `2606`, `307/10000` are
`PairCorrSharp.boxPatchGap_floor_su2`'s side and gap. -/
theorem clay_continuum_floor_su2_rhoA (h2 : (2 : ℕ) ≠ 0) (τ : Fin 4)
    (hB : ContinuumSep.UniformBoundSep h2 (ContinuumNontrivial.rhoA h2)) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h2 (PairCorrSharp.floorBeta 2) (PairCorrSharp.floorBeta 2)
      (HeatBathLocal.boxRate 2 (PairCorrSharp.floorBeta 2) 2606 (307 / 10000)))
    (hP : PairLowerBound h2 (zA 2) τ) :
    ClayRoutes.ClayContinuum h2 (zA 2) τ (zA_refl τ) hB L :=
  clay_continuum_of_boxPatchGap_pairLowerBound (by norm_num) h2 (zA 2) τ (zA_refl τ) hB hL
    (β₀ := PairCorrSharp.floorBeta 2) (βUV := PairCorrSharp.floorBeta 2)
    (PairCorrSharp.floorBeta_pos h2) le_rfl le_rfl (PairCorrSharp.boxPatchGap_floor_su2 h2) huv hP

#print axioms clay_continuum_floor_su2_rhoA

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(3)`, AT `rhoA`.**

DERIVED: `3` is the rank; `2` in the proof is the least rank with a non-zero Haar variance; `0` is the
excluded colour count, the reflection plane and the lower end of `L`; `4` in `Fin 4` is the spacetime dimension; `545`,
`367/2500` are `PairCorrSharp.boxPatchGap_floor_su3`'s side and gap. -/
theorem clay_continuum_floor_su3_rhoA (h3 : (3 : ℕ) ≠ 0) (τ : Fin 4)
    (hB : ContinuumSep.UniformBoundSep h3 (ContinuumNontrivial.rhoA h3)) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h3 (PairCorrSharp.floorBeta 3) (PairCorrSharp.floorBeta 3)
      (HeatBathLocal.boxRate 3 (PairCorrSharp.floorBeta 3) 545 (367 / 2500)))
    (hP : PairLowerBound h3 (zA 3) τ) :
    ClayRoutes.ClayContinuum h3 (zA 3) τ (zA_refl τ) hB L :=
  clay_continuum_of_boxPatchGap_pairLowerBound (by norm_num) h3 (zA 3) τ (zA_refl τ) hB hL
    (β₀ := PairCorrSharp.floorBeta 3) (βUV := PairCorrSharp.floorBeta 3)
    (PairCorrSharp.floorBeta_pos h3) le_rfl le_rfl (PairCorrSharp.boxPatchGap_floor_su3 h3) huv hP

#print axioms clay_continuum_floor_su3_rhoA

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(2)`, AT `rhoA`, ON THE REFLECTION DIAGONAL.** As
`clay_continuum_floor_su2_rhoA`, with E as `ContinuumSep.DiagBoundSep h2 (rhoA h2) τ`: each separated
positive-time monomial `P` has one constant bounding `latSkR(θP ∪ P)` at `rhoA` eventually in the step
(`clay_continuum_of_boxPatchGap_diagBoundSep`). The reflection compatibility is
`Renorm.connected_reflCompat` at `zA_refl`, no hypothesis.

DERIVED: `2` is the rank; `0` is the excluded colour count, the reflection plane and the lower end of
`L`; `4` in `Fin 4` is the spacetime dimension; `2606`, `307/10000` are
`PairCorrSharp.boxPatchGap_floor_su2`'s side and gap. -/
theorem clay_continuum_floor_su2_rhoA_diagBoundSep (h2 : (2 : ℕ) ≠ 0) (τ : Fin 4)
    (hD : ContinuumSep.DiagBoundSep h2 (ContinuumNontrivial.rhoA h2) τ) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h2 (PairCorrSharp.floorBeta 2) (PairCorrSharp.floorBeta 2)
      (HeatBathLocal.boxRate 2 (PairCorrSharp.floorBeta 2) 2606 (307 / 10000)))
    (hP : PairLowerBound h2 (zA 2) τ) :
    ClayRoutes.ClayContinuumPair h2 (zA 2) τ (zA_refl τ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep h2 (Renorm.connected h2 (zA 2)) τ
        (Renorm.connected_reflCompat h2 (zA 2) τ (zA_refl τ)) hD) L :=
  clay_continuum_of_boxPatchGap_diagBoundSep (by norm_num) h2 (zA 2) τ (zA_refl τ) hD hL
    (β₀ := PairCorrSharp.floorBeta 2) (βUV := PairCorrSharp.floorBeta 2)
    (PairCorrSharp.floorBeta_pos h2) le_rfl le_rfl (PairCorrSharp.boxPatchGap_floor_su2 h2) huv hP

#print axioms clay_continuum_floor_su2_rhoA_diagBoundSep

/-- **THE CONTINUUM CLAY STATEMENT AT THE FLOOR, `SU(3)`, AT `rhoA`, ON THE REFLECTION DIAGONAL.** As
`clay_continuum_floor_su3_rhoA`, with E as `ContinuumSep.DiagBoundSep h3 (rhoA h3) τ`
(`clay_continuum_of_boxPatchGap_diagBoundSep`).

DERIVED: `3` is the rank; `2` in the proof is the least rank with a non-zero Haar variance; `0` is the
excluded colour count, the reflection plane and the lower end of `L`; `4` in `Fin 4` is the spacetime
dimension; `545`, `367/2500` are `PairCorrSharp.boxPatchGap_floor_su3`'s side and gap. -/
theorem clay_continuum_floor_su3_rhoA_diagBoundSep (h3 : (3 : ℕ) ≠ 0) (τ : Fin 4)
    (hD : ContinuumSep.DiagBoundSep h3 (ContinuumNontrivial.rhoA h3) τ) {L : ℝ} (hL : 0 < L)
    (huv : ClayRoutes.UVBelowIR τ 0 h3 (PairCorrSharp.floorBeta 3) (PairCorrSharp.floorBeta 3)
      (HeatBathLocal.boxRate 3 (PairCorrSharp.floorBeta 3) 545 (367 / 2500)))
    (hP : PairLowerBound h3 (zA 3) τ) :
    ClayRoutes.ClayContinuumPair h3 (zA 3) τ (zA_refl τ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep h3 (Renorm.connected h3 (zA 3)) τ
        (Renorm.connected_reflCompat h3 (zA 3) τ (zA_refl τ)) hD) L :=
  clay_continuum_of_boxPatchGap_diagBoundSep (by norm_num) h3 (zA 3) τ (zA_refl τ) hD hL
    (β₀ := PairCorrSharp.floorBeta 3) (βUV := PairCorrSharp.floorBeta 3)
    (PairCorrSharp.floorBeta_pos h3) le_rfl le_rfl (PairCorrSharp.boxPatchGap_floor_su3 h3) huv hP

#print axioms clay_continuum_floor_su3_rhoA_diagBoundSep

end RhoA

end MassGap.ClayReduce
