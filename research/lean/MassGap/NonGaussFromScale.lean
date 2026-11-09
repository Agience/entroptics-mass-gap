import Mathlib
import MassGap.SU2Best
import MassGap.StrongKernelNear
import MassGap.VortexStrong

/-!
# MassGap.NonGaussFromScale — the three-point input as a statement about the bare Wilson measures

The `SU(2)` target asks `ObsLower h2N (zFix 2 zri zwe)`. Under `SepConv` it is the
target clause `NonGaussianT` (`InputsTriage.nonGaussianT_rhoD_iff_lower`). This module separates the
normalisation `z_sc = 2/a_k⁴` from the dynamics, states the remaining dynamical content as one clause on
the bare Wilson states `stateK`, and records why the strong-coupling theorems of the tree do not supply
it. Declarations are in the namespace `MassGap.NonGaussFromScale`.

## 1. The bare reading and the scaling (proved)

`bareRead3 hN k a b c` is the unit-strength connected three-point reading of the observer's field
`obs N` at step `k`: the state `stateK hN k` (the Wilson state at `dyBeta k`) of the product of the three
mean-subtracted fields smeared at spacing `a_k = dySpacing N k` (each smearing carries `a_k⁴` per site).

* `obsRead_zFix`: `obsRead hN (zFix N zri zwe) k ![a, b, c] = (8 / a_k¹²) · bareRead3 hN k a b c` at every
  step (`NonGaussLink.obsRead_eq`, `z_sc = 2/a_k⁴`). So the renormalised reading has a finite non-zero
  limit exactly when the bare reading is of size `a_k¹²`; this is the scaling of a connected three-point
  function of a dimension-`4` field at fixed physical separations.

## 2. The clause (definition) and what it is (proved)

`ThreePointAtScale hN ℓ`: a triple of continuous test functions, pairwise `ℓ`-separated, and `κ > 0` with
`κ · a_k¹² ≤ |bareRead3 hN k a b c|` on a set of `ultra`. It reads only `stateK`, `dySpacing` and the
observer's field; it does not read `z`, the continuum limit, or any convergence statement.

* `obsLower_of_scale`: for `ℓ > 0`, `ThreePointAtScale hN ℓ` gives `ObsLower hN (zFix N zri zwe)` for every
  `zri`, `zwe` (with `κ' = 8κ`, `d = ℓ`).
* `scale_of_obsLower`: `ObsLower hN (zFix N zri zwe)` gives `ThreePointAtScale hN d` at its separation `d`
  (with `κ' = κ/8`).
* **`obsLower_zFix_iff`**: `ObsLower hN (zFix N zri zwe) ↔ ∃ ℓ > 0, ThreePointAtScale hN ℓ`.

So the clause is `ObsLower` with the normalisation removed, and nothing weaker gives `NonGaussianT`:
by `InputsTriage.obsLower_of_nonGaussianT`, under `SepConv` any statement
giving `NonGaussianT` gives `ObsLower`, hence `∃ ℓ > 0, ThreePointAtScale hN ℓ`. Restating `ObsLower` in
this form discharges nothing; what it changes is that the open input is now a statement about the bare
measures alone.

* `nonGaussianT_two_of_scale`: the substrate and flow bundles of `SU2Best` (for `SepConv`, through
  `WardFromLattice.sepConv_of_multiScale`) and `ThreePointAtScale h2N b` at the substrate's scale `b` give
  `NonGaussianT h2N (rhoD (fR 2) (zFix 2 zri zwe))`.

## 3. No capstone through `SubstrateAt`

No `ClayStatementAt` is stated from `SubstrateAt`: its `endpoint` field,
`MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 4. The strong-coupling theorems do not reach `stateK` (proved, and the reading of it argued)

Every step's coupling is at least `1` (`ContinuumSchwinger.one_le_dyBeta`), and tends to infinity
(`tendsto_dyBeta`). `dyBeta_outside_strong` proves, at every step `k`:
* `¬ |dyBeta k| ≤ 1/65536`, the coupling hypothesis of `StrongKernelNear.kernelNear_strong_explicit`;
* `¬ dyBeta k ≤ VortexStrong.β₀`, the coupling hypothesis of `VortexStrong.condenses_vortexR_strong`;
* `1 < coreRate K (dyBeta k)` for every `K`, so the rate of `StrongCoupling`'s clustering bound is not
  below one at any step.
SURVEY (not formalised): the strong-coupling statements in the tree (`StrongCoupling`, `StrongKernelNear`, `VortexStrong`,
`ChunkActivity`, `PolymerCount`, `MatchAt`) are upper bounds (decay, clustering, condensation); none is a
lower bound on a connected correlation, and none is a three-point statement. `ChunkActivity.wilsonChunk`
is a Wilson activity on a coarse torus at a coupling `βeff` that is an input; no declaration constructs
an effective measure at scale `b` from `stateK` (`MultiScale`, §1), so a statement about the coarse
theory has no proved link to `bareRead3`.

ARGUED (not formalised): at small bare coupling the connected three-point function of three plaquettes
on the faces of one lattice cube meeting at a corner is non-zero at order `β³` in the character
expansion (the three remaining faces close the surface). That is a statement at lattice separation `1`
and small `β`. The clause asks a lower bound at physical separation `ℓ`, i.e. lattice separation
`ℓ/a_k → ∞`, at `β = dyBeta k → ∞`, of size `a_k¹²`: the strong-coupling expansion is outside its
domain there. The strong-coupling reading "the theory at scale `b` is strongly coupled" is a statement
about an effective theory at scale `b`; turning it into `ThreePointAtScale` needs the map from `stateK`
to that effective theory together with a lower bound that survives it, which the tree does not have.
So `ThreePointAtScale` stays a clause. The short-distance end gives no help either:
`ShortDistance.treeThreeTr_eq_zero` makes the tree value of the trace three-point function vanish.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `3` the number of insertions; `4` the dimension, the power of `a_k` per
insertion; `12 = 3 · 4`; `8 = 2³`, `2` the limit of `z_sc · a_k⁴`; `1/65536` and `β₀` the coupling bounds
of the two theorems named; `1` the lower bound of `dyBeta`; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.NonGaussFromScale

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.ObserverChoice MassGap.SU2Best

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The bare reading and the scaling -/

/-- **The bare three-point reading** of the observer's field at step `k`: unit field strength, mean
subtracted in `stateK hN k`. DERIVED: `3` the number of insertions. -/
def bareRead3 (hN : N ≠ 0) (k : ℕ) (a b c : TestFn) : ℝ :=
  latSkR hN (NonTrivialCanonical.rho1 hN) k (fun i => (obs N, (![a, b, c] : Fin 3 → TestFn) i))

/-- **The renormalised reading at `zFix` is `8/a_k¹²` times the bare reading.**
DERIVED: `8 = 2³`, `12 = 3 · 4`. -/
theorem obsRead_zFix (hN : N ≠ 0) (zri zwe : ℕ → ℝ) (k : ℕ) (a b c : TestFn) :
    NonGaussLink.obsRead hN (ZCanon.zFix N zri zwe) k ![a, b, c]
      = 8 / dySpacing N k ^ 12 * bareRead3 hN k a b c := by
  rw [NonGaussLink.obsRead_eq]
  show (2 / dySpacing N k ^ 4) ^ 3 * bareRead3 hN k a b c = _
  congr 1
  rw [div_pow, ← pow_mul]
  norm_num

/-- `0 < a_k¹²`. DERIVED: `12` as in `obsRead_zFix`. -/
theorem dySpacing_pow12_pos (hN : N ≠ 0) (k : ℕ) : 0 < dySpacing N k ^ 12 :=
  pow_pos (dySpacing_pos (Nat.one_le_iff_ne_zero.mpr hN) k) 12

/-! ## 2. The clause -/

/-- **The three-point clause at a fixed physical scale**, on the bare Wilson states. A triple of
continuous, pairwise `ℓ`-separated test functions and `κ > 0` with `κ · a_k¹² ≤ |bareRead3 hN k a b c|`
on a set of `ultra`.

DERIVED: `12` the scaling of three dimension-`4` insertions; `0` the sign of `κ`. -/
def ThreePointAtScale (hN : N ≠ 0) (ℓ : ℝ) : Prop :=
  ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
    ∧ ContinuumSep.sepBy ℓ a b ∧ ContinuumSep.sepBy ℓ a c ∧ ContinuumSep.sepBy ℓ b c
    ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k in (ultra : Filter ℕ),
        κ * dySpacing N k ^ 12 ≤ |bareRead3 hN k a b c|

/-- **`ObsLower` at `zFix` from the clause at a positive scale**, with `κ' = 8κ`, `d = ℓ`.
DERIVED: `8` as in `obsRead_zFix`. -/
theorem obsLower_of_scale (hN : N ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) (zri zwe : ℕ → ℝ)
    (h : ThreePointAtScale hN ℓ) : InputsTriage.ObsLower hN (ZCanon.zFix N zri zwe) := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, κ, hκ, hev⟩ := h
  refine ⟨a, b, c, ha, hb, hc, ⟨ℓ, hℓ, hab, hac, hbc⟩, 8 * κ, by linarith, hev.mono fun k hk => ?_⟩
  have h12 := dySpacing_pow12_pos hN k
  rw [obsRead_zFix, abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 8) h12),
    div_mul_eq_mul_div, le_div_iff₀ h12]
  linarith

/-- **The clause from `ObsLower` at `zFix`**, at its separation `d`, with `κ' = κ/8`.
DERIVED: `8` as in `obsRead_zFix`. -/
theorem scale_of_obsLower (hN : N ≠ 0) (zri zwe : ℕ → ℝ)
    (h : InputsTriage.ObsLower hN (ZCanon.zFix N zri zwe)) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale hN ℓ := by
  obtain ⟨a, b, c, ha, hb, hc, ⟨d, hd, hab, hac, hbc⟩, κ, hκ, hev⟩ := h
  refine ⟨d, hd, a, b, c, ha, hb, hc, hab, hac, hbc, κ / 8, by linarith,
    hev.mono fun k hk => ?_⟩
  have h12 := dySpacing_pow12_pos hN k
  rw [obsRead_zFix, abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 8) h12),
    div_mul_eq_mul_div, le_div_iff₀ h12] at hk
  linarith

/-- **`ObsLower` at `zFix` is the clause at some positive scale.** DERIVED: no numeral. -/
theorem obsLower_zFix_iff (hN : N ≠ 0) (zri zwe : ℕ → ℝ) :
    InputsTriage.ObsLower hN (ZCanon.zFix N zri zwe) ↔ ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale hN ℓ :=
  ⟨scale_of_obsLower hN zri zwe, fun ⟨_, hℓ, h⟩ => obsLower_of_scale hN hℓ zri zwe h⟩

/-- **`NonGaussianT` from the clause at the substrate's scale**: `SepConv` from the substrate and flow
bundles (`WardFromLattice.sepConv_of_multiScale`), then `InputsTriage.nonGaussianT_rhoD_of_lower`.
DERIVED: `2` is `SU(2)`. -/
theorem nonGaussianT_two_of_scale {zri zwe : ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {W : ConfFlow 2} {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateAt W (ZCanon.zFix 2 zri zwe) b Wf)
    (F : GradientFlowProps Wf cf (ZCanon.zFix 2 zri zwe) μ)
    (h3 : ThreePointAtScale h2N b) :
    NonGaussianT h2N (rhoD (fR 2) (ZCanon.zFix 2 zri zwe)) :=
  InputsTriage.nonGaussianT_rhoD_of_lower h2N (fR 2) _
    (WardFromLattice.sepConv_of_multiScale (S.toStrong F).toRenAt F.coef)
    (obsLower_of_scale h2N S.b_pos zri zwe h3)

/-! ## 4. The strong-coupling theorems do not reach `stateK` -/

/-- **Every step's coupling is outside the proved strong-coupling regimes**: it violates the coupling
hypothesis of `StrongKernelNear.kernelNear_strong_explicit` (`|β| ≤ 1/65536`) and of
`VortexStrong.condenses_vortexR_strong` (`β ≤ β₀`), and the rate `coreRate K` of `StrongCoupling`'s
clustering bound is above one there, for every `K`.

DERIVED: `1` the lower bound of `dyBeta` and the threshold of the rate; `1/65536`, `β₀` the two
coupling bounds; `2`, `3`, `4` the constants of `coreRate` and of `exp (2β) ≥ 1 + 2β ≥ 3`. -/
theorem dyBeta_outside_strong (hN : 1 ≤ N) (k : ℕ) :
    ¬ |dyBeta hN k| ≤ 1 / 65536 ∧ ¬ dyBeta hN k ≤ VortexStrong.β₀
      ∧ ∀ K : ℕ, 1 < StrongCoupling.coreRate K (dyBeta hN k) := by
  have h1 := one_le_dyBeta hN k
  refine ⟨fun h => ?_, fun h => ?_, fun K => ?_⟩
  · have := le_trans h1 (le_abs_self (dyBeta hN k))
    linarith
  · have hb : VortexStrong.β₀ < 1 := by
      show (1 : ℝ) / 4000000 < 1
      norm_num
    linarith
  · set β := dyBeta hN k
    have hK : (4 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
      linarith
    have he2 : (2 : ℝ) ≤ Real.exp (2 * β) - 1 := by
      have := Real.add_one_le_exp (2 * β)
      linarith
    have he4 : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp
      (mul_nonneg (by linarith) (Nat.cast_nonneg K))
    unfold StrongCoupling.coreRate
    have h8 : (8 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) := by
      nlinarith
    nlinarith

end MassGap.NonGaussFromScale

end

#print axioms MassGap.NonGaussFromScale.obsRead_zFix
#print axioms MassGap.NonGaussFromScale.obsLower_of_scale
#print axioms MassGap.NonGaussFromScale.scale_of_obsLower
#print axioms MassGap.NonGaussFromScale.obsLower_zFix_iff
#print axioms MassGap.NonGaussFromScale.nonGaussianT_two_of_scale
#print axioms MassGap.NonGaussFromScale.dyBeta_outside_strong
