import Mathlib
import MassGap.PeriodicState

/-!
# MassGap.PeriodicReduce — the reads at the periodic state from one inequality per observable on the periodic lattices

This module states the pairings of the gauge-invariant Wilson transfer operator at the periodic state
`PeriodicState.periodicState hN β`, whose existence at every coupling is proved, so no state input
remains.

## What is here

1. `torusConn τ p hN β j x c` is the connected reflected-shifted pairing of `x` at lag `c` in the
   periodic Wilson state `torusState hN (2j + 1) β` (extent `2(j + 1)`):
   `μⱼ(θx · Sᶜx) − μⱼ(θx)·μⱼ(Sᶜx)`, with `θ = ireflObs τ (2p)` and `S` the unit shift along `τ`.
   Each of its three expectations converges to the periodic state's along `periodicUltra hN β`
   (`tendsto_torusConn`).
2. `periodic_form_vac`, `periodic_form_pow`: at `periodicGaugeInvData`, `D.form x D.vac = ν(θx)` and
   `D.form x (Tᶜ x) = ν(θx · Sᶜx)`, `ν = periodicState hN β`
   (`GaugeInvariantAlgebra.gaugeInv_form_pow` at the three periodic state facts).
3. Slack along a filter: `nonneg_of_slack_filter` and `slack_of_nonneg_filter`, and
   `state_centred_mul`, the state of a product centred at the first factor's mean.

## Scope

Along `periodicUltra` the sets of `j` known to belong to it are the tails (`periodicUltra_le`), the
power-of-two extents (`periodicUltra_le_dyadic`) and the sets where a given `2^i` divides the extent
`2j + 2` (`periodicUltra_dvd`). The module does not assert a non-zero vacuum complement; that is
`PeriodicContent.periodic_exists_ne_zero_orth_vacuum`.
-/

namespace MassGap.PeriodicReduce

open MassGap MassGap.GNSHilbert MassGap.PeriodicState

variable {N : ℕ}

/-! ## 1. Slack along a filter -/

section Slack

/-- A real family converging along a non-trivial filter `l`, and at least `−ε` eventually along `l`
for every `ε > 0`, has a nonnegative limit.

DERIVED: `0` is the lower bound concluded and the sign of each slack `ε`; the `2` in the proof halves
a negative limit. -/
theorem nonneg_of_slack_filter {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → ℝ} {L : ℝ}
    (hu : Filter.Tendsto u l (nhds L)) (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, -ε ≤ u i) : 0 ≤ L := by
  by_contra hneg
  have hL : L < 0 := not_le.mp hneg
  have hle : -(-L / 2) ≤ L := ge_of_tendsto hu (h (-L / 2) (by linarith))
  linarith

#print axioms nonneg_of_slack_filter

/-- A real family converging along `l` to a nonnegative limit is eventually at least `−ε` along `l`,
for every `ε > 0`.

DERIVED: `0` is the sign of the limit and of each slack `ε`. -/
theorem slack_of_nonneg_filter {ι : Type*} {l : Filter ι} {u : ι → ℝ} {L : ℝ}
    (hu : Filter.Tendsto u l (nhds L)) (hL : 0 ≤ L) : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, -ε ≤ u i := by
  intro ε hε
  filter_upwards [hu.eventually (lt_mem_nhds (show L - ε < L by linarith))] with n hn
  linarith

#print axioms slack_of_nonneg_filter

/-- A state against a product of two observables centred at the first one's mean:
`ν((f − ν f·1)(g − ν f·1)) = ν(f g) − ν f · ν g`.

DERIVED: `1` is the constant observable. -/
theorem state_centred_mul {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (f g : C(X, ℝ)) :
    ν ((f - ν f • 1) * (g - ν f • 1)) = ν (f * g) - ν f * ν g := by
  have hexp : (f - ν f • 1) * (g - ν f • 1)
      = f * g - ν f • g - ν f • f + (ν f * ν f) • (1 : C(X, ℝ)) := by
    ext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.add_apply, smul_eq_mul]
    ring
  rw [hexp]
  simp only [MassGap.DLRLimit.State.map_add, MassGap.DLRLimit.State.map_sub,
    MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one]
  ring

#print axioms state_centred_mul

end Slack

/-! ## 2. The connected pairing on the periodic lattices -/

section Torus

/-- The connected reflected-shifted pairing of `x` at lag `c` in the periodic Wilson state of extent
`2(j + 1)` at coupling `β`: `μⱼ(θx · Sᶜx) − μⱼ(θx)·μⱼ(Sᶜx)`, with `μⱼ = torusState hN (2j + 1) β`,
`θ = ireflObs τ (2p)` the reflection `x_τ ↦ 2p − x_τ` (mirror plane `x_τ = p`), and `S` the unit
shift along `τ`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`; `2` in `2 * p` is
the plane-to-constant doubling; `2` and `1` in `2 * j + 1` index the even-extent family
`torusState hN (2j + 1) β` that `periodicState` is the limit of. -/
noncomputable def torusConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (c : ℕ) : ℝ :=
  torusState hN (2 * j + 1) β
      (MassGap.LatticeReflection.ireflObs τ (2 * p) x
        * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
    - torusState hN (2 * j + 1) β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
      * torusState hN (2 * j + 1) β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)

/-- The periodic connected pairing converges to the periodic state's along `periodicUltra hN β`:
each of its three expectations does (`PeriodicState.tendsto_periodicState`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
theorem tendsto_torusConn (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (c : ℕ) :
    Filter.Tendsto (fun j => torusConn τ p hN β j x c)
      ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ)
      (nhds (periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
        - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x))) :=
  (tendsto_periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
      * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)).sub
    ((tendsto_periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)).mul
      (tendsto_periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)))

#print axioms tendsto_torusConn

end Torus

/-! ## 3. The transfer form at the periodic state -/

section Form

/-- The gauge-invariant transfer form at the periodic state, against the vacuum, is the periodic
state's one-point function of the reflected observable: `D.form x D.vac = ν(θx)`,
`D = periodicGaugeInvData τ p hN β`, `ν = periodicState hN β`. The form is `ν(θx · y)` and the vacuum
is the constant `1`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
theorem periodic_form_vac (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) :
    (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac
      = periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := by
  have h : (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac
      = periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) := rfl
  rw [h, mul_one]

#print axioms periodic_form_vac

/-- The gauge-invariant transfer form at the periodic state, at a translate, is the periodic state's
reflected-shifted pairing: `D.form x (Tᶜ x) = ν(θx · Sᶜx)`. `GaugeInvariantAlgebra.gaugeInv_form_pow`
at the three facts `periodicGaugeInvData` is built from.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling of the
reflection plane. -/
theorem periodic_form_pow (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (c : ℕ) :
    (periodicGaugeInvData τ p hN β).form x (((periodicGaugeInvData τ p hN β).T ^ c) x)
      = periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) :=
  MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p (periodicState hN β)
    (periodicState_reflInvariant hN β τ (2 * p)) (periodicState_reflPositive hN β τ p)
    (periodicState_shift hN β τ) x c

#print axioms periodic_form_pow

end Form

/-! ## 4. W5 at the periodic state, its converse, and the composition -/

section Compose

end Compose

end MassGap.PeriodicReduce
