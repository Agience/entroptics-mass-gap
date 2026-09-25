import Mathlib
import MassGap.PeriodicState
import MassGap.ReadReduce

/-!
# MassGap.PeriodicReduce — the reads at the periodic state from one inequality per observable on the periodic lattices

`ReadReduce` states the reads of the gauge-invariant Wilson transfer operator as one inequality per
local observable in the free-boundary boxes, at the free-boundary limit state `htend`. This module
states the same reduction at the periodic state `PeriodicState.periodicState hN β`, whose existence
at every coupling is proved, so no state input remains.

## The chain

1. `torusConn τ p hN β j x c` is the connected reflected-shifted pairing of `x` at lag `c` in the
   periodic Wilson state `torusState hN (2j + 1) β` (extent `2(j + 1)`):
   `μⱼ(θx · Sᶜx) − μⱼ(θx)·μⱼ(Sᶜx)`, with `θ = ireflObs τ (2p)` and `S` the unit shift along `τ`.
   Each of its three expectations converges to the periodic state's along `periodicUltra hN β`
   (`tendsto_torusConn`).
2. `TorusReadsClearWith τ p hN β k γ`: for every gauge-invariant half-space observable `x` and every
   `ε > 0`, eventually along `periodicUltra hN β`, `−ε ≤ marginSum k γ (torusConn τ p hN β j x)`.
   `torusSlack_iff`: observable by observable, that slack condition holds exactly when
   `0 ≤ marginSum k γ` of the periodic state's connected profile.
3. `periodic_form_vac`, `periodic_form_pow`: at `periodicGaugeInvData`, `D.form x D.vac = ν(θx)` and
   `D.form x (Tᶜ x) = ν(θx · Sᶜx)`, `ν = periodicState hN β`
   (`GaugeInvariantAlgebra.gaugeInv_form_pow` at the three periodic state facts).
4. `periodic_localReads_of_torusReads` (W5): the torus input gives the local margin inequality at
   every `x` with `D.form x D.vac = 0`; `periodic_torusReads_of_localReads` is the converse.
5. `periodic_readsClear_of_torusReads`: W5, then `ReadReduce.readsClearWith_of_local` (W4, generic
   in the transfer data), then `ReadReduce.readsClear_of_readsClearWith` (W3, at `γ > 3^{−1/4}`).
   `periodic_gap_of_torusReads` and `periodic_clay_gap_of_torusReads` add
   `PeriodicState.periodic_gap_of_reads` and `PeriodicState.periodic_clay_gap_of_reads`, at `β ≥ 0`.

## Scope

`TorusReadsClearWith` is a hypothesis of the chain; nothing here proves it at any coupling. It is
stated along `periodicUltra hN β`, an ultrafilter chosen by `Classical.choose` in
`PeriodicState.exists_periodic_limit`, and along that filter it is exactly the margin inequality of
the limit state (`torusSlack_iff`). `torusReadsClearWith_of_atTop` derives it from the same slack
inequality along `atTop`, which names no ultrafilter and asks for more: every large periodic
lattice, not those in one ultrafilter set. W3 is sufficient only, as in `ReadReduce`: `ReadsClear`
asks each vector for a cosine average above `3^{−1/4}`, the torus input asks every vector for a
cosine average of at least one common `γ > 3^{−1/4}`. W4 and W5 lose nothing
(`periodic_torusReads_of_localReads`), so the torus input is the gap stated through the periodic
lattices, as the box input is through the boxes, not a weaker condition. Along `periodicUltra` no set
of `j` is known to belong to it beyond the tails `periodicUltra_le` gives, so the checkable form is
`torusReadsClearWith_of_atTop`'s. The chain does not assert a non-zero vacuum complement; that is
`PeriodicContent.periodic_exists_ne_zero_orth_vacuum`.
-/

namespace MassGap.PeriodicReduce

open MassGap MassGap.GNSHilbert MassGap.PeriodicState

variable {N : ℕ}

/-! ## 1. Slack along a filter -/

section Slack

/-- A real family converging along a non-trivial filter `l`, and at least `−ε` eventually along `l`
for every `ε > 0`, has a nonnegative limit. `ReadReduce.nonneg_of_slack` along any non-trivial
filter.

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
for every `ε > 0`. `ReadReduce.slack_of_nonneg` along any filter.

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

/-- **THE INPUT, on the periodic lattices.** At coupling `β`, aperture `2k + 1` and margin `γ`: for
every gauge-invariant half-space observable `x` and every slack `ε > 0`, the set of `j` with
`−ε ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · torusConn τ p hN β j x (circLag d)` belongs to
the ultrafilter `periodicUltra hN β` — a non-strict inequality, linear in the connected pairings of
`x` at lags `0, …, k + 1` in the periodic Wilson state of extent `2(j + 1)`.

Observable by observable it is exactly the periodic state's margin inequality (`torusSlack_iff`).
`torusReadsClearWith_of_atTop` derives it from the same inequality holding for all large `j`, which
does not mention the ultrafilter.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the sign of the slack. -/
def TorusReadsClearWith (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ) (γ : ℝ) : Prop :=
  ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
      -ε ≤ MassGap.ReadReduce.marginSum k γ (torusConn τ p hN β j x)

/-- **The input from every large periodic lattice.** If for every gauge-invariant half-space
observable `x` and every `ε > 0` the periodic margin sum is at least `−ε` for all large `j`, then
`TorusReadsClearWith τ p hN β k γ`: `periodicUltra hN β` is finer than `atTop`
(`PeriodicState.periodicUltra_le`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the sign of the slack. -/
theorem torusReadsClearWith_of_atTop (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ) (γ : ℝ)
    (h : ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in Filter.atTop,
        -ε ≤ MassGap.ReadReduce.marginSum k γ (torusConn τ p hN β j x)) :
    TorusReadsClearWith τ p hN β k γ :=
  fun x hx ε hε => (h x hx ε hε).filter_mono (periodicUltra_le hN β)

#print axioms torusReadsClearWith_of_atTop

/-- The periodic inequality without slack — `0 ≤` the periodic margin sum for all large `j`, at every
gauge-invariant half-space observable — gives `TorusReadsClearWith`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank and the sign of the sum. -/
theorem torusReadsClearWith_of_eventually (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ)
    (γ : ℝ)
    (h : ∀ x ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ᶠ j in Filter.atTop, 0 ≤ MassGap.ReadReduce.marginSum k γ (torusConn τ p hN β j x)) :
    TorusReadsClearWith τ p hN β k γ := by
  refine torusReadsClearWith_of_atTop τ p hN β k γ (fun x hx ε hε => ?_)
  filter_upwards [h x hx] with j hj
  linarith

#print axioms torusReadsClearWith_of_eventually

/-- **The slack form is the periodic state's margin inequality, observable by observable.** For any
continuous `x`: the periodic margin sums of `x` are at least `−ε` eventually along
`periodicUltra hN β`, for every `ε > 0`, exactly when
`0 ≤ marginSum k γ (c ↦ ν(θx · Sᶜx) − ν(θx)·ν(Sᶜx))`, `ν = periodicState hN β`. The periodic margin
sums converge to it along the ultrafilter (`tendsto_torusConn`, `ReadReduce.tendsto_marginSum`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the sign of the slack and of
the limit; `2` is the doubling of the reflection plane. -/
theorem torusSlack_iff (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ) (γ : ℝ)
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ j in ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
        -ε ≤ MassGap.ReadReduce.marginSum k γ (torusConn τ p hN β j x))
      ↔ 0 ≤ MassGap.ReadReduce.marginSum k γ (fun c =>
          periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
            - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
              * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)) := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  have hlim := MassGap.ReadReduce.tendsto_marginSum k γ (fun j => torusConn τ p hN β j x) _
    (tendsto_torusConn τ p hN β x)
  exact ⟨nonneg_of_slack_filter hlim, slack_of_nonneg_filter hlim⟩

#print axioms torusSlack_iff

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

/-- **W5 at the periodic state: the torus input gives the local condition.** Under
`TorusReadsClearWith τ p hN β k γ`, every `x` in the gauge-invariant algebra with
`D.form x D.vac = 0` (`D = periodicGaugeInvData τ p hN β`) has
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · D.form x (T^{circLag d} x)`.

`torusSlack_iff` turns the slack inequality at `x` into `0 ≤` the margin sum of the periodic state's
connected profile; `ν(θx) = D.form x D.vac = 0` (`periodic_form_vac`) and
`ν(θx · Sᶜx) = D.form x (Tᶜ x)` (`periodic_form_pow`) identify that profile with
`c ↦ D.form x (Tᶜ x)`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the orthogonality and the
sign of the sum. -/
theorem periodic_localReads_of_torusReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ)
    (γ : ℝ) (htorus : TorusReadsClearWith τ p hN β k γ)
    (x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (hx : (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac = 0) :
    0 ≤ MassGap.ReadReduce.marginSum k γ (fun c => (periodicGaugeInvData τ p hN β).form x
      (((periodicGaugeInvData τ p hN β).T ^ c) x)) := by
  have hθ : periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 :=
    (periodic_form_vac τ p hN β x).symm.trans hx
  have hprof : ∀ c : ℕ,
      periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
        - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
          * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c]
            (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
      = (periodicGaugeInvData τ p hN β).form x (((periodicGaugeInvData τ p hN β).T ^ c) x) := by
    intro c
    rw [hθ, zero_mul, sub_zero, periodic_form_pow τ p hN β x c]
  have hlim := (torusSlack_iff τ p hN β k γ
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))).mp (htorus x.1 x.2)
  exact le_of_le_of_eq hlim (MassGap.ReadReduce.marginSum_congr k γ hprof)

#print axioms periodic_localReads_of_torusReads

/-- **The converse of W5 at the periodic state: the local condition gives the torus input.** With
`D = periodicGaugeInvData τ p hN β`: if every `x` in the gauge-invariant algebra with
`D.form x D.vac = 0` has
`0 ≤ ∑_{d : Fin (2k + 2)} (cos (readAngle k d) − γ) · D.form x (T^{circLag d} x)`, then
`TorusReadsClearWith τ p hN β k γ`.

For an observable `x` of the algebra, `y = x − ν(θx)·1` is in the algebra and `D.form y D.vac = 0`
(`periodic_form_vac`, `θ1 = 1`, `ν 1 = 1`); its form profile `ν(θy · Sᶜy)` (`periodic_form_pow`) is
`ν(θx · Sᶜx) − ν(θx)·ν(Sᶜx)` (`Sᶜ1 = 1`, `GaugeInvariantAlgebra.iterate_shift_sub_smul_one`,
`state_centred_mul`), so the hypothesis at `y` is `0 ≤` the periodic state's margin sum of the
connected profile of `x`, which `torusSlack_iff` turns into the slack inequality.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the orthogonality and the
sign of the sum. -/
theorem periodic_torusReads_of_localReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ)
    (γ : ℝ)
    (hloc : ∀ x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (periodicGaugeInvData τ p hN β).form x (periodicGaugeInvData τ p hN β).vac = 0 →
        0 ≤ MassGap.ReadReduce.marginSum k γ (fun c => (periodicGaugeInvData τ p hN β).form x
          (((periodicGaugeInvData τ p hN β).T ^ c) x))) :
    TorusReadsClearWith τ p hN β k γ := by
  intro x hx
  refine (torusSlack_iff τ p hN β k γ x).mpr ?_
  have hθ1 : MassGap.LatticeReflection.ireflObs τ (2 * p)
      (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
    ext U; rfl
  have hθy : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
      = MassGap.LatticeReflection.ireflObs τ (2 * p) x
        - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
    rw [map_sub, map_smul, hθ1]
  have hy : x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
        • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    Submodule.sub_mem _ hx
      (Submodule.smul_mem _ _ (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p))
  obtain ⟨y, hyv⟩ : ∃ y : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (y : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = x - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
          • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :=
    ⟨⟨_, hy⟩, rfl⟩
  have hvac : (periodicGaugeInvData τ p hN β).form y (periodicGaugeInvData τ p hN β).vac = 0 := by
    rw [periodic_form_vac τ p hN β y, hyv, hθy, MassGap.DLRLimit.State.map_sub,
      MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one]
    ring
  have hprof : ∀ c : ℕ,
      (periodicGaugeInvData τ p hN β).form y (((periodicGaugeInvData τ p hN β).T ^ c) y)
        = periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x)
          - periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
            * periodicState hN β ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[c] x) := by
    intro c
    rw [periodic_form_pow τ p hN β y c, hyv, hθy,
      MassGap.GaugeInvariantAlgebra.iterate_shift_sub_smul_one τ c x
        (periodicState hN β (MassGap.LatticeReflection.ireflObs τ (2 * p) x))]
    exact state_centred_mul (periodicState hN β) _ _
  exact le_of_le_of_eq (hloc y hvac) (MassGap.ReadReduce.marginSum_congr k γ hprof)

#print axioms periodic_torusReads_of_localReads

/-- **The reads at the periodic state from the torus input.** At any real `β` and a margin
`γ > 3^{−1/4}`: `TorusReadsClearWith τ p hN β k γ` gives `SpectralGap.ReadsClear` for the
gauge-invariant GNS transfer operator at `periodicGaugeInvData τ p hN β`, aperture `2k + 1`. W5
(`periodic_localReads_of_torusReads`), then W4 (`ReadReduce.readsClearWith_of_local`), then W3
(`ReadReduce.readsClear_of_readsClearWith`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `3`, `1` and `4` spell the
floor `3^{−1/4}`. -/
theorem periodic_readsClear_of_torusReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (k : ℕ)
    {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ) (htorus : TorusReadsClearWith τ p hN β k γ) :
    MassGap.SpectralGap.ReadsClear (opT (periodicGaugeInvData τ p hN β))
      (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k :=
  MassGap.ReadReduce.readsClear_of_readsClearWith (opT (periodicGaugeInvData τ p hN β))
    (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k hγ
    (MassGap.ReadReduce.readsClearWith_of_local (periodicGaugeInvData τ p hN β) k γ
      (periodic_localReads_of_torusReads τ p hN β k γ htorus))

#print axioms periodic_readsClear_of_torusReads

/-- **The transfer gap at the periodic state from the torus input, at every `β ≥ 0`.** Under a
margin `γ > 3^{−1/4}` and `TorusReadsClearWith τ p hN β k γ`, the vacuum complement of the
gauge-invariant GNS space at `periodicGaugeInvData τ p hN β` is contracted: there is `ρ` with
`0 ≤ ρ < 1`, `ρ^{k+1} = 12(1 − 3^{−1/4})/8`, and `‖opTᵐ u‖ ≤ ρᵐ ‖u‖` for every `u` orthogonal to the
vacuum and every `m`. `PeriodicState.periodic_gap_of_reads` at
`periodic_readsClear_of_torusReads`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `β` and of
`ρ`, and the orthogonality; `1` is the upper bound on `ρ` and the `+ 1` of `k + 1`; `3`, `1` and `4`
spell the floor `3^{−1/4}`; `12` and `8` complete the cap `12(1 − 3^{−1/4})/8` of
`SpectralRead.lam0_pow_lt_of_tension`. -/
theorem periodic_gap_of_torusReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (htorus : TorusReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
        inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
          (periodicGaugeInvData τ p hN β).vac) u = 0 →
        ∀ m : ℕ, ‖((opT (periodicGaugeInvData τ p hN β)) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  periodic_gap_of_reads τ p hN hβ k (periodic_readsClear_of_torusReads τ p hN β k hγ htorus)

#print axioms periodic_gap_of_torusReads

/-- **The Clay spectral statement at the periodic state from the torus input, at every `β ≥ 0`.**
Under a margin `γ > 3^{−1/4}` and `TorusReadsClearWith τ p hN β k γ`: there is `ρ` with `0 < ρ < 1`
and `ρ^{k+1} = 12(1 − 3^{−1/4})/8` such that the gauge-invariant GNS transfer operator at
`periodicGaugeInvData τ p hN β` is self-adjoint, `0 < −log ρ`, its spectrum lies in
`{1} ∪ [0, exp(−(−log ρ))]`, and `1` is its greatest element.
`PeriodicState.periodic_clay_gap_of_reads` at `periodic_readsClear_of_torusReads`. The statement does
not assert a non-zero vacuum complement.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of `β`, of `ρ`
and of the spectrum, and the sign of the gap; `1` is the vacuum eigenvalue, the upper bound on `ρ`
and the `+ 1` of `k + 1`; `3`, `1` and `4` spell the floor `3^{−1/4}`; `12` and `8` complete the cap
`12(1 − 3^{−1/4})/8`. -/
theorem periodic_clay_gap_of_torusReads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (htorus : TorusReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      IsSelfAdjoint (opT (periodicGaugeInvData τ p hN β))
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT (periodicGaugeInvData τ p hN β))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT (periodicGaugeInvData τ p hN β))) 1 :=
  periodic_clay_gap_of_reads τ p hN hβ k (periodic_readsClear_of_torusReads τ p hN β k hγ htorus)

#print axioms periodic_clay_gap_of_torusReads

end Compose

end MassGap.PeriodicReduce
