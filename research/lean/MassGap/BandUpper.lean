import Mathlib
import MassGap.OneInput
import MassGap.FinalBridge

/-!
# MassGap.BandUpper — the upper half of the measured band along the coupling towers

The residual `hR` of `OneInput.clayStatement_of_strongEnd` asks, frequently near `0⁺`, that every coupling tower
`βs` at the window coupling `u₀` is a measured tower `MeasuredTower.MeasTowerG (SU N) βs` and carries
`ConstantPhysicsLine.ExistAlong N βs`. `MeasTowerG` is the band `c a_k ≤ m′(β_k) ≤ 2c a_k` with
`a_k = aRunG 1 / 2^{k+1}`, i.e. in window units (`ScaleLightCone.windowReading N βs k = 2^k m′(β_k)`) a pinch
`L ≤ 2^k m′ ≤ 2L` with `L = c · aRunG 1 / 2`. The lower half at `L = log 2` is proved
(`FinalBridge.windowReading_floor`). This module reads the upper half. Declarations are in the namespace
`MassGap.BandUpper`.

## 1. A mass is bounded above by a correlator that is seen (proved, any `G`)

* `measMassOfG_le_of_floor`: if along separations `z_j` with `‖z_j‖∞ → ∞` the connected correlation of a reading
  stays above `a e^{−M ‖z_j‖∞}` with `a > 0`, the measured mass (the supremum of the decay rates) is at most `M`.
  An upper bound on the mass is a lower bound on a correlation; nothing less gives it.
* `measMassOfG_le_of_logConvex`: the reflection-positivity template. An abstract read `g` (not tied to `stateK` here) with `g(0) > 0`, `g(m₁) > 0` and
  the log-convexity of `ApertureThing.stateK_far_ge` (`g(m₁)^m ≤ g(m)^{m₁} g(0)^{m−m₁}`, `m ≥ m₁`), dominated in
  absolute value by the correlation at a separation of sup-norm `2m`, gives
  `measMass ≤ log(g(0)/g(m₁)) / (2 m₁)`. One near read fixes every far read.

## 2. The band in window units (proved, `SU(N)`)

* `measTowerG_iff_window`: `MeasTowerG (SU N) βs` holds exactly when `βs → ∞` and some `L > 0` has, eventually,
  `m′(β_k)` finite and `L ≤ 2^k m′(β_k) ≤ 2L`. The factor `2` of the band is a ratio of the window reading's upper
  to its lower bound; it is built into `MeasuredTower.BandG`, which the frozen target `ClayStatementOf` reaches through `MeasTowerG`; it is not weakened here.
* `WindowUpper N βs U`: eventually `m′(β_k) ≤ U / 2^k`.
* `windowUpper_of_corrFloor`: the window upper bound from a correlation floor at the window rate at each step
  (`measMassOfG_le_of_floor` at `M = U/2^k`).
* `measTowerG_of_windowUpper`: near `0⁺`, every coupling tower with `WindowUpper N βs (2 log 2)` is a measured
  tower: the proved floor `log 2` and the upper bound `2 log 2` are the band at `L = log 2`.
* `clayStatement_of_strongEnd_upper`: `StrongEnd N` and, frequently near `0⁺`, `WindowUpper N βs (2 log 2)` and
  `ExistAlong N βs` along every tower give `ClayStatementOf (SU N)`. The lower half of the band is discharged.
  Vacuous: `ReflFloor.not_upper_residual` refutes the residual `WindowUpper N βs (2 log 2)` under `StrongEnd N`
  (the window reading of a tower grows like `log(1/u₀)`); the capstone is kept as the statement `ReflFloor`
  refutes. The lemmas of this module are unaffected.

## What does not follow, plainly

* The upper half is not proved. `WindowUpper` asks the tensor correlation of the periodic state at `β_k` to stay
  seen at the window scale `2^k` (`windowUpper_of_corrFloor`, `measMassOfG_le_of_logConvex`). Every proved fact at
  the window coupling `u₀ ≤ 1/1000` runs the other way: the basin gives the transfer gap
  (`CouplingTower.windowGap`) and so decay, a lower bound on the mass. No theorem found in the tree bounds a correlation
  of the infinite-volume periodic state below in terms of the window coupling `u₀`, which is a torus free-energy
  defect (`CouplingTower.windowCoupling`), and none found relates the reflected read `ApertureThing.gK` of the step
  states `stateK` to `FocusZoom.stateCov` of `periodicStateG`. Those two links are the obstruction. The
  ultralocal test `ApertureThing.inner_load_bearing` shows the contact read alone cannot replace them.
* A finite upper bound `2^k m′ ≤ U` with `U > 2 log 2` does not give `MeasTowerG` from the floor `log 2`: the
  band needs the window reading pinched within the ratio `2` (`measTowerG_iff_window`). A band with any finite
  ratio would need a different target; the target is frozen.
* `WindowUpper N βs (2 log 2)` is sufficient for the band, not equivalent: a tower in a band at `L > log 2` meets
  `MeasTowerG` without it. So `clayStatement_of_strongEnd_upper` is a capstone beside
  `OneInput.clayStatement_of_strongEnd`, not a rewriting of its residual.

The residual of `OneInput.clayStatement_of_strongEnd` is the bridge `StrongEnd N`, the ultraviolet input, and the
existence input `ExistAlong`. This module states the ultraviolet input as the one-sided `WindowUpper N βs (2 log 2)`
(the floor half is proved). The route at its sharpest is in PAPER §6.6 "The route at its sharpest".

DERIVED (module-wide): `0` the limit `0⁺`, the signs and the contact gap; `2` the band ratio of `MeasTowerG`, the
window base, the least rank of `SU(N)`, the two lattice steps of one reflected gap, and the base of `log 2`;
`1` the first halving of `dySpacingG` and the least gap index. Inherited, not derived here: `log 2` the window
rate of `CouplingTower.windowGap` through `FinalBridge.windowReading_floor`, so the upper constant `2 log 2` is the
band ratio times the inherited floor; `1/1000` the seed of `DoublingSharp`, inside `windowReading_floor` and
`OneInput.clayStatement_of_strongEnd` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.BandUpper

open Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG
open MassGap.DLRLimit (State)
open MassGap.MeasuredTower
open MassGap.MeasuredSpacing (mU measSpacing mUG_SU)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.ConstantPhysicsLine (ExistAlong)

/-! ## 1. A seen correlation bounds the mass above -/

section General

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A correlation floor bounds the measured mass above.** Along separations with `‖z_j‖∞ → ∞`, a connected
correlation above `a e^{−M ‖z_j‖∞}` with `a > 0` keeps every decay rate at most `M`. DERIVED: `0` the sign of
`a` and the limit of the exponential. -/
theorem measMassOfG_le_of_floor {ν : State (MassGap.GibbsSpec.IConf G)}
    {E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)} {M a : ℝ} (ha : 0 < a) (x : ISite) {z : ℕ → ISite}
    (hz : Tendsto (fun j => (snormG (z j) : ℝ)) atTop atTop)
    (hfl : ∀ᶠ j in atTop,
      a * Real.exp (-(M * snormG (z j))) ≤ |FocusZoom.stateCov ν (E x) (E (x + z j))|) :
    measMassOfG G ν E ≤ ENNReal.ofReal M := by
  unfold measMassOfG
  refine iSup₂_le fun m hm => ?_
  obtain ⟨C, hC⟩ := hm
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hlt0
  have hlt := not_le.mp hlt0
  have hd : 0 < (m : ℝ) - M := sub_pos.mpr hlt
  have ht : Tendsto (fun j => C * Real.exp (-(((m : ℝ) - M) * snormG (z j)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => ((m : ℝ) - M) * snormG (z j)) atTop atTop :=
      Tendsto.const_mul_atTop hd hz
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    rw [mul_zero] at h2
    exact h2
  obtain ⟨j, hj1, hj2⟩ := ((ht.eventually (gt_mem_nhds ha)).and hfl).exists
  have h3 := hC x (z j)
  set s : ℝ := (snormG (z j) : ℝ)
  have e : C * Real.exp (-(((m : ℝ) - M) * s)) * Real.exp (-(M * s)) = C * Real.exp (-((m : ℝ) * s)) := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  have hpos := Real.exp_pos (-(M * s))
  have h4 : a * Real.exp (-(M * s)) ≤ C * Real.exp (-(((m : ℝ) - M) * s)) * Real.exp (-(M * s)) := by
    rw [e]
    exact le_trans hj2 h3
  have h5 := le_of_mul_le_mul_right h4 hpos
  linarith

/-- **The reflection-positivity template.** A read `g` with `g(0) > 0`, `g(m₁) > 0` (`m₁ ≥ 1`) and the
log-convexity `g(m₁)^m ≤ g(m)^{m₁} g(0)^{m−m₁}` of `ApertureThing.stateK_far_ge`, dominated by the correlation at a
separation of sup-norm `2m`, bounds the measured mass by `log(g(0)/g(m₁)) / (2 m₁)`. DERIVED: `2` the two lattice
steps of one reflected gap; `1` the least gap index; `0` the contact gap. -/
theorem measMassOfG_le_of_logConvex {ν : State (MassGap.GibbsSpec.IConf G)}
    {E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)} (x : ISite) {z : ℕ → ISite}
    (hz : ∀ m, snormG (z m) = 2 * m) {g : ℕ → ℝ} {m₁ : ℕ} (hm₁ : 1 ≤ m₁) (hg0 : 0 < g 0)
    (hg1 : 0 < g m₁) (hlc : ∀ m, m₁ ≤ m → g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁))
    (hread : ∀ m, |g m| ≤ |FocusZoom.stateCov ν (E x) (E (x + z m))|) :
    measMassOfG G ν E ≤ ENNReal.ofReal (Real.log (g 0 / g m₁) / (2 * m₁)) := by
  set M := Real.log (g 0 / g m₁) / (2 * m₁) with hM
  have hm1r : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  have hzt : Tendsto (fun j => (snormG (z j) : ℝ)) atTop atTop := by
    simp only [hz]
    push_cast
    exact Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop
  refine measMassOfG_le_of_floor hg0 x hzt ?_
  filter_upwards [eventually_ge_atTop m₁] with m hm
  refine le_trans ?_ (hread m)
  have hP : 0 < g m₁ ^ m := pow_pos hg1 m
  have hR := lt_of_lt_of_le hP (hlc m hm)
  have hgm : g m ^ m₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hR
    exact lt_irrefl _ hR
  have hgm0 : g m ≠ 0 := fun h0 => hgm (by rw [h0, zero_pow (by omega)])
  have hg0p : g 0 ^ (m - m₁) ≠ 0 := (pow_pos hg0 _).ne'
  have hlog := Real.log_le_log hP (hlc m hm)
  rw [Real.log_mul hgm hg0p, Real.log_pow, Real.log_pow, Real.log_pow, Nat.cast_sub hm] at hlog
  have hkey : Real.log (g 0) - M * (snormG (z m) : ℝ) ≤ Real.log (g m) := by
    rw [hz m, hM, Real.log_div hg0.ne' hg1.ne']
    push_cast
    have e : (Real.log (g 0) - Real.log (g m₁)) / (2 * m₁) * (2 * m)
        = (m : ℝ) / m₁ * (Real.log (g 0) - Real.log (g m₁)) := by
      field_simp
    rw [e]
    have h2 : (m₁ : ℝ) * (Real.log (g 0) - (m : ℝ) / m₁ * (Real.log (g 0) - Real.log (g m₁)))
        ≤ (m₁ : ℝ) * Real.log (g m) := by
      have e2 : (m₁ : ℝ) * (Real.log (g 0) - (m : ℝ) / m₁ * (Real.log (g 0) - Real.log (g m₁)))
          = (m : ℝ) * Real.log (g m₁) - ((m : ℝ) - m₁) * Real.log (g 0) := by
        field_simp
        ring
      rw [e2]
      linarith
    exact le_of_mul_le_mul_left h2 hm1r
  calc g 0 * Real.exp (-(M * (snormG (z m) : ℝ)))
      = Real.exp (Real.log (g 0) - M * (snormG (z m) : ℝ)) := by
        rw [Real.exp_sub, Real.exp_log hg0, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (Real.log (g m)) := Real.exp_le_exp.mpr hkey
    _ = |g m| := by rw [← Real.log_abs, Real.exp_log (abs_pos.mpr hgm0)]

end General

/-! ## 2. The band in window units along the towers -/

section Tower

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The measured tower is the window pinch of ratio `2`.** `MeasTowerG (SU N) βs` holds exactly when `βs → ∞`
and some `L > 0` has, eventually, `m′(β_k)` finite and `L ≤ 2^k m′(β_k) ≤ 2L`. DERIVED: `2` the band ratio and the
window base; `1` the first halving of `dySpacingG`; `0` the sign. -/
theorem measTowerG_iff_window (βs : ℕ → ℝ) :
    MeasTowerG (MassGap.SUN.SU N) βs ↔ Tendsto βs atTop atTop ∧ ∃ L : ℝ, 0 < L ∧ ∀ᶠ k in atTop,
      mU (NeZero.ne N) (βs k) ≠ ⊤ ∧ L ≤ ScaleLightCone.windowReading N βs k ∧
        ScaleLightCone.windowReading N βs k ≤ 2 * L := by
  set A := GaugeRunning.aRunG (MassGap.SUN.SU N) 1 with hA
  have hA0 : 0 < A := aRunG_pos (MassGap.SUN.SU N) one_pos
  have hd : ∀ k : ℕ, dySpacingG (MassGap.SUN.SU N) k = A / 2 ^ (k + 1) := fun _ => rfl
  constructor
  · rintro ⟨hβ, c, hc, hb⟩
    refine ⟨hβ, c * A / 2, by positivity, ?_⟩
    filter_upwards [hb] with k hk
    have hne : mU (NeZero.ne N) (βs k) ≠ ⊤ := by rw [← mUG_SU]; exact hk.ne_top
    obtain ⟨h1, h2⟩ := hk.spacing hc
    have es : measSpacingG (MassGap.SUN.SU N) (βs k) = measSpacing (NeZero.ne N) (βs k) := by
      unfold measSpacingG measSpacing; rw [mUG_SU]
    rw [es, hd] at h1 h2
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have e1 : c * (A / 2 ^ (k + 1)) = c * A / 2 / 2 ^ k := by rw [pow_succ]; field_simp
    have e2 : 2 * c * (A / 2 ^ (k + 1)) = 2 * (c * A / 2) / 2 ^ k := by rw [pow_succ]; field_simp
    rw [e1, div_le_iff₀ hp] at h1
    rw [e2, le_div_iff₀ hp] at h2
    unfold ScaleLightCone.windowReading
    exact ⟨hne, by linarith, by linarith⟩
  · rintro ⟨hβ, L, hL, hb⟩
    refine ⟨hβ, 2 * L / A, by positivity, ?_⟩
    filter_upwards [hb] with k ⟨hne, hlo, hhi⟩
    have e : mUG (MassGap.SUN.SU N) (βs k) = ENNReal.ofReal (measSpacing (NeZero.ne N) (βs k)) := by
      rw [mUG_SU]; exact (ENNReal.ofReal_toReal hne).symm
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have e1 : 2 * L / A * (A / 2 ^ (k + 1)) = L / 2 ^ k := by rw [pow_succ]; field_simp
    have e2 : 2 * (2 * L / A) * (A / 2 ^ (k + 1)) = 2 * L / 2 ^ k := by rw [pow_succ]; field_simp
    unfold ScaleLightCone.windowReading at hlo hhi
    refine ⟨?_, ?_⟩
    · rw [e, hd, e1]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hp]
      linarith
    · rw [e, hd, e2]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hp]
      linarith

variable (N) in
/-- **The window upper bound at level `U`**: eventually `m′(β_k) ≤ U / 2^k`, i.e. `2^k m′(β_k) ≤ U` with the mass
finite. DERIVED: `2` the window base. -/
def WindowUpper (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≤ ENNReal.ofReal (U / 2 ^ k)

/-- **The window upper bound from a correlation seen at the window rate.** If at each step (eventually) the tensor
correlation of the periodic state at `β_k` stays above `a e^{−(U/2^k)‖z_j‖∞}` along separations with
`‖z_j‖∞ → ∞`, then `WindowUpper N βs U`. DERIVED: `2` the window base; `0` the sign. -/
theorem windowUpper_of_corrFloor {βs : ℕ → ℝ} {U : ℝ}
    (h : ∀ᶠ k in atTop, ∃ a : ℝ, 0 < a ∧ ∃ (x : ISite) (z : ℕ → ISite),
      Tendsto (fun j => (snormG (z j) : ℝ)) atTop atTop ∧ ∀ᶠ j in atTop,
        a * Real.exp (-(U / 2 ^ k * snormG (z j))) ≤
          |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
            (tensorEnergyG (MassGap.SUN.SU N) x) (tensorEnergyG (MassGap.SUN.SU N) (x + z j))|) :
    WindowUpper N βs U := by
  filter_upwards [h] with k ⟨a, ha, x, z, hz, hfl⟩
  rw [← mUG_SU]
  exact measMassOfG_le_of_floor ha x hz hfl

/-- **Near `0⁺` the window upper bound at `2 log 2` makes a coupling tower a measured tower**: the proved floor
`log 2 ≤ 2^k m′` (`FinalBridge.windowReading_floor`) and `2^k m′ ≤ 2 log 2` are the band at `L = log 2`
(`measTowerG_iff_window`). DERIVED: `0` the limit `0⁺`; `2` the band ratio and the least rank; `1` the base of
`log 2 > 0`. Inherited: `log 2` the window rate. -/
theorem measTowerG_of_windowUpper :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      WindowUpper N βs (2 * Real.log 2) → MeasTowerG (MassGap.SUN.SU N) βs := by
  filter_upwards [FinalBridge.windowReading_floor (N := N) (Fact.out : 2 ≤ N)] with u hu βs hT hU
  have hfin : ∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ∞ :=
    hU.mono fun _ hk => ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
  have hfl := hu βs hT hfin
  refine (measTowerG_iff_window βs).mpr ⟨hT.1, Real.log 2, Real.log_pos one_lt_two, ?_⟩
  filter_upwards [hU, hfin, hfl] with k hk hne hlo
  refine ⟨hne, hlo, ?_⟩
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h0 : 0 ≤ 2 * Real.log 2 / 2 ^ k := div_nonneg (by positivity) hp.le
  have h1 := ENNReal.toReal_le_of_le_ofReal h0 hk
  unfold ScaleLightCone.windowReading
  unfold measSpacing
  rw [le_div_iff₀ hp] at h1
  linarith

/-- **The root at `SU(N)` with the lower half of the band discharged.** `StrongEnd N` and, at window couplings
arbitrarily close to `0⁺`, the window upper bound `WindowUpper N βs (2 log 2)` and `ExistAlong N βs` along every
coupling tower there give `ClayStatementOf (SU N)` (`OneInput.clayStatement_of_strongEnd` with
`measTowerG_of_windowUpper`). DERIVED: `0` the limit `0⁺`; `2` the band ratio and the least rank. Inherited:
`log 2` the window rate. Vacuous: `ReflFloor.not_upper_residual` refutes the residual under `StrongEnd N`; use
`OneInput.clayStatement_of_strongEnd`. -/
theorem clayStatement_of_strongEnd_upper (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      WindowUpper N βs (2 * Real.log 2) ∧ ExistAlong N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  OneInput.clayStatement_of_strongEnd hS
    ((hR.and_eventually (measTowerG_of_windowUpper (N := N))).mono fun _ h βs hT =>
      ⟨h.2 βs hT (h.1 βs hT).1, (h.1 βs hT).2⟩)

end Tower

end MassGap.BandUpper

end

#print axioms MassGap.BandUpper.measMassOfG_le_of_floor
#print axioms MassGap.BandUpper.measMassOfG_le_of_logConvex
#print axioms MassGap.BandUpper.measTowerG_iff_window
#print axioms MassGap.BandUpper.windowUpper_of_corrFloor
#print axioms MassGap.BandUpper.measTowerG_of_windowUpper
#print axioms MassGap.BandUpper.clayStatement_of_strongEnd_upper
