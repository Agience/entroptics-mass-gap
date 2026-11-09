import Mathlib
import MassGap.StepPeriodic
import MassGap.ObserverFlowSeed

/-!
# MassGap.BandClose — the reflected read of the tensor reading, split into its diagonal part and a defect

`StepPeriodic.windowUpper_of_reads` reduces `BandUpper.WindowUpper` to two links: a domination (1′) of the
centred reflected covariance `stateCov ν (θX) (T_{2m e₀} X)` by the diagonal tensor covariance, and a floor
(link 2) on one reflected read at the window scale. This module reads both at `X = tensorEnergyG 0`.
Declarations are in the namespace `MassGap.BandClose`.

## 1. The geometry of the mirror on the tensor reading (proved)

* `ireflObs_plaqFieldG`: the reflection carries a plaquette density to the density of the reflected
  plaquette (`LatticeReflection.ihol_ireflConf`, a class function kills the conjugation).
* `plaqFieldG_swap`: the transposed plane reads the same density (the reversed loop is the inverse
  holonomy; `GaugeGroup.wilsonDensityG_inv`).
* `transObs_plaqFieldG`, `transObs_tensorEnergyG`: translation moves the base.
* `ireflObs_tensorEnergyG_zero`: `θ(E 0) = P₀₁(−e₀) − P₂₃(0)`, with `E = tensorEnergyG`. The `(0,1)`-plaquette
  extends along the mirror axis and lands one step below; the `(2,3)`-plaquette lies in the mirror and stays.
* `ireflObs_tensorEnergyG_split`: `θ(E 0) = E 0 + Δ` with `Δ = P₀₁(−e₀) − P₀₁(0)`, the time difference of the
  time-extended density across the mirror.
* `not_translate_combination`: no finitely supported combination of translates of `E` is carried by `θ` into
  the span of translates of `E` coefficientwise. The proof is on the coefficient level: the `(0,1)`- and
  `(2,3)`-weights would have to agree after shifts differing by `e₀`, which forces every weight along a time line
  to be equal, hence zero for finite support. So, with the linear independence of the plaquette densities as functions
  (`PlaqIndep.plaqFamily_linearIndependent`, and at the function level `PlaqIndep.not_reflection_symmetric`), option (a) of a reflection-symmetric reading in the span of translates of `E`
  does not exist, and `measMassOfG` is pinned to the one reading `E` (it is a supremum over decay rates of `E`,
  not over a class of readings). The statement is the combinatorial core; linear independence of the
  plaquette densities as functions is not formalised.

## 2. The split of the reflected read (proved)

* `reflRead_split`: for `g = gP β (connP β (E 0))`,
  `g m = stateCov ν (E 0) (E (0 + (2m)e₀)) + R m` with `R m = stateCov ν Δ (E ((2m)e₀))`.

## 3. The template with a comparable read (proved)

* `logConvex_floor`: the one-near-read floor `g(0) e^{−M·2m} ≤ |g m|` (`m ≥ m₁`) of log-convexity.
* `measMassOfG_le_of_logConvex_cmp`: `BandUpper.measMassOfG_le_of_logConvex` with the domination
  `|g m| ≤ |diag m|` for every `m` weakened to comparability: some `a > 0` with `a |g m| ≤ |diag m|`
  eventually. The prefactor of a correlation floor does not enter the mass.
* `windowUpper_of_tensorReads`: `WindowUpper N βs U` from, eventually in `k`, `g(0) > 0`, the window floor
  (link 2) and comparability (1″) of the reflected read of `E 0` with the diagonal read.
* `windowUpper_of_defect`: the same with (1″) replaced by the defect bound: some `c < 1` with
  `|R m| ≤ c |g m|` eventually. This is the exact form of the remaining mixed-to-diagonal inequality.
* `clayStatement_of_strongEnd_reads`: `StrongEnd N` and, frequently near `0⁺`, along every tower the reads
  `ReflReadsAt N βs (2 log 2)` (positive contact, window floor, defect bound) and `ExistAlong N βs` give
  `ClayStatementOf (SU N)`. Vacuous: `windowUpper_of_defect` turns the residual into `BandUpper.WindowUpper` at
  the fixed level `2 log 2`, which `ReflFloor.not_upper_residual` refutes under `StrongEnd N`. The lemmas of
  this module are unaffected.

## What does not follow, plainly

* (1′) does not close structurally. The mass is read through the one reading `E`; no reflection-symmetric
  reading in the span of translates of `E` exists (`not_translate_combination`); Cauchy–Schwarz in the
  reflection-positive form bounds a mixed read above by diagonal reflected reads, never below, so it runs the
  wrong way for a floor. (1′) is reduced to the defect bound below; it is not discharged. What is proved is the exact split `g = diag + R`; the remaining inequality is
  `∃ c < 1, ∀ᶠ m, |stateCov ν Δ (E((2m)e₀))| ≤ c · |g m|`, the defect `Δ = P₀₁(−e₀) − P₀₁(0)` read against the
  far tensor density, relative to the reflected read itself. By translation invariance `R m` is the discrete
  time difference `C(2m+1) − C(2m)` of `C(n) = stateCov ν (P₀₁ 0) (E(n e₀))`; no theorem found in the tree bounds it.
* Link 2 does not close. The tower is defined by the finite-torus free-energy defect
  `CouplingTower.windowCoupling N β w = defectW N β (2^w)`, whose `β`-derivative is a difference of torus mean
  actions (`ReadSaturates.hasDerivAt_freeI_XY`). The floor needs a reflected two-point read of the
  infinite-volume `periodicStateG (SU N) β_k` at gap `2m₁`. No theorem found in the tree relates torus mean actions
  at side `2^w` to a two-point covariance of the periodic state, so the exact remaining inequality is, eventually
  in `k`, with `g_k = gP β_k (connP β_k (E 0))`: `0 < g_k 0` and some `m₁ ≥ 1` with
  `g_k 0 · e^{−2 m₁ · 2 log 2 / 2^k} ≤ g_k m₁`. The positivity `0 < g_k 0` is proved in `ReadPos.gE_zero_pos`;
  the window floor is what remains (`ReadPos.ReflFloorAt`).
* So `MeasTowerG` along every tower near `0⁺` is not proved and `clayStatement_of_strongEnd_exist`
  (StrongEnd and ExistAlong only) is not built. The count stays three: `StrongEnd N`, `ExistAlong`, and the upper
  half, now in the form `ReflReadsAt N βs (2 log 2)`.

DERIVED (module-wide): `0` the plane, the time axis, the origin, the contact gap and the signs; `1` the unit step,
the least gap index and the swap of the two plane directions; `2` the two steps of one reflected gap, the window
base and the band ratio; `3` the last plane direction of the tensor reading. Inherited, not derived here: `log 2`
the window rate of `CouplingTower.windowGap` through `BandUpper.measTowerG_of_windowUpper`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.BandClose

open Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.JointRP
  MassGap.ApertureThing MassGap.ClayTreeG
open MassGap.MeasuredTower
open MassGap.MeasuredSpacing (mU mUG_SU)
open MassGap.StepPeriodic (gP connP gP_conn)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.ConstantPhysicsLine (ExistAlong)

variable {N : ℕ} [NeZero N]

/-! ## 1. The mirror on the tensor reading -/

/-- **The reflection moves a plaquette density to the reflected plaquette.** DERIVED: `4` the dimension. -/
theorem ireflObs_plaqFieldG (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq) :
    LatticeReflection.ireflObs τ c (plaqFieldG (G := MassGap.SUN.SU N) q).1
      = (plaqFieldG (G := MassGap.SUN.SU N) (LatticeReflection.ireflPlaq τ c q)).1 := by
  ext U
  obtain ⟨g, hg⟩ := LatticeReflection.ihol_ireflConf τ c q U
  show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q (LatticeReflection.ireflConf τ c U))
    = GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol (LatticeReflection.ireflPlaq τ c q) U)
  unfold MassGap.GibbsSpec.ihol
  rw [GaugeWilson.ibd_gibbs_eq_infinite, hg]
  exact GaugeGroup.wilsonDensityG_conj g _

/-- **The transposed plane reads the same density**: the reversed loop is the inverse holonomy.
DERIVED: `1`, `2` the two plane directions. -/
theorem plaqFieldG_swap (μ ν : Fin 4) (x : ISite) :
    (plaqFieldG (G := MassGap.SUN.SU N) ((ν, μ), x)).1 = (plaqFieldG (G := MassGap.SUN.SU N) ((μ, ν), x)).1 := by
  ext U
  show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol ((ν, μ), x) U)
    = GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol ((μ, ν), x) U)
  have e : MassGap.GibbsSpec.ihol ((ν, μ), x) U = (MassGap.GibbsSpec.ihol ((μ, ν), x) U)⁻¹ := by
    unfold MassGap.GibbsSpec.ihol
    rw [GaugeWilson.ibd_gibbs_eq_infinite, wilsonHol_ibd, wilsonHol_ibd]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e, GaugeGroup.wilsonDensityG_inv]

/-- **Translation moves the base of a plaquette density.** DERIVED: no numeral. -/
theorem transObs_plaqFieldG (p : Fin 4 × Fin 4) (y x : ISite) :
    transObs x (plaqFieldG (G := MassGap.SUN.SU N) (p, y)).1 = (plaqFieldG (G := MassGap.SUN.SU N) (p, y + x)).1 := by
  ext U
  show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol (p, y) (transConf x U))
    = GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol (p, y + x) U)
  rw [MassGap.ObserverFlowSeed.ihol_transConf]

/-- **Translation moves the tensor reading.** DERIVED: no numeral. -/
theorem transObs_tensorEnergyG (y x : ISite) :
    transObs x (tensorEnergyG (MassGap.SUN.SU N) y) = tensorEnergyG (MassGap.SUN.SU N) (y + x) := by
  unfold tensorEnergyG
  rw [map_sub, transObs_plaqFieldG, transObs_plaqFieldG]

/-- The mirror about `x₀ = 0` sends the origin, reflected about `−1`, to `−e₀`. DERIVED: `0` the plane and
the axis; `1` the link length. -/
theorem ireflSite_zero_sub_one : LatticeReflection.ireflSite 0 (0 - 1) (0 : ISite) = -eT := by
  funext i
  fin_cases i <;> simp [LatticeReflection.ireflSite, eT]

/-- The mirror about `x₀ = 0` fixes the origin. DERIVED: `0` the plane, the axis and the origin. -/
theorem ireflSite_zero_zero : LatticeReflection.ireflSite 0 0 (0 : ISite) = 0 := by
  funext i
  fin_cases i <;> simp [LatticeReflection.ireflSite]

/-- **The mirror on the tensor reading at the origin**: `θ(E 0) = P₀₁(−e₀) − P₂₃(0)`. The `(0,1)`-plaquette
extends along the axis and lands one step below; the `(2,3)`-plaquette lies in the mirror. DERIVED: `0`, `1`,
`2`, `3` the two planes; `0` the plane of the mirror. -/
theorem ireflObs_tensorEnergyG_zero :
    LatticeReflection.ireflObs 0 0 (tensorEnergyG (MassGap.SUN.SU N) 0)
      = (plaqFieldG (G := MassGap.SUN.SU N) (((0 : Fin 4), (1 : Fin 4)), -eT)).1
        - (plaqFieldG (G := MassGap.SUN.SU N) (((2 : Fin 4), (3 : Fin 4)), 0)).1 := by
  unfold tensorEnergyG
  rw [map_sub, ireflObs_plaqFieldG, ireflObs_plaqFieldG]
  have h1 : LatticeReflection.ireflPlaq 0 0 (((0 : Fin 4), (1 : Fin 4)), (0 : ISite))
      = (((1 : Fin 4), (0 : Fin 4)), -eT) := by
    simp only [LatticeReflection.ireflPlaq, if_true]
    rw [ireflSite_zero_sub_one]
  have h2 : LatticeReflection.ireflPlaq 0 0 (((2 : Fin 4), (3 : Fin 4)), (0 : ISite))
      = (((2 : Fin 4), (3 : Fin 4)), (0 : ISite)) := by
    simp only [LatticeReflection.ireflPlaq]
    rw [if_neg (by decide), if_neg (by decide), ireflSite_zero_zero]
  rw [h1, h2, plaqFieldG_swap (N := N) 0 1 (-eT)]

/-- **The mirror defect**: the time difference `P₀₁(−e₀) − P₀₁(0)` of the time-extended density across the
mirror. DERIVED: `0`, `1` the plane; `0` the origin. -/
def mirrorDefect : C(Cfg N, ℝ) :=
  (plaqFieldG (G := MassGap.SUN.SU N) (((0 : Fin 4), (1 : Fin 4)), -eT)).1
    - (plaqFieldG (G := MassGap.SUN.SU N) (((0 : Fin 4), (1 : Fin 4)), 0)).1

/-- **`θ(E 0) = E 0 + Δ`.** DERIVED: `0` the origin and the plane. -/
theorem ireflObs_tensorEnergyG_split :
    LatticeReflection.ireflObs 0 0 (tensorEnergyG (MassGap.SUN.SU N) 0)
      = tensorEnergyG (MassGap.SUN.SU N) 0 + mirrorDefect (N := N) := by
  rw [ireflObs_tensorEnergyG_zero]
  unfold tensorEnergyG mirrorDefect
  abel

/-- **No reflection-symmetric reading in the span of translates of `E`** (coefficient level). The mirror `ρ`
sends `P₀₁(a)` to `P₀₁(ρa − e₀)` and `P₂₃(a)` to `P₂₃(ρa)`. If the image of `Σ_a w_a E(a)` were `Σ_b v_b E(b)`,
the `(0,1)` part would force `v_b = w(ρ(b + e₀))` and the `(2,3)` part `v_b = w(ρb)`; with `c = ρb` this is
`w(c − e₀) = w(c)` at every base. This theorem shows that relation with finite support forces `w = 0`.
DERIVED: `0` the time axis; `1` the unit step. -/
theorem not_translate_combination (w : ISite → ℝ) (hfin : (Function.support w).Finite)
    (hshift : ∀ c : ISite, w (c - eT) = w c) : w = 0 := by
  funext c
  by_contra hne
  have hmem : ∀ n : ℕ, c - n • eT ∈ Function.support w := by
    intro n
    induction n with
    | zero => simpa using hne
    | succ n ih =>
      have e : c - (n + 1) • eT = (c - n • eT) - eT := by rw [add_smul, one_smul]; abel
      rw [Function.mem_support, e, hshift]
      exact ih
  have hinj : Function.Injective fun n : ℕ => c - n • eT := by
    intro n n' h
    have h0 := congrFun h 0
    simp [eT] at h0
    exact_mod_cast h0
  exact (Set.infinite_of_injective_forall_mem hinj hmem) hfin

/-! ## 2. The split of the reflected read -/

/-- A covariance is additive in its first argument. DERIVED: no numeral. -/
theorem stateCov_add_left {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : DLRLimit.State X)
    (f₁ f₂ g : C(X, ℝ)) :
    FocusZoom.stateCov ν (f₁ + f₂) g = FocusZoom.stateCov ν f₁ g + FocusZoom.stateCov ν f₂ g := by
  unfold FocusZoom.stateCov
  rw [add_mul, ν.map_add, ν.map_add]
  ring

/-- **The reflected read of `E 0` is the diagonal tensor covariance plus the defect read**:
`gP β (connP β (E 0)) m = stateCov ν (E 0) (E (0 + (2m) e₀)) + stateCov ν Δ (E ((2m) e₀))`.
DERIVED: `2` the two steps of one gap; `0` the origin. -/
theorem reflRead_split (β : ℝ) (m : ℕ) :
    gP β (connP β (tensorEnergyG (MassGap.SUN.SU N) 0)) m
      = FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
          (tensorEnergyG (MassGap.SUN.SU N) 0) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))
        + FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
          (mirrorDefect (N := N)) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT)) := by
  rw [gP_conn, ireflObs_tensorEnergyG_split, transObs_tensorEnergyG, stateCov_add_left]

/-- The sup-norm of `(2m) e₀` is `2m`. DERIVED: `2` the two steps; `0` the axis. -/
theorem snormG_eT (m : ℕ) : snormG ((2 * m) • eT) = 2 * m := by
  unfold snormG
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    fin_cases i <;> simp [eT, Int.natAbs_mul]
  · exact Finset.le_sup_of_le (Finset.mem_univ 0) (by simp [eT, Int.natAbs_mul])

/-! ## 3. The template with a comparable read -/

section General

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **One near read fixes every far read**: with log-convexity, `g(0) e^{−M·2m} ≤ |g m|` for `m ≥ m₁`,
`M = log(g(0)/g(m₁))/(2m₁)`. DERIVED: `2` the two steps of one gap; `1` the least gap index; `0` the contact
gap. -/
theorem logConvex_floor {g : ℕ → ℝ} {m₁ : ℕ} (hm₁ : 1 ≤ m₁) (hg0 : 0 < g 0) (hg1 : 0 < g m₁)
    (hlc : ∀ m, m₁ ≤ m → g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁)) {m : ℕ} (hm : m₁ ≤ m) :
    g 0 * Real.exp (-(Real.log (g 0 / g m₁) / (2 * m₁) * (2 * m : ℕ))) ≤ |g m| := by
  set M := Real.log (g 0 / g m₁) / (2 * m₁) with hM
  have hm1r : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
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
  have hkey : Real.log (g 0) - M * ((2 * m : ℕ) : ℝ) ≤ Real.log (g m) := by
    rw [hM, Real.log_div hg0.ne' hg1.ne']
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
  calc g 0 * Real.exp (-(M * ((2 * m : ℕ) : ℝ)))
      = Real.exp (Real.log (g 0) - M * ((2 * m : ℕ) : ℝ)) := by
        rw [Real.exp_sub, Real.exp_log hg0, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (Real.log (g m)) := Real.exp_le_exp.mpr hkey
    _ = |g m| := by rw [← Real.log_abs, Real.exp_log (abs_pos.mpr hgm0)]

/-- **The reflection-positivity template with a comparable read.** As
`BandUpper.measMassOfG_le_of_logConvex`, with the domination `|g m| ≤ |diag m|` at every `m` weakened to:
some `a > 0` has `a |g m| ≤ |diag m|` eventually. DERIVED: `2` the two steps of one gap; `1` the least gap
index; `0` the contact gap and the sign of `a`. -/
theorem measMassOfG_le_of_logConvex_cmp {ν : DLRLimit.State (MassGap.GibbsSpec.IConf G)}
    {E : ISite → C(MassGap.GibbsSpec.IConf G, ℝ)} (x : ISite) {z : ℕ → ISite}
    (hz : ∀ m, snormG (z m) = 2 * m) {g : ℕ → ℝ} {m₁ : ℕ} (hm₁ : 1 ≤ m₁) (hg0 : 0 < g 0)
    (hg1 : 0 < g m₁) (hlc : ∀ m, m₁ ≤ m → g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁))
    (hcmp : ∃ a : ℝ, 0 < a ∧ ∀ᶠ m in atTop,
      a * |g m| ≤ |FocusZoom.stateCov ν (E x) (E (x + z m))|) :
    measMassOfG G ν E ≤ ENNReal.ofReal (Real.log (g 0 / g m₁) / (2 * m₁)) := by
  obtain ⟨a, ha, hcm⟩ := hcmp
  have hzt : Tendsto (fun j => (snormG (z j) : ℝ)) atTop atTop := by
    simp only [hz]
    push_cast
    exact Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop
  refine BandUpper.measMassOfG_le_of_floor (mul_pos ha hg0) x hzt ?_
  filter_upwards [eventually_ge_atTop m₁, hcm] with m hm hc
  have hf := logConvex_floor hm₁ hg0 hg1 hlc hm
  rw [hz m]
  calc a * g 0 * Real.exp (-(Real.log (g 0 / g m₁) / (2 * m₁) * ((2 * m : ℕ) : ℝ)))
      = a * (g 0 * Real.exp (-(Real.log (g 0 / g m₁) / (2 * m₁) * ((2 * m : ℕ) : ℝ)))) := by ring
    _ ≤ a * |g m| := mul_le_mul_of_nonneg_left hf ha.le
    _ ≤ _ := hc

end General

/-! ## 4. The window upper bound from the reads of `E 0` -/

/-- **The reflected read of the tensor reading at the origin**, at `β`. DERIVED: `0` the origin. -/
abbrev gE (β : ℝ) : ℕ → ℝ := gP (N := N) β (connP β (tensorEnergyG (MassGap.SUN.SU N) 0))

/-- The tensor reading at the origin is a positive half-space observable: both plaquettes are based at time
`0`. DERIVED: `0` the plane and the origin. -/
theorem tensorEnergyG_zero_mem :
    tensorEnergyG (MassGap.SUN.SU N) 0 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  have hq : ∀ q : MassGap.GibbsSpec.IPlaq, q.2 = 0 →
      (plaqFieldG (G := MassGap.SUN.SU N) q).1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
    intro q h0
    refine HalfSpaceAlgebra.mem_halfSpaceAlg.mpr ⟨(MassGap.GibbsSpec.ilinks q).toFinset, ?_, ?_⟩
    · intro l hl
      exact GaugeInvariantAlgebra.ilinks_mem_posHalf_of_le q (by rw [h0]; rfl)
        l (List.mem_toFinset.mp (Finset.mem_coe.mp hl))
    · intro U V h
      show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q U)
        = GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q V)
      rw [MassGap.GibbsSpec.ihol_congr q U V (fun l hl => h l (List.mem_toFinset.mpr hl))]
  unfold tensorEnergyG
  exact Submodule.sub_mem _ (hq _ rfl) (hq _ rfl)

/-- **The window upper bound from the reflected reads of `E 0`.** Along a tower `βs`, if eventually in `k`
the reflected read `g = gE (βs k)` has `g(0) > 0`, a window floor `g(0) e^{−2 m₁ U/2^k} ≤ g(m₁)` (link 2)
and is comparable to the diagonal tensor read (1″), then `WindowUpper N βs U`. DERIVED: `2` the two steps of
one gap and the window base; `1` the least gap index; `0` the origin, the contact gap and the signs. -/
theorem windowUpper_of_tensorReads [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ}
    (h : ∀ᶠ k in atTop, 0 < gE (N := N) (βs k) 0 ∧ (∃ m₁ : ℕ, 1 ≤ m₁ ∧
      gE (N := N) (βs k) 0 * Real.exp (-(2 * m₁ * (U / 2 ^ k))) ≤ gE (N := N) (βs k) m₁) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ m in atTop, a * |gE (N := N) (βs k) m| ≤
        |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k))
          (tensorEnergyG (MassGap.SUN.SU N) 0) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))|) :
    BandUpper.WindowUpper N βs U := by
  filter_upwards [h] with k ⟨hg0, ⟨m₁, hm₁, hfl⟩, hcmp⟩
  set g : ℕ → ℝ := gE (N := N) (βs k) with hg
  have hg1 : 0 < g m₁ := lt_of_lt_of_le (mul_pos hg0 (Real.exp_pos _)) hfl
  have hlc : ∀ m, m₁ ≤ m → g m₁ ^ m ≤ g m ^ m₁ * g 0 ^ (m - m₁) := fun m hm =>
    StepPeriodic.periodic_far_ge (βs k) (StepPeriodic.connP_mem (βs k) tensorEnergyG_zero_mem) hm
  have hM := measMassOfG_le_of_logConvex_cmp (E := tensorEnergyG (MassGap.SUN.SU N)) (0 : ISite)
    (z := fun m => (2 * m) • eT) snormG_eT hm₁ hg0 hg1 hlc hcmp
  rw [← mUG_SU]
  refine le_trans hM (ENNReal.ofReal_le_ofReal ?_)
  have hlog := Real.log_le_log (mul_pos hg0 (Real.exp_pos _)) hfl
  rw [Real.log_mul hg0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hm1r : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  rw [div_le_iff₀ (by positivity), Real.log_div hg0.ne' hg1.ne']
  linarith

/-- **The defect form of (1″)**: if the mirror-defect read is eventually a strict fraction `c < 1` of the
reflected read, the reflected read is comparable to the diagonal read, with `a = 1 − c`. DERIVED: `1` the
unit fraction; `0` the sign. -/
theorem cmp_of_defect (β : ℝ)
    (hd : ∃ c : ℝ, c < 1 ∧ ∀ᶠ m in atTop,
      |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β) (mirrorDefect (N := N))
        (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))| ≤ c * |gE (N := N) β m|) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ m in atTop, a * |gE (N := N) β m| ≤
      |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
        (tensorEnergyG (MassGap.SUN.SU N) 0) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))| := by
  obtain ⟨c, hc, hev⟩ := hd
  refine ⟨1 - c, by linarith, ?_⟩
  filter_upwards [hev] with m hm
  have hs := reflRead_split (N := N) β m
  have htri := abs_add_le
    (FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
      (tensorEnergyG (MassGap.SUN.SU N) 0) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT)))
    (FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) β)
      (mirrorDefect (N := N)) (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT)))
  rw [← hs] at htri
  linarith

variable (N) in
/-- **The reflected reads along a tower at level `U`**: eventually in `k`, with `g = gE (βs k)`, a positive
contact read, a window floor at `U` (link 2), and the mirror-defect bound (the remaining form of (1′)).
DERIVED: `2` the two steps of one gap and the window base; `1` the least gap index and the unit fraction;
`0` the origin, the contact gap and the signs. -/
def ReflReadsAt (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∀ᶠ k in atTop, 0 < gE (N := N) (βs k) 0 ∧ (∃ m₁ : ℕ, 1 ≤ m₁ ∧
    gE (N := N) (βs k) 0 * Real.exp (-(2 * m₁ * (U / 2 ^ k))) ≤ gE (N := N) (βs k) m₁) ∧
    ∃ c : ℝ, c < 1 ∧ ∀ᶠ m in atTop,
      |FocusZoom.stateCov (GaugeWilson.periodicStateG (MassGap.SUN.SU N) (βs k)) (mirrorDefect (N := N))
        (tensorEnergyG (MassGap.SUN.SU N) (0 + (2 * m) • eT))| ≤ c * |gE (N := N) (βs k) m|

/-- **The window upper bound from the reflected reads.** DERIVED: no numeral beyond `ReflReadsAt`. -/
theorem windowUpper_of_defect [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ} (h : ReflReadsAt N βs U) :
    BandUpper.WindowUpper N βs U :=
  windowUpper_of_tensorReads (h.mono fun k ⟨h0, h1, h2⟩ => ⟨h0, h1, cmp_of_defect (βs k) h2⟩)

/-- **The root at `SU(N)` with the upper half in reflected-read form.** `StrongEnd N` and, at window
couplings arbitrarily close to `0⁺`, `ReflReadsAt N βs (2 log 2)` and `ExistAlong N βs` along every coupling
tower give `ClayStatementOf (SU N)`. DERIVED: `0` the limit `0⁺`; `2` the band ratio and the least rank.
Inherited: `log 2` the window rate. Vacuous: its residual implies `BandUpper.WindowUpper` at a fixed level,
refuted under `StrongEnd N` by `ReflFloor.not_upper_residual`; use `OneInput.clayStatement_of_strongEnd`. -/
theorem clayStatement_of_strongEnd_reads [Fact (2 ≤ N)] (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReflReadsAt N βs (2 * Real.log 2) ∧ ExistAlong N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  BandUpper.clayStatement_of_strongEnd_upper hS
    (hR.mono fun _ h βs hT => ⟨windowUpper_of_defect (h βs hT).1, (h βs hT).2⟩)

end MassGap.BandClose

end

#print axioms MassGap.BandClose.ireflObs_plaqFieldG
#print axioms MassGap.BandClose.plaqFieldG_swap
#print axioms MassGap.BandClose.transObs_plaqFieldG
#print axioms MassGap.BandClose.transObs_tensorEnergyG
#print axioms MassGap.BandClose.ireflSite_zero_sub_one
#print axioms MassGap.BandClose.ireflSite_zero_zero
#print axioms MassGap.BandClose.ireflObs_tensorEnergyG_zero
#print axioms MassGap.BandClose.ireflObs_tensorEnergyG_split
#print axioms MassGap.BandClose.not_translate_combination
#print axioms MassGap.BandClose.stateCov_add_left
#print axioms MassGap.BandClose.reflRead_split
#print axioms MassGap.BandClose.snormG_eT
#print axioms MassGap.BandClose.logConvex_floor
#print axioms MassGap.BandClose.measMassOfG_le_of_logConvex_cmp
#print axioms MassGap.BandClose.tensorEnergyG_zero_mem
#print axioms MassGap.BandClose.windowUpper_of_tensorReads
#print axioms MassGap.BandClose.cmp_of_defect
#print axioms MassGap.BandClose.windowUpper_of_defect
#print axioms MassGap.BandClose.clayStatement_of_strongEnd_reads
