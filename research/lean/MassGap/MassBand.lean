import Mathlib
import MassGap.ReflFloor
import MassGap.BandUpper
import MassGap.ReadPos

/-!
# MassGap.MassBand — the measured band along one coupling tower: a pairwise ratio, and its upper half at the tower's own depth

The headline `OneInput.clayStatement_of_strongEnd` takes `StrongEnd N` and, frequently as `u₀ → 0⁺`, along every
coupling tower `βs` at window coupling `u₀`, `MeasuredTower.MeasTowerG (SU N) βs ∧ ExistAlong N βs`. This module
reads the first conjunct (M) along one tower. Declarations are in the namespace `MassGap.MassBand`.

## (M) in plain mathematics

At step `k` of a tower (`βs k → ∞`, torus doubling defect `D(βs k, k) = u₀` at window side `2^k`), `m′(βs k)` is
the measured tensor mass: the supremum, in `[0, ∞]`, of the rates `m` with
`|Cov_ν(E(x), E(x+z))| ≤ C e^{−m ‖z‖∞}`, where `ν` is the infinite-volume periodic Wilson state at `βs k` and
`E = P₀₁ − P₂₃`. The window reading is `w_k = 2^k m′(βs k)`. (M) asks one `L > 0` with, eventually,
`m′(βs k)` finite and `L ≤ w_k ≤ 2L` (`BandUpper.measTowerG_iff_window`).

* The lower half (`L ≤ w_k` for some `L > 0`) is proved on every tower at `u₀ ≤ 1/1000`
  (`FinalBridge.windowReading_floor`, `L = log 2`, given finiteness) and at `u₀ ≤ (1/2)^{2^i}/250` with
  `L = 2^i log 2` (`ReflFloor.mass_floor_deep`, no finiteness needed).
* The upper half is finiteness of `m′(βs k)` and the ratio: the eventual supremum of `w_k` at most twice its
  eventual infimum. An upper bound on a mass is a lower bound on a correlation
  (`BandUpper.measMassOfG_le_of_floor`).

## What is proved

* `measTowerG_iff_ratio`: near `0⁺`, on every tower, (M) holds exactly when some `K` has, for all `j, k ≥ K`,
  `m′(βs j) < ∞` and `w_j ≤ 2 w_k`. The constant `L` disappears: (M) is a pairwise ratio of the window reading
  along the tower. The floor supplies positivity.
* `measTowerG_of_windowUpper_deep`: a tower at `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, with the window upper bound at
  level `2 · 2^i log 2` is a measured tower (band at `L = 2^i log 2`, the tower's own proved floor).
* `measTowerG_of_reflFloor_deep`: the same from the reflected floor `ReadPos.ReflFloorAt` at that level.
* `not_windowUpper_shallow`: at `u₀ ≤ (1/2)^{2^{i+2}}/250` the level `2 · 2^i log 2` is refuted
  (`ReflFloor.not_windowUpper`). So the depth `i` in the residual below has to sit within two of the deepest depth
  the seed allows; the residual is not refuted by the deep floor at that choice.
* `deepResidual_of_upper`: the residual of `BandUpper.clayStatement_of_strongEnd_upper` (level `2 log 2`, refuted
  under `StrongEnd` by `ReflFloor.not_upper_residual`) implies the residual of `clayStatement_of_strongEnd_deep`.
* `clayStatement_of_strongEnd_deep`: `StrongEnd N` and, frequently near `0⁺`, some depth `i ≥ 1` with
  `u₀ ≤ (1/2)^{2^i}/250` and, along every tower at `u₀`, `WindowUpper N βs (2 · 2^i log 2) ∧ ExistAlong N βs`,
  give `ClayStatementOf (SU N)`.

## Tests

* Consistency with the deep floor. At `β = βs k` the recursion (`ReflFloor.iterate_seed`) carries the defect
  `u₀ ≤ (1/2)^{2^i}/250` at window `k` to `≤ (1/2)^{2^{i+j}}/250` at window `k+j`, and `mass_ge_deep` there gives
  `2^{i+j} log 2 / 2^{k+j}`: the same floor. Windows below `k` have a larger defect. So the recursion gives one
  floor per tower and no growth of `w_k` along a fixed tower; the argument of `ReflFloor` refutes fixed levels
  across towers (as `u₀ → 0⁺`), not the band along one tower.
* Oscillation. No proved statement bounds `w_k` above at any `k`; none forces it to oscillate. Neither half of a
  refutation of the ratio is in the tree.
* The contact read `ReadPos.gE_zero_pos` is `g(0) > 0` only. Through log-convexity
  (`BandUpper.measMassOfG_le_of_logConvex`) an upper bound needs `g(m₁) ≥ g(0) e^{−2 m₁ U / 2^k}` at one lag
  `m₁ ≥ 1`, a far read; `g(0)` alone fixes no rate.
* The defect. A large gap of the transfer matrix would make the torus free energy nearly extensive and so the
  defect small; read in that direction the defect `D = u₀` bounds the transfer gap above. The measured tensor mass
  is at least the transfer gap (`GapReadsTensorProved.gapReadsTensor`), not at most: the tensor channel may miss
  the lowest excitation. A defect bound on the transfer gap does not bound `m′` above unless the tensor reading
  overlaps the lowest excited state, which is again a correlation floor.

## What does not follow

* The upper half is not proved. The exact missing inequality, at the tower's depth `i`, is, eventually in `k`,
  `m′(βs k) ≤ 2 · 2^i log 2 / 2^k`; by `BandUpper.windowUpper_of_corrFloor` it follows from a tensor correlation
  floor `|Cov_ν(E(x), E(x+z_j))| ≥ a e^{−(2^{i+1} log 2 / 2^k) ‖z_j‖∞}`, `a > 0`, along separations `‖z_j‖∞ → ∞`.
  In the exact form `measTowerG_iff_ratio` it is: `m′(βs k) < ∞` and `w_j ≤ 2 w_k` for all large `j, k`.
* Finiteness of `m′` along a tower is not proved; it is part of the upper half.
* `clayStatement_of_strongEnd_deep` is a capstone beside `OneInput.clayStatement_of_strongEnd`: its residual
  implies the residual there through `measTowerG_of_windowUpper_deep`, not conversely (a band at `L` above
  `2^i log 2` meets (M) without the level `2 · 2^i log 2`).
* `ExistAlong` and `StrongEnd N`: untouched.

DERIVED (module-wide): `0` the limit `0⁺` and the signs; `1` the least depth and the base of `log 2 > 0`; `2` the
band ratio of `MeasTowerG`, the window base, the doubling, the least rank and the base of `log 2`; `4` in
`2^{i+2} = 4 · 2^i`, two doublings past the depth `i`. Inherited, not derived here: `250` the squaring constant
and `(1/2)^{2^i}/250` the deep seed of `ReflFloor.mass_floor_deep`, whose `i = 1` value is the seed `1/1000` of
`DoublingSharp`; `log 2` the rate of one halving.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.MassBand

open Filter Topology
open scoped ENNReal
open MassGap.MeasuredTower (MeasTowerG)
open MassGap.MeasuredSpacing (mU measSpacing)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.ConstantPhysicsLine (ExistAlong)
open MassGap.BandUpper (WindowUpper)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-! ## 1. The band is a pairwise ratio -/

/-- **The measured tower is a pairwise ratio of the window reading.** Near `0⁺`, on every coupling tower,
`MeasTowerG (SU N) βs` holds exactly when some `K` has, for all `j, k ≥ K`, `m′(βs j)` finite and
`2^j m′(βs j) ≤ 2 · 2^k m′(βs k)`. The proved floor `FinalBridge.windowReading_floor` supplies `L > 0`, taken as
the infimum of the window reading from the point where the floor holds. DERIVED: `0` the limit `0⁺`; `2` the band
ratio and the least rank; `1` the base of `log 2 > 0`. -/
theorem measTowerG_iff_ratio :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      (MeasTowerG (MassGap.SUN.SU N) βs ↔ ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
        mU (NeZero.ne N) (βs j) ≠ ⊤ ∧
          ScaleLightCone.windowReading N βs j ≤ 2 * ScaleLightCone.windowReading N βs k) := by
  filter_upwards [FinalBridge.windowReading_floor (N := N) (Fact.out : 2 ≤ N)] with u hu βs hT
  have hl := Real.log_pos one_lt_two
  constructor
  · intro hM
    obtain ⟨-, L, hL, hb⟩ := (BandUpper.measTowerG_iff_window βs).mp hM
    obtain ⟨K, hK⟩ := eventually_atTop.mp hb
    exact ⟨K, fun j k hj hk => ⟨(hK j hj).1, by linarith [(hK j hj).2.2, (hK k hk).2.1]⟩⟩
  · rintro ⟨K, hK⟩
    have hfin : ∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ⊤ :=
      (eventually_ge_atTop K).mono fun k hk => (hK k k hk hk).1
    obtain ⟨K2, hK2⟩ := eventually_atTop.mp ((hu βs hT hfin).and (eventually_ge_atTop K))
    set w := ScaleLightCone.windowReading N βs with hw
    set s : Set ℝ := w '' Set.Ici K2 with hs
    have hne : s.Nonempty := ⟨w K2, K2, Set.mem_Ici.mpr le_rfl, rfl⟩
    have hbdd : BddBelow s := ⟨0, by
      rintro _ ⟨k, hk, rfl⟩
      exact le_trans hl.le (hK2 k hk).1⟩
    have hlog : Real.log 2 ≤ sInf s := le_csInf hne (by
      rintro _ ⟨k, hk, rfl⟩
      exact (hK2 k hk).1)
    refine (BandUpper.measTowerG_iff_window βs).mpr
      ⟨hT.1, sInf s, lt_of_lt_of_le hl hlog, ?_⟩
    filter_upwards [eventually_ge_atTop K2] with j hj
    have hjK : K ≤ j := (hK2 j hj).2
    refine ⟨(hK j j hjK hjK).1, csInf_le hbdd ⟨j, hj, rfl⟩, ?_⟩
    have h2 : w j / 2 ≤ sInf s := le_csInf hne (by
      rintro _ ⟨k, hk, rfl⟩
      have := (hK j k hjK (hK2 k hk).2).2
      linarith)
    linarith

/-! ## 2. The upper half at the tower's own depth -/

/-- **The window upper bound is monotone in its level.** DERIVED: `2` the window base. -/
theorem windowUpper_mono {βs : ℕ → ℝ} {U U' : ℝ} (hUU : U ≤ U') (h : WindowUpper N βs U) :
    WindowUpper N βs U' :=
  h.mono fun k hk => hk.trans (ENNReal.ofReal_le_ofReal
    ((div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ k)).mpr hUU))

/-- **At depth `i` the upper bound at twice the deep floor gives the band.** A coupling tower at
`u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, with `WindowUpper N βs (2 · 2^i log 2)` is a measured tower: the proved floor
`2^i log 2 ≤ 2^k m′` (`ReflFloor.mass_floor_deep`) and the upper bound are the band at `L = 2^i log 2`.
DERIVED: `1` the least depth; `2` the band ratio and the base. Inherited: `250` and the deep seed. -/
theorem measTowerG_of_windowUpper_deep {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (hU : WindowUpper N βs (2 * (2 ^ i * Real.log 2))) :
    MeasTowerG (MassGap.SUN.SU N) βs := by
  have hl := Real.log_pos one_lt_two
  refine (BandUpper.measTowerG_iff_window βs).mpr ⟨hT.1, 2 ^ i * Real.log 2, by positivity, ?_⟩
  filter_upwards [hU, ReflFloor.mass_floor_deep (Fact.out : 2 ≤ N) hi hu hT] with k hk hlo
  have hne : mU (NeZero.ne N) (βs k) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hk
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := (ENNReal.ofReal_le_iff_le_toReal hne).mp hlo
  have h2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hk
  rw [div_le_iff₀ hp] at h1
  rw [le_div_iff₀ hp] at h2
  unfold ScaleLightCone.windowReading measSpacing
  exact ⟨hne, by linarith, by linarith⟩

/-- **The same from the reflected floor at that level.** `ReadPos.ReflFloorAt N βs (2 · 2^i log 2)` gives the
window upper bound (`ReadPos.reflReadsAt_of_floor`, `BandClose.windowUpper_of_defect`). DERIVED: `1` the least
depth; `2` the band ratio. Inherited: `250` and the deep seed. -/
theorem measTowerG_of_reflFloor_deep {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    (h : ReadPos.ReflFloorAt N βs (2 * (2 ^ i * Real.log 2))) :
    MeasTowerG (MassGap.SUN.SU N) βs :=
  measTowerG_of_windowUpper_deep hi hu hT
    (BandClose.windowUpper_of_defect (ReadPos.reflReadsAt_of_floor (hT.2.2.mono fun _ hk => hk.2.1) h))

/-- **A depth two below the seed's deepest is refuted.** At `u₀ ≤ (1/2)^{2^{i+2}}/250` no coupling tower has
`WindowUpper N βs (2 · 2^i log 2)`, since `2 · 2^i log 2 < 2^{i+2} log 2` (`ReflFloor.not_windowUpper`).
DERIVED: `1` the least depth; `2` the doubling; `4` two doublings. Inherited: `250`. -/
theorem not_windowUpper_shallow {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ (i + 2)) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ¬ WindowUpper N βs (2 * (2 ^ i * Real.log 2)) := by
  refine ReflFloor.not_windowUpper (Fact.out : 2 ≤ N) (by omega) hu hT ?_
  have hl := Real.log_pos one_lt_two
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  have e : (2 : ℝ) ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
  rw [e]
  have := mul_pos h2i hl
  nlinarith

/-! ## 3. The root with the upper half at the tower's depth -/

/-- **The level-`2 log 2` residual implies the depth residual** (at `i = 1`, where the deep seed is `1/1000`).
DERIVED: `0` the limit `0⁺`; `1` the depth; `2` the band ratio. Inherited: `250`. -/
theorem deepResidual_of_upper
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      WindowUpper N βs (2 * Real.log 2) ∧ ExistAlong N βs) :
    ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ i : ℕ, 1 ≤ i ∧ u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250 ∧
      ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
        WindowUpper N βs (2 * (2 ^ i * Real.log 2)) ∧ ExistAlong N βs := by
  have hs : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ 1) / 250 :=
    nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
  have hl := Real.log_pos one_lt_two
  refine (hR.and_eventually hs).mono fun u ⟨h, hu⟩ => ⟨1, le_rfl, hu, fun βs hT =>
    ⟨windowUpper_mono ?_ (h βs hT).1, (h βs hT).2⟩⟩
  rw [pow_one]
  linarith

/-- **The root at `SU(N)` with the upper half at the tower's own depth.** `StrongEnd N` and, at window couplings
arbitrarily close to `0⁺`, a depth `i ≥ 1` with `u₀ ≤ (1/2)^{2^i}/250` and, along every coupling tower at `u₀`,
`WindowUpper N βs (2 · 2^i log 2)` and `ExistAlong N βs`, give `ClayStatementOf (SU N)`
(`OneInput.clayStatement_of_strongEnd` with `measTowerG_of_windowUpper_deep`). DERIVED: `0` the limit `0⁺`; `1`
the least depth; `2` the band ratio. Inherited: `250` and the deep seed. -/
theorem clayStatement_of_strongEnd_deep (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ i : ℕ, 1 ≤ i ∧ u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250 ∧
      ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
        WindowUpper N βs (2 * (2 ^ i * Real.log 2)) ∧ ExistAlong N βs) :
    ClayStatementG.ClayStatementOf (MassGap.SUN.SU N) :=
  OneInput.clayStatement_of_strongEnd hS (hR.mono fun _ ⟨_, hi, hu, h⟩ βs hT =>
    ⟨measTowerG_of_windowUpper_deep hi hu hT (h βs hT).1, (h βs hT).2⟩)

end MassGap.MassBand

end

#print axioms MassGap.MassBand.measTowerG_iff_ratio
#print axioms MassGap.MassBand.windowUpper_mono
#print axioms MassGap.MassBand.measTowerG_of_windowUpper_deep
#print axioms MassGap.MassBand.measTowerG_of_reflFloor_deep
#print axioms MassGap.MassBand.not_windowUpper_shallow
#print axioms MassGap.MassBand.deepResidual_of_upper
#print axioms MassGap.MassBand.clayStatement_of_strongEnd_deep
