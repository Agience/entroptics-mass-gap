import Mathlib
import MassGap.ObserverEnergyM
import MassGap.PotSharpCluster
import MassGap.HeatBathLocal

noncomputable section

/-!
# MassGap.ObserverEnergyV — the coarse view in the proved box gives the gap of the energy transfer

Statement V of the observer route: at one dyadic step `m₀`, the law the observer reads is, on a coarse
lattice, Wilson times a gauge-invariant local potential inside the proved box (`SU(2)`, `β ≤ 1/20`,
that is `β_std ≤ 1/10`, local norm `≤ 1/16`, supports within two steps). This module states V and
proves that it gives the gap of the energy density's reconstructed transfer at step `m₀`, at an explicit
rate that does not depend on the field normalisation.

1. **Clustering on the box at an explicit rate** (`abs_le_coarseRate`, `pot_cluster_rate`):
   `PotSharpCluster.pot_cluster_full_sharp` with `y = 3` and `⌊n/(6z+1)⌋` sweeps gives, for every pair of
   observables read on supports of sizes `≤ a`, `≤ b` at neighbour level `n` and of second moments
   `≤ M`, the bound `M (b + (2/c) e^{c/2} a) · coarseRate 5184 (7/100)ⁿ`, uniformly in the volume.
   `pot_h_null`: an observable not reading a torus link is fixed by that link's conditional expectation
   up to a null vector, so a local observable's support bounds the links its `hₗ` sees.
2. **Lattice clustering uniform in the fine step gives the gap** (`kernF_conn_le_of_lat`,
   `LatClusterRate`, `flow_gapAt_of_latClusterRate`): a bound on the observer's connected reflected
   lattice functions at time `aₘ₀ n`, holding eventually in the fine step with a constant free in the
   step, passes to the `ultra`-limit (`ContinuumFlow.tendsto_contSF`) and, through
   `FlowCapstone.gapAt_gTransfer_of_abs_cluster`, is the gap of the transfer at step `m₀` at that rate.
3. **V, pairing form** (`ObserverVPair`, the weakest form the gap consumes): for every pair of margin
   monomials there are support bounds `a`, `b` and a second-moment bound `M` such that, eventually in the
   fine step, the three reflected lattice functions are limits of pairings of two readers in a box
   Gibbs state, at neighbour level `⌊n/q⌋`. `latClusterRate_of_observerVPair` turns it into lattice
   clustering at `vRate q = coarseRate^{1/q}`.
4. **V, law form** (`ObserverV`, the statement as the route poses it): at each large fine step one
   coarse map `χₖ` whose law under `stateK k` is a limit of box Gibbs states, the observer's reflected
   smeared products factor through `χₖ` as local gauge-invariant coarse observables of bounded support,
   their second moments are bounded, and their supports separate linearly in `n`.
   `observerVPair_of_observerV` derives the pairing form.
5. **The energy density** (`energy_gapAt_of_observerV`, `energy_M_of_observerV`,
   `energy_clay_of_observerV`): V for `ObserverEnergyMoments.obsEnergyOn` gives
   `GapAt (energyTransfer … m₀) (vRate q)`, hence `FlowClusterAbs` at every window and, with the smeared
   moments (E) and `FlowConnectedNonzero` (N), the continuum statement.

The `a⁻⁴` of the energy density enters only the second-moment bound `M` of the readers (the readers of
the scaled field carry the factor); the rate `vRate q` is that of the box and the separation, and the
gap is the same at every normalisation. V puts an upper bound on the readers' moments and asks
nothing of their connected pairings, so it does not decide N; without N the gap is free and empty
(`ObserverEnergyM.flowClusterAbs_of_not_connectedNonzero`).
-/

namespace MassGap.ObserverEnergyV

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM Filter
open MassGap.KnabeCriterion (PatchSystem ReadsNot periodicGaugeInvSubmodule
  periodicGaugeInv_of_isIGaugeInvariant)
open MassGap.HeatBathGapDecay (Far nrm nrm_nonneg SeparatedPair)
open MassGap.WeightedErgodic (oneW)
open MassGap.WeightedTorus (wTorusState wForm wCondExp wLift torusObs_wLift wExpect)
open MassGap.LocalPotential (LocalPotFam potWeight)
open MassGap.PotKnabe (potSys)
open MassGap.ObserverKnabe (obsNb Near2)
open MassGap.PotSharpCluster (pot_cluster_full_sharp)
open MassGap.PeriodicState (torusObs)
open MassGap.GaugeInvariantAlgebra (IsIGaugeInvariant)
open scoped Topology

/-! ## 1. Clustering on the box at an explicit rate -/

section Box

/-- **The clustering rate of a covariance bound** at neighbour bound `z` and heat-bath gap `c`:
`max(e/3, e^{−c/(2(6z + 1))})`, the rate per neighbour level of `cov_bound_exp` at `y = 3` with
`⌊n/(6z + 1)⌋` sweeps.

DERIVED: `1` is the exponent of `e` and the `+ 1` of the sweep length; `2` is `gapRate`'s, in
`e^{−cs/2}`; `6 = 2y`. CHOSEN: `3` is the sweep parameter `y`, the least integer above `e`, so that
`e/3 < 1`; `6z + 1 = 2zy + 1` levels per sweep (as `HeatBathGapDecay.clusterRate`, before its square
root). -/
def coarseRate (z : ℕ) (c : ℝ) : ℝ :=
  max (Real.exp 1 / 3) (Real.exp (-(c / (2 * ((6 * z + 1 : ℕ) : ℝ)))))

/-- DERIVED: `0` is the sign; `3` is the sweep parameter. -/
theorem coarseRate_pos (z : ℕ) (c : ℝ) : 0 < coarseRate z c :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

#print axioms coarseRate_pos

/-- DERIVED: `1` is the bound; `0` the sign of `c`; `3` the sweep parameter (`e < 3`). -/
theorem coarseRate_lt_one (z : ℕ) {c : ℝ} (hc : 0 < c) : coarseRate z c < 1 := by
  have hD : (0 : ℝ) < ((6 * z + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  refine max_lt ?_ ?_
  · have := Real.exp_one_lt_d9
    linarith
  · have hpos : 0 < c / (2 * ((6 * z + 1 : ℕ) : ℝ)) := div_pos hc (mul_pos two_pos hD)
    calc Real.exp (-(c / (2 * ((6 * z + 1 : ℕ) : ℝ)))) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

#print axioms coarseRate_lt_one

/-- **The arithmetic of the clustering rate.** If for every number of sweeps `s` the covariance `X`
obeys the bound of `HeatBathGapDecay.cov_bound_exp` at `y = 3` and level `n`, with norms `nf`, `ng`
(`nf ng ≤ Mx`), support sizes `Cc ≤ b`, `Ac ≤ a` and gap `c > 0`, then
`|X| ≤ Mx (b + (2/c) e^{c/2} a) · coarseRate z cⁿ`. At `s = ⌊n/(6z + 1)⌋`:
`s e^{6zs} 3⁻ⁿ ≤ (e/3)ⁿ` and `e^{−cs/2} ≤ e^{c/2} (e^{−c/(2(6z+1))})ⁿ`.

DERIVED: `2`, `3`, `6`, `1` as in `coarseRate`; `0` the signs of the norms and sizes. -/
theorem abs_le_coarseRate {z : ℕ} {c : ℝ} (hc : 0 < c) {X nf ng Ac Cc Mx a b : ℝ} (n : ℕ)
    (hX : ∀ s : ℕ, |X| ≤ s * Cc * (nf * ((3 : ℝ)⁻¹ ^ n * Real.exp (2 * (z : ℝ) * 3 * s))) * ng
        + 2 / c * Real.exp (-(c * s / 2)) * (Ac * nf) * ng)
    (hnf : 0 ≤ nf) (hng : 0 ≤ ng) (hu : nf * ng ≤ Mx) (hCc0 : 0 ≤ Cc) (hCc : Cc ≤ b)
    (hAc0 : 0 ≤ Ac) (hAc : Ac ≤ a) :
    |X| ≤ Mx * (b + 2 / c * Real.exp (c / 2) * a) * coarseRate z c ^ n := by
  have h2c : 0 ≤ 2 / c := div_nonneg zero_le_two hc.le
  have hD : (0 : ℝ) < ((6 * z + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hDval : ((6 * z + 1 : ℕ) : ℝ) = 6 * (z : ℝ) + 1 := by push_cast; ring
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = coarseRate z c := ⟨_, rfl⟩
  have hr0a : Real.exp 1 / 3 ≤ r0 := by rw [hr0]; exact le_max_left _ _
  have hr0b : Real.exp (-(c / (2 * ((6 * z + 1 : ℕ) : ℝ)))) ≤ r0 := by
    rw [hr0]; exact le_max_right _ _
  have hr0pos : 0 < r0 := by rw [hr0]; exact coarseRate_pos z c
  rw [← hr0]
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = n / (6 * z + 1) := ⟨_, rfl⟩
  have hdm : ((6 * z + 1 : ℕ) : ℝ) * s + ((n % (6 * z + 1) : ℕ) : ℝ) = n := by
    rw [hs]
    exact_mod_cast Nat.div_add_mod n (6 * z + 1)
  have hml : ((n % (6 * z + 1) : ℕ) : ℝ) < ((6 * z + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mod_lt n (by omega : 6 * z + 1 > 0)
  have hm0 : (0 : ℝ) ≤ ((n % (6 * z + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsD : ((6 * z + 1 : ℕ) : ℝ) * s ≤ n := by linarith
  have hnD : (n : ℝ) ≤ ((6 * z + 1 : ℕ) : ℝ) * s + ((6 * z + 1 : ℕ) : ℝ) := by linarith
  have i1 : (s : ℝ) * Real.exp (2 * z * 3 * s) ≤ Real.exp n := by
    calc (s : ℝ) * Real.exp (2 * z * 3 * s) ≤ Real.exp s * Real.exp (2 * z * 3 * s) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (s : ℝ)])
            (Real.exp_pos _).le
      _ = Real.exp (((6 * z + 1 : ℕ) : ℝ) * s) := by
          rw [← Real.exp_add, hDval]
          congr 1
          ring
      _ ≤ Real.exp n := Real.exp_le_exp.mpr hsD
  have p1 : (s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n ≤ r0 ^ n := by
    calc (s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n ≤ Real.exp n * (3 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right i1 (pow_nonneg (by norm_num) n)
      _ = (Real.exp 1 / 3) ^ n := by
          rw [div_eq_mul_inv, mul_pow, ← Real.exp_nat_mul, mul_one]
      _ ≤ r0 ^ n := pow_le_pow_left₀ (by positivity) hr0a n
  have i2 : Real.exp (-(c * s / 2))
      ≤ Real.exp (c / 2) * Real.exp (-(c / (2 * ((6 * z + 1 : ℕ) : ℝ)))) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hDD : ((6 * z + 1 : ℕ) : ℝ) * ((6 * z + 1 : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hD.ne'
    have hm := mul_le_mul_of_nonneg_right hnD (le_of_lt (div_pos hc (mul_pos two_pos hD)))
    have he : (((6 * z + 1 : ℕ) : ℝ) * s + ((6 * z + 1 : ℕ) : ℝ))
          * (c / (2 * ((6 * z + 1 : ℕ) : ℝ)))
        = c * s / 2 + c / 2 := by
      linear_combination (c * s / 2 + c / 2) * hDD
    linarith
  have p2 : Real.exp (-(c * s / 2)) ≤ Real.exp (c / 2) * r0 ^ n :=
    i2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hr0b n)
      (Real.exp_pos _).le)
  have huv : 0 ≤ nf * ng := mul_nonneg hnf hng
  have hb0 : 0 ≤ b := hCc0.trans hCc
  have ha0 : 0 ≤ a := hAc0.trans hAc
  have T1le : (s : ℝ) * Cc * (nf * ((3 : ℝ)⁻¹ ^ n * Real.exp (2 * z * 3 * s))) * ng
      ≤ r0 ^ n * (b * Mx) := by
    calc (s : ℝ) * Cc * (nf * ((3 : ℝ)⁻¹ ^ n * Real.exp (2 * z * 3 * s))) * ng
        = ((s : ℝ) * Real.exp (2 * z * 3 * s) * (3 : ℝ)⁻¹ ^ n) * (Cc * (nf * ng)) := by ring
      _ ≤ r0 ^ n * (b * Mx) :=
          mul_le_mul p1 (mul_le_mul hCc hu huv hb0) (mul_nonneg hCc0 huv)
            (pow_nonneg hr0pos.le n)
  have T2le : 2 / c * Real.exp (-(c * s / 2)) * (Ac * nf) * ng
      ≤ 2 / c * (Real.exp (c / 2) * r0 ^ n) * (a * Mx) := by
    calc 2 / c * Real.exp (-(c * s / 2)) * (Ac * nf) * ng
        = 2 / c * Real.exp (-(c * s / 2)) * (Ac * (nf * ng)) := by ring
      _ ≤ 2 / c * (Real.exp (c / 2) * r0 ^ n) * (a * Mx) :=
          mul_le_mul (mul_le_mul_of_nonneg_left p2 h2c) (mul_le_mul hAc hu huv ha0)
            (mul_nonneg hAc0 huv)
            (mul_nonneg h2c (mul_nonneg (Real.exp_pos _).le (pow_nonneg hr0pos.le n)))
  have hfinal : r0 ^ n * (b * Mx) + 2 / c * (Real.exp (c / 2) * r0 ^ n) * (a * Mx)
      = Mx * (b + 2 / c * Real.exp (c / 2) * a) * r0 ^ n := by ring
  linarith [hX s, T1le, T2le, hfinal]

#print axioms abs_le_coarseRate

/-- **An observable not reading a torus link is fixed by its conditional expectation, up to a null
vector**: on the potential box system, `ReadsNot j l x` gives `B(hₗ x, hₗ x) = 0`. The torus reading of
`x − Eₗ x` is `torusObs x − wAvg (torusObs x)`, which vanishes (`WeightedHeatBath.wAvg_of_readsNot`).

DERIVED: `2` is the rank; `300000` the box side; `0` the null value. -/
theorem pot_h_null (β : ℝ) (F : LocalPotFam 2)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := 2) (2 * j + 1)))
    (hx : ReadsNot j l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))) :
    (potSys β F hdiam j hj).B ((potSys β F hdiam j hj).h l x) ((potSys β F hdiam j hj).h l x) = 0 := by
  have h0 : ∀ W, (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)) (pullback (2 * j + 1) W)
      - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
          (pullback (2 * j + 1) W) = 0 := by
    intro W
    have e1 : wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
          (pullback (2 * j + 1) W)
        = (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)) (pullback (2 * j + 1) W) :=
      (congrFun (torusObs_wLift (potWeight β F) (2 * j + 1) l
        (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))) W).trans
        (MassGap.WeightedHeatBath.wAvg_of_readsNot ((potWeight β F).pos _)
          ((potWeight β F).cont _) l hx W)
    rw [e1, sub_self]
  show wExpect ((potWeight β F).Φ (2 * j + 1))
      (torusObs (2 * j + 1)
        (((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
            - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)))
          * ((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
            - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))))) = 0
  have hz : torusObs (2 * j + 1)
      (((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
          - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)))
        * ((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
          - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))))
      = fun _ => 0 := by
    funext W
    show ((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)) (pullback (2 * j + 1) W)
        - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
            (pullback (2 * j + 1) W))
      * ((x : C(GibbsSpec.IConf (SUN.SU 2), ℝ)) (pullback (2 * j + 1) W)
        - wLift (potWeight β F) (2 * j + 1) l (x : C(GibbsSpec.IConf (SUN.SU 2), ℝ))
            (pullback (2 * j + 1) W)) = 0
    rw [h0 W, mul_zero]
  rw [hz]
  unfold wExpect
  simp

#print axioms pot_h_null

/-- **Clustering on the sharp box at an explicit rate.** `SU(2)`, `β ≤ 1/20` (`β_std ≤ 1/10`), local
norm `≤ 1/16`, supports within two steps, every extent: two observables at neighbour level `n` along
`obsNb`, read on supports of sizes `≤ a`, `≤ b`, of second moments `≤ M`, have
`|B(f, g) − B(f, 1) B(g, 1)| ≤ max(M, 0) (b + (2/c) e^{c/2} a) · coarseRate 5184 cⁿ` at `c = 7/100`
(`pot_cluster_full_sharp`, `abs_le_coarseRate`). No hypothesis beyond the box; uniform in the volume.

DERIVED: `5184` is `card_near2_le`'s window count; `7/100` is `pot_globalGap_sharp`'s gap; `3` the
sweep parameter; `300000` the box side; `2` the rank; `1/20`, `1/16` the box. -/
theorem pot_cluster_rate {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 20) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 16)
    (hdiam : ∀ M X a b, a ∈ (F.P M).supp X → b ∈ (F.P M).supp X → Near2 (b.2 - a.2))
    (j : ℕ) (hj : 300000 ≤ j + 1) {a b : ℕ} {M : ℝ} (f g : (potSys β F hdiam j hj).E) (n : ℕ)
    (hsep : SeparatedPair (potSys β F hdiam j hj) (obsNb (2 * j + 1)) f g n a b)
    (hff : (potSys β F hdiam j hj).B f f ≤ M) (hgg : (potSys β F hdiam j hj).B g g ≤ M) :
    |(potSys β F hdiam j hj).B f g
        - (potSys β F hdiam j hj).B f (oneW j) * (potSys β F hdiam j hj).B g (oneW j)|
      ≤ max M 0 * (b + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
          * coarseRate 5184 (7 / 100) ^ n := by
  obtain ⟨A, C, hA, hC, hf, hg, hfar⟩ := hsep
  have hnf := nrm_nonneg (potSys β F hdiam j hj) f
  have hng := nrm_nonneg (potSys β F hdiam j hj) g
  have hnfM : nrm (potSys β F hdiam j hj) f ≤ Real.sqrt (max M 0) :=
    Real.sqrt_le_sqrt (hff.trans (le_max_left M 0))
  have hngM : nrm (potSys β F hdiam j hj) g ≤ Real.sqrt (max M 0) :=
    Real.sqrt_le_sqrt (hgg.trans (le_max_left M 0))
  have hu : nrm (potSys β F hdiam j hj) f * nrm (potSys β F hdiam j hj) g ≤ max M 0 := by
    calc nrm (potSys β F hdiam j hj) f * nrm (potSys β F hdiam j hj) g
        ≤ Real.sqrt (max M 0) * Real.sqrt (max M 0) :=
          mul_le_mul hnfM hngM hng (Real.sqrt_nonneg _)
      _ = max M 0 := Real.mul_self_sqrt (le_max_right M 0)
  exact abs_le_coarseRate (z := 5184) (by norm_num) n
    (fun s => pot_cluster_full_sharp hβ0 hβ F hν hdiam j hj A C f g hf hg n hfar
      (by norm_num : (1 : ℝ) ≤ 3) s)
    hnf hng hu (Nat.cast_nonneg _) (by exact_mod_cast hC) (Nat.cast_nonneg _)
    (by exact_mod_cast hA)

#print axioms pot_cluster_rate

end Box

/-! ## 2. Lattice clustering uniform in the fine step gives the gap -/

section Limit

variable {N : ℕ}

/-- **A lattice bound passes to the flowed kernel.** If, eventually in the fine step, the connected
reflected lattice function of `P` and `Q` shifted by `aₘ₀ n` is at most `B`, then so is the connected
flowed kernel (`tendsto_contSF` along `ultra ≤ atTop`; the one-point function of the shifted monomial is
that of `Q`, `ObserverGapScale.kernF_vac_shift`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem kernF_conn_le_of_lat (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    (m0 n : ℕ) (P Q : Mono N) {B : ℝ}
    (h : ∀ᶠ k in atTop,
      |latSF hN Φ k (pairFam τ P (Mono.shift (timeVec N m0 τ n) Q))
        - latSF hN Φ k (pairFam τ P (emptyMono N))
          * latSF hN Φ k (pairFam τ (emptyMono N) (Mono.shift (timeVec N m0 τ n) Q))| ≤ B) :
    |kernF hN Φ τ P (Mono.shift (timeVec N m0 τ n) Q)
        - kernF hN Φ τ P (emptyMono N) * kernF hN Φ τ (emptyMono N) Q| ≤ B := by
  rw [← kernF_vac_shift hN Φ τ m0 n Q]
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact le_of_tendsto
    (((tendsto_contSF hN Φ hB _).sub
      ((tendsto_contSF hN Φ hB _).mul (tendsto_contSF hN Φ hB _))).abs)
    (h.filter_mono ultra_le)

#print axioms kernF_conn_le_of_lat

/-- **Lattice clustering at rate `ρ` along the grid of step `m₀`, uniform in the fine step**: every pair
of margin monomials has a constant `C` such that at every `n`, eventually in the fine step `k`, the
connected reflected lattice function at time `aₘ₀ n` is at most `C ρⁿ`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def LatClusterRate (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (m0 : ℕ) (ρ : ℝ) : Prop :=
  ∀ P Q : MarginMono N τ r, ∃ C : ℝ, ∀ n : ℕ, ∀ᶠ k in atTop,
    |latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m0 τ n) Q.1))
      - latSF hN Φ k (pairFam τ P.1 (emptyMono N))
        * latSF hN Φ k (pairFam τ (emptyMono N) (Mono.shift (timeVec N m0 τ n) Q.1))|
      ≤ C * ρ ^ n

/-- **Lattice clustering uniform in the fine step is the gap at step `m₀`**, at the same rate
(`kernF_conn_le_of_lat`, `FlowCapstone.gapAt_gTransfer_of_abs_cluster`).

DERIVED: `0` is the excluded colour count and the lower end of `ρ`; `4` in `Fin 4` is the spacetime
dimension. -/
theorem flow_gapAt_of_latClusterRate (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving τ r) (m0 : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : LatClusterRate hN Φ τ r m0 ρ) :
    TransferGap.GapAt (flowTransfer hN Φ hB τ hpos m0) ρ := by
  unfold flowTransfer
  refine gapAt_gTransfer_of_abs_cluster _ _ _ _ _ _ _ _ _ hρ (fun P Q => ?_)
  obtain ⟨C, hC⟩ := h P Q
  refine ⟨C, fun n => ?_⟩
  rw [MarginMono.shift_iterate]
  exact kernF_conn_le_of_lat hN Φ hB τ m0 n P.1 Q.1 (hC n)

#print axioms flow_gapAt_of_latClusterRate

/-- **The reflected lattice function as a state value**: `latSF(θP ∪ Q) = νₖ(θX_P · X_Q)`, with
`X_P = prodSmear aₖ (Φₖ P)` (`latSF_pairFam`, `latSk_eq`, `latS_pairFam`).

DERIVED: `0` is the excluded colour count and the reflection plane; `4` in `Fin 4` is the spacetime
dimension. -/
theorem latSF_pair_eq (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (P Q : Mono N) :
    latSF hN Φ k (pairFam τ P Q)
      = stateK hN k (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (Φ.mono k P))
          * prodSmear (dySpacing N k) (Φ.mono k Q)) := by
  rw [latSF_pairFam, latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]

#print axioms latSF_pair_eq

/-- The smeared product of the empty monomial is `1`.

DERIVED: `0` is the number of factors; `1` the unit observable. -/
theorem prodSmear_empty (a : ℝ) : prodSmear a (emptyMono N) = 1 := by
  unfold prodSmear
  exact Finset.prod_of_isEmpty _

#print axioms prodSmear_empty

end Limit

/-! ## 3. Statement V and the gap -/

section V

/-- **The proved box** for a coupling and a potential family: `0 ≤ β ≤ 1/20` (`β_std ≤ 1/10`) and
local norm `≤ 1/16` at every extent.

DERIVED: `1/20` and `1/16` are `LocalPotentialSharp.potBox_localGap_sharp`'s box; `0` the sign. -/
def InBox (β : ℝ) (Fp : LocalPotFam 2) : Prop :=
  0 ≤ β ∧ β ≤ 1 / 20 ∧ ∀ M l, (Fp.P M).norm l ≤ 1 / 16

/-- Supports within two steps per coordinate.

DERIVED: `2` is the rank. -/
def HDiam (Fp : LocalPotFam 2) : Prop :=
  ∀ M X x y, x ∈ (Fp.P M).supp X → y ∈ (Fp.P M).supp X → Near2 (y.2 - x.2)

/-- **The box system at extent index `j + 299999`**: the potential patch system on the periodic lattice
of extent `2(j + 299999) + 2 ≥ 600000`.

DERIVED: `299999 = 300000 − 1`, the least extent index holding the box side `300000`; `2` the rank. -/
abbrev boxSys (β : ℝ) (Fp : LocalPotFam 2) (hdiam : HDiam Fp) (j : ℕ) : PatchSystem :=
  potSys β Fp hdiam (j + 299999) (by omega)

/-- **The per-level rate of V at level ratio `q`**: `coarseRate 5184 (7/100)^{1/q}`, written
`exp(log coarseRate / q)`.

DERIVED: `5184` the window count; `7/100` the global gap of the sharp box. -/
def vRate (q : ℕ) : ℝ := Real.exp (Real.log (coarseRate 5184 (7 / 100)) / q)

/-- DERIVED: `0` the sign. -/
theorem vRate_pos (q : ℕ) : 0 < vRate q := Real.exp_pos _

#print axioms vRate_pos

/-- DERIVED: `1` the bound; `0` the lower end of `q`; `5184`, `7/100` as in `vRate`. -/
theorem vRate_lt_one {q : ℕ} (hq : 0 < q) : vRate q < 1 := by
  have hl : Real.log (coarseRate 5184 (7 / 100)) < 0 :=
    Real.log_neg (coarseRate_pos _ _) (coarseRate_lt_one _ (by norm_num))
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  unfold vRate
  calc Real.exp (Real.log (coarseRate 5184 (7 / 100)) / q) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos hl hqr)
    _ = 1 := Real.exp_zero

#print axioms vRate_lt_one

/-- **Level `⌊n/q⌋` against rate per step**: `ρ^{⌊n/q⌋} ≤ ρ⁻¹ (ρ^{1/q})ⁿ` for `0 < ρ < 1`.

DERIVED: `1` the bound on `ρ` and the floor's slack; `0` the signs. -/
theorem pow_div_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ρ ^ (n / q) ≤ ρ⁻¹ * Real.exp (Real.log ρ / q) ^ n := by
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 : ρ ^ (n / q) = Real.exp (((n / q : ℕ) : ℝ) * Real.log ρ) := by
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  have e2 : ρ⁻¹ * Real.exp (Real.log ρ / q) ^ n = Real.exp (Real.log ρ * ((n : ℝ) / q - 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_log (inv_pos.mpr hρ0), Real.log_inv, ← Real.exp_add]
    congr 1
    ring
  have hm : (n : ℝ) / q ≤ ((n / q : ℕ) : ℝ) + 1 := by
    have h1 : q * (n / q) + n % q = n := Nat.div_add_mod n q
    have h2 : n % q < q := Nat.mod_lt n hq
    have h3 : (n : ℝ) < (q : ℝ) * (((n / q : ℕ) : ℝ) + 1) := by
      have : n < q * (n / q + 1) := by nlinarith
      exact_mod_cast this
    rw [div_le_iff₀ hqr]
    linarith
  rw [e1, e2]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonpos_left hm hl.le]

#print axioms pow_div_le

/-- **Statement V, pairing form** (the weakest form the gap consumes), for a flow of `SU(2)` at step `m₀`
and level ratio `q`. For every pair of margin monomials there are support bounds `a`, `b` and a
second-moment bound `M`, free in the fine step and in `n`, such that at every `n`, eventually in the
fine step `k`: some coupling and potential in the proved box (`InBox`, `HDiam`), some filter `𝒰` of
extent indices and two readers `f j`, `g j` on the box systems with, eventually in `𝒰`, supports of sizes
`≤ a`, `≤ b` at `obsNb` level `⌊n/q⌋` (`SeparatedPair`) and second moments `≤ M`, whose pairing and
two means converge along `𝒰` to the reflected lattice functions of `P` and `Q` shifted by `aₘ₀ n`.

DERIVED: `2` is the rank; `299999` the extent offset of `boxSys`; `4` in `Fin 4` is the spacetime
dimension. -/
def ObserverVPair (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 q : ℕ) : Prop :=
  ∀ P Q : MarginMono 2 τ r, ∃ (a b : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
    ∃ (β : ℝ) (Fp : LocalPotFam 2) (hdiam : HDiam Fp), InBox β Fp ∧
    ∃ (𝒰 : Filter ℕ) (f g : ∀ j : ℕ, (boxSys β Fp hdiam j).E), 𝒰.NeBot ∧
      (∀ᶠ j in 𝒰, SeparatedPair (boxSys β Fp hdiam j) (obsNb (2 * (j + 299999) + 1))
          (f j) (g j) (n / q) a b
        ∧ (boxSys β Fp hdiam j).B (f j) (f j) ≤ Mb ∧ (boxSys β Fp hdiam j).B (g j) (g j) ≤ Mb) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (f j) (g j)) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1)))) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (f j) (oneW (j + 299999))) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2)))) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (g j) (oneW (j + 299999))) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))))

/-- **V in pairing form gives lattice clustering at `vRate q`**, with constant
`max(M, 0) (b + (2/c) e^{c/2} a) / coarseRate` (`pot_cluster_rate` on each box, its bound passed to the
limit along `𝒰`; `pow_div_le`). The rate is the box's and the separation's alone: it does not see `M`.

DERIVED: `7/100` the sharp box's gap; `5184` the window count; `299999` the extent offset; `2` the
rank; `0` the lower end of `q`. -/
theorem latClusterRate_of_observerVPair {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 q : ℕ} (hq : 0 < q)
    (hV : ObserverVPair Φ τ r m0 q) : LatClusterRate two_ne Φ τ r m0 (vRate q) := by
  intro P Q
  obtain ⟨a, b, Mb, hPQ⟩ := hV P Q
  have hρ0 := coarseRate_pos 5184 (7 / 100)
  have hρ1 := coarseRate_lt_one 5184 (by norm_num : (0 : ℝ) < 7 / 100)
  have hK : 0 ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a) :=
    mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
    * (coarseRate 5184 (7 / 100))⁻¹, fun n => ?_⟩
  filter_upwards [hPQ n] with k hk
  obtain ⟨β, Fp, hdiam, ⟨hβ0, hβ, hν⟩, 𝒰, f, g, hU, hev, h1, h2, h3⟩ := hk
  haveI := hU
  refine le_of_tendsto ((h1.sub (h2.mul h3)).abs) ?_
  filter_upwards [hev] with j hj
  obtain ⟨hsep, hff, hgg⟩ := hj
  have hb := pot_cluster_rate hβ0 hβ Fp hν hdiam (j + 299999) (by omega) (f j) (g j) (n / q)
    hsep hff hgg
  calc _ ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
        * coarseRate 5184 (7 / 100) ^ (n / q) := hb
    _ ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
        * ((coarseRate 5184 (7 / 100))⁻¹ * vRate q ^ n) :=
        mul_le_mul_of_nonneg_left (pow_div_le hρ0 hρ1 hq n) hK
    _ = _ := by ring

#print axioms latClusterRate_of_observerVPair

/-- **The coarse law in the box at one fine step**: along the filter `𝒰` of extent indices, the box
Gibbs states of `Wilson(β) × e^{Fp}` converge, on every continuous observable `G`, to the law of the
coarse map `χ` under the step-`k` state: `wTorusState (potWeight β Fp) (2(j + 299999) + 1) G →
stateK k (G ∘ χ)`.

DERIVED: `2` is the rank; `299999` the extent offset; `1` the successor writing the extent. -/
def CoarseLawAt (k : ℕ) (β : ℝ) (Fp : LocalPotFam 2) (𝒰 : Filter ℕ) (χ : C(Cfg 2, Cfg 2)) : Prop :=
  ∀ G : C(Cfg 2, ℝ), Tendsto (fun j => wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) G) 𝒰
    (𝓝 (stateK two_ne k (G.comp χ)))

/-- **Statement V, law form**, for a flow of `SU(2)` at step `m₀` and level ratio `q`: at every large
fine step `k` one coarse map `χₖ`, one coupling and potential in the proved box, and one filter `𝒰ₖ`
with `CoarseLawAt` (the coarse view's law is a limit of box Gibbs states); and for every pair of margin
monomials support bounds `a`, `b` and a second-moment bound `M` such that at every `n`, eventually in
`k`, the reflected smeared product of `P` and the smeared product of `Q` shifted by `aₘ₀ n` are
`G_P ∘ χₖ`, `G_Q ∘ χₖ` for gauge-invariant coarse observables local on `S_P`, `S_Q` (`|S_P| ≤ a`,
`|S_Q| ≤ b`), with second moments `< M` under `stateK k`, and, on the large periodic lattices of `𝒰ₖ`,
every link of `S_Q` at `obsNb` level `⌊n/q⌋` from `S_P`.

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `4` in `Fin 4` is the
spacetime dimension. -/
def ObserverV (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 q : ℕ) : Prop :=
  ∃ (β : ℕ → ℝ) (Fp : ℕ → LocalPotFam 2) (hdiam : ∀ k, HDiam (Fp k)) (𝒰 : ℕ → Filter ℕ)
    (χ : ℕ → C(Cfg 2, Cfg 2)),
    (∀ᶠ k in atTop, InBox (β k) (Fp k) ∧ (𝒰 k).NeBot ∧ CoarseLawAt k (β k) (Fp k) (𝒰 k) (χ k)) ∧
    ∀ P Q : MarginMono 2 τ r, ∃ (a b : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
      ∃ (GP GQ : C(Cfg 2, ℝ)) (SP SQ : Finset ILink),
        IsIGaugeInvariant GP ∧ IsIGaugeInvariant GQ ∧ IsLocalOn SP ⇑GP ∧ IsLocalOn SQ ⇑GQ ∧
        SP.card ≤ a ∧ SQ.card ≤ b ∧
        LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1)) = GP.comp (χ k) ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1)) = GQ.comp (χ k) ∧
        stateK two_ne k (GP.comp (χ k) * GP.comp (χ k)) < Mb ∧
        stateK two_ne k (GQ.comp (χ k) * GQ.comp (χ k)) < Mb ∧
        ∀ᶠ j in 𝒰 k, ∀ l ∈ SQ.image (linkMod (2 * (j + 299999) + 1)),
          Far (obsNb (2 * (j + 299999) + 1)) (SP.image (linkMod (2 * (j + 299999) + 1))) (n / q) l

/-- **The law form of V gives the pairing form.** The readers are `G_P`, `G_Q` in the periodic
gauge-invariant observables (`periodicGaugeInv_of_isIGaugeInvariant`); their torus supports are the
images of `S_P`, `S_Q`, off which `hₗ` is null (`HeatBathLocal.readsNot_of_isLocalOn`, `pot_h_null`);
the pairing and means are the law at `G_P G_Q`, `G_P · 1`, `G_Q · 1` (`latSF_pair_eq`,
`prodSmear_empty`, `FlowCapstone.mono_empty`), and the second moments pass from the limit to the boxes
eventually along `𝒰`.

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `1` the unit
observable. -/
theorem observerVPair_of_observerV {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 q : ℕ}
    (hV : ObserverV Φ τ r m0 q) : ObserverVPair Φ τ r m0 q := by
  obtain ⟨β, Fp, hdiam, 𝒰, χ, hlaw, hread⟩ := hV
  intro P Q
  obtain ⟨a, b, Mb, h⟩ := hread P Q
  refine ⟨a, b, Mb, fun n => ?_⟩
  filter_upwards [hlaw, h n] with k hk hrk
  obtain ⟨hbox, hU, hL⟩ := hk
  obtain ⟨GP, GQ, SP, SQ, hgP, hgQ, hlP, hlQ, hcP, hcQ, hP, hQ, hmP, hmQ, hfar⟩ := hrk
  refine ⟨β k, Fp k, hdiam k, hbox, 𝒰 k,
    fun j => ⟨GP, periodicGaugeInv_of_isIGaugeInvariant (2 * (j + 299999) + 1) hgP⟩,
    fun j => ⟨GQ, periodicGaugeInv_of_isIGaugeInvariant (2 * (j + 299999) + 1) hgQ⟩, hU, ?_, ?_, ?_, ?_⟩
  · have hmP' : stateK two_ne k ((GP * GP).comp (χ k)) < Mb := by
      rw [ContinuousMap.mul_comp]; exact hmP
    have hmQ' : stateK two_ne k ((GQ * GQ).comp (χ k)) < Mb := by
      rw [ContinuousMap.mul_comp]; exact hmQ
    filter_upwards [hfar, (hL (GP * GP)).eventually (Iio_mem_nhds hmP'),
      (hL (GQ * GQ)).eventually (Iio_mem_nhds hmQ')] with j hj hj1 hj2
    have hA : ((SP.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1)))).card ≤ a :=
      Finset.card_image_le.trans hcP
    have hC : ((SQ.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1)))).card ≤ b :=
      Finset.card_image_le.trans hcQ
    refine ⟨⟨(SP.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1))),
      (SQ.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1))),
      hA, hC, fun l hl => ?_,
      fun l hl => ?_, hj⟩, le_of_lt hj1, le_of_lt hj2⟩
    · exact pot_h_null (β k) (Fp k) (hdiam k) (j + 299999) (by omega) l _
        (MassGap.HeatBathLocal.readsNot_of_isLocalOn hlP (j + 299999) l hl)
    · exact pot_h_null (β k) (Fp k) (hdiam k) (j + 299999) (by omega) l _
        (MassGap.HeatBathLocal.readsNot_of_isLocalOn hlQ (j + 299999) l hl)
  · have e : latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1))
        = stateK two_ne k ((GP * GQ).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ← hP, ← hQ]
    rw [e]
    exact hL (GP * GQ)
  · have e : latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2))
        = stateK two_ne k ((GP * 1).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hP, mono_empty,
        prodSmear_empty]
    rw [e]
    exact hL (GP * 1)
  · have e : latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))
        = stateK two_ne k ((GQ * 1).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hQ, mono_empty,
        prodSmear_empty, mul_comm]
      rfl
    rw [e]
    exact hL (GQ * 1)

#print axioms observerVPair_of_observerV

end V

/-! ## 4. The energy density -/

section Energy

/-- **V gives the gap of the energy density's transfer at step `m₀`**, at the explicit rate
`vRate q = coarseRate 5184 (7/100)^{1/q}`, under any proof `hB` of the uniform bound and a physical
range bound (`latClusterRate_of_observerVPair`, `flow_gapAt_of_latClusterRate`). The rate is free of
the `a⁻⁴` factor, which sits in the readers' second-moment bound.

DERIVED: `2` is the rank; `1/6` the dominance bound; `0` the lower end of `q`. -/
theorem energy_gapAt_of_observerVPair {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {q : ℕ} (hq : 0 < q)
    (hV : ObserverVPair (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q) :
    TransferGap.GapAt (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (vRate q) :=
  flow_gapAt_of_latClusterRate two_ne _ hB τ _ m0 (vRate_pos q).le
    (latClusterRate_of_observerVPair hq hV)

#print axioms energy_gapAt_of_observerVPair

/-- **V (law form) gives the gap of the energy density's transfer at step `m₀`** at `vRate q`
(`observerVPair_of_observerV`, `energy_gapAt_of_observerVPair`).

DERIVED: `2` is the rank; `1/6` the dominance bound; `0` the lower end of `q`. -/
theorem energy_gapAt_of_observerV {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {q : ℕ} (hq : 0 < q)
    (hV : ObserverV (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q) :
    TransferGap.GapAt (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (vRate q) :=
  energy_gapAt_of_observerVPair hc0 hc n R D hD s hs hB τ hphys m0 hq
    (observerVPair_of_observerV hV)

#print axioms energy_gapAt_of_observerV

/-- **V gives M for the energy density**: `FlowClusterAbs` at every window `L > 0`
(`ObserverEnergyM.energy_M_iff_gap` at step `m₀`, `energy_gapAt_of_observerV`).

DERIVED: `2` is the rank; `1/6` the dominance bound; `0` the lower end of `q` and `L`. -/
theorem energy_M_of_observerV {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ) {q : ℕ} (hq : 0 < q)
    (hV : ObserverV (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q) {L : ℝ} (hL : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hL).mpr
    ⟨vRate q, vRate_pos q, vRate_lt_one hq,
      energy_gapAt_of_observerV hc0 hc n R D hD s hs hB τ hphys m0 hq hV⟩

#print axioms energy_M_of_observerV

/-- **The continuum statement from V.** The smeared moments on `D` (E), V at one step `m₀` (M) and
`FlowConnectedNonzero` (N) give, at every dyadic step, the energy density's transfer gapped at a
physical rate `c'/L` and a non-zero vector orthogonal to the vacuum
(`ObserverEnergyM.energy_clay_of_gap` at the rate `vRate q`).

DERIVED: `2` is the rank and the moment's degree; `1/6` the dominance bound; `0` the lower end of `q`
and `L`. -/
theorem energy_clay_of_observerV {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k (smear (dySpacing 2 k)
        ((obsEnergyOn c hc0 hc n R D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    {q : ℕ} (hq : 0 < q) (hV : ObserverV (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q)
    {L : ℝ} (hL : 0 < L) (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) :=
  energy_clay_of_gap hc0 hc n R D hD s hs hM τ hphys m0 hL (vRate_pos q) (vRate_lt_one hq)
    (energy_gapAt_of_observerV hc0 hc n R D hD s hs _ τ hphys m0 hq hV) hNT

#print axioms energy_clay_of_observerV

end Energy

end MassGap.ObserverEnergyV
