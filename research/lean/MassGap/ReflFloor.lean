import Mathlib
import MassGap.TorusDecay
import MassGap.ReadPos
import MassGap.TowerParamFree

/-!
# MassGap.ReflFloor — the window floor at a fixed level fails near `0⁺`: the residual of the floor root is refuted by the bridge

`ReadPos.clayStatement_of_strongEnd_floor` takes `StrongEnd N` and, frequently as `u₀ → 0⁺`, along every coupling
tower at window coupling `u₀`, `ReadPos.ReflFloorAt N βs (2 log 2) ∧ ExistAlong N βs`. This module proves that the
second hypothesis is false whenever the first holds. That capstone is therefore vacuous as stated: its
hypotheses are jointly inconsistent. Declarations are in the namespace `MassGap.ReflFloor`.

## (R) in plain mathematics

At step `k` of a tower (`βs k → ∞`, window side `2^k`, torus doubling defect `D(βs k, k) = u₀`), let
`X = E 0 − ν(E 0)` with `E 0 = P₀₁(0) − P₂₃(0)` (time-space minus space-space plaquette density at the origin),
`ν = ` the infinite-volume periodic Wilson state at `βs k`, `θ` the site reflection about `x₀ = 0`, and
`g(m) = ν(θX · T_{2m e₀} X)`. (R) says, eventually in `k`:

* window floor: some `m₁ ≥ 1` has `g(0) e^{−2 m₁ U / 2^k} ≤ g(m₁)`, `U = 2 log 2`;
* defect bound: some `c < 1` has `|Cov_ν(P₀₁(−e₀) − P₀₁(0), E(2m e₀))| ≤ c |g(m)|` for all large `m`.

Through log-convexity and the split `g = diag + defect` (`BandClose`) the two give `m′(βs k) ≤ U/2^k`, the
measured tensor mass at most `U` per window (`BandUpper.WindowUpper`).

## The refutation (proved)

The proved lower half of the band reads the doubling recursion at one depth: a defect `≤ 1/1000` at side `n`
gives the ratio `½` at lag `n` (`TorusDecay.dyadic_torus_decay`), so the rate `log 2` per window. The recursion
gives more at a smaller defect: `250 Δ(0) ≤ t ≤ 1/4` gives `250 Δ(k) ≤ t^{2^k}` (`iterate_seed`), and at
`t = (1/2)^{2^i}` the excited weight of the torus is at most `(1/2)^{2^{k+i}}` (`excited_le_deep`). That is the
hypothesis of `KernelGap.gap_of_excited` at depth `k + i` and lag `n / 2^i`, so the ratio `½` holds at lag
`n/2^i` (`torus_decay_deep`) and the transfer gap at window `w` has rate `2^i log 2 / 2^w`
(`windowGap_deep`). The proved `GapReadsTensorProved.gapReadsTensor` turns it into the measured tensor mass:

* `mass_floor_deep`: a coupling tower at `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, has `2^i log 2 / 2^k ≤ m′(βs k)`
  eventually.
* `not_windowUpper`, `not_reflFloorAt`: such a tower has neither `WindowUpper N βs U` nor `ReflFloorAt N βs U`
  for any `U < 2^i log 2`.
* `eventually_not_reflFloorAt`: for every real `U`, eventually as `u₀ → 0⁺`, no coupling tower at `u₀` has
  `ReflFloorAt N βs U`.
* `not_floor_residual`: `StrongEnd N` refutes the residual of `ReadPos.clayStatement_of_strongEnd_floor` at every
  level `U`, and `not_upper_residual` refutes the residual of `BandUpper.clayStatement_of_strongEnd_upper`.
* `headline_hypotheses_inconsistent`: `StrongEnd N` and the floor residual at `U = 2 log 2` give `False`.

So the window reading `2^k m′` of a tower is not pinned at `log 2`: it grows at least like `log(1/(250 u₀))` up
to the dyadic rounding, and a fixed upper level `U` is exceeded at every small enough `u₀`. The band of
`MeasuredTower.MeasTowerG` is not refuted: its level `L` is existential per tower, and
`OneInput.clayStatement_of_strongEnd` (residual `MeasTowerG ∧ ExistAlong`) is untouched.

## Tests

* Free (Gaussian) theory: not a model here. `PhotonStall.photon_not_strongEnd` shows the abelian Gaussian chain
  has no tower near `0⁺`, so there the residual is vacuous; the refutation uses only facts proved at `SU(N)`.
* Strong coupling: towers have `βs k → ∞`, so strong coupling is off every tower; the window floor and the
  defect bound are read only along towers. Nothing in this module decides either at small `β`.
* The defect bound alone (`FloorFold.DefectAt`) is not refuted: the refutation passes through the window floor,
  which with the defect bound gives `WindowUpper`; with `c < 1` and no floor nothing contradicts the mass floor.

## What does not follow

* No part of (R) is proved. What is proved is its negation near `0⁺`, at every fixed level `U`.
* `MeasTowerG` along towers, `ExistAlong`, and `StrongEnd N` itself: untouched.
* The window floor at a level that grows with `log(1/u₀)`: not stated or refuted here. A level `U(u₀)` with
  `U(u₀) ≥ 2^i log 2` at `u₀ ≤ (1/2)^{2^i}/250` escapes `not_reflFloorAt`; whether the mass then sits in a band of
  ratio `2` is `MeasTowerG`, the residual of `OneInput.clayStatement_of_strongEnd`.
* The defect bound: neither proved nor refuted. The exact inequality stays
  `∃ c < 1, ∀ᶠ m, |C(2m+1) − C(2m)| ≤ c |g(m)|`, `C(n) = Cov_ν(P₀₁(0), E(n e₀))`.

DERIVED (module-wide): `0` the plane, the time axis, the contact gap and the signs; `1` the least depth, the unit
step and the group unit; `2` the doubling, the base of the window and of the ratio `½`, the half-length of the
torus and the two lattice steps of one reflected gap; `4` in `1/4` the squaring threshold of
`DoublingSharp.iterate_sharp`; `8` in `8 p ≤ Δ` (`DoublingRecursion.p_le_Δ`), inherited. Inherited, not derived
here: `250` the squaring constant and `1/1000` the seed of `DoublingSharp.rec_sharp`; `100` and `1/8` of
`ChainDecay.chain_decay`; `log 2` the rate of one halving.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace MassGap.ReflFloor

open Filter Topology

/-! ## 1. The doubling recursion at depth -/

section Doubling

open MassGap.DoublingRecursion MassGap.DoublingPower MassGap.DoublingSharp

variable {x : Pt → ℝ}

/-- **The squaring recursion from any seed below `1/4`**: `250 Δ(0) ≤ t ≤ 1/4` gives `250 Δ(k) ≤ t^{2^k}`.
`DoublingSharp.iterate_sharp` is the case `t = 1/4`. DERIVED: `4` the squaring threshold; `2` the square.
Inherited: `250`, `1/1000` of `DoublingSharp.rec_sharp`. -/
theorem iterate_seed (hx : PositiveS x) (hp : Positive x) {t : ℝ} (ht : t ≤ 1 / 4)
    (h0 : 250 * Δ x (corner 0) ≤ t) : ∀ k, 250 * Δ x (corner k) ≤ t ^ (2 ^ k) := by
  have ht0 : 0 ≤ t := le_trans (by have := Δ_nonneg hp (corner 0); positivity) h0
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hk0 := Δ_nonneg hp (corner k)
    have hq : t ^ (2 ^ k) ≤ t := by
      have := pow_le_pow_of_le_one ht0 (by linarith) (Nat.one_le_two_pow (n := k))
      simpa using this
    have hsmall : Δ x (corner k) ≤ 1 / 1000 := by linarith
    have hr := rec_sharp hx (corner k) hsmall
    rw [corner_succ]
    have hsq : (250 * Δ x (corner k)) ^ 2 ≤ (t ^ (2 ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    have : (t ^ (2 ^ k)) ^ 2 = t ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    nlinarith

/-- **The excited weight at corner `k` from a deep seed**: `250 Δ(0) ≤ (1/2)^{2^i}`, `i ≥ 1`, gives
`s ≤ (1/2)^{2^{k+i}}`. DERIVED: `1` the least depth; `2` the base of the ratio. Inherited: `250`, `8` of
`DoublingRecursion.p_le_Δ`, `2` and `1/4` of `DoublingPower.excited_le_two_defect`. -/
theorem excited_le_deep (hx : PositiveS x) (hp : Positive x) {i : ℕ} (hi : 1 ≤ i)
    (h0 : 250 * Δ x (corner 0) ≤ (1 / 2 : ℝ) ^ (2 ^ i)) (k : ℕ) {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}
    (h : PowerFacts a lam s m) (h1 : x (corner k) = Real.log (a m))
    (h2 : x (corner k + E 0) = Real.log (a (2 * m))) :
    s ≤ (1 / 2 : ℝ) ^ (2 ^ (k + i)) := by
  have ht : (1 / 2 : ℝ) ^ (2 ^ i) ≤ 1 / 4 := by
    have h2i : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    calc (1 / 2 : ℝ) ^ (2 ^ i) ≤ (1 / 2) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) h2i
      _ = 1 / 4 := by norm_num
  have hit := iterate_seed hx hp ht h0 k
  have he : ((1 / 2 : ℝ) ^ (2 ^ i)) ^ (2 ^ k) = (1 / 2) ^ (2 ^ (k + i)) := by
    rw [← pow_mul, ← pow_add, Nat.add_comm i k]
  rw [he] at hit
  have hpd : p x 0 (corner k) = defect a m := by rw [p, h1, h2]; rfl
  have h8 := p_le_Δ hp (corner k)
  have hq1 : (1 / 2 : ℝ) ^ (2 ^ (k + i)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ (k + i)) := by positivity
  have hd : defect a m ≤ 1 / 4 := by rw [← hpd]; nlinarith
  have := excited_le_two_defect h hd
  rw [← hpd] at this
  nlinarith

end Doubling

/-! ## 2. The torus decay at lag `n / 2^i` -/

section Torus

open MeasureTheory Real MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower
  MassGap.HiddenChain MassGap.ChainClosing MassGap.ChainReduce MassGap.ChainDecay
  MassGap.TorusChain MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.DoublingPower
  MassGap.SlabKernelOperator MassGap.TorusDecay

variable {N : ℕ}

/-- **The finite-volume decay at lag `2^{b−i}` from a deep seed.** At `β ≥ 0`, side `n = 2^b`, depth
`1 ≤ i < b` and `16 log ZR(n⁴) − log ZR((2n)⁴) ≤ (1/2)^{2^i}/250`, every gauge-invariant half-space observable `x`
and every `ε > 0` have, eventually along `periodicUltra`, `torusConn x (2^{b−i}) ≤ ½ torusConn x 0 + ε`.
`TorusDecay.dyadic_torus_decay` is the lag `n` at the seed `1/1000`; the proof is the same with
`KernelGap.gap_of_excited` at depth `k + i`. DERIVED: `1` the least depth; `2` the doubling, the half-length and
the base of the ratio; `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus. Inherited: `250` the
squaring constant; `100`, `1/8` of `ChainDecay.chain_decay`. -/
theorem torus_decay_deep (hN : N ≠ 0) (β : ℝ) (hβ : 0 ≤ β) {b i : ℕ} (hi : 1 ≤ i) (hib : i + 1 ≤ b)
    (hseed : 16 * Real.log (RectWilson.ZR (fun _ => 2 ^ b) N β)
      - Real.log (RectWilson.ZR (fun _ => 2 * 2 ^ b) N β) ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250)
    (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))
    (hx : x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := SUN.SU N) 0 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ),
      PeriodicReduce.torusConn 0 0 hN β j x (2 ^ (b - i))
        ≤ 1 / 2 * PeriodicReduce.torusConn 0 0 hN β j x 0 + ε := by
  set n := 2 ^ b with hndef
  set d := 2 ^ (b - i) with hddef
  have hn2 : 2 ≤ n := by
    rw [hndef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd2 : 2 ≤ d := by
    rw [hddef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdn : d ≤ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hde : Even d := by
    refine ⟨2 ^ (b - i - 1), ?_⟩
    rw [hddef, ← two_mul, ← pow_succ']
    congr 1; omega
  have hdq : ∀ k : ℕ, 2 ^ (k + i) * d = 2 ^ k * n := fun k => by
    rw [hddef, hndef, ← pow_add, ← pow_add]
    congr 1; omega
  -- the window of `x`
  have hxh : x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SUN.SU N) 0 0 := (Submodule.mem_inf.mp hx).1
  obtain ⟨R0, hR0⟩ := winLocal_of_mem hxh
  set R := 2 * R0 with hRdef
  have hRw : WinLocal R x := hR0.mono (by omega)
  have hRe : Even R := ⟨R0, by omega⟩
  obtain ⟨C, hC⟩ := InfiniteLattice.bounded_of_continuous x.continuous
  set B := max C 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hCB : ∀ U, |x U| ≤ B := fun U => (hC U).trans (le_max_left _ _)
  -- the doubling recursion
  have he : Even n := ⟨2 ^ (b - 1), by rw [hndef, ← two_mul, ← pow_succ']; congr 1; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, n = 2 ^ (a + 1) := ⟨b - 1, by rw [hndef]; congr 1; omega⟩
  have hfr := factRep hN hβ hn2 he
  have hp := positive_of_facts hfr
  have hxS := DoublingSharp.positiveS_of_facts hfr
  have hΔ : 250 * Δ (xW N n β) (corner 0) ≤ (1 / 2 : ℝ) ^ (2 ^ i) := by
    rw [Δ_corner0]; linarith
  -- the dyadic depth needed for `ε`
  set δ : ℝ := min (1 / 8) ((ε / (100 * B ^ 2)) ^ 2 / 2) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨K0, hK0⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  set J0 := 2 ^ (K0 + 2) * n + R + R + n with hJ0
  filter_upwards [PeriodicDyadic.periodicUltra_seed_mem hN β a,
    (PeriodicState.periodicUltra_le hN β) (eventually_ge_atTop J0)] with j hjk hjJ
  obtain ⟨k, hk⟩ := hjk
  rw [← ha] at hk
  -- the depth `k` is large
  have hkK : K0 + 2 ≤ k := by
    by_contra hlt
    have h1 : 2 ^ k ≤ 2 ^ (K0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ k * n ≤ 2 ^ (K0 + 1) * n := Nat.mul_le_mul_right n h1
    have h3 : 2 ^ (K0 + 2) * n = 2 * (2 ^ (K0 + 1) * n) := by rw [pow_succ]; ring
    omega
  have hhe : Even (j + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = 4 * t := ⟨2 ^ (k - 2), by
      rw [show k = (k - 2) + 2 by omega, pow_add]; norm_num; ring⟩
    rw [ht] at hk
    exact ⟨t * n, by nlinarith⟩
  have hwin : R + n + R ≤ j + 1 := by
    have : n ≤ 2 ^ (K0 + 2) * n := Nat.le_mul_of_pos_left n (Nat.two_pow_pos _)
    omega
  have hwind : R + d + R ≤ j + 1 := by omega
  have hkn : 2 ^ (k + i) * d / 2 = j + 1 := by rw [hdq k]; omega
  -- the transfer kernel of this torus
  set M := 2 * j + 1 with hMdef
  have hSt := step_wt (M := M) hN hβ
  have hkc : Continuous (Function.uncurry (kern (hA 0 (Tc M) N) (wt M N β))) := by
    rw [kern_wt]; exact continuous_kT β
  have hkb := abs_kern_le (ν := hA 0 (Tc M) N) hSt.le_one
  have hks : ∀ y z : Sl M N, kern (hA 0 (Tc M) N) (wt M N β) y z
      = kern (hA 0 (Tc M) N) (wt M N β) z y := by
    rw [kern_wt]; exact kT_symm β
  have hpos : 0 < ‖kernelCLM (kern (hA 0 (Tc M) N) (wt M N β)) 1 (KernelEigen.kmeas hkc)
      zero_le_one hkb (hS 0 (Tc M) N) (hS 0 (Tc M) N)‖ := by
    refine norm_pos_iff.mpr (kernelCLM_ne_zero _ _ _ _ _ _ _ (kTmin_pos (μ := 0) (T := Tc M) β)
      (fun y z => ?_))
    rw [kern_wt]; exact kT_lower hN hβ y z
  obtain ⟨φ, hφm, ⟨Bφ, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hS 0 (Tc M) N) hkc zero_le_one hkb hks hpos
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith
  have hpf := powerFacts (μ := hS 0 (Tc M) N) (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb
    hφ1 heig hc hc0 (j + 1) (by omega)
  obtain ⟨h1, h2⟩ := xW_corner hN hβ hn2 he hk
  have hexc := excited_le_deep hxS hp hi hΔ k hpf h1 h2
  have hgap := KernelGap.gap_of_excited (KernelEigen.kmeas hkc) zero_le_one hkb hks hφm hφb hφ1
    heig hc hc0 (k + i) d (by omega) hde (by rw [hkn]; exact hexc)
  -- the excited weight of the torus
  set s := KernelPower.excited (hS 0 (Tc M) N) (kern (hA 0 (Tc M) N) (wt M N β)) c φ (j + 1) with hsdef'
  have hlp : 0 < |c| := abs_pos.mpr hc0
  have hs0 : 0 ≤ s := div_nonneg (hs_nonneg _) (by positivity)
  have hsk : s ≤ (1 / 2) ^ K0 := by
    refine hexc.trans ?_
    have : K0 ≤ 2 ^ (k + i) := by
      have h1 := Nat.lt_two_pow_self (n := k)
      have h2 : 2 ^ k ≤ 2 ^ (k + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) this
  have hsδ : s ≤ δ := (hsk.trans hK0.le)
  have hs8 : s ≤ 1 / 8 := hsδ.trans (min_le_left _ _)
  have hsdef : hs (hS 0 (Tc M) N) (iter (hS 0 (Tc M) N)
      (rem (kern (hA 0 (Tc M) N) (wt M N β)) c φ) j) = s * |c| ^ (2 * (j + 1)) := by
    rw [hsdef']; unfold KernelPower.excited
    rw [show j + 1 - 1 = j by omega]; field_simp
  have hη : 100 * B ^ 2 * Real.sqrt (2 * s) ≤ ε := by
    have hB2 : 0 < 100 * B ^ 2 := by positivity
    have h2s : 2 * s ≤ (ε / (100 * B ^ 2)) ^ 2 := by
      have := hsδ.trans (min_le_right _ _); linarith
    have := Real.sqrt_le_sqrt h2s
    rw [Real.sqrt_sq (by positivity)] at this
    calc 100 * B ^ 2 * Real.sqrt (2 * s) ≤ 100 * B ^ 2 * (ε / (100 * B ^ 2)) :=
          mul_le_mul_of_nonneg_left this hB2.le
      _ = ε := by field_simp
  -- the observables as window insertions
  set θx := (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R]
    (LatticeReflection.ireflObs 0 0 x) with hθx
  have hW1 : WinLocal R θx := winLocal_refl hRw
  have hWs : ∀ e, WinLocal (R + e) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[e] x) :=
    fun e => winLocal_shift hRw e
  set F₁ : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ := winF θx with hF₁def
  set F₂ : (ℕ → Sl M N) → (ℕ → Ax M N) → ℝ := winF x with hF₂def
  have hrev : ∀ V A, F₁ V A = F₂ (revX R V) (revY (invA (M := M) (N := N)) R A) :=
    fun V A => winF_refl hRw V A
  have iF₁ : Ins F₁ B := ⟨measurable_winF θx, fun V A => by rw [hrev]; exact hCB _⟩
  have iF₂ : Ins F₂ B := ⟨measurable_winF x, fun V A => hCB _⟩
  have l₁ : LocalUpTo R F₁ := localUpTo_winF hW1
  have l₂ : LocalUpTo R F₂ := localUpTo_winF hRw
  have hshiftF : ∀ e, winF (M := M) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[e] x)
      = fun V A => F₂ (sshift V e) (sshift A e) := fun e => by
    funext V A; exact winF_shift hRw e V A
  -- the torus expectations as closed chains
  have T1 : PeriodicState.torusState hN M β (LatticeReflection.ireflObs 0 0 x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M F₁ := by
    rw [← torusState_iterS hN M β R, torusState_Eh hN hβ hW1 (by omega)]
  have T2 : ∀ e, R + (R + e) ≤ M → PeriodicState.torusState hN M β
      ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[e] x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
          (fun V A => F₂ (sshift V (R + e)) (sshift A (R + e))) := by
    intro e he'
    rw [← torusState_iterS hN M β R, ← Function.iterate_add_apply,
      torusState_Eh hN hβ (hWs (R + e)) he', hshiftF]
  have T3 : ∀ e, R + (R + e) ≤ M → PeriodicState.torusState hN M β
      (LatticeReflection.ireflObs 0 0 x
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[e] x)
      = Eh (hS 0 (Tc M) N) (hA 0 (Tc M) N) (wt M N β) M
          (fun V A => F₁ V A * F₂ (sshift V (R + e)) (sshift A (R + e))) := by
    intro e he'
    rw [← torusState_iterS hN M β R, iterS_mul, ← Function.iterate_add_apply,
      torusState_Eh hN hβ ((hW1.mono (by omega : R ≤ R + (R + e))).mul (hWs (R + e))) he']
    congr 1; funext V A
    show F₁ V A * winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[R + e] x) V A = _
    rw [hshiftF]
  have hθ : LatticeReflection.ireflObs (G := SUN.SU N) 0 (2 * (0 : ℤ))
      = LatticeReflection.ireflObs 0 0 := by norm_num
  have key := chain_decay hSt (invA (M := M) (N := N)) mp_invA invA_invA
    (fun V A V' => wt_symm β V A V') hφm hφb hφ1 heig hc0 j hs0 hs8 hsdef hhe
    (L := M) (by omega) hde hc hgap hRe hwind iF₁ iF₂ l₁ l₂ hrev
  unfold PeriodicReduce.torusConn
  rw [hθ, T3 d (by omega), T1, T2 d (by omega), T3 0 (by omega), T2 0 (by omega),
    Nat.add_comm R d, Nat.add_zero]
  linarith

end Torus

/-! ## 3. The window gap and the mass floor at depth -/

section Gap

open MassGap.CouplingTower (StrongEnd CouplingTower windowCoupling)
open MassGap.ConstantPhysicsLine (ExistAlong)
open MassGap.MeasuredSpacing (mU)

variable {N : ℕ}

/-- **The window gap at depth `i`**: a window `w ≥ i + 1` with `D(β, w) ≤ (1/2)^{2^i}/250` gives the periodic
transfer gap and the periodic Clay gap at rate `r` with `−log r = log 2 / 2^{w−i}`. `CouplingTower.windowGap` is
the rate `log 2 / 2^w` at the seed `1/1000`. DERIVED: `1` the least depth; `2` the base. Inherited: `250`. -/
theorem windowGap_deep (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {i w : ℕ} (hi : 1 ≤ i)
    (hw : i + 1 ≤ w) (hs : windowCoupling N β w ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ TransferGap.GapAt (PeriodicState.periodicGaugeInvData 0 0 hN β) r ∧
      PeriodicContent.PeriodicClayGapAt 0 0 hN β r ∧ -Real.log r = Real.log 2 / 2 ^ (w - i) := by
  have hm : 2 ^ (w - i) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hq1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hdec := torus_decay_deep hN β hβ hi hw hs
  have hlag := WeakCouplingWindow.torusLagClear_stepRate 0 0 hN β hq0.le hm hdec
  have hr0 := WeakCouplingWindow.stepRate_pos hq0 (2 ^ (w - i))
  have hr1 := WeakCouplingWindow.stepRate_lt_one hq0.le hq1 hm
  have hg := (WeakCouplingWindow.torusLagClear_iff_gapAt 0 0 hN hβ hm hr0.le).mp hlag
  refine ⟨_, hr0, hr1, hg, GapStep.periodic_clayGapAt_of_gapAt 0 0 hN2 hN hβ hr0 hr1 hg, ?_⟩
  rw [WeakCouplingWindow.neg_log_stepRate hq0, one_div (2 : ℝ), Real.log_inv, neg_neg]
  push_cast
  rfl

/-- **The measured tensor mass at depth `i`**: at `β ≥ 0`, a window `w ≥ i + 1` with
`D(β, w) ≤ (1/2)^{2^i}/250` has `2^i log 2 / 2^w ≤ m′(β)`. DERIVED: `1` the least depth; `2` the base.
Inherited: `250`. -/
theorem mass_ge_deep [NeZero N] (hN2 : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {i w : ℕ} (hi : 1 ≤ i)
    (hw : i + 1 ≤ w) (hs : windowCoupling N β w ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) :
    ENNReal.ofReal (2 ^ i * Real.log 2 / 2 ^ w) ≤ mU (NeZero.ne N) β := by
  obtain ⟨r, -, -, -, hcl, hr⟩ := windowGap_deep hN2 (NeZero.ne N) hβ hi hw hs
  have h := GapReadsTensorProved.gapReadsTensor (N := N) β hβ r hcl
  have e : 2 ^ i * Real.log 2 / 2 ^ w = -Real.log r := by
    rw [hr]
    have hp : (2 : ℝ) ^ w = 2 ^ i * 2 ^ (w - i) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]
    field_simp
  rw [e]
  exact h

/-- **The mass floor along a tower at depth `i`**: a coupling tower at `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, has
`2^i log 2 / 2^k ≤ m′(βs k)` eventually. At `i = 1` this is twice the rate of `FinalBridge.windowReading_floor`, at
the smaller seed `1/1000`. DERIVED: `1` the least depth; `2` the base. Inherited: `250`. -/
theorem mass_floor_deep [NeZero N] (hN2 : 2 ≤ N) {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id) :
    ∀ᶠ k in atTop, ENNReal.ofReal (2 ^ i * Real.log 2 / 2 ^ k) ≤ mU (NeZero.ne N) (βs k) := by
  filter_upwards [hT.2.2, eventually_ge_atTop (i + 1)] with k ⟨_, hβ, hg⟩ hk
  have hg' : windowCoupling N (βs k) k = u₀ := hg
  exact mass_ge_deep hN2 hβ hi hk (by rw [hg']; exact hu)

/-- **No window upper bound below the deep floor**: a coupling tower at `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, has no
`WindowUpper N βs U` at any `U < 2^i log 2`. DERIVED: `1` the least depth; `2` the base; `0` the sign. Inherited: `250`
the squaring constant of `DoublingSharp.rec_sharp`. -/
theorem not_windowUpper [NeZero N] (hN2 : 2 ≤ N) {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    {U : ℝ} (hU : U < 2 ^ i * Real.log 2) : ¬ BandUpper.WindowUpper N βs U := by
  intro hW
  obtain ⟨k, hlo, hhi⟩ := ((mass_floor_deep hN2 hi hu hT).and hW).exists
  have h := hlo.trans hhi
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hpos : 0 < 2 ^ i * Real.log 2 / 2 ^ k := by
    have := Real.log_pos one_lt_two; positivity
  rcases (ENNReal.ofReal_le_ofReal_iff' (q := U / 2 ^ k)).mp h with h' | h'
  · rw [div_le_div_iff_of_pos_right hp] at h'
    linarith
  · linarith

/-- **No floor residual below the deep floor**: a coupling tower at `u₀ ≤ (1/2)^{2^i}/250`, `i ≥ 1`, has no
`ReadPos.ReflFloorAt N βs U` at any `U < 2^i log 2`: the floor and the defect bound would give `WindowUpper`.
DERIVED: `1` the least depth; `2` the base. Inherited: `250` the squaring constant of
`DoublingSharp.rec_sharp`. -/
theorem not_reflFloorAt [NeZero N] [Fact (2 ≤ N)] {u₀ : ℝ} {i : ℕ} (hi : 1 ≤ i)
    (hu : u₀ ≤ (1 / 2 : ℝ) ^ (2 ^ i) / 250) {βs : ℕ → ℝ} (hT : CouplingTower N u₀ βs id)
    {U : ℝ} (hU : U < 2 ^ i * Real.log 2) : ¬ ReadPos.ReflFloorAt N βs U := fun h =>
  not_windowUpper (Fact.out : 2 ≤ N) hi hu hT hU
    (BandClose.windowUpper_of_defect
      (ReadPos.reflReadsAt_of_floor (hT.2.2.mono fun _ hk => hk.2.1) h))

/-- Every real level lies below `2^i log 2` at some depth `i ≥ 1`. DERIVED: `1` the least depth and the shift;
`2` the base. -/
theorem exists_depth (U : ℝ) : ∃ i : ℕ, 1 ≤ i ∧ U < 2 ^ i * Real.log 2 := by
  have hl := Real.log_pos one_lt_two
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (U / Real.log 2) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨i + 1, by omega, ?_⟩
  have h1 : (2 : ℝ) ^ i ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_lt_iff₀ hl] at hi
  nlinarith

/-- **At every fixed level the floor fails near `0⁺`**: for every real `U`, eventually as `u₀ → 0⁺`, no coupling
tower at `u₀` has `ReadPos.ReflFloorAt N βs U`. DERIVED: `0` the limit `0⁺`; `2` the base. Inherited: `250`. -/
theorem eventually_not_reflFloorAt [NeZero N] [Fact (2 ≤ N)] (U : ℝ) :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ¬ ReadPos.ReflFloorAt N βs U := by
  obtain ⟨i, hi, hU⟩ := exists_depth U
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 ^ i) / 250 := by positivity
  filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds hpos)] with u hu βs hT
  exact not_reflFloorAt hi hu hT hU

/-- **The same for the window upper bound.** DERIVED: `0` the limit `0⁺`; `2` the base. Inherited: `250`. -/
theorem eventually_not_windowUpper [NeZero N] [Fact (2 ≤ N)] (U : ℝ) :
    ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ¬ BandUpper.WindowUpper N βs U := by
  obtain ⟨i, hi, hU⟩ := exists_depth U
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 ^ i) / 250 := by positivity
  filter_upwards [nhdsWithin_le_nhds (Iic_mem_nhds hpos)] with u hu βs hT
  exact not_windowUpper (Fact.out : 2 ≤ N) hi hu hT hU

/-- **The bridge refutes the floor residual at every level**: under `StrongEnd N`, for every real `U`, it is not
the case that frequently as `u₀ → 0⁺` every coupling tower at `u₀` has `ReadPos.ReflFloorAt N βs U`. The towers
exist near `0⁺` (`TowerParamFree.vanishing_iff_towers`). DERIVED: `0` the limit `0⁺`. -/
theorem not_floor_residual [NeZero N] [Fact (2 ≤ N)] (hS : StrongEnd N) (U : ℝ) :
    ¬ ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ReadPos.ReflFloorAt N βs U := by
  intro hR
  have htow : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
    (TowerParamFree.vanishing_iff_towers (Fact.out : 2 ≤ N)).mp
      ((StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mp hS)
  obtain ⟨u, ⟨hRu, βs, hT⟩, hno⟩ :=
    ((hR.and_eventually htow).and_eventually (eventually_not_reflFloorAt (N := N) U)).exists
  exact hno βs hT (hRu βs hT)

/-- **The bridge refutes the upper residual at every level**: the same for `BandUpper.WindowUpper`, the residual of
`BandUpper.clayStatement_of_strongEnd_upper`. DERIVED: `0` the limit `0⁺`. -/
theorem not_upper_residual [NeZero N] [Fact (2 ≤ N)] (hS : StrongEnd N) (U : ℝ) :
    ¬ ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → BandUpper.WindowUpper N βs U := by
  intro hR
  have htow : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∃ βs : ℕ → ℝ, CouplingTower N u₀ βs id :=
    (TowerParamFree.vanishing_iff_towers (Fact.out : 2 ≤ N)).mp
      ((StrongEndVanishing.strongEnd_iff_vanishing (NeZero.ne N)).mp hS)
  obtain ⟨u, ⟨hRu, βs, hT⟩, hno⟩ :=
    ((hR.and_eventually htow).and_eventually (eventually_not_windowUpper (N := N) U)).exists
  exact hno βs hT (hRu βs hT)

/-- **The hypotheses of `ReadPos.clayStatement_of_strongEnd_floor` are inconsistent**: `StrongEnd N` and its
residual `ReflFloorAt N βs (2 log 2) ∧ ExistAlong N βs` (frequently near `0⁺`, along every tower) give `False`.
DERIVED: `2` the band ratio. Inherited: `log 2` the window rate. -/
theorem headline_hypotheses_inconsistent [NeZero N] [Fact (2 ≤ N)] (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReadPos.ReflFloorAt N βs (2 * Real.log 2) ∧ ExistAlong N βs) : False :=
  not_floor_residual hS (2 * Real.log 2) (hR.mono fun _ h βs hT => (h βs hT).1)

end Gap

end MassGap.ReflFloor

end

#print axioms MassGap.ReflFloor.iterate_seed
#print axioms MassGap.ReflFloor.excited_le_deep
#print axioms MassGap.ReflFloor.torus_decay_deep
#print axioms MassGap.ReflFloor.windowGap_deep
#print axioms MassGap.ReflFloor.mass_ge_deep
#print axioms MassGap.ReflFloor.mass_floor_deep
#print axioms MassGap.ReflFloor.not_windowUpper
#print axioms MassGap.ReflFloor.not_reflFloorAt
#print axioms MassGap.ReflFloor.exists_depth
#print axioms MassGap.ReflFloor.eventually_not_reflFloorAt
#print axioms MassGap.ReflFloor.eventually_not_windowUpper
#print axioms MassGap.ReflFloor.not_floor_residual
#print axioms MassGap.ReflFloor.not_upper_residual
#print axioms MassGap.ReflFloor.headline_hypotheses_inconsistent
