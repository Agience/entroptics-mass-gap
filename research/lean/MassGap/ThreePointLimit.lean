import Mathlib
import MassGap.ThreePointAnomaly
import MassGap.ContinuumSchwinger

/-!
# MassGap.ThreePointLimit — a coupling family through each `stateK`, and its two-point derivative

`ThreePointAnomaly` proves the trace-anomaly identity `d/dβ cum2 = −Σ_p cum3(·,·,φ_p)` on every periodic
torus and lists, as its step 1, a family of infinite-volume states differentiable in `β` that agrees with
`stateK` at the step couplings. This module builds that family and reduces its differentiability to two
statements about the torus derivatives, uniform in the volume. Declarations are in the namespace
`MassGap.ThreePointLimit`.

## 1. The volume filter is fixed, the coupling varies (proved)

`stateK hN k = periodicState hN (dyBeta k)` is the limit of `torusState hN (2j+1) (dyBeta k)` along the
ultrafilter `periodicUltra hN (dyBeta k)` on extents. That ultrafilter is a `Classical.choose` of a
proposition that depends on the coupling, so two couplings have no common volume filter in the tree.
The family here keeps the volume ultrafilter and moves the coupling:

* `exists_state_ultra`: along any ultrafilter on the index, a family of states has a limit state (no
  refinement: an ultrafilter finer than an ultrafilter is itself).
* `limState hN u β`: the limit of `torusState hN (2j+1) β` along a given ultrafilter `u` on extents, at
  every real `β`.
* **`limState_periodicUltra`**: `limState hN (periodicUltra hN β) β = periodicState hN β`, so
  **`stateK_eq_limState`**: `stateK hN k = limState hN u_k (dyBeta k)` with `u_k = periodicUltra hN (dyBeta k)`.
  For each step `k`, `β ↦ limState hN u_k β` is a family of infinite-volume states through `stateK hN k`.

The family through step `k` meets `stateK hN (k+1)` only if the limit of the torus states at
`dyBeta (k+1)` does not depend on the ultrafilter (uniqueness of the periodic limit), which the tree does
not have. A coupling derivative at `dyBeta k` along `u_k` needs one step only.

## 2. The derivative passes through an ultralimit under equicontinuity (proved)

* **`hasDerivAt_of_equicont`**: along any non-trivial filter, if `c_i` has derivative `d_i` everywhere,
  `c_i → C` pointwise, `d_i(x₀) → D`, and the `d_i` are equicontinuous at `x₀` uniformly in `i`, then
  `C` has derivative `D` at `x₀`. The mean-value bound `|c_i t − c_i x₀ − (t − x₀) d_i x₀| ≤ ε |t − x₀|`
  holds at every `i` and is closed, so it passes to the limit.
* `exists_tendsto_of_bounded`: a bounded real sequence converges along every ultrafilter.

An integral form (`cum2 y − cum2 x = −∫ Σ_p cum3`) does not pass to the limit along `u`: dominated
convergence along a filter needs it countably generated, and a non-principal ultrafilter on `ℕ` is not.
The pointwise form of §2 needs no measurability of the ultralimit.

## 3. The two-point derivative of the family (proved, from two torus statements)

`dTorus M β f g = −Σ_p cum3 β f g φ_p` is the torus derivative of `torusCum2` (`torusCum2_hasDerivAt`).

* `AnomalyBounded f g β₀`: `|dTorus (2j+1) β₀ f g| ≤ B` for every extent index `j`.
* `AnomalyEquicont f g β₀`: the functions `t ↦ dTorus (2j+1) t f g` are equicontinuous at `β₀`,
  uniformly in `j`. `anomalyEquicont_of_lipschitz`: a Lipschitz bound uniform in `j` gives it.
* **`limCum2_hasDerivAt`**: under both, for every ultrafilter `u` on extents there is `D` with
  `dTorus (2j+1) β₀ f g → D` along `u` and `d/dβ limCum2 hN u β f g = D` at `β₀`.
* **`stateK_cum2_hasDerivAt`**: at `β₀ = dyBeta k`, `u = u_k`: the family through `stateK hN k` has
  a coupling derivative of its connected two-point function at `dyBeta k`, equal to the ultralimit of
  `−Σ_p cum3` over the torus volumes, and its value at `dyBeta k` is the connected two-point function of
  `stateK hN k`.

## 4. What the two torus statements are

`AnomalyBounded` is implied by summability, uniform in the volume, of `p ↦ cum3 β₀ f g φ_p` over the torus
plaquettes (the connected three-point function with one insertion summed over the volume). `AnomalyEquicont`
is implied by a uniform Lipschitz bound in `β`; the `β`-derivative of `cum3 f g φ_p` is
`−cum4(f, g, φ_p, S)` (argued, not formalised: the tree has no `cum4` and no `cum3_hasDerivAt`), so a
uniform Lipschitz bound is implied by summability, uniform in the volume, of `(p, q) ↦ cum4 β f g φ_p φ_q`
near `β₀` (four-point clustering). `AnomalyBounded` is a finite-volume bound at `β₀`; `AnomalyEquicont` is
one on a coupling window around `β₀`; both are uniform in the extent. `ClusterRoute.ClusterPM` and `ClusterPassage.PointCluster` bound cumulants of the
flowed composites in `stateK hN k`, the infinite-volume state, eventually in the step `k`; they do not
bound torus cumulants with a plaquette insertion uniformly in the extent at a fixed coupling, so neither
supplies these two statements. Identifying `D` with the infinite-volume sum `−Σ_p cum3^u(f, g, φ_p)`
over `ℤ⁴` plaquettes is a further statement (domination of the torus terms by a summable weight on `ℤ⁴`
plaquettes, then `tendsto_tsum_of_dominated_convergence`, which needs no countability of the filter).

Open: `AnomalyBounded` and `AnomalyEquicont` at `dyBeta k` (proved nowhere, not supplied by `ClusterPM` or
`PointCluster`); the identification of `D` with the `ℤ⁴` sum `−Σ_p cum3^u`; uniqueness of the periodic
limit, needed for the family through step `k` to reach `stateK hN (k+1)`. At `β ≠ dyBeta k`, `limState` is a
state not shown to satisfy the DLR equations.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2j + 1` the even-extent index of `PeriodicState`; `4` the dimension; `1` the
extent's successor and the radius of the Lipschitz window; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ThreePointLimit

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.PeriodicState MassGap.ThreePointAnomaly MassGap.ContinuumSchwinger
open Filter
open scoped Topology

/-! ## 1. The volume filter is fixed, the coupling varies -/

section States

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Two states with the same values are equal. DERIVED: no numeral. -/
theorem state_eq {ν ν' : MassGap.DLRLimit.State X} (h : ∀ f, ν f = ν' f) : ν = ν' := by
  cases ν
  cases ν'
  congr
  funext f
  exact h f

/-- **A limit state along a given ultrafilter.** `DLRLimit.exists_limit_state` at the ultrafilter
itself; its refinement is the ultrafilter (`Ultrafilter.unique`). DERIVED: no numeral. -/
theorem exists_state_ultra {ι : Type*} (u : Ultrafilter ι) (μ : ι → MassGap.DLRLimit.State X) :
    ∃ ν : MassGap.DLRLimit.State X,
      ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) (u : Filter ι) (𝓝 (ν f)) := by
  haveI : (u : Filter ι).NeBot := u.neBot'
  obtain ⟨u', ν, hle, h⟩ := MassGap.DLRLimit.exists_limit_state (u : Filter ι) μ
  have heq : (u' : Filter ι) = u := u.unique hle
  exact ⟨ν, fun f => by rw [← heq]; exact h f⟩

end States

variable {N : ℕ}

/-- **The limit of the periodic torus states along a given ultrafilter `u` on extents**, at coupling
`β`. DERIVED: `2j + 1` the even-extent index. -/
def limState (hN : N ≠ 0) (u : Ultrafilter ℕ) (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :=
  (exists_state_ultra u (fun j : ℕ => torusState hN (2 * j + 1) β)).choose

/-- DERIVED: `2j + 1` the even-extent index. -/
theorem tendsto_limState (hN : N ≠ 0) (u : Ultrafilter ℕ) (β : ℝ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Tendsto (fun j : ℕ => torusState hN (2 * j + 1) β f) (u : Filter ℕ) (𝓝 (limState hN u β f)) :=
  (exists_state_ultra u (fun j : ℕ => torusState hN (2 * j + 1) β)).choose_spec f

/-- **At its own ultrafilter the family is the periodic state.** DERIVED: no numeral. -/
theorem limState_periodicUltra (hN : N ≠ 0) (β : ℝ) :
    limState hN (periodicUltra hN β) β = periodicState hN β := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  exact state_eq fun f =>
    tendsto_nhds_unique (tendsto_limState hN (periodicUltra hN β) β f) (tendsto_periodicState hN β f)

/-- **The family through step `k`**: `stateK hN k` is `limState` at `dyBeta k` along
`periodicUltra hN (dyBeta k)`. DERIVED: `1` the least colour count. -/
theorem stateK_eq_limState (hN : N ≠ 0) (k : ℕ) :
    stateK hN k
      = limState hN (periodicUltra hN (dyBeta (one_le_of_ne_zero hN) k))
          (dyBeta (one_le_of_ne_zero hN) k) := by
  rw [limState_periodicUltra]
  rfl

/-! ## 2. The derivative passes through an ultralimit under equicontinuity -/

/-- **A pointwise limit of differentiable functions with equicontinuous derivatives is differentiable.**
Along any non-trivial filter: `c_i` with derivative `d_i` everywhere, `c_i → C` pointwise,
`d_i x₀ → D`, and `|d_i t − d_i x₀| ≤ ε` for `|t − x₀| < δ(ε)` at every `i`, give `C' (x₀) = D`.
DERIVED: no numeral. -/
theorem hasDerivAt_of_equicont {ι : Type*} {l : Filter ι} [l.NeBot]
    (c d : ι → ℝ → ℝ) (C : ℝ → ℝ) {D x₀ : ℝ}
    (hc : ∀ i t, HasDerivAt (c i) (d i t) t)
    (hC : ∀ t, Tendsto (fun i => c i t) l (𝓝 (C t)))
    (hD : Tendsto (fun i => d i x₀) l (𝓝 D))
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ i t, |t - x₀| < δ → |d i t - d i x₀| ≤ ε) :
    HasDerivAt C D x₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := heq ε hε
  filter_upwards [Metric.ball_mem_nhds x₀ hδ] with t ht
  have hfin : ∀ i, |c i t - c i x₀ - (t - x₀) * d i x₀| ≤ ε * |t - x₀| := by
    intro i
    have hder : ∀ s ∈ Metric.ball x₀ δ,
        HasDerivWithinAt (fun s => c i s - s * d i x₀) (d i s - d i x₀) (Metric.ball x₀ δ) s := by
      intro s _
      have h1 : HasDerivAt (fun s => c i s - s * d i x₀) (d i s - 1 * d i x₀) s :=
        (hc i s).sub ((hasDerivAt_id' s).mul_const (d i x₀))
      rw [one_mul] at h1
      exact h1.hasDerivWithinAt
    have hbd : ∀ s ∈ Metric.ball x₀ δ, ‖d i s - d i x₀‖ ≤ ε := by
      intro s hs
      rw [Real.norm_eq_abs]
      rw [Metric.mem_ball, Real.dist_eq] at hs
      exact hb i s hs
    have h2 := (convex_ball x₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
      (Metric.mem_ball_self hδ) ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h2
    rw [show c i t - c i x₀ - (t - x₀) * d i x₀
        = (c i t - t * d i x₀) - (c i x₀ - x₀ * d i x₀) by ring]
    exact h2
  have hlim : Tendsto (fun i => |c i t - c i x₀ - (t - x₀) * d i x₀|) l
      (𝓝 |C t - C x₀ - (t - x₀) * D|) :=
    (((hC t).sub (hC x₀)).sub (hD.const_mul (t - x₀))).abs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  exact le_of_tendsto' hlim hfin

/-- **A bounded real sequence converges along every ultrafilter.** DERIVED: no numeral. -/
theorem exists_tendsto_of_bounded (u : Ultrafilter ℕ) (a : ℕ → ℝ) (B : ℝ) (h : ∀ j, |a j| ≤ B) :
    ∃ D : ℝ, Tendsto a (u : Filter ℕ) (𝓝 D) := by
  have hmem : Set.Icc (-B) B ∈ (Ultrafilter.map a u : Filter ℝ) := by
    rw [Ultrafilter.coe_map]
    exact Filter.mem_map.mpr (Filter.univ_mem' fun j => abs_le.mp (h j))
  obtain ⟨D, _hD, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map a u)
    (le_principal_iff.mpr hmem)
  refine ⟨D, ?_⟩
  have hmap : Filter.map a (u : Filter ℕ) ≤ 𝓝 D := by
    rw [← Ultrafilter.coe_map]
    exact hlim
  exact hmap

/-! ## 3. The two-point derivative of the family -/

/-- **The torus derivative of the connected two-point function**: `−Σ_p cum3 β f g φ_p` on the torus of
extent `M + 1`. DERIVED: `4` the dimension; `1` the extent's successor. -/
def dTorus (M : ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) : ℝ :=
  -∑ p, cum3 (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (torusObs M g)
    (wilsonPlaqObs (WilsonHypercubic.bd (d := 4) (n := M + 1)) p)

/-- `d/dβ torusCum2 = dTorus`. DERIVED: no numeral. -/
theorem torusCum2_hasDerivAt' (hN : N ≠ 0) (M : ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    HasDerivAt (fun x => torusCum2 hN M x f g) (dTorus M β f g) β :=
  torusCum2_hasDerivAt hN M β f g

/-- **The torus derivative is bounded uniformly in the extent** at `β₀`.
DERIVED: `2j + 1` the even-extent index. -/
def AnomalyBounded (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (β₀ : ℝ) : Prop :=
  ∃ B : ℝ, ∀ j : ℕ, |dTorus (2 * j + 1) β₀ f g| ≤ B

/-- **The torus derivatives are equicontinuous at `β₀`, uniformly in the extent.**
DERIVED: `2j + 1` the even-extent index; `0` the signs. -/
def AnomalyEquicont (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (β₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (j : ℕ) (t : ℝ), |t - β₀| < δ →
    |dTorus (2 * j + 1) t f g - dTorus (2 * j + 1) β₀ f g| ≤ ε

/-- **A Lipschitz bound uniform in the extent gives equicontinuity.**
DERIVED: `1` the radius of the window and the shift of `L`; `0` the signs. -/
theorem anomalyEquicont_of_lipschitz
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {β₀ L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (j : ℕ) (t : ℝ), |t - β₀| ≤ 1 →
      |dTorus (2 * j + 1) t f g - dTorus (2 * j + 1) β₀ f g| ≤ L * |t - β₀|) :
    AnomalyEquicont f g β₀ := by
  intro ε hε
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨min 1 (ε / (L + 1)), lt_min one_pos (div_pos hε hL1), fun j t ht => ?_⟩
  have h1 : |t - β₀| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
  have h2 : |t - β₀| ≤ ε / (L + 1) := (lt_of_lt_of_le ht (min_le_right _ _)).le
  calc |dTorus (2 * j + 1) t f g - dTorus (2 * j + 1) β₀ f g|
      ≤ L * |t - β₀| := hL j t h1
    _ ≤ (L + 1) * (ε / (L + 1)) :=
        mul_le_mul (by linarith) h2 (abs_nonneg _) hL1.le
    _ = ε := by field_simp

/-- **The connected two-point function of the family** along `u` at coupling `β`.
DERIVED: no numeral. -/
def limCum2 (hN : N ≠ 0) (u : Ultrafilter ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) : ℝ :=
  limState hN u β (f * g) - limState hN u β f * limState hN u β g

/-- `torusCum2 → limCum2` along `u`. DERIVED: `2j + 1` the even-extent index. -/
theorem tendsto_torusCum2 (hN : N ≠ 0) (u : Ultrafilter ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Tendsto (fun j : ℕ => torusCum2 hN (2 * j + 1) β f g) (u : Filter ℕ)
      (𝓝 (limCum2 hN u β f g)) :=
  (tendsto_limState hN u β (f * g)).sub
    ((tendsto_limState hN u β f).mul (tendsto_limState hN u β g))

/-- **The coupling derivative of the family's connected two-point function.** Under `AnomalyBounded`
and `AnomalyEquicont` at `β₀`, along every ultrafilter `u` on extents, `dTorus` at `β₀` has a limit
`D` and `d/dβ limCum2 hN u β f g = D` at `β₀`. DERIVED: `2j + 1` the even-extent index. -/
theorem limCum2_hasDerivAt (hN : N ≠ 0) (u : Ultrafilter ℕ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {β₀ : ℝ}
    (hB : AnomalyBounded f g β₀) (hE : AnomalyEquicont f g β₀) :
    ∃ D : ℝ, Tendsto (fun j : ℕ => dTorus (2 * j + 1) β₀ f g) (u : Filter ℕ) (𝓝 D)
      ∧ HasDerivAt (fun β => limCum2 hN u β f g) D β₀ := by
  obtain ⟨B, hBj⟩ := hB
  obtain ⟨D, hD⟩ := exists_tendsto_of_bounded u _ B hBj
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  exact ⟨D, hD, hasDerivAt_of_equicont (l := (u : Filter ℕ))
    (fun j β => torusCum2 hN (2 * j + 1) β f g) (fun j t => dTorus (2 * j + 1) t f g) _
    (fun j t => torusCum2_hasDerivAt' hN (2 * j + 1) t f g)
    (fun t => tendsto_torusCum2 hN u t f g) hD hE⟩

/-- **Step 1 at step `k`**: under `AnomalyBounded` and `AnomalyEquicont` at `dyBeta k`, the family
`β ↦ limState hN u_k β`, `u_k = periodicUltra hN (dyBeta k)`, passes through `stateK hN k` at `dyBeta k`
(`stateK_eq_limState`) and its connected two-point function has a coupling derivative there, the
ultralimit `D` of the torus derivatives `−Σ_p cum3`; its value at `dyBeta k` is the connected two-point
function of `stateK hN k`. DERIVED: `1` the least colour count; `2j + 1` the even-extent index. -/
theorem stateK_cum2_hasDerivAt (hN : N ≠ 0) (k : ℕ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hB : AnomalyBounded f g (dyBeta (one_le_of_ne_zero hN) k))
    (hE : AnomalyEquicont f g (dyBeta (one_le_of_ne_zero hN) k)) :
    ∃ D : ℝ,
      Tendsto (fun j : ℕ => dTorus (2 * j + 1) (dyBeta (one_le_of_ne_zero hN) k) f g)
          ((periodicUltra hN (dyBeta (one_le_of_ne_zero hN) k) : Ultrafilter ℕ) : Filter ℕ) (𝓝 D)
        ∧ HasDerivAt
            (fun β => limCum2 hN (periodicUltra hN (dyBeta (one_le_of_ne_zero hN) k)) β f g) D
            (dyBeta (one_le_of_ne_zero hN) k)
        ∧ limCum2 hN (periodicUltra hN (dyBeta (one_le_of_ne_zero hN) k))
            (dyBeta (one_le_of_ne_zero hN) k) f g
          = stateK hN k (f * g) - stateK hN k f * stateK hN k g := by
  obtain ⟨D, hD, hder⟩ := limCum2_hasDerivAt hN (periodicUltra hN (dyBeta (one_le_of_ne_zero hN) k))
    f g hB hE
  refine ⟨D, hD, hder, ?_⟩
  rw [stateK_eq_limState]
  rfl

end MassGap.ThreePointLimit

end

#print axioms MassGap.ThreePointLimit.state_eq
#print axioms MassGap.ThreePointLimit.exists_state_ultra
#print axioms MassGap.ThreePointLimit.tendsto_limState
#print axioms MassGap.ThreePointLimit.limState_periodicUltra
#print axioms MassGap.ThreePointLimit.stateK_eq_limState
#print axioms MassGap.ThreePointLimit.hasDerivAt_of_equicont
#print axioms MassGap.ThreePointLimit.exists_tendsto_of_bounded
#print axioms MassGap.ThreePointLimit.torusCum2_hasDerivAt'
#print axioms MassGap.ThreePointLimit.anomalyEquicont_of_lipschitz
#print axioms MassGap.ThreePointLimit.tendsto_torusCum2
#print axioms MassGap.ThreePointLimit.limCum2_hasDerivAt
#print axioms MassGap.ThreePointLimit.stateK_cum2_hasDerivAt
