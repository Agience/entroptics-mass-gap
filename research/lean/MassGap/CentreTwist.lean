import Mathlib
import MassGap.GaugeInvariantAlgebra
import MassGap.PeriodicState
import MassGap.SimpleGroup

/-!
# MassGap.CentreTwist — the centre twist is a gauge transformation on `ℤ⁴`, and invisible to the target

The centre (one-form) symmetry of a lattice gauge theory multiplies every link crossing a
codimension-one hyperplane by a central element `z`. On the periodic lattice it is a genuine global
symmetry whose sectors are 't Hooft's electric fluxes; the Polyakov loop winding across the
hyperplane picks up `z`. This module locates the observables of the one open input,
`ChessboardRead.TorusLagClear`, relative to it.

## What it gives

1. `heightTwist_eq_igaugeTransform`: on `ℤ⁴`, multiplying every link along `ν` by
   `z^{h(x_ν + 1) − h(x_ν)}` — for ANY height function `h : ℤ → ℤ` and central `z` — is the local
   gauge transformation `x ↦ (z^{h(x_ν)})⁻¹`. So every `GaugeInvariantAlgebra.IsIGaugeInvariant`
   observable is unchanged by it (`isIGaugeInvariant_heightTwist`).
2. `hyperTwist_eq_heightTwist`, `gaugeInv_hyperTwist`: the twist across one hyperplane
   `x_ν = a + ½` is the case `h = stepHeight a`; every member of `gaugeInvHalfSpaceAlg τ p` is
   invariant. `centre_invisible_SU`: at `SU(N)`, `2 ≤ N`, the centre has an element `z ≠ 1`, its
   twist moves every configuration, and it fixes every member of the algebra.
3. `pullback_torusTwist`, `torusObs_torusTwist`: on the periodic lattice of extent `M + 1` the twist
   across `x_ν = a + ½` pulls back to a height twist on `ℤ⁴` (`h = torusHeight M a`, which steps by
   one exactly at the periodic copies of `a`), so every torus observable `PeriodicState.torusObs M f`
   with `f` gauge invariant on `ℤ⁴` is invariant under the torus centre twist.

## Consequence for the route

`gaugeInvHalfSpaceAlg`, the algebra of `PeriodicState.periodicGaugeInvData`, is fixed pointwise by
every central twist (`gaugeInv_hyperTwist`), so it contains no charged observable. A bound on the
non-zero flux sectors of the periodic lattices is a statement about vectors outside it.
`CentreSector.charged_rate_does_not_reach_neutral` shows on abstract transfer data that such a bound,
even at rate `0`, fixes no neutral rate.
-/

namespace MassGap.CentreTwist

open MassGap.InfiniteLattice MassGap.GaugeInvariantAlgebra

/-! ## 1. Height twists on `ℤ⁴` are gauge transformations -/

section Height

variable {G : Type} [Group G]

/-- **The height twist.** Every link along `ν` based at `x` is multiplied by
`z ^ (h (x ν + 1) − h (x ν))`; every other link is unchanged.

DERIVED: `4` is the spacetime dimension; `1` is the unit step from a link's source to its target. -/
def heightTwist (ν : Fin 4) (z : G) (h : ℤ → ℤ) (U : IConf G) : IConf G :=
  fun l => if l.1 = ν then z ^ (h (l.2 ν + 1) - h (l.2 ν)) * U l else U l

/-- The height that steps by one across the hyperplane `x_ν = a + ½`.

DERIVED: `1` and `0` are the height above and below the hyperplane. -/
def stepHeight (a : ℤ) (s : ℤ) : ℤ := if a < s then 1 else 0

/-- `stepHeight a` steps by one exactly at `s = a`.

DERIVED: `1` is the unit step and the step value; `0` the value elsewhere. -/
theorem stepHeight_succ_sub (a s : ℤ) :
    stepHeight a (s + 1) - stepHeight a s = if s = a then 1 else 0 := by
  unfold stepHeight
  split_ifs <;> omega

#print axioms stepHeight_succ_sub

/-- **The twist across one hyperplane**: every link along `ν` based at `x_ν = a` — the links crossing
`x_ν = a + ½` — is multiplied by `z`.

DERIVED: `4` is the spacetime dimension. -/
def hyperTwist (ν : Fin 4) (a : ℤ) (z : G) (U : IConf G) : IConf G :=
  fun l => if l.1 = ν ∧ l.2 ν = a then z * U l else U l

/-- The hyperplane twist is the height twist at `stepHeight a`.

DERIVED: `4` is the spacetime dimension; `1` is the unit step. -/
theorem hyperTwist_eq_heightTwist (ν : Fin 4) (a : ℤ) (z : G) (U : IConf G) :
    hyperTwist ν a z U = heightTwist ν z (stepHeight a) U := by
  funext l
  obtain ⟨μ, x⟩ := l
  show (if μ = ν ∧ x ν = a then z * U (μ, x) else U (μ, x))
    = (if μ = ν then z ^ (stepHeight a (x ν + 1) - stepHeight a (x ν)) * U (μ, x)
        else U (μ, x))
  rw [stepHeight_succ_sub]
  by_cases hμ : μ = ν
  · by_cases hs : x ν = a
    · rw [if_pos (And.intro hμ hs), if_pos hμ, if_pos hs, zpow_one]
    · have hn : ¬ (μ = ν ∧ x ν = a) := fun h => hs h.2
      rw [if_neg hn, if_pos hμ, if_neg hs, zpow_zero, one_mul]
  · have hn : ¬ (μ = ν ∧ x ν = a) := fun h => hμ h.1
    rw [if_neg hn, if_neg hμ]

#print axioms hyperTwist_eq_heightTwist

/-- For any `z ≠ 1` the twist moves every configuration: at the link `(ν, a)` it multiplies by `z`.

DERIVED: `1` is the group identity; `4` the spacetime dimension. -/
theorem hyperTwist_ne (ν : Fin 4) (a : ℤ) {z : G} (hz : z ≠ 1) (U : IConf G) :
    hyperTwist ν a z U ≠ U := by
  intro h
  have h' := congrFun h (ν, fun _ => a)
  have e : hyperTwist ν a z U (ν, fun _ => a) = z * U (ν, fun _ => a) := by
    show (if ν = ν ∧ a = a then z * U (ν, fun _ => a) else U (ν, fun _ => a)) = _
    exact if_pos (And.intro rfl rfl)
  rw [e] at h'
  exact hz (mul_right_cancel (h'.trans (one_mul _).symm))

#print axioms hyperTwist_ne

end Height

section Gauge

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **A height twist by a central element is a local gauge transformation on `ℤ⁴`**:
`heightTwist ν z h U = igaugeTransform (x ↦ (z ^ h (x ν))⁻¹) U`. On a link along `ν` at `x` the gauge
factors are `(z^{h(x_ν)})⁻¹` at the source and `z^{h(x_ν + 1)}` at the target, which commute past
`U l` and combine to `z^{h(x_ν+1) − h(x_ν)}`; on any other link source and target share `x_ν` and the
factors cancel. Centrality is used for every power of `z` (`Subgroup.zpow_mem`).

DERIVED: `4` is the spacetime dimension; `1` is the unit step. -/
theorem heightTwist_eq_igaugeTransform (ν : Fin 4) {z : G} (hz : z ∈ Subgroup.center G)
    (h : ℤ → ℤ) (U : IConf G) :
    heightTwist ν z h U = igaugeTransform (fun x => (z ^ h (x ν))⁻¹) U := by
  have hc : ∀ (k : ℤ) (g : G), g * z ^ k = z ^ k * g := fun k g =>
    Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hz k) g
  funext l
  obtain ⟨μ, x⟩ := l
  show (if μ = ν then z ^ (h (x ν + 1) - h (x ν)) * U (μ, x) else U (μ, x))
    = (z ^ h (x ν))⁻¹ * U (μ, x) * (z ^ h (MassGap.InfiniteLattice.ishift μ x ν))⁻¹⁻¹
  rw [inv_inv]
  by_cases hμ : μ = ν
  · have hs : MassGap.InfiniteLattice.ishift μ x ν = x ν + 1 := by
      rw [hμ]
      show Function.update x ν (x ν + 1) ν = x ν + 1
      exact Function.update_self ν (x ν + 1) x
    rw [if_pos hμ, hs, ← zpow_neg, mul_assoc, hc, ← mul_assoc, ← zpow_add, neg_add_eq_sub]
  · have hs : MassGap.InfiniteLattice.ishift μ x ν = x ν := by
      show Function.update x μ (x μ + 1) ν = x ν
      exact Function.update_of_ne (Ne.symm hμ) (x μ + 1) x
    rw [if_neg hμ, hs, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

#print axioms heightTwist_eq_igaugeTransform

/-- **Gauge-invariant observables do not see a central height twist.**

DERIVED: `4` is the spacetime dimension. -/
theorem isIGaugeInvariant_heightTwist {F : C(IConf G, ℝ)} (hF : IsIGaugeInvariant F)
    (ν : Fin 4) {z : G} (hz : z ∈ Subgroup.center G) (h : ℤ → ℤ) (U : IConf G) :
    F (heightTwist ν z h U) = F U := by
  rw [heightTwist_eq_igaugeTransform ν hz h U]
  exact hF _ U

#print axioms isIGaugeInvariant_heightTwist

/-- **Every member of the target's algebra is centre neutral.** For `x ∈ gaugeInvHalfSpaceAlg τ p`,
a central `z` and any hyperplane `x_ν = a + ½`: `x (hyperTwist ν a z U) = x U`.

DERIVED: `4` is the spacetime dimension. -/
theorem gaugeInv_hyperTwist (τ : Fin 4) (p : ℤ) {x : C(IConf G, ℝ)}
    (hx : x ∈ gaugeInvHalfSpaceAlg (G := G) τ p) (ν : Fin 4) (a : ℤ) {z : G}
    (hz : z ∈ Subgroup.center G) (U : IConf G) :
    x (hyperTwist ν a z U) = x U := by
  have hg : IsIGaugeInvariant x := (Submodule.mem_inf.mp hx).2
  rw [hyperTwist_eq_heightTwist]
  exact isIGaugeInvariant_heightTwist hg ν hz _ U

#print axioms gaugeInv_hyperTwist

end Gauge

/-- **At `SU(N)` the centre is non-trivial and invisible to the target's algebra.** For `2 ≤ N`
there is a central `z ≠ 1` whose twist across `x_ν = a + ½` moves every configuration and fixes
every member of `gaugeInvHalfSpaceAlg τ p` (`SimpleGroup.exists_mem_center_ne_one`,
`hyperTwist_ne`, `gaugeInv_hyperTwist`).

DERIVED: `2` is the least rank with a non-trivial centre; `1` the group identity; `4` the spacetime
dimension. -/
theorem centre_invisible_SU (N : ℕ) (hN2 : 2 ≤ N) (τ : Fin 4) (p : ℤ) (ν : Fin 4) (a : ℤ) :
    ∃ z : MassGap.SUN.SU N, z ∈ Subgroup.center (MassGap.SUN.SU N) ∧ z ≠ 1 ∧
      (∀ U : IConf (MassGap.SUN.SU N), hyperTwist ν a z U ≠ U) ∧
      ∀ x ∈ gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p,
        ∀ U : IConf (MassGap.SUN.SU N), x (hyperTwist ν a z U) = x U := by
  obtain ⟨z, hz, hz1⟩ := MassGap.SimpleGroup.exists_mem_center_ne_one hN2
  exact ⟨z, hz, hz1, fun U => hyperTwist_ne ν a hz1 U,
    fun x hx U => gaugeInv_hyperTwist τ p hx ν a hz U⟩

#print axioms centre_invisible_SU

/-! ## 2. The torus twist pulls back to a height twist -/

section Torus

/-- **Floor division steps by one exactly at a multiple.** For `0 < q`:
`(t + 1) / q = t / q + (1 if (t + 1) % q = 0 else 0)`. `Int.ediv_emod_unique` in the two cases
`t % q + 1 = q` and `t % q + 1 < q`.

DERIVED: `1` is the unit step; `0` the residue of a multiple and the lower end of `q`. -/
theorem ediv_succ (t : ℤ) {q : ℤ} (hq : 0 < q) :
    (t + 1) / q = t / q + if (t + 1) % q = 0 then 1 else 0 := by
  have h0 : 0 ≤ t % q := Int.emod_nonneg t (ne_of_gt hq)
  have h1 : t % q < q := Int.emod_lt_of_pos t hq
  have hd : t % q + q * (t / q) = t := Int.emod_add_mul_ediv t q
  by_cases hc : t % q + 1 = q
  · have hu : (t + 1) / q = t / q + 1 ∧ (t + 1) % q = 0 :=
      (Int.ediv_emod_unique hq).mpr ⟨by linear_combination hd - hc, le_refl 0, hq⟩
    rw [if_pos hu.2, hu.1]
  · have hlt : t % q + 1 < q := lt_of_le_of_ne (Int.add_one_le_of_lt h1) hc
    have hu : (t + 1) / q = t / q ∧ (t + 1) % q = t % q + 1 :=
      (Int.ediv_emod_unique hq).mpr ⟨by linear_combination hd, by linarith, hlt⟩
    have hne : ¬ (t + 1) % q = 0 := by
      rw [hu.2]
      intro h
      linarith
    rw [if_neg hne, hu.1, add_zero]

#print axioms ediv_succ

/-- `finMod M s = a` exactly when `s % (M + 1)` is `a`'s value.

DERIVED: `1` is the successor writing the extent `M + 1`, as in `InfiniteLattice.finMod`. -/
theorem finMod_eq_iff (M : ℕ) (s : ℤ) (a : Fin (M + 1)) :
    finMod M s = a ↔ s % ((M : ℤ) + 1) = ((a : ℕ) : ℤ) := by
  have hpos : (0 : ℤ) < (M : ℤ) + 1 := by positivity
  have h0 : (0 : ℤ) ≤ s % ((M : ℤ) + 1) := Int.emod_nonneg s hpos.ne'
  rw [Fin.ext_iff]
  show (s % ((M : ℤ) + 1)).toNat = (a : ℕ) ↔ _
  constructor
  · intro h
    rw [← Int.toNat_of_nonneg h0, h]
  · intro h
    rw [h, Int.toNat_natCast]

#print axioms finMod_eq_iff

/-- **The torus height**: the number of periodic copies of the level `a` crossed, as a floor
quotient, `⌊(s + M − a)/(M + 1)⌋`.

DERIVED: `1` is the successor writing the extent `M + 1`. -/
def torusHeight (M : ℕ) (a : Fin (M + 1)) (s : ℤ) : ℤ :=
  (s + ((M : ℤ) - ((a : ℕ) : ℤ))) / ((M : ℤ) + 1)

/-- **The torus height steps by one exactly at the periodic copies of `a`**:
`torusHeight M a (s + 1) − torusHeight M a s = (1 if finMod M s = a else 0)`.

DERIVED: `1` is the unit step, the step value and the successor writing the extent; `0` the value
elsewhere and the residue of a multiple. -/
theorem torusHeight_succ_sub (M : ℕ) (a : Fin (M + 1)) (s : ℤ) :
    torusHeight M a (s + 1) - torusHeight M a s = if finMod M s = a then 1 else 0 := by
  have hq : (0 : ℤ) < (M : ℤ) + 1 := by positivity
  have ha0 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
  have ha1 : ((a : ℕ) : ℤ) < (M : ℤ) + 1 := by
    have := a.isLt
    omega
  have ht : s + 1 + ((M : ℤ) - ((a : ℕ) : ℤ)) = s + ((M : ℤ) - ((a : ℕ) : ℤ)) + 1 := by ring
  have hiff : (s + ((M : ℤ) - ((a : ℕ) : ℤ)) + 1) % ((M : ℤ) + 1) = 0 ↔ finMod M s = a := by
    have hre : s + ((M : ℤ) - ((a : ℕ) : ℤ)) + 1
        = (s - ((a : ℕ) : ℤ)) + ((M : ℤ) + 1) * 1 := by ring
    rw [hre, Int.add_mul_emod_self_left, finMod_eq_iff]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
      have hs : s = ((a : ℕ) : ℤ) + ((M : ℤ) + 1) * k := by linarith
      rw [hs, Int.add_mul_emod_self_left, Int.emod_eq_of_lt ha0 ha1]
    · intro h
      rw [Int.sub_emod, h, Int.emod_eq_of_lt ha0 ha1, sub_self, Int.zero_emod]
  unfold torusHeight
  rw [ht, ediv_succ _ hq, add_sub_cancel_left]
  by_cases hc : finMod M s = a
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · have hn : ¬ (s + ((M : ℤ) - ((a : ℕ) : ℤ)) + 1) % ((M : ℤ) + 1) = 0 :=
      fun h => hc (hiff.mp h)
    rw [if_neg hn, if_neg hc]

#print axioms torusHeight_succ_sub

variable {G : Type} [Group G]

/-- **The torus centre twist** across `x_ν = a + ½` on the periodic lattice of extent `M + 1`: every
link along `ν` based at `x_ν = a` multiplied by `z`. The Polyakov loop winding along `ν` crosses the
hyperplane once.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def torusTwist (M : ℕ) (ν : Fin 4) (a : Fin (M + 1)) (z : G)
    (W : WilsonHypercubic.Link 4 (M + 1) → G) : WilsonHypercubic.Link 4 (M + 1) → G :=
  fun l => if l.1 = ν ∧ l.2 ν = a then z * W l else W l

/-- **The torus twist, pulled back to `ℤ⁴`, is a height twist** at `torusHeight M a`: the pulled-back
configuration is twisted at every periodic copy of the hyperplane, and `torusHeight_succ_sub` counts
the copies.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem pullback_torusTwist (M : ℕ) (ν : Fin 4) (a : Fin (M + 1)) (z : G)
    (W : WilsonHypercubic.Link 4 (M + 1) → G) :
    pullback M (torusTwist M ν a z W) = heightTwist ν z (torusHeight M a) (pullback M W) := by
  funext l
  obtain ⟨μ, x⟩ := l
  show (if μ = ν ∧ finMod M (x ν) = a then z * W (μ, siteMod M x) else W (μ, siteMod M x))
    = (if μ = ν then z ^ (torusHeight M a (x ν + 1) - torusHeight M a (x ν)) * W (μ, siteMod M x)
        else W (μ, siteMod M x))
  rw [torusHeight_succ_sub]
  by_cases hμ : μ = ν
  · by_cases hs : finMod M (x ν) = a
    · rw [if_pos (And.intro hμ hs), if_pos hμ, if_pos hs, zpow_one]
    · have hn : ¬ (μ = ν ∧ finMod M (x ν) = a) := fun h => hs h.2
      rw [if_neg hn, if_pos hμ, if_neg hs, zpow_zero, one_mul]
  · have hn : ¬ (μ = ν ∧ finMod M (x ν) = a) := fun h => hμ h.1
    rw [if_neg hn, if_neg hμ]

#print axioms pullback_torusTwist

end Torus

/-- **Every torus observable of a gauge-invariant `ℤ⁴` observable is twist-invariant.** For `f`
gauge invariant and `z` central in `SU(N)`, `PeriodicState.torusObs M f` is invariant under the torus
centre twist across every hyperplane, in every direction `ν`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_torusTwist {N : ℕ} (M : ℕ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : IsIGaugeInvariant (G := MassGap.SUN.SU N) f) (ν : Fin 4) (a : Fin (M + 1))
    {z : MassGap.SUN.SU N} (hz : z ∈ Subgroup.center (MassGap.SUN.SU N))
    (W : WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    MassGap.PeriodicState.torusObs M f (torusTwist M ν a z W)
      = MassGap.PeriodicState.torusObs M f W := by
  show f (pullback M (torusTwist M ν a z W)) = f (pullback M W)
  rw [pullback_torusTwist]
  exact isIGaugeInvariant_heightTwist hf ν hz _ _

#print axioms torusObs_torusTwist

/-- The same for every member of the target's algebra.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_torusTwist_gaugeInv {N : ℕ} (M : ℕ) (τ : Fin 4) (p : ℤ)
    {x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)}
    (hx : x ∈ gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) (ν : Fin 4) (a : Fin (M + 1))
    {z : MassGap.SUN.SU N} (hz : z ∈ Subgroup.center (MassGap.SUN.SU N))
    (W : WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    MassGap.PeriodicState.torusObs M x (torusTwist M ν a z W)
      = MassGap.PeriodicState.torusObs M x W :=
  torusObs_torusTwist M x (Submodule.mem_inf.mp hx).2 ν a hz W

#print axioms torusObs_torusTwist_gaugeInv

end MassGap.CentreTwist
