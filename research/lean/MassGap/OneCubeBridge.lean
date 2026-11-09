import Mathlib
import MassGap.DSGaugeQuotient
import MassGap.CoarseDS
import MassGap.UVStepMap

noncomputable section

/-!
# MassGap.OneCubeBridge — one cube of fixed physical size gives the branch gap

## Source

D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, "Lattice Mass Gaps and Continuum Criteria for
Four-Dimensional Yang–Mills Theory" (unrefereed), <https://github.com/creelie/4Y-M>, tag `v4.42.0`
(<https://doi.org/10.5281/zenodo.24055064>), `strong-coupling/forest/main.tex`, Section "The
continuum step at one physical scale", Definition `def:cube`, Theorems `thm:onescale`, `thm:transfer`,
Lemma `lem:dscomparison`, Propositions `prop:gauss`, `prop:gaussforest`, `prop:gaussevery`, cited below as [BBLR].
D. Bhattacharjee, U. Bhattacharya, "Spacing-Uniform Lattice Inequalities Cannot Produce the Yang–Mills Mass Gap"
(unrefereed), Zenodo, <https://doi.org/10.5281/zenodo.23444339>, source `source-history/superseded-layouts/tex/main.tex` of the same repository at `v4.42.0`,
Theorem `thm:nogo`, cited below as [BB]. The theorems of [BBLR] are not used as Lean hypotheses except where a
declaration says so; each ported statement carries its Lean proof.

## Their condition

[BBLR, Definition `def:cube`], in their words. For a finite set `V` of links, `γ_V(· | Q)` is the probability measure
on `G^V` with density proportional to `exp(Nβ Σ_{p ∩ V ≠ ∅} Re Tr Q^F_p)` against Haar measure, the links outside `V`
being those of `Q`; `d_V(Q_V, Q'_V) = Σ_{i ∈ V} δ(Q_i, Q'_i)`; and for `j ∈ A \ V`,

    C_{V,j} = sup W₁^{d_V}(γ_V(· | Q), γ_V(· | Q')) / δ(Q_j, Q'_j),

the supremum over pairs differing only at `j`. For `n ≥ 2` even, `V` is the set of active links `(x, μ)` with
`x ∈ [0, n)⁴`, its translates `V_x`, `x ∈ 2ℤ⁴`, satisfy `C_{V_x, j + x} = C_{V, j}`, every active link lies in exactly
`N_n = (n/2)⁴` of them, a class `c` is an orbit of `2ℤ⁴` on the active links, and `K_c = Σ_{j ∈ c \ V} C_{V,j}`.

    D(n, α), for 0 < α < 1, at the coupling β:  K_c ≤ α N_n for every class c.

The measure is the Wilson measure in their forest gauge; `A` is the set of links outside the forest `F`.
`DCond` is this condition on any finite system, in their translate form
`Σ_{x : j ∉ V_x} C_{V_x, j} = K_{c(j)}`. `weighted_le_of_DCond` is the summation in the proof of
[BBLR, Lemma `lem:dscomparison`(b)], `eq_zero_of_DCond` its uniqueness clause at `S = ∅`.

## Our condition, and the exact comparison

`CubeCond N β n α` is `DSGaugeQuotient.DSBoxInfluenceQ` at all large torus extents: a bi-invariant continuous
separating cost `d₀` and `C ≥ 0` with, for every direction `μ`,

    Σ_{x ∈ [0, n)⁴} Σ_{k ∉ V} C (μ, x) k ≤ α · #[0, n)⁴,

where `V` is the box of all links based in `[0, n)⁴` and, for every continuous `g` of the box links that is invariant
under gauge transformations at the interior sites of `V` and has Lipschitz vector `v`, moving an outside link `k` moves
the box mean of `g` by at most `(Σ_{l ∈ V} C l k · v l) · d₀`. It differs from `D(n, α)` in four ways.

1. Variables. `D` is posed on the forest-gauge links. `CubeCond` is posed on the ungauged Wilson measure, tested
   against interior-gauge-invariant functions; for a bi-invariant cost that restriction loses nothing
   (`DSGaugeQuotient.blkInfl_iff_Q`). Gauge invariance here means interior gauge invariance of the test: the outside
   link `k` is moved as a link, and gauge transformations at boundary sites are not quotiented.
2. Translates. `D` uses `2ℤ⁴` and up to `64` classes; `CubeCond` uses `ℤ⁴` and the `4` directions.
3. Which end is grouped. `K_c` groups by the class of the outside link `j`; `CubeCond` groups by the direction of the
   inside link `l`. `direction_sum_eq_class_sum`: both have the same total `Σ_{l ∈ V} Σ_{k ∉ V} C l k`, so each condition
   gives the other averaged over the groups, and neither gives the other group by group.
4. Strength of the entry. `C_{V,j}` tests `f` that is `1`-Lipschitz in the summed metric, the vector `v ≡ 1`. `BlkInfl`
   carries every vector `v`. `joint_influence`: `C_{V,j} := Σ_{l ∈ V} C l j` then satisfies their inequality; a joint
   coefficient does not split into entries, so `CubeCond`'s entry bound is the stronger one.

## What was ported

* `weighted_le_of_DCond`, `good_le_of_DCond`, `eq_zero_of_DCond`: the contraction of [BBLR, `lem:dscomparison`(b)].
* `cube_column_gain`, `cov_cube`: on any finite block system with influences of range `ρ`, block-averaged coefficient
  `α` gives covariance decay at every `θ` with `α < θ^ρ`, with a constant free of the size of the system
  (`CoarseDS.cov_spatialDS`). Rate `log(1/α)/ρ` per unit of distance, as in [BBLR, `thm:onescale`(v)], where `ρ = 2n`.
* `gapAt_of_forall_lt`, `gapAt_of_cube_cluster`: decay at every rate below `λ₀` gives the transfer gap at `λ₀`, the step
  [BBLR, `prop:gapdecay`] takes.
* `gapAt_of_cube`, `branchGap_of_cube`, `uvBelowIR_of_cube`, `clay_of_cube`: the lattice step at the Wilson measure and
  [BBLR, `thm:transfer`] on our route. These are proved outright from `CubeCond`, through
  `DSBoxFloor.overlapPoincare_of_DS` and `OverlapSweep.gapAt_ov`.
* `branchGap_of_cube_cluster`: the sharp rate `log(1/α)/(2ℓ)` of [BBLR, `thm:transfer`], with their lattice conclusion
  `thm:onescale`(v) as a named hypothesis (`CubeClusterAt`, unrefereed).
* `nogo_limit_zero`: [BB, Theorem `thm:nogo`].

## Rates

`branchGap_of_cube` has rate `cubeRate α / ℓ`, with `cubeRate α ≈ √(1 − α) / 8087040`: its proof passes through the
Poincaré inequality and a light cone, not through the Wasserstein contraction of [BBLR], and pays `√(1 − α)` and the
derived geometric constants. `branchGap_of_cube_cluster` has the rate of [BBLR] and asks for their decay. Either is
positive at fixed `α < 1`, fixed `ℓ`; `BranchGap` asks nothing more.

## `CubeCond` against `UVStepMap.BoundedSeed`

No implication between them is proved, in either direction. `branchGap_of_cube_or_seed` shows a branch may use
either at each coupling: they meet at `BranchGap`.

## The flat-field filter

`not_DCond_of_flat` is the last step of [BBLR, Propositions `prop:gaussforest`, `prop:gaussevery`], ported: weights
`a_c ≥ 0`, not all zero, with `Nn Σ a_c ≤ Σ a_c K_c` exclude `K_c ≤ α Nn` for every `c`, at every `α < 1`.

## The no-go

[BB, Theorem `thm:nogo`]: if gaps at spacing `a` are at least `δ > 0` in lattice units, uniformly, renormalised two-point
functions that converge at `t₁ < t₂` have limit `0` at `t₂`. Our statements are compatible with it, checked as follows.
`IRGapAt` and `BranchGap` carry a rate in physical units: the lattice rate is `m · aRun N β`, which vanishes along the
branch (`lattice_rate_tendsto_zero`, `branch_rate_lt`), so no uniform `δ` is asserted. The factor that drives [BB] is then
`e^{−(m a)(t/a)} = e^{−m t}`, free of `a` (`physical_factor`), and the ratio bound forces nothing. The no-go constrains
the hypothesis: `CubeAlong` with a bounded side gives a spacing-uniform lattice gap (`uniformGap_of_bounded_side`), which
is the situation of `nogo_limit_zero`. So the side must grow as `1/a`.

## What does not follow

`CubeCond` is open at every `β > 0`: no proof is given.

* `CubeCond` at any `β > 0` is not proved here. `cubeCond_zero` is its one instance, `β = 0`, `α = 0`; the branch starts at
  `βUV > 0`. `CubeAlong` is a hypothesis and no theorem in this tree establishes it.
* `gapAt_of_cube` does not reach [BBLR]'s lattice gap `log(1/α)/(2n)`: the Wilson proof runs through `cubeRate`. The decay
  `CubeClusterAt` at their rate is unproved for us, and `cov_cube` stops at Lipschitz observables of a finite system.
* `D(n, α)` itself is not a Lean hypothesis at the Wilson measure, since the forest gauge is not in this tree; `DCond` is
  its abstract form. No implication from `D(n, α)` to `CubeCond` is claimed.
* `clay_of_cube` keeps E, N, Y as hypotheses; the cube says nothing of the existence or non-triviality of the limit.
* [BBLR] and [BB] are unrefereed. No Lean statement here depends on them being correct.

DERIVED (module-wide): `0` the signs and the vacuum pairing; `1` the unit of the contraction and the rate it must beat;
`2` the even lag and the factor of `ρ_n = 2n`; `4` the spacetime dimension.
-/

namespace MassGap.OneCubeBridge

open MassGap Filter Topology
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.PeriodicState (periodicGaugeInvData)
open MassGap.UVStepMap (Branch BranchGap BoundedSeed)
open MassGap.HeatBathGapDecay (TorusClusterAt gapAt_of_torusClusterAt)
open MassGap.DSBlockContract (BlockKer BlkInfl ReadsOnly)
open MassGap.DobrushinMixed (LipD)
open MassGap.DobrushinGeneral (ex)
open MassGap.CoarseDS (BlockLaw cov_spatialDS)

variable {N : ℕ}

/-! ## 1. Their condition on a finite system -/

section Cond

variable {Lk Z : Type} [Fintype Lk] [Fintype Z] [DecidableEq Lk]

/-- **The influence of one link on the translates not containing it.** `Σ_{x : j ∉ V_x} C_{V_x, j}`, which is `K_{c(j)}`
in [BBLR, Section "Averaged cubes"] (Bhattacharjee, Bhattacharya, Lockwood, Romanov, unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`, `strong-coupling/forest/main.tex`).

DERIVED: `0` the terms of the translates containing `j`. -/
def influenceOff (V : Z → Finset Lk) (C : Z → Lk → ℝ) (j : Lk) : ℝ :=
  ∑ z, if j ∈ V z then 0 else C z j

/-- **The condition `D(n, α)`** of [BBLR, Definition `def:cube`] (unrefereed, <https://github.com/creelie/4Y-M>
`v4.42.0`), on a finite system: the total influence of each link on the translates not containing it is at most
`α` times the number `Nn` of translates containing it.

DERIVED: no numeral. -/
def DCond (V : Z → Finset Lk) (C : Z → Lk → ℝ) (Nn α : ℝ) : Prop :=
  ∀ j, influenceOff V C j ≤ α * Nn

/-- **The summation of [BBLR, Lemma `lem:dscomparison`(b)]** (unrefereed, <https://github.com/creelie/4Y-M>
`v4.42.0`). With `ϱ` the discrepancy of a coupling and `w` a weight, the block bound on each admissible translate
`Σ_{i ∈ V_z} w_i ϱ_i ≤ w̄_z Σ_{j ∉ V_z} C_{z,j} ϱ_j`, the comparison `w̄_z ≤ E w_j` on the support of `C`, and `D(n, α)`
give `Nn Σ_G wϱ ≤ α E Nn Σ wϱ`, where every link of `G` lies in at least `Nn` admissible translates.

DERIVED: `0` the signs and the terms off `V z`. -/
theorem weighted_le_of_DCond {V : Z → Finset Lk} {C : Z → Lk → ℝ} {Nn α E : ℝ} {w ϱ : Lk → ℝ} {wbar : Z → ℝ}
    (hC0 : ∀ z j, 0 ≤ C z j) (hw : ∀ i, 0 ≤ w i) (hϱ : ∀ i, 0 ≤ ϱ i) (hE : 0 ≤ E)
    (G : Finset Lk) (Adm : Finset Z)
    (hcount : ∀ i ∈ G, Nn ≤ ((Adm.filter fun z => i ∈ V z).card : ℝ))
    (hblock : ∀ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i ≤ wbar z * ∑ j, (if j ∈ V z then 0 else C z j * ϱ j))
    (hbar : ∀ z ∈ Adm, ∀ j, j ∉ V z → C z j ≠ 0 → wbar z ≤ E * w j)
    (hD : DCond V C Nn α) :
    Nn * ∑ i ∈ G, w i * ϱ i ≤ α * E * Nn * ∑ i, w i * ϱ i := by
  have hwϱ : ∀ i, 0 ≤ w i * ϱ i := fun i => mul_nonneg (hw i) (hϱ i)
  have h1 : Nn * ∑ i ∈ G, w i * ϱ i ≤ ∑ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i := by
    calc Nn * ∑ i ∈ G, w i * ϱ i = ∑ i ∈ G, Nn * (w i * ϱ i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ G, ∑ z ∈ Adm, (if i ∈ V z then w i * ϱ i else 0) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcount i hi) (hwϱ i)
      _ ≤ ∑ i, ∑ z ∈ Adm, (if i ∈ V z then w i * ϱ i else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => ?_
          refine Finset.sum_nonneg fun z _ => ?_
          split_ifs
          · exact hwϱ i
          · exact le_rfl
      _ = ∑ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : ∀ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i
      ≤ ∑ j, (if j ∈ V z then 0 else E * w j * (C z j * ϱ j)) := by
    intro z hz
    refine (hblock z hz).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with hj
    · simp
    · by_cases hc : C z j = 0
      · simp [hc]
      · exact mul_le_mul_of_nonneg_right (hbar z hz j hj hc) (mul_nonneg (hC0 z j) (hϱ j))
  have hnn : ∀ z j, 0 ≤ (if j ∈ V z then (0 : ℝ) else E * w j * (C z j * ϱ j)) := by
    intro z j
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hE (hw j)) (mul_nonneg (hC0 z j) (hϱ j))
  have h3 : ∑ z ∈ Adm, ∑ j, (if j ∈ V z then (0 : ℝ) else E * w j * (C z j * ϱ j))
      ≤ ∑ z, ∑ j, (if j ∈ V z then (0 : ℝ) else E * w j * (C z j * ϱ j)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun z _ _ => Finset.sum_nonneg fun j _ => hnn z j
  have h4 : ∑ z, ∑ j, (if j ∈ V z then (0 : ℝ) else E * w j * (C z j * ϱ j))
      ≤ α * E * Nn * ∑ i, w i * ϱ i := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have e : ∑ z, (if j ∈ V z then (0 : ℝ) else E * w j * (C z j * ϱ j))
        = E * (w j * ϱ j) * influenceOff V C j := by
      unfold influenceOff
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs
      · simp
      · ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (hD j) (mul_nonneg hE (hwϱ j))
    linarith [this, (by ring : E * (w j * ϱ j) * (α * Nn) = α * E * Nn * (w j * ϱ j))]
  exact h1.trans ((Finset.sum_le_sum h2).trans (h3.trans h4))

#print axioms weighted_le_of_DCond

/-- **The good links are bounded by the rest.** At `0 < Nn`, `θ = α E`: `(1 − θ) Σ_G wϱ ≤ θ Σ_{Gᶜ} wϱ`, the last display
of [BBLR, Lemma `lem:dscomparison`(b)] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`).

DERIVED: `1` the unit of the contraction; `0` the sign. -/
theorem good_le_of_DCond {V : Z → Finset Lk} {C : Z → Lk → ℝ} {Nn α E : ℝ} {w ϱ : Lk → ℝ} {wbar : Z → ℝ}
    (hC0 : ∀ z j, 0 ≤ C z j) (hw : ∀ i, 0 ≤ w i) (hϱ : ∀ i, 0 ≤ ϱ i) (hE : 0 ≤ E) (hNn : 0 < Nn)
    (G : Finset Lk) (Adm : Finset Z)
    (hcount : ∀ i ∈ G, Nn ≤ ((Adm.filter fun z => i ∈ V z).card : ℝ))
    (hblock : ∀ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i ≤ wbar z * ∑ j, (if j ∈ V z then 0 else C z j * ϱ j))
    (hbar : ∀ z ∈ Adm, ∀ j, j ∉ V z → C z j ≠ 0 → wbar z ≤ E * w j)
    (hD : DCond V C Nn α) :
    (1 - α * E) * ∑ i ∈ G, w i * ϱ i ≤ α * E * ∑ i ∈ Gᶜ, w i * ϱ i := by
  have h := weighted_le_of_DCond hC0 hw hϱ hE G Adm hcount hblock hbar hD
  rw [← Finset.sum_add_sum_compl G (fun i => w i * ϱ i)] at h
  have h' : Nn * ∑ i ∈ G, w i * ϱ i
      ≤ Nn * (α * E * (∑ i ∈ G, w i * ϱ i + ∑ i ∈ Gᶜ, w i * ϱ i)) := by
    calc Nn * ∑ i ∈ G, w i * ϱ i
        ≤ α * E * Nn * (∑ i ∈ G, w i * ϱ i + ∑ i ∈ Gᶜ, w i * ϱ i) := h
      _ = Nn * (α * E * (∑ i ∈ G, w i * ϱ i + ∑ i ∈ Gᶜ, w i * ϱ i)) := by ring
  have h'' := le_of_mul_le_mul_left h' hNn
  linarith

#print axioms good_le_of_DCond

/-- **No exceptional set: no discrepancy.** At `α E < 1` and `0 < w`, with every link in at least `Nn > 0` translates:
`ϱ = 0`, the clause "`μ₁ = μ₂` if `S = ∅`" of [BBLR, Lemma `lem:dscomparison`(b)] (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`).

DERIVED: `0` the limit; `1` the contraction. -/
theorem eq_zero_of_DCond {V : Z → Finset Lk} {C : Z → Lk → ℝ} {Nn α E : ℝ} {w ϱ : Lk → ℝ} {wbar : Z → ℝ}
    (hC0 : ∀ z j, 0 ≤ C z j) (hw : ∀ i, 0 < w i) (hϱ : ∀ i, 0 ≤ ϱ i) (hE : 0 ≤ E) (hNn : 0 < Nn)
    (hθ : α * E < 1) (Adm : Finset Z)
    (hcount : ∀ i, Nn ≤ ((Adm.filter fun z => i ∈ V z).card : ℝ))
    (hblock : ∀ z ∈ Adm, ∑ i ∈ V z, w i * ϱ i ≤ wbar z * ∑ j, (if j ∈ V z then 0 else C z j * ϱ j))
    (hbar : ∀ z ∈ Adm, ∀ j, j ∉ V z → C z j ≠ 0 → wbar z ≤ E * w j)
    (hD : DCond V C Nn α) (i : Lk) : ϱ i = 0 := by
  have h := good_le_of_DCond hC0 (fun i => (hw i).le) hϱ hE hNn Finset.univ Adm
    (fun i _ => hcount i) hblock hbar hD
  rw [Finset.compl_univ, Finset.sum_empty, mul_zero] at h
  have hnn : ∀ i ∈ (Finset.univ : Finset Lk), 0 ≤ w i * ϱ i :=
    fun i _ => mul_nonneg (hw i).le (hϱ i)
  have hsum : ∑ i, w i * ϱ i = 0 := by
    have h0 : 0 ≤ ∑ i, w i * ϱ i := Finset.sum_nonneg hnn
    nlinarith
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hi).resolve_left (hw i).ne'

#print axioms eq_zero_of_DCond

/-- **The flat-field filter.** The last step of [BBLR, Propositions `prop:gaussforest`, `prop:gaussevery`] (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`): weights `a_c ≥ 0`, not all zero, with `Nn Σ a_c ≤ Σ a_c K_c`, exclude
`K_c ≤ α Nn` for every `c`, at every `α < 1`.

DERIVED: `0` the signs; `1` the coefficient the condition must stay below. -/
theorem not_DCond_of_flat {ι : Type*} [Fintype ι] {K a : ι → ℝ} {Nn α : ℝ} (ha : ∀ c, 0 ≤ a c)
    (hne : ∃ c, a c ≠ 0) (hNn : 0 < Nn) (hα : α < 1) (hsum : Nn * ∑ c, a c ≤ ∑ c, a c * K c) :
    ¬ ∀ c, K c ≤ α * Nn := by
  intro hK
  obtain ⟨c, hc⟩ := hne
  have hpos : 0 < ∑ c, a c :=
    Finset.sum_pos' (fun c _ => ha c) ⟨c, Finset.mem_univ c, lt_of_le_of_ne (ha c) (Ne.symm hc)⟩
  have hle : ∑ c, a c * K c ≤ α * Nn * ∑ c, a c := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have := mul_le_mul_of_nonneg_left (hK c) (ha c)
    linarith [this, (by ring : a c * (α * Nn) = α * Nn * a c)]
  have hlt : α * Nn * ∑ c, a c < Nn * ∑ c, a c := by
    have : (α * Nn) < Nn := by nlinarith
    exact mul_lt_mul_of_pos_right this hpos
  linarith

#print axioms not_DCond_of_flat

/-- **Grouping by the inside link and by the outside link have one total.** Our box average groups the influences by the
direction of the inside link, `K_c` of [BBLR] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`) by the class of
the outside link; both sum to `Σ_{l ∈ V} Σ_{k ∉ V} C l k`.

DERIVED: no numeral. -/
theorem direction_sum_eq_class_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (dir : Lk → ι) (V : Finset Lk)
    (C : Lk → Lk → ℝ) :
    ∑ μ, ∑ l ∈ V.filter (fun l => dir l = μ), ∑ k ∈ Vᶜ, C l k
      = ∑ ν, ∑ k ∈ (Vᶜ).filter (fun k => dir k = ν), ∑ l ∈ V, C l k := by
  rw [Finset.sum_fiberwise, Finset.sum_fiberwise, Finset.sum_comm]

#print axioms direction_sum_eq_class_sum

omit [Fintype Lk] in
/-- **An influence matrix gives their joint coefficient.** `BlkInfl K d C` at the vector `v ≡ 1`: the test functions of
`C_{V,j}` in [BBLR, Section "Averaged cubes"] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`) move by at most
`(Σ_{l ∈ V} C l k) · d`. So `Σ_{l ∈ V} C l k` bounds `C_{V,k}`, by Kantorovich duality (argued).

DERIVED: `1` the vector of the summed metric. -/
theorem joint_influence {Ω : Type} [TopologicalSpace Ω] {K : BlockKer Ω Lk} {d : Lk → Ω → Ω → ℝ}
    {C : Lk → Lk → ℝ} (h : BlkInfl K d C) {g : (Lk → Ω) → ℝ} (hg : Continuous g) (hR : ReadsOnly K.S g)
    (hv : LipD d g (fun _ => 1)) (W : Lk → Ω) (k : Lk) (hk : k ∉ K.S) (x : Ω) :
    |K.Q g (Function.update W k x) - K.Q g W| ≤ (∑ l ∈ K.S, C l k) * d k x (W k) := by
  simpa using h g hg hR _ hv W k hk x

#print axioms joint_influence

end Cond

/-! ## 2. The abstract lattice step -/

section Abstract

variable {Lk Z : Type} [Fintype Lk] [Fintype Z] [DecidableEq Lk]

/-- **The block average of influences of range `ρ` gives the weighted column gain.** If every link lies in exactly `Mult`
blocks and the summed influence over those blocks is at most `α Mult`, the gain weighted by `θ^{−Dst}` is at least
`Mult (1 − α/θ^ρ)`.

DERIVED: `1` the unit of the gain; `0` the terms off the blocks and the signs. -/
theorem cube_column_gain (S : Z → Finset Lk) {C : Z → Lk → Lk → ℝ} (hC0 : ∀ z l k, 0 ≤ C z l k)
    (Dst : Lk → Lk → ℕ) {ρ Mult : ℕ} {α θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hrange : ∀ z l k, l ∈ S z → k ∉ S z → C z l k ≠ 0 → Dst l k ≤ ρ) (l : Lk)
    (hmult : (Finset.univ.filter (fun z => l ∈ S z)).card = Mult)
    (hcol : ∑ z, (if l ∈ S z then ∑ k ∈ (S z)ᶜ, C z l k else 0) ≤ α * Mult) :
    (Mult : ℝ) * (1 - α / θ ^ ρ)
      ≤ ∑ z, (if l ∈ S z then 1 - ∑ k ∈ (S z)ᶜ, C z l k / θ ^ Dst l k else 0) := by
  have hE : 0 < θ ^ ρ := pow_pos hθ0 ρ
  have hterm : ∀ z, (if l ∈ S z then 1 - (∑ k ∈ (S z)ᶜ, C z l k) / θ ^ ρ else 0)
      ≤ (if l ∈ S z then 1 - ∑ k ∈ (S z)ᶜ, C z l k / θ ^ Dst l k else 0) := by
    intro z
    split_ifs with hl
    · have : ∑ k ∈ (S z)ᶜ, C z l k / θ ^ Dst l k ≤ (∑ k ∈ (S z)ᶜ, C z l k) / θ ^ ρ := by
        rw [Finset.sum_div]
        refine Finset.sum_le_sum fun k hk => ?_
        by_cases hc : C z l k = 0
        · simp [hc]
        · have hd := hrange z l k hl (Finset.mem_compl.mp hk) hc
          exact div_le_div_of_nonneg_left (hC0 z l k) hE (pow_le_pow_of_le_one hθ0.le hθ1 hd)
      linarith
    · exact le_rfl
  have hsplit : ∑ z, (if l ∈ S z then 1 - (∑ k ∈ (S z)ᶜ, C z l k) / θ ^ ρ else 0)
      = (Mult : ℝ) - (∑ z, if l ∈ S z then ∑ k ∈ (S z)ᶜ, C z l k else 0) / θ ^ ρ := by
    have e : ∀ z, (if l ∈ S z then 1 - (∑ k ∈ (S z)ᶜ, C z l k) / θ ^ ρ else 0)
        = (if l ∈ S z then (1 : ℝ) else 0)
          - (if l ∈ S z then ∑ k ∈ (S z)ᶜ, C z l k else 0) / θ ^ ρ := by
      intro z
      split_ifs <;> simp
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_boole, hmult]
  have hbound : (Mult : ℝ) * (1 - α / θ ^ ρ)
      ≤ (Mult : ℝ) - (∑ z, if l ∈ S z then ∑ k ∈ (S z)ᶜ, C z l k else 0) / θ ^ ρ := by
    have : (∑ z, if l ∈ S z then ∑ k ∈ (S z)ᶜ, C z l k else 0) / θ ^ ρ ≤ α * Mult / θ ^ ρ :=
      div_le_div_of_nonneg_right hcol hE.le
    have e : (Mult : ℝ) * (1 - α / θ ^ ρ) = Mult - α * Mult / θ ^ ρ := by ring
    linarith
  calc (Mult : ℝ) * (1 - α / θ ^ ρ) ≤ _ := hbound
    _ = _ := hsplit.symm
    _ ≤ _ := Finset.sum_le_sum fun z _ => hterm z

#print axioms cube_column_gain

/-- **A contraction on one cube gives covariance decay.** On a finite block system with a `BlockLaw`, influences of
range `ρ`, every link in exactly `Mult` blocks, and block-averaged coefficient `α`: at every `θ ≤ 1` with `α < θ^ρ`,

    |σ(f g) − σ f σ g| ≤ 2 V_g Smax Dm² θ^{−R} Mult / (Mult (1 − α/θ^ρ)) · θ^{dd+1} Σ v_f,

for `f` reading farther than `dd` from the support of `g`. The rate `log(1/α)/ρ` per unit of distance and the constant free
of the system size are the content of [BBLR, Theorem `thm:onescale`(v)], `ρ_n = 2n` (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`); the proof here is `CoarseDS.cov_spatialDS`, with the coefficient grouped by
inside link.

DERIVED: `2` the conditional covariance and the cost square; `1` the step beyond `dd`; `0` the signs. -/
theorem cov_cube {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [Nonempty Ω] [Nonempty Z]
    {K : Z → BlockKer Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hL : BlockLaw K σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm) (hD : ∀ l a b, d l a b ≤ Dm)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z)) (hC0 : ∀ z l k, 0 ≤ C z l k)
    (Dst : Lk → Lk → ℕ) (hDt : ∀ a b c, Dst a c ≤ Dst a b + Dst b c)
    {ρ : ℕ} {α θ : ℝ} (hα : 0 ≤ α) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hαθ : α < θ ^ ρ)
    (hrange : ∀ z l k, l ∈ (K z).S → k ∉ (K z).S → C z l k ≠ 0 → Dst l k ≤ ρ)
    {Mult Smax R : ℕ} (hM : 0 < Mult) (hMZ : Mult ≤ Fintype.card Z)
    (hmult : ∀ l, (Finset.univ.filter (fun z => l ∈ (K z).S)).card = Mult)
    (hcol : ∀ l, ∑ z, (if l ∈ (K z).S then ∑ k ∈ (K z).Sᶜ, C z l k else 0) ≤ α * Mult)
    (hS : ∀ z, ((K z).S).card ≤ Smax) (hR : ∀ z, ∀ l ∈ (K z).S, ∀ m ∈ (K z).S, Dst l m ≤ R)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipD d f vf) (hvg : LipD d g vg) (B : Finset Lk) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg) (dd : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → ∀ b ∈ B, dd < Dst k b) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ 2 * Vg * Smax * Dm ^ 2 / θ ^ R * Mult / ((Mult : ℝ) * (1 - α / θ ^ ρ))
        * (θ ^ (dd + 1) * ∑ k, vf k) := by
  have hE : 0 < θ ^ ρ := pow_pos hθ0 ρ
  have hfrac : α / θ ^ ρ < 1 := (div_lt_one hE).mpr hαθ
  have hfrac0 : 0 ≤ α / θ ^ ρ := div_nonneg hα hE.le
  have hMr : (0 : ℝ) < Mult := by exact_mod_cast hM
  have hγ0 : 0 < (Mult : ℝ) * (1 - α / θ ^ ρ) := mul_pos hMr (by linarith)
  have hγZ : (Mult : ℝ) * (1 - α / θ ^ ρ) ≤ Fintype.card Z := by
    have hMZr : (Mult : ℝ) ≤ Fintype.card Z := by exact_mod_cast hMZ
    nlinarith
  exact cov_spatialDS hL hd0 hDm hD hC hC0 Dst hDt hθ0 hθ1 hγ0 hγZ
    (fun l => cube_column_gain (fun z => (K z).S) hC0 Dst hθ0 hθ1 hrange l (hmult l) (hcol l))
    (fun l => (hmult l).le) hS hR hf hg hvf hvg B hVg hgB hgV dd hfar

#print axioms cov_cube

end Abstract

/-! ## 3. From decay at every lower rate to the gap at the rate -/

section Rate

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The gap passes to the supremum of the rates.** `GapAt D (e^{−λ})` at every `λ < λ₀` gives `GapAt D (e^{−λ₀})`: the
closed form of "with every `λ < log(1/α)/(2n)`" in the proof of [BBLR, Theorem `thm:onescale`] (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`).

DERIVED: `2` the degree of `GapAt`. -/
theorem gapAt_of_forall_lt (D : Transfer.TransferData A) {lam₀ : ℝ}
    (h : ∀ lam : ℝ, lam < lam₀ → TransferGap.GapAt D (Real.exp (-lam))) :
    TransferGap.GapAt D (Real.exp (-lam₀)) := by
  intro x hx
  have hc : Tendsto (fun lam : ℝ => Real.exp (-lam) ^ 2 * D.form x x) (𝓝[<] lam₀)
      (𝓝 (Real.exp (-lam₀) ^ 2 * D.form x x)) := by
    have hcont : Continuous fun lam : ℝ => Real.exp (-lam) ^ 2 * D.form x x := by fun_prop
    exact (hcont.tendsto lam₀).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hc
    (eventually_mem_nhdsWithin.mono fun lam hlam => h lam hlam x hx)

#print axioms gapAt_of_forall_lt

/-- **The rate in lattice units against the rate in physical units.** `n a ≤ ℓ` gives `(R/ℓ) a ≤ R/n`.

DERIVED: `0` the signs; `1` the least side. -/
theorem rate_le {R ℓ a : ℝ} {n : ℕ} (hR : 0 ≤ R) (hℓ : 0 < ℓ) (hn : 1 ≤ n) (h : (n : ℝ) * a ≤ ℓ) :
    R / ℓ * a ≤ R / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hℓ hn']
  nlinarith [mul_le_mul_of_nonneg_left h hR]

#print axioms rate_le

end Rate

/-- **Clustering at every lower rate gives the gap at the rate.** `gapAt_of_torusClusterAt` and `gapAt_of_forall_lt`.

DERIVED: `4` the spacetime dimension; `0` the excluded rank. -/
theorem gapAt_of_cube_cluster (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {lam₀ : ℝ}
    (h : ∀ lam : ℝ, lam < lam₀ → TorusClusterAt τ p hN β (Real.exp (-lam))) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-lam₀)) :=
  gapAt_of_forall_lt _ fun lam hlam =>
    gapAt_of_torusClusterAt τ p hN β (Real.exp_pos _).le (h lam hlam)

#print axioms gapAt_of_cube_cluster

/-- **The lattice conclusion of [BBLR, Theorem `thm:onescale`(v)]**, as a statement about the periodic Wilson state:
clustering at every lattice rate below `log(1/α)/(2n)`. [BBLR] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`)
derive it from `D(n, α)` in the forest gauge; used here as a hypothesis, and not derived from `CubeCond`.

DERIVED: `2` the factor of `ρ_n = 2n`; `1` the numerator of `1/α`; `4` the spacetime dimension. -/
def CubeClusterAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  ∀ lam : ℝ, lam < Real.log (1 / α) / (2 * n) → TorusClusterAt τ p hN β (Real.exp (-lam))

/-- **The rate of [BBLR, Theorem `thm:transfer`] on the branch.** If at every branch coupling `CubeClusterAt` (unrefereed
hypothesis) holds at a side with `n · aRun N β ≤ ℓ`: `BranchGap` at `log(1/α)/(2ℓ)`.

DERIVED: `2` the factor of `ρ_n = 2n`; `1` the least side and the bound on `α`; `0` the signs; `4` the spacetime dimension. -/
theorem branchGap_of_cube_cluster (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV ℓ α : ℝ} (hℓ : 0 < ℓ) (hα0 : 0 < α)
    (hα1 : α < 1)
    (h : ∀ β : ℝ, Branch N β₀ βUV β → ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * aRun N β ≤ ℓ ∧ CubeClusterAt τ p hN β n α) :
    BranchGap τ p hN β₀ βUV (Real.log (1 / α) / (2 * ℓ)) := by
  intro β hβ
  obtain ⟨n, hn, hna, hc⟩ := h β hβ
  have hlog : 0 ≤ Real.log (1 / α) / 2 :=
    div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hα0]; linarith)) (by norm_num)
  have hg := gapAt_of_cube_cluster τ p hN β hc
  unfold UVIRSplit.IRGapAt
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ hg
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hr := rate_le hlog hℓ hn hna
  have e1 : Real.log (1 / α) / (2 * ℓ) = Real.log (1 / α) / 2 / ℓ := by rw [div_div]
  have e2 : Real.log (1 / α) / (2 * (n : ℝ)) = Real.log (1 / α) / 2 / n := by rw [div_div]
  rw [e1, e2]
  exact hr

#print axioms branchGap_of_cube_cluster

/-! ## 4. The cube at the Wilson measure -/

/-- **The cube condition at the Wilson measure.** At all large torus extents, `DSGaugeQuotient.DSBoxInfluenceQ β n j α`:
the gauge-invariant Dobrushin–Shlosman box criterion at side `n`, the analogue on the ungauged measure of `D(n, α)` in
[BBLR, Definition `def:cube`] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`). The module docstring lists the
four differences.

DERIVED: no numeral. -/
def CubeCond (N : ℕ) (β : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  ∀ᶠ j in atTop, DSGaugeQuotient.DSBoxInfluenceQ (N := N) β n j α

/-- **The condition is satisfiable**: at `β = 0` the box law ignores the outside, and `CubeCond N 0 n 0` holds at every
side (`DSGaugeQuotient.dsBoxInfluenceQ_zero`). This is its one instance in the tree.

DERIVED: `0` the coupling and the coefficient. -/
theorem cubeCond_zero (n : ℕ) : CubeCond N 0 n 0 :=
  Eventually.of_forall fun j => DSGaugeQuotient.dsBoxInfluenceQ_zero n j

#print axioms cubeCond_zero

/-- **The rate per cube.** `√(c/(389376 + c))/810` at `c = (1 − α)/256`.

DERIVED: `256 = 4⁴` the corner multiplicity of `DSBoxFloor.overlapPoincare_of_DS`; `389376 = 624²` and `810` the sweep and
the light cone of `OverlapSweep.torusClusterAt_ov`; `1` the unit of the contraction. -/
def cubeRate (α : ℝ) : ℝ := Real.sqrt (((1 - α) / 256) / (389376 + (1 - α) / 256)) / 810

/-- DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem cubeRate_pos {α : ℝ} (hα : α < 1) : 0 < cubeRate α := by
  have hc : 0 < (1 - α) / 256 := by linarith
  unfold cubeRate
  have : 0 < ((1 - α) / 256) / (389376 + (1 - α) / 256) := by positivity
  exact div_pos (Real.sqrt_pos.mpr this) (by norm_num)

#print axioms cubeRate_pos

/-- **The cube gives the lattice gap of order `1/n`.** `CubeCond N β n α` at `α < 1`, `1 ≤ n` gives the transfer gap at the
lattice rate `cubeRate α / n`. This is the lattice part of [BBLR, Theorem `thm:onescale`] (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`) for `CubeCond`, by a different proof: `DSGaugeQuotient.dsBox_of_Q`,
`DSBoxFloor.overlapPoincare_of_DS`, `OverlapSweep.gapAt_ov`.

DERIVED: `3` the colour period; `2 * j + 1` the even-extent family; `4` the spacetime dimension; `810` as in `cubeRate`. -/
theorem gapAt_of_cube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : α < 1)
    (h : CubeCond N β n α) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(cubeRate α / n))) := by
  have hc : 0 < (1 - α) / 256 := by linarith
  have hP : ∀ᶠ j in atTop, OverlapSweep.OverlapPoincare hN β n j ((1 - α) / 256) := by
    filter_upwards [h, Filter.eventually_ge_atTop (3 * n)] with j hj hjn
    exact DSBoxFloor.overlapPoincare_of_DS hN β hn (by omega) hα.le (DSGaugeQuotient.dsBox_of_Q hj)
  have hg := OverlapSweep.gapAt_ov τ p hN β hn hc hP
  have e : Real.sqrt (((1 - α) / 256) / (389376 + (1 - α) / 256)) / (810 * (n : ℝ)) = cubeRate α / n := by
    unfold cubeRate
    exact (div_div _ _ _).symm
  rw [e] at hg
  exact hg

#print axioms gapAt_of_cube

/-- **The cube at one coupling, at physical size at most `ℓ`,** gives the gap at the physical rate `cubeRate α / ℓ`.

DERIVED: `4` the spacetime dimension; `1` the least side; `0` the signs. -/
theorem irGapAt_of_cube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β ℓ α : ℝ} {n : ℕ} (hℓ : 0 < ℓ) (hn : 1 ≤ n) (hα : α < 1)
    (hna : (n : ℝ) * aRun N β ≤ ℓ) (h : CubeCond N β n α) :
    UVIRSplit.IRGapAt τ p hN β (cubeRate α / ℓ) := by
  unfold UVIRSplit.IRGapAt
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ (gapAt_of_cube τ p hN β hn hα h)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact rate_le (cubeRate_pos hα).le hℓ hn hna

#print axioms irGapAt_of_cube

/-- **The cube along the branch.** At every coupling of `Branch N β₀ βUV`, the cube condition at coefficient `α` on a side
`n` with `n · aRun N β ≤ ℓ`: the hypothesis of [BBLR, Theorem `thm:transfer`] (unrefereed,
<https://github.com/creelie/4Y-M> `v4.42.0`), with `CubeCond` for `D` and the branch for their dyadic sequence.

DERIVED: `1` the least side. -/
def CubeAlong (N : ℕ) (β₀ βUV ℓ α : ℝ) : Prop :=
  ∀ β : ℝ, Branch N β₀ βUV β → ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * aRun N β ≤ ℓ ∧ CubeCond N β n α

/-- **The cube along the branch gives the branch gap.** `CubeAlong N β₀ βUV ℓ α` at `α < 1`, `0 < ℓ`:
`BranchGap τ p hN β₀ βUV (cubeRate α / ℓ)`, at every plane and time axis. A cube of fixed physical size, with one
coefficient below one, is the whole input.

DERIVED: `4` the spacetime dimension; `0` the signs; `1` the bound on `α`. -/
theorem branchGap_of_cube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : α < 1)
    (h : CubeAlong N β₀ βUV ℓ α) : BranchGap τ p hN β₀ βUV (cubeRate α / ℓ) := by
  intro β hβ
  obtain ⟨n, hn, hna, hc⟩ := h β hβ
  exact irGapAt_of_cube τ p hN hℓ hn hα hna hc

#print axioms branchGap_of_cube

/-- **The cube along the branch gives `UVBelowIR`,** at every rate `0 < M ≤ cubeRate α / ℓ`
(`UVStepMap.uvBelowIR_of_branchGap`).

DERIVED: `1` the least colour count and the bound on `α`; `0` the signs; `4` the spacetime dimension. -/
theorem uvBelowIR_of_cube (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ βUV ℓ α M : ℝ} (hUV : 0 < βUV)
    (hℓ : 0 < ℓ) (hα : α < 1) (hM : 0 < M) (hMm : M ≤ cubeRate α / ℓ) (h : CubeAlong N β₀ βUV ℓ α) :
    ClayRoutes.UVBelowIR τ p hN β₀ βUV M :=
  UVStepMap.uvBelowIR_of_branchGap τ p hN1 hN hUV hM hMm (branchGap_of_cube τ p hN hℓ hα h)

#print axioms uvBelowIR_of_cube

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the cube.** At `2 ≤ N`, `0 < L`, `0 < βUV ≤ β₀`, `α < 1`, `0 < ℓ`,
`CubeAlong N β₀ βUV ℓ α` and E, N, Y: `ClayRoutes.ClayContinuum` (`UVStepMap.clay_of_branchGap`). This is the place of
[BBLR, Theorem `thm:transfer`] (unrefereed, <https://github.com/creelie/4Y-M> `v4.42.0`) on our route; E, N, Y stay
hypotheses.

DERIVED: `2` the least rank; `0` the reflection plane and the signs; `4` the spacetime dimension; `1` the bound on `α`. -/
theorem clay_of_cube (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV ℓ α : ℝ} (hUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀) (hℓ : 0 < ℓ) (hα : α < 1)
    (h : CubeAlong N β₀ βUV ℓ α)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  UVStepMap.clay_of_branchGap hN2 hN Z τ hZ hB hL hUV hUVβ₀ (div_pos (cubeRate_pos hα) hℓ)
    (branchGap_of_cube τ 0 hN hℓ hα h) O G hconv hY

#print axioms clay_of_cube

/-! ## 5. The cube and the seed meet at the branch gap -/

/-- **A seed at one coupling gives the gap at the physical rate `log 2 / C`.** The body of
`UVStepMap.branchGap_of_boundedSeed` at one coupling.

DERIVED: `2` the least rank and the doubling; `log 2` the window gap; `0` the plane, the time axis and the signs;
`1/1000` the seed of `CouplingTower.windowGap`. -/
theorem irGapAt_of_seed (hN2 : 2 ≤ N) (hN : N ≠ 0) {β C : ℝ} {w : ℕ} (hβ : 0 ≤ β) (hC : 0 < C) (hw : 1 ≤ w)
    (hseed : CouplingTower.windowCoupling N β w ≤ 1 / 1000) (hsize : (2 : ℝ) ^ w * aRun N β ≤ C) :
    UVIRSplit.IRGapAt 0 0 hN β (Real.log 2 / C) := by
  obtain ⟨r, hr0, _, hg, _, hlog⟩ := CouplingTower.windowGap hN2 hN hβ hw hseed
  unfold UVIRSplit.IRGapAt
  refine GapStep.gapAt_mono _ hr0.le ?_ hg
  have hr : r = Real.exp (-(Real.log 2 / 2 ^ w)) := by
    rw [← hlog, neg_neg, Real.exp_log hr0]
  rw [hr, Real.exp_le_exp, neg_le_neg_iff]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2w : (0 : ℝ) < 2 ^ w := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hC h2w]
  nlinarith [mul_le_mul_of_nonneg_left hsize hl2.le]

#print axioms irGapAt_of_seed

/-- **Cube or seed at each coupling gives the branch gap.** At every branch coupling, either the cube condition at a side
of physical size at most `ℓ`, or a seed window of physical size at most `C`: `BranchGap` at
`min (cubeRate α / ℓ) (log 2 / C)`. So neither condition needs the other, and `CubeAlong`, `BoundedSeed` are the two
extreme cases.

DERIVED: `2` the least rank; `0` the plane, the time axis and the signs; `1` the least indices and the bound on `α`;
`1/1000` the seed of `DoublingSharp`. -/
theorem branchGap_of_cube_or_seed (hN2 : 2 ≤ N) (hN : N ≠ 0) {β₀ βUV ℓ C α : ℝ} (hUV : 0 < βUV) (hℓ : 0 < ℓ)
    (hC : 0 < C) (hα : α < 1)
    (h : ∀ β : ℝ, Branch N β₀ βUV β →
      (∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * aRun N β ≤ ℓ ∧ CubeCond N β n α) ∨
      (∃ w : ℕ, 1 ≤ w ∧ CouplingTower.windowCoupling N β w ≤ 1 / 1000 ∧ (2 : ℝ) ^ w * aRun N β ≤ C)) :
    BranchGap 0 0 hN β₀ βUV (min (cubeRate α / ℓ) (Real.log 2 / C)) := by
  intro β hβ
  have hβ0 : 0 < β := lt_of_lt_of_le hUV hβ.1
  have ha : 0 ≤ aRun N β := (aRun_pos (by omega) hβ0).le
  rcases h β hβ with ⟨n, hn, hna, hc⟩ | ⟨w, hw, hseed, hsize⟩
  · exact UVStepMap.irGapAt_mono 0 0 hN (min_le_left _ _) ha (irGapAt_of_cube 0 0 hN hℓ hn hα hna hc)
  · exact UVStepMap.irGapAt_mono 0 0 hN (min_le_right _ _) ha (irGapAt_of_seed hN2 hN hβ0.le hC hw hseed hsize)

#print axioms branchGap_of_cube_or_seed

/-! ## 6. The no-go -/

/-- **The no-go of [BB, Theorem `thm:nogo`]** (Bhattacharjee, Bhattacharya, unrefereed, Zenodo,
<https://doi.org/10.5281/zenodo.23444339>), at the ratio bound: `S₂ ≤ e^{−c/a} S₁`, `0 ≤ S₂`, `a → 0⁺`, `c > 0`, and
convergence of `S₁` and `S₂`, give limit `0` for `S₂`. In their use `c = δ (t₂ − t₁)`, `δ` a spacing-uniform lattice gap, and
every renormalisation constant has cancelled.

DERIVED: `0` the limit and the signs. -/
theorem nogo_limit_zero {ι : Type*} {F : Filter ι} [F.NeBot] {a S₁ S₂ : ι → ℝ} {L₁ L₂ c : ℝ} (hc : 0 < c)
    (ha : Tendsto a F (𝓝[>] 0)) (hS₁ : Tendsto S₁ F (𝓝 L₁)) (hS₂ : Tendsto S₂ F (𝓝 L₂))
    (h0 : ∀ᶠ i in F, 0 ≤ S₂ i) (hr : ∀ᶠ i in F, S₂ i ≤ Real.exp (-(c * (a i)⁻¹)) * S₁ i) : L₂ = 0 := by
  have hinv : Tendsto (fun i => c * (a i)⁻¹) F atTop :=
    (tendsto_inv_nhdsGT_zero.comp ha).const_mul_atTop hc
  have hexp : Tendsto (fun i => Real.exp (-(c * (a i)⁻¹))) F (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hinv
  have hprod : Tendsto (fun i => Real.exp (-(c * (a i)⁻¹)) * S₁ i) F (𝓝 0) := by
    simpa using hexp.mul hS₁
  have hzero : Tendsto S₂ F (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod h0 hr
  exact tendsto_nhds_unique hS₂ hzero

#print axioms nogo_limit_zero

/-- **At a rate in physical units the factor of [BB] is free of the spacing.** A lattice gap `m a` over `t/a` lattice steps
has the factor `e^{−m t}`, so the ratio bound of [BB, Lemma `lem:ratio`] (unrefereed,
<https://doi.org/10.5281/zenodo.23444339>) forces nothing.

DERIVED: no numeral. -/
theorem physical_factor {m a t : ℝ} (ha : a ≠ 0) : Real.exp (-((m * a) * (t / a))) = Real.exp (-(m * t)) := by
  have e : (m * a) * (t / a) = m * t := by
    field_simp
  rw [e]

#print axioms physical_factor

/-- **The lattice rate of a physical rate vanishes.** `m · aRun N β → 0`, so `BranchGap` asserts no spacing-uniform gap.

DERIVED: `0` the limit; `1` the least colour count. -/
theorem lattice_rate_tendsto_zero (hN1 : 1 ≤ N) (m : ℝ) :
    Tendsto (fun β => m * aRun N β) atTop (𝓝 0) := by
  simpa using (ConstantPhysics.tendsto_aRun_zero (N := N) hN1).const_mul m

#print axioms lattice_rate_tendsto_zero

/-- **No uniform lattice gap in `BranchGap`.** Below every `δ > 0`, eventually in `β`.

DERIVED: `0` the sign and the limit; `1` the least colour count. -/
theorem branch_rate_lt (hN1 : 1 ≤ N) (m : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ β in atTop, m * aRun N β < δ :=
  (lattice_rate_tendsto_zero hN1 m).eventually (gt_mem_nhds hδ)

#print axioms branch_rate_lt

/-- **A bounded side gives a spacing-uniform gap.** If the sides of the cube stay at most `n₀` on the branch, the lattice gap
is at least `cubeRate α / n₀` at every branch coupling, in lattice units, the premise of [BB, Theorem `thm:nogo`]
(unrefereed, <https://doi.org/10.5281/zenodo.23444339>). So the side in `CubeAlong` has to grow as the spacing falls.

DERIVED: `1` the least side and the bound on `α`; `0` the signs; `4` the spacetime dimension. -/
theorem uniformGap_of_bounded_side (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV α : ℝ} {n₀ : ℕ} (hα : α < 1)
    (h : ∀ β : ℝ, Branch N β₀ βUV β → ∃ n : ℕ, 1 ≤ n ∧ n ≤ n₀ ∧ CubeCond N β n α) (β : ℝ)
    (hβ : Branch N β₀ βUV β) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(cubeRate α / n₀))) := by
  obtain ⟨n, hn, hn₀, hc⟩ := h β hβ
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ (gapAt_of_cube τ p hN β hn hα hc)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (cubeRate_pos hα).le hn' (by exact_mod_cast hn₀)

#print axioms uniformGap_of_bounded_side

end MassGap.OneCubeBridge
