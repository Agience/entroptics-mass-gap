import Mathlib
import MassGap.CellLinks

/-!
# MassGap.MatchAt — the match at the fixed length: Kotecký–Preiss for the chunk theory

The owner's chain, part 2. At the fixed physical length `r*` the substrate is to read coarse: the
block (chunk) theory at `r*` is a polymer gas whose activities satisfy the Kotecký–Preiss criterion.
This module states that criterion (`MatchAt`), proves that it gives exponential clustering of the
polymer gas (finite polymer systems, real activities of either sign, no cluster expansion), wires the
clustering into `CellLinks.Screens` and the (B) fields of `OneBridgeSU.OneBridgeData`, and states the
three routes the owner gave to `MatchAt` as theorems with their inputs explicit.

## 1. Finite hard-core polymer systems (`Compat`, `Z`, `nbr`, `Dob`)

`Pol` a finite type of polymers, `inc` a symmetric incompatibility relation, `w : Pol → ℝ` the
activities. `Z S = Σ_{T ⊆ S compatible} Π_{γ∈T} w γ`; `nbr γ` the polymers `≠ γ` incompatible with
`γ`. `Z_rec`: `Z S = Z (S∖γ) + w γ · Z (S∖γ∖nbr γ)`.

* `Dob c` (Dobrushin's criterion): `c ≥ 0` and `|w γ| e^{Σ_{nbr γ} c} ≤ 1 − e^{−c γ}`.
* `dob_bounds`: under `Dob c`, `Z S > 0` for every `S` and `e^{−c γ} Z (S∖γ) ≤ Z S ≤ e^{c γ} Z (S∖γ)`
  (strong induction on `S`). `abs_L_le`: the log-ratio `L S γ = log Z S − log Z (S∖γ)` has
  `|L| ≤ c γ`.
* `decay`: with a size `sz`, a weight `b ≥ 0`, a rate `κ ≥ 0` and the decay criterion
  `Σ_{δ∈nbr γ} (e^{c δ} − 1)(1 + b δ e^{κ sz δ}) ≤ b γ`, and any `φ` with `φ γ ≤ φ δ + sz δ` along
  active incompatible pairs and `φ γ ≤ 0` next to an active polymer of `U`:
  `|L S γ − L (S∖U) γ| ≤ (e^{c γ} − 1) b γ e^{−κ φ γ}`. The proof runs the recursion
  `e^{L} = 1 + w e^{−X}` through a Lipschitz bound (`F_lip`, mean value theorem) and the telescoping of
  `X` over `nbr γ`; nothing is expanded.
* `cluster`: for `A` disjoint from `U`,
  `|Q S A U| ≤ Σ_{γ∈A} (e^{c γ} − 1) b γ e^{−κ φ γ}`, `Q = log Z S − log Z (S∖A) − log Z (S∖U) +
  log Z (S∖U∖A)`. `truncated`: `|Z S Z(S∖U∖A) − Z(S∖A) Z(S∖U)| ≤ (e^{δ} − 1) Z(S∖A) Z(S∖U)` for
  `|Q| ≤ δ`. For `w ≥ 0`, `Z(S∖A)/Z S` is the probability that no polymer of `A` is present, so `Q` is
  the log of a truncated correlation of two local events.

## 2. Polymers on sites: `MatchAt` (Kotecký–Preiss with a decay weight)

Polymers are `Finset V`, incompatible when they meet (`meet`). `site v` the polymers containing `v`.

`MatchAt w a κ`: `w ∅ = 0`, `0 ≤ a ≤ 1`, `0 ≤ κ`, and at every site
`Σ_{X ∋ v} |w X| e^{a|X|} (1 + |X| e^{κ|X|}) ≤ a`.
This is the per-site Kotecký–Preiss criterion `Σ_{X∋v} |w X| e^{a|X|} ≤ a` with the extra weight
`1 + |X| e^{κ|X|}` that buys the decay rate `κ`.

* `dob_of_matchAt`: `MatchAt ⇒ Dob` with `c X = log(1 + |w X| e^{a|X|})`.
* `cluster_sites`: `MatchAt`, a `1`-Lipschitz distance function `dset` (for a pseudo-metric `ρ`)
  with `dset ≤ 0` on the active polymers of `U`, `ρ ≤ |X|` inside every active polymer, and a region
  `Λ` with `dset ≥ R` on it; for `A` polymers meeting `Λ`, disjoint from `U`:
  `|Q S A U| ≤ |Λ| a e^{−κ R}`. Exponential clustering at rate `κ` per unit of `ρ`, uniform in
  `S`, in the number of sites and in the volume.
* Control `not_matchAt_of_heavy`: a site with `Σ_{X∋v} |w X| > 1/2` fails `MatchAt`.

## 3. To (B): `PolymerCross`, `screens_of_polymerCross`, `relFloorM_of_polymerCross`

`PolymerCross P v d Kx M a κ L r₀`: for every pair of cells `i ≠ j` there is a polymer system with
`MatchAt w a κ`, the geometry of `cluster_sites`, `|Λ| ≤ M`, `R ≥ d(i,j) L − r₀`, and the cross term
bounded by the polymer interaction, `|⟪P vᵢ, P vⱼ⟫| ≤ Kx |Q| ‖vᵢ‖ ‖vⱼ‖`.
`screens_of_polymerCross`: that is `CellLinks.Screens` with `Ke = Kx M a e^{κ r₀}`,
`ξ = ℓ/(κ L)`. `relFloorM_of_polymerCross`: on the Wilson box of `CellLinks.BoxParams`, the cell rate
and `PolymerCross` for the pieces of the cell chain at every `m > 0`, `k ≥ K₀`, with one set of
constants, give `RelFloorM` with one rate and one zoom (fields (A) and (B) of `OneBridgeData`).

The hypothesis of `PolymerCross` that carries the content is the last clause: that the cross terms of
the conditional martingale pieces of the Wilson Doob slab are dominated by the polymer interaction of
a chunk theory at the cell scale. No declaration derives it from the Wilson measure: it is the
representation of the slab's conditional correlations through the polymer gas of the effective
action at `r*`, which is the match itself. `MatchAt` is a statement about some activities `w`; no
declaration here ties `w` to the block-spin effective action of 4D `SU(N)`.

## 4. The owner's three routes to `MatchAt`

* `matchAt_of_count` (the common engine): activities with `Σ_{X∋v, |X|=n} |w X| ≤ (z e^{−τ})ⁿ` and
  `4 z e^{1+κ−τ} ≤ 1` give `MatchAt w 1 κ`. `z` is the entropy per chunk (polymer count), `τ` the cost
  per chunk.
* Route (1), zoom out: `exists_length_match`, `matchAt_of_tension`. With `τ = σ k ℓ²` (an edge across
  chunks of side `ℓ` costs `σ × area`), for every `σ > 0` there is `ℓ₀` with `MatchAt` at every
  `ℓ ≥ ℓ₀`. The input is the count hypothesis at every `ℓ`: the activities of the chunk theory at
  side `ℓ` are bounded by its own tension. That is a bound on the flow from `r*` to `ℓ` (the
  intermediate regime), and `σ` is the effective tension of the chunk theory, not the string tension
  of the full measure read from large loops.
* Route (2), few states per chunk: `matchAt_of_states`, `entropy_split`, `card_labelled`. Polymer
  shapes counted by `zsⁿ`, each chunk with `k` readable states, so `z = zs k`; a cost per chunk
  `c ≥ log(zs k) + log 4 + 1 + κ` gives `MatchAt`. A chunk of continuous `SU(N)` links read in full
  (the whole fibre) has no finite `k`; `k` is finite for a coarse reading (a finite partition, as in
  `FiniteInformation`), and then the activities in the count are those of the coarse-read process,
  which is the full theory only when the reading is lumpable (`FiniteInformation.Passes`); a per-chunk
  defect leaves a floor (`FiniteInformation.floor_attained`).
* Route (3), fixed point: `matchAt_map`, `matchAt_of_fixedPoint`. If the chunk law at step `k+1`
  is the chunk law at step `k` transported by a bijection of chunks, `MatchAt` at one step gives
  `MatchAt` at every later step with the same `(a, κ)`. The content is the invariance hypothesis
  `hinv`; it is the aperture invariance (`FineLinks` link (2), `ApertureInvariance`,
  `NoTransition`) read on the chunk law, so this route closes exactly when that invariance holds.
* U(1) control: `not_matchAt_of_heavy`. At `σ = 0` the count bound with `τ = 0` and `z ≥ 1` has
  `4 z e^{1+κ} > 1`, so `matchAt_of_count` does not apply, and any activities with a per-site weight
  above `1/2` fail `MatchAt` outright.

## Strength

`cluster_sites` is a theorem about finite polymer systems with no hypothesis beyond `MatchAt` and the
geometry. Nothing here proves `MatchAt` for the block-spin effective action of 4D `SU(N)` at any
length, nor `PolymerCross` for the Wilson slab. Each of the three routes moves the input to a named
hypothesis: (1) and (2) to the count bound of the chunk theory at the chosen length (the
intermediate-regime flow), (3) to the invariance of the chunk law. No route, alone or combined,
removes the intermediate-regime flow: (3) needs `MatchAt` at one length as its base, and that base is
what (1) or (2) supplies only with the count bound of the flowed theory as input.

## Numerics (`research/code/match_checks.py`, under 10 s, no Monte Carlo)

* Pure Wilson action, polymer bound `|w X| ≤ u^{|X|}`, `u = sup |e^{−S_p}/c₀ − 1|`, entropy
  `e·20` per plaquette (4D link adjacency): `matchAt_of_count` holds for `β_std ≤ 0.0017`, the direct
  per-site KP sum (closed surfaces, `n ≥ 6`) for `β_std ≤ 0.0074`, SU(2) and SU(3) alike
  (`g² ≥ 544` for SU(2)). The tree's pruned strong-coupling region (`PotSharpCluster`, Knabe route)
  is `β_std ≤ 0.1`, `g² ≥ 40`. At `g² = O(1)` (`β_std = 1 … 4`) `u = 1.4 … 10`: far outside.
* The two-loop spacing peaks at `g² = 121/(102 b₀)` (`25.5` for SU(2)) and decreases beyond, so it
  does not reach either region; the largest ratio it gives from `g² = 1` is `7.9·10³` (13
  doublings).
* Edge cost: a flux tube of `ℓ` chunks has activity `e^{−4 σ r*² ℓ}`; the count route needs a cost
  per chunk `σ r*² ≥ log(20e) + 1 + log 4 = 6.38` (`r* ≥ 2.5/√σ`); `σ r*² = 1, 2, 4` fail.
  `U(1)` at weak coupling (`σ = 0`) fails.
* Migdal–Kadanoff (`b = 2`, an approximation, not a bound on the RG): SU(2) from `β_std = 1, 2, 4, 6`
  enters the KP region after `4, 8, 15, 23` doublings and stays (the stability of route (3) at the
  trivial fixed point); `U(1)` at `β ≥ 1` never enters it.

DERIVED (module-wide): `0` the empty polymer, the sign of every weight and the empty family; `1` the
unit activity of the empty family, the KP constant `a = 1` of the routes and the shift in
`e^x ≥ 1 + x`; `2` in `1 + |X| e^{κ|X|} ≥ 2` and in `1 + n ≤ 2ⁿ`; `1/2` the ratio bound `q ≤ 1/2`
of the geometric series, whence `4 = 2 · 2` in `4 z e^{1+κ−τ} ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MatchAt

open Finset

/-! ## 1. Finite hard-core polymer systems -/

section Polymer

/-- A symmetric relation. -/
abbrev SymmRel {α : Type*} (r : α → α → Prop) : Prop := ∀ ⦃x y⦄, r x y → r y x

variable {Pol : Type*} [Fintype Pol] [DecidableEq Pol] (inc : Pol → Pol → Prop) [DecidableRel inc]

/-- **A compatible family**: pairwise compatible polymers. -/
def Compat (T : Finset Pol) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ inc x y

instance (T : Finset Pol) : Decidable (Compat inc T) := by unfold Compat; infer_instance

variable (w : Pol → ℝ)

/-- **The partition function** of the polymers in `S`. -/
def Z (S : Finset Pol) : ℝ := ∑ T ∈ S.powerset.filter (Compat inc), ∏ γ ∈ T, w γ

/-- The polymers other than `γ` incompatible with `γ`. -/
def nbr (γ : Pol) : Finset Pol := univ.filter fun δ => δ ≠ γ ∧ inc γ δ

/-- **Dobrushin's criterion** with weights `c`. -/
def Dob (c : Pol → ℝ) : Prop :=
  ∀ γ, 0 ≤ c γ ∧ |w γ| * Real.exp (∑ δ ∈ nbr inc γ, c δ) ≤ 1 - Real.exp (-c γ)

/-- The log-ratio of removing `γ`. -/
def L (S : Finset Pol) (γ : Pol) : ℝ := Real.log (Z inc w S) - Real.log (Z inc w (S.erase γ))

/-- The log-ratio of removing `nbr γ` after `γ`. -/
def Xf (S : Finset Pol) (γ : Pol) : ℝ :=
  Real.log (Z inc w (S.erase γ)) - Real.log (Z inc w (S.erase γ \ nbr inc γ))

/-- The log-ratio of removing `B`. -/
def G (S B : Finset Pol) : ℝ := Real.log (Z inc w S) - Real.log (Z inc w (S \ B))

/-- **The polymer interaction of `A` and `U` in `S`.** -/
def Q (S A U : Finset Pol) : ℝ :=
  Real.log (Z inc w S) - Real.log (Z inc w (S \ A))
    - (Real.log (Z inc w (S \ U)) - Real.log (Z inc w ((S \ U) \ A)))

variable {inc w}

theorem compat_insert (hs : SymmRel inc) {γ : Pol} {t : Finset Pol} (hγ : γ ∉ t) :
    Compat inc (insert γ t) ↔ Compat inc t ∧ ∀ δ ∈ t, ¬ inc γ δ := by
  constructor
  · intro h
    refine ⟨fun x hx y hy hxy => h x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy,
      fun δ hδ => h γ (mem_insert_self _ _) δ (mem_insert_of_mem hδ) ?_⟩
    intro e
    rw [e] at hγ
    exact hγ hδ
  · rintro ⟨h1, h2⟩ x hx y hy hxy
    rw [mem_insert] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx]; exact h2 y hy
    · rw [hy]; exact fun h => h2 x hx (hs h)
    · exact h1 x hx y hy hxy

theorem Z_empty : Z inc w ∅ = 1 := by
  have h : Compat inc (∅ : Finset Pol) := by
    unfold Compat
    intro x hx
    exact absurd hx (notMem_empty x)
  unfold Z
  rw [powerset_empty, filter_singleton, if_pos h, sum_singleton, prod_empty]

/-- **The recursion** `Z S = Z (S∖γ) + w γ · Z (S∖γ∖nbr γ)`. -/
theorem Z_rec (hs : SymmRel inc) {S : Finset Pol} {γ : Pol} (hγ : γ ∈ S) :
    Z inc w S = Z inc w (S.erase γ) + w γ * Z inc w (S.erase γ \ nbr inc γ) := by
  have hnot : γ ∉ S.erase γ := notMem_erase γ S
  have hS : S = insert γ (S.erase γ) := (insert_erase hγ).symm
  have hpow : (S.erase γ \ nbr inc γ).powerset
      = (S.erase γ).powerset.filter (fun t => ∀ δ ∈ t, ¬ inc γ δ) := by
    ext t
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      refine ⟨fun x hx => (mem_sdiff.1 (h hx)).1, fun δ hδ hi => (mem_sdiff.1 (h hδ)).2 ?_⟩
      exact mem_filter.2 ⟨mem_univ _, ne_of_mem_erase (mem_sdiff.1 (h hδ)).1, hi⟩
    · rintro ⟨h1, h2⟩ x hx
      exact mem_sdiff.2 ⟨h1 hx, fun hn => h2 x hx (mem_filter.1 hn).2.2⟩
  unfold Z
  simp only [sum_filter]
  rw [hpow, sum_filter]
  conv_lhs => rw [hS]
  rw [sum_powerset_insert hnot, mul_sum]
  congr 1
  refine sum_congr rfl fun t ht => ?_
  have hγt : γ ∉ t := fun h => hnot (mem_powerset.1 ht h)
  rw [prod_insert hγt]
  by_cases h1 : Compat inc t
  · by_cases h2 : ∀ δ ∈ t, ¬ inc γ δ
    · rw [if_pos ((compat_insert hs hγt).2 ⟨h1, h2⟩), if_pos h2, if_pos h1]
    · rw [if_neg (fun h => h2 ((compat_insert hs hγt).1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 ((compat_insert hs hγt).1 h).1)]
    by_cases h2 : ∀ δ ∈ t, ¬ inc γ δ
    · rw [if_pos h2, if_neg h1, mul_zero]
    · rw [if_neg h2, mul_zero]

/-- **Removing a set costs at most its weights**, given one-step bounds below `s`. -/
theorem Z_sdiff_le {c : Pol → ℝ} (hc : ∀ γ, 0 ≤ c γ) {s : Finset Pol}
    (hpos : ∀ T ⊆ s, 0 < Z inc w T)
    (H : ∀ T ⊆ s, ∀ δ ∈ T, Z inc w (T.erase δ) ≤ Real.exp (c δ) * Z inc w T) (B : Finset Pol) :
    Z inc w (s \ B) ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w s := by
  refine Finset.induction_on B (by simp) ?_
  intro b B hb ih
  rw [sdiff_insert, sum_insert hb, Real.exp_add, mul_assoc]
  by_cases hbm : b ∈ s \ B
  · calc Z inc w ((s \ B).erase b) ≤ Real.exp (c b) * Z inc w (s \ B) := H _ sdiff_subset b hbm
      _ ≤ Real.exp (c b) * (Real.exp (∑ δ ∈ B, c δ) * Z inc w s) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
  · rw [erase_eq_of_notMem hbm]
    calc Z inc w (s \ B) ≤ Real.exp (∑ δ ∈ B, c δ) * Z inc w s := ih
      _ ≤ Real.exp (c b) * (Real.exp (∑ δ ∈ B, c δ) * Z inc w s) :=
          le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le (hpos s subset_rfl).le)
            (Real.one_le_exp (hc b))

/-- **One Dobrushin step.** -/
theorem dob_step (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) {S : Finset Pol} {γ : Pol}
    (hγ : γ ∈ S)
    (ih : ∀ T ⊂ S, 0 < Z inc w T ∧ ∀ δ ∈ T, Real.exp (-c δ) * Z inc w (T.erase δ) ≤ Z inc w T ∧
      Z inc w T ≤ Real.exp (c δ) * Z inc w (T.erase δ)) :
    Real.exp (-c γ) * Z inc w (S.erase γ) ≤ Z inc w S ∧
      Z inc w S ≤ Real.exp (c γ) * Z inc w (S.erase γ) := by
  set s := S.erase γ with hs_def
  have hsub : ∀ T ⊆ s, T ⊂ S := fun T hT => hT.trans_ssubset (erase_ssubset hγ)
  have hpos : ∀ T ⊆ s, 0 < Z inc w T := fun T hT => (ih T (hsub T hT)).1
  have H : ∀ T ⊆ s, ∀ δ ∈ T, Z inc w (T.erase δ) ≤ Real.exp (c δ) * Z inc w T := by
    intro T hT δ hδ
    have h1 := ((ih T (hsub T hT)).2 δ hδ).1
    calc Z inc w (T.erase δ) = Real.exp (c δ) * (Real.exp (-c δ) * Z inc w (T.erase δ)) := by
          rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (c δ) * Z inc w T := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hc : ∀ δ, 0 ≤ c δ := fun δ => (hD δ).1
  have hR := Z_sdiff_le hc hpos H (nbr inc γ)
  have hZs := hpos s subset_rfl
  have hZn : 0 ≤ Z inc w (s \ nbr inc γ) := (hpos _ sdiff_subset).le
  have hab : |w γ * Z inc w (s \ nbr inc γ)| ≤ (1 - Real.exp (-c γ)) * Z inc w s := by
    rw [abs_mul, abs_of_nonneg hZn]
    calc |w γ| * Z inc w (s \ nbr inc γ)
        ≤ |w γ| * (Real.exp (∑ δ ∈ nbr inc γ, c δ) * Z inc w s) :=
          mul_le_mul_of_nonneg_left hR (abs_nonneg _)
      _ = (|w γ| * Real.exp (∑ δ ∈ nbr inc γ, c δ)) * Z inc w s := by ring
      _ ≤ (1 - Real.exp (-c γ)) * Z inc w s := mul_le_mul_of_nonneg_right (hD γ).2 hZs.le
  have hrec : Z inc w S = Z inc w s + w γ * Z inc w (s \ nbr inc γ) := Z_rec hs hγ
  obtain ⟨hl, hu⟩ := abs_le.1 hab
  have k1 : Real.exp (-c γ) * Z inc w s = Z inc w s - (1 - Real.exp (-c γ)) * Z inc w s := by ring
  have hce : 0 ≤ (Real.exp (c γ) + Real.exp (-c γ) - 2) * Z inc w s :=
    mul_nonneg (by linarith [Real.add_one_le_exp (c γ), Real.add_one_le_exp (-c γ)]) hZs.le
  have k2 : Real.exp (c γ) * Z inc w s = Z inc w s + (1 - Real.exp (-c γ)) * Z inc w s
      + (Real.exp (c γ) + Real.exp (-c γ) - 2) * Z inc w s := by ring
  constructor <;> linarith

/-- **Dobrushin's theorem** on a finite polymer system: `Z S > 0` and
`e^{−c γ} Z (S∖γ) ≤ Z S ≤ e^{c γ} Z (S∖γ)`. -/
theorem dob_bounds (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S : Finset Pol) :
    0 < Z inc w S ∧ ∀ γ ∈ S, Real.exp (-c γ) * Z inc w (S.erase γ) ≤ Z inc w S ∧
      Z inc w S ≤ Real.exp (c γ) * Z inc w (S.erase γ) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    have hstep : ∀ γ ∈ S, Real.exp (-c γ) * Z inc w (S.erase γ) ≤ Z inc w S ∧
        Z inc w S ≤ Real.exp (c γ) * Z inc w (S.erase γ) := fun γ hγ => dob_step hs hD hγ ih
    refine ⟨?_, hstep⟩
    rcases S.eq_empty_or_nonempty with h | ⟨γ, hγ⟩
    · rw [h, Z_empty]; exact one_pos
    · exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) (ih _ (erase_ssubset hγ)).1) (hstep γ hγ).1

theorem Z_pos (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S : Finset Pol) :
    0 < Z inc w S := (dob_bounds hs hD S).1

theorem erase_le (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (T : Finset Pol) (δ : Pol)
    (hδ : δ ∈ T) : Z inc w (T.erase δ) ≤ Real.exp (c δ) * Z inc w T := by
  have h1 := ((dob_bounds hs hD T).2 δ hδ).1
  calc Z inc w (T.erase δ) = Real.exp (c δ) * (Real.exp (-c δ) * Z inc w (T.erase δ)) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (c δ) * Z inc w T := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- **The log-ratio is bounded by the weight**: `|L S γ| ≤ c γ`. -/
theorem abs_L_le (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S : Finset Pol) (γ : Pol) :
    |L inc w S γ| ≤ c γ := by
  by_cases hγ : γ ∈ S
  · obtain ⟨h1, h2⟩ := (dob_bounds hs hD S).2 γ hγ
    have hp := Z_pos hs hD S
    have hp' := Z_pos hs hD (S.erase γ)
    rw [abs_le]
    unfold L
    constructor
    · have := Real.log_le_log (mul_pos (Real.exp_pos _) hp') h1
      rw [Real.log_mul (Real.exp_pos _).ne' hp'.ne', Real.log_exp] at this
      linarith
    · have := Real.log_le_log hp h2
      rw [Real.log_mul (Real.exp_pos _).ne' hp'.ne', Real.log_exp] at this
      linarith
  · unfold L
    rw [erase_eq_of_notMem hγ, sub_self, abs_zero]
    exact (hD γ).1

/-- An inactive polymer changes nothing. -/
theorem L_eq_zero_of_w (hs : SymmRel inc) {S : Finset Pol} {γ : Pol} (hw : w γ = 0) :
    L inc w S γ = 0 := by
  unfold L
  by_cases hγ : γ ∈ S
  · rw [Z_rec hs hγ, hw, zero_mul, add_zero, sub_self]
  · rw [erase_eq_of_notMem hγ, sub_self]

theorem L_eq_F (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) {S : Finset Pol} {γ : Pol}
    (hγ : γ ∈ S) :
    L inc w S γ = Real.log (1 + w γ * Real.exp (-(Xf inc w S γ))) := by
  have hp := Z_pos hs hD (S.erase γ)
  have hp' := Z_pos hs hD (S.erase γ \ nbr inc γ)
  have hX : Real.exp (-(Xf inc w S γ)) = Z inc w (S.erase γ \ nbr inc γ) / Z inc w (S.erase γ) := by
    unfold Xf
    rw [neg_sub, Real.exp_sub, Real.exp_log hp', Real.exp_log hp]
  unfold L
  rw [hX, ← Real.log_div (Z_pos hs hD S).ne' hp.ne', Z_rec hs hγ, add_div, div_self hp.ne',
    mul_div_assoc]

theorem Xf_ge (hs : SymmRel inc) {c : Pol → ℝ} (hD : Dob inc w c) (S : Finset Pol) (γ : Pol) :
    -(∑ δ ∈ nbr inc γ, c δ) ≤ Xf inc w S γ := by
  have hR := Z_sdiff_le (s := S.erase γ) (fun δ => (hD δ).1) (fun T _ => Z_pos hs hD T)
    (fun T _ δ hδ => erase_le hs hD T δ hδ) (nbr inc γ)
  have hp := Z_pos hs hD (S.erase γ)
  have hp' := Z_pos hs hD (S.erase γ \ nbr inc γ)
  have := Real.log_le_log hp' hR
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at this
  unfold Xf
  linarith

theorem G_insert {S B : Finset Pol} {d : Pol} :
    G inc w S (insert d B) = G inc w S B + L inc w (S \ B) d := by
  unfold G L
  rw [sdiff_insert]
  ring

/-- **Lipschitz bound** for `x ↦ log (1 + w e^{−x})` where `|w| e^{−x} ≤ 1 − e^{−ε}`. -/
theorem F_lip {w ε x y m : ℝ} (hε : 0 ≤ ε) (hx : m ≤ x) (hy : m ≤ y)
    (hm : |w| * Real.exp (-m) ≤ 1 - Real.exp (-ε)) :
    |Real.log (1 + w * Real.exp (-x)) - Real.log (1 + w * Real.exp (-y))|
      ≤ (Real.exp ε - 1) * |x - y| := by
  have hden : ∀ t, m ≤ t → Real.exp (-ε) ≤ 1 + w * Real.exp (-t) := by
    intro t ht
    have h1 : Real.exp (-t) ≤ Real.exp (-m) := Real.exp_le_exp.2 (by linarith)
    have h2 : -(|w| * Real.exp (-t)) ≤ w * Real.exp (-t) := by
      rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le w) (Real.exp_pos _).le
    have h3 : |w| * Real.exp (-t) ≤ |w| * Real.exp (-m) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
    linarith
  have hderiv : ∀ t ∈ Set.Ici m, HasDerivWithinAt (fun t => Real.log (1 + w * Real.exp (-t)))
      (w * (Real.exp (-t) * -1) / (1 + w * Real.exp (-t))) (Set.Ici m) t := by
    intro t ht
    have hpos : 0 < 1 + w * Real.exp (-t) := lt_of_lt_of_le (Real.exp_pos _) (hden t ht)
    exact ((((hasDerivAt_neg t).exp).const_mul w).const_add 1).log hpos.ne' |>.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ici m,
      ‖w * (Real.exp (-t) * -1) / (1 + w * Real.exp (-t))‖ ≤ Real.exp ε - 1 := by
    intro t ht
    have hd := hden t ht
    have hpos : 0 < 1 + w * Real.exp (-t) := lt_of_lt_of_le (Real.exp_pos _) hd
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hnum : |w * (Real.exp (-t) * -1)| ≤ 1 - Real.exp (-ε) := by
      rw [abs_mul, abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by linarith [Set.mem_Ici.1 ht])) (abs_nonneg w)).trans hm
    have hk : (Real.exp ε - 1) * Real.exp (-ε) = 1 - Real.exp (-ε) := by
      rw [sub_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    have he : 0 ≤ Real.exp ε - 1 := sub_nonneg.2 (Real.one_le_exp hε)
    linarith [mul_le_mul_of_nonneg_left hd he]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici m)
    (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hx)
  simpa [Real.norm_eq_abs] using this

variable {c b sz φ : Pol → ℝ} {κ : ℝ} {U : Finset Pol}

/-- **Decay of the influence of `U`** on the log-ratio of `γ`:
`|L S γ − L (S∖U) γ| ≤ (e^{c γ} − 1) b γ e^{−κ φ γ}`. -/
theorem decay (hs : SymmRel inc) (hD : Dob inc w c) (hκ : 0 ≤ κ) (hb0 : ∀ γ, 0 ≤ b γ)
    (hb : ∀ γ, ∑ δ ∈ nbr inc γ, (Real.exp (c δ) - 1) * (1 + b δ * Real.exp (κ * sz δ)) ≤ b γ)
    (hφU : ∀ γ δ, δ ∈ nbr inc γ → w δ ≠ 0 → δ ∈ U → φ γ ≤ 0)
    (hφ : ∀ γ δ, δ ∈ nbr inc γ → w δ ≠ 0 → φ γ ≤ φ δ + sz δ) (S : Finset Pol) :
    ∀ γ, γ ∉ U → |L inc w S γ - L inc w (S \ U) γ|
      ≤ (Real.exp (c γ) - 1) * b γ * Real.exp (-(κ * φ γ)) := by
  have hε : ∀ δ, 0 ≤ Real.exp (c δ) - 1 := fun δ => sub_nonneg.2 (Real.one_le_exp (hD δ).1)
  have hterm0 : ∀ δ, 0 ≤ (Real.exp (c δ) - 1) * (1 + b δ * Real.exp (κ * sz δ)) := fun δ =>
    mul_nonneg (hε δ) (by have := hb0 δ; positivity)
  induction S using Finset.strongInduction
  rename_i S ih
  intro γ hγU
  have hR0 : 0 ≤ (Real.exp (c γ) - 1) * b γ * Real.exp (-(κ * φ γ)) :=
    mul_nonneg (mul_nonneg (hε γ) (hb0 γ)) (Real.exp_pos _).le
  by_cases hγS : γ ∈ S
  swap
  · have h1 : L inc w S γ = 0 := by unfold L; rw [erase_eq_of_notMem hγS, sub_self]
    have h2 : L inc w (S \ U) γ = 0 := by
      unfold L; rw [erase_eq_of_notMem (fun h => hγS (mem_sdiff.1 h).1), sub_self]
    rw [h1, h2, sub_zero, abs_zero]
    exact hR0
  have hγS' : γ ∈ S \ U := mem_sdiff.2 ⟨hγS, hγU⟩
  set s0 := S.erase γ with hs0
  have hsU : (S \ U).erase γ = s0 \ U := by
    ext x
    simp only [hs0, mem_erase, mem_sdiff]
    tauto
  have hinc : ∀ B : Finset Pol, B ⊆ nbr inc γ → |G inc w s0 B - G inc w (s0 \ U) B|
      ≤ Real.exp (-(κ * φ γ)) *
        ∑ δ ∈ B, (Real.exp (c δ) - 1) * (1 + b δ * Real.exp (κ * sz δ)) := by
    intro B
    refine Finset.induction_on B (fun _ => by simp [G]) ?_
    intro d B hd ihB hsub
    have hdB : B ⊆ nbr inc γ := (subset_insert d B).trans hsub
    have hdn : d ∈ nbr inc γ := hsub (mem_insert_self d B)
    rw [G_insert, G_insert, sum_insert hd, mul_add]
    have hcomm : (s0 \ U) \ B = (s0 \ B) \ U := sdiff_sdiff_comm
    rw [hcomm]
    have hT : s0 \ B ⊂ S := (sdiff_subset).trans_ssubset (erase_ssubset hγS)
    have key : |L inc w (s0 \ B) d - L inc w ((s0 \ B) \ U) d|
        ≤ Real.exp (-(κ * φ γ)) * ((Real.exp (c d) - 1) * (1 + b d * Real.exp (κ * sz d))) := by
      by_cases hw : w d = 0
      · rw [L_eq_zero_of_w hs hw, L_eq_zero_of_w hs hw, sub_zero, abs_zero]
        exact mul_nonneg (Real.exp_pos _).le (hterm0 d)
      by_cases hdU : d ∈ U
      · have h0 : L inc w ((s0 \ B) \ U) d = 0 := by
          unfold L
          rw [erase_eq_of_notMem (fun h => (mem_sdiff.1 h).2 hdU), sub_self]
        rw [h0, sub_zero]
        have hφ0 := hφU γ d hdn hw hdU
        have he1 : 1 ≤ Real.exp (-(κ * φ γ)) :=
          Real.one_le_exp (neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos hκ hφ0))
        have hbe : 1 ≤ 1 + b d * Real.exp (κ * sz d) := by
          have := mul_nonneg (hb0 d) (Real.exp_pos (κ * sz d)).le
          linarith
        calc |L inc w (s0 \ B) d| ≤ c d := abs_L_le hs hD _ _
          _ ≤ Real.exp (c d) - 1 := by linarith [Real.add_one_le_exp (c d)]
          _ ≤ (Real.exp (c d) - 1) * (1 + b d * Real.exp (κ * sz d)) :=
              le_mul_of_one_le_right (hε d) hbe
          _ ≤ Real.exp (-(κ * φ γ)) * ((Real.exp (c d) - 1) * (1 + b d * Real.exp (κ * sz d))) :=
              le_mul_of_one_le_left (hterm0 d) he1
      · have hIH := ih (s0 \ B) hT d hdU
        refine hIH.trans ?_
        have hφd := hφ γ d hdn hw
        have hexp : Real.exp (-(κ * φ d)) ≤ Real.exp (κ * sz d) * Real.exp (-(κ * φ γ)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hφd hκ])
        have hA : 0 ≤ (Real.exp (c d) - 1) * Real.exp (-(κ * φ γ)) :=
          mul_nonneg (hε d) (Real.exp_pos _).le
        calc (Real.exp (c d) - 1) * b d * Real.exp (-(κ * φ d))
            ≤ (Real.exp (c d) - 1) * b d * (Real.exp (κ * sz d) * Real.exp (-(κ * φ γ))) :=
              mul_le_mul_of_nonneg_left hexp (mul_nonneg (hε d) (hb0 d))
          _ = (Real.exp (c d) - 1) * b d * (Real.exp (κ * sz d) * Real.exp (-(κ * φ γ)))
              + 0 := by ring
          _ ≤ (Real.exp (c d) - 1) * b d * (Real.exp (κ * sz d) * Real.exp (-(κ * φ γ)))
              + (Real.exp (c d) - 1) * Real.exp (-(κ * φ γ)) := by linarith
          _ = Real.exp (-(κ * φ γ)) * ((Real.exp (c d) - 1) * (1 + b d * Real.exp (κ * sz d))) := by
              ring
    have e : G inc w s0 B + L inc w (s0 \ B) d - (G inc w (s0 \ U) B + L inc w ((s0 \ B) \ U) d)
        = (L inc w (s0 \ B) d - L inc w ((s0 \ B) \ U) d)
          + (G inc w s0 B - G inc w (s0 \ U) B) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add key (ihB hdB))
  have hX : |Xf inc w S γ - Xf inc w (S \ U) γ| ≤ Real.exp (-(κ * φ γ)) * b γ := by
    have h := hinc (nbr inc γ) subset_rfl
    have hXS : Xf inc w S γ = G inc w s0 (nbr inc γ) := rfl
    have hXU : Xf inc w (S \ U) γ = G inc w (s0 \ U) (nbr inc γ) := by
      unfold Xf G
      rw [hsU]
    rw [hXS, hXU]
    exact h.trans (mul_le_mul_of_nonneg_left (hb γ) (Real.exp_pos _).le)
  rw [L_eq_F hs hD hγS, L_eq_F hs hD hγS']
  have hm : |w γ| * Real.exp (-(-(∑ δ ∈ nbr inc γ, c δ))) ≤ 1 - Real.exp (-c γ) := by
    rw [neg_neg]; exact (hD γ).2
  calc |Real.log (1 + w γ * Real.exp (-Xf inc w S γ))
        - Real.log (1 + w γ * Real.exp (-Xf inc w (S \ U) γ))|
      ≤ (Real.exp (c γ) - 1) * |Xf inc w S γ - Xf inc w (S \ U) γ| :=
        F_lip (hD γ).1 (Xf_ge hs hD S γ) (Xf_ge hs hD (S \ U) γ) hm
    _ ≤ (Real.exp (c γ) - 1) * (Real.exp (-(κ * φ γ)) * b γ) :=
        mul_le_mul_of_nonneg_left hX (hε γ)
    _ = (Real.exp (c γ) - 1) * b γ * Real.exp (-(κ * φ γ)) := by ring

/-- **Exponential clustering of the polymer gas**: for `A` disjoint from `U`,
`|Q S A U| ≤ Σ_{γ∈A} (e^{c γ} − 1) b γ e^{−κ φ γ}`. -/
theorem cluster (hs : SymmRel inc) (hD : Dob inc w c) (hκ : 0 ≤ κ) (hb0 : ∀ γ, 0 ≤ b γ)
    (hb : ∀ γ, ∑ δ ∈ nbr inc γ, (Real.exp (c δ) - 1) * (1 + b δ * Real.exp (κ * sz δ)) ≤ b γ)
    (hφU : ∀ γ δ, δ ∈ nbr inc γ → w δ ≠ 0 → δ ∈ U → φ γ ≤ 0)
    (hφ : ∀ γ δ, δ ∈ nbr inc γ → w δ ≠ 0 → φ γ ≤ φ δ + sz δ) (S A : Finset Pol)
    (hAU : ∀ γ ∈ A, γ ∉ U) :
    |Q inc w S A U| ≤ ∑ γ ∈ A, (Real.exp (c γ) - 1) * b γ * Real.exp (-(κ * φ γ)) := by
  revert hAU
  refine Finset.induction_on A (fun _ => by simp [Q]) ?_
  intro a A ha ih hAU
  have ihA := ih fun γ hγ => hAU γ (mem_insert_of_mem hγ)
  have haU : a ∉ U := hAU a (mem_insert_self a A)
  have hd := decay hs hD hκ hb0 hb hφU hφ (S \ A) a haU
  have hcomm : (S \ U) \ A = (S \ A) \ U := sdiff_sdiff_comm
  unfold Q at ihA ⊢
  rw [sdiff_insert, sdiff_insert, sum_insert ha, hcomm]
  rw [hcomm] at ihA
  have e : Real.log (Z inc w S) - Real.log (Z inc w ((S \ A).erase a))
      - (Real.log (Z inc w (S \ U)) - Real.log (Z inc w (((S \ A) \ U).erase a)))
      = (L inc w (S \ A) a - L inc w ((S \ A) \ U) a)
        + (Real.log (Z inc w S) - Real.log (Z inc w (S \ A))
          - (Real.log (Z inc w (S \ U)) - Real.log (Z inc w ((S \ A) \ U)))) := by
    unfold L; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add hd ihA)

/-- `|x| ≤ δ` gives `|e^x − 1| ≤ e^δ − 1`. -/
theorem abs_exp_sub_one_le {x δ : ℝ} (h : |x| ≤ δ) : |Real.exp x - 1| ≤ Real.exp δ - 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.one_le_exp hx))]
    linarith [Real.exp_le_exp.2 (le_of_abs_le h)]
  · have hlt : Real.exp x - 1 < 0 := by
      linarith [(Real.exp_lt_exp.2 hx).trans_eq Real.exp_zero]
    rw [abs_of_neg hlt]
    have h1 : Real.exp (-x) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith [(abs_le.1 h).1])
    linarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]

/-- **The truncated correlation**: `|Q| ≤ δ` gives
`|Z S Z(S∖U∖A) − Z(S∖A) Z(S∖U)| ≤ (e^δ − 1) Z(S∖A) Z(S∖U)`. -/
theorem truncated (hs : SymmRel inc) (hD : Dob inc w c) {S A U : Finset Pol} {δ : ℝ}
    (h : |Q inc w S A U| ≤ δ) :
    |Z inc w S * Z inc w ((S \ U) \ A) - Z inc w (S \ A) * Z inc w (S \ U)|
      ≤ (Real.exp δ - 1) * (Z inc w (S \ A) * Z inc w (S \ U)) := by
  have h1 := Z_pos hs hD S
  have h2 := Z_pos hs hD (S \ A)
  have h3 := Z_pos hs hD (S \ U)
  have h4 := Z_pos hs hD ((S \ U) \ A)
  have hq : Real.exp (Q inc w S A U) * (Z inc w (S \ A) * Z inc w (S \ U))
      = Z inc w S * Z inc w ((S \ U) \ A) := by
    unfold Q
    simp only [Real.exp_sub]
    rw [Real.exp_log h1, Real.exp_log h2, Real.exp_log h3, Real.exp_log h4]
    field_simp
  have hD0 : 0 < Z inc w (S \ A) * Z inc w (S \ U) := mul_pos h2 h3
  rw [← hq, show Real.exp (Q inc w S A U) * (Z inc w (S \ A) * Z inc w (S \ U))
      - Z inc w (S \ A) * Z inc w (S \ U)
      = (Real.exp (Q inc w S A U) - 1) * (Z inc w (S \ A) * Z inc w (S \ U)) by ring,
    abs_mul, abs_of_pos hD0]
  exact mul_le_mul_of_nonneg_right (abs_exp_sub_one_le h) hD0.le

end Polymer

/-! ## 2. Polymers on sites: `MatchAt` -/

section Sites

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two polymers are incompatible when they meet. -/
def meet (X Y : Finset V) : Prop := (X ∩ Y).Nonempty

instance : DecidableRel (meet (V := V)) := fun X Y => by unfold meet; infer_instance

theorem meet_symm : SymmRel (meet (V := V)) := by
  intro X Y h
  unfold meet at *
  rwa [inter_comm]

/-- The polymers containing `v`. -/
def site (v : V) : Finset (Finset V) := univ.filter fun X => v ∈ X

/-- **The match at the fixed length** (Kotecký–Preiss per site, with decay weight):
`w ∅ = 0`, `0 ≤ a ≤ 1`, `0 ≤ κ`, and `Σ_{X ∋ v} |w X| e^{a|X|} (1 + |X| e^{κ|X|}) ≤ a` at every
site. -/
def MatchAt (w : Finset V → ℝ) (a κ : ℝ) : Prop :=
  w ∅ = 0 ∧ 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ κ ∧
    ∀ v : V, ∑ X ∈ site v, |w X| * Real.exp (a * X.card) * (1 + X.card * Real.exp (κ * X.card)) ≤ a

/-- The per-site summand of `MatchAt`. -/
def kp (w : Finset V → ℝ) (a κ : ℝ) (X : Finset V) : ℝ :=
  |w X| * Real.exp (a * X.card) * (1 + X.card * Real.exp (κ * X.card))

/-- The Kotecký–Preiss weight `|w X| e^{a|X|}`. -/
def eps (w : Finset V → ℝ) (a : ℝ) (X : Finset V) : ℝ := |w X| * Real.exp (a * X.card)

/-- The Dobrushin weight `log (1 + |w X| e^{a|X|})`. -/
def cKP (w : Finset V → ℝ) (a : ℝ) (X : Finset V) : ℝ := Real.log (1 + eps w a X)

theorem eps_nonneg (w : Finset V → ℝ) (a : ℝ) (X : Finset V) : 0 ≤ eps w a X :=
  mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem exp_cKP (w : Finset V → ℝ) (a : ℝ) (X : Finset V) :
    Real.exp (cKP w a X) - 1 = eps w a X := by
  unfold cKP
  rw [Real.exp_log (by linarith [eps_nonneg w a X])]
  ring

theorem eps_le_kp {w : Finset V → ℝ} {a κ : ℝ} (X : Finset V) : eps w a X ≤ kp w a κ X := by
  unfold kp
  have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) X.card) (Real.exp_pos (κ * X.card)).le
  have := eps_nonneg w a X
  unfold eps at this ⊢
  nlinarith

theorem kp_nonneg (w : Finset V → ℝ) (a κ : ℝ) (X : Finset V) : 0 ≤ kp w a κ X :=
  (eps_nonneg w a X).trans (eps_le_kp X)

/-- **A sum over the polymers meeting `X` is at most the sum over the sites of `X`.** -/
theorem sum_meet_le (f : Finset V → ℝ) (hf : ∀ Y, 0 ≤ f Y) (X : Finset V)
    (T : Finset (Finset V)) (hT : ∀ Y ∈ T, (X ∩ Y).Nonempty) :
    ∑ Y ∈ T, f Y ≤ ∑ v ∈ X, ∑ Y ∈ site v, f Y := by
  have hite : ∀ (v : V) (Y : Finset V), 0 ≤ (if v ∈ Y then f Y else 0) := fun v Y => by
    split_ifs
    · exact hf Y
    · exact le_rfl
  calc ∑ Y ∈ T, f Y ≤ ∑ Y ∈ T, ∑ v ∈ X, (if v ∈ Y then f Y else 0) := by
        refine sum_le_sum fun Y hY => ?_
        obtain ⟨v, hv⟩ := hT Y hY
        rw [mem_inter] at hv
        have := single_le_sum (f := fun v => if v ∈ Y then f Y else 0)
          (fun u _ => hite u Y) hv.1
        simpa [hv.2] using this
    _ ≤ ∑ Y, ∑ v ∈ X, (if v ∈ Y then f Y else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun Y _ _ => sum_nonneg fun u _ => hite u Y)
    _ = ∑ v ∈ X, ∑ Y, (if v ∈ Y then f Y else 0) := sum_comm
    _ = ∑ v ∈ X, ∑ Y ∈ site v, f Y := by simp only [site, sum_filter]

theorem sum_site_le {w : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt w a κ) (X : Finset V) :
    ∑ v ∈ X, ∑ Y ∈ site v, kp w a κ Y ≤ X.card * a := by
  calc ∑ v ∈ X, ∑ Y ∈ site v, kp w a κ Y ≤ ∑ _v ∈ X, a := sum_le_sum fun v _ => hM.2.2.2.2 v
    _ = X.card * a := by rw [sum_const, nsmul_eq_mul]

theorem mem_nbr_meet {X Y : Finset V} (h : Y ∈ nbr meet X) : Y ≠ X ∧ (X ∩ Y).Nonempty :=
  (mem_filter.1 h).2

/-- **Kotecký–Preiss gives Dobrushin** with `c X = log (1 + |w X| e^{a|X|})`. -/
theorem dob_of_matchAt {w : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt w a κ) :
    Dob meet w (cKP w a) := by
  intro X
  have hc0 : 0 ≤ cKP w a X := Real.log_nonneg (by linarith [eps_nonneg w a X])
  refine ⟨hc0, ?_⟩
  rcases X.eq_empty_or_nonempty with hX | hX
  · subst hX
    rw [hM.1, abs_zero, zero_mul]
    exact sub_nonneg.2 ((Real.exp_le_exp.2 (by linarith : -cKP w a ∅ ≤ 0)).trans_eq Real.exp_zero)
  have hXn : X ∉ nbr meet X := fun h => (mem_nbr_meet h).1 rfl
  have hcle : ∀ Y, cKP w a Y ≤ kp w a κ Y := fun Y => by
    unfold cKP
    have := Real.log_le_sub_one_of_pos (by linarith [eps_nonneg w a Y] : 0 < 1 + eps w a Y)
    linarith [eps_le_kp (w := w) (a := a) (κ := κ) Y]
  have hsum : cKP w a X + ∑ Y ∈ nbr meet X, cKP w a Y ≤ X.card * a := by
    rw [← sum_insert hXn]
    calc ∑ Y ∈ insert X (nbr meet X), cKP w a Y ≤ ∑ Y ∈ insert X (nbr meet X), kp w a κ Y :=
          sum_le_sum fun Y _ => hcle Y
      _ ≤ ∑ v ∈ X, ∑ Y ∈ site v, kp w a κ Y := by
          refine sum_meet_le _ (kp_nonneg w a κ) X _ fun Y hY => ?_
          rcases mem_insert.1 hY with h | h
          · rw [h, inter_self]; exact hX
          · exact (mem_nbr_meet h).2
      _ ≤ X.card * a := sum_site_le hM X
  have hexp : Real.exp (-cKP w a X) = (1 + eps w a X)⁻¹ := by
    unfold cKP
    rw [Real.exp_neg, Real.exp_log (by linarith [eps_nonneg w a X])]
  have hpos : 0 < 1 + eps w a X := by linarith [eps_nonneg w a X]
  calc |w X| * Real.exp (∑ Y ∈ nbr meet X, cKP w a Y)
      ≤ |w X| * Real.exp (a * X.card - cKP w a X) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (abs_nonneg _)
    _ = eps w a X * Real.exp (-cKP w a X) := by
        unfold eps
        rw [sub_eq_add_neg, Real.exp_add]; ring
    _ = 1 - Real.exp (-cKP w a X) := by
        rw [hexp]
        first | (field_simp; done) | (field_simp; ring)

/-- **Kotecký–Preiss gives the decay criterion** with `b = sz = |X|`. -/
theorem decayKP_of_matchAt {w : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt w a κ) (X : Finset V) :
    ∑ Y ∈ nbr meet X, (Real.exp (cKP w a Y) - 1) * (1 + (Y.card : ℝ) * Real.exp (κ * Y.card))
      ≤ X.card := by
  calc ∑ Y ∈ nbr meet X, (Real.exp (cKP w a Y) - 1) * (1 + (Y.card : ℝ) * Real.exp (κ * Y.card))
      = ∑ Y ∈ nbr meet X, kp w a κ Y := by
        refine sum_congr rfl fun Y _ => ?_
        rw [exp_cKP]; rfl
    _ ≤ ∑ v ∈ X, ∑ Y ∈ site v, kp w a κ Y :=
        sum_meet_le _ (kp_nonneg w a κ) X _ fun Y hY => (mem_nbr_meet hY).2
    _ ≤ X.card * a := sum_site_le hM X
    _ ≤ X.card := mul_le_of_le_one_right (Nat.cast_nonneg _) hM.2.2.1

/-- The distance of a polymer: the least `dset` over its sites. -/
def phi (dset : V → ℝ) (X : Finset V) : ℝ := if h : X.Nonempty then X.inf' h dset else 0

theorem phi_le (dset : V → ℝ) {X : Finset V} {x : V} (hx : x ∈ X) : phi dset X ≤ dset x := by
  rw [phi, dif_pos ⟨x, hx⟩]
  exact inf'_le _ hx

theorem phi_eq (dset : V → ℝ) {X : Finset V} (hX : X.Nonempty) : ∃ x ∈ X, phi dset X = dset x := by
  obtain ⟨x, hx, he⟩ := exists_mem_eq_inf' hX dset
  exact ⟨x, hx, by rw [phi, dif_pos hX, he]⟩

/-- **Exponential clustering from `MatchAt`**: `|Q S A U| ≤ |Λ| a e^{−κ R}` when every polymer of
`A` meets `Λ`, `dset ≥ R` on `Λ`, `dset ≤ 0` on the active polymers of `U`, `dset` is `1`-Lipschitz for
`ρ`, and every active polymer has `ρ`-diameter at most its size. -/
theorem cluster_sites {w : Finset V → ℝ} {a κ : ℝ} (hM : MatchAt w a κ)
    {ρ : V → V → ℝ} {dset : V → ℝ} (hlip : ∀ x y, dset x ≤ dset y + ρ x y)
    (hdiam : ∀ X, w X ≠ 0 → ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card)
    {U : Finset (Finset V)} (hcore : ∀ Y ∈ U, w Y ≠ 0 → ∀ y ∈ Y, dset y ≤ 0)
    {Λ : Finset V} {R : ℝ} (hΛ : ∀ y ∈ Λ, R ≤ dset y)
    {A : Finset (Finset V)} (hA : ∀ X ∈ A, (X ∩ Λ).Nonempty) (hAU : ∀ X ∈ A, X ∉ U)
    (S : Finset (Finset V)) :
    |Q meet w S A U| ≤ Λ.card * a * Real.exp (-(κ * R)) := by
  have hκ := hM.2.2.2.1
  have hφU : ∀ γ δ, δ ∈ nbr meet γ → w δ ≠ 0 → δ ∈ U → phi dset γ ≤ 0 := by
    intro γ δ hδ hw hU
    obtain ⟨z, hz⟩ := (mem_nbr_meet hδ).2
    rw [mem_inter] at hz
    exact (phi_le dset hz.1).trans (hcore δ hU hw z hz.2)
  have hφ : ∀ γ δ, δ ∈ nbr meet γ → w δ ≠ 0 →
      phi dset γ ≤ phi dset δ + (fun Y : Finset V => (Y.card : ℝ)) δ := by
    intro γ δ hδ hw
    obtain ⟨z, hz⟩ := (mem_nbr_meet hδ).2
    rw [mem_inter] at hz
    obtain ⟨x, hx, he⟩ := phi_eq dset ⟨z, hz.2⟩
    calc phi dset γ ≤ dset z := phi_le dset hz.1
      _ ≤ dset x + ρ z x := hlip z x
      _ ≤ phi dset δ + δ.card := by rw [he]; linarith [hdiam δ hw z hz.2 x hx]
  have hcl := cluster (sz := fun Y : Finset V => (Y.card : ℝ)) (b := fun Y : Finset V => (Y.card : ℝ))
    meet_symm (dob_of_matchAt hM) hκ (fun _ => Nat.cast_nonneg _) (decayKP_of_matchAt hM) hφU hφ S A
    hAU
  refine hcl.trans ?_
  have hterm : ∀ X ∈ A, (Real.exp (cKP w a X) - 1) * (X.card : ℝ) * Real.exp (-(κ * phi dset X))
      ≤ Real.exp (-(κ * R)) * kp w a κ X := by
    intro X hX
    rw [exp_cKP]
    by_cases hw : w X = 0
    · have : eps w a X = 0 := by unfold eps; rw [hw, abs_zero, zero_mul]
      rw [this, zero_mul, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (kp_nonneg w a κ X)
    obtain ⟨y, hy⟩ := hA X hX
    rw [mem_inter] at hy
    obtain ⟨x, hx, he⟩ := phi_eq dset ⟨y, hy.1⟩
    have hRφ : R ≤ phi dset X + X.card := by
      rw [he]
      linarith [hΛ y hy.2, hlip y x, hdiam X hw y hy.1 x hx]
    have hexp : Real.exp (-(κ * phi dset X)) ≤ Real.exp (-(κ * R)) * Real.exp (κ * X.card) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hRφ hκ])
    have hE := eps_nonneg w a X
    have hc : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    calc eps w a X * X.card * Real.exp (-(κ * phi dset X))
        ≤ eps w a X * X.card * (Real.exp (-(κ * R)) * Real.exp (κ * X.card)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hE hc)
      _ ≤ eps w a X * X.card * (Real.exp (-(κ * R)) * Real.exp (κ * X.card))
          + eps w a X * Real.exp (-(κ * R)) := by
          have := mul_nonneg hE (Real.exp_pos (-(κ * R))).le
          linarith
      _ = Real.exp (-(κ * R)) * kp w a κ X := by unfold kp eps; ring
  calc ∑ X ∈ A, (Real.exp (cKP w a X) - 1) * (X.card : ℝ) * Real.exp (-(κ * phi dset X))
      ≤ ∑ X ∈ A, Real.exp (-(κ * R)) * kp w a κ X := sum_le_sum hterm
    _ = Real.exp (-(κ * R)) * ∑ X ∈ A, kp w a κ X := by rw [mul_sum]
    _ ≤ Real.exp (-(κ * R)) * (Λ.card * a) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine (sum_meet_le _ (kp_nonneg w a κ) Λ A fun X hX => ?_).trans (sum_site_le hM Λ)
        rw [inter_comm]; exact hA X hX
    _ = Λ.card * a * Real.exp (-(κ * R)) := by ring

/-- **Control**: a site of total activity above `1/2` fails `MatchAt`. -/
theorem not_matchAt_of_heavy {w : Finset V → ℝ} {a κ : ℝ} {v : V}
    (h : 1 / 2 < ∑ X ∈ site v, |w X|) : ¬ MatchAt w a κ := by
  intro hM
  obtain ⟨-, ha0, ha1, hκ, hs⟩ := hM
  have hge : ∀ X ∈ site v, 2 * |w X| ≤ kp w a κ X := by
    intro X hX
    have hc : (1 : ℝ) ≤ X.card := Nat.one_le_cast.2 (card_pos.2 ⟨v, (mem_filter.1 hX).2⟩)
    have h1 : 1 ≤ Real.exp (a * X.card) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (κ * X.card) := Real.one_le_exp (by positivity)
    have h3 : 2 ≤ 1 + (X.card : ℝ) * Real.exp (κ * X.card) := by nlinarith
    have hEF : 2 ≤ Real.exp (a * X.card) * (1 + (X.card : ℝ) * Real.exp (κ * X.card)) := by
      have := mul_le_mul h1 h3 zero_le_two (Real.exp_pos _).le
      linarith
    calc 2 * |w X| = |w X| * 2 := by ring
      _ ≤ |w X| * (Real.exp (a * X.card) * (1 + (X.card : ℝ) * Real.exp (κ * X.card))) :=
          mul_le_mul_of_nonneg_left hEF (abs_nonneg _)
      _ = kp w a κ X := by unfold kp; ring
  have h2 := sum_le_sum hge
  rw [← mul_sum] at h2
  have h3 := hs v
  have : ∑ X ∈ site v, kp w a κ X ≤ a := h3
  linarith

/-! ## 4. The owner's three routes -/

/-- **The engine of the routes**: a count `Σ_{X∋v, |X|=n} |w X| ≤ (z e^{−τ})ⁿ` (entropy `z` and cost
`τ` per chunk) and `4 z e^{1+κ−τ} ≤ 1` give `MatchAt w 1 κ`. -/
theorem matchAt_of_count {w : Finset V → ℝ} {z τ κ : ℝ} (hw0 : w ∅ = 0) (hz : 0 ≤ z) (hκ : 0 ≤ κ)
    (hcount : ∀ v n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w X|
      ≤ (z * Real.exp (-τ)) ^ n)
    (hq : 4 * z * Real.exp (1 + κ - τ) ≤ 1) : MatchAt w 1 κ := by
  refine ⟨hw0, zero_le_one, le_rfl, hκ, fun v => ?_⟩
  set q := 2 * z * Real.exp (1 + κ - τ) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by rw [hq_def]; linarith
  have hqe : z * Real.exp (-τ) * (2 * Real.exp (1 + κ)) = q := by
    rw [hq_def, show 1 + κ - τ = (1 + κ) + -τ by ring, Real.exp_add (1 + κ) (-τ)]; ring
  have hfX : ∀ n : ℕ, Real.exp (1 * (n : ℝ)) * (1 + n * Real.exp (κ * n))
      ≤ (2 * Real.exp (1 + κ)) ^ n := by
    intro n
    have hb : (1 : ℝ) + n ≤ 2 ^ n := by
      have := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) n
      norm_num at this ⊢
      linarith
    have he : 1 ≤ Real.exp (κ * n) := Real.one_le_exp (by positivity)
    have h2 : (2 * Real.exp (1 + κ)) ^ n = Real.exp (1 * n) * (2 ^ n * Real.exp (κ * n)) := by
      rw [mul_pow, ← Real.exp_nat_mul, show (n : ℝ) * (1 + κ) = 1 * n + κ * n by ring,
        Real.exp_add]
      ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_right hb (zero_le_one.trans he)
    have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hmaps : ∀ X ∈ site v, X.card ∈ Ico 1 (Fintype.card V + 1) := by
    intro X hX
    rw [mem_Ico]
    exact ⟨card_pos.2 ⟨v, (mem_filter.1 hX).2⟩, Nat.lt_succ_of_le (card_le_univ X)⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hn : ∀ n ∈ Ico 1 (Fintype.card V + 1),
      ∑ X ∈ (site v).filter (fun X => X.card = n),
        |w X| * Real.exp (1 * X.card) * (1 + X.card * Real.exp (κ * X.card)) ≤ q ^ n := by
    intro n _
    calc ∑ X ∈ (site v).filter (fun X => X.card = n),
          |w X| * Real.exp (1 * X.card) * (1 + X.card * Real.exp (κ * X.card))
        = ∑ X ∈ (site v).filter (fun X => X.card = n),
          |w X| * (Real.exp (1 * (n : ℝ)) * (1 + n * Real.exp (κ * n))) := by
          refine sum_congr rfl fun X hX => ?_
          rw [(mem_filter.1 hX).2]; ring
      _ ≤ ∑ X ∈ (site v).filter (fun X => X.card = n), |w X| * (2 * Real.exp (1 + κ)) ^ n :=
          sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hfX n) (abs_nonneg _)
      _ = (∑ X ∈ (site v).filter (fun X => X.card = n), |w X|) * (2 * Real.exp (1 + κ)) ^ n := by
          rw [sum_mul]
      _ ≤ (z * Real.exp (-τ)) ^ n * (2 * Real.exp (1 + κ)) ^ n :=
          mul_le_mul_of_nonneg_right (hcount v n) (by positivity)
      _ = q ^ n := by rw [← mul_pow, hqe]
  calc ∑ n ∈ Ico 1 (Fintype.card V + 1), ∑ X ∈ (site v).filter (fun X => X.card = n),
        |w X| * Real.exp (1 * X.card) * (1 + X.card * Real.exp (κ * X.card))
      ≤ ∑ n ∈ Ico 1 (Fintype.card V + 1), q ^ n := sum_le_sum hn
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    _ ≤ 1 := by
        rw [pow_one, div_le_one (by linarith)]
        linarith

/-- **Route (1), the length**: for `σ > 0`, `k > 0` there is `ℓ₀` such that the cost
`τ = σ k ℓ²` of an edge across chunks of side `ℓ ≥ ℓ₀` meets `4 z e^{1+κ−τ} ≤ 1`. -/
theorem exists_length_match {z σ k κ : ℝ} (hz : 0 ≤ z) (hσ : 0 < σ) (hk : 0 < k) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ ℓ, ℓ₀ ≤ ℓ → 4 * z * Real.exp (1 + κ - σ * k * ℓ ^ 2) ≤ 1 := by
  set M := |1 + κ + Real.log (4 * z + 1)| + 1 with hMdef
  have hσk : 0 < σ * k := mul_pos hσ hk
  refine ⟨max 1 (M / (σ * k)), lt_of_lt_of_le one_pos (le_max_left _ _), fun ℓ hℓ => ?_⟩
  have hℓ1 : 1 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓM : M / (σ * k) ≤ ℓ := (le_max_right _ _).trans hℓ
  have hsq : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hM : M ≤ σ * k * ℓ ^ 2 := by
    have h1 := (div_le_iff₀ hσk).1 hℓM
    nlinarith [mul_le_mul_of_nonneg_left hsq hσk.le]
  have hpos : 0 < 4 * z + 1 := by linarith
  have hexp : Real.exp (1 + κ - σ * k * ℓ ^ 2) ≤ (4 * z + 1)⁻¹ := by
    rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith [le_abs_self (1 + κ + Real.log (4 * z + 1)), hMdef])
  calc 4 * z * Real.exp (1 + κ - σ * k * ℓ ^ 2)
      ≤ (4 * z + 1) * Real.exp (1 + κ - σ * k * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (4 * z + 1) * (4 * z + 1)⁻¹ := mul_le_mul_of_nonneg_left hexp hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

end Sites

/-- **Route (1), zoom out**: chunk theories at side `ℓ` whose activities obey the count with cost
`σ k ℓ²` per chunk (the effective tension of the chunk theory times the area of a face) satisfy
`MatchAt` at every `ℓ ≥ ℓ₀`. The count at every `ℓ` is the input: it is the control of the flow from
`r*` to `ℓ`. -/
theorem matchAt_of_tension {V : ℝ → Type*} [∀ ℓ, Fintype (V ℓ)] [∀ ℓ, DecidableEq (V ℓ)]
    (w : ∀ ℓ, Finset (V ℓ) → ℝ) {z σ k κ : ℝ} (hz : 0 ≤ z) (hσ : 0 < σ) (hk : 0 < k)
    (hκ : 0 ≤ κ) (hw0 : ∀ ℓ, w ℓ ∅ = 0)
    (hcount : ∀ ℓ (v : V ℓ) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w ℓ X|
      ≤ (z * Real.exp (-(σ * k * ℓ ^ 2))) ^ n) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ ℓ, ℓ₀ ≤ ℓ → MatchAt (w ℓ) 1 κ := by
  obtain ⟨ℓ₀, hℓ₀, h⟩ := exists_length_match (κ := κ) hz hσ hk
  exact ⟨ℓ₀, hℓ₀, fun ℓ hℓ => matchAt_of_count (hw0 ℓ) hz hκ (hcount ℓ) (h ℓ hℓ)⟩

section States

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `k` readable states on each of `n` chunks: `kⁿ` labellings. -/
theorem card_labelled (n k : ℕ) : Fintype.card (Fin n → Fin k) = k ^ n := by simp

/-- Shape entropy times state entropy: `(zs e^{−c})ⁿ kⁿ = ((zs k) e^{−c})ⁿ`. -/
theorem entropy_split (zs k c : ℝ) (n : ℕ) :
    (zs * Real.exp (-c)) ^ n * k ^ n = ((zs * k) * Real.exp (-c)) ^ n := by
  rw [← mul_pow]; ring

/-- **Route (2), few states per chunk**: entropy `log (zs k)` per chunk (shapes `zs`, states `k`)
and a cost `c ≥ log (zs k) + log 4 + 1 + κ` per chunk give `MatchAt w 1 κ`. -/
theorem matchAt_of_states {w : Finset V → ℝ} {zs k c κ : ℝ} (hw0 : w ∅ = 0) (hzs : 0 < zs)
    (hk : 0 < k) (hκ : 0 ≤ κ)
    (hcount : ∀ v n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w X|
      ≤ ((zs * k) * Real.exp (-c)) ^ n)
    (hc : Real.log (zs * k) + Real.log 4 + 1 + κ ≤ c) : MatchAt w 1 κ := by
  have hz := mul_pos hzs hk
  refine matchAt_of_count hw0 hz.le hκ hcount ?_
  have h : Real.exp (1 + κ - c) ≤ Real.exp (-(Real.log (4 * (zs * k)))) := by
    refine Real.exp_le_exp.2 ?_
    rw [Real.log_mul (by norm_num) hz.ne']
    linarith
  rw [Real.exp_neg, Real.exp_log (by positivity)] at h
  calc 4 * (zs * k) * Real.exp (1 + κ - c) ≤ 4 * (zs * k) * (4 * (zs * k))⁻¹ :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

end States

/-- **Route (3), a transported chunk law keeps the match**, with the same constants. -/
theorem matchAt_map {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (e : V' ≃ V) {w : Finset V → ℝ} {a κ : ℝ} (h : MatchAt w a κ) :
    MatchAt (fun Y : Finset V' => w (Y.map e.toEmbedding)) a κ := by
  obtain ⟨h0, ha0, ha1, hκ, hs⟩ := h
  refine ⟨by simpa using h0, ha0, ha1, hκ, fun v' => ?_⟩
  refine (Finset.sum_equiv e.finsetCongr (fun Y => ?_) (fun Y _ => ?_)).trans_le (hs (e v'))
  · simp [site, Equiv.finsetCongr_apply]
  · simp [Equiv.finsetCongr_apply, card_map]

/-- **Route (3), fixed point**: if the chunk law at step `k+1` is the law at step `k` transported by a
bijection of chunks, `MatchAt` at step `k₀` holds at every `k ≥ k₀` with the same `(a, κ)`. -/
theorem matchAt_of_fixedPoint {V : ℕ → Type*} [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
    (w : ∀ k, Finset (V k) → ℝ) (e : ∀ k, V (k + 1) ≃ V k)
    (hinv : ∀ k Y, w (k + 1) Y = w k (Y.map (e k).toEmbedding)) {a κ : ℝ} {k₀ : ℕ}
    (h : MatchAt (w k₀) a κ) : ∀ k, k₀ ≤ k → MatchAt (w k) a κ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    have hw : w (k + 1) = fun Y => w k (Y.map (e k).toEmbedding) := funext (hinv k)
    rw [hw]
    exact matchAt_map (e k) ih

/-! ## 3. To (B) -/

section Link

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **Cross terms dominated by a polymer interaction**: for each pair of cells `i ≠ j` a polymer system
with `MatchAt w a κ`, the geometry of `cluster_sites`, a region of at most `M` sites at distance
`R ≥ d(i,j) L − r₀`, and `|⟪P vᵢ, P vⱼ⟫| ≤ Kx |Q| ‖vᵢ‖ ‖vⱼ‖`. -/
def PolymerCross (P : E →L[ℝ] E) (v : Fin n → E) (d : Fin n → Fin n → ℕ)
    (Kx M a κ L r₀ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (w : Finset V → ℝ)
    (ρ : V → V → ℝ) (dset : V → ℝ) (U A S : Finset (Finset V)) (Λ : Finset V) (R : ℝ),
    MatchAt w a κ ∧ (∀ x y, dset x ≤ dset y + ρ x y) ∧
    (∀ X, w X ≠ 0 → ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card) ∧
    (∀ Y ∈ U, w Y ≠ 0 → ∀ y ∈ Y, dset y ≤ 0) ∧ (∀ y ∈ Λ, R ≤ dset y) ∧
    (∀ X ∈ A, (X ∩ Λ).Nonempty) ∧ (∀ X ∈ A, X ∉ U) ∧ (Λ.card : ℝ) ≤ M ∧
    (d i j : ℝ) * L - r₀ ≤ R ∧
    |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |Q meet w S A U| * (‖v i‖ * ‖v j‖)

/-- **`PolymerCross` is screening**: `CellLinks.Screens` with `Ke = Kx M a e^{κ r₀}`,
`ξ = ℓ/(κ L)`. -/
theorem screens_of_polymerCross {P : E →L[ℝ] E} {v : Fin n → E} {d : Fin n → Fin n → ℕ}
    {Kx M a κ L r₀ ℓ : ℝ} (hKx : 0 ≤ Kx) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (h : PolymerCross P v d Kx M a κ L r₀) :
    CellLinks.Screens P v d (Kx * M * a * Real.exp (κ * r₀)) (ℓ / (κ * L)) ℓ := by
  intro i j hij
  obtain ⟨V, _, _, w, ρ, dset, U, A, S, Λ, R, hM, hlip, hdiam, hcore, hΛ, hA, hAU, hcard, hR, hx⟩ :=
    h i j hij
  have hcl := cluster_sites hM hlip hdiam hcore hΛ hA hAU S
  have ha : 0 ≤ a := hM.2.1
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hcard
  have hd : (d i j : ℝ) * ℓ / (ℓ / (κ * L)) = d i j * (κ * L) := by
    rw [div_div_eq_mul_div, mul_right_comm, mul_div_cancel_right₀ _ hℓ.ne']
  have hexp : Real.exp (-(κ * R))
      ≤ Real.exp (κ * r₀) * Real.exp (-((d i j : ℝ) * ℓ / (ℓ / (κ * L)))) := by
    rw [← Real.exp_add, hd]
    exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hR hκ.le])
  have hvv : 0 ≤ ‖v i‖ * ‖v j‖ := by positivity
  have hstep : (Λ.card : ℝ) * a * Real.exp (-(κ * R))
      ≤ M * a * (Real.exp (κ * r₀) * Real.exp (-((d i j : ℝ) * ℓ / (ℓ / (κ * L))))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcard ha) hexp (Real.exp_pos _).le (mul_nonneg hM0 ha)
  calc |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |Q meet w S A U| * (‖v i‖ * ‖v j‖) := hx
    _ ≤ Kx * (Λ.card * a * Real.exp (-(κ * R))) * (‖v i‖ * ‖v j‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcl hKx) hvv
    _ ≤ Kx * (M * a * (Real.exp (κ * r₀) * Real.exp (-((d i j : ℝ) * ℓ / (ℓ / (κ * L))))))
          * (‖v i‖ * ‖v j‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hKx) hvv
    _ = Kx * M * a * Real.exp (κ * r₀) * Real.exp (-((d i j : ℝ) * ℓ / (ℓ / (κ * L))))
          * (‖v i‖ * ‖v j‖) := by ring

/-- **(A) and (B) on the Wilson box from the match**: the cell rate and `PolymerCross` for the pieces
of the cell chain at level `r`, at every aperture `m > 0` and zoom `k ≥ K₀ ≥ r`, with one set of
constants, give `RelFloorM` with one rate and one zoom. -/
theorem relFloorM_of_polymerCross {N : ℕ} (X : CellLinks.BoxParams N) (hN : N ≠ 0) {r K₀ : ℕ}
    (hrK : r ≤ K₀) {ρc Kx M a κ L r₀ A' : ℝ} {p : ℕ} (hρc : 0 < ρc) (hKx : 0 ≤ Kx) (hM0 : 0 ≤ M)
    (ha0 : 0 ≤ a) (hκ : 0 < κ) (hL : 0 < L) (hA : 0 ≤ A')
    (h1 : ρc ^ 2 + Kx * M * a * Real.exp (κ * r₀) * A' * UniformAperture.edgeSum p
      (NonAbelianForget.edgeRate (1 / (X.a₀ / 2 ^ r / (κ * L))) 0 (X.a₀ / 2 ^ r)) < 1)
    (hD : ∀ m, 0 < m → UniformAperture.ShellCount (CellLinks.boxDist X.μ m r) A' p)
    (hS : ∀ m (hm : 0 < m) k (hk : K₀ ≤ k) (g : MeasureTheory.Lp ℝ 2 (X.slab hN m k).π),
      inner ℝ g (SlabKernelOperator.oneLp (X.slab hN m k).π) = 0 →
      (∀ i, ‖(X.slab hN m k).P ((X.cellChain hN r m k (hrK.trans hk) hm).piece g i)‖ ^ 2
        ≤ ρc ^ 2 * ‖(X.cellChain hN r m k (hrK.trans hk) hm).piece g i‖ ^ 2) ∧
      PolymerCross (X.slab hN m k).P ((X.cellChain hN r m k (hrK.trans hk) hm).piece g)
        (CellLinks.boxDist X.μ m r) Kx M a κ L r₀) :
    SlabMeasure.RelFloorM (X.box.slab hN) (fun _ => UniformAperture.cellRate ρc
      (Kx * M * a * Real.exp (κ * r₀) * A' * UniformAperture.edgeSum p
        (NonAbelianForget.edgeRate (1 / (X.a₀ / 2 ^ r / (κ * L))) 0 (X.a₀ / 2 ^ r))))
      (fun _ => K₀) := by
  have hℓ : 0 < X.a₀ / 2 ^ r := by have := X.ha₀; positivity
  have hKe : 0 ≤ Kx * M * a * Real.exp (κ * r₀) :=
    mul_nonneg (mul_nonneg (mul_nonneg hKx hM0) ha0) (Real.exp_pos _).le
  exact X.relFloorM_of_screened hN hrK hρc hKe hA (div_pos hℓ (mul_pos hκ hL)) h1 hD
    (fun m hm k hk g hg => ⟨(hS m hm k hk g hg).1,
      screens_of_polymerCross hKx hκ hℓ (hS m hm k hk g hg).2⟩)

end Link

#print axioms Z_rec
#print axioms dob_bounds
#print axioms abs_L_le
#print axioms F_lip
#print axioms decay
#print axioms cluster
#print axioms truncated
#print axioms dob_of_matchAt
#print axioms decayKP_of_matchAt
#print axioms cluster_sites
#print axioms not_matchAt_of_heavy
#print axioms matchAt_of_count
#print axioms exists_length_match
#print axioms matchAt_of_tension
#print axioms matchAt_of_states
#print axioms matchAt_map
#print axioms matchAt_of_fixedPoint
#print axioms screens_of_polymerCross
#print axioms relFloorM_of_polymerCross

end MassGap.MatchAt
