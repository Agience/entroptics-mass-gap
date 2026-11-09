import Mathlib
import MassGap.ChunkActivity
import MassGap.PlaqVariance
import MassGap.HaarVariance

/-!
# MassGap.ChunkLinks — the Wilson polymer gas on links, read by `PolymerCross`

`ChunkActivity.partition_eq_polymerZ` writes the Wilson partition function as the hard-core gas of
the activities `act` on plaquette polymers, incompatible when they touch or overlap (`Inc`).
`MatchAt`'s clustering (`cluster_sites`) and `PolymerCross` read the gas on site polymers that are
incompatible when they overlap (`meet`). This module carries the Wilson gas over to link polymers,
where `Inc` becomes `meet`, so that `PolymerCross` reads the Wilson gas's own interaction.

## Choice of route

The link transport is used, not a generalisation of `MatchAt` to an arbitrary incompatibility.
`cluster_sites`, `screens_of_polymerCross` and `relFloorM_of_polymerCross` are all stated for
`Q meet`; generalising would restate each of them for `Inc`. The transport needs one identity of
partition functions (`Z_push`) and lands on `meet` itself, so every `MatchAt` consumer applies
unchanged.

## 1. Transport of a hard-core gas (`pre`, `fib`, `push`, `Z_clique`, `Z_push`)

For `g : Pol → Pol'`, `push g w y = Σ_{g x = y} w x`, `pre g S' = {x | g x ∈ S'}`.
`Z_clique`: for a clique `C ⊆ P` (pairwise incompatible),
`Z P = Z (P∖C) + Σ_{x∈C} w x · Z (P∖C∖nbr x)`. `Z_push`: if `inc x y ↔ inc' (g x) (g y)` and
distinct points of one fibre are incompatible, then `Z inc' (push g w) S' = Z inc w (pre g S')` for
every `S'` (strong induction on `S'`, `MatchAt.Z_rec` against `Z_clique` on a fibre).

## 2. The link gas (`supp`, `inc_iff_meet`, `linkAct`, `linkZ_eq`, `partition_eq_linkZ`, `linkQ_eq`)

`supp bd X = ⋃_{p∈X} linkSupp bd p`. When every plaquette has a link (`hbd`),
`Inc bd X Y ↔ meet (supp X) (supp Y)` (`inc_iff_meet`, from `StrongCoupling.Touch`: two plaquettes
touch when their link supports meet). With `linkAct bd β = push (supp bd) (act bd β)`:

    MatchAt.Z meet (linkAct bd β) S' = MatchAt.Z (Inc bd) (act bd β) (pre (supp bd) S'),

the Wilson partition function is `MatchAt.Z meet (linkAct bd β) univ`, and
`Q meet (linkAct bd β) S A U = Q (Inc bd) (act bd β) (pre S) (pre A) (pre U)` (`linkQ_eq`).

## 3. The count and the match on links (`countAt_link`, `matchAt_link_of_decay`)

`countAt_link`: with at most `c > 0` links per plaquette, at most `M ≥ 1` plaquettes per link, the
rooted connected count `#connSets v m ≤ Kᵐ`, connected support, `Decay w t`, `t ≥ 0` and
`2 K e^{−t/2} ≤ 1`, the pushed activities satisfy `CountAt (push (supp bd) w) M (t/(2c))`.
Each link polymer `Λ ∋ l` of size `n` collects plaquette polymers `X` with `n ≤ c |X|`; half of the
cost `e^{−t|X|}` pays `e^{−(t/(2c)) n}`, the other half sums the connected polymers through each of
the `≤ M` plaquettes on `l` to at most `1`.

On the 4D torus (`c = 4`, `M = 16`, `K = 4225`): `countAt_link_hypercubic`, and
`matchAt_link_of_decay`: `8 · kpCost 16 κ ≤ t` gives `MatchAt (push (supp bd) w) 1 κ`.
`matchAt_linkAct_of_tau`: `8 · kpCost 16 κ ≤ tau β` gives `MatchAt (linkAct bd β) 1 κ`;
`exists_beta_matchAt_linkAct`: such a `β > 0` exists for every `κ ≥ 0`.

## 4. `PolymerCross` on the Wilson gas (`WilsonLinkPolymerCross`, `polymerCross_of_wilsonLink`)

`WilsonLinkPolymerCross` is the clause list of `MatchAt.PolymerCross` other than `MatchAt`, with the
polymer type `Finset (Link 4 nC)`, `w = linkAct` and the cross term bounded by
`Q (Inc bd) (act bd β)` of plaquette families `pre S, pre A, pre U`: the interaction of the Wilson
gas. `polymerCross_of_wilsonLink` proves `PolymerCross … 1 κ …` from it and
`8 · kpCost 16 κ ≤ tau β`. Every clause other than `MatchAt`, in particular the cross-term bound,
stays a hypothesis.

Under `8 · kpCost 16 κ ≤ tau β` the clause forces exact orthogonality beyond a range fixed by the
torus: `CrossTerm.cross_zero_of_far` gives `⟪P vᵢ, P vⱼ⟫ = 0` whenever
`d(i,j) L − r₀ > CrossTerm.farRange nC = (|Link 4 nC| + 1)|Link 4 nC|`, because on the finite torus
`Q` vanishes once `A` and `U` are that far apart (`CrossTerm.Q_eq_zero_of_far`), and a lower bound on
`|Q|` at every separation is false (`CrossTerm.not_qFloor`). So this clause is not a usable route to
(B); the (B) input of the bridge is `CellLinks.ScreenedCells`, screening with one `(Ke, ξ)` at every
aperture and zoom.

## 5. The one-plaquette activity is nonzero (`act_singleton_ne_zero`, `chunkDecay_wilson_witness'`)

`act_singleton_ne_zero_of`: `β > 0` and a configuration with `φ_p ≠ 0` give `act {p} ≠ 0`
(the integrand `e^{−βφ_p} − 1 ≤ 0` is continuous and nonzero somewhere; product Haar charges open
sets). `act_singleton_ne_zero`: on the 4D torus with `2 ≤ N`, `2 ≤ n` and `p` spanning two distinct
directions, `act {p} ≠ 0` at every `β > 0`. The hypotheses exclude plaquettes with equal directions,
whose boundary word retraces itself; `2 ≤ n` is what the one-link witness uses (at side `1` the four
links collapse to two and the holonomy is a commutator). Non-vanishing is proved for the plaquette
`act`, not for `linkAct`. `chunkDecay_wilson_witness'` adds this conjunct to
`ChunkActivity.chunkDecay_wilson_witness`.

DERIVED (module-wide): `0` the empty polymer and signs; `1` the empty family, the KP constant and
`M ≥ 1`; `2` the halving of the cost `t` and the geometric ratio `≤ 1/2`; `4` the links per plaquette
of the hypercubic boundary word and the dimension; `16 = 4 · 4` the plaquettes per link
(`linkMult_bd_le`); `4225 = (16·4 + 1)²` the entropy of `card_connSets_le_hypercubic`;
`8 = 2 · 4`; `8450 = 2 · 4225`, below `65⁴`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ChunkLinks

open Finset MeasureTheory
open MassGap.StrongCoupling MassGap.PolymerCount MassGap.NoTransitionFlow MassGap.ChunkActivity
open MassGap.WilsonAction MassGap.WilsonLattice MassGap.WilsonReal MassGap.CompactGauge
  MassGap.LatticeGauge

/-! ## 1. Transport of a hard-core gas -/

section Push

variable {Pol Pol' : Type*} [Fintype Pol] [DecidableEq Pol] [Fintype Pol'] [DecidableEq Pol']

/-- The polymers whose image lies in `S'`. -/
def pre (g : Pol → Pol') (S' : Finset Pol') : Finset Pol := univ.filter fun x => g x ∈ S'

/-- The fibre of `g` over `y`. -/
def fib (g : Pol → Pol') (y : Pol') : Finset Pol := univ.filter fun x => g x = y

/-- **The pushed activity** `Σ_{g x = y} w x`. -/
def push (g : Pol → Pol') (w : Pol → ℝ) (y : Pol') : ℝ := ∑ x ∈ fib g y, w x

omit [DecidableEq Pol] [Fintype Pol'] in
theorem mem_pre {g : Pol → Pol'} {S' : Finset Pol'} {x : Pol} : x ∈ pre g S' ↔ g x ∈ S' := by
  simp [pre]

omit [DecidableEq Pol] [Fintype Pol'] in
theorem mem_fib {g : Pol → Pol'} {y : Pol'} {x : Pol} : x ∈ fib g y ↔ g x = y := by
  simp [fib]

omit [Fintype Pol'] in
theorem pre_sdiff (g : Pol → Pol') (S T : Finset Pol') : pre g (S \ T) = pre g S \ pre g T := by
  ext x
  simp [pre]

omit [DecidableEq Pol] in
theorem pre_univ (g : Pol → Pol') : pre g (univ : Finset Pol') = univ := by
  ext x
  simp [pre]

omit [DecidableEq Pol] [Fintype Pol'] in
/-- **Summing the fibres over `T` is summing over the preimage of `T`.** -/
theorem sum_fib_eq (g : Pol → Pol') (f : Pol → ℝ) (T : Finset Pol') :
    ∑ y ∈ T, ∑ x ∈ fib g y, f x = ∑ x ∈ pre g T, f x := by
  rw [← sum_fiberwise_of_maps_to (s := pre g T) (t := T) (g := g) (fun x hx => mem_pre.1 hx)]
  refine sum_congr rfl fun y hy => ?_
  congr 1
  ext x
  rw [mem_fib, mem_filter, mem_pre]
  constructor
  · intro h
    exact ⟨h ▸ hy, h⟩
  · exact fun h => h.2

/-- **Removing a clique**: for `C ⊆ P` pairwise incompatible,
`Z P = Z (P∖C) + Σ_{x∈C} w x · Z (P∖C∖nbr x)`. -/
theorem Z_clique {inc : Pol → Pol → Prop} [DecidableRel inc] (hs : MatchAt.SymmRel inc)
    (w : Pol → ℝ) {P C : Finset Pol} (hCP : C ⊆ P)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → inc x y) :
    MatchAt.Z inc w P = MatchAt.Z inc w (P \ C)
      + ∑ x ∈ C, w x * MatchAt.Z inc w ((P \ C) \ MatchAt.nbr inc x) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert c C hc ih =>
    have hCP' : C ⊆ P := (subset_insert c C).trans hCP
    have hC' : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → inc x y := fun x hx y hy =>
      hC x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
    have hcm : c ∈ P \ C := mem_sdiff.2 ⟨hCP (mem_insert_self c C), hc⟩
    have hsum : ∑ x ∈ C, w x * MatchAt.Z inc w ((P \ C) \ MatchAt.nbr inc x)
        = ∑ x ∈ C, w x * MatchAt.Z inc w ((P \ insert c C) \ MatchAt.nbr inc x) := by
      refine sum_congr rfl fun x hx => ?_
      have hxc : c ≠ x := by
        rintro rfl
        exact hc hx
      have hinc : inc x c := hC x (mem_insert_of_mem hx) c (mem_insert_self _ _) hxc.symm
      congr 2
      ext y
      simp only [mem_sdiff, mem_insert, MatchAt.nbr, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hyP, hyC⟩, hyn⟩
        refine ⟨⟨hyP, ?_⟩, hyn⟩
        rintro (h | h)
        · rw [h] at hyn
          exact hyn ⟨hxc, hinc⟩
        · exact hyC h
      · rintro ⟨⟨hyP, hyC⟩, hyn⟩
        exact ⟨⟨hyP, fun h => hyC (Or.inr h)⟩, hyn⟩
    rw [ih hCP' hC', MatchAt.Z_rec hs hcm, sum_insert hc, ← sdiff_insert, hsum]
    ring

/-- **The partition function of a transported gas**: if `inc x y ↔ inc' (g x) (g y)` and distinct
points of a fibre are incompatible, `Z inc' (push g w) S' = Z inc w (pre g S')`. -/
theorem Z_push {inc : Pol → Pol → Prop} [DecidableRel inc] {inc' : Pol' → Pol' → Prop}
    [DecidableRel inc'] (hs : MatchAt.SymmRel inc) (hs' : MatchAt.SymmRel inc')
    (g : Pol → Pol') (w : Pol → ℝ) (hg : ∀ x y, inc x y ↔ inc' (g x) (g y))
    (hfib : ∀ x y, x ≠ y → g x = g y → inc x y) (S' : Finset Pol') :
    MatchAt.Z inc' (push g w) S' = MatchAt.Z inc w (pre g S') := by
  induction S' using Finset.strongInduction with
  | H S' ih =>
    rcases S'.eq_empty_or_nonempty with h | ⟨y, hy⟩
    · subst h
      have : pre g (∅ : Finset Pol') = ∅ := by
        ext x
        simp [pre]
      rw [this, MatchAt.Z_empty, MatchAt.Z_empty]
    · have hC : fib g y ⊆ pre g S' := fun x hx => mem_pre.2 ((mem_fib.1 hx) ▸ hy)
      have hcl : ∀ x ∈ fib g y, ∀ x' ∈ fib g y, x ≠ x' → inc x x' := fun x hx x' hx' hne =>
        hfib x x' hne ((mem_fib.1 hx).trans (mem_fib.1 hx').symm)
      have e1 : pre g S' \ fib g y = pre g (S'.erase y) := by
        ext x
        rw [mem_sdiff, mem_pre, mem_fib, mem_pre, mem_erase]
        tauto
      have e2 : ∀ x ∈ fib g y, (pre g S' \ fib g y) \ MatchAt.nbr inc x
          = pre g (S'.erase y \ MatchAt.nbr inc' y) := by
        intro x hx
        have hx' := mem_fib.1 hx
        ext x'
        simp only [MatchAt.nbr, mem_sdiff, mem_pre, mem_fib, mem_erase, mem_filter, mem_univ,
          true_and]
        rw [hg x x', hx']
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h2, h1⟩, fun h4 => h3 ⟨fun e => h2 (by rw [e]; exact hx'), h4.2⟩⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h2, h1⟩, fun h4 => h3 ⟨h1, h4.2⟩⟩
      have hsum : ∑ x ∈ fib g y, w x * MatchAt.Z inc w ((pre g S' \ fib g y) \ MatchAt.nbr inc x)
          = ∑ x ∈ fib g y, w x * MatchAt.Z inc w (pre g (S'.erase y \ MatchAt.nbr inc' y)) :=
        sum_congr rfl fun x hx => by rw [e2 x hx]
      rw [MatchAt.Z_rec hs' hy, Z_clique hs w hC hcl, hsum, e1, ← sum_mul,
        ih _ (erase_ssubset hy), ih _ ((sdiff_subset).trans_ssubset (erase_ssubset hy))]
      rfl

end Push

/-! ## 2. The link gas -/

section Links

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **The link support of a plaquette polymer**: the links of its plaquettes. -/
def supp (bd : Pq → List (Lk × Bool)) (X : Finset Pq) : Finset Lk := X.biUnion (linkSupp bd)

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
theorem mem_supp {bd : Pq → List (Lk × Bool)} {X : Finset Pq} {l : Lk} :
    l ∈ supp bd X ↔ ∃ p ∈ X, l ∈ linkSupp bd p := mem_biUnion

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- **Touch-or-overlap is overlap of link supports**, when every plaquette names a link. -/
theorem inc_iff_meet (bd : Pq → List (Lk × Bool)) (hbd : ∀ p, (linkSupp bd p).Nonempty)
    (X Y : Finset Pq) : Inc bd X Y ↔ MatchAt.meet (supp bd X) (supp bd Y) := by
  constructor
  · rintro ⟨p, hp, q, hq, h⟩
    rcases h with h | ⟨l, hl, hl'⟩
    · rw [← h] at hq
      obtain ⟨l, hl⟩ := hbd p
      exact ⟨l, mem_inter.2 ⟨mem_supp.2 ⟨p, hp, hl⟩, mem_supp.2 ⟨p, hq, hl⟩⟩⟩
    · exact ⟨l, mem_inter.2 ⟨mem_supp.2 ⟨p, hp, hl⟩, mem_supp.2 ⟨q, hq, hl'⟩⟩⟩
  · rintro ⟨l, hl⟩
    rw [mem_inter] at hl
    obtain ⟨p, hp, hlp⟩ := mem_supp.1 hl.1
    obtain ⟨q, hq, hlq⟩ := mem_supp.1 hl.2
    exact ⟨p, hp, q, hq, Or.inr ⟨l, hlp, hlq⟩⟩

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
theorem supp_eq_empty {bd : Pq → List (Lk × Bool)} (hbd : ∀ p, (linkSupp bd p).Nonempty)
    {X : Finset Pq} (h : supp bd X = ∅) : X = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨l, hl⟩ := hbd p
  have : l ∈ supp bd X := mem_supp.2 ⟨p, hp, hl⟩
  rw [h] at this
  exact notMem_empty l this

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- Distinct plaquette polymers with one link support are incompatible. -/
theorem inc_of_supp_eq (bd : Pq → List (Lk × Bool)) (hbd : ∀ p, (linkSupp bd p).Nonempty)
    (X Y : Finset Pq) (hXY : X ≠ Y) (h : supp bd X = supp bd Y) : Inc bd X Y := by
  rcases (supp bd X).eq_empty_or_nonempty with h0 | ⟨l, hl⟩
  · exact absurd ((supp_eq_empty hbd h0).trans (supp_eq_empty hbd (h ▸ h0)).symm) hXY
  · refine (inc_iff_meet bd hbd X Y).2 ⟨l, mem_inter.2 ⟨hl, h ▸ hl⟩⟩

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- The card of a link support is at most `c |X|` when each plaquette has at most `c` links. -/
theorem card_supp_le (bd : Pq → List (Lk × Bool)) {c : ℕ} (hc : ∀ p, (linkSupp bd p).card ≤ c)
    (X : Finset Pq) : (supp bd X).card ≤ c * X.card := by
  calc (supp bd X).card ≤ ∑ p ∈ X, (linkSupp bd p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ X, c := sum_le_sum fun p _ => hc p
    _ = c * X.card := by rw [sum_const, smul_eq_mul, mul_comm]

omit [Fintype Lk] [DecidableEq Pq] in
theorem push_supp_empty {bd : Pq → List (Lk × Bool)} (hbd : ∀ p, (linkSupp bd p).Nonempty)
    {w : Finset Pq → ℝ} (hw0 : w ∅ = 0) : push (supp bd) w ∅ = 0 := by
  unfold push
  refine sum_eq_zero fun X hX => ?_
  rw [supp_eq_empty hbd (mem_fib.1 hX), hw0]

/-- **The Wilson activities on link polymers**: `linkAct bd β Λ = Σ_{supp X = Λ} act bd β X`. -/
def linkAct (bd : Pq → List (Lk × Bool)) (β : ℝ) : Finset Lk → ℝ :=
  push (supp bd) (act (Nc := Nc) bd β)

omit [DecidableEq Pq] in
theorem linkAct_empty (bd : Pq → List (Lk × Bool)) (hbd : ∀ p, (linkSupp bd p).Nonempty)
    (β : ℝ) : linkAct (Nc := Nc) bd β ∅ = 0 :=
  push_supp_empty hbd (act_empty bd β)

/-- **The link gas is the Wilson gas**: `Z meet (linkAct bd β) S' = Z (Inc bd) (act bd β) (pre S')`
at every family `S'` of link polymers. -/
theorem linkZ_eq (bd : Pq → List (Lk × Bool)) (hbd : ∀ p, (linkSupp bd p).Nonempty) (β : ℝ)
    (S' : Finset (Finset Lk)) :
    MatchAt.Z MatchAt.meet (linkAct (Nc := Nc) bd β) S'
      = MatchAt.Z (Inc bd) (act (Nc := Nc) bd β) (pre (supp bd) S') :=
  Z_push (inc_symm bd) MatchAt.meet_symm (supp bd) _ (inc_iff_meet bd hbd)
    (inc_of_supp_eq bd hbd) S'

/-- **The Wilson partition function is the link-gas partition function.** -/
theorem partition_eq_linkZ (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (hbd : ∀ p, (linkSupp bd p).Nonempty) (β : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β
      = MatchAt.Z MatchAt.meet (linkAct (Nc := Nc) bd β) univ := by
  rw [partition_eq_polymerZ hN, linkZ_eq bd hbd, pre_univ, Finset.powerset_univ]

/-- **The link-gas interaction is the Wilson-gas interaction**:
`Q meet (linkAct bd β) S A U = Q (Inc bd) (act bd β) (pre S) (pre A) (pre U)`. -/
theorem linkQ_eq (bd : Pq → List (Lk × Bool)) (hbd : ∀ p, (linkSupp bd p).Nonempty) (β : ℝ)
    (S A U : Finset (Finset Lk)) :
    MatchAt.Q MatchAt.meet (linkAct (Nc := Nc) bd β) S A U
      = MatchAt.Q (Inc bd) (act (Nc := Nc) bd β) (pre (supp bd) S) (pre (supp bd) A)
          (pre (supp bd) U) := by
  unfold MatchAt.Q
  simp only [linkZ_eq bd hbd β, pre_sdiff]

/-! ## 3. The count and the match on links -/

open scoped Classical in
/-- The weight `e^{−s|X|}` on the active polymers of `w`, `0` elsewhere. -/
def gw (w : Finset Pq → ℝ) (s : ℝ) (X : Finset Pq) : ℝ :=
  if w X ≠ 0 then Real.exp (-(s * X.card)) else 0

omit [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq] in
theorem gw_nonneg (w : Finset Pq → ℝ) (s : ℝ) (X : Finset Pq) : 0 ≤ gw w s X := by
  unfold gw
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- **A geometric site sum**: a nonnegative `g` with `CountAt g z τ` and `2 z e^{−τ} ≤ 1` has
`Σ_{X ∋ v} g X ≤ 1`. -/
theorem sum_site_le_one {V : Type*} [Fintype V] [DecidableEq V] {g : Finset V → ℝ} {z τ : ℝ}
    (hg : ∀ X, 0 ≤ g X) (h : CountAt g z τ) (hz : 0 ≤ z)
    (hq : 2 * (z * Real.exp (-τ)) ≤ 1) (v : V) : ∑ X ∈ MatchAt.site v, g X ≤ 1 := by
  set q := z * Real.exp (-τ) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hmaps : ∀ X ∈ MatchAt.site v, X.card ∈ Ico 1 (Fintype.card V + 1) := by
    intro X hX
    rw [mem_Ico]
    exact ⟨card_pos.2 ⟨v, (mem_filter.1 hX).2⟩, Nat.lt_succ_of_le (card_le_univ X)⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ n ∈ Ico 1 (Fintype.card V + 1), ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), g X
      ≤ ∑ n ∈ Ico 1 (Fintype.card V + 1), q ^ n := by
        refine sum_le_sum fun n _ => le_trans (le_of_eq ?_) (h v n)
        exact sum_congr rfl fun X _ => (abs_of_nonneg (hg X)).symm
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    _ ≤ 1 := by
        rw [pow_one, div_le_one (by linarith)]
        linarith

/-- **The count on links**: at most `c > 0` links per plaquette, at most `M ≥ 1` plaquettes per
link, `#connSets v m ≤ Kᵐ`, connected support, `Decay w t` with `t ≥ 0` and `2 K e^{−t/2} ≤ 1` give
`CountAt (push (supp bd) w) M (t/(2c))`. -/
theorem countAt_link (bd : Pq → List (Lk × Bool)) {w : Finset Pq → ℝ} {t : ℝ} {c M K : ℕ}
    (hc0 : 0 < c) (hc : ∀ p, (linkSupp bd p).card ≤ c) (hM1 : 1 ≤ M)
    (hM : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ M)
    (hK : ∀ v m, (connSets bd v m).card ≤ K ^ m) (hwc : ConnSupp bd w) (hwd : Decay w t)
    (ht : 0 ≤ t) (hq : 2 * ((K : ℝ) * Real.exp (-(t / 2))) ≤ 1) :
    CountAt (push (supp bd) w) M (t / (2 * c)) := by
  classical
  set s := t / (2 * c) with hs
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 hc0
  -- the auxiliary weight and its site sum
  have hgc : ConnSupp bd (gw w (t / 2)) := by
    intro X hX
    refine hwc X fun h => hX ?_
    unfold gw
    rw [if_neg (not_not.2 h)]
  have hgd : Decay (gw w (t / 2)) (t / 2) := by
    intro X
    rw [abs_of_nonneg (gw_nonneg w _ X)]
    unfold gw
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hsite : ∀ p, ∑ X ∈ MatchAt.site p, gw w (t / 2) X ≤ 1 := fun p =>
    sum_site_le_one (gw_nonneg w _) (countAt_of_connSets_card bd hK hgc hgd)
      (Nat.cast_nonneg _) hq p
  intro l n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hemp : (MatchAt.site l).filter (fun Λ : Finset Lk => Λ.card = 0) = ∅ := by
      ext Λ
      simp only [mem_filter, MatchAt.site, mem_univ, true_and, notMem_empty, iff_false, not_and]
      intro hl h0
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hl
      exact notMem_empty l hl
    rw [hemp, sum_empty, pow_zero]
    exact zero_le_one
  set T := (MatchAt.site l).filter (fun Λ : Finset Lk => Λ.card = n) with hT
  set Pl := univ.filter fun p => l ∈ linkSupp bd p with hPl
  -- per-plaquette bound
  have hinner : ∀ p, ∑ X ∈ (pre (supp bd) T).filter (fun X => p ∈ X), |w X|
      ≤ Real.exp (-(s * n)) := by
    intro p
    calc ∑ X ∈ (pre (supp bd) T).filter (fun X => p ∈ X), |w X|
        ≤ ∑ X ∈ (pre (supp bd) T).filter (fun X => p ∈ X),
            Real.exp (-(s * n)) * gw w (t / 2) X := by
          refine sum_le_sum fun X hX => ?_
          have hXT := mem_pre.1 (mem_filter.1 hX).1
          have hcard : (supp bd X).card = n := (mem_filter.1 hXT).2
          by_cases hw : w X = 0
          · rw [hw, abs_zero]
            exact mul_nonneg (Real.exp_pos _).le (gw_nonneg w _ X)
          · have hgX : gw w (t / 2) X = Real.exp (-(t / 2 * X.card)) := by
              unfold gw
              rw [if_pos hw]
            rw [hgX]
            have hnX : (n : ℝ) ≤ c * X.card := by
              rw [← hcard]
              exact_mod_cast card_supp_le bd hc X
            have hsn : s * n ≤ t / 2 * X.card := by
              calc s * n ≤ s * (c * X.card) :=
                    mul_le_mul_of_nonneg_left hnX (by rw [hs]; positivity)
                _ = t / 2 * X.card := by
                    rw [hs]
                    field_simp
            calc |w X| ≤ Real.exp (-(t * X.card)) := hwd X
              _ = Real.exp (-(t / 2 * X.card)) * Real.exp (-(t / 2 * X.card)) := by
                  rw [← Real.exp_add]
                  congr 1
                  ring
              _ ≤ Real.exp (-(s * n)) * Real.exp (-(t / 2 * X.card)) :=
                  mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith))
                    (Real.exp_pos _).le
      _ = Real.exp (-(s * n)) * ∑ X ∈ (pre (supp bd) T).filter (fun X => p ∈ X),
            gw w (t / 2) X := by rw [mul_sum]
      _ ≤ Real.exp (-(s * n)) * ∑ X ∈ MatchAt.site p, gw w (t / 2) X := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ => gw_nonneg w _ X
          intro X hX
          exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hX).2⟩
      _ ≤ Real.exp (-(s * n)) * 1 := mul_le_mul_of_nonneg_left (hsite p) (Real.exp_pos _).le
      _ = Real.exp (-(s * n)) := mul_one _
  calc ∑ Λ ∈ T, |push (supp bd) w Λ|
      ≤ ∑ Λ ∈ T, ∑ X ∈ fib (supp bd) Λ, |w X| :=
        sum_le_sum fun Λ _ => abs_sum_le_sum_abs _ _
    _ = ∑ X ∈ pre (supp bd) T, |w X| := sum_fib_eq _ _ T
    _ ≤ ∑ X ∈ pre (supp bd) T, ∑ p ∈ X.filter (fun p => l ∈ linkSupp bd p), |w X| := by
        refine sum_le_sum fun X hX => ?_
        have hlX : l ∈ supp bd X := (mem_filter.1 (mem_filter.1 (mem_pre.1 hX)).1).2
        obtain ⟨p, hp, hlp⟩ := mem_supp.1 hlX
        exact single_le_sum (f := fun _ => |w X|) (fun _ _ => abs_nonneg _)
          (mem_filter.2 ⟨hp, hlp⟩)
    _ = ∑ p ∈ Pl, ∑ X ∈ (pre (supp bd) T).filter (fun X => p ∈ X), |w X| := by
        refine sum_comm' fun X p => ?_
        simp only [hPl, mem_filter, mem_univ, true_and]
        tauto
    _ ≤ ∑ _p ∈ Pl, Real.exp (-(s * n)) := sum_le_sum fun p _ => hinner p
    _ = Pl.card * Real.exp (-(s * n)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * Real.exp (-(s * n)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hM l) (Real.exp_pos _).le
    _ ≤ (M : ℝ) ^ n * Real.exp (-(s * n)) :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ (by exact_mod_cast hM1) hn.ne')
          (Real.exp_pos _).le
    _ = ((M : ℝ) * Real.exp (-s)) ^ n := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

end Links

/-! ### The 4D torus -/

section Hypercubic

variable {n : ℕ} [NeZero n]

/-- Every hypercubic plaquette names a link. -/
theorem linkSupp_nonempty_hypercubic (q : WilsonHypercubic.Plaq 4 n) :
    (linkSupp (WilsonHypercubic.bd (d := 4) (n := n)) q).Nonempty :=
  ⟨(q.1.1, q.2), by simp [linkSupp, WilsonHypercubic.bd]⟩

/-- **The count on the links of the 4D torus**: connected support, `Decay w t`, `t ≥ 0` and
`2 · 4225 · e^{−t/2} ≤ 1` give `CountAt (push (supp bd) w) 16 (t/8)`. -/
theorem countAt_link_hypercubic {w : Finset (WilsonHypercubic.Plaq 4 n) → ℝ} {t : ℝ}
    (hwc : ConnSupp (WilsonHypercubic.bd (d := 4) (n := n)) w) (hwd : Decay w t) (ht : 0 ≤ t)
    (hq : 2 * ((4225 : ℝ) * Real.exp (-(t / 2))) ≤ 1) :
    CountAt (push (supp (WilsonHypercubic.bd (d := 4) (n := n))) w) 16 (t / 8) := by
  classical
  have h := countAt_link (WilsonHypercubic.bd (d := 4) (n := n)) (c := 4) (M := 16)
    (K := (16 * 4 + 1) ^ 2) (by norm_num) (fun p => linkSupp_bd_card_le p) (by norm_num)
    (fun l => by
      have := linkMult_bd_le (dim := 4) (n := n) l
      unfold linkMult at this
      convert this using 2)
    (fun v m => card_connSets_le_hypercubic v m) hwc hwd ht (by norm_num at hq ⊢; linarith)
  have e : t / (2 * ((4 : ℕ) : ℝ)) = t / 8 := by norm_num
  rw [e] at h
  exact_mod_cast h

/-- **The match on the links of the 4D torus**: `w ∅ = 0`, connected support and `Decay w t` with
`8 · kpCost 16 κ ≤ t` give `MatchAt (push (supp bd) w) 1 κ`. -/
theorem matchAt_link_of_decay {w : Finset (WilsonHypercubic.Plaq 4 n) → ℝ} {t κ : ℝ}
    (hκ : 0 ≤ κ) (hw0 : w ∅ = 0) (hwc : ConnSupp (WilsonHypercubic.bd (d := 4) (n := n)) w)
    (hwd : Decay w t) (hτ : 8 * kpCost 16 κ ≤ t) :
    MatchAt.MatchAt (push (supp (WilsonHypercubic.bd (d := 4) (n := n))) w) 1 κ := by
  have hlog65 : 0 ≤ Real.log (4 * 16 + 1) := Real.log_nonneg (by norm_num)
  have hk0 : 0 ≤ kpCost 16 κ := by unfold kpCost; linarith
  have ht : 0 ≤ t := by linarith
  have hlog : Real.log 8450 ≤ t / 2 := by
    have h1 : Real.log 8450 ≤ Real.log ((4 * 16 + 1 : ℝ) ^ 4) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    unfold kpCost at hτ
    push_cast at h1
    linarith
  have hq : 2 * ((4225 : ℝ) * Real.exp (-(t / 2))) ≤ 1 := by
    have he : Real.exp (-(t / 2)) ≤ Real.exp (-Real.log 8450) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log 8450), Real.exp_log (by norm_num)] at he
    have : 2 * ((4225 : ℝ) * Real.exp (-(t / 2))) ≤ 2 * (4225 * (8450 : ℝ)⁻¹) := by
      have := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 4225)
      linarith
    refine this.trans (le_of_eq ?_)
    norm_num
  exact MatchAt.matchAt_of_count (push_supp_empty linkSupp_nonempty_hypercubic hw0)
    (by norm_num) hκ (countAt_link_hypercubic hwc hwd ht hq)
    (count_cond_of_ge (by norm_num) (by linarith))

/-- **The Wilson link gas satisfies `MatchAt`**: `β > 0` and `8 · kpCost 16 κ ≤ tau β` give
`MatchAt (linkAct bd β) 1 κ` on the links of the 4D torus. -/
theorem matchAt_linkAct_of_tau {Nc : ℕ} (hN : Nc ≠ 0) {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ)
    (hτ : 8 * kpCost 16 κ ≤ tau β) :
    MatchAt.MatchAt (linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := n)) β) 1 κ :=
  matchAt_link_of_decay hκ (act_empty _ _) (act_connSupp _ _) (decay_tau hN _ hβ) hτ

/-- **The coupling hypothesis holds**: for every `κ ≥ 0` some `β > 0` has
`8 · kpCost 16 κ ≤ tau β`, so the Wilson link gas at that `β` satisfies `MatchAt … 1 κ`. -/
theorem exists_beta_matchAt_linkAct {Nc : ℕ} (hN : Nc ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ β : ℝ, 0 < β ∧ 8 * kpCost 16 κ ≤ tau β ∧
      MatchAt.MatchAt (linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := n)) β) 1 κ := by
  have hlog65 : 0 ≤ Real.log (4 * 16 + 1) := Real.log_nonneg (by norm_num)
  have ht : 0 ≤ 8 * kpCost 16 κ := by unfold kpCost; linarith
  obtain ⟨hβ, hr⟩ := βstar_spec ht
  have hτ := (le_tau_iff hβ).2 hr
  exact ⟨βstar (8 * kpCost 16 κ), hβ, hτ, matchAt_linkAct_of_tau hN hβ hκ hτ⟩

end Hypercubic

/-! ## 4. `PolymerCross` on the Wilson gas -/

section Cross

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **`PolymerCross` on the Wilson link gas**: the clauses of `MatchAt.PolymerCross` other than
`MatchAt`, with polymers `Finset (Link 4 nC)`, `w = linkAct` at coupling `β`, and the cross term
bounded by the interaction `Q (Inc bd) (act bd β)` of the Wilson gas on the plaquette families
`pre S`, `pre A`, `pre U`. Under `8 · kpCost 16 κ ≤ tau β` it forces `⟪P vᵢ, P vⱼ⟫ = 0` beyond the
fixed range `CrossTerm.farRange nC` (`CrossTerm.cross_zero_of_far`); it is not a usable route to (B),
whose input is `CellLinks.ScreenedCells`.

DERIVED: `4` the dimension; `16 = 4 · 4` the plaquettes per link (`linkMult_bd_le`); `8 = 2 · 4` the
halving of the cost and the links per plaquette (`matchAt_link_of_decay`). -/
def WilsonLinkPolymerCross (Nc nC : ℕ) [NeZero nC] (β : ℝ) (P : E →L[ℝ] E) (v : Fin n → E)
    (d : Fin n → Fin n → ℕ) (Kx M L r₀ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ (ρ : WilsonHypercubic.Link 4 nC → WilsonHypercubic.Link 4 nC → ℝ)
    (dset : WilsonHypercubic.Link 4 nC → ℝ) (U A S : Finset (Finset (WilsonHypercubic.Link 4 nC)))
    (Λ : Finset (WilsonHypercubic.Link 4 nC)) (R : ℝ),
    (∀ x y, dset x ≤ dset y + ρ x y) ∧
    (∀ X, linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β X ≠ 0 →
      ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card) ∧
    (∀ Y ∈ U, linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β Y ≠ 0 →
      ∀ y ∈ Y, dset y ≤ 0) ∧ (∀ y ∈ Λ, R ≤ dset y) ∧
    (∀ X ∈ A, (X ∩ Λ).Nonempty) ∧ (∀ X ∈ A, X ∉ U) ∧ (Λ.card : ℝ) ≤ M ∧
    (d i j : ℝ) * L - r₀ ≤ R ∧
    |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |MatchAt.Q (Inc (WilsonHypercubic.bd (d := 4) (n := nC)))
      (act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) S)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) A)
      (pre (supp (WilsonHypercubic.bd (d := 4) (n := nC))) U)| * (‖v i‖ * ‖v j‖)

/-- **`PolymerCross` from the Wilson link clauses**: with `8 · kpCost 16 κ ≤ tau β` the `MatchAt`
clause is supplied by the Wilson link gas, and the cross term is read through `linkQ_eq`. -/
theorem polymerCross_of_wilsonLink {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : 8 * kpCost 16 κ ≤ tau β) {P : E →L[ℝ] E} {v : Fin n → E}
    {d : Fin n → Fin n → ℕ} {Kx M L r₀ : ℝ} (h : WilsonLinkPolymerCross Nc nC β P v d Kx M L r₀) :
    MatchAt.PolymerCross P v d Kx M 1 κ L r₀ := by
  intro i j hij
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i j hij
  refine ⟨WilsonHypercubic.Link 4 nC, inferInstance, inferInstance,
    linkAct (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β, ρ, dset, U, A, S, Λ, R,
    matchAt_linkAct_of_tau hN hβ hκ hτ, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  rw [linkQ_eq _ linkSupp_nonempty_hypercubic]
  exact h9

end Cross

/-! ## 5. The one-plaquette activity is nonzero -/

section Single

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

omit [DecidableEq Pq] in
/-- **`act {p} ≠ 0` from one configuration**: `β > 0` and some configuration with `φ_p ≠ 0`. -/
theorem act_singleton_ne_zero_of (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 < β)
    (p : Pq) (hU : ∃ U : Lk → MassGap.SUN.SU Nc, wilsonDensity (N := Nc) (wilsonHol bd p U) ≠ 0) :
    act (Nc := Nc) bd β {p} ≠ 0 := by
  obtain ⟨U₀, hU₀⟩ := hU
  set F : (Lk → MassGap.SUN.SU Nc) → ℝ :=
    fun U => 1 - Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) with hFdef
  have hc : Continuous (fun U : Lk → MassGap.SUN.SU Nc => wilsonDensity (N := Nc) (wilsonHol bd p U)) :=
    continuous_wilsonDensity.comp (MassGap.PlaqVariance.continuous_wilsonHol bd p)
  have hF : Continuous F :=
    continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul hc).neg)
  have hFnn : 0 ≤ F := by
    intro U
    have h0 := wilsonDensity_nonneg hN (wilsonHol bd p U)
    have : Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    show 0 ≤ 1 - _
    linarith
  have hF0 : F U₀ ≠ 0 := by
    have h0 := lt_of_le_of_ne (wilsonDensity_nonneg hN (wilsonHol bd p U₀)) (Ne.symm hU₀)
    have : Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U₀))) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith)
    show 1 - _ ≠ 0
    linarith
  have hpos : 0 < ∫ U, F U ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) :=
    hF.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace F)
      hFnn hF0
  have hact : act (Nc := Nc) bd β {p} = -∫ U, F U
      ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    classical
    rw [act_of bd β ⟨Finset.singleton_nonempty p, touchConnected_singleton bd p⟩, ← integral_neg]
    unfold zw
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul, Finset.prod_singleton, hFdef, wfun_apply]
    ring
  rw [hact]
  linarith

/-- **A plaquette of the 4D torus with two distinct directions has a configuration with
`φ_p ≠ 0`**, for `2 ≤ N` and `2 ≤ n`. -/
theorem exists_density_ne_zero_hypercubic (hN2 : 2 ≤ Nc) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (p : WilsonHypercubic.Plaq 4 n) (hp : p.1.1 ≠ p.1.2) :
    ∃ U : WilsonHypercubic.Link 4 n → MassGap.SUN.SU Nc,
      wilsonDensity (N := Nc) (wilsonHol (WilsonHypercubic.bd (d := 4) (n := n)) p U) ≠ 0 := by
  obtain ⟨⟨μ, ν⟩, x⟩ := p
  simp only at hp
  obtain ⟨m, rfl⟩ : ∃ m, Nc = m + 2 := ⟨Nc - 2, by omega⟩
  set g : MassGap.SUN.SU (m + 2) := MassGap.HaarVariance.flipEl m with hg
  have hgpos : 0 < wilsonDensity (N := m + 2) g := by
    have h := MassGap.HaarVariance.reTr_flipEl m
    unfold MassGap.HaarVariance.reTr at h
    unfold wilsonDensity
    rw [hg, h]
    have e : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [e, div_mul_eq_mul_div, one_mul, sub_pos, div_lt_one hpos]
    linarith
  have h1 : ((ν, WilsonHypercubic.shift μ x) : WilsonHypercubic.Link 4 n) ≠ (μ, x) :=
    fun h => hp (congrArg Prod.fst h).symm
  have h3 : ((ν, x) : WilsonHypercubic.Link 4 n) ≠ (μ, x) := fun h => hp (congrArg Prod.fst h).symm
  have h2 : ((μ, WilsonHypercubic.shift ν x) : WilsonHypercubic.Link 4 n) ≠ (μ, x) := by
    intro h
    have hx := congrFun (congrArg Prod.snd h) ν
    simp only [WilsonHypercubic.shift, Function.update_self] at hx
    have h10 : (1 : Fin n) = 0 := by
      have := congrArg (fun a => a - x ν) hx
      simpa using this
    have hv := congrArg Fin.val h10
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    exact one_ne_zero hv
  refine ⟨Function.update (fun _ => 1) (μ, x) g, ?_⟩
  simp only [wilsonHol, WilsonHypercubic.bd, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, inv_one, mul_one, Bool.false_eq_true,
    ↓reduceIte]
  exact hgpos.ne'

/-- **The one-plaquette Wilson activity is nonzero** on the 4D torus: `2 ≤ N`, `2 ≤ n`, `β > 0`,
and `p` spanning two distinct directions give `act {p} ≠ 0`. -/
theorem act_singleton_ne_zero (hN2 : 2 ≤ Nc) {n : ℕ} [NeZero n] (hn : 2 ≤ n) {β : ℝ} (hβ : 0 < β)
    (p : WilsonHypercubic.Plaq 4 n) (hp : p.1.1 ≠ p.1.2) :
    act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := n)) β {p} ≠ 0 :=
  act_singleton_ne_zero_of (by omega) _ hβ p (exists_density_ne_zero_hypercubic hN2 hn p hp)

/-- **The witness of `ChunkActivity.chunkDecay_wilson_witness`, with nonzero activities**: for
`σ₀, f ≥ 0` the couplings `βstar (σ₀ f L²)` are positive, meet `ChunkDecay`, and for `2 ≤ N` every
one-plaquette activity on a coarse torus of side `≥ 2` with two distinct directions is nonzero. -/
theorem chunkDecay_wilson_witness' (hN2 : 2 ≤ Nc) (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    {σ₀ f : ℝ} (hσ₀ : 0 ≤ σ₀) (hf : 0 ≤ f) :
    (∀ j L, 0 < (fun (_ : ℕ) (L : ℝ) => βstar (σ₀ * f * L ^ 2)) j L) ∧
    ChunkDecay nB (wilsonChunk Nc nB (fun _ L => βstar (σ₀ * f * L ^ 2))) σ₀ f ∧
    ∀ j L (p : WilsonHypercubic.Plaq 4 (nB j L)), 2 ≤ nB j L → p.1.1 ≠ p.1.2 →
      wilsonChunk Nc nB (fun _ L => βstar (σ₀ * f * L ^ 2)) j L {p} ≠ 0 := by
  obtain ⟨h1, h2⟩ := chunkDecay_wilson_witness (Nc := Nc) (by omega) nB hσ₀ hf
  exact ⟨h1, h2, fun j L p hn hp => act_singleton_ne_zero hN2 hn (h1 j L) p hp⟩

end Single

#print axioms sum_fib_eq
#print axioms Z_clique
#print axioms Z_push
#print axioms inc_iff_meet
#print axioms inc_of_supp_eq
#print axioms linkAct_empty
#print axioms linkZ_eq
#print axioms partition_eq_linkZ
#print axioms linkQ_eq
#print axioms sum_site_le_one
#print axioms countAt_link
#print axioms countAt_link_hypercubic
#print axioms matchAt_link_of_decay
#print axioms matchAt_linkAct_of_tau
#print axioms exists_beta_matchAt_linkAct
#print axioms polymerCross_of_wilsonLink
#print axioms act_singleton_ne_zero_of
#print axioms exists_density_ne_zero_hypercubic
#print axioms act_singleton_ne_zero
#print axioms chunkDecay_wilson_witness'

end MassGap.ChunkLinks
