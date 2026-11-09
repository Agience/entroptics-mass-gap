import Mathlib
import MassGap.StrongCoupling
import MassGap.OneWayCost
import MassGap.VortexCondense

/-!
# MassGap.PolymerCount — the count hypothesis: the entropy half proved, the activity half named

## What the count hypothesis says

Every consumer of `MatchAt.matchAt_of_count` (`NoTransitionFlow.matchAt_along_flow`,
`matchAt_of_tension_flow`, `matchAt_uniform_of_runsOneWay`, `matchAt_uniform_of_edgesCannotEndNA`,
`OneWayCost.matchAt_uniform_of_runsOneWayTo`, `VortexCondense.count_uniform_of_floor`,
`VortexCondense.matchAt_uniform_of_condensation`, `MatchAt.matchAt_of_tension`,
`MatchAt.matchAt_of_states`) reads the same clause, here `CountAt w z τ`:

    ∀ v n,  Σ_{X ∋ v, |X| = n} |w X|  ≤  (z e^{−τ})ⁿ,

with `w : Finset V → ℝ` the activities of a polymer gas on the chunks `V`, `z` the entropy per chunk
and `τ` the cost per chunk (`σ f L²` on the floor route, `s j k` on the running route). The clause
mixes two things: how many polymers of size `n` contain a chunk (combinatorics) and how small each
activity is (the effective action).

## 1. The split (`countAt_of_decay`, `decay_of_countAt`)

* `TouchConnected bd X`: every two members of `X` are touch-reachable inside `X`
  (`StrongCoupling.Reach`). `ConnSupp bd w`: `w X ≠ 0` only on touch-connected `X` — the activities
  are those of a polymer representation whose polymers are connected sets.
* `Decay w τ`: `|w X| ≤ e^{−τ |X|}` for every `X`: each chunk of a polymer costs `τ`.
* `countAt_of_connSets_card`: a bound `#connSets bd v n ≤ Kⁿ` on the rooted connected sets, with
  `ConnSupp` and `Decay w τ`, gives `CountAt w K τ`.
* `countAt_of_decay`: with `K = (touchDeg bd + 1)²` from `StrongCoupling.card_connSets_le` (the
  walk-encoding count of touch-connected sets, two steps per new member; no lattice extent): for any
  boundary map `bd`, `ConnSupp` and `Decay w τ` give `CountAt w ((touchDeg bd + 1)²) τ`.
* `decay_of_countAt` (converse): `CountAt w z τ` with `z > 0` and `w ∅ = 0` gives
  `Decay w (τ − log z)`: the single term `X` of the sum at `n = |X|` is at most the whole sum.

So on connected-supported activities the count hypothesis and per-polymer decay are the same
statement up to a shift of the cost per chunk by the logarithm of the entropy constant:
`Decay w τ ⇒ CountAt w K τ ⇒ Decay w (τ − log K)`. The combinatorial content of the count is the
lattice-animal bound, and it is proved; what is left is `Decay`, a bound on the activities.

## 2. The concrete chunk polymers (`countAt_of_decay_hypercubic`)

The block-spin effective theory at chunk side `L` is a lattice gauge theory on the coarse lattice;
its polymers are sets of coarse plaquettes, `WilsonHypercubic.Plaq 4 n` on the periodic coarse torus of
extent `n`, connected under touching (sharing a link of `WilsonHypercubic.bd`). On these,
`StrongCoupling.card_connSets_le_hypercubic` gives `K = (16·4 + 1)² = 4225` at every extent:
`countAt_of_decay_hypercubic` is `CountAt w zHyper4 τ` from `ConnSupp` and `Decay w τ`, with
`zHyper4 = 4225` (`zHyper4_eq`).

`witness`: the activities `e^{−τ|X|}` on the nonempty touch-connected sets and `0` elsewhere satisfy
`w ∅ = 0`, `ConnSupp` and `Decay w τ` (`witness_hyps`), and are nonzero on every one-plaquette polymer
(`witness_singleton_ne`): the hypotheses of `matchAt_uniform_of_uniformDecay` (`ChunkDecay`) hold
with nonzero activities; the witness is built to saturate `Decay` and carries no information about
the Wilson measure.

## 3. The consumers, at their own signatures

Each theorem below calls the consumer named, with `hcount` supplied by `countAt_of_decay_hypercubic`
and `z = zHyper4`; the chunk type at zoom `j` and side `L` (or step `k`) is
`Plaq 4 (nB j L)`, `nB j L ≠ 0` the extent of the coarse torus.

* `matchAt_of_decay`: one chunk theory; `Decay` at cost `τ ≥ kpCost zHyper4 κ` gives `MatchAt w 1 κ`
  (`MatchAt.matchAt_of_count`).
* `matchAt_uniform_of_edgesCannotEndNA_decay`: `NoTransitionFlow.matchAt_uniform_of_edgesCannotEndNA`
  with `Decay (w j L) (σ j f L²)`.
* `matchAt_uniform_of_runsOneWayTo_decay`: `OneWayCost.matchAt_uniform_of_runsOneWayTo` with
  `Decay (w j k) (s j k)` and target `kpCost zHyper4 κ`.
* `matchAt_uniform_of_condensation_decay`: `VortexCondense.matchAt_uniform_of_condensation` with
  `Decay (w j L) ((σlat j / a j²) f L²)`.
* `matchAt_uniform_of_uniformDecay`: no floor and no running asked: `Decay (w j L) (σ₀ f L²)` with one
  `σ₀ > 0` at every zoom gives one `L₀` with `MatchAt` at every zoom and every `L ≥ L₀`
  (`MatchAt.exists_length_match`, `MatchAt.matchAt_of_count`). `uniformDecay_of_floor` (via
  `decay_mono`): a floor `σ j ≥ σ₀` turns per-zoom decay at `σ j f L²` into decay at `σ₀ f L²`. So
  (R1) of `NoTransitionFlow`, together with (R2) in its decay form (connected support and
  `Decay (w j L) (σ j f L²)`), implies this hypothesis. (R2) as a count gives decay only at
  `σ j f L² − log z` (`decay_of_countAt`).

## What remains for `MatchAt`

`ChunkDecay w σ₀ f`: at every zoom `j` and side `L`, the block-spin chunk activities on the coarse
plaquettes `Plaq 4 (nB j L)` are supported on touch-connected polymers and obey
`|w j L X| ≤ e^{−σ₀ f L² |X|}`. `matchAt_uniform_of_chunkDecay` is
`matchAt_uniform_of_uniformDecay` with it as the one input. This is the physics: a bound on the
activities of the block-spin effective action of the 4D `SU(N)` Wilson measure at one uniform cost
per chunk, which no declaration constructs (`MatchAt`, §3: no declaration ties `w` to the effective
action). It is not the string-tension floor in disguise: `Floor σ` is a statement about Wilson loops
(`NoTransition.Floor`, `VortexCondense.HasTension`) and enters the count only through `decay_mono`;
`ChunkDecay` with `σ₀ > 0` is what the consumers need, and it contains the floor's role (one
positive cost for every zoom) together with the control of the activities by that cost. The
entropy factor `z` is not an input: it is `4225`. `w` is a free function: `w = 0` meets
`ChunkDecay`. Reaching `ClayStatement` further needs `MatchAt.PolymerCross` for that same `w`
(`relFloorM_of_polymerCross`).

DERIVED (module-wide): `16 · 4 + 1 = 65` the touch degree bound `16 d` of
`StrongCoupling.touchDeg_bd_le` at `d = 4` plus the stay-put step; `2` the two walk steps per new
plaquette (`4225 = 65²`); `4` the dimension; `0` the empty polymer and the sign of every weight;
`1` the KP constant `a = 1` of `matchAt_of_count`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.PolymerCount

open Finset
open MassGap.MatchAt MassGap.StrongCoupling MassGap.NoTransitionFlow

/-! ## 1. The split -/

/-- **The count hypothesis** of `MatchAt.matchAt_of_count`, as its consumers state it:
`Σ_{X ∋ v, |X| = n} |w X| ≤ (z e^{−τ})ⁿ` at every chunk `v` and size `n`. -/
def CountAt {V : Type*} [Fintype V] [DecidableEq V] (w : Finset V → ℝ) (z τ : ℝ) : Prop :=
  ∀ v n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w X| ≤ (z * Real.exp (-τ)) ^ n

/-- **Per-polymer decay at cost `τ` per chunk**: `|w X| ≤ e^{−τ |X|}`. -/
def Decay {V : Type*} (w : Finset V → ℝ) (τ : ℝ) : Prop :=
  ∀ X, |w X| ≤ Real.exp (-(τ * X.card))

section Generic

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **A touch-connected set**: every two members are touch-reachable inside it. -/
def TouchConnected (bd : Pq → List (Lk × Bool)) (X : Finset Pq) : Prop :=
  ∀ p ∈ X, ∀ q ∈ X, Reach bd X p q

/-- **Activities supported on touch-connected polymers.** -/
def ConnSupp (bd : Pq → List (Lk × Bool)) (w : Finset Pq → ℝ) : Prop :=
  ∀ X, w X ≠ 0 → TouchConnected bd X

/-- **Rooted connected count and decay give the count hypothesis**: `#connSets bd v n ≤ Kⁿ`,
`ConnSupp` and `Decay w τ` give `CountAt w K τ`. -/
theorem countAt_of_connSets_card (bd : Pq → List (Lk × Bool)) {w : Finset Pq → ℝ} {τ : ℝ}
    {K : ℕ} (hK : ∀ v n, (connSets bd v n).card ≤ K ^ n) (hc : ConnSupp bd w)
    (hd : Decay w τ) : CountAt w K τ := by
  intro v n
  have hsub : ((site v).filter (fun X => X.card = n)).filter (fun X => |w X| ≠ 0)
      ⊆ connSets bd v n := by
    intro X hX
    rw [mem_filter, mem_filter] at hX
    obtain ⟨⟨hXs, hcard⟩, hw⟩ := hX
    have hv : v ∈ X := (mem_filter.1 hXs).2
    exact mem_connSets.2 ⟨hv, fun q hq => hc X (abs_ne_zero.1 hw) v hv q hq, hcard⟩
  calc ∑ X ∈ (site v).filter (fun X => X.card = n), |w X|
      = ∑ X ∈ ((site v).filter (fun X => X.card = n)).filter (fun X => |w X| ≠ 0), |w X| :=
        (sum_filter_ne_zero _).symm
    _ ≤ ∑ X ∈ connSets bd v n, |w X| :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _X ∈ connSets bd v n, Real.exp (-τ) ^ n := by
        refine sum_le_sum fun X hX => ?_
        have hcard := (mem_connSets.1 hX).2.2
        calc |w X| ≤ Real.exp (-(τ * X.card)) := hd X
          _ = Real.exp (-τ) ^ n := by
              rw [hcard, ← Real.exp_nat_mul]
              congr 1
              ring
    _ = (connSets bd v n).card * Real.exp (-τ) ^ n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) ^ n * Real.exp (-τ) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hK v n
    _ = ((K : ℝ) * Real.exp (-τ)) ^ n := (mul_pow _ _ _).symm

/-- **The count hypothesis from connected support and decay**, with the entropy constant
`(touchDeg bd + 1)²` of `StrongCoupling.card_connSets_le`. -/
theorem countAt_of_decay (bd : Pq → List (Lk × Bool)) {w : Finset Pq → ℝ} {τ : ℝ}
    (hc : ConnSupp bd w) (hd : Decay w τ) :
    CountAt w (((touchDeg bd + 1) ^ 2 : ℕ) : ℝ) τ :=
  countAt_of_connSets_card bd (fun v n => card_connSets_le bd v n) hc hd

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- **A single-plaquette set is touch-connected.** -/
theorem touchConnected_singleton (bd : Pq → List (Lk × Bool)) (p : Pq) :
    TouchConnected bd {p} := by
  intro a ha b hb
  rw [mem_singleton] at ha hb
  rw [ha, hb]
  exact Relation.ReflTransGen.refl

open scoped Classical in
/-- **A witness**: `e^{−τ|X|}` on the nonempty touch-connected sets, `0` elsewhere. -/
def witness (bd : Pq → List (Lk × Bool)) (τ : ℝ) (X : Finset Pq) : ℝ :=
  if X.Nonempty ∧ TouchConnected bd X then Real.exp (-(τ * X.card)) else 0

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- **The witness meets the hypotheses**: `w ∅ = 0`, `ConnSupp`, `Decay w τ`. -/
theorem witness_hyps (bd : Pq → List (Lk × Bool)) (τ : ℝ) :
    witness bd τ ∅ = 0 ∧ ConnSupp bd (witness bd τ) ∧ Decay (witness bd τ) τ := by
  classical
  refine ⟨?_, fun X hX => ?_, fun X => ?_⟩
  · unfold witness
    exact if_neg (fun h : (∅ : Finset Pq).Nonempty ∧ TouchConnected bd ∅ =>
      Finset.not_nonempty_empty h.1)
  · unfold witness at hX
    by_contra hn
    exact hX (if_neg (fun h => hn h.2))
  · unfold witness
    split_ifs
    · rw [abs_of_pos (Real.exp_pos _)]
    · rw [abs_zero]
      exact (Real.exp_pos _).le

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
/-- **The witness is nonzero on every one-plaquette polymer.** -/
theorem witness_singleton_ne (bd : Pq → List (Lk × Bool)) (τ : ℝ) (p : Pq) :
    witness bd τ {p} ≠ 0 := by
  classical
  unfold witness
  rw [if_pos ⟨singleton_nonempty p, touchConnected_singleton bd p⟩]
  exact (Real.exp_pos _).ne'

end Generic

/-- **The converse**: the count with `z > 0` and `w ∅ = 0` gives per-polymer decay at the cost
`τ − log z`. -/
theorem decay_of_countAt {V : Type*} [Fintype V] [DecidableEq V] {w : Finset V → ℝ} {z τ : ℝ}
    (hz : 0 < z) (h : CountAt w z τ) (hw0 : w ∅ = 0) : Decay w (τ - Real.log z) := by
  intro X
  rcases X.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp [hw0]
  · have hmem : X ∈ (site v).filter (fun Y => Y.card = X.card) :=
      mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hv⟩, rfl⟩
    have h1 := (single_le_sum (f := fun Y => |w Y|) (fun _ _ => abs_nonneg _) hmem).trans
      (h v X.card)
    have hze : z * Real.exp (-τ) = Real.exp (-(τ - Real.log z)) := by
      rw [neg_sub, Real.exp_sub, Real.exp_log hz, Real.exp_neg, div_eq_mul_inv]
    calc |w X| ≤ (z * Real.exp (-τ)) ^ X.card := h1
      _ = Real.exp (-((τ - Real.log z) * X.card)) := by
          rw [hze, ← Real.exp_nat_mul]
          congr 1
          ring

/-- **Decay at a higher cost is decay at a lower one.** -/
theorem decay_mono {V : Type*} {w : Finset V → ℝ} {τ τ' : ℝ} (h : Decay w τ) (hτ : τ' ≤ τ) :
    Decay w τ' := fun X =>
  (h X).trans (Real.exp_le_exp.2 (neg_le_neg
    (mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg _))))

/-! ## 2. The concrete chunk polymers -/

/-- **The entropy constant of the coarse plaquettes of the 4D torus**: `(16·4 + 1)²`.
DERIVED: `16 · 4 = 16 d` the touch degree bound of `StrongCoupling.touchDeg_bd_le` at `d = 4`; `1` the
stay-put step; `2` the two walk steps per new plaquette. -/
def zHyper4 : ℝ := (((16 * 4 + 1) ^ 2 : ℕ) : ℝ)

theorem zHyper4_eq : zHyper4 = 4225 := by norm_num [zHyper4]

theorem zHyper4_nonneg : 0 ≤ zHyper4 := Nat.cast_nonneg _

/-- **The count hypothesis on the coarse plaquettes of the 4D torus**, at every extent: connected
support and decay give `CountAt w zHyper4 τ`. -/
theorem countAt_of_decay_hypercubic {n : ℕ} [NeZero n] {w : Finset (WilsonHypercubic.Plaq 4 n) → ℝ}
    {τ : ℝ} (hc : ConnSupp (WilsonHypercubic.bd (d := 4) (n := n)) w) (hd : Decay w τ) :
    CountAt w zHyper4 τ :=
  countAt_of_connSets_card _ (fun v m => card_connSets_le_hypercubic v m) hc hd

/-! ## 3. The consumers, at their own signatures -/

/-- **One chunk theory**: connected support and decay at a cost `τ ≥ kpCost zHyper4 κ` give
`MatchAt w 1 κ`. -/
theorem matchAt_of_decay {n : ℕ} [NeZero n] {w : Finset (WilsonHypercubic.Plaq 4 n) → ℝ}
    {τ κ : ℝ} (hκ : 0 ≤ κ) (hw0 : w ∅ = 0)
    (hc : ConnSupp (WilsonHypercubic.bd (d := 4) (n := n)) w) (hd : Decay w τ)
    (hτ : kpCost zHyper4 κ ≤ τ) : MatchAt w 1 κ :=
  matchAt_of_count hw0 zHyper4_nonneg hκ (countAt_of_decay_hypercubic hc hd)
    (count_cond_of_ge zHyper4_nonneg hτ)

/-- **The floor route with the count discharged to decay**: `NoTransitionFlow`'s
`matchAt_uniform_of_edgesCannotEndNA` on the coarse plaquettes, `hcount` from
`countAt_of_decay_hypercubic`. -/
theorem matchAt_uniform_of_edgesCannotEndNA_decay {N : ℕ} (hN : 2 ≤ N) (nB : ℕ → ℝ → ℕ)
    [∀ j L, NeZero (nB j L)] (w : ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ)
    {σ : ℕ → ℝ} {f κ : ℝ} (hf : 0 < f) (hκ : 0 ≤ κ)
    (hedge : NoTransition.EdgesCannotEndNA (MassGap.SUN.SU N) σ) (hw0 : ∀ j L, w j L ∅ = 0)
    (hc : ∀ j L, ConnSupp (WilsonHypercubic.bd (d := 4) (n := nB j L)) (w j L))
    (hd : ∀ j L, Decay (w j L) (σ j * f * L ^ 2)) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ :=
  NoTransitionFlow.matchAt_uniform_of_edgesCannotEndNA hN
    (V := fun j L => WilsonHypercubic.Plaq 4 (nB j L)) w zHyper4_nonneg hf hκ hedge hw0
    (fun j L v m => countAt_of_decay_hypercubic (hc j L) (hd j L) v m)

/-- **The running route with the count discharged to decay**: `OneWayCost`'s
`matchAt_uniform_of_runsOneWayTo` on the coarse plaquettes at target `kpCost zHyper4 κ`. -/
theorem matchAt_uniform_of_runsOneWayTo_decay (nB : ℕ → ℕ → ℕ) [∀ j k, NeZero (nB j k)]
    (w : ∀ j k, Finset (WilsonHypercubic.Plaq 4 (nB j k)) → ℝ) {s : ℕ → ℕ → ℝ} {κ b s₀ : ℝ}
    (hκ : 0 ≤ κ) (hb : 0 < b) (hs₀ : 0 < s₀) (hstart : ∀ j, s₀ ≤ s j 0)
    (hrun : ∀ j, OneWayCost.RunsOneWayTo b (kpCost zHyper4 κ) (s j)) (hw0 : ∀ j k, w j k ∅ = 0)
    (hc : ∀ j k, ConnSupp (WilsonHypercubic.bd (d := 4) (n := nB j k)) (w j k))
    (hd : ∀ j k, Decay (w j k) (s j k)) :
    ∃ K : ℕ, ∀ j k, K ≤ k → MatchAt (w j k) 1 κ :=
  OneWayCost.matchAt_uniform_of_runsOneWayTo (V := fun j k => WilsonHypercubic.Plaq 4 (nB j k)) w
    zHyper4_nonneg hκ hb hs₀ hstart hrun hw0
    (fun j k v m => countAt_of_decay_hypercubic (hc j k) (hd j k) v m)

/-- **The condensation route with the count discharged to decay**: `VortexCondense`'s
`matchAt_uniform_of_condensation` on the coarse plaquettes. -/
theorem matchAt_uniform_of_condensation_decay {W : ℕ → ℕ → ℕ → ℕ → ℝ} {Winf : ℕ → ℕ → ℕ → ℝ}
    {e : ℕ → ℕ → ℝ} {La Lb : ℕ → ℕ → ℕ} {a σlat : ℕ → ℝ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (ha : ∀ j, 0 < a j)
    (hTY : ∀ j K, VortexCondense.TYBound (W j K) (e j K) (La j K) (Lb j K))
    (he0 : ∀ j K, 0 ≤ e j K)
    (hcond : ∀ j, VortexCondense.Condenses (e j) (fun K => (La j K : ℝ) * Lb j K) (ρ₀ * a j ^ 2))
    (hadm : ∀ j m n, 1 ≤ m → 1 ≤ n → ∀ᶠ K in Filter.atTop, VortexCondense.Adm (La j K) (Lb j K) m n)
    (hlim : ∀ j m n, Filter.Tendsto (fun K => W j K m n) Filter.atTop (nhds (Winf j m n)))
    (hT : ∀ j, VortexCondense.HasTension (Winf j) (σlat j))
    (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (w : ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ) {f κ : ℝ} (hf : 0 < f) (hκ : 0 ≤ κ)
    (hw0 : ∀ j L, w j L ∅ = 0)
    (hc : ∀ j L, ConnSupp (WilsonHypercubic.bd (d := 4) (n := nB j L)) (w j L))
    (hd : ∀ j L, Decay (w j L) (σlat j / a j ^ 2 * f * L ^ 2)) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ :=
  VortexCondense.matchAt_uniform_of_condensation hρ₀ ha hTY he0 hcond hadm hlim hT
    (V := fun j L => WilsonHypercubic.Plaq 4 (nB j L)) w zHyper4_nonneg hf hκ hw0
    (fun j L v m => countAt_of_decay_hypercubic (hc j L) (hd j L) v m)

/-- **One hypothesis, no floor and no running**: decay at one cost `σ₀ f L²` (`σ₀, f > 0`) at every
zoom and side, with connected support, gives one `L₀` with `MatchAt` at every zoom and `L ≥ L₀`. -/
theorem matchAt_uniform_of_uniformDecay (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (w : ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ) {σ₀ f κ : ℝ} (hσ₀ : 0 < σ₀)
    (hf : 0 < f) (hκ : 0 ≤ κ) (hw0 : ∀ j L, w j L ∅ = 0)
    (hc : ∀ j L, ConnSupp (WilsonHypercubic.bd (d := 4) (n := nB j L)) (w j L))
    (hd : ∀ j L, Decay (w j L) (σ₀ * f * L ^ 2)) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ := by
  obtain ⟨L₀, hL₀, h⟩ := exists_length_match (κ := κ) zHyper4_nonneg hσ₀ hf
  exact ⟨L₀, hL₀, fun j L hL => matchAt_of_count (hw0 j L) zHyper4_nonneg hκ
    (countAt_of_decay_hypercubic (hc j L) (hd j L)) (h L hL)⟩

/-- **A floor reduces per-zoom decay to uniform decay**: `σ j ≥ σ₀`, `f ≥ 0` and decay at
`σ j f L²` give decay at `σ₀ f L²`. -/
theorem uniformDecay_of_floor {V : ℕ → ℝ → Type*} (w : ∀ j L, Finset (V j L) → ℝ) {σ : ℕ → ℝ}
    {σ₀ f : ℝ} (hf : 0 ≤ f) (hlow : ∀ j, σ₀ ≤ σ j)
    (hd : ∀ j L, Decay (w j L) (σ j * f * L ^ 2)) :
    ∀ j L, Decay (w j L) (σ₀ * f * L ^ 2) := fun j L =>
  decay_mono (hd j L)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hlow j) hf) (sq_nonneg L))

/-! ## What remains -/

/-- **The remaining input to uniform `MatchAt`, on the concrete chunk polymers**: at every zoom `j`
and side `L` the activities on the coarse plaquettes `Plaq 4 (nB j L)` are supported on
touch-connected polymers, vanish on `∅`, and decay at the one cost `σ₀ f L²` per chunk. `w` is a
free function: `w = 0` meets it, and no declaration ties `w` to the block-spin effective action of
the Wilson measure. Reaching `ClayStatement` further needs `MatchAt.PolymerCross` for that same `w`
(`relFloorM_of_polymerCross`). -/
def ChunkDecay (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (w : ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ) (σ₀ f : ℝ) : Prop :=
  ∀ j L, w j L ∅ = 0 ∧ ConnSupp (WilsonHypercubic.bd (d := 4) (n := nB j L)) (w j L) ∧
    Decay (w j L) (σ₀ * f * L ^ 2)

/-- **`ChunkDecay` with `σ₀, f > 0` gives one length with the match at every zoom.** -/
theorem matchAt_uniform_of_chunkDecay (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (w : ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ) {σ₀ f κ : ℝ} (hσ₀ : 0 < σ₀)
    (hf : 0 < f) (hκ : 0 ≤ κ) (h : ChunkDecay nB w σ₀ f) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ :=
  matchAt_uniform_of_uniformDecay nB w hσ₀ hf hκ (fun j L => (h j L).1) (fun j L => (h j L).2.1)
    (fun j L => (h j L).2.2)

/-- **`ChunkDecay` is satisfiable with nonzero activities**: the witness at cost `σ₀ f L²` meets it
and is nonzero on every one-plaquette polymer. -/
theorem chunkDecay_witness (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)] (σ₀ f : ℝ) :
    ChunkDecay nB (fun j L => witness (WilsonHypercubic.bd (d := 4) (n := nB j L))
      (σ₀ * f * L ^ 2)) σ₀ f ∧
    ∀ j L (p : WilsonHypercubic.Plaq 4 (nB j L)),
      witness (WilsonHypercubic.bd (d := 4) (n := nB j L)) (σ₀ * f * L ^ 2) {p} ≠ 0 :=
  ⟨fun _ _ => witness_hyps _ _, fun _ _ p => witness_singleton_ne _ _ p⟩

#print axioms countAt_of_connSets_card
#print axioms countAt_of_decay
#print axioms touchConnected_singleton
#print axioms witness_hyps
#print axioms witness_singleton_ne
#print axioms decay_of_countAt
#print axioms decay_mono
#print axioms zHyper4_eq
#print axioms countAt_of_decay_hypercubic
#print axioms matchAt_of_decay
#print axioms matchAt_uniform_of_edgesCannotEndNA_decay
#print axioms matchAt_uniform_of_runsOneWayTo_decay
#print axioms matchAt_uniform_of_condensation_decay
#print axioms matchAt_uniform_of_uniformDecay
#print axioms uniformDecay_of_floor
#print axioms matchAt_uniform_of_chunkDecay
#print axioms chunkDecay_witness

end MassGap.PolymerCount
