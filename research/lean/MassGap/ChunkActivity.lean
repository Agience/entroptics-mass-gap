import Mathlib
import MassGap.PolymerCount

/-!
# MassGap.ChunkActivity — the polymer activities of the Wilson measure, wired to `ChunkDecay`

`PolymerCount.ChunkDecay nB w σ₀ f` asks three things of activities
`w j L : Finset (Plaq 4 (nB j L)) → ℝ`: `w ∅ = 0`, support on touch-connected sets, and
`|w X| ≤ e^{−σ₀ f L² |X|}`. This module builds the activities of the `SU(N)` Wilson lattice measure
on a finite plaquette geometry, proves the polymer representation of its partition function, proves
the first two clauses and a single-scale decay bound, and states what `ChunkDecay` and
`MatchAt.PolymerCross` ask of these activities.

## 1. The activities (`act`)

`StrongCoupling` already writes each Boltzmann factor as `1 + ρ_p` with
`ρ_p = wfun β φ_p = e^{−βφ_p} − 1` (`boltz_eq_subset_sum`), and its `zw bd β ∅ E` is the product-Haar
integral `∫ ∏_{p∈E} ρ_p`; `subset_sum_eq_subPart` and `subPart_univ_eq_partition` give
`Σ_{E ⊆ W} zw ∅ E = Z_W` and `Z_univ = Z`. Here

    act bd β X = zw bd β ∅ X     on nonempty touch-connected X,     0 otherwise.

## 2. The polymer representation (`subPart_eq_polymerZ`, `partition_eq_polymerZ`)

`Inc bd X Y`: some plaquette of `X` equals or touches (shares a link with) one of `Y`. With
`MatchAt.Z inc w S = Σ_{T ⊆ S compatible} ∏_{X∈T} w X`, the hard-core polymer partition function of
`MatchAt`,

    Z_W = MatchAt.Z (Inc bd) (act bd β) W.powerset      at every β, every W,

and at `W = univ` the Wilson partition function is the polymer partition function. The proof:
`comps bd E` (the touch components of `E`) is a compatible family of nonempty touch-connected sets
with union `E` (`comps_sup`, `comps_mem`, `comps_compat`); a compatible family of such sets is the
component family of its union (`comps_family`); and the Haar integral of `∏_{E} ρ_p` factorises over
a compatible family, the members drawing on pairwise disjoint link sets (`zw_sup_eq_prod`, from
`StrongCoupling.zw_split`). So `E ↦ comps E` matches the subsets with the families of nonzero weight
(`Finset.sum_bij_ne_zero`).

## 3. Decay (`act_abs_le`, `decay_of_rate_le`, `decay_tau`)

For `β ≥ 0` and `φ ∈ [0, 2]`, `|e^{−βφ} − 1| ≤ rate β = 1 − e^{−2β}` (`wfun_abs_le`), so
`|act X| ≤ (rate β)^{|X|}`, and `Decay (act bd β) t` whenever `rate β ≤ e^{−t}`. With
`tau β = −log (rate β)`: for `β > 0`, `0 < tau β` (`tau_pos`), `Decay (act bd β) (tau β)`
(`decay_tau`), and `t ≤ tau β ↔ rate β ≤ e^{−t}` (`le_tau_iff`). `rate β < 1` at every `β ≥ 0`, so
the cost per plaquette is positive at every positive coupling; it is large only for small `β`.

The single-plaquette activity is bounded below as well (`rate_mul_mean_le_abs_act_singleton`):
`(rate β / 2) · ∫ φ_p ≤ |act {p}|`, from the convexity of `exp` on the chord over `[0, 2]`.

## 4. The chunk statement (`wilsonChunk`, `chunkDecay_of_rate`, `rate_mean_le_of_chunkDecay`)

No declaration in the tree constructs the block-spin effective action on the coarse torus
`Plaq 4 (nB j L)` (`BlockLattice.blockConf` is an averaged `SU(2)` block step on `ℤ⁴`, with no
effective measure). `wilsonChunk Nc nB βeff j L` is the Wilson activity `act` on the coarse torus at a
coupling `βeff j L`: the chunk activities when the effective action at zoom `j`, side `L` is a Wilson
action at coupling `βeff j L`. On these:

* `chunkDecay_of_rate`: `0 ≤ βeff j L` and `rate (βeff j L) ≤ e^{−σ₀ f L²}` at every `j, L` give
  `ChunkDecay nB (wilsonChunk Nc nB βeff) σ₀ f`; `chunkDecay_of_tau` is the same with
  `σ₀ f L² ≤ tau (βeff j L)`; `matchAt_uniform_of_wilsonChunk` composes it with
  `PolymerCount.matchAt_uniform_of_chunkDecay`.
* `rate_mean_le_of_chunkDecay` (converse, on one plaquette): `ChunkDecay` forces
  `(rate (βeff j L) / 2) · ∫ φ_p ≤ e^{−σ₀ f L²}` at every coarse plaquette `p`.
* `chunkDecay_wilson_witness`: the couplings `βstar (σ₀ f L²)`, `βstar t = −½ log (1 − e^{−t}/2)`,
  are positive and meet `chunkDecay_of_rate` for `σ₀, f ≥ 0`: the hypotheses hold together at
  positive couplings. No declaration here proves `act {p} ≠ 0`, so at `Nc = 1` (where `φ ≡ 0`) the
  witness holds with zero activities; `βstar (σ₀ f L²) → 0` as `L → ∞`, and the witness says nothing
  about the block-spin map.

So on Wilson-form chunk theories `ChunkDecay` at one `σ₀` is, up to the factor `∫ φ_p / 2`, the
statement `1 − e^{−2 βeff j L} ≲ e^{−σ₀ f L²}`: the effective coupling of the chunk theory at side `L`
is exponentially small in `L²`, uniformly in the zoom `j`. That the effective action of the block-spin
map is of Wilson form, and that its coupling runs this way, is the open physics; neither is proved
here.

## 5. `PolymerCross` on the same activities (`WilsonPolymerCross`, `polymerCross_of_wilson`)

`MatchAt.PolymerCross` asks, per pair of cells, for some polymer system with `MatchAt w a κ` and a
cross-term bound by its interaction `Q meet w S A U`. `WilsonPolymerCross` is that clause list with
the polymer type fixed to `Plaq 4 nC` and `w = act` at coupling `β`, and the `MatchAt` clause removed;
`polymerCross_of_wilson` proves `PolymerCross … 1 κ …` from it, supplying `MatchAt (act …) 1 κ` from
`tau β ≥ kpCost zHyper4 κ` (`matchAt_wilson_of_tau`). Every other clause, in particular the
cross-term bound by the interaction, stays a hypothesis.

`Q meet w` is the interaction of the gas whose polymers are incompatible when they overlap
(`MatchAt.meet`); the Wilson partition function is the gas whose polymers are incompatible when they
overlap or touch (`Inc`, §2). With these activities the two partition functions differ, so the
interaction `PolymerCross` reads is not the Wilson gas's own. `ChunkLinks.WilsonLinkPolymerCross`
reads the Wilson gas's own interaction on link polymers. On a finite torus, under the coupling
hypotheses of `polymerCross_of_wilson` and `ChunkLinks.polymerCross_of_wilsonLink`, both clauses force exact
orthogonality of the cross terms beyond a range fixed by the torus side (`CrossTerm.cross_zero_of_far`,
`CrossTerm.cross_zero_of_far_plaq`), so neither is a usable route to (B); the (B) input of the bridge
is `CellLinks.ScreenedCells`, screening with one `(Ke, ξ)` at every aperture and zoom.

DERIVED (module-wide): `0` the empty polymer and the signs; `1` the factor `e^0` split off each
Boltzmann weight and the empty product; `2` the top of the Wilson density's range `[0, 2]`, entering
`rate β = 1 − e^{−2β}` and the chord weight `φ/2`; `4` the dimension of the coarse torus; the `1/2`
of `βstar` undoes that `2`, and its `1/2` inside the logarithm is a choice placing
`rate (βstar t) = e^{−t}/2` below `e^{−t}`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ChunkActivity

open Finset MeasureTheory
open MassGap.StrongCoupling MassGap.PolymerCount MassGap.NoTransitionFlow
open MassGap.WilsonAction MassGap.WilsonLattice MassGap.WilsonReal MassGap.CompactGauge
  MassGap.LatticeGauge

/-! ## 1. The activities -/

section Generic

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **Polymer incompatibility**: some plaquette of `X` equals or touches one of `Y`. -/
def Inc (bd : Pq → List (Lk × Bool)) (X Y : Finset Pq) : Prop :=
  ∃ p ∈ X, ∃ q ∈ Y, p = q ∨ Touch bd p q

open scoped Classical in
noncomputable instance (bd : Pq → List (Lk × Bool)) : DecidableRel (Inc bd) :=
  fun _ _ => Classical.propDecidable _

theorem inc_symm (bd : Pq → List (Lk × Bool)) : MatchAt.SymmRel (Inc bd) := by
  rintro X Y ⟨p, hp, q, hq, h⟩
  exact ⟨q, hq, p, hp, h.elim (fun e => Or.inl e.symm) (fun t => Or.inr (touch_symm t))⟩

open scoped Classical in
/-- **The Wilson polymer activity**: `∫ ∏_{p∈X} (e^{−βφ_p} − 1)` against product Haar on a nonempty
touch-connected `X`, `0` elsewhere. -/
def act (bd : Pq → List (Lk × Bool)) (β : ℝ) (X : Finset Pq) : ℝ :=
  if X.Nonempty ∧ TouchConnected bd X then zw (Nc := Nc) bd β ∅ X else 0

omit [DecidableEq Pq] in
theorem act_empty (bd : Pq → List (Lk × Bool)) (β : ℝ) : act (Nc := Nc) bd β ∅ = 0 := by
  classical
  unfold act
  exact if_neg (fun h => Finset.not_nonempty_empty h.1)

omit [DecidableEq Pq] in
theorem act_of (bd : Pq → List (Lk × Bool)) (β : ℝ) {X : Finset Pq}
    (h : X.Nonempty ∧ TouchConnected bd X) : act (Nc := Nc) bd β X = zw (Nc := Nc) bd β ∅ X := by
  classical
  unfold act
  exact if_pos h

omit [DecidableEq Pq] in
theorem act_ne_zero (bd : Pq → List (Lk × Bool)) (β : ℝ) {X : Finset Pq}
    (h : act (Nc := Nc) bd β X ≠ 0) : X.Nonempty ∧ TouchConnected bd X := by
  classical
  by_contra hn
  unfold act at h
  exact h (if_neg hn)

omit [DecidableEq Pq] in
/-- **The activities are supported on touch-connected polymers.** -/
theorem act_connSupp (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    ConnSupp bd (act (Nc := Nc) bd β) := fun _ h => (act_ne_zero bd β h).2

/-! ## 2. The polymer representation -/

theorem reach_symm {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a b : Pq}
    (h : Reach bd V a b) : Reach bd V b a := by
  unfold Reach at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, touch_symm hbc.2.2⟩ ih

omit [Fintype Lk] [Fintype Pq] [DecidableEq Pq] in
theorem reach_mono {bd : Pq → List (Lk × Bool)} {V W : Finset Pq} (hVW : V ⊆ W) {a b : Pq}
    (h : Reach bd V a b) : Reach bd W a b := by
  unfold Reach at h ⊢
  exact Relation.ReflTransGen.mono (fun _ _ h => ⟨hVW h.1, hVW h.2.1, h.2.2⟩) h

/-- A reach chain from `a` inside `E` stays inside `a`'s component. -/
theorem reach_compOf {bd : Pq → List (Lk × Bool)} {E : Finset Pq} {a p : Pq}
    (h : Reach bd E a p) : Reach bd (compOf bd E a) a p := by
  classical
  have key : ∀ y, Relation.ReflTransGen (fun x y => x ∈ E ∧ y ∈ E ∧ Touch bd x y) a y →
      Reach bd (compOf bd E a) a y := by
    intro y hy
    induction hy with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
        exact Relation.ReflTransGen.tail ih
          ⟨mem_compOf.2 ⟨hbc.1, hab⟩, mem_compOf.2 ⟨hbc.2.1, hab.tail hbc⟩, hbc.2.2⟩
  exact key p h

theorem compOf_touchConnected (bd : Pq → List (Lk × Bool)) (E : Finset Pq) (a : Pq) :
    TouchConnected bd (compOf bd E a) := by
  intro p hp q hq
  have hp' := reach_compOf (mem_compOf.1 hp).2
  have hq' := reach_compOf (mem_compOf.1 hq).2
  have h1 := reach_symm hp'
  unfold Reach at h1 hq' ⊢
  exact h1.trans hq'

theorem compOf_eq_of_mem {bd : Pq → List (Lk × Bool)} {E : Finset Pq} {a q : Pq}
    (hq : q ∈ compOf bd E a) : compOf bd E a = compOf bd E q := by
  have haq := (mem_compOf.1 hq).2
  ext x
  rw [mem_compOf, mem_compOf]
  constructor
  · rintro ⟨hx, hax⟩
    have h1 := reach_symm haq
    unfold Reach at h1 hax ⊢
    exact ⟨hx, h1.trans hax⟩
  · rintro ⟨hx, hqx⟩
    unfold Reach at haq hqx ⊢
    exact ⟨hx, haq.trans hqx⟩

open scoped Classical in
/-- **The touch components of `E`.** -/
def comps (bd : Pq → List (Lk × Bool)) (E : Finset Pq) : Finset (Finset Pq) :=
  E.image (compOf bd E)

theorem comps_mem {bd : Pq → List (Lk × Bool)} {E C : Finset Pq} (hC : C ∈ comps bd E) :
    C.Nonempty ∧ TouchConnected bd C ∧ C ⊆ E := by
  classical
  unfold comps at hC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
  exact ⟨⟨a, self_mem_compOf ha⟩, compOf_touchConnected bd E a, Finset.filter_subset _ _⟩

/-- **The components cover `E`.** -/
theorem comps_sup (bd : Pq → List (Lk × Bool)) (E : Finset Pq) : (comps bd E).sup id = E := by
  classical
  ext p
  rw [Finset.mem_sup]
  constructor
  · rintro ⟨C, hC, hp⟩
    exact (comps_mem hC).2.2 hp
  · intro hp
    exact ⟨compOf bd E p, Finset.mem_image.2 ⟨p, hp, rfl⟩, self_mem_compOf hp⟩

/-- **Distinct components are compatible.** -/
theorem comps_compat (bd : Pq → List (Lk × Bool)) (E : Finset Pq) :
    MatchAt.Compat (Inc bd) (comps bd E) := by
  classical
  intro C hC D hD hCD hinc
  unfold comps at hC hD
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hC
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hD
  obtain ⟨p, hp, q, hq, hpq⟩ := hinc
  have hqa : q ∈ compOf bd E a := by
    rcases hpq with rfl | ht
    · exact hp
    · have hpE := (mem_compOf.1 hp).1
      have hqE := (mem_compOf.1 hq).1
      exact mem_compOf.2 ⟨hqE, (mem_compOf.1 hp).2.tail ⟨hpE, hqE, ht⟩⟩
  exact hCD ((compOf_eq_of_mem hqa).trans (compOf_eq_of_mem hq).symm)

/-- **An admissible family**: nonempty touch-connected members, pairwise compatible. -/
def Admissible (bd : Pq → List (Lk × Bool)) (T : Finset (Finset Pq)) : Prop :=
  (∀ X ∈ T, X.Nonempty ∧ TouchConnected bd X) ∧ MatchAt.Compat (Inc bd) T

/-- In an admissible family, the component of a member's plaquette inside the union is the member. -/
theorem compOf_sup_eq (bd : Pq → List (Lk × Bool)) {T : Finset (Finset Pq)}
    (hT : Admissible bd T) {X : Finset Pq} (hX : X ∈ T) {a : Pq} (ha : a ∈ X) :
    compOf bd (T.sup id) a = X := by
  classical
  have hsub : X ⊆ T.sup id := Finset.le_sup (f := id) hX
  ext y
  rw [mem_compOf]
  constructor
  · rintro ⟨_, hy⟩
    have key : ∀ y, Relation.ReflTransGen
        (fun x y => x ∈ T.sup id ∧ y ∈ T.sup id ∧ Touch bd x y) a y → y ∈ X := by
      intro y hy
      induction hy with
      | refl => exact ha
      | @tail b c _ hbc ih =>
          obtain ⟨Y, hY, hcY⟩ := Finset.mem_sup.1 hbc.2.1
          by_cases hXY : X = Y
          · rw [hXY]; exact hcY
          · exact (hT.2 X hX Y hY hXY ⟨b, ih, c, hcY, Or.inr hbc.2.2⟩).elim
    exact key y hy
  · intro hy
    exact ⟨hsub hy, reach_mono hsub ((hT.1 X hX).2 a ha y hy)⟩

/-- **An admissible family is the component family of its union.** -/
theorem comps_family (bd : Pq → List (Lk × Bool)) {T : Finset (Finset Pq)}
    (hT : Admissible bd T) : comps bd (T.sup id) = T := by
  classical
  ext X
  unfold comps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨Y, hY, haY⟩ := Finset.mem_sup.1 ha
    rw [compOf_sup_eq bd hT hY haY]
    exact hY
  · intro hX
    obtain ⟨a, ha⟩ := (hT.1 X hX).1
    have hsub : X ⊆ T.sup id := Finset.le_sup (f := id) hX
    exact ⟨a, hsub ha, compOf_sup_eq bd hT hX ha⟩

/-- **The Haar integral factorises over a compatible family**:
`∫ ∏_{p ∈ ⋃T} ρ_p = ∏_{X∈T} ∫ ∏_{p∈X} ρ_p`. -/
theorem zw_sup_eq_prod (bd : Pq → List (Lk × Bool)) (β : ℝ) (T : Finset (Finset Pq))
    (hT : MatchAt.Compat (Inc bd) T) :
    zw (Nc := Nc) bd β ∅ (T.sup id) = ∏ X ∈ T, zw (Nc := Nc) bd β ∅ X := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.prod_empty]
      unfold zw
      simp
  | @insert X T hX ih =>
      have hT' : MatchAt.Compat (Inc bd) T := fun x hx y hy hxy =>
        hT x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have hXT : ∀ Y ∈ T, ¬ Inc bd X Y := fun Y hY =>
        hT X (Finset.mem_insert_self _ _) Y (Finset.mem_insert_of_mem hY)
          (fun e => hX (e ▸ hY))
      rw [Finset.sup_insert, Finset.prod_insert hX, ← ih hT']
      have hdisj : Disjoint X (T.sup id) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        obtain ⟨Y, hY, hpY⟩ := Finset.mem_sup.1 hp'
        exact hXT Y hY ⟨p, hp, p, hpY, Or.inl rfl⟩
      have hlinks : Disjoint (X.biUnion (linkSupp bd)) ((T.sup id).biUnion (linkSupp bd)) := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨q, hq, hlq⟩ := Finset.mem_biUnion.1 hl'
        obtain ⟨Y, hY, hqY⟩ := Finset.mem_sup.1 hq
        exact hXT Y hY ⟨p, hp, q, hqY, Or.inr ⟨l, hlp, hlq⟩⟩
      exact zw_split (Nc := Nc) bd β ∅ ∅ ∅ (id X ⊔ T.sup id) X (T.sup id) _ _ hlinks
        (Finset.empty_union ∅).symm rfl (Finset.disjoint_empty_left _) hdisj
        (fun p hp => absurd hp (Finset.notMem_empty p)) (supp_subset_biUnion bd X)
        (fun p hp => absurd hp (Finset.notMem_empty p)) (supp_subset_biUnion bd (T.sup id))

/-- **The subset weight is the product of the component activities.** -/
theorem zw_eq_prod_comps (bd : Pq → List (Lk × Bool)) (β : ℝ) (E : Finset Pq) :
    zw (Nc := Nc) bd β ∅ E = ∏ C ∈ comps bd E, act (Nc := Nc) bd β C := by
  conv_lhs => rw [← comps_sup bd E]
  rw [zw_sup_eq_prod bd β _ (comps_compat bd E)]
  exact Finset.prod_congr rfl (fun C hC =>
    (act_of bd β ⟨(comps_mem hC).1, (comps_mem hC).2.1⟩).symm)

/-- **The polymer representation of the sub-volume partition function**: at every `β` and every
plaquette set `W`, `Z_W = MatchAt.Z (Inc bd) (act bd β) W.powerset`, the hard-core gas of the
connected polymers inside `W`, incompatible when they overlap or touch. -/
theorem subPart_eq_polymerZ (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    subPart (Nc := Nc) bd β W = MatchAt.Z (Inc bd) (act (Nc := Nc) bd β) W.powerset := by
  classical
  rw [← subset_sum_eq_subPart hN bd β W]
  unfold MatchAt.Z
  symm
  refine Finset.sum_bij_ne_zero (fun (T : Finset (Finset Pq)) _ _ => T.sup id) ?_ ?_ ?_ ?_
  · intro T hT _
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨X, hX, hxX⟩ := Finset.mem_sup.1 hx
    have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1) hX
    exact Finset.mem_powerset.1 this hxX
  · intro T₁ h₁ hn₁ T₂ h₂ hn₂ heq
    have ha₁ : Admissible bd T₁ := ⟨fun X hX =>
      act_ne_zero bd β (Finset.prod_ne_zero_iff.1 hn₁ X hX), (Finset.mem_filter.1 h₁).2⟩
    have ha₂ : Admissible bd T₂ := ⟨fun X hX =>
      act_ne_zero bd β (Finset.prod_ne_zero_iff.1 hn₂ X hX), (Finset.mem_filter.1 h₂).2⟩
    rw [← comps_family bd ha₁, ← comps_family bd ha₂]
    exact congrArg (comps bd) heq
  · intro E hE hne
    refine ⟨comps bd E, ?_, ?_, comps_sup bd E⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (fun C hC => ?_), comps_compat bd E⟩
      exact Finset.mem_powerset.2 ((comps_mem hC).2.2.trans (Finset.mem_powerset.1 hE))
    · rw [← zw_eq_prod_comps]
      exact hne
  · intro T hT hn
    have ha : Admissible bd T := ⟨fun X hX =>
      act_ne_zero bd β (Finset.prod_ne_zero_iff.1 hn X hX), (Finset.mem_filter.1 hT).2⟩
    rw [zw_sup_eq_prod bd β T ha.2]
    exact Finset.prod_congr rfl (fun X hX => act_of bd β (ha.1 X hX))

/-- **The Wilson partition function is the polymer partition function** of the activities `act`. -/
theorem partition_eq_polymerZ (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β
      = MatchAt.Z (Inc bd) (act (Nc := Nc) bd β) (Finset.univ : Finset Pq).powerset := by
  rw [← subPart_univ_eq_partition, subPart_eq_polymerZ hN]

/-! ## 3. Decay -/

/-- **The per-plaquette bound** `1 − e^{−2β}`. -/
def rate (β : ℝ) : ℝ := 1 - Real.exp (-(2 * β))

/-- **The cost per plaquette** `−log (1 − e^{−2β})`. -/
def tau (β : ℝ) : ℝ := -Real.log (rate β)

theorem rate_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ rate β := by
  unfold rate
  have : Real.exp (-(2 * β)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem rate_pos {β : ℝ} (hβ : 0 < β) : 0 < rate β := by
  unfold rate
  have : Real.exp (-(2 * β)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

theorem rate_lt_one (β : ℝ) : rate β < 1 := by
  unfold rate
  linarith [Real.exp_pos (-(2 * β))]

theorem tau_pos {β : ℝ} (hβ : 0 < β) : 0 < tau β := by
  unfold tau
  linarith [Real.log_neg (rate_pos hβ) (rate_lt_one β)]

theorem le_tau_iff {β t : ℝ} (hβ : 0 < β) : t ≤ tau β ↔ rate β ≤ Real.exp (-t) := by
  unfold tau
  rw [← Real.log_le_iff_le_exp (rate_pos hβ)]
  constructor <;> intro h <;> linarith

/-- **One factor**: `|e^{−βφ} − 1| ≤ 1 − e^{−2β}` for `β ≥ 0`, `0 ≤ φ ≤ 2`. -/
theorem wfun_abs_le {β φ : ℝ} (hβ : 0 ≤ β) (h0 : 0 ≤ φ) (h2 : φ ≤ 2) :
    |wfun β φ| ≤ rate β := by
  rw [wfun_apply]
  unfold rate
  have h1 : Real.exp (-(β * φ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h3 : Real.exp (-(2 * β)) ≤ Real.exp (-(β * φ)) := Real.exp_le_exp.2 (by nlinarith)
  rw [abs_of_nonpos (by linarith)]
  linarith

omit [DecidableEq Lk] [DecidableEq Pq] in
/-- **The subset weight bound**: `|∫ ∏_{p∈X} ρ_p| ≤ (1 − e^{−2β})^{|X|}` for `β ≥ 0`. -/
theorem zw_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (X : Finset Pq) : |zw (Nc := Nc) bd β ∅ X| ≤ rate β ^ X.card := by
  unfold zw
  have hb : ∀ U : Lk → MassGap.SUN.SU Nc,
      ‖(∏ p ∈ (∅ : Finset Pq), wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ X, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))‖ ≤ rate β ^ X.card := by
    intro U
    rw [Finset.prod_empty, one_mul, Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ p ∈ X, |wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
        ≤ ∏ _p ∈ X, rate β := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun p _ =>
          wfun_abs_le hβ (wilsonDensity_nonneg hN _) (wilsonDensity_le_two hN _))
      _ = rate β ^ X.card := Finset.prod_const _
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) (Filter.Eventually.of_forall hb)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

omit [DecidableEq Pq] in
/-- **The activity bound**: `|act X| ≤ (1 − e^{−2β})^{|X|}` for `β ≥ 0`. -/
theorem act_abs_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (X : Finset Pq) : |act (Nc := Nc) bd β X| ≤ rate β ^ X.card := by
  classical
  unfold act
  split_ifs
  · exact zw_abs_le hN bd hβ X
  · rw [abs_zero]
    exact pow_nonneg (rate_nonneg hβ) _

omit [DecidableEq Pq] in
/-- **Decay at any cost the rate pays for**: `rate β ≤ e^{−t}` gives `Decay (act bd β) t`. -/
theorem decay_of_rate_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β t : ℝ} (hβ : 0 ≤ β)
    (h : rate β ≤ Real.exp (-t)) : Decay (act (Nc := Nc) bd β) t := by
  intro X
  calc |act (Nc := Nc) bd β X| ≤ rate β ^ X.card := act_abs_le hN bd hβ X
    _ ≤ Real.exp (-t) ^ X.card := pow_le_pow_left₀ (rate_nonneg hβ) h _
    _ = Real.exp (-(t * X.card)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

omit [DecidableEq Pq] in
/-- **Decay at the explicit cost** `tau β = −log (1 − e^{−2β})`, for `β > 0`. -/
theorem decay_tau (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 < β) :
    Decay (act (Nc := Nc) bd β) (tau β) :=
  decay_of_rate_le hN bd hβ.le ((le_tau_iff hβ).1 le_rfl)

/-- **The chord bound**: `1 − e^{−βφ} ≥ (φ/2)(1 − e^{−2β})` for `0 ≤ φ ≤ 2`. -/
theorem chord_le {β φ : ℝ} (h0 : 0 ≤ φ) (h2 : φ ≤ 2) :
    φ / 2 * rate β ≤ -wfun β φ := by
  rw [wfun_apply]
  unfold rate
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-(2 * β)))
    (by linarith : (0 : ℝ) ≤ 1 - φ / 2) (by linarith : (0 : ℝ) ≤ φ / 2) (by ring)
  simp only [smul_eq_mul, Real.exp_zero] at hc
  have harg : (1 - φ / 2) * 0 + φ / 2 * -(2 * β) = -(β * φ) := by ring
  rw [harg] at hc
  nlinarith

/-- **The single-plaquette activity from below**: `(rate β / 2) ∫ φ_p ≤ |act {p}|`. -/
theorem rate_mul_mean_le_abs_act_singleton (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (p : Pq) :
    rate β / 2 * ∫ U, wilsonDensity (N := Nc) (wilsonHol bd p U)
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))
      ≤ |act (Nc := Nc) bd β {p}| := by
  have hmeas : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      wilsonDensity (N := Nc) (wilsonHol bd p U)) :=
    measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p)
  have hint1 : Integrable (fun U : Lk → MassGap.SUN.SU Nc =>
      wilsonDensity (N := Nc) (wilsonHol bd p U))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    refine (integrable_const (2 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun U => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (wilsonDensity_nonneg hN _)]
    exact wilsonDensity_le_two hN _
  have hint2 : Integrable (fun U : Lk → MassGap.SUN.SU Nc =>
      wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    simpa using integrable_wprod hN bd β {p}
  have hact : act (Nc := Nc) bd β {p} = ∫ U, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
      ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    rw [act_of bd β ⟨Finset.singleton_nonempty p, touchConnected_singleton bd p⟩]
    unfold zw
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul, Finset.prod_singleton]
  rw [hact, ← integral_const_mul]
  calc ∫ U, rate β / 2 * wilsonDensity (N := Nc) (wilsonHol bd p U)
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))
      ≤ ∫ U, -wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
        refine integral_mono (hint1.const_mul _) hint2.neg (fun U => ?_)
        have := chord_le (β := β) (wilsonDensity_nonneg hN (wilsonHol bd p U))
          (wilsonDensity_le_two hN (wilsonHol bd p U))
        dsimp only
        linarith
    _ = -∫ U, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := integral_neg _
    _ ≤ _ := neg_le_abs _

end Generic

/-! ## 4. The chunk statement -/

/-- **The Wilson chunk activities**: `act` on the coarse torus `Plaq 4 (nB j L)` at coupling
`βeff j L`. -/
def wilsonChunk (Nc : ℕ) (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)] (βeff : ℕ → ℝ → ℝ) :
    ∀ j L, Finset (WilsonHypercubic.Plaq 4 (nB j L)) → ℝ :=
  fun j L => act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nB j L)) (βeff j L)

/-- **`ChunkDecay` from the coupling**: `0 ≤ βeff j L` and `1 − e^{−2 βeff j L} ≤ e^{−σ₀ f L²}` at
every zoom and side give `ChunkDecay` for the Wilson chunk activities. -/
theorem chunkDecay_of_rate {Nc : ℕ} (hN : Nc ≠ 0) (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (βeff : ℕ → ℝ → ℝ) {σ₀ f : ℝ} (hβ : ∀ j L, 0 ≤ βeff j L)
    (h : ∀ j L, rate (βeff j L) ≤ Real.exp (-(σ₀ * f * L ^ 2))) :
    ChunkDecay nB (wilsonChunk Nc nB βeff) σ₀ f := fun j L =>
  ⟨act_empty _ _, act_connSupp _ _, decay_of_rate_le hN _ (hβ j L) (h j L)⟩

/-- **`ChunkDecay` from the cost**: `0 < βeff j L` and `σ₀ f L² ≤ tau (βeff j L)`. -/
theorem chunkDecay_of_tau {Nc : ℕ} (hN : Nc ≠ 0) (nB : ℕ → ℝ → ℕ) [∀ j L, NeZero (nB j L)]
    (βeff : ℕ → ℝ → ℝ) {σ₀ f : ℝ} (hβ : ∀ j L, 0 < βeff j L)
    (h : ∀ j L, σ₀ * f * L ^ 2 ≤ tau (βeff j L)) :
    ChunkDecay nB (wilsonChunk Nc nB βeff) σ₀ f :=
  chunkDecay_of_rate hN nB βeff (fun j L => (hβ j L).le)
    (fun j L => (le_tau_iff (hβ j L)).1 (h j L))

/-- **The match at every zoom from the coupling**, on the Wilson chunk activities. -/
theorem matchAt_uniform_of_wilsonChunk {Nc : ℕ} (hN : Nc ≠ 0) (nB : ℕ → ℝ → ℕ)
    [∀ j L, NeZero (nB j L)] (βeff : ℕ → ℝ → ℝ) {σ₀ f κ : ℝ} (hσ₀ : 0 < σ₀) (hf : 0 < f)
    (hκ : 0 ≤ κ) (hβ : ∀ j L, 0 ≤ βeff j L)
    (h : ∀ j L, rate (βeff j L) ≤ Real.exp (-(σ₀ * f * L ^ 2))) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt.MatchAt (wilsonChunk Nc nB βeff j L) 1 κ :=
  matchAt_uniform_of_chunkDecay nB _ hσ₀ hf hκ (chunkDecay_of_rate hN nB βeff hβ h)

/-- **What `ChunkDecay` forces on one plaquette**:
`(1 − e^{−2 βeff j L})/2 · ∫ φ_p ≤ e^{−σ₀ f L²}` at every coarse plaquette `p`. -/
theorem rate_mean_le_of_chunkDecay {Nc : ℕ} (hN : Nc ≠ 0) (nB : ℕ → ℝ → ℕ)
    [∀ j L, NeZero (nB j L)] (βeff : ℕ → ℝ → ℝ) {σ₀ f : ℝ}
    (h : ChunkDecay nB (wilsonChunk Nc nB βeff) σ₀ f) (j : ℕ) (L : ℝ)
    (p : WilsonHypercubic.Plaq 4 (nB j L)) :
    rate (βeff j L) / 2 * ∫ U, wilsonDensity (N := Nc)
        (wilsonHol (WilsonHypercubic.bd (d := 4) (n := nB j L)) p U)
        ∂(Measure.pi (fun _ : WilsonHypercubic.Link 4 (nB j L) => probHaar (MassGap.SUN.SU Nc)))
      ≤ Real.exp (-(σ₀ * f * L ^ 2)) := by
  have h1 := rate_mul_mean_le_abs_act_singleton hN
    (WilsonHypercubic.bd (d := 4) (n := nB j L)) (βeff j L) p
  have h2 := (h j L).2.2 {p}
  rw [Finset.card_singleton, Nat.cast_one, mul_one] at h2
  exact h1.trans h2

/-- **A coupling meeting a cost**: `βstar t = −½ log (1 − e^{−t}/2)`. -/
def βstar (t : ℝ) : ℝ := -(1 / 2) * Real.log (1 - Real.exp (-t) / 2)

theorem βstar_spec {t : ℝ} (ht : 0 ≤ t) :
    0 < βstar t ∧ rate (βstar t) ≤ Real.exp (-t) := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hp := Real.exp_pos (-t)
  have hx0 : 0 < 1 - Real.exp (-t) / 2 := by linarith
  have hx1 : 1 - Real.exp (-t) / 2 < 1 := by linarith
  refine ⟨?_, ?_⟩
  · unfold βstar
    nlinarith [Real.log_neg hx0 hx1]
  · unfold rate βstar
    have : -(2 * (-(1 / 2) * Real.log (1 - Real.exp (-t) / 2)))
        = Real.log (1 - Real.exp (-t) / 2) := by ring
    rw [this, Real.exp_log hx0]
    linarith

/-- **The coupling hypotheses hold at positive couplings**: for `σ₀, f ≥ 0` the couplings
`βstar (σ₀ f L²)` are positive and the Wilson chunk activities at them meet `ChunkDecay`. -/
theorem chunkDecay_wilson_witness {Nc : ℕ} (hN : Nc ≠ 0) (nB : ℕ → ℝ → ℕ)
    [∀ j L, NeZero (nB j L)] {σ₀ f : ℝ} (hσ₀ : 0 ≤ σ₀) (hf : 0 ≤ f) :
    (∀ j L, 0 < (fun (_ : ℕ) (L : ℝ) => βstar (σ₀ * f * L ^ 2)) j L) ∧
    ChunkDecay nB (wilsonChunk Nc nB (fun _ L => βstar (σ₀ * f * L ^ 2))) σ₀ f := by
  have ht : ∀ L : ℝ, 0 ≤ σ₀ * f * L ^ 2 := fun L => by positivity
  exact ⟨fun _ L => (βstar_spec (ht L)).1,
    chunkDecay_of_rate hN nB _ (fun _ L => (βstar_spec (ht L)).1.le)
      (fun _ L => (βstar_spec (ht L)).2)⟩

/-! ## 5. `PolymerCross` on the same activities -/

/-- **One coarse torus**: `tau β ≥ kpCost zHyper4 κ` gives `MatchAt (act …) 1 κ` on `Plaq 4 n`. -/
theorem matchAt_wilson_of_tau {Nc : ℕ} (hN : Nc ≠ 0) {n : ℕ} [NeZero n] {β κ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : kpCost zHyper4 κ ≤ tau β) :
    MatchAt.MatchAt (act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := n)) β) 1 κ :=
  matchAt_of_decay hκ (act_empty _ _) (act_connSupp _ _) (decay_tau hN _ hβ) hτ

section Cross

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **`PolymerCross` on the Wilson activities**: the clauses of `MatchAt.PolymerCross` other than
`MatchAt`, with the polymer type `Plaq 4 nC` and `w = act` at coupling `β`. The cross-term clause
reads `Q meet act`, the interaction of the overlap gas, which is not the Wilson gas's own (that gas is
hard-core under `Inc`, §2). -/
def WilsonPolymerCross (Nc nC : ℕ) [NeZero nC] (β : ℝ) (P : E →L[ℝ] E) (v : Fin n → E)
    (d : Fin n → Fin n → ℕ) (Kx M L r₀ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ (ρ : WilsonHypercubic.Plaq 4 nC → WilsonHypercubic.Plaq 4 nC → ℝ)
    (dset : WilsonHypercubic.Plaq 4 nC → ℝ) (U A S : Finset (Finset (WilsonHypercubic.Plaq 4 nC)))
    (Λ : Finset (WilsonHypercubic.Plaq 4 nC)) (R : ℝ),
    (∀ x y, dset x ≤ dset y + ρ x y) ∧
    (∀ X, act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β X ≠ 0 →
      ∀ x ∈ X, ∀ y ∈ X, ρ x y ≤ X.card) ∧
    (∀ Y ∈ U, act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β Y ≠ 0 →
      ∀ y ∈ Y, dset y ≤ 0) ∧ (∀ y ∈ Λ, R ≤ dset y) ∧
    (∀ X ∈ A, (X ∩ Λ).Nonempty) ∧ (∀ X ∈ A, X ∉ U) ∧ (Λ.card : ℝ) ≤ M ∧
    (d i j : ℝ) * L - r₀ ≤ R ∧
    |inner ℝ (P (v i)) (P (v j))| ≤ Kx * |MatchAt.Q MatchAt.meet
      (act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β) S A U| * (‖v i‖ * ‖v j‖)

/-- **`PolymerCross` from the Wilson clauses**: with `tau β ≥ kpCost zHyper4 κ` the `MatchAt` clause
is supplied by the Wilson activities themselves. The cross-term clause it leaves open reads
`Q meet act`, which is not the interaction of the Wilson gas. -/
theorem polymerCross_of_wilson {Nc nC : ℕ} [NeZero nC] (hN : Nc ≠ 0) {β κ : ℝ} (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hτ : kpCost zHyper4 κ ≤ tau β) {P : E →L[ℝ] E} {v : Fin n → E}
    {d : Fin n → Fin n → ℕ} {Kx M L r₀ : ℝ} (h : WilsonPolymerCross Nc nC β P v d Kx M L r₀) :
    MatchAt.PolymerCross P v d Kx M 1 κ L r₀ := by
  intro i j hij
  obtain ⟨ρ, dset, U, A, S, Λ, R, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h i j hij
  exact ⟨WilsonHypercubic.Plaq 4 nC, inferInstance, inferInstance,
    act (Nc := Nc) (WilsonHypercubic.bd (d := 4) (n := nC)) β, ρ, dset, U, A, S, Λ, R,
    matchAt_wilson_of_tau hN hβ hκ hτ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Cross

#print axioms inc_symm
#print axioms act_empty
#print axioms act_connSupp
#print axioms comps_sup
#print axioms comps_compat
#print axioms comps_family
#print axioms zw_sup_eq_prod
#print axioms zw_eq_prod_comps
#print axioms subPart_eq_polymerZ
#print axioms partition_eq_polymerZ
#print axioms tau_pos
#print axioms le_tau_iff
#print axioms wfun_abs_le
#print axioms zw_abs_le
#print axioms act_abs_le
#print axioms decay_of_rate_le
#print axioms decay_tau
#print axioms chord_le
#print axioms rate_mul_mean_le_abs_act_singleton
#print axioms chunkDecay_of_rate
#print axioms chunkDecay_of_tau
#print axioms matchAt_uniform_of_wilsonChunk
#print axioms rate_mean_le_of_chunkDecay
#print axioms βstar_spec
#print axioms chunkDecay_wilson_witness
#print axioms matchAt_wilson_of_tau
#print axioms polymerCross_of_wilson

end MassGap.ChunkActivity
