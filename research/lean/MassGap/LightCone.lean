import Mathlib
import MassGap.Detectability

noncomputable section

/-!
# MassGap.LightCone — the light-cone identity for layered products of conditional expectations

`SweepFilter.sweep_cov` asks `⟨Sⁱ f, g⟩ = ⟨f, g⟩` for `i ≤ d`. This module proves that identity for
products of form-orthogonal projections arranged in layers, from two locality properties of each
projection and its self-adjointness; no expectation, no measure.

## Setting (`Setting`)

A symmetric positive semi-definite form `B`, projections `P i` that are `B`-self-adjoint, a predicate
`RN m x` ("`x` does not read the link `m`"), and for each `i` a set `box i` of links and a set `nb i ⊇ box i`
(the box and the links sharing a plaquette with it). Each projection
- (`far`) keeps "does not read `m`" for every `m ∉ nb i`;
- (`keep_reads`, `keep_null`) acts on a vector reading no link of `box i` as the identity up to a null
  vector, and keeps every link it does not read.
For the block conditional expectations of the Wilson measure these are `BlockCommute.blkAvg_update_far`,
`BlockHeatBath.torusBlkCondExp_keeps` and `torusBlkCondExp_selfAdj`. A layer (`Layer`) is a list without
repetition whose distinct members commute and whose boxes avoid each other's neighbourhoods.

## What it gives

1. `layer_pair`: for `x` reading only `A` and `y` reading no link of any box of the layer that meets `A`,
   `B(seqLin c x, y) = B(x, y)`: each projection either fixes `x` up to a null vector (its box misses `A`)
   or, commuted to the front of its layer, fixes `y` up to a null vector.
2. `layer_reads`: after a layer, `x` reads only `A ∪ ⋃ {nb i | box i meets A}` (boxes of one layer do not
   chain, since each misses the others' neighbourhoods).
3. `cone`: with a potential `ψ` rising by at most `W` from a box to its neighbourhood, `x` reading only
   `{ψ ≤ L}` and `y` reading no link of `{ψ ≤ L + W·(number of layers)}`:
   `B(seqLin (layers.flatten) x, y) = B(x, y)`.
4. `seqLin_pow`: `(seqLin P w)ᵏ = seqLin P (k copies of w)`.

DERIVED (module-wide): `0` the null value and the empty product; `1` the successor of a power.
-/

namespace MassGap.LightCone

open MassGap.Detectability

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι Λ : Type*}

/-- **The locality setting.** See the module docstring.

DERIVED: `0` the null value and the sign. -/
structure Setting (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : ι → E →ₗ[ℝ] E) (RN : Λ → E → Prop)
    (box nb : ι → Set Λ) : Prop where
  symm : ∀ x y, B x y = B y x
  psd : ∀ x, 0 ≤ B x x
  sa : ∀ i x y, B (P i x) y = B x (P i y)
  far : ∀ i x m, m ∉ nb i → RN m x → RN m (P i x)
  keep_reads : ∀ i x, (∀ m ∈ box i, RN m x) → ∀ m, RN m x → RN m (P i x)
  keep_null : ∀ i x, (∀ m ∈ box i, RN m x) → B (P i x - x) (P i x - x) = 0
  box_sub : ∀ i, box i ⊆ nb i

/-- **`x` reads only links of `A`.**

DERIVED: no numeral. -/
def ReadsOnly (RN : Λ → E → Prop) (A : Set Λ) (x : E) : Prop := ∀ m, m ∉ A → RN m x

omit [AddCommGroup E] [Module ℝ E] in
/-- DERIVED: no numeral. -/
theorem ReadsOnly.mono {RN : Λ → E → Prop} {A A' : Set Λ} {x : E} (h : ReadsOnly RN A x)
    (hA : A ⊆ A') : ReadsOnly RN A' x :=
  fun m hm => h m (fun h' => hm (hA h'))

#print axioms ReadsOnly.mono

/-- **A layer**: no repetition; distinct members commute and each box misses the other's neighbourhood.

DERIVED: no numeral. -/
def Layer (P : ι → E →ₗ[ℝ] E) (box nb : ι → Set Λ) (c : List ι) : Prop :=
  c.Nodup ∧ ∀ i ∈ c, ∀ j ∈ c, i ≠ j → (∀ x, P i (P j x) = P j (P i x)) ∧ Disjoint (box j) (nb i)

/-- The tail of a layer is a layer.

DERIVED: no numeral. -/
theorem Layer.tail {P : ι → E →ₗ[ℝ] E} {box nb : ι → Set Λ} {i : ι} {c : List ι}
    (h : Layer P box nb (i :: c)) : Layer P box nb c :=
  ⟨(List.nodup_cons.mp h.1).2, fun a ha b hb hab =>
    h.2 a (List.mem_cons_of_mem i ha) b (List.mem_cons_of_mem i hb) hab⟩

#print axioms Layer.tail

/-- The head of a layer against its tail.

DERIVED: no numeral. -/
theorem Layer.head {P : ι → E →ₗ[ℝ] E} {box nb : ι → Set Λ} {i : ι} {c : List ι}
    (h : Layer P box nb (i :: c)) {j : ι} (hj : j ∈ c) :
    (∀ x, P i (P j x) = P j (P i x)) ∧ Disjoint (box j) (nb i) := by
  have hne : i ≠ j := fun e => (List.nodup_cons.mp h.1).1 (e ▸ hj)
  exact h.2 i (List.mem_cons_self) j (List.mem_cons_of_mem i hj) hne

#print axioms Layer.head

/-- A projection commuting with every member of a list commutes with its product.

DERIVED: no numeral. -/
theorem seqLin_comm (P : ι → E →ₗ[ℝ] E) (i : ι) (c : List ι)
    (h : ∀ j ∈ c, ∀ x, P i (P j x) = P j (P i x)) (x : E) :
    seqLin P c (P i x) = P i (seqLin P c x) := by
  induction c generalizing x with
  | nil => rfl
  | cons j c ih =>
    rw [seqLin_cons, seqLin_cons, ← h j List.mem_cons_self x,
      ih (fun j' hj' => h j' (List.mem_cons_of_mem j hj')) (P j x)]

#print axioms seqLin_comm

/-- `(seqLin P w)ᵏ` is the product along `k` copies of `w`.

DERIVED: `0` the empty power; `1` the successor. -/
theorem seqLin_pow (P : ι → E →ₗ[ℝ] E) (w : List ι) (k : ℕ) (x : E) :
    (seqLin P w ^ k) x = seqLin P (List.replicate k w).flatten x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, List.replicate_succ, List.flatten_cons, seqLin_append]

#print axioms seqLin_pow

section Cone

variable {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} {P : ι → E →ₗ[ℝ] E} {RN : Λ → E → Prop} {box nb : ι → Set Λ}

/-- A null vector pairs to zero.

DERIVED: `0` the null value; `2` the square of Cauchy–Schwarz. -/
theorem null_pair (hS : Setting B P RN box nb) {z : E} (hz : B z z = 0) (w : E) : B z w = 0 := by
  have h := ChebyshevFilter.form_cs B hS.symm hS.psd z w
  rw [hz, zero_mul] at h
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h (sq_nonneg _))

#print axioms null_pair

/-- **One layer is invisible to a vector reading none of the boxes it can reach.**

DERIVED: no numeral. -/
theorem layer_pair (hS : Setting B P RN box nb) (c : List ι) (hc : Layer P box nb c) (A : Set Λ)
    (x y : E) (hx : ReadsOnly RN A x)
    (hy : ∀ i ∈ c, (box i ∩ A).Nonempty → ∀ m ∈ box i, RN m y) :
    B (seqLin P c x) y = B x y := by
  induction c with
  | nil => rfl
  | cons i c ih =>
    have ih' := ih hc.tail (fun j hj => hy j (List.mem_cons_of_mem i hj))
    rw [seqLin_cons]
    by_cases hA : (box i ∩ A).Nonempty
    · have hyi := hy i List.mem_cons_self hA
      have hnull := hS.keep_null i y hyi
      rw [seqLin_comm P i c (fun j hj => (hc.head hj).1) x, hS.sa]
      have e : B (seqLin P c x) (P i y) = B (seqLin P c x) y + B (P i y - y) (seqLin P c x) := by
        rw [hS.symm (P i y - y), map_sub]
        ring
      rw [e, null_pair hS hnull, add_zero, ih']
    · have hxi : ∀ m ∈ box i, RN m x := fun m hm =>
        hx m (fun hmA => hA ⟨m, hm, hmA⟩)
      have hnull := hS.keep_null i x hxi
      have e : seqLin P c (P i x) = seqLin P c x + seqLin P c (P i x - x) := by
        rw [map_sub]; abel
      rw [e, map_add, LinearMap.add_apply, seqLin_adj B P hS.sa c (P i x - x),
        null_pair hS hnull, add_zero, ih']

#print axioms layer_pair

/-- **The reading set after one layer.**

DERIVED: no numeral. -/
theorem layer_reads (hS : Setting B P RN box nb) (c : List ι) (hc : Layer P box nb c)
    (A Y : Set Λ) (x : E) (hx : ReadsOnly RN (A ∪ Y) x) (hY : ∀ i ∈ c, Disjoint (box i) Y) :
    ReadsOnly RN (A ∪ Y ∪ {m | ∃ i ∈ c, (box i ∩ A).Nonempty ∧ m ∈ nb i}) (seqLin P c x) := by
  induction c generalizing x Y with
  | nil =>
    exact hx.mono (fun m hm => Or.inl hm)
  | cons i c ih =>
    rw [seqLin_cons]
    by_cases hA : (box i ∩ A).Nonempty
    · have hx' : ReadsOnly RN (A ∪ (Y ∪ nb i)) (P i x) := by
        intro m hm
        simp only [Set.mem_union, not_or] at hm
        exact hS.far i x m hm.2.2 (hx m (by simp only [Set.mem_union, not_or]; exact ⟨hm.1, hm.2.1⟩))
      have hY' : ∀ j ∈ c, Disjoint (box j) (Y ∪ nb i) := fun j hj =>
        Disjoint.union_right (hY j (List.mem_cons_of_mem i hj)) (hc.head hj).2
      refine (ih hc.tail (Y ∪ nb i) (P i x) hx' hY').mono ?_
      intro m hm
      simp only [Set.mem_union, Set.mem_setOf_eq] at hm ⊢
      rcases hm with (hm | hm | hm) | ⟨j, hj, hjA, hjm⟩
      · exact Or.inl (Or.inl hm)
      · exact Or.inl (Or.inr hm)
      · exact Or.inr ⟨i, List.mem_cons_self, hA, hm⟩
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, hjA, hjm⟩
    · have hxi : ∀ m ∈ box i, RN m x := by
        intro m hm
        refine hx m ?_
        rintro (hmA | hmY)
        · exact hA ⟨m, hm, hmA⟩
        · exact Set.disjoint_left.mp (hY i List.mem_cons_self) hm hmY
      have hx' : ReadsOnly RN (A ∪ Y) (P i x) := fun m hm => hS.keep_reads i x hxi m (hx m hm)
      refine (ih hc.tail Y (P i x) hx' (fun j hj => hY j (List.mem_cons_of_mem i hj))).mono ?_
      intro m hm
      simp only [Set.mem_union, Set.mem_setOf_eq] at hm ⊢
      rcases hm with hm | ⟨j, hj, hjA, hjm⟩
      · exact Or.inl hm
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, hjA, hjm⟩

#print axioms layer_reads

/-- **The light-cone identity for a layered product.** See the module docstring, item 3.

DERIVED: no numeral beyond the layer count. -/
theorem cone (hS : Setting B P RN box nb) (ψ : Λ → ℕ) (W : ℕ)
    (hψ : ∀ i, ∀ m ∈ box i, ∀ m' ∈ nb i, ψ m' ≤ ψ m + W)
    (ls : List (List ι)) (hls : ∀ c ∈ ls, Layer P box nb c) (L : ℕ) (x y : E)
    (hx : ReadsOnly RN {m | ψ m ≤ L} x) (hy : ∀ m, ψ m ≤ L + W * ls.length → RN m y) :
    B (seqLin P ls.flatten x) y = B x y := by
  induction ls generalizing x L with
  | nil => rfl
  | cons c ls ih =>
    have hc := hls c List.mem_cons_self
    rw [List.flatten_cons, seqLin_append]
    have hreads := layer_reads hS c hc {m | ψ m ≤ L} ∅ x
      (hx.mono (fun m hm => Or.inl hm)) (fun i _ => Set.disjoint_empty _)
    have hx' : ReadsOnly RN {m | ψ m ≤ L + W} (seqLin P c x) := by
      refine hreads.mono ?_
      intro m hm
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_empty_iff_false, or_false] at hm ⊢
      rcases hm with hm | ⟨i, _, ⟨m₀, hm₀b, hm₀A⟩, hmn⟩
      · omega
      · have := hψ i m₀ hm₀b m hmn
        simp only [Set.mem_setOf_eq] at hm₀A
        omega
    have hy' : ∀ m, ψ m ≤ L + W + W * ls.length → RN m y := by
      intro m hm
      refine hy m ?_
      rw [List.length_cons, Nat.mul_succ]
      linarith
    rw [ih (fun c' hc' => hls c' (List.mem_cons_of_mem c hc')) (L + W) (seqLin P c x) hx' hy']
    refine layer_pair hS c hc {m | ψ m ≤ L} x y hx (fun i _ hiA m hm => ?_)
    obtain ⟨m₀, hm₀b, hm₀A⟩ := hiA
    have h1 := hψ i m₀ hm₀b m (hS.box_sub i hm)
    simp only [Set.mem_setOf_eq] at hm₀A
    refine hy m ?_
    rw [List.length_cons, Nat.mul_succ]
    linarith [Nat.zero_le (W * ls.length)]

#print axioms cone

end Cone

end MassGap.LightCone
