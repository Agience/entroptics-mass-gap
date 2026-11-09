import Mathlib
import MassGap.StrongTransferGap
import MassGap.RectTorusState
import MassGap.GeneralDecay
import MassGap.StrongCouplingGap

/-!
# MassGap.UniformRelayStrong — the strong-coupling relay gap, uniform in the slice

`uniformRelayGap` proves `StrongTransferGap.UniformRelayGap N`: there are `β₀ > 0` and `m > 0` such that at
every `0 ≤ β ≤ β₀`, every direction `i` and every transverse extent `T`, the slice transfer
`K = kT i T N β` has a unit eigenpair `(λ, φ)` with `‖K − λ φ⊗φ‖ ≤ |λ| e^{−m}`. `uniformSliceDecay` is the
time-decay form `StrongTransferGap.UniformSliceDecay N`. The rate is `e^{−m} = coreRate 64 β₀`, fixed before
`i` and `T`. Declarations are in the namespace `MassGap.UniformRelayStrong`.

## 1. The rectangular torus as a cluster-expansion carrier

The rectangular Wilson torus `RectWilson.sysR L N` is `wilsonSystem (rbd L)`, so
`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` reads on it once the carrier facts hold:
`touchDeg (rbd L) ≤ 64` (`touchDeg_rbd_le`, through `linkMult_rbd_le`), a link sits at its plaquette's site or
one step above on every axis (`rlink_site_coord`), the boxes `rCube b R` of forward offsets are touch-connected
from a diagonal base plaquette (`rreach_from_base`), and `Touch` moves the circle distance along an axis by at
most one (`rcircDist_lipschitz`, `r_not_mem_ball`). No extent enters these bounds.

## 2. Two slices

A slice function `u` read at time `s` is local on the spatial links at time `s` (`localOnLinks_sliceObs`);
their halo lies in the two-layer slab `rCube (layB μ s) (layR L μ)` (`linkHalo_subset_layer`), of at most
`32 |TT|` plaquettes (`card_layer_le`). On the torus of time extent `2j + 2` the slabs at times `0` and
`j + 1` are more than `j` touch-steps apart, so (`rect_pair_cluster`, `slice_pair_cluster`)

    |E[u(V₀) u(V_{j+1})] − E[u(V₀)] E[u(V_{j+1})]|  ≤  coreConstG (2 ‖u‖²) 64 β U · coreRate 64 β ^ (j + 2 − U),

`U = 64 |TT|`, with the torus read as `pairExp` of `a = K^{∗(j+1)}` (`RectTorusState.rectState_pairObs`).
The transverse extent enters the prefactor only; the rate is `coreRate 64 β`.

## 3. From two slices to the remainder

With `a = λ^{j+1} φ⊗φ + r`, `r = (K − λ φ⊗φ)^{∗(j+1)}` (`KernelPower.iter_decomp`), the three numerators of the
two-slice read expand into `λ^{2(j+1)} ⟨φ², u⟩²`, the cross term `2 λ^{j+1} ∫∫ (φu) r (φu)` and corrections
bounded by `hs(r)` (`pair_expand`, `mid_right_zero`, `mid_left_zero`), and `alg_w` solves for the cross term
(`w_bound`). The cross term is the form `⟨w, R^{j+1} w⟩` of the remainder operator `R` on `w = φu`
(`pow_apply_ae`, `inner_pow_eq`).

## 4. The bootstrap

* `floor_decay`: a kernel with values in `[a, 1]`, `a > 0`, and a positive eigenfunction has
  `hs(r_j) ≤ C (λ q₀)^{2(j+1)}` with some `q₀ < 1`: `K − (a/B²) φ⊗φ` is nonnegative with eigenvalue
  `λ − a/B²`, and its iterates are bounded by positivity alone.
* `gap_step`: decay of `hs(r_j)` at `λ q` and two-slice decay at `ρ` give per-vector decay
  `‖Rᵗ w‖ ≤ C_w (λ max ρ q²)ᵗ` on continuous `w`, since `‖Rᵗ w‖² = ⟨w, R^{2t} w⟩`; the continuous functions are
  dense (`ContinuousMap.toLp_denseRange`; `φ` is continuous, `continuous_eigen`), so
  `‖R‖ ≤ λ max ρ q²` (`StrongTransferGap.opNorm_le_of_decay_dense`). `KernelPower.hs_iter_le` turns the
  operator bound back into decay of `hs(r_j)`.
* `gap_of_pairDecay`: iterating, `‖R‖ ≤ λ max ρ (q₀^{2^m})` for every `m`, hence `‖R‖ ≤ λ ρ`.

## 5. The uniform gap

`slice_relay_gap`: at `0 ≤ β` with `coreRate 64 β ≤ ρ < 1`, every slice has the Jentzsch top
(`JentzschKT.exists_pos_eigen_kT`) with remainder norm at most `|λ| ρ`; an empty transverse extent is a point
(`relay_gap_empty`). `uniformRelayGap` takes `β₀` half the threshold of
`StrongCoupling.core_rate_lt_one_of_small_hypercubic 4` and `ρ = coreRate 64 β₀`, using `coreRate_mono_beta`.

## Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: nothing.
* Assumed: nothing beyond the imported modules.

DERIVED (module-wide): `16 * 4 = 64` the touch degree of the four-dimensional carrier; `4` the boundary word and
the dimension; `2` the doubling, the square and the two time layers; `1` the lattice step and the ceiling of
the kernel; `5` the correction count of `alg_w`; `1/2` the floor of `q₀`; `0` the lower ends.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.UniformRelayStrong

open MeasureTheory Filter Topology
open MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower MassGap.SlabKernelOperator
open MassGap.StrongCoupling (linkSupp Touch Reach ball linkHalo touchDeg linkMult touchNbrs circDist)

/-! ## 1. The rectangular torus as a cluster-expansion carrier -/

section Geom

variable {L : Fin 4 → ℕ} [∀ k, NeZero (L k)]

/-- The coordinates of `rshift L a x`: `x τ + 1` on the axis `a`, `x τ` elsewhere. DERIVED: `1` the
step. -/
theorem rshift_apply (a τ : Fin 4) (x : RSite L) :
    rshift L a x τ = if a = τ then x τ + 1 else x τ := by
  unfold rshift
  by_cases h : a = τ
  · subst h; simp
  · rw [Function.update_of_ne (Ne.symm h)]; simp [h]

/-- One step back along `μ`. DERIVED: `1` the step. -/
def runshift (μ : Fin 4) (x : RSite L) : RSite L := Function.update x μ (x μ - 1)

/-- DERIVED: no numeral. -/
theorem runshift_rshift (μ : Fin 4) (x : RSite L) : runshift μ (rshift L μ x) = x := by
  unfold runshift rshift
  rw [Function.update_self, Function.update_idem]
  simp

/-- DERIVED: no numeral. -/
theorem rshift_runshift (μ : Fin 4) (x : RSite L) : rshift L μ (runshift μ x) = x := by
  unfold runshift rshift
  rw [Function.update_self, Function.update_idem]
  simp

/-- **A link of a rectangular plaquette sits at the plaquette's site or one step above it, on every
axis.** DERIVED: `1` the step. -/
theorem rlink_site_coord (τ a b : Fin 4) (x : RSite L) (ld : Fin 4) (ls : RSite L)
    (hl : (ld, ls) ∈ linkSupp (rbd L) ((a, b), x)) :
    ls τ = x τ ∨ ls τ = x τ + 1 := by
  have hsite : ls = x ∨ ls = rshift L a x ∨ ls = rshift L b x := by
    simp only [linkSupp, rbd, List.map_cons, List.map_nil, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hl
    tauto
  rcases hsite with h | h | h
  · exact Or.inl (by rw [h])
  · rw [h, rshift_apply]; split_ifs with he
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [h, rshift_apply]; split_ifs with he
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The first link of `((a, b), x)` is `(a, x)`. DERIVED: no numeral. -/
theorem rhead_mem (q : RPlaq L) : (q.1.1, q.2) ∈ linkSupp (rbd L) q := by
  simp [linkSupp, rbd]

/-- The last link of `((a, b), x)` is `(b, x)`. DERIVED: no numeral. -/
theorem rlast_mem (q : RPlaq L) : (q.1.2, q.2) ∈ linkSupp (rbd L) q := by
  simp [linkSupp, rbd]

/-- The second link of `((a, b), x)` is `(b, x + e_a)`. DERIVED: no numeral. -/
theorem rsecond_mem (q : RPlaq L) : (q.1.2, rshift L q.1.1 q.2) ∈ linkSupp (rbd L) q := by
  simp [linkSupp, rbd]

open scoped Classical in
/-- **A link of the rectangular torus is named by at most `16` plaquettes**: one slot of the boundary
word and the plane's other direction fix the plaquette. DERIVED: `4 * 4` slots times directions. -/
theorem linkMult_rbd_le (l : RLink L) : linkMult (rbd L) l ≤ 4 * 4 := by
  classical
  obtain ⟨δ, y⟩ := l
  set g : Fin 4 × Fin 4 → RPlaq L := fun z =>
    if z.1 = 0 then ((δ, z.2), y)
    else if z.1 = 1 then ((z.2, δ), runshift z.2 y)
    else if z.1 = 2 then ((δ, z.2), runshift z.2 y)
    else ((z.2, δ), y) with hg
  have hsub : (Finset.univ.filter (fun q : RPlaq L => (δ, y) ∈ linkSupp (rbd L) q))
      ⊆ Finset.image g Finset.univ := by
    intro q hq
    obtain ⟨⟨μ, ν⟩, x⟩ := q
    have hmem := (Finset.mem_filter.mp hq).2
    simp only [linkSupp, rbd, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Prod.mk.injEq] at hmem
    refine Finset.mem_image.mpr ?_
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨(0, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · exact ⟨(1, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg, runshift_rshift]⟩
    · exact ⟨(2, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg, runshift_rshift]⟩
    · exact ⟨(3, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · simp at h
  unfold linkMult
  calc (Finset.univ.filter (fun q : RPlaq L => (δ, y) ∈ linkSupp (rbd L) q)).card
      ≤ (Finset.image g Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 × Fin 4)).card := Finset.card_image_le
    _ = 4 * 4 := by simp

/-- A rectangular plaquette names at most four links. DERIVED: `4` the boundary word's length. -/
theorem linkSupp_rbd_card_le (q : RPlaq L) : (linkSupp (rbd L) q).card ≤ 4 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simp [rbd]

open scoped Classical in
/-- **`touchDeg (rbd L) ≤ 16 * 4`**, whatever the extents. DERIVED: `16 = 4 · 4` links per plaquette
times plaquettes per link slot; `4` the second directions. -/
theorem touchDeg_rbd_le : touchDeg (rbd L) ≤ 16 * 4 := by
  classical
  refine Finset.sup_le (fun p _ => ?_)
  refine le_trans (StrongCoupling.touchNbrs_card_le (rbd L) p) ?_
  calc ∑ l ∈ linkSupp (rbd L) p, linkMult (rbd L) l
      ≤ ∑ _l ∈ linkSupp (rbd L) p, 4 * 4 := Finset.sum_le_sum (fun l _ => linkMult_rbd_le l)
    _ = (linkSupp (rbd L) p).card * (4 * 4) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * (4 * 4) := Nat.mul_le_mul_right _ (linkSupp_rbd_card_le p)
    _ = 16 * 4 := by norm_num

/-- A site lies in the box of forward offsets `R` at `b`. DERIVED: no numeral. -/
def RInCube (b : RSite L) (R : Fin 4 → ℕ) (s : RSite L) : Prop :=
  ∀ k : Fin 4, ((s k - b k : Fin (L k)) : ℕ) ≤ R k

open scoped Classical in
/-- The plaquettes based in the box of forward offsets `R` at `b`. DERIVED: no numeral. -/
noncomputable def rCube (b : RSite L) (R : Fin 4 → ℕ) : Finset (RPlaq L) :=
  Finset.univ.filter (fun q => RInCube b R q.2)

open scoped Classical in
/-- DERIVED: no numeral. -/
theorem mem_rCube {b : RSite L} {R : Fin 4 → ℕ} {q : RPlaq L} :
    q ∈ rCube b R ↔ RInCube b R q.2 := by
  unfold rCube; simp

/-- DERIVED: `0` the offset of the base. -/
theorem mem_rCube_base (b : RSite L) (R : Fin 4 → ℕ) (c d : Fin 4) : ((c, d), b) ∈ rCube b R :=
  mem_rCube.mpr (fun k => by simp)

/-- **Plaquettes at one site are touch-connected** inside any `V` holding every plaquette at that site.
DERIVED: no numeral. -/
theorem rreach_same_site {V : Finset (RPlaq L)} (s : RSite L) (hV : ∀ a b : Fin 4, ((a, b), s) ∈ V)
    (a b c d : Fin 4) : Reach (rbd L) V ((a, b), s) ((c, d), s) := by
  have h1 : Touch (rbd L) ((a, b), s) ((a, c), s) :=
    ⟨(a, s), rhead_mem ((a, b), s), rhead_mem ((a, c), s)⟩
  have h2 : Touch (rbd L) ((a, c), s) ((c, d), s) :=
    ⟨(c, s), rlast_mem ((a, c), s), rhead_mem ((c, d), s)⟩
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single ⟨hV a b, hV a c, h1⟩)
    (Relation.ReflTransGen.single ⟨hV a c, hV c d, h2⟩)

/-- The summed forward offset of `s` from `b`. DERIVED: no numeral. -/
def rDepth (b s : RSite L) : ℕ := ∑ k : Fin 4, ((s k - b k : Fin (L k)) : ℕ)

/-- **Every plaquette of `rCube b R` is reachable from `((e, e), b)` inside it**, by induction on the
summed offset: one step back along an axis of positive offset stays in the box, and the diagonal
plaquette there shares a link with the diagonal plaquette at the original site. DERIVED: `1` the
step. -/
theorem rreach_from_base (b : RSite L) (R : Fin 4 → ℕ) (e : Fin 4) :
    ∀ D : ℕ, ∀ q : RPlaq L, q ∈ rCube b R → rDepth b q.2 = D →
      Reach (rbd L) (rCube b R) ((e, e), b) q := by
  intro D
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨⟨c, d⟩, s⟩ := q
    have hd' : ∑ k : Fin 4, ((s k - b k : Fin (L k)) : ℕ) = 0 := hd
    have hs : s = b := by
      funext k
      have hk : ((s k - b k : Fin (L k)) : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff.mp hd') k (Finset.mem_univ k)
      have h0 : s k - b k = 0 := Fin.ext (hk.trans (Fin.val_zero (L k)).symm)
      exact sub_eq_zero.mp h0
    rw [hs]
    exact rreach_same_site b (fun a' b' => mem_rCube_base b R a' b') e e c d
  | succ D ih =>
    intro q hq hd
    obtain ⟨⟨c, d⟩, s⟩ := q
    have hin : RInCube b R s := mem_rCube.mp hq
    have hd' : ∑ k : Fin 4, ((s k - b k : Fin (L k)) : ℕ) = D + 1 := hd
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, 0 < ((s i - b i : Fin (L i)) : ℕ) := by
      by_contra hcon
      push Not at hcon
      have h0 : ∑ k : Fin 4, ((s k - b k : Fin (L k)) : ℕ) = 0 :=
        Finset.sum_eq_zero (fun k _ => by have := hcon k; omega)
      omega
    obtain ⟨s', hs'⟩ : ∃ s' : RSite L, s' = runshift i s := ⟨_, rfl⟩
    have hkey : ((s' i - b i : Fin (L i)) : ℕ) + 1 = ((s i - b i : Fin (L i)) : ℕ) := by
      have e1 : s' i - b i + 1 = s i - b i := by
        rw [hs']
        unfold runshift
        rw [Function.update_self, sub_right_comm, sub_add_cancel]
      rcases StrongCoupling.val_add_one_cases (s' i - b i) with h | ⟨h, _⟩
      · rw [e1] at h; omega
      · rw [e1] at h; omega
    have hj : ∀ k : Fin 4, k ≠ i → s' k = s k := fun k hne => by
      rw [hs']
      exact Function.update_of_ne hne _ _
    have hin' : RInCube b R s' := fun k => by
      by_cases hki : k = i
      · subst hki
        have := hin k
        omega
      · rw [hj k hki]
        exact hin k
    have hdepth : rDepth b s' = D := by
      show ∑ k : Fin 4, ((s' k - b k : Fin (L k)) : ℕ) = D
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hd' ⊢
      have hrest : ∑ k ∈ Finset.univ.erase i, ((s' k - b k : Fin (L k)) : ℕ)
          = ∑ k ∈ Finset.univ.erase i, ((s k - b k : Fin (L k)) : ℕ) :=
        Finset.sum_congr rfl (fun k hk' => by rw [hj k (Finset.ne_of_mem_erase hk')])
      rw [hrest]
      omega
    have hr : ((i, i), s') ∈ rCube b R := mem_rCube.mpr hin'
    have ht : ((i, i), s) ∈ rCube b R := mem_rCube.mpr hin
    have h1 := ih ((i, i), s') hr hdepth
    have hsh : rshift L i s' = s := by rw [hs']; exact rshift_runshift i s
    have htouch : Touch (rbd L) ((i, i), s') ((i, i), s) := by
      refine ⟨(i, s), ?_, rhead_mem ((i, i), s)⟩
      have h2 := rsecond_mem (L := L) ((i, i), s')
      simp only at h2
      rwa [hsh] at h2
    have h2 : Reach (rbd L) (rCube b R) ((i, i), s') ((i, i), s) :=
      Relation.ReflTransGen.single ⟨hr, ht, htouch⟩
    have h3 : Reach (rbd L) (rCube b R) ((i, i), s) ((c, d), s) :=
      rreach_same_site s (fun _ _ => mem_rCube.mpr hin) i i c d
    exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans h2 h3)

/-- **`Touch` moves the circle distance of the `τ`-coordinate from `c` by at most one.** DERIVED: `1`
the step. -/
theorem rcircDist_lipschitz (τ : Fin 4) (c : Fin (L τ)) (p q : RPlaq L) (h : Touch (rbd L) p q) :
    circDist (q.2 τ - c) ≤ circDist (p.2 τ - c) + 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := p
  obtain ⟨⟨c', e⟩, y⟩ := q
  obtain ⟨⟨ld, ls⟩, hp, hq⟩ := h
  have hP := rlink_site_coord τ a b x ld ls hp
  have hQ := rlink_site_coord τ c' e y ld ls hq
  show circDist (y τ - c) ≤ circDist (x τ - c) + 1
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · rw [← hP, ← hQ]; omega
  · have h1 : circDist (y τ - c) ≤ circDist (y τ - c + 1) + 1 := StrongCoupling.circDist_le_succ _
    have e1 : y τ - c + 1 = x τ - c := by rw [sub_add_eq_add_sub, ← hQ, hP]
    rw [e1] at h1
    exact h1
  · have h1 : circDist (x τ - c + 1) ≤ circDist (x τ - c) + 1 := StrongCoupling.circDist_succ_le _
    have e1 : x τ - c + 1 = y τ - c := by rw [sub_add_eq_add_sub, ← hP, hQ]
    rw [e1] at h1
    exact h1
  · have hxy : x τ = y τ := StrongCoupling.fin_add_one_inj (by rw [← hP, ← hQ])
    rw [hxy]; omega

/-- **Two base plaquettes whose `τ`-coordinates are more than `k` apart on the circle are more than `k`
touch-steps apart.** DERIVED: `0` the level of the first base. -/
theorem r_not_mem_ball (τ : Fin 4) (x y : RSite L) (c d e f : Fin 4) (k : ℕ)
    (hk : k < circDist (y τ - x τ)) : ((c, d), y) ∉ ball (rbd L) ((e, f), x) k := by
  intro hmem
  have hlvl := StrongCoupling.lvl_le_of_mem_ball (rbd L) ((e, f), x)
    (fun q : RPlaq L => circDist (q.2 τ - x τ))
    ((congrArg circDist (sub_self (x τ))).trans StrongCoupling.circDist_zero)
    (fun p q ht => rcircDist_lipschitz τ _ p q ht) k _ hmem
  exact absurd hlvl (not_le.mpr hk)

end Geom

/-! ## 2. Slice layers -/

section Layer

variable {L : Fin 4 → ℕ} [∀ k, NeZero (L k)] (μ : Fin 4)

/-- The offsets of a layer: `1` along `μ` (two time layers), the whole extent across. DERIVED: `1` the
second layer. -/
def layR (L : Fin 4 → ℕ) (μ : Fin 4) : Fin 4 → ℕ := fun k => if k = μ then 1 else L k

/-- The base site of the layer ending at time `t`: time `t − 1`, transverse origin. DERIVED: `1` the
step. -/
def layB (t : Fin (L μ)) : RSite L := Function.update 0 μ (t - 1)

/-- **The halo of links at time `t` along `μ` lies in the layer of `t`.** DERIVED: `1` the step. -/
theorem linkHalo_subset_layer (t : Fin (L μ)) (S : Finset (RLink L)) (hS : ∀ l ∈ S, l.2 μ = t) :
    linkHalo (rbd L) S ⊆ rCube (layB μ t) (layR L μ) := by
  intro q hq
  obtain ⟨⟨a, b⟩, s⟩ := q
  obtain ⟨⟨ld, ls⟩, hl, hlS⟩ := StrongCoupling.mem_linkHalo.mp hq
  refine mem_rCube.mpr (fun k => ?_)
  by_cases hk : k = μ
  · subst hk
    have ht : ls k = t := by have := hS _ hlS; simpa using this
    simp only [layR, if_true, layB, Function.update_self]
    rcases rlink_site_coord k a b s ld ls hl with h | h
    · have e : s k - (t - 1) = 1 := by rw [← h, ht, sub_sub_cancel]
      rw [e]
      have h1 := StrongCoupling.val_add_one_cases (0 : Fin (L k))
      simp only [zero_add, Fin.val_zero] at h1
      omega
    · have e : s k - (t - 1) = 0 := by rw [← ht, h, add_sub_cancel_right, sub_self]
      rw [e]; simp
  · simp only [layR, hk, if_false]
    exact (Fin.isLt _).le

open scoped Classical in
/-- **A layer has at most `2 · 16 · |TT|` plaquettes**, `|TT|` the transverse sites: a plaquette is
fixed by its plane, its time offset (`0` or `1`) and its transverse site. DERIVED: `2` the two time
layers; `16 = 4 · 4` the planes. -/
theorem card_layer_le (t : Fin (L μ)) :
    (rCube (layB μ t) (layR L μ)).card ≤ 16 * 2 * Fintype.card (TT μ (tr L μ)) := by
  classical
  let F : RPlaq L → (Fin 4 × Fin 4) × ℕ × TT μ (tr L μ) := fun q =>
    (q.1, ((q.2 μ - layB μ t μ : Fin (L μ)) : ℕ), fun k => q.2 k.1)
  have hmaps : ∀ q ∈ rCube (layB μ t) (layR L μ),
      F q ∈ (Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ Finset.range 2 ×ˢ
        (Finset.univ : Finset (TT μ (tr L μ))) := by
    intro q hq
    have hin := (mem_rCube.mp hq) μ
    simp only [layR, if_true] at hin
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, and_true, F]
    omega
  have hinj : Set.InjOn F (rCube (layB μ t) (layR L μ) : Set (RPlaq L)) := by
    intro q _ q' _ h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine Prod.ext h1 (funext fun k => ?_)
    by_cases hk : k = μ
    · subst hk
      exact sub_left_inj.mp (Fin.ext h2)
    · exact congrFun h3 ⟨k, hk⟩
  have hle := Finset.card_le_card_of_injOn F hmaps hinj
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Finset.card_range] at hle
  linarith

end Layer

/-! ## 3. The cluster bound for two slices of a rectangular torus -/

section Cluster

variable {N : ℕ}

/-- The rectangular pullback is continuous. DERIVED: `0` the extent bound. -/
theorem continuous_rpull (L : Fin 4 → ℕ) :
    Continuous (fun U : RLink L → SUN.SU N =>
      (RectTorusState.rpull L U : GibbsSpec.IConf (SUN.SU N))) := by
  refine continuous_pi fun l => ?_
  by_cases h : ∀ k, 0 < L k
  · simp only [RectTorusState.rpull, dif_pos h]; exact continuous_apply _
  · simp only [RectTorusState.rpull, dif_neg h]; exact continuous_const

open scoped Classical in
/-- The spatial links of the torus at time `t` along `μ`. DERIVED: no numeral. -/
noncomputable def sliceLinks (L : Fin 4 → ℕ) (μ : Fin 4) (t : Fin (L μ)) : Finset (RLink L) :=
  Finset.univ.filter (fun l => l.1 ≠ μ ∧ l.2 μ = t)

/-- A slice function read at time `s` of the torus. DERIVED: no numeral. -/
def sliceObs (L : Fin 4 → ℕ) (μ : Fin 4) (s : ℕ) (u : C(RectTorusState.SlR μ (tr L μ) N, ℝ)) :
    (RLink L → SUN.SU N) → ℝ :=
  fun W => u (FluxDuality.readSlice μ (tr L μ) (s : ℤ) (RectTorusState.rpull L W))

/-- **A slice function read at time `s` is local on the links of that slice.** DERIVED: no numeral. -/
theorem localOnLinks_sliceObs (L : Fin 4 → ℕ) (hpos : ∀ k, 0 < L k) (μ : Fin 4) {s : ℕ}
    (hs : s < L μ) (u : C(RectTorusState.SlR μ (tr L μ) N, ℝ)) :
    StrongCoupling.LocalOnLinks (Nc := N) (sliceLinks L μ ⟨s, hs⟩) (sliceObs L μ s u) := by
  classical
  refine StrongCoupling.localOnLinks_of_continuous
    (u.continuous.comp ((FluxDuality.readSlice μ (tr L μ) (s : ℤ)).continuous.comp
      (continuous_rpull L))) (fun U V hUV => ?_)
  show u _ = u _
  congr 1
  funext l
  show RectTorusState.rpull L U (l.1.1, FluxDuality.siteOf μ (s : ℤ) l.2)
    = RectTorusState.rpull L V (l.1.1, FluxDuality.siteOf μ (s : ℤ) l.2)
  simp only [RectTorusState.rpull, dif_pos hpos]
  refine hUV _ ?_
  simp only [sliceLinks, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨l.1.2, ?_⟩
  show RectTorusState.rmod (L μ) (hpos μ) (FluxDuality.siteOf μ (s : ℤ) l.2 μ) = ⟨s, hs⟩
  rw [FluxDuality.siteOf_self]
  exact RectTorusState.rmod_natCast (hpos μ) hs

/-- A slice function read on the torus is bounded by its sup norm. DERIVED: no numeral. -/
theorem abs_sliceObs_le (L : Fin 4 → ℕ) (μ : Fin 4) (s : ℕ)
    (u : C(RectTorusState.SlR μ (tr L μ) N, ℝ)) (W : RLink L → SUN.SU N) :
    |sliceObs L μ s u W| ≤ ‖u‖ := by
  have h := u.norm_coe_le_norm (FluxDuality.readSlice μ (tr L μ) (s : ℤ) (RectTorusState.rpull L W))
  rw [Real.norm_eq_abs] at h
  exact h

/-- The rectangular state's connected correlation of two slices is the carrier's. DERIVED: `1` the
second slice's offset. -/
theorem rect_conn_eq (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) (μ : Fin 4) (j : ℕ)
    (u : C(RectTorusState.SlR μ (tr L μ) N, ℝ)) :
    RectTorusState.rectState hN L β
        (RectTorusState.pairObsR μ (tr L μ) (j + 1)
          (u.comp ContinuousMap.fst * u.comp ContinuousMap.snd))
      - RectTorusState.rectState hN L β
          (RectTorusState.pairObsR μ (tr L μ) (j + 1) (u.comp ContinuousMap.fst))
        * RectTorusState.rectState hN L β
            (RectTorusState.pairObsR μ (tr L μ) (j + 1) (u.comp ContinuousMap.snd))
      = StrongCoupling.wilsonCorrConnObs (Nc := N) (rbd L) (sliceObs L μ 0 u)
          (sliceObs L μ (j + 1) u) β :=
  rfl

/-- **The cluster bound for two slices of a rectangular torus.** On the torus with time extent
`2j + 2` along `μ` and any positive transverse extents, at `0 ≤ β` with `coreRate 64 β < 1` and
`64 |TT| ≤ j + 2`, the two-slice connected correlation of a continuous slice function `u` satisfies

    |E[u(V₀) u(V_{j+1})] − E[u(V₀)] E[u(V_{j+1})]|  ≤  coreConstG (2 ‖u‖²) 64 β U · coreRate 64 β ^ (j + 2 − U),

`U = 64 |TT|`, read through `RectTorusState.rectState_pairObs` as `pairExp` of `a = kT^{∗(j+1)}`. The
anchors are the two two-layer slabs around the slices (`linkHalo_subset_layer`, `rreach_from_base`,
`card_layer_le`), more than `j` touch-steps apart on the time circle (`r_not_mem_ball`).

DERIVED: `16 * 4` the touch degree (`touchDeg_rbd_le`); `64 = 2 · 32` two slabs of at most `2 · 16 |TT|`
plaquettes; `2` in `2 ‖u‖²` the two products of the pair term; `j + 2` the base plaquettes; `j + 1` the
half extent. -/
theorem rect_pair_cluster {L : Fin 4 → ℕ} [∀ k, NeZero (L k)] (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1) (μ : Fin 4) (j : ℕ) (hL : L μ = j + 1 + j + 1)
    (u : C(RectTorusState.SlR μ (tr L μ) N, ℝ))
    (hU : 64 * Fintype.card (TT μ (tr L μ)) ≤ j + 2) :
    |FluxDuality.pairExp (hS μ (tr L μ) N) (iter (hS μ (tr L μ) N) (kT μ (tr L μ) N β) j)
          (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp (hS μ (tr L μ) N) (iter (hS μ (tr L μ) N) (kT μ (tr L μ) N β) j)
            (fun p => u p.1)
          * FluxDuality.pairExp (hS μ (tr L μ) N) (iter (hS μ (tr L μ) N) (kT μ (tr L μ) N β) j)
            (fun p => u p.2)|
      ≤ StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β (64 * Fintype.card (TT μ (tr L μ)))
        * StrongCoupling.coreRate (16 * 4) β ^ (j + 2 - 64 * Fintype.card (TT μ (tr L μ))) := by
  classical
  have hpos : ∀ k, 0 < L k := fun k => Nat.pos_of_ne_zero (NeZero.ne (L k))
  have e1 := RectTorusState.rectState_pairObs hN hβ (μ := μ) j hL hpos
    (u.comp ContinuousMap.fst * u.comp ContinuousMap.snd)
  have e2 := RectTorusState.rectState_pairObs hN hβ (μ := μ) j hL hpos (u.comp ContinuousMap.fst)
  have e3 := RectTorusState.rectState_pairObs hN hβ (μ := μ) j hL hpos (u.comp ContinuousMap.snd)
  have f1 : ⇑(u.comp ContinuousMap.fst * u.comp ContinuousMap.snd
      : C(RectTorusState.SlR μ (tr L μ) N × RectTorusState.SlR μ (tr L μ) N, ℝ))
      = fun p => u p.1 * u p.2 := rfl
  have f2 : ⇑(u.comp ContinuousMap.fst
      : C(RectTorusState.SlR μ (tr L μ) N × RectTorusState.SlR μ (tr L μ) N, ℝ))
      = fun p => u p.1 := rfl
  have f3 : ⇑(u.comp ContinuousMap.snd
      : C(RectTorusState.SlR μ (tr L μ) N × RectTorusState.SlR μ (tr L μ) N, ℝ))
      = fun p => u p.2 := rfl
  rw [f1] at e1
  rw [f2] at e2
  rw [f3] at e3
  rw [← e1, ← e2, ← e3, rect_conn_eq hN L β μ j u]
  have hs0 : 0 < L μ := hpos μ
  have hs1 : j + 1 < L μ := by omega
  set t₀ : Fin (L μ) := ⟨0, hs0⟩ with ht₀
  set t₁ : Fin (L μ) := ⟨j + 1, hs1⟩ with ht₁
  have hab : Disjoint (sliceLinks L μ t₀) (sliceLinks L μ t₁) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [sliceLinks, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have h12 := congrArg Fin.val (h1.2.symm.trans h2.2)
    rw [ht₀, ht₁] at h12
    simp at h12
  have hAo := linkHalo_subset_layer μ t₀ (sliceLinks L μ t₀)
    (fun l hl => (Finset.mem_filter.mp hl).2.2)
  have hBo := linkHalo_subset_layer μ t₁ (sliceLinks L μ t₁)
    (fun l hl => (Finset.mem_filter.mp hl).2.2)
  have hcirc : j < circDist (layB μ t₁ μ - layB μ t₀ μ) := by
    simp only [layB, Function.update_self]
    rw [sub_sub_sub_cancel_right]
    have h0 : t₀ = 0 := Fin.ext (by simp [ht₀])
    rw [h0, sub_zero]
    unfold StrongCoupling.circDist
    simp only [ht₁]
    omega
  have hkb := r_not_mem_ball μ (layB μ t₀) (layB μ t₁) μ μ μ μ j hcirc
  have hcard : (rCube (layB μ t₀) (layR L μ) ∪ rCube (layB μ t₁) (layR L μ)).card
      ≤ 64 * Fintype.card (TT μ (tr L μ)) := by
    have h1 := card_layer_le μ t₀
    have h2 := card_layer_le μ t₁
    have h3 := Finset.card_union_le (rCube (layB μ t₀) (layR L μ)) (rCube (layB μ t₁) (layR L μ))
    omega
  have hbase := StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball hN (rbd L) hab
    (localOnLinks_sliceObs L hpos μ hs0 u) (localOnLinks_sliceObs L hpos μ hs1 u)
    (abs_sliceObs_le L μ 0 u) (abs_sliceObs_le L μ (j + 1) u) hAo hBo
    (mem_rCube_base (layB μ t₀) (layR L μ) μ μ) (mem_rCube_base (layB μ t₁) (layR L μ) μ μ)
    (fun q hq => rreach_from_base _ _ μ _ q hq rfl) (fun q hq => rreach_from_base _ _ μ _ q hq rfl)
    hβ (16 * 4) touchDeg_rbd_le hr j hkb (le_trans hcard hU)
  refine le_trans hbase ?_
  have hC : (0 : ℝ) ≤ 2 * (‖u‖ * ‖u‖) := by positivity
  have hr0 : 0 ≤ StrongCoupling.coreRate (16 * 4) β := StrongCoupling.coreRate_nonneg _ hβ
  have hCC := GeneralDecay.coreConstG_le_of_le hC hβ hr hcard
  have hpow' := StrongCoupling.pow_le_pow_of_le_one_asm hr0 hr.le
    (Nat.sub_le_sub_left hcard (j + 2))
  have hCK : (0 : ℝ) ≤ StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β
      (64 * Fintype.card (TT μ (tr L μ))) := by
    unfold StrongCoupling.coreConstG StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - StrongCoupling.coreRate (16 * 4) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)) this.le
  exact mul_le_mul hCC hpow' (pow_nonneg hr0 _) hCK

/-- The extents of the torus with transverse extents `T` and time extent `m` along `μ`.
DERIVED: no numeral. -/
def extT (μ : Fin 4) (T : {k : Fin 4 // k ≠ μ} → ℕ) (m : ℕ) : Fin 4 → ℕ :=
  fun k => if h : k = μ then m else T ⟨k, h⟩

/-- DERIVED: no numeral. -/
theorem tr_extT (μ : Fin 4) (T : {k : Fin 4 // k ≠ μ} → ℕ) (m : ℕ) : tr (extT μ T m) μ = T := by
  funext k
  simp [tr, extT, k.2]

/-- DERIVED: no numeral. -/
theorem extT_self (μ : Fin 4) (T : {k : Fin 4 // k ≠ μ} → ℕ) (m : ℕ) : extT μ T m μ = m := by
  simp [extT]

/-- **The two-slice cluster bound for the slice transfer of any positive transverse extents.**
`rect_pair_cluster` on the torus `extT μ T (2j + 2)`, read at `T` through `tr_extT`.

DERIVED: as `rect_pair_cluster`; `0` the transverse extent bound; `16 * 4` the touch degree
(`touchDeg_rbd_le`); `64 = 2 · 32` two slabs of at most `2 · 16 |TT|` plaquettes. -/
theorem slice_pair_cluster (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1) (μ : Fin 4) (T : {k : Fin 4 // k ≠ μ} → ℕ)
    (hT : ∀ k, 0 < T k) (j : ℕ) (u : C(RectTorusState.SlR μ T N, ℝ))
    (hU : 64 * Fintype.card (TT μ T) ≤ j + 2) :
    |FluxDuality.pairExp (hS μ T N) (iter (hS μ T N) (kT μ T N β) j) (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp (hS μ T N) (iter (hS μ T N) (kT μ T N β) j) (fun p => u p.1)
          * FluxDuality.pairExp (hS μ T N) (iter (hS μ T N) (kT μ T N β) j) (fun p => u p.2)|
      ≤ StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β (64 * Fintype.card (TT μ T))
        * StrongCoupling.coreRate (16 * 4) β ^ (j + 2 - 64 * Fintype.card (TT μ T)) := by
  have key : ∀ T' : {k : Fin 4 // k ≠ μ} → ℕ, tr (extT μ T (j + 1 + j + 1)) μ = T' →
      ∀ u : C(RectTorusState.SlR μ T' N, ℝ), 64 * Fintype.card (TT μ T') ≤ j + 2 →
      |FluxDuality.pairExp (hS μ T' N) (iter (hS μ T' N) (kT μ T' N β) j)
            (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp (hS μ T' N) (iter (hS μ T' N) (kT μ T' N β) j) (fun p => u p.1)
          * FluxDuality.pairExp (hS μ T' N) (iter (hS μ T' N) (kT μ T' N β) j) (fun p => u p.2)|
      ≤ StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β (64 * Fintype.card (TT μ T'))
        * StrongCoupling.coreRate (16 * 4) β ^ (j + 2 - 64 * Fintype.card (TT μ T')) := by
    intro T' e
    subst e
    haveI : ∀ k, NeZero (extT μ T (j + 1 + j + 1) k) := fun k => ⟨by
      by_cases h : k = μ
      · subst h; simp [extT]
      · simp only [extT, dif_neg h]; exact (hT ⟨k, h⟩).ne'⟩
    intro u hU
    exact rect_pair_cluster hN hβ hr μ j (extT_self μ T _) u hU
  exact key T (tr_extT μ T _) u hU

end Cluster

/-! ## 4. Kernel algebra on a probability space -/

section KernelAlgebra

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `|a b| ≤ A B` from `|a| ≤ A` and `|b| ≤ B`. DERIVED: no numeral. -/
theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- A product of bounded kernels is bounded. DERIVED: no numeral. -/
theorem bdd_mul {a b : X → X → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun x y => a x y * b x y) := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  obtain ⟨Cb, hCb⟩ := hb.bdd
  exact ⟨ha.meas.mul hb.meas, Ca * Cb, fun x y => abs_mul_le_of (hCa x y) (hCb x y)⟩

/-- A bounded function of the first variable. DERIVED: no numeral. -/
theorem bdd_left {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Bdd (fun x (_ : X) => f x) :=
  ⟨hf.comp measurable_fst, C, fun x _ => hC x⟩

/-- A bounded function of the second variable. DERIVED: no numeral. -/
theorem bdd_right {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Bdd (fun (_ : X) y => f y) :=
  ⟨hf.comp measurable_snd, C, fun _ y => hC y⟩

/-- A constant kernel. DERIVED: no numeral. -/
theorem bdd_const (a : ℝ) : Bdd (fun (_ _ : X) => a) :=
  ⟨measurable_const, |a|, fun _ _ => le_rfl⟩

/-- Iterated integrals of bounded kernels add. DERIVED: no numeral. -/
theorem iint_add {F G : X → X → ℝ} (hF : Bdd F) (hG : Bdd G) :
    ∫ x, ∫ y, (F x y + G x y) ∂μ ∂μ = (∫ x, ∫ y, F x y ∂μ ∂μ) + ∫ x, ∫ y, G x y ∂μ ∂μ := by
  obtain ⟨CF, hCF⟩ := hF.bdd
  obtain ⟨CG, hCG⟩ := hG.bdd
  have e : ∀ x, ∫ y, (F x y + G x y) ∂μ = ∫ y, F x y ∂μ + ∫ y, G x y ∂μ := fun x =>
    integral_add (integrable_of_bdd (hF.row x) (hCF x)) (integrable_of_bdd (hG.row x) (hCG x))
  simp_rw [e]
  exact integral_add
    (integrable_of_bdd (measurable_integral_right hF.meas) (fun x => abs_integral_le (hCF x)))
    (integrable_of_bdd (measurable_integral_right hG.meas) (fun x => abs_integral_le (hCG x)))

/-- **`|∫∫ a² G| ≤ S · hs(a)`** for `|G| ≤ S`. DERIVED: `2` the square. -/
theorem abs_iint_sq_mul_le {a G : X → X → ℝ} (ha : Bdd a) {S : ℝ}
    (hS : ∀ x y, |G x y| ≤ S) :
    |∫ x, ∫ y, a x y ^ 2 * G x y ∂μ ∂μ| ≤ S * hs μ a := by
  have ha2 : Bdd (fun x y => a x y ^ 2) := by
    have h := bdd_mul ha ha
    simpa [sq] using h
  obtain ⟨C2, hC2⟩ := ha2.bdd
  have hrow : ∀ x, Integrable (fun y => S * a x y ^ 2) μ := fun x =>
    (integrable_of_bdd (ha2.row x) (hC2 x)).const_mul S
  have hpt : ∀ x, |∫ y, a x y ^ 2 * G x y ∂μ| ≤ ∫ y, S * a x y ^ 2 ∂μ := by
    intro x
    have h := norm_integral_le_of_norm_le (μ := μ) (f := fun y => a x y ^ 2 * G x y) (hrow x)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hS x y) (sq_nonneg _))
    simpa [Real.norm_eq_abs] using h
  have hout : Integrable (fun x => ∫ y, S * a x y ^ 2 ∂μ) μ := by
    refine integrable_of_bdd (measurable_integral_right (measurable_const.mul ha2.meas))
      (C := |S| * C2) (fun x => abs_integral_le fun y => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC2 x y) (abs_nonneg _)
  have h := norm_integral_le_of_norm_le (μ := μ) (f := fun x => ∫ y, a x y ^ 2 * G x y ∂μ) hout
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  simp only [integral_const_mul]
  rfl

/-- **A `pairExp` read of a bounded test is bounded by the test's bound.** DERIVED: `0` the empty
denominator. -/
theorem abs_pairExp_le {a : X → X → ℝ} (ha : Bdd a) {h : X × X → ℝ} {S : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ p, |h p| ≤ S) : |FluxDuality.pairExp μ a h| ≤ S := by
  unfold FluxDuality.pairExp
  rcases (hs_nonneg (μ := μ) a).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, abs_zero]; exact hS0
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact abs_iint_sq_mul_le (G := fun x y => h (x, y)) ha (fun x y => hS (x, y))

/-- **The pair-read algebra.** If the normalized numerators of a two-point read decompose as
`p²·cc² + 2 p W + X`, `p²·cc + Z₂`, `p²·cc + Z₃` over `p² + Y`, with the corrections bounded by `Y`,
then a bound `ε` on the connected read bounds the middle term:
`|W| ≤ (ε (p² + Y) + 5 s² Y) / (2p)`. DERIVED: `2` the cross term; `5 = 2 + 1 + 1 + 1` the four
correction bounds; `4` in the intermediate bound. -/
theorem alg_w {p Y cc X Z2 Z3 W s ε Q1 Quu Qu1 Q1u : ℝ} (hp : 0 < p) (hY : 0 ≤ Y) (hs : 0 ≤ s)
    (hcc : |cc| ≤ s) (hX : |X| ≤ s * s * Y) (hZ2 : |Z2| ≤ s * Y) (hZ3 : |Z3| ≤ s * Y)
    (hQ1 : Q1 = p ^ 2 + Y) (hQuu : Quu = p ^ 2 * (cc * cc) + (2 * p * W + X))
    (hQu1 : Qu1 = p ^ 2 * cc + Z2) (hQ1u : Q1u = p ^ 2 * cc + Z3)
    (hcorr : |Quu / Q1 - Qu1 / Q1 * (Q1u / Q1)| ≤ ε) :
    |W| ≤ (ε * (p ^ 2 + Y) + 5 * (s * s) * Y) / (2 * p) := by
  have hQ : 0 < p ^ 2 + Y := by positivity
  subst hQ1 hQuu hQu1 hQ1u
  set corr := (p ^ 2 * (cc * cc) + (2 * p * W + X)) / (p ^ 2 + Y)
    - (p ^ 2 * cc + Z2) / (p ^ 2 + Y) * ((p ^ 2 * cc + Z3) / (p ^ 2 + Y)) with hcorrdef
  set num := p ^ 2 * cc * (Z2 + Z3) + Z2 * Z3 - p ^ 2 * (cc * cc) * Y with hnum
  have key : 2 * p * W = corr * (p ^ 2 + Y) + num / (p ^ 2 + Y) - X := by
    rw [hcorrdef, hnum]
    field_simp
    ring
  have h1 : |p ^ 2 * cc * (Z2 + Z3)| ≤ p ^ 2 * s * (2 * (s * Y)) := by
    refine abs_mul_le_of (abs_mul_le_of (le_of_eq (abs_of_nonneg (sq_nonneg p))) hcc) ?_
    exact (abs_add_le _ _).trans (by linarith)
  have h2 : |Z2 * Z3| ≤ (s * Y) * (s * Y) := abs_mul_le_of hZ2 hZ3
  have h3 : |p ^ 2 * (cc * cc) * Y| ≤ p ^ 2 * (s * s) * Y :=
    abs_mul_le_of (abs_mul_le_of (le_of_eq (abs_of_nonneg (sq_nonneg p))) (abs_mul_le_of hcc hcc))
      (le_of_eq (abs_of_nonneg hY))
  have hnumb : |num| ≤ 4 * (s * s) * Y * (p ^ 2 + Y) := by
    have e : |num| ≤ |p ^ 2 * cc * (Z2 + Z3)| + |Z2 * Z3| + |p ^ 2 * (cc * cc) * Y| := by
      rw [hnum]
      have := abs_sub (p ^ 2 * cc * (Z2 + Z3) + Z2 * Z3) (p ^ 2 * (cc * cc) * Y)
      have := abs_add_le (p ^ 2 * cc * (Z2 + Z3)) (Z2 * Z3)
      linarith
    have hsY : 0 ≤ s * s * Y := by positivity
    nlinarith [mul_nonneg hsY (sq_nonneg p), mul_nonneg hsY hY]
  have hdiv : |num / (p ^ 2 + Y)| ≤ 4 * (s * s) * Y := by
    rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ]; exact hnumb
  have hcorrQ : |corr * (p ^ 2 + Y)| ≤ ε * (p ^ 2 + Y) := by
    rw [abs_mul, abs_of_pos hQ]; exact mul_le_mul_of_nonneg_right hcorr hQ.le
  have h2pW : |2 * p * W| ≤ ε * (p ^ 2 + Y) + 5 * (s * s) * Y := by
    rw [key]
    have := abs_sub (corr * (p ^ 2 + Y) + num / (p ^ 2 + Y)) X
    have := abs_add_le (corr * (p ^ 2 + Y)) (num / (p ^ 2 + Y))
    linarith
  have h2p : 0 < 2 * p := by linarith
  rw [le_div_iff₀ h2p, mul_comm]
  have e : |2 * p * W| = 2 * p * |W| := by rw [abs_mul, abs_of_pos h2p]
  linarith

end KernelAlgebra

/-! ## 5. The two-slice read through the eigen-decomposition -/

section PairRead

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hk hsym hφm hφb hφ1 heig in
/-- **The two-slice numerator in the eigen-decomposition.** With `a = k^{∗(j+1)} = c^{j+1} φ⊗φ + r`,
`r = (k − c φ⊗φ)^{∗(j+1)}`,

    ∫∫ a² g₁ ⊗ g₂ = c^{2(j+1)} ⟨φ², g₁⟩ ⟨φ², g₂⟩ + 2 c^{j+1} ∫∫ (φ g₁) r (φ g₂) + ∫∫ r² g₁ ⊗ g₂.

DERIVED: `2` the square and the cross term; `j + 1` the power. -/
theorem pair_expand (j : ℕ) {g₁ g₂ : X → ℝ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    {s₁ s₂ : ℝ} (hs₁ : ∀ x, |g₁ x| ≤ s₁) (hs₂ : ∀ x, |g₂ x| ≤ s₂) :
    ∫ x, ∫ y, iter μ k j x y ^ 2 * (g₁ x * g₂ y) ∂μ ∂μ
      = (c ^ (j + 1)) ^ 2 * ((∫ x, φ x ^ 2 * g₁ x ∂μ) * ∫ y, φ y ^ 2 * g₂ y ∂μ)
        + (2 * c ^ (j + 1) * ∫ x, ∫ y, φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y) ∂μ ∂μ
          + ∫ x, ∫ y, iter μ (rem k c φ) j x y ^ 2 * (g₁ x * g₂ y) ∂μ ∂μ) := by
  have hr : Bdd (iter μ (rem k c φ) j) := (Bdd.rem hk hφm hφb (c := c)).iter j
  have hφ2 : ∀ x, |φ x ^ 2| ≤ B ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2
  have hA1 : Bdd (fun x (_ : X) => (c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x)) :=
    bdd_left (measurable_const.mul ((hφm.pow_const 2).mul hg₁))
      (fun x => abs_mul_le_of le_rfl (abs_mul_le_of (hφ2 x) (hs₁ x)))
  have hA2 : Bdd (fun (_ : X) y => φ y ^ 2 * g₂ y) :=
    bdd_right ((hφm.pow_const 2).mul hg₂) (fun y => abs_mul_le_of (hφ2 y) (hs₂ y))
  have hA : Bdd (fun x y => (c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x) * (φ y ^ 2 * g₂ y)) :=
    bdd_mul hA1 hA2
  have hM : Bdd (fun x y => φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y)) :=
    bdd_mul (bdd_mul (bdd_mul (bdd_left hφm hφb) (bdd_left hg₁ hs₁)) hr)
      (bdd_mul (bdd_right hφm hφb) (bdd_right hg₂ hs₂))
  have hB : Bdd (fun x y => 2 * c ^ (j + 1) * (φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y))) :=
    bdd_mul (bdd_const _) hM
  have hC : Bdd (fun x y => iter μ (rem k c φ) j x y ^ 2 * (g₁ x * g₂ y)) := by
    have h := bdd_mul (bdd_mul hr hr) (bdd_mul (bdd_left hg₁ hs₁) (bdd_right hg₂ hs₂))
    simpa [sq] using h
  have eA : ∫ x, ∫ y, (c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x) * (φ y ^ 2 * g₂ y) ∂μ ∂μ
      = (c ^ (j + 1)) ^ 2 * ((∫ x, φ x ^ 2 * g₁ x ∂μ) * ∫ y, φ y ^ 2 * g₂ y ∂μ) := by
    have e : ∀ x, ∫ y, (c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x) * (φ y ^ 2 * g₂ y) ∂μ
        = (c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x) * ∫ y, φ y ^ 2 * g₂ y ∂μ := fun x =>
      integral_const_mul _ _
    simp_rw [e]
    rw [integral_mul_const, integral_const_mul]
    ring
  have eB : ∫ x, ∫ y, 2 * c ^ (j + 1) * (φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y)) ∂μ ∂μ
      = 2 * c ^ (j + 1) * ∫ x, ∫ y, φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y) ∂μ ∂μ := by
    simp only [integral_const_mul]
  calc ∫ x, ∫ y, iter μ k j x y ^ 2 * (g₁ x * g₂ y) ∂μ ∂μ
      = ∫ x, ∫ y, ((c ^ (j + 1)) ^ 2 * (φ x ^ 2 * g₁ x) * (φ y ^ 2 * g₂ y)
          + (2 * c ^ (j + 1) * (φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * g₂ y))
            + iter μ (rem k c φ) j x y ^ 2 * (g₁ x * g₂ y))) ∂μ ∂μ := by
        congr 1; funext x; congr 1; funext y
        rw [iter_decomp hk hsym hφm hφb hφ1 heig j x y]; ring
    _ = _ := by
        rw [iint_add hA (hB.add hC), iint_add hB hC, eA, eB]

include hk hφm hφb hφ1 heig in
/-- The cross term vanishes against the constant on the right: the remainder rows are orthogonal to
`φ`. DERIVED: `1` the constant test. -/
theorem mid_right_zero (j : ℕ) (g₁ : X → ℝ) :
    ∫ x, ∫ y, φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * 1) ∂μ ∂μ = 0 := by
  have e : ∀ x, ∫ y, φ x * g₁ x * iter μ (rem k c φ) j x y * (φ y * 1) ∂μ
      = (φ x * g₁ x) * ∫ y, iter μ (rem k c φ) j x y * φ y ∂μ := by
    intro x; rw [← integral_const_mul]; congr 1; funext y; ring
  simp_rw [e, iter_rem_row_orth hk hφm hφb hφ1 heig j, mul_zero, integral_zero]

include hk hsym hφm hφb hφ1 heig in
/-- The cross term vanishes against the constant on the left: the remainder columns are orthogonal
to `φ`. DERIVED: `1` the constant test. -/
theorem mid_left_zero (j : ℕ) {g₂ : X → ℝ} (hg₂ : Measurable g₂) {s₂ : ℝ}
    (hs₂ : ∀ x, |g₂ x| ≤ s₂) :
    ∫ x, ∫ y, φ x * 1 * iter μ (rem k c φ) j x y * (φ y * g₂ y) ∂μ ∂μ = 0 := by
  have hr : Bdd (iter μ (rem k c φ) j) := (Bdd.rem hk hφm hφb (c := c)).iter j
  have hM : Bdd (fun x y => φ x * 1 * iter μ (rem k c φ) j x y * (φ y * g₂ y)) :=
    bdd_mul (bdd_mul (bdd_mul (bdd_left hφm hφb) (bdd_const 1)) hr)
      (bdd_mul (bdd_right hφm hφb) (bdd_right hg₂ hs₂))
  obtain ⟨CM, hCM⟩ := hM.bdd
  rw [swap_bdd hM.meas hCM]
  have e : ∀ y, ∫ x, φ x * 1 * iter μ (rem k c φ) j x y * (φ y * g₂ y) ∂μ
      = (∫ x, φ x * iter μ (rem k c φ) j x y ∂μ) * (φ y * g₂ y) := by
    intro y; rw [← integral_mul_const]; congr 1; funext x; ring
  simp_rw [e, iter_rem_col_orth hk hsym hφm hφb hφ1 heig j, zero_mul, integral_zero]

include hφm hφb hφ1 in
/-- `|⟨φ², u⟩| ≤ s` for `|u| ≤ s`. DERIVED: `2` the square. -/
theorem abs_int_phi_sq_le {u : X → ℝ} {s : ℝ} (hus : ∀ x, |u x| ≤ s) :
    |∫ x, φ x ^ 2 * u x ∂μ| ≤ s := by
  have hφ2 : ∀ x, |φ x ^ 2| ≤ B ^ 2 := fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb x) 2
  have hint : Integrable (fun x => s * φ x ^ 2) μ :=
    (integrable_of_bdd (hφm.pow_const 2) hφ2).const_mul s
  have h := norm_integral_le_of_norm_le (μ := μ) (f := fun x => φ x ^ 2 * u x) hint
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hus x) (sq_nonneg _))
  rw [Real.norm_eq_abs, integral_const_mul, hφ1, mul_one] at h
  exact h

include hk hsym hφm hφb hφ1 heig in
/-- **A bound on the connected two-slice read bounds the remainder's form.** For `|u| ≤ s` and
`|E[u ⊗ u] − E[u ⊗ 1] E[1 ⊗ u]| ≤ ε` in the read `pairExp (k^{∗(j+1)})`,

    |∫∫ (φ u) r (φ u)|  ≤  (ε (c^{2(j+1)} + hs r) + 5 s² hs r) / (2 c^{j+1}),

`r = (k − c φ⊗φ)^{∗(j+1)}` (`pair_expand`, `mid_right_zero`, `mid_left_zero`,
`KernelPower.hs_iter_decomp`, `alg_w`). DERIVED: `2`, `5` as in `alg_w`. -/
theorem w_bound (hc : 0 < c) (j : ℕ) {u : X → ℝ} (hum : Measurable u) {s : ℝ} (hs0 : 0 ≤ s)
    (hus : ∀ x, |u x| ≤ s) {ε : ℝ}
    (hcorr : |FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
          * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2)| ≤ ε) :
    |∫ x, ∫ y, φ x * u x * iter μ (rem k c φ) j x y * (φ y * u y) ∂μ ∂μ|
      ≤ (ε * ((c ^ (j + 1)) ^ 2 + hs μ (iter μ (rem k c φ) j))
          + 5 * (s * s) * hs μ (iter μ (rem k c φ) j)) / (2 * c ^ (j + 1)) := by
  have hr : Bdd (iter μ (rem k c φ) j) := (Bdd.rem hk hφm hφb (c := c)).iter j
  have h1m : Measurable (fun _ : X => (1 : ℝ)) := measurable_const
  have h1b : ∀ x : X, |(fun _ : X => (1 : ℝ)) x| ≤ 1 := fun _ => by simp
  have Euu := pair_expand hk hsym hφm hφb hφ1 heig j hum hum hus hus
  have Eu1 := pair_expand hk hsym hφm hφb hφ1 heig j hum h1m hus h1b
  have E1u := pair_expand hk hsym hφm hφb hφ1 heig j h1m hum h1b hus
  rw [mid_right_zero hk hφm hφb hφ1 heig j u] at Eu1
  rw [mid_left_zero hk hsym hφm hφb hφ1 heig j hum hus] at E1u
  have hφ1' : ∫ y, φ y ^ 2 * (fun _ : X => (1 : ℝ)) y ∂μ = 1 := by simpa using hφ1
  rw [hφ1'] at Eu1 E1u
  simp only [mul_one, one_mul, mul_zero, zero_add] at Eu1 E1u
  have hden := hs_iter_decomp hk hsym hφm hφb hφ1 heig j
  have hQ1 : hs μ (iter μ k j) = (c ^ (j + 1)) ^ 2 + hs μ (iter μ (rem k c φ) j) := by
    rw [hden, ← pow_mul, mul_comm]
  unfold FluxDuality.pairExp at hcorr
  have hX := abs_iint_sq_mul_le (μ := μ) (G := fun x y => u x * u y) hr
    (fun x y => abs_mul_le_of (hus x) (hus y))
  have hZ2 := abs_iint_sq_mul_le (μ := μ) (G := fun x (_ : X) => u x) hr (fun x _ => hus x)
  have hZ3 := abs_iint_sq_mul_le (μ := μ) (G := fun (_ : X) y => u y) hr (fun _ y => hus y)
  exact alg_w (pow_pos hc (j + 1)) (hs_nonneg _) hs0 (abs_int_phi_sq_le hφm hφb hφ1 hus) hX hZ2 hZ3
    hQ1 Euu Eu1 E1u hcorr

end PairRead

/-! ## 6. Operator powers of a kernel -/

section OperatorPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The `(j+1)`-th power of a kernel operator acts by the iterated kernel.** DERIVED: `1` the first
power. -/
theorem pow_apply_ae {r : X → X → ℝ} (hr : Bdd r) {C : ℝ} (hm : Measurable (Function.uncurry r))
    (hC0 : 0 ≤ C) (hb : ∀ x y, |r x y| ≤ C) (f : Lp ℝ 2 μ) :
    ∀ j : ℕ, (((kernelCLM r C hm hC0 hb μ μ) ^ (j + 1)) f : X → ℝ)
      =ᵐ[μ] fun x => ∫ y, iter μ r j x y * (f : X → ℝ) y ∂μ
  | 0 => by
    rw [zero_add, pow_one]
    exact coeFn_kernelCLM r C hm hC0 hb μ μ f
  | j + 1 => by
    have IH := pow_apply_ae hr hm hC0 hb f j
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [coeFn_kernelCLM r C hm hC0 hb μ μ
      (((kernelCLM r C hm hC0 hb μ μ) ^ (j + 1)) f)] with x hx
    rw [hx, kernelFun_congr IH x]
    unfold kernelFun
    have hfint : Integrable (f : X → ℝ) μ := (Lp.memLp f).integrable one_le_two
    obtain ⟨Cr, hCr⟩ := hr.bdd
    obtain ⟨Cj, hCj⟩ := (hr.iter (μ := μ) j).bdd
    have hint : Integrable (Function.uncurry fun y z => r x y * iter μ r j y z * (f : X → ℝ) z)
        (μ.prod μ) :=
      (hfint.comp_snd μ).bdd_mul (c := Cr * Cj)
        ((((hr.row x).comp measurable_fst).mul (hr.iter (μ := μ) j).meas).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact abs_mul_le_of (hCr x p.1) (hCj p.1 p.2))
    calc ∫ y, r x y * ∫ z, iter μ r j y z * (f : X → ℝ) z ∂μ ∂μ
        = ∫ y, ∫ z, r x y * iter μ r j y z * (f : X → ℝ) z ∂μ ∂μ := by
          congr 1; funext y; rw [← integral_const_mul]; congr 1; funext z; ring
      _ = ∫ z, ∫ y, r x y * iter μ r j y z * (f : X → ℝ) z ∂μ ∂μ := integral_integral_swap hint
      _ = ∫ z, iter μ r (j + 1) x z * (f : X → ℝ) z ∂μ := by
          congr 1; funext z; rw [integral_mul_const]; rfl

/-- **The form of a kernel power on a vector represented by `w`.** DERIVED: `1` the first power. -/
theorem inner_pow_eq {r : X → X → ℝ} (hr : Bdd r) {C : ℝ} (hm : Measurable (Function.uncurry r))
    (hC0 : 0 ≤ C) (hb : ∀ x y, |r x y| ≤ C) (f : Lp ℝ 2 μ) {w : X → ℝ}
    (hfw : (f : X → ℝ) =ᵐ[μ] w) (j : ℕ) :
    inner ℝ f (((kernelCLM r C hm hC0 hb μ μ) ^ (j + 1)) f)
      = ∫ x, w x * ∫ y, iter μ r j x y * w y ∂μ ∂μ := by
  rw [SlabTransferAdjoint.real_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [hfw, pow_apply_ae hr hm hC0 hb f j] with x hx hy
  rw [hx, hy]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfw] with y hy'
  rw [hy']

end OperatorPower

/-! ## 7. A first gap from the floor of the kernel -/

section Floor

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- `hs(h) ≤ M²` for `|h| ≤ M`. DERIVED: `2` the square. -/
theorem hs_le_sq {h : X → X → ℝ} (hh : Bdd h) {M : ℝ} (hM : ∀ x y, |h x y| ≤ M) :
    hs μ h ≤ M ^ 2 := by
  have h2 : Bdd (fun x y => h x y ^ 2) := by
    have := bdd_mul hh hh
    simpa [sq] using this
  obtain ⟨C2, hC2⟩ := h2.bdd
  have hpt : ∀ x y, h x y ^ 2 ≤ M ^ 2 := fun x y => by
    have h1 := hM x y
    have h0 := abs_nonneg (h x y)
    rw [← sq_abs]
    exact pow_le_pow_left₀ h0 h1 2
  unfold hs
  calc ∫ x, ∫ y, h x y ^ 2 ∂μ ∂μ ≤ ∫ _x, ∫ _y, M ^ 2 ∂μ ∂μ := by
        refine integral_mono
          (integrable_of_bdd (measurable_integral_right h2.meas) (fun x => abs_integral_le (hC2 x)))
          (integrable_const _) (fun x => ?_)
        exact integral_mono (integrable_of_bdd (h2.row x) (hC2 x)) (integrable_const _)
          (fun y => hpt x y)
    _ = M ^ 2 := by simp

variable {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hk hsym hφm hφb hφ1 heig in
/-- **A floor on the kernel gives a first decay of the remainder.** For a kernel with values in
`[a, 1]`, `a > 0`, and a unit eigenfunction `φ ≥ c₀ > 0` with eigenvalue `c > 0`, there are
`0 ≤ q₀ < 1` and `C ≥ 0` with `hs((k − c φ⊗φ)^{∗(j+1)}) ≤ C (c q₀)^{2(j+1)}` at every `j`.

`k'' = k − (a/B²) φ⊗φ` is nonnegative with `k'' φ = d φ`, `d = c − a/B²`; its iterates lie in
`[0, dʲ φ(x)/c₀]` by positivity alone, and `k''^{∗(j+1)} − d^{j+1} φ⊗φ` is the remainder of `k`
(`KernelPower.iter_decomp` for `k''`). `q₀ = max (d/c) (1/2)`.

DERIVED: `2` the square in `B²` and in `hs`; `1/2` keeps `q₀` positive; `1` the ceiling of `k`. -/
theorem floor_decay {a c₀ : ℝ} (ha : 0 < a) (hlo : ∀ x y, a ≤ k x y) (hhi : ∀ x y, k x y ≤ 1)
    (hc₀ : 0 < c₀) (hφlow : ∀ x, c₀ ≤ φ x) (hc : 0 < c) :
    ∃ q₀ : ℝ, 0 ≤ q₀ ∧ q₀ < 1 ∧ ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH * (c * q₀) ^ (2 * (j + 1)) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hφ0 : ∀ x, 0 < φ x := fun x => hc₀.trans_le (hφlow x)
  have hB : 0 < B := (hφ0 x₀).trans_le ((le_abs_self _).trans (hφb x₀))
  have hφB : ∀ x, φ x ≤ B := fun x => (le_abs_self _).trans (hφb x)
  set e := a / B ^ 2 with he
  have he0 : 0 < e := by positivity
  set d := c - e with hd
  have hk'' : Bdd (rem k e φ) := Bdd.rem hk hφm hφb
  have hsym'' : ∀ x y, rem k e φ x y = rem k e φ y x := fun x y => by
    unfold MassGap.KernelPower.rem; rw [hsym x y]; ring
  have hφφ : ∀ x y, e * φ x * φ y ≤ a := fun x y => by
    have h1 : φ x * φ y ≤ B * B :=
      mul_le_mul (hφB x) (hφB y) (hφ0 y).le hB.le
    calc e * φ x * φ y = e * (φ x * φ y) := by ring
      _ ≤ e * (B * B) := mul_le_mul_of_nonneg_left h1 he0.le
      _ = a := by rw [he]; field_simp
  have hk''0 : ∀ x y, 0 ≤ rem k e φ x y := fun x y => by
    unfold MassGap.KernelPower.rem; linarith [hφφ x y, hlo x y]
  have hk''1 : ∀ x y, rem k e φ x y ≤ 1 := fun x y => by
    unfold MassGap.KernelPower.rem
    have : 0 ≤ e * φ x * φ y := by have := hφ0 x; have := hφ0 y; positivity
    linarith [hhi x y]
  have hφ2i : Integrable (fun y => φ y ^ 2) μ := integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2)
    (fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb y) 2)
  have heig'' : ∀ z, ∫ y, rem k e φ z y * φ y ∂μ = d * φ z := by
    intro z
    obtain ⟨Ck, hCk⟩ := hk.bdd
    unfold MassGap.KernelPower.rem
    have ef : (fun y => (k z y - e * φ z * φ y) * φ y) = fun y => k z y * φ y - (e * φ z) * φ y ^ 2 := by
      funext y; ring
    rw [ef, integral_sub (integrable_mul_of_bdd (hk.row z) hφm (hCk z) hφb) (hφ2i.const_mul _),
      integral_const_mul, hφ1, heig z, hd]
    ring
  have hd0 : 0 ≤ d := by
    have h := heig'' x₀
    have hnn : 0 ≤ ∫ y, rem k e φ x₀ y * φ y ∂μ :=
      integral_nonneg fun y => mul_nonneg (hk''0 x₀ y) (hφ0 y).le
    rw [h] at hnn
    exact nonneg_of_mul_nonneg_left hnn (hφ0 x₀)
  have hiter : ∀ j x y, 0 ≤ iter μ (rem k e φ) j x y ∧
      iter μ (rem k e φ) j x y ≤ d ^ j * (φ x / c₀) := by
    intro j
    induction j with
    | zero =>
      intro x y
      refine ⟨hk''0 x y, ?_⟩
      have : 1 ≤ φ x / c₀ := by rw [le_div_iff₀ hc₀, one_mul]; exact hφlow x
      simp only [iter, pow_zero, one_mul]
      linarith [hk''1 x y]
    | succ j ih =>
      intro x y
      have hrj := hk''.iter (μ := μ) j
      obtain ⟨Cj, hCj⟩ := hrj.bdd
      obtain ⟨C'', hC''⟩ := hk''.bdd
      change 0 ≤ ∫ z, rem k e φ x z * iter μ (rem k e φ) j z y ∂μ ∧
        ∫ z, rem k e φ x z * iter μ (rem k e φ) j z y ∂μ ≤ d ^ (j + 1) * (φ x / c₀)
      refine ⟨integral_nonneg fun z => mul_nonneg (hk''0 x z) (ih z y).1, ?_⟩
      have hi1 : Integrable (fun z => rem k e φ x z * iter μ (rem k e φ) j z y) μ :=
        integrable_mul_of_bdd (hk''.row x) (hrj.col y) (hC'' x) (fun z => hCj z y)
      have hi2 : Integrable (fun z => rem k e φ x z * (d ^ j / c₀ * φ z)) μ :=
        integrable_mul_of_bdd (hk''.row x) (measurable_const.mul hφm) (hC'' x)
          (fun z => abs_mul_le_of le_rfl (hφb z))
      calc ∫ z, rem k e φ x z * iter μ (rem k e φ) j z y ∂μ
          ≤ ∫ z, rem k e φ x z * (d ^ j / c₀ * φ z) ∂μ := by
            refine integral_mono hi1 hi2 (fun z => mul_le_mul_of_nonneg_left ?_ (hk''0 x z))
            have := (ih z y).2
            calc iter μ (rem k e φ) j z y ≤ d ^ j * (φ z / c₀) := this
              _ = d ^ j / c₀ * φ z := by ring
        _ = d ^ j / c₀ * ∫ z, rem k e φ x z * φ z ∂μ := by
            rw [← integral_const_mul]; congr 1; funext z; ring
        _ = d ^ (j + 1) * (φ x / c₀) := by rw [heig'' x]; ring
  have hremeq : rem (rem k e φ) d φ = rem k c φ := by
    funext x y; unfold MassGap.KernelPower.rem; rw [hd]; ring
  set q₀ := max (d / c) (1 / 2) with hq₀
  have hq0 : 0 ≤ q₀ := le_max_of_le_right (by norm_num)
  have hdc : d / c < 1 := by rw [div_lt_one hc, hd]; linarith
  have hq1 : q₀ < 1 := max_lt hdc (by norm_num)
  have hcq : 0 < c * q₀ := mul_pos hc (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hdle : d ≤ c * q₀ := by
    have : d = c * (d / c) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le
  have hcq1 : c * q₀ ≤ c := by
    have := mul_le_mul_of_nonneg_left hq1.le hc.le; linarith
  set M₀ := B / c₀ + c * B ^ 2 with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hbound : ∀ j x y, |iter μ (rem k c φ) j x y| ≤ (c * q₀) ^ j * M₀ := by
    intro j x y
    have hdec := iter_decomp (μ := μ) hk'' hsym'' hφm hφb hφ1 heig'' j x y
    rw [hremeq] at hdec
    have h1 := (hiter j x y).1
    have h2 := (hiter j x y).2
    have hdj : d ^ j ≤ (c * q₀) ^ j := pow_le_pow_left₀ hd0 hdle j
    have hφx : φ x / c₀ ≤ B / c₀ := div_le_div_of_nonneg_right (hφB x) hc₀.le
    have hpp : |d ^ (j + 1) * φ x * φ y| ≤ (c * q₀) ^ j * (c * B ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hd0 _)]
      have hφxy : |φ x| * |φ y| ≤ B ^ 2 := by
        rw [sq]; exact mul_le_mul (hφb x) (hφb y) (abs_nonneg _) hB.le
      calc d ^ (j + 1) * |φ x| * |φ y| = d ^ j * d * (|φ x| * |φ y|) := by ring
        _ ≤ (c * q₀) ^ j * c * B ^ 2 := by
            refine mul_le_mul (mul_le_mul hdj (hdle.trans hcq1) hd0 (pow_nonneg hcq.le _)) hφxy
              (by positivity) (by positivity)
        _ = (c * q₀) ^ j * (c * B ^ 2) := by ring
    have heq : iter μ (rem k c φ) j x y = iter μ (rem k e φ) j x y - d ^ (j + 1) * φ x * φ y := by
      linarith
    rw [heq]
    calc |iter μ (rem k e φ) j x y - d ^ (j + 1) * φ x * φ y|
        ≤ |iter μ (rem k e φ) j x y| + |d ^ (j + 1) * φ x * φ y| := abs_sub _ _
      _ ≤ (c * q₀) ^ j * (B / c₀) + (c * q₀) ^ j * (c * B ^ 2) := by
          refine add_le_add ?_ hpp
          rw [abs_of_nonneg h1]
          calc iter μ (rem k e φ) j x y ≤ d ^ j * (φ x / c₀) := h2
            _ ≤ (c * q₀) ^ j * (B / c₀) :=
                mul_le_mul hdj hφx (div_nonneg (hφ0 x).le hc₀.le) (pow_nonneg hcq.le _)
      _ = (c * q₀) ^ j * M₀ := by rw [hM₀]; ring
  refine ⟨q₀, hq0, hq1, (M₀ / (c * q₀)) ^ 2, sq_nonneg _, fun j => ?_⟩
  have hr : Bdd (iter μ (rem k c φ) j) := (Bdd.rem hk hφm hφb (c := c)).iter j
  refine (hs_le_sq hr (hbound j)).trans (le_of_eq ?_)
  have hc' : c ≠ 0 := hc.ne'
  have hq' : q₀ ≠ 0 := (lt_of_lt_of_le (by norm_num) (le_max_right _ _)).ne'
  rw [div_pow, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  field_simp
  ring

end Floor

/-! ## 8. The gap from the two-slice cluster bound -/

section Gap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

variable (μ) in
/-- **Two-slice decay at rate `ρ`**: for every continuous test `u` the connected two-slice read of
`pairExp (k^{∗(j+1)})` is at most `C_u ρ^{j+1}` for all large `j`. DERIVED: `1` the power offset. -/
def PairDecay (k : X → X → ℝ) (ρ : ℝ) : Prop :=
  ∀ u : C(X, ℝ), ∃ C : ℝ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
    |FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
          * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2)| ≤ C * ρ ^ (j + 1)

variable {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hφm hφb heig in
/-- **An eigenfunction of a continuous kernel bounded by `1` is continuous.** DERIVED: `1` the kernel
bound. -/
theorem continuous_eigen (hkc : Continuous (Function.uncurry k)) (hk1 : ∀ x y, |k x y| ≤ 1)
    (hc : c ≠ 0) : Continuous φ := by
  have e : φ = fun z => c⁻¹ * ∫ y, k z y * φ y ∂μ := by
    funext z; rw [heig z]; field_simp
  rw [e]
  refine continuous_const.mul (continuous_of_dominated (bound := fun _ => 1 * B) (fun z => ?_)
    (fun z => Filter.Eventually.of_forall fun y => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun y => ?_))
  · exact ((hkc.measurable.comp measurable_prodMk_left).mul hφm).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_mul_le_of (hk1 z y) (hφb y)
  · exact (hkc.comp (continuous_id.prodMk continuous_const)).mul continuous_const

include hk hsym hφm hφb hφ1 heig in
/-- **One doubling step of the bootstrap.** Under `PairDecay μ k ρ` with `0 < ρ ≤ 1`, a decay
`hs(r_j) ≤ C (c q)^{2(j+1)}` of the remainder iterates at some `0 ≤ q ≤ 1` gives
`‖R‖ ≤ c · max ρ q²`, `R = kernelCLM (k − c φ⊗φ)`.

On a continuous `w = φ u`, `‖Rᵗ w‖² = ⟨w, R^{2t} w⟩` (`StrongTransferGap.pow_inner_symm`) is the remainder's
form at `2t` (`inner_pow_eq`), which `w_bound` bounds by the two-slice read and `hs(r)`; this is per-vector
decay at rate `c · max ρ q²`, and `StrongTransferGap.opNorm_le_of_decay_dense` on the dense continuous
functions gives the operator bound.

DERIVED: `2` the doubling and the square; `5` as in `alg_w`; `1` the bounds on `ρ`, `q`. -/
theorem gap_step (hkc : Continuous (Function.uncurry k)) (hk1 : ∀ x y, |k x y| ≤ 1)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hφlow : ∀ x, c₀ ≤ φ x) (hc : 0 < c)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hdec : PairDecay μ k ρ)
    {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem k c φ x y| ≤ Cr)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {CH : ℝ} (hCH0 : 0 ≤ CH)
    (hH : ∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH * (c * q) ^ (2 * (j + 1))) :
    ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ c * max ρ (q ^ 2) := by
  classical
  set θ := max ρ (q ^ 2) with hθ
  have hθ0 : 0 < θ := lt_max_of_lt_left hρ0
  have hρθ : ρ ≤ θ := le_max_left _ _
  have hqθ : q ^ 2 ≤ θ := le_max_right _ _
  set R := kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ with hRdef
  have hsymr : ∀ x y, rem k c φ x y = rem k c φ y x := fun x y => by
    unfold MassGap.KernelPower.rem; rw [hsym x y]; ring
  have hA : ∀ u v, inner ℝ (R u) v = inner ℝ u (R v) := fun u v =>
    (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ Cr hrm hCr0 hrb μ hsymr).isSymmetric u v
  have hφpos : ∀ x, 0 < φ x := fun x => hc₀.trans_le (hφlow x)
  have hφc : Continuous φ := continuous_eigen hφm hφb heig hkc hk1 hc.ne'
  have hrem : Bdd (rem k c φ) := Bdd.rem hk hφm hφb
  refine StrongTransferGap.opNorm_le_of_decay_dense hA (mul_nonneg hc.le hθ0.le)
    (ContinuousMap.toLp_denseRange ℝ μ ℝ (p := 2) (by norm_num)) ?_
  rintro f ⟨w, rfl⟩
  let u : C(X, ℝ) := ⟨fun x => w x / φ x, w.continuous.div hφc (fun x => (hφpos x).ne')⟩
  have hwu : ∀ x, φ x * u x = w x := fun x => by
    show φ x * (w x / φ x) = w x
    have h := (hφpos x).ne'
    field_simp
  set s := ‖u‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  have hus : ∀ x, |u x| ≤ s := fun x => by
    have := u.norm_coe_le_norm x; rwa [Real.norm_eq_abs] at this
  have hum : Measurable (u : X → ℝ) := u.continuous.measurable
  obtain ⟨C, j₀, hC⟩ := hdec u
  set C' := max C (2 * (s * s) / ρ ^ j₀) with hC'
  have hC'0 : 0 ≤ C' := le_max_of_le_right (by positivity)
  have hcorr : ∀ j : ℕ,
      |FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
          * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2)| ≤ C' * ρ ^ (j + 1) := by
    intro j
    by_cases hj : j₀ ≤ j
    · exact (hC j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ0.le _))
    · have hkj : Bdd (iter μ k j) := hk.iter j
      have p1 := abs_pairExp_le (μ := μ) hkj (h := fun p : X × X => u p.1 * u p.2)
        (mul_nonneg hs0 hs0) (fun p => abs_mul_le_of (hus p.1) (hus p.2))
      have p2 := abs_pairExp_le (μ := μ) hkj (h := fun p : X × X => u p.1) hs0 (fun p => hus p.1)
      have p3 := abs_pairExp_le (μ := μ) hkj (h := fun p : X × X => u p.2) hs0 (fun p => hus p.2)
      have htriv : |FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2)
          - FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
            * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2)| ≤ 2 * (s * s) := by
        have := abs_sub (FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2))
          (FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
            * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2))
        have := abs_mul_le_of p2 p3
        linarith
      refine htriv.trans ?_
      have hjj : j + 1 ≤ j₀ := by omega
      have hpow : ρ ^ j₀ ≤ ρ ^ (j + 1) := pow_le_pow_of_le_one hρ0.le hρ1 hjj
      have hρj : 0 < ρ ^ j₀ := pow_pos hρ0 _
      calc 2 * (s * s) = 2 * (s * s) / ρ ^ j₀ * ρ ^ j₀ := by field_simp
        _ ≤ 2 * (s * s) / ρ ^ j₀ * ρ ^ (j + 1) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C' * ρ ^ (j + 1) := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hρ0.le _)
  set D := (C' * (1 + CH) + 5 * (s * s) * CH) / 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hW : ∀ j : ℕ,
      |∫ x, ∫ y, φ x * u x * iter μ (rem k c φ) j x y * (φ y * u y) ∂μ ∂μ|
        ≤ D * (c * θ) ^ (j + 1) := by
    intro j
    have hb := w_bound hk hsym hφm hφb hφ1 heig hc j hum hs0 hus (hcorr j)
    refine hb.trans ?_
    set P := c ^ (j + 1) with hP
    have hP0 : 0 < P := pow_pos hc _
    set Y := hs μ (iter μ (rem k c φ) j) with hY
    have hY0 : 0 ≤ Y := hs_nonneg _
    set Qn := (q ^ 2) ^ (j + 1) with hQn
    have hQn0 : 0 ≤ Qn := by positivity
    have hQn1 : Qn ≤ 1 := pow_le_one₀ (sq_nonneg q) (by nlinarith)
    have hQθ : Qn ≤ θ ^ (j + 1) := pow_le_pow_left₀ (sq_nonneg q) hqθ _
    have hρn : ρ ^ (j + 1) ≤ θ ^ (j + 1) := pow_le_pow_left₀ hρ0.le hρθ _
    have hYb : Y ≤ CH * (P ^ 2 * Qn) := by
      have := hH j
      have e : (c * q) ^ (2 * (j + 1)) = P ^ 2 * Qn := by
        rw [hP, hQn]; ring
      rwa [e] at this
    have hnum : C' * ρ ^ (j + 1) * (P ^ 2 + Y) + 5 * (s * s) * Y
        ≤ P ^ 2 * (2 * D) * θ ^ (j + 1) := by
      have h1 : C' * ρ ^ (j + 1) * (P ^ 2 + Y) ≤ C' * θ ^ (j + 1) * (P ^ 2 * (1 + CH)) := by
        have hY' : P ^ 2 + Y ≤ P ^ 2 * (1 + CH) := by
          have : CH * (P ^ 2 * Qn) ≤ CH * P ^ 2 :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg P) hQn1) hCH0
          nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left hρn hC'0) hY' (by positivity) (by positivity)
      have h2 : 5 * (s * s) * Y ≤ 5 * (s * s) * (CH * (P ^ 2 * θ ^ (j + 1))) := by
        refine mul_le_mul_of_nonneg_left (hYb.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQθ (sq_nonneg P)) hCH0
      rw [hD]
      nlinarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * P)]
    calc C' * ρ ^ (j + 1) * (P ^ 2 + Y) + 5 * (s * s) * Y ≤ P ^ 2 * (2 * D) * θ ^ (j + 1) := hnum
      _ = D * (c * θ) ^ (j + 1) * (2 * P) := by rw [hP, mul_pow]; ring
  -- per-vector decay
  set f := ContinuousMap.toLp (E := ℝ) 2 μ ℝ w with hf
  have hfw : (f : X → ℝ) =ᵐ[μ] w := ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (μ := μ) (𝕜 := ℝ) w
  refine ⟨max (Real.sqrt D) ‖f‖, fun t => ?_⟩
  rcases t with _ | t
  · simp
  · have hsq : ‖(R ^ (t + 1)) f‖ ^ 2 ≤ D * (c * θ) ^ (2 * (t + 1)) := by
      have e1 : ‖(R ^ (t + 1)) f‖ ^ 2 = inner ℝ f ((R ^ ((t + 1 + t) + 1)) f) := by
        rw [← real_inner_self_eq_norm_sq, StrongTransferGap.pow_inner_symm hA (t + 1) f,
          ← mul_apply_eq_comp, ← pow_add]
        congr 2
      have e2 := inner_pow_eq hrem hrm hCr0 hrb f hfw (t + 1 + t)
      have e3 : ∫ x, w x * ∫ y, iter μ (rem k c φ) (t + 1 + t) x y * w y ∂μ ∂μ
          = ∫ x, ∫ y, φ x * u x * iter μ (rem k c φ) (t + 1 + t) x y * (φ y * u y) ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_const_mul]; congr 1; funext y
        rw [hwu x, hwu y]; ring
      rw [e1, e2, e3]
      refine (le_abs_self _).trans ((hW (t + 1 + t)).trans (le_of_eq ?_))
      congr 2; omega
    have hcθ : 0 ≤ c * θ := mul_nonneg hc.le hθ0.le
    have hn0 : 0 ≤ ‖(R ^ (t + 1)) f‖ := norm_nonneg _
    have hsqrt : ‖(R ^ (t + 1)) f‖ ≤ Real.sqrt D * (c * θ) ^ (t + 1) := by
      rw [← pow_le_pow_iff_left₀ hn0 (by positivity) two_ne_zero]
      calc ‖(R ^ (t + 1)) f‖ ^ 2 ≤ D * (c * θ) ^ (2 * (t + 1)) := hsq
        _ = (Real.sqrt D * (c * θ) ^ (t + 1)) ^ 2 := by
            rw [mul_pow (Real.sqrt D), Real.sq_sqrt hD0, ← pow_mul, mul_comm 2 (t + 1)]
    exact hsqrt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

include hk hsym hφm hφb hφ1 heig in
/-- **The remainder norm is at most `c ρ`.** A kernel with values in `[a, 1]`, `a > 0`, continuous and
symmetric, with a unit eigenfunction `φ ≥ c₀ > 0` at `c > 0` and two-slice decay at rate
`0 < ρ ≤ 1`, has `‖kernelCLM (k − c φ⊗φ)‖ ≤ c ρ`.

`floor_decay` starts the bootstrap at some `q₀ < 1`; `gap_step` takes the decay at `q` to the operator
bound at `max ρ q²` and, through `KernelPower.hs_iter_le`, back to a decay at `max ρ q²`. After `m`
steps the bound is `c · max ρ (q₀^{2^m})`, which tends to `c ρ`.

DERIVED: `2` the doubling; `1` the bounds on `ρ`, `q`. -/
theorem gap_of_pairDecay (hkc : Continuous (Function.uncurry k)) {a : ℝ} (ha : 0 < a)
    (hlo : ∀ x y, a ≤ k x y) (hhi : ∀ x y, k x y ≤ 1)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hφlow : ∀ x, c₀ ≤ φ x) (hc : 0 < c)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hdec : PairDecay μ k ρ)
    {Cr : ℝ} (hrm : Measurable (Function.uncurry (rem k c φ))) (hCr0 : 0 ≤ Cr)
    (hrb : ∀ x y, |rem k c φ x y| ≤ Cr) :
    ‖kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ‖ ≤ c * ρ := by
  have hk1 : ∀ x y, |k x y| ≤ 1 := fun x y => by
    rw [abs_le]; exact ⟨by linarith [hlo x y], hhi x y⟩
  obtain ⟨q₀, hq00, hq01, CH₀, hCH₀, hH₀⟩ :=
    floor_decay (μ := μ) hk hsym hφm hφb hφ1 heig ha hlo hhi hc₀ hφlow hc
  set R := kernelCLM (rem k c φ) Cr hrm hCr0 hrb μ μ with hRdef
  -- decay at a rate `q` is monotone in `q`
  have mono : ∀ {q q' CH : ℝ}, 0 ≤ q → q ≤ q' →
      (∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH * (c * q) ^ (2 * (j + 1))) → 0 ≤ CH →
      ∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH * (c * q') ^ (2 * (j + 1)) := by
    intro q q' CH hq hqq' h hCH j
    refine (h j).trans (mul_le_mul_of_nonneg_left ?_ hCH)
    exact pow_le_pow_left₀ (mul_nonneg hc.le hq) (mul_le_mul_of_nonneg_left hqq' hc.le) _
  -- the operator bound gives decay at the same rate
  have back : ∀ {θ : ℝ}, 0 < θ → ‖R‖ ≤ c * θ → ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH * (c * θ) ^ (2 * (j + 1)) := by
    intro θ hθ hR
    have hcθ : 0 < c * θ := mul_pos hc hθ
    refine ⟨hs μ (rem k c φ) / (c * θ) ^ 2, div_nonneg (hs_nonneg _) (by positivity), fun j => ?_⟩
    have h := hs_iter_le (μ := μ) hrm hCr0 hrb 0 j
    rw [zero_add] at h
    refine h.trans ?_
    have hpow : ‖R‖ ^ (2 * j) ≤ (c * θ) ^ (2 * j) := pow_le_pow_left₀ (norm_nonneg _) hR _
    have e : hs μ (rem k c φ) / (c * θ) ^ 2 * (c * θ) ^ (2 * (j + 1))
        = (c * θ) ^ (2 * j) * hs μ (rem k c φ) := by
      have hne : (c * θ) ^ 2 ≠ 0 := by positivity
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hpow (hs_nonneg _)
  -- the bootstrap
  have hmax : ∀ x : ℝ, 0 ≤ x → max ρ ((max ρ x) ^ 2) ≤ max ρ (x ^ 2) := by
    intro x hx
    refine max_le (le_max_left _ _) ?_
    rcases le_total ρ x with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]
      exact (pow_le_of_le_one hρ0.le hρ1 two_ne_zero).trans (le_max_left _ _)
  have hseq : ∀ m : ℕ, (∃ CH : ℝ, 0 ≤ CH ∧ ∀ j : ℕ,
      hs μ (iter μ (rem k c φ) j) ≤ CH * (c * max ρ (q₀ ^ (2 ^ m))) ^ (2 * (j + 1))) ∧
      ‖R‖ ≤ c * max ρ (q₀ ^ (2 ^ (m + 1))) := by
    intro m
    induction m with
    | zero =>
      have hH : ∀ j : ℕ, hs μ (iter μ (rem k c φ) j) ≤ CH₀ * (c * max ρ (q₀ ^ (2 ^ 0))) ^ (2 * (j + 1)) :=
        mono hq00 (by simp) hH₀ hCH₀
      refine ⟨⟨CH₀, hCH₀, hH⟩, ?_⟩
      have hs := gap_step hk hsym hφm hφb hφ1 heig hkc hk1 hc₀ hφlow hc hρ0 hρ1 hdec hrm hCr0 hrb
        (le_max_of_le_left hρ0.le) (max_le hρ1 (by simpa using hq01.le)) hCH₀ hH
      refine hs.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
      have := hmax (q₀ ^ (2 ^ 0)) (by positivity)
      simpa [pow_succ, pow_mul] using this
    | succ m ih =>
      obtain ⟨⟨CH, hCH, hH⟩, hR⟩ := ih
      have hθ0 : 0 < max ρ (q₀ ^ (2 ^ (m + 1))) := lt_max_of_lt_left hρ0
      obtain ⟨CH', hCH', hH'⟩ := back hθ0 hR
      have hq1 : max ρ (q₀ ^ (2 ^ (m + 1))) ≤ 1 :=
        max_le hρ1 (pow_le_one₀ hq00 hq01.le)
      refine ⟨⟨CH', hCH', hH'⟩, ?_⟩
      have hs := gap_step hk hsym hφm hφb hφ1 heig hkc hk1 hc₀ hφlow hc hρ0 hρ1 hdec hrm hCr0 hrb
        hθ0.le hq1 hCH' hH'
      refine hs.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
      have := hmax (q₀ ^ (2 ^ (m + 1))) (by positivity)
      have e : (q₀ ^ (2 ^ (m + 1))) ^ 2 = q₀ ^ (2 ^ (m + 1 + 1)) := by
        rw [← pow_mul, ← pow_succ]
      rwa [e] at this
  -- the limit
  have hle : ∀ m : ℕ, ‖R‖ ≤ c * max ρ (q₀ ^ (m + 1)) := by
    intro m
    refine (hseq m).2.trans (mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) hc.le)
    refine pow_le_pow_of_le_one hq00 hq01.le ?_
    have : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    omega
  have htend : Tendsto (fun m : ℕ => c * max ρ (q₀ ^ (m + 1))) atTop (𝓝 (c * max ρ 0)) :=
    (tendsto_const_nhds.max ((tendsto_pow_atTop_nhds_zero_of_lt_one hq00 hq01).comp
      (tendsto_add_atTop_nat 1))).const_mul c
  have := ge_of_tendsto' htend hle
  rwa [max_eq_left hρ0.le] at this

end Gap

/-! ## 9. The uniform relay gap -/

section Uniform

variable {N : ℕ} [NeZero N]

/-- **`coreRate K β` is monotone in `β ≥ 0`.** DERIVED: `2`, `4` the exponents of `coreRate`. -/
theorem coreRate_mono_beta (K : ℕ) {β β' : ℝ} (hβ : 0 ≤ β) (h : β ≤ β') :
    StrongCoupling.coreRate K β ≤ StrongCoupling.coreRate K β' := by
  unfold StrongCoupling.coreRate
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : Real.exp (2 * β) - 1 ≤ Real.exp (2 * β') - 1 := by
    have := Real.exp_le_exp.mpr (by linarith : 2 * β ≤ 2 * β'); linarith
  have h0 : 0 ≤ Real.exp (2 * β) - 1 := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * β); linarith
  have h2 : Real.exp (4 * β * K) ≤ Real.exp (4 * β' * K) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hA : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (Real.exp_pos _).le
    (mul_nonneg hA (h0.trans h1))

/-- **A slice with an empty transverse extent has a gap at every rate.** The slice configuration space
is a point, the unit eigenfunction is `±1`, the kernel is its eigenvalue, and the remainder vanishes.
DERIVED: `0` the empty extent and the remainder. -/
theorem relay_gap_empty {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ)
    (hT : ∃ k, T k = 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ,
      SliceTransferGap.TransferGapAt N i T β lam φ (|lam| * ρ) := by
  obtain ⟨k₀, hk₀⟩ := hT
  haveI : IsEmpty (Fin (T k₀)) := by rw [hk₀]; infer_instance
  haveI : IsEmpty (TT i T) := ⟨fun y => isEmptyElim (y k₀)⟩
  haveI : IsEmpty (SpT i T) := ⟨fun p => isEmptyElim p.2⟩
  obtain ⟨hpos, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen_kT (μ := i) (T := T) (N := N) (NeZero.ne N) hβ
  set c := ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le (NeZero.ne N) hβ) (hS i T N) (hS i T N)‖ with hcdef
  let x₀ : SpT i T → SUN.SU N := fun p => isEmptyElim p
  have hall : ∀ x : SpT i T → SUN.SU N, x = x₀ := fun x => funext fun p => isEmptyElim p
  have hint : ∀ f : (SpT i T → SUN.SU N) → ℝ, ∫ y, f y ∂(hS i T N) = f x₀ := by
    intro f
    have e : (fun y => f y) = fun _ => f x₀ := funext fun y => by rw [hall y]
    rw [e, integral_const]
    simp
  have hφ2 : φ x₀ ^ 2 = 1 := by rw [← hint (fun x => φ x ^ 2)]; exact hφ1
  have hφ0 : φ x₀ ≠ 0 := (hc₀.trans_le (hlow x₀)).ne'
  have hk : kT i T N β x₀ x₀ = c := by
    have h := heig x₀
    rw [hint (fun y => kT i T N β x₀ y * φ y)] at h
    exact mul_right_cancel₀ hφ0 h
  have hbr := Bdd.rem (bdd_kT (μ := i) (T := T) (NeZero.ne N) hβ) hφm hφb (c := c)
  have hzero : ∀ x y, |rem (kT i T N β) c φ x y| ≤ 0 := by
    intro x y
    rw [hall x, hall y]
    unfold MassGap.KernelPower.rem
    rw [hk, mul_assoc, ← sq, hφ2]
    simp
  refine ⟨c, φ, hφm, ⟨_, hφb⟩, hφ1, hpos.ne', heig, 0, hbr.meas, le_rfl, hzero, ?_⟩
  exact (norm_kernelCLM_le _ _ _ _ _ _ _).trans (by positivity)

/-- **The relay gap of one slice at a rate fixed by the coupling.** At `0 ≤ β` with
`coreRate 64 β ≤ ρ < 1`, `0 < ρ`, every slice transfer `kT i T N β` has a unit eigenpair with remainder
norm at most `|λ| ρ`, whatever the transverse extents `T`.

The eigenpair is the Jentzsch top (`JentzschKT.exists_pos_eigen_kT`): `λ = ‖K‖ > 0`, `φ ≥ c₀ > 0`. The
two-slice cluster bound `slice_pair_cluster` gives `PairDecay` at rate `ρ` with a prefactor that grows
with `|TT|` and no rate loss, and `gap_of_pairDecay` turns it into the operator bound. An empty
transverse extent is `relay_gap_empty`.

DERIVED: `16 * 4` the touch degree; `64 |TT|` the anchor size; `1` the rate's ceiling. -/
theorem slice_relay_gap {β : ℝ} (hβ : 0 ≤ β) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hrβ : StrongCoupling.coreRate (16 * 4) β ≤ ρ) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ,
      SliceTransferGap.TransferGapAt N i T β lam φ (|lam| * ρ) := by
  by_cases hT : ∀ k, 0 < T k
  · have hN : N ≠ 0 := NeZero.ne N
    have hr : StrongCoupling.coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrβ hρ1
    obtain ⟨hpos, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
      JentzschKT.exists_pos_eigen_kT (μ := i) (T := T) (N := N) hN hβ
    set c := ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one
      (abs_kT_le hN hβ) (hS i T N) (hS i T N)‖ with hcdef
    have hk : Bdd (kT i T N β) := bdd_kT hN hβ
    have hbr := Bdd.rem hk hφm hφb (c := c)
    obtain ⟨Cr, hrb⟩ := hbr.bdd
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (hS i T N)
    have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hrb x₀ x₀)
    have hdec : PairDecay (hS i T N) (kT i T N β) ρ := by
      intro u
      set U := 64 * Fintype.card (TT i T) with hU
      set G := StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β U with hG
      refine ⟨G * (ρ / ρ ^ U), U, fun j hj => ?_⟩
      have h := slice_pair_cluster hN hβ hr i T hT j u (by omega)
      refine h.trans ?_
      have hr0 : 0 ≤ StrongCoupling.coreRate (16 * 4) β := StrongCoupling.coreRate_nonneg _ hβ
      have hG0 : 0 ≤ G := by
        rw [hG]
        unfold StrongCoupling.coreConstG StrongCoupling.corePrefactorG
        have : (0 : ℝ) < 1 - StrongCoupling.coreRate (16 * 4) β := by linarith
        exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
          this.le
      have hpow : StrongCoupling.coreRate (16 * 4) β ^ (j + 2 - U) ≤ ρ ^ (j + 2 - U) :=
        pow_le_pow_left₀ hr0 hrβ _
      have hρU : 0 < ρ ^ U := pow_pos hρ0 _
      have e : ρ ^ (j + 2 - U) = ρ ^ (j + 1) * (ρ / ρ ^ U) := by
        rw [eq_comm, mul_div_assoc', div_eq_iff hρU.ne', ← pow_succ, ← pow_add]
        congr 1; omega
      calc G * StrongCoupling.coreRate (16 * 4) β ^ (j + 2 - U) ≤ G * ρ ^ (j + 2 - U) :=
            mul_le_mul_of_nonneg_left hpow hG0
        _ = G * (ρ / ρ ^ U) * ρ ^ (j + 1) := by rw [e]; ring
    have hgap := gap_of_pairDecay (μ := hS i T N) hk (kT_symm β) hφm hφb hφ1 heig
      (continuous_kT β) (kTmin_pos β) (kT_lower hN hβ) (kT_le_one hN hβ) hc₀ hlow hpos hρ0 hρ1.le
      hdec hbr.meas hCr0 hrb
    refine ⟨c, φ, hφm, ⟨_, hφb⟩, hφ1, hpos.ne', heig, Cr, hbr.meas, hCr0, hrb, ?_⟩
    rwa [abs_of_pos hpos]
  · push Not at hT
    obtain ⟨k, hk⟩ := hT
    exact relay_gap_empty hβ i T ⟨k, by omega⟩ hρ0.le

/-- **`StrongTransferGap.UniformRelayGap N`: the strong-coupling relay gap, uniform in the slice.** There
are `β₀ > 0` and `m > 0` such that at every `0 ≤ β ≤ β₀`, every direction `i` and every transverse
extent `T`, the slice transfer has a unit eigenpair with remainder norm at most `|λ| e^{−m}`.

`β₀` is half the threshold of `StrongCoupling.core_rate_lt_one_of_small_hypercubic 4`, and
`e^{−m} = coreRate 64 β₀`; `coreRate 64 β ≤ coreRate 64 β₀` below it (`coreRate_mono_beta`), and
`slice_relay_gap` gives each slice.

DERIVED: `16 * 4` the touch degree; `2` halves the threshold; `0` the lower ends. -/
theorem uniformRelayGap : StrongTransferGap.UniformRelayGap N := by
  obtain ⟨b, hb, hsmall⟩ := StrongCoupling.core_rate_lt_one_of_small_hypercubic 4
  have hβ₀ : 0 < b / 2 := by positivity
  have hβ₀b : b / 2 < b := by linarith
  set ρ := StrongCoupling.coreRate (16 * 4) (b / 2) with hρ
  have hρ0 : 0 < ρ := StrongCouplingGap.coreRate_pos _ hβ₀
  have hρ1 : ρ < 1 := hsmall (b / 2) hβ₀.le hβ₀b
  refine ⟨b / 2, hβ₀, -Real.log ρ, neg_pos.mpr (Real.log_neg hρ0 hρ1), fun β hβ hββ₀ i T => ?_⟩
  have e : Real.exp (-(-Real.log ρ)) = ρ := by rw [neg_neg, Real.exp_log hρ0]
  rw [e]
  exact slice_relay_gap hβ hρ0 hρ1 (coreRate_mono_beta _ hβ hββ₀) i T

/-- **`StrongTransferGap.UniformSliceDecay N`**, the time-decay form, from `uniformRelayGap` and
`StrongTransferGap.uniformSliceDecay_iff`. DERIVED: no numeral. -/
theorem uniformSliceDecay : StrongTransferGap.UniformSliceDecay N :=
  StrongTransferGap.uniformSliceDecay_iff.mpr uniformRelayGap

end Uniform

end MassGap.UniformRelayStrong

end

#print axioms MassGap.UniformRelayStrong.rshift_apply
#print axioms MassGap.UniformRelayStrong.runshift_rshift
#print axioms MassGap.UniformRelayStrong.rshift_runshift
#print axioms MassGap.UniformRelayStrong.rlink_site_coord
#print axioms MassGap.UniformRelayStrong.rhead_mem
#print axioms MassGap.UniformRelayStrong.rlast_mem
#print axioms MassGap.UniformRelayStrong.rsecond_mem
#print axioms MassGap.UniformRelayStrong.linkMult_rbd_le
#print axioms MassGap.UniformRelayStrong.linkSupp_rbd_card_le
#print axioms MassGap.UniformRelayStrong.touchDeg_rbd_le
#print axioms MassGap.UniformRelayStrong.mem_rCube
#print axioms MassGap.UniformRelayStrong.mem_rCube_base
#print axioms MassGap.UniformRelayStrong.rreach_same_site
#print axioms MassGap.UniformRelayStrong.rreach_from_base
#print axioms MassGap.UniformRelayStrong.rcircDist_lipschitz
#print axioms MassGap.UniformRelayStrong.r_not_mem_ball
#print axioms MassGap.UniformRelayStrong.linkHalo_subset_layer
#print axioms MassGap.UniformRelayStrong.card_layer_le
#print axioms MassGap.UniformRelayStrong.continuous_rpull
#print axioms MassGap.UniformRelayStrong.localOnLinks_sliceObs
#print axioms MassGap.UniformRelayStrong.abs_sliceObs_le
#print axioms MassGap.UniformRelayStrong.rect_conn_eq
#print axioms MassGap.UniformRelayStrong.rect_pair_cluster
#print axioms MassGap.UniformRelayStrong.tr_extT
#print axioms MassGap.UniformRelayStrong.extT_self
#print axioms MassGap.UniformRelayStrong.slice_pair_cluster
#print axioms MassGap.UniformRelayStrong.abs_mul_le_of
#print axioms MassGap.UniformRelayStrong.bdd_mul
#print axioms MassGap.UniformRelayStrong.bdd_left
#print axioms MassGap.UniformRelayStrong.bdd_right
#print axioms MassGap.UniformRelayStrong.bdd_const
#print axioms MassGap.UniformRelayStrong.iint_add
#print axioms MassGap.UniformRelayStrong.abs_iint_sq_mul_le
#print axioms MassGap.UniformRelayStrong.abs_pairExp_le
#print axioms MassGap.UniformRelayStrong.alg_w
#print axioms MassGap.UniformRelayStrong.pair_expand
#print axioms MassGap.UniformRelayStrong.mid_right_zero
#print axioms MassGap.UniformRelayStrong.mid_left_zero
#print axioms MassGap.UniformRelayStrong.abs_int_phi_sq_le
#print axioms MassGap.UniformRelayStrong.w_bound
#print axioms MassGap.UniformRelayStrong.pow_apply_ae
#print axioms MassGap.UniformRelayStrong.inner_pow_eq
#print axioms MassGap.UniformRelayStrong.hs_le_sq
#print axioms MassGap.UniformRelayStrong.floor_decay
#print axioms MassGap.UniformRelayStrong.continuous_eigen
#print axioms MassGap.UniformRelayStrong.gap_step
#print axioms MassGap.UniformRelayStrong.gap_of_pairDecay
#print axioms MassGap.UniformRelayStrong.coreRate_mono_beta
#print axioms MassGap.UniformRelayStrong.relay_gap_empty
#print axioms MassGap.UniformRelayStrong.slice_relay_gap
#print axioms MassGap.UniformRelayStrong.uniformRelayGap
#print axioms MassGap.UniformRelayStrong.uniformSliceDecay
