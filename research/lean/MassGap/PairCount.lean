import Mathlib
import MassGap.HeatBath

noncomputable section

/-!
# MassGap.PairCount — the plaquette counts of a pair of torus links

## What it gives

`n2 M l m`: the number of non-diagonal ordered plaquettes of the periodic lattice of extent `M + 1`
whose boundary word visits both `l` and `m`. At extent at least `2` (`1 ≤ M`):
* a non-diagonal plaquette visits four distinct links (`nodup_nondiag`), a diagonal plaquette has
  holonomy `1` (`wilsonHol_diag`);
* at most `12` non-diagonal plaquettes visit a link (`card_visit_nondiag_le`);
* `n2 M l m ∈ {0, 2, 4}` for `l ≠ m` (`n2_cases`);
* `Σ_{m ≠ l} n2 M l m ≤ 36 = 12 · 3` (`sum_n2_le`);
* at most `3` partners have `n2 = 4` (`card_n2_four_le`).

## The route

Sites are the additive group `Fin 4 → Fin (M + 1)`, and the shift in direction `ρ` adds the unit
vector `ev M ρ` (`shift_eq`). At `1 ≤ M` the unit vectors are non-zero, distinct, and no two
distinct ones sum to `0` (`ev_ne_zero`, `ev_inj`, `ev_add_ne_zero`).

The non-diagonal plaquettes through `l = (a, y)` are exactly the images of
`(s, t, ρ) ∈ Bool × Bool × (Fin 4 ∖ {a})` under `plq a y`: plane `(a, ρ)` or `(ρ, a)` by `s`, base
`y` or `y − ev ρ` by `t` (`plq_cover`, `plq_visit`, `plq_nondiag`), injectively (`plq_inj`, through
the left inverse `plqInv`). So `card_visit_nondiag_le` is `|Bool × Bool × Fin 3| = 12`, and
`n2 M l m` is the number of parameters whose plaquette also visits `m` (`n2_eq_card`). The two
orientations visit the same links (`mem_word_swap`), so `n2 M l m = 2 · |tp a y m|` with `tp` the
`(t, ρ)` of the plane `(a, ρ)` visiting `m` (`card_T_eq`). A partner `m ≠ l` lies in at most one
plane per base (`tp_unique`), so `|tp| ≤ 2`; a partner off the direction `a` lies in at most one
plaquette (`card_tp_le_one`, from `no_double`), so `n2 = 4` forces `m = (a, y + ev ρ)`
(`card_n2_four_le`). `sum_n2_le` is double counting: each of the at most `12` plaquettes through
`l` visits at most `3` other links.
-/

namespace MassGap.PairCount

open MassGap.HeatBath (bdT)
open MassGap.WilsonLattice (wilsonHol)

/-- **The pair count**: non-diagonal ordered plaquettes visiting both `l` and `m`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`p.1.1`, `p.1.2` are projections. -/
def n2 (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℕ :=
  (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
    p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst ∧ m ∈ (bdT M p).map Prod.fst)).card

/-! ## 1. Unit vectors and the boundary word -/

/-- The unit vector of direction `ρ` in the site group.

DERIVED: `4` is the spacetime dimension; `1` is the unit step and the successor writing the
extent. -/
private def ev (M : ℕ) (ρ : Fin 4) : WilsonHypercubic.Site 4 (M + 1) := Pi.single ρ 1

/-- DERIVED: `4` is the spacetime dimension; `1` is the unit step and the successor writing the
extent. -/
private theorem ev_self (M : ℕ) (ρ : Fin 4) : ev M ρ ρ = 1 := by
  simp [ev]

/-- DERIVED: `4` is the spacetime dimension; `0` is the off-axis entry. -/
private theorem ev_ne (M : ℕ) {ρ σ : Fin 4} (h : σ ≠ ρ) : ev M ρ σ = 0 := by
  simp [ev, Pi.single_apply, h]

/-- DERIVED: `1` is the least `M` (extent `2`) and the unit; `0` is the zero of `Fin (M + 1)`. -/
private theorem finOne_ne_zero {M : ℕ} (hM : 1 ≤ M) : (1 : Fin (M + 1)) ≠ 0 := by
  intro h
  have h' := Fin.one_eq_zero_iff.mp h
  omega

/-- DERIVED: `1` is the least `M`; `0` is the zero site; `4` is the spacetime dimension. -/
private theorem ev_ne_zero {M : ℕ} (hM : 1 ≤ M) (ρ : Fin 4) : ev M ρ ≠ 0 := by
  intro h
  have h1 := congrFun h ρ
  rw [ev_self, Pi.zero_apply] at h1
  exact finOne_ne_zero hM h1

/-- DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem ev_inj {M : ℕ} (hM : 1 ≤ M) {ρ σ : Fin 4} (h : ev M ρ = ev M σ) : ρ = σ := by
  by_contra hne
  have h1 := congrFun h ρ
  rw [ev_self, ev_ne M hne] at h1
  exact finOne_ne_zero hM h1

/-- DERIVED: `1` is the least `M`; `0` is the zero site; `4` is the spacetime dimension. -/
private theorem ev_add_ne_zero {M : ℕ} (hM : 1 ≤ M) {ρ σ : Fin 4} (h : ρ ≠ σ) :
    ev M ρ + ev M σ ≠ 0 := by
  intro h0
  have h1 := congrFun h0 ρ
  rw [Pi.add_apply, ev_self, ev_ne M h, add_zero, Pi.zero_apply] at h1
  exact finOne_ne_zero hM h1

/-- **The shift adds the unit vector.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private theorem shift_eq (M : ℕ) (ρ : Fin 4) (x : WilsonHypercubic.Site 4 (M + 1)) :
    WilsonHypercubic.shift ρ x = x + ev M ρ := by
  funext k
  by_cases hk : k = ρ
  · rw [hk, WilsonHypercubic.shift, Function.update_self, Pi.add_apply, ev_self]
  · rw [WilsonHypercubic.shift, Function.update_of_ne hk, Pi.add_apply, ev_ne M hk, add_zero]

/-- DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem add_ev_ne {M : ℕ} (hM : 1 ≤ M) (ρ : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1)) :
    y + ev M ρ ≠ y := by
  intro h
  apply ev_ne_zero hM ρ
  have h2 : y + ev M ρ = y + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h2

/-- DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem sub_ev_ne {M : ℕ} (hM : 1 ≤ M) (ρ : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1)) :
    y - ev M ρ ≠ y := by
  intro h
  exact ev_ne_zero hM ρ (sub_eq_self.mp h)

/-- **The links of a plaquette**: `(μ, x)`, `(ν, x + ev μ)`, `(μ, x + ev ν)`, `(ν, x)`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private theorem mem_word (M : ℕ) (μ ν : Fin 4) (x : WilsonHypercubic.Site 4 (M + 1))
    (k : WilsonHypercubic.Link 4 (M + 1)) :
    k ∈ (bdT M ((μ, ν), x)).map Prod.fst ↔
      k = (μ, x) ∨ k = (ν, x + ev M μ) ∨ k = (μ, x + ev M ν) ∨ k = (ν, x) := by
  rw [← shift_eq M μ x, ← shift_eq M ν x]
  show k ∈ [(μ, x), (ν, WilsonHypercubic.shift μ x), (μ, WilsonHypercubic.shift ν x), (ν, x)] ↔ _
  simp only [List.mem_cons, List.not_mem_nil, or_false, iff_self]

/-- The two orientations of a plane visit the same links.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private theorem mem_word_swap (M : ℕ) (μ ν : Fin 4) (x : WilsonHypercubic.Site 4 (M + 1))
    (k : WilsonHypercubic.Link 4 (M + 1)) :
    k ∈ (bdT M ((ν, μ), x)).map Prod.fst ↔ k ∈ (bdT M ((μ, ν), x)).map Prod.fst := by
  rw [mem_word, mem_word]
  tauto

/-- A link off the direction `a` visited by a plaquette of the plane `(a, ρ)` is one of its two
`ρ`-links.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`k.1`, `k.2` are projections. -/
private theorem mem_word_off {M : ℕ} {a ρ : Fin 4} {x : WilsonHypercubic.Site 4 (M + 1)}
    {k : WilsonHypercubic.Link 4 (M + 1)} (hka : k.1 ≠ a)
    (h : k ∈ (bdT M ((a, ρ), x)).map Prod.fst) : k.2 = x + ev M a ∨ k.2 = x := by
  rcases (mem_word M a ρ x k).mp h with h1 | h1 | h1 | h1
  · exact absurd (congrArg Prod.fst h1) hka
  · exact Or.inl (congrArg Prod.snd h1)
  · exact absurd (congrArg Prod.fst h1) hka
  · exact Or.inr (congrArg Prod.snd h1)

/-- **A diagonal plaquette has holonomy `1`**: its word is `[(a, x), (a, x + â), (a, x + â)⁻¹, (a, x)⁻¹]`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the group
identity; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem wilsonHol_diag {G : Type} [Group G] (M : ℕ) (p : WilsonHypercubic.Plaq 4 (M + 1))
    (hp : p.1.1 = p.1.2) (U : WilsonHypercubic.Link 4 (M + 1) → G) :
    wilsonHol (bdT M) p U = 1 := by
  obtain ⟨⟨μ, ν⟩, x⟩ := p
  have hμν : μ = ν := hp
  rw [← hμν]
  simp [wilsonHol, bdT, WilsonHypercubic.bd]

#print axioms wilsonHol_diag

/-- **A non-diagonal plaquette visits four distinct links** at extent at least `2`.

DERIVED: `4` is the spacetime dimension; `1` is the least `M` (extent `2`) and the successor
writing the extent; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem nodup_nondiag {M : ℕ} (hM : 1 ≤ M) (p : WilsonHypercubic.Plaq 4 (M + 1))
    (hp : p.1.1 ≠ p.1.2) : ((bdT M p).map Prod.fst).Nodup := by
  obtain ⟨⟨μ, ν⟩, x⟩ := p
  have hμν : μ ≠ ν := hp
  have hx1 : x + ev M μ ≠ x := add_ev_ne hM μ x
  have hx2 : x + ev M ν ≠ x := add_ev_ne hM ν x
  show [(μ, x), (ν, WilsonHypercubic.shift μ x), (μ, WilsonHypercubic.shift ν x), (ν, x)].Nodup
  rw [shift_eq M μ x, shift_eq M ν x]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_singleton _⟩⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hμν (congrArg Prod.fst h), fun h => hx2 (congrArg Prod.snd h).symm,
      fun h => hμν (congrArg Prod.fst h)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hμν (congrArg Prod.fst h).symm, fun h => hx1 (congrArg Prod.snd h)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => hμν (congrArg Prod.fst h)

#print axioms nodup_nondiag

/-! ## 2. The plaquettes through a link, parametrised -/

/-- The ordered plane of `a` and `ρ`: `(a, ρ)` for `true`, `(ρ, a)` for `false`.

DERIVED: `4` is the spacetime dimension. -/
private def pl (a ρ : Fin 4) : Bool → Fin 4 × Fin 4
  | true => (a, ρ)
  | false => (ρ, a)

/-- The base site: `y` for `true`, `y − ev ρ` for `false`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private def bs {M : ℕ} (y : WilsonHypercubic.Site 4 (M + 1)) (ρ : Fin 4) :
    Bool → WilsonHypercubic.Site 4 (M + 1)
  | true => y
  | false => y - ev M ρ

/-- The plaquette of parameters `(s, t, ρ)` through `(a, y)`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`q.1`, `q.2` are projections. -/
private def plq {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1)) (q : Bool × Bool × Fin 4) :
    WilsonHypercubic.Plaq 4 (M + 1) :=
  (pl a q.2.2 q.1, bs y q.2.2 q.2.1)

/-- The parameters: two orientations, two bases, the three directions other than `a`.

DERIVED: `4` is the spacetime dimension. -/
private def dom (a : Fin 4) : Finset (Bool × Bool × Fin 4) :=
  (Finset.univ : Finset Bool) ×ˢ ((Finset.univ : Finset Bool) ×ˢ (Finset.univ.erase a))

/-- DERIVED: `4` is the spacetime dimension; `2` in `q.2.2` is a projection. -/
private theorem mem_dom {a : Fin 4} {q : Bool × Bool × Fin 4} : q ∈ dom a ↔ q.2.2 ≠ a := by
  simp [dom, Finset.mem_product, Finset.mem_erase]

/-- DERIVED: `12 = 2 · 2 · 3`; `4` is the spacetime dimension. -/
private theorem card_dom (a : Fin 4) : (dom a).card = 12 := by
  simp [dom, Finset.card_product, Finset.card_erase_of_mem]

/-- DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` are
projections. -/
private theorem plq_nondiag {M : ℕ} {a : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)}
    {q : Bool × Bool × Fin 4} (hq : q.2.2 ≠ a) : (plq a y q).1.1 ≠ (plq a y q).1.2 := by
  obtain ⟨s, t, ρ⟩ := q
  cases s
  · exact hq
  · exact Ne.symm hq

/-- DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private theorem plq_visit {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (q : Bool × Bool × Fin 4) : (a, y) ∈ (bdT M (plq a y q)).map Prod.fst := by
  obtain ⟨s, t, ρ⟩ := q
  cases s <;> cases t
  · exact (mem_word M ρ a (y - ev M ρ) (a, y)).mpr (Or.inr (Or.inl (by rw [sub_add_cancel])))
  · exact (mem_word M ρ a y (a, y)).mpr (Or.inr (Or.inr (Or.inr rfl)))
  · exact (mem_word M a ρ (y - ev M ρ) (a, y)).mpr
      (Or.inr (Or.inr (Or.inl (by rw [sub_add_cancel]))))
  · exact (mem_word M a ρ y (a, y)).mpr (Or.inl rfl)

/-- **Every non-diagonal plaquette through `(a, y)` has parameters.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` are
projections. -/
private theorem plq_cover {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (p : WilsonHypercubic.Plaq 4 (M + 1)) (hp : p.1.1 ≠ p.1.2)
    (hl : (a, y) ∈ (bdT M p).map Prod.fst) : ∃ q ∈ dom a, plq a y q = p := by
  obtain ⟨⟨μ, ν⟩, x⟩ := p
  have hμν : μ ≠ ν := hp
  rcases (mem_word M μ ν x (a, y)).mp hl with h | h | h | h
  · have h1 : a = μ := congrArg Prod.fst h
    have h2 : y = x := congrArg Prod.snd h
    refine ⟨(true, true, ν), mem_dom.mpr ?_, ?_⟩
    · show ν ≠ a
      rw [h1]
      exact Ne.symm hμν
    · show ((a, ν), y) = ((μ, ν), x)
      rw [h1, h2]
  · have h1 : a = ν := congrArg Prod.fst h
    have h2 : y = x + ev M μ := congrArg Prod.snd h
    refine ⟨(false, false, μ), mem_dom.mpr ?_, ?_⟩
    · show μ ≠ a
      rw [h1]
      exact hμν
    · show ((μ, a), y - ev M μ) = ((μ, ν), x)
      rw [h1, h2, add_sub_cancel_right]
  · have h1 : a = μ := congrArg Prod.fst h
    have h2 : y = x + ev M ν := congrArg Prod.snd h
    refine ⟨(true, false, ν), mem_dom.mpr ?_, ?_⟩
    · show ν ≠ a
      rw [h1]
      exact Ne.symm hμν
    · show ((a, ν), y - ev M ν) = ((μ, ν), x)
      rw [h1, h2, add_sub_cancel_right]
  · have h1 : a = ν := congrArg Prod.fst h
    have h2 : y = x := congrArg Prod.snd h
    refine ⟨(false, true, μ), mem_dom.mpr ?_, ?_⟩
    · show μ ≠ a
      rw [h1]
      exact hμν
    · show ((μ, a), y) = ((μ, ν), x)
      rw [h1, h2]

/-- The left inverse of `plq a y` on its parameters.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` are
projections. -/
private def plqInv {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (p : WilsonHypercubic.Plaq 4 (M + 1)) : Bool × Bool × Fin 4 :=
  (decide (p.1.1 = a), decide (p.2 = y), if p.1.1 = a then p.1.2 else p.1.1)

/-- DERIVED: `1` is the least `M`; `4` is the spacetime dimension; `2` in `q.2.2` is a projection. -/
private theorem plqInv_plq {M : ℕ} (hM : 1 ≤ M) {a : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)}
    {q : Bool × Bool × Fin 4} (hq : q.2.2 ≠ a) : plqInv a y (plq a y q) = q := by
  obtain ⟨s, t, ρ⟩ := q
  have hρ : ρ ≠ a := hq
  have hne : y - ev M ρ ≠ y := sub_ev_ne hM ρ y
  have he : ev M ρ ≠ 0 := ev_ne_zero hM ρ
  cases s <;> cases t <;> simp [plqInv, plq, pl, bs, hρ, hne, he]

/-- **The parametrisation is injective.**

DERIVED: `1` is the least `M`; `4` is the spacetime dimension; `2` in `q.2.2` is a projection. -/
private theorem plq_inj {M : ℕ} (hM : 1 ≤ M) {a : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)}
    {q q' : Bool × Bool × Fin 4} (hq : q.2.2 ≠ a) (hq' : q'.2.2 ≠ a)
    (h : plq a y q = plq a y q') : q = q' :=
  calc q = plqInv a y (plq a y q) := (plqInv_plq hM hq).symm
    _ = plqInv a y (plq a y q') := by rw [h]
    _ = q' := plqInv_plq hM hq'

/-- **At most `12` non-diagonal plaquettes visit a link**: `4` positions in the word, `3` other
directions each.

DERIVED: `12 = 4 · 3`; `4` is the spacetime dimension and the word length; `1` is the successor
writing the extent; `1`, `2` in `p.1.1`, `p.1.2` are projections. -/
theorem card_visit_nondiag_le (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).card ≤ 12 := by
  obtain ⟨a, y⟩ := l
  have hsub : Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
        p.1.1 ≠ p.1.2 ∧ (a, y) ∈ (bdT M p).map Prod.fst)
      ⊆ (dom a).image (plq a y) := by
    intro p hp
    obtain ⟨-, hd, hl⟩ := Finset.mem_filter.mp hp
    obtain ⟨q, hq, hqp⟩ := plq_cover a y p hd hl
    exact Finset.mem_image.mpr ⟨q, hq, hqp⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (dom a).card := Finset.card_image_le
    _ = 12 := card_dom a

#print axioms card_visit_nondiag_le

/-- The pair count is symmetric.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem n2_symm (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1)) : n2 M l m = n2 M m l := by
  unfold n2
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

#print axioms n2_symm

/-! ## 3. The pair count through the parameters -/

/-- **The pair count as a count of parameters.**

DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem n2_eq_card {M : ℕ} (hM : 1 ≤ M) (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (k : WilsonHypercubic.Link 4 (M + 1)) :
    n2 M (a, y) k = ((dom a).filter (fun q => k ∈ (bdT M (plq a y q)).map Prod.fst)).card := by
  unfold n2
  symm
  apply Finset.card_nbij (plq a y)
  · intro q hq
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    have hd : q.2.2 ≠ a := mem_dom.mp hq'.1
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, plq_nondiag hd, plq_visit a y q, hq'.2⟩)
  · intro q₁ hq₁ q₂ hq₂ h
    exact plq_inj hM (mem_dom.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hq₁)).1)
      (mem_dom.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hq₂)).1) h
  · intro p hp
    obtain ⟨-, hd, hl, hk⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨q, hq, hqp⟩ := plq_cover a y p hd hl
    exact ⟨q, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hq, by rw [hqp]; exact hk⟩), hqp⟩

/-- Changing the orientation does not change the links visited.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private theorem mem_plq_orient {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (s t : Bool) (ρ : Fin 4) (k : WilsonHypercubic.Link 4 (M + 1)) :
    k ∈ (bdT M (plq a y (s, t, ρ))).map Prod.fst
      ↔ k ∈ (bdT M (plq a y (true, t, ρ))).map Prod.fst := by
  cases s
  · exact mem_word_swap M a ρ (bs y ρ t) k
  · exact Iff.rfl

/-- The (base, direction) parameters of the plane `(a, ρ)` whose plaquette visits `k`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1`, `2` in
`r.1`, `r.2` are projections. -/
private def tp {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (k : WilsonHypercubic.Link 4 (M + 1)) : Finset (Bool × Fin 4) :=
  ((Finset.univ : Finset Bool) ×ˢ (Finset.univ.erase a)).filter
    (fun r => k ∈ (bdT M (plq a y (true, r.1, r.2))).map Prod.fst)

/-- **Two orientations each**: the parameter count is twice `|tp|`.

DERIVED: `2` is the number of orientations; `4` is the spacetime dimension; `1` is the successor
writing the extent. -/
private theorem card_T_eq {M : ℕ} (a : Fin 4) (y : WilsonHypercubic.Site 4 (M + 1))
    (k : WilsonHypercubic.Link 4 (M + 1)) :
    ((dom a).filter (fun q => k ∈ (bdT M (plq a y q)).map Prod.fst)).card = 2 * (tp a y k).card := by
  have h : (dom a).filter (fun q => k ∈ (bdT M (plq a y q)).map Prod.fst)
      = (Finset.univ : Finset Bool) ×ˢ tp a y k := by
    ext ⟨s, t, ρ⟩
    simp only [dom, tp, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      mem_plq_orient a y s t ρ k, iff_self]
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_bool]

/-- The shifted site `y ± ev ρ`: `+` for `true`, `−` for `false`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
private def nb {M : ℕ} (y : WilsonHypercubic.Site 4 (M + 1)) (ρ : Fin 4) :
    Bool → WilsonHypercubic.Site 4 (M + 1)
  | true => y + ev M ρ
  | false => y - ev M ρ

/-- DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem nb_inj {M : ℕ} (hM : 1 ≤ M) {y : WilsonHypercubic.Site 4 (M + 1)} {ρ σ : Fin 4}
    {t : Bool} (h : nb y ρ t = nb y σ t) : ρ = σ := by
  cases t
  · have h' : y - ev M ρ = y - ev M σ := h
    exact ev_inj hM (sub_right_inj.mp h')
  · have h' : y + ev M ρ = y + ev M σ := h
    exact ev_inj hM (add_left_cancel h')

/-- **A partner in the plane `(a, ρ)`** is a `ρ`-link, or the other `a`-link `(a, y ± ev ρ)`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `1` in `k.1` is
a projection. -/
private theorem mem_plq_true {M : ℕ} {a ρ : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)} {t : Bool}
    {k : WilsonHypercubic.Link 4 (M + 1)} (hk : k ≠ (a, y))
    (h : k ∈ (bdT M (plq a y (true, t, ρ))).map Prod.fst) : k.1 = ρ ∨ k = (a, nb y ρ t) := by
  cases t
  · rcases (mem_word M a ρ (y - ev M ρ) k).mp h with h1 | h1 | h1 | h1
    · exact Or.inr h1
    · exact Or.inl (congrArg Prod.fst h1)
    · exact absurd (by rw [h1, sub_add_cancel]) hk
    · exact Or.inl (congrArg Prod.fst h1)
  · rcases (mem_word M a ρ y k).mp h with h1 | h1 | h1 | h1
    · exact absurd h1 hk
    · exact Or.inl (congrArg Prod.fst h1)
    · exact Or.inr h1
    · exact Or.inl (congrArg Prod.fst h1)

/-- **One plane per base**: a partner visited from the same base in the planes `(a, ρ)` and
`(a, σ)` has `ρ = σ`.

DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem tp_unique {M : ℕ} (hM : 1 ≤ M) {a : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)}
    {k : WilsonHypercubic.Link 4 (M + 1)} (hk : k ≠ (a, y)) {t : Bool} {ρ σ : Fin 4}
    (hρ : ρ ≠ a) (hσ : σ ≠ a)
    (h1 : k ∈ (bdT M (plq a y (true, t, ρ))).map Prod.fst)
    (h2 : k ∈ (bdT M (plq a y (true, t, σ))).map Prod.fst) : ρ = σ := by
  rcases mem_plq_true hk h1 with e1 | e1 <;> rcases mem_plq_true hk h2 with e2 | e2
  · exact e1.symm.trans e2
  · exact absurd (e1.symm.trans (congrArg Prod.fst e2)) hρ
  · exact absurd (e2.symm.trans (congrArg Prod.fst e1)) hσ
  · have e3 : nb y ρ t = nb y σ t := congrArg Prod.snd (e1.symm.trans e2)
    exact nb_inj hM e3

/-- `tp` is injective in the base.

DERIVED: `1` is the least `M`; `4` is the spacetime dimension; `1` in `r.1` is a projection. -/
private theorem tp_fst_inj {M : ℕ} (hM : 1 ≤ M) {a : Fin 4} {y : WilsonHypercubic.Site 4 (M + 1)}
    {k : WilsonHypercubic.Link 4 (M + 1)} (hk : k ≠ (a, y)) {r r' : Bool × Fin 4}
    (hr : r ∈ tp a y k) (hr' : r' ∈ tp a y k) (h : r.1 = r'.1) : r = r' := by
  obtain ⟨t, ρ⟩ := r
  obtain ⟨t', σ⟩ := r'
  have h' : t = t' := h
  have hr1 := Finset.mem_filter.mp hr
  have hr2 := Finset.mem_filter.mp hr'
  have hρ : ρ ≠ a := (Finset.mem_erase.mp (Finset.mem_product.mp hr1.1).2).1
  have hσ : σ ≠ a := (Finset.mem_erase.mp (Finset.mem_product.mp hr2.1).2).1
  rw [← h'] at hr2
  have hρσ : ρ = σ := tp_unique hM hk hρ hσ hr1.2 hr2.2
  rw [h', hρσ]

/-- DERIVED: `2` is the number of bases; `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem card_tp_le_two {M : ℕ} (hM : 1 ≤ M) {a : Fin 4}
    {y : WilsonHypercubic.Site 4 (M + 1)} {k : WilsonHypercubic.Link 4 (M + 1)} (hk : k ≠ (a, y)) :
    (tp a y k).card ≤ 2 := by
  calc (tp a y k).card ≤ (Finset.univ : Finset Bool).card :=
        Finset.card_le_card_of_injOn Prod.fst
          (fun r _ => Finset.mem_coe.mpr (Finset.mem_univ _))
          (fun r hr r' hr' h => tp_fst_inj hM hk (Finset.mem_coe.mp hr) (Finset.mem_coe.mp hr') h)
    _ = 2 := by rw [Finset.card_univ, Fintype.card_bool]

/-- **No double partner off the direction `a`**: `z ∈ {y + ev a, y}` and
`z ∈ {y − ev b + ev a, y − ev b}` are incompatible for `a ≠ b`.

DERIVED: `1` is the least `M`; `4` is the spacetime dimension. -/
private theorem no_double {M : ℕ} (hM : 1 ≤ M) {a b : Fin 4} (hab : a ≠ b)
    {y z : WilsonHypercubic.Site 4 (M + 1)}
    (h1 : z = y + ev M a ∨ z = y) (h2 : z = y - ev M b + ev M a ∨ z = y - ev M b) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have h3 : y = y - ev M b := add_right_cancel (h1.symm.trans h2)
    exact sub_ev_ne hM b y h3.symm
  · have h3 : y + ev M a = y + -ev M b := by
      rw [← sub_eq_add_neg]
      exact h1.symm.trans h2
    have h4 : ev M a = -ev M b := add_left_cancel h3
    exact ev_add_ne_zero hM hab (eq_neg_iff_add_eq_zero.mp h4)
  · have h5 : y = y - ev M b + ev M a := h1.symm.trans h2
    have h3 : y + ev M b = y + ev M a :=
      calc y + ev M b = (y - ev M b + ev M a) + ev M b := by rw [← h5]
        _ = y + ev M a := by abel
    exact hab (ev_inj hM (add_left_cancel h3)).symm
  · exact sub_ev_ne hM b y (h1.symm.trans h2).symm

/-- **A partner off the direction `a` lies in at most one plaquette.**

DERIVED: `1` is the least `M` and the bound; `4` is the spacetime dimension; `1` in `k.1` is a
projection. -/
private theorem card_tp_le_one {M : ℕ} (hM : 1 ≤ M) {a : Fin 4}
    {y : WilsonHypercubic.Site 4 (M + 1)} {k : WilsonHypercubic.Link 4 (M + 1)}
    (hk : k ≠ (a, y)) (hka : k.1 ≠ a) : (tp a y k).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro r hr r' hr'
  obtain ⟨t, ρ⟩ := r
  obtain ⟨t', σ⟩ := r'
  have hr1 := Finset.mem_filter.mp hr
  have hr2 := Finset.mem_filter.mp hr'
  have hkρ : k.1 = ρ := by
    rcases mem_plq_true hk hr1.2 with e | e
    · exact e
    · exact absurd (congrArg Prod.fst e) hka
  have hkσ : k.1 = σ := by
    rcases mem_plq_true hk hr2.2 with e | e
    · exact e
    · exact absurd (congrArg Prod.fst e) hka
  have hρσ : ρ = σ := hkρ.symm.trans hkσ
  have hρa : a ≠ ρ := fun e => hka (hkρ.trans e.symm)
  rw [← hρσ] at hr2
  cases t <;> cases t'
  · rw [hρσ]
  · exfalso
    have hA : k.2 = y + ev M a ∨ k.2 = y := mem_word_off (ρ := ρ) (x := y) hka hr2.2
    have hB : k.2 = y - ev M ρ + ev M a ∨ k.2 = y - ev M ρ :=
      mem_word_off (ρ := ρ) (x := y - ev M ρ) hka hr1.2
    exact no_double hM hρa hA hB
  · exfalso
    have hA : k.2 = y + ev M a ∨ k.2 = y := mem_word_off (ρ := ρ) (x := y) hka hr1.2
    have hB : k.2 = y - ev M ρ + ev M a ∨ k.2 = y - ev M ρ :=
      mem_word_off (ρ := ρ) (x := y - ev M ρ) hka hr2.2
    exact no_double hM hρa hA hB
  · rw [hρσ]

/-- **The pair count is `0`, `2` or `4`.**

DERIVED: `4` is the spacetime dimension and the largest count (two unordered plaquettes, two
orientations each); `2` is one unordered plaquette in its two orientations; `0` is none; `1` is the
least `M` and the successor writing the extent. -/
theorem n2_cases {M : ℕ} (hM : 1 ≤ M) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) :
    n2 M l m = 0 ∨ n2 M l m = 2 ∨ n2 M l m = 4 := by
  obtain ⟨a, y⟩ := l
  have hk : m ≠ (a, y) := Ne.symm hlm
  rw [n2_eq_card hM a y m, card_T_eq a y m]
  have h2 := card_tp_le_two hM hk
  omega

#print axioms n2_cases

/-- The links visited by one plaquette, other than a given one, number at most `3`.

DERIVED: `3 = 4 − 1`: `4` is the word length and the spacetime dimension; `1` is the successor
writing the extent. -/
private theorem card_others_le {M : ℕ} (l : WilsonHypercubic.Link 4 (M + 1))
    (p : WilsonHypercubic.Plaq 4 (M + 1)) (hl : l ∈ (bdT M p).map Prod.fst) :
    ((Finset.univ.erase l).filter (fun m => m ∈ (bdT M p).map Prod.fst)).card ≤ 3 := by
  have hlen : ((bdT M p).map Prod.fst).length = 4 := rfl
  have hsub : (Finset.univ.erase l).filter (fun m => m ∈ (bdT M p).map Prod.fst)
      ⊆ ((bdT M p).map Prod.fst).toFinset.erase l := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hm1).1, List.mem_toFinset.mpr hm2⟩
  have hc := Finset.card_erase_of_mem (List.mem_toFinset.mpr hl)
  have hle := List.toFinset_card_le (l := (bdT M p).map Prod.fst)
  rw [hlen] at hle
  have := Finset.card_le_card hsub
  omega

/-- **Double counting**: `Σ_{a ∈ s} |V ∩ r a| ≤ 3 |V|` when every `p ∈ V` has at most `3` related
`a ∈ s`.

DERIVED: `3` is the per-plaquette bound of `card_others_le`. -/
private theorem sum_card_filter_le {α β : Type} (s : Finset α) (V : Finset β)
    (r : α → β → Prop) [∀ a b, Decidable (r a b)]
    (hb : ∀ p ∈ V, (s.filter (fun a => r a p)).card ≤ 3) :
    ∑ a ∈ s, (V.filter (fun p => r a p)).card ≤ V.card * 3 :=
  calc ∑ a ∈ s, (V.filter (fun p => r a p)).card
      = ∑ p ∈ V, (s.filter (fun a => r a p)).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ ≤ ∑ _p ∈ V, 3 := Finset.sum_le_sum hb
    _ = V.card * 3 := by rw [Finset.sum_const, smul_eq_mul]

/-- **The pair counts of a link sum to at most `36`** (`card_visit_nondiag_le`, double counting).

DERIVED: `36 = 12 · 3`: `12` plaquettes, `3` other links each; `4` is the spacetime dimension; `1`
is the least `M` and the successor writing the extent. -/
theorem sum_n2_le {M : ℕ} (hM : 1 ≤ M) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ m ∈ Finset.univ.erase l, n2 M l m ≤ 36 := by
  have hn2 : ∀ m, n2 M l m
      = ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
            (fun p => m ∈ (bdT M p).map Prod.fst)).card := by
    intro m
    unfold n2
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc, iff_self]
  have hb : ∀ p ∈ Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst),
      ((Finset.univ.erase l).filter (fun m => m ∈ (bdT M p).map Prod.fst)).card ≤ 3 :=
    fun p hp => card_others_le l p (Finset.mem_filter.mp hp).2.2
  have hsum := sum_card_filter_le (Finset.univ.erase l)
    (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
      p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst))
    (fun m p => m ∈ (bdT M p).map Prod.fst) hb
  have hcard := card_visit_nondiag_le M l
  calc ∑ m ∈ Finset.univ.erase l, n2 M l m
      = ∑ m ∈ Finset.univ.erase l, ((Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).filter
            (fun p => m ∈ (bdT M p).map Prod.fst)).card :=
        Finset.sum_congr rfl (fun m _ => hn2 m)
    _ ≤ (Finset.univ.filter (fun p : WilsonHypercubic.Plaq 4 (M + 1) =>
          p.1.1 ≠ p.1.2 ∧ l ∈ (bdT M p).map Prod.fst)).card * 3 := hsum
    _ ≤ 36 := by omega

#print axioms sum_n2_le

/-- **At most `3` partners of a link have pair count `4`**, one per plane through `l`.

DERIVED: `3` is the number of directions other than `l.1`; `4` is the spacetime dimension and the
pair count; `1` is the least `M` and the successor writing the extent. -/
theorem card_n2_four_le {M : ℕ} (hM : 1 ≤ M) (l : WilsonHypercubic.Link 4 (M + 1)) :
    (Finset.univ.filter (fun m : WilsonHypercubic.Link 4 (M + 1) => m ≠ l ∧ n2 M l m = 4)).card
      ≤ 3 := by
  obtain ⟨a, y⟩ := l
  have hsub : Finset.univ.filter (fun m : WilsonHypercubic.Link 4 (M + 1) =>
        m ≠ (a, y) ∧ n2 M (a, y) m = 4)
      ⊆ (Finset.univ.erase a).image
          (fun ρ => ((a, y + ev M ρ) : WilsonHypercubic.Link 4 (M + 1))) := by
    intro m hm
    obtain ⟨-, hk, h4⟩ := Finset.mem_filter.mp hm
    rw [n2_eq_card hM a y m, card_T_eq a y m] at h4
    have hc2 : (tp a y m).card = 2 := by omega
    have hma : m.1 = a := by
      by_contra hne
      have := card_tp_le_one hM hk hne
      omega
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (true, ρ) ∈ tp a y m := by
      by_contra hno
      push_neg at hno
      have hle : (tp a y m).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro r hr r' hr'
        apply tp_fst_inj hM hk hr hr'
        obtain ⟨t, ρ⟩ := r
        obtain ⟨t', σ⟩ := r'
        cases t
        · cases t'
          · rfl
          · exact absurd hr' (hno σ)
        · exact absurd hr (hno ρ)
      omega
    have hρ' := Finset.mem_filter.mp hρ
    have hρa : ρ ≠ a := (Finset.mem_erase.mp (Finset.mem_product.mp hρ'.1).2).1
    rcases mem_plq_true hk hρ'.2 with h1 | h1
    · exact absurd (hma.symm.trans h1) (Ne.symm hρa)
    · exact Finset.mem_image.mpr ⟨ρ, Finset.mem_erase.mpr ⟨hρa, Finset.mem_univ _⟩, h1.symm⟩
  have h3 : (Finset.univ.erase a : Finset (Fin 4)).card = 3 := by
    simp [Finset.card_erase_of_mem]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase a).card := Finset.card_image_le
    _ = 3 := h3

#print axioms card_n2_four_le

end MassGap.PairCount
