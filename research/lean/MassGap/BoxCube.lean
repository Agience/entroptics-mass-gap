import Mathlib
import MassGap.ReflectionHalfSpace

/-!
# Cubes of plaquettes in a box

The cluster bound for general local observables (`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball`)
anchors each observable on a touch-connected set of plaquettes containing its halo. In a `ℤ⁴` box the
anchor is the set of plaquettes based in a cube: it contains the halo of every link inside the cube
(`linkHalo_subset_cubePlaq`), it is touch-connected (`reach_cubePlaq`), and its size depends on the
cube's side alone (`card_cubePlaq_le`), not on the box.

Two plaquettes at the same site with a common direction share the link in that direction at the site;
a plaquette `((i, j), x)` shares its second link `(j, x + eᵢ)` with every plaquette based at `x + eᵢ`
that starts in direction `j`. These two moves connect the cube.
-/

namespace MassGap.BoxCube

open MassGap.ReflectionHalfSpace

/-- A link of a box plaquette is in the support of its box word, as an element of the box.
The converse of `ReflectionHalfSpace.mem_ilinks_of_mem_linkSupp_boxBd`.

DERIVED: the `4` is the spacetime dimension carried by `ILink` and `IPlaq`. -/
theorem mem_linkSupp_boxBd_of_mem_ilinks (Λ : Finset MassGap.InfiniteLattice.ILink)
    (q : ↥(iplqAll Λ)) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq)) (hΛ : l ∈ Λ) :
    (⟨l, hΛ⟩ : ↥Λ) ∈ MassGap.StrongCoupling.linkSupp (boxBd Λ) q := by
  classical
  have h := hl
  rw [← boxBd_map_fst Λ q] at h
  obtain ⟨lb, hlb, he⟩ := List.mem_map.mp h
  unfold MassGap.StrongCoupling.linkSupp
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨lb, hlb, Subtype.ext he⟩

#print axioms mem_linkSupp_boxBd_of_mem_ilinks

/-- Every link of a box plaquette lies in the box.

DERIVED: the `4` is the spacetime dimension carried by `ILink` and `IPlaq`. -/
theorem mem_box_of_mem_ilinks (Λ : Finset MassGap.InfiniteLattice.ILink) (q : ↥(iplqAll Λ))
    {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq)) : l ∈ Λ :=
  MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp q.2).1 l hl

#print axioms mem_box_of_mem_ilinks

/-- **Two box plaquettes sharing a link touch** in the box's touch graph.

DERIVED: the `4` is the spacetime dimension carried by `ILink` and `IPlaq`. -/
theorem touch_of_shared (Λ : Finset MassGap.InfiniteLattice.ILink) (q q' : ↥(iplqAll Λ))
    {l : MassGap.InfiniteLattice.ILink}
    (h : l ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq))
    (h' : l ∈ MassGap.GibbsSpec.ilinks (q' : MassGap.GibbsSpec.IPlaq)) :
    MassGap.StrongCoupling.Touch (boxBd Λ) q q' :=
  ⟨⟨l, mem_box_of_mem_ilinks Λ q h⟩, mem_linkSupp_boxBd_of_mem_ilinks Λ q h _,
    mem_linkSupp_boxBd_of_mem_ilinks Λ q' h' _⟩

#print axioms touch_of_shared

/-- A site lies in the cube of side `R` based at `x₀`: `x₀ i ≤ x i ≤ x₀ i + R` on every axis.

DERIVED: the `4` is the spacetime dimension indexing the axes. -/
def InCube (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ) (x : MassGap.GibbsSpec.ISite) : Prop :=
  ∀ i : Fin 4, x₀ i ≤ x i ∧ x i ≤ x₀ i + R

open scoped Classical in
/-- The box plaquettes based in the cube of side `R` at `x₀`.

DERIVED: no numeral. -/
noncomputable def cubePlaq (Λ : Finset MassGap.InfiniteLattice.ILink) (x₀ : MassGap.GibbsSpec.ISite)
    (R : ℕ) : Finset ↥(iplqAll Λ) :=
  Finset.univ.filter (fun q => InCube x₀ R (q : MassGap.GibbsSpec.IPlaq).2)

open scoped Classical in
/-- Membership in `cubePlaq`, unfolded: the plaquette's base site is in the cube.

DERIVED: no numeral. -/
theorem mem_cubePlaq {Λ : Finset MassGap.InfiniteLattice.ILink} {x₀ : MassGap.GibbsSpec.ISite}
    {R : ℕ} {q : ↥(iplqAll Λ)} :
    q ∈ cubePlaq Λ x₀ R ↔ InCube x₀ R (q : MassGap.GibbsSpec.IPlaq).2 := by
  unfold cubePlaq; simp

#print axioms mem_cubePlaq

/-- The first link of `((a, b), x)` is `(a, x)`.

DERIVED: no numeral. -/
theorem head_link_mem (q : MassGap.GibbsSpec.IPlaq) :
    (q.1.1, q.2) ∈ MassGap.GibbsSpec.ilinks q := by
  rw [MassGap.GibbsSpec.ilinks_eq]; simp

#print axioms head_link_mem

/-- The last link of `((a, b), x)` is `(b, x)`.

DERIVED: no numeral. -/
theorem last_link_mem (q : MassGap.GibbsSpec.IPlaq) :
    (q.1.2, q.2) ∈ MassGap.GibbsSpec.ilinks q := by
  rw [MassGap.GibbsSpec.ilinks_eq]; simp

#print axioms last_link_mem

/-- The second link of `((a, b), x)` is `(b, x + e_a)`.

DERIVED: no numeral. -/
theorem second_link_mem (q : MassGap.GibbsSpec.IPlaq) :
    (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2) ∈ MassGap.GibbsSpec.ilinks q := by
  rw [MassGap.GibbsSpec.ilinks_eq]; simp

#print axioms second_link_mem

/-- One step of reach inside a set, from membership and a shared link.

DERIVED: no numeral. -/
theorem reach_single (Λ : Finset MassGap.InfiniteLattice.ILink) {V : Finset ↥(iplqAll Λ)}
    {q q' : ↥(iplqAll Λ)} (hq : q ∈ V) (hq' : q' ∈ V) {l : MassGap.InfiniteLattice.ILink}
    (h : l ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq))
    (h' : l ∈ MassGap.GibbsSpec.ilinks (q' : MassGap.GibbsSpec.IPlaq)) :
    MassGap.StrongCoupling.Reach (boxBd Λ) V q q' :=
  Relation.ReflTransGen.single ⟨hq, hq', touch_of_shared Λ q q' h h'⟩

#print axioms reach_single

/-- The box plaquette `((a, b), x)`, given that it is non-degenerate and in the cube where the box
holds every cube plaquette.

DERIVED: the `4` is the spacetime dimension of the direction indices. -/
def mkPlaq {Λ : Finset MassGap.InfiniteLattice.ILink} {x₀ : MassGap.GibbsSpec.ISite} {R : ℕ}
    (hbox : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 → q ∈ iplqAll Λ)
    (a b : Fin 4) (hab : a ≠ b) (x : MassGap.GibbsSpec.ISite) (hx : InCube x₀ R x) :
    ↥(iplqAll Λ) :=
  ⟨((a, b), x), hbox ((a, b), x) hab hx⟩

/-- **Plaquettes of the cube at one site are connected** inside the cube: two of them with a common
direction share the link in that direction at the site, and two with no common direction are joined
through a plaquette taking one direction from each.

DERIVED: the `4` is the spacetime dimension of the direction indices. -/
theorem reach_same_site {Λ : Finset MassGap.InfiniteLattice.ILink} {x₀ : MassGap.GibbsSpec.ISite}
    {R : ℕ} (hbox : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 → q ∈ iplqAll Λ)
    (q q' : ↥(iplqAll Λ)) (hq : q ∈ cubePlaq Λ x₀ R) (hq' : q' ∈ cubePlaq Λ x₀ R)
    (hs : (q : MassGap.GibbsSpec.IPlaq).2 = (q' : MassGap.GibbsSpec.IPlaq).2) :
    MassGap.StrongCoupling.Reach (boxBd Λ) (cubePlaq Λ x₀ R) q q' := by
  classical
  obtain ⟨⟨⟨a, b⟩, x⟩, hqm⟩ := q
  obtain ⟨⟨⟨c, d⟩, y⟩, hqm'⟩ := q'
  simp only at hs
  have hyx : y = x := hs.symm
  have hab : a ≠ b := (mem_iplqAll.mp hqm).2
  have hx : InCube x₀ R x := mem_cubePlaq.mp hq
  -- a link at `x` in direction `e` is shared by any two plaquettes at `x` using direction `e`
  have hlink : ∀ (e : Fin 4) (r r' : ↥(iplqAll Λ)), r ∈ cubePlaq Λ x₀ R → r' ∈ cubePlaq Λ x₀ R →
      (r : MassGap.GibbsSpec.IPlaq).2 = x → (r' : MassGap.GibbsSpec.IPlaq).2 = x →
      (e = (r : MassGap.GibbsSpec.IPlaq).1.1 ∨ e = (r : MassGap.GibbsSpec.IPlaq).1.2) →
      (e = (r' : MassGap.GibbsSpec.IPlaq).1.1 ∨ e = (r' : MassGap.GibbsSpec.IPlaq).1.2) →
      MassGap.StrongCoupling.Reach (boxBd Λ) (cubePlaq Λ x₀ R) r r' := by
    intro e r r' hr hr' hrx hr'x he he'
    have hm : ∀ s : ↥(iplqAll Λ), (s : MassGap.GibbsSpec.IPlaq).2 = x →
        (e = (s : MassGap.GibbsSpec.IPlaq).1.1 ∨ e = (s : MassGap.GibbsSpec.IPlaq).1.2) →
        (e, x) ∈ MassGap.GibbsSpec.ilinks (s : MassGap.GibbsSpec.IPlaq) := by
      intro s hsx hse
      rcases hse with h | h
      · have := head_link_mem (s : MassGap.GibbsSpec.IPlaq); rw [hsx, ← h] at this; exact this
      · have := last_link_mem (s : MassGap.GibbsSpec.IPlaq); rw [hsx, ← h] at this; exact this
    exact reach_single Λ hr hr' (hm r hrx he) (hm r' hr'x he')
  by_cases hshare : c = a ∨ c = b ∨ d = a ∨ d = b
  · rcases hshare with h | h | h | h
    · exact hlink a _ _ hq hq' rfl hyx (Or.inl rfl) (Or.inl h.symm)
    · exact hlink b _ _ hq hq' rfl hyx (Or.inr rfl) (Or.inl h.symm)
    · exact hlink a _ _ hq hq' rfl hyx (Or.inl rfl) (Or.inr h.symm)
    · exact hlink b _ _ hq hq' rfl hyx (Or.inr rfl) (Or.inr h.symm)
  · push_neg at hshare
    obtain ⟨hca, hcb, -, -⟩ := hshare
    -- through the plaquette `((a, c), x)`
    let m : ↥(iplqAll Λ) := mkPlaq hbox a c (Ne.symm hca) x hx
    have hm : m ∈ cubePlaq Λ x₀ R := mem_cubePlaq.mpr hx
    exact Relation.ReflTransGen.trans
      (hlink a _ m hq hm rfl rfl (Or.inl rfl) (Or.inl rfl))
      (hlink c m _ hm hq' rfl hyx (Or.inr rfl) (Or.inl rfl))

#print axioms reach_same_site

/-- A direction other than `i`.

DERIVED: `0` and `1` are two distinct directions; the `4` is the spacetime dimension. -/
def otherDir (i : Fin 4) : Fin 4 := if i = 0 then 1 else 0

/-- `otherDir i` differs from `i`.

DERIVED: the `4` is the spacetime dimension. -/
theorem otherDir_ne (i : Fin 4) : otherDir i ≠ i := by
  unfold otherDir; split <;> omega

#print axioms otherDir_ne

/-- The coordinate sum of `x - x₀` inside the cube, the induction measure for connectivity.

DERIVED: the `4` is the spacetime dimension indexing the axes. -/
def cubeDepth (x₀ x : MassGap.GibbsSpec.ISite) : ℕ := ∑ i : Fin 4, (x i - x₀ i).toNat

/-- **Every plaquette of the cube is reachable from the cube's base plaquette** inside the cube.
By induction on the coordinate depth of its site: at depth zero the site is `x₀` and
`reach_same_site` applies; otherwise some coordinate exceeds `x₀`'s, one step back along it stays in
the cube, and the plaquette there leaving in that direction shares a link with a plaquette at the
original site.

DERIVED: `0` and `1` are the directions of the base plaquette and one lattice step; the `4` is the
spacetime dimension. -/
theorem reach_cubePlaq_from_base {Λ : Finset MassGap.InfiniteLattice.ILink}
    {x₀ : MassGap.GibbsSpec.ISite} {R : ℕ}
    (hbox : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 → q ∈ iplqAll Λ)
    (hx₀ : InCube x₀ R x₀) :
    ∀ n : ℕ, ∀ q : ↥(iplqAll Λ), q ∈ cubePlaq Λ x₀ R →
      cubeDepth x₀ (q : MassGap.GibbsSpec.IPlaq).2 = n →
      MassGap.StrongCoupling.Reach (boxBd Λ) (cubePlaq Λ x₀ R)
        (mkPlaq hbox 0 1 (by decide) x₀ hx₀) q := by
  classical
  have hbase : mkPlaq hbox 0 1 (by decide) x₀ hx₀ ∈ cubePlaq Λ x₀ R := mem_cubePlaq.mpr hx₀
  intro n
  induction n with
  | zero =>
    intro q hq hd
    have hin := mem_cubePlaq.mp hq
    have hsite : (q : MassGap.GibbsSpec.IPlaq).2 = x₀ := by
      funext i
      have hsum := hd
      unfold cubeDepth at hsum
      have hi : ((q : MassGap.GibbsSpec.IPlaq).2 i - x₀ i).toNat = 0 :=
        (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
      have := (hin i).1
      omega
    exact reach_same_site hbox _ q hbase hq (by rw [hsite]; rfl)
  | succ n ih =>
    intro q hq hd
    have hin := mem_cubePlaq.mp hq
    set x := (q : MassGap.GibbsSpec.IPlaq).2 with hxdef
    -- some coordinate exceeds the base
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, x₀ i < x i := by
      by_contra hcon
      push_neg at hcon
      have : cubeDepth x₀ x = 0 := by
        unfold cubeDepth
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have := hcon j
        omega
      omega
    set y := MassGap.GibbsSpec.iunshift i x with hydef
    have hyi : y i = x i - 1 := by simp [hydef, MassGap.GibbsSpec.iunshift]
    have hyj : ∀ j, j ≠ i → y j = x j := fun j hj => by
      simp [hydef, MassGap.GibbsSpec.iunshift, Function.update_of_ne hj]
    have hy : InCube x₀ R y := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [hyi]; have := hin j; omega
      · rw [hyj j hj]; exact hin j
    have hxy : MassGap.GibbsSpec.ishift i y = x := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [MassGap.GibbsSpec.ishift, hyi]
      · simp [MassGap.GibbsSpec.ishift, Function.update_of_ne hj, hyj j hj]
    have hdepth : cubeDepth x₀ y = n := by
      unfold cubeDepth at hd ⊢
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hd ⊢
      have hrest : ∑ j ∈ Finset.univ.erase i, (y j - x₀ j).toNat
          = ∑ j ∈ Finset.univ.erase i, (x j - x₀ j).toNat :=
        Finset.sum_congr rfl (fun j hj => by rw [hyj j (Finset.ne_of_mem_erase hj)])
      rw [hrest, hyi]
      omega
    let j := otherDir i
    have hji : j ≠ i := otherDir_ne i
    let r : ↥(iplqAll Λ) := mkPlaq hbox i j (Ne.symm hji) y hy
    have hr : r ∈ cubePlaq Λ x₀ R := mem_cubePlaq.mpr hy
    have h1 := ih r hr hdepth
    -- `r` shares `(j, x)` with the plaquette `((j, i), x)` at the original site
    let s : ↥(iplqAll Λ) := mkPlaq hbox j i hji x hin
    have hs : s ∈ cubePlaq Λ x₀ R := mem_cubePlaq.mpr hin
    have hl1 : (j, x) ∈ MassGap.GibbsSpec.ilinks (r : MassGap.GibbsSpec.IPlaq) := by
      have := second_link_mem (r : MassGap.GibbsSpec.IPlaq)
      simpa [r, mkPlaq, hxy] using this
    have hl2 : (j, x) ∈ MassGap.GibbsSpec.ilinks (s : MassGap.GibbsSpec.IPlaq) :=
      head_link_mem (s : MassGap.GibbsSpec.IPlaq)
    exact Relation.ReflTransGen.trans h1
      (Relation.ReflTransGen.trans (reach_single Λ hr hs hl1 hl2)
        (reach_same_site hbox s q hs hq rfl))

#print axioms reach_cubePlaq_from_base

/-- **The cube's plaquettes are touch-connected inside the cube**, from any one of them: every
member reaches the base plaquette and the base reaches every member (`reach_cubePlaq_from_base`,
`StrongCoupling.reach_symm`).

DERIVED: no numeral. -/
theorem reach_cubePlaq {Λ : Finset MassGap.InfiniteLattice.ILink}
    {x₀ : MassGap.GibbsSpec.ISite} {R : ℕ}
    (hbox : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 → q ∈ iplqAll Λ)
    {a : ↥(iplqAll Λ)} (ha : a ∈ cubePlaq Λ x₀ R) :
    ∀ p ∈ cubePlaq Λ x₀ R, MassGap.StrongCoupling.Reach (boxBd Λ) (cubePlaq Λ x₀ R) a p := by
  have hx₀ : InCube x₀ R x₀ := fun i => ⟨le_rfl, by omega⟩
  intro p hp
  exact Relation.ReflTransGen.trans
    (MassGap.StrongCoupling.reach_symm
      (reach_cubePlaq_from_base hbox hx₀ _ a ha rfl))
    (reach_cubePlaq_from_base hbox hx₀ _ p hp rfl)

#print axioms reach_cubePlaq

/-- **The halo of links strictly inside a cube lies in the cube's plaquettes.** A plaquette using a
link sits at that link's site or one step below it on each axis (`ReflectionHalfSpace.ilink_site_coord`),
so a link with every coordinate in `[x₀ i + 1, x₀ i + R]` is used only by plaquettes based in the
cube of side `R` at `x₀`.

DERIVED: the `1` is the one lattice step between a plaquette's base and its farthest link; the `4`
is the spacetime dimension indexing the axes. -/
theorem linkHalo_subset_cubePlaq (Λ : Finset MassGap.InfiniteLattice.ILink)
    (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ) (S : Finset ↥Λ)
    (hS : ∀ l ∈ S, ∀ i : Fin 4,
      x₀ i + 1 ≤ (l : MassGap.InfiniteLattice.ILink).2 i ∧ (l : MassGap.InfiniteLattice.ILink).2 i ≤ x₀ i + R) :
    MassGap.StrongCoupling.linkHalo (boxBd Λ) S ⊆ cubePlaq Λ x₀ R := by
  intro q hq
  obtain ⟨l, hl, hlS⟩ := MassGap.StrongCoupling.mem_linkHalo.mp hq
  have hil := mem_ilinks_of_mem_linkSupp_boxBd Λ q l hl
  refine mem_cubePlaq.mpr (fun i => ?_)
  have hc := ilink_site_coord i (q : MassGap.GibbsSpec.IPlaq) (l : MassGap.InfiniteLattice.ILink) hil
  have hb := hS l hlS i
  omega

#print axioms linkHalo_subset_cubePlaq

open scoped Classical in
/-- **The cube's plaquette count depends only on its side**: at most `16 · (R + 1)⁴`, whatever the box
and wherever the cube sits. The cube's plaquettes inject into direction pairs times cube sites.

DERIVED: `16` is the number of direction pairs `4 · 4`; `R + 1` sites per axis, `1` for the base
site; the exponent `4` is the spacetime dimension. -/
theorem card_cubePlaq_le (Λ : Finset MassGap.InfiniteLattice.ILink) (x₀ : MassGap.GibbsSpec.ISite)
    (R : ℕ) : (cubePlaq Λ x₀ R).card ≤ 16 * (R + 1) ^ 4 := by
  classical
  let T : Finset MassGap.GibbsSpec.IPlaq :=
    (Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ
      Fintype.piFinset (fun i : Fin 4 => Finset.Icc (x₀ i) (x₀ i + R))
  have hmaps : ∀ q ∈ cubePlaq Λ x₀ R, (q : MassGap.GibbsSpec.IPlaq) ∈ T := by
    intro q hq
    have hin := mem_cubePlaq.mp hq
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun i => ?_)⟩
    exact Finset.mem_Icc.mpr (hin i)
  have hle : (cubePlaq Λ x₀ R).card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun q => (q : MassGap.GibbsSpec.IPlaq)) hmaps
      (fun a _ b _ h => Subtype.ext h)
  have hi : ∀ i : Fin 4, (Finset.Icc (x₀ i) (x₀ i + R)).card = R + 1 := by
    intro i; rw [Int.card_Icc]; omega
  have hT : T.card = 16 * (R + 1) ^ 4 := by
    simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_piFinset, hi, Finset.prod_const]
  omega

#print axioms card_cubePlaq_le

/-! ## The box state of two local observables -/

section BoxBridge

variable {N : ℕ}

/-- **The box state's connected correlation of two continuous observables is `wilsonCorrConnObs`**
at the box carrier, each observable read through the splice. `stateFree_eq_expect_boxBd` three times;
the rest is definitional.

DERIVED: the `0` and the `2` are `wilsonDensity`'s range, as `stateFree` takes them. -/
theorem stateFree_connected_eq_wilsonCorrConnObs
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω (f * g)
      - stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f
        * stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω g
      = MassGap.StrongCoupling.wilsonCorrConnObs (Nc := N) (boxBd Λ)
          (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
          (fun u => g (MassGap.GibbsSpec.splice Λ u ω)) β := by
  rw [stateFree_eq_expect_boxBd, stateFree_eq_expect_boxBd, stateFree_eq_expect_boxBd]
  rfl

#print axioms stateFree_connected_eq_wilsonCorrConnObs

open scoped Classical in
/-- The links of `S` that lie in the box, as elements of the box.

DERIVED: no numeral. -/
noncomputable def boxLinks (Λ S : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Λ.attach.filter (fun l => (l : MassGap.InfiniteLattice.ILink) ∈ S)

open scoped Classical in
/-- Membership in `boxLinks`, unfolded.

DERIVED: no numeral. -/
theorem mem_boxLinks {Λ S : Finset MassGap.InfiniteLattice.ILink} {l : ↥Λ} :
    l ∈ boxLinks Λ S ↔ (l : MassGap.InfiniteLattice.ILink) ∈ S := by
  unfold boxLinks; simp

#print axioms mem_boxLinks

/-- **An observable local on `S ⊆ Λ`, read through the splice, is local on the box links of `S`.**
It is continuous in the box configuration (`continuous_splice_left`), and on the links of `S` the
splice follows the box configuration (`GibbsSpec.splice_mem`).

DERIVED: no numeral. -/
theorem localOnLinks_splice (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) {S : Finset MassGap.InfiniteLattice.ILink}
    (hS : S ⊆ Λ) (hf : MassGap.InfiniteLattice.IsLocalOn S (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)) :
    MassGap.StrongCoupling.LocalOnLinks (Nc := N) (boxLinks Λ S)
      (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := by
  refine MassGap.StrongCoupling.localOnLinks_of_continuous
    (f.continuous.comp (continuous_splice_left Λ ω))
    (fun U V hUV => hf (MassGap.GibbsSpec.splice Λ U ω) (MassGap.GibbsSpec.splice Λ V ω)
      (fun l hl => ?_))
  have hlΛ : l ∈ Λ := hS hl
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
  exact hUV ⟨l, hlΛ⟩ (mem_boxLinks.mpr hl)

#print axioms localOnLinks_splice

/-- **A continuous observable read through the splice is bounded by its sup norm.**

DERIVED: no numeral. -/
theorem abs_splice_le (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    |f (MassGap.GibbsSpec.splice Λ u ω)| ≤ ‖f‖ := by
  simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (MassGap.GibbsSpec.splice Λ u ω)

#print axioms abs_splice_le

/-- **`coreConstG` grows with the anchor size `u`**, below the geometric threshold: the prefactor is
`C · Aᵘ · Eᵘ` with `A = 4 (K + 1)² ≥ 1` and `E = e^{4βK} ≥ 1`.

DERIVED: the `4`, `1` and `2` are `corePrefactorG`'s; the `0`s are the sign hypotheses; the `1` in
`< 1` is the geometric threshold. -/
theorem coreConstG_le_of_le {C : ℝ} (hC : 0 ≤ C) {β : ℝ} (hβ : 0 ≤ β) {K : ℕ}
    (hr : MassGap.StrongCoupling.coreRate K β < 1) {u U : ℕ} (h : u ≤ U) :
    MassGap.StrongCoupling.coreConstG C K β u ≤ MassGap.StrongCoupling.coreConstG C K β U := by
  unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : (1 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have hE : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp (by positivity)
  have hd : (0 : ℝ) ≤ (1 - MassGap.StrongCoupling.coreRate K β)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA h) hC)
    (pow_le_pow_right₀ hE h) (by positivity) (mul_nonneg hC (by positivity))

#print axioms coreConstG_le_of_le

/-- **The box cluster bound for two local observables, anchored on cubes.** Given `N ≠ 0`, let `f` be
local on `Sf ⊆ Λ` and `g` on `Sg ⊆ Λ`, disjoint, with the links of `Sf` strictly inside the cube of
side `R` at `x₀` and those of `Sg` strictly inside the one at `y₀`, and the box holding every
non-degenerate plaquette based in either cube. If
the two cubes' base sites are more than `k` apart along an axis `τ` and `32 (R + 1)⁴ ≤ k + 2`, then
at every `0 ≤ β` with `coreRate 64 β < 1`

    |⟨f g⟩ − ⟨f⟩⟨g⟩|_box  ≤  coreConstG (2 ‖f‖ ‖g‖) 64 β U · coreRate 64 β ^ (k + 2 − U),
    U = 32 (R + 1)⁴,

with a right side independent of the box and of the boundary configuration, for every box that
holds both supports and both cubes.

The anchors are the cubes' plaquettes (`linkHalo_subset_cubePlaq`, `reach_cubePlaq`), their bases
are separated by `ReflectionHalfSpace.not_mem_ball_of_axis_gt`, and their sizes are bounded by
`card_cubePlaq_le`; `StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` gives the bound at the
anchors' own size, carried to `U` by `coreConstG_le_of_le` and the rate's bound by one.

DERIVED: `16 * 4` is the box's touch-degree bound (`touchDeg_boxBd_le`); `32 = 2 · 16` is two
cubes of at most `16 (R + 1)⁴` plaquettes (`card_cubePlaq_le`), with `R + 1` sites per axis and the
exponent `4` the dimension; the `2` in `2 ‖f‖ ‖g‖` is `pairTermObs_abs_le`'s two products; the `2` in
`k + 2` is the two base plaquettes; `0` and `1` are the sign hypotheses and the geometric
threshold; the `1` in `x₀ i + 1` keeps the links strictly inside the
cube. -/
theorem stateFree_connected_abs_le_of_cubes (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    {Sf Sg : Finset MassGap.InfiniteLattice.ILink} (hSf : Sf ⊆ Λ) (hSg : Sg ⊆ Λ)
    (hfl : MassGap.InfiniteLattice.IsLocalOn Sf (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (hgl : MassGap.InfiniteLattice.IsLocalOn Sg (g : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (hdis : Disjoint Sf Sg) {x₀ y₀ : MassGap.GibbsSpec.ISite} {R : ℕ}
    (hcf : ∀ l ∈ Sf, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R)
    (hcg : ∀ l ∈ Sg, ∀ i : Fin 4, y₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ y₀ i + R)
    (hboxf : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube x₀ R q.2 → q ∈ iplqAll Λ)
    (hboxg : ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → InCube y₀ R q.2 → q ∈ iplqAll Λ)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) (τ : Fin 4) (k : ℕ)
    (hk : k < (y₀ τ - x₀ τ).natAbs) (hu : 32 * (R + 1) ^ 4 ≤ k + 2) :
    |stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω (f * g)
      - stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f
        * stateFree MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω g|
      ≤ MassGap.StrongCoupling.coreConstG (2 * (‖f‖ * ‖g‖)) (16 * 4) β (32 * (R + 1) ^ 4)
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k + 2 - 32 * (R + 1) ^ 4) := by
  classical
  rw [stateFree_connected_eq_wilsonCorrConnObs]
  have hx₀ : InCube x₀ R x₀ := fun i => ⟨le_rfl, by omega⟩
  have hy₀ : InCube y₀ R y₀ := fun i => ⟨le_rfl, by omega⟩
  let a : ↥(iplqAll Λ) := mkPlaq hboxf 0 1 (by decide) x₀ hx₀
  let b : ↥(iplqAll Λ) := mkPlaq hboxg 0 1 (by decide) y₀ hy₀
  have ha : a ∈ cubePlaq Λ x₀ R := mem_cubePlaq.mpr hx₀
  have hb : b ∈ cubePlaq Λ y₀ R := mem_cubePlaq.mpr hy₀
  have hab : Disjoint (boxLinks Λ Sf) (boxLinks Λ Sg) := by
    rw [Finset.disjoint_left]
    intro l hl hl'
    exact Finset.disjoint_left.mp hdis (mem_boxLinks.mp hl) (mem_boxLinks.mp hl')
  have hAo := linkHalo_subset_cubePlaq Λ x₀ R (boxLinks Λ Sf)
    (fun l hl i => hcf l (mem_boxLinks.mp hl) i)
  have hBo := linkHalo_subset_cubePlaq Λ y₀ R (boxLinks Λ Sg)
    (fun l hl i => hcg l (mem_boxLinks.mp hl) i)
  have hkb : b ∉ MassGap.StrongCoupling.ball (boxBd Λ) a k :=
    not_mem_ball_of_axis_gt Λ τ a b k hk
  have hcard : (cubePlaq Λ x₀ R ∪ cubePlaq Λ y₀ R).card ≤ 32 * (R + 1) ^ 4 := by
    have h1 := card_cubePlaq_le Λ x₀ R
    have h2 := card_cubePlaq_le Λ y₀ R
    have h3 := Finset.card_union_le (cubePlaq Λ x₀ R) (cubePlaq Λ y₀ R)
    omega
  have hbase := MassGap.StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball hN (boxBd Λ) hab
    (localOnLinks_splice Λ ω f hSf hfl) (localOnLinks_splice Λ ω g hSg hgl)
    (abs_splice_le Λ ω f) (abs_splice_le Λ ω g) hAo hBo ha hb
    (reach_cubePlaq hboxf ha) (reach_cubePlaq hboxg hb) hβ (16 * 4) (touchDeg_boxBd_le Λ) hr k hkb
    (le_trans hcard hu)
  refine le_trans hbase ?_
  have hC : (0 : ℝ) ≤ 2 * (‖f‖ * ‖g‖) := by positivity
  have hr0 : 0 ≤ MassGap.StrongCoupling.coreRate (16 * 4) β :=
    MassGap.StrongCoupling.coreRate_nonneg _ hβ
  have hCC := coreConstG_le_of_le hC hβ hr hcard
  have hpow := MassGap.StrongCoupling.pow_le_pow_of_le_one_asm hr0 hr.le
    (Nat.sub_le_sub_left hcard (k + 2))
  have hCK : (0 : ℝ) ≤ MassGap.StrongCoupling.coreConstG (2 * (‖f‖ * ‖g‖)) (16 * 4) β
      (32 * (R + 1) ^ 4) := by
    unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - MassGap.StrongCoupling.coreRate (16 * 4) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)) this.le
  exact mul_le_mul hCC hpow (pow_nonneg hr0 _) hCK

#print axioms stateFree_connected_abs_le_of_cubes

end BoxBridge

end MassGap.BoxCube
