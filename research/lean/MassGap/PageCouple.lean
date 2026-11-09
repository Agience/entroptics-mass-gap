import Mathlib
import MassGap.MixCut

/-!
# MassGap.PageCouple — the class of the coupling between two pages: XY for `U(1)`, chiral for `SU(N)`

The open input on the route to `CouplingTower.StrongEnd N` is `MixEqui.MixEquiUp N β`, equivalently
`MixPlane.NoStallOnSegment N β`: as the mixed coupling `t = β_⊥` rises from the decoupled pages (`t = 0`, proved
to vanish, `TwoDVanish.decoupled_vanishes`) to `t = β`, no transition. This module identifies the variable that couples two adjacent
pages and the class of the coupling it carries, as a structural statement about the mixed plaquette of
`AnisoTorus`. It proves no statement about a transition. Declarations are in `MassGap.PageCouple`.

## 1. The mixed holonomy and the page-relative transport (proved)

A page is a `(0,1)` plane at fixed transverse coordinates. A mixed plaquette `((i, j), x)` with `i ∈ {0, 1}` and
`j ∈ {2, 3}` reads a link of page `P` (`A = U(i, x)`), a transverse link (`T' = U(j, x + i)`), a link of the
adjacent page `P' = P + j` backwards (`B = U(i, x + j)`) and a transverse link back (`T = U(j, x)`):
`hol = A T' B⁻¹ T⁻¹` (`mixHol`, `hol_eq_mixHol`).

* `mixHol_gauge`: independent site-local rotations `g` of page `P` and `h` of page `P'` act on the page links as
  `A ↦ g A g⁻¹` (endpoints), on the transverse links as `T ↦ g T h⁻¹`, and conjugate the holonomy by `g(x)`.
* `mixHol_left`: the layer rotation `MixCut.gT` rotates page links only; it left-translates the holonomy. This is
  the mechanism of `MixCut.hol_gT_mixA`, which makes every mixed holonomy Haar at `t = 0`.
* `pageRel a b T y = a(y)⁻¹ T(y) b(y)`: the transverse transport read in page frames `a` (page `P`) and `b`
  (page `P'`). `pageRel_gauge`: it is invariant under the joint rotation `a ↦ g a`, `b ↦ h b`, `T ↦ g T h⁻¹`.
  `pageRel_frame`: a page-global change of frames `a ↦ a c`, `b ↦ b d` (which leaves every page link
  `a(x) a(x')⁻¹` unchanged) acts as `W ↦ c⁻¹ W d`: left and right multiplication, the symmetry `G × G` of a
  principal chiral field.

## 2. Abelian versus non-abelian (proved)

* `transport_comm`, `frame_comm` (any commutative group): `g T h⁻¹ = T (g h⁻¹)` and `c⁻¹ W d = W (c⁻¹ d)`. The
  two page rotations enter only through one difference field, and a page-global choice acts through one
  element; the diagonal choice `c = d` acts trivially (`frame_diag_comm`). For `U(1)` this is one angle per site.
* `frame_not_left`, `frame_not_right` (`SU(2)`): the diagonal page-global choice `c = d = iσ₃` is not a left or a
  right translation by any single element. The page-global symmetry does not reduce to one group.
* `LineUp V`: some page-global pair `(c, d)` brings the transports `V k` at all sites into a commuting family.
  `lineUp_comm`: always, in a commutative group. `lineUp_two`: always, for two sites, in any group.
  `not_lineUp_su2` (CHOSEN configuration `(1, iσ₃, iσ₂)` on three sites): no page-global pair lines the three
  transports up in `SU(2)`. Three is the first count with an obstruction; two always lines up (`lineUp_two`).

## 3. The effective coupling on flat pages (proved identity; regime argued)

`mixHol_flat`: if both pages are flat (page links pure gauge, `A = a(x) a(x')⁻¹`, `B = b(x) b(x')⁻¹`), the mixed
holonomy is `a(x) W(x') W(x)⁻¹ a(x)⁻¹` with `W = pageRel a b T`. `wilsonDensity_flat` (`SU(N)`): the mixed
plaquette's density is `1 − (1/N) Re tr (W(x') W(x)⁻¹)`, the nearest-neighbour action of the principal chiral
field `W` on the page. `xy_flat` (`U(1)`, `W = e^{iθ}`): `Re (W(x') W(x)⁻¹) = cos (θ(x') − θ(x))`, the XY action.
So at `t > 0` on flat pages the pair of adjacent pages couples through a 2D principal chiral model at coupling
`t` for `SU(N)`, and through an XY model for `U(1)`.

The first-order term in `t` of the inter-page coupling, with the pages integrated at `t = 0`, is a constant: every
mixed holonomy is Haar there (`MixCut.meanMix_zero`, proved). The first nonconstant inter-page term needs closed
surfaces of mixed plaquettes; its coefficient is not computed here. Flat pages are the large-`β` in-plane regime:
on a 2D page the plaquette variables are independent and concentrate at `1` as `β` grows (argued from
`TwoDVanish`'s character structure, not proved here), and the defects of flatness are what the chiral field
`W` does not see.

## 4. What this identifies and what remains

The class of the effective 2D model between pages: XY for `U(1)` (Berezinskii–Kosterlitz–Thouless transition,
Fröhlich–Spencer 1981, cited), principal chiral for `SU(N)` (asymptotically free, mass gap at every coupling:
Polyakov's conjecture, open). The remaining statement is unchanged: `MixEqui.MixEquiUp N β`, equivalently
`MixPlane.NoStallOnSegment N β`; the iff `MixEqui.mixEquiUp_iff_noStall` takes `LayerSplit.TwoDCharacter N β` as a
hypothesis, and `TwoDVanish` supplies its consumed conclusion. Through this module it reads: the
anisotropic torus, whose inter-page coupling on flat pages is the `SU(N)` principal chiral action at coupling `t`,
has no transition for `t ∈ [0, β]`, uniformly in the window.

DERIVED (module-wide): `0`, `1` the first page block and the identity; `2` the greatest site count that always lines
up and the dimension of a page; `3` the first site count with an obstruction. CHOSEN: `iσ₃`, `iσ₂` (any
non-commuting pair serves). Cited: Fröhlich–Spencer (BKT), Polyakov (chiral mass gap), in prose only.

## What does not follow

No statement here bounds anything at `t > 0` or excludes a transition, for `U(1)` or `SU(N)`. `not_lineUp_su2`
is an algebraic obstruction for one chosen configuration; it does not show that the `SU(N)` chiral model is
massive, and `lineUp_comm` does not show that the `U(1)` model is massless. `mixHol_flat` is an identity on flat
pages only; the reduction of the page integral to flat pages plus defects, and the coefficient of the first
nonconstant inter-page term, are not built. Polyakov's conjecture is not proved and is not an input of any
theorem here. `MixEqui.MixEquiUp`, `MixPlane.NoStallOnSegment` and `AnisoTorus.AnisoAnalytic` stay open.
-/

namespace MassGap.PageCouple

open MassGap MassGap.RectWilson

/-! ## 1. The mixed holonomy and the page-relative transport -/

section Group

variable {G : Type*} [Group G]

/-- **The mixed holonomy**: a link `A` of page `P`, a transverse link `Tf`, a link `B` of page `P'` backwards,
the transverse link `T` back. No numeral. -/
def mixHol (A Tf B T : G) : G := A * Tf * B⁻¹ * T⁻¹

/-- **Gauge law of the mixed holonomy**: site rotations `g` of page `P`, `h` of page `P'` at the two base points
`x`, `x'` conjugate it by `g x`. No numeral. -/
theorem mixHol_gauge (A Tf B T gx gx' hx hx' : G) :
    mixHol (gx * A * gx'⁻¹) (gx' * Tf * hx'⁻¹) (hx * B * hx'⁻¹) (gx * T * hx⁻¹)
      = gx * mixHol A Tf B T * gx⁻¹ := by
  unfold mixHol; group

/-- **A rotation of page links only left-translates the holonomy** (the mechanism of `MixCut.hol_gT_mixA`).
No numeral. -/
theorem mixHol_left (c A Tf B T : G) : mixHol (c * A) Tf B T = c * mixHol A Tf B T := by
  unfold mixHol; group

/-- **The page-relative transport**: the transverse link read in the page frames `a`, `b`. No numeral. -/
def pageRel {S : Type*} (a b T : S → G) (y : S) : G := (a y)⁻¹ * T y * b y

/-- **Invariance under independent page rotations**. No numeral. -/
theorem pageRel_gauge {S : Type*} (a b T g h : S → G) (y : S) :
    pageRel (fun z => g z * a z) (fun z => h z * b z) (fun z => g z * T z * (h z)⁻¹) y = pageRel a b T y := by
  unfold pageRel; group

/-- **A page-global change of frames leaves page links unchanged**. No numeral. -/
theorem link_frame {S : Type*} (a : S → G) (c : G) (x x' : S) :
    (a x * c) * (a x' * c)⁻¹ = a x * (a x')⁻¹ := by group

/-- **A page-global change of frames acts by left and right multiplication** on the transport. No numeral. -/
theorem pageRel_frame {S : Type*} (a b T : S → G) (c d : G) (y : S) :
    pageRel (fun z => a z * c) (fun z => b z * d) T y = c⁻¹ * pageRel a b T y * d := by
  unfold pageRel; group

/-- **Flat pages**: with pure-gauge page links the mixed holonomy is a conjugate of `W(x') W(x)⁻¹`,
`W = pageRel a b T`. No numeral. -/
theorem mixHol_flat {S : Type*} (a b T : S → G) (x x' : S) :
    mixHol (a x * (a x')⁻¹) (T x') (b x * (b x')⁻¹) (T x)
      = a x * (pageRel a b T x' * (pageRel a b T x)⁻¹) * (a x)⁻¹ := by
  unfold mixHol pageRel; group

/-- **Lining up**: some page-global pair `(c, d)` makes the transports at all sites commute. No numeral. -/
def LineUp {ι : Type*} (V : ι → G) : Prop := ∃ c d : G, ∀ k l, Commute (c * V k * d⁻¹) (c * V l * d⁻¹)

/-- **Two sites always line up**, in any group: `c = 1`, `d = V 0`. DERIVED: `2` the site count; `0` the first. -/
theorem lineUp_two (V : Fin 2 → G) : LineUp V := by
  refine ⟨1, V 0, fun k l => ?_⟩
  have h0 : (1 : G) * V 0 * (V 0)⁻¹ = 1 := by group
  fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, h0]
  · exact Commute.refl _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact Commute.refl _

end Group

/-- **The mixed plaquette of the torus is `mixHol`** of its four links. No numeral. -/
theorem hol_eq_mixHol {L : Fin 4 → ℕ} {N : ℕ} (U : RLink L → SUN.SU N) (i j : Fin 4) (x : RSite L) :
    (sysR L N).hol ((i, j), x) U
      = mixHol (U (i, x)) (U (j, rshift L i x)) (U (i, rshift L j x)) (U (j, x)) := by
  rw [hol_eq]; rfl

/-! ## 2. Abelian: one difference field -/

section Comm

variable {G : Type*} [CommGroup G]

/-- **Abelian page rotations enter through one difference**. No numeral. -/
theorem transport_comm (g T h : G) : g * T * h⁻¹ = T * (g * h⁻¹) := by
  rw [mul_comm g T, mul_assoc]

/-- **An abelian page-global choice acts through one element**. No numeral. -/
theorem frame_comm (c W d : G) : c⁻¹ * W * d = W * (c⁻¹ * d) := by
  rw [mul_comm c⁻¹ W, mul_assoc]

/-- **The diagonal abelian choice acts trivially**. No numeral. -/
theorem frame_diag_comm (c W : G) : c⁻¹ * W * c = W := by
  rw [frame_comm, inv_mul_cancel, mul_one]

/-- **Abelian transports always line up**. No numeral. -/
theorem lineUp_comm {ι : Type*} (V : ι → G) : LineUp V :=
  ⟨1, 1, fun _ _ => Commute.all _ _⟩

end Comm

/-! ## 3. SU(2): a non-commuting pair -/

section SU2

/-- `iσ₃ = diag(i, −i)`. CHOSEN. -/
def sA : SUN.SU 2 :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- `iσ₂ = [[0, 1], [−1, 0]]`. CHOSEN. -/
def sB : SUN.SU 2 :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- **The pair does not commute**: the `(0, 1)` entries of `sA sB` and `sB sA` are `i` and `−i`.
DERIVED: `0`, `1` the entry read. -/
theorem sA_sB_ne : sA * sB ≠ sB * sA := by
  intro h
  have e := congrArg (fun g : SUN.SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) h
  have e' : Complex.I = -Complex.I := by
    simpa [sA, sB, Matrix.mul_apply, Fin.sum_univ_two] using e
  have : (2 : ℂ) * Complex.I = 0 := by linear_combination e'
  simp [Complex.I_ne_zero] at this

theorem not_commute_sA_sB : ¬ Commute sA sB := fun h => sA_sB_ne h.eq

/-- **The diagonal page-global choice is not a left translation**. No numeral beyond `1`, the identity read. -/
theorem frame_not_left : ¬ ∃ e : SUN.SU 2, ∀ W, sA⁻¹ * W * sA = e * W := by
  rintro ⟨e, he⟩
  have h1 := he 1
  have he1 : e = 1 := by
    have : sA⁻¹ * 1 * sA = e * 1 := h1
    rw [mul_one, mul_one, inv_mul_cancel] at this
    exact this.symm
  have h2 := he sB
  rw [he1, one_mul] at h2
  apply sA_sB_ne
  calc sA * sB = sA * (sA⁻¹ * sB * sA) := by rw [h2]
    _ = sB * sA := by group

/-- **The diagonal page-global choice is not a right translation**. No numeral beyond `1`. -/
theorem frame_not_right : ¬ ∃ e : SUN.SU 2, ∀ W, sA⁻¹ * W * sA = W * e := by
  rintro ⟨e, he⟩
  have he1 : e = 1 := by
    have : sA⁻¹ * 1 * sA = 1 * e := he 1
    rw [mul_one, one_mul, inv_mul_cancel] at this
    exact this.symm
  have h2 := he sB
  rw [he1, mul_one] at h2
  apply sA_sB_ne
  calc sA * sB = sA * (sA⁻¹ * sB * sA) := by rw [h2]
    _ = sB * sA := by group

/-- Conjugates commute only if the originals do. No numeral. -/
theorem commute_of_conj {G : Type*} [Group G] {c x y : G} (h : Commute (c * x * c⁻¹) (c * y * c⁻¹)) :
    Commute x y := by
  have e : c * (x * y) * c⁻¹ = c * (y * x) * c⁻¹ := by
    have := h.eq
    calc c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
      _ = c * y * c⁻¹ * (c * x * c⁻¹) := this
      _ = c * (y * x) * c⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel e)

/-- **Three `SU(2)` transports that no page-global pair lines up**: `(1, iσ₃, iσ₂)`. CHOSEN configuration.
DERIVED: `3` the site count; `0`, `1`, `2` the sites. -/
theorem not_lineUp_su2 : ¬ LineUp (![1, sA, sB] : Fin 3 → SUN.SU 2) := by
  rintro ⟨c, d, h⟩
  set X : Fin 3 → SUN.SU 2 := fun k => c * (![1, sA, sB] : Fin 3 → SUN.SU 2) k * d⁻¹ with hX
  have h01 : Commute (X 0) (X 1) := h 0 1
  have h02 : Commute (X 0) (X 2) := h 0 2
  have h12 : Commute (X 1) (X 2) := h 1 2
  have h00 : Commute (X 0) (X 0) := Commute.refl _
  -- `X k (X 0)⁻¹ = c V_k c⁻¹`
  have hA : X 1 * (X 0)⁻¹ = c * sA * c⁻¹ := by
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; group
  have hB : X 2 * (X 0)⁻¹ = c * sB * c⁻¹ := by
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; group
  have hc : Commute (X 1 * (X 0)⁻¹) (X 2 * (X 0)⁻¹) := by
    refine Commute.mul_left ?_ ?_
    · exact Commute.mul_right h12 h01.symm.inv_right
    · exact Commute.mul_right h02.inv_left h00.inv_left.inv_right
  rw [hA, hB] at hc
  exact not_commute_sA_sB (commute_of_conj hc)

end SU2

/-! ## 4. The flat-page coupling: chiral for `SU(N)`, XY for `U(1)` -/

/-- **`SU(N)`: the flat-page mixed density is the principal chiral action** of `W = pageRel a b T`.
No numeral. -/
theorem wilsonDensity_flat {N : ℕ} {S : Type*} (a b T : S → SUN.SU N) (x x' : S) :
    WilsonAction.wilsonDensity (mixHol (a x * (a x')⁻¹) (T x') (b x * (b x')⁻¹) (T x))
      = WilsonAction.wilsonDensity (pageRel a b T x' * (pageRel a b T x)⁻¹) := by
  rw [mixHol_flat, WilsonAction.wilsonDensity_conj]

/-- **`U(1)`: the flat-page mixed coupling is the XY action**: `Re (e^{iθ'} e^{−iθ}) = cos (θ' − θ)`.
No numeral. -/
theorem xy_flat (θ θ' : ℝ) :
    (((Circle.exp θ' * (Circle.exp θ)⁻¹ : Circle) : ℂ)).re = Real.cos (θ' - θ) := by
  rw [← div_eq_mul_inv, ← Circle.exp_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- **`U(1)`: the flat-page transport is one angle per site**, `pageRel` of angle fields is the angle
`τ − α + β'`. No numeral. -/
theorem pageRel_circle {S : Type*} (α β' τ : S → ℝ) (y : S) :
    pageRel (fun z => Circle.exp (α z)) (fun z => Circle.exp (β' z)) (fun z => Circle.exp (τ z)) y
      = Circle.exp (τ y - α y + β' y) := by
  unfold pageRel
  rw [Circle.exp_add, Circle.exp_sub, div_eq_mul_inv, mul_comm (Circle.exp (τ y))]

end MassGap.PageCouple

#print axioms MassGap.PageCouple.mixHol_gauge
#print axioms MassGap.PageCouple.mixHol_left
#print axioms MassGap.PageCouple.pageRel_gauge
#print axioms MassGap.PageCouple.link_frame
#print axioms MassGap.PageCouple.pageRel_frame
#print axioms MassGap.PageCouple.mixHol_flat
#print axioms MassGap.PageCouple.lineUp_two
#print axioms MassGap.PageCouple.hol_eq_mixHol
#print axioms MassGap.PageCouple.transport_comm
#print axioms MassGap.PageCouple.frame_comm
#print axioms MassGap.PageCouple.frame_diag_comm
#print axioms MassGap.PageCouple.lineUp_comm
#print axioms MassGap.PageCouple.sA_sB_ne
#print axioms MassGap.PageCouple.not_commute_sA_sB
#print axioms MassGap.PageCouple.frame_not_left
#print axioms MassGap.PageCouple.frame_not_right
#print axioms MassGap.PageCouple.commute_of_conj
#print axioms MassGap.PageCouple.not_lineUp_su2
#print axioms MassGap.PageCouple.wilsonDensity_flat
#print axioms MassGap.PageCouple.xy_flat
#print axioms MassGap.PageCouple.pageRel_circle
