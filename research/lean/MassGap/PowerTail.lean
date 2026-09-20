import Mathlib
import MassGap.ContactFloor
import MassGap.WeakArm

/-!
# MassGap.PowerTail — the zero-coupling endpoint, and two things that cannot reach `[b, ∞)`

`ContactFloor.contact_relative_unconditional` proves the contact-relative quartic law

    ρ_N(β, d) ≤ C · ρ_N(β, 0) / circLag(d)⁴      (circLag d ≥ 1, every aperture)

on a derived interval `[0, b]`. `ShareEnvelope.substrate_of_contact_relative_decay` consumes the same
law at EVERY coupling. What is open is `[b, ∞)`. This file measures the two objects a reader is most
likely to reach for there, and proves one new fact about the other end of the line.

## The new fact: at zero coupling the correlation is a pure contact term

`corrClay_at_zero_coupling` — `ρ_0(d) = 0` at every lag `d ≠ 0` and every extent `≥ 2`. At `β = 0`
the state is product Haar; the base plaquette and the lag plaquette read DISJOINT link sets, because
the lag displaces along direction `2` and neither plaquette's boundary word leaves the `(0,1)` plane;
so the joint average factorizes and the connected part is zero.

The proof is `ContactFloor.integral_hol_clay`'s argument with a second plaquette present. The handle
is the direction-`1` link at the LAG plaquette's own base site: it is the last letter of that
plaquette's word, so translating it right-multiplies that holonomy, and it is none of the base
plaquette's four links, so that holonomy does not move. Averaging the handle over the group and
swapping the order of integration sends the lag plaquette's holonomy through Haar and leaves the base
plaquette alone — `integral_prod_hol_factor`. No independence lemma for product measures is used; the
content is the single-link left-invariance `ContactFloor.linkTranslate_measurePreserving` already
carries, and `PlaqVariance.corrClay_zero_pos_at_zero_coupling` keeps the statement from being the
whole function vanishing (`contact_value_pos_at_zero_coupling`).

Consequences: `wilsonCorrAt_at_zero_coupling` puts it on the object the substrate read consumes, at
every aperture including `N = 0`, whose only lag has circle distance `0` and is therefore outside the
hypothesis rather than an exception to it; and `contact_relative_at_zero_coupling` reads it as the
target law holding at `β = 0` WITH `C = 0` — the strongest constant there is.

## The Haar comparison has no reverse, at any rate

`ContactFloor.wilsonCorrConn_self_ge_haar` bounds the coupled variance BELOW by `e^{−2β·touch}` times
the Haar one. An upper bound of the same shape at the lag, `ρ_β(d) ≤ K(β)·ρ_0(d)`, would turn the
endpoint above into a bound at every coupling.

`haar_comparison_forces_vanishing` — for ANY multiplier `K` depending on the aperture, the coupling
and the lag, however fast it grows in any of them, such a comparison forces `ρ_β(d) ≤ 0` at every
aperture, every coupling and every lag with circle distance at least one. The right-hand side is a
multiple of zero.

`substrate_of_haar_comparison` — and it then yields `∃ B, ∀ N β, d2At N β ≤ B` outright, through
`ShareEnvelope.substrate_of_contact_relative_decay` at `C = 0`, `m₀ = 1`. So a reversed comparison is
not a step towards the open statement: it is strictly stronger than it, and it additionally asserts
that the connected plaquette correlation is a contact term at every coupling. Either no reversed
comparison exists at any rate, or the correlation vanishes off contact everywhere; there is no third
case, and neither branch is a route.

## The floor route does not survive `b → ∞`

`StrongArm.contact_relative_on_strong_arm` reaches a RATIO by dividing an ABSOLUTE bound by a floor
under the contact value, and that floor is `e^{−128b}·δ₀` (`contactFloor_explicit`, the same proof as
`ContactFloor.contactFloor_holds` with the `b`-dependence written out rather than existentially
hidden). Two measurements:

* `contactFloor_below_every_level` — the floor family's infimum over cuts is zero.
* `floor_route_constant_unbounded` — for any fixed positive numerator `A` and any assignment `C` of a
  constant to a cut that the route's own inequality `A ≤ C(b)·e^{−128b}·δ₀` certifies, `C` is
  unbounded. `floor_route_nonvacuous` exhibits the witness, so this is not an implication out of an
  empty hypothesis.

The numerator in the actual route is `coreConst(16·4, b)·S`, which `StrongArm.coreConst_mono_beta`
makes monotone increasing in `b`, so holding it fixed at a positive constant gives the route the
benefit of the doubt and the constant still diverges at least like `e^{128b}`. Enlarging the proved
interval therefore does not approach the half-line. This is a statement about the ROUTE — divide an
absolute bound by a floor — and it is the arithmetic behind `StrongArm.ContactFloor`'s own note that
any argument for `[b, ∞)` must never bound `ρ(0)` below.

## What is NOT claimed

Nothing here says the quartic law fails on `[b, ∞)`; nothing in the tree says that. Nothing here
produces a power tail at large coupling. `corrClay_at_zero_coupling` is a fact about `β = 0` alone and
is silent at every other coupling: it is the endpoint that shows the strong arm is a statement about
how fast the correlation TURNS ON, and it is the object that makes the one-directionality of the Haar
comparison a theorem rather than a remark.

DERIVED: `128` is `2·16·4` carried in from `ContactFloor`; `4` is the problem's dimension, `3` is
`SU(3)`, the directions `0, 1` span the plaquette's plane and `2` is the lag axis transverse to it,
all fixed by `WilsonBridge.corrClay`. The extent `m + 2` is where a single periodic step moves a site,
which is the same threshold `ContactFloor.shift_ne` runs into. No numeral here is a magnitude.
-/
namespace MassGap.PowerTail

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MassGap.PlaqVariance MassGap.ContactFloor
open MeasureTheory

/-! ### The two plaquettes `corrClay` reads -/

/-- The plaquette `corrClay` reads at lag `lag`: the `(0,1)` plane, displaced `lag` steps along
direction `2`. `clayPlaq` is its `lag = 0` instance.

DERIVED: every index here is `corrClay`'s own, not a choice of this definition. `4` is the lattice
dimension `WilsonBridge.corrClay` is built at; `(0,1)` is the plane its plaquette spans and `2` the
axis its lag runs along, both read off `WilsonBridge.clayPlaq`, whose `lag = 0` case this generalises.
Changing any of them would describe a different correlation, not a differently-tuned one. -/
def lagPlaq (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Plaq 4 n :=
  ((0, 1), siteAtHyper 2 lag)

#print axioms lagPlaq

/-- `corrClay` IS the connected correlation of those two plaquettes — by `rfl`, checked here rather
than read off a docstring. -/
theorem corrClay_eq_conn (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrClay n β lag
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
          (clayPlaq n) β (lagPlaq n lag) := rfl

#print axioms corrClay_eq_conn

/-- The boundary word of a hypercubic plaquette, spelled out as an ordered product. -/
theorem hol_plaq_eq {n : ℕ} [NeZero n] (μ ν : Fin 4) (x : MassGap.WilsonHypercubic.Site 4 n)
    (U : MassGap.WilsonHypercubic.Link 4 n → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := n)) ((μ, ν), x) U
      = U (μ, x) * (U (ν, MassGap.WilsonHypercubic.shift μ x)
          * ((U (μ, MassGap.WilsonHypercubic.shift ν x))⁻¹ * (U (ν, x))⁻¹)) := by
  simp [wilsonHol, MassGap.WilsonHypercubic.bd]

#print axioms hol_plaq_eq

/-! ### Coordinates: the two plaquettes share no link when the lag is nonzero -/

theorem shift_apply_of_ne {n : ℕ} [NeZero n] (μ : Fin 4)
    (x : MassGap.WilsonHypercubic.Site 4 n) {j : Fin 4} (h : j ≠ μ) :
    MassGap.WilsonHypercubic.shift μ x j = x j := by
  simp [MassGap.WilsonHypercubic.shift, Function.update_of_ne h]

theorem shift_apply_self {n : ℕ} [NeZero n] (μ : Fin 4)
    (x : MassGap.WilsonHypercubic.Site 4 n) :
    MassGap.WilsonHypercubic.shift μ x μ = x μ + 1 := by
  simp [MassGap.WilsonHypercubic.shift]

theorem siteAtHyper_apply_self {n : ℕ} [NeZero n] (μ : Fin 4) (lag : Fin n) :
    siteAtHyper μ lag μ = lag := by
  simp [siteAtHyper]

theorem siteAtHyper_apply_of_ne {n : ℕ} [NeZero n] (μ : Fin 4) (lag : Fin n) {j : Fin 4}
    (h : j ≠ μ) : siteAtHyper μ lag j = 0 := by
  simp [siteAtHyper, Function.update_of_ne h]

#print axioms shift_apply_of_ne
#print axioms shift_apply_self
#print axioms siteAtHyper_apply_self
#print axioms siteAtHyper_apply_of_ne

/-- **THE TRANSLATION HANDLE.** The direction-`1` link at the LAG plaquette's own base site. It is
the last letter of that plaquette's boundary word, carried with orientation `false`, and — when the
lag is nonzero — it belongs to no link of the base plaquette.

DERIVED: `1` is forced, not picked. `WilsonHypercubic.bd` writes a plaquette's boundary word as
`[(mu,x,true), (nu,shift mu x,true), (mu,shift nu x,false), (nu,x,false)]`, so for the `(0,1)` plane
the LAST letter is the direction-`1` link at the base site — and the last letter is the one a right
translation acts on. `4` is the lattice dimension and `2` the lag axis, both inherited from `lagPlaq`.
The whole argument needs exactly this link and no other. -/
def handle (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Link 4 n :=
  ((1 : Fin 4), siteAtHyper 2 lag)

#print axioms handle

/-! ### The handle moves the lag plaquette and leaves the base plaquette alone -/

/-- **The handle right-multiplies the LAG plaquette's holonomy.** The three other letters of its
boundary word are different links: two by direction, one because a single periodic step moves the
site, which is where extent at least two is used. -/
theorem hol_linkTranslate_lag (m : ℕ) (lag : Fin (m + 2)) (g : MassGap.SUN.SU 3)
    (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (lagPlaq (m + 2) lag)
        (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U)
      = wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (lagPlaq (m + 2) lag) U
        * g := by
  classical
  have hd : (0 : Fin 4) ≠ 1 := by decide
  have hs0 : siteAtHyper (2 : Fin 4) lag (0 : Fin 4) = 0 :=
    siteAtHyper_apply_of_ne _ _ (by decide)
  have hshift0 : MassGap.WilsonHypercubic.shift (0 : Fin 4) (siteAtHyper (2 : Fin 4) lag)
      ≠ siteAtHyper (2 : Fin 4) lag := by
    intro h
    have h0 := congrFun h (0 : Fin 4)
    rw [shift_apply_self, hs0] at h0
    have h1 : ((0 : Fin (m + 2)) + 1) = 0 := h0
    have h2 := congrArg Fin.val h1
    simp at h2
  have h1 : (((0 : Fin 4), siteAtHyper (2 : Fin 4) lag) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hd (congrArg Prod.fst h)
  have h2 : (((1 : Fin 4),
      MassGap.WilsonHypercubic.shift (0 : Fin 4) (siteAtHyper (2 : Fin 4) lag)) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hshift0 (congrArg Prod.snd h)
  have h3 : (((0 : Fin 4),
      MassGap.WilsonHypercubic.shift (1 : Fin 4) (siteAtHyper (2 : Fin 4) lag)) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hd (congrArg Prod.fst h)
  show wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
      (((0 : Fin 4), (1 : Fin 4)), siteAtHyper (2 : Fin 4) lag)
      (linkTranslate (Nc := 3) g⁻¹ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) U)
    = wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
        (((0 : Fin 4), (1 : Fin 4)), siteAtHyper (2 : Fin 4) lag) U * g
  rw [hol_plaq_eq, hol_plaq_eq,
    linkTranslate_of_ne (Nc := 3) _ _ _ h1,
    linkTranslate_of_ne (Nc := 3) _ _ _ h2,
    linkTranslate_of_ne (Nc := 3) _ _ _ h3,
    linkTranslate_self (Nc := 3)]
  group

#print axioms hol_linkTranslate_lag

/-- **The handle leaves the BASE plaquette's holonomy alone**, when the lag is nonzero. Each of the
four letters of the base plaquette's word differs from the handle: two by direction, and two because
their sites carry coordinate `2` equal to `0` while the handle's site carries `lag`. This is the one
place the lag being nonzero is used, and it is the whole geometric content: at lag zero the two
plaquettes coincide and no handle of this kind exists. -/
theorem hol_linkTranslate_clay_fixed (m : ℕ) {lag : Fin (m + 2)} (hlag : lag ≠ 0)
    (g : MassGap.SUN.SU 3) (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2))
        (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U)
      = wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U := by
  classical
  have hd : (0 : Fin 4) ≠ 1 := by decide
  have hlagc : siteAtHyper (2 : Fin 4) lag (2 : Fin 4) = lag := siteAtHyper_apply_self _ _
  have hsite : ∀ x : MassGap.WilsonHypercubic.Site 4 (m + 2), x (2 : Fin 4) = 0 →
      x ≠ siteAtHyper (2 : Fin 4) lag := by
    intro x hx h
    apply hlag
    have hc := congrFun h (2 : Fin 4)
    rw [hx, hlagc] at hc
    exact hc.symm
  have hz2 : (fun _ => (0 : Fin (m + 2))) (2 : Fin 4) = 0 := rfl
  have hsz0 : MassGap.WilsonHypercubic.shift (0 : Fin 4) (fun _ => (0 : Fin (m + 2)))
      (2 : Fin 4) = 0 := shift_apply_of_ne _ _ (by decide : (2 : Fin 4) ≠ 0)
  have k1 : (((0 : Fin 4), (fun _ => (0 : Fin (m + 2)))) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hd (congrArg Prod.fst h)
  have k2 : (((1 : Fin 4),
      MassGap.WilsonHypercubic.shift (0 : Fin 4) (fun _ => (0 : Fin (m + 2)))) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hsite _ hsz0 (congrArg Prod.snd h)
  have k3 : (((0 : Fin 4),
      MassGap.WilsonHypercubic.shift (1 : Fin 4) (fun _ => (0 : Fin (m + 2)))) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hd (congrArg Prod.fst h)
  have k4 : (((1 : Fin 4), (fun _ => (0 : Fin (m + 2)))) :
      MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) := by
    intro h; exact hsite _ hz2 (congrArg Prod.snd h)
  show wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
      (((0 : Fin 4), (1 : Fin 4)), (fun _ => (0 : Fin (m + 2))))
      (linkTranslate (Nc := 3) g⁻¹ ((1 : Fin 4), siteAtHyper (2 : Fin 4) lag) U)
    = wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
        (((0 : Fin 4), (1 : Fin 4)), (fun _ => (0 : Fin (m + 2)))) U
  rw [hol_plaq_eq, hol_plaq_eq,
    linkTranslate_of_ne (Nc := 3) _ _ _ k1,
    linkTranslate_of_ne (Nc := 3) _ _ _ k2,
    linkTranslate_of_ne (Nc := 3) _ _ _ k3,
    linkTranslate_of_ne (Nc := 3) _ _ _ k4]

#print axioms hol_linkTranslate_clay_fixed

/-! ### The factorization at zero coupling

The argument of `ContactFloor.integral_hol_clay`, run with a SECOND plaquette present. The handle
belongs to the lag plaquette and to nothing the base plaquette reads, so averaging over it sends the
lag plaquette's holonomy through Haar while the base plaquette's is untouched — and the joint
integral factorizes. No independence lemma for product measures is needed: the whole content is the
single-link left-invariance that `linkTranslate_measurePreserving` already carries. -/

/-- **THE JOINT INTEGRAL FACTORIZES AT ZERO COUPLING**, for every nonzero lag:

    ∫ f(hol_base) · h(hol_lag) dπ  =  (∫ f(hol_base) dπ) · (∫ h dHaar)

`π` is product Haar over the links — which IS the `β = 0` Gibbs measure
(`WilsonReal.wilsonSystem_expect_at_zero`). -/
theorem integral_prod_hol_factor (m : ℕ) {lag : Fin (m + 2)} (hlag : lag ≠ 0)
    (f h : MassGap.SUN.SU 3 → ℝ) (hf : Measurable f) (hh : Measurable h)
    (Mf Mh : ℝ) (hfb : ∀ g, |f g| ≤ Mf) (hhb : ∀ g, |h g| ≤ Mh) :
    (∫ U, f (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U)
          * h (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
              (lagPlaq (m + 2) lag) U)
        ∂(Measure.pi fun _ : MassGap.WilsonHypercubic.Link 4 (m + 2) =>
            probHaar (MassGap.SUN.SU 3)))
      = (∫ U, f (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
              (clayPlaq (m + 2)) U)
          ∂(Measure.pi fun _ : MassGap.WilsonHypercubic.Link 4 (m + 2) =>
              probHaar (MassGap.SUN.SU 3)))
        * ∫ g, h g ∂(probHaar (MassGap.SUN.SU 3)) := by
  classical
  set π : Measure (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :=
    Measure.pi (fun _ => probHaar (MassGap.SUN.SU 3)) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  set hol0 : (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) → MassGap.SUN.SU 3 :=
    fun U => wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
    with hhol0
  set hol1 : (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) → MassGap.SUN.SU 3 :=
    fun U => wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
      (lagPlaq (m + 2) lag) U with hhol1
  have hc0 : Continuous hol0 := MassGap.PlaqVariance.continuous_wilsonHol _ _
  have hc1 : Continuous hol1 := MassGap.PlaqVariance.continuous_wilsonHol _ _
  have hMf : (0 : ℝ) ≤ Mf := le_trans (abs_nonneg _) (hfb 1)
  have hMh : (0 : ℝ) ≤ Mh := le_trans (abs_nonneg _) (hhb 1)
  -- translating the handle moves only the lag plaquette
  have hshift : ∀ g : MassGap.SUN.SU 3,
      (∫ U, f (hol0 U) * h (hol1 U * g) ∂π) = ∫ U, f (hol0 U) * h (hol1 U) ∂π := by
    intro g
    have hstep := integral_comp_linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag)
      (fun U => f (hol0 U) * h (hol1 U))
    calc (∫ U, f (hol0 U) * h (hol1 U * g) ∂π)
        = ∫ U, f (hol0 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U))
              * h (hol1 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U)) ∂π := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
          have e0 : hol0 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U) = hol0 U :=
            hol_linkTranslate_clay_fixed m hlag g U
          have e1 : hol1 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U) = hol1 U * g :=
            hol_linkTranslate_lag m lag g U
          show f (hol0 U) * h (hol1 U * g)
            = f (hol0 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U))
              * h (hol1 (linkTranslate (Nc := 3) g⁻¹ (handle (m + 2) lag) U))
          rw [e0, e1]
      _ = ∫ U, f (hol0 U) * h (hol1 U) ∂π := hstep
  have hmeas : Measurable (Function.uncurry
      (fun (g : MassGap.SUN.SU 3)
        (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) =>
          f (hol0 U) * h (hol1 U * g))) := by
    show Measurable fun z : MassGap.SUN.SU 3
      × (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) =>
        f (hol0 z.2) * h (hol1 z.2 * z.1)
    exact (hf.comp (hc0.comp continuous_snd).measurable).mul
      (hh.comp (Continuous.measurable ((hc1.comp continuous_snd).mul continuous_fst)))
  have hintg : Integrable (Function.uncurry
      (fun (g : MassGap.SUN.SU 3)
        (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) =>
          f (hol0 U) * h (hol1 U * g)))
      ((probHaar (MassGap.SUN.SU 3)).prod π) := by
    refine integrable_of_bounded hmeas (Mf * Mh) (fun z => ?_)
    show |f (hol0 z.2) * h (hol1 z.2 * z.1)| ≤ Mf * Mh
    rw [abs_mul]
    exact mul_le_mul (hfb _) (hhb _) (abs_nonneg _) hMf
  have hswap := MeasureTheory.integral_integral_swap hintg
  have hinner : ∀ U, (∫ g, f (hol0 U) * h (hol1 U * g) ∂(probHaar (MassGap.SUN.SU 3)))
      = f (hol0 U) * ∫ g, h g ∂(probHaar (MassGap.SUN.SU 3)) := by
    intro U
    rw [integral_const_mul]
    exact congrArg _ (MeasureTheory.integral_mul_left_eq_self h (hol1 U))
  calc (∫ U, f (hol0 U) * h (hol1 U) ∂π)
      = ∫ _g : MassGap.SUN.SU 3, (∫ U, f (hol0 U) * h (hol1 U) ∂π)
          ∂(probHaar (MassGap.SUN.SU 3)) :=
        (integral_const_prob (probHaar (MassGap.SUN.SU 3)) _).symm
    _ = ∫ g, (∫ U, f (hol0 U) * h (hol1 U * g) ∂π) ∂(probHaar (MassGap.SUN.SU 3)) := by
        simp only [hshift]
    _ = ∫ U, (∫ g, f (hol0 U) * h (hol1 U * g) ∂(probHaar (MassGap.SUN.SU 3))) ∂π := hswap
    _ = ∫ U, f (hol0 U) * (∫ g, h g ∂(probHaar (MassGap.SUN.SU 3))) ∂π := by simp only [hinner]
    _ = (∫ U, f (hol0 U) ∂π) * ∫ g, h g ∂(probHaar (MassGap.SUN.SU 3)) := integral_mul_const _ _

#print axioms integral_prod_hol_factor

/-! ### The zero-coupling endpoint -/

/-- **AT ZERO COUPLING THE CONNECTED CORRELATION VANISHES AT EVERY NONZERO LAG.**

    ρ_0(d) = 0   for every `d ≠ 0`, at every extent `≥ 2`.

At `β = 0` the state is product Haar, and the two plaquettes read disjoint link sets, so the joint
average factorizes (`integral_prod_hol_factor`) and the connected part — which is exactly the joint
minus the product of the marginals — is zero. The correlation at zero coupling is a pure CONTACT
term. -/
theorem corrClay_at_zero_coupling (m : ℕ) {lag : Fin (m + 2)} (hlag : lag ≠ 0) :
    corrClay (m + 2) 0 lag = 0 := by
  classical
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  have hbound : ∀ g : MassGap.SUN.SU 3, |wilsonDensity (N := 3) g| ≤ 2 := fun g =>
    abs_le.mpr ⟨by linarith [wilsonDensity_nonneg h3 g], wilsonDensity_le_two h3 g⟩
  have hlagint : (∫ U, wilsonPlaqObs (N := 3)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (lagPlaq (m + 2) lag) U
        ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
            (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3))))
      = ∫ g, wilsonDensity (N := 3) g ∂(probHaar (MassGap.SUN.SU 3)) := by
    have hfac := integral_prod_hol_factor m hlag (fun _ => (1 : ℝ)) (wilsonDensity (N := 3))
      measurable_const measurable_wilsonDensity 1 2 (fun g => by norm_num) hbound
    have hraw : (∫ U, wilsonDensity (N := 3)
          (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
            (lagPlaq (m + 2) lag) U)
          ∂(Measure.pi fun _ : MassGap.WilsonHypercubic.Link 4 (m + 2) =>
              probHaar (MassGap.SUN.SU 3)))
        = ∫ g, wilsonDensity (N := 3) g ∂(probHaar (MassGap.SUN.SU 3)) := by
      simpa using hfac
    exact hraw
  have hjoint : (∫ U, wilsonPlaqObs (N := 3)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
        * wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
            (lagPlaq (m + 2) lag) U
        ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
            (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3))))
      = (∫ U, wilsonPlaqObs (N := 3)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
            ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
                (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3))))
          * ∫ g, wilsonDensity (N := 3) g ∂(probHaar (MassGap.SUN.SU 3)) :=
    integral_prod_hol_factor m hlag (wilsonDensity (N := 3)) (wilsonDensity (N := 3))
      measurable_wilsonDensity measurable_wilsonDensity 2 2 hbound hbound
  rw [corrClay_eq_conn]
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  rw [wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero,
    hjoint, hlagint]
  ring

#print axioms corrClay_at_zero_coupling

/-! ### What the endpoint gives -/

/-- **The correlation the substrate read consumes vanishes at zero coupling, at every lag with
circle distance at least one, at every aperture.** The aperture `N = 0` is covered and not excluded:
there the only lag is `0`, whose circle distance is `0`, so the hypothesis is empty. -/
theorem wilsonCorrAt_at_zero_coupling (N : ℕ) (d : Fin (N + 1)) (hd : 1 ≤ Moment.circLag d) :
    MassGap.wilsonCorrAt N 0 d = 0 := by
  have hdv : 1 ≤ (d : ℕ) := le_trans hd (min_le_left _ _)
  have hlt := d.isLt
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hne : d ≠ 0 := by
    intro h
    rw [h] at hdv
    simp at hdv
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact corrClay_at_zero_coupling m hne

#print axioms wilsonCorrAt_at_zero_coupling

/-- **THE CONTACT-RELATIVE POWER LAW HOLDS AT ZERO COUPLING WITH `C = 0`** — the strongest constant
there is. The law is not merely true at the free end, it is true there with nothing to spare, which
is what makes `[0, b]` a statement about how fast the correlation TURNS ON rather than about how fast
it decays. -/
theorem contact_relative_at_zero_coupling (N : ℕ) (d : Fin (N + 1)) (hd : 1 ≤ Moment.circLag d) :
    MassGap.wilsonCorrAt N 0 d
      ≤ 0 * MassGap.wilsonCorrAt N 0 0 / (Moment.circLag d : ℝ) ^ 4 := by
  rw [wilsonCorrAt_at_zero_coupling N d hd]
  simp

#print axioms contact_relative_at_zero_coupling

/-- **NON-VACUITY: the zero-coupling correlation is a CONTACT TERM, not the zero function.** The
value at lag `0` is strictly positive at every aperture (`PlaqVariance.corrClay_zero_pos_at_zero_coupling`),
so `wilsonCorrAt_at_zero_coupling` says the profile is supported at the origin and not that there is
nothing there. -/
theorem contact_value_pos_at_zero_coupling (N : ℕ) : 0 < MassGap.wilsonCorrAt N 0 0 :=
  MassGap.PlaqVariance.corrClay_zero_pos_at_zero_coupling N

#print axioms contact_value_pos_at_zero_coupling

/-! ### The Haar comparison has no reverse

`ContactFloor.wilsonCorrConn_self_ge_haar` bounds the coupled variance BELOW by `e^{−2β·touch}` times
the Haar one. The obvious hope is a matching UPPER bound at the lag — `ρ_β(d) ≤ K(β)·ρ_0(d)` for some
rate `K` — which would turn the zero-coupling endpoint into a bound at every coupling. The two
theorems below say what that costs. -/

/-- **A REVERSED HAAR COMPARISON, AT ANY RATE WHATEVER, FORCES THE CORRELATION TO VANISH OFF
CONTACT.**

`K` is an arbitrary multiplier depending on the APERTURE, the COUPLING and the LAG — it may grow as
fast as it likes in any of the three, `e^{+cβ}` or anything else. The conclusion does not weaken,
because the object being compared against is ZERO at every lag with circle distance at least one
(`wilsonCorrAt_at_zero_coupling`), and any multiple of zero is zero.

So the asymmetry noted in `ContactFloor` is not a gap in the proof there and is not removable by
choosing a better rate. The `β = 0` object cannot be a majorant at ANY rate unless the correlation it
majorises is itself nonpositive at every coupling and every lag off contact. -/
theorem haar_comparison_forces_vanishing (K : ℕ → ℝ → ℕ → ℝ)
    (hcmp : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 1 ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d ≤ K N β (d : ℕ) * MassGap.wilsonCorrAt N 0 d)
    (N : ℕ) (β : ℝ) (d : Fin (N + 1)) (hd : 1 ≤ Moment.circLag d) :
    MassGap.wilsonCorrAt N β d ≤ 0 := by
  have h := hcmp N β d hd
  rwa [wilsonCorrAt_at_zero_coupling N d hd, mul_zero] at h

#print axioms haar_comparison_forces_vanishing

/-- **AND IT IMMEDIATELY GIVES THE WHOLE SUBSTRATE BOUND, WITH `C = 0`.**

This is the sharp form of the no-go: a reversed Haar comparison is not a step towards the open
statement, it is already strictly stronger than it. Anyone who produces one has not reduced the
problem — they have solved it, and along the way proved that the connected plaquette correlation is a
pure contact term at every coupling, which is what the interacting theory is not
(`WilsonBridge.wilsonCorrConn`'s whole reason for existing is that the disconnected floor has been
subtracted and something is left).

Read as a dichotomy: either no reversed comparison exists at any rate, or the correlation vanishes
off contact at every coupling. There is no third case, and neither branch leaves a route through the
`β = 0` object.

FOOTPRINT. This is the one declaration in the file whose `#print axioms` carries
`wilson_reflection_positive_at`, and it carries it from
`ShareEnvelope.substrate_of_contact_relative_decay`, not from anything proved here.
`haar_comparison_forces_vanishing`, which is the mathematical content, is foundational only. -/
theorem substrate_of_haar_comparison (K : ℕ → ℝ → ℕ → ℝ)
    (hcmp : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 1 ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d ≤ K N β (d : ℕ) * MassGap.wilsonCorrAt N 0 d) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  MassGap.ShareEnvelope.substrate_of_contact_relative_decay 1 0 le_rfl
    (fun N β d hd => by
      have h := haar_comparison_forces_vanishing K hcmp N β d hd
      simpa using h)

#print axioms substrate_of_haar_comparison

/-! ### The floor route does not survive `b → ∞`

`StrongArm.contact_relative_on_strong_arm` reaches the ratio by dividing an ABSOLUTE bound by a floor
under the contact value, and `ContactFloor.contactFloor_holds` supplies that floor as
`e^{−128b}·δ₀`. The obvious next move — push the cut `b` out and take a limit — is measured here. -/

/-- **THE TREE'S FLOOR, WITH ITS SHAPE VISIBLE.** `contactFloor_holds` states the floor existentially;
this is the same proof with `e^{−128b}·δ₀` written out, so that the `b`-dependence is a term a later
theorem can quantify over rather than a remark. `δ₀` is `ContactFloor.exists_haar_floor`'s
aperture-free Haar floor and carries no `b`. -/
theorem contactFloor_explicit :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (b : ℝ) (N : ℕ) (β : ℝ), 0 ≤ β → β ≤ b →
      Real.exp (-(128 * b)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.ContactFloor.exists_haar_floor
  refine ⟨δ₀, hδ₀, fun b N β hβ0 hβb => ?_⟩
  have hstep := MassGap.ContactFloor.corrClay_zero_ge N hβ0
  have hmono : Real.exp (-(128 * b)) ≤ Real.exp (-(128 * β)) := by
    rw [Real.exp_le_exp]; linarith
  have hδ : δ₀ ≤ corrClay (N + 1) 0 0 := hfloor N
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  calc Real.exp (-(128 * b)) * δ₀
      ≤ Real.exp (-(128 * β)) * δ₀ := mul_le_mul_of_nonneg_right hmono hδ₀.le
    _ ≤ Real.exp (-(128 * β)) * corrClay (N + 1) 0 0 :=
        mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
    _ ≤ corrClay (N + 1) β 0 := hstep

#print axioms contactFloor_explicit

/-- **THE FLOOR'S INFIMUM OVER CUTS IS ZERO.** For every positive level there is a cut at which the
floor is below it. So no single positive number is a floor on the whole half-line by way of this
family, and the failure is not a matter of a poor constant: the exponent is `2·touchDeg` and the
whole family is exponentially small in the cut.

The positivity of `δ₀` is carried so the statement reads against the floor and is UNDERSCORED because
it is not consumed: at `δ₀ ≤ 0` the conclusion is immediate, so the no-go is wider than the object it
is stated about. -/
theorem contactFloor_below_every_level {δ₀ : ℝ} (_hδ₀ : 0 < δ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ Real.exp (-(128 * b)) * δ₀ < ε := by
  refine ⟨max 1 (δ₀ / ε), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  set b : ℝ := max 1 (δ₀ / ε) with hb
  have hb1 : (1 : ℝ) ≤ b := le_max_left _ _
  have hbq : δ₀ / ε ≤ b := le_max_right _ _
  have hE : (128 : ℝ) * b + 1 ≤ Real.exp (128 * b) := Real.add_one_le_exp _
  have hq : δ₀ / ε < Real.exp (128 * b) := by nlinarith
  have hEpos : (0 : ℝ) < Real.exp (128 * b) := Real.exp_pos _
  have hkey : δ₀ < ε * Real.exp (128 * b) := by
    rw [div_lt_iff₀ hε] at hq
    linarith
  rw [Real.exp_neg]
  rw [inv_mul_eq_div, div_lt_iff₀ hEpos]
  linarith

#print axioms contactFloor_below_every_level

/-- **THE CONSTANT THE FLOOR ROUTE PRODUCES IS UNBOUNDED IN THE CUT.**

Let `A > 0` be any fixed positive numerator — in `StrongArm.contact_relative_on_strong_arm` it is
`coreConst(16·4, b)·S`, which is MONOTONE INCREASING in `b`
(`StrongArm.coreConst_mono_beta`), so bounding it below by its value at any cut is giving the route
the benefit of the doubt. If `C : ℝ → ℝ` assigns to each cut a constant that the route's own
inequality `A ≤ C(b)·δ(b)` certifies against the floor `δ(b) = e^{−128b}·δ₀`, then `C` is unbounded:
for every level there is a cut whose constant exceeds it.

So the proved interval cannot be grown into the half-line. The statement
`contact_relative_unconditional` produces is not a family converging to anything as `b → ∞`; its
constant diverges at least like `e^{128b}`, which is the floor's own exponent. That is a property of
the ROUTE — dividing an absolute bound by a floor — and it is why `[b, ∞)` needs an argument that
never bounds `ρ(0)` below, as `StrongArm.ContactFloor`'s own docstring says.

DERIVED: `128` is `2·16·4` carried in from the floor; no numeral here is a magnitude. -/
theorem floor_route_constant_unbounded {δ₀ A : ℝ} (hδ₀ : 0 < δ₀) (hA : 0 < A)
    (C : ℝ → ℝ) (hC : ∀ b : ℝ, 0 ≤ b → A ≤ C b * (Real.exp (-(128 * b)) * δ₀)) (M : ℝ) :
    ∃ b : ℝ, 0 < b ∧ M < C b := by
  set t : ℝ := |M| * δ₀ / A with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨max 1 t, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  set b : ℝ := max 1 t with hb
  have hb1 : (1 : ℝ) ≤ b := le_max_left _ _
  have hbt : t ≤ b := le_max_right _ _
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb1
  set E : ℝ := Real.exp (128 * b) with hEdef
  have hE : (0 : ℝ) < E := Real.exp_pos _
  have hlin : (128 : ℝ) * b + 1 ≤ E := Real.add_one_le_exp _
  have h2 : t + 1 ≤ E := by nlinarith
  have hA' : A ≤ C b * (E⁻¹ * δ₀) := by
    have := hC b hbpos.le
    rwa [Real.exp_neg, ← hEdef] at this
  have hAt : A * t = |M| * δ₀ := by
    rw [ht]; field_simp
  have hstep1 : A * (t + 1) ≤ A * E := mul_le_mul_of_nonneg_left h2 hA.le
  have hstep2 : A * E ≤ C b * (E⁻¹ * δ₀) * E := mul_le_mul_of_nonneg_right hA' hE.le
  have hstep3 : C b * (E⁻¹ * δ₀) * E = C b * δ₀ := by
    field_simp
  have hmain : |M| * δ₀ + A ≤ C b * δ₀ := by
    have : A * (t + 1) = A * t + A := by ring
    rw [this, hAt] at hstep1
    rw [hstep3] at hstep2
    linarith
  have hMabs : M ≤ |M| := le_abs_self M
  nlinarith [hδ₀, hA, hmain, hMabs]

#print axioms floor_route_constant_unbounded

/-- **NON-VACUITY OF THE ROUTE NO-GO.** The hypothesis of `floor_route_constant_unbounded` is
satisfiable — the smallest constant the route's own inequality admits is `A/(e^{−128b}·δ₀)` — so the
no-go is not an implication out of an empty hypothesis. Stated so the divergence is exhibited on a
witness and not only asserted of an abstract family. -/
theorem floor_route_nonvacuous {δ₀ A : ℝ} (hδ₀ : 0 < δ₀) (hA : 0 < A) :
    ∃ C : ℝ → ℝ, (∀ b : ℝ, 0 ≤ b → A ≤ C b * (Real.exp (-(128 * b)) * δ₀)) ∧
      ∀ M : ℝ, ∃ b : ℝ, 0 < b ∧ M < C b := by
  refine ⟨fun b => A / (Real.exp (-(128 * b)) * δ₀), fun b _ => ?_, ?_⟩
  · have hpos : (0 : ℝ) < Real.exp (-(128 * b)) * δ₀ := by positivity
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
  · intro M
    refine floor_route_constant_unbounded hδ₀ hA _ (fun b _ => ?_) M
    have hpos : (0 : ℝ) < Real.exp (-(128 * b)) * δ₀ := by positivity
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

#print axioms floor_route_nonvacuous

end MassGap.PowerTail
