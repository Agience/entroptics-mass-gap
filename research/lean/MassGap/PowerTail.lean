import Mathlib
import MassGap.ContactFloor
import MassGap.WeakArm

/-!
# MassGap.PowerTail — the connected correlation at zero coupling, and two consequences

## The zero-coupling value

`corrClay_at_zero_coupling`: `corrClay (m + 2) 0 lag = 0` at every lag other than `0`. At `β = 0` the
Gibbs measure is product Haar (`WilsonReal.wilsonSystem_expect_at_zero`), and the two plaquettes
`clayPlaq` and `lagPlaq` read disjoint link sets when the lag is nonzero, so the joint average
factorises and the connected part vanishes.

The factorisation is `integral_prod_hol_factor`. Its handle is `handle`, the direction-`1` link at
the lag plaquette's base site: `hol_linkTranslate_lag` shows translating it right-multiplies that
plaquette's holonomy, because it is the last letter of the boundary word, and
`hol_linkTranslate_clay_fixed` shows the base plaquette's holonomy does not move, because the handle
is none of its four links. Averaging over the handle and swapping the order of integration then sends
the lag plaquette's holonomy through Haar. No independence lemma for product measures is used; the
content is the single-link left-invariance of `ContactFloor.linkTranslate_measurePreserving`.

`wilsonCorrAt_at_zero_coupling` restates it on `wilsonCorrAt`, at every aperture including `N = 0`,
where the only lag has circle distance `0` and the hypothesis `1 ≤ circLag d` is empty.
`contact_relative_at_zero_coupling` reads it as the contact-relative quartic law at `C = 0`, and
`contact_value_pos_at_zero_coupling` records that the value at lag `0` is strictly positive, so the
profile is supported at the origin rather than identically zero.

## Two consequences

`haar_comparison_forces_vanishing`: for any multiplier `K : ℕ → ℝ → ℕ → ℝ`, a comparison
`ρ_β(d) ≤ K N β d · ρ_0(d)` at every lag with circle distance at least one forces `ρ_β(d) ≤ 0` there,
because the right-hand side is a multiple of zero. `substrate_of_haar_comparison` feeds that into
`ShareEnvelope.substrate_of_contact_relative_decay` at `C = 0`, `m₀ = 1`, giving
`∃ B, ∀ N β, d2At N β ≤ B`.

`contactFloor_explicit` writes `ContactFloor.contactFloor_holds`'s floor as `e^{−128b}·δ₀` with the
`b`-dependence visible. `contactFloor_below_every_level` shows that family goes below every positive
level as `b` grows, and `floor_route_constant_unbounded` shows that any `C : ℝ → ℝ` satisfying
`A ≤ C(b)·e^{−128b}·δ₀` for a fixed `A > 0` is unbounded. `floor_route_nonvacuous` exhibits such a
`C`, so the hypothesis is satisfiable.

## Scope

`corrClay_at_zero_coupling` is about `β = 0` and asserts nothing at any other coupling. Nothing here
states that the contact-relative law fails at large coupling, and nothing here produces a bound there.

DERIVED: `128` is `2·16·4` carried in from `ContactFloor`; `4` is the lattice dimension, `3` is the
colour rank of `SU(3)`, the directions `0` and `1` span the plaquette's plane and `2` is the lag axis
transverse to it, all fixed by `WilsonBridge.corrClay`. The extent is written `m + 2` because a
single periodic step must move a site, the same threshold `ContactFloor.shift_ne` requires. No
numeral here is a magnitude.
-/
namespace MassGap.PowerTail

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MassGap.PlaqVariance MassGap.ContactFloor
open MeasureTheory

/-! ### The two plaquettes `corrClay` reads -/

/-- The plaquette `corrClay` reads at lag `lag`: the ordered plane `(0, 1)` based at
`siteAtHyper 2 lag`, the origin displaced `lag` steps along direction `2`. `WilsonBridge.clayPlaq` is
the `lag = 0` case.

DERIVED: every index is `corrClay`'s own, not a choice of this definition. `4` is the lattice
dimension `WilsonBridge.corrClay` is built at; `0` and `1` are the two directions its plaquette spans
and `2` the axis its lag runs along, all read off `WilsonBridge.clayPlaq`. Changing any of them
describes a different correlation. -/
def lagPlaq (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Plaq 4 n :=
  ((0, 1), siteAtHyper 2 lag)

#print axioms lagPlaq

/-- `corrClay n β lag = wilsonCorrConn bd (clayPlaq n) β (lagPlaq n lag)`, by `rfl`: the definitional
identification of `corrClay` with the connected correlation of the two named plaquettes.

DERIVED: `4` is the lattice dimension and `3` the colour rank, both `corrClay`'s; the plane and lag
indices are inside `clayPlaq` and `lagPlaq`. This declaration introduces no numeral. -/
theorem corrClay_eq_conn (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrClay n β lag
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
          (clayPlaq n) β (lagPlaq n lag) := rfl

#print axioms corrClay_eq_conn

/-- The holonomy of the hypercubic plaquette `((μ, ν), x)` written out as the ordered product
`U (μ, x) * (U (ν, shift μ x) * ((U (μ, shift ν x))⁻¹ * (U (ν, x))⁻¹))`, by `simp` on `wilsonHol`
and `bd`. Bracketed to the right, which is the shape the `linkTranslate` rewrites below consume.

Holds for every `μ`, `ν`, including `μ = ν`.

DERIVED: `4` is the lattice dimension and `3` the colour rank; `⁻¹` is the group inverse. No numeral
of this declaration's own. -/
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

/-- The direction-`1` link at the lag plaquette's own base site `siteAtHyper 2 lag`. It is the last
letter of that plaquette's boundary word, carried with orientation `false`, and when the lag is
nonzero it is none of the base plaquette's four links.

DERIVED: `1` is the direction, forced rather than picked. `WilsonHypercubic.bd` writes a boundary
word as `[(μ,x,true), (ν,shift μ x,true), (μ,shift ν x,false), (ν,x,false)]`, so at the `(0, 1)`
plane the last letter is the direction-`1` link at the base site, and the last letter is the one a
right translation acts on. `4` is the lattice dimension and `2` the lag axis, both from `lagPlaq`. -/
def handle (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Link 4 n :=
  ((1 : Fin 4), siteAtHyper 2 lag)

#print axioms handle

/-! ### The handle moves the lag plaquette and leaves the base plaquette alone -/

/-- Translating the handle by `g⁻¹` right-multiplies the lag plaquette's holonomy by `g`:
`wilsonHol bd (lagPlaq lag) (linkTranslate g⁻¹ (handle lag) U) = wilsonHol bd (lagPlaq lag) U * g`.

The three other letters of the boundary word are different links: two by direction (`0 ≠ 1`), and
one because a single periodic step moves the site. That last step is where the extent being at least
two is used — at extent one every shift is the identity.

DERIVED: `2` in `m + 2` is the least extent at which a unit shift moves a site, which the proof
needs. `3` is the colour rank and `4` the lattice dimension. `0` and `1` are the plane directions and
`2` the lag axis, all from `lagPlaq` and `handle`; `⁻¹` is the group inverse. -/
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

/-- For `lag ≠ 0`, translating the handle leaves the base plaquette's holonomy unchanged:
`wilsonHol bd (clayPlaq) (linkTranslate g⁻¹ (handle lag) U) = wilsonHol bd (clayPlaq) U`.

Each of the four letters of the base plaquette's word differs from the handle: two by direction, and
two because their sites have coordinate `2` equal to `0` while the handle's site has coordinate `2`
equal to `lag`.

`hlag` is used exactly here, and it is the whole geometric content: at `lag = 0` the two plaquettes
coincide and no such handle exists.

DERIVED: `0` is the lag value excluded by `hlag` and the coordinate the base plaquette's sites carry
on the lag axis. `2` in `m + 2` is the extent bound and `2` in the coordinate index is the lag axis.
`3` is the colour rank, `4` the lattice dimension, and `0`, `1` the plane directions. -/
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

/-! ### The factorisation under product Haar

`ContactFloor.integral_hol_clay`'s argument with a second plaquette present. The handle belongs to
the lag plaquette and to none of the links the base plaquette reads, so averaging over it sends the
lag plaquette's holonomy through Haar while the base plaquette's is untouched, and the joint integral
factorises. No independence lemma for product measures is used; the content is the single-link
left-invariance of `linkTranslate_measurePreserving`. -/

/-- For `lag ≠ 0` and bounded measurable `f`, `h : SU 3 → ℝ`,

    ∫ f(hol_base) · h(hol_lag) dπ  =  (∫ f(hol_base) dπ) · (∫ h dHaar),

where `π` is the product Haar measure over the links.

`hol_linkTranslate_clay_fixed` and `hol_linkTranslate_lag` make the integrand invariant under
translating the handle by `g⁻¹`, so the integral is unchanged when `hol_lag` is replaced by
`hol_lag * g`; averaging that over `g`, swapping the order by `integral_integral_swap` — for which
the bounds `Mf`, `Mh` supply integrability — and using left-invariance of Haar inside gives the
product.

`f` and `h` are arbitrary bounded measurable functions; the boundedness hypotheses are what the
Fubini step consumes.

DERIVED: `0` is the lag value excluded by `hlag`. `2` in `m + 2` is the extent bound, `3` the colour
rank and `4` the lattice dimension; `Mf` and `Mh` are the caller's bounds. -/
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

/-- `corrClay (m + 2) 0 lag = 0` for every `lag ≠ 0`, at every extent of the form `m + 2`.

At `β = 0` the Gibbs measure is product Haar (`wilsonSystem_expect_at_zero`), so both the joint
expectation and the lag marginal are plain integrals; `integral_prod_hol_factor` factorises the first
and evaluates the second, and the connected part — the joint minus the product of the marginals —
cancels by `ring`. The bound `2` on `|wilsonDensity|` supplies the boundedness hypotheses.

About `β = 0` only. Nothing here is asserted at any other coupling.

DERIVED: `0` is the coupling the statement is at, the lag value excluded by `hlag`, and the value
concluded. `2` in `m + 2` is the least extent at which the argument's shift is nontrivial. `3` is the
colour rank and `4` the lattice dimension; the `2` bounding `|wilsonDensity|` is
`wilsonDensity_le_two`'s and appears in the proof. -/
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

/-- `wilsonCorrAt N 0 d = 0` at every aperture `N` and every lag `d` with `1 ≤ circLag d`.
`StrongArm.wilsonCorrAt_eq_corrClay` transports `corrClay_at_zero_coupling`; the hypothesis forces
`d ≠ 0` and `N ≥ 1`, which is what lets `N` be written `m + 1`.

`N = 0` is covered rather than excluded: there the only lag is `0`, whose circle distance is `0`, so
the hypothesis is unsatisfiable and the statement is vacuous at that aperture.

DERIVED: `1` is the lower bound on the circle distance, which excludes the contact lag, and the `+1`
of `Fin (N + 1)`, the number of lags. `0` is the coupling, the lag index excluded, and the value
concluded. -/
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

/-- `wilsonCorrAt N 0 d ≤ 0 * wilsonCorrAt N 0 0 / (circLag d)^4` at every aperture and every lag with
`1 ≤ circLag d`. Immediate from `wilsonCorrAt_at_zero_coupling`: both sides are `0`.

The contact-relative quartic law at the constant `C = 0`, at the coupling `β = 0` only.

DERIVED: `1` is the lower bound on the circle distance. `0` is the coupling, the contact lag in the
denominator's reference value, and the constant `C` in front — which is `0` because the left side
vanishes, not by a choice. `4` is the exponent of the quartic law, `ContactFloor`'s. -/
theorem contact_relative_at_zero_coupling (N : ℕ) (d : Fin (N + 1)) (hd : 1 ≤ Moment.circLag d) :
    MassGap.wilsonCorrAt N 0 d
      ≤ 0 * MassGap.wilsonCorrAt N 0 0 / (Moment.circLag d : ℝ) ^ 4 := by
  rw [wilsonCorrAt_at_zero_coupling N d hd]
  simp

#print axioms contact_relative_at_zero_coupling

/-- `0 < wilsonCorrAt N 0 0` at every aperture. The body is
`PlaqVariance.corrClay_zero_pos_at_zero_coupling`.

Together with `wilsonCorrAt_at_zero_coupling` this says the zero-coupling profile is supported at the
contact lag and is not the zero function.

DERIVED: `0` is the coupling, the contact lag, and the strict lower bound asserted; it is the only
numeral. -/
theorem contact_value_pos_at_zero_coupling (N : ℕ) : 0 < MassGap.wilsonCorrAt N 0 0 :=
  MassGap.PlaqVariance.corrClay_zero_pos_at_zero_coupling N

#print axioms contact_value_pos_at_zero_coupling

/-! ### Comparison against the zero-coupling value

`ContactFloor.wilsonCorrConn_self_ge_haar` bounds the coupled variance below by `e^{−2β·touch}` times
the Haar one. The two theorems below concern an upper bound of the matching shape at the lag,
`ρ_β(d) ≤ K·ρ_0(d)`, and what follows from one. -/

/-- For any `K : ℕ → ℝ → ℕ → ℝ`: if `wilsonCorrAt N β d ≤ K N β d * wilsonCorrAt N 0 d` at every
aperture, coupling and lag with `1 ≤ circLag d`, then `wilsonCorrAt N β d ≤ 0` at all of them.

`wilsonCorrAt_at_zero_coupling` makes the right-hand side `K N β d * 0 = 0`.

`K` may depend on all three arguments and grow arbitrarily fast in each; the conclusion does not
weaken, because a multiple of zero is zero regardless.

DERIVED: `1` is the lower bound on the circle distance and the `+1` of `Fin (N + 1)`. `0` is the
coupling the comparison is against and the upper bound concluded. -/
theorem haar_comparison_forces_vanishing (K : ℕ → ℝ → ℕ → ℝ)
    (hcmp : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 1 ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d ≤ K N β (d : ℕ) * MassGap.wilsonCorrAt N 0 d)
    (N : ℕ) (β : ℝ) (d : Fin (N + 1)) (hd : 1 ≤ Moment.circLag d) :
    MassGap.wilsonCorrAt N β d ≤ 0 := by
  have h := hcmp N β d hd
  rwa [wilsonCorrAt_at_zero_coupling N d hd, mul_zero] at h

#print axioms haar_comparison_forces_vanishing

/-- The same hypothesis yields `∃ B : ℝ, ∀ N β, d2At N β ≤ B`.
`haar_comparison_forces_vanishing` supplies the contact-relative law at `C = 0`, `m₀ = 1`, and
`ShareEnvelope.substrate_of_contact_relative_decay` consumes it.

So a comparison of that shape implies the uniform bound on `d2At`, and also implies the connected
plaquette correlation is nonpositive off contact at every coupling.

Scope: this is the one declaration in the file whose `#print axioms` carries
`wilson_reflection_positive_at`, inherited from
`ShareEnvelope.substrate_of_contact_relative_decay`. `haar_comparison_forces_vanishing`, which is
the arithmetic, does not.

DERIVED: `1` is the lower bound on the circle distance in `hcmp`, the `+1` of `Fin (N + 1)`, and the
`m₀` passed to `substrate_of_contact_relative_decay`. `0` is the coupling the comparison is against
and the constant `C` passed to that lemma. -/
theorem substrate_of_haar_comparison (K : ℕ → ℝ → ℕ → ℝ)
    (hcmp : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 1 ≤ Moment.circLag d →
      MassGap.wilsonCorrAt N β d ≤ K N β (d : ℕ) * MassGap.wilsonCorrAt N 0 d) :
    ∃ B : ℝ, ∀ N β, MassGap.d2At N β ≤ B :=
  MassGap.ShareEnvelope.substrate_of_contact_relative_decay 1 0 le_rfl
    (fun N β d hd => by
      have h := haar_comparison_forces_vanishing K hcmp N β d hd
      simpa using h)

#print axioms substrate_of_haar_comparison

/-! ### The floor as a function of the cut

`StrongArm.contact_relative_on_strong_arm` reaches a ratio by dividing an absolute bound by a floor
under the contact value, and `ContactFloor.contactFloor_holds` supplies that floor as `e^{−128b}·δ₀`.
The three theorems below measure that family as `b` grows. -/

/-- There is a `δ₀ > 0` with `exp (-(128 * b)) * δ₀ ≤ wilsonCorrAt N β 0` at every cut `b`, aperture
`N`, and coupling `β ∈ [0, b]`. `ContactFloor.exists_haar_floor` supplies `δ₀`, monotonicity of `exp`
replaces `β` by `b` in the exponent, and `ContactFloor.corrClay_zero_ge` closes it.

`ContactFloor.contactFloor_holds` states the same floor existentially; here the `b`-dependence is
written out, so that `contactFloor_below_every_level` and `floor_route_constant_unbounded` can
quantify over it. `δ₀` is aperture-free and carries no `b`.

DERIVED: `0` is the strict lower bound on `δ₀` and the lower end of the coupling interval, and the
contact lag the floor is under. `128` is `2 · 16 · 4`, carried in from `ContactFloor` — twice the
touch degree at dimension four — and is not chosen here. -/
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

/-- For every `ε > 0` there is a cut `b > 0` with `exp (-(128 * b)) * δ₀ < ε`. The witness is
`max 1 (δ₀ / ε)`, using `Real.add_one_le_exp` to put `exp (128 * b)` above `δ₀ / ε`.

So no positive number is a lower bound for the whole family `b ↦ exp (-(128*b)) * δ₀`.

`_hδ₀` is spelled with an underscore because it is unused: at `δ₀ ≤ 0` the conclusion is immediate,
so the statement is wider than the floor it is phrased against.

DERIVED: `0` is the strict lower bound on `δ₀`, on `ε`, and on the cut `b`. `128` is
`contactFloor_explicit`'s exponent, carried from `ContactFloor`. -/
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

/-- For `δ₀ > 0`, `A > 0`, and any `C : ℝ → ℝ` satisfying `A ≤ C b * (exp (-(128 * b)) * δ₀)` at
every `b ≥ 0`: for every level `M` there is a cut `b > 0` with `M < C b`. So `C` is unbounded.

The witness is `max 1 (|M| δ₀ / A)`, with `Real.add_one_le_exp` again supplying the growth.

`A` is a fixed positive number. In `StrongArm.contact_relative_on_strong_arm` the corresponding
numerator is `coreConst(16·4, b)·S`, which `StrongArm.coreConst_mono_beta` makes monotone increasing
in `b`, so holding it fixed bounds it below by its value at any cut.

The statement is about any `C` meeting that inequality; `floor_route_nonvacuous` exhibits one, so the
hypothesis is satisfiable.

DERIVED: `0` is the strict lower bound on `δ₀`, on `A`, on the cut in `hC`'s quantifier, and on the
witness `b`. `128` is the floor's exponent, `2 · 16 · 4` carried in from `ContactFloor`; `M` is the
caller's level. No numeral here is a magnitude. -/
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

/-- For `δ₀ > 0` and `A > 0` there is a `C : ℝ → ℝ` satisfying
`A ≤ C b * (exp (-(128 * b)) * δ₀)` at every `b ≥ 0` and unbounded above on the positive cuts.

The witness is `C b = A / (exp (-(128*b)) * δ₀)`, the smallest constant the inequality admits, for
which the inequality is an equality; its unboundedness is `floor_route_constant_unbounded` applied to
itself.

So `floor_route_constant_unbounded`'s hypothesis is satisfiable, and the divergence is exhibited on a
witness rather than only asserted of an abstract family.

DERIVED: `0` is the strict lower bound on `δ₀` and on `A`, the lower bound on the cut, and the strict
lower bound on the witness. `128` is the floor's exponent, carried from `ContactFloor`. -/
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
