import Mathlib
import MassGap.WilsonBridge

/-!
# MassGap.LocalGauge — the site-dependent gauge group of the hypercubic Wilson lattice

`CompactGauge.confConj` conjugates every link by one constant group element. This module defines the
larger action carrying one group element per site,

    U_μ(x)  ↦  g(x) · U_μ(x) · g(x + μ̂)⁻¹,

as `gaugeTransform` on `WilsonHypercubic.Link d n`, and proves the Gibbs state of the Wilson system
invariant under it.

The chain. `shift_comm` proves the two unit shifts of a plaquette commute. `hol_gaugeTransform` then
proves the plaquette holonomy is conjugated by `g` at the plaquette's base site: the interior factors
cancel telescopically along the four-letter boundary word, and the far-corner pair cancels because
the shifts commute. `wilsonDensity_gaugeTransform` follows, since `wilsonDensity` is a class
function, and with it `plaqObs_gauge_invariant_local`, `wilsonAction_gauge_invariant_local` and
`boltz_gauge_invariant_local`.

On the measure side, `linkTwoSided` is a per-coordinate left-then-right translation;
`linkTwoSided_measurePreserving` proves it preserves the product Haar measure by
`Measure.pi_map_pi`, and `linkTwoSidedEquiv` upgrades it to a measurable equivalence. `gaugeEquiv`
is `gaugeTransform` in that form — `gaugeEquiv_apply` is the `rfl` identifying them — and
`gaugeEquiv_measurePreserving` transports the result. `expect_gauge_invariant_local` combines the
measure and action halves through `System.expect_invariant_of_mp`, for an arbitrary observable, not
only a gauge-invariant one. `gaugeTransform_const` records that a constant `g` gives back
`CompactGauge.confConj`, definitionally.

`clayState_gauge_invariant_local` is the `d = 4`, `N = 3` instance, and
`corrClay_gauge_invariant_local` applies it to `WilsonBridge.corrClay`.

## Scope

Everything is stated at a fixed finite extent `n` with periodic sites `Site d n = Fin d → Fin n`; no
limit in `n` and no continuum limit appears. The objects are real-valued functions on a finite
configuration space integrated against a Gibbs measure — there is no Hilbert space and no operator
here. No curvature two-form, covariant derivative or polynomial in them is defined anywhere in this
module, and no statement relates `wilsonPlaqObs` to one. `corrClay_gauge_invariant_local` uses the
single ordered plane `(0, 1)` for both of its plaquettes, so the correlator it concerns carries one
index pair, not two independent ones.
-/

namespace MassGap.LocalGauge

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory Measure

variable {d n : ℕ}

/-! ### The two unit shifts of a plaquette commute

The geometric content of the telescoping in `hol_gaugeTransform`: stepping one unit along `μ` and
then one along `ν` reaches the same site as the other order, so the two gauge elements at the far
corner of the plaquette are the same element and cancel. -/

/-- `shift ν (shift μ x) = shift μ (shift ν x)` for any two directions and any site. `shift` is a
`Function.update` of one coordinate, so for `μ ≠ ν` the two updates are at different indices and
`Function.update_comm` applies; for `μ = ν` the two sides are the same expression.

The sites are `Site d n = Fin d → Fin n`, so the coordinate increment wraps — the periodicity is in
the `Fin n` arithmetic, not in this statement.

DERIVED: no numeral. The unit increment lives inside `shift` and does not appear here. -/
theorem shift_comm [NeZero n] (μ ν : Fin d) (x : Site d n) :
    shift ν (shift μ x) = shift μ (shift ν x) := by
  by_cases h : μ = ν
  · subst h; rfl
  · have h' : ν ≠ μ := fun hh => h hh.symm
    have e1 : shift μ x ν = x ν := by
      simp only [MassGap.WilsonHypercubic.shift, Function.update_apply, if_neg h']
    have e2 : shift ν x μ = x μ := by
      simp only [MassGap.WilsonHypercubic.shift, Function.update_apply, if_neg h]
    show Function.update (shift μ x) ν (shift μ x ν + 1)
        = Function.update (shift ν x) μ (shift ν x μ + 1)
    rw [e1, e2]
    show Function.update (Function.update x μ (x μ + 1)) ν (x ν + 1)
        = Function.update (Function.update x ν (x ν + 1)) μ (x μ + 1)
    exact Function.update_comm h _ _ x

/-! ### The local gauge action on link variables -/

/-- The site-dependent gauge action on configurations: given `g : Site d n → G`, send
`U : Link d n → G` to `fun l => g l.2 * U l * (g (shift l.1 l.2))⁻¹`.

A link is a pair `(direction, base site)` and `WilsonHypercubic.bd` traverses it from its base site
to the shifted one, so `g` enters at the source and `g⁻¹` at the target. For constant `g` the two
factors are inverse to each other and the action becomes conjugation; `gaugeTransform_const` records
that.

`G` is any group with a `MeasurableSpace`, and `[NeZero n]` is required only because `Site d n` uses
`Fin n`.

DERIVED: no numeral. The `1` and `2` in `l.1` and `l.2` are structure projections of the pair
`Link d n = Fin d × Site d n`, selecting the direction and the base site; they are not numbers. -/
def gaugeTransform {G : Type} [Group G] [MeasurableSpace G] [NeZero n]
    (g : Site d n → G) (U : Link d n → G) : Link d n → G :=
  fun l => g l.2 * U l * (g (shift l.1 l.2))⁻¹

/-- `wilsonHol bd q (gaugeTransform g U) = g q.2 * wilsonHol bd q U * (g q.2)⁻¹`: the plaquette
holonomy is conjugated by the gauge element at the plaquette's base site.

The proof writes both sides out as four-letter products. In

    (g_x A g_μ⁻¹) · (g_μ B g_{νμ}⁻¹) · (g_ν C g_{μν}⁻¹)⁻¹ · (g_x D g_ν⁻¹)⁻¹

the `g_μ` pair cancels between the first two factors, the `g_ν` pair between the last two, and the
far-corner pair `g_{νμ}`, `g_{μν}` cancels by `shift_comm`; `group` closes it. What survives is
`g_x` on the left and `g_x⁻¹` on the right.

Conjugation, not invariance: the holonomy does move, and it is `wilsonDensity` being a class function
that makes the observable invariant.

DERIVED: no numeral. The `2` in `q.2` is the structure projection selecting the plaquette's base
site from `Plaq d n = (Fin d × Fin d) × Site d n`; the `⁻¹` is the group inverse. -/
theorem hol_gaugeTransform {G : Type} [Group G] [MeasurableSpace G] [NeZero n]
    (g : Site d n → G) (U : Link d n → G) (q : Plaq d n) :
    wilsonHol (bd (d := d) (n := n)) q (gaugeTransform g U)
      = g q.2 * wilsonHol (bd (d := d) (n := n)) q U * (g q.2)⁻¹ := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  show wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) (gaugeTransform g U)
      = g x * wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U * (g x)⁻¹
  have hs : shift ν (shift μ x) = shift μ (shift ν x) := shift_comm μ ν x
  have hL : wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) (gaugeTransform g U)
      = (g x * U (μ, x) * (g (shift μ x))⁻¹)
        * ((g (shift μ x) * U (ν, shift μ x) * (g (shift ν (shift μ x)))⁻¹)
          * ((g (shift ν x) * U (μ, shift ν x) * (g (shift μ (shift ν x)))⁻¹)⁻¹
            * ((g x * U (ν, x) * (g (shift ν x))⁻¹)⁻¹ * 1))) := rfl
  have hR : wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U
      = U (μ, x) * (U (ν, shift μ x) * ((U (μ, shift ν x))⁻¹ * ((U (ν, x))⁻¹ * 1))) := rfl
  rw [hL, hR, hs]
  group

/-! ### The plaquette observable and the action are invariant, pointwise in the configuration -/

/-- `wilsonDensity (wilsonHol bd q (gaugeTransform g U)) = wilsonDensity (wilsonHol bd q U)`, for
every site-dependent `g`, every configuration and every plaquette. `hol_gaugeTransform` conjugates
the holonomy and `wilsonDensity_conj` — trace cyclicity — shows `wilsonDensity` does not see
conjugation.

Pointwise in the configuration: no measure and no expectation is involved.

DERIVED: no numeral. -/
theorem wilsonDensity_gaugeTransform {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (U : Link d n → MassGap.SUN.SU N) (q : Plaq d n) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (gaugeTransform g U))
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  rw [hol_gaugeTransform]
  exact wilsonDensity_conj _ _

/-- `wilsonPlaqObs bd q (gaugeTransform g U) = wilsonPlaqObs bd q U`. The same statement as
`wilsonDensity_gaugeTransform`, phrased on the observable of the `wilsonSystem` configuration type;
the body is that theorem.

So the plaquette observable is unchanged by every site-dependent gauge transformation, not only by
the constant ones. Locality — that it reads only the four links of its own plaquette — is
`ReflectionPositivity.hol_congr_on_support` and is not restated here.

DERIVED: no numeral. -/
theorem plaqObs_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (q : Plaq d n)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    wilsonPlaqObs (N := N) (bd (d := d) (n := n)) q (gaugeTransform g U)
      = wilsonPlaqObs (N := N) (bd (d := d) (n := n)) q U :=
  wilsonDensity_gaugeTransform g U q

/-- `(wilsonSystem bd wilsonDensity).action (gaugeTransform g U) = (…).action U`. The action is the
sum of the plaquette density over all of `Plaq d n`, and every summand is invariant by
`wilsonDensity_gaugeTransform`, so `Finset.sum_congr` closes it.

DERIVED: no numeral. -/
theorem wilsonAction_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).action (gaugeTransform g U)
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).action U :=
  Finset.sum_congr rfl (fun q _ => wilsonDensity_gaugeTransform g U q)

/-- `(wilsonSystem bd wilsonDensity).boltz β (gaugeTransform g U) = (…).boltz β U`, at every real
`β`. `System.boltz` is `exp` of the negated action scaled by `β`, so this is
`wilsonAction_gauge_invariant_local` under a rewrite.

`β` is unrestricted in sign.

DERIVED: no numeral. -/
theorem boltz_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N) (β : ℝ)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).boltz β (gaugeTransform g U)
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).boltz β U := by
  unfold System.boltz
  rw [wilsonAction_gauge_invariant_local]

/-! ### The measure side

Per link, the gauge transformation is a left translation by `g(x)` followed by a right translation by
`g(x + μ̂)⁻¹`. On a compact group the probability Haar measure is invariant under both
(`CompactGauge.isMulLeftInvariant_probHaar` and `CompactGauge.isMulRightInvariant_probHaar`, the
latter from unimodularity), and the product measure is preserved coordinatewise.

The two translating elements differ from link to link, so the per-link maps form a family rather
than a single map; `linkTwoSided` is stated for an arbitrary such family, over an arbitrary finite
index type. -/

/-- The per-coordinate two-sided translation of a configuration by two families `a`, `b : ι → G`:
`U ↦ fun l => a l * U l * b l`. `ι` is arbitrary and no relation between `a` and `b` is assumed.

DERIVED: no numeral. -/
def linkTwoSided (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} (a b : ι → G) (U : ι → G) : ι → G :=
  fun l => a l * U l * b l

/-- `linkTwoSided G a b` is measure-preserving from `Measure.pi (fun _ => probHaar G)` to itself, for
any finite `ι` and any families `a`, `b : ι → G`. Each coordinate map `u ↦ a l * u * b l` is a
left translation composed with a right translation, each preserving `probHaar G` on a compact group;
`Measure.pi_map_pi` assembles the coordinates.

`G` must be a compact, nonempty topological group with a Borel measurable structure; `ι` must be a
`Fintype`, which is what `Measure.pi` needs.

DERIVED: no numeral. -/
theorem linkTwoSided_measurePreserving (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} [Fintype ι] (a b : ι → G) :
    MeasurePreserving (linkTwoSided G a b) (Measure.pi fun _ : ι => probHaar G)
      (Measure.pi fun _ : ι => probHaar G) := by
  have hstep : ∀ l : ι,
      MeasurePreserving (fun u : G => a l * u * b l) (probHaar G) (probHaar G) := by
    intro l
    have h := (measurePreserving_mul_left (probHaar G) (a l)).comp
      (measurePreserving_mul_right (probHaar G) (b l))
    convert h using 1
    funext u; simp [Function.comp, mul_assoc]
  haveI hsf : ∀ l : ι, SigmaFinite ((probHaar G).map (fun u : G => a l * u * b l)) :=
    fun l => by rw [(hstep l).map_eq]; infer_instance
  refine ⟨measurable_pi_lambda _ (fun l => (hstep l).measurable.comp (measurable_pi_apply l)), ?_⟩
  have hmap : (fun l : ι => (probHaar G).map (fun u : G => a l * u * b l))
      = fun _ : ι => probHaar G := funext fun l => (hstep l).map_eq
  rw [show linkTwoSided G a b
        = (fun (U : ι → G) (l : ι) => (fun u : G => a l * u * b l) (U l)) from rfl,
    Measure.pi_map_pi (fun l => (hstep l).aemeasurable), hmap]

/-- `linkTwoSided G a b` as a measurable equivalence `(ι → G) ≃ᵐ (ι → G)`. The inverse is
`linkTwoSided` at the pointwise inverse families, both round trips closed by `group`, and both
directions measurable because multiplication by a constant on either side is continuous.

No finiteness of `ι` is required here; only `linkTwoSided_measurePreserving` needs it.

DERIVED: no numeral. The `⁻¹` in the inverse families is the group inverse. -/
noncomputable def linkTwoSidedEquiv (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} (a b : ι → G) : (ι → G) ≃ᵐ (ι → G) where
  toFun := linkTwoSided G a b
  invFun := linkTwoSided G (fun l => (a l)⁻¹) (fun l => (b l)⁻¹)
  left_inv := fun U => by funext l; simp only [linkTwoSided]; group
  right_inv := fun U => by funext l; simp only [linkTwoSided]; group
  measurable_toFun := measurable_pi_lambda _ (fun l =>
    (((continuous_const.mul continuous_id).mul continuous_const).measurable).comp
      (measurable_pi_apply l))
  measurable_invFun := measurable_pi_lambda _ (fun l =>
    (((continuous_const.mul continuous_id).mul continuous_const).measurable).comp
      (measurable_pi_apply l))

/-- The site-dependent gauge transformation as a measurable equivalence of `Link d n → G`:
`linkTwoSidedEquiv` at the families `l ↦ g l.2` and `l ↦ (g (shift l.1 l.2))⁻¹`.

Being an equivalence, it is invertible for every `g`, with inverse the transformation by `g⁻¹`
pointwise.

DERIVED: no numeral. The `1` and `2` in `l.1`, `l.2` are the projections of `Link d n` onto its
direction and its base site. -/
noncomputable def gaugeEquiv (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (g : Site d n → G) : (Link d n → G) ≃ᵐ (Link d n → G) :=
  linkTwoSidedEquiv G (fun l : Link d n => g l.2) (fun l : Link d n => (g (shift l.1 l.2))⁻¹)

/-- `gaugeEquiv G g U = gaugeTransform g U`, by `rfl`: the equivalence and the plain function are the
same map, with the source-site element on the left and the inverted target-site element on the right.

DERIVED: no numeral. -/
theorem gaugeEquiv_apply (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (g : Site d n → G) (U : Link d n → G) :
    gaugeEquiv G g U = gaugeTransform g U := rfl

/-- `gaugeTransform (fun _ => a) U = confConj G a U`, by `rfl`: at a constant gauge element the
site-dependent action is exactly `CompactGauge.confConj`, conjugation of every link by `a`.

So `confConj` is the constant subgroup of the action defined here, definitionally rather than up to
an isomorphism.

DERIVED: no numeral. -/
theorem gaugeTransform_const (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (a : G) (U : Link d n → G) :
    gaugeTransform (fun _ : Site d n => a) U = confConj (ι := Link d n) G a U := rfl

/-- `gaugeEquiv G g` is measure-preserving for `Measure.pi (fun _ : Link d n => probHaar G)`.
`linkTwoSided_measurePreserving` at the two gauge families; `Link d n` is a `Fintype`, which is what
supplies the finiteness that lemma needs.

Holds for every `g`, with no condition relating the values of `g` at different sites.

DERIVED: no numeral. -/
theorem gaugeEquiv_measurePreserving (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    [NeZero n] (g : Site d n → G) :
    MeasurePreserving (gaugeEquiv G g) (Measure.pi fun _ : Link d n => probHaar G)
      (Measure.pi fun _ : Link d n => probHaar G) :=
  linkTwoSided_measurePreserving G _ _

/-! ### The Gibbs state under the site-dependent gauge group -/

/-- For every `g : Site d n → SU N`, every real `β` and every observable `O`, the Gibbs expectation
of `fun U => O (gaugeTransform g U)` equals that of `O`.

`System.expect_invariant_of_mp` applied to `gaugeEquiv_measurePreserving` (the measure is preserved)
and `boltz_gauge_invariant_local` (the weight is preserved).

`O` is arbitrary: it need not be gauge invariant, and need not be local. What is invariant is the
expectation of the transported observable, which is a statement about the state rather than about
`O`.

DERIVED: no numeral. -/
theorem expect_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N) (β : ℝ)
    (O : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (fun U => O (gaugeTransform g U))
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β O :=
  System.expect_invariant_of_mp _ (probHaar (MassGap.SUN.SU N)) β O
    (gaugeEquiv (MassGap.SUN.SU N) g) (gaugeEquiv_measurePreserving (MassGap.SUN.SU N) g)
    (fun U => boltz_gauge_invariant_local g β U)

/-! ### At `d = 4`, `N = 3` -/

/-- `expect_gauge_invariant_local` at `d = 4` and `N = 3`: the Gibbs expectation of the
four-dimensional `SU(3)` Wilson system is unchanged when the observable is transported by a
site-dependent gauge transformation.

The body is the general theorem; the two literals are the only difference.

DERIVED: `4` is the spatial dimension `d`, fixing the site type to `Site 4 n` and the direction type
to `Fin 4`. `3` is the `N` of `SU N`, the colour rank. Both are instantiations of the general
statement's variables, so neither is derived from anything within this file. -/
theorem clayState_gauge_invariant_local {n : ℕ} [NeZero n] (g : Site 4 n → MassGap.SUN.SU 3)
    (β : ℝ)
    (O : (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).Config → ℝ) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β (fun U => O (gaugeTransform g U))
      = (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β O :=
  expect_gauge_invariant_local g β O

/-- Building `WilsonBridge.corrClay n β lag` with both plaquette observables precomposed with
`gaugeTransform g` gives back `corrClay n β lag` itself, for every `g : Site 4 n → SU 3`, every real
`β` and every lag.

The connected form is spelled out in the statement: the expectation of the product minus the product
of the expectations, each observable being `wilsonPlaqObs` at the plane `(0, 1)`, one at the origin
site and one at `siteAtHyper 2 lag`. The proof rewrites every occurrence by
`plaqObs_gauge_invariant_local` and closes by `rfl`.

Both plaquettes carry the same ordered plane `(0, 1)`, so this is a correlator of one index pair.
`β` is unrestricted and `lag : Fin n`, so the separation wraps with the periodic extent.

DERIVED: `4` is the spatial dimension and `3` the colour rank, as in
`clayState_gauge_invariant_local`. `0` and `1` are the two directions of the ordered plane both
plaquettes are taken in, and the `0` in `fun _ => 0` is the base site, every coordinate at the
origin. `2` in `siteAtHyper 2 lag` names the axis the separation is taken along — a direction index
in `Fin 4`, distinct from the plane's `0` and `1`, so the separation is transverse to the
plaquette. -/
theorem corrClay_gauge_invariant_local {n : ℕ} [NeZero n] (β : ℝ) (lag : Fin n)
    (g : Site 4 n → MassGap.SUN.SU 3) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β
        (fun U => wilsonPlaqObs (N := 3) (bd (d := 4) (n := n))
              (((0, 1), fun _ => 0) : Plaq 4 n) (gaugeTransform g U)
            * wilsonPlaqObs (N := 3) (bd (d := 4) (n := n))
              (((0, 1), siteAtHyper 2 lag) : Plaq 4 n) (gaugeTransform g U))
      - (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
            (probHaar (MassGap.SUN.SU 3)) β
            (fun U => wilsonPlaqObs (N := 3) (bd (d := 4) (n := n))
              (((0, 1), fun _ => 0) : Plaq 4 n) (gaugeTransform g U))
        * (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
            (probHaar (MassGap.SUN.SU 3)) β
            (fun U => wilsonPlaqObs (N := 3) (bd (d := 4) (n := n))
              (((0, 1), siteAtHyper 2 lag) : Plaq 4 n) (gaugeTransform g U))
      = corrClay n β lag := by
  simp only [plaqObs_gauge_invariant_local]
  rfl

#print axioms shift_comm
#print axioms hol_gaugeTransform
#print axioms wilsonDensity_gaugeTransform
#print axioms plaqObs_gauge_invariant_local
#print axioms wilsonAction_gauge_invariant_local
#print axioms boltz_gauge_invariant_local
#print axioms linkTwoSided_measurePreserving
#print axioms gaugeEquiv_apply
#print axioms gaugeTransform_const
#print axioms gaugeEquiv_measurePreserving
#print axioms expect_gauge_invariant_local
#print axioms clayState_gauge_invariant_local
#print axioms corrClay_gauge_invariant_local

end MassGap.LocalGauge
