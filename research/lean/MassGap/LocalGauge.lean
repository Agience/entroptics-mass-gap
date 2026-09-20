import Mathlib
import MassGap.WilsonBridge

/-!
# MassGap.LocalGauge — the LOCAL (site-dependent) gauge group of the hypercubic Wilson lattice

Every gauge-invariance statement elsewhere in this development is about `CompactGauge.confConj`,
which conjugates every link by ONE constant group element. That is the global subgroup. The gauge
group of a lattice gauge theory is larger: it carries one group element per SITE, and acts by

    U_μ(x)  ↦  g(x) · U_μ(x) · g(x + μ̂)⁻¹.

This file defines that action (`gaugeTransform`) on `WilsonHypercubic.Link`, and proves that the
plaquette holonomy transforms by conjugation at the plaquette's base point (`hol_gaugeTransform`) —
the interior `g`s cancel telescopically because the boundary word is a closed loop and because the
two unit shifts commute (`shift_comm`). Everything else follows: `wilsonDensity` is a class function,
so the plaquette observable is invariant pointwise; the action is the sum of those, so the Boltzmann
weight is invariant; and the transformation is a per-link left-and-right translation, so it preserves
the product Haar measure and therefore the whole Gibbs state.

The payoff, `corrClay_gauge_invariant_local`, is that `WilsonBridge.corrClay` — the constructed
four-dimensional `SU(3)` connected plaquette correlation — is a correlation function of local
operators that are invariant under the genuine local gauge group, not merely under the constant one.

## What Clay row A8 still lacks after this file

Jaffe–Witten ask for "local quantum field operators in correspondence with the gauge-invariant local
polynomials in the curvature `F` and its covariant derivatives, such as `Tr F_ij F_kl(x)`." What is
here is a lattice object, and four things are still missing.

* **There is no `F`.** No definition in this tree constructs a curvature two-form, a covariant
  derivative, or any polynomial in them. The identification of the plaquette with a discretised
  `Tr F F` is prose only (`research/PAPER.md`, the weak-coupling paragraph beginning "The
  weak-coupling limit is computed", around line 756), and there it is stated only for the `β → ∞`
  free-field limit. No Lean statement relates `plaqE`/`wilsonPlaqObs` to any `F`.
* **The index pairs are not independent.** `corrHyper` takes a single ordered plane `(μ, ν)` and
  uses it for BOTH plaquettes, so `corrClay` is shaped like `⟨O_{01}(0) O_{01}(x)⟩`, never like
  `⟨Tr F_ij F_kl⟩` with an independent second pair. Nothing here constructs the mixed-index object.
* **There are no quantum field operators on a Hilbert space.** Everything in this file is a
  real-valued function on a finite Euclidean configuration space integrated against a Gibbs measure.
  No Osterwalder–Schrader reconstruction to operators on a Hilbert space is performed here.
* **The lattice is finite and periodic.** `n` is an extent and there is no continuum limit; the
  gauge group proved to act here is the lattice gauge group at fixed `n`.

What this file does close is exactly one thing: the gauge invariance of the constructed correlator
is now under the site-dependent group, which is the group A8 means.

Foundational footprint only (`#print axioms` at the end).
Build: `python research/code/lean_build.py build MassGap.LocalGauge`.
-/

namespace MassGap.LocalGauge

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory Measure

variable {d n : ℕ}

/-! ### The two unit shifts of a plaquette commute

This is the whole geometric content of the telescoping: the plaquette loop closes, i.e. going one
step along `μ` then one along `ν` lands on the same site as the other order, so the two `g`s at the
far corner are the same element and cancel. -/

/-- **Unit shifts commute.** `shift` updates one coordinate, so two shifts in different directions
are updates at different indices (which commute), and two shifts in the same direction are the same
expression either way. -/
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

/-- **The local (site-dependent) gauge transformation.**

A link is `(direction, base site)`, and `WilsonHypercubic.bd` traverses it from its base site `x` to
`shift μ x`. So a gauge element `g : Site → G` acts on the link by `g` at the source and `g⁻¹` at the
target: `U_μ(x) ↦ g(x) · U_μ(x) · g(x + μ̂)⁻¹`.

This is the genuine lattice gauge group. `CompactGauge.confConj` is the constant-`g` subgroup of it:
for `g` constant the target factor is the same element as the source factor and the action collapses
to conjugation. -/
def gaugeTransform {G : Type} [Group G] [MeasurableSpace G] [NeZero n]
    (g : Site d n → G) (U : Link d n → G) : Link d n → G :=
  fun l => g l.2 * U l * (g (shift l.1 l.2))⁻¹

/-- **The plaquette holonomy is conjugated by the gauge element at its BASE POINT.**

`hol q (gaugeTransform g U) = g(x) · hol q U · g(x)⁻¹` where `x = q.2` is the plaquette's base site.
The proof is the telescoping: writing the four boundary factors out,

    (g_x A g_μ⁻¹) · (g_μ B g_{νμ}⁻¹) · (g_ν C g_{μν}⁻¹)⁻¹ · (g_x D g_ν⁻¹)⁻¹

the `g_μ` pair cancels between the first two factors, the `g_ν` pair between the last two, and the
far-corner pair `g_{νμ}`, `g_{μν}` cancels because the shifts commute (`shift_comm`) — which is the
statement that the loop closes. What survives is `g_x` on the left and `g_x⁻¹` on the right. -/
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

/-- **The Wilson plaquette density is invariant under a LOCAL gauge transformation.** The holonomy is
conjugated (`hol_gaugeTransform`) and `wilsonDensity` is a class function (`wilsonDensity_conj`, from
trace cyclicity), so the density does not move at all. -/
theorem wilsonDensity_gaugeTransform {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (U : Link d n → MassGap.SUN.SU N) (q : Plaq d n) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (gaugeTransform g U))
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  rw [hol_gaugeTransform]
  exact wilsonDensity_conj _ _

/-- **The plaquette observable is a LOCAL gauge-invariant operator.** This is the A8 property of the
operator itself: `wilsonPlaqObs` reads only the four links of its own plaquette
(`ReflectionPositivity.hol_congr_on_support`) and is unchanged by every site-dependent gauge
transformation, not merely by the constant ones. -/
theorem plaqObs_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (q : Plaq d n)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    wilsonPlaqObs (N := N) (bd (d := d) (n := n)) q (gaugeTransform g U)
      = wilsonPlaqObs (N := N) (bd (d := d) (n := n)) q U :=
  wilsonDensity_gaugeTransform g U q

/-- **The full Wilson action is invariant under a local gauge transformation** — every plaquette term
is, and the action is their sum over the `d²·n^d` plaquettes. -/
theorem wilsonAction_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).action (gaugeTransform g U)
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).action U :=
  Finset.sum_congr rfl (fun q _ => wilsonDensity_gaugeTransform g U q)

/-- The Boltzmann weight is invariant under a local gauge transformation. -/
theorem boltz_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N) (β : ℝ)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).boltz β (gaugeTransform g U)
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).boltz β U := by
  unfold System.boltz
  rw [wilsonAction_gauge_invariant_local]

/-! ### The measure side: the local gauge transformation preserves the product Haar measure

The gauge transformation is, per link, a LEFT translation by `g(x)` followed by a RIGHT translation
by `g(x + μ̂)⁻¹`. On a compact group the probability Haar measure is invariant under both
(`CompactGauge.isMulLeftInvariant_probHaar`, `CompactGauge.isMulRightInvariant_probHaar`, the latter
from unimodularity), and the product measure is preserved coordinatewise. Unlike `confConj` the two
translating elements differ from link to link, so the per-link maps form a family rather than a
constant; that is the only difference from `CompactGauge.confConj_measurePreserving`. -/

/-- A per-coordinate two-sided translation of a configuration: `U ↦ (l ↦ a l · U l · b l)`. -/
def linkTwoSided (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    {ι : Type} (a b : ι → G) (U : ι → G) : ι → G :=
  fun l => a l * U l * b l

/-- **A per-link two-sided translation preserves the product Haar measure.** Each coordinate map
`u ↦ a l · u · b l` is left-then-right translation, measure-preserving by left- and right-invariance
of `probHaar`; `Measure.pi_map_pi` assembles the coordinates. -/
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

/-- The per-link translation as a MEASURABLE EQUIVALENCE (inverse: translate by the inverses). -/
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

/-- **The local gauge transformation as a measurable equivalence of configurations.** -/
noncomputable def gaugeEquiv (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (g : Site d n → G) : (Link d n → G) ≃ᵐ (Link d n → G) :=
  linkTwoSidedEquiv G (fun l : Link d n => g l.2) (fun l : Link d n => (g (shift l.1 l.2))⁻¹)

/-- `gaugeEquiv` really is `gaugeTransform`: source-site left factor, target-site right factor. -/
theorem gaugeEquiv_apply (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (g : Site d n → G) (U : Link d n → G) :
    gaugeEquiv G g U = gaugeTransform g U := rfl

/-- A constant gauge element acts by conjugation — `CompactGauge.confConj` is the constant subgroup
of the local gauge group defined here, and nothing else in the tree acts by more than that. -/
theorem gaugeTransform_const (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [NeZero n]
    (a : G) (U : Link d n → G) :
    gaugeTransform (fun _ : Site d n => a) U = confConj (ι := Link d n) G a U := rfl

/-- **The local gauge transformation preserves the lattice measure.** -/
theorem gaugeEquiv_measurePreserving (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G]
    [NeZero n] (g : Site d n → G) :
    MeasurePreserving (gaugeEquiv G g) (Measure.pi fun _ : Link d n => probHaar G)
      (Measure.pi fun _ : Link d n => probHaar G) :=
  linkTwoSided_measurePreserving G _ _

/-! ### The Gibbs state of the hypercubic Wilson lattice is locally gauge invariant -/

/-- **The Gibbs expectation is invariant under the LOCAL gauge group.** For ANY observable — not only
gauge-invariant ones — transporting it by a site-dependent gauge transformation leaves the
expectation unchanged: the transformation preserves the product Haar measure
(`gaugeEquiv_measurePreserving`) and the Wilson action (`boltz_gauge_invariant_local`), so
`System.expect_invariant_of_mp` applies. This is the defining symmetry of a gauge theory, on the
genuine gauge group rather than its constant subgroup. -/
theorem expect_gauge_invariant_local {N : ℕ} [NeZero n] (g : Site d n → MassGap.SUN.SU N) (β : ℝ)
    (O : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (fun U => O (gaugeTransform g U))
      = (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β O :=
  System.expect_invariant_of_mp _ (probHaar (MassGap.SUN.SU N)) β O
    (gaugeEquiv (MassGap.SUN.SU N) g) (gaugeEquiv_measurePreserving (MassGap.SUN.SU N) g)
    (fun U => boltz_gauge_invariant_local g β U)

/-! ### The payoff: `corrClay` is a correlator of local gauge-invariant operators -/

/-- **The four-dimensional `SU(3)` Gibbs state is invariant under the local gauge group.** The
`d = 4`, `N = 3` instance — the Clay problem's own lattice — of `expect_gauge_invariant_local`. -/
theorem clayState_gauge_invariant_local {n : ℕ} [NeZero n] (g : Site 4 n → MassGap.SUN.SU 3)
    (β : ℝ)
    (O : (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).Config → ℝ) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β (fun U => O (gaugeTransform g U))
      = (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β O :=
  expect_gauge_invariant_local g β O

/-- **THE PAYOFF.** `WilsonBridge.corrClay` — the connected two-point function of the plaquette
observable of four-dimensional `SU(3)` Wilson lattice gauge theory, at an ordered plane and a genuine
spatial separation — is unchanged when both operators are composed with an arbitrary site-dependent
gauge transformation. Its operators are therefore LOCAL (each reads only its own four links) and
GAUGE-INVARIANT under the genuine local gauge group, which is the correspondence Clay row A8 asks
for at the operator level. What it is not is `Tr F_ij F_kl`; see the header for exactly what is
still missing. -/
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
