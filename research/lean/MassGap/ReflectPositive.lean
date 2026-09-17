import Mathlib
import MassGap.Reflect
import MassGap.WilsonBridge

/-!
# MassGap.ReflectPositive — the lag correlation IS a reflection pairing

`Complete.wilson_reflection_positive_at` asserts, of the constructed correlation
`wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β`, that it is nonnegative at every lag and has
positive total mass. This file identifies the first half of that assertion with the
Osterwalder–Seiler pairing inequality, on the reflection `Reflect.reflConf` the tree already builds.

## The identification

`corrClay` is `WilsonBridge.corrHyper` at `d = 4`, `Nc = 3`, plane `(0,1)`, lag axis `2`: the
CONNECTED correlation of the plaquette-energy observable at the origin with the same observable
displaced `lag` steps along the lag axis.

The displacement is not merely similar to a reflection — it IS one. `reflPlaq τ c` carries the
plaquette at the origin to the plaquette at `siteAtHyper τ c` (`reflPlaq_origin`), and the Wilson
density is a class function, so the displaced observable is the base observable composed with the
reflection of configurations (`plaqE_lag`). Hence

    corrHyper … lag  =  ⟨(φ₀ − ⟨φ₀⟩) · (φ₀ − ⟨φ₀⟩)∘θ⟩,   θ = reflConf τ lag

which is `corrHyper_eq_pairing`. That is exactly the quantity Osterwalder–Seiler prove nonnegative.

## What that buys, precisely

`corrHyper_nonneg_of_reflPositive` derives nonnegativity of the correlation from
`PlaqReflPositive` — the pairing inequality for ONE plaquette observable at ONE reflection constant.
`corrHyper_rp_of` assembles the shape of the axiom from that plus one strict-positivity input at lag
zero, and `sum_pos_of_head_pos` isolates what that second input has to be.

## The locality side condition, verified

The cited theorem applies to an observable supported on one side of the reflection plane.
`plaq_link_ne_refl` proves that no link of the base plaquette is fixed by the reflection whenever the
lag is nonzero: every link of a plaquette spanning two directions transverse to the reflection axis
sits at lag-coordinate `x τ`, and its mirror sits at `c − x τ`. So the observable and its reflection
read disjoint link sets, which is the hypothesis the citation needs and which nothing in the tree had
checked.

## What is NOT here, and why the axiom is not discharged

* The pairing inequality itself. `PlaqReflPositive` is a hypothesis.

* The ACTION SPLIT. `Reflect.reflect_action_invariant` gives `S(θU) = S(U)` — invariance of the
  Wilson action under the reflection. The Osterwalder–Seiler argument consumes something different:
  `S = S₊ + θS₊ + S₀`, the action written as a positive-half piece, its mirror, and the plaquettes
  meeting the plane. That split needs a partition of the link set into the two half-spaces and the
  plane, and no declaration in this development supplies one. Invariance follows from the split; the
  split does not follow from invariance.

* The MECHANISM at shared coordinates. `ReflectionPositivity.pairing_with_reflection_nonneg`
  concludes `∫ h·(h∘θ) = (∫ h)²` from `Disjoint S T` — the two halves read disjoint coordinates. Under
  a reflection whose plane passes through sites, the plane's transverse links are read by BOTH
  halves, so that lemma does not apply to the Wilson weight. What applies is the conditional form,
  `∫ over the plane of (∫ over the positive half of h)²`, and no three-block decomposition of the
  product Haar measure exists in the tree; `WilsonReal.block_integral_factor` is two-block and
  requires disjointness.

* A pairing inequality quantified over ALL bounded measurable observables is false, which is why
  `PlaqReflPositive` is not stated that way. `oddObs` builds an observable odd under the reflection
  — the difference of a function of two links the reflection exchanges — and
  `pairing_nonpos_of_odd` proves its pairing equals `−⟨O²⟩` and is nonpositive. Reflection positivity
  is a statement about observables supported on ONE SIDE of the plane, which is what
  `plaq_link_ne_refl` checks for the observable used here.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.ReflectPositive`.
-/

namespace MassGap.ReflectPositive

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic
open MassGap.WilsonBridge MassGap.Reflect
open MeasureTheory Finset

variable {d n Nc : ℕ}

/-! ### Linearity of the correlation numerator -/

/-- **The correlation numerator is linear**, in the one combination this file needs:

    ∫ (f−a)(g−a) e^{−βS} = ∫ fg e^{−βS} − a∫f e^{−βS} − a∫g e^{−βS} + a²Z.

Stated for an arbitrary `LatticeGauge.System` so that no Wilson-specific unfolding happens inside. -/
theorem corrNum_pair_sub_const {G : Type} [MeasurableSpace G] (sys : System G)
    (ν : Measure G) (β : ℝ) (f g : sys.Config → ℝ) (a : ℝ)
    (ifg : Integrable (fun U => (f U * g U) * sys.boltz β U) (sys.vol ν))
    (if' : Integrable (fun U => f U * sys.boltz β U) (sys.vol ν))
    (ig : Integrable (fun U => g U * sys.boltz β U) (sys.vol ν))
    (ib : Integrable (fun U => sys.boltz β U) (sys.vol ν)) :
    sys.corrNum ν β (fun U => (f U - a) * (g U - a))
      = sys.corrNum ν β (fun U => f U * g U) - a * sys.corrNum ν β f - a * sys.corrNum ν β g
        + a ^ 2 * sys.partition ν β := by
  have hsplit : ∀ U, ((f U - a) * (g U - a)) * sys.boltz β U
      = (f U * g U) * sys.boltz β U + ((-a) * (f U * sys.boltz β U)
        + ((-a) * (g U * sys.boltz β U) + a ^ 2 * sys.boltz β U)) := fun U => by ring
  have i2 : Integrable (fun U => (-a) * (f U * sys.boltz β U)) (sys.vol ν) := if'.const_mul (-a)
  have i3 : Integrable (fun U => (-a) * (g U * sys.boltz β U)) (sys.vol ν) := ig.const_mul (-a)
  have i4 : Integrable (fun U => a ^ 2 * sys.boltz β U) (sys.vol ν) := ib.const_mul (a ^ 2)
  have i34 : Integrable
      (fun U => (-a) * (g U * sys.boltz β U) + a ^ 2 * sys.boltz β U) (sys.vol ν) := i3.add i4
  have i234 : Integrable (fun U => (-a) * (f U * sys.boltz β U)
      + ((-a) * (g U * sys.boltz β U) + a ^ 2 * sys.boltz β U)) (sys.vol ν) := i2.add i34
  unfold System.corrNum System.partition
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add ifg i234, integral_add i2 i34, integral_add i3 i4,
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-! ### The hypercubic Wilson Gibbs state and its plaquette-energy observables -/

/-- The plaquette-energy observable of the `d`-dimensional periodic `SU(Nc)` Wilson lattice.

DERIVED: no numeral appears; `Nc`, `d`, `n` and the plaquette are the caller's. -/
noncomputable def plaqE (Nc : ℕ) {d n : ℕ} [NeZero n] (q : Plaq d n) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ :=
  wilsonPlaqObs (N := Nc) (bd (d := d) (n := n)) q

/-- The Gibbs expectation of that lattice, at coupling `β`.

DERIVED: no numeral appears; the coupling and the observable are the caller's. -/
noncomputable def EW (Nc : ℕ) {d n : ℕ} [NeZero n] (β : ℝ)
    (O : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ) : ℝ :=
  (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) β O

/-- **`corrHyper` written out**: the two-point function minus the product of one-point functions,
in the notation of this file. Definitional. -/
theorem corrHyper_unfold (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) :
    corrHyper (d := d) Nc n μ ν τ β lag
      = EW Nc β (fun U => plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
            * plaqE Nc (((μ, ν), siteAtHyper τ lag) : Plaq d n) U)
        - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))
          * EW Nc β (plaqE Nc (((μ, ν), siteAtHyper τ lag) : Plaq d n)) := rfl

theorem plaqE_nonneg (hNc : Nc ≠ 0) [NeZero n] (q : Plaq d n)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config) :
    0 ≤ plaqE Nc q U :=
  wilsonPlaqObs_nonneg hNc _ _ _

theorem plaqE_le_two (hNc : Nc ≠ 0) [NeZero n] (q : Plaq d n)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config) :
    plaqE Nc q U ≤ 2 :=
  wilsonPlaqObs_le_two hNc _ _ _

theorem measurable_plaqE [NeZero n] (q : Plaq d n) : Measurable (plaqE Nc q) :=
  measurable_wilsonPlaqObs _ _

theorem abs_plaqE_le_two (hNc : Nc ≠ 0) [NeZero n] (q : Plaq d n)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config) :
    |plaqE Nc q U| ≤ 2 := by
  rw [abs_of_nonneg (plaqE_nonneg hNc q U)]
  exact plaqE_le_two hNc q U

/-- **The centred pairing, expanded.** Linearity of the Gibbs state on two plaquette observables. -/
theorem EW_pair_sub_const (hNc : Nc ≠ 0) [NeZero n] (β : ℝ) (p q : Plaq d n) (a : ℝ) :
    EW Nc β (fun U => (plaqE Nc p U - a) * (plaqE Nc q U - a))
      = EW Nc β (fun U => plaqE Nc p U * plaqE Nc q U)
        - a * EW Nc β (plaqE Nc p) - a * EW Nc β (plaqE Nc q) + a ^ 2 := by
  have hZ : 0 < (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hNc _ β
  have ifg : Integrable (fun U => (plaqE Nc p U * plaqE Nc q U)
      * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_mul_boltz_integrable hNc _ β _
      ((measurable_plaqE p).mul (measurable_plaqE q)) 4 (fun U => by
        rw [abs_mul]
        exact le_trans (mul_le_mul (abs_plaqE_le_two hNc p U) (abs_plaqE_le_two hNc q U)
          (abs_nonneg _) (by norm_num)) (by norm_num))
  have ip : Integrable (fun U => plaqE Nc p U
      * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_mul_boltz_integrable hNc _ β _ (measurable_plaqE p) 2
      (abs_plaqE_le_two hNc p)
  have iq : Integrable (fun U => plaqE Nc q U
      * (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_mul_boltz_integrable hNc _ β _ (measurable_plaqE q) 2
      (abs_plaqE_le_two hNc q)
  have ib : Integrable (fun U =>
      (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).boltz β U)
      ((wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).vol
        (probHaar (MassGap.SUN.SU Nc))) := by
    have h := wilsonSystem_mul_boltz_integrable hNc (bd (d := d) (n := n)) β
      (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
    simpa using h
  have hlin := corrNum_pair_sub_const
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc)))
    (probHaar (MassGap.SUN.SU Nc)) β (plaqE Nc p) (plaqE Nc q) a ifg ip iq ib
  unfold EW System.expect
  rw [hlin]
  field_simp

/-! ### The lag displacement is a reflection -/

/-- **The reflection carries the plaquette at the origin to the plaquette at lag `c`.** The plane is
spanned by two directions transverse to the reflection axis, so `reflPlaq` takes its third branch and
acts on the base site alone; `reflSite τ c` sends the origin to `siteAtHyper τ c`. -/
theorem reflPlaq_origin [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c : Fin n) :
    reflPlaq τ c (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)
      = ((μ, ν), siteAtHyper τ c) := by
  have h : reflSite τ c (fun _ => (0 : Fin n)) = siteAtHyper (d := d) (n := n) τ c := by
    funext j
    by_cases hj : j = τ
    · subst hj
      simp [reflSite, siteAtHyper, sub_zero]
    · simp [reflSite, siteAtHyper, Function.update_of_ne hj]
  simp only [reflPlaq, hμ, hν, if_false, h]

/-- **A plaquette observable composed with the reflection is the reflected plaquette's observable.**
The mirrored holonomy is only CONJUGATE to the image plaquette's (`Reflect.hol_reflConf`), and the
Wilson density is a class function (`WilsonAction.wilsonDensity_conj`), so the two agree. -/
theorem plaqE_reflConf (Nc : ℕ) [NeZero n] (τ : Fin d) (c : Fin n)
    (q : Plaq d n) (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc q (reflConf τ c U) = plaqE Nc (reflPlaq τ c q) U := by
  obtain ⟨g, hg⟩ := hol_reflConf (G := MassGap.SUN.SU Nc) τ c q U
  show wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U))
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ c q) U)
  rw [hg, wilsonDensity_conj]

/-- **The lag-displaced observable is the base observable composed with the reflection.** -/
theorem plaqE_lag (Nc : ℕ) [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c : Fin n)
    (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc (((μ, ν), siteAtHyper τ c) : Plaq d n) U
      = plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (reflConf τ c U) := by
  rw [plaqE_reflConf Nc τ c, reflPlaq_origin hμ hν c]

/-- **The one-point function does not move with the lag** — the reflection preserves the Gibbs state
(`Reflect.expect_reflect_invariant`), so the displaced plaquette has the same mean energy. -/
theorem EW_plaqE_lag (Nc : ℕ) [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (c : Fin n) (β : ℝ) :
    EW Nc β (plaqE Nc (((μ, ν), siteAtHyper τ c) : Plaq d n))
      = EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)) := by
  have h : EW Nc β (fun U =>
        plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (reflConf τ c U))
      = EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)) :=
    expect_reflect_invariant (n := n) Nc τ c β
      (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))
  rw [← h]
  exact congrArg _ (funext fun U => plaqE_lag Nc hμ hν c U)

/-! ### The correlation IS the pairing -/

/-- **The connected lag correlation is the reflection pairing of the centred plaquette observable.**

    corrHyper … lag = ⟨(φ₀ − ⟨φ₀⟩) · (φ₀ − ⟨φ₀⟩)∘θ⟩,   θ = reflConf τ lag.

The right-hand side is the quantity Osterwalder–Seiler prove nonnegative. This is the identification
`Complete.wilson_reflection_positive_at`'s first conjunct was missing. -/
theorem corrHyper_eq_pairing (hNc : Nc ≠ 0) [NeZero n] {μ ν τ : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n) :
    corrHyper (d := d) Nc n μ ν τ β lag
      = EW Nc β (fun U =>
          (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
            - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
          * (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (reflConf τ lag U)
            - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))) := by
  have hmean := EW_plaqE_lag (n := n) Nc hμ hν lag β
  have hfun : (fun U =>
        (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
        * (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (reflConf τ lag U)
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))))
      = (fun U =>
        (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
        * (plaqE Nc (((μ, ν), siteAtHyper τ lag) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))) :=
    funext fun U => by rw [plaqE_lag Nc hμ hν lag U]
  rw [hfun, EW_pair_sub_const hNc β
    (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (((μ, ν), siteAtHyper τ lag) : Plaq d n) _,
    hmean, corrHyper_unfold Nc μ ν τ β lag, hmean]
  ring

/-! ### The reduction -/

/-- **The Osterwalder–Seiler pairing inequality, at one plaquette and one reflection constant.**

`0 ≤ ⟨F · F∘θ⟩` for `F` the plaquette-energy observable of `q` centred at any constant, and `θ` the
reflection with constant `c`. This is the cited content in its textbook form — nonnegativity of an
observable paired with its own reflection — narrowed to the single observable this development uses.
Its locality side condition is checked by `plaq_link_ne_refl`.

DERIVED: the only numeral is the `0` of `0 ≤ …`, which IS positive-semidefiniteness — the definition
of the property, not a threshold chosen for it. Nothing else here carries a magnitude: `a` is the
caller's centring constant, `c` the caller's reflection constant. -/
def PlaqReflPositive (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (q : Plaq d n) : Prop :=
  ∀ a : ℝ, 0 ≤ EW Nc β (fun U => (plaqE Nc q U - a) * (plaqE Nc q (reflConf τ c U) - a))

/-- **The correlation is nonnegative if the pairing is** — the reduction, at one lag. -/
theorem corrHyper_nonneg_of_reflPositive (hNc : Nc ≠ 0) [NeZero n] {μ ν τ : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n)
    (hRP : PlaqReflPositive Nc τ lag β (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)) :
    0 ≤ corrHyper (d := d) Nc n μ ν τ β lag := by
  rw [corrHyper_eq_pairing hNc hμ hν β lag]
  exact hRP _

/-! ### The locality side condition -/

/-- Every link of a plaquette spanning two directions transverse to the reflection axis sits at the
same lag-coordinate as the plaquette's base site: stepping in `μ` or `ν` does not move the `τ`
coordinate. -/
theorem bd_link_tau_coord [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (x : Site d n)
    (l : Link d n) (hl : l ∈ (bd (((μ, ν), x) : Plaq d n)).map Prod.fst) :
    l.2 τ = x τ := by
  have hsμ : (WilsonHypercubic.shift μ x) τ = x τ := by
    simp [WilsonHypercubic.shift, Function.update_of_ne (Ne.symm hμ)]
  have hsν : (WilsonHypercubic.shift ν x) τ = x τ := by
    simp [WilsonHypercubic.shift, Function.update_of_ne (Ne.symm hν)]
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h <;> subst h
  exacts [rfl, hsμ, hsν, rfl]

/-- Every link of such a plaquette runs in a direction transverse to the reflection axis. -/
theorem bd_link_dir_ne [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (x : Site d n)
    (l : Link d n) (hl : l ∈ (bd (((μ, ν), x) : Plaq d n)).map Prod.fst) : l.1 ≠ τ := by
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h <;> subst h
  exacts [hμ, hν, hμ, hν]

/-- **The reflected link's lag-coordinate is `c − x τ`** for a link transverse to the axis. -/
theorem reflLink_tau_coord [NeZero n] {τ : Fin d} (c : Fin n) (l : Link d n) (h : l.1 ≠ τ) :
    (reflLink τ c l).2 τ = c - l.2 τ := by
  simp [reflLink, h, reflSite]

/-- **No link of the base plaquette is fixed by the reflection, once the lag is nonzero.**

This is the locality side condition the cited theorem needs, verified on this geometry: the base
plaquette's links all sit at lag-coordinate `0` (`bd_link_tau_coord`), their mirrors all sit at
lag-coordinate `c` (`reflLink_tau_coord`), so the observable and its reflection read disjoint sets of
link variables whenever `c ≠ 0`. -/
theorem plaq_link_ne_refl [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) {c : Fin n}
    (hc : c ≠ 0) (l : Link d n)
    (hl : l ∈ (bd (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)).map Prod.fst) :
    reflLink τ c l ≠ l := by
  have h0 : l.2 τ = 0 := bd_link_tau_coord hμ hν _ l hl
  have hne : l.1 ≠ τ := bd_link_dir_ne hμ hν _ l hl
  intro hcon
  have h1 : (reflLink τ c l).2 τ = c - l.2 τ := reflLink_tau_coord c l hne
  rw [hcon, h0, sub_zero] at h1
  exact hc h1.symm

/-! ### Why the pairing inequality cannot be stated observable-free

Reflection positivity is a statement about observables supported on ONE SIDE of the reflection plane.
Dropping that restriction makes it false, and the witness is elementary: an observable ODD under the
reflection pairs to minus a square. The three declarations below construct such an observable on this
geometry and prove its pairing nonpositive, which is why `PlaqReflPositive` quantifies over one
plaquette rather than over all observables.
-/

/-- The difference of a function of a link and of its mirror — odd under the reflection by
construction.

DERIVED: no numeral appears; the link, the reflection constant and the scalar function are the
caller's. -/
noncomputable def oddObs (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n)
    (g : MassGap.SUN.SU Nc → ℝ) (l : Link d n) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ :=
  fun U => g (U l) - g (U (reflLink τ c l))

/-- **It is odd**, for a link transverse to the reflection axis (where `reflConf` carries no
dagger). -/
theorem oddObs_odd (Nc : ℕ) [NeZero n] {τ : Fin d} (c : Fin n) (g : MassGap.SUN.SU Nc → ℝ)
    (l : Link d n) (hl : l.1 ≠ τ)
    (U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config) :
    oddObs Nc τ c g l (reflConf τ c U) = - oddObs Nc τ c g l U := by
  have hfst : (reflLink τ c l).1 = l.1 := rfl
  have h1 : reflConf τ c U l = U (reflLink τ c l) := by
    simp only [reflConf, if_neg hl]
  have h2 : reflConf τ c U (reflLink τ c l) = U l := by
    simp only [reflConf, hfst, if_neg hl, reflLink_involutive τ c l]
  show g (reflConf τ c U l) - g (reflConf τ c U (reflLink τ c l))
      = -(g (U l) - g (U (reflLink τ c l)))
  rw [h1, h2]
  ring

/-- **An odd observable pairs to minus a square, hence nonpositively.**

So a reflection-positivity statement quantified over every bounded measurable observable is false for
this measure, and the restriction to observables supported on one side of the plane is not
decoration. `plaq_link_ne_refl` is the check that the observable `PlaqReflPositive` is stated about
does satisfy it. -/
theorem pairing_nonpos_of_odd (hNc : Nc ≠ 0) [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (O : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ)
    (hodd : ∀ U, O (reflConf τ c U) = - O U) :
    EW Nc β (fun U => O U * O (reflConf τ c U)) = - EW Nc β (fun U => O U * O U)
      ∧ EW Nc β (fun U => O U * O (reflConf τ c U)) ≤ 0 := by
  have hrw : (fun U => O U * O (reflConf τ c U))
      = (fun U : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config =>
          (-1 : ℝ) * (O U * O U)) :=
    funext fun U => by rw [hodd U]; ring
  have heq : EW Nc β (fun U => O U * O (reflConf τ c U)) = - EW Nc β (fun U => O U * O U) := by
    unfold EW
    rw [hrw, wilsonSystem_expect_smul]
    ring
  refine ⟨heq, ?_⟩
  rw [heq, neg_nonpos]
  exact wilsonSystem_expect_nonneg hNc _ β _ (fun U => mul_self_nonneg _)

/-! ### What the second conjunct needs, and what it does not get from reflection positivity -/

/-- **Nonnegativity at every lag plus strict positivity at lag zero gives positive total mass.**

Stated separately because the two conjuncts of `Complete.wilson_reflection_positive_at` have
different provenance: the first is reflection positivity, the second is not implied by it at all. A
correlation that vanishes identically satisfies reflection positivity and fails this. -/
theorem sum_pos_of_head_pos {m : ℕ} (ρ : Fin (m + 1) → ℝ) (hnn : ∀ k, 0 ≤ ρ k) (h0 : 0 < ρ 0) :
    0 < ∑ k, ρ k :=
  Finset.sum_pos' (fun k _ => hnn k) ⟨0, Finset.mem_univ 0, h0⟩

/-- **The shape of the axiom, from the pairing inequality plus one strict-positivity input.**

Given the Osterwalder–Seiler pairing inequality at every lag, and `0 < ρ(0)` — which is
`0 < Var(φ₀)`, the statement that the plaquette energy is not almost surely constant — the
correlation is nonnegative at every lag and has positive total mass. That is exactly the conjunction
`Complete.wilson_reflection_positive_at` asserts, for `corrHyper` in place of `wilsonCorrAt`; at
`d = 4`, `Nc = 3`, plane `(0,1)`, axis `2`, extent `N+1` the two are the same function by
`WilsonBridge.corrClay` and `Complete.wilsonCorrAt`, both of which are definitional. -/
theorem corrHyper_rp_of (hNc : Nc ≠ 0) {m : ℕ} {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    (hRP : ∀ lag : Fin (m + 1),
      PlaqReflPositive Nc τ lag β (((μ, ν), (fun _ => 0 : Site d (m + 1))) : Plaq d (m + 1)))
    (h0 : 0 < corrHyper (d := d) Nc (m + 1) μ ν τ β 0) :
    (∀ lag, 0 ≤ corrHyper (d := d) Nc (m + 1) μ ν τ β lag)
      ∧ 0 < ∑ lag, corrHyper (d := d) Nc (m + 1) μ ν τ β lag := by
  have hnn : ∀ lag, 0 ≤ corrHyper (d := d) Nc (m + 1) μ ν τ β lag := fun lag =>
    corrHyper_nonneg_of_reflPositive hNc hμ hν β lag (hRP lag)
  exact ⟨hnn, sum_pos_of_head_pos _ hnn h0⟩

/-! ### At the Clay problem's own parameters

`WilsonBridge.corrClay` is `corrHyper` at `d = 4`, `Nc = 3`, plane `(0,1)`, lag axis `2`, and
`Complete.wilsonCorrAt N β = corrClay (N+1) β` by definition. So the theorem below is the axiom
`Complete.wilson_reflection_positive_at` with its two conjuncts traced to their two different
sources.
-/

/-- **The axiom's statement, reduced to the pairing inequality plus one strict-positivity input.**

`corrClay` is the function `Complete.wilsonCorrAt` is defined to be, so this is exactly the
conjunction `Complete.wilson_reflection_positive_at` asserts, derived from

* `hRP` — the Osterwalder–Seiler pairing inequality for the single plaquette-energy observable of the
  base plaquette, at each reflection constant; and
* `h0` — strict positivity of the correlation at lag zero, which is `0 < Var(φ₀)`: the plaquette
  energy is not almost surely constant under the Gibbs measure.

Reflection positivity says nothing about `h0`: the identically-zero correlation satisfies every
pairing inequality and fails `h0`. The two conjuncts of the axiom have different provenance and only
the first is Osterwalder–Seiler. -/
theorem corrClay_rp_of (N : ℕ) (β : ℝ)
    (hRP : ∀ lag : Fin (N + 1), PlaqReflPositive 3 (2 : Fin 4) lag β
      ((((0 : Fin 4), (1 : Fin 4)), (fun _ => 0 : Site 4 (N + 1))) : Plaq 4 (N + 1)))
    (h0 : 0 < corrClay (N + 1) β 0) :
    (∀ lag, 0 ≤ corrClay (N + 1) β lag) ∧ 0 < ∑ lag, corrClay (N + 1) β lag :=
  corrHyper_rp_of (Nc := 3) (d := 4) (m := N) (by norm_num)
    (μ := 0) (ν := 1) (τ := 2) (by decide) (by decide) β hRP h0

section Audit
#print axioms corrNum_pair_sub_const
#print axioms EW_pair_sub_const
#print axioms reflPlaq_origin
#print axioms plaqE_reflConf
#print axioms plaqE_lag
#print axioms EW_plaqE_lag
#print axioms corrHyper_unfold
#print axioms corrHyper_eq_pairing
#print axioms corrHyper_nonneg_of_reflPositive
#print axioms bd_link_tau_coord
#print axioms bd_link_dir_ne
#print axioms reflLink_tau_coord
#print axioms plaq_link_ne_refl
#print axioms sum_pos_of_head_pos
#print axioms corrHyper_rp_of
#print axioms corrClay_rp_of
#print axioms oddObs_odd
#print axioms pairing_nonpos_of_odd
end Audit

end MassGap.ReflectPositive
