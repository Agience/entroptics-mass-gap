import Mathlib
import MassGap.Reflect
import MassGap.WilsonBridge

/-!
# MassGap.ReflectPositive — the connected lag correlation written as a reflection pairing

`WilsonBridge.corrHyper Nc n μ ν τ β lag` is the connected correlation of the plaquette-energy
observable at the origin with the same observable displaced `lag` steps along the axis `τ`. This
file rewrites it as a pairing of one observable with its own image under `Reflect.reflConf`, and
reduces its nonnegativity to a single hypothesis about that pairing.

## The rewriting

`plaqE Nc q` is the plaquette-energy observable and `EW Nc β` the Gibbs expectation of the
hypercubic Wilson system. `reflPlaq_origin` sends the base plaquette to the plaquette at
`siteAtHyper τ c`; `plaqE_reflConf` moves the reflection from the plaquette onto the configuration,
using that the mirrored holonomy is conjugate (`Reflect.hol_reflConf`) and that `wilsonDensity` is a
class function; `plaqE_lag` combines them. `EW_plaqE_lag` shows the one-point function does not
move, from `Reflect.expect_reflect_invariant`. `corrNum_pair_sub_const` and `EW_pair_sub_const`
supply the linearity, and `corrHyper_eq_pairing` is the resulting identity

    corrHyper … lag = EW ((φ₀ − ⟨φ₀⟩) * ((φ₀ − ⟨φ₀⟩) ∘ reflConf τ lag)).

## The reduction

`PlaqReflPositive Nc τ c β q` is the hypothesis `0 ≤ EW ((φ_q − a) * ((φ_q − a) ∘ reflConf τ c))`
for every centring constant `a`. `corrHyper_nonneg_of_reflPositive` turns it into
`0 ≤ corrHyper … lag`; `sum_pos_of_head_pos` adds nonnegativity at every lag to strict positivity at
lag zero to get a positive total; `corrHyper_rp_of` and `corrClay_rp_of` assemble both, the latter at
`Nc = 3`, `d = 4`, plane `(0, 1)`, axis `2`.

## The locality of the base plaquette

`bd_link_tau_coord` and `bd_link_dir_ne` say every link of a plaquette spanning two directions
transverse to `τ` runs transverse to `τ` and sits at the plaquette's own `τ`-coordinate;
`reflLink_tau_coord` puts its mirror at `c − x τ`; `plaq_link_ne_refl` concludes that no link of the
base plaquette is fixed by the reflection once `c ≠ 0`.

## Odd observables

`oddObs` is the difference of a function of a link and of its mirror, `oddObs_odd` shows it changes
sign under `reflConf` for a transverse link, and `pairing_nonpos_of_odd` computes its pairing as
`- EW (O * O) ≤ 0`. So a pairing inequality quantified over all bounded measurable observables of
this measure does not hold, which is why `PlaqReflPositive` names one plaquette.

Scope: `PlaqReflPositive` is a hypothesis in every theorem that uses it; no declaration here proves
it, and no action split `S = S₊ + θS₊ + S₀` is constructed. `Reflect.reflect_action_invariant` gives
invariance of the action, which is a different statement.
`ReflectionPositivity.pairing_with_reflection_nonneg` requires two disjoint blocks of links and so
does not apply to a reflection plane passing through sites. The strict positivity `h0` at lag zero
is a separate hypothesis: a correlation that vanishes identically satisfies every pairing inequality
and fails it. Axiom footprints are printed in the `Audit` section.
-/

namespace MassGap.ReflectPositive

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic
open MassGap.WilsonBridge MassGap.Reflect
open MeasureTheory Finset

variable {d n Nc : ℕ}

/-! ### Linearity of the correlation numerator -/

/-- For a `LatticeGauge.System sys`, a measure `ν`, a coupling `β`, observables `f`, `g` and a
constant `a`, given integrability of `f * g * boltz`, of `f * boltz`, of `g * boltz` and of `boltz`,

    corrNum ν β ((f - a) * (g - a))
      = corrNum ν β (f * g) - a * corrNum ν β f - a * corrNum ν β g + a ^ 2 * partition ν β.

The integrand is split by `ring` into four pieces and the integral distributed across them, which is
what the four integrability hypotheses are for.

Scope: stated for an arbitrary `System`, so nothing Wilson-specific is unfolded inside. The
normalisation is `corrNum` (unnormalised), which is why the constant term carries the partition
function rather than `1`.

DERIVED: the exponent `2` is the square on the constant `a`, the term left when both factors
contribute their `-a`. No other numeral appears in the statement. -/
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

/-! ### The plaquette-energy observable and the Gibbs expectation it is read against -/

/-- `WilsonReal.wilsonPlaqObs` at the hypercubic boundary word: the plaquette-energy observable
of `q` on the `d`-dimensional periodic lattice of extent `n` over `SU Nc`. Its range is `[0, 2]`
(`plaqE_nonneg`, `plaqE_le_two`) and it is measurable (`measurable_plaqE`).

DERIVED: no numeral appears in the statement; `Nc`, `d`, `n` and the plaquette `q` are the
caller's. -/
noncomputable def plaqE (Nc : ℕ) {d n : ℕ} [NeZero n] (q : Plaq d n) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ :=
  wilsonPlaqObs (N := Nc) (bd (d := d) (n := n)) q

/-- The Gibbs expectation of the hypercubic Wilson system at coupling `β`, taken against the product
Haar measure `probHaar (SUN.SU Nc)`: `System.expect` at that system and measure.

Scope: `β` is an arbitrary real, of either sign; the measure is fixed at product Haar.

DERIVED: no numeral appears in the statement; the coupling and the observable are the caller's. -/
noncomputable def EW (Nc : ℕ) {d n : ℕ} [NeZero n] (β : ℝ)
    (O : (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ) : ℝ :=
  (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) β O

/-- `corrHyper Nc n μ ν τ β lag` written in this file's notation: the expectation of the product of
the base plaquette's observable and the observable at `siteAtHyper τ lag`, minus the product of the
two one-point functions. Proved by `rfl`, so it is a change of notation rather than a computation.

DERIVED: `0` occurs twice, as the origin site `fun _ => 0` of the base plaquette in the two-point
term and again in the one-point term. -/
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

/-- For `Nc ≠ 0` and two plaquettes `p`, `q`,

    EW Nc β ((plaqE p - a) * (plaqE q - a))
      = EW Nc β (plaqE p * plaqE q) - a * EW Nc β (plaqE p) - a * EW Nc β (plaqE q) + a ^ 2.

It is `corrNum_pair_sub_const` divided through by the partition function, which
`wilsonSystem_partition_pos` makes nonzero. The four integrability hypotheses are discharged from
`abs_plaqE_le_two` through `wilsonSystem_mul_boltz_integrable`, at sup-norm bounds `4`, `2`, `2` and
`1` respectively.

Scope: `hNc : Nc ≠ 0` is what makes the partition function positive. No relation between `p` and `q`
is assumed.

DERIVED: `0` is the value `Nc` is assumed to differ from; the exponent `2` is the square on the
centring constant `a`. The sup-norm bounds used in the proof do not appear in the statement. -/
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

/-! ### Rewriting the lag displacement through `Reflect.reflConf` -/

/-- For plaquette directions `μ`, `ν` both distinct from the reflection axis `τ`,
`reflPlaq τ c ((μ, ν), fun _ => 0) = ((μ, ν), siteAtHyper τ c)`. Both `hμ` and `hν` send `reflPlaq`
into its third branch, where it acts on the base site alone, and `reflSite τ c` carries the origin
to `siteAtHyper τ c`.

Scope: the hypotheses `hμ`, `hν` are what select that branch; a plaquette with a direction along `τ`
is not covered.

DERIVED: `0` is the origin site `fun _ => 0` the reflection is applied to. -/
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

/-- `plaqE Nc q (reflConf τ c U) = plaqE Nc (reflPlaq τ c q) U` at every plaquette `q` and
configuration `U`. `Reflect.hol_reflConf` gives a group element `g` conjugating the two holonomies,
and `WilsonAction.wilsonDensity_conj` says the density does not see it.

Scope: the two holonomies are conjugate, not equal — the statement holds because the observable is a
class function, and would fail for one that is not.

DERIVED: no numeral appears in the statement. -/
theorem plaqE_reflConf (Nc : ℕ) [NeZero n] (τ : Fin d) (c : Fin n)
    (q : Plaq d n) (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc q (reflConf τ c U) = plaqE Nc (reflPlaq τ c q) U := by
  obtain ⟨g, hg⟩ := hol_reflConf (G := MassGap.SUN.SU Nc) τ c q U
  show wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U))
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ c q) U)
  rw [hg, wilsonDensity_conj]

/-- For `μ`, `ν` distinct from `τ`,
`plaqE Nc ((μ, ν), siteAtHyper τ c) U = plaqE Nc ((μ, ν), fun _ => 0) (reflConf τ c U)`:
the displaced observable is the base observable read on the reflected configuration.
`plaqE_reflConf` moves the reflection and `reflPlaq_origin` identifies the image plaquette.

DERIVED: `0` is the origin site `fun _ => 0` of the base plaquette. -/
theorem plaqE_lag (Nc : ℕ) [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c : Fin n)
    (U : Link d n → MassGap.SUN.SU Nc) :
    plaqE Nc (((μ, ν), siteAtHyper τ c) : Plaq d n) U
      = plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (reflConf τ c U) := by
  rw [plaqE_reflConf Nc τ c, reflPlaq_origin hμ hν c]

/-- `EW Nc β (plaqE Nc ((μ, ν), siteAtHyper τ c)) = EW Nc β (plaqE Nc ((μ, ν), fun _ => 0))` for
`μ`, `ν` distinct from `τ`: the one-point function is the same at the displaced plaquette as at the
base one. `plaqE_lag` rewrites the displaced observable as the base one composed with `reflConf`, and
`Reflect.expect_reflect_invariant` says the Gibbs expectation is unchanged by that composition.

DERIVED: `0` occurs twice, as the origin site `fun _ => 0` on each side of the equation. -/
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

/-! ### The identity: the connected correlation as a reflection pairing -/

/-- For `Nc ≠ 0` and `μ`, `ν` distinct from `τ`, the connected correlation equals the pairing of the
centred base observable with its own reflection:

    corrHyper Nc n μ ν τ β lag
      = EW Nc β ((φ₀ - ⟨φ₀⟩) * ((φ₀ - ⟨φ₀⟩) ∘ reflConf τ lag)),   φ₀ = plaqE Nc ((μ, ν), fun _ => 0).

The proof rewrites the reflected factor through `plaqE_lag`, expands with `EW_pair_sub_const`, and
uses `EW_plaqE_lag` twice so that both centring constants are the base one-point function; the
remaining algebra matches `corrHyper_unfold`.

Scope: the centring constant on both factors is `EW Nc β (plaqE Nc ((μ, ν), fun _ => 0))`, the base
plaquette's mean — the statement is about that particular centring, not an arbitrary one.

DERIVED: `0` occurs five times — once as the value `Nc` is assumed to differ from, and four times as
the origin site `fun _ => 0` of the base plaquette, which appears in each of the two factors and in
each of the two centring constants. -/
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

/-! ### `PlaqReflPositive`, and nonnegativity of the correlation from it -/

/-- The proposition `∀ a : ℝ, 0 ≤ EW Nc β ((plaqE Nc q - a) * ((plaqE Nc q ∘ reflConf τ c) - a))`:
the pairing of the plaquette-energy observable of `q`, centred at an arbitrary constant, with its own
image under the reflection at constant `c`, is nonnegative.

Scope: this is a `def ... : Prop` — a hypothesis shape, not a theorem. It is stated for the single
plaquette `q` and the single reflection constant `c`, and `pairing_nonpos_of_odd` shows the
corresponding statement over all bounded measurable observables does not hold. The locality that
makes `q` a one-sided observable is `plaq_link_ne_refl`.

DERIVED: `0` is the lower bound of the pairing, which is the property itself rather than a chosen
threshold. `a` is the centring constant, quantified over; `c` and `q` are the caller's. -/
def PlaqReflPositive (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (q : Plaq d n) : Prop :=
  ∀ a : ℝ, 0 ≤ EW Nc β (fun U => (plaqE Nc q U - a) * (plaqE Nc q (reflConf τ c U) - a))

/-- For `Nc ≠ 0`, `μ`, `ν` distinct from `τ`, and `PlaqReflPositive Nc τ lag β ((μ, ν), fun _ => 0)`,
the correlation satisfies `0 ≤ corrHyper Nc n μ ν τ β lag`. The proof rewrites by
`corrHyper_eq_pairing` and applies the hypothesis at the base plaquette's mean as centring constant.

Scope: one lag at a time, and the hypothesis is required at that same lag as the reflection
constant.

DERIVED: `0` occurs three times — the value `Nc` is assumed to differ from, the origin site
`fun _ => 0` of the base plaquette, and the lower bound on the correlation. -/
theorem corrHyper_nonneg_of_reflPositive (hNc : Nc ≠ 0) [NeZero n] {μ ν τ : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n)
    (hRP : PlaqReflPositive Nc τ lag β (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)) :
    0 ≤ corrHyper (d := d) Nc n μ ν τ β lag := by
  rw [corrHyper_eq_pairing hNc hμ hν β lag]
  exact hRP _

/-! ### The base plaquette reads links the reflection does not fix -/

/-- For `μ`, `ν` distinct from `τ`, every link occurring in `bd ((μ, ν), x)` has `τ`-coordinate
`x τ`. The boundary word uses only the sites `x`, `shift μ x` and `shift ν x`, and `shift` updates
only its own direction, so neither move touches the `τ` coordinate. The proof enumerates the word's
four entries.

DERIVED: no numeral appears in the statement. -/
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

/-- For `μ`, `ν` distinct from `τ`, every link occurring in `bd ((μ, ν), x)` has direction other than
`τ`. The four entries of the boundary word run along `μ`, `ν`, `μ`, `ν` in that order, and each is
closed by one of the two hypotheses.

DERIVED: no numeral appears in the statement. -/
theorem bd_link_dir_ne [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (x : Site d n)
    (l : Link d n) (hl : l ∈ (bd (((μ, ν), x) : Plaq d n)).map Prod.fst) : l.1 ≠ τ := by
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h <;> subst h
  exacts [hμ, hν, hμ, hν]

/-- For a link `l` whose direction is not `τ`, `(reflLink τ c l).2 τ = c - l.2 τ`. On such a link
`reflLink` takes the branch that leaves the direction alone and applies `reflSite`, which subtracts
the `τ` coordinate from `c`.

Scope: the hypothesis `l.1 ≠ τ` selects that branch; a link running along `τ` is reflected
differently.

DERIVED: no numeral appears in the statement. -/
theorem reflLink_tau_coord [NeZero n] {τ : Fin d} (c : Fin n) (l : Link d n) (h : l.1 ≠ τ) :
    (reflLink τ c l).2 τ = c - l.2 τ := by
  simp [reflLink, h, reflSite]

/-- For `μ`, `ν` distinct from `τ` and a reflection constant `c ≠ 0`, no link of
`bd ((μ, ν), fun _ => 0)` is fixed by `reflLink τ c`. Every such link sits at `τ`-coordinate `0`
(`bd_link_tau_coord`) and runs transverse to `τ` (`bd_link_dir_ne`), so its mirror sits at `c - 0 = c`
(`reflLink_tau_coord`); equality would force `c = 0`.

This says the base observable and its reflection read disjoint sets of link variables whenever the
lag is nonzero.

Scope: at `c = 0` the reflection fixes these links and the conclusion does not hold, which is why
`hc` is required.

DERIVED: `0` occurs twice — the value `c` is assumed to differ from, and the origin site
`fun _ => 0` of the base plaquette, whose `τ`-coordinate is what the argument reads. -/
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

/-! ### An observable whose pairing is nonpositive

The three declarations below construct an observable odd under the reflection — the difference of a
function of a link and of its mirror — and compute its pairing as minus the expectation of a square.
So the pairing inequality does not hold when quantified over all bounded measurable observables of
this measure, which is why `PlaqReflPositive` names a single plaquette.
-/

/-- The observable `U ↦ g (U l) - g (U (reflLink τ c l))`: the difference of a scalar function `g` of
a link's value and of its mirror's. `oddObs_odd` shows it changes sign under `reflConf τ c` when
`l.1 ≠ τ`.

DERIVED: no numeral appears in the statement; the link `l`, the reflection constant `c` and the
scalar function `g` are the caller's. -/
noncomputable def oddObs (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n)
    (g : MassGap.SUN.SU Nc → ℝ) (l : Link d n) :
    (wilsonSystem (bd (d := d) (n := n)) (wilsonDensity (N := Nc))).Config → ℝ :=
  fun U => g (U l) - g (U (reflLink τ c l))

/-- For a link `l` with `l.1 ≠ τ`, `oddObs Nc τ c g l (reflConf τ c U) = - oddObs Nc τ c g l U` at
every configuration `U`. On a transverse link `reflConf` reads the mirror's value without a dagger,
and `Reflect.reflLink_involutive` returns the mirror of the mirror, so the two terms swap.

Scope: `hl : l.1 ≠ τ` selects the branch of `reflConf` that carries no dagger; a link along `τ` is
not covered.

DERIVED: no numeral appears in the statement. -/
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

/-- For `Nc ≠ 0` and an observable `O` with `O (reflConf τ c U) = - O U` at every `U`, the pairing
satisfies both `EW Nc β (O * (O ∘ reflConf τ c)) = - EW Nc β (O * O)` and
`EW Nc β (O * (O ∘ reflConf τ c)) ≤ 0`. The integrand is rewritten as `(-1) * (O * O)`,
`wilsonSystem_expect_smul` pulls the scalar out, and `wilsonSystem_expect_nonneg` makes the remaining
expectation of a square nonnegative.

So a pairing inequality quantified over every bounded measurable observable of this measure does not
hold. The observable `PlaqReflPositive` names is not of this kind; `plaq_link_ne_refl` is the check
that distinguishes it.

Scope: `O` is arbitrary apart from the oddness hypothesis, which `oddObs_odd` supplies for `oddObs`
on a transverse link.

DERIVED: `0` occurs twice — the value `Nc` is assumed to differ from, and the upper bound on the
pairing. -/
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

/-! ### Positive total mass, from nonnegativity plus a strictly positive lag-zero term -/

/-- For `ρ : Fin (m + 1) → ℝ` nonnegative everywhere with `0 < ρ 0`, the total `∑ k, ρ k` is strictly
positive. It is `Finset.sum_pos'` with `0` as the witness index.

Scope: the index type is `Fin (m + 1)`, so it is nonempty and `ρ 0` exists. Nonnegativity alone does
not give a positive total — a sequence that vanishes identically satisfies it and fails the
conclusion.

DERIVED: `1` is the `+ 1` in `Fin (m + 1)`, which makes the index type nonempty; `0` occurs four
times — the lower bound on each `ρ k`, the strict lower bound in `h0`, the index `0` at which that
bound is taken, and the lower bound on the total. -/
theorem sum_pos_of_head_pos {m : ℕ} (ρ : Fin (m + 1) → ℝ) (hnn : ∀ k, 0 ≤ ρ k) (h0 : 0 < ρ 0) :
    0 < ∑ k, ρ k :=
  Finset.sum_pos' (fun k _ => hnn k) ⟨0, Finset.mem_univ 0, h0⟩

/-- For `Nc ≠ 0`, `μ`, `ν` distinct from `τ`, extent `m + 1`, the hypothesis `hRP` giving
`PlaqReflPositive` at every lag, and `h0 : 0 < corrHyper Nc (m + 1) μ ν τ β 0`, the conclusion is
the conjunction

    (∀ lag, 0 ≤ corrHyper Nc (m + 1) μ ν τ β lag) ∧ 0 < ∑ lag, corrHyper Nc (m + 1) μ ν τ β lag.

The first conjunct is `corrHyper_nonneg_of_reflPositive` at each lag; the second is
`sum_pos_of_head_pos` applied to it together with `h0`.

Scope: `h0` is an independent hypothesis — the pairing inequalities alone do not give it, since the
identically-zero correlation satisfies them. Its content is that the plaquette energy has positive
variance under the Gibbs measure.

DERIVED: `0` occurs six times — the value `Nc` is assumed to differ from, the origin site
`fun _ => 0` of the base plaquette, the lower bound and the lag index in `h0`, the lower bound in the
first conjunct, and the lower bound on the total. `1` occurs six times, as the `+ 1` in the extent
`m + 1`: in the index type of `hRP`, in the `Site` and `Plaq` types, and in each of the three
`corrHyper` applications. -/
theorem corrHyper_rp_of (hNc : Nc ≠ 0) {m : ℕ} {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    (hRP : ∀ lag : Fin (m + 1),
      PlaqReflPositive Nc τ lag β (((μ, ν), (fun _ => 0 : Site d (m + 1))) : Plaq d (m + 1)))
    (h0 : 0 < corrHyper (d := d) Nc (m + 1) μ ν τ β 0) :
    (∀ lag, 0 ≤ corrHyper (d := d) Nc (m + 1) μ ν τ β lag)
      ∧ 0 < ∑ lag, corrHyper (d := d) Nc (m + 1) μ ν τ β lag := by
  have hnn : ∀ lag, 0 ≤ corrHyper (d := d) Nc (m + 1) μ ν τ β lag := fun lag =>
    corrHyper_nonneg_of_reflPositive hNc hμ hν β lag (hRP lag)
  exact ⟨hnn, sum_pos_of_head_pos _ hnn h0⟩

/-! ### The same statement at `corrClay`'s parameters

`WilsonBridge.corrClay` is `corrHyper` at `Nc = 3`, `d = 4`, plane `(0, 1)`, lag axis `2`, and
`Complete.wilsonCorrAt N β` is `corrClay (N + 1) β` by definition. The theorem below is
`corrHyper_rp_of` instantiated there.
-/

/-- `corrHyper_rp_of` at `Nc := 3`, `d := 4`, `μ := 0`, `ν := 1`, `τ := 2`, `m := N`, which are the
parameters defining `WilsonBridge.corrClay`. Given `hRP`, the `PlaqReflPositive` hypothesis at every
lag for the base plaquette of `Plaq 4 (N + 1)`, and `h0 : 0 < corrClay (N + 1) β 0`, the conclusion
is

    (∀ lag, 0 ≤ corrClay (N + 1) β lag) ∧ 0 < ∑ lag, corrClay (N + 1) β lag.

The two distinctness side conditions `0 ≠ 2` and `1 ≠ 2` in `Fin 4` are discharged by `decide`, and
`3 ≠ 0` by `norm_num`. Since `Complete.wilsonCorrAt N β` is `corrClay (N + 1) β` by definition, the
same statement reads for that function.

Scope: `h0` is a hypothesis, independent of `hRP`. `β` is an arbitrary real.

DERIVED: `3` is the gauge rank `Nc`, fixed by `corrClay`; `4` occurs five times, as the dimension
`d` — in the three `Fin 4` direction literals and in the `Site 4` and `Plaq 4` types; `2` is the lag
axis `τ`; `1` occurs seven times — once as the plaquette direction `ν` and six times as the `+ 1` in
the extent `N + 1`, in the index type of `hRP`, in the `Site` and `Plaq` types, and in each of the
three `corrClay` applications; `0` occurs six times — the plaquette direction `μ`, the origin site
`fun _ => 0`, the lower bound and the lag index in `h0`, the lower bound in the first conjunct, and
the lower bound on the total. -/
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
