import MassGap.PlaqVariance
import MassGap.WilsonAnalytic

/-!
# MassGap.AreaLaw — the rectangular Wilson loop, and the coupling dependence of the Wilson measure

The file has two independent halves.

## Part 1: the rectangular Wilson loop

`WilsonHypercubic.bd` gives the boundary word of a single plaquette. `rectWord` generalises it to
the `R × T` rectangle in the `(μ, ν)` coordinate plane based at a site `x`, as an ordered list of
`(link, orientation)` pairs in the same format, so `WilsonLattice.wilsonHol` turns it into the
ordered loop product with no new machinery. `rectWord_one_one` states that at `R = T = 1` the word
is `bd` applied to the plaquette `((μ, ν), x)`.

What is proved about the loop is structural. The word has `2 * (R + T)` letters
(`rectWord_length`); a rectangle of zero width has identity holonomy (`loopHol_zero_width`); the
holonomy conjugates under a global gauge transformation (`loopHol_conj`); the normalised loop
observable `loopObs` is continuous (`continuous_loopObs`), measurable (`measurable_loopObs`), equal
to `1` at the all-identity configuration (`loopObs_one`) and bounded in absolute value by `1`
uniformly in `R`, `T` and the configuration (`abs_loopObs_le_one`). That uniform bound is the only
bound on `loopObs` stated in this file.

## Part 2: the coupling dependence of the mean Wilson action

For the four-dimensional `SU(3)` system on the periodic lattice, the mean Wilson action is a
strictly decreasing function of `β` at every real `β`:

    d/dβ ⟨S⟩_β = −(⟨S²⟩_β − ⟨S⟩_β²)  <  0.

`action_hasDerivAt` is `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` at the observable `O = S`,
where the right-hand side is minus the variance of the action; `abs_action_le` supplies the uniform
bound that lemma requires. `expect_var_pos` gives strict positivity of that variance from two
configurations at which the observable takes different values, and `clay_action_var_pos` feeds it
`PlaqVariance.confOne` and `PlaqVariance.confAB` together with `action_confOne` and
`action_confAB_pos`. Hence `clay_mean_action_deriv_neg`, `clay_mean_action_strictAnti`, and
`clay_mean_action_ne_of_ne`: distinct couplings give distinct mean actions.

The Part 2 statements carry no smallness hypothesis and no bound on `β`. They are stated for the
periodic torus of extent `n` with `NeZero n`, not for `ℤ⁴`. `su_one_mean_action_deriv_zero` is the
control at rank `N = 1`: there the same derivative is zero at every `β` and on every geometry.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.AreaLaw`.
-/

namespace MassGap.AreaLaw

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic
open MeasureTheory

/-! ## Part 1: the rectangular Wilson loop -/

variable {d n : ℕ}

/-- The `k`-fold unit shift in direction `μ`, by recursion on `k`: zero steps is the identity on
sites, and `k + 1` steps applies `LatticeGauge.shift μ` to the `k`-step shift. `shiftN μ 1` is
`shift μ`, which is the step `WilsonHypercubic.bd` uses.

DERIVED: the `0` is the base case of the recursion, no steps taken; the `1` in `k + 1` is the
successor pattern, one further step. `k` counts lattice steps; no lattice spacing enters. -/
def shiftN [NeZero n] (μ : Fin d) : ℕ → Site d n → Site d n
  | 0, x => x
  | (k + 1), x => shift μ (shiftN μ k x)

@[simp] theorem shiftN_zero [NeZero n] (μ : Fin d) (x : Site d n) : shiftN μ 0 x = x := rfl

@[simp] theorem shiftN_one [NeZero n] (μ : Fin d) (x : Site d n) : shiftN μ 1 x = shift μ x := rfl

/-- The boundary word of the `R × T` rectangular Wilson loop in the `(μ, ν)` plane at site `x`.

The four sides in cyclic order: `R` steps along `μ` forwards, `T` steps along `ν` forwards at the
far end, `R` steps back along `μ` inverted (the range reversed), `T` steps back along `ν` inverted.
The `Bool` is the orientation in `WilsonHypercubic.bd`'s convention — `true` is the link, `false`
its inverse — so `WilsonLattice.wilsonHol` reads the list as an ordered loop product.

`R` and `T` are the caller's side lengths in lattice steps, and nothing requires `μ ≠ ν`.

DERIVED: no numeral appears in the statement. -/
def rectWord [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) : List (Link d n × Bool) :=
  ((List.range R).map (fun i => ((μ, shiftN μ i x), true)))
    ++ ((List.range T).map (fun j => ((ν, shiftN ν j (shiftN μ R x)), true)))
    ++ ((List.range R).reverse.map (fun i => ((μ, shiftN μ i (shiftN ν T x)), false)))
    ++ ((List.range T).reverse.map (fun j => ((ν, shiftN ν j x), false)))

/-- At `R = T = 1` the rectangular word is `WilsonHypercubic.bd ((μ, ν), x)`, with the same letters
in the same order, so the index conventions below are `bd`'s.

DERIVED: the two `1`s are the side lengths `R` and `T`, one lattice step each. -/
theorem rectWord_one_one [NeZero n] (μ ν : Fin d) (x : Site d n) :
    rectWord μ ν x 1 1 = bd ((μ, ν), x) := by
  simp [rectWord, bd, List.range_one]

/-- The word has `2 * (R + T)` letters: the four sides contribute `R`, `T`, `R` and `T`, the two
reversed sides having the same length as the sides they retrace.

DERIVED: the `2` counts the two traversals of each side length, forwards and back; it is a
multiplicity, not a magnitude. -/
theorem rectWord_length [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    (rectWord μ ν x R T).length = 2 * (R + T) := by
  simp only [rectWord, List.length_append, List.length_map, List.length_range,
    List.length_reverse]
  ring

/-- The holonomy of the rectangular Wilson loop: `WilsonLattice.wilsonHol` applied to the constant
family `fun _ : Unit => rectWord μ ν x R T` at its single index, which is the ordered product of the
link variables around the loop with inverses where the word runs backwards. Every general fact about
`wilsonHol` applies to it.

DERIVED: no numeral appears in the statement. -/
noncomputable def loopHol {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : MassGap.SUN.SU N :=
  wilsonHol (fun _ : Unit => rectWord μ ν x R T) () U

/-- The normalised Wilson loop observable `(1 / N) * Re tr` of the loop holonomy, valued in `ℝ`.
At `R = T = 1` it is the complement of the plaquette energy (`loopObs_one_one`).

DERIVED: the `1` is the numerator of the character normalisation `1 / N`, which makes the value `1`
at the identity holonomy for every rank `N`. It is not a scale. -/
noncomputable def loopObs {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  (1 / (N : ℝ))
    * (Matrix.trace ((loopHol μ ν x R T U : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re

/-- The `1 × 1` loop holonomy is the plaquette holonomy: `loopHol μ ν x 1 1 U` is
`wilsonHol bd ((μ, ν), x) U`, by rewriting with `rectWord_one_one`.

DERIVED: the two `1`s are the side lengths `R` and `T`. -/
theorem loopHol_one_one {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    loopHol μ ν x 1 1 U = wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U := by
  show (((rectWord μ ν x 1 1).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) = _
  rw [rectWord_one_one]
  rfl

/-- The loop observable is the complement of the Wilson density of the loop holonomy:
`loopObs μ ν x R T U = 1 - wilsonDensity (loopHol μ ν x R T U)`. Both sides unfold to the same
expression in `Re tr`, so bounds on `wilsonDensity` transfer to `loopObs`.

DERIVED: the `1` is the value `wilsonDensity` subtracts its normalised trace from, the observable's
value at the identity holonomy. -/
theorem loopObs_eq {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) :
    loopObs μ ν x R T U = 1 - wilsonDensity (N := N) (loopHol μ ν x R T U) := by
  unfold loopObs wilsonDensity
  ring

/-- The `1 × 1` loop observable is the complement of the plaquette energy:
`loopObs μ ν x 1 1 U = 1 - wilsonDensity (wilsonHol bd ((μ, ν), x) U)`. Composed from `loopObs_eq`
and `loopHol_one_one`.

DERIVED: the first two `1`s are the side lengths `R` and `T`; the third is the value the Wilson
density is subtracted from. -/
theorem loopObs_one_one {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    loopObs μ ν x 1 1 U
      = 1 - wilsonDensity (N := N) (wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U) := by
  rw [loopObs_eq, loopHol_one_one]

/-! ### Retracing

The two lemmas below are the list-level group identities behind `loopHol_zero_width`: a word
followed by its own reversal with every letter inverted has identity product. Both go by
induction on the list, so neither depends on a particular library spelling. -/

/-- For a map `f` into a group, the reversed list with every letter inverted has product
`((l.map f).prod)⁻¹`. Induction on `l`.

DERIVED: no numeral appears in the statement. -/
theorem prod_rev_inv {G : Type*} [Group G] {α : Type*} (f : α → G) (l : List α) :
    (l.reverse.map (fun a => (f a)⁻¹)).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev]

/-- A word followed by its own retracing has identity product:
`((l.map f) ++ (l.reverse.map (fun a => (f a)⁻¹))).prod = 1`, from `prod_rev_inv` and
`mul_inv_cancel`.

DERIVED: the `1` is the group identity, the value of the product. -/
theorem prod_retrace {G : Type*} [Group G] {α : Type*} (f : α → G) (l : List α) :
    ((l.map f) ++ (l.reverse.map (fun a => (f a)⁻¹))).prod = 1 := by
  rw [List.prod_append, prod_rev_inv f l, mul_inv_cancel]

/-- A rectangle of zero width has identity holonomy: `loopHol μ ν x 0 T U = 1` for every
configuration, every `T` and every pair of directions. With `R = 0` the word is `T` steps along `ν`
followed by their retracing, so `prod_retrace` applies. This is the check that `rectWord` is a
closed loop rather than an arbitrary list.

DERIVED: the `0` is the side length `R`, no steps along `μ`; the `1` is the identity of
`MassGap.SUN.SU N`. -/
theorem loopHol_zero_width {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) :
    loopHol μ ν x 0 T U = 1 := by
  have hw : rectWord μ ν x 0 T
      = ((List.range T).map (fun j => ((ν, shiftN ν j x), true)))
        ++ ((List.range T).reverse.map (fun j => ((ν, shiftN ν j x), false))) := by
    simp [rectWord]
  show (((rectWord μ ν x 0 T).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) = 1
  rw [hw, List.map_append, List.map_map, List.map_map]
  have hf : ((fun lo : Link d n × Bool => if lo.2 then U lo.1 else (U lo.1)⁻¹)
        ∘ fun j : ℕ => ((ν, shiftN ν j x), true))
      = fun j : ℕ => U (ν, shiftN ν j x) := by
    funext j; simp
  have hg : ((fun lo : Link d n × Bool => if lo.2 then U lo.1 else (U lo.1)⁻¹)
        ∘ fun j : ℕ => ((ν, shiftN ν j x), false))
      = fun j : ℕ => (U (ν, shiftN ν j x))⁻¹ := by
    funext j; simp
  rw [hf, hg]
  exact prod_retrace (fun j : ℕ => U (ν, shiftN ν j x)) (List.range T)

/-- Replacing `U` by `fun l => g * U l * g⁻¹` conjugates the loop holonomy by `g`. This is
`WilsonLattice.wilsonHol_conj` at the loop's own word. The transformation is global — `g` does not
depend on the site — so the statement is about a constant gauge rotation, not a site-dependent one.

DERIVED: no numeral appears in the statement. -/
theorem loopHol_conj {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (g : MassGap.SUN.SU N) (U : Link d n → MassGap.SUN.SU N) :
    loopHol μ ν x R T (fun l => g * U l * g⁻¹) = g * loopHol μ ν x R T U * g⁻¹ :=
  wilsonHol_conj (fun _ : Unit => rectWord μ ν x R T) g () U

/-- The loop holonomy is continuous in the configuration, from
`PlaqVariance.continuous_wilsonHol` at the loop's own word.

DERIVED: no numeral appears in the statement. -/
theorem continuous_loopHol {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    Continuous (loopHol (N := N) μ ν x R T) :=
  MassGap.PlaqVariance.continuous_wilsonHol (fun _ : Unit => rectWord μ ν x R T) ()

/-- The loop observable is continuous in the configuration, hence measurable
(`measurable_loopObs`) and usable as an observable of the Gibbs measure. From `loopObs_eq`,
`continuous_wilsonDensity` and `continuous_loopHol`.

DERIVED: no numeral appears in the statement. -/
theorem continuous_loopObs {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    Continuous (loopObs (N := N) μ ν x R T) := by
  have h : loopObs (N := N) μ ν x R T
      = fun U => 1 - wilsonDensity (N := N) (loopHol μ ν x R T U) :=
    funext (fun U => loopObs_eq μ ν x R T U)
  rw [h]
  exact continuous_const.sub (continuous_wilsonDensity.comp (continuous_loopHol μ ν x R T))

theorem measurable_loopObs {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    Measurable (loopObs (N := N) μ ν x R T) :=
  (continuous_loopObs μ ν x R T).measurable

/-- `|loopObs μ ν x R T U| ≤ 1`, uniformly in `R`, `T`, the site, the directions and the
configuration: the observable is a normalised character of a unitary matrix. From
`wilsonDensity_nonneg` and `wilsonDensity_le_two` through `loopObs_eq`. The rank hypothesis `N ≠ 0`
is what those two bounds require.

DERIVED: the `0` is the rank condition `N ≠ 0`; the `1` is the bound on the absolute value. -/
theorem abs_loopObs_le_one {N : ℕ} (hN : N ≠ 0) [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : |loopObs μ ν x R T U| ≤ 1 := by
  have h0 := wilsonDensity_nonneg hN (loopHol μ ν x R T U)
  have h2 := wilsonDensity_le_two hN (loopHol μ ν x R T U)
  rw [loopObs_eq, abs_le]
  constructor <;> linarith

/-- At the all-identity configuration the loop observable is `1`, for every `R`, `T`, site and pair
of directions. The loop holonomy is a product of identities, and `wilsonDensity_one` needs `N ≠ 0`.

DERIVED: the `0` is the rank condition `N ≠ 0`; the `1` in `fun _ => 1` is the identity of
`MassGap.SUN.SU N` assigned to every link; the final `1` is the value of the observable. -/
theorem loopObs_one {N : ℕ} (hN : N ≠ 0) [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    loopObs (N := N) μ ν x R T (fun _ => 1) = 1 := by
  have h1 : loopHol (N := N) μ ν x R T (fun _ => 1) = 1 := by
    show (((rectWord μ ν x R T).map (fun lo => if lo.2 then (1 : MassGap.SUN.SU N)
      else (1 : MassGap.SUN.SU N)⁻¹)).prod) = 1
    refine List.prod_eq_one ?_
    intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨lo, _, rfl⟩ := hg
    cases lo.2 <;> simp
  rw [loopObs_eq, h1, wilsonDensity_one hN]
  ring

#print axioms rectWord_one_one
#print axioms rectWord_length
#print axioms loopObs_eq
#print axioms continuous_loopObs
#print axioms measurable_loopObs
#print axioms loopHol_one_one
#print axioms loopObs_one_one
#print axioms loopHol_zero_width
#print axioms loopHol_conj
#print axioms abs_loopObs_le_one
#print axioms loopObs_one

/-! ## Part 2: the coupling dependence of the mean Wilson action

The observable below is the total Wilson action `S = ∑_p φ_W(hol p)`, not the Wilson loop of Part 1.
The statement is that its Gibbs mean is strictly decreasing in `β`.

Two inputs. `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` gives, for an observable `O`,
`d⟨O⟩/dβ = −(⟨O·S⟩ − ⟨O⟩⟨S⟩)`; at `O = S` the right-hand side is minus the variance of the action.
`expect_var_pos` gives strict positivity of that variance from two configurations at which the
observable takes different values.
-/

section Variance

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- The total Wilson action is bounded in absolute value by `2 * Fintype.card Pq`, since each
plaquette density lies in `[0, 2]` (`WilsonAction.wilsonDensity_nonneg`, `wilsonDensity_le_two`).
This is the uniform bound `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` asks for at the observable
`S`. Stated for an arbitrary boundary-word family `bdw` over finite link and plaquette types.

DERIVED: the `0` is the rank condition `N ≠ 0`; the `2` is the upper end of `wilsonDensity`'s range,
and `Fintype.card Pq` is the plaquette count of whatever geometry the caller supplies. -/
theorem abs_action_le (hN : N ≠ 0) (bdw : Pq → List (Lk × Bool))
    (U : (wilsonSystem bdw (wilsonDensity (N := N))).Config) :
    |(wilsonSystem bdw (wilsonDensity (N := N))).action U| ≤ 2 * (Fintype.card Pq : ℝ) := by
  have hact : (wilsonSystem bdw (wilsonDensity (N := N))).action U
      = ∑ p : Pq, wilsonDensity (N := N) (wilsonHol bdw p U) := rfl
  rw [hact]
  calc |∑ p : Pq, wilsonDensity (N := N) (wilsonHol bdw p U)|
      ≤ ∑ p : Pq, |wilsonDensity (N := N) (wilsonHol bdw p U)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Pq, (2 : ℝ) := Finset.sum_le_sum (fun p _ => by
        rw [abs_of_nonneg (wilsonDensity_nonneg hN _)]
        exact wilsonDensity_le_two hN _)
    _ = 2 * (Fintype.card Pq : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- The Gibbs variance of a continuous bounded observable is strictly positive as soon as the
observable takes different values at two configurations.

The hypotheses are `N ≠ 0`, continuity of `O`, a uniform bound `M` with `|O U| ≤ M` for every `U`,
and two configurations `U`, `V` with `O U ≠ O V`. The conclusion is `0 < ⟨O²⟩_β - ⟨O⟩_β²` at the
given `β`. The Gibbs weight is positive and continuous at every real coupling, so a nonnegative
continuous integrand `(O - ⟨O⟩)² · e^{−βS}` with zero integral vanishes identically, which would
force `O` constant.

`O` is an arbitrary observable, not a plaquette density; the instance Part 2 uses is the action
itself. There is no smallness hypothesis, no sign condition and no bound on `β`.

DERIVED: the first `0` is the rank condition `N ≠ 0`; the second is the lower bound in the
conclusion, the strict positivity of the variance. -/
theorem expect_var_pos (hN : N ≠ 0) (bdw : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bdw (wilsonDensity (N := N))).Config → ℝ)
    (hcont : Continuous O) (M : ℝ) (hb : ∀ U, |O U| ≤ M)
    (U V : (wilsonSystem bdw (wilsonDensity (N := N))).Config) (hUV : O U ≠ O V) :
    0 < (wilsonSystem bdw (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
          (fun W => O W * O W)
        - ((wilsonSystem bdw (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O)
          * ((wilsonSystem bdw (wilsonDensity (N := N))).expect
              (probHaar (MassGap.SUN.SU N)) β O) := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bdw (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  haveI : ((wilsonSystem bdw (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure :=
    inferInstanceAs ((Measure.pi
      (fun _ : Lk => probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure)
  have hM : 0 ≤ M := le_trans (abs_nonneg (O U)) (hb U)
  have hZ : 0 < (wilsonSystem bdw (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β := wilsonSystem_partition_pos hN bdw β
  have hwpos : ∀ W, 0 < (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W :=
    fun W => wilsonSystem_boltz_pos bdw β W
  set m : ℝ := (wilsonSystem bdw (wilsonDensity (N := N))).expect
    (probHaar (MassGap.SUN.SU N)) β O with hm
  -- the three integrability facts
  have iO : Integrable (fun W => O W * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bdw β O hcont.measurable M hb
  have iw : Integrable ((wilsonSystem bdw (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    have h := wilsonSystem_mul_boltz_integrable hN bdw β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using h
  have iO2 : Integrable (fun W => (O W * O W)
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bdw β (fun W => O W * O W)
      (hcont.mul hcont).measurable (M * M)
      (fun W => by
        rw [abs_mul]
        exact mul_le_mul (hb W) (hb W) (abs_nonneg _) hM)
  have i2 : Integrable (fun W => (-(2 * m)) * (O W
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W))
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    iO.const_mul _
  have i3 : Integrable (fun W => m ^ 2
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    iw.const_mul _
  have hsplit : ∀ W, (O W - m) ^ 2 * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
      = (O W * O W) * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
        + ((-(2 * m)) * (O W * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
          + m ^ 2 * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W) := fun W => by ring
  have i23 : Integrable (fun W => (-(2 * m)) * (O W
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      + m ^ 2 * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    i2.add i3
  have iI : Integrable (fun W => (O W - m) ^ 2
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (iO2.add i23).congr (Filter.Eventually.of_forall (fun W => (hsplit W).symm))
  -- ⟨O⟩·Z is the unnormalised first moment
  have hmZ : m * (wilsonSystem bdw (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β
      = (wilsonSystem bdw (wilsonDensity (N := N))).corrNum
          (probHaar (MassGap.SUN.SU N)) β O := by
    rw [hm]; unfold System.expect; exact div_mul_cancel₀ _ hZ.ne'
  have hkey : (∫ W, (O W - m) ^ 2
        * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
        ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = (wilsonSystem bdw (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun W => O W * O W)
        - m ^ 2 * (wilsonSystem bdw (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add iO2 i23, integral_add i2 i3, integral_const_mul, integral_const_mul]
    unfold System.corrNum System.partition
    rw [show (∫ W, O W * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        = (wilsonSystem bdw (wilsonDensity (N := N))).corrNum
            (probHaar (MassGap.SUN.SU N)) β O from rfl,
      show (∫ W, (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        = (wilsonSystem bdw (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β from rfl,
      ← hmZ]
    ring
  have hInn : 0 ≤ ∫ W, (O W - m) ^ 2
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
      ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    integral_nonneg (fun W => mul_nonneg (sq_nonneg _) (hwpos W).le)
  have hIpos : 0 < ∫ W, (O W - m) ^ 2
      * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
      ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    refine lt_of_le_of_ne hInn (fun h0 => ?_)
    have hnn : (0 : (wilsonSystem bdw (wilsonDensity (N := N))).Config → ℝ)
        ≤ fun W => (O W - m) ^ 2
          * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W :=
      fun W => mul_nonneg (sq_nonneg _) (hwpos W).le
    have hae := (integral_eq_zero_iff_of_nonneg hnn iI).mp h0.symm
    have hcont2 : Continuous (fun W => (O W - m) ^ 2
        * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W) :=
      ((hcont.sub continuous_const).pow 2).mul
        (MassGap.PlaqVariance.continuous_wilsonSystem_boltz bdw β)
    have hzero := (Continuous.ae_eq_iff_eq
      ((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))
      hcont2 continuous_const).mp hae
    have hconst : ∀ W, O W = m := by
      intro W
      have hW : (O W - m) ^ 2
          * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W = 0 := congrFun hzero W
      have h1 := (mul_eq_zero.mp hW).resolve_right (hwpos W).ne'
      have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    exact hUV ((hconst U).trans (hconst V).symm)
  have hexp : (wilsonSystem bdw (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (fun W => O W * O W) - m * m
      = (∫ W, (O W - m) ^ 2 * (wilsonSystem bdw (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bdw (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        / (wilsonSystem bdw (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β := by
    rw [hkey]
    have hZne : (wilsonSystem bdw (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β ≠ 0 := hZ.ne'
    show ((wilsonSystem bdw (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun W => O W * O W))
        / (wilsonSystem bdw (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β - m * m = _
    field_simp
  rw [hexp]
  exact div_pos hIpos hZ

#print axioms abs_action_le
#print axioms expect_var_pos

/-- The mean action has derivative `−(⟨S·S⟩_β − ⟨S⟩_β⟨S⟩_β)` in the coupling at the given `β`: the
instance `O = S` of `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, with
`PlaqVariance.continuous_wilsonSystem_action` supplying measurability and `abs_action_le` the
uniform bound. Holds for any boundary-word family over finite link and plaquette types, any geometry
and any `N ≠ 0`. The sign of that derivative comes from `expect_var_pos`, not from here.

DERIVED: the `0` is the rank condition `N ≠ 0`. -/
theorem action_hasDerivAt (hN : N ≠ 0) (bdw : Pq → List (Lk × Bool)) (β : ℝ) :
    HasDerivAt (fun x : ℝ => (wilsonSystem bdw (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) x (wilsonSystem bdw (wilsonDensity (N := N))).action)
      (-((wilsonSystem bdw (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
            (fun U => (wilsonSystem bdw (wilsonDensity (N := N))).action U
              * (wilsonSystem bdw (wilsonDensity (N := N))).action U)
          - (wilsonSystem bdw (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
              (wilsonSystem bdw (wilsonDensity (N := N))).action
            * (wilsonSystem bdw (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
                (wilsonSystem bdw (wilsonDensity (N := N))).action)) β :=
  MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bdw β
    (wilsonSystem bdw (wilsonDensity (N := N))).action
    (MassGap.PlaqVariance.continuous_wilsonSystem_action bdw).measurable
    (2 * (Fintype.card Pq : ℝ)) (abs_action_le hN bdw)

#print axioms action_hasDerivAt

/-! ### The trivial gauge group

`action_hasDerivAt` names a derivative for every `N ≠ 0` without signing it. At `N = 1` that
derivative is zero: the determinant condition pins the single entry, every holonomy is the identity,
the action vanishes identically, and the mean action is constant in `β` at every geometry. The
strict inequality in `clay_mean_action_deriv_neg` therefore rests on the strict positivity of the
variance, and that in turn on the non-commutation of two `SU(3)` elements. -/

/-- At rank `N = 1` the Wilson action vanishes at every configuration: each plaquette density is
zero (`PlaqVariance.wilsonDensity_su_one`) and the action is their sum.

DERIVED: the `1`s are the rank at which `wilsonDensity` and `wilsonSystem` are taken; the `0` is the
value of the action. -/
theorem action_su_one (bdw : Pq → List (Lk × Bool))
    (U : (wilsonSystem bdw (wilsonDensity (N := 1))).Config) :
    (wilsonSystem bdw (wilsonDensity (N := 1))).action U = 0 := by
  show (∑ _p : Pq, wilsonDensity (N := 1) (wilsonHol bdw _p U)) = 0
  exact Finset.sum_eq_zero (fun p _ => MassGap.PlaqVariance.wilsonDensity_su_one _)

/-- At rank `N = 1` the derivative of the mean action in the coupling is zero, at every `β` and for
every boundary-word family over finite link and plaquette types. From `action_su_one`, which makes
both `⟨S⟩` and `⟨S²⟩` zero, together with `action_hasDerivAt`.

DERIVED: the `1`s are the rank at which `wilsonDensity`, `wilsonSystem` and `probHaar (SU 1)` are
taken; the `0` is the value of the derivative. -/
theorem su_one_mean_action_deriv_zero (bdw : Pq → List (Lk × Bool)) (β : ℝ) :
    deriv (fun x : ℝ => (wilsonSystem bdw (wilsonDensity (N := 1))).expect
        (probHaar (MassGap.SUN.SU 1)) x
        (wilsonSystem bdw (wilsonDensity (N := 1))).action) β = 0 := by
  have hz : (wilsonSystem bdw (wilsonDensity (N := 1))).action = fun _ => (0 : ℝ) :=
    funext (action_su_one bdw)
  have he : ∀ γ : ℝ, (wilsonSystem bdw (wilsonDensity (N := 1))).expect
      (probHaar (MassGap.SUN.SU 1)) γ
      (wilsonSystem bdw (wilsonDensity (N := 1))).action = 0 := by
    intro γ
    rw [hz]
    unfold System.expect System.corrNum
    simp
  have he2 : ∀ γ : ℝ, (wilsonSystem bdw (wilsonDensity (N := 1))).expect
      (probHaar (MassGap.SUN.SU 1)) γ
      (fun U => (wilsonSystem bdw (wilsonDensity (N := 1))).action U
        * (wilsonSystem bdw (wilsonDensity (N := 1))).action U) = 0 := by
    intro γ
    rw [hz]
    unfold System.expect System.corrNum
    simp
  rw [(action_hasDerivAt (by norm_num) bdw β).deriv, he2 β, he β]
  ring

#print axioms action_su_one
#print axioms su_one_mean_action_deriv_zero

end Variance

/-! ### The four-dimensional `SU(3)` instance

`PlaqVariance` supplies the two configurations the section uses and the non-commutation fact they
rest on. `confOne` carries the identity on every link; `confAB` is built from the two `SU(3)`
elements `gA` and `gB`, and `PlaqVariance.obs_confAB` gives its plaquette energy `4/3` at the
plaquette `PlaqVariance.clayPlaq n`. -/

section Clay

open MassGap.PlaqVariance

variable {n : ℕ}

/-- Every plaquette holonomy of the all-identity configuration is the identity: the ordered loop is
a product of identities and their inverses.

DERIVED: the `4`s are the lattice dimension, fixed here rather than general; the `1` is the group
identity, the value of the holonomy. -/
theorem wilsonHol_confOne [NeZero n] (p : Plaq 4 n) :
    wilsonHol (bd (d := 4) (n := n)) p (confOne n) = 1 := by
  show (((bd (d := 4) (n := n) p).map (fun lo => if lo.2 then (1 : MassGap.SUN.SU 3)
    else (1 : MassGap.SUN.SU 3)⁻¹)).prod) = 1
  refine List.prod_eq_one ?_
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨lo, _, rfl⟩ := hg
  cases lo.2 <;> simp

/-- The all-identity configuration has total Wilson action zero: every plaquette holonomy is the
identity (`wilsonHol_confOne`) and `wilsonDensity_one` sends the identity to zero.

DERIVED: the `4` is the lattice dimension and the `3` the rank `N` at which `wilsonDensity` is
taken; the `0` is the value of the action. -/
theorem action_confOne [NeZero n] :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action (confOne n) = 0 := by
  show (∑ p : Plaq 4 n, wilsonDensity (N := 3)
    (wilsonHol (bd (d := 4) (n := n)) p (confOne n))) = 0
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [wilsonHol_confOne p]
  exact wilsonDensity_one (by norm_num)

/-- The configuration `confAB` has strictly positive total Wilson action. Every plaquette
contributes nonnegatively (`wilsonDensity_nonneg`), and the single plaquette
`PlaqVariance.clayPlaq n` contributes `4/3` by `PlaqVariance.obs_confAB`, so `Finset.single_le_sum`
bounds the sum below by that one term.

DERIVED: the `0` is the lower bound in the conclusion; the `4` is the lattice dimension and the `3`
the rank `N`. -/
theorem action_confAB_pos [NeZero n] :
    0 < (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action (confAB n) := by
  have hterm : wilsonDensity (N := 3)
      (wilsonHol (bd (d := 4) (n := n)) (clayPlaq n) (confAB n)) = 4 / 3 := obs_confAB n
  have hle : wilsonDensity (N := 3)
      (wilsonHol (bd (d := 4) (n := n)) (clayPlaq n) (confAB n))
      ≤ ∑ p : Plaq 4 n, wilsonDensity (N := 3)
          (wilsonHol (bd (d := 4) (n := n)) p (confAB n)) :=
    Finset.single_le_sum
      (f := fun p : Plaq 4 n => wilsonDensity (N := 3)
        (wilsonHol (bd (d := 4) (n := n)) p (confAB n)))
      (fun p _ => wilsonDensity_nonneg (by norm_num) _) (Finset.mem_univ (clayPlaq n))
  show 0 < ∑ p : Plaq 4 n, wilsonDensity (N := 3)
    (wilsonHol (bd (d := 4) (n := n)) p (confAB n))
  rw [hterm] at hle
  linarith

/-- The Gibbs variance of the Wilson action of the four-dimensional `SU(3)` theory is strictly
positive at every real `β`.

`expect_var_pos` applied to the two configurations `PlaqVariance.confOne` and `PlaqVariance.confAB`,
whose actions differ by `action_confOne` and `action_confAB_pos`, with
`PlaqVariance.continuous_wilsonSystem_action` for continuity and `abs_action_le` for the uniform
bound. Stated on the periodic lattice for any extent `n` with `NeZero n`.

DERIVED: the `0` is the lower bound in the conclusion; the `4` is the lattice dimension and the `3`
the rank of the gauge group, appearing both in `wilsonDensity (N := 3)` and in `probHaar (SU 3)`. -/
theorem clay_action_var_pos [NeZero n] (β : ℝ) :
    0 < (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
          (probHaar (MassGap.SUN.SU 3)) β
          (fun U => (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action U
            * (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action U)
        - (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
            (probHaar (MassGap.SUN.SU 3)) β
            (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
          * (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
              (probHaar (MassGap.SUN.SU 3)) β
              (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action := by
  refine expect_var_pos (by norm_num) (bd (d := 4) (n := n)) β
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
    (MassGap.PlaqVariance.continuous_wilsonSystem_action _)
    (2 * (Fintype.card (Plaq 4 n) : ℝ)) (abs_action_le (by norm_num) _)
    (confOne n) (confAB n) ?_
  rw [action_confOne]
  exact ne_of_lt action_confAB_pos

/-- The derivative of the mean action of the four-dimensional `SU(3)` theory in the coupling is
strictly negative at every real `β`, from `action_hasDerivAt` and `clay_action_var_pos`.

DERIVED: the `4` is the lattice dimension and the `3` the rank of the gauge group; the `0` is the
upper bound in the conclusion, the sign of the derivative. -/
theorem clay_mean_action_deriv_neg [NeZero n] (β : ℝ) :
    deriv (fun x : ℝ => (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
      (probHaar (MassGap.SUN.SU 3)) x
      (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action) β < 0 := by
  rw [(action_hasDerivAt (by norm_num) (bd (d := 4) (n := n)) β).deriv]
  linarith [clay_action_var_pos (n := n) β]

/-- The mean Wilson action of the four-dimensional `SU(3)` theory is a strictly decreasing function
of `β` on all of `ℝ`: `strictAnti_of_deriv_neg` applied to `clay_mean_action_deriv_neg`.

The measure is the Wilson Gibbs measure built on product Haar over the links with the ordered-loop
holonomy. There is no smallness hypothesis and no bound on `β`; the extent `n` is arbitrary subject
to `NeZero n`, and the geometry is the periodic torus rather than `ℤ⁴`.

DERIVED: the `4` is the lattice dimension, and the `3` is the rank of the gauge group, appearing
both as `wilsonDensity (N := 3)` and as `probHaar (SU 3)`. -/
theorem clay_mean_action_strictAnti [NeZero n] :
    StrictAnti (fun β : ℝ => (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
      (probHaar (MassGap.SUN.SU 3)) β
      (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action) :=
  strictAnti_of_deriv_neg (fun β => clay_mean_action_deriv_neg β)

/-- Distinct couplings give distinct mean actions: from `β₁ ≠ β₂` the two means differ. This is the
injectivity of `clay_mean_action_strictAnti`.

DERIVED: the `4` is the lattice dimension and the `3` the rank of the gauge group, in
`wilsonDensity (N := 3)` and `probHaar (SU 3)`. The subscripts of `β₁` and `β₂` are part of those
identifiers. -/
theorem clay_mean_action_ne_of_ne [NeZero n] {β₁ β₂ : ℝ} (h : β₁ ≠ β₂) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β₁
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
      ≠ (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β₂
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action :=
  fun heq => h ((clay_mean_action_strictAnti (n := n)).injective heq)

/-- At any nonzero coupling the mean action differs from the mean action at `β = 0`, which is the
one taken against product Haar. The `β₂ = 0` instance of `clay_mean_action_ne_of_ne`.

DERIVED: the `4` is the lattice dimension and the `3` the rank of the gauge group; the first `0` is
the hypothesis `β ≠ 0`, and the second is the coupling the comparison is made against. -/
theorem clay_not_free [NeZero n] {β : ℝ} (hβ : β ≠ 0) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
      ≠ (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) 0
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action :=
  clay_mean_action_ne_of_ne hβ

/-- The system the section is stated about is definitionally `WilsonHypercubic.sysWilson 3 4 n`, the
four-dimensional `SU(3)` Wilson lattice gauge system; proved by `rfl`.

DERIVED: in `sysWilson 3 4 n` the `3` is the rank `N` and the `4` the dimension `d`, in that
argument order; on the right-hand side they reappear as `bd (d := 4)` and
`wilsonDensity (N := 3)`. -/
theorem sysWilson_clay (n : ℕ) [NeZero n] :
    sysWilson 3 4 n = wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3)) := rfl

#print axioms action_confOne
#print axioms action_confAB_pos
#print axioms clay_action_var_pos
#print axioms clay_mean_action_deriv_neg
#print axioms clay_mean_action_strictAnti
#print axioms clay_mean_action_ne_of_ne
#print axioms clay_not_free
#print axioms sysWilson_clay

end Clay

end MassGap.AreaLaw
