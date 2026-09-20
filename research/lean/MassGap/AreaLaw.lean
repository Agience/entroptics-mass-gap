import MassGap.PlaqVariance
import MassGap.WilsonAnalytic

/-!
# MassGap.AreaLaw — the rectangular Wilson loop, and coupling-dependence of the Wilson measure

Two independent things live here, and the second is NOT the first.

## Part 1: the rectangular Wilson loop

`WilsonHypercubic.bd` gives the boundary word of a single plaquette — the `1 × 1` Wilson loop.
`rectWord` generalises it to the `R × T` rectangle in the `(μ, ν)` coordinate plane based at a site
`x`, as an ordered list of `(link, orientation)` pairs in the same format, so `WilsonLattice.wilsonHol`
turns it into the ordered loop product with no new machinery. `rectWord_one_one` checks the
generalisation against the tree's own convention: at `R = T = 1` the word IS `bd`, on the nose.

What is proved about the loop is elementary structure: its length is the perimeter `2(R+T)`, a
zero-width rectangle retraces itself and has trivial holonomy, the holonomy conjugates under a global
gauge transformation, the normalised loop observable is bounded by `1` and is continuous.

## Part 2: the Wilson measure moves with the coupling

For the four-dimensional `SU(3)` system on the periodic lattice — the Clay problem's dimension and
group — the mean Wilson action is a strictly decreasing function of `β`, at every real `β`:

    d/dβ ⟨S⟩_β = −(⟨S²⟩_β − ⟨S⟩_β²)  <  0.

The derivative is `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` at the observable `O = S`, where it
is exactly minus the variance of the action. `action_var_pos` gives the strict inequality from two
configurations with different total action: the all-identity configuration has `S = 0`, and the
configuration carrying `PlaqVariance.gA` on one axis and `gB` on the others has `S ≥ 4/3`, because
those two `SU(3)` elements do not commute. Hence `clay_mean_action_strictAnti`, and therefore
`clay_mean_action_ne_of_ne`: no two couplings give the same theory.

Unconditional. No smallness hypothesis, no bound on `β`, no carried input. The negative control
`su_one_mean_action_deriv_zero` shows the derivative is exactly zero for the trivial gauge group, so
the strict inequality is not a formality of the Gibbs construction.

## WHAT PART 2 IS NOT

It is **not an area law**, and nothing in this file is. An area law is a statement about the
`R × T` Wilson loop of Part 1 —

    ∃ σ > 0, ∀ R T, |⟨W(R,T)⟩_β| ≤ exp(−σ · R · T),

with `σ` derived — and no such bound is proved here, at any coupling. Part 1 defines `W(R,T)` and
proves elementary facts about it; Part 2 is about the action `S`, a different observable, and bounds
nothing exponentially in anything.

It is also not a string tension, not confinement, and not a mass gap. What it is: a property of the
constructed `SU(3)` Wilson Gibbs measure that distinguishes it from the product-Haar theory at every
coupling, derived from the measure rather than assumed of it.

### The distance to an area law, named

The exact cluster expansion in `StrongCoupling.lean` is stated for the two-plaquette connected
correlator `WilsonBridge.wilsonCorrConn`. Its two general components — `boltz_eq_subset_sum` and
`corrNum_eq_subset_sum` — are general in the observable, but the vanishing theorem the decay rests on
(`nonbridging_sum_eq_zero`) and every bound downstream of it (`pairTerm`, `corePairs`, `coreRate`,
`corrClay_abs_le_coreConst_mul_rate_pow`) are built on the pair `(p₀, p_d)` and on
`WilsonReal.wilsonPlaqObs`. A Wilson loop is not a product of plaquette densities, so none of them
applies to `loopObs` as stated.

Beyond re-stating those for a loop observable, an area law needs one thing this tree does not have:
the lower bound `|E| ≥ R · T` on the size of an activated set that can contribute — the statement
that a discrete surface spanning the rectangle has at least `R · T` faces. That is the discrete
Plateau problem. The covering condition alone (every loop link met by some activated plaquette)
yields only `|E| ≥ (R + T)/2`, which is a perimeter bound, and a perimeter law is the non-confining
behaviour.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.AreaLaw`.
-/

namespace MassGap.AreaLaw

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic
open MeasureTheory

/-! ## Part 1: the rectangular Wilson loop -/

variable {d n : ℕ}

/-- The `k`-fold unit shift in direction `μ`. `shiftN μ 1 = shift μ`, which is what ties the loop
below to `WilsonHypercubic.bd`'s own step.

DERIVED: `k` is a number of lattice steps, not a length; the lattice spacing never appears. -/
def shiftN [NeZero n] (μ : Fin d) : ℕ → Site d n → Site d n
  | 0, x => x
  | (k + 1), x => shift μ (shiftN μ k x)

@[simp] theorem shiftN_zero [NeZero n] (μ : Fin d) (x : Site d n) : shiftN μ 0 x = x := rfl

@[simp] theorem shiftN_one [NeZero n] (μ : Fin d) (x : Site d n) : shiftN μ 1 x = shift μ x := rfl

/-- **The boundary word of the `R × T` rectangular Wilson loop** in the `(μ, ν)` plane at site `x`.

The four sides in cyclic order: `R` steps along `μ` forwards, `T` steps along `ν` forwards at the far
end, `R` steps back along `μ` inverted (traversed in reverse), `T` steps back along `ν` inverted.
The `Bool` is the orientation, exactly as in `WilsonHypercubic.bd` — `true` is the link, `false` its
inverse — so `WilsonLattice.wilsonHol` reads it as the ordered loop product with no new machinery.

DERIVED: `R` and `T` are the caller's side lengths in lattice steps. The two directions are what a
plane has (`WilsonHypercubic.Plaq`); the orientations are forced by traversing a closed loop. -/
def rectWord [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) : List (Link d n × Bool) :=
  ((List.range R).map (fun i => ((μ, shiftN μ i x), true)))
    ++ ((List.range T).map (fun j => ((ν, shiftN ν j (shiftN μ R x)), true)))
    ++ ((List.range R).reverse.map (fun i => ((μ, shiftN μ i (shiftN ν T x)), false)))
    ++ ((List.range T).reverse.map (fun j => ((ν, shiftN ν j x), false)))

/-- **The `1 × 1` rectangle IS the plaquette.** The generalisation agrees with the tree's own
boundary word on the nose, so the index conventions below are `bd`'s and not a second set. -/
theorem rectWord_one_one [NeZero n] (μ ν : Fin d) (x : Site d n) :
    rectWord μ ν x 1 1 = bd ((μ, ν), x) := by
  simp [rectWord, bd, List.range_one]

/-- **The word's length is the perimeter `2(R+T)`** — a loop traverses `2(R+T)` links, not `R·T` of
them. Recorded because it is the quantity an area law is NOT about. -/
theorem rectWord_length [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    (rectWord μ ν x R T).length = 2 * (R + T) := by
  simp only [rectWord, List.length_append, List.length_map, List.length_range,
    List.length_reverse]
  ring

/-- **The holonomy of the rectangular Wilson loop**: the ordered product of the link variables around
the loop, inverses where the loop runs backwards. This is `WilsonLattice.wilsonHol` on the one-element
index type, so every general fact about `wilsonHol` applies to it. -/
noncomputable def loopHol {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : MassGap.SUN.SU N :=
  wilsonHol (fun _ : Unit => rectWord μ ν x R T) () U

/-- **The normalised Wilson loop observable** `W(R,T) = (1/N)·Re tr` of the loop holonomy. At
`R = T = 1` it is `1 − φ_W`, the plaquette density's complement (`loopObs_one_one`).

DERIVED: the `1` is the numerator of the character normalisation `1/N`, which is what makes `loopObs` equal `1` at the identity configuration for every rank. It is not a scale. -/
noncomputable def loopObs {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  (1 / (N : ℝ))
    * (Matrix.trace ((loopHol μ ν x R T U : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re

/-- The `1 × 1` loop holonomy is the plaquette holonomy. -/
theorem loopHol_one_one {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    loopHol μ ν x 1 1 U = wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U := by
  show (((rectWord μ ν x 1 1).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) = _
  rw [rectWord_one_one]
  rfl

/-- **The loop observable is the complement of the Wilson density of the loop holonomy.** The same
relation `φ_W = 1 − (1/N)·Re tr` the plaquette action already uses, at the loop's own holonomy — so
every bound on `wilsonDensity` transfers to the loop. -/
theorem loopObs_eq {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) :
    loopObs μ ν x R T U = 1 - wilsonDensity (N := N) (loopHol μ ν x R T U) := by
  unfold loopObs wilsonDensity
  ring

/-- The `1 × 1` loop observable is the complement of the plaquette energy: `W(1,1) = 1 − φ_W`. -/
theorem loopObs_one_one {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) :
    loopObs μ ν x 1 1 U
      = 1 - wilsonDensity (N := N) (wilsonHol (bd (d := d) (n := n)) ((μ, ν), x) U) := by
  rw [loopObs_eq, loopHol_one_one]

/-! ### A closed loop that retraces itself

The word is a genuine closed loop, not a list of links that happens to have the right length: a
rectangle of zero width traverses each of its links forwards and then backwards, and its ordered
product collapses to the identity. The two lemmas below are the group-theoretic content, proved by
list induction so nothing depends on a library spelling. -/

/-- The reversed word with every letter inverted has the inverse product. -/
theorem prod_rev_inv {G : Type*} [Group G] {α : Type*} (f : α → G) (l : List α) :
    (l.reverse.map (fun a => (f a)⁻¹)).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev]

/-- **A word followed by its own retracing has trivial product.** -/
theorem prod_retrace {G : Type*} [Group G] {α : Type*} (f : α → G) (l : List α) :
    ((l.map f) ++ (l.reverse.map (fun a => (f a)⁻¹))).prod = 1 := by
  rw [List.prod_append, prod_rev_inv f l, mul_inv_cancel]

/-- **A zero-width rectangle has trivial holonomy.** With `R = 0` the loop runs `T` steps along `ν`
and immediately retraces them, so every link is traversed once forwards and once backwards and the
ordered product is the identity — whatever the configuration. This is the check that `rectWord` is a
closed loop rather than an arbitrary list. -/
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

/-- **The loop holonomy conjugates under a global gauge transformation** — `wilsonHol_conj` at the
loop's own word, so the loop observable `loopObs` is gauge-invariant by trace cyclicity. -/
theorem loopHol_conj {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (g : MassGap.SUN.SU N) (U : Link d n → MassGap.SUN.SU N) :
    loopHol μ ν x R T (fun l => g * U l * g⁻¹) = g * loopHol μ ν x R T U * g⁻¹ :=
  wilsonHol_conj (fun _ : Unit => rectWord μ ν x R T) g () U

/-- The loop holonomy is continuous in the configuration. -/
theorem continuous_loopHol {N : ℕ} [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ) :
    Continuous (loopHol (N := N) μ ν x R T) :=
  MassGap.PlaqVariance.continuous_wilsonHol (fun _ : Unit => rectWord μ ν x R T) ()

/-- The loop observable is continuous, hence measurable — so it is a legitimate observable of the
Gibbs measure. -/
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

/-- **The loop observable is bounded by `1`**, uniformly in `R`, `T` and the configuration: it is a
normalised character of a unitary matrix. This is the trivial bound an area law has to improve on. -/
theorem abs_loopObs_le_one {N : ℕ} (hN : N ≠ 0) [NeZero n] (μ ν : Fin d) (x : Site d n) (R T : ℕ)
    (U : Link d n → MassGap.SUN.SU N) : |loopObs μ ν x R T U| ≤ 1 := by
  have h0 := wilsonDensity_nonneg hN (loopHol μ ν x R T U)
  have h2 := wilsonDensity_le_two hN (loopHol μ ν x R T U)
  rw [loopObs_eq, abs_le]
  constructor <;> linarith

/-- The loop observable at the all-identity configuration is `1` — the maximum. -/
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

/-! ## Part 2: the Wilson measure moves with the coupling

Nothing below concerns the Wilson loop. The observable is the total Wilson action `S = ∑_p φ_W(hol p)`,
and the statement is that its Gibbs mean is strictly decreasing in `β`.

The mechanism is one identity and one inequality. The identity is
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt`, which at an observable `O` gives
`d⟨O⟩/dβ = −(⟨O·S⟩ − ⟨O⟩⟨S⟩)`; taken at `O = S` the right-hand side is exactly minus the variance of
the action. The inequality is that this variance is strictly positive, which needs only two
configurations at which `S` differs.
-/

section Variance

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- **The total Wilson action is bounded by `2·|plaquettes|`**, since each plaquette density lies in
`[0, 2]` (`WilsonAction.wilsonDensity_nonneg`, `wilsonDensity_le_two`). This is the bound
`wilsonSystem_expect_hasDerivAt` asks for at the observable `S`.

DERIVED: the `2` is `wilsonDensity`'s own range and the cardinality is the lattice's own plaquette
count. Neither is chosen. -/
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

/-- **The Gibbs variance of a continuous bounded observable is strictly positive as soon as the
observable takes two different values.**

`PlaqVariance.wilsonCorrConn_self_pos` is this statement for the plaquette-energy observable. The
argument uses nothing specific to that observable: the Gibbs weight is positive and continuous at
every real coupling, so an integrand `(O − ⟨O⟩)²·e^{−βS}` that integrates to zero and is continuous
and nonnegative must vanish identically, forcing `O` to be constant. Stated here for a general `O`
because the observable Part 2 needs is the ACTION, not a plaquette.

No smallness, no sign condition and no bound on `β`. -/
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

/-- **The derivative of the mean action is minus the variance of the action.**

`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` at the observable `O = S`. Stated separately because
`O = S` is the one instance where the general covariance `⟨O·S⟩ − ⟨O⟩⟨S⟩` is a variance, hence signed.

Holds at every real `β`, on any geometry and any `N ≠ 0`. -/
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

/-! ### Negative control: the trivial gauge group does not move

`action_hasDerivAt` holds for every `N ≠ 0`, so on its own it says nothing about whether the theory
depends on the coupling — the derivative it names could be zero. For `SU(1)` it IS zero: the
determinant condition pins the single entry, every holonomy is the identity, the action vanishes
identically, and the mean action is constant in `β` at every geometry.

So `clay_mean_action_deriv_neg` below is not a formality of the Gibbs construction. What carries it
is the strict positivity of the variance, and what carries that is the non-commutation of two
`SU(3)` elements. -/

/-- The Wilson action of the trivial gauge group vanishes identically. -/
theorem action_su_one (bdw : Pq → List (Lk × Bool))
    (U : (wilsonSystem bdw (wilsonDensity (N := 1))).Config) :
    (wilsonSystem bdw (wilsonDensity (N := 1))).action U = 0 := by
  show (∑ _p : Pq, wilsonDensity (N := 1) (wilsonHol bdw _p U)) = 0
  exact Finset.sum_eq_zero (fun p _ => MassGap.PlaqVariance.wilsonDensity_su_one _)

/-- **NEGATIVE CONTROL.** For the trivial gauge group the mean action has derivative exactly zero in
the coupling, at every `β` and on every geometry — the theory really is `β`-independent there. -/
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

/-! ### The Clay instance: four dimensions, `SU(3)`

`PlaqVariance` builds the two configurations this needs and proves the one non-commutation fact they
rest on. `confOne` carries the identity on every link; `confAB` carries `gA` on every direction-`0`
link and `gB` on the others, and `gA`, `gB` are the two `SU(3)` elements whose commutator gives
plaquette energy `4/3` rather than `0`. -/

section Clay

open MassGap.PlaqVariance

variable {n : ℕ}

/-- The all-identity configuration has holonomy `1` on every plaquette. -/
theorem wilsonHol_confOne [NeZero n] (p : Plaq 4 n) :
    wilsonHol (bd (d := 4) (n := n)) p (confOne n) = 1 := by
  show (((bd (d := 4) (n := n) p).map (fun lo => if lo.2 then (1 : MassGap.SUN.SU 3)
    else (1 : MassGap.SUN.SU 3)⁻¹)).prod) = 1
  refine List.prod_eq_one ?_
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨lo, _, rfl⟩ := hg
  cases lo.2 <;> simp

/-- **The all-identity configuration has zero total action** — no flux anywhere. -/
theorem action_confOne [NeZero n] :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action (confOne n) = 0 := by
  show (∑ p : Plaq 4 n, wilsonDensity (N := 3)
    (wilsonHol (bd (d := 4) (n := n)) p (confOne n))) = 0
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [wilsonHol_confOne p]
  exact wilsonDensity_one (by norm_num)

/-- **The commutator configuration has strictly positive total action.** Every plaquette contributes
nonnegatively, and the `(0,1)` plaquette at the origin contributes `4/3`, because `gA` and `gB` do
not commute (`PlaqVariance.wilsonDensity_comm`). -/
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

/-- **The action of four-dimensional `SU(3)` lattice gauge theory has strictly positive variance at
every coupling.** Two configurations, one with `S = 0` and one with `S ≥ 4/3`, are all
`expect_var_pos` needs. The non-commutation of `gA` and `gB` is the whole input. -/
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

/-- **The mean action of the four-dimensional `SU(3)` Wilson theory has strictly negative derivative
in the coupling, at every real `β`.** -/
theorem clay_mean_action_deriv_neg [NeZero n] (β : ℝ) :
    deriv (fun x : ℝ => (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
      (probHaar (MassGap.SUN.SU 3)) x
      (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action) β < 0 := by
  rw [(action_hasDerivAt (by norm_num) (bd (d := 4) (n := n)) β).deriv]
  linarith [clay_action_var_pos (n := n) β]

/-- **THE STATEMENT: the mean Wilson action is a strictly decreasing function of the coupling.**

Four dimensions, `SU(3)`, the genuine Wilson action, product Haar over links, ordered-loop holonomy —
and the map `β ↦ ⟨S⟩_β` is strictly decreasing on all of `ℝ`. Unconditional: no smallness hypothesis,
no carried input, no restriction on the periodic extent.

This is NOT an area law and NOT a string tension. What it says is that the constructed measure
genuinely depends on the coupling — the theory is not the `β`-independent product-Haar theory, and
the dependence is derived from the measure rather than asserted of it. -/
theorem clay_mean_action_strictAnti [NeZero n] :
    StrictAnti (fun β : ℝ => (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
      (probHaar (MassGap.SUN.SU 3)) β
      (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action) :=
  strictAnti_of_deriv_neg (fun β => clay_mean_action_deriv_neg β)

/-- **No two couplings give the same theory.** An immediate consequence of strict monotonicity, and
the form in which "the theory is not `β`-independent" is checkable. -/
theorem clay_mean_action_ne_of_ne [NeZero n] {β₁ β₂ : ℝ} (h : β₁ ≠ β₂) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β₁
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
      ≠ (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β₂
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action :=
  fun heq => h ((clay_mean_action_strictAnti (n := n)).injective heq)

/-- **The theory at any nonzero coupling differs from the free theory.** The `β = 0` instance of the
statement above, written out because "product Haar" is the free theory and this is the corner that
names it. -/
theorem clay_not_free [NeZero n] {β : ℝ} (hβ : β ≠ 0) :
    (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) β
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action
      ≠ (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).expect
        (probHaar (MassGap.SUN.SU 3)) 0
        (wilsonSystem (bd (d := 4) (n := n)) (wilsonDensity (N := 3))).action :=
  clay_mean_action_ne_of_ne hβ

/-- The system Part 2 is about is `WilsonHypercubic.sysWilson 3 4 n` — the four-dimensional `SU(3)`
Wilson lattice gauge system, not a relabelling of one. -/
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
