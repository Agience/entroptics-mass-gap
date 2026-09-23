import MassGap.WilsonGauge

/-!
# MassGap.GibbsPositive — strict positivity of the Gibbs expectation of the plaquette energy

`WilsonGauge.QG` is the clamp

    QG j a = min (max (sysYM.expect (probHaar G3) a O0) 0) 1,

with `sysYM` the four-dimensional periodic `SU(3)` Wilson system and `O0` the plaquette energy of the
plane-`(0,1)` plaquette at the origin. This module proves `0 < QG j a` at every `j` and every `a`, so
the lower clamp never fires and `QG` is nowhere zero.

## The chain

`System.expect` is `corrNum / partition`, and the two halves are separate.

* `WilsonReal.wilsonSystem_partition_pos` gives `0 < partition` and is used unchanged.
* `corrNum_plaqObs_pos` gives `0 < corrNum` from a single configuration at which the plaquette energy
  is positive. The integrand `φ_p · e^{−βS}` is nonnegative by `wilsonPlaqObs_nonneg` and
  `wilsonSystem_boltz_pos`, and continuous by `continuous_plaqObs` and `continuous_boltz` — which is
  what this module adds to the measurability already available. The product Haar measure is positive
  on nonempty opens, so `Continuous.ae_eq_iff_eq` upgrades a vanishing integral to vanishing at every
  configuration, which the supplied configuration contradicts.

The configuration is `confD`: the identity on every link except those in direction `0` whose site has
axis-`1` coordinate `0`, which carry `gD = diag(1, −1, −1) ∈ SU(3)`. Of the four boundary links of the
plaquette `((0,1), origin)` only `(0, origin)` meets that description, so `hol_confD` reads the
boundary word as `gD · 1 · 1⁻¹ · 1⁻¹ = gD` and `plaqObs_confD` evaluates its Wilson density to `4/3`.

`expect_O0_pos`, `QG_pos`, `QG_ne_zero`, `ymFamilyGauge_Q_pos` and `ymFamilyGaugeCounted_Q_pos` are
the consequences. `QYM_pos_of` is the corresponding statement for `MassGap.QYM`, conditional on a
supplied positivity of `wilsonCorrAt` at one lag.

## Scope

Each statement is at a fixed coupling. `QG j a` is the expectation at `β = a`, and no statement here
bounds `QG j a` from below uniformly in `a`, so nothing here is about a limit in `a` or about the
limit `q` that `Measure.continuum_of_family` produces.

`ymFamilyGaugeCounted` and `ymFamilyGauge` carry `QG` as their reflected form, which is why the
positivity covers them. `WilsonInstance.ymFamily` does not: its form is `QYM N`, and no statement
here equates the two, so `QYM_pos_of` takes the positivity of the correlation as a hypothesis.

## Negative controls

* `expect_centred_eq_zero` — on the same system, at the same coupling and against the same measure,
  the centred plaquette energy `O0 − ⟨O0⟩` has expectation exactly `0`, while
  `centred_ne_zero_at_identity` shows it is not the zero function. The nonnegativity of the observable
  is therefore load-bearing.
* `expect_plaqObs_su_one_eq_zero` — for `SU(1)` the plaquette energy is identically zero and the
  expectation is exactly `0`, at every coupling and every geometry. The existence of a group element
  whose real trace falls below `N` is therefore load-bearing too.
-/

namespace MassGap.GibbsPositive

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal
open MeasureTheory

/-! ### Continuity of the Wilson observables

`WilsonReal` proves measurability. The step from "the integral vanishes" to "the integrand vanishes
at every configuration" needs continuity instead, so these four mirror the measurability proofs with
`Continuous` in place of `Measurable`. -/

/-- For any list `l : List (L × Bool)`, the map sending `U : L → G` to the ordered product of its
step factors is continuous, for `G` a topological group. List induction: the empty product is
constant, and the cons step is `Continuous.mul` of a coordinate projection, inverted or not, with the
inductive hypothesis.

The continuity counterpart of `WilsonLattice.measurable_stepListProd`; `IsTopologicalGroup G` is what
makes multiplication and inversion continuous.

DERIVED: no numeral. -/
theorem continuous_stepProd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {L : Type} (l : List (L × Bool)) :
    Continuous (fun U : L → G => (l.map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod) := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil]; exact continuous_const
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Continuous.mul ?_ ih
    by_cases ha : a.2 = true
    · have he : (fun U : L → G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => U a.1 :=
        funext fun U => if_pos ha
      rw [he]; exact continuous_apply a.1
    · have he : (fun U : L → G => if a.2 then U a.1 else (U a.1)⁻¹) = fun U => (U a.1)⁻¹ :=
        funext fun U => if_neg ha
      rw [he]; exact (continuous_apply a.1).inv

/-- `wilsonHol bd p` is continuous in the configuration, for every boundary word assignment and every
plaquette. It is `continuous_stepProd` at the list `bd p`.

DERIVED: no numeral. -/
theorem continuous_hol {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {L P : Type} (bd : P → List (L × Bool)) (p : P) :
    Continuous (wilsonHol (G := G) bd p) :=
  continuous_stepProd (bd p)

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- `wilsonPlaqObs bd p` is continuous: `continuous_wilsonDensity` composed with `continuous_hol`.

DERIVED: no numeral. `N` is the section variable. -/
theorem continuous_plaqObs (bd : Pq → List (Lk × Bool)) (p : Pq) :
    Continuous (wilsonPlaqObs (N := N) bd p) :=
  continuous_wilsonDensity.comp (continuous_hol bd p)

/-- `(wilsonSystem bd wilsonDensity).action` is continuous. It is a finite sum of the plaquette
densities, each continuous, so `continuous_finsetSum` applies; finiteness of `Pq` is what makes the
sum finite.

DERIVED: no numeral. -/
theorem continuous_action (bd : Pq → List (Lk × Bool)) :
    Continuous (wilsonSystem bd (wilsonDensity (N := N))).action := by
  show Continuous fun U => ∑ p : Pq, wilsonDensity (wilsonHol bd p U)
  exact continuous_finsetSum _ (fun p _ => continuous_wilsonDensity.comp (continuous_hol bd p))

/-- `(wilsonSystem bd wilsonDensity).boltz β` is continuous, at every real `β`. It unfolds to
`Real.exp` of a constant multiple of the action, so `Real.continuous_exp` composed with
`continuous_action` closes it.

DERIVED: no numeral. `β` is unrestricted in sign. -/
theorem continuous_boltz (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Continuous ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) := by
  show Continuous fun U => Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action U)
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_action bd))

/-! ### The Gibbs expectation of the plaquette energy is strictly positive -/

/-- For `N ≠ 0` and any real `β`, the correlation numerator `∫ φ_p · e^{−βS}` is strictly positive as
soon as one configuration `U₀` has `0 < wilsonPlaqObs bd p U₀`.

The integral is nonnegative by `wilsonPlaqObs_nonneg` and `wilsonSystem_boltz_pos`, and integrable by
`wilsonSystem_mul_boltz_integrable` at the bound `2`. If it were `0`, then
`integral_eq_zero_iff_of_nonneg` would make the integrand vanish almost everywhere, and
`Continuous.ae_eq_iff_eq` — available because the product Haar measure is `IsOpenPosMeasure` and the
integrand is continuous — would make it vanish everywhere, contradicting `hU₀`.

`β` carries no sign condition, no smallness and no bound; the only inputs are the positivity of the
Gibbs weight, the continuity of the integrand, and one configuration.

DERIVED: `0` is the value `N` is required to differ from in `hN`, the strict lower bound on the
plaquette energy at `U₀` in `hU₀`, and the strict lower bound concluded of the numerator. -/
theorem corrNum_plaqObs_pos (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U₀ : (wilsonSystem bd (wilsonDensity (N := N))).Config)
    (hU₀ : 0 < wilsonPlaqObs (N := N) bd p U₀) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).corrNum
        (probHaar (MassGap.SUN.SU N)) β (wilsonPlaqObs (N := N) bd p) := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  haveI : ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure :=
    inferInstanceAs ((Measure.pi
      (fun _ : Lk => probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure)
  have hwpos : ∀ U, 0 < (wilsonSystem bd (wilsonDensity (N := N))).boltz β U :=
    fun U => wilsonSystem_boltz_pos bd β U
  have hnn : (0 : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
      ≤ fun U => wilsonPlaqObs (N := N) bd p U
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U :=
    fun U => mul_nonneg (wilsonPlaqObs_nonneg hN bd p U) (hwpos U).le
  have hint : Integrable (fun U => wilsonPlaqObs (N := N) bd p U
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bd β (wilsonPlaqObs (N := N) bd p)
      (measurable_wilsonPlaqObs bd p) 2
      (fun U => abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hN bd p U],
        wilsonPlaqObs_le_two hN bd p U⟩)
  unfold System.corrNum
  refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => ?_)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
  have hcont : Continuous (fun U => wilsonPlaqObs (N := N) bd p U
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U) :=
    (continuous_plaqObs bd p).mul (continuous_boltz bd β)
  have hzero := (Continuous.ae_eq_iff_eq
    ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))
    hcont continuous_const).mp hae
  have hU : wilsonPlaqObs (N := N) bd p U₀
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U₀ = 0 := congrFun hzero U₀
  exact hU₀.ne' ((mul_eq_zero.mp hU).resolve_right (hwpos U₀).ne')

/-- Under the same hypotheses as `corrNum_plaqObs_pos`, the Gibbs expectation of the plaquette energy
is strictly positive. `System.expect` unfolds to `corrNum / partition`, and `div_pos` combines
`corrNum_plaqObs_pos` with `WilsonReal.wilsonSystem_partition_pos`.

DERIVED: `0` is the value `N` is required to differ from in `hN`, the strict lower bound on the
plaquette energy at `U₀`, and the strict lower bound concluded of the expectation; all three are
`corrNum_plaqObs_pos`'s. -/
theorem expect_plaqObs_pos (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U₀ : (wilsonSystem bd (wilsonDensity (N := N))).Config)
    (hU₀ : 0 < wilsonPlaqObs (N := N) bd p U₀) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (wilsonPlaqObs (N := N) bd p) := by
  unfold System.expect
  exact div_pos (corrNum_plaqObs_pos hN bd p β U₀ hU₀) (wilsonSystem_partition_pos hN bd β)

/-! ### One `SU(3)` element and one configuration carrying a nonzero plaquette energy -/

/-- The matrix `diag(1, −1, −1)` of size three over `ℂ`. Real, symmetric (`matD_star`), an involution
(`matD_mul_self`), and of determinant one, hence special-unitary (`matD_mem`).

DERIVED: `3` is the rank, the size of the matrix; `0` are the six off-diagonal entries, which make it
diagonal. The diagonal entries `1`, `-1`, `-1` are square roots of unity multiplying to
`1 * (-1) * (-1) = 1`, which is what puts the matrix in `SU(3)` rather than only in `U(3)`, so they
are forced by the determinant condition rather than chosen. -/
def matD : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem matD_star : star matD = matD := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matD]

theorem matD_mul_self : matD * matD = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matD, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matD_mem : matD ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, matD_star]; exact matD_mul_self
  · simp [matD, Matrix.det_fin_three]

/-- `matD` as an element of `SU 3`, paired with `matD_mem`.

DERIVED: `3` is the rank, the matrix dimension, carried from `matD`; the definition introduces no
numeral of its own. -/
noncomputable def gD : MassGap.SUN.SU 3 := ⟨matD, matD_mem⟩

@[simp] theorem gD_coe : (gD : Matrix (Fin 3) (Fin 3) ℂ) = matD := rfl

/-- `wilsonDensity gD = 4 / 3` at `N = 3`. The real trace of `matD` is `1 + (−1) + (−1) = −1`, and
`wilsonDensity` is `1 − (Re tr)/N`, so the value is `1 − (−1)/3 = 4/3`.

This is the only place a specific group element's trace enters the positivity; what the argument
needs is that the value is nonzero.

DERIVED: `3` in `N := 3` is the rank and the denominator of the density's normalisation; the two are
the same number. `4 / 3` is `1 − (−1)/3`, the value forced by `matD`'s trace, so neither `4` nor the
second `3` is chosen. -/
theorem wilsonDensity_gD : wilsonDensity (N := 3) gD = 4 / 3 := by
  unfold wilsonDensity
  rw [gD_coe]
  norm_num [matD, Matrix.trace_fin_three_of, Complex.add_re, Complex.neg_re, Complex.one_re]

/-- The configuration on `Link 4 WilsonGauge.nYM` carrying `gD` on every link whose direction is `0`
and whose site has axis-`1` coordinate `0`, and the group identity on every other link.

Of the four boundary links of the plaquette `((0,1), origin)`, only `(0, origin)` meets that
description: the other direction-`0` link sits at `origin + 1̂`, whose axis-`1` coordinate is `1`.
`hol_confD` is that computation.

DERIVED: `4` is the spatial dimension, fixing the link type. `0` is the direction the configuration
acts in and the axis-`1` coordinate it selects; the `1` in `l.2 1` is the axis whose coordinate is
read, chosen as the plaquette's second direction so that the two direction-`0` links of the boundary
word are distinguished. `1` is the group identity carried on every other link. -/
noncomputable def confD : MassGap.WilsonHypercubic.Link 4 WilsonGauge.nYM → WilsonGauge.G3 :=
  fun l => if l.1 = 0 then (if l.2 1 = 0 then gD else 1) else 1

/-- The holonomy of the plaquette `((0, 1), origin)` at the configuration `confD` is `gD`. The four
boundary factors evaluate to `gD`, `1`, `1⁻¹` and `1⁻¹`, so the ordered product collapses to `gD`;
the three auxiliary equations identify each link's value.

DERIVED: `4` is the spatial dimension. `0` and `1` are the two directions of the plaquette's plane,
and `fun _ => 0` is the origin site, every coordinate zero. -/
theorem hol_confD :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD = gD := by
  have h1 : confD ((0 : Fin 4),
      (fun _ => 0 : MassGap.WilsonHypercubic.Site 4 WilsonGauge.nYM)) = gD := by
    simp [confD]
  have h2 : ∀ x : MassGap.WilsonHypercubic.Site 4 WilsonGauge.nYM,
      confD ((1 : Fin 4), x) = 1 := by
    intro x; simp [confD]
  have h3 : confD ((0 : Fin 4),
      MassGap.WilsonHypercubic.shift (d := 4) (n := WilsonGauge.nYM) 1 (fun _ => 0)) = 1 := by
    simp [confD, MassGap.WilsonHypercubic.shift]
  simp [wilsonHol, MassGap.WilsonHypercubic.bd, h1, h2, h3]

/-- `wilsonPlaqObs bd ((0,1), origin) confD = 4 / 3` at `N = 3`, `d = 4`. The observable unfolds to
`wilsonDensity` of the holonomy, which `hol_confD` identifies as `gD` and `wilsonDensity_gD`
evaluates.

The configuration `corrNum_plaqObs_pos` requires; what it supplies is a positive value, and `4 / 3`
is positive.

DERIVED: `3` is the colour rank and `4` the spatial dimension. `0` and `1` are the plaquette's plane
and `fun _ => 0` its base site. The value `4 / 3` is `wilsonDensity_gD`'s, forced by `matD`'s
trace. -/
theorem plaqObs_confD :
    wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD = 4 / 3 := by
  show wilsonDensity (N := 3)
    (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD) = 4 / 3
  rw [hol_confD]
  exact wilsonDensity_gD

/-! ### The reflected Schwinger form of the gauge families is strictly positive -/

/-- `0 < WilsonGauge.sysYM.expect (probHaar G3) β WilsonGauge.O0`, at every real `β`.
`expect_plaqObs_pos` with `confD` as the witnessing configuration and `plaqObs_confD` as the
positivity at it.

`β` is unrestricted: negative couplings are included, since nothing in `expect_plaqObs_pos`
constrains the sign.

DERIVED: `0` is the strict lower bound concluded; it is the only numeral in the statement. The rank
`3`, the dimension `4` and the plane `(0, 1)` are `WilsonGauge.sysYM`'s and `WilsonGauge.O0`'s. -/
theorem expect_O0_pos (β : ℝ) :
    0 < WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0 := by
  have hobs : 0 < wilsonPlaqObs (N := 3)
      (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD := by
    rw [plaqObs_confD]; norm_num
  exact expect_plaqObs_pos (N := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
    (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) β confD hobs

/-- `0 < WilsonGauge.QG j a`, at every `j` and every `a`. `QG_eq` unfolds the clamp; `expect_O0_pos`
at the coupling `(a : ℝ)` makes `max_eq_left` applicable, so the lower clamp is inert, and `lt_min`
then compares the positive expectation with `1`.

So the lower clamp `max · 0` never fires, and the upper clamp `min · 1` cannot produce `0` because
both of its arguments are positive.

DERIVED: `4` is the spatial dimension, in the two permutation groups `Equiv.Perm (Fin 4)` of the
index type. `0` is the strict lower bound concluded. The clamp bounds `0` and `1` are
`WilsonGauge.QG`'s own. -/
theorem QG_pos (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    0 < WilsonGauge.QG j a := by
  rw [WilsonGauge.QG_eq]
  have h := expect_O0_pos (a : ℝ)
  rw [max_eq_left h.le]
  exact lt_min h one_pos

/-- `WilsonGauge.QG j a ≠ 0` at every `j` and `a`, from `QG_pos`. So `QG` is not the identically-zero
form.

DERIVED: `4` is the spatial dimension in the index type; `0` is the value denied. Both are
`QG_pos`'s. -/
theorem QG_ne_zero (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    WilsonGauge.QG j a ≠ 0 := (QG_pos j a).ne'

/-- `0 < (WilsonGauge.ymFamilyGaugeCounted ev edge c hsorted hcount hres).Q j a`, for every choice of
spectral data `ev`, `edge`, `c` and the three hypotheses about them. The body is `QG_pos`: that
family's `Q` field is `QG` whatever spectrum it is built from, so the positivity does not depend on
the spectral arguments at all.

`WilsonModel.ymFamilyTension` is one instantiation.

DERIVED: `0` is the strict lower bound concluded, carried from `QG_pos`. `1` in `hres` is the least
resolved dimension the family's construction requires, a hypothesis passed through untouched; `ev`,
`edge` and `c` are the caller's. -/
theorem ymFamilyGaugeCounted_Q_pos
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((MassGap.Measure.resolvedDim (Finset.range (WilsonGauge.NaG a))
      (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ MassGap.Measure.resolvedDim (Finset.range (WilsonGauge.NaG a)) (ev a) edge)
    (j : (WilsonGauge.ymFamilyGaugeCounted ev edge c hsorted hcount hres).J) (a : ℕ) :
    0 < (WilsonGauge.ymFamilyGaugeCounted ev edge c hsorted hcount hres).Q j a :=
  QG_pos j a

/-- `0 < WilsonGauge.ymFamilyGauge.Q j a` at every `j` and `a`. That family's `Q` field is `QG`, so
the body is `QG_pos`.

Its reflected form is therefore nowhere zero, and the family is not the one that satisfies the
`LatticeYMFamily` inequalities by being identically zero.

DERIVED: `0` is the strict lower bound concluded, carried from `QG_pos`. -/
theorem ymFamilyGauge_Q_pos (j : WilsonGauge.ymFamilyGauge.J) (a : ℕ) :
    0 < WilsonGauge.ymFamilyGauge.Q j a := QG_pos j a

theorem ymFamilyGauge_Q_ne_zero (j : WilsonGauge.ymFamilyGauge.J) (a : ℕ) :
    WilsonGauge.ymFamilyGauge.Q j a ≠ 0 := (QG_pos j a).ne'

/-- `0 < MassGap.QYM N j a`, given `0 < wilsonCorrAt N a` at the lag `j.2.2 % (N + 1)`. `QYM` is a
`min` against `1`, so `lt_min` applied to the hypothesis and `one_pos` closes it.

`QYM N` is the reflected form of `WilsonInstance.ymFamily`, and it is not `QG`; no statement here
equates the two, which is why the correlation's positivity is a hypothesis rather than a conclusion.

Stated about `QYM` directly rather than about `(ymFamily N).Q`, which it equals definitionally:
`ymFamily` carries an even-extent hypothesis that this statement does not need, since it concerns one
lag at any extent.

DERIVED: `0` is the strict lower bound assumed of the correlation and concluded of `QYM`. `1` in
`N + 1` is the number of lags, the size of the index type `Fin (N + 1)` that the modulus lands in;
the clamp's own `1` is `QYM`'s. The `2`s in `j.2.2` are structure projections selecting the third
component of the index `j`, not numbers. -/
theorem QYM_pos_of (N a : ℕ) (j : MassGap.JYM)
    (hd : 0 < MassGap.wilsonCorrAt N (a : ℝ)
            ⟨j.2.2 % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩) :
    0 < MassGap.QYM N j a :=
  lt_min hd one_pos

/-! ### Negative control 1: an observable on the same system whose expectation is zero

`corrNum_plaqObs_pos` consumes the nonnegativity of the plaquette energy. Without it the conclusion
fails on the same system, at the same coupling and against the same measure: the centred plaquette
energy integrates to exactly zero while being nonzero at an explicit configuration. -/

/-- Shifting an observable by a constant `c` shifts its Gibbs expectation by `c`:
`expect (fun U => O U - c) = expect O - c`, for `N ≠ 0`, any real `β`, and any measurable `O`
bounded in absolute value by some `M`.

The numerator splits by `integral_add` into the original integral and `(-c)` times the partition
function; dividing by the partition function, which `wilsonSystem_partition_pos` makes nonzero, leaves
`-c`. The boundedness hypothesis `hb` is what supplies integrability through
`wilsonSystem_mul_boltz_integrable`.

DERIVED: `0` is the value `N` is required to differ from in `hN`; it is the only numeral. `M` and `c`
are the caller's. -/
theorem wilsonSystem_expect_sub_const (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hb : ∀ U, |O U| ≤ M) (c : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O U - c)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O - c := by
  have hZne : (wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β ≠ 0 := (wilsonSystem_partition_pos hN bd β).ne'
  have hintO : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bd β O hmeas M hb
  have hintW : Integrable (fun U => (-c) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (-c)) measurable_const |c|
      (fun _ => le_of_eq (abs_neg c))
  unfold System.expect System.corrNum
  have h : (fun U => (O U - c) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      = (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
          + (-c) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U) := by
    funext U; ring
  rw [h, integral_add hintO hintW, integral_const_mul,
    show (∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = (wilsonSystem bd (wilsonDensity (N := N))).partition
          (probHaar (MassGap.SUN.SU N)) β from rfl,
    add_div, mul_div_assoc, div_self hZne, mul_one]
  ring

/-- The centred plaquette energy `O0 − ⟨O0⟩` has Gibbs expectation exactly `0`, at every real `β`, on
the same system and against the same measure as `expect_O0_pos`.
`wilsonSystem_expect_sub_const` at `c = ⟨O0⟩` and the bound `2`, followed by `sub_self`.

So `expect_O0_pos` is not a property of every observable on this system; it holds of the plaquette
energy because that observable is nonnegative, and the centred one is not.

DERIVED: `0` is the value concluded of the expectation. `3` and `4` are the rank and dimension of
`sysYM`, `(0, 1)` the plaquette's plane and `fun _ => 0` its base site, all carried from
`WilsonGauge.O0`; `2` is the bound on the plaquette energy passed to
`wilsonSystem_expect_sub_const`, which is `wilsonPlaqObs_le_two`'s. -/
theorem expect_centred_eq_zero (β : ℝ) :
    WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β
        (fun U => WilsonGauge.O0 U
          - WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0) = 0 := by
  have hEq : WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0
      = (wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
            (wilsonDensity (N := 3))).expect (probHaar (MassGap.SUN.SU 3)) β
          (wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
            (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM)) := rfl
  have h := wilsonSystem_expect_sub_const (N := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM)) β
    (wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM))
    (measurable_wilsonPlaqObs _ _) 2
    (fun U => abs_le.mpr ⟨by
        linarith [wilsonPlaqObs_nonneg (N := 3) (by norm_num)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
          (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) U],
      wilsonPlaqObs_le_two (N := 3) (by norm_num)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
        (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) U⟩)
    (WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0)
  refine h.trans ?_
  rw [← hEq]
  exact sub_self _

/-- `WilsonGauge.O0 (fun _ => 1) = 0`: at the all-identity configuration the boundary word multiplies
to the identity, and `wilsonDensity_one` evaluates the density there.

`N ≠ 0` is what makes the density at the identity `0` rather than undefined, and is discharged by
`norm_num` at `N = 3`.

DERIVED: `1` is the group identity carried on every link; `0` is the value of the plaquette energy
there. `3` and `4` are the rank and dimension of `sysYM`, and `(0, 1)` the plaquette's plane. -/
theorem O0_confOne : WilsonGauge.O0 (fun _ => 1) = 0 := by
  have hhol : WilsonGauge.sysYM.hol
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM)
      (fun _ => (1 : WilsonGauge.G3)) = 1 := by
    show wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM)
      (fun _ => (1 : WilsonGauge.G3)) = 1
    simp [wilsonHol, MassGap.WilsonHypercubic.bd]
  unfold WilsonGauge.O0
  rw [hhol]
  exact wilsonDensity_one (N := 3) (by norm_num)

/-- The centred plaquette energy is nonzero at the all-identity configuration, at every real `β`:
`O0 (fun _ => 1) − ⟨O0⟩ ≠ 0`. `O0_confOne` makes it `−⟨O0⟩`, which `expect_O0_pos` makes nonzero.

Together with `expect_centred_eq_zero` this shows that an observable can have expectation `0` without
being the zero function, so the nonnegativity hypothesis in `corrNum_plaqObs_pos` cannot be dropped.

DERIVED: `1` is the group identity carried on every link; `0` is the value denied of the centred
observable. -/
theorem centred_ne_zero_at_identity (β : ℝ) :
    WilsonGauge.O0 (fun _ => 1)
      - WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0 ≠ 0 := by
  rw [O0_confOne, zero_sub, neg_ne_zero]
  exact (expect_O0_pos β).ne'

/-! ### Negative control 2: the trivial gauge group

`expect_plaqObs_pos` also consumes the existence of a group element whose real trace falls below `N`.
For `SU(1)` the determinant condition pins the single entry to `1`, every holonomy is the identity,
the plaquette energy is identically zero, and the expectation is exactly zero — at every coupling and
on every geometry. -/

/-- `wilsonDensity g = 0` for every `g : SU 1`. The determinant of a one-by-one matrix is its single
entry, which `SU` pins to `1`, so the trace is `1` and the density `1 − 1/1` is `0`.

DERIVED: `1` is the rank, which makes the matrix one-by-one, and the value its entry, trace and
determinant all take. `0` is the resulting density. -/
theorem wilsonDensity_su_one (g : MassGap.SUN.SU 1) : wilsonDensity g = 0 := by
  have hdet : (g : Matrix (Fin 1) (Fin 1) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rw [Matrix.det_fin_one] at hdet
  have htr : Matrix.trace (g : Matrix (Fin 1) (Fin 1) ℂ) = (1 : ℂ) := by
    rw [Matrix.trace_fin_one]; exact hdet
  unfold wilsonDensity
  rw [htr]
  norm_num

/-- At `N = 1` the Gibbs expectation of the plaquette energy is exactly `0`, for every boundary word
assignment, every plaquette and every real `β`. Every value of the observable is `0` by
`wilsonDensity_su_one`, so the numerator integrates to `0`.

Holds at every geometry and every coupling, so the strict positivity of `expect_plaqObs_pos` genuinely
depends on the gauge group having an element whose real trace falls below `N`.

DERIVED: `1` is the rank of the gauge group instantiated; `0` is the value concluded of the
expectation. -/
theorem expect_plaqObs_su_one_eq_zero (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := 1))).expect (probHaar (MassGap.SUN.SU 1)) β
      (wilsonPlaqObs (N := 1) bd p) = 0 := by
  have hobs : ∀ U : (wilsonSystem bd (wilsonDensity (N := 1))).Config,
      wilsonPlaqObs (N := 1) bd p U = 0 := fun U => wilsonDensity_su_one _
  unfold System.expect System.corrNum
  simp only [hobs, zero_mul, integral_zero, zero_div]

#print axioms corrNum_plaqObs_pos
#print axioms expect_plaqObs_pos
#print axioms wilsonDensity_gD
#print axioms plaqObs_confD
#print axioms expect_O0_pos
#print axioms QG_pos
#print axioms ymFamilyGauge_Q_pos
#print axioms ymFamilyGaugeCounted_Q_pos
#print axioms QYM_pos_of
#print axioms expect_centred_eq_zero
#print axioms centred_ne_zero_at_identity
#print axioms expect_plaqObs_su_one_eq_zero

end MassGap.GibbsPositive
