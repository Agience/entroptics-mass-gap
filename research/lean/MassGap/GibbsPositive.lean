import MassGap.CompactGauge
import MassGap.SUN
import MassGap.WilsonAction
import MassGap.WilsonLattice
import MassGap.WilsonReal

/-!
# MassGap.GibbsPositive — strict positivity of the Gibbs expectation of the plaquette energy

This module proves `0 < expect φ_p` for the Wilson system at every coupling `β`, given a single
configuration at which the plaquette energy is positive.

## The chain

`System.expect` is `corrNum / partition`, and the two halves are separate.

* `WilsonReal.wilsonSystem_partition_pos` gives `0 < partition` and is used unchanged.
* `corrNum_plaqObs_pos` gives `0 < corrNum` from a single configuration at which the plaquette energy
  is positive. The integrand `φ_p · e^{−βS}` is nonnegative by `wilsonPlaqObs_nonneg` and
  `wilsonSystem_boltz_pos`, and continuous by `continuous_plaqObs` and `continuous_boltz` — which is
  what this module adds to the measurability already available. The product Haar measure is positive
  on nonempty opens, so `Continuous.ae_eq_iff_eq` upgrades a vanishing integral to vanishing at every
  configuration, which the supplied configuration contradicts.

The witnessing configuration for `SU(3)` uses `gD = diag(1, −1, −1) ∈ SU(3)`, whose Wilson density is
`4/3` (`wilsonDensity_gD`).

## Scope

Each statement is at a fixed coupling, and no statement here bounds the expectation from below
uniformly in `β`.

## Controls

* `wilsonSystem_expect_sub_const` — the expectation of an observable shifted by a constant.
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

/-! ### The reflected Schwinger form of the gauge families is strictly positive -/

/-! ### Shifting an observable by a constant

`corrNum_plaqObs_pos` consumes the nonnegativity of the plaquette energy. The shift of an observable
by a constant shifts its expectation by that constant. -/

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
#print axioms expect_plaqObs_su_one_eq_zero

end MassGap.GibbsPositive
