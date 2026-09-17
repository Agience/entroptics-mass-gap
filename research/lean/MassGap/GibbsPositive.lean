import MassGap.WilsonGauge

/-!
# MassGap.GibbsPositive — the reflected Schwinger form of the gauge families is strictly positive

Every `LatticeYMFamily` in the tree carries its reflected form `Q` as data, and the Osterwalder–
Schrader fields it must satisfy are `0 ≤ Q`, `Q ≤ resolvedDim · B`, and two invariances. All four
hold vacuously of `Q ≡ 0`, so nothing in the family interface distinguishes the physical measure from
the zero one. For `WilsonGauge.QG` the clamp `min (max · 0) 1` makes that gap concrete: the lower
clamp would manufacture `0` out of any expectation that failed to be positive.

This file closes it for the gauge families. The reflected form is

    QG j a = min (max (sysYM.expect (probHaar G3) a O0) 0) 1,

`sysYM` the four-dimensional periodic `SU(3)` Wilson system and `O0` the plaquette energy of the
plane-`(0,1)` plaquette at the origin, and the file proves `0 < QG j a` for EVERY test configuration
`j` and EVERY spacing index `a`.

## What the positivity rests on

`System.expect` is `corrNum / partition`, so the two halves are separate:

* `0 < partition` is already in the tree — `WilsonReal.wilsonSystem_partition_pos`, from the pointwise
  positivity of `e^{−βS}` and the uniform bound `0 ≤ S ≤ 2·#Plaq` that `wilsonDensity_nonneg` /
  `wilsonDensity_le_two` supply. Nothing here re-proves it.
* `0 < corrNum` is `corrNum_plaqObs_pos`. The integrand `φ_p · e^{−βS}` is nonnegative
  (`wilsonPlaqObs_nonneg`, `wilsonSystem_boltz_pos`) and CONTINUOUS, and the product Haar measure over
  the links is positive on nonempty opens (`probHaar` is a Haar measure, hence `IsOpenPosMeasure`;
  `Measure.pi` carries that to configurations). A continuous nonnegative function with zero integral
  against such a measure vanishes at EVERY configuration (`Continuous.ae_eq_iff_eq`), so a single
  configuration at which the plaquette energy is nonzero rules the integral being zero out.

The remaining obligation is therefore one configuration with a nonzero plaquette energy, and
`confD` is it: the identity on every link except the one link `(direction 0, ν-slice 0)` of the
plaquette's boundary word, which carries `gD = diag(1,−1,−1) ∈ SU(3)`. The boundary word then reads
`gD · 1 · 1⁻¹ · 1⁻¹ = gD`, whose Wilson density is `4/3`. Only the periodic extent `nYM = 2` is used,
so that the two `direction 0` links of the word are distinct links.

## What this does and does not settle

It settles that `Q` is not identically zero at any finite spacing, for `ymFamilyGauge`, for every
`ymFamilyGaugeCounted` family (hence for `WilsonModel.ymFamilyTension`), and — conditionally on one
named positivity — for `WilsonInstance.ymFamily`.

It does NOT settle that the continuum limit `q` produced by `Measure.continuum_of_family` is nonzero.
`QG j a` is the expectation at coupling `β = a`, the limit is taken along `a → ∞`, and the lower bound
this file gives degrades with `a` (the integrand's own lower bound is `e^{−2a·#Plaq}`). A nonzero `q`
needs a bound on `QG j a` uniform in `a`, which is a different statement and is not proved here.

## Negative controls

Two, because the positivity has two inputs and each can fail on its own.

* `expect_centred_eq_zero` — on the SAME system, at the SAME coupling, the CENTRED plaquette energy
  `O0 − ⟨O0⟩` has expectation exactly `0`, while `centred_ne_zero_at_identity` shows it is not the
  zero function. So the argument is not proving something true of every observable: drop
  nonnegativity and the conclusion is false.
* `expect_plaqObs_su_one_eq_zero` — for the trivial gauge group `SU(1)` the plaquette energy is
  identically zero and the expectation is exactly `0` at every coupling and every geometry. So the
  argument is not a formality of the Gibbs construction either: it consumes an actual group element
  with trace below `N`.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.GibbsPositive`.
-/

namespace MassGap.GibbsPositive

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal
open MeasureTheory

/-! ### Continuity of the Wilson observables

`WilsonReal` proves measurability; the step from "the integral vanishes" to "the integrand vanishes at
every configuration" needs the stronger CONTINUITY. These mirror the measurability proofs. -/

/-- The ordered product of link-dependent step factors is continuous (list induction). -/
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

/-- The Wilson plaquette holonomy is continuous in the configuration. -/
theorem continuous_hol {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {L P : Type} (bd : P → List (L × Bool)) (p : P) :
    Continuous (wilsonHol (G := G) bd p) :=
  continuous_stepProd (bd p)

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- The plaquette-energy observable is continuous. -/
theorem continuous_plaqObs (bd : Pq → List (Lk × Bool)) (p : Pq) :
    Continuous (wilsonPlaqObs (N := N) bd p) :=
  continuous_wilsonDensity.comp (continuous_hol bd p)

/-- The Wilson action is continuous. -/
theorem continuous_action (bd : Pq → List (Lk × Bool)) :
    Continuous (wilsonSystem bd (wilsonDensity (N := N))).action := by
  show Continuous fun U => ∑ p : Pq, wilsonDensity (wilsonHol bd p U)
  exact continuous_finsetSum _ (fun p _ => continuous_wilsonDensity.comp (continuous_hol bd p))

/-- The Boltzmann weight is continuous. -/
theorem continuous_boltz (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Continuous ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) := by
  show Continuous fun U => Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action U)
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_action bd))

/-! ### The Gibbs expectation of the plaquette energy is strictly positive -/

/-- **The correlation numerator `∫ φ_p e^{−βS}` is strictly positive** as soon as the plaquette energy
is nonzero at ONE configuration.

The hypothesis is the weakest available: no smallness, no sign condition on `β`, no bound. The three
inputs are pointwise positivity of the Gibbs weight, continuity of the integrand, and positivity of
the product Haar measure on nonempty opens. -/
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

/-- **The Gibbs expectation of the plaquette energy is strictly positive** — `corrNum > 0` over
`partition > 0`. This is the non-degeneracy the reflected Schwinger form needs. -/
theorem expect_plaqObs_pos (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U₀ : (wilsonSystem bd (wilsonDensity (N := N))).Config)
    (hU₀ : 0 < wilsonPlaqObs (N := N) bd p U₀) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).expect
        (probHaar (MassGap.SUN.SU N)) β (wilsonPlaqObs (N := N) bd p) := by
  unfold System.expect
  exact div_pos (corrNum_plaqObs_pos hN bd p β U₀ hU₀) (wilsonSystem_partition_pos hN bd β)

/-! ### One `SU(3)` element and one configuration carrying a nonzero plaquette energy -/

/-- `diag(1, −1, −1)`: real, symmetric, orthogonal, determinant one.

DERIVED: `diag(1, -1, -1)`: determinant `1*(-1)*(-1) = 1` is exactly what puts it in SU(3), so the entries are forced by the group, not chosen. `3` is the rank, `0` the off-diagonal. -/
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

/-- `diag(1, −1, −1)` as an element of `SU(3)`.

DERIVED: `3` is SU(3)'s rank; `1` is the coercion of `matD` with its membership proof. -/
noncomputable def gD : MassGap.SUN.SU 3 := ⟨matD, matD_mem⟩

@[simp] theorem gD_coe : (gD : Matrix (Fin 3) (Fin 3) ℂ) = matD := rfl

/-- Its Wilson density is `4/3`: the real trace is `−1`, not `3`. This single inequality is the whole
gauge-group input to the positivity. -/
theorem wilsonDensity_gD : wilsonDensity (N := 3) gD = 4 / 3 := by
  unfold wilsonDensity
  rw [gD_coe]
  norm_num [matD, Matrix.trace_fin_three_of, Complex.add_re, Complex.neg_re, Complex.one_re]

/-- **The configuration.** `gD` on every `direction 0` link whose site sits on the `ν = 0` slice of
axis `1`, the identity everywhere else. Of the plaquette `((0,1), origin)`'s four boundary links only
`(0, origin)` meets that description — the other `direction 0` link is at `origin + 1̂`, whose axis-`1`
coordinate is `1` — so the boundary word reads `gD · 1 · 1⁻¹ · 1⁻¹`.

DERIVED: `4` is the Clay problem's dimension, `0` the direction and slice the configuration acts on, `1` the identity carried on every other link. The direction-only form is what makes the holonomy non-trivial at every extent. -/
noncomputable def confD : MassGap.WilsonHypercubic.Link 4 WilsonGauge.nYM → WilsonGauge.G3 :=
  fun l => if l.1 = 0 then (if l.2 1 = 0 then gD else 1) else 1

/-- The plaquette holonomy at `confD` is `gD`. -/
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

/-- The plaquette energy of `confD` is `4/3`, so in particular it is not zero. -/
theorem plaqObs_confD :
    wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD = 4 / 3 := by
  show wilsonDensity (N := 3)
    (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD) = 4 / 3
  rw [hol_confD]
  exact wilsonDensity_gD

/-! ### The reflected Schwinger form of the gauge families is strictly positive -/

/-- **`0 < ⟨O0⟩` on the four-dimensional periodic `SU(3)` Wilson lattice**, at every coupling. -/
theorem expect_O0_pos (β : ℝ) :
    0 < WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0 := by
  have hobs : 0 < wilsonPlaqObs (N := 3)
      (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
      (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) confD := by
    rw [plaqObs_confD]; norm_num
  exact expect_plaqObs_pos (N := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := WilsonGauge.nYM))
    (((0, 1), fun _ => 0) : MassGap.WilsonHypercubic.Plaq 4 WilsonGauge.nYM) β confD hobs

/-- **The reflected Schwinger form is strictly positive**, at every test configuration and every
spacing index. The lower clamp `max · 0` never fires, and the upper clamp `min · 1` cannot reach `0`
because both of its arguments are positive. -/
theorem QG_pos (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    0 < WilsonGauge.QG j a := by
  rw [WilsonGauge.QG_eq]
  have h := expect_O0_pos (a : ℝ)
  rw [max_eq_left h.le]
  exact lt_min h one_pos

/-- `QG` is nowhere zero, so it is not the identically-zero form. -/
theorem QG_ne_zero (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    WilsonGauge.QG j a ≠ 0 := (QG_pos j a).ne'

/-- **Non-degeneracy of every counted gauge family.** `ymFamilyGaugeCounted` carries `QG` as its
reflected form whatever spectrum it is given, so the positivity is independent of the spectral data.
`WilsonModel.ymFamilyTension` is one instantiation of this. -/
theorem ymFamilyGaugeCounted_Q_pos
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((MassGap.Measure.resolvedDim (Finset.range (WilsonGauge.NaG a))
      (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ MassGap.Measure.resolvedDim (Finset.range (WilsonGauge.NaG a)) (ev a) edge)
    (j : (WilsonGauge.ymFamilyGaugeCounted ev edge c hsorted hcount hres).J) (a : ℕ) :
    0 < (WilsonGauge.ymFamilyGaugeCounted ev edge c hsorted hcount hres).Q j a :=
  QG_pos j a

/-- **Non-degeneracy of `ymFamilyGauge`.** Its reflected form is nowhere zero, so the family is not
the vacuous one that satisfies every Osterwalder–Schrader field by being identically zero. -/
theorem ymFamilyGauge_Q_pos (j : WilsonGauge.ymFamilyGauge.J) (a : ℕ) :
    0 < WilsonGauge.ymFamilyGauge.Q j a := QG_pos j a

theorem ymFamilyGauge_Q_ne_zero (j : WilsonGauge.ymFamilyGauge.J) (a : ℕ) :
    WilsonGauge.ymFamilyGauge.Q j a ≠ 0 := (QG_pos j a).ne'

/-- **Non-degeneracy of `WilsonInstance.ymFamily`, reduced to one positivity.** That family's
reflected form is NOT `QG`: `(ymFamily N).Q` is `QYM N` — the clamp of `wilsonCorrAt N a` at the lag
`j.2.2 % (N+1)` — and no theorem here makes the two forms equal. Its non-degeneracy therefore reduces
to the positivity of that correlation at one lag, and no further. At `j.2.2 = 0` the lag is `0` and
the hypothesis is `0 < WilsonBridge.corrClay (N+1) a 0`, the plaquette-energy variance.

Stated about `QYM` rather than about `(ymFamily N).Q`, which it equals by definition: the family
OBJECT is built with `wilson_reflection_positive_at` in its `os_rp` field, so any statement that
names `ymFamily` carries that axiom whatever its proof does. -/
theorem QYM_pos_of (N a : ℕ) (j : MassGap.JYM)
    (hd : 0 < MassGap.wilsonCorrAt N (a : ℝ)
            ⟨j.2.2 % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩) :
    0 < MassGap.QYM N j a :=
  lt_min hd one_pos

/-! ### NEGATIVE CONTROL 1: an observable on the SAME system whose expectation IS zero

The positivity above consumes the NONNEGATIVITY of the plaquette energy. Drop it and the conclusion
fails on the same system, at the same coupling, against the same measure: the centred plaquette
energy integrates to exactly zero while being nonzero at an explicit configuration. -/

/-- Shifting an observable by a constant shifts its Gibbs expectation by that constant. -/
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

/-- **The negative control.** The centred plaquette energy has expectation EXACTLY zero — same
system, same measure, same coupling, same machinery. So `expect_O0_pos` is not a statement that holds
of any observable; it holds of this one because the plaquette energy is nonnegative. -/
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

/-- The centred observable is NOT the zero function: at the all-identity configuration the plaquette
holonomy is the identity, the plaquette energy is `0`, and the centred value is `−⟨O0⟩ < 0`. -/
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

theorem centred_ne_zero_at_identity (β : ℝ) :
    WilsonGauge.O0 (fun _ => 1)
      - WilsonGauge.sysYM.expect (probHaar WilsonGauge.G3) β WilsonGauge.O0 ≠ 0 := by
  rw [O0_confOne, zero_sub, neg_ne_zero]
  exact (expect_O0_pos β).ne'

/-! ### NEGATIVE CONTROL 2: the trivial gauge group

The positivity also consumes the existence of a group element whose real trace is below `N`. For
`SU(1)` the determinant condition pins the single entry to `1`, every holonomy is the identity, the
plaquette energy is identically zero, and the expectation is exactly zero — at every coupling and on
every geometry. So `expect_plaqObs_pos`'s hypothesis is not decoration. -/

/-- In `SU(1)` the determinant condition fixes the only entry, so the Wilson density vanishes. -/
theorem wilsonDensity_su_one (g : MassGap.SUN.SU 1) : wilsonDensity g = 0 := by
  have hdet : (g : Matrix (Fin 1) (Fin 1) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rw [Matrix.det_fin_one] at hdet
  have htr : Matrix.trace (g : Matrix (Fin 1) (Fin 1) ℂ) = (1 : ℂ) := by
    rw [Matrix.trace_fin_one]; exact hdet
  unfold wilsonDensity
  rw [htr]
  norm_num

/-- **The second negative control.** For the trivial gauge group the plaquette expectation is exactly
zero, so `0 <` above is not a formality of the Gibbs construction. -/
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
