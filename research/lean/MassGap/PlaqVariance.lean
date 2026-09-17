import Mathlib
import MassGap.WilsonBridge

/-!
# MassGap.PlaqVariance — the plaquette energy is not almost surely constant

`ReflectPositive.corrClay_rp_of` reduces `Complete.wilson_reflection_positive_at` to two inputs. One
is the Osterwalder–Seiler pairing inequality. The other is

    0 < corrClay (N + 1) β 0

and it is NOT reflection positivity: the identically zero correlation satisfies every pairing
inequality and fails this. This file supplies it.

## What the quantity is

Unfolding the constructed definitions — `corrClay n β lag = corrHyper (d := 4) 3 n 0 1 2 β lag`,
`corrHyper … = wilsonCorrConn bd ((μ,ν), 0) β ((μ,ν), siteAtHyper τ lag)`, and
`wilsonCorrConn` subtracting `⟨φ_{p₀}⟩·⟨φ_p⟩` — at `lag = 0` the two plaquettes COINCIDE
(`siteAtHyper_zero`), so the quantity is the VARIANCE of one plaquette-energy observable:

    corrClay (N+1) β 0 = ⟨φ_q²⟩_β − ⟨φ_q⟩_β²,   q = plane (0,1) at the origin.

Positivity of a variance says exactly that `φ_q` is not almost surely constant under the `SU(3)`
Wilson Gibbs measure. That is a statement about the gauge group, not about a reflection.

## How it is proved

`wilsonCorrConn_self_pos` is the general mechanism, at any `SU(N)`, any boundary-word geometry, any
coupling. Three facts drive it:

* The Gibbs weight `e^{−βS}` is strictly positive everywhere (`wilsonSystem_boltz_pos`), so the
  variance is `(∫ (φ − m)² e^{−βS}) / Z` with `Z > 0`.
* Product Haar over the links is positive on nonempty opens: `probHaar` is a Haar measure, hence
  `IsOpenPosMeasure`, and `Measure.pi.isOpenPosMeasure` carries that to configurations.
* `(φ − m)² e^{−βS}` is CONTINUOUS (`continuous_wilsonPlaqObs`, `continuous_wilsonSystem_boltz`).
  A continuous function that integrates to zero against an open-positive measure is identically
  zero (`Continuous.ae_eq_iff_eq`), which would force `φ` to take one single value at EVERY
  configuration.

So the only remaining obligation is to exhibit two configurations on which `φ_q` differs, and
`obs_confOne` / `obs_confAB` do that with the plaquette holonomy `1` and the holonomy
`gA·gB·gA⁻¹·gB⁻¹ = diag(−1,−1,1)`. The two `SU(3)` elements are real involutions, so no inverse has
to be computed, and the commutator is nontrivial because `SU(3)` is non-abelian — which is where the
gauge group enters and the only place it does.

## Where it is NOT true, and why that matters

`wilsonCorrConn_self_eq_zero_of_trivial` proves the SAME connected correlation is EXACTLY ZERO for
`SU(1)`, the trivial group: there every holonomy is the identity, `φ ≡ 0`, and the variance vanishes.
So `0 <` here is not a formality that any Wilson system satisfies — it fails for a degenerate gauge
group, and the proof above genuinely consumes the existence of two non-commuting group elements.

## Range of validity

`corrClay_zero_pos` holds for EVERY `β : ℝ` — positive, zero and negative — and for every periodic
extent `N + 1 ≥ 1`. Nothing in the argument is perturbative and nothing needs `β` small or large. At
`β = 0` the measure is bare product Haar and the argument is unchanged, since the weight is then the
constant `1`, which is still strictly positive.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.PlaqVariance`.
-/

namespace MassGap.PlaqVariance

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic MassGap.WilsonBridge
open MeasureTheory

/-! ### Continuity of the Wilson observables

`WilsonReal` proves measurability of the holonomy, the action and the Boltzmann weight; the argument
below needs the stronger CONTINUITY, because the step that converts "integrates to zero" into
"vanishes at every configuration" is `Continuous.ae_eq_iff_eq`. The proofs mirror the measurability
ones line for line. -/

/-- The ordered product of link-dependent step factors is continuous (list induction) — the
continuity counterpart of `WilsonLattice.measurable_stepListProd`. -/
theorem continuous_stepListProd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
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
theorem continuous_wilsonHol {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {L P : Type} (bd : P → List (L × Bool)) (p : P) :
    Continuous (wilsonHol (G := G) bd p) := by
  exact continuous_stepListProd (bd p)

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- The plaquette-energy observable is continuous. -/
theorem continuous_wilsonPlaqObs (bd : Pq → List (Lk × Bool)) (p : Pq) :
    Continuous (wilsonPlaqObs (N := N) bd p) := by
  exact continuous_wilsonDensity.comp (continuous_wilsonHol bd p)

/-- The Wilson action is continuous. -/
theorem continuous_wilsonSystem_action (bd : Pq → List (Lk × Bool)) :
    Continuous (wilsonSystem bd (wilsonDensity (N := N))).action := by
  show Continuous fun U => ∑ p : Pq, wilsonDensity (wilsonHol bd p U)
  exact continuous_finsetSum _ (fun p _ => continuous_wilsonDensity.comp (continuous_wilsonHol bd p))

/-- The Boltzmann weight is continuous. -/
theorem continuous_wilsonSystem_boltz (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Continuous ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) := by
  show Continuous fun U => Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action U)
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonSystem_action bd))

/-! ### The variance is strictly positive as soon as the observable moves at all -/

/-- **The connected correlation of a plaquette with ITSELF is its variance, and it is strictly
positive unless the plaquette energy is constant on the whole configuration space.**

The hypothesis is the weakest possible: TWO configurations at which the observable differs. It is
also necessary — `wilsonCorrConn_self_eq_zero_of_trivial` shows the conclusion is false without it.

No smallness, no sign condition and no bound on `β`: the Gibbs weight is positive and continuous for
every real coupling, which is all the argument uses. -/
theorem wilsonCorrConn_self_pos (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U V : (wilsonSystem bd (wilsonDensity (N := N))).Config)
    (hUV : wilsonPlaqObs (N := N) bd p U ≠ wilsonPlaqObs (N := N) bd p V) :
    0 < wilsonCorrConn (Nc := N) bd p β p := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  haveI : ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure :=
    inferInstanceAs ((Measure.pi
      (fun _ : Lk => probHaar (MassGap.SUN.SU N))).IsOpenPosMeasure)
  -- abbreviations, spelled out so nothing depends on `set` unfolding the right way
  have hZ : 0 < (wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β := wilsonSystem_partition_pos hN bd β
  have hwpos : ∀ W, 0 < (wilsonSystem bd (wilsonDensity (N := N))).boltz β W :=
    fun W => wilsonSystem_boltz_pos bd β W
  have hb0 : ∀ W, 0 ≤ wilsonPlaqObs (N := N) bd p W := fun W => wilsonPlaqObs_nonneg hN bd p W
  have hb2 : ∀ W, wilsonPlaqObs (N := N) bd p W ≤ 2 := fun W => wilsonPlaqObs_le_two hN bd p W
  set m : ℝ := (wilsonSystem bd (wilsonDensity (N := N))).expect
    (probHaar (MassGap.SUN.SU N)) β (wilsonPlaqObs (N := N) bd p) with hm
  -- the three integrals
  have iφ : Integrable (fun W => wilsonPlaqObs (N := N) bd p W
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bd β (wilsonPlaqObs (N := N) bd p)
      (measurable_wilsonPlaqObs bd p) 2
      (fun W => abs_le.mpr ⟨by linarith [hb0 W], hb2 W⟩)
  have iw : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    have h := wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using h
  have iφ2 : Integrable (fun W => (wilsonPlaqObs (N := N) bd p W * wilsonPlaqObs (N := N) bd p W)
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    wilsonSystem_mul_boltz_integrable hN bd β
      (fun W => wilsonPlaqObs (N := N) bd p W * wilsonPlaqObs (N := N) bd p W)
      ((measurable_wilsonPlaqObs bd p).mul (measurable_wilsonPlaqObs bd p)) 4
      (fun W => by
        rw [abs_of_nonneg (mul_nonneg (hb0 W) (hb0 W))]
        nlinarith [hb0 W, hb2 W])
  have i2 : Integrable (fun W => (-(2 * m)) * (wilsonPlaqObs (N := N) bd p W
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W))
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    iφ.const_mul _
  have i3 : Integrable (fun W => m ^ 2 * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    iw.const_mul _
  -- the pointwise expansion of the centred square
  have hsplit : ∀ W, (wilsonPlaqObs (N := N) bd p W - m) ^ 2
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
      = (wilsonPlaqObs (N := N) bd p W * wilsonPlaqObs (N := N) bd p W)
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
        + ((-(2 * m)) * (wilsonPlaqObs (N := N) bd p W
            * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
          + m ^ 2 * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W) := fun W => by ring
  have i23 : Integrable (fun W => (-(2 * m)) * (wilsonPlaqObs (N := N) bd p W
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      + m ^ 2 * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    i2.add i3
  have iI : Integrable (fun W => (wilsonPlaqObs (N := N) bd p W - m) ^ 2
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (iφ2.add i23).congr (Filter.Eventually.of_forall (fun W => (hsplit W).symm))
  -- ⟨φ⟩·Z is the unnormalised first moment
  have hmZ : m * (wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) β
      = (wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (wilsonPlaqObs (N := N) bd p) := by
    rw [hm]; unfold System.expect; exact div_mul_cancel₀ _ hZ.ne'
  -- the centred second moment, written in terms of the two unnormalised moments
  have hkey : (∫ W, (wilsonPlaqObs (N := N) bd p W - m) ^ 2
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = (wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun W => wilsonPlaqObs (N := N) bd p W * wilsonPlaqObs (N := N) bd p W)
        - m ^ 2 * (wilsonSystem bd (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add iφ2 i23, integral_add i2 i3,
      integral_const_mul, integral_const_mul]
    unfold System.corrNum System.partition
    rw [show (∫ W, wilsonPlaqObs (N := N) bd p W
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        = (wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
            (wilsonPlaqObs (N := N) bd p) from rfl,
      show (∫ W, (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        = (wilsonSystem bd (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β from rfl,
      ← hmZ]
    ring
  -- the centred second moment is strictly positive
  have hInn : 0 ≤ ∫ W, (wilsonPlaqObs (N := N) bd p W - m) ^ 2
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
      ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    integral_nonneg (fun W => mul_nonneg (sq_nonneg _) (hwpos W).le)
  have hIpos : 0 < ∫ W, (wilsonPlaqObs (N := N) bd p W - m) ^ 2
      * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
      ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    refine lt_of_le_of_ne hInn (fun h0 => ?_)
    have hnn : (0 : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
        ≤ fun W => (wilsonPlaqObs (N := N) bd p W - m) ^ 2
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W :=
      fun W => mul_nonneg (sq_nonneg _) (hwpos W).le
    have hae := (integral_eq_zero_iff_of_nonneg hnn iI).mp h0.symm
    have hcont : Continuous (fun W => (wilsonPlaqObs (N := N) bd p W - m) ^ 2
        * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W) :=
      (((continuous_wilsonPlaqObs bd p).sub continuous_const).pow 2).mul
        (continuous_wilsonSystem_boltz bd β)
    have hzero := (Continuous.ae_eq_iff_eq
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))
      hcont continuous_const).mp hae
    have hconst : ∀ W, wilsonPlaqObs (N := N) bd p W = m := by
      intro W
      have hW : (wilsonPlaqObs (N := N) bd p W - m) ^ 2
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W = 0 := congrFun hzero W
      have := (mul_eq_zero.mp hW).resolve_right (hwpos W).ne'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    exact hUV ((hconst U).trans (hconst V).symm)
  -- and the variance is that, divided by Z
  have hexp : wilsonCorrConn (Nc := N) bd p β p
      = (∫ W, (wilsonPlaqObs (N := N) bd p W - m) ^ 2
          * (wilsonSystem bd (wilsonDensity (N := N))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
        / (wilsonSystem bd (wilsonDensity (N := N))).partition
            (probHaar (MassGap.SUN.SU N)) β := by
    rw [hkey]
    have hZne : (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β ≠ 0 := hZ.ne'
    show ((wilsonSystem bd (wilsonDensity (N := N))).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun W => wilsonPlaqObs (N := N) bd p W * wilsonPlaqObs (N := N) bd p W))
        / (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β
        - m * m = _
    field_simp
  rw [hexp]
  exact div_pos hIpos hZ

#print axioms wilsonCorrConn_self_pos

/-! ### NEGATIVE CONTROL: the same correlation VANISHES for a trivial gauge group

The theorem above is not a formality of the Gibbs construction — it is false for a gauge group with
one element. `SU(1)` is the `1×1` special unitary group: the determinant condition pins the single
entry to `1`, so the group is trivial, every holonomy is the identity, the plaquette energy is
identically `0`, and the connected self-correlation is EXACTLY `0`, not merely small.

This is what makes the hypothesis of `wilsonCorrConn_self_pos` load-bearing, and it is why the
Clay instance below has to produce two `SU(3)` elements that do not commute. -/

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

/-- **The negative control.** For the trivial gauge group the connected self-correlation is exactly
zero at every coupling and on every geometry: the plaquette energy is constant, so its variance
vanishes. `0 <` in `wilsonCorrConn_self_pos` therefore genuinely uses the structure of `SU(3)`. -/
theorem wilsonCorrConn_self_eq_zero_of_trivial (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ) :
    wilsonCorrConn (Nc := 1) bd p β p = 0 := by
  have hobs : ∀ W : (wilsonSystem bd (wilsonDensity (N := 1))).Config,
      wilsonPlaqObs (N := 1) bd p W = 0 := fun W => wilsonDensity_su_one _
  unfold wilsonCorrConn wilsonCorr System.expect System.corrNum
  simp only [hobs, zero_mul, mul_zero, integral_zero, zero_div, sub_zero]

/-- **Why the two are consistent**, and what that says about the hypothesis. For the trivial group
the hypothesis of `wilsonCorrConn_self_pos` cannot be met at all: every pair of configurations
carries the same plaquette energy. Were it ever met there, the general theorem would deliver
`0 < 0` against `wilsonCorrConn_self_eq_zero_of_trivial`. So the two-values hypothesis is not
decoration — it is the entire gauge-group content of the positivity. -/
theorem su_one_has_no_two_values (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U V : (wilsonSystem bd (wilsonDensity (N := 1))).Config) :
    wilsonPlaqObs (N := 1) bd p U = wilsonPlaqObs (N := 1) bd p V := by
  show wilsonDensity (wilsonHol bd p U) = wilsonDensity (wilsonHol bd p V)
  rw [wilsonDensity_su_one, wilsonDensity_su_one]

#print axioms wilsonCorrConn_self_eq_zero_of_trivial
#print axioms su_one_has_no_two_values

/-! ### Two non-commuting `SU(3)` elements, as real involutions

`gA = diag(1,−1,−1)` and `gB` the sign-corrected transposition of the first two axes. Both square to
the identity, so the boundary word's two INVERSE entries need no inverse computed, and

    gA·gB·gA⁻¹·gB⁻¹ = (gA·gB)² = diag(−1,−1,1),

whose real trace is `−1`, not `3`. That single inequality is the whole of the gauge-group input. -/

/-- `diag(1, −1, −1)`: real, symmetric, orthogonal, determinant one.

DERIVED: `diag(1, -1, -1)`: determinant 1 puts it in SU(3), so the entries are the group's. `3` is the rank. -/
def matA : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- The transposition of the first two axes with the third reflected, so the determinant is one.

DERIVED: a real involution in SU(3): the off-diagonal `1`s swap two basis vectors and the `-1` restores determinant 1. Forced by the group, and chosen to NOT commute with `matA` -- the commutator is the whole content of the non-constancy proof. -/
def matB : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem matA_star : star matA = matA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA]

theorem matB_star : star matB = matB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB]

theorem matA_mul_self : matA * matA = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matB_mul_self : matB * matB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB, Matrix.mul_apply, Fin.sum_univ_succ]

theorem matA_mem : matA ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, matA_star]; exact matA_mul_self
  · simp [matA, Matrix.det_fin_three]

theorem matB_mem : matB ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, matB_star]; exact matB_mul_self
  · simp [matB, Matrix.det_fin_three]

/-- `diag(1,−1,−1)` as an element of `SU(3)`.

DERIVED: `3` is SU(3)'s rank; `1` is the membership coercion. -/
noncomputable def gA : MassGap.SUN.SU 3 := ⟨matA, matA_mem⟩

/-- The sign-corrected axis transposition as an element of `SU(3)`.

DERIVED: `3` is SU(3)'s rank. -/
noncomputable def gB : MassGap.SUN.SU 3 := ⟨matB, matB_mem⟩

@[simp] theorem gA_coe : (gA : Matrix (Fin 3) (Fin 3) ℂ) = matA := rfl
@[simp] theorem gB_coe : (gB : Matrix (Fin 3) (Fin 3) ℂ) = matB := rfl

theorem gA_mul_self : gA * gA = 1 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_one, gA_coe]
  exact matA_mul_self

theorem gB_mul_self : gB * gB = 1 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_one, gB_coe]
  exact matB_mul_self

@[simp] theorem gA_inv : gA⁻¹ = gA := inv_eq_of_mul_eq_one_right gA_mul_self

@[simp] theorem gB_inv : gB⁻¹ = gB := inv_eq_of_mul_eq_one_right gB_mul_self

/-- **The commutator is nontrivial**: `(gA·gB)² = diag(−1,−1,1)`. -/
theorem comm_coe : ((gA * (gB * (gA * gB)) : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ)
    = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, gA_coe, gB_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, matB, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Wilson density of the commutator is `4/3`, not `0`. -/
theorem wilsonDensity_comm : wilsonDensity (gA * (gB * (gA * gB))) = 4 / 3 := by
  unfold wilsonDensity
  rw [comm_coe]
  norm_num [Matrix.trace_fin_three_of, Complex.add_re, Complex.neg_re, Complex.one_re]

/-! ### The Clay instance: `0 < corrClay (N+1) β 0` -/

/-- At lag zero the displaced site IS the origin, so `corrHyper` pairs a plaquette with itself. -/
theorem siteAtHyper_zero {d n : ℕ} [NeZero n] (τ : Fin d) :
    siteAtHyper (d := d) (n := n) τ 0 = (fun _ => 0) := by
  funext i
  simp [siteAtHyper, Function.update_apply]

/-- The plaquette `corrClay` is about: the `(0,1)` plane at the origin of the periodic 4-D lattice.

DERIVED: `4` is the Clay problem's dimension and `(0, 1)` the first two axes, which span the plaquette's plane. `0` is the base site. The lattice fixes all three. -/
def clayPlaq (n : ℕ) [NeZero n] : MassGap.WilsonHypercubic.Plaq 4 n := ((0, 1), fun _ => 0)

/-- **`corrClay` at lag zero is a VARIANCE**, not a reflection pairing: the two plaquettes coincide. -/
theorem corrClay_zero_eq (N : ℕ) (β : ℝ) :
    corrClay (N + 1) β 0
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
          (clayPlaq (N + 1)) β (clayPlaq (N + 1)) := by
  unfold corrClay corrHyper clayPlaq
  rw [siteAtHyper_zero]

/-- The all-identity configuration.

DERIVED: `4` is the dimension, `3` the rank, `1` the group identity carried on every link. -/
noncomputable def confOne (n : ℕ) : MassGap.WilsonHypercubic.Link 4 n → MassGap.SUN.SU 3 :=
  fun _ => 1

/-- The configuration carrying `gA` on every direction-`0` link and `gB` on every other link.

It depends only on the DIRECTION, never on the site, which is what makes the holonomy come out as a
commutator at every periodic extent `n` — including `n = 1`, where the four links of the plaquette
are not distinct.

DERIVED: `4` is the Clay problem's dimension, `3` SU(3)'s rank, `0` the direction whose links carry
`gA`, and `1` the membership coercions. The split by DIRECTION rather than site is the content, as
the paragraph above says; no numeral here is tunable. -/
noncomputable def confAB (n : ℕ) : MassGap.WilsonHypercubic.Link 4 n → MassGap.SUN.SU 3 :=
  fun l => if l.1 = 0 then gA else gB

theorem obs_confOne (n : ℕ) [NeZero n] :
    wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
      (clayPlaq n) (confOne n) = 0 := by
  show wilsonDensity (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
    (clayPlaq n) (confOne n)) = 0
  have h : wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
      (clayPlaq n) (confOne n) = 1 := by
    simp [wilsonHol, MassGap.WilsonHypercubic.bd, clayPlaq, confOne]
  rw [h]
  exact wilsonDensity_one (by norm_num)

theorem obs_confAB (n : ℕ) [NeZero n] :
    wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
      (clayPlaq n) (confAB n) = 4 / 3 := by
  show wilsonDensity (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
    (clayPlaq n) (confAB n)) = 4 / 3
  have h : wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := n))
      (clayPlaq n) (confAB n) = gA * (gB * (gA * gB)) := by
    simp [wilsonHol, MassGap.WilsonHypercubic.bd, clayPlaq, confAB]
  rw [h]
  exact wilsonDensity_comm

/-- **THE THEOREM.** The strict-positivity input of `ReflectPositive.corrClay_rp_of`, discharged:
the connected Wilson correlation at lag zero is strictly positive at EVERY real coupling and every
periodic extent.

What it says physically is that the plaquette-energy observable of four-dimensional `SU(3)` lattice
gauge theory is not almost surely constant. What it is NOT is reflection positivity: the identically
zero correlation satisfies every pairing inequality and fails this. -/
theorem corrClay_zero_pos (N : ℕ) (β : ℝ) : 0 < corrClay (N + 1) β 0 := by
  rw [corrClay_zero_eq]
  refine wilsonCorrConn_self_pos (by norm_num) _ (clayPlaq (N + 1)) β
    (confOne (N + 1)) (confAB (N + 1)) ?_
  rw [obs_confOne, obs_confAB]
  norm_num

#print axioms corrClay_zero_pos

/-- **The `β = 0` corner, machine-checked rather than asserted.** At zero coupling the Gibbs weight
is the constant `1` and the measure is bare product Haar; the plaquette energy still fluctuates, so
the variance is still strictly positive. This is a literal instance of `corrClay_zero_pos`, recorded
because "all `β`" is the kind of claim that deserves its endpoints written down. -/
theorem corrClay_zero_pos_at_zero_coupling (N : ℕ) : 0 < corrClay (N + 1) 0 0 :=
  corrClay_zero_pos N 0

/-- **The smallest lattice corner.** At `n = 1` the four links of the plaquette are NOT distinct —
`shift μ x = x` — so a configuration that updated a single link would give the identity holonomy.
`confAB` depends only on the DIRECTION, which is why the holonomy is the commutator at every extent
including this one. -/
theorem corrClay_zero_pos_smallest_lattice (β : ℝ) : 0 < corrClay 1 β 0 :=
  corrClay_zero_pos 0 β

/-- The same statement in the shape `ReflectPositive.corrClay_rp_of` consumes it. -/
theorem wilson_reflection_positive_input (N : ℕ) (β : ℝ) :
    0 < WilsonBridge.corrClay (N + 1) β 0 := corrClay_zero_pos N β

#print axioms corrClay_zero_pos_at_zero_coupling
#print axioms corrClay_zero_pos_smallest_lattice
#print axioms wilson_reflection_positive_input
#print axioms wilsonDensity_comm
#print axioms obs_confAB
#print axioms corrClay_zero_eq

end MassGap.PlaqVariance
