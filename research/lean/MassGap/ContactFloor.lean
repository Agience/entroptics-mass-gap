import Mathlib
import MassGap.StrongArm
import MassGap.PlaqVariance

/-!
# MassGap.ContactFloor — an aperture-uniform floor on the contact term

`StrongArm.contact_relative_on_strong_arm` takes one hypothesis, `StrongArm.ContactFloor b`: a
single positive number below `wilsonCorrAt N β 0` at every aperture `N` and every coupling in
`[0, b]`. `contactFloor_holds` proves that statement at every real `b`, and
`contact_relative_unconditional` restates the strong-arm conclusion with the hypothesis discharged.

## The quantity

`wilsonCorrAt N β 0 = corrClay (N+1) β 0` is the connected correlation at zero lag, which is the
variance of the plaquette-energy observable `φ_p` under the `SU(3)` Wilson Gibbs measure on the
periodic four-dimensional lattice. The target is therefore `Var_β(φ_p) ≥ δ > 0`, uniform in the
extent.

## The general step

`wilsonCorrConn_self_ge_haar` states

    Var_β(φ_p) ≥ e^{−2β·|touchNbrs bd p|} · Var_0(φ_p)

at every geometry, every `SU(Nc)` with `Nc ≠ 0` and every `β ≥ 0`. The exponent counts the
plaquettes that touch `p`. The proof splits the action along that set — `S = S_touch + S_rest` —
which is legitimate because a plaquette that does not touch `p` reads none of `p`'s links
(`ReflectionPositivity.action_on_congr_of_support`). Then

* `e^{−βS_touch} ∈ [e^{−2β|touch|}, 1]` because each plaquette density lies in `[0, 2]`, so the
  numerator loses at most `e^{−2β|touch|}` and the partition function is at most `∫ e^{−βS_rest}`;
* `(φ_p − c)²` and `e^{−βS_rest}` read disjoint link blocks, so they factor under product Haar
  (`WilsonReal.block_integral_factor`) and the common factor `∫ e^{−βS_rest}` cancels;
* `∫ (φ_p − c)² dHaar ≥ ∫ (φ_p − ⟨φ_p⟩_Haar)² dHaar` for every `c` (`haar_centred_le`), which lets
  the Gibbs mean — a function of both the coupling and the aperture — be discarded.

`StrongCoupling.touchDeg_bd_le` bounds `|touchNbrs|` by `16·dim`, a quantity with no extent in it,
and that is what makes the factor aperture-free. `WilsonReal.wilsonSystem_partition_pos` and
`WilsonRead.expect_ge_haar_of_nonneg` carry exponents proportional to the plaquette count instead.

## The Haar variance

The step reduces an `(N, β)`-uniform floor to an `N`-uniform floor on the pure Haar variance
`corrClay n 0 0`, which has no coupling in it. That is closed by a pushforward:

* at extent `n ≥ 2` the four links of the plaquette are distinct, so translating the last link on
  the left carries the holonomy to `hol · g` (`hol_linkTranslate_clay`); averaging over `g` and
  swapping the order of integration (Fubini on two probability measures) shows the holonomy pushes
  product Haar forward to Haar on `SU(3)` — `integral_hol_clay`. So `corrClay n 0 0` is the same
  number at every `n ≥ 2`, namely `∫ φ² dHaar − (∫ φ dHaar)²`;
* at extent `n = 1` the four links are not distinct (`shift μ x = x`), the holonomy is a commutator
  and the pushforward has no starting point. `n = 1` is one lattice, so its Haar variance is one
  number, and `PlaqVariance.corrClay_zero_pos` gives its positivity.

`exists_haar_floor` is the `min` of the two, and neither carries an extent.

## Scope of the constants

* `16·dim` is `StrongCoupling.touchDeg_bd_le`, read off `bd`'s own boundary word. At `dim = 4` that
  is `64`, so the exponent is `2·β·64` and the factor on `[0, b]` is at least `e^{−128b}`. The `2`
  is `WilsonAction.wilsonDensity_le_two`, itself `|Re tr U| ≤ N`.
* `haarSecond − haarMean²` and `corrClay 1 0 0` are Haar integrals. Their positivity is
  non-constructive (`PlaqVariance.corrClay_zero_pos` runs `Continuous.ae_eq_iff_eq` against an
  `IsOpenPosMeasure` and yields no rate), so no numerical value for either appears anywhere in this
  file. Each is a single universal number with no aperture and no coupling in it.
* The floor shrinks as `b` grows, by the factor `e^{−128b}`. `contactFloor_holds` and
  `contact_relative_unconditional` are statements about a bounded coupling interval `[0, b]`; they
  quantify over no coupling above `b`.

Foundational footprint only (`#print axioms` after every declaration).
Build: `python code/lean_build.py build MassGap.ContactFloor`.
-/

namespace MassGap.ContactFloor

open MeasureTheory
open MassGap MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice
open MassGap.WilsonAction MassGap.WilsonReal MassGap.WilsonBridge

/-! ### Toolchain probes — the names this file depends on, elaborated here so a missing or
renamed declaration fails at this point rather than inside a proof -/

section Probes

#check @MeasureTheory.integral_integral_swap
#check @MeasureTheory.integral_mul_left_eq_self
#check @Finset.sum_add_sum_compl
#check @MassGap.WilsonReal.block_integral_factor
#check @MeasureTheory.Measure.pi_map_pi
#check @measurePreserving_mul_left
#check @MeasureTheory.Integrable.mono'
#check @continuous_finsetSum
#check @MassGap.WilsonReal.wilsonSystem_expect_at_zero
#check @MassGap.PlaqVariance.corrClay_zero_eq
#check @MassGap.PlaqVariance.clayPlaq
#check @MassGap.StrongCoupling.touchNbrs_card_le_touchDeg
#check @MassGap.StrongCoupling.touchDeg_bd_le
#check @MassGap.StrongCoupling.mem_touchNbrs
#check @MassGap.ReflectionPositivity.hol_congr_on_support
#check @MassGap.ReflectionPositivity.action_on_congr_of_support
#check @MassGap.PlaqVariance.continuous_wilsonHol
#check @Fin.val_one

example (m : ℕ) : (1 : Fin (m + 2)) ≠ 0 := by simp

example (m : ℕ) : (((0 : Fin (m + 2)) + 1) : Fin (m + 2)).val = 1 := by simp

/-- The boundary word of the Clay plaquette, spelled out and checked by `simp`. -/
example (m : ℕ) (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
        (MassGap.PlaqVariance.clayPlaq (m + 2)) U
      = U ((0 : Fin 4), (fun _ => 0))
        * (U ((1 : Fin 4), MassGap.WilsonHypercubic.shift (0 : Fin 4) (fun _ => 0))
          * ((U ((0 : Fin 4), MassGap.WilsonHypercubic.shift (1 : Fin 4) (fun _ => 0)))⁻¹
            * (U ((1 : Fin 4), (fun _ => 0)))⁻¹)) := by
  simp [wilsonHol, MassGap.WilsonHypercubic.bd, MassGap.PlaqVariance.clayPlaq]

end Probes

/-! ### A bounded measurable function is integrable against a probability measure -/

/-- A measurable real function bounded in absolute value by `M` is integrable against a
probability measure. The Wilson observables used below are all bounded by explicit constants. -/
theorem integrable_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hm : Measurable f) (M : ℝ) (hb : ∀ x, |f x| ≤ M) :
    Integrable f μ :=
  (integrable_const M).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hb x))

#print axioms integrable_of_bounded

/-- The total real mass of a probability measure.

DERIVED: `1` is the mass `measure_univ` assigns to the whole space under `IsProbabilityMeasure`; it
is the definition of the class, not a normalisation chosen here. -/
theorem measureReal_univ_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : μ.real Set.univ = 1 := by
  change (μ Set.univ).toReal = 1
  rw [measure_univ, ENNReal.toReal_one]

#print axioms measureReal_univ_one

/-- The integral of a constant against a probability measure is that constant. -/
theorem integral_const_prob {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) : (∫ _x, c ∂μ) = c := by
  rw [integral_const, measureReal_univ_one, one_smul]

#print axioms integral_const_prob

/-- `|a - b| ≤ |a| + |b|` on `ℝ`, the form in which the centred-square bounds below use the
triangle inequality. -/
theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    rcases abs_cases (a - b) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [ha, hb, hc] <;> linarith

#print axioms abs_sub_le_add

section General

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk] [DecidableEq Pq]

/-! ### The connected self-correlation in centred form

`PlaqVariance.wilsonCorrConn_self_pos` uses this identity inside its own proof without exporting it.
It is stated as a theorem here because every bound below is applied to it. -/

/-- The connected self-correlation equals the centred second moment,
`ρ_p(β) = (∫ (φ_p − ⟨φ_p⟩_β)² e^{−βS}) / Z`, at every coupling `β` and every geometry `bd`.

DERIVED: `0` is in `hN : Nc ≠ 0`, the rank being nonzero, which is what
`WilsonReal.wilsonSystem_partition_pos` needs to give `Z > 0` before the division is legitimate.
`2` is the exponent of the centred second moment the identity is about. -/
theorem wilsonCorrConn_self_eq_centred (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq)
    (β : ℝ) :
    wilsonCorrConn (Nc := Nc) bd p β p
      = (∫ W, (wilsonPlaqObs (N := Nc) bd p W
            - (wilsonSystem bd (wilsonDensity (N := Nc))).expect
                (probHaar (MassGap.SUN.SU Nc)) β (wilsonPlaqObs (N := Nc) bd p)) ^ 2
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        / (wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := Nc))).vol
      (probHaar (MassGap.SUN.SU Nc))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
  have hZ : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  have hb0 : ∀ W, 0 ≤ wilsonPlaqObs (N := Nc) bd p W := fun W => wilsonPlaqObs_nonneg hN bd p W
  have hb2 : ∀ W, wilsonPlaqObs (N := Nc) bd p W ≤ 2 := fun W => wilsonPlaqObs_le_two hN bd p W
  set m : ℝ := (wilsonSystem bd (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) β (wilsonPlaqObs (N := Nc) bd p) with hm
  have iφ : Integrable (fun W => wilsonPlaqObs (N := Nc) bd p W
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_mul_boltz_integrable hN bd β (wilsonPlaqObs (N := Nc) bd p)
      (measurable_wilsonPlaqObs bd p) 2
      (fun W => abs_le.mpr ⟨by linarith [hb0 W], hb2 W⟩)
  have iw : Integrable ((wilsonSystem bd (wilsonDensity (N := Nc))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) := by
    have h := wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using h
  have iφ2 : Integrable (fun W => (wilsonPlaqObs (N := Nc) bd p W * wilsonPlaqObs (N := Nc) bd p W)
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_mul_boltz_integrable hN bd β
      (fun W => wilsonPlaqObs (N := Nc) bd p W * wilsonPlaqObs (N := Nc) bd p W)
      ((measurable_wilsonPlaqObs bd p).mul (measurable_wilsonPlaqObs bd p)) 4
      (fun W => by
        rw [abs_of_nonneg (mul_nonneg (hb0 W) (hb0 W))]
        nlinarith [hb0 W, hb2 W])
  have i2 : Integrable (fun W => (-(2 * m)) * (wilsonPlaqObs (N := Nc) bd p W
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W))
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    iφ.const_mul _
  have i3 : Integrable (fun W => m ^ 2 * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    iw.const_mul _
  have hsplit : ∀ W, (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
      = (wilsonPlaqObs (N := Nc) bd p W * wilsonPlaqObs (N := Nc) bd p W)
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
        + ((-(2 * m)) * (wilsonPlaqObs (N := Nc) bd p W
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
          + m ^ 2 * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W) := fun W => by ring
  have i23 : Integrable (fun W => (-(2 * m)) * (wilsonPlaqObs (N := Nc) bd p W
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
      + m ^ 2 * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W)
      ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    i2.add i3
  have hmZ : m * (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β
      = (wilsonSystem bd (wilsonDensity (N := Nc))).corrNum (probHaar (MassGap.SUN.SU Nc)) β
          (wilsonPlaqObs (N := Nc) bd p) := by
    rw [hm]; unfold System.expect; exact div_mul_cancel₀ _ hZ.ne'
  have hkey : (∫ W, (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
      = (wilsonSystem bd (wilsonDensity (N := Nc))).corrNum (probHaar (MassGap.SUN.SU Nc)) β
          (fun W => wilsonPlaqObs (N := Nc) bd p W * wilsonPlaqObs (N := Nc) bd p W)
        - m ^ 2 * (wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add iφ2 i23, integral_add i2 i3,
      integral_const_mul, integral_const_mul]
    unfold System.corrNum System.partition
    rw [show (∫ W, wilsonPlaqObs (N := Nc) bd p W
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        = (wilsonSystem bd (wilsonDensity (N := Nc))).corrNum (probHaar (MassGap.SUN.SU Nc)) β
            (wilsonPlaqObs (N := Nc) bd p) from rfl,
      show (∫ W, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        = (wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β from rfl,
      ← hmZ]
    ring
  rw [hkey]
  have hZne : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β ≠ 0 := hZ.ne'
  show ((wilsonSystem bd (wilsonDensity (N := Nc))).corrNum (probHaar (MassGap.SUN.SU Nc)) β
        (fun W => wilsonPlaqObs (N := Nc) bd p W * wilsonPlaqObs (N := Nc) bd p W))
      / (wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β
      - m * m = _
  field_simp

#print axioms wilsonCorrConn_self_eq_centred

/-! ### The Haar variance, and that it is the smallest centred second moment -/

/-- At coupling `0` the connected self-correlation is the bare Haar variance of `φ_p`: the
Boltzmann weight is constant and the partition function is `1`.

DERIVED: `0` is both the coupling the identity is stated at and the `Nc ≠ 0` of `hN`; `2` is the
exponent of the centred square. -/
theorem wilsonCorrConn_self_at_zero (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) :
    wilsonCorrConn (Nc := Nc) bd p 0 p
      = ∫ W, (wilsonPlaqObs (N := Nc) bd p W
            - ∫ V, wilsonPlaqObs (N := Nc) bd p V
                ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol
                  (probHaar (MassGap.SUN.SU Nc)))) ^ 2
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := Nc))).vol
      (probHaar (MassGap.SUN.SU Nc))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
  have hb : ∀ W, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz 0 W = 1 :=
    fun W => by unfold System.boltz; simp
  have hden : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) 0 = 1 := by
    unfold System.partition
    simp [hb]
  have hexp : (wilsonSystem bd (wilsonDensity (N := Nc))).expect
      (probHaar (MassGap.SUN.SU Nc)) 0 (wilsonPlaqObs (N := Nc) bd p)
      = ∫ V, wilsonPlaqObs (N := Nc) bd p V
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) :=
    wilsonSystem_expect_at_zero bd _
  rw [wilsonCorrConn_self_eq_centred hN bd p 0, hden, hexp, div_one]
  simp [hb]

#print axioms wilsonCorrConn_self_at_zero

/-- The Haar variance is the smallest centred second moment: for every real `c`, the zero-coupling
connected self-correlation is at most `∫ (φ_p − c)² dHaar`. The conclusion is an inequality; the
proof establishes the exact gap `(mean − c)²` and then discards it. This is how the Gibbs mean
`⟨φ⟩_β` — a function of both the coupling and the aperture — is replaced by a bound depending on
neither.

DERIVED: `0` is the coupling on the left-hand side and the `Nc ≠ 0` of `hN`; `2` is the exponent of
the centred square. `c` is universally quantified and carries no numeral. -/
theorem haar_centred_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq) (c : ℝ) :
    wilsonCorrConn (Nc := Nc) bd p 0 p
      ≤ ∫ W, (wilsonPlaqObs (N := Nc) bd p W - c) ^ 2
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))) := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := Nc))).vol
      (probHaar (MassGap.SUN.SU Nc))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
  have hb0 : ∀ W, 0 ≤ wilsonPlaqObs (N := Nc) bd p W := fun W => wilsonPlaqObs_nonneg hN bd p W
  have hb2 : ∀ W, wilsonPlaqObs (N := Nc) bd p W ≤ 2 := fun W => wilsonPlaqObs_le_two hN bd p W
  set μ := (wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)) with hμ
  set m₀ : ℝ := ∫ V, wilsonPlaqObs (N := Nc) bd p V ∂μ with hm₀
  have iφ : Integrable (wilsonPlaqObs (N := Nc) bd p) μ :=
    integrable_of_bounded (measurable_wilsonPlaqObs bd p) 2
      (fun W => abs_le.mpr ⟨by linarith [hb0 W], hb2 W⟩)
  have icen : Integrable (fun W => (wilsonPlaqObs (N := Nc) bd p W - m₀) ^ 2) μ := by
    refine integrable_of_bounded
      (((measurable_wilsonPlaqObs bd p).sub measurable_const).pow measurable_const)
      ((2 + |m₀|) ^ 2) (fun W => ?_)
    have hx : |wilsonPlaqObs (N := Nc) bd p W| ≤ 2 := abs_le.mpr ⟨by linarith [hb0 W], hb2 W⟩
    have h1 : |wilsonPlaqObs (N := Nc) bd p W - m₀| ≤ 2 + |m₀| := by
      have := abs_sub_le_add (wilsonPlaqObs (N := Nc) bd p W) m₀
      linarith
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (wilsonPlaqObs (N := Nc) bd p W - m₀) ^ 2
        = |wilsonPlaqObs (N := Nc) bd p W - m₀| ^ 2 := (sq_abs _).symm
      _ ≤ (2 + |m₀|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hpt : ∀ W, (wilsonPlaqObs (N := Nc) bd p W - c) ^ 2
      = (wilsonPlaqObs (N := Nc) bd p W - m₀) ^ 2
        + ((2 * (m₀ - c)) * wilsonPlaqObs (N := Nc) bd p W + (c ^ 2 - m₀ ^ 2)) := by
    intro W; ring
  have iL : Integrable (fun W => (2 * (m₀ - c)) * wilsonPlaqObs (N := Nc) bd p W) μ :=
    iφ.const_mul _
  have iK : Integrable
      (fun _ : (wilsonSystem bd (wilsonDensity (N := Nc))).Config => c ^ 2 - m₀ ^ 2) μ :=
    integrable_const _
  have iLK : Integrable (fun W => (2 * (m₀ - c)) * wilsonPlaqObs (N := Nc) bd p W
      + (c ^ 2 - m₀ ^ 2)) μ := iL.add iK
  have step1 : (∫ W, (wilsonPlaqObs (N := Nc) bd p W - c) ^ 2 ∂μ)
      = (∫ W, (wilsonPlaqObs (N := Nc) bd p W - m₀) ^ 2 ∂μ)
        + ∫ W, ((2 * (m₀ - c)) * wilsonPlaqObs (N := Nc) bd p W + (c ^ 2 - m₀ ^ 2)) ∂μ := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_add icen iLK
  have step2 : (∫ W, ((2 * (m₀ - c)) * wilsonPlaqObs (N := Nc) bd p W + (c ^ 2 - m₀ ^ 2)) ∂μ)
      = (m₀ - c) ^ 2 := by
    rw [integral_add iL iK, integral_const_mul, integral_const_prob, ← hm₀]
    ring
  have hval : (∫ W, (wilsonPlaqObs (N := Nc) bd p W - c) ^ 2 ∂μ)
      = (∫ W, (wilsonPlaqObs (N := Nc) bd p W - m₀) ^ 2 ∂μ) + (m₀ - c) ^ 2 := by
    rw [step1, step2]
  rw [wilsonCorrConn_self_at_zero hN bd p, ← hμ, ← hm₀, hval]
  linarith [sq_nonneg (m₀ - c)]

#print axioms haar_centred_le

/-- At coupling `0` the connected self-correlation is the difference of the Haar moments,
`∫ φ_p² − (∫ φ_p)²`. Stated separately from `wilsonCorrConn_self_at_zero` because this is the form
the `SU(3)` pushforward feeds, and unlike its siblings it carries no `Nc ≠ 0` hypothesis.

DERIVED: `0` is the coupling the identity is stated at; `2` is the exponent on the mean. -/
theorem wilsonCorrConn_self_at_zero_moments (bd : Pq → List (Lk × Bool)) (p : Pq) :
    wilsonCorrConn (Nc := Nc) bd p 0 p
      = (∫ U, wilsonPlaqObs (N := Nc) bd p U * wilsonPlaqObs (N := Nc) bd p U
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        - (∫ U, wilsonPlaqObs (N := Nc) bd p U
            ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol
              (probHaar (MassGap.SUN.SU Nc)))) ^ 2 := by
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  rw [wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero]
  ring

#print axioms wilsonCorrConn_self_at_zero_moments

/-! ### Splitting the action at a plaquette

`StrongCoupling.touchNbrs bd p` is the set of plaquettes sharing a link with `p`. Its complement
reads none of `p`'s links, so the complement's contribution to the action is a function of the other
links alone. -/

/-- The Boltzmann weight of the plaquettes outside `StrongCoupling.touchNbrs bd p`: `exp` of
`-β` times the action density summed over that complement. -/
noncomputable def restWeight (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) : ℝ :=
  Real.exp (-β * ∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
    wilsonDensity (N := Nc) (wilsonHol bd q U))

/-- The Boltzmann weight of the plaquettes that touch `p`: `exp` of `-β` times the action density
summed over `StrongCoupling.touchNbrs bd p`.

DERIVED: the declaration carries no numeral. The `2` per plaquette quoted below is
`WilsonAction.wilsonDensity_le_two`'s cap on a single plaquette's action density, which is the
group's own: `φ_W g = 1 − Re tr g / N` with `|Re tr g| ≤ N`, so `φ_W` lands in `[0, 2]` at every
rank. The number of plaquettes summed is `(StrongCoupling.touchNbrs bd p).card`, bounded by
`touchDeg bd`, a property of the incidence map with no extent in it. -/
noncomputable def touchWeight (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) : ℝ :=
  Real.exp (-β * ∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
    wilsonDensity (N := Nc) (wilsonHol bd q U))

#print axioms restWeight
#print axioms touchWeight

/-- The Boltzmann weight factorises at `p`'s touch-neighbourhood: `boltz β U` is
`touchWeight bd p β U * restWeight bd p β U`, by splitting the action sum over
`StrongCoupling.touchNbrs bd p` and its complement. -/
theorem boltz_eq_touch_mul_rest (bd : Pq → List (Lk × Bool)) (p : Pq) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) :
    (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
      = touchWeight (Nc := Nc) bd p β U * restWeight (Nc := Nc) bd p β U := by
  classical
  have hact : (wilsonSystem bd (wilsonDensity (N := Nc))).action U
      = (∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
          wilsonDensity (N := Nc) (wilsonHol bd q U))
        + ∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
            wilsonDensity (N := Nc) (wilsonHol bd q U) := by
    show (∑ q, wilsonDensity (N := Nc) (wilsonHol bd q U)) = _
    rw [Finset.sum_add_sum_compl]
  unfold System.boltz touchWeight restWeight
  rw [hact, ← Real.exp_add]
  congr 1
  ring

#print axioms boltz_eq_touch_mul_rest

/-- A plaquette outside `StrongCoupling.touchNbrs bd p` names no link of
`StrongCoupling.linkSupp bd p`. This is the combinatorial content that makes the split of
`boltz_eq_touch_mul_rest` a split into disjoint link blocks. -/
theorem rest_support (bd : Pq → List (Lk × Bool)) (p : Pq) :
    ∀ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ, ∀ l ∈ (bd q).map Prod.fst,
      l ∈ (MassGap.StrongCoupling.linkSupp bd p)ᶜ := by
  classical
  intro q hq l hl
  rw [Finset.mem_compl] at hq ⊢
  intro hlS
  refine hq (MassGap.StrongCoupling.mem_touchNbrs.mpr ⟨l, hlS, ?_⟩)
  simpa [MassGap.StrongCoupling.linkSupp] using hl

#print axioms rest_support

/-- Extend a tuple indexed by a block `S : Finset Lk` to a total configuration on `Lk`, filling
the links outside `S` with the group identity.

DERIVED: the declaration carries no numeral. The `1` in the body is the group identity of
`SUN.SU Nc`, not a numeric value: `WilsonReal.block_integral_factor` needs a total function on
links, so the links outside `S` must carry something. `blockExt_restrict` together with
`ReflectionPositivity.hol_congr_on_support` shows the composite `wilsonHol bd p ∘ blockExt S`
depends on the links of `S` alone, so any other fixed element gives the same theorems. -/
noncomputable def blockExt (S : Finset Lk) (v : S → MassGap.SUN.SU Nc) :
    Lk → MassGap.SUN.SU Nc :=
  fun l => if h : l ∈ S then v ⟨l, h⟩ else 1

theorem continuous_blockExt (S : Finset Lk) : Continuous (blockExt (Nc := Nc) S) := by
  refine continuous_pi (fun l => ?_)
  by_cases h : l ∈ S
  · simp only [blockExt, dif_pos h]
    exact continuous_apply _
  · simp only [blockExt, dif_neg h]
    exact continuous_const

#print axioms blockExt
#print axioms continuous_blockExt

theorem blockExt_restrict (S : Finset Lk) (U : Lk → MassGap.SUN.SU Nc) {l : Lk} (hl : l ∈ S) :
    blockExt (Nc := Nc) S (fun i : ↥S => U i.val) l = U l := by
  simp [blockExt, dif_pos hl]

#print axioms blockExt_restrict

/-! ### The factorisation

`(φ_p − c)²` reads only `StrongCoupling.linkSupp bd p` and `restWeight` only its complement. The
blocks are disjoint, so `WilsonReal.block_integral_factor` applies and the `restWeight` integral
comes out as a common factor that cancels against the partition function in
`wilsonCorrConn_self_ge_haar`. -/

/-- The centred square and the rest-weight factor under product Haar: the integral of
`(φ_p − c)² * restWeight bd p β` is the product of the two integrals. `(φ_p − c)²` reads only
`StrongCoupling.linkSupp bd p` and `restWeight` only its complement, so
`WilsonReal.block_integral_factor` applies.

DERIVED: `2` is the exponent of the centred square. `c` and `β` are universally quantified. -/
theorem block_factor (bd : Pq → List (Lk × Bool)) (p : Pq) (β c : ℝ) :
    (∫ U, (wilsonPlaqObs (N := Nc) bd p U - c) ^ 2 * restWeight (Nc := Nc) bd p β U
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (wilsonPlaqObs (N := Nc) bd p U - c) ^ 2
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, restWeight (Nc := Nc) bd p β U
          ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  set S : Finset Lk := MassGap.StrongCoupling.linkSupp bd p with hS
  set T : Finset Lk := Sᶜ with hT
  set Φ : (↥S → MassGap.SUN.SU Nc) → ℝ := fun v =>
    (wilsonDensity (N := Nc) (wilsonHol bd p (blockExt (Nc := Nc) S v)) - c) ^ 2 with hΦ
  set Ψ : (↥T → MassGap.SUN.SU Nc) → ℝ := fun w =>
    Real.exp (-β * ∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
      wilsonDensity (N := Nc) (wilsonHol bd q (blockExt (Nc := Nc) T w))) with hΨ
  have hΦm : Measurable Φ := by
    rw [hΦ]
    refine Continuous.measurable ?_
    exact ((continuous_wilsonDensity.comp
      ((MassGap.PlaqVariance.continuous_wilsonHol bd p).comp
        (continuous_blockExt (Nc := Nc) S))).sub continuous_const).pow 2
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    refine Continuous.measurable ?_
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    exact continuous_finsetSum _ (fun q _ =>
      continuous_wilsonDensity.comp
        ((MassGap.PlaqVariance.continuous_wilsonHol bd q).comp
          (continuous_blockExt (Nc := Nc) T)))
  have hΦeq : ∀ U : Lk → MassGap.SUN.SU Nc,
      Φ (fun i : ↥S => U i.val) = (wilsonPlaqObs (N := Nc) bd p U - c) ^ 2 := by
    intro U
    have hhol : wilsonHol bd p (blockExt (Nc := Nc) S (fun i : ↥S => U i.val))
        = wilsonHol bd p U := by
      refine MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => ?_)
      refine blockExt_restrict (Nc := Nc) S U ?_
      rw [hS]
      simpa [MassGap.StrongCoupling.linkSupp] using hl
    rw [hΦ]
    simp only [hhol]
    try rfl
  have hΨeq : ∀ U : Lk → MassGap.SUN.SU Nc,
      Ψ (fun i : ↥T => U i.val) = restWeight (Nc := Nc) bd p β U := by
    intro U
    have hsum : (∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
          wilsonDensity (N := Nc) (wilsonHol bd q
            (blockExt (Nc := Nc) T (fun i : ↥T => U i.val))))
        = ∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
            wilsonDensity (N := Nc) (wilsonHol bd q U) := by
      refine MassGap.ReflectionPositivity.action_on_congr_of_support bd
        (wilsonDensity (N := Nc)) ((MassGap.StrongCoupling.touchNbrs bd p)ᶜ) T
        (by rw [hT, hS]; exact rest_support bd p) _ U (fun l hl => ?_)
      exact blockExt_restrict (Nc := Nc) T U hl
    rw [hΨ]
    simp only [hsum]
    try rfl
  have hptw : ∀ U : Lk → MassGap.SUN.SU Nc,
      (wilsonPlaqObs (N := Nc) bd p U - c) ^ 2 * restWeight (Nc := Nc) bd p β U
        = Φ (fun i : ↥S => U i.val) * Ψ (fun i : ↥T => U i.val) := by
    intro U
    rw [hΦeq U, hΨeq U]
  have hdisj : Disjoint S T := by rw [hT]; exact disjoint_compl_right
  have hfac := MassGap.WilsonReal.block_integral_factor (N := Nc) S T hdisj Φ Ψ hΦm hΨm
  have hvol : ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))
      = Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) := rfl
  rw [hvol]
  calc (∫ U, (wilsonPlaqObs (N := Nc) bd p U - c) ^ 2 * restWeight (Nc := Nc) bd p β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∫ U, Φ (fun i : ↥S => (U : Lk → MassGap.SUN.SU Nc) i.val)
          * Ψ (fun i : ↥T => (U : Lk → MassGap.SUN.SU Nc) i.val)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) :=
        integral_congr_ae (Filter.Eventually.of_forall hptw)
    _ = (∫ U, Φ (fun i : ↥S => (U : Lk → MassGap.SUN.SU Nc) i.val)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, Ψ (fun i : ↥T => (U : Lk → MassGap.SUN.SU Nc) i.val)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := hfac
    _ = _ := by
        congr 1
        · exact integral_congr_ae (Filter.Eventually.of_forall hΦeq)
        · exact integral_congr_ae (Filter.Eventually.of_forall hΨeq)

#print axioms block_factor

/-! ### The estimate -/

/-- The Gibbs connected self-correlation at coupling `β` is at least
`exp (-(2 * β * (touchNbrs bd p).card))` times the one at coupling `0`, at every geometry, every
`SU(Nc)` with `Nc ≠ 0` and every `β ≥ 0`. The exponent counts the plaquettes sharing a link with
`p`, not the plaquettes of the lattice; `StrongCoupling.touchDeg_bd_le` bounds that card by `16·dim`
with no extent in it, whereas `WilsonReal.wilsonSystem_partition_pos` and
`WilsonRead.expect_ge_haar_of_nonneg` carry exponents proportional to the plaquette count.

DERIVED: `0` is the `Nc ≠ 0` of `hN`, the `0 ≤ β` of `hβ`, and the coupling on the left-hand side.
`2` is the factor in the exponent, one per unit of `WilsonAction.wilsonDensity_le_two`'s cap `[0, 2]`
on a plaquette density. -/
theorem wilsonCorrConn_self_ge_haar (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq)
    {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs bd p).card : ℝ)))
        * wilsonCorrConn (Nc := Nc) bd p 0 p
      ≤ wilsonCorrConn (Nc := Nc) bd p β p := by
  classical
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := Nc))).vol
      (probHaar (MassGap.SUN.SU Nc))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
  set μ := (wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)) with hμ
  set K : ℝ := ((MassGap.StrongCoupling.touchNbrs bd p).card : ℝ) with hK
  set E : ℝ := Real.exp (-(2 * β * K)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hb0 : ∀ W, 0 ≤ wilsonPlaqObs (N := Nc) bd p W := fun W => wilsonPlaqObs_nonneg hN bd p W
  have hb2 : ∀ W, wilsonPlaqObs (N := Nc) bd p W ≤ 2 := fun W => wilsonPlaqObs_le_two hN bd p W
  set m : ℝ := (wilsonSystem bd (wilsonDensity (N := Nc))).expect
    (probHaar (MassGap.SUN.SU Nc)) β (wilsonPlaqObs (N := Nc) bd p) with hm
  set Z : ℝ := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hZ : 0 < Z := wilsonSystem_partition_pos hN bd β
  -- the two pieces of the weight
  have htw0 : ∀ U, 0 ≤ ∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
      wilsonDensity (N := Nc) (wilsonHol bd q U) :=
    fun U => Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
  have htwK : ∀ U, (∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
      wilsonDensity (N := Nc) (wilsonHol bd q U)) ≤ K * 2 := by
    intro U
    calc (∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
          wilsonDensity (N := Nc) (wilsonHol bd q U))
        ≤ ∑ _q ∈ MassGap.StrongCoupling.touchNbrs bd p, (2 : ℝ) :=
          Finset.sum_le_sum (fun q _ => wilsonDensity_le_two hN _)
      _ = K * 2 := by rw [Finset.sum_const, nsmul_eq_mul, hK]
  have hTlow : ∀ U, E ≤ touchWeight (Nc := Nc) bd p β U := by
    intro U
    rw [hE]
    unfold touchWeight
    rw [Real.exp_le_exp]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr (htwK U))]
  have hTup : ∀ U, touchWeight (Nc := Nc) bd p β U ≤ 1 := by
    intro U
    unfold touchWeight
    have h := Real.exp_le_exp.mpr
      (show -β * (∑ q ∈ MassGap.StrongCoupling.touchNbrs bd p,
        wilsonDensity (N := Nc) (wilsonHol bd q U)) ≤ 0 by
        nlinarith [mul_nonneg hβ (htw0 U)])
    simpa using h
  have hR0 : ∀ U, 0 < restWeight (Nc := Nc) bd p β U := fun U => Real.exp_pos _
  have hRup : ∀ U, restWeight (Nc := Nc) bd p β U ≤ 1 := by
    intro U
    unfold restWeight
    have hs : (0 : ℝ) ≤ ∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
        wilsonDensity (N := Nc) (wilsonHol bd q U) :=
      Finset.sum_nonneg (fun q _ => wilsonDensity_nonneg hN _)
    have h := Real.exp_le_exp.mpr
      (show -β * (∑ q ∈ (MassGap.StrongCoupling.touchNbrs bd p)ᶜ,
        wilsonDensity (N := Nc) (wilsonHol bd q U)) ≤ 0 by
        nlinarith [mul_nonneg hβ hs])
    simpa using h
  have hRmeas : Measurable (fun W : (wilsonSystem bd (wilsonDensity (N := Nc))).Config =>
      restWeight (Nc := Nc) bd p β W) := by
    refine Continuous.measurable ?_
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    exact continuous_finsetSum _ (fun q _ =>
      continuous_wilsonDensity.comp (MassGap.PlaqVariance.continuous_wilsonHol bd q))
  have hCmeas : Measurable (fun W => (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2) :=
    ((measurable_wilsonPlaqObs bd p).sub measurable_const).pow measurable_const
  have hCbd : ∀ W, |(wilsonPlaqObs (N := Nc) bd p W - m) ^ 2| ≤ (2 + |m|) ^ 2 := by
    intro W
    have hx : |wilsonPlaqObs (N := Nc) bd p W| ≤ 2 := abs_le.mpr ⟨by linarith [hb0 W], hb2 W⟩
    have h1 : |wilsonPlaqObs (N := Nc) bd p W - m| ≤ 2 + |m| := by
      have := abs_sub_le_add (wilsonPlaqObs (N := Nc) bd p W) m
      linarith
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
        = |wilsonPlaqObs (N := Nc) bd p W - m| ^ 2 := (sq_abs _).symm
      _ ≤ (2 + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have iNum : Integrable (fun W => (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W) μ :=
    wilsonSystem_mul_boltz_integrable hN bd β _ hCmeas ((2 + |m|) ^ 2) hCbd
  have iCR : Integrable (fun W => (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
      * restWeight (Nc := Nc) bd p β W) μ := by
    refine integrable_of_bounded (hCmeas.mul hRmeas) ((2 + |m|) ^ 2) (fun W => ?_)
    rw [abs_mul, abs_of_nonneg (hR0 W).le]
    nlinarith [hCbd W, hRup W, (hR0 W).le, abs_nonneg ((wilsonPlaqObs (N := Nc) bd p W - m) ^ 2)]
  have iR : Integrable (fun W : (wilsonSystem bd (wilsonDensity (N := Nc))).Config =>
      restWeight (Nc := Nc) bd p β W) μ := by
    refine integrable_of_bounded hRmeas 1 (fun W => ?_)
    rw [abs_of_nonneg (hR0 W).le]; exact hRup W
  have iB : Integrable ((wilsonSystem bd (wilsonDensity (N := Nc))).boltz β) μ := by
    have h := wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using h
  set H : ℝ := ∫ W, (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2 ∂μ with hH
  set J : ℝ := ∫ W, restWeight (Nc := Nc) bd p β W ∂μ with hJ
  have hnum : E * (H * J) ≤ ∫ W, (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
      * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β W ∂μ := by
    have hfac : H * J = ∫ W, (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2
        * restWeight (Nc := Nc) bd p β W ∂μ := by
      rw [hH, hJ, hμ]; exact (block_factor bd p β m).symm
    rw [hfac, ← integral_const_mul]
    refine integral_mono (iCR.const_mul _) iNum (fun W => ?_)
    rw [boltz_eq_touch_mul_rest bd p β W]
    have hA : (0 : ℝ) ≤ (wilsonPlaqObs (N := Nc) bd p W - m) ^ 2 * restWeight (Nc := Nc) bd p β W :=
      mul_nonneg (sq_nonneg _) (hR0 W).le
    nlinarith [mul_le_mul_of_nonneg_left (hTlow W) hA]
  have hZJ : Z ≤ J := by
    rw [hZdef, hJ]
    unfold System.partition
    rw [← hμ]
    refine integral_mono iB iR (fun W => ?_)
    rw [boltz_eq_touch_mul_rest bd p β W]
    nlinarith [mul_le_mul_of_nonneg_right (hTup W) (hR0 W).le]
  have hJ0 : 0 < J := lt_of_lt_of_le hZ hZJ
  have hV0 : wilsonCorrConn (Nc := Nc) bd p 0 p ≤ H := by
    rw [hH, hμ]; exact haar_centred_le hN bd p m
  have hV0nn : 0 ≤ wilsonCorrConn (Nc := Nc) bd p 0 p := by
    rw [wilsonCorrConn_self_at_zero hN bd p]
    exact integral_nonneg (fun W => sq_nonneg _)
  rw [wilsonCorrConn_self_eq_centred hN bd p β, ← hm, ← hZdef, ← hμ, le_div_iff₀ hZ]
  calc E * wilsonCorrConn (Nc := Nc) bd p 0 p * Z
      ≤ E * wilsonCorrConn (Nc := Nc) bd p 0 p * J :=
        mul_le_mul_of_nonneg_left hZJ (mul_nonneg hE0.le hV0nn)
    _ ≤ E * H * J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV0 hE0.le) hJ0.le
    _ = E * (H * J) := by ring
    _ ≤ _ := hnum

#print axioms wilsonCorrConn_self_ge_haar

end General

/-! ### The single-link translation, on an arbitrary link set

`WilsonRead`'s `linkTranslate` is typed on `Fin 8` for the two-plaquette system. The same three
lemmas are restated here at an arbitrary finite link type, which is what the hypercubic argument
below consumes. -/

section Translate

variable {Nc : ℕ} {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- Left-translate a single link by `g`, leaving every other link alone. -/
noncomputable def linkTranslate (g : MassGap.SUN.SU Nc) (i₀ : Lk) (U : Lk → MassGap.SUN.SU Nc) :
    Lk → MassGap.SUN.SU Nc :=
  fun l => if l = i₀ then g * U l else U l

theorem linkTranslate_self (g : MassGap.SUN.SU Nc) (i₀ : Lk) (U : Lk → MassGap.SUN.SU Nc) :
    linkTranslate (Nc := Nc) g i₀ U i₀ = g * U i₀ := by
  simp [linkTranslate]

theorem linkTranslate_of_ne (g : MassGap.SUN.SU Nc) (i₀ : Lk) (U : Lk → MassGap.SUN.SU Nc)
    {l : Lk} (h : l ≠ i₀) : linkTranslate (Nc := Nc) g i₀ U l = U l := by
  simp [linkTranslate, h]

#print axioms linkTranslate
#print axioms linkTranslate_self
#print axioms linkTranslate_of_ne

theorem linkTranslate_coord_mp (g : MassGap.SUN.SU Nc) (i₀ l : Lk) :
    MeasurePreserving (fun u : MassGap.SUN.SU Nc => if l = i₀ then g * u else u)
      (probHaar (MassGap.SUN.SU Nc)) (probHaar (MassGap.SUN.SU Nc)) := by
  by_cases h : l = i₀
  · simp only [h, if_pos rfl]
    exact measurePreserving_mul_left (probHaar (MassGap.SUN.SU Nc)) g
  · simp only [if_neg h]
    exact MeasurePreserving.id (probHaar (MassGap.SUN.SU Nc))

/-- `linkTranslate g i₀` preserves the product Haar measure on `Lk → SU Nc`: left-invariance in
the `i₀` factor and the identity in the others, assembled coordinatewise by `Measure.pi_map_pi`. -/
theorem linkTranslate_measurePreserving (g : MassGap.SUN.SU Nc) (i₀ : Lk) :
    MeasurePreserving (linkTranslate (Nc := Nc) g i₀)
      (Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc))
      (Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) := by
  have hmeas : Measurable (linkTranslate (Nc := Nc) g i₀) := by
    refine measurable_pi_lambda _ (fun l => ?_)
    by_cases h : l = i₀
    · simp only [linkTranslate, h, if_pos rfl]
      exact measurable_const.mul (measurable_pi_apply i₀)
    · simp only [linkTranslate, if_neg h]
      exact measurable_pi_apply l
  refine ⟨hmeas, ?_⟩
  have hform : linkTranslate (Nc := Nc) g i₀
      = (fun (U : Lk → MassGap.SUN.SU Nc) (l : Lk) =>
          (fun u : MassGap.SUN.SU Nc => if l = i₀ then g * u else u) (U l)) := by
    funext U l; simp only [linkTranslate]
  rw [hform, Measure.pi_map_pi (fun l => (linkTranslate_coord_mp (Nc := Nc) g i₀ l).aemeasurable)]
  simp only [(linkTranslate_coord_mp (Nc := Nc) g i₀ _).map_eq]

#print axioms linkTranslate_coord_mp
#print axioms linkTranslate_measurePreserving

/-- The single-link translation packaged as a measurable equivalence, with `linkTranslate g⁻¹ i₀`
as its inverse. `MeasurePreserving.integral_comp'` transports an integral only along an `≃ᵐ`, which
is why this form is needed. -/
noncomputable def linkTranslateEquiv (g : MassGap.SUN.SU Nc) (i₀ : Lk) :
    (Lk → MassGap.SUN.SU Nc) ≃ᵐ (Lk → MassGap.SUN.SU Nc) where
  toFun := linkTranslate (Nc := Nc) g i₀
  invFun := linkTranslate (Nc := Nc) g⁻¹ i₀
  left_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  right_inv := fun U => by
    funext l; by_cases h : l = i₀ <;> simp [linkTranslate, h]
  measurable_toFun := (linkTranslate_measurePreserving (Nc := Nc) g i₀).measurable
  measurable_invFun := (linkTranslate_measurePreserving (Nc := Nc) g⁻¹ i₀).measurable

theorem linkTranslateEquiv_measurePreserving (g : MassGap.SUN.SU Nc) (i₀ : Lk) :
    MeasurePreserving (linkTranslateEquiv (Nc := Nc) g i₀)
      (Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc))
      (Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) :=
  linkTranslate_measurePreserving (Nc := Nc) g i₀

#print axioms linkTranslateEquiv
#print axioms linkTranslateEquiv_measurePreserving

/-- Translating one link leaves every product-Haar integral unchanged: `∫ F (linkTranslate g i₀ U)`
equals `∫ F U`, for an arbitrary `F : (Lk → SU Nc) → ℝ`. -/
theorem integral_comp_linkTranslate (g : MassGap.SUN.SU Nc) (i₀ : Lk)
    (F : (Lk → MassGap.SUN.SU Nc) → ℝ) :
    (∫ U, F (linkTranslate (Nc := Nc) g i₀ U)
        ∂(Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))
      = ∫ U, F U ∂(Measure.pi fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) :=
  (linkTranslateEquiv_measurePreserving (Nc := Nc) g i₀).integral_comp' F

#print axioms integral_comp_linkTranslate

end Translate

/-! ### The Clay plaquette at extent at least two: the holonomy is Haar-distributed -/

section Clay

open MassGap.PlaqVariance

/-- At extent `m + 2` a single periodic step in any direction moves the origin. This is where the
extent enters the pushforward below, and the corresponding statement is false at extent `1`.

DERIVED: `4` is the spacetime dimension, the range of the direction index `μ`. `2` is in the extent
`m + 2`, which is how "at least two" is written so that the successor structure is available; `0`
is the origin site, `fun _ => 0`. -/
theorem shift_ne (m : ℕ) (μ : Fin 4) :
    MassGap.WilsonHypercubic.shift (d := 4) (n := m + 2) μ (fun _ => 0) ≠ (fun _ => 0) := by
  intro h
  have h1 := congrFun h μ
  rw [MassGap.WilsonHypercubic.shift, Function.update_self] at h1
  have h2 : ((0 : Fin (m + 2)) + 1) = 0 := h1
  have h3 := congrArg Fin.val h2
  simp at h3

#print axioms shift_ne

/-- The ordered holonomy of `PlaqVariance.clayPlaq` at extent `m + 2`, with the boundary word
spelled out as `V(0,x) · V(1, x+0̂) · V(0, x+1̂)⁻¹ · V(1,x)⁻¹` at the origin.

DERIVED: `4` is the spacetime dimension, `3` the rank of `SUN.SU 3` carried from
`WilsonBridge.corrClay`, `0` and `1` the two direction indices spanning the plaquette's plane and
the origin site, and `2` the extent `m + 2` at which the statement is made. -/
theorem hol_clay_eq (m : ℕ) (V : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) V
      = V ((0 : Fin 4), (fun _ => 0))
        * (V ((1 : Fin 4), MassGap.WilsonHypercubic.shift (0 : Fin 4) (fun _ => 0))
          * ((V ((0 : Fin 4), MassGap.WilsonHypercubic.shift (1 : Fin 4) (fun _ => 0)))⁻¹
            * (V ((1 : Fin 4), (fun _ => 0)))⁻¹)) := by
  simp [wilsonHol, MassGap.WilsonHypercubic.bd, clayPlaq]

#print axioms hol_clay_eq

/-- Left-translating the link `(1, origin)` by `g⁻¹` right-multiplies the Clay plaquette's
holonomy by `g`. The last entry of the boundary word carries orientation `false`, so
`(g⁻¹·U)⁻¹ = U⁻¹·g`; the other three entries are different links, which is where extent `m + 2`
rather than `1` is used, through `shift_ne`.

DERIVED: `4` is the spacetime dimension, `3` the rank carried from `WilsonBridge.corrClay`, `0` and
`1` the direction indices of the plaquette's plane and the origin site, and `2` the extent. -/
theorem hol_linkTranslate_clay (m : ℕ) (g : MassGap.SUN.SU 3)
    (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :
    wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2))
        (linkTranslate (Nc := 3) g⁻¹ ((1 : Fin 4), (fun _ => 0)) U)
      = wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U * g := by
  classical
  have hd : (0 : Fin 4) ≠ 1 := by decide
  have h1 : (((0 : Fin 4), (fun _ => 0)) : MassGap.WilsonHypercubic.Link 4 (m + 2))
      ≠ ((1 : Fin 4), (fun _ => 0)) := by
    intro h
    have hf : (0 : Fin 4) = 1 := congrArg Prod.fst h
    exact hd hf
  have h2 : (((1 : Fin 4), MassGap.WilsonHypercubic.shift (0 : Fin 4) (fun _ => 0)) :
      MassGap.WilsonHypercubic.Link 4 (m + 2)) ≠ ((1 : Fin 4), (fun _ => 0)) := by
    intro h; exact shift_ne m 0 (congrArg Prod.snd h)
  have h3 : (((0 : Fin 4), MassGap.WilsonHypercubic.shift (1 : Fin 4) (fun _ => 0)) :
      MassGap.WilsonHypercubic.Link 4 (m + 2)) ≠ ((1 : Fin 4), (fun _ => 0)) := by
    intro h
    have hf : (0 : Fin 4) = 1 := congrArg Prod.fst h
    exact hd hf
  rw [hol_clay_eq, hol_clay_eq,
    linkTranslate_of_ne (Nc := 3) _ _ _ h1,
    linkTranslate_of_ne (Nc := 3) _ _ _ h2,
    linkTranslate_of_ne (Nc := 3) _ _ _ h3,
    linkTranslate_self (Nc := 3)]
  group

#print axioms hol_linkTranslate_clay

/-- At extent `m + 2` the Clay plaquette's holonomy pushes product Haar forward to Haar on
`SU(3)`: for `f` measurable and bounded by `M`, the product-Haar integral of `f ∘ hol` equals the
Haar integral of `f`. `hol_linkTranslate_clay` makes the integral independent of a right shift;
averaging over the shift and swapping the order of integration (both measures are probability
measures, the integrand bounded and measurable) turns the inner integral into a left translation of
Haar.

DERIVED: `4` is the spacetime dimension, `3` the rank of `SUN.SU 3`, and `2` the extent `m + 2`. The
bound `M` is a variable; no numerical bound is fixed here. -/
theorem integral_hol_clay (m : ℕ) (f : MassGap.SUN.SU 3 → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ g, |f g| ≤ M) :
    (∫ U, f (wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U)
        ∂(Measure.pi fun _ : MassGap.WilsonHypercubic.Link 4 (m + 2) =>
            probHaar (MassGap.SUN.SU 3)))
      = ∫ g, f g ∂(probHaar (MassGap.SUN.SU 3)) := by
  classical
  set π : Measure (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) :=
    Measure.pi (fun _ => probHaar (MassGap.SUN.SU 3)) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  set hol : (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) → MassGap.SUN.SU 3 :=
    fun U => wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
      with hhol
  have hcont : Continuous hol := MassGap.PlaqVariance.continuous_wilsonHol _ _
  show (∫ U, f (hol U) ∂π) = ∫ g, f g ∂(probHaar (MassGap.SUN.SU 3))
  have hshift : ∀ g : MassGap.SUN.SU 3, (∫ U, f (hol U * g) ∂π) = ∫ U, f (hol U) ∂π := by
    intro g
    have hstep := integral_comp_linkTranslate (Nc := 3) g⁻¹
      (((1 : Fin 4), (fun _ => 0)) : MassGap.WilsonHypercubic.Link 4 (m + 2))
      (fun U => f (hol U))
    calc (∫ U, f (hol U * g) ∂π)
        = ∫ U, f (hol (linkTranslate (Nc := 3) g⁻¹
            (((1 : Fin 4), (fun _ => 0)) : MassGap.WilsonHypercubic.Link 4 (m + 2)) U)) ∂π := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
          exact congrArg f (hol_linkTranslate_clay m g U).symm
      _ = ∫ U, f (hol U) ∂π := hstep
  have hmeas : Measurable (Function.uncurry
      (fun (g : MassGap.SUN.SU 3)
        (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) => f (hol U * g))) := by
    show Measurable fun z : MassGap.SUN.SU 3
      × (MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) => f (hol z.2 * z.1)
    exact hf.comp (Continuous.measurable ((hcont.comp continuous_snd).mul continuous_fst))
  have hintg : Integrable (Function.uncurry
      (fun (g : MassGap.SUN.SU 3)
        (U : MassGap.WilsonHypercubic.Link 4 (m + 2) → MassGap.SUN.SU 3) => f (hol U * g)))
      ((probHaar (MassGap.SUN.SU 3)).prod π) :=
    integrable_of_bounded hmeas M (fun z => hb _)
  have hswap := MeasureTheory.integral_integral_swap hintg
  have hinner : ∀ U, (∫ g, f (hol U * g) ∂(probHaar (MassGap.SUN.SU 3)))
      = ∫ g, f g ∂(probHaar (MassGap.SUN.SU 3)) :=
    fun U => MeasureTheory.integral_mul_left_eq_self f (hol U)
  calc (∫ U, f (hol U) ∂π)
      = ∫ _g : MassGap.SUN.SU 3, (∫ U, f (hol U) ∂π) ∂(probHaar (MassGap.SUN.SU 3)) :=
        (integral_const_prob (probHaar (MassGap.SUN.SU 3)) _).symm
    _ = ∫ g, (∫ U, f (hol U * g) ∂π) ∂(probHaar (MassGap.SUN.SU 3)) := by simp only [hshift]
    _ = ∫ U, (∫ g, f (hol U * g) ∂(probHaar (MassGap.SUN.SU 3))) ∂π := hswap
    _ = ∫ _U, (∫ g, f g ∂(probHaar (MassGap.SUN.SU 3))) ∂π := by simp only [hinner]
    _ = ∫ g, f g ∂(probHaar (MassGap.SUN.SU 3)) := integral_const_prob π _

#print axioms integral_hol_clay

/-! ### The Haar variance of the Clay plaquette is one number -/

/-- The `SU(3)` Haar mean of the Wilson plaquette density `wilsonDensity (N := 3)`.

DERIVED: the declaration carries no numeral in its type, `ℝ`. The `3` in the body is the rank of the
gauge group, carried from `WilsonBridge.corrClay`, whose zero-coupling contact value this file
computes. No numerical value for this integral is stated anywhere in the file:
`corrClay_zero_at_zero_eq` gives the contact value as `haarSecond − haarMean ^ 2`, and the only
further fact used is strict positivity. -/
noncomputable def haarMean : ℝ :=
  ∫ g, wilsonDensity (N := 3) g ∂(probHaar (MassGap.SUN.SU 3))

/-- The `SU(3)` Haar second moment of the Wilson plaquette density.

DERIVED: the declaration carries no numeral in its type, `ℝ`. The `3` in the body is the rank of the
gauge group, `WilsonBridge.corrClay`'s own, exactly as in `haarMean`; the product of the density
with itself is what makes this a second moment, the quantity `haarSecond − haarMean ^ 2` subtracts
the squared mean from. No numerical value for this integral is stated. -/
noncomputable def haarSecond : ℝ :=
  ∫ g, wilsonDensity (N := 3) g * wilsonDensity (N := 3) g ∂(probHaar (MassGap.SUN.SU 3))

#print axioms haarMean
#print axioms haarSecond

/-- At extent `m + 2` and coupling `0`, the lag-zero Clay correlation equals
`haarSecond - haarMean ^ 2`, a single `SU(3)` Haar quantity with no extent in it.

DERIVED: `0` is the coupling and the lag at which `corrClay` is read; `2` is the extent `m + 2`,
which is the range `integral_hol_clay` covers, and the exponent on `haarMean`. -/
theorem corrClay_zero_at_zero_eq (m : ℕ) :
    corrClay (m + 2) 0 0 = haarSecond - haarMean ^ 2 := by
  classical
  have h1 : (∫ U, wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
      (clayPlaq (m + 2)) U
      ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
          (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3)))) = haarMean :=
    integral_hol_clay m (wilsonDensity (N := 3)) measurable_wilsonDensity 2
      (fun g => abs_le.mpr ⟨by linarith [wilsonDensity_nonneg (by norm_num : (3:ℕ) ≠ 0) g],
        wilsonDensity_le_two (by norm_num) g⟩)
  have h2 : (∫ U, wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
      (clayPlaq (m + 2)) U * wilsonPlaqObs (N := 3)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
      ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
          (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3)))) = haarSecond :=
    integral_hol_clay m (fun g => wilsonDensity (N := 3) g * wilsonDensity (N := 3) g)
      (measurable_wilsonDensity.mul measurable_wilsonDensity) 4
      (fun g => by
        have hg0 := wilsonDensity_nonneg (by norm_num : (3:ℕ) ≠ 0) g
        have hg2 := wilsonDensity_le_two (by norm_num : (3:ℕ) ≠ 0) g
        rw [abs_of_nonneg (mul_nonneg hg0 hg0)]
        nlinarith)
  calc corrClay (m + 2) 0 0
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
          (clayPlaq (m + 2)) 0 (clayPlaq (m + 2)) := corrClay_zero_eq (m + 1) 0
    _ = (∫ U, wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
            (clayPlaq (m + 2)) U * wilsonPlaqObs (N := 3)
              (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2)) (clayPlaq (m + 2)) U
            ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
                (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3))))
          - (∫ U, wilsonPlaqObs (N := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
              (clayPlaq (m + 2)) U
              ∂((wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := m + 2))
                  (wilsonDensity (N := 3))).vol (probHaar (MassGap.SUN.SU 3)))) ^ 2 :=
        wilsonCorrConn_self_at_zero_moments _ _
    _ = haarSecond - haarMean ^ 2 := by rw [h1, h2]

#print axioms corrClay_zero_at_zero_eq

/-- The lag-zero, coupling-`0` Clay correlation takes the same value at every extent `m + 2` as it
does at extent `2`.

DERIVED: `0` is the coupling and the lag; `2` is the extent `m + 2` on the left and the base extent
`2` on the right. The statement says nothing about extent `1`; `exists_haar_floor` handles that
case separately. -/
theorem corrClay_zero_at_zero_const (m : ℕ) : corrClay (m + 2) 0 0 = corrClay 2 0 0 := by
  rw [corrClay_zero_at_zero_eq m, corrClay_zero_at_zero_eq 0]

#print axioms corrClay_zero_at_zero_const

/-- There is a positive `δ₀` below `corrClay (N + 1) 0 0` at every `N`. The witness is the `min`
of two numbers — the extent-`1` lattice's Haar variance and the common value at every extent at
least `2` (`corrClay_zero_at_zero_const`) — neither of which carries an extent. Their positivity is
`PlaqVariance.corrClay_zero_pos`, which is non-constructive, so `δ₀` is not given numerically.

DERIVED: `0` is the strict lower bound in `0 < δ₀`, and the coupling and lag at which `corrClay` is
read. `1` is the successor in the aperture-to-extent map `N ↦ N + 1`, `corrClay`'s own indexing. -/
theorem exists_haar_floor :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ N : ℕ, δ₀ ≤ corrClay (N + 1) 0 0 := by
  have hone : 0 < corrClay 1 0 0 := MassGap.PlaqVariance.corrClay_zero_pos 0 0
  have htwo : 0 < corrClay 2 0 0 := MassGap.PlaqVariance.corrClay_zero_pos 1 0
  refine ⟨min (corrClay 1 0 0) (corrClay 2 0 0), lt_min hone htwo, fun N => ?_⟩
  cases N with
  | zero => exact min_le_left _ _
  | succ m =>
      have h : corrClay (m + 1 + 1) 0 0 = corrClay 2 0 0 := corrClay_zero_at_zero_const m
      rw [h]
      exact min_le_right _ _

#print axioms exists_haar_floor

end Clay

/-! ### The floor

`StrongCoupling.touchDeg_bd_le` supplies `16·dim = 64` at `dim = 4`, with no extent in it, so the
exponential factor is at least `e^{−128β}` at every aperture; `exists_haar_floor` supplies the
extent-free Haar value. -/

open MassGap.PlaqVariance

/-- The contact value at coupling `β ≥ 0` is at least `e^{−128β}` times the contact value of the
same aperture at coupling `0`. The factor carries no extent; the right-hand side still does, since
`corrClay (N + 1) 0 0` is indexed by `N`. `exists_haar_floor` removes that remaining `N`.

DERIVED: `128 = 2 · 16 · 4` — `StrongCoupling.touchDeg_bd_le` bounds the touch count by `16 * dim`,
which is `64` at `dim = 4`, and `WilsonAction.wilsonDensity_le_two`'s cap `[0, 2]` contributes the
factor `2` in `wilsonCorrConn_self_ge_haar`'s exponent. `0` is the `0 ≤ β` of `hβ`, the coupling and
the lag on the right-hand side. `1` is the successor in `corrClay (N + 1)`. -/
theorem corrClay_zero_ge (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(128 * β)) * corrClay (N + 1) 0 0 ≤ corrClay (N + 1) β 0 := by
  classical
  have hcard : (MassGap.StrongCoupling.touchNbrs
      (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1))).card ≤ 64 := by
    have h1 := MassGap.StrongCoupling.touchNbrs_card_le_touchDeg
      (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1))
    have h2 := MassGap.StrongCoupling.touchDeg_bd_le (dim := 4) (n := N + 1)
    omega
  have hK : ((MassGap.StrongCoupling.touchNbrs
      (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1))).card : ℝ) ≤ 64 := by
    exact_mod_cast hcard
  have hbase := wilsonCorrConn_self_ge_haar (Nc := 3) (by norm_num)
    (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1)) hβ
  have heq0 : corrClay (N + 1) 0 0
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
          (clayPlaq (N + 1)) 0 (clayPlaq (N + 1)) := corrClay_zero_eq N 0
  have heqβ : corrClay (N + 1) β 0
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
          (clayPlaq (N + 1)) β (clayPlaq (N + 1)) := corrClay_zero_eq N β
  have hV0 : 0 ≤ wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
      (clayPlaq (N + 1)) 0 (clayPlaq (N + 1)) := by
    rw [← heq0]; exact (MassGap.PlaqVariance.corrClay_zero_pos N 0).le
  have hexp : Real.exp (-(128 * β))
      ≤ Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs
          (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1))).card : ℝ))) := by
    rw [Real.exp_le_exp]
    nlinarith [hK, hβ, mul_nonneg hβ (sub_nonneg.mpr hK)]
  rw [heq0, heqβ]
  calc Real.exp (-(128 * β)) * wilsonCorrConn (Nc := 3)
        (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1)) 0 (clayPlaq (N + 1))
      ≤ Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs
            (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1)) (clayPlaq (N + 1))).card : ℝ)))
          * wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
            (clayPlaq (N + 1)) 0 (clayPlaq (N + 1)) :=
        mul_le_mul_of_nonneg_right hexp hV0
    _ ≤ _ := hbase

#print axioms corrClay_zero_ge

/-- `StrongArm.ContactFloor b` holds at every real `b`. No sign condition on `b` is needed, since
a negative `b` makes the inner quantifier over `β ∈ [0, b]` empty. The witness is `e^{−128b}` times
`exists_haar_floor`'s extent-free constant, where `128 = 2 · 16 · 4` comes from
`StrongCoupling.touchDeg_bd_le` at `dim = 4` against `WilsonAction.wilsonDensity_le_two`.

DERIVED: the statement carries no numeral; `b : ℝ` is the only argument and `ContactFloor` is a
named predicate. The constants quoted above sit in the proof and in `corrClay_zero_ge`. -/
theorem contactFloor_holds (b : ℝ) : MassGap.StrongArm.ContactFloor b := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := exists_haar_floor
  refine ⟨Real.exp (-(128 * b)) * δ₀, by positivity, fun N β hβ0 hβb => ?_⟩
  have hstep := corrClay_zero_ge N hβ0
  have hmono : Real.exp (-(128 * b)) ≤ Real.exp (-(128 * β)) := by
    rw [Real.exp_le_exp]; linarith
  have hδ : δ₀ ≤ corrClay (N + 1) 0 0 := hfloor N
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  calc Real.exp (-(128 * b)) * δ₀
      ≤ Real.exp (-(128 * β)) * δ₀ := mul_le_mul_of_nonneg_right hmono hδ₀.le
    _ ≤ Real.exp (-(128 * β)) * corrClay (N + 1) 0 0 :=
        mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
    _ ≤ corrClay (N + 1) β 0 := hstep

#print axioms contactFloor_holds

/-- `StrongArm.contact_relative_on_strong_arm` with its `ContactFloor` hypothesis discharged: there
is a `b > 0` with `StrongCoupling.coreRate (16 * 4) b < 1` and a single `C ≥ 0` such that
`wilsonCorrAt N β d ≤ C * wilsonCorrAt N β 0 / (circLag d) ^ 4` at every aperture `N`, every
coupling `β ∈ [0, b]` and every lag `d` with `circLag d ≥ 1`. The `b` is the one
`contact_relative_on_strong_arm` produces; the statement quantifies over no coupling above it.

DERIVED: `16 * 4` is `StrongCoupling.touchDeg_bd_le`'s bound `16 * dim` at `dim = 4`, inherited from
`contact_relative_on_strong_arm` and not chosen here. `4` is also the exponent on `circLag d`, that
theorem's own decay power. `0` is the strict bound in `0 < b`, the sign condition `0 ≤ C` and
`0 ≤ β`, and the contact lag in `wilsonCorrAt N β 0`. `1` is the floor on `circLag d` and the bound
`coreRate … b < 1`. -/
theorem contact_relative_unconditional :
    ∃ b : ℝ, 0 < b ∧ MassGap.StrongCoupling.coreRate (16 * 4) b < 1 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)), 0 ≤ β → β ≤ b →
        1 ≤ Moment.circLag d →
          MassGap.wilsonCorrAt N β d
            ≤ C * MassGap.wilsonCorrAt N β 0 / (Moment.circLag d : ℝ) ^ 4 := by
  obtain ⟨b, hb, hrb, himp⟩ := MassGap.StrongArm.contact_relative_on_strong_arm
  exact ⟨b, hb, hrb, himp (contactFloor_holds b)⟩

#print axioms contact_relative_unconditional

/-- The Entroptics read's weight bound with its constant uniform in the aperture: one `δ > 0`
such that for every aperture `N`, every read `R` whose `ρ` is `corrClay (N + 1) β`, and every
coupling `β ∈ (0, b]` with `StrongCoupling.coreRate (16 * 4) β < 1`,

    R.p d ≤ (coreConst (16 * 4) β / (coreRate (16 * 4) β * δ) + 1) * coreRate (16 * 4) β ^ circLag d

at every lag `d`. The `∃ δ` binds outside the `∀ N`, so one `δ` serves every aperture.

`StrongCoupling.read_p_le_of_corrClay` supplies the bound at a per-read lower bound on `∑ρ`; here
that bound is `contactFloor_holds`, whose `δ` does not depend on `N`. The read's `ρ` is nonnegative,
so `∑ρ ≥ ρ 0`, and `ρ 0` is the contact term `wilsonCorrAt N β 0`.

Scope. `coreConst` and `coreRate` both depend on `β`, and the hypothesis `coreRate (16 * 4) β < 1`
is an assumption of this statement rather than a consequence; it is available near zero coupling by
`StrongCoupling.core_rate_lt_one_of_small_hypercubic`. The conclusion is quantified over
`β ∈ (0, b]` only.

DERIVED: `16 * 4` is `StrongCoupling.touchDeg_bd_le`'s `16 * dim` at `dim = 4`, inherited from
`read_p_le_of_corrClay`. The `+ 1` in the constant and the division by `coreRate` are that
theorem's own. `0` is the strict bound in `0 < δ` and `0 < β`, and the contact lag in `R.ρ 0` and
`wilsonCorrAt N β 0`, where the two plaquettes coincide. `1` is the successor in `corrClay (N + 1)`
and in `Fin (N + 1)`, the `+ 1` of the constant, and the bound in `coreRate … β < 1`. -/
theorem read_p_le_aperture_uniform (b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (R : Moment.Read N) (β : ℝ),
      (∀ d : Fin (N + 1), R.ρ d = MassGap.WilsonBridge.corrClay (N + 1) β d) →
      0 < β → β ≤ b → MassGap.StrongCoupling.coreRate (16 * 4) β < 1 →
      ∀ d : Fin (N + 1),
        R.p d ≤ (MassGap.StrongCoupling.coreConst (16 * 4) β
            / (MassGap.StrongCoupling.coreRate (16 * 4) β * δ) + 1)
          * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (Moment.circLag d) := by
  obtain ⟨δ, hδ, hfloor⟩ := contactFloor_holds b
  refine ⟨δ, hδ, fun N R β hρ hβ hb hr d => ?_⟩
  refine MassGap.StrongCoupling.read_p_le_of_corrClay R hρ hδ ?_ hβ hr d
  -- the contact term is the read's lag-zero weight, and the sum dominates that one term.
  have h0 : δ ≤ R.ρ 0 := by
    rw [hρ 0, ← MassGap.StrongArm.wilsonCorrAt_eq_corrClay N β 0]
    exact hfloor N β hβ.le hb
  exact le_trans h0 (Finset.single_le_sum (fun i _ => R.hρ i) (Finset.mem_univ (0 : Fin (N + 1))))

#print axioms read_p_le_aperture_uniform

end MassGap.ContactFloor
