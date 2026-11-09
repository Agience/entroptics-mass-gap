import Mathlib
import MassGap.FluxSectorFourier
import MassGap.FluxShareSquaring

/-!
# MassGap.ZeroFluxSector — the zero-flux sector of a finite abelian centre action

Let `(X, μ)` be a probability space, `G` a finite abelian group acting on `X` by measure-preserving
maps `act g` (`FluxSectorFourier.CentreAction`), and `a` a bounded, symmetric kernel invariant under
the action. On the lattice `a` is the transfer over half the time extent on one slice, and
`G = Z_N³` the centre of `SU(N)` placed on the three transverse directions.

The zero-flux kernel is the average over the action,

    zk a act (x, y) = |G|⁻¹ Σ_g a(x, act g y),

the sector of the trivial character: `sec a act 1 = zk a act` (`sec_one`). For `G = Z₂³` acting by
the three centre flips it is `SectorDefect.evL a flips`.

* `hs_zk_eq_mean`: `hs(zk) = |G|⁻¹ Σ_g twist(a, act g)`. The trace of the zero-flux sector is the
  mean of the twisted traces. So `hs(zk) ≤ hs(a)` (`hs_zk_le`), and for `a ≥ 0`, every twisted trace
  being nonnegative and the untwisted one being `hs(a)`, `hs(a)/|G| ≤ hs(zk)` (`hs_div_card_le_hs_zk`).
* `zk_conv`: `zk(a ∗ a) = zk ∗ zk`. The zero-flux sector of the transfer over twice the time is the
  doubled zero-flux sector.
* `hs_conv_zk_le`: `hs(zk ∗ zk) ≤ hs(a ∗ a)`, and `hs_conv_le_zk`:
  `hs(a ∗ a) ≤ hs(zk ∗ zk) + (hs(a) − hs(zk))²`. Both from `FluxSectorFourier.integral_conv_sq`: the
  doubled kernel's squared rows split over the sectors, the trivial sector's Gram kernel is `zk ∗ zk`
  (`gramC_one`), and each other sector's term is at most its trace squared
  (`FluxSectorFourier.norm_gramC_sq_le`), the traces summing to `hs(a)` (`sum_sectorTrace`).
* `dd_le_zk`: `dd(a) ≤ dd(zk) + 2 (log hs(a) − log hs(zk))`.
* `odds_conv_le_zk`: doubling the time squares the flux odds at the cost `exp(dd zk)`.

These are the `|G|`-sector forms of `SectorDefect.dd_le_evL`, `hs_conv_le_evL`, `hs_evL_ge`,
`FluxShareSquaring.hs_evL_eq`, `evL_conv` and `odds_conv_le`, with `2^{|l|}` replaced by `|G|`.

DERIVED (module-wide): `|G|⁻¹` is the average over the group; `0` is the identity element; `1` is the
trivial character; `2` is the square in `hs` and in the Cauchy–Schwarz step.
-/

noncomputable section

namespace MassGap.ZeroFluxSector

open MeasureTheory MassGap.KernelPower MassGap.FluxSectorFourier MassGap.SectorDefect
open scoped ComplexConjugate

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {act : G → X → X} {a : X → X → ℝ}

/-- **The zero-flux kernel** `zk a act (x, y) = |G|⁻¹ Σ_g a(x, act g y)`. -/
def zk (a : X → X → ℝ) (act : G → X → X) (x y : X) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, a x (act g y)

/-! ## 1. The kernel -/

omit [MeasurableSpace X] [DecidableEq G] in
/-- The trivial-character sector is the zero-flux kernel. -/
theorem sec_one (x y : X) : sec a act (1 : AddChar G ℂ) x y = (zk a act x y : ℂ) := by
  unfold sec zk
  simp only [AddChar.one_apply, one_mul]
  push_cast
  rfl

theorem zk_act_right (hA : CentreAction μ act) (h : G) (x y : X) :
    zk a act x (act h y) = zk a act x y := by
  have e := sec_act_right (a := a) hA (1 : AddChar G ℂ) h x y
  rw [sec_one, sec_one, AddChar.one_apply, map_one, one_mul] at e
  exact_mod_cast e

theorem zk_act_left (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (h : G) (x y : X) : zk a act (act h x) y = zk a act x y := by
  have e := sec_act_left (a := a) hA hinv (1 : AddChar G ℂ) h x y
  rw [sec_one, sec_one, AddChar.one_apply, one_mul] at e
  exact_mod_cast e

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem zk_symm (hA : CentreAction μ act) (hsym : ∀ x y, a x y = a y x)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) (x y : X) :
    zk a act x y = zk a act y x := by
  unfold zk
  congr 1
  have e : ∀ g, a y (act g x) = a x (act (-g) y) := fun g => by
    rw [hsym, ← hinv (-g) (act g x) y, ← hA.add, neg_add_cancel, hA.zero]
  simp_rw [e]
  exact (Equiv.sum_comp (Equiv.neg G) (fun g => a x (act g y))).symm

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem measurable_zk (ha : Bdd a) (hA : CentreAction μ act) :
    Measurable (Function.uncurry (zk a act)) := by
  show Measurable (fun p : X × X => (Fintype.card G : ℝ)⁻¹ * ∑ g, a p.1 (act g p.2))
  exact measurable_const.mul (Finset.measurable_sum _ fun g _ =>
    ha.meas.comp (measurable_fst.prodMk ((hA.meas g).comp measurable_snd)))

omit [MeasurableSpace X] in
theorem abs_zk_le {C : ℝ} (hC : ∀ x y, |a x y| ≤ C) (x y : X) : |zk a act x y| ≤ C := by
  unfold zk
  have hG : (0 : ℝ) < Fintype.card G := card_pos_real
  rw [abs_mul, abs_of_pos (inv_pos.mpr hG), inv_mul_le_iff₀ hG]
  calc |∑ g, a x (act g y)| ≤ ∑ g, |a x (act g y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, C := Finset.sum_le_sum fun g _ => hC _ _
    _ = Fintype.card G * C := by simp [Finset.sum_const, nsmul_eq_mul]

omit [IsProbabilityMeasure μ] in
theorem bdd_zk (ha : Bdd a) (hA : CentreAction μ act) : Bdd (zk a act) := by
  obtain ⟨C, hC⟩ := ha.bdd
  exact ⟨measurable_zk ha hA, C, abs_zk_le hC⟩

omit [MeasurableSpace X] in
theorem zk_low {c : ℝ} (hc : ∀ x y, c ≤ a x y) (x y : X) : c ≤ zk a act x y := by
  unfold zk
  have hG : (0 : ℝ) < Fintype.card G := card_pos_real
  rw [le_inv_mul_iff₀ hG]
  calc (Fintype.card G : ℝ) * c = ∑ _g : G, c := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ g, a x (act g y) := Finset.sum_le_sum fun g _ => hc _ _

/-! ## 2. The trivial sector in the Fourier decomposition -/

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem gramC_one (hA : CentreAction μ act) (hsym : ∀ x y, a x y = a y x)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) (x z : X) :
    gramC μ a act 1 x z = (conv μ (zk a act) (zk a act) x z : ℂ) := by
  unfold gramC
  rw [show conv μ (zk a act) (zk a act) x z = ∫ y, zk a act x y * zk a act y z ∂μ from rfl,
    ← integral_complex_ofReal]
  congr 1; funext y
  rw [sec_one, sec_one, Complex.conj_ofReal, zk_symm hA hsym hinv z y, Complex.ofReal_mul]

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem secDiag_one (x : X) : secDiag μ a act 1 x = ∫ y, zk a act x y ^ 2 ∂μ := by
  unfold secDiag
  congr 1; funext y
  rw [sec_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem sectorTrace_one : sectorTrace μ a act 1 = hs μ (zk a act) := by
  unfold sectorTrace hs
  congr 1; funext x; exact secDiag_one x

/-! ## 3. The trace of the zero-flux sector -/

/-- **The zero-flux trace is the mean twisted trace**: `hs(zk) = |G|⁻¹ Σ_g twist(a, act g)`. -/
theorem hs_zk_eq_mean (ha : Bdd a) (hA : CentreAction μ act) :
    hs μ (zk a act) = (Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g) := by
  have hrow : ∀ x, ∫ y, zk a act x y ^ 2 ∂μ = ∫ y, a x y * zk a act x y ∂μ := by
    intro x
    have h1 := integral_a_mul_conj_sec ha hA (1 : AddChar G ℂ) x x
    rw [gramC_diag, secDiag_one] at h1
    simp_rw [sec_one, Complex.conj_ofReal, ← Complex.ofReal_mul] at h1
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1.symm
  have hrow2 : ∀ x, ∫ y, a x y * zk a act x y ∂μ
      = (Fintype.card G : ℝ)⁻¹ * ∑ g, ∫ y, a x y * a x (act g y) ∂μ := by
    intro x
    have e : (fun y => a x y * zk a act x y)
        = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, a x y * a x (act g y) := by
      funext y
      show a x y * ((Fintype.card G : ℝ)⁻¹ * ∑ g, a x (act g y)) = _
      rw [mul_left_comm, Finset.mul_sum]
    rw [e, integral_const_mul, integral_finsetSum _ fun g _ =>
      FluxSectorBound.bdd_rows ha (bdd_act ha hA g) x x]
  unfold hs
  simp_rw [hrow, hrow2]
  rw [integral_const_mul, integral_finsetSum _ fun g _ =>
    int_row (FluxSectorBound.bdd_mul ha (bdd_act ha hA g))]
  rfl

/-- The zero-flux trace is at most the trace. -/
theorem hs_zk_le (ha : Bdd a) (hA : CentreAction μ act) : hs μ (zk a act) ≤ hs μ a := by
  rw [hs_zk_eq_mean ha hA]
  have hG : (0 : ℝ) < Fintype.card G := card_pos_real
  rw [inv_mul_le_iff₀ hG]
  calc ∑ g, FluxSectorBound.twist μ a (act g) ≤ ∑ _g : G, hs μ a :=
        Finset.sum_le_sum fun g _ => FluxShareSquaring.twist_le_hs ha (hA.mp g)
    _ = Fintype.card G * hs μ a := by simp [Finset.sum_const, nsmul_eq_mul]

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
theorem act_zero_eq_id (hA : CentreAction μ act) : act 0 = id := funext hA.zero

/-- **For a nonnegative kernel the zero-flux sector carries at least `1/|G|` of the trace.** -/
theorem hs_div_card_le_hs_zk (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y) (hA : CentreAction μ act) :
    hs μ a / Fintype.card G ≤ hs μ (zk a act) := by
  rw [hs_zk_eq_mean ha hA, div_eq_inv_mul]
  have hG : (0 : ℝ) < Fintype.card G := card_pos_real
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hG.le)
  have h0 : FluxSectorBound.twist μ a (act 0) = hs μ a := by
    rw [act_zero_eq_id hA, FluxShareSquaring.twist_id]
  rw [← h0]
  exact Finset.single_le_sum (f := fun g => FluxSectorBound.twist μ a (act g))
    (fun g _ => integral_nonneg fun x => integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _))
    (Finset.mem_univ 0)

/-! ## 4. Time doubling -/

theorem conv_zk_eq (ha : Bdd a) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) (x z : X) :
    conv μ (zk a act) (zk a act) x z = conv μ a (zk a act) x z := by
  obtain ⟨C, hC⟩ := ha.bdd
  have bz := bdd_zk ha hA
  have hterm : ∀ g, ∫ y, a x (act g y) * zk a act y z ∂μ = ∫ y, a x y * zk a act y z ∂μ := by
    intro g
    have h := hA.integral_comp g (fun y => a x y * zk a act y z)
    rw [← h]
    congr 1; funext y
    rw [zk_act_left hA hinv]
  have hint : ∀ g, Integrable (fun y => a x (act g y) * zk a act y z) μ := fun g =>
    FluxShareSquaring.int_prod ((ha.row x).comp (hA.meas g)) (bz.col z) (fun y => hC x _)
      (fun y => abs_zk_le hC y z)
  show ∫ y, zk a act x y * zk a act y z ∂μ = ∫ y, a x y * zk a act y z ∂μ
  have e : (fun y => zk a act x y * zk a act y z)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, a x (act g y) * zk a act y z := by
    funext y
    show (Fintype.card G : ℝ)⁻¹ * (∑ g, a x (act g y)) * zk a act y z = _
    rw [mul_assoc, Finset.sum_mul]
  rw [e, integral_const_mul, integral_finsetSum _ fun g _ => hint g]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (card_pos_real (G := G)).ne', one_mul]

/-- **The zero-flux sector of the doubled kernel is the doubled zero-flux sector**:
`zk(a ∗ a) = zk ∗ zk`. -/
theorem zk_conv (ha : Bdd a) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) :
    zk (conv μ a a) act = conv μ (zk a act) (zk a act) := by
  obtain ⟨C, hC⟩ := ha.bdd
  funext x z
  rw [conv_zk_eq ha hA hinv x z]
  show (Fintype.card G : ℝ)⁻¹ * ∑ g, ∫ y, a x y * a y (act g z) ∂μ
    = ∫ y, a x y * zk a act y z ∂μ
  have e : (fun y => a x y * zk a act y z)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, a x y * a y (act g z) := by
    funext y
    show a x y * ((Fintype.card G : ℝ)⁻¹ * ∑ g, a y (act g z)) = _
    rw [mul_left_comm, Finset.mul_sum]
  rw [e, integral_const_mul, integral_finsetSum _ fun g _ =>
    FluxShareSquaring.int_prod (ha.row x) (ha.col (act g z)) (fun y => hC x y) (fun y => hC y _)]

/-! ## 5. The doubled trace against the zero-flux sector -/

omit [IsProbabilityMeasure μ] [DecidableEq G] in
theorem norm_gramC_one_sq (hA : CentreAction μ act) (hsym : ∀ x y, a x y = a y x)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) (x : X) :
    ∫ z, ‖gramC μ a act 1 x z‖ ^ 2 ∂μ = ∫ z, conv μ (zk a act) (zk a act) x z ^ 2 ∂μ := by
  congr 1; funext z
  rw [gramC_one hA hsym hinv, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The zero-flux doubled trace is at most the doubled trace.** -/
theorem hs_conv_zk_le (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) :
    hs μ (conv μ (zk a act) (zk a act)) ≤ hs μ (conv μ a a) := by
  have bz := bdd_zk ha hA
  have hpt : ∀ x, ∫ z, conv μ (zk a act) (zk a act) x z ^ 2 ∂μ ≤ ∫ z, conv μ a a x z ^ 2 ∂μ := by
    intro x
    rw [integral_conv_sq ha hsym hA hinv x, ← norm_gramC_one_sq hA hsym hinv x]
    exact Finset.single_le_sum (f := fun ψ => ∫ z, ‖gramC μ a act ψ x z‖ ^ 2 ∂μ)
      (fun ψ _ => integral_nonneg fun z => sq_nonneg _) (Finset.mem_univ 1)
  unfold hs
  exact integral_mono (int_row (bdd_sq (bz.conv (μ := μ) bz)))
    (int_row (bdd_sq (ha.conv (μ := μ) ha))) hpt

/-- **The doubled trace against the zero-flux sector**:
`hs(a ∗ a) ≤ hs(zk ∗ zk) + (hs(a) − hs(zk))²`. -/
theorem hs_conv_le_zk (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) :
    hs μ (conv μ a a) ≤ hs μ (conv μ (zk a act) (zk a act)) + (hs μ a - hs μ (zk a act)) ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_bound ha
  have bz := bdd_zk ha hA
  set s := (Finset.univ : Finset (AddChar G ℂ)).erase 1 with hsdef
  have hpt : ∀ x, ∫ z, conv μ a a x z ^ 2 ∂μ
      ≤ ∫ z, conv μ (zk a act) (zk a act) x z ^ 2 ∂μ
        + ∑ ψ ∈ s, secDiag μ a act ψ x * sectorTrace μ a act ψ := by
    intro x
    rw [integral_conv_sq ha hsym hA hinv x,
      ← Finset.add_sum_erase Finset.univ (fun ψ => ∫ z, ‖gramC μ a act ψ x z‖ ^ 2 ∂μ)
        (Finset.mem_univ 1),
      norm_gramC_one_sq hA hsym hinv x]
    refine add_le_add le_rfl (Finset.sum_le_sum fun ψ _ => ?_)
    unfold sectorTrace
    rw [← integral_const_mul]
    have iL : Integrable (fun z => ‖gramC μ a act ψ x z‖ ^ 2) μ :=
      rint ((measurable_gramC_row ha hA ψ x).norm.pow_const 2) (C := C * C * (C * C)) fun z => by
        rw [norm_pow, norm_norm, sq]
        exact mul_le_mul (norm_gramC_le hC ψ x z) (norm_gramC_le hC ψ x z) (norm_nonneg _)
          (mul_nonneg hC0 hC0)
    exact integral_mono iL ((int_secDiag ha hA hC ψ).const_mul _)
      fun z => norm_gramC_sq_le ha hA ψ x z
  have iA : Integrable (fun x => ∫ z, conv μ a a x z ^ 2 ∂μ) μ :=
    int_row (bdd_sq (ha.conv (μ := μ) ha))
  have iZ : Integrable (fun x => ∫ z, conv μ (zk a act) (zk a act) x z ^ 2 ∂μ) μ :=
    int_row (bdd_sq (bz.conv (μ := μ) bz))
  have iS : Integrable (fun x => ∑ ψ ∈ s, secDiag μ a act ψ x * sectorTrace μ a act ψ) μ :=
    integrable_finsetSum _ fun ψ _ => (int_secDiag ha hA hC ψ).mul_const _
  have hint : hs μ (conv μ a a) ≤ hs μ (conv μ (zk a act) (zk a act))
      + ∑ ψ ∈ s, sectorTrace μ a act ψ * sectorTrace μ a act ψ := by
    unfold hs
    calc ∫ x, ∫ z, conv μ a a x z ^ 2 ∂μ ∂μ
        ≤ ∫ x, (∫ z, conv μ (zk a act) (zk a act) x z ^ 2 ∂μ
            + ∑ ψ ∈ s, secDiag μ a act ψ x * sectorTrace μ a act ψ) ∂μ :=
          integral_mono iA (iZ.add iS) hpt
      _ = _ := by
          rw [integral_add iZ iS, integral_finsetSum _ fun ψ _ =>
            (int_secDiag ha hA hC ψ).mul_const _]
          congr 1
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [integral_mul_const]; rfl
  have hsum : ∑ ψ ∈ s, sectorTrace μ a act ψ = hs μ a - hs μ (zk a act) := by
    have h1 := sum_sectorTrace ha hsym hA
    rw [← Finset.add_sum_erase Finset.univ (sectorTrace μ a act) (Finset.mem_univ 1),
      sectorTrace_one] at h1
    linarith
  have hsq : ∑ ψ ∈ s, sectorTrace μ a act ψ * sectorTrace μ a act ψ
      ≤ (∑ ψ ∈ s, sectorTrace μ a act ψ) ^ 2 := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_le_sum fun ψ hψ => mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := sectorTrace μ a act) (fun φ _ => sectorTrace_nonneg φ) hψ)
      (sectorTrace_nonneg ψ)
  rw [hsum] at hsq
  linarith

/-! ## 6. The doubling defect -/

theorem hs_zk_pos {c : ℝ} (hc : 0 < c) (ha : Bdd a) (hA : CentreAction μ act)
    (hlow : ∀ x y, c ≤ a x y) : 0 < hs μ (zk a act) := by
  have := sq_le_hs (μ := μ) (bdd_zk ha hA) hc.le (zk_low (act := act) hlow)
  have : 0 < c ^ 2 := by positivity
  linarith

theorem hs_conv_zk_pos {c : ℝ} (hc : 0 < c) (ha : Bdd a) (hA : CentreAction μ act)
    (hlow : ∀ x y, c ≤ a x y) : 0 < hs μ (conv μ (zk a act) (zk a act)) := by
  have bz := bdd_zk ha hA
  have := sq_le_hs (μ := μ) (bz.conv (μ := μ) bz) (mul_nonneg hc.le hc.le)
    (conv_low (μ := μ) bz hc.le (zk_low (act := act) hlow))
  have : 0 < (c * c) ^ 2 := by positivity
  linarith

/-- **The defect is at most the zero-flux sector's defect plus twice the log of its inverse share.** -/
theorem dd_le_zk {c : ℝ} (hc : 0 < c) (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (hlow : ∀ x y, c ≤ a x y) :
    dd μ a ≤ dd μ (zk a act) + 2 * (Real.log (hs μ a) - Real.log (hs μ (zk a act))) := by
  have := Real.log_le_log (hs_conv_zk_pos hc ha hA hlow) (hs_conv_zk_le ha hsym hA hinv)
  unfold dd
  linarith

/-- **Doubling the time squares the flux odds**, at the cost of the zero-flux sector's defect:
`(hs(a∗a) − hs(zk(a∗a)))/hs(a∗a) ≤ ((hs a − hs zk)/hs zk)² · exp(dd zk)`. -/
theorem odds_conv_le_zk {c : ℝ} (hc : 0 < c) (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (hlow : ∀ x y, c ≤ a x y) :
    (hs μ (conv μ a a) - hs μ (zk (conv μ a a) act)) / hs μ (conv μ a a)
      ≤ ((hs μ a - hs μ (zk a act)) / hs μ (zk a act)) ^ 2 * Real.exp (dd μ (zk a act)) := by
  rw [zk_conv ha hA hinv]
  have h1 : hs μ (conv μ a a) - hs μ (conv μ (zk a act) (zk a act))
      ≤ (hs μ a - hs μ (zk a act)) ^ 2 := by
    have := hs_conv_le_zk ha hsym hA hinv; linarith
  exact FluxShareSquaring.odds_step (hs_zk_pos hc ha hA hlow) (hs_conv_zk_pos hc ha hA hlow)
    (hs_conv_zk_le ha hsym hA hinv) h1 rfl

end MassGap.ZeroFluxSector

end

#print axioms MassGap.ZeroFluxSector.zk_symm
#print axioms MassGap.ZeroFluxSector.hs_zk_eq_mean
#print axioms MassGap.ZeroFluxSector.hs_zk_le
#print axioms MassGap.ZeroFluxSector.hs_div_card_le_hs_zk
#print axioms MassGap.ZeroFluxSector.zk_conv
#print axioms MassGap.ZeroFluxSector.hs_conv_zk_le
#print axioms MassGap.ZeroFluxSector.hs_conv_le_zk
#print axioms MassGap.ZeroFluxSector.dd_le_zk
#print axioms MassGap.ZeroFluxSector.odds_conv_le_zk
