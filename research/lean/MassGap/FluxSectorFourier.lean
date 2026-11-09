import Mathlib
import MassGap.FluxSectorBound

/-!
# MassGap.FluxSectorFourier — the doubled trace over the flux sectors of a finite abelian action

Let `(X, μ)` be a probability space and `G` a finite abelian group acting on `X` by measurable,
measure-preserving maps `act g`. Let `a` be a bounded, measurable, symmetric kernel on `X` with
`a(act g x, act g y) = a(x, y)`. On the lattice, `a` is the transfer over half the time extent, `X`
the slice configurations, and `G = Z_N × Z_N` the centre flips of two spatial directions.
`FluxSectorBound` is the case `G = Z_2` with one flip.

The characters `ψ` of `G` split `a` into the electric-flux sectors
`e_ψ(x, y) = |G|⁻¹ Σ_g ψ(g) a(x, act g y)`, with `a = Σ_ψ e_ψ` (`sum_sec`).

* `integral_sec_mul_conj`: two different sectors are orthogonal in the second variable. Moving `y`
  along `act h` multiplies the integrand by `conj ψ(h) · φ(h)`, which is not `1` for some `h`.
* `conv_eq_sum_gram`: `a ∗ a = Σ_ψ G_ψ`, with `G_ψ(x, z) = ∫ e_ψ(x, y) conj e_ψ(z, y) dy`.
* `integral_conv_sq`: `∫ (a ∗ a)(x, z)² dz = Σ_ψ ∫ |G_ψ(x, z)|² dz`, since the Gram kernels of two
  sectors are orthogonal in `z` as well.
* `hs_conv_le_sum_sq`: Cauchy–Schwarz on each Gram kernel gives `hs(a ∗ a) ≤ Σ_ψ c_ψ²`, where
  `c_ψ = ∫∫ |e_ψ|²` is the trace of sector `ψ`, and `Σ_ψ c_ψ = hs(a)` (`sum_sectorTrace`).
* `sectorTrace_le`: for `a ≥ 0`, every sector trace is at most the average twisted trace
  `τ = |G|⁻¹ Σ_g twist(a, act g)`.
* **`hs_conv_le_mul_avg_twist`**: `hs(a ∗ a) ≤ hs(a) · τ` for `a ≥ 0`.
* `twist_sum_le`: with a weight `χ_g ∈ [0, 1]` per group element marking the slices where the
  `g`-twisted row is not suppressed, and with the weights summing to at most `|G|/2` except where `a`
  is small, `Σ_g twist(a, act g) ≤ |G| ε + (|G|/2) hs(a) + |G| η`.
* **`hs_conv_le_three_quarters`**: together, `hs(a ∗ a) ≤ (3/4) hs(a)²` when `ε + η ≤ hs(a)/4`.

DERIVED (module-wide): `|G|⁻¹` is the average over the group; `0` is the identity element and the
cross terms; `2` is the square, the halving of the weight sum, and the arithmetic–geometric mean;
`3/4 = 1/2 + 1/4`, the weight bound `1/2` plus the smallness margin `1/4`.
-/

noncomputable section

namespace MassGap.FluxSectorFourier

open MeasureTheory MassGap.KernelPower
open scoped ComplexConjugate

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **A measure-preserving action** of `G` on `X`. -/
structure CentreAction (μ : Measure X) (act : G → X → X) : Prop where
  meas : ∀ g, Measurable (act g)
  zero : ∀ x, act 0 x = x
  add : ∀ g h x, act (g + h) x = act g (act h x)
  mp : ∀ g, MeasurePreserving (act g) μ μ

variable {act : G → X → X}

/-- One element of the action as a measurable equivalence. -/
def CentreAction.equiv (hA : CentreAction μ act) (g : G) : X ≃ᵐ X where
  toFun := act g
  invFun := act (-g)
  left_inv x := by
    show act (-g) (act g x) = x
    rw [← hA.add, neg_add_cancel, hA.zero]
  right_inv x := by
    show act g (act (-g) x) = x
    rw [← hA.add, add_neg_cancel, hA.zero]
  measurable_toFun := hA.meas g
  measurable_invFun := hA.meas (-g)

theorem CentreAction.integral_comp (hA : CentreAction μ act) (g : G) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : X → E) :
    ∫ y, f (act g y) ∂μ = ∫ y, f y ∂μ := by
  have hmp : MeasurePreserving (hA.equiv g) μ μ := hA.mp g
  exact hmp.integral_comp' f

/-! ## Bookkeeping -/

theorem cint {f : X → ℂ} (hm : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

theorem rint {f : X → ℝ} (hm : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

theorem norm_integral_le_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E}
    {C : ℝ} (hb : ∀ y, ‖f y‖ ≤ C) : ‖∫ y, f y ∂μ‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall hb)
  simpa using h

theorem exists_bound {a : X → X → ℝ} (ha : Bdd a) : ∃ C, 0 ≤ C ∧ ∀ x y, ‖a x y‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha.bdd
  exact ⟨|C|, abs_nonneg _, fun x y => by
    rw [Real.norm_eq_abs]; exact (hC x y).trans (le_abs_self C)⟩

theorem card_pos_real : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos

theorem card_ne_zero_complex : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem norm_char (ψ : AddChar G ℂ) (g : G) : ‖ψ g‖ = 1 := AddChar.norm_apply ψ g

/-! ## The flux sectors -/

/-- **The sector kernel** `e_ψ(x, y) = |G|⁻¹ Σ_g ψ(g) a(x, act g y)`. -/
def sec (a : X → X → ℝ) (act : G → X → X) (ψ : AddChar G ℂ) (x y : X) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g, ψ g * (a x (act g y) : ℂ)

variable {a : X → X → ℝ}

theorem measurable_sec (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ) :
    Measurable (Function.uncurry (sec a act ψ)) := by
  show Measurable (fun p : X × X => (Fintype.card G : ℂ)⁻¹ * ∑ g, ψ g * (a p.1 (act g p.2) : ℂ))
  refine measurable_const.mul (Finset.measurable_sum _ fun g _ => measurable_const.mul ?_)
  exact Complex.measurable_ofReal.comp
    (ha.meas.comp (measurable_fst.prodMk ((hA.meas g).comp measurable_snd)))

theorem measurable_sec_row (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ) (x : X) :
    Measurable (sec a act ψ x) := by
  show Measurable (fun y => (Fintype.card G : ℂ)⁻¹ * ∑ g, ψ g * (a x (act g y) : ℂ))
  refine measurable_const.mul (Finset.measurable_sum _ fun g _ => measurable_const.mul ?_)
  exact Complex.measurable_ofReal.comp ((ha.row x).comp (hA.meas g))

theorem norm_sec_le {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C) (ψ : AddChar G ℂ) (x y : X) :
    ‖sec a act ψ x y‖ ≤ C := by
  unfold sec
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ card_pos_real]
  calc ‖∑ g, ψ g * (a x (act g y) : ℂ)‖ ≤ ∑ g, ‖ψ g * (a x (act g y) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _g : G, C := Finset.sum_le_sum fun g _ => by
        rw [norm_mul, norm_char, one_mul, Complex.norm_real]; exact hC _ _
    _ = Fintype.card G * C := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **The sectors add up to the kernel.** -/
theorem sum_sec (hA : CentreAction μ act) (x y : X) :
    ∑ ψ : AddChar G ℂ, sec a act ψ x y = (a x y : ℂ) := by
  unfold sec
  rw [← Finset.mul_sum, Finset.sum_comm]
  have e : ∀ g : G, ∑ ψ : AddChar G ℂ, ψ g * (a x (act g y) : ℂ)
      = (if g = 0 then (Fintype.card G : ℂ) else 0) * (a x (act g y) : ℂ) := by
    intro g; rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  simp_rw [e, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hA.zero]
  rw [← mul_assoc, inv_mul_cancel₀ card_ne_zero_complex, one_mul]

/-- Reindexing a character sum by a translation. -/
theorem sum_shift (ψ : AddChar G ℂ) (F : G → ℂ) (h : G) :
    ∑ g, ψ g * F (g + h) = conj (ψ h) * ∑ g, ψ g * F g := by
  have e1 : ∑ g, ψ g * F (g + h) = ∑ g, (fun k => ψ (k - h) * F k) (Equiv.addRight h g) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [e1, Equiv.sum_comp (Equiv.addRight h) (fun k => ψ (k - h) * F k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  ring

theorem sum_shift_neg (ψ : AddChar G ℂ) (F : G → ℂ) (h : G) :
    ∑ g, ψ g * F (g - h) = ψ h * ∑ g, ψ g * F g := by
  have e : ∑ g, ψ g * F (g - h) = ∑ g, ψ g * F (g + -h) := by
    simp only [sub_eq_add_neg]
  rw [e, sum_shift, AddChar.map_neg_eq_conj, Complex.conj_conj]

/-- Moving the second variable along the action multiplies a sector by `conj ψ(h)`. -/
theorem sec_act_right (hA : CentreAction μ act) (ψ : AddChar G ℂ) (h : G) (x y : X) :
    sec a act ψ x (act h y) = conj (ψ h) * sec a act ψ x y := by
  unfold sec
  have e : ∑ g, ψ g * (a x (act g (act h y)) : ℂ)
      = ∑ g, ψ g * (fun k => (a x (act k y) : ℂ)) (g + h) :=
    Finset.sum_congr rfl fun g _ => by simp only [hA.add]
  rw [e, sum_shift ψ (fun k => (a x (act k y) : ℂ)) h]
  ring

/-- Moving the first variable along the action multiplies a sector by `ψ(h)`. -/
theorem sec_act_left (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (ψ : AddChar G ℂ) (h : G) (x y : X) :
    sec a act ψ (act h x) y = ψ h * sec a act ψ x y := by
  unfold sec
  have key : ∀ g, a (act h x) (act g y) = a x (act (g - h) y) := fun g => by
    have := hinv h x (act (g - h) y)
    rwa [← hA.add, show h + (g - h) = g by abel] at this
  have e : ∑ g, ψ g * (a (act h x) (act g y) : ℂ)
      = ∑ g, ψ g * (fun k => (a x (act k y) : ℂ)) (g - h) :=
    Finset.sum_congr rfl fun g _ => by simp only [key]
  rw [e, sum_shift_neg ψ (fun k => (a x (act k y) : ℂ)) h]
  ring

/-- An integral that is multiplied by `c ≠ 1` under one element of the action vanishes. -/
theorem integral_eq_zero_of_act (hA : CentreAction μ act) {f : X → ℂ} {h : G} {c : ℂ}
    (hf : ∀ y, f (act h y) = c * f y) (hc : c ≠ 1) : ∫ y, f y ∂μ = 0 := by
  have e := hA.integral_comp h f
  simp_rw [hf] at e
  rw [integral_const_mul] at e
  have h0 : (c - 1) * ∫ y, f y ∂μ = 0 := by rw [sub_mul, e, one_mul, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hc
  · exact h1

/-- Two different characters differ by a phase other than `1` at some element. -/
theorem exists_phase_ne {ψ φ : AddChar G ℂ} (hne : ψ ≠ φ) : ∃ h : G, conj (ψ h) * φ h ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  apply hne
  ext h
  have hn : ψ h * conj (ψ h) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_char]; simp
  calc ψ h = ψ h * (conj (ψ h) * φ h) := by rw [hcon h, mul_one]
    _ = (ψ h * conj (ψ h)) * φ h := by ring
    _ = φ h := by rw [hn, one_mul]

theorem int_sec_conj (ha : Bdd a) (hA : CentreAction μ act) {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C)
    (φ ψ : AddChar G ℂ) (x z : X) :
    Integrable (fun y => sec a act φ x y * conj (sec a act ψ z y)) μ := by
  refine cint ((measurable_sec_row ha hA φ x).mul
    (Complex.continuous_conj.measurable.comp (measurable_sec_row ha hA ψ z))) (C := C * C)
    fun y => ?_
  rw [norm_mul, Complex.norm_conj]
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x x)
  exact mul_le_mul (norm_sec_le hC φ x y) (norm_sec_le hC ψ z y) (norm_nonneg _) h0

/-- **Different sectors are orthogonal in the second variable.** -/
theorem integral_sec_mul_conj (hA : CentreAction μ act) {ψ φ : AddChar G ℂ} (hne : ψ ≠ φ)
    (x z : X) : ∫ y, sec a act ψ x y * conj (sec a act φ z y) ∂μ = 0 := by
  obtain ⟨h, hh⟩ := exists_phase_ne hne
  refine integral_eq_zero_of_act hA (h := h) (c := conj (ψ h) * φ h) (fun y => ?_) hh
  rw [sec_act_right hA, sec_act_right hA, map_mul, Complex.conj_conj]
  ring

/-! ## The Gram kernels of the sectors -/

/-- **The Gram kernel of a sector**, `G_ψ(x, z) = ∫ e_ψ(x, y) conj e_ψ(z, y) dy`. -/
def gramC (μ : Measure X) (a : X → X → ℝ) (act : G → X → X) (ψ : AddChar G ℂ) (x z : X) : ℂ :=
  ∫ y, sec a act ψ x y * conj (sec a act ψ z y) ∂μ

/-- **The diagonal of a sector's Gram kernel**, `∫ |e_ψ(x, y)|² dy`. -/
def secDiag (μ : Measure X) (a : X → X → ℝ) (act : G → X → X) (ψ : AddChar G ℂ) (x : X) : ℝ := ∫ y, ‖sec a act ψ x y‖ ^ 2 ∂μ

/-- **The trace of a sector**, `c_ψ = ∫∫ |e_ψ|²`. -/
def sectorTrace (μ : Measure X) (a : X → X → ℝ) (act : G → X → X) (ψ : AddChar G ℂ) : ℝ := ∫ x, secDiag μ a act ψ x ∂μ

theorem gramC_diag (ψ : AddChar G ℂ) (x : X) :
    gramC μ a act ψ x x = (secDiag μ a act ψ x : ℂ) := by
  unfold gramC secDiag
  rw [← integral_complex_ofReal]
  congr 1; funext y
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem secDiag_nonneg (ψ : AddChar G ℂ) (x : X) : 0 ≤ secDiag μ a act ψ x :=
  integral_nonneg fun _ => sq_nonneg _

theorem sectorTrace_nonneg (ψ : AddChar G ℂ) : 0 ≤ sectorTrace μ a act ψ :=
  integral_nonneg fun x => secDiag_nonneg ψ x

theorem measurable_gramC_row (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ) (x : X) :
    Measurable (gramC μ a act ψ x) := by
  have hm : Measurable (fun p : X × X => sec a act ψ x p.2 * conj (sec a act ψ p.1 p.2)) :=
    ((measurable_sec_row ha hA ψ x).comp measurable_snd).mul
      (Complex.continuous_conj.measurable.comp (measurable_sec ha hA ψ))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem norm_gramC_le {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C) (ψ : AddChar G ℂ) (x z : X) :
    ‖gramC μ a act ψ x z‖ ≤ C * C := by
  unfold gramC
  refine norm_integral_le_const fun y => ?_
  rw [norm_mul, Complex.norm_conj]
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x x)
  exact mul_le_mul (norm_sec_le hC ψ x y) (norm_sec_le hC ψ z y) (norm_nonneg _) h0

theorem measurable_secDiag (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ) :
    Measurable (secDiag μ a act ψ) := by
  have hm : Measurable (Function.uncurry fun x y => ‖sec a act ψ x y‖ ^ 2) :=
    (measurable_sec ha hA ψ).norm.pow_const 2
  exact measurable_integral_right hm

theorem secDiag_le {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C) (ψ : AddChar G ℂ) (x : X) :
    secDiag μ a act ψ x ≤ C * C := by
  unfold secDiag
  have h := norm_integral_le_const (μ := μ) (f := fun y => ‖sec a act ψ x y‖ ^ 2) (C := C * C)
    fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
      exact mul_le_mul (norm_sec_le (act := act) hC ψ x y) (norm_sec_le (act := act) hC ψ x y)
        (norm_nonneg _) ((norm_nonneg _).trans (hC x x))
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h)

theorem int_secDiag (ha : Bdd a) (hA : CentreAction μ act) {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C)
    (ψ : AddChar G ℂ) : Integrable (secDiag μ a act ψ) μ :=
  rint (measurable_secDiag ha hA ψ) (C := C * C) fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (secDiag_nonneg ψ x)]; exact secDiag_le hC ψ x

/-- `∫ a(x, y) conj e_ψ(z, y) dy = G_ψ(x, z)`: only the sector `ψ` of `a(x, ·)` survives. -/
theorem integral_a_mul_conj_sec (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ)
    (x z : X) : ∫ y, (a x y : ℂ) * conj (sec a act ψ z y) ∂μ = gramC μ a act ψ x z := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  have e : ∀ y, (a x y : ℂ) * conj (sec a act ψ z y)
      = ∑ φ : AddChar G ℂ, sec a act φ x y * conj (sec a act ψ z y) := by
    intro y; rw [← sum_sec hA x y, Finset.sum_mul]
  simp_rw [e]
  rw [integral_finsetSum _ fun φ _ => int_sec_conj ha hA hC φ ψ x z]
  rw [Finset.sum_eq_single ψ (fun φ _ hφ => integral_sec_mul_conj hA hφ x z)
    (fun h => absurd (Finset.mem_univ ψ) h)]
  rfl

theorem int_a_conj_sec (ha : Bdd a) (hA : CentreAction μ act) {C : ℝ} (hC : ∀ x y, ‖a x y‖ ≤ C)
    (ψ : AddChar G ℂ) (x z : X) :
    Integrable (fun y => (a x y : ℂ) * conj (sec a act ψ z y)) μ := by
  refine cint ((Complex.measurable_ofReal.comp (ha.row x)).mul
    (Complex.continuous_conj.measurable.comp (measurable_sec_row ha hA ψ z))) (C := C * C)
    fun y => ?_
  rw [norm_mul, Complex.norm_conj, Complex.norm_real]
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x x)
  exact mul_le_mul (hC x y) (norm_sec_le hC ψ z y) (norm_nonneg _) h0

/-- **`a ∗ a` is the sum of the sector Gram kernels.** -/
theorem conv_eq_sum_gram (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (x z : X) : ((conv μ a a x z : ℝ) : ℂ) = ∑ ψ, gramC μ a act ψ x z := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  unfold conv
  rw [← integral_complex_ofReal]
  have e : ∀ y, ((a x y * a y z : ℝ) : ℂ) = ∑ ψ, (a x y : ℂ) * conj (sec a act ψ z y) := by
    intro y
    rw [← Finset.mul_sum, ← map_sum, sum_sec hA, Complex.conj_ofReal, hsym y z,
      Complex.ofReal_mul]
  simp_rw [e]
  rw [integral_finsetSum _ fun ψ _ => int_a_conj_sec ha hA hC ψ x z]
  exact Finset.sum_congr rfl fun ψ _ => integral_a_mul_conj_sec ha hA ψ x z

/-- Moving the second variable along the action multiplies a Gram kernel by `conj ψ(h)`. -/
theorem gramC_act_right (hA : CentreAction μ act) (hinv : ∀ g x y, a (act g x) (act g y) = a x y)
    (ψ : AddChar G ℂ) (h : G) (x z : X) :
    gramC μ a act ψ x (act h z) = conj (ψ h) * gramC μ a act ψ x z := by
  unfold gramC
  rw [← integral_const_mul]
  congr 1; funext y
  rw [sec_act_left hA hinv, map_mul]
  ring

/-- **Different sector Gram kernels are orthogonal in the second variable.** -/
theorem integral_gramC_mul_conj (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) {ψ φ : AddChar G ℂ} (hne : ψ ≠ φ) (x : X) :
    ∫ z, gramC μ a act ψ x z * conj (gramC μ a act φ x z) ∂μ = 0 := by
  obtain ⟨h, hh⟩ := exists_phase_ne hne
  refine integral_eq_zero_of_act hA (h := h) (c := conj (ψ h) * φ h) (fun z => ?_) hh
  rw [gramC_act_right hA hinv, gramC_act_right hA hinv, map_mul, Complex.conj_conj]
  ring

theorem int_gramC_conj (ha : Bdd a) (hA : CentreAction μ act) {C : ℝ}
    (hC : ∀ x y, ‖a x y‖ ≤ C) (ψ φ : AddChar G ℂ) (x : X) :
    Integrable (fun z => gramC μ a act ψ x z * conj (gramC μ a act φ x z)) μ := by
  refine cint ((measurable_gramC_row ha hA ψ x).mul
    (Complex.continuous_conj.measurable.comp (measurable_gramC_row ha hA φ x)))
    (C := C * C * (C * C)) fun z => ?_
  rw [norm_mul, Complex.norm_conj]
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x x)
  exact mul_le_mul (norm_gramC_le hC ψ x z) (norm_gramC_le hC φ x z) (norm_nonneg _)
    (mul_nonneg h0 h0)

/-- **The squared doubled kernel splits over the sectors**:
`∫ (a ∗ a)(x, z)² dz = Σ_ψ ∫ |G_ψ(x, z)|² dz`. -/
theorem integral_conv_sq (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) (x : X) :
    ∫ z, conv μ a a x z ^ 2 ∂μ = ∑ ψ, ∫ z, ‖gramC μ a act ψ x z‖ ^ 2 ∂μ := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_sum]
  have e1 : ∀ z, ((conv μ a a x z ^ 2 : ℝ) : ℂ)
      = ∑ ψ, ∑ φ, gramC μ a act ψ x z * conj (gramC μ a act φ x z) := by
    intro z
    have h1 := conv_eq_sum_gram ha hsym hA x z
    have h2 : ((conv μ a a x z : ℝ) : ℂ) = conj ((conv μ a a x z : ℝ) : ℂ) :=
      (Complex.conj_ofReal _).symm
    rw [Complex.ofReal_pow, sq]
    nth_rewrite 2 [h2]
    rw [h1, map_sum, Finset.sum_mul_sum]
  simp_rw [e1]
  rw [integral_finsetSum _ fun ψ _ => integrable_finsetSum _ fun φ _ =>
    int_gramC_conj ha hA hC ψ φ x]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [integral_finsetSum _ fun φ _ => int_gramC_conj ha hA hC ψ φ x]
  rw [Finset.sum_eq_single ψ (fun φ _ hφ => integral_gramC_mul_conj hA hinv (Ne.symm hφ) x)
    (fun h => absurd (Finset.mem_univ ψ) h)]
  rw [← integral_complex_ofReal]
  congr 1; funext z
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Cauchy–Schwarz for a sector Gram kernel: `|G_ψ(x, z)|² ≤ d_ψ(x) d_ψ(z)`. -/
theorem norm_gramC_sq_le (ha : Bdd a) (hA : CentreAction μ act) (ψ : AddChar G ℂ) (x z : X) :
    ‖gramC μ a act ψ x z‖ ^ 2 ≤ secDiag μ a act ψ x * secDiag μ a act ψ z := by
  obtain ⟨C, hC0, hC⟩ := exists_bound ha
  set f : X → ℝ := fun y => ‖sec a act ψ x y‖
  set g : X → ℝ := fun y => ‖sec a act ψ z y‖
  have hfm : Measurable f := (measurable_sec_row ha hA ψ x).norm
  have hgm : Measurable g := (measurable_sec_row ha hA ψ z).norm
  have hfb : ∀ y, ‖f y‖ ≤ C := fun y => by
    simp only [f, norm_norm]; exact norm_sec_le hC ψ x y
  have hgb : ∀ y, ‖g y‖ ≤ C := fun y => by
    simp only [g, norm_norm]; exact norm_sec_le hC ψ z y
  have i1 : Integrable (fun y => f y ^ 2) μ := rint (hfm.pow_const 2) (C := C * C) fun y => by
    rw [norm_pow, sq]; exact mul_le_mul (hfb y) (hfb y) (norm_nonneg _) hC0
  have i2 : Integrable (fun y => g y ^ 2) μ := rint (hgm.pow_const 2) (C := C * C) fun y => by
    rw [norm_pow, sq]; exact mul_le_mul (hgb y) (hgb y) (norm_nonneg _) hC0
  have i3 : Integrable (fun y => f y * g y) μ := rint (hfm.mul hgm) (C := C * C) fun y => by
    rw [norm_mul]; exact mul_le_mul (hfb y) (hgb y) (norm_nonneg _) hC0
  have hcs := sq_integral_mul_le i1 i2 i3
  have hn : ‖gramC μ a act ψ x z‖ ≤ ∫ y, f y * g y ∂μ := by
    unfold gramC
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext y
    rw [norm_mul, Complex.norm_conj]
  have hp : 0 ≤ ‖gramC μ a act ψ x z‖ := norm_nonneg _
  calc ‖gramC μ a act ψ x z‖ ^ 2 ≤ (∫ y, f y * g y ∂μ) ^ 2 := pow_le_pow_left₀ hp hn 2
    _ ≤ _ := hcs

/-- **The doubled trace is at most the sum of the squared sector traces.** -/
theorem hs_conv_le_sum_sq (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) :
    hs μ (conv μ a a) ≤ ∑ ψ, sectorTrace μ a act ψ * sectorTrace μ a act ψ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound ha
  have hcb : Bdd (conv μ a a) := ha.conv ha
  obtain ⟨Cb, hCb⟩ := hcb.bdd
  have hin : ∀ x, ∫ z, conv μ a a x z ^ 2 ∂μ
      ≤ ∑ ψ, secDiag μ a act ψ x * sectorTrace μ a act ψ := by
    intro x
    rw [integral_conv_sq ha hsym hA hinv x]
    refine Finset.sum_le_sum fun ψ _ => ?_
    unfold sectorTrace
    rw [← integral_const_mul]
    have iL : Integrable (fun z => ‖gramC μ a act ψ x z‖ ^ 2) μ :=
      rint ((measurable_gramC_row ha hA ψ x).norm.pow_const 2) (C := C * C * (C * C)) fun z => by
        rw [norm_pow, norm_norm, sq]
        exact mul_le_mul (norm_gramC_le hC ψ x z) (norm_gramC_le hC ψ x z) (norm_nonneg _)
          (mul_nonneg hC0 hC0)
    exact integral_mono iL ((int_secDiag ha hA hC ψ).const_mul _)
      fun z => norm_gramC_sq_le ha hA ψ x z
  have iR : Integrable (fun x => ∑ ψ, secDiag μ a act ψ x * sectorTrace μ a act ψ) μ :=
    integrable_finsetSum _ fun ψ _ => (int_secDiag ha hA hC ψ).mul_const _
  have iL : Integrable (fun x => ∫ z, conv μ a a x z ^ 2 ∂μ) μ := by
    refine rint (measurable_integral_right (hcb.meas.pow_const 2)) (C := Cb * Cb) fun x => ?_
    rw [Real.norm_eq_abs]
    refine abs_integral_le fun z => ?_
    rw [abs_of_nonneg (sq_nonneg _), sq]
    have := hCb x z
    nlinarith [abs_nonneg (conv μ a a x z), sq_abs (conv μ a a x z)]
  unfold hs
  calc ∫ x, ∫ z, conv μ a a x z ^ 2 ∂μ ∂μ
      ≤ ∫ x, ∑ ψ, secDiag μ a act ψ x * sectorTrace μ a act ψ ∂μ := integral_mono iL iR hin
    _ = ∑ ψ, sectorTrace μ a act ψ * sectorTrace μ a act ψ := by
        rw [integral_finsetSum _ fun ψ _ => (int_secDiag ha hA hC ψ).mul_const _]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [integral_mul_const]; rfl

/-- **The sector traces add up to the trace.** -/
theorem sum_sectorTrace (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act) :
    ∑ ψ, sectorTrace μ a act ψ = hs μ a := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  have hx : ∀ x, ∑ ψ, secDiag μ a act ψ x = ∫ y, a x y ^ 2 ∂μ := by
    intro x
    have h1 := conv_eq_sum_gram ha hsym hA x x
    simp_rw [gramC_diag] at h1
    rw [← Complex.ofReal_sum] at h1
    have h2 := (Complex.ofReal_injective h1).symm
    rw [h2]
    unfold conv
    congr 1; funext y; rw [hsym y x, sq]
  unfold sectorTrace hs
  rw [← integral_finsetSum _ fun ψ _ => int_secDiag ha hA hC ψ]
  congr 1; funext x; exact hx x

/-- **For `a ≥ 0`, every sector trace is at most the average twisted trace.** -/
theorem sectorTrace_le (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y) (hA : CentreAction μ act)
    (ψ : AddChar G ℂ) :
    sectorTrace μ a act ψ
      ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound ha
  set r : G → X → ℝ := fun g x => ∫ y, a x y * a x (act g y) ∂μ with hr
  have hrm : ∀ g, Measurable (r g) := fun g =>
    measurable_integral_right (F := fun x y => a x y * a x (act g y))
      (ha.meas.mul (ha.meas.comp (measurable_fst.prodMk ((hA.meas g).comp measurable_snd))))
  have hrb : ∀ g x, ‖r g x‖ ≤ C * C := fun g x => by
    refine norm_integral_le_const fun y => ?_
    rw [norm_mul]; exact mul_le_mul (hC x y) (hC x _) (norm_nonneg _) hC0
  have hr0 : ∀ g x, 0 ≤ r g x := fun g x =>
    integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _)
  have hpt : ∀ x, secDiag μ a act ψ x ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, r g x := by
    intro x
    have h1 := integral_a_mul_conj_sec ha hA ψ x x
    rw [gramC_diag] at h1
    have e : ∀ y, (a x y : ℂ) * conj (sec a act ψ x y)
        = (Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ψ g) * ((a x y * a x (act g y) : ℝ) : ℂ) := by
      intro y
      unfold sec
      rw [map_mul, map_inv₀, map_natCast, map_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
    simp_rw [e] at h1
    rw [integral_const_mul, integral_finsetSum _ fun g _ => ?_] at h1
    · have h2 : ∀ g, ∫ y, conj (ψ g) * ((a x y * a x (act g y) : ℝ) : ℂ) ∂μ
          = conj (ψ g) * (r g x : ℂ) := by
        intro g; rw [integral_const_mul, integral_complex_ofReal]
      simp_rw [h2] at h1
      have h3 : ‖(secDiag μ a act ψ x : ℂ)‖ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, r g x := by
        rw [← h1, norm_mul, norm_inv, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr card_pos_real.le)
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun g _ => ?_))
        rw [norm_mul, Complex.norm_conj, norm_char, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hr0 g x)]
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (secDiag_nonneg ψ x)] at h3
    · have hm : Measurable (fun y => a x y * a x (act g y)) :=
        (ha.row x).mul ((ha.row x).comp (hA.meas g))
      refine cint (measurable_const.mul (Complex.measurable_ofReal.comp hm)) (C := C * C)
        fun y => ?_
      rw [norm_mul, Complex.norm_conj, norm_char, one_mul, Complex.norm_real, norm_mul]
      exact mul_le_mul (hC x y) (hC x _) (norm_nonneg _) hC0
  have iR : Integrable (fun x => (Fintype.card G : ℝ)⁻¹ * ∑ g, r g x) μ :=
    (integrable_finsetSum _ fun g _ => rint (hrm g) (hrb g)).const_mul _
  unfold sectorTrace
  calc ∫ x, secDiag μ a act ψ x ∂μ ≤ ∫ x, (Fintype.card G : ℝ)⁻¹ * ∑ g, r g x ∂μ :=
        integral_mono (int_secDiag ha hA hC ψ) iR hpt
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun g _ => rint (hrm g) (hrb g)]
        rfl

/-- **The doubled trace is at most the trace times the average twisted trace**, for `a ≥ 0`. -/
theorem hs_conv_le_mul_avg_twist (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y)
    (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) :
    hs μ (conv μ a a)
      ≤ hs μ a * ((Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g)) := by
  set τ := (Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g)
  calc hs μ (conv μ a a) ≤ ∑ ψ, sectorTrace μ a act ψ * sectorTrace μ a act ψ :=
        hs_conv_le_sum_sq ha hsym hA hinv
    _ ≤ ∑ ψ, sectorTrace μ a act ψ * τ := Finset.sum_le_sum fun ψ _ =>
        mul_le_mul_of_nonneg_left (sectorTrace_le ha ha0 hA ψ) (sectorTrace_nonneg ψ)
    _ = hs μ a * τ := by rw [← Finset.sum_mul, sum_sectorTrace ha hsym hA]

/-! ## Suppressed twisted rows -/

theorem bdd_act (ha : Bdd a) (hA : CentreAction μ act) (g : G) :
    Bdd (fun x y => a x (act g y)) := by
  obtain ⟨C, hC⟩ := ha.bdd
  exact ⟨ha.meas.comp (measurable_fst.prodMk ((hA.meas g).comp measurable_snd)), C,
    fun x y => hC x (act g y)⟩

/-- **One twisted row.** If `a(x,y) a(x, gy) ≤ ε + χ(y)(a(x,y)² + a(x,gy)²)/2` pointwise, with
`0 ≤ χ ≤ 1` measurable and invariant under `act g`, then
`∫ a(x,y) a(x, gy) dy ≤ ε + ∫ χ(y) a(x,y)² dy`. -/
theorem row_twist_le (ha : Bdd a) (hA : CentreAction μ act) (g : G) {χ : X → ℝ}
    (hχ : Measurable χ) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hχσ : ∀ y, χ (act g y) = χ y) {ε : ℝ}
    (h : ∀ x y, a x y * a x (act g y) ≤ ε + χ y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2))
    (x : X) :
    ∫ y, a x y * a x (act g y) ∂μ ≤ ε + ∫ y, χ y * a x y ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := ha.bdd
  have hσ := bdd_act ha hA g
  have bχa : Bdd (fun x y => χ y * a x y ^ 2) := by
    refine ⟨(hχ.comp measurable_snd).mul (ha.meas.pow_const 2), C ^ 2, fun x y => ?_⟩
    rw [abs_mul, abs_of_nonneg (hχb y).1, abs_of_nonneg (sq_nonneg _)]
    have h1 : a x y ^ 2 ≤ C ^ 2 := by
      have := hC x y; nlinarith [abs_nonneg (a x y), sq_abs (a x y)]
    nlinarith [(hχb y).1, (hχb y).2, sq_nonneg (a x y)]
  have bχaσ : Bdd (fun x y => χ y * a x (act g y) ^ 2) := by
    refine ⟨(hχ.comp measurable_snd).mul (hσ.meas.pow_const 2), C ^ 2, fun x y => ?_⟩
    rw [abs_mul, abs_of_nonneg (hχb y).1, abs_of_nonneg (sq_nonneg _)]
    have h1 : a x (act g y) ^ 2 ≤ C ^ 2 := by
      have := hC x (act g y); nlinarith [abs_nonneg (a x (act g y)), sq_abs (a x (act g y))]
    nlinarith [(hχb y).1, (hχb y).2, sq_nonneg (a x (act g y))]
  have e : (fun y => ε + χ y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2))
      = fun y => ε + ((χ y * a x y ^ 2) / 2 + (χ y * a x (act g y) ^ 2) / 2) := by
    funext y; ring
  have i1 : Integrable (fun y => χ y * a x y ^ 2 / 2) μ :=
    (FluxSectorBound.irow bχa x).div_const 2
  have i2 : Integrable (fun y => χ y * a x (act g y) ^ 2 / 2) μ :=
    (FluxSectorBound.irow bχaσ x).div_const 2
  have i12 : Integrable (fun y => χ y * a x y ^ 2 / 2 + χ y * a x (act g y) ^ 2 / 2) μ := i1.add i2
  have iR : Integrable (fun y => ε + χ y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2)) μ := by
    rw [e]; exact (integrable_const ε).add i12
  have hle : ∫ y, a x y * a x (act g y) ∂μ
      ≤ ∫ y, ε + χ y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2) ∂μ :=
    integral_mono (FluxSectorBound.bdd_rows ha hσ x x) iR (fun y => h x y)
  have hflip : ∫ y, χ y * a x (act g y) ^ 2 ∂μ = ∫ y, χ y * a x y ^ 2 ∂μ := by
    have := hA.integral_comp g (fun y => χ y * a x y ^ 2)
    simp only [hχσ] at this
    exact this
  have e2 : ∫ y, ε + χ y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2) ∂μ
      = ε + ((∫ y, χ y * a x y ^ 2 ∂μ) / 2 + (∫ y, χ y * a x (act g y) ^ 2 ∂μ) / 2) := by
    rw [e, integral_add (integrable_const ε) i12, integral_add i1 i2, integral_const,
      integral_div, integral_div]
    simp
  rw [e2, hflip] at hle
  linarith

/-- **The twisted traces sum to at most half the group times the trace**, up to the suppressed rows
and the small overlap. -/
theorem twist_sum_le (ha : Bdd a) (hA : CentreAction μ act) {χ : G → X → ℝ}
    (hχ : ∀ g, Measurable (χ g)) (hχb : ∀ g y, 0 ≤ χ g y ∧ χ g y ≤ 1)
    (hχσ : ∀ g y, χ g (act g y) = χ g y) {ε η : ℝ}
    (h1 : ∀ g x y, a x y * a x (act g y) ≤ ε + χ g y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2))
    (h3 : ∀ x y, (∑ g, χ g y) * a x y ^ 2
      ≤ (Fintype.card G : ℝ) / 2 * a x y ^ 2 + Fintype.card G * η) :
    ∑ g, FluxSectorBound.twist μ a (act g)
      ≤ Fintype.card G * ε + (Fintype.card G : ℝ) / 2 * hs μ a + Fintype.card G * η := by
  obtain ⟨C, hC0, hC⟩ := exists_bound ha
  have bsq : Bdd (fun x y => a x y ^ 2) := by
    have := FluxSectorBound.bdd_mul ha ha; simpa [sq] using this
  have bχ : ∀ g, Bdd (fun x y => χ g y * a x y ^ 2) := fun g =>
    FluxSectorBound.bdd_mul ⟨(hχ g).comp measurable_snd, 1, fun x y => by
      rw [abs_of_nonneg (hχb g y).1]; exact (hχb g y).2⟩ bsq
  set r : G → X → ℝ := fun g x => ∫ y, a x y * a x (act g y) ∂μ with hr
  have hrm : ∀ g, Measurable (r g) := fun g =>
    measurable_integral_right (FluxSectorBound.bdd_mul ha (bdd_act ha hA g)).meas
  have hrb : ∀ g x, ‖r g x‖ ≤ C * C := fun g x => by
    refine norm_integral_le_const fun y => ?_
    rw [norm_mul]; exact mul_le_mul (hC x y) (hC x _) (norm_nonneg _) hC0
  have hx : ∀ x, ∑ g, r g x
      ≤ Fintype.card G * ε + (Fintype.card G : ℝ) / 2 * ∫ y, a x y ^ 2 ∂μ
        + Fintype.card G * η := by
    intro x
    have hrow : ∀ g, r g x ≤ ε + ∫ y, χ g y * a x y ^ 2 ∂μ := fun g =>
      row_twist_le ha hA g (hχ g) (hχb g) (hχσ g) (h1 g) x
    have hsum : ∑ g, ∫ y, χ g y * a x y ^ 2 ∂μ
        ≤ (Fintype.card G : ℝ) / 2 * ∫ y, a x y ^ 2 ∂μ + Fintype.card G * η := by
      rw [← integral_finsetSum _ fun g _ => FluxSectorBound.irow (bχ g) x]
      have i3 : Integrable (fun y => (Fintype.card G : ℝ) / 2 * a x y ^ 2
          + Fintype.card G * η) μ :=
        ((FluxSectorBound.irow bsq x).const_mul _).add (integrable_const _)
      calc ∫ y, ∑ g, χ g y * a x y ^ 2 ∂μ
          ≤ ∫ y, ((Fintype.card G : ℝ) / 2 * a x y ^ 2 + Fintype.card G * η) ∂μ :=
            integral_mono (integrable_finsetSum _ fun g _ => FluxSectorBound.irow (bχ g) x) i3
              (fun y => by rw [← Finset.sum_mul]; exact h3 x y)
        _ = (Fintype.card G : ℝ) / 2 * ∫ y, a x y ^ 2 ∂μ + Fintype.card G * η := by
            rw [integral_add ((FluxSectorBound.irow bsq x).const_mul _) (integrable_const _),
              integral_const_mul, integral_const]
            simp
    calc ∑ g, r g x ≤ ∑ g, (ε + ∫ y, χ g y * a x y ^ 2 ∂μ) := Finset.sum_le_sum fun g _ => hrow g
      _ = Fintype.card G * ε + ∑ g, ∫ y, χ g y * a x y ^ 2 ∂μ := by
          rw [Finset.sum_add_distrib]; simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by linarith
  have i0 : Integrable (fun x => ∫ y, a x y ^ 2 ∂μ) μ :=
    rint (measurable_integral_right bsq.meas) (C := C * C) fun x => by
      refine norm_integral_le_const fun y => ?_
      rw [norm_pow, sq]; exact mul_le_mul (hC x y) (hC x y) (norm_nonneg _) hC0
  have iL : Integrable (fun x => ∑ g, r g x) μ :=
    integrable_finsetSum _ fun g _ => rint (hrm g) (hrb g)
  have iA : Integrable (fun x => Fintype.card G * ε + (Fintype.card G : ℝ) / 2
      * ∫ y, a x y ^ 2 ∂μ) μ := (integrable_const _).add (i0.const_mul _)
  have iR : Integrable (fun x => Fintype.card G * ε + (Fintype.card G : ℝ) / 2
      * ∫ y, a x y ^ 2 ∂μ + Fintype.card G * η) μ := iA.add (integrable_const _)
  have hT : ∑ g, FluxSectorBound.twist μ a (act g) = ∫ x, ∑ g, r g x ∂μ := by
    rw [integral_finsetSum _ fun g _ => rint (hrm g) (hrb g)]; rfl
  rw [hT]
  calc ∫ x, ∑ g, r g x ∂μ
      ≤ ∫ x, (Fintype.card G * ε + (Fintype.card G : ℝ) / 2 * ∫ y, a x y ^ 2 ∂μ
          + Fintype.card G * η) ∂μ := integral_mono iL iR hx
    _ = _ := by
        rw [integral_add iA (integrable_const _),
          integral_add (integrable_const _) (i0.const_mul _),
          integral_const_mul ((Fintype.card G : ℝ) / 2) (fun x => ∫ y, a x y ^ 2 ∂μ),
          integral_const, integral_const]
        simp [hs]

/-- **The doubled trace drops to three quarters of the squared trace.** For a nonnegative
symmetric kernel invariant under the action, with suppressed twisted rows off the weights, weights
summing to at most `|G|/2` up to `η`, and `ε + η ≤ hs(a)/4`: `hs(a ∗ a) ≤ (3/4) hs(a)²`. -/
theorem hs_conv_le_three_quarters (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y)
    (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (hinv : ∀ g x y, a (act g x) (act g y) = a x y) {χ : G → X → ℝ}
    (hχ : ∀ g, Measurable (χ g)) (hχb : ∀ g y, 0 ≤ χ g y ∧ χ g y ≤ 1)
    (hχσ : ∀ g y, χ g (act g y) = χ g y) {ε η : ℝ}
    (h1 : ∀ g x y, a x y * a x (act g y) ≤ ε + χ g y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2))
    (h3 : ∀ x y, (∑ g, χ g y) * a x y ^ 2
      ≤ (Fintype.card G : ℝ) / 2 * a x y ^ 2 + Fintype.card G * η)
    (hsmall : ε + η ≤ hs μ a / 4) :
    hs μ (conv μ a a) ≤ 3 / 4 * hs μ a ^ 2 := by
  have hT := twist_sum_le ha hA hχ hχb hχσ h1 h3
  have hmain := hs_conv_le_mul_avg_twist ha ha0 hsym hA hinv
  have hG := card_pos_real (G := G)
  have hτ : (Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g)
      ≤ ε + hs μ a / 2 + η := by
    rw [inv_mul_le_iff₀ hG]
    linarith
  have hh := hs_nonneg (μ := μ) a
  calc hs μ (conv μ a a)
      ≤ hs μ a * ((Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (act g)) := hmain
    _ ≤ hs μ a * (3 / 4 * hs μ a) :=
        mul_le_mul_of_nonneg_left (by linarith) hh
    _ = 3 / 4 * hs μ a ^ 2 := by ring

end MassGap.FluxSectorFourier

#print axioms MassGap.FluxSectorFourier.sum_sec
#print axioms MassGap.FluxSectorFourier.integral_sec_mul_conj
#print axioms MassGap.FluxSectorFourier.conv_eq_sum_gram
#print axioms MassGap.FluxSectorFourier.integral_conv_sq
#print axioms MassGap.FluxSectorFourier.hs_conv_le_sum_sq
#print axioms MassGap.FluxSectorFourier.sum_sectorTrace
#print axioms MassGap.FluxSectorFourier.sectorTrace_le
#print axioms MassGap.FluxSectorFourier.hs_conv_le_mul_avg_twist
#print axioms MassGap.FluxSectorFourier.twist_sum_le
#print axioms MassGap.FluxSectorFourier.hs_conv_le_three_quarters
