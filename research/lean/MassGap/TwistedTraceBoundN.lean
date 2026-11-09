import Mathlib
import MassGap.TwistedTraceBound
import MassGap.FluxSectorFourier

/-!
# MassGap.TwistedTraceBoundN — the centre action of `Z_N × Z_N` on a slice and the kernel bounds

These are the `SU(N)` pieces, for every `N ≥ 2`, with the full centre `Z_N` in place of `−1`. The weak-coupling
bound on a fixed torus, that the doubling defect stays above `1/1000`, is `deltaLengthUnbounded` in
`TwistedTraceBoundFull`.

Fix the torus of side `n = m + 1 = 2j` and the transfer in direction `0`, a kernel on the
configurations of one spatial slice.

**The centre action.** `G = Z_N × Z_N` acts on a slice: `g = (g₁, g₂)` multiplies every link in
spatial direction `1` whose `1`-coordinate is `0` by `e(g₁) = exp(2πi g₁/N)`, and every link in
direction `2` whose `2`-coordinate is `0` by `e(g₂)`. It preserves Haar measure and the transfer
kernel (`kT_act`), since a spatial plaquette meets the flipped links of each direction in two
opposite links or none (`plaq_phase`), and a temporal plaquette meets them in its two spatial links.
`centreAction` packages it as a `FluxSectorFourier.CentreAction`.

Also here: bounds on the transfer kernel `kT` from the temporal action (`kT_le_gk`, `gk_le_of_tp`,
`kT_le_of_lip`), the spatial-action bound (`kT_le_sp`), and the smallest phase jump
`κ = min_{c ≠ 0} |1 − e(c)|` (`exists_phase_gap`).

DERIVED (module-wide): `0` is the time direction and the flipped coordinate; `1`, `2` name the two
spatial directions.
-/

noncomputable section

namespace MassGap.TwistedTraceBoundN

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower
open MassGap.TwistedTraceBound (D d1 d2 d2_ne_d1 Tn Site step pos org step_self step_ne pos_succ
  pos_val pos_ne pos_period step_comm pos_step_comm iter_bounds iter_offdiag iter_le_sp exp_dec
  ZR_lower)

/-- Slice configurations. -/
abbrev Cfg (m N : ℕ) : Type := SpT 0 (Tn m) → SUN.SU N

/-- `e(k) = exp(2πik/N)`. -/
local notation "ee" => ZMod.stdAddChar

/-- The weight of a set: `1` on it, `0` off it. -/
def chi {X : Type*} (S : Set X) : X → ℝ := S.indicator (fun _ => 1)

theorem chi_of_mem {X : Type*} {S : Set X} {y : X} (h : y ∈ S) : chi S y = 1 := by
  unfold chi; rw [Set.indicator_of_mem h]

theorem chi_of_not_mem {X : Type*} {S : Set X} {y : X} (h : y ∉ S) : chi S y = 0 := by
  unfold chi; rw [Set.indicator_of_notMem h]

/-! ## 1. Matrix facts -/

section Matrices

variable {N : ℕ}

theorem coeU (g : SUN.SU N) :
    ((g : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1

theorem coe_inv (g : SUN.SU N) :
    ((g⁻¹ : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = star (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem wd_congr {g h : SUN.SU N}
    (e : (g : Matrix (Fin N) (Fin N) ℂ) = (h : Matrix (Fin N) (Fin N) ℂ)) :
    WilsonAction.wilsonDensity g = WilsonAction.wilsonDensity h := by
  unfold WilsonAction.wilsonDensity; rw [e]

theorem smul_plaq (ea eb ec ed : ℂ) (A B C E : Matrix (Fin N) (Fin N) ℂ) :
    (ea • A) * (eb • B) * star (ec • C) * star (ed • E)
      = (ea * eb * star ec * star ed) • (A * B * star C * star E) := by
  rw [star_smul, star_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1; ring

theorem smul_plaq_time (c : ℂ) (A B C E : Matrix (Fin N) (Fin N) ℂ) :
    A * (c • B) * star C * star (c • E) = (c * star c) • (A * B * star C * star E) := by
  rw [star_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1; ring

theorem star_conj (A X : Matrix (Fin N) (Fin N) ℂ) : star (A * X * star A) = A * star X * star A := by
  rw [star_mul, star_mul, star_star, Matrix.mul_assoc]

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup


theorem norm_star_sub_star (U V : Matrix (Fin N) (Fin N) ℂ) : ‖star U - star V‖ = ‖U - V‖ := by
  rw [← star_sub]
  exact Matrix.frobenius_norm_conjTranspose (U - V)

end Frob

end Matrices

/-! ## 2. The centre of SU(N) and its action on a slice -/

section Centre

variable {N : ℕ} [NeZero N]


theorem norm_ee (k : ZMod N) : ‖ee k‖ = 1 := AddChar.norm_apply _ k

theorem ee_mul_star (k : ZMod N) : ee k * star (ee k) = 1 := by
  have h := Complex.mul_conj (ee k)
  rw [Complex.normSq_eq_norm_sq, norm_ee] at h
  simpa using h

theorem star_ee (k : ZMod N) : star (ee k) = ee (-k) := by
  rw [AddChar.map_neg_eq_conj]; rfl

theorem ee_pow (k : ZMod N) (n : ℕ) : ee k ^ n = ee (n • k) :=
  (AddChar.map_nsmul_eq_pow _ n k).symm

/-- **The centre element** `e(k) · 1` of `SU(N)`. -/
def cz (k : ZMod N) : SUN.SU N :=
  ⟨ee k • (1 : Matrix (Fin N) (Fin N) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, Matrix.one_mul,
        ee_mul_star, one_smul]
    · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ee_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul]
      exact AddChar.map_zero_eq_one _⟩

theorem coe_cz (k : ZMod N) :
    ((cz k : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = ee k • (1 : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem cz_add (a b : ZMod N) : cz (a + b) = cz a * cz b := by
  apply Subtype.ext
  show ee (a + b) • (1 : Matrix (Fin N) (Fin N) ℂ)
    = (ee a • (1 : Matrix (Fin N) (Fin N) ℂ)) * (ee b • (1 : Matrix (Fin N) (Fin N) ℂ))
  rw [smul_mul_smul_comm, Matrix.one_mul, AddChar.map_add_eq_mul]

theorem cz_zero : cz (0 : ZMod N) = 1 := by
  apply Subtype.ext
  show ee (0 : ZMod N) • (1 : Matrix (Fin N) (Fin N) ℂ) = 1
  rw [AddChar.map_zero_eq_one, one_smul]

variable {m : ℕ}

/-- The phase of direction `ν` under `g`. -/
def ph (g : ZMod N × ZMod N) (ν : D) : ZMod N :=
  if ν = d1 then g.1 else if ν = d2 then g.2 else 0

/-- The charge carried by a link: the phase of its direction if its own coordinate is `0`. -/
def lc (g : ZMod N × ZMod N) (l : SpT 0 (Tn m)) : ZMod N :=
  if (l.2 l.1).val = 0 then ph g l.1 else 0

theorem ph_add (g h : ZMod N × ZMod N) (ν : D) : ph (g + h) ν = ph g ν + ph h ν := by
  unfold ph; split_ifs <;> simp

theorem lc_add (g h : ZMod N × ZMod N) (l : SpT 0 (Tn m)) : lc (g + h) l = lc g l + lc h l := by
  unfold lc; split_ifs <;> simp [ph_add]

theorem lc_zero (l : SpT 0 (Tn m)) : lc (0 : ZMod N × ZMod N) l = 0 := by
  unfold lc ph; split_ifs <;> simp

theorem ph_d1 (g : ZMod N × ZMod N) : ph g d1 = g.1 := by simp [ph]

theorem ph_d2 (g : ZMod N × ZMod N) : ph g d2 = g.2 := by simp [ph, d2_ne_d1]

theorem lc_step {ν ν' : D} (h : ν ≠ ν') (g : ZMod N × ZMod N) (y : Site m) :
    lc g (ν, step ν' y) = lc g (ν, y) := by
  simp only [lc, step_ne h]

/-- **The centre action** of `Z_N × Z_N` on slice configurations. -/
def act (g : ZMod N × ZMod N) (V : Cfg m N) : Cfg m N := fun l => cz (lc g l) * V l

theorem coe_act (g : ZMod N × ZMod N) (V : Cfg m N) (l : SpT 0 (Tn m)) :
    ((act g V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = ee (lc g l) • ((V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  show ((cz (lc g l) * V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = _
  rw [Submonoid.coe_mul, coe_cz, smul_mul_assoc, Matrix.one_mul]

/-- The phases around a spatial plaquette cancel. -/
theorem plaq_phase (g : ZMod N × ZMod N) (νa νb : D) (y : Site m) :
    ee (lc g (νa, y)) * ee (lc g (νb, step νa y)) * star (ee (lc g (νa, step νb y)))
      * star (ee (lc g (νb, y))) = 1 := by
  by_cases hab : νa = νb
  · subst hab
    calc ee (lc g (νa, y)) * ee (lc g (νa, step νa y)) * star (ee (lc g (νa, step νa y)))
          * star (ee (lc g (νa, y)))
        = (ee (lc g (νa, y)) * star (ee (lc g (νa, y))))
          * (ee (lc g (νa, step νa y)) * star (ee (lc g (νa, step νa y)))) := by ring
      _ = 1 := by rw [ee_mul_star, ee_mul_star, one_mul]
  · rw [lc_step (Ne.symm hab), lc_step hab]
    calc ee (lc g (νa, y)) * ee (lc g (νb, y)) * star (ee (lc g (νa, y))) * star (ee (lc g (νb, y)))
        = (ee (lc g (νa, y)) * star (ee (lc g (νa, y))))
          * (ee (lc g (νb, y)) * star (ee (lc g (νb, y)))) := by ring
      _ = 1 := by rw [ee_mul_star, ee_mul_star, one_mul]

theorem sp_act (g : ZMod N × ZMod N) (V : Cfg m N) : spT 0 (Tn m) (act g V) = spT 0 (Tn m) V := by
  unfold spT
  refine Finset.sum_congr rfl fun νa _ => Finset.sum_congr rfl fun νb _ =>
    Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_act]
  rw [smul_plaq, plaq_phase, one_smul]

theorem tp_act (g : ZMod N × ZMod N) (A : TT 0 (Tn m) → SUN.SU N) (V V' : Cfg m N) :
    tpT 0 (Tn m) A (act g V) (act g V') = tpT 0 (Tn m) A V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun νb _ => Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_act]
  rw [smul_plaq_time, ee_mul_star, one_smul]

theorem gk_act (g : ZMod N × ZMod N) (β : ℝ) (V V' : Cfg m N) :
    gk 0 (Tn m) N β (act g V) (act g V') = gk 0 (Tn m) N β V V' := by
  unfold gk
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [tp_act]

theorem kT_act (g : ZMod N × ZMod N) (β : ℝ) (V V' : Cfg m N) :
    kT 0 (Tn m) N β (act g V) (act g V') = kT 0 (Tn m) N β V V' := by
  unfold kT; rw [sp_act, sp_act, gk_act]

theorem mp_act (g : ZMod N × ZMod N) :
    MeasurePreserving (act (m := m) g) (hS 0 (Tn m) N) (hS 0 (Tn m) N) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU N)) (fun _ => probHaar (SUN.SU N))
    (fun l => measurePreserving_mul_left (probHaar (SUN.SU N)) (cz (lc g l)))

/-- **The centre action is a measure-preserving action of `Z_N × Z_N`.** -/
theorem centreAction :
    FluxSectorFourier.CentreAction (hS 0 (Tn m) N) (act (m := m) (N := N)) where
  meas g := (mp_act g).measurable
  zero V := funext fun l => by simp only [act, lc_zero, cz_zero, one_mul]
  add g h V := funext fun l => by simp only [act, lc_add, cz_add, mul_assoc]
  mp := mp_act

end Centre

/-! ## 3. Kernel iterates under the action -/

theorem iter_inv_act {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {act : G → X → X}
    (hA : FluxSectorFourier.CentreAction μ act)
    {k : X → X → ℝ} (hk : ∀ g x y, k (act g x) (act g y) = k x y) :
    ∀ i g x y, iter μ k i (act g x) (act g y) = iter μ k i x y
  | 0, g, x, y => hk g x y
  | i + 1, g, x, y => by
    change ∫ z, k (act g x) z * iter μ k i z (act g y) ∂μ = ∫ z, k x z * iter μ k i z y ∂μ
    rw [← hA.integral_comp g (fun z => k (act g x) z * iter μ k i z (act g y))]
    congr 1; funext z
    rw [hk, iter_inv_act hA hk i g z y]

/-! ## 4. Kernel bounds -/

section Kernel

variable {N m : ℕ}

theorem gk_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m N) :
    0 ≤ gk 0 (Tn m) N β V V' :=
  (Real.exp_pos _).le.trans (gk_ge hN hβ V V')

theorem kT_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m N) :
    0 ≤ kT 0 (Tn m) N β V V' :=
  (kTmin_pos β).le.trans (kT_lower hN hβ V V')

theorem kT_le_gk (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m N) :
    kT 0 (Tn m) N β V V' ≤ gk 0 (Tn m) N β V V' := by
  unfold kT
  have h1 : Real.exp (-β * spT 0 (Tn m) V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg hN V; nlinarith
  have h2 : Real.exp (-β * spT 0 (Tn m) V' / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg hN V'; nlinarith
  have h0 := gk_nonneg hN hβ V V'
  calc Real.exp (-β * spT 0 (Tn m) V / 2) * gk 0 (Tn m) N β V V'
        * Real.exp (-β * spT 0 (Tn m) V' / 2)
      ≤ 1 * gk 0 (Tn m) N β V V' * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h0) h2 (Real.exp_pos _).le
        exact mul_nonneg zero_le_one h0
    _ = gk 0 (Tn m) N β V V' := by ring

theorem kT_le_sp (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m N) :
    kT 0 (Tn m) N β V V' ≤ Real.exp (-β * spT 0 (Tn m) V' / 2) := by
  unfold kT
  have h1 : Real.exp (-β * spT 0 (Tn m) V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg hN V; nlinarith
  have h0 := gk_nonneg hN hβ V V'
  have h3 := gk_le_one hN hβ V V'
  calc Real.exp (-β * spT 0 (Tn m) V / 2) * gk 0 (Tn m) N β V V'
        * Real.exp (-β * spT 0 (Tn m) V' / 2)
      ≤ 1 * 1 * Real.exp (-β * spT 0 (Tn m) V' / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul h1 h3 h0 zero_le_one
    _ = _ := by ring

theorem gk_le_of_tp (hN : N ≠ 0) {β s : ℝ} (hβ : 0 ≤ β) {V V' : Cfg m N}
    (h : ∀ A, s ≤ tpT 0 (Tn m) A V V') : gk 0 (Tn m) N β V V' ≤ Real.exp (-2 * β * s) := by
  unfold gk
  have hm : Measurable fun A : TT 0 (Tn m) → SUN.SU N =>
      Real.exp (-β * (2 * tpT 0 (Tn m) A V V')) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tp continuous_id continuous_const continuous_const)))).measurable
  have hb : ∀ A : TT 0 (Tn m) → SUN.SU N, |Real.exp (-β * (2 * tpT 0 (Tn m) A V V'))| ≤ 1 := by
    intro A
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := tp_nonneg hN A V V'; nlinarith
  calc ∫ A, Real.exp (-β * (2 * tpT 0 (Tn m) A V V')) ∂(hA 0 (Tn m) N)
      ≤ ∫ _A, Real.exp (-2 * β * s) ∂(hA 0 (Tn m) N) :=
        integral_mono (integrable_of_bdd hm hb) (integrable_const _) fun A => by
          rw [Real.exp_le_exp]; have := h A; nlinarith
    _ = Real.exp (-2 * β * s) := by simp

/-- The kernel bound from a Lipschitz observable. -/
theorem kT_le_of_lip (hN : N ≠ 0) {g : Cfg m N → ℂ} {L β : ℝ} (hL : 0 < L) (hβ : 0 ≤ β)
    (hlip : ∀ A V V', ‖g V - g V'‖ ≤ L * Real.sqrt (tpT 0 (Tn m) A V V')) (V V' : Cfg m N) :
    kT 0 (Tn m) N β V V' ≤ Real.exp (-2 * β * (‖g V - g V'‖ / L) ^ 2) := by
  refine (kT_le_gk hN hβ V V').trans (gk_le_of_tp hN (s := (‖g V - g V'‖ / L) ^ 2) hβ fun A => ?_)
  have h := hlip A V V'
  have hs : ‖g V - g V'‖ / L ≤ Real.sqrt (tpT 0 (Tn m) A V V') := by
    rw [div_le_iff₀ hL]; linarith
  have := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hL.le) hs 2
  rwa [Real.sq_sqrt (tp_nonneg hN A V V')] at this

end Kernel

/-! ## 5. Holonomies and words -/

section Holonomy

variable {N m : ℕ}

end Holonomy

section Charge

variable {N m : ℕ} [NeZero N]

theorem natCast_fin_inj {a b : Fin N} (h : ((a : ℕ) : ZMod N) = ((b : ℕ) : ZMod N)) : a = b := by
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
  exact Fin.ext this

/-- The smallest jump `|1 − e(c)|` over the nonzero `c`. -/
theorem exists_phase_gap : ∃ κ : ℝ, 0 < κ ∧ ∀ c : ZMod N, c ≠ 0 → κ ≤ ‖1 - ee c‖ := by
  classical
  set s := (Finset.univ : Finset (ZMod N)).filter (fun c => c ≠ 0)
  rcases s.eq_empty_or_nonempty with hs | hs
  · refine ⟨1, one_pos, fun c hc => ?_⟩
    have : c ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    rw [hs] at this
    exact absurd this (Finset.notMem_empty _)
  · obtain ⟨c₀, hc₀, hmin⟩ := s.exists_min_image (fun c => ‖1 - ee c‖) hs
    refine ⟨‖1 - ee c₀‖, ?_, fun c hc => hmin c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have h1 : ZMod.stdAddChar c₀ = ZMod.stdAddChar (0 : ZMod N) := by
      rw [AddChar.map_zero_eq_one]; exact h.symm
    exact (Finset.mem_filter.mp hc₀).2 (ZMod.injective_stdAddChar h1)

end Charge

/-! ## 6. The ladders -/

section Ladders

attribute [local instance] Matrix.frobeniusNormedAddCommGroup


variable {N m : ℕ}

theorem wd_le_tp (hN : N ≠ 0) (A : TT 0 (Tn m) → SUN.SU N) (V V' : Cfg m N) (ν : D) (y : Site m) :
    WilsonAction.wilsonDensity (A y * V' (ν, y) * (A (tsh 0 (Tn m) ν y))⁻¹ * (V (ν, y))⁻¹)
      ≤ tpT 0 (Tn m) A V V' := by
  unfold tpT
  have hnn : ∀ ν y, 0 ≤ WilsonAction.wilsonDensity
      (A y * V' (ν, y) * (A (tsh 0 (Tn m) ν y))⁻¹ * (V (ν, y))⁻¹) :=
    fun _ _ => WilsonAction.wilsonDensity_nonneg hN _
  calc _ ≤ ∑ y', WilsonAction.wilsonDensity
        (A y' * V' (ν, y') * (A (tsh 0 (Tn m) ν y'))⁻¹ * (V (ν, y'))⁻¹) :=
        Finset.single_le_sum (fun y' _ => hnn ν y') (Finset.mem_univ y)
    _ ≤ _ := Finset.single_le_sum (f := fun ν => ∑ y', WilsonAction.wilsonDensity
        (A y' * V' (ν, y') * (A (tsh 0 (Tn m) ν y'))⁻¹ * (V (ν, y'))⁻¹))
        (fun ν _ => Finset.sum_nonneg fun y' _ => hnn ν y') (Finset.mem_univ ν)

theorem wd_le_sp (hN : N ≠ 0) (V : Cfg m N) (νa νb : D) (y : Site m) :
    WilsonAction.wilsonDensity (V (νa, y) * V (νb, tsh 0 (Tn m) νa y)
      * (V (νa, tsh 0 (Tn m) νb y))⁻¹ * (V (νb, y))⁻¹) ≤ spT 0 (Tn m) V := by
  unfold spT
  have hnn : ∀ νa νb y, 0 ≤ WilsonAction.wilsonDensity (V (νa, y) * V (νb, tsh 0 (Tn m) νa y)
      * (V (νa, tsh 0 (Tn m) νb y))⁻¹ * (V (νb, y))⁻¹) :=
    fun _ _ _ => WilsonAction.wilsonDensity_nonneg hN _
  calc _ ≤ ∑ y', WilsonAction.wilsonDensity (V (νa, y') * V (νb, tsh 0 (Tn m) νa y')
        * (V (νa, tsh 0 (Tn m) νb y'))⁻¹ * (V (νb, y'))⁻¹) :=
        Finset.single_le_sum (fun y' _ => hnn νa νb y') (Finset.mem_univ y)
    _ ≤ ∑ νb', ∑ y', WilsonAction.wilsonDensity (V (νa, y') * V (νb', tsh 0 (Tn m) νa y')
        * (V (νa, tsh 0 (Tn m) νb' y'))⁻¹ * (V (νb', y'))⁻¹) :=
        Finset.single_le_sum (f := fun νb' => ∑ y', WilsonAction.wilsonDensity
          (V (νa, y') * V (νb', tsh 0 (Tn m) νa y') * (V (νa, tsh 0 (Tn m) νb' y'))⁻¹
            * (V (νb', y'))⁻¹))
          (fun νb' _ => Finset.sum_nonneg fun y' _ => hnn νa νb' y') (Finset.mem_univ νb)
    _ ≤ _ := Finset.single_le_sum (f := fun νa' => ∑ νb', ∑ y', WilsonAction.wilsonDensity
          (V (νa', y') * V (νb', tsh 0 (Tn m) νa' y') * (V (νa', tsh 0 (Tn m) νb' y'))⁻¹
            * (V (νb', y'))⁻¹))
          (fun νa' _ => Finset.sum_nonneg fun νb' _ => Finset.sum_nonneg fun y' _ => hnn νa' νb' y')
          (Finset.mem_univ νa)

end Ladders

/-! ## 7. Assembly -/

section Assembly

variable {N : ℕ} [NeZero N]

end Assembly

end MassGap.TwistedTraceBoundN

#print axioms MassGap.TwistedTraceBoundN.kT_act
