import Mathlib
import MassGap.FluxSectorBound
import MassGap.DeltaLengthTower
import MassGap.HeatBathErgodic

/-!
# MassGap.TwistedTraceBound — the centre flips and kernel bounds for twisted traces (SU(2))

Fix the torus of side `n = m + 1 = 2j` and the transfer in direction `0`, a kernel on the
configurations of one spatial slice (`RectTransfer.kT`). `a = kT^{∗j}` is the transfer over half the
time extent. `hs(a) = ZR(n⁴)`, and `hs(a ∗ a) = ZR(2n × n³)`.

**The centre flips.** `flip ν` multiplies by `−1` every link in spatial direction `ν` whose
`ν`-coordinate is `0`. It preserves Haar measure and the transfer kernel (`kT_flip`, `flipF`).

**The kernel bounds.** The module collects the estimates a suppression argument for twisted traces
uses:
* `kT_le_of_lip`: if an observable `g` satisfies `|g V − g V'| ≤ L √(tp(A))` for every axis-link
  configuration `A`, then `kT V V'` is at most `exp(−2β (|g V − g V'| / L)²)`. The ingredients are
  `kT_le_gk` and `gk_le_of_tp`; `iter_offdiag` carries the bound to the iterates `kT^{∗j}`, and
  `iter_le_sp` bounds the iterates by `exp(−β sp(y)/2)` in the spatial action.
* `wd_le_tp`, `wd_le_sp`: each plaquette density is at most the temporal, respectively spatial, slice
  action.
* `ZR_lower`: `ZR ≥ c_η e^{−βη}` for every `η > 0`, since a neighbourhood of the trivial configuration
  has positive Haar measure.

No asymptotic expansion enters. Every suppression is exponential in `β` and is compared with an
`e^{−βη}` lower bound on `ZR`, `η` as small as needed.

DERIVED (module-wide): `0` is the time direction and the flipped coordinate; `1`, `2` name the two
spatial directions.
-/

noncomputable section

namespace MassGap.TwistedTraceBound

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower

/-! ## 1. Geometry of the spatial torus -/

/-- Spatial directions. -/
abbrev D : Type := {j : Fin 4 // j ≠ 0}

/-- Spatial direction `1`. -/
def d1 : D := ⟨1, by decide⟩
/-- Spatial direction `2`. -/
def d2 : D := ⟨2, by decide⟩

theorem d2_ne_d1 : d2 ≠ d1 := by decide

variable (m : ℕ)

/-- Transverse extents `m + 1`. -/
abbrev Tn : D → ℕ := fun _ => m + 1
/-- Sites of the spatial torus. -/
abbrev Site : Type := TT 0 (Tn m)
/-- Slice configurations. -/
abbrev Cfg : Type := SpT 0 (Tn m) → SUN.SU 2

variable {m}

/-- One step in direction `ν`. -/
abbrev step (ν : D) (y : Site m) : Site m := tsh 0 (Tn m) ν y

/-- `i` steps in direction `ν`. -/
def pos (ν : D) (i : ℕ) (y : Site m) : Site m := (step ν)^[i] y

/-- The origin. -/
def org : Site m := fun _ => (0 : Fin (m + 1))

theorem step_self (ν : D) (y : Site m) : step ν y ν = y ν + 1 := by
  simp [step, tsh, finRotate_succ_apply]

theorem step_ne {ν k : D} (h : k ≠ ν) (y : Site m) : step ν y k = y k := by
  simp [step, tsh, Function.update_of_ne h]

theorem pos_zero (ν : D) (y : Site m) : pos ν 0 y = y := rfl

theorem pos_succ (ν : D) (i : ℕ) (y : Site m) : pos ν (i + 1) y = step ν (pos ν i y) :=
  Function.iterate_succ_apply' _ _ _

theorem pos_val (ν : D) (i : ℕ) (y : Site m) : (pos ν i y ν).val = ((y ν).val + i) % (m + 1) := by
  induction i with
  | zero =>
    show (y ν).val = ((y ν).val + 0) % (m + 1)
    rw [Nat.add_zero, Nat.mod_eq_of_lt (y ν).isLt]
  | succ i ih =>
    rw [pos_succ, step_self, Fin.val_add, ih, Fin.val_one', ← Nat.add_mod]
    congr 1

theorem pos_ne {ν k : D} (h : k ≠ ν) (i : ℕ) (y : Site m) : pos ν i y k = y k := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pos_succ, step_ne h, ih]

theorem pos_period (ν : D) (y : Site m) : pos ν (m + 1) y = y := by
  funext k
  by_cases h : k = ν
  · subst h
    apply Fin.ext
    rw [pos_val, Nat.add_mod_right, Nat.mod_eq_of_lt (y k).isLt]
  · rw [pos_ne h]

theorem step_comm {ν ν' : D} (h : ν ≠ ν') (y : Site m) :
    step ν (step ν' y) = step ν' (step ν y) := by
  funext k
  by_cases hk : k = ν
  · subst hk
    simp only [step_self, step_ne h]
  · by_cases hk' : k = ν'
    · subst hk'
      simp only [step_self, step_ne hk]
    · simp only [step_ne hk, step_ne hk']

theorem pos_step_comm {ν ν' : D} (h : ν ≠ ν') (i : ℕ) (y : Site m) :
    pos ν i (step ν' y) = step ν' (pos ν i y) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pos_succ, pos_succ, ih, step_comm h]

/-! ## 2. The centre flip -/

/-- The centre element `−1` of `SU(2)`. -/
def negOne : SUN.SU 2 :=
  ⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]; simp
    · simp [Matrix.det_neg]⟩

theorem coe_negOne : ((negOne : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

theorem negOne_mul_self : negOne * negOne = 1 := Subtype.ext (by simp [negOne])

/-- The flip sign of a link. -/
def sgn (ν : D) (l : SpT 0 (Tn m)) : SUN.SU 2 :=
  if l.1 = ν ∧ (l.2 ν).val = 0 then negOne else 1

/-- The flip sign as a scalar. -/
def es (ν : D) (l : SpT 0 (Tn m)) : ℂ :=
  if l.1 = ν ∧ (l.2 ν).val = 0 then -1 else 1

/-- **The centre flip** in direction `ν`. -/
def flip (ν : D) (V : Cfg m) : Cfg m := fun l => sgn ν l * V l

theorem coe_flip (ν : D) (V : Cfg m) (l : SpT 0 (Tn m)) :
    ((flip ν V l : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = es ν l • ((V l : SUN.SU 2) : Matrix _ _ ℂ) := by
  unfold flip sgn es
  split_ifs <;> simp [coe_negOne]

theorem flip_flip (ν : D) (V : Cfg m) : flip ν (flip ν V) = V := by
  funext l
  unfold flip
  rw [← mul_assoc]
  unfold sgn
  split_ifs <;> simp [negOne_mul_self]

theorem es_sq (ν : D) (l : SpT 0 (Tn m)) : es ν l * es ν l = 1 := by
  unfold es; split_ifs <;> norm_num

theorem star_es (ν : D) (l : SpT 0 (Tn m)) : star (es ν l) = es ν l := by
  unfold es; split_ifs <;> simp

theorem es_dir {ν : D} {l : SpT 0 (Tn m)} (h : l.1 ≠ ν) : es ν l = 1 := by
  unfold es; rw [if_neg (fun h' => h h'.1)]

theorem es_step {ν ν' : D} (h : ν' ≠ ν) (d : D) (y : Site m) :
    es ν (d, step ν' y) = es ν (d, y) := by
  simp only [es, step_ne (Ne.symm h)]

/-- `((g⁻¹ : SU 2) : M) = star g`. -/
theorem coe_inv (g : SUN.SU 2) :
    ((g⁻¹ : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) = star (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem wd_congr {g h : SUN.SU 2}
    (e : (g : Matrix (Fin 2) (Fin 2) ℂ) = (h : Matrix (Fin 2) (Fin 2) ℂ)) :
    WilsonAction.wilsonDensity g = WilsonAction.wilsonDensity h := by
  unfold WilsonAction.wilsonDensity; rw [e]

theorem smul_plaq (ea eb ec ed : ℂ) (A B C E : Matrix (Fin 2) (Fin 2) ℂ) (hc : star ec = ec)
    (hd : star ed = ed) :
    (ea • A) * (eb • B) * star (ec • C) * star (ed • E)
      = (ea * eb * ec * ed) • (A * B * star C * star E) := by
  rw [star_smul, star_smul, hc, hd]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1; ring

/-- The sign product around a spatial plaquette is `1`. -/
theorem es_plaq (ν νa νb : D) (y : Site m) :
    es ν (νa, y) * es ν (νb, step νa y) * es ν (νa, step νb y) * es ν (νb, y) = 1 := by
  by_cases hb : νb = ν
  · subst hb
    by_cases ha : νa = νb
    · subst ha
      calc es νa (νa, y) * es νa (νa, step νa y) * es νa (νa, step νa y) * es νa (νa, y)
          = (es νa (νa, y) * es νa (νa, y)) * (es νa (νa, step νa y) * es νa (νa, step νa y)) := by
            ring
        _ = 1 := by rw [es_sq, es_sq, one_mul]
    · rw [es_dir (l := (νa, y)) ha, es_dir (l := (νa, step νb y)) ha, es_step ha]
      rw [one_mul, mul_one, es_sq]
  · rw [es_dir (l := (νb, step νa y)) hb, es_dir (l := (νb, y)) hb, es_step hb]
    rw [mul_one, mul_one, es_sq]

theorem sp_flip (ν : D) (V : Cfg m) : spT 0 (Tn m) (flip ν V) = spT 0 (Tn m) V := by
  unfold spT
  refine Finset.sum_congr rfl fun νa _ => Finset.sum_congr rfl fun νb _ =>
    Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_flip]
  rw [smul_plaq _ _ _ _ _ _ _ _ (star_es _ _) (star_es _ _), es_plaq, one_smul]

theorem tp_flip (ν : D) (A : TT 0 (Tn m) → SUN.SU 2) (V V' : Cfg m) :
    tpT 0 (Tn m) A (flip ν V) (flip ν V') = tpT 0 (Tn m) A V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun νb _ => Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_flip]
  have h := smul_plaq 1 (es ν (νb, y)) 1 (es ν (νb, y)) ((A y : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
    ((V' (νb, y) : SUN.SU 2) : Matrix _ _ ℂ) ((A (tsh 0 (Tn m) νb y) : SUN.SU 2) : Matrix _ _ ℂ)
    ((V (νb, y) : SUN.SU 2) : Matrix _ _ ℂ) (by simp) (star_es _ _)
  simp only [one_smul] at h
  rw [h, one_mul, mul_one, es_sq, one_smul]

theorem gk_flip (ν : D) (β : ℝ) (V V' : Cfg m) :
    gk 0 (Tn m) 2 β (flip ν V) (flip ν V') = gk 0 (Tn m) 2 β V V' := by
  unfold gk
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [tp_flip]

theorem kT_flip (ν : D) (β : ℝ) (V V' : Cfg m) :
    kT 0 (Tn m) 2 β (flip ν V) (flip ν V') = kT 0 (Tn m) 2 β V V' := by
  unfold kT; rw [sp_flip, sp_flip, gk_flip]

theorem mp_flip (ν : D) :
    MeasurePreserving (flip (m := m) ν) (hS 0 (Tn m) 2) (hS 0 (Tn m) 2) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU 2)) (fun _ => probHaar (SUN.SU 2))
    (fun l => measurePreserving_mul_left (probHaar (SUN.SU 2)) (sgn ν l))

theorem flipF (ν : D) : FluxSectorBound.Flip (hS 0 (Tn m) 2) (flip (m := m) ν) :=
  ⟨(mp_flip ν).measurable, flip_flip ν, mp_flip ν⟩

/-! ## 3. Kernel iterates -/

section Iter

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ}

theorem iter_inv {σ : X → X} (hf : FluxSectorBound.Flip μ σ)
    (hk : ∀ x y, k (σ x) (σ y) = k x y) : ∀ i x y, iter μ k i (σ x) (σ y) = iter μ k i x y
  | 0, x, y => hk x y
  | i + 1, x, y => by
    change ∫ z, k (σ x) z * iter μ k i z (σ y) ∂μ = ∫ z, k x z * iter μ k i z y ∂μ
    rw [← hf.integral_comp (fun z => k (σ x) z * iter μ k i z (σ y))]
    congr 1; funext z
    rw [hk, iter_inv hf hk i z y]

theorem iter_bounds (hkb : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hk1 : ∀ x y, k x y ≤ 1) :
    ∀ i x y, 0 ≤ iter μ k i x y ∧ iter μ k i x y ≤ 1
  | 0, x, y => ⟨hk0 x y, hk1 x y⟩
  | i + 1, x, y => by
    have ih := iter_bounds hkb hk0 hk1 i
    change 0 ≤ ∫ z, k x z * iter μ k i z y ∂μ ∧ ∫ z, k x z * iter μ k i z y ∂μ ≤ 1
    have hm : Measurable fun z => k x z * iter μ k i z y := (hkb.row x).mul ((hkb.iter i).col y)
    have hb : ∀ z, |k x z * iter μ k i z y| ≤ 1 := fun z => by
      rw [abs_of_nonneg (mul_nonneg (hk0 x z) (ih z y).1)]
      exact mul_le_one₀ (hk1 x z) (ih z y).1 (ih z y).2
    refine ⟨integral_nonneg fun z => mul_nonneg (hk0 x z) (ih z y).1, ?_⟩
    calc ∫ z, k x z * iter μ k i z y ∂μ ≤ ∫ _z, (1 : ℝ) ∂μ :=
          integral_mono (integrable_of_bdd hm hb) (integrable_const _) fun z => (abs_le.mp (hb z)).2
      _ = 1 := by simp

theorem exp_dec {β s t : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp (-2 * β * t ^ 2) ≤ Real.exp (-2 * β * s ^ 2) := by
  rw [Real.exp_le_exp]
  have : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs hst 2
  nlinarith

/-- **Off-diagonal decay of the iterates.** -/
theorem iter_offdiag (hkb : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hk1 : ∀ x y, k x y ≤ 1)
    {g : X → ℂ} {L β : ℝ} (hL : 0 < L) (hβ : 0 ≤ β)
    (hbase : ∀ x y, k x y ≤ Real.exp (-2 * β * (‖g x - g y‖ / L) ^ 2)) :
    ∀ i x y, iter μ k i x y ≤ Real.exp (-2 * β * (‖g x - g y‖ / ((i + 1 : ℝ) * L)) ^ 2)
  | 0, x, y => by
    show k x y ≤ _
    simpa using hbase x y
  | i + 1, x, y => by
    have ih := iter_offdiag hkb hk0 hk1 hL hβ hbase i
    have bnd := iter_bounds (μ := μ) hkb hk0 hk1 i
    change ∫ z, k x z * iter μ k i z y ∂μ ≤ _
    set Dd := ‖g x - g y‖ with hDd
    set B := Real.exp (-2 * β * (Dd / (((i + 1 : ℕ) : ℝ) + 1) / L) ^ 2) with hB
    have hpt : ∀ z, k x z * iter μ k i z y ≤ Real.exp (-2 * β * (Dd / ((((i + 1 : ℕ) : ℝ) + 1) * L)) ^ 2) := by
      intro z
      have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hi2 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) + 1 := by positivity
      have htri : Dd ≤ ‖g x - g z‖ + ‖g z - g y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have hD0 : 0 ≤ Dd := norm_nonneg _
      by_cases hc : Dd / (((i + 1 : ℕ) : ℝ) + 1) ≤ ‖g x - g z‖
      · have h1 : k x z ≤ Real.exp (-2 * β * (Dd / ((((i + 1 : ℕ) : ℝ) + 1) * L)) ^ 2) := by
          refine (hbase x z).trans (exp_dec hβ (by positivity) ?_)
          rw [← div_div]
          exact div_le_div_of_nonneg_right hc hL.le
        calc k x z * iter μ k i z y ≤ k x z * 1 :=
              mul_le_mul_of_nonneg_left (bnd z y).2 (hk0 x z)
          _ ≤ _ := by rw [mul_one]; exact h1
      · push_neg at hc
        have h2 : Dd / ((((i + 1 : ℕ) : ℝ) + 1) * L) ≤ ‖g z - g y‖ / (((i : ℝ) + 1) * L) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hc' : ‖g x - g z‖ * (((i + 1 : ℕ) : ℝ) + 1) < Dd := (lt_div_iff₀ hi2).mp hc
          have t1 : (Dd - ‖g x - g z‖) * (((i + 1 : ℕ) : ℝ) + 1)
              ≤ ‖g z - g y‖ * (((i + 1 : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hi2.le
          have key : Dd * ((i : ℝ) + 1) ≤ ‖g z - g y‖ * (((i + 1 : ℕ) : ℝ) + 1) := by
            push_cast at hc' t1 ⊢
            nlinarith
          have := mul_le_mul_of_nonneg_right key hL.le
          push_cast at this ⊢
          nlinarith
        have h3 : iter μ k i z y ≤ Real.exp (-2 * β * (Dd / ((((i + 1 : ℕ) : ℝ) + 1) * L)) ^ 2) :=
          (ih z y).trans (exp_dec hβ (by positivity) h2)
        calc k x z * iter μ k i z y ≤ 1 * iter μ k i z y :=
              mul_le_mul_of_nonneg_right (hk1 x z) (bnd z y).1
          _ ≤ _ := by rw [one_mul]; exact h3
    have hm : Measurable fun z => k x z * iter μ k i z y := (hkb.row x).mul ((hkb.iter i).col y)
    have hb : ∀ z, |k x z * iter μ k i z y| ≤ 1 := fun z => by
      rw [abs_of_nonneg (mul_nonneg (hk0 x z) (bnd z y).1)]
      exact mul_le_one₀ (hk1 x z) (bnd z y).1 (bnd z y).2
    calc ∫ z, k x z * iter μ k i z y ∂μ
        ≤ ∫ _z, Real.exp (-2 * β * (Dd / ((((i + 1 : ℕ) : ℝ) + 1) * L)) ^ 2) ∂μ :=
          integral_mono (integrable_of_bdd hm hb) (integrable_const _) hpt
      _ = _ := by simp

/-- **The last slice's spatial factor survives the iterates.** -/
theorem iter_le_sp (hkb : Bdd k) (hk0 : ∀ x y, 0 ≤ k x y) (hk1 : ∀ x y, k x y ≤ 1)
    {f : X → ℝ} (hbase : ∀ x y, k x y ≤ f y) : ∀ i x y, iter μ k i x y ≤ f y
  | 0, x, y => hbase x y
  | i + 1, x, y => by
    have ih := iter_le_sp hkb hk0 hk1 hbase i
    have bnd := iter_bounds (μ := μ) hkb hk0 hk1 i
    change ∫ z, k x z * iter μ k i z y ∂μ ≤ f y
    have hm : Measurable fun z => k x z * iter μ k i z y := (hkb.row x).mul ((hkb.iter i).col y)
    have hb : ∀ z, |k x z * iter μ k i z y| ≤ 1 := fun z => by
      rw [abs_of_nonneg (mul_nonneg (hk0 x z) (bnd z y).1)]
      exact mul_le_one₀ (hk1 x z) (bnd z y).1 (bnd z y).2
    calc ∫ z, k x z * iter μ k i z y ∂μ ≤ ∫ _z, f y ∂μ :=
          integral_mono (integrable_of_bdd hm hb) (integrable_const _) fun z =>
            (mul_le_mul_of_nonneg_left (ih z y) (hk0 x z)).trans
              (by have := (bnd z y).1; have := ih z y
                  have h0 : 0 ≤ f y := this.trans' (bnd z y).1
                  nlinarith [hk1 x z, hk0 x z])
      _ = f y := by simp

end Iter

/-! ## 4. Kernel bounds on the lattice -/

theorem gk_nonneg {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m) : 0 ≤ gk 0 (Tn m) 2 β V V' :=
  (Real.exp_pos _).le.trans (gk_ge (by norm_num) hβ V V')

theorem kT_nonneg {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m) : 0 ≤ kT 0 (Tn m) 2 β V V' :=
  (kTmin_pos β).le.trans (kT_lower (by norm_num) hβ V V')

theorem kT_le_gk {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m) :
    kT 0 (Tn m) 2 β V V' ≤ gk 0 (Tn m) 2 β V V' := by
  unfold kT
  have h1 : Real.exp (-β * spT 0 (Tn m) V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg (by norm_num : (2 : ℕ) ≠ 0) V; nlinarith
  have h2 : Real.exp (-β * spT 0 (Tn m) V' / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg (by norm_num : (2 : ℕ) ≠ 0) V'; nlinarith
  have h0 := gk_nonneg hβ V V'
  calc Real.exp (-β * spT 0 (Tn m) V / 2) * gk 0 (Tn m) 2 β V V' * Real.exp (-β * spT 0 (Tn m) V' / 2)
      ≤ 1 * gk 0 (Tn m) 2 β V V' * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 h0) h2 (Real.exp_pos _).le
        exact mul_nonneg zero_le_one h0
    _ = gk 0 (Tn m) 2 β V V' := by ring

theorem kT_le_sp {β : ℝ} (hβ : 0 ≤ β) (V V' : Cfg m) :
    kT 0 (Tn m) 2 β V V' ≤ Real.exp (-β * spT 0 (Tn m) V' / 2) := by
  unfold kT
  have h1 : Real.exp (-β * spT 0 (Tn m) V / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := sp_nonneg (by norm_num : (2 : ℕ) ≠ 0) V; nlinarith
  have h0 := gk_nonneg hβ V V'
  have h3 := gk_le_one (by norm_num : (2 : ℕ) ≠ 0) hβ V V'
  calc Real.exp (-β * spT 0 (Tn m) V / 2) * gk 0 (Tn m) 2 β V V' * Real.exp (-β * spT 0 (Tn m) V' / 2)
      ≤ 1 * 1 * Real.exp (-β * spT 0 (Tn m) V' / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul h1 h3 h0 zero_le_one
    _ = _ := by ring

/-- A uniform lower bound on the temporal action gives exponential decay of `gk`. -/
theorem gk_le_of_tp {β s : ℝ} (hβ : 0 ≤ β) {V V' : Cfg m}
    (h : ∀ A, s ≤ tpT 0 (Tn m) A V V') : gk 0 (Tn m) 2 β V V' ≤ Real.exp (-2 * β * s) := by
  unfold gk
  have hm : Measurable fun A : TT 0 (Tn m) → SUN.SU 2 =>
      Real.exp (-β * (2 * tpT 0 (Tn m) A V V')) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_tp continuous_id continuous_const continuous_const)))).measurable
  have hb : ∀ A : TT 0 (Tn m) → SUN.SU 2, |Real.exp (-β * (2 * tpT 0 (Tn m) A V V'))| ≤ 1 := by
    intro A
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := tp_nonneg (by norm_num : (2 : ℕ) ≠ 0) A V V'; nlinarith
  calc ∫ A, Real.exp (-β * (2 * tpT 0 (Tn m) A V V')) ∂(hA 0 (Tn m) 2)
      ≤ ∫ _A, Real.exp (-2 * β * s) ∂(hA 0 (Tn m) 2) :=
        integral_mono (integrable_of_bdd hm hb) (integrable_const _) fun A => by
          rw [Real.exp_le_exp]; have := h A; nlinarith
    _ = Real.exp (-2 * β * s) := by simp

/-! ## 5. The partition function is not exponentially small -/

theorem action_one {N : ℕ} (hN : N ≠ 0) (L : Fin 4 → ℕ) :
    (sysR L N).action (fun _ => (1 : SUN.SU N)) = 0 := by
  unfold LatticeGauge.System.action
  refine Finset.sum_eq_zero fun p _ => ?_
  simp [sysR, WilsonLattice.wilsonSystem, WilsonLattice.wilsonHol, WilsonAction.wilsonDensity_one hN]

/-- **`ZR ≥ c_η e^{−βη}`**, for every `η > 0`. -/
theorem ZR_lower {N : ℕ} (hN : N ≠ 0) (L : Fin 4 → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 ≤ β → c * Real.exp (-β * η) ≤ ZR L N β := by
  let sys := sysR L N
  haveI : IsProbabilityMeasure (sys.vol (probHaar (SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : RLink L => probHaar (SUN.SU N))))
  haveI : (sys.vol (probHaar (SUN.SU N))).IsOpenPosMeasure :=
    inferInstanceAs ((Measure.pi (fun _ : RLink L => probHaar (SUN.SU N))).IsOpenPosMeasure)
  set O : Set (sys.Config) := {U | sys.action U < η} with hO
  have hOo : IsOpen O := isOpen_lt (GibbsPositive.continuous_action (rbd L)) continuous_const
  have h1 : (fun _ => (1 : SUN.SU N)) ∈ O := by
    show sys.action (fun _ => 1) < η
    rw [action_one hN]; exact hη
  set c := (sys.vol (probHaar (SUN.SU N)) O).toReal
  have hc : 0 < c := ENNReal.toReal_pos (hOo.measure_ne_zero _ ⟨_, h1⟩) (measure_ne_top _ _)
  refine ⟨c, hc, fun β hβ => ?_⟩
  have iw : Integrable (sys.boltz β) (sys.vol (probHaar (SUN.SU N))) := by
    have h := WilsonReal.wilsonSystem_mul_boltz_integrable hN (rbd L) β (fun _ => (1 : ℝ))
      measurable_const 1 (fun _ => by norm_num)
    simp only [one_mul] at h
    exact h
  have hi : Integrable (O.indicator fun _ => Real.exp (-β * η)) (sys.vol (probHaar (SUN.SU N))) :=
    (integrable_const _).indicator hOo.measurableSet
  calc c * Real.exp (-β * η) = ∫ U, O.indicator (fun _ => Real.exp (-β * η)) U
        ∂(sys.vol (probHaar (SUN.SU N))) := by
        rw [integral_indicator_const _ hOo.measurableSet, smul_eq_mul]; rfl
    _ ≤ ∫ U, sys.boltz β U ∂(sys.vol (probHaar (SUN.SU N))) := by
        refine integral_mono hi iw fun U => ?_
        by_cases hU : U ∈ O
        · rw [Set.indicator_of_mem hU]
          unfold LatticeGauge.System.boltz
          rw [Real.exp_le_exp]
          have : sys.action U < η := hU
          nlinarith
        · rw [Set.indicator_of_notMem hU]
          exact (WilsonReal.wilsonSystem_boltz_pos (rbd L) β U).le
    _ = ZR L N β := rfl

/-! ## 6. Holonomies -/

theorem memU {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    M ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp h).1

theorem memDet {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    M.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp h).2

theorem coeU (g : SUN.SU 2) : ((g : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  memU g.2

/-! ## 8. Plaquette density bounds by the slice actions -/

section Ladders

attribute [local instance] Matrix.frobeniusNormedAddCommGroup


theorem wd_le_tp (A : TT 0 (Tn m) → SUN.SU 2) (V V' : Cfg m) (ν : D) (y : Site m) :
    WilsonAction.wilsonDensity (A y * V' (ν, y) * (A (tsh 0 (Tn m) ν y))⁻¹ * (V (ν, y))⁻¹)
      ≤ tpT 0 (Tn m) A V V' := by
  unfold tpT
  have hnn : ∀ ν y, 0 ≤ WilsonAction.wilsonDensity
      (A y * V' (ν, y) * (A (tsh 0 (Tn m) ν y))⁻¹ * (V (ν, y))⁻¹) :=
    fun _ _ => WilsonAction.wilsonDensity_nonneg (by norm_num) _
  calc _ ≤ ∑ y', WilsonAction.wilsonDensity
        (A y' * V' (ν, y') * (A (tsh 0 (Tn m) ν y'))⁻¹ * (V (ν, y'))⁻¹) :=
        Finset.single_le_sum (fun y' _ => hnn ν y') (Finset.mem_univ y)
    _ ≤ _ := Finset.single_le_sum (f := fun ν => ∑ y', WilsonAction.wilsonDensity
        (A y' * V' (ν, y') * (A (tsh 0 (Tn m) ν y'))⁻¹ * (V (ν, y'))⁻¹))
        (fun ν _ => Finset.sum_nonneg fun y' _ => hnn ν y') (Finset.mem_univ ν)

theorem wd_le_sp (V : Cfg m) (νa νb : D) (y : Site m) :
    WilsonAction.wilsonDensity (V (νa, y) * V (νb, tsh 0 (Tn m) νa y)
      * (V (νa, tsh 0 (Tn m) νb y))⁻¹ * (V (νb, y))⁻¹) ≤ spT 0 (Tn m) V := by
  unfold spT
  have hnn : ∀ νa νb y, 0 ≤ WilsonAction.wilsonDensity (V (νa, y) * V (νb, tsh 0 (Tn m) νa y)
      * (V (νa, tsh 0 (Tn m) νb y))⁻¹ * (V (νb, y))⁻¹) :=
    fun _ _ _ => WilsonAction.wilsonDensity_nonneg (by norm_num) _
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

/-! ## 9. Assembly -/

/-- The weight of a set of slices: `1` on it, `0` off it. -/
def chi (S : Set (Cfg m)) : Cfg m → ℝ := S.indicator (fun _ => 1)

theorem chi_of_mem {S : Set (Cfg m)} {y : Cfg m} (h : y ∈ S) : chi S y = 1 := by
  unfold chi; rw [Set.indicator_of_mem h]

theorem chi_of_not_mem {S : Set (Cfg m)} {y : Cfg m} (h : y ∉ S) : chi S y = 0 := by
  unfold chi; rw [Set.indicator_of_notMem h]


/-- The kernel bound from a Lipschitz observable. -/
theorem kT_le_of_lip {g : Cfg m → ℂ} {L β : ℝ} (hL : 0 < L) (hβ : 0 ≤ β)
    (hlip : ∀ A V V', ‖g V - g V'‖ ≤ L * Real.sqrt (tpT 0 (Tn m) A V V')) (V V' : Cfg m) :
    kT 0 (Tn m) 2 β V V' ≤ Real.exp (-2 * β * (‖g V - g V'‖ / L) ^ 2) := by
  refine (kT_le_gk hβ V V').trans (gk_le_of_tp (s := (‖g V - g V'‖ / L) ^ 2) hβ fun A => ?_)
  · have h := hlip A V V'
    have hs : ‖g V - g V'‖ / L ≤ Real.sqrt (tpT 0 (Tn m) A V V') := by
      rw [div_le_iff₀ hL]; linarith
    have := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hL.le) hs 2
    rwa [Real.sq_sqrt (tp_nonneg (by norm_num) A V V')] at this

end MassGap.TwistedTraceBound

#print axioms MassGap.TwistedTraceBound.kT_flip
#print axioms MassGap.TwistedTraceBound.ZR_lower
