import Mathlib
import MassGap.SectorDefect
import MassGap.TwistedTraceBound

/-!
# MassGap.CentreSectorSeed — the SU(2) seed is a flux-sector bound and a trivial-sector bound

`defectW 2 β n = 16 log ZR(n⁴) − log ZR((2n)⁴)` is the sum `8p₀ + 4p₁ + 2p₂ + p₃` of four
one-direction defects along the corner path `pathV`: step `i` doubles direction `i` of the torus
whose directions below `i` are already doubled (`defectW_eq`). Each `pᵢ` is the doubling defect
`SectorDefect.dd` of the transfer kernel `halfK β n i` over half the time extent `n`, on the slice
transverse to `i`.

**The centre flips of a slice.** `centreFlip ν` multiplies by `−1` every link in the transverse
direction `ν` whose `ν`-coordinate is `0`. It preserves Haar measure and the transfer kernel
(`kT_flip`), and the three flips of a slice commute (`centreFlip_comm`). Their joint even sector is the
trivial electric-flux sector; its kernel is `trivK β n i = evL (halfK β n i) (flips …)`.

* `fluxShare β n i = (hs(halfK) − hs(trivK)) / hs(halfK)`: the share of the trace carried by the
  states with non-zero electric flux, i.e. `(1/8) Σ (1 − Z_S/Z)` over the seven non-empty sets `S`
  of flips, `Z_S` the trace with the flips of `S` inserted (the partition function twisted in the
  time–space planes of `S`).
* `trivialDefect β n i = dd(trivK)`: the doubling defect of the trivial sector alone, i.e. the
  glueball part of the light-state count.

**Proved.**
* `defectW_le_of_sectors`: if, at side `n`, every step has `fluxShare ≤ 1/80000` and
  `trivialDefect ≤ 1/80000`, then `defectW 2 β n ≤ 1/1000`.
* `sectors_of_defectW`: conversely, `defectW 2 β n ≤ δ ≤ 1/1000` gives, at every step,
  `fluxShare ≤ 4δ` and `trivialDefect ≤ 2δ`.
* `seedExistsPow_iff_sectorSeedPow`: `DeltaLengthTower.SeedExistsPow 2 ↔ SectorSeedPow`. The
  converse direction moves three sharp squarings past the seed side (`defectW_eight_le`), where the
  defect is below `1/320000`.

So (A₂) for SU(2) is exactly the conjunction of two statements at one side: the
non-trivial flux sectors are suppressed (the 't Hooft electric-flux free energies are large, i.e.
the twisted partition functions are close to the untwisted one), and the trivial sector has a small
defect of its own. Neither implies the other: the deconfined 4D `Z₂` theory has the second and not
the first, and the endpoint of the first-order line of the fundamental–adjoint SU(2) action has the
first and not the second.

DERIVED (module-wide): `8, 4, 2, 1` are the weights of `DoublingRecursion.Δ`'s corner path, summing
to `15`; `1/80000` is chosen so that `15 · 5/80000 ≤ 1/1000`, the `5` being `1` for the trivial
defect plus `2 · 2` for twice the log share at a share of at least `1/2`; the `4` in `4δ` is `1/(2 · (1/8))`,
the fully even share being at least `1/8 = 2⁻³` (three flips); `2δ` bounds
`1/(1 − δ − 16δ²) − 1` for `δ ≤ 1/1000`; `1/320000 = (1/80000)/4`, and three squarings reach
`1/16384000 = (1/4)⁸/250` (`DoublingSharp.iterate_sharp`).
-/

noncomputable section

namespace MassGap.CentreSectorSeed

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SectorDefect MassGap.DoublingRecursion

/-! ## 1. The centre flips of a general slice -/

section Flip

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- Slice configurations. -/
abbrev Cfg (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) : Type := SpT μ T → SUN.SU 2

/-- The flip sign of a link. -/
def sgn (ν : {j : Fin 4 // j ≠ μ}) (l : SpT μ T) : SUN.SU 2 :=
  if l.1 = ν ∧ (l.2 ν).val = 0 then TwistedTraceBound.negOne else 1

/-- The flip sign as a scalar. -/
def es (ν : {j : Fin 4 // j ≠ μ}) (l : SpT μ T) : ℂ :=
  if l.1 = ν ∧ (l.2 ν).val = 0 then -1 else 1

/-- **The centre flip** in the transverse direction `ν`. -/
def centreFlip (ν : {j : Fin 4 // j ≠ μ}) (V : Cfg μ T) : Cfg μ T := fun l => sgn ν l * V l

theorem coe_centreFlip (ν : {j : Fin 4 // j ≠ μ}) (V : Cfg μ T) (l : SpT μ T) :
    ((centreFlip ν V l : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = es ν l • ((V l : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold centreFlip sgn es
  split_ifs <;> simp [TwistedTraceBound.coe_negOne]

theorem centreFlip_flip (ν : {j : Fin 4 // j ≠ μ}) (V : Cfg μ T) :
    centreFlip ν (centreFlip ν V) = V := by
  funext l
  unfold centreFlip
  rw [← mul_assoc]
  unfold sgn
  split_ifs <;> simp [TwistedTraceBound.negOne_mul_self]

theorem centreFlip_comm (ν ν' : {j : Fin 4 // j ≠ μ}) (V : Cfg μ T) :
    centreFlip ν (centreFlip ν' V) = centreFlip ν' (centreFlip ν V) := by
  funext l
  apply Subtype.ext
  rw [coe_centreFlip, coe_centreFlip, coe_centreFlip, coe_centreFlip, smul_smul, smul_smul,
    mul_comm (es ν l)]

theorem es_sq (ν : {j : Fin 4 // j ≠ μ}) (l : SpT μ T) : es ν l * es ν l = 1 := by
  unfold es; split_ifs <;> norm_num

theorem star_es (ν : {j : Fin 4 // j ≠ μ}) (l : SpT μ T) : star (es ν l) = es ν l := by
  unfold es; split_ifs <;> simp

theorem es_dir {ν : {j : Fin 4 // j ≠ μ}} {l : SpT μ T} (h : l.1 ≠ ν) : es ν l = 1 := by
  unfold es; rw [if_neg (fun h' => h h'.1)]

theorem tsh_ne {ν ν' : {j : Fin 4 // j ≠ μ}} (h : ν ≠ ν') (y : TT μ T) : tsh μ T ν' y ν = y ν := by
  unfold tsh; rw [Function.update_of_ne h]

theorem es_step {ν ν' : {j : Fin 4 // j ≠ μ}} (h : ν' ≠ ν) (d : {j : Fin 4 // j ≠ μ}) (y : TT μ T) :
    es ν (d, tsh μ T ν' y) = es ν (d, y) := by
  simp only [es, tsh_ne (Ne.symm h)]

/-- The sign product around a spatial plaquette is `1`. -/
theorem es_plaq (ν νa νb : {j : Fin 4 // j ≠ μ}) (y : TT μ T) :
    es ν (νa, y) * es ν (νb, tsh μ T νa y) * es ν (νa, tsh μ T νb y) * es ν (νb, y) = 1 := by
  by_cases hb : νb = ν
  · subst hb
    by_cases ha : νa = νb
    · subst ha
      calc es νa (νa, y) * es νa (νa, tsh μ T νa y) * es νa (νa, tsh μ T νa y) * es νa (νa, y)
          = (es νa (νa, y) * es νa (νa, y)) * (es νa (νa, tsh μ T νa y) * es νa (νa, tsh μ T νa y)) := by
            ring
        _ = 1 := by rw [es_sq, es_sq, one_mul]
    · rw [es_dir (l := (νa, y)) ha, es_dir (l := (νa, tsh μ T νb y)) ha, es_step ha]
      rw [one_mul, mul_one, es_sq]
  · rw [es_dir (l := (νb, tsh μ T νa y)) hb, es_dir (l := (νb, y)) hb, es_step hb]
    rw [mul_one, mul_one, es_sq]

theorem sp_flip (ν : {j : Fin 4 // j ≠ μ}) (V : Cfg μ T) :
    spT μ T (centreFlip ν V) = spT μ T V := by
  unfold spT
  refine Finset.sum_congr rfl fun νa _ => Finset.sum_congr rfl fun νb _ =>
    Finset.sum_congr rfl fun y _ => TwistedTraceBound.wd_congr ?_
  simp only [Submonoid.coe_mul, TwistedTraceBound.coe_inv, coe_centreFlip]
  rw [TwistedTraceBound.smul_plaq _ _ _ _ _ _ _ _ (star_es _ _) (star_es _ _), es_plaq, one_smul]

theorem tp_flip (ν : {j : Fin 4 // j ≠ μ}) (A : TT μ T → SUN.SU 2) (V V' : Cfg μ T) :
    tpT μ T A (centreFlip ν V) (centreFlip ν V') = tpT μ T A V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun νb _ => Finset.sum_congr rfl fun y _ =>
    TwistedTraceBound.wd_congr ?_
  simp only [Submonoid.coe_mul, TwistedTraceBound.coe_inv, coe_centreFlip]
  have h := TwistedTraceBound.smul_plaq 1 (es ν (νb, y)) 1 (es ν (νb, y))
    ((A y : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
    ((V' (νb, y) : SUN.SU 2) : Matrix _ _ ℂ) ((A (tsh μ T νb y) : SUN.SU 2) : Matrix _ _ ℂ)
    ((V (νb, y) : SUN.SU 2) : Matrix _ _ ℂ) (by simp) (star_es _ _)
  simp only [one_smul] at h
  rw [h, one_mul, mul_one, es_sq, one_smul]

theorem gk_flip (ν : {j : Fin 4 // j ≠ μ}) (β : ℝ) (V V' : Cfg μ T) :
    gk μ T 2 β (centreFlip ν V) (centreFlip ν V') = gk μ T 2 β V V' := by
  unfold gk
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [tp_flip]

theorem kT_flip (ν : {j : Fin 4 // j ≠ μ}) (β : ℝ) (V V' : Cfg μ T) :
    kT μ T 2 β (centreFlip ν V) (centreFlip ν V') = kT μ T 2 β V V' := by
  unfold kT; rw [sp_flip, sp_flip, gk_flip]

theorem mp_flip (ν : {j : Fin 4 // j ≠ μ}) :
    MeasurePreserving (centreFlip (T := T) ν) (hS μ T 2) (hS μ T 2) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU 2)) (fun _ => probHaar (SUN.SU 2))
    (fun l => measurePreserving_mul_left (probHaar (SUN.SU 2)) (sgn ν l))

theorem flipF (ν : {j : Fin 4 // j ≠ μ}) :
    FluxSectorBound.Flip (hS μ T 2) (centreFlip (T := T) ν) :=
  ⟨(mp_flip ν).measurable, centreFlip_flip ν, mp_flip ν⟩

variable (μ T) in
/-- The three centre flips of the slice. -/
def flips : List (Cfg μ T → Cfg μ T) :=
  (Finset.univ : Finset {j : Fin 4 // j ≠ μ}).toList.map (centreFlip (T := T))

theorem flips_spec : Flips (hS μ T 2) (flips μ T) := by
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ V => ?_⟩
  · obtain ⟨ν, _, rfl⟩ := List.mem_map.mp hσ
    exact flipF ν
  · obtain ⟨ν, _, rfl⟩ := List.mem_map.mp hσ
    obtain ⟨ν', _, rfl⟩ := List.mem_map.mp hτ
    exact centreFlip_comm ν ν' V


theorem card_transverse (μ : Fin 4) : Fintype.card {j : Fin 4 // j ≠ μ} = 3 := by
  first
  | simp
  | (fin_cases μ <;> decide)

theorem flips_length : (flips μ T).length = 3 := by
  simp only [flips, List.length_map, Finset.length_toList, Finset.card_univ]
  exact card_transverse μ

theorem kT_flips_inv (β : ℝ) : ∀ σ ∈ flips μ T, ∀ i x y,
    iter (hS μ T 2) (kT μ T 2 β) i (σ x) (σ y) = iter (hS μ T 2) (kT μ T 2 β) i x y := by
  intro σ hσ
  obtain ⟨ν, _, rfl⟩ := List.mem_map.mp hσ
  exact TwistedTraceBound.iter_inv (flipF ν) (kT_flip ν β)

end Flip

/-! ## 2. The corner path and the four one-direction defects -/

/-- The corner path of `DoublingRecursion.Δ`: step `i` starts at `pathV i` and doubles direction `i`. -/
def pathV : Fin 4 → Pt := ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0]]

theorem pathV_self (i : Fin 4) : pathV i i = 0 := by fin_cases i <;> rfl

theorem path_first : corner 0 = pathV 0 := by decide
theorem path_step0 : pathV 0 + E 0 = pathV 1 := by decide
theorem path_step1 : pathV 1 + E 1 = pathV 2 := by decide
theorem path_step2 : pathV 2 + E 2 = pathV 3 := by decide
theorem path_last : pathV 3 + E 3 = corner 0 + one := by decide

/-- Transverse extents at step `i`. -/
abbrev Tr (n : ℕ) (i : Fin 4) : {j : Fin 4 // j ≠ i} → ℕ := tr (DoublingWilson.ext n (pathV i)) i

/-- Haar measure on the slice of step `i`. -/
abbrev hSi (n : ℕ) (i : Fin 4) : Measure (Cfg i (Tr n i)) := hS i (Tr n i) 2

/-- The transfer over half the time extent `n`, on the slice of step `i`. -/
def halfK (β : ℝ) (n : ℕ) (i : Fin 4) : Cfg i (Tr n i) → Cfg i (Tr n i) → ℝ :=
  iter (hSi n i) (kT i (Tr n i) 2 β) (n / 2 - 1)

/-- The trivial electric-flux sector of `halfK`: the part even under all three centre flips. -/
def trivK (β : ℝ) (n : ℕ) (i : Fin 4) : Cfg i (Tr n i) → Cfg i (Tr n i) → ℝ :=
  evL (halfK β n i) (flips i (Tr n i))

/-- **The flux share**: the share of the trace carried by non-zero electric flux. -/
def fluxShare (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) / hs (hSi n i) (halfK β n i)

/-- **The trivial-sector defect**: the doubling defect of the trivial flux sector alone. -/
def trivialDefect (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ := dd (hSi n i) (trivK β n i)

/-- The floor of `halfK`. -/
def floor (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ := kTmin i (Tr n i) β ^ (n / 2 - 1 + 1)

theorem floor_pos (β : ℝ) (n : ℕ) (i : Fin 4) : 0 < floor β n i := pow_pos (kTmin_pos β) _

theorem adm_halfK {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    Adm (flips i (Tr n i)) (floor β n i) (halfK β n i) := by
  have hk := bdd_kT (μ := i) (T := Tr n i) (N := 2) (by norm_num) hβ
  have hlow : ∀ V V', kTmin i (Tr n i) β ≤ kT i (Tr n i) 2 β V V' :=
    kT_lower (N := 2) (by norm_num) hβ
  unfold halfK floor
  exact ⟨hk.iter _, CyclicKernel.iter_symm hk (kT_symm β) _, fun σ hσ => kT_flips_inv β σ hσ _,
    iter_low hk (kTmin_pos β).le hlow _⟩

theorem adm_trivK {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    Adm ([] : List (Cfg i (Tr n i) → Cfg i (Tr n i))) (floor β n i) (trivK β n i) :=
  adm_evL _ _ flips_spec (adm_halfK hβ n i)

section Positivity

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

theorem hs_pos_of_adm {l : List (X → X)} {c : ℝ} {b : X → X → ℝ} (hc : 0 < c) (hb : Adm l c b) :
    0 < hs ν b := by
  have := sq_le_hs (μ := ν) hb.bdd hc.le hb.low
  have : 0 < c ^ 2 := by positivity
  linarith

theorem hs_conv_pos_of_adm {l : List (X → X)} {c : ℝ} {b : X → X → ℝ} (hc : 0 < c)
    (hb : Adm l c b) : 0 < hs ν (conv ν b b) := by
  have := sq_le_hs (μ := ν) (hb.bdd.conv (μ := ν) hb.bdd) (mul_nonneg hc.le hc.le)
    (conv_low (μ := ν) hb.bdd hc.le hb.low)
  have : 0 < (c * c) ^ 2 := by positivity
  linarith

theorem dd_nonneg {l : List (X → X)} {c : ℝ} {b : X → X → ℝ} (hc : 0 < c) (hb : Adm l c b) :
    0 ≤ dd ν b := by
  have hA := hs_pos_of_adm (ν := ν) hc hb
  have hD := hs_conv_pos_of_adm (ν := ν) hc hb
  have hle : hs ν (conv ν b b) ≤ hs ν b ^ 2 := by
    rw [sq]; exact hs_conv_le_mul hb.bdd hb.bdd
  have := Real.log_le_log hD hle
  rw [Real.log_pow] at this
  unfold dd
  push_cast at this
  linarith

end Positivity

/-- Each step of the corner path is the doubling defect of `halfK`. -/
theorem p_eq_dd {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4) :
    p (DoublingWilson.xW 2 n β) i (pathV i) = dd (hSi n i) (halfK β n i) := by
  have hN : (2 : ℕ) ≠ 0 := by norm_num
  unfold p
  rw [DoublingWilson.xW_eq hN hβ hn he (pathV i) i, DoublingWilson.xW_eq hN hβ hn he (pathV i + E i) i,
    DoublingWilson.tr_ext_add, DoublingWilson.ext_add_self]
  have hext : DoublingWilson.ext n (pathV i) i = n := by simp [DoublingWilson.ext, pathV_self]
  rw [hext]
  unfold DoublingWilson.F traceSeq dd halfK
  have h2 : 2 * n / 2 - 1 = (n / 2 - 1) + (n / 2 - 1) + 1 := by obtain ⟨k, rfl⟩ := he; omega
  rw [h2, iter_add (bdd_kT hN hβ)]

/-- **The defect along the corner path**: `defectW = 8p₀ + 4p₁ + 2p₂ + p₃`. -/
theorem defectW_eq {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    ZoomSelfScale.defectW 2 β n = 8 * dd (hSi n 0) (halfK β n 0) + 4 * dd (hSi n 1) (halfK β n 1)
      + 2 * dd (hSi n 2) (halfK β n 2) + dd (hSi n 3) (halfK β n 3) := by
  have hΔ : ZoomSelfScale.defectW 2 β n = Δ (DoublingWilson.xW 2 n β) (corner 0) := by
    rw [DoublingWilson.Δ_corner0]; rfl
  rw [hΔ, ← p_eq_dd hβ hn he 0, ← p_eq_dd hβ hn he 1, ← p_eq_dd hβ hn he 2, ← p_eq_dd hβ hn he 3]
  unfold Δ p
  rw [path_step0, path_step1, path_step2, path_last, path_first]
  ring

/-! ## 3. The two sector statements give the seed -/

/-- One step: small flux share and small trivial defect give a small step defect. -/
theorem dd_halfK_le_of_sectors {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    (hf : fluxShare β n i ≤ 1 / 80000) (ht : trivialDefect β n i ≤ 1 / 80000) :
    dd (hSi n i) (halfK β n i) ≤ 1 / 16000 := by
  have hc := floor_pos β n i
  have hadm := adm_halfK hβ n i
  set A := hs (hSi n i) (halfK β n i) with hAdef
  set B := hs (hSi n i) (trivK β n i) with hBdef
  have hA : 0 < A := hs_pos_of_adm hc hadm
  have hB : 0 < B := hs_pos_of_adm hc (adm_trivK hβ n i)
  have h1 : A - B ≤ A / 80000 := by
    have := (div_le_iff₀ hA).mp hf
    linarith
  have h2 : Real.log A - Real.log B ≤ (A - B) / B := by
    rw [← Real.log_div hA.ne' hB.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hA hB)
    have e : (A - B) / B = A / B - 1 := by rw [sub_div, div_self hB.ne']
    linarith
  have h3 : (A - B) / B ≤ 2 / 80000 := by
    rw [div_le_iff₀ hB]
    linarith
  have hdd : dd (hSi n i) (halfK β n i)
      ≤ dd (hSi n i) (trivK β n i) + 2 * (Real.log A - Real.log B) :=
    dd_le_evL hc (flips i (Tr n i)) (halfK β n i) flips_spec hadm
  have ht' : dd (hSi n i) (trivK β n i) ≤ 1 / 80000 := ht
  linarith

/-- **Sufficiency at one side.** -/
theorem defectW_le_of_sectors {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : ∀ i : Fin 4, fluxShare β n i ≤ 1 / 80000 ∧ trivialDefect β n i ≤ 1 / 80000) :
    ZoomSelfScale.defectW 2 β n ≤ 1 / 1000 := by
  have hs := fun i => dd_halfK_le_of_sectors hβ n i (h i).1 (h i).2
  rw [defectW_eq hβ hn he]
  linarith [hs 0, hs 1, hs 2, hs 3]

/-- **Necessity at one side.** A defect at most `δ ≤ 1/1000` bounds the flux share by `4δ` and the
trivial defect by `2δ` at every step. -/
theorem sectors_of_defectW {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) (hd : ZoomSelfScale.defectW 2 β n ≤ δ) (i : Fin 4) :
    fluxShare β n i ≤ 4 * δ ∧ trivialDefect β n i ≤ 2 * δ := by
  have hc := fun j => floor_pos β n j
  have hnn := fun j => dd_nonneg (ν := hSi n j) (hc j) (adm_halfK hβ n j)
  have hsum := defectW_eq hβ hn he
  have hp : dd (hSi n i) (halfK β n i) ≤ δ := by
    fin_cases i
    · show dd (hSi n 0) (halfK β n 0) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSi n 1) (halfK β n 1) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSi n 2) (halfK β n 2) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSi n 3) (halfK β n 3) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
  have hadm := adm_halfK hβ n i
  have hadmT := adm_trivK hβ n i
  set A := hs (hSi n i) (halfK β n i) with hAdef
  set B := hs (hSi n i) (trivK β n i) with hBdef
  set D := hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i)) with hDdef
  set Dk := hs (hSi n i) (conv (hSi n i) (trivK β n i) (trivK β n i)) with hDkdef
  have hA : 0 < A := hs_pos_of_adm (hc i) hadm
  have hB : 0 < B := hs_pos_of_adm (hc i) hadmT
  have hD : 0 < D := hs_conv_pos_of_adm (hc i) hadm
  have hDk : 0 < Dk := hs_conv_pos_of_adm (hc i) hadmT
  -- the defect bound as a lower bound on the doubled trace
  have hlog : Real.log (A ^ 2) - δ ≤ Real.log D := by
    have : 2 * Real.log A - Real.log D ≤ δ := hp
    rw [Real.log_pow]; push_cast; linarith
  have hexp : 1 - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ); linarith
  have hD1 : A ^ 2 * Real.exp (-δ) ≤ D := by
    calc A ^ 2 * Real.exp (-δ) = Real.exp (Real.log (A ^ 2) + -δ) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = D := Real.exp_log hD
  have hD2 : A ^ 2 * (1 - δ) ≤ D := by
    have : A ^ 2 * (1 - δ) ≤ A ^ 2 * Real.exp (-δ) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith
  -- the sector bounds
  have hconv : D ≤ Dk + (A - B) ^ 2 := hs_conv_le_evL _ _ flips_spec hadm
  have hDkB : Dk ≤ B * B := hs_conv_le_mul hadmT.bdd hadmT.bdd
  have hBA : B ≤ A := hs_evL_le _ _ flips_spec hadm
  have hB8 : A / 8 ≤ B := by
    have h8 : A / 2 ^ (flips i (Tr n i)).length ≤ B := hs_evL_ge (hc i).le _ _ flips_spec hadm
    rw [flips_length] at h8
    have e : A / 2 ^ 3 = A / 8 := by norm_num
    rw [e] at h8
    exact h8
  have hAB : 0 ≤ A - B := by linarith
  have hkey : 2 * B * (A - B) ≤ δ * A ^ 2 := by nlinarith
  have hflux : A - B ≤ 4 * δ * A := by
    have h1 : A / 4 * (A - B) ≤ 2 * B * (A - B) := mul_le_mul_of_nonneg_right (by linarith) hAB
    have h2 : A * (A - B) ≤ A * (4 * δ * A) := by nlinarith
    exact le_of_mul_le_mul_left h2 hA
  refine ⟨?_, ?_⟩
  · show (A - B) / A ≤ 4 * δ
    rw [div_le_iff₀ hA]; linarith
  · show dd (hSi n i) (evL (halfK β n i) (flips i (Tr n i))) ≤ 2 * δ
    have hsq : (A - B) ^ 2 ≤ (4 * δ * A) ^ 2 := pow_le_pow_left₀ hAB hflux 2
    have hDk2 : A ^ 2 * (1 - δ - 16 * δ ^ 2) ≤ Dk := by nlinarith
    have hB2 : B ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hB.le hBA 2
    have hq : 0 ≤ 1 - 18 * δ - 32 * δ ^ 2 := by nlinarith
    have hpoly : 1 ≤ (1 + 2 * δ) * (1 - δ - 16 * δ ^ 2) := by nlinarith [mul_nonneg hδ0 hq]
    have hA2 : A ^ 2 ≤ (1 + 2 * δ) * (A ^ 2 * (1 - δ - 16 * δ ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hpoly (sq_nonneg A)
      calc A ^ 2 = A ^ 2 * 1 := by ring
        _ ≤ A ^ 2 * ((1 + 2 * δ) * (1 - δ - 16 * δ ^ 2)) := this
        _ = (1 + 2 * δ) * (A ^ 2 * (1 - δ - 16 * δ ^ 2)) := by ring
    have hA3 : (1 + 2 * δ) * (A ^ 2 * (1 - δ - 16 * δ ^ 2)) ≤ (1 + 2 * δ) * Dk :=
      mul_le_mul_of_nonneg_left hDk2 (by linarith)
    have hratio : B ^ 2 / Dk ≤ 1 + 2 * δ := by
      rw [div_le_iff₀ hDk]; linarith
    have hlogB : 2 * Real.log B - Real.log Dk ≤ B ^ 2 / Dk - 1 := by
      have := Real.log_le_sub_one_of_pos (div_pos (pow_pos hB 2) hDk)
      rw [Real.log_div (pow_pos hB 2).ne' hDk.ne', Real.log_pow] at this
      push_cast at this
      linarith
    have : dd (hSi n i) (evL (halfK β n i) (flips i (Tr n i))) = 2 * Real.log B - Real.log Dk := rfl
    rw [this]
    linarith

/-- Three sharp squarings: a seed at an even side `n ≥ 2` gives `defectW(8n) ≤ 1/16384000`. -/
theorem defectW_eight_le {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : ZoomSelfScale.defectW 2 β n ≤ 1 / 1000) :
    ZoomSelfScale.defectW 2 β (2 ^ 3 * n) ≤ 1 / 16384000 := by
  have hN : (2 : ℕ) ≠ 0 := by norm_num
  have hfr := DoublingWilson.factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (DoublingWilson.xW 2 n β) (corner 0) ≤ 1 / 1000 := by
    rw [DoublingWilson.Δ_corner0]; exact h
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) 3
  rw [← WDeltaRun.Δ_corner]
  norm_num at hi ⊢
  linarith

/-! ## 4. Along the couplings -/

/-- **The sector seed on power-of-two sides**: eventually in `β`, some `2ᵇ` has, at every step of
the corner path, flux share and trivial-sector defect at most `1/80000`.

CHOSEN: `1/80000` so that `15 · 5/80000 ≤ 1/1000`, the `RunSeed` threshold `defectW_le_of_sectors`
feeds; a smaller value would only make the seed harder to meet. -/
def SectorSeedPow : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
    ∀ i : Fin 4, fluxShare β (2 ^ b) i ≤ 1 / 80000 ∧ trivialDefect β (2 ^ b) i ≤ 1 / 80000

/-- **The sector seed gives (A₂) for SU(2).** -/
theorem seedExistsPow_of_sectorSeedPow (h : SectorSeedPow) : DeltaLengthTower.SeedExistsPow 2 := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hs⟩ hβ
  exact ⟨b, hb, defectW_le_of_sectors hβ (DeltaLengthTower.two_le_two_pow hb)
    (DeltaLengthTower.even_two_pow hb) hs⟩

/-- **(A₂) for SU(2) gives the sector seed**: three sharp squarings beyond a seed side bring the
defect below `1/320000`, and necessity at that side gives both sector bounds at `1/80000`. -/
theorem sectorSeedPow_of_seedExistsPow (h : DeltaLengthTower.SeedExistsPow 2) : SectorSeedPow := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hd⟩ hβ
  have h8 := defectW_eight_le hβ (DeltaLengthTower.two_le_two_pow hb)
    (DeltaLengthTower.even_two_pow hb) hd
  rw [← pow_add] at h8
  have hb3 : 1 ≤ 3 + b := by omega
  refine ⟨3 + b, hb3, fun i => ?_⟩
  have := sectors_of_defectW hβ (DeltaLengthTower.two_le_two_pow hb3)
    (DeltaLengthTower.even_two_pow hb3) (δ := 1 / 320000) (by norm_num) (by norm_num)
    (by linarith) i
  constructor <;> linarith [this.1, this.2]

/-- **(A₂) for SU(2) is the sector seed.** -/
theorem seedExistsPow_iff_sectorSeedPow : DeltaLengthTower.SeedExistsPow 2 ↔ SectorSeedPow :=
  ⟨sectorSeedPow_of_seedExistsPow, seedExistsPow_of_sectorSeedPow⟩

end MassGap.CentreSectorSeed

end

#print axioms MassGap.CentreSectorSeed.kT_flip
#print axioms MassGap.CentreSectorSeed.defectW_eq
#print axioms MassGap.CentreSectorSeed.defectW_le_of_sectors
#print axioms MassGap.CentreSectorSeed.sectors_of_defectW
#print axioms MassGap.CentreSectorSeed.seedExistsPow_of_sectorSeedPow
#print axioms MassGap.CentreSectorSeed.seedExistsPow_iff_sectorSeedPow
