import Mathlib
import MassGap.FluxShareSquaring

/-!
# MassGap.TrivialSectorDefect — the trivial-sector defect against the step defect, and the two parts of the SU(2) seed stated apart

`CentreSectorSeed.SectorSeedPow` asks, at each large `β`, for one power-of-two side `2ᵇ` at which every
step of the corner path has a small flux share (`fluxShare`) and a small trivial-sector defect
(`trivialDefect`, the doubling defect of the zero-flux kernel `trivK`). This module relates the trivial
part to the step defect and separates the two parts.

**1. Time doubling acts on the trivial sector alone** (`trivK_doubled`, `trivialDefectDoubled_eq`). The
zero-flux kernel of the transfer over twice the time extent is `trivK ∗ trivK`: the trivial sector of the
doubled torus is a function of the trivial sector of the original one, and the flux sectors do not enter.
Flux feeds nothing into the trivial sector along the transfer direction. The reverse feed exists:
`FluxShareSquaring.fluxShareDoubled_le` squares the flux odds at the cost `exp(trivialDefect)`.

**2. At a common side the trivial part is the step defect, up to the flux share.** With `p` the step
defect `dd(halfK)` and `f` the flux share,

    p + 2 log(1 − f) ≤ trivialDefect ≤ p − log(1 − f² e^p)

(`trivialDefect_ge_step`, `trivialDefect_le_step`; the second needs `f² e^p < 1`). So once the flux share
is small, the trivial part and the step defect are the same statement.

**3. The two parts stated apart** (`sectorSeedPow_iff_fluxEventually_trivialFrequently`,
`sectorSeedPow_iff_fluxFrequently_trivialEventually`). For predicates `P, Q` on the sides, the joint
statement "some side carries both" is equivalent to "`P` at all large sides and `Q` at arbitrarily large
sides" as soon as the joint statement climbs to all large sides (`iff_eventually_and_frequently`). For
SU(2) it climbs: a seed at `2ᵇ` is a seed at every `2ᶜ`, `c ≥ b` (`DeltaLengthTower.seedPow_mono`), three
sharp squarings put the defect below `1/320000` at every `2ᶜ`, `c ≥ b + 3`, and `sectors_of_defectW` gives
both parts there (`eventually_sectorsAt`). Hence

    SectorSeedPow ↔ FluxPartEventually ∧ TrivialPartFrequently
                  ↔ FluxPartFrequently ∧ TrivialPartEventually,

each conjunct a statement about one sector at sides of its own choosing. The equivalences hold with the
same thresholds as `SectorSeedPow`; no threshold is moved.

DERIVED (module-wide): `1/80000` is `SectorSeedPow`'s threshold; `3` is the number of sharp squarings of
`CentreSectorSeed.defectW_eight_le`; `1/320000 = (1/80000)/4` is the defect at which `sectors_of_defectW`
returns `4δ = 1/80000` and `2δ ≤ 1/80000`; `2` in `2 log` is the square in `hs`.
-/

noncomputable section

namespace MassGap.TrivialSectorDefect

open MeasureTheory Filter MassGap.KernelPower MassGap.SectorDefect MassGap.CentreSectorSeed
  MassGap.FluxShareSquaring

/-! ## 1. Time doubling acts on the trivial sector alone -/

/-- **The zero-flux kernel of the time-doubled transfer is the doubled zero-flux kernel.** -/
theorem trivK_doubled {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    evL (conv (hSi n i) (halfK β n i) (halfK β n i)) (flips i (Tr n i))
      = conv (hSi n i) (trivK β n i) (trivK β n i) :=
  evL_conv (flips i (Tr n i)) (halfK β n i) flips_spec (adm_halfK hβ n i)

/-- The trivial-sector defect of the torus doubled along the transfer direction. -/
def trivialDefectDoubled (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  dd (hSi n i) (evL (conv (hSi n i) (halfK β n i) (halfK β n i)) (flips i (Tr n i)))

/-- **The time-doubled trivial defect is a function of the trivial kernel alone.** -/
theorem trivialDefectDoubled_eq {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    trivialDefectDoubled β n i = dd (hSi n i) (conv (hSi n i) (trivK β n i) (trivK β n i)) := by
  unfold trivialDefectDoubled
  rw [trivK_doubled hβ n i]

/-! ## 2. The trivial defect against the step defect -/

/-- The real-number step of `trivialDefect_le_step`. -/
theorem le_step_real {A B D Dk p f : ℝ} (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hBA : B ≤ A) (hconv : D ≤ Dk + (A - B) ^ 2) (hp : p = 2 * Real.log A - Real.log D)
    (hf : f * A = A - B) (hq : f ^ 2 * Real.exp p < 1) :
    2 * Real.log B - Real.log Dk ≤ p - Real.log (1 - f ^ 2 * Real.exp p) := by
  have hE : 0 < Real.exp p := Real.exp_pos p
  have hA2 : 0 < A ^ 2 := pow_pos hA 2
  have hexp : Real.exp p = A ^ 2 / D := by
    rw [hp, Real.exp_sub, Real.exp_log hD,
      show (2 : ℝ) * Real.log A = Real.log (A ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log hA2]
  have hAD : A ^ 2 / Real.exp p = D := by
    rw [hexp, div_div_eq_mul_div, mul_div_cancel_left₀ _ hA2.ne']
  have hq0 : 0 < 1 - f ^ 2 * Real.exp p := by linarith
  have h1 : A ^ 2 * (1 - f ^ 2 * Real.exp p) / Real.exp p = A ^ 2 / Real.exp p - (f * A) ^ 2 := by
    field_simp
  have hlow : A ^ 2 * (1 - f ^ 2 * Real.exp p) / Real.exp p ≤ Dk := by
    rw [h1, hAD, hf]; linarith
  have hpos : 0 < A ^ 2 * (1 - f ^ 2 * Real.exp p) / Real.exp p :=
    div_pos (mul_pos hA2 hq0) hE
  have hlog1 := Real.log_le_log hpos hlow
  rw [Real.log_div (mul_pos hA2 hq0).ne' hE.ne', Real.log_mul hA2.ne' hq0.ne', Real.log_exp,
    Real.log_pow] at hlog1
  have hlogB : Real.log B ≤ Real.log A := Real.log_le_log hB hBA
  push_cast at hlog1
  linarith

/-- **Upper bound**: `trivialDefect ≤ p − log(1 − f² e^p)` when `f² e^p < 1`, with `p` the step defect
and `f` the flux share. -/
theorem trivialDefect_le_step {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    (hq : fluxShare β n i ^ 2 * Real.exp (dd (hSi n i) (halfK β n i)) < 1) :
    trivialDefect β n i ≤ dd (hSi n i) (halfK β n i)
      - Real.log (1 - fluxShare β n i ^ 2 * Real.exp (dd (hSi n i) (halfK β n i))) := by
  have hc := CentreSectorSeed.floor_pos β n i
  have hadm := adm_halfK hβ n i
  have hadmT := adm_trivK hβ n i
  have hA : 0 < hs (hSi n i) (halfK β n i) := hs_pos_of_adm hc hadm
  have hB : 0 < hs (hSi n i) (trivK β n i) := hs_pos_of_adm hc hadmT
  have hD : 0 < hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i)) :=
    hs_conv_pos_of_adm hc hadm
  have hBA : hs (hSi n i) (trivK β n i) ≤ hs (hSi n i) (halfK β n i) :=
    hs_evL_le _ _ flips_spec hadm
  have hconv : hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
      ≤ hs (hSi n i) (conv (hSi n i) (trivK β n i) (trivK β n i))
        + (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) ^ 2 :=
    hs_conv_le_evL _ _ flips_spec hadm
  have hf : fluxShare β n i * hs (hSi n i) (halfK β n i)
      = hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i) := by
    show (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) / hs (hSi n i) (halfK β n i)
        * hs (hSi n i) (halfK β n i) = _
    exact div_mul_cancel₀ _ hA.ne'
  exact le_step_real hA hB hD hBA hconv rfl hf hq

/-- **Lower bound**: `p + 2 log(1 − f) ≤ trivialDefect` (`SectorDefect.dd_le_evL`). -/
theorem trivialDefect_ge_step {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    dd (hSi n i) (halfK β n i) + 2 * Real.log (1 - fluxShare β n i) ≤ trivialDefect β n i := by
  have hc := CentreSectorSeed.floor_pos β n i
  have hadm := adm_halfK hβ n i
  have hA : 0 < hs (hSi n i) (halfK β n i) := hs_pos_of_adm hc hadm
  have hB : 0 < hs (hSi n i) (trivK β n i) := hs_pos_of_adm hc (adm_trivK hβ n i)
  have h1 : dd (hSi n i) (halfK β n i) ≤ trivialDefect β n i
      + 2 * (Real.log (hs (hSi n i) (halfK β n i)) - Real.log (hs (hSi n i) (trivK β n i))) :=
    dd_le_evL hc (flips i (Tr n i)) (halfK β n i) flips_spec hadm
  have e : 1 - fluxShare β n i = hs (hSi n i) (trivK β n i) / hs (hSi n i) (halfK β n i) := by
    show 1 - (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) / hs (hSi n i) (halfK β n i)
      = _
    rw [sub_div, div_self hA.ne']; ring
  rw [e, Real.log_div hB.ne' hA.ne']
  linarith

/-! ## 3. Two per-side statements, stated apart -/

section Abstract

variable {P Q : ℝ → ℕ → Prop}

/-- **The joint statement splits as "one at all large sides, the other at arbitrarily large sides"**,
provided it climbs: a side carrying both gives all large sides carrying both. -/
theorem iff_eventually_and_frequently
    (hclimb : (∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ P β b ∧ Q β b) →
      ∀ᶠ β in atTop, ∀ᶠ b in atTop, P β b ∧ Q β b) :
    (∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ P β b ∧ Q β b) ↔
      (∀ᶠ β in atTop, ∀ᶠ b in atTop, P β b) ∧ (∀ᶠ β in atTop, ∃ᶠ b in atTop, Q β b) := by
  constructor
  · intro h
    have hc := hclimb h
    refine ⟨hc.mono fun β hβ => hβ.mono fun b hb => hb.1, hc.mono fun β hβ => ?_⟩
    exact (hβ.mono fun b hb => hb.2).frequently
  · rintro ⟨hP, hQ⟩
    filter_upwards [hP, hQ] with β hp hq
    obtain ⟨b, ⟨hpb, hb1⟩, hqb⟩ := ((hp.and (eventually_ge_atTop 1)).and_frequently hq).exists
    exact ⟨b, hb1, hpb, hqb⟩

end Abstract

/-- The flux part at side `2ᵇ`.

DERIVED: `1/80000` is `SectorSeedPow`'s threshold (`CentreSectorSeedN`: `15 · 5/80000 ≤ 1/1000`). -/
def FluxAt (β : ℝ) (b : ℕ) : Prop := ∀ i : Fin 4, fluxShare β (2 ^ b) i ≤ 1 / 80000

/-- **The trivial part at side `2ᵇ`**: the zero-flux sector has doubling defect at most `1/80000` at
every step of the corner path.

DERIVED: `1/80000` is `SectorSeedPow`'s threshold (`CentreSectorSeedN`: `15 · 5/80000 ≤ 1/1000`). -/
def TrivialAt (β : ℝ) (b : ℕ) : Prop := ∀ i : Fin 4, trivialDefect β (2 ^ b) i ≤ 1 / 80000

/-- The flux part at all large dyadic sides. -/
def FluxPartEventually : Prop := ∀ᶠ β in atTop, ∀ᶠ b in atTop, FluxAt β b

/-- The flux part at arbitrarily large dyadic sides. -/
def FluxPartFrequently : Prop := ∀ᶠ β in atTop, ∃ᶠ b in atTop, FluxAt β b

/-- **The trivial part at all large dyadic sides.** -/
def TrivialPartEventually : Prop := ∀ᶠ β in atTop, ∀ᶠ b in atTop, TrivialAt β b

/-- **The trivial part at arbitrarily large dyadic sides.** -/
def TrivialPartFrequently : Prop := ∀ᶠ β in atTop, ∃ᶠ b in atTop, TrivialAt β b

theorem sectorSeedPow_iff_joint :
    SectorSeedPow ↔ ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ FluxAt β b ∧ TrivialAt β b := by
  unfold SectorSeedPow FluxAt TrivialAt
  constructor
  · intro h
    filter_upwards [h] with β ⟨b, hb, hs⟩
    exact ⟨b, hb, fun i => (hs i).1, fun i => (hs i).2⟩
  · intro h
    filter_upwards [h] with β ⟨b, hb, hf, ht⟩
    exact ⟨b, hb, fun i => ⟨hf i, ht i⟩⟩

/-- **(A₂) for SU(2) climbs**: eventually in `β`, every large dyadic side carries both parts. -/
theorem eventually_sectorsAt (h : DeltaLengthTower.SeedExistsPow 2) :
    ∀ᶠ β in atTop, ∀ᶠ b in atTop, FluxAt β b ∧ TrivialAt β b := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hd⟩ hβ
  filter_upwards [eventually_ge_atTop (b + 3)] with c hc
  have hc3 : 1 ≤ c - 3 := by omega
  have hm : ZoomSelfScale.defectW 2 β (2 ^ (c - 3)) ≤ 1 / 1000 :=
    DeltaLengthTower.seedPow_mono (by norm_num) hβ hb (by omega) hd
  have h8 := defectW_eight_le hβ (DeltaLengthTower.two_le_two_pow hc3)
    (DeltaLengthTower.even_two_pow hc3) hm
  rw [← pow_add, show 3 + (c - 3) = c by omega] at h8
  have hc1 : 1 ≤ c := by omega
  have hs := fun i => sectors_of_defectW hβ (DeltaLengthTower.two_le_two_pow hc1)
    (DeltaLengthTower.even_two_pow hc1) (δ := 1 / 320000) (by norm_num) (by norm_num)
    (by linarith) i
  exact ⟨fun i => by linarith [(hs i).1], fun i => by linarith [(hs i).2]⟩

theorem climb :
    (∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ FluxAt β b ∧ TrivialAt β b) →
      ∀ᶠ β in atTop, ∀ᶠ b in atTop, FluxAt β b ∧ TrivialAt β b := fun h =>
  eventually_sectorsAt (seedExistsPow_of_sectorSeedPow (sectorSeedPow_iff_joint.mpr h))

theorem climb_swap :
    (∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ TrivialAt β b ∧ FluxAt β b) →
      ∀ᶠ β in atTop, ∀ᶠ b in atTop, TrivialAt β b ∧ FluxAt β b := fun h =>
  (climb (h.mono fun _ ⟨b, hb, ht, hf⟩ => ⟨b, hb, hf, ht⟩)).mono fun _ hβ =>
    hβ.mono fun _ hb => ⟨hb.2, hb.1⟩

/-- **The SU(2) sector seed is the flux part at all large sides together with the trivial part at
arbitrarily large sides.** -/
theorem sectorSeedPow_iff_fluxEventually_trivialFrequently :
    SectorSeedPow ↔ FluxPartEventually ∧ TrivialPartFrequently := by
  rw [sectorSeedPow_iff_joint]
  exact iff_eventually_and_frequently climb

/-- **The SU(2) sector seed is the trivial part at all large sides together with the flux part at
arbitrarily large sides.** -/
theorem sectorSeedPow_iff_fluxFrequently_trivialEventually :
    SectorSeedPow ↔ FluxPartFrequently ∧ TrivialPartEventually := by
  rw [sectorSeedPow_iff_joint]
  have h := iff_eventually_and_frequently (P := TrivialAt) (Q := FluxAt) climb_swap
  have e : (∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ FluxAt β b ∧ TrivialAt β b)
      ↔ ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ TrivialAt β b ∧ FluxAt β b := by
    constructor
    · exact fun h => h.mono fun _ ⟨b, hb, hf, ht⟩ => ⟨b, hb, ht, hf⟩
    · exact fun h => h.mono fun _ ⟨b, hb, ht, hf⟩ => ⟨b, hb, hf, ht⟩
  rw [e, h]
  exact and_comm

/-- **(A₂) for SU(2), stated apart.** -/
theorem seedExistsPow_iff_fluxEventually_trivialFrequently :
    DeltaLengthTower.SeedExistsPow 2 ↔ FluxPartEventually ∧ TrivialPartFrequently :=
  seedExistsPow_iff_sectorSeedPow.trans sectorSeedPow_iff_fluxEventually_trivialFrequently

theorem seedExistsPow_iff_fluxFrequently_trivialEventually :
    DeltaLengthTower.SeedExistsPow 2 ↔ FluxPartFrequently ∧ TrivialPartEventually :=
  seedExistsPow_iff_sectorSeedPow.trans sectorSeedPow_iff_fluxFrequently_trivialEventually

/-- The frequent trivial part gives the trivial conjunct of `SectorSeedPow` at some side `2ᵇ`, `b ≥ 1`. -/
theorem exists_trivialAt_of_frequently (h : TrivialPartFrequently) :
    ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ TrivialAt β b := by
  filter_upwards [h] with β hβ
  obtain ⟨b, hb1, hb⟩ := ((eventually_ge_atTop 1).and_frequently hβ).exists
  exact ⟨b, hb1, hb⟩

end MassGap.TrivialSectorDefect

end

#print axioms MassGap.TrivialSectorDefect.trivK_doubled
#print axioms MassGap.TrivialSectorDefect.trivialDefectDoubled_eq
#print axioms MassGap.TrivialSectorDefect.trivialDefect_le_step
#print axioms MassGap.TrivialSectorDefect.trivialDefect_ge_step
#print axioms MassGap.TrivialSectorDefect.iff_eventually_and_frequently
#print axioms MassGap.TrivialSectorDefect.eventually_sectorsAt
#print axioms MassGap.TrivialSectorDefect.sectorSeedPow_iff_fluxEventually_trivialFrequently
#print axioms MassGap.TrivialSectorDefect.sectorSeedPow_iff_fluxFrequently_trivialEventually
#print axioms MassGap.TrivialSectorDefect.seedExistsPow_iff_fluxEventually_trivialFrequently
#print axioms MassGap.TrivialSectorDefect.seedExistsPow_iff_fluxFrequently_trivialEventually
