import Mathlib
import MassGap.WeightedProduct

noncomputable section

/-!
# MassGap.WeightedProfile15 — the weighted box criterion at box side 15, with explicit weights

An instance of `WeightedProduct.ProfileData 15`: integer profiles `f` (across a link) and `g` (along it),
the sampled `sin^0.15` profile at the link midpoints of the box (`research/code/lab/emit_profile.py`),
with every finite correlation bound checked by `decide`. Its threshold is

    (a₂ − K + e) · 15⁴ / a₁² = 5308617107446623908889550801875 / 69954790179518989117503537761344 ≈ 0.07589,

so `clay15` states the continuum Clay conclusion from `BoxGap.BoxFibreGap hN β₀ 15 γ` at any
`γ > 0.0759`, with the UV step, E, N and Y.
-/

namespace MassGap.WeightedProfile15

open MassGap MassGap.WeightedProduct

/-- The profile across a link (sites `0 … 14` of the box). DERIVED: sampled values, scale 1000. -/
def fL : List ℕ := [713, 838, 901, 942, 969, 987, 997, 1000, 997, 987, 969, 942, 901, 838, 713]

/-- The profile along a link (links `0 … 13`). DERIVED: sampled values, scale 1000. -/
def gL : List ℕ := [790, 874, 923, 956, 979, 993, 999, 999, 993, 979, 956, 923, 874, 790]

def fl (t : ℕ) : ℕ := fL.getD t 0
def gl (t : ℕ) : ℕ := gL.getD t 0

theorem ff_fw_n : ∀ D, D < 15 → (Finset.range 15).sum (fun t => fl t * fl (t + D)) ≤ 12633834 := by decide

theorem ff_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => fl (t + r) * fl t) ≤ 12633834 := by decide

theorem gg_fw_n : ∀ D, D < 15 → (Finset.range 15).sum (fun t => gl t * gl (t + D)) ≤ 12192664 := by decide

theorem gg_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => gl (t + r) * gl t) ≤ 12192664 := by decide

theorem gf_fw_n : ∀ D, D < 15 → (Finset.range 15).sum (fun t => gl t * fl (t + D)) ≤ 12153220 := by decide

theorem gf_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => gl (t + r) * fl t) ≤ 12153220 := by decide

theorem fg_fw_n : ∀ D, D < 15 → (Finset.range 15).sum (fun t => fl t * gl (t + D)) ≤ 12153220 := by decide

theorem fg_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => fl (t + r) * gl t) ≤ 12153220 := by decide

theorem ffnz_fw_n : ∀ D, 1 ≤ D → D < 15 → (Finset.range 15).sum (fun t => fl t * fl (t + D)) ≤ 12103028 := by decide

theorem ffnz_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => fl (t + r) * fl t) ≤ 12103028 := by decide

theorem ggnz_fw_n : ∀ D, 1 ≤ D → D < 15 → (Finset.range 15).sum (fun t => gl t * gl (t + D)) ≤ 11557257 := by decide

theorem ggnz_bw_n : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => gl (t + r) * gl t) ≤ 11557257 := by decide

theorem fl_le (t : ℕ) : fl t ≤ 1000 := by
  unfold fl
  rcases lt_or_ge t 15 with h | h
  · interval_cases t <;> decide
  · rw [List.getD_eq_default (l := fL) (d := 0) (by simp [fL]; omega)]; norm_num

theorem gl_le (t : ℕ) : gl t ≤ 1000 := by
  unfold gl
  rcases lt_or_ge t 14 with h | h
  · interval_cases t <;> decide
  · rw [List.getD_eq_default (l := gL) (d := 0) (by simp [gL]; omega)]; norm_num

theorem fl_zero (t : ℕ) (h : 15 ≤ t) : fl t = 0 := by
  unfold fl; exact List.getD_eq_default (l := fL) (d := 0) (by simp [fL]; omega)

theorem gl_zero (t : ℕ) (h : 15 ≤ t) : gl t = 0 := by
  unfold gl; exact List.getD_eq_default (l := gL) (d := 0) (by simp [gL]; omega)

/-- Real form of a forward check. -/
theorem fw_real (u v : ℕ → ℕ) (U : ℕ)
    (h : ∀ D, D < 15 → (Finset.range 15).sum (fun t => u t * v (t + D)) ≤ U) :
    ∀ D, D < 15 → ∑ t ∈ Finset.range 15, (u t : ℝ) * (v (t + D) : ℝ) ≤ (U : ℝ) := by
  intro D hD; exact_mod_cast h D hD

theorem fwnz_real (u v : ℕ → ℕ) (U : ℕ)
    (h : ∀ D, 1 ≤ D → D < 15 → (Finset.range 15).sum (fun t => u t * v (t + D)) ≤ U) :
    ∀ D, 1 ≤ D → D < 15 → ∑ t ∈ Finset.range 15, (u t : ℝ) * (v (t + D) : ℝ) ≤ (U : ℝ) := by
  intro D h1 hD; exact_mod_cast h D h1 hD

theorem bw_real (u v : ℕ → ℕ) (U : ℕ)
    (h : ∀ r, 1 ≤ r → r < 15 → (Finset.range 15).sum (fun t => u (t + r) * v t) ≤ U) :
    ∀ r, 1 ≤ r → r < 15 → ∑ t ∈ Finset.range 15, (u (t + r) : ℝ) * (v t : ℝ) ≤ (U : ℝ) := by
  intro r h1 hr; exact_mod_cast h r h1 hr


/-- **The profile data at box side 15.**

DERIVED: computed -- `15` the box side; `1000` the profile scale of `fL`, `gL` (bounds `fl_le`, `gl_le`);
`12633834`, `12192664`, `12153220`, `12103028`, `11557257` the correlation sums of the sampled profiles
(`research/code/lab/emit_profile.py`), checked by `decide` in `ff_fw_n` … `ggnz_bw_n`. -/
def P15 : ProfileData 15 where
  f := fun t => (fl t : ℝ)
  g := fun t => (gl t : ℝ)
  fM := 1000
  gM := 1000
  f_nn := fun t => Nat.cast_nonneg _
  g_nn := fun t => Nat.cast_nonneg _
  f_le := fun t => by exact_mod_cast fl_le t
  g_le := fun t => by exact_mod_cast gl_le t
  f_zero := fun t h => by simp [fl_zero t h]
  g_zero := fun t h => by simp [gl_zero t h]
  Uff := (12633834 : ℕ)
  Ugg := (12192664 : ℕ)
  Ugf := (12153220 : ℕ)
  Ufg := (12153220 : ℕ)
  Unzff := (12103028 : ℕ)
  Unzgg := (11557257 : ℕ)
  Uff_nn := Nat.cast_nonneg _
  Ugg_nn := Nat.cast_nonneg _
  Ugf_nn := Nat.cast_nonneg _
  Ufg_nn := Nat.cast_nonneg _
  Unzff_nn := Nat.cast_nonneg _
  Unzgg_nn := Nat.cast_nonneg _
  ff_fw := fw_real fl fl _ ff_fw_n
  ff_bw := bw_real fl fl _ ff_bw_n
  gg_fw := fw_real gl gl _ gg_fw_n
  gg_bw := bw_real gl gl _ gg_bw_n
  gf_fw := fw_real gl fl _ gf_fw_n
  gf_bw := bw_real gl fl _ gf_bw_n
  fg_fw := fw_real fl gl _ fg_fw_n
  fg_bw := bw_real fl gl _ fg_bw_n
  ffnz_fw := fwnz_real fl fl _ ffnz_fw_n
  ffnz_bw := bw_real fl fl _ ffnz_bw_n
  ggnz_fw := fwnz_real gl gl _ ggnz_fw_n
  ggnz_bw := bw_real gl gl _ ggnz_bw_n

theorem fc_ff0 : ProfileData.fc (n := 15) P15.f P15.f 0 = (12633834 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => fl t * fl (t + 0)) = 12633834 := by decide
  show ∑ t ∈ Finset.range 15, ((fl t : ℕ) : ℝ) * ((fl (t + 0) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_ff1 : ProfileData.fc (n := 15) P15.f P15.f 1 = (12103028 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => fl t * fl (t + 1)) = 12103028 := by decide
  show ∑ t ∈ Finset.range 15, ((fl t : ℕ) : ℝ) * ((fl (t + 1) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_gg0 : ProfileData.fc (n := 15) P15.g P15.g 0 = (12192664 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => gl t * gl (t + 0)) = 12192664 := by decide
  show ∑ t ∈ Finset.range 15, ((gl t : ℕ) : ℝ) * ((gl (t + 0) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_gg1 : ProfileData.fc (n := 15) P15.g P15.g 1 = (11557257 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => gl t * gl (t + 1)) = 11557257 := by decide
  show ∑ t ∈ Finset.range 15, ((gl t : ℕ) : ℝ) * ((gl (t + 1) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_gf0 : ProfileData.fc (n := 15) P15.g P15.f 0 = (12153220 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => gl t * fl (t + 0)) = 12153220 := by decide
  show ∑ t ∈ Finset.range 15, ((gl t : ℕ) : ℝ) * ((fl (t + 0) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_gf1 : ProfileData.fc (n := 15) P15.g P15.f 1 = (12153220 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => gl t * fl (t + 1)) = 12153220 := by decide
  show ∑ t ∈ Finset.range 15, ((gl t : ℕ) : ℝ) * ((fl (t + 1) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem fc_fg0 : ProfileData.fc (n := 15) P15.f P15.g 0 = (12153220 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => fl t * gl (t + 0)) = 12153220 := by decide
  show ∑ t ∈ Finset.range 15, ((fl t : ℕ) : ℝ) * ((gl (t + 0) : ℕ) : ℝ) = _
  exact_mod_cast h

theorem sum_f : ∑ t ∈ Finset.range 15, P15.f t = (13694 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => fl t) = 13694 := by decide
  show ∑ t ∈ Finset.range 15, ((fl t : ℕ) : ℝ) = _
  exact_mod_cast h

theorem sum_g : ∑ t ∈ Finset.range 15, P15.g t = (13028 : ℝ) := by
  have h : (Finset.range 15).sum (fun t => gl t) = 13028 := by decide
  show ∑ t ∈ Finset.range 15, ((gl t : ℕ) : ℝ) = _
  exact_mod_cast h

theorem K15 : P15.K = (23575073306197854855508430400 : ℝ) := by
  unfold ProfileData.K P15
  simp only [max_def]
  norm_num

/-- **The threshold at box side 15**: `(a₂ − K + e) · 15⁴ / a₁² < 0.0759`
(exactly `5308617107446623908889550801875 / 69954790179518989117503537761344`). -/
theorem thr15 : (P15.a₂ - P15.K + P15.e) * ((15 : ℕ) : ℝ) ^ 4 / P15.a₁ ^ 2 < 759 / 10000 := by
  unfold ProfileData.a₂ ProfileData.e ProfileData.a₁
  rw [K15, fc_ff0, fc_ff1, fc_gg0, fc_gg1, fc_gf0, fc_gf1, fc_fg0, sum_f, sum_g]
  norm_num

#print axioms thr15

theorem K15_pos : 0 < P15.K := by rw [K15]; norm_num

theorem a15_ne : P15.a₁ ≠ 0 := by
  unfold ProfileData.a₁; rw [sum_f, sum_g]; norm_num

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one box of side 15.** At `2 ≤ N`, `0 < L`, `0 < β₀`,
`βUV ≤ β₀`: the box check `BoxGap.BoxFibreGap hN β₀ 15 γ` at some `γ ≥ 0.0759`, the UV step below the
box's rate, and E, N, Y give `ClayRoutes.ClayContinuum hN Z τ hZ hB L`.

DERIVED: `15` the box side; `0.0759` rounds the threshold `≈ 0.07589` up; `2` the least rank with a
non-zero Haar variance; `0` the excluded colour count and lower ends; `4` the spacetime dimension;
`759/10000 = 0.0759`, the rounded threshold of `thr15`. -/
theorem clay15 {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hγ : 759 / 10000 ≤ γ)
    (hbox : BoxGap.BoxFibreGap hN β₀ 15 γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV
      (MassGap.WeightedBox.weightedRate N β₀
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e γ)))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_profile hN2 hN Z τ hZ hB hL P15 hβ₀ hUVβ₀ (by norm_num)
    (lt_of_lt_of_le (by norm_num) hγ) K15_pos a15_ne (lt_of_lt_of_le thr15 hγ) hbox huv O G hconv hY

#print axioms clay15

end MassGap.WeightedProfile15
