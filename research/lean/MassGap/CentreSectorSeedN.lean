import Mathlib
import MassGap.ZeroFluxSector
import MassGap.SliceCentreAction

/-!
# MassGap.CentreSectorSeedN — the SU(N) seed is a flux-sector bound and a zero-flux bound

This is `CentreSectorSeed` for every `N ≥ 1`, with the centre `Z_N³` of `SliceCentreAction` in place
of the three `Z₂` flips.

`defectW N β n = 8p₀ + 4p₁ + 2p₂ + p₃` along the corner path (`defectW_eqN`), each `pᵢ` the doubling
defect `dd(halfKN N β n i)` of the transfer over half the time extent on the slice of step `i`. Every
slice carries the measure-preserving action of `Z_N³` that preserves the transfer
(`SliceCentreAction.centreAction`, `kT_act`). Its zero-flux sector is
`trivKN N β n i = ZeroFluxSector.zk (halfKN N β n i) act`, the average of `halfKN` over the action.

* `fluxShareN N β n i = (hs(halfKN) − hs(trivKN)) / hs(halfKN)`: the share of the trace carried by
  the states with non-zero electric flux. `fluxShareN_eq_mean`: it is
  `1 − N⁻³ Σ_g Z_g/Z`, the mean deficit of the `N³` twisted partition functions.
* `trivialDefectN N β n i = dd(trivKN)`: the doubling defect of the zero-flux sector alone.

**Proved.**
* `defectW_le_of_sectorsN`: if at side `n` every step has `fluxShareN ≤ 1/80000` and
  `trivialDefectN ≤ 1/80000`, then `defectW N β n ≤ 1/1000`.
* `sectors_of_defectWN`: conversely, `defectW N β n ≤ δ` with `(4 + N⁶) δ ≤ 2` gives at every step
  `fluxShareN ≤ N³ δ / 2` and `trivialDefectN ≤ 2δ`.
* `exists_squarings`: some number `k` of sharp squarings (`DoublingSharp.iterate_sharp`) brings a seed's
  defect to a `δ` meeting both, with both returned bounds at most `1/80000`.
* **`seedExistsPow_iff_sectorSeedPowN`**: `DeltaLengthTower.SeedExistsPow N ↔ SectorSeedPowN N`.
* `fluxShareDoubled_leN`: doubling the time squares the flux odds at the cost `exp(trivialDefectN)`.

So (A₂) for SU(N) is the conjunction of two statements at one side, with the same thresholds as for
SU(2): the non-zero electric-flux sectors carry a share at most `1/80000` of the trace, and the
zero-flux sector has doubling defect at most `1/80000`. The statements hold for every `N ≥ 1`.

DERIVED (module-wide): `8, 4, 2, 1` are the weights of `DoublingRecursion.Δ`'s corner path, summing to
`15`; `1/80000` is chosen so that `15 · 5/80000 ≤ 1/1000`, the `5` being `1` for the zero-flux defect
plus `2 · 2` for twice the log share at a share of at least `1/2`; `N³ = |Z_N³|`
(`SliceCentreAction.card_cen`), so the zero-flux share is at least `N⁻³` and the flux share is at
most `N³δ/2`; `(4 + N⁶) δ ≤ 2` is the condition under which `1/(1 − δ − (N³δ/2)²) ≤ 1 + 2δ`;
`1/(40000 (N³ + 1))`, `1/160000` and `2/(4 + N⁶)` are the defects at which `N³δ/2`, `2δ` and the
condition reach `1/80000`, `1/80000` and equality; `250` and `1/4` are `DoublingSharp.iterate_sharp`'s.
-/

noncomputable section

namespace MassGap.CentreSectorSeedN

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SectorDefect MassGap.DoublingRecursion MassGap.ZeroFluxSector
open MassGap.CentreSectorSeed (pathV pathV_self path_first path_step0 path_step1 path_step2
  path_last Tr)
open MassGap.SliceCentreAction (Cen act centreAction card_cen iter_act)

variable {N : ℕ}

/-! ## 1. The kernels of a step -/

variable (N) in
/-- Haar measure on the slice of step `i`. -/
abbrev hSN (n : ℕ) (i : Fin 4) : Measure (SpT i (Tr n i) → SUN.SU N) := hS i (Tr n i) N

variable (N) in
/-- The transfer over half the time extent `n`, on the slice of step `i`. -/
def halfKN (β : ℝ) (n : ℕ) (i : Fin 4) :
    (SpT i (Tr n i) → SUN.SU N) → (SpT i (Tr n i) → SUN.SU N) → ℝ :=
  iter (hSN N n i) (kT i (Tr n i) N β) (n / 2 - 1)

variable [NeZero N]

variable (N) in
/-- **The zero-flux kernel of step `i`**: `halfKN` averaged over the centre `Z_N³`. -/
def trivKN (β : ℝ) (n : ℕ) (i : Fin 4) :
    (SpT i (Tr n i) → SUN.SU N) → (SpT i (Tr n i) → SUN.SU N) → ℝ :=
  zk (halfKN N β n i) (act (μ := i) (T := Tr n i) (N := N))

variable (N) in
/-- **The flux share**: the share of the trace carried by non-zero electric flux. -/
def fluxShareN (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  (hs (hSN N n i) (halfKN N β n i) - hs (hSN N n i) (trivKN N β n i)) / hs (hSN N n i) (halfKN N β n i)

variable (N) in
/-- **The zero-flux defect**: the doubling defect of the zero-flux sector alone. -/
def trivialDefectN (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ := dd (hSN N n i) (trivKN N β n i)

section Kernel

variable {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
include hβ

theorem bdd_halfKN : Bdd (halfKN N β n i) := by
  unfold halfKN; exact (bdd_kT (NeZero.ne N) hβ).iter _

theorem symm_halfKN : ∀ x y, halfKN N β n i x y = halfKN N β n i y x := by
  unfold halfKN; exact CyclicKernel.iter_symm (bdd_kT (NeZero.ne N) hβ) (kT_symm β) _

theorem low_halfKN : ∀ x y, CentreSectorSeed.floor β n i ≤ halfKN N β n i x y := by
  unfold halfKN CentreSectorSeed.floor
  exact iter_low (bdd_kT (NeZero.ne N) hβ) (kTmin_pos β).le (kT_lower (NeZero.ne N) hβ) _

theorem nonneg_halfKN : ∀ x y, 0 ≤ halfKN N β n i x y := fun x y =>
  (CentreSectorSeed.floor_pos β n i).le.trans (low_halfKN hβ n i x y)

theorem adm_halfKN :
    Adm ([] : List ((SpT i (Tr n i) → SUN.SU N) → (SpT i (Tr n i) → SUN.SU N)))
      (CentreSectorSeed.floor β n i) (halfKN N β n i) :=
  ⟨bdd_halfKN hβ n i, symm_halfKN hβ n i, fun _ h => by simp at h, low_halfKN hβ n i⟩

omit hβ in
theorem inv_halfKN : ∀ g x y, halfKN N β n i (act g x) (act g y) = halfKN N β n i x y := by
  unfold halfKN; exact fun g x y => iter_act β _ g x y

theorem bdd_trivKN : Bdd (trivKN N β n i) := bdd_zk (bdd_halfKN hβ n i) centreAction

theorem hs_halfKN_pos : 0 < hs (hSN N n i) (halfKN N β n i) :=
  CentreSectorSeed.hs_pos_of_adm (CentreSectorSeed.floor_pos β n i) (adm_halfKN hβ n i)

theorem hs_conv_halfKN_pos : 0 < hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)) :=
  CentreSectorSeed.hs_conv_pos_of_adm (CentreSectorSeed.floor_pos β n i) (adm_halfKN hβ n i)

theorem hs_trivKN_pos : 0 < hs (hSN N n i) (trivKN N β n i) :=
  hs_zk_pos (CentreSectorSeed.floor_pos β n i) (bdd_halfKN hβ n i) centreAction (low_halfKN hβ n i)

theorem hs_conv_trivKN_pos :
    0 < hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i)) :=
  hs_conv_zk_pos (CentreSectorSeed.floor_pos β n i) (bdd_halfKN hβ n i) centreAction (low_halfKN hβ n i)

theorem hs_trivKN_le : hs (hSN N n i) (trivKN N β n i) ≤ hs (hSN N n i) (halfKN N β n i) :=
  hs_zk_le (bdd_halfKN hβ n i) centreAction

/-- **The zero-flux sector carries at least `N⁻³` of the trace.** -/
theorem hs_trivKN_ge :
    hs (hSN N n i) (halfKN N β n i) / (N : ℝ) ^ 3 ≤ hs (hSN N n i) (trivKN N β n i) := by
  have h := hs_div_card_le_hs_zk (bdd_halfKN hβ n i) (nonneg_halfKN hβ n i)
    (centreAction (μ := i) (T := Tr n i) (N := N))
  rw [card_cen] at h
  exact_mod_cast h

theorem hs_conv_le_trivKN :
    hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i))
      ≤ hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i))
        + (hs (hSN N n i) (halfKN N β n i) - hs (hSN N n i) (trivKN N β n i)) ^ 2 :=
  hs_conv_le_zk (bdd_halfKN hβ n i) (symm_halfKN hβ n i) centreAction (inv_halfKN n i)

theorem hs_conv_trivKN_le :
    hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i))
      ≤ hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)) :=
  hs_conv_zk_le (bdd_halfKN hβ n i) (symm_halfKN hβ n i) centreAction (inv_halfKN n i)

/-- **The step defect is at most the zero-flux defect plus twice the log of its inverse share.** -/
theorem dd_le_trivKN :
    dd (hSN N n i) (halfKN N β n i) ≤ trivialDefectN N β n i
      + 2 * (Real.log (hs (hSN N n i) (halfKN N β n i))
        - Real.log (hs (hSN N n i) (trivKN N β n i))) :=
  dd_le_zk (CentreSectorSeed.floor_pos β n i) (bdd_halfKN hβ n i) (symm_halfKN hβ n i) centreAction
    (inv_halfKN n i) (low_halfKN hβ n i)

end Kernel

/-! ## 2. The corner path -/

/-- Each step of the corner path is the doubling defect of `halfKN`. -/
theorem p_eq_ddN {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4) :
    p (DoublingWilson.xW N n β) i (pathV i) = dd (hSN N n i) (halfKN N β n i) := by
  have hN : N ≠ 0 := NeZero.ne N
  unfold p
  rw [DoublingWilson.xW_eq hN hβ hn he (pathV i) i,
    DoublingWilson.xW_eq hN hβ hn he (pathV i + E i) i,
    DoublingWilson.tr_ext_add, DoublingWilson.ext_add_self]
  have hext : DoublingWilson.ext n (pathV i) i = n := by
    simp [DoublingWilson.ext, pathV_self]
  rw [hext]
  unfold DoublingWilson.F traceSeq dd halfKN
  have h2 : 2 * n / 2 - 1 = (n / 2 - 1) + (n / 2 - 1) + 1 := by obtain ⟨k, rfl⟩ := he; omega
  rw [h2, iter_add (bdd_kT hN hβ)]

/-- **The defect along the corner path**: `defectW = 8p₀ + 4p₁ + 2p₂ + p₃`, for every `N`. -/
theorem defectW_eqN {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    ZoomSelfScale.defectW N β n = 8 * dd (hSN N n 0) (halfKN N β n 0)
      + 4 * dd (hSN N n 1) (halfKN N β n 1) + 2 * dd (hSN N n 2) (halfKN N β n 2)
      + dd (hSN N n 3) (halfKN N β n 3) := by
  have hΔ : ZoomSelfScale.defectW N β n = Δ (DoublingWilson.xW N n β) (corner 0) := by
    rw [DoublingWilson.Δ_corner0]; rfl
  rw [hΔ, ← p_eq_ddN hβ hn he 0, ← p_eq_ddN hβ hn he 1, ← p_eq_ddN hβ hn he 2,
    ← p_eq_ddN hβ hn he 3]
  unfold Δ p
  rw [path_step0, path_step1, path_step2, path_last, path_first]
  ring

/-! ## 3. The two sector statements give the seed -/

/-- One step: small flux share and small zero-flux defect give a small step defect. -/
theorem dd_halfKN_le_of_sectors {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    (hf : fluxShareN N β n i ≤ 1 / 80000) (ht : trivialDefectN N β n i ≤ 1 / 80000) :
    dd (hSN N n i) (halfKN N β n i) ≤ 1 / 16000 := by
  set A := hs (hSN N n i) (halfKN N β n i) with hAdef
  set B := hs (hSN N n i) (trivKN N β n i) with hBdef
  have hA : 0 < A := hs_halfKN_pos hβ n i
  have hB : 0 < B := hs_trivKN_pos hβ n i
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
  have hdd := dd_le_trivKN (N := N) hβ n i
  linarith

/-- **Sufficiency at one side.** -/
theorem defectW_le_of_sectorsN {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : ∀ i : Fin 4, fluxShareN N β n i ≤ 1 / 80000 ∧ trivialDefectN N β n i ≤ 1 / 80000) :
    ZoomSelfScale.defectW N β n ≤ 1 / 1000 := by
  have hs := fun i => dd_halfKN_le_of_sectors hβ n i (h i).1 (h i).2
  rw [defectW_eqN hβ hn he]
  linarith [hs 0, hs 1, hs 2, hs 3]

/-- The real-number step of `sectors_of_defectWN`. With `A = hs(a)`, `B = hs(e)` the zero-flux
trace, `D`, `Dk` the doubled traces, `M` the number of sectors and `δ` a bound on the defect: the flux
share is at most `Mδ/2` and the zero-flux defect at most `2δ`, when `(4 + M²) δ ≤ 2`. -/
theorem sectors_real {A B D Dk δ M : ℝ} (hA : 0 < A) (hB : 0 < B) (hDk : 0 < Dk) (hM : 0 < M)
    (hδ0 : 0 ≤ δ) (hδ : (4 + M ^ 2) * δ ≤ 2) (hD2 : A ^ 2 * (1 - δ) ≤ D)
    (hconv : D ≤ Dk + (A - B) ^ 2) (hDkB : Dk ≤ B * B) (hBA : B ≤ A) (hBM : A ≤ B * M) :
    (A - B) / A ≤ M * δ / 2 ∧ 2 * Real.log B - Real.log Dk ≤ 2 * δ := by
  have hAB : 0 ≤ A - B := by linarith
  have hkey : 2 * B * (A - B) ≤ δ * A ^ 2 := by nlinarith
  have h2 : 2 * (A * (A - B)) ≤ M * (δ * A ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hBM hAB, mul_le_mul_of_nonneg_left hkey hM.le]
  have h3 : A * (A - B) ≤ A * (M * δ * A / 2) := by linarith
  have hflux : A - B ≤ M * δ * A / 2 := le_of_mul_le_mul_left h3 hA
  refine ⟨by rw [div_le_iff₀ hA]; linarith, ?_⟩
  have hsq : (A - B) ^ 2 ≤ M ^ 2 * δ ^ 2 / 4 * A ^ 2 := by
    calc (A - B) ^ 2 ≤ (M * δ * A / 2) ^ 2 := pow_le_pow_left₀ hAB hflux 2
      _ = M ^ 2 * δ ^ 2 / 4 * A ^ 2 := by ring
  have hDk2 : A ^ 2 * (1 - δ - M ^ 2 * δ ^ 2 / 4) ≤ Dk := by nlinarith
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hP : M ^ 2 * δ ≤ 2 - 4 * δ := by linarith
  have hP0 : 0 ≤ M ^ 2 * δ := mul_nonneg hM2 hδ0
  have hδ2 : δ ≤ 1 / 2 := by linarith
  have hq : M ^ 2 * δ / 4 * (1 + 2 * δ) ≤ (2 - 4 * δ) / 4 * (1 + 2 * δ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hb : 0 ≤ 1 - 2 * δ - M ^ 2 * δ / 4 * (1 + 2 * δ) := by
    nlinarith [sq_nonneg (1 - 2 * δ)]
  have hpoly : 1 ≤ (1 + 2 * δ) * (1 - δ - M ^ 2 * δ ^ 2 / 4) := by
    have e : (1 + 2 * δ) * (1 - δ - M ^ 2 * δ ^ 2 / 4)
        = 1 + δ * (1 - 2 * δ - M ^ 2 * δ / 4 * (1 + 2 * δ)) := by ring
    rw [e]; linarith [mul_nonneg hδ0 hb]
  have hB2 : B ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hB.le hBA 2
  have hA2 : A ^ 2 ≤ (1 + 2 * δ) * Dk := by
    calc A ^ 2 = A ^ 2 * 1 := by ring
      _ ≤ A ^ 2 * ((1 + 2 * δ) * (1 - δ - M ^ 2 * δ ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left hpoly (sq_nonneg A)
      _ = (1 + 2 * δ) * (A ^ 2 * (1 - δ - M ^ 2 * δ ^ 2 / 4)) := by ring
      _ ≤ (1 + 2 * δ) * Dk := mul_le_mul_of_nonneg_left hDk2 (by linarith)
  have hratio : B ^ 2 / Dk ≤ 1 + 2 * δ := by
    rw [div_le_iff₀ hDk]; linarith
  have hlogB : 2 * Real.log B - Real.log Dk ≤ B ^ 2 / Dk - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos (pow_pos hB 2) hDk)
    rw [Real.log_div (pow_pos hB 2).ne' hDk.ne', Real.log_pow] at this
    push_cast at this
    linarith
  linarith

/-- **Necessity at one side.** A defect at most `δ`, with `(4 + N⁶) δ ≤ 2`, bounds the flux share by
`N³δ/2` and the zero-flux defect by `2δ` at every step. -/
theorem sectors_of_defectWN {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : (4 + (N : ℝ) ^ 6) * δ ≤ 2) (hd : ZoomSelfScale.defectW N β n ≤ δ)
    (i : Fin 4) :
    fluxShareN N β n i ≤ (N : ℝ) ^ 3 * δ / 2 ∧ trivialDefectN N β n i ≤ 2 * δ := by
  have hnn := fun j => CentreSectorSeed.dd_nonneg (ν := hSN N n j) (CentreSectorSeed.floor_pos β n j)
    (adm_halfKN (N := N) hβ n j)
  have hsum := defectW_eqN (N := N) hβ hn he
  have hp : dd (hSN N n i) (halfKN N β n i) ≤ δ := by
    fin_cases i
    · show dd (hSN N n 0) (halfKN N β n 0) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSN N n 1) (halfKN N β n 1) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSN N n 2) (halfKN N β n 2) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
    · show dd (hSN N n 3) (halfKN N β n 3) ≤ δ
      linarith [hnn 0, hnn 1, hnn 2, hnn 3]
  set A := hs (hSN N n i) (halfKN N β n i) with hAdef
  set B := hs (hSN N n i) (trivKN N β n i) with hBdef
  set D := hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i)) with hDdef
  set Dk := hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i)) with hDkdef
  have hA : 0 < A := hs_halfKN_pos hβ n i
  have hB : 0 < B := hs_trivKN_pos hβ n i
  have hD : 0 < D := hs_conv_halfKN_pos hβ n i
  have hDk : 0 < Dk := hs_conv_trivKN_pos hβ n i
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
  have hconv : D ≤ Dk + (A - B) ^ 2 := hs_conv_le_trivKN hβ n i
  have hDkB : Dk ≤ B * B := hs_conv_le_mul (bdd_trivKN hβ n i) (bdd_trivKN hβ n i)
  have hBA : B ≤ A := hs_trivKN_le hβ n i
  have hM : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  have hBM : A ≤ B * (N : ℝ) ^ 3 := (div_le_iff₀ hM).mp (hs_trivKN_ge hβ n i)
  have hδM : (4 + ((N : ℝ) ^ 3) ^ 2) * δ ≤ 2 := by
    rw [show ((N : ℝ) ^ 3) ^ 2 = (N : ℝ) ^ 6 by ring]; exact hδ
  obtain ⟨hf, ht⟩ := sectors_real hA hB hDk hM hδ0 hδM hD2 hconv hDkB hBA hBM
  exact ⟨hf, ht⟩

/-! ## 4. Sharp squarings -/

/-- **Sharp squarings of a seed**: `250 · defectW(2ᵏ n) ≤ (1/4)^{2ᵏ}`. -/
theorem defectW_sharp {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : ZoomSelfScale.defectW N β n ≤ 1 / 1000) (k : ℕ) :
    250 * ZoomSelfScale.defectW N β (2 ^ k * n) ≤ (1 / 4) ^ (2 ^ k) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hfr := DoublingWilson.factRep hN hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (DoublingWilson.xW N n β) (corner 0) ≤ 1 / 1000 := by
    rw [DoublingWilson.Δ_corner0]; exact h
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  rwa [WDeltaRun.Δ_corner] at hi

omit [NeZero N] in
/-- **Enough sharp squarings meet both sector bounds**: some `k` makes every `δ ≥ 0` with
`250 δ ≤ (1/4)^{2ᵏ}` satisfy the hypothesis of `sectors_of_defectWN` with both returned bounds at most
`1/80000`. -/
theorem exists_squarings (N : ℕ) : ∃ k : ℕ, ∀ δ : ℝ, 0 ≤ δ → 250 * δ ≤ (1 / 4) ^ (2 ^ k) →
    (4 + (N : ℝ) ^ 6) * δ ≤ 2 ∧ (N : ℝ) ^ 3 * δ / 2 ≤ 1 / 80000 ∧ 2 * δ ≤ 1 / 80000 := by
  have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hN6 : (0 : ℝ) ≤ (N : ℝ) ^ 6 := by positivity
  have hτ0 : (0 : ℝ) < min (min (1 / (40000 * ((N : ℝ) ^ 3 + 1))) (1 / 160000))
      (2 / (4 + (N : ℝ) ^ 6)) :=
    lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (mul_pos (by norm_num : (0 : ℝ) < 250) hτ0)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  refine ⟨m, fun δ hδ0 hδ => ?_⟩
  have hmm : ((1 : ℝ) / 4) ^ (2 ^ m) ≤ (1 / 4) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self (n := m)).le
  have hδτ : δ ≤ min (min (1 / (40000 * ((N : ℝ) ^ 3 + 1))) (1 / 160000))
      (2 / (4 + (N : ℝ) ^ 6)) := by linarith
  have h1 : δ ≤ 1 / (40000 * ((N : ℝ) ^ 3 + 1)) :=
    hδτ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : δ ≤ 1 / 160000 := hδτ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : δ ≤ 2 / (4 + (N : ℝ) ^ 6) := hδτ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h1 h3
  refine ⟨by linarith, by nlinarith, by linarith⟩

/-- A seed at an even side `n ≥ 2`, `k` squarings beyond it, carries both sector bounds. -/
theorem sectors_of_seed {k : ℕ} (hk : ∀ δ : ℝ, 0 ≤ δ → 250 * δ ≤ (1 / 4) ^ (2 ^ k) →
      (4 + (N : ℝ) ^ 6) * δ ≤ 2 ∧ (N : ℝ) ^ 3 * δ / 2 ≤ 1 / 80000 ∧ 2 * δ ≤ 1 / 80000)
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (hd : ZoomSelfScale.defectW N β n ≤ 1 / 1000) (i : Fin 4) :
    fluxShareN N β (2 ^ k * n) i ≤ 1 / 80000 ∧ trivialDefectN N β (2 ^ k * n) i ≤ 1 / 80000 := by
  have hs := defectW_sharp hβ hn he hd k
  have hδ0 : (0 : ℝ) ≤ (1 / 4) ^ (2 ^ k) / 250 := by positivity
  obtain ⟨c1, c2, c3⟩ := hk _ hδ0 (by linarith)
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hn' : 2 ≤ 2 ^ k * n := by nlinarith
  have he' : Even (2 ^ k * n) := he.mul_left _
  have := sectors_of_defectWN hβ hn' he' hδ0 c1 (by linarith) i
  exact ⟨this.1.trans c2, this.2.trans c3⟩

/-! ## 5. Along the couplings -/

variable (N) in
/-- **The sector seed on power-of-two sides**: eventually in `β`, some `2ᵇ` has, at every step of
the corner path, flux share and zero-flux defect at most `1/80000`. DERIVED: `1/80000` chosen so that
`15 · 5/80000 ≤ 1/1000` (module docstring); `1` the least exponent, so `2ᵇ ≥ 2`. -/
def SectorSeedPowN : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
    ∀ i : Fin 4, fluxShareN N β (2 ^ b) i ≤ 1 / 80000 ∧ trivialDefectN N β (2 ^ b) i ≤ 1 / 80000

/-- **The sector seed gives (A₂) for SU(N).** -/
theorem seedExistsPow_of_sectorSeedPowN (h : SectorSeedPowN N) :
    DeltaLengthTower.SeedExistsPow N := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hs⟩ hβ
  exact ⟨b, hb, defectW_le_of_sectorsN hβ (DeltaLengthTower.two_le_two_pow hb)
    (DeltaLengthTower.even_two_pow hb) hs⟩

/-- **(A₂) for SU(N) gives the sector seed**: `k` sharp squarings beyond a seed side
(`exists_squarings`) bring the defect to where necessity gives both sector bounds at `1/80000`. -/
theorem sectorSeedPowN_of_seedExistsPow (h : DeltaLengthTower.SeedExistsPow N) :
    SectorSeedPowN N := by
  obtain ⟨k, hk⟩ := exists_squarings N
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hd⟩ hβ
  refine ⟨k + b, by omega, fun i => ?_⟩
  have := sectors_of_seed hk hβ (DeltaLengthTower.two_le_two_pow hb)
    (DeltaLengthTower.even_two_pow hb) hd i
  rwa [← pow_add] at this

/-- **(A₂) for SU(N) is the sector seed.** -/
theorem seedExistsPow_iff_sectorSeedPowN :
    DeltaLengthTower.SeedExistsPow N ↔ SectorSeedPowN N :=
  ⟨sectorSeedPowN_of_seedExistsPow, seedExistsPow_of_sectorSeedPowN⟩

/-! ## 6. The flux share as twisted traces -/

variable (N) in
/-- **The twisted ratio** `Z_g/Z` at step `i`, side `n`: the trace with the centre element `g`
inserted at one time slice, over the trace. -/
def twistRatioN (β : ℝ) (n : ℕ) (i : Fin 4) (g : Cen i N) : ℝ :=
  FluxSectorBound.twist (hSN N n i) (halfKN N β n i) (act (T := Tr n i) g)
    / hs (hSN N n i) (halfKN N β n i)

/-- **The flux share is one minus the mean twisted ratio**: `fluxShareN = 1 − N⁻³ Σ_g Z_g/Z`. -/
theorem fluxShareN_eq_mean {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    fluxShareN N β n i = 1 - ((N : ℝ) ^ 3)⁻¹ * ∑ g, twistRatioN N β n i g := by
  have hA := hs_halfKN_pos (N := N) hβ n i
  have hB := hs_zk_eq_mean (bdd_halfKN hβ n i) (centreAction (μ := i) (T := Tr n i) (N := N))
  rw [card_cen] at hB
  push_cast at hB
  unfold fluxShareN trivKN twistRatioN
  rw [hB, ← Finset.sum_div, sub_div, div_self hA.ne']
  ring

variable (N) in
/-- The flux share of the torus doubled along the transfer direction `i`. -/
def fluxShareDoubledN (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  (hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i))
    - hs (hSN N n i) (zk (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i))
        (act (μ := i) (T := Tr n i) (N := N))))
    / hs (hSN N n i) (conv (hSN N n i) (halfKN N β n i) (halfKN N β n i))

/-- **Doubling the time squares the flux odds**:
`fluxShareDoubledN ≤ (fluxShareN/(1 − fluxShareN))² · exp(trivialDefectN)`. -/
theorem fluxShareDoubled_leN {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    fluxShareDoubledN N β n i
      ≤ (fluxShareN N β n i / (1 - fluxShareN N β n i)) ^ 2 * Real.exp (trivialDefectN N β n i) := by
  have h := odds_conv_le_zk (CentreSectorSeed.floor_pos β n i) (bdd_halfKN (N := N) hβ n i) (symm_halfKN hβ n i)
    centreAction (inv_halfKN n i) (low_halfKN hβ n i)
  have hA := hs_halfKN_pos (N := N) hβ n i
  have hodds : fluxShareN N β n i / (1 - fluxShareN N β n i)
      = (hs (hSN N n i) (halfKN N β n i) - hs (hSN N n i) (trivKN N β n i))
        / hs (hSN N n i) (trivKN N β n i) := by
    unfold fluxShareN
    have e : 1 - (hs (hSN N n i) (halfKN N β n i) - hs (hSN N n i) (trivKN N β n i))
        / hs (hSN N n i) (halfKN N β n i)
        = hs (hSN N n i) (trivKN N β n i) / hs (hSN N n i) (halfKN N β n i) := by
      rw [sub_div, div_self hA.ne']; ring
    rw [e, div_div_div_cancel_right₀ hA.ne']
  unfold fluxShareDoubledN
  rw [hodds]
  exact h

end MassGap.CentreSectorSeedN

end

#print axioms MassGap.CentreSectorSeedN.defectW_eqN
#print axioms MassGap.CentreSectorSeedN.hs_trivKN_ge
#print axioms MassGap.CentreSectorSeedN.defectW_le_of_sectorsN
#print axioms MassGap.CentreSectorSeedN.sectors_of_defectWN
#print axioms MassGap.CentreSectorSeedN.exists_squarings
#print axioms MassGap.CentreSectorSeedN.seedExistsPow_iff_sectorSeedPowN
#print axioms MassGap.CentreSectorSeedN.fluxShareN_eq_mean
#print axioms MassGap.CentreSectorSeedN.fluxShareDoubled_leN
