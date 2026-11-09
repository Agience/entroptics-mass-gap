import Mathlib
import MassGap.TomboulisYaffe
import MassGap.VortexTorus

/-!
# MassGap.VortexTwo — the zoom chain on the published Tomboulis–Yaffe form, on the doubling corner tori

`VortexTorus.floor_of_vortexR_condensation` takes `VortexCondense.TYBoundR` as an input. That predicate
is false on the diagonal plane (`TomboulisYaffe.not_tyBoundR_diag`) and, off the diagonal, asks more than
the published `SU(2)` inequality. This module rebuilds the chain on what `TomboulisYaffe` derives from
the one named chessboard input `ChessboardFlux`: `wloopR ≤ 2 ((1 − zR)/2)^{mn/(L_a L_b)}` on rectangles
with `L_a = 2^p m`, `L_b = 2^q n` (`AdmTwo`). The plane is `(i, ν)` with `ν ≠ i` an explicit hypothesis.

## The doubling corner tori

The box family is `Lc (2^{K+1}) i`: extent `2^{K+1}` along `i`, `2^{pathV i b} · 2^{K+1}` along `b`.
`admTwo_Lc_doubling`: for `p ≤ K` the square `2^p × 2^p` is `AdmTwo` in every plane `(i, b)`. Every
side `2^{K+1}` is even and at least `2` (`two_le_two_pow_succ`, `even_two_pow_succ`), the conditions of
`VortexCondense.zR_Lc_le_one`.

## The area law with the factor `2`

* `wloopR_area_two`: on one doubling torus, `ChessboardFlux` and `vortexR ≤ exp(−s L_i L_ν)` give
  `wloopR (2^p) (2^p) ≤ 2 exp(−s 4^p)` for `p ≤ K`.
* `areaLaw_two_of_vortexR_condensation`: along the doubling family, `ChessboardFlux` on every torus,
  condensation of `vortexR` at rate `ρ` per unit area of the plane, and the limit of the square loops
  give `Winf (2^p) (2^p) ≤ 2 exp(−ρ 4^p)` for every `p`.

## The prefactor in the abstract chain

`areaLaw_limit_const`: the form of `VortexCondense.areaLaw_limit` with a prefactor `C`: if for every
`ρ' < ρ` eventually `W K m n ≤ C exp(−ρ' mn)`, and `W K m n → Winf m n`, then
`Winf m n ≤ C exp(−ρ mn)`. `areaLaw_two_of_vortexR_condensation` is built on it.

## The tension from a subsequence

`HasTension W σ` is a limit along all `n`. `le_tension_of_area_subseq`: along any `φ p → ∞`,
`W (φ p) (φ p) ≤ C exp(−ρ φ(p)²)` with `C > 0` gives `ρ ≤ σ`: the subsequence of a convergent sequence
has the same limit, and `log C / φ(p)² → 0`. `le_tension_of_area_const` is the case `φ = id` (the form
of `VortexCondense.le_tension_of_area` with a prefactor); `le_tension_of_area_two` is the case
`φ p = 2^p`, `C = 2`. So the constant `2` does not change the rate.

Every consumer of `ChessboardFlux` here takes `0 ≤ β`, used for `0 ≤ 1 − zR`
(`VortexCondense.zR_Lc_le_one`). The doubling exponent of the square `2^p` in `Lc (2^{K+1}) i` is
`K + 1 − p ≥ 1`, as `Adm` (`m < L_a`) forces.

## The zoom

* `floor_of_vortexR_condensation_two`: at every zoom `j`, `ChessboardFlux` on every doubling torus,
  condensation of `vortexR` at the lattice rate `ρ₀ (a j)²`, the limit of the square loops and
  `HasTension` give `NoTransition.Floor (σlat / a²)`.
* `matchAt_uniform_of_vortexR_condensation_two`: with the count hypothesis of
  `MatchAt.matchAt_of_count` at cost `(σlat j / a j²) f L²`, one `L₀` gives `MatchAt` at every zoom
  and every `L ≥ L₀`.

Neither takes `TYBoundR`, `Adm` on all rectangles, or a size hypothesis.

## What stays a hypothesis

`ChessboardFlux` (reflection positivity and the chessboard estimate on `RectWilson.RSite` are not in the
tree), condensation of `vortexR` uniformly in the zoom in physical units, the limit `K → ∞` of the
square loops, `HasTension` of that limit, and the chunk count. `chessboardFlux_zero`: at `β = 0` the
flux operator is `0`, so `ChessboardFlux` holds in every plane; with `VortexTorus.condenses_vortexR_zero`
the first two inputs hold together at `β = 0`. There the published form forces
`wloopR (2^p) (2^p) ≤ 0` (`wloopR_two_zero_le`), so the square-loop limit and `HasTension` are jointly
false (`not_hyps_two_zero`): the only point where `ChessboardFlux` is proved is a point where the zoom
hypotheses fail together. `a j` is an input: nothing here relates it to `β j`, so the uniformity in
physical units is as strong as that identification. `area_two_tension_consistent`: the area law
with the factor `2` along the squares `2^p` and `HasTension W ρ` hold together for `W = e^{−ρmn}`, so
`le_tension_of_area_two` is not vacuous. No declaration exhibits all hypotheses of the zoom theorems
jointly at weak coupling.

DERIVED (module-wide): `2` is `|ℤ₂|` (the prefactor of the published form) and the base of the
doubling; `K + 1` the shift that makes the side at least `2`; `1` the least loop side.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.VortexTwo

open Filter Topology MeasureTheory
open MassGap.MatchAt MassGap.VortexCondense MassGap.GapSideVortexRect MassGap.VortexTorus
  MassGap.TomboulisYaffe

/-! ## 1. The doubling corner tori -/

theorem two_le_two_pow_succ (K : ℕ) : 2 ≤ 2 ^ (K + 1) := by
  have h := Nat.one_le_two_pow (n := K)
  rw [pow_succ]
  omega

theorem even_two_pow_succ (K : ℕ) : Even (2 ^ (K + 1)) :=
  Nat.even_pow.2 ⟨even_two, by omega⟩

/-- **Power-of-two squares are `AdmTwo` on the doubling corner tori**: for `p ≤ K`, the `2^p × 2^p`
square in the plane `(i, b)` of `Lc (2^{K+1}) i` tiles the cross-section with power-of-two ratios. -/
theorem admTwo_Lc_doubling (i b : Fin 4) {p K : ℕ} (hpK : p ≤ K) :
    AdmTwo (Lc (2 ^ (K + 1)) i i) (Lc (2 ^ (K + 1)) i b) (2 ^ p) (2 ^ p) := by
  have hlt : 2 ^ p < 2 ^ (K + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdvd : 2 ^ p ∣ 2 ^ (K + 1) := pow_dvd_pow 2 (by omega)
  refine ⟨⟨?_, hdvd.trans (dvd_Lc _ i b), ?_, hlt.trans_le (le_Lc _ i b)⟩,
    ⟨K + 1 - p, ?_⟩, ⟨CentreSectorSeed.pathV i b + (K + 1 - p), ?_⟩⟩
  · rw [Lc_self]; exact hdvd
  · rw [Lc_self]; exact hlt
  · rw [Lc_self, ← pow_add, Nat.sub_add_cancel (by omega)]
  · show 2 ^ (CentreSectorSeed.pathV i b) * 2 ^ (K + 1)
      = 2 ^ (CentreSectorSeed.pathV i b + (K + 1 - p)) * 2 ^ p
    rw [pow_add 2 (CentreSectorSeed.pathV i b), mul_assoc, ← pow_add 2 (K + 1 - p) p,
      Nat.sub_add_cancel (by omega)]

/-! ## 2. The area law with the factor `2` -/

/-- **The area law with the prefactor `2` on one doubling torus.** `ChessboardFlux` in the plane
`(i, ν)`, `ν ≠ i`, and `vortexR ≤ exp(−s L_i L_ν)` give `wloopR (2^p) (2^p) ≤ 2 exp(−s 4^p)` for
`p ≤ K`. -/
theorem wloopR_area_two {β s : ℝ} (hβ : 0 ≤ β) {K : ℕ} (i ν : Fin 4) (hν : ν ≠ i)
    (o : RectWilson.RSite (Lc (2 ^ (K + 1)) i))
    (hCB : ChessboardFlux (Lc (2 ^ (K + 1)) i) i ν o β)
    (hv : vortexR (Lc (2 ^ (K + 1)) i) i ν β
      ≤ Real.exp (-(s * (((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)))))
    {p : ℕ} (hpK : p ≤ K) :
    wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) o β
      ≤ 2 * Real.exp (-(s * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ)))) :=
  area_two_of_chessboard (Lc (2 ^ (K + 1)) i) (Ne.symm hν) o hCB
    (vortexR_Lc_nonneg hβ (two_le_two_pow_succ K) (even_two_pow_succ K) i ⟨ν, hν⟩).2
    ((one_sub_zR_le_vortexR (Lc (2 ^ (K + 1)) i) i ν β).trans hv) (admTwo_Lc_doubling i ν hpK)

/-- **The thermodynamic limit of an area law with a prefactor.** If for every `ρ' < ρ` eventually
`W K ≤ C exp(−ρ' x)`, and `W K → w`, then `w ≤ C exp(−ρ x)`. -/
theorem areaLaw_limit_const {W : ℕ → ℝ} {w C ρ x : ℝ}
    (hW : ∀ ρ' < ρ, ∀ᶠ K in atTop, W K ≤ C * Real.exp (-(ρ' * x)))
    (hlim : Tendsto W atTop (𝓝 w)) : w ≤ C * Real.exp (-(ρ * x)) := by
  have hstep : ∀ ρ' < ρ, w ≤ C * Real.exp (-(ρ' * x)) := fun ρ' hρ' =>
    le_of_tendsto hlim (hW ρ' hρ')
  have h1 : Tendsto (fun k : ℕ => ρ - 1 / ((k : ℝ) + 1)) atTop (𝓝 ρ) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ)).sub
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  have h2 : Tendsto (fun k : ℕ => C * Real.exp (-((ρ - 1 / ((k : ℝ) + 1)) * x))) atTop
      (𝓝 (C * Real.exp (-(ρ * x)))) :=
    ((Real.continuous_exp.tendsto _).comp ((h1.mul_const _).neg)).const_mul C
  refine ge_of_tendsto h2 (Eventually.of_forall fun k => hstep _ ?_)
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

/-- **The area law with the prefactor `2` in the limit along the doubling tori.** `ChessboardFlux` on
every torus `Lc (2^{K+1}) i` in the plane `(i, ν)`, `ν ≠ i`, condensation of `vortexR` at rate `ρ` per
unit area of the plane, and the limit of the square loops give `Winf (2^p) (2^p) ≤ 2 exp(−ρ 4^p)`. -/
theorem areaLaw_two_of_vortexR_condensation {β ρ : ℝ} (hβ : 0 ≤ β) (i ν : Fin 4) (hν : ν ≠ i)
    (o : ∀ K, RectWilson.RSite (Lc (2 ^ (K + 1)) i))
    (hCB : ∀ K, ChessboardFlux (Lc (2 ^ (K + 1)) i) i ν (o K) β)
    (hcond : Condenses (fun K => vortexR (Lc (2 ^ (K + 1)) i) i ν β)
      (fun K => ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)) ρ)
    {Winf : ℕ → ℕ → ℝ}
    (hlim : ∀ p, Tendsto (fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o K) β) atTop
      (𝓝 (Winf (2 ^ p) (2 ^ p)))) :
    ∀ p, Winf (2 ^ p) (2 ^ p) ≤ 2 * Real.exp (-(ρ * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ)))) := by
  intro p
  refine areaLaw_limit_const (W := fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o K) β)
    (fun ρ' hρ' => ?_) (hlim p)
  filter_upwards [hcond ρ' hρ', eventually_ge_atTop p] with K hK hpK
  exact wloopR_area_two hβ i ν hν (o K) (hCB K) hK hpK

/-! ## 3. The tension from a subsequence -/

/-- **An area law with a prefactor along a subsequence bounds the tension below.** `HasTension W σ`,
`φ p → ∞`, and `W (φ p) (φ p) ≤ C exp(−ρ φ(p)²)` with `C > 0` give `ρ ≤ σ`. -/
theorem le_tension_of_area_subseq {W : ℕ → ℕ → ℝ} {σ ρ C : ℝ} (hC : 0 < C) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hT : HasTension W σ)
    (harea : ∀ p, W (φ p) (φ p) ≤ C * Real.exp (-(ρ * ((φ p : ℝ) * φ p)))) : ρ ≤ σ := by
  have h1 : Tendsto (fun p => -Real.log (W (φ p) (φ p)) / ((φ p : ℕ) : ℝ) ^ 2) atTop (𝓝 σ) :=
    hT.2.comp hφ
  have hsq : Tendsto (fun p => ((φ p : ℕ) : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_natCast_atTop_atTop.comp hφ)
  have h2 : Tendsto (fun p => ρ - Real.log C / ((φ p : ℕ) : ℝ) ^ 2) atTop (𝓝 ρ) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ)).sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log C) atTop (𝓝 (Real.log C))).div_atTop hsq)
    simpa using this
  refine le_of_tendsto_of_tendsto h2 h1 ?_
  filter_upwards [hφ.eventually_ge_atTop 1] with p hp
  have hpos := hT.1 (φ p) hp
  have hl : Real.log (W (φ p) (φ p)) ≤ Real.log C - ρ * ((φ p : ℝ) * φ p) := by
    have := Real.log_le_log hpos (harea p)
    rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
  have hn0 : (0 : ℝ) < (φ p : ℝ) := by exact_mod_cast hp
  have hn2 : (0 : ℝ) < ((φ p : ℕ) : ℝ) ^ 2 := by positivity
  have hsq' : ((φ p : ℕ) : ℝ) ^ 2 = (φ p : ℝ) * φ p := sq _
  rw [le_div_iff₀ hn2, sub_mul, div_mul_cancel₀ _ hn2.ne', hsq']
  linarith

/-- **An area law with a prefactor bounds the tension below**: `HasTension W σ` and
`W n n ≤ C exp(−ρ n²)` for every `n`, `C > 0`, give `ρ ≤ σ`. -/
theorem le_tension_of_area_const {W : ℕ → ℕ → ℝ} {σ ρ C : ℝ} (hC : 0 < C) (hT : HasTension W σ)
    (harea : ∀ n, W n n ≤ C * Real.exp (-(ρ * ((n : ℝ) * n)))) : ρ ≤ σ :=
  le_tension_of_area_subseq (φ := id) hC tendsto_id hT harea

theorem tendsto_two_pow :Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))

/-- **The constant `2` does not change the rate**: `HasTension W σ` and
`W (2^p) (2^p) ≤ 2 exp(−ρ 4^p)` for every `p` give `ρ ≤ σ`. -/
theorem le_tension_of_area_two {W : ℕ → ℕ → ℝ} {σ ρ : ℝ} (hT : HasTension W σ)
    (harea : ∀ p, W (2 ^ p) (2 ^ p)
      ≤ 2 * Real.exp (-(ρ * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ))))) : ρ ≤ σ :=
  le_tension_of_area_subseq (φ := fun p => 2 ^ p) two_pos tendsto_two_pow hT harea

/-! ## 4. The zoom -/

/-- **Condensation of the torus vortex free energy gives the floor, on the published form.** At zoom
`j` the boxes are `Lc (2^{K+1}) i` at coupling `β j`; `ChessboardFlux` in the plane `(i, ν)`, `ν ≠ i`,
on every torus, condensation of `vortexR` at the lattice rate `ρ₀ (a j)²` per unit area of the plane,
the limit of the square loops and `HasTension` give `Floor (σlat / a²)`. -/
theorem floor_of_vortexR_condensation_two {β a σlat : ℕ → ℝ} {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j) (hβ : ∀ j, 0 ≤ β j) (i ν : Fin 4) (hν : ν ≠ i)
    (o : ∀ _ : ℕ, ∀ K, RectWilson.RSite (Lc (2 ^ (K + 1)) i))
    (hCB : ∀ j K, ChessboardFlux (Lc (2 ^ (K + 1)) i) i ν (o j K) (β j))
    (hcond : ∀ j, Condenses (fun K => vortexR (Lc (2 ^ (K + 1)) i) i ν (β j))
      (fun K => ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)) (ρ₀ * a j ^ 2))
    {Winf : ℕ → ℕ → ℕ → ℝ}
    (hlim : ∀ j p, Tendsto (fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o j K) (β j))
      atTop (𝓝 (Winf j (2 ^ p) (2 ^ p))))
    (hT : ∀ j, HasTension (Winf j) (σlat j)) :
    NoTransition.Floor (fun j => σlat j / a j ^ 2) := by
  refine ⟨ρ₀, hρ₀, fun j => ?_⟩
  have harea := areaLaw_two_of_vortexR_condensation (hβ j) i ν hν (o j) (hCB j) (hcond j) (hlim j)
  have h := le_tension_of_area_two (hT j) harea
  rw [le_div_iff₀ (pow_pos (ha j) 2)]
  exact h

/-- **Torus condensation, the count, and one length for every zoom, on the published form.** The
hypotheses of `floor_of_vortexR_condensation_two` and the count of `MatchAt.matchAt_of_count` at cost
`(σlat j / a j²) f L²` give one `L₀` with `MatchAt` at every zoom and every `L ≥ L₀`. -/
theorem matchAt_uniform_of_vortexR_condensation_two {β a σlat : ℕ → ℝ} {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j) (hβ : ∀ j, 0 ≤ β j) (i ν : Fin 4) (hν : ν ≠ i)
    (o : ∀ _ : ℕ, ∀ K, RectWilson.RSite (Lc (2 ^ (K + 1)) i))
    (hCB : ∀ j K, ChessboardFlux (Lc (2 ^ (K + 1)) i) i ν (o j K) (β j))
    (hcond : ∀ j, Condenses (fun K => vortexR (Lc (2 ^ (K + 1)) i) i ν (β j))
      (fun K => ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)) (ρ₀ * a j ^ 2))
    {Winf : ℕ → ℕ → ℕ → ℝ}
    (hlim : ∀ j p, Tendsto (fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o j K) (β j))
      atTop (𝓝 (Winf j (2 ^ p) (2 ^ p))))
    (hT : ∀ j, HasTension (Winf j) (σlat j))
    {V : ℕ → ℝ → Type*} [∀ j L, Fintype (V j L)] [∀ j L, DecidableEq (V j L)]
    (w : ∀ j L, Finset (V j L) → ℝ) {z f κ : ℝ} (hz : 0 ≤ z) (hf : 0 < f) (hκ : 0 ≤ κ)
    (hw0 : ∀ j L, w j L ∅ = 0)
    (hcount : ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(σlat j / a j ^ 2 * f * L ^ 2))) ^ n) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ := by
  have hfl := floor_of_vortexR_condensation_two hρ₀ ha hβ i ν hν o hCB hcond hlim hT
  obtain ⟨L₀, hL₀, h⟩ := NoTransitionFlow.uniform_length_of_floor (κ := κ) hz hf hfl
  exact ⟨L₀, hL₀, fun j L hL => matchAt_of_count (hw0 j L) hz hκ (hcount j L) (h j L hL)⟩

/-! ## 5. Non-vacuity checks -/

/-- **At `β = 0` the chessboard input holds** in every plane: the flux operator is `0`, both sides of
each inequality are `0`. -/
theorem chessboardFlux_zero (L : Fin 4 → ℕ) (a b : Fin 4) (o : RectWilson.RSite L) :
    ChessboardFlux L a b o 0 := by
  intro m n hadm
  obtain ⟨hm, hn⟩ := adm_pos hadm.1
  have hLa : (0 : ℝ) < L a := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hadm.1.2.2.1
  have hLb : (0 : ℝ) < L b := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le n) hadm.1.2.2.2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : ((m : ℝ) * n) / ((L a : ℝ) * L b) ≠ 0 := (by positivity : (0 : ℝ) < _).ne'
  have hf : ∀ (ζ : RectWilson.RPlaq L → SUN.SU 2) (U : RectWilson.RLink L → SUN.SU 2),
      fluxOp L 0 ζ U = 0 := by
    intro ζ U
    simp [fluxOp, vortexOp]
  have hev : ∀ X : (RectWilson.RLink L → SUN.SU 2) → ℝ, (∀ U, X U = 0) → ev L 0 X = 0 := by
    intro X hX
    simp [ev, hX]
  rw [hev _ (fun U => by rw [hf, zero_mul]), hev _ (hf _), hev _ (fun U => by rw [hf, zero_mul]),
    hev _ (hf _), Real.zero_rpow hx]
  exact ⟨le_rfl, le_rfl⟩

/-- **The tension inputs are jointly satisfiable**: for `W m n = e^{−ρmn}` the area law with the
factor `2` along the squares `2^p` and `HasTension W ρ` both hold. -/
theorem area_two_tension_consistent {ρ : ℝ} :
    (∀ p, Real.exp (-(ρ * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ))))
      ≤ 2 * Real.exp (-(ρ * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ))))) ∧
    HasTension (fun m n => Real.exp (-(ρ * ((m : ℝ) * n)))) ρ := by
  refine ⟨fun p => ?_, condensation_hyps_consistent.2.2⟩
  have := Real.exp_pos (-(ρ * (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ))))
  linarith

/-- **At `β = 0` the published form forces every doubling square loop to be `≤ 0`.** -/
theorem wloopR_two_zero_le (K : ℕ) (i ν : Fin 4) (hν : ν ≠ i)
    (o : MassGap.RectWilson.RSite (Lc (2 ^ (K + 1)) i)) {p : ℕ} (hpK : p ≤ K) :
    wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) o 0 ≤ 0 := by
  have h := MassGap.TomboulisYaffe.tyTwo_of_chessboard (Lc (2 ^ (K + 1)) i) (Ne.symm hν) o
    (chessboardFlux_zero _ i ν o) (admTwo_Lc_doubling i ν hpK)
  rw [zR_zero, sub_self, zero_div] at h
  have hLa : (0 : ℝ) < ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) := by
    rw [Lc_self]; positivity
  have hLb : (0 : ℝ) < ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ) := by
    have := le_Lc (2 ^ (K + 1)) i ν
    have h2 : 0 < 2 ^ (K + 1) := by positivity
    exact_mod_cast (lt_of_lt_of_le h2 this)
  have hx : (((2 ^ p : ℕ) : ℝ) * ((2 ^ p : ℕ) : ℝ)) / (((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ)
      * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.zero_rpow hx, mul_zero] at h
  exact h

/-- **At `β = 0` the hypotheses of `floor_of_vortexR_condensation_two` are jointly false**:
the square-loop limit and `HasTension` cannot both hold at a zoom with `β j = 0`. -/
theorem not_hyps_two_zero (i ν : Fin 4) (hν : ν ≠ i)
    (o : ∀ K, MassGap.RectWilson.RSite (Lc (2 ^ (K + 1)) i)) {Winf : ℕ → ℕ → ℝ} {σ : ℝ}
    (hlim : ∀ p, Tendsto (fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o K) 0) atTop
      (𝓝 (Winf (2 ^ p) (2 ^ p))))
    (hT : HasTension Winf σ) : False := by
  have hle : Winf (2 ^ 0) (2 ^ 0) ≤ 0 :=
    le_of_tendsto (hlim 0) (Eventually.of_forall fun K =>
      wloopR_two_zero_le K i ν hν (o K) (Nat.zero_le K))
  have hpos := hT.1 (2 ^ 0) (by norm_num)
  linarith

#print axioms two_le_two_pow_succ
#print axioms even_two_pow_succ
#print axioms admTwo_Lc_doubling
#print axioms wloopR_area_two
#print axioms areaLaw_two_of_vortexR_condensation
#print axioms areaLaw_limit_const
#print axioms le_tension_of_area_subseq
#print axioms le_tension_of_area_const
#print axioms tendsto_two_pow
#print axioms le_tension_of_area_two
#print axioms floor_of_vortexR_condensation_two
#print axioms matchAt_uniform_of_vortexR_condensation_two
#print axioms chessboardFlux_zero
#print axioms area_two_tension_consistent
#print axioms wloopR_two_zero_le
#print axioms not_hyps_two_zero

end MassGap.VortexTwo
