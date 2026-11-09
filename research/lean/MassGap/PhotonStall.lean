import Mathlib
import MassGap.WindowFreq
import MassGap.ZoomContract

/-!
# MassGap.PhotonStall — the doubling defect of a Gaussian photon, in closed form

`CouplingTower.windowCoupling N β w = 16 log Z(2^w) − log Z(2^{w+1})` is the doubling defect `D` of the
Wilson torus; the bridge `CouplingTower.StrongEnd N` asks that, frequently as `β → ∞`, `D` tend to `0` along
the windows (seed form: some window has `D ≤ 1/1000`). The zero-mode volumes of the photon model are chosen,
not derived. This module computes `D` for Gaussian models on the periodic torus of side `L` in `d`
dimensions, from the explicit spectrum `ω²_k = m² + Σ_μ 4 sin²(π k_μ/L)` (`WindowFreq.omega2D`), and reads
off where the coupling and the window enter. Declarations are in `MassGap.PhotonStall`.

The Gaussian photon here is a model. It is not the compact `U(1)` Wilson measure, and nothing in this
module links the two: the step "compact `U(1)` at large `β` is within `o(1)` in `D` of the Gaussian photon"
is not proved, and §5 records why it fails in two dimensions. Every free energy is taken as the Gaussian
determinant formula, as in `WindowFreq` (it is a definition, not derived from an integral).

## 1. Volume terms cancel; constants are multiplied by `2^d − 1` (proved)

* `dbl d F L = 2^d F(L) − F(2L)`, the doubling functional; `defectD_eq_dbl` (`WindowFreq.defectD` is
  `dbl` of `logZD`).
* `dbl_affine`: for `F(n) = a nᵈ + b + c G(n)`, `dbl d F L = (2^d − 1) b + c · dbl d G L`. The extensive part
  cancels exactly; a box-independent part `b` survives with weight `2^d − 1` (`15` in four dimensions).
* `defectD_eq`: `defectD m d L = −dbl d (logDetD m d) L / 2`.

## 2. Zero modes of the torus spectrum (proved)

* `phat2_eq_zero_iff`, `omega2D_zero_eq_zero_iff`: at `m = 0`, `ω²_k = 0` exactly when `k = 0`.
* `zeroModes_massless`, `nzCount_massless`: one zero mode, so `L^d − 1` non-zero modes.
* `omega2D_pos`, `nzCount_massive`: at `m ≠ 0`, no zero mode, `L^d` non-zero modes.

## 3. The coupling enters only through the zero modes (proved)

`logDetDβ β m d L = Σ_{ω²≠0} log(β ω²_k)` is the log-determinant of `β(−Δ + m²)`, and `logZDβ`, `defectDβ`
are the free energy and the doubling defect at coupling `β`, with the zero mode kept at the tree's weight
(`WindowFreq.logZD`: `(2π)^{1/2}` per mode, untouched by `β`, since `β` does not act on a flat direction).

* `logDetDβ_eq`: `logDetDβ = logDetD + #(non-zero modes) · log β`.
* `defectDβ_massive`: `m ≠ 0` ⇒ `defectDβ β m d L = defectD m d L`. The coupling drops out.
* `defectDβ_massless`: `defectDβ β 0 d L = defectD 0 d L + (2^d − 1)/2 · log β`. The non-zero-mode count is
  `L^d − 1`, so the coupling survives the cancellation of §1 through the single zero mode. At every fixed
  window `D → +∞` as `β → ∞` (`massless_tendsto_beta`).

## 4. The massless chain, exactly (proved)

* `logDetD_one`, `defectD_one`: the `d = 1` torus objects are `WindowFreq.logDet`, `WindowFreq.defect`.
* `chain_window`: `defectDβ β 0 1 (2^w) = log 2 − w log 2 + (log β)/2` (from
  `ZoomContract.freeWindow_massless`).
* `chain_tendsto_atBot`, `chain_not_vanishes`: at every `β > 0`, `D → −∞` along the windows; it does not
  tend to `0`.
* `chain_negative`: at every `β > 0` some window has `D < 0`. The Gaussian `D` is not non-negative, so it is
  not in the class `𝒜` of the map (`CouplingTower.windowCoupling_nonneg` fails for it), and the signed seed
  form `D ≤ 1/1000` holds for it at every `β` through the sign, not through a vanishing read.

## 5. The Gaussian photon (proved for the model)

The model, `logZPh β d L`: for each non-zero momentum `k`, `d − 1` transverse polarizations, each a Gaussian
factor `(2π/(β ω²_k))^{1/2}` (the action `β|dA|²/2` restricted to 1-forms modulo exact ones, where `d*d` acts
as `ω²_k` on the transverse space); the Faddeev–Popov Jacobian of the gauge orbit, `(ω²_k)^{1/2}` per
non-zero momentum (`β`-free); the zero modes in orthonormal link coordinates, all `β`-free: `d` harmonic
(flat-connection) modes, each a holonomy circle of length `2π L^{d/2−1}`, and the inverse of the constant-gauge
stabilizer, of length `2π L^{d/2}`, left after the gauge group is divided out. `transverse_finrank` proves the
polarization count: the orthogonal complement of a non-zero momentum vector in `ℝᵈ` has dimension `d − 1`.
The plaquette field of an abelian configuration is a closed 2-form (`CurveFloor.plaquette_closed`); the model
is the Gaussian measure on that space, and that identification is part of the model, not proved here.

* `logZPh_eq`: `logZPh = (d−1)/2 · (log 2π − log β)(L^d − 1) − (d−2)/2 · logDetD 0 d L + (d−1) log 2π
  + d(d−3)/2 · log L`. The `d − 1` transverse modes and the one Jacobian factor leave `d − 2` massless scalars.
* `defectPh_split`: `defectPh β d L = phRest d L + phCoeff d · log β`, `phCoeff d = (2^d − 1)(d − 1)/2`,
  `phRest = (d − 2) · defectD 0 d L + phCoeff · log 2π + d(d−3)/2 · ((2^d − 1) log L − log 2)`. The coupling
  enters only through the constant `−(d − 1)` of the non-zero transverse count `(d − 1)(L^d − 1)`.
* `photon4`: `D = 2 (defectD 0 4 L + 15 log L) + 45/2 (log β + log 2π) − 2 log 2`. The zero-mode volumes add
  `30 log L`, the leading `log L` that the two scalar `det′` defects lose (`log det′ = L⁴ f + 2 log L + c +
  o(1)`, Chinta–Jorgenson–Karlsson, cited): in general the `log L` coefficient of `D` is
  `(2^d − 1)(d − 1)(d − 4)/2`, which is zero exactly at `d = 4` (and `d = 1`).
* `photon2`: `D = 3/2 (log β + log 2π) + log 2 − 3 log L`; `photon2_tendsto_atBot`: `D → −∞` along the
  windows. Check (argued): the two-dimensional Villain torus has `Z = Σ_n e^{−n² L²/(2β)}` up to extensive
  factors, so for `L² ≪ β` its `log Z` is `½ log(2πβ) − log L`, the model's value.
* `photon_tendsto_beta`: for `d ≥ 2`, at every fixed window `D → +∞` as `β → ∞`.

## 6. The coupling is an additive shift (proved)

* `vanishes_at_most_one`, `not_frequently_of_unique`: if `D(β, w) = A(w) + c log β` with `c ≠ 0`, at most one
  positive coupling has `D(β, ·) → 0`, so the vanishing read cannot hold frequently as `β → ∞`.
* `photon_vanishes_unique`, `photon_not_strongEnd` (`d ≥ 2`), `massless_vanishes_unique` (`d ≥ 1`): the
  Gaussian photon and the massless scalar vanish at at most one coupling. The model fails the bridge's shape
  unconditionally, at every window profile, without the `det′` asymptotics.
* `photon4_stall_of`: if the scalar remainder `defectD 0 4 L + 15 log L` is bounded below along the windows
  (the cited asymptotics give convergence), then eventually in `β` every window has `D > 1/1000`: a stall on a
  ray of the map's kind, with `D` tending to a `β`-dependent constant along the zoom. `photon4_atBot_of`: if
  instead the remainder tends to `−∞`, so does `D`, at every `β`.

## 7. The mechanism

In the Gaussian photon, `D` splits into (i) `d − 2` copies of the massless scalar `det′` defect, with no `β`;
(ii) the zero-mode volumes (holonomies and the gauge stabilizer), with no `β` and a `log L` term; and (iii)
`phCoeff d · log β`, the only place the coupling enters, through the constant of the non-zero-mode count. In
four dimensions (i) and (ii) cancel at order `log L`, given the cited `det′` asymptotics (the scale invariance of the four-dimensional Maxwell
field), so what survives along the zoom is a constant plus (iii): the stall of the photon-like phase. In the
model the coupling does not dissolve the stall; it raises it by `45/2 · log β`.

What a proof of `StrongEnd N` must break, stated as a property and not claimed: at arbitrarily large `β`,
along some window that grows with `β`, the `SU(N)` Wilson measure's `D` is not within `o(1)` of a Gaussian
model whose coupling enters only as an additive `c log β` with `c > 0`. Equivalently, at large `β` and large
windows the compact measure must depart from its Gaussian (spin-wave) model: the flat-connection and
zero-mode volumes must stop being `β`-independent Gaussian volumes. Two-dimensional compact `U(1)` already
departs from its Gaussian model in this sense (character expansion, `log Z = L² log c₀(β) + O(e^{−cL²})`, so
its `D → 0` at every `β`; cited, not proved here); there the crossover is at `L² ≈ β`, where the model's `D`
changes sign.

## What does not follow

* Nothing here is a statement about `CouplingTower.windowCoupling`. The Gaussian photon is a model; no
  theorem links it to the compact `U(1)` or `SU(N)` Wilson measure.
* The Gaussian `D` is not non-negative (`chain_negative`, `photon2_tendsto_atBot`), so the models are not in
  the map's class `𝒜`; a signed seed `D ≤ 1/1000` can hold for them through the sign.
* The `d`-dimensional massless scalar `det′` asymptotics are not proved; the four-dimensional ray stall is
  conditional on them (`photon4_stall_of`). The massive `d`-dimensional vanishing (`WindowFreq.FreeCasimirD`)
  is not proved; only `d = 1` is (`WindowFreq.freeWindow_vanishes_iff`).
* The zero-mode volumes fix the `log 2π` and `log L` constants. The `log β` coefficient does not depend on
  them, provided they do not depend on `β`.
* `StrongEnd N` is neither proved nor refuted.

DERIVED (module-wide): `0` the zero mode, the signs and the limit; `1` the lattice spacing, the least box, the
single scalar zero mode, the least dimension and the gap between two couplings; `2` the doubling, the Gaussian
factor `1/2`, the square in `4 sin² = (2 sin)²`; `2π` the Gaussian normalization and the `U(1)` angle range;
`2^d` the copies; `2^d − 1` the copies less the doubled box; `d − 1` the transverse polarizations
(`transverse_finrank`); `d − 2` the transverse count less the Faddeev–Popov factor; `d/2 − 1`, `d/2` the
orthonormal rescaling of the zero modes, whence `d(d − 3)/2`; `3 = 2² − 1`, `15 = 2⁴ − 1`, `45/2 = 15 · 3/2`
and `30 = 2 · 15` their specialisations. Inherited: `1/1000` the seed level of `CouplingTower`
(`DoublingSharp`). Proof-internal: the `1` margin in `photon4_stall_of`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.PhotonStall

open Real Filter Topology Finset
open MassGap.WindowFreq (omega2D logDetD logZD defectD)

/-! ## 1. The doubling functional -/

/-- **The doubling functional** `2^d F(L) − F(2L)`. DERIVED: `2` the doubling, `2^d` the copies. -/
def dbl (d : ℕ) (F : ℕ → ℝ) (L : ℕ) : ℝ := 2 ^ d * F L - F (2 * L)

/-- DERIVED: no numeral beyond `dbl`. -/
theorem defectD_eq_dbl (m : ℝ) (d L : ℕ) : defectD m d L = dbl d (logZD m d) L := rfl

/-- **Volume terms cancel**: `dbl` of `a nᵈ + b + c G(n)` is `(2^d − 1) b + c · dbl G`.
DERIVED: `1` the box itself, `2` the doubling. -/
theorem dbl_affine (d : ℕ) (a b c : ℝ) (G : ℕ → ℝ) (L : ℕ) :
    dbl d (fun n => a * (n : ℝ) ^ d + b + c * G n) L = (2 ^ d - 1) * b + c * dbl d G L := by
  unfold dbl
  push_cast
  rw [mul_pow]
  ring

/-- **The scalar defect is the doubled `det′`**. DERIVED: `2` the Gaussian factor. -/
theorem defectD_eq (m : ℝ) (d L : ℕ) : defectD m d L = -(dbl d (logDetD m d) L / 2) := by
  unfold defectD logZD dbl
  push_cast
  rw [mul_pow]
  ring

/-! ## 2. Zero modes -/

/-- The modes with non-zero frequency. DERIVED: `0` the zero frequency. -/
def nzModes (m : ℝ) (d L : ℕ) : Finset (Fin d → Fin L) :=
  (Finset.univ : Finset (Fin d → Fin L)).filter (fun k => omega2D m d L k ≠ 0)

/-- The number of non-zero modes. DERIVED: none. -/
def nzCount (m : ℝ) (d L : ℕ) : ℕ := (nzModes m d L).card

/-- DERIVED: `0` the zero frequency. -/
theorem mem_nzModes {m : ℝ} {d L : ℕ} {k : Fin d → Fin L} : k ∈ nzModes m d L ↔ omega2D m d L k ≠ 0 := by
  simp [nzModes]

/-- DERIVED: none. -/
theorem logDetD_eq_nz (m : ℝ) (d L : ℕ) :
    logDetD m d L = ∑ k ∈ nzModes m d L, Real.log (omega2D m d L k) := rfl

/-- DERIVED: none. -/
theorem card_modes (d L : ℕ) : (Finset.univ : Finset (Fin d → Fin L)).card = L ^ d := by
  simp [Finset.card_univ, Fintype.card_fun]

/-- DERIVED: `0` the sign. -/
theorem phat2_nonneg (L j : ℕ) : 0 ≤ FreqRead.phat2 1 L j := by
  unfold FreqRead.phat2
  positivity

/-- **The single zero of the lattice momentum**: `4 sin²(π j/L) = 0` for `j < L` exactly when `j = 0`.
DERIVED: `0` the zero mode; `π` the half turn. -/
theorem phat2_eq_zero_iff {L : ℕ} (j : Fin L) : FreqRead.phat2 1 L (j : ℕ) = 0 ↔ (j : ℕ) = 0 := by
  unfold FreqRead.phat2
  constructor
  · intro h
    by_contra hj
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have hjpos : (0 : ℝ) < (j : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hlt : ((j : ℕ) : ℝ) < L := by exact_mod_cast j.isLt
    have h1 : 0 < π * ((j : ℕ) : ℝ) / L := by positivity
    have h2 : π * ((j : ℕ) : ℝ) / L < π := by
      rw [div_lt_iff₀ hL]
      nlinarith [Real.pi_pos]
    have hs := Real.sin_pos_of_pos_of_lt_pi h1 h2
    have : 0 < (2 / (1 : ℝ)) ^ 2 * Real.sin (π * ((j : ℕ) : ℝ) / L) ^ 2 := by positivity
    linarith
  · intro h
    rw [h]
    simp

/-- **The massless zero mode**: `ω²_k = 0` at `m = 0` exactly when every component of `k` is `0`.
DERIVED: `0` the mass and the zero mode; `2` the square. -/
theorem omega2D_zero_eq_zero_iff {d L : ℕ} (k : Fin d → Fin L) :
    omega2D 0 d L k = 0 ↔ ∀ μ, (k μ : ℕ) = 0 := by
  unfold omega2D
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add,
    Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => phat2_nonneg _ _)]
  simp only [Finset.mem_univ, true_implies]
  exact forall_congr' fun μ => phat2_eq_zero_iff (k μ)

/-- **One zero mode** at `m = 0`. DERIVED: `1` the single zero mode; `0` the zero momentum. -/
theorem zeroModes_massless {d L : ℕ} (hL : 0 < L) :
    ((Finset.univ : Finset (Fin d → Fin L)).filter (fun k => ¬ omega2D 0 d L k ≠ 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => ⟨0, hL⟩, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_singleton,
    omega2D_zero_eq_zero_iff]
  constructor
  · intro h
    funext μ
    exact Fin.ext (h μ)
  · rintro rfl μ
    rfl

/-- **`L^d − 1` non-zero modes** at `m = 0`. DERIVED: `1` the zero mode. -/
theorem nzCount_massless {d L : ℕ} (hL : 0 < L) : (nzCount 0 d L : ℝ) = (L : ℝ) ^ d - 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d → Fin L)))
    (fun k => omega2D 0 d L k ≠ 0)
  rw [zeroModes_massless hL, card_modes] at h
  unfold nzCount nzModes
  have h' : ((((Finset.univ : Finset (Fin d → Fin L)).filter (fun k => omega2D 0 d L k ≠ 0)).card : ℕ) : ℝ)
      + 1 = ((L ^ d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- **No zero mode** at `m ≠ 0`. DERIVED: `0` the sign; `2` the square. -/
theorem omega2D_pos {m : ℝ} (hm : m ≠ 0) {d L : ℕ} (k : Fin d → Fin L) : 0 < omega2D m d L k := by
  unfold omega2D
  have h1 := Finset.sum_nonneg (fun μ (_ : μ ∈ (Finset.univ : Finset (Fin d))) =>
    phat2_nonneg L (k μ : ℕ))
  have h2 : 0 < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  linarith

/-- **`L^d` non-zero modes** at `m ≠ 0`. DERIVED: none. -/
theorem nzCount_massive {m : ℝ} (hm : m ≠ 0) (d L : ℕ) : (nzCount m d L : ℝ) = (L : ℝ) ^ d := by
  unfold nzCount nzModes
  rw [Finset.filter_true_of_mem (fun k _ => (omega2D_pos hm k).ne'), card_modes]
  push_cast
  ring

/-! ## 3. The coupling -/

/-- **The log-determinant of `β(−Δ + m²)`** over the non-zero modes. DERIVED: `0` the excluded zero
frequency. -/
def logDetDβ (β m : ℝ) (d L : ℕ) : ℝ := ∑ k ∈ nzModes m d L, Real.log (β * omega2D m d L k)

/-- **The free energy at coupling `β`**, zero mode at the tree's weight. DERIVED: `2` the Gaussian factor,
`2π` its normalization. -/
def logZDβ (β m : ℝ) (d L : ℕ) : ℝ := (L : ℝ) ^ d / 2 * Real.log (2 * π) - logDetDβ β m d L / 2

/-- **The doubling defect at coupling `β`**. DERIVED: `2^d` the copies, `2` the doubling. -/
def defectDβ (β m : ℝ) (d L : ℕ) : ℝ := 2 ^ d * logZDβ β m d L - logZDβ β m d (2 * L)

/-- **`β` multiplies the non-zero modes only.** DERIVED: `0` the sign. -/
theorem logDetDβ_eq {β : ℝ} (hβ : 0 < β) (m : ℝ) (d L : ℕ) :
    logDetDβ β m d L = logDetD m d L + nzCount m d L * Real.log β := by
  have hterm : ∀ k ∈ nzModes m d L,
      Real.log (β * omega2D m d L k) = Real.log β + Real.log (omega2D m d L k) :=
    fun k hk => Real.log_mul hβ.ne' (mem_nzModes.mp hk)
  unfold logDetDβ nzCount
  rw [logDetD_eq_nz, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The coupling in the defect** is the doubled non-zero-mode count. DERIVED: `2` the doubling. -/
theorem defectDβ_eq {β : ℝ} (hβ : 0 < β) (m : ℝ) (d L : ℕ) :
    defectDβ β m d L = defectD m d L
      - Real.log β / 2 * (2 ^ d * (nzCount m d L : ℝ) - nzCount m d (2 * L)) := by
  unfold defectDβ logZDβ defectD logZD
  rw [logDetDβ_eq hβ, logDetDβ_eq hβ]
  ring

/-- **Massive: the coupling drops out.** DERIVED: `0` the sign; `2` the doubling. -/
theorem defectDβ_massive {β m : ℝ} (hβ : 0 < β) (hm : m ≠ 0) (d L : ℕ) :
    defectDβ β m d L = defectD m d L := by
  rw [defectDβ_eq hβ, nzCount_massive hm, nzCount_massive hm]
  push_cast
  rw [mul_pow]
  ring

/-- **Massless: the coupling survives through the zero mode**, with weight `(2^d − 1)/2`.
DERIVED: `1` the zero mode; `2` the doubling. -/
theorem defectDβ_massless {β : ℝ} (hβ : 0 < β) {d L : ℕ} (hL : 0 < L) :
    defectDβ β 0 d L = defectD 0 d L + (2 ^ d - 1) / 2 * Real.log β := by
  rw [defectDβ_eq hβ, nzCount_massless hL, nzCount_massless (by omega : 0 < 2 * L)]
  push_cast
  rw [mul_pow]
  ring

/-- DERIVED: `1` the least dimension; `2` the doubling. -/
theorem copies_sub_one_pos {d : ℕ} (hd : 1 ≤ d) : (0 : ℝ) < 2 ^ d - 1 := by
  have : (2 : ℝ) ≤ 2 ^ d := le_self_pow₀ (by norm_num) (by omega)
  linarith

/-- **At a fixed window the massless defect diverges with the coupling.** DERIVED: `0` the sign; `1` the
least dimension and box. -/
theorem massless_tendsto_beta {d L : ℕ} (hd : 1 ≤ d) (hL : 0 < L) :
    Tendsto (fun β => defectDβ β 0 d L) atTop atTop := by
  have hc : (0 : ℝ) < (2 ^ d - 1) / 2 := by have := copies_sub_one_pos hd; positivity
  have hlog : Tendsto (fun β => (2 ^ d - 1) / 2 * Real.log β) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hc
  refine tendsto_atTop.2 fun B => ?_
  filter_upwards [tendsto_atTop.1 hlog (B - defectD 0 d L), eventually_gt_atTop 0] with β hB hβ
  rw [defectDβ_massless hβ hL]
  linarith

/-! ## 4. The massless chain -/

/-- The filter is bookkeeping (`log 0 = 0`). DERIVED: `0` the zero frequency. -/
theorem logDetD_eq_sum (m : ℝ) (d L : ℕ) :
    logDetD m d L = ∑ k : Fin d → Fin L, Real.log (omega2D m d L k) := by
  unfold logDetD
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not.mp h, Real.log_zero]

/-- **The `d = 1` torus is the chain of `WindowFreq`.** DERIVED: `1` the dimension. -/
theorem logDetD_one (m : ℝ) (L : ℕ) : logDetD m 1 L = WindowFreq.logDet m L := by
  rw [logDetD_eq_sum, WindowFreq.logDet_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun j => Real.log (FreqRead.omega2 m 1 L j)) L,
    ← (Equiv.funUnique (Fin 1) (Fin L)).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [omega2D, FreqRead.omega2, Equiv.funUnique]

/-- DERIVED: `1` the dimension. -/
theorem defectD_one (m : ℝ) (L : ℕ) : defectD m 1 L = WindowFreq.defect m L := by
  rw [WindowFreq.defect_eq]
  unfold defectD logZD
  rw [logDetD_one, logDetD_one]
  push_cast
  ring

/-- **The massless chain at coupling `β`, along the windows**: `log 2 − w log 2 + (log β)/2`.
DERIVED: `0` the mass; `1` the dimension; `2` the doubling and the Gaussian factor. -/
theorem chain_window {β : ℝ} (hβ : 0 < β) (w : ℕ) :
    defectDβ β 0 1 (2 ^ w) = Real.log 2 - w * Real.log 2 + Real.log β / 2 := by
  have h := ZoomContract.freeWindow_massless w
  unfold WindowFreq.freeWindow at h
  rw [defectDβ_massless hβ (by positivity), defectD_one, h]
  ring

/-- **The massless chain diverges along the windows** at every coupling. DERIVED: `0` the sign. -/
theorem chain_tendsto_atBot {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun w : ℕ => defectDβ β 0 1 (2 ^ w)) atTop atBot := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : Tendsto (fun w : ℕ => (w : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hl
  refine tendsto_atBot.2 fun B => ?_
  filter_upwards [tendsto_atTop.1 h (Real.log 2 + Real.log β / 2 - B)] with w hw
  rw [chain_window hβ]
  linarith

/-- **The massless chain does not vanish.** DERIVED: `0` the limit. -/
theorem chain_not_vanishes {β : ℝ} (hβ : 0 < β) :
    ¬ Tendsto (fun w : ℕ => defectDβ β 0 1 (2 ^ w)) atTop (𝓝 0) :=
  not_tendsto_nhds_of_tendsto_atBot (chain_tendsto_atBot hβ) 0

/-- **The Gaussian defect is not non-negative**: some window has `D < 0`. DERIVED: `0` the sign. -/
theorem chain_negative {β : ℝ} (hβ : 0 < β) : ∃ w : ℕ, defectDβ β 0 1 (2 ^ w) < 0 :=
  ((chain_tendsto_atBot hβ).eventually (eventually_lt_atBot 0)).exists

/-! ## 5. The Gaussian photon -/

/-- **The transverse polarizations**: the orthogonal complement of a non-zero momentum in `ℝᵈ` has
dimension `d − 1`. DERIVED: `1` the longitudinal direction. -/
theorem transverse_finrank {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    Module.finrank ℝ (ℝ ∙ v)ᗮ = d - 1 := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
  have h1 : Module.finrank ℝ (ℝ ∙ v) = 1 := by
    first
    | exact finrank_span_singleton hv
    | exact Submodule.finrank_span_singleton hv
  rw [h1, finrank_euclideanSpace_fin] at h
  omega

/-- **The Gaussian photon free energy** (model). Per non-zero momentum: `d − 1` transverse Gaussian factors
`(2π/(β ω²))^{1/2}` and the Faddeev–Popov factor `(ω²)^{1/2}`. Zero modes, in orthonormal link coordinates:
`d` holonomy circles, each of length `2π L^{d/2 − 1}` (a holonomy angle `θ ∈ [0, 2π)` is `L` links of the
constant mode, whose unit vector has entries `L^{−d/2}`); the gauge group divided out, which leaves the
inverse of the constant-gauge stabilizer, of length `2π L^{d/2}`.
DERIVED: `d − 1` the transverse count (`transverse_finrank`); `2` the Gaussian factor; `2π` the Gaussian
normalization. CHOSEN: the zero-mode volumes `2π L^{d/2−1}` and `2π L^{d/2}` (the `U(1)` angle range and the
exponents of the orthonormal rescaling enter only through this model choice). -/
def logZPh (β : ℝ) (d L : ℕ) : ℝ :=
  (∑ k ∈ nzModes 0 d L,
      (((d : ℝ) - 1) / 2 * Real.log (2 * π / (β * omega2D 0 d L k)) + Real.log (omega2D 0 d L k) / 2))
    + d * (Real.log (2 * π) + ((d : ℝ) / 2 - 1) * Real.log L)
    - (Real.log (2 * π) + (d : ℝ) / 2 * Real.log L)

/-- **The Gaussian photon doubling defect.** DERIVED: `2^d` the copies, `2` the doubling. -/
def defectPh (β : ℝ) (d L : ℕ) : ℝ := 2 ^ d * logZPh β d L - logZPh β d (2 * L)

/-- **`d − 2` massless scalars plus zero modes.** DERIVED: `1` the zero mode; `2` the Gaussian factor;
`3 = 1 + 2` from `d(d/2 − 1) − d/2 = d(d − 3)/2`. -/
theorem logZPh_eq {β : ℝ} (hβ : 0 < β) {d L : ℕ} (hL : 0 < L) :
    logZPh β d L = ((d : ℝ) - 1) / 2 * (Real.log (2 * π) - Real.log β) * ((L : ℝ) ^ d - 1)
      - ((d : ℝ) - 2) / 2 * logDetD 0 d L + ((d : ℝ) - 1) * Real.log (2 * π)
      + (d : ℝ) * ((d : ℝ) - 3) / 2 * Real.log L := by
  unfold logZPh
  have h2π : (2 * π) ≠ 0 := by positivity
  have hterm : ∀ k ∈ nzModes 0 d L,
      ((d : ℝ) - 1) / 2 * Real.log (2 * π / (β * omega2D 0 d L k)) + Real.log (omega2D 0 d L k) / 2
        = ((d : ℝ) - 1) / 2 * (Real.log (2 * π) - Real.log β)
          - ((d : ℝ) - 2) / 2 * Real.log (omega2D 0 d L k) := by
    intro k hk
    have hk' := mem_nzModes.mp hk
    rw [Real.log_div h2π (mul_ne_zero hβ.ne' hk'), Real.log_mul hβ.ne' hk']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← logDetD_eq_nz]
  have hc := nzCount_massless (d := d) hL
  unfold nzCount at hc
  rw [hc]
  ring

/-- The coupling coefficient `(2^d − 1)(d − 1)/2`. DERIVED: the zero-mode constant `−(d − 1)` of the
transverse count, times `2^d − 1`, times the Gaussian `1/2`. -/
def phCoeff (d : ℕ) : ℝ := (2 ^ d - 1) * ((d : ℝ) - 1) / 2

/-- The coupling-free part of the photon defect. DERIVED: as in `defectPh_split`. -/
def phRest (d L : ℕ) : ℝ :=
  ((d : ℝ) - 2) * defectD 0 d L + phCoeff d * Real.log (2 * π)
    + (d : ℝ) * ((d : ℝ) - 3) / 2 * ((2 ^ d - 1) * Real.log L - Real.log 2)

/-- **The photon defect in closed form**: `D = phRest d L + phCoeff d · log β`, with
`phRest = (d − 2) · defectD 0 d L + phCoeff · log 2π + d(d − 3)/2 · ((2^d − 1) log L − log 2)`.
The coupling enters only through `phCoeff d · log β`. DERIVED: `1` the zero mode; `2` the doubling. -/
theorem defectPh_split {β : ℝ} (hβ : 0 < β) {d L : ℕ} (hL : 0 < L) :
    defectPh β d L = phRest d L + phCoeff d * Real.log β := by
  unfold defectPh phRest phCoeff defectD logZD
  rw [logZPh_eq hβ hL, logZPh_eq hβ (by omega : 0 < 2 * L)]
  have hl2 : Real.log (2 * (L : ℝ)) = Real.log 2 + Real.log L :=
    Real.log_mul (by norm_num) (by exact_mod_cast hL.ne')
  push_cast
  rw [mul_pow, hl2]
  ring

/-- DERIVED: `2` the least dimension with a transverse mode. -/
theorem phCoeff_pos {d : ℕ} (hd : 2 ≤ d) : 0 < phCoeff d := by
  unfold phCoeff
  have h1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have := copies_sub_one_pos (by omega : 1 ≤ d)
  positivity

/-- **Four dimensions**: `D = 2 (defectD 0 4 L + 15 log L) + 45/2 (log β + log 2π) − 2 log 2`. The `log L`
of the zero modes, `30 log L`, is exactly the one the two scalar `det′` defects lose at leading order.
DERIVED: `4` the dimension; `15 = 2⁴ − 1`; `2 = 4 − 2 = 4·1/2`; `45/2 = 15 · 3/2`. -/
theorem photon4 {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 0 < L) :
    defectPh β 4 L = 2 * (defectD 0 4 L + 15 * Real.log L)
      + 45 / 2 * (Real.log β + Real.log (2 * π)) - 2 * Real.log 2 := by
  rw [defectPh_split hβ hL]
  unfold phRest phCoeff
  push_cast
  ring

/-- **Two dimensions**: no propagating mode; `D = 3/2 (log β + log 2π) + log 2 − 3 log L`.
DERIVED: `2` the dimension; `3 = 2² − 1`. -/
theorem photon2 {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 0 < L) :
    defectPh β 2 L = 3 / 2 * (Real.log β + Real.log (2 * π)) + Real.log 2 - 3 * Real.log L := by
  rw [defectPh_split hβ hL]
  unfold phRest phCoeff
  push_cast
  ring

/-- **Two dimensions along the windows**: `D → −∞` at every coupling. DERIVED: `0` the sign. -/
theorem photon2_tendsto_atBot {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun w : ℕ => defectPh β 2 (2 ^ w)) atTop atBot := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : Tendsto (fun w : ℕ => (w : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hl
  refine tendsto_atBot.2 fun B => ?_
  filter_upwards [tendsto_atTop.1 h
    ((3 / 2 * (Real.log β + Real.log (2 * π)) + Real.log 2 - B) / 3)] with w hw
  rw [photon2 hβ (by positivity)]
  push_cast
  rw [Real.log_pow]
  linarith

/-- **At a fixed window the photon defect diverges with the coupling** (`d ≥ 2`). DERIVED: `0` the sign. -/
theorem photon_tendsto_beta {d L : ℕ} (hd : 2 ≤ d) (hL : 0 < L) :
    Tendsto (fun β => defectPh β d L) atTop atTop := by
  have hlog : Tendsto (fun β => phCoeff d * Real.log β) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (phCoeff_pos hd)
  refine tendsto_atTop.2 fun B => ?_
  filter_upwards [tendsto_atTop.1 hlog (B - phRest d L), eventually_gt_atTop 0] with β hB hβ
  rw [defectPh_split hβ hL]
  linarith

/-! ## 6. The coupling is an additive shift: at most one coupling vanishes -/

/-- **A `log β` shift admits at most one vanishing coupling.** If `D(β, w) = A(w) + c log β` with `c ≠ 0`,
two positive couplings at which `D(β, ·) → 0` are equal. DERIVED: `0` the limit. -/
theorem vanishes_at_most_one {A : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0) {β₁ β₂ : ℝ} (h1 : 0 < β₁) (h2 : 0 < β₂)
    (t1 : Tendsto (fun w => A w + c * Real.log β₁) atTop (𝓝 0))
    (t2 : Tendsto (fun w => A w + c * Real.log β₂) atTop (𝓝 0)) : β₁ = β₂ := by
  have h := t1.sub t2
  have hfun : (fun w => (A w + c * Real.log β₁) - (A w + c * Real.log β₂))
      = fun _ => c * (Real.log β₁ - Real.log β₂) := by
    funext w
    ring
  rw [hfun, sub_zero] at h
  have e := tendsto_nhds_unique tendsto_const_nhds h
  have hl : Real.log β₁ = Real.log β₂ := by
    rcases mul_eq_zero.mp e with h0 | h0
    · exact absurd h0 hc
    · linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) hl

/-- **At most one positive point ⇒ not frequently at `∞`.** DERIVED: `1` the least coupling taken and the
gap between the two couplings. -/
theorem not_frequently_of_unique {P : ℝ → Prop}
    (hu : ∀ β₁ β₂ : ℝ, 0 < β₁ → 0 < β₂ → P β₁ → P β₂ → β₁ = β₂) : ¬ ∃ᶠ β in atTop, P β := by
  intro h
  obtain ⟨b1, hb1, p1⟩ := frequently_atTop.1 h 1
  obtain ⟨b2, hb2, p2⟩ := frequently_atTop.1 h (b1 + 1)
  have := hu b1 b2 (by linarith) (by linarith) p1 p2
  linarith

/-- **The Gaussian photon vanishes at at most one coupling** (`d ≥ 2`), unconditionally.
DERIVED: `2` the least dimension; `0` the limit. -/
theorem photon_vanishes_unique {d : ℕ} (hd : 2 ≤ d) {β₁ β₂ : ℝ} (h1 : 0 < β₁) (h2 : 0 < β₂)
    (t1 : Tendsto (fun w : ℕ => defectPh β₁ d (2 ^ w)) atTop (𝓝 0))
    (t2 : Tendsto (fun w : ℕ => defectPh β₂ d (2 ^ w)) atTop (𝓝 0)) : β₁ = β₂ := by
  have e : ∀ β : ℝ, 0 < β →
      (fun w : ℕ => defectPh β d (2 ^ w)) = fun w => phRest d (2 ^ w) + phCoeff d * Real.log β :=
    fun β hβ => funext fun w => defectPh_split hβ (by positivity)
  rw [e β₁ h1] at t1
  rw [e β₂ h2] at t2
  exact vanishes_at_most_one (phCoeff_pos hd).ne' h1 h2 t1 t2

/-- **The Gaussian photon fails the bridge's shape** (`d ≥ 2`): it is not true that frequently as `β → ∞`
the defect tends to `0` along the windows. This is the model counterpart of `¬ StrongEnd`, not a statement
about the Wilson measure. DERIVED: `2` the least dimension. -/
theorem photon_not_strongEnd {d : ℕ} (hd : 2 ≤ d) :
    ¬ ∃ᶠ β in atTop, Tendsto (fun w : ℕ => defectPh β d (2 ^ w)) atTop (𝓝 0) :=
  not_frequently_of_unique fun _ _ h1 h2 t1 t2 => photon_vanishes_unique hd h1 h2 t1 t2

/-- **The massless scalar vanishes at at most one coupling** (`d ≥ 1`). DERIVED: `1` the least dimension
and box. -/
theorem massless_vanishes_unique {d : ℕ} (hd : 1 ≤ d) {β₁ β₂ : ℝ} (h1 : 0 < β₁) (h2 : 0 < β₂)
    (t1 : Tendsto (fun w : ℕ => defectDβ β₁ 0 d (2 ^ w)) atTop (𝓝 0))
    (t2 : Tendsto (fun w : ℕ => defectDβ β₂ 0 d (2 ^ w)) atTop (𝓝 0)) : β₁ = β₂ := by
  have e : ∀ β : ℝ, 0 < β → (fun w : ℕ => defectDβ β 0 d (2 ^ w))
      = fun w => defectD 0 d (2 ^ w) + (2 ^ d - 1) / 2 * Real.log β :=
    fun β hβ => funext fun w => defectDβ_massless hβ (by positivity)
  rw [e β₁ h1] at t1
  rw [e β₂ h2] at t2
  have hc : ((2 : ℝ) ^ d - 1) / 2 ≠ 0 := by have := copies_sub_one_pos hd; positivity
  exact vanishes_at_most_one hc h1 h2 t1 t2

/-- **Four dimensions, a stall on a ray, conditional on the scalar `det′` remainder.** If
`defectD 0 4 L + 15 log L` is bounded below along the windows (the `det′` asymptotics
`log det′ = L⁴ f + 2 log L + c + o(1)`, cited and not proved, give convergence), then eventually in `β`
every window has `D > 1/1000`. DERIVED: `0` the sign; `4` the dimension;
`15 = 2⁴ − 1` as in `photon4`. Inherited: `1/1000` the seed level of `CouplingTower`. -/
theorem photon4_stall_of {r : ℝ}
    (hR : ∀ w : ℕ, r ≤ defectD 0 4 (2 ^ w) + 15 * Real.log ((2 ^ w : ℕ) : ℝ)) :
    ∀ᶠ β in atTop, ∀ w : ℕ, 1 / 1000 < defectPh β 4 (2 ^ w) := by
  have hlog : Tendsto (fun β => 45 / 2 * Real.log β) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  filter_upwards [tendsto_atTop.1 hlog
      (1 / 1000 + 1 - 2 * r - 45 / 2 * Real.log (2 * π) + 2 * Real.log 2),
    eventually_gt_atTop 0] with β hB hβ w
  rw [photon4 hβ (by positivity)]
  have := hR w
  linarith

/-- **Four dimensions, the other branch**: if the scalar remainder tends to `−∞` along the windows, so does
the photon defect, at every `β > 0`. DERIVED: `4` the dimension, `0` the sign; `15 = 2⁴ − 1` as in
`photon4`. -/
theorem photon4_atBot_of
    (hS : Tendsto (fun w : ℕ => defectD 0 4 (2 ^ w) + 15 * Real.log ((2 ^ w : ℕ) : ℝ)) atTop atBot)
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun w : ℕ => defectPh β 4 (2 ^ w)) atTop atBot := by
  refine tendsto_atBot.2 fun B => ?_
  filter_upwards [tendsto_atBot.1 hS
    ((B - 45 / 2 * (Real.log β + Real.log (2 * π)) + 2 * Real.log 2) / 2)] with w hw
  rw [photon4 hβ (by positivity)]
  linarith

end MassGap.PhotonStall

end

#print axioms MassGap.PhotonStall.dbl_affine
#print axioms MassGap.PhotonStall.defectD_eq
#print axioms MassGap.PhotonStall.mem_nzModes
#print axioms MassGap.PhotonStall.phat2_eq_zero_iff
#print axioms MassGap.PhotonStall.omega2D_zero_eq_zero_iff
#print axioms MassGap.PhotonStall.zeroModes_massless
#print axioms MassGap.PhotonStall.nzCount_massless
#print axioms MassGap.PhotonStall.nzCount_massive
#print axioms MassGap.PhotonStall.logDetDβ_eq
#print axioms MassGap.PhotonStall.defectDβ_eq
#print axioms MassGap.PhotonStall.defectDβ_massive
#print axioms MassGap.PhotonStall.defectDβ_massless
#print axioms MassGap.PhotonStall.massless_tendsto_beta
#print axioms MassGap.PhotonStall.logDetD_one
#print axioms MassGap.PhotonStall.defectD_one
#print axioms MassGap.PhotonStall.chain_window
#print axioms MassGap.PhotonStall.chain_tendsto_atBot
#print axioms MassGap.PhotonStall.chain_not_vanishes
#print axioms MassGap.PhotonStall.chain_negative
#print axioms MassGap.PhotonStall.transverse_finrank
#print axioms MassGap.PhotonStall.logZPh_eq
#print axioms MassGap.PhotonStall.defectPh_split
#print axioms MassGap.PhotonStall.phCoeff_pos
#print axioms MassGap.PhotonStall.photon4
#print axioms MassGap.PhotonStall.photon2
#print axioms MassGap.PhotonStall.photon2_tendsto_atBot
#print axioms MassGap.PhotonStall.photon_tendsto_beta
#print axioms MassGap.PhotonStall.vanishes_at_most_one
#print axioms MassGap.PhotonStall.not_frequently_of_unique
#print axioms MassGap.PhotonStall.photon_vanishes_unique
#print axioms MassGap.PhotonStall.photon_not_strongEnd
#print axioms MassGap.PhotonStall.massless_vanishes_unique
#print axioms MassGap.PhotonStall.photon4_stall_of
#print axioms MassGap.PhotonStall.photon4_atBot_of
