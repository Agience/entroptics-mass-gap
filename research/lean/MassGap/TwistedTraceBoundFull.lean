import Mathlib
import MassGap.TwistedTraceBoundN
import MassGap.ChargedWordTrace

/-!
# MassGap.TwistedTraceBoundFull — on a fixed torus the SU(N) doubling defect stays large at weak coupling

This is the weak-coupling bound for every `N ≥ 2`, with the full centre `Z_N` acting on a slice.
`TwistedTraceBound` supplies the kernel bounds it uses (`iter_offdiag`, `iter_le_sp`, `ZR_lower`). The declarations live in the namespace `MassGap.TwistedTraceBoundN`, next to the centre action
and kernel bounds of `MassGap.TwistedTraceBoundN`, which they use.

Fix the torus of side `n = m + 1 = 2j` and the transfer in direction `0`, a kernel on the
configurations of one spatial slice. `a = kT^{∗j}` is the transfer over half the time extent,
`hs(a) = ZR(n⁴)` and `hs(a ∗ a) = ZR(2n × n³)`.

**The centre action.** `G = Z_N × Z_N` acts on a slice (`TwistedTraceBoundN.act`, `kT_act`). It
multiplies the holonomy `P_ν` around direction `ν` through the origin by `e(g_ν)` (`hol_act_self`). So
the word `w_q = P₂^{b'} P₁^{a'} (P₁*)^a (P₂*)^b` has its trace multiplied by `e(charge q g)`,
`charge q g = (a' − a) g₁ + (b' − b) g₂` (`tw_act`).

**The sector bound.** `FluxSectorFourier.hs_conv_le_three_quarters` gives
`hs(a ∗ a) ≤ (3/4) hs(a)²` from two inputs, for each slice `y`:
* if some word with `charge q g ≠ 0` has `|tr w_q(y)| > 1/2`, the `g`-twisted row at `y` is
  exponentially small. The trace moves by at least `κ/2` under `g`, with `κ = min_{c ≠ 0} |1 − e(c)|`
  (`exists_phase_gap`), while the time ladder makes `tr w_q` Lipschitz in the square root of the
  temporal action (`lip_tw`), so `kT` is at most `exp(−2β(Δ/L)²)`.
* the elements `g` with no such word form a set `H_y`. If some `g₀` lies outside it, then `h ↦ h + g₀`
  maps `H_y` into its complement (`charge` is additive), so `|H_y| ≤ |G|/2`. If `H_y = G`, every
  charged word has `|tr w_q(y)| ≤ 1/2`, and `ChargedWordTrace.exists_commutator_floor` with the spatial
  ladder (`comm_le`) gives spatial action at least `s₀ > 0` (`exists_sp_floor`), so `a(·, y)` is
  exponentially small.
* `ZR_lower` bounds `hs(a)` below by `c_η e^{−βη}`, `η` as small as needed.

So at every large `β`, `ZR(2n × n³) ≤ (3/4) ZR(n⁴)²` (`doubled_trace_le`); the one-direction defect is
at least `log(4/3) ≥ 1/4`, and `defectW N β n > 1/1000` (`defect_gt`). Hence `deltaLengthUnbounded`:
(B₂) for every `N ≥ 2`.

No asymptotic expansion enters. Every suppression is exponential in `β` and is compared with an
`e^{−βη}` lower bound on `ZR`.

Controls:
* `β = 0`: the suppression factors `e^{−βc}` equal `1` and the smallness hypothesis
  `ε + η ≤ hs(a)/4` fails. There every twisted trace equals the trace and the defect is `0`
  (`SeedZeroCoupling.defect_at_zero`). The bound is a statement at large `β` only.
* U(1): the same centre action is a symmetry and a U(1) holonomy has trace of modulus one, so the
  argument gives a large defect on every fixed torus at weak coupling for U(1) as well. That is
  correct: U(1) keeps the defect of order one at every side, and is separated from SU(N) by (A₂).

DERIVED (module-wide): `0` is the time direction and the flipped coordinate; `1`, `2` name the two
spatial directions; `1/2` is the trace window of `ChargedWordTrace`; `κ/2 = κ · (1/2)` and `κ/4` are
the trace jump and its share on one side of the triangle inequality; `L = 4N²(m+1)√(2N)` is the trace
factor `N`, the word length bound `2N` per holonomy, two holonomies, `m + 1` rungs, and the `√(2N)` of
`‖g − 1‖² = 2N ρ(g)`; `3/4` is `FluxSectorFourier`'s; `1/4 ≤ log(4/3)` is `1 − 1/x ≤ log x`.
-/

noncomputable section

namespace MassGap.TwistedTraceBoundN

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.HolonomyLadder
open MassGap.TwistedTraceBound (D d1 d2 d2_ne_d1 Tn Site step pos org step_self step_ne pos_succ
  pos_val pos_ne pos_period step_comm pos_step_comm iter_bounds iter_offdiag iter_le_sp exp_dec
  ZR_lower)
open MassGap.ChargedWordTrace (Idx word Charged)

/-- `e(k) = exp(2πik/N)`. -/
local notation "ee" => ZMod.stdAddChar

/-! ## 1. Words under conjugation, scaling and perturbation -/

section Matrices

variable {N : ℕ}

theorem conj_pow {A X : Matrix (Fin N) (Fin N) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∀ k : ℕ, (A * X * star A) ^ k = A * X ^ k * star A
  | 0 => by simp [mul_star_self hA]
  | k + 1 => by
    rw [pow_succ, conj_pow hA k, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star A) A, star_mul_self hA, Matrix.one_mul]


theorem word_conj {A X Y : Matrix (Fin N) (Fin N) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (q : Idx N) : word (A * X * star A) (A * Y * star A) q = A * word X Y q * star A := by
  have hc : ∀ Z : Matrix (Fin N) (Fin N) ℂ, star A * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, star_mul_self hA, Matrix.one_mul]
  unfold word
  rw [star_conj, star_conj, conj_pow hA, conj_pow hA, conj_pow hA, conj_pow hA]
  simp only [Matrix.mul_assoc, hc]

theorem word_smul (c₁ c₂ : ℂ) (X Y : Matrix (Fin N) (Fin N) ℂ) (q : Idx N) :
    word (c₁ • X) (c₂ • Y) q
      = (c₂ ^ (q.1 : ℕ) * c₁ ^ (q.2.1 : ℕ) * star c₁ ^ (q.2.2.1 : ℕ) * star c₂ ^ (q.2.2.2 : ℕ))
        • word X Y q := by
  unfold word
  simp only [star_smul, smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

open MassGap.FrobeniusUnitary

theorem norm_pow_sub_pow_le {U V : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∀ k : ℕ, ‖U ^ k - V ^ k‖ ≤ k * ‖U - V‖
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ]
    have ih := norm_pow_sub_pow_le hU hV k
    calc ‖U ^ k * U - V ^ k * V‖ ≤ ‖U ^ k - V ^ k‖ + ‖U - V‖ := norm_mul_sub_mul_le (pow_mem hV k) hU
      _ ≤ k * ‖U - V‖ + ‖U - V‖ := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * ‖U - V‖ := by push_cast; ring

/-- **A word is Lipschitz in its two unitaries.** -/
theorem norm_word_sub_le {X Y X' Y' : Matrix (Fin N) (Fin N) ℂ}
    (hX : X ∈ Matrix.unitaryGroup (Fin N) ℂ) (hY : Y ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hX' : X' ∈ Matrix.unitaryGroup (Fin N) ℂ) (hY' : Y' ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (q : Idx N) : ‖word X Y q - word X' Y' q‖ ≤ 2 * N * (‖X - X'‖ + ‖Y - Y'‖) := by
  unfold word
  have hsX : star X ∈ Matrix.unitaryGroup (Fin N) ℂ := Unitary.star_mem hX
  have hsY : star Y ∈ Matrix.unitaryGroup (Fin N) ℂ := Unitary.star_mem hY
  have hsX' : star X' ∈ Matrix.unitaryGroup (Fin N) ℂ := Unitary.star_mem hX'
  have hsY' : star Y' ∈ Matrix.unitaryGroup (Fin N) ℂ := Unitary.star_mem hY'
  have u1 : Y' ^ (q.1 : ℕ) * X' ^ (q.2.1 : ℕ) * star X' ^ (q.2.2.1 : ℕ)
      ∈ Matrix.unitaryGroup (Fin N) ℂ := mul_mem (mul_mem (pow_mem hY' _) (pow_mem hX' _))
        (pow_mem hsX' _)
  have u2 : Y' ^ (q.1 : ℕ) * X' ^ (q.2.1 : ℕ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mul_mem (pow_mem hY' _) (pow_mem hX' _)
  have h1 := norm_mul_sub_mul_le (A := Y ^ (q.1 : ℕ) * X ^ (q.2.1 : ℕ) * star X ^ (q.2.2.1 : ℕ))
    (B' := star Y' ^ (q.2.2.2 : ℕ)) u1 (pow_mem hsY (q.2.2.2 : ℕ))
  have h2 := norm_mul_sub_mul_le (A := Y ^ (q.1 : ℕ) * X ^ (q.2.1 : ℕ))
    (B' := star X' ^ (q.2.2.1 : ℕ)) u2 (pow_mem hsX (q.2.2.1 : ℕ))
  have h3 := norm_mul_sub_mul_le (A := Y ^ (q.1 : ℕ)) (B' := X' ^ (q.2.1 : ℕ))
    (pow_mem hY' (q.1 : ℕ)) (pow_mem hX (q.2.1 : ℕ))
  have p1 := norm_pow_sub_pow_le hY hY' (q.1 : ℕ)
  have p2 := norm_pow_sub_pow_le hX hX' (q.2.1 : ℕ)
  have p3 := norm_pow_sub_pow_le hsX hsX' (q.2.2.1 : ℕ)
  have p4 := norm_pow_sub_pow_le hsY hsY' (q.2.2.2 : ℕ)
  rw [norm_star_sub_star] at p3 p4
  have nX := norm_nonneg (X - X')
  have nY := norm_nonneg (Y - Y')
  have b1 : ((q.1 : ℕ) : ℝ) ≤ N := by exact_mod_cast q.1.isLt.le
  have b2 : ((q.2.1 : ℕ) : ℝ) ≤ N := by exact_mod_cast q.2.1.isLt.le
  have b3 : ((q.2.2.1 : ℕ) : ℝ) ≤ N := by exact_mod_cast q.2.2.1.isLt.le
  have b4 : ((q.2.2.2 : ℕ) : ℝ) ≤ N := by exact_mod_cast q.2.2.2.isLt.le
  have m1 := mul_le_mul_of_nonneg_right b1 nY
  have m2 := mul_le_mul_of_nonneg_right b2 nX
  have m3 := mul_le_mul_of_nonneg_right b3 nX
  have m4 := mul_le_mul_of_nonneg_right b4 nY
  linarith

end Frob

end Matrices

/-! ## 2. Holonomies and words -/

section Holonomy

variable {N m : ℕ}

/-- The holonomy around direction `ν` through `y`. -/
def hol (ν : D) (V : Cfg m N) (y : Site m) : Matrix (Fin N) (Fin N) ℂ :=
  lprod (fun i => ((V (ν, pos ν i y) : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)) (m + 1)

theorem lprod_congr {f f' : ℕ → Matrix (Fin N) (Fin N) ℂ} (k : ℕ) (h : ∀ i < k, f i = f' i) :
    lprod f k = lprod f' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lprod_succ, lprod_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem lprod_succ' (f : ℕ → Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    lprod f (k + 1) = f 0 * lprod (fun i => f (i + 1)) k := by
  induction k with
  | zero => rw [lprod_succ, lprod_zero, lprod_zero, Matrix.one_mul, Matrix.mul_one]
  | succ k ih => rw [lprod_succ, ih, lprod_succ, Matrix.mul_assoc]

theorem lprod_memSU {f : ℕ → Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ i, f i ∈ Matrix.specialUnitaryGroup (Fin N) ℂ) (k : ℕ) :
    lprod f k ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  induction k with
  | zero => rw [lprod_zero]; exact one_mem _
  | succ k ih => rw [lprod_succ]; exact mul_mem ih (hf k)

theorem hol_memSU (ν : D) (V : Cfg m N) (y : Site m) :
    hol ν V y ∈ Matrix.specialUnitaryGroup (Fin N) ℂ :=
  lprod_memSU (fun i => (V (ν, pos ν i y)).2) _

theorem hol_memU (ν : D) (V : Cfg m N) (y : Site m) :
    hol ν V y ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (hol_memSU ν V y)).1

theorem continuous_lprod {Y : Type*} [TopologicalSpace Y]
    {f : ℕ → Y → Matrix (Fin N) (Fin N) ℂ} (hf : ∀ i, Continuous (f i)) (k : ℕ) :
    Continuous fun y => lprod (fun i => f i y) k := by
  induction k with
  | zero => simp only [lprod_zero]; exact continuous_const
  | succ k ih => simp only [lprod_succ]; exact ih.mul (hf k)

theorem continuous_hol (ν : D) (y : Site m) : Continuous fun V : Cfg m N => hol ν V y := by
  unfold hol
  exact continuous_lprod
    (f := fun i (V : Cfg m N) => ((V (ν, pos ν i y) : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))
    (fun i => continuous_subtype_val.comp (continuous_apply (ν, pos ν i y))) (m + 1)

/-- **The trace of a word in the two holonomies through the origin.** -/
def tw (q : Idx N) (V : Cfg m N) : ℂ :=
  Matrix.trace (word (hol d1 V org) (hol d2 V org) q)

theorem continuous_tw (q : Idx N) : Continuous (tw (m := m) q) := by
  have h1 := continuous_hol (N := N) (m := m) d1 org
  have h2 := continuous_hol (N := N) (m := m) d2 org
  unfold tw word
  exact ((((h2.pow _).mul (h1.pow _)).mul (h1.matrix_conjTranspose.pow _)).mul
    (h2.matrix_conjTranspose.pow _)).matrix_trace

end Holonomy

section Charge

variable {N m : ℕ} [NeZero N]

/-- **The charge** `(a' − a) g₁ + (b' − b) g₂` of the word `q` under `g`. -/
def charge (q : Idx N) (g : ZMod N × ZMod N) : ZMod N :=
  (((q.2.1 : ℕ) : ZMod N) - ((q.2.2.1 : ℕ) : ZMod N)) * g.1
    + (((q.1 : ℕ) : ZMod N) - ((q.2.2.2 : ℕ) : ZMod N)) * g.2

theorem charge_add (q : Idx N) (g h : ZMod N × ZMod N) :
    charge q (g + h) = charge q g + charge q h := by
  unfold charge; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem exists_charge_ne {q : Idx N} (hq : Charged q) : ∃ g : ZMod N × ZMod N, charge q g ≠ 0 := by
  rcases hq with h | h
  · refine ⟨(1, 0), fun h0 => h (natCast_fin_inj ?_)⟩
    unfold charge at h0
    simp only [mul_one, mul_zero, add_zero] at h0
    exact sub_eq_zero.mp h0
  · refine ⟨(0, 1), fun h0 => h (natCast_fin_inj ?_)⟩
    unfold charge at h0
    simp only [mul_one, mul_zero, zero_add] at h0
    exact sub_eq_zero.mp h0

theorem phase_eq (q : Idx N) (g : ZMod N × ZMod N) :
    ee g.2 ^ (q.1 : ℕ) * ee g.1 ^ (q.2.1 : ℕ) * star (ee g.1) ^ (q.2.2.1 : ℕ)
      * star (ee g.2) ^ (q.2.2.2 : ℕ) = ee (charge q g) := by
  rw [star_ee, star_ee, ee_pow, ee_pow, ee_pow, ee_pow, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [charge, nsmul_eq_mul]
  ring

/-- The action multiplies the holonomy around `ν` through the origin by `e(ph g ν)`. -/
theorem hol_act_self (g : ZMod N × ZMod N) (ν : D) (V : Cfg m N) :
    hol ν (act g V) org = ee (ph g ν) • hol ν V org := by
  unfold hol
  rw [lprod_succ', lprod_succ']
  have h0 : lc g (ν, pos ν 0 (org (m := m))) = ph g ν := by
    unfold lc; rw [if_pos]; simp [pos, org]
  have hrest : lprod (fun i => ((act g V (ν, pos ν (i + 1) org) : SUN.SU N)
      : Matrix (Fin N) (Fin N) ℂ)) m
      = lprod (fun i => ((V (ν, pos ν (i + 1) org) : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)) m := by
    refine lprod_congr m fun i hi => ?_
    rw [coe_act]
    have : lc g (ν, pos ν (i + 1) (org (m := m))) = 0 := by
      unfold lc
      rw [if_neg]
      intro h
      have h' : (pos ν (i + 1) (org (m := m)) ν).val = 0 := h
      rw [pos_val] at h'
      have h0' : (org (m := m) ν).val = 0 := rfl
      rw [h0', zero_add, Nat.mod_eq_of_lt (by omega)] at h'
      omega
    rw [this, AddChar.map_zero_eq_one, one_smul]
  rw [hrest, coe_act, h0, Matrix.smul_mul]

/-- **The trace of a word picks up the phase of its charge.** -/
theorem tw_act (q : Idx N) (g : ZMod N × ZMod N) (V : Cfg m N) :
    tw q (act g V) = ee (charge q g) * tw q V := by
  unfold tw
  rw [hol_act_self, hol_act_self, ph_d1, ph_d2, word_smul, Matrix.trace_smul, phase_eq, smul_eq_mul]

theorem norm_tw_act (q : Idx N) (g : ZMod N × ZMod N) (V : Cfg m N) :
    ‖tw q (act g V)‖ = ‖tw q V‖ := by
  rw [tw_act, norm_mul, norm_ee, one_mul]

end Charge

/-! ## 3. The ladders -/

section Ladders

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

open MassGap.FrobeniusUnitary

variable {N m : ℕ}

/-- **The time ladder.** Across one time step, the holonomy through `y` moves by at most
`(m+1) √(2N tp)`, conjugated by the axis link at `y`. -/
theorem time_ladder (hN : N ≠ 0) (A : TT 0 (Tn m) → SUN.SU N) (V V' : Cfg m N) (ν : D)
    (y : Site m) :
    ‖hol ν V y - ((A y : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) * hol ν V' y
        * star ((A y : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)‖
      ≤ (m + 1) * Real.sqrt (2 * N * tpT 0 (Tn m) A V V') := by
  set u : ℕ → Matrix (Fin N) (Fin N) ℂ := fun i => ((V (ν, pos ν i y) : SUN.SU N) : Matrix _ _ ℂ)
  set v : ℕ → Matrix (Fin N) (Fin N) ℂ := fun i => ((V' (ν, pos ν i y) : SUN.SU N) : Matrix _ _ ℂ)
  set w : ℕ → Matrix (Fin N) (Fin N) ℂ := fun i => ((A (pos ν i y) : SUN.SU N) : Matrix _ _ ℂ)
  have h := ladder u v w (fun i => coeU _) (fun i => coeU _) (fun i => coeU _) (m + 1)
  have hw : w (m + 1) = w 0 := by simp only [w]; rw [pos_period]; rfl
  rw [hw] at h
  have hterm : ∀ i, ‖u i - w i * v i * star (w (i + 1))‖
      ≤ Real.sqrt (2 * N * tpT 0 (Tn m) A V V') := by
    intro i
    rw [norm_sub_eq_one_sub (coeU _), norm_sub_rev]
    have e : w i * v i * star (w (i + 1)) * star (u i)
        = ((A (pos ν i y) * V' (ν, pos ν i y) * (A (tsh 0 (Tn m) ν (pos ν i y)))⁻¹
            * (V (ν, pos ν i y))⁻¹ : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
      simp only [Submonoid.coe_mul, coe_inv, w, v, u, pos_succ]
    rw [e]
    exact norm_sub_one_le hN _ (wd_le_tp hN A V V' ν (pos ν i y))
  calc ‖lprod u (m + 1) - w 0 * lprod v (m + 1) * star (w 0)‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖u i - w i * v i * star (w (i + 1))‖ := h
    _ ≤ ∑ _i ∈ Finset.range (m + 1), Real.sqrt (2 * N * tpT 0 (Tn m) A V V') :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (m + 1) * Real.sqrt (2 * N * tpT 0 (Tn m) A V V') := by simp

/-- **The spatial ladder for one row.** -/
theorem row_ladder (hN : N ≠ 0) (V : Cfg m N) (j : ℕ) :
    ‖hol d1 V (pos d2 j org)
        - ((V (d2, pos d2 j org) : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          * hol d1 V (pos d2 (j + 1) org)
          * star ((V (d2, pos d2 j org) : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)‖
      ≤ (m + 1) * Real.sqrt (2 * N * spT 0 (Tn m) V) := by
  set yj := pos d2 j (org (m := m))
  set u : ℕ → Matrix (Fin N) (Fin N) ℂ := fun i => ((V (d1, pos d1 i yj) : SUN.SU N) : Matrix _ _ ℂ)
  set v : ℕ → Matrix (Fin N) (Fin N) ℂ :=
    fun i => ((V (d1, pos d1 i (pos d2 (j + 1) org)) : SUN.SU N) : Matrix _ _ ℂ)
  set w : ℕ → Matrix (Fin N) (Fin N) ℂ := fun i => ((V (d2, pos d1 i yj) : SUN.SU N) : Matrix _ _ ℂ)
  have h := ladder u v w (fun i => coeU _) (fun i => coeU _) (fun i => coeU _) (m + 1)
  have hw : w (m + 1) = w 0 := by simp only [w]; rw [pos_period]; rfl
  rw [hw] at h
  have hterm : ∀ i, ‖u i - w i * v i * star (w (i + 1))‖
      ≤ Real.sqrt (2 * N * spT 0 (Tn m) V) := by
    intro i
    have hY : w (i + 1) * star (v i) * star (w i) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      mul_mem (mul_mem (coeU _) (Unitary.star_mem (coeU _))) (Unitary.star_mem (coeU _))
    have hXY : w i * v i * star (w (i + 1)) * (w (i + 1) * star (v i) * star (w i)) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (w (i + 1))) (w (i + 1)), star_mul_self (coeU _), Matrix.one_mul,
        ← Matrix.mul_assoc (v i) (star (v i)), mul_star_self (coeU _), Matrix.one_mul,
        mul_star_self (coeU _)]
    rw [norm_sub_eq_mul_sub_one hY hXY]
    have hcomm : tsh 0 (Tn m) d2 (pos d1 i yj) = pos d1 i (pos d2 (j + 1) org) := by
      show step d2 (pos d1 i yj) = _
      rw [← pos_step_comm (Ne.symm d2_ne_d1), pos_succ]
    have e : u i * (w (i + 1) * star (v i) * star (w i))
        = ((V (d1, pos d1 i yj) * V (d2, tsh 0 (Tn m) d1 (pos d1 i yj))
            * (V (d1, tsh 0 (Tn m) d2 (pos d1 i yj)))⁻¹ * (V (d2, pos d1 i yj))⁻¹ : SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ) := by
      rw [hcomm]
      simp only [Submonoid.coe_mul, coe_inv, w, v, u, pos_succ, Matrix.mul_assoc]
    rw [e]
    exact norm_sub_one_le hN _ (wd_le_sp hN V d1 d2 (pos d1 i yj))
  calc ‖lprod u (m + 1) - w 0 * lprod v (m + 1) * star (w 0)‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖u i - w i * v i * star (w (i + 1))‖ := h
    _ ≤ ∑ _i ∈ Finset.range (m + 1), Real.sqrt (2 * N * spT 0 (Tn m) V) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (m + 1) * Real.sqrt (2 * N * spT 0 (Tn m) V) := by simp

/-- **Lattice Stokes on the `(1,2)` torus.** -/
theorem comm_le (hN : N ≠ 0) (V : Cfg m N) :
    ‖hol d1 V org * hol d2 V org - hol d2 V org * hol d1 V org‖
      ≤ (m + 1) * ((m + 1) * Real.sqrt (2 * N * spT 0 (Tn m) V)) := by
  set c : ℕ → Matrix (Fin N) (Fin N) ℂ :=
    fun j => ((V (d2, pos d2 j org) : SUN.SU N) : Matrix _ _ ℂ)
  set R : ℕ → Matrix (Fin N) (Fin N) ℂ := fun j => hol d1 V (pos d2 j org)
  set E := (m + 1) * Real.sqrt (2 * N * spT 0 (Tn m) V)
  have hchain : ∀ k : ℕ, ‖R 0 - lprod c k * R k * star (lprod c k)‖ ≤ k * E := by
    intro k
    induction k with
    | zero =>
      simp only [lprod_zero, Matrix.one_mul, star_one, Matrix.mul_one, sub_self, norm_zero]
      simp
    | succ k ih =>
      have hC := lprod_mem (fun j => coeU (V (d2, pos d2 j org))) k
      have e : R 0 - lprod c (k + 1) * R (k + 1) * star (lprod c (k + 1))
          = (R 0 - lprod c k * R k * star (lprod c k))
            + lprod c k * (R k - c k * R (k + 1) * star (c k)) * star (lprod c k) := by
        rw [lprod_succ, star_mul]
        simp only [mul_sub, sub_mul, Matrix.mul_assoc]
        abel
      rw [e]
      have hrow := row_ladder hN V k
      calc ‖(R 0 - lprod c k * R k * star (lprod c k))
            + lprod c k * (R k - c k * R (k + 1) * star (c k)) * star (lprod c k)‖
          ≤ ‖R 0 - lprod c k * R k * star (lprod c k)‖
            + ‖lprod c k * (R k - c k * R (k + 1) * star (c k)) * star (lprod c k)‖ :=
            norm_add_le _ _
        _ = ‖R 0 - lprod c k * R k * star (lprod c k)‖
            + ‖R k - c k * R (k + 1) * star (c k)‖ := by
            rw [frob_mul_unitary (Unitary.star_mem hC), frob_unitary_mul hC]
        _ ≤ k * E + E := add_le_add ih hrow
        _ = ((k + 1 : ℕ) : ℝ) * E := by push_cast; ring
  have h := hchain (m + 1)
  have hR : R (m + 1) = R 0 := by simp only [R]; rw [pos_period]; rfl
  have hP2 : lprod c (m + 1) = hol d2 V org := rfl
  rw [hR, hP2] at h
  have hP2u : hol d2 V org ∈ Matrix.unitaryGroup (Fin N) ℂ := hol_memU _ _ _
  have e2 : hol d1 V org * hol d2 V org - hol d2 V org * hol d1 V org
      = (R 0 - hol d2 V org * R 0 * star (hol d2 V org)) * hol d2 V org := by
    simp only [R]
    rw [sub_mul, Matrix.mul_assoc _ (star _), star_mul_self hP2u, Matrix.mul_one]
    rfl
  rw [e2, frob_mul_unitary hP2u]
  calc ‖R 0 - hol d2 V org * R 0 * star (hol d2 V org)‖ ≤ ((m + 1 : ℕ) : ℝ) * E := h
    _ = _ := by push_cast; ring

/-- **A slice with every charged word of small trace has spatial action at least `s₀ > 0`.** -/
theorem exists_sp_floor (hN : 2 ≤ N) (m : ℕ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ V : Cfg m N, (∀ q : Idx N, Charged q → ‖tw q V‖ ≤ 1 / 2) →
      s₀ ≤ spT 0 (Tn m) V := by
  have hN0 : N ≠ 0 := by omega
  obtain ⟨δ, hδ, hfloor⟩ := ChargedWordTrace.exists_commutator_floor hN
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hNR : (0 : ℝ) < 2 * N := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    linarith
  refine ⟨(δ / ((m : ℝ) + 1) ^ 2) ^ 2 / (2 * N), by positivity, fun V hV => ?_⟩
  have hc := hfloor ⟨hol d1 V org, hol_memSU _ _ _⟩ ⟨hol d2 V org, hol_memSU _ _ _⟩ hV
  have hl := comm_le hN0 V
  have hsp := sp_nonneg hN0 V
  have hs : δ / ((m : ℝ) + 1) ^ 2 ≤ Real.sqrt (2 * N * spT 0 (Tn m) V) := by
    rw [div_le_iff₀ (by positivity)]
    have : δ ≤ (m + 1) * ((m + 1) * Real.sqrt (2 * N * spT 0 (Tn m) V)) := hc.trans hl
    nlinarith
  have hs' : (δ / ((m : ℝ) + 1) ^ 2) ^ 2 ≤ 2 * N * spT 0 (Tn m) V := by
    have := pow_le_pow_left₀ (by positivity) hs 2
    rwa [Real.sq_sqrt (by positivity)] at this
  rw [div_le_iff₀ hNR]
  linarith

/-- **The word traces are Lipschitz in the temporal action.** -/
theorem lip_tw (hN : N ≠ 0) (q : Idx N) (A : TT 0 (Tn m) → SUN.SU N) (V V' : Cfg m N) :
    ‖tw q V - tw q V'‖
      ≤ (4 * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * Real.sqrt (2 * N)) * Real.sqrt (tpT 0 (Tn m) A V V') := by
  set a := ((A org : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
  have hA := coeU (A org)
  have h1 := time_ladder hN A V V' d1 org
  have h2 := time_ladder hN A V V' d2 org
  have hQ1 : a * hol d1 V' org * star a ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mul_mem (mul_mem hA (hol_memU _ _ _)) (Unitary.star_mem hA)
  have hQ2 : a * hol d2 V' org * star a ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mul_mem (mul_mem hA (hol_memU _ _ _)) (Unitary.star_mem hA)
  have hw := norm_word_sub_le (hol_memU d1 V org) (hol_memU d2 V org) hQ1 hQ2 q
  have htr : tw q V - tw q V' = Matrix.trace (word (hol d1 V org) (hol d2 V org) q
      - word (a * hol d1 V' org * star a) (a * hol d2 V' org * star a) q) := by
    rw [word_conj hA, Matrix.trace_sub, trace_conj hA]; rfl
  have ht := abs_trace_le (N := N) (word (hol d1 V org) (hol d2 V org) q
      - word (a * hol d1 V' org * star a) (a * hol d2 V' org * star a) q)
  have hsq : Real.sqrt (2 * N * tpT 0 (Tn m) A V V')
      = Real.sqrt (2 * N) * Real.sqrt (tpT 0 (Tn m) A V V') :=
    Real.sqrt_mul (by positivity) _
  rw [hsq] at h1 h2
  rw [htr]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs1 := Real.sqrt_nonneg (2 * (N : ℝ))
  have hs2 := Real.sqrt_nonneg (tpT 0 (Tn m) A V V')
  have hsum : ‖hol d1 V org - a * hol d1 V' org * star a‖ + ‖hol d2 V org - a * hol d2 V' org * star a‖
      ≤ 2 * ((m + 1) * (Real.sqrt (2 * N) * Real.sqrt (tpT 0 (Tn m) A V V'))) := by linarith
  calc ‖Matrix.trace (word (hol d1 V org) (hol d2 V org) q
        - word (a * hol d1 V' org * star a) (a * hol d2 V' org * star a) q)‖
      ≤ N * ‖word (hol d1 V org) (hol d2 V org) q
        - word (a * hol d1 V' org * star a) (a * hol d2 V' org * star a) q‖ := ht
    _ ≤ N * (2 * N * (‖hol d1 V org - a * hol d1 V' org * star a‖
          + ‖hol d2 V org - a * hol d2 V' org * star a‖)) :=
        mul_le_mul_of_nonneg_left hw hN0
    _ ≤ N * (2 * N * (2 * ((m + 1) * (Real.sqrt (2 * N) * Real.sqrt (tpT 0 (Tn m) A V V'))))) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Ladders

/-! ## 4. Assembly -/

section Assembly

variable {N : ℕ} [NeZero N]

/-- **The doubled trace on the torus of side `2j` is at most three quarters of the squared trace at
every large `β`.** -/
theorem doubled_trace_le (hN : 2 ≤ N) (j m : ℕ) (hj : 1 ≤ j) (hm : m + 1 = 2 * j) :
    ∀ᶠ β in atTop,
      hs (hS 0 (Tn m) N) (conv (hS 0 (Tn m) N)
          (iter (hS 0 (Tn m) N) (kT 0 (Tn m) N β) (j - 1))
          (iter (hS 0 (Tn m) N) (kT 0 (Tn m) N β) (j - 1)))
        ≤ 3 / 4 * hs (hS 0 (Tn m) N) (iter (hS 0 (Tn m) N) (kT 0 (Tn m) N β) (j - 1)) ^ 2 := by
  classical
  have hN0 : N ≠ 0 := by omega
  obtain ⟨s₀, hs₀0, hfloor⟩ := exists_sp_floor hN m
  obtain ⟨κ, hκ, hκle⟩ := exists_phase_gap (N := N)
  set L : ℝ := 4 * (N : ℝ) ^ 2 * ((m : ℝ) + 1) * Real.sqrt (2 * N) with hLdef
  have hL : 0 < L := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : 0 < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  set c₁ : ℝ := 2 * ((κ / 4) / ((j : ℝ) * L)) ^ 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set κ' : ℝ := min c₁ s₀ / 2 with hκ'
  have hκ'0 : 0 < κ' := by positivity
  obtain ⟨c₀, hc₀, hZl⟩ := ZR_lower (N := N) hN0 (fun _ => m + 1) hκ'0
  have hT : Tendsto (fun β : ℝ => Real.exp (-(β * κ'))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hκ'0)
  have hev : ∀ᶠ β in atTop, Real.exp (-(β * κ')) < c₀ / 8 :=
    hT.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβe hβ
  set k := kT 0 (Tn m) N β
  set μ := hS 0 (Tn m) N
  have hkb : Bdd k := bdd_kT hN0 hβ
  have hk0 : ∀ x y, 0 ≤ k x y := kT_nonneg hN0 hβ
  have hk1 : ∀ x y, k x y ≤ 1 := kT_le_one hN0 hβ
  set a := iter μ k (j - 1) with ha
  have hab : Bdd a := hkb.iter (j - 1)
  have hbnd := iter_bounds (μ := μ) hkb hk0 hk1 (j - 1)
  have ha0 : ∀ x y, 0 ≤ a x y := fun x y => (hbnd x y).1
  have hsym : ∀ x y, a x y = a y x := CyclicKernel.iter_symm hkb (kT_symm β) (j - 1)
  have hA := centreAction (m := m) (N := N)
  have hinv : ∀ g x y, a (act g x) (act g y) = a x y := fun g x y =>
    iter_inv_act hA (fun g x y => kT_act g β x y) (j - 1) g x y
  -- the off-diagonal bound for each word
  have hj' : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    rw [Nat.cast_sub hj]; push_cast; ring
  have offd : ∀ (q : Idx N) (x y : Cfg m N),
      a x y ≤ Real.exp (-2 * β * (‖tw q x - tw q y‖ / ((j : ℝ) * L)) ^ 2) := by
    intro q x y
    have := iter_offdiag (μ := μ) hkb hk0 hk1 hL hβ
      (kT_le_of_lip hN0 hL hβ (fun A V V' => lip_tw hN0 q A V V')) (j - 1) x y
    rwa [hj'] at this
  set ε : ℝ := Real.exp (-β * c₁) with hε
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hdec : ∀ t : ℝ, κ / 4 ≤ t → Real.exp (-2 * β * (t / ((j : ℝ) * L)) ^ 2) ≤ ε := by
    intro t ht
    rw [hε, hc₁]
    have := exp_dec (β := β) hβ (s := (κ / 4) / ((j : ℝ) * L)) (t := t / ((j : ℝ) * L))
      (by positivity) (div_le_div_of_nonneg_right ht (by positivity))
    refine this.trans (le_of_eq ?_)
    ring_nf
  -- a charged word above `1/2` makes the twisted row small
  have twisted_small : ∀ (g : ZMod N × ZMod N) (q : Idx N) (x y : Cfg m N), charge q g ≠ 0 →
      1 / 2 < ‖tw q y‖ → a x y * a x (act g y) ≤ ε := by
    intro g q x y hq hy
    have hjump : κ / 2 ≤ ‖tw q y - tw q (act g y)‖ := by
      rw [tw_act, show tw q y - ee (charge q g) * tw q y = (1 - ee (charge q g)) * tw q y by ring,
        norm_mul]
      have := hκle _ hq
      nlinarith [norm_nonneg (1 - ee (charge q g))]
    have hsum : κ / 2 ≤ ‖tw q x - tw q y‖ + ‖tw q x - tw q (act g y)‖ := by
      have h1 : ‖tw q y - tw q (act g y)‖ ≤ ‖tw q x - tw q y‖ + ‖tw q x - tw q (act g y)‖ := by
        calc ‖tw q y - tw q (act g y)‖ = ‖(tw q x - tw q (act g y)) - (tw q x - tw q y)‖ := by
              ring_nf
          _ ≤ ‖tw q x - tw q (act g y)‖ + ‖tw q x - tw q y‖ := norm_sub_le _ _
          _ = _ := by ring
      linarith
    by_cases hxy : κ / 4 ≤ ‖tw q x - tw q y‖
    · have h1 := (offd q x y).trans (hdec _ hxy)
      calc a x y * a x (act g y) ≤ ε * 1 := mul_le_mul h1 (hbnd x (act g y)).2 (ha0 _ _) hε0
        _ = ε := mul_one ε
    · have hxσ : κ / 4 ≤ ‖tw q x - tw q (act g y)‖ := by push_neg at hxy; linarith
      have h1 := (offd q x (act g y)).trans (hdec _ hxσ)
      calc a x y * a x (act g y) ≤ 1 * ε := mul_le_mul (hbnd x y).2 h1 (ha0 _ _) zero_le_one
        _ = ε := one_mul ε
  -- the weights
  set S : ZMod N × ZMod N → Set (Cfg m N) := fun g =>
    {V | ∀ q : Idx N, charge q g ≠ 0 → ‖tw q V‖ ≤ 1 / 2} with hSdef
  have hSc : ∀ g, IsClosed (S g) := fun g => by
    simp only [hSdef, Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_le (continuous_norm.comp (continuous_tw q)) continuous_const
  have hχ : ∀ g, Measurable (chi (S g)) := fun g =>
    measurable_const.indicator (hSc g).measurableSet
  have hχb : ∀ g y, 0 ≤ chi (S g) y ∧ chi (S g) y ≤ 1 := by
    intro g y
    by_cases h : y ∈ S g
    · rw [chi_of_mem h]; norm_num
    · rw [chi_of_not_mem h]; norm_num
  have hmem : ∀ g h y, act h y ∈ S g ↔ y ∈ S g := by
    intro g h y
    simp only [hSdef, Set.mem_setOf_eq, norm_tw_act]
  have hχσ : ∀ g y, chi (S g) (act g y) = chi (S g) y := by
    intro g y
    by_cases h : y ∈ S g
    · rw [chi_of_mem h, chi_of_mem ((hmem g g y).mpr h)]
    · rw [chi_of_not_mem h, chi_of_not_mem (fun h' => h ((hmem g g y).mp h'))]
  have amgm : ∀ p r : ℝ, p * r ≤ (p ^ 2 + r ^ 2) / 2 := fun p r => by
    nlinarith [sq_nonneg (p - r)]
  have h1 : ∀ g x y, a x y * a x (act g y)
      ≤ ε + chi (S g) y * ((a x y ^ 2 + a x (act g y) ^ 2) / 2) := by
    intro g x y
    by_cases hy : y ∈ S g
    · rw [chi_of_mem hy, one_mul]
      linarith [amgm (a x y) (a x (act g y))]
    · rw [chi_of_not_mem hy, zero_mul, add_zero]
      simp only [hSdef, Set.mem_setOf_eq, not_forall, not_le] at hy
      obtain ⟨q, hq, hlt⟩ := hy
      exact twisted_small g q x y hq hlt
  set η : ℝ := Real.exp (-β * s₀) with hη
  have h3 : ∀ x y, (∑ g, chi (S g) y) * a x y ^ 2
      ≤ (Fintype.card (ZMod N × ZMod N) : ℝ) / 2 * a x y ^ 2
        + Fintype.card (ZMod N × ZMod N) * η := by
    intro x y
    have hη0 : 0 ≤ η := (Real.exp_pos _).le
    have ha2 : 0 ≤ a x y ^ 2 := sq_nonneg _
    have hsum0 : 0 ≤ ∑ g, chi (S g) y := Finset.sum_nonneg fun g _ => (hχb g y).1
    have hG0 : (0 : ℝ) ≤ Fintype.card (ZMod N × ZMod N) := Nat.cast_nonneg _
    by_cases hall : ∀ g, y ∈ S g
    · have hsmallTr : ∀ q : Idx N, Charged q → ‖tw q y‖ ≤ 1 / 2 := fun q hq => by
        obtain ⟨g, hg⟩ := exists_charge_ne hq
        exact hall g q hg
      have hsp := hfloor y hsmallTr
      have hay : a x y ≤ Real.exp (-β * spT 0 (Tn m) y / 2) :=
        iter_le_sp (μ := μ) hkb hk0 hk1 (f := fun y => Real.exp (-β * spT 0 (Tn m) y / 2))
          (kT_le_sp hN0 hβ) (j - 1) x y
      have hsq : a x y ^ 2 ≤ η := by
        have := pow_le_pow_left₀ (ha0 x y) hay 2
        refine this.trans ?_
        rw [← Real.exp_nat_mul, hη, Real.exp_le_exp]
        push_cast
        nlinarith
      have hsum : ∑ g, chi (S g) y ≤ Fintype.card (ZMod N × ZMod N) := by
        calc ∑ g, chi (S g) y ≤ ∑ _g : ZMod N × ZMod N, (1 : ℝ) :=
              Finset.sum_le_sum fun g _ => (hχb g y).2
          _ = Fintype.card (ZMod N × ZMod N) := by simp
      nlinarith [mul_le_mul hsum hsq ha2 hG0]
    · push_neg at hall
      obtain ⟨g₀, hg₀⟩ := hall
      have hite : ∀ g, chi (S g) y = if y ∈ S g then 1 else 0 := fun g => by
        unfold chi; rw [Set.indicator_apply]
      have hcount : ∑ g, chi (S g) y ≤ (Fintype.card (ZMod N × ZMod N) : ℝ) / 2 := by
        rw [Finset.sum_congr rfl fun g _ => hite g, Finset.sum_boole]
        set T := (Finset.univ : Finset (ZMod N × ZMod N)).filter (fun g => y ∈ S g)
        have hinj : T.card
            ≤ ((Finset.univ : Finset (ZMod N × ZMod N)).filter (fun g => ¬ y ∈ S g)).card := by
          refine Finset.card_le_card_of_injOn (fun h => h + g₀) ?_ ?_
          · intro h hh
            simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
            intro hmem'
            obtain ⟨q, hq0, hqt⟩ : ∃ q : Idx N, charge q g₀ ≠ 0 ∧ 1 / 2 < ‖tw q y‖ := by
              by_contra hc
              push_neg at hc
              exact hg₀ (fun q hq => hc q hq)
            have hqh : charge q h = 0 := by
              by_contra hne
              exact absurd (hh q hne) (not_le.mpr hqt)
            have hne : charge q (h + g₀) ≠ 0 := by rw [charge_add, hqh, zero_add]; exact hq0
            exact absurd (hmem' q hne) (not_le.mpr hqt)
          · intro h₁ _ h₂ _ he
            exact add_right_cancel he
        have hsplit : T.card
            + ((Finset.univ : Finset (ZMod N × ZMod N)).filter (fun g => ¬ y ∈ S g)).card
            = Fintype.card (ZMod N × ZMod N) := by
          rw [← Finset.card_univ]
          exact Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun g => y ∈ S g)
        have h2 : 2 * T.card ≤ Fintype.card (ZMod N × ZMod N) := by omega
        have h2R : (2 : ℝ) * T.card ≤ Fintype.card (ZMod N × ZMod N) := by exact_mod_cast h2
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hcount ha2]
  -- the trace is `ZR(n⁴)` and is not exponentially small
  have hZ1 : ZR (fun _ => m + 1) N β = hs μ a := by
    rw [ZR_eq_traceSeq (μ := 0) (L := fun _ => m + 1) (N := N) hN0 hβ j hj (by simp [hm])]
    unfold traceSeq
    congr 2
    show (m + 1) / 2 - 1 = j - 1
    omega
  have hsmall : ε + η ≤ hs μ a / 4 := by
    have hZ := hZl β hβ
    rw [hZ1] at hZ
    have e1 : ε ≤ Real.exp (-(β * κ')) * Real.exp (-(β * κ')) := by
      rw [← Real.exp_add, hε, Real.exp_le_exp]
      have : 2 * κ' ≤ c₁ := by rw [hκ']; linarith [min_le_left c₁ s₀]
      nlinarith
    have e2 : η ≤ Real.exp (-(β * κ')) * Real.exp (-(β * κ')) := by
      rw [← Real.exp_add, hη, Real.exp_le_exp]
      have : 2 * κ' ≤ s₀ := by rw [hκ']; linarith [min_le_right c₁ s₀]
      nlinarith
    have e3 : Real.exp (-β * κ') = Real.exp (-(β * κ')) := by ring_nf
    rw [e3] at hZ
    have hp := Real.exp_pos (-(β * κ'))
    nlinarith [mul_lt_mul_of_pos_left hβe hp]
  exact FluxSectorFourier.hs_conv_le_three_quarters hab ha0 hsym hA hinv hχ hχb hχσ h1 h3 hsmall

end Assembly

/-- **The defect on the torus of side `2j` exceeds `1/1000` at every large `β`**, for `N ≥ 2`. -/
theorem defect_gt {N : ℕ} (hN : 2 ≤ N) (j : ℕ) (hj : 1 ≤ j) :
    ∀ᶠ β in atTop, 1 / 1000 < ZoomSelfScale.defectW N β (2 * j) := by
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : N ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * j := ⟨2 * j - 1, by omega⟩
  filter_upwards [doubled_trace_le hN j m hj hm, eventually_ge_atTop (0 : ℝ)] with β hmain hβ
  set k := kT 0 (Tn m) N β
  set μ := hS 0 (Tn m) N
  have hkb : Bdd k := bdd_kT hN0 hβ
  set a := iter μ k (j - 1) with ha
  have hZ1 : ZR (fun _ => m + 1) N β = hs μ a := by
    rw [ZR_eq_traceSeq (μ := 0) (L := fun _ => m + 1) (N := N) hN0 hβ j hj (by simp [hm])]
    unfold traceSeq
    congr 2
    show (m + 1) / 2 - 1 = j - 1
    omega
  have hZpos : 0 < hs μ a := by rw [← hZ1]; exact DeltaLengthTower.ZR_pos hN0 _ β
  -- the doubled trace is `ZR(2n × n³)`
  set L₂ : Fin 4 → ℕ :=
    DoublingWilson.ext (m + 1) (DoublingRecursion.corner 0 + DoublingRecursion.E 0)
  have hL₂0 : L₂ 0 = 2 * (2 * j) := by
    show DoublingWilson.ext (m + 1) (DoublingRecursion.corner 0 + DoublingRecursion.E 0) 0 = _
    rw [DoublingWilson.ext_add_self]
    simp [DoublingWilson.ext, DoublingRecursion.corner, hm]
  have hT₂ : tr L₂ 0 = Tn m := by
    show tr (DoublingWilson.ext (m + 1) (DoublingRecursion.corner 0 + DoublingRecursion.E 0)) 0 = _
    rw [DoublingWilson.tr_ext_add]
    funext k
    simp [DoublingWilson.ext, DoublingRecursion.corner]
  have hZ2 : ZR L₂ N β = hs μ (conv μ a a) := by
    have := ZR_eq_traceSeq (μ := 0) (L := L₂) (N := N) hN0 hβ (2 * j) (by omega) hL₂0
    rw [hT₂, hL₂0] at this
    rw [this]
    unfold traceSeq
    have e : 2 * (2 * j) / 2 - 1 = (j - 1) + (j - 1) + 1 := by omega
    rw [e, iter_add hkb]
  have hZ2pos : 0 < ZR L₂ N β := DeltaLengthTower.ZR_pos hN0 _ β
  -- the one-direction defect
  have hn : 2 ≤ m + 1 := by omega
  have he : Even (m + 1) := ⟨j, by omega⟩
  have hpos := DoublingWilson.positive (N := N) hN0 hβ hn he
  have hpΔ := DoublingRecursion.p_le_Δ hpos (DoublingRecursion.corner 0)
  have hΔ : DoublingRecursion.Δ (DoublingWilson.xW N (m + 1) β) (DoublingRecursion.corner 0)
      = ZoomSelfScale.defectW N β (m + 1) := DoublingWilson.Δ_corner0 (m + 1)
  have hp : DoublingRecursion.p (DoublingWilson.xW N (m + 1) β) 0 (DoublingRecursion.corner 0)
      = 2 * Real.log (hs μ a) - Real.log (hs μ (conv μ a a)) := by
    unfold DoublingRecursion.p DoublingWilson.xW
    rw [← hZ2]
    have hc0 : DoublingWilson.ext (m + 1) (DoublingRecursion.corner 0) = fun _ => m + 1 := by
      funext i; simp [DoublingWilson.ext, DoublingRecursion.corner]
    rw [hc0, hZ1]
  have hlog : Real.log (hs μ (conv μ a a)) ≤ Real.log (3 / 4) + 2 * Real.log (hs μ a) := by
    rw [← hZ2] at hmain ⊢
    have := Real.log_le_log hZ2pos hmain
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hl : 1 / 4 ≤ -Real.log (3 / 4) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [show (4 / 3 : ℝ) = (3 / 4)⁻¹ by norm_num, Real.log_inv] at this
    norm_num at this ⊢
    linarith
  rw [show 2 * j = m + 1 by omega, ← hΔ]
  rw [hp] at hpΔ
  linarith

/-- **(B₂) for SU(N), every `N ≥ 2`.** For every `b ≥ 1`, frequently in `β`, `2ᵇ` is not a seed. -/
theorem deltaLengthUnbounded {N : ℕ} (hN : 2 ≤ N) : DeltaLengthTower.DeltaLengthUnbounded N := by
  intro b hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have h := defect_gt hN (2 ^ c) Nat.one_le_two_pow
  rw [show 2 * 2 ^ c = 2 ^ (c + 1) by ring] at h
  exact h.frequently

/-- **The gap half along the theory's own scale, for SU(N), from (A₂) alone.** With (B₂) proved,
`DeltaLengthTower.selfScaledGap` needs only `SeedExistsPow N`. -/
theorem selfScaledGap_of_seedExistsPow {N : ℕ} (hN : 2 ≤ N) (hN0 : N ≠ 0)
    (hA : DeltaLengthTower.SeedExistsPow N) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) :
    ∃ βs : ℕ → ℝ, Tendsto βs atTop atTop ∧ ∀ᶠ b in atTop,
      (∃ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 hN0 (βs b) r ∧
        Real.log 2 / ℓ₀ ≤ -Real.log r / (ℓ₀ / 2 ^ (b + 1)))
      ∧ 1 / 1000 < ZoomSelfScale.defectW N (βs b) (2 ^ b) :=
  DeltaLengthTower.selfScaledGap hN hN0 hA (deltaLengthUnbounded hN) hℓ

end MassGap.TwistedTraceBoundN

#print axioms MassGap.TwistedTraceBoundN.tw_act
#print axioms MassGap.TwistedTraceBoundN.comm_le
#print axioms MassGap.TwistedTraceBoundN.exists_sp_floor
#print axioms MassGap.TwistedTraceBoundN.lip_tw
#print axioms MassGap.TwistedTraceBoundN.doubled_trace_le
#print axioms MassGap.TwistedTraceBoundN.defect_gt
#print axioms MassGap.TwistedTraceBoundN.deltaLengthUnbounded
#print axioms MassGap.TwistedTraceBoundN.selfScaledGap_of_seedExistsPow
