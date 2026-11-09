import Mathlib
import MassGap.FreqRead

/-!
# MassGap.FloorModes — the aperture's own information: the occupied-mode count does not carry the floor

The question: a window holds finitely many modes; does the finiteness of the in-aperture information force a
lowest non-zero note independent of the window size? This module defines the read, computes it at the free
field in closed-form bounds, and records what it says about the lattice mass `mU β`
(`FinalBridge.MassReadOpens`). Declarations are in the namespace `MassGap.FloorModes`.

## 1. The read (defined)

`occ s w = exp(∑_{j∈s} −p_j log p_j)`, `p = w / ∑ w`: the entropy-effective number of occupied modes of the
spectrum `w` on the mode set `s` (the formula of `ApertureModes.spDim`, on a `Finset`; the `2^H` of
`entroptics.reads._fill_of`, in nats). It is a read of the normalised weights alone; nothing is chosen.

* `occ_smul`: the read ignores the normalisation of the weights.
* `occ_const`: `n` equal modes read `n`; `occ_le_card`: the read never exceeds the number of modes. At every
  finite window the count is finite, for every field.
* `occ_ge`: if every weight lies in `[lo, hi]`, `0 < lo`, the read is at least `card · lo / hi`
  (Shannon entropy is at least the min-entropy).

At the free field (`FreqRead`): the kept band of a periodic box of `L` cells of spacing `a` is
`keptSet L = {1, …, L−1}` and the spectral weight of mode `j` is the free power `FreqRead.power = 1/ω_j²`
(`FreqRead.energyMean_eq_flat`: equipartition). `occFree m a L = occ (keptSet L) (power m a L)`. The window
opens as `L → ∞` at fixed spacing and mass: the window `2^w` of `FinalBridge.apertureRead` at fixed `β`.

## 2. The free-field dichotomy (proved)

* `massive_occ_ge`: for `m ≠ 0`, `(L − 1) · m²/(m² + (2/a)²) ≤ occFree m a L ≤ L − 1`. The massive count is
  extensive: it grows linearly with the window.
* `massless_occ_bounded`: for `a ≠ 0`, `∃ C, ∀ L ≥ 2, occFree 0 a L ≤ C`. The massless count is bounded as the
  window opens. Proof: `p_j ≤ (π²/2)(1/j² + 1/(L−j)²)` (`massless_ratio`, from Jordan's inequality
  `jordan` and `sin x ≤ x`); Gibbs' inequality against the reference `(1/j² + 1/(L−j)²)/2`
  (`negMulLog_le_cross`); the entropy of `1/n²` is summable (`summable_negMulLog_invSq`).
* `occFree_bounded_iff`: for `a ≠ 0`, the count stays bounded as the window opens exactly when `m = 0`.
* `occFree_magnify`: the massless count does not depend on the spacing: opening the window by magnifying the
  cells (`A → ∞` at fixed `L`) leaves it fixed.

So the dichotomy runs the other way from the one suggested: in one dimension a bounded count is the massless,
scale-invariant signature (`p_j ∝ 1/j²` converges to a fixed distribution); a mass shows as an extensive count,
`∝ (m A)` for `m A` large, the number of modes under the mass shell.

## 3. The physical dimension (proved, and argued)

On the `d`-dimensional periodic box (`keptD d L`, the non-zero momenta of `(Fin L)^d`; weights
`1/p̂²(k)`, `phat2d`):

* `massless_occD_ge`: for `d ≥ 1`, `a ≠ 0`, `L ≥ 2`, `(L^d − 1)(2/L)²/d ≤ occ`.
* `massless_occD_unbounded`: for `d ≥ 3` the massless count is unbounded as the window opens.

So in the dimension of the tree (`d = 4`) the massless free count also grows without bound. Argued, not proved
here: for `d ≥ 3`, `1/p̂²` is integrable on the Brillouin zone, the normalised weights converge to a density
`ρ_m` on the zone, and the count is `≈ L^d exp(h(ρ_m))` with `h` the differential entropy, finite and
continuous in `m` at `m = 0`. The count is then extensive at `m = 0` and at `m > 0` alike, with a coefficient
that does not jump at `m = 0`. Argued: neither boundedness nor the growth law of the count separates the massive from
the massless field in four dimensions.

## 4. The interacting statement, and whether it gives `mU > 0` (proved where stated, otherwise argued)

The candidate statements the free computation suggests, at fixed `β`, with the interacting weights the Gram
eigenvalues of a screen (`ApertureModes.effDim`):

* (a) "the occupied-mode count stays bounded as the window opens": false at the massive free field in one
  dimension (`massive_occ_ge`, proved); the same weights-in-an-interval argument applies in `d` dimensions
  (argued, not formalised here), so it cannot be a criterion for a mass. Plainly, it does not imply `mU > 0`.
* (b) "the count is extensive" (grows with the window): implies a mass at the one-dimensional free field
  (`occFree_bounded_iff`) but not in `d ≥ 3` (`massless_occD_unbounded`).
* In general the count reads only the weights; the floor is a statement about the rates. `count_blind_to_rates`
  (counterexample choice: unit weights, massless dispersion): the count is `L − 1`, extensive, while the
  slowest full-box rate is `ω₀ = 0`. A profile `∑ w_j e^{−r_j τ}` (`FreqRead.profile`) has its rates and
  weights as independent coordinates; the link between them is the free propagator (`w = 1/ω²`), and in the
  interacting theory that link is the Källén–Lehmann spectral measure itself, whose bottom is the mass
  (`BandShell.SpecBottom`).

The compact gauge group supplies a floor at each finite window: the transfer matrix of a finite Wilson box is a
positive compact operator on `L²` of a compact group product, and its gap above the vacuum is positive at each
finite box (Perron–Frobenius, standard, not formalised here; at one link it is the Casimir gap of the heat kernel on `SU(N)`). That floor is
finite-window information too, and what the question needs is its uniformity as the window opens. The
occupied-mode count does not carry that uniformity: it is bounded in the massless one-dimensional case and
unbounded for the massless field in `d ≥ 3` (`massless_occD_unbounded`, proved) and, by the same argument, for
the massive field (argued, not formalised here). Plainly, no statement about the count alone implies `mU β > 0`.

## 5. Verdict (plainly)

Finiteness of the in-aperture information does not force a floor: it holds for the free massless field at every
window. Boundedness of the count as the window opens signals the absence of a mass in one dimension, and is
absent for the massless field in `d ≥ 3` (proved) and for the massive field (argued). The extra content a floor needs is a
uniform lower bound on the rates, which is `FinalBridge.MassReadOpens` itself (`FinalBridge.readOpens_iff`),
and turning a count statement into it needs the weight–rate link, which in the interacting theory is the
spectral measure whose bottom is `mU`. This route is the same problem as mass positivity, not an easier one.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the zero mass, the zero mode and the empty set; `1` the first kept mode,
the one-mode read and the base of `log`; `2` the `2/a` of the lattice dispersion and the least box with a kept mode,
the square in `1/j²` and the halving of the Gibbs reference (`u ≤ 2`); `π²/2` from `(π/2)²` (Jordan's `2/π`
through `Real.mul_le_sin`, and `sin x ≤ x`) times the `2` of `(u+v)² ≤ 2(u²+v²)`; `4` the square of `2/L` and `2 · 2` in `log n ≤ 2√n`; `3` the least
dimension where `1/p̂²` is integrable at the origin. Proof device: the exponent `3/2` in the summability of
`log n / n²` (any exponent strictly between `1` and `2` gives the same existence statement). Counterexample
choice: unit weights in `count_blind_to_rates`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FloorModes

open Real Filter Topology Finset
open MassGap.FreqRead (phat2 omega2 omega power keptSet)

/-! ## 1. The read -/

section Read

variable {ι : Type*}

/-- **The occupied-mode count of a spectrum**: `exp(−∑ pⱼ log pⱼ)`, `p = w / ∑ w`. DERIVED: no numeral. -/
def occ (s : Finset ι) (w : ι → ℝ) : ℝ :=
  Real.exp (∑ j ∈ s, Real.negMulLog (w j / ∑ i ∈ s, w i))

/-- DERIVED: `0` the sign. -/
theorem occ_pos (s : Finset ι) (w : ι → ℝ) : 0 < occ s w := Real.exp_pos _

/-- **The read ignores the normalisation.** DERIVED: `0` the excluded scale. -/
theorem occ_smul (s : Finset ι) (w : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    occ s (fun j => c * w j) = occ s w := by
  unfold occ
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- DERIVED: `1` the total probability; `0` the excluded total. -/
theorem sum_norm {s : Finset ι} {w : ι → ℝ} (hS : ∑ i ∈ s, w i ≠ 0) :
    ∑ j ∈ s, w j / ∑ i ∈ s, w i = 1 := by
  rw [← Finset.sum_div, div_self hS]

/-- **Gibbs, one term**: `−p log p ≤ p log(1/q) + q − p` (`log x ≤ x − 1`). DERIVED: `0` the signs; `1` the
base of `log`. -/
theorem negMulLog_le_cross {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.negMulLog p ≤ p * Real.log (1 / q) + q - p := by
  have h := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at h
  have h2 : p * (Real.log q - Real.log p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h hp.le
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hp.ne', mul_one] at h2
  rw [one_div, Real.log_inv]
  show -p * Real.log p ≤ p * -Real.log q + q - p
  linarith

/-- **Gibbs' inequality**: `H(p) ≤ ∑ p log(1/q) + ∑ q − ∑ p`. DERIVED: `0` the signs. -/
theorem gibbs {s : Finset ι} {p q : ι → ℝ} (hp : ∀ j ∈ s, 0 < p j) (hq : ∀ j ∈ s, 0 < q j) :
    ∑ j ∈ s, Real.negMulLog (p j) ≤
      ∑ j ∈ s, p j * Real.log (1 / q j) + ∑ j ∈ s, q j - ∑ j ∈ s, p j := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun j hj => negMulLog_le_cross (hp j hj) (hq j hj)

/-- **Shannon is at least min-entropy**: if every `pⱼ ≤ P`, `(∑ p) log(1/P) ≤ H(p)`. DERIVED: `0` the signs;
`1` the base of `log`. -/
theorem log_inv_le_entropy {s : Finset ι} {p : ι → ℝ} {P : ℝ} (hp : ∀ j ∈ s, 0 < p j)
    (hP : ∀ j ∈ s, p j ≤ P) : (∑ j ∈ s, p j) * Real.log (1 / P) ≤ ∑ j ∈ s, Real.negMulLog (p j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have h0 := hp j hj
  have h1 : Real.log (1 / P) ≤ Real.log (1 / p j) :=
    Real.log_le_log (one_div_pos.mpr (h0.trans_le (hP j hj))) (one_div_le_one_div_of_le h0 (hP j hj))
  have h2 := mul_le_mul_of_nonneg_left h1 h0.le
  rw [one_div (p j), Real.log_inv] at h2
  show p j * Real.log (1 / P) ≤ -p j * Real.log (p j)
  linarith

/-- **`n` equal modes read `n`.** DERIVED: no numeral. -/
theorem occ_const {s : Finset ι} (hne : s.Nonempty) {c : ℝ} (hc : 0 < c) :
    occ s (fun _ => c) = s.card := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  unfold occ
  simp only [Finset.sum_const, nsmul_eq_mul]
  have e1 : c / ((s.card : ℝ) * c) = (s.card : ℝ)⁻¹ := by
    field_simp
  have e2 : (s.card : ℝ) * Real.negMulLog (s.card : ℝ)⁻¹ = Real.log s.card := by
    rw [Real.negMulLog, Real.log_inv]
    field_simp
  rw [e1, e2, Real.exp_log hn]

/-- **The count never exceeds the number of modes** (Gibbs against the flat reference). DERIVED: `0` the
signs; `1` the total probability. -/
theorem occ_le_card {s : Finset ι} {w : ι → ℝ} (hw : ∀ j ∈ s, 0 < w j) (hne : s.Nonempty) :
    occ s w ≤ s.card := by
  have hS : 0 < ∑ i ∈ s, w i := Finset.sum_pos hw hne
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  have hp : ∀ j ∈ s, 0 < w j / ∑ i ∈ s, w i := fun j hj => div_pos (hw j hj) hS
  have hG := gibbs hp (fun j _ => (inv_pos.mpr hn : (0 : ℝ) < (s.card : ℝ)⁻¹))
  have e1 : ∑ j ∈ s, w j / (∑ i ∈ s, w i) * Real.log (1 / (s.card : ℝ)⁻¹) = Real.log s.card := by
    rw [← Finset.sum_mul, sum_norm hS.ne', one_mul, one_div, inv_inv]
  have e2 : ∑ _j ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn.ne']
  rw [e1, e2, sum_norm hS.ne'] at hG
  unfold occ
  calc _ ≤ Real.exp (Real.log s.card + 1 - 1) := Real.exp_le_exp.mpr hG
    _ = s.card := by rw [add_sub_cancel_right, Real.exp_log hn]

/-- **Weights in `[lo, hi]` read at least `card · lo / hi`.** DERIVED: `0` the signs. -/
theorem occ_ge {s : Finset ι} {w : ι → ℝ} {lo hi : ℝ} (hlo : 0 < lo)
    (hw : ∀ j ∈ s, lo ≤ w j ∧ w j ≤ hi) (hne : s.Nonempty) : (s.card : ℝ) * lo / hi ≤ occ s w := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ i ∈ s, w i := ⟨_, rfl⟩
  have hwpos : ∀ j ∈ s, 0 < w j := fun j hj => hlo.trans_le (hw j hj).1
  have hhi : 0 < hi := by
    obtain ⟨j, hj⟩ := hne
    exact (hwpos j hj).trans_le (hw j hj).2
  have hS : 0 < S := hSdef ▸ Finset.sum_pos hwpos hne
  have hSlo : (s.card : ℝ) * lo ≤ S := by
    have := Finset.card_nsmul_le_sum s w lo (fun j hj => (hw j hj).1)
    rw [hSdef]
    simpa [nsmul_eq_mul] using this
  have hp : ∀ j ∈ s, 0 < w j / S := fun j hj => div_pos (hwpos j hj) hS
  have hP : ∀ j ∈ s, w j / S ≤ hi / S := fun j hj => div_le_div_of_nonneg_right (hw j hj).2 hS.le
  have hE := log_inv_le_entropy hp hP
  have h1 : ∑ j ∈ s, w j / S = 1 := by rw [hSdef]; exact sum_norm (hSdef ▸ hS.ne')
  rw [h1, one_mul, one_div_div] at hE
  unfold occ
  rw [← hSdef]
  calc (s.card : ℝ) * lo / hi ≤ S / hi := div_le_div_of_nonneg_right hSlo hhi.le
    _ = Real.exp (Real.log (S / hi)) := (Real.exp_log (div_pos hS hhi)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hE

end Read

/-! ## 2. The free field in one dimension -/

section Free

/-- **The free count**: the read of the kept band of the free power `1/ω²`. DERIVED: no numeral. -/
def occFree (m a : ℝ) (L : ℕ) : ℝ := occ (keptSet L) (power m a L)

/-- DERIVED: `0`, `1`, `2` the membership `1 ≤ j < L`. -/
theorem mem_kept {L j : ℕ} : j ∈ keptSet L ↔ j ≠ 0 ∧ j < L := by
  simp [keptSet, Finset.mem_erase, Finset.mem_range]

/-- DERIVED: `1`, `2` the least box with a kept mode. -/
theorem kept_nonempty {L : ℕ} (hL : 2 ≤ L) : (keptSet L).Nonempty :=
  ⟨1, mem_kept.mpr ⟨one_ne_zero, by omega⟩⟩

/-- **The lattice dispersion is at most `(2/a)²`**. DERIVED: `2` the lattice dispersion; `1` the bound
`sin² ≤ 1`. -/
theorem phat2_le (a : ℝ) (L j : ℕ) : phat2 a L j ≤ (2 / a) ^ 2 := by
  unfold phat2
  have h := Real.sin_sq_add_cos_sq (π * j / L)
  have hc := sq_nonneg (Real.cos (π * j / L))
  have hs : Real.sin (π * j / L) ^ 2 ≤ 1 := by linarith
  exact mul_le_of_le_one_right (sq_nonneg _) hs

/-- **The massive count is extensive**: `(L − 1) m²/(m² + (2/a)²) ≤ occFree m a L ≤ L − 1`.
DERIVED: `2` the lattice dispersion and the least box; `1` the zero mode removed. -/
theorem massive_occ_ge {m : ℝ} (hm : m ≠ 0) (a : ℝ) {L : ℕ} (hL : 2 ≤ L) :
    ((L : ℝ) - 1) * (m ^ 2 / (m ^ 2 + (2 / a) ^ 2)) ≤ occFree m a L ∧ occFree m a L ≤ (L : ℝ) - 1 := by
  have hm2 : 0 < m ^ 2 := by positivity
  have hc : 0 ≤ (2 / a) ^ 2 := sq_nonneg _
  have hw : ∀ j ∈ keptSet L, (m ^ 2 + (2 / a) ^ 2)⁻¹ ≤ power m a L j ∧ power m a L j ≤ (m ^ 2)⁻¹ := by
    intro j _
    have h0 := FreqRead.phat2_nonneg a L j
    have h1 := phat2_le a L j
    refine ⟨inv_anti₀ (show (0 : ℝ) < m ^ 2 + phat2 a L j by linarith) ?_, inv_anti₀ hm2 ?_⟩
    · show m ^ 2 + phat2 a L j ≤ m ^ 2 + (2 / a) ^ 2
      linarith
    · show m ^ 2 ≤ m ^ 2 + phat2 a L j
      linarith
  have h := occ_ge (by positivity) hw (kept_nonempty hL)
  have hpos : ∀ j ∈ keptSet L, 0 < power m a L j := fun j hj =>
    (inv_pos.mpr (by positivity : (0 : ℝ) < m ^ 2 + (2 / a) ^ 2)).trans_le (hw j hj).1
  have hup := occ_le_card hpos (kept_nonempty hL)
  rw [FreqRead.card_keptSet (by omega)] at h hup
  have e : ((L : ℝ) - 1) * (m ^ 2 / (m ^ 2 + (2 / a) ^ 2)) =
      ((L : ℝ) - 1) * (m ^ 2 + (2 / a) ^ 2)⁻¹ / (m ^ 2)⁻¹ := by
    rw [div_inv_eq_mul]; ring
  refine ⟨?_, hup⟩
  rw [e]
  exact h

/-- **The massive count is unbounded as the window opens.** DERIVED: `1`, `2` the shift `L = n + 2`. -/
theorem massive_occ_unbounded {m : ℝ} (hm : m ≠ 0) (a : ℝ) :
    ¬ ∃ C : ℝ, ∀ L : ℕ, 2 ≤ L → occFree m a L ≤ C := by
  rintro ⟨C, hC⟩
  have hm2 : 0 < m ^ 2 := by positivity
  have hr : 0 < m ^ 2 / (m ^ 2 + (2 / a) ^ 2) := div_pos hm2 (add_pos_of_pos_of_nonneg hm2 (sq_nonneg _))
  obtain ⟨n, h3⟩ : ∃ n : ℕ, C / (m ^ 2 / (m ^ 2 + (2 / a) ^ 2)) ≤ n := ⟨_, Nat.le_ceil _⟩
  have h1 := (massive_occ_ge hm a (L := n + 2) (by omega)).1
  have h2 := hC (n + 2) (by omega)
  have h4 : ((n + 2 : ℕ) : ℝ) - 1 = n + 1 := by push_cast; ring
  rw [h4] at h1
  have h5 : C < (n + 1) * (m ^ 2 / (m ^ 2 + (2 / a) ^ 2)) := by
    rw [div_le_iff₀ hr] at h3
    nlinarith
  linarith

/-! ### The massless count -/

/-- **`1/n²`**, with `1/0² = 0`. DERIVED: `2` the square. -/
def invSq (n : ℕ) : ℝ := ((n : ℝ) ^ 2)⁻¹

/-- DERIVED: `0` the sign. -/
theorem invSq_nonneg (n : ℕ) : 0 ≤ invSq n := by unfold invSq; positivity

/-- DERIVED: `2` the square; `1` the exponent above one. -/
theorem summable_invSq : Summable invSq :=
  Real.summable_nat_pow_inv.mpr (by norm_num)

/-- DERIVED: `3/2` proof device; `1` the split `3/2 = 1 + 1/2`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rcases hx.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by norm_num), zero_mul]
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one, Real.sqrt_eq_rpow]

/-- **The entropy of `1/n²` is summable.** DERIVED: `4 = 2 · 2` from `log n ≤ 2√n`; `3/2` proof device. -/
theorem summable_negMulLog_invSq : Summable fun n => Real.negMulLog (invSq n) := by
  have hb : Summable fun n : ℕ => 4 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
    have := Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 3 / 2 by norm_num)
    refine (this.congr fun n => ?_).mul_left 4
    rw [rpow_three_halves (Nat.cast_nonneg n)]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hb
  · refine Real.negMulLog_nonneg (invSq_nonneg n) ?_
    unfold invSq
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast h)
      exact inv_le_one_of_one_le₀ this
  · rcases Nat.eq_zero_or_pos n with h | hn
    · subst h; simp [invSq]
    · have hx : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx
      have hlog : Real.log n ≤ 2 * √(n : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos hs
        rw [Real.log_sqrt hx.le] at h1
        linarith
      have e : Real.negMulLog (invSq n) = ((n : ℝ) ^ 2)⁻¹ * (2 * Real.log n) := by
        simp only [invSq, Real.negMulLog, Real.log_inv, Real.log_pow]
        push_cast
        ring
      rw [e]
      have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hx.le
      calc ((n : ℝ) ^ 2)⁻¹ * (2 * Real.log n) ≤ ((n : ℝ) ^ 2)⁻¹ * (2 * (2 * √(n : ℝ))) := by
            have : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
            nlinarith
        _ = 4 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
            rw [show (n : ℝ) ^ 2 = ((n : ℝ) * √(n : ℝ)) * √(n : ℝ) by rw [mul_assoc, hss]; ring]
            field_simp
            ring

/-- DERIVED: `0` the sign. -/
theorem sum_kept_le_tsum {φ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ φ n) (hs : Summable φ) (L : ℕ) :
    ∑ j ∈ keptSet L, φ j ≤ ∑' n, φ n :=
  hs.sum_le_tsum _ (fun n _ => h0 n)

/-- **The reflected kept band**. DERIVED: `0` the sign. -/
theorem sum_kept_reflect_le_tsum {φ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ φ n) (hs : Summable φ) (L : ℕ) :
    ∑ j ∈ keptSet L, φ (L - j) ≤ ∑' n, φ n := by
  rw [← Finset.sum_image (f := φ) (g := fun j => L - j)]
  · exact hs.sum_le_tsum _ (fun n _ => h0 n)
  · intro x hx y hy hxy
    have hxy' : L - x = L - y := hxy
    have hx' := mem_kept.mp (Finset.mem_coe.mp hx)
    have hy' := mem_kept.mp (Finset.mem_coe.mp hy)
    omega

/-- **Jordan on the folded box**: `2y z / L² ≤ sin(π y/L)` for `0 ≤ y`, `2y ≤ L`, `0 ≤ z ≤ L`.
DERIVED: `2/π` Jordan's constant (`Real.mul_le_sin`); `2` the half box. -/
theorem jordan_aux {L y z : ℝ} (hL : 0 < L) (hy : 0 ≤ y) (h2y : 2 * y ≤ L) (hz : z ≤ L) :
    2 * z * y / L ^ 2 ≤ Real.sin (π * y / L) := by
  have hπ := pi_pos
  have h1 : π * y / L ≤ π / 2 := by
    rw [div_le_div_iff₀ hL two_pos]
    nlinarith
  have h0 : 0 ≤ π * y / L := by positivity
  calc 2 * z * y / L ^ 2 ≤ 2 * y / L := by
        rw [div_le_div_iff₀ (by positivity) hL]
        nlinarith [mul_nonneg (mul_nonneg hy hL.le) (sub_nonneg.mpr hz)]
    _ = 2 / π * (π * y / L) := by field_simp
    _ ≤ _ := Real.mul_le_sin h0 h1

/-- **Jordan on the kept band**: `2 j (L − j) / L² ≤ sin(π j / L)`. DERIVED: `2` the half box. -/
theorem jordan {L j : ℕ} (hj : j ∈ keptSet L) :
    2 * (j : ℝ) * ((L : ℝ) - j) / (L : ℝ) ^ 2 ≤ Real.sin (π * j / L) := by
  obtain ⟨hj0, hjL⟩ := mem_kept.mp hj
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hjr : (j : ℝ) < L := by exact_mod_cast hjL
  have hj0r : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases le_or_gt (2 * (j : ℝ)) L with h | h
  · have := jordan_aux hLr hj0r h (show (L : ℝ) - j ≤ L by linarith)
    calc 2 * (j : ℝ) * ((L : ℝ) - j) / (L : ℝ) ^ 2 = 2 * ((L : ℝ) - j) * j / (L : ℝ) ^ 2 := by ring
      _ ≤ _ := this
  · have := jordan_aux hLr (show (0 : ℝ) ≤ L - j by linarith) (by linarith) (show (j : ℝ) ≤ L by linarith)
    have e : Real.sin (π * ((L : ℝ) - j) / L) = Real.sin (π * j / L) := by
      rw [← Real.sin_pi_sub]
      congr 1
      field_simp
      ring
    rw [e] at this
    exact this

/-- DERIVED: `0` the zero mass. -/
theorem power_zero (a : ℝ) (L j : ℕ) : power 0 a L j = (phat2 a L j)⁻¹ := by
  simp [power, omega2]

/-- **The massless weights are dominated by the folded `1/j²`**:
`pⱼ ≤ (π²/2)(1/j² + 1/(L−j)²)`. DERIVED: `π²/2` from `(π/2)²` (Jordan's `2/π` through `Real.mul_le_sin`, and `sin x ≤ x`) times the `2` of
`(u+v)² ≤ 2(u²+v²)`; `2` the least box. -/
theorem massless_ratio {a : ℝ} (ha : a ≠ 0) {L j : ℕ} (hL : 2 ≤ L) (hj : j ∈ keptSet L) :
    power 0 a L j / ∑ i ∈ keptSet L, power 0 a L i ≤ π ^ 2 / 2 * (invSq j + invSq (L - j)) := by
  obtain ⟨hj0, hjL⟩ := mem_kept.mp hj
  have h1m : 1 ∈ keptSet L := mem_kept.mpr ⟨one_ne_zero, by omega⟩
  have hpos : ∀ i ∈ keptSet L, 0 < power 0 a L i := fun i hi =>
    inv_pos.mpr (FreqRead.omega2_kept_pos ha hL hi)
  have hS : power 0 a L 1 ≤ ∑ i ∈ keptSet L, power 0 a L i :=
    Finset.single_le_sum (fun i hi => (hpos i hi).le) h1m
  have step1 := div_le_div_of_nonneg_left (hpos j hj).le (hpos 1 h1m) hS
  have e1 : power 0 a L j / power 0 a L 1 = phat2 a L 1 / phat2 a L j := by
    rw [power_zero, power_zero, inv_div_inv]
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set J : ℝ := (j : ℝ) with hJdef
  set K : ℝ := (L : ℝ) - j with hKdef
  have hJ : 1 ≤ J := by rw [hJdef]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj0)
  have hK : 1 ≤ K := by
    have : (j : ℝ) + 1 ≤ L := by exact_mod_cast hjL
    rw [hKdef]; linarith
  have hLJK : (L : ℝ) = J + K := by rw [hJdef, hKdef]; ring
  have hc : 0 < (2 / a) ^ 2 := by positivity
  have hs1 : Real.sin (π * ((1 : ℕ) : ℝ) / L) ≤ π / L := by
    rw [Nat.cast_one, mul_one]; exact Real.sin_le (by positivity)
  have hs1' : 0 ≤ Real.sin (π * ((1 : ℕ) : ℝ) / L) := by
    rw [Nat.cast_one]; exact FreqRead.sin_fund_nonneg (by omega)
  have ht := jordan hj
  have htpos : 0 < 2 * J * K / (L : ℝ) ^ 2 := by positivity
  have hnum : phat2 a L 1 ≤ (2 / a) ^ 2 * (π / L) ^ 2 := by
    unfold phat2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs1' hs1 2) hc.le
  have hden : (2 / a) ^ 2 * (2 * J * K / (L : ℝ) ^ 2) ^ 2 ≤ phat2 a L j := by
    unfold phat2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le ht 2) hc.le
  have step2 : phat2 a L 1 / phat2 a L j ≤
      ((2 / a) ^ 2 * (π / L) ^ 2) / ((2 / a) ^ 2 * (2 * J * K / (L : ℝ) ^ 2) ^ 2) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  rw [mul_div_mul_left _ _ hc.ne'] at step2
  have hJ0 : J ≠ 0 := by linarith
  have hK0 : K ≠ 0 := by linarith
  have e2 : (π / L) ^ 2 / (2 * J * K / (L : ℝ) ^ 2) ^ 2 = π ^ 2 / 4 * (J⁻¹ + K⁻¹) ^ 2 := by
    rw [hLJK]
    field_simp
    ring
  have e3 : invSq j + invSq (L - j) = (J ^ 2)⁻¹ + (K ^ 2)⁻¹ := by
    simp only [invSq, Nat.cast_sub hjL.le, hJdef, hKdef]
  have h4 : (J⁻¹ + K⁻¹) ^ 2 ≤ 2 * ((J ^ 2)⁻¹ + (K ^ 2)⁻¹) := by
    rw [← inv_pow, ← inv_pow]
    nlinarith [sq_nonneg (J⁻¹ - K⁻¹)]
  rw [e3]
  calc power 0 a L j / ∑ i ∈ keptSet L, power 0 a L i ≤ power 0 a L j / power 0 a L 1 := step1
    _ = phat2 a L 1 / phat2 a L j := e1
    _ ≤ (π / L) ^ 2 / (2 * J * K / (L : ℝ) ^ 2) ^ 2 := step2
    _ = π ^ 2 / 4 * (J⁻¹ + K⁻¹) ^ 2 := e2
    _ ≤ π ^ 2 / 4 * (2 * ((J ^ 2)⁻¹ + (K ^ 2)⁻¹)) := by
        have : 0 ≤ π ^ 2 / 4 := by positivity
        exact mul_le_mul_of_nonneg_left h4 this
    _ = π ^ 2 / 2 * ((J ^ 2)⁻¹ + (K ^ 2)⁻¹) := by ring

/-- **`−(a+b) log(a+b) ≤ −a log a − b log b`** for `a, b > 0`. DERIVED: `0` the signs. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  have h1 : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx (by linarith)
  have h2 : Real.log y ≤ Real.log (x + y) := Real.log_le_log hy (by linarith)
  show -(x + y) * Real.log (x + y) ≤ -x * Real.log x + -y * Real.log y
  nlinarith [mul_le_mul_of_nonneg_left h1 hx.le, mul_le_mul_of_nonneg_left h2 hy.le]

/-- **One term of the massless bound**: with `p ≤ K₀ u`, `0 < u ≤ 2`, Gibbs against `u/2` gives
`−p log p ≤ K₀ (−u log u) + (2K₀ · (−½ log ½) + ½) u`. DERIVED: `2` the halving of the reference. -/
theorem massless_term {p u K₀ : ℝ} (hp : 0 < p) (hu : 0 < u) (hu2 : u ≤ 2) (hpu : p ≤ K₀ * u) :
    Real.negMulLog p ≤ K₀ * Real.negMulLog u + (2 * K₀ * Real.negMulLog (1 / 2) + 1 / 2) * u := by
  have hq : 0 < u / 2 := by positivity
  have h1 := negMulLog_le_cross hp hq
  have hl : 0 ≤ Real.log (1 / (u / 2)) := Real.log_nonneg (one_le_one_div hq (by linarith))
  have h2 : p * Real.log (1 / (u / 2)) ≤ K₀ * u * Real.log (1 / (u / 2)) :=
    mul_le_mul_of_nonneg_right hpu hl
  have h3 : K₀ * u * Real.log (1 / (u / 2)) =
      K₀ * Real.negMulLog u + 2 * K₀ * Real.negMulLog (1 / 2) * u := by
    rw [one_div_div, Real.log_div two_ne_zero hu.ne']
    simp only [Real.negMulLog]
    rw [one_div, Real.log_inv]
    ring
  linarith

/-- **The massless count is bounded as the window opens.** DERIVED: `π²/2` the Jordan constant; `2` the least
box and the halving of the reference; `1` the probability total. -/
theorem massless_occ_bounded {a : ℝ} (ha : a ≠ 0) :
    ∃ C : ℝ, ∀ L : ℕ, 2 ≤ L → occFree 0 a L ≤ C := by
  have hK₀ : 0 ≤ π ^ 2 / 2 := by positivity
  have hc : 0 ≤ 2 * (π ^ 2 / 2) * Real.negMulLog (1 / 2) + 1 / 2 := by
    have : 0 ≤ Real.negMulLog (1 / 2) := Real.negMulLog_nonneg (by norm_num) (by norm_num)
    exact add_nonneg (mul_nonneg (by positivity) this) (by norm_num)
  refine ⟨Real.exp (π ^ 2 / 2 * (2 * ∑' n, Real.negMulLog (invSq n)) +
    (2 * (π ^ 2 / 2) * Real.negMulLog (1 / 2) + 1 / 2) * (2 * ∑' n, invSq n)), fun L hL => ?_⟩
  have hpos : ∀ i ∈ keptSet L, 0 < power 0 a L i := fun i hi =>
    inv_pos.mpr (FreqRead.omega2_kept_pos ha hL hi)
  have hS : 0 < ∑ i ∈ keptSet L, power 0 a L i := Finset.sum_pos hpos (kept_nonempty hL)
  have hg0 : ∀ n, 0 ≤ Real.negMulLog (invSq n) := fun n => by
    refine Real.negMulLog_nonneg (invSq_nonneg n) ?_
    unfold invSq
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast h))
  have hterm : ∀ j ∈ keptSet L,
      Real.negMulLog (power 0 a L j / ∑ i ∈ keptSet L, power 0 a L i) ≤
        π ^ 2 / 2 * (Real.negMulLog (invSq j) + Real.negMulLog (invSq (L - j))) +
          (2 * (π ^ 2 / 2) * Real.negMulLog (1 / 2) + 1 / 2) * (invSq j + invSq (L - j)) := by
    intro j hj
    obtain ⟨hj0, hjL⟩ := mem_kept.mp hj
    have hfj : 0 < invSq j :=
      inv_pos.mpr (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hj0) 2)
    have hfk : 0 < invSq (L - j) :=
      inv_pos.mpr (pow_pos (by exact_mod_cast (show 0 < L - j by omega)) 2)
    have hfj1 : invSq j ≤ 1 := by
      unfold invSq; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0))
    have hfk1 : invSq (L - j) ≤ 1 := by
      unfold invSq; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ L - j by omega)))
    have hp : 0 < power 0 a L j / ∑ i ∈ keptSet L, power 0 a L i := div_pos (hpos j hj) hS
    have ht := massless_term hp (add_pos hfj hfk) (by linarith) (massless_ratio ha hL hj)
    have hsub := negMulLog_add_le hfj hfk
    have : π ^ 2 / 2 * Real.negMulLog (invSq j + invSq (L - j)) ≤
        π ^ 2 / 2 * (Real.negMulLog (invSq j) + Real.negMulLog (invSq (L - j))) :=
      mul_le_mul_of_nonneg_left hsub hK₀
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at hsum
  have b1 := sum_kept_le_tsum hg0 summable_negMulLog_invSq L
  have b2 := sum_kept_reflect_le_tsum hg0 summable_negMulLog_invSq L
  have b3 := sum_kept_le_tsum invSq_nonneg summable_invSq L
  have b4 := sum_kept_reflect_le_tsum invSq_nonneg summable_invSq L
  have hH : ∑ j ∈ keptSet L, Real.negMulLog (power 0 a L j / ∑ i ∈ keptSet L, power 0 a L i) ≤
      π ^ 2 / 2 * (2 * ∑' n, Real.negMulLog (invSq n)) +
        (2 * (π ^ 2 / 2) * Real.negMulLog (1 / 2) + 1 / 2) * (2 * ∑' n, invSq n) := by
    have i1 := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hK₀
    have i2 := mul_le_mul_of_nonneg_left (add_le_add b3 b4) hc
    linarith
  exact Real.exp_le_exp.mpr hH

/-- **The free dichotomy**: the count stays bounded as the window opens exactly when the field is massless.
DERIVED: `0` the zero mass; `2` the least box. -/
theorem occFree_bounded_iff {a : ℝ} (ha : a ≠ 0) (m : ℝ) :
    (∃ C : ℝ, ∀ L : ℕ, 2 ≤ L → occFree m a L ≤ C) ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    exact massive_occ_unbounded hm a h
  · rintro rfl
    exact massless_occ_bounded ha

/-- **The massless count does not depend on the spacing** (magnify `a ↦ a'` at fixed `L`).
DERIVED: `0` the zero mass and the excluded spacings; `2` the lattice dispersion. -/
theorem occFree_magnify {a a' : ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0) (L : ℕ) :
    occFree 0 a' L = occFree 0 a L := by
  have e : power 0 a' L = fun j => (a' / a) ^ 2 * power 0 a L j := by
    funext j
    rw [power_zero, power_zero]
    simp only [phat2]
    rw [mul_inv, mul_inv, ← mul_assoc]
    congr 1
    field_simp
  unfold occFree
  rw [e, occ_smul _ _ (pow_ne_zero 2 (div_ne_zero ha' ha))]

/-- **Unit weights read `L − 1` whatever the rates are** (counterexample choice: unit weights):
`occ (keptSet L) 1 = L − 1`, and the massless dispersion has `ω₀ = 0` at the excluded zero mode. The count takes
the weights alone; this records that it carries no rate. It is two facts, not a theorem relating them. DERIVED: `0` the zero mass and the
zero mode; `1` the unit weights; `2` the least box. -/
theorem count_blind_to_rates (a : ℝ) {L : ℕ} (hL : 2 ≤ L) :
    occ (keptSet L) (fun _ => (1 : ℝ)) = (L : ℝ) - 1 ∧ omega 0 a L 0 = 0 := by
  refine ⟨?_, FreqRead.omega_zero_mode le_rfl a L⟩
  rw [occ_const (kept_nonempty hL) one_pos, FreqRead.card_keptSet (by omega)]

end Free

/-! ## 3. The free massless field in `d` dimensions -/

section Dim

/-- **The kept momenta of `(Fin L)^d`**: the non-zero ones. DERIVED: `0` the zero momentum. -/
def keptD (d L : ℕ) : Finset (Fin d → Fin L) :=
  Finset.univ.filter fun k => ∃ μ, (k μ : ℕ) ≠ 0

/-- **The `d`-dimensional lattice dispersion** `p̂²(k) = ∑_μ p̂²(k_μ)`. DERIVED: no numeral. -/
def phat2d (d : ℕ) (a : ℝ) (L : ℕ) (k : Fin d → Fin L) : ℝ := ∑ μ, phat2 a L (k μ)

/-- DERIVED: `1` the one zero momentum. -/
theorem card_keptD_ge (d : ℕ) {L : ℕ} (hL : 1 ≤ L) : (L : ℝ) ^ d - 1 ≤ (keptD d L).card := by
  set z : Fin d → Fin L := fun _ => ⟨0, by omega⟩
  have hsub : (Finset.univ : Finset (Fin d → Fin L)) ⊆ insert z (keptD d L) := by
    intro k _
    by_cases h : ∃ μ, (k μ : ℕ) ≠ 0
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · push Not at h
      refine Finset.mem_insert.mpr (Or.inl ?_)
      funext μ
      exact Fin.ext (h μ)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le z (keptD d L))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h1
  have h2 : ((L ^ d : ℕ) : ℝ) ≤ ((keptD d L).card : ℝ) + 1 := by exact_mod_cast h1
  push_cast at h2
  linarith

/-- **The massless count in `d` dimensions**: `(L^d − 1)(2/L)²/d ≤ occ`. DERIVED: `2/π` Jordan's constant
(through `(2/L)²`); `1` the least dimension; `2` the least box and the lattice dispersion. -/
theorem massless_occD_ge {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : a ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    ((L : ℝ) ^ d - 1) * (2 / L) ^ 2 / d ≤ occ (keptD d L) (fun k => (phat2d d a L k)⁻¹) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc : 0 < (2 / a) ^ 2 := by positivity
  have hp1 : 0 < phat2 a L 1 := FreqRead.phat2_fund_pos ha hL
  have hw : ∀ k ∈ keptD d L, (d * (2 / a) ^ 2)⁻¹ ≤ (phat2d d a L k)⁻¹ ∧
      (phat2d d a L k)⁻¹ ≤ (phat2 a L 1)⁻¹ := by
    intro k hk
    obtain ⟨μ, hμ⟩ := (Finset.mem_filter.mp hk).2
    have hfund : phat2 a L 1 ≤ phat2 a L (k μ) :=
      FreqRead.phat2_fund_le (Nat.one_le_iff_ne_zero.mpr hμ) (by have := (k μ).isLt; omega)
    have hle : phat2 a L (k μ) ≤ phat2d d a L k :=
      Finset.single_le_sum (f := fun ν => phat2 a L (k ν)) (fun ν _ => FreqRead.phat2_nonneg a L (k ν))
        (Finset.mem_univ μ)
    have hup : phat2d d a L k ≤ d * (2 / a) ^ 2 := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin d)) (fun ν => phat2 a L (k ν))
        ((2 / a) ^ 2) (fun ν _ => phat2_le a L (k ν))
      simpa [phat2d, nsmul_eq_mul] using this
    exact ⟨inv_anti₀ (hp1.trans_le (hfund.trans hle)) hup, inv_anti₀ hp1 (hfund.trans hle)⟩
  have hne : (keptD d L).Nonempty :=
    ⟨fun _ => ⟨1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨0, by omega⟩, by simp⟩⟩⟩
  have h := occ_ge (by positivity) hw hne
  have hcard := card_keptD_ge d (L := L) (by omega)
  have hs : 2 / (L : ℝ) ≤ Real.sin (π * ((1 : ℕ) : ℝ) / L) := by
    have h0 : 0 ≤ π * 1 / (L : ℝ) := by positivity
    have h1 : π * 1 / (L : ℝ) ≤ π / 2 := by
      have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
      rw [div_le_div_iff₀ hLr two_pos]
      nlinarith [pi_pos]
    have := Real.mul_le_sin h0 h1
    rw [Nat.cast_one]
    calc 2 / (L : ℝ) = 2 / π * (π * 1 / L) := by field_simp
      _ ≤ _ := this
  have e : ((keptD d L).card : ℝ) * (d * (2 / a) ^ 2)⁻¹ / (phat2 a L 1)⁻¹ =
      ((keptD d L).card : ℝ) * Real.sin (π * ((1 : ℕ) : ℝ) / L) ^ 2 / d := by
    rw [div_inv_eq_mul]
    simp only [phat2]
    field_simp
  rw [e] at h
  have hsq : (2 / (L : ℝ)) ^ 2 ≤ Real.sin (π * ((1 : ℕ) : ℝ) / L) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  have hcard0 : (0 : ℝ) ≤ (L : ℝ) ^ d - 1 := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))
    linarith
  calc ((L : ℝ) ^ d - 1) * (2 / L) ^ 2 / d ≤ ((keptD d L).card : ℝ) * Real.sin (π * ((1 : ℕ) : ℝ) / L) ^ 2 / d := by
        apply div_le_div_of_nonneg_right _ hdr.le
        exact mul_le_mul hcard hsq (by positivity) (Nat.cast_nonneg _)
    _ ≤ _ := h

/-- **In `d ≥ 3` dimensions the massless count is unbounded as the window opens.** DERIVED: `3` the least
dimension where `1/p̂²` is integrable at the origin; `4` the square of `2/L`; `1`, `2` the shift `L = n + 2`. -/
theorem massless_occD_unbounded {d : ℕ} (hd : 3 ≤ d) {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ C : ℝ, ∀ L : ℕ, 2 ≤ L → occ (keptD d L) (fun k => (phat2d d a L k)⁻¹) ≤ C := by
  rintro ⟨C, hC⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have key : ∀ L : ℕ, 2 ≤ L → 4 * ((L : ℝ) - 1) / d ≤ occ (keptD d L) (fun k => (phat2d d a L k)⁻¹) := by
    intro L hL
    have h := massless_occD_ge (d := d) (by omega) ha hL
    have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hpow : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
    have h3 : 4 * ((L : ℝ) - 1) ≤ ((L : ℝ) ^ d - 1) * (2 / L) ^ 2 := by
      rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    exact (div_le_div_of_nonneg_right h3 hdr.le).trans h
  obtain ⟨n, h3⟩ : ∃ n : ℕ, C * d / 4 ≤ n := ⟨_, Nat.le_ceil _⟩
  have h1 := key (n + 2) (by omega)
  have h2 := hC (n + 2) (by omega)
  have h4 : ((n + 2 : ℕ) : ℝ) - 1 = n + 1 := by push_cast; ring
  rw [h4, div_le_iff₀ hdr] at h1
  have : C * d < 4 * ((n : ℝ) + 1) := by linarith
  nlinarith

end Dim

end MassGap.FloorModes

#print axioms MassGap.FloorModes.occ_smul
#print axioms MassGap.FloorModes.occ_const
#print axioms MassGap.FloorModes.occ_le_card
#print axioms MassGap.FloorModes.occ_ge
#print axioms MassGap.FloorModes.gibbs
#print axioms MassGap.FloorModes.massive_occ_ge
#print axioms MassGap.FloorModes.massive_occ_unbounded
#print axioms MassGap.FloorModes.summable_negMulLog_invSq
#print axioms MassGap.FloorModes.jordan
#print axioms MassGap.FloorModes.massless_ratio
#print axioms MassGap.FloorModes.massless_occ_bounded
#print axioms MassGap.FloorModes.occFree_bounded_iff
#print axioms MassGap.FloorModes.occFree_magnify
#print axioms MassGap.FloorModes.count_blind_to_rates
#print axioms MassGap.FloorModes.massless_occD_ge
#print axioms MassGap.FloorModes.massless_occD_unbounded
