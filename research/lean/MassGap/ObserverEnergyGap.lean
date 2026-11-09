import Mathlib
import MassGap.ObserverEnergyV

noncomputable section

/-!
# MassGap.ObserverEnergyGap — V on the coarse-readable span joined with the leakage criterion

`ObserverEnergyV` proves the gap of the energy density's transfer at step `m₀` from statement V, whose
clause 2 asks every reflected smeared product to factor through one coarse map with a bounded-support
reader. For the APE observer that clause fails off the coarse-readable fields. `ObserverResidual`
proves the gap from a coarse rate `ρc`, a residual rate `ρr` and a leakage `η` with
`η² < (1 − ρc²)(1 − ρr²)`. This module joins the two.

1. **Per-vector decay is a contraction of every power** (`form_T_le_of_decay`,
   `form_pow_le_of_decay`): a single vector `x` with `⟨x, T^{2n} x⟩ ≤ K r^{2n}` has
   `‖T^j x‖² ≤ (r^j)² ‖x‖²` for every `j`. No invariant subspace is needed: the bound is the spectral
   measure of `x` alone (`SecondEigenvalue.norm_le_of_absolute_iterate_bound`).
2. **The join on any transfer** (`gapAt_of_coarse_decay_leak`): per-vector decay at rate `r < 1` on the
   vacuum-orthogonal part of a span `C` holding the vacuum, plus the leakage inputs (`LeakInputs`: an
   orthogonal split, the residual rate `ρr`, the leakage `η` at time `k`) with
   `η² < (1 − r^{2k})(1 − ρr²)`, give a gap.
3. **Clustering on a set of monomials gives the decay on their span** (`form_iterate_le_of_abs_cluster_on`,
   `coarse_contract_gTransfer`, `LatClusterRateOn`, `flow_coarse_contract`): the reflected clustering
   bound asked only for pairs in a set `S` of margin monomials contracts `T^k` on
   `coarseSpan S = Finsupp.supported ℝ ℝ S` by `(ρ^k)²`.
4. **V on the generators** (`ObserverVPairOn`, `ObserverVOn`, `latClusterRateOn_of_observerVPairOn`,
   `observerVPairOn_of_observerVOn`): statement V with its reader clauses asked only for pairs `P, Q ∈ S`
   (and every time translate of `Q` by `aₘ₀ n`). The coarse law clause is unchanged. The rate is
   `vRate q`, as for the full V.
5. **The energy density** (`energy_gapAt_of_coarseV_leak`, `energy_M_of_coarseV_leak`,
   `energy_clay_of_coarseV_leak`): V on `S ∋ ∅` plus `LeakInputs` on `coarseSpan S` at time `k` with
   `η² < (1 − vRate q^{2k})(1 − ρr²)` give the gap of `energyTransfer … m₀`, hence M and, with E and N,
   the continuum statement.

The coarse rate here is the proved box's, `vRate q ^ k`, with `1 − vRate q^{2k} = 1 − e^{−2.2504·10⁻⁶ k/q}`.
A measured coarse decay faster than the box's is not available to this theorem: it would have to be
supplied as a separate coarse input, not by V. Without N the conclusion is free
(`ObserverEnergyM.flowClusterAbs_of_not_connectedNonzero`).
-/

namespace MassGap.ObserverEnergyGap

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV Filter
open MassGap.KnabeCriterion (PatchSystem ReadsNot periodicGaugeInvSubmodule
  periodicGaugeInv_of_isIGaugeInvariant)
open MassGap.HeatBathGapDecay (Far nrm nrm_nonneg SeparatedPair)
open MassGap.WeightedErgodic (oneW)
open MassGap.WeightedTorus (wTorusState wForm wCondExp wLift torusObs_wLift wExpect)
open MassGap.LocalPotential (LocalPotFam potWeight)
open MassGap.PotKnabe (potSys)
open MassGap.ObserverKnabe (obsNb Near2)
open MassGap.PeriodicState (torusObs)
open MassGap.GaugeInvariantAlgebra (IsIGaugeInvariant)
open scoped Topology

/-! ## 1. Per-vector decay is a contraction of every power -/

section Generic

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **One vector's decay bounds its first step.** If `⟨x, T^{2n} x⟩ ≤ K r^{2n}` for all `n` and
`0 ≤ r`, then `‖T x‖² ≤ r² ‖x‖²` (`ClayCapstone.absolute_decay_of_form_decay`,
`SecondEigenvalue.norm_le_of_absolute_iterate_bound`; the body of
`ContinuumSep.gapAt_of_per_vector_form_decay` read for one vector).

DERIVED: `0` the sign of `r`; `2` the doubled separation and the form's degree. -/
theorem form_T_le_of_decay (D : Transfer.TransferData A) {r K : ℝ} (hr : 0 ≤ r) (x : A)
    (hK : ∀ n : ℕ, D.form x ((D.T ^ (2 * n)) x) ≤ K * r ^ (2 * n)) :
    D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x := by
  obtain ⟨K', hK'⟩ := ClayCapstone.absolute_decay_of_form_decay D x hr hK
  have hb : ‖D.Tq (Transfer.GNS.mk D.toReflForm x)‖ ≤ r * ‖Transfer.GNS.mk D.toReflForm x‖ :=
    SecondEigenvalue.norm_le_of_absolute_iterate_bound D.Tq D.Tq_isSymmetric hr hK'
  rw [D.Tq_mk] at hb
  have hTx : ‖Transfer.GNS.mk D.toReflForm (D.T x)‖ * ‖Transfer.GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := Transfer.GNS.norm_mk_mul_norm_mk _
  have hxx : ‖Transfer.GNS.mk D.toReflForm x‖ * ‖Transfer.GNS.mk D.toReflForm x‖ = D.form x x :=
    Transfer.GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖Transfer.GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖Transfer.GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms form_T_le_of_decay

/-- **One vector's decay bounds every power.** Under the hypothesis of `form_T_le_of_decay`,
`‖T^j x‖² ≤ (r^j)² ‖x‖²` for every `j`: `T^j x` decays with constant `K r^{2j}`
(`TransferGap.form_pow_symm`), so each step contracts by `r²`.

DERIVED: `0` the sign of `r` and the base case; `1` the successor step; `2` the doubled separation and
the form's degree. -/
theorem form_pow_le_of_decay (D : Transfer.TransferData A) {r K : ℝ} (hr : 0 ≤ r) (x : A)
    (hK : ∀ n : ℕ, D.form x ((D.T ^ (2 * n)) x) ≤ K * r ^ (2 * n)) (j : ℕ) :
    D.form ((D.T ^ j) x) ((D.T ^ j) x) ≤ (r ^ j) ^ 2 * D.form x x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hdec : ∀ n : ℕ, D.form ((D.T ^ j) x) ((D.T ^ (2 * n)) ((D.T ^ j) x))
        ≤ (K * r ^ (2 * j)) * r ^ (2 * n) := by
      intro n
      have e : (D.T ^ j) ((D.T ^ (2 * n)) ((D.T ^ j) x)) = (D.T ^ (2 * (n + j))) x := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add]
        have h2 : j + 2 * n + j = 2 * (n + j) := by ring
        rw [h2]
      rw [TransferGap.form_pow_symm D j x, e]
      calc D.form x ((D.T ^ (2 * (n + j))) x) ≤ K * r ^ (2 * (n + j)) := hK (n + j)
        _ = (K * r ^ (2 * j)) * r ^ (2 * n) := by ring
    have h1 := form_T_le_of_decay D hr ((D.T ^ j) x) hdec
    have hs : (D.T ^ (j + 1)) x = D.T ((D.T ^ j) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hs]
    calc D.form (D.T ((D.T ^ j) x)) (D.T ((D.T ^ j) x))
        ≤ r ^ 2 * D.form ((D.T ^ j) x) ((D.T ^ j) x) := h1
      _ ≤ r ^ 2 * ((r ^ j) ^ 2 * D.form x x) := mul_le_mul_of_nonneg_left ih (sq_nonneg r)
      _ = (r ^ (j + 1)) ^ 2 * D.form x x := by ring

#print axioms form_pow_le_of_decay

/-- **The leakage inputs at time `k`** for a span `C`: every vector splits as `c + d` with `c ∈ C` and
`d` orthogonal to `C`; `T^k` contracts the residual `C^⊥` by `ρr` (squared); and the leakage
`⟨T^k c, T^k d⟩ = ⟨c, T^{2k} d⟩` of a vacuum-orthogonal `c ∈ C` and a residual `d` is at most
`η ‖c‖ ‖d‖`. These are the `hsplit`, `hres`, `hleak` of `ObserverResidual.gapAt_of_leak`.

DERIVED: `0` is orthogonality; `2` the form's degree. -/
def LeakInputs (D : Transfer.TransferData A) (C : Submodule ℝ A) (k : ℕ) (ρr η : ℝ) : Prop :=
  (∀ x : A, ∃ c ∈ C, ∃ d : A, (∀ z ∈ C, D.form z d = 0) ∧ x = c + d)
  ∧ (∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) d) ((D.T ^ k) d) ≤ ρr ^ 2 * D.form d d)
  ∧ (∀ c ∈ C, D.form c D.vac = 0 → ∀ d : A, (∀ z ∈ C, D.form z d = 0) →
      D.form ((D.T ^ k) c) ((D.T ^ k) d) ^ 2 ≤ η ^ 2 * (D.form c c * D.form d d))

/-- **The join on any transfer.** A span `C` holding the vacuum whose vacuum-orthogonal members decay
at rate `0 ≤ r < 1` (each with its own constant), and the leakage inputs at time `k ≥ 1` with
`ρr² < 1` and `η² < (1 − (r^k)²)(1 − ρr²)`, give `GapAt D ρ` for some `0 < ρ < 1`
(`form_pow_le_of_decay` supplies the coarse contraction `(r^k)²` of `gapAt_of_leak`).

DERIVED: `0` and `1` bracket `r`, `ρr`, `ρ` and `k`; `2` the doubled separation and the form's degree. -/
theorem gapAt_of_coarse_decay_leak (D : Transfer.TransferData A) (C : Submodule ℝ A)
    (hvac : D.vac ∈ C) {k : ℕ} (hk : 0 < k) {r ρr η : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hρr : ρr ^ 2 < 1) (hη : η ^ 2 < (1 - (r ^ k) ^ 2) * (1 - ρr ^ 2))
    (hdec : ∀ c ∈ C, D.form c D.vac = 0 →
      ∃ K : ℝ, ∀ n : ℕ, D.form c ((D.T ^ (2 * n)) c) ≤ K * r ^ (2 * n))
    (hL : LeakInputs D C k ρr η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt D ρ := by
  obtain ⟨hsplit, hres, hleak⟩ := hL
  have hrk : r ^ k < 1 := pow_lt_one₀ hr0 hr1 hk.ne'
  have hrk0 : 0 ≤ r ^ k := pow_nonneg hr0 k
  have hρc : (r ^ k) ^ 2 < 1 := by nlinarith
  refine ObserverResidual.gapAt_of_leak D C hvac hsplit hk hρc hρr hη ?_ hres hleak
  intro c hc hcv
  obtain ⟨K, hK⟩ := hdec c hc hcv
  exact form_pow_le_of_decay D hr0 c hK k

#print axioms gapAt_of_coarse_decay_leak

end Generic

/-! ## 2. Clustering on a set of monomials gives the decay on their span -/

section Kernel

variable {M : Type}

/-- **The coarse span of a set of basis vectors**: the combinations supported in `S`.

DERIVED: no numeral. -/
abbrev coarseSpan (S : Set M) : Submodule ℝ (M →₀ ℝ) := Finsupp.supported ℝ ℝ S

/-- **Per-vector decay from clustering on a set.** If every pair in `S` has its own constant `C` with
`|K P (shⁿ Q) − K P e · K e Q| ≤ C ρⁿ`, every combination supported in `S` and orthogonal to `e`
decays at rate `ρ`. Pairs outside `S` are not asked (`FlowCapstone.form_iterate_le_of_abs_cluster`
restricted to the support).

DERIVED: `1` is the vacuum coefficient; `0` is the vanishing pairing and the constant off `S`. -/
theorem form_iterate_le_of_abs_cluster_on (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (sh : M → M) (e : M) {ρ : ℝ} (S : Set M)
    (hcl : ∀ P ∈ S, ∀ Q ∈ S, ∃ C : ℝ, ∀ n : ℕ, |K P (sh^[n] Q) - K P e * K e Q| ≤ C * ρ ^ n)
    (x : M →₀ ℝ) (hxS : x ∈ coarseSpan S) (hx : gForm K x (Finsupp.single e 1) = 0) :
    ∃ C : ℝ, ∀ n : ℕ, gForm K x ((⇑(gT sh))^[n] x) ≤ C * ρ ^ n := by
  classical
  have hsub : ∀ P ∈ x.support, P ∈ S := fun P hP =>
    ((Finsupp.mem_supported ℝ x).mp hxS) (Finset.mem_coe.mpr hP)
  have hvacR : ∑ P ∈ x.support, x P * K P e = 0 := by
    rw [← gForm_single_right]; exact hx
  have hvacL : ∑ Q ∈ x.support, x Q * K e Q = 0 := by
    rw [← hvacR]; exact Finset.sum_congr rfl (fun Q _ => by rw [hK e Q])
  let Cf : M → M → ℝ := fun P Q =>
    if h : P ∈ S ∧ Q ∈ S then Classical.choose (hcl P h.1 Q h.2) else 0
  have hCf : ∀ P ∈ S, ∀ Q ∈ S, ∀ n : ℕ, |K P (sh^[n] Q) - K P e * K e Q| ≤ Cf P Q * ρ ^ n := by
    intro P hP Q hQ n
    have h := Classical.choose_spec (hcl P hP Q hQ) n
    have hc : Cf P Q = Classical.choose (hcl P hP Q hQ) := dif_pos ⟨hP, hQ⟩
    rw [hc]
    exact h
  refine ⟨∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Cf P Q, fun n => ?_⟩
  have hsplit : ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * K P (sh^[n] Q)
      = ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * (K P (sh^[n] Q) - K P e * K e Q)
        + ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * (K P e * K e Q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  have hzero : ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * (K P e * K e Q) = 0 := by
    have h : ∀ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * (K P e * K e Q)
        = x P * K P e * ∑ Q ∈ x.support, x Q * K e Q := by
      intro P _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun Q _ => by ring)
    rw [Finset.sum_congr rfl h, hvacL]
    simp
  rw [gForm_iterate_eq, hsplit, hzero, add_zero]
  calc ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q * (K P (sh^[n] Q) - K P e * K e Q)
      ≤ ∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * (Cf P Q * ρ ^ n) := by
        refine Finset.sum_le_sum (fun P hP => Finset.sum_le_sum (fun Q hQ => ?_))
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hCf P (hsub P hP) Q (hsub Q hQ) n)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Cf P Q) * ρ ^ n := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring

#print axioms form_iterate_le_of_abs_cluster_on

/-- **The coarse contraction of a kernel transfer from clustering on a set.** Under clustering at rate
`0 ≤ ρ` on the pairs of `S`, `T^k` contracts the vacuum-orthogonal part of `coarseSpan S` by `(ρ^k)²`,
for every `k` (`form_iterate_le_of_abs_cluster_on`, `form_pow_le_of_decay`).

DERIVED: `0` the sign of `ρ` and the vanishing pairing; `2` the doubled separation and the form's
degree. -/
theorem coarse_contract_gTransfer (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C)
    (e : M) (he : sh e = e) (hee : K e e = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (S : Set M)
    (hcl : ∀ P ∈ S, ∀ Q ∈ S, ∃ C : ℝ, ∀ n : ℕ, |K P (sh^[n] Q) - K P e * K e Q| ≤ C * ρ ^ n)
    (k : ℕ) :
    ∀ c ∈ coarseSpan S, (gTransfer K hK hG sh hsh hb e he hee).form c
        (gTransfer K hK hG sh hsh hb e he hee).vac = 0 →
      (gTransfer K hK hG sh hsh hb e he hee).form
          (((gTransfer K hK hG sh hsh hb e he hee).T ^ k) c)
          (((gTransfer K hK hG sh hsh hb e he hee).T ^ k) c)
        ≤ (ρ ^ k) ^ 2 * (gTransfer K hK hG sh hsh hb e he hee).form c c := by
  intro c hc hcv
  obtain ⟨C, hC⟩ := form_iterate_le_of_abs_cluster_on K hK sh e S hcl c hc hcv
  refine form_pow_le_of_decay _ hρ c (K := C) (fun n => ?_) k
  rw [Module.End.pow_apply]
  exact hC (2 * n)

#print axioms coarse_contract_gTransfer

/-- **Per-vector decay of a kernel transfer from clustering on a set**, in the form
`gapAt_of_coarse_decay_leak` consumes.

DERIVED: `0` the vanishing pairing; `2` the doubled separation. -/
theorem coarse_decay_gTransfer (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C)
    (e : M) (he : sh e = e) (hee : K e e = 1) {ρ : ℝ} (S : Set M)
    (hcl : ∀ P ∈ S, ∀ Q ∈ S, ∃ C : ℝ, ∀ n : ℕ, |K P (sh^[n] Q) - K P e * K e Q| ≤ C * ρ ^ n) :
    ∀ c ∈ coarseSpan S, (gTransfer K hK hG sh hsh hb e he hee).form c
        (gTransfer K hK hG sh hsh hb e he hee).vac = 0 →
      ∃ C : ℝ, ∀ n : ℕ, (gTransfer K hK hG sh hsh hb e he hee).form c
        (((gTransfer K hK hG sh hsh hb e he hee).T ^ (2 * n)) c) ≤ C * ρ ^ (2 * n) := by
  intro c hc hcv
  obtain ⟨C, hC⟩ := form_iterate_le_of_abs_cluster_on K hK sh e S hcl c hc hcv
  refine ⟨C, fun n => ?_⟩
  rw [Module.End.pow_apply]
  exact hC (2 * n)

#print axioms coarse_decay_gTransfer

end Kernel

/-! ## 3. Lattice clustering on a set of margin monomials -/

section Flow

variable {N : ℕ}

/-- **Lattice clustering at rate `ρ` on a set `S` of margin monomials**: `LatClusterRate` asked only for
pairs `P, Q ∈ S`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def LatClusterRateOn (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (m0 : ℕ) (ρ : ℝ)
    (S : Set (MarginMono N τ r)) : Prop :=
  ∀ P ∈ S, ∀ Q ∈ S, ∃ C : ℝ, ∀ n : ℕ, ∀ᶠ k in atTop,
    |latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m0 τ n) Q.1))
      - latSF hN Φ k (pairFam τ P.1 (emptyMono N))
        * latSF hN Φ k (pairFam τ (emptyMono N) (Mono.shift (timeVec N m0 τ n) Q.1))|
      ≤ C * ρ ^ n

/-- **Lattice clustering on `S` gives per-vector decay on its span** in the flowed transfer at step
`m₀` (`kernF_conn_le_of_lat`, `coarse_decay_gTransfer`).

DERIVED: `0` is the excluded colour count and the vanishing pairing; `2` the doubled separation; `4`
in `Fin 4` is the spacetime dimension. -/
theorem flow_coarse_decay (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving τ r) (m0 : ℕ) {ρ : ℝ} (S : Set (MarginMono N τ r))
    (h : LatClusterRateOn hN Φ τ r m0 ρ S) :
    ∀ c ∈ coarseSpan S, (flowTransfer hN Φ hB τ hpos m0).form c
        (flowTransfer hN Φ hB τ hpos m0).vac = 0 →
      ∃ C : ℝ, ∀ n : ℕ, (flowTransfer hN Φ hB τ hpos m0).form c
        (((flowTransfer hN Φ hB τ hpos m0).T ^ (2 * n)) c) ≤ C * ρ ^ (2 * n) := by
  unfold flowTransfer
  refine coarse_decay_gTransfer _ _ _ _ _ _ _ _ _ S (fun P hP Q hQ => ?_)
  obtain ⟨C, hC⟩ := h P hP Q hQ
  refine ⟨C, fun n => ?_⟩
  rw [MarginMono.shift_iterate]
  exact kernF_conn_le_of_lat hN Φ hB τ m0 n P.1 Q.1 (hC n)

#print axioms flow_coarse_decay

end Flow

/-! ## 4. Statement V on the generators of the coarse span -/

section VOn

/-- **Statement V, pairing form, on a set `S` of margin monomials**: `ObserverVPair` asked only for
pairs `P, Q ∈ S` (with every time translate of `Q` by `aₘ₀ n`).

DERIVED: `2` is the rank; `299999` the extent offset of `boxSys`; `4` in `Fin 4` is the spacetime
dimension. -/
def ObserverVPairOn (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 q : ℕ) (S : Set (MarginMono 2 τ r)) :
    Prop :=
  ∀ P ∈ S, ∀ Q ∈ S, ∃ (a b : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
    ∃ (β : ℝ) (Fp : LocalPotFam 2) (hdiam : HDiam Fp), InBox β Fp ∧
    ∃ (𝒰 : Filter ℕ) (f g : ∀ j : ℕ, (boxSys β Fp hdiam j).E), 𝒰.NeBot ∧
      (∀ᶠ j in 𝒰, SeparatedPair (boxSys β Fp hdiam j) (obsNb (2 * (j + 299999) + 1))
          (f j) (g j) (n / q) a b
        ∧ (boxSys β Fp hdiam j).B (f j) (f j) ≤ Mb ∧ (boxSys β Fp hdiam j).B (g j) (g j) ≤ Mb) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (f j) (g j)) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1)))) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (f j) (oneW (j + 299999))) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2)))) ∧
      Tendsto (fun j => (boxSys β Fp hdiam j).B (g j) (oneW (j + 299999))) 𝒰
        (𝓝 (latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))))

/-- **V on `S` gives lattice clustering on `S` at `vRate q`** (the proof of
`latClusterRate_of_observerVPair`, pair by pair).

DERIVED: `7/100` the sharp box's gap; `5184` the window count; `299999` the extent offset; `2` the
rank; `0` the lower end of `q`. -/
theorem latClusterRateOn_of_observerVPairOn {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 q : ℕ}
    {S : Set (MarginMono 2 τ r)} (hq : 0 < q) (hV : ObserverVPairOn Φ τ r m0 q S) :
    LatClusterRateOn two_ne Φ τ r m0 (vRate q) S := by
  intro P hP Q hQ
  obtain ⟨a, b, Mb, hPQ⟩ := hV P hP Q hQ
  have hρ0 := coarseRate_pos 5184 (7 / 100)
  have hρ1 := coarseRate_lt_one 5184 (by norm_num : (0 : ℝ) < 7 / 100)
  have hK : 0 ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a) :=
    mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
    * (coarseRate 5184 (7 / 100))⁻¹, fun n => ?_⟩
  filter_upwards [hPQ n] with k hk
  obtain ⟨β, Fp, hdiam, ⟨hβ0, hβ, hν⟩, 𝒰, f, g, hU, hev, h1, h2, h3⟩ := hk
  haveI := hU
  refine le_of_tendsto ((h1.sub (h2.mul h3)).abs) ?_
  filter_upwards [hev] with j hj
  obtain ⟨hsep, hff, hgg⟩ := hj
  have hb := pot_cluster_rate hβ0 hβ Fp hν hdiam (j + 299999) (by omega) (f j) (g j) (n / q)
    hsep hff hgg
  calc _ ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
        * coarseRate 5184 (7 / 100) ^ (n / q) := hb
    _ ≤ max Mb 0 * ((b : ℝ) + 2 / (7 / 100) * Real.exp (7 / 100 / 2) * a)
        * ((coarseRate 5184 (7 / 100))⁻¹ * vRate q ^ n) :=
        mul_le_mul_of_nonneg_left (pow_div_le hρ0 hρ1 hq n) hK
    _ = _ := by ring

#print axioms latClusterRateOn_of_observerVPairOn

/-- **Statement V, law form, on a set `S` of margin monomials**: `ObserverV` with the coarse law
clause unchanged and the reader, moment and separation clauses asked only for pairs `P, Q ∈ S`. Clause
2 (factorisation through the coarse map with bounded-support readers) is not asked of any monomial
outside `S`.

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `4` in `Fin 4` is the
spacetime dimension. -/
def ObserverVOn (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 q : ℕ) (S : Set (MarginMono 2 τ r)) : Prop :=
  ∃ (β : ℕ → ℝ) (Fp : ℕ → LocalPotFam 2) (hdiam : ∀ k, HDiam (Fp k)) (𝒰 : ℕ → Filter ℕ)
    (χ : ℕ → C(Cfg 2, Cfg 2)),
    (∀ᶠ k in atTop, InBox (β k) (Fp k) ∧ (𝒰 k).NeBot ∧ CoarseLawAt k (β k) (Fp k) (𝒰 k) (χ k)) ∧
    ∀ P ∈ S, ∀ Q ∈ S, ∃ (a b : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
      ∃ (GP GQ : C(Cfg 2, ℝ)) (SP SQ : Finset ILink),
        IsIGaugeInvariant GP ∧ IsIGaugeInvariant GQ ∧ IsLocalOn SP ⇑GP ∧ IsLocalOn SQ ⇑GQ ∧
        SP.card ≤ a ∧ SQ.card ≤ b ∧
        LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1)) = GP.comp (χ k) ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1)) = GQ.comp (χ k) ∧
        stateK two_ne k (GP.comp (χ k) * GP.comp (χ k)) < Mb ∧
        stateK two_ne k (GQ.comp (χ k) * GQ.comp (χ k)) < Mb ∧
        ∀ᶠ j in 𝒰 k, ∀ l ∈ SQ.image (linkMod (2 * (j + 299999) + 1)),
          Far (obsNb (2 * (j + 299999) + 1)) (SP.image (linkMod (2 * (j + 299999) + 1))) (n / q) l

/-- **The full V is V on every set.**

DERIVED: no numeral beyond those of `ObserverV`. -/
theorem observerVOn_of_observerV {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 q : ℕ}
    (hV : ObserverV Φ τ r m0 q) (S : Set (MarginMono 2 τ r)) : ObserverVOn Φ τ r m0 q S := by
  obtain ⟨β, Fp, hdiam, 𝒰, χ, hlaw, hread⟩ := hV
  exact ⟨β, Fp, hdiam, 𝒰, χ, hlaw, fun P _ Q _ => hread P Q⟩

#print axioms observerVOn_of_observerV

/-- **The law form of V on `S` gives the pairing form on `S`** (the proof of
`observerVPair_of_observerV`, pair by pair).

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `1` the unit
observable. -/
theorem observerVPairOn_of_observerVOn {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 q : ℕ}
    {S : Set (MarginMono 2 τ r)} (hV : ObserverVOn Φ τ r m0 q S) : ObserverVPairOn Φ τ r m0 q S := by
  obtain ⟨β, Fp, hdiam, 𝒰, χ, hlaw, hread⟩ := hV
  intro P hPS Q hQS
  obtain ⟨a, b, Mb, h⟩ := hread P hPS Q hQS
  refine ⟨a, b, Mb, fun n => ?_⟩
  filter_upwards [hlaw, h n] with k hk hrk
  obtain ⟨hbox, hU, hL⟩ := hk
  obtain ⟨GP, GQ, SP, SQ, hgP, hgQ, hlP, hlQ, hcP, hcQ, hP, hQ, hmP, hmQ, hfar⟩ := hrk
  refine ⟨β k, Fp k, hdiam k, hbox, 𝒰 k,
    fun j => ⟨GP, periodicGaugeInv_of_isIGaugeInvariant (2 * (j + 299999) + 1) hgP⟩,
    fun j => ⟨GQ, periodicGaugeInv_of_isIGaugeInvariant (2 * (j + 299999) + 1) hgQ⟩, hU, ?_, ?_, ?_, ?_⟩
  · have hmP' : stateK two_ne k ((GP * GP).comp (χ k)) < Mb := by
      rw [ContinuousMap.mul_comp]; exact hmP
    have hmQ' : stateK two_ne k ((GQ * GQ).comp (χ k)) < Mb := by
      rw [ContinuousMap.mul_comp]; exact hmQ
    filter_upwards [hfar, (hL (GP * GP)).eventually (Iio_mem_nhds hmP'),
      (hL (GQ * GQ)).eventually (Iio_mem_nhds hmQ')] with j hj hj1 hj2
    have hA : ((SP.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1)))).card ≤ a :=
      Finset.card_image_le.trans hcP
    have hC : ((SQ.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1)))).card ≤ b :=
      Finset.card_image_le.trans hcQ
    refine ⟨⟨(SP.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1))),
      (SQ.image (linkMod (2 * (j + 299999) + 1))
        : Finset (WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1))),
      hA, hC, fun l hl => ?_,
      fun l hl => ?_, hj⟩, le_of_lt hj1, le_of_lt hj2⟩
    · exact pot_h_null (β k) (Fp k) (hdiam k) (j + 299999) (by omega) l _
        (MassGap.HeatBathLocal.readsNot_of_isLocalOn hlP (j + 299999) l hl)
    · exact pot_h_null (β k) (Fp k) (hdiam k) (j + 299999) (by omega) l _
        (MassGap.HeatBathLocal.readsNot_of_isLocalOn hlQ (j + 299999) l hl)
  · have e : latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1))
        = stateK two_ne k ((GP * GQ).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ← hP, ← hQ]
    rw [e]
    exact hL (GP * GQ)
  · have e : latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2))
        = stateK two_ne k ((GP * 1).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hP, mono_empty,
        prodSmear_empty]
    rw [e]
    exact hL (GP * 1)
  · have e : latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))
        = stateK two_ne k ((GQ * 1).comp (χ k)) := by
      rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hQ, mono_empty,
        prodSmear_empty, mul_comm]
      rfl
    rw [e]
    exact hL (GQ * 1)

#print axioms observerVPairOn_of_observerVOn

end VOn

/-! ## 5. The energy density -/

section Energy

/-- **V on the coarse span joined with the leakage criterion gives the gap of the energy transfer.**
For a set `S` of margin monomials holding the empty one: V in pairing form on `S` at ratio `q > 0`
(`ObserverVPairOn`), and the leakage inputs on `coarseSpan S` at time `k ≥ 1` with residual rate
`ρr² < 1` and leakage `η² < (1 − (vRate q ^ k)²)(1 − ρr²)`, give `GapAt (energyTransfer … m₀) ρ` for
some `0 < ρ < 1`. The coarse contraction is `(vRate q ^ k)²`, from the box's rate alone.

DERIVED: `2` is the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `q`, `k`,
the rates and `ρ`; `1` the vacuum coefficient. -/
theorem energy_gapAt_of_coarseV_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {q : ℕ} (hq : 0 < q)
    (hV : ObserverVPairOn (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q S)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - (vRate q ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) ρ := by
  have hvac : (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac ∈ coarseSpan S :=
    Finsupp.single_mem_supported ℝ (1 : ℝ) hS
  exact gapAt_of_coarse_decay_leak _ (coarseSpan S) hvac hk (vRate_pos q).le (vRate_lt_one hq) hρr
    hη (flow_coarse_decay two_ne _ hB τ _ m0 S (latClusterRateOn_of_observerVPairOn hq hV)) hL

#print axioms energy_gapAt_of_coarseV_leak

/-- **M for the energy density from V on the coarse span and the leakage criterion** (law form of V on
`S`; `energy_M_iff_gap`).

DERIVED: `2` is the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `q`, `k`,
`L` and the rates. -/
theorem energy_M_of_coarseV_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {q : ℕ} (hq : 0 < q)
    (hV : ObserverVOn (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q S)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - (vRate q ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hLw).mpr
    (energy_gapAt_of_coarseV_leak hc0 hc n R D hD s hs hB τ hphys m0 S hS hq
      (observerVPairOn_of_observerVOn hV) hk hρr hη hL)

#print axioms energy_M_of_coarseV_leak

/-- **The continuum statement from E, V on the coarse span, the leakage criterion and N**
(`energy_clay_of_gap` at the rate the join supplies). The leakage inputs are read on the transfer built
from the smeared-moment bound `hM`.

DERIVED: `2` is the rank, the form's degree and makes the power even; `1/6` the dominance bound; `0`
and `1` bracket `q`, `k`, `L` and the rates. -/
theorem energy_clay_of_coarseV_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK two_ne k (smear (dySpacing 2 k)
        ((obsEnergyOn c hc0 hc n R D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {q : ℕ} (hq : 0 < q)
    (hV : ObserverVOn (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 q S)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - (vRate q ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs
      (uniformBoundF_of_smearedMomentBound two_ne _
        (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM))
      τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) (hNT : FlowConnectedNonzero two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ,
      ContinuumClay.GappedAt
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m)
          (Real.exp (-(c' / L) * dySpacing 2 m))
        ∧ ContinuumClay.NontrivialVacuum
          (flowTransfer two_ne (obsEnergyOn c hc0 hc n R D hD s hs)
            (uniformBoundF_of_smearedMomentBound two_ne _
              (smearedMomentBound_energyOn two_ne (obsConfFlow c hc0 hc n R) D hD s hs hM)) τ
            (Flow.posPreserving_of_physRange two_ne _ hphys τ) m) := by
  obtain ⟨ρ, hρ0, hρ1, hg⟩ := energy_gapAt_of_coarseV_leak hc0 hc n R D hD s hs _ τ hphys m0 S hS hq
    (observerVPairOn_of_observerVOn hV) hk hρr hη hL
  exact energy_clay_of_gap hc0 hc n R D hD s hs hM τ hphys m0 hLw hρ0 hρ1 hg hNT

#print axioms energy_clay_of_coarseV_leak

end Energy

end MassGap.ObserverEnergyGap
