import Mathlib
import MassGap.BoxGapBE
import MassGap.CouplingTower

noncomputable section

/-!
# MassGap.UVStepMap — what `RestoreShimsClay.UVBelowIR` asks, exactly

`RestoreShimsClay.UVBelowIR τ p hN β₀ βUV M₀` asks for non-negative losses `ε` with a dyadic
budget `E < M₀` below `aRun N β₀` and the clipped block step `UVIRSplit.UVLossStepBelow τ p hN βUV ε M₀`.
This module maps it onto plain gap statements.

## Results

1. `uvBelowIR_iff_dyadic`: the loss function matters only at the dyadic spacings `aRun N β₀ / 2ⁱ`.
   `UVBelowIR` holds exactly when a sequence `e i ≥ 0` with partial sums at most `E < M₀` carries every
   rate `M ≤ M₀` from each coupling `β` at spacing exactly `aRun N β₀ / 2ⁱ` to every `β'` in the next
   octave, losing `e i` (`DyadicStep`). Off the dyadic spacings the loss is set to `max M₀ 0`, where the
   step is automatic (`TransferGap.gapAt_of_one_le_sq`).
2. `gapAt_branch_of_uvBelowIR`: `UVBelowIR` and `IRGapAt` at `β₀` give the gap at one physical rate
   `M₀ − E > 0` at every coupling of the branch `Branch N β₀ βUV` (`βUV ≤ β`, `aRun N β ≤ aRun N β₀`),
   not only eventually.
3. `uvBelowIR_of_branchGap`: conversely the gap at one physical rate `m > 0` on the branch gives
   `UVBelowIR` at every rate `0 < M ≤ m`, with zero loss on the branch.
4. `exists_uvBelowIR_iff_branchGap`: given the proved IR gap at `β₀` at rate `M₀`, `UVBelowIR` at some
   rate in `(0, M₀]` holds exactly when the lattice gap holds at one positive physical rate on the whole
   branch (`BranchGap`). The loss bookkeeping adds nothing: the input is the lattice gap, uniform in the
   spacing, at every coupling past `β₀` on the weak side.
5. `uvBelowIR_of_split`: the finite + tail split. A gap at rate `m₁` on the finite part
   (`aRun N β₀ / 2ᴷ ≤ aRun N β`, `K` octaves) and at rate `m₂` on the tail (`aRun N β < aRun N β₀ / 2ᴷ`) give
   `UVBelowIR` at `min (min m₁ m₂) M₀`.
6. `branchGap_of_boundedSeed`, `strongEnd_of_boundedSeed`, `clay_of_boundedSeed`: the window read of
   `CouplingTower`. If on the branch some window `2^w` is in the basin of `DoublingSharp`
   (`windowCoupling N β w ≤ 1/1000`) at physical size `2^w · aRun N β ≤ C`, the branch gap holds at rate
   `log 2 / C` (`CouplingTower.windowGap`), `CouplingTower.StrongEnd N` holds, and with E, N, Y the
   continuum Clay statement follows (`clay_of_branchGap`).

## Status

No gap on the branch beyond `β₀` is proved here: `BranchGap` and `BoundedSeed` are hypotheses, not theorems, and no
theorem in this tree establishes either. The file proves only the equivalences and implications above. E, N and Y
enter `clay_of_branchGap` and `clay_of_boundedSeed` as unchanged hypotheses.

## Relation to `StrongEnd` and `NoStall`

`StrongEnd N` gives a gap frequently in `β`, at the lattice rate `log 2 / 2^w` of the seed window, with
no bound on `2^w · aRun N β`. `StrongAnchor.NoStall N` gives the seed at every `β ≥ 0`, again with no
bound on its physical size. `UVBelowIR` with the IR gap is the gap at one physical rate on the whole
branch (4). So `UVBelowIR` at `β₀` is neither implied by `StrongEnd` nor by `NoStall` in this tree: it
asks the extra uniformity `sup_β 2^{w(β)} · aRun N β < ∞` (6 shows that uniformity suffices). I found no
theorem in the tree from a transfer gap to `StrongAnchor.Vanishes`, so the reverse implication is not
available either.

## The tower in numbers (computed with mpmath at 30 digits, not proved; not in Lean)

`SU(2)`, `β₀ = 3/40`: `aRun 2 β₀ = 0.61026`; the weak-side couplings at spacing `aRun 2 β₀ / 2ⁱ` are
`β = 0.0817, 0.3165, 0.4774, 0.6276, 0.7726, 0.9146, 1.0545, 1.1929` for `i = 0, …, 7`.
`SU(3)`, `β₀ = floorBeta 3 = 0.17616` (the peak): `β = 0.7119, 1.0740, 1.4119, 1.7382, 2.0577, 2.3724,
2.6839` for `i = 1, …, 7`. The first octave alone (`K = 1`) asks the gap on `β ∈ [0.0817, 0.3165]`
(`SU(2)`) and `[0.1762, 0.7119]` (`SU(3)`), past the pair-route reach `0.07594`, `0.1821`.
-/

namespace MassGap.UVStepMap

open MassGap MassGap.AsymptoticScaling MassGap.PeriodicState Filter Topology

variable {N : ℕ}

/-! ## 1. The branch and the dyadic step -/

/-- **The branch past `β₀`.** Couplings `β ≥ βUV` whose spacing is at most the base spacing
`aRun N β₀`: every coupling the composition `UVIRSplit.gapAt_eventually_of_uv_ir_below` reaches.

DERIVED: no numeral. -/
def Branch (N : ℕ) (β₀ βUV β : ℝ) : Prop := βUV ≤ β ∧ aRun N β ≤ aRun N β₀

/-- **The gap at one physical rate on the branch.** `UVIRSplit.IRGapAt τ p hN β m` at every coupling
of `Branch N β₀ βUV`.

DERIVED: `4` the spacetime dimension; `0` the excluded rank. -/
def BranchGap (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₀ βUV m : ℝ) : Prop :=
  ∀ β : ℝ, Branch N β₀ βUV β → UVIRSplit.IRGapAt τ p hN β m

/-- **The step at the dyadic spacings.** For every octave `i`, every coupling `β ≥ βUV` at spacing
exactly `aRun N β₀ / 2ⁱ`, every `β' ≥ βUV` in the next octave and every rate `M ≤ M₀`: the gap at
physical rate `M` at `β` gives the gap at physical rate `M − e i` at `β'`.

DERIVED: `2` the block factor of `UVIRSplit.LossStep`; `1` the next octave; `4` the spacetime
dimension; `0` the excluded rank. -/
def DyadicStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₀ βUV M₀ : ℝ) (e : ℕ → ℝ) : Prop :=
  ∀ (i : ℕ) (β β' : ℝ), βUV ≤ β → βUV ≤ β' → aRun N β = aRun N β₀ / 2 ^ i →
    aRun N β₀ / 2 ^ (i + 1) ≤ aRun N β' → aRun N β' ≤ aRun N β₀ / 2 ^ i →
    ∀ M : ℝ, M ≤ M₀ →
      TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
      TransferGap.GapAt (periodicGaugeInvData τ p hN β') (Real.exp (-((M - e i) * aRun N β')))

/-- The dyadic spacings are distinct: `a / 2ⁱ = a / 2ʲ` at `a ≠ 0` forces `i = j`.

DERIVED: `2` the block factor; `0` the excluded spacing. -/
theorem dyadic_inj {a : ℝ} (ha : a ≠ 0) {i j : ℕ} (h : a / 2 ^ i = a / 2 ^ j) : i = j := by
  have h2i : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : (2 : ℝ) ^ i = 2 ^ j := by
    rw [div_eq_div_iff h2i h2j] at h
    exact (mul_left_cancel₀ ha h).symm
  have hn : ((2 ^ i : ℕ) : ℝ) = ((2 ^ j : ℕ) : ℝ) := by push_cast; exact hp
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective hn)

#print axioms dyadic_inj

/-- **A step from a loss at least the rate is automatic.** At `M ≤ ε` and `0 ≤ a'` the rate
`e^{−(M − ε)·a'}` is at least one, so `GapAt` holds at it on any transfer data.

DERIVED: `1` the rate at which `GapAt` is automatic; `2` its degree; `0` the sign of `a'`. -/
theorem gapAt_of_loss_ge {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    {M ε a' : ℝ} (hM : M ≤ ε) (ha' : 0 ≤ a') :
    TransferGap.GapAt D (Real.exp (-((M - ε) * a'))) := by
  apply TransferGap.gapAt_of_one_le_sq
  have hprod : (M - ε) * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ha'
  have h1 : 1 ≤ Real.exp (-((M - ε) * a')) := Real.one_le_exp (by linarith)
  nlinarith

#print axioms gapAt_of_loss_ge

/-- **`UVBelowIR` is the dyadic step.** At `1 ≤ N`, `0 < β₀` and `0 < βUV`: `UVBelowIR τ p hN β₀ βUV M₀`
holds exactly when some `e i ≥ 0` with partial sums at most `E < M₀` satisfy `DyadicStep`. Forward:
`e i = ε (aRun N β₀ / 2ⁱ)`. Backward: `ε` is `e i` at the spacing `aRun N β₀ / 2ⁱ` (`dyadic_inj`) and
`max M₀ 0` elsewhere, where the step is automatic (`gapAt_of_loss_ge`).

DERIVED: `1` the least colour count; `0` the signs of `β₀`, `βUV`, the losses; `2` the block factor;
`4` the spacetime dimension. -/
theorem uvBelowIR_iff_dyadic (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ βUV M₀ : ℝ}
    (hβ₀ : 0 < β₀) (hUV : 0 < βUV) :
    ClayRoutes.UVBelowIR τ p hN β₀ βUV M₀ ↔
      ∃ (e : ℕ → ℝ) (E : ℝ), (∀ i, 0 ≤ e i) ∧ (∀ n, ∑ i ∈ Finset.range n, e i ≤ E) ∧ E < M₀ ∧
        DyadicStep τ p hN β₀ βUV M₀ e := by
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  constructor
  · rintro ⟨ε, E, hε, hbud, hEM, hstep⟩
    refine ⟨fun i => ε (aRun N β₀ / 2 ^ i), E, fun i => hε _, hbud, hEM, ?_⟩
    intro i β β' hβ hβ' hai h1 h2 M hM hg
    have hhalf : aRun N β / 2 ≤ aRun N β' := by
      rw [hai, div_div, ← pow_succ]; exact h1
    have h := hstep β β' hβ hβ' hhalf (by rw [hai]; exact h2) M hM hg
    rw [hai] at h
    exact h
  · rintro ⟨e, E, he, hbud, hEM, hstep⟩
    classical
    let ε : ℝ → ℝ := fun s =>
      if h : ∃ i : ℕ, s = aRun N β₀ / 2 ^ i then e (Nat.find h) else max M₀ 0
    have hεd : ∀ i : ℕ, ε (aRun N β₀ / 2 ^ i) = e i := by
      intro i
      have hex : ∃ j : ℕ, aRun N β₀ / 2 ^ i = aRun N β₀ / 2 ^ j := ⟨i, rfl⟩
      simp only [ε, dif_pos hex]
      congr 1
      exact (dyadic_inj ha₀.ne' (Nat.find_spec hex)).symm
    refine ⟨ε, E, ?_, ?_, hEM, ?_⟩
    · intro s
      simp only [ε]
      split_ifs
      · exact he _
      · exact le_max_right _ _
    · intro n
      simpa only [hεd] using hbud n
    · intro β β' hβ hβ' h1 h2 M hM hg
      have ha' : 0 < aRun N β' := aRun_pos hN1 (lt_of_lt_of_le hUV hβ')
      by_cases hd : ∃ i : ℕ, aRun N β = aRun N β₀ / 2 ^ i
      · obtain ⟨i, hi⟩ := hd
        rw [hi, hεd i]
        refine hstep i β β' hβ hβ' hi ?_ (by rw [← hi]; exact h2) M hM hg
        rw [pow_succ, ← div_div, ← hi]; exact h1
      · have hεv : ε (aRun N β) = max M₀ 0 := by simp only [ε, dif_neg hd]
        rw [hεv]
        exact gapAt_of_loss_ge _ (hM.trans (le_max_left _ _)) ha'.le

#print axioms uvBelowIR_iff_dyadic

/-! ## 2. `UVBelowIR` is the gap on the branch -/

/-- **The IR gap moves to a smaller rate.** `IRGapAt τ p hN β M₀` gives `IRGapAt τ p hN β M` at
`M ≤ M₀` and `0 ≤ aRun N β` (`GapStep.gapAt_mono`).

DERIVED: `0` the sign of the spacing; `4` the spacetime dimension. -/
theorem irGapAt_mono (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β M M₀ : ℝ} (hM : M ≤ M₀)
    (ha : 0 ≤ aRun N β) (h : UVIRSplit.IRGapAt τ p hN β M₀) : UVIRSplit.IRGapAt τ p hN β M := by
  unfold UVIRSplit.IRGapAt at *
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ h
  rw [Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_right hM ha]

#print axioms irGapAt_mono

/-- **`UVBelowIR` with the IR gap gives the gap on the whole branch.** At `1 ≤ N`, `0 < βUV ≤ β₀`:
`UVBelowIR τ p hN β₀ βUV M₀` and `IRGapAt τ p hN β₀ M₀` give some `m ∈ (0, M₀]` with
`BranchGap τ p hN β₀ βUV m`, `m = M₀ − E`. The proof is the composition of
`UVIRSplit.gapAt_eventually_of_uv_ir_below` run at a given branch coupling in place of a large one:
dyadic couplings `γ i ≥ β₀` (`AsymptoticScaling.exists_beta_aRun_eq`), the octave `n` of `β`
(`Nat.find`), the chain `γ 0 → … → γ n` (`UVIRSplit.gapAt_chain_below`) and the last step `γ n → β`.

DERIVED: `1` the least colour count; `0` the signs; `2` the block factor; `4` the spacetime dimension. -/
theorem gapAt_branch_of_uvBelowIR (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {β₀ βUV M₀ : ℝ} (hUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀)
    (huv : ClayRoutes.UVBelowIR τ p hN β₀ βUV M₀) (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) :
    ∃ m : ℝ, 0 < m ∧ m ≤ M₀ ∧ BranchGap τ p hN β₀ βUV m := by
  obtain ⟨ε, E, hε, hbudget, hEM, hstepB⟩ := huv
  have hβ₀ : 0 < β₀ := lt_of_lt_of_le hUV hUVβ₀
  have hE0 : 0 ≤ E := by simpa using hbudget 0
  refine ⟨M₀ - E, by linarith, by linarith, ?_⟩
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  have hgex : ∀ i : ℕ, ∃ g : ℝ, β₀ ≤ g ∧ aRun N g = aRun N β₀ / 2 ^ (i + 1) := by
    intro i
    have hlt : aRun N β₀ / 2 ^ (i + 1) < aRun N β₀ :=
      div_lt_self ha₀ (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i))
    exact exists_beta_aRun_eq hN1 (div_pos ha₀ (by positivity)) hlt
  choose g hgβ hg using hgex
  obtain ⟨γ, hγ0, hγβ, hγ⟩ : ∃ γ : ℕ → ℝ, γ 0 = β₀ ∧ (∀ i : ℕ, β₀ ≤ γ i) ∧
      ∀ i : ℕ, aRun N (γ i) = aRun N β₀ / 2 ^ i :=
    ⟨(fun i => match i with | 0 => β₀ | k + 1 => g k),
     rfl,
     fun i => by
      cases i with
      | zero => exact le_rfl
      | succ k => exact hgβ k,
     fun i => by
      cases i with
      | zero =>
        show aRun N β₀ = aRun N β₀ / 2 ^ 0
        rw [pow_zero, div_one]
      | succ k =>
        show aRun N (g k) = aRun N β₀ / 2 ^ (k + 1)
        exact hg k⟩
  have hstep : ∀ j : ℕ, ∀ M : ℝ, M ≤ M₀ →
      TransferGap.GapAt (periodicGaugeInvData τ p hN (γ j)) (Real.exp (-(M * aRun N (γ j)))) →
      TransferGap.GapAt (periodicGaugeInvData τ p hN (γ (j + 1)))
        (Real.exp (-((M - ε (aRun N β₀ / 2 ^ j)) * aRun N (γ (j + 1))))) := by
    intro j M hM hgj
    have h := hstepB (γ j) (γ (j + 1)) (hUVβ₀.trans (hγβ j)) (hUVβ₀.trans (hγβ (j + 1)))
      (le_of_eq (by rw [hγ j, hγ (j + 1), pow_succ, div_div]))
      (by
        rw [hγ j, hγ (j + 1), pow_succ, ← div_div]
        have hnn : 0 ≤ aRun N β₀ / 2 ^ j := div_nonneg ha₀.le (by positivity)
        linarith)
      M hM hgj
    rw [hγ j] at h
    exact h
  have hbase0 : TransferGap.GapAt (periodicGaugeInvData τ p hN (γ 0))
      (Real.exp (-(M₀ * aRun N (γ 0)))) := by
    rw [hγ0]
    exact hir
  intro β ⟨hβUV, hβa⟩
  have ha : 0 < aRun N β := aRun_pos hN1 (lt_of_lt_of_le hUV hβUV)
  have hex : ∃ n : ℕ, aRun N β₀ / 2 ^ (n + 1) < aRun N β := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (aRun N β₀ / aRun N β) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1)), pow_succ]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [hn, mul_pos h2n ha]
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, aRun N β₀ / 2 ^ (n + 1) < aRun N β ∧
      ∀ k : ℕ, k < n → ¬ (aRun N β₀ / 2 ^ (k + 1) < aRun N β) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hle : aRun N β ≤ aRun N β₀ / 2 ^ n := by
    cases n with
    | zero =>
      rw [pow_zero, div_one]
      exact hβa
    | succ k => exact not_lt.mp (hmin k (Nat.lt_succ_self k))
  have hchain : TransferGap.GapAt (periodicGaugeInvData τ p hN (γ n))
      (Real.exp (-((M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i)) * aRun N (γ n)))) :=
    UVIRSplit.gapAt_chain_below (fun i => periodicGaugeInvData τ p hN (γ i))
      (fun i => aRun N (γ i)) (fun i => ε (aRun N β₀ / 2 ^ i)) M₀ n (fun i => hε _) hbase0
      (fun j _ M hM hgj => hstep j M hM hgj) n le_rfl
  have hlast := hstepB (γ n) β (hUVβ₀.trans (hγβ n)) hβUV
    (by
      rw [hγ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hγ n]
      exact hle)
    (M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i))
    (sub_le_self _ (Finset.sum_nonneg (fun i _ => hε _))) hchain
  rw [hγ n] at hlast
  have hS : ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i) + ε (aRun N β₀ / 2 ^ n) ≤ E := by
    have hb := hbudget (n + 1)
    rw [Finset.sum_range_succ] at hb
    exact hb
  have hmono : Real.exp (-((M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i)
        - ε (aRun N β₀ / 2 ^ n)) * aRun N β))
      ≤ Real.exp (-((M₀ - E) * aRun N β)) := by
    rw [Real.exp_le_exp]
    have hm := mul_le_mul_of_nonneg_right
      (show M₀ - E ≤ M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i)
        - ε (aRun N β₀ / 2 ^ n) by linarith) ha.le
    linarith
  exact GapStep.gapAt_mono _ (Real.exp_pos _).le hmono hlast

#print axioms gapAt_branch_of_uvBelowIR

/-- **The gap on the branch gives `UVBelowIR`.** At `1 ≤ N`, `0 < βUV`, `0 < M ≤ m`: `BranchGap τ p hN β₀
βUV m` gives `UVBelowIR τ p hN β₀ βUV M` with `ε = 0` at spacings up to `aRun N β₀` and `ε = M` above
(where the step is automatic, `gapAt_of_loss_ge`), budget `E = 0`. A target `β'` on the branch carries
the rate `m ≥ M` itself; a target off the branch has a source off it too, at loss `M`.

DERIVED: `1` the least colour count; `0` the signs, the loss on the branch and the budget, and the floor
of the threshold `max (aRun N β₀) 0`; `4` the spacetime dimension. -/
theorem uvBelowIR_of_branchGap (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {β₀ βUV m M : ℝ} (hUV : 0 < βUV) (hM : 0 < M) (hMm : M ≤ m)
    (hgap : BranchGap τ p hN β₀ βUV m) : ClayRoutes.UVBelowIR τ p hN β₀ βUV M := by
  classical
  refine ⟨fun s => if s ≤ max (aRun N β₀) 0 then 0 else M, 0, ?_, ?_, hM, ?_⟩
  · intro s
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hM.le
  · intro n
    have h : ∀ i ∈ Finset.range n,
        (fun s => if s ≤ max (aRun N β₀) 0 then (0 : ℝ) else M) (aRun N β₀ / 2 ^ i) = 0 := by
      intro i _
      have hle : aRun N β₀ / 2 ^ i ≤ max (aRun N β₀) 0 := by
        rcases le_or_gt 0 (aRun N β₀) with h0 | h0
        · exact (div_le_self h0 (one_le_pow₀ (by norm_num))).trans (le_max_left _ _)
        · exact (div_nonpos_of_nonpos_of_nonneg h0.le (by positivity)).trans (le_max_right _ _)
      simp only [if_pos hle]
    rw [Finset.sum_eq_zero h]
  · intro β β' hβ hβ' _ h2 M' hM' _
    have ha' : 0 < aRun N β' := aRun_pos hN1 (lt_of_lt_of_le hUV hβ')
    by_cases hb' : aRun N β' ≤ aRun N β₀
    · have hg := hgap β' ⟨hβ', hb'⟩
      unfold UVIRSplit.IRGapAt at hg
      refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ hg
      rw [Real.exp_le_exp]
      have hε0 : 0 ≤ (fun s => if s ≤ max (aRun N β₀) 0 then (0 : ℝ) else M) (aRun N β) := by
        simp only; split_ifs <;> linarith
      nlinarith [mul_le_mul_of_nonneg_right
        (show M' - (fun s => if s ≤ max (aRun N β₀) 0 then (0 : ℝ) else M) (aRun N β) ≤ m by linarith) ha'.le]
    · have hb : ¬ aRun N β ≤ max (aRun N β₀) 0 := fun h =>
        (le_max_iff.mp (h2.trans h)).elim hb' (fun h3 => absurd h3 (not_le.mpr ha'))
      simp only [if_neg hb]
      exact gapAt_of_loss_ge _ hM' ha'.le

#print axioms uvBelowIR_of_branchGap

/-- **`UVBelowIR` at some rate is the gap on the branch.** At `1 ≤ N`, `0 < βUV ≤ β₀`, `0 < M₀` and the
IR gap `IRGapAt τ p hN β₀ M₀`: `UVBelowIR τ p hN β₀ βUV M` at some `M ∈ (0, M₀]` holds exactly when
`BranchGap τ p hN β₀ βUV m` holds at some `m > 0` (`gapAt_branch_of_uvBelowIR`, `irGapAt_mono`,
`uvBelowIR_of_branchGap` at `M = min m M₀`).

DERIVED: `1` the least colour count; `0` the signs; `4` the spacetime dimension. -/
theorem exists_uvBelowIR_iff_branchGap (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {β₀ βUV M₀ : ℝ} (hUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀) (hM₀ : 0 < M₀)
    (hir : UVIRSplit.IRGapAt τ p hN β₀ M₀) :
    (∃ M : ℝ, 0 < M ∧ M ≤ M₀ ∧ ClayRoutes.UVBelowIR τ p hN β₀ βUV M) ↔
      ∃ m : ℝ, 0 < m ∧ BranchGap τ p hN β₀ βUV m := by
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 (lt_of_lt_of_le hUV hUVβ₀)
  constructor
  · rintro ⟨M, hM, hMM₀, huv⟩
    obtain ⟨m, hm, _, hg⟩ := gapAt_branch_of_uvBelowIR τ p hN1 hN hUV hUVβ₀ huv
      (irGapAt_mono τ p hN hMM₀ ha₀.le hir)
    exact ⟨m, hm, hg⟩
  · rintro ⟨m, hm, hg⟩
    exact ⟨min m M₀, lt_min hm hM₀, min_le_right _ _,
      uvBelowIR_of_branchGap τ p hN1 hN hUV (lt_min hm hM₀) (min_le_left _ _) hg⟩

#print axioms exists_uvBelowIR_iff_branchGap

/-! ## 3. The finite + tail split -/

/-- **Finite octaves and a tail.** At `1 ≤ N`, `0 < βUV`, `0 < m₁`, `0 < m₂`, `0 < M₀` and any `K`: the
gap at rate `m₁` on the first `K` octaves of the branch (`aRun N β₀ / 2ᴷ ≤ aRun N β`) and at rate `m₂` on
the tail (`aRun N β < aRun N β₀ / 2ᴷ`) give `UVBelowIR τ p hN β₀ βUV (min (min m₁ m₂) M₀)`.

DERIVED: `2` the block factor; `1` the least colour count; `0` the signs; `4` the spacetime dimension.
CHOSEN: none; `K` is the caller's. -/
theorem uvBelowIR_of_split (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {β₀ βUV m₁ m₂ M₀ : ℝ} (K : ℕ) (hUV : 0 < βUV) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hM₀ : 0 < M₀)
    (hfin : ∀ β : ℝ, Branch N β₀ βUV β → aRun N β₀ / 2 ^ K ≤ aRun N β →
      UVIRSplit.IRGapAt τ p hN β m₁)
    (htail : ∀ β : ℝ, Branch N β₀ βUV β → aRun N β < aRun N β₀ / 2 ^ K →
      UVIRSplit.IRGapAt τ p hN β m₂) :
    ClayRoutes.UVBelowIR τ p hN β₀ βUV (min (min m₁ m₂) M₀) := by
  refine uvBelowIR_of_branchGap τ p hN1 hN hUV (lt_min (lt_min hm₁ hm₂) hM₀) (min_le_left _ _) ?_
  intro β hβ
  have ha : 0 ≤ aRun N β := (aRun_pos hN1 (lt_of_lt_of_le hUV hβ.1)).le
  rcases le_or_gt (aRun N β₀ / 2 ^ K) (aRun N β) with h | h
  · exact irGapAt_mono τ p hN (min_le_left _ _) ha (hfin β hβ h)
  · exact irGapAt_mono τ p hN (min_le_right _ _) ha (htail β hβ h)

#print axioms uvBelowIR_of_split

/-! ## 4. The window read: a seed of bounded physical size -/

/-- **A seed window of bounded physical size on the branch.** At every branch coupling some window
`2^w`, `w ≥ 1`, is in the basin of `DoublingSharp` (`windowCoupling N β w ≤ 1/1000`) and spans at most
`C` in units of the spacing, `2^w · aRun N β ≤ C`.

DERIVED: `1/1000` the seed of `DoublingSharp`; `1` the least window index; `2` the doubling. -/
def BoundedSeed (N : ℕ) (β₀ βUV C : ℝ) : Prop :=
  ∀ β : ℝ, Branch N β₀ βUV β →
    ∃ w : ℕ, 1 ≤ w ∧ CouplingTower.windowCoupling N β w ≤ 1 / 1000 ∧ (2 : ℝ) ^ w * aRun N β ≤ C

/-- **A bounded seed gives the branch gap at rate `log 2 / C`.** At `2 ≤ N`, `0 ≤ βUV`, `0 < C`:
`CouplingTower.windowGap` gives the gap at the lattice rate `r` with `−log r = log 2 / 2^w`, and
`2^w · aRun N β ≤ C` moves it to `e^{−(log 2 / C)·aRun N β}`.

DERIVED: `2` the least rank and the doubling; `log 2` the window gap of `windowGap`; `0` the plane,
the time axis and the signs. -/
theorem branchGap_of_boundedSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) {β₀ βUV C : ℝ} (hUV : 0 ≤ βUV)
    (hC : 0 < C) (hs : BoundedSeed N β₀ βUV C) :
    BranchGap 0 0 hN β₀ βUV (Real.log 2 / C) := by
  intro β hβ
  obtain ⟨w, hw, hseed, hsize⟩ := hs β hβ
  obtain ⟨r, hr0, _, hg, _, hlog⟩ :=
    CouplingTower.windowGap hN2 hN (hUV.trans hβ.1) hw hseed
  unfold UVIRSplit.IRGapAt
  refine GapStep.gapAt_mono _ hr0.le ?_ hg
  have hr : r = Real.exp (-(Real.log 2 / 2 ^ w)) := by
    rw [← hlog, neg_neg, Real.exp_log hr0]
  rw [hr, Real.exp_le_exp, neg_le_neg_iff]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2w : (0 : ℝ) < 2 ^ w := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hC h2w]
  nlinarith [mul_le_mul_of_nonneg_left hsize hl2.le]

#print axioms branchGap_of_boundedSeed

/-- **A bounded seed gives `StrongEnd`.** At `1 ≤ N`, `0 < β₀`, `0 ≤ βUV`: every large `β` is on the
branch (`WeakCouplingWindow.eventually_aRun_le`), its seed window makes the window coupling vanish
(`CouplingTower.tendsto_zero_of_seed`), so the vanishing holds eventually, hence frequently.

DERIVED: `1` the least colour count; `0` the signs and the limit. -/
theorem strongEnd_of_boundedSeed (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ βUV C : ℝ} (hβ₀ : 0 < β₀)
    (hUV : 0 ≤ βUV) (hs : BoundedSeed N β₀ βUV C) : CouplingTower.StrongEnd N := by
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  refine Filter.Eventually.frequently ?_
  filter_upwards [WeakCouplingWindow.eventually_aRun_le hN1 ha₀, Filter.eventually_ge_atTop βUV]
    with β hβa hβUV
  obtain ⟨w, hw, hseed, _⟩ := hs β ⟨hβUV, hβa⟩
  exact CouplingTower.tendsto_zero_of_seed hN (hUV.trans hβUV) hw hseed

#print axioms strongEnd_of_boundedSeed

/-! ## 5. The continuum statement from the branch gap -/

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the branch gap.** At `2 ≤ N`, `0 < L`, `0 < βUV ≤ β₀`, the
gap at one physical rate `m > 0` on the branch (which contains `β₀`), and E, N, Y:
`ClayRoutes.ClayContinuum` (`RestoreShimsClay.clay_continuum_of_irGap` at `M₀ = m`,
`uvBelowIR_of_branchGap`).

DERIVED: `2` the least rank with a non-zero Haar variance; `0` the reflection plane and the signs; `4`
the spacetime dimension. -/
theorem clay_of_branchGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV m : ℝ} (hUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀) (hm : 0 < m)
    (hgap : BranchGap τ 0 hN β₀ βUV m)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_irGap hN2 hN Z τ hZ hB hL (lt_of_lt_of_le hUV hUVβ₀) hUVβ₀
    (hgap β₀ ⟨hUVβ₀, le_rfl⟩)
    (uvBelowIR_of_branchGap τ 0 (by omega) hN hUV hm le_rfl hgap) O G hconv hY

#print axioms clay_of_branchGap

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from a bounded seed.** At `2 ≤ N`, `0 < L`, `0 < βUV ≤ β₀`, `0 < C`,
`BoundedSeed N β₀ βUV C` and E, N, Y at the plane `τ = 0`: `ClayRoutes.ClayContinuum`
(`branchGap_of_boundedSeed`, `clay_of_branchGap`).

DERIVED: `2` the least rank; `0` the reflection plane, the time axis and the signs; `4` the spacetime
dimension. -/
theorem clay_of_boundedSeed (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV C : ℝ} (hUV : 0 < βUV) (hUVβ₀ : βUV ≤ β₀) (hC : 0 < C)
    (hs : BoundedSeed N β₀ βUV C)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) 0 O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z 0 hZ hB L :=
  clay_of_branchGap hN2 hN Z 0 hZ hB hL hUV hUVβ₀
    (div_pos (Real.log_pos (by norm_num)) hC)
    (branchGap_of_boundedSeed hN2 hN hUV.le hC hs) O G hconv hY

#print axioms clay_of_boundedSeed

end MassGap.UVStepMap
