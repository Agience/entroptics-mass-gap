import Mathlib
import MassGap.WeakCouplingWindow
import MassGap.PeriodicStrongCoupling

/-!
# MassGap.UVIRSplit — the uniform physical gap from a lossy block step and a gap at one coupling

## What it gives

The M core's open input is `WeakCouplingWindow.FixedWindowDecay τ p hN L`, the uniform physical gap
at the periodic state (`WeakCouplingWindow.fixedWindowDecay_iff`). This module splits it into an
ultraviolet input, a block step between two couplings that loses at most a summable amount of
physical rate, and an infrared input, the gap at one coupling, and proves the composition.

1. `LossStep D a βUV ε`: on any family of transfer data, the gap at physical rate `M` at `β` gives
   the gap at physical rate `M − ε(a β)` at every `β'` one block step finer
   (`a β / 2 ≤ a β' ≤ a β`). `LossBudget ε a₀ E`: the losses of the dyadic tower below `a₀` sum to at
   most `E`. `VanishingLoss ε`: that budget tends to zero with `a₀`. `gapAt_chain`: a base gap and
   `K` lossy steps give the gap at the base rate less the summed losses.
2. `UVLossStep τ p hN βUV ε` is `LossStep` at `periodicGaugeInvData τ p hN` and the two-loop spacing
   `aRun N`; `UVInput τ p hN` adds `VanishingLoss`. `IRGapAt τ p hN β₀ M₀` is `GapAt` at
   `e^{−M₀·aRun N β₀}` at the one coupling `β₀`. `uvLossStep_iff_lag`, `uvLossStep_iff_long_lag`: the
   step is one lag bound at the finer coupling, at a lag of any physical length `ℓ`.
   `physStep_of_uvLossStep`: at zero loss the step is `GapStep.PhysStep`.
3. `gapAt_eventually_of_uv_ir`, `fixedWindowDecay_of_uv_ir`: `UVLossStep` from `βUV`, the IR gap at
   `β₀ ≥ βUV` at physical rate `M₀`, and a loss budget `E < M₀` below `aRun N β₀` give `GapAt` at
   physical rate `M₀ − E` at every large `β`, hence `FixedWindowDecay` at every window `L > 0`. The
   proof reaches every large `β` by `n` exact halvings from `β₀` and one last partial step, `n`
   depending on `β` and unbounded, and pays the loss of each.
4. `irGapAt_of_fixedWindowDecay`: `FixedWindowDecay` gives `IRGapAt` at every large `β₀`, at one
   rate `M > 0`. `fixedWindowDecay_iff_irGapAt`, `fixedWindowDecay_iff_of_uvInput`: under the UV
   input with vanishing losses, `FixedWindowDecay τ p hN L` holds exactly when `IRGapAt` holds at one
   coupling `β₀ ≥ βUV` at a rate above the loss budget below `aRun N β₀`.
5. `irGapAt_of_strong_coupling_chain`, `fixedWindowDecay_of_base_crossover_uv`: the proved
   strong-coupling base (`PeriodicStrongCoupling.periodic_tower_base`) and `K` lossy crossover steps,
   `K` finite, give `IRGapAt` at the end of the crossover, and with the UV step `FixedWindowDecay`.
6. `lossStep_without_gap`, `vanishingLoss_zero`: the UV shape, with zero loss, holds on a family with
   no gap at any coupling (`TransferGap.diagTransfer 1`, identity step), so the gap the composition
   returns comes from `IRGapAt`. `lossStep_not_automatic`: a family on which `LossStep` fails at every
   loss below `log 2`, so `LossStep` is a constraint.

## The literature, and which input it addresses

Balaban's four-dimensional programme: T. Balaban, Commun. Math. Phys. 95 (1984) 17–40; 96 (1984)
223–250; 98 (1985) 17–51; 99 (1985) 75–102 and 389–434; 102 (1985) 277–309; "Renormalization group
approach to lattice gauge field theories I", 109 (1987) 249–301; "… II. Cluster expansions", 116
(1988) 1–22; "Convergent renormalization expansions for lattice gauge theories", 119 (1988)
243–285; "Large field renormalization I, II", 122 (1989) 175–202 and 355–392. What it proves: for
the Wilson-action lattice gauge theory on a periodic lattice `T_η` of spacing `η`, with the bare
density `exp[−(1/g₀²)A − E]` (`E` a vacuum-energy normalisation), the effective densities `ρ_k`
after `k` block-spin steps with a fixed large block factor `L`, down to the unit lattice, keep their
inductive form and satisfy
`χ_k exp[−(1/g_k²)A(U_k) − E₋|T_η|] ≤ ρ_k ≤ exp(E₊|T_η|)` with `E₋, E₊` independent of `k`, of the
torus and of the configuration (CMP 122 (1989) 355, (0.1); CMP 119 (1988), Corollary 3,
"Ultraviolet Stability"), provided every running coupling `g_k` stays in `]0, γ]` for a small `γ`
(CMP 122 (1989) 355, Theorem 1; the removal of that proviso rests on a second-order perturbative
theorem of CMP 109 whose proof Balaban states is unpublished). The bounds are extensive in the torus
volume. Not proved: a limit, or a subsequential limit, of any correlation or Wilson-loop expectation
(Balaban, CMP 122 (1989) 356, defers "expectation values of physical observables" to further work);
the infinite-volume limit; clustering or a gap at weak coupling.

J. Magnen, V. Rivasseau, R. Sénéor, "Construction of YM4 with an infrared cutoff", Commun. Math. Phys.
155 (1993) 325–383: for `SU(2)`, trivial topological sector, a continuum momentum cutoff of a
stabilising shape with gauge-restoring counterterms, a regularised axial gauge at large fields and a
background-dependent covariant gauge at small fields, a fixed infrared cutoff (zero mode deleted; a
finite torus or an infrared propagator cutoff) and a coupling small at the cutoff scale: the
ultraviolet limit of the gauge-fixed Schwinger functions of the connection exists and satisfies the
Slavnov identities. The authors state that the paper gives the elements of the proof and not every
detail; the Schwinger functions are not Euclidean invariant; the infrared cutoff is not removed; the
Osterwalder–Schrader axioms, gauge-invariant composite observables, infinite volume and a gap are not
treated.

Strong coupling: K. Osterwalder, E. Seiler, "Gauge field theories on a lattice", Ann. Phys. 110
(1978) 440–471 — the infinite-volume limit and clustering at small `β` at fixed spacing, which the
tree carries as `PeriodicStrongCoupling.periodic_tower_base`.

Which input is which. Neither input is a published theorem. `UVLossStep` is the block step stated on
the infinite-volume transfer gap, the correlation-level consequence a block-spin analysis would have
to deliver between spacings `a` and `a/2`; Balaban's theorem bounds the effective densities of such
block steps in a finite torus and supplies no correlation bound, no infinite volume and no statement
about a gap.
`IRGapAt` is the gap of the lattice theory in infinite volume at one coupling `β₀`, in units of
`aRun N β₀`. At strong coupling it is proved: `irGapAt_of_strong_coupling_chain` at `K = 0` gives it at
every `β₀ ∈ (0, βsc)` at every `M₀ ≤ −log(coreRate (16 * 4) β₀) / aRun N β₀`, a rate unbounded as
`β₀ → 0`, where `coreRate` and `aRun N` both tend to zero. So `IRGapAt` carries content only at a
coupling past the strong-coupling region: at `βUV ≤ β₀ < βsc` with a loss budget below that rate,
`fixedWindowDecay_of_base_crossover_uv` at `K = 0` gives `FixedWindowDecay` from `UVLossStep` alone, and
the open content is the UV step across the crossover. A gap at any single coupling outside the
strong-coupling region is open for non-abelian four-dimensional lattice gauge theory.

## Scope

`UVLossStep`, `IRGapAt`, `LossBudget`, `VanishingLoss` and the crossover steps are hypotheses of
every forward theorem here. `FixedWindowDecay` implies `IRGapAt` at every large `β₀` at one rate
`M > 0` (`irGapAt_of_fixedWindowDecay`); the converse takes `UVLossStep`. `UVLossStep` alone
constrains little: where the physical rates attainable at a spacing `a` are bounded by `B(a)`, it
holds with `ε(a) = B(a)`, every conclusion then being a rate at least one. Its content is carried
together with `VanishingLoss` or a budget `E` below the IR rate, which every forward theorem takes.
The block factor is `2`, the halving of `GapStep.PhysStep`, where Balaban's block factor `L` is a
large integer; the composition's argument runs with `L`-adic spacings in place of dyadic ones, which
this module does not state. `aRun N` rises on `(0, 17N²/(88π²)]` and falls past it
(`AsymptoticScaling.aRun`); the tree proves neither monotonicity, so `LossStep` compares any two couplings
above `βUV` with spacings one step apart, in either order of coupling, and at `βUV` below the peak it
pairs a strong coupling with a weak one of the same spacing. `ε` carries no sign condition: at `M = 0`
the hypothesis is automatic, so a negative loss at an admissible `β` asserts a gap at `β'` outright.
-/

namespace MassGap.UVIRSplit

open MassGap MassGap.AsymptoticScaling MassGap.PeriodicState

/-! ## 1. Lossy steps on transfer data -/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **A block step with a loss.** For a family of transfer data `D β` on one module, a spacing
function `a`, a threshold `βUV` and a loss function `ε` of the coarse spacing: for every two
couplings `β, β' ≥ βUV` whose spacings satisfy `a β / 2 ≤ a β' ≤ a β` (one block step, the finer
spacing at least half the coarser), and every `M`, the gap at rate `e^{−M·a β}` at `β` gives the gap at
rate `e^{−(M − ε(a β))·a β'}` at `β'`: the physical rate `M` at `β` survives at `β'` less `ε(a β)`.

DERIVED: `2` is the halving of `GapStep.physStep_iff_lag`, the block factor of the tree's tower.
CHOSEN: the step is asked at every spacing ratio in `[1/2, 1]`, not only at `1/2`, so that a tower
from one coupling reaches every finer spacing; any fixed block factor `b > 1` in place of `2` serves. -/
def LossStep (D : ℝ → Transfer.TransferData A) (a : ℝ → ℝ) (βUV : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → a β / 2 ≤ a β' → a β' ≤ a β →
    ∀ M : ℝ, TransferGap.GapAt (D β) (Real.exp (-(M * a β))) →
      TransferGap.GapAt (D β') (Real.exp (-((M - ε (a β)) * a β')))

/-- **The loss budget from a spacing.** The losses `ε` at the dyadic spacings `a₀, a₀/2, a₀/4, …` sum,
over every initial segment, to at most `E`.

DERIVED: `2` is `LossStep`'s block factor. -/
def LossBudget (ε : ℝ → ℝ) (a₀ E : ℝ) : Prop :=
  ∀ n : ℕ, ∑ i ∈ Finset.range n, ε (a₀ / 2 ^ i) ≤ E

/-- **The losses vanish in the continuum.** For every `δ > 0` there is `a₁ > 0` such that every spacing
`0 < a ≤ a₁` has loss budget `δ`: the total loss of the dyadic tower below `a` tends to zero with `a`.

DERIVED: `0` is the sign of `δ`, `a₁` and `a`. -/
def VanishingLoss (ε : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ a₁ : ℝ, 0 < a₁ ∧ ∀ a : ℝ, 0 < a → a ≤ a₁ → LossBudget ε a δ

/-- **The chain of lossy steps.** For transfer data `D j` on one module, spacings `a j`, losses `e j`
and a finite length `K`: the gap at rate `e^{−M₀·a 0}` at `j = 0` and, at every `j < K` and every `M`,
the step from the gap at rate `e^{−M·a j}` at `j` to the gap at rate `e^{−(M − e j)·a (j+1)}` at
`j + 1`, give at every `j ≤ K` the gap at rate `e^{−(M₀ − Σ_{i<j} e i)·a j}`. Induction on `j`
(`Finset.sum_range_succ`, `sub_sub`).

DERIVED: `0` is the base index; `1` is the step to the next index. -/
theorem gapAt_chain (D : ℕ → Transfer.TransferData A) (a e : ℕ → ℝ) (M₀ : ℝ) (K : ℕ)
    (hbase : TransferGap.GapAt (D 0) (Real.exp (-(M₀ * a 0))))
    (hstep : ∀ j : ℕ, j < K → ∀ M : ℝ, TransferGap.GapAt (D j) (Real.exp (-(M * a j))) →
      TransferGap.GapAt (D (j + 1)) (Real.exp (-((M - e j) * a (j + 1))))) :
    ∀ j : ℕ, j ≤ K →
      TransferGap.GapAt (D j) (Real.exp (-((M₀ - ∑ i ∈ Finset.range j, e i) * a j))) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Finset.sum_range_zero, sub_zero]
    exact hbase
  | succ j ih =>
    intro hj
    have h := hstep j (by omega) _ (ih (by omega))
    rw [Finset.sum_range_succ, ← sub_sub]
    exact h

#print axioms gapAt_chain

/-- **A step out of a gapless coupling holds with any non-negative loss.** If no `D β` with
`β ≥ βUV` has `GapAt` at any rate `r` with `r² < 1`, the spacing is positive above `βUV`, and
`ε ≥ 0`, then `LossStep D a βUV ε`. At `M > 0` the hypothesis `GapAt (D β) (e^{−M·a β})` is a gap
below one and does not hold; at `M ≤ 0` the conclusion's rate `e^{−(M − ε)·a β'}` is at least one and
`TransferGap.gapAt_of_one_le_sq` gives it.

DERIVED: `2` is `GapAt`'s degree, the square of the rate; `1` is the rate at which `GapAt` is
automatic; `0` is the sign of `ε` and of the spacing. -/
theorem lossStep_of_no_gap (D : ℝ → Transfer.TransferData A) (a : ℝ → ℝ) (βUV : ℝ) (ε : ℝ → ℝ)
    (hε : ∀ s : ℝ, 0 ≤ ε s) (ha : ∀ β : ℝ, βUV ≤ β → 0 < a β)
    (hno : ∀ β : ℝ, βUV ≤ β → ∀ r : ℝ, r ^ 2 < 1 → ¬ TransferGap.GapAt (D β) r) :
    LossStep D a βUV ε := by
  intro β β' hβ hβ' _ _ M hg
  by_cases hM : 0 < M
  · have hpos : 0 < M * a β := mul_pos hM (ha β hβ)
    have h1 : Real.exp (-(M * a β)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h0 : 0 < Real.exp (-(M * a β)) := Real.exp_pos _
    have hr2 : Real.exp (-(M * a β)) ^ 2 < 1 := by nlinarith
    exact (hno β hβ (Real.exp (-(M * a β))) hr2 hg).elim
  · have hM' : M ≤ 0 := not_lt.mp hM
    apply TransferGap.gapAt_of_one_le_sq
    have hprod : (M - ε (a β)) * a β' ≤ 0 := by
      nlinarith [hε (a β), ha β' hβ']
    have h1 : 1 ≤ Real.exp (-((M - ε (a β)) * a β')) := Real.one_le_exp (by linarith)
    nlinarith

#print axioms lossStep_of_no_gap

/-- **A step that loses the gap is excluded.** If `GapAt (D β) (e^{−M·a β})` holds with `ε(a β) < M`,
`0 < a β'`, the two couplings are admissible for one block step, and `D β'` has no `GapAt` at any
rate `r` with `r² < 1`, then `LossStep D a βUV ε` fails: the step would put a gap at the rate
`e^{−(M − ε(a β))·a β'} < 1` at `β'`.

DERIVED: `2` is `LossStep`'s block factor and `GapAt`'s degree; `1` is the rate at which `GapAt` is
automatic; `0` is the sign of the spacing. -/
theorem not_lossStep_of_gap_lost (D : ℝ → Transfer.TransferData A) (a : ℝ → ℝ) (βUV : ℝ)
    (ε : ℝ → ℝ) {β β' M : ℝ} (hβ : βUV ≤ β) (hβ' : βUV ≤ β') (h1 : a β / 2 ≤ a β')
    (h2 : a β' ≤ a β) (hg : TransferGap.GapAt (D β) (Real.exp (-(M * a β))))
    (hM : ε (a β) < M) (ha' : 0 < a β')
    (hno : ∀ r : ℝ, r ^ 2 < 1 → ¬ TransferGap.GapAt (D β') r) :
    ¬ LossStep D a βUV ε := by
  intro hstep
  have h := hstep β β' hβ hβ' h1 h2 M hg
  have hpos : 0 < (M - ε (a β)) * a β' := mul_pos (by linarith) ha'
  have e1 : Real.exp (-((M - ε (a β)) * a β')) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e0 : 0 < Real.exp (-((M - ε (a β)) * a β')) := Real.exp_pos _
  exact hno _ (by nlinarith) h

#print axioms not_lossStep_of_gap_lost

end Abstract

/-! ## 2. Two-dimensional witnesses -/

section Witness

/-- **The two-dimensional model has no gap below its own rate.** `TransferGap.diagTransfer lam`
fixes the vacuum coordinate and scales the other by `lam`; at every `r` with `r² < lam²` it has no
`GapAt` at `r`: the vector `(0, 1)` is orthogonal to the vacuum, of form `1`, and its image has form
`lam²`.

DERIVED: `2` is `GapAt`'s degree and the form's; `1` is the contractivity bound `diagTransfer` takes. -/
theorem diag_no_gap_of_lt (lam : ℝ) (hlam : lam ^ 2 ≤ 1) (r : ℝ) (hr : r ^ 2 < lam ^ 2) :
    ¬ TransferGap.GapAt (TransferGap.diagTransfer lam hlam) r := by
  intro hg
  have hvac : (TransferGap.diagTransfer lam hlam).form (fun i => if i = 0 then (0 : ℝ) else 1)
      (TransferGap.diagTransfer lam hlam).vac = 0 := by
    simp only [TransferGap.diagTransfer]
    norm_num
  have h := hg _ hvac
  simp only [TransferGap.diagTransfer, TransferGap.diagStep, LinearMap.coe_mk,
    AddHom.coe_mk] at h
  norm_num at h
  nlinarith [h, sq_abs r, sq_abs lam, abs_nonneg r, abs_nonneg lam]

#print axioms diag_no_gap_of_lt

/-- **The block step is not automatic.** There is a family `D` of two-dimensional transfer data such
that, at spacing `1` and threshold `0`, every loss function with `ε 1 < log 2` fails `LossStep`:
`D 0` has the gap at rate `1/2 = e^{−log 2·1}` and `D 1` has no gap below one
(`not_lossStep_of_gap_lost`).

DERIVED: `2` in `Fin 2` is the model's dimension; `log 2` is `−log` of the rate `1/2` at spacing `1`.
CHOSEN: the rates `1/2` below the coupling `1` and `1` from it on, the constant spacing `1` and the
threshold `0`; any rate in `[0, 1)` below and `1` above serve. -/
theorem lossStep_not_automatic :
    ∃ D : ℝ → Transfer.TransferData (Fin 2 → ℝ), ∀ ε : ℝ → ℝ, ε 1 < Real.log 2 →
      ¬ LossStep D (fun _ => 1) 0 ε := by
  refine ⟨fun β => TransferGap.diagTransfer (if β < 1 then 1 / 2 else 1)
    (by split_ifs <;> norm_num), fun ε hε => ?_⟩
  have hbase : TransferGap.GapAt
      (TransferGap.diagTransfer (if (0 : ℝ) < 1 then 1 / 2 else 1) (by split_ifs <;> norm_num))
      (Real.exp (-(Real.log 2 * 1))) := by
    refine GapStep.gapAt_mono _ ?_ ?_ (TransferGap.gapAt_diagTransfer _ _)
    · rw [if_pos (by norm_num : (0 : ℝ) < 1)]
      norm_num
    · rw [if_pos (by norm_num : (0 : ℝ) < 1), mul_one, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
  refine not_lossStep_of_gap_lost _ (fun _ => 1) 0 ε (β := 0) (β' := 1) (M := Real.log 2)
    le_rfl zero_le_one (by norm_num) le_rfl hbase hε one_pos ?_
  intro r hr
  exact diag_no_gap_of_lt _ _ r (by rw [if_neg (lt_irrefl (1 : ℝ)), one_pow]; exact hr)

#print axioms lossStep_not_automatic

end Witness

/-! ## 3. At the periodic state -/

section Wilson

variable {N : ℕ}

/-- **THE UV INPUT: the block step at the periodic state, with a loss.** `LossStep` for the periodic
gauge-invariant transfer data `periodicGaugeInvData τ p hN β` at the two-loop spacing `aRun N`: for
every two couplings `β, β' ≥ βUV` with `aRun N β / 2 ≤ aRun N β' ≤ aRun N β` and every `M`, the gap
at rate `e^{−M·aRun N β}` at `β` gives the gap at rate `e^{−(M − ε(aRun N β))·aRun N β'}` at `β'`.

This is not a theorem of the literature: it concerns the infinite-volume transfer gap, and the
block-spin results cited in the module docstring bound effective densities in a finite torus. It is
the correlation-level, infinite-volume statement such a block step would have to deliver. Its content
is carried together with `VanishingLoss` or a loss budget below the IR rate: with `ε(a)` at least the
largest physical rate attainable at spacing `a`, every conclusion is a rate at least one.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. The `2` is `LossStep`'s. -/
def UVLossStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (βUV : ℝ) (ε : ℝ → ℝ) : Prop :=
  LossStep (fun β => periodicGaugeInvData τ p hN β) (aRun N) βUV ε

/-- **The UV input with vanishing losses.** Some threshold `βUV` and loss function `ε` have
`VanishingLoss ε` and `UVLossStep τ p hN βUV ε`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
def UVInput (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) : Prop :=
  ∃ βUV : ℝ, ∃ ε : ℝ → ℝ, VanishingLoss ε ∧ UVLossStep τ p hN βUV ε

/-- **THE IR INPUT: the gap at one coupling, in physical units.** At the coupling `β₀`, the periodic
gauge-invariant transfer data has `GapAt` at rate `e^{−M₀·aRun N β₀}`: physical rate `M₀` at spacing
`aRun N β₀` (`GapStep.phys_rate_le_iff`). One coupling, one lattice spacing, infinite volume.
`aRun N β₀` reads as a lattice spacing only past its peak at `β = 17N²/(88π²)`
(`AsymptoticScaling.aRun`); below the peak `IRGapAt` holds at the proved strong-coupling rate
(`irGapAt_of_strong_coupling_chain`, `K = 0`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. -/
def IRGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₀ M₀ : ℝ) : Prop :=
  TransferGap.GapAt (periodicGaugeInvData τ p hN β₀) (Real.exp (-(M₀ * aRun N β₀)))

/-- **At zero loss the UV step is `GapStep.PhysStep`.** Under `UVLossStep τ p hN βUV ε`, two couplings
`β, β' ≥ βUV` at halved spacing `aRun N β' = aRun N β / 2`, with `0 ≤ aRun N β` and
`ε (aRun N β) = 0`, have `GapStep.PhysStep τ p hN β β' M` at every `M`; so along a halving sequence
with zero loss `GapStep.periodic_clay_tower` applies.

DERIVED: `4` is the spacetime dimension; `2` is the halving; `0` is the excluded rank, the sign of the
spacing and the loss. -/
theorem physStep_of_uvLossStep (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {βUV : ℝ} {ε : ℝ → ℝ}
    (h : UVLossStep τ p hN βUV ε) {β β' : ℝ} (hβ : βUV ≤ β) (hβ' : βUV ≤ β')
    (hhalf : aRun N β' = aRun N β / 2) (ha : 0 ≤ aRun N β) (h0 : ε (aRun N β) = 0) (M : ℝ) :
    GapStep.PhysStep τ p hN β β' M := by
  intro hg
  have hstep := h β β' hβ hβ' hhalf.ge (by rw [hhalf]; linarith) M hg
  rw [h0, sub_zero] at hstep
  exact hstep

#print axioms physStep_of_uvLossStep

/-- **The UV step is one lag at the finer coupling.** At `0 ≤ βUV` and any choice of lag
`m : ℝ → ℕ` with `m β ≠ 0`: `UVLossStep τ p hN βUV ε` holds exactly when, for every admissible pair
and every `M`, the gap at rate `e^{−M·aRun N β}` at `β` gives every `x` orthogonal to the vacuum at
`β'` the single-lag bound `form x (T^{m β'} x) ≤ (e^{−(M − ε)·aRun N β'})^{m β'} · form x x`
(`ChessboardRead.gapAt_iff_lag`, positivity of the transfer at `β' ≥ 0`,
`PeriodicState.periodic_positiveTransfer`). The step is a statement about one separation, which the
caller may place at any physical length (`uvLossStep_iff_long_lag`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `βUV`, the
excluded lag and the vacuum pairing; `2` is `LossStep`'s block factor. -/
theorem uvLossStep_iff_lag (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {βUV : ℝ} (hUV : 0 ≤ βUV)
    (ε : ℝ → ℝ) (m : ℝ → ℕ) (hm : ∀ β : ℝ, m β ≠ 0) :
    UVLossStep τ p hN βUV ε ↔
      ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
        ∀ M : ℝ, TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
          ∀ x, (periodicGaugeInvData τ p hN β').form x (periodicGaugeInvData τ p hN β').vac = 0 →
            (periodicGaugeInvData τ p hN β').form x
                (((periodicGaugeInvData τ p hN β').T ^ m β') x)
              ≤ Real.exp (-((M - ε (aRun N β)) * aRun N β')) ^ m β'
                * (periodicGaugeInvData τ p hN β').form x x := by
  constructor
  · intro h β β' h1 h2 h3 h4 M hg
    exact (ChessboardRead.gapAt_iff_lag _
      (PeriodicState.periodic_positiveTransfer τ p hN (hUV.trans h2)) (hm β')
      (Real.exp_pos _).le).mp (h β β' h1 h2 h3 h4 M hg)
  · intro h β β' h1 h2 h3 h4 M hg
    exact (ChessboardRead.gapAt_iff_lag _
      (PeriodicState.periodic_positiveTransfer τ p hN (hUV.trans h2)) (hm β')
      (Real.exp_pos _).le).mpr (h β β' h1 h2 h3 h4 M hg)

#print axioms uvLossStep_iff_lag

/-- The lag `max 1 ⌈ℓ/a⌉₊`: at spacing `a > 0` it spans at least the physical length `ℓ`
(`le_longLag_mul`), and it is never zero (`longLag_ne_zero`).

DERIVED: `1` is the least non-zero lag. -/
noncomputable def longLag (ℓ a : ℝ) : ℕ := max 1 ⌈ℓ / a⌉₊

/-- `longLag ℓ a ≠ 0`.

DERIVED: `0` is the excluded lag; `1` is `longLag`'s floor. -/
theorem longLag_ne_zero (ℓ a : ℝ) : longLag ℓ a ≠ 0 :=
  (lt_of_lt_of_le Nat.one_pos (le_max_left 1 _)).ne'

#print axioms longLag_ne_zero

/-- `ℓ ≤ longLag ℓ a · a` at `0 < a`: the lag spans at least the physical length `ℓ`
(`Nat.le_ceil`, `div_le_iff₀`).

DERIVED: `0` is the sign of the spacing. -/
theorem le_longLag_mul (ℓ : ℝ) {a : ℝ} (ha : 0 < a) : ℓ ≤ (longLag ℓ a : ℝ) * a := by
  have h1 : ℓ / a ≤ (⌈ℓ / a⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈ℓ / a⌉₊ : ℝ) ≤ (longLag ℓ a : ℝ) := by
    unfold longLag
    exact Nat.cast_le.mpr (le_max_right _ _)
  exact (div_le_iff₀ ha).mp (h1.trans h2)

#print axioms le_longLag_mul

/-- **The UV step at physical separation at least `ℓ`.** At `0 ≤ βUV` and every `ℓ`:
`UVLossStep τ p hN βUV ε` holds exactly when, for every admissible pair and every `M`, the gap at
rate `e^{−M·aRun N β}` at `β` gives every `x` orthogonal to the vacuum at `β'` the single-lag bound at
the lag `longLag ℓ (aRun N β')`, which spans at least `ℓ` in physical units wherever
`0 < aRun N β'` (`le_longLag_mul`). `uvLossStep_iff_lag` at that lag.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `βUV` and the
vacuum pairing; `2` is `LossStep`'s block factor. -/
theorem uvLossStep_iff_long_lag (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {βUV : ℝ} (hUV : 0 ≤ βUV)
    (ε : ℝ → ℝ) (ℓ : ℝ) :
    UVLossStep τ p hN βUV ε ↔
      ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → aRun N β / 2 ≤ aRun N β' → aRun N β' ≤ aRun N β →
        ∀ M : ℝ, TransferGap.GapAt (periodicGaugeInvData τ p hN β) (Real.exp (-(M * aRun N β))) →
          ∀ x, (periodicGaugeInvData τ p hN β').form x (periodicGaugeInvData τ p hN β').vac = 0 →
            (periodicGaugeInvData τ p hN β').form x
                (((periodicGaugeInvData τ p hN β').T ^ longLag ℓ (aRun N β')) x)
              ≤ Real.exp (-((M - ε (aRun N β)) * aRun N β')) ^ longLag ℓ (aRun N β')
                * (periodicGaugeInvData τ p hN β').form x x :=
  uvLossStep_iff_lag τ p hN hUV ε (fun β' => longLag ℓ (aRun N β'))
    (fun β' => longLag_ne_zero ℓ (aRun N β'))

#print axioms uvLossStep_iff_long_lag

/-- **The composition: the gap at every large coupling from the UV step and the gap at one coupling.**
At `1 ≤ N`, a coupling `0 < β₀` with `βUV ≤ β₀`, a loss budget `E` for the dyadic tower below
`aRun N β₀`, `UVLossStep τ p hN βUV ε` and `IRGapAt τ p hN β₀ M₀`: at every large `β`, the periodic
data has `GapAt` at rate `e^{−(M₀ − E)·aRun N β}`.

The proof: couplings `γ i ≥ β₀` with `aRun N (γ i) = aRun N β₀ / 2ⁱ`, `γ 0 = β₀`
(`AsymptoticScaling.exists_beta_aRun_eq`); a large `β` has `aRun N β ≤ aRun N β₀`
(`WeakCouplingWindow.eventually_aRun_le`), so its octave `n` has
`aRun N β₀ / 2ⁿ⁺¹ < aRun N β ≤ aRun N β₀ / 2ⁿ` (`pow_unbounded_of_one_lt`, `Nat.find`); the chain
`γ 0 → … → γ n` of exact halvings (`gapAt_chain`) and one last step `γ n → β` lose
`Σ_{i ≤ n} ε(aRun N β₀ / 2ⁱ) ≤ E`, and `GapStep.gapAt_mono` moves the rate to `e^{−(M₀ − E)·aRun N β}`.

DERIVED: `4` is the spacetime dimension; `1` is the least colour count, for `aRun_pos`; `0` is the
excluded rank and the sign of `β₀`; the `2` of the dyadic spacings is `LossStep`'s block factor. -/
theorem gapAt_eventually_of_uv_ir (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0)
    {βUV β₀ M₀ E : ℝ} {ε : ℝ → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hbudget : LossBudget ε (aRun N β₀) E) (huv : UVLossStep τ p hN βUV ε)
    (hir : IRGapAt τ p hN β₀ M₀) :
    ∀ᶠ β in Filter.atTop, TransferGap.GapAt (periodicGaugeInvData τ p hN β)
      (Real.exp (-((M₀ - E) * aRun N β))) := by
  have ha₀ : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  -- couplings at the dyadic spacings below `aRun N β₀`
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
  -- one exact halving, with its loss
  have hstep : ∀ j : ℕ, ∀ M : ℝ,
      TransferGap.GapAt (periodicGaugeInvData τ p hN (γ j)) (Real.exp (-(M * aRun N (γ j)))) →
      TransferGap.GapAt (periodicGaugeInvData τ p hN (γ (j + 1)))
        (Real.exp (-((M - ε (aRun N β₀ / 2 ^ j)) * aRun N (γ (j + 1))))) := by
    intro j M hgj
    have h := huv (γ j) (γ (j + 1)) (hUVβ₀.trans (hγβ j)) (hUVβ₀.trans (hγβ (j + 1)))
      (le_of_eq (by rw [hγ j, hγ (j + 1), pow_succ, div_div]))
      (by
        rw [hγ j, hγ (j + 1), pow_succ, ← div_div]
        have hnn : 0 ≤ aRun N β₀ / 2 ^ j := div_nonneg ha₀.le (by positivity)
        linarith)
      M hgj
    rw [hγ j] at h
    exact h
  have hbase0 : TransferGap.GapAt (periodicGaugeInvData τ p hN (γ 0))
      (Real.exp (-(M₀ * aRun N (γ 0)))) := by
    rw [hγ0]
    exact hir
  filter_upwards [WeakCouplingWindow.eventually_aRun_le hN1 ha₀,
    Filter.eventually_ge_atTop βUV, Filter.eventually_gt_atTop (0 : ℝ)] with β hβa hβUV hβ0
  have ha : 0 < aRun N β := aRun_pos hN1 hβ0
  -- the octave of `β`
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
  -- the chain of exact halvings to `γ n`
  have hchain : TransferGap.GapAt (periodicGaugeInvData τ p hN (γ n))
      (Real.exp (-((M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i)) * aRun N (γ n)))) :=
    gapAt_chain (fun i => periodicGaugeInvData τ p hN (γ i)) (fun i => aRun N (γ i))
      (fun i => ε (aRun N β₀ / 2 ^ i)) M₀ n hbase0 (fun j _ M hgj => hstep j M hgj) n le_rfl
  -- the last step, from `γ n` to `β`
  have hlast := huv (γ n) β (hUVβ₀.trans (hγβ n)) hβUV
    (by
      rw [hγ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hγ n]
      exact hle)
    (M₀ - ∑ i ∈ Finset.range n, ε (aRun N β₀ / 2 ^ i)) hchain
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

#print axioms gapAt_eventually_of_uv_ir

/-- **THE UV/IR SPLIT: `FixedWindowDecay` from the UV step and the gap at one coupling.** At `2 ≤ N`,
a window `0 < L`, a coupling `0 < β₀` with `βUV ≤ β₀`, a loss budget `E` for the dyadic tower below
`aRun N β₀` with `E < M₀`, `UVLossStep τ p hN βUV ε` and `IRGapAt τ p hN β₀ M₀`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L`.

`gapAt_eventually_of_uv_ir` gives `GapAt` at `r = e^{−(M₀ − E)·aRun N β}` at every large `β`;
`GapStep.periodic_clayGapAt_of_gapAt` gives `PeriodicClayGapAt` at `r`, whose physical rate
`−log r / aRun N β` is `M₀ − E = c/L` with `c = (M₀ − E)·L > 0`; and
`WeakCouplingWindow.fixedWindowDecay_of_physical_gap` returns `FixedWindowDecay`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance of the
real trace; `0` is the excluded rank and the sign of `L` and `β₀`. -/
theorem fixedWindowDecay_of_uv_ir (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV β₀ M₀ E : ℝ} {ε : ℝ → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hbudget : LossBudget ε (aRun N β₀) E) (hEM : E < M₀)
    (huv : UVLossStep τ p hN βUV ε) (hir : IRGapAt τ p hN β₀ M₀) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  have hN1 : 1 ≤ N := by omega
  have hev := gapAt_eventually_of_uv_ir τ p hN1 hN hβ₀ hUVβ₀ hbudget huv hir
  refine WeakCouplingWindow.fixedWindowDecay_of_physical_gap τ p hN1 hN hL
    ⟨(M₀ - E) * L, mul_pos (sub_pos.mpr hEM) hL, ?_⟩
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with β hg hβ0
  have ha : 0 < aRun N β := aRun_pos hN1 hβ0
  have hr0 : 0 < Real.exp (-((M₀ - E) * aRun N β)) := Real.exp_pos _
  have hr1 : Real.exp (-((M₀ - E) * aRun N β)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (sub_pos.mpr hEM) ha))
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0.le hr0 hr1 hg, ?_⟩
  have e1 : (M₀ - E) * L / L = M₀ - E := mul_div_cancel_right₀ _ hL.ne'
  have e2 : -Real.log (Real.exp (-((M₀ - E) * aRun N β))) / aRun N β = M₀ - E := by
    rw [Real.log_exp, neg_neg]
    exact mul_div_cancel_right₀ _ ha.ne'
  exact le_of_eq (by rw [e1, e2])

#print axioms fixedWindowDecay_of_uv_ir

/-- **`FixedWindowDecay` gives the IR input at every large coupling.** At `2 ≤ N` and `0 < L`,
`FixedWindowDecay τ p hN L` gives some `M > 0` with `IRGapAt τ p hN β₀ M` at every large `β₀`:
`WeakCouplingWindow.fixedWindowDecay_iff` gives `PeriodicClayGapAt` at a rate `r` with
`c/L ≤ −log r / aRun N β₀`, its contraction conjunct is `GapAt` at `r`
(`WeakCouplingWindow.gapAt_of_periodicClayGapAt`), and `r ≤ e^{−(c/L)·aRun N β₀}` moves it to the
IR rate (`GapStep.gapAt_mono`); the proof takes `M = c/L`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L` and `M`. -/
theorem irGapAt_of_fixedWindowDecay (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) (h : WeakCouplingWindow.FixedWindowDecay τ p hN L) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ β₀ in Filter.atTop, IRGapAt τ p hN β₀ M := by
  obtain ⟨c, hc, hev⟩ := (WeakCouplingWindow.fixedWindowDecay_iff τ p hN2 hN hL).mp h
  refine ⟨c / L, div_pos hc hL, ?_⟩
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with β hβ hβ0
  obtain ⟨r, hcl, hrate⟩ := hβ
  have hg := WeakCouplingWindow.gapAt_of_periodicClayGapAt τ p hN hcl
  obtain ⟨hr0, -, -, -, -, -, -⟩ := hcl
  have ha : 0 < aRun N β := aRun_pos (by omega) hβ0
  have h1 : c / L * aRun N β ≤ -Real.log r := (le_div_iff₀ ha).mp hrate
  have hle : r ≤ Real.exp (-(c / L * aRun N β)) := by
    rw [← Real.exp_log hr0, Real.exp_le_exp]
    linarith
  exact GapStep.gapAt_mono _ hr0.le hle hg

#print axioms irGapAt_of_fixedWindowDecay

/-- **Under the UV input, `FixedWindowDecay` is the gap at one coupling.** At `2 ≤ N`, `0 < L`,
`VanishingLoss ε` and `UVLossStep τ p hN βUV ε`: `FixedWindowDecay τ p hN L` holds exactly when some
coupling `0 < β₀` with `βUV ≤ β₀` and some `M₀`, `E` have the loss budget `E` below `aRun N β₀`,
`E < M₀`, and `IRGapAt τ p hN β₀ M₀`.

Forward: `irGapAt_of_fixedWindowDecay` gives `M > 0` and the IR gap at rate `M` at every large `β₀`;
`VanishingLoss` at `δ = M/2` gives `a₁`, and a large `β₀` has `aRun N β₀ ≤ a₁`
(`WeakCouplingWindow.eventually_aRun_le`), budget `M/2 < M`, `β₀ ≥ βUV` and `β₀ > 0`
(`Filter.Eventually.exists`). Back: `fixedWindowDecay_of_uv_ir`.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L` and `β₀`. CHOSEN: `δ = M/2` in the proof; any `δ ∈ (0, M)`
serves. -/
theorem fixedWindowDecay_iff_irGapAt (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) {βUV : ℝ} {ε : ℝ → ℝ} (hvan : VanishingLoss ε)
    (huv : UVLossStep τ p hN βUV ε) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
      ∃ β₀ M₀ E : ℝ, 0 < β₀ ∧ βUV ≤ β₀ ∧ LossBudget ε (aRun N β₀) E ∧ E < M₀ ∧
        IRGapAt τ p hN β₀ M₀ := by
  constructor
  · intro h
    have hN1 : 1 ≤ N := by omega
    obtain ⟨M, hM, hev⟩ := irGapAt_of_fixedWindowDecay τ p hN2 hN hL h
    obtain ⟨a₁, ha₁, hbud⟩ := hvan (M / 2) (half_pos hM)
    obtain ⟨β₀, hβ₀ir, hβ₀a, hβ₀UV, hβ₀pos⟩ :=
      (hev.and ((WeakCouplingWindow.eventually_aRun_le hN1 ha₁).and
        ((Filter.eventually_ge_atTop βUV).and (Filter.eventually_gt_atTop (0 : ℝ))))).exists
    exact ⟨β₀, M, M / 2, hβ₀pos, hβ₀UV, hbud _ (aRun_pos hN1 hβ₀pos) hβ₀a, half_lt_self hM,
      hβ₀ir⟩
  · rintro ⟨β₀, M₀, E, hβ₀, hUVβ₀, hbudget, hEM, hir⟩
    exact fixedWindowDecay_of_uv_ir τ p hN2 hN hL hβ₀ hUVβ₀ hbudget hEM huv hir

#print axioms fixedWindowDecay_iff_irGapAt

/-- **The same from the packaged UV input.** At `2 ≤ N`, `0 < L` and `UVInput τ p hN`, there are
`βUV` and `ε` with `UVLossStep τ p hN βUV ε` under which `FixedWindowDecay τ p hN L` is the IR gap at
one coupling beating the loss budget below it (`fixedWindowDecay_iff_irGapAt`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L` and `β₀`. -/
theorem fixedWindowDecay_iff_of_uvInput (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {L : ℝ}
    (hL : 0 < L) (h : UVInput τ p hN) :
    ∃ βUV : ℝ, ∃ ε : ℝ → ℝ, UVLossStep τ p hN βUV ε ∧
      (WeakCouplingWindow.FixedWindowDecay τ p hN L ↔
        ∃ β₀ M₀ E : ℝ, 0 < β₀ ∧ βUV ≤ β₀ ∧ LossBudget ε (aRun N β₀) E ∧ E < M₀ ∧
          IRGapAt τ p hN β₀ M₀) := by
  obtain ⟨βUV, ε, hvan, huv⟩ := h
  exact ⟨βUV, ε, huv, fixedWindowDecay_iff_irGapAt τ p hN2 hN hL hvan huv⟩

#print axioms fixedWindowDecay_iff_of_uvInput

/-- **The IR gap from the strong-coupling base and finitely many steps.** At `1 ≤ N` there is
`βsc > 0` such that for every finite chain of couplings `c 0, …, c K` with `0 < c 0 < βsc`, every
`Ms ≤ −log(coreRate (16 * 4) (c 0)) / aRun N (c 0)`, and every chain of lossy steps
`IRGapAt (c j) M → IRGapAt (c (j+1)) (M − e j)` for `j < K`:
`IRGapAt τ p hN (c K) (Ms − Σ_{j<K} e j)`. The base is proved
(`PeriodicStrongCoupling.periodic_tower_base`); the `K` steps are the hypotheses; `gapAt_chain`
composes them.

At small `β` the two-loop formula `aRun N β` is small (it rises to its maximum at
`β = 17N²/(88π²) ≈ 0.0196·N²`, `AsymptoticScaling.aRun`), so `Ms` measures the strong-coupling rate
in the units of a formula outside its range. The step hypotheses carry both the crossover from strong
to weak coupling and that change of units; neither is proved here.

DERIVED: `16 * 4` is the periodic touch-degree bound of `periodic_tower_base`; `4` is the spacetime
dimension; `1` is the least colour count and the step to the next index; `0` is the excluded rank,
the base index and the sign of `βsc` and `c 0`. -/
theorem irGapAt_of_strong_coupling_chain (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) :
    ∃ βsc > 0, ∀ (c e : ℕ → ℝ) (K : ℕ) (Ms : ℝ), 0 < c 0 → c 0 < βsc →
      Ms ≤ -Real.log (StrongCoupling.coreRate (16 * 4) (c 0)) / aRun N (c 0) →
      (∀ j : ℕ, j < K → ∀ M : ℝ, IRGapAt τ p hN (c j) M → IRGapAt τ p hN (c (j + 1)) (M - e j)) →
      IRGapAt τ p hN (c K) (Ms - ∑ i ∈ Finset.range K, e i) := by
  obtain ⟨βsc, hβsc, hbase⟩ := PeriodicStrongCoupling.periodic_tower_base τ p hN1 hN
  refine ⟨βsc, hβsc, fun c e K Ms hc0 hcsc hMs hsteps => ?_⟩
  exact gapAt_chain (fun j => periodicGaugeInvData τ p hN (c j)) (fun j => aRun N (c j)) e Ms K
    (hbase (c 0) hc0 hcsc Ms hMs) (fun j hj M hgj => hsteps j hj M hgj) K le_rfl

#print axioms irGapAt_of_strong_coupling_chain

/-- **Base, crossover and UV together.** At `2 ≤ N` and `0 < L` there is `βsc > 0` such that a finite
crossover chain `c 0, …, c K` from `0 < c 0 < βsc` with losses `e j` (as in
`irGapAt_of_strong_coupling_chain`), ending at `c K > 0` with `βUV ≤ c K`, a loss budget `E` below
`aRun N (c K)` with `E < Ms − Σ_{j<K} e j`, and `UVLossStep τ p hN βUV ε`, give
`FixedWindowDecay τ p hN L`. `irGapAt_of_strong_coupling_chain` and `fixedWindowDecay_of_uv_ir`.

DERIVED: `16 * 4` is the periodic touch-degree bound; `4` is the spacetime dimension; `2` is the least
rank with a non-zero Haar variance; `1` is the step to the next index; `0` is the excluded rank, the
base index and the sign of `βsc`, `c 0`, `c K` and `L`. -/
theorem fixedWindowDecay_of_base_crossover_uv (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    ∃ βsc > 0, ∀ (c e : ℕ → ℝ) (K : ℕ) (Ms βUV E : ℝ) (ε : ℝ → ℝ), 0 < c 0 → c 0 < βsc →
      Ms ≤ -Real.log (StrongCoupling.coreRate (16 * 4) (c 0)) / aRun N (c 0) →
      (∀ j : ℕ, j < K → ∀ M : ℝ, IRGapAt τ p hN (c j) M → IRGapAt τ p hN (c (j + 1)) (M - e j)) →
      0 < c K → βUV ≤ c K → LossBudget ε (aRun N (c K)) E →
      E < Ms - ∑ i ∈ Finset.range K, e i → UVLossStep τ p hN βUV ε →
      WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨βsc, hβsc, hchain⟩ := irGapAt_of_strong_coupling_chain τ p (by omega : 1 ≤ N) hN
  exact ⟨βsc, hβsc, fun c e K Ms βUV E ε hc0 hcsc hMs hsteps hcK hUV hbud hlt huv =>
    fixedWindowDecay_of_uv_ir τ p hN2 hN hL hcK hUV hbud hlt huv
      (hchain c e K Ms hc0 hcsc hMs hsteps)⟩

#print axioms fixedWindowDecay_of_base_crossover_uv

/-- **The zero loss vanishes.** `VanishingLoss (fun _ => 0)`: every budget is `0`.

DERIVED: `0` is the loss and the sign of `δ`. CHOSEN: `1` in the proof, the witness `a₁`; any
positive number serves. -/
theorem vanishingLoss_zero : VanishingLoss (fun _ : ℝ => (0 : ℝ)) := by
  intro δ hδ
  refine ⟨1, one_pos, fun a _ _ => ?_⟩
  intro n
  simp only [Finset.sum_const_zero]
  exact hδ.le

#print axioms vanishingLoss_zero

/-- **The UV step carries no gap: it holds on a gapless family at the tree's spacing.** At `1 ≤ N`,
`0 < βUV` and `ε ≥ 0`, the constant family `TransferGap.diagTransfer 1`, whose step is the identity,
satisfies `LossStep` at the spacing `aRun N` above `βUV` (`lossStep_of_no_gap`), and has no `GapAt`
at any `r` with `r² < 1` (`diag_no_gap_of_lt`). With `ε = 0` the loss also vanishes
(`vanishingLoss_zero`), so the UV shape together with `VanishingLoss` holds where no coupling has a
gap: the gap in `fixedWindowDecay_of_uv_ir` comes from `IRGapAt`.

DERIVED: `2` is `GapAt`'s degree; `1` is the least colour count, for `aRun_pos`, the rate of the
identity step and the rate at which `GapAt` is automatic; `0` is the sign of `βUV` and `ε`. -/
theorem lossStep_without_gap (hN1 : 1 ≤ N) {βUV : ℝ} (hUV : 0 < βUV) {ε : ℝ → ℝ}
    (hε : ∀ s : ℝ, 0 ≤ ε s) :
    LossStep (fun _ : ℝ => TransferGap.diagTransfer 1 (by norm_num)) (aRun N) βUV ε ∧
      ∀ r : ℝ, r ^ 2 < 1 → ¬ TransferGap.GapAt (TransferGap.diagTransfer 1 (by norm_num)) r := by
  have hno : ∀ r : ℝ, r ^ 2 < 1 →
      ¬ TransferGap.GapAt (TransferGap.diagTransfer 1 (by norm_num)) r :=
    fun r hr => diag_no_gap_of_lt 1 (by norm_num) r (by rw [one_pow]; exact hr)
  exact ⟨lossStep_of_no_gap _ (aRun N) βUV ε hε
    (fun β hβ => aRun_pos hN1 (lt_of_lt_of_le hUV hβ)) (fun _ _ r hr => hno r hr), hno⟩

#print axioms lossStep_without_gap

end Wilson

end MassGap.UVIRSplit
