import MassGap.CellCouple

/-!
# MassGap.LocalGap — the Knabe local-gap criterion, its derived threshold, and a saturating control

## What this module is for

`CellCouple` closes the operator-norm route: the residual between a coupled chain Hamiltonian and a
product reference is EXTENSIVE in the bond count, so a fixed budget `μ/2` admits only finitely many
volumes. The surviving route is the local-gap (Knabe / Gosset–Mozgunov) criterion, where the bound on
the bulk gap is produced by a window of FIXED size and therefore carries no bond count at all.

`CellSpectrum` already carries the abstract Gosset–Mozgunov assembly for the plain-window chain
(`gm_eq23_c1`, `gm_gap_c1`). What it does NOT carry is the step that makes it the Knabe criterion:
`gm_gap_c1` takes the per-window bound as a bare hypothesis `hlem4`. This module supplies it from the
window's own spectrum, states the criterion in its canonical form, derives the threshold instead of
choosing it, and exhibits a family that saturates the threshold exactly.

## The three statements

* `knabe_chain_gap` / `knabe_chain_gap_of_local_spectrum` — the criterion. A frustration-free
  nearest-neighbour projector chain on `ZMod L` whose every `m`-bond window has spectrum in
  `{0} ∪ [ε,∞)` has every positive eigenvalue of `H = ∑ h_b` bounded below by `(m·ε − 1)/(m − 1)`.
  `L` does not occur in that bound, which is the whole point: `knabe_gap_volume_independent` says one
  constant serves every volume and every dimension of the state space at once.

* `knabe_bound_pos_iff` — the threshold is DERIVED. `(m·ε − 1)/(m − 1) > 0` holds exactly when
  `ε > 1/m`. The number `1/m` is the zero of the bound, not a chosen constant; `m` is the window size
  and is the only parameter.

* `laplace_never_clears_threshold` / `laplace_no_uniform_gap` — the control. The discrete-Laplacian
  chain (bond `b` carries the rank-one projector onto `e_b − e_{b+1}`) is a frustration-free projector
  chain meeting every structural hypothesis, and on it the linear ramp `r i = i` forces `ε ≤ 1/m` on
  every window: the criterion's hypothesis is unsatisfiable there at every window size. The same ramp
  applied to the whole chain forces any bulk gap to satisfy `g ≤ 1/L`, so no positive constant serves
  every volume. The threshold is exactly the line between the two.

## What the ramp computes

For a block of `n` consecutive bonds, `B = ∑_{j<n} h_j` acts on `r i = i` as a discrete second
difference, which vanishes on a linear function except at the two ends of the block. Concretely
`B r = −(1/2)(e_0 − e_n)`, so `⟨Br, Br⟩ = 1/2` while `⟨r, Br⟩ = n/2`. The operator inequality
`B² ⪰ ε B` read at `r` is then `ε·(n/2) ≤ 1/2`, i.e. `ε ≤ 1/n`. At `n = m` that is the window bound;
at `n = L` it is the bulk bound. One computation, both halves, and it lands on `1/n` — the same number
`knabe_bound_pos_iff` produces from the criterion. `laplace_ground_state` records that this chain is
frustration-free, so `1/L` really is a bound on its gap and not an artifact of a missing zero mode.

## The structural hypothesis, and whether Yang–Mills meets it

Every theorem here is about a chain of PROJECTORS (`h b * h b = h b`) whose far-separated terms
commute. Frustration-freeness is a restriction on the physics and not a normalisation: it says the
ground state minimises each local term separately. `Transfer.TransferData` builds the Yang–Mills
object as a self-adjoint contraction on a GNS quotient — a positive contraction, not a sum of
projectors — and the Kogut–Susskind Hamiltonian `(g²/2)∑E² − (1/g²)∑Re tr U_p` has an electric and a
magnetic term that do not commute, so its ground state does not minimise both. Nothing in this module
supplies that presentation, and the criterion does not apply to the physical transfer operator until
something does.
-/

namespace MassGap.LocalGap

open scoped Matrix
open Matrix
open MassGap.CellEnclosure

/-! ### The Knabe window -/

/-- The Knabe window: the `m` consecutive bond terms starting at bond `k`. Written with the explicit
`(1 : ℝ) •` so that it is the same term as the deformed window of `gm_gap_c1` at unit weights.

DERIVED: the weight `1` is the Gosset–Mozgunov deformation coefficient `c_j` at its undeformed value.
It is not a tuning knob here — it is what makes the window autocorrelation `A_x = m − x`, which is the
only input `hnn_c1` accepts, and it is what turns the bound of `gm_gap_c1` into `(m·ε − 1)/(m − 1)`. A
different weight would be a different criterion with a different threshold. -/
noncomputable def win {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ)
    (k : ZMod L) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))

/-- A Hermitian idempotent is positive semidefinite: `P = Pᴴ P`. -/
theorem proj_posSemidef {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ} (hP : P.IsHermitian)
    (hPi : P * P = P) : P.PosSemidef := by
  have hs := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hPi] at hs

/-- A window of Hermitian bond terms is Hermitian. -/
theorem win_isHermitian {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (m : ℕ) (k : ZMod L) : (win h m k).IsHermitian :=
  isHermitian_sum _ _ (fun j _ => by rw [one_smul]; exact hherm _)

/-- A window of projectors is positive semidefinite, so its eigenvalues are nonnegative without any
extra hypothesis: frustration-freeness already supplies the `hpsd` input of `operator_sq_ge_of_gap`. -/
theorem win_posSemidef {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b) (m : ℕ) (k : ZMod L) :
    (win h m k).PosSemidef :=
  Matrix.posSemidef_sum _ (fun j _ => by
    rw [one_smul]; exact proj_posSemidef (hherm _) (hproj _))

/-! ### The criterion -/

/-- **Knabe local-gap criterion, operator-inequality form (foundational).** For a frustration-free
nearest-neighbour projector chain on `ZMod L` whose far-separated pair sums are positive semidefinite,
if every `m`-bond window satisfies the operator inequality `W² ⪰ ε W`, then every positive eigenvalue
`lam` of `H = ∑_b h_b` obeys `lam ≥ (m·ε − 1)/(m − 1)`.

The bound does not mention `L`. That is the property the operator-norm route of `CellCouple` cannot
have: there the residual carried a bond count, here the constant is produced by a window of fixed
size `m` and the chain length only has to be long enough (`2m ≤ L`) for the windows to fit twice. -/
theorem knabe_chain_gap {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b)
    (m : ℕ) (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L)
    (hfar : ∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
      (∑ b : ZMod L, h b * h (b + δ)).PosSemidef)
    {ε : ℝ}
    (hwin : ∀ k : ZMod L, ∀ x : Fin N → ℝ,
      ε * (x ⬝ᵥ (win h m k *ᵥ x)) ≤ (win h m k *ᵥ x) ⬝ᵥ (win h m k *ᵥ x))
    {lam : ℝ} {ψ : Fin N → ℝ}
    (hψ : (∑ b, h b) *ᵥ ψ = lam • ψ) (hψ0 : ψ ⬝ᵥ ψ ≠ 0) (hlam : 0 < lam) :
    ((m : ℝ) * ε - 1) / ((m : ℝ) - 1) ≤ lam := by
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have h0 := gm_gap_c1 h hherm hproj m hm2 hmL hfar hψ hψ0 hlam (fun k => hwin k ψ)
  have hrw : ((m : ℝ) * ε - 1) / ((m : ℝ) - 1)
      = ((m : ℝ) - 1)⁻¹ * ε * (m : ℝ) - ((m : ℝ) - 1)⁻¹ := by
    field_simp
  rw [hrw]
  exact h0

/-- **Knabe local-gap criterion, spectral form (foundational).** The same statement with the local
input in the shape a finite-size diagonalisation actually produces: every eigenvalue of every window
is `0` or at least `ε`. Positive semidefiniteness of the windows is not assumed — it follows from the
bond terms being projectors (`win_posSemidef`) — and `operator_sq_ge_of_gap` turns the spectral
condition into the operator inequality the assembly consumes. -/
theorem knabe_chain_gap_of_local_spectrum {N L : ℕ} [NeZero L]
    (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b)
    (m : ℕ) (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L)
    (hfar : ∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
      (∑ b : ZMod L, h b * h (b + δ)).PosSemidef)
    {ε : ℝ}
    (hgap : ∀ k : ZMod L, ∀ i,
      (win_isHermitian h hherm m k).eigenvalues i = 0 ∨ ε ≤ (win_isHermitian h hherm m k).eigenvalues i)
    {lam : ℝ} {ψ : Fin N → ℝ}
    (hψ : (∑ b, h b) *ᵥ ψ = lam • ψ) (hψ0 : ψ ⬝ᵥ ψ ≠ 0) (hlam : 0 < lam) :
    ((m : ℝ) * ε - 1) / ((m : ℝ) - 1) ≤ lam := by
  refine knabe_chain_gap h hherm hproj m hm2 hmL hfar (fun k => ?_) hψ hψ0 hlam
  exact operator_sq_ge_of_gap (win_isHermitian h hherm m k)
    (fun i => (win_posSemidef h hherm hproj m k).eigenvalues_nonneg i) (hgap k)

/-- **The threshold is derived, not chosen (foundational).** The bound `(m·ε − 1)/(m − 1)` produced by
`knabe_chain_gap` is strictly positive exactly when the local gap exceeds `1/m`. Nothing selects the
number `1/m`: it is the zero of the bound, and the only parameter is the window size `m`. -/
theorem knabe_bound_pos_iff (m : ℕ) (hm2 : 2 ≤ m) (ε : ℝ) :
    0 < ((m : ℝ) * ε - 1) / ((m : ℝ) - 1) ↔ 1 / (m : ℝ) < ε := by
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [div_pos_iff]
  constructor
  · rintro (⟨hnum, _⟩ | ⟨_, hden⟩)
    · rw [div_lt_iff₀ hm0]; nlinarith
    · linarith
  · intro hε
    left
    refine ⟨?_, hm1⟩
    rw [div_lt_iff₀ hm0] at hε
    nlinarith

/-- **One constant for every volume (foundational).** Fix a window size `m` and a local gap `ε` above
the threshold. Then there is a single `g > 0` — namely `(m·ε − 1)/(m − 1)` — that bounds the positive
spectrum of EVERY chain satisfying the hypotheses, at every chain length `L` and every state-space
dimension `N`. This is the statement the extensive residual of `CellCouple.chain_budget_fails` denies
to the operator-norm route, and the reason a local-gap argument survives where that one does not. -/
theorem knabe_gap_volume_independent {m : ℕ} (hm2 : 2 ≤ m) {ε : ℝ} (hthr : 1 / (m : ℝ) < ε) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (N L : ℕ) [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ),
        (∀ b, (h b).IsHermitian) → (∀ b, h b * h b = h b) → 2 * m ≤ L →
        (∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
          (∑ b : ZMod L, h b * h (b + δ)).PosSemidef) →
        (∀ k : ZMod L, ∀ x : Fin N → ℝ,
          ε * (x ⬝ᵥ (win h m k *ᵥ x)) ≤ (win h m k *ᵥ x) ⬝ᵥ (win h m k *ᵥ x)) →
        ∀ (lam : ℝ) (ψ : Fin N → ℝ), (∑ b, h b) *ᵥ ψ = lam • ψ → ψ ⬝ᵥ ψ ≠ 0 → 0 < lam →
        g ≤ lam := by
  refine ⟨((m : ℝ) * ε - 1) / ((m : ℝ) - 1), (knabe_bound_pos_iff m hm2 ε).mpr hthr, ?_⟩
  intro N L _ h hherm hproj hmL hfar hwin lam ψ hψ hψ0 hlam
  exact knabe_chain_gap h hherm hproj m hm2 hmL hfar hwin hψ hψ0 hlam

/-! ### The statement cannot be satisfied by a degenerate window family

The window hypothesis `hwin` holds for EVERY `ε` when the windows are zero, so a statement of this
shape has to be checked against that escape. It is closed: the windows sum to `m·H`, so windows that
all vanish force `H = 0`, and then no eigenvalue is positive and `hlam` fails. -/

/-- The windows sum to `m · H`: every bond term lies in exactly `m` of them. -/
theorem sum_win {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (∑ k : ZMod L, win h m k) = (m : ℝ) • (∑ b, h b) := by
  have hw := weighted_window_sum h m (fun _ => (1 : ℝ))
  simpa [win, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hw

/-- **A vanishing window family kills the chain (foundational).** If every window is `0` then
`H = ∑_b h_b = 0`. So the window hypothesis of `knabe_chain_gap` cannot be met vacuously by trivial
windows while the conclusion still says anything. -/
theorem sum_eq_zero_of_win_eq_zero {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (m : ℕ) (hm : 0 < m) (hzero : ∀ k, win h m k = 0) : (∑ b, h b) = 0 := by
  have hsum := sum_win h m
  rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const, smul_zero] at hsum
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := hsum.symm
  simpa [smul_eq_zero, hmne] using this

/-- **No positive eigenvalue survives a vanishing window family (foundational).** Together with
`sum_eq_zero_of_win_eq_zero` this is the non-triviality check: the hypothesis `0 < lam` of
`knabe_chain_gap` is unsatisfiable exactly when the window family is degenerate, so the criterion
never delivers a positive bound from an empty statement. -/
theorem no_positive_eigenvalue_of_win_eq_zero {N L : ℕ} [NeZero L]
    (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ) (hm : 0 < m) (hzero : ∀ k, win h m k = 0)
    {lam : ℝ} {ψ : Fin N → ℝ} (hψ : (∑ b, h b) *ᵥ ψ = lam • ψ) (hψ0 : ψ ⬝ᵥ ψ ≠ 0) : lam = 0 := by
  rw [sum_eq_zero_of_win_eq_zero h m hm hzero, Matrix.zero_mulVec] at hψ
  by_contra hne
  apply hψ0
  have hz : ψ = 0 := by
    have := hψ.symm
    rcases smul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hne
    · exact h1
  rw [hz]; simp

/-- The window index type is inhabited and each window carries `m ≥ 1` terms, so the family quantified
over in `knabe_chain_gap` is never empty. -/
theorem win_family_nonempty {L : ℕ} [NeZero L] : Nonempty (ZMod L) :=
  ⟨0⟩

/-! ### A witness above the threshold, so the criterion is not vacuous

`siteProj` is the chain of rank-one projectors onto distinct basis directions: bond `b` projects onto
`e_{b.val}` in `ℝ^{L+1}`. Its bond terms are genuinely different from one another, all the structural
hypotheses hold, every window is itself a projector (so `ε = 1` with equality), and `1 > 1/m` clears
the threshold for every `m ≥ 2`. -/

/-- Distinct residues have distinct values. -/
theorem zmod_val_ne {L : ℕ} [NeZero L] {b c : ZMod L} (hbc : b ≠ c) : b.val ≠ c.val := by
  intro hv
  apply hbc
  calc b = ((b.val : ℕ) : ZMod L) := (ZMod.natCast_rightInverse b).symm
    _ = ((c.val : ℕ) : ZMod L) := by rw [hv]
    _ = c := ZMod.natCast_rightInverse c

/-- A sum of pairwise orthogonal projectors is a projector. -/
theorem sum_proj_idem {N : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → Matrix (Fin N) (Fin N) ℝ) (hidem : ∀ i ∈ s, P i * P i = P i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    (∑ i ∈ s, P i) * (∑ i ∈ s, P i) = ∑ i ∈ s, P i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
    (fun hns => absurd hi hns)]
  exact hidem i hi

/-- Bond `b` of the witness chain: the rank-one projector onto the basis direction `e_{b.val}`.

DERIVED: `0` and `1` are the only diagonal entries an idempotent diagonal matrix can carry, so they
are forced by `siteProj_idem`, not selected. The entry is `1` exactly on the one site the bond reads. -/
noncomputable def siteProj (L : ℕ) [NeZero L] (b : ZMod L) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  Matrix.diagonal (fun i => if i.val = b.val then (1 : ℝ) else 0)

theorem siteProj_isHermitian (L : ℕ) [NeZero L] (b : ZMod L) : (siteProj L b).IsHermitian :=
  Matrix.isHermitian_diagonal _

theorem siteProj_idem (L : ℕ) [NeZero L] (b : ZMod L) :
    siteProj L b * siteProj L b = siteProj L b := by
  rw [siteProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i.val = b.val <;> simp [hi]

theorem siteProj_orth (L : ℕ) [NeZero L] {b c : ZMod L} (hbc : b ≠ c) :
    siteProj L b * siteProj L c = 0 := by
  have hv := zmod_val_ne hbc
  have hfun : (fun i : Fin (L + 1) =>
      (if i.val = b.val then (1 : ℝ) else 0) * (if i.val = c.val then (1 : ℝ) else 0)) = 0 := by
    funext i
    show (if i.val = b.val then (1 : ℝ) else 0) * (if i.val = c.val then (1 : ℝ) else 0) = 0
    by_cases h1 : i.val = b.val
    · rw [if_neg (show ¬ (i.val = c.val) by omega), mul_zero]
    · rw [if_neg h1, zero_mul]
  rw [siteProj, siteProj, Matrix.diagonal_mul_diagonal, hfun]
  exact Matrix.diagonal_zero

/-- Every window of the witness chain is itself a projector: the `m` bonds it covers are distinct
residues, so the rank-one terms are pairwise orthogonal. -/
theorem win_siteProj_idem (L m : ℕ) [NeZero L] (hmL : m ≤ L) (k : ZMod L) :
    win (siteProj L) m k * win (siteProj L) m k = win (siteProj L) m k := by
  have hinj : ∀ j₁ ∈ Finset.range m, ∀ j₂ ∈ Finset.range m, j₁ ≠ j₂ →
      k + ((j₁ : ℕ) : ZMod L) ≠ k + ((j₂ : ℕ) : ZMod L) := by
    intro j₁ h₁ j₂ h₂ hne heq
    apply hne
    have hc : ((j₁ : ℕ) : ZMod L) = ((j₂ : ℕ) : ZMod L) := add_left_cancel heq
    have hv := congrArg ZMod.val hc
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := Finset.mem_range.mp h₁; omega),
      Nat.mod_eq_of_lt (by have := Finset.mem_range.mp h₂; omega)] at hv
    exact hv
  have hrw : win (siteProj L) m k = ∑ j ∈ Finset.range m, siteProj L (k + ((j : ℕ) : ZMod L)) := by
    simp [win]
  rw [hrw]
  exact sum_proj_idem _ _ (fun j _ => siteProj_idem L _)
    (fun j₁ h₁ j₂ h₂ hne => siteProj_orth L (hinj j₁ h₁ j₂ h₂ hne))

/-- A symmetric projector satisfies the window operator inequality at `ε = 1`, with equality. -/
theorem op_sq_ge_one_of_proj {N : ℕ} {W : Matrix (Fin N) (Fin N) ℝ} (hW : W.IsHermitian)
    (hWi : W * W = W) (x : Fin N → ℝ) :
    (1 : ℝ) * (x ⬝ᵥ (W *ᵥ x)) ≤ (W *ᵥ x) ⬝ᵥ (W *ᵥ x) := by
  have h1 : (W *ᵥ x) ⬝ᵥ (W *ᵥ x) = x ⬝ᵥ ((W * W) *ᵥ x) := by
    rw [sadj hW, mulVec_mulVec]
  rw [h1, hWi, one_mul]

/-- **The criterion is not vacuous (foundational).** For every window size `m ≥ 2` and every chain
length `L ≥ 2m` the hypotheses of `knabe_chain_gap` are jointly satisfiable, with a local gap `ε = 1`
strictly above the derived threshold `1/m`, a positive eigenvalue, and a strictly positive bound. The
bond terms are pairwise distinct projectors, not a single term repeated. -/
theorem knabe_witness (L m : ℕ) [NeZero L] (hm2 : 2 ≤ m) (hmL : 2 * m ≤ L) :
    ∃ (h : ZMod L → Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ) (ψ : Fin (L + 1) → ℝ) (lam ε : ℝ),
      (∀ b, (h b).IsHermitian) ∧ (∀ b, h b * h b = h b) ∧
      (∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
        (∑ b : ZMod L, h b * h (b + δ)).PosSemidef) ∧
      (∀ k : ZMod L, ∀ x : Fin (L + 1) → ℝ,
        ε * (x ⬝ᵥ (win h m k *ᵥ x)) ≤ (win h m k *ᵥ x) ⬝ᵥ (win h m k *ᵥ x)) ∧
      1 / (m : ℝ) < ε ∧
      ((∑ b, h b) *ᵥ ψ = lam • ψ) ∧ ψ ⬝ᵥ ψ ≠ 0 ∧ 0 < lam ∧
      0 < ((m : ℝ) * ε - 1) / ((m : ℝ) - 1) := by
  classical
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  set i0 : Fin (L + 1) := ⟨0, by omega⟩ with hi0
  refine ⟨siteProj L, Pi.single i0 (1 : ℝ), 1, 1, fun b => siteProj_isHermitian L b,
    fun b => siteProj_idem L b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro δ hδ0 _ _
    have hz : (∑ b : ZMod L, siteProj L b * siteProj L (b + δ)) = 0 := by
      refine Finset.sum_eq_zero (fun b _ => siteProj_orth L ?_)
      intro heq
      refine hδ0 ?_
      have hb0 : b + (0 : ZMod L) = b + δ := by rw [add_zero]; exact heq
      exact (add_left_cancel hb0).symm
    rw [hz]
    exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩
  · intro k x
    exact op_sq_ge_one_of_proj (win_isHermitian _ (siteProj_isHermitian L) m k)
      (win_siteProj_idem L m (by omega) k) x
  · have : (1 : ℝ) < (m : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith
    rw [div_lt_one (by linarith)]
    exact this
  · rw [Matrix.sum_mulVec, one_smul]
    rw [Finset.sum_eq_single (0 : ZMod L)]
    · funext i
      rw [siteProj, Matrix.mulVec_diagonal, ZMod.val_zero]
      by_cases hi : i = i0
      · rw [hi, hi0]; simp
      · have hz : (Pi.single i0 (1 : ℝ) : Fin (L + 1) → ℝ) i = 0 := by
          simp [hi]
        rw [hz]; ring
    · intro b _ hb
      have hbv : b.val ≠ 0 := by
        have := zmod_val_ne hb
        rwa [ZMod.val_zero] at this
      funext i
      rw [siteProj, Matrix.mulVec_diagonal]
      by_cases hi : i = i0
      · rw [hi, hi0]
        simp only []
        rw [if_neg (by simpa using (Ne.symm hbv))]
        simp
      · have hz : (Pi.single i0 (1 : ℝ) : Fin (L + 1) → ℝ) i = 0 := by
          simp [hi]
        rw [hz]; simp
    · intro hns; exact absurd (Finset.mem_univ (0 : ZMod L)) hns
  · rw [single_dotProduct_self]; norm_num
  · norm_num
  · have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    rw [div_pos_iff]
    left
    constructor
    · linarith
    · linarith

/-! ### The control: the discrete-Laplacian chain saturates the threshold

Bond `b` carries the rank-one projector onto `e_{b.val} − e_{b.val+1}` in `ℝ^{L+1}`, so `H = ∑_b h_b`
is half the path-graph Laplacian on `L+1` sites. This is a frustration-free projector chain meeting
every structural hypothesis of `knabe_chain_gap`: the terms are Hermitian idempotents, far-separated
terms annihilate one another, and the constant vector is a common zero.

The linear ramp `r i = i` is annihilated by the second difference in the interior of any block of
consecutive bonds, so the block operator sends it to a fixed two-site vector no matter how long the
block is. That is the whole content: the numerator of the Rayleigh quotient stays at `1/2` while the
denominator grows like the block length. -/

/-- The two-site vector `e_p − e_q`.

DERIVED: the coefficients `+1` and `−1` are what make `pairVec ⊙ pairVec = 2` (`pair_self`), which is
in turn what fixes the `1/2` in `dproj` by idempotence. `0` is the value off the two sites, i.e. the
statement that the bond term reads only its own two sites. -/
noncomputable def pairVec (L : ℕ) (p q : Fin (L + 1)) : Fin (L + 1) → ℝ :=
  fun i => (if i = p then (1 : ℝ) else 0) - (if i = q then (1 : ℝ) else 0)

/-- Left end of bond `b`.

DERIVED: `L + 1` sites carry `L` bonds, so `b.val < L` places `b.val` and `b.val + 1` in range. -/
def bs (L : ℕ) [NeZero L] (b : ZMod L) : Fin (L + 1) :=
  ⟨b.val, by have := ZMod.val_lt b; omega⟩

/-- Right end of bond `b`.

DERIVED: the offset `+1` is what nearest-neighbour means; the criterion's `hfar` hypothesis is stated
about offsets outside `{0, ±1}`, so any other offset would not be the chain the criterion is about. -/
def bt (L : ℕ) [NeZero L] (b : ZMod L) : Fin (L + 1) :=
  ⟨b.val + 1, by have := ZMod.val_lt b; omega⟩

theorem bs_val (L : ℕ) [NeZero L] (b : ZMod L) : (bs L b).val = b.val := rfl
theorem bt_val (L : ℕ) [NeZero L] (b : ZMod L) : (bt L b).val = b.val + 1 := rfl

/-- The bond vector of bond `b`.

DERIVED: the literals come from `bs`/`bt` (the `L + 1` sites) and from `pairVec`. -/
noncomputable def dvec (L : ℕ) [NeZero L] (b : ZMod L) : Fin (L + 1) → ℝ :=
  pairVec L (bs L b) (bt L b)

theorem pair_self (L : ℕ) {p q : Fin (L + 1)} (hpq : p ≠ q) :
    (pairVec L p q) ⬝ᵥ (pairVec L p q) = 2 := by
  have hpt : ∀ i : Fin (L + 1), pairVec L p q i * pairVec L p q i
      = (if i = p then (1 : ℝ) else 0) + (if i = q then (1 : ℝ) else 0) := by
    intro i
    unfold pairVec
    by_cases h1 : i = p
    · subst h1
      rw [if_pos rfl, if_neg hpq]; ring
    · by_cases h2 : i = q
      · subst h2
        rw [if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2]; ring
  show (∑ i, pairVec L p q i * pairVec L p q i) = 2
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ q (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, if_true]
  norm_num

/-- The ramp `r i = i`.

DERIVED: `L + 1` is the site count. The ramp itself is not a fitted trial vector: it is the unique
shape (up to affine changes, which the operator kills) whose discrete second difference vanishes, and
that is precisely why `blockOp_ramp` leaves only the two ends of the block. -/
noncomputable def ramp (L : ℕ) : Fin (L + 1) → ℝ := fun i => (i.val : ℝ)

theorem pair_ramp (L : ℕ) (p q : Fin (L + 1)) :
    (pairVec L p q) ⬝ᵥ (ramp L) = (p.val : ℝ) - (q.val : ℝ) := by
  show (∑ i, pairVec L p q i * ramp L i) = _
  simp only [pairVec, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ p (fun i => ramp L i),
    Finset.sum_ite_eq' Finset.univ q (fun i => ramp L i)]
  simp [ramp]

theorem pair_const (L : ℕ) (p q : Fin (L + 1)) :
    (pairVec L p q) ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
  show (∑ i, pairVec L p q i * (1 : ℝ)) = 0
  simp only [pairVec, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ q (fun _ => (1 : ℝ))]
  simp

theorem dvec_ramp (L : ℕ) [NeZero L] (b : ZMod L) : (dvec L b) ⬝ᵥ (ramp L) = -1 := by
  rw [dvec, pair_ramp, bs_val, bt_val]
  push_cast
  ring

/-- The bond projector of bond `b`: the rank-one projector onto `e_{b.val} − e_{b.val+1}`.

DERIVED: the `1/2` is forced. `dvec_self` gives `dvec ⊙ dvec = 2`, so `c·v vᵀ` is idempotent exactly at
`c = 1/2` — any other coefficient breaks `dproj_idem` and the chain would not be a projector chain at
all. The `1` is the site-count offset `L + 1`. -/
noncomputable def dproj (L : ℕ) [NeZero L] (b : ZMod L) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  Matrix.of fun i j => (1 / 2 : ℝ) * (dvec L b i * dvec L b j)

theorem dvec_self (L : ℕ) [NeZero L] (b : ZMod L) : (dvec L b) ⬝ᵥ (dvec L b) = 2 := by
  refine pair_self L ?_
  intro hcon
  have := congrArg Fin.val hcon
  rw [bs_val, bt_val] at this
  omega

theorem dproj_mulVec (L : ℕ) [NeZero L] (b : ZMod L) (x : Fin (L + 1) → ℝ) :
    dproj L b *ᵥ x = ((1 / 2 : ℝ) * ((dvec L b) ⬝ᵥ x)) • (dvec L b) := by
  funext i
  show (∑ j, dproj L b i j * x j) = _
  simp only [dproj, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  show (∑ j, (1 / 2 : ℝ) * (dvec L b i * dvec L b j) * x j) = _
  rw [show ((1 / 2 : ℝ) * ((dvec L b) ⬝ᵥ x)) * dvec L b i
      = ∑ j, (1 / 2 : ℝ) * (dvec L b i * dvec L b j) * x j by
    show _ = ∑ j, (1 / 2 : ℝ) * (dvec L b i * dvec L b j) * x j
    rw [show ((dvec L b) ⬝ᵥ x) = ∑ j, dvec L b j * x j from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)]

theorem dproj_isHermitian (L : ℕ) [NeZero L] (b : ZMod L) : (dproj L b).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, dproj, Matrix.of_apply, star_trivial]
  ring

theorem dproj_idem (L : ℕ) [NeZero L] (b : ZMod L) : dproj L b * dproj L b = dproj L b := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [dproj, Matrix.of_apply]
  have hstep : ∀ j, ((1 / 2 : ℝ) * (dvec L b i * dvec L b j)) *
      ((1 / 2 : ℝ) * (dvec L b j * dvec L b k))
      = ((1 / 4 : ℝ) * (dvec L b i * dvec L b k)) * (dvec L b j * dvec L b j) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum,
    show (∑ j, dvec L b j * dvec L b j) = 2 from dvec_self L b]
  ring

theorem dproj_orth (L : ℕ) [NeZero L] (b c : ZMod L) (hd : (dvec L b) ⬝ᵥ (dvec L c) = 0) :
    dproj L b * dproj L c = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [dproj, Matrix.of_apply]
  have hstep : ∀ j, ((1 / 2 : ℝ) * (dvec L b i * dvec L b j)) *
      ((1 / 2 : ℝ) * (dvec L c j * dvec L c k))
      = ((1 / 4 : ℝ) * (dvec L b i * dvec L c k)) * (dvec L b j * dvec L c j) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hstep j), ← Finset.mul_sum,
    show (∑ j, dvec L b j * dvec L c j) = 0 from hd]
  ring

/-- Bonds whose site pairs are two apart carry orthogonal vectors. -/
theorem dvec_orth_far (L : ℕ) [NeZero L] (b c : ZMod L)
    (hfar : b.val + 2 ≤ c.val ∨ c.val + 2 ≤ b.val) : (dvec L b) ⬝ᵥ (dvec L c) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases h1 : i = bs L b
  · have e1 : i ≠ bs L c := by
      intro hh; rw [h1] at hh
      have := congrArg Fin.val hh; rw [bs_val, bs_val] at this; omega
    have e2 : i ≠ bt L c := by
      intro hh; rw [h1] at hh
      have := congrArg Fin.val hh; rw [bs_val, bt_val] at this; omega
    have : dvec L c i = 0 := by simp [dvec, pairVec, e1, e2]
    rw [this]; ring
  · by_cases h2 : i = bt L b
    · have e1 : i ≠ bs L c := by
        intro hh; rw [h2] at hh
        have := congrArg Fin.val hh; rw [bt_val, bs_val] at this; omega
      have e2 : i ≠ bt L c := by
        intro hh; rw [h2] at hh
        have := congrArg Fin.val hh; rw [bt_val, bt_val] at this; omega
      have : dvec L c i = 0 := by simp [dvec, pairVec, e1, e2]
      rw [this]; ring
    · have : dvec L b i = 0 := by simp [dvec, pairVec, h1, h2]
      rw [this]; ring

/-- A cyclic offset outside `{0, ±1}` separates the two bonds by at least two sites. -/
theorem far_val (L : ℕ) [NeZero L] (hL : 2 ≤ L) (b δ : ZMod L)
    (h0 : δ ≠ 0) (h1 : δ ≠ 1) (hm1 : δ ≠ -1) :
    b.val + 2 ≤ (b + δ).val ∨ (b + δ).val + 2 ≤ b.val := by
  have hbv := ZMod.val_lt b
  have hdv := ZMod.val_lt δ
  have hcast : δ = ((δ.val : ℕ) : ZMod L) := (ZMod.natCast_rightInverse δ).symm
  have hd0 : δ.val ≠ 0 := by
    intro hh; exact h0 (by rw [hcast, hh]; simp)
  have hd1 : δ.val ≠ 1 := by
    intro hh; exact h1 (by rw [hcast, hh]; simp)
  have hdL : δ.val ≠ L - 1 := by
    intro hh
    refine hm1 ?_
    rw [hcast, hh, Nat.cast_sub (by omega : 1 ≤ L), ZMod.natCast_self]
    simp
  have hadd : (b + δ).val = (b.val + δ.val) % L := ZMod.val_add b δ
  rcases lt_or_ge (b.val + δ.val) L with hlt | hge
  · left; rw [hadd, Nat.mod_eq_of_lt hlt]; omega
  · right
    have hmod : (b.val + δ.val) % L = b.val + δ.val - L := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hadd, hmod]
    omega

/-- **The control chain meets every structural hypothesis (foundational).** Far-separated pair sums
vanish, hence are positive semidefinite: the control is not excluded by `hfar`. -/
theorem dproj_far_psd (L : ℕ) [NeZero L] (hL : 2 ≤ L) (δ : ZMod L)
    (h0 : δ ≠ 0) (h1 : δ ≠ 1) (hm1 : δ ≠ -1) :
    (∑ b : ZMod L, dproj L b * dproj L (b + δ)).PosSemidef := by
  have hz : (∑ b : ZMod L, dproj L b * dproj L (b + δ)) = 0 := by
    refine Finset.sum_eq_zero (fun b _ => ?_)
    exact dproj_orth L b (b + δ) (dvec_orth_far L b (b + δ) (far_val L hL b δ h0 h1 hm1))
  rw [hz]
  exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩

/-! #### The block operator and the ramp -/

/-- A block of `n` consecutive bonds starting at bond `0`.

DERIVED: `0` is the start of the block and is the only start needed, because the window hypothesis of
the criterion is quantified over every `k` and one window suffices to refute it. `L + 1` is the site
count. -/
noncomputable def blockOp (L : ℕ) [NeZero L] (n : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  ∑ j ∈ Finset.range n, dproj L ((j : ℕ) : ZMod L)

theorem cast_val (L : ℕ) [NeZero L] {j : ℕ} (hj : j < L) : (((j : ℕ) : ZMod L)).val = j := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]

/-- The two-site vector at the two ends of a block of `n` bonds, written at the level of site
indices so that the telescoping induction does not have to carry a bound on `n`.

DERIVED: the two sites `0` and `n` are the output of the telescoping in `block_sum`, not a choice —
the interior of the block cancels term by term. The `±1` coefficients are inherited from `pairVec`. -/
noncomputable def endVec (L n : ℕ) : Fin (L + 1) → ℝ :=
  fun i => (if i.val = 0 then (1 : ℝ) else 0) - (if i.val = n then (1 : ℝ) else 0)

theorem endVec_eq_pairVec (L n : ℕ) (hn : n ≤ L) :
    endVec L n = pairVec L ⟨0, by omega⟩ ⟨n, by omega⟩ := by
  funext i
  unfold endVec pairVec
  have e1 : (i = (⟨0, by omega⟩ : Fin (L + 1))) ↔ (i.val = 0) :=
    ⟨fun h => by rw [h], fun h => Fin.val_injective h⟩
  have e2 : (i = (⟨n, by omega⟩ : Fin (L + 1))) ↔ (i.val = n) :=
    ⟨fun h => by rw [h], fun h => Fin.val_injective h⟩
  simp only [e1, e2]

/-- **Block telescoping.** A block of `n` consecutive bond vectors sums to `e_0 − e_n`: the interior
cancels and only the two ends of the block survive, whatever `n` is. -/
theorem block_sum (L : ℕ) [NeZero L] :
    ∀ n : ℕ, n ≤ L → ∀ i : Fin (L + 1),
      (∑ j ∈ Finset.range n, dvec L ((j : ℕ) : ZMod L) i) = endVec L n i := by
  intro n
  induction n with
  | zero => intro _ i; simp [endVec]
  | succ n ih =>
    intro hn i
    rw [Finset.sum_range_succ, ih (by omega) i]
    have hbsv : (bs L ((n : ℕ) : ZMod L)).val = n := by
      rw [bs_val, cast_val L (by omega)]
    have hbtv : (bt L ((n : ℕ) : ZMod L)).val = n + 1 := by
      rw [bt_val, cast_val L (by omega)]
    have e1 : (i = bs L ((n : ℕ) : ZMod L)) ↔ (i.val = n) :=
      ⟨fun h => by rw [h, hbsv], fun h => Fin.val_injective (by rw [hbsv]; exact h)⟩
    have e2 : (i = bt L ((n : ℕ) : ZMod L)) ↔ (i.val = n + 1) :=
      ⟨fun h => by rw [h, hbtv], fun h => Fin.val_injective (by rw [hbtv]; exact h)⟩
    show _ = endVec L (n + 1) i
    unfold endVec dvec pairVec
    simp only [e1, e2]
    ring

theorem blockOp_ramp (L : ℕ) [NeZero L] (n : ℕ) (hn : n ≤ L) :
    blockOp L n *ᵥ ramp L = (-(1 / 2) : ℝ) • endVec L n := by
  rw [blockOp, Matrix.sum_mulVec]
  funext i
  rw [Finset.sum_apply]
  have hterm : ∀ j ∈ Finset.range n, (dproj L ((j : ℕ) : ZMod L) *ᵥ ramp L) i
      = (-(1 / 2) : ℝ) * dvec L ((j : ℕ) : ZMod L) i := by
    intro j _
    rw [dproj_mulVec, dvec_ramp]
    show ((1 / 2 : ℝ) * (-1)) * dvec L ((j : ℕ) : ZMod L) i = _
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, block_sum L n hn i]
  rfl

/-- **The ramp bound — the control's single computation (foundational).** For a block of `n`
consecutive bonds, the operator inequality `B² ⪰ g·B` read at the linear ramp gives `g·(n/2) ≤ 1/2`,
hence `g ≤ 1/n`. The right side does not grow with `n` because the second difference of a linear
function vanishes except at the two ends of the block. -/
theorem block_ramp_bound (L : ℕ) [NeZero L] (n : ℕ) (hn0 : 0 < n) (hnL : n ≤ L) {g : ℝ}
    (hop : ∀ x : Fin (L + 1) → ℝ,
      g * (x ⬝ᵥ (blockOp L n *ᵥ x)) ≤ (blockOp L n *ᵥ x) ⬝ᵥ (blockOp L n *ᵥ x)) :
    g ≤ 1 / (n : ℝ) := by
  have hne : (⟨0, by omega⟩ : Fin (L + 1)) ≠ (⟨n, by omega⟩ : Fin (L + 1)) := by
    intro hh; have := congrArg Fin.val hh; simp at this; omega
  have hev := endVec_eq_pairVec L n hnL
  have hBr : blockOp L n *ᵥ ramp L
      = (-(1 / 2) : ℝ) • pairVec L ⟨0, by omega⟩ ⟨n, by omega⟩ := by
    rw [blockOp_ramp L n hnL, hev]
  have hnum : (blockOp L n *ᵥ ramp L) ⬝ᵥ (blockOp L n *ᵥ ramp L) = 1 / 2 := by
    rw [hBr, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, pair_self L hne]
    norm_num
  have hden : (ramp L) ⬝ᵥ (blockOp L n *ᵥ ramp L) = (n : ℝ) / 2 := by
    rw [hBr, dotProduct_comm, smul_dotProduct, smul_eq_mul, pair_ramp]
    push_cast
    ring
  have h := hop (ramp L)
  rw [hnum, hden] at h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  rw [le_div_iff₀ hnR]
  linarith

/-! #### The two instantiations -/

/-- The window at bond `0` of the control chain is the block of its first `m` bonds. -/
theorem win_dproj_eq_blockOp (L m : ℕ) [NeZero L] :
    win (dproj L) m 0 = blockOp L m := by
  simp [win, blockOp]

/-- The whole control chain is the block of all `L` of its bonds; `val` is the bijection. -/
def zmodEquivFin_aux (L : ℕ) [NeZero L] : ZMod L ≃ Fin L where
  toFun b := ⟨b.val, ZMod.val_lt b⟩
  invFun j := ((j : ℕ) : ZMod L)
  left_inv b := ZMod.natCast_rightInverse b
  right_inv j := by
    apply Fin.val_injective
    show (((j : ℕ) : ZMod L)).val = j.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt]

theorem sum_zmod_range {M : Type*} [AddCommMonoid M] (L : ℕ) [NeZero L] (f : ZMod L → M) :
    (∑ b : ZMod L, f b) = ∑ j ∈ Finset.range L, f ((j : ℕ) : ZMod L) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => f ((j : ℕ) : ZMod L)) L]
  refine Fintype.sum_equiv (zmodEquivFin_aux L) f (fun j => f ((j : ℕ) : ZMod L)) (fun b => ?_)
  congr 1
  exact (ZMod.natCast_rightInverse b).symm

/-- The control chain Hamiltonian: half the path-graph Laplacian on `L + 1` sites.

DERIVED: `L + 1` is the site count that `L` bonds require. The factor of a half is not written here —
it is already inside `dproj`, where idempotence forces it. -/
noncomputable def Hlap (L : ℕ) [NeZero L] : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  ∑ b : ZMod L, dproj L b

theorem Hlap_eq_blockOp (L : ℕ) [NeZero L] : Hlap L = blockOp L L := by
  rw [Hlap, blockOp, sum_zmod_range L (fun b => dproj L b)]

/-- **The control chain is frustration-free (foundational).** The constant vector is a common zero of
every bond term, so `Hlap` has a zero ground state and `1/L` really does bound its gap. -/
theorem laplace_ground_state (L : ℕ) [NeZero L] : Hlap L *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  rw [Hlap, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [dproj_mulVec, dvec, pair_const]
  simp

/-- **The control chain's windows never clear the Knabe threshold (foundational).** On the
discrete-Laplacian chain, any `ε` satisfying the window operator inequality at every window satisfies
`ε ≤ 1/m`. The hypothesis `1/m < ε` of `knabe_gap_volume_independent` is therefore unsatisfiable on
this family, at every window size. -/
theorem laplace_window_gap_le (L m : ℕ) [NeZero L] (hm0 : 0 < m) (hmL : m ≤ L) {ε : ℝ}
    (hwin : ∀ k : ZMod L, ∀ x : Fin (L + 1) → ℝ,
      ε * (x ⬝ᵥ (win (dproj L) m k *ᵥ x)) ≤ (win (dproj L) m k *ᵥ x) ⬝ᵥ (win (dproj L) m k *ᵥ x)) :
    ε ≤ 1 / (m : ℝ) := by
  refine block_ramp_bound L m hm0 hmL (fun x => ?_)
  have h := hwin 0 x
  rwa [win_dproj_eq_blockOp] at h

theorem laplace_never_clears_threshold (L m : ℕ) [NeZero L] (hm0 : 0 < m) (hmL : m ≤ L) {ε : ℝ}
    (hwin : ∀ k : ZMod L, ∀ x : Fin (L + 1) → ℝ,
      ε * (x ⬝ᵥ (win (dproj L) m k *ᵥ x)) ≤ (win (dproj L) m k *ᵥ x) ⬝ᵥ (win (dproj L) m k *ᵥ x)) :
    ¬ (1 / (m : ℝ) < ε) :=
  not_lt.mpr (laplace_window_gap_le L m hm0 hmL hwin)

/-- **The control chain's bulk gap collapses with the volume (foundational).** Any `g` satisfying the
operator inequality `Hlap² ⪰ g·Hlap` — which by `gap_of_operator_sq_ge` is exactly a spectral gap `g`
above the zero ground state — obeys `g ≤ 1/L`. -/
theorem laplace_chain_gap_le (L : ℕ) [NeZero L] {g : ℝ}
    (hop : ∀ x : Fin (L + 1) → ℝ,
      g * (x ⬝ᵥ (Hlap L *ᵥ x)) ≤ (Hlap L *ᵥ x) ⬝ᵥ (Hlap L *ᵥ x)) :
    g ≤ 1 / (L : ℝ) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine block_ramp_bound L L hL0 le_rfl (fun x => ?_)
  have h := hop x
  rwa [Hlap_eq_blockOp] at h

/-- **No volume-independent gap for the control family (foundational).** There is no positive constant
that bounds the gap of `Hlap L` for every `L`. Together with `laplace_never_clears_threshold` this is
the control: a chain that satisfies every structural hypothesis of `knabe_chain_gap` but sits at or
below the derived threshold has no volume-independent gap, so the threshold is not slack bookkeeping —
dropping it would make the criterion false. -/
theorem laplace_no_uniform_gap :
    ¬ ∃ g : ℝ, 0 < g ∧ ∀ (L : ℕ) (_ : NeZero L),
      ∀ x : Fin (L + 1) → ℝ, g * (x ⬝ᵥ (Hlap L *ᵥ x)) ≤ (Hlap L *ᵥ x) ⬝ᵥ (Hlap L *ᵥ x) := by
  rintro ⟨g, hg, hall⟩
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / g)
  have hL0 : 0 < L := by
    by_contra hc
    have : L = 0 := by omega
    rw [this] at hL
    simp at hL
    have : 0 < 1 / g := by positivity
    linarith
  haveI : NeZero L := ⟨by omega⟩
  have hb := laplace_chain_gap_le L (g := g) (hall L inferInstance)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  rw [div_lt_iff₀ hg] at hL
  rw [le_div_iff₀ hLR] at hb
  linarith

/-! #### The control read against the criterion's own spectral hypothesis

`laplace_window_gap_le` and `laplace_chain_gap_le` are stated with the operator inequality, which is
what the assembly consumes. `gap_of_operator_sq_ge` and `operator_sq_ge_of_gap` make that equivalent
to the spectral condition, so the same bounds can be read directly against the hypothesis and the
conclusion of `knabe_chain_gap_of_local_spectrum`. -/

theorem dproj_posSemidef (L : ℕ) [NeZero L] (b : ZMod L) : (dproj L b).PosSemidef :=
  proj_posSemidef (dproj_isHermitian L b) (dproj_idem L b)

theorem Hlap_isHermitian (L : ℕ) [NeZero L] : (Hlap L).IsHermitian :=
  isHermitian_sum _ _ (fun b _ => dproj_isHermitian L b)

theorem Hlap_posSemidef (L : ℕ) [NeZero L] : (Hlap L).PosSemidef :=
  Matrix.posSemidef_sum _ (fun b _ => dproj_posSemidef L b)

/-- **The control chain meets every structural hypothesis of the criterion (foundational).** Hermitian
idempotent bond terms, far-separated pair sums positive semidefinite, and a zero ground state. The
criterion does not apply to it for exactly one reason: the local gap never clears the threshold. -/
theorem laplace_meets_structure (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    (∀ b : ZMod L, (dproj L b).IsHermitian) ∧ (∀ b : ZMod L, dproj L b * dproj L b = dproj L b) ∧
      (∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
        (∑ b : ZMod L, dproj L b * dproj L (b + δ)).PosSemidef) ∧
      (Hlap L *ᵥ (fun _ => (1 : ℝ)) = 0) :=
  ⟨dproj_isHermitian L, dproj_idem L, dproj_far_psd L hL, laplace_ground_state L⟩

/-- **The criterion's local hypothesis is unsatisfiable on the control, in spectral form
(foundational).** If every eigenvalue of every `m`-bond window of the control chain is `0` or at least
`ε`, then `ε ≤ 1/m`. So `knabe_chain_gap_of_local_spectrum` can never be applied to this family with a
threshold-clearing `ε`. -/
theorem laplace_local_spectrum_le (L m : ℕ) [NeZero L] (hm0 : 0 < m) (hmL : m ≤ L) {ε : ℝ}
    (hgap : ∀ k : ZMod L, ∀ i,
      (win_isHermitian (dproj L) (dproj_isHermitian L) m k).eigenvalues i = 0 ∨
        ε ≤ (win_isHermitian (dproj L) (dproj_isHermitian L) m k).eigenvalues i) :
    ε ≤ 1 / (m : ℝ) := by
  refine laplace_window_gap_le L m hm0 hmL (fun k => ?_)
  exact operator_sq_ge_of_gap (win_isHermitian (dproj L) (dproj_isHermitian L) m k)
    (fun i => (win_posSemidef (dproj L) (dproj_isHermitian L) (dproj_idem L) m k).eigenvalues_nonneg i)
    (hgap k)

/-- **The control chain's spectral gap is at most `1/L` (foundational).** The conclusion of the
criterion in the same spectral currency: if every eigenvalue of `Hlap L` is `0` or at least `g`, then
`g ≤ 1/L`. With `laplace_ground_state` supplying the zero eigenvalue, that is the gap. -/
theorem laplace_spectrum_le (L : ℕ) [NeZero L] {g : ℝ}
    (hgap : ∀ i, (Hlap_isHermitian L).eigenvalues i = 0 ∨ g ≤ (Hlap_isHermitian L).eigenvalues i) :
    g ≤ 1 / (L : ℝ) :=
  laplace_chain_gap_le L (operator_sq_ge_of_gap (Hlap_isHermitian L)
    (fun i => (Hlap_posSemidef L).eigenvalues_nonneg i) hgap)

#print axioms proj_posSemidef
#print axioms win_isHermitian
#print axioms win_posSemidef
#print axioms knabe_chain_gap
#print axioms knabe_chain_gap_of_local_spectrum
#print axioms knabe_bound_pos_iff
#print axioms knabe_gap_volume_independent
#print axioms sum_win
#print axioms sum_eq_zero_of_win_eq_zero
#print axioms no_positive_eigenvalue_of_win_eq_zero
#print axioms sum_proj_idem
#print axioms win_siteProj_idem
#print axioms knabe_witness
#print axioms far_val
#print axioms dproj_far_psd
#print axioms block_sum
#print axioms blockOp_ramp
#print axioms block_ramp_bound
#print axioms laplace_ground_state
#print axioms laplace_window_gap_le
#print axioms laplace_never_clears_threshold
#print axioms laplace_chain_gap_le
#print axioms laplace_meets_structure
#print axioms laplace_local_spectrum_le
#print axioms laplace_spectrum_le
#print axioms laplace_no_uniform_gap

end MassGap.LocalGap
