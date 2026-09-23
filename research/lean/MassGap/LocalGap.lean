import MassGap.CellCouple

/-!
# MassGap.LocalGap — the Knabe local-gap criterion, its threshold, and a saturating control

Three groups of statements about a nearest-neighbour chain of Hermitian idempotents indexed by
`ZMod L`, acting on `Fin N → ℝ`.

## The criterion

`win h m k` is the window `∑ j ∈ Finset.range m, (1 : ℝ) • h (k + j)`, the `m` consecutive bond terms
starting at bond `k`. `knabe_chain_gap` states: if every bond term is a Hermitian idempotent, every
far-separated pair sum `∑ b, h b * h (b + δ)` with `δ ∉ {0, 1, -1}` is positive semidefinite,
`2 ≤ m`, `2 * m ≤ L`, and every window satisfies `ε * ⟪x, W x⟫ ≤ ⟪W x, W x⟫`, then every positive
eigenvalue of `H = ∑ b, h b` is at least `(m * ε - 1) / (m - 1)`. The bound does not mention `L`.
`knabe_chain_gap_of_local_spectrum` takes the local input in spectral form — every window eigenvalue
is `0` or at least `ε` — through `operator_sq_ge_of_gap`, with positive semidefiniteness of the
windows supplied by `win_posSemidef`.

`knabe_bound_pos_iff` locates the zero of that bound: `0 < (m * ε - 1) / (m - 1)` if and only if
`1 / m < ε`. `knabe_gap_volume_independent` packages the criterion as a single `g > 0` serving every
`L` and every `N`.

`sum_win`, `sum_eq_zero_of_win_eq_zero` and `no_positive_eigenvalue_of_win_eq_zero` close the
degenerate case: the windows sum to `m • H`, so windows that all vanish force `H = 0` and no
eigenvalue is positive. `knabe_witness` exhibits a family meeting every hypothesis at `ε = 1`:
`siteProj L b` is the rank-one projector onto the basis direction `e_{b.val}` in `ℝ^(L+1)`, distinct
bonds are orthogonal, and every window is itself a projector (`win_siteProj_idem`).

## The control

`dproj L b` is the rank-one projector onto `dvec L b = e_{b.val} - e_{b.val+1}`, so
`Hlap L = ∑ b, dproj L b` is half the path-graph Laplacian on `L + 1` sites.
`laplace_meets_structure` records that it satisfies every structural hypothesis of the criterion, and
`laplace_ground_state` that the constant vector is a common zero of every bond term.

`ramp L i = i` is the linear ramp. For a block of `n` consecutive bonds, `block_sum` telescopes the
bond vectors to `e_0 - e_n` and `blockOp_ramp` gives `blockOp L n *ᵥ ramp L = -(1/2) • (e_0 - e_n)`,
so `⟪B r, B r⟫ = 1/2` while `⟪r, B r⟫ = n / 2`. Reading `B ^ 2 ⪰ g * B` at `r` therefore gives
`g ≤ 1 / n` (`block_ramp_bound`). At `n = m` that is `laplace_window_gap_le` and
`laplace_never_clears_threshold`; at `n = L` it is `laplace_chain_gap_le`, and
`laplace_no_uniform_gap` follows. `laplace_local_spectrum_le` and `laplace_spectrum_le` restate the
two in the spectral currency of `knabe_chain_gap_of_local_spectrum`.

## Scope

Every theorem here is about a chain of Hermitian idempotents whose far-separated terms commute.
Frustration-freeness — the ground state minimising each local term separately — is a restriction on
the family, not a normalisation. `Transfer.TransferData` carries a self-adjoint contraction on a GNS
quotient rather than a sum of projectors, and the Kogut–Susskind Hamiltonian
`(g²/2) ∑ E² - (1/g²) ∑ Re tr U_p` has an electric and a magnetic term that do not commute. Nothing
here supplies a projector-chain presentation of either.
-/

namespace MassGap.LocalGap

open scoped Matrix
open Matrix
open MassGap.CellEnclosure

/-! ### The window, and its elementary properties -/

/-- `∑ j ∈ Finset.range m, (1 : ℝ) • h (k + j)`: the `m` consecutive bond terms starting at bond `k`.
The scalar is written explicitly so that this is the same term as the deformed window of
`CellSpectrum.gm_gap_c1` at unit weights.

Scope: the sum is over `Finset.range m` with the index added in `ZMod L`, so it wraps when
`m` exceeds `L`.

DERIVED: no numeral appears in the type. In the body, `1` is the Gosset–Mozgunov deformation
coefficient at its undeformed value; it is what makes the window autocorrelation `A_x = m - x`, the
input `CellSpectrum.hnn_c1` accepts, and what turns `gm_gap_c1`'s bound into `(m * ε - 1)/(m - 1)`. -/
noncomputable def win {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ)
    (k : ZMod L) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ j ∈ Finset.range m, (1 : ℝ) • h (k + (j : ZMod L))

/-- A Hermitian idempotent is positive semidefinite. `Matrix.posSemidef_conjTranspose_mul_self`
gives `Pᴴ * P` positive semidefinite, and the two hypotheses rewrite that to `P`.

DERIVED: no numeral appears in the statement. -/
theorem proj_posSemidef {N : ℕ} {P : Matrix (Fin N) (Fin N) ℝ} (hP : P.IsHermitian)
    (hPi : P * P = P) : P.PosSemidef := by
  have hs := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hPi] at hs

/-- `(win h m k).IsHermitian` when every bond term is Hermitian: a finite sum of Hermitian matrices,
with the unit scalar removed by `one_smul`.

DERIVED: no numeral appears in the statement. -/
theorem win_isHermitian {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (m : ℕ) (k : ZMod L) : (win h m k).IsHermitian :=
  isHermitian_sum _ _ (fun j _ => by rw [one_smul]; exact hherm _)

/-- `(win h m k).PosSemidef` when every bond term is a Hermitian idempotent: a finite sum of positive
semidefinite matrices by `proj_posSemidef`. Its eigenvalues are therefore nonnegative, which is the
`hpsd` input `CellSpectrum.operator_sq_ge_of_gap` takes, so that hypothesis need not be assumed
separately.

DERIVED: no numeral appears in the statement. -/
theorem win_posSemidef {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (hherm : ∀ b, (h b).IsHermitian) (hproj : ∀ b, h b * h b = h b) (m : ℕ) (k : ZMod L) :
    (win h m k).PosSemidef :=
  Matrix.posSemidef_sum _ (fun j _ => by
    rw [one_smul]; exact proj_posSemidef (hherm _) (hproj _))

/-! ### The criterion, its threshold, and the degenerate case -/

/-- For a chain `h : ZMod L → Matrix (Fin N) (Fin N) ℝ` of Hermitian idempotents whose far-separated
pair sums `∑ b, h b * h (b + δ)` are positive semidefinite for every `δ` outside `{0, 1, -1}`, with
`2 ≤ m` and `2 * m ≤ L`: if every `m`-bond window satisfies
`ε * (x ⬝ᵥ (W *ᵥ x)) ≤ (W *ᵥ x) ⬝ᵥ (W *ᵥ x)` at every `x`, then every eigenvalue `lam > 0` of
`∑ b, h b` satisfies `(m * ε - 1) / (m - 1) ≤ lam`.

The proof is `CellSpectrum.gm_gap_c1` at unit weights, with the bound rewritten by `field_simp`.

Scope: frustration-freeness is not among the hypotheses. The bound does not mention `L`; the chain
length enters only through `2 * m ≤ L`, which makes the windows fit twice. `ε` is not assumed
positive, and the conclusion is about positive eigenvalues only.

DERIVED: `2` occurs twice, as the lower bound on the window size `m` and as the factor in
`2 * m ≤ L`. `0` occurs three times — the offset excluded in `hfar`, the value `ψ ⬝ᵥ ψ` is assumed to
differ from, and the strict lower bound on the eigenvalue. `1` occurs four times — the two offsets
`1` and `-1` excluded in `hfar`, and the `- 1` in the numerator and in the denominator of the bound,
both of which come from `gm_gap_c1`'s own shape. -/
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

/-- `knabe_chain_gap` with the local hypothesis in spectral form: every eigenvalue of every `m`-bond
window is `0` or at least `ε`. `win_posSemidef` supplies the nonnegativity and
`CellSpectrum.operator_sq_ge_of_gap` converts the spectral condition to the operator inequality.

Scope: as `knabe_chain_gap`; the window's positive semidefiniteness is derived from the bond terms
being Hermitian idempotents rather than assumed.

DERIVED: `2` occurs twice, as the lower bound on `m` and as the factor in `2 * m ≤ L`. `0` occurs
four times — the offset excluded in `hfar`, the eigenvalue alternative in `hgap`, the value `ψ ⬝ᵥ ψ`
differs from, and the strict lower bound on `lam`. `1` occurs four times — the offsets `1` and `-1`
in `hfar`, and the `- 1` in the numerator and denominator of the bound. -/
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

/-- For `2 ≤ m`, `0 < (m * ε - 1) / (m - 1) ↔ 1 / m < ε`. The denominator is positive by `2 ≤ m`, so
`div_pos_iff` leaves only the numerator, and `div_lt_iff₀` rearranges it.

So `1 / m` is the zero of `knabe_chain_gap`'s bound, with the window size `m` the only parameter.

DERIVED: `2` is the lower bound on `m`, which makes the denominator `m - 1` positive; `0` is the
comparison point on the left; `1` occurs three times — the `- 1` in the numerator, the `- 1` in the
denominator, and the numerator of the threshold `1 / m`. -/
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

/-- For a window size `m ≥ 2` and a local gap `ε` with `1 / m < ε`, there is a single `g > 0` — the
value `(m * ε - 1) / (m - 1)` — bounding every positive eigenvalue of `∑ b, h b` for EVERY chain
satisfying the hypotheses, at every chain length `L` and every state-space dimension `N`. Positivity
of `g` is `knabe_bound_pos_iff`; the bound is `knabe_chain_gap`.

Scope: `g` is chosen before `N` and `L` are quantified, which is the content. `CellCouple`'s
`chain_budget_fails` is the corresponding statement for the operator-norm route, where the residual
carries a bond count.

DERIVED: `2` occurs twice, as the lower bound on `m` and as the factor in `2 * m ≤ L`. `1` occurs
three times — the numerator of the threshold `1 / m`, and the offsets `1` and `-1` excluded in the
far-separation hypothesis. `0` occurs four times — the strict lower bound on `g`, the offset `0`
excluded in that hypothesis, the value `ψ ⬝ᵥ ψ` differs from, and the strict lower bound on `lam`.
The two `- 1`s of the witness bound appear in the proof, not in the statement. -/
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

/-! ### The degenerate case: vanishing windows

The window hypothesis holds for every `ε` when the windows are zero. The three theorems below close
that case: the windows sum to `m • H`, so windows that all vanish force `H = 0`, and then no
eigenvalue is positive and `knabe_chain_gap`'s hypothesis `0 < lam` cannot be met. -/

/-- `(∑ k : ZMod L, win h m k) = (m : ℝ) • (∑ b, h b)`: every bond term lies in exactly `m` windows.
It is `CellSpectrum.weighted_window_sum` at unit weights, with the constant sum evaluated.

DERIVED: no numeral appears in the statement. -/
theorem sum_win {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (∑ k : ZMod L, win h m k) = (m : ℝ) • (∑ b, h b) := by
  have hw := weighted_window_sum h m (fun _ => (1 : ℝ))
  simpa [win, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hw

/-- If `0 < m` and every window `win h m k` is `0`, then `∑ b, h b = 0`. `sum_win` makes the left
side `(m : ℝ) • ∑ b, h b`, and `m` is nonzero as a real.

DERIVED: `0` occurs three times — the strict lower bound on `m`, the value every window is assumed to
take, and the value the chain sum is shown to take. -/
theorem sum_eq_zero_of_win_eq_zero {N L : ℕ} [NeZero L] (h : ZMod L → Matrix (Fin N) (Fin N) ℝ)
    (m : ℕ) (hm : 0 < m) (hzero : ∀ k, win h m k = 0) : (∑ b, h b) = 0 := by
  have hsum := sum_win h m
  rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const, smul_zero] at hsum
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := hsum.symm
  simpa [smul_eq_zero, hmne] using this

/-- If `0 < m`, every window is `0`, and `(∑ b, h b) *ᵥ ψ = lam • ψ` with `ψ ⬝ᵥ ψ ≠ 0`, then
`lam = 0`. `sum_eq_zero_of_win_eq_zero` makes the left side zero, so `lam • ψ = 0`; `ψ` is nonzero by
`hψ0`, hence `lam` is.

Together with the previous theorem this rules out satisfying `knabe_chain_gap`'s window hypothesis
vacuously: with degenerate windows its hypothesis `0 < lam` cannot be met.

DERIVED: `0` occurs four times — the strict lower bound on `m`, the value every window takes, the
value `ψ ⬝ᵥ ψ` differs from, and the value concluded for `lam`. -/
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

/-- `Nonempty (ZMod L)` for `L` nonzero, witnessed by `0`. The window index type of
`knabe_chain_gap` is therefore inhabited.

DERIVED: no numeral appears in the statement; the witness `0` is in the proof term. -/
theorem win_family_nonempty {L : ℕ} [NeZero L] : Nonempty (ZMod L) :=
  ⟨0⟩

/-! ### A family satisfying the criterion's hypotheses

`siteProj L b` is the rank-one projector onto the basis direction `e_{b.val}` in `ℝ^(L+1)`. Its bond
terms are pairwise distinct and pairwise orthogonal, all the structural hypotheses hold, every window
is itself a projector — so the window inequality holds at `ε = 1` with equality — and `1 / m < 1` for
every `m ≥ 2`. -/

/-- Distinct elements of `ZMod L` have distinct `val`s, since `ZMod.natCast_rightInverse` recovers
each from its value.

DERIVED: no numeral appears in the statement. -/
theorem zmod_val_ne {L : ℕ} [NeZero L] {b c : ZMod L} (hbc : b ≠ c) : b.val ≠ c.val := by
  intro hv
  apply hbc
  calc b = ((b.val : ℕ) : ZMod L) := (ZMod.natCast_rightInverse b).symm
    _ = ((c.val : ℕ) : ZMod L) := by rw [hv]
    _ = c := ZMod.natCast_rightInverse c

/-- If the `P i` for `i ∈ s` are idempotent and pairwise orthogonal (`P i * P j = 0` for `i ≠ j`),
then `(∑ i ∈ s, P i)` is idempotent. Expanding by `Finset.sum_mul_sum`, each row collapses to its
diagonal term.

DERIVED: `0` is the value of each off-diagonal product, which is what orthogonality means here. -/
theorem sum_proj_idem {N : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → Matrix (Fin N) (Fin N) ℝ) (hidem : ∀ i ∈ s, P i * P i = P i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    (∑ i ∈ s, P i) * (∑ i ∈ s, P i) = ∑ i ∈ s, P i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
    (fun hns => absurd hi hns)]
  exact hidem i hi

/-- The diagonal matrix on `Fin (L + 1)` with entry `1` at index `b.val` and `0` elsewhere: the
rank-one projector onto the basis direction `e_{b.val}`. `siteProj_isHermitian`, `siteProj_idem` and
`siteProj_orth` record that it is Hermitian, idempotent, and orthogonal to `siteProj L c` for
`c ≠ b`.

DERIVED: `1` occurs twice in the type, as the `+ 1` in the site count `Fin (L + 1)` at each index; in
the body, `1` and `0` are the two diagonal entries an idempotent diagonal matrix can carry, with `1`
on the single site the bond reads. -/
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

/-- For `m ≤ L`, every window of `siteProj L` is itself idempotent. The `m` bond indices it covers
are distinct residues — `add_left_cancel` plus `ZMod.val_natCast` under `m ≤ L` — so the rank-one
terms are pairwise orthogonal and `sum_proj_idem` applies.

Scope: `m ≤ L` is what makes the indices distinct; without it the window would revisit a bond and the
sum would not be idempotent.

DERIVED: no numeral appears in the statement. -/
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

/-- For a Hermitian idempotent `W`, `(1 : ℝ) * (x ⬝ᵥ (W *ᵥ x)) ≤ (W *ᵥ x) ⬝ᵥ (W *ᵥ x)` at every `x`,
with equality: moving `W` across the inner product by `CellSpectrum.sadj` turns the right side into
`x ⬝ᵥ ((W * W) *ᵥ x)`, which idempotence collapses.

DERIVED: `1` is the value of `ε` at which the window inequality holds, forced by idempotence rather
than chosen. -/
theorem op_sq_ge_one_of_proj {N : ℕ} {W : Matrix (Fin N) (Fin N) ℝ} (hW : W.IsHermitian)
    (hWi : W * W = W) (x : Fin N → ℝ) :
    (1 : ℝ) * (x ⬝ᵥ (W *ᵥ x)) ≤ (W *ᵥ x) ⬝ᵥ (W *ᵥ x) := by
  have h1 : (W *ᵥ x) ⬝ᵥ (W *ᵥ x) = x ⬝ᵥ ((W * W) *ᵥ x) := by
    rw [sadj hW, mulVec_mulVec]
  rw [h1, hWi, one_mul]

/-- For every `m ≥ 2` and `L ≥ 2 * m`, the hypotheses of `knabe_chain_gap` are jointly satisfiable:
there are a chain `h`, a vector `ψ`, an eigenvalue `lam` and a local gap `ε` with all the structural
conditions, `1 / m < ε`, `(∑ b, h b) *ᵥ ψ = lam • ψ`, `ψ ⬝ᵥ ψ ≠ 0`, `0 < lam`, and a strictly
positive bound `(m * ε - 1) / (m - 1)`.

The witness is `h := siteProj L`, `ψ := Pi.single ⟨0, _⟩ 1`, `lam := 1` and `ε := 1`. Far-separated
pair sums vanish by `siteProj_orth`, the window inequality is `op_sq_ge_one_of_proj` at
`win_siteProj_idem`, and the eigenvector computation isolates the bond at residue `0`.

Scope: the bond terms are pairwise distinct projectors, not one term repeated.

DERIVED: `2` occurs twice, as the lower bound on `m` and as the factor in `2 * m ≤ L`. `1` occurs
nine times — four as the `+ 1` in the site count `Fin (L + 1)` (in the matrix type twice, in `ψ`'s
type, and in the window hypothesis's vector type), the offsets `1` and `-1` excluded in the
far-separation hypothesis, the numerator of the threshold `1 / m`, and the `- 1` in the numerator and
in the denominator of the final bound. `0` occurs four times — the offset `0` excluded in the
far-separation hypothesis, the value `ψ ⬝ᵥ ψ` differs from, the strict lower bound on `lam`, and the
strict lower bound on the final bound. -/
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

/-! ### The discrete-Laplacian chain, which sits at the threshold

Bond `b` carries the rank-one projector onto `e_{b.val} - e_{b.val+1}` in `ℝ^(L+1)`, so
`Hlap L = ∑ b, dproj L b` is half the path-graph Laplacian on `L + 1` sites. It meets every
structural hypothesis of `knabe_chain_gap`: Hermitian idempotent terms, far-separated terms
annihilating one another, and the constant vector a common zero.

The linear ramp `r i = i` is annihilated by the second difference in the interior of any block of
consecutive bonds, so the block operator sends it to a fixed two-site vector whatever the block
length. The numerator of the Rayleigh quotient therefore stays at `1/2` while the denominator grows
like the block length. -/

/-- The two-site vector `e_p - e_q` on `Fin (L + 1)`, as
`fun i => (if i = p then 1 else 0) - (if i = q then 1 else 0)`. `pair_self` computes its self-product
as `2` for `p ≠ q`, which is what fixes the coefficient in `dproj` by idempotence.

DERIVED: `1` occurs twice in the type, as the `+ 1` in the site count `Fin (L + 1)` at the domain and
at the index type. In the body, the two `1`s are the coefficients at `p` and at `q` (the latter
negated), and the two `0`s are the value at every other site — the statement that the vector reads
only those two sites. -/
noncomputable def pairVec (L : ℕ) (p q : Fin (L + 1)) : Fin (L + 1) → ℝ :=
  fun i => (if i = p then (1 : ℝ) else 0) - (if i = q then (1 : ℝ) else 0)

/-- The left end of bond `b`, as the index `b.val` in `Fin (L + 1)`. The bound `ZMod.val_lt` places
it in range.

DERIVED: `1` is the `+ 1` in the site count `Fin (L + 1)`: `L + 1` sites carry `L` bonds, so
`b.val < L` puts both `b.val` and `b.val + 1` in range. -/
def bs (L : ℕ) [NeZero L] (b : ZMod L) : Fin (L + 1) :=
  ⟨b.val, by have := ZMod.val_lt b; omega⟩

/-- The right end of bond `b`, as the index `b.val + 1` in `Fin (L + 1)`.

DERIVED: `1` in the type is the `+ 1` in the site count `Fin (L + 1)`; the `+ 1` in the body is the
offset that makes the bond nearest-neighbour, matching the offsets `knabe_chain_gap`'s `hfar`
hypothesis excludes. -/
def bt (L : ℕ) [NeZero L] (b : ZMod L) : Fin (L + 1) :=
  ⟨b.val + 1, by have := ZMod.val_lt b; omega⟩

theorem bs_val (L : ℕ) [NeZero L] (b : ZMod L) : (bs L b).val = b.val := rfl
theorem bt_val (L : ℕ) [NeZero L] (b : ZMod L) : (bt L b).val = b.val + 1 := rfl

/-- `pairVec L (bs L b) (bt L b)`: the two-site vector at the two ends of bond `b`, that is
`e_{b.val} - e_{b.val+1}`. `dvec_self` computes its self-product as `2`.

DERIVED: `1` is the `+ 1` in the site count `Fin (L + 1)`; the remaining literals are inside `bs`,
`bt` and `pairVec`. -/
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

/-- `fun i => (i.val : ℝ)` on `Fin (L + 1)`: the linear ramp. Its discrete second difference
vanishes, which is why `blockOp_ramp` leaves only the two ends of a block.

DERIVED: `1` is the `+ 1` in the site count `Fin (L + 1)`. The ramp is not a fitted trial vector —
up to affine changes, which the block operator annihilates, it is the shape whose second difference
vanishes. -/
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

/-- `Matrix.of fun i j => (1 / 2 : ℝ) * (dvec L b i * dvec L b j)`: the rank-one projector onto
`dvec L b = e_{b.val} - e_{b.val+1}`. `dproj_isHermitian`, `dproj_idem` and `dproj_orth` record
Hermiticity, idempotence, and orthogonality for bonds whose vectors are orthogonal.

DERIVED: `1` occurs twice in the type, as the `+ 1` in the site count `Fin (L + 1)` at each index. In
the body, `1` and `2` are the coefficient `1 / 2`, which is forced: `dvec_self` gives
`dvec ⬝ᵥ dvec = 2`, so `c • (v vᵀ)` is idempotent exactly at `c = 1 / 2`. -/
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

/-- `(dvec L b) ⬝ᵥ (dvec L c) = 0` when the two bonds' left ends are at least two apart in either
direction. Each site index is handled in turn: at the two ends of bond `b` the vector of bond `c`
vanishes, and elsewhere so does that of bond `b`.

DERIVED: `2` occurs twice, as the separation in each disjunct of the hypothesis — two apart is what
makes the two-site supports disjoint; `0` is the value of the inner product. -/
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

/-- For `2 ≤ L` and an offset `δ` outside `{0, 1, -1}` in `ZMod L`, the bonds `b` and `b + δ` have
left ends at least two apart in one direction or the other. The proof converts the three exclusions
into `δ.val ∉ {0, 1, L - 1}` and splits on whether `b.val + δ.val` wraps.

DERIVED: `2` occurs three times — the lower bound on `L`, and the separation in each disjunct of the
conclusion; `0` and `1` are two of the three excluded offsets, the third being `-1`. -/
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

/-- For `2 ≤ L` and an offset `δ` outside `{0, 1, -1}`, `∑ b : ZMod L, dproj L b * dproj L (b + δ)`
is positive semidefinite — in fact zero, by `far_val`, `dvec_orth_far` and `dproj_orth`. So the
discrete-Laplacian chain satisfies `knabe_chain_gap`'s far-separation hypothesis.

DERIVED: `2` is the lower bound on `L`; `0` and `1` are two of the three excluded offsets, the third
being `-1`. -/
theorem dproj_far_psd (L : ℕ) [NeZero L] (hL : 2 ≤ L) (δ : ZMod L)
    (h0 : δ ≠ 0) (h1 : δ ≠ 1) (hm1 : δ ≠ -1) :
    (∑ b : ZMod L, dproj L b * dproj L (b + δ)).PosSemidef := by
  have hz : (∑ b : ZMod L, dproj L b * dproj L (b + δ)) = 0 := by
    refine Finset.sum_eq_zero (fun b _ => ?_)
    exact dproj_orth L b (b + δ) (dvec_orth_far L b (b + δ) (far_val L hL b δ h0 h1 hm1))
  rw [hz]
  exact ⟨Matrix.isHermitian_zero, fun x => by simp⟩

/-! #### The block operator, the ramp, and the bound they give -/

/-- `∑ j ∈ Finset.range n, dproj L (j : ZMod L)`: the block of `n` consecutive bond terms starting at
bond `0`. `win_dproj_eq_blockOp` identifies it with the window at `k = 0`, and `Hlap_eq_blockOp` with
the whole chain at `n = L`.

Scope: only the block starting at `0` is needed, because the criterion's window hypothesis is
quantified over every `k` and one window bounds `ε`.

DERIVED: `1` occurs twice in the type, as the `+ 1` in the site count `Fin (L + 1)` at each index.
The start index `0` is in the body. -/
noncomputable def blockOp (L : ℕ) [NeZero L] (n : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  ∑ j ∈ Finset.range n, dproj L ((j : ℕ) : ZMod L)

theorem cast_val (L : ℕ) [NeZero L] {j : ℕ} (hj : j < L) : (((j : ℕ) : ZMod L)).val = j := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]

/-- `fun i => (if i.val = 0 then 1 else 0) - (if i.val = n then 1 else 0)`: the two-site vector at the
ends of a block of `n` bonds, written on site indices so that the induction in `block_sum` carries no
bound on `n`. `endVec_eq_pairVec` identifies it with `pairVec L 0 n` when `n ≤ L`.

DERIVED: `1` in the type is the `+ 1` in the site count `Fin (L + 1)`. In the body, the two sites
`0` and `n` are what the telescoping in `block_sum` leaves — the interior cancels term by term — and
the two `1`s and two `0`s are the coefficients at and off those sites, inherited from `pairVec`. -/
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

/-- For `n ≤ L`, `∑ j ∈ Finset.range n, dvec L (j : ZMod L) i = endVec L n i` at every site `i`:
the block of `n` consecutive bond vectors telescopes to `e_0 - e_n`. Induction on `n`, with the
index identities `cast_val`, `bs_val` and `bt_val` at each step.

DERIVED: `1` is the `+ 1` in the site count `Fin (L + 1)`. -/
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

/-- For `0 < n ≤ L`, any `g` satisfying
`g * (x ⬝ᵥ (blockOp L n *ᵥ x)) ≤ (blockOp L n *ᵥ x) ⬝ᵥ (blockOp L n *ᵥ x)` at every `x` satisfies
`g ≤ 1 / n`.

Read at the ramp: `blockOp_ramp` gives `blockOp L n *ᵥ ramp L = -(1/2) • (e_0 - e_n)`, so
`pair_self` makes the right side `1 / 2` and `pair_ramp` makes the left side `g * (n / 2)`.
The right side does not grow with `n`, because the second difference of a linear function vanishes
away from the two ends of the block.

Scope: the hypothesis is required at every `x`, but only the ramp is used.

DERIVED: `0` is the strict lower bound on the block length `n`; `1` occurs twice, as the `+ 1` in the
site count `Fin (L + 1)` and as the numerator of the bound `1 / n`. The `1 / 2` of the computation
lives in the proof. -/
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

/-! #### The bound at `n = m` and at `n = L` -/

/-- `win (dproj L) m 0 = blockOp L m`: the window at bond `0` is the block of the first `m` bonds, by
`simp` on both definitions.

DERIVED: `0` is the window's starting bond. -/
theorem win_dproj_eq_blockOp (L m : ℕ) [NeZero L] :
    win (dproj L) m 0 = blockOp L m := by
  simp [win, blockOp]

/-- The equivalence `ZMod L ≃ Fin L` sending `b` to `⟨b.val, ZMod.val_lt b⟩`, with inverse the
natural-number cast. It is what `sum_zmod_range` uses to rewrite a sum over `ZMod L` as a sum over
`Finset.range L`, and hence `Hlap_eq_blockOp`.

DERIVED: no numeral appears in the statement. -/
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

/-- `∑ b : ZMod L, dproj L b`: the chain Hamiltonian, which is half the path-graph Laplacian on
`L + 1` sites. `Hlap_eq_blockOp` identifies it with `blockOp L L`.

DERIVED: `1` occurs twice in the type, as the `+ 1` in the site count `Fin (L + 1)` at each index:
`L` bonds require `L + 1` sites. The factor of a half is inside `dproj`, where idempotence forces
it. -/
noncomputable def Hlap (L : ℕ) [NeZero L] : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  ∑ b : ZMod L, dproj L b

theorem Hlap_eq_blockOp (L : ℕ) [NeZero L] : Hlap L = blockOp L L := by
  rw [Hlap, blockOp, sum_zmod_range L (fun b => dproj L b)]

/-- `Hlap L *ᵥ (fun _ => 1) = 0`: the constant vector is annihilated by every bond term, since
`pair_const` makes `dvec L b ⬝ᵥ 1` vanish. So `Hlap L` has a zero eigenvalue, which is what makes
`laplace_chain_gap_le`'s bound a bound on a gap above a ground state rather than on a spectrum with
no zero in it.

DERIVED: `1` is the value of the constant vector; `0` is the value of the product. -/
theorem laplace_ground_state (L : ℕ) [NeZero L] : Hlap L *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  rw [Hlap, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [dproj_mulVec, dvec, pair_const]
  simp

/-- For `0 < m ≤ L`, any `ε` satisfying the window operator inequality at every window of
`dproj L` satisfies `ε ≤ 1 / m`. It is `block_ramp_bound` at `n := m`, with
`win_dproj_eq_blockOp` identifying the window at bond `0` with the block.

So the hypothesis `1 / m < ε` of `knabe_gap_volume_independent` cannot be met on this family, at any
window size. `laplace_never_clears_threshold` states that directly.

DERIVED: `0` is the strict lower bound on `m`; `1` occurs twice, as the `+ 1` in the site count
`Fin (L + 1)` and as the numerator of the bound `1 / m`. -/
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

/-- Any `g` satisfying `g * (x ⬝ᵥ (Hlap L *ᵥ x)) ≤ (Hlap L *ᵥ x) ⬝ᵥ (Hlap L *ᵥ x)` at every `x`
satisfies `g ≤ 1 / L`. It is `block_ramp_bound` at `n := L`, with `Hlap_eq_blockOp` identifying the
whole chain with the block of all its bonds.

`CellSpectrum.gap_of_operator_sq_ge` makes that operator inequality a spectral gap `g` above the zero
ground state, which `laplace_ground_state` supplies.

DERIVED: `1` occurs twice, as the `+ 1` in the site count `Fin (L + 1)` and as the numerator of the
bound `1 / L`. -/
theorem laplace_chain_gap_le (L : ℕ) [NeZero L] {g : ℝ}
    (hop : ∀ x : Fin (L + 1) → ℝ,
      g * (x ⬝ᵥ (Hlap L *ᵥ x)) ≤ (Hlap L *ᵥ x) ⬝ᵥ (Hlap L *ᵥ x)) :
    g ≤ 1 / (L : ℝ) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine block_ramp_bound L L hL0 le_rfl (fun x => ?_)
  have h := hop x
  rwa [Hlap_eq_blockOp] at h

/-- There is no `g > 0` satisfying the operator inequality for `Hlap L` at every `L`. Taking `L`
above `1 / g`, `laplace_chain_gap_le` gives `g ≤ 1 / L < g`.

Together with `laplace_never_clears_threshold`, this chain satisfies every structural hypothesis of
`knabe_chain_gap` and has no volume-independent gap, so the threshold `1 / m` cannot be dropped from
the criterion.

DERIVED: `0` is the strict lower bound on `g`; `1` is the `+ 1` in the site count `Fin (L + 1)`. -/
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

/-! #### The same bounds in spectral form

`laplace_window_gap_le` and `laplace_chain_gap_le` are stated with the operator inequality.
`CellSpectrum.gap_of_operator_sq_ge` and `operator_sq_ge_of_gap` relate that to the spectral
condition, so the same bounds read directly against the hypothesis and the conclusion of
`knabe_chain_gap_of_local_spectrum`. -/

theorem dproj_posSemidef (L : ℕ) [NeZero L] (b : ZMod L) : (dproj L b).PosSemidef :=
  proj_posSemidef (dproj_isHermitian L b) (dproj_idem L b)

theorem Hlap_isHermitian (L : ℕ) [NeZero L] : (Hlap L).IsHermitian :=
  isHermitian_sum _ _ (fun b _ => dproj_isHermitian L b)

theorem Hlap_posSemidef (L : ℕ) [NeZero L] : (Hlap L).PosSemidef :=
  Matrix.posSemidef_sum _ (fun b _ => dproj_posSemidef L b)

/-- Four facts about `dproj L`, conjoined, for `2 ≤ L`: every bond term is Hermitian; every bond term
is idempotent; every far-separated pair sum is positive semidefinite; and the constant vector is
annihilated by `Hlap L`. These are `dproj_isHermitian`, `dproj_idem`, `dproj_far_psd` and
`laplace_ground_state`.

So the family satisfies every structural hypothesis of `knabe_chain_gap`; what it does not satisfy is
the local-gap hypothesis, by `laplace_window_gap_le`.

DERIVED: `2` is the lower bound on `L`, inherited from `dproj_far_psd`; `0` occurs twice, as the
excluded offset in the far-separation clause and as the value of `Hlap L` on the constant vector; `1`
occurs three times — two of the three excluded offsets (`1` and `-1`) and the value of the constant
vector. -/
theorem laplace_meets_structure (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    (∀ b : ZMod L, (dproj L b).IsHermitian) ∧ (∀ b : ZMod L, dproj L b * dproj L b = dproj L b) ∧
      (∀ δ : ZMod L, δ ≠ 0 → δ ≠ 1 → δ ≠ -1 →
        (∑ b : ZMod L, dproj L b * dproj L (b + δ)).PosSemidef) ∧
      (Hlap L *ᵥ (fun _ => (1 : ℝ)) = 0) :=
  ⟨dproj_isHermitian L, dproj_idem L, dproj_far_psd L hL, laplace_ground_state L⟩

/-- For `0 < m ≤ L`, if every eigenvalue of every `m`-bond window of `dproj L` is `0` or at least
`ε`, then `ε ≤ 1 / m`. `CellSpectrum.operator_sq_ge_of_gap` converts the spectral condition to the
operator inequality — the windows are positive semidefinite by `win_posSemidef` — and
`laplace_window_gap_le` bounds it.

So `knabe_chain_gap_of_local_spectrum` cannot be applied to this family with an `ε` above `1 / m`.

DERIVED: `0` occurs twice, as the strict lower bound on `m` and as the eigenvalue alternative in
`hgap`; `1` occurs twice, as the `+ 1` in the site count `Fin (L + 1)` inside the window's matrix
type and as the numerator of the bound `1 / m`. -/
theorem laplace_local_spectrum_le (L m : ℕ) [NeZero L] (hm0 : 0 < m) (hmL : m ≤ L) {ε : ℝ}
    (hgap : ∀ k : ZMod L, ∀ i,
      (win_isHermitian (dproj L) (dproj_isHermitian L) m k).eigenvalues i = 0 ∨
        ε ≤ (win_isHermitian (dproj L) (dproj_isHermitian L) m k).eigenvalues i) :
    ε ≤ 1 / (m : ℝ) := by
  refine laplace_window_gap_le L m hm0 hmL (fun k => ?_)
  exact operator_sq_ge_of_gap (win_isHermitian (dproj L) (dproj_isHermitian L) m k)
    (fun i => (win_posSemidef (dproj L) (dproj_isHermitian L) (dproj_idem L) m k).eigenvalues_nonneg i)
    (hgap k)

/-- If every eigenvalue of `Hlap L` is `0` or at least `g`, then `g ≤ 1 / L`. It is
`CellSpectrum.operator_sq_ge_of_gap` — with nonnegativity from `Hlap_posSemidef` — followed by
`laplace_chain_gap_le`.

`laplace_ground_state` supplies the zero eigenvalue, so this bounds the gap above a ground state.

DERIVED: `0` is the eigenvalue alternative in `hgap`; `1` is the numerator of the bound `1 / L`. -/
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
