import Mathlib
import MassGap.CountMoments
import MassGap.FreeLevels

/-!
# MassGap.ApertureFinite — a finite aperture holds a finite count

The input H3 of `CountMoments` is `CountBoundG`: the Rényi-½ count `spRenyi` of the observer's screen, a box of
fixed physical side `ρ` (`L_k = ⌈ρ / a_k⌉` sites per side), bounded along the zoom. This module proves the count
mechanism on the box itself, for any state, and moves the heat screen's count onto one inequality (`BareRatio`) on
the bare plaquette field. The heat screen is not `CountBoundG`. Declarations are in the namespace `MassGap.ApertureFinite`.

## 1. The count is at most the count of any diagonal (proved)

`sum_sqrt_le_of_mix` (scalar): if `q` is doubly stochastic and `∑_α q_{αβ} λ_α ≤ μ_β`, then
`∑ √λ ≤ ∑ √μ`. Per mode `2√λ ≤ tλ + 1/t` with `t = ∑_β q_{αβ} / √(μ_β + ε)` and `1/t ≤ ∑_β q_{αβ} √(μ_β + ε)`
(Cauchy–Schwarz); summing and letting `ε → 0`.

`spRenyi_eig_le_frame`: for every orthonormal frame `w` of the screen's index set and weights `g` with
`ν((∑_y w_{yβ} F_y)²) ≤ g_β`, `spRenyi (eig ν F) ≤ (∑_β √g_β)² / ∑_y ν(F_y²)`. `spRenyi_eig_le_diag`: at
`g_β = ν((∑_y w_{yβ} F_y)²)`, the count of the Gram spectrum is at most the count of the Gram diagonal in the frame
`w`. The overlaps `q_{αβ} = ⟨e_α, w_β⟩²` of the Gram eigenbasis with the frame are the doubly stochastic matrix.
No translation invariance and no periodic box enter.

## 2. The Dirichlet frame of the box (proved)

`sinF K n j = √(2/(K+1)) sin(π (j+1)(n+1)/(K+1))` on `Fin K`: `sinF_cols`, `sinF_rows` (orthonormal columns from the
cosine sum `cos_sum`, rows from `mul_eq_one_comm`). `boxF K y β = ∏_μ sinF K (y_μ) (β_μ)` on `(Fin d → Fin K)`:
`boxF_cols`, `boxF_rows`. These are the Dirichlet eigenmodes of the box Laplacian (`FreeLevels.phat_eigen`), at
the levels `FreeLevels.boxU`.

## 3. A linear screen holds its kernel's count (proved)

`linScreen P w f`: `F_y = ∑_x K_{yx} P_x`, `K = ∑_β f_β w_β w_βᵀ`. `spRenyi_linScreen_le`: if the bare readings
have `ν((∑ u_x P_x)²) ≤ c ∑ u_x²` (the bare covariance on the box has operator norm at most `c`), then
`spRenyi ≤ c (∑ |f_β|)² / ∑_y ν(F_y²)`. `spRenyi_linScreen_white`: for orthonormal bare readings (white noise)
`spRenyi ≤ spRenyi (f²)`, the kernel's own count.

## 4. The heat screen (proved)

`heatW K θ = e^{−2θ μ_β}` (`FreeLevels.heatSpec 1 (boxU 1 θ K)`, box side `1`, flow time `θ` in units of the box
side squared), `heatF = √heatW = e^{−θ μ_β}`, so the kernel is the Dirichlet heat kernel `e^{−θΔ}` of the screen
box. `spRenyi_heatW_le`: `spRenyi (heatW K θ) ≤ Rheat θ` for every `K ≥ 1` (`FreeLevels.free_h3` at
`ω₀ = 1`, `τ = 2θ`, ladder `1/2`). So a heat screen of white noise holds at most `Rheat θ` modes at every zoom.

## 5. The Wilson tower (proved, given one inequality)

`heatScreen S θ ρ k O`: the Dirichlet heat smoothing, at flow time `θ ρ²`, of the bare connected reading
`O − ν_k(O)` over the screen box. `BareRatio S D ρ θ`: one `Q` with, eventually, for every `O ∈ D`, some `c` that
bounds the bare covariance on the box in operator norm and has `c ∑_β heatW_β ≤ Q ∑_y ν_k(F_y²)`.
`count_heatScreen`: `BareRatio` gives `spRenyi ≤ Rheat θ · max(Q, 0)` along the zoom. `BareRatio` is a
scale-free ratio of the bare plaquette's lattice-unit spectral density: its supremum over the box against its
heat-weighted average. It is a condition on the operator norm, not on the trace (the trace is `L_k⁴ c(0)` and
carries no concentration) and not on physical units.

`countBoundG_of_sineCount`: for every flow `W` of the tree, `CountBoundG S W D ρ` follows from a bound on the
Rényi-½ count of the flowed screen's Dirichlet-mode variances `ν_k((∑_y boxF_{yβ} cScreen_y)²)`, a sufficient
diagonal form of H3 on the box, with no Szegő comparison. It is stronger than `CountBoundG` (the eigen-count is at
most the diagonal count), so it is a sufficient condition, not an equivalent one. `hU_of_sineCount` feeds it to `CountMoments.hU_of_count`.

## 6. The paper test of the linear route

* A flow of (E) is a `ConfFlowG`: a continuous, gauge-covariant, reflection-equivariant configuration map of finite
  lattice range, read as `O ∘ V_k`. A linear smoothing of the plaquette field is a map on readings, not on
  configurations, so it is not a `W` of `ExistAlong` at all; the clauses `hphys`, the mixing, the composites never
  come into question. Its count bound feeds `hU` for no `W`. The heat screen of §5 is the statement "a finite
  aperture holds a finite count" for the Wilson measure, and §5's `countBoundG_of_sineCount` is the link to `hU`:
  the flowed screen's Dirichlet-mode variances in place of the linear kernel's.
* A box average in place of the heat kernel does not hold a bounded count (argued): its transfer function decays
  like `1/(pℓ)` per direction, `∑_p |K̂(p)| ~ (L/ℓ) log ℓ`, so the count grows like `log⁸(ℓ)` at `ℓ = s/a_k`.
  The heat kernel's `e^{−θ p²}` is summable at every zoom; the Rényi-½ count asks for `∑ |K̂| < ∞`, not `∑ |K̂|² < ∞`.
* The facts proved about the Wilson measure do not give `BareRatio`. Boundedness of the plaquette gives an
  operator norm of at most `L_k⁴ c(0)` (the box volume). Translation invariance does not bound the operator norm
  uniformly. Reflection positivity gives positivity of reflected pairings, not an upper bound on the spectral
  density relative to its low-momentum average. `BareRatio` needs the UV behaviour of the bare plaquette two-point
  function: its lattice-unit spectral density, supremum over the box, within a fixed factor of its heat-weighted
  average, uniformly in the coupling along the tower.
* Free and `U(1)` checks (argued). Free linear plaquette angle: `ĉ(p) = (p̂_μ² + p̂_ν²)/(β p̂²) ≤ 1/β`; the heat
  weights concentrate at lattice momenta `≲ 1/(√θ L_k) → 0`, where the isotropic average is `1/(2β)`, so
  `Q → 2`; the Schur row sum diverges logarithmically there, so the operator-norm form is the one that holds.
  Compact `U(1)` reading `1 − cos θ` at Gaussian order: the connected correlator `e^{−c₀}(cosh c_θ(z) − 1) ≥ 0` decays
  like `|z|^{−8}`, so `ĉ(p) ≤ ĉ(0) = ∑_z c(z)` and the heat-weighted average tends to `ĉ(0)`: `Q → 1`. White noise
  (`spRenyi_linScreen_white`): `Q = 1` exactly.

## What does not follow

* `BareRatio` is checked on paper only (the free field and compact `U(1)`); it is not proved or computed.
* `BareRatio` is not proved at any coupling of the interacting theory, and no Wilson-measure fact beyond being a
  state enters §1–§5. `count_heatScreen` moves the count onto `BareRatio`; it discharges nothing of (E).
* The heat screen is not `cScreen` for any `ConfFlowG`, so `count_heatScreen` is not `CountBoundG`.
* `countBoundG_of_sineCount` replaces the eigen-spectrum by the Dirichlet-mode diagonal; the bound on that
  diagonal's count for the observer `ConsolidatedRoot.obsW` is not proved. `CountMoments` §4 argues that the
  compact reading's high modes decay slower than `e^{−2θp²}`, so a heat-domination of `obsW`'s modes with a fixed
  constant fails; the diagonal form carries no such constant.
* `ModeHyperG`, `PhysVarG`, `PhysMeanG` and the other clauses of (E) are untouched.
* `Rheat θ` grows as `θ → 0` like `θ^{−2}`; nothing here fixes `θ`.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the signs and the lowest index; `1` the unit vectors, the frequency shift `j + 1`, the
site shift `n + 1` and the unit weights of `heatSpec`; `2` the squares, the half-angle `θ/2`, the product formula
`2 sin x sin y`, the normalization `2/(K + 1)`, the flow factor in `τ = 2θ` and the even dimension `2 · 2`; `4` the
spacetime dimension; `π` the Dirichlet frequencies. CHOSEN: the box side `1` of `FreeLevels.boxU` (only `θ/1²`
enters), the ladder `1/2` of `free_h3` (any `a ∈ (0, 1)` serves). `θ`, `ρ`, `Q`, `c` hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApertureFinite

open Finset Filter
open scoped Real
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ClayTreeG MassGap.CountMoments
open MassGap.ApertureModes (gram apSite)
open MassGap.ApertureCount (eig evec mode spRenyi state_mode_mul sum_evec_smul_mode evec_rows evec_cols
  sum_eig eig_nonneg)

/-! ## 1. The count is at most the count of any diagonal -/

/-- **Concave sums under a doubly stochastic mixing**: if `q ≥ 0` has unit row and column sums and
`∑_α q_{αβ} λ_α ≤ μ_β`, then `∑_α √λ_α ≤ ∑_β √μ_β`. DERIVED: `2` the AM–GM step `2√λ ≤ tλ + 1/t`; `1` the unit
sums; `0` the signs. -/
theorem sum_sqrt_le_of_mix {ι κ : Type*} [Fintype ι] [Fintype κ] {lam : ι → ℝ} {mu : κ → ℝ}
    {q : ι → κ → ℝ} (hl : ∀ α, 0 ≤ lam α) (hm : ∀ β, 0 ≤ mu β) (hq : ∀ α β, 0 ≤ q α β)
    (hrow : ∀ α, ∑ β, q α β = 1) (hcol : ∀ β, ∑ α, q α β = 1)
    (hdom : ∀ β, ∑ α, q α β * lam α ≤ mu β) :
    ∑ α, Real.sqrt (lam α) ≤ ∑ β, Real.sqrt (mu β) := by
  have key : ∀ ε : ℝ, 0 < ε → ∑ α, Real.sqrt (lam α) ≤ ∑ β, Real.sqrt (mu β + ε) := by
    intro ε hε
    have hs : ∀ β, 0 < Real.sqrt (mu β + ε) := fun β => Real.sqrt_pos.2 (by linarith [hm β])
    have hss : ∀ β, Real.sqrt (mu β + ε) * Real.sqrt (mu β + ε) = mu β + ε :=
      fun β => Real.mul_self_sqrt (by linarith [hm β])
    have hCS : ∀ α, 1 ≤ (∑ β, q α β / Real.sqrt (mu β + ε)) * ∑ β, q α β * Real.sqrt (mu β + ε) := by
      intro α
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun β => Real.sqrt (q α β / Real.sqrt (mu β + ε)))
        (fun β => Real.sqrt (q α β * Real.sqrt (mu β + ε)))
      have h1 : ∑ β, Real.sqrt (q α β / Real.sqrt (mu β + ε)) * Real.sqrt (q α β * Real.sqrt (mu β + ε))
          = 1 := by
        rw [← hrow α]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Real.sqrt_mul (div_nonneg (hq α β) (hs β).le)]
        have e : q α β / Real.sqrt (mu β + ε) * (q α β * Real.sqrt (mu β + ε)) = q α β ^ 2 := by
          have := (hs β).ne'
          field_simp
        rw [e]
        exact Real.sqrt_sq (hq α β)
      have h2 : ∑ β, Real.sqrt (q α β / Real.sqrt (mu β + ε)) ^ 2 = ∑ β, q α β / Real.sqrt (mu β + ε) :=
        Finset.sum_congr rfl fun β _ => Real.sq_sqrt (div_nonneg (hq α β) (hs β).le)
      have h3 : ∑ β, Real.sqrt (q α β * Real.sqrt (mu β + ε)) ^ 2 = ∑ β, q α β * Real.sqrt (mu β + ε) :=
        Finset.sum_congr rfl fun β _ => Real.sq_sqrt (mul_nonneg (hq α β) (hs β).le)
      rw [h1, h2, h3, one_pow] at h
      exact h
    have ht : ∀ α, 0 < ∑ β, q α β / Real.sqrt (mu β + ε) := by
      intro α
      have h0 : 0 ≤ ∑ β, q α β / Real.sqrt (mu β + ε) :=
        Finset.sum_nonneg fun β _ => div_nonneg (hq α β) (hs β).le
      rcases h0.lt_or_eq with h | h
      · exact h
      · have := hCS α
        rw [← h, zero_mul] at this
        linarith
    have hper : ∀ α, 2 * Real.sqrt (lam α)
        ≤ (∑ β, q α β / Real.sqrt (mu β + ε)) * lam α + ∑ β, q α β * Real.sqrt (mu β + ε) := by
      intro α
      set t := ∑ β, q α β / Real.sqrt (mu β + ε) with htd
      set u := ∑ β, q α β * Real.sqrt (mu β + ε) with hud
      have hsq := Real.sq_sqrt (hl α)
      have h1 : 1 ≤ t * u := hCS α
      have h2 := sq_nonneg (t * Real.sqrt (lam α) - 1)
      have e : t ^ 2 * Real.sqrt (lam α) ^ 2 = t ^ 2 * lam α := by rw [hsq]
      have hk : 2 * Real.sqrt (lam α) * t ≤ (t * lam α + u) * t := by nlinarith
      exact le_of_mul_le_mul_right hk (ht α)
    have hsum : 2 * ∑ α, Real.sqrt (lam α)
        ≤ ∑ α, (∑ β, q α β / Real.sqrt (mu β + ε)) * lam α
          + ∑ α, ∑ β, q α β * Real.sqrt (mu β + ε) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun α _ => hper α
    have hA : ∑ α, (∑ β, q α β / Real.sqrt (mu β + ε)) * lam α ≤ ∑ β, Real.sqrt (mu β + ε) := by
      calc ∑ α, (∑ β, q α β / Real.sqrt (mu β + ε)) * lam α
          = ∑ α, ∑ β, q α β * lam α / Real.sqrt (mu β + ε) :=
            Finset.sum_congr rfl fun α _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun β _ => by ring
        _ = ∑ β, ∑ α, q α β * lam α / Real.sqrt (mu β + ε) := Finset.sum_comm
        _ = ∑ β, (∑ α, q α β * lam α) / Real.sqrt (mu β + ε) :=
            Finset.sum_congr rfl fun β _ => (Finset.sum_div _ _ _).symm
        _ ≤ ∑ β, mu β / Real.sqrt (mu β + ε) :=
            Finset.sum_le_sum fun β _ => div_le_div_of_nonneg_right (hdom β) (hs β).le
        _ ≤ ∑ β, Real.sqrt (mu β + ε) := Finset.sum_le_sum fun β _ => by
            rw [div_le_iff₀ (hs β), hss β]
            linarith
    have hB : ∑ α, ∑ β, q α β * Real.sqrt (mu β + ε) = ∑ β, Real.sqrt (mu β + ε) := by
      calc ∑ α, ∑ β, q α β * Real.sqrt (mu β + ε) = ∑ β, ∑ α, q α β * Real.sqrt (mu β + ε) :=
            Finset.sum_comm
        _ = ∑ β, Real.sqrt (mu β + ε) :=
            Finset.sum_congr rfl fun β _ => by rw [← Finset.sum_mul, hcol β, one_mul]
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hn : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hn1 : (0 : ℝ) < (Fintype.card κ : ℝ) + 1 := by linarith
  have hd : 0 < δ / ((Fintype.card κ : ℝ) + 1) := div_pos hδ hn1
  refine (key _ (pow_pos hd 2)).trans ?_
  have h1 : ∀ β, Real.sqrt (mu β + (δ / ((Fintype.card κ : ℝ) + 1)) ^ 2)
      ≤ Real.sqrt (mu β) + δ / ((Fintype.card κ : ℝ) + 1) := by
    intro β
    have hm0 := Real.sq_sqrt (hm β)
    have hr0 := Real.sqrt_nonneg (mu β)
    calc Real.sqrt (mu β + (δ / ((Fintype.card κ : ℝ) + 1)) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (mu β) + δ / ((Fintype.card κ : ℝ) + 1)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith
      _ = Real.sqrt (mu β) + δ / ((Fintype.card κ : ℝ) + 1) := Real.sqrt_sq (by positivity)
  calc ∑ β, Real.sqrt (mu β + (δ / ((Fintype.card κ : ℝ) + 1)) ^ 2)
      ≤ ∑ β, (Real.sqrt (mu β) + δ / ((Fintype.card κ : ℝ) + 1)) := Finset.sum_le_sum fun β _ => h1 β
    _ = ∑ β, Real.sqrt (mu β) + (Fintype.card κ : ℝ) * (δ / ((Fintype.card κ : ℝ) + 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ β, Real.sqrt (mu β) + δ := by
        have : (Fintype.card κ : ℝ) * (δ / ((Fintype.card κ : ℝ) + 1)) ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ hn1]
          nlinarith
        linarith

#print axioms sum_sqrt_le_of_mix

/-- **The Rényi-½ count in closed form**: `spRenyi w = (∑ √w)² / ∑ w` for `w ≥ 0`. DERIVED: `2` the square. -/
theorem spRenyi_eq_sq_div {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw : ∀ α, 0 ≤ w α) :
    spRenyi w = (∑ α, Real.sqrt (w α)) ^ 2 / ∑ α, w α := by
  have hS : 0 ≤ ∑ α, w α := Finset.sum_nonneg fun α _ => hw α
  unfold spRenyi
  rw [Finset.sum_congr rfl fun α _ => Real.sqrt_div (hw α) _, ← Finset.sum_div, div_pow, Real.sq_sqrt hS]

#print axioms spRenyi_eq_sq_div

section Frame

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → C(X, ℝ))

/-- **Parseval in a frame with orthonormal rows**: `∑_β (∑_y w_{yβ} e_y)² = ∑_y e_y²`. DERIVED: `2` the square;
`0`, `1` the entries of the identity. -/
theorem sum_sq_frame {κ : Type*} [Fintype κ] (e : ι → ℝ) (w : ι → κ → ℝ)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0) :
    ∑ β, (∑ y, w y β * e y) ^ 2 = ∑ y, e y ^ 2 := by
  calc ∑ β, (∑ y, w y β * e y) ^ 2 = ∑ β, ∑ y, ∑ z, (e y * e z) * (w y β * w z β) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ y, ∑ β, ∑ z, (e y * e z) * (w y β * w z β) := Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ β, (e y * e z) * (w y β * w z β) := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ y, ∑ z, (e y * e z) * ∑ β, w y β * w z β :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
    _ = ∑ y, e y ^ 2 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [hrows, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

/-- **A combination of the screen in its modes**: `∑_y v_y F_y = ∑_α (∑_y v_y e_{yα}) mode_α`.
DERIVED: no numeral. -/
theorem comb_eq_modes (v : ι → ℝ) :
    ∑ y, v y • F y = ∑ α, (∑ y, v y * evec ν F y α) • mode ν F α := by
  simp only [Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.smul_sum, sum_evec_smul_mode]

/-- **The second moment of a mode combination**: `ν((∑_α c_α mode_α)²) = ∑_α c_α² λ_α`.
DERIVED: `2` the square; `0` the off-diagonal pairings. -/
theorem state_sq_comb (c : ι → ℝ) :
    ν ((∑ α, c α • mode ν F α) ^ 2) = ∑ α, c α ^ 2 * eig ν F α := by
  rw [sq, Finset.sum_mul_sum, ν.map_sum]
  simp only [ν.map_sum, smul_mul_smul_comm, ν.map_smul, state_mode_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- **The second moment of a screen combination in the eigenbasis**. DERIVED: `2` the square. -/
theorem state_sq_frameComb (v : ι → ℝ) :
    ν ((∑ y, v y • F y) ^ 2) = ∑ α, (∑ y, v y * evec ν F y α) ^ 2 * eig ν F α := by
  rw [comb_eq_modes, state_sq_comb]

/-- The columns of the eigenvector matrix have unit length. DERIVED: `1` the unit length; `2` the square. -/
theorem evec_sq_sum (α : ι) : ∑ y, evec ν F y α ^ 2 = 1 := by
  have h := evec_cols ν F α α
  rw [if_pos rfl] at h
  simpa only [sq] using h

/-- **The concave sum of the Gram spectrum against a frame**: for an orthonormal frame `w` and
`ν((∑_y w_{yβ} F_y)²) ≤ g_β`, `∑_α √λ_α ≤ ∑_β √g_β`. DERIVED: `0`, `1` the identity's entries; `2` the square. -/
theorem sum_sqrt_eig_le_frame {κ : Type*} [Fintype κ] [DecidableEq κ] (w : ι → κ → ℝ) (g : κ → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0)
    (hdom : ∀ β, ν ((∑ y, w y β • F y) ^ 2) ≤ g β) :
    ∑ α, Real.sqrt (eig ν F α) ≤ ∑ β, Real.sqrt (g β) := by
  refine sum_sqrt_le_of_mix (q := fun α β => (∑ y, w y β * evec ν F y α) ^ 2) (eig_nonneg ν F)
    (fun β => ?_) (fun α β => sq_nonneg _) (fun α => ?_) (fun β => ?_) (fun β => ?_)
  · exact (ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity).trans (hdom β)
  · show ∑ β, (∑ y, w y β * evec ν F y α) ^ 2 = 1
    have h := sum_sq_frame (fun y => evec ν F y α) w hrows
    beta_reduce at h
    rw [h, evec_sq_sum]
  · show ∑ α, (∑ y, w y β * evec ν F y α) ^ 2 = 1
    have h := sum_sq_frame (fun y => w y β) (evec ν F) (evec_rows ν F)
    beta_reduce at h
    have h1 := hcols β β
    rw [if_pos rfl] at h1
    calc ∑ α, (∑ y, w y β * evec ν F y α) ^ 2 = ∑ α, (∑ y, evec ν F y α * w y β) ^ 2 :=
          Finset.sum_congr rfl fun α _ => by
            rw [Finset.sum_congr rfl fun y _ => mul_comm (w y β) (evec ν F y α)]
      _ = ∑ y, w y β ^ 2 := h
      _ = 1 := by simpa only [sq] using h1
  · show ∑ α, (∑ y, w y β * evec ν F y α) ^ 2 * eig ν F α ≤ g β
    exact (state_sq_frameComb ν F (fun y => w y β)).symm.le.trans (hdom β)

/-- **The count against a frame**: under the hypotheses of `sum_sqrt_eig_le_frame`,
`spRenyi (eig ν F) ≤ (∑_β √g_β)² / ∑_y ν(F_y²)`. DERIVED: `2` the square. -/
theorem spRenyi_eig_le_frame {κ : Type*} [Fintype κ] [DecidableEq κ] (w : ι → κ → ℝ) (g : κ → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0)
    (hdom : ∀ β, ν ((∑ y, w y β • F y) ^ 2) ≤ g β) :
    spRenyi (eig ν F) ≤ (∑ β, Real.sqrt (g β)) ^ 2 / ∑ y, ν (F y ^ 2) := by
  rw [spRenyi_eq_sq_div _ (eig_nonneg ν F), sum_eig]
  apply div_le_div_of_nonneg_right _
    (Finset.sum_nonneg fun y _ => ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _)
    (sum_sqrt_eig_le_frame ν F w g hcols hrows hdom) 2

/-- **The trace in a frame**: `∑_β ν((∑_y w_{yβ} F_y)²) = ∑_y ν(F_y²)`. DERIVED: `2` the square. -/
theorem sum_frame_eq_trace {κ : Type*} [Fintype κ] (w : ι → κ → ℝ)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0) :
    ∑ β, ν ((∑ y, w y β • F y) ^ 2) = ∑ y, ν (F y ^ 2) := by
  rw [← sum_eig ν F]
  calc ∑ β, ν ((∑ y, w y β • F y) ^ 2)
      = ∑ β, ∑ α, (∑ y, w y β * evec ν F y α) ^ 2 * eig ν F α :=
        Finset.sum_congr rfl fun β _ => state_sq_frameComb ν F (fun y => w y β)
    _ = ∑ α, ∑ β, (∑ y, w y β * evec ν F y α) ^ 2 * eig ν F α := Finset.sum_comm
    _ = ∑ α, (∑ β, (∑ y, w y β * evec ν F y α) ^ 2) * eig ν F α :=
        Finset.sum_congr rfl fun α _ => by rw [Finset.sum_mul]
    _ = ∑ α, eig ν F α := Finset.sum_congr rfl fun α _ => by
        have h := sum_sq_frame (fun y => evec ν F y α) w hrows
        beta_reduce at h
        rw [h, evec_sq_sum, one_mul]

/-- **The count is at most the count of the diagonal in any orthonormal frame**:
`spRenyi (eig ν F) ≤ spRenyi (β ↦ ν((∑_y w_{yβ} F_y)²))`. DERIVED: `2` the square; `0`, `1` the identity's
entries. -/
theorem spRenyi_eig_le_diag {κ : Type*} [Fintype κ] [DecidableEq κ] (w : ι → κ → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0) :
    spRenyi (eig ν F) ≤ spRenyi (fun β => ν ((∑ y, w y β • F y) ^ 2)) := by
  have hg : ∀ β, 0 ≤ ν ((∑ y, w y β • F y) ^ 2) :=
    fun β => ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  rw [spRenyi_eq_sq_div _ hg, sum_frame_eq_trace ν F w hrows]
  exact spRenyi_eig_le_frame ν F w _ hcols hrows fun β => le_rfl

end Frame

#print axioms sum_sq_frame
#print axioms comb_eq_modes
#print axioms state_sq_comb
#print axioms state_sq_frameComb
#print axioms evec_sq_sum
#print axioms sum_sqrt_eig_le_frame
#print axioms spRenyi_eig_le_frame
#print axioms sum_frame_eq_trace
#print axioms spRenyi_eig_le_diag

/-! ## 2. The Dirichlet frame of the box -/

/-- **The Dirichlet sine** of frequency `u` at site `n`: `sin(π u (n + 1)/(K + 1))`. DERIVED: `1` the site shift
and the wall at `K + 1`; `π` the frequency. -/
def sv (K u : ℕ) (n : Fin K) : ℝ := Real.sin (π * (u : ℝ) * (((n : ℕ) : ℝ) + 1) / ((K : ℝ) + 1))

/-- **The Dirichlet cosine sum**: for `0 < m < 2(K + 1)`, `∑_{n<K} cos(π m (n + 1)/(K + 1)) = −(1 + (−1)^m)/2`.
Telescoping `sin((i + 1/2)θ)`. DERIVED: `2` the half-angle and the product formula; `1` the shift; `π` the
frequency. -/
theorem cos_sum (K m : ℕ) (hm0 : 0 < m) (hm : m < 2 * (K + 1)) :
    ∑ n : Fin K, Real.cos (π * (m : ℝ) * (((n : ℕ) : ℝ) + 1) / ((K : ℝ) + 1)) = -(1 + (-1) ^ m) / 2 := by
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmr : (m : ℝ) < 2 * ((K : ℝ) + 1) := by exact_mod_cast hm
  set θ : ℝ := π * m / ((K : ℝ) + 1) with hθ
  have hθK : θ * ((K : ℝ) + 1) = (m : ℝ) * π := by rw [hθ, div_mul_cancel₀ _ hK1.ne', mul_comm]
  have hs : 0 < Real.sin (θ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]; exact div_pos (div_pos (mul_pos Real.pi_pos hm0') hK1) two_pos
    · rw [hθ, div_div, div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have hterm : ∀ n : ℕ, Real.cos (π * (m : ℝ) * ((n : ℝ) + 1) / ((K : ℝ) + 1))
      = Real.cos (θ * ((n : ℝ) + 1)) := by
    intro n; congr 1; rw [hθ]; ring
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Real.cos (π * (m : ℝ) * ((n : ℝ) + 1) / ((K : ℝ) + 1))) K]
  simp only [hterm]
  set g : ℕ → ℝ := fun i => Real.sin (θ * (i : ℝ) + θ / 2) with hg
  have htel : ∀ i : ℕ, g (i + 1) - g i = 2 * Real.sin (θ / 2) * Real.cos (θ * ((i : ℝ) + 1)) := by
    intro i
    simp only [hg]
    push_cast
    have e1 : (θ * ((i : ℝ) + 1) + θ / 2 - (θ * (i : ℝ) + θ / 2)) / 2 = θ / 2 := by ring
    have e2 : (θ * ((i : ℝ) + 1) + θ / 2 + (θ * (i : ℝ) + θ / 2)) / 2 = θ * ((i : ℝ) + 1) := by ring
    rw [Real.sin_sub_sin, e1, e2]
  have hsum : 2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range K, Real.cos (θ * ((i : ℝ) + 1)) = g K - g 0 := by
    rw [Finset.mul_sum, ← Finset.sum_range_sub g K]
    exact Finset.sum_congr rfl fun i _ => (htel i).symm
  have hgK : g K = -((-1) ^ m * Real.sin (θ / 2)) := by
    simp only [hg]
    rw [show θ * (K : ℝ) + θ / 2 = (m : ℝ) * π - θ / 2 by rw [← hθK]; ring, Real.sin_sub,
      Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    ring
  have hg0 : g 0 = Real.sin (θ / 2) := by simp [hg]
  rw [hgK, hg0] at hsum
  apply mul_left_cancel₀ (mul_pos two_pos hs).ne'
  rw [hsum]
  ring

/-- `2 sin x sin y = cos(x − y) − cos(x + y)`. DERIVED: `2` the product formula. -/
theorem two_sin_mul_sin (x y : ℝ) : 2 * (Real.sin x * Real.sin y) = Real.cos (x - y) - Real.cos (x + y) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- **Distinct Dirichlet sines are orthogonal**: for `0 < v < u ≤ K`, `∑_n sv u n · sv v n = 0`.
DERIVED: `2` the product formula and the parity `(−1)^{2v} = 1`; `0` the value. -/
theorem sv_orth_ne (K u v : ℕ) (hv : 0 < v) (hvu : v < u) (hu : u ≤ K) :
    ∑ n : Fin K, sv K u n * sv K v n = 0 := by
  have hc1 : ((u - v : ℕ) : ℝ) = (u : ℝ) - v := Nat.cast_sub hvu.le
  have hc2 : (((u - v) + 2 * v : ℕ) : ℝ) = (u : ℝ) + v := by
    rw [Nat.cast_add, hc1]; push_cast; ring
  have h2 : ∀ n : Fin K, 2 * (sv K u n * sv K v n)
      = Real.cos (π * ((u - v : ℕ) : ℝ) * (((n : ℕ) : ℝ) + 1) / ((K : ℝ) + 1))
        - Real.cos (π * (((u - v) + 2 * v : ℕ) : ℝ) * (((n : ℕ) : ℝ) + 1) / ((K : ℝ) + 1)) := by
    intro n
    unfold sv
    rw [two_sin_mul_sin, hc2, hc1]
    congr 1 <;> congr 1 <;> ring
  have hA := cos_sum K (u - v) (by omega) (by omega)
  have hB := cos_sum K ((u - v) + 2 * v) (by omega) (by omega)
  have hpow : ((-1 : ℝ) ^ ((u - v) + 2 * v)) = (-1) ^ (u - v) := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have h : 2 * ∑ n : Fin K, sv K u n * sv K v n = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun n _ => h2 n, Finset.sum_sub_distrib, hA, hB, hpow]
    ring
  linarith

/-- **A Dirichlet sine has squared norm `(K + 1)/2`**: for `0 < u ≤ K`. DERIVED: `2` the product formula and
the parity; `1` the wall. -/
theorem sv_orth_self (K u : ℕ) (hu0 : 0 < u) (hu : u ≤ K) :
    ∑ n : Fin K, sv K u n * sv K u n = ((K : ℝ) + 1) / 2 := by
  have h2 : ∀ n : Fin K, 2 * (sv K u n * sv K u n)
      = 1 - Real.cos (π * ((2 * u : ℕ) : ℝ) * (((n : ℕ) : ℝ) + 1) / ((K : ℝ) + 1)) := by
    intro n
    unfold sv
    rw [two_sin_mul_sin, sub_self, Real.cos_zero]
    congr 1
    congr 1
    push_cast
    ring
  have hB := cos_sum K (2 * u) (by omega) (by omega)
  have hpow : ((-1 : ℝ) ^ (2 * u)) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  have h : 2 * ∑ n : Fin K, sv K u n * sv K u n = (K : ℝ) + 1 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun n _ => h2 n, Finset.sum_sub_distrib, hB, hpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  linarith

/-- **The normalized Dirichlet frame** on `Fin K`: site `n`, mode `j`, `√(2/(K + 1)) sin(π (j + 1)(n + 1)/(K + 1))`.
DERIVED: `2` the normalization; `1` the frequency shift. -/
def sinF (K : ℕ) (n j : Fin K) : ℝ := Real.sqrt (2 / ((K : ℝ) + 1)) * sv K ((j : ℕ) + 1) n

/-- **The Dirichlet frame has orthonormal columns**. DERIVED: `0`, `1` the identity's entries; `2` the
normalization. -/
theorem sinF_cols (K : ℕ) (j j' : Fin K) :
    ∑ n, sinF K n j * sinF K n j' = if j = j' then 1 else 0 := by
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hc : Real.sqrt (2 / ((K : ℝ) + 1)) * Real.sqrt (2 / ((K : ℝ) + 1)) = 2 / ((K : ℝ) + 1) :=
    Real.mul_self_sqrt (by positivity)
  have e : ∑ n, sinF K n j * sinF K n j'
      = 2 / ((K : ℝ) + 1) * ∑ n, sv K ((j : ℕ) + 1) n * sv K ((j' : ℕ) + 1) n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold sinF
    rw [mul_mul_mul_comm, hc]
  rw [e]
  have hj := j.isLt
  have hj' := j'.isLt
  by_cases h : j = j'
  · subst h
    rw [if_pos rfl, sv_orth_self K ((j : ℕ) + 1) (by omega) (by omega)]
    field_simp
  · rw [if_neg h]
    have hne : (j : ℕ) ≠ (j' : ℕ) := fun h' => h (Fin.ext h')
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h0 := sv_orth_ne K ((j' : ℕ) + 1) ((j : ℕ) + 1) (by omega) (by omega) (by omega)
      rw [Finset.sum_congr rfl fun n _ => mul_comm (sv K ((j : ℕ) + 1) n) (sv K ((j' : ℕ) + 1) n), h0,
        mul_zero]
    · rw [sv_orth_ne K ((j : ℕ) + 1) ((j' : ℕ) + 1) (by omega) (by omega) (by omega), mul_zero]

/-- **The Dirichlet frame has orthonormal rows** (a square matrix with orthonormal columns). DERIVED: `0`, `1` the
identity's entries. -/
theorem sinF_rows (K : ℕ) (n n' : Fin K) :
    ∑ j, sinF K n j * sinF K n' j = if n = n' then 1 else 0 := by
  have h1 : (Matrix.of fun n j => sinF K n j).transpose * (Matrix.of fun n j => sinF K n j) = 1 := by
    ext j j'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    exact sinF_cols K j j'
  have h2 : (Matrix.of fun n j => sinF K n j) * (Matrix.of fun n j => sinF K n j).transpose = 1 :=
    mul_eq_one_comm.1 h1
  have h3 := congrArg (fun A : Matrix (Fin K) (Fin K) ℝ => A n n') h2
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] using h3

/-- A product of Kronecker deltas is the delta of the tuples. DERIVED: `0`, `1` the entries. -/
theorem prod_ite_eq_ite {d K : ℕ} (β γ : Fin d → Fin K) :
    ∏ μ, (if β μ = γ μ then (1 : ℝ) else 0) = if β = γ then 1 else 0 := by
  by_cases h : β = γ
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨μ, hμ⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (if_neg hμ)

/-- **Product frames are orthonormal**: if `φ` has orthonormal columns, so has `∏_μ φ (y_μ) (β_μ)`.
DERIVED: `0`, `1` the entries. -/
theorem prod_frame {d K : ℕ} (φ : Fin K → Fin K → ℝ)
    (hφ : ∀ j j', ∑ n, φ n j * φ n j' = if j = j' then 1 else 0) (β γ : Fin d → Fin K) :
    ∑ y : Fin d → Fin K, (∏ μ, φ (y μ) (β μ)) * (∏ μ, φ (y μ) (γ μ)) = if β = γ then 1 else 0 := by
  calc ∑ y : Fin d → Fin K, (∏ μ, φ (y μ) (β μ)) * (∏ μ, φ (y μ) (γ μ))
      = ∑ y : Fin d → Fin K, ∏ μ, (φ (y μ) (β μ) * φ (y μ) (γ μ)) :=
        Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm
    _ = ∏ μ, ∑ n, φ n (β μ) * φ n (γ μ) := (Fintype.prod_sum (fun μ n => φ n (β μ) * φ n (γ μ))).symm
    _ = ∏ μ, (if β μ = γ μ then (1 : ℝ) else 0) := Finset.prod_congr rfl fun μ _ => hφ _ _
    _ = if β = γ then 1 else 0 := prod_ite_eq_ite β γ

/-- **The Dirichlet frame of the box** `(Fin d → Fin K)`: `∏_μ sinF K (y_μ) (β_μ)`. DERIVED: no numeral. -/
def boxF (K : ℕ) {d : ℕ} (y β : Fin d → Fin K) : ℝ := ∏ μ, sinF K (y μ) (β μ)

/-- DERIVED: `0`, `1` the entries. -/
theorem boxF_cols (K : ℕ) {d : ℕ} (β γ : Fin d → Fin K) :
    ∑ y, boxF K y β * boxF K y γ = if β = γ then 1 else 0 :=
  prod_frame (sinF K) (sinF_cols K) β γ

/-- DERIVED: `0`, `1` the entries. -/
theorem boxF_rows (K : ℕ) {d : ℕ} (y z : Fin d → Fin K) :
    ∑ β, boxF K y β * boxF K z β = if y = z then 1 else 0 :=
  prod_frame (fun j n => sinF K n j) (fun n n' => sinF_rows K n n') y z

#print axioms cos_sum
#print axioms two_sin_mul_sin
#print axioms sv_orth_ne
#print axioms sv_orth_self
#print axioms sinF_cols
#print axioms sinF_rows
#print axioms prod_ite_eq_ite
#print axioms prod_frame
#print axioms boxF_cols
#print axioms boxF_rows

/-! ## 3. A linear screen holds its kernel's count -/

section Linear

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The kernel of a frame and a transfer function**: `K_{yx} = ∑_β f_β w_{yβ} w_{xβ}`. DERIVED: no numeral. -/
def kerOf (w : ι → ι → ℝ) (f : ι → ℝ) (y x : ι) : ℝ := ∑ β, f β * w y β * w x β

/-- **A linear screen**: `F_y = ∑_x K_{yx} P_x`. DERIVED: no numeral. -/
def linScreen (P : ι → C(X, ℝ)) (w : ι → ι → ℝ) (f : ι → ℝ) : ι → C(X, ℝ) :=
  fun y => ∑ x, kerOf w f y x • P x

/-- The frame diagonalizes the kernel: `∑_y w_{yβ} K_{yx} = f_β w_{xβ}`. DERIVED: `0`, `1` the entries. -/
theorem sum_frame_ker (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0) (β x : ι) :
    ∑ y, w y β * kerOf w f y x = f β * w x β := by
  unfold kerOf
  calc ∑ y, w y β * ∑ γ, f γ * w y γ * w x γ = ∑ y, ∑ γ, (f γ * w x γ) * (w y β * w y γ) :=
        Finset.sum_congr rfl fun y _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun γ _ => by ring
    _ = ∑ γ, ∑ y, (f γ * w x γ) * (w y β * w y γ) := Finset.sum_comm
    _ = ∑ γ, (f γ * w x γ) * ∑ y, w y β * w y γ :=
        Finset.sum_congr rfl fun γ _ => by rw [Finset.mul_sum]
    _ = f β * w x β := by
        simp only [hcols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [CompactSpace X] in
/-- **A frame combination of a linear screen**: `∑_y w_{yβ} F_y = ∑_x (f_β w_{xβ}) P_x`. DERIVED: no numeral. -/
theorem frame_comb_lin (P : ι → C(X, ℝ)) (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0) (β : ι) :
    ∑ y, w y β • linScreen P w f y = ∑ x, (f β * w x β) • P x := by
  unfold linScreen
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_smul, sum_frame_ker w f hcols β x]

/-- `∑_x (f_β w_{xβ})² = f_β²` on a frame with orthonormal columns. DERIVED: `2` the square. -/
theorem sum_sq_col (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0) (β : ι) :
    ∑ x, (f β * w x β) ^ 2 = f β ^ 2 := by
  have h1 := hcols β β
  rw [if_pos rfl] at h1
  calc ∑ x, (f β * w x β) ^ 2 = f β ^ 2 * ∑ x, w x β * w x β := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    _ = f β ^ 2 := by rw [h1, mul_one]

/-- **A linear screen holds its kernel's count up to the bare condition ratio**: if
`ν((∑ u_x P_x)²) ≤ c ∑ u_x²` for every `u`, then `spRenyi ≤ c (∑_β |f_β|)² / ∑_y ν(F_y²)`.
DERIVED: `2` the squares; `0` the sign of `c`. -/
theorem spRenyi_linScreen_le (P : ι → C(X, ℝ)) (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ u : ι → ℝ, ν ((∑ x, u x • P x) ^ 2) ≤ c * ∑ x, u x ^ 2) :
    spRenyi (eig ν (linScreen P w f)) ≤ c * (∑ β, |f β|) ^ 2 / ∑ y, ν (linScreen P w f y ^ 2) := by
  have hdom : ∀ β, ν ((∑ y, w y β • linScreen P w f y) ^ 2) ≤ c * f β ^ 2 := by
    intro β
    rw [frame_comb_lin P w f hcols β]
    have h := hC (fun x => f β * w x β)
    beta_reduce at h
    rw [sum_sq_col w f hcols β] at h
    exact h
  have h := spRenyi_eig_le_frame ν (linScreen P w f) w (fun β => c * f β ^ 2) hcols hrows hdom
  have hs : ∑ β, Real.sqrt (c * f β ^ 2) = Real.sqrt c * ∑ β, |f β| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by rw [Real.sqrt_mul hc, Real.sqrt_sq_eq_abs]
  beta_reduce at h
  rw [hs, mul_pow, Real.sq_sqrt hc] at h
  exact h

/-- **Orthonormal bare readings**: `ν((∑ u_x P_x)²) = ∑ u_x²`. DERIVED: `2` the square; `0`, `1` the
pairings. -/
theorem state_sq_white (P : ι → C(X, ℝ)) (hP : ∀ x z, ν (P x * P z) = if x = z then 1 else 0)
    (u : ι → ℝ) : ν ((∑ x, u x • P x) ^ 2) = ∑ x, u x ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ν.map_sum]
  simp only [ν.map_sum, smul_mul_smul_comm, ν.map_smul, hP, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **The white-noise test**: a linear screen of orthonormal bare readings holds at most its kernel's count,
`spRenyi (eig ν F) ≤ spRenyi (f²)`. DERIVED: `2` the squares; `1` the unit condition ratio. -/
theorem spRenyi_linScreen_white (P : ι → C(X, ℝ)) (w : ι → ι → ℝ) (f : ι → ℝ)
    (hcols : ∀ β γ, ∑ y, w y β * w y γ = if β = γ then 1 else 0)
    (hrows : ∀ y z, ∑ β, w y β * w z β = if y = z then 1 else 0)
    (hP : ∀ x z, ν (P x * P z) = if x = z then 1 else 0) :
    spRenyi (eig ν (linScreen P w f)) ≤ spRenyi (fun β => f β ^ 2) := by
  have h := spRenyi_linScreen_le ν P w f hcols hrows zero_le_one
    (fun u => (state_sq_white ν P hP u).trans_le (le_of_eq (one_mul _).symm))
  have htot : ∑ y, ν (linScreen P w f y ^ 2) = ∑ β, f β ^ 2 := by
    rw [← sum_frame_eq_trace ν (linScreen P w f) w hrows]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [frame_comb_lin P w f hcols β, state_sq_white ν P hP, sum_sq_col w f hcols β]
  rw [htot, one_mul] at h
  rw [spRenyi_eq_sq_div _ (fun β => sq_nonneg (f β))]
  have hs : ∑ β, Real.sqrt (f β ^ 2) = ∑ β, |f β| :=
    Finset.sum_congr rfl fun β _ => Real.sqrt_sq_eq_abs _
  rw [hs]
  exact h

end Linear

#print axioms sum_frame_ker
#print axioms frame_comb_lin
#print axioms sum_sq_col
#print axioms spRenyi_linScreen_le
#print axioms state_sq_white
#print axioms spRenyi_linScreen_white

/-! ## 4. The heat screen -/

/-- The box index in the dimension form `2 · 2` of `FreeLevels`. DERIVED: `4 = 2 · 2` the dimension. -/
def e4 (K : ℕ) : (Fin 4 → Fin K) ≃ (Fin (2 * 2) → Fin K) :=
  Equiv.arrowCongr (finCongr (by norm_num)) (Equiv.refl _)

/-- **The heat spectrum of the box** `e^{−2θ μ_β}`, box side `1`, flow time `θ`. CHOSEN: the box side `1`
(only `θ/1²` enters); DERIVED: `1` the unit weights. -/
def heatW (K : ℕ) (θ : ℝ) : (Fin 4 → Fin K) → ℝ :=
  FreeLevels.heatSpec (fun _ => (1 : ℝ)) (FreeLevels.boxU 1 θ K) ∘ e4 K

/-- **The heat transfer function** `e^{−θ μ_β} = √(heatW)`: the kernel `kerOf boxF heatF` is the Dirichlet heat
kernel `e^{−θΔ}` of the box (`FreeLevels.phat_eigen`). DERIVED: no numeral. -/
def heatF (K : ℕ) (θ : ℝ) (β : Fin 4 → Fin K) : ℝ := Real.sqrt (heatW K θ β)

/-- **The free heat count bound**: `free_h3`'s Rényi-½ bound at `ω₀ = 1`, `τ = 2θ`, ladder `1/2`, `m = 2`.
CHOSEN: the ladder `1/2`. DERIVED: `2` the even dimension `2 · 2` and `τ = 2θ`; `1` the unit weight ratio;
`4`, `π` from `free_h3`. -/
def Rheat (θ : ℝ) : ℝ :=
  FreeLevels.renyiFactor 2 (1 / 2) ^ 2 * (1 * Real.exp 1) ^ 2
    * (FreeLevels.renyiFactor 2 (1 / 2) ^ 2 * (1 * Real.exp 1) * ((1 / (2 * θ) + π ^ 2) / 4) ^ 2)

/-- DERIVED: `0` the sign. -/
theorem heatW_pos (K : ℕ) (θ : ℝ) (β : Fin 4 → Fin K) : 0 < heatW K θ β := by
  simp only [heatW, Function.comp_apply, FreeLevels.heatSpec, one_mul]
  exact Real.exp_pos _

/-- **The heat spectrum holds a bounded count at every zoom**: `spRenyi (heatW K θ) ≤ Rheat θ` for `K ≥ 1`,
`θ > 0`. CHOSEN: the ladder `1/2`. DERIVED: `2` the dimension form and `τ = 2θ`; `1` the box side and the
weights. -/
theorem spRenyi_heatW_le (K : ℕ) (hK : 0 < K) {θ : ℝ} (hθ : 0 < θ) : spRenyi (heatW K θ) ≤ Rheat θ := by
  have h := FreeLevels.free_h3 (L := 1) (t := θ) (K := K) (m := 2) (τ := 2 * θ) (ω₀ := 1)
    (w := fun _ => (1 : ℝ)) (wlo := 1) (lam := heatW K θ) (a := 1 / 2) hK one_pos hθ two_pos
    (by linarith) (by rw [one_pow, div_one]) one_pos (fun _ => ⟨le_rfl, by rw [one_mul]⟩) (e4 K) rfl
    (by norm_num) (by norm_num)
  obtain ⟨h1, -, h3⟩ := h
  calc spRenyi (heatW K θ) ≤ _ := h3
    _ ≤ Rheat θ := by
        unfold Rheat
        exact mul_le_mul_of_nonneg_left h1 (by positivity)

#print axioms heatW_pos
#print axioms spRenyi_heatW_le

/-! ## 5. The Wilson tower -/

section Tower

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The bare connected reading** `O − ν_k(O)` (no flow). DERIVED: `1` the constant. -/
def bareRead (S : Sched G) (k : ℕ) (O : LField G) : C(IConf G, ℝ) :=
  O.1 - S.ν k O.1 • (1 : C(IConf G, ℝ))

/-- **The bare screen**: the bare connected reading at every site of the box of side `L_k = ⌈ρ / a_k⌉`.
DERIVED: `4` the dimension. -/
def bareScreen (S : Sched G) (ρ : ℝ) (k : ℕ) (O : LField G) :
    (Fin 4 → Fin (scrSide S ρ k)) → C(IConf G, ℝ) :=
  fun x => transObs (apSite x) (bareRead S k O)

/-- **The heat screen**: the bare screen smoothed by the Dirichlet heat kernel of the box at flow time `θ` in
units of the box side squared (`θ ρ²` physically). DERIVED: no numeral. -/
def heatScreen (S : Sched G) (θ ρ : ℝ) (k : ℕ) (O : LField G) :
    (Fin 4 → Fin (scrSide S ρ k)) → C(IConf G, ℝ) :=
  linScreen (bareScreen S ρ k O) (boxF (scrSide S ρ k)) (heatF (scrSide S ρ k) θ)

/-- **The bare condition ratio along the zoom**: one `Q` with, eventually, for every `O ∈ D`, some `c ≥ 0`
bounding the bare covariance on the box in operator norm, `ν_k((∑ u_x P_x)²) ≤ c ∑ u_x²`, with
`c ∑_β heatW_β ≤ Q ∑_y ν_k(F_y²)` for the heat screen `F`. DERIVED: `2` the squares; `0` the sign. -/
def BareRatio (S : Sched G) (D : Set (LField G)) (ρ θ : ℝ) : Prop :=
  ∃ Q : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, ∃ c : ℝ, 0 ≤ c ∧
    (∀ u : (Fin 4 → Fin (scrSide S ρ k)) → ℝ,
      S.ν k ((∑ x, u x • bareScreen S ρ k O x) ^ 2) ≤ c * ∑ x, u x ^ 2) ∧
    c * (∑ β, heatW (scrSide S ρ k) θ β) ≤ Q * ∑ y, S.ν k (heatScreen S θ ρ k O y ^ 2)

/-- **A finite aperture holds a finite count, for the heat screen**: given `BareRatio`, the Rényi-½ count of the
heat screen of fixed physical side `ρ` is at most `Rheat θ · max(Q, 0)` along the zoom.
DERIVED: `0` the signs and the empty case. -/
theorem count_heatScreen (S : Sched G) (D : Set (LField G)) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    (h : BareRatio S D ρ θ) :
    ∃ Rb : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, spRenyi (eig (S.ν k) (heatScreen S θ ρ k O)) ≤ Rb := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨Rheat θ * max Q 0, ?_⟩
  filter_upwards [hQ] with k hk O hO
  obtain ⟨c, hc, hC, hratio⟩ := hk O hO
  have hK : 0 < scrSide S ρ k := Nat.ceil_pos.2 (div_pos hρ (S.a_pos k))
  haveI : Nonempty (Fin (scrSide S ρ k)) := ⟨⟨0, hK⟩⟩
  have hW := heatW_pos (scrSide S ρ k) θ
  have hR := spRenyi_heatW_le (scrSide S ρ k) hK hθ
  have hR0 : 0 ≤ spRenyi (heatW (scrSide S ρ k) θ) := by unfold spRenyi; positivity
  have hlin := spRenyi_linScreen_le (S.ν k) (bareScreen S ρ k O) (boxF (scrSide S ρ k))
    (heatF (scrSide S ρ k) θ) (boxF_cols _) (boxF_rows _) hc hC
  have hS : 0 < ∑ β, heatW (scrSide S ρ k) θ β :=
    Finset.sum_pos (fun β _ => hW β) Finset.univ_nonempty
  have hsq : (∑ β, |heatF (scrSide S ρ k) θ β|) ^ 2
      = spRenyi (heatW (scrSide S ρ k) θ) * ∑ β, heatW (scrSide S ρ k) θ β := by
    rw [spRenyi_eq_sq_div _ (fun β => (hW β).le), div_mul_cancel₀ _ hS.ne']
    congr 1
    exact Finset.sum_congr rfl fun β _ => abs_of_nonneg (Real.sqrt_nonneg _)
  rw [hsq] at hlin
  have hT0 : 0 ≤ ∑ y, S.ν k (heatScreen S θ ρ k O y ^ 2) :=
    Finset.sum_nonneg fun y _ => (S.ν k).nonneg _ fun x => by
      simp only [ContinuousMap.pow_apply]; positivity
  change spRenyi (eig (S.ν k) (heatScreen S θ ρ k O))
      ≤ c * (spRenyi (heatW (scrSide S ρ k) θ) * ∑ β, heatW (scrSide S ρ k) θ β)
        / ∑ y, S.ν k (heatScreen S θ ρ k O y ^ 2) at hlin
  rcases hT0.eq_or_lt with hT | hT
  · rw [← hT, div_zero] at hlin
    exact hlin.trans (mul_nonneg (hR0.trans hR) (le_max_right _ _))
  · calc spRenyi (eig (S.ν k) (heatScreen S θ ρ k O))
        ≤ c * (spRenyi (heatW (scrSide S ρ k) θ) * ∑ β, heatW (scrSide S ρ k) θ β)
            / ∑ y, S.ν k (heatScreen S θ ρ k O y ^ 2) := hlin
      _ = spRenyi (heatW (scrSide S ρ k) θ) * (c * (∑ β, heatW (scrSide S ρ k) θ β)
            / ∑ y, S.ν k (heatScreen S θ ρ k O y ^ 2)) := by ring
      _ ≤ spRenyi (heatW (scrSide S ρ k) θ) * Q := by
          apply mul_le_mul_of_nonneg_left _ hR0
          rw [div_le_iff₀ hT]
          exact hratio
      _ ≤ spRenyi (heatW (scrSide S ρ k) θ) * max Q 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hR0
      _ ≤ Rheat θ * max Q 0 := mul_le_mul_of_nonneg_right hR (le_max_right _ _)

/-- **`CountBoundG` from the Dirichlet-mode diagonal**: for every flow `W`, if the Rényi-½ count of the flowed
screen's Dirichlet-mode variances `ν_k((∑_y boxF_{yβ} cScreen_y)²)` is bounded along the zoom, then
`CountBoundG S W D ρ`. DERIVED: `2` the square. -/
theorem countBoundG_of_sineCount (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (ρ : ℝ)
    (h : ∃ Q : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D,
      spRenyi (fun β => S.ν k ((∑ y, boxF (scrSide S ρ k) y β • cScreen S W ρ k O y) ^ 2)) ≤ Q) :
    CountBoundG S W D ρ := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, hQ.mono fun k hk O hO =>
    (spRenyi_eig_le_diag (S.ν k) (cScreen S W ρ k O) (boxF (scrSide S ρ k)) (boxF_cols _)
      (boxF_rows _)).trans (hk O hO)⟩

end Tower

open MassGap.MeasuredTower (schedAlongG)

/-- **The class-moment clause `hU` of (E) from the Dirichlet-mode count**: `CountMoments.hU_of_count` with H3
supplied by `countBoundG_of_sineCount`. DERIVED: `2` the least rank and the square; `0` the sign of `ρ`. -/
theorem hU_of_sineCount {N : ℕ} [NeZero N] [Fact (2 ≤ N)] (βs : ℕ → ℝ) (W : ConfFlowG (MassGap.SUN.SU N))
    {ρ : ℝ} (hρ : 0 < ρ)
    (h1 : ModeHyperG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) ρ)
    (h3 : ∃ Q : ℝ, ∀ᶠ k in atTop, ∀ O ∈ MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N),
      spRenyi (fun β => (schedAlongG _ βs).ν k
        ((∑ y, boxF (scrSide (schedAlongG _ βs) ρ k) y β • cScreen (schedAlongG _ βs) W ρ k O y) ^ 2)) ≤ Q)
    (hv : PhysVarG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)))
    (hm : PhysMeanG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))) :
    ∃ t C₀ : ℝ, 0 < t ∧ 0 ≤ C₀ ∧
      MassGap.ObserverLinkedG.ClassMomentsG (schedAlongG _ βs) W
        (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) t C₀ :=
  hU_of_count βs W hρ h1 (countBoundG_of_sineCount _ W _ ρ h3) hv hm

#print axioms count_heatScreen
#print axioms countBoundG_of_sineCount
#print axioms hU_of_sineCount

end MassGap.ApertureFinite

end
