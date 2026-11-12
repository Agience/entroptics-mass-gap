import Mathlib
import MassGap.TensionFloor
import MassGap.VortexAperture
import MassGap.SlabKernelOperator
import MassGap.KernelGap

/-!
# MassGap.ElectricLoops — electric flux loops as states on the slice, and the gap from their cost

`SizePartition` sorts the slice's configuration space by the size of the magnetic vortex lines and finds that
per-piece Rayleigh bounds against the vacuum cannot give `m > 0` once the vacuum has weight off every piece
(`nonpos_of_balanced`). The author's picture (gluons attract; a flux tube of length `R` costs `σR`; photons do not
attract) is electric: an electric flux loop `C` is the state `W_C Ω`, not a region of configuration space.
This module builds that version on the real objects at `SU(2)`: the slice of step `i` at side `n`
(`TensionFloor.Slice n i`, Haar `hSN 2 n i`), the zero-flux kernel `trivKN 2 β n i`, the half-time kernel
`halfKN 2 β n i`, and the electric-flux ratio `VortexAperture.elecRatio`.

## 1. The abstract reduction (proved, any real inner product space)

* `OrthBound T Ω κ`: `‖T f‖ ≤ κ ‖f‖` for `f ⊥ Ω`. `Generates Ω S` (E1, abstract): every `f ⊥ Ω` lies in
  the closure of `span S`.
* **`spanBound_iff`**: for generators orthogonal to `Ω` and (E1), the bound on `span S` is `OrthBound`.
  Asked on the span, (E1) + (E2) restates the bound.
* **`diagonal_not_span`**: for orthonormal `e₁, e₂` with `T e₁ = 0`, `T e₂ = e₂`, the generators
  `e₁ ± ε e₂` satisfy `‖T u‖ ≤ ε ‖u‖`, span `e₂`, and `‖T e₂‖ = ‖e₂‖`. A per-generator bound at any
  rate does not bound the span: the cross terms `⟪T u, T v⟫` carry what the diagonal does not.
* `schur_finset`, **`bound_on_shells`**, `orthBound_of_shells`: mutually orthogonal shells `S_k`, block
  bounds `|⟪T x, T y⟫| ≤ b_kl ‖x‖‖y‖` (`x ∈ S_k`, `y ∈ S_l`, `b ≥ 0` symmetric) and row sums
  `Σ_l b_kl ≤ κ²` give `‖T f‖ ≤ κ ‖f‖` on the closure of `⨆ S_k` (Schur's test).
* **`exists_shells_iff`**: with the shells existentially quantified, the shell form is `OrthBound` (one
  shell, `Ω⊥`). The shell form carries content only through shells fixed in advance.

## 2. Loops on the slice (defined; the identities proved)

* `Step i = Dir i × Bool`, `next`, `letter`, `walk y s` (the oriented links of the path `s` from `y`),
  `endpt`, `rev`; `wh w V` the ordered holonomy of a word. `walk_append`, `endpt_rev`, **`wh_rev`** (the
  reversed path has the inverse holonomy).
* `Loop i T`: a base site and a path returning to it. `Loop.hol`, **`Loop.wl`** `= Re tr hol_C`,
  `Loop.len` (perimeter in lattice units), `Loop.inv`, `Loop.comp`, `Loop.conj`. `continuous_wl`,
  `abs_wl_le` (`|W_C| ≤ 2`).
* `su2_trace_im` (the `SU(2)` trace is real), **`su2_mandelstam`** (`tr A · tr B = tr AB + tr AB⁻¹`),
  **`Loop.wl_mul`**: `W_C W_{C'} = W_{C C'} + W_{C C'⁻¹}` for loops at one base; **`Loop.wl_conj`**: moving
  the base along a path leaves `W` unchanged; `wl_nil`: the empty loop has `W = 2`. So the span of the
  Wilson loops at one base is a unital algebra of continuous functions, and loops at different bases join
  it through `Loop.wl_conj` given a connecting path (that the torus has one is not a declaration).
* `gauge h V` (`V(ν, y) ↦ h(y) V(ν, y) h(y + ν)⁻¹`), `wh_walk_gauge`, **`Loop.wl_gauge`**: every Wilson loop
  is gauge invariant.

## 3. Loop states, size filtration, shells (defined; the structure proved)

* `vev μ Ω C = ∫ W_C Ω²`, **`loopState μ Ω C = (W_C − ⟨W_C⟩) Ω`**. `loopState_orth`: `∫ Ω ψ_C = 0` when
  `∫ Ω² = 1`. `memLp_loopState`: `ψ_C ∈ L²` for bounded measurable `Ω`.
* `loopSet μ Ω a R`: the `L²` classes of `ψ_C` with `a · len C ≤ R` (physical perimeter at spacing `a`);
  **`H μ Ω a R`** their span; `H_mono`. `finite_loopSet` (`a > 0`): finitely many, so
  `hasOrthogonalProjection_H`.
* `shellOf`, **`shell μ Ω a R k`**: `S₀ = H_{R₀}`, `S_{k+1} = H_{R_{k+1}} ⊓ H_{R_k}⊥`. `shellOf_orth`,
  `shell_orth`: mutually orthogonal. `le_iSup_shellOf`, **`span_allLoops_le`**: for radii `R_k` monotone
  and reaching every perimeter, the span of all loop states lies in `⨆ S_k`.

## 4. The gap on the real slice (proved, conditional on (E1) and (E2'))

On `TensionFloor.EigenLevels β n i g₀ E φ μ` with measurable `φ_j` and the `L²` operator `kernelCLM` of
`trivKN 2 β n i`, `t = n · aRun 2 β`:

* `trivKN_vecOf`: the operator acts on `φ_j` by `μ_j`. **`zeroFluxGap_of_levelBound`**:
  `‖T φ_j‖ ≤ |μ_{g₀}| e^{−m t/2} ‖φ_j‖` for every `j ≠ g₀` gives `ZeroFluxGap g₀ E m`;
  `zeroFluxGap_of_orthBound`: so does `OrthBound` at `Ω = φ_{g₀}`.
* **`zeroFluxGap_of_loopShells`**: (E1) every excited level `φ_j` is in the closure of the span of the loop
  states of `Ω = φ_{g₀}`, and (E2') the transfer blocks between the loop shells of radii `R_k` have
  symmetric bounds `b_kl` with row sums at most `μ_{g₀}² e^{−m t}`: then `ZeroFluxGap g₀ E m`.
* **`zeroFluxGap_of_electricCost`**: (E2') in the attraction form. Shell radii `R_k > 0`; the diagonal block
  of shell `k` costs the tension and the localisation at its own radius,
  `b_kk ≤ μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`; the off-diagonal row sums are at most `μ_{g₀}² η`. Then
  `ZeroFluxGap g₀ E m` with `e^{−m t} = e^{−2√(c c' σ) t} + η` (`AttractCost.two_sqrt_le_cost`;
  `rowSum_le`). Arithmetic, not a declaration: `m > 0` exactly when `η < 1 − e^{−2√(c c' σ) t}`.

## 5. Winding loops and (V) (proved)

* `rsec a act ψ` (the real sector kernel of a real character), `sectorTrace_eq_hs`, `integral_rsec`, and
  **`sector_bound`**: a bounded state `f` with `f ∘ act g = Re ψ(g) · f` has
  `‖a f‖² ≤ sectorTrace ψ · ‖f‖²`. **`zk_sector_eq_zero`**: for `ψ ≠ 1` the zero-flux kernel annihilates it.
* `windLoop ν y`: the straight loop winding once in direction `ν` (`iterate_tsh_period`: it closes).
  `charge_windLoop`, **`wl_windLoop_act`**: through `y_ν = 0` it crosses the twisted links once, so
  `W(act g V) = Re e(g_ν) · W(V)`. `chi ν` the character `g ↦ e(g_ν)`, real (`chi_im`) and odd under the
  twist `e_ν` (`chi_single`). `windState ν y Ω = W_ν Ω`; `windState_act`: for centre-invariant `Ω` it lies
  in the sector `chi ν`.
* **`trivKN_windState`**: `trivKN` annihilates a winding state: it carries electric flux.
* **`winding_transfer_le`**: `‖halfKN f‖² ≤ oddFlux β n i ν · ‖f‖²` for `f = W_ν Ω`.
  `oddFlux_le_elecRatio` (`n ≥ 2` even): `oddFlux ≤ elecRatio · hs(halfKN)`.
* **`winding_cost_of_elec`**: `elecRatio β n i ν ≤ A e^{−σ n a}` gives
  `‖halfKN f‖² ≤ A e^{−σ n a} · hs(halfKN) · ‖f‖²`; **`windingCost_of_vortexCostAt`**: `VortexCostAt σ A ℓ`
  gives this, eventually in `β`, on the whole window of (V).

## Evaluation

* Search: no Wilson-loop state on a slice, and no transfer matrix element of a loop operator, is in the live
  tree or in the pruned archive (tainted modules skipped). The tree's loops are expectations on the 4-torus
  (`TomboulisYaffe.wHol`, `VortexCondense.rectHol`/`wloopR`, `WilsonLattice.wilsonHol`) or a plaquette on the
  slice (`SizePartition.plaqHol`); the archive's `ClassOSSpace` takes loops as local fields of the
  Osterwalder–Schrader reconstruction and needs no Giles step. The `SU(2)` Mandelstam identity is
  `su2_mandelstam` here; Giles reconstruction at `SU(2)` is `LoopsGenerate.giles`. `Step`, `Loop`, `loopState`, `H`, `shell`,
  `windLoop`, `rsec` are new.
* (E1). Proved: the algebraic half. Wilson loops are gauge invariant and continuous, their span contains the
  constants and is closed under products at one base (`Loop.wl_mul`), and across bases given a connecting
  path (`Loop.wl_conj`).
  The analytic half is proved in `LoopsGenerate` (`excited_mem_closure_loops`, at `β > 0`): Wilson loops
  separate gauge orbits (`giles`), Stone–Weierstrass gives density, the ground level is nowhere zero
  (`ground_ne_zero`) and the excited levels are gauge invariant (`level_gauge`); so every excited level lies
  in the closed span of the loop states, which is the `hgen` input of `zeroFluxGap_of_loopShells`
  (`LoopsGenerate.zeroFluxGap_of_loopShells_E2`). (E1) is asked of the excited levels only; on all of `L²(slice)` it fails (argued), since loop states are gauge invariant and `L²(slice)`
  contains states that are not.
* What (V) gives (proved): the winding loops. A winding state lies in a sector odd under the twist `e_ν`,
  `trivKN` kills it, and its transfer is bounded by `oddFlux`, hence by `elecRatio · hs(halfKN)`, hence under
  (V) by `A e^{−σ n a} · hs(halfKN)` on the window. The bound is one-directional: `sectorTrace` is a
  Hilbert–Schmidt sum over the whole sector, so a bound on one state does not return (V). It is relative to
  the full trace `hs(halfKN)`, not to `μ_{g₀}²`; the ratio `hs(halfKN)/μ_{g₀}²` contains the
  normalised zero-flux heat trace of `GlueballArea.ZeroFluxCount` plus the non-zero-flux sectors; it is not
  bounded here. And it is the rate `σ` per length that (V) asks
  (`e^{−σ n a}`), not the area cost `σ L t` (argued in `VortexAperture`).
* What is new: the contractible loops. Their charge (signed crossing number) is even, so (argued, not a
  declaration) their states are centre-invariant and lie in the zero-flux sector, which `oddFlux` and
  `elecRatio` do not see: (V) constrains none of their transfer elements. The diagonal clause of
  `zeroFluxGap_of_electricCost` (a closed flux loop of size `R` costs `c σ R` at one transfer time) is the
  converse Tomboulis–Yaffe statement, and the coupling `η` between shells is a second input. Neither is
  proved. On the class of kernels the sector machinery uses, neither follows from (V)
  (`AttractCost`: a neutral factor invisible to every twist, `FiniteReadingFlux.wilson_neutral`).
* Is "(E1) + (E2) at all sizes" the gap? Measured against the free parameter:
  - (E2) asked on the span: equivalent to the bound (`spanBound_iff`), a restatement.
  - (E2) asked per loop (diagonal), at any rate: not sufficient (`diagonal_not_span`).
  - (E2) in shell form with the shells free: equivalent to the bound (`exists_shells_iff`).
  - (E2') with the shells fixed by loop geometry (`shell`: loops of physical perimeter in `(R_{k−1}, R_k]`,
    orthogonalised against the smaller ones): the minimal form that reduces the gap without restating it
    (`zeroFluxGap_of_loopShells`). Its free data are the block numbers `b`, bounded below by the real
    transfer's block inner products, and in the attraction form the constants `c, c'` (which, as in
    `AttractCost`, set the gap's value with `σ` only labelling the cost). Argued, not a declaration: (E2')
    is strictly stronger than the gap, since infinitely many orthogonal one-dimensional shells and a
    rank-one `T` along a unit vector whose shell coefficients are not summable have bounded `T` and
    unbounded row sums. So the reduction is a sufficient condition, not an equivalence.
  - Time: the statements are matrix-element bounds at the one transfer time `t = n a` of `trivKN`. Argued:
    a bound `e^{−σ R t}` for all `t` cannot hold for large loops, since the decay rate in `t` of any state
    orthogonal to `Ω` with a component on the lowest excited level is that level's gap.
* Uniformity: every theorem here is at one `(β, n, i)`. For `RunSeed` the inputs would be needed with
  `c, c', σ, η` fixed on the window, uniformly as `β → ∞`; nothing here addresses that.

DERIVED (module-wide): `2` is `N` for `SU(2)`, the bound `|tr| ≤ 2`, the empty loop's trace, the `L²`
exponent and the square in `‖·‖²`, and `t/2` the half time of `μ_j² = e^{−E_j t}`; `1/2` in
`schur_finset` is `xy ≤ (x² + y²)/2`; `(2ε)⁻¹` recovers `e₂` from `(e₁ + εe₂) − (e₁ − εe₂)`; `0` is the
coordinate of the twisted links (`SliceCentreAction.lc`) and the trivial loop; `1` the unit norm and the
generator of `Z₂`; `5` and `2` in `windingCost_of_vortexCostAt` are the window of `FluxCost.VortexCostAt`;
`2√(c c' σ)` is `AttractCost.two_sqrt_le_cost`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ElectricLoops

open MeasureTheory Filter Finset

/-! ## 1. Abstract reduction -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The relative bound on `Ω⊥`**: `‖T f‖ ≤ κ ‖f‖` for every `f ⊥ Ω`. -/
def OrthBound (T : E →L[ℝ] E) (Ω : E) (κ : ℝ) : Prop :=
  ∀ f : E, inner ℝ Ω f = 0 → ‖T f‖ ≤ κ * ‖f‖

/-- **(E1), abstract**: every vector orthogonal to `Ω` is a limit of combinations of `S`. -/
def Generates (Ω : E) (S : Set E) : Prop :=
  ∀ f : E, inner ℝ Ω f = 0 → f ∈ closure (Submodule.span ℝ S : Set E)

/-- The bound defines a closed set. -/
theorem isClosed_bound (T : E →L[ℝ] E) (κ : ℝ) : IsClosed {f : E | ‖T f‖ ≤ κ * ‖f‖} :=
  isClosed_le (continuous_norm.comp T.continuous) (continuous_const.mul continuous_norm)

/-- A bound on a set extends to its closure. -/
theorem orthBound_of_closure {T : E →L[ℝ] E} {Ω : E} {κ : ℝ} {M : Set E}
    (hgen : ∀ f : E, inner ℝ Ω f = 0 → f ∈ closure M) (h : ∀ ψ ∈ M, ‖T ψ‖ ≤ κ * ‖ψ‖) :
    OrthBound T Ω κ := fun f hf =>
  closure_minimal h (isClosed_bound T κ) (hgen f hf)

/-- (E1) and the bound on the span give the bound on `Ω⊥`. -/
theorem orthBound_of_span {T : E →L[ℝ] E} {Ω : E} {κ : ℝ} {S : Set E} (hgen : Generates Ω S)
    (h : ∀ ψ ∈ Submodule.span ℝ S, ‖T ψ‖ ≤ κ * ‖ψ‖) : OrthBound T Ω κ :=
  orthBound_of_closure hgen h

/-- Combinations of vectors orthogonal to `Ω` are orthogonal to `Ω`. -/
theorem span_orth {Ω : E} {S : Set E} (hS : ∀ s ∈ S, inner ℝ Ω s = 0) :
    ∀ ψ ∈ Submodule.span ℝ S, inner ℝ Ω ψ = 0 := by
  intro ψ hψ
  have hle : Submodule.span ℝ S ≤ (ℝ ∙ Ω)ᗮ := by
    rw [Submodule.span_le]
    intro s hs
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 (hS s hs)
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hψ)

/-- **With the bound asked on the span, (E1) + (E2) is the bound on `Ω⊥`**: for generators
orthogonal to `Ω`, the two are equivalent. -/
theorem spanBound_iff {T : E →L[ℝ] E} {Ω : E} {κ : ℝ} {S : Set E} (hgen : Generates Ω S)
    (hS : ∀ s ∈ S, inner ℝ Ω s = 0) :
    (∀ ψ ∈ Submodule.span ℝ S, ‖T ψ‖ ≤ κ * ‖ψ‖) ↔ OrthBound T Ω κ :=
  ⟨orthBound_of_span hgen, fun h ψ hψ => h ψ (span_orth hS ψ hψ)⟩

/-- **Schur's test on orthogonal blocks**: for pairwise orthogonal `x_k`, block bounds
`|⟪T x_k, T x_l⟫| ≤ b_kl ‖x_k‖ ‖x_l‖` with `b ≥ 0` symmetric and row sums at most `κ²` give
`‖T Σ x_k‖² ≤ κ² ‖Σ x_k‖²`. -/
theorem schur_finset {ι : Type*} (s : Finset ι) (T : E →L[ℝ] E) (x : ι → E)
    (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → inner ℝ (x k) (x l) = 0)
    (b : ι → ι → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k ∈ s, ∀ l ∈ s, |inner ℝ (T (x k)) (T (x l))| ≤ b k l * (‖x k‖ * ‖x l‖))
    {κ : ℝ} (hrow : ∀ k ∈ s, ∑ l ∈ s, b k l ≤ κ ^ 2) :
    ‖T (∑ k ∈ s, x k)‖ ^ 2 ≤ κ ^ 2 * ‖∑ k ∈ s, x k‖ ^ 2 := by
  have hn : ‖∑ k ∈ s, x k‖ ^ 2 = ∑ k ∈ s, ‖x k‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [inner_sum, Finset.sum_eq_single k (fun l hl hlk => horth k hk l hl (Ne.symm hlk))
      (fun h => absurd hk h), real_inner_self_eq_norm_sq]
  have hT : ‖T (∑ k ∈ s, x k)‖ ^ 2 = ∑ k ∈ s, ∑ l ∈ s, inner ℝ (T (x k)) (T (x l)) := by
    rw [← real_inner_self_eq_norm_sq, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
  have h1 : ∑ k ∈ s, ∑ l ∈ s, inner ℝ (T (x k)) (T (x l))
      ≤ ∑ k ∈ s, ∑ l ∈ s, (b k l * ‖x k‖ ^ 2 / 2 + b l k * ‖x l‖ ^ 2 / 2) := by
    refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => ?_
    have h2 : ‖x k‖ * ‖x l‖ ≤ (‖x k‖ ^ 2 + ‖x l‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖x k‖ - ‖x l‖)]
    calc inner ℝ (T (x k)) (T (x l)) ≤ |inner ℝ (T (x k)) (T (x l))| := le_abs_self _
      _ ≤ b k l * (‖x k‖ * ‖x l‖) := hblk k hk l hl
      _ ≤ b k l * ((‖x k‖ ^ 2 + ‖x l‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 (hb0 k l)
      _ = _ := by rw [hsym l k]; ring
  have h3 : ∑ k ∈ s, ∑ l ∈ s, (b k l * ‖x k‖ ^ 2 / 2 + b l k * ‖x l‖ ^ 2 / 2)
      = ∑ k ∈ s, ‖x k‖ ^ 2 * ∑ l ∈ s, b k l := by
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => b l k * ‖x l‖ ^ 2 / 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h4 : ∑ k ∈ s, ‖x k‖ ^ 2 * ∑ l ∈ s, b k l ≤ ∑ k ∈ s, ‖x k‖ ^ 2 * κ ^ 2 :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hrow k hk) (sq_nonneg _)
  rw [hT, hn, Finset.mul_sum]
  calc _ ≤ _ := h1
    _ = _ := h3
    _ ≤ _ := h4
    _ = _ := Finset.sum_congr rfl fun k _ => by ring

/-- **Schur's test on shells**: mutually orthogonal shells, symmetric block bounds and row sums at
most `κ²` bound `T` by `κ` on the closure of the span of the shells. -/
theorem bound_on_shells {ι : Type*} {T : E →L[ℝ] E} (S : ι → Submodule ℝ E)
    (horth : ∀ k l, k ≠ l → ∀ x ∈ S k, ∀ y ∈ S l, inner ℝ x y = 0)
    (b : ι → ι → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k l, ∀ x ∈ S k, ∀ y ∈ S l, |inner ℝ (T x) (T y)| ≤ b k l * (‖x‖ * ‖y‖))
    {κ : ℝ} (hκ : 0 ≤ κ) (hrow : ∀ k (s : Finset ι), ∑ l ∈ s, b k l ≤ κ ^ 2) :
    ∀ f ∈ closure ((⨆ k, S k : Submodule ℝ E) : Set E), ‖T f‖ ≤ κ * ‖f‖ := by
  classical
  refine closure_minimal (fun ψ hψ => ?_) (isClosed_bound T κ)
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hψ
  obtain ⟨c, hc⟩ := (Submodule.mem_iSup_finset_iff_exists_sum S ψ).1 hs
  have key := schur_finset s T (fun k => (c k : E))
    (fun k _ l _ hkl => horth k l hkl _ (c k).2 _ (c l).2) b hb0 hsym
    (fun k _ l _ => hblk k l _ (c k).2 _ (c l).2) (fun k _ => hrow k s)
  rw [hc] at key
  have hc0 : 0 ≤ κ * ‖ψ‖ := mul_nonneg hκ (norm_nonneg _)
  rw [← mul_pow] at key
  exact le_of_pow_le_pow_left₀ two_ne_zero hc0 key

/-- **The shell form gives the bound on `Ω⊥`** when the shells generate `Ω⊥`. -/
theorem orthBound_of_shells {ι : Type*} {T : E →L[ℝ] E} {Ω : E} (S : ι → Submodule ℝ E)
    (horth : ∀ k l, k ≠ l → ∀ x ∈ S k, ∀ y ∈ S l, inner ℝ x y = 0)
    (hgen : ∀ f : E, inner ℝ Ω f = 0 → f ∈ closure ((⨆ k, S k : Submodule ℝ E) : Set E))
    (b : ι → ι → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k l, ∀ x ∈ S k, ∀ y ∈ S l, |inner ℝ (T x) (T y)| ≤ b k l * (‖x‖ * ‖y‖))
    {κ : ℝ} (hκ : 0 ≤ κ) (hrow : ∀ k (s : Finset ι), ∑ l ∈ s, b k l ≤ κ ^ 2) :
    OrthBound T Ω κ := fun f hf =>
  bound_on_shells S horth b hb0 hsym hblk hκ hrow f (hgen f hf)

/-- **With the shells free, the shell form is the bound** (one shell, `Ω⊥`, block bound `κ²`). -/
theorem exists_shells_iff {T : E →L[ℝ] E} {Ω : E} {κ : ℝ} (hκ : 0 ≤ κ) :
    (∃ (ι : Type) (S : ι → Submodule ℝ E) (b : ι → ι → ℝ),
      (∀ k l, k ≠ l → ∀ x ∈ S k, ∀ y ∈ S l, inner ℝ x y = 0) ∧
      (∀ f : E, inner ℝ Ω f = 0 → f ∈ closure ((⨆ k, S k : Submodule ℝ E) : Set E)) ∧
      (∀ k l, 0 ≤ b k l) ∧ (∀ k l, b k l = b l k) ∧
      (∀ k l, ∀ x ∈ S k, ∀ y ∈ S l, |inner ℝ (T x) (T y)| ≤ b k l * (‖x‖ * ‖y‖)) ∧
      (∀ k (s : Finset ι), ∑ l ∈ s, b k l ≤ κ ^ 2)) ↔ OrthBound T Ω κ := by
  constructor
  · rintro ⟨ι, S, b, h1, h2, h3, h4, h5, h6⟩
    exact orthBound_of_shells S h1 h2 b h3 h4 h5 hκ h6
  · intro h
    refine ⟨Unit, fun _ => (ℝ ∙ Ω)ᗮ, fun _ _ => κ ^ 2, fun k l hkl => absurd (Subsingleton.elim k l) hkl,
      fun f hf => subset_closure ?_, fun _ _ => sq_nonneg κ, fun _ _ => rfl, ?_, ?_⟩
    · exact (le_iSup (fun _ : Unit => (ℝ ∙ Ω)ᗮ) ()) ((Submodule.mem_orthogonal_singleton_iff_inner_right).2 hf)
    · intro k l x hx y hy
      have hx' := h x ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hx)
      have hy' := h y ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy)
      calc |inner ℝ (T x) (T y)| ≤ ‖T x‖ * ‖T y‖ := abs_real_inner_le_norm _ _
        _ ≤ (κ * ‖x‖) * (κ * ‖y‖) :=
          mul_le_mul hx' hy' (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))
        _ = κ ^ 2 * (‖x‖ * ‖y‖) := by ring
    · intro k s
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (s.card : ℝ) ≤ 1 := by
        exact_mod_cast (Finset.card_le_univ s).trans (by simp)
      nlinarith [sq_nonneg κ]

/-- **Diagonal bounds on generators do not bound their span**: `e₁ ± ε e₂` have `‖T u‖ ≤ ε ‖u‖`
and span `e₂`, on which `‖T e₂‖ = ‖e₂‖`. -/
theorem diagonal_not_span {e₁ e₂ : E} (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : inner ℝ e₁ e₂ = 0)
    {T : E →L[ℝ] E} (hT1 : T e₁ = 0) (hT2 : T e₂ = e₂) {ε : ℝ} (hε : 0 < ε) :
    ‖T (e₁ + ε • e₂)‖ ≤ ε * ‖e₁ + ε • e₂‖ ∧ ‖T (e₁ - ε • e₂)‖ ≤ ε * ‖e₁ - ε • e₂‖ ∧
      e₂ ∈ Submodule.span ℝ ({e₁ + ε • e₂, e₁ - ε • e₂} : Set E) ∧ ‖T e₂‖ = ‖e₂‖ := by
  have hp : T (e₁ + ε • e₂) = ε • e₂ := by rw [map_add, map_smul, hT1, hT2, zero_add]
  have hm : T (e₁ - ε • e₂) = -(ε • e₂) := by rw [map_sub, map_smul, hT1, hT2, zero_sub]
  have hnp : 1 ≤ ‖e₁ + ε • e₂‖ := by
    have h := norm_add_sq_real e₁ (ε • e₂)
    rw [inner_smul_right, h12, norm_smul, h1, h2, Real.norm_eq_abs, abs_of_pos hε] at h
    nlinarith [norm_nonneg (e₁ + ε • e₂)]
  have hnm : 1 ≤ ‖e₁ - ε • e₂‖ := by
    have h := norm_sub_sq_real e₁ (ε • e₂)
    rw [inner_smul_right, h12, norm_smul, h1, h2, Real.norm_eq_abs, abs_of_pos hε] at h
    nlinarith [norm_nonneg (e₁ - ε • e₂)]
  refine ⟨?_, ?_, ?_, by rw [hT2]⟩
  · rw [hp, norm_smul, h2, Real.norm_eq_abs, abs_of_pos hε, mul_one]
    nlinarith
  · rw [hm, norm_neg, norm_smul, h2, Real.norm_eq_abs, abs_of_pos hε, mul_one]
    nlinarith
  · have hc : (2 * ε)⁻¹ * 2 * ε = 1 := by field_simp
    have he : (2 * ε)⁻¹ • ((e₁ + ε • e₂) - (e₁ - ε • e₂)) = e₂ := by
      rw [add_sub_sub_cancel, ← two_smul ℝ (ε • e₂), smul_smul, smul_smul, hc, one_smul]
    have hmem : (2 * ε)⁻¹ • ((e₁ + ε • e₂) - (e₁ - ε • e₂))
        ∈ Submodule.span ℝ ({e₁ + ε • e₂, e₁ - ε • e₂} : Set E) :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp)))
    rwa [he] at hmem

end Abstract

/-! ## 2. Loops on the slice -/

section Loops

open MassGap.RectWilson (SpT TT tsh)

/-- A transverse direction of the slice of step `i`. -/
abbrev Dir (i : Fin 4) : Type := {j : Fin 4 // j ≠ i}

/-- One step of a lattice path: a direction and an orientation (`true` forward). -/
abbrev Step (i : Fin 4) : Type := Dir i × Bool

variable {i : Fin 4} {T : Dir i → ℕ}

/-- One transverse step backwards. -/
def tshInv (ν : Dir i) (y : TT i T) : TT i T :=
  Function.update y ν ((finRotate (T ν)).symm (y ν))

/-- `tshInv` undoes `tsh`. -/
theorem tshInv_tsh (ν : Dir i) (y : TT i T) : tshInv ν (tsh i T ν y) = y := by
  unfold tshInv tsh
  rw [Function.update_idem, Function.update_self, Equiv.symm_apply_apply, Function.update_eq_self]

/-- `tsh` undoes `tshInv`. -/
theorem tsh_tshInv (ν : Dir i) (y : TT i T) : tsh i T ν (tshInv ν y) = y := by
  unfold tshInv tsh
  rw [Function.update_idem, Function.update_self, Equiv.apply_symm_apply, Function.update_eq_self]

/-- The site after a step. -/
def next (y : TT i T) (s : Step i) : TT i T := if s.2 then tsh i T s.1 y else tshInv s.1 y

/-- The oriented link a step crosses. -/
def letter (y : TT i T) (s : Step i) : SpT i T × Bool :=
  if s.2 then ((s.1, y), true) else ((s.1, tshInv s.1 y), false)

/-- The oriented links of a path from `y`. -/
def walk : TT i T → List (Step i) → List (SpT i T × Bool)
  | _, [] => []
  | y, s :: ss => letter y s :: walk (next y s) ss

/-- The end point of a path from `y`. -/
def endpt : TT i T → List (Step i) → TT i T
  | y, [] => y
  | y, s :: ss => endpt (next y s) ss

/-- The links of a concatenated path. -/
theorem walk_append (y : TT i T) (s s' : List (Step i)) :
    walk y (s ++ s') = walk y s ++ walk (endpt y s) s' := by
  induction s generalizing y with
  | nil => rfl
  | cons a ss ih => simp only [List.cons_append, walk, endpt, ih]

/-- The end point of a concatenated path. -/
theorem endpt_append (y : TT i T) (s s' : List (Step i)) :
    endpt y (s ++ s') = endpt (endpt y s) s' := by
  induction s generalizing y with
  | nil => rfl
  | cons a ss ih => simp only [List.cons_append, endpt, ih]

/-- The reversed step. -/
def flip (s : Step i) : Step i := (s.1, !s.2)

/-- The reversed path. -/
def rev (s : List (Step i)) : List (Step i) := (s.map flip).reverse

/-- Reversing a path with one more step. -/
theorem rev_cons (a : Step i) (s : List (Step i)) : rev (a :: s) = rev s ++ [flip a] := by
  simp [rev]

/-- A step and its reverse return to the start. -/
theorem next_flip (y : TT i T) (a : Step i) : next (next y a) (flip a) = y := by
  rcases a with ⟨ν, b⟩
  cases b
  · simp [next, flip, tsh_tshInv]
  · simp [next, flip, tshInv_tsh]

/-- The reversed path returns to the start. -/
theorem endpt_rev (y : TT i T) (s : List (Step i)) : endpt (endpt y s) (rev s) = y := by
  induction s generalizing y with
  | nil => rfl
  | cons a ss ih =>
      rw [rev_cons, endpt_append]
      simp only [endpt]
      rw [ih, next_flip]

/-- **The holonomy of a word** of oriented links: the ordered product. -/
def wh (w : List (SpT i T × Bool)) (V : SpT i T → SUN.SU 2) : SUN.SU 2 :=
  (w.map fun lo => if lo.2 then V lo.1 else (V lo.1)⁻¹).prod

/-- The holonomy of a concatenated word is the product. -/
theorem wh_append (w w' : List (SpT i T × Bool)) (V : SpT i T → SUN.SU 2) :
    wh (w ++ w') V = wh w V * wh w' V := by
  simp [wh]

/-- A reversed step has the inverse holonomy. -/
theorem wh_letter_flip (y : TT i T) (a : Step i) (V : SpT i T → SUN.SU 2) :
    wh [letter (next y a) (flip a)] V = (wh [letter y a] V)⁻¹ := by
  rcases a with ⟨ν, b⟩
  cases b
  · simp [wh, letter, next, flip]
  · simp [wh, letter, next, flip, tshInv_tsh]

/-- **The reversed path has the inverse holonomy.** -/
theorem wh_rev (y : TT i T) (s : List (Step i)) (V : SpT i T → SUN.SU 2) :
    wh (walk (endpt y s) (rev s)) V = (wh (walk y s) V)⁻¹ := by
  induction s generalizing y with
  | nil => simp [wh, walk, rev, endpt]
  | cons a ss ih =>
      rw [rev_cons, walk_append]
      simp only [endpt]
      rw [wh_append, ih, endpt_rev]
      rw [show walk (next y a) [flip a] = [letter (next y a) (flip a)] from rfl, wh_letter_flip,
        show walk y (a :: ss) = [letter y a] ++ walk (next y a) ss from rfl, wh_append, mul_inv_rev]

/-- The holonomy of a word is continuous in the configuration. -/
theorem continuous_wh (w : List (SpT i T × Bool)) :
    Continuous fun V : SpT i T → SUN.SU 2 => wh w V := by
  induction w with
  | nil => simpa [wh] using continuous_const
  | cons x w ih =>
      have hx : Continuous fun V : SpT i T → SUN.SU 2 => if x.2 then V x.1 else (V x.1)⁻¹ := by
        by_cases h : x.2
        · simp only [h, if_true]; exact continuous_apply _
        · simp only [h]; exact (continuous_apply _).inv
      have : (fun V : SpT i T → SUN.SU 2 => wh (x :: w) V)
          = fun V => (if x.2 then V x.1 else (V x.1)⁻¹) * wh w V := by
        funext V; simp [wh]
      rw [this]
      exact hx.mul ih

/-- **A closed lattice loop** on the slice: a base site and a path returning to it. -/
structure Loop (i : Fin 4) (T : Dir i → ℕ) where
  base : TT i T
  steps : List (Step i)
  closed : endpt base steps = base

/-- The holonomy of a loop, from its base. -/
def Loop.hol (C : Loop i T) (V : SpT i T → SUN.SU 2) : SUN.SU 2 := wh (walk C.base C.steps) V

/-- **The Wilson loop** `Re tr hol_C`. -/
def Loop.wl (C : Loop i T) (V : SpT i T → SUN.SU 2) : ℝ :=
  (Matrix.trace (C.hol V : Matrix (Fin 2) (Fin 2) ℂ)).re

/-- The perimeter, in lattice units. -/
def Loop.len (C : Loop i T) : ℕ := C.steps.length

/-- The loop traversed backwards. -/
def Loop.inv (C : Loop i T) : Loop i T :=
  ⟨C.base, rev C.steps, by have h := endpt_rev C.base C.steps; rwa [C.closed] at h⟩

/-- Two loops at one base, composed. -/
def Loop.comp (C C' : Loop i T) (h : C'.base = C.base) : Loop i T :=
  ⟨C.base, C.steps ++ C'.steps, by rw [endpt_append, C.closed, ← h, C'.closed]⟩

/-- The reversed loop has the inverse holonomy. -/
theorem Loop.hol_inv (C : Loop i T) (V : SpT i T → SUN.SU 2) : C.inv.hol V = (C.hol V)⁻¹ := by
  have h := wh_rev C.base C.steps V
  rw [C.closed] at h
  exact h

/-- The composed loop has the product holonomy. -/
theorem Loop.hol_comp (C C' : Loop i T) (h : C'.base = C.base) (V : SpT i T → SUN.SU 2) :
    (C.comp C' h).hol V = C.hol V * C'.hol V := by
  unfold Loop.hol Loop.comp
  simp only
  rw [walk_append, wh_append, C.closed, ← h]

/-- The Wilson loop is continuous in the configuration. -/
theorem continuous_wl (C : Loop i T) : Continuous C.wl := by
  unfold Loop.wl Loop.hol
  exact Complex.continuous_re.comp
    ((continuous_subtype_val.comp (continuous_wh _)).matrix_trace)

/-- `|W_C| ≤ 2`. -/
theorem abs_wl_le (C : Loop i T) (V : SpT i T → SUN.SU 2) : |C.wl V| ≤ 2 := by
  have h := WilsonAction.abs_re_trace_le (C.hol V)
  unfold Loop.wl
  simpa using h

/-! ### The `SU(2)` trace identities -/

/-- On `SU(2)` the adjoint is the adjugate. -/
theorem su2_star_eq_adj (B : SUN.SU 2) :
    star (B : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.adjugate (B : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hB := Matrix.mem_specialUnitaryGroup_iff.mp B.2
  have hu : star (B : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hB.1
  have hma := Matrix.mul_adjugate (B : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hB.2, one_smul] at hma
  calc star (B : Matrix (Fin 2) (Fin 2) ℂ)
      = star (B : Matrix (Fin 2) (Fin 2) ℂ) * ((B : Matrix (Fin 2) (Fin 2) ℂ)
          * Matrix.adjugate (B : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [hma, mul_one]
    _ = Matrix.adjugate (B : Matrix (Fin 2) (Fin 2) ℂ) := by rw [← mul_assoc, hu, one_mul]

/-- `B + adj B = tr B · 1` on `2 × 2` matrices (Cayley–Hamilton). -/
theorem add_adj_fin_two (B : Matrix (Fin 2) (Fin 2) ℂ) :
    B + Matrix.adjugate B = Matrix.trace B • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.trace_fin_two]; ring

/-- **The `SU(2)` trace is real.** -/
theorem su2_trace_im (B : SUN.SU 2) : (Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (su2_star_eq_adj B)
  simp only [Matrix.star_apply, Matrix.adjugate_fin_two] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one] at h
  rw [Matrix.trace_fin_two, Complex.add_im, ← h, Complex.star_def, Complex.conj_im]
  ring

/-- **The `SU(2)` Mandelstam identity**: `tr A · tr B = tr(AB) + tr(AB⁻¹)`. -/
theorem su2_mandelstam (A B : SUN.SU 2) :
    (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ)).re * (Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℂ)).re
      = (Matrix.trace ((A * B : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)).re
        + (Matrix.trace ((A * B⁻¹ : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  have hc : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.trace ((A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ))
        + Matrix.trace ((A : Matrix (Fin 2) (Fin 2) ℂ) * star (B : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [← Matrix.trace_add, ← mul_add, su2_star_eq_adj, add_adj_fin_two, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, mul_comm]
  have hA := su2_trace_im A
  have hB := su2_trace_im B
  have hre := congrArg Complex.re hc
  rw [Complex.mul_re, hA, hB, mul_zero, sub_zero, Complex.add_re] at hre
  rw [hre]
  rfl

/-- **The product of two Wilson loops at one base is a sum of two Wilson loops.** -/
theorem Loop.wl_mul (C C' : Loop i T) (h : C'.base = C.base) (V : SpT i T → SUN.SU 2) :
    C.wl V * C'.wl V = (C.comp C' h).wl V + (C.comp C'.inv h).wl V := by
  unfold Loop.wl
  rw [Loop.hol_comp, Loop.hol_comp, Loop.hol_inv]
  exact su2_mandelstam _ _

/-- A path `p` from `y` to the base of `C'`, `C'`, and `p` back: a loop at `y`. -/
def Loop.conj (C' : Loop i T) (y : TT i T) (p : List (Step i)) (hp : endpt y p = C'.base) :
    Loop i T :=
  ⟨y, p ++ C'.steps ++ rev p, by
    rw [endpt_append, endpt_append, hp, C'.closed, ← hp, endpt_rev]⟩

/-- **Moving the base along a path does not change the Wilson loop.** -/
theorem Loop.wl_conj (C' : Loop i T) (y : TT i T) (p : List (Step i)) (hp : endpt y p = C'.base)
    (V : SpT i T → SUN.SU 2) : (C'.conj y p hp).wl V = C'.wl V := by
  unfold Loop.wl Loop.hol Loop.conj
  simp only
  rw [walk_append, walk_append, wh_append, wh_append, endpt_append, hp, C'.closed]
  have hr : wh (walk C'.base (rev p)) V = (wh (walk y p) V)⁻¹ := by
    have h := wh_rev y p V
    rwa [hp] at h
  rw [hr]
  set P := wh (walk y p) V
  set Q := wh (walk C'.base C'.steps) V
  have : ((P * Q * P⁻¹ : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (P : Matrix (Fin 2) (Fin 2) ℂ) * (Q : Matrix (Fin 2) (Fin 2) ℂ)
        * star (P : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [this, Matrix.trace_mul_cycle]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp P.2).1
  rw [hu, Matrix.one_mul]

/-- The trivial loop has Wilson loop `2`. -/
theorem wl_nil (y : TT i T) (V : SpT i T → SUN.SU 2) :
    (⟨y, [], rfl⟩ : Loop i T).wl V = 2 := by
  simp [Loop.wl, Loop.hol, walk, wh]

end Loops


/-! ## 3. Shells of a monotone family -/

section Shells

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shells of a family of subspaces. -/
def shellOf (Hs : ℕ → Submodule ℝ E) : ℕ → Submodule ℝ E
  | 0 => Hs 0
  | k + 1 => Hs (k + 1) ⊓ (Hs k)ᗮ

/-- Each shell lies in its subspace. -/
theorem shellOf_le (Hs : ℕ → Submodule ℝ E) : ∀ k, shellOf Hs k ≤ Hs k
  | 0 => le_rfl
  | _ + 1 => inf_le_left

/-- **The shells of a monotone family are mutually orthogonal.** -/
theorem shellOf_orth (Hs : ℕ → Submodule ℝ E) (hmono : Monotone Hs) :
    ∀ k l, k ≠ l → ∀ x ∈ shellOf Hs k, ∀ y ∈ shellOf Hs l, inner ℝ x y = 0 := by
  have key : ∀ k l, k < l → ∀ x ∈ shellOf Hs k, ∀ y ∈ shellOf Hs l, inner ℝ x y = 0 := by
    intro k l hkl x hx y hy
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have hy' : y ∈ (Hs l')ᗮ := (show shellOf Hs (l' + 1) ≤ _ from inf_le_right) hy
    have hx' : x ∈ Hs l' := hmono (by omega : k ≤ l') (shellOf_le Hs k hx)
    exact (Submodule.mem_orthogonal _ _).1 hy' x hx'
  intro k l hkl x hx y hy
  rcases lt_or_gt_of_ne hkl with h | h
  · exact key k l h x hx y hy
  · rw [real_inner_comm]; exact key l k h y hy x hx

/-- **Each subspace of a monotone family of complete subspaces lies in the span of the shells**
(`H_{k+1} = H_k ⊕ (H_k⊥ ⊓ H_{k+1})`). -/
theorem le_iSup_shellOf (Hs : ℕ → Submodule ℝ E) (hmono : Monotone Hs)
    (hproj : ∀ k, (Hs k).HasOrthogonalProjection) :
    ∀ k, Hs k ≤ ⨆ j, shellOf Hs j
  | 0 => le_iSup (shellOf Hs) 0
  | k + 1 => by
      haveI := hproj k
      rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hmono (Nat.le_succ k))]
      refine sup_le (le_iSup_shellOf Hs hmono hproj k) ?_
      have : (Hs k)ᗮ ⊓ Hs (k + 1) = shellOf Hs (k + 1) := inf_comm _ _
      rw [this]
      exact le_iSup (shellOf Hs) (k + 1)

end Shells

/-! ## 4. Loop states -/

section States

open MassGap.RectWilson (SpT TT)

variable {i : Fin 4} {T : Dir i → ℕ} {μ : Measure (SpT i T → SUN.SU 2)}

/-- The expectation of `W_C` in the state `Ω`: `∫ W_C Ω²`. -/
def vev (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) (C : Loop i T) : ℝ :=
  ∫ V, C.wl V * Ω V ^ 2 ∂μ

/-- **The loop state** `ψ_C = (W_C − ⟨W_C⟩) Ω`. -/
def loopState (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) (C : Loop i T) :
    (SpT i T → SUN.SU 2) → ℝ :=
  fun V => (C.wl V - vev μ Ω C) * Ω V

/-- `∫ Ω² = 1` makes `Ω²` integrable. -/
theorem integrable_sq_of_norm {Ω : (SpT i T → SUN.SU 2) → ℝ} (h1 : ∫ V, Ω V ^ 2 ∂μ = 1) :
    Integrable (fun V => Ω V ^ 2) μ :=
  Integrable.of_integral_ne_zero (by rw [h1]; norm_num)

/-- `W_C Ω²` is integrable (`|W_C| ≤ 2`). -/
theorem integrable_wl_sq {Ω : (SpT i T → SUN.SU 2) → ℝ} (h1 : ∫ V, Ω V ^ 2 ∂μ = 1) (C : Loop i T) :
    Integrable (fun V => C.wl V * Ω V ^ 2) μ := by
  have hi := integrable_sq_of_norm h1
  refine Integrable.mono' (hi.const_mul 2)
    ((continuous_wl C).aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun V => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Ω V))]
  exact mul_le_mul_of_nonneg_right (abs_wl_le C V) (sq_nonneg _)

/-- **Every loop state is orthogonal to the vacuum.** -/
theorem loopState_orth {Ω : (SpT i T → SUN.SU 2) → ℝ} (h1 : ∫ V, Ω V ^ 2 ∂μ = 1) (C : Loop i T) :
    ∫ V, Ω V * loopState μ Ω C V ∂μ = 0 := by
  have he : (fun V => Ω V * loopState μ Ω C V)
      = fun V => C.wl V * Ω V ^ 2 - vev μ Ω C * Ω V ^ 2 := by
    funext V; unfold loopState; ring
  rw [he, integral_sub (integrable_wl_sq h1 C) ((integrable_sq_of_norm h1).const_mul _),
    integral_const_mul, h1, mul_one]
  unfold vev
  ring

/-- A loop state of a bounded measurable `Ω` is in `L²`. -/
theorem memLp_loopState [IsFiniteMeasure μ] {Ω : (SpT i T → SUN.SU 2) → ℝ} (hm : Measurable Ω) {B : ℝ}
    (hB : ∀ V, |Ω V| ≤ B) (C : Loop i T) : MemLp (loopState μ Ω C) 2 μ := by
  refine MemLp.of_bound (((continuous_wl C).measurable.sub_const _).mul hm).aestronglyMeasurable
    ((2 + |vev μ Ω C|) * B) (Filter.Eventually.of_forall fun V => ?_)
  rw [Real.norm_eq_abs]
  unfold loopState
  rw [abs_mul]
  refine mul_le_mul ((abs_sub _ _).trans (add_le_add (abs_wl_le C V) le_rfl)) (hB V)
    (abs_nonneg _) (by positivity)

/-- **The loop states of physical size at most `R`**, as `L²` vectors: the classes of `ψ_C`
with `a · len C ≤ R`. -/
def loopSet (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) (a R : ℝ) :
    Set (Lp ℝ 2 μ) :=
  {g | ∃ C : Loop i T, a * (C.len : ℝ) ≤ R ∧ (g : (SpT i T → SUN.SU 2) → ℝ) =ᵐ[μ] loopState μ Ω C}

/-- **`H_R`**: the span of the loop states of size at most `R`. -/
def H (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) (a R : ℝ) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (loopSet μ Ω a R)

/-- `H_R` grows with `R`. -/
theorem H_mono (Ω : (SpT i T → SUN.SU 2) → ℝ) (a : ℝ) {R R' : ℝ} (h : R ≤ R') :
    H μ Ω a R ≤ H μ Ω a R' :=
  Submodule.span_mono fun _ ⟨C, hC, he⟩ => ⟨C, hC.trans h, he⟩

/-- **The loop shells**: `S₀ = H_{R₀}`, `S_{k+1} = H_{R_{k+1}} ⊖ H_{R_k}`. -/
def shell (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) (a : ℝ) (R : ℕ → ℝ) :
    ℕ → Submodule ℝ (Lp ℝ 2 μ) :=
  shellOf fun k => H μ Ω a (R k)

end States



/-! ## 5. The loop shells are finite-dimensional, and generate what the loops generate -/

section Generation

open MassGap.RectWilson (SpT TT)

variable {i : Fin 4} {T : Dir i → ℕ} {μ : Measure (SpT i T → SUN.SU 2)}

/-- Finitely many loops have perimeter at most `N`. -/
theorem finite_loops (N : ℕ) : {C : Loop i T | C.len ≤ N}.Finite := by
  have hfin : ((Set.univ : Set (TT i T)) ×ˢ {l : List (Step i) | l.length ≤ N}).Finite :=
    Set.finite_univ.prod (List.finite_length_le _ _)
  refine (hfin.preimage (f := fun C : Loop i T => (C.base, C.steps)) ?_).subset ?_
  · intro C _ C' _ h
    cases C; cases C'
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro C hC
    exact ⟨Set.mem_univ _, hC⟩

/-- **Finitely many loop states have size at most `R`** (at lattice spacing `a > 0`). -/
theorem finite_loopSet (Ω : (SpT i T → SUN.SU 2) → ℝ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (loopSet μ Ω a R).Finite := by
  have hF := finite_loops (i := i) (T := T) ⌊R / a⌋₊
  refine (hF.biUnion fun C _ => (?_ : ({g : Lp ℝ 2 μ |
      (g : (SpT i T → SUN.SU 2) → ℝ) =ᵐ[μ] loopState μ Ω C}).Finite)).subset ?_
  · refine Set.Subsingleton.finite fun g hg g' hg' => Lp.ext ?_
    exact (Set.mem_setOf_eq ▸ hg).trans (Set.mem_setOf_eq ▸ hg').symm
  · rintro g ⟨C, hC, he⟩
    refine Set.mem_biUnion (x := C) ?_ he
    show C.len ≤ ⌊R / a⌋₊
    refine Nat.le_floor ?_
    rw [le_div_iff₀ ha]
    linarith

/-- `H_R` is finite-dimensional, so it has an orthogonal projection. -/
theorem hasOrthogonalProjection_H (Ω : (SpT i T → SUN.SU 2) → ℝ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (H μ Ω a R).HasOrthogonalProjection := by
  haveI : FiniteDimensional ℝ (H μ Ω a R) :=
    FiniteDimensional.span_of_finite ℝ (finite_loopSet Ω ha R)
  haveI : CompleteSpace (H μ Ω a R) := FiniteDimensional.complete ℝ _
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- All loop states, as `L²` vectors. -/
def allLoops (μ : Measure (SpT i T → SUN.SU 2)) (Ω : (SpT i T → SUN.SU 2) → ℝ) : Set (Lp ℝ 2 μ) :=
  {g | ∃ C : Loop i T, (g : (SpT i T → SUN.SU 2) → ℝ) =ᵐ[μ] loopState μ Ω C}

/-- The loop shells are mutually orthogonal. -/
theorem shell_orth (Ω : (SpT i T → SUN.SU 2) → ℝ) (a : ℝ) {R : ℕ → ℝ} (hR : Monotone R) :
    ∀ k l, k ≠ l → ∀ x ∈ shell μ Ω a R k, ∀ y ∈ shell μ Ω a R l, inner ℝ x y = 0 :=
  shellOf_orth _ fun _ _ h => H_mono Ω a (hR h)

/-- **The loops' span lies in the span of the shells**, for radii `R_k` that are monotone and
reach every perimeter. -/
theorem span_allLoops_le (Ω : (SpT i T → SUN.SU 2) → ℝ) {a : ℝ} (ha : 0 < a) {R : ℕ → ℝ}
    (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, a * (N : ℝ) ≤ R k) :
    Submodule.span ℝ (allLoops μ Ω) ≤ ⨆ k, shell μ Ω a R k := by
  rw [Submodule.span_le]
  rintro g ⟨C, he⟩
  obtain ⟨k, hk⟩ := hreach C.len
  have hg : g ∈ H μ Ω a (R k) := Submodule.subset_span ⟨C, hk, he⟩
  exact le_iSup_shellOf (fun k => H μ Ω a (R k)) (fun _ _ h => H_mono Ω a (hR h))
    (fun k => hasOrthogonalProjection_H Ω ha (R k)) k hg

end Generation

/-! ## 6. The gap on the real slice -/

section Slice

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap)
open MassGap.SlabKernelOperator (kernelCLM coeFn_kernelCLM kernelFun)

/-- A measurable `φ` with `∫ φ² = 1` is in `L²`. -/
theorem memLp_of_norm {X : Type*} [MeasurableSpace X] {ν : Measure X} {φ : X → ℝ}
    (hm : Measurable φ) (h1 : ∫ x, φ x * φ x ∂ν = 1) : MemLp φ 2 ν := by
  have hi : Integrable (fun x => φ x * φ x) ν := Integrable.of_integral_ne_zero (by rw [h1]; norm_num)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  simpa [sq] using hi

/-- A normalised measurable function as an `L²` vector. -/
def vecOf {X : Type*} [MeasurableSpace X] {ν : Measure X} {φ : X → ℝ} (hm : Measurable φ)
    (h1 : ∫ x, φ x * φ x ∂ν = 1) : Lp ℝ 2 ν :=
  (memLp_of_norm hm h1).toLp φ

/-- `‖φ‖ = 1` in `L²`. -/
theorem norm_vecOf {X : Type*} [MeasurableSpace X] {ν : Measure X} {φ : X → ℝ} (hm : Measurable φ)
    (h1 : ∫ x, φ x * φ x ∂ν = 1) : ‖vecOf hm h1‖ = 1 := by
  have h := KernelPower.norm_sq_eq_integral (vecOf hm h1)
  have : ∫ x, ((vecOf hm h1 : Lp ℝ 2 ν) : X → ℝ) x ^ 2 ∂ν = 1 := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_norm hm h1).coeFn_toLp] with x hx
    unfold vecOf; rw [hx, sq]
  rw [this] at h
  nlinarith [norm_nonneg (vecOf hm h1), sq_nonneg (‖vecOf hm h1‖ - 1)]

/-- The `L²` inner product of two such vectors is `∫ φ ψ`. -/
theorem inner_vecOf {X : Type*} [MeasurableSpace X] {ν : Measure X} {φ ψ : X → ℝ}
    (hm : Measurable φ) (h1 : ∫ x, φ x * φ x ∂ν = 1) (hm' : Measurable ψ) (h1' : ∫ x, ψ x * ψ x ∂ν = 1) :
    inner ℝ (vecOf hm h1) (vecOf hm' h1') = ∫ x, φ x * ψ x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_norm hm h1).coeFn_toLp, (memLp_of_norm hm' h1').coeFn_toLp] with x hx hx'
  unfold vecOf; rw [hx, hx']; simp [mul_comm]

/-- The operator of `trivKN` acts on the level `φ_j` by `μ_j`. -/
theorem trivKN_vecOf {β : ℝ} {n : ℕ} {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C) (j : ι) :
    kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (vecOf (hm j) (hL.norm j))
      = μv j • vecOf (hm j) (hL.norm j) := by
  apply Lp.ext
  filter_upwards [coeFn_kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i)
      (vecOf (hm j) (hL.norm j)), Lp.coeFn_smul (μv j) (vecOf (hm j) (hL.norm j)),
      (memLp_of_norm (hm j) (hL.norm j)).coeFn_toLp] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  change kernelFun (trivKN 2 β n i) (hSN 2 n i)
      (((memLp_of_norm (hm j) (hL.norm j)).toLp (φ j) : Lp ℝ 2 (hSN 2 n i)) : Slice n i → ℝ) z
    = μv j * (((memLp_of_norm (hm j) (hL.norm j)).toLp (φ j) : Lp ℝ 2 (hSN 2 n i)) :
        Slice n i → ℝ) z
  rw [h3, KernelPower.kernelFun_congr (memLp_of_norm (hm j) (hL.norm j)).coeFn_toLp z]
  exact hL.eigen j z

/-- **A relative bound on the excited levels is the gap clause.** -/
theorem zeroFluxGap_of_levelBound {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C) {m : ℝ}
    (h : ∀ j, j ≠ g₀ →
      ‖kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) (vecOf (hm j) (hL.norm j))‖
        ≤ |μv g₀| * Real.exp (-(m * ((n : ℝ) * aRun 2 β)) / 2) * ‖vecOf (hm j) (hL.norm j)‖) :
    ZeroFluxGap g₀ E m := by
  intro j hj
  set t := (n : ℝ) * aRun 2 β with ht
  have htpos : 0 < t := mul_pos (by exact_mod_cast hn) (aRun_pos (by norm_num) hβ)
  have hb := h j hj
  rw [trivKN_vecOf hL hm hkm hC0 hkb j, norm_smul, norm_vecOf, mul_one, mul_one,
    Real.norm_eq_abs] at hb
  have hsq : μv j ^ 2 ≤ μv g₀ ^ 2 * Real.exp (-(m * t)) := by
    have := pow_le_pow_left₀ (abs_nonneg _) hb 2
    have he : Real.exp (-(m * t) / 2) ^ 2 = Real.exp (-(m * t)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [sq_abs, mul_pow, sq_abs, he] at this
    exact this
  rw [hL.energy j, hL.energy g₀, ← Real.exp_add, Real.exp_le_exp] at hsq
  have : (E g₀ + m) * t ≤ E j * t := by linarith
  exact le_of_mul_le_mul_right this htpos

/-- **The relative bound on `Ω⊥` gives the gap clause.** -/
theorem zeroFluxGap_of_orthBound {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C) {m : ℝ}
    (h : OrthBound (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i))
      (vecOf (hm g₀) (hL.norm g₀)) (|μv g₀| * Real.exp (-(m * ((n : ℝ) * aRun 2 β)) / 2))) :
    ZeroFluxGap g₀ E m :=
  zeroFluxGap_of_levelBound hβ hn hL hm hkm hC0 hkb fun j hj =>
    h _ (by rw [inner_vecOf]; exact hL.orth g₀ j (Ne.symm hj))

/-- **The electric reduction.** On the zero-flux slice, with `Ω = φ_{g₀}`: (E1) every excited level
is in the closure of the span of the loop states, and (E2') the transfer blocks between the loop
shells of radii `R_k` (monotone, reaching every perimeter) have symmetric bounds with row sums at
most `μ_{g₀}² e^{−m t}`; then `ZeroFluxGap g₀ E m`. -/
theorem zeroFluxGap_of_loopShells {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    (b : ℕ → ℕ → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k l, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ∀ y ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R l,
      |inner ℝ (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x)
        (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) y)| ≤ b k l * (‖x‖ * ‖y‖))
    {m : ℝ} (hrow : ∀ k (s : Finset ℕ), ∑ l ∈ s, b k l
      ≤ (|μv g₀| * Real.exp (-(m * ((n : ℝ) * aRun 2 β)) / 2)) ^ 2) :
    ZeroFluxGap g₀ E m := by
  have ha : 0 < aRun 2 β := aRun_pos (by norm_num) hβ
  refine zeroFluxGap_of_levelBound hβ hn hL hm hkm hC0 hkb fun j hj => ?_
  exact bound_on_shells (shell (hSN 2 n i) (φ g₀) (aRun 2 β) R) (shell_orth _ _ hR) b hb0 hsym
    hblk (by positivity) hrow _ (closure_mono (span_allLoops_le (φ g₀) ha hR hreach) (hgen j hj))

end Slice


/-! ## 7. A state in one flux sector: the transfer is bounded by that sector's trace -/

section Sector

open MassGap.KernelPower MassGap.FluxSectorFourier

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] {act : G → X → X} {a : X → X → ℝ}

/-- The sector kernel of a real-valued character, as a real kernel. -/
def rsec (a : X → X → ℝ) (act : G → X → X) (ψ : AddChar G ℂ) (x y : X) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, (ψ g).re * a x (act g y)

omit [MeasurableSpace X] [IsProbabilityMeasure μ] in
/-- For a real-valued character the complex sector kernel is the real one. -/
theorem sec_eq_rsec {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (x y : X) :
    sec a act ψ x y = (rsec a act ψ x y : ℂ) := by
  unfold sec rsec
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  exact Complex.ext (by simp) (by simp [hψ g])

omit [IsProbabilityMeasure μ] in
/-- For a real-valued character the sector trace is `hs` of the real sector kernel. -/
theorem sectorTrace_eq_hs {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) :
    sectorTrace μ a act ψ = hs μ (rsec a act ψ) := by
  unfold sectorTrace secDiag hs
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [sec_eq_rsec hψ, Complex.norm_real, Real.norm_eq_abs, sq_abs]

omit [MeasurableSpace X] [IsProbabilityMeasure μ] in
/-- A real-valued character takes the values `±1`. -/
theorem re_mul_self {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (g : G) :
    (ψ g).re * (ψ g).re = 1 := by
  have h : ‖ψ g‖ = 1 := AddChar.norm_apply ψ g
  have h2 : ‖ψ g‖ ^ 2 = (ψ g).re * (ψ g).re + (ψ g).im * (ψ g).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [h, hψ g] at h2
  linarith

/-- Moving the second argument along the action multiplies by the character. -/
theorem integral_act_sector {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (hA : CentreAction μ act)
    {f : X → ℝ} (hf : ∀ g y, f (act g y) = (ψ g).re * f y) (x : X) (g : G) :
    ∫ y, a x (act g y) * f y ∂μ = (ψ g).re * ∫ y, a x y * f y ∂μ := by
  classical
  have h1 : (fun y => a x (act g y) * f y)
      = fun y => (ψ g).re * (a x (act g y) * f (act g y)) := by
    funext y
    rw [hf g y]
    calc a x (act g y) * f y = ((ψ g).re * (ψ g).re) * (a x (act g y) * f y) := by
          rw [re_mul_self hψ g, one_mul]
      _ = _ := by ring
  rw [h1, integral_const_mul]
  congr 1
  exact hA.integral_comp g (fun z => a x z * f z)

/-- **On a state of the sector `ψ` the kernel acts as its sector kernel.** -/
theorem integral_rsec {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (hA : CentreAction μ act)
    (ha : Bdd a) {f : X → ℝ} (hfm : Measurable f) {B : ℝ} (hfb : ∀ y, |f y| ≤ B)
    (hf : ∀ g y, f (act g y) = (ψ g).re * f y) (x : X) :
    ∫ y, rsec a act ψ x y * f y ∂μ = ∫ y, a x y * f y ∂μ := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  have hint : ∀ g, Integrable (fun y => a x (act g y) * f y) μ := fun g =>
    integrable_of_bdd (((ha.row x).comp (hA.meas g)).mul hfm) (C := Ca * B) fun y => by
      rw [abs_mul]
      exact mul_le_mul (hCa x _) (hfb y) (abs_nonneg _) ((abs_nonneg _).trans (hCa x y))
  have he : (fun y => rsec a act ψ x y * f y)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, (ψ g).re * (a x (act g y) * f y) := by
    funext y
    unfold rsec
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [he, integral_const_mul, integral_finsetSum _ (fun g _ => (hint g).const_mul _)]
  simp_rw [integral_const_mul, integral_act_sector hψ hA hf x]
  have hs : ∑ g : G, (ψ g).re * ((ψ g).re * ∫ y, a x y * f y ∂μ)
      = (Fintype.card G : ℝ) * ∫ y, a x y * f y ∂μ := by
    simp_rw [← mul_assoc, re_mul_self hψ, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hs, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

omit [IsProbabilityMeasure μ] in
/-- The real sector kernel is bounded and measurable. -/
theorem bdd_rsec {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (hA : CentreAction μ act) (ha : Bdd a) :
    Bdd (rsec a act ψ) := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  refine ⟨?_, |Ca|, fun x y => ?_⟩
  · show Measurable fun p : X × X => rsec a act ψ p.1 p.2
    unfold rsec
    refine measurable_const.mul (Finset.measurable_sum _ fun g _ => measurable_const.mul ?_)
    exact ha.meas.comp (measurable_fst.prodMk ((hA.meas g).comp measurable_snd))
  · unfold rsec
    have hre : ∀ g, |(ψ g).re| = 1 := fun g => by
      have := re_mul_self hψ g
      nlinarith [abs_mul_abs_self (ψ g).re, abs_nonneg (ψ g).re]
    have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    rw [abs_mul, abs_inv, abs_of_pos hcard]
    have hsum : |∑ g, (ψ g).re * a x (act g y)| ≤ (Fintype.card G : ℝ) * |Ca| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ g ∈ (Finset.univ : Finset G), |(ψ g).re * a x (act g y)| ≤ |Ca| := fun g _ => by
        rw [abs_mul, hre g, one_mul]; exact (hCa x _).trans (le_abs_self _)
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (Fintype.card G : ℝ)⁻¹ * |∑ g, (ψ g).re * a x (act g y)|
        ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * |Ca|) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hcard.le)
      _ = |Ca| := by rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- **A state in the sector `ψ` sees only that sector's trace**:
`‖a f‖² ≤ c_ψ ‖f‖²`, `c_ψ = sectorTrace ψ`. -/
theorem sector_bound {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (hA : CentreAction μ act)
    (ha : Bdd a) {f : X → ℝ} (hfm : Measurable f) {B : ℝ} (hfb : ∀ y, |f y| ≤ B)
    (hf : ∀ g y, f (act g y) = (ψ g).re * f y) :
    ∫ x, (∫ y, a x y * f y ∂μ) ^ 2 ∂μ ≤ sectorTrace μ a act ψ * ∫ y, f y ^ 2 ∂μ := by
  have hr := bdd_rsec hψ hA ha (μ := μ)
  obtain ⟨Cr, hCr⟩ := hr.bdd
  rw [sectorTrace_eq_hs hψ]
  simp_rw [← integral_rsec hψ hA ha hfm hfb hf]
  have hf2 : Integrable (fun y => f y ^ 2) μ :=
    integrable_of_bdd (hfm.pow_const 2) (C := B ^ 2) fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfb y) 2
  have hpt : ∀ x, (∫ y, rsec a act ψ x y * f y ∂μ) ^ 2
      ≤ (∫ y, rsec a act ψ x y ^ 2 ∂μ) * ∫ y, f y ^ 2 ∂μ := fun x =>
    sq_integral_mul_le
      (integrable_of_bdd ((hr.row x).pow_const 2) (C := Cr ^ 2) fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCr x y) 2)
      hf2
      (integrable_of_bdd ((hr.row x).mul hfm) (C := Cr * B) fun y => by
        rw [abs_mul]
        exact mul_le_mul (hCr x y) (hfb y) (abs_nonneg _) ((abs_nonneg _).trans (hCr x y)))
  rw [hs, ← integral_mul_const]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
    (Filter.Eventually.of_forall hpt)
  exact (integrable_of_bdd (measurable_integral_right (hr.meas.pow_const 2)) (C := Cr ^ 2)
    (fun x => abs_integral_le fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCr x y) 2)).mul_const _

/-- **The zero-flux kernel annihilates a state of a nontrivial sector.** -/
theorem zk_sector_eq_zero {ψ : AddChar G ℂ} (hψ : ∀ g, (ψ g).im = 0) (hψ1 : ψ ≠ 1)
    (hA : CentreAction μ act) (ha : Bdd a) {f : X → ℝ} (hfm : Measurable f) {B : ℝ}
    (hfb : ∀ y, |f y| ≤ B) (hf : ∀ g y, f (act g y) = (ψ g).re * f y) (x : X) :
    ∫ y, ZeroFluxSector.zk a act x y * f y ∂μ = 0 := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  have hint : ∀ g, Integrable (fun y => a x (act g y) * f y) μ := fun g =>
    integrable_of_bdd (((ha.row x).comp (hA.meas g)).mul hfm) (C := Ca * B) fun y => by
      rw [abs_mul]
      exact mul_le_mul (hCa x _) (hfb y) (abs_nonneg _) ((abs_nonneg _).trans (hCa x y))
  have he : (fun y => ZeroFluxSector.zk a act x y * f y)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, a x (act g y) * f y := by
    funext y
    unfold ZeroFluxSector.zk
    rw [mul_assoc, Finset.sum_mul]
  rw [he, integral_const_mul, integral_finsetSum _ (fun g _ => hint g)]
  simp_rw [integral_act_sector hψ hA hf x]
  rw [← Finset.sum_mul]
  have h0 : ∑ g : G, (ψ g).re = 0 := by
    rw [← Complex.re_sum, AddChar.sum_eq_zero_of_ne_one hψ1, Complex.zero_re]
  rw [h0, zero_mul, mul_zero]

end Sector

/-! ## 8. Winding loops: odd electric flux, and what (V) gives for them -/

section Winding

open MassGap.RectWilson (SpT TT tsh)
open MassGap.SliceCentreAction (Cen act lc centreAction)
open MassGap.TwistedTraceBoundN (cz coe_cz cz_add cz_zero)
open MassGap.CentreSectorSeedN (halfKN hSN bdd_halfKN hs_halfKN_pos)
open MassGap.CentreSectorSeed (Tr)
open MassGap.TensionFloor (Slice)
open MassGap.VortexAperture (oddFlux oddTrace elecRatio one_sub_zR_eq_oddFlux char_two_torsion)
open MassGap.AsymptoticScaling (aRun)
open MassGap.KernelPower (hs)

variable {i : Fin 4} {T : Dir i → ℕ}

/-- Centre elements commute with `SU(2)`. -/
theorem cz_comm (k : ZMod 2) (U : SUN.SU 2) : cz k * U = U * cz k := by
  apply Subtype.ext
  show ((cz k : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)
    = (U : Matrix (Fin 2) (Fin 2) ℂ) * ((cz k : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
  rw [coe_cz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **A forward word under the centre action** picks up the centre element of its total charge. -/
theorem wh_act_fwd (g : Cen i 2) (V : SpT i T → SUN.SU 2) :
    ∀ w : List (SpT i T × Bool), (∀ lo ∈ w, lo.2 = true) →
      wh w (act g V) = cz ((w.map fun lo => lc g lo.1).sum) * wh w V
  | [], _ => by simp [wh, cz_zero]
  | lo :: w, hw => by
      have h1 : lo.2 = true := hw lo List.mem_cons_self
      have ih := wh_act_fwd g V w (fun l hl => hw l (List.mem_cons_of_mem _ hl))
      have e1 : wh (lo :: w) (act g V) = act g V lo.1 * wh w (act g V) := by
        simp [wh, h1]
      have e2 : wh (lo :: w) V = V lo.1 * wh w V := by simp [wh, h1]
      rw [e1, e2, ih, List.map_cons, List.sum_cons, cz_add]
      show cz (lc g lo.1) * V lo.1 * (cz _ * wh w V) = _
      calc cz (lc g lo.1) * V lo.1 * (cz ((w.map fun lo => lc g lo.1).sum) * wh w V)
          = cz (lc g lo.1) * (V lo.1 * cz ((w.map fun lo => lc g lo.1).sum)) * wh w V := by
            simp only [mul_assoc]
        _ = cz (lc g lo.1) * (cz ((w.map fun lo => lc g lo.1).sum) * V lo.1) * wh w V := by
            rw [← cz_comm _ (V lo.1)]
        _ = _ := by simp only [mul_assoc]

/-- One rotation adds `1` modulo `n`. -/
theorem finRotate_val (n : ℕ) (x : Fin n) : (finRotate n x).val = (x.val + 1) % n := by
  rcases n with _ | m
  · exact x.elim0
  · by_cases h : x = Fin.last m
    · subst h
      rw [finRotate_last]
      simp
    · rw [coe_finRotate_of_ne_last h]
      have := Fin.val_lt_last h
      rw [Nat.mod_eq_of_lt (by omega)]

/-- `j` rotations add `j` modulo `n`. -/
theorem iterate_finRotate_val (n : ℕ) (x : Fin n) (j : ℕ) :
    ((finRotate n)^[j] x).val = (x.val + j) % n := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ j ih => rw [Function.iterate_succ_apply', finRotate_val, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Steps in direction `ν` move the `ν` coordinate. -/
theorem iterate_tsh_self (ν : Dir i) (y : TT i T) (j : ℕ) :
    ((tsh i T ν)^[j] y) ν = (finRotate (T ν))^[j] (y ν) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      simp [tsh]

/-- Steps in direction `ν` fix the other coordinates. -/
theorem iterate_tsh_ne (ν ν' : Dir i) (h : ν' ≠ ν) (y : TT i T) (j : ℕ) :
    ((tsh i T ν)^[j] y) ν' = y ν' := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ← ih]
      simp [tsh, Function.update_of_ne h]

/-- `T_ν` steps in direction `ν` return to the start. -/
theorem iterate_tsh_period (ν : Dir i) (y : TT i T) : (tsh i T ν)^[T ν] y = y := by
  funext ν'
  by_cases h : ν' = ν
  · subst h
    rw [iterate_tsh_self]
    apply Fin.ext
    rw [iterate_finRotate_val, Nat.add_mod_right, Nat.mod_eq_of_lt (y ν').isLt]
  · exact iterate_tsh_ne ν ν' h y _

/-- The end point of `k` forward steps in direction `ν`. -/
theorem endpt_line (ν : Dir i) : ∀ (k : ℕ) (y : TT i T),
    endpt y (List.replicate k (ν, true)) = (tsh i T ν)^[k] y
  | 0, _ => rfl
  | k + 1, y => by
      rw [List.replicate_succ]
      simp only [endpt, next, if_true]
      rw [endpt_line ν k, Function.iterate_succ_apply]

/-- A straight forward path crosses its links forward. -/
theorem walk_line_fwd (ν : Dir i) : ∀ (k : ℕ) (y : TT i T),
    ∀ lo ∈ walk y (List.replicate k (ν, true)), lo.2 = true
  | 0, _ => by simp [walk]
  | k + 1, y => by
      rw [List.replicate_succ]
      intro lo hlo
      simp only [walk, letter, next, if_true, List.mem_cons] at hlo
      rcases hlo with rfl | hlo
      · rfl
      · exact walk_line_fwd ν k _ lo hlo

/-- The centre charge of a straight path: the charges of the links it crosses. -/
theorem charge_line (g : Cen i 2) (ν : Dir i) : ∀ (k : ℕ) (y : TT i T),
    ((walk y (List.replicate k (ν, true))).map fun lo => lc g lo.1).sum
      = ∑ j ∈ Finset.range k, lc g (ν, (tsh i T ν)^[j] y)
  | 0, _ => by simp [walk]
  | k + 1, y => by
      rw [List.replicate_succ, Finset.sum_range_succ']
      simp only [walk, letter, next, if_true, List.map_cons, List.sum_cons]
      rw [charge_line g ν k, add_comm]
      simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- **The straight winding loop** in direction `ν` through `y`. -/
def windLoop (ν : Dir i) (y : TT i T) : Loop i T :=
  ⟨y, List.replicate (T ν) (ν, true), by rw [endpt_line, iterate_tsh_period]⟩

/-- **The winding loop through the hyperplane `y_ν = 0` carries charge `g_ν`**: it crosses the
hyperplane once. -/
theorem charge_windLoop (g : Cen i 2) (ν : Dir i) (y : TT i T) (hy : (y ν).val = 0) :
    ((walk y (List.replicate (T ν) (ν, true))).map fun lo => lc g lo.1).sum = g ν := by
  rw [charge_line]
  have hterm : ∀ j ∈ Finset.range (T ν), lc g (ν, (tsh i T ν)^[j] y) = if j = 0 then g ν else 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    unfold lc
    simp only
    rw [iterate_tsh_self, iterate_finRotate_val, hy, zero_add, Nat.mod_eq_of_lt hj']
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.2 (lt_of_le_of_lt (Nat.zero_le _) (y ν).isLt))]

/-- **A winding loop changes sign with its own centre twist**:
`W(act g V) = Re e(g_ν) · W(V)`. -/
theorem wl_windLoop_act (ν : Dir i) (y : TT i T) (hy : (y ν).val = 0) (g : Cen i 2)
    (V : SpT i T → SUN.SU 2) :
    (windLoop ν y).wl (act g V) = (ZMod.stdAddChar (N := 2) (g ν)).re * (windLoop ν y).wl V := by
  unfold Loop.wl Loop.hol windLoop
  simp only
  rw [wh_act_fwd g V _ (walk_line_fwd ν _ y), charge_windLoop g ν y hy]
  set Hm := wh (walk y (List.replicate (T ν) (ν, true))) V
  have hc : ((cz (g ν) * Hm : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = ZMod.stdAddChar (N := 2) (g ν) • (Hm : Matrix (Fin 2) (Fin 2) ℂ) := by
    show ((cz (g ν) : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ) * (Hm : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [coe_cz, Matrix.smul_mul, Matrix.one_mul]
  rw [hc, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, su2_trace_im Hm, mul_zero, sub_zero]

/-- The character of `Z₂³` reading the `ν` component: `g ↦ e(g_ν)`. -/
def chi (ν : Dir i) : AddChar (Cen i 2) ℂ :=
  (ZMod.stdAddChar (N := 2)).compAddMonoidHom (Pi.evalAddMonoidHom (fun _ : Dir i => ZMod 2) ν)

/-- `χ_ν(g) = e(g_ν)`. -/
theorem chi_apply (ν : Dir i) (g : Cen i 2) : chi ν g = ZMod.stdAddChar (N := 2) (g ν) := rfl

/-- `χ_ν` is real. -/
theorem chi_im (ν : Dir i) (g : Cen i 2) : (chi ν g).im = 0 := by
  rw [chi_apply]
  have hg : g ν + g ν = 0 := by
    generalize g ν = x
    revert x; decide
  rcases char_two_torsion (ZMod.stdAddChar (N := 2)) hg with h | h <;> rw [h] <;> simp

/-- `χ_ν` is odd under the twist `e_ν`. -/
theorem chi_single (ν : Dir i) : chi ν (Pi.single ν 1) ≠ 1 := by
  rw [chi_apply, Pi.single_eq_same]
  intro h
  have h0 : ZMod.stdAddChar (N := 2) 1 = ZMod.stdAddChar (N := 2) 0 := by
    rw [h, AddChar.map_zero_eq_one]
  have := ZMod.injective_stdAddChar h0
  exact absurd this (by decide)

/-- **The winding state** `W_ν Ω`. -/
def windState (ν : Dir i) (y : TT i T) (Ω : (SpT i T → SUN.SU 2) → ℝ) :
    (SpT i T → SUN.SU 2) → ℝ :=
  fun V => (windLoop ν y).wl V * Ω V

/-- **The winding state lies in the sector `χ_ν`.** -/
theorem windState_act (ν : Dir i) (y : TT i T) (hy : (y ν).val = 0) {Ω : (SpT i T → SUN.SU 2) → ℝ}
    (hΩ : ∀ g V, Ω (act g V) = Ω V) (g : Cen i 2) (V : SpT i T → SUN.SU 2) :
    windState ν y Ω (act g V) = (chi ν g).re * windState ν y Ω V := by
  unfold windState
  rw [wl_windLoop_act ν y hy, hΩ, chi_apply, mul_assoc]

/-- A sector odd under `e_ν` has trace at most `oddFlux`. -/
theorem sectorTrace_le_oddFlux {β : ℝ} (n : ℕ) (i : Fin 4) (ν : Dir i)
    {ψ : AddChar (Cen i 2) ℂ} (hψ : ψ (Pi.single ν 1) ≠ 1) :
    FluxSectorFourier.sectorTrace (hSN 2 n i) (halfKN 2 β n i)
      (act (μ := i) (T := Tr n i) (N := 2)) ψ ≤ oddFlux β n i ν := by
  classical
  unfold oddFlux oddTrace
  refine Finset.single_le_sum (f := fun ψ => FluxSectorFourier.sectorTrace (hSN 2 n i)
    (halfKN 2 β n i) (act (μ := i) (T := Tr n i) (N := 2)) ψ)
    (fun ψ _ => FluxSectorFourier.sectorTrace_nonneg ψ) ?_
  simp [hψ]

/-- **The transfer of a winding state is bounded by the odd electric-flux trace**:
`‖halfKN f‖² ≤ oddFlux · ‖f‖²` for `f = W_ν Ω`, `Ω` centre-invariant and bounded. -/
theorem winding_transfer_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (ν : Dir i)
    (y : TT i (Tr n i)) (hy : (y ν).val = 0) {Ω : Slice n i → ℝ} (hΩm : Measurable Ω) {B : ℝ}
    (hΩb : ∀ V, |Ω V| ≤ B) (hΩc : ∀ g V, Ω (act g V) = Ω V) :
    ∫ x, (∫ V, halfKN 2 β n i x V * windState ν y Ω V ∂(hSN 2 n i)) ^ 2 ∂(hSN 2 n i)
      ≤ oddFlux β n i ν * ∫ V, windState ν y Ω V ^ 2 ∂(hSN 2 n i) := by
  have hfm : Measurable (windState ν y Ω) := (continuous_wl _).measurable.mul hΩm
  have hfb : ∀ V, |windState ν y Ω V| ≤ 2 * B := fun V => by
    unfold windState; rw [abs_mul]
    exact mul_le_mul (abs_wl_le _ V) (hΩb V) (abs_nonneg _) (by norm_num)
  have h := sector_bound (chi_im ν) centreAction (bdd_halfKN (N := 2) hβ n i) hfm hfb
    (windState_act ν y hy hΩc)
  exact h.trans (mul_le_mul_of_nonneg_right (sectorTrace_le_oddFlux n i ν (chi_single ν))
    (integral_nonneg fun _ => sq_nonneg _))

/-- **A winding state has no zero-flux component**: `trivKN` annihilates it. -/
theorem trivKN_windState {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (ν : Dir i)
    (y : TT i (Tr n i)) (hy : (y ν).val = 0) {Ω : Slice n i → ℝ} (hΩm : Measurable Ω) {B : ℝ}
    (hΩb : ∀ V, |Ω V| ≤ B) (hΩc : ∀ g V, Ω (act g V) = Ω V) (x : Slice n i) :
    ∫ V, CentreSectorSeedN.trivKN 2 β n i x V * windState ν y Ω V ∂(hSN 2 n i) = 0 := by
  have hfm : Measurable (windState ν y Ω) := (continuous_wl _).measurable.mul hΩm
  have hfb : ∀ V, |windState ν y Ω V| ≤ 2 * B := fun V => by
    unfold windState; rw [abs_mul]
    exact mul_le_mul (abs_wl_le _ V) (hΩb V) (abs_nonneg _) (by norm_num)
  have hne : chi ν ≠ 1 := fun h => chi_single ν (by rw [h, AddChar.one_apply])
  exact zk_sector_eq_zero (chi_im ν) hne centreAction (bdd_halfKN (N := 2) hβ n i) hfm hfb
    (windState_act ν y hy hΩc) x

/-- **The odd trace is at most `elecRatio` times the full trace.** -/
theorem oddFlux_le_elecRatio {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : Dir i) : oddFlux β n i ν ≤ elecRatio β n i ν * hs (hSN 2 n i) (halfKN 2 β n i) := by
  have h := one_sub_zR_eq_oddFlux hβ hn he i ν
  have hH : 0 < hs (hSN 2 n i) (halfKN 2 β n i) := hs_halfKN_pos (N := 2) hβ n i
  have hz := GapSideVortexRect.zR_pos (GapSideVortexRect.Lc n i) i ν.1 β
  have hO : 0 ≤ oddFlux β n i ν := by
    classical
    unfold oddFlux oddTrace
    exact Finset.sum_nonneg fun ψ _ => FluxSectorFourier.sectorTrace_nonneg ψ
  set z := GapSideVortexRect.zR (GapSideVortexRect.Lc n i) i ν.1 β
  set Hh := hs (hSN 2 n i) (halfKN 2 β n i)
  set O := oddFlux β n i ν
  have h2O : 2 * O = (1 - z) * Hh := by rw [h, div_mul_cancel₀ _ hH.ne']
  have hHO : 0 < Hh - O := by nlinarith [mul_pos hz hH]
  unfold elecRatio
  change O ≤ O / (Hh - O) * Hh
  have hq : 0 ≤ O / (Hh - O) := div_nonneg hO hHO.le
  calc O = O / (Hh - O) * (Hh - O) := by rw [div_mul_cancel₀ _ hHO.ne']
    _ ≤ O / (Hh - O) * Hh := mul_le_mul_of_nonneg_left (by linarith) hq

/-- **What (V) gives for a winding loop.** If the electric-flux ratio of the plane `(i, ν)` is at
most `A e^{−σ n a}`, the transfer of the winding state is bounded by `A e^{−σ n a}` times the full
trace: `‖halfKN f‖² ≤ A e^{−σ n a} · hs(halfKN) · ‖f‖²`. -/
theorem winding_cost_of_elec {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : Dir i) (y : TT i (Tr n i)) (hy : (y ν).val = 0) {Ω : Slice n i → ℝ} (hΩm : Measurable Ω)
    {B : ℝ} (hΩb : ∀ V, |Ω V| ≤ B) (hΩc : ∀ g V, Ω (act g V) = Ω V) {σ A : ℝ}
    (hE : elecRatio β n i ν ≤ A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β)))) :
    ∫ x, (∫ V, halfKN 2 β n i x V * windState ν y Ω V ∂(hSN 2 n i)) ^ 2 ∂(hSN 2 n i)
      ≤ A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) * hs (hSN 2 n i) (halfKN 2 β n i)
        * ∫ V, windState ν y Ω V ^ 2 ∂(hSN 2 n i) := by
  have hH : 0 ≤ hs (hSN 2 n i) (halfKN 2 β n i) := (hs_halfKN_pos (N := 2) hβ n i).le
  have hf2 : 0 ≤ ∫ V, windState ν y Ω V ^ 2 ∂(hSN 2 n i) := integral_nonneg fun _ => sq_nonneg _
  refine (winding_transfer_le hβ n i ν y hy hΩm hΩb hΩc).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hf2
  exact (oddFlux_le_elecRatio hβ hn he i ν).trans (mul_le_mul_of_nonneg_right hE hH)

/-- **(V) gives the winding-loop cost on its window.** -/
theorem windingCost_of_vortexCostAt {σ A ℓ : ℝ} (hV : FluxCost.VortexCostAt σ A ℓ) :
    ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ →
      ∀ (i : Fin 4) (ν : Dir i) (y : TT i (Tr n i)), (y ν).val = 0 →
      ∀ (Ω : Slice n i → ℝ), Measurable Ω → ∀ B : ℝ, (∀ V, |Ω V| ≤ B) →
      (∀ g V, Ω (act g V) = Ω V) →
      ∫ x, (∫ V, halfKN 2 β n i x V * windState ν y Ω V ∂(hSN 2 n i)) ^ 2 ∂(hSN 2 n i)
        ≤ A * Real.exp (-(σ * ((n : ℝ) * aRun 2 β))) * hs (hSN 2 n i) (halfKN 2 β n i)
          * ∫ V, windState ν y Ω V ^ 2 ∂(hSN 2 n i) := by
  filter_upwards [VortexAperture.elecCostAt_of_vortexCostAt hV, eventually_ge_atTop (0 : ℝ)]
    with β hE hβ0 n hp h2 hlo hup i ν y hy Ω hΩm B hΩb hΩc
  exact winding_cost_of_elec hβ0 h2 (FluxCost.even_of_pow2 hp h2) i ν y hy hΩm hΩb hΩc
    (hE n hp h2 hlo hup i ν)

end Winding


/-! ## 9. Gauge invariance of the Wilson loops -/

section Gauge

open MassGap.RectWilson (SpT TT tsh)

variable {i : Fin 4} {T : Dir i → ℕ}

/-- **A gauge transformation** of a slice configuration: `V(ν, y) ↦ h(y) V(ν, y) h(y + ν)⁻¹`. -/
def gauge (h : TT i T → SUN.SU 2) (V : SpT i T → SUN.SU 2) : SpT i T → SUN.SU 2 :=
  fun l => h l.2 * V l * (h (tsh i T l.1 l.2))⁻¹

/-- One letter under a gauge transformation. -/
theorem wh_letter_gauge (h : TT i T → SUN.SU 2) (V : SpT i T → SUN.SU 2) (y : TT i T) (a : Step i) :
    wh [letter y a] (gauge h V) = h y * wh [letter y a] V * (h (next y a))⁻¹ := by
  rcases a with ⟨ν, b⟩
  cases b
  · simp only [wh, letter, next, gauge, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, tsh_tshInv]
    group
  · simp only [wh, letter, next, gauge, if_true, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]

/-- **A path's holonomy under a gauge transformation**: `h(start) · hol · h(end)⁻¹`. -/
theorem wh_walk_gauge (h : TT i T → SUN.SU 2) (V : SpT i T → SUN.SU 2) :
    ∀ (s : List (Step i)) (y : TT i T),
      wh (walk y s) (gauge h V) = h y * wh (walk y s) V * (h (endpt y s))⁻¹
  | [], y => by simp [wh, walk, endpt]
  | a :: ss, y => by
      rw [show walk y (a :: ss) = [letter y a] ++ walk (next y a) ss from rfl, wh_append, wh_append,
        wh_letter_gauge, wh_walk_gauge h V ss (next y a)]
      simp only [endpt]
      group

/-- **The Wilson loop is gauge invariant.** -/
theorem Loop.wl_gauge (C : Loop i T) (h : TT i T → SUN.SU 2) (V : SpT i T → SUN.SU 2) :
    C.wl (gauge h V) = C.wl V := by
  unfold Loop.wl Loop.hol
  rw [wh_walk_gauge, C.closed]
  set P := h C.base
  set Q := wh (walk C.base C.steps) V
  have : ((P * Q * P⁻¹ : SUN.SU 2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (P : Matrix (Fin 2) (Fin 2) ℂ) * (Q : Matrix (Fin 2) (Fin 2) ℂ)
        * star (P : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [this, Matrix.trace_mul_cycle]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp P.2).1
  rw [hu, Matrix.one_mul]

end Gauge


/-! ## 10. The electric cost on the loop shells -/

section Cost

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap)
open MassGap.SlabKernelOperator (kernelCLM)

/-- **Row sums from a diagonal cost and an off-diagonal coupling.** -/
theorem rowSum_le {b : ℕ → ℕ → ℝ} (hb0 : ∀ k l, 0 ≤ b k l) {D η : ℝ} (hdiag : ∀ k, b k k ≤ D)
    (hoff : ∀ k (s : Finset ℕ), ∑ l ∈ s.erase k, b k l ≤ η) (k : ℕ) (s : Finset ℕ) :
    ∑ l ∈ s, b k l ≤ D + η := by
  by_cases hk : k ∈ s
  · rw [← Finset.add_sum_erase s _ hk]
    exact add_le_add (hdiag k) (hoff k s)
  · rw [← Finset.erase_eq_of_notMem hk]
    have := hoff k s
    have hD : 0 ≤ D := (hb0 k k).trans (hdiag k)
    linarith

/-- **The electric cost gives the gap.** On the loop shells of radii `R_k > 0`: if (E1) the excited
levels are generated by loop states, the diagonal block of shell `k` costs the tension and the
localisation at its own radius, `b_kk ≤ μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`, and the off-diagonal
row sums are at most `μ_{g₀}² η`, then `ZeroFluxGap g₀ E m` with
`e^{−m t} = e^{−2√(c c' σ) t} + η`. -/
theorem zeroFluxGap_of_electricCost {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) {i : Fin 4}
    {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → Slice n i → ℝ} {μv : ι → ℝ}
    (hL : EigenLevels β n i g₀ E φ μv) (hm : ∀ j, Measurable (φ j))
    {C : ℝ} (hkm : Measurable (Function.uncurry (trivKN 2 β n i))) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |trivKN 2 β n i x y| ≤ C)
    {R : ℕ → ℝ} (hR : Monotone R) (hR0 : ∀ k, 0 < R k)
    (hreach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k)
    (hgen : ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoops (hSN 2 n i) (φ g₀)) : Set (Lp ℝ 2 (hSN 2 n i))))
    (b : ℕ → ℕ → ℝ) (hb0 : ∀ k l, 0 ≤ b k l) (hsym : ∀ k l, b k l = b l k)
    (hblk : ∀ k l, ∀ x ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k,
      ∀ y ∈ shell (hSN 2 n i) (φ g₀) (aRun 2 β) R l,
      |inner ℝ (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) x)
        (kernelCLM (trivKN 2 β n i) C hkm hC0 hkb (hSN 2 n i) (hSN 2 n i) y)| ≤ b k l * (‖x‖ * ‖y‖))
    {c c' σ η : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hη : 0 ≤ η)
    (hdiag : ∀ k, b k k ≤ μv g₀ ^ 2 *
      Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))))
    (hoff : ∀ k (s : Finset ℕ), ∑ l ∈ s.erase k, b k l ≤ μv g₀ ^ 2 * η) :
    ZeroFluxGap g₀ E (-Real.log (Real.exp (-(2 * Real.sqrt (c * c' * σ) * ((n : ℝ) * aRun 2 β))) + η)
      / ((n : ℝ) * aRun 2 β)) := by
  set t := (n : ℝ) * aRun 2 β with ht
  have htpos : 0 < t := mul_pos (by exact_mod_cast hn) (aRun_pos (by norm_num) hβ)
  set X := Real.exp (-(2 * Real.sqrt (c * c' * σ) * t)) + η
  have hX : 0 < X := by positivity
  refine zeroFluxGap_of_loopShells hβ hn hL hm hkm hC0 hkb hR hreach hgen b hb0 hsym hblk ?_
  intro k s
  have hd : ∀ k, b k k ≤ μv g₀ ^ 2 * Real.exp (-(2 * Real.sqrt (c * c' * σ) * t)) := fun k =>
    (hdiag k).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg
      (mul_le_mul_of_nonneg_right (AttractCost.two_sqrt_le_cost hc hc' hσ (hR0 k)) htpos.le)))
      (sq_nonneg _))
  refine (rowSum_le hb0 hd hoff k s).trans (le_of_eq ?_)
  have hm' : -(-Real.log X / t * t) / 2 = Real.log X / 2 := by field_simp
  rw [mul_pow, sq_abs, hm', ← Real.exp_nat_mul]
  rw [show ((2 : ℕ) : ℝ) * (Real.log X / 2) = Real.log X by push_cast; ring, Real.exp_log hX]
  ring

end Cost


end MassGap.ElectricLoops

#print axioms MassGap.ElectricLoops.isClosed_bound
#print axioms MassGap.ElectricLoops.orthBound_of_closure
#print axioms MassGap.ElectricLoops.orthBound_of_span
#print axioms MassGap.ElectricLoops.span_orth
#print axioms MassGap.ElectricLoops.spanBound_iff
#print axioms MassGap.ElectricLoops.schur_finset
#print axioms MassGap.ElectricLoops.bound_on_shells
#print axioms MassGap.ElectricLoops.orthBound_of_shells
#print axioms MassGap.ElectricLoops.exists_shells_iff
#print axioms MassGap.ElectricLoops.diagonal_not_span
#print axioms MassGap.ElectricLoops.tshInv_tsh
#print axioms MassGap.ElectricLoops.tsh_tshInv
#print axioms MassGap.ElectricLoops.walk_append
#print axioms MassGap.ElectricLoops.endpt_append
#print axioms MassGap.ElectricLoops.rev_cons
#print axioms MassGap.ElectricLoops.next_flip
#print axioms MassGap.ElectricLoops.endpt_rev
#print axioms MassGap.ElectricLoops.wh_append
#print axioms MassGap.ElectricLoops.wh_letter_flip
#print axioms MassGap.ElectricLoops.wh_rev
#print axioms MassGap.ElectricLoops.continuous_wh
#print axioms MassGap.ElectricLoops.Loop.hol_inv
#print axioms MassGap.ElectricLoops.Loop.hol_comp
#print axioms MassGap.ElectricLoops.continuous_wl
#print axioms MassGap.ElectricLoops.abs_wl_le
#print axioms MassGap.ElectricLoops.su2_star_eq_adj
#print axioms MassGap.ElectricLoops.add_adj_fin_two
#print axioms MassGap.ElectricLoops.su2_trace_im
#print axioms MassGap.ElectricLoops.su2_mandelstam
#print axioms MassGap.ElectricLoops.Loop.wl_mul
#print axioms MassGap.ElectricLoops.Loop.wl_conj
#print axioms MassGap.ElectricLoops.wl_nil
#print axioms MassGap.ElectricLoops.shellOf_le
#print axioms MassGap.ElectricLoops.shellOf_orth
#print axioms MassGap.ElectricLoops.le_iSup_shellOf
#print axioms MassGap.ElectricLoops.integrable_sq_of_norm
#print axioms MassGap.ElectricLoops.integrable_wl_sq
#print axioms MassGap.ElectricLoops.loopState_orth
#print axioms MassGap.ElectricLoops.memLp_loopState
#print axioms MassGap.ElectricLoops.H_mono
#print axioms MassGap.ElectricLoops.finite_loops
#print axioms MassGap.ElectricLoops.finite_loopSet
#print axioms MassGap.ElectricLoops.hasOrthogonalProjection_H
#print axioms MassGap.ElectricLoops.shell_orth
#print axioms MassGap.ElectricLoops.span_allLoops_le
#print axioms MassGap.ElectricLoops.memLp_of_norm
#print axioms MassGap.ElectricLoops.norm_vecOf
#print axioms MassGap.ElectricLoops.inner_vecOf
#print axioms MassGap.ElectricLoops.trivKN_vecOf
#print axioms MassGap.ElectricLoops.zeroFluxGap_of_levelBound
#print axioms MassGap.ElectricLoops.zeroFluxGap_of_orthBound
#print axioms MassGap.ElectricLoops.zeroFluxGap_of_loopShells
#print axioms MassGap.ElectricLoops.sec_eq_rsec
#print axioms MassGap.ElectricLoops.sectorTrace_eq_hs
#print axioms MassGap.ElectricLoops.re_mul_self
#print axioms MassGap.ElectricLoops.integral_act_sector
#print axioms MassGap.ElectricLoops.integral_rsec
#print axioms MassGap.ElectricLoops.bdd_rsec
#print axioms MassGap.ElectricLoops.sector_bound
#print axioms MassGap.ElectricLoops.zk_sector_eq_zero
#print axioms MassGap.ElectricLoops.cz_comm
#print axioms MassGap.ElectricLoops.wh_act_fwd
#print axioms MassGap.ElectricLoops.finRotate_val
#print axioms MassGap.ElectricLoops.iterate_finRotate_val
#print axioms MassGap.ElectricLoops.iterate_tsh_self
#print axioms MassGap.ElectricLoops.iterate_tsh_ne
#print axioms MassGap.ElectricLoops.iterate_tsh_period
#print axioms MassGap.ElectricLoops.endpt_line
#print axioms MassGap.ElectricLoops.walk_line_fwd
#print axioms MassGap.ElectricLoops.charge_line
#print axioms MassGap.ElectricLoops.charge_windLoop
#print axioms MassGap.ElectricLoops.wl_windLoop_act
#print axioms MassGap.ElectricLoops.chi_apply
#print axioms MassGap.ElectricLoops.chi_im
#print axioms MassGap.ElectricLoops.chi_single
#print axioms MassGap.ElectricLoops.windState_act
#print axioms MassGap.ElectricLoops.sectorTrace_le_oddFlux
#print axioms MassGap.ElectricLoops.winding_transfer_le
#print axioms MassGap.ElectricLoops.trivKN_windState
#print axioms MassGap.ElectricLoops.oddFlux_le_elecRatio
#print axioms MassGap.ElectricLoops.winding_cost_of_elec
#print axioms MassGap.ElectricLoops.windingCost_of_vortexCostAt
#print axioms MassGap.ElectricLoops.wh_letter_gauge
#print axioms MassGap.ElectricLoops.wh_walk_gauge
#print axioms MassGap.ElectricLoops.Loop.wl_gauge
#print axioms MassGap.ElectricLoops.rowSum_le
#print axioms MassGap.ElectricLoops.zeroFluxGap_of_electricCost
