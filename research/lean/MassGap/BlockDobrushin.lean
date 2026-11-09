import Mathlib
import MassGap.CoarseBoundary
import MassGap.BoxFocusTest

noncomputable section

/-!
# MassGap.BlockDobrushin — the block-scale Dobrushin step and what it asks of one scale

`BoxFocusTest.KernelNear Δ X δ` asks that the box kernel `γ_Δ X` lie within `δ ≈ e^{−m t}` of one constant at
every boundary condition, for a box of physical radius `~ t`, uniformly in `β`. This module groups the
configuration into blocks of a fixed physical size `b` and proves the Dobrushin iteration on the block system in
the abstract, then the two directions that tie the block condition to `KernelNear` at the block scale itself.

## 1. The Dobrushin iteration (proved, abstract)

Blocks `ι` (a finite type), block configurations `∀ b, Y b`, and oscillation vectors read through
`CoarseBoundary.BlockOsc` (changing block `b` alone moves `g` by at most `v b`).
* `DobCond C α`: the block influence matrix `C` has nonnegative entries and row sums `Σ_j C i j ≤ α`.
* `step C v i = Σ_j C i j v j`; `step_le`, `iter_nonneg`, `iter_le`: `(step C)^[n] v ≤ αⁿ V` when `v ≤ V`.
* `DobInfl K C`: the operator `K` on block functions sends every per-block oscillation vector `v ≥ 0` to at most
  `step C v`. This is the Dobrushin influence inequality, stated for the operator (for the Wilson system `K` is
  the kernel of one shell of blocks; the identification is argued, §3 items 2–3).
* `blockOsc_iter`: `K^[n] g` has per-block oscillation `(step C)^[n] v`.
* `exists_near_of_blockOsc`: a per-block oscillation vector `ε` puts `g` within `Σ_b ε b` of one constant.
* `dobrushin_near_const`: `DobInfl K C`, `DobCond C α`, `0 ≤ v ≤ V` give
  `∃ c, ∀ y, |K^[n] g y − c| ≤ |ι| αⁿ V`. `pow_le_exp`: `α ≤ e^{−κ}` gives `αⁿ ≤ e^{−κ n}`.
  With `n = t / b` shells and `κ = −log α` (`α > 0`), the bound is `|ι| V e^{−(κ/b) t}`: a mass `κ/b` in physical units,
  and the prefactor is the number of blocks, a physical count.

## 2. The two directions at the block scale (proved, with the entry reading argued)

* `kernelNear_of_blockFactor`: if the Wilson box kernel factors as `γ_Δ X = g ∘ e` through any block map `e` and
  `g` has per-block oscillations summing to at most `δ`, then `KernelNear Δ X δ`.
* `blockOsc_of_near`: conversely a function within `δ` of one constant has per-block oscillation at most `2 δ` at
  every block; `rowSum_le_of_near`: with the influence of block `i` confined to the blocks `s i` and each entry
  read off a function within `δ` of a constant, the row sum is at most `2 |s i| δ`.
So, granted that each entry `C i j` is the per-block oscillation of a function within `δ` of a constant
(argued, §3 item 2), the Dobrushin condition at the block scale and the
`KernelNear` form at the block scale imply each other up to the fixed factor `2 |s i|` (the neighbour-block
count, `3⁴ − 1 = 80` for cubic blocks in four dimensions; the count is argued, not formalised).

## 3. Evaluation (argued)

1. **The surface count is physical.** At the block level the count is the number of blocks, `(t/b)^{d−1}` on
   the boundary and `(t/b)^d` in `dobrushin_near_const`, independent of `a_k`. The block step removes the
   `|∂Δ|`-in-lattice-units prefactor of the standard bound.
2. **The block condition is `KernelNear` at the one scale `b`.** The entry `C i j` is the oscillation, over the
   configurations of block `j`, of the one-shell kernel applied to a test of block `i`; its row sum `< 1` is a
   uniform boundary-influence bound on a box of physical size `~ b`, the same form as `KernelNear`, with the
   tolerance `α < 1` (a contraction) instead of `e^{−m t}` (a decay). Section 2 proves the two arithmetic
   directions; with the entry reading above they are equivalent up to the neighbour count. So the block route reduces the gap to one fixed-physical-scale statement — the author's "one
   scale fixes all" in precise form: `KernelNear` at one physical size `b`, with tolerance below
   `1/(2 · 80)` of the test oscillation, over the whole class of block tests, uniformly in `β`, gives
   `KernelNear` at every physical size `t` with `δ ≤ |ι| e^{−(κ/b) t}` through `dobrushin_near_const`.
   It does not remove the problem; it moves it to one scale, and it asks there for every test of a block, not
   one loop `X`.
3. **The class of tests is where `β` enters.** Read on all bounded tests of a block (total variation), the
   row sum tends to the neighbour count as `β → ∞` at fixed `b`: the conditional law of a block concentrates on
   the configurations fixed by the boundary, so two boundary conditions give nearly disjoint laws. A uniform
   `α < 1` is possible only on a restricted class (gauge-invariant, coarse, or Lipschitz in a block metric),
   and `DobInfl` then needs `K` to keep that class, which the one-shell Wilson kernel does not do for the
   fine-link class (`CoarseBoundary` item 1: a boundary condition is a point configuration and is not
   integrated). This is the same object `CoarseBoundary` names: the effective density of the exact decimation
   at the scale `a_{k₀}`, per block, uniform in `k`. The archived `DSBlockContract`, `CoarseDS` and `DSBoxFloor`
   carry the Dobrushin–Shlosman box criterion `DSBoxInfluence` at box side
   `⌈1/(κ aRun β)⌉₊` through to the Clay statement on the same reduction; their Gaussian unit has the box average
   of the summed influence equal to the mean escape probability of the killed walk, `1` when massless, so the
   criterion at scale `b` holds only when the scale-`b` system already has a mass `m` with `m b ≳ 6`.
4. **`RunSeed` does not supply it.** `WDeltaRun.RunSeed 2` is three clauses at one physical size
   (`RunSeedLink.runSeed_iff_vortex`: vortex free energies and the zero-flux defect). They are free-energy ratios of
   twisted to untwisted partition functions — integrated quantities, the same for every boundary condition —
   and they carry no sup over boundary conditions; the block condition is a sup over the configurations of a
   neighbouring block. A bound from the vortex free energies to the block influence would be a new step (none in
   the tree).

DERIVED (module-wide): `0` the signs; `1` the unit of the iterate; `2` the two sides of a constant.
-/

namespace MassGap.BlockDobrushin

open MassGap.CoarseBoundary (BlockOsc abs_sub_le_sum)

/-! ## 1. The Dobrushin iteration -/

section Iteration

variable {ι : Type*} [Fintype ι]

/-- One application of the block influence matrix to an oscillation vector. -/
def step (C : ι → ι → ℝ) (v : ι → ℝ) : ι → ℝ := fun i => ∑ j, C i j * v j

/-- **Dobrushin's condition** on the block influence matrix: nonnegative entries, row sums at most `α`. -/
def DobCond (C : ι → ι → ℝ) (α : ℝ) : Prop := (∀ i j, 0 ≤ C i j) ∧ ∀ i, ∑ j, C i j ≤ α

theorem step_nonneg {C : ι → ι → ℝ} {v : ι → ℝ} (hC : ∀ i j, 0 ≤ C i j) (hv : ∀ j, 0 ≤ v j) (i : ι) :
    0 ≤ step C v i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hC i j) (hv j)

theorem step_le {C : ι → ι → ℝ} {α V : ℝ} {v : ι → ℝ} (hD : DobCond C α) (hV : ∀ j, v j ≤ V)
    (hV0 : 0 ≤ V) (i : ι) : step C v i ≤ α * V :=
  calc step C v i = ∑ j, C i j * v j := rfl
    _ ≤ ∑ j, C i j * V := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hV j) (hD.1 i j)
    _ = (∑ j, C i j) * V := by rw [Finset.sum_mul]
    _ ≤ α * V := mul_le_mul_of_nonneg_right (hD.2 i) hV0

theorem iter_nonneg {C : ι → ι → ℝ} {v : ι → ℝ} (hC : ∀ i j, 0 ≤ C i j) (hv : ∀ j, 0 ≤ v j) :
    ∀ n i, 0 ≤ (step C)^[n] v i := by
  intro n
  induction n with
  | zero => exact hv
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply']
    exact step_nonneg hC ih i

/-- **`n` shells contract by `αⁿ`.** -/
theorem iter_le {C : ι → ι → ℝ} {α V : ℝ} {v : ι → ℝ} (hD : DobCond C α) (hα : 0 ≤ α) (hV0 : 0 ≤ V)
    (hV : ∀ j, v j ≤ V) : ∀ n i, (step C)^[n] v i ≤ α ^ n * V := by
  intro n
  induction n with
  | zero => intro i; simpa using hV i
  | succ n ih =>
    intro i
    rw [Function.iterate_succ_apply']
    calc step C ((step C)^[n] v) i ≤ α * (α ^ n * V) :=
          step_le hD ih (mul_nonneg (pow_nonneg hα n) hV0) i
      _ = α ^ (n + 1) * V := by ring

variable {Y : ι → Type*}

/-- **The Dobrushin influence inequality** for an operator on block functions: every per-block oscillation
vector `v ≥ 0` of `g` is sent to the per-block oscillation vector `step C v` of `K g`. -/
def DobInfl (K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)) (C : ι → ι → ℝ) : Prop :=
  ∀ (g : (∀ b, Y b) → ℝ) (v : ι → ℝ), (∀ j, 0 ≤ v j) → BlockOsc g v → BlockOsc (K g) (step C v)

theorem blockOsc_iter {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ} (hK : DobInfl K C)
    (hC : ∀ i j, 0 ≤ C i j) {g : (∀ b, Y b) → ℝ} {v : ι → ℝ} (hv : ∀ j, 0 ≤ v j) (hg : BlockOsc g v) :
    ∀ n, BlockOsc (K^[n] g) ((step C)^[n] v) := by
  intro n
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hK _ _ (iter_nonneg hC hv n) ih

variable [DecidableEq ι]

/-- **Per-block oscillations put `g` near one constant.** -/
theorem exists_near_of_blockOsc {g : (∀ b, Y b) → ℝ} {ε : ι → ℝ} (hg : BlockOsc g ε) :
    ∃ c : ℝ, ∀ y, |g y - c| ≤ ∑ b, ε b := by
  rcases isEmpty_or_nonempty (∀ b, Y b) with h | ⟨⟨y₀⟩⟩
  · exact ⟨0, fun y => (h.false y).elim⟩
  · exact ⟨g y₀, fun y => abs_sub_le_sum hg y y₀⟩

/-- **The block Dobrushin step.** Row sums at most `α` and an initial per-block oscillation at most `V` put
`n` shells of the kernel within `|ι| αⁿ V` of one constant at every block configuration. -/
theorem dobrushin_near_const {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ} {α V : ℝ}
    (hK : DobInfl K C) (hD : DobCond C α) (hα : 0 ≤ α) (hV0 : 0 ≤ V) {g : (∀ b, Y b) → ℝ}
    {v : ι → ℝ} (hv : ∀ j, 0 ≤ v j) (hV : ∀ j, v j ≤ V) (hg : BlockOsc g v) (n : ℕ) :
    ∃ c : ℝ, ∀ y, |K^[n] g y - c| ≤ Fintype.card ι * (α ^ n * V) := by
  obtain ⟨c, hc⟩ := exists_near_of_blockOsc (blockOsc_iter hK hD.1 hv hg n)
  refine ⟨c, fun y => (hc y).trans ?_⟩
  calc ∑ b, (step C)^[n] v b ≤ ∑ _b : ι, α ^ n * V :=
        Finset.sum_le_sum fun b _ => iter_le hD hα hV0 hV n b
    _ = Fintype.card ι * (α ^ n * V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Iteration

/-- **A contraction factor is an exponential in the shell count.** -/
theorem pow_le_exp {α κ : ℝ} (hα : 0 ≤ α) (h : α ≤ Real.exp (-κ)) (n : ℕ) :
    α ^ n ≤ Real.exp (-(κ * n)) := by
  calc α ^ n ≤ Real.exp (-κ) ^ n := pow_le_pow_left₀ hα h n
    _ = Real.exp (-(κ * n)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-! ## 2. The two directions at the block scale -/

section Converse

variable {ι : Type*} {Y : ι → Type*}

/-- **Near a constant gives a per-block oscillation `2 δ`** at every block. -/
theorem blockOsc_of_near {g : (∀ b, Y b) → ℝ} {c δ : ℝ} (h : ∀ y, |g y - c| ≤ δ) :
    BlockOsc g (fun _ => 2 * δ) := by
  intro b y y' _
  have h2 : |c - g y'| ≤ δ := by rw [abs_sub_comm]; exact h y'
  calc |g y - g y'| ≤ |g y - c| + |c - g y'| := abs_sub_le _ _ _
    _ ≤ 2 * δ := by linarith [h y]

/-- **The row sum from the block-scale near-constant form.** If the influence of block `i` is confined to the
blocks `s i` (`C i j = 0` off `s i`) and every entry is at most `2 δ` (the per-block oscillation of a function
within `δ` of a constant, `blockOsc_of_near`), the row sum is at most `2 |s i| δ`. -/
theorem rowSum_le_of_near [Fintype ι] (C : ι → ι → ℝ) (s : ι → Finset ι) {δ : ℝ}
    (hoff : ∀ i j, j ∉ s i → C i j = 0) (hent : ∀ i j, C i j ≤ 2 * δ) (i : ι) :
    ∑ j, C i j ≤ (s i).card * (2 * δ) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (s i)) (fun j _ hj => hoff i j hj)]
  calc ∑ j ∈ s i, C i j ≤ ∑ _j ∈ s i, 2 * δ := Finset.sum_le_sum fun j _ => hent i j
    _ = (s i).card * (2 * δ) := by rw [Finset.sum_const, nsmul_eq_mul]

end Converse

section Wilson

open MassGap.GibbsSpec MassGap.SUN MassGap.PeriodicStateDLR

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}

/-- **`KernelNear` from a block factorisation.** If the Wilson box kernel factors through a block map `e` as
`γ_Δ X = g ∘ e` and `g` has per-block oscillations summing to at most `δ`, then `KernelNear Δ X δ`. -/
theorem kernelNear_of_blockFactor (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SU N), ℝ))
    (e : IConf (SU N) → ∀ b, Y b) (g : (∀ b, Y b) → ℝ)
    (hfac : ∀ ω, wspec hN β Δ X ω = g (e ω)) {ε : ι → ℝ} (hg : BlockOsc g ε) {δ : ℝ}
    (hδ : ∑ b, ε b ≤ δ) : BoxFocusTest.KernelNear hN β Δ X δ := by
  obtain ⟨c, hc⟩ := exists_near_of_blockOsc hg
  exact ⟨c, fun ω => by rw [hfac]; exact (hc _).trans hδ⟩

/-- **`KernelNear` from the block Dobrushin step.** The box kernel equals `n` shells of a block operator with
Dobrushin influence `C` and row sums at most `α`, applied to a block function of per-block oscillation at most
`V`: then `KernelNear Δ X (|ι| αⁿ V)`. -/
theorem kernelNear_of_dobrushin (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SU N), ℝ))
    (e : IConf (SU N) → ∀ b, Y b) {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ}
    {α V : ℝ} (hK : DobInfl K C) (hD : DobCond C α) (hα : 0 ≤ α) (hV0 : 0 ≤ V)
    {g : (∀ b, Y b) → ℝ} {v : ι → ℝ} (hv : ∀ j, 0 ≤ v j) (hV : ∀ j, v j ≤ V) (hg : BlockOsc g v)
    (n : ℕ) (hfac : ∀ ω, wspec hN β Δ X ω = K^[n] g (e ω)) :
    BoxFocusTest.KernelNear hN β Δ X (Fintype.card ι * (α ^ n * V)) := by
  obtain ⟨c, hc⟩ := dobrushin_near_const hK hD hα hV0 hv hV hg n
  exact ⟨c, fun ω => by rw [hfac]; exact hc _⟩

end Wilson

end MassGap.BlockDobrushin

#print axioms MassGap.BlockDobrushin.iter_le
#print axioms MassGap.BlockDobrushin.blockOsc_iter
#print axioms MassGap.BlockDobrushin.exists_near_of_blockOsc
#print axioms MassGap.BlockDobrushin.dobrushin_near_const
#print axioms MassGap.BlockDobrushin.pow_le_exp
#print axioms MassGap.BlockDobrushin.blockOsc_of_near
#print axioms MassGap.BlockDobrushin.rowSum_le_of_near
#print axioms MassGap.BlockDobrushin.kernelNear_of_blockFactor
#print axioms MassGap.BlockDobrushin.kernelNear_of_dobrushin
