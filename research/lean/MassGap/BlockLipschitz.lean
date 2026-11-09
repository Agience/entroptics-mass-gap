import Mathlib
import MassGap.BlockDobrushin

noncomputable section

/-!
# MassGap.BlockLipschitz — the Lipschitz (Kantorovich) block contraction and the photon filter

`BlockDobrushin` reduces `KernelNear` at every physical size to a block contraction at one physical size `b`,
on a class of block tests the one-shell kernel keeps. Read on all bounded tests (total variation) the row sum
tends to the neighbour count as `β → ∞`. This module takes the class of tests that are Lipschitz in a metric on
each block's configuration (for SU(2): the bi-invariant metric on the block's gauge-invariant data), proves the
Dobrushin iteration on that class, proves the coupling bound that controls the entries, and proves the
obstruction any candidate contraction must meet: a kernel that commutes with a shift moving a test by a fixed
amount admits no contraction.

## 1. The Lipschitz Dobrushin iteration (proved, abstract)

* `BlockLip g L`: changing block `b` alone from `y b` to `y' b` moves `g` by at most `L b · dist (y b) (y' b)`.
* `blockOsc_of_blockLip`: with every block of diameter at most `D`, `BlockLip g L` gives `BlockOsc g (L · D)`.
* `LipInfl K C`: `K` sends every Lipschitz vector `L ≥ 0` of `g` to the Lipschitz vector `step C L` of `K g`
  (the Lipschitz-Dobrushin influence inequality, stated for the operator).
* `blockLip_iter`: `K^[n] g` has Lipschitz vector `(step C)^[n] L`.
* `lip_near_const`: `LipInfl K C`, `DobCond C α`, `0 ≤ L ≤ V`, diameter `≤ D` give
  `∃ c, ∀ y, |K^[n] g y − c| ≤ |ι| αⁿ V D`.
* `kernelNear_of_lip`: the same bound for the Wilson box kernel when it equals `n` shells of `K` read through a
  block map, i.e. `KernelNear Δ X (|ι| αⁿ V D)`.

## 2. The coupling bound (proved, abstract)

* `abs_integral_sub_le_coupling`: for `μ`, `ν` the two marginals of a measure `π` on `X × X` and `f` with
  `|f x − f x'| ≤ ℓ · dist x x'`, `|∫ f dμ − ∫ f dν| ≤ ℓ · ∫ dist dπ`. This is the direction of
  Kantorovich duality the contraction uses: an entry `C i j` is bounded by `κ` once, for every pair of boundary
  conditions differing on block `j` alone, the two conditional laws of block `i` admit a coupling with mean
  distance at most `κ` times the distance of the two boundary conditions on block `j`.

## 3. The photon filter (proved, abstract)

* `iterate_shift`: if `K` commutes with a map `τ` of configurations, adds constants through, and `g ∘ τ = g + c`,
  then `K^[n] g ∘ τ = K^[n] g + c` for every `n`. With `c ≠ 0` it is incompatible with bounded block diameter
  (a bounded Lipschitz `g` forces `c = 0`); it serves non-compact blocks.
* `not_contract_of_shift`: a Lipschitz test `g` whose iterates keep a gap `c > 0` between `τ y₀` and `y₀`
  (`c ≤ |K^[n] g (τ y₀) − K^[n] g y₀|` for all `n`) is incompatible with `LipInfl K C`, `DobCond C α`, `α < 1`.

## 4. Evaluation (argued)

1. **Choice of class.** The Lipschitz class is chosen over the centre-projected (`ℤ₂`) class. The centre
   projection does not commute with the one-shell kernel, so `DobInfl` has no class to act on; and it carries
   no photon filter: for U(1) at weak coupling every plaquette is near `1` and every `ℤ₂`-projected test is near
   constant, so a `ℤ₂` contraction would hold vacuously for U(1) and distinguish nothing. Discrete gauge theories
   are gapped in both of their phases, so a `ℤ₂` contraction would not read confinement either.
2. **U(1) fails, through §3.** In the Gaussian (spin-wave) approximation of compact U(1) at large `β`, the field
   equations are linear, and a field `h` with constant field strength `F` (`A_μ(x) = ½ F_{μν} x_ν`) solves them.
   The conditional law of a Gaussian given boundary data `y + h` is the shift by `h` of the law given `y`, so the
   one-shell kernel commutes with `τ = (· + h)`, adds constants through, and the plaquette test `g = F_p` (a
   coordinate of the block's gauge-invariant data, Lipschitz with constant `1` in the max-plaquette metric)
   satisfies `g ∘ τ = g + F`. `iterate_shift` then gives a gap `F` at every shell count. In this
   approximation the blocks are non-compact, so `not_contract_of_shift` (which needs bounded block diameter) does
   not apply directly; a diameter-free form of the bound (not built) excludes `α < 1`. For compact U(1) itself the exact shift is replaced by the
   Coulomb-phase response: a uniform imposed field is not screened (finite dielectric constant), the gap stays
   above a fixed `c > 0` at every `n`, and `not_contract_of_shift` applies as stated. This is consistent with the
   Fröhlich–Spencer / Guth proof of a massless phase of 4D compact U(1) at weak coupling: a Lipschitz contraction
   holding uniformly in `β` for U(1) would prove a false theorem, and §3 shows the class cannot.
3. **What differs for SU(2).** The filter is driven by an exact continuous shift symmetry of the conditional
   laws, which exists because the abelian field equations are linear (superposition of a constant-`F`
   solution). The plaquette action of SU(2) is invariant under multiplying all `μ`-links by a fixed `z` only for
   `z` central (`z ∈ ℤ₂`): `U_p ↦ z U_μ U_ν U_μ'⁻¹ z⁻¹ U_ν'⁻¹` equals `U_p` for every configuration only when `z`
   commutes with every link. The remaining shift group is discrete, so no continuous family `c → 0` of exact
   gaps exists. This does not make SU(2) contract: at a block of fixed lattice size and `β → ∞` the linearised
   SU(2) field is three copies of the U(1) Gaussian, the constant-`F` shift of an abelian subalgebra holds up to
   `O(g²)` per lattice length, and the gap persists over a fixed number of lattice spacings. The defect
   accumulates only over a physical length, where the running coupling `g(b)` is order one.
4. **The hypothesis.** `SU2BlockLipContract b α` (stated in prose, not as a Lean `def`, because the effective
   block kernel at scale `b` is not built in the tree): there are `b` (physical) and `α < 1` such that for every
   `β` large, grouping links into cubic blocks of `b / a(β)` lattice spacings, the one-shell kernel of the
   Wilson measure (or of its exact decimation to scale `b`) satisfies `LipInfl K C` with `DobCond C α` on block
   tests Lipschitz in the max-plaquette bi-invariant metric of the block's gauge-invariant data. By
   `kernelNear_of_lip` it gives `KernelNear` at physical size `t = n b` with `δ = |ι| V D αⁿ = |ι| V D e^{−(κ/b) t}`,
   `κ = −log α`, uniformly in `β`.
5. **It is circular.** By `BlockDobrushin` §2 (`blockOsc_of_near`, `rowSum_le_of_near`) a row sum below `1` at
   scale `b` is `KernelNear` at the one size `b` with tolerance below `1/(2·80)` of the test's Lipschitz
   constant: a finite-size mass statement (Dobrushin–Shlosman / Martinelli–Olivieri form). It is the mass at one
   scale, not a step towards it.
6. **It is the asymptotic-freedom crossover.** The statement it asks for is: *at a physical scale `b` with
   `b Λ ≫ 1` the renormalised effective action of the decimation (Bałaban's effective action at the block
   scale `k₀` with `a_{k₀} = b`) lies in the strong-coupling regime where the single-block influence is below
   `1/80` uniformly in `β`*; equivalently `g(b)² ≥ g_*²`, the threshold at which `StrongKernelNear`'s sequential
   Dobrushin sweep closes, with the non-Wilson remainder of the effective action small in the same norm.
   Bałaban's renormalisation-group bounds control the effective actions while the running coupling is small
   (ultraviolet stability); they do not reach the crossover to `g(b) = O(1)`. That crossover is the open input,
   and `SU2BlockLipContract` is that input in Dobrushin form.

DERIVED (module-wide): `0` the signs; `1` the unit of the iterate and of the strict contraction; `2` the two
sides of a constant.
-/

namespace MassGap.BlockLipschitz

open MassGap.CoarseBoundary (BlockOsc)
open MassGap.BlockDobrushin (step DobCond iter_nonneg iter_le exists_near_of_blockOsc)

/-! ## 1. The Lipschitz Dobrushin iteration -/

section Iteration

variable {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ b, PseudoMetricSpace (Y b)]

/-- **Per-block Lipschitz vector.** Changing block `b` alone moves `g` by at most `L b` times the distance of
the two configurations of block `b`. -/
def BlockLip (g : (∀ b, Y b) → ℝ) (L : ι → ℝ) : Prop :=
  ∀ b (y y' : ∀ b, Y b), (∀ b', b' ≠ b → y b' = y' b') → |g y - g y'| ≤ L b * dist (y b) (y' b)

omit [Fintype ι] in
/-- A Lipschitz vector and a diameter bound give a per-block oscillation vector. -/
theorem blockOsc_of_blockLip {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} {D : ℝ} (hL : ∀ b, 0 ≤ L b)
    (hD : ∀ b (u v : Y b), dist u v ≤ D) (hg : BlockLip g L) : BlockOsc g (fun b => L b * D) :=
  fun b y y' h => (hg b y y' h).trans (mul_le_mul_of_nonneg_left (hD b _ _) (hL b))

/-- **The Lipschitz-Dobrushin influence inequality** for an operator on block functions. -/
def LipInfl (K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)) (C : ι → ι → ℝ) : Prop :=
  ∀ (g : (∀ b, Y b) → ℝ) (L : ι → ℝ), (∀ j, 0 ≤ L j) → BlockLip g L → BlockLip (K g) (step C L)

theorem blockLip_iter {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ} (hK : LipInfl K C)
    (hC : ∀ i j, 0 ≤ C i j) {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} (hL : ∀ j, 0 ≤ L j) (hg : BlockLip g L) :
    ∀ n, BlockLip (K^[n] g) ((step C)^[n] L) := by
  intro n
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; exact hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hK _ _ (iter_nonneg hC hL n) ih

variable [DecidableEq ι]

/-- **The Lipschitz block Dobrushin step.** Row sums at most `α`, an initial Lipschitz vector at most `V` and
block diameters at most `D` put `n` shells of the kernel within `|ι| αⁿ V D` of one constant. -/
theorem lip_near_const {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ} {α V D : ℝ}
    (hK : LipInfl K C) (hDC : DobCond C α) (hα : 0 ≤ α) (hV0 : 0 ≤ V) (hD0 : 0 ≤ D)
    (hDiam : ∀ b (u v : Y b), dist u v ≤ D) {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} (hL : ∀ j, 0 ≤ L j)
    (hLV : ∀ j, L j ≤ V) (hg : BlockLip g L) (n : ℕ) :
    ∃ c : ℝ, ∀ y, |K^[n] g y - c| ≤ Fintype.card ι * (α ^ n * V) * D := by
  have hB := blockOsc_of_blockLip (fun b => iter_nonneg hDC.1 hL n b) hDiam (blockLip_iter hK hDC.1 hL hg n)
  obtain ⟨c, hc⟩ := exists_near_of_blockOsc hB
  refine ⟨c, fun y => (hc y).trans ?_⟩
  calc ∑ b, (step C)^[n] L b * D ≤ ∑ _b : ι, α ^ n * V * D :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (iter_le hDC hα hV0 hLV n b) hD0
    _ = Fintype.card ι * (α ^ n * V) * D := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## 3. The photon filter -/

omit [Fintype ι] [∀ b, PseudoMetricSpace (Y b)] [DecidableEq ι] in
/-- **A shift that commutes with the kernel survives every shell.** -/
theorem iterate_shift {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {τ : (∀ b, Y b) → (∀ b, Y b)}
    (hcomm : ∀ f, K (f ∘ τ) = K f ∘ τ) (hconst : ∀ f (a : ℝ), K (fun y => f y + a) = fun y => K f y + a)
    {g : (∀ b, Y b) → ℝ} {c : ℝ} (hg : ∀ y, g (τ y) = g y + c) :
    ∀ n y, K^[n] g (τ y) = K^[n] g y + c := by
  intro n
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    intro y
    have hfun : K^[n] g ∘ τ = fun y => K^[n] g y + c := funext ih
    rw [Function.iterate_succ_apply']
    have := congrFun (hcomm (K^[n] g)) y
    simp only [Function.comp_apply] at this
    rw [← this, hfun, hconst]

/-- **No contraction survives a persistent gap.** If the iterates of a Lipschitz test keep a gap `c > 0`
between two configurations at every shell count, no Lipschitz-Dobrushin contraction `α < 1` holds. -/
theorem not_contract_of_shift {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ} {α V D : ℝ}
    (hK : LipInfl K C) (hDC : DobCond C α) (hα : 0 ≤ α) (hα1 : α < 1) (hV0 : 0 ≤ V) (hD0 : 0 ≤ D)
    (hDiam : ∀ b (u v : Y b), dist u v ≤ D) {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} (hL : ∀ j, 0 ≤ L j)
    (hLV : ∀ j, L j ≤ V) (hg : BlockLip g L) (y₀ y₁ : ∀ b, Y b) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ n, c ≤ |K^[n] g y₁ - K^[n] g y₀|) : False := by
  set M : ℝ := 2 * (Fintype.card ι * V * D) + 1 with hMdef
  have hM0 : 0 ≤ Fintype.card ι * V * D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hV0) hD0
  have hM : 0 < M := by rw [hMdef]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hc hM) hα1
  obtain ⟨c', hc'⟩ := lip_near_const hK hDC hα hV0 hD0 hDiam hL hLV hg n
  have h1 := hc' y₁
  have h0 := hc' y₀
  have htri : |K^[n] g y₁ - K^[n] g y₀| ≤ |K^[n] g y₁ - c'| + |K^[n] g y₀ - c'| := by
    rw [← abs_sub_comm c' (K^[n] g y₀)]; exact abs_sub_le _ _ _
  have hpow : 0 ≤ α ^ n := pow_nonneg hα n
  have hlt : M * α ^ n < c := by
    rw [lt_div_iff₀ hM] at hn; rw [mul_comm]; exact hn
  have hle : 2 * (Fintype.card ι * (α ^ n * V) * D) ≤ M * α ^ n := by
    have : 2 * (Fintype.card ι * (α ^ n * V) * D) = 2 * (Fintype.card ι * V * D) * α ^ n := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) hpow
  linarith [hgap n]

end Iteration

/-! ## 2. The coupling bound -/

section Coupling

open MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- **A coupling bounds the difference of two expectations of a Lipschitz test.** -/
theorem abs_integral_sub_le_coupling {μ ν : Measure X} (π : Measure (X × X))
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) {f : X → ℝ} {ℓ : ℝ} (hfm : Measurable f)
    (hf : ∀ x x', |f x - f x'| ≤ ℓ * dist x x')
    (hI1 : Integrable (fun p : X × X => f p.1) π) (hI2 : Integrable (fun p : X × X => f p.2) π)
    (hId : Integrable (fun p : X × X => dist p.1 p.2) π) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ℓ * ∫ p, dist p.1 p.2 ∂π := by
  rw [← h1, ← h2, integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hfm.aestronglyMeasurable, ← integral_sub hI1 hI2,
    ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans ?_
  exact integral_mono (hI1.sub hI2).abs (hId.const_mul ℓ) fun p => hf p.1 p.2

end Coupling

/-! ## The Wilson box kernel -/

section Wilson

open MassGap.GibbsSpec MassGap.SUN MassGap.PeriodicStateDLR

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ b, PseudoMetricSpace (Y b)]

/-- **`KernelNear` from the Lipschitz block Dobrushin step.** The box kernel equals `n` shells of a block
operator with Lipschitz-Dobrushin influence `C` (row sums at most `α`) applied to a block test of Lipschitz
vector at most `V`, with block diameters at most `D`: then `KernelNear Δ X (|ι| αⁿ V D)`. -/
theorem kernelNear_of_lip (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SU N), ℝ))
    (e : IConf (SU N) → ∀ b, Y b) {K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)} {C : ι → ι → ℝ}
    {α V D : ℝ} (hK : LipInfl K C) (hDC : DobCond C α) (hα : 0 ≤ α) (hV0 : 0 ≤ V) (hD0 : 0 ≤ D)
    (hDiam : ∀ b (u v : Y b), dist u v ≤ D) {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} (hL : ∀ j, 0 ≤ L j)
    (hLV : ∀ j, L j ≤ V) (hg : BlockLip g L) (n : ℕ) (hfac : ∀ ω, wspec hN β Δ X ω = K^[n] g (e ω)) :
    BoxFocusTest.KernelNear hN β Δ X (Fintype.card ι * (α ^ n * V) * D) := by
  obtain ⟨c, hc⟩ := lip_near_const hK hDC hα hV0 hD0 hDiam hL hLV hg n
  exact ⟨c, fun ω => by rw [hfac]; exact hc _⟩

end Wilson

end MassGap.BlockLipschitz

#print axioms MassGap.BlockLipschitz.blockLip_iter
#print axioms MassGap.BlockLipschitz.lip_near_const
#print axioms MassGap.BlockLipschitz.iterate_shift
#print axioms MassGap.BlockLipschitz.not_contract_of_shift
#print axioms MassGap.BlockLipschitz.abs_integral_sub_le_coupling
#print axioms MassGap.BlockLipschitz.kernelNear_of_lip
