import Mathlib
import MassGap.TensionFloor

/-!
# MassGap.SizePartition — the IMS localisation for a transfer kernel, and the loop-size partition of the slice

`TensionFloor` reduces the `SU(2)` zero-flux gap to the author's attraction picture made precise and records the
missing structure: a partition of the slice's configuration space by loop size, a per-piece cost, and a
localisation error. This module builds the partition and the IMS skeleton on the real objects, and measures
what the skeleton asks.

## 1. The IMS identity for a kernel (proved, any measure space, any kernel)

`form μ K f g = ∫∫ K(x,y) f(x) g(y)`, `nsq μ f = ∫ f²`, `quad μ K λ f = λ · nsq f − form f f` (the form of
`λ − K`). `IsSqPartition χ`: `Σ_i χ_i(x)² = 1` at every `x` (`ι` finite). `loc χ i ψ = χ_i ψ`.
`locErr μ K χ ψ = ½ ∫∫ K(x,y) ψ(x) ψ(y) Σ_i (χ_i(x) − χ_i(y))²`, the kernel of `½ Σ_i [χ_i,[χ_i,K]]`.

* `sum_mul_eq`: `Σ_i χ_i(x) χ_i(y) = 1 − ½ Σ_i (χ_i(x) − χ_i(y))²`, the pointwise core.
* **`form_split`**: `form ψ ψ = Σ_i form (χ_i ψ) (χ_i ψ) + locErr ψ`.
* `nsq_split`: `nsq ψ = Σ_i nsq (χ_i ψ)`.
* **`quad_split`**: `quad λ ψ = Σ_i quad λ (χ_i ψ) − locErr ψ`, at every `λ`.

The identities hold for every kernel: neither symmetry nor positivity of `K` is used, and the partition
functions need not commute with anything. Integrability: `Adm μ K ψ` (the integrands of `form ψ ψ` and
`nsq ψ` are integrable) and measurable `χ_i`; the localised integrands are then integrable because
`|χ_i| ≤ 1`.

## 2. The skeleton: per-piece cost and localisation cost give the gap (proved)

`Ω` with eigenvalue `λ₀`, `Orth μ Ω ψ` (`∫ Ω ψ = 0`).

* (ii') `PieceCost μ K χ Ω λ₀ f`: for every admissible `ψ ⊥ Ω` and every piece `i`,
  `f_i · nsq(χ_i ψ) ≤ quad λ₀ (χ_i ψ)`.
* (iii') `LocCost μ K χ g`: for every admissible `ψ`, `locErr ψ ≤ Σ_i g_i · nsq(χ_i ψ)` (the IMS
  operator bound `½ Σ_i [χ_i,[χ_i,K]] ≤ Σ_i χ_i g_i χ_i`, read on forms).
* **`quad_ge_of_pieces`**: (ii'), (iii') and `m ≤ f_i − g_i` for every `i` give
  `m · nsq ψ ≤ quad λ₀ ψ` on every admissible `ψ ⊥ Ω`.
* `form_eigen`: on an integrable eigenfunction `form ψ ψ = μ · nsq ψ` (Fubini).
* **`exists_partition_iff`**: with the partition existentially quantified,
  `(∃ ι χ f g, (ii') ∧ (iii') ∧ m ≤ f − g) ↔ FormGap μ K Ω λ₀ m` (the trivial one-piece partition,
  `locErr = 0`). The skeleton's content is in the partition being fixed in advance.

## 3. (ii') is unsatisfiable at `m > 0` when the vacuum can be balanced off every piece (proved)

`Balanced μ χ Ω`: for every piece `i` there is a bounded measurable `h` with `χ_i h = χ_i` and
`∫ h Ω² = 0` (then `h Ω ⊥ Ω` and its piece `i` is the vacuum's own piece `χ_i Ω`).

* **`nonpos_of_balanced`**: `K Ω = λ₀ Ω`, `nsq Ω > 0`, `Balanced`, (ii') at `f`, (iii') at `g` and
  `m ≤ f_i − g_i` for all `i` force `m ≤ 0`. Proof: `quad λ₀ Ω = 0`, so `quad_split` at `Ω` gives
  `Σ_i quad λ₀ (χ_i Ω) = locErr Ω ≤ Σ_i g_i w_i` (`w_i = nsq (χ_i Ω)`), while (ii') at `h Ω` gives
  `f_i w_i ≤ quad λ₀ (χ_i Ω)` for every `i`; so `m · nsq Ω ≤ Σ (f_i − g_i) w_i ≤ 0`.
* `balanced_piece`: a piece is balanced when `χ_i` vanishes on a measurable set `B` with
  `∫_B Ω² > 0` (`h = 1 − (nsq Ω / ∫_B Ω²) 1_B`).

So per-piece Rayleigh bounds against `Ω` alone, the form (ii') takes, cannot yield a positive gap once
every piece misses a region where the vacuum has weight.

## 4. The local-vacuum skeleton: local vacua and a gluing term (proved)

* (ii'') `LocalGap μ K χ λ₀ u f`: for every admissible `ψ` (no orthogonality) and every `i`,
  `f_i (nsq(χ_i ψ) − ⟨u_i, χ_i ψ⟩²) ≤ quad λ₀ (χ_i ψ)`: piece `i` has a local vacuum `u_i` and a local
  gap `f_i` above it.
* **`quad_ge_of_local_vacua`**: (ii''), (iii') and `m ≤ f_i − g_i` give
  `m · nsq ψ − Σ_i f_i ⟨u_i, χ_i ψ⟩² ≤ quad λ₀ ψ` for every admissible `ψ`.
* `formGap_of_local_vacua`: adding (iv) the gluing bound `Σ_i f_i ⟨u_i, χ_i ψ⟩² ≤ η · nsq ψ` on
  `ψ ⊥ Ω` gives `FormGap μ K Ω λ₀ (m − η)`.
  (ii'') is consistent with the vacuum (at `u_i = χ_i Ω/√w_i` its left side vanishes on `χ_i Ω`, so the balanced-piece obstruction of §3 no longer applies).

## 5. The loop-size partition of the real slice (defined; measurability proved)

On `Slice n i` (spatial `SU(2)` links of step `i`, Haar `hSN 2 n i`):

* `plaqHol V ν ν' y`: the holonomy of the spatial plaquette at `y` in the plane `(ν, ν')` (the argument of
  `RectWilson.spT`'s density).
* `pierce θ δ d = min 1 (max 0 ((d − θ)/δ))`: `0` below density `θ`, `1` above `θ + δ`, linear between. At
  `SU(2)` the density is `1 − ½ Re tr ∈ [0, 2]`; `θ = 1` is the centre-projection threshold
  (`Re tr < 0`), a thin centre vortex having density `2`.
* `loopLen θ δ V = Σ_{ν,ν',y} pierce(density(plaqHol V ν ν' y))`: the soft number of pierced spatial
  plaquettes (ordered planes, so each plaquette twice; diagonal `ν = ν'` terms vanish at `θ ≥ 0`, `δ > 0`), the length of the vortex lines in the slice in
  dual-link units, doubled. `loopSize θ δ β V = aRun 2 β · loopLen / 2`: that length in physical units.
* `bucketW w K k s`: tents of width `w` centred at `k w` for `k < K`, and a ramp to `1` beyond
  `(K − 1) w` for the last bucket. `sqPart W i₀`: `χ_i = √(W_i⁺/Σ_j W_j⁺)` (`i₀`'s indicator where all
  weights vanish); `sqPart_isSqPartition` (always) and `measurable_sqPart`.
* `sizePart θ δ β w K : Fin (K+1) → Slice n i → ℝ`: `sqPart` of the buckets of `loopSize`.
  `sizePart_isSqPartition`, `measurable_sizePart` (`continuous_loopLen`).
* `SizePieceCost`, `SizeLocCost`: (ii') and (iii') for `trivKN 2 β n i` and `sizePart`.
* **`zeroFluxGap_of_sizePieces`**: on `TensionFloor.EigenLevels β n i g₀ E φ μ` with `μ_{g₀} = λ₀`,
  `0 < m < λ₀`, `μ_j ≥ 0`, every `φ_j` admissible, (ii') against `φ_{g₀}`, (iii') and `m ≤ f_k − g_k`:
  `ZeroFluxGap g₀ E (−2 log(1 − m/λ₀) / (n · aRun 2 β))`. Its hypotheses at `m > 0` are argued
  unsatisfiable on the slice (Evaluation below), so it is the chain on the real objects, not a route to
  the gap; the surviving form is §4.

## Evaluation

* Search: no IMS identity, double-commutator identity or square partition of unity is in the live tree, the
  pruned archive (tainted modules skipped; `ZeroDiagPartition` is a sum-one dyadic partition on `ℝ^d`,
  `TemperedLocalize` a distributional support statement, `HeatBathLocal.torus_poincare` a Poincaré
  inequality on the torus), Mathlib (`SmoothPartitionOfUnity` sums to one, not squares), or the
  Entroptics library. `SecondEigenvalue` has Rayleigh quotients on an invariant subspace, not a
  localisation. The tree's vortex objects (`VortexCondense`, `VortexTorus`, `VortexAperture`,
  `ChunkActivity`) are twisted partition functions and plaquette polymers on the 4-torus, not a size
  functional on the slice; `loopLen` is new.
* The skeleton reduces the gap to (ii') + (iii') without restating it only through the fixed partition
  (`exists_partition_iff`: with the partition free it is the gap). With the loop-size partition fixed, the
  real-object chain is `zeroFluxGap_of_sizePieces`.
* But (ii') in the form above (per-piece Rayleigh bounds on `ψ ⊥ Ω`), with (iii') and `m ≤ f − g`, has no solution at `m > 0` once
  the vacuum is balanced off every piece (`nonpos_of_balanced`). On the slice (argued, not formalised):
  `trivKN ≥ floor β n i > 0`, so the ground eigenfunction can be taken strictly positive; every bucket of
  `sizePart` vanishes on a set of positive Haar measure (for `δ > 0`, `0 < θ < 2`, `w > 0`, `K ≥ 1` and
  `w` below the largest `loopSize`: bucket `0` vanishes on the open set `loopSize > w`, every other bucket
  on the open neighbourhood of the identity where every plaquette density is below `θ`; open sets have
  positive Haar measure), so every piece is balanced (`balanced_piece`) and the chain gives `m ≤ 0`. This is the
  configuration-space form of the obstruction in `TensionFloor`: a centre-vortex size is a magnetic
  property of a configuration, and (V) (`VortexCostAt`: `1 − zR` small, vortices free) says the vacuum is
  spread over vortex sizes rather than concentrated on a small-size piece.
* The form that survives is §4: (ii'') a local gap `f_k` above a local vacuum on each size piece, (iii')
  the localisation bound, and (iv) the gluing bound on the overlaps `⟨u_k, χ_k ψ⟩` of a state orthogonal
  to `Ω` with the local vacua. (iv) is a gap statement for the coarse chain on piece labels; with one
  piece it is `⟨Ω, ψ⟩ = 0` and (ii'') is the gap. The author's flux-tube cost (a loop of size `R` costs `cσR`)
  is a statement about electric flux loops, which are states (`tr hol_C · Ω`), not regions of
  configuration space; on the size pieces it would enter (ii'') as the local gap and (iv) as the coarse
  chain. None of (ii''), (iii'), (iv) is proved for `trivKN`; each is open.

DERIVED (module-wide): `½` and `2` in the IMS identity are `Σ_i (a_i − b_i)² = Σ a_i² + Σ b_i² − 2 Σ a_i b_i`
at `Σ a_i² = Σ b_i² = 1`; `−2 log` and the `2` in `loopSize`'s `/ 2` are the square in
`μ_j² = e^{−E_j t}` and the two orientations of each plaquette; `1` in `pierce` and `bucketW` is the
indicator's value; `θ = 1` is where `Re tr` changes sign at `SU(2)`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SizePartition

open MeasureTheory Finset

/-! ## 1. The IMS identity for a kernel -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {ι : Type*} [Fintype ι]

variable (μ) in
/-- The bilinear form of a kernel: `∫∫ K(x,y) f(x) g(y)`. -/
def form (K : X → X → ℝ) (f g : X → ℝ) : ℝ := ∫ p, K p.1 p.2 * f p.1 * g p.2 ∂(μ.prod μ)

variable (μ) in
/-- The squared norm `∫ f²`. -/
def nsq (f : X → ℝ) : ℝ := ∫ x, f x ^ 2 ∂μ

variable (μ) in
/-- The form of `λ − K`: `λ · nsq f − form f f`. -/
def quad (K : X → X → ℝ) (lam : ℝ) (f : X → ℝ) : ℝ := lam * nsq μ f - form μ K f f

/-- The `i`-th localised piece `χ_i ψ`. -/
def loc (χ : ι → X → ℝ) (i : ι) (f : X → ℝ) : X → ℝ := fun x => χ i x * f x

variable (μ) in
/-- The localisation error: the form of `½ Σ_i [χ_i,[χ_i,K]]`. -/
def locErr (K : X → X → ℝ) (χ : ι → X → ℝ) (f : X → ℝ) : ℝ :=
  (1 / 2) * ∫ p, K p.1 p.2 * f p.1 * f p.2 * ∑ i, (χ i p.1 - χ i p.2) ^ 2 ∂(μ.prod μ)

/-- A square partition of unity: `Σ_i χ_i(x)² = 1` at every `x`. -/
def IsSqPartition (χ : ι → X → ℝ) : Prop := ∀ x, ∑ i, χ i x ^ 2 = 1

variable (μ) in
/-- Admissible: the integrands of `form f f` and `nsq f` are integrable. -/
structure Adm (K : X → X → ℝ) (f : X → ℝ) : Prop where
  form_int : Integrable (fun p : X × X => K p.1 p.2 * f p.1 * f p.2) (μ.prod μ)
  sq_int : Integrable (fun x => f x ^ 2) μ

variable (μ) in
/-- `ψ ⊥ Ω` in `L²(μ)`. -/
def Orth (Ω ψ : X → ℝ) : Prop := ∫ x, Ω x * ψ x ∂μ = 0

theorem nsq_nonneg (f : X → ℝ) : 0 ≤ nsq μ f := integral_nonneg fun _ => sq_nonneg _

variable {χ : ι → X → ℝ} {K : X → X → ℝ}

omit [MeasurableSpace X] in
theorem sq_le_one_of_part (h : IsSqPartition χ) (i : ι) (x : X) : χ i x ^ 2 ≤ 1 := by
  rw [← h x]
  exact Finset.single_le_sum (f := fun j => χ j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

omit [MeasurableSpace X] in
theorem abs_le_one_of_part (h : IsSqPartition χ) (i : ι) (x : X) : |χ i x| ≤ 1 := by
  have := sq_le_one_of_part h i x
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

omit [MeasurableSpace X] in
/-- **The pointwise core**: `Σ_i χ_i(x) χ_i(y) = 1 − ½ Σ_i (χ_i(x) − χ_i(y))²`. -/
theorem sum_mul_eq (h : IsSqPartition χ) (x y : X) :
    ∑ i, χ i x * χ i y = 1 - (1 / 2) * ∑ i, (χ i x - χ i y) ^ 2 := by
  have e : ∀ i, (χ i x - χ i y) ^ 2 = χ i x ^ 2 + χ i y ^ 2 - 2 * (χ i x * χ i y) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, Finset.sum_add_distrib, h x, h y,
    ← Finset.mul_sum]
  ring

omit [MeasurableSpace X] in
theorem integrand_split (h : IsSqPartition χ) (K : X → X → ℝ) (ψ : X → ℝ) (x y : X) :
    K x y * ψ x * ψ y = ∑ i, K x y * loc χ i ψ x * loc χ i ψ y
      + (1 / 2) * (K x y * ψ x * ψ y * ∑ i, (χ i x - χ i y) ^ 2) := by
  have e : ∑ i, K x y * loc χ i ψ x * loc χ i ψ y = K x y * ψ x * ψ y * ∑ i, χ i x * χ i y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [loc]; ring
  rw [e, sum_mul_eq h x y]
  ring

theorem integrable_piece (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) {ψ : X → ℝ}
    (hA : Adm μ K ψ) (i : ι) :
    Integrable (fun p : X × X => K p.1 p.2 * loc χ i ψ p.1 * loc χ i ψ p.2) (μ.prod μ) := by
  have hg : AEStronglyMeasurable (fun p : X × X => χ i p.1 * χ i p.2) (μ.prod μ) :=
    (((hm i).comp measurable_fst).mul ((hm i).comp measurable_snd)).aestronglyMeasurable
  have hb : ∀ᵐ p ∂(μ.prod μ), ‖χ i p.1 * χ i p.2‖ ≤ 1 := ae_of_all _ fun p => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (abs_le_one_of_part hχ i p.1) (abs_nonneg _) (abs_le_one_of_part hχ i p.2)
  refine (hA.form_int.mul_bdd hg hb).congr (ae_of_all _ fun p => ?_)
  simp only [loc]
  ring

theorem integrable_loc_sq (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) {ψ : X → ℝ}
    (hψ : Integrable (fun x => ψ x ^ 2) μ) (i : ι) :
    Integrable (fun x => loc χ i ψ x ^ 2) μ := by
  have hg : AEStronglyMeasurable (fun x => χ i x ^ 2) μ := ((hm i).pow_const 2).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖χ i x ^ 2‖ ≤ 1 := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_one_of_part hχ i x
  refine (hψ.bdd_mul hg hb).congr (ae_of_all _ fun x => ?_)
  simp only [loc]
  ring

/-- **The IMS identity for a kernel**: `form ψ ψ = Σ_i form (χ_i ψ) (χ_i ψ) + locErr ψ`. -/
theorem form_split (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) {ψ : X → ℝ}
    (hA : Adm μ K ψ) :
    form μ K ψ ψ = ∑ i, form μ K (loc χ i ψ) (loc χ i ψ) + locErr μ K χ ψ := by
  have hI := fun i => integrable_piece hχ hm hA i
  have hS : Integrable (fun p : X × X => ∑ i, K p.1 p.2 * loc χ i ψ p.1 * loc χ i ψ p.2) (μ.prod μ) :=
    integrable_finsetSum _ fun i _ => hI i
  have hR : Integrable (fun p : X × X =>
      (1 / 2) * (K p.1 p.2 * ψ p.1 * ψ p.2 * ∑ i, (χ i p.1 - χ i p.2) ^ 2)) (μ.prod μ) := by
    refine (hA.form_int.sub hS).congr (ae_of_all _ fun p => ?_)
    have := integrand_split hχ K ψ p.1 p.2
    simp only [Pi.sub_apply]
    linear_combination this
  have hfun : (fun p : X × X => K p.1 p.2 * ψ p.1 * ψ p.2) = fun p =>
      (∑ i, K p.1 p.2 * loc χ i ψ p.1 * loc χ i ψ p.2)
        + (1 / 2) * (K p.1 p.2 * ψ p.1 * ψ p.2 * ∑ i, (χ i p.1 - χ i p.2) ^ 2) :=
    funext fun p => integrand_split hχ K ψ p.1 p.2
  unfold form locErr
  rw [hfun, integral_add hS hR, integral_finsetSum _ fun i _ => hI i, integral_const_mul]

/-- `nsq ψ = Σ_i nsq (χ_i ψ)`. -/
theorem nsq_split (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) {ψ : X → ℝ}
    (hψ : Integrable (fun x => ψ x ^ 2) μ) :
    nsq μ ψ = ∑ i, nsq μ (loc χ i ψ) := by
  unfold nsq
  rw [← integral_finsetSum _ fun i _ => integrable_loc_sq hχ hm hψ i]
  congr 1
  funext x
  simp only [loc, mul_pow, ← Finset.sum_mul, hχ x, one_mul]

/-- **The IMS identity for `λ − K`**: `quad λ ψ = Σ_i quad λ (χ_i ψ) − locErr ψ`. -/
theorem quad_split (lam : ℝ) (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) {ψ : X → ℝ}
    (hA : Adm μ K ψ) :
    quad μ K lam ψ = ∑ i, quad μ K lam (loc χ i ψ) - locErr μ K χ ψ := by
  unfold quad
  rw [nsq_split hχ hm hA.sq_int, form_split hχ hm hA, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- Multiplying an admissible function by a bounded measurable one keeps it admissible. -/
theorem adm_mul {f h : X → ℝ} (hA : Adm μ K f) (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Adm μ K (fun x => h x * f x) := by
  have hC0 : ∀ x, 0 ≤ C := fun x => (abs_nonneg _).trans (hC x)
  constructor
  · have hg : AEStronglyMeasurable (fun p : X × X => h p.1 * h p.2) (μ.prod μ) :=
      ((hh.comp measurable_fst).mul (hh.comp measurable_snd)).aestronglyMeasurable
    have hb : ∀ᵐ p ∂(μ.prod μ), ‖h p.1 * h p.2‖ ≤ C * C := ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _) (hC _) (abs_nonneg _) (hC0 p.1)
    refine (hA.form_int.mul_bdd hg hb).congr (ae_of_all _ fun p => ?_)
    ring
  · have hg : AEStronglyMeasurable (fun x => h x ^ 2) μ := (hh.pow_const 2).aestronglyMeasurable
    have hb : ∀ᵐ x ∂μ, ‖h x ^ 2‖ ≤ C * C := ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow, sq]
      exact mul_le_mul (hC _) (hC _) (abs_nonneg _) (hC0 x)
    refine (hA.sq_int.bdd_mul hg hb).congr (ae_of_all _ fun x => ?_)
    ring

/-- On an integrable eigenfunction, `form ψ ψ = μ · nsq ψ` (Fubini). -/
theorem form_eigen [SFinite μ] {ψ : X → ℝ} {ev : ℝ}
    (hint : Integrable (fun p : X × X => K p.1 p.2 * ψ p.1 * ψ p.2) (μ.prod μ))
    (heig : ∀ x, ∫ y, K x y * ψ y ∂μ = ev * ψ x) : form μ K ψ ψ = ev * nsq μ ψ := by
  unfold form nsq
  rw [integral_prod _ hint]
  have e : (fun x => ∫ y, K x y * ψ x * ψ y ∂μ) = fun x => ev * ψ x ^ 2 := by
    funext x
    have e' : (fun y => K x y * ψ x * ψ y) = fun y => ψ x * (K x y * ψ y) := funext fun y => by ring
    rw [e', integral_const_mul, heig x]
    ring
  show ∫ x, ∫ y, K x y * ψ x * ψ y ∂μ ∂μ = _
  rw [e, integral_const_mul]

/-! ## 2. The skeleton -/

variable (μ) in
/-- **(ii') Per-piece cost**: on every admissible `ψ ⊥ Ω`, piece `i` costs at least `f_i` per unit norm
in `λ₀ − K`. -/
def PieceCost (K : X → X → ℝ) (χ : ι → X → ℝ) (Ω : X → ℝ) (lam : ℝ) (f : ι → ℝ) : Prop :=
  ∀ ψ, Adm μ K ψ → Orth μ Ω ψ → ∀ i, f i * nsq μ (loc χ i ψ) ≤ quad μ K lam (loc χ i ψ)

variable (μ) in
/-- **(iii') Localisation cost**: on every admissible `ψ`, `locErr ψ ≤ Σ_i g_i nsq(χ_i ψ)`. -/
def LocCost (K : X → X → ℝ) (χ : ι → X → ℝ) (g : ι → ℝ) : Prop :=
  ∀ ψ, Adm μ K ψ → locErr μ K χ ψ ≤ ∑ i, g i * nsq μ (loc χ i ψ)

variable (μ) in
/-- The gap on forms: `m · nsq ψ ≤ quad λ₀ ψ` on every admissible `ψ ⊥ Ω`. -/
def FormGap (K : X → X → ℝ) (Ω : X → ℝ) (lam m : ℝ) : Prop :=
  ∀ ψ, Adm μ K ψ → Orth μ Ω ψ → m * nsq μ ψ ≤ quad μ K lam ψ

theorem sum_cost_ge {ψ : X → ℝ} {m : ℝ} {f g : ι → ℝ} (hχ : IsSqPartition χ)
    (hm : ∀ i, Measurable (χ i)) (hψ : Integrable (fun x => ψ x ^ 2) μ) (hmin : ∀ i, m ≤ f i - g i) :
    m * nsq μ ψ ≤ ∑ i, f i * nsq μ (loc χ i ψ) - ∑ i, g i * nsq μ (loc χ i ψ) := by
  rw [nsq_split hχ hm hψ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => by
    have := mul_le_mul_of_nonneg_right (hmin i) (nsq_nonneg (μ := μ) (loc χ i ψ))
    linarith

/-- **The IMS skeleton**: (ii') and (iii') with `m ≤ f_i − g_i` give the gap `m` on forms. -/
theorem quad_ge_of_pieces {Ω ψ : X → ℝ} {lam m : ℝ} {f g : ι → ℝ} (hχ : IsSqPartition χ)
    (hm : ∀ i, Measurable (χ i)) (hA : Adm μ K ψ) (hO : Orth μ Ω ψ)
    (hf : PieceCost μ K χ Ω lam f) (hg : LocCost μ K χ g) (hmin : ∀ i, m ≤ f i - g i) :
    m * nsq μ ψ ≤ quad μ K lam ψ := by
  rw [quad_split lam hχ hm hA]
  have h1 := hg ψ hA
  have h2 : ∑ i, f i * nsq μ (loc χ i ψ) ≤ ∑ i, quad μ K lam (loc χ i ψ) :=
    Finset.sum_le_sum fun i _ => hf ψ hA hO i
  have h3 := sum_cost_ge hχ hm hA.sq_int hmin (f := f) (g := g)
  linarith

theorem formGap_of_pieces {Ω : X → ℝ} {lam m : ℝ} {f g : ι → ℝ} (hχ : IsSqPartition χ)
    (hm : ∀ i, Measurable (χ i)) (hf : PieceCost μ K χ Ω lam f) (hg : LocCost μ K χ g)
    (hmin : ∀ i, m ≤ f i - g i) : FormGap μ K Ω lam m :=
  fun _ hA hO => quad_ge_of_pieces hχ hm hA hO hf hg hmin

/-- **With the partition free, the skeleton is the gap**: the one-piece partition `χ ≡ 1` has
`locErr = 0`, and (ii') at `f ≡ m` is `FormGap`. -/
theorem exists_partition_iff {Ω : X → ℝ} {lam m : ℝ} :
    (∃ (κ : Type) (_ : Fintype κ) (χ : κ → X → ℝ) (f g : κ → ℝ), IsSqPartition χ ∧
        (∀ i, Measurable (χ i)) ∧ PieceCost μ K χ Ω lam f ∧ LocCost μ K χ g ∧ ∀ i, m ≤ f i - g i) ↔
      FormGap μ K Ω lam m := by
  constructor
  · rintro ⟨κ, _, χ, f, g, hχ, hm, hf, hg, hmin⟩
    exact formGap_of_pieces hχ hm hf hg hmin
  · intro h
    have hl : ∀ ψ : X → ℝ, loc (fun (_ : Unit) (_ : X) => (1 : ℝ)) () ψ = ψ :=
      fun ψ => funext fun x => one_mul _
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => m, fun _ => 0, fun x => by simp,
      fun _ => measurable_const, fun ψ hA hO i => ?_, fun ψ _ => ?_, fun _ => by simp⟩
    · rw [hl]
      exact h ψ hA hO
    · simp [locErr]

/-! ## 3. Balanced pieces: (ii') forces `m ≤ 0` -/

variable (μ) in
/-- **The vacuum can be balanced off every piece**: for each `i` a bounded measurable `h` with
`χ_i h = χ_i` and `∫ h Ω² = 0`. -/
def Balanced (χ : ι → X → ℝ) (Ω : X → ℝ) : Prop :=
  ∀ i, ∃ h : X → ℝ, Measurable h ∧ (∃ C, ∀ x, |h x| ≤ C) ∧ (∀ x, χ i x * h x = χ i x) ∧
    ∫ x, h x * Ω x ^ 2 ∂μ = 0

/-- **Per-piece costs against `Ω` give no positive gap once the vacuum is balanced off every piece.** -/
theorem nonpos_of_balanced [SFinite μ] {Ω : X → ℝ} {lam m : ℝ} {f g : ι → ℝ}
    (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) (hA : Adm μ K Ω)
    (heig : ∀ x, ∫ y, K x y * Ω y ∂μ = lam * Ω x) (hn : 0 < nsq μ Ω) (hbal : Balanced μ χ Ω)
    (hf : PieceCost μ K χ Ω lam f) (hg : LocCost μ K χ g) (hmin : ∀ i, m ≤ f i - g i) : m ≤ 0 := by
  have hq0 : quad μ K lam Ω = 0 := by
    unfold quad
    rw [form_eigen hA.form_int heig]
    ring
  have hsplit := quad_split lam hχ hm hA
  have hloc := hg Ω hA
  have hpiece : ∀ i, f i * nsq μ (loc χ i Ω) ≤ quad μ K lam (loc χ i Ω) := by
    intro i
    obtain ⟨h, hhm, ⟨C, hC⟩, hfix, hint⟩ := hbal i
    have hAψ := adm_mul hA hhm hC
    have hO : Orth μ Ω (fun x => h x * Ω x) := by
      show ∫ x, Ω x * (h x * Ω x) ∂μ = 0
      rw [← hint]
      congr 1
      funext x
      ring
    have hl : loc χ i (fun x => h x * Ω x) = loc χ i Ω := by
      funext x
      show χ i x * (h x * Ω x) = χ i x * Ω x
      rw [← mul_assoc, hfix x]
    have := hf _ hAψ hO i
    rwa [hl] at this
  have h2 : ∑ i, f i * nsq μ (loc χ i Ω) ≤ ∑ i, quad μ K lam (loc χ i Ω) :=
    Finset.sum_le_sum fun i _ => hpiece i
  have h3 := sum_cost_ge hχ hm hA.sq_int hmin (f := f) (g := g)
  by_contra hcon
  have := mul_pos (lt_of_not_ge hcon) hn
  linarith

/-- A piece is balanced when `χ_i` vanishes on a measurable set carrying vacuum weight. -/
theorem balanced_piece {χi Ω : X → ℝ} {B : Set X} (hB : MeasurableSet B) (hzero : ∀ x ∈ B, χi x = 0)
    (hΩ : Integrable (fun x => Ω x ^ 2) μ)
    (hw : 0 < ∫ x, B.indicator (fun _ => (1 : ℝ)) x * Ω x ^ 2 ∂μ) :
    ∃ h : X → ℝ, Measurable h ∧ (∃ C, ∀ x, |h x| ≤ C) ∧ (∀ x, χi x * h x = χi x) ∧
      ∫ x, h x * Ω x ^ 2 ∂μ = 0 := by
  classical
  obtain ⟨wB, hwB⟩ : ∃ w, w = ∫ x, B.indicator (fun _ => (1 : ℝ)) x * Ω x ^ 2 ∂μ := ⟨_, rfl⟩
  rw [← hwB] at hw
  obtain ⟨k, hk⟩ : ∃ k, k = (∫ x, Ω x ^ 2 ∂μ) / wB := ⟨_, rfl⟩
  have hI : Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) x * Ω x ^ 2) μ := by
    refine hΩ.bdd_mul (c := 1) (measurable_const.indicator hB).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Set.indicator_apply]
    split_ifs <;> simp
  refine ⟨fun x => 1 - k * B.indicator (fun _ => (1 : ℝ)) x,
    measurable_const.sub (measurable_const.mul (measurable_const.indicator hB)),
    ⟨1 + |k|, fun x => ?_⟩, fun x => ?_, ?_⟩
  · show |1 - k * B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 + |k|
    rw [Set.indicator_apply]
    split_ifs
    · rw [mul_one]
      exact abs_le.mpr ⟨by linarith [le_abs_self k], by linarith [neg_le_abs k]⟩
    · rw [mul_zero, sub_zero, abs_one]
      linarith [abs_nonneg k]
  · show χi x * (1 - k * B.indicator (fun _ => (1 : ℝ)) x) = χi x
    by_cases hx : x ∈ B
    · rw [hzero x hx, zero_mul]
    · rw [Set.indicator_of_notMem hx, mul_zero, sub_zero, mul_one]
  · have e : (fun x => (1 - k * B.indicator (fun _ => (1 : ℝ)) x) * Ω x ^ 2) =
        fun x => Ω x ^ 2 - k * (B.indicator (fun _ => (1 : ℝ)) x * Ω x ^ 2) :=
      funext fun x => by ring
    rw [e, integral_sub hΩ (hI.const_mul k), integral_const_mul, ← hwB, hk,
      div_mul_cancel₀ _ hw.ne', sub_self]

/-! ## 4. The local-vacuum skeleton: local vacua and a gluing term -/

variable (μ) in
/-- `⟨u, v⟩` in `L²(μ)`. -/
def ip (u v : X → ℝ) : ℝ := ∫ x, u x * v x ∂μ

variable (μ) in
/-- **(ii'') Local gap above a local vacuum**: on every admissible `ψ` and every piece `i`,
`f_i (nsq(χ_i ψ) − ⟨u_i, χ_i ψ⟩²) ≤ quad λ₀ (χ_i ψ)`. -/
def LocalGap (K : X → X → ℝ) (χ : ι → X → ℝ) (lam : ℝ) (u : ι → X → ℝ) (f : ι → ℝ) : Prop :=
  ∀ ψ, Adm μ K ψ → ∀ i,
    f i * (nsq μ (loc χ i ψ) - ip μ (u i) (loc χ i ψ) ^ 2) ≤ quad μ K lam (loc χ i ψ)

/-- **The local-vacuum skeleton**: (ii''), (iii') and `m ≤ f_i − g_i` give
`m · nsq ψ − Σ_i f_i ⟨u_i, χ_i ψ⟩² ≤ quad λ₀ ψ`. -/
theorem quad_ge_of_local_vacua {ψ : X → ℝ} {lam m : ℝ} {u : ι → X → ℝ} {f g : ι → ℝ}
    (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) (hA : Adm μ K ψ)
    (hf : LocalGap μ K χ lam u f) (hg : LocCost μ K χ g) (hmin : ∀ i, m ≤ f i - g i) :
    m * nsq μ ψ - ∑ i, f i * ip μ (u i) (loc χ i ψ) ^ 2 ≤ quad μ K lam ψ := by
  rw [quad_split lam hχ hm hA]
  have h1 := hg ψ hA
  have h2 : ∑ i, (f i * nsq μ (loc χ i ψ) - f i * ip μ (u i) (loc χ i ψ) ^ 2)
      ≤ ∑ i, quad μ K lam (loc χ i ψ) :=
    Finset.sum_le_sum fun i _ => by
      have := hf ψ hA i
      linarith [mul_sub (f i) (nsq μ (loc χ i ψ)) (ip μ (u i) (loc χ i ψ) ^ 2)]
  rw [Finset.sum_sub_distrib] at h2
  have h3 := sum_cost_ge hχ hm hA.sq_int hmin (f := f) (g := g)
  linarith

/-- (ii''), (iii') and (iv) the gluing bound `Σ_i f_i ⟨u_i, χ_i ψ⟩² ≤ η nsq ψ` on `ψ ⊥ Ω` give the gap
`m − η` on forms. -/
theorem formGap_of_local_vacua {Ω : X → ℝ} {lam m η : ℝ} {u : ι → X → ℝ} {f g : ι → ℝ}
    (hχ : IsSqPartition χ) (hm : ∀ i, Measurable (χ i)) (hf : LocalGap μ K χ lam u f)
    (hg : LocCost μ K χ g) (hmin : ∀ i, m ≤ f i - g i)
    (hglue : ∀ ψ, Adm μ K ψ → Orth μ Ω ψ → ∑ i, f i * ip μ (u i) (loc χ i ψ) ^ 2 ≤ η * nsq μ ψ) :
    FormGap μ K Ω lam (m - η) := fun ψ hA hO => by
  have := quad_ge_of_local_vacua hχ hm hA hf hg hmin
  have := hglue ψ hA hO
  linarith [sub_mul m η (nsq μ ψ)]

end Generic

/-! ## 5. The loop-size partition of the real slice -/

section Real

open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.GlueballArea (ZeroFluxGap)
open MassGap.AsymptoticScaling (aRun aRun_pos)

variable {n : ℕ} {i : Fin 4}

/-- The holonomy of the spatial plaquette at `y` in the plane `(ν, ν')` of the slice. -/
def plaqHol (V : Slice n i) (ν ν' : {j : Fin 4 // j ≠ i})
    (y : RectWilson.TT i (CentreSectorSeed.Tr n i)) : SUN.SU 2 :=
  V (ν, y) * V (ν', RectWilson.tsh i (CentreSectorSeed.Tr n i) ν y)
    * (V (ν, RectWilson.tsh i (CentreSectorSeed.Tr n i) ν' y))⁻¹ * (V (ν', y))⁻¹

/-- The soft pierce indicator: `0` below `θ`, `1` above `θ + δ`, linear between. -/
def pierce (θ δ d : ℝ) : ℝ := min 1 (max 0 ((d - θ) / δ))

/-- The soft number of pierced spatial plaquettes (ordered planes). -/
def loopLen (θ δ : ℝ) (V : Slice n i) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ i}, ∑ ν' : {j : Fin 4 // j ≠ i},
    ∑ y : RectWilson.TT i (CentreSectorSeed.Tr n i),
      pierce θ δ (WilsonAction.wilsonDensity (plaqHol V ν ν' y))

/-- The vortex length of a slice configuration in physical units. -/
def loopSize (θ δ β : ℝ) (V : Slice n i) : ℝ := aRun 2 β * loopLen θ δ V / 2

theorem continuous_pierce (θ δ : ℝ) : Continuous (pierce θ δ) :=
  continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const δ))

theorem continuous_plaqHol (ν ν' : {j : Fin 4 // j ≠ i})
    (y : RectWilson.TT i (CentreSectorSeed.Tr n i)) :
    Continuous fun V : Slice n i => plaqHol V ν ν' y := by
  have e1 : Continuous fun V : Slice n i => V (ν, y) := continuous_apply _
  have e2 : Continuous fun V : Slice n i =>
      V (ν', RectWilson.tsh i (CentreSectorSeed.Tr n i) ν y) := continuous_apply _
  have e3 : Continuous fun V : Slice n i =>
      V (ν, RectWilson.tsh i (CentreSectorSeed.Tr n i) ν' y) := continuous_apply _
  have e4 : Continuous fun V : Slice n i => V (ν', y) := continuous_apply _
  unfold plaqHol
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_loopLen (θ δ : ℝ) : Continuous (loopLen (n := n) (i := i) θ δ) := by
  unfold loopLen
  exact continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ν' _ =>
    continuous_finsetSum _ fun y _ =>
      (continuous_pierce θ δ).comp (WilsonAction.continuous_wilsonDensity.comp (continuous_plaqHol ν ν' y))

theorem measurable_loopSize (θ δ β : ℝ) : Measurable (loopSize (n := n) (i := i) θ δ β) :=
  ((continuous_const.mul (continuous_loopLen θ δ)).div_const 2).measurable

/-- The bucket weights in physical size: tents of width `w` at `k w` for `k < K`; a ramp for `k = K`. -/
def bucketW (w : ℝ) (K : ℕ) (k : Fin (K + 1)) : ℝ → ℝ :=
  if (k : ℕ) = K then fun s => min 1 (max 0 ((s - ((K : ℝ) - 1) * w) / w))
  else fun s => max 0 (1 - |s - (k : ℝ) * w| / w)

theorem continuous_bucketW (w : ℝ) (K : ℕ) (k : Fin (K + 1)) : Continuous (bucketW w K k) := by
  unfold bucketW
  split_ifs
  · exact continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const w))
  · exact continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const w))

/-- The square partition from nonnegative-part weights: `χ_i = √(W_i⁺ / Σ_j W_j⁺)`, and the indicator of
`i₀` where every weight vanishes. -/
def sqPart {X ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → X → ℝ) (i₀ : ι) (k : ι) (x : X) : ℝ :=
  if ∑ j, max 0 (W j x) = 0 then (if k = i₀ then 1 else 0)
  else Real.sqrt (max 0 (W k x) / ∑ j, max 0 (W j x))

theorem sqPart_isSqPartition {X ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → X → ℝ) (i₀ : ι) :
    IsSqPartition (sqPart W i₀) := by
  intro x
  by_cases h : ∑ j, max 0 (W j x) = 0
  · have e : ∀ k, (if k = i₀ then (1 : ℝ) else 0) ^ 2 = if k = i₀ then 1 else 0 := fun k => by
      split_ifs <;> norm_num
    simp only [sqPart, h, if_true, e, Finset.sum_ite_eq', Finset.mem_univ]
  · have hpos : 0 ≤ ∑ j, max 0 (W j x) := Finset.sum_nonneg fun j _ => le_max_left _ _
    simp only [sqPart, h, if_false]
    rw [Finset.sum_congr rfl fun k _ => Real.sq_sqrt (div_nonneg (le_max_left _ _) hpos),
      ← Finset.sum_div, div_self h]

theorem measurable_sqPart {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    {W : ι → X → ℝ} (hW : ∀ k, Measurable (W k)) (i₀ k : ι) : Measurable (sqPart W i₀ k) := by
  have hS : Measurable fun x => ∑ j, max 0 (W j x) :=
    Finset.measurable_sum _ fun j _ => measurable_const.max (hW j)
  unfold sqPart
  exact Measurable.ite (measurableSet_eq_fun hS measurable_const) measurable_const
    ((measurable_const.max (hW k)).div hS).sqrt

/-- **The loop-size partition of the slice**: `K + 1` buckets of width `w` in `loopSize`. -/
def sizePart (θ δ β w : ℝ) (K : ℕ) : Fin (K + 1) → Slice n i → ℝ :=
  sqPart (fun k V => bucketW w K k (loopSize θ δ β V)) 0

theorem sizePart_isSqPartition (θ δ β w : ℝ) (K : ℕ) :
    IsSqPartition (sizePart (n := n) (i := i) θ δ β w K) :=
  sqPart_isSqPartition _ _

theorem measurable_sizePart (θ δ β w : ℝ) (K : ℕ) (k : Fin (K + 1)) :
    Measurable (sizePart (n := n) (i := i) θ δ β w K k) :=
  measurable_sqPart (fun k => (continuous_bucketW w K k).measurable.comp (measurable_loopSize θ δ β)) _ _

/-- (ii') on the real objects: per-piece cost of `trivKN 2 β n i` on the loop-size pieces. -/
def SizePieceCost (θ δ β w : ℝ) (K n : ℕ) (i : Fin 4) (Ω : Slice n i → ℝ) (lam : ℝ)
    (f : Fin (K + 1) → ℝ) : Prop :=
  PieceCost (hSN 2 n i) (trivKN 2 β n i) (sizePart θ δ β w K) Ω lam f

/-- (iii') on the real objects: the localisation cost of the loop-size partition for `trivKN 2 β n i`. -/
def SizeLocCost (θ δ β w : ℝ) (K n : ℕ) (i : Fin 4) (g : Fin (K + 1) → ℝ) : Prop :=
  LocCost (hSN 2 n i) (trivKN 2 β n i) (sizePart (n := n) (i := i) θ δ β w K) g

/-- **The skeleton on the real zero-flux kernel**: (ii') against the ground eigenfunction and (iii') on the
loop-size pieces give the gap clause at `−2 log(1 − m/λ₀) / (n · aRun 2 β)`. The hypotheses
(ii') + (iii') + `m ≤ f_k − g_k` at `m > 0` are argued unsatisfiable on the slice (not formalised): with
the ground eigenfunction strictly positive and every size piece balanced, `nonpos_of_balanced` forces
`m ≤ 0`. So this theorem is the chain on the real objects, not a route to the gap; the surviving form is
§4. -/
theorem zeroFluxGap_of_sizePieces {β θ δ w lam m : ℝ} {K : ℕ} {κ : Type*} {g₀ : κ} {E : κ → ℝ}
    {φ : κ → Slice n i → ℝ} {ev : κ → ℝ} {f g : Fin (K + 1) → ℝ}
    (hβ : 0 < β) (hn : 0 < n) (h : EigenLevels β n i g₀ E φ ev) (hg₀ : ev g₀ = lam)
    (hm0 : 0 < m) (hml : m < lam) (hpos : ∀ j, 0 ≤ ev j)
    (hadm : ∀ j, Adm (hSN 2 n i) (trivKN 2 β n i) (φ j))
    (hf : SizePieceCost θ δ β w K n i (φ g₀) lam f) (hg : SizeLocCost θ δ β w K n i g)
    (hmin : ∀ k, m ≤ f k - g k) :
    ZeroFluxGap g₀ E (-2 * Real.log (1 - m / lam) / ((n : ℝ) * aRun 2 β)) := by
  intro j hj
  have ht : 0 < (n : ℝ) * aRun 2 β := mul_pos (Nat.cast_pos.mpr hn) (aRun_pos (by norm_num) hβ)
  have hn1 : nsq (hSN 2 n i) (φ j) = 1 := by
    unfold nsq
    simp only [sq]
    exact h.norm j
  have hq := quad_ge_of_pieces (sizePart_isSqPartition θ δ β w K) (measurable_sizePart θ δ β w K)
    (hadm j) (h.orth g₀ j (Ne.symm hj)) hf hg hmin
  have hform := form_eigen (hadm j).form_int (h.eigen j)
  unfold quad at hq
  rw [hform, hn1] at hq
  have hμ : ev j ≤ lam - m := by linarith
  have hsq : ev j ^ 2 ≤ (lam - m) ^ 2 := pow_le_pow_left₀ (hpos j) hμ 2
  have hlam0 : 0 < lam := hm0.trans hml
  have hpos1 : 0 < 1 - m / lam := by
    rw [sub_pos, div_lt_one hlam0]
    exact hml
  have hl2 : lam ^ 2 = Real.exp (-(E g₀ * ((n : ℝ) * aRun 2 β))) := by
    rw [← hg₀]
    exact h.energy g₀
  have hlm : (lam - m) ^ 2 = Real.exp (-(E g₀ * ((n : ℝ) * aRun 2 β)) + 2 * Real.log (1 - m / lam)) := by
    have e1 : lam - m = lam * (1 - m / lam) := by field_simp
    rw [e1, mul_pow, hl2, Real.exp_add, two_mul, Real.exp_add, Real.exp_log hpos1, sq]
  rw [h.energy j, hlm, Real.exp_le_exp] at hsq
  have key : -2 * Real.log (1 - m / lam) / ((n : ℝ) * aRun 2 β) ≤ E j - E g₀ := by
    rw [div_le_iff₀ ht]
    nlinarith
  linarith

end Real

end MassGap.SizePartition

#print axioms MassGap.SizePartition.form_split
#print axioms MassGap.SizePartition.quad_split
#print axioms MassGap.SizePartition.quad_ge_of_pieces
#print axioms MassGap.SizePartition.exists_partition_iff
#print axioms MassGap.SizePartition.nonpos_of_balanced
#print axioms MassGap.SizePartition.balanced_piece
#print axioms MassGap.SizePartition.quad_ge_of_local_vacua
#print axioms MassGap.SizePartition.formGap_of_local_vacua
#print axioms MassGap.SizePartition.sizePart_isSqPartition
#print axioms MassGap.SizePartition.measurable_sizePart
#print axioms MassGap.SizePartition.zeroFluxGap_of_sizePieces
