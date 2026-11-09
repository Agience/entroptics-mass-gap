import Mathlib
import MassGap.SliceTransferGap
import MassGap.SlabTransferAdjoint

/-!
# MassGap.StrongTransferGap — a gapped slice transfer at positive coupling, and what uniformity needs

The slice transfer `K = kT i T N β` is symmetric, and at `β ≥ 0` its values lie in `[a, 1]` with
`a = kTmin i T β = e^{−β M}`, `M = slabM i T = spMax + 2 tpMax = 30 |TT|` (`RectTransfer.kT_lower`,
`kT_le_one`, `kTmin_eq`, `slabM_eq`); `|TT|` is the number of transverse sites of the slice. At `β = 0`, `K = 1`,
the constant kernel, which on the product Haar probability measure is the rank-one projection onto constants
with eigenvalue `1` (`SliceTransferGap.transferGapAt_zero_coupling`, `ρ = 0`). This module builds, at each fixed slice, a gapped instance of `SliceTransferGap.TransferGapAt` (`ρ ≤ |λ|/2`) at
every `0 < β ≤ β₀(T)`, a threshold that tends to `0` as the slice grows; it proves that the per-observable time-decay form of a
uniform gap gives the gap, and names the uniform statement, which `UniformRelayStrong.uniformRelayGap` proves. Declarations are in the namespace
`MassGap.StrongTransferGap`.

## 1. The gap at a fixed slice (proved)

* `doeblin_rem` (generic, any probability space): a bounded kernel with `a ≤ k ≤ 1`, `a > 0`, and a unit
  eigenfunction `φ ≥ c₀ > 0` with eigenvalue `λ` give `a ≤ λ ≤ 1` and `|k(x, y) − λ φ(x) φ(y)| ≤ 1/a − a` at
  every `x, y`. With `s = ∫ φ`: the eigen equation gives `a s ≤ λ φ ≤ s` pointwise (`lam_phi_mem`); integrating,
  `a ≤ λ ≤ 1`; `λ = ∫ φ (λ φ) ≤ s²`; `s² ≤ 1` from `∫ (φ − s)² ≥ 0`. So `λ φ(x) φ(y)` lies in
  `[a² s²/λ, s²/λ] ⊆ [a², 1/a]`, and `k` in `[a, 1]`.
* `strong_data`: at every `β ≥ 0`, the Jentzsch top `(λ, φ)` of `JentzschKT.exists_pos_eigen_kT` satisfies
  `TransferGapAt N i T β λ φ (e^{β M} − e^{−β M})` with `e^{−β M} ≤ λ ≤ 1`. The remainder norm is bounded by its
  sup norm (`SlabKernelOperator.norm_kernelCLM_le`).
* `strong_gap_rate`: if `2 β M ≤ log(1 + e^{−x})`, then `TransferGapAt N i T β λ φ (|λ| e^{−x})`. The ratio
  is `ρ/λ ≤ e^{2 β M} − 1`.
* **`strong_gap_half`**: at every `0 ≤ β ≤ β₀(T) = log(3/2) / (2 (M + 1))`,
  `TransferGapAt N i T β λ φ (|λ|/2)`; `betaStrong_pos`: `β₀(T) > 0`. `strong_gap_centre`: the pair is the
  Jentzsch top, `λ = ‖K‖`, and `φ` is centre-invariant (`SliceTransferGap.top_of_gap`, `phi_act_kT`). This is a gapped instance at positive coupling for one slice at a time: `β₀(T) → 0` as `|TT| → ∞` (§2).

`ρ(β, T) = e^{β M} − e^{−β M} = 2 sinh(β M)`, `M = 30 |TT|`, and `ρ ≤ |λ| (e^{2 β M} − 1)`.

## 2. Uniformity in the side

The bound is not uniform (argued). `M` is extensive: for the slice `Tr n i` of `CentreSectorSeed`,
`|TT| = 2^i n³` (from `DoublingWilson.ext` and `pathV`), so `β₀(Tr n i) ≈ log(3/2)/(60 · 2^i n³) → 0`. This is the
sup-norm route, not a weakness of the estimate: `kT` is a product of `e^{−β ·}` over `O(|TT|)` plaquettes, so its
oscillation `1 − kTmin` and the sup of the remainder grow with the slice volume. Any bound through
`‖K − K₀‖`, a Hilbert–Schmidt norm, or the sup norm has the same defect.

What a uniform bound needs (proved reduction). For a symmetric bounded operator `R`, per-vector decay
`‖R^t f‖ ≤ C_f ρ^t` at every `t`, with a constant `C_f` that may depend on `f` in any way, gives `‖R f‖ ≤ ρ ‖f‖`:

* `pow_inner_symm`, `sq_norm_pow_le`: `‖R^k f‖² = ⟨f, R^{2k} f⟩ ≤ ‖f‖ ‖R^{2k} f‖`.
* `norm_apply_pow_two_le`: `‖f‖ ‖R f‖^{2^j} ≤ ‖f‖^{2^j} ‖R^{2^j} f‖` (the doubling step, iterated).
* `norm_apply_le_of_decay`: hence `‖R f‖ ≤ ρ ‖f‖`; `opNorm_le_of_decay`: `‖R‖ ≤ ρ` if this holds at every `f`;
  `opNorm_le_of_decay_dense`: at every `f` of a dense set suffices.
* `transferGapAt_of_sliceDecay`, `sliceDecay_of_transferGapAt`: on the slice, `SliceDecayAt` (the remainder's
  powers decay at rate `|λ| e^{−m}` on every `L²` vector, any prefactor) is equivalent to
  `TransferGapAt … (|λ| e^{−m})`. `uniformSliceDecay_iff`: `UniformSliceDecay N ↔ UniformRelayGap N`.

So the extensive prefactor is harmless; only the rate must be uniform in `T`. That is the form a strong-coupling
cluster expansion delivers (proved in `UniformRelayStrong`): the two-slice connected correlation on the rectangular
torus is bounded with a prefactor that grows with `|TT|` and the rate `coreRate 64 β`, independent of the
transverse extent.

What supplies it. `ContractionReads.cov_sep_strong_rec` and `KernelDecayAt` are local-box statements for the
periodic infinite-lattice state and do not reach slice observables, which read the whole transverse torus. The
time-direction bound comes instead from the cluster bound read on the rectangular Wilson torus
(`UniformRelayStrong.rect_pair_cluster`), turned into an operator bound by `UniformRelayStrong.gap_of_pairDecay`.

## 3. The uniform Prop (proved in `UniformRelayStrong`)

**`UniformRelayGap N`**: there are `β₀ > 0` and `m > 0` such that at every `0 ≤ β ≤ β₀`, every direction `i`
and every transverse extent `T`, the slice transfer has an eigenpair with `TransferGapAt N i T β λ φ (|λ| e^{−m})`.
`m` is a lattice-unit rate fixed before `T`. This is the uniform-in-`T` strong-coupling relay gap. Its equivalent
`UniformSliceDecay N` is the time-decay form. Both are proved in `UniformRelayStrong` (`uniformRelayGap`,
`uniformSliceDecay`); neither is used as a hypothesis here.

## 4. Relation to the measured rate (argued; `gapClause_strong` proved)

`SliceTransferGap.TransferGapMeasured` asks `ρ ≤ |λ| e^{−c m′}` with `c` fixed, only eventually as `β → ∞`. A
strong-coupling gap tests the per-coupling clause, never the Prop: no statement at small `β` is an instance of a
statement read along `β → ∞`. `gapClause_strong` gives that clause at side `n` whenever
`2 β M(Tr n i) ≤ log(1 + e^{−c m′})`. Whether this holds with one fixed `c` is a comparison of two rates. The
strong-coupling instance supplies `x(β, T) = −log(e^{2 β M} − 1)`, about `log(1/(2 β M))`, which grows as `β → 0`
but falls with `T` and is negative once `e^{2 β M} > 2`. `SubstrateDecode.measMass_strong` gives at
`|β| ≤ 2^{-16}` only a lower bound, `measMass ≥ log 2`, for the site-energy read (`m′` reads `tensorEnergy`, and
`m′ = ⊤` would give `m′.toReal = 0`). A fixed `c` with `c m′ ≤ x(β, T)` needs an upper bound on `m′` of the same
order as `log(1/β)`, which the tree does not have; the `T`-uniform rate is `UniformRelayGap`
(`UniformRelayStrong.uniformRelayGap`), at small `β` only. The anchor
clause of `TransferGapMeasured` is not addressed here.

## 5. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the non-uniformity of the sup-norm route and `|TT| = 2^i n³` for `Tr n i` (§2), why the tree's local box decay does not reach slice observables (§2), the measured-rate comparison (§4).
* Assumed: nothing. `UniformRelayGap` and `UniformSliceDecay` are stated and related to each other here, and proved in
`UniformRelayStrong`.

## 6. Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every slice statement | swept over `[0, β₀(T)]` in `strong_gap_half`; `β ≥ 0` elsewhere |
| `i` (direction), `T` (transverse extent) | the slice lemmas | chosen; swept in the uniform Props |
| `a = kTmin = e^{−β M}` | `doeblin_rem`, `strong_data` | derived: the least value of `kT` |
| `M = slabM i T` | the slice lemmas | derived: `spMax + 2 tpMax = 30 |TT|` |
| `λ`, `φ` | the instances | the Jentzsch top: `λ = ‖K‖`, `φ ≥ c₀ > 0` |
| `ρ` | `TransferGapAt` | `e^{β M} − e^{−β M}`, or `|λ| e^{−x}`, or `|λ|/2` |
| `x` | `strong_gap_rate` | chosen: the target rate per hop |
| `β₀(T) = log(3/2) / (2(M + 1))` | `strong_gap_half` | derived |
| `s = ∫ φ`, `c₀`, `B` | `doeblin_rem` | local: the mean, the floor and the bound of `φ` |
| `A`, `f`, `C`, `t`, `j`, `D` | the decay lemmas | generic operator, vector, prefactor, power, doubling index, dense set |
| `m` | `SliceDecayAt`, the uniform Props | the rate per hop in lattice units |
| `β₀`, `m` | `UniformRelayGap` | existential, fixed before `i` and `T` |
| `c`, `n`, `m′` | `gapClause_strong` | as in `TransferGapMeasured` |
| `N` | the type | shared with the substrate |

DERIVED (module-wide): `1` the upper value of `kT` and the normalization; `2` the square, the doubling and
`e^{2 β M}`; `3/2 = 1 + 1/2` and `1/2` the rate of `strong_gap_half`; `30 = 18 + 2 · 6` the plaquette count per
transverse site (`3 · 3` spatial pairs and `3` temporal ones, each `≤ 2`); `0` the floor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.StrongTransferGap

open MeasureTheory Filter Topology
open MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower MassGap.SlabKernelOperator
open MassGap.SliceTransferGap (TransferGapAt top_of_gap phi_act_kT int_sq_comb)
open MassGap.SliceCentreAction (Cfg Cen act)
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)

/-! ## 1. A kernel between `a` and `1` (generic) -/

section Doeblin

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The eigen equation pins `λ φ` between `a s` and `s`**, `s = ∫ φ`, for a kernel with values in `[a, 1]`
and a nonnegative eigenfunction. DERIVED: `1` the upper value of the kernel. -/
theorem lam_phi_mem {k : X → X → ℝ} (hk : Bdd k) {a : ℝ} (hlo : ∀ x y, a ≤ k x y)
    (hhi : ∀ x y, k x y ≤ 1) {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
    (hφ0 : ∀ x, 0 ≤ φ x) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (z : X) :
    a * ∫ y, φ y ∂μ ≤ c * φ z ∧ c * φ z ≤ ∫ y, φ y ∂μ := by
  obtain ⟨Ck, hCk⟩ := hk.bdd
  have hi : Integrable (fun y => k z y * φ y) μ := integrable_mul_of_bdd (hk.row z) hφm (hCk z) hφb
  have hiφ : Integrable φ μ := integrable_of_bdd hφm hφb
  rw [← heig z]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hiφ.const_mul a) hi (fun y => mul_le_mul_of_nonneg_right (hlo z y) (hφ0 y))
  · refine integral_mono hi hiφ (fun y => ?_)
    have := mul_le_mul_of_nonneg_right (hhi z y) (hφ0 y)
    simpa using this

/-- **The Doeblin bound on the remainder**: a bounded kernel with values in `[a, 1]`, `a > 0`, and a unit
eigenfunction `φ ≥ c₀ > 0` with eigenvalue `λ` give `a ≤ λ ≤ 1` and `|k − λ φ⊗φ| ≤ 1/a − a` pointwise.
DERIVED: `1` the upper value and the normalization; `2` the square in `∫ (φ − s)² ≥ 0`. -/
theorem doeblin_rem {k : X → X → ℝ} (hk : Bdd k) {a : ℝ} (ha0 : 0 < a) (hlo : ∀ x y, a ≤ k x y)
    (hhi : ∀ x y, k x y ≤ 1) {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hφlow : ∀ x, c₀ ≤ φ x) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) :
    a ≤ c ∧ c ≤ 1 ∧ 0 ≤ 1 / a - a ∧ ∀ x y, |rem k c φ x y| ≤ 1 / a - a := by
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => hc₀.le.trans (hφlow x)
  have hiφ : Integrable φ μ := integrable_of_bdd hφm hφb
  have hpt := fun z => lam_phi_mem (μ := μ) hk hlo hhi hφm hφb hφ0 heig z
  have hs0 : c₀ ≤ ∫ y, φ y ∂μ := by
    have := integral_mono (integrable_const c₀) hiφ (fun x => hφlow x)
    simpa using this
  have hspos : 0 < ∫ y, φ y ∂μ := hc₀.trans_le hs0
  have hconst : ∀ r : ℝ, ∫ _z : X, r ∂μ = r := fun r => by simp
  -- integrate the pointwise bounds
  have hlo_int : a * ∫ y, φ y ∂μ ≤ c * ∫ y, φ y ∂μ := by
    have h := integral_mono (integrable_const (a * ∫ y, φ y ∂μ)) (hiφ.const_mul c) (fun z => (hpt z).1)
    rwa [hconst, integral_const_mul] at h
  have hhi_int : c * ∫ y, φ y ∂μ ≤ ∫ y, φ y ∂μ := by
    have h := integral_mono (hiφ.const_mul c) (integrable_const (∫ y, φ y ∂μ)) (fun z => (hpt z).2)
    rwa [hconst, integral_const_mul] at h
  have hac : a ≤ c := le_of_mul_le_mul_right hlo_int hspos
  have hc1 : c ≤ 1 := by
    have h : c * ∫ y, φ y ∂μ ≤ 1 * ∫ y, φ y ∂μ := by rw [one_mul]; exact hhi_int
    exact le_of_mul_le_mul_right h hspos
  have hc0 : 0 < c := ha0.trans_le hac
  -- `λ ≤ s²`
  have hcs2 : c ≤ (∫ y, φ y ∂μ) * (∫ y, φ y ∂μ) := by
    have e1 : ∫ x, φ x * (c * φ x) ∂μ = c := by
      have : (fun x => φ x * (c * φ x)) = fun x => c * φ x ^ 2 := by funext x; ring
      rw [this, integral_const_mul, hφ1, mul_one]
    have e2 : ∫ x, φ x * (∫ y, φ y ∂μ) ∂μ = (∫ y, φ y ∂μ) * (∫ y, φ y ∂μ) := integral_mul_const _ _
    have hi2 : Integrable (fun x => φ x * (c * φ x)) μ :=
      integrable_mul_of_bdd hφm (measurable_const.mul hφm) hφb (Cg := |c| * B)
        (fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg c))
    have h := integral_mono hi2 (hiφ.mul_const (∫ y, φ y ∂μ))
      (fun x => mul_le_mul_of_nonneg_left (hpt x).2 (hφ0 x))
    rwa [e1, e2] at h
  -- `s² ≤ 1`
  have hs2 : (∫ y, φ y ∂μ) * (∫ y, φ y ∂μ) ≤ 1 := by
    have h := int_sq_comb (μ := μ) (φ := fun _ : X => (1 : ℝ)) (ψ := φ) measurable_const hφm
      (Bφ := 1) (fun _ => by norm_num) hφb 1 (-(∫ y, φ y ∂μ))
    have h0 : 0 ≤ ∫ x, (1 * φ x + -(∫ y, φ y ∂μ) * 1) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have i1 : ∫ x, φ x * (1 : ℝ) ∂μ = ∫ y, φ y ∂μ := by simp
    have i2 : ∫ _x : X, (1 : ℝ) ^ 2 ∂μ = 1 := by simp
    have h' := h0.trans_eq h
    rw [hφ1, i1, i2] at h'
    nlinarith
  have hia : 1 ≤ 1 / a := by rw [le_div_iff₀ ha0]; linarith
  have hinv : a * (1 / a) = 1 := by field_simp
  have h1a : a ≤ 1 := hac.trans hc1
  have hkey : 1 - a * a ≤ 1 / a - a := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1a) (sub_nonneg.2 (h1a.trans hia))]
  refine ⟨hac, hc1, by linarith, fun x y => ?_⟩
  obtain ⟨hu1, hu2⟩ := hpt x
  obtain ⟨hv1, hv2⟩ := hpt y
  generalize ∫ y, φ y ∂μ = s at hu1 hu2 hv1 hv2 hcs2 hs2 hspos
  have hφx := hφ0 x
  have hφy := hφ0 y
  have hP0 : 0 ≤ c * φ x * φ y := mul_nonneg (mul_nonneg hc0.le hφx) hφy
  have hcP : c * (c * φ x * φ y) = (c * φ x) * (c * φ y) := by ring
  have hus : 0 ≤ a * s := mul_nonneg ha0.le hspos.le
  have huv_le : (c * φ x) * (c * φ y) ≤ s * s :=
    mul_le_mul hu2 hv2 (mul_nonneg hc0.le hφy) hspos.le
  have huv_ge : (a * s) * (a * s) ≤ (c * φ x) * (c * φ y) :=
    mul_le_mul hu1 hv1 hus (mul_nonneg hc0.le hφx)
  have hPup : c * φ x * φ y ≤ 1 / a := by
    rw [le_div_iff₀ ha0]
    calc c * φ x * φ y * a ≤ c * φ x * φ y * c := mul_le_mul_of_nonneg_left hac hP0
      _ = (c * φ x) * (c * φ y) := by ring
      _ ≤ s * s := huv_le
      _ ≤ 1 := hs2
  have hPlo : a * a ≤ c * φ x * φ y := by
    have h1 : c * (a * a) ≤ c * (c * φ x * φ y) := by
      calc c * (a * a) ≤ (s * s) * (a * a) := mul_le_mul_of_nonneg_right hcs2 (mul_self_nonneg a)
        _ = (a * s) * (a * s) := by ring
        _ ≤ (c * φ x) * (c * φ y) := huv_ge
        _ = c * (c * φ x * φ y) := hcP.symm
    exact le_of_mul_le_mul_left h1 hc0
  have hk1 := hhi x y
  have hk0 := hlo x y
  show |k x y - c * φ x * φ y| ≤ 1 / a - a
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Doeblin

/-! ## 2. The slice transfer at small coupling -/

section Slice

variable {N : ℕ} [NeZero N] {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

variable (i T) in
/-- **The extensive weight of one slice**: `M = spMax + 2 tpMax`, so `kTmin = e^{−β M}`. DERIVED: `2` the coefficient of `gk`'s weight `e^{−2β tp}` (both orientations of a temporal plaquette). -/
def slabM : ℝ := spMax i T + 2 * tpMax i T

theorem slabM_nonneg : 0 ≤ slabM i T := by
  unfold slabM spMax tpMax; positivity

/-- Three transverse directions. DERIVED: `3 = 4 − 1`. -/
theorem card_ne : Fintype.card {j : Fin 4 // j ≠ i} = 3 := by
  fin_cases i <;> rfl

/-- **`M = 30 |TT|`**: `9` ordered spatial direction pairs and `3` temporal ones per transverse site, each of
action at most `2`. DERIVED: `30 = 2 · 9 + 2 · 2 · 3`. -/
theorem slabM_eq : slabM i T = 30 * (Fintype.card (TT i T) : ℝ) := by
  unfold slabM spMax tpMax
  simp only [card_ne]
  push_cast
  ring

/-- **The floor of the slice transfer is `e^{−β M}`.** DERIVED: no numeral. -/
theorem kTmin_eq : kTmin i T β = Real.exp (-(β * slabM i T)) := by
  unfold kTmin slabM
  rw [← Real.exp_add]
  congr 1
  ring

/-- Monotonicity of the gap statement in `ρ`. DERIVED: no numeral. -/
theorem transferGapAt_mono {lam ρ ρ' : ℝ} {φ : Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ≤ ρ') : TransferGapAt N i T β lam φ ρ' := by
  obtain ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, hR⟩ := h
  exact ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, hR.trans hρ⟩

/-- **The slice transfer at any `β ≥ 0`, with an explicit remainder bound**: the Jentzsch top `(λ, φ)` has
`‖K − λ φ⊗φ‖ ≤ e^{β M} − e^{−β M}` and `e^{−β M} ≤ λ ≤ 1`. DERIVED: `1` the upper value of `kT`. -/
theorem strong_data (hβ : 0 ≤ β) :
    ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ,
      TransferGapAt N i T β lam φ (Real.exp (β * slabM i T) - Real.exp (-(β * slabM i T))) ∧
        Real.exp (-(β * slabM i T)) ≤ lam ∧ lam ≤ 1 := by
  obtain ⟨-, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen_kT (μ := i) (T := T) (N := N) (NeZero.ne N) hβ
  have hk : Bdd (kT i T N β) := bdd_kT (NeZero.ne N) hβ
  obtain ⟨hac, hc1, hρ0, hrem⟩ := doeblin_rem (μ := hS i T N) hk (kTmin_pos (μ := i) (T := T) β)
    (kT_lower (NeZero.ne N) hβ) (kT_le_one (NeZero.ne N) hβ) hφm hφb hc₀ hlow hφ1 heig
  have ea : kTmin i T β = Real.exp (-(β * slabM i T)) := kTmin_eq
  have eρ : 1 / kTmin i T β - kTmin i T β
      = Real.exp (β * slabM i T) - Real.exp (-(β * slabM i T)) := by
    rw [ea, Real.exp_neg, one_div, inv_inv]
  rw [eρ] at hρ0 hrem
  rw [ea] at hac
  exact ⟨_, φ, ⟨hφm, ⟨_, hφb⟩, hφ1, (lt_of_lt_of_le (Real.exp_pos _) hac).ne', heig, _,
    (Bdd.rem hk hφm hφb).meas, hρ0, hrem, norm_kernelCLM_le _ _ _ _ _ _ _⟩, hac, hc1⟩

/-- **The gap at a target rate `x`**: if `2 β M ≤ log(1 + e^{−x})`, the Jentzsch top has remainder norm at
most `|λ| e^{−x}`. DERIVED: `1`, `2` in `e^{2 β M} − 1`. -/
theorem strong_gap_rate (hβ : 0 ≤ β) {x : ℝ}
    (hx : 2 * (β * slabM i T) ≤ Real.log (1 + Real.exp (-x))) :
    ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ,
      TransferGapAt N i T β lam φ (|lam| * Real.exp (-x)) ∧
        Real.exp (-(β * slabM i T)) ≤ lam ∧ lam ≤ 1 := by
  obtain ⟨lam, φ, h, hlo, hhi⟩ := strong_data (N := N) (i := i) (T := T) hβ
  refine ⟨lam, φ, transferGapAt_mono h ?_, hlo, hhi⟩
  have hy0 : 0 ≤ β * slabM i T := mul_nonneg hβ slabM_nonneg
  have e : Real.exp (β * slabM i T) - Real.exp (-(β * slabM i T))
      = Real.exp (-(β * slabM i T)) * (Real.exp (2 * (β * slabM i T)) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    have : -(β * slabM i T) + 2 * (β * slabM i T) = β * slabM i T := by ring
    rw [this]
  have h2 : Real.exp (2 * (β * slabM i T)) ≤ 1 + Real.exp (-x) := by
    calc Real.exp (2 * (β * slabM i T)) ≤ Real.exp (Real.log (1 + Real.exp (-x))) :=
          Real.exp_le_exp.mpr hx
      _ = 1 + Real.exp (-x) := Real.exp_log (by positivity)
  have h3 : 0 ≤ Real.exp (2 * (β * slabM i T)) - 1 := by
    have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * (β * slabM i T))
    linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le (Real.exp_pos _) hlo
  rw [e, abs_of_pos hlam0]
  calc Real.exp (-(β * slabM i T)) * (Real.exp (2 * (β * slabM i T)) - 1)
      ≤ lam * (Real.exp (2 * (β * slabM i T)) - 1) := mul_le_mul_of_nonneg_right hlo h3
    _ ≤ lam * Real.exp (-x) := mul_le_mul_of_nonneg_left (by linarith) hlam0.le

variable (i T) in
/-- **The strong-coupling threshold of one slice**: `β₀(T) = log(3/2) / (2 (M + 1))`. DERIVED: `3/2 = 1 + 1/2`;
`2` the square `e^{2 β M} = (1/a)/a` in the ratio `ρ/λ`; `1` keeps the denominator positive at `M = 0`. -/
def betaStrong : ℝ := Real.log (3 / 2) / (2 * (slabM i T + 1))

theorem betaStrong_pos : 0 < betaStrong i T := by
  unfold betaStrong
  have h1 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have h2 : 0 < 2 * (slabM i T + 1) := by linarith [slabM_nonneg (i := i) (T := T)]
  positivity

/-- **The first gapped slice transfer at positive coupling**: at every `0 ≤ β ≤ β₀(T)` the Jentzsch top has
remainder norm at most `|λ|/2`. DERIVED: `2` the rate `e^{−log 2} = 1/2`; `3/2`. -/
theorem strong_gap_half (hβ : 0 ≤ β) (hβ0 : β ≤ betaStrong i T) :
    ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ, TransferGapAt N i T β lam φ (|lam| / 2) ∧
      Real.exp (-(β * slabM i T)) ≤ lam ∧ lam ≤ 1 := by
  have hM := slabM_nonneg (i := i) (T := T)
  have hden : 0 < 2 * (slabM i T + 1) := by linarith
  have h1 : β * (2 * (slabM i T + 1)) ≤ Real.log (3 / 2) := by
    have := mul_le_mul_of_nonneg_right hβ0 hden.le
    rwa [betaStrong, div_mul_cancel₀ _ hden.ne'] at this
  have hx : 2 * (β * slabM i T) ≤ Real.log (1 + Real.exp (-Real.log 2)) := by
    have e : 1 + Real.exp (-Real.log 2) = 3 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [e]
    nlinarith
  obtain ⟨lam, φ, h, hlo, hhi⟩ := strong_gap_rate (N := N) (i := i) (T := T) hβ hx
  refine ⟨lam, φ, ?_, hlo, hhi⟩
  have e2 : |lam| * Real.exp (-Real.log 2) = |lam| / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; ring
  rwa [e2] at h

/-- **The strong-coupling pair is the Jentzsch top and is centre-invariant**: `λ = ‖K‖` and
`φ (act g x) = φ x`, through `SliceTransferGap.top_of_gap` and `phi_act_kT`. DERIVED: `2` the rate. -/
theorem strong_gap_centre (hβ : 0 ≤ β) (hβ0 : β ≤ betaStrong i T) :
    ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ, TransferGapAt N i T β lam φ (|lam| / 2) ∧
      lam = ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one
        (abs_kT_le (NeZero.ne N) hβ) (hS i T N) (hS i T N)‖ ∧
      ∀ (g : Cen i N) (x : Cfg i T N), φ (act g x) = φ x := by
  obtain ⟨lam, φ, h, hlo, -⟩ := strong_gap_half (N := N) hβ hβ0
  have hlam0 : 0 < lam := lt_of_lt_of_le (Real.exp_pos _) hlo
  have hρ : (|lam| / 2) ^ 2 < lam ^ 2 := by
    rw [abs_of_pos hlam0]; nlinarith
  exact ⟨lam, φ, h, (top_of_gap hβ h hρ).2, fun g x => phi_act_kT hβ h hρ g x⟩

/-- **The gap clause of `TransferGapMeasured` at one coupling and one side**, from the strong-coupling
instance, whenever `2 β M(Tr n i) ≤ log(1 + e^{−c m′})`. This is the per-coupling clause, not an instance of the
Prop. DERIVED: `2`, `1`. -/
theorem gapClause_strong {c : ℝ} (n : ℕ) (hβ : 0 ≤ β)
    (hx : 2 * (β * slabM i (CentreSectorSeed.Tr n i))
      ≤ Real.log (1 + Real.exp (-(c * (measMassOf (periodicState (NeZero.ne N) β) tensorEnergy).toReal)))) :
    ∃ lam : ℝ, ∃ φ : Cfg i (CentreSectorSeed.Tr n i) N → ℝ, ∃ ρ : ℝ,
      TransferGapAt N i (CentreSectorSeed.Tr n i) β lam φ ρ ∧
        ρ ≤ |lam| * Real.exp (-(c * (measMassOf (periodicState (NeZero.ne N) β) tensorEnergy).toReal)) := by
  obtain ⟨lam, φ, h, -, -⟩ := strong_gap_rate (N := N) (i := i) (T := CentreSectorSeed.Tr n i) hβ hx
  exact ⟨lam, φ, _, h, le_rfl⟩

end Slice

/-! ## 3. Per-vector time decay gives the operator bound (generic) -/

section Decay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Powers of a symmetric operator are symmetric. DERIVED: `1` the step. -/
theorem pow_inner_symm {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (k : ℕ)
    (u v : E) : inner ℝ ((A ^ k) u) v = inner ℝ u ((A ^ k) v) := by
  induction k generalizing u v with
  | zero => simp
  | succ k ih =>
    calc inner ℝ ((A ^ (k + 1)) u) v = inner ℝ ((A ^ k) (A u)) v := by
          rw [pow_succ, mul_apply_eq_comp]
      _ = inner ℝ (A u) ((A ^ k) v) := ih _ _
      _ = inner ℝ u (A ((A ^ k) v)) := hA _ _
      _ = inner ℝ u ((A ^ (k + 1)) v) := by rw [pow_succ', mul_apply_eq_comp]

/-- **`‖A^k f‖² ≤ ‖f‖ ‖A^{2k} f‖`** for symmetric `A`. DERIVED: `2` the square. -/
theorem sq_norm_pow_le {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (k : ℕ)
    (f : E) : ‖(A ^ k) f‖ ^ 2 ≤ ‖f‖ * ‖(A ^ (2 * k)) f‖ := by
  rw [← real_inner_self_eq_norm_sq, pow_inner_symm hA, two_mul, pow_add, mul_apply_eq_comp]
  exact real_inner_le_norm _ _

/-- **The doubling step, iterated**: `‖f‖ ‖A f‖^{2^j} ≤ ‖f‖^{2^j} ‖A^{2^j} f‖`. DERIVED: `2` the doubling. -/
theorem norm_apply_pow_two_le {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (f : E) (j : ℕ) : ‖f‖ * ‖A f‖ ^ (2 ^ j) ≤ ‖f‖ ^ (2 ^ j) * ‖(A ^ (2 ^ j)) f‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases (norm_nonneg f).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]; positivity
    · have key := sq_norm_pow_le hA (2 ^ j) f
      have e : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
      rw [e] at key
      have h1 := pow_le_pow_left₀ (by positivity) ih 2
      have ea : ‖A f‖ ^ (2 ^ (j + 1)) = (‖A f‖ ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
      have eb : ‖f‖ ^ (2 ^ (j + 1)) = (‖f‖ ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [ea, eb]
      refine le_of_mul_le_mul_left ?_ hpos
      calc ‖f‖ * (‖f‖ * (‖A f‖ ^ 2 ^ j) ^ 2) = (‖f‖ * ‖A f‖ ^ 2 ^ j) ^ 2 := by ring
        _ ≤ (‖f‖ ^ 2 ^ j * ‖(A ^ 2 ^ j) f‖) ^ 2 := h1
        _ = (‖f‖ ^ 2 ^ j) ^ 2 * ‖(A ^ 2 ^ j) f‖ ^ 2 := by ring
        _ ≤ (‖f‖ ^ 2 ^ j) ^ 2 * (‖f‖ * ‖(A ^ 2 ^ (j + 1)) f‖) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = ‖f‖ * ((‖f‖ ^ 2 ^ j) ^ 2 * ‖(A ^ 2 ^ (j + 1)) f‖) := by ring

/-- **Per-vector decay at rate `ρ` bounds one application**: for symmetric `A`, if `‖A^t f‖ ≤ C ρ^t` at
every `t` (any `C`), then `‖A f‖ ≤ ρ ‖f‖`. DERIVED: `2` the doubling; `0`, `1` the first power. -/
theorem norm_apply_le_of_decay {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {ρ : ℝ} (hρ : 0 ≤ ρ) {f : E} {C : ℝ} (hC : ∀ t : ℕ, ‖(A ^ t) f‖ ≤ C * ρ ^ t) :
    ‖A f‖ ≤ ρ * ‖f‖ := by
  by_contra hlt
  push Not at hlt
  have hF : 0 < ‖f‖ := by
    rcases (norm_nonneg f).eq_or_lt with h0 | h0
    · have hf0 : f = 0 := norm_eq_zero.mp h0.symm
      simp [hf0] at hlt
    · exact h0
  have hbound : ∀ j : ℕ, ‖f‖ * ‖A f‖ ^ (2 ^ j) ≤ C * (ρ * ‖f‖) ^ (2 ^ j) := by
    intro j
    calc ‖f‖ * ‖A f‖ ^ (2 ^ j) ≤ ‖f‖ ^ (2 ^ j) * ‖(A ^ (2 ^ j)) f‖ := norm_apply_pow_two_le hA f j
      _ ≤ ‖f‖ ^ (2 ^ j) * (C * ρ ^ (2 ^ j)) := mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = C * (ρ * ‖f‖) ^ (2 ^ j) := by rw [mul_pow]; ring
  rcases hρ.eq_or_lt with hρ0 | hρpos
  · have h := hbound 0
    rw [pow_zero, pow_one, pow_one, ← hρ0, zero_mul, mul_zero] at h
    rw [← hρ0, zero_mul] at hlt
    exact absurd h (not_le.mpr (mul_pos hF hlt))
  · have hr : 0 < ρ * ‖f‖ := mul_pos hρpos hF
    have hq : 1 < ‖A f‖ / (ρ * ‖f‖) := by rw [one_lt_div hr]; exact hlt
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hq).comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℕ) < 2))
    obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop (C / ‖f‖)).exists
    have h := hbound j
    simp only [Function.comp_apply] at hj
    rw [div_pow, lt_div_iff₀ (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hF] at hj
    linarith

/-- **Per-vector decay at every vector bounds the operator**: `‖A‖ ≤ ρ`. DERIVED: no numeral. -/
theorem opNorm_le_of_decay {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ f : E, ∃ C : ℝ, ∀ t : ℕ, ‖(A ^ t) f‖ ≤ C * ρ ^ t) : ‖A‖ ≤ ρ :=
  A.opNorm_le_bound hρ fun f => by
    obtain ⟨C, hC⟩ := h f
    exact norm_apply_le_of_decay hA hρ hC

/-- **Per-vector decay on a dense set bounds the operator**: `‖A‖ ≤ ρ`. The bound `‖A f‖ ≤ ρ ‖f‖` is a closed
condition. DERIVED: no numeral. -/
theorem opNorm_le_of_decay_dense {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {ρ : ℝ} (hρ : 0 ≤ ρ) {D : Set E} (hD : Dense D)
    (h : ∀ f ∈ D, ∃ C : ℝ, ∀ t : ℕ, ‖(A ^ t) f‖ ≤ C * ρ ^ t) : ‖A‖ ≤ ρ := by
  refine A.opNorm_le_bound hρ fun f => ?_
  have hS : IsClosed {g : E | ‖A g‖ ≤ ρ * ‖g‖} :=
    isClosed_le (continuous_norm.comp A.continuous) (continuous_const.mul continuous_norm)
  have hsub : D ⊆ {g : E | ‖A g‖ ≤ ρ * ‖g‖} := fun g hg => by
    obtain ⟨C, hC⟩ := h g hg
    exact norm_apply_le_of_decay hA hρ hC
  have hcl := closure_minimal hsub hS
  rw [hD.closure_eq] at hcl
  exact hcl (Set.mem_univ f)

/-- `‖A^t f‖ ≤ ‖A‖^t ‖f‖`. DERIVED: `1` the step. -/
theorem norm_pow_apply_le (A : E →L[ℝ] E) (f : E) (t : ℕ) : ‖(A ^ t) f‖ ≤ ‖A‖ ^ t * ‖f‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ' A, pow_succ' ‖A‖, mul_apply_eq_comp, mul_assoc]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg A))

end Decay

/-! ## 4. The uniform statement -/

section Uniform

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **Per-vector time decay of the slice remainder**: `φ` is a bounded measurable unit eigenfunction of
`K = kT` with eigenvalue `λ ≠ 0`, and on every `L²` vector `f` the remainder's powers decay at rate
`|λ| e^{−m}`, with a prefactor `C_f` that may depend on `f`. DERIVED: `1` the normalization. -/
def SliceDecayAt (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β lam : ℝ) (φ : Cfg i T N → ℝ) (m : ℝ) :
    Prop :=
  Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ lam ≠ 0 ∧
    (∀ z, ∫ y, kT i T N β z y * φ y ∂(hS i T N) = lam * φ z) ∧
    ∃ C : ℝ, ∃ hm : Measurable (Function.uncurry (rem (kT i T N β) lam φ)), ∃ hC0 : 0 ≤ C,
      ∃ hb : ∀ x y, |rem (kT i T N β) lam φ x y| ≤ C,
        ∀ f : Lp ℝ 2 (hS i T N), ∃ Cf : ℝ, ∀ t : ℕ,
          ‖((kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N)) ^ t) f‖
            ≤ Cf * (|lam| * Real.exp (-m)) ^ t

/-- **Per-vector decay gives the transfer gap** at rate `|λ| e^{−m}`. DERIVED: no numeral. -/
theorem transferGapAt_of_sliceDecay {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β lam m : ℝ}
    {φ : Cfg i T N → ℝ} (h : SliceDecayAt N i T β lam φ m) :
    TransferGapAt N i T β lam φ (|lam| * Real.exp (-m)) := by
  obtain ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, hdec⟩ := h
  refine ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, ?_⟩
  have hsym : ∀ x y, rem (kT i T N β) lam φ x y = rem (kT i T N β) lam φ y x := by
    intro x y
    simp only [MassGap.KernelPower.rem]
    rw [kT_symm β x y]
    ring
  have hA : ∀ u v, inner ℝ (kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N) u) v
      = inner ℝ u (kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N) v) :=
    fun u v => (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ C hm hC0 hb (hS i T N)
      hsym).isSymmetric u v
  exact opNorm_le_of_decay hA (by positivity) hdec

/-- **The transfer gap gives per-vector decay**, with `C_f = ‖f‖`. DERIVED: no numeral. -/
theorem sliceDecay_of_transferGapAt {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β lam ρ m : ℝ}
    {φ : Cfg i T N → ℝ} (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ≤ |lam| * Real.exp (-m)) :
    SliceDecayAt N i T β lam φ m := by
  obtain ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, hR⟩ := h
  refine ⟨h1, h2, h3, h4, h5, C, hm, hC0, hb, fun f => ⟨‖f‖, fun t => ?_⟩⟩
  calc _ ≤ ‖kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ^ t * ‖f‖ :=
        norm_pow_apply_le _ _ _
    _ ≤ (|lam| * Real.exp (-m)) ^ t * ‖f‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hR.trans hρ) t) (norm_nonneg _)
    _ = ‖f‖ * (|lam| * Real.exp (-m)) ^ t := mul_comm _ _

variable (N) in
/-- **The uniform-in-`T` strong-coupling relay gap** (proved: `UniformRelayStrong.uniformRelayGap`): there are `β₀ > 0` and a
lattice-unit rate `m > 0` such that at every `0 ≤ β ≤ β₀`, every direction and every transverse extent, the
slice transfer has an eigenpair with remainder norm at most `|λ| e^{−m}`. DERIVED: `0`. -/
def UniformRelayGap : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ m : ℝ, 0 < m ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
    ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ), ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ,
      TransferGapAt N i T β lam φ (|lam| * Real.exp (-m))

variable (N) in
/-- **The time-decay form of the uniform relay gap** (proved: `UniformRelayStrong.uniformSliceDecay`): the same quantifiers, with
per-vector decay of the remainder at rate `|λ| e^{−m}` and any prefactor. DERIVED: `0`. -/
def UniformSliceDecay : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ m : ℝ, 0 < m ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
    ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ), ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ,
      SliceDecayAt N i T β lam φ m

/-- **The time-decay form is the uniform relay gap**: the prefactor is free, the rate is all. DERIVED: no
numeral. -/
theorem uniformSliceDecay_iff : UniformSliceDecay N ↔ UniformRelayGap N := by
  constructor
  · rintro ⟨β₀, hβ₀, m, hm, h⟩
    refine ⟨β₀, hβ₀, m, hm, fun β hβ hβ₀' i T => ?_⟩
    obtain ⟨lam, φ, hd⟩ := h β hβ hβ₀' i T
    exact ⟨lam, φ, transferGapAt_of_sliceDecay hd⟩
  · rintro ⟨β₀, hβ₀, m, hm, h⟩
    refine ⟨β₀, hβ₀, m, hm, fun β hβ hβ₀' i T => ?_⟩
    obtain ⟨lam, φ, hd⟩ := h β hβ hβ₀' i T
    exact ⟨lam, φ, sliceDecay_of_transferGapAt hd le_rfl⟩

/-- **At one slice the uniform statement's clause holds at a `T`-dependent coupling**: for every `T` there is
`β₀(T) > 0` below which the clause holds with `m = log 2`. The threshold is `log(3/2)/(2(30 |TT| + 1))`, so this
does not give `UniformRelayGap`. DERIVED: `2` the rate `e^{−log 2} = 1/2`. -/
theorem relayGap_fixed_slice (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) :
    0 < betaStrong i T ∧ ∀ β : ℝ, 0 ≤ β → β ≤ betaStrong i T →
      ∃ lam : ℝ, ∃ φ : Cfg i T N → ℝ, TransferGapAt N i T β lam φ (|lam| * Real.exp (-Real.log 2)) := by
  refine ⟨betaStrong_pos, fun β hβ hβ0 => ?_⟩
  obtain ⟨lam, φ, h, -, -⟩ := strong_gap_half (N := N) hβ hβ0
  refine ⟨lam, φ, ?_⟩
  have e2 : |lam| * Real.exp (-Real.log 2) = |lam| / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; ring
  rw [e2]; exact h

end Uniform

end MassGap.StrongTransferGap

end

#print axioms MassGap.StrongTransferGap.lam_phi_mem
#print axioms MassGap.StrongTransferGap.doeblin_rem
#print axioms MassGap.StrongTransferGap.slabM_nonneg
#print axioms MassGap.StrongTransferGap.card_ne
#print axioms MassGap.StrongTransferGap.slabM_eq
#print axioms MassGap.StrongTransferGap.kTmin_eq
#print axioms MassGap.StrongTransferGap.transferGapAt_mono
#print axioms MassGap.StrongTransferGap.strong_data
#print axioms MassGap.StrongTransferGap.strong_gap_rate
#print axioms MassGap.StrongTransferGap.betaStrong_pos
#print axioms MassGap.StrongTransferGap.strong_gap_half
#print axioms MassGap.StrongTransferGap.strong_gap_centre
#print axioms MassGap.StrongTransferGap.gapClause_strong
#print axioms MassGap.StrongTransferGap.pow_inner_symm
#print axioms MassGap.StrongTransferGap.sq_norm_pow_le
#print axioms MassGap.StrongTransferGap.norm_apply_pow_two_le
#print axioms MassGap.StrongTransferGap.norm_apply_le_of_decay
#print axioms MassGap.StrongTransferGap.opNorm_le_of_decay
#print axioms MassGap.StrongTransferGap.opNorm_le_of_decay_dense
#print axioms MassGap.StrongTransferGap.norm_pow_apply_le
#print axioms MassGap.StrongTransferGap.transferGapAt_of_sliceDecay
#print axioms MassGap.StrongTransferGap.sliceDecay_of_transferGapAt
#print axioms MassGap.StrongTransferGap.uniformSliceDecay_iff
#print axioms MassGap.StrongTransferGap.relayGap_fixed_slice
