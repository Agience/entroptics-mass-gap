import Mathlib
import MassGap.FocusFeed
import MassGap.LoopsGenerate
import MassGap.BlockLipschitz
import MassGap.TensionFloor
import MassGap.GlueballArea

/-!
# MassGap.ScaleControl — one input for the zero-flux half (T) at `SU(2)`

`ScaleControlAt c c' σ δ α V D B t₀ Cc ℓ` is a single `Prop` (a structure) at `SU(2)`: constants fixed in the zoom
and, eventually in `β`, at every power-of-two side `n ≥ 2` with physical extent `n a ∈ [2ℓ, 5ℓ]` and every step
`i`, a `SliceControl` record on the real objects of that slice. `ScaleControl ℓ` is its existential over the
constants together with the positivity of the resulting rate. From it:

* **`zeroFluxGap_of_sliceControl`**: one record gives `ZeroFluxGap g₀ E (diagRate c c' σ δ (n a))` on that slice,
  through `FocusFeed.zeroFluxGap_of_kernelNear_bridge`. (E1) is not a field: it is supplied by
  `LoopsGenerate.excited_mem_closure_loops`. `KernelNear` at the focal boxes is not a field: it is produced from
  the block contraction by `kernelNear_of_blockContract` (`BlockLipschitz.kernelNear_of_lip`).
* **`diagRate_eq`, `diagRate_mono`**: `diagRate c c' σ δ t = √(c c' σ) + c σ δ/2 + 2 log(1 − e^{−c σ δ t/4})/t`,
  nondecreasing in `t > 0`. So the rates on the window are all at least `m = diagRate c c' σ δ (2ℓ)`: the gap is
  uniform in the zoom (`zeroFluxGap_mono`).
* **`uniformGlueball_of_scaleControlAt`**: `GlueballArea.UniformGlueball 2 m t₀ Cc ℓ`.
* **`hiddenCostAt_of_scaleControlAt`**: `ObserverTheory.HiddenCostAt 2 m (2 Cc e^{m t₀}) ℓ`, via
  `GlueballArea.hiddenCostAt_of_uniformGlueball`.
* **`hiddenCostAt_of_scaleControl`**: `ScaleControl ℓ` gives `∃ σ A, 0 < σ ∧ HiddenCostAt 2 σ A ℓ`.
* **`gram_of_orthonormal`**: an orthonormal family satisfies the Gram clause with `λ = 1`.

## The fields, classified

Constants of `ScaleControlAt` (`c, c', σ, δ` the shell rate; `α, V, D, B` the block contraction; `t₀, Cc` the
count) carry sign conditions only (bookkeeping). Per slice, `SliceControl`:

* **Bookkeeping, formalisation-open (not physics).** `levels`, `meas`: an orthonormal family of measurable
  eigenfunctions of `trivKN 2 β n i` exhausting both traces (`TensionFloor.EigenLevels`). Existence is the
  Hilbert–Schmidt spectral theorem for the symmetric bounded kernel; not proved in the tree.
* **Bookkeeping (dischargeable).** `C, kmeas, C0, kbd`: a bound of the kernel (`CentreSectorSeedN.bdd_trivKN`
  gives one at `β ≥ 0`). `R, R_mono, R_reach, R_pos, R_step`: radii (`R k = (k + 1) δ` qualifies when `δ > 0`;
  argued, not built here). `κ, v, span`: a finite family spanning each shell (argued: shells are spanned by finitely
  many projected loop states on the finite torus, `FocusFeed.shell_succ_eq_span`; finiteness of the loop set is
  not built). `lam, lam_pos, gram`: for an orthonormal `v k` it holds with `λ = 1` (`gram_of_orthonormal`), so the
  Gram clause carries no content once a finite spanning family exists (replaced by an orthonormal basis of the
  shell's span, on which `bridge` and `rate` are then stated); its cost is moved into `#κ_k`.
* **Physics, open.** `contract` (the block contraction: `BlockContract`, i.e. `BlockLipschitz.LipInfl` with
  `BlockDobrushin.DobCond` and the factorisation of the Wilson box kernel through `m` block shells, for every
  reflected periodic observable at a box the shifted partner does not read); `bridge` (slice pairing against the
  periodic covariance with error `η_k`; it compares the kernel-scale `‖T v‖²` with a normalised covariance, so
  the factor `μ_{g₀}²` is carried by `contract`'s constants; `SliceLift.SliceControl'` states the matched form);
  `rate` (`#κ_k (2 M_k δ_k + η_k) ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) t}`,
  `δ_k = B αᵐ V D`); `count` (`GlueballArea.ZeroFluxCount g₀ E t₀ Cc`).

## Circularity check (argued, not declarations)

* No field is `ZeroFluxGap`, `HiddenCostAt` or `RunSeed`. `count` is the count clause of `UniformGlueball`; with no
  gap it gives no decay of the defect (the defect bound of `trivialDefectN_le_of_levels` needs both).
* `bridge` with `rate` implies the diagonal shell bound (E2') of `LoopZoom.zeroFluxGap_of_electricDiag`, which is
  strictly stronger than a gap: its rate `c σ R_k + c'/R_k` grows with the shell radius. They are not equivalent
  to `ZeroFluxGap`. They are the clustering content `LoopZoom` §2 found circular: a per-pair bound on connected
  loop correlators at time `t` that must beat the number `#κ_k` of pairs.
* The periodic observables `X`, the reflection `τ, p` and the shift `s` are unconstrained (as in
  `FocusFeed.zeroFluxGap_of_kernelNear_bridge`). At `X = 0` the block contraction holds with the zero operator
  and the zero test (`K = 0`, `g = 0`, influence `0`) (given `B ≥ 0`; for `B < 0` the block contraction is
  unsatisfiable), the covariance is `0`, and `bridge` is the slice pair bound
  `|⟪T v_kj, T v_kl⟫| ≤ η_k` itself. So `contract` is load-bearing only when `X_kj` is the periodic counterpart of
  `v_kj` with `η_k` small; that counterpart is `SliceLift.lift`, and `SliceLift.SliceControl'` fixes `X`
  to it; in this record, with `X` free, the (T) content sits in `bridge + rate` and `count`.
* `α < 1` is not a field: the derivation does not use it. The block contraction enters only through `δ_k` in
  `rate`; a contraction `α < 1` at a physical block scale uniformly in `β` (the asymptotic-freedom crossover,
  `BlockLipschitz` §4 item 6) is what would make `δ_k = B αᵐ V D` small.

DERIVED (module-wide): `2` is `SU(2)`, the `L²` exponent, the doubling `2p` of the reflection plane, the two-sided
spread `2 M δ` and the window's lower end `2ℓ`; `5` is `HiddenCostAt`'s window; `4` is `diagRate`'s quarter rate;
`1` is the Gram constant of an orthonormal family.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleControl

open MeasureTheory Filter
open MassGap.ElectricLoops
open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels zeroFluxLevels_iff)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap ZeroFluxCount UniformGlueball hiddenCostAt_of_uniformGlueball)
open MassGap.SlabKernelOperator (kernelCLM)
open MassGap.LoopZoom (diagRate)
open MassGap.PeriodicState (periodicState)
open MassGap.LatticeReflection (ireflObs)
open MassGap.ReflectionShift (ishiftObsL)
open MassGap.FocusZoom (stateCov)
open MassGap.GibbsSpec (ILink IConf VConf splice)
open MassGap.BlockLipschitz (LipInfl BlockLip)
open MassGap.BlockDobrushin (DobCond)

/-! ## 1. The rate of the diagonal route, uniform on the window -/

/-- **Closed form of `diagRate`**: `√(c c' σ) + c σ δ/2 + 2 log(1 − e^{−c σ δ t/4})/t` (`t > 0`, `c σ δ > 0`). -/
theorem diagRate_eq {c c' σ δ t : ℝ} (ht : 0 < t) (hq : 0 < c * σ * δ) :
    diagRate c c' σ δ t = Real.sqrt (c * c' * σ) + c * σ * δ / 2
      + 2 * Real.log (1 - Real.exp (-(c * σ * δ * t / 4))) / t := by
  have hq1 : Real.exp (-(c * σ * δ * t / 4)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by have := mul_pos hq ht; linarith)
  have h1q : (0 : ℝ) < 1 - Real.exp (-(c * σ * δ * t / 4)) := by linarith
  unfold diagRate
  rw [Real.log_mul (Real.exp_pos _).ne' (div_pos (Real.exp_pos _) h1q).ne',
    Real.log_div (Real.exp_pos _).ne' h1q.ne', Real.log_exp, Real.log_exp]
  field_simp
  ring

/-- **`diagRate` is nondecreasing in the time** `t > 0` (`c σ δ > 0`). -/
theorem diagRate_mono {c c' σ δ t₀ t : ℝ} (hq : 0 < c * σ * δ) (ht₀ : 0 < t₀) (h : t₀ ≤ t) :
    diagRate c c' σ δ t₀ ≤ diagRate c c' σ δ t := by
  have ht : 0 < t := ht₀.trans_le h
  rw [diagRate_eq ht₀ hq, diagRate_eq ht hq]
  have hq0pos : 0 < Real.exp (-(c * σ * δ * t₀ / 4)) := Real.exp_pos _
  have hqpos : 0 < Real.exp (-(c * σ * δ * t / 4)) := Real.exp_pos _
  have hq0 : Real.exp (-(c * σ * δ * t₀ / 4)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by have := mul_pos hq ht₀; linarith)
  have hqq : Real.exp (-(c * σ * δ * t / 4)) ≤ Real.exp (-(c * σ * δ * t₀ / 4)) := by
    rw [Real.exp_le_exp]; have := mul_le_mul_of_nonneg_left h hq.le; linarith
  have hL : Real.log (1 - Real.exp (-(c * σ * δ * t₀ / 4)))
      ≤ Real.log (1 - Real.exp (-(c * σ * δ * t / 4))) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL0 : Real.log (1 - Real.exp (-(c * σ * δ * t₀ / 4))) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have key : 2 * Real.log (1 - Real.exp (-(c * σ * δ * t₀ / 4))) / t₀
      ≤ 2 * Real.log (1 - Real.exp (-(c * σ * δ * t / 4))) / t := by
    rw [div_le_div_iff₀ ht₀ ht]
    nlinarith [mul_le_mul_of_nonneg_left hL ht₀.le, mul_le_mul_of_nonpos_left h hL0]
  linarith

/-- A gap at rate `m'` is a gap at every smaller rate. -/
theorem zeroFluxGap_mono {ι : Type*} {g₀ : ι} {E : ι → ℝ} {m m' : ℝ} (h : ZeroFluxGap g₀ E m')
    (hm : m ≤ m') : ZeroFluxGap g₀ E m :=
  fun j hj => by have := h j hj; linarith

/-! ## 2. The block contraction and the Gram clause -/

/-- **The block contraction for one observable at one box** (`SU(2)`, coupling `β`): a block decomposition with at
most `B` blocks of diameter at most `D`, a block operator `K` with Lipschitz–Dobrushin influence `C_b` of row sums
at most `α` (`BlockLipschitz.LipInfl`, `BlockDobrushin.DobCond`), and a block test `g` of Lipschitz vector in
`[0, V]`, such that the Wilson box kernel of `X` at `Δ` is `m` shells of `K` applied to `g`, read through the block
map `e`. -/
def BlockContract (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SUN.SU 2), ℝ)) (α V D B : ℝ) (m : ℕ) : Prop :=
  ∃ (ιb : Type) (_ : Fintype ιb) (Y : ιb → Type) (_ : ∀ b, PseudoMetricSpace (Y b))
    (e : IConf (SUN.SU 2) → ∀ b, Y b) (K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)) (Cb : ιb → ιb → ℝ)
    (g : (∀ b, Y b) → ℝ) (L : ιb → ℝ),
    (Fintype.card ιb : ℝ) ≤ B ∧ LipInfl K Cb ∧ DobCond Cb α ∧ (∀ b (u v : Y b), dist u v ≤ D) ∧
      (∀ j, 0 ≤ L j) ∧ (∀ j, L j ≤ V) ∧ BlockLip g L ∧
      ∀ ω, MassGap.PeriodicStateDLR.wspec (two_ne_zero : (2 : ℕ) ≠ 0) β Δ X ω = K^[m] g (e ω)

/-- **`KernelNear` from the block contraction**: `KernelNear Δ X (B αᵐ V D)`. -/
theorem kernelNear_of_blockContract {β : ℝ} {Δ : Finset ILink} {X : C(IConf (SUN.SU 2), ℝ)}
    {α V D B : ℝ} {m : ℕ} (hα : 0 ≤ α) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (h : BlockContract β Δ X α V D B m) :
    MassGap.BoxFocusTest.KernelNear (two_ne_zero : (2 : ℕ) ≠ 0) β Δ X (B * (α ^ m * V) * D) := by
  classical
  obtain ⟨ιb, _, Y, _, e, K, Cb, g, L, hB, hK, hDC, hDiam, hL, hLV, hg, hfac⟩ := h
  obtain ⟨c0, hc⟩ := MassGap.BlockLipschitz.kernelNear_of_lip (two_ne_zero : (2 : ℕ) ≠ 0) β Δ X e hK
    hDC hα hV hD hDiam hL hLV hg m hfac
  refine ⟨c0, fun ω => (hc ω).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (mul_nonneg (pow_nonneg hα m) hV)) hD

/-- **The Gram clause of an orthonormal family holds with `λ = 1`.** -/
theorem gram_of_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ : Type*}
    [Fintype κ] {v : κ → E} (hv : Orthonormal ℝ v) (a : κ → ℝ) :
    1 * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hv.inner_sum a a Finset.univ, one_mul]
  refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
  simp [sq]

/-! ## 3. The per-slice record -/

/-- **The control of one zero-flux slice** (`SU(2)`, coupling `β`, side `n`, step `i`), on the real objects
`trivKN 2 β n i`, its slice measure `hSN 2 n i`, the loop shells of `ElectricLoops`, the periodic state
`periodicState` and the Wilson box kernel. The constants `c, c', σ, δ` (shell rate), `α, V, D, B` (block
contraction) and `t₀, Cc` (count) are those of `ScaleControlAt`, the same at every slice. Classification of each
field: module docstring. -/
structure SliceControl (c c' σ δ α V D B t₀ Cc : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  /-- Index type of the levels. -/
  ι : Type
  /-- The ground level. -/
  g₀ : ι
  /-- The level energies. -/
  E : ι → ℝ
  /-- The eigenfunctions. -/
  φ : ι → Slice n i → ℝ
  /-- The eigenvalues. -/
  μ : ι → ℝ
  /-- Bookkeeping (spectral theorem, not in the tree): orthonormal eigenfunctions exhausting both traces. -/
  levels : EigenLevels β n i g₀ E φ μ
  /-- Bookkeeping: each eigenfunction is measurable. -/
  meas : ∀ j, Measurable (φ j)
  /-- Bookkeeping: a bound of the kernel (`CentreSectorSeedN.bdd_trivKN`). -/
  C : ℝ
  kmeas : Measurable (Function.uncurry (trivKN 2 β n i))
  C0 : 0 ≤ C
  kbd : ∀ x y, |trivKN 2 β n i x y| ≤ C
  /-- Bookkeeping: the shell radii. -/
  R : ℕ → ℝ
  R_mono : Monotone R
  R_reach : ∀ N : ℕ, ∃ k, aRun 2 β * (N : ℝ) ≤ R k
  R_pos : ∀ k, 0 < R k
  R_step : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k
  /-- Bookkeeping: a finite family spanning each shell. -/
  κ : ℕ → Type
  [κfin : ∀ k, Fintype (κ k)]
  v : ∀ k, κ k → Lp ℝ 2 (hSN 2 n i)
  span : ∀ k, shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k ≤ Submodule.span ℝ (Set.range (v k))
  /-- Bookkeeping: the Gram lower bound (`λ = 1` for an orthonormal family, `gram_of_orthonormal`). -/
  lam : ℕ → ℝ
  lam_pos : ∀ k, 0 < lam k
  gram : ∀ k (a : κ k → ℝ), lam k * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v k j‖ ^ 2
  /-- The periodic observables, the reflection plane `(τ, p)`, the shift `s`, the bridge errors `η`, the bounds
  `M` of the shifted observables and the block-shell counts. -/
  X : ∀ k, κ k → C(IConf (SUN.SU 2), ℝ)
  τ : Fin 4
  p : ℤ
  s : ℕ
  η : ℕ → ℝ
  M : ℕ → ℝ
  shells : ℕ → ℕ
  /-- Physics, open: the block contraction of every reflected observable at a box its shifted partner does not
  read. Not `ZeroFluxGap`; load-bearing only through `bridge` with `X` tied to `v` (module docstring). -/
  contract : ∀ k j l, ∃ Δ : Finset ILink,
    BlockContract β Δ (ireflObs τ (2 * p) (X k j)) α V D B (shells k) ∧
      (∀ (u : VConf (SUN.SU 2) Δ) (ω : IConf (SUN.SU 2)),
        (⇑(ishiftObsL τ))^[s] (X k l) (splice Δ u ω) = (⇑(ishiftObsL τ))^[s] (X k l) ω) ∧
      ∀ ω, |(⇑(ishiftObsL τ))^[s] (X k l) ω| ≤ M k
  /-- Physics, open: the slice–periodic comparison with error `η_k`. At `X = 0` it is the slice pair bound.
  Not `ZeroFluxGap`; with `rate` it implies the diagonal shell bound (E2'), which is stronger than a gap. -/
  bridge : ∀ k j l,
    |inner ℝ (kernelCLM (trivKN 2 β n i) C kmeas C0 kbd (hSN 2 n i) (hSN 2 n i) (v k j))
      (kernelCLM (trivKN 2 β n i) C kmeas C0 kbd (hSN 2 n i) (hSN 2 n i) (v k l))|
    ≤ |stateCov (periodicState (two_ne_zero : (2 : ℕ) ≠ 0) β) (ireflObs τ (2 * p) (X k j))
        ((⇑(ishiftObsL τ))^[s] (X k l))| + η k
  /-- Physics, open: the per-pair bound beats the number of pairs at the shell rate. A numeric inequality on
  the slice data; not `ZeroFluxGap` (argued: it is the clustering content `LoopZoom` §2 found circular). -/
  rate : ∀ k, (Fintype.card (κ k) : ℝ) * (2 * M k * (B * (α ^ shells k * V) * D) + η k)
    ≤ lam k * (μ g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))))
  /-- Physics, open: the count clause at the physical time `t₀`. Not `HiddenCostAt`: without a gap it gives no
  decay of the defect. -/
  count : ZeroFluxCount g₀ E t₀ Cc

/-- **One slice record gives the gap on that slice** at `diagRate c c' σ δ (n a)`. -/
theorem zeroFluxGap_of_sliceControl {c c' σ δ α V D B t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4}
    (hβ : 0 < β) (hn : 0 < n) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ)
    (hα : 0 ≤ α) (hV : 0 ≤ V) (hD : 0 ≤ D) (S : SliceControl c c' σ δ α V D B t₀ Cc β n i) :
    ZeroFluxGap S.g₀ S.E (diagRate c c' σ δ ((n : ℝ) * aRun 2 β)) := by
  letI := S.κfin
  have hpos : ∀ j : {j : Fin 4 // j ≠ i}, 0 < CentreSectorSeed.Tr n i j := fun j => by
    simp only [CentreSectorSeed.Tr, RectWilson.tr, DoublingWilson.ext]
    positivity
  let y₀ : RectWilson.TT i (CentreSectorSeed.Tr n i) := fun j => ⟨0, hpos j⟩
  have hgen := MassGap.LoopsGenerate.excited_mem_closure_loops hβ S.levels S.meas y₀
  refine MassGap.FocusFeed.zeroFluxGap_of_kernelNear_bridge hβ hn S.levels S.meas S.kmeas S.C0 S.kbd
    S.R_mono S.R_reach hgen hc hc' hσ hδ S.R_pos S.R_step S.κ S.v S.span S.lam S.lam_pos S.gram S.X S.τ
    S.p S.s S.η S.M (fun k => B * (α ^ S.shells k * V) * D) S.bridge ?_ S.rate
  intro k j l
  obtain ⟨Δ, hK, hY, hYM⟩ := S.contract k j l
  exact ⟨Δ, kernelNear_of_blockContract hα hV hD hK, hY, hYM⟩

/-! ## 4. The single input and (T) -/

/-- **Scale control at the window `[2ℓ, 5ℓ]`** (`SU(2)`): sign conditions on the constants, `0 ≤ t₀ ≤ 2ℓ`, and,
eventually in `β`, a `SliceControl` record at every power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and every step
`i`, with the same constants at every `β`. -/
structure ScaleControlAt (c c' σ δ α V D B t₀ Cc ℓ : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c'_nonneg : 0 ≤ c'
  σ_nonneg : 0 ≤ σ
  step_pos : 0 < c * σ * δ
  α_nonneg : 0 ≤ α
  V_nonneg : 0 ≤ V
  D_nonneg : 0 ≤ D
  t₀_nonneg : 0 ≤ t₀
  t₀_le : t₀ ≤ 2 * ℓ
  slices : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ → ∀ i : Fin 4,
      Nonempty (SliceControl c c' σ δ α V D B t₀ Cc β n i)

/-- **`ScaleControlAt` gives the uniform glueball statement** at `m = diagRate c c' σ δ (2ℓ)`. -/
theorem uniformGlueball_of_scaleControlAt {c c' σ δ α V D B t₀ Cc ℓ : ℝ}
    (h : ScaleControlAt c c' σ δ α V D B t₀ Cc ℓ) :
    UniformGlueball 2 (diagRate c c' σ δ (2 * ℓ)) t₀ Cc ℓ := by
  filter_upwards [h.slices, eventually_gt_atTop (0 : ℝ)] with β hS hβ n hn h2 hlo hhi i
  obtain ⟨S⟩ := hS n hn h2 hlo hhi i
  have hn0 : 0 < n := by omega
  have ht : 0 < (n : ℝ) * aRun 2 β := mul_pos (by exact_mod_cast hn0) (aRun_pos (by norm_num) hβ)
  have hℓ : 0 < 2 * ℓ := by linarith
  have hg := zeroFluxGap_of_sliceControl hβ hn0 h.c_nonneg h.c'_nonneg h.σ_nonneg h.step_pos
    h.α_nonneg h.V_nonneg h.D_nonneg S
  exact ⟨S.ι, S.g₀, S.E, zeroFluxLevels_iff.2 ⟨S.φ, S.μ, S.levels⟩,
    zeroFluxGap_mono hg (diagRate_mono h.step_pos hℓ hlo), S.count⟩

/-- **(T) from `ScaleControlAt`**: `HiddenCostAt 2 m (2 Cc e^{m t₀}) ℓ`, `m = diagRate c c' σ δ (2ℓ)`. -/
theorem hiddenCostAt_of_scaleControlAt {c c' σ δ α V D B t₀ Cc ℓ : ℝ}
    (h : ScaleControlAt c c' σ δ α V D B t₀ Cc ℓ) :
    ObserverTheory.HiddenCostAt 2 (diagRate c c' σ δ (2 * ℓ))
      (2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀)) ℓ :=
  hiddenCostAt_of_uniformGlueball h.t₀_nonneg h.t₀_le (uniformGlueball_of_scaleControlAt h)

/-- **The single input at the window `[2ℓ, 5ℓ]`**: constants with a positive rate `diagRate c c' σ δ (2ℓ)` and
`ScaleControlAt` at them. -/
def _root_.MassGap.ScaleControl (ℓ : ℝ) : Prop :=
  ∃ c c' σ δ α V D B t₀ Cc : ℝ,
    0 < diagRate c c' σ δ (2 * ℓ) ∧ ScaleControlAt c c' σ δ α V D B t₀ Cc ℓ

/-- **(T) from `ScaleControl`**: a positive `σ` and an `A` with `HiddenCostAt 2 σ A ℓ`. -/
theorem hiddenCostAt_of_scaleControl {ℓ : ℝ} (h : ScaleControl ℓ) :
    ∃ σ A : ℝ, 0 < σ ∧ ObserverTheory.HiddenCostAt 2 σ A ℓ := by
  obtain ⟨c, c', σ, δ, α, V, D, B, t₀, Cc, hpos, hS⟩ := h
  exact ⟨_, _, hpos, hiddenCostAt_of_scaleControlAt hS⟩

end MassGap.ScaleControl

#print axioms MassGap.ScaleControl.diagRate_eq
#print axioms MassGap.ScaleControl.diagRate_mono
#print axioms MassGap.ScaleControl.zeroFluxGap_mono
#print axioms MassGap.ScaleControl.kernelNear_of_blockContract
#print axioms MassGap.ScaleControl.gram_of_orthonormal
#print axioms MassGap.ScaleControl.zeroFluxGap_of_sliceControl
#print axioms MassGap.ScaleControl.uniformGlueball_of_scaleControlAt
#print axioms MassGap.ScaleControl.hiddenCostAt_of_scaleControlAt
#print axioms MassGap.ScaleControl.hiddenCostAt_of_scaleControl
