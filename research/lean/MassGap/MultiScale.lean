import Mathlib
import MassGap.ScaleControlFull

/-!
# MassGap.MultiScale — the renormalisation-group content of the `SU(2)` record, as one statement

`ScaleControlFull.ScaleControlFullAt W r z` holds eleven fields. This module separates the fields that are
statements about the Wilson `SU(2)` theory across scales (the short-distance end, the asymptotic-freedom
coefficient, the strong-coupling end at the physical scale) from those that are not, states the former as one
`Prop`, `MultiScale W`, and relates it to the `ScaleControlFull` record.

## 1. `MultiScale W` (the statement)

Three clauses, each on the real objects of the tree:

* `uv` (**short distance**): `UVSplit W`, the small-field/large-field split of the one-site exponential
  moment of every flowed field of `SymPlaqClass 2` in physical units, at the class bound `symPlaqSup`
  (`ExistenceFlow.SmallLargeSplit` on `stateK`, the Wilson state at `dyBeta k`).
* `af` (**asymptotic freedom**): a two-point kernel of the trace channel `rhoD (fR 2) zOne` with the
  asymptotic-freedom coefficient (`TwoPointKernel ∧ AFCoefficient 2`).
* `endpoint` (**strong-coupling end**): `Endpoint`, constants fixed once and, frequently in the physical
  window `ℓ`, eventually in `β`, on every power-of-two slice with `n a ∈ [2ℓ, 5ℓ]`: a `SliceEnd` record (the
  zero-flux levels of the slice transfer `trivKN`, the loop-shell pair bound with error `η_k`, the rate
  `#κ_k η_k ≤ λ_k μ_{g₀}² e^{−(c σ R_k + c'/R_k) n a}`, and the count at `t₀`) and the odd-flux levels
  (`ScaleControlRun.OddLevels`: odd gap `m` and odd count `Co`).

Read as a Bałaban-type statement (argued, not a declaration): `uv` is the ultraviolet end: a uniform one-site
exponential moment of the flowed fields in physical units (the small/large-field split adds nothing to it,
`uvSplit_iff`); `af` is the running of the coupling read on the trace two-point function; `endpoint` is the end of the
flow at the physical scale, where the slice transfer has a gap uniform in `β`. The tree has no block-spin map
and no effective action on `stateK`, so the intermediate scales `a_k < a < b` are not stated; the three
clauses are the two ends and the coefficient.

## 2. What is derived (proved)

* **`contract` is redundant.** `SliceEnd` is `ScaleControl.SliceControl` without the periodic observables,
  the reflection data, the block-contraction field `contract` and the periodic `bridge`; in their place the
  slice pair bound `|⟪T v_kj, T v_kl⟫| ≤ η_k`. `SliceEnd.toControl` builds a `SliceControl` at
  `α = V = D = B = 0` with `X = 0` (`contract` by `blockContract_zero`: no blocks, the identity operator, the
  zero test, through `PeriodicStateDLR.wspec_empty`). `SliceControl.toEnd` goes back with
  `η'_k = 2 M_k B αᵐ V D + η_k`, through `ScaleControl.kernelNear_of_blockContract` and
  `BoxFocusTest.cov_le_of_kernelNear`. So **`endpoint_iff_run`: `Endpoint ↔ ScaleControlRun`**: the
  block contraction and the infinite-volume periodic state carry no logical content in `ScaleControlRun`
  beyond the slice pair bound and the rate (`SliceControl` does not tie `X` to `v`, so they are met at `X = 0`).
* **`uv` gives the record's `uv`** (`uv_of_uvSplit`, through `ExistenceFlow.siteExp_of_split`), with the class
  bound discharged (`symPlaq_le`: every member of `SymPlaqClass 2` is at most `symPlaqSup = 2 · #(S₄ × 2⁴)`,
  each of the summands of `sym` a Wilson density `≤ 2`). Conversely `split_of_siteExp` (cut-off `χ = 1`): the
  split is not stronger than `FlowUV.SiteExp`, so `uvSplit_iff`.
* **`af` is the record's `kern` at `zOne`**; `hz`, `hzS`, `hzP` are discharged at `zOne`
  (`ScaleControlFull.fullAt_zOne`).
* **`multiScale_iff`**: `MultiScale W ↔` the record's `uv`, `kern` (at `zOne`) and `run`. The statement asks no
  more than those three fields.

## 3. No capstone from `MultiScale`

`MultiScale W` carries `endpoint : Endpoint`, which `InputAudit.not_multiScaleEndpoint` refutes under the argued
growth of the zero-flux level count, so no `ClayStatementAt` is stated from it. `fullAt_of_multiScale` still
builds the `ScaleControlFull` record from it and the five fields it does not contain.

## 4. What remains separate, and why (argued from the definitions)

* `phys` (`PhysRange r` of `energy0 W`): a property of the chosen flow's range, not of the measure.
* `low` (`ObsLower`): given `comp`, equivalent to the target clause `NonGaussianT`
  (`InputsTriage.nonGaussianT_rhoD_iff_lower`); a statement on the observer's three-point reading.
* `ward` (`WardT`): the translation Ward identity of the trace channel in the limit; a symmetry statement on
  the continuum composite, not a size bound.
* `comp` (`BoundC ∧ OS0C ∧ OS1C ∧ CovC ∧ CompNondeg` of `CbR 2 zOne`): size and covariance clauses of the
  bare composites at the factor `z ∼ 2/a⁴`. `BoundC` bounds readings that contain the disconnected part
  `z · ν_k(O)`, of order `a⁻⁴ ν_k(O)`; `uv` bounds moments of the flowed fields `O ∘ V_k`, not of the bare
  composites, and the tree has no relation between the two at this factor. Not derived.
* `approx` (`ApproxK`): an approximation of the composites by the observer's margin monomials; positivity
  alone does not give it (`ApproxObserver.exists_jointRPK_not_approxK`).
* Within `endpoint`, `count` (zero flux) and the odd `count` are heat-trace bounds at the fixed time `t₀`,
  and the gap clauses are spectral bounds; neither follows from the other (`ZeroFluxCount` at `t₀` is not
  implied by the trace identities of `EigenLevels`, which are at the window time `n a ≥ 2ℓ ≥ t₀`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the Wilson density bound and the two sides of a covariance; `0` the
block constants of the empty block family, the reflection plane, the shift and the signs; `1` the cut-off
`χ = 1`; `2 · 1 + 3` and `4` the site count of `classMoments_of_siteExp`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MultiScale

open MeasureTheory Filter
open MassGap.ScaleControl (SliceControl BlockContract kernelNear_of_blockContract)
open MassGap.ScaleControlRun (OddLevels SliceRun ScaleControlRunAt)
open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.TensionFloor (Slice EigenLevels)
open MassGap.AsymptoticScaling (aRun)
open MassGap.GlueballArea (ZeroFluxCount)
open MassGap.SlabKernelOperator (kernelCLM)
open MassGap.LoopZoom (diagRate)
open MassGap.LatticeReflection (ireflObs)
open MassGap.ReflectionShift (ishiftObsL)
open MassGap.GibbsSpec (ILink IConf)

/-! ## 1. The slice endpoint without the periodic state -/

/-- **The control of one zero-flux slice, on the slice alone** (`SU(2)`, coupling `β`, side `n`, step `i`):
the fields of `ScaleControl.SliceControl` that read the slice transfer `trivKN 2 β n i`, with the slice pair
bound `|⟪T v_kj, T v_kl⟫| ≤ η_k` in place of the periodic observables, `contract` and `bridge`. -/
structure SliceEnd (c c' σ δ t₀ Cc : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
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
  /-- Bookkeeping: a bound of the kernel. -/
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
  span : ∀ k, MassGap.ElectricLoops.shell (hSN 2 n i) (φ g₀) (aRun 2 β) R k
    ≤ Submodule.span ℝ (Set.range (v k))
  /-- Bookkeeping: the Gram lower bound. -/
  lam : ℕ → ℝ
  lam_pos : ∀ k, 0 < lam k
  gram : ∀ k (a : κ k → ℝ), lam k * ∑ j, a j ^ 2 ≤ ‖∑ j, a j • v k j‖ ^ 2
  /-- The pair errors. -/
  η : ℕ → ℝ
  /-- Open: the slice pair bound of the loop shells. -/
  pair : ∀ k j l,
    |inner ℝ (kernelCLM (trivKN 2 β n i) C kmeas C0 kbd (hSN 2 n i) (hSN 2 n i) (v k j))
      (kernelCLM (trivKN 2 β n i) C kmeas C0 kbd (hSN 2 n i) (hSN 2 n i) (v k l))| ≤ η k
  /-- Open: the pair errors beat the number of pairs at the shell rate. -/
  rate : ∀ k, (Fintype.card (κ k) : ℝ) * η k
    ≤ lam k * (μ g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun 2 β))))
  /-- Open: the count clause at the physical time `t₀`. -/
  count : ZeroFluxCount g₀ E t₀ Cc

/-- **The block contraction of the zero observable**: the empty block family, the identity operator and the
zero test, at the empty box, with all block constants `0`. -/
theorem blockContract_zero (β : ℝ) (τ : Fin 4) (c : ℤ) (m : ℕ) :
    BlockContract β ∅ (ireflObs τ c (0 : C(IConf (SUN.SU 2), ℝ))) 0 0 0 0 m := by
  refine ⟨Empty, inferInstance, fun _ => Unit, fun _ => inferInstance, fun _ _ => (), id,
    fun _ _ => 0, fun _ => 0, fun _ => 0, by simp, ?_, ?_, fun b => b.elim, fun j => j.elim,
    fun j => j.elim, fun b => b.elim, ?_⟩
  · intro g L _ _ b
    exact b.elim
  · exact ⟨fun i => i.elim, fun i => i.elim⟩
  · intro ω
    rw [MassGap.PeriodicStateDLR.wspec_empty, map_zero, Function.iterate_id]
    rfl

/-- **`SliceEnd` gives `SliceControl`** at `α = V = D = B = 0`, with the periodic observables `0`. -/
def SliceEnd.toControl {c c' σ δ t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4}
    (S : SliceEnd c c' σ δ t₀ Cc β n i) : SliceControl c c' σ δ 0 0 0 0 t₀ Cc β n i where
  ι := S.ι
  g₀ := S.g₀
  E := S.E
  φ := S.φ
  μ := S.μ
  levels := S.levels
  meas := S.meas
  C := S.C
  kmeas := S.kmeas
  C0 := S.C0
  kbd := S.kbd
  R := S.R
  R_mono := S.R_mono
  R_reach := S.R_reach
  R_pos := S.R_pos
  R_step := S.R_step
  κ := S.κ
  κfin := S.κfin
  v := S.v
  span := S.span
  lam := S.lam
  lam_pos := S.lam_pos
  gram := S.gram
  X := fun _ _ => 0
  τ := 0
  p := 0
  s := 0
  η := S.η
  M := fun _ => 0
  shells := fun _ => 0
  contract := fun _ _ _ => ⟨∅, blockContract_zero β 0 (2 * 0) 0, fun _ _ => by simp, fun _ => by simp⟩
  bridge := fun k j l => (S.pair k j l).trans (le_add_of_nonneg_left (abs_nonneg _))
  rate := fun k => by
    letI := S.κfin
    convert S.rate k using 2
    simp
  count := S.count

/-- **`SliceControl` gives `SliceEnd`** (`α, V, D ≥ 0`), at the pair errors `2 M_k B αᵐ V D + η_k`:
`bridge`, with the covariance bounded through `contract`
(`BoxFocusTest.cov_le_of_kernelNear` at `ScaleControl.kernelNear_of_blockContract`). -/
def _root_.MassGap.ScaleControl.SliceControl.toEnd {c c' σ δ α V D B t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4}
    (hα : 0 ≤ α) (hV : 0 ≤ V) (hD : 0 ≤ D) (S : SliceControl c c' σ δ α V D B t₀ Cc β n i) :
    SliceEnd c c' σ δ t₀ Cc β n i where
  ι := S.ι
  g₀ := S.g₀
  E := S.E
  φ := S.φ
  μ := S.μ
  levels := S.levels
  meas := S.meas
  C := S.C
  kmeas := S.kmeas
  C0 := S.C0
  kbd := S.kbd
  R := S.R
  R_mono := S.R_mono
  R_reach := S.R_reach
  R_pos := S.R_pos
  R_step := S.R_step
  κ := S.κ
  κfin := S.κfin
  v := S.v
  span := S.span
  lam := S.lam
  lam_pos := S.lam_pos
  gram := S.gram
  η := fun k => 2 * S.M k * (B * (α ^ S.shells k * V) * D) + S.η k
  pair := fun k j l => by
    obtain ⟨Δ, hK, hY, hYM⟩ := S.contract k j l
    have hc := MassGap.BoxFocusTest.cov_le_of_kernelNear (two_ne_zero : (2 : ℕ) ≠ 0) β Δ _ _ hY hYM
      (kernelNear_of_blockContract hα hV hD hK)
    have hb := S.bridge k j l
    linarith
  rate := fun k => S.rate k
  count := S.count

/-! ## 2. The strong-coupling end -/

/-- **One slice of the endpoint**: a `SliceEnd` record and, for every transverse `ν`, the odd levels on the
same zero-flux levels. -/
structure EndRun (c c' σ δ t₀ Cc m Co : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  core : SliceEnd c c' σ δ t₀ Cc β n i
  odd : ∀ ν : {j : Fin 4 // j ≠ i}, OddLevels β n i ν core.g₀ core.E m t₀ Co

/-- **The endpoint at the window `[2ℓ, 5ℓ]`**: sign conditions and, eventually in `β`, an `EndRun` at every
power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and every step. -/
structure EndpointAt (c c' σ δ t₀ Cc m Co ℓ : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c'_nonneg : 0 ≤ c'
  σ_nonneg : 0 ≤ σ
  step_pos : 0 < c * σ * δ
  t₀_nonneg : 0 ≤ t₀
  t₀_le : t₀ ≤ 2 * ℓ
  slices : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun 2 β → (n : ℝ) * aRun 2 β ≤ 5 * ℓ → ∀ i : Fin 4,
      Nonempty (EndRun c c' σ δ t₀ Cc m Co β n i)

/-- **The strong-coupling end**: constants fixed once, a positive zero-flux rate at `ℓ₀ > 0`, a positive odd
gap `m`, and `EndpointAt` frequently in `ℓ`. -/
def Endpoint : Prop :=
  ∃ c c' σ δ t₀ Cc m Co ℓ₀ : ℝ, 0 < ℓ₀ ∧ 0 < diagRate c c' σ δ (2 * ℓ₀) ∧ 0 < m ∧ 0 ≤ Cc ∧
    0 ≤ Co ∧ ∃ᶠ ℓ in atTop, EndpointAt c c' σ δ t₀ Cc m Co ℓ

theorem runAt_of_endpointAt {c c' σ δ t₀ Cc m Co ℓ : ℝ} (h : EndpointAt c c' σ δ t₀ Cc m Co ℓ) :
    ScaleControlRunAt c c' σ δ 0 0 0 0 t₀ Cc m Co ℓ where
  c_nonneg := h.c_nonneg
  c'_nonneg := h.c'_nonneg
  σ_nonneg := h.σ_nonneg
  step_pos := h.step_pos
  α_nonneg := le_rfl
  V_nonneg := le_rfl
  D_nonneg := le_rfl
  t₀_nonneg := h.t₀_nonneg
  t₀_le := h.t₀_le
  slices := by
    filter_upwards [h.slices] with β hS n hn h2 hlo hhi i
    obtain ⟨R⟩ := hS n hn h2 hlo hhi i
    exact ⟨⟨R.core.toControl, R.odd⟩⟩

theorem endpointAt_of_runAt {c c' σ δ α V D B t₀ Cc m Co ℓ : ℝ}
    (h : ScaleControlRunAt c c' σ δ α V D B t₀ Cc m Co ℓ) : EndpointAt c c' σ δ t₀ Cc m Co ℓ where
  c_nonneg := h.c_nonneg
  c'_nonneg := h.c'_nonneg
  σ_nonneg := h.σ_nonneg
  step_pos := h.step_pos
  t₀_nonneg := h.t₀_nonneg
  t₀_le := h.t₀_le
  slices := by
    filter_upwards [h.slices] with β hS n hn h2 hlo hhi i
    obtain ⟨R⟩ := hS n hn h2 hlo hhi i
    exact ⟨⟨R.ctl.toEnd h.α_nonneg h.V_nonneg h.D_nonneg, R.odd⟩⟩

/-- **The endpoint is the run**: `Endpoint ↔ ScaleControlRun`. The block contraction and the periodic state
of `ScaleControlRun` carry nothing beyond the slice pair bound. -/
theorem endpoint_iff_run : Endpoint ↔ ScaleControlRun := by
  constructor
  · rintro ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ₀, h1, h2, h3, h4, h5, hf⟩
    exact ⟨c, c', σ, δ, 0, 0, 0, 0, t₀, Cc, m, Co, ℓ₀, h1, h2, h3, h4, h5,
      hf.mono fun ℓ h => runAt_of_endpointAt h⟩
  · rintro ⟨c, c', σ, δ, α, V, D, B, t₀, Cc, m, Co, ℓ₀, h1, h2, h3, h4, h5, hf⟩
    exact ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ₀, h1, h2, h3, h4, h5,
      hf.mono fun ℓ h => endpointAt_of_runAt h⟩

end MassGap.MultiScale

/-! ## 3. The short-distance end and the statement -/

namespace MassGap.MultiScale

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP
open MassGap.ScaleControlFull (ScaleControlFullAt zOne)

/-- **The bound of the symmetrised plaquette class**: `2` per summand of `sym`. -/
def symPlaqSup : ℝ := (Fintype.card (Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : ℝ) * 2

/-- **Every member of `SymPlaqClass 2` is at most `symPlaqSup`.** -/
theorem symPlaq_le : ∀ O ∈ SymPlaqClass 2, ∀ U, O.1 U ≤ symPlaqSup := by
  rintro O ⟨q, rfl⟩ U
  rw [sym_apply]
  refine (Finset.sum_le_sum fun g _ => (?_ : _ ≤ (2 : ℝ))).trans ?_
  · exact MassGap.WilsonAction.wilsonDensity_le_two (by norm_num) _
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, symPlaqSup]

/-- **The short-distance clause**: the small-field/large-field split at the class bound `symPlaqSup`.
DERIVED: `2 * 1 + 3`, `4` the site count `(2R + 3)⁴` of `FlowUV.classUnitExp_of_siteExp` at `R = 1`; `2` the
rank. -/
def UVSplit (W : ConfFlow 2) : Prop :=
  ∃ t C₁ C₂ : ℝ, 0 < t ∧ ExistenceFlow.SmallLargeSplit (ne_zero_of_two_le (le_refl 2)) W
    (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) symPlaqSup C₁ C₂

/-- **The split at the cut-off `χ = 1`**: `SiteExp` gives `SmallLargeSplit` at any `M`, with `C₂ = 0`. -/
theorem split_of_siteExp {N : ℕ} (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {s C M : ℝ} (h : FlowUV.SiteExp hN W D s C) : ExistenceFlow.SmallLargeSplit hN W D s M C 0 := by
  unfold FlowUV.SiteExp at h
  unfold ExistenceFlow.SmallLargeSplit
  filter_upwards [h] with k hk O hO
  refine ⟨1, fun U => by simp, ?_, ?_⟩
  · rw [one_mul]; exact hk O hO
  · rw [sub_self, (stateK hN k).map_zero, zero_mul]

/-- **`UVSplit` is the record's `uv`.** -/
theorem uvSplit_iff (W : ConfFlow 2) :
    UVSplit W ↔ ∃ t C : ℝ, 0 < t ∧
      FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C := by
  constructor
  · rintro ⟨t, C₁, C₂, ht, h⟩
    exact ScaleControlFull.uv_of_split ht symPlaq_le h
  · rintro ⟨t, C, ht, h⟩
    exact ⟨t, C, 0, ht, split_of_siteExp _ W h⟩

/-- **The multi-scale statement at one flow `W`** (`SU(2)`): the short-distance split, the asymptotic-freedom
kernel of the trace channel at `zOne`, and the strong-coupling end. Module docstring, §1. -/
structure _root_.MassGap.MultiScale (W : ConfFlow 2) : Prop where
  /-- Short distance: the small-field/large-field split in physical units. -/
  uv : UVSplit W
  /-- Asymptotic freedom: a two-point kernel of the trace with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G
    ∧ AFCoefficient 2 G
  /-- Strong coupling at the physical scale: the slice endpoint with the odd levels. -/
  endpoint : Endpoint

/-- **`MultiScale` is the record's `uv`, `kern` and `run`** (at `zOne`). -/
theorem multiScale_iff (W : ConfFlow 2) :
    MultiScale W ↔ (∃ t C : ℝ, 0 < t ∧
        FlowUV.SiteExp (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) (t * (2 * 1 + 3) ^ 4) C)
      ∧ (∃ G : ℝ → ℝ, TwoPointKernel (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne) G
        ∧ AFCoefficient 2 G) ∧ ScaleControlRun := by
  constructor
  · intro h
    exact ⟨(uvSplit_iff W).1 h.uv, h.af, endpoint_iff_run.1 h.endpoint⟩
  · rintro ⟨hu, hk, hr⟩
    exact ⟨(uvSplit_iff W).2 hu, hk, endpoint_iff_run.2 hr⟩

/-- **The record from `MultiScale`** and the five fields it does not contain, at `zOne`. -/
theorem fullAt_of_multiScale {W : ConfFlow 2} {r : ℝ} (h : MultiScale W)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hlow : InputsTriage.ObsLower (ne_zero_of_two_le (le_refl 2)) zOne)
    (hward : WardT (ne_zero_of_two_le (le_refl 2)) (rhoD (fR 2) zOne))
    (hcomp : InputsTriage.BoundC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ OS0C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ CovC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)
      ∧ CompNondeg (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (happrox : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0)
      (mixKR (le_refl 2) W zOne r) (gramF (le_refl 2) W r)) :
    ScaleControlFullAt W r zOne :=
  ScaleControlFull.fullAt_zOne (endpoint_iff_run.1 h.endpoint) ((uvSplit_iff W).1 h.uv) hphys h.af
    hlow hward hcomp happrox

end MassGap.MultiScale

end

#print axioms MassGap.MultiScale.blockContract_zero
#print axioms MassGap.MultiScale.SliceEnd.toControl
#print axioms MassGap.ScaleControl.SliceControl.toEnd
#print axioms MassGap.MultiScale.runAt_of_endpointAt
#print axioms MassGap.MultiScale.endpointAt_of_runAt
#print axioms MassGap.MultiScale.endpoint_iff_run
#print axioms MassGap.MultiScale.symPlaq_le
#print axioms MassGap.MultiScale.split_of_siteExp
#print axioms MassGap.MultiScale.uvSplit_iff
#print axioms MassGap.MultiScale.multiScale_iff
#print axioms MassGap.MultiScale.fullAt_of_multiScale
