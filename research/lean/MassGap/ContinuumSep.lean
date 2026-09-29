import Mathlib
import MassGap.ContinuumReconstruction
import MassGap.ContinuumCluster
import MassGap.ClayCapstone
import MassGap.GNSCompare
import MassGap.GapToOperator
import MassGap.SecondEigenvalue
import MassGap.TransferGap

noncomputable section

/-!
# MassGap.ContinuumSep — the continuum chain on families with separated supports, and the gap

## The uniform bound on separated families

`ContinuumSchwinger.UniformBound` bounds every family, including `((O, f), (O, f))`, whose value at a growing field-strength factor `Z` is `Z²` times the second moment of one smeared
field, at least `Z²` times its variance.
`UniformBoundSep hN ρ` asks for the bound only where the test-function supports are pairwise at
sup-distance at least `d > 0`: for every family `F` and every `d > 0` one constant bounds the
renormalised lattice functions of every dyadic per-factor translate of `F` whose supports are
pairwise `d`-separated (`FamSep d`). `uniformBoundSep_of_uniformBound`: `UniformBound` implies it.

## The chain on separated positive-time monomials

`SepMono N τ` is the positive-time monomials whose factors are, for one `d > 0`, supported in
`y_τ ≥ d` and pairwise `d`-separated (`sepPos τ d`). For two of them, `θP ∪ Q` is `d`-separated
(`famSep_pairFam`), and the dyadic time step keeps them in `SepMono` (`sepPos_shift`). So every
family the reconstruction and clustering consume is a separated reflected pair `θP' ∪ Q'` at a common
dyadic time shift of two separated monomials.

## E on reflected pairs

`PairBoundSep hN ρ τ` asks for the bound only on those families: each pair `P, Q` of separated
positive-time monomials has one constant bounding `|latSkR(θP' ∪ Q')|` eventually in the step, at every
common dyadic time shift `P', Q'`. `DiagBoundSep hN ρ τ` asks it only on the reflection diagonal
`θP ∪ P`, unshifted.

* `sq_latSkR_pairFam_le`, `abs_latSkR_pairFam_le_sqrt`: Cauchy–Schwarz for the reflected lattice
  pairing at each step (`Transfer.ReflForm.cauchy_schwarz` on `ContinuumCluster.Dk`).
* `latSkR_pairFam_shift_self_le`: the reflected diagonal of a monomial shifted forward in time is at
  most the unshifted diagonal at each step (`TransferData.T_contract`, iterated).
* `diagBoundSep_of_uniformBoundSep`, `pairBoundSep_of_diagBoundSep` (under `ReflCompat τ`),
  `pairBoundSep_of_uniformBoundSep`: `UniformBoundSep → DiagBoundSep → PairBoundSep`.
* `tendsto_pair_sep_of_pairBound`, `kernSep_iterate_bound_of_pairBound`: existence of the limit on
  every separated reflected pair, and OS0 along the shifts, on `PairBoundSep`.

The chain runs on `PairBoundSep`:

* existence `tendsto_contS_sep`, OS0 `exists_abs_contS_le_sep`, both for separated families under
  `UniformBoundSep`; `tendsto_pair_sep`, `kernSep_iterate_bound` their reflected-pair forms under
  `UniformBoundSep`, and `tendsto_pair_sep_of_pairBound`, `kernSep_iterate_bound_of_pairBound` under
  `PairBoundSep`;
* OS2 `contS_gram_nonneg_sep` on `SepMono`;
* the reconstruction `continuum_reconstruction_sep`: Hilbert space, unit vacuum, self-adjoint
  transfer operator at each dyadic step with spectrum in `[0, 1]`, `⟪vecOfSep P, vecOfSep Q⟫ = S(θP ∪ Q)`;
* clustering `contS_cluster_of_fixedWindowDecay_sep` from `WeakCouplingWindow.FixedWindowDecay`.

## The gap

`continuum_gap_sep`: at `2 ≤ N`, a window `L > 0`, `FixedWindowDecay τ 0 hN L`, `PairBoundSep` and `ReflCompat τ`,
there is `c > 0` such that for every dyadic step `m` the reconstructed transfer data satisfy
`TransferGap.GapAt` at `r_m = exp(−(c/L)·dySpacing N m)`, the operator `opT` contracts the vacuum
complement by `r_m`, and `spectrum ℝ opT ⊆ {1} ∪ [0, r_m]` with `1` the greatest element. The rate
`c/L` does not depend on `m`.

The route: for `x` in the module with `⟨x, Ω⟩ = 0`, `⟨x, Tʲx⟩ = ∑ x_P x_Q (S(θP ∪ TʲQ) − S(θP)S(Q))`
because both vacuum sums vanish (`form_pow_le_of_cluster_sep`); the clustering bound gives
`⟨x, Tʲx⟩ ≤ K_x r_mʲ` with `K_x = ∑ |x_P||x_Q| √(S(θP ∪ P)(S(θQ ∪ Q) − S(Q)²))`, a constant chosen
after the vector; `ClayCapstone.absolute_decay_of_form_decay` and
`SecondEigenvalue.norm_le_of_absolute_iterate_bound` turn per-vector decay into `GapAt`
(`gapAt_of_per_vector_form_decay`), with no density argument: every class of the real quotient is a
module vector. `GapToOperator` carries `GapAt` to the completion.

## Non-triviality

`exists_orth_ne_zero_sep`: if `S(θQ ∪ Q) − S(Q)² ≠ 0` for one separated monomial `Q`
(`ConnectedTwoPointNonzero`), the Hilbert space has a non-zero vector orthogonal to the vacuum and
not a multiple of it. Without that the gap statement holds on a space that may be spanned by `Ω`.

## Scope

`PairBoundSep` (or `DiagBoundSep`, or `UniformBoundSep`), `FixedWindowDecay` and
`ConnectedTwoPointNonzero` are hypotheses. `UniformBoundSep` holds at bounded renormalisation
(`uniformBoundSep_of_uniformBound`, `ContinuumSchwinger.uniformBound_of_bounded`), where the limit is
degenerate; at a growing `Z` none of them is proved here. The reconstructed transfer data
`contTransferSep hN ρ τ hB hR m` takes the witness `hB : PairBoundSep hN ρ τ` only inside its proof
fields, so any two witnesses give definitionally equal data. The transfer operators are given at the
dyadic steps; no Hamiltonian is constructed.
-/

namespace MassGap.ContinuumSep

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Separated supports -/

section Separation

/-- The supports of `f` and `g` are at sup-distance at least `d`: every point where `f` is non-zero
and every point where `g` is non-zero differ by at least `d` in some coordinate.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the support. -/
def sepBy (d : ℝ) (f g : TestFn) : Prop :=
  ∀ y z : Fin 4 → ℝ, f.1 y ≠ 0 → g.1 z ≠ 0 → ∃ i : Fin 4, d ≤ |y i - z i|

/-- The test functions of a family are pairwise `d`-separated.

DERIVED: no numeral. -/
def FamSep {ι : Type} (d : ℝ) (F : ι → SField N) : Prop :=
  ∀ i j, i ≠ j → sepBy d (F i).2 (F j).2

/-- A common translation keeps separation.

DERIVED: `4` in `Fin 4 → ℝ` is the spacetime dimension. -/
theorem sepBy_translate {d : ℝ} {f g : TestFn} (h : sepBy d f g) (v : Fin 4 → ℝ) :
    sepBy d (f.translate v) (g.translate v) := by
  intro y z hy hz
  obtain ⟨i, hi⟩ := h (y - v) (z - v) hy hz
  refine ⟨i, ?_⟩
  have e : (y - v) i - (z - v) i = y i - z i := by
    rw [Pi.sub_apply, Pi.sub_apply]
    ring
  rw [e] at hi
  exact hi

#print axioms sepBy_translate

/-- The time reflection keeps separation.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem sepBy_reflect (τ : Fin 4) {d : ℝ} {f g : TestFn} (h : sepBy d f g) :
    sepBy d (f.reflect τ) (g.reflect τ) := by
  intro y z hy hz
  obtain ⟨i, hi⟩ := h (reflR τ y) (reflR τ z) hy hz
  refine ⟨i, ?_⟩
  have e : reflR τ y i - reflR τ z i = reflR τ (y - z) i := by
    rw [reflR_sub, Pi.sub_apply]
  rw [e, abs_reflR, Pi.sub_apply] at hi
  exact hi

#print axioms sepBy_reflect

/-- **The uniform bound on separated families (stated; proved at bounded data through
`uniformBoundSep_of_uniformBound`).** For every family `F` and every
`d > 0` there is one constant bounding, eventually in the step, the renormalised lattice Schwinger
function of every dyadic per-factor translate of `F` whose test-function supports are pairwise at
sup-distance at least `d`.

Configurations with coincident or overlapping supports, such as `((O, f), (O, f))` untranslated with
`f ≠ 0`, are outside its quantifier: the bound covers only the translates in which every factor's
support is `d`-separated from every other factor's. The constant is chosen after `d`, so it may grow
as `d → 0`.

DERIVED: `0` is the excluded colour count and the sign of `d`. -/
def UniformBoundSep (hN : N ≠ 0) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N) (d : ℝ), 0 < d → ∃ C : ℝ,
    ∀ (m : ℕ) (n : ι → ISite),
      FamSep d (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i)))) →
      ∀ᶠ k in atTop,
        |latSkR hN ρ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C

/-- **`UniformBound` implies `UniformBoundSep`**: the same constant serves, the separation
hypothesis unused.

DERIVED: `0` is the excluded colour count. -/
theorem uniformBoundSep_of_uniformBound (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBound hN ρ) :
    UniformBoundSep hN ρ := by
  intro ι _ F d _
  obtain ⟨C, hC⟩ := hB ι F
  exact ⟨C, fun m n _ => hC m n⟩

#print axioms uniformBoundSep_of_uniformBound

/-- **Existence of the limit on separated families**: under `UniformBoundSep`, for every family
whose supports are pairwise `d`-separated with `d > 0`, `latSkR hN ρ k F → contS hN ρ F` along
`ultra`.

DERIVED: `0` is the sign of `d` and the zero translation. -/
theorem tendsto_contS_sep (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBoundSep hN ρ) {ι : Type}
    [Fintype ι] (F : ι → SField N) {d : ℝ} (hd : 0 < d) (hF : FamSep d F) :
    Tendsto (fun k => latSkR hN ρ k F) (ultra : Filter ℕ) (𝓝 (contS hN ρ F)) := by
  obtain ⟨C, hC⟩ := hB ι F d hd
  have hF0 : FamSep d (fun i => ((F i).1,
      (F i).2.translate (site (dySpacing N 0) ((fun _ : ι => (0 : ISite)) i)))) := by
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta]
    exact hF
  have h0 := hC 0 (fun _ => 0) hF0
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_contS_sep

/-- **OS0 on separated families**: under `UniformBoundSep`, for every family `F` and `d > 0`, one
constant bounds `|contS|` at every dyadic per-factor translate of `F` whose supports are pairwise
`d`-separated.

DERIVED: `0` is the sign of `d`. -/
theorem exists_abs_contS_le_sep (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBoundSep hN ρ)
    {ι : Type} [Fintype ι] (F : ι → SField N) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
      FamSep d (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i)))) →
      |contS hN ρ (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB ι F d hd
  exact ⟨C, fun m n hs =>
    le_of_tendsto (tendsto_contS_sep hN ρ hB _ hd hs).abs ((hC m n hs).filter_mono ultra_le)⟩

#print axioms exists_abs_contS_le_sep

end Separation

/-! ## 2. Separated positive-time monomials -/

section Monomials

/-- Every factor of `P` is supported in `y_τ ≥ d`, and the factors are pairwise `d`-separated.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the support. -/
def sepPos (τ : Fin 4) (d : ℝ) (P : Mono N) : Prop :=
  (∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ) ∧ ∀ i j, i ≠ j → sepBy d (P.2 i).2 (P.2 j).2

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem sepPos_mono {τ : Fin 4} {d d' : ℝ} {P : Mono N} (h : sepPos τ d P) (hd : d' ≤ d) :
    sepPos τ d' P := by
  refine ⟨fun i y hy => le_trans hd (h.1 i y hy), fun i j hij => ?_⟩
  intro y z hy hz
  obtain ⟨k, hk⟩ := h.2 i j hij y z hy hz
  exact ⟨k, le_trans hd hk⟩

#print axioms sepPos_mono

/-- A translation forward in time keeps a monomial `d`-separated and positive-time.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the time component. -/
theorem sepPos_shift {τ : Fin 4} {d : ℝ} {P : Mono N} (h : sepPos τ d P) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v τ) : sepPos τ d (Mono.shift v P) := by
  refine ⟨fun i y hy => ?_, fun i j hij => sepBy_translate (h.2 i j hij) v⟩
  have h1 := h.1 i (y - v) hy
  have h2 : (y - v) τ = y τ - v τ := rfl
  rw [h2] at h1
  linarith

#print axioms sepPos_shift

/-- **`θP ∪ Q` is separated**: two `d`-separated positive-time monomials give a `d`-separated
reflected pair. Within `θP` and within `Q` by `sepBy_reflect` and the hypotheses; across, the
factors of `θP` sit in `y_τ ≤ −d` and those of `Q` in `y_τ ≥ d`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of `d`. -/
theorem famSep_pairFam {τ : Fin 4} {d : ℝ} {P Q : Mono N} (hd : 0 ≤ d) (hP : sepPos τ d P)
    (hQ : sepPos τ d Q) : FamSep d (pairFam τ P Q) := by
  intro x x' hne
  cases x with
  | inl i =>
    cases x' with
    | inl j =>
      have hij : i ≠ j := fun h => hne (congrArg Sum.inl h)
      exact sepBy_reflect τ (hP.2 i j hij)
    | inr j =>
      intro y z hy hz
      have h1 : d ≤ reflR τ y τ := hP.1 i (reflR τ y) hy
      have h2 : d ≤ z τ := hQ.1 j z hz
      have h3 : reflR τ y τ = -y τ := by simp only [reflR, Function.update_self]
      refine ⟨τ, ?_⟩
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self (z τ - y τ))
  | inr i =>
    cases x' with
    | inl j =>
      intro y z hy hz
      have h1 : d ≤ y τ := hQ.1 i y hy
      have h2 : d ≤ reflR τ z τ := hP.1 j (reflR τ z) hz
      have h3 : reflR τ z τ = -z τ := by simp only [reflR, Function.update_self]
      refine ⟨τ, ?_⟩
      exact le_trans (by linarith) (le_abs_self (y τ - z τ))
    | inr j =>
      have hij : i ≠ j := fun h => hne (congrArg Sum.inr h)
      exact hQ.2 i j hij

#print axioms famSep_pairFam

/-- Two separated positive-time monomials, with their own margins, give a separated reflected pair
at the smaller margin.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the margins. -/
theorem famSep_pairFam_exists {τ : Fin 4} {P Q : Mono N}
    (hP : ∃ d : ℝ, 0 < d ∧ sepPos τ d P) (hQ : ∃ d : ℝ, 0 < d ∧ sepPos τ d Q) :
    ∃ d : ℝ, 0 < d ∧ FamSep d (pairFam τ P Q) := by
  obtain ⟨d₁, hd₁, h₁⟩ := hP
  obtain ⟨d₂, hd₂, h₂⟩ := hQ
  exact ⟨min d₁ d₂, lt_min hd₁ hd₂, famSep_pairFam (lt_min hd₁ hd₂).le
    (sepPos_mono h₁ (min_le_left _ _)) (sepPos_mono h₂ (min_le_right _ _))⟩

#print axioms famSep_pairFam_exists

/-- **Separated positive-time monomials**: some margin `d > 0` works for `sepPos`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the margin. -/
abbrev SepMono (N : ℕ) (τ : Fin 4) : Type := {P : Mono N // ∃ d : ℝ, 0 < d ∧ sepPos τ d P}

/-- Every factor of a separated monomial has positive-time support.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem sepMono_posTime {τ : Fin 4} (P : SepMono N τ) (i : Fin P.1.1) :
    PosTime τ (P.1.2 i).2 := by
  obtain ⟨d, hd, hP⟩ := P.2
  exact ⟨d, hd, hP.1 i⟩

#print axioms sepMono_posTime

/-- The empty monomial is separated, at any margin; `1` is used.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the margin. CHOSEN: the margin
`1`; the empty family has no factor, so every positive margin serves. -/
theorem emptyMono_sep (τ : Fin 4) : ∃ d : ℝ, 0 < d ∧ sepPos τ d (emptyMono N) :=
  ⟨1, one_pos, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩

#print axioms emptyMono_sep

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem timeVec_nonneg (hN : N ≠ 0) (m : ℕ) (τ : Fin 4) (n : ℕ) : 0 ≤ timeVec N m τ n τ := by
  rw [timeVec_self]
  exact mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) m).le (by positivity)

#print axioms timeVec_nonneg

/-- The forward time step of a separated monomial by `dySpacing N m` in direction `τ`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The body steps
by one unit time step, whose time component is non-negative. -/
def SepMono.shift (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : SepMono N τ) : SepMono N τ :=
  ⟨Mono.shift (timeVec N m τ 1) P.1, by
    obtain ⟨d, hd, hP⟩ := P.2
    exact ⟨d, hd, sepPos_shift hP (by
      rw [timeVec_self]
      exact mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) m).le (by norm_num))⟩⟩

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem SepMono.shift_iterate (hN : N ≠ 0) (τ : Fin 4) (m n : ℕ) (P : SepMono N τ) :
    ((SepMono.shift hN τ m)^[n] P).1 = Mono.shift (timeVec N m τ n) P.1 := by
  induction n with
  | zero =>
    show P.1 = Mono.shift (timeVec N m τ ((0 : ℕ) : ℤ)) P.1
    rw [Nat.cast_zero, timeVec_zero, Mono.shift_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show Mono.shift (timeVec N m τ 1) ((SepMono.shift hN τ m)^[n] P).1 = _
    rw [ih, Mono.shift_shift, timeVec_add, Nat.cast_succ]

#print axioms SepMono.shift_iterate

/-- Two half steps are one step, on separated monomials.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `1` is the
half-step offset. -/
theorem SepMono.shift_half (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : SepMono N τ) :
    SepMono.shift hN τ (m + 1) (SepMono.shift hN τ (m + 1) P) = SepMono.shift hN τ m P := by
  apply Subtype.ext
  show Mono.shift (timeVec N (m + 1) τ 1) (Mono.shift (timeVec N (m + 1) τ 1) P.1)
    = Mono.shift (timeVec N m τ 1) P.1
  rw [Mono.shift_shift, timeVec_one_add]

#print axioms SepMono.shift_half

/-- The empty separated monomial, the vacuum before completion.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the number of factors.
CHOSEN: the margin `1`, as in `emptyMono_sep`. -/
def emptySep (N : ℕ) (τ : Fin 4) : SepMono N τ :=
  ⟨⟨0, Fin.elim0⟩, ⟨1, one_pos, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem shift_emptySep (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) :
    SepMono.shift hN τ m (emptySep N τ) = emptySep N τ :=
  Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0))

#print axioms shift_emptySep

end Monomials

/-! ## 3. E on reflected pairs -/

section Pairs

/-- A separated positive-time monomial is, eventually in the step, a vector of the lattice transfer
data `Dk` (`ContinuumCluster.Yv_mem`).

DERIVED: `0` is the excluded colour count and the plane; `1` is the least colour count; `4` in
`Fin 4` is the spacetime dimension. -/
theorem eventually_Yv_mem_sep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (P : SepMono N τ) :
    ∀ᶠ k in atTop,
      Yv ρ k P.1 ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0 := by
  have hmem : ∀ᶠ k in atTop, ∀ i : Fin P.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.2 i).1.sub r).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem (one_le_of_ne_zero hN) τ _ _
      (sepMono_posTime P i))
  filter_upwards [hmem] with k hk
  exact Yv_mem hN ρ τ k P.1 hk

#print axioms eventually_Yv_mem_sep

/-- **Cauchy–Schwarz for the reflected lattice pairing at step `k`.** For monomials whose renormalised
observables lie in the gauge-invariant half-space algebra,
`latSkR(θP ∪ Q)² ≤ latSkR(θP ∪ P) · latSkR(θQ ∪ Q)`: `Transfer.ReflForm.cauchy_schwarz` for the
form of `ContinuumCluster.Dk`, which is the reflected pairing of the step-`k` state
(`ContinuumCluster.latSkR_pairFam_eq`).

DERIVED: `0` is the excluded colour count and the plane; `2` is the square; `4` in `Fin 4` is the
spacetime dimension. -/
theorem sq_latSkR_pairFam_le (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ)
    (P Q : Mono N)
    (hP : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : Yv ρ k Q ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    latSkR hN ρ k (pairFam τ P Q) ^ 2
      ≤ latSkR hN ρ k (pairFam τ P P) * latSkR hN ρ k (pairFam τ Q Q) := by
  have h := (Dk hN τ k).toReflForm.cauchy_schwarz ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k Q, hQ⟩
  have e1 : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k Q, hQ⟩ = latSkR hN ρ k (pairFam τ P Q) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k P Q]
  have e2 : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k P, hP⟩ = latSkR hN ρ k (pairFam τ P P) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k P P]
  have e3 : (Dk hN τ k).form ⟨Yv ρ k Q, hQ⟩ ⟨Yv ρ k Q, hQ⟩ = latSkR hN ρ k (pairFam τ Q Q) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k Q Q]
  calc latSkR hN ρ k (pairFam τ P Q) ^ 2
      = (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k Q, hQ⟩ ^ 2 := by rw [e1]
    _ ≤ (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k P, hP⟩
          * (Dk hN τ k).form ⟨Yv ρ k Q, hQ⟩ ⟨Yv ρ k Q, hQ⟩ := h
    _ = latSkR hN ρ k (pairFam τ P P) * latSkR hN ρ k (pairFam τ Q Q) := by rw [e2, e3]

#print axioms sq_latSkR_pairFam_le

/-- **The square-root form**: `|latSkR(θP ∪ Q)| ≤ √(latSkR(θP ∪ P) · latSkR(θQ ∪ Q))`
(`Real.abs_le_sqrt`).

DERIVED: `0` is the excluded colour count and the plane; `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_latSkR_pairFam_le_sqrt (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    (k : ℕ) (P Q : Mono N)
    (hP : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0)
    (hQ : Yv ρ k Q ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    |latSkR hN ρ k (pairFam τ P Q)|
      ≤ Real.sqrt (latSkR hN ρ k (pairFam τ P P) * latSkR hN ρ k (pairFam τ Q Q)) :=
  Real.abs_le_sqrt (sq_latSkR_pairFam_le hN ρ τ hR k P Q hP hQ)

#print axioms abs_latSkR_pairFam_le_sqrt

/-- The reflected diagonal is non-negative at each step (`form_nonneg` of `ContinuumCluster.Dk`).

DERIVED: `0` is the excluded colour count, the plane and the sign; `4` in `Fin 4` is the spacetime
dimension. -/
theorem latSkR_pairFam_self_nonneg (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    (k : ℕ) (P : Mono N)
    (hP : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    0 ≤ latSkR hN ρ k (pairFam τ P P) := by
  have h := (Dk hN τ k).form_nonneg ⟨Yv ρ k P, hP⟩
  have e : (Dk hN τ k).form ⟨Yv ρ k P, hP⟩ ⟨Yv ρ k P, hP⟩ = latSkR hN ρ k (pairFam τ P P) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k P P]
  exact le_of_le_of_eq h e

#print axioms latSkR_pairFam_self_nonneg

/-- The form along the powers of `T` does not exceed its value at the start (`T_contract`, iterated).

DERIVED: `0` is the base case of the induction; `1` the step. -/
theorem form_T_pow_self_le {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    (x : A) (j : ℕ) : D.form ((D.T ^ j) x) ((D.T ^ j) x) ≤ D.form x x := by
  induction j with
  | zero => exact le_of_eq (by rw [pow_zero, Module.End.one_apply])
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (D.T_contract _).trans ih

#print axioms form_T_pow_self_le

/-- **The reflected diagonal of a forward-shifted monomial is a form value along `T`.** At step
`k ≥ m`, the dyadic time `timeVec N m τ n` is `2^{k−m} n` lattice steps, and
`latSkR(θP' ∪ P') = ⟨T^{2^{k−m} n} Y_P, T^{2^{k−m} n} Y_P⟩` for `P' = P` shifted by it
(`ContinuumCluster.Dk_T_pow`, `ContinuumCluster.Yv_shift`).

DERIVED: `0` is the excluded colour count and the plane; `2` is the halving of the dyadic spacing,
`2^{k−m}` lattice steps per step of `dySpacing N m` (`ContinuumSchwinger.site_dySpacing`); `4` in
`Fin 4` is the spacetime dimension. -/
theorem latSkR_pairFam_shift_eq_form (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    {k m : ℕ} (hk : m ≤ k) (n : ℕ) (P : Mono N)
    (hY : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    latSkR hN ρ k (pairFam τ (Mono.shift (timeVec N m τ n) P) (Mono.shift (timeVec N m τ n) P))
      = (Dk hN τ k).form (((Dk hN τ k).T ^ (2 ^ (k - m) * n)) ⟨Yv ρ k P, hY⟩)
          (((Dk hN τ k).T ^ (2 ^ (k - m) * n)) ⟨Yv ρ k P, hY⟩) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hvec : site (dySpacing N k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ))
      = timeVec N m τ n := by
    unfold timeVec
    rw [site_dySpacing N hk, scaleSite_axisVec]
    congr 2
  rw [Dk_form, Dk_T_pow, ishiftObsL_iterate, Yv_shift ρ k ha _ P, hvec,
    latSkR_pairFam_eq hN ρ τ hR k]

#print axioms latSkR_pairFam_shift_eq_form

/-- **Shifting forward in time does not raise the reflected diagonal at a step**: at `k ≥ m`,
`latSkR(θP' ∪ P') ≤ latSkR(θP ∪ P)` for `P' = P` shifted by `timeVec N m τ n`
(`latSkR_pairFam_shift_eq_form`, `form_T_pow_self_le`).

DERIVED: `0` is the excluded colour count and the plane; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSkR_pairFam_shift_self_le (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    {k m : ℕ} (hk : m ≤ k) (n : ℕ) (P : Mono N)
    (hY : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    latSkR hN ρ k (pairFam τ (Mono.shift (timeVec N m τ n) P) (Mono.shift (timeVec N m τ n) P))
      ≤ latSkR hN ρ k (pairFam τ P P) := by
  rw [latSkR_pairFam_shift_eq_form hN ρ τ hR hk n P hY]
  have e : (Dk hN τ k).form ⟨Yv ρ k P, hY⟩ ⟨Yv ρ k P, hY⟩ = latSkR hN ρ k (pairFam τ P P) := by
    rw [Dk_form, latSkR_pairFam_eq hN ρ τ hR k P P]
  exact le_of_le_of_eq (form_T_pow_self_le (Dk hN τ k) ⟨Yv ρ k P, hY⟩ (2 ^ (k - m) * n)) e

#print axioms latSkR_pairFam_shift_self_le

/-- The same on separated monomials, with the shift as the iterate `SepMono.shift^[n]`.

DERIVED: `0` is the excluded colour count and the plane; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSkR_iterate_self_le (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    {k m : ℕ} (hk : m ≤ k) (n : ℕ) (P : SepMono N τ)
    (hY : Yv ρ k P.1 ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0) :
    latSkR hN ρ k (pairFam τ ((SepMono.shift hN τ m)^[n] P).1 ((SepMono.shift hN τ m)^[n] P).1)
      ≤ latSkR hN ρ k (pairFam τ P.1 P.1) := by
  rw [SepMono.shift_iterate]
  exact latSkR_pairFam_shift_self_le hN ρ τ hR hk n P.1 hY

#print axioms latSkR_iterate_self_le

/-- **E on reflection-diagonal pairs (stated, not proved).** Every separated positive-time monomial
`P` has one constant bounding the reflected second moment `latSkR(θP ∪ P)` eventually in the step.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def DiagBoundSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) : Prop :=
  ∀ P : SepMono N τ, ∃ C : ℝ, ∀ᶠ k in atTop, latSkR hN ρ k (pairFam τ P.1 P.1) ≤ C

/-- **E on reflected pairs (stated, not proved).** Every pair of separated positive-time monomials
`P, Q` has one constant bounding `|latSkR(θP' ∪ Q')|` eventually in the step, at every common dyadic
time shift `P' = SepMono.shift^[n] P`, `Q' = SepMono.shift^[n] Q`: the families the chain reads E on
(`tendsto_pair_sep_of_pairBound` at `n = 0`, `kernSep_iterate_bound_of_pairBound`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
def PairBoundSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) : Prop :=
  ∀ P Q : SepMono N τ, ∃ C : ℝ, ∀ m n : ℕ, ∀ᶠ k in atTop,
    |latSkR hN ρ k (pairFam τ ((SepMono.shift hN τ m)^[n] P).1 ((SepMono.shift hN τ m)^[n] Q).1)|
      ≤ C

/-- **The diagonal bound gives the pair bound.** At a step past `m` where `P`, `Q` and their shifts are
vectors of `Dk`: Cauchy–Schwarz (`sq_latSkR_pairFam_le`), the shifted diagonals at most the unshifted
ones (`latSkR_iterate_self_le`), and those at most `C_P`, `C_Q`; the constant is `√(C_P C_Q)`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem pairBoundSep_of_diagBoundSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ)
    (hD : DiagBoundSep hN ρ τ) : PairBoundSep hN ρ τ := by
  intro P Q
  obtain ⟨CP, hCP⟩ := hD P
  obtain ⟨CQ, hCQ⟩ := hD Q
  refine ⟨Real.sqrt (CP * CQ), fun m n => ?_⟩
  filter_upwards [Filter.eventually_ge_atTop m, hCP, hCQ, eventually_Yv_mem_sep hN ρ τ P,
    eventually_Yv_mem_sep hN ρ τ Q,
    eventually_Yv_mem_sep hN ρ τ ((SepMono.shift hN τ m)^[n] P),
    eventually_Yv_mem_sep hN ρ τ ((SepMono.shift hN τ m)^[n] Q)]
    with k hk hkP hkQ hYP hYQ hYP' hYQ'
  have hcs := sq_latSkR_pairFam_le hN ρ τ hR k _ _ hYP' hYQ'
  have h0P := latSkR_pairFam_self_nonneg hN ρ τ hR k _ hYP'
  have h0Q := latSkR_pairFam_self_nonneg hN ρ τ hR k _ hYQ'
  have hPP := (latSkR_iterate_self_le hN ρ τ hR hk n P hYP).trans hkP
  have hQQ := (latSkR_iterate_self_le hN ρ τ hR hk n Q hYQ).trans hkQ
  exact Real.abs_le_sqrt (hcs.trans (mul_le_mul hPP hQQ h0Q (h0P.trans hPP)))

#print axioms pairBoundSep_of_diagBoundSep

/-- **`UniformBoundSep` gives the diagonal bound**: its constant for the family `θP ∪ P`, which is
separated (`famSep_pairFam_exists`), at the zero translation.

DERIVED: `0` is the excluded colour count, the sign of the separation, the zero translation and the
dyadic level of it; `4` in `Fin 4` is the spacetime dimension. -/
theorem diagBoundSep_of_uniformBoundSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)
    (hB : UniformBoundSep hN ρ) : DiagBoundSep hN ρ τ := by
  intro P
  obtain ⟨d, hd, hF⟩ := famSep_pairFam_exists P.2 P.2
  obtain ⟨C, hC⟩ := hB _ (pairFam τ P.1 P.1) d hd
  have hF0 : FamSep d (fun i => ((pairFam τ P.1 P.1 i).1,
      (pairFam τ P.1 P.1 i).2.translate
        (site (dySpacing N 0) ((fun _ : Fin P.1.1 ⊕ Fin P.1.1 => (0 : ISite)) i)))) := by
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta]
    exact hF
  have h0 := hC 0 (fun _ => 0) hF0
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  exact ⟨C, h0.mono (fun _ hk => (le_abs_self _).trans hk)⟩

#print axioms diagBoundSep_of_uniformBoundSep

/-- **`UniformBoundSep` gives the pair bound** under reflection compatibility
(`diagBoundSep_of_uniformBoundSep`, `pairBoundSep_of_diagBoundSep`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem pairBoundSep_of_uniformBoundSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)
    (hR : ρ.ReflCompat τ) (hB : UniformBoundSep hN ρ) : PairBoundSep hN ρ τ :=
  pairBoundSep_of_diagBoundSep hN ρ τ hR (diagBoundSep_of_uniformBoundSep hN ρ τ hB)

#print axioms pairBoundSep_of_uniformBoundSep

/-- **Existence of every limit the chain consumes, on `PairBoundSep`**: for two separated
positive-time monomials, `latSkR hN ρ k (θP ∪ Q) → kern hN ρ τ P Q` along `ultra`. The bound at
`m = n = 0` is eventual, so the sequence converges along `ultra` (`exists_tendsto_ultra`). The same
conclusion as `tendsto_pair_sep`, which reads `UniformBoundSep`.

DERIVED: `0` is the excluded colour count, the sign of the margins, the dyadic level and the number of
shifts; `4` in `Fin 4` is the spacetime dimension. -/
theorem tendsto_pair_sep_of_pairBound (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)
    (hB : PairBoundSep hN ρ τ) {P Q : Mono N}
    (hP : ∃ d : ℝ, 0 < d ∧ sepPos τ d P) (hQ : ∃ d : ℝ, 0 < d ∧ sepPos τ d Q) :
    Tendsto (fun k => latSkR hN ρ k (pairFam τ P Q)) (ultra : Filter ℕ)
      (𝓝 (kern hN ρ τ P Q)) := by
  obtain ⟨C, hC⟩ := hB ⟨P, hP⟩ ⟨Q, hQ⟩
  have h0 : ∀ᶠ k in atTop, |latSkR hN ρ k (pairFam τ P Q)| ≤ C := by
    have h := hC 0 0
    rwa [Function.iterate_zero_apply, Function.iterate_zero_apply] at h
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_pair_sep_of_pairBound

end Pairs

/-! ## 4. Existence and OS2 on separated monomials -/

section Positivity

/-- **Existence of every limit the chain consumes, under `UniformBoundSep`**: for two separated
positive-time monomials, `latSkR hN ρ k (pairFam τ P Q) → kern hN ρ τ P Q` along `ultra`. The chain
reads the same conclusion from `PairBoundSep` (`tendsto_pair_sep_of_pairBound`).

DERIVED: `0` is the excluded colour count and the sign of the margins; `4` in `Fin 4` is the
spacetime dimension. -/
theorem tendsto_pair_sep (hN : N ≠ 0) (ρ : Renorm N) (hB : UniformBoundSep hN ρ) (τ : Fin 4)
    {P Q : Mono N} (hP : ∃ d : ℝ, 0 < d ∧ sepPos τ d P) (hQ : ∃ d : ℝ, 0 < d ∧ sepPos τ d Q) :
    Tendsto (fun k => latSkR hN ρ k (pairFam τ P Q)) (ultra : Filter ℕ)
      (𝓝 (kern hN ρ τ P Q)) := by
  obtain ⟨d, hd, hF⟩ := famSep_pairFam_exists hP hQ
  exact tendsto_contS_sep hN ρ hB (pairFam τ P Q) hd hF

#print axioms tendsto_pair_sep

/-- **OS2 on separated monomials.** Under `PairBoundSep` and reflection-compatible data, for every
finite set of separated positive-time monomials and real coefficients,
`0 ≤ ∑_{P,Q} c_P c_Q S(θP ∪ Q)`.

DERIVED: `0` is the excluded colour count and the sign concluded; `4` in `Fin 4` is the spacetime
dimension. -/
theorem contS_gram_nonneg_sep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hB : PairBoundSep hN ρ τ)
    (hR : ρ.ReflCompat τ) (s : Finset (SepMono N τ)) (c : SepMono N τ → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kern hN ρ τ P.1 Q.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have htend : Tendsto
      (fun k => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kern hN ρ τ P.1 Q.1)) :=
    tendsto_finset_sum _ (fun P _ => tendsto_finset_sum _
      (fun Q _ => (tendsto_pair_sep_of_pairBound hN ρ τ hB P.2 Q.2).const_mul (c P * c Q)))
  refine ge_of_tendsto htend ?_
  have hmem : ∀ᶠ k in atTop, ∀ P ∈ s, ∀ i : Fin P.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.2 i).1.sub r).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    (Filter.eventually_all_finset s).mpr (fun P _ =>
      Filter.eventually_all.mpr
        (fun i => eventually_smear_sub_mem (one_le_of_ne_zero hN) τ _ _ (sepMono_posTime P i)))
  have hev : ∀ᶠ k in atTop,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1) := by
    filter_upwards [hmem] with k hk
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hsum : ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkR hN ρ k (pairFam τ P.1 Q.1)
        = ∑ P ∈ s, ∑ Q ∈ s, (c P * ρ.zmono k P.1) * (c Q * ρ.zmono k Q.1) * stateK hN k
            (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (ρ.mono k P.1))
              * prodSmear (dySpacing N k) (ρ.mono k Q.1)) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
      rw [latSkR_pairFam hN ρ τ hR, latSk_eq, latS_pairFam _ ha]
      ring
    have hX : (∑ P ∈ s, (c P * ρ.zmono k P.1) • prodSmear (dySpacing N k) (ρ.mono k P.1))
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
      Submodule.sum_mem _ (fun P hP => Submodule.smul_mem _ _
        (HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
          (fun i _ => hk P hP i (ρ.c k (P.1.2 i).1))))
    rw [hsum]
    exact le_of_le_of_eq (stateK_rp hN k τ _ hX)
      (gram_expand (stateK hN k) (LatticeReflection.ireflObs τ 0) s
        (fun P => c P * ρ.zmono k P.1) (fun P => prodSmear (dySpacing N k) (ρ.mono k P.1)))
  exact hev.filter_mono ultra_le

#print axioms contS_gram_nonneg_sep

end Positivity

/-! ## 5. The reflection form and the transfer operators on separated monomials -/

section Form

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)

/-- Finite real combinations of separated positive-time monomials.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
abbrev AmodSep (N : ℕ) (τ : Fin 4) : Type := SepMono N τ →₀ ℝ

/-- The kernel on separated monomials.

DERIVED: no numeral. -/
noncomputable def kernSep (P Q : SepMono N τ) : ℝ := kern hN ρ τ P.1 Q.1

/-- DERIVED: no numeral. -/
theorem kernSep_symm (hR : ρ.ReflCompat τ) (P Q : SepMono N τ) :
    kernSep hN ρ τ P Q = kernSep hN ρ τ Q P :=
  kern_symm hN ρ τ hR P.1 Q.1

#print axioms kernSep_symm

/-- `S(θ(TP) ∪ Q) = S(θP ∪ TQ)`, by dyadic translation invariance of the limit.

DERIVED: `1` is the unit step. -/
theorem kernSep_shift (m : ℕ) (P Q : SepMono N τ) :
    kernSep hN ρ τ (SepMono.shift hN τ m P) Q = kernSep hN ρ τ P (SepMono.shift hN τ m Q) := by
  show kern hN ρ τ (Mono.shift (timeVec N m τ 1) P.1) Q.1
    = kern hN ρ τ P.1 (Mono.shift (timeVec N m τ 1) Q.1)
  unfold kern
  rw [pairFam_shift]
  exact contS_translate hN ρ _ m (axisVec τ (-1))

#print axioms kernSep_shift

/-- **The reflection form** `⟨c, d⟩ = ∑_{P,Q} c_P d_Q S(θP ∪ Q)` on separated monomials.

DERIVED: no numeral. -/
noncomputable def formSep (c d : AmodSep N τ) : ℝ :=
  c.sum (fun P a => d.sum (fun Q b => a * b * kernSep hN ρ τ P Q))

/-- DERIVED: no numeral. -/
theorem formSep_add_left (c c' d : AmodSep N τ) :
    formSep hN ρ τ (c + c') d = formSep hN ρ τ c d + formSep hN ρ τ c' d := by
  unfold formSep
  exact Finsupp.sum_add_index' (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

#print axioms formSep_add_left

/-- DERIVED: no numeral. -/
theorem formSep_smul_left (r : ℝ) (c d : AmodSep N τ) :
    formSep hN ρ τ (r • c) d = r * formSep hN ρ τ c d := by
  unfold formSep
  have h1 : (r • c).sum (fun P a => d.sum (fun Q b => a * b * kernSep hN ρ τ P Q))
      = c.sum (fun P a => d.sum (fun Q b => (r • a) * b * kernSep hN ρ τ P Q)) :=
    Finsupp.sum_smul_index' (fun P => by simp)
  rw [h1, Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun P _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun Q _ => ?_)
  rw [smul_eq_mul]
  ring

#print axioms formSep_smul_left

/-- DERIVED: no numeral. -/
theorem formSep_symm (hR : ρ.ReflCompat τ) (c d : AmodSep N τ) :
    formSep hN ρ τ c d = formSep hN ρ τ d c := by
  unfold formSep
  rw [Finsupp.sum_comm c d (fun P a Q b => a * b * kernSep hN ρ τ P Q)]
  refine Finsupp.sum_congr (fun Q _ => Finsupp.sum_congr (fun P _ => ?_))
  simp only [kernSep_symm hN ρ τ hR P Q]
  ring

#print axioms formSep_symm

/-- **Positivity of the form** is `contS_gram_nonneg_sep`.

DERIVED: `0` is the sign. -/
theorem formSep_nonneg (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (c : AmodSep N τ) :
    0 ≤ formSep hN ρ τ c c := by
  show 0 ≤ ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q * kern hN ρ τ P.1 Q.1
  exact contS_gram_nonneg_sep hN ρ τ hB hR c.support (fun P => c P)

#print axioms formSep_nonneg

/-- DERIVED: `0` is the zero combination. -/
theorem formSep_zero_left (d : AmodSep N τ) : formSep hN ρ τ 0 d = 0 := by
  unfold formSep
  exact Finsupp.sum_zero_index

#print axioms formSep_zero_left

/-- DERIVED: `0` is the zero combination. -/
theorem formSep_zero_right (c : AmodSep N τ) : formSep hN ρ τ c 0 = 0 := by
  simp [formSep]

#print axioms formSep_zero_right

/-- DERIVED: no numeral. -/
theorem formSep_single (P Q : SepMono N τ) (a b : ℝ) :
    formSep hN ρ τ (Finsupp.single P a) (Finsupp.single Q b) = a * b * kernSep hN ρ τ P Q := by
  unfold formSep
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals simp

#print axioms formSep_single

/-- **The continuum reflection form on separated monomials**, a `Transfer.ReflForm`.

DERIVED: no numeral. -/
noncomputable def contReflFormSep (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) :
    Transfer.ReflForm (AmodSep N τ) where
  form := formSep hN ρ τ
  form_symm := formSep_symm hN ρ τ hR
  form_add_left := formSep_add_left hN ρ τ
  form_smul_left := formSep_smul_left hN ρ τ
  form_nonneg := formSep_nonneg hN ρ τ hB hR

/-- DERIVED: no numeral. -/
theorem formSep_mapDomain_left (g : SepMono N τ → SepMono N τ) (c d : AmodSep N τ) :
    formSep hN ρ τ (Finsupp.mapDomain g c) d
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernSep hN ρ τ (g P) Q)) := by
  unfold formSep
  exact Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

#print axioms formSep_mapDomain_left

/-- DERIVED: no numeral. -/
theorem formSep_mapDomain_right (g : SepMono N τ → SepMono N τ) (c d : AmodSep N τ) :
    formSep hN ρ τ c (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernSep hN ρ τ P (g Q))) := by
  unfold formSep
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

#print axioms formSep_mapDomain_right

/-- DERIVED: no numeral. -/
theorem formSep_mapDomain (g : SepMono N τ → SepMono N τ) (c d : AmodSep N τ) :
    formSep hN ρ τ (Finsupp.mapDomain g c) (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernSep hN ρ τ (g P) (g Q))) := by
  rw [formSep_mapDomain_left]
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

#print axioms formSep_mapDomain

/-- **The time step at level `m`** on separated monomials, extended linearly.

DERIVED: no numeral. -/
noncomputable def TmSep (m : ℕ) : AmodSep N τ →ₗ[ℝ] AmodSep N τ :=
  Finsupp.lmapDomain ℝ ℝ (SepMono.shift hN τ m)

/-- DERIVED: no numeral. -/
theorem TmSep_symm (m : ℕ) (c d : AmodSep N τ) :
    formSep hN ρ τ (TmSep hN τ m c) d = formSep hN ρ τ c (TmSep hN τ m d) := by
  show formSep hN ρ τ (Finsupp.mapDomain (SepMono.shift hN τ m) c) d
    = formSep hN ρ τ c (Finsupp.mapDomain (SepMono.shift hN τ m) d)
  rw [formSep_mapDomain_left, formSep_mapDomain_right]
  refine Finsupp.sum_congr (fun P _ => Finsupp.sum_congr (fun Q _ => ?_))
  simp only [kernSep_shift]

#print axioms TmSep_symm

/-- DERIVED: no numeral. -/
theorem TmSep_iterate (m n : ℕ) (c : AmodSep N τ) :
    (⇑(TmSep hN τ m))^[n] c = Finsupp.mapDomain ((SepMono.shift hN τ m)^[n]) c := by
  induction n with
  | zero => exact Finsupp.mapDomain_id.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
    show Finsupp.mapDomain (SepMono.shift hN τ m)
        (Finsupp.mapDomain ((SepMono.shift hN τ m)^[n]) c) = _
    rw [← Finsupp.mapDomain_comp]

#print axioms TmSep_iterate

/-- `T_m = T_{m+1} ∘ T_{m+1}` on `AmodSep`.

DERIVED: `1` is the half-step offset. -/
theorem TmSep_half (m : ℕ) (c : AmodSep N τ) :
    TmSep hN τ m c = TmSep hN τ (m + 1) (TmSep hN τ (m + 1) c) := by
  show Finsupp.mapDomain (SepMono.shift hN τ m) c
    = Finsupp.mapDomain (SepMono.shift hN τ (m + 1))
        (Finsupp.mapDomain (SepMono.shift hN τ (m + 1)) c)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  exact (SepMono.shift_half hN τ m P).symm

#print axioms TmSep_half

/-- **OS0 along the shifts, under `UniformBoundSep`**: the kernel of iterated shifts of two separated
monomials is bounded uniformly in the number of shifts. The shifted pair is separated at the smaller of
the two margins, for every number of shifts. The reconstruction reads the same conclusion from
`PairBoundSep` (`kernSep_iterate_bound_of_pairBound`).

DERIVED: `0` is the sign of the margins. -/
theorem kernSep_iterate_bound (hB : UniformBoundSep hN ρ) (m : ℕ) (P Q : SepMono N τ) :
    ∃ C : ℝ, ∀ n : ℕ,
      |kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P) ((SepMono.shift hN τ m)^[n] Q)| ≤ C := by
  obtain ⟨d₁, hd₁, h₁⟩ := P.2
  obtain ⟨d₂, hd₂, h₂⟩ := Q.2
  have hd : 0 < min d₁ d₂ := lt_min hd₁ hd₂
  obtain ⟨C, hC⟩ := exists_abs_contS_le_sep hN ρ hB (pairFam τ P.1 Q.1) hd
  refine ⟨C, fun n => ?_⟩
  have hsep : FamSep (min d₁ d₂) (pairFam τ (Mono.shift (timeVec N m τ n) P.1)
      (Mono.shift (timeVec N m τ n) Q.1)) :=
    famSep_pairFam hd.le (sepPos_shift (sepPos_mono h₁ (min_le_left _ _)) (timeVec_nonneg hN m τ n))
      (sepPos_shift (sepPos_mono h₂ (min_le_right _ _)) (timeVec_nonneg hN m τ n))
  rw [pairFam_shiftN] at hsep
  unfold kernSep kern
  rw [SepMono.shift_iterate, SepMono.shift_iterate, pairFam_shiftN]
  exact hC m _ hsep

#print axioms kernSep_iterate_bound

/-- **`kernSep_iterate_bound` on `PairBoundSep`**, with the same conclusion: the kernel of iterated
shifts of two separated monomials is bounded uniformly in the number of shifts. The pair bound at
`(m, n)` passes to the limit along `ultra` (`tendsto_pair_sep_of_pairBound`).

DERIVED: no numeral. -/
theorem kernSep_iterate_bound_of_pairBound (hB : PairBoundSep hN ρ τ) (m : ℕ) (P Q : SepMono N τ) :
    ∃ C : ℝ, ∀ n : ℕ,
      |kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P) ((SepMono.shift hN τ m)^[n] Q)| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB P Q
  exact ⟨C, fun n => le_of_tendsto
    (tendsto_pair_sep_of_pairBound hN ρ τ hB ((SepMono.shift hN τ m)^[n] P).2
      ((SepMono.shift hN τ m)^[n] Q).2).abs
    ((hC m n).filter_mono ultra_le)⟩

#print axioms kernSep_iterate_bound_of_pairBound

/-- The form of iterated shifts is bounded uniformly in the number of shifts.

DERIVED: no numeral. -/
theorem formSep_iterate_le (hB : PairBoundSep hN ρ τ) (m : ℕ) (c : AmodSep N τ) :
    ∃ B : ℝ, ∀ n : ℕ,
      formSep hN ρ τ ((⇑(TmSep hN τ m))^[n] c) ((⇑(TmSep hN τ m))^[n] c) ≤ B := by
  choose C hC using kernSep_iterate_bound_of_pairBound hN ρ τ hB m
  refine ⟨∑ P ∈ c.support, ∑ Q ∈ c.support, |c P| * |c Q| * C P Q, fun n => ?_⟩
  rw [TmSep_iterate, formSep_mapDomain]
  show ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q
      * kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P) ((SepMono.shift hN τ m)^[n] Q) ≤ _
  refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
  calc c P * c Q * kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P) ((SepMono.shift hN τ m)^[n] Q)
      ≤ |c P * c Q * kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P)
          ((SepMono.shift hN τ m)^[n] Q)| := le_abs_self _
    _ = |c P| * |c Q| * |kernSep hN ρ τ ((SepMono.shift hN τ m)^[n] P)
          ((SepMono.shift hN τ m)^[n] Q)| := by rw [abs_mul, abs_mul]
    _ ≤ |c P| * |c Q| * C P Q :=
        mul_le_mul_of_nonneg_left (hC P Q n) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

#print axioms formSep_iterate_le

/-- **The time step contracts the form**, by iterated Schwarz with the bound of
`kernSep_iterate_bound_of_pairBound`.

DERIVED: no numeral. -/
theorem TmSep_contract (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (m : ℕ)
    (c : AmodSep N τ) :
    formSep hN ρ τ (TmSep hN τ m c) (TmSep hN τ m c) ≤ formSep hN ρ τ c c := by
  obtain ⟨B, hB'⟩ := formSep_iterate_le hN ρ τ hB m c
  exact SchwarzIteration.contract_of_bounded_orbit (contReflFormSep hN ρ τ hB hR)
    (⇑(TmSep hN τ m)) (TmSep_symm hN ρ τ m) c B hB'

#print axioms TmSep_contract

/-- **The continuum transfer data on separated monomials at the dyadic step `dySpacing N m`.** The
witness `hB` enters only the proof fields `form_nonneg` and `T_contract`, so the data does not depend on
which witness is given.

DERIVED: `1` is the coefficient of the vacuum. -/
noncomputable def contTransferSep (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (m : ℕ) :
    Transfer.TransferData (AmodSep N τ) where
  toReflForm := contReflFormSep hN ρ τ hB hR
  T := TmSep hN τ m
  vac := Finsupp.single (emptySep N τ) 1
  T_symm := TmSep_symm hN ρ τ m
  T_contract := TmSep_contract hN ρ τ hB hR m
  T_vac := by
    show Finsupp.mapDomain (SepMono.shift hN τ m) (Finsupp.single (emptySep N τ) 1)
      = Finsupp.single (emptySep N τ) 1
    rw [Finsupp.mapDomain_single, shift_emptySep]
  vac_norm := by
    show formSep hN ρ τ (Finsupp.single (emptySep N τ) 1) (Finsupp.single (emptySep N τ) 1) = 1
    rw [formSep_single, one_mul, one_mul]
    exact kern_empty hN ρ τ

/-- **Positivity of the transfer operator**: `⟨c, T_m c⟩ = ⟨T_{m+1} c, T_{m+1} c⟩ ≥ 0`.

DERIVED: `1` is the half-step offset. -/
theorem positiveTransfer_sep (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (m : ℕ) :
    GNSHilbert.PositiveTransfer (contTransferSep hN ρ τ hB hR m) := by
  intro c
  show 0 ≤ formSep hN ρ τ c (TmSep hN τ m c)
  rw [TmSep_half, ← TmSep_symm hN ρ τ (m + 1)]
  exact formSep_nonneg hN ρ τ hB hR _

#print axioms positiveTransfer_sep

end Form

/-! ## 6. The reconstruction on separated monomials -/

section Reconstruction

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hB : PairBoundSep hN ρ τ)
  (hR : ρ.ReflCompat τ)

/-- The vector of the separated monomial `P` in the reconstructed Hilbert space.

DERIVED: `1` the coefficient, `0` the imaginary component. -/
noncomputable def vecOfSep (m : ℕ) (P : SepMono N τ) :
    GNSHilbert.H (contTransferSep hN ρ τ hB hR m).toReflForm :=
  ((GNSHilbert.Pre.ofPair (contTransferSep hN ρ τ hB hR m).toReflForm (Finsupp.single P 1) 0
    : GNSHilbert.Pre (contTransferSep hN ρ τ hB hR m).toReflForm)
    : GNSHilbert.H (contTransferSep hN ρ τ hB hR m).toReflForm)

/-- **The reconstruction reads the Schwinger functions**: `⟪vecOfSep P, vecOfSep Q⟫ = S(θP ∪ Q)`.

DERIVED: `1` the coefficients, `0` the imaginary parts. -/
theorem inner_vecOfSep (m : ℕ) (P Q : SepMono N τ) :
    inner ℂ (vecOfSep hN ρ τ hB hR m P) (vecOfSep hN ρ τ hB hR m Q)
      = (kern hN ρ τ P.1 Q.1 : ℂ) := by
  unfold vecOfSep
  rw [GNSHilbert.inner_coe]
  refine OSPositivity.ceq ?_ ?_
  · rw [OSPositivity.cform_re, Complex.ofReal_re]
    show formSep hN ρ τ (Finsupp.single P 1) (Finsupp.single Q 1) + formSep hN ρ τ 0 0
      = kern hN ρ τ P.1 Q.1
    rw [formSep_single, formSep_zero_left, one_mul, one_mul, add_zero]
    rfl
  · rw [OSPositivity.cform_im, Complex.ofReal_im]
    show formSep hN ρ τ (Finsupp.single P 1) 0 - formSep hN ρ τ 0 (Finsupp.single Q 1) = 0
    rw [formSep_zero_right, formSep_zero_left, sub_zero]

#print axioms inner_vecOfSep

/-- **Requirement E on `PairBoundSep`.** At every `SU(N)`, `N ≠ 0`, every renormalisation `ρ`
with `PairBoundSep` and reflection compatibility, every time direction `τ` and every dyadic time
step `dySpacing N m`: a complete complex Hilbert space, a unit vacuum, a self-adjoint transfer
operator fixing it with spectrum in `[0, 1]`, and `⟪vecOfSep P, vecOfSep Q⟫ = S(θP ∪ Q)` for every
pair of separated positive-time monomials.

DERIVED: `1` is the vacuum norm and the top of the spectrum; `0` its bottom. -/
theorem continuum_reconstruction_sep (m : ℕ) :
    CompleteSpace (GNSHilbert.H (contTransferSep hN ρ τ hB hR m).toReflForm)
    ∧ ‖GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
        (contTransferSep hN ρ τ hB hR m).vac‖ = 1
    ∧ IsSelfAdjoint (GNSHilbert.opT (contTransferSep hN ρ τ hB hR m))
    ∧ GNSHilbert.opT (contTransferSep hN ρ τ hB hR m)
        (GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
          (contTransferSep hN ρ τ hB hR m).vac)
      = GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
          (contTransferSep hN ρ τ hB hR m).vac
    ∧ spectrum ℝ (GNSHilbert.opT (contTransferSep hN ρ τ hB hR m)) ⊆ Set.Icc 0 1
    ∧ ∀ P Q : SepMono N τ,
        inner ℂ (vecOfSep hN ρ τ hB hR m P) (vecOfSep hN ρ τ hB hR m Q)
          = (kern hN ρ τ P.1 Q.1 : ℂ) :=
  ⟨GNSHilbert.complete_H _, GNSHilbert.norm_Omega_vac _, GNSHilbert.isSelfAdjoint_opT _,
    GNSHilbert.opT_Omega _,
    fun x hx => ⟨GNSHilbert.spectrum_opT_nonneg _ (positiveTransfer_sep hN ρ τ hB hR m) hx,
      (GNSHilbert.spectrum_opT_subset_unit_interval _ hx).2⟩,
    inner_vecOfSep hN ρ τ hB hR m⟩

#print axioms continuum_reconstruction_sep

end Reconstruction

/-! ## 7. Clustering on separated monomials -/

section Cluster

/-- **OS4 for the limit on separated monomials, from `FixedWindowDecay`.** At `2 ≤ N`, a window
`L > 0`, `FixedWindowDecay τ 0 hN L`, `PairBoundSep` and reflection-compatible data, there is
`c > 0` such that for all separated positive-time monomials `P`, `Q` and every dyadic time
`t = dySpacing N m · n`, `n ∈ ℕ`, along `τ`,

    (S(θP ∪ T_t Q) − S(θP) S(Q))² ≤ exp(−2 (c/L) t) · S(θP ∪ P) · (S(θQ ∪ Q) − S(Q)²).

DERIVED: `2 ≤ N` is `gapAt_physical_of_fixedWindowDecay`'s; `2` is also the square; `0` is the
excluded colour count, the plane of `FixedWindowDecay τ 0`, and the sign of `c` and of `L`; `4` in
`Fin 4` is the spacetime dimension. -/
theorem contS_cluster_of_fixedWindowDecay_sep (hN2 : 2 ≤ N) (hN : N ≠ 0) (ρ : Renorm N)
    (τ : Fin 4) (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) :
    ∃ c : ℝ, 0 < c ∧ ∀ (P Q : SepMono N τ) (m n : ℕ),
      (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2
        ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
          * (kern hN ρ τ P.1 P.1
            * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hN1 := one_le_of_ne_zero hN
  obtain ⟨c, hc, hev⟩ := WeakCouplingWindow.gapAt_physical_of_fixedWindowDecay τ 0 hN2 hN hL hW
  have hevk : ∀ᶠ k in atTop, ∃ r : ℝ, TransferGap.GapAt (Dk hN τ k) r
      ∧ PeriodicContent.PeriodicClayGapAt τ 0 hN (dyBeta hN1 k) r
      ∧ c / L ≤ -Real.log r / AsymptoticScaling.aRun N (dyBeta hN1 k) :=
    (tendsto_dyBeta hN1).eventually hev
  refine ⟨c, hc, fun P Q m n => ?_⟩
  have hmemP : ∀ᶠ k in atTop, ∀ i : Fin P.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.2 i).1.sub r).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (sepMono_posTime P i))
  have hmemQ : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((Q.1.2 i).1.sub r).1 (Q.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (sepMono_posTime Q i))
  have hQn : ∃ d : ℝ, 0 < d ∧ sepPos τ d (Mono.shift (timeVec N m τ n) Q.1) := by
    obtain ⟨d, hd, hQ'⟩ := Q.2
    exact ⟨d, hd, sepPos_shift hQ' (timeVec_nonneg hN m τ n)⟩
  have hE : ∃ d : ℝ, 0 < d ∧ sepPos τ d (emptyMono N) := emptyMono_sep τ
  have hf : Tendsto (fun k => (latSkR hN ρ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
        - latSkR hN ρ k (pairFam τ P.1 (emptyMono N))
          * latSkR hN ρ k (pairFam τ (emptyMono N) Q.1)) ^ 2) (ultra : Filter ℕ)
      (𝓝 ((kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2)) :=
    ((tendsto_pair_sep_of_pairBound hN ρ τ hB P.2 hQn).sub
      ((tendsto_pair_sep_of_pairBound hN ρ τ hB P.2 hE).mul
        (tendsto_pair_sep_of_pairBound hN ρ τ hB hE Q.2))).pow 2
  have hg : Tendsto (fun k => Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (latSkR hN ρ k (pairFam τ P.1 P.1)
          * (latSkR hN ρ k (pairFam τ Q.1 Q.1)
            - latSkR hN ρ k (pairFam τ (emptyMono N) Q.1) ^ 2))) (ultra : Filter ℕ)
      (𝓝 (Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)))) :=
    ((tendsto_pair_sep_of_pairBound hN ρ τ hB P.2 P.2).mul
      ((tendsto_pair_sep_of_pairBound hN ρ τ hB Q.2 Q.2).sub
        ((tendsto_pair_sep_of_pairBound hN ρ τ hB hE Q.2).pow 2))).const_mul _
  refine le_of_tendsto_of_tendsto hf hg ?_
  have hevLE : ∀ᶠ k in atTop,
      (latSkR hN ρ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
        - latSkR hN ρ k (pairFam τ P.1 (emptyMono N))
          * latSkR hN ρ k (pairFam τ (emptyMono N) Q.1)) ^ 2
      ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n))
        * (latSkR hN ρ k (pairFam τ P.1 P.1)
          * (latSkR hN ρ k (pairFam τ Q.1 Q.1)
            - latSkR hN ρ k (pairFam τ (emptyMono N) Q.1) ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop m, hevk, hmemP, hmemQ] with k hk hkr hkP hkQ
    obtain ⟨r, hg, hclay, hrate⟩ := hkr
    have ha := dySpacing_pos hN1 k
    have hr0 : 0 < r := hclay.1
    have hvec : site (dySpacing N k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ))
        = timeVec N m τ n := by
      unfold timeVec
      rw [site_dySpacing N hk, scaleSite_axisVec]
      congr 2
    obtain ⟨hcl, hY⟩ := lattice_cluster hN ρ τ hR k hr0.le hg P.1 Q.1
      (Yv_mem hN ρ τ k P.1 hkP) (Yv_mem hN ρ τ k Q.1 hkQ) (2 ^ (k - m) * n)
    rw [hvec] at hcl
    have hlog : Real.log r ≤ -(c / L) * dySpacing N k := by
      have h1 := hrate
      rw [aRun_dyBeta, le_div_iff₀ ha] at h1
      linarith
    have hr_le : r ≤ Real.exp (-(c / L) * dySpacing N k) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.mpr hlog
    have hpow : r ^ (2 * (2 ^ (k - m) * n)) ≤ Real.exp (-(2 * (c / L)) * (dySpacing N m * n)) := by
      calc r ^ (2 * (2 ^ (k - m) * n))
          ≤ Real.exp (-(c / L) * dySpacing N k) ^ (2 * (2 ^ (k - m) * n)) :=
            pow_le_pow_left₀ hr0.le hr_le _
        _ = Real.exp (((2 * (2 ^ (k - m) * n) : ℕ) : ℝ) * (-(c / L) * dySpacing N k)) :=
            (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(2 * (c / L)) * (dySpacing N m * n)) := by
            rw [← dySpacing_mul_pow N hk]
            push_cast
            congr 1
            ring
    exact hcl.trans (mul_le_mul_of_nonneg_right hpow hY)
  exact hevLE.filter_mono ultra_le

#print axioms contS_cluster_of_fixedWindowDecay_sep

end Cluster

/-! ## 8. From clustering to the gap -/

section Gap

/-- `a² ≤ E² Y` with `0 ≤ E` gives `|a| ≤ E √Y`.

DERIVED: `2` is the square; `0` is the sign of `E`. -/
theorem abs_le_mul_sqrt_of_sq_le_sep {a E Y : ℝ} (hE : 0 ≤ E) (h : a ^ 2 ≤ E ^ 2 * Y) :
    |a| ≤ E * Real.sqrt Y := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hE, ← Real.sqrt_mul (sq_nonneg E)]
  exact Real.sqrt_le_sqrt h

#print axioms abs_le_mul_sqrt_of_sq_le_sep

/-- **`GapAt` from per-vector decay of the form at even separations.** If every `x` orthogonal to
the vacuum has a constant `K` with `D.form x ((D.T ^ (2 n)) x) ≤ K r^{2n}` for all `n`, and
`0 ≤ r`, then `GapAt D r`. The constant is chosen after the vector.
`ClayCapstone.absolute_decay_of_form_decay` gives `‖Tqⁿ [x]‖ ≤ K' rⁿ`,
`SecondEigenvalue.norm_le_of_absolute_iterate_bound` gives `‖Tq [x]‖ ≤ r ‖[x]‖`, and the norms square
to the form.

DERIVED: `0` is the lower bound on `r` and the vanishing pairing with the vacuum; `2` is the doubling
of the separation and `GapAt`'s exponent. -/
theorem gapAt_of_per_vector_form_decay {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x : A, D.form x D.vac = 0 →
      ∃ K : ℝ, ∀ n : ℕ, D.form x ((D.T ^ (2 * n)) x) ≤ K * r ^ (2 * n)) :
    TransferGap.GapAt D r := by
  intro x hx
  obtain ⟨K, hK⟩ := h x hx
  obtain ⟨K', hK'⟩ := ClayCapstone.absolute_decay_of_form_decay D x hr hK
  have hb : ‖D.Tq (Transfer.GNS.mk D.toReflForm x)‖ ≤ r * ‖Transfer.GNS.mk D.toReflForm x‖ :=
    SecondEigenvalue.norm_le_of_absolute_iterate_bound D.Tq D.Tq_isSymmetric hr hK'
  rw [D.Tq_mk] at hb
  have hTx : ‖Transfer.GNS.mk D.toReflForm (D.T x)‖ * ‖Transfer.GNS.mk D.toReflForm (D.T x)‖
      = D.form (D.T x) (D.T x) := Transfer.GNS.norm_mk_mul_norm_mk _
  have hxx : ‖Transfer.GNS.mk D.toReflForm x‖ * ‖Transfer.GNS.mk D.toReflForm x‖ = D.form x x :=
    Transfer.GNS.norm_mk_mul_norm_mk _
  have hnn : 0 ≤ ‖Transfer.GNS.mk D.toReflForm (D.T x)‖ := norm_nonneg _
  have hnx : 0 ≤ ‖Transfer.GNS.mk D.toReflForm x‖ := norm_nonneg _
  nlinarith [hb, hTx, hxx, hnn, hnx, mul_nonneg hr hnx]

#print axioms gapAt_of_per_vector_form_decay

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)

/-- The form of a combination against a translate of itself, as a double sum of Schwinger functions.

DERIVED: no numeral. -/
theorem formSep_pow (m j : ℕ) (x : AmodSep N τ) :
    formSep hN ρ τ x ((TmSep hN τ m ^ j) x)
      = ∑ P ∈ x.support, ∑ Q ∈ x.support,
          x P * x Q * kern hN ρ τ P.1 (Mono.shift (timeVec N m τ j) Q.1) := by
  rw [Module.End.pow_apply, TmSep_iterate, formSep_mapDomain_right]
  show ∑ P ∈ x.support, ∑ Q ∈ x.support,
      x P * x Q * kernSep hN ρ τ P ((SepMono.shift hN τ m)^[j] Q) = _
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  show x P * x Q * kern hN ρ τ P.1 ((SepMono.shift hN τ m)^[j] Q).1 = _
  rw [SepMono.shift_iterate]

#print axioms formSep_pow

/-- The form of a combination against the vacuum.

DERIVED: `1` is the coefficient of the vacuum. -/
theorem formSep_vac_right (x : AmodSep N τ) :
    formSep hN ρ τ x (Finsupp.single (emptySep N τ) 1)
      = ∑ P ∈ x.support, x P * kern hN ρ τ P.1 (emptyMono N) := by
  show ∑ P ∈ x.support, (Finsupp.single (emptySep N τ) (1 : ℝ)).sum
      (fun Q b => x P * b * kernSep hN ρ τ P Q) = _
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finsupp.sum_single_index]
  · show x P * 1 * kern hN ρ τ P.1 (emptyMono N) = x P * kern hN ρ τ P.1 (emptyMono N)
    rw [mul_one]
  · simp

#print axioms formSep_vac_right

/-- **Per-vector decay from clustering.** With reflection-compatible data, if the reflected clustering bound holds at rate `γ` for
all separated monomials at the dyadic step `m`, then every combination `x` orthogonal to the vacuum
has a constant `K` with `⟨x, T_mʲ x⟩ ≤ K · exp(−γ · dySpacing N m)ʲ` for all `j`. Both vacuum sums of
`x` vanish, so `⟨x, T_mʲ x⟩` is the double sum of connected functions, each bounded through the
clustering hypothesis by `exp(−γ · dySpacing N m)ʲ · √(S(θP ∪ P)(S(θQ ∪ Q) − S(Q)²))`.

DERIVED: `2` is the square and the doubling in the clustering rate; `1` the vacuum coefficient; `0`
the vanishing pairing with the vacuum. -/
theorem form_pow_le_of_cluster_sep (hR : ρ.ReflCompat τ) (m : ℕ) {γ : ℝ}
    (hcl : ∀ (P Q : SepMono N τ) (n : ℕ),
      (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2
        ≤ Real.exp (-(2 * γ) * (dySpacing N m * n))
          * (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)))
    (x : AmodSep N τ) (hx : formSep hN ρ τ x (Finsupp.single (emptySep N τ) 1) = 0) :
    ∃ K : ℝ, ∀ j : ℕ,
      formSep hN ρ τ x ((TmSep hN τ m ^ j) x) ≤ K * Real.exp (-γ * dySpacing N m) ^ j := by
  have hr0 : 0 ≤ Real.exp (-γ * dySpacing N m) := (Real.exp_pos _).le
  have hexp : ∀ j : ℕ, Real.exp (-(2 * γ) * (dySpacing N m * j))
      = (Real.exp (-γ * dySpacing N m) ^ j) ^ 2 := by
    intro j
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hvacR : ∑ P ∈ x.support, x P * kern hN ρ τ P.1 (emptyMono N) = 0 := by
    rw [← formSep_vac_right hN ρ τ x]
    exact hx
  have hvacL : ∑ Q ∈ x.support, x Q * kern hN ρ τ (emptyMono N) Q.1 = 0 := by
    have h : ∀ Q ∈ x.support, x Q * kern hN ρ τ (emptyMono N) Q.1
        = x Q * kern hN ρ τ Q.1 (emptyMono N) :=
      fun Q _ => by rw [kern_symm hN ρ τ hR (emptyMono N) Q.1]
    rw [Finset.sum_congr rfl h]
    exact hvacR
  refine ⟨∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Real.sqrt
      (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)),
    fun j => ?_⟩
  have hconn : ∀ P Q : SepMono N τ,
      |kern hN ρ τ P.1 (Mono.shift (timeVec N m τ j) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1|
        ≤ Real.exp (-γ * dySpacing N m) ^ j * Real.sqrt
          (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)) := by
    intro P Q
    have h := hcl P Q j
    rw [hexp j] at h
    exact abs_le_mul_sqrt_of_sq_le_sep (pow_nonneg hr0 j) h
  have hsplit : ∑ P ∈ x.support, ∑ Q ∈ x.support,
        x P * x Q * kern hN ρ τ P.1 (Mono.shift (timeVec N m τ j) Q.1)
      = ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ j) Q.1)
            - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1)
        + ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  have hzero : ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
      * (kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) = 0 := by
    have h : ∀ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
        * (kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1)
        = x P * kern hN ρ τ P.1 (emptyMono N)
          * ∑ Q ∈ x.support, x Q * kern hN ρ τ (emptyMono N) Q.1 := by
      intro P _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      ring
    rw [Finset.sum_congr rfl h, hvacL]
    simp
  rw [formSep_pow, hsplit, hzero, add_zero]
  calc ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ j) Q.1)
            - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1)
      ≤ ∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q|
          * (Real.exp (-γ * dySpacing N m) ^ j * Real.sqrt
            (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1
              - kern hN ρ τ (emptyMono N) Q.1 ^ 2))) := by
        refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hconn P Q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Real.sqrt
          (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2)))
          * Real.exp (-γ * dySpacing N m) ^ j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring

#print axioms form_pow_le_of_cluster_sep

/-- **`GapAt` at each dyadic step from the clustering bound at rate `γ`**:
`GapAt (contTransferSep … m) (exp(−γ · dySpacing N m))`.

DERIVED: `2` is the doubling in the clustering rate and the separation `2n` fed to
`gapAt_of_per_vector_form_decay`; `0` the sign of the exponential. -/
theorem gapAt_sep_of_cluster (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (m : ℕ) {γ : ℝ}
    (hcl : ∀ (P Q : SepMono N τ) (n : ℕ),
      (kern hN ρ τ P.1 (Mono.shift (timeVec N m τ n) Q.1)
          - kern hN ρ τ P.1 (emptyMono N) * kern hN ρ τ (emptyMono N) Q.1) ^ 2
        ≤ Real.exp (-(2 * γ) * (dySpacing N m * n))
          * (kern hN ρ τ P.1 P.1 * (kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2))) :
    TransferGap.GapAt (contTransferSep hN ρ τ hB hR m) (Real.exp (-γ * dySpacing N m)) := by
  refine gapAt_of_per_vector_form_decay _ (Real.exp_pos _).le (fun x hx => ?_)
  obtain ⟨K, hK⟩ := form_pow_le_of_cluster_sep hN ρ τ hR m hcl x hx
  exact ⟨K, fun n => hK (2 * n)⟩

#print axioms gapAt_sep_of_cluster

end Gap

/-! ## 9. The continuum gap -/

section Headline

/-- **M in the continuum, on `PairBoundSep`.** At `2 ≤ N`, a window `L > 0`,
`FixedWindowDecay τ 0 hN L`, `PairBoundSep` and reflection-compatible data, there is `c > 0`
such that at every dyadic step `m`, with `r_m = exp(−(c/L) · dySpacing N m)`:

1. `0 < r_m < 1`;
2. `GapAt` of the reconstructed transfer data at `r_m`;
3. `‖opT u‖ ≤ r_m ‖u‖` for every `u` orthogonal to the vacuum in the completed Hilbert space;
4. `spectrum ℝ opT ⊆ {1} ∪ [0, r_m]`;
5. `1` is the greatest element of the spectrum.

The rate `c/L` is the same at every `m`: a spectral gap of physical size at least `c/L` for the transfer operator over the dyadic time
`dySpacing N m`. The Hilbert space may be spanned by the vacuum; `exists_orth_ne_zero_sep` gives it a
non-zero vacuum-orthogonal vector under `ConnectedTwoPointNonzero`.

DERIVED: `2 ≤ N` is `gapAt_physical_of_fixedWindowDecay`'s; `0` is the excluded colour count, the
plane of `FixedWindowDecay τ 0`, the sign of `c`, `L` and `r_m`, the vanishing vacuum pairing and the
bottom of the spectrum; `1` is the vacuum eigenvalue and the contraction threshold; `4` in `Fin 4` is
the spacetime dimension. -/
theorem continuum_gap_sep (hN2 : 2 ≤ N) (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)
    (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      0 < Real.exp (-(c / L) * dySpacing N m) ∧ Real.exp (-(c / L) * dySpacing N m) < 1
      ∧ TransferGap.GapAt (contTransferSep hN ρ τ hB hR m) (Real.exp (-(c / L) * dySpacing N m))
      ∧ (∀ u : GNSHilbert.H (contTransferSep hN ρ τ hB hR m).toReflForm,
          inner ℂ (GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
            (contTransferSep hN ρ τ hB hR m).vac) u = (0 : ℂ) →
          ‖GNSHilbert.opT (contTransferSep hN ρ τ hB hR m) u‖
            ≤ Real.exp (-(c / L) * dySpacing N m) * ‖u‖)
      ∧ spectrum ℝ (GNSHilbert.opT (contTransferSep hN ρ τ hB hR m))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(c / L) * dySpacing N m))
      ∧ IsGreatest (spectrum ℝ (GNSHilbert.opT (contTransferSep hN ρ τ hB hR m))) 1 := by
  obtain ⟨c, hc, hcl⟩ := contS_cluster_of_fixedWindowDecay_sep hN2 hN ρ τ hB hR hL hW
  refine ⟨c, hc, fun m => ?_⟩
  have hr0 : 0 < Real.exp (-(c / L) * dySpacing N m) := Real.exp_pos _
  have hr1 : Real.exp (-(c / L) * dySpacing N m) < 1 := by
    rw [Real.exp_lt_one_iff, neg_mul]
    exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (dySpacing_pos (one_le_of_ne_zero hN) m))
  have hg : TransferGap.GapAt (contTransferSep hN ρ τ hB hR m)
      (Real.exp (-(c / L) * dySpacing N m)) :=
    gapAt_sep_of_cluster hN ρ τ hB hR m (γ := c / L) (fun P Q n => hcl P Q m n)
  refine ⟨hr0, hr1, hg, fun u hu => GapToOperator.norm_opT_le_of_orth _ hr0.le hg u hu, ?_,
    GNSHilbert.isGreatest_one_spectrum_opT _⟩
  intro x hx
  rcases GapToOperator.spectrum_opT_subset _ hr0.le hg hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Set.mem_Ici.mp
      (GNSHilbert.spectrum_opT_nonneg _ (positiveTransfer_sep hN ρ τ hB hR m) hx), h.2⟩

#print axioms continuum_gap_sep

/-- **The headline from `UniformBound`**: `continuum_gap_sep` through
`uniformBoundSep_of_uniformBound` and `pairBoundSep_of_uniformBoundSep`.

DERIVED: `2` is the least rank with a non-zero Haar variance (`gapAt_physical_of_fixedWindowDecay`'s);
`0` is the excluded colour count, the lower end of `L`, `c` and the spectral interval; `1` is the
vacuum eigenvalue; `4` in `Fin 4` is the spacetime dimension. -/
theorem continuum_gap_of_uniformBound (hN2 : 2 ≤ N) (hN : N ≠ 0) (ρ : Renorm N)
    (hB : UniformBound hN ρ) (τ : Fin 4) (hR : ρ.ReflCompat τ) {L : ℝ} (hL : 0 < L)
    (hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
      spectrum ℝ (GNSHilbert.opT
          (contTransferSep hN ρ τ (pairBoundSep_of_uniformBoundSep hN ρ τ hR
            (uniformBoundSep_of_uniformBound hN ρ hB)) hR m))
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(c / L) * dySpacing N m)) := by
  obtain ⟨c, hc, h⟩ := continuum_gap_sep hN2 hN ρ τ
    (pairBoundSep_of_uniformBoundSep hN ρ τ hR (uniformBoundSep_of_uniformBound hN ρ hB)) hR hL hW
  exact ⟨c, hc, fun m => (h m).2.2.2.2.1⟩

#print axioms continuum_gap_of_uniformBound

end Headline

/-! ## 10. Non-triviality from a non-zero connected two-point function -/

section Nontrivial

/-- A vector whose vacuum-orthogonal part has non-zero form gives a non-zero vector of the completion
orthogonal to the vacuum.

DERIVED: `0` is the vanishing vacuum pairing and the zero vector; `2` is the square of the vacuum
coefficient. -/
theorem exists_orth_ne_zero {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (x : A) (hx : D.form x x - D.form x D.vac ^ 2 ≠ 0) :
    ∃ u : GNSHilbert.H D.toReflForm,
      inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = (0 : ℂ) ∧ u ≠ 0 := by
  refine ⟨GNSCompare.toH D.toReflForm (TransferGap.vacProj D x), ?_, ?_⟩
  · exact (GNSCompare.inner_vac_toH_eq_zero_iff D.toReflForm D.vac _).2
      (TransferGap.vacProj_orth D x)
  · intro h0
    have h1 := (GNSCompare.coe_ofPair_eq_zero_iff D.toReflForm _).1 h0
    rw [form_vacProj] at h1
    exact hx h1

#print axioms exists_orth_ne_zero

/-- A non-zero vector orthogonal to the unit vacuum is not a complex multiple of it.

DERIVED: `0` is the vanishing pairing and the zero vector; `1` is the vacuum norm; `2` the square of
the norm. -/
theorem not_mem_span_vac {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    {u : GNSHilbert.H D.toReflForm}
    (hu : inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = (0 : ℂ)) (hu0 : u ≠ 0) :
    ∀ a : ℂ, u ≠ a • GNSHilbert.Omega D.toReflForm D.vac := by
  intro a ha
  have h1 : inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = a := by
    rw [ha, inner_smul_right, inner_self_eq_norm_sq_to_K, GNSHilbert.norm_Omega_vac]
    simp
  rw [hu] at h1
  apply hu0
  rw [ha, ← h1, zero_smul]

#print axioms not_mem_span_vac

/-- **The connected two-point function is non-zero somewhere (stated, not proved).** Some separated
positive-time monomial `Q` has `S(θQ ∪ Q) − S(Q)² ≠ 0`, with `S(Q) = S(θ∅ ∪ Q)`.

DERIVED: `0` is the excluded colour count and the value excluded; `2` the square; `4` in `Fin 4` is
the spacetime dimension. -/
def ConnectedTwoPointNonzero (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) : Prop :=
  ∃ Q : SepMono N τ, kern hN ρ τ Q.1 Q.1 - kern hN ρ τ (emptyMono N) Q.1 ^ 2 ≠ 0

/-- **Non-triviality of the reconstructed space.** Under `ConnectedTwoPointNonzero`, at every dyadic
step the Hilbert space has a non-zero vector orthogonal to the vacuum and not a complex multiple of
it: its dimension exceeds one.

DERIVED: `0` is the vanishing vacuum pairing, the zero vector and the excluded colour count; `1` the
vacuum coefficient; `2` the square; `4` in `Fin 4` is the spacetime dimension. -/
theorem exists_orth_ne_zero_sep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)
    (hB : PairBoundSep hN ρ τ) (hR : ρ.ReflCompat τ) (m : ℕ)
    (h : ConnectedTwoPointNonzero hN ρ τ) :
    ∃ u : GNSHilbert.H (contTransferSep hN ρ τ hB hR m).toReflForm,
      inner ℂ (GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
        (contTransferSep hN ρ τ hB hR m).vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega (contTransferSep hN ρ τ hB hR m).toReflForm
        (contTransferSep hN ρ τ hB hR m).vac := by
  obtain ⟨Q, hQ⟩ := h
  have hx : (contTransferSep hN ρ τ hB hR m).form (Finsupp.single Q 1) (Finsupp.single Q 1)
      - (contTransferSep hN ρ τ hB hR m).form (Finsupp.single Q 1)
          (contTransferSep hN ρ τ hB hR m).vac ^ 2 ≠ 0 := by
    show formSep hN ρ τ (Finsupp.single Q 1) (Finsupp.single Q 1)
      - formSep hN ρ τ (Finsupp.single Q 1) (Finsupp.single (emptySep N τ) 1) ^ 2 ≠ 0
    rw [formSep_single, formSep_single]
    simp only [one_mul]
    show kern hN ρ τ Q.1 Q.1 - kern hN ρ τ Q.1 (emptyMono N) ^ 2 ≠ 0
    rw [← kern_symm hN ρ τ hR (emptyMono N) Q.1]
    exact hQ
  obtain ⟨u, hu, hu0⟩ := exists_orth_ne_zero (contTransferSep hN ρ τ hB hR m) _ hx
  exact ⟨u, hu, hu0, not_mem_span_vac _ hu hu0⟩

#print axioms exists_orth_ne_zero_sep

end Nontrivial

end MassGap.ContinuumSep
