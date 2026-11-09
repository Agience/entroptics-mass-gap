import Mathlib
import MassGap.FocusZoom

/-!
# MassGap.BoxFocusTest — which form of `FocusZoom.BoxFocus` is non-circular, and what it reduces to

`FocusZoom.cov_le_of_focus` bounds the connected correlator of the periodic Wilson state by
`BoxFocus` (the in-box covariance at every boundary condition) plus `BoundaryLag` (the covariance of the
two box averages). This module tests the two candidate weakenings of `BoxFocus` and finds the single
specification-level input that both remainders reduce to.

## Evaluation

1. **The ν-mean of the in-box term is a covariance of `ν`** (proved). `meanFocus_eq`:
   `ν(γ_Λ(XY) − γ_Λ X · γ_Λ Y) = Cov_ν(X, Y) − Cov_ν(γ_Λ X, γ_Λ Y)`. So the averaged form `MeanFocus`
   together with `BoundaryLag` is equivalent to the covariance bound itself, in both directions
   (`cov_le_of_meanFocus`, `meanFocus_of_cov`): replacing `BoxFocus` by its ν-mean makes the DLR split
   a rewriting of `Cov_ν(X, Y)`, i.e. circular. `meanFocus_of_boxFocus`: the uniform form implies the
   mean form.
2. **The mean-square oscillation of a box kernel is a covariance of `ν`** (proved). `kernel_var_eq_cov`:
   `Cov_ν(γ_Δ X, γ_Δ X) = Cov_ν(X, γ_Δ X)`, the correlation of `X` with its own box average, a functional
   of the boundary links of `Δ`. So an L²-averaged (ν-typical) boundary-influence bound is again a
   correlation of the state: circular.
3. **The uniform boundary-influence bound is the single non-circular input** (proved). `KernelNear Δ X δ`:
   the box kernel `γ_Δ X` is within `δ` of one constant at every boundary condition. It is a property of
   the specification alone (no state appears), and its form for every `ε > 0` with some box
   (`∀ ε > 0, ∃ Δ, KernelNear Δ X ε`) is exactly the hypothesis of
   `DLRLimit.dlr_eq_at_of_kernel_near_const` (uniqueness of DLR states). From it:
   * `cov_le_of_kernelNear`: for `Y` not reading `Δ` with `|Y| ≤ M`, `|Cov_ν(X, Y)| ≤ 2 M δ` directly
     (through `FocusZoom.cov_screen`), with no box containing both observables and no boundary term;
   * `boxFocus_of_kernelNear`: for `Δ ⊆ Λ`, `BoxFocus Λ X Y (2 M δ)` — the uniform in-box bound follows
     from the uniform kernel bound at the smaller box around `X` (through `boxState`, the box measure at a
     fixed boundary condition, and `PeriodicStateDLR.periodicState_dlr_nested`);
   * `boundaryLag_of_kernelNear`: `BoundaryLag Λ X Y (2 M δ)` from `KernelNear Λ X δ` and `|γ_Λ Y| ≤ M`.
   So the "box around `X` alone" placement that `FocusZoom` found circular is circular only when the
   screened correlator `Cov_ν(γ_Δ X, Y)` is bounded through `ν`; bounded through the uniform oscillation of
   `γ_Δ X` it is not.
4. **Is the uniform form false?** (argued, not a declaration). No counterexample is constructed.
   * The boundary condition enters the box weight only through the crossing plaquettes
     (`FocusZoom.wt_le_wt`); each carries one box link and three boundary links, so `ω` acts as an
     arbitrary `SU(N)` field of strength `β` on each surface link. A flux-pinning `ω` (surface holonomy
     `g`, e.g. a centre element, around a large surface loop) is therefore admissible.
   * In two dimensions the in-box law at boundary holonomy `g` is the heat-kernel product conditioned on
     the ordered plaquette product `= g`; by the character expansion the induced covariance and the kernel
     oscillation are `O(Σ_r d_r² (c_r / (d_r c_0))^{n−2})`, area law in the box, **uniform in `g`**: pinned
     flux does not produce long-range in-box order there.
   * A counterexample needs boundary data whose in-box minimisers form a continuum (a modulus such as
     the position of a forced vortex sheet), giving `O(1)` covariance along it. Such data exist in a box of
     fixed lattice size as `β → ∞`; in that regime the box is physically small and the `ν`-typical
     in-box covariance is a perturbative power law, so the target `e^{−c σ R t}` fails for typical `ω` as
     well: the failure is the box scale, not the uniformity. At fixed physical size above the confinement
     length a forced centre flux is expected to delocalise (the magnetic twist free energy is exponentially
     small in the confined phase), leaving no modulus.
   * Restricting to ν-typical `ω` does not weaken the uniform form: `ω ↦ γ_Λ f(ω)` is continuous, and the
     periodic state's finite marginals have densities bounded below, so the supremum over `ω` equals the
     ν-essential supremum. The only genuine weakening is an average, and items 1 and 2 show every average
     is circular.
5. **What remains**: `KernelNear` at the focal scale — the influence of an arbitrary boundary condition on
   a box of physical radius `~ t` on the box average of a loop at its centre is at most
   `δ ≈ e^{−m t}`, uniformly in `ω` and in `β` at fixed physical size. This is a Dobrushin–Shlosman-type
   finite-volume mixing condition. At small `β` it is proved in the uniform form
   (`StrongKernelNear.kernelNear_strong_explicit`, `|β| ≤ 2^{-16}`); uniformly in `β` it is open, and the standard bounds carry a surface
   prefactor `|∂Δ|` in lattice units, which grows as `β → ∞` at fixed physical radius.

## What is proved

* §1 (any state): `cov_le_of_near_const`.
* §2 (box measure): `boxState`, `boxState_apply`, `wspec_splice_self`.
* §3 (periodic `SU(N)` state): `KernelNear`, `cov_le_of_kernelNear`, `boxFocus_of_kernelNear`,
  `boundaryLag_of_kernelNear`, `MeanFocus`, `meanFocus_eq`, `meanFocus_of_boxFocus`,
  `cov_le_of_meanFocus`, `meanFocus_of_cov`, `kernel_var_eq_cov`.

DERIVED (module-wide): `2` is the two-sided spread `|g − ν g| ≤ |g| + |ν g| ≤ 2 M` of the second
observable about its mean.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.BoxFocusTest

open MeasureTheory
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.PeriodicStateDLR (wspec wspec_apply periodicState_dlr wspec_add wspec_smul wspec_one
  periodicState_dlr_nested)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity measurable_wilsonDensity wilsonDensity_nonneg
  wilsonDensity_le_two)
open MassGap.CompactGauge (probHaar)
open MassGap.FocusZoom (stateCov abs_state_le BoxFocus BoundaryLag dlr_cov_split wspec_mul_outside
  cov_screen)

/-! ## 1. A covariance with one observable near a constant -/

/-- **Covariance against a near-constant observable.** If `|f − c| ≤ δ` and `|g| ≤ M` pointwise, then
`|Cov_ν(f, g)| ≤ 2 M δ` for every state `ν`. -/
theorem cov_le_of_near_const {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : State X)
    (f g : C(X, ℝ)) {c δ M : ℝ} (hf : ∀ x, |f x - c| ≤ δ) (hg : ∀ x, |g x| ≤ M) :
    |stateCov ν f g| ≤ 2 * M * δ := by
  obtain ⟨x₀⟩ := ν.nonempty
  set d := ν g with hd
  have hdM : |d| ≤ M := abs_state_le ν g x₀ hg
  have e : (f - c • (1 : C(X, ℝ))) * (g - d • (1 : C(X, ℝ)))
      = f * g - d • f - c • g + (c * d) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have hcov : stateCov ν f g = ν ((f - c • (1 : C(X, ℝ))) * (g - d • (1 : C(X, ℝ)))) := by
    rw [e, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul, ν.map_one]
    unfold stateCov
    rw [← hd]
    ring
  rw [hcov]
  refine abs_state_le ν _ x₀ fun x => ?_
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one]
  have h1 := hf x
  have h2 : |g x - d| ≤ 2 * M := by
    calc |g x - d| ≤ |g x| + |d| := abs_sub _ _
      _ ≤ M + M := add_le_add (hg x) hdM
      _ = 2 * M := by ring
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h1
  rw [abs_mul]
  calc |f x - c| * |g x - d| ≤ δ * (2 * M) :=
        mul_le_mul h1 h2 (abs_nonneg _) hδ
    _ = 2 * M * δ := by ring

/-! ## 2. The box measure at a fixed boundary condition -/

section Box

variable {N : ℕ}

/-- **The box measure at boundary condition `ω`**, as a state: `f ↦ γ_Λ(f | ω)`. -/
def boxState (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (ω : IConf (SU N)) : State (IConf (SU N)) where
  toFun f := wspec hN β Λ f ω
  map_add' f g := by
    show wspec hN β Λ (f + g) ω = wspec hN β Λ f ω + wspec hN β Λ g ω
    rw [wspec_add]; rfl
  map_smul' c f := by
    show wspec hN β Λ (c • f) ω = c * wspec hN β Λ f ω
    rw [wspec_smul]; rfl
  nonneg' f hf := MassGap.WilsonDLR.spec_nonneg measurable_wilsonDensity (wilsonDensity_nonneg hN)
      (wilsonDensity_le_two hN) β Λ _ (fun U => hf U) ω
  one' := by
    show wspec hN β Λ 1 ω = 1
    rw [wspec_one]; rfl

theorem boxState_apply (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (ω : IConf (SU N))
    (f : C(IConf (SU N), ℝ)) : boxState hN β Λ ω f = wspec hN β Λ f ω := rfl

/-- **A box kernel does not read its own box**: `γ_Δ f (splice Δ u ω) = γ_Δ f ω`. -/
theorem wspec_splice_self (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (f : C(IConf (SU N), ℝ))
    (u : VConf (SU N) Δ) (ω : IConf (SU N)) :
    wspec hN β Δ f (splice Δ u ω) = wspec hN β Δ f ω := by
  rw [wspec_apply, wspec_apply]
  have h := spec_splice_off (wilsonDensity (N := N)) β Δ Δ (probHaar (SU N)) (⇑f) u
    (fun x => ω x) ω (fun x hx => absurd x.2 hx)
  have hω : splice Δ (fun x => ω x) ω = ω := by
    funext l
    by_cases hl : l ∈ Δ
    · rw [splice_mem hl]
    · rw [splice_not_mem hl]
  rw [h, hω]

end Box

/-! ## 3. The uniform kernel bound, and the averaged forms -/

section Periodic

variable {N : ℕ}

/-- **Uniform boundary influence** (named input): the box kernel of `X` at `Δ` lies within `δ` of one
constant at every boundary condition. A property of the specification alone. Not proved. -/
def KernelNear (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SU N), ℝ)) (δ : ℝ) : Prop :=
  ∃ c : ℝ, ∀ ω, |wspec hN β Δ X ω - c| ≤ δ

/-- **The uniform kernel bound gives the correlator directly.** For `Y` not reading `Δ` and `|Y| ≤ M`:
`|Cov_ν(X, Y)| ≤ 2 M δ`. -/
theorem cov_le_of_kernelNear (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {δ M : ℝ} (hY : ∀ (u : VConf (SU N) Δ) (ω : IConf (SU N)), Y (splice Δ u ω) = Y ω)
    (hYM : ∀ ω, |Y ω| ≤ M) (hK : KernelNear hN β Δ X δ) :
    |stateCov (periodicState hN β) X Y| ≤ 2 * M * δ := by
  obtain ⟨c, hc⟩ := hK
  rw [cov_screen hN β Δ X Y hY]
  exact cov_le_of_near_const _ _ _ hc hYM

/-- **The uniform kernel bound at a smaller box gives `BoxFocus`.** For `Δ ⊆ Λ`, `Y` not reading `Δ`,
`|Y| ≤ M`: `BoxFocus Λ X Y (2 M δ)`. -/
theorem boxFocus_of_kernelNear (hN : N ≠ 0) (β : ℝ) {Δ Λ : Finset ILink} (hΔΛ : Δ ⊆ Λ)
    (X Y : C(IConf (SU N), ℝ)) {δ M : ℝ}
    (hY : ∀ (u : VConf (SU N) Δ) (ω : IConf (SU N)), Y (splice Δ u ω) = Y ω)
    (hYM : ∀ ω, |Y ω| ≤ M) (hK : KernelNear hN β Δ X δ) :
    BoxFocus hN β Λ X Y (2 * M * δ) := by
  obtain ⟨c, hc⟩ := hK
  intro ω
  have e1 : wspec hN β Λ (X * Y) = wspec hN β Λ (wspec hN β Δ X * Y) := by
    rw [← wspec_mul_outside hN β Δ X Y hY]
    exact (periodicState_dlr_nested hN β hΔΛ (X * Y)).1.symm
  have e2 : wspec hN β Λ X = wspec hN β Λ (wspec hN β Δ X) :=
    (periodicState_dlr_nested hN β hΔΛ X).1.symm
  have h : wspec hN β Λ (X * Y) ω - wspec hN β Λ X ω * wspec hN β Λ Y ω
      = stateCov (boxState hN β Λ ω) (wspec hN β Δ X) Y := by
    unfold stateCov
    rw [boxState_apply, boxState_apply, boxState_apply, e1, e2]
  rw [h]
  exact cov_le_of_near_const _ _ _ hc hYM

/-- **The uniform kernel bound gives `BoundaryLag`.** From `KernelNear Λ X δ` and `|γ_Λ Y| ≤ M`. -/
theorem boundaryLag_of_kernelNear (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {δ M : ℝ} (hYM : ∀ ω, |wspec hN β Λ Y ω| ≤ M) (hK : KernelNear hN β Λ X δ) :
    BoundaryLag hN β Λ X Y (2 * M * δ) := by
  obtain ⟨c, hc⟩ := hK
  exact cov_le_of_near_const _ _ _ hc hYM

/-- **The in-box term averaged over the boundary condition** (the weakening `dlr_cov_split`'s first term
uses): `|ν(γ_Λ(XY) − γ_Λ X · γ_Λ Y)| ≤ ε`. -/
def MeanFocus (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ)) (ε : ℝ) : Prop :=
  |periodicState hN β (wspec hN β Λ (X * Y) - wspec hN β Λ X * wspec hN β Λ Y)| ≤ ε

/-- **The averaged in-box term is a difference of two covariances of the state**:
`ν(γ_Λ(XY) − γ_Λ X γ_Λ Y) = Cov_ν(X, Y) − Cov_ν(γ_Λ X, γ_Λ Y)`. -/
theorem meanFocus_eq (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ)) :
    periodicState hN β (wspec hN β Λ (X * Y) - wspec hN β Λ X * wspec hN β Λ Y)
      = stateCov (periodicState hN β) X Y
        - stateCov (periodicState hN β) (wspec hN β Λ X) (wspec hN β Λ Y) := by
  rw [dlr_cov_split hN β Λ X Y]
  ring

/-- The uniform form implies the averaged form. -/
theorem meanFocus_of_boxFocus (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {ε : ℝ} (h : BoxFocus hN β Λ X Y ε) : MeanFocus hN β Λ X Y ε :=
  abs_state_le _ _ (fun _ => 1) fun ω => by
    rw [ContinuousMap.sub_apply, ContinuousMap.mul_apply]; exact h ω

/-- **Averaged form and boundary term give the correlator** (`MeanFocus + BoundaryLag ⇒ Cov`). -/
theorem cov_le_of_meanFocus (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {ε ε' : ℝ} (h : MeanFocus hN β Λ X Y ε) (hbd : BoundaryLag hN β Λ X Y ε') :
    |stateCov (periodicState hN β) X Y| ≤ ε + ε' := by
  unfold MeanFocus at h
  unfold BoundaryLag at hbd
  rw [meanFocus_eq] at h
  have := abs_add_le (stateCov (periodicState hN β) X Y
      - stateCov (periodicState hN β) (wspec hN β Λ X) (wspec hN β Λ Y))
    (stateCov (periodicState hN β) (wspec hN β Λ X) (wspec hN β Λ Y))
  rw [sub_add_cancel] at this
  linarith

/-- **The correlator and the boundary term give the averaged form** (`Cov + BoundaryLag ⇒ MeanFocus`):
the converse, so with `BoundaryLag` the averaged form is the covariance bound. -/
theorem meanFocus_of_cov (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {ε₁ ε' : ℝ} (h : |stateCov (periodicState hN β) X Y| ≤ ε₁) (hbd : BoundaryLag hN β Λ X Y ε') :
    MeanFocus hN β Λ X Y (ε₁ + ε') := by
  unfold MeanFocus
  unfold BoundaryLag at hbd
  rw [meanFocus_eq]
  exact (abs_sub _ _).trans (add_le_add h hbd)

/-- **The mean-square oscillation of a box kernel is a covariance of the state**:
`Cov_ν(γ_Δ X, γ_Δ X) = Cov_ν(X, γ_Δ X)`. -/
theorem kernel_var_eq_cov (hN : N ≠ 0) (β : ℝ) (Δ : Finset ILink) (X : C(IConf (SU N), ℝ)) :
    stateCov (periodicState hN β) (wspec hN β Δ X) (wspec hN β Δ X)
      = stateCov (periodicState hN β) X (wspec hN β Δ X) :=
  (cov_screen hN β Δ X (wspec hN β Δ X) (fun u ω => wspec_splice_self hN β Δ X u ω)).symm

end Periodic

#print axioms cov_le_of_near_const
#print axioms boxState
#print axioms wspec_splice_self
#print axioms cov_le_of_kernelNear
#print axioms boxFocus_of_kernelNear
#print axioms boundaryLag_of_kernelNear
#print axioms meanFocus_eq
#print axioms meanFocus_of_boxFocus
#print axioms cov_le_of_meanFocus
#print axioms meanFocus_of_cov
#print axioms kernel_var_eq_cov

end MassGap.BoxFocusTest
