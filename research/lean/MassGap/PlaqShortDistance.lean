import Mathlib
import MassGap.BoxFocusTest
import MassGap.BareRatioProof

/-!
# MassGap.PlaqShortDistance — the lowest-mode variance is at least a sum of one-link conditional variances

`BareRatioProof` reduces the heat-screen count bound to `LowModeRatio`: the operator norm of the bare covariance
on the screen box within a fixed factor `Q'` of the lowest Dirichlet-mode variance `ν_k((∑_x v_x P_x)²)`.
`PlaqPositive` shows that reflection positivity does not bound that variance from below: the profile
`Γ(0) = 1`, `Γ(±1) = −1/2` is consistent with every reflection inequality and has zero lowest-mode variance.
This module proves the lower bound that the DLR structure of the Wilson measure gives, at every coupling and
every finite set of links, and names what remains. Declarations are in the namespace
`MassGap.PlaqShortDistance`.

Throughout, `ν = periodicState hN β` (the step-`k` state of `schedSU N` at `β = dyBeta k`), `γ_Λ = wspec hN β Λ`
the box kernel with boundary condition, and `cv_Λ h = γ_Λ(h²) − (γ_Λ h)²` the conditional variance of `h` given
the links off `Λ`.

## 1. The conditional variance (proved)

`state_sq_le`: `μ(h)² ≤ μ(h²)` for every state. `cv_nonneg`: `cv_Λ h ≥ 0` at every boundary condition (the box
measure at `ω`, `BoxFocusTest.boxState`, is a state). `wspec_of_outside`: an observable not reading `Λ` is fixed
by `γ_Λ`. `cv_add_outside`: `cv_Λ(h + r) = cv_Λ h` when `r` does not read `Λ` (pull-out,
`FocusZoom.wspec_mul_outside`).

## 2. The conditioning chain (proved)

`cv_step`: for `L ⊆ B`, `ν(cv_L h) ≤ ν(h²) − ν((γ_B h)²)`: `γ_B h = γ_B(γ_L h)` (DLR consistency,
`PeriodicStateDLR.periodicState_dlr_nested`), Jensen for `γ_B` at each boundary condition, and the DLR equations.
`chain`: for any sequence of links `l_0, l_1, …` and `Λ_i = {l_j : j < i}` (`past`),
`∑_{i<m} ν(cv_{l_i}(γ_{Λ_i} F)) ≤ ν(F²) − ν((γ_{Λ_m} F)²)`. No separation of the links and no product structure
of the kernel enters; it is the martingale decomposition of the variance along the filtration that releases one
link at a time, with the later terms dropped.

## 3. Sparse links and local pieces (proved)

`SparseSplit F m` bundles links `l_i` and, for each `i < m`, a split `F = f_i + r_i` with `f_i` local on `T_i`,
`r_i` local on `R_i`, the earlier links off `T_i`, `l_i ∉ R_i`, and `l_i` off the boundary links of `Λ_i`
(`apart_of_plaq`: it suffices that `l_i` shares no plaquette with an earlier `l_j`). Then
`γ_{Λ_i} F = f_i + γ_{Λ_i} r_i`, the second term does not read `l_i` (`local_wspec`, from
`WilsonDLR.isLocalOn_spec`), and `cv_{l_i}(γ_{Λ_i} F) = cv_{l_i} f_i`.

`var_ge_splitFloor`: `∑_{i<m} ν(cv_{l_i} f_i) ≤ ν(F²) − ν(F)²`, at every `N ≠ 0`, every real `β`, every `F`.

## 4. The lowest mode and the count bound (proved, conditional on `SplitRatio`)

The count bound for the heat screen is not proved here; it is implied by `SplitRatio`, which is open.

`SplitRatio N D ρ Q'`: eventually along `schedSU N`, for every `O ∈ D`, some `c ≥ 0` bounding the bare covariance
of the screen box in operator norm, a `SparseSplit` of the lowest-mode field `F = ∑_x boxF_{x,bot} P_x`, and
`c ≤ Q' ∑_i ν_k(cv_{l_i} f_i)`. `lowModeRatio_of_split`: `SplitRatio N D ρ Q'` gives
`LowModeRatio (schedSU N) D ρ Q'`. `count_heatScreen_of_split`: with `ρ, θ > 0` it gives the bounded Rényi-½
count of the heat screen (`ApertureFinite.count_heatScreen` through `BareRatioProof.bareRatio_of_lowMode`).

## 5. The paper tests

Argued, not formalized.

* The profile of `PlaqPositive` §8 (`Γ(0) = 1`, `Γ(±1) = −1/2`). Its lowest-mode variance tends to `0`. Under
  the Wilson measure §3 bounds that variance below by `∑_i ν(cv_{l_i} f_i)`. With links on a sublattice of
  spacing `s` (`s ≥ 2` keeps every plaquette off two of them) and `f_i` the part of `F` reading `l_i`, the sum is
  `∑_i v_{x_i}² ν(cv_{l_i} A_{l_i})` up to the variation of `v` over one cell, `A_l` the unweighted local reading
  at `l`; if `ν(cv_l A_l) ≥ κ C(0)` the lowest-mode variance is at least `κ C(0) s^{−4}` (up to that variation),
  which the profile violates. So the profile is excluded by the DLR structure exactly when the one-link
  conditional variance of the local reading is a fixed fraction of the plaquette variance; reflection positivity
  is not used.
* Linear angle reading (free compact `U(1)`, `sin θ_p`). The plaquettes through `l` enter `f_l` with both signs
  (orientation), so at Gaussian order `f_l` is `(∂v) A_l`, of size `1/L` against `v`: the floor is `O(L^{−2})`
  relative, and the bound is weak. Consistent: the box sum of a curl telescopes.
* The symmetrized class (`SymPlaqG.SymPlaqClassG`) at weak coupling. Every plaquette through `l` enters with a
  positive weight (`BareRatioProof.boxF_bot_nonneg`), and `f_l = const − Re tr(U_l S_w)/N` with `S_w` the weighted
  staple sum. At Gaussian order around the staple's polar point the quadratic term dominates and
  `ν(cv_l f_l) ~ c(N) w̄²/β²`, the order of `C(0) = Var(P) ~ c'(N)/β²`; so the floor is a fixed fraction of
  `C(0)` uniformly in `β` at that order. At a boundary condition with `S_w = 0` the conditional variance is `0`, so
  only the `ν`-average has a floor, never a uniform one.

## What does not follow

* The count bound for the heat screen is not proved; it follows only from `SplitRatio`.
* `LowModeRatio` and `RelSum` are not proved; `SplitRatio` is not proved along any tower. `lowModeRatio_of_split`
  removes the lower half of `LowModeRatio` (the cancellation that the §8 profile exhibits) and the sign clause of
  `RelSum`; it does not touch the upper half.
* The remaining inequality is `SplitRatio`'s last clause: one `Q'` with, eventually along the tower,
  `‖C_k‖_op ≤ Q' ∑_i ν_k(cv_{l_i} f_i)` for a sparse split of the lowest-mode field. With the §5 estimates it is
  `∑_z C_k(z) ≤ K ν_k(cv_l A_l)` (the operator norm read at zero momentum, `PlaqPositive` §8): the plaquette
  correlator's sum is bounded by a fixed multiple of the one-link conditional variance of the local reading,
  uniformly as the coupling grows. That is relative summability without signs, against a local scale. The
  transfer gap along the tower gives only a factor growing like `2^{4k}` (`BareRatioProof` §5).
* The per-link floor `ν_k(cv_l A_l) ≥ κ C_k(0)` is not proved; §5 argues it at Gaussian order only. No upper bound
  `C_k(0) ≤ c/β_k²` and no lower bound on `ν_k(cv_l A_l)` at the scale `1/β_k²` are in the tree
  (`PlaquetteFloor` bounds the mean below, a mean, not a variance; its constants are quoted from that module).
* Strict positivity of a single `ν(cv_{l_i} f_i)` is not proved here.
* Only the `SU(N)` schedule is covered: the box kernel `wspec` and its DLR equations are stated for
  `periodicState`.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the signs, the empty past and the lowest Dirichlet mode; `1` the unit observable and the
index step; `2` the squares and the cross term `2 h r` of `(h + r)²`. `s`, `κ`, `K`, `c(N)` and the exponents in §5
appear only in the argued text. `m`, `l`, `Q'`, `c` are hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.PlaqShortDistance

open Finset Filter
open MassGap.GibbsSpec
open MassGap.DLRLimit (State IsLocalOnC)
open MassGap.PeriodicStateDLR (wspec wspec_apply periodicState_dlr wspec_add wspec_smul wspec_one
  periodicState_dlr_nested wspec_empty)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.BoxFocusTest (boxState boxState_apply)
open MassGap.FocusZoom (wspec_mul_outside)

/-! ## 1. The conditional variance -/

/-- **Jensen for a state**: `μ(h)² ≤ μ(h²)`. DERIVED: `2` the square and the cross term. -/
theorem state_sq_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (μ : State X) (h : C(X, ℝ)) :
    μ h ^ 2 ≤ μ (h * h) := by
  have e : (h - μ h • (1 : C(X, ℝ))) * (h - μ h • (1 : C(X, ℝ)))
      = h * h - (2 * μ h) • h + (μ h * μ h) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have h0 : 0 ≤ μ ((h - μ h • (1 : C(X, ℝ))) * (h - μ h • (1 : C(X, ℝ)))) :=
    μ.nonneg _ fun x => by rw [ContinuousMap.mul_apply]; exact mul_self_nonneg _
  rw [e, μ.map_add, μ.map_sub, μ.map_smul, μ.map_smul, μ.map_one] at h0
  nlinarith

variable {N : ℕ}

/-- **An observable not reading `Λ`**: invariant under every splice on `Λ`. DERIVED: no numeral. -/
def Outside (Λ : Finset ILink) (h : C(IConf (SU N), ℝ)) : Prop :=
  ∀ (u : VConf (SU N) Λ) (ω : IConf (SU N)), h (splice Λ u ω) = h ω

/-- **The conditional variance given the links off `Λ`**: `cv_Λ h = γ_Λ(h²) − (γ_Λ h)²`. DERIVED: `2` the
square. -/
def cv (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (h : C(IConf (SU N), ℝ)) : C(IConf (SU N), ℝ) :=
  wspec hN β Λ (h * h) - wspec hN β Λ h * wspec hN β Λ h

/-- **Jensen for the box kernel at a boundary condition**: `(γ_Λ h)(ω)² ≤ γ_Λ(h²)(ω)`. DERIVED: `2` the
square. -/
theorem wspec_sq_le (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (h : C(IConf (SU N), ℝ)) (ω : IConf (SU N)) :
    wspec hN β Λ h ω * wspec hN β Λ h ω ≤ wspec hN β Λ (h * h) ω := by
  have h1 := state_sq_le (boxState hN β Λ ω) h
  rw [boxState_apply, boxState_apply, sq] at h1
  exact h1

/-- **The conditional variance is non-negative at every boundary condition**. DERIVED: `0` the sign. -/
theorem cv_nonneg (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (h : C(IConf (SU N), ℝ)) (ω : IConf (SU N)) :
    0 ≤ cv hN β Λ h ω := by
  unfold cv
  rw [ContinuousMap.sub_apply, ContinuousMap.mul_apply]
  linarith [wspec_sq_le hN β Λ h ω]

/-- **The box kernel fixes an observable not reading the box**. DERIVED: `1` the unit observable. -/
theorem wspec_of_outside (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (r : C(IConf (SU N), ℝ))
    (hr : Outside Λ r) : wspec hN β Λ r = r := by
  have h := wspec_mul_outside hN β Λ 1 r hr
  rw [one_mul, wspec_one, one_mul] at h
  exact h

/-- **Adding an observable that does not read the box leaves the conditional variance unchanged**.
DERIVED: `2` the cross term of the square. -/
theorem cv_add_outside (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (h r : C(IConf (SU N), ℝ))
    (hr : Outside Λ r) : cv hN β Λ (h + r) = cv hN β Λ h := by
  have hrr : Outside Λ (r * r) := fun u ω => by
    rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply, hr u ω]
  have e1 : (h + r) * (h + r) = h * h + ((2 : ℝ) • (h * r) + r * r) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have a1 : wspec hN β Λ (h * r) = wspec hN β Λ h * r := wspec_mul_outside hN β Λ h r hr
  have a2 : wspec hN β Λ (r * r) = r * r := wspec_of_outside hN β Λ _ hrr
  have a3 : wspec hN β Λ r = r := wspec_of_outside hN β Λ r hr
  unfold cv
  rw [e1, wspec_add, wspec_add, wspec_smul, a1, a2, wspec_add, a3]
  ext ω
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- **A local observable off `L` does not read `L`**. DERIVED: no numeral. -/
theorem outside_of_local {L T : Finset ILink} {h : C(IConf (SU N), ℝ)} (hh : IsLocalOnC T h)
    (hT : ∀ x ∈ T, x ∉ L) : Outside L h := fun _ _ =>
  hh _ _ fun x hx => splice_not_mem (hT x hx)

/-- **The box kernel of a local observable is local on its support and the boundary links of the box**.
DERIVED: no numeral. -/
theorem local_wspec (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) {S : Finset ILink} {f : C(IConf (SU N), ℝ)}
    (hf : IsLocalOnC S f) : IsLocalOnC (S ∪ MassGap.WilsonDLR.bdLinks Λ) (wspec hN β Λ f) :=
  fun U V hUV => by
    rw [wspec_apply, wspec_apply]
    exact MassGap.WilsonDLR.isLocalOn_spec (wilsonDensity (N := N)) β Λ (probHaar (SU N))
      (fun U V h => hf U V h) U V hUV

#print axioms state_sq_le
#print axioms wspec_sq_le
#print axioms cv_nonneg
#print axioms wspec_of_outside
#print axioms cv_add_outside
#print axioms outside_of_local
#print axioms local_wspec

/-! ## 2. The conditioning chain -/

/-- **The links released before step `i`**: `Λ_i = {l_j : j < i}`. DERIVED: no numeral. -/
def past (l : ℕ → ILink) (i : ℕ) : Finset ILink := (range i).image l

/-- The empty past. DERIVED: `0` the empty range. -/
theorem past_zero (l : ℕ → ILink) : past l 0 = ∅ := by simp [past]

/-- The past grows. DERIVED: `1` the index step. -/
theorem past_mono (l : ℕ → ILink) (i : ℕ) : past l i ⊆ past l (i + 1) :=
  image_subset_image (range_subset_range.2 (Nat.le_succ i))

/-- The link released at step `i` lies in the next past. DERIVED: `1` the index step. -/
theorem single_sub_past (l : ℕ → ILink) (i : ℕ) : ({l i} : Finset ILink) ⊆ past l (i + 1) :=
  singleton_subset_iff.2 (mem_image.2 ⟨i, mem_range.2 (Nat.lt_succ_self i), rfl⟩)

/-- **One step of the chain**: for `L ⊆ B`, `ν(cv_L h) ≤ ν(h²) − ν((γ_B h)²)`. DERIVED: `2` the squares. -/
theorem cv_step (hN : N ≠ 0) (β : ℝ) {L B : Finset ILink} (hLB : L ⊆ B) (h : C(IConf (SU N), ℝ)) :
    periodicState hN β (cv hN β L h)
      ≤ periodicState hN β (h * h) - periodicState hN β (wspec hN β B h * wspec hN β B h) := by
  have e1 : wspec hN β B h = wspec hN β B (wspec hN β L h) :=
    ((periodicState_dlr_nested hN β hLB h).1).symm
  have hJ : periodicState hN β (wspec hN β B (wspec hN β L h) * wspec hN β B (wspec hN β L h))
      ≤ periodicState hN β (wspec hN β B (wspec hN β L h * wspec hN β L h)) :=
    (periodicState hN β).mono fun ω => by
      rw [ContinuousMap.mul_apply]
      exact wspec_sq_le hN β B _ ω
  have e2 : periodicState hN β (wspec hN β B (wspec hN β L h * wspec hN β L h))
      = periodicState hN β (wspec hN β L h * wspec hN β L h) := periodicState_dlr hN β B _
  have e3 : periodicState hN β (wspec hN β L (h * h)) = periodicState hN β (h * h) :=
    periodicState_dlr hN β L (h * h)
  have e4 : periodicState hN β (cv hN β L h)
      = periodicState hN β (wspec hN β L (h * h)) - periodicState hN β (wspec hN β L h * wspec hN β L h) := by
    unfold cv
    rw [(periodicState hN β).map_sub]
  rw [e1, e4]
  linarith

/-- **The conditioning chain**: `∑_{i<m} ν(cv_{l_i}(γ_{Λ_i} F)) ≤ ν(F²) − ν((γ_{Λ_m} F)²)`. DERIVED: `0` the
empty past; `1` the index step; `2` the squares. -/
theorem chain (hN : N ≠ 0) (β : ℝ) (l : ℕ → ILink) (F : C(IConf (SU N), ℝ)) (m : ℕ) :
    ∑ i ∈ range m, periodicState hN β (cv hN β {l i} (wspec hN β (past l i) F))
      ≤ periodicState hN β (F * F)
        - periodicState hN β (wspec hN β (past l m) F * wspec hN β (past l m) F) := by
  induction m with
  | zero =>
    rw [sum_range_zero, past_zero, wspec_empty, sub_self]
  | succ m ih =>
    rw [sum_range_succ]
    have hstep := cv_step hN β (single_sub_past l m) (wspec hN β (past l m) F)
    have hnest : wspec hN β (past l (m + 1)) (wspec hN β (past l m) F) = wspec hN β (past l (m + 1)) F :=
      (periodicState_dlr_nested hN β (past_mono l m) F).1
    rw [hnest] at hstep
    linarith

#print axioms past_zero
#print axioms past_mono
#print axioms single_sub_past
#print axioms cv_step
#print axioms chain

/-! ## 3. Sparse links and local pieces -/

/-- **A link sharing no plaquette with `Λ` is off its boundary links**. DERIVED: no numeral. -/
theorem not_mem_bdLinks {Λ : Finset ILink} {l : ILink}
    (h : ∀ q : IPlaq, l ∈ ilinks q → ∀ l' ∈ ilinks q, l' ∉ Λ) : l ∉ MassGap.WilsonDLR.bdLinks Λ := by
  intro hl
  unfold MassGap.WilsonDLR.bdLinks at hl
  obtain ⟨q, hq, hlq⟩ := mem_biUnion.mp hl
  obtain ⟨l', hl', hl'Λ⟩ := mem_boundaryPlaqs.mp hq
  exact h q (List.mem_toFinset.mp hlq) l' hl' hl'Λ

/-- **Links sharing no plaquette with the earlier ones are apart**: if no plaquette contains both `l_j` and
`l_i` for `j < i`, then `l_i` is off the boundary links of `Λ_i`. DERIVED: no numeral. -/
theorem apart_of_plaq (l : ℕ → ILink) (i : ℕ)
    (h : ∀ j < i, ∀ q : IPlaq, l j ∈ ilinks q → l i ∉ ilinks q) :
    l i ∉ MassGap.WilsonDLR.bdLinks (past l i) :=
  not_mem_bdLinks fun q hiq l' hl' hl'p => by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hl'p
    exact h j (mem_range.mp hj) q hl' hiq

/-- **A sparse split of `F` along `m` links**: for each `i < m`, `F = f_i + r_i`, `f_i` local on `T_i` and off
the earlier links, `r_i` local on `R_i ∌ l_i`, and `l_i` off the boundary links of the earlier ones. DERIVED: no
numeral. -/
structure SparseSplit (F : C(IConf (SU N), ℝ)) (m : ℕ) where
  /-- The links, released in order. -/
  l : ℕ → ILink
  /-- The part of `F` reading `l_i`. -/
  f : ℕ → C(IConf (SU N), ℝ)
  /-- The rest of `F`. -/
  r : ℕ → C(IConf (SU N), ℝ)
  /-- A support of `f_i`. -/
  T : ℕ → Finset ILink
  /-- A support of `r_i`. -/
  R : ℕ → Finset ILink
  dec : ∀ i < m, F = f i + r i
  locf : ∀ i < m, IsLocalOnC (T i) (f i)
  locr : ∀ i < m, IsLocalOnC (R i) (r i)
  early : ∀ i < m, ∀ j < i, l j ∉ T i
  own : ∀ i < m, l i ∉ R i
  apart : ∀ i < m, l i ∉ MassGap.WilsonDLR.bdLinks (past l i)

/-- **The conditional-variance floor of a split**: `∑_{i<m} ν(cv_{l_i} f_i)`. DERIVED: no numeral. -/
def splitFloor (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m) : ℝ :=
  ∑ i ∈ range m, periodicState hN β (cv hN β {sp.l i} (sp.f i))

/-- The floor is non-negative. DERIVED: `0` the sign. -/
theorem splitFloor_nonneg (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m) :
    0 ≤ splitFloor hN β sp :=
  sum_nonneg fun _ _ =>(periodicState hN β).nonneg _ (cv_nonneg hN β _ _)

/-- **Each chain term is the local conditional variance**: `cv_{l_i}(γ_{Λ_i} F) = cv_{l_i} f_i`. DERIVED: no
numeral. -/
theorem chain_term (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m)
    {i : ℕ} (hi : i < m) :
    cv hN β {sp.l i} (wspec hN β (past sp.l i) F) = cv hN β {sp.l i} (sp.f i) := by
  have hfo : Outside (past sp.l i) (sp.f i) := outside_of_local (sp.locf i hi) fun x hx hxp => by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hxp
    exact sp.early i hi j (mem_range.mp hj) hx
  have hro : Outside {sp.l i} (wspec hN β (past sp.l i) (sp.r i)) :=
    outside_of_local (local_wspec hN β _ (sp.locr i hi)) fun x hx hxl => by
      rw [mem_singleton] at hxl
      subst hxl
      rcases mem_union.mp hx with h1 | h1
      · exact sp.own i hi h1
      · exact sp.apart i hi h1
  have e : wspec hN β (past sp.l i) F = wspec hN β (past sp.l i) (sp.f i + sp.r i) :=
    congrArg (wspec hN β (past sp.l i)) (sp.dec i hi)
  rw [e, wspec_add, wspec_of_outside hN β _ _ hfo, cv_add_outside hN β _ _ _ hro]

/-- **The variance is at least the conditional-variance floor of a sparse split**:
`∑_{i<m} ν(cv_{l_i} f_i) ≤ ν(F²) − ν(F)²`, at every `N ≠ 0` and every real `β`. DERIVED: `2` the squares. -/
theorem var_ge_splitFloor (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m) :
    splitFloor hN β sp ≤ periodicState hN β (F * F) - periodicState hN β F ^ 2 := by
  have hsum : splitFloor hN β sp
      = ∑ i ∈ range m, periodicState hN β (cv hN β {sp.l i} (wspec hN β (past sp.l i) F)) :=
    sum_congr rfl fun i hi => by rw [chain_term hN β sp (mem_range.mp hi)]
  have hc := chain hN β sp.l F m
  have hJ := state_sq_le (periodicState hN β) (wspec hN β (past sp.l m) F)
  rw [periodicState_dlr] at hJ
  rw [hsum]
  linarith

/-- **The second moment is at least the floor**: `∑_{i<m} ν(cv_{l_i} f_i) ≤ ν(F²)`. DERIVED: `2` the square. -/
theorem sq_ge_splitFloor (hN : N ≠ 0) (β : ℝ) {F : C(IConf (SU N), ℝ)} {m : ℕ} (sp : SparseSplit F m) :
    splitFloor hN β sp ≤ periodicState hN β (F ^ 2) := by
  have h := var_ge_splitFloor hN β sp
  rw [sq F]
  nlinarith [sq_nonneg (periodicState hN β F)]

#print axioms not_mem_bdLinks
#print axioms apart_of_plaq
#print axioms splitFloor_nonneg
#print axioms chain_term
#print axioms var_ge_splitFloor
#print axioms sq_ge_splitFloor

/-! ## 4. The lowest mode and the count bound -/

section Tower

open MassGap.ClayTreeG (schedSU)
open MassGap.ContinuumField (LField)
open MassGap.CountMoments (scrSide)
open MassGap.ApertureFinite (bareScreen boxF BareRatio heatScreen count_heatScreen)
open MassGap.BareRatioProof (LowModeRatio bot0 bareRatio_of_lowMode)

variable (N) [NeZero N]

/-- The coupling of step `k` of `schedSU N`. DERIVED: `1` from the hypothesis `1 ≤ N` of the schedule. -/
def βk (k : ℕ) : ℝ :=
  MassGap.ContinuumSchwinger.dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero (NeZero.ne N)) k

/-- **The operator norm within `Q'` of a conditional-variance floor of the lowest mode**: eventually, for every
`O ∈ D`, some `c ≥ 0` bounding the bare covariance of the screen box in operator norm, a sparse split of the
lowest-mode field, and `c ≤ Q' ∑_i ν_k(cv_{l_i} f_i)`. DERIVED: `2` the squares; `0` the signs. -/
def SplitRatio (D : Set (LField (SU N))) (ρ Q' : ℝ) : Prop :=
  0 ≤ Q' ∧ ∀ᶠ k in atTop, ∀ O ∈ D, ∀ hK : 0 < scrSide (schedSU N) ρ k, ∃ c : ℝ, 0 ≤ c ∧
    (∀ u : (Fin 4 → Fin (scrSide (schedSU N) ρ k)) → ℝ,
      (schedSU N).ν k ((∑ x, u x • bareScreen (schedSU N) ρ k O x) ^ 2) ≤ c * ∑ x, u x ^ 2) ∧
    ∃ (m : ℕ) (sp : SparseSplit
        (∑ x, boxF (scrSide (schedSU N) ρ k) x (bot0 _ hK) • bareScreen (schedSU N) ρ k O x) m),
      c ≤ Q' * splitFloor (NeZero.ne N) (βk N k) sp

/-- **`LowModeRatio` from a conditional-variance floor**: `SplitRatio N D ρ Q'` gives
`LowModeRatio (schedSU N) D ρ Q'`. DERIVED: no numeral. -/
theorem lowModeRatio_of_split (D : Set (LField (SU N))) {ρ Q' : ℝ} (h : SplitRatio N D ρ Q') :
    LowModeRatio (schedSU N) D ρ Q' := by
  obtain ⟨hQ, hev⟩ := h
  refine ⟨hQ, ?_⟩
  filter_upwards [hev] with k hk O hO hK
  obtain ⟨c, hc, hC, m, sp, hle⟩ := hk O hO hK
  refine ⟨c, hc, hC, hle.trans (mul_le_mul_of_nonneg_left ?_ hQ)⟩
  exact sq_ge_splitFloor (NeZero.ne N) (βk N k) sp

/-- **A finite aperture holds a finite count, from a conditional-variance floor**: for `ρ, θ > 0`,
`SplitRatio N D ρ Q'` bounds the heat screen's Rényi-½ count along `schedSU N`. DERIVED: `0` the signs. -/
theorem count_heatScreen_of_split (D : Set (LField (SU N))) {ρ θ Q' : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    (h : SplitRatio N D ρ Q') :
    ∃ Rb : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D,
      MassGap.ApertureCount.spRenyi
        (MassGap.ApertureCount.eig ((schedSU N).ν k) (heatScreen (schedSU N) θ ρ k O)) ≤ Rb :=
  count_heatScreen (schedSU N) D hρ hθ (bareRatio_of_lowMode (schedSU N) D hρ hθ (lowModeRatio_of_split N D h))

end Tower

#print axioms βk
#print axioms lowModeRatio_of_split
#print axioms count_heatScreen_of_split

end MassGap.PlaqShortDistance

end
