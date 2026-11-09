import Mathlib
import MassGap.PeriodicStateDLR

/-!
# MassGap.FocusZoom — the downward comparison (big box → box of size `R`) by conditioning, and what it reaches

`LoopZoom` reduces (E2') to the diagonal shell bound alone (`LoopZoom.zeroFluxGap_of_electricDiag`) and
finds that the chessboard comparison runs upward (tiles of size `R` glued into the torus of size `L`).
This module states the downward comparison in its weakest form on the real objects — conditioning the
periodic infinite-volume Wilson state on the outside of a focal box `Λ` of size `R` — proves what holds,
and names what remains.

## Evaluation

1. **The conditioning step holds and is exact** (proved, real objects). The periodic state
   `ν = PeriodicState.periodicState hN β` satisfies the DLR equations (`PeriodicStateDLR.periodicState_dlr`).
   From those alone, for any box `Λ` and continuous observables `X, Y`:
   * **`dlr_cov_split`** (law of total covariance): `Cov_ν(X, Y) = ν(γ_Λ(XY) − γ_Λ X · γ_Λ Y)
     + Cov_ν(γ_Λ X, γ_Λ Y)`, `γ_Λ = wspec hN β Λ` the box kernel with boundary condition. The first term
     is the **in-box term** (the box covariance at boundary condition `ω`, averaged over `ω`); the second
     is the **boundary term** (the covariance of the two box averages, which read only the observable's
     support and the box's boundary links, `S ∪ bdLinks Λ`, `WilsonDLR.isLocalOn_spec`).
   * **`wspec_mul_outside`, `cov_screen`**: if `Y` does not read `Λ`, `γ_Λ(XY) = γ_Λ X · Y` and
     `Cov_ν(X, Y) = Cov_ν(γ_Λ X, Y)`. Conditioning on the outside of a box around `X` alone replaces the
     loop by its box average and changes nothing else.
   * **`cov_le_of_focus`**: `BoxFocus Λ X Y ε` (the in-box covariance at most `ε` at every boundary
     condition) and `BoundaryLag Λ X Y ε'` give `|Cov_ν(X, Y)| ≤ ε + ε'`.
2. **The boundary-condition comparison holds in one form** (proved, real objects).
   **`spec_le_of_boundary`**: for `f ≥ 0` measurable, bounded and reading only the links of `Λ`, at
   any two boundary conditions,
   `γ_Λ(f | ω) ≤ e^{4 |β| c_Λ} γ_Λ(f | ω')`, `c_Λ = #(boundaryPlaqs Λ \ plaqsIn Λ)` the plaquettes that
   cross the surface of `Λ`. The abstract form is **`ratio_le_of_weight`** (two weights within a factor
   `e^K` of each other give expectations of a nonnegative `f` within `e^{2K}`). Argued, not a declaration:
   the periodic torus of side `R` is not a boundary condition of the box (its wrap plaquettes read the
   box's own links), but its weight differs from the free box weight by the same kind of factor, so
   `ratio_le_of_weight` compares the box at any `ω` with the `R`-torus at constant `e^{4 |β| c}` as well.
3. **Circularity test** (argued, on the declarations above).
   * **Box around `X` alone** (`cov_screen`): the decay of `Cov_ν(X_0, Y_t)` in `t` is the decay of
     `Cov_ν(γ_Λ X_0, Y_t)`, a correlation between a functional of the box surface and an observable at
     distance `t − R`. Bounding it is decay of correlations beyond `R`: the gap. **Circular.**
   * **Box containing both `X_0` and `Y_t`** (`dlr_cov_split`): the boundary term is the covariance of two
     surface functionals of the same box carried through its outside, again a correlation at separation
     `t` outside the box: **circular** for the same reason. The in-box term needs `BoxFocus` at
     `ε ≈ e^{−c σ R t}` **uniformly in the boundary condition `ω`**. The only uniformity proved is
     `spec_le_of_boundary`, whose constant `e^{4 |β| c_Λ}` has `c_Λ` the surface plaquette count in
     lattice units: at fixed physical `R` and `t`, `c_Λ ~ (R/a)²(t/a) + (R/a)³`, so the exponent
     `4 |β| c_Λ` is unbounded as `β → ∞` (an absolute bound on a scale-closed set is vacuous). It also compares nonnegative
     expectations only; the in-box covariance is signed, and `γ_Λ(XY) − γ_Λ X γ_Λ Y` at `ω` is not
     controlled by its value at `ω'` through a weight ratio. Uniformity of boundary effects at scale `R`
     is a finite-size mixing condition at that scale; whether it holds uniformly in `β` is the content of
     the gap at scale `R`. **Not reached; not circular in the sense of asking decay beyond `R`, but asks
     uniformity in `ω`, which no declaration in the tree gives.**
   **Decision**: the downward comparison exists exactly as the DLR split; its boundary term is circular
   in both placements, and its in-box term is a uniform-in-boundary box bound at scale `R` that the tree
   does not supply. There is no non-circular inequality from the box of size `R` (with boundary) to the
   periodic `R`-torus electric-flux quantity: the only boundary comparison available is the weight
   ratio, vacuous at fixed physical `R` uniformly in `β`, and it does not act on covariances. Further
   (from `LoopZoom`, argued there): the `R × R` loop on the `R`-torus has holonomy the commutator
   `P_b P_a P_b⁻¹ P_a⁻¹`, of zero centre charge, so it is not the winding state (V) prices.
4. **The focus rule** (proved, what it adds). Reading the shell of radius `R` at its own scale gives the
   cost `c σ R + c'/R`; **`focus_attains`**: at `R* = √c' / √(c σ)` it equals `2 √(c c' σ)`, the floor
   `AttractCost.two_sqrt_le_cost` and the first factor `e^{−√(c c' σ) t/2}` of `LoopZoom.diagRate`.
   So "in focus" is the equality case of a bound already used, and the shell construction
   (`ElectricLoops.shell`: shell `k` orthogonal to every loop of radius `R_{k−1}`) already removes the
   content resolvable at smaller scales. On the real objects focusing adds no inequality; it does not
   supply the diagonal shell bound.

## How the remainder would feed `LoopZoom.zeroFluxGap_of_electricDiag` (argued)

`cov_le_of_focus` bounds a connected correlator of the periodic infinite-volume state by
`BoxFocus + BoundaryLag`. `PeriodicReduce.periodic_form_pow` reads the periodic state's pairings
`ν(θx · Sᶜx)` as transfer elements of the gauge-invariant periodic transfer, so `BoxFocus` and
`BoundaryLag` at the focal box `Λ_R × [0, t]`, for every loop state of radius at most `R_k`, at
`ε + ε' ≤ μ² e^{−(c σ R_k + c'/R_k) t} ‖x‖²` and uniformly over the shell, would give the diagonal
bound for that transfer. `zeroFluxGap_of_electricDiag` is stated on the finite slice operator
`trivKN 2 β n i` at `Ω = φ_{g₀}`; the bridge from the periodic state's connected pairings to that slice's
shell elements is not in the tree, and the uniformity over a shell is the clustering `LoopZoom` found
circular (`LoopZoom.block_rayleigh`).

## What is proved

* §1 (abstract): `ratio_le_of_weight`.
* §2 (`GibbsSpec`, any measurable group, density in `[0, 2]`): `wt_le_wt`, `spec_le_of_boundary`.
* §3 (periodic `SU(N)` state): `stateCov`, `dlr_cov_split`, `wspec_mul_outside`, `cov_screen`,
  `abs_state_le`, `BoxFocus`, `BoundaryLag`, `cov_le_of_focus`.
* §4: `focus_attains`.

DERIVED (module-wide): `2` is the range bound `φ ≤ 2` of the plaquette density and the doubling of `K` in
the ratio of two quotients; `4 = 2 · 2` is that range bound times the two sides of the ratio; `1` is the
constant configuration used to read off `0 ≤ ε`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FocusZoom

open MeasureTheory

/-! ## 1. Two weights within `e^K` give expectations within `e^{2K}` -/

/-- **The weight-ratio comparison.** For weights `0 ≤ w'`, `w ≤ e^K w'` and `w' ≤ e^K w` pointwise, a
nonnegative `f`, and `0 < ∫ w'`: `(∫ f w)/(∫ w) ≤ e^{2K} (∫ f w')/(∫ w')`. -/
theorem ratio_le_of_weight {α : Type*} [MeasurableSpace α] (m : Measure α) {f w w' : α → ℝ} {K : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hw'0 : ∀ x, 0 ≤ w' x) (hw1 : ∀ x, w x ≤ Real.exp K * w' x)
    (hw2 : ∀ x, w' x ≤ Real.exp K * w x)
    (hfw : Integrable (fun x => f x * w x) m) (hfw' : Integrable (fun x => f x * w' x) m)
    (hiw : Integrable w m) (hiw' : Integrable w' m) (hpos : 0 < ∫ x, w' x ∂m) :
    (∫ x, f x * w x ∂m) / (∫ x, w x ∂m)
      ≤ Real.exp (2 * K) * ((∫ x, f x * w' x ∂m) / (∫ x, w' x ∂m)) := by
  have hA : ∫ x, f x * w x ∂m ≤ Real.exp K * ∫ x, f x * w' x ∂m := by
    rw [← integral_const_mul]
    refine integral_mono hfw (hfw'.const_mul _) fun x => ?_
    have := mul_le_mul_of_nonneg_left (hw1 x) (hf x)
    simp only
    nlinarith [this]
  have hB : ∫ x, w' x ∂m ≤ Real.exp K * ∫ x, w x ∂m := by
    rw [← integral_const_mul]
    exact integral_mono hiw' (hiw.const_mul _) hw2
  have heK := Real.exp_pos K
  have hd : 0 < ∫ x, w x ∂m := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have ha : 0 ≤ ∫ x, f x * w' x ∂m := integral_nonneg fun x => mul_nonneg (hf x) (hw'0 x)
  set a := ∫ x, f x * w' x ∂m
  set b := ∫ x, w' x ∂m
  set d := ∫ x, w x ∂m
  rw [div_le_iff₀ hd]
  have hab : 0 ≤ a / b := div_nonneg ha hpos.le
  have e1 : a = a / b * b := by field_simp
  have e2 : Real.exp (2 * K) = Real.exp K * Real.exp K := by rw [two_mul, Real.exp_add]
  calc ∫ x, f x * w x ∂m ≤ Real.exp K * a := hA
    _ = Real.exp K * (a / b * b) := by rw [← e1]
    _ ≤ Real.exp K * (a / b * (Real.exp K * d)) := by gcongr
    _ = Real.exp (2 * K) * (a / b) * d := by rw [e2]; ring

/-! ## 2. The boundary-condition comparison on the Wilson specification -/

section Spec

open MassGap.GibbsSpec

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- **The Boltzmann weight at two boundary conditions.** Only the plaquettes crossing the surface of `Λ`
(`boundaryPlaqs Λ \ plaqsIn Λ`) read the boundary condition; each contributes at most `2`, so
`wt(u, ω) ≤ e^{|β| · 2 c_Λ} wt(u, ω')`. -/
theorem wt_le_wt {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink)
    (u : VConf G Λ) (ω ω' : IConf G) :
    wt φ β Λ u ω
      ≤ Real.exp (|β| * (((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ) * 2)) * wt φ β Λ u ω' := by
  unfold wt
  rw [← Real.exp_add, Real.exp_le_exp]
  have hs : ∀ η : IConf G, actionOn φ (boundaryPlaqs Λ) (splice Λ u η)
      = actionOn φ (plaqsIn Λ) (splice Λ u η)
        + actionOn φ (boundaryPlaqs Λ \ plaqsIn Λ) (splice Λ u η) :=
    fun η => actionOn_sdiff φ (plaqsIn_subset_boundaryPlaqs Λ) _
  have hin : actionOn φ (plaqsIn Λ) (splice Λ u ω) = actionOn φ (plaqsIn Λ) (splice Λ u ω') :=
    actionOn_congr φ _ _ _ fun q hq l hl => by
      have hlΛ := (mem_plaqsIn.1 hq) l hl
      rw [splice_mem hlΛ, splice_mem hlΛ]
  rw [hs ω, hs ω', hin]
  set I := actionOn φ (plaqsIn Λ) (splice Λ u ω')
  set c : ℝ := ((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ)
  set a := actionOn φ (boundaryPlaqs Λ \ plaqsIn Λ) (splice Λ u ω)
  set b := actionOn φ (boundaryPlaqs Λ \ plaqsIn Λ) (splice Λ u ω')
  have ha0 : 0 ≤ a := actionOn_nonneg hφ0 _ _
  have ha2 : a ≤ c * 2 := actionOn_le hφ2 _ _
  have hb0 : 0 ≤ b := actionOn_nonneg hφ0 _ _
  have hb2 : b ≤ c * 2 := actionOn_le hφ2 _ _
  have hab : |a - b| ≤ c * 2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have key : -β * (a - b) ≤ |β| * (c * 2) := by
    calc -β * (a - b) ≤ |-β * (a - b)| := le_abs_self _
      _ = |β| * |a - b| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * (c * 2) := mul_le_mul_of_nonneg_left hab (abs_nonneg β)
  have e : -β * (I + a) = -β * (I + b) + -β * (a - b) := by ring
  rw [e]
  linarith

/-- **The boundary-condition comparison.** For `f ≥ 0` measurable, bounded, reading only the links of
`Λ`: at any two boundary conditions, `γ_Λ(f | ω) ≤ e^{4 |β| c_Λ} γ_Λ(f | ω')`, where
`c_Λ = #(boundaryPlaqs Λ \ plaqsIn Λ)` counts the plaquettes crossing the surface of `Λ`. -/
theorem spec_le_of_boundary {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) (hf0 : ∀ U, 0 ≤ f U) {C : ℝ} (hC : ∀ U, |f U| ≤ C)
    (hloc : ∀ (u : VConf G Λ) (ω ω' : IConf G), f (splice Λ u ω) = f (splice Λ u ω'))
    (ω ω' : IConf G) :
    spec φ β Λ μ f ω
      ≤ Real.exp (4 * (|β| * ((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ))) * spec φ β Λ μ f ω' := by
  have key := ratio_le_of_weight (vol μ Λ) (f := fun u => f (splice Λ u ω))
    (w := fun u => wt φ β Λ u ω) (w' := fun u => wt φ β Λ u ω')
    (K := |β| * (((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ) * 2))
    (fun u => hf0 _) (fun u => (wt_pos φ β Λ u ω').le)
    (fun u => wt_le_wt hφ0 hφ2 β Λ u ω ω') (fun u => wt_le_wt hφ0 hφ2 β Λ u ω' ω)
    (integrable_num hφ hφ0 hφ2 β Λ μ hf hC ω)
    (by
      have h := integrable_num hφ hφ0 hφ2 β Λ μ hf hC ω'
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [hloc u ω' ω])
    (integrable_wt hφ hφ0 hφ2 β Λ μ ω) (integrable_wt hφ hφ0 hφ2 β Λ μ ω')
    (by have h := part_pos hφ hφ0 hφ2 β Λ μ ω'; unfold part at h; exact h)
  have e : (fun u : VConf G Λ => f (splice Λ u ω') * wt φ β Λ u ω')
      = fun u => f (splice Λ u ω) * wt φ β Λ u ω' := funext fun u => by rw [hloc u ω' ω]
  unfold spec num part
  rw [e, show (4 : ℝ) * (|β| * ((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ))
    = 2 * (|β| * (((boundaryPlaqs Λ \ plaqsIn Λ).card : ℝ) * 2)) by ring]
  exact key

end Spec

/-! ## 3. Conditioning the periodic state on the outside of a box -/

section Periodic

open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.PeriodicStateDLR (wspec wspec_apply periodicState_dlr)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)

/-- The connected correlator of a state: `ν(f g) − ν(f) ν(g)`. -/
def stateCov {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : State X) (f g : C(X, ℝ)) : ℝ :=
  ν (f * g) - ν f * ν g

/-- A state is bounded by a pointwise bound. -/
theorem abs_state_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : State X) (f : C(X, ℝ))
    (x₀ : X) {ε : ℝ} (h : ∀ x, |f x| ≤ ε) : |ν f| ≤ ε :=
  (ν.abs_le_norm f).trans ((ContinuousMap.norm_le f ((abs_nonneg _).trans (h x₀))).2 fun x => by
    rw [Real.norm_eq_abs]; exact h x)

variable {N : ℕ}

/-- **The law of total covariance on the periodic state** (from the DLR equations alone):
`Cov_ν(X, Y) = ν(γ_Λ(XY) − γ_Λ X · γ_Λ Y) + Cov_ν(γ_Λ X, γ_Λ Y)`. -/
theorem dlr_cov_split (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ)) :
    stateCov (periodicState hN β) X Y
      = periodicState hN β (wspec hN β Λ (X * Y) - wspec hN β Λ X * wspec hN β Λ Y)
        + stateCov (periodicState hN β) (wspec hN β Λ X) (wspec hN β Λ Y) := by
  unfold stateCov
  rw [State.map_sub, periodicState_dlr hN β Λ (X * Y), periodicState_dlr hN β Λ X,
    periodicState_dlr hN β Λ Y]
  ring

/-- **An observable that does not read `Λ` leaves the box kernel**: `γ_Λ(X Y) = γ_Λ X · Y`. -/
theorem wspec_mul_outside (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    (hY : ∀ (u : VConf (SU N) Λ) (ω : IConf (SU N)), Y (splice Λ u ω) = Y ω) :
    wspec hN β Λ (X * Y) = wspec hN β Λ X * Y := by
  ext ω
  rw [ContinuousMap.mul_apply, wspec_apply, wspec_apply]
  unfold spec num
  have h : ∀ u : VConf (SU N) Λ,
      (⇑(X * Y)) (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ u ω
        = (X (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ u ω) * Y ω := fun u => by
    rw [ContinuousMap.mul_apply, hY]; ring
  simp_rw [h, integral_mul_const]
  ring

/-- **Screening**: with `Y` not reading `Λ`, `Cov_ν(X, Y) = Cov_ν(γ_Λ X, Y)`. Conditioning on the
outside of a box around `X` replaces `X` by its box average and nothing else. -/
theorem cov_screen (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    (hY : ∀ (u : VConf (SU N) Λ) (ω : IConf (SU N)), Y (splice Λ u ω) = Y ω) :
    stateCov (periodicState hN β) X Y = stateCov (periodicState hN β) (wspec hN β Λ X) Y := by
  unfold stateCov
  rw [← periodicState_dlr hN β Λ (X * Y), wspec_mul_outside hN β Λ X Y hY,
    periodicState_dlr hN β Λ X]

/-- **The in-box term, uniform in the boundary condition** (named remainder): at every `ω`, the box
covariance `γ_Λ(XY | ω) − γ_Λ(X | ω) γ_Λ(Y | ω)` is at most `ε` in absolute value. Not proved. -/
def BoxFocus (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ)) (ε : ℝ) : Prop :=
  ∀ ω, |wspec hN β Λ (X * Y) ω - wspec hN β Λ X ω * wspec hN β Λ Y ω| ≤ ε

/-- **The boundary term** (named remainder): the covariance of the two box averages is at most `ε'`.
Not proved; bounding it is a correlation at separation beyond the box (module docstring, §3).
DERIVED: no numeral in the definition; `3` is the module docstring's section number. -/
def BoundaryLag (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ)) (ε' : ℝ) : Prop :=
  |stateCov (periodicState hN β) (wspec hN β Λ X) (wspec hN β Λ Y)| ≤ ε'

/-- **The two named remainders bound the connected correlator**: `|Cov_ν(X, Y)| ≤ ε + ε'`. -/
theorem cov_le_of_focus (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X Y : C(IConf (SU N), ℝ))
    {ε ε' : ℝ} (hbox : BoxFocus hN β Λ X Y ε) (hbd : BoundaryLag hN β Λ X Y ε') :
    |stateCov (periodicState hN β) X Y| ≤ ε + ε' := by
  rw [dlr_cov_split hN β Λ X Y]
  refine (abs_add_le _ _).trans (add_le_add ?_ hbd)
  exact abs_state_le _ _ (fun _ => 1) fun ω => by
    rw [ContinuousMap.sub_apply, ContinuousMap.mul_apply]; exact hbox ω

end Periodic

/-! ## 4. The focus: the shell cost at its own scale attains the floor -/

/-- **In focus.** At `R* = √c' / √(c σ)` the shell cost `c σ R + c'/R` equals `2 √(c c' σ)`, the floor of
`AttractCost.two_sqrt_le_cost` and the first factor of `LoopZoom.diagRate`. -/
theorem focus_attains {c c' σ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hσ : 0 < σ) :
    0 < Real.sqrt c' / Real.sqrt (c * σ)
      ∧ c * σ * (Real.sqrt c' / Real.sqrt (c * σ)) + c' / (Real.sqrt c' / Real.sqrt (c * σ))
        = 2 * Real.sqrt (c * c' * σ) := by
  have hcs : 0 < c * σ := mul_pos hc hσ
  have ha : 0 < Real.sqrt (c * σ) := Real.sqrt_pos.2 hcs
  have hb : 0 < Real.sqrt c' := Real.sqrt_pos.2 hc'
  refine ⟨div_pos hb ha, ?_⟩
  have ha2 : Real.sqrt (c * σ) ^ 2 = c * σ := Real.sq_sqrt hcs.le
  have hb2 : Real.sqrt c' ^ 2 = c' := Real.sq_sqrt hc'.le
  rw [show c * c' * σ = (c * σ) * c' by ring, Real.sqrt_mul hcs.le]
  set a := Real.sqrt (c * σ)
  set b := Real.sqrt c'
  rw [← ha2, ← hb2]
  field_simp
  ring

#print axioms ratio_le_of_weight
#print axioms spec_le_of_boundary
#print axioms dlr_cov_split
#print axioms cov_screen
#print axioms cov_le_of_focus
#print axioms focus_attains

end MassGap.FocusZoom
