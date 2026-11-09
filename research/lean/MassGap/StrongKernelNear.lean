import Mathlib
import MassGap.BoxFocusTest

/-!
# MassGap.StrongKernelNear — `KernelNear` at strong coupling, by Dobrushin's single-link sweep

`BoxFocusTest.KernelNear Δ X δ` asks that the Wilson box kernel `γ_Δ X` lie within `δ` of one constant at
every boundary condition. This module proves it on the real Wilson specification for small `|β|`, with `δ`
decaying geometrically in the depth of `X`'s support inside `Δ`.

## 1. The single-link influence (proved, real specification)

`spec_single_osc`: for a bounded measurable `f` whose per-link oscillation is `v` (`LinkOsc f v`: changing the
link `l` alone moves `f` by at most `v l`), the single-link kernel `γ_{i}` satisfies, when two boundary
conditions differ only at the link `j`,
`|γ_{i} f(η) − γ_{i} f(η')| ≤ v j + infl β i j · v i`, with
`infl β i j = 2 (e^{2 K_{ij}} − 1)`, `K_{ij} = |β| · 2 · #(plaquettes through i crossing the surface of {i})`
when `j` is read by a plaquette through `i` (`j ∈ nbr i`) and `K_{ij} = 0` otherwise. The weights at the two
boundary conditions are within `e^{K_{ij}}` (`FocusZoom.wt_le_wt`; equal when `j ∉ nbr i`), and two
averages of one function of oscillation `E` under weights within `e^{K}` differ by at most `2 (e^{2K} − 1) E`
(`avg_sub_le`, from `FocusZoom.ratio_le_of_weight`). `linkOsc_spec_single` packages this as
`LinkOsc (γ_{i} f) (upd β i v)`: the oscillation at `i` is set to `0` and `infl β i j · v i` is added at
every `j`.

Counts (proved): `#(touching l) ≤ 16`, `#(boundaryPlaqs {i}) ≤ 16`, `#(nbr i) ≤ 64`, so
`infl β i j ≤ c0 β = 2 (e^{64 |β|} − 1)` and the Dobrushin row sum is at most `64 · c0 β`. (These are the
crude counts of the oriented, degenerate-inclusive plaquette encoding `IPlaq`; the physical count is
`2(d−1) = 6` plaquettes and `18` neighbouring links.)

## 2. The sweep (proved)

DLR consistency (`GibbsSpec.dlr_consistent`) gives `γ_Δ = γ_Δ ∘ γ_{i}` for `i ∈ Δ`, so `γ_Δ X = γ_Δ g` for
every `g` obtained from `X` by a finite sequence of single-link kernels inside `Δ`. Fix a depth
`d : ILink → ℕ` vanishing off `Δ` and `1`-Lipschitz along plaquette adjacency inside `Δ`
(`d i ≤ d j + 1` for `j ∈ nbr i`), and `θ ∈ (0, 1]` with `64 · c0 β < θ`. With the weights `ρ l = θ^{d l}`:
* `sum_upd_le`: one update at `i ∈ Δ` lowers `θ · Σ_T ρ v` by at least `(θ − 64 c0) ρ_i v_i`, for every
  finite `T ∋ i`. So the weighted oscillation over `Δ ∪ nbr(Δ)` never rises, and, updating at the link that
  maximises `ρ v` on `Δ`, the weighted oscillation inside `Δ` contracts by `q = 1 − (θ − 64 c0)/(θ |Δ|) < 1`.
* `spec_abs_sub_le_sum`: a kernel of a function local on `U` with oscillation vector `v` moves by at most
  `Σ_U v` between any two boundary conditions.
As the number of updates grows the inside part goes to `0`; the outside part (where `ρ = 1`) stays below its
initial value `2 Σ_{l ∈ A} θ^{d l}`, `A` the support of `X`.

## 3. The result (proved)

* `kernel_near_strong` (any measurable density in `[0, 2]`, any probability measure on `G`):
  `|γ_Δ X(ω) − γ_Δ X(ω')| ≤ 2 Σ_{l ∈ A} θ^{d l}` for `|X| ≤ 1`, `X` local on `A ⊆ Δ`.
* `kernelNear_strong` (Wilson, `SU(N)`): `KernelNear Δ X (2 Σ_{l∈A} θ^{d l})`.
* `kernelNear_strong_explicit`: at `|β| ≤ β₀ = 2^{-16}` with `θ = 1/2`, and `L ≤ d l` on `A`:
  `KernelNear Δ X (2 |A| 2^{−L})`. A decay rate `log 2` per unit of depth, in lattice units.

## 4. What weak coupling needs (argued)

The proof uses the total-variation influence of one link on one link, `infl ≈ 4 K_{ij} = 8 |β|·(plaquettes)`.
The bound grows with `β`, and the influence cannot stay small: as `β → ∞` the conditional law of a link given
its neighbours concentrates near the configuration they fix, so two neighbouring configurations give nearly
disjoint laws; the coefficient (a total-variation distance) tends to `1`, so the row sum tends to `18 > 1`.
So the single-link condition holds only below a fixed `β` (of order `10^{-3}` with the physical counts `6`/`18`
in this module's per-link exponent, or `10^{-2}` if only the plaquette shared by `i` and `j` enters `K_{ij}`;
estimates; `2^{-16}` with the crude counts proved here), and with it any statement at fixed
physical size, since fixed physical size means `β → ∞` with the box growing in lattice units. What is needed
instead is the same contraction for blocks of a fixed physical size `b` (`BlockDobrushin.DobCond` at block
scale), with entries read on a class of tests the one-shell kernel keeps (`BlockDobrushin` §3 items 2–3:
total variation fails for the same concentration reason at block level). That is the physical-units block
route of `BlockDobrushin`: `KernelNear` at the one physical scale `b`, uniformly in `β`. The present module
supplies the sweep (§2) in sequential form for per-link sup-oscillation. A block version needs the block
analogue of `spec_single_osc`, and the sweep must be re-read on the class of tests `BlockDobrushin` §3 names,
since total variation fails at block scale; this is not built.

DERIVED (module-wide): `2` the range of the density and the two sides of a constant; `16 = 4 · 4` the
candidate plaquettes per link of `touching`; `64 = 16 · 4` the links they read; `32 = 16 · 2` the bound on
`K_i / |β|`; `2^{-16}` and `1/2` the explicit `β₀` and `θ`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StrongKernelNear

open MeasureTheory Filter MassGap.GibbsSpec

/-! ## 1. Two weighted averages -/

/-- Two averages of `h` under weights within `e^K` of each other differ by at most `(e^{2K} − 1) · 2E`,
`E` the oscillation of `h`. -/
theorem avg_sub_le {α : Type*} [MeasurableSpace α] (m : Measure α) {h w w' : α → ℝ} {K E : ℝ}
    (x0 : α) (hK : 0 ≤ K) (_hw0 : ∀ x, 0 ≤ w x) (hw'0 : ∀ x, 0 ≤ w' x)
    (hw1 : ∀ x, w x ≤ Real.exp K * w' x) (hw2 : ∀ x, w' x ≤ Real.exp K * w x)
    (hiw : Integrable w m) (hiw' : Integrable w' m) (hpos : 0 < ∫ x, w x ∂m)
    (hpos' : 0 < ∫ x, w' x ∂m)
    (hhw : Integrable (fun x => h x * w x) m) (hhw' : Integrable (fun x => h x * w' x) m)
    (hE : ∀ x, |h x - h x0| ≤ E) :
    (∫ x, h x * w x ∂m) / (∫ x, w x ∂m) - (∫ x, h x * w' x ∂m) / (∫ x, w' x ∂m)
      ≤ (Real.exp (2 * K) - 1) * (2 * E) := by
  have hg0 : ∀ x, 0 ≤ h x - (h x0 - E) := fun x => by
    have := (abs_le.1 (hE x)).1; linarith
  have hg2 : ∀ x, h x - (h x0 - E) ≤ 2 * E := fun x => by
    have := (abs_le.1 (hE x)).2; linarith
  have hfun : ∀ u : α → ℝ, (fun x => (h x - (h x0 - E)) * u x)
      = fun x => h x * u x - (h x0 - E) * u x := fun u => by funext x; ring
  have hint : ∀ {u : α → ℝ}, Integrable u m → Integrable (fun x => h x * u x) m →
      Integrable (fun x => (h x - (h x0 - E)) * u x) m := by
    intro u hu hhu
    rw [hfun u]; exact hhu.sub (hu.const_mul _)
  have hsplit : ∀ {u : α → ℝ}, Integrable u m → Integrable (fun x => h x * u x) m →
      (∫ x, (h x - (h x0 - E)) * u x ∂m) = (∫ x, h x * u x ∂m) - (h x0 - E) * ∫ x, u x ∂m := by
    intro u hu hhu
    rw [hfun u, integral_sub hhu (hu.const_mul _), integral_const_mul]
  have hR := MassGap.FocusZoom.ratio_le_of_weight m (f := fun x => h x - (h x0 - E)) hg0 hw'0 hw1
    hw2 (hint hiw hhw) (hint hiw' hhw') hiw hiw' hpos'
  have e1 : ((∫ x, h x * w x ∂m) - (h x0 - E) * ∫ x, w x ∂m) / (∫ x, w x ∂m)
      = (∫ x, h x * w x ∂m) / (∫ x, w x ∂m) - (h x0 - E) := by
    rw [sub_div, mul_div_assoc, div_self hpos.ne', mul_one]
  have e2 : ((∫ x, h x * w' x ∂m) - (h x0 - E) * ∫ x, w' x ∂m) / (∫ x, w' x ∂m)
      = (∫ x, h x * w' x ∂m) / (∫ x, w' x ∂m) - (h x0 - E) := by
    rw [sub_div, mul_div_assoc, div_self hpos'.ne', mul_one]
  rw [hsplit hiw hhw, hsplit hiw' hhw', e1, e2] at hR
  have hP2 : (∫ x, h x * w' x ∂m) / (∫ x, w' x ∂m) - (h x0 - E) ≤ 2 * E := by
    rw [← e2, div_le_iff₀ hpos', ← hsplit hiw' hhw']
    calc ∫ x, (h x - (h x0 - E)) * w' x ∂m ≤ ∫ x, 2 * E * w' x ∂m :=
          integral_mono (hint hiw' hhw') (hiw'.const_mul _)
            fun x => mul_le_mul_of_nonneg_right (hg2 x) (hw'0 x)
      _ = 2 * E * ∫ x, w' x ∂m := integral_const_mul _ _
  have hex : 1 ≤ Real.exp (2 * K) := Real.one_le_exp (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hex) (sub_nonneg.2 hP2)]

/-- **The two-sided single-link comparison** in the abstract: `a` within `D` of `h` pointwise, `h` of
oscillation `E`, weights within `e^K`. -/
theorem abs_avg_sub_le {α : Type*} [MeasurableSpace α] (m : Measure α) {a h w w' : α → ℝ}
    {K D E : ℝ} (x0 : α) (hK : 0 ≤ K) (hw0 : ∀ x, 0 ≤ w x) (hw'0 : ∀ x, 0 ≤ w' x)
    (hw1 : ∀ x, w x ≤ Real.exp K * w' x) (hw2 : ∀ x, w' x ≤ Real.exp K * w x)
    (hiw : Integrable w m) (hiw' : Integrable w' m) (hpos : 0 < ∫ x, w x ∂m)
    (hpos' : 0 < ∫ x, w' x ∂m) (haw : Integrable (fun x => a x * w x) m)
    (hhw : Integrable (fun x => h x * w x) m) (hhw' : Integrable (fun x => h x * w' x) m)
    (hD : ∀ x, |a x - h x| ≤ D) (hE : ∀ x, |h x - h x0| ≤ E) :
    |(∫ x, a x * w x ∂m) / (∫ x, w x ∂m) - (∫ x, h x * w' x ∂m) / (∫ x, w' x ∂m)|
      ≤ D + 2 * (Real.exp (2 * K) - 1) * E := by
  have h1 := avg_sub_le m x0 hK hw0 hw'0 hw1 hw2 hiw hiw' hpos hpos' hhw hhw' hE
  have h2 := avg_sub_le m x0 hK hw'0 hw0 hw2 hw1 hiw' hiw hpos' hpos hhw' hhw hE
  have h3 : |(∫ x, a x * w x ∂m) / (∫ x, w x ∂m) - (∫ x, h x * w x ∂m) / (∫ x, w x ∂m)| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have e : (∫ x, a x * w x ∂m) - (∫ x, h x * w x ∂m) = ∫ x, (a x - h x) * w x ∂m := by
      rw [← integral_sub haw hhw]; congr 1; funext x; ring
    rw [e]
    have hn := norm_integral_le_of_norm_le (hiw.const_mul D)
      (Filter.Eventually.of_forall fun x => (by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 x)]
        exact mul_le_mul_of_nonneg_right (hD x) (hw0 x) : ‖(a x - h x) * w x‖ ≤ D * w x))
    rw [Real.norm_eq_abs, integral_const_mul] at hn
    exact hn
  rw [abs_le] at h3 ⊢
  constructor <;> nlinarith [h1, h2, h3.1, h3.2]

/-! ## 2. Per-link oscillation -/

section Osc

variable {G : Type}

/-- **Per-link oscillation**: changing the link `l` alone moves `f` by at most `v l`. -/
def LinkOsc (f : IConf G → ℝ) (v : ILink → ℝ) : Prop :=
  ∀ (l : ILink) (η η' : IConf G), (∀ l', l' ≠ l → η l' = η' l') → |f η - f η'| ≤ v l

/-- `f` reads only the links of `U`. -/
def IsLocalOn (U : Finset ILink) (f : IConf G → ℝ) : Prop :=
  ∀ η η' : IConf G, (∀ l ∈ U, η l = η' l) → f η = f η'

theorem abs_sub_le_sum_of_off {f : IConf G → ℝ} {v : ILink → ℝ} (hf : LinkOsc f v)
    (T : Finset ILink) :
    ∀ η η' : IConf G, (∀ l, l ∉ T → η l = η' l) → |f η - f η'| ≤ ∑ l ∈ T, v l := by
  refine Finset.induction_on T ?_ ?_
  · intro η η' h
    have : η = η' := funext fun l => h l (Finset.notMem_empty l)
    subst this; simp
  · intro a T haT ih η η' h
    rw [Finset.sum_insert haT]
    have h1 : |f η - f (Function.update η a (η' a))| ≤ v a :=
      hf a _ _ fun l hl => (Function.update_of_ne hl _ _).symm
    have h2 : |f (Function.update η a (η' a)) - f η'| ≤ ∑ l ∈ T, v l := by
      refine ih _ _ fun l hl => ?_
      by_cases hla : l = a
      · subst hla; simp
      · rw [Function.update_of_ne hla]; exact h l (by simp [hla, hl])
    calc |f η - f η'| ≤ |f η - f (Function.update η a (η' a))|
          + |f (Function.update η a (η' a)) - f η'| := abs_sub_le _ _ _
      _ ≤ v a + ∑ l ∈ T, v l := add_le_add h1 h2

/-- **A local function moves by at most the summed oscillation over its links.** -/
theorem abs_sub_le_sum_local {f : IConf G → ℝ} {v : ILink → ℝ} {U : Finset ILink}
    (hf : LinkOsc f v) (hloc : IsLocalOn U f) (η η' : IConf G) :
    |f η - f η'| ≤ ∑ l ∈ U, v l := by
  have hζ : f (fun l => if l ∈ U then η' l else η l) = f η' :=
    hloc _ _ fun l hl => by simp [hl]
  calc |f η - f η'| = |f η - f (fun l => if l ∈ U then η' l else η l)| := by rw [hζ]
    _ ≤ ∑ l ∈ U, v l := abs_sub_le_sum_of_off hf U η _ fun l hl => by simp [hl]

end Osc

/-! ## 3. Counts, neighbours, influence -/

/-- The links read by the plaquettes through `i`. -/
def nbr (i : ILink) : Finset ILink := (boundaryPlaqs {i}).biUnion fun q => (ilinks q).toFinset

theorem card_touching_le (l : ILink) : (touching l).card ≤ 16 := by
  unfold touching
  exact Finset.card_biUnion_le.trans
    ((Finset.sum_le_sum fun ν _ => Finset.card_le_four).trans (by simp))

theorem card_boundaryPlaqs_single_le (i : ILink) : (boundaryPlaqs {i}).card ≤ 16 := by
  unfold boundaryPlaqs
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.singleton_biUnion]
  exact card_touching_le i

theorem card_nbr_le (i : ILink) : (nbr i).card ≤ 64 := by
  unfold nbr
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ q ∈ boundaryPlaqs {i}, (ilinks q).toFinset.card ≤ ∑ _q ∈ boundaryPlaqs {i}, 4 :=
        Finset.sum_le_sum fun q _ => (List.toFinset_card_le _).trans (by simp [ilinks_eq])
    _ = (boundaryPlaqs {i}).card * 4 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 16 * 4 := Nat.mul_le_mul_right 4 (card_boundaryPlaqs_single_le i)

/-- The weight-ratio exponent of the single-link kernel at `i` (`FocusZoom.wt_le_wt` at `{i}`). -/
def Kw (β : ℝ) (i : ILink) : ℝ := |β| * (((boundaryPlaqs {i} \ plaqsIn {i}).card : ℝ) * 2)

theorem Kw_le (β : ℝ) (i : ILink) : Kw β i ≤ 32 * |β| := by
  unfold Kw
  have h : (boundaryPlaqs {i} \ plaqsIn {i}).card ≤ 16 :=
    (Finset.card_le_card Finset.sdiff_subset).trans (card_boundaryPlaqs_single_le i)
  have h' : ((boundaryPlaqs {i} \ plaqsIn {i}).card : ℝ) ≤ 16 := by exact_mod_cast h
  nlinarith [abs_nonneg β]

/-- The exponent seen by the link `j`: `Kw β i` if a plaquette through `i` reads `j`, else `0`. -/
def Kij (β : ℝ) (i j : ILink) : ℝ := if j ∈ nbr i then Kw β i else 0

theorem Kij_nonneg (β : ℝ) (i j : ILink) : 0 ≤ Kij β i j := by
  unfold Kij
  split_ifs
  · unfold Kw; positivity
  · exact le_rfl

/-- **The influence of the link `j` on the conditional law of the link `i`**, as a bound on the
oscillation it transmits. -/
def infl (β : ℝ) (i j : ILink) : ℝ := 2 * (Real.exp (2 * Kij β i j) - 1)

/-- The uniform bound on `infl`. DERIVED: `64 = 2 · 32`, the `2` of `infl`'s exponent times `Kw_le`'s
`32 = 16 · 2`; `2` the range of the density. -/
def c0 (β : ℝ) : ℝ := 2 * (Real.exp (64 * |β|) - 1)

theorem c0_nonneg (β : ℝ) : 0 ≤ c0 β := by
  unfold c0
  have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 64 * |β|)
  linarith

theorem infl_nonneg (β : ℝ) (i j : ILink) : 0 ≤ infl β i j := by
  unfold infl
  have := Real.one_le_exp (by linarith [Kij_nonneg β i j] : (0 : ℝ) ≤ 2 * Kij β i j)
  linarith

theorem infl_eq_zero {β : ℝ} {i j : ILink} (h : j ∉ nbr i) : infl β i j = 0 := by
  unfold infl Kij
  rw [if_neg h, mul_zero, Real.exp_zero, sub_self, mul_zero]

theorem infl_le (β : ℝ) (i j : ILink) : infl β i j ≤ c0 β := by
  unfold infl c0 Kij
  split_ifs
  · have := Kw_le β i
    have : Real.exp (2 * Kw β i) ≤ Real.exp (64 * |β|) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · have : 1 ≤ Real.exp (64 * |β|) := Real.one_le_exp (by positivity)
    rw [mul_zero, Real.exp_zero]
    linarith

/-! ## 4. The single-link kernel on the real specification -/

section Weight

variable {G : Type} [Group G]

/-- The single-link weight reads the boundary condition only on `nbr i`. -/
theorem wt_congr_nbr (φ : G → ℝ) (β : ℝ) (i : ILink) (u : VConf G {i}) {η η' : IConf G}
    (h : ∀ l ∈ nbr i, η l = η' l) : wt φ β {i} u η = wt φ β {i} u η' := by
  have hA : actionOn φ (boundaryPlaqs {i}) (splice {i} u η)
      = actionOn φ (boundaryPlaqs {i}) (splice {i} u η') :=
    actionOn_congr φ _ _ _ fun q hq l hl => by
      by_cases hli : l ∈ ({i} : Finset ILink)
      · rw [splice_mem hli, splice_mem hli]
      · rw [splice_not_mem hli, splice_not_mem hli]
        exact h l (Finset.mem_biUnion.mpr ⟨q, hq, List.mem_toFinset.mpr hl⟩)
  unfold wt; rw [hA]

/-- **The weight ratio under a change of the link `j`**: within `e^{K_{ij}}`. -/
theorem wt_le_exp_Kij {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (i j : ILink) (u : VConf G {i}) {η η' : IConf G} (h : ∀ l, l ≠ j → η l = η' l) :
    wt φ β {i} u η ≤ Real.exp (Kij β i j) * wt φ β {i} u η' := by
  unfold Kij
  split_ifs with hj
  · exact MassGap.FocusZoom.wt_le_wt hφ0 hφ2 β {i} u η η'
  · rw [Real.exp_zero, one_mul,
      wt_congr_nbr φ β i u (fun l hl => h l (fun hlj => hj (hlj ▸ hl)))]

end Weight

section Spec

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **The single-link influence bound on the real specification.** Two boundary conditions differing
only at `j`: the single-link kernel at `i` moves by at most `v j + infl β i j · v i`. -/
theorem spec_single_osc {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] {f : IConf G → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ η, |f η| ≤ B) {v : ILink → ℝ} (hosc : LinkOsc f v)
    (i j : ILink) {η η' : IConf G} (h : ∀ l, l ≠ j → η l = η' l) :
    |spec φ β {i} μ f η - spec φ β {i} μ f η'| ≤ v j + infl β i j * v i := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB η)
  have hint : ∀ ζ ζ' : IConf G, Integrable
      (fun u : VConf G {i} => f (splice {i} u ζ') * wt φ β {i} u ζ) (vol μ {i}) := fun ζ ζ' =>
    integrable_of_bounded _ ((hf.comp (measurable_splice_left _ ζ')).mul
        (measurable_wt_left hφ β _ ζ))
      (C := B * Real.exp (|β| * (((boundaryPlaqs ({i} : Finset ILink)).card : ℝ) * 2))) fun u => by
        rw [abs_mul, abs_of_pos (wt_pos φ β _ u ζ)]
        exact mul_le_mul (hB _) (wt_le hφ0 hφ2 β _ u ζ) (wt_pos φ β _ u ζ).le hB0
  have key := abs_avg_sub_le (vol μ {i}) (a := fun u => f (splice {i} u η))
    (h := fun u => f (splice {i} u η')) (w := fun u => wt φ β {i} u η)
    (w' := fun u => wt φ β {i} u η') (K := Kij β i j) (D := v j) (E := v i)
    (fun _ => 1) (Kij_nonneg β i j) (fun u => (wt_pos φ β _ u η).le)
    (fun u => (wt_pos φ β _ u η').le)
    (fun u => wt_le_exp_Kij hφ0 hφ2 β i j u h)
    (fun u => wt_le_exp_Kij hφ0 hφ2 β i j u (fun l hl => (h l hl).symm))
    (integrable_wt hφ hφ0 hφ2 β _ μ η) (integrable_wt hφ hφ0 hφ2 β _ μ η')
    (part_pos hφ hφ0 hφ2 β _ μ η) (part_pos hφ hφ0 hφ2 β _ μ η')
    (hint η η) (hint η η') (hint η' η')
    (fun u => hosc j _ _ fun l hl => by
      by_cases hli : l ∈ ({i} : Finset ILink)
      · rw [splice_mem hli, splice_mem hli]
      · rw [splice_not_mem hli, splice_not_mem hli]; exact h l hl)
    (fun u => hosc i _ _ fun l hl => by
      have hli : l ∉ ({i} : Finset ILink) := by simpa using hl
      rw [splice_not_mem hli, splice_not_mem hli])
  have e : infl β i j * v i = 2 * (Real.exp (2 * Kij β i j) - 1) * v i := rfl
  rw [e]
  exact key

/-- The oscillation vector after one single-link kernel at `i`. -/
def upd (β : ℝ) (i : ILink) (v : ILink → ℝ) (j : ILink) : ℝ :=
  if j = i then 0 else v j + infl β i j * v i

theorem upd_nonneg (β : ℝ) (i : ILink) {v : ILink → ℝ} (hv : ∀ l, 0 ≤ v l) (l : ILink) :
    0 ≤ upd β i v l := by
  unfold upd
  split_ifs
  · exact le_rfl
  · exact add_nonneg (hv l) (mul_nonneg (infl_nonneg β i l) (hv i))

/-- **`γ_{i}` sends the oscillation vector `v` to `upd β i v`.** -/
theorem linkOsc_spec_single {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] {f : IConf G → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ η, |f η| ≤ B) {v : ILink → ℝ} (hosc : LinkOsc f v)
    (i : ILink) : LinkOsc (spec φ β {i} μ f) (upd β i v) := by
  intro l η η' h
  unfold upd
  split_ifs with hli
  · rw [spec_congr_off φ β {i} μ f (fun l' hl' => h l' (by rw [hli]; simpa using hl')), sub_self,
      abs_zero]
  · exact spec_single_osc hφ hφ0 hφ2 β μ hf hB hosc i l h

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- `γ_{i}` keeps locality on any `U ⊇ nbr i`. -/
theorem isLocalOn_spec_single (φ : G → ℝ) (β : ℝ) (μ : Measure G) {U : Finset ILink}
    {f : IConf G → ℝ} (hf : IsLocalOn U f) (i : ILink) (hU : nbr i ⊆ U) :
    IsLocalOn U (spec φ β {i} μ f) := by
  intro η η' h
  have h1 : ∀ u : VConf G {i}, f (splice {i} u η) = f (splice {i} u η') := fun u =>
    hf _ _ fun l hl => by
      by_cases hli : l ∈ ({i} : Finset ILink)
      · rw [splice_mem hli, splice_mem hli]
      · rw [splice_not_mem hli, splice_not_mem hli]; exact h l hl
  have h2 : ∀ u : VConf G {i}, wt φ β {i} u η = wt φ β {i} u η' := fun u =>
    wt_congr_nbr φ β i u fun l hl => h l (hU hl)
  unfold spec num part
  simp only [h1, h2]

theorem spec_le_of_le {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ η, |f η| ≤ B) {ω : IConf G} {K : ℝ}
    (hK : ∀ u, f (splice Λ u ω) ≤ K) : spec φ β Λ μ f ω ≤ K := by
  have hZ := part_pos hφ hφ0 hφ2 β Λ μ ω
  unfold spec
  rw [div_le_iff₀ hZ]
  unfold num part
  rw [← integral_const_mul]
  exact integral_mono (integrable_num hφ hφ0 hφ2 β Λ μ hf hB ω)
    ((integrable_wt hφ hφ0 hφ2 β Λ μ ω).const_mul K)
    fun u => mul_le_mul_of_nonneg_right (hK u) (wt_pos φ β Λ u ω).le

theorem le_spec_of_le {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ η, |f η| ≤ B) {ω : IConf G} {K : ℝ}
    (hK : ∀ u, K ≤ f (splice Λ u ω)) : K ≤ spec φ β Λ μ f ω := by
  have hZ := part_pos hφ hφ0 hφ2 β Λ μ ω
  unfold spec
  rw [le_div_iff₀ hZ]
  unfold num part
  rw [← integral_const_mul]
  exact integral_mono ((integrable_wt hφ hφ0 hφ2 β Λ μ ω).const_mul K)
    (integrable_num hφ hφ0 hφ2 β Λ μ hf hB ω)
    fun u => mul_le_mul_of_nonneg_right (hK u) (wt_pos φ β Λ u ω).le

/-- **A kernel of a local function moves by at most its summed oscillation** between any two boundary
conditions. -/
theorem spec_abs_sub_le_sum {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (Λ : Finset ILink) (μ : Measure G) [IsProbabilityMeasure μ]
    {f : IConf G → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ η, |f η| ≤ B) {v : ILink → ℝ}
    (hosc : LinkOsc f v) {U : Finset ILink} (hloc : IsLocalOn U f) (ω ω' : IConf G) :
    |spec φ β Λ μ f ω - spec φ β Λ μ f ω'| ≤ ∑ l ∈ U, v l := by
  have hD : ∀ (ζ ζ' : IConf G) (u u' : VConf G Λ),
      f (splice Λ u ζ) ≤ f (splice Λ u' ζ') + ∑ l ∈ U, v l := fun ζ ζ' u u' => by
    have := abs_sub_le_sum_local hosc hloc (splice Λ u ζ) (splice Λ u' ζ')
    linarith [le_abs_self (f (splice Λ u ζ) - f (splice Λ u' ζ'))]
  have side : ∀ ζ ζ' : IConf G, spec φ β Λ μ f ζ ≤ spec φ β Λ μ f ζ' + ∑ l ∈ U, v l := by
    intro ζ ζ'
    have h1 : ∀ u' : VConf G Λ, spec φ β Λ μ f ζ - ∑ l ∈ U, v l ≤ f (splice Λ u' ζ') := by
      intro u'
      have := spec_le_of_le hφ hφ0 hφ2 β Λ μ hf hB (ω := ζ) (K := f (splice Λ u' ζ') + ∑ l ∈ U, v l)
        (fun u => hD ζ ζ' u u')
      linarith
    have := le_spec_of_le hφ hφ0 hφ2 β Λ μ hf hB (ω := ζ') h1
    linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [side ω ω']
  · linarith [side ω' ω]

end Spec

/-! ## 5. The weighted sweep -/

/-- The `θ^{d}`-weighted oscillation over `T`. -/
def wsum (θ : ℝ) (d : ILink → ℕ) (T : Finset ILink) (v : ILink → ℝ) : ℝ :=
  ∑ l ∈ T, θ ^ d l * v l

/-- The initial oscillation vector of an observable with `|X| ≤ 1` local on `A`. -/
def initOsc (A : Finset ILink) (l : ILink) : ℝ := if l ∈ A then 2 else 0

theorem initOsc_nonneg (A : Finset ILink) (l : ILink) : 0 ≤ initOsc A l := by
  unfold initOsc; split_ifs <;> norm_num

theorem linkOsc_init {G : Type} {X : IConf G → ℝ} {A : Finset ILink} (hX1 : ∀ η, |X η| ≤ 1)
    (hloc : IsLocalOn A X) : LinkOsc X (initOsc A) := by
  intro l η η' h
  unfold initOsc
  split_ifs with hl
  · have a1 := abs_le.mp (hX1 η)
    have a2 := abs_le.mp (hX1 η')
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · rw [hloc η η' fun l' hl' => h l' (fun he => hl (he ▸ hl')), sub_self, abs_zero]

theorem wsum_initOsc (θ : ℝ) (d : ILink → ℕ) {A U : Finset ILink} (hAU : A ⊆ U) :
    wsum θ d U (initOsc A) = 2 * ∑ l ∈ A, θ ^ d l := by
  unfold wsum
  rw [← Finset.sum_subset hAU (fun l _ hl => by rw [initOsc, if_neg hl, mul_zero]),
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l hl => by rw [initOsc, if_pos hl, mul_comm]

/-- **One update lowers the weighted oscillation.** For `i ∈ Δ ∩ T`, a `1`-Lipschitz depth and
`θ ∈ (0, 1]`: `θ · Σ_T ρ (upd v) ≤ θ · Σ_T ρ v − (θ − 64 c0) ρ_i v_i`. -/
theorem sum_upd_le (β θ : ℝ) (d : ILink → ℕ) (Δ T : Finset ILink) {i : ILink} (hiΔ : i ∈ Δ)
    (hiT : i ∈ T) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hd : ∀ i ∈ Δ, ∀ j ∈ nbr i, d i ≤ d j + 1)
    {v : ILink → ℝ} (hv : ∀ l, 0 ≤ v l) :
    θ * wsum θ d T (upd β i v)
      ≤ θ * wsum θ d T v - (θ - 64 * c0 β) * (θ ^ d i * v i) := by
  have hinfl : θ * ∑ l ∈ T, θ ^ d l * infl β i l ≤ 64 * c0 β * θ ^ d i := by
    have hs1 : ∑ l ∈ T, θ ^ d l * infl β i l ≤ ∑ l ∈ T ∪ nbr i, θ ^ d l * infl β i l :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun l _ _ => mul_nonneg (pow_nonneg hθ0.le _) (infl_nonneg β i l))
    have hs2 : ∑ l ∈ T ∪ nbr i, θ ^ d l * infl β i l = ∑ l ∈ nbr i, θ ^ d l * infl β i l :=
      (Finset.sum_subset Finset.subset_union_right
        (fun l _ hl => by rw [infl_eq_zero hl, mul_zero])).symm
    have hs3 : θ * ∑ l ∈ nbr i, θ ^ d l * infl β i l ≤ ∑ _l ∈ nbr i, θ ^ d i * c0 β := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have hp : θ * θ ^ d l ≤ θ ^ d i := by
        rw [← pow_succ']; exact pow_le_pow_of_le_one hθ0.le hθ1 (hd i hiΔ l hl)
      calc θ * (θ ^ d l * infl β i l) = (θ * θ ^ d l) * infl β i l := by ring
        _ ≤ θ ^ d i * c0 β :=
          mul_le_mul hp (infl_le β i l) (infl_nonneg β i l) (pow_nonneg hθ0.le _)
    have hs4 : ∑ _l ∈ nbr i, θ ^ d i * c0 β ≤ 64 * c0 β * θ ^ d i := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have : ((nbr i).card : ℝ) ≤ 64 := by exact_mod_cast card_nbr_le i
      nlinarith [mul_le_mul_of_nonneg_right this
        (mul_nonneg (pow_nonneg hθ0.le (d i)) (c0_nonneg β))]
    calc θ * ∑ l ∈ T, θ ^ d l * infl β i l ≤ θ * ∑ l ∈ nbr i, θ ^ d l * infl β i l := by
          rw [← hs2]; exact mul_le_mul_of_nonneg_left hs1 hθ0.le
      _ ≤ 64 * c0 β * θ ^ d i := hs3.trans hs4
  have hsT : θ ^ d i * upd β i v i + ∑ l ∈ T.erase i, θ ^ d l * upd β i v l
      = ∑ l ∈ T, θ ^ d l * upd β i v l :=
    Finset.add_sum_erase T (fun l => θ ^ d l * upd β i v l) hiT
  have hsV : θ ^ d i * v i + ∑ l ∈ T.erase i, θ ^ d l * v l = ∑ l ∈ T, θ ^ d l * v l :=
    Finset.add_sum_erase T (fun l => θ ^ d l * v l) hiT
  have hsI : θ ^ d i * infl β i i + ∑ l ∈ T.erase i, θ ^ d l * infl β i l
      = ∑ l ∈ T, θ ^ d l * infl β i l :=
    Finset.add_sum_erase T (fun l => θ ^ d l * infl β i l) hiT
  have hE : ∑ l ∈ T.erase i, θ ^ d l * upd β i v l
      = ∑ l ∈ T.erase i, θ ^ d l * v l + v i * ∑ l ∈ T.erase i, θ ^ d l * infl β i l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [upd, if_neg (Finset.ne_of_mem_erase hl)]; ring
  have hui : upd β i v i = 0 := if_pos rfl
  rw [hui, mul_zero, zero_add] at hsT
  have hIi : 0 ≤ θ ^ d i * infl β i i := mul_nonneg (pow_nonneg hθ0.le _) (infl_nonneg β i i)
  have hvi := hv i
  unfold wsum
  rw [← hsT, ← hsV, hE]
  have hsI' : v i * (θ * ∑ l ∈ T, θ ^ d l * infl β i l)
      = v i * θ * (θ ^ d i * infl β i i) + v i * θ * ∑ l ∈ T.erase i, θ ^ d l * infl β i l := by
    rw [← hsI]; ring
  nlinarith [mul_le_mul_of_nonneg_left hinfl hvi, mul_nonneg (mul_nonneg hvi hθ0.le) hIi]

/-- The contraction arithmetic of one greedy update. -/
theorem step_arith {θ S S' R A n r : ℝ} (hθ : 0 < θ) (hr0 : 0 ≤ r)
    (h1 : θ * S' ≤ θ * S - A * R) (hSR : S ≤ n * R) (hrA : r * (θ * n) = A) :
    S' ≤ (1 - r) * S := by
  have h2 : θ * r * S ≤ θ * r * (n * R) := mul_le_mul_of_nonneg_left hSR (mul_nonneg hθ.le hr0)
  have h3 : r * (θ * n) * R = A * R := by rw [hrA]
  have key : θ * S' ≤ θ * ((1 - r) * S) := by nlinarith
  exact le_of_mul_le_mul_left key hθ

/-- The hull: `Δ` and every link read by a plaquette through a link of `Δ`. -/
def hull (Δ : Finset ILink) : Finset ILink := Δ ∪ Δ.biUnion nbr

/-- The contraction rate of one greedy update. DERIVED: `64 = 16 · 4` the links read by the plaquettes
through one link (`card_nbr_le`), so `64 · c0 β` bounds the Dobrushin row sum. -/
def qrate (β θ : ℝ) (Δ : Finset ILink) : ℝ := 1 - (θ - 64 * c0 β) / (θ * Δ.card)

theorem qrate_mem {β θ : ℝ} {Δ : Finset ILink} (hΔ : Δ.Nonempty) (hθ0 : 0 < θ)
    (hβ : 64 * c0 β < θ) : 0 ≤ qrate β θ Δ ∧ qrate β θ Δ < 1 := by
  have hn1 : (1 : ℝ) ≤ Δ.card := Nat.one_le_cast.mpr (Finset.card_pos.mpr hΔ)
  have hden : 0 < θ * Δ.card := mul_pos hθ0 (by linarith)
  have hr1 : (θ - 64 * c0 β) / (θ * Δ.card) ≤ 1 := by
    rw [div_le_one hden]; nlinarith [c0_nonneg β]
  have hr0 : 0 < (θ - 64 * c0 β) / (θ * Δ.card) := div_pos (by linarith) hden
  unfold qrate
  constructor <;> linarith

section Main

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **`KernelNear` at strong coupling, any density in `[0, 2]`.** For `|X| ≤ 1` local on `A ⊆ Δ`, a depth
`d` vanishing off `Δ` and `1`-Lipschitz along `nbr` inside `Δ`, and `θ ∈ (0, 1]` above the row sum
`64 · c0 β`: the box kernel moves by at most `2 Σ_{l ∈ A} θ^{d l}` between any two boundary conditions. -/
theorem kernel_near_strong {φ : G → ℝ} (hφ : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (μ : Measure G) [IsProbabilityMeasure μ] (Δ A : Finset ILink)
    (hAΔ : A ⊆ Δ) {X : IConf G → ℝ} (hX : Measurable X) (hX1 : ∀ η, |X η| ≤ 1)
    (hXloc : IsLocalOn A X) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 64 * c0 β < θ)
    (d : ILink → ℕ) (hdout : ∀ l, l ∉ Δ → d l = 0) (hd : ∀ i ∈ Δ, ∀ j ∈ nbr i, d i ≤ d j + 1)
    (ω ω' : IConf G) :
    |spec φ β Δ μ X ω - spec φ β Δ μ X ω'| ≤ 2 * ∑ l ∈ A, θ ^ d l := by
  have hΔU : Δ ⊆ hull Δ := Finset.subset_union_left
  have hnU : ∀ i ∈ Δ, nbr i ⊆ hull Δ := fun i hi =>
    (Finset.subset_biUnion_of_mem nbr hi).trans Finset.subset_union_right
  have hAU : A ⊆ hull Δ := hAΔ.trans hΔU
  have hinv : ∀ n : ℕ, ∃ (g : IConf G → ℝ) (v : ILink → ℝ), Measurable g ∧ (∀ η, |g η| ≤ 1) ∧
      IsLocalOn (hull Δ) g ∧ LinkOsc g v ∧ (∀ l, 0 ≤ v l) ∧
      (∀ ζ, spec φ β Δ μ g ζ = spec φ β Δ μ X ζ) ∧
      wsum θ d Δ v ≤ qrate β θ Δ ^ n * wsum θ d Δ (initOsc A) ∧
      wsum θ d (hull Δ) v ≤ wsum θ d (hull Δ) (initOsc A) := by
    intro n
    induction n with
    | zero =>
      exact ⟨X, initOsc A, hX, hX1, fun η η' h => hXloc η η' fun l hl => h l (hAU hl),
        linkOsc_init hX1 hXloc, initOsc_nonneg A, fun _ => rfl, le_of_eq (by ring), le_rfl⟩
    | succ n ih =>
      obtain ⟨g, v, hg, hg1, hgl, hgo, hv, hgs, hΨ, hΦ⟩ := ih
      rcases Δ.eq_empty_or_nonempty with hΔ | hΔ
      · refine ⟨g, v, hg, hg1, hgl, hgo, hv, hgs, ?_, hΦ⟩
        simp [wsum, hΔ]
      · obtain ⟨i, hiΔ, hmax⟩ := Finset.exists_max_image Δ (fun l => θ ^ d l * v l) hΔ
        have hR0 : 0 ≤ θ ^ d i * v i := mul_nonneg (pow_nonneg hθ0.le _) (hv i)
        refine ⟨spec φ β {i} μ g, upd β i v, measurable_spec_right hφ β {i} μ hg,
          fun η => abs_spec_le hφ hφ0 hφ2 β {i} μ hg hg1 η,
          isLocalOn_spec_single φ β μ hgl i (hnU i hiΔ),
          linkOsc_spec_single hφ hφ0 hφ2 β μ hg hg1 hgo i, upd_nonneg β i hv,
          fun ζ => (dlr_consistent hφ hφ0 hφ2 β μ {i} Δ (Finset.singleton_subset_iff.mpr hiΔ) g
            hg hg1 ζ).trans (hgs ζ), ?_, ?_⟩
        · have h1 := sum_upd_le β θ d Δ Δ hiΔ hiΔ hθ0 hθ1 hd hv
          have hn1 : (1 : ℝ) ≤ Δ.card := Nat.one_le_cast.mpr (Finset.card_pos.mpr hΔ)
          have hne : θ * (Δ.card : ℝ) ≠ 0 := (mul_pos hθ0 (by linarith)).ne'
          have hΨR : wsum θ d Δ v ≤ Δ.card * (θ ^ d i * v i) := by
            unfold wsum
            calc ∑ l ∈ Δ, θ ^ d l * v l ≤ ∑ _l ∈ Δ, θ ^ d i * v i := Finset.sum_le_sum hmax
              _ = Δ.card * (θ ^ d i * v i) := by rw [Finset.sum_const, nsmul_eq_mul]
          obtain ⟨r, hr⟩ : ∃ r, r = (θ - 64 * c0 β) / (θ * Δ.card) := ⟨_, rfl⟩
          have hrA : r * (θ * Δ.card) = θ - 64 * c0 β := by rw [hr]; field_simp
          have hr0 : 0 ≤ r := by
            rw [hr]; exact div_nonneg (by linarith) (mul_nonneg hθ0.le (by linarith))
          have hq : qrate β θ Δ = 1 - r := by rw [qrate, hr]
          have hstep := step_arith hθ0 hr0 h1 hΨR hrA
          rw [← hq] at hstep
          have hq0 := (qrate_mem hΔ hθ0 hβ).1
          calc wsum θ d Δ (upd β i v) ≤ qrate β θ Δ * wsum θ d Δ v := hstep
            _ ≤ qrate β θ Δ * (qrate β θ Δ ^ n * wsum θ d Δ (initOsc A)) :=
                mul_le_mul_of_nonneg_left hΨ hq0
            _ = qrate β θ Δ ^ (n + 1) * wsum θ d Δ (initOsc A) := by ring
        · have h1 := sum_upd_le β θ d Δ (hull Δ) hiΔ (hΔU hiΔ) hθ0 hθ1 hd hv
          have h2 : wsum θ d (hull Δ) (upd β i v) ≤ wsum θ d (hull Δ) v := by
            have : 0 ≤ (θ - 64 * c0 β) * (θ ^ d i * v i) := mul_nonneg (by linarith) hR0
            have key : θ * wsum θ d (hull Δ) (upd β i v) ≤ θ * wsum θ d (hull Δ) v := by linarith
            exact le_of_mul_le_mul_left key hθ0
          exact h2.trans hΦ
  have hfin : ∀ n : ℕ, |spec φ β Δ μ X ω - spec φ β Δ μ X ω'|
      ≤ qrate β θ Δ ^ n * wsum θ d Δ (initOsc A) / θ ^ (Δ.sup d) + 2 * ∑ l ∈ A, θ ^ d l := by
    intro n
    obtain ⟨g, v, hg, hg1, hgl, hgo, hv, hgs, hΨ, hΦ⟩ := hinv n
    rw [← hgs ω, ← hgs ω']
    have h1 := spec_abs_sub_le_sum hφ hφ0 hφ2 β Δ μ hg hg1 hgo hgl ω ω'
    have hsplit : ∑ l ∈ hull Δ, v l = ∑ l ∈ hull Δ \ Δ, v l + ∑ l ∈ Δ, v l :=
      (Finset.sum_sdiff hΔU).symm
    have hout : ∑ l ∈ hull Δ \ Δ, v l ≤ 2 * ∑ l ∈ A, θ ^ d l := by
      have e : ∑ l ∈ hull Δ \ Δ, v l = ∑ l ∈ hull Δ \ Δ, θ ^ d l * v l :=
        Finset.sum_congr rfl fun l hl => by
          rw [hdout l (Finset.mem_sdiff.mp hl).2, pow_zero, one_mul]
      have hΦs : wsum θ d (hull Δ) v
          = ∑ l ∈ hull Δ \ Δ, θ ^ d l * v l + ∑ l ∈ Δ, θ ^ d l * v l :=
        (Finset.sum_sdiff hΔU).symm
      have hΔ0 : 0 ≤ ∑ l ∈ Δ, θ ^ d l * v l :=
        Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hθ0.le _) (hv l)
      rw [e, ← wsum_initOsc θ d hAU]
      linarith
    have hin : ∑ l ∈ Δ, v l ≤ qrate β θ Δ ^ n * wsum θ d Δ (initOsc A) / θ ^ (Δ.sup d) := by
      rw [le_div_iff₀ (pow_pos hθ0 _), Finset.sum_mul]
      refine le_trans ?_ hΨ
      exact Finset.sum_le_sum fun l hl => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hθ0.le hθ1 (Finset.le_sup hl)) (hv l)
    linarith
  rcases Δ.eq_empty_or_nonempty with hΔ | hΔ
  · have h := hfin 0
    have h0 : wsum θ d Δ (initOsc A) = 0 := by simp [wsum, hΔ]
    rw [h0, mul_zero, zero_div, zero_add] at h
    exact h
  · obtain ⟨hq0, hq1⟩ := qrate_mem hΔ hθ0 hβ
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (wsum θ d Δ (initOsc A))).div_const (θ ^ Δ.sup d)).add_const (2 * ∑ l ∈ A, θ ^ d l)
    simp only [zero_mul, zero_div, zero_add] at ht
    exact ge_of_tendsto' ht hfin

end Main

/-! ## 6. The Wilson specification -/

section Wilson

open MassGap.WilsonAction MassGap.CompactGauge

variable {N : ℕ}

/-- **`KernelNear` at strong coupling on the Wilson specification.** -/
theorem kernelNear_strong (hN : N ≠ 0) (β : ℝ) (Δ A : Finset ILink) (hAΔ : A ⊆ Δ)
    (X : C(IConf (MassGap.SUN.SU N), ℝ)) (hX1 : ∀ ω, |X ω| ≤ 1) (hXloc : IsLocalOn A ⇑X)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 64 * c0 β < θ) (d : ILink → ℕ)
    (hdout : ∀ l, l ∉ Δ → d l = 0) (hd : ∀ i ∈ Δ, ∀ j ∈ nbr i, d i ≤ d j + 1) :
    BoxFocusTest.KernelNear hN β Δ X (2 * ∑ l ∈ A, θ ^ d l) := by
  refine ⟨MassGap.PeriodicStateDLR.wspec hN β Δ X (fun _ => 1), fun ω => ?_⟩
  rw [MassGap.PeriodicStateDLR.wspec_apply, MassGap.PeriodicStateDLR.wspec_apply]
  exact kernel_near_strong measurable_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β (probHaar (MassGap.SUN.SU N)) Δ A hAΔ X.continuous.measurable hX1
    hXloc hθ0 hθ1 hβ d hdout hd ω _

/-- `|β| ≤ 2^{-16}` puts the row sum `64 · c0 β` at most `1/4`. -/
theorem row_le_quarter {β : ℝ} (hβ : |β| ≤ 1 / 65536) : 64 * c0 β ≤ 1 / 4 := by
  unfold c0
  set x := 64 * |β| with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 1024 := by rw [hx]; linarith
  have hlow := Real.add_one_le_exp (-x)
  have hm : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hE1 : 1 ≤ Real.exp x := Real.one_le_exp hx0
  have hEx : Real.exp x * (1 - x) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ Real.exp x)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hx1 (by linarith : 0 ≤ Real.exp x)]

/-- **Explicit strong-coupling `KernelNear`.** At `|β| ≤ β₀ = 2^{-16}`, with depth `d` as above and every
link of `X`'s support at depth at least `L`: `KernelNear Δ X (2 |A| 2^{−L})`. -/
theorem kernelNear_strong_explicit (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536)
    (Δ A : Finset ILink) (hAΔ : A ⊆ Δ) (X : C(IConf (MassGap.SUN.SU N), ℝ))
    (hX1 : ∀ ω, |X ω| ≤ 1) (hXloc : IsLocalOn A ⇑X) (d : ILink → ℕ)
    (hdout : ∀ l, l ∉ Δ → d l = 0) (hd : ∀ i ∈ Δ, ∀ j ∈ nbr i, d i ≤ d j + 1) (L : ℕ)
    (hL : ∀ l ∈ A, L ≤ d l) :
    BoxFocusTest.KernelNear hN β Δ X (2 * A.card * (1 / 2) ^ L) := by
  obtain ⟨c, hc⟩ := kernelNear_strong hN β Δ A hAΔ X hX1 hXloc (θ := 1 / 2) (by norm_num)
    (by norm_num) (by linarith [row_le_quarter hβ]) d hdout hd
  have hs : ∑ l ∈ A, (1 / 2 : ℝ) ^ d l ≤ A.card * (1 / 2) ^ L := by
    calc ∑ l ∈ A, (1 / 2 : ℝ) ^ d l ≤ ∑ _l ∈ A, (1 / 2 : ℝ) ^ L :=
          Finset.sum_le_sum fun l hl => pow_le_pow_of_le_one (by norm_num) (by norm_num) (hL l hl)
      _ = A.card * (1 / 2) ^ L := by rw [Finset.sum_const, nsmul_eq_mul]
  exact ⟨c, fun ω => (hc ω).trans (by linarith)⟩

end Wilson

end MassGap.StrongKernelNear

#print axioms MassGap.StrongKernelNear.avg_sub_le
#print axioms MassGap.StrongKernelNear.spec_single_osc
#print axioms MassGap.StrongKernelNear.linkOsc_spec_single
#print axioms MassGap.StrongKernelNear.spec_abs_sub_le_sum
#print axioms MassGap.StrongKernelNear.sum_upd_le
#print axioms MassGap.StrongKernelNear.kernel_near_strong
#print axioms MassGap.StrongKernelNear.kernelNear_strong
#print axioms MassGap.StrongKernelNear.kernelNear_strong_explicit
