import Mathlib
import MassGap.BoxDobrushinCoupling

noncomputable section

/-!
# MassGap.BoxDobrushinSpatial — the spatial form of Dobrushin decay on the box

`BoxDobrushinCoupling` bounds the total oscillation left after a heat-bath sweep. This module keeps
the oscillation vector and turns it into a covariance bound that decays with the influence distance.

1. **The vector form** (`oscRun`, `osc_run`). Along any list of heat baths, the oscillation vector
   evolves by `oscStep`: the heat bath at `l` sets the entry at `l` to `0` and adds `C(l, k) v_l` at
   every `k`.
2. **The covariance telescope** (`cov_step`, `oscCost`, `cov_run`). One heat bath at `l` changes
   `⟨f g⟩` into `⟨(P_l f) g⟩` at cost `v_f(l) v_g(l)`: the difference is the conditional covariance
   `⟨(f − P_l f)(g − P_l g)⟩` (detailed balance and `P_l P_l = P_l`). Along a list the costs add up to
   `oscCost`, the oscillation of `f` removed at each step weighted by the oscillation of `g` there.
3. **The weighted mass** (`mass_step`, `cost_le`). With a level `ψ` that one influence step changes by
   at most one and `α < θ ≤ 1`, the mass `Σ_k θ^{ψ k} v_k` drops at every heat bath by at least
   `(1 − α/θ)` times the weighted entry it removes. Hence `(θ − α) · oscCost ≤ V_g θ Σ_k θ^{ψ k} v_f(k)`
   whenever `v_g ≤ V_g θ^ψ`, uniformly in the length of the list.
4. **The covariance bound** (`cov_le_weighted`). Repeated full sweeps converge to the Gibbs state
   (`BoxDobrushinCoupling.sweep_to_gibbs`), so
   `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ V_g θ/(θ − α) · Σ_k θ^{ψ k} v_f(k)`.
5. **Spatial decay** (`reach`, `level`, `cov_spatial`, `box_cov_spatial`, `box_cov_spatial_79`). For
   `g` reading only links in `B` and `f` reading only links outside the `d`-step influence
   neighbourhood `reach C B d`, the covariance is `≤ V_g θ/(θ − α) · θ^{d+1} Σ v_f`. For the box weight
   at Lean `β ≤ 1/40` and local norm `≤ 1/16` (row sum `α = 39/40`) at `θ = 79/80` the prefactor is
   `79`: decay rate `log(80/79)` per influence step; any `θ ∈ (39/40, 1]` is allowed, so every rate
   below `log(40/39)` is reached.

## Scope

The bound lives on the finite periodic box, against its Gibbs state `wExpect (wtV β P)`. The
`hrec`/`hread` inputs of `BoxDobrushin.dlr_eq_of_influence` concern a box inside a larger lattice
with two boundary conditions, and `ObserverEnergyGap.LatClusterRateOn` concerns `latSF` of the
flowed observable; neither identification is made here.
-/

namespace MassGap.BoxDobrushinSpatial

open MeasureTheory Filter Topology
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (exists_abs_le integrable_of_abs_le)
open MassGap.WeightedHeatBath (wAvg wAvg_update wAvg_of_readsNot continuous_wAvg)
open MassGap.WeightedTorus (wExpect expect_wAvg_mul integral_pos_weight)
open MassGap.LocalPotential (LocalPot wtV)
open MassGap.BoxDobrushinCoupling (OscLe Infl oscStep osc_step sweep continuous_sweep wAvg_sub_le
  sweep_to_gibbs boxInfl infl_wtV boxInfl_nonneg rowSum_box wtV_pos continuous_wtV)

variable {N : ℕ}

/-! ## 1. Expectation algebra -/

section Expect

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- A continuous function times a continuous weight is integrable against the product Haar measure.

DERIVED: no numeral. -/
theorem integrable_mul_weight {Φ : (Lk → SU N) → ℝ} (hcont : Continuous Φ)
    {F : (Lk → SU N) → ℝ} (hF : Continuous F) :
    Integrable (fun W => F W * Φ W) (Measure.pi fun _ : Lk => probHaar (SU N)) := by
  obtain ⟨C, hC⟩ := exists_abs_le (hF.mul hcont)
  exact integrable_of_abs_le _ (hF.mul hcont).measurable hC

#print axioms integrable_mul_weight

/-- `wExpect` is additive on continuous observables.

DERIVED: no numeral. -/
theorem wExpect_sub {Φ : (Lk → SU N) → ℝ} (hcont : Continuous Φ) {F G : (Lk → SU N) → ℝ}
    (hF : Continuous F) (hG : Continuous G) :
    wExpect Φ (fun W => F W - G W) = wExpect Φ F - wExpect Φ G := by
  unfold wExpect
  rw [← sub_div, ← integral_sub (integrable_mul_weight hcont hF) (integrable_mul_weight hcont hG)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show (F W - G W) * Φ W = F W * Φ W - G W * Φ W
  ring

#print axioms wExpect_sub

/-- `wExpect` is homogeneous.

DERIVED: no numeral. -/
theorem wExpect_const_mul (Φ : (Lk → SU N) → ℝ) (c : ℝ) (F : (Lk → SU N) → ℝ) :
    wExpect Φ (fun W => c * F W) = c * wExpect Φ F := by
  unfold wExpect
  have e : ∀ W, c * F W * Φ W = c * (F W * Φ W) := fun W => by ring
  simp only [e, integral_const_mul]
  ring

#print axioms wExpect_const_mul

/-- **A bounded observable has a bounded expectation**: `|F| ≤ c` gives `|wExpect Φ F| ≤ c`.

DERIVED: no numeral. -/
theorem abs_wExpect_le {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {F : (Lk → SU N) → ℝ} (hF : Continuous F) {c : ℝ} (hc : ∀ W, |F W| ≤ c) :
    |wExpect Φ F| ≤ c := by
  have hZ := integral_pos_weight hpos hcont
  have iΦ : Integrable Φ (Measure.pi fun _ : Lk => probHaar (SU N)) := by
    obtain ⟨C, hC⟩ := exists_abs_le hcont
    exact integrable_of_abs_le _ hcont.measurable hC
  have iF := integrable_mul_weight hcont hF
  unfold wExpect
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ, ← integral_const_mul, abs_le]
  constructor
  · rw [← integral_neg]
    refine integral_mono (iΦ.const_mul c).neg iF fun W => ?_
    have h1 := (abs_le.mp (hc W)).1
    have h2 := hpos W
    show -(c * Φ W) ≤ F W * Φ W
    nlinarith
  · refine integral_mono iF (iΦ.const_mul c) fun W => ?_
    have h1 := (abs_le.mp (hc W)).2
    have h2 := hpos W
    show F W * Φ W ≤ c * Φ W
    nlinarith

#print axioms abs_wExpect_le

end Expect

/-! ## 2. One heat bath: the conditional covariance -/

section Step

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **A heat bath moves an observable by at most its oscillation at that link**:
`|f W − P_l f W| ≤ v_l`.

DERIVED: no numeral. -/
theorem abs_sub_wAvg_le {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l : Lk) {f : (Lk → SU N) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v)
    (W : Lk → SU N) : |f W - wAvg Φ l f W| ≤ v l := by
  have h := wAvg_sub_le hpos hcont l hf
    (show Continuous fun _ : Lk → SU N => f W from continuous_const) W (c := v l)
    (fun g => hv W l g)
  rw [wAvg_of_readsNot hpos hcont l (f := fun _ : Lk → SU N => f W) (fun _ _ => rfl) W] at h
  rw [abs_sub_comm]
  exact h

#print axioms abs_sub_wAvg_le

/-- **One heat bath in the covariance**: replacing `f` by `P_l f` in `⟨f g⟩` costs at most
`v_f(l) v_g(l)`. The difference is `⟨(f − P_l f)(g − P_l g)⟩`, since `⟨P_l f · g⟩ = ⟨f · P_l g⟩`
(detailed balance) and `⟨P_l f · g⟩ = ⟨P_l f · P_l g⟩` (detailed balance at `P_l f`, which the heat
bath fixes).

DERIVED: no numeral. -/
theorem cov_step {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : OscLe f vf) (hvg : OscLe g vg) :
    |wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => wAvg Φ l f W * g W)| ≤ vf l * vg l := by
  have hPfc : Continuous (wAvg Φ l f) := continuous_wAvg hpos hcont l hf
  have hPgc : Continuous (wAvg Φ l g) := continuous_wAvg hpos hcont l hg
  have db1 : wExpect Φ (fun W => wAvg Φ l f W * g W) = wExpect Φ (fun W => f W * wAvg Φ l g W) :=
    expect_wAvg_mul hpos hcont l hf hg
  have hPP : wAvg Φ l (wAvg Φ l f) = wAvg Φ l f := funext fun W =>
    wAvg_of_readsNot hpos hcont l (fun V h => wAvg_update Φ l f V h) W
  have db2 : wExpect Φ (fun W => wAvg Φ l f W * g W)
      = wExpect Φ (fun W => wAvg Φ l f W * wAvg Φ l g W) := by
    have h := expect_wAvg_mul hpos hcont l hPfc hg
    rw [hPP] at h
    exact h
  have hE : wExpect Φ (fun W => (f W - wAvg Φ l f W) * (g W - wAvg Φ l g W))
      = (wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => wAvg Φ l f W * g W))
        - (wExpect Φ (fun W => f W * wAvg Φ l g W)
          - wExpect Φ (fun W => wAvg Φ l f W * wAvg Φ l g W)) := by
    have e : (fun W => (f W - wAvg Φ l f W) * (g W - wAvg Φ l g W)) = fun W =>
        (f W * g W - wAvg Φ l f W * g W) - (f W * wAvg Φ l g W - wAvg Φ l f W * wAvg Φ l g W) :=
      funext fun W => by ring
    rw [e, wExpect_sub hcont (F := fun W => f W * g W - wAvg Φ l f W * g W)
        (G := fun W => f W * wAvg Φ l g W - wAvg Φ l f W * wAvg Φ l g W)
        ((hf.mul hg).sub (hPfc.mul hg)) ((hf.mul hPgc).sub (hPfc.mul hPgc)),
      wExpect_sub hcont (F := fun W => f W * g W) (G := fun W => wAvg Φ l f W * g W)
        (hf.mul hg) (hPfc.mul hg),
      wExpect_sub hcont (F := fun W => f W * wAvg Φ l g W)
        (G := fun W => wAvg Φ l f W * wAvg Φ l g W) (hf.mul hPgc) (hPfc.mul hPgc)]
  have hbound : ∀ W, |(f W - wAvg Φ l f W) * (g W - wAvg Φ l g W)| ≤ vf l * vg l := fun W => by
    rw [abs_mul]
    exact mul_le_mul (abs_sub_wAvg_le hpos hcont l hf hvf W) (abs_sub_wAvg_le hpos hcont l hg hvg W)
      (abs_nonneg _) (hvf.nonneg l)
  have hb := abs_wExpect_le hpos hcont
    (F := fun W => (f W - wAvg Φ l f W) * (g W - wAvg Φ l g W)) ((hf.sub hPfc).mul (hg.sub hPgc))
    hbound
  have hd : wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => wAvg Φ l f W * g W)
      = wExpect Φ (fun W => (f W - wAvg Φ l f W) * (g W - wAvg Φ l g W)) := by
    linarith [hE, db1, db2]
  rw [hd]
  exact hb

#print axioms cov_step

end Step

/-! ## 3. Runs of heat baths: the vector form and the covariance telescope -/

section Run

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The oscillation vector along a list of heat baths**: `oscStep` at each link in order. -/
def oscRun (C : Lk → Lk → ℝ) : List Lk → (Lk → ℝ) → (Lk → ℝ)
  | [], v => v
  | l :: L, v => oscRun C L (oscStep C l v)

/-- **The covariance cost of a run**: at each heat bath `l`, the oscillation of `f` removed there,
`v_l`, times the oscillation `w_l` of the other observable.

DERIVED: `0` the cost of the empty run. -/
def oscCost (C : Lk → Lk → ℝ) (w : Lk → ℝ) : List Lk → (Lk → ℝ) → ℝ
  | [], _ => 0
  | l :: L, v => v l * w l + oscCost C w L (oscStep C l v)

/-- **The vector form of Dobrushin's comparison**: along any list of heat baths, `oscRun C L v` bounds
the single-link oscillations of the swept observable (`osc_step` at each step).

DERIVED: no numeral. -/
theorem osc_run {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      OscLe (sweep Φ L f) (oscRun C L v)
  | [], _, _, _, hv => hv
  | l :: L, _, hf, _, hv =>
      osc_run hpos hcont hC L (continuous_wAvg hpos hcont l hf) (osc_step hpos hcont hC hf hv l)

#print axioms osc_run

/-- **The covariance telescope**: along any list `L` of heat baths,
`|⟨f g⟩ − ⟨(sweep L f) g⟩| ≤ oscCost C v_g L v_f` (`cov_step` at each step, `osc_step` for the
vector).

DERIVED: `0` the cost of the empty run. -/
theorem cov_run {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) {g : (Lk → SU N) → ℝ} (hg : Continuous g) {vg : Lk → ℝ}
    (hvg : OscLe g vg) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      |wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => sweep Φ L f W * g W)|
        ≤ oscCost C vg L v
  | [], f, _, v, _ => by
      show |wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => f W * g W)| ≤ 0
      simp
  | l :: L, f, hf, v, hv => by
      have h1 := cov_step hpos hcont l hf hg hv hvg
      have h2 := cov_run hpos hcont hC hg hvg L (continuous_wAvg hpos hcont l hf)
        (osc_step hpos hcont hC hf hv l)
      show |wExpect Φ (fun W => f W * g W)
          - wExpect Φ (fun W => sweep Φ L (wAvg Φ l f) W * g W)|
        ≤ v l * vg l + oscCost C vg L (oscStep C l v)
      calc |wExpect Φ (fun W => f W * g W)
            - wExpect Φ (fun W => sweep Φ L (wAvg Φ l f) W * g W)|
          ≤ |wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => wAvg Φ l f W * g W)|
            + |wExpect Φ (fun W => wAvg Φ l f W * g W)
              - wExpect Φ (fun W => sweep Φ L (wAvg Φ l f) W * g W)| := abs_sub_le _ _ _
        _ ≤ v l * vg l + oscCost C vg L (oscStep C l v) := add_le_add h1 h2

#print axioms cov_run

/-- A sweep along a concatenation is the composite sweep.

DERIVED: no numeral. -/
theorem sweep_append (Φ : (Lk → SU N) → ℝ) :
    ∀ (L1 L2 : List Lk) (f : (Lk → SU N) → ℝ), sweep Φ (L1 ++ L2) f = sweep Φ L2 (sweep Φ L1 f)
  | [], _, _ => rfl
  | l :: L1, L2, f => sweep_append Φ L1 L2 (wAvg Φ l f)

#print axioms sweep_append

/-- `n` copies of a list, concatenated.

DERIVED: `0`, `1` the recursion on the copy count. -/
def rep (L : List Lk) : ℕ → List Lk
  | 0 => []
  | n + 1 => L ++ rep L n

/-- `n` iterated sweeps along `L` are one sweep along `rep L n`.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem sweep_rep (Φ : (Lk → SU N) → ℝ) (L : List Lk) :
    ∀ (n : ℕ) (f : (Lk → SU N) → ℝ), (sweep Φ L)^[n] f = sweep Φ (rep L n) f
  | 0, _ => rfl
  | n + 1, f => by
      show (sweep Φ L)^[n + 1] f = sweep Φ (L ++ rep L n) f
      rw [Function.iterate_succ_apply, sweep_rep Φ L n, sweep_append]

#print axioms sweep_rep

end Run

/-! ## 4. The weighted mass -/

section Mass

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- `oscStep` keeps a vector non-negative when `C ≥ 0`.

DERIVED: `0` the sign. -/
theorem oscStep_nonneg {C : Lk → Lk → ℝ} (hC0 : ∀ l k, 0 ≤ C l k) {v : Lk → ℝ}
    (hv : ∀ k, 0 ≤ v k) (l : Lk) : ∀ k, 0 ≤ oscStep C l v k := by
  intro k
  by_cases hk : k = l
  · simp only [oscStep, hk, ↓reduceIte, le_refl]
  · simp only [oscStep, hk, ↓reduceIte]
    exact add_nonneg (hv k) (mul_nonneg (hC0 l k) (hv l))

#print axioms oscStep_nonneg

/-- **The weighted mass drops at every heat bath.** Let `C ≥ 0` have row sums `≤ α`, `0 ≤ θ ≤ 1`,
and `ψ` a level with `C l k ≠ 0 → ψ l ≤ ψ k + 1`. For `v ≥ 0`, the heat bath at `l` gives
`θ M(oscStep C l v) ≤ θ M(v) − (θ − α) θ^{ψ l} v_l` with `M(v) = Σ_k θ^{ψ k} v_k`.

DERIVED: `0` the sign; `1` the bound on `θ` and the level range of one influence step. -/
theorem mass_step {C : Lk → Lk → ℝ} (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {v : Lk → ℝ} (hv : ∀ k, 0 ≤ v k) (l : Lk) :
    θ * ∑ k, θ ^ ψ k * oscStep C l v k
      ≤ θ * ∑ k, θ ^ ψ k * v k - (θ - α) * (θ ^ ψ l * v l) := by
  have hpt : ∀ k, θ ^ ψ k * oscStep C l v k
      ≤ θ ^ ψ k * v k + θ ^ ψ k * C l k * v l - (if k = l then θ ^ ψ l * v l else 0) := by
    intro k
    by_cases hk : k = l
    · rw [hk]
      simp only [oscStep, ↓reduceIte, mul_zero]
      have := mul_nonneg (mul_nonneg (pow_nonneg hθ0 (ψ l)) (hC0 l l)) (hv l)
      linarith
    · simp only [oscStep, hk, ↓reduceIte]
      exact le_of_eq (by ring)
  have hsum : ∑ k, θ ^ ψ k * oscStep C l v k
      ≤ ∑ k, θ ^ ψ k * v k + ∑ k, θ ^ ψ k * C l k * v l - θ ^ ψ l * v l := by
    have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt k
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ l (fun _ => θ ^ ψ l * v l), if_pos (Finset.mem_univ l)] at h
    exact h
  have hpt2 : ∀ k, θ * (θ ^ ψ k * C l k * v l) ≤ C l k * (θ ^ ψ l * v l) := by
    intro k
    by_cases hc : C l k = 0
    · rw [hc]; simp
    · have hp : θ ^ (ψ k + 1) ≤ θ ^ ψ l := pow_le_pow_of_le_one hθ0 hθ1 (hloc l k hc)
      rw [pow_succ] at hp
      have h := mul_le_mul_of_nonneg_right hp (mul_nonneg (hC0 l k) (hv l))
      calc θ * (θ ^ ψ k * C l k * v l) = θ ^ ψ k * θ * (C l k * v l) := by ring
        _ ≤ θ ^ ψ l * (C l k * v l) := h
        _ = C l k * (θ ^ ψ l * v l) := by ring
  have hs2 : θ * ∑ k, θ ^ ψ k * C l k * v l ≤ α * (θ ^ ψ l * v l) := by
    rw [Finset.mul_sum]
    calc ∑ k, θ * (θ ^ ψ k * C l k * v l) ≤ ∑ k, C l k * (θ ^ ψ l * v l) :=
          Finset.sum_le_sum fun k _ => hpt2 k
      _ = (∑ k, C l k) * (θ ^ ψ l * v l) := by rw [Finset.sum_mul]
      _ ≤ α * (θ ^ ψ l * v l) :=
          mul_le_mul_of_nonneg_right (hrow l) (mul_nonneg (pow_nonneg hθ0 _) (hv l))
  have h3 := mul_le_mul_of_nonneg_left hsum hθ0
  linarith

#print axioms mass_step

/-- **The cost of every run is bounded by the initial weighted mass**: if `v_g ≤ V_g θ^ψ`, then
`(θ − α) · oscCost C v_g L v ≤ V_g θ Σ_k θ^{ψ k} v_k` for every list `L` (`mass_step`).

DERIVED: `0` the sign; `1` the bound on `θ` and the level range. -/
theorem cost_le {C : Lk → Lk → ℝ} (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hαθ : α ≤ θ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {w : Lk → ℝ} {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hw : ∀ k, w k ≤ Vg * θ ^ ψ k) :
    ∀ (L : List Lk) (v : Lk → ℝ), (∀ k, 0 ≤ v k) →
      (θ - α) * oscCost C w L v ≤ Vg * (θ * ∑ k, θ ^ ψ k * v k)
  | [], v, hv => by
      simp only [oscCost, mul_zero]
      exact mul_nonneg hVg (mul_nonneg hθ0
        (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hθ0 _) (hv k)))
  | l :: L, v, hv => by
      have ih := cost_le hC0 hrow hαθ hθ0 hθ1 ψ hloc hVg hw L (oscStep C l v)
        (oscStep_nonneg hC0 hv l)
      have hm := mass_step hC0 hrow hθ0 hθ1 ψ hloc hv l
      have hθα : 0 ≤ θ - α := by linarith
      have h0 := mul_le_mul_of_nonneg_left (hw l) (hv l)
      have h1 := mul_le_mul_of_nonneg_left h0 hθα
      have h2 := mul_le_mul_of_nonneg_left hm hVg
      show (θ - α) * (v l * w l + oscCost C w L (oscStep C l v)) ≤ _
      linarith

#print axioms cost_le

end Mass

/-! ## 5. The covariance bound -/

section Cov

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **Dobrushin's covariance bound, weighted form.** For a positive continuous weight with influence
matrix `C ≥ 0` of row sums `≤ α`, any `α < θ ≤ 1`, any level `ψ` that one influence step changes by
at most one, continuous `f, g` with oscillation bounds `v_f, v_g` and `v_g ≤ V_g θ^ψ`:
`|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ V_g θ/(θ − α) · Σ_k θ^{ψ k} v_f(k)`
(`cov_run` and `cost_le` along `n` full sweeps; the remainder `⟨(Tⁿ f − ⟨f⟩) g⟩` is
`≤ αⁿ Σ v_f · sup|g|` by `sweep_to_gibbs`, and `n → ∞`).

DERIVED: `0` the sign of `α` and the limit of `αⁿ`; `1` the bound on `θ`. -/
theorem cov_le_weighted {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {f g : C(Lk → SU N, ℝ)} {vf vg : Lk → ℝ}
    (hvf : OscLe f vf) (hvg : OscLe g vg) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hw : ∀ k, vg k ≤ Vg * θ ^ ψ k) :
    |wExpect Φ (fun W => f W * g W) - wExpect Φ f * wExpect Φ g|
      ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨B, hB⟩ := exists_abs_le g.continuous
  have hθ0 : 0 ≤ θ := by linarith
  have hα1 : α < 1 := by linarith
  have hθα : 0 < θ - α := by linarith
  have hvf0 : ∀ k, 0 ≤ vf k := hvf.nonneg
  have hS0 : 0 ≤ ∑ k, vf k := Finset.sum_nonneg fun k _ => hvf0 k
  have hn : ∀ n : ℕ, |wExpect Φ (fun W => f W * g W) - wExpect Φ f * wExpect Φ g|
      ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + α ^ n * (∑ k, vf k) * B := by
    intro n
    have h1 := cov_run hpos hcont hC g.continuous hvg (rep L n) f.continuous hvf
    have h2 := cost_le hC0 hrow hαθ.le hθ0 hθ1 ψ hloc hVg hw (rep L n) vf hvf0
    have h3 : oscCost C vg (rep L n) vf ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
      have e : Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
          = Vg * (θ * ∑ k, θ ^ ψ k * vf k) / (θ - α) := by ring
      rw [e, le_div_iff₀ hθα]
      linarith
    have hc : Continuous (sweep Φ (rep L n) f) := continuous_sweep hpos hcont _ f.continuous
    have hcE : Continuous fun _ : Lk → SU N => wExpect Φ f := continuous_const
    have hT : ∀ W, |(sweep Φ (rep L n) f W - wExpect Φ f) * g W| ≤ α ^ n * (∑ k, vf k) * B := by
      intro W
      have h := sweep_to_gibbs hpos hcont hC hC0 hrow hα0 hα1.le hL n f hvf W
      rw [sweep_rep] at h
      rw [abs_mul]
      exact mul_le_mul h (hB W) (abs_nonneg _) (mul_nonneg (pow_nonneg hα0 n) hS0)
    have e : wExpect Φ (fun W => sweep Φ (rep L n) f W * g W) - wExpect Φ f * wExpect Φ g
        = wExpect Φ (fun W => (sweep Φ (rep L n) f W - wExpect Φ f) * g W) := by
      have e1 : (fun W => (sweep Φ (rep L n) f W - wExpect Φ f) * g W)
          = fun W => sweep Φ (rep L n) f W * g W - wExpect Φ f * g W :=
        funext fun W => by ring
      rw [e1, wExpect_sub hcont (F := fun W => sweep Φ (rep L n) f W * g W)
        (G := fun W => wExpect Φ f * g W) (hc.mul g.continuous) (hcE.mul g.continuous),
        wExpect_const_mul]
    have h4 : |wExpect Φ (fun W => sweep Φ (rep L n) f W * g W) - wExpect Φ f * wExpect Φ g|
        ≤ α ^ n * (∑ k, vf k) * B := by
      rw [e]
      exact abs_wExpect_le hpos hcont (F := fun W => (sweep Φ (rep L n) f W - wExpect Φ f) * g W)
        ((hc.sub hcE).mul g.continuous) hT
    calc |wExpect Φ (fun W => f W * g W) - wExpect Φ f * wExpect Φ g|
        ≤ |wExpect Φ (fun W => f W * g W) - wExpect Φ (fun W => sweep Φ (rep L n) f W * g W)|
          + |wExpect Φ (fun W => sweep Φ (rep L n) f W * g W) - wExpect Φ f * wExpect Φ g| :=
          abs_sub_le _ _ _
      _ ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + α ^ n * (∑ k, vf k) * B := by
          linarith [h1.trans h3]
  have ht : Tendsto (fun n : ℕ => Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + α ^ n * (∑ k, vf k) * B)
      atTop (𝓝 (Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + 0 * (∑ k, vf k) * B)) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weighted

end Cov

/-! ## 6. Spatial decay -/

section Spatial

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

open Classical in
/-- **The `n`-step influence neighbourhood of `B`**: `B`, then every link with a non-zero influence
on a link already reached.

DERIVED: `0` the start of the recursion and the excluded influence; `1` one step. -/
def reach (C : Lk → Lk → ℝ) (B : Finset Lk) : ℕ → Finset Lk
  | 0 => B
  | n + 1 => reach C B n ∪ Finset.univ.filter (fun l => ∃ k ∈ reach C B n, C l k ≠ 0)

/-- **The influence level of `l` relative to `B`, capped at `D`**: the number of `n < D` with `l`
outside `reach C B n`.

DERIVED: no numeral. -/
def level (C : Lk → Lk → ℝ) (B : Finset Lk) (D : ℕ) (l : Lk) : ℕ :=
  ((Finset.range D).filter (fun n => l ∉ reach C B n)).card

/-- The neighbourhoods grow.

DERIVED: no numeral. -/
theorem reach_mono (C : Lk → Lk → ℝ) (B : Finset Lk) {n m : ℕ} (h : n ≤ m) :
    reach C B n ⊆ reach C B m := by
  induction h with
  | refl => exact fun x hx => hx
  | step _ ih =>
      intro x hx
      show x ∈ reach C B _ ∪ _
      exact Finset.mem_union_left _ (ih hx)

#print axioms reach_mono

/-- **One influence step changes the level by at most one**: `C l k ≠ 0 → level l ≤ level k + 1`,
the `hloc` hypothesis of `mass_step` (and of `BoxDobrushin.influence_decay`).

DERIVED: `0` the excluded influence and the first index; `1` one step. -/
theorem level_loc (C : Lk → Lk → ℝ) (B : Finset Lk) (D : ℕ) {l k : Lk} (h : C l k ≠ 0) :
    level C B D l ≤ level C B D k + 1 := by
  unfold level
  have hsub : (Finset.range D).filter (fun n => l ∉ reach C B n)
      ⊆ insert 0 (((Finset.range D).filter (fun n => k ∉ reach C B n)).image Nat.succ) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rcases n with _ | m
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, ?_, rfl⟩)
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, fun hk => hn.2 ?_⟩
      show l ∈ reach C B m ∪ _
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, h⟩)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right Finset.card_image_le 1

#print axioms level_loc

/-- The level vanishes on `B`.

DERIVED: `0` the level and the first neighbourhood. -/
theorem level_of_mem (C : Lk → Lk → ℝ) {B : Finset Lk} (D : ℕ) {l : Lk} (hl : l ∈ B) :
    level C B D l = 0 := by
  unfold level
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _ hn
  exact hn (reach_mono C B (Nat.zero_le n) hl)

#print axioms level_of_mem

/-- Outside `reach C B d` the level capped at `d + 1` is `d + 1`.

DERIVED: `1` the cap beyond `d`. -/
theorem level_far (C : Lk → Lk → ℝ) (B : Finset Lk) {d : ℕ} {l : Lk} (hl : l ∉ reach C B d) :
    level C B (d + 1) l = d + 1 := by
  unfold level
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro n hn hmem
  exact hl (reach_mono C B (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hmem)

#print axioms level_far

/-- **Spatial Dobrushin decay.** Under the influence hypotheses with row sums `≤ α < θ ≤ 1`: if `g`
has oscillation `≤ V_g` on `B` and `0` off it, and `f` has oscillation `0` on `reach C B d` (the
`d`-step influence neighbourhood of `B`), then
`|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ V_g θ/(θ − α) · θ^{d+1} Σ_k v_f(k)` (`cov_le_weighted` at `level C B (d + 1)`).

DERIVED: `0` the sign and the oscillations off the supports; `1` the bound on `θ` and the cap
beyond `d`. -/
theorem cov_spatial {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    {f g : C(Lk → SU N, ℝ)} {vf vg : Lk → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg)
    (B : Finset Lk) {Vg : ℝ} (hVg : 0 ≤ Vg) (hgB : ∀ k, k ∉ B → vg k = 0)
    (hgV : ∀ k, vg k ≤ Vg) (d : ℕ) (hfar : ∀ k, vf k ≠ 0 → k ∉ reach C B d) :
    |wExpect Φ (fun W => f W * g W) - wExpect Φ f * wExpect Φ g|
      ≤ Vg * θ / (θ - α) * (θ ^ (d + 1) * ∑ k, vf k) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hw : ∀ k, vg k ≤ Vg * θ ^ level C B (d + 1) k := by
    intro k
    by_cases hk : k ∈ B
    · rw [level_of_mem C (d + 1) hk, pow_zero, mul_one]
      exact hgV k
    · rw [hgB k hk]
      exact mul_nonneg hVg (pow_nonneg hθ0 _)
  have h := cov_le_weighted hpos hcont hC hC0 hrow hα0 hαθ hθ1 (level C B (d + 1))
    (fun l k hlk => level_loc C B (d + 1) hlk) hvf hvg hVg hw
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : vf k = 0
    · rw [hk]; simp
    · rw [level_far C B (hfar k hk)]
  · exact div_nonneg (mul_nonneg hVg hθ0) (by linarith)

#print axioms cov_spatial

/-- **An observable reading only the links of `A` has oscillation supported on `A`**: with
`|f| ≤ B₀`, the vector `2B₀` on `A` and `0` off it bounds its single-link oscillations. So the
support hypotheses of `cov_spatial` are met by every continuous local observable.

DERIVED: `0` the oscillation off `A` and the sign; `1` the identity configuration; `2` the two
values compared. -/
theorem oscLe_of_reads {f : (Lk → SU N) → ℝ} (hf : Continuous f) (A : Finset Lk)
    (hA : ∀ W k g, k ∉ A → f (Function.update W k g) = f W) :
    ∃ V : ℝ, 0 ≤ V ∧ OscLe f (fun k => if k ∈ A then V else 0) := by
  obtain ⟨B, hB⟩ := exists_abs_le hf
  refine ⟨2 * B, ?_, fun W k g => ?_⟩
  · have := (abs_nonneg _).trans (hB (fun _ => 1))
    linarith
  · show |f (Function.update W k g) - f W| ≤ if k ∈ A then 2 * B else 0
    by_cases hk : k ∈ A
    · rw [if_pos hk]
      have h1 := abs_le.mp (hB (Function.update W k g))
      have h2 := abs_le.mp (hB W)
      rw [abs_le]
      constructor <;> linarith
    · rw [if_neg hk, hA W k g hk, sub_self, abs_zero]

#print axioms oscLe_of_reads

end Spatial

/-! ## 7. The box -/

section Box

/-- **Spatial Dobrushin decay for the box weight** at Lean `β ≤ 1/40` and local norm `≤ 1/16` at
every link (`infl_wtV`, `rowSum_box` at `α = 39/40`, `cov_spatial`): for every
`θ ∈ (39/40, 1]`, `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ V_g θ/(θ − 39/40) · θ^{d+1} Σ v_f` when `g` is supported on `B`
and `f` off the `d`-step influence neighbourhood of `B`.

DERIVED: `0` the excluded colour count and the sign of `β`; `1` the least `M` and the bound on `θ`;
`1/40`, `1/16`, `39/40` as in `rowSum_box`; `4`, `1` as in `BoxDobrushinCoupling.pairPlaq`. -/
theorem box_cov_spatial (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {M : ℕ}
    (hM : 1 ≤ M) (P : LocalPot N M) (hnorm : ∀ l, P.norm l ≤ 1 / 16) {θ : ℝ}
    (hθ : 39 / 40 < θ) (hθ1 : θ ≤ 1)
    {f g : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)}
    {vf vg : WilsonHypercubic.Link 4 (M + 1) → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg)
    (B : Finset (WilsonHypercubic.Link 4 (M + 1))) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg) (d : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → k ∉ reach (boxInfl β P) B d) :
    |wExpect (wtV β P) (fun W => f W * g W) - wExpect (wtV β P) f * wExpect (wtV β P) g|
      ≤ Vg * θ / (θ - 39 / 40) * (θ ^ (d + 1) * ∑ k, vf k) :=
  cov_spatial (wtV_pos β P) (continuous_wtV β P) (infl_wtV hN hβ0 P) (boxInfl_nonneg hβ0 P)
    (fun l => rowSum_box hβ0 hβ hM P l (hnorm l)) (by norm_num) hθ hθ1 hvf hvg B hVg hgB hgV d hfar

#print axioms box_cov_spatial

/-- **The box at `θ = 79/80`**: `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 79 V_g (79/80)^{d+1} Σ v_f`, decay rate
`log(80/79) ≈ 0.01258` per influence step.

DERIVED: `79/80` the chosen `θ`, midway between `39/40 = 78/80` and `1`;
`79 = (79/80)/(79/80 − 78/80)`; `1/40`, `1/16` as in `rowSum_box`; the rest as in `box_cov_spatial`. -/
theorem box_cov_spatial_79 (hN : N ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {M : ℕ}
    (hM : 1 ≤ M) (P : LocalPot N M) (hnorm : ∀ l, P.norm l ≤ 1 / 16)
    {f g : C(WilsonHypercubic.Link 4 (M + 1) → SU N, ℝ)}
    {vf vg : WilsonHypercubic.Link 4 (M + 1) → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg)
    (B : Finset (WilsonHypercubic.Link 4 (M + 1))) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg) (d : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → k ∉ reach (boxInfl β P) B d) :
    |wExpect (wtV β P) (fun W => f W * g W) - wExpect (wtV β P) f * wExpect (wtV β P) g|
      ≤ 79 * Vg * ((79 / 80) ^ (d + 1) * ∑ k, vf k) := by
  have h := box_cov_spatial hN hβ0 hβ hM P hnorm (θ := 79 / 80) (by norm_num) (by norm_num)
    hvf hvg B hVg hgB hgV d hfar
  have e : Vg * (79 / 80) / (79 / 80 - 39 / 40) = 79 * Vg := by ring
  rwa [e] at h

#print axioms box_cov_spatial_79

end Box

end MassGap.BoxDobrushinSpatial
