import Mathlib
import MassGap.ObserverEnergyCellM

noncomputable section

/-!
# MassGap.ObserverEnergyCellWitness — the cell-view hypothesis is satisfiable and leaves room for N

`ObserverEnergyCellM.CellViewDobrushin` asks a truncated Dobrushin law of class `α` of the cell-energy
field (`DobrushinUnbounded.TruncLaw`) at every truncation level, and affine cell readings of the
monomials of `S`. This module shows the hypothesis is not empty and says what it forces.

1. **The point-mass specification** (`diracSpec`, `diracSpec_infl`, `pointState`, `invariant_dirac`,
   `reach_zeroM`): the kernel that sets one spin to a fixed value is a specification of zero influence,
   and the point state at the constant configuration is invariant under it.
2. **Constant cell fields satisfy `TruncLaw` at every level and class** (`truncLaw_const`): for any
   state, any countable cell type and any cell distance vanishing on the diagonal.
3. **The full cell view holds for a flow, on the Wilson state of every step** (`zeroFlow`,
   `cellE_zeroFlow`, `cellView_zeroFlow`, `cellMoments_zeroFlow`, `latClusterRate_zeroFlow`): for the flow
   that sends every field to `0`, `CellViewDobrushin` holds at `lv = 1`, every `α ≥ 0`, on the cell set
   of single-cell monomials of any base family with a reflection map, and the chain of
   `latClusterRateOn_of_cellView` runs. The cell energies of that flow vanish: this witnesses the
   consistency of the two clauses together, not a non-trivial field.
4. **Class `0` kills the pairings between separated cells** (`truncLaw_zero_cov`): a truncated law of
   class `0` makes the truncated covariance of affine readings of separated cells exactly `0`.
5. **Class `α > 0` does not** (`pairSpec`, `pairBox`, `pairState`, `truncLaw_pair`, `pair_cov`): two
   `±1` cells with a nearest-neighbour coupling `κ ∈ [0, 1/2]` satisfy `TruncLaw` of class `2κ` at every
   level `L ≠ 0`, and their covariance is `2κ`. At `κ = 0` the law is the product law; at
   `κ = 9/20` the class is the `9/10` of `energy_M_of_cellView_90` and the covariance is `9/10`.

## What the M chain needs and what N needs

M consumes `TruncLaw` only through `truncLaw_cov`: covariance decay `θ^{d+1}` between readings more than
`d` apart. N needs a non-zero connected pairing of cell readings. Class `0` (independent cells) forbids
every pairing between separated cells (`truncLaw_zero_cov`); class `α ∈ (0, 1)` admits pairings of size
`α` at the nearest separation (`pair_cov`), so the hypothesis M uses does not force triviality.
-/

namespace MassGap.ObserverEnergyCellWitness

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyCellM Filter
open MassGap.DobrushinUnbounded (Spec SInfl Invariant TruncLaw Tsp clampL clampL_mem
  continuous_clampL tspin truncMap pullC affT truncLaw_cov)
open MassGap.BoxDobrushinSpatial (reach)
open scoped Topology

/-! ## 1. The point-mass specification -/

section Dirac

variable {Ω : Type} [TopologicalSpace Ω]

/-- **The point-mass specification**: the kernel at `l` sets the spin at `l` to `x`.

DERIVED: no numeral. -/
def diracSpec {Lk : Type} [DecidableEq Lk] (x : Ω) : Spec Ω Lk where
  P l f W := f (Function.update W l x)
  cont l _ hf := hf.comp (continuous_id.update l continuous_const)
  lin _ _ _ _ _ _ _ _ := rfl
  one _ _ := rfl
  mono _ _ _ _ _ _ h := h x
  upd l f W y := by
    show f (Function.update (Function.update W l y) l x) = f (Function.update W l x)
    rw [Function.update_idem]

/-- **The point-mass specification has zero influence.**

DERIVED: `0` the influence. -/
theorem diracSpec_infl {Lk : Type} [DecidableEq Lk] (x : Ω) :
    SInfl (diracSpec (Lk := Lk) x) (fun _ _ => 0) := by
  intro l k _ W y φ _ _ _
  show |φ (Function.update (Function.update W k y) l x l) - φ (Function.update W l x l)| ≤ 0
  rw [Function.update_self, Function.update_self, sub_self, abs_zero]

#print axioms diracSpec_infl

/-- **The point state** at `x`: evaluation at `x`.

DERIVED: `0`, `1` as in `DLRLimit.State`. -/
def pointState {X : Type} [TopologicalSpace X] [CompactSpace X] (x : X) : DLRLimit.State X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  nonneg' _ h := h x
  one' := rfl

/-- **The point state at the constant configuration is invariant under the point-mass kernels.**

DERIVED: no numeral. -/
theorem invariant_dirac [CompactSpace Ω] {Lk : Type} [DecidableEq Lk] (x : Ω) :
    Invariant (diracSpec (Lk := Lk) x) (pointState (fun _ : Lk => x)) := by
  intro l f
  exact congrArg (⇑f) (Function.update_eq_self l (fun _ : Lk => x))

#print axioms invariant_dirac

/-- **Zero influence reaches nothing new**: under a vanishing matrix the `d`-step neighbourhood of `B`
is `B`.

DERIVED: `0` the influence. -/
theorem reach_zeroM {Lk : Type} [Fintype Lk] [DecidableEq Lk] (C : Lk → Lk → ℝ)
    (hC : ∀ l k, C l k = 0) (B : Finset Lk) (d : ℕ) : reach C B d = B := by
  induction d with
  | zero => rfl
  | succ n ih => simp [reach, ih, hC]

#print axioms reach_zeroM

/-- Under any matrix the neighbourhood of `∅` is `∅`.

DERIVED: no numeral. -/
theorem reach_empty {Lk : Type} [Fintype Lk] [DecidableEq Lk] (C : Lk → Lk → ℝ) (d : ℕ) :
    reach C ∅ d = ∅ := by
  induction d with
  | zero => rfl
  | succ n ih => simp [reach, ih]

#print axioms reach_empty

end Dirac

/-! ## 2. Constant cell fields satisfy the truncated law -/

section Const

/-- **The box index of a cell at stage `j`**: `enc c + 1` if `enc c < j`, else the spare site `0`.

DERIVED: `1` the offset past the spare site `0`. -/
def encIdx {Cl : Type} (enc : Cl → ℕ) (j : ℕ) (c : Cl) : Fin (j + 1) :=
  if h : enc c < j then ⟨enc c + 1, by omega⟩ else 0

/-- DERIVED: `1` the offset. -/
theorem encIdx_val {Cl : Type} (enc : Cl → ℕ) {j : ℕ} {c : Cl} (h : enc c < j) :
    (encIdx enc j c : ℕ) = enc c + 1 := by
  simp [encIdx, h]

#print axioms encIdx_val

/-- **A constant cell field has a truncated Dobrushin law of every class `α ≥ 0` at every level.**
If every cell energy is the constant `v`, then for any state `ν`, any countable cell type and any
cell distance vanishing on the diagonal, `TruncLaw ν e L α cd` holds: boxes `Fin (j + 1)` read the
cells through an injection into `ℕ` (cells beyond stage `j` share the spare site), each carries the
point-mass specification at the truncated value of `v` (zero influence, `reach_zeroM`) and its
invariant point state, and every truncated reading is the constant it takes on the constant
configuration.

DERIVED: `0` the influence and the sign of `α`; `1` the box offset. -/
theorem truncLaw_const {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]
    [Countable Cl] (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (v : ℝ) (he : ∀ c U, e c U = v)
    (L α : ℝ) (hα : 0 ≤ α) (cd : Cl → Cl → ℕ) (hcd : ∀ c, cd c c = 0) : TruncLaw ν e L α cd := by
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat Cl
  refine ⟨atTop, fun j => j + 1, encIdx enc, fun _ => diracSpec (tspin L v),
    fun j => pointState (fun _ : Fin (j + 1) => tspin L v), fun _ _ _ => 0, inferInstance,
    fun _ => diracSpec_infl _, fun _ _ _ => le_rfl, fun _ _ => by simp [hα],
    fun _ => invariant_dirac _, ?_, ?_⟩
  · intro A A' d hsep
    have hev : ∀ᶠ j in atTop, ∀ c ∈ A ∪ A', enc c < j :=
      (Filter.eventually_all_finset _).2 fun c _ => Filter.eventually_gt_atTop (enc c)
    filter_upwards [hev] with j hj c hc hmem
    rw [reach_zeroM _ (fun _ _ => rfl)] at hmem
    obtain ⟨c', hc', hcc⟩ := Finset.mem_image.1 hmem
    have h1 := encIdx_val enc (hj c (Finset.mem_union_left _ hc))
    have h2 := encIdx_val enc (hj c' (Finset.mem_union_right _ hc'))
    have h3 : enc c' = enc c := by
      have := congrArg Fin.val hcc
      omega
    have h4 := henc h3
    subst h4
    have := hsep c' hc c' hc'
    rw [hcd] at this
    omega
  · intro A H _
    have e2 : ν (H.comp (truncMap L e)) = H (fun _ => tspin L v) := by
      have : H.comp (truncMap L e) = (H (fun _ => tspin L v)) • (1 : C(X, ℝ)) := by
        ext U
        show H (fun c => tspin L (e c U)) = H (fun _ => tspin L v) * 1
        simp only [he, mul_one]
      rw [this, ν.map_smul, ν.map_one, mul_one]
    show Tendsto (fun _ : ℕ => H (fun _ => tspin L v)) atTop (𝓝 (ν (H.comp (truncMap L e))))
    rw [e2]
    exact tendsto_const_nhds

#print axioms truncLaw_const

end Const

/-! ## 3. The full cell view holds for the zero flow on every Wilson state -/

section ZeroFlow

/-- **The zero flow**: every field goes to `0 · O`, of range `0`.

DERIVED: `0` the factor and the range; `2` the rank. -/
def zeroFlow : Flow 2 where
  map _ O := scaleField O 0
  range _ := 0
  map_refl _ τ O := (refl_scaleField τ O 0).symm
  map_local _ O S _ := ⟨S, fun U V _ => by
      show (0 : ℝ) * O.1 U = 0 * O.1 V
      rw [zero_mul, zero_mul], fun l hl => ⟨l, hl, fun i => by simp⟩⟩

/-- **The cells of the zero flow have zero energy** (`smear_smul` at `0`).

DERIVED: `0` the energy; `2` the rank. -/
theorem cellE_zeroFlow {nb : ℕ} (base : Fin nb → SField 2) (m0 k : ℕ) (c : Cell nb) (U : Cfg 2) :
    cellE zeroFlow base m0 k c U = 0 := by
  unfold cellE
  show smear (dySpacing 2 k) ((0 : ℝ) • (cellDatum base m0 c).1.1) (cellDatum base m0 c).2 U = 0
  rw [smear_smul (dySpacing_pos (by norm_num) k)]
  simp

#print axioms cellE_zeroFlow

/-- **`CellViewDobrushin` holds for the zero flow on the Wilson state of every step**, at `lv = 1`, every
class `α ≥ 0`, on the cell set of single-cell monomials of any base family with a reflection map `ρ`
on `I`: the law clause by `truncLaw_const` at `v = 0` (`cellDist` vanishes on the diagonal), the
reader clause by `cellView_readers`. For `i ∈ I` the set holds a one-factor monomial on the base `i`
(`cellSet_nontrivial`).

DERIVED: `1` the rate `lv`; `0` the cell energy and the sign of `α`; `2` the rank. -/
theorem cellView_zeroFlow {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (I : Set (Fin nb)) (ρ : Fin nb → Fin nb) (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i))
    {α : ℝ} (hα : 0 ≤ α) :
    CellViewDobrushin zeroFlow τ r m0 1 α (cellSet base m0 τ r I) (cellDist τ)
      (cellE zeroFlow base m0) :=
  ⟨fun L _ => Filter.Eventually.of_forall fun k =>
      truncLaw_const (stateK two_ne k) (cellE zeroFlow base m0 k) 0 (cellE_zeroFlow base m0 k) L α hα
        (cellDist τ) (fun c => by simp [cellDist]),
    cellView_readers zeroFlow base m0 τ r I ρ hρ⟩

#print axioms cellView_zeroFlow

/-- **The cells of the zero flow have uniform moments** (every power of `0` is at most `1`).

DERIVED: `1` the bound; `2` the even power and the rank; `0` the cell energy. -/
theorem cellMoments_zeroFlow {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) :
    CellMoments (fun k => cellE zeroFlow base m0 k) := by
  intro p
  refine ⟨1, Filter.Eventually.of_forall fun k c => ?_⟩
  calc stateK two_ne k (cellE zeroFlow base m0 k c ^ (2 * p)) ≤ stateK two_ne k 1 :=
        (stateK two_ne k).mono fun U => by
          rw [ContinuousMap.pow_apply, cellE_zeroFlow, ContinuousMap.one_apply]
          exact pow_le_one₀ le_rfl zero_le_one
    _ = 1 := (stateK two_ne k).map_one

#print axioms cellMoments_zeroFlow

/-- **The chain of `latClusterRateOn_of_cellView` runs on the zero-flow witness**: clustering at
`(√θ)¹` for every `θ ∈ (α, 1]`, `α ≥ 0`.

DERIVED: `1` the rate `lv` and the bound on `θ`; `0` the sign of `α`; `2` the rank. -/
theorem latClusterRate_zeroFlow {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (I : Set (Fin nb)) (ρ : Fin nb → Fin nb) (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i))
    {α θ : ℝ} (hα : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) :
    LatClusterRateOn two_ne zeroFlow τ r m0 (Real.sqrt θ ^ 1) (cellSet base m0 τ r I) :=
  latClusterRateOn_of_cellView (cellView_zeroFlow base m0 τ r I ρ hρ hα)
    (cellMoments_zeroFlow base m0) hα hαθ hθ1

#print axioms latClusterRate_zeroFlow

end ZeroFlow

/-! ## 4. Class `0` forbids pairings between separated cells -/

section ZeroClass

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **A truncated law of class `0` makes separated truncated readings uncorrelated.** Under
`TruncLaw ν e L 0 cd`, affine readings of the truncated field on cells more than `d` apart in `cd` have
truncated covariance exactly `0` (`truncLaw_cov` at every `θ ∈ (0, 1]` gives `≤ K θ`, `K` the product
of the weights and the spin diameters).

DERIVED: `0` the class and the covariance; `1` the bound on `θ`; `2 |L|` the spin diameter. -/
theorem truncLaw_zero_cov {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {L : ℝ} {cd : Cl → Cl → ℕ}
    (hv : TruncLaw ν e L 0 cd) (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (d : ℕ)
    (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    ν ((affT L AF wF bF * affT L AG wG bG).comp (truncMap L e))
      - ν ((affT L AF wF bF).comp (truncMap L e)) * ν ((affT L AG wG bG).comp (truncMap L e))
      = 0 := by
  have hWF0 : 0 ≤ WF := (Finset.sum_nonneg fun c _ => abs_nonneg (wF c)).trans hWF
  have hWG0 : 0 ≤ WG := (Finset.sum_nonneg fun c _ => abs_nonneg (wG c)).trans hWG
  set K := WG * (2 * |L|) * (WF * (2 * |L|)) with hKdef
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hWG0 (by positivity)) (mul_nonneg hWF0 (by positivity))
  set x := ν ((affT L AF wF bF * affT L AG wG bG).comp (truncMap L e))
      - ν ((affT L AF wF bF).comp (truncMap L e)) * ν ((affT L AG wG bG).comp (truncMap L e))
    with hxdef
  have hb : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → |x| ≤ K * θ := by
    intro θ h0 h1
    have h := truncLaw_cov hv le_rfl h0 h1 AF AG wF wG bF bG hWF hWG d hsep
    have e1 : WG * (2 * |L|) * θ / (θ - 0) = WG * (2 * |L|) := by
      rw [sub_zero, mul_div_assoc, div_self h0.ne', mul_one]
    rw [e1] at h
    have hp : θ ^ (d + 1) ≤ θ := by
      calc θ ^ (d + 1) = θ * θ ^ d := by ring
        _ ≤ θ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1) h0.le
        _ = θ := mul_one θ
    calc |x| ≤ WG * (2 * |L|) * (θ ^ (d + 1) * (WF * (2 * |L|))) := h
      _ = K * θ ^ (d + 1) := by rw [hKdef]; ring
      _ ≤ K * θ := mul_le_mul_of_nonneg_left hp hK
  rw [← abs_eq_zero]
  by_contra hne
  have hx : 0 < |x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
  have h1 := hb (min 1 (|x| / (2 * (K + 1)))) (lt_min one_pos (div_pos hx (by linarith)))
    (min_le_left _ _)
  have h2 : K * min 1 (|x| / (2 * (K + 1))) ≤ K * (|x| / (2 * (K + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hK
  have h3 : K * (|x| / (2 * (K + 1))) < |x| := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [hx, hK]
  linarith

#print axioms truncLaw_zero_cov

end ZeroClass

/-! ## 5. Class `α > 0` admits pairings: two coupled cells -/

section Pair

/-- **The other site of a pair.**

DERIVED: `0`, `1` the two sites. -/
def oth (l : Fin 2) : Fin 2 := if l = 0 then 1 else 0

/-- DERIVED: `2` the number of sites. -/
theorem oth_ne : ∀ l : Fin 2, oth l ≠ l := by decide

#print axioms oth_ne

/-- DERIVED: `2` the number of sites. -/
theorem oth_eq : ∀ l k : Fin 2, l ≠ k → oth l = k := by decide

#print axioms oth_eq

/-- **The conditional probability of the upper spin** given the other spin `y`:
`1/2 + κ · clamp_m(y)/m`.

DERIVED: `1/2` the unbiased probability. -/
def lam (κ m y : ℝ) : ℝ := 1 / 2 + κ * clampL m y / m

/-- DERIVED: no numeral. -/
theorem continuous_lam (κ m : ℝ) : Continuous (lam κ m) :=
  continuous_const.add ((continuous_const.mul (continuous_clampL m)).div_const m)

#print axioms continuous_lam

/-- **The conditional probability lies within `κ` of `1/2`.**

DERIVED: `1/2` the unbiased probability; `0` the signs. -/
theorem lam_mem {κ m : ℝ} (hκ : 0 ≤ κ) (hm : 0 < m) (y : ℝ) :
    1 / 2 - κ ≤ lam κ m y ∧ lam κ m y ≤ 1 / 2 + κ := by
  have hc := clampL_mem m y
  rw [abs_of_pos hm] at hc
  unfold lam
  constructor
  · have : -κ ≤ κ * clampL m y / m := by
      rw [le_div_iff₀ hm]
      nlinarith [hc.1]
    linarith
  · have : κ * clampL m y / m ≤ κ := by
      rw [div_le_iff₀ hm]
      nlinarith [hc.2]
    linarith

#print axioms lam_mem

/-- The clamp of `m` at `m > 0` is `m`; that of `−m` is `−m`.

DERIVED: `0` the sign of `m`. -/
theorem clampL_self {m : ℝ} (hm : 0 < m) : clampL m m = m ∧ clampL m (-m) = -m := by
  unfold clampL
  rw [abs_of_pos hm]
  constructor
  · rw [min_self, max_eq_right (show -m ≤ m by linarith)]
  · rw [min_eq_left (show -m ≤ m by linarith), max_self]

#print axioms clampL_self

/-- The conditional probability at the two spins `±m`.

DERIVED: `1/2` the unbiased probability. -/
theorem lam_pm {κ m : ℝ} (hm : 0 < m) : lam κ m m = 1 / 2 + κ ∧ lam κ m (-m) = 1 / 2 - κ := by
  obtain ⟨h1, h2⟩ := clampL_self hm
  unfold lam
  rw [h1, h2]
  constructor
  · rw [mul_div_assoc, div_self hm.ne', mul_one]
  · rw [mul_neg, neg_div, mul_div_assoc, div_self hm.ne', mul_one]
    ring

#print axioms lam_pm

/-- The truncation of `−1` is minus that of `1`.

DERIVED: `1` the spin. -/
theorem clampL_neg_one (L : ℝ) : clampL L (-1) = -clampL L 1 := by
  unfold clampL
  have hL := abs_nonneg L
  rcases le_total |L| 1 with h | h
  · rw [min_eq_left (show (-1 : ℝ) ≤ |L| by linarith),
      max_eq_left (show (-1 : ℝ) ≤ -|L| by linarith), min_eq_right h,
      max_eq_right (show -|L| ≤ |L| by linarith)]
  · rw [min_eq_left (show (-1 : ℝ) ≤ |L| by linarith),
      max_eq_right (show -|L| ≤ (-1 : ℝ) by linarith), min_eq_left h,
      max_eq_right (show -|L| ≤ (1 : ℝ) by linarith)]

#print axioms clampL_neg_one

/-- The truncation of `1` at a level `L ≠ 0` is positive.

DERIVED: `0`, `1` the sign and the spin. -/
theorem clampL_one_pos {L : ℝ} (hL : L ≠ 0) : 0 < clampL L 1 :=
  lt_of_lt_of_le (lt_min one_pos (abs_pos.2 hL)) (le_max_right _ _)

#print axioms clampL_one_pos

/-- **The coupled pair specification** on two truncated spins: the kernel at `l` puts the spin at `l`
to the upper value `p` with probability `lam κ m (W (oth l))` and to the lower value `q` otherwise.

DERIVED: `1` the total probability. -/
def pairSpec {L : ℝ} (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) (p q : Tsp L) {m : ℝ} (hm : 0 < m) :
    Spec (Tsp L) (Fin 2) where
  P l f W := lam κ m (W (oth l)) * f (Function.update W l p)
    + (1 - lam κ m (W (oth l))) * f (Function.update W l q)
  cont l _ hf := by
    have hl : Continuous (fun W : Fin 2 → Tsp L => lam κ m (W (oth l) : ℝ)) :=
      (continuous_lam κ m).comp (continuous_subtype_val.comp (continuous_apply _))
    exact (hl.mul (hf.comp (continuous_id.update l continuous_const))).add
      ((continuous_const.sub hl).mul (hf.comp (continuous_id.update l continuous_const)))
  lin _ _ _ _ _ _ _ _ := by ring
  one _ _ := by ring
  mono l _ _ _ _ W h := by
    have hb := lam_mem hκ0 hm (W (oth l) : ℝ)
    exact add_le_add (mul_le_mul_of_nonneg_left (h p) (by linarith [hb.1]))
      (mul_le_mul_of_nonneg_left (h q) (by linarith [hb.2]))
  upd l f W y := by
    show lam κ m (Function.update W l y (oth l) : ℝ) * f (Function.update (Function.update W l y) l p)
        + (1 - lam κ m (Function.update W l y (oth l) : ℝ))
          * f (Function.update (Function.update W l y) l q)
      = lam κ m (W (oth l) : ℝ) * f (Function.update W l p)
        + (1 - lam κ m (W (oth l) : ℝ)) * f (Function.update W l q)
    rw [Function.update_of_ne (oth_ne l), Function.update_idem, Function.update_idem]

/-- **The influence matrix of the pair**: `2κ` off the diagonal.

DERIVED: `2κ` the width of the conditional probability's range; `0` the diagonal. -/
def pairInfl (κ : ℝ) (l k : Fin 2) : ℝ := if l = k then 0 else 2 * κ

/-- **The pair specification has influence `2κ`.** Changing the other spin moves the conditional
probability by at most `2κ` (`lam_mem`), and a `[0, 1]` test function of the spin moves by at most `1`.

DERIVED: `2κ`, `0`, `1` as in `pairInfl` and `SInfl`. -/
theorem pairSpec_infl {κ L : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) (p q : Tsp L) {m : ℝ} (hm : 0 < m) :
    SInfl (pairSpec κ hκ0 hκ1 p q hm) (pairInfl κ) := by
  intro l k hlk W y φ _ h0 h1
  show |(lam κ m (Function.update W k y (oth l) : ℝ) * φ (Function.update (Function.update W k y) l p l)
      + (1 - lam κ m (Function.update W k y (oth l) : ℝ))
        * φ (Function.update (Function.update W k y) l q l))
      - (lam κ m (W (oth l) : ℝ) * φ (Function.update W l p l)
        + (1 - lam κ m (W (oth l) : ℝ)) * φ (Function.update W l q l))| ≤ pairInfl κ l k
  simp only [Function.update_self]
  unfold pairInfl
  rw [if_neg hlk]
  set a := lam κ m (Function.update W k y (oth l) : ℝ)
  set b := lam κ m (W (oth l) : ℝ)
  have ha := lam_mem hκ0 hm (Function.update W k y (oth l) : ℝ)
  have hb := lam_mem hκ0 hm (W (oth l) : ℝ)
  have e : a * φ p + (1 - a) * φ q - (b * φ p + (1 - b) * φ q) = (a - b) * (φ p - φ q) := by ring
  rw [e, abs_mul]
  have hab : |a - b| ≤ 2 * κ := by
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hpq : |φ p - φ q| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [h0 p, h0 q, h1 p, h1 q]
  calc |a - b| * |φ p - φ q| ≤ 2 * κ * 1 :=
        mul_le_mul hab hpq (abs_nonneg _) (by linarith)
    _ = 2 * κ := mul_one _

#print axioms pairSpec_infl

/-- **The weight of an equal pair** `(1/2 + κ)/2` and of an unequal pair `(1/2 − κ)/2`.

DERIVED: `1/2` the unbiased probability; `2` the two configurations of each kind. -/
def wEq (κ : ℝ) : ℝ := (1 / 2 + κ) / 2

/-- DERIVED: as `wEq`. -/
def wNe (κ : ℝ) : ℝ := (1 / 2 - κ) / 2

/-- **The pair state on a two-site space**: weight `wEq` on the equal configurations `(u, u)`, `(v, v)`,
`wNe` on the unequal ones.

DERIVED: `0`, `1` the two sites; `1/2` through `wEq`, `wNe`. -/
def pairOn {Y : Type} (u v : Y) (κ : ℝ) (f : (Fin 2 → Y) → ℝ) : ℝ :=
  wEq κ * f ![u, u] + wNe κ * f ![u, v] + wNe κ * f ![v, u] + wEq κ * f ![v, v]

/-- **The pair state** as a `DLRLimit.State` on `Fin 2 → Y`, `|κ| ≤ 1/2`.

DERIVED: `1/2` the bound on `κ`; `0`, `1` as in `DLRLimit.State`. -/
def pairStateOn {κ : ℝ} {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (u v : Y) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1 / 2) : DLRLimit.State (Fin 2 → Y) where
  toFun f := pairOn u v κ f
  map_add' f g := by
    unfold pairOn
    simp only [ContinuousMap.add_apply]
    ring
  map_smul' c f := by
    unfold pairOn
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring
  nonneg' f h := by
    unfold pairOn wEq wNe
    have h1 : 0 ≤ (1 / 2 + κ) / 2 := by linarith
    have h2 : 0 ≤ (1 / 2 - κ) / 2 := by linarith
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg h1 (h _)) (mul_nonneg h2 (h _)))
      (mul_nonneg h2 (h _))) (mul_nonneg h1 (h _))
  one' := by
    unfold pairOn wEq wNe
    simp only [ContinuousMap.one_apply]
    ring

/-- Updating a pair at site `0` or `1`.

DERIVED: `0`, `1` the sites. -/
theorem update_pair0 {Y : Type} (a b c : Y) : Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> rfl

#print axioms update_pair0

/-- DERIVED: `0`, `1` the sites. -/
theorem update_pair1 {Y : Type} (a b c : Y) : Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> rfl

#print axioms update_pair1

/-- **The pair state is invariant under the pair specification** at the spins `p`, `q = −p`.

DERIVED: `0`, `1` the sites; `1/2` the unbiased probability. -/
theorem invariant_pair {κ L : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) (p q : Tsp L) (hp : 0 < (p : ℝ))
    (hq : (q : ℝ) = -(p : ℝ)) :
    Invariant (pairSpec κ hκ0 hκ1 p q hp) (pairStateOn p q hκ0 hκ1) := by
  intro l f
  obtain ⟨hlp, hlq⟩ := lam_pm (κ := κ) hp
  rw [← hq] at hlq
  show pairOn p q κ (fun W => lam κ (p : ℝ) (W (oth l) : ℝ) * f (Function.update W l p)
      + (1 - lam κ (p : ℝ) (W (oth l) : ℝ)) * f (Function.update W l q)) = pairOn p q κ f
  unfold pairOn wEq wNe
  have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
  rcases hl with rfl | rfl
  · simp [oth, update_pair0, hlp, hlq]
    ring
  · simp [oth, update_pair1, hlp, hlq]
    ring

#print axioms invariant_pair

/-- **The two `±1` cells** on `Fin 2 → Bool`: the cell `c` reads `1` if its bit is set, else `−1`.

DERIVED: `±1` the two energies. -/
def pairCell (c : Fin 2) : C(Fin 2 → Bool, ℝ) :=
  ⟨fun U => if U c then 1 else -1, continuous_of_discreteTopology⟩

/-- **The cell distance of the pair**: `0` on the diagonal, `1` off it.

DERIVED: `0`, `1` the distances. -/
def pairDist (c c' : Fin 2) : ℕ := if c = c' then 0 else 1

/-- **The coupled pair satisfies the truncated law of class `2κ` at every level `L ≠ 0`.** The state
`pairStateOn true false` of the two `±1` cells is, read through the truncation at `L`, exactly the box
state `pairStateOn p q` of the pair specification at `p = T_L(1)`, `q = T_L(−1) = −p`; the influence is
`2κ` (`pairSpec_infl`) with row sums `2κ`, and influence steps are one unit of `pairDist`.

DERIVED: `2κ` the class; `0`, `1` the sites and distances; `1/2` the bound on `κ`. -/
theorem truncLaw_pair {κ L : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) (hL : L ≠ 0) :
    TruncLaw (pairStateOn true false hκ0 hκ1) pairCell L (2 * κ) pairDist := by
  have hp : 0 < (tspin L 1 : ℝ) := clampL_one_pos hL
  have hq : (tspin L (-1) : ℝ) = -(tspin L 1 : ℝ) := clampL_neg_one L
  refine ⟨atTop, fun _ => 2, fun _ c => c, fun _ => pairSpec κ hκ0 hκ1 (tspin L 1) (tspin L (-1)) hp,
    fun _ => pairStateOn (tspin L 1) (tspin L (-1)) hκ0 hκ1, fun _ => pairInfl κ, inferInstance,
    fun _ => pairSpec_infl hκ0 hκ1 _ _ hp, fun _ l k => ?_, fun _ l => ?_,
    fun _ => invariant_pair hκ0 hκ1 _ _ hp hq, ?_, ?_⟩
  · show 0 ≤ pairInfl κ l k
    unfold pairInfl
    split_ifs <;> linarith
  · rw [Fin.sum_univ_two]
    unfold pairInfl
    fin_cases l <;> simp
  · intro A A' d hsep
    refine Filter.Eventually.of_forall fun _ c hc hmem => ?_
    rcases A'.eq_empty_or_nonempty with h0 | ⟨c', hc'⟩
    · rw [h0, Finset.image_empty, reach_empty] at hmem
      exact Finset.notMem_empty c hmem
    · have hd : d < pairDist c c' := hsep c hc c' hc'
      have hd1 : pairDist c c' ≤ 1 := by unfold pairDist; split_ifs <;> omega
      have hd0 : d = 0 := by omega
      subst hd0
      have hmem' : c ∈ A'.image (fun c => c) := hmem
      obtain ⟨c'', hc'', hcc⟩ := Finset.mem_image.1 hmem'
      subst hcc
      have := hsep c'' hc c'' hc''
      simp [pairDist] at this
  · intro A H _
    have e : (pairStateOn true false hκ0 hκ1) (H.comp (truncMap L pairCell))
        = (pairStateOn (tspin L 1) (tspin L (-1)) hκ0 hκ1) (H.comp (pullC (fun c : Fin 2 => c))) := by
      show pairOn true false κ (fun U => H (fun c => tspin L (pairCell c U)))
        = pairOn (tspin L 1) (tspin L (-1)) κ (fun W => H (fun c => W c))
      unfold pairOn
      beta_reduce
      have h1 : (fun c => tspin L (pairCell c ![true, true])) = ![tspin L 1, tspin L 1] := by
        funext c; fin_cases c <;> rfl
      have h2 : (fun c => tspin L (pairCell c ![true, false])) = ![tspin L 1, tspin L (-1)] := by
        funext c; fin_cases c <;> rfl
      have h3 : (fun c => tspin L (pairCell c ![false, true])) = ![tspin L (-1), tspin L 1] := by
        funext c; fin_cases c <;> rfl
      have h4 : (fun c => tspin L (pairCell c ![false, false])) = ![tspin L (-1), tspin L (-1)] := by
        funext c; fin_cases c <;> rfl
      rw [h1, h2, h3, h4]
    show Tendsto (fun _ : ℕ => (pairStateOn (tspin L 1) (tspin L (-1)) hκ0 hκ1)
        (H.comp (pullC (fun c : Fin 2 => c)))) atTop
      (𝓝 ((pairStateOn true false hκ0 hκ1) (H.comp (truncMap L pairCell))))
    rw [e]
    exact tendsto_const_nhds

#print axioms truncLaw_pair

/-- **The coupled cells are correlated**: their covariance in the pair state is `2κ`, the class of the
law; both means vanish.

DERIVED: `2κ` the covariance; `0` the means. -/
theorem pair_cov {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    (pairStateOn true false hκ0 hκ1) (pairCell 0 * pairCell 1)
        - (pairStateOn true false hκ0 hκ1) (pairCell 0) * (pairStateOn true false hκ0 hκ1) (pairCell 1)
      = 2 * κ := by
  show pairOn true false κ (fun U => pairCell 0 U * pairCell 1 U)
      - pairOn true false κ (fun U => pairCell 0 U) * pairOn true false κ (fun U => pairCell 1 U)
    = 2 * κ
  unfold pairOn wEq wNe pairCell
  simp <;> ring

#print axioms pair_cov

/-- **At class `9/10` the pair has covariance `9/10`.** At `κ = 9/20` the coupled pair satisfies the
truncated law of class `9/10` (the class of `energy_M_of_cellView_90`) at every level `L ≠ 0`, and the
covariance of its two cells is `9/10`.

DERIVED: `9/20` the coupling; `9/10 = 2 · 9/20` the class and the covariance; `1/2` the bound. -/
theorem pair_90 {L : ℝ} (hL : L ≠ 0) :
    TruncLaw (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 9 / 20) (by norm_num)) pairCell L
        (9 / 10) pairDist ∧
      (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 9 / 20) (by norm_num))
          (pairCell 0 * pairCell 1)
        - (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 9 / 20) (by norm_num)) (pairCell 0)
          * (pairStateOn true false (by norm_num : (0 : ℝ) ≤ 9 / 20) (by norm_num)) (pairCell 1)
        = 9 / 10 := by
  have h := truncLaw_pair (κ := 9 / 20) (by norm_num) (by norm_num) hL
  have hc := pair_cov (κ := 9 / 20) (by norm_num) (by norm_num)
  rw [show (2 : ℝ) * (9 / 20) = 9 / 10 by norm_num] at h hc
  exact ⟨h, hc⟩

#print axioms pair_90

end Pair

end MassGap.ObserverEnergyCellWitness
