import Mathlib
import MassGap.DobrushinMixed
import MassGap.BlockHeatBath

noncomputable section

/-!
# MassGap.DSBlockContract — the block dynamics over all translates contracts the summed link metric

`DobrushinMixed.lip_stepD` moves a Lipschitz vector through one single-site kernel. Here the kernel resamples a
whole block `S` given the outside, and the influence is the Dobrushin–Shlosman one: the effect of one outside
site `k` on the conditional law of the block, tested against functions of the block that are Lipschitz in the
summed cost.

1. **Block kernels** (`BlockKer`): an operator `Q` on real functions of the configuration that reads `f` only on
   the fibre `glue S W ·`, is bounded by the fibre's supremum, does not read `S`, and is continuous and additive.
   `wilsonKer` is the instance for the Wilson block average `BlockHeatBath.blkAvg`.
2. **The block influence** (`BlkInfl`): for every continuous `g` reading only `S` with Lipschitz vector `v`,
   moving the outside site `k` by `x` moves `Q g` by at most `(Σ_{l ∈ S} C l k v l) · d k x (W k)`. With `v`
   the indicator of one link `l` this is the W1 influence of `k` on the marginal at `l`; with general `v` it is
   the joint form, which a single coupling of the two block laws bounds (the synchronous coupling of two
   frozen-boundary runs that differ at `k`).
3. **One block step** (`blk_stepD`): `Q f` has the vector `blkVec`: `0` on `S`, `v k + Σ_{l∈S} C l k v l` off it.
4. **The average over a family of blocks** (`avgQ`, `avg_stepD`, `sum_avgVec_le`, `avg_iterD`, `osc_iter_le`):
   the total of the vector falls by `Σ_l v l · (1/|Z|) Σ_z gain_z l`, where `gain_z l = 1 − Σ_{k ∉ S_z} C_z l k`
   for `l ∈ S_z`. A column bound `κ |Z| ≤ Σ_z gain_z l` at every link gives the contraction `1 − κ` of the
   total, hence oscillation `≤ (1 − κ)ⁿ (Σ v) Dm` after `n` steps.

## The translate count

For the translates `V + z` of one box on a periodic lattice, every link lies in `|V|` translates (per link
direction, the box's links of that direction), and by translation covariance
`Σ_z gain_z l = Σ_{l' ∈ V} (1 − Σ_{k ∉ V} C_V l' k)` over the box links `l'` of `l`'s direction:
`|V|(1 − ρ_V)` in the notation of the box criterion, so `κ = |V|(1 − ρ_V)/|Z|`. A single block of the
`n`-grid alone gives no such per-link count: a boundary link's summed influence is not bounded by the box
average. `DSBoxFloor` supplies the covariance and the count.

## Gaussian unit

For a Gaussian field the conditional law of a box is a shift of a fixed law by the linear response to the
boundary, so the shift coupling realises every `C l k` at once (the joint form equals the marginal form), and
`(1/|V|) Σ_{l ∈ V} Σ_{k ∉ V} C l k = ρ_V` is the mean escape probability of the killed walk
(`research/code/lab/ds_unit.py`). Massless, `ρ_V = 1`: the gain vanishes and nothing contracts.

DERIVED (module-wide): `0` the signs and the block entries of `blkVec`; `1` the gain's unit.
-/

namespace MassGap.DSBlockContract

open MeasureTheory
open MassGap.DobrushinMixed (LipD abs_sub_le_sum_lipD)
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)

/-! ## 1. Block kernels and the block influence -/

section Generic

variable {Ω : Type} [TopologicalSpace Ω] {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **`g` reads only the links of `S`.** DERIVED: no numeral. -/
def ReadsOnly (S : Finset Lk) (g : (Lk → Ω) → ℝ) : Prop :=
  ∀ U U' : Lk → Ω, (∀ l ∈ S, U l = U' l) → g U = g U'

omit [TopologicalSpace Ω] [Fintype Lk] in
/-- Re-gluing over the same set forgets the inner outside. DERIVED: no numeral. -/
theorem glue_glue_right (S : Finset Lk) (W V V' : Lk → Ω) :
    glue S W (glue S V' V) = glue S W V := by
  funext i
  by_cases hi : i ∈ S
  · rw [glue_of_mem hi, glue_of_mem hi, glue_of_mem hi]
  · rw [glue_of_not_mem hi, glue_of_not_mem hi]

#print axioms glue_glue_right

omit [TopologicalSpace Ω] [Fintype Lk] in
/-- An update outside `S` commutes with the glue. DERIVED: no numeral. -/
theorem glue_update_off (S : Finset Lk) (W V : Lk → Ω) {k : Lk} (hk : k ∉ S) (x : Ω) :
    glue S (Function.update W k x) V = Function.update (glue S W V) k x := by
  funext i
  by_cases hik : i = k
  · subst hik
    rw [glue_of_not_mem hk, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hik]
    by_cases hi : i ∈ S
    · rw [glue_of_mem hi, glue_of_mem hi]
    · rw [glue_of_not_mem hi, glue_of_not_mem hi, Function.update_of_ne hik]

#print axioms glue_update_off

omit [TopologicalSpace Ω] [Fintype Lk] in
/-- An update inside `S` of the fibre is an update of the glued configuration. DERIVED: no numeral. -/
theorem glue_update_in (S : Finset Lk) (W U : Lk → Ω) {l : Lk} (hl : l ∈ S) (y : Ω) :
    glue S W (Function.update U l y) = Function.update (glue S W U) l y := by
  funext i
  by_cases hil : i = l
  · subst hil
    rw [glue_of_mem hl, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hil]
    by_cases hi : i ∈ S
    · rw [glue_of_mem hi, glue_of_mem hi, Function.update_of_ne hil]
    · rw [glue_of_not_mem hi, glue_of_not_mem hi]

#print axioms glue_update_in

omit [TopologicalSpace Ω] [Fintype Lk] in
/-- An update outside `S` of the fibre changes nothing. DERIVED: no numeral. -/
theorem glue_update_fibre_off (S : Finset Lk) (W U : Lk → Ω) {l : Lk} (hl : l ∉ S) (y : Ω) :
    glue S W (Function.update U l y) = glue S W U := by
  funext i
  by_cases hi : i ∈ S
  · have hil : i ≠ l := fun h => hl (h ▸ hi)
    rw [glue_of_mem hi, glue_of_mem hi, Function.update_of_ne hil]
  · rw [glue_of_not_mem hi, glue_of_not_mem hi]

#print axioms glue_update_fibre_off

/-- **A block kernel**: resample the links of `S` given the rest.

DERIVED: no numeral. -/
structure BlockKer (Ω : Type) [TopologicalSpace Ω] (Lk : Type) [DecidableEq Lk] where
  /-- The block. -/
  S : Finset Lk
  /-- The kernel, acting on real functions of the configuration. -/
  Q : ((Lk → Ω) → ℝ) → (Lk → Ω) → ℝ
  /-- Feller. -/
  cont : ∀ {f : (Lk → Ω) → ℝ}, Continuous f → Continuous (Q f)
  /-- Additive on continuous functions. -/
  sub : ∀ {f g : (Lk → Ω) → ℝ}, Continuous f → Continuous g → ∀ W : Lk → Ω,
    Q (fun U => f U - g U) W = Q f W - Q g W
  /-- Bounded by the supremum on the fibre `glue S W ·`. -/
  bound : ∀ {h : (Lk → Ω) → ℝ}, Continuous h → ∀ (W : Lk → Ω) (B : ℝ),
    (∀ V : Lk → Ω, |h (glue S W V)| ≤ B) → |Q h W| ≤ B
  /-- Reads `f` only on the fibre at `W`. -/
  fibre : ∀ {f : (Lk → Ω) → ℝ}, Continuous f → ∀ W : Lk → Ω,
    Q (fun U => f (glue S W U)) W = Q f W
  /-- Does not read the block. -/
  reads_not : ∀ (f : (Lk → Ω) → ℝ) (W : Lk → Ω) (k : Lk), k ∈ S → ∀ x : Ω,
    Q f (Function.update W k x) = Q f W

/-- **The Dobrushin–Shlosman influence of the outside on the block**, in the costs `d`: for every continuous `g`
reading only the block, with Lipschitz vector `v`, moving the outside link `k` from `W k` to `x` moves the block
mean of `g` by at most `(Σ_{l ∈ S} C l k · v l) · d k x (W k)`.

DERIVED: no numeral. -/
def BlkInfl (K : BlockKer Ω Lk) (d : Lk → Ω → Ω → ℝ) (C : Lk → Lk → ℝ) : Prop :=
  ∀ g : (Lk → Ω) → ℝ, Continuous g → ReadsOnly K.S g → ∀ v : Lk → ℝ, LipD d g v →
    ∀ (W : Lk → Ω) (k : Lk), k ∉ K.S → ∀ x : Ω,
      |K.Q g (Function.update W k x) - K.Q g W| ≤ (∑ l ∈ K.S, C l k * v l) * d k x (W k)

/-- **The vector after one block step**: `0` on the block, `v k + Σ_{l∈S} C l k v l` off it.

DERIVED: `0` the block entries. -/
def blkVec (S : Finset Lk) (C : Lk → Lk → ℝ) (v : Lk → ℝ) : Lk → ℝ :=
  fun k => if k ∈ S then 0 else v k + ∑ l ∈ S, C l k * v l

omit [Fintype Lk] in
/-- **One block step on Lipschitz vectors.**

DERIVED: `0` the signs. -/
theorem blk_stepD (K : BlockKer Ω Lk) {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Lk → Lk → ℝ} (hC : BlkInfl K d C) (hC0 : ∀ l k, 0 ≤ C l k)
    {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : LipD d f v) :
    LipD d (K.Q f) (blkVec K.S C v) := by
  refine ⟨fun k => ?_, fun W k x => ?_⟩
  · unfold blkVec
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hv.1 k) (Finset.sum_nonneg fun l _ => mul_nonneg (hC0 l k) (hv.1 l))
  · by_cases hk : k ∈ K.S
    · rw [K.reads_not f W k hk x, sub_self, abs_zero]
      simp only [blkVec, if_pos hk, zero_mul, le_refl]
    · simp only [blkVec, if_neg hk]
      obtain ⟨ψ, hψ⟩ : ∃ ψ : (Lk → Ω) → ℝ, ∀ U, ψ U = f (glue K.S W U) := ⟨_, fun _ => rfl⟩
      have hψe : ψ = fun U => f (glue K.S W U) := funext hψ
      have hψc : Continuous ψ := by
        rw [hψe]; exact hf.comp (MassGap.BlockHeatBath.continuous_glue_right K.S W)
      have hψR : ReadsOnly K.S ψ := by
        intro U U' h
        rw [hψ, hψ]
        congr 1
        funext i
        by_cases hi : i ∈ K.S
        · rw [glue_of_mem hi, glue_of_mem hi, h i hi]
        · rw [glue_of_not_mem hi, glue_of_not_mem hi]
      have hψL : LipD d ψ v := by
        refine ⟨hv.1, fun U l y => ?_⟩
        rw [hψ, hψ]
        by_cases hl : l ∈ K.S
        · rw [glue_update_in K.S W U hl y]
          have h := hv.2 (glue K.S W U) l y
          rwa [glue_of_mem hl] at h
        · rw [glue_update_fibre_off K.S W U hl y, sub_self, abs_zero]
          exact mul_nonneg (hv.1 l) (hd0 l y (U l))
      have s0 : K.Q ψ W = K.Q f W := by
        rw [hψe]; exact K.fibre hf W
      have s1 : |K.Q f (Function.update W k x) - K.Q ψ (Function.update W k x)|
          ≤ v k * d k x (W k) := by
        rw [← K.sub hf hψc (Function.update W k x)]
        refine K.bound (hf.sub hψc) (Function.update W k x) _ (fun V => ?_)
        show |f (glue K.S (Function.update W k x) V) - ψ (glue K.S (Function.update W k x) V)| ≤ _
        rw [hψ, glue_glue_right, glue_update_off K.S W V hk x]
        have h := hv.2 (glue K.S W V) k x
        rwa [glue_of_not_mem hk] at h
      have s2 := hC ψ hψc hψR v hψL W k hk x
      have e : K.Q f (Function.update W k x) - K.Q f W
          = (K.Q f (Function.update W k x) - K.Q ψ (Function.update W k x))
            + (K.Q ψ (Function.update W k x) - K.Q ψ W) := by
        rw [s0]; ring
      rw [e]
      calc _ ≤ |K.Q f (Function.update W k x) - K.Q ψ (Function.update W k x)|
            + |K.Q ψ (Function.update W k x) - K.Q ψ W| := abs_add_le _ _
        _ ≤ v k * d k x (W k) + (∑ l ∈ K.S, C l k * v l) * d k x (W k) := add_le_add s1 s2
        _ = (v k + ∑ l ∈ K.S, C l k * v l) * d k x (W k) := by ring

#print axioms blk_stepD

/-! ## 2. The average over a family of blocks -/

/-- **The gain at a link**: `1 − Σ_{k ∉ S} C l k` on the block, `0` off it.

DERIVED: `1` the unit; `0` off the block. -/
def gain (S : Finset Lk) (C : Lk → Lk → ℝ) (l : Lk) : ℝ :=
  if l ∈ S then 1 - ∑ k ∈ Sᶜ, C l k else 0

/-- **The total of the block-step vector.**

DERIVED: no numeral. -/
theorem sum_blkVec (S : Finset Lk) (C : Lk → Lk → ℝ) (v : Lk → ℝ) :
    ∑ k, blkVec S C v k = ∑ k, v k - ∑ l, v l * gain S C l := by
  have h1 : ∑ k, blkVec S C v k = ∑ k ∈ Sᶜ, (v k + ∑ l ∈ S, C l k * v l) := by
    rw [← Finset.sum_add_sum_compl S (blkVec S C v)]
    have h0 : ∑ k ∈ S, blkVec S C v k = 0 :=
      Finset.sum_eq_zero fun k hk => by simp only [blkVec, if_pos hk]
    rw [h0, zero_add]
    exact Finset.sum_congr rfl fun k hk => by
      simp only [blkVec, if_neg (Finset.mem_compl.mp hk)]
  have h2 : ∑ l, v l * gain S C l = ∑ l ∈ S, v l * (1 - ∑ k ∈ Sᶜ, C l k) := by
    rw [← Finset.sum_add_sum_compl S (fun l => v l * gain S C l)]
    have h0 : ∑ l ∈ Sᶜ, v l * gain S C l = 0 :=
      Finset.sum_eq_zero fun l hl => by simp only [gain, if_neg (Finset.mem_compl.mp hl), mul_zero]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun l hl => by simp only [gain, if_pos hl]
  have h3 : ∑ k ∈ Sᶜ, ∑ l ∈ S, C l k * v l = ∑ l ∈ S, v l * ∑ k ∈ Sᶜ, C l k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h1, h2, Finset.sum_add_distrib, h3, ← Finset.sum_add_sum_compl S v]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

#print axioms sum_blkVec

variable {Z : Type} [Fintype Z]

/-- **The averaged block dynamics**: `(1/|Z|) Σ_z Q_z`.

DERIVED: no numeral. -/
def avgQ (K : Z → BlockKer Ω Lk) (f : (Lk → Ω) → ℝ) (W : Lk → Ω) : ℝ :=
  (Fintype.card Z : ℝ)⁻¹ * ∑ z, (K z).Q f W

/-- **The averaged vector.** DERIVED: no numeral. -/
def avgVec (K : Z → BlockKer Ω Lk) (C : Z → Lk → Lk → ℝ) (v : Lk → ℝ) : Lk → ℝ :=
  fun k => (Fintype.card Z : ℝ)⁻¹ * ∑ z, blkVec (K z).S (C z) v k

omit [Fintype Lk] in
/-- DERIVED: no numeral. -/
theorem continuous_avgQ (K : Z → BlockKer Ω Lk) {f : (Lk → Ω) → ℝ} (hf : Continuous f) :
    Continuous (avgQ K f) :=
  continuous_const.mul (continuous_finsetSum _ fun z _ => (K z).cont hf)

#print axioms continuous_avgQ

omit [Fintype Lk] in
/-- **The averaged step on Lipschitz vectors.**

DERIVED: `0` the signs. -/
theorem avg_stepD (K : Z → BlockKer Ω Lk) {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z)) (hC0 : ∀ z l k, 0 ≤ C z l k)
    {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : LipD d f v) :
    LipD d (avgQ K f) (avgVec K C v) := by
  have hz : ∀ z, LipD d ((K z).Q f) (blkVec (K z).S (C z) v) :=
    fun z => blk_stepD (K z) hd0 (hC z) (hC0 z) hf hv
  have hZ0 : (0 : ℝ) ≤ (Fintype.card Z : ℝ)⁻¹ := by positivity
  refine ⟨fun k => mul_nonneg hZ0 (Finset.sum_nonneg fun z _ => (hz z).1 k), fun W k x => ?_⟩
  unfold avgQ avgVec
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hZ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hZ0
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => (hz z).2 W k x)

#print axioms avg_stepD

/-- **The column bound contracts the total**: `κ |Z| ≤ Σ_z gain_z l` at every link gives
`Σ avgVec ≤ (1 − κ) Σ v`.

DERIVED: `0` the signs; `1` the contraction's unit. -/
theorem sum_avgVec_le [Nonempty Z] (K : Z → BlockKer Ω Lk) (C : Z → Lk → Lk → ℝ) {κ : ℝ}
    (hcol : ∀ l, κ * Fintype.card Z ≤ ∑ z, gain (K z).S (C z) l) {v : Lk → ℝ} (hv0 : ∀ k, 0 ≤ v k) :
    ∑ k, avgVec K C v k ≤ (1 - κ) * ∑ k, v k := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have e : ∑ k, avgVec K C v k
      = (Fintype.card Z : ℝ)⁻¹ * ∑ z, (∑ k, v k - ∑ l, v l * gain (K z).S (C z) l) := by
    unfold avgVec
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun z _ => sum_blkVec _ _ _
  have e2 : ∑ z, (∑ k, v k - ∑ l, v l * gain (K z).S (C z) l)
      = (Fintype.card Z : ℝ) * ∑ k, v k - ∑ l, v l * ∑ z, gain (K z).S (C z) l := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
  have h3 : κ * Fintype.card Z * ∑ k, v k ≤ ∑ l, v l * ∑ z, gain (K z).S (C z) l := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ =>
      calc κ * Fintype.card Z * v l = v l * (κ * Fintype.card Z) := by ring
        _ ≤ v l * ∑ z, gain (K z).S (C z) l := mul_le_mul_of_nonneg_left (hcol l) (hv0 l)
  rw [e, e2, inv_mul_le_iff₀ hZ]
  have e3 : (Fintype.card Z : ℝ) * ((1 - κ) * ∑ k, v k)
      = (Fintype.card Z : ℝ) * ∑ k, v k - κ * Fintype.card Z * ∑ k, v k := by ring
  rw [e3]
  linarith

#print axioms sum_avgVec_le

/-- **`n` averaged steps leave total `≤ (1 − κ)ⁿ Σ v`.**

DERIVED: `0` the signs; `1` the contraction's unit. -/
theorem avg_iterD [Nonempty Z] (K : Z → BlockKer Ω Lk) {d : Lk → Ω → Ω → ℝ}
    (hd0 : ∀ l a b, 0 ≤ d l a b) {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z))
    (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} (hcol : ∀ l, κ * Fintype.card Z ≤ ∑ z, gain (K z).S (C z) l)
    (hκ1 : κ ≤ 1) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipD d f v →
      ∃ u : Lk → ℝ, LipD d ((avgQ K)^[n] f) u ∧ ∑ k, u k ≤ (1 - κ) ^ n * ∑ k, v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    have h1 := avg_stepD K hd0 hC hC0 hf hv
    obtain ⟨u, hu, hus⟩ := avg_iterD K hd0 hC hC0 hcol hκ1 n (continuous_avgQ K hf) h1
    refine ⟨u, by rwa [Function.iterate_succ_apply], ?_⟩
    have h2 := sum_avgVec_le K C hcol hv.1
    calc ∑ k, u k ≤ (1 - κ) ^ n * ∑ k, avgVec K C v k := hus
      _ ≤ (1 - κ) ^ n * ((1 - κ) * ∑ k, v k) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) n)
      _ = (1 - κ) ^ (n + 1) * ∑ k, v k := by ring

#print axioms avg_iterD

omit [Fintype Lk] in
/-- DERIVED: no numeral. -/
theorem continuous_iter_avgQ (K : Z → BlockKer Ω Lk) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → Continuous ((avgQ K)^[n] f)
  | 0, _, hf => hf
  | n + 1, f, hf => by
    rw [Function.iterate_succ_apply]
    exact continuous_iter_avgQ K n (continuous_avgQ K hf)

#print axioms continuous_iter_avgQ

/-- **Oscillation after `n` averaged steps**: `|Tⁿf W − Tⁿf W'| ≤ (1 − κ)ⁿ (Σ v) Dm`.

DERIVED: `0` the signs; `1` the contraction's unit. -/
theorem osc_iter_le [CompactSpace Ω] [Nonempty Ω] [Nonempty Z] (K : Z → BlockKer Ω Lk) {d : Lk → Ω → Ω → ℝ}
    (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm) (hDm : 0 ≤ Dm)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z))
    (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} (hcol : ∀ l, κ * Fintype.card Z ≤ ∑ z, gain (K z).S (C z) l)
    (hκ1 : κ ≤ 1) (n : ℕ) {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : LipD d f v)
    (W W' : Lk → Ω) :
    |(avgQ K)^[n] f W - (avgQ K)^[n] f W'| ≤ (1 - κ) ^ n * (∑ k, v k) * Dm := by
  obtain ⟨u, hu, hus⟩ := avg_iterD K hd0 hC hC0 hcol hκ1 n hf hv
  calc _ ≤ (∑ k, u k) * Dm := abs_sub_le_sum_lipD hD hu W W'
    _ ≤ ((1 - κ) ^ n * ∑ k, v k) * Dm := mul_le_mul_of_nonneg_right hus hDm
    _ = (1 - κ) ^ n * (∑ k, v k) * Dm := by ring

#print axioms osc_iter_le

end Generic

/-! ## 3. The Wilson block kernel -/

section Wilson

open MassGap.HeatBath (wt continuous_wt wt_pos)
open MassGap.BlockHeatBath
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq] [DecidableEq Lk]

/-- Subtraction. DERIVED: `-1` the coefficient of the subtracted function. -/
theorem blkAvg_sub (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {f g : (Lk → SU N) → ℝ}
    (hf : Continuous f) (hg : Continuous g) (W : Lk → SU N) :
    blkAvg bd β S (fun U => f U - g U) W = blkAvg bd β S f W - blkAvg bd β S g W := by
  have hg' : Continuous (fun U => (-1 : ℝ) * g U) := continuous_const.mul hg
  have h := blkAvg_add bd β S hf hg' W
  have e : (fun U => f U - g U) = (fun U => f U + (-1 : ℝ) * g U) := funext fun U => by ring
  rw [e, h, blkAvg_const_mul]
  ring

#print axioms blkAvg_sub

/-- **The block average is bounded by the fibre's supremum.**

DERIVED: no numeral. -/
theorem abs_blkAvg_le (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) {h : (Lk → SU N) → ℝ}
    (W : Lk → SU N) (B : ℝ) (hB : ∀ V, |h (glue S W V)| ≤ B) : |blkAvg bd β S h W| ≤ B := by
  unfold blkAvg
  have hp := blkPart_pos bd β S W
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have hint1 : Integrable (fun V => wt bd β (glue S W V)) (Measure.pi fun _ : Lk => probHaar (SU N)) := by
    have := integrable_glue bd β S (f := fun _ => (1 : ℝ)) continuous_const W
    simpa using this
  have hint : Integrable (fun V => B * wt bd β (glue S W V)) (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    hint1.const_mul B
  unfold blkNum blkPart
  calc |∫ V, h (glue S W V) * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N))|
      ≤ ∫ V, B * wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun V => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos bd β _)]
        exact mul_le_mul_of_nonneg_right (hB V) (wt_pos bd β _).le
    _ = B * ∫ V, wt bd β (glue S W V) ∂(Measure.pi fun _ : Lk => probHaar (SU N)) :=
        integral_const_mul _ _

#print axioms abs_blkAvg_le

/-- The block average reads `f` only on the fibre. DERIVED: no numeral. -/
theorem blkAvg_fibre (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) (f : (Lk → SU N) → ℝ)
    (W : Lk → SU N) : blkAvg bd β S (fun U => f (glue S W U)) W = blkAvg bd β S f W := by
  unfold blkAvg blkNum
  simp only [glue_glue_right]

#print axioms blkAvg_fibre

/-- **The Wilson block kernel** of the block `S`.

DERIVED: no numeral. -/
def wilsonKer (bd : Pq → List (Lk × Bool)) (β : ℝ) (S : Finset Lk) : BlockKer (SU N) Lk where
  S := S
  Q := blkAvg bd β S
  cont hf := continuous_blkAvg bd β S hf
  sub hf hg W := blkAvg_sub bd β S hf hg W
  bound _ W B hB := abs_blkAvg_le bd β S W B hB
  fibre _ W := blkAvg_fibre bd β S _ W
  reads_not f W _ hk x := blkAvg_update_mem bd β hk f W x

end Wilson

end MassGap.DSBlockContract
