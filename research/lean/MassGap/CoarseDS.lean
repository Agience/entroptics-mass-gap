import Mathlib
import MassGap.DSBlockContract

noncomputable section

/-!
# MassGap.CoarseDS — the weighted Dobrushin–Shlosman box criterion gives spatial covariance decay

`DSBlockContract` contracts the total Lipschitz vector of the averaged block dynamics `T = (1/|Z|) Σ_z Q_z` under the
column bound `κ |Z| ≤ Σ_z gain_z l`. This module gives the spatial form, the block analogue of
`DobrushinMixed.cov_spatialD`, for any family of block kernels on a finite site set that leaves a state invariant:

1. **Weighted contraction** (`gainW`, `sum_blkVecW`, `sum_avgVecW_le`, `avg_iterW`): with a weight `u ≥ 0` and the
   weighted gain `gainW_z l = u_l − Σ_{k ∉ S_z} C_z l k u_k` on the block, the weighted column bound
   `κ |Z| u_l ≤ Σ_z gainW_z l` contracts `Σ_k u_k v_k` by `1 − κ` per averaged step.
2. **Block laws and the covariance telescope** (`BlockLaw`, `fibre_osc`, `cov_blk_step`, `cov_avg_step`,
   `cov_run`): a state invariant under each block kernel, with pull-out of functions that do not read the block and
   the conditional covariance at most twice the product of the fibre oscillations; replacing `f` by `T f` in
   `σ(f g)` costs at most `(G Mult/|Z|) Σ_k u_k v_f(k)` when every block meeting the support of `g` has
   `2 (Σ_{S_z} v_g) Dm² ≤ G u_l` on its sites and every site lies in at most `Mult` blocks.
3. **The covariance bound** (`cov_le_weightedDS`): `|σ(f g) − σ f σ g| ≤ (G Mult/|Z|)/κ · Σ_k u_k v_f(k)`.
4. **Spatial decay** (`cov_spatialDS`): with `u = θ^{dist(·, B)}` and the weighted DS column gain
   `γ₀ ≤ Σ_{z ∋ l} (1 − Σ_{k ∉ S_z} C_z l k θ^{−D(l,k)})` at every site (`κ = γ₀/|Z|`), blocks of at most `Smax`
   sites and diameter `R`: `|σ(f g) − σ f σ g| ≤ 2 V_g Smax Dm² θ^{−R} Mult/γ₀ · θ^{dd+1} Σ_k v_f(k)` when `f` reads
   only sites farther than `dd` from the support `B` of `g`. For the translates of one box `V` on a torus,
   `Mult = |V|` and `γ₀ = |V|(1 − ρ_V^θ)`, so the constant does not depend on the size of the torus.

DERIVED (module-wide): `0` the signs and the block entries; `1` the gain's unit and the bound on `θ`; `2` the square of
the cost bound.
-/

namespace MassGap.CoarseDS

open MeasureTheory Filter Topology
open MassGap.DLRLimit
open MassGap.DSBlockContract (BlockKer BlkInfl blkVec blk_stepD avgQ avgVec avg_stepD continuous_avgQ
  continuous_iter_avgQ)
open MassGap.DobrushinMixed (LipD abs_sub_le_lipD_finset abs_sub_le_sum_lipD)
open MassGap.DobrushinGeneral (ex ex_mk ex_sub ex_const_mul abs_ex_le cmul csub csmul csubc)
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)
open MassGap.HeatBath (exists_abs_le)

variable {Ω : Type} [TopologicalSpace Ω] {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-! ## 1. Weighted contraction -/

section Weighted

/-- **The weighted gain at a site**: `u_l − Σ_{k ∉ S} C l k u_k` on the block, `0` off it.

DERIVED: `0` off the block. -/
def gainW (S : Finset Lk) (C : Lk → Lk → ℝ) (u : Lk → ℝ) (l : Lk) : ℝ :=
  if l ∈ S then u l - ∑ k ∈ Sᶜ, C l k * u k else 0

/-- **The weighted total of the block-step vector.**

DERIVED: no numeral. -/
theorem sum_blkVecW (S : Finset Lk) (C : Lk → Lk → ℝ) (u v : Lk → ℝ) :
    ∑ k, u k * blkVec S C v k = ∑ k, u k * v k - ∑ l, v l * gainW S C u l := by
  have h1 : ∑ k, u k * blkVec S C v k = ∑ k ∈ Sᶜ, u k * (v k + ∑ l ∈ S, C l k * v l) := by
    rw [← Finset.sum_add_sum_compl S (fun k => u k * blkVec S C v k)]
    have h0 : ∑ k ∈ S, u k * blkVec S C v k = 0 :=
      Finset.sum_eq_zero fun k hk => by simp only [blkVec, if_pos hk, mul_zero]
    rw [h0, zero_add]
    exact Finset.sum_congr rfl fun k hk => by simp only [blkVec, if_neg (Finset.mem_compl.mp hk)]
  have h2 : ∑ l, v l * gainW S C u l = ∑ l ∈ S, v l * (u l - ∑ k ∈ Sᶜ, C l k * u k) := by
    rw [← Finset.sum_add_sum_compl S (fun l => v l * gainW S C u l)]
    have h0 : ∑ l ∈ Sᶜ, v l * gainW S C u l = 0 :=
      Finset.sum_eq_zero fun l hl => by simp only [gainW, if_neg (Finset.mem_compl.mp hl), mul_zero]
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun l hl => by simp only [gainW, if_pos hl]
  have h3 : ∑ k ∈ Sᶜ, u k * ∑ l ∈ S, C l k * v l = ∑ l ∈ S, v l * ∑ k ∈ Sᶜ, C l k * u k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have h4 : ∑ k ∈ Sᶜ, u k * (v k + ∑ l ∈ S, C l k * v l)
      = ∑ k ∈ Sᶜ, u k * v k + ∑ k ∈ Sᶜ, u k * ∑ l ∈ S, C l k * v l := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h5 : ∑ l ∈ S, v l * (u l - ∑ k ∈ Sᶜ, C l k * u k)
      = ∑ l ∈ S, u l * v l - ∑ l ∈ S, v l * ∑ k ∈ Sᶜ, C l k * u k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, h4, h3, h5, ← Finset.sum_add_sum_compl S (fun k => u k * v k)]
  ring

#print axioms sum_blkVecW

variable {Z : Type} [Fintype Z]

/-- **The weighted column bound contracts the weighted total**: `κ |Z| u_l ≤ Σ_z gainW_z l` at every site gives
`Σ_k u_k avgVec_k ≤ (1 − κ) Σ_k u_k v_k`.

DERIVED: `0` the signs; `1` the contraction's unit. -/
theorem sum_avgVecW_le [Nonempty Z] (K : Z → BlockKer Ω Lk) (C : Z → Lk → Lk → ℝ) {κ : ℝ} {u : Lk → ℝ}
    (hcol : ∀ l, κ * Fintype.card Z * u l ≤ ∑ z, gainW (K z).S (C z) u l) {v : Lk → ℝ}
    (hv0 : ∀ k, 0 ≤ v k) :
    ∑ k, u k * avgVec K C v k ≤ (1 - κ) * ∑ k, u k * v k := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have e : ∑ k, u k * avgVec K C v k
      = (Fintype.card Z : ℝ)⁻¹ * ∑ z, (∑ k, u k * v k - ∑ l, v l * gainW (K z).S (C z) u l) := by
    unfold avgVec
    have : ∀ k, u k * ((Fintype.card Z : ℝ)⁻¹ * ∑ z, blkVec (K z).S (C z) v k)
        = (Fintype.card Z : ℝ)⁻¹ * ∑ z, u k * blkVec (K z).S (C z) v k := fun k => by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    simp_rw [this]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun z _ => sum_blkVecW _ _ _ _
  have e2 : ∑ z, (∑ k, u k * v k - ∑ l, v l * gainW (K z).S (C z) u l)
      = (Fintype.card Z : ℝ) * ∑ k, u k * v k - ∑ l, v l * ∑ z, gainW (K z).S (C z) u l := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
  have h3 : κ * Fintype.card Z * ∑ k, u k * v k ≤ ∑ l, v l * ∑ z, gainW (K z).S (C z) u l := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ =>
      calc κ * Fintype.card Z * (u l * v l) = v l * (κ * Fintype.card Z * u l) := by ring
        _ ≤ v l * ∑ z, gainW (K z).S (C z) u l := mul_le_mul_of_nonneg_left (hcol l) (hv0 l)
  rw [e, e2, inv_mul_le_iff₀ hZ]
  have e3 : (Fintype.card Z : ℝ) * ((1 - κ) * ∑ k, u k * v k)
      = (Fintype.card Z : ℝ) * ∑ k, u k * v k - κ * Fintype.card Z * ∑ k, u k * v k := by ring
  rw [e3]
  linarith

#print axioms sum_avgVecW_le

/-- **`n` averaged steps leave weighted total `≤ (1 − κ)ⁿ Σ u v`.**

DERIVED: `0` the signs; `1` the contraction's unit. -/
theorem avg_iterW [Nonempty Z] (K : Z → BlockKer Ω Lk) {d : Lk → Ω → Ω → ℝ}
    (hd0 : ∀ l a b, 0 ≤ d l a b) {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z))
    (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} {u : Lk → ℝ}
    (hcol : ∀ l, κ * Fintype.card Z * u l ≤ ∑ z, gainW (K z).S (C z) u l) (hκ1 : κ ≤ 1) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipD d f v →
      ∃ w : Lk → ℝ, LipD d ((avgQ K)^[n] f) w ∧ ∑ k, u k * w k ≤ (1 - κ) ^ n * ∑ k, u k * v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    have h1 := avg_stepD K hd0 hC hC0 hf hv
    obtain ⟨w, hw, hws⟩ := avg_iterW K hd0 hC hC0 hcol hκ1 n (continuous_avgQ K hf) h1
    refine ⟨w, by rwa [Function.iterate_succ_apply], ?_⟩
    have h2 := sum_avgVecW_le K C hcol hv.1
    calc ∑ k, u k * w k ≤ (1 - κ) ^ n * ∑ k, u k * avgVec K C v k := hws
      _ ≤ (1 - κ) ^ n * ((1 - κ) * ∑ k, u k * v k) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) n)
      _ = (1 - κ) ^ (n + 1) * ∑ k, u k * v k := by ring

#print axioms avg_iterW

end Weighted

/-! ## 2. Block laws and the covariance telescope -/

section Cov

variable [CompactSpace Ω] [Nonempty Ω]
variable {Z : Type} [Fintype Z]

/-- **A state invariant under a family of block kernels**, with pull-out of functions that do not read the block and
the conditional covariance bounded by the product of the fibre oscillations.

DERIVED: no numeral. -/
structure BlockLaw (K : Z → BlockKer Ω Lk) (σ : State (Lk → Ω)) : Prop where
  inv : ∀ z {h : (Lk → Ω) → ℝ}, Continuous h → ex σ ((K z).Q h) = ex σ h
  pull : ∀ z {h g : (Lk → Ω) → ℝ}, Continuous h → Continuous g →
    (∀ (U : Lk → Ω) (k : Lk) (x : Ω), k ∈ (K z).S → g (Function.update U k x) = g U) →
    ∀ W, (K z).Q (fun U => h U * g U) W = (K z).Q h W * g W
  covb : ∀ z {f g : (Lk → Ω) → ℝ}, Continuous f → Continuous g → ∀ (W : Lk → Ω) {a b : ℝ},
    (∀ V V' : Lk → Ω, |f (glue (K z).S W V) - f (glue (K z).S W V')| ≤ a) →
    (∀ V V' : Lk → Ω, |g (glue (K z).S W V) - g (glue (K z).S W V')| ≤ b) →
    |(K z).Q (fun U => f U * g U) W - (K z).Q f W * (K z).Q g W| ≤ 2 * (a * b)

theorem ex_add (σ : State (Lk → Ω)) {F G : (Lk → Ω) → ℝ} (hF : Continuous F) (hG : Continuous G) :
    ex σ (fun x => F x + G x) = ex σ F + ex σ G := by
  rw [ex_mk σ (F := fun x => F x + G x) (hF.add hG), ex_mk σ hF, ex_mk σ hG]
  exact σ.map_add ⟨F, hF⟩ ⟨G, hG⟩

theorem ex_finsum (σ : State (Lk → Ω)) (s : Finset Z) {F : Z → (Lk → Ω) → ℝ} (hF : ∀ z, Continuous (F z)) :
    ex σ (fun x => ∑ z ∈ s, F z x) = ∑ z ∈ s, ex σ (F z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [ex_mk σ continuous_const]
    exact σ.map_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [ex_add σ (hF a) (continuous_finsetSum _ fun z _ => hF z), ih]

#print axioms ex_finsum

/-- **The fibre oscillation of a Lipschitz function on a block**: `(Σ_{l ∈ S} v l) Dm`.

DERIVED: no numeral. -/
theorem fibre_osc {d : Lk → Ω → Ω → ℝ} {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm) {f : (Lk → Ω) → ℝ}
    {v : Lk → ℝ} (hv : LipD d f v) (S : Finset Lk) (W V V' : Lk → Ω) :
    |f (glue S W V) - f (glue S W V')| ≤ (∑ l ∈ S, v l) * Dm := by
  have h := abs_sub_le_lipD_finset hv (glue S W V) (glue S W V') S
  have e : (fun k => if k ∈ S then glue S W V' k else glue S W V k) = glue S W V' := by
    funext k
    by_cases hk : k ∈ S
    · rw [if_pos hk]
    · rw [if_neg hk, glue_of_not_mem hk, glue_of_not_mem hk]
  rw [e] at h
  refine h.trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hD _ _ _) (hv.1 k)

#print axioms fibre_osc

/-- **One block kernel in the covariance**: replacing `f` by `Q_z f` in `σ(f g)` costs at most
`(Σ_{S_z} v_f) Dm · (Σ_{S_z} v_g) Dm`.

DERIVED: no numeral. -/
theorem cov_blk_step {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ) (z : Z)
    {d : Lk → Ω → Ω → ℝ} {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm) {f g : (Lk → Ω) → ℝ} (hf : Continuous f)
    (hg : Continuous g) {vf vg : Lk → ℝ} (hvf : LipD d f vf) (hvg : LipD d g vg) :
    |ex σ (fun W => f W * g W) - ex σ (fun W => (K z).Q f W * g W)|
      ≤ 2 * ((∑ l ∈ (K z).S, vf l) * Dm * ((∑ l ∈ (K z).S, vg l) * Dm)) := by
  have hQf := (K z).cont hf
  have hQg := (K z).cont hg
  have i1 := hL.inv z (cmul hf hg)
  have i2 := hL.inv z (cmul hg hQf)
  have e2 : (K z).Q (fun W => g W * (K z).Q f W) = fun W => (K z).Q g W * (K z).Q f W :=
    funext fun W => hL.pull z hg hQf (fun U k x hk => (K z).reads_not f U k hk x) W
  rw [e2] at i2
  have e3 : (fun W => (K z).Q f W * g W) = fun W => g W * (K z).Q f W := funext fun W => mul_comm _ _
  rw [e3, ← i1, ← i2, ← ex_sub σ ((K z).cont (cmul hf hg)) (cmul hQg hQf)]
  refine abs_ex_le σ (csub ((K z).cont (cmul hf hg)) (cmul hQg hQf)) fun W => ?_
  have h := hL.covb z hf hg W (fibre_osc hD hvf (K z).S W) (fibre_osc hD hvg (K z).S W)
  rwa [mul_comm ((K z).Q g W)]

#print axioms cov_blk_step

/-- **The averaged step in the covariance, against a weight**: if every block has `2 (Σ_{S_z} v_g) Dm² ≤ G u_l` at
each of its sites and every site lies in at most `Mult` blocks, replacing `f` by `T f` costs at most
`(G Mult/|Z|) Σ_k u_k v_f(k)`.

DERIVED: `2` the conditional covariance. -/
theorem cov_avg_step [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ)
    {d : Lk → Ω → Ω → ℝ} {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm) {u : Lk → ℝ} {G : ℝ} (hG0 : 0 ≤ G)
    (hu0 : ∀ k, 0 ≤ u k) {Mult : ℕ} (hmult : ∀ l, (Finset.univ.filter (fun z => l ∈ (K z).S)).card ≤ Mult)
    {g : (Lk → Ω) → ℝ} (hg : Continuous g) {vg : Lk → ℝ} (hvg : LipD d g vg)
    (hG : ∀ z l, l ∈ (K z).S → 2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm) ≤ G * u l)
    {f : (Lk → Ω) → ℝ} (hf : Continuous f) {vf : Lk → ℝ} (hvf : LipD d f vf) :
    |ex σ (fun W => f W * g W) - ex σ (fun W => avgQ K f W * g W)|
      ≤ G * Mult / Fintype.card Z * ∑ k, u k * vf k := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  set c : ℝ := (Fintype.card Z : ℝ)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hcZ : c * Fintype.card Z = 1 := by rw [hc]; field_simp
  have e1 : ex σ (fun W => avgQ K f W * g W) = c * ∑ z, ex σ (fun W => (K z).Q f W * g W) := by
    have : (fun W => avgQ K f W * g W) = fun W => c * ∑ z, (K z).Q f W * g W := by
      funext W
      unfold avgQ
      rw [mul_assoc, Finset.sum_mul]
    rw [this, ex_const_mul σ c (continuous_finsetSum _ fun z _ => cmul ((K z).cont hf) hg),
      ex_finsum σ Finset.univ (fun z => cmul ((K z).cont hf) hg)]
  have e0 : ex σ (fun W => f W * g W) = c * ∑ _z : Z, ex σ (fun W => f W * g W) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcZ, one_mul]
  rw [e1, e0, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hc0]
  have hstep : ∀ z, |ex σ (fun W => f W * g W) - ex σ (fun W => (K z).Q f W * g W)|
      ≤ ∑ l ∈ (K z).S, G * (u l * vf l) := by
    intro z
    refine (cov_blk_step hL z hD hf hg hvf hvg).trans ?_
    have h1 : 2 * ((∑ l ∈ (K z).S, vf l) * Dm * ((∑ l ∈ (K z).S, vg l) * Dm))
        = ∑ l ∈ (K z).S, vf l * (2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm)) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h1]
    exact Finset.sum_le_sum fun l hl => by
      have := mul_le_mul_of_nonneg_left (hG z l hl) (hvf.1 l)
      linarith
  have hswap : ∑ z, ∑ l ∈ (K z).S, G * (u l * vf l)
      = ∑ l, G * (u l * vf l) * (Finset.univ.filter (fun z => l ∈ (K z).S)).card := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun l => Finset.univ.filter (fun z => l ∈ (K z).S))]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    · intro z l; simp
  calc c * |∑ z, (ex σ (fun W => f W * g W) - ex σ (fun W => (K z).Q f W * g W))|
      ≤ c * ∑ z, ∑ l ∈ (K z).S, G * (u l * vf l) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun z _ => hstep z)) hc0
    _ = c * ∑ l, G * (u l * vf l) * (Finset.univ.filter (fun z => l ∈ (K z).S)).card := by rw [hswap]
    _ ≤ c * ∑ l, G * (u l * vf l) * Mult := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hc0
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmult l)
          (mul_nonneg hG0 (mul_nonneg (hu0 l) (hvf.1 l)))
    _ = G * Mult / Fintype.card Z * ∑ k, u k * vf k := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [hc]; ring

#print axioms cov_avg_step

/-- **The covariance telescope along the averaged dynamics**: `n` averaged steps cost at most
`(G Mult/|Z|)/κ · Σ_k u_k v_f(k)` in total (the weighted total contracts by `1 − κ` per step).

DERIVED: `0` the empty run; `1` the contraction's unit. -/
theorem cov_run [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hD : ∀ l a b, d l a b ≤ Dm)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z)) (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} {u : Lk → ℝ}
    (hu0 : ∀ k, 0 ≤ u k) (hcol : ∀ l, κ * Fintype.card Z * u l ≤ ∑ z, gainW (K z).S (C z) u l) (hκ0 : 0 < κ)
    {G : ℝ} (hG0 : 0 ≤ G) {Mult : ℕ} (hmult : ∀ l, (Finset.univ.filter (fun z => l ∈ (K z).S)).card ≤ Mult)
    {g : (Lk → Ω) → ℝ} (hg : Continuous g) {vg : Lk → ℝ} (hvg : LipD d g vg)
    (hG : ∀ z l, l ∈ (K z).S → 2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm) ≤ G * u l) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, LipD d f v →
      |ex σ (fun W => f W * g W) - ex σ (fun W => (avgQ K)^[n] f W * g W)|
        ≤ G * Mult / Fintype.card Z / κ * ∑ k, u k * v k
  | 0, f, hf, v, hv => by
    simp only [Function.iterate_zero, id, sub_self, abs_zero]
    refine mul_nonneg (div_nonneg (div_nonneg (mul_nonneg hG0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hκ0.le)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hu0 k) (hv.1 k))
  | n + 1, f, hf, v, hv => by
    have hG1 : 0 ≤ G * Mult / Fintype.card Z := div_nonneg (mul_nonneg hG0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have h1 := cov_avg_step hL hD hG0 hu0 hmult hg hvg hG hf hv
    have hA := avg_stepD K hd0 hC hC0 hf hv
    have h2 := cov_run hL hd0 hD hC hC0 hu0 hcol hκ0 hG0 hmult hg hvg hG n (continuous_avgQ K hf) hA
    have h3 := sum_avgVecW_le K C hcol hv.1
    rw [Function.iterate_succ_apply]
    calc _ ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => avgQ K f W * g W)|
          + |ex σ (fun W => avgQ K f W * g W) - ex σ (fun W => (avgQ K)^[n] (avgQ K f) W * g W)| :=
          abs_sub_le _ _ _
      _ ≤ G * Mult / Fintype.card Z * ∑ k, u k * v k
          + G * Mult / Fintype.card Z / κ * ∑ k, u k * avgVec K C v k := add_le_add h1 h2
      _ ≤ G * Mult / Fintype.card Z * ∑ k, u k * v k
          + G * Mult / Fintype.card Z / κ * ((1 - κ) * ∑ k, u k * v k) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 (div_nonneg hG1 hκ0.le))
      _ = G * Mult / Fintype.card Z / κ * ∑ k, u k * v k := by field_simp; ring

#print axioms cov_run

theorem ex_const (σ : State (Lk → Ω)) (c : ℝ) : ex σ (fun _ => c) = c := by
  rw [ex_mk σ continuous_const]
  have : (⟨fun _ => c, continuous_const⟩ : C(Lk → Ω, ℝ)) = c • (1 : C(Lk → Ω, ℝ)) := by
    ext; simp
  rw [this, σ.map_smul, σ.map_one, mul_one]

/-- **The averaged dynamics leaves the state invariant.**

DERIVED: `1` the normalisation. -/
theorem ex_avgQ [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ)
    {h : (Lk → Ω) → ℝ} (hh : Continuous h) : ex σ (avgQ K h) = ex σ h := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have e : avgQ K h = fun W => (Fintype.card Z : ℝ)⁻¹ * ∑ z, (K z).Q h W := rfl
  rw [e, ex_const_mul σ _ (continuous_finsetSum _ fun z _ => (K z).cont hh),
    ex_finsum σ Finset.univ (fun z => (K z).cont hh)]
  simp_rw [hL.inv _ hh]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

theorem ex_iter_avgQ [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ) :
    ∀ (n : ℕ) {h : (Lk → Ω) → ℝ}, Continuous h → ex σ ((avgQ K)^[n] h) = ex σ h
  | 0, _, _ => rfl
  | n + 1, h, hh => by
    rw [Function.iterate_succ_apply, ex_iter_avgQ hL n (continuous_avgQ K hh), ex_avgQ hL hh]

#print axioms ex_iter_avgQ

/-- **The Dobrushin–Shlosman covariance bound against a weight.** A state invariant under block kernels with
influences `C ≥ 0`, a weight `u ≥ umin > 0` with the weighted column bound, every site in at most `Mult` blocks, and
`2 (Σ_{S_z} v_g) Dm² ≤ G u_l` on every block: `|σ(f g) − σ f σ g| ≤ (G Mult/|Z|)/κ · Σ_k u_k v_f(k)`. (The factor `2`
is the conditional covariance bound `2 a b` for fibre oscillations `a`, `b`.)

DERIVED: `0` the sign of `1 − κ` and the limit of `(1 − κ)ⁿ`; `1` the bound on `κ`. -/
theorem cov_le_weightedDS [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm) (hD : ∀ l a b, d l a b ≤ Dm)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z)) (hC0 : ∀ z l k, 0 ≤ C z l k) {κ : ℝ} {u : Lk → ℝ}
    {umin : ℝ} (humin : 0 < umin) (hu : ∀ k, umin ≤ u k)
    (hcol : ∀ l, κ * Fintype.card Z * u l ≤ ∑ z, gainW (K z).S (C z) u l) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {G : ℝ} (hG0 : 0 ≤ G) {Mult : ℕ} (hmult : ∀ l, (Finset.univ.filter (fun z => l ∈ (K z).S)).card ≤ Mult)
    {g : (Lk → Ω) → ℝ} (hg : Continuous g) {vg : Lk → ℝ} (hvg : LipD d g vg)
    (hG : ∀ z l, l ∈ (K z).S → 2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm) ≤ G * u l)
    {f : (Lk → Ω) → ℝ} (hf : Continuous f) {vf : Lk → ℝ} (hvf : LipD d f vf) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g| ≤ G * Mult / Fintype.card Z / κ * ∑ k, u k * vf k := by
  have hu0 : ∀ k, 0 ≤ u k := fun k => humin.le.trans (hu k)
  obtain ⟨Bg, hBg⟩ := exists_abs_le hg
  set X := ∑ k, u k * vf k with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => mul_nonneg (hu0 k) (hvf.1 k)
  have hn : ∀ n : ℕ, |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ G * Mult / Fintype.card Z / κ * X + (1 - κ) ^ n * X / umin * Dm * Bg := by
    intro n
    have h1 := cov_run hL hd0 hD hC hC0 hu0 hcol hκ0 hG0 hmult hg hvg hG n hf hvf
    obtain ⟨w, hw, hws⟩ := avg_iterW K hd0 hC hC0 hcol hκ1 n hf hvf
    have hc := continuous_iter_avgQ K n hf
    have hwsum : ∑ k, w k ≤ (1 - κ) ^ n * X / umin := by
      rw [le_div_iff₀ humin]
      calc (∑ k, w k) * umin = ∑ k, umin * w k := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ ∑ k, u k * w k := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hu k) (hw.1 k)
        _ ≤ (1 - κ) ^ n * X := hws
    have hosc : ∀ W, |(avgQ K)^[n] f W - ex σ f| ≤ (1 - κ) ^ n * X / umin * Dm := by
      intro W
      have hinv := ex_iter_avgQ hL n hf
      have hb : ∀ V, |(avgQ K)^[n] f V - (avgQ K)^[n] f W| ≤ (1 - κ) ^ n * X / umin * Dm := fun V =>
        (abs_sub_le_sum_lipD hD hw V W).trans (mul_le_mul_of_nonneg_right hwsum hDm)
      have he := abs_ex_le σ (csubc hc ((avgQ K)^[n] f W)) hb
      rw [ex_sub σ hc continuous_const, ex_const, hinv] at he
      rwa [abs_sub_comm] at he
    have e : ex σ (fun W => (avgQ K)^[n] f W * g W) - ex σ f * ex σ g
        = ex σ (fun W => ((avgQ K)^[n] f W - ex σ f) * g W) := by
      have e1 : (fun W => ((avgQ K)^[n] f W - ex σ f) * g W)
          = fun W => (avgQ K)^[n] f W * g W - ex σ f * g W := funext fun W => by ring
      rw [e1, ex_sub σ (F := fun W => (avgQ K)^[n] f W * g W) (G := fun W => ex σ f * g W) (cmul hc hg)
        (csmul _ hg), ex_const_mul σ _ hg]
    have h4 : |ex σ (fun W => (avgQ K)^[n] f W * g W) - ex σ f * ex σ g|
        ≤ (1 - κ) ^ n * X / umin * Dm * Bg := by
      rw [e]
      refine abs_ex_le σ (cmul (csubc hc (ex σ f)) hg) fun W => ?_
      rw [abs_mul]
      exact mul_le_mul (hosc W) (hBg W) (abs_nonneg _)
        (mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg (by linarith) n) hX0) humin.le) hDm)
    calc _ ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => (avgQ K)^[n] f W * g W)|
          + |ex σ (fun W => (avgQ K)^[n] f W * g W) - ex σ f * ex σ g| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h4
  have ht : Tendsto (fun n : ℕ => G * Mult / Fintype.card Z / κ * X + (1 - κ) ^ n * X / umin * Dm * Bg) atTop
      (𝓝 (G * Mult / Fintype.card Z / κ * X + 0 * X / umin * Dm * Bg)) :=
    (((((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const X).div_const
      umin).mul_const Dm).mul_const Bg).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weightedDS

/-- **Spatial decay under the weighted Dobrushin–Shlosman column bound.** For a site distance `Dst` (triangle
inequality), `0 < θ ≤ 1`, block kernels with influences `C ≥ 0`, the weighted column gain
`γ₀ ≤ Σ_z [l ∈ S_z] (1 − Σ_{k ∉ S_z} C_z l k θ^{−D(l,k)})` at every site (`0 < γ₀ ≤ |Z|`), every site in at most
`Mult` blocks, blocks of at most `Smax` sites and diameter `≤ R`: if `g` has vector `≤ V_g` on `B` and `0` off it,
and `f` reads only sites farther than `dd` from `B`, then
`|σ(f g) − σ f σ g| ≤ 2 V_g Smax Dm² θ^{−R} Mult/γ₀ · θ^{dd+1} Σ_k v_f(k)`. For the translates of one box `V` on a
torus, `Mult = |V|` and `γ₀ = |V| (1 − ρ_V^θ)`: the constant does not depend on the size of the torus.

DERIVED: `0` the sign and the vectors off the supports; `1` the bound on `θ` and the step beyond `dd`; `2` the
square of the cost bound and the conditional covariance. -/
theorem cov_spatialDS [Nonempty Z] {K : Z → BlockKer Ω Lk} {σ : State (Lk → Ω)} (hL : BlockLaw K σ)
    {d : Lk → Ω → Ω → ℝ} (hd0 : ∀ l a b, 0 ≤ d l a b) {Dm : ℝ} (hDm : 0 ≤ Dm) (hD : ∀ l a b, d l a b ≤ Dm)
    {C : Z → Lk → Lk → ℝ} (hC : ∀ z, BlkInfl (K z) d (C z)) (hC0 : ∀ z l k, 0 ≤ C z l k)
    (Dst : Lk → Lk → ℕ) (hDt : ∀ a b c, Dst a c ≤ Dst a b + Dst b c)
    {θ γ₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hγ0 : 0 < γ₀) (hγZ : γ₀ ≤ Fintype.card Z)
    (hDS : ∀ l, γ₀ ≤ ∑ z, (if l ∈ (K z).S then 1 - ∑ k ∈ (K z).Sᶜ, C z l k / θ ^ Dst l k else 0))
    {Mult Smax R : ℕ} (hmult : ∀ l, (Finset.univ.filter (fun z => l ∈ (K z).S)).card ≤ Mult)
    (hS : ∀ z, ((K z).S).card ≤ Smax) (hR : ∀ z, ∀ l ∈ (K z).S, ∀ m ∈ (K z).S, Dst l m ≤ R)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : LipD d f vf) (hvg : LipD d g vg) (B : Finset Lk) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg) (dd : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → ∀ b ∈ B, dd < Dst k b) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ 2 * Vg * Smax * Dm ^ 2 / θ ^ R * Mult / γ₀ * (θ ^ (dd + 1) * ∑ k, vf k) := by
  have hZ : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = γ₀ / Fintype.card Z := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; exact div_pos hγ0 hZ
  have hκ1 : κ ≤ 1 := by rw [hκdef, div_le_one hZ]; exact hγZ
  have hκZ : κ * Fintype.card Z = γ₀ := by rw [hκdef]; field_simp
  obtain ⟨ψ, hψd⟩ : ∃ ψ : Lk → ℕ, ∀ k,
      ψ k = if h : B.Nonempty then B.inf' h (fun b => Dst k b) else dd + 1 := ⟨_, fun _ => rfl⟩
  have hψ : ∀ l k, ψ l ≤ ψ k + Dst l k := by
    intro l k
    rw [hψd l, hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h, dif_pos h]
      obtain ⟨b, hb, hbk⟩ := Finset.exists_mem_eq_inf' h (fun b => Dst k b)
      rw [hbk]
      calc B.inf' h (fun b => Dst l b) ≤ Dst l b := Finset.inf'_le _ hb
        _ ≤ Dst l k + Dst k b := hDt l k b
        _ = Dst k b + Dst l k := add_comm _ _
    · rw [dif_neg h, dif_neg h]
      omega
  have hψle : ∀ l, ∀ b ∈ B, ψ l ≤ Dst l b := by
    intro l b hb
    rw [hψd l, dif_pos ⟨b, hb⟩]
    exact Finset.inf'_le _ hb
  have hψfar : ∀ k, vf k ≠ 0 → dd + 1 ≤ ψ k := by
    intro k hk
    rw [hψd k]
    by_cases h : B.Nonempty
    · rw [dif_pos h]
      exact Finset.le_inf' h _ fun b hb => hfar k hk b hb
    · rw [dif_neg h]
  have hθ0' : 0 ≤ θ := hθ0.le
  have hu0 : ∀ k, 0 ≤ θ ^ ψ k := fun k => pow_nonneg hθ0' _
  obtain ⟨Nψ, hNψ⟩ : ∃ Nψ : ℕ, ∀ k, ψ k ≤ Nψ :=
    ⟨∑ k, ψ k, fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)⟩
  have humin : 0 < θ ^ Nψ := pow_pos hθ0 _
  have hu_ge : ∀ k, θ ^ Nψ ≤ θ ^ ψ k := fun k => pow_le_pow_of_le_one hθ0' hθ1 (hNψ k)
  -- the weighted column bound
  have hcol : ∀ l, κ * Fintype.card Z * θ ^ ψ l ≤ ∑ z, gainW (K z).S (C z) (fun k => θ ^ ψ k) l := by
    intro l
    have hz : ∀ z, θ ^ ψ l * (if l ∈ (K z).S then 1 - ∑ k ∈ (K z).Sᶜ, C z l k / θ ^ Dst l k else 0)
        ≤ gainW (K z).S (C z) (fun k => θ ^ ψ k) l := by
      intro z
      unfold gainW
      split_ifs with hl
      · rw [mul_sub, mul_one, Finset.mul_sum]
        have : ∑ k ∈ (K z).Sᶜ, C z l k * θ ^ ψ k ≤ ∑ k ∈ (K z).Sᶜ, θ ^ ψ l * (C z l k / θ ^ Dst l k) :=
          Finset.sum_le_sum fun k _ => by
            have hp : 0 < θ ^ Dst l k := pow_pos hθ0 _
            have hpow : θ ^ ψ k * θ ^ Dst l k ≤ θ ^ ψ l := by
              rw [← pow_add]; exact pow_le_pow_of_le_one hθ0' hθ1 (hψ l k)
            rw [mul_div_assoc', le_div_iff₀ hp]
            calc C z l k * θ ^ ψ k * θ ^ Dst l k = C z l k * (θ ^ ψ k * θ ^ Dst l k) := by ring
              _ ≤ C z l k * θ ^ ψ l := mul_le_mul_of_nonneg_left hpow (hC0 z l k)
              _ = θ ^ ψ l * C z l k := by ring
        linarith
      · simp
    calc κ * Fintype.card Z * θ ^ ψ l = θ ^ ψ l * γ₀ := by rw [hκZ]; ring
      _ ≤ θ ^ ψ l * ∑ z, (if l ∈ (K z).S then 1 - ∑ k ∈ (K z).Sᶜ, C z l k / θ ^ Dst l k else 0) :=
          mul_le_mul_of_nonneg_left (hDS l) (hu0 l)
      _ = ∑ z, θ ^ ψ l * (if l ∈ (K z).S then 1 - ∑ k ∈ (K z).Sᶜ, C z l k / θ ^ Dst l k else 0) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ z, gainW (K z).S (C z) (fun k => θ ^ ψ k) l := Finset.sum_le_sum fun z _ => hz z
  -- the block bound on the support of `g`
  have hθR : 0 < θ ^ R := pow_pos hθ0 _
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 2 * Vg * Smax * Dm ^ 2 / θ ^ R := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hVg) (Nat.cast_nonneg _)) (sq_nonneg _))
      hθR.le
  have hG : ∀ z l, l ∈ (K z).S → 2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm) ≤ G * θ ^ ψ l := by
    intro z l hl
    by_cases hb : ∃ b ∈ (K z).S, b ∈ B
    · obtain ⟨b, hbS, hbB⟩ := hb
      have hul : θ ^ R ≤ θ ^ ψ l :=
        pow_le_pow_of_le_one hθ0' hθ1 ((hψle l b hbB).trans (hR z l hl b hbS))
      have hsum : ∑ m ∈ (K z).S, vg m ≤ Smax * Vg := by
        calc ∑ m ∈ (K z).S, vg m ≤ ∑ _m ∈ (K z).S, Vg := Finset.sum_le_sum fun m _ => hgV m
          _ = (K z).S.card * Vg := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ Smax * Vg := mul_le_mul_of_nonneg_right (by exact_mod_cast hS z) hVg
      calc 2 * ((∑ m ∈ (K z).S, vg m) * Dm * Dm) ≤ 2 * (Smax * Vg * Dm * Dm) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hDm) hDm) zero_le_two
        _ = G * θ ^ R := by rw [hGdef, div_mul_cancel₀ _ hθR.ne']; ring
        _ ≤ G * θ ^ ψ l := mul_le_mul_of_nonneg_left hul hG0
    · push_neg at hb
      have h0 : ∑ m ∈ (K z).S, vg m = 0 := Finset.sum_eq_zero fun m hm => hgB m (hb m hm)
      rw [h0, zero_mul, zero_mul, mul_zero]
      exact mul_nonneg hG0 (hu0 l)
  have h := cov_le_weightedDS hL hd0 hDm hD hC hC0 humin hu_ge hcol hκ0 hκ1 hG0 hmult hg hvg hG hf hvf
  have e : G * Mult / Fintype.card Z / κ = 2 * Vg * Smax * Dm ^ 2 / θ ^ R * Mult / γ₀ := by
    rw [hGdef, hκdef]; field_simp
  rw [e] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : vf k = 0
    · rw [hk]; simp
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0' hθ1 (hψfar k hk)) (hvf.1 k)
  · rw [← e]
    exact div_nonneg (div_nonneg (mul_nonneg hG0 (Nat.cast_nonneg _)) hZ.le) hκ0.le

#print axioms cov_spatialDS

end Cov

end MassGap.CoarseDS
