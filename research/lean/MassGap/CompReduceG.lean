import Mathlib
import MassGap.ClayWiringG
import MassGap.CompReduce

/-!
# MassGap.CompReduceG — the tensor-sector clauses from the composites clauses, over `G`

The mirror of `CompReduce` over a schedule `S` of a `GaugeGroup G`. An index map `e : Idx4 → C.Ix`
with `C.cl (e α)` the monomial `Re tr F_{α₀α₁} F_{α₂α₃}` and
`(C.ren k (e α)).1 = ∑_b M k α b • (op b).1` at every step makes the lattice reading of the sector a
finite combination of composite readings:

`latTG S ρ k F = ∑_{α : ι → Idx4} (∏ᵢ cᵢ(αᵢ)) · latCG S C k ((e αᵢ, fᵢ))ᵢ` (`latTG_expand`).

| `CompReduce` (`SU(N)`) | here (any `G`, `S`) | input it reads |
|---|---|---|
| `latT_expand`, `contT_expand` | `latTG_expand`, `contTG_expand` | `ConvCG` (the second) |
| `sepConv_of_comp`, `os1Sep_of_comp`, `os0Sep_of_comp` | `sepConvG_of_comp`, `os1SepG_of_comp`, `os0SepG_of_comp` | `ConvCG`, `OS1CG`, `OS0CG` |
| `e_injective` | `e_injectiveG` | none |
| `adm_abPot`, `cval_abPot` | `adm_abPotG`, `cval_abPotG` | `∀ a : ℝ, lieGen (a • H)` (the first) |
| `tensorNondeg_of_comp` | `tensorNondegG_of_comp` | `ConvCG`, `CompNondegG`, `AbelianGenG G` |
| `tensorCov_of_comp` | `tensorCovG_of_comp` | `ConvCG`, `CovCG`, `hrep` |

The group-free parts of `CompReduce` (`adm_relabel`, `l1_nonneg`, `le_abs_bound`, `quadC`,
`exists_quadC_ne`, `lin`, `abPot`, `mcomm_smul_self`, `covDF_nil`, `covDF_one`, `onShell_abPot`,
`sepBy_symm`) are used as they are; `abPot` is read at `d = GaugeGroup.dim G`.

## The abelian test potential

At `SU(N)` the test potential of `tensorNondeg_of_comp` is `A_μ(x) = (½ ∑_ν x_ν v_{νμ}) · H` at
`H = diag(1, −1, 0, …)`, and `GPot.Adm` holds since every real multiple of `H` is Hermitian and
traceless. Over `G` admissibility is `GaugeLie.lieGen` of every value, a predicate entered per
instance; `GaugeLie` states no closure of `lieGen` under real multiples and no non-zero element. So
the potential's generator is an input, `AbelianGenG G`: some `H` with `lieGen (a • H)` for every real
`a` and `Re tr H² ≠ 0`. On that potential `cval (Re tr F_{α₀α₁} F_{α₂α₃}) = Re tr H² · v_{α₀α₁}
v_{α₂α₃}` (`cval_abPotG`); at `SU(N)`, `Re tr H² = 2`.

DERIVED (module-wide): `0`, `1`, `2`, `3` the tensor slots, the unit values and the vanishing
values; `2` the half in the potential and the pair count; `4` the dimension.
-/

noncomputable section

namespace MassGap.CompReduceG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.CompReduce Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## 1. Smearing is linear in the field -/

/-- **Smearing a finite combination of fields** is the combination of the smeared fields.

DERIVED: `4` the cell-volume exponent. -/
theorem smear_sum_smulG {a : ℝ} (ha : 0 < a) {B : Type} (s : Finset B) (c : B → ℝ)
    (F : B → C(IConf G, ℝ)) (f : TestFn) :
    smear a (∑ b ∈ s, c b • F b) f = ∑ b ∈ s, c b • smear a (F b) f := by
  obtain ⟨R, M, hf⟩ := f.2
  have e : ∀ b, smear a (F b) f
      = ∑ x ∈ box ⌈R / a⌉₊, (a ^ 4 * f.1 (site a x)) • transObs x (F b) :=
    fun b => smear_eq_sum ha (F b) f hf (Finset.Subset.refl _)
  rw [smear_eq_sum ha _ f hf (Finset.Subset.refl _)]
  simp only [e, map_sum, map_smul, Finset.smul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => smul_comm _ _ _)

/-! ## 2. The sector reading as a combination of composite readings -/

/-- The smeared connected basis field `op b − ν_k(op b)` at step `k`. DERIVED: no numeral. -/
def sfG (S : Sched G) (ρ : RenormMixG G) (k : ℕ) (b : ρ.B) (f : TestFn) : C(IConf G, ℝ) :=
  smear (S.a k) ((ρ.op b).sub (S.ν k (ρ.op b).1)).1 f

/-- The sector reading as the state of a product of sums. DERIVED: no numeral. -/
theorem latTG_eq_state (S : Sched G) (ρ : RenormMixG G) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) :
    latTG S ρ k F = S.ν k (∏ i, ∑ b, mixCG ρ k (F i).1 b • sfG S ρ k b (F i).2) := by
  rw [Fintype.prod_sum, (S.ν k).map_sum]
  unfold latTG
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prod_smul_eq, (S.ν k).map_smul]
  rfl

/-- The mixing coefficients of `c` regrouped by tensor component. DERIVED: no numeral. -/
theorem sum_mixCG_smul (ρ : RenormMixG G) (k : ℕ) (c : Idx4 → ℝ) (F : ρ.B → C(IConf G, ℝ)) :
    ∑ b, mixCG ρ k c b • F b = ∑ α, c α • ∑ b, ρ.M k α b • F b := by
  unfold mixCG
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- **The smeared connected composite `e α`** is the mixing combination of the smeared connected
basis fields. DERIVED: no numeral. -/
theorem smear_cFieldG (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ) (α : Idx4)
    (f : TestFn) :
    smear (S.a k) (cFieldG S C k (e α, f)).1.1 f = ∑ b, ρ.M k α b • sfG S ρ k b f := by
  have h : (cFieldG S C k (e α, f)).1.1
      = ∑ b, ρ.M k α b • ((ρ.op b).sub (S.ν k (ρ.op b).1)).1 := by
    show (C.ren k (e α)).1 - S.ν k (C.ren k (e α)).1 • (1 : C(IConf G, ℝ)) = _
    rw [hren k α, (S.ν k).map_sum]
    simp only [(S.ν k).map_smul]
    show _ = ∑ b, ρ.M k α b • ((ρ.op b).1 - S.ν k (ρ.op b).1 • (1 : C(IConf G, ℝ)))
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
  rw [h, smear_sum_smulG (S.a_pos k)]
  rfl

/-- **The sector reading at step `k`** is `∑_α (∏ᵢ cᵢ(αᵢ)) · latCG k ((e αᵢ, fᵢ))ᵢ`.

DERIVED: no numeral. -/
theorem latTG_expand (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : ι → TDatum) :
    latTG S ρ k F = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i))
      * latCG S C k (fun i => (e (α i), (F i).2)) := by
  rw [latTG_eq_state]
  have h : ∀ i, ∑ b, mixCG ρ k (F i).1 b • sfG S ρ k b (F i).2
      = ∑ β, (F i).1 β • smear (S.a k) (cFieldG S C k (e β, (F i).2)).1.1 (F i).2 := by
    intro i
    rw [sum_mixCG_smul]
    exact Finset.sum_congr rfl fun β _ => by rw [smear_cFieldG S ρ C e hren k β (F i).2]
  rw [Finset.prod_congr rfl fun i _ => h i, Fintype.prod_sum, (S.ν k).map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [prod_smul_eq, (S.ν k).map_smul]
  rfl

/-- **The sector's lattice sequence converges on an admissible family**, from `ConvCG`.

DERIVED: no numeral. -/
theorem tendsto_latTG (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    Tendsto (fun k => latTG S ρ k F) (ultra : Filter ℕ)
      (𝓝 (∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * contCG S C (fun i => (e (α i), (F i).2)))) := by
  have e1 : (fun k => latTG S ρ k F) = fun k => ∑ α : ι → Idx4, (∏ i, (F i).1 (α i))
      * latCG S C k (fun i => (e (α i), (F i).2)) :=
    funext fun k => latTG_expand S ρ C e hren k F
  rw [e1]
  exact tendsto_finsetSum _ fun α _ =>
    (hconv ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _)).const_mul _

/-- **The sector's value on an admissible family** is `∑_α (∏ᵢ cᵢ(αᵢ)) · contCG ((e αᵢ, fᵢ))ᵢ`.

DERIVED: no numeral. -/
theorem contTG_expand (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    contTG S ρ F
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * contCG S C (fun i => (e (α i), (F i).2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold contTG
  exact (tendsto_latTG S ρ C e hren hconv F hF).limUnder_eq

/-! ## 3. `SepConvG`, `OS1SepG`, `OS0SepG` -/

/-- **`SepConvG` from `ConvCG`** and the index map. DERIVED: no numeral. -/
theorem sepConvG_of_comp (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C) :
    SepConvG S ρ := by
  intro ι _ _ F hF
  rw [contTG_expand S ρ C e hren hconv F hF]
  exact tendsto_latTG S ρ C e hren hconv F hF

/-- **`OS1SepG` from `ConvCG`, `OS1CG`** and the index map. DERIVED: no numeral. -/
theorem os1SepG_of_comp (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    (h1 : OS1CG S C) : OS1SepG S ρ := by
  intro ι _ _ F hF v
  rw [contTG_expand S ρ C e hren hconv F hF]
  refine (tendsto_finsetSum _ fun α _ =>
    (h1 ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _) v).const_mul
      (∏ i, (F i).1 (α i))).congr fun k => ?_
  rw [latTG_expand S ρ C e hren k]
  rfl

/-- **`OS0SepG` from `ConvCG`, `OS0CG`** and the index map, with constants `|α|`,
`|γ| · ∑_α |Cc (e α)|`, `β`, `∑_α |κ (e α)|`.

DERIVED: `0` the signs; `1` the top of the separation. -/
theorem os0SepG_of_comp (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    (h0 : OS0CG S C) : OS0SepG S ρ := by
  obtain ⟨A, γ, β, Cc, κ, hb⟩ := h0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ a, κ (e a) ≤ K :=
    ⟨∑ α, |κ (e α)|, fun a => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun α => |κ (e α)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ a))⟩
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, ∀ a, |Cc (e a)| ≤ Cm :=
    ⟨∑ α, |Cc (e α)|, fun a => Finset.single_le_sum (f := fun α => |Cc (e α)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)⟩
  refine ⟨|A|, |γ| * Cm, β, K, fun n F d hd hd1 hc hs => ?_⟩
  have hXY : ∀ (a : Idx4) (f : TestFn),
      |Cc (e a) * (d ^ κ (e a))⁻¹ * l1 f| ≤ Cm * (d ^ K)⁻¹ * l1 f := by
    intro a f
    have hpa : 0 < d ^ κ (e a) := Real.rpow_pos_of_pos hd _
    have hpK : 0 < d ^ K := Real.rpow_pos_of_pos hd _
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hpa, abs_of_nonneg (l1_nonneg f)]
    have h4 : (d ^ κ (e a))⁻¹ ≤ (d ^ K)⁻¹ :=
      inv_anti₀ hpK (Real.rpow_le_rpow_of_exponent_ge hd hd1 (hK a))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hCm a) h4 (inv_nonneg.mpr hpa.le) ((abs_nonneg _).trans (hCm a)))
      (l1_nonneg f)
  have hterm : ∀ α : Fin n → Idx4, |contCG S C (fun i => (e (α i), (F i).2))|
      ≤ |A| * |γ| ^ n * (n.factorial : ℝ) ^ β * ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2) := fun α =>
    le_abs_bound (X := fun i => Cc (e (α i)) * (d ^ κ (e (α i)))⁻¹ * l1 (F i).2)
      (hb n (fun i => (e (α i), (F i).2)) d hd hd1 (fun i => hc i) (fun i j hij => hs i j hij))
      (fun i => hXY (α i) (F i).2)
  rw [contTG_expand S ρ C e hren hconv F ⟨hc, d, hd, hs⟩]
  have hp : ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2) = (Cm * (d ^ K)⁻¹) ^ n * ∏ i, l1 (F i).2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hq : ∏ i, (cnorm (F i).1 * l1 (F i).2) = (∏ i, cnorm (F i).1) * ∏ i, l1 (F i).2 :=
    Finset.prod_mul_distrib
  have hr : (d ^ (K * n))⁻¹ = ((d ^ K)⁻¹) ^ n := by rw [Real.rpow_mul_natCast hd.le, inv_pow]
  calc |∑ α : Fin n → Idx4, (∏ i, (F i).1 (α i)) * contCG S C (fun i => (e (α i), (F i).2))|
      ≤ ∑ α : Fin n → Idx4,
          |(∏ i, (F i).1 (α i)) * contCG S C (fun i => (e (α i), (F i).2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : Fin n → Idx4, (∏ i, |(F i).1 (α i)|)
          * (|A| * |γ| ^ n * (n.factorial : ℝ) ^ β * ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2)) :=
        Finset.sum_le_sum fun α _ => by
          rw [abs_mul, Finset.abs_prod]
          exact mul_le_mul_of_nonneg_left (hterm α) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = (∏ i, cnorm (F i).1)
          * (|A| * |γ| ^ n * (n.factorial : ℝ) ^ β * ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact (Fintype.prod_sum (fun i j => |(F i).1 j|)).symm
    _ = |A| * (|γ| * Cm) ^ n * (n.factorial : ℝ) ^ β * (d ^ (K * n))⁻¹
          * ∏ i, (cnorm (F i).1 * l1 (F i).2) := by
        rw [hp, hq, hr, mul_pow, mul_pow]
        ring

/-! ## 4. The index map is injective -/

/-- **`e` is injective**: `C.cl (e α)` determines `α`. DERIVED: `0`–`3` the slots. -/
theorem e_injectiveG (C : CompositesG G) (e : Idx4 → C.Ix)
    (he : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)]) :
    Function.Injective e := by
  intro α β h
  have h1 := congrArg C.cl h
  rw [he, he] at h1
  clear he h
  simp at h1
  funext i
  fin_cases i <;> simp_all

/-! ## 5. The abelian potential over `G` -/

section Potential

variable (G) in
/-- **An abelian generator of the plaquette representation's Lie algebra**: a `d × d` matrix `H`
whose every real multiple is in `lieGen`, with `Re tr H² ≠ 0`.

DERIVED: `0` the excluded trace; `2` the square. -/
def AbelianGenG [GaugeSimple G] [GaugeLie G] : Prop :=
  ∃ H : Fin (GaugeGroup.dim G) → Fin (GaugeGroup.dim G) → ℂ,
    (∀ a : ℝ, GaugeLie.lieGen (G := G) (Matrix.of (a • H)))
      ∧ (Matrix.trace (Matrix.of H * Matrix.of H)).re ≠ 0

/-- **The abelian potential at a generator whose real multiples are in `lieGen` is admissible**:
smooth, with values in `lieGen`. DERIVED: no numeral. -/
theorem adm_abPotG [GaugeSimple G] [GaugeLie G]
    (H : Fin (GaugeGroup.dim G) → Fin (GaugeGroup.dim G) → ℂ)
    (hH : ∀ a : ℝ, GaugeLie.lieGen (G := G) (Matrix.of (a • H))) (v : Fin 4 → Fin 4 → ℝ) :
    AdmPot (G := G) (abPot H v) := by
  refine ⟨fun n => contDiff_pi.mpr fun μ => ?_, fun x μ => hH (lin v μ x)⟩
  have h : (fun x => abPot H v x μ) = ⇑((lin v μ).smulRight H) := by
    funext x
    rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

/-- **The value of `Re tr F_{α₀α₁} F_{α₂α₃}`** on the abelian potential at `H` with antisymmetric
`v`: `Re tr H² · v_{α₀α₁} v_{α₂α₃}`. DERIVED: `0`–`3` the slots; `2` the half. -/
theorem cval_abPotG {d : ℕ} (H : Fin d → Fin d → ℂ) (v : Fin 4 → Fin 4 → ℝ)
    (hv : ∀ a b, v b a = -v a b) (g : ℝ) (a : Idx4) :
    cval g (abPot H v) [([([], a 0, a 1), ([], a 2, a 3)], true)]
      = (Matrix.trace (Matrix.of H * Matrix.of H)).re * (v (a 0) (a 1) * v (a 2) (a 3)) := by
  have hF : ∀ ρ σ, covDF g (abPot H v) ρ σ [] 0 = v ρ σ • H := by
    intro ρ σ
    rw [covDF_nil]
    show (v ρ σ / 2 - v σ ρ / 2) • H = v ρ σ • H
    rw [hv]
    congr 1
    ring
  simp only [cval, wordTr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    hF, ↓reduceIte]
  show (Matrix.trace ((v (a 0) (a 1) • Matrix.of H) * (v (a 2) (a 3) • Matrix.of H))).re = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
    Complex.smul_re, Complex.smul_re]
  simp only [smul_eq_mul]
  ring

end Potential

/-! ## 6. `TensorNondegG` from `CompNondegG` -/

/-- **`TensorNondegG` from `ConvCG`, `CompNondegG`**, the index map and an abelian generator
`AbelianGenG G`. DERIVED: `0` the excluded values; `2` the order; `3` the last slot of the
four-index `α : Idx4` in `he`. -/
theorem tensorNondegG_of_comp [GaugeSimple G] [GaugeLie G] (S : Sched G) (ρ : RenormMixG G)
    (C : CompositesG G) (e : Idx4 → C.Ix)
    (he : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    (hnd : CompNondegG S C) (hab : AbelianGenG G) : TensorNondegG S ρ := by
  classical
  obtain ⟨H, hH, htr⟩ := hab
  intro c hc
  obtain ⟨v, hv, hq⟩ := exists_quadC_ne c hc
  have hinj : Function.Injective e := e_injectiveG C e he
  obtain ⟨c', hval, hzero⟩ : ∃ c' : C.Ix →₀ ℝ, (∀ a, c' (e a) = c a)
      ∧ ∀ i, i ∉ Set.range e → c' i = 0 :=
    ⟨Finsupp.mapDomain e (Finsupp.equivFunOnFinite.symm c),
      fun a => by rw [Finsupp.mapDomain_apply hinj]; rfl,
      fun i hi => Finsupp.mapDomain_notin_range _ _ hi⟩
  have hrange : ∀ i ∈ c'.support, ∃ a, e a = i := fun i hi => by
    by_contra hni
    exact Finsupp.mem_support_iff.mp hi (hzero i fun ⟨a, ha⟩ => hni ⟨a, ha⟩)
  have hsum : ∀ ψ : C.Ix → ℝ, ∑ i ∈ c'.support, c' i * ψ i = ∑ a, c a * ψ (e a) := by
    intro ψ
    have hsub : c'.support ⊆ Finset.univ.image e := fun i hi => by
      obtain ⟨a, rfl⟩ := hrange i hi
      exact Finset.mem_image_of_mem e (Finset.mem_univ a)
    rw [Finset.sum_subset hsub (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_mul]),
      Finset.sum_image hinj.injOn]
    exact Finset.sum_congr rfl fun a _ => by rw [hval]
  have hdim : ∀ i ∈ c'.support, cdim (C.cl i) = 4 := fun i hi => by
    obtain ⟨a, rfl⟩ := hrange i hi
    rw [he]
    rfl
  have hsupEq : ∀ i ∈ c'.support,
      cdim (C.cl i) = c'.support.sup (fun j => cdim (C.cl j)) := fun i hi => by
    rw [hdim i hi]
    exact le_antisymm ((hdim i hi).symm.le.trans (Finset.le_sup (f := fun j => cdim (C.cl j)) hi))
      (Finset.sup_le fun j hj => (hdim j hj).le)
  obtain ⟨f, h, hf, hh, ⟨d, hd, hs⟩, hne⟩ := hnd c' (by
    refine ⟨abPot H v, 1, adm_abPotG H hH v, onShell_abPot H v 1, ?_⟩
    rw [Finset.filter_true_of_mem hsupEq]
    simp only [one_pow, mul_one]
    have hs2 := hsum (fun i => cval 1 (abPot H v) (C.cl i))
    beta_reduce at hs2
    rw [hs2]
    simp only [he, cval_abPotG H v hv]
    intro h0
    apply hq
    have h2 : ∑ α, c α * ((Matrix.trace (Matrix.of H * Matrix.of H)).re
        * (v (α 0) (α 1) * v (α 2) (α 3)))
        = (Matrix.trace (Matrix.of H * Matrix.of H)).re * quadC c v := by
      unfold quadC
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [h2] at h0
    exact (mul_eq_zero.mp h0).resolve_left htr)
  refine ⟨f, h, hf, hh, ⟨d, hd, hs⟩, ?_⟩
  have hadm : Adm (![(c, f), (c, h)] : Fin 2 → TDatum) := by
    refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
    · fin_cases i
      · exact hf
      · exact hh
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hs
      · exact sepBy_symm hs
      · exact absurd rfl hij
  have h2 : ∀ x : Fin 2 → Idx4,
      (∏ i, ((![(c, f), (c, h)] : Fin 2 → TDatum) i).1 (x i))
        * contCG S C (fun i => (e (x i), ((![(c, f), (c, h)] : Fin 2 → TDatum) i).2))
      = (fun p : Idx4 × Idx4 => c p.1 * c p.2
          * contCG S C (![(e p.1, f), (e p.2, h)] : Fin 2 → CDatumG C))
          ((piFinTwoEquiv fun _ => Idx4) x) := by
    intro x
    rw [Fin.prod_univ_two]
    have hfun : (fun i => (e (x i), ((![(c, f), (c, h)] : Fin 2 → TDatum) i).2))
        = (![(e (x 0), f), (e (x 1), h)] : Fin 2 → CDatumG C) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    rfl
  have hdouble : ∑ i ∈ c'.support, ∑ j ∈ c'.support,
      c' i * c' j * contCG S C (![(i, f), (j, h)] : Fin 2 → CDatumG C)
      = ∑ a, ∑ b, c a * c b * contCG S C (![(e a, f), (e b, h)] : Fin 2 → CDatumG C) := by
    have h1 : ∀ i, ∑ j ∈ c'.support,
        c' i * c' j * contCG S C (![(i, f), (j, h)] : Fin 2 → CDatumG C)
        = c' i * ∑ b, c b * contCG S C (![(i, f), (e b, h)] : Fin 2 → CDatumG C) := by
      intro i
      have hs1 := hsum (fun j => contCG S C (![(i, f), (j, h)] : Fin 2 → CDatumG C))
      beta_reduce at hs1
      rw [← hs1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    have hs3 := hsum (fun i => ∑ b, c b * contCG S C (![(i, f), (e b, h)] : Fin 2 → CDatumG C))
    beta_reduce at hs3
    rw [hs3]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
  rw [contTG_expand S ρ C e hren hconv _ hadm, Fintype.sum_equiv (piFinTwoEquiv fun _ => Idx4) _
    (fun p : Idx4 × Idx4 => c p.1 * c p.2
      * contCG S C (![(e p.1, f), (e p.2, h)] : Fin 2 → CDatumG C)) h2,
    Fintype.sum_prod_type]
  exact fun h0 => hne (hdouble.trans h0)

/-! ## 7. `TensorCovG` from `CovCG` -/

/-- The values of `∑_β t_β · single (e β) 1`: `t b` at `e b`, `0` off the range of `e`.

DERIVED: `1` the unit coefficient; `0` the vanishing value. -/
theorem rep_evalG (C : CompositesG G) (e : Idx4 → C.Ix) (hinj : Function.Injective e)
    (t : Idx4 → ℝ) :
    (∀ b, (∑ β, t β • Finsupp.single (e β) (1 : ℝ)) (e b) = t b)
      ∧ ∀ j, j ∉ Set.range e → (∑ β, t β • Finsupp.single (e β) (1 : ℝ)) j = 0 := by
  classical
  constructor
  · intro b
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
    · simp
    · intro β _ hβ
      simp [hinj.ne hβ]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · intro j hj
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun β _ => ?_
    have h : e β ≠ j := fun h => hj ⟨β, h⟩
    simp [h]

/-- `rep_evalG` at a finsupp equal to `∑_β t_β · single (e β) 1`.

DERIVED: `1` the unit coefficient; `0` the vanishing value. -/
theorem rep_evalG' (C : CompositesG G) (e : Idx4 → C.Ix) (hinj : Function.Injective e)
    (t : Idx4 → ℝ) (r : C.Ix →₀ ℝ) (hr : r = ∑ β : Idx4, t β • Finsupp.single (e β) (1 : ℝ)) :
    (∀ b, r (e b) = t b) ∧ ∀ j, j ∉ Set.range e → r j = 0 := by
  subst hr
  exact rep_evalG C e hinj t

/-- **A sum over the supports of finsupps carried by the range of `e`** is a sum over `ι → Idx4`.

DERIVED: `0` the vanishing values. -/
theorem sum_piFinset_rangeG {ι : Type} [Fintype ι] [DecidableEq ι] (C : CompositesG G)
    (e : Idx4 → C.Ix) (hinj : Function.Injective e) (r : ι → (C.Ix →₀ ℝ)) (t : ι → Idx4 → ℝ)
    (hre : ∀ i b, r i (e b) = t i b) (hr0 : ∀ i j, j ∉ Set.range e → r i j = 0)
    (g : (ι → C.Ix) → ℝ) :
    ∑ σ ∈ Fintype.piFinset (fun i => (r i).support), (∏ i, r i (σ i)) * g σ
      = ∑ β : ι → Idx4, (∏ i, t i (β i)) * g (fun i => e (β i)) := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun β _ _ => fun i => e (β i)) ?_ ?_ ?_ ?_
  · intro β _ hne
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finsupp.mem_support_iff]
    show r i (e (β i)) ≠ 0
    rw [hre]
    intro h0
    apply hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
  · intro β _ _ β' _ _ hb
    funext i
    exact hinj (congrFun hb i)
  · intro σ hσ hne
    have hσ' : ∀ i, ∃ b, e b = σ i := fun i => by
      by_contra hni
      exact Finsupp.mem_support_iff.mp (Fintype.mem_piFinset.mp hσ i)
        (hr0 i (σ i) fun ⟨b, hb⟩ => hni ⟨b, hb⟩)
    choose β hβ using hσ'
    have hσeq : (fun i => e (β i)) = σ := funext hβ
    refine ⟨β, Finset.mem_univ _, ?_, hσeq⟩
    rw [← hσeq] at hne
    simp only [hre] at hne
    exact hne
  · intro β _ _
    simp only [hre]

/-- **`TensorCovG` from `ConvCG`, `CovCG`** and the index map, when the rotation representation of
each `e α` is `∑_β tcoef R α β · single (e β) 1`. DERIVED: `1` the unit coefficient. -/
theorem tensorCovG_of_comp (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) (e : Idx4 → C.Ix)
    (hinj : Function.Injective e)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvCG S C)
    (hcov : CovCG S C)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, C.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ)) :
    TensorCovG S ρ := by
  intro A hA ι _ _ F hF
  have hre1 : ∀ a b, C.rep A (e a) (e b) = tcoef A a b := fun a b =>
    (rep_evalG' C e hinj _ _ (hrep A hA a)).1 b
  have hre0 : ∀ a j, j ∉ Set.range e → C.rep A (e a) j = 0 := fun a j hj =>
    (rep_evalG' C e hinj _ _ (hrep A hA a)).2 j hj
  have hterm : ∀ α : ι → Idx4,
      Tendsto (fun k => latCG S C k (fun i => (e (α i), rotTest A (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
          * contCG S C (fun i => (e (β i), (F i).2)))) := by
    intro α
    have h : Tendsto (fun k => latCG S C k (fun i => (e (α i), rotTest A (F i).2)))
        (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (C.rep A (e (α i))).support),
          (∏ i, C.rep A (e (α i)) (σ i)) * contCG S C (fun i => (σ i, (F i).2)))) :=
      hcov A hA ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _)
    rw [sum_piFinset_rangeG C e hinj (fun i => C.rep A (e (α i))) (fun i => tcoef A (α i))
      (fun i b => hre1 (α i) b) (fun i j hj => hre0 (α i) j hj)
      (fun σ => contCG S C (fun i => (σ i, (F i).2)))] at h
    exact h
  have hL : ∑ β : ι → Idx4, (∏ i, rotC A (F i).1 (β i))
        * contCG S C (fun i => (e (β i), (F i).2))
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * ∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
        * contCG S C (fun i => (e (β i), (F i).2)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hp : ∏ i, rotC A (F i).1 (β i)
        = ∑ α : ι → Idx4, ∏ i, ((F i).1 (α i) * tcoef A (α i) (β i)) :=
      Fintype.prod_sum (fun i a => (F i).1 a * tcoef A a (β i))
    rw [hp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have hval : contTG S ρ (fun i => (rotC A (F i).1, (F i).2))
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * ∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
        * contCG S C (fun i => (e (β i), (F i).2)) :=
    (contTG_expand S ρ C e hren hconv _ (adm_relabel hF _)).trans hL
  rw [hval]
  refine (tendsto_finsetSum _ fun α _ =>
    (hterm α).const_mul (∏ i, (F i).1 (α i))).congr fun k => ?_
  rw [latTG_expand S ρ C e hren k]

end MassGap.CompReduceG

end

#print axioms MassGap.CompReduceG.latTG_expand
#print axioms MassGap.CompReduceG.contTG_expand
#print axioms MassGap.CompReduceG.sepConvG_of_comp
#print axioms MassGap.CompReduceG.os1SepG_of_comp
#print axioms MassGap.CompReduceG.os0SepG_of_comp
#print axioms MassGap.CompReduceG.e_injectiveG
#print axioms MassGap.CompReduceG.adm_abPotG
#print axioms MassGap.CompReduceG.cval_abPotG
#print axioms MassGap.CompReduceG.tensorNondegG_of_comp
#print axioms MassGap.CompReduceG.sum_piFinset_rangeG
#print axioms MassGap.CompReduceG.tensorCovG_of_comp
