import Mathlib
import MassGap.TransContSU
import MassGap.LinkReduce

/-!
# The tensor-sector clauses from the composites clauses

`TIn ρ C X w wC` carries an index map `e : Idx4 → C.Ix` with `C.cl (e α)` the monomial
`Re tr F_{α₀α₁} F_{α₂α₃}` and `(C.ren k (e α)).1 = ∑_b M k α b • (op b).1` at every step. With it the
lattice reading of the sector is a finite combination of composite readings:

`latT k F = ∑_{α : ι → Idx4} (∏ᵢ cᵢ(αᵢ)) · latC k ((e αᵢ, fᵢ))ᵢ` (`latT_expand`).

From this identity:

* `SepConv`, `OS1Sep` follow from `ConvC`, `OS1C` (`sepConv_of_comp`, `os1Sep_of_comp`);
* `OS0Sep` follows from `ConvC`, `OS0C`, with constants `|α|`, `|γ| · ∑_α |Cc (e α)|`, `β`,
  `∑_α |κ (e α)|` (`os0Sep_of_comp`);
* `TensorNondeg` follows from `ConvC`, `CompNondeg` at `2 ≤ N` (`tensorNondeg_of_comp`): the
  combination `c' = ∑_α c_α · single (e α)` is tested on the abelian potential
  `A_μ(x) = (½ ∑_ν x_ν v_{νμ}) · diag(1, −1, 0, …)`, which is smooth, Hermitian, traceless and on
  shell, with `F_{ρσ} = v_{ρσ} · diag(1, −1, 0, …)` for antisymmetric `v`; some antisymmetric `v`
  has `∑_α c_α v_{α₀α₁} v_{α₂α₃} ≠ 0` when `projR c ≠ 0` (`exists_quadC_ne`, by polarisation).

* `TensorCov` follows from `ConvC`, `CovC` when the composite representation acts on the
  sector indices by the tensor coefficients, `C.rep R (e α) = ∑_β tcoef R α β • single (e β) 1`
  (`hrep`, a condition on the data; `tensorCov_of_comp`).

`clayStatementAt_of_composites` is `clayStatementAt_of_link` with `hConv`, `h0`, `h1`, `hND`
discharged this way; `clayStatementAt_of_composites_rep` also discharges `hCov` and builds `TIn` from
`e`, its two equations and `HLs X w ≤ HLC X wC`, given `hrep`.

DERIVED (module-wide): `0`, `1`, `2`, `3` the tensor slots, the unit values and the vanishing
values; `2` the half in the potential, the pair count and `tr diag(1, −1, 0, …)²`; `4` the
dimension; `8` the order of the Riemann group in `projR`.
-/

noncomputable section

namespace MassGap.CompReduce

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. Smearing is linear in the field -/

/-- **Smearing a finite combination of fields** is the combination of the smeared fields. An alias
of `LinkReduce.smear_sum`. -/
alias smear_sum_smul := MassGap.LinkReduce.smear_sum

/-! ## 2. The sector reading as a combination of composite readings -/

/-- The smeared connected basis field `op b − ν_k(op b)` at step `k`. -/
def sf (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) (b : ρ.B) (f : TestFn) : C(Cfg N, ℝ) :=
  smear (dySpacing N k) ((ρ.op b).sub (stateK hN k (ρ.op b).1)).1 f

/-- The sector reading as the state of a product of sums. -/
theorem latT_eq_state (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) :
    latT hN ρ k F = stateK hN k (∏ i, ∑ b, mixC ρ k (F i).1 b • sf hN ρ k b (F i).2) := by
  rw [Fintype.prod_sum, (stateK hN k).map_sum]
  unfold latT
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [prod_smul_eq, (stateK hN k).map_smul]
  rfl

/-- The mixing coefficients of `c` regrouped by tensor component. -/
theorem sum_mixC_smul (ρ : RenormMix N) (k : ℕ) (c : Idx4 → ℝ) (G : ρ.B → C(Cfg N, ℝ)) :
    ∑ b, mixC ρ k c b • G b = ∑ α, c α • ∑ b, ρ.M k α b • G b := by
  unfold mixC
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- **The smeared connected composite `e α`** is the mixing combination of the smeared connected
basis fields, from the second clause of `TIn`. -/
theorem smear_cField (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ) (α : Idx4)
    (f : TestFn) :
    smear (dySpacing N k) (cField hN C k (e α, f)).1.1 f = ∑ b, ρ.M k α b • sf hN ρ k b f := by
  have h : (cField hN C k (e α, f)).1.1
      = ∑ b, ρ.M k α b • ((ρ.op b).sub (stateK hN k (ρ.op b).1)).1 := by
    show (C.ren k (e α)).1 - stateK hN k (C.ren k (e α)).1 • (1 : C(Cfg N, ℝ)) = _
    rw [hren k α, (stateK hN k).map_sum]
    simp only [(stateK hN k).map_smul]
    show _ = ∑ b, ρ.M k α b • ((ρ.op b).1 - stateK hN k (ρ.op b).1 • (1 : C(Cfg N, ℝ)))
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
  rw [h, smear_sum_smul (dySpacing_pos (one_le_of_ne_zero hN) k)]
  rfl

/-- **The sector reading at step `k`** is `∑_α (∏ᵢ cᵢ(αᵢ)) · latC k ((e αᵢ, fᵢ))ᵢ`. -/
theorem latT_expand (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (F : ι → TDatum) :
    latT hN ρ k F = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i))
      * latC hN C k (fun i => (e (α i), (F i).2)) := by
  rw [latT_eq_state]
  have h : ∀ i, ∑ b, mixC ρ k (F i).1 b • sf hN ρ k b (F i).2
      = ∑ β, (F i).1 β • smear (dySpacing N k) (cField hN C k (e β, (F i).2)).1.1 (F i).2 := by
    intro i
    rw [sum_mixC_smul]
    exact Finset.sum_congr rfl fun β _ => by rw [smear_cField hN ρ C e hren k β (F i).2]
  rw [Finset.prod_congr rfl fun i _ => h i, Fintype.prod_sum, (stateK hN k).map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [prod_smul_eq, (stateK hN k).map_smul]
  rfl

/-- Admissibility reads only the test functions. -/
theorem adm_relabel {ι Xd Yd : Type} {F : ι → Xd × TestFn} (hF : Adm F) (D : ι → Yd) :
    Adm (fun i => (D i, (F i).2)) :=
  ⟨fun i => hF.1 i, hF.2.imp fun _ hd => ⟨hd.1, fun i j hij => hd.2 i j hij⟩⟩

/-- **The sector's lattice sequence converges on an admissible family**, from `ConvC`. -/
theorem tendsto_latT (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    Tendsto (fun k => latT hN ρ k F) (ultra : Filter ℕ)
      (𝓝 (∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * contC hN C (fun i => (e (α i), (F i).2)))) := by
  have e1 : (fun k => latT hN ρ k F) = fun k => ∑ α : ι → Idx4, (∏ i, (F i).1 (α i))
      * latC hN C k (fun i => (e (α i), (F i).2)) :=
    funext fun k => latT_expand hN ρ C e hren k F
  rw [e1]
  exact tendsto_finsetSum _ fun α _ =>
    (hconv ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _)).const_mul _

/-- **The sector's value on an admissible family** is `∑_α (∏ᵢ cᵢ(αᵢ)) · contC ((e αᵢ, fᵢ))ᵢ`. -/
theorem contT_expand (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) :
    contT hN ρ F
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * contC hN C (fun i => (e (α i), (F i).2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold contT
  exact (tendsto_latT hN ρ C e hren hconv F hF).limUnder_eq

/-! ## 3. `SepConv`, `OS1Sep`, `OS0Sep` -/

/-- **`SepConv` from `ConvC`** and the second clause of `TIn`. -/
theorem sepConv_of_comp (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C) :
    SepConv hN ρ := by
  intro ι _ _ F hF
  rw [contT_expand hN ρ C e hren hconv F hF]
  exact tendsto_latT hN ρ C e hren hconv F hF

/-- **`OS1Sep` from `ConvC`, `OS1C`** and the second clause of `TIn`. -/
theorem os1Sep_of_comp (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    (h1 : OS1C hN C) : OS1Sep hN ρ := by
  intro ι _ _ F hF v
  rw [contT_expand hN ρ C e hren hconv F hF]
  refine (tendsto_finsetSum _ fun α _ =>
    (h1 ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _) v).const_mul
      (∏ i, (F i).1 (α i))).congr fun k => ?_
  rw [latT_expand hN ρ C e hren k]
  rfl

/-- The `L¹` norm is non-negative. -/
theorem l1_nonneg (f : TestFn) : 0 ≤ l1 f :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _

/-- A bound `s ≤ A γⁿ (n!)^β ∏ Xᵢ` with `|Xᵢ| ≤ Yᵢ` gives `s ≤ |A| |γ|ⁿ (n!)^β ∏ Yᵢ`. -/
theorem le_abs_bound {A γ β : ℝ} {n : ℕ} {X Y : Fin n → ℝ} {s : ℝ}
    (hs : s ≤ A * γ ^ n * (n.factorial : ℝ) ^ β * ∏ i, X i) (hXY : ∀ i, |X i| ≤ Y i) :
    s ≤ |A| * |γ| ^ n * (n.factorial : ℝ) ^ β * ∏ i, Y i := by
  have hf : 0 ≤ (n.factorial : ℝ) ^ β := Real.rpow_nonneg (Nat.cast_nonneg _) β
  refine hs.trans ((le_abs_self _).trans ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hf, Finset.abs_prod]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hXY i))
    (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) hf)

/-- **`OS0Sep` from `ConvC`, `OS0C`** and the second clause of `TIn`, with constants `|α|`,
`|γ| · ∑_α |Cc (e α)|`, `β`, `∑_α |κ (e α)|`. -/
theorem os0Sep_of_comp (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    (h0 : OS0C hN C) : OS0Sep hN ρ := by
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
  have hterm : ∀ α : Fin n → Idx4, |contC hN C (fun i => (e (α i), (F i).2))|
      ≤ |A| * |γ| ^ n * (n.factorial : ℝ) ^ β * ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2) := fun α =>
    le_abs_bound (X := fun i => Cc (e (α i)) * (d ^ κ (e (α i)))⁻¹ * l1 (F i).2)
      (hb n (fun i => (e (α i), (F i).2)) d hd hd1 (fun i => hc i) (fun i j hij => hs i j hij))
      (fun i => hXY (α i) (F i).2)
  rw [contT_expand hN ρ C e hren hconv F ⟨hc, d, hd, hs⟩]
  have hp : ∏ i, (Cm * (d ^ K)⁻¹ * l1 (F i).2) = (Cm * (d ^ K)⁻¹) ^ n * ∏ i, l1 (F i).2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hq : ∏ i, (cnorm (F i).1 * l1 (F i).2) = (∏ i, cnorm (F i).1) * ∏ i, l1 (F i).2 :=
    Finset.prod_mul_distrib
  have hr : (d ^ (K * n))⁻¹ = ((d ^ K)⁻¹) ^ n := by rw [Real.rpow_mul_natCast hd.le, inv_pow]
  calc |∑ α : Fin n → Idx4, (∏ i, (F i).1 (α i)) * contC hN C (fun i => (e (α i), (F i).2))|
      ≤ ∑ α : Fin n → Idx4,
          |(∏ i, (F i).1 (α i)) * contC hN C (fun i => (e (α i), (F i).2))| :=
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

/-- **`e` is injective**: `C.cl (e α)` determines `α`. -/
theorem e_injective (C : Composites N) (e : Idx4 → C.Ix)
    (he : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)]) :
    Function.Injective e := by
  intro α β h
  have h1 := congrArg C.cl h
  rw [he, he] at h1
  clear he h
  simp at h1
  funext i
  fin_cases i <;> simp_all

/-! ## 5. Polarisation: a non-zero Riemann projection is seen by some antisymmetric `v` -/

/-- The Kronecker delta on `Fin 4`. -/
def dl (x y : Fin 4) : ℝ := if x = y then 1 else 0

/-- The antisymmetric unit `E_{μν} − E_{νμ}`. -/
def asym (μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ := fun x y => dl x μ * dl y ν - dl x ν * dl y μ

/-- The quadratic form `∑_α c_α v_{α₀α₁} v_{α₂α₃}`.

DERIVED: `0`, `1`, `2`, `3` the four slots of the index `α : Idx4`. -/
def quadC (c : Idx4 → ℝ) (v : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ α : Idx4, c α * (v (α 0) (α 1) * v (α 2) (α 3))

/-- The sum against a product of four deltas picks one component. -/
theorem sum_dl4 (c : Idx4 → ℝ) (a b p q : Fin 4) :
    ∑ α : Idx4, c α * ((dl (α 0) a * dl (α 1) b) * (dl (α 2) p * dl (α 3) q)) = c ![a, b, p, q] := by
  rw [Finset.sum_eq_single ![a, b, p, q]]
  · simp [dl]
  · intro β _ hβ
    by_cases h : β 0 = a ∧ β 1 = b ∧ β 2 = p ∧ β 3 = q
    · exfalso
      apply hβ
      obtain ⟨h0, h1, h2, h3⟩ := h
      funext i
      fin_cases i <;> simp [h0, h1, h2, h3]
    · simp only [dl]
      split_ifs <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Polarisation**: `Q(A + B) − Q(A) − Q(B) = 8 · projR c (μ, ν, ρ, σ)` for
`A = E_{μν} − E_{νμ}`, `B = E_{ρσ} − E_{σρ}`. -/
theorem polar (c : Idx4 → ℝ) (μ ν ρ σ : Fin 4) :
    quadC c (asym μ ν + asym ρ σ) - quadC c (asym μ ν) - quadC c (asym ρ σ)
      = 8 * projR c ![μ, ν, ρ, σ] := by
  have key : ∀ α : Idx4,
      c α * ((asym μ ν + asym ρ σ) (α 0) (α 1) * (asym μ ν + asym ρ σ) (α 2) (α 3))
        - c α * (asym μ ν (α 0) (α 1) * asym μ ν (α 2) (α 3))
        - c α * (asym ρ σ (α 0) (α 1) * asym ρ σ (α 2) (α 3))
      = c α * ((dl (α 0) μ * dl (α 1) ν) * (dl (α 2) ρ * dl (α 3) σ))
        - c α * ((dl (α 0) μ * dl (α 1) ν) * (dl (α 2) σ * dl (α 3) ρ))
        - c α * ((dl (α 0) ν * dl (α 1) μ) * (dl (α 2) ρ * dl (α 3) σ))
        + c α * ((dl (α 0) ν * dl (α 1) μ) * (dl (α 2) σ * dl (α 3) ρ))
        + c α * ((dl (α 0) ρ * dl (α 1) σ) * (dl (α 2) μ * dl (α 3) ν))
        - c α * ((dl (α 0) ρ * dl (α 1) σ) * (dl (α 2) ν * dl (α 3) μ))
        - c α * ((dl (α 0) σ * dl (α 1) ρ) * (dl (α 2) μ * dl (α 3) ν))
        + c α * ((dl (α 0) σ * dl (α 1) ρ) * (dl (α 2) ν * dl (α 3) μ)) := by
    intro α
    simp only [asym, Pi.add_apply]
    ring
  unfold quadC
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun α _ => key α]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_dl4]
  rw [show projR c ![μ, ν, ρ, σ] = (c ![μ, ν, ρ, σ] - c ![ν, μ, ρ, σ] - c ![μ, ν, σ, ρ]
      + c ![ν, μ, σ, ρ] + c ![ρ, σ, μ, ν] - c ![ρ, σ, ν, μ] - c ![σ, ρ, μ, ν]
      + c ![σ, ρ, ν, μ]) / 8 from rfl]
  ring

/-- **A non-zero Riemann projection is seen by an antisymmetric `v`**: some antisymmetric `v` has
`∑_α c_α v_{α₀α₁} v_{α₂α₃} ≠ 0`. -/
theorem exists_quadC_ne (c : Idx4 → ℝ) (hc : projR c ≠ 0) :
    ∃ v : Fin 4 → Fin 4 → ℝ, (∀ a b, v b a = -v a b) ∧ quadC c v ≠ 0 := by
  obtain ⟨α, hα⟩ := Function.ne_iff.mp hc
  have hx : (![α 0, α 1, α 2, α 3] : Idx4) = α := by
    funext i
    fin_cases i <;> rfl
  have hp := polar c (α 0) (α 1) (α 2) (α 3)
  rw [hx] at hp
  have hanti : ∀ μ ν a b, asym μ ν b a = -asym μ ν a b := by
    intro μ ν a b
    simp only [asym]
    ring
  by_contra hall
  push Not at hall
  have h1 := hall (asym (α 0) (α 1)) (hanti _ _)
  have h2 := hall (asym (α 2) (α 3)) (hanti _ _)
  have h3 := hall (asym (α 0) (α 1) + asym (α 2) (α 3)) (fun a b => by
    simp only [Pi.add_apply, hanti _ _ b a]
    ring)
  apply hα
  show projR c α = 0
  linarith

/-! ## 6. The abelian on-shell potential -/

section Potential

variable (hN2 : 2 ≤ N)

/-- The first colour index. -/
def i0 : Fin N := ⟨0, by omega⟩

/-- The second colour index. -/
def i1 : Fin N := ⟨1, by omega⟩

theorem i0_ne_i1 : i0 hN2 ≠ i1 hN2 := fun h => absurd (congrArg Fin.val h) (by simp [i0, i1])

/-- The diagonal `(1, −1, 0, …)`. -/
def hr : Fin N → ℝ := Pi.single (i0 hN2) 1 - Pi.single (i1 hN2) 1

/-- The matrix `diag(1, −1, 0, …)`. -/
def Hc : Fin N → Fin N → ℂ := Matrix.of.symm (Matrix.diagonal fun i => ((hr hN2 i : ℝ) : ℂ))

theorem sum_hr : ∑ i, hr hN2 i = 0 := by
  simp [hr, Finset.sum_sub_distrib]

theorem sum_hr_sq : ∑ i, hr hN2 i * hr hN2 i = 2 := by
  have hne := i0_ne_i1 hN2
  have h : ∀ i, hr hN2 i * hr hN2 i
      = (Pi.single (i0 hN2) (1 : ℝ) : Fin N → ℝ) i + (Pi.single (i1 hN2) (1 : ℝ) : Fin N → ℝ) i := by
    intro i
    by_cases h0 : i = i0 hN2
    · subst h0
      simp [hr, hne]
    · by_cases h1 : i = i1 hN2
      · subst h1
        simp [hr, h0]
      · simp [hr, h0, h1]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Fintype.sum_pi_single',
    Fintype.sum_pi_single']
  norm_num

theorem of_smul_Hc (a : ℝ) :
    Matrix.of (a • Hc hN2) = a • Matrix.diagonal fun i => ((hr hN2 i : ℝ) : ℂ) := rfl

theorem isHermitian_smul_Hc (a : ℝ) : (Matrix.of (a • Hc hN2)).IsHermitian := by
  rw [of_smul_Hc]
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Complex.real_smul]
    simp
  · rw [if_neg (Ne.symm hij), if_neg hij, smul_zero, star_zero]

theorem trace_smul_Hc (a : ℝ) : (Matrix.of (a • Hc hN2)).trace = 0 := by
  rw [of_smul_Hc, Matrix.trace_smul, Matrix.trace_diagonal, ← Complex.ofReal_sum, sum_hr,
    Complex.ofReal_zero, smul_zero]

theorem trace_Hc_sq : Matrix.trace (Matrix.of (Hc hN2) * Matrix.of (Hc hN2)) = 2 := by
  have h : Matrix.of (Hc hN2) = Matrix.diagonal fun i => ((hr hN2 i : ℝ) : ℂ) := rfl
  rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have h2 : ∑ i, ((hr hN2 i : ℝ) : ℂ) * ((hr hN2 i : ℝ) : ℂ)
      = ((∑ i, hr hN2 i * hr hN2 i : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, sum_hr_sq]
  norm_num

end Potential

/-- The linear form `x ↦ ½ ∑_ν x_ν v_{νσ}`. -/
def lin (v : Fin 4 → Fin 4 → ℝ) (σ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ ν, (v ν σ / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) ν

theorem lin_dir (v : Fin 4 → Fin 4 → ℝ) (σ ρ : Fin 4) : lin v σ (dir ρ) = v ρ σ / 2 := by
  simp [lin, dir, Pi.single_apply]

/-- **The abelian potential** `A_μ(x) = (½ ∑_ν x_ν v_{νμ}) · H`. -/
def abPot (H : Fin N → Fin N → ℂ) (v : Fin 4 → Fin 4 → ℝ) : GPot N := fun x μ => lin v μ x • H

/-- The commutator of two real multiples of one matrix vanishes. -/
theorem mcomm_smul_self (a b : ℝ) (H : Fin N → Fin N → ℂ) : mcomm (a • H) (b • H) = 0 := by
  funext i j
  show (Matrix.of (a • H) * Matrix.of (b • H) - Matrix.of (b • H) * Matrix.of (a • H)) i j = 0
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [Matrix.of_apply, Pi.smul_apply, Complex.real_smul]
  ring

theorem fderiv_abPot (H : Fin N → Fin N → ℂ) (v : Fin 4 → Fin 4 → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) : fderiv ℝ (fun y => abPot H v y μ) x = (lin v μ).smulRight H := by
  have h : (fun y => abPot H v y μ) = ⇑((lin v μ).smulRight H) := by
    funext y
    rfl
  rw [h, ContinuousLinearMap.fderiv]

/-- **The field strength** of the abelian potential: `F_{ρσ} = ½ (v_{ρσ} − v_{σρ}) · H`. -/
theorem covDF_nil (H : Fin N → Fin N → ℂ) (v : Fin 4 → Fin 4 → ℝ) (g : ℝ) (ρ σ : Fin 4) :
    covDF g (abPot H v) ρ σ [] = fun _ => (v ρ σ / 2 - v σ ρ / 2) • H := by
  funext x
  show fderiv ℝ (fun y => abPot H v y σ) x (dir ρ) - fderiv ℝ (fun y => abPot H v y ρ) x (dir σ)
      + (Complex.I * (g : ℂ)) • mcomm (abPot H v x ρ) (abPot H v x σ)
      = (v ρ σ / 2 - v σ ρ / 2) • H
  rw [fderiv_abPot, fderiv_abPot, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, lin_dir, lin_dir, sub_smul]
  show _ + (Complex.I * (g : ℂ)) • mcomm (lin v ρ x • H) (lin v σ x • H) = _
  rw [mcomm_smul_self, smul_zero, add_zero]

/-- The covariant derivative of the constant field strength vanishes. -/
theorem covDF_one (H : Fin N → Fin N → ℂ) (v : Fin 4 → Fin 4 → ℝ) (g : ℝ) (ρ σ μ : Fin 4) :
    covDF g (abPot H v) ρ σ [μ] = fun _ => 0 := by
  funext x
  show fderiv ℝ (covDF g (abPot H v) ρ σ []) x (dir μ)
      + (Complex.I * (g : ℂ)) • mcomm (lin v μ x • H) (covDF g (abPot H v) ρ σ [] x) = 0
  rw [covDF_nil, fderiv_const_apply, zero_apply, zero_add]
  show (Complex.I * (g : ℂ)) • mcomm (lin v μ x • H) ((v ρ σ / 2 - v σ ρ / 2) • H) = 0
  rw [mcomm_smul_self, smul_zero]

/-- **The abelian potential is on shell.** -/
theorem onShell_abPot (H : Fin N → Fin N → ℂ) (v : Fin 4 → Fin 4 → ℝ) (g : ℝ) :
    OnShell g (abPot H v) := by
  intro x ν
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [covDF_one]

/-- **The abelian potential at `H = diag(1, −1, 0, …)` is admissible**: smooth, Hermitian, traceless. -/
theorem adm_abPot (hN2 : 2 ≤ N) (v : Fin 4 → Fin 4 → ℝ) : GPot.Adm (abPot (Hc hN2) v) := by
  refine ⟨fun n => contDiff_pi.mpr fun μ => ?_,
    fun x μ => ⟨isHermitian_smul_Hc hN2 (lin v μ x), trace_smul_Hc hN2 (lin v μ x)⟩⟩
  have h : (fun x => abPot (Hc hN2) v x μ) = ⇑((lin v μ).smulRight (Hc hN2)) := by
    funext x
    rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

/-- **The value of `Re tr F_{α₀α₁} F_{α₂α₃}`** on the abelian potential with antisymmetric `v`:
`2 v_{α₀α₁} v_{α₂α₃}`. -/
theorem cval_abPot (hN2 : 2 ≤ N) (v : Fin 4 → Fin 4 → ℝ) (hv : ∀ a b, v b a = -v a b) (g : ℝ)
    (a : Idx4) :
    cval g (abPot (Hc hN2) v) [([([], a 0, a 1), ([], a 2, a 3)], true)]
      = 2 * (v (a 0) (a 1) * v (a 2) (a 3)) := by
  have hF : ∀ ρ σ, covDF g (abPot (Hc hN2) v) ρ σ [] 0 = v ρ σ • Hc hN2 := by
    intro ρ σ
    rw [covDF_nil]
    show (v ρ σ / 2 - v σ ρ / 2) • Hc hN2 = v ρ σ • Hc hN2
    rw [hv]
    congr 1
    ring
  simp only [cval, wordTr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    hF, ↓reduceIte]
  show (Matrix.trace ((v (a 0) (a 1) • Matrix.of (Hc hN2))
    * (v (a 2) (a 3) • Matrix.of (Hc hN2)))).re = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, trace_Hc_sq,
    Complex.smul_re, Complex.smul_re]
  simp only [smul_eq_mul, Complex.re_ofNat]
  ring

/-! ## 7. `TensorNondeg` from `CompNondeg` -/

/-- Separation is symmetric. -/
theorem sepBy_symm {d : ℝ} {f g : TestFn} (h : ContinuumSep.sepBy d f g) :
    ContinuumSep.sepBy d g f := by
  intro y z hy hz
  obtain ⟨i, hi⟩ := h z y hz hy
  exact ⟨i, by rwa [abs_sub_comm] at hi⟩

/-- **`TensorNondeg` from `ConvC`, `CompNondeg`** and the first two clauses of `TIn`, at `2 ≤ N`. -/
theorem tensorNondeg_of_comp (hN : N ≠ 0) (hN2 : 2 ≤ N) (ρ : RenormMix N) (C : Composites N)
    (e : Idx4 → C.Ix) (he : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    (hnd : CompNondeg hN C) : TensorNondeg hN ρ := by
  classical
  intro c hc
  obtain ⟨v, hv, hq⟩ := exists_quadC_ne c hc
  have hinj : Function.Injective e := e_injective C e he
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
    refine ⟨abPot (Hc hN2) v, 1, adm_abPot hN2 v, onShell_abPot (Hc hN2) v 1, ?_⟩
    rw [Finset.filter_true_of_mem hsupEq]
    simp only [one_pow, mul_one]
    have hs2 := hsum (fun i => cval 1 (abPot (Hc hN2) v) (C.cl i))
    beta_reduce at hs2
    rw [hs2]
    simp only [he, cval_abPot hN2 v hv]
    intro h0
    apply hq
    have h2 : ∑ α, c α * (2 * (v (α 0) (α 1) * v (α 2) (α 3))) = 2 * quadC c v := by
      unfold quadC
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    linarith)
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
        * contC hN C (fun i => (e (x i), ((![(c, f), (c, h)] : Fin 2 → TDatum) i).2))
      = (fun p : Idx4 × Idx4 => c p.1 * c p.2
          * contC hN C (![(e p.1, f), (e p.2, h)] : Fin 2 → CDatum C))
          ((piFinTwoEquiv fun _ => Idx4) x) := by
    intro x
    rw [Fin.prod_univ_two]
    have hfun : (fun i => (e (x i), ((![(c, f), (c, h)] : Fin 2 → TDatum) i).2))
        = (![(e (x 0), f), (e (x 1), h)] : Fin 2 → CDatum C) := by
      funext i
      fin_cases i <;> rfl
    rw [hfun]
    rfl
  have hdouble : ∑ i ∈ c'.support, ∑ j ∈ c'.support,
      c' i * c' j * contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C)
      = ∑ a, ∑ b, c a * c b * contC hN C (![(e a, f), (e b, h)] : Fin 2 → CDatum C) := by
    have h1 : ∀ i, ∑ j ∈ c'.support, c' i * c' j * contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C)
        = c' i * ∑ b, c b * contC hN C (![(i, f), (e b, h)] : Fin 2 → CDatum C) := by
      intro i
      have hs1 := hsum (fun j => contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C))
      beta_reduce at hs1
      rw [← hs1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    have hs3 := hsum (fun i => ∑ b, c b * contC hN C (![(i, f), (e b, h)] : Fin 2 → CDatum C))
    beta_reduce at hs3
    rw [hs3]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
  rw [contT_expand hN ρ C e hren hconv _ hadm, Fintype.sum_equiv (piFinTwoEquiv fun _ => Idx4) _
    (fun p : Idx4 × Idx4 => c p.1 * c p.2
      * contC hN C (![(e p.1, f), (e p.2, h)] : Fin 2 → CDatum C)) h2,
    Fintype.sum_prod_type]
  exact fun h0 => hne (hdouble.trans h0)

/-! ## 8. The capstone -/

/-- **`ClayStatementAt` from the inputs of `clayStatementAt_of_link` without `hConv`, `h0`, `h1`,
`hND`.** `SepConv`, `OS0Sep`, `OS1Sep`, `TensorNondeg` of `ρ` are `sepConv_of_comp`,
`os0Sep_of_comp`, `os1Sep_of_comp`, `tensorNondeg_of_comp` from `hCO` and `hTI`. -/
theorem clayStatementAt_of_composites (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hDrefl : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM (ne_zero_of_two_le hN2) W D hDrefl O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTie ρ X.O)
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hL : LinkTS (ne_zero_of_two_le hN2) W D hDrefl X ρ w)
    (hnt : ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ)
    (hAC : ApertureConv (ne_zero_of_two_le hN2) W D hDrefl)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTie ρ Mb Z ∧ TopNorm N Z)
    (hWard : WardT (ne_zero_of_two_le hN2) ρ) (hCD : CompData C)
    (hCO : CompOS (ne_zero_of_two_le hN2) C) (hLC : LinkC (ne_zero_of_two_le hN2) X C wC)
    (hTI : TIn ρ C X w wC) (hGen : ObsGen (ne_zero_of_two_le hN2) W D hDrefl X) :
    ClayStatementAt hN2 W D hDrefl := by
  obtain ⟨e, he, hren, -⟩ := id hTI
  obtain ⟨hConvC, h0C, h1C, -, hNDC⟩ := id hCO
  exact clayStatementAt_of_link hN2 W D hDrefl X ρ G w hSM hH hRie hTie
    (sepConv_of_comp _ ρ C e hren hConvC) (os0Sep_of_comp _ ρ C e hren hConvC h0C)
    (os1Sep_of_comp _ ρ C e hren hConvC h1C) hCov hL hnt hK hAF hNG
    (tensorNondeg_of_comp _ hN2 ρ C e he hren hConvC hNDC) hAC C wC hCT hWard hCD hCO hLC hTI hGen

/-! ## 9. `TensorCov` from `CovC` -/

/-- The values of `∑_β t_β · single (e β) 1`: `t b` at `e b`, `0` off the range of `e`. -/
theorem rep_eval (C : Composites N) (e : Idx4 → C.Ix) (hinj : Function.Injective e)
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

/-- `rep_eval` at a finsupp equal to `∑_β t_β · single (e β) 1`. -/
theorem rep_eval' (C : Composites N) (e : Idx4 → C.Ix) (hinj : Function.Injective e)
    (t : Idx4 → ℝ) (r : C.Ix →₀ ℝ) (hr : r = ∑ β : Idx4, t β • Finsupp.single (e β) (1 : ℝ)) :
    (∀ b, r (e b) = t b) ∧ ∀ j, j ∉ Set.range e → r j = 0 := by
  subst hr
  exact rep_eval C e hinj t

/-- **A sum over the supports of finsupps carried by the range of `e`** is a sum over `ι → Idx4`. -/
theorem sum_piFinset_range {ι : Type} [Fintype ι] [DecidableEq ι] (C : Composites N)
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

/-- **`TensorCov` from `ConvC`, `CovC`** and the second clause of `TIn`, when the rotation
representation of each `e α` is `∑_β tcoef R α β · single (e β) 1`. -/
theorem tensorCov_of_comp (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hinj : Function.Injective e)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (hconv : ConvC hN C)
    (hcov : CovC hN C)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, C.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ)) :
    TensorCov hN ρ := by
  intro A hA ι _ _ F hF
  have hre1 : ∀ a b, C.rep A (e a) (e b) = tcoef A a b := fun a b =>
    (rep_eval' C e hinj _ _ (hrep A hA a)).1 b
  have hre0 : ∀ a j, j ∉ Set.range e → C.rep A (e a) j = 0 := fun a j hj =>
    (rep_eval' C e hinj _ _ (hrep A hA a)).2 j hj
  have hterm : ∀ α : ι → Idx4,
      Tendsto (fun k => latC hN C k (fun i => (e (α i), rotTest A (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
          * contC hN C (fun i => (e (β i), (F i).2)))) := by
    intro α
    have h : Tendsto (fun k => latC hN C k (fun i => (e (α i), rotTest A (F i).2)))
        (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (C.rep A (e (α i))).support),
          (∏ i, C.rep A (e (α i)) (σ i)) * contC hN C (fun i => (σ i, (F i).2)))) :=
      hcov A hA ι (fun i => (e (α i), (F i).2)) (adm_relabel hF _)
    rw [sum_piFinset_range C e hinj (fun i => C.rep A (e (α i))) (fun i => tcoef A (α i))
      (fun i b => hre1 (α i) b) (fun i j hj => hre0 (α i) j hj)
      (fun σ => contC hN C (fun i => (σ i, (F i).2)))] at h
    exact h
  have hL : ∑ β : ι → Idx4, (∏ i, rotC A (F i).1 (β i)) * contC hN C (fun i => (e (β i), (F i).2))
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * ∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
        * contC hN C (fun i => (e (β i), (F i).2)) := by
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
  have hval : contT hN ρ (fun i => (rotC A (F i).1, (F i).2))
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * ∑ β : ι → Idx4, (∏ i, tcoef A (α i) (β i))
        * contC hN C (fun i => (e (β i), (F i).2)) :=
    (contT_expand hN ρ C e hren hconv _ (adm_relabel hF _)).trans hL
  rw [hval]
  refine (tendsto_finsetSum _ fun α _ =>
    (hterm α).const_mul (∏ i, (F i).1 (α i))).congr fun k => ?_
  rw [latT_expand hN ρ C e hren k]

/-- **`ClayStatementAt` from the inputs of `clayStatementAt_of_composites` without `hCov`**, with
the clauses of `TIn` given at one index map `e` and the rotation representation of `e α` equal to
`∑_β tcoef R α β · single (e β) 1` (`hrep`). `TensorCov` of `ρ` is `tensorCov_of_comp`. -/
theorem clayStatementAt_of_composites_rep (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hDrefl : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM (ne_zero_of_two_le hN2) W D hDrefl O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTie ρ X.O)
    (hL : LinkTS (ne_zero_of_two_le hN2) W D hDrefl X ρ w)
    (hnt : ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ)
    (hAC : ApertureConv (ne_zero_of_two_le hN2) W D hDrefl)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTie ρ Mb Z ∧ TopNorm N Z)
    (hWard : WardT (ne_zero_of_two_le hN2) ρ) (hCD : CompData C)
    (hCO : CompOS (ne_zero_of_two_le hN2) C) (hLC : LinkC (ne_zero_of_two_le hN2) X C wC)
    (e : Idx4 → C.Ix) (he : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hHL : HLs X w ≤ HLC X wC)
    (hrep : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      ∀ α : Idx4, C.rep R (e α) = ∑ β : Idx4, tcoef R α β • Finsupp.single (e β) (1 : ℝ))
    (hGen : ObsGen (ne_zero_of_two_le hN2) W D hDrefl X) :
    ClayStatementAt hN2 W D hDrefl :=
  clayStatementAt_of_composites hN2 W D hDrefl X ρ G w hSM hH hRie hTie
    (tensorCov_of_comp _ ρ C e (e_injective C e he) hren hCO.1 hCO.2.2.2.1 hrep)
    hL hnt hK hAF hNG hAC C wC hCT hWard hCD hCO hLC ⟨e, he, hren, hHL⟩ hGen

end MassGap.CompReduce

end

#print axioms MassGap.CompReduce.latT_expand
#print axioms MassGap.CompReduce.contT_expand
#print axioms MassGap.CompReduce.sepConv_of_comp
#print axioms MassGap.CompReduce.os1Sep_of_comp
#print axioms MassGap.CompReduce.os0Sep_of_comp
#print axioms MassGap.CompReduce.e_injective
#print axioms MassGap.CompReduce.exists_quadC_ne
#print axioms MassGap.CompReduce.adm_abPot
#print axioms MassGap.CompReduce.onShell_abPot
#print axioms MassGap.CompReduce.cval_abPot
#print axioms MassGap.CompReduce.tensorNondeg_of_comp
#print axioms MassGap.CompReduce.clayStatementAt_of_composites
#print axioms MassGap.CompReduce.sum_piFinset_range
#print axioms MassGap.CompReduce.tensorCov_of_comp
#print axioms MassGap.CompReduce.clayStatementAt_of_composites_rep
