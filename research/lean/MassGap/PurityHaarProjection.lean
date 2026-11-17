import Mathlib
import MassGap.RectTransferG
import MassGap.PurityWilson

/-!
# MassGap.PurityHaarProjection — the Haar projection and the `q`-improved transfer bound, Lemma 5.3 of the purity paper

Lemma 5.3 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
reads the temporal kernel through the matrix `P = ∫ ρ(g) dg`. For a compact gauge group `G`
(`GaugeGroup`) with representation `ρ = repM G` of dimension `d`:

* `haarProj_mul_repM`, `repM_mul_haarProj`, `haarProj_mul_self`: `P ρ(h) = ρ(h) P = P² = P`
  (right and left invariance of Haar measure), and `integral_repM_inv`: `∫ ρ(g⁻¹) dg = P`.
* `range_haarProj`, `trace_haarProj`: `P` projects onto the fixed subspace
  `fixedSub G = {v | ∀ g, ρ(g) v = v}`, and `Tr P = q` with `q = fixedRank G = dim (fixedSub G)`;
  `fixedRank_le`: `q ≤ d`; `fixedRank_lt`: `q < d` for nontrivial `G`.
* `integral_pi_two`: two distinct coordinates of product Haar measure are independent.
* `measurePreserving_shiftAt`: left translation of one coordinate preserves product Haar measure;
  `integral_trace_mul`: `∫ Tr (ρ(g) Y) dg = Tr (P Y)`.
* `integral_trace_link`, `integral_wilson_link`: if `M(A)` does not depend on the coordinate `A_y`,
  `∫ Tr ρ(A_y M(A)) dA = Tr P = q` and `∫ (1 − Re Tr ρ(A_y M(A))/d) dA = 1 − q/d`.
* `integral_trace_edge`, `integral_wilson_edge`: for distinct endpoints `x ≠ y`,
  `∫ Tr ρ(A_y a A_x⁻¹ b) dA = Tr P = q` and `∫ (1 − Re Tr ρ(A_y a A_x⁻¹ b)/d) dA = 1 − q/d`
  (`M(A) = a A_x⁻¹ b`).
* `integral_tpG`, `integral_exponent`: on a slice with every transverse period at least `2`
  (`RectWilson.tsh_ne_self`), `∫ tp(A, V, V') dA = (tpMax/2)(1 − q/d)`, and the exponent of `gkG` has `∫ −2β tp dA = −β tpMax (1 − q/d)`.
* `gkG_ge_fixed`, `kTG_lower_fixed`: Jensen gives `exp(−β tpMax (1 − q/d)) ≤ gkG` at every real `β`,
  and `kTminFixed ≤ kTG` at `β ≥ 0`, with `kTminFixed = e^{−β spMax} e^{−β tpMax (1 − q/d)}`.

DERIVED (module-wide): `2` the smallest period at which the step `tsh` moves a site, and the two
orientations of each temporal plaquette.
-/

namespace MassGap.PurityHaarProjection

open MeasureTheory Module MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectWilsonG
  MassGap.RectTransferG MassGap.GaugeGroup

open scoped Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- A continuous function on a compact space is integrable for every finite measure. -/
theorem integrable_contX {X E : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup E] [SecondCountableTopology E] {ν : Measure X}
    [IsFiniteMeasure ν] {f : X → E} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_repM_entry (i j : Fin (dim G)) : Continuous fun g : G => repM G g i j :=
  continuous_repM.matrix_elem i j

/-! ## The Haar projection -/

variable (G) in
/-- `P = ∫ ρ(g) dg`, entrywise. -/
noncomputable def haarProj : Matrix (Fin (dim G)) (Fin (dim G)) ℂ :=
  fun i j => ∫ g, repM G g i j ∂probHaar G

theorem haarProj_apply (i j : Fin (dim G)) : haarProj G i j = ∫ g, repM G g i j ∂probHaar G := rfl

/-- `∫ ρ(g⁻¹) dg = P` (inversion invariance). -/
theorem integral_repM_inv (i j : Fin (dim G)) :
    ∫ g, repM G g⁻¹ i j ∂probHaar G = haarProj G i j :=
  integral_inv_eq_self (fun g => repM G g i j) (probHaar G)

/-- `ρ(h) P = P` (left invariance). -/
theorem repM_mul_haarProj (h : G) : repM G h * haarProj G = haarProj G := by
  ext i j
  have hs : ∀ g : G, ∑ k, repM G h i k * repM G g k j = repM G (h * g) i j := fun g => by
    rw [repM_mul, Matrix.mul_apply]
  calc (repM G h * haarProj G) i j
      = ∑ k, ∫ g, repM G h i k * repM G g k j ∂probHaar G := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ g, ∑ k, repM G h i k * repM G g k j ∂probHaar G :=
        (integral_finsetSum _ fun k _ =>
          (integrable_contX (continuous_repM_entry k j)).const_mul _).symm
    _ = ∫ g, repM G (h * g) i j ∂probHaar G := by simp_rw [hs]
    _ = haarProj G i j := integral_mul_left_eq_self (fun g => repM G g i j) h

/-- `P ρ(h) = P` (right invariance). -/
theorem haarProj_mul_repM (h : G) : haarProj G * repM G h = haarProj G := by
  ext i j
  have hs : ∀ g : G, ∑ k, repM G g i k * repM G h k j = repM G (g * h) i j := fun g => by
    rw [repM_mul, Matrix.mul_apply]
  calc (haarProj G * repM G h) i j
      = ∑ k, ∫ g, repM G g i k * repM G h k j ∂probHaar G := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => (integral_mul_const _ _).symm
    _ = ∫ g, ∑ k, repM G g i k * repM G h k j ∂probHaar G :=
        (integral_finsetSum _ fun k _ =>
          (integrable_contX (continuous_repM_entry i k)).mul_const _).symm
    _ = ∫ g, repM G (g * h) i j ∂probHaar G := by simp_rw [hs]
    _ = haarProj G i j := integral_mul_right_eq_self (fun g => repM G g i j) h

/-- `P² = P`. -/
theorem haarProj_mul_self : haarProj G * haarProj G = haarProj G := by
  ext i j
  have hs : ∀ g : G, ∑ k, haarProj G i k * repM G g k j = haarProj G i j := fun g => by
    have := congrFun (congrFun (haarProj_mul_repM g) i) j
    rwa [Matrix.mul_apply] at this
  calc (haarProj G * haarProj G) i j
      = ∑ k, ∫ g, haarProj G i k * repM G g k j ∂probHaar G := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ g, ∑ k, haarProj G i k * repM G g k j ∂probHaar G :=
        (integral_finsetSum _ fun k _ =>
          (integrable_contX (continuous_repM_entry k j)).const_mul _).symm
    _ = haarProj G i j := by simp_rw [hs]; simp

/-! ## The fixed subspace and its dimension `q` -/

variable (G) in
/-- The vectors fixed by every `ρ(g)`. -/
def fixedSub : Submodule ℂ (Fin (dim G) → ℂ) where
  carrier := {v | ∀ g : G, repM G g *ᵥ v = v}
  add_mem' := fun ha hb g => by rw [Matrix.mulVec_add, ha g, hb g]
  zero_mem' := fun g => Matrix.mulVec_zero _
  smul_mem' := fun c v hv g => by rw [Matrix.mulVec_smul, hv g]

variable (G) in
/-- `q = dim (fixedSub G)`. -/
noncomputable def fixedRank : ℕ := finrank ℂ (fixedSub G)

theorem mem_fixedSub {v : Fin (dim G) → ℂ} : v ∈ fixedSub G ↔ ∀ g : G, repM G g *ᵥ v = v :=
  Iff.rfl

/-- A fixed vector is fixed by `P`. -/
theorem haarProj_mulVec_of_mem {v : Fin (dim G) → ℂ} (hv : v ∈ fixedSub G) :
    haarProj G *ᵥ v = v := by
  funext i
  have hs : ∀ g : G, ∑ j, repM G g i j * v j = v i := fun g => by
    have := congrFun (mem_fixedSub.1 hv g) i
    rwa [Matrix.mulVec, dotProduct] at this
  calc (haarProj G *ᵥ v) i
      = ∑ j, ∫ g, repM G g i j * v j ∂probHaar G := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
    _ = ∫ g, ∑ j, repM G g i j * v j ∂probHaar G :=
        (integral_finsetSum _ fun j _ =>
          (integrable_contX (continuous_repM_entry i j)).mul_const _).symm
    _ = v i := by simp_rw [hs]; simp

/-- `P` maps onto the fixed subspace. -/
theorem range_haarProj : LinearMap.range (Matrix.toLin' (haarProj G)) = fixedSub G := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine mem_fixedSub.2 fun g => ?_
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, repM_mul_haarProj]
  · intro hv
    exact ⟨v, by rw [Matrix.toLin'_apply, haarProj_mulVec_of_mem hv]⟩

/-- `Tr P = q`. -/
theorem trace_haarProj : Matrix.trace (haarProj G) = (fixedRank G : ℂ) := by
  have hid : IsIdempotentElem (Matrix.toLin' (haarProj G)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, haarProj_mul_self]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [Matrix.trace_toLin'_eq, range_haarProj] at h
  exact h

/-- `q ≤ d`. -/
theorem fixedRank_le : fixedRank G ≤ dim G := by
  have := Submodule.finrank_le (fixedSub G)
  rwa [Module.finrank_fin_fun] at this

/-- `q < d` for nontrivial `G`: if every vector were fixed, `ρ(g) = 1` for all `g`, and `ρ` is
injective. -/
theorem fixedRank_lt [Nontrivial G] : fixedRank G < dim G := by
  refine lt_of_le_of_ne fixedRank_le fun hq => ?_
  have htop : fixedSub G = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [Module.finrank_fin_fun]; exact hq)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have h1 : repM G g = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    exact mem_fixedSub.1 (show v ∈ fixedSub G from htop ▸ Submodule.mem_top) g)
  exact hg (repM_injective (h1.trans repM_one.symm))

/-! ## Two independent coordinates -/

/-- Two distinct coordinates of product Haar measure are independent. -/
theorem integral_pi_two {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι} (hxy : x ≠ y)
    (f g : G → ℂ) :
    ∫ A : ι → G, f (A y) * g (A x) ∂(Measure.pi fun _ => probHaar G) =
      (∫ a, f a ∂probHaar G) * ∫ a, g a ∂probHaar G := by
  let F : ι → G → ℂ := fun z a => if z = y then f a else if z = x then g a else 1
  have hF : ∀ A : ι → G, ∏ z, F z (A z) = f (A y) * g (A x) := fun A => by
    rw [Fintype.prod_eq_mul y x hxy.symm fun c hc => by simp [F, hc.1, hc.2]]
    simp [F, hxy]
  have hI := integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := fun _ : ι => probHaar G) F
  simp_rw [hF] at hI
  rw [hI, Fintype.prod_eq_mul y x hxy.symm fun c hc => by simp [F, hc.1, hc.2]]
  simp [F, hxy]

/-! ## One coordinate integrated out -/

/-- Left translation by `g` of the coordinate `y`. -/
def shiftAt {ι : Type*} [DecidableEq ι] (y : ι) (g : G) (A : ι → G) : ι → G :=
  fun z => if z = y then g * A z else A z

theorem measurePreserving_shiftAt {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι) (g : G) :
    MeasurePreserving (shiftAt y g) (Measure.pi fun _ : ι => probHaar G)
      (Measure.pi fun _ : ι => probHaar G) :=
  measurePreserving_pi (fun _ => probHaar G) (fun _ => probHaar G)
    (f := fun z a => if z = y then g * a else a) fun z => by
      by_cases h : z = y
      · simp only [h, ↓reduceIte]; exact measurePreserving_mul_left (probHaar G) g
      · simp only [h, ↓reduceIte]; exact MeasurePreserving.id _

/-- `∫ Tr (ρ(g) Y) dg = Tr (P Y)`. -/
theorem integral_trace_mul (Y : Matrix (Fin (dim G)) (Fin (dim G)) ℂ) :
    ∫ g, Matrix.trace (repM G g * Y) ∂probHaar G = Matrix.trace (haarProj G * Y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    (integrable_contX (continuous_repM_entry i k)).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => (integrable_contX (continuous_repM_entry i k)).mul_const _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_mul_const, haarProj_apply]

/-- If `M(A)` does not depend on `A_y`, `∫ Tr ρ(A_y M(A)) dA = Tr P`. -/
theorem integral_trace_link {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι)
    {M : (ι → G) → G} (hM : Continuous M)
    (hMy : ∀ A B : ι → G, (∀ z, z ≠ y → A z = B z) → M A = M B) :
    ∫ A : ι → G, Matrix.trace (repM G (A y * M A)) ∂(Measure.pi fun _ => probHaar G) =
      Matrix.trace (haarProj G) := by
  have hY : Continuous fun A : ι → G => repM G (A y * M A) :=
    continuous_repM.comp ((continuous_apply y).mul hM)
  have hF : Continuous fun A : ι → G => Matrix.trace (repM G (A y * M A)) :=
    (continuous_id.matrix_trace).comp hY
  have hinv : ∀ g : G,
      ∫ A : ι → G, Matrix.trace (repM G (A y * M A)) ∂(Measure.pi fun _ => probHaar G) =
        ∫ A : ι → G, Matrix.trace (repM G g * repM G (A y * M A))
          ∂(Measure.pi fun _ => probHaar G) := fun g => by
    have hφ := measurePreserving_shiftAt (G := G) y g
    have e1 := integral_map (μ := Measure.pi fun _ : ι => probHaar G) hφ.measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [hφ.map_eq] at e1
    rw [e1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
    have h1 : shiftAt y g A y = g * A y := by simp [shiftAt]
    have h2 : M (shiftAt y g A) = M A := hMy _ _ fun z hz => by simp [shiftAt, hz]
    show Matrix.trace (repM G (shiftAt y g A y * M (shiftAt y g A))) = _
    rw [h1, h2, mul_assoc, repM_mul]
  have hint : Integrable (Function.uncurry fun (g : G) (A : ι → G) =>
      Matrix.trace (repM G g * repM G (A y * M A)))
      ((probHaar G).prod (Measure.pi fun _ : ι => probHaar G)) :=
    integrable_contX ((continuous_id.matrix_trace).comp
      ((continuous_repM.comp continuous_fst).mul (hY.comp continuous_snd)))
  calc ∫ A : ι → G, Matrix.trace (repM G (A y * M A)) ∂(Measure.pi fun _ => probHaar G)
      = ∫ _g : G, ∫ A : ι → G, Matrix.trace (repM G (A y * M A))
          ∂(Measure.pi fun _ => probHaar G) ∂probHaar G := by
        simp only [integral_const, probReal_univ, one_smul]
    _ = ∫ g : G, ∫ A : ι → G, Matrix.trace (repM G g * repM G (A y * M A))
          ∂(Measure.pi fun _ => probHaar G) ∂probHaar G :=
        integral_congr_ae (Filter.Eventually.of_forall hinv)
    _ = ∫ A : ι → G, ∫ g : G, Matrix.trace (repM G g * repM G (A y * M A))
          ∂probHaar G ∂(Measure.pi fun _ => probHaar G) := integral_integral_swap hint
    _ = ∫ _A : ι → G, Matrix.trace (haarProj G) ∂(Measure.pi fun _ => probHaar G) := by
        simp_rw [integral_trace_mul, haarProj_mul_repM]
    _ = Matrix.trace (haarProj G) := by simp only [integral_const, probReal_univ, one_smul]

/-- If `M(A)` does not depend on `A_y`, `∫ (1 − Re Tr ρ(A_y M(A))/d) dA = 1 − q/d`. -/
theorem integral_wilson_link {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι)
    {M : (ι → G) → G} (hM : Continuous M)
    (hMy : ∀ A B : ι → G, (∀ z, z ≠ y → A z = B z) → M A = M B) :
    ∫ A : ι → G, wilsonDensityG G (A y * M A) ∂(Measure.pi fun _ => probHaar G) =
      1 - (fixedRank G : ℝ) / dim G := by
  have hc : Continuous fun A : ι → G => Matrix.trace (repM G (A y * M A)) :=
    (continuous_id.matrix_trace).comp (continuous_repM.comp ((continuous_apply y).mul hM))
  have hre : ∫ A : ι → G, (Matrix.trace (repM G (A y * M A))).re
      ∂(Measure.pi fun _ => probHaar G) = fixedRank G := by
    have h := integral_re (𝕜 := ℂ) (integrable_contX (ν := Measure.pi fun _ => probHaar G) hc)
    rw [integral_trace_link y hM hMy, trace_haarProj] at h
    simpa using h
  have hi : Integrable (fun A : ι → G => (Matrix.trace (repM G (A y * M A))).re)
      (Measure.pi fun _ => probHaar G) := integrable_contX (Complex.continuous_re.comp hc)
  simp only [wilsonDensityG]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul, hre]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-! ## The edge mean -/

/-- `Tr (Y C Z D) = ∑ (Y_ij Z_kl)(C_jk D_li)`. -/
theorem trace_expand {n : ℕ} (Y C Z D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Y * C * Z * D) =
      ∑ i, ∑ l, ∑ k, ∑ j, (Y i j * Z k l) * (C j k * D l i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem integral_sum4 {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}
    {f : Fin n → Fin n → Fin n → Fin n → X → ℂ} (hf : ∀ i l k j, Integrable (f i l k j) ν) :
    ∫ A, ∑ i, ∑ l, ∑ k, ∑ j, f i l k j A ∂ν = ∑ i, ∑ l, ∑ k, ∑ j, ∫ A, f i l k j A ∂ν := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hf i l k j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => hf i l k j]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hf i l k j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun j _ => hf i l k j]

/-- For distinct endpoints, `∫ Tr ρ(A_y a A_x⁻¹ b) dA = Tr P`. -/
theorem integral_trace_edge {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι} (hxy : x ≠ y)
    (a b : G) :
    ∫ A : ι → G, Matrix.trace (repM G (A y * a * (A x)⁻¹ * b)) ∂(Measure.pi fun _ => probHaar G) =
      Matrix.trace (haarProj G) := by
  simpa only [mul_assoc] using integral_trace_link y (M := fun A : ι → G => a * ((A x)⁻¹ * b))
    (continuous_const.mul ((continuous_apply x).inv.mul continuous_const))
    fun A B h => congrArg (fun g => a * (g⁻¹ * b)) (h x hxy)

/-- For distinct endpoints, `∫ (1 − Re Tr ρ(A_y a A_x⁻¹ b)/d) dA = 1 − q/d`. -/
theorem integral_wilson_edge {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι} (hxy : x ≠ y)
    (a b : G) :
    ∫ A : ι → G, wilsonDensityG G (A y * a * (A x)⁻¹ * b) ∂(Measure.pi fun _ => probHaar G) =
      1 - (fixedRank G : ℝ) / dim G := by
  simpa only [mul_assoc] using integral_wilson_link y (M := fun A : ι → G => a * ((A x)⁻¹ * b))
    (continuous_const.mul ((continuous_apply x).inv.mul continuous_const))
    fun A B h => congrArg (fun g => a * (g⁻¹ * b)) (h x hxy)

/-! ## The temporal action of one slice -/

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- `∫ tp(A, V, V') dA = (tpMax/2)(1 − q/d)`. -/
theorem integral_tpG (hT : ∀ ν, 2 ≤ T ν) (V V' : SpT μ T → G) :
    ∫ A, tpTG G μ T A V V' ∂(hAG G μ T) =
      RectTransfer.tpMax μ T / 2 * (1 - (fixedRank G : ℝ) / dim G) := by
  have hc : ∀ (ν : {j : Fin 4 // j ≠ μ}) (y : TT μ T), Continuous fun A : TT μ T → G =>
      wilsonDensityG G (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹) := fun ν y =>
    continuous_wilsonDensityG.comp ((((continuous_apply y).mul continuous_const).mul
      (continuous_apply (tsh μ T ν y)).inv).mul continuous_const)
  unfold tpTG
  calc ∫ A, ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
        wilsonDensityG G (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹) ∂(hAG G μ T)
      = ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T, ∫ A,
        wilsonDensityG G (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹) ∂(hAG G μ T) := by
        rw [integral_finsetSum _ fun ν _ =>
          integrable_finsetSum _ fun y _ => integrable_contX (hc ν y)]
        exact Finset.sum_congr rfl fun ν _ =>
          integral_finsetSum _ fun y _ => integrable_contX (hc ν y)
    _ = ∑ _ν : {j : Fin 4 // j ≠ μ}, ∑ _y : TT μ T, (1 - (fixedRank G : ℝ) / dim G) :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ =>
          integral_wilson_edge (tsh_ne_self (hT ν) y) _ _
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RectTransfer.tpMax]
        ring

/-- The exponent of `gkG`: `∫ −2β tp(A, V, V') dA = −β tpMax (1 − q/d)`. -/
theorem integral_exponent (hT : ∀ ν, 2 ≤ T ν) (β : ℝ) (V V' : SpT μ T → G) :
    ∫ A, -β * (2 * tpTG G μ T A V V') ∂(hAG G μ T) =
      -β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)) := by
  rw [integral_const_mul, integral_const_mul, integral_tpG hT]
  ring

/-- Lemma 5.3, lower bound with `q`: `exp(−β tpMax (1 − q/d)) ≤ gkG`, at every real `β` (Jensen). -/
theorem gkG_ge_fixed (hT : ∀ ν, 2 ≤ T ν) (β : ℝ) (V V' : SpT μ T → G) :
    Real.exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G))) ≤
      gkG G μ T β V V' := by
  unfold gkG
  have hc : Continuous fun A : TT μ T → G => -β * (2 * tpTG G μ T A V V') :=
    continuous_const.mul (continuous_const.mul
      (continuous_tpG continuous_id continuous_const continuous_const))
  refine PurityWilson.kernel_lower (integrable_contX hc)
    (integrable_contX (Real.continuous_exp.comp hc)) (integral_exponent hT β V V')

variable (μ T) in
/-- `kTminFixed β = e^{−β spMax} e^{−β tpMax (1 − q/d)}`. -/
noncomputable def kTminFixed (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [GaugeGroup G] (β : ℝ) : ℝ :=
  Real.exp (-β * RectTransfer.spMax μ T) *
    Real.exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)))

/-- `kTminFixed ≤ kTG` at `β ≥ 0`. -/
theorem kTG_lower_fixed (hT : ∀ ν, 2 ≤ T ν) {β : ℝ} (hβ : 0 ≤ β) (V V' : SpT μ T → G) :
    kTminFixed μ T G β ≤ kTG G μ T β V V' := by
  unfold kTG kTminFixed
  have h1 : Real.exp (-β * RectTransfer.spMax μ T / 2) ≤ Real.exp (-β * spTG G μ T V / 2) := by
    rw [Real.exp_le_exp]; have := spG_le V; nlinarith
  have h2 : Real.exp (-β * RectTransfer.spMax μ T / 2) ≤ Real.exp (-β * spTG G μ T V' / 2) := by
    rw [Real.exp_le_exp]; have := spG_le V'; nlinarith
  have h3 := gkG_ge_fixed hT β V V'
  have e : Real.exp (-β * RectTransfer.spMax μ T)
      = Real.exp (-β * RectTransfer.spMax μ T / 2) * Real.exp (-β * RectTransfer.spMax μ T / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have h0 : 0 ≤ gkG G μ T β V V' := (Real.exp_pos _).le.trans h3
  calc Real.exp (-β * RectTransfer.spMax μ T / 2) * Real.exp (-β * RectTransfer.spMax μ T / 2)
        * Real.exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)))
      = Real.exp (-β * RectTransfer.spMax μ T / 2) *
          Real.exp (-β * (RectTransfer.tpMax μ T * (1 - (fixedRank G : ℝ) / dim G)))
          * Real.exp (-β * RectTransfer.spMax μ T / 2) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le) h2
          (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le h0)

end MassGap.PurityHaarProjection

#print axioms MassGap.PurityHaarProjection.integrable_contX
#print axioms MassGap.PurityHaarProjection.continuous_repM_entry
#print axioms MassGap.PurityHaarProjection.haarProj_apply
#print axioms MassGap.PurityHaarProjection.integral_repM_inv
#print axioms MassGap.PurityHaarProjection.repM_mul_haarProj
#print axioms MassGap.PurityHaarProjection.haarProj_mul_repM
#print axioms MassGap.PurityHaarProjection.haarProj_mul_self
#print axioms MassGap.PurityHaarProjection.mem_fixedSub
#print axioms MassGap.PurityHaarProjection.haarProj_mulVec_of_mem
#print axioms MassGap.PurityHaarProjection.range_haarProj
#print axioms MassGap.PurityHaarProjection.trace_haarProj
#print axioms MassGap.PurityHaarProjection.fixedRank_le
#print axioms MassGap.PurityHaarProjection.fixedRank_lt
#print axioms MassGap.PurityHaarProjection.integral_pi_two
#print axioms MassGap.PurityHaarProjection.measurePreserving_shiftAt
#print axioms MassGap.PurityHaarProjection.integral_trace_mul
#print axioms MassGap.PurityHaarProjection.integral_trace_link
#print axioms MassGap.PurityHaarProjection.integral_wilson_link
#print axioms MassGap.PurityHaarProjection.trace_expand
#print axioms MassGap.PurityHaarProjection.integral_sum4
#print axioms MassGap.PurityHaarProjection.integral_trace_edge
#print axioms MassGap.PurityHaarProjection.integral_wilson_edge
#print axioms MassGap.PurityHaarProjection.integral_tpG
#print axioms MassGap.PurityHaarProjection.integral_exponent
#print axioms MassGap.PurityHaarProjection.gkG_ge_fixed
#print axioms MassGap.PurityHaarProjection.kTG_lower_fixed
