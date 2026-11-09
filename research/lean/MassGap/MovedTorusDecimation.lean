import Mathlib
import MassGap.ElectricStep
import MassGap.HolderBondMoving

/-!
# MassGap.MovedTorusDecimation — on the moved side-`2n` torus, integrating the links inside the `2 × 2` blocks and the midpoint links leaves the side-`n` torus with the fourfold convolution, for every compact group

After the bond moves of `HolderBondMoving`, a plaquette of the side-`2n` torus survives when its site is even in the
two directions transverse to its plane. The survivors fill the coordinate planes at even transverse position, one
`2 × 2` block above each coarse plaquette. This module integrates them out.

## The objects

* `emb X ε = 2X + ε` (`embEquiv`): a fine site is a coarse site and a parity vector `ε ∈ {0,1}⁴`. A step along `i`
  sets `εᵢ = 1`, or moves the coarse site and sets `εᵢ = 0` (`tshift_emb`).
* `Plane`: the pairs `i < j`. `par i j a b = a eᵢ + b eⱼ`.
* The fine links split three ways (`eZ`, `enc`):
  - line links `(μ, 2X + s e_μ)`, two per coarse link;
  - the four links interior to the block `(X, p)` (`cellInt`): `(i, eⱼ)`, `(i, eᵢ + eⱼ)`, `(j, eᵢ)`, `(j, eᵢ + eⱼ)`;
  - the rest (`Free`), which lie on no surviving plaquette.
* `asm`: the fine configuration from its three parts. `blockW w U X p`: the product of `w` over the four fine
  plaquettes of the block.

## What is proved

* `measurePreserving_asm`: the assembly carries product Haar measure on the parts to product Haar measure on the fine
  links.
* `blockW_asm`: on the assembled configuration the block's four words are `a₁ v₁ h₁⁻¹ d₁⁻¹`, `a₂ b₁ h₂⁻¹ v₁⁻¹`,
  `h₁ v₂ c₁⁻¹ d₂⁻¹` and `h₂ b₂ c₂⁻¹ v₂⁻¹`. Here `a, b, c, d` are the fine links of the four coarse links, and `h, v`
  the interior links.
* `block_integral`: for a continuous class function `w`, integrating the four interior links gives
  `(w ⋆ w) ⋆ (w ⋆ w)` at `(a₁a₂)(b₁b₂)(c₁c₂)⁻¹(d₁d₂)⁻¹`, the boundary word of the coarse plaquette whose links are
  the products. Each link is one `ElectricStep.integral_link`; `h₁, h₂` enter only through `h₁h₂`.
* `integral_shear`: the two fine links of a coarse link collapse to their product, by left invariance.
* **`decimation`**: for every compact second-countable group and continuous class `w`,
  `∫ ∏_X ∏_p blockW w U X p dU = ∫ ∏_X ∏_p ((w ⋆ w) ⋆ (w ⋆ w))(hol_{p,X} V) dV`. The left side is on the
  side-`2n` torus, the right side on the side-`n` torus.

The identity is exact and carries no group-specific content.

DERIVED (module-wide): `4` the dimension; `2` the doubling (parities in `Fin 2`, side `2n`); `4 = 2²` the plaquettes
and the interior links of a block.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.MovedTorusDecimation

open MeasureTheory Set MassGap.CompactGauge MassGap.TorusDoubling MassGap.HolderBondMoving
  MassGap.ElectricStep

/-! ## 1. Fine sites as a coarse site and a parity -/

theorem val_finRotate {N : ℕ} (i : Fin N) : (finRotate N i).val = (i.val + 1) % N := by
  cases N with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    split_ifs with h
    · rw [h, Fin.val_last, Nat.mod_self]
    · have h1 : i.val ≠ m := fun e => h (Fin.ext (by rw [e, Fin.val_last]))
      have h2 := i.isLt
      rw [Nat.mod_eq_of_lt (by omega)]

variable {n : ℕ}

/-- **The fine site `2X + ε`** of the side-`2n` torus, for a coarse site `X` and a parity vector `ε`. -/
def emb (X : TSite 4 n) (ε : Fin 4 → Fin 2) : TSite 4 (2 * n) :=
  fun k => ⟨2 * (X k).val + (ε k).val, by have := (X k).isLt; have := (ε k).isLt; omega⟩

theorem emb_injective {X X' : TSite 4 n} {ε ε' : Fin 4 → Fin 2} (h : emb X ε = emb X' ε') :
    X = X' ∧ ε = ε' := by
  have hk : ∀ k, 2 * (X k).val + (ε k).val = 2 * (X' k).val + (ε' k).val := fun k => by
    have := congrArg Fin.val (congrFun h k); simpa [emb] using this
  refine ⟨funext fun k => Fin.ext ?_, funext fun k => Fin.ext ?_⟩ <;>
    have := hk k <;> have := (ε k).isLt <;> have := (ε' k).isLt <;> omega

theorem fin2_eq_one {a : Fin 2} (h : a ≠ 0) : a = 1 := by
  have := a.isLt
  have : a.val ≠ 0 := fun e => h (Fin.ext e)
  exact Fin.ext (by simp; omega)

/-- **One step on the fine torus.** From `2X + ε`, a step along `i` sets `ε_i = 1` if it was `0`, and
otherwise moves the coarse site one step and sets `ε_i = 0`. -/
theorem tshift_emb (i : Fin 4) (X : TSite 4 n) (ε : Fin 4 → Fin 2) :
    tshift i (emb X ε) = if ε i = 0 then emb X (Function.update ε i 1)
      else emb (tshift i X) (Function.update ε i 0) := by
  funext k
  by_cases hk : k = i
  · subst hk
    split_ifs with h
    · apply Fin.ext
      simp only [tshift, Function.update_self, emb, val_finRotate]
      rw [h]
      have := (X k).isLt
      simp only [Fin.val_zero, add_zero, Fin.val_one]
      exact Nat.mod_eq_of_lt (by omega)
    · apply Fin.ext
      simp only [tshift, Function.update_self, emb, val_finRotate]
      rw [fin2_eq_one h]
      simp only [Fin.val_one, Fin.val_zero, add_zero]
      rw [show 2 * (X k).val + 1 + 1 = 2 * ((X k).val + 1) by ring, Nat.mul_mod_mul_left]
  · split_ifs <;> simp [tshift, emb, Function.update_of_ne hk]

variable (n) in
/-- **Fine sites are coarse sites with a parity.** -/
def embEquiv : TSite 4 n × (Fin 4 → Fin 2) ≃ TSite 4 (2 * n) where
  toFun p := emb p.1 p.2
  invFun x := (fun k => ⟨(x k).val / 2, by have := (x k).isLt; omega⟩,
    fun k => ⟨(x k).val % 2, by omega⟩)
  left_inv p := by
    obtain ⟨X, ε⟩ := p
    refine Prod.ext (funext fun k => Fin.ext ?_) (funext fun k => Fin.ext ?_) <;>
      simp only [emb] <;> have := (ε k).isLt <;> omega
  right_inv x := by
    funext k
    apply Fin.ext
    simp only [emb]
    omega

theorem embEquiv_apply (p : TSite 4 n × (Fin 4 → Fin 2)) : embEquiv n p = emb p.1 p.2 := rfl

/-- A sum over fine sites is a sum over coarse sites and parities. -/
theorem sum_fine {M : Type*} [AddCommMonoid M] (F : TSite 4 (2 * n) → M) :
    ∑ x, F x = ∑ X : TSite 4 n, ∑ ε : Fin 4 → Fin 2, F (emb X ε) := by
  rw [← (embEquiv n).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The parity of the fine coordinate `2X + ε` is `ε`. -/
theorem emb_even_iff (X : TSite 4 n) (ε : Fin 4 → Fin 2) (k : Fin 4) :
    (emb X ε k).val % 2 = 0 ↔ ε k = 0 := by
  simp only [emb, Fin.ext_iff, Fin.val_zero]
  have := (ε k).isLt
  omega

/-! ## 2. Parity vectors, planes and the cell of a link -/

/-- The parity vector `a eᵢ + b eⱼ`. -/
def par (i j : Fin 4) (a b : Fin 2) : Fin 4 → Fin 2 := fun k => if k = i then a else if k = j then b else 0

/-- The parity vector `s e_μ`. -/
def pv (μ : Fin 4) (s : Fin 2) : Fin 4 → Fin 2 := fun k => if k = μ then s else 0

/-- The coordinate planes, `i < j`. -/
abbrev Plane : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- **The four links interior to a block** of the plane `p = (i, j)`: `(i, eⱼ)`, `(i, eᵢ + eⱼ)`,
`(j, eᵢ)`, `(j, eᵢ + eⱼ)`. DERIVED: `0`, `1`, `2`, `3` the indices of the four links in `Fin 4`, `4 = 2²`;
`0`, `1` the parities. -/
def cellInt (p : Plane) (m : Fin 4) : Fin 4 × (Fin 4 → Fin 2) :=
  match m with
  | 0 => (p.1.1, par p.1.1 p.1.2 0 1)
  | 1 => (p.1.1, par p.1.1 p.1.2 1 1)
  | 2 => (p.1.2, par p.1.1 p.1.2 1 0)
  | 3 => (p.1.2, par p.1.1 p.1.2 1 1)

/-- The cell of a line link `(μ, s e_μ)` or of a block-interior link. -/
def cellJ : (Fin 4 × Fin 2) ⊕ (Plane × Fin 4) → Fin 4 × (Fin 4 → Fin 2)
  | Sum.inl (μ, s) => (μ, pv μ s)
  | Sum.inr (p, m) => cellInt p m

theorem cellJ_injective : Function.Injective cellJ := by
  decide

/-! ## 3. The fine links: lines, block interiors and the rest -/

variable (n) in
/-- **Line links** `((μ, X), s)`, the fine link `(μ, 2X + s e_μ)`, and **block-interior links**
`((X, p), m)`. -/
abbrev Zl : Type := (TLink 4 n × Fin 2) ⊕ ((TSite 4 n × Plane) × Fin 4)

/-- The fine link of a line or block-interior index. -/
def eZ : Zl n → TLink 4 (2 * n)
  | Sum.inl ((μ, X), s) => (μ, emb X (pv μ s))
  | Sum.inr ((X, p), m) => ((cellInt p m).1, emb X (cellInt p m).2)

/-- The coarse site of an index. -/
def siteZ : Zl n → TSite 4 n
  | Sum.inl ((_, X), _) => X
  | Sum.inr ((X, _), _) => X

/-- The cell index of an index. -/
def idxZ : Zl n → (Fin 4 × Fin 2) ⊕ (Plane × Fin 4)
  | Sum.inl ((μ, _), s) => Sum.inl (μ, s)
  | Sum.inr ((_, p), m) => Sum.inr (p, m)

theorem eZ_eq (z : Zl n) : eZ z = ((cellJ (idxZ z)).1, emb (siteZ z) (cellJ (idxZ z)).2) := by
  rcases z with ⟨⟨μ, X⟩, s⟩ | ⟨⟨X, p⟩, m⟩ <;> rfl

theorem eZ_injective : Function.Injective (eZ (n := n)) := by
  intro z z' h
  rw [eZ_eq, eZ_eq] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨hs, he⟩ := emb_injective h2
  have hc : cellJ (idxZ z) = cellJ (idxZ z') := Prod.ext h1 he
  have hi := cellJ_injective hc
  rcases z with ⟨⟨μ, X⟩, s⟩ | ⟨⟨X, p⟩, m⟩ <;> rcases z' with ⟨⟨μ', X'⟩, s'⟩ | ⟨⟨X', p'⟩, m'⟩ <;>
    simp_all [siteZ, idxZ]

variable (n) in
/-- The remaining fine links. -/
abbrev Free : Type := ((Set.range (eZ (n := n)))ᶜ : Set (TLink 4 (2 * n)))

open Classical in
/-- **Every fine link is a line link, a block-interior link, or one of the rest.** -/
def enc : Zl n ⊕ Free n ≃ TLink 4 (2 * n) :=
  (Equiv.sumCongr (Equiv.ofInjective eZ eZ_injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (eZ (n := n))))

theorem enc_inl (z : Zl n) : enc (Sum.inl z) = eZ z := by
  simp [enc, Equiv.Set.sumCompl_apply_inl]

theorem enc_inr (c : Free n) : enc (Sum.inr c) = (c : TLink 4 (2 * n)) := by
  simp [enc, Equiv.Set.sumCompl_apply_inr]

/-! ## 4. The configuration in three parts -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- The two fine links of a coarse link. -/
def sel2 (q : G × G) (s : Fin 2) : G := match s with
  | 0 => q.1
  | 1 => q.2

/-- The four interior links of a block. DERIVED: `0`, `1`, `2`, `3` the indices of the four interior links in
`Fin 4`, in the order of `cellInt`. -/
def sel4 (q : (G × G) × (G × G)) (m : Fin 4) : G := match m with
  | 0 => q.1.1
  | 1 => q.1.2
  | 2 => q.2.1
  | 3 => q.2.2

variable (n G) in
/-- The configuration in three parts: two fine links per coarse link, four interior links per block,
and the rest. -/
abbrev Cfg : Type :=
  ((TLink 4 n → G × G) × (TSite 4 n × Plane → (G × G) × (G × G))) × (Free n → G)

/-- **The fine configuration assembled from its three parts.** -/
def asm (c : Cfg n G) : TLink 4 (2 * n) → G := fun ℓ =>
  Sum.elim (Sum.elim (fun ls : TLink 4 n × Fin 2 => sel2 (c.1.1 ls.1) ls.2)
    (fun xm : (TSite 4 n × Plane) × Fin 4 => sel4 (c.1.2 xm.1) xm.2)) c.2 (enc.symm ℓ)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem asm_line (c : Cfg n G) (l : TLink 4 n) (s : Fin 2) :
    asm c (eZ (Sum.inl (l, s))) = sel2 (c.1.1 l) s := by
  rw [asm, ← enc_inl, Equiv.symm_apply_apply]; rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem asm_int (c : Cfg n G) (xp : TSite 4 n × Plane) (m : Fin 4) :
    asm c (eZ (Sum.inr (xp, m))) = sel4 (c.1.2 xp) m := by
  rw [asm, ← enc_inl, Equiv.symm_apply_apply]; rfl

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem asm_free (c : Cfg n G) (f : Free n) : asm c f = c.2 f := by
  rw [asm, ← enc_inr, Equiv.symm_apply_apply]; rfl

variable (n G) in
/-- The product Haar measure on the three parts. -/
abbrev cfgMeasure : Measure (Cfg n G) :=
  ((Measure.pi fun _ : TLink 4 n => (probHaar G).prod (probHaar G)).prod
    (Measure.pi fun _ : TSite 4 n × Plane =>
      ((probHaar G).prod (probHaar G)).prod ((probHaar G).prod (probHaar G)))).prod
  (Measure.pi fun _ : Free n => probHaar G)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
theorem measurable_asm : Measurable (asm (n := n) (G := G)) := by
  refine measurable_pi_iff.mpr fun ℓ => ?_
  simp only [asm]
  generalize enc.symm ℓ = w
  rcases w with (⟨l, s⟩ | ⟨xp, m⟩) | f
  · fin_cases s
    · exact measurable_fst.comp ((measurable_pi_apply l).comp (measurable_fst.comp measurable_fst))
    · exact measurable_snd.comp ((measurable_pi_apply l).comp (measurable_fst.comp measurable_fst))
  · have hB : Measurable fun c : Cfg n G => c.1.2 xp :=
      (measurable_pi_apply xp).comp (measurable_snd.comp measurable_fst)
    fin_cases m
    · exact measurable_fst.comp (measurable_fst.comp hB)
    · exact measurable_snd.comp (measurable_fst.comp hB)
    · exact measurable_fst.comp (measurable_snd.comp hB)
    · exact measurable_snd.comp (measurable_snd.comp hB)
  · exact (measurable_pi_apply f).comp measurable_snd

/-- **The assembly preserves product Haar measure.** -/
theorem measurePreserving_asm :
    MeasurePreserving (asm (n := n) (G := G)) (cfgMeasure n G)
      (Measure.pi fun _ : TLink 4 (2 * n) => probHaar G) := by
  refine ⟨measurable_asm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_asm (MeasurableSet.univ_pi hs)]
  have hpre : asm ⁻¹' univ.pi s
      = ((univ.pi fun l : TLink 4 n => s (eZ (Sum.inl (l, 0))) ×ˢ s (eZ (Sum.inl (l, 1)))) ×ˢ
        (univ.pi fun xp : TSite 4 n × Plane =>
          (s (eZ (Sum.inr (xp, 0))) ×ˢ s (eZ (Sum.inr (xp, 1)))) ×ˢ
          (s (eZ (Sum.inr (xp, 2))) ×ˢ s (eZ (Sum.inr (xp, 3)))))) ×ˢ
        (univ.pi fun f : Free n => s f) := by
    ext c
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨⟨fun l => ⟨?_, ?_⟩, fun xp => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩, fun f => ?_⟩
      · have := h (eZ (Sum.inl (l, 0))); rwa [asm_line] at this
      · have := h (eZ (Sum.inl (l, 1))); rwa [asm_line] at this
      · have := h (eZ (Sum.inr (xp, 0))); rwa [asm_int] at this
      · have := h (eZ (Sum.inr (xp, 1))); rwa [asm_int] at this
      · have := h (eZ (Sum.inr (xp, 2))); rwa [asm_int] at this
      · have := h (eZ (Sum.inr (xp, 3))); rwa [asm_int] at this
      · have := h f; rwa [asm_free] at this
    · rintro ⟨⟨hA, hB⟩, hC⟩ ℓ
      rw [← enc.apply_symm_apply ℓ]
      generalize enc.symm ℓ = w
      rcases w with (⟨l, t⟩ | ⟨xp, m⟩) | f
      · rw [enc_inl, asm_line]
        fin_cases t
        · exact (hA l).1
        · exact (hA l).2
      · rw [enc_inl, asm_int]
        fin_cases m
        · exact (hB xp).1.1
        · exact (hB xp).1.2
        · exact (hB xp).2.1
        · exact (hB xp).2.2
      · rw [enc_inr, asm_free]
        exact hC f
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Measure.pi_pi]
  simp only [Measure.prod_prod]
  conv_rhs =>
    rw [← enc.prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type,
      Fintype.prod_prod_type (f := fun x : TLink 4 n × Fin 2 => probHaar G (s (enc (Sum.inl (Sum.inl x))))),
      Fintype.prod_prod_type
        (f := fun x : (TSite 4 n × Plane) × Fin 4 => probHaar G (s (enc (Sum.inl (Sum.inr x)))))]
  simp only [enc_inl, enc_inr, Fin.prod_univ_two, Fin.prod_univ_four]
  ring_nf

/-! ## 5. The block: four plaquettes, four interior links -/

theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [SecondCountableTopology G] in
/-- The convolution of class functions is a class function. -/
theorem conv_class {u v : G → ℝ} (hu : ∀ k x, u (k * x * k⁻¹) = u x)
    (hv : ∀ k x, v (k * x * k⁻¹) = v x) (k x : G) : conv u v (k * x * k⁻¹) = conv u v x := by
  unfold conv
  have h1 := integral_mul_left_eq_self (μ := probHaar G)
    (fun h => u h * v (h⁻¹ * (k * x * k⁻¹))) k
  have h2 := integral_mul_right_eq_self (μ := probHaar G)
    (fun h => u (k * h) * v ((k * h)⁻¹ * (k * x * k⁻¹))) k⁻¹
  rw [← h1, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [show k * (h * k⁻¹) = k * h * k⁻¹ by group, hu,
    show (k * h * k⁻¹)⁻¹ * (k * x * k⁻¹) = k * (h⁻¹ * x) * k⁻¹ by group, hv]

/-- The convolution of continuous functions is continuous. -/
theorem continuous_conv {u v : G → ℝ} (hu : Continuous u) (hv : Continuous v) :
    Continuous (conv u v) := by
  have hf : Continuous (Function.uncurry fun (g h : G) => u h * v (h⁻¹ * g)) :=
    (hu.comp continuous_snd).mul (hv.comp (continuous_snd.inv.mul continuous_fst))
  have h := continuous_parametric_integral_of_continuous (μ := probHaar G) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

/-- **The block integral.** Integrating the four interior links of a `2 × 2` block (the links
`h₁ = q.1.1`, `h₂ = q.1.2`, `v₁ = q.2.1`, `v₂ = q.2.2`) leaves the fourfold convolution at the boundary
word of the coarse plaquette, whose links are the products `a₁a₂`, `b₁b₂`, `c₁c₂`, `d₁d₂`. -/
theorem block_integral (w : G → ℝ) (hw : Continuous w) (hwc : ∀ k x, w (k * x * k⁻¹) = w x)
    (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
    ∫ q, w (a1 * q.2.1 * q.1.1⁻¹ * d1⁻¹) * w (a2 * b1 * q.1.2⁻¹ * q.2.1⁻¹)
        * w (q.1.1 * q.2.2 * c1⁻¹ * d2⁻¹) * w (q.1.2 * b2 * c2⁻¹ * q.2.2⁻¹)
        ∂(((probHaar G).prod (probHaar G)).prod ((probHaar G).prod (probHaar G)))
      = conv (conv w w) (conv w w) (a1 * a2 * (b1 * b2) * (c1 * c2)⁻¹ * (d1 * d2)⁻¹) := by
  set μ := probHaar G
  set W2 := conv w w with hW2
  have hW2c : Continuous W2 := continuous_conv hw hw
  have hW2cl : ∀ k x, W2 (k * x * k⁻¹) = W2 x := conv_class hwc hwc
  have hint : Integrable (fun q : (G × G) × (G × G) => w (a1 * q.2.1 * q.1.1⁻¹ * d1⁻¹)
      * w (a2 * b1 * q.1.2⁻¹ * q.2.1⁻¹) * w (q.1.1 * q.2.2 * c1⁻¹ * d2⁻¹)
      * w (q.1.2 * b2 * c2⁻¹ * q.2.2⁻¹)) ((μ.prod μ).prod (μ.prod μ)) :=
    integrable_of_continuous (by fun_prop)
  rw [integral_prod _ hint]
  -- the two vertical interior links, for fixed horizontal ones
  have inner : ∀ h : G × G, ∫ v : G × G, w (a1 * v.1 * h.1⁻¹ * d1⁻¹) * w (a2 * b1 * h.2⁻¹ * v.1⁻¹)
      * w (h.1 * v.2 * c1⁻¹ * d2⁻¹) * w (h.2 * b2 * c2⁻¹ * v.2⁻¹) ∂(μ.prod μ)
      = W2 (a1 * a2 * b1 * (h.1 * h.2)⁻¹ * d1⁻¹) * W2 (h.1 * h.2 * b2 * (c1 * c2)⁻¹ * d2⁻¹) := by
    intro h
    have e : (fun v : G × G => w (a1 * v.1 * h.1⁻¹ * d1⁻¹) * w (a2 * b1 * h.2⁻¹ * v.1⁻¹)
        * w (h.1 * v.2 * c1⁻¹ * d2⁻¹) * w (h.2 * b2 * c2⁻¹ * v.2⁻¹))
        = fun v => (w (a1 * v.1 * h.1⁻¹ * d1⁻¹) * w (a2 * b1 * h.2⁻¹ * v.1⁻¹))
          * (w (h.1 * v.2 * c1⁻¹ * d2⁻¹) * w (h.2 * b2 * c2⁻¹ * v.2⁻¹)) := by
      funext v; ring
    rw [e, integral_prod_mul (fun g => w (a1 * g * h.1⁻¹ * d1⁻¹) * w (a2 * b1 * h.2⁻¹ * g⁻¹))
      (fun g => w (h.1 * g * c1⁻¹ * d2⁻¹) * w (h.2 * b2 * c2⁻¹ * g⁻¹)),
      integral_link w w hwc a1 h.1 a2 h.2 d1 b1, integral_link w w hwc h.1 c1 h.2 c2 d2 b2]
  simp_rw [inner]
  -- the horizontal interior links enter only through `h₁h₂`
  set Ψ : G → ℝ := fun m => W2 (a1 * a2 * b1 * m⁻¹ * d1⁻¹) * W2 (m * b2 * (c1 * c2)⁻¹ * d2⁻¹) with hΨ
  have hΨc : Continuous Ψ := by
    refine (hW2c.comp ?_).mul (hW2c.comp ?_) <;> fun_prop
  have e2 : ∫ h : G × G, Ψ (h.1 * h.2) ∂(μ.prod μ) = ∫ m, Ψ m ∂μ := by
    rw [integral_prod _ (integrable_of_continuous (f := fun h : G × G => Ψ (h.1 * h.2))
      (hΨc.comp (continuous_fst.mul continuous_snd)))]
    simp only [integral_mul_left_eq_self Ψ, integral_const, probReal_univ, one_smul]
  rw [show (fun h : G × G => W2 (a1 * a2 * b1 * (h.1 * h.2)⁻¹ * d1⁻¹)
      * W2 (h.1 * h.2 * b2 * (c1 * c2)⁻¹ * d2⁻¹)) = fun h => Ψ (h.1 * h.2) from rfl, e2]
  -- the last link
  have e3 : ∀ m, Ψ m = W2 (1 * m * ((c1 * c2) * b2⁻¹)⁻¹ * d2⁻¹)
      * W2 (d1⁻¹ * (a1 * a2 * b1) * 1⁻¹ * m⁻¹) := by
    intro m
    have hA : W2 (a1 * a2 * b1 * m⁻¹ * d1⁻¹) = W2 (d1⁻¹ * (a1 * a2 * b1) * 1⁻¹ * m⁻¹) := by
      rw [← hW2cl d1 (d1⁻¹ * (a1 * a2 * b1) * 1⁻¹ * m⁻¹)]; congr 1; group
    have hB : W2 (m * b2 * (c1 * c2)⁻¹ * d2⁻¹) = W2 (1 * m * ((c1 * c2) * b2⁻¹)⁻¹ * d2⁻¹) := by
      congr 1; group
    show W2 (a1 * a2 * b1 * m⁻¹ * d1⁻¹) * W2 (m * b2 * (c1 * c2)⁻¹ * d2⁻¹) = _
    rw [hA, hB, mul_comm]
  simp_rw [e3]
  rw [integral_link W2 W2 hW2cl 1 ((c1 * c2) * b2⁻¹) d1⁻¹ 1 d2 (a1 * a2 * b1),
    ← conv_class hW2cl hW2cl d1]
  congr 1
  group

/-! ## 6. The links of a block -/

section Links

variable {i j : Fin 4}

theorem par_i (a b : Fin 2) : par i j a b i = a := by simp [par]

theorem par_j (hij : i ≠ j) (a b : Fin 2) : par i j a b j = b := by simp [par, hij.symm]

theorem update_par_i (a b a' : Fin 2) :
    Function.update (par i j a b) i a' = par i j a' b := by
  funext k; by_cases hk : k = i
  · subst hk; simp [par]
  · simp [par, hk]

theorem update_par_j (hij : i ≠ j) (a b b' : Fin 2) :
    Function.update (par i j a b) j b' = par i j a b' := by
  funext k; by_cases hk : k = j
  · subst hk; simp [par, Ne.symm hij]
  · simp [par, hk]

theorem par_eq_pv_i (a : Fin 2) : par i j a 0 = pv i a := by
  funext k; by_cases hk : k = i <;> simp [par, pv, hk]

theorem par_eq_pv_j (hij : i ≠ j) (b : Fin 2) : par i j 0 b = pv j b := by
  funext k; by_cases hk : k = i
  · subst hk; simp [par, pv, hij]
  · simp [par, pv, hk]

theorem tshift_i_0 (X : TSite 4 n) (b : Fin 2) :
    tshift i (emb X (par i j 0 b)) = emb X (par i j 1 b) := by
  rw [tshift_emb, par_i, if_pos rfl, update_par_i]

theorem tshift_i_1 (X : TSite 4 n) (b : Fin 2) :
    tshift i (emb X (par i j 1 b)) = emb (tshift i X) (par i j 0 b) := by
  rw [tshift_emb, par_i, if_neg (by decide), update_par_i]

theorem tshift_j_0 (hij : i ≠ j) (X : TSite 4 n) (a : Fin 2) :
    tshift j (emb X (par i j a 0)) = emb X (par i j a 1) := by
  rw [tshift_emb, par_j hij, if_pos rfl, update_par_j hij]

theorem tshift_j_1 (hij : i ≠ j) (X : TSite 4 n) (a : Fin 2) :
    tshift j (emb X (par i j a 1)) = emb (tshift j X) (par i j a 0) := by
  rw [tshift_emb, par_j hij, if_neg (by decide), update_par_j hij]

end Links

theorem plane_ne (p : Plane) : p.1.1 ≠ p.1.2 := p.2.ne

/-- The line link `(μ, X, s)`. -/
theorem lk_line_i (p : Plane) (X : TSite 4 n) (a : Fin 2) :
    ((p.1.1, emb X (par p.1.1 p.1.2 a 0)) : TLink 4 (2 * n)) = eZ (Sum.inl ((p.1.1, X), a)) := by
  rw [par_eq_pv_i]; rfl

theorem lk_line_j (p : Plane) (X : TSite 4 n) (b : Fin 2) :
    ((p.1.2, emb X (par p.1.1 p.1.2 0 b)) : TLink 4 (2 * n)) = eZ (Sum.inl ((p.1.2, X), b)) := by
  rw [par_eq_pv_j (plane_ne p)]; rfl

theorem lk_int (p : Plane) (X : TSite 4 n) (m : Fin 4) :
    (((cellInt p m).1, emb X (cellInt p m).2) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), m)) := rfl

/-- **The four fine plaquettes of the block `(X, p)`**, as a product of weights. -/
def blockW (w : G → ℝ) (U : TLink 4 (2 * n) → G) (X : TSite 4 n) (p : Plane) : ℝ :=
  w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 0)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 0)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 0 1)) U)
    * w (thol ((p.1.1, p.1.2), emb X (par p.1.1 p.1.2 1 1)) U)

/-- The block weight of the assembled configuration, in the three parts. -/
theorem blockW_asm (w : G → ℝ) (c : Cfg n G) (X : TSite 4 n) (p : Plane) :
    blockW w (asm c) X p =
      w ((c.1.1 (p.1.1, X)).1 * (c.1.2 (X, p)).2.1 * ((c.1.2 (X, p)).1.1)⁻¹ * ((c.1.1 (p.1.2, X)).1)⁻¹)
      * w ((c.1.1 (p.1.1, X)).2 * (c.1.1 (p.1.2, tshift p.1.1 X)).1 * ((c.1.2 (X, p)).1.2)⁻¹
          * ((c.1.2 (X, p)).2.1)⁻¹)
      * w ((c.1.2 (X, p)).1.1 * (c.1.2 (X, p)).2.2 * ((c.1.1 (p.1.1, tshift p.1.2 X)).1)⁻¹
          * ((c.1.1 (p.1.2, X)).2)⁻¹)
      * w ((c.1.2 (X, p)).1.2 * (c.1.1 (p.1.2, tshift p.1.1 X)).2 * ((c.1.1 (p.1.1, tshift p.1.2 X)).2)⁻¹
          * ((c.1.2 (X, p)).2.2)⁻¹) := by
  have hij := plane_ne p
  unfold blockW thol
  simp only
  rw [tshift_i_0, tshift_j_0 hij, tshift_i_1, tshift_j_0 hij, tshift_i_0, tshift_j_1 hij,
    tshift_i_1, tshift_j_1 hij]
  rw [lk_line_i p X 0, lk_line_j p X 0, lk_line_i p X 1, lk_line_j p (tshift p.1.1 X) 0,
    lk_line_j p X 1, lk_line_i p (tshift p.1.2 X) 0, lk_line_j p (tshift p.1.1 X) 1,
    lk_line_i p (tshift p.1.2 X) 1]
  rw [show ((p.1.2, emb X (par p.1.1 p.1.2 1 0)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 2)) from rfl,
    show ((p.1.1, emb X (par p.1.1 p.1.2 0 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 0)) from rfl,
    show ((p.1.1, emb X (par p.1.1 p.1.2 1 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 1)) from rfl,
    show ((p.1.2, emb X (par p.1.1 p.1.2 1 1)) : TLink 4 (2 * n)) = eZ (Sum.inr ((X, p), 3)) from rfl]
  simp only [asm_line, asm_int]
  rfl

/-! ## 7. The decimation -/

omit [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_thol {d N : ℕ} (q : TPlaq d N) : Continuous fun U : TLink d N → G => thol q U := by
  unfold thol; fun_prop

theorem continuous_blockW {w : G → ℝ} (hw : Continuous w) (X : TSite 4 n) (p : Plane) :
    Continuous fun U : TLink 4 (2 * n) → G => blockW w U X p := by
  unfold blockW
  exact (((hw.comp (continuous_thol _)).mul (hw.comp (continuous_thol _))).mul
    (hw.comp (continuous_thol _))).mul (hw.comp (continuous_thol _))

/-- **Two fine links per coarse link collapse to their product**, by left invariance. -/
theorem integral_shear (Φ : (TLink 4 n → G) → ℝ) (hΦ : Continuous Φ) :
    ∫ A, Φ (fun l => (A l).1 * (A l).2)
        ∂(Measure.pi fun _ : TLink 4 n => (probHaar G).prod (probHaar G))
      = ∫ V, Φ V ∂(Measure.pi fun _ : TLink 4 n => probHaar G) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow G G (TLink 4 n)
    (fun _ => probHaar G) (fun _ => probHaar G)
  have h1 := hmp.integral_comp' (fun VV : (TLink 4 n → G) × (TLink 4 n → G) => Φ (VV.1 * VV.2))
  calc ∫ A, Φ (fun l => (A l).1 * (A l).2)
        ∂(Measure.pi fun _ : TLink 4 n => (probHaar G).prod (probHaar G))
      = ∫ A, (fun VV : (TLink 4 n → G) × (TLink 4 n → G) => Φ (VV.1 * VV.2))
          (MeasurableEquiv.arrowProdEquivProdArrow G G (TLink 4 n) A)
          ∂(Measure.pi fun _ : TLink 4 n => (probHaar G).prod (probHaar G)) := rfl
    _ = ∫ VV, Φ (VV.1 * VV.2) ∂((Measure.pi fun _ : TLink 4 n => probHaar G).prod
          (Measure.pi fun _ : TLink 4 n => probHaar G)) := h1
    _ = ∫ V, Φ V ∂(Measure.pi fun _ : TLink 4 n => probHaar G) := by
      rw [integral_prod _ (integrable_of_continuous (f := fun VV : (TLink 4 n → G) × (TLink 4 n → G) =>
        Φ (VV.1 * VV.2)) (hΦ.comp (continuous_fst.mul continuous_snd)))]
      simp only [integral_mul_left_eq_self (fun V => Φ V), integral_const, probReal_univ, one_smul]

/-- **The moved-torus decimation, for any compact group.** On the side-`2n` torus, the product over the
`2 × 2` blocks of the coordinate planes at even transverse position of the weights `w` of their four
plaquettes, integrated against product Haar measure on all fine links, is the side-`n` integral of the
product over coarse plaquettes of the fourfold convolution `(w ⋆ w) ⋆ (w ⋆ w)`. -/
theorem decimation (w : G → ℝ) (hw : Continuous w) (hwc : ∀ k x, w (k * x * k⁻¹) = w x) :
    ∫ U, ∏ X : TSite 4 n, ∏ p : Plane, blockW w U X p
        ∂(Measure.pi fun _ : TLink 4 (2 * n) => probHaar G)
      = ∫ V, ∏ X : TSite 4 n, ∏ p : Plane, conv (conv w w) (conv w w) (thol ((p.1.1, p.1.2), X) V)
          ∂(Measure.pi fun _ : TLink 4 n => probHaar G) := by
  set K4 := conv (conv w w) (conv w w) with hK4
  have hK4c : Continuous K4 := continuous_conv (continuous_conv hw hw) (continuous_conv hw hw)
  have hF : Continuous fun U : TLink 4 (2 * n) → G => ∏ X : TSite 4 n, ∏ p : Plane, blockW w U X p :=
    continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ => continuous_blockW hw X p
  rw [← (measurePreserving_asm (n := n) (G := G)).map_eq,
    integral_map measurable_asm.aemeasurable hF.aestronglyMeasurable]
  simp_rw [blockW_asm]
  -- the integrand depends on the line and block parts only
  set Bk : (TLink 4 n → G × G) → TSite 4 n → Plane → (G × G) × (G × G) → ℝ := fun A X p q =>
    w ((A (p.1.1, X)).1 * q.2.1 * q.1.1⁻¹ * ((A (p.1.2, X)).1)⁻¹)
      * w ((A (p.1.1, X)).2 * (A (p.1.2, tshift p.1.1 X)).1 * q.1.2⁻¹ * q.2.1⁻¹)
      * w (q.1.1 * q.2.2 * ((A (p.1.1, tshift p.1.2 X)).1)⁻¹ * ((A (p.1.2, X)).2)⁻¹)
      * w (q.1.2 * (A (p.1.2, tshift p.1.1 X)).2 * ((A (p.1.1, tshift p.1.2 X)).2)⁻¹ * q.2.2⁻¹)
    with hBk
  set H : (TLink 4 n → G × G) × (TSite 4 n × Plane → (G × G) × (G × G)) → ℝ :=
    fun ab => ∏ X : TSite 4 n, ∏ p : Plane, Bk ab.1 X p (ab.2 (X, p)) with hH
  have hHc : Continuous H := by
    refine continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ => ?_
    simp only [hBk]
    fun_prop
  rw [show (fun c : Cfg n G => ∏ X : TSite 4 n, ∏ p : Plane, Bk c.1.1 X p (c.1.2 (X, p)))
      = fun c => H c.1 from rfl, integral_fun_fst H, probReal_univ, one_smul,
    integral_prod H (integrable_of_continuous hHc)]
  -- the blocks, one at a time
  have hB : ∀ A : TLink 4 n → G × G,
      ∫ B, H (A, B) ∂(Measure.pi fun _ : TSite 4 n × Plane =>
        ((probHaar G).prod (probHaar G)).prod ((probHaar G).prod (probHaar G)))
      = ∏ X : TSite 4 n, ∏ p : Plane, K4 (thol ((p.1.1, p.1.2), X) fun l => (A l).1 * (A l).2) := by
    intro A
    have e : (fun B : TSite 4 n × Plane → (G × G) × (G × G) => H (A, B))
        = fun B => ∏ xp : TSite 4 n × Plane, Bk A xp.1 xp.2 (B xp) := by
      funext B
      simp only [hH]
      rw [Fintype.prod_prod_type]
    rw [e, integral_fintype_prod_eq_prod (fun (xp : TSite 4 n × Plane) q => Bk A xp.1 xp.2 q), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun X _ => Finset.prod_congr rfl fun p _ => ?_
    simp only [hBk]
    rw [block_integral w hw hwc]
    rfl
  simp_rw [hB]
  exact integral_shear (fun V => ∏ X : TSite 4 n, ∏ p : Plane, K4 (thol ((p.1.1, p.1.2), X) V))
    (continuous_finsetProd _ fun X _ => continuous_finsetProd _ fun p _ =>
      hK4c.comp (continuous_thol _))

end MassGap.MovedTorusDecimation

#print axioms MassGap.MovedTorusDecimation.measurePreserving_asm
#print axioms MassGap.MovedTorusDecimation.block_integral
#print axioms MassGap.MovedTorusDecimation.decimation
