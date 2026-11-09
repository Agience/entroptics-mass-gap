import Mathlib
import MassGap.TransContSU

/-!
# The sector's link from the composites' link

`TIn` places the tensor among the composites: an index `e α` with classical monomial
`Re tr F_{α₀α₁} F_{α₂α₃}` and renormalised field `∑_b M k α b · op b`. This module builds the
sector's vectors from the composites' vectors through that index,

  `wOfC e wC P = ∑_{α : Fin n → Idx4} (∏ᵢ cᵢ(αᵢ)) • wC (P_α)`,

where `P_α` keeps the test functions of `P` and replaces the data by `e (α i)` (`monoAt`), and proves
from `LinkC` and the first two clauses of `TIn`:

* the Gram identity `⟪wOfC P, wOfC Q⟫ = kernT P Q` (`gram_wOfC`). At each step the sector's reading
  is the combination `∑_α ∏ᵢ cᵢ(αᵢ) · latC(e α, f)` (`latT_eq_sum_latC`, from the linearity of the
  smearing and of the state in the field); the reflected slots carry `reflC`, whose sign at `α` is
  `(−1)^{#{j | αⱼ = τ}}`, the reflection sign `sgnC` of the composite `e α` (`ctau_tensor`);
* the shift and the vacuum, term by term (`wOfC_shift`, `wOfC_empty`);
* `HLs X (wOfC e wC) ≤ HLC X wC` (`hLs_le_hLC`), the third clause of `TIn`.

`clayStatementAt_of_inputs_L` is `TransContSU.clayStatementAt_of_inputs_TC` at `w := wOfC e wC`,
with `hL` replaced by its cross-reading conjunct and `hTI` by its first two clauses.

The second part: a channel matrix commuting with the hypercubic group sends `ε` to a multiple of `ε`
(`zAct_epsC`). Sign flips force every axis to occur among the indices of a non-zero component,
so the component vanishes off the permutations; permutation matrices give `t (σ⁻¹ ∘ β) = sgn σ · t β`.
`topNorm_of_channelTie` is `TopNorm` from `ChannelTie` and the limit of the identity component, and
`clayStatementAt_of_inputs_L'` is `clayStatementAt_of_inputs_L` with `TopNorm` replaced by that
limit.

DERIVED (module-wide): `0` the reflection plane, the empty monomial's length, the vanishing values;
`1` the empty product, the unit coefficient and the unit entries; `-1` the sign of a flipped axis;
`2` the limit of `TopNorm`; `4` the dimension.
-/

noncomputable section

namespace MassGap.LinkReduce

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The vectors of the sector from the composites -/

/-- The composite monomial of `P` at the components `α`: the test functions of `P`, the data
`e (α i)`. -/
def monoAt {Ix : Type} {τ : Fin 4} (e : Idx4 → Ix) (P : TSep τ) (α : Fin P.1.1 → Idx4) :
    TSepG Ix τ :=
  ⟨⟨P.1.1, fun i => (e (α i), (P.1.2 i).2)⟩,
    ⟨fun i => P.2.1 i, P.2.2.imp fun _ hd => ⟨hd.1, fun i y hy => hd.2.1 i y hy,
      fun i j hij => hd.2.2 i j hij⟩⟩⟩

/-- The coefficient of the components `α` in `P`: `∏ᵢ cᵢ(αᵢ)`. -/
def coefAt {τ : Fin 4} (P : TSep τ) (α : Fin P.1.1 → Idx4) : ℝ := ∏ i, (P.1.2 i).1 (α i)

/-- **The sector's vector from the composites' vectors**: `∑_α (∏ᵢ cᵢ(αᵢ)) • wC (P_α)`. -/
def wOfC {Ix : Type} {τ : Fin 4} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : Idx4 → Ix) (wC : TSepG Ix τ → H) (P : TSep τ) : H :=
  ∑ α : Fin P.1.1 → Idx4, ((coefAt P α : ℝ) : ℂ) • wC (monoAt e P α)

/-! ## 2. The sector's reading as a combination of the composites' readings -/

/-- The smearing is linear in the field. -/
theorem smear_sum {a : ℝ} (ha : 0 < a) {B : Type} (s : Finset B) (c : B → ℝ)
    (F : B → C(Cfg N, ℝ)) (f : TestFn) :
    smear a (∑ b ∈ s, c b • F b) f = ∑ b ∈ s, c b • smear a (F b) f := by
  obtain ⟨R, M, hf⟩ := f.2
  have e1 : ∀ G : C(Cfg N, ℝ),
      smear a G f = ∑ x ∈ box ⌈R / a⌉₊, (a ^ 4 * f.1 (site a x)) • transObs x G :=
    fun G => smear_eq_sum ha G f hf (Finset.Subset.refl _)
  simp only [e1, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
  rw [smul_comm]

/-- The connected renormalised field of a composite whose field is `∑_b M k α b · op b` is
`∑_b M k α b · (op b − ν_k(op b))`. -/
theorem cField_field (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (k : ℕ) (x : C.Ix)
    (α : Idx4) (hren : (C.ren k x).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (f : TestFn) :
    (cField hN C k (x, f)).1.1 = ∑ b, ρ.M k α b • (locField hN ρ k b f).1.1 := by
  show (C.ren k x).1 - stateK hN k (C.ren k x).1 • (1 : C(Cfg N, ℝ))
    = ∑ b, ρ.M k α b • ((ρ.op b).1 - stateK hN k (ρ.op b).1 • (1 : C(Cfg N, ℝ)))
  rw [hren, MassGap.DLRLimit.State.map_sum]
  simp only [MassGap.DLRLimit.State.map_smul, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]

/-- **The composites' reading at the components `α`** expands over the basis. -/
theorem latC_expand (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (k : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (x : ι → C.Ix) (α : ι → Idx4)
    (hren : ∀ i, (C.ren k (x i)).1 = ∑ b, ρ.M k (α i) b • (ρ.op b).1) (f : ι → TestFn) :
    latC hN C k (fun i => (x i, f i))
      = ∑ b : ι → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSk hN k (fun i => locField hN ρ k (b i) (f i)) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  show stateK hN k (∏ i, smear (dySpacing N k) (cField hN C k (x i, f i)).1.1 (f i))
    = ∑ b : ι → ρ.B, (∏ i, ρ.M k (α i) (b i))
        * stateK hN k (∏ i, smear (dySpacing N k) (locField hN ρ k (b i) (f i)).1.1 (f i))
  have h1 : ∀ i, smear (dySpacing N k) (cField hN C k (x i, f i)).1.1 (f i)
      = ∑ b, ρ.M k (α i) b • smear (dySpacing N k) (locField hN ρ k b (f i)).1.1 (f i) :=
    fun i => by rw [cField_field hN ρ C k (x i) (α i) (hren i), smear_sum ha]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Fintype.prod_sum, MassGap.DLRLimit.State.map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_smul, MassGap.DLRLimit.State.map_smul]

/-- **The sector's reading at step `k` is `∑_α ∏ᵢ cᵢ(αᵢ) · latC((e αᵢ, fᵢ)ᵢ)`**, from the second
clause of `TIn` at step `k`. -/
theorem latT_eq_sum_latC (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (k : ℕ) (hren : ∀ α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) :
    latT hN ρ k F
      = ∑ α : ι → Idx4, (∏ i, (F i).1 (α i)) * latC hN C k (fun i => (e (α i), (F i).2)) := by
  have h2 : ∀ α : ι → Idx4, latC hN C k (fun i => (e (α i), (F i).2))
      = ∑ b : ι → ρ.B, (∏ i, ρ.M k (α i) (b i))
          * latSk hN k (fun i => locField hN ρ k (b i) (F i).2) :=
    fun α => latC_expand hN ρ C k (fun i => e (α i)) α (fun i => hren (α i)) (fun i => (F i).2)
  unfold latT
  simp only [h2, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (ι → Idx4)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h3 : (∏ i, mixC ρ k (F i).1 (b i))
      = ∑ α : ι → Idx4, ∏ i, ((F i).1 (α i) * ρ.M k (α i) (b i)) :=
    Fintype.prod_sum (fun i α' => (F i).1 α' * ρ.M k α' (b i))
  rw [h3, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-! ## 3. The kernel -/

/-- The reflection count of the tensor's monomial: `ctau τ` of `Re tr F_{α₀α₁} F_{α₂α₃}` is the
number of indices equal to `τ`. -/
theorem ctau_tensor (τ : Fin 4) (a : Idx4) :
    ctau τ [([([], a 0, a 1), ([], a 2, a 3)], true)]
      = (Finset.univ.filter (fun j => a j = τ)).card := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  simp only [ctau, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.count_nil]
  ring

/-- `ΘP ∪ Q` at the components `γ` is `ΘP_{γ∘inl} ∪ Q_{γ∘inr}` of the composites. -/
theorem pairC_monoAt (C : Composites N) {τ : Fin 4}
    (e : Idx4 → C.Ix) (P Q : TSep τ) (γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4) :
    (fun s => (e (γ s), (pairT τ P.1 Q.1 s).2))
      = pairC C τ (monoAt e P (fun i => γ (Sum.inl i))).1 (monoAt e Q (fun j => γ (Sum.inr j))).1 :=
  funext fun s => by rcases s with i | j <;> rfl

/-- **The lattice sequence of `ΘP ∪ Q` converges** to `∑_γ ∏ₛ cₛ(γₛ) · S_C(ΘP_{γ∘inl} ∪ Q_{γ∘inr})`,
from the second clause of `TIn` and the convergence clause of `LinkC`. -/
theorem tendsto_latT_pairT (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) {τ : Fin 4}
    (e : Idx4 → C.Ix) (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hconv : ∀ P Q : TSepG C.Ix τ, Tendsto (fun k => latC hN C k (pairC C τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (contC hN C (pairC C τ P.1 Q.1))))
    (P Q : TSep τ) :
    Tendsto (fun k => latT hN ρ k (pairT τ P.1 Q.1)) (ultra : Filter ℕ)
      (𝓝 (∑ γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4, (∏ s, (pairT τ P.1 Q.1 s).1 (γ s))
        * contC hN C (pairC C τ (monoAt e P (fun i => γ (Sum.inl i))).1
            (monoAt e Q (fun j => γ (Sum.inr j))).1))) := by
  have hk : (fun k => latT hN ρ k (pairT τ P.1 Q.1))
      = fun k => ∑ γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4, (∏ s, (pairT τ P.1 Q.1 s).1 (γ s))
        * latC hN C k (pairC C τ (monoAt e P (fun i => γ (Sum.inl i))).1
            (monoAt e Q (fun j => γ (Sum.inr j))).1) := funext fun k => by
    rw [latT_eq_sum_latC hN ρ C e k (hren k)]
    exact Finset.sum_congr rfl fun γ _ => by rw [pairC_monoAt C e P Q γ]; rfl
  rw [hk]
  exact tendsto_finsetSum _ fun γ _ => (hconv _ _).const_mul _

/-- **The sector's kernel is the composites' kernel at the components**:
`kernT P Q = ∑_{α, β} cP(α) cQ(β) kernC(P_α, Q_β)`, from the first two clauses of `TIn` and the
convergence clause of `LinkC`. -/
theorem kernT_eq (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) {τ : Fin 4}
    (e : Idx4 → C.Ix) (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hconv : ∀ P Q : TSepG C.Ix τ, Tendsto (fun k => latC hN C k (pairC C τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (contC hN C (pairC C τ P.1 Q.1))))
    (P Q : TSep τ) :
    kernT hN ρ τ P Q = ∑ α : Fin P.1.1 → Idx4, ∑ β : Fin Q.1.1 → Idx4,
      coefAt P α * coefAt Q β * kernC hN C τ (monoAt e P α) (monoAt e Q β) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  rw [kernT, contT, (tendsto_latT_pairT hN ρ C e hren hconv P Q).limUnder_eq,
    ← (Equiv.sumArrowEquivProdArrow (Fin P.1.1) (Fin Q.1.1) Idx4).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  show (∏ s, (pairT τ P.1 Q.1 s).1 (Sum.elim α β s))
      * contC hN C (pairC C τ (monoAt e P α).1 (monoAt e Q β).1) = _
  have hL : ∀ i, (pairT τ P.1 Q.1 (Sum.inl i)).1 (Sum.elim α β (Sum.inl i))
      = (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) * (P.1.2 i).1 (α i) := fun i => by
    rw [he1 (α i), ctau_tensor τ (α i)]
    rfl
  have hR : ∀ j, (pairT τ P.1 Q.1 (Sum.inr j)).1 (Sum.elim α β (Sum.inr j))
      = (Q.1.2 j).1 (β j) := fun j => rfl
  have hS : sgnC C τ (monoAt e P α).1 = ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) := rfl
  rw [Fintype.prod_sum_type]
  simp only [hL, hR]
  rw [Finset.prod_mul_distrib, kernC, hS]
  simp only [coefAt]
  ring

/-- **The Gram identity** of `wOfC e wC`, from `LinkC` and the first two clauses of `TIn`. -/
theorem gram_wOfC (hN : N ≠ 0) (ρ : RenormMix N) (C : Composites N) {τ : Fin 4} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (wC : TSepG C.Ix τ → H)
    (e : Idx4 → C.Ix) (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hG : ∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latC hN C k (pairC C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contC hN C (pairC C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernC hN C τ P Q : ℂ))
    (P Q : TSep τ) :
    inner ℂ (wOfC e wC P) (wOfC e wC Q) = (kernT hN ρ τ P Q : ℂ) := by
  rw [kernT_eq hN ρ C e he1 hren (fun P Q => (hG P Q).1) P Q]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  unfold wOfC
  rw [sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_smul_left, inner_sum, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [inner_smul_right, (hG _ _).2]
  ring

/-! ## 4. Shift, vacuum, and the space of the sector -/

/-- **The shift**, term by term from the shift clause of `LinkC`. -/
theorem wOfC_shift (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {Ix : Type} (e : Idx4 → Ix) (wC : TSepG Ix τ → X.base.H)
    (hS : ∀ (m : ℕ) (P : TSepG Ix τ), wC (shiftT hN τ m P) = X.base.time (dySpacing N m) (wC P))
    (m : ℕ) (P : TSep τ) :
    wOfC e wC (shiftT hN τ m P) = X.base.time (dySpacing N m) (wOfC e wC P) := by
  unfold wOfC
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, ← hS]
  rfl

/-- **The vacuum**: the empty monomial has the single component, with coefficient `1`. -/
theorem wOfC_empty {τ : Fin 4} {Ix : Type} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : Idx4 → Ix) (wC : TSepG Ix τ → H) {v : H}
    (h0 : wC (emptyG Ix τ) = v) : wOfC e wC (emptyT τ) = v := by
  haveI : IsEmpty (Fin (emptyT τ).1.1) := Fin.isEmpty
  have hm : ∀ α, monoAt e (emptyT τ) α = emptyG Ix τ :=
    fun α => Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun i => (Nat.not_lt_zero _ i.2).elim)))
  have hc : ∀ α, coefAt (emptyT τ) α = 1 :=
    fun α => by simp only [coefAt, Finset.univ_eq_empty, Finset.prod_empty]
  unfold wOfC
  simp only [hm, hc, Complex.ofReal_one, one_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, h0]

/-- **The sector's space lies in the composites' space**: each `wOfC e wC P` is a finite
combination of the vectors `wC`. -/
theorem hLs_le_hLC {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) {C : Composites N} (e : Idx4 → C.Ix)
    (wC : TSepG C.Ix τ → X.base.H) : HLs X (wOfC e wC) ≤ HLC X wC := by
  unfold HLs HLC HLg
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨P, rfl⟩
  unfold wOfC
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **`LinkHS` at `wOfC e wC`** from `LinkC`, the first two clauses of `TIn` at `e`, and the
cross-reading conjunct of `LinkHS`. -/
theorem linkHS_of_comp (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hDr : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4}
    {r : ℝ} (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (C : Composites N)
    (wC : TSepG C.Ix τ → X.base.H) (hLC : LinkC hN X C wC) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hX : ∀ (P : TSep τ) (Q : MarginMonoD N D τ r),
      Tendsto (fun k => mixLatT hN ρ (energy0 W D hDr) τ k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT hN ρ (energy0 W D hDr) τ P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (X.cvec Q) = (mixT hN ρ (energy0 W D hDr) τ P.1 Q.1.1 : ℂ)) :
    LinkHS hN W D hDr X ρ (wOfC e wC) :=
  ⟨gram_wOfC hN ρ C wC e he1 he2 hLC.1, fun m P => wOfC_shift hN e wC hLC.2.1 m P,
    wOfC_empty e wC hLC.2.2, hX⟩

/-- **`TIn` at `wOfC e wC`** from its first two clauses at `e`. -/
theorem tIn_of_comp {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (C : Composites N)
    (wC : TSepG C.Ix τ → X.base.H) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) :
    TIn ρ C X (wOfC e wC) wC :=
  ⟨e, he1, he2, hLs_le_hLC X e wC⟩

/-! ## 5. The capstone with the sector's link from the composites' link -/

/-- **`ClayStatementAt` from the inputs of `TransContSU.clayStatementAt_of_inputs_TC` at
`w := wOfC e wC`**, with `hL` replaced by its cross-reading conjunct `hX` and `hTI` by its first two
clauses `he1`, `he2` at `e`. The Gram, shift and vacuum conjuncts of `hL` are `linkHS_of_comp`; the
third clause of `hTI` is `hLs_le_hLC`. -/
theorem clayStatementAt_of_inputs_L (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z)
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1
      = ∑ b, (mixOfZ B op m Z).M k α b • ((mixOfZ B op m Z).op b).1)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N))
          0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).cvec Q)
          = (mixT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1
            : ℂ))
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) Cs wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  TransContSU.clayStatementAt_of_inputs_TC hN2 hN W ht hU hphys hNT hfar op m Z hZ hD hRie b0 κ
    htr hop hZtie h0 hCov G hK hAF hNG hND (wOfC e wC)
    (linkHS_of_comp hN W (SymPlaqClass N) (symPlaq_refl N) _ (mixOfZ B op m Z) Cs wC hLC e he1
      he2 hX)
    Cs wC hCT hWard hCD hCO hLC (tIn_of_comp _ (mixOfZ B op m Z) Cs wC e he1 he2)

/-! ## 6. A channel matrix commuting with the hypercubic group fixes the line of `ε` -/

/-- The sign of the axis `μ`: `-1` at `μ`, `1` elsewhere. -/
def dsign (μ : Fin 4) : Fin 4 → ℝ := fun ν => if ν = μ then -1 else 1

/-- The permutation matrix `e_j ↦ e_{σ j}`. -/
def permM (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if i = σ j then 1 else 0

theorem isHyp_dsign (μ : Fin 4) : IsHyp (Matrix.diagonal (dsign μ)) := by
  refine ⟨?_, fun i j => ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff', Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext ν
    simp only [dsign]
    split_ifs <;> norm_num
  · simp only [Matrix.diagonal_apply, dsign]
    split_ifs <;> norm_num

theorem isHyp_permM (σ : Equiv.Perm (Fin 4)) : IsHyp (permM σ) := by
  refine ⟨?_, fun i j => ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff']
    ext i j
    simp [permM, Matrix.mul_apply, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · simp only [permM, Matrix.of_apply]
    split_ifs <;> norm_num

/-- A diagonal matrix acts on a component by the product of its entries at the indices. -/
theorem rotC_diagonal (d : Fin 4 → ℝ) (c : Idx4 → ℝ) (β : Idx4) :
    rotC (Matrix.diagonal d) c β = (∏ j, d (β j)) * c β := by
  unfold rotC tcoef
  rw [Finset.sum_eq_single β]
  · simp only [Matrix.diagonal_apply_eq]
    ring
  · intro α _ hα
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
      by_contra h
      exact hα (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    have h0 : Matrix.diagonal d (β j) (α j) = 0 := Matrix.diagonal_apply_ne _ (Ne.symm hj)
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  · intro h
    exact absurd (Finset.mem_univ β) h

/-- A permutation matrix acts on components by `c ↦ c ∘ σ⁻¹`. -/
theorem rotC_permM (σ : Equiv.Perm (Fin 4)) (c : Idx4 → ℝ) (β : Idx4) :
    rotC (permM σ) c β = c (fun j => σ.symm (β j)) := by
  unfold rotC tcoef
  rw [Finset.sum_eq_single (fun j => σ.symm (β j))]
  · simp [permM]
  · intro α _ hα
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ σ.symm (β j) := by
      by_contra h
      exact hα (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
    simp only [permM, Matrix.of_apply]
    exact if_neg fun h => hj (by rw [h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem epsC_of_bij {γ : Idx4} (h : Function.Bijective γ) :
    epsC γ = (((Equiv.Perm.sign (Equiv.ofBijective γ h) : ℤˣ) : ℤ) : ℝ) := by
  simp only [epsC, dif_pos h]

theorem epsC_of_not_bij {γ : Idx4} (h : ¬ Function.Bijective γ) : epsC γ = 0 := by
  simp only [epsC, dif_neg h]

/-- `ε (σ⁻¹ ∘ γ) = sgn σ · ε γ`. -/
theorem epsC_symm_comp (σ : Equiv.Perm (Fin 4)) (γ : Idx4) :
    epsC (fun j => σ.symm (γ j)) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * epsC γ := by
  by_cases h : Function.Bijective γ
  · have h' : Function.Bijective (fun j => σ.symm (γ j)) := σ.symm.bijective.comp h
    rw [epsC_of_bij h', epsC_of_bij h]
    have e : Equiv.ofBijective (fun j => σ.symm (γ j)) h' = σ⁻¹ * Equiv.ofBijective γ h :=
      Equiv.ext fun _ => rfl
    rw [e, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · have h' : ¬ Function.Bijective (fun j => σ.symm (γ j)) := fun hb => h (by
      have hγ : γ = fun j => σ ((fun j => σ.symm (γ j)) j) :=
        funext fun j => (σ.apply_symm_apply _).symm
      rw [hγ]
      exact σ.bijective.comp hb)
    rw [epsC_of_not_bij h', epsC_of_not_bij h, mul_zero]

theorem zAct_neg (Zm : Idx4 → Idx4 → ℝ) (c : Idx4 → ℝ) :
    zAct Zm (fun γ => -c γ) = fun β => -zAct Zm c β := by
  funext β
  simp only [zAct, neg_mul, Finset.sum_neg_distrib]

theorem zAct_smul (Zm : Idx4 → Idx4 → ℝ) (s : ℝ) (c : Idx4 → ℝ) :
    zAct Zm (fun γ => s * c γ) = fun β => s * zAct Zm c β := by
  funext β
  simp only [zAct, Finset.mul_sum, mul_assoc]

/-- A sign flip sends `ε` to `−ε`. -/
theorem rotC_dsign_epsC (μ : Fin 4) :
    rotC (Matrix.diagonal (dsign μ)) epsC = fun γ => -epsC γ := by
  funext γ
  rw [rotC_diagonal]
  by_cases hγ : Function.Bijective γ
  · have hp : ∏ j, dsign μ (γ j) = ∏ ν, dsign μ ν :=
      Fintype.prod_bijective γ hγ (fun j => dsign μ (γ j)) (dsign μ) (fun _ => rfl)
    have hm : ∏ ν, dsign μ ν = -1 := by simp [dsign, Finset.prod_ite_eq']
    rw [hp, hm]
    ring
  · rw [epsC_of_not_bij hγ]
    ring

/-- A permutation matrix sends `ε` to `sgn σ · ε`. -/
theorem rotC_permM_epsC (σ : Equiv.Perm (Fin 4)) :
    rotC (permM σ) epsC = fun γ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * epsC γ :=
  funext fun γ => by rw [rotC_permM, epsC_symm_comp]

/-- **A channel matrix commuting with the hypercubic group sends `ε` to a multiple of `ε`**: the
multiple is its identity component. -/
theorem zAct_epsC (Zm : Idx4 → Idx4 → ℝ)
    (hc : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, IsHyp A → ∀ c, zAct Zm (rotC A c) = rotC A (zAct Zm c)) :
    zAct Zm epsC = zAct Zm epsC id • epsC := by
  funext β
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hβ : Function.Bijective β
  · have h := congrFun (hc _ (isHyp_permM (Equiv.ofBijective β hβ)) epsC) β
    rw [rotC_permM_epsC, zAct_smul, rotC_permM] at h
    dsimp only at h
    have hid : (fun j => (Equiv.ofBijective β hβ).symm (β j)) = id :=
      funext fun j => Equiv.ofBijective_symm_apply_apply β hβ j
    rw [hid] at h
    have hs : (((Equiv.Perm.sign (Equiv.ofBijective β hβ) : ℤˣ) : ℤ) : ℝ)
        * (((Equiv.Perm.sign (Equiv.ofBijective β hβ) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective β hβ)) with h1 | h1 <;>
        simp [h1]
    rw [epsC_of_bij hβ, ← h]
    linear_combination (-(zAct Zm epsC β)) * hs
  · rw [epsC_of_not_bij hβ, mul_zero]
    by_contra hne
    apply hβ
    refine Finite.surjective_iff_bijective.mp fun μ => ?_
    by_contra hμ
    have hμ' : ∀ j, β j ≠ μ := fun j hj => hμ ⟨j, hj⟩
    have h := congrFun (hc _ (isHyp_dsign μ) epsC) β
    rw [rotC_dsign_epsC, zAct_neg, rotC_diagonal] at h
    dsimp only at h
    have h1 : ∏ j, dsign μ (β j) = 1 := Finset.prod_eq_one fun j _ => by simp [dsign, hμ' j]
    rw [h1, one_mul] at h
    exact hne (by linarith)

/-- **`TopNorm` from the channel tie and the limit of the identity component**: the first clause of
`TopNorm` holds at `zq k = zAct (Z k) ε id` by `zAct_epsC`. -/
theorem topNorm_of_channelTie (ρ : RenormMix N) (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ)
    (hCT : ChannelTie ρ Mb Zc)
    (hlim : Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2)) :
    TopNorm N Zc :=
  ⟨fun k => zAct (Zc k) epsC id, fun k => zAct_epsC (Zc k) (hCT.2.1 k), hlim⟩

/-- **`clayStatementAt_of_inputs_L` with `TopNorm` replaced by the limit of the identity component**
`zAct (Zc k) ε id · a_k⁴ → 2`; the first clause of `TopNorm` is `zAct_epsC` from the second clause of
`ChannelTie`. -/
theorem clayStatementAt_of_inputs_L' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z)
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1
      = ∑ b, (mixOfZ B op m Z).M k α b • ((mixOfZ B op m Z).op b).1)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N))
          0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).cvec Q)
          = (mixT hN (mixOfZ B op m Z) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1
            : ℂ))
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) Cs wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_of_inputs_L hN2 hN W ht hU hphys hNT hfar op m Z hZ hD hRie b0 κ htr hop hZtie
    h0 hCov G hK hAF hNG hND Cs wC e he1 he2 hX
    (let ⟨Mb, Zc, h1, h2⟩ := hCT
     ⟨Mb, Zc, h1, topNorm_of_channelTie (mixOfZ B op m Z) Mb Zc h1 h2⟩)
    hWard hCD hCO hLC

end MassGap.LinkReduce

end

#print axioms MassGap.LinkReduce.smear_sum
#print axioms MassGap.LinkReduce.cField_field
#print axioms MassGap.LinkReduce.latC_expand
#print axioms MassGap.LinkReduce.latT_eq_sum_latC
#print axioms MassGap.LinkReduce.ctau_tensor
#print axioms MassGap.LinkReduce.pairC_monoAt
#print axioms MassGap.LinkReduce.tendsto_latT_pairT
#print axioms MassGap.LinkReduce.kernT_eq
#print axioms MassGap.LinkReduce.gram_wOfC
#print axioms MassGap.LinkReduce.wOfC_shift
#print axioms MassGap.LinkReduce.wOfC_empty
#print axioms MassGap.LinkReduce.hLs_le_hLC
#print axioms MassGap.LinkReduce.linkHS_of_comp
#print axioms MassGap.LinkReduce.tIn_of_comp
#print axioms MassGap.LinkReduce.clayStatementAt_of_inputs_L
#print axioms MassGap.LinkReduce.isHyp_dsign
#print axioms MassGap.LinkReduce.isHyp_permM
#print axioms MassGap.LinkReduce.rotC_diagonal
#print axioms MassGap.LinkReduce.rotC_permM
#print axioms MassGap.LinkReduce.epsC_symm_comp
#print axioms MassGap.LinkReduce.rotC_dsign_epsC
#print axioms MassGap.LinkReduce.rotC_permM_epsC
#print axioms MassGap.LinkReduce.zAct_epsC
#print axioms MassGap.LinkReduce.topNorm_of_channelTie
#print axioms MassGap.LinkReduce.clayStatementAt_of_inputs_L'
