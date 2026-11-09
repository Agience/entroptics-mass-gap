import Mathlib
import MassGap.CompReduceG
import MassGap.LinkReduce

/-!
# MassGap.LinkReduceG — the sector's link from the composites' link, over `G`

The mirror of `LinkReduce` over a schedule `S` of a `GaugeGroup G`. The sector's vectors are built
from the composites' vectors through an index map `e` (`LinkReduce.wOfC`, group-free):

  `wOfC e wC P = ∑_{α : Fin n → Idx4} (∏ᵢ cᵢ(αᵢ)) • wC (P_α)`.

| `LinkReduce` (`SU(N)`) | here (any `G`, `S`) | input it reads |
|---|---|---|
| `latT_eq_sum_latC` | `CompReduceG.latTG_expand` | the second clause of `e` |
| `pairC_monoAt`, `tendsto_latT_pairT`, `kernT_eq` | `pairCG_monoAt`, `tendsto_latTG_pairT`, `kernTG_eq` | the convergence clause of `LinkCG` |
| `gram_wOfC` | `gram_wOfCG` | the first clause of `LinkCG`, both clauses of `e` |
| `wOfC_shift` | `wOfC_shiftG` | the shift clause of `LinkCG` |
| `hLs_le_hLC` | `hLs_le_hLCG` | none |
| `linkHS_of_comp`, `tIn_of_comp` | `linkHSG_of_comp`, `tInG_of_comp` | `LinkCG`, the clauses of `e`, `hX` |
| `topNorm_of_channelTie` | `topNormG_of_channelTie` | `ChannelTieG`, the limit of the identity component |

The group-free parts of `LinkReduce` (`monoAt`, `coefAt`, `wOfC`, `ctau_tensor`, `wOfC_empty`,
`zAct_epsC`) are used as they are.

DERIVED (module-wide): `0` the vanishing values; `1` the empty product and the unit coefficient;
`-1` the sign of a reflected index; `4` the dimension.
-/

noncomputable section

namespace MassGap.LinkReduceG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.CompReduceG MassGap.LinkReduce Filter
open scoped Topology Matrix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## 1. The kernel -/

/-- `ΘP ∪ Q` at the components `γ` is `ΘP_{γ∘inl} ∪ Q_{γ∘inr}` of the composites.

DERIVED: no numeral. -/
theorem pairCG_monoAt (C : CompositesG G) {τ : Fin 4}
    (e : Idx4 → C.Ix) (P Q : TSep τ) (γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4) :
    (fun s => (e (γ s), (pairT τ P.1 Q.1 s).2))
      = pairCG C τ (monoAt e P (fun i => γ (Sum.inl i))).1
          (monoAt e Q (fun j => γ (Sum.inr j))).1 :=
  funext fun s => by rcases s with i | j <;> rfl

/-- **The lattice sequence of `ΘP ∪ Q` converges** to
`∑_γ ∏ₛ cₛ(γₛ) · S_C(ΘP_{γ∘inl} ∪ Q_{γ∘inr})`, from the second clause of `e` and the convergence
clause of `LinkCG`. DERIVED: no numeral. -/
theorem tendsto_latTG_pairT (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) {τ : Fin 4}
    (e : Idx4 → C.Ix) (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hconv : ∀ P Q : TSepG C.Ix τ, Tendsto (fun k => latCG S C k (pairCG C τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (contCG S C (pairCG C τ P.1 Q.1))))
    (P Q : TSep τ) :
    Tendsto (fun k => latTG S ρ k (pairT τ P.1 Q.1)) (ultra : Filter ℕ)
      (𝓝 (∑ γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4, (∏ s, (pairT τ P.1 Q.1 s).1 (γ s))
        * contCG S C (pairCG C τ (monoAt e P (fun i => γ (Sum.inl i))).1
            (monoAt e Q (fun j => γ (Sum.inr j))).1))) := by
  have hk : (fun k => latTG S ρ k (pairT τ P.1 Q.1))
      = fun k => ∑ γ : Fin P.1.1 ⊕ Fin Q.1.1 → Idx4, (∏ s, (pairT τ P.1 Q.1 s).1 (γ s))
        * latCG S C k (pairCG C τ (monoAt e P (fun i => γ (Sum.inl i))).1
            (monoAt e Q (fun j => γ (Sum.inr j))).1) := funext fun k => by
    rw [latTG_expand S ρ C e hren k]
    exact Finset.sum_congr rfl fun γ _ => by rw [pairCG_monoAt C e P Q γ]; rfl
  rw [hk]
  exact tendsto_finsetSum _ fun γ _ => (hconv _ _).const_mul _

/-- **The sector's kernel is the composites' kernel at the components**:
`kernTG P Q = ∑_{α, β} cP(α) cQ(β) kernCG(P_α, Q_β)`. DERIVED: `-1` the sign of a reflected
index; `3` the last slot of the four-index `α : Idx4` in `he1`. -/
theorem kernTG_eq (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) {τ : Fin 4}
    (e : Idx4 → C.Ix) (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hconv : ∀ P Q : TSepG C.Ix τ, Tendsto (fun k => latCG S C k (pairCG C τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (contCG S C (pairCG C τ P.1 Q.1))))
    (P Q : TSep τ) :
    kernTG S ρ τ P Q = ∑ α : Fin P.1.1 → Idx4, ∑ β : Fin Q.1.1 → Idx4,
      coefAt P α * coefAt Q β * kernCG S C τ (monoAt e P α) (monoAt e Q β) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  rw [kernTG, contTG, (tendsto_latTG_pairT S ρ C e hren hconv P Q).limUnder_eq,
    ← (Equiv.sumArrowEquivProdArrow (Fin P.1.1) (Fin Q.1.1) Idx4).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  show (∏ s, (pairT τ P.1 Q.1 s).1 (Sum.elim α β s))
      * contCG S C (pairCG C τ (monoAt e P α).1 (monoAt e Q β).1) = _
  have hL : ∀ i, (pairT τ P.1 Q.1 (Sum.inl i)).1 (Sum.elim α β (Sum.inl i))
      = (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) * (P.1.2 i).1 (α i) := fun i => by
    rw [he1 (α i), ctau_tensor τ (α i)]
    rfl
  have hR : ∀ j, (pairT τ P.1 Q.1 (Sum.inr j)).1 (Sum.elim α β (Sum.inr j))
      = (Q.1.2 j).1 (β j) := fun j => rfl
  have hS : sgnCG C τ (monoAt e P α).1 = ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (e (α i))) := rfl
  rw [Fintype.prod_sum_type]
  simp only [hL, hR]
  rw [Finset.prod_mul_distrib, kernCG, hS]
  simp only [coefAt]
  ring

/-- **The Gram identity** of `wOfC e wC`, from the first clause of `LinkCG` and both clauses of `e`.

DERIVED: `3` the last slot of the four-index `α : Idx4` in `he1`. -/
theorem gram_wOfCG (S : Sched G) (ρ : RenormMixG G) (C : CompositesG G) {τ : Fin 4} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (wC : TSepG C.Ix τ → H)
    (e : Idx4 → C.Ix) (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hG : ∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latCG S C k (pairCG C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contCG S C (pairCG C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernCG S C τ P Q : ℂ))
    (P Q : TSep τ) :
    inner ℂ (wOfC e wC P) (wOfC e wC Q) = (kernTG S ρ τ P Q : ℂ) := by
  rw [kernTG_eq S ρ C e he1 hren (fun P Q => (hG P Q).1) P Q]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  unfold wOfC
  rw [sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_smul_left, inner_sum, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [inner_smul_right, (hG _ _).2]
  ring

/-! ## 2. Shift, vacuum, and the space of the sector -/

/-- **The shift**, term by term from the shift clause of `LinkCG`. DERIVED: no numeral. -/
theorem wOfC_shiftG (S : Sched G) {D : Set (LField G)} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinkedG G D τ r} {Ix : Type} (e : Idx4 → Ix) (wC : TSepG Ix τ → X.base.H)
    (hS : ∀ (m : ℕ) (P : TSepG Ix τ), wC (shiftTG S τ m P) = X.base.time (S.a m) (wC P))
    (m : ℕ) (P : TSep τ) :
    wOfC e wC (shiftTG S τ m P) = X.base.time (S.a m) (wOfC e wC P) := by
  unfold wOfC
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, ← hS]
  rfl

/-- **The sector's space lies in the composites' space**: each `wOfC e wC P` is a finite
combination of the vectors `wC`. DERIVED: no numeral. -/
theorem hLs_le_hLCG {D : Set (LField G)} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinkedG G D τ r) {C : CompositesG G} (e : Idx4 → C.Ix)
    (wC : TSepG C.Ix τ → X.base.H) : HLsG X (wOfC e wC) ≤ HLCG X wC := by
  unfold HLsG HLCG HLg
  refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨P, rfl⟩
  unfold wOfC
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **`LinkHSG` at `wOfC e wC`** from `LinkCG`, both clauses of `e`, and the cross-reading conjunct
of `LinkHSG`. DERIVED: `3` the last slot of the four-index `α : Idx4` in `he1`. -/
theorem linkHSG_of_comp (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) {τ : Fin 4}
    {r : ℝ} (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (C : CompositesG G)
    (wC : TSepG C.Ix τ → X.base.H) (hLC : LinkCG S X C wC) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hX : ∀ (P : TSep τ) (Q : MarginMonoDG G D τ r),
      Tendsto (fun k => mixLatTG S ρ (energyMapG S W D) τ k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) (X.cvec Q) = (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1 : ℂ)) :
    LinkHSG S W D X ρ (wOfC e wC) :=
  ⟨gram_wOfCG S ρ C wC e he1 he2 hLC.1, fun m P => wOfC_shiftG S e wC hLC.2.1 m P,
    wOfC_empty e wC hLC.2.2, hX⟩

/-- **`TInG` at `wOfC e wC`** from both clauses of `e`. DERIVED: `3` the last slot of the four-index
`α : Idx4` in `he1`. -/
theorem tInG_of_comp {D : Set (LField G)} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (C : CompositesG G)
    (wC : TSepG C.Ix τ → X.base.H) (e : Idx4 → C.Ix)
    (he1 : ∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) :
    TInG ρ C X (wOfC e wC) wC :=
  ⟨e, he1, he2, hLs_le_hLCG X e wC⟩

/-! ## 3. `TopNormG` from the channel tie -/

/-- **`TopNormG` from the channel tie and the limit of the identity component**: the first clause
of `TopNormG` holds at `zq k = zAct (Z k) ε id` by `LinkReduce.zAct_epsC`.

DERIVED: `4` the dimension. -/
theorem topNormG_of_channelTie [GaugeSimple G] [GaugeLie G] (S : Sched G) (K : ClayConsts)
    (ρ : RenormMixG G) (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ)
    (hCT : ChannelTieG ρ Mb Zc)
    (hlim : Tendsto (fun k => zAct (Zc k) epsC id * S.a k ^ 4) atTop (𝓝 K.cTop)) :
    TopNormG S K Zc :=
  ⟨fun k => zAct (Zc k) epsC id, fun k => zAct_epsC (Zc k) (hCT.2.1 k), hlim⟩

end MassGap.LinkReduceG

end

#print axioms MassGap.LinkReduceG.pairCG_monoAt
#print axioms MassGap.LinkReduceG.tendsto_latTG_pairT
#print axioms MassGap.LinkReduceG.kernTG_eq
#print axioms MassGap.LinkReduceG.gram_wOfCG
#print axioms MassGap.LinkReduceG.wOfC_shiftG
#print axioms MassGap.LinkReduceG.hLs_le_hLCG
#print axioms MassGap.LinkReduceG.linkHSG_of_comp
#print axioms MassGap.LinkReduceG.tInG_of_comp
#print axioms MassGap.LinkReduceG.topNormG_of_channelTie
