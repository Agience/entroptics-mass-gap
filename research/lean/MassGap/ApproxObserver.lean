import Mathlib
import MassGap.CompositeLink

/-!
# MassGap.ApproxObserver — what `ApproxK` asks, what positivity cannot give, and the time reduction

`MixConvRP.clayStatementAt_SU_reflAvg'` takes `hA : CompositeLink.ApproxK Kc X G` with
`Kc = kernC (CbR N z) 0` (the composites' reflected two-point readings), `X = mixKR` (composite ×
flowed observer) and `G = gramF` (the observer's flowed Gram matrix). This module states `ApproxK` as
an identity of correlation functions, proves that the joint positivity `JointRPK` the tree proves
(`ReflAvg.jointRPK_R`), taken as a hypothesis on general data, does not imply it, and proves the
Hilbert-space step of a time (Reeh–Schlieder-type) reduction.

## 1. `ApproxK` as a saturation of correlation functions

`gain X G P c = 2 ∑_Q c_Q X(P,Q) − ∑_{Q,Q'} c_Q c_{Q'} G(Q,Q')`.

* `gain_le`: under `JointRPK`, `gain X G P c ≤ Kc(P,P)` for every finite real combination `c`.
* `approxK_iff_isLUB`: under `JointRPK`, `ApproxK Kc X G` holds iff for every composite `P`,
  `Kc(P,P)` is the least upper bound of `gain X G P c` over `c`. In words: the composite's reflected
  two-point function equals the supremum, over finite real combinations of the observer's monomials,
  of twice the mixed reading minus the observer's reflected Gram form.

## 2. Positivity alone does not give `ApproxK` (the decoupled sector)

* `jointRPK_add`: adding to `Kc` a kernel `Δ` that is positive on pairs (`PairPos Δ`) keeps `JointRPK`,
  with `X` and `G` unchanged.
* `not_approxK_add`: under `JointRPK Kc X G`, if `Δ(P,P) > 0` at one composite, `ApproxK (Kc + Δ) X G`
  fails.
* `exists_jointRPK_not_approxK`: for every observer Gram kernel `G` with `gForm G c c ≥ 0`, there are
  composite data `Kc`, `X` (one composite, `Kc = 1`, `X = 0`) with `JointRPK Kc X G` and
  `¬ ApproxK Kc X G`.

Reading (argued): any derivation of `ApproxK` must use an input that excludes a component of the composites
orthogonal to everything the observer reads: a generation (cyclicity) statement, of the kind
`ObserverAxioms.CyclicD` is for a field class inside the observer's own space.

## 3. The time step of a Reeh–Schlieder-type reduction (any inner product space)

* `mem_of_apply_mem`: in a complete inner product space, let `V` be a closed subspace and `T` a
  symmetric injective linear map with `T V ⊆ V`. If `T w ∈ V`, then `w ∈ V`.

Read with `T` a transfer `e^{-sH}` and `V` the closed span of the observer's vectors (invariant: a
shifted margin monomial is a margin monomial, `ContinuumTimeGroup.stepT_gvecT`): a composite whose
time-translate lies in the observer's closed span lies there itself. This removes the margin `r` from
the question (composites at times in `(0, r]` reduce to composites beyond `r`), but not the
generation statement of section 2. Applying it to the composites needs a Hilbert space holding both
families with one transfer, and an injective transfer; neither is built in the tree (the composites'
vectors are constructed inside `preH` from `ApproxK` itself, `CompositeLink.exists_link`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the sign, the zero vector and the empty time; `1` the unit composite and
the unit kernel; `2` the cross-term factor, the square and the halving of `Δ(P,P)`.
-/

noncomputable section

namespace MassGap.ApproxObserver

open MassGap.CompositeLink MassGap.ContinuumFlow

/-! ## 1. `ApproxK` as a saturation -/

section Saturation

variable {M I : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}

/-- **The gain of a combination**: `2 ∑_Q c_Q X(P,Q) − ∑_{Q,Q'} c_Q c_{Q'} G(Q,Q')`.

DERIVED: `2` the cross-term factor. -/
def gain (X : I → M → ℝ) (G : M → M → ℝ) (P : I) (c : M →₀ ℝ) : ℝ :=
  2 * xL (X P) c - gForm G c c

/-- **The gain is bounded by the composite's reflected two-point reading**, under `JointRPK`
(at `P' = P`, `t = 0`). DERIVED: `0` the value of `t`. -/
theorem gain_le (hJ : JointRPK Kc X G) (P : I) (c : M →₀ ℝ) : gain X G P c ≤ Kc P P := by
  have h := hJ P P 0 c
  unfold gain
  nlinarith [h]

/-- **`ApproxK` is the saturation of the gain**: under `JointRPK`, `ApproxK Kc X G` holds iff at
every composite `P`, `Kc(P,P)` is the least upper bound of the gains `gain X G P c`.

DERIVED: `0` the sign of `ε`. -/
theorem approxK_iff_isLUB (hJ : JointRPK Kc X G) :
    ApproxK Kc X G ↔ ∀ P, IsLUB (Set.range (gain X G P)) (Kc P P) := by
  constructor
  · intro hA P
    refine ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨c, rfl⟩
      exact gain_le hJ P c
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨c, hc⟩ := hA P ε hε
      have hb' : gain X G P c ≤ b := hb ⟨c, rfl⟩
      unfold gain at hb'
      linarith
  · intro h P ε hε
    obtain ⟨_, ⟨c, rfl⟩, hlt, -⟩ := (h P).exists_between (sub_lt_self (Kc P P) hε)
    refine ⟨c, ?_⟩
    unfold gain at hlt
    linarith

end Saturation

/-! ## 2. The decoupled sector -/

section Decoupled

variable {M I : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}

/-- **A kernel positive on pairs**: `Δ(P,P) + 2t Δ(P,P') + t² Δ(P',P') ≥ 0` for all `P, P'`, `t`.

DERIVED: `0` the sign; `2` the cross-term factor and the square. -/
def PairPos (Δ : I → I → ℝ) : Prop :=
  ∀ (P P' : I) (t : ℝ), 0 ≤ Δ P P + 2 * t * Δ P P' + t ^ 2 * Δ P' P'

/-- **Adding a sector the observer does not read keeps joint positivity**: `JointRPK Kc X G` and
`PairPos Δ` give `JointRPK (Kc + Δ) X G`.

DERIVED: no numeral. -/
theorem jointRPK_add (hJ : JointRPK Kc X G) {Δ : I → I → ℝ} (hΔ : PairPos Δ) :
    JointRPK (fun P P' => Kc P P' + Δ P P') X G := by
  intro P P' t c
  have h1 := hJ P P' t c
  have h2 := hΔ P P' t
  show 0 ≤ (Kc P P + Δ P P) + 2 * t * (Kc P P' + Δ P P') + t ^ 2 * (Kc P' P' + Δ P' P')
    - 2 * xL (X P) c - 2 * t * xL (X P') c + gForm G c c
  nlinarith [h1, h2]

/-- **The added sector is not approximated**: under `JointRPK Kc X G`, if `Δ(P,P) > 0` at one
composite `P`, `ApproxK (Kc + Δ) X G` fails.

DERIVED: `2` the halving of `Δ(P,P)`; `0` the sign. -/
theorem not_approxK_add (hJ : JointRPK Kc X G) {Δ : I → I → ℝ} {P : I} (hP : 0 < Δ P P) :
    ¬ ApproxK (fun P P' => Kc P P' + Δ P P') X G := by
  intro hA
  obtain ⟨c, hc⟩ := hA P (Δ P P / 2) (by positivity)
  have h0 := gain_le hJ P c
  unfold gain at h0
  have hc' : Kc P P + Δ P P - 2 * xL (X P) c + gForm G c c ≤ Δ P P / 2 := hc
  linarith

/-- **Joint positivity does not imply `ApproxK`**: for every observer kernel `G` with
`gForm G c c ≥ 0`, one composite with `Kc = 1` and `X = 0` satisfies `JointRPK` and not `ApproxK`.

DERIVED: `1` the unit kernel; `0` the vanishing cross kernel; `1/2` the tolerance. -/
theorem exists_jointRPK_not_approxK (hG : ∀ c : M →₀ ℝ, 0 ≤ gForm G c c) :
    JointRPK (fun _ _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) G
      ∧ ¬ ApproxK (fun _ _ : Unit => (1 : ℝ)) (fun _ (_ : M) => (0 : ℝ)) G := by
  have hx : ∀ c : M →₀ ℝ, xL (fun _ : M => (0 : ℝ)) c = 0 := fun c => by
    unfold xL
    simp
  refine ⟨fun P P' t c => ?_, fun hA => ?_⟩
  · show 0 ≤ 1 + 2 * t * 1 + t ^ 2 * 1 - 2 * xL (fun _ : M => (0 : ℝ)) c
      - 2 * t * xL (fun _ : M => (0 : ℝ)) c + gForm G c c
    rw [hx]
    nlinarith [hG c, sq_nonneg (1 + t)]
  · obtain ⟨c, hc⟩ := hA () (1 / 2) (by norm_num)
    have hc' : 1 - 2 * xL (fun _ : M => (0 : ℝ)) c + gForm G c c ≤ 1 / 2 := hc
    rw [hx] at hc'
    linarith [hG c]

end Decoupled

/-! ## 3. The time step -/

section Time

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **A vector whose image under a symmetric injective map preserving a closed subspace lies in it,
lies in it.** With `w = v + u`, `v ∈ V`, `u ∈ Vᗮ`: `T u = T w − T v ∈ V`, and `T u ∈ Vᗮ` by symmetry
and `T V ⊆ V`; so `T u = 0`, `u = 0`.

DERIVED: `0` the zero vector. -/
theorem mem_of_apply_mem (V : Submodule 𝕜 H) (hV : IsClosed (V : Set H)) (T : H →ₗ[𝕜] H)
    (hT : ∀ x y, inner 𝕜 (T x) y = inner 𝕜 x (T y)) (hinj : Function.Injective T)
    (hTV : ∀ x ∈ V, T x ∈ V) {w : H} (hw : T w ∈ V) : w ∈ V := by
  haveI : CompleteSpace V := hV.completeSpace_coe
  obtain ⟨v, hv, u, hu, rfl⟩ := V.exists_add_mem_mem_orthogonal w
  have hTu : T u ∈ V := by
    have e : T u = T (v + u) - T v := by rw [map_add, add_sub_cancel_left]
    rw [e]
    exact V.sub_mem hw (hTV v hv)
  have hTu' : T u ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [← hT x u]
    exact Submodule.inner_right_of_mem_orthogonal (hTV x hx) hu
  have h0 : T u = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hTu hTu')
  have hu0 : u = 0 := hinj (by rw [h0, map_zero])
  rw [hu0, add_zero]
  exact hv

end Time

end MassGap.ApproxObserver

end

#print axioms MassGap.ApproxObserver.gain_le
#print axioms MassGap.ApproxObserver.approxK_iff_isLUB
#print axioms MassGap.ApproxObserver.jointRPK_add
#print axioms MassGap.ApproxObserver.not_approxK_add
#print axioms MassGap.ApproxObserver.exists_jointRPK_not_approxK
#print axioms MassGap.ApproxObserver.mem_of_apply_mem
