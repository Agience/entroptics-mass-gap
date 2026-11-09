import Mathlib
import MassGap.ShortDistance
import MassGap.PeriodicStateDLR

/-!
# MassGap.WardFromLattice — the exact lattice identities, what `WardT` asks beyond them, and the flowed Ward clause

The `SU(2)` target asks
`hward : WardT h2N (rhoD (fR 2) z)`: for some `κ`, every direction `ν`, every admissible `C¹` family
`F` and every `C¹` function `h` equal to `1` within `d` of the supports of the fields in `I` and to `0`
within `d` of the others, `∑_μ S((Θ_{μν}, ∂_μ h), F) = −∑_{i ∈ I} S(F with fᵢ ↦ ∂_ν fᵢ)`, with
`Θ_{μν} = stressC κ μ ν`. This module proves the identities the lattice measure satisfies exactly,
states what `WardT` asks beyond them, and proves `WardT` equivalent, under the expansion
clause `ExpandR`, to a clause on the flowed fields.

## 1. Exact lattice identities (proved, every step, every mixing)

* `latT_translate`: the lattice reading of every family is unchanged when every insertion is translated
  by a lattice vector `a_k n` (`ContinuumSchwinger.latS_translate`, `PeriodicState.periodicState_shift`).
* `latT_telescope`: with `G_j` the family whose insertions of index `< j` are translated by `a_k n`,
  `∑_{j < n} (S_k(G_{j+1}) − S_k(G_j)) = 0`; `G_{j+1}` is `G_j` with the `j`-th insertion translated
  (`transUpTo_succ`). This is the discrete global translation Ward identity: the sum over the insertions
  of the lattice difference in one slot vanishes.
* `periodicState_linkChange`, `stateK_linkChange`: the change of variables `U_l ↦ γ_l U_l` on the links
  `l` of a finite set `Λ`, `γ` fixed. For every continuous `f`,
  `ν(f ∘ L_γ) = ν(f · e^{−β (S_Λ(L_γ⁻¹ U) − S_Λ(U))})`, `S_Λ` the Wilson action of the plaquettes
  through `Λ`, `ν` the infinite-volume periodic Wilson state at every `β` (so `stateK hN k` at every `k`).
  Proof: the DLR equation at `Λ` (`PeriodicStateDLR.periodicState_dlr`) and left invariance of the product
  Haar measure on `Λ` (`integral_mul_left_eq_self`). This is the Schwinger–Dyson identity of the link
  variables in integrated form.

## 2. What `WardT` asks beyond them

Proved:
* `latT_cons_zero`: a reading with a zero test function in the first slot is `0` at every step.
* `wardT_global`: at `h ≡ 1`, `I` all indices, the left side of `WardT` vanishes, and `WardT` gives
  `∑ᵢ S(F with fᵢ ↦ ∂_ν fᵢ) = 0`: the continuum form of the global identity whose lattice form is
  `latT_telescope`. The remaining content of `WardT` is the local one, `h` non-constant.

ARGUED (not formalised):
* The lattice has no exact local translation identity. Its translation group is `a_k ℤ⁴`, and the
  identities of §1 are its global invariance and the link changes of variables with `γ` independent of
  the field. The local identity is the change of variables by the covariant translation
  `δU_μ(x) = ε h(x) a F_{νμ}(x) U_μ(x)`, which depends on the field: its Jacobian on the Haar measure
  is not `1`, and the variation of the Wilson action is `−∑ ∂_μh T^{lat}_{μν}` plus terms of order `a`.
* The renormalisation of `Θ`. At `rhoD f z` the insertion of `stressC κ μ ν` is the traceless-Ricci
  channel with factor `z_ri k` plus `(κ/4) δ_{μν}` times the trace with factor `(N/16) z_sc k`
  (`WardKernel.latT_stress_split`, `mixC_stressC_some`, `mixC_stressC_none`). `WardT` fixes the
  normalisation `z_ri` of the traceless channel relative to the contact terms, and `κ` (the trace
  anomaly). The identities of §1 are statements on `stateK hN k` alone and do not read `z`, so they
  cannot fix `z_ri`; in the capstone `z` is tied to the flowed proxies through `ExpandR`. Mixing with the identity is
  removed by the connected fields (`locField`); the remaining mixing is with total derivatives and
  equation-of-motion fields, whose separated insertions against `∂h` (supported away from the probes)
  carry the `O(a)` contact terms and vanish in the limit.

## 3. The flowed Ward clause (proved: the derivation and its converse)

`msT Wf cf k s G` is the flowed reading of a family of the tensor sector: the multilinear expansion over
the tensor components with each component `eI α` replaced by its flowed proxy `msProx Wf cf k s (eI α)`
(`MultiScaleAll.msLat`). `FlowWard Wf cf`: for some `κ` and all data of `WardT`, as `s → 0⁺`, the
flowed readings satisfy the Ward identity up to `η`, eventually along `ultra`:
`|∑_μ msT(Θ_{μν}, ∂_μh; F) + ∑_{i∈I} msT(F with ∂_ν fᵢ)| ≤ η`. It reads only the flowed proxies, not `z`
or `μ`.

* `SmallFlow`, `SmallFlow.add`, `SmallFlow.sum`: `|a_k − b_k(s)| ≤ η` for small `s`, eventually in `k`.
* `latT_smallFlow`: `ExpandR` gives `SmallFlow` between the lattice reading of every admissible family of
  the tensor sector at `rhoD (fR N) z` and its flowed reading (`CompReduce.latT_expand`, `ExpandR` on
  each composite family `(eI αᵢ, fᵢ)`).
* `adm_cons`, `adm_update`: the families of `WardT` are admissible (`∂h` vanishes within `d` of every
  support; `∂_ν fᵢ` is supported in the closure of the support of `fᵢ`).
* `wardT_of_flowWard`: `SepConv`, `ExpandR` and `FlowWard` give `WardT (rhoD (fR N) z)`.
* `flowWard_of_wardT`: `SepConv`, `ExpandR` and `WardT` give `FlowWard`. So under the expansion clause
  `FlowWard` is equivalent to `WardT` (`wardT_iff_flowWard`): it carries the same Ward content, read on
  the flowed fields at positive flow time. It is not a
  discharge of `WardT`.
* `sepConv_of_scale_expand`: `scale` and `ExpandR` give `SepConv (rhoD (fR N) z)`.

`msT`, `FlowWard`, `latT_smallFlow`, `wardT_of_flowWard`, `flowWard_of_wardT`, `wardT_iff_flowWard` and
`sepConv_of_scale_expand` are stated at every `SU(N)` (`[NeZero N]`); `sepConv_of_multiScale` is at
`SU(2)`.

ARGUED: at fixed `s > 0`, the flowed proxies are smooth functionals of the links at radius `√(8s)`, so
in the step limit the covariant-translation change of variables of §2 acts on them without contact
terms at the probes; this is the Suzuki / Del Debbio–Patella–Rago route to the Ward identity of the
flowed energy–momentum tensor. Its formalisation would need the field-dependent change of variables
and its Jacobian, which §1 does not provide.

## 4. No capstone through `MultiScaleAllRenAt`

No `ClayStatementAt` is stated from `MultiScaleAllRenAt`: its `endpoint` field, `MultiScale.Endpoint`, is
refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.
`wardT_of_flowWard` and `sepConv_of_multiScale` remain.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`; `4` the dimension; `1` the differentiability order, the value of
`h` and the step of the telescope; `0` the limit point, the zero test function and the signs; `3` the
split of the tolerance `η/3`; `1/2` the halving of the separation.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.WardFromLattice

open Filter MeasureTheory
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement

/-! ## 1. Exact lattice identities -/

section Translate

variable {N : ℕ}

/-- **Lattice translation invariance of every reading**: translating every insertion by the lattice
vector `a_k n` leaves the step-`k` reading unchanged, at every mixing `ρ`.
DERIVED: no numeral. -/
theorem latT_translate (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (F : ι → TDatum) (n : ISite) :
    latT hN ρ k (fun i => translateD (site (dySpacing N k) n) (F i)) = latT hN ρ k F := by
  unfold latT
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact latS_translate (stateK hN k) (fun τ => PeriodicState.periodicState_shift hN _ τ)
    (dySpacing_pos (one_le_of_ne_zero hN) k) (fun i => locField hN ρ k (b i) (F i).2) n

/-- The family with its insertions of index `< j` translated by `v`. DERIVED: no numeral. -/
def transUpTo {n : ℕ} (v : Fin 4 → ℝ) (F : Fin n → TDatum) (j : ℕ) : Fin n → TDatum :=
  fun i => if (i : ℕ) < j then translateD v (F i) else F i

/-- **One more slot translated**: `G_{j+1}` is `G_j` with the `j`-th insertion translated.
DERIVED: `1` the step. -/
theorem transUpTo_succ {n : ℕ} (v : Fin 4 → ℝ) (F : Fin n → TDatum) {j : ℕ} (hj : j < n) :
    transUpTo v F (j + 1) = Function.update (transUpTo v F j) ⟨j, hj⟩ (translateD v (F ⟨j, hj⟩)) := by
  funext i
  by_cases h : i = ⟨j, hj⟩
  · subst h
    simp [transUpTo]
  · rw [Function.update_of_ne h]
    have hne : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp only [transUpTo]
    by_cases hi : (i : ℕ) < j
    · rw [if_pos (show (i : ℕ) < j + 1 by omega), if_pos hi]
    · rw [if_neg (show ¬ (i : ℕ) < j + 1 by omega), if_neg hi]

/-- **The discrete global translation Ward identity**: the sum over the slots of the lattice
difference in one slot vanishes, at every step.
DERIVED: `1` the step of the telescope; `0` the value. -/
theorem latT_telescope (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {n : ℕ} (F : Fin n → TDatum)
    (m : ISite) :
    ∑ j ∈ Finset.range n, (latT hN ρ k (transUpTo (site (dySpacing N k) m) F (j + 1))
      - latT hN ρ k (transUpTo (site (dySpacing N k) m) F j)) = 0 := by
  have h0 : transUpTo (site (dySpacing N k) m) F 0 = F := funext fun i => by simp [transUpTo]
  have hn : transUpTo (site (dySpacing N k) m) F n
      = fun i => translateD (site (dySpacing N k) m) (F i) :=
    funext fun i => by simp [transUpTo, i.isLt]
  refine (Finset.sum_range_sub
    (fun j => latT hN ρ k (transUpTo (site (dySpacing N k) m) F j)) n).trans ?_
  show latT hN ρ k (transUpTo _ F n) - latT hN ρ k (transUpTo _ F 0) = 0
  rw [h0, hn, latT_translate, sub_self]

end Translate

section Link

open MassGap.GibbsSpec MassGap.PeriodicStateDLR
open MassGap.WilsonAction (wilsonDensity continuous_wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

variable {N : ℕ}

/-- **Left multiplication at the links of `Λ`**: `U_l ↦ γ_l U_l` for `l ∈ Λ`. DERIVED: no numeral. -/
def lmul (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ) (U : GibbsSpec.IConf (SU N)) : GibbsSpec.IConf (SU N) :=
  splice Λ (fun l => γ l * U l.1) U

/-- DERIVED: no numeral. -/
theorem continuous_lmul (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ) : Continuous (lmul Λ γ) := by
  refine continuous_pi fun l => ?_
  by_cases hl : l ∈ Λ
  · have e : (fun U : GibbsSpec.IConf (SU N) => lmul Λ γ U l) = fun U => γ ⟨l, hl⟩ * U l :=
      funext fun U => by simp [lmul, splice, hl]
    rw [e]
    exact continuous_const.mul (continuous_apply l)
  · have e : (fun U : GibbsSpec.IConf (SU N) => lmul Λ γ U l) = fun U => U l :=
      funext fun U => by simp [lmul, splice, hl]
    rw [e]
    exact continuous_apply l

/-- The left multiplication of a spliced configuration is the splice of the multiplied inside.
DERIVED: no numeral. -/
theorem lmul_splice (Λ : Finset GibbsSpec.ILink) (γ u : VConf (SU N) Λ) (ω : GibbsSpec.IConf (SU N)) :
    lmul Λ γ (splice Λ u ω) = splice Λ (γ * u) ω := by
  funext l
  by_cases hl : l ∈ Λ
  · simp [lmul, splice, hl]
  · simp [lmul, splice, hl]

/-- The change of the action of the plaquettes through `Λ` under `L_γ⁻¹`. DERIVED: no numeral. -/
def dAct (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ) (U : GibbsSpec.IConf (SU N)) : ℝ :=
  actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) (lmul Λ γ⁻¹ U)
    - actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) U

/-- **The Boltzmann ratio** `e^{−β (S_Λ(L_γ⁻¹ U) − S_Λ(U))}` as a continuous observable.
DERIVED: no numeral. -/
def wRatio (β : ℝ) (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => Real.exp (-β * dAct Λ γ U), by
    have hc := MassGap.WilsonDLR.continuous_actionOn (G := SU N) (continuous_wilsonDensity (N := N))
      (boundaryPlaqs Λ)
    exact Real.continuous_exp.comp (continuous_const.mul ((hc.comp (continuous_lmul Λ γ⁻¹)).sub hc))⟩

/-- DERIVED: no numeral. -/
theorem wRatio_mul_wt (β : ℝ) (Λ : Finset GibbsSpec.ILink) (γ u : VConf (SU N) Λ) (ω : GibbsSpec.IConf (SU N)) :
    wRatio β Λ γ (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ u ω
      = wt (wilsonDensity (N := N)) β Λ (γ⁻¹ * u) ω := by
  show Real.exp (-β * dAct Λ γ (splice Λ u ω))
      * Real.exp (-β * actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) (splice Λ u ω))
    = Real.exp (-β * actionOn (wilsonDensity (N := N)) (boundaryPlaqs Λ) (splice Λ (γ⁻¹ * u) ω))
  rw [← Real.exp_add, dAct, lmul_splice]
  congr 1
  ring

instance isMulLeftInvariant_vol (Λ : Finset GibbsSpec.ILink) :
    (vol (probHaar (SU N)) Λ).IsMulLeftInvariant := by
  unfold vol
  infer_instance

/-- **The link change of variables, infinite volume**: for every finite link set `Λ`, every `γ` on
it and every continuous `f`, `ν(f ∘ L_γ) = ν(f · e^{−β (S_Λ(L_γ⁻¹ U) − S_Λ(U))})` in the periodic
Wilson state at every `β`.
DERIVED: no numeral. -/
theorem periodicState_linkChange (hN : N ≠ 0) (β : ℝ) (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ)
    (f : C(GibbsSpec.IConf (SU N), ℝ)) :
    PeriodicState.periodicState hN β (f.comp ⟨lmul Λ γ, continuous_lmul Λ γ⟩)
      = PeriodicState.periodicState hN β (f * wRatio β Λ γ) := by
  rw [← periodicState_dlr hN β Λ (f.comp ⟨lmul Λ γ, continuous_lmul Λ γ⟩),
    ← periodicState_dlr hN β Λ (f * wRatio β Λ γ)]
  congr 1
  ext ω
  rw [wspec_apply, wspec_apply]
  unfold GibbsSpec.spec GibbsSpec.num
  congr 1
  have key := integral_mul_left_eq_self (μ := vol (probHaar (SU N)) Λ)
    (fun v : VConf (SU N) Λ => f (splice Λ v ω) * wt (wilsonDensity (N := N)) β Λ (γ⁻¹ * v) ω) γ
  simp only [inv_mul_cancel_left] at key
  calc ∫ u, (f.comp ⟨lmul Λ γ, continuous_lmul Λ γ⟩) (splice Λ u ω)
          * wt (wilsonDensity (N := N)) β Λ u ω ∂(vol (probHaar (SU N)) Λ)
      = ∫ u, f (splice Λ (γ * u) ω) * wt (wilsonDensity (N := N)) β Λ u ω
          ∂(vol (probHaar (SU N)) Λ) := by
        congr 1
        funext u
        simp [lmul_splice]
    _ = ∫ u, f (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ (γ⁻¹ * u) ω
          ∂(vol (probHaar (SU N)) Λ) := key
    _ = ∫ u, (f * wRatio β Λ γ) (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ u ω
          ∂(vol (probHaar (SU N)) Λ) := by
        congr 1
        funext u
        rw [ContinuousMap.mul_apply, mul_assoc, wRatio_mul_wt]

/-- **The link change of variables in the state of step `k`.** DERIVED: no numeral. -/
theorem stateK_linkChange (hN : N ≠ 0) (k : ℕ) (Λ : Finset GibbsSpec.ILink) (γ : VConf (SU N) Λ)
    (f : C(GibbsSpec.IConf (SU N), ℝ)) :
    stateK hN k (f.comp ⟨lmul Λ γ, continuous_lmul Λ γ⟩)
      = stateK hN k (f * wRatio (dyBeta (one_le_of_ne_zero hN) k) Λ γ) :=
  periodicState_linkChange hN _ Λ γ f

end Link

/-! ## 2. The global part of `WardT` -/

section Global

variable {N : ℕ}

/-- The zero test function. DERIVED: `0` the value, the support radius and the bound. -/
def zeroT : TestFn :=
  ⟨fun _ => 0, 0, 0, le_refl 0, fun _ => by simp, fun _ h => absurd rfl h⟩

/-- A field smeared with a test function that vanishes everywhere is `0`. DERIVED: `0` the value. -/
theorem smear_zero_of (a : ℝ) (O : C(Cfg N, ℝ)) {u : TestFn} (hu : ∀ x, u.1 x = 0) :
    smear a O u = 0 := by
  unfold smear
  simp [hu]

/-- **A reading with a zero test function in the first slot is `0`.** DERIVED: `0` the value. -/
theorem latT_cons_zero (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {n : ℕ} (c : Idx4 → ℝ)
    {u : TestFn} (hu : ∀ x, u.1 x = 0) (F : Fin n → TDatum) :
    latT hN ρ k (Fin.cons (α := fun _ => TDatum) (c, u) F) = 0 := by
  unfold latT
  refine Finset.sum_eq_zero fun b _ => ?_
  have h : latSk hN k (fun i => locField hN ρ k (b i)
      ((Fin.cons (α := fun _ => TDatum) (c, u) F) i).2) = 0 := by
    unfold latSk latS
    rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1))), MassGap.DLRLimit.State.map_zero]
    exact smear_zero_of _ _ (fun x => by simpa [locField] using hu x)
  rw [h, mul_zero]

/-- **The global part of `WardT`**: at `h ≡ 1` and `I` all indices the left side vanishes, so `WardT`
gives `∑ᵢ S(F with fᵢ ↦ ∂_ν fᵢ) = 0`.
DERIVED: `1` the constant `h` and the separation used. -/
theorem wardT_global (hN : N ≠ 0) (ρ : RenormMix N) (hW : WardT hN ρ) (ν : Fin 4) {n : ℕ}
    (F : Fin n → TDatum) (df : Fin n → TestFn) (hF : Adm F) (hC : ∀ i, ContDiff ℝ 1 (F i).2.1)
    (hdf : ∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) :
    ∑ i, contT hN ρ (Function.update F i ((F i).1, df i)) = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨κ, hκ⟩ := hW
  have h := hκ ν n F Finset.univ (fun _ => 1) (fun _ => zeroT) df 1 one_pos hF contDiff_const
    (fun μ x => by simp [zeroT]) hC hdf (fun i x y _ _ => by simp)
  have hz : ∀ μ : Fin 4, contT hN ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, zeroT) F) = 0 := by
    intro μ
    have e : ∀ k, latT hN ρ k (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, zeroT) F) = 0 :=
      fun k => latT_cons_zero hN ρ k _ (u := zeroT) (fun _ => rfl) F
    unfold contT
    simp only [e]
    exact tendsto_const_nhds.limUnder_eq
  rw [Finset.sum_eq_zero (fun μ _ => hz μ)] at h
  linarith

end Global

/-! ## 3. Small flow time -/

section Small

/-- **The reading `a` is the flowed reading `b s` at small flow time**: for every `η > 0`, for all
small `s > 0`, eventually in the step, `|a_k − b_k(s)| ≤ η`.
DERIVED: `0` the limit point. -/
def SmallFlow (a : ℕ → ℝ) (b : ℝ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in atTop, |a k - b s k| ≤ η

/-- DERIVED: `2` the halving. -/
theorem SmallFlow.add {a a' : ℕ → ℝ} {b b' : ℝ → ℕ → ℝ} (h : SmallFlow a b)
    (h' : SmallFlow a' b') : SmallFlow (fun k => a k + a' k) (fun s k => b s k + b' s k) := by
  intro η hη
  filter_upwards [h (η / 2) (by positivity), h' (η / 2) (by positivity)] with s hs hs'
  filter_upwards [hs, hs'] with k hk hk'
  have e : a k + a' k - (b s k + b' s k) = (a k - b s k) + (a' k - b' s k) := by ring
  rw [e]
  linarith [abs_add_le (a k - b s k) (a' k - b' s k)]

/-- DERIVED: `0` the value. -/
theorem SmallFlow.zero : SmallFlow (fun _ => 0) (fun _ _ => 0) := fun η hη =>
  Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => by simp [hη.le]

/-- DERIVED: no numeral. -/
theorem SmallFlow.sum {ι : Type} (S : Finset ι) {a : ι → ℕ → ℝ} {b : ι → ℝ → ℕ → ℝ}
    (h : ∀ j ∈ S, SmallFlow (a j) (b j)) :
    SmallFlow (fun k => ∑ j ∈ S, a j k) (fun s k => ∑ j ∈ S, b j s k) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa using SmallFlow.zero
  · intro j S hj ih h
    have := (h j (Finset.mem_insert_self j S)).add
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj'))
    simpa [Finset.sum_insert hj] using this

/-- **The forward step**: two readings at small flow time whose flowed sum tends to `0` along
`ultra` have opposite limits.
DERIVED: `3` the split of the tolerance; `2` the halving. -/
theorem eq_neg_of_smallFlow {A B : ℕ → ℝ} {SA SB : ℝ → ℕ → ℝ} {cA cB : ℝ}
    (hA : SmallFlow A SA) (hB : SmallFlow B SB)
    (hW : ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ), |SA s k + SB s k| ≤ η)
    (hTA : Tendsto A (ultra : Filter ℕ) (𝓝 cA)) (hTB : Tendsto B (ultra : Filter ℕ) (𝓝 cB)) :
    cA = -cB := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hbound : ∀ η : ℝ, 0 < η → ∀ᶠ k in (ultra : Filter ℕ), |A k + B k| ≤ η := by
    intro η hη
    have h3 : 0 < η / 3 := by positivity
    obtain ⟨s, hs1, hs2, hs3⟩ := ((hA (η / 3) h3).and ((hB (η / 3) h3).and (hW (η / 3) h3))).exists
    filter_upwards [hs1.filter_mono ultra_le, hs2.filter_mono ultra_le, hs3] with k k1 k2 k3
    have e : A k + B k = (A k - SA s k) + (B k - SB s k) + (SA s k + SB s k) := by ring
    rw [e]
    linarith [abs_add_three (A k - SA s k) (B k - SB s k) (SA s k + SB s k)]
  have hT := (hTA.add hTB).abs
  have hle : ∀ η : ℝ, 0 < η → |cA + cB| ≤ η := fun η hη => le_of_tendsto hT (hbound η hη)
  have h0 : cA + cB = 0 := by
    by_contra hne
    have := hle (|cA + cB| / 2) (half_pos (abs_pos.mpr hne))
    linarith [abs_pos.mpr hne]
  linarith

/-- **The converse step**: two readings at small flow time with opposite limits along `ultra` have a
flowed sum tending to `0`.
DERIVED: `3` the split of the tolerance. -/
theorem flowSum_of_eq_neg {A B : ℕ → ℝ} {SA SB : ℝ → ℕ → ℝ} {cA cB : ℝ}
    (hA : SmallFlow A SA) (hB : SmallFlow B SB)
    (hTA : Tendsto A (ultra : Filter ℕ) (𝓝 cA)) (hTB : Tendsto B (ultra : Filter ℕ) (𝓝 cB))
    (h : cA = -cB) :
    ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ), |SA s k + SB s k| ≤ η := by
  intro η hη
  have h3 : 0 < η / 3 := by positivity
  have hc : cA + cB = 0 := by rw [h]; ring
  have hT := (hTA.add hTB).abs
  rw [hc, abs_zero] at hT
  have hev : ∀ᶠ k in (ultra : Filter ℕ), |A k + B k| ≤ η / 3 := hT.eventually (Iic_mem_nhds h3)
  filter_upwards [hA (η / 3) h3, hB (η / 3) h3] with s hs1 hs2
  filter_upwards [hs1.filter_mono ultra_le, hs2.filter_mono ultra_le, hev] with k k1 k2 k3
  have e : SA s k + SB s k = (SA s k - A k) + (SB s k - B k) + (A k + B k) := by ring
  rw [e]
  linarith [abs_add_three (SA s k - A k) (SB s k - B k) (A k + B k),
    abs_sub_comm (A k) (SA s k), abs_sub_comm (B k) (SB s k)]

end Small

/-! ## 4. Admissibility of the families of `WardT` -/

section Adm

/-- Where a function is constant on a ball, its derivative vanishes. DERIVED: `0` the derivative. -/
theorem fderiv_eq_zero_of_const_on_ball {h : (Fin 4 → ℝ) → ℝ} {y x : Fin 4 → ℝ} {d c : ℝ}
    (hc : ∀ w, dist y w < d → h w = c) (hx : dist y x < d) : fderiv ℝ h x = 0 := by
  have hev : h =ᶠ[𝓝 x] fun _ => c := by
    have hb : Metric.ball y d ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_comm]; exact hx)
    filter_upwards [hb] with w hw
    exact hc w (by rw [Metric.mem_ball, dist_comm] at hw; exact hw)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply c

/-- Where the derivative is non-zero, the function is non-zero arbitrarily near.
DERIVED: `0` the value. -/
theorem exists_ne_zero_near {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (h : fderiv ℝ f x ≠ 0) (r : ℝ)
    (hr : 0 < r) : ∃ x', dist x x' < r ∧ f x' ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  apply h
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with w hw
    exact hne w (by rw [Metric.mem_ball, dist_comm] at hw; exact hw)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

/-- Points at sup-distance `≥ d` are separated in some coordinate. DERIVED: no numeral. -/
theorem sep_of_dist {x y : Fin 4 → ℝ} {d : ℝ} (hd : 0 < d) (h : ¬ dist y x < d) :
    ∃ i : Fin 4, d ≤ |x i - y i| := by
  by_contra hne
  simp only [not_exists, not_le] at hne
  apply h
  rw [dist_pi_lt_iff hd]
  intro i
  rw [Real.dist_eq, abs_sub_comm]
  exact hne i

/-- **The family with the stress insertion first is admissible** when the insertion's test function is
continuous and `d`-far from the supports of `F`. DERIVED: no numeral. -/
theorem adm_cons {n : ℕ} {F : Fin n → TDatum} (hF : Adm F) {c : Idx4 → ℝ} {u : TestFn}
    (hu : Continuous u.1) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i x y, u.1 x ≠ 0 → (F i).2.1 y ≠ 0 → ¬ dist y x < d) :
    Adm (Fin.cons (α := fun _ => TDatum) (c, u) F) := by
  obtain ⟨hc, d0, hd0, hs⟩ := hF
  refine ⟨fun i => ?_, min d d0, lt_min hd hd0, fun i j hij => ?_⟩
  · cases i using Fin.cases with
    | zero => simpa using hu
    | succ i => simpa using hc i
  · cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        intro x y hx hy
        obtain ⟨m, hm⟩ := sep_of_dist hd (hsep j x y hx hy)
        exact ⟨m, (min_le_left _ _).trans hm⟩
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        intro y x hy hx
        obtain ⟨m, hm⟩ := sep_of_dist hd (hsep i x y hx hy)
        exact ⟨m, (min_le_left _ _).trans (by rw [abs_sub_comm]; exact hm)⟩
      | succ j =>
        simp only [Fin.cons_succ]
        intro x y hx hy
        obtain ⟨m, hm⟩ := hs i j (fun e => hij (by rw [e])) x y hx hy
        exact ⟨m, (min_le_right _ _).trans hm⟩

/-- **The family with one test function replaced is admissible** when the new test function is
continuous and non-zero only arbitrarily near the support of the old one.
DERIVED: `2` the halving of the separation. -/
theorem adm_update {n : ℕ} {F : Fin n → TDatum} (hF : Adm F) (i : Fin n) {u : TestFn}
    (hu : Continuous u.1)
    (hsupp : ∀ x, u.1 x ≠ 0 → ∀ r : ℝ, 0 < r → ∃ x', dist x x' < r ∧ (F i).2.1 x' ≠ 0) :
    Adm (Function.update F i ((F i).1, u)) := by
  obtain ⟨hc, d0, hd0, hs⟩ := hF
  have hd2 : 0 < d0 / 2 := by positivity
  have key : ∀ j, j ≠ i → ∀ x y, u.1 x ≠ 0 → (F j).2.1 y ≠ 0 →
      ∃ m : Fin 4, d0 / 2 ≤ |x m - y m| := by
    intro j hj x y hx hy
    obtain ⟨x', hxx', hx'⟩ := hsupp x hx (d0 / 2) hd2
    obtain ⟨m, hm⟩ := hs i j (Ne.symm hj) x' y hx' hy
    refine ⟨m, ?_⟩
    have h1 : |x m - x' m| ≤ dist x x' := by
      rw [← Real.dist_eq]
      exact dist_le_pi_dist x x' m
    have h2 : |x' m - y m| ≤ |x m - x' m| + |x m - y m| := by
      have := abs_sub_le (x' m) (x m) (y m)
      rw [abs_sub_comm (x' m) (x m)] at this
      linarith
    linarith
  refine ⟨fun j => ?_, d0 / 2, hd2, fun j l hjl => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using hu
    · simpa [Function.update_of_ne hj] using hc j
  · by_cases hj : j = i
    · subst hj
      have hl : l ≠ j := fun e => hjl e.symm
      simp only [Function.update_self, Function.update_of_ne hl]
      intro x y hx hy
      exact key l hl x y hx hy
    · by_cases hl : l = i
      · subst hl
        simp only [Function.update_self, Function.update_of_ne hj]
        intro y x hy hx
        obtain ⟨m, hm⟩ := key j hj x y hx hy
        exact ⟨m, by rw [abs_sub_comm]; exact hm⟩
      · simp only [Function.update_of_ne hj, Function.update_of_ne hl]
        intro x y hx hy
        obtain ⟨m, hm⟩ := hs j l hjl x y hx hy
        exact ⟨m, by linarith⟩

end Adm

end MassGap.WardFromLattice

/-! ## 5. The flowed Ward clause -/

namespace MassGap.WardFromLattice

open Filter
open scoped Topology
open MassGap MassGap.ContinuumField MassGap.ClayStatement
open MassGap.InfiniteLattice MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-- **The flowed reading of the tensor sector**: the multilinear expansion over the tensor components,
each component `eI α` read through its flowed proxy at scale `s` (`msLat`).
DERIVED: no numeral. -/
def msT [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : ι → TDatum) : ℝ :=
  ∑ α : ι → Idx4, (∏ i, (G i).1 (α i)) * msLat Wf cf k s (fun i => (eI (α i), (G i).2))

/-- **The lattice reading of the tensor sector is its flowed reading at small flow time**, on every
admissible family, from `ExpandR`.
DERIVED: `0` the limit point. -/
theorem latT_smallFlow [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandR Wf cf z μ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : ι → TDatum) (hG : Adm G) :
    SmallFlow (fun k => latT (NeZero.ne N) (rhoD (fR N) z) k G) (fun s k => msT Wf cf k s G) := by
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  obtain ⟨hc, d, hd, hsep⟩ := hG
  set C : ℝ := ∑ α : ι → Idx4, |∏ i, (G i).1 (α i)|
      * (Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (eI (α i)))⁻¹ * l1 (G i).2)) with hCdef
  intro η hη
  have hT : Tendsto (fun s : ℝ => (s / d) ^ ε * C) (𝓝[>] 0) (𝓝 0) := by
    have h0 : ContinuousAt (fun s : ℝ => (s / d) ^ ε * C) 0 :=
      ((continuousAt_id.div_const d).rpow_const (Or.inr hε.le)).mul continuousAt_const
    simpa [Real.zero_rpow hε.ne'] using h0.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hT.eventually (Iic_mem_nhds hη), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (mul_pos hθ hd))] with s hs1 hs2 hs3
  have hs1' : (s / d) ^ ε * C ≤ η := hs1
  have hk : ∀ᶠ k in atTop, ∀ α : ι → Idx4,
      |latC (NeZero.ne N) (CRen N z μ) k (fun i => (eI (α i), (G i).2))
          - msLat Wf cf k s (fun i => (eI (α i), (G i).2))|
        ≤ Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (eI (α i)))⁻¹ * l1 (G i).2) := by
    rw [Filter.eventually_all]
    intro α
    exact hEx ι (fun i => (eI (α i), (G i).2)) d hd (fun i => hc i) (fun i j hij => hsep i j hij)
      s hs2 hs3
  filter_upwards [hk] with k hk
  show |latT (NeZero.ne N) (rhoD (fR N) z) k G - msT Wf cf k s G| ≤ η
  rw [CompReduce.latT_expand (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) k G]
  unfold msT
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hs1')
  rw [hCdef, Finset.mul_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [← mul_sub, abs_mul]
  calc |∏ i, (G i).1 (α i)|
        * |latC (NeZero.ne N) (CRen N z μ) k (fun i => (eI (α i), (G i).2))
            - msLat Wf cf k s (fun i => (eI (α i), (G i).2))|
      ≤ |∏ i, (G i).1 (α i)|
          * (Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (eI (α i)))⁻¹ * l1 (G i).2)) :=
        mul_le_mul_of_nonneg_left (hk α) (abs_nonneg _)
    _ = (s / d) ^ ε * (|∏ i, (G i).1 (α i)|
          * (Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (eI (α i)))⁻¹ * l1 (G i).2))) := by ring

/-- **The flowed Ward clause**: for some `κ` and all data of `WardT`, as `s → 0⁺`, the flowed readings
satisfy the translation Ward identity up to `η`, eventually along `ultra`.
DERIVED: `1` the differentiability order and the value of `h`; `0` its other value, the signs and the
limit point. -/
def FlowWard [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ κ : ℝ, ∀ (ν : Fin 4) (n : ℕ) (F : Fin n → TDatum) (I : Finset (Fin n))
      (h : (Fin 4 → ℝ) → ℝ) (dh : Fin 4 → TestFn) (df : Fin n → TestFn) (d : ℝ),
    0 < d → Adm F → ContDiff ℝ 1 h → (∀ μ x, (dh μ).1 x = fderiv ℝ h x (dir μ)) →
    (∀ i, ContDiff ℝ 1 (F i).2.1) → (∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) →
    (∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d → h y = if i ∈ I then 1 else 0) →
    ∀ η : ℝ, 0 < η → ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      |∑ μ, msT Wf cf k s (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F)
        + ∑ i ∈ I, msT Wf cf k s (Function.update F i ((F i).1, df i))| ≤ η

/-- The stress families of `WardT` are admissible. DERIVED: `1` the differentiability order. -/
theorem adm_stress {n : ℕ} {F : Fin n → TDatum} (hF : Adm F) {I : Finset (Fin n)}
    {h : (Fin 4 → ℝ) → ℝ} {dh : Fin 4 → TestFn} {d : ℝ} (hd : 0 < d) (hh : ContDiff ℝ 1 h)
    (hdh : ∀ μ x, (dh μ).1 x = fderiv ℝ h x (dir μ))
    (hloc : ∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d → h y = if i ∈ I then 1 else 0)
    (c : Idx4 → ℝ) (m : Fin 4) : Adm (Fin.cons (α := fun _ => TDatum) (c, dh m) F) := by
  refine adm_cons hF ?_ hd ?_
  · rw [show (dh m).1 = fun x => fderiv ℝ h x (dir m) from funext (hdh m)]
    exact (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  · intro i x y hx hy hxy
    apply hx
    simp [hdh m x, fderiv_eq_zero_of_const_on_ball (fun w hw => hloc i y w hy hw) hxy]

/-- The derivative families of `WardT` are admissible. DERIVED: `1` the differentiability order. -/
theorem adm_deriv {n : ℕ} {F : Fin n → TDatum} (hF : Adm F) {ν : Fin 4} {df : Fin n → TestFn}
    (hFc : ∀ i, ContDiff ℝ 1 (F i).2.1) (hdf : ∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν))
    (i : Fin n) : Adm (Function.update F i ((F i).1, df i)) := by
  refine adm_update hF i ?_ ?_
  · rw [show (df i).1 = fun x => fderiv ℝ (F i).2.1 x (dir ν) from funext (hdf i)]
    exact ((hFc i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  · intro x hx r hr
    refine exists_ne_zero_near ?_ r hr
    intro h0
    apply hx
    simp [hdf i x, h0]

/-- **`WardT` from the flowed Ward clause**, given `SepConv` and the expansion clause `ExpandR`, at every
`SU(N)`. -/
theorem wardT_of_flowWard [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hE : ExpandR Wf cf z μ)
    (hW : FlowWard Wf cf) : WardT (NeZero.ne N) (rhoD (fR N) z) := by
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, fun ν n F I h dh df d hd hF hh hdh hFc hdf hloc => ?_⟩
  have hG := adm_stress hF hd hh hdh hloc
  have hH := adm_deriv hF hFc hdf
  exact eq_neg_of_smallFlow
    (SmallFlow.sum Finset.univ fun m _ => latT_smallFlow hE _ (hG (stressC κ m ν) m))
    (SmallFlow.sum I fun i _ => latT_smallFlow hE _ (hH i))
    (hκ ν n F I h dh df d hd hF hh hdh hFc hdf hloc)
    (tendsto_finsetSum _ fun m _ => hS _ _ (hG (stressC κ m ν) m))
    (tendsto_finsetSum _ fun i _ => hS _ _ (hH i))

/-- **The flowed Ward clause from `WardT`**, given `SepConv` and `ExpandR`, at every `SU(N)`. -/
theorem flowWard_of_wardT [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hE : ExpandR Wf cf z μ)
    (hW : WardT (NeZero.ne N) (rhoD (fR N) z)) : FlowWard Wf cf := by
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, fun ν n F I h dh df d hd hF hh hdh hFc hdf hloc => ?_⟩
  have hG := adm_stress hF hd hh hdh hloc
  have hH := adm_deriv hF hFc hdf
  exact flowSum_of_eq_neg
    (SmallFlow.sum Finset.univ fun m _ => latT_smallFlow hE _ (hG (stressC κ m ν) m))
    (SmallFlow.sum I fun i _ => latT_smallFlow hE _ (hH i))
    (tendsto_finsetSum _ fun m _ => hS _ _ (hG (stressC κ m ν) m))
    (tendsto_finsetSum _ fun i _ => hS _ _ (hH i))
    (hκ ν n F I h dh df d hd hF hh hdh hFc hdf hloc)

/-- **Under `SepConv` and `ExpandR`, `WardT` and the flowed Ward clause are equivalent**, at every
`SU(N)`. -/
theorem wardT_iff_flowWard [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hS : SepConv (NeZero.ne N) (rhoD (fR N) z)) (hE : ExpandR Wf cf z μ) :
    WardT (NeZero.ne N) (rhoD (fR N) z) ↔ FlowWard Wf cf :=
  ⟨flowWard_of_wardT hS hE, wardT_of_flowWard hS hE⟩

/-- **`SepConv` of the tensor sector from the scale clause and `ExpandR`**, at every `SU(N)`: `ConvC` of
`CRen N z μ` (`CompositesRenAll.boundC_ren_of_scale_expand`) through `CompReduce.sepConv_of_comp`. -/
theorem sepConv_of_scale_expand [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ} (hb : 0 < b)
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlAll b Wf)
    (hex : ExpandR Wf cf z μ) : SepConv (NeZero.ne N) (rhoD (fR N) z) :=
  CompReduce.sepConv_of_comp (NeZero.ne N) (rhoD (fR N) z) (CRen N z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α)
    ((InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_scale_expand hb hsc hex))

/-- **`SepConv` of the tensor sector at the capstone's data**: `ConvC` of `CRen 2 z μ`
(`CompositesRenAll.convC_ren_of_all`) through `CompReduce.sepConv_of_comp`.
DERIVED: `2` is `SU(2)`. -/
theorem sepConv_of_multiScale {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (H : MultiScaleAllRenAt W z μ b Wf cf)
    (hcb : CoefBound cf) : SepConv h2N (rhoD (fR 2) z) :=
  CompReduce.sepConv_of_comp h2N (rhoD (fR 2) z) (CRen 2 z μ) eI
    (fun k α => buildRen_he2 _ _ μ k α) (convC_ren_of_all (multiScaleAllRen_of' ⟨b, Wf, cf, H, hcb⟩))

end MassGap.WardFromLattice

end

#print axioms MassGap.WardFromLattice.latT_translate
#print axioms MassGap.WardFromLattice.transUpTo_succ
#print axioms MassGap.WardFromLattice.latT_telescope
#print axioms MassGap.WardFromLattice.periodicState_linkChange
#print axioms MassGap.WardFromLattice.stateK_linkChange
#print axioms MassGap.WardFromLattice.latT_cons_zero
#print axioms MassGap.WardFromLattice.wardT_global
#print axioms MassGap.WardFromLattice.SmallFlow.sum
#print axioms MassGap.WardFromLattice.eq_neg_of_smallFlow
#print axioms MassGap.WardFromLattice.flowSum_of_eq_neg
#print axioms MassGap.WardFromLattice.adm_cons
#print axioms MassGap.WardFromLattice.adm_update
#print axioms MassGap.WardFromLattice.latT_smallFlow
#print axioms MassGap.WardFromLattice.wardT_of_flowWard
#print axioms MassGap.WardFromLattice.flowWard_of_wardT
#print axioms MassGap.WardFromLattice.wardT_iff_flowWard
#print axioms MassGap.WardFromLattice.sepConv_of_scale_expand
#print axioms MassGap.WardFromLattice.sepConv_of_multiScale
