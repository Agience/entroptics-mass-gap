import Mathlib
import MassGap.FlowCovN
import MassGap.WardFromLattice
import MassGap.ExistencePos
import MassGap.CompositeOS0Test

/-!
# MassGap.WardN — the global translation Ward identity from the lattice, and `WardT` reduced to its off-probe part

`FlowCovN.clayStatement_of_covC` takes, at every `N ≥ 2`, the clause
`WardT (rhoD (fR N) (ZCanon.zFix N zri zwe))`: for some `κ`, every direction `ν`, every admissible `C¹`
family `F`, every `I` and every `C¹` function `h` equal to `1` within `d` of the supports of the fields
in `I` and to `0` within `d` of the others,
`∑_μ S((Θ_{μν}, ∂_μ h), F) = −∑_{i ∈ I} S(F with fᵢ ↦ ∂_ν fᵢ)`.
This module proves the part of that identity which follows from the translation invariance of the
lattice Wilson state, and reduces `WardT` to the rest.

## 1. Linearity of the readings in one test function (proved, every step, every mixing)

* `tfLin a b f g`: the test function `a f + b g`.
* `latT_update_lin`: the step-`k` reading is linear in the test function of one slot
  (`ExistencePos.smear_lincomb`, linearity of the state).
* `contT_update_lin`: the same for the continuum reading, on admissible families, given `SepConv`.

## 2. The global translation Ward identity (proved from `SepConv`, `OS1Sep`, `OS0Sep`)

`WardGlobal`: for every admissible family of `C¹` test functions,
`∑ᵢ S(F with fᵢ ↦ ∂_ν fᵢ) = 0`. It is the integrated Ward identity of the translations, and it is
`WardT` at `h ≡ 1`, `I` every index (`WardFromLattice.wardT_global` derives it from `WardT`).

`wardGlobal_of_os` proves it from `SepConv`, `OS1Sep` and `OS0Sep`. `OS1Sep` (with `SepConv`) gives
`S(F translated by t e_ν) = S(F)` for every real `t` (`contT_translate_eq`); its lattice source is the
exact invariance of `stateK hN k` under the lattice translations (`WardFromLattice.latT_translate`).
Telescoping over the slots (`telescopeW`) and linearity give, for `t ≠ 0` small,
`∑_j S(slots < j translated, slot j ↦ (τ_t f_j − f_j)/t, slots > j unchanged) = 0`.
Each term tends to `S(F with f_j ↦ −∂_ν f_j)` as `t → 0`: `OS0Sep` bounds a reading by a constant times
`∏ᵢ ‖gᵢ‖_{L¹}` on families supported in fixed `d`-separated envelopes (`os0_famW`), so the reading is
Lipschitz in each slot's `L¹` norm (`abs_sub_le_envW`); `τ_t f − f → 0` and
`(τ_t f − f)/t + ∂_ν f → 0` uniformly, with supports in a fixed cube (`translate_unif`, `dq_unif`,
`l1_le_cube`).

`wardGlobal_of_scale`: at `rhoD (fR N) z`, `WardGlobal` from `ScaleControlAll`, `ExpandStrong` and
`CoefBound` (through `CompReduce.os1Sep_of_comp`, `CompReduce.os0Sep_of_comp`,
`WardFromLattice.sepConv_of_scale_expand`), at every `SU(N)`.

## 3. `WardT` reduced to the off-probe clause (proved)

* `contT_one_zero`: a one-insertion reading is `0` at every mixing: the inserted field is connected and
  the state is translation invariant (`ContinuumNontrivial.stateK_smear_connected`). So `WardT` holds
  with no probes (`n = 0`): `∑_μ S((Θ_{μν}, ∂_μ h)) = 0`.
* `WardOff`: `WardT` restricted to families with at least one insertion whose first insertion is not in
  `I` (`h` vanishes near the first probe).
* `wardT_of_off`: `SepConv`, `WardGlobal` and `WardOff` give `WardT`. For `0 ∈ I`, `WardOff` at
  `1 − h` and the complement `Iᶜ`, linearity in the stress slot (`∂(1 − h) = −∂h`) and `WardGlobal`
  (`∑_{I} + ∑_{Iᶜ} = 0`) give the identity at `h`, `I`.
* `wardT_iff_wardOff`: under `SepConv` and `WardGlobal` the two are equivalent.

## 4. The capstone with `WardOff` (proved)

`FlowCovWardInputsN` is `FlowCovN.FlowCovInputsN` with `WardT` replaced by `WardOff`;
`flowCovInputsN_of_ward` and `clayStatement_of_wardOff` derive `FlowCovInputsN` and `ClayStatementDy`
from it. The global part of the Ward identity and the no-probe part are discharged by the listed
inputs; what `WardOff` asks is the local identity with `h` vanishing near one probe. Under `SepConv` and
`WardGlobal`, both supplied by the bundle, `WardOff` is equivalent to `WardT` (`wardT_iff_wardOff`): it
carries all the local content of `WardT`, so the capstone restates that input rather than weakening it.

## 5. What `WardOff` asks (ARGUED, not formalised)

`WardOff` contains the conservation of `Θ` away from the probes (`I = ∅`: `∑_μ S((Θ_{μν}, ∂_μ h), F) = 0`
with `∂h` supported away from every probe) and the contact terms at the probes in `I`. Neither is a
statement on the lattice state alone: at `rhoD (fR N) z` the stress insertion reads the traceless-Ricci
channel with factor `z_ri k` (`WardKernel.mixC_stressC_some`), and `zri` enters `FlowCovInputsN` only as
a non-vanishing sequence tied to the flowed proxies through `ExpandStrong`. The lattice translation group
`a_k ℤ⁴` gives the global identity of §2 and no local one; the local identity is the change of variables
by the field-dependent covariant translation (`WardFromLattice` §2), whose lattice form carries the
finite renormalisation of the lattice stress tensor (the normalisation of `z_ri` against the contact
terms) and `O(a)` terms. So the remaining clause is the normalisation of the traceless channel as the
stress tensor's, plus conservation away from probes; the listed inputs (`ScaleControlAll`,
`ExpandStrong`, `CoefBound`, `CovC`) fix `z_ri` only up to the flowed proxies they are tied to, and none
reads the Ward normalisation.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the exponent of the cube volume; `1` the differentiability
order, the value of `h`, the unit coefficient and the top of the separation; `0` the limit point, the
vanishing values and the first slot; `2` the halving of the separation and of the cube; `12` the bound of
the block-step flow, `2` the least colour count (as in `FlowCovN`).
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.WardN

open Filter MeasureTheory
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement

variable {N : ℕ}

/-! ## 1. Linear combinations of test functions and linearity of the readings -/

section Lin

/-- **The test function `a f + b g`**: supported in the larger cube, bounded by `|a| M + |b| M'`.
DERIVED: `0` the vanishing value. -/
def tfLin (a b : ℝ) (f g : TestFn) : TestFn :=
  ⟨fun y => a * f.1 y + b * g.1 y, by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    obtain ⟨R', M', _, hM', hs'⟩ := g.2
    refine ⟨max R R', |a| * M + |b| * M', le_max_of_le_left hR, fun y => ?_, fun y hy i => ?_⟩
    · calc |a * f.1 y + b * g.1 y| ≤ |a * f.1 y| + |b * g.1 y| := abs_add_le _ _
        _ = |a| * |f.1 y| + |b| * |g.1 y| := by rw [abs_mul, abs_mul]
        _ ≤ |a| * M + |b| * M' := add_le_add (mul_le_mul_of_nonneg_left (hM y) (abs_nonneg a))
            (mul_le_mul_of_nonneg_left (hM' y) (abs_nonneg b))
    · by_cases hf : f.1 y = 0
      · have hg : g.1 y ≠ 0 := fun hg => hy (by simp only [hf, hg, mul_zero, add_zero])
        exact le_max_of_le_right (hs' y hg i)
      · exact le_max_of_le_left (hs y hf i)⟩

/-- DERIVED: no numeral. -/
@[simp] theorem tfLin_apply (a b : ℝ) (f g : TestFn) (y : Fin 4 → ℝ) :
    (tfLin a b f g).1 y = a * f.1 y + b * g.1 y := rfl

/-- DERIVED: no numeral. -/
theorem update_fst {ι : Type} [DecidableEq ι] (G : ι → TDatum) (j : ι) (w : TestFn) (i : ι) :
    (Function.update G j ((G j).1, w) i).1 = (G i).1 := by
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- DERIVED: no numeral. -/
theorem update_snd {ι : Type} [DecidableEq ι] (G : ι → TDatum) (j : ι) (w : TestFn) (i : ι) :
    (Function.update G j ((G j).1, w) i).2 = Function.update (fun l => (G l).2) j w i := by
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- A product with one factor updated. DERIVED: no numeral. -/
theorem prod_update_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X M : Type} [CommMonoid M]
    (φ : ι → X → M) (u : ι → X) (j : ι) (w : X) :
    ∏ i, φ i (Function.update u j w i) = φ j w * ∏ i ∈ Finset.univ.erase j, φ i (u i) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => φ i (Function.update u j w i))
    (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **The step-`k` reading is linear in the test function of one slot**, at every mixing.
DERIVED: `2` the two terms. -/
theorem latT_update_lin (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (G : ι → TDatum) (j : ι) (w g₁ g₂ : TestFn) (s₁ s₂ : ℝ)
    (hw : ∀ y, w.1 y = s₁ * g₁.1 y + s₂ * g₂.1 y) :
    latT hN ρ k (Function.update G j ((G j).1, w))
      = s₁ * latT hN ρ k (Function.update G j ((G j).1, g₁))
        + s₂ * latT hN ρ k (Function.update G j ((G j).1, g₂)) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  have key : ∀ (u : TestFn) (b : ι → ρ.B),
      (∏ i, mixC ρ k (Function.update G j ((G j).1, u) i).1 (b i))
          * latSk hN k (fun i => locField hN ρ k (b i) (Function.update G j ((G j).1, u) i).2)
        = (∏ i, mixC ρ k (G i).1 (b i))
          * stateK hN k (CompReduce.sf hN ρ k (b j) u
              * ∏ i ∈ Finset.univ.erase j, CompReduce.sf hN ρ k (b i) (G i).2) := by
    intro u b
    simp only [update_fst]
    congr 1
    show stateK hN k (∏ i, CompReduce.sf hN ρ k (b i) (Function.update G j ((G j).1, u) i).2) = _
    simp only [update_snd]
    have hp := prod_update_eq (fun i v => CompReduce.sf hN ρ k (b i) v) (fun l => (G l).2) j u
    rw [hp]
  have hsf : ∀ bb : ρ.B, CompReduce.sf hN ρ k bb w
      = s₁ • CompReduce.sf hN ρ k bb g₁ + s₂ • CompReduce.sf hN ρ k bb g₂ := by
    intro bb
    unfold CompReduce.sf
    rw [ExistencePos.smear_lincomb ha _ w ![s₁, s₂] ![g₁, g₂]
      (fun y => by simp [Fin.sum_univ_two, hw y])]
    simp [Fin.sum_univ_two]
  unfold latT
  simp only [key, hsf, add_mul, smul_mul_assoc, DLRLimit.State.map_add, DLRLimit.State.map_smul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The continuum reading is linear in the test function of one slot**, on admissible families,
given `SepConv`. DERIVED: no numeral. -/
theorem contT_update_lin (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : ι → TDatum) (j : ι) (w g₁ g₂ : TestFn) (s₁ s₂ : ℝ)
    (hw : ∀ y, w.1 y = s₁ * g₁.1 y + s₂ * g₂.1 y)
    (hA : Adm (Function.update G j ((G j).1, w))) (hA1 : Adm (Function.update G j ((G j).1, g₁)))
    (hA2 : Adm (Function.update G j ((G j).1, g₂))) :
    contT hN ρ (Function.update G j ((G j).1, w))
      = s₁ * contT hN ρ (Function.update G j ((G j).1, g₁))
        + s₂ * contT hN ρ (Function.update G j ((G j).1, g₂)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have e : ∀ k, latT hN ρ k (Function.update G j ((G j).1, w))
      = s₁ * latT hN ρ k (Function.update G j ((G j).1, g₁))
        + s₂ * latT hN ρ k (Function.update G j ((G j).1, g₂)) :=
    fun k => latT_update_lin hN ρ k G j w g₁ g₂ s₁ s₂ hw
  have h := hS _ _ hA
  simp only [e] at h
  exact tendsto_nhds_unique h (((hS _ _ hA1).const_mul s₁).add ((hS _ _ hA2).const_mul s₂))

end Lin

/-! ## 2. Families in separated envelopes -/

section Env

/-- A family with fixed coefficients and test functions `g`. DERIVED: no numeral. -/
def famW {n : ℕ} (c : Fin n → Idx4 → ℝ) (g : Fin n → TestFn) : Fin n → TDatum := fun i => (c i, g i)

/-- A continuous test function supported in `E`. DERIVED: `0` the vanishing value. -/
def OkW (E : Set (Fin 4 → ℝ)) (f : TestFn) : Prop := Continuous f.1 ∧ ∀ y, f.1 y ≠ 0 → y ∈ E

/-- Envelopes pairwise `d`-separated in some coordinate. DERIVED: `4` the dimension. -/
def SepEnvW {n : ℕ} (d : ℝ) (E : Fin n → Set (Fin 4 → ℝ)) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ E i, ∀ y ∈ E j, ∃ m : Fin 4, d ≤ |x m - y m|

/-- DERIVED: `0` the vanishing value. -/
theorem OkW.lin {E : Set (Fin 4 → ℝ)} {f g : TestFn} (hf : OkW E f) (hg : OkW E g) (a b : ℝ) :
    OkW E (tfLin a b f g) := by
  refine ⟨?_, fun y hy => ?_⟩
  · show Continuous (fun y => a * f.1 y + b * g.1 y)
    exact (continuous_const.mul hf.1).add (continuous_const.mul hg.1)
  · by_cases h : f.1 y = 0
    · exact hg.2 y (fun h' => hy (by simp [h, h']))
    · exact hf.2 y h

/-- DERIVED: no numeral. -/
theorem okW_update {n : ℕ} {E : Fin n → Set (Fin 4 → ℝ)} {g : Fin n → TestFn}
    (hg : ∀ l, OkW (E l) (g l)) (j : Fin n) {w : TestFn} (hw : OkW (E j) w) :
    ∀ l, OkW (E l) (Function.update g j w l) := by
  intro l
  by_cases h : l = j
  · subst h
    simpa using hw
  · rw [Function.update_of_ne h]
    exact hg l

/-- DERIVED: no numeral. -/
theorem sepD_famW {n : ℕ} {d : ℝ} {E : Fin n → Set (Fin 4 → ℝ)} (hE : SepEnvW d E)
    (c : Fin n → Idx4 → ℝ) {g : Fin n → TestFn} (hg : ∀ i, OkW (E i) (g i)) : SepD d (famW c g) :=
  fun i j hij x y hx hy => hE i j hij x ((hg i).2 x hx) y ((hg j).2 y hy)

/-- DERIVED: `0` the sign of the separation. -/
theorem adm_famW {n : ℕ} {d : ℝ} (hd : 0 < d) {E : Fin n → Set (Fin 4 → ℝ)} (hE : SepEnvW d E)
    (c : Fin n → Idx4 → ℝ) {g : Fin n → TestFn} (hg : ∀ i, OkW (E i) (g i)) : Adm (famW c g) :=
  ⟨fun i => (hg i).1, d, hd, sepD_famW hE c hg⟩

/-- DERIVED: no numeral. -/
theorem famW_update {n : ℕ} (c : Fin n → Idx4 → ℝ) (g : Fin n → TestFn) (j : Fin n) (w : TestFn) :
    famW c (Function.update g j w) = Function.update (famW c g) j ((famW c g j).1, w) := by
  funext i
  by_cases h : i = j
  · subst h
    simp [famW]
  · simp [famW, Function.update_of_ne h]

/-- **Linearity in one slot on envelope families.** DERIVED: `0` the sign of the separation. -/
theorem contT_famW_lin (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) {n : ℕ} {d : ℝ}
    (hd : 0 < d) {E : Fin n → Set (Fin 4 → ℝ)} (hE : SepEnvW d E) (c : Fin n → Idx4 → ℝ)
    (g : Fin n → TestFn) (hg : ∀ l, OkW (E l) (g l)) (j : Fin n) (w g₁ g₂ : TestFn) (s₁ s₂ : ℝ)
    (hw : ∀ y, w.1 y = s₁ * g₁.1 y + s₂ * g₂.1 y) (hw0 : OkW (E j) w) (hw1 : OkW (E j) g₁)
    (hw2 : OkW (E j) g₂) :
    contT hN ρ (famW c (Function.update g j w))
      = s₁ * contT hN ρ (famW c (Function.update g j g₁))
        + s₂ * contT hN ρ (famW c (Function.update g j g₂)) := by
  have hA := adm_famW hd hE c (okW_update hg j hw0)
  have hA1 := adm_famW hd hE c (okW_update hg j hw1)
  have hA2 := adm_famW hd hE c (okW_update hg j hw2)
  rw [famW_update] at hA hA1 hA2 ⊢
  rw [famW_update, famW_update]
  exact contT_update_lin hN ρ hS (famW c g) j w g₁ g₂ s₁ s₂ hw hA hA1 hA2

/-- The tuple whose entries of index `< m` are taken from `g'`, the others from `g`.
DERIVED: no numeral. -/
def mixW {n : ℕ} {X : Type} (g g' : Fin n → X) (m : ℕ) : Fin n → X :=
  fun l => if (l : ℕ) < m then g' l else g l

/-- DERIVED: `1` the step. -/
theorem mixW_succ {n : ℕ} {X : Type} (g g' : Fin n → X) (i : Fin n) :
    Function.update (mixW g g' (i : ℕ)) i (g' i) = mixW g g' ((i : ℕ) + 1) := by
  funext l
  by_cases h : l = i
  · subst h
    simp [mixW]
  · rw [Function.update_of_ne h]
    have hne : (l : ℕ) ≠ i := fun e => h (Fin.ext e)
    simp only [mixW]
    by_cases hl : (l : ℕ) < i
    · rw [if_pos hl, if_pos (by omega)]
    · rw [if_neg hl, if_neg (by omega)]

/-- DERIVED: no numeral. -/
theorem mixW_self {n : ℕ} {X : Type} (g g' : Fin n → X) (i : Fin n) :
    Function.update (mixW g g' (i : ℕ)) i (g i) = mixW g g' (i : ℕ) := by
  funext l
  by_cases h : l = i
  · subst h
    simp [mixW]
  · rw [Function.update_of_ne h]

/-- DERIVED: no numeral. -/
theorem okW_mix {n : ℕ} {E : Fin n → Set (Fin 4 → ℝ)} {g g' : Fin n → TestFn}
    (hg : ∀ l, OkW (E l) (g l)) (hg' : ∀ l, OkW (E l) (g' l)) (m : ℕ) :
    ∀ l, OkW (E l) (mixW g g' m l) := by
  intro l
  simp only [mixW]
  split_ifs
  · exact hg' l
  · exact hg l

/-- **The telescope over the slots**: `Ψ g' − Ψ g` is the sum over `i` of the change of slot `i` from
`g i` to `g' i`, the slots before `i` already changed. DERIVED: `0`, `1` the ends and the step. -/
theorem telescopeW {n : ℕ} {X : Type} (Ψ : (Fin n → X) → ℝ) (g g' : Fin n → X) :
    Ψ g' - Ψ g = ∑ i : Fin n, (Ψ (Function.update (mixW g g' (i : ℕ)) i (g' i))
      - Ψ (Function.update (mixW g g' (i : ℕ)) i (g i))) := by
  simp only [mixW_succ, mixW_self]
  rw [show (∑ i : Fin n, (Ψ (mixW g g' ((i : ℕ) + 1)) - Ψ (mixW g g' (i : ℕ))))
      = ∑ m ∈ Finset.range n, (Ψ (mixW g g' (m + 1)) - Ψ (mixW g g' m)) from
    Fin.sum_univ_eq_sum_range (fun m => Ψ (mixW g g' (m + 1)) - Ψ (mixW g g' m)) n,
    Finset.sum_range_sub (fun m => Ψ (mixW g g' m)) n]
  have h0 : mixW g g' 0 = g := funext fun l => by simp [mixW]
  have hn : mixW g g' n = g' := funext fun l => by simp [mixW, l.isLt]
  rw [h0, hn]

/-- DERIVED: no numeral. -/
theorem cnorm_nonneg (c : Idx4 → ℝ) : 0 ≤ cnorm c := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **`OS0Sep` on envelope families**: at a fixed separation `d ≤ 1`, the reading is bounded by a
constant times `∏ᵢ ‖gᵢ‖_{L¹}`. DERIVED: `0`, `1` the range of the separation. -/
theorem os0_famW (hN : N ≠ 0) (ρ : RenormMix N) (h0 : OS0Sep hN ρ) {n : ℕ} (c : Fin n → Idx4 → ℝ)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ E : Fin n → Set (Fin 4 → ℝ), SepEnvW d E → ∀ g : Fin n → TestFn,
      (∀ i, OkW (E i) (g i)) → |contT hN ρ (famW c g)| ≤ K * ∏ i, l1 (g i) := by
  obtain ⟨α, γ, β, κ, hb⟩ := h0
  have hc0 : 0 ≤ ∏ i, cnorm (c i) := Finset.prod_nonneg fun i _ => cnorm_nonneg _
  refine ⟨|α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹| * ∏ i, cnorm (c i),
    mul_nonneg (abs_nonneg _) hc0, fun E hE g hg => ?_⟩
  have h : |contT hN ρ (famW c g)|
      ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹ * ∏ i, (cnorm (c i) * l1 (g i)) :=
    hb n (famW c g) d hd hd1 (fun i => (hg i).1) (sepD_famW hE c hg)
  have hp : 0 ≤ ∏ i, l1 (g i) := Finset.prod_nonneg fun i _ => CompReduce.l1_nonneg _
  refine h.trans ?_
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hc0) hp

/-- **The reading is Lipschitz in the slots' `L¹` norms** on envelope families: with every slot of `g`
and `g'` of `L¹` norm `≤ B` and every slot difference of `L¹` norm `≤ ε`,
`|S(g) − S(g')| ≤ n K ε B^{n−1}`. DERIVED: `1` the unit coefficients and the exponent shift. -/
theorem abs_sub_le_envW (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) {n : ℕ}
    (c : Fin n → Idx4 → ℝ) {d K : ℝ} (hd : 0 < d) {E : Fin n → Set (Fin 4 → ℝ)} (hE : SepEnvW d E)
    (hK : ∀ g : Fin n → TestFn, (∀ i, OkW (E i) (g i)) →
      |contT hN ρ (famW c g)| ≤ K * ∏ i, l1 (g i)) (hK0 : 0 ≤ K)
    (g g' : Fin n → TestFn) (hg : ∀ i, OkW (E i) (g i)) (hg' : ∀ i, OkW (E i) (g' i))
    {B ε : ℝ} (hB : ∀ i, l1 (g i) ≤ B) (hB' : ∀ i, l1 (g' i) ≤ B)
    (hε : ∀ i, l1 (tfLin 1 (-1) (g i) (g' i)) ≤ ε) :
    |contT hN ρ (famW c g) - contT hN ρ (famW c g')| ≤ n * (K * ε * B ^ (n - 1)) := by
  have hT := telescopeW (fun u => contT hN ρ (famW c u)) g' g
  rw [hT]
  have hterm : ∀ i : Fin n,
      |contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g i)))
        - contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g' i)))| ≤ K * ε * B ^ (n - 1) := by
    intro i
    have hM := okW_mix hg' hg (i : ℕ)
    have hΔ : OkW (E i) (tfLin 1 (-1) (g i) (g' i)) := (hg i).lin (hg' i) 1 (-1)
    rw [contT_famW_lin hN ρ hS hd hE c _ hM i (g i) (tfLin 1 (-1) (g i) (g' i)) (g' i) 1 1
      (fun y => by simp only [tfLin_apply]; ring) (hg i) hΔ (hg' i)]
    rw [show ∀ a b : ℝ, 1 * a + 1 * b - b = a from fun a b => by ring]
    refine (hK _ (okW_update hM i hΔ)).trans ?_
    have hp := prod_update_eq (fun _ v => l1 v) (mixW g' g (i : ℕ)) i (tfLin 1 (-1) (g i) (g' i))
    rw [hp, mul_assoc K]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have hMB : ∀ l, l1 (mixW g' g (i : ℕ) l) ≤ B := by
      intro l
      simp only [mixW]
      split_ifs
      · exact hB l
      · exact hB' l
    have hε0 : 0 ≤ ε := (CompReduce.l1_nonneg _).trans (hε i)
    refine mul_le_mul (hε i) ?_ (Finset.prod_nonneg fun l _ => CompReduce.l1_nonneg _) hε0
    calc ∏ l ∈ Finset.univ.erase i, l1 (mixW g' g (i : ℕ) l)
        ≤ ∏ _l ∈ Finset.univ.erase i, B :=
          Finset.prod_le_prod (fun l _ => CompReduce.l1_nonneg _) (fun l _ => hMB l)
      _ = B ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  calc |∑ i : Fin n, (contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g i)))
        - contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g' i))))|
      ≤ ∑ i : Fin n, |contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g i)))
        - contT hN ρ (famW c (Function.update (mixW g' g (i : ℕ)) i (g' i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, K * ε * B ^ (n - 1) := Finset.sum_le_sum fun i _ => hterm i
    _ = n * (K * ε * B ^ (n - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Real translation invariance of the continuum reading**, from `OS1Sep` and `SepConv`.
DERIVED: no numeral. -/
theorem contT_translate_eq (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) (h1 : OS1Sep hN ρ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) (hF : Adm F) (v : Fin 4 → ℝ) :
    contT hN ρ (fun i => translateD v (F i)) = contT hN ρ F := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact tendsto_nhds_unique (hS _ _ (ClayWiring.adm_translate hF v)) (h1 _ F hF v)

end Env

/-! ## 3. Uniform estimates on one test function -/

section Unif

/-- A test function has compact support. An alias of `CompositeOS0Test.hasCompactSupport_testFn`. -/
alias hasCompactSupport_tf := MassGap.CompositeOS0Test.hasCompactSupport_testFn

/-- DERIVED: `1` the unit entry. -/
theorem abs_dir_le (ν i : Fin 4) : |dir ν i| ≤ 1 := by
  by_cases h : i = ν
  · subst h
    simp [dir]
  · simp [dir, h]

/-- The translate by `s e`, `|eᵢ| ≤ 1`, is within `|s|` of the point. DERIVED: `1` the bound on `e`. -/
theorem dist_sub_smul_le (y e : Fin 4 → ℝ) (he : ∀ i, |e i| ≤ 1) (s : ℝ) :
    dist (y - s • e) y ≤ |s| := by
  refine (dist_pi_le_iff (abs_nonneg s)).2 fun i => ?_
  rw [Real.dist_eq]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, abs_neg, abs_mul]
  calc |s| * |e i| ≤ |s| * 1 := mul_le_mul_of_nonneg_left (he i) (abs_nonneg s)
    _ = |s| := mul_one _

/-- **Translations converge uniformly**: `sup_y |f(y − t e) − f(y)| ≤ η` for small `t`.
DERIVED: `0` the limit point; `1` the bound on `e`. -/
theorem translate_unif (f : TestFn) (hf : Continuous f.1) (e : Fin 4 → ℝ) (he : ∀ i, |e i| ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y, |(f.translate (t • e)).1 y - f.1 y| ≤ η := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
    ((hasCompactSupport_tf f).uniformContinuous_of_continuous hf) η hη
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht y
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have hd : dist (y - t • e) y < δ := (dist_sub_smul_le y e he t).trans_lt ht
  have := hδf hd
  rw [Real.dist_eq] at this
  exact this.le

/-- **Difference quotients converge uniformly**: for `f` of class `C¹`,
`|f(y − t e_ν) − f(y) + t ∂_ν f(y)| ≤ η |t|` for small `t`, every `y`.
DERIVED: `0` the limit point; `1` the differentiability order. -/
theorem dq_unif (f df : TestFn) (hC : ContDiff ℝ 1 f.1) (ν : Fin 4)
    (hdf : ∀ x, df.1 x = fderiv ℝ f.1 x (dir ν)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y, |f.1 (y - t • dir ν) - f.1 y + t * df.1 y| ≤ η * |t| := by
  have hdc : Continuous df.1 := by
    rw [show df.1 = fun x => fderiv ℝ f.1 x (dir ν) from funext hdf]
    exact (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
    ((hasCompactSupport_tf df).uniformContinuous_of_continuous hdc) η hη
  have hdiff : Differentiable ℝ f.1 := hC.differentiable one_ne_zero
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht y
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f.1 (y - s • dir ν) + s * df.1 y)
      (-(df.1 (y - s • dir ν)) + df.1 y) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => y - s • dir ν) (-(dir ν)) s := by
      simpa using ((hasDerivAt_id s).smul_const (dir ν)).const_sub y
    have h1 := (hdiff (y - s • dir ν)).hasFDerivAt.comp_hasDerivAt s hl
    have h2 := h1.add ((hasDerivAt_id s).mul_const (df.1 y))
    refine h2.congr_deriv ?_
    rw [map_neg, ← hdf, one_mul]
  have hb : ∀ s ∈ Metric.ball (0 : ℝ) δ, ‖-(df.1 (y - s • dir ν)) + df.1 y‖ ≤ η := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    have hd : dist y (y - s • dir ν) < δ := by
      rw [dist_comm]
      exact (dist_sub_smul_le y (dir ν) (abs_dir_le ν) s).trans_lt hs
    have := hδf hd
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs, neg_add_eq_sub]
    exact this.le
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => f.1 (y - s • dir ν) + s * df.1 y)
    (fun s _ => (hder s).hasDerivWithinAt) hb (convex_ball 0 δ) (Metric.mem_ball_self hδ) ht
  simp only [zero_smul, sub_zero, zero_mul, add_zero, Real.norm_eq_abs] at hmv
  calc |f.1 (y - t • dir ν) - f.1 y + t * df.1 y|
      = |f.1 (y - t • dir ν) + t * df.1 y - f.1 y| := by congr 1; ring
    _ ≤ η * |t| := hmv

/-- **The `L¹` norm is at most the sup bound times the cube volume.** DERIVED: `2` the side of the
cube; `4` the dimension. -/
theorem l1_le_cube (g : TestFn) {R M : ℝ} (hR : 0 ≤ R) (hM : ∀ y, |g.1 y| ≤ M)
    (hs : ∀ y, g.1 y ≠ 0 → ∀ i, |y i| ≤ R) : l1 g ≤ M * (2 * R) ^ 4 := by
  have hle : ∀ y, |g.1 y| ≤ (Set.Icc (fun _ : Fin 4 => -R) (fun _ => R)).indicator (fun _ => M) y := by
    intro y
    by_cases hy : y ∈ Set.Icc (fun _ : Fin 4 => -R) (fun _ => R)
    · rw [Set.indicator_of_mem hy]
      exact hM y
    · rw [Set.indicator_of_notMem hy]
      by_contra hne
      have hg : g.1 y ≠ 0 := fun h0 => hne (by rw [h0, abs_zero])
      exact hy (Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i => (abs_le.mp (hs y hg i)).1,
        Pi.le_def.mpr fun i => (abs_le.mp (hs y hg i)).2⟩)
  have hint : Integrable ((Set.Icc (fun _ : Fin 4 => -R) (fun _ => R)).indicator fun _ => M) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)
  have hRR : (fun _ : Fin 4 => -R) ≤ fun _ => R := fun _ => by linarith
  calc l1 g = ∫ y, |g.1 y| := rfl
    _ ≤ ∫ y, (Set.Icc (fun _ : Fin 4 => -R) (fun _ => R)).indicator (fun _ => M) y :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hint
          (Eventually.of_forall hle)
    _ = M * (2 * R) ^ 4 := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, measureReal_def,
          Real.volume_Icc_pi_toReal hRR]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- DERIVED: no numeral. -/
theorem lin_aux {t X Y : ℝ} (ht : t ≠ 0) : X = t * (1 / t * X + -1 / t * Y) + 1 * Y := by
  have h : t * (1 / t) = 1 := mul_one_div_cancel ht
  have h' : t * (-1 / t) = -1 := by rw [neg_div, mul_neg, h]
  linear_combination (-X) * h + (-Y) * h'

/-- DERIVED: no numeral. -/
theorem dq_aux {t X Y Z η : ℝ} (ht : t ≠ 0) (h : |X - Y + t * Z| ≤ η * |t|) :
    |1 * (1 / t * X + -1 / t * Y) + -1 * (-1 * Z + 0 * Z)| ≤ η := by
  have htu : t * (1 / t) = 1 := mul_one_div_cancel ht
  have e : 1 * (1 / t * X + -1 / t * Y) + -1 * (-1 * Z + 0 * Z) = 1 / t * (X - Y + t * Z) := by
    linear_combination (-Z) * htu
  rw [e, abs_mul]
  calc |1 / t| * |X - Y + t * Z| ≤ |1 / t| * (η * |t|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = η * |t * (1 / t)| := by rw [abs_mul]; ring
    _ = η := by rw [htu, abs_one, mul_one]

end Unif
/-! ## 4. The global translation Ward identity -/

section Global

/-- **The global translation Ward identity**: for every admissible family of `C¹` test functions,
`∑ᵢ S(F with fᵢ ↦ ∂_ν fᵢ) = 0`. DERIVED: `1` the differentiability order; `0` the value. -/
def WardGlobal (hN : N ≠ 0) (ρ : RenormMix N) : Prop :=
  ∀ (ν : Fin 4) (n : ℕ) (F : Fin n → TDatum) (df : Fin n → TestFn), Adm F →
    (∀ i, ContDiff ℝ 1 (F i).2.1) → (∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) →
    ∑ i, contT hN ρ (Function.update F i ((F i).1, df i)) = 0

/-- The difference quotient `(f(· − t e) − f)/t`. DERIVED: `1` the coefficients. -/
def dqW (t : ℝ) (e : Fin 4 → ℝ) (f : TestFn) : TestFn :=
  tfLin (1 / t) (-1 / t) (f.translate (t • e)) f

/-- The negated test function. DERIVED: `1`, `0` the coefficients. -/
def negW (g : TestFn) : TestFn := tfLin (-1) 0 g g

/-- The envelope of a family: the points within `r` of the support of each test function.
DERIVED: `0` the vanishing value. -/
def envW {n : ℕ} (f : Fin n → TestFn) (r : ℝ) : Fin n → Set (Fin 4 → ℝ) :=
  fun i => {y | ∃ x, (f i).1 x ≠ 0 ∧ dist x y ≤ r}

/-- DERIVED: `0` the vanishing value. -/
theorem mem_envW {n : ℕ} (f : Fin n → TestFn) (r : ℝ) (i : Fin n) (y : Fin 4 → ℝ) :
    y ∈ envW f r i ↔ ∃ x, (f i).1 x ≠ 0 ∧ dist x y ≤ r := Iff.rfl

/-- The reading with the slots `< j` translated by `t e_ν`, slot `j` the difference quotient.
DERIVED: no numeral. -/
def AW (hN : N ≠ 0) (ρ : RenormMix N) {n : ℕ} (c : Fin n → Idx4 → ℝ) (f : Fin n → TestFn)
    (ν : Fin 4) (t : ℝ) (j : Fin n) : ℝ :=
  contT hN ρ (famW c (Function.update (mixW f (fun l => (f l).translate (t • dir ν)) (j : ℕ)) j
    (dqW t (dir ν) (f j))))

/-- **`WardGlobal` from `SepConv`, `OS1Sep` and `OS0Sep`.**
DERIVED: `4` the quarter of the separation kept by the envelopes; `2` the half of the separation and
the side of the cube; `1` the top of the separation and the unit bounds; `0` the limit point. -/
theorem wardGlobal_of_os (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) (h1 : OS1Sep hN ρ)
    (h0 : OS0Sep hN ρ) : WardGlobal hN ρ := by
  intro ν n F df hF hC hdf
  obtain ⟨c, f, rfl⟩ : ∃ (c : Fin n → Idx4 → ℝ) (f : Fin n → TestFn), F = famW c f :=
    ⟨fun i => (F i).1, fun i => (F i).2, rfl⟩
  simp only [← famW_update]
  obtain ⟨hcF, d0, hd0, hsF⟩ := hF
  have hd : 0 < min (d0 / 2) 1 := lt_min (by linarith) one_pos
  have hd1 : min (d0 / 2) 1 ≤ 1 := min_le_right _ _
  have he1 : ∀ i, |dir ν i| ≤ 1 := abs_dir_le ν
  -- the envelopes are separated
  have hE : SepEnvW (min (d0 / 2) 1) (envW f (d0 / 4)) := by
    intro i j hij x hx y hy
    obtain ⟨x', hx', hxx⟩ := (mem_envW f _ i x).1 hx
    obtain ⟨y', hy', hyy⟩ := (mem_envW f _ j y).1 hy
    obtain ⟨m, hm⟩ := hsF i j hij x' y' hx' hy'
    refine ⟨m, (min_le_left _ _).trans ?_⟩
    have h1' : |x' m - x m| ≤ d0 / 4 := by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist x' x m).trans hxx
    have h2' : |y' m - y m| ≤ d0 / 4 := by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist y' y m).trans hyy
    have h3 := abs_sub_le (x' m) (x m) (y' m)
    have h4 := abs_sub_le (x m) (y m) (y' m)
    rw [abs_sub_comm (y m) (y' m)] at h4
    linarith
  -- the test functions in their envelopes
  have okf : ∀ i, OkW (envW f (d0 / 4) i) (f i) := fun i =>
    ⟨hcF i, fun y hy => (mem_envW f _ i y).2 ⟨y, hy, by rw [dist_self]; linarith⟩⟩
  have okτ : ∀ t : ℝ, |t| ≤ d0 / 4 → ∀ i, OkW (envW f (d0 / 4) i) ((f i).translate (t • dir ν)) := by
    intro t ht i
    refine ⟨(hcF i).comp (continuous_id.sub continuous_const), fun y hy => ?_⟩
    exact (mem_envW f _ i y).2 ⟨y - t • dir ν, hy, (dist_sub_smul_le y (dir ν) he1 t).trans ht⟩
  have hdfc : ∀ i, Continuous (df i).1 := by
    intro i
    rw [show (df i).1 = fun x => fderiv ℝ (f i).1 x (dir ν) from funext (hdf i)]
    exact ((hC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have okdf : ∀ i, OkW (envW f (d0 / 4) i) (df i) := by
    intro i
    refine ⟨hdfc i, fun y hy => ?_⟩
    have hne : fderiv ℝ (f i).1 y ≠ 0 := by
      intro h0
      apply hy
      rw [hdf i y]
      show fderiv ℝ (f i).1 y (dir ν) = 0
      rw [h0]
      rfl
    obtain ⟨x', hxx', hx'⟩ := WardFromLattice.exists_ne_zero_near hne (d0 / 4) (by linarith)
    exact (mem_envW f _ i y).2 ⟨x', hx', by rw [dist_comm]; exact hxx'.le⟩
  have okD : ∀ t : ℝ, |t| ≤ d0 / 4 → ∀ i, OkW (envW f (d0 / 4) i) (dqW t (dir ν) (f i)) :=
    fun t ht i => (okτ t ht i).lin (okf i) _ _
  have okN : ∀ i, OkW (envW f (d0 / 4) i) (negW (df i)) := fun i => (okdf i).lin (okdf i) _ _
  -- step 1: the telescoped identity at every small `t ≠ 0`
  have hid : ∀ t : ℝ, t ≠ 0 → |t| ≤ d0 / 4 → ∑ j, AW hN ρ c f ν t j = 0 := by
    intro t ht0 htd
    have hτ := okτ t htd
    have hTel := telescopeW (fun u => contT hN ρ (famW c u)) f
      (fun l => (f l).translate (t • dir ν))
    have hinv : contT hN ρ (famW c (fun l => (f l).translate (t • dir ν)))
        = contT hN ρ (famW c f) :=
      contT_translate_eq hN ρ hS h1 (famW c f) (adm_famW hd hE c okf) (t • dir ν)
    rw [hinv, sub_self] at hTel
    have hterm : ∀ j : Fin n,
        contT hN ρ (famW c (Function.update (mixW f (fun l => (f l).translate (t • dir ν)) (j : ℕ))
            j ((f j).translate (t • dir ν))))
          - contT hN ρ (famW c (Function.update (mixW f (fun l => (f l).translate (t • dir ν))
            (j : ℕ)) j (f j))) = t * AW hN ρ c f ν t j := by
      intro j
      rw [contT_famW_lin hN ρ hS hd hE c _ (okW_mix okf hτ (j : ℕ)) j ((f j).translate (t • dir ν))
        (dqW t (dir ν) (f j)) (f j) t 1 (fun y => lin_aux ht0) (hτ j) (okD t htd j) (okf j)]
      unfold AW
      ring
    simp only [hterm, ← Finset.mul_sum] at hTel
    exact (mul_eq_zero.mp hTel.symm).resolve_left ht0
  -- step 2: each term converges
  obtain ⟨K, hK0, hK⟩ := os0_famW hN ρ h0 c hd hd1
  have hKE := hK _ hE
  obtain ⟨Rc, hRcdef⟩ : ∃ Rc : ℝ, Rc = ∑ i, MultiScaleAll.tR (f i) + d0 := ⟨_, rfl⟩
  obtain ⟨Mx, hMxdef⟩ : ∃ Mx : ℝ,
      Mx = ∑ i, (MultiScaleAll.tM (f i) + MultiScaleAll.tM (df i)) + 1 := ⟨_, rfl⟩
  have hRnn : ∀ i, 0 ≤ MultiScaleAll.tR (f i) := fun i => (MultiScaleAll.tIs (f i)).1
  have hMnn : ∀ g : TestFn, 0 ≤ MultiScaleAll.tM g := fun g => (MultiScaleAll.tIs g).M_nonneg
  have hRc : ∀ i, MultiScaleAll.tR (f i) + d0 / 4 ≤ Rc := by
    intro i
    have := Finset.single_le_sum (f := fun l => MultiScaleAll.tR (f l)) (fun l _ => hRnn l)
      (Finset.mem_univ i)
    linarith
  have hRc0 : 0 ≤ Rc := by
    have : 0 ≤ ∑ i, MultiScaleAll.tR (f i) := Finset.sum_nonneg fun l _ => hRnn l
    linarith
  have hMx : ∀ i, MultiScaleAll.tM (f i) + MultiScaleAll.tM (df i) + 1 ≤ Mx := by
    intro i
    have := Finset.single_le_sum (f := fun l => MultiScaleAll.tM (f l) + MultiScaleAll.tM (df l))
      (fun l _ => add_nonneg (hMnn _) (hMnn _)) (Finset.mem_univ i)
    linarith
  have hMx0 : 0 ≤ Mx := by
    have : 0 ≤ ∑ i, (MultiScaleAll.tM (f i) + MultiScaleAll.tM (df i)) :=
      Finset.sum_nonneg fun l _ => add_nonneg (hMnn _) (hMnn _)
    linarith
  have cube : ∀ i y, y ∈ envW f (d0 / 4) i → ∀ m, |y m| ≤ Rc := by
    intro i y hy m
    obtain ⟨x, hx, hxy⟩ := (mem_envW f _ i y).1 hy
    have h1' := (MultiScaleAll.tIs (f i)).2.2 x hx m
    have h2' : |x m - y m| ≤ d0 / 4 := by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist x y m).trans hxy
    have h3 := abs_sub_abs_le_abs_sub (y m) (x m)
    rw [abs_sub_comm] at h3
    linarith [hRc i]
  have l1E : ∀ i (g : TestFn) (M : ℝ), OkW (envW f (d0 / 4) i) g → (∀ y, |g.1 y| ≤ M) →
      l1 g ≤ M * (2 * Rc) ^ 4 :=
    fun i g M hg hM => l1_le_cube g hRc0 hM fun y hy => cube i y (hg.2 y hy)
  have hsm : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ d0 / 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < d0 / 4)] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  have hB0 : 0 ≤ Mx * (2 * Rc) ^ 4 := mul_nonneg hMx0 (pow_nonneg (by linarith) 4)
  have hconv : ∀ j : Fin n, Tendsto (fun t => AW hN ρ c f ν t j) (𝓝[≠] 0)
      (𝓝 (contT hN ρ (famW c (Function.update f j (negW (df j)))))) := by
    intro j
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = n * K * (2 * Rc) ^ 4 * (Mx * (2 * Rc) ^ 4) ^ (n - 1) :=
      ⟨_, rfl⟩
    have hQ : 0 ≤ Q := by
      rw [hQdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hK0)
        (pow_nonneg (by linarith) 4)) (pow_nonneg hB0 _)
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (Q + 1) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      exact div_pos hε (by linarith)
    have hη1 : 0 < min η 1 := lt_min hη one_pos
    have hU1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i y,
        |((f i).translate (t • dir ν)).1 y - (f i).1 y| ≤ η :=
      Filter.eventually_all.2 fun i => translate_unif (f i) (hcF i) (dir ν) he1 hη
    have hU2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i y,
        |(f i).1 (y - t • dir ν) - (f i).1 y + t * (df i).1 y| ≤ min η 1 * |t| :=
      Filter.eventually_all.2 fun i => dq_unif (f i) (df i) (hC i) ν (hdf i) hη1
    filter_upwards [nhdsWithin_le_nhds hU1, nhdsWithin_le_nhds hU2, nhdsWithin_le_nhds hsm,
      self_mem_nhdsWithin] with t hu1 hu2 htd ht0
    have ht0' : t ≠ 0 := ht0
    have hDj : ∀ y, |(tfLin 1 (-1) (dqW t (dir ν) (f j)) (negW (df j))).1 y| ≤ min η 1 :=
      fun y => dq_aux ht0' (hu2 j y)
    have hB : ∀ l, l1 (Function.update (mixW f (fun l => (f l).translate (t • dir ν)) (j : ℕ)) j
        (dqW t (dir ν) (f j)) l) ≤ Mx * (2 * Rc) ^ 4 := by
      intro l
      by_cases hl : l = j
      · rw [hl, Function.update_self]
        refine l1E j _ Mx (okD t htd j) fun y => ?_
        have h1' := hDj y
        have h2' := (MultiScaleAll.tIs (df j)).2.1 y
        have h3' := hMx j
        have h4' := hMnn (f j)
        have hrel : (tfLin 1 (-1) (dqW t (dir ν) (f j)) (negW (df j))).1 y
            = (dqW t (dir ν) (f j)).1 y + (df j).1 y := by
          simp only [tfLin_apply, negW]
          ring
        rw [hrel] at h1'
        have h5 : |(dqW t (dir ν) (f j)).1 y|
            ≤ |(dqW t (dir ν) (f j)).1 y + (df j).1 y| + |(df j).1 y| := by
          have := abs_add_le ((dqW t (dir ν) (f j)).1 y + (df j).1 y) (-(df j).1 y)
          rw [add_neg_cancel_right, abs_neg] at this
          exact this
        linarith [min_le_right η 1]
      · rw [Function.update_of_ne hl]
        simp only [mixW]
        split_ifs
        · exact l1E l _ Mx (okτ t htd l) fun y =>
            ((MultiScaleAll.tIs (f l)).2.1 (y - t • dir ν)).trans (by linarith [hMx l, hMnn (df l)])
        · exact l1E l _ Mx (okf l) fun y =>
            ((MultiScaleAll.tIs (f l)).2.1 y).trans (by linarith [hMx l, hMnn (df l)])
    have hB' : ∀ l, l1 (Function.update f j (negW (df j)) l) ≤ Mx * (2 * Rc) ^ 4 := by
      intro l
      by_cases hl : l = j
      · rw [hl, Function.update_self]
        refine l1E j _ Mx (okN j) fun y => ?_
        have h2' := (MultiScaleAll.tIs (df j)).2.1 y
        have h3' := hMx j
        have h4' := hMnn (f j)
        show |-1 * (df j).1 y + 0 * (df j).1 y| ≤ Mx
        rw [show -1 * (df j).1 y + 0 * (df j).1 y = -(df j).1 y by ring, abs_neg]
        linarith
      · rw [Function.update_of_ne hl]
        exact l1E l _ Mx (okf l) fun y =>
          ((MultiScaleAll.tIs (f l)).2.1 y).trans (by linarith [hMx l, hMnn (df l)])
    have hε' : ∀ l, l1 (tfLin 1 (-1)
        (Function.update (mixW f (fun l => (f l).translate (t • dir ν)) (j : ℕ)) j
          (dqW t (dir ν) (f j)) l) (Function.update f j (negW (df j)) l)) ≤ η * (2 * Rc) ^ 4 := by
      intro l
      by_cases hl : l = j
      · rw [hl, Function.update_self, Function.update_self]
        exact l1E j _ η ((okD t htd j).lin (okN j) 1 (-1)) fun y =>
          (hDj y).trans (min_le_left _ _)
      · rw [Function.update_of_ne hl, Function.update_of_ne hl]
        simp only [mixW]
        split_ifs
        · refine l1E l _ η ((okτ t htd l).lin (okf l) 1 (-1)) fun y => ?_
          show |1 * ((f l).translate (t • dir ν)).1 y + -1 * (f l).1 y| ≤ η
          rw [show 1 * ((f l).translate (t • dir ν)).1 y + -1 * (f l).1 y
            = ((f l).translate (t • dir ν)).1 y - (f l).1 y by ring]
          exact hu1 l y
        · refine l1E l _ η ((okf l).lin (okf l) 1 (-1)) fun y => ?_
          show |1 * (f l).1 y + -1 * (f l).1 y| ≤ η
          rw [show 1 * (f l).1 y + -1 * (f l).1 y = 0 by ring, abs_zero]
          exact hη.le
    have hfin := abs_sub_le_envW hN ρ hS c hd hE hKE hK0 _ _
      (okW_update (okW_mix okf (okτ t htd) (j : ℕ)) j (okD t htd j))
      (okW_update okf j (okN j)) hB hB' hε'
    rw [Real.dist_eq]
    unfold AW
    calc _ ≤ (n : ℝ) * (K * (η * (2 * Rc) ^ 4) * (Mx * (2 * Rc) ^ 4) ^ (n - 1)) := hfin
      _ = η * Q := by rw [hQdef]; ring
      _ < η * (Q + 1) := mul_lt_mul_of_pos_left (by linarith) hη
      _ = ε := by rw [hηdef]; exact div_mul_cancel₀ ε (by linarith : (0 : ℝ) < Q + 1).ne'
  -- step 3: the limit of the identity
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∑ j, AW hN ρ c f ν t j = 0 := by
    filter_upwards [nhdsWithin_le_nhds hsm, self_mem_nhdsWithin] with t htd ht0
    exact hid t ht0 htd
  have hT0 : ∑ j, contT hN ρ (famW c (Function.update f j (negW (df j)))) = 0 :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun j _ => hconv j)
      (tendsto_const_nhds.congr' (hsmall.mono fun t ht => ht.symm))
  -- step 4: `−∂_ν f` to `∂_ν f`
  have hTneg : ∀ j, contT hN ρ (famW c (Function.update f j (negW (df j))))
      = -contT hN ρ (famW c (Function.update f j (df j))) := by
    intro j
    rw [contT_famW_lin hN ρ hS hd hE c f okf j (negW (df j)) (df j) (df j) (-1) 0 (fun y => rfl)
      (okN j) (okdf j) (okdf j)]
    ring
  simp only [hTneg, Finset.sum_neg_distrib, neg_eq_zero] at hT0
  exact hT0

end Global

/-! ## 5. `WardT` reduced to the off-probe clause -/

section Off

/-- **A one-insertion reading vanishes** at every step and mixing: the inserted field is connected and
the state is translation invariant. DERIVED: `1` the number of insertions; `0` the value. -/
theorem latT_one_zero (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) (G : Fin 1 → TDatum) :
    latT hN ρ k G = 0 := by
  unfold latT
  refine Finset.sum_eq_zero fun b _ => ?_
  have h : latSk hN k (fun i => locField hN ρ k (b i) (G i).2) = 0 := by
    show stateK hN k (∏ i, CompReduce.sf hN ρ k (b i) (G i).2) = 0
    rw [Fin.prod_univ_one]
    exact ContinuumNontrivial.stateK_smear_connected hN k (ρ.op (b 0)) (G 0).2
  rw [h, mul_zero]

/-- DERIVED: `1` the number of insertions; `0` the value. -/
theorem contT_one_zero (hN : N ≠ 0) (ρ : RenormMix N) (G : Fin 1 → TDatum) : contT hN ρ G = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have e : ∀ k, latT hN ρ k G = 0 := fun k => latT_one_zero hN ρ k G
  unfold contT
  simp only [e]
  exact tendsto_const_nhds.limUnder_eq

/-- **The off-probe Ward clause**: `WardT` on families with at least one insertion whose first
insertion is not in `I` (`h` vanishes near the first probe).
DERIVED: `1` the differentiability order, the value of `h` and the extra slot; `0` its other value,
the first slot and the sign of the separation. -/
def WardOff (hN : N ≠ 0) (ρ : RenormMix N) : Prop :=
  ∃ κ : ℝ, ∀ (ν : Fin 4) (n : ℕ) (F : Fin (n + 1) → TDatum) (I : Finset (Fin (n + 1)))
      (h : (Fin 4 → ℝ) → ℝ) (dh : Fin 4 → TestFn) (df : Fin (n + 1) → TestFn) (d : ℝ),
    0 ∉ I → 0 < d → Adm F → ContDiff ℝ 1 h → (∀ μ x, (dh μ).1 x = fderiv ℝ h x (dir μ)) →
    (∀ i, ContDiff ℝ 1 (F i).2.1) → (∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) →
    (∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d → h y = if i ∈ I then 1 else 0) →
    ∑ μ, contT hN ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F)
      = -∑ i ∈ I, contT hN ρ (Function.update F i ((F i).1, df i))

/-- `WardT` contains `WardOff`. DERIVED: no numeral. -/
theorem wardOff_of_wardT (hN : N ≠ 0) (ρ : RenormMix N) (hW : WardT hN ρ) : WardOff hN ρ := by
  obtain ⟨κ, hκ⟩ := hW
  exact ⟨κ, fun ν n F I h dh df d _ hd hF hh hdh hFc hdf hloc =>
    hκ ν (n + 1) F I h dh df d hd hF hh hdh hFc hdf hloc⟩

/-- **`WardT` from `SepConv`, `WardGlobal` and `WardOff`.** With no probes both sides vanish
(`contT_one_zero`); with the first probe outside `I` it is `WardOff`; with the first probe in `I`,
`WardOff` at `1 − h` and `Iᶜ`, linearity in the stress slot and `WardGlobal` give it.
DERIVED: `1` the constant of `1 − h` and the coefficient; `0` the first slot and the values. -/
theorem wardT_of_off (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ) (hG : WardGlobal hN ρ)
    (hW : WardOff hN ρ) : WardT hN ρ := by
  obtain ⟨κ, hκ⟩ := hW
  refine ⟨κ, fun ν n F I h dh df d hd hF hh hdh hFc hdf hloc => ?_⟩
  cases n with
  | zero =>
    rw [Finset.sum_eq_zero (fun i _ => Fin.elim0 i), neg_zero]
    exact Finset.sum_eq_zero fun μ _ => contT_one_zero hN ρ _
  | succ m =>
    by_cases h0 : (0 : Fin (m + 1)) ∈ I
    · have hh' : ContDiff ℝ 1 (fun y => 1 - h y) := contDiff_const.sub hh
      have hdh' : ∀ μ x, (negW (dh μ)).1 x = fderiv ℝ (fun y => 1 - h y) x (dir μ) := by
        intro μ x
        show -1 * (dh μ).1 x + 0 * (dh μ).1 x = fderiv ℝ (fun y => 1 - h y) x (dir μ)
        rw [fderiv_const_sub]
        show -1 * (dh μ).1 x + 0 * (dh μ).1 x = -(fderiv ℝ h x (dir μ))
        rw [← hdh]
        ring
      have hloc' : ∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d →
          (fun y => 1 - h y) y = if i ∈ Iᶜ then 1 else 0 := by
        intro i x y hx hxy
        have e := hloc i x y hx hxy
        by_cases hi : i ∈ I
        · simp [hi, e]
        · simp [hi, e]
      have hK := hκ ν m F Iᶜ (fun y => 1 - h y) (fun μ => negW (dh μ)) df d (by simp [h0]) hd hF
        hh' hdh' hFc hdf hloc'
      have hneg : ∀ μ, contT hN ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, negW (dh μ)) F)
          = -contT hN ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F) := by
        intro μ
        have hupd : ∀ w : TestFn,
            Function.update (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F) 0
              (((Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F :
                Fin (m + 1 + 1) → TDatum) 0).1, w)
            = Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, w) F := by
          intro w
          simp only [Fin.cons_zero, Fin.update_cons_zero]
        have hA := WardFromLattice.adm_stress hF hd hh hdh hloc (stressC κ μ ν) μ
        have hA' := WardFromLattice.adm_stress hF hd hh' hdh' hloc' (stressC κ μ ν) μ
        rw [← hupd] at hA hA'
        have key := contT_update_lin hN ρ hS
          (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F) 0 (negW (dh μ)) (dh μ) (dh μ)
          (-1) 0 (fun y => rfl) hA' hA hA
        rw [hupd, hupd] at key
        rw [key]
        ring
      simp only [hneg, Finset.sum_neg_distrib, neg_inj] at hK
      have hglob := hG ν (m + 1) F df hF hFc hdf
      have hsplit := Finset.sum_add_sum_compl I
        (fun i => contT hN ρ (Function.update F i ((F i).1, df i)))
      rw [hK]
      linarith
    · exact hκ ν m F I h dh df d h0 hd hF hh hdh hFc hdf hloc

/-- **Under `SepConv` and `WardGlobal`, `WardT` and `WardOff` are equivalent.** DERIVED: no numeral. -/
theorem wardT_iff_wardOff (hN : N ≠ 0) (ρ : RenormMix N) (hS : SepConv hN ρ)
    (hG : WardGlobal hN ρ) : WardT hN ρ ↔ WardOff hN ρ :=
  ⟨wardOff_of_wardT hN ρ, wardT_of_off hN ρ hS hG⟩

end Off

end MassGap.WardN

/-! ## 6. The capstone with `WardOff` -/

namespace MassGap.WardN

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN MassGap.FlowCovN

variable {N : ℕ}

/-- **`WardGlobal` at `rhoD (fR N) z` from the listed inputs**, at every `SU(N)`: `SepConv`, `OS1Sep`,
`OS0Sep` of the tensor sector from `ScaleControlAll`, `ExpandStrong` and `CoefBound`
(`CompReduce.os1Sep_of_comp`, `CompReduce.os0Sep_of_comp`, `WardFromLattice.sepConv_of_scale_expand`).
DERIVED: no numeral. -/
theorem wardGlobal_of_scale [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb : 0 < b) (hsc : ScaleControlAll b Wf)
    (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf) :
    WardGlobal (NeZero.ne N) (rhoD (fR N) z) := by
  have hex := expandR_of_strong hE
  have hconv := convC_of_choice hb hsc hE
  exact wardGlobal_of_os _ _
    (WardFromLattice.sepConv_of_scale_expand hb hsc hex)
    (CompReduce.os1Sep_of_comp _ _ (CRen N z μ) eI (fun k α => buildRen_he2 _ _ μ k α) hconv
      (os1C_of_scale_expand hb hsc hex))
    (CompReduce.os0Sep_of_comp _ _ (CRen N z μ) eI (fun k α => buildRen_he2 _ _ μ k α) hconv
      (os0C_of_scale_expand_coef hb hsc hex hcb))

/-- **The per-`N` inputs with `WardOff` in place of `WardT`**: `FlowCovN.FlowCovInputsN` with its clause
`WardT (rhoD (fR N) (zFix N zri zwe))` replaced by `WardOff` at the same data.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of the
block-step flow. -/
def FlowCovWardInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardOff (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`FlowCovWardInputsN` gives `FlowCovInputsN`**: `WardT` from `WardOff` (`wardT_of_off`), with
`SepConv` and `WardGlobal` from the substrate, `ExpandStrong` and `CoefBound`.
DERIVED: `2` the least colour count. -/
theorem flowCovInputsN_of_ward (hN2 : 2 ≤ N) (h : FlowCovWardInputsN N hN2) :
    FlowCovInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hA,
    h3, hfar⟩ := h
  have hS := WardFromLattice.sepConv_of_scale_expand S.b_pos S.scale (expandR_of_strong hE)
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV,
    wardT_of_off _ _ hS (wardGlobal_of_scale S.b_pos S.scale hE hC) hW, hP, hA, h3, hfar⟩

/-- **`ClayStatementDy` from `FlowCovWardInputsN` at every `N ≥ 2`** (`FlowCovN.clayStatement_of_covC`).
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_wardOff (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), FlowCovWardInputsN N hN2) :
    MassGap.ClayStatementDy :=
  clayStatement_of_covC fun N hN2 => flowCovInputsN_of_ward hN2 (h N hN2)

end MassGap.WardN

end

#print axioms MassGap.WardN.latT_update_lin
#print axioms MassGap.WardN.contT_update_lin
#print axioms MassGap.WardN.telescopeW
#print axioms MassGap.WardN.os0_famW
#print axioms MassGap.WardN.abs_sub_le_envW
#print axioms MassGap.WardN.contT_translate_eq
#print axioms MassGap.WardN.translate_unif
#print axioms MassGap.WardN.dq_unif
#print axioms MassGap.WardN.l1_le_cube
#print axioms MassGap.WardN.wardGlobal_of_os
#print axioms MassGap.WardN.wardGlobal_of_scale
#print axioms MassGap.WardN.latT_one_zero
#print axioms MassGap.WardN.contT_one_zero
#print axioms MassGap.WardN.wardOff_of_wardT
#print axioms MassGap.WardN.wardT_of_off
#print axioms MassGap.WardN.wardT_iff_wardOff
#print axioms MassGap.WardN.flowCovInputsN_of_ward
#print axioms MassGap.WardN.clayStatement_of_wardOff
