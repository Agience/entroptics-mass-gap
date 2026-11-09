import Mathlib
import MassGap.MixConvRP

/-!
# MassGap.CompositesRen — composites renormalised off the tensor indices

`CompositesBuild.build ρ bare` sets `ren k i = bare i` at every index `i` with `dec i.1 = none` (off the
tensor indices): the bare dimensionless lattice field, independent of `k`. `CompositeNondeg` records the
consequence for `CompNondeg`. This module builds a family with the same index set, classical monomials, bare
fields and rotation representation, whose renormalised fields carry the factor `a_k^{−cdim i}` and a
subtraction of lower-dimension bare fields, and re-routes the reflection-averaged SU capstone through it.

## 1. The family `buildRen ρ bare μ`

`μ : OffMix` holds three free inputs: a log-factor `lz k i`, a finite mixing set `J i`, and mixing
coefficients `m k i j`.

* `lowJ μ i`: the elements `j` of `J i` with `cdim j < cdim i` and `(−1)^{ctau 0 j} = (−1)^{ctau 0 i}`.
* `subF μ bare k i = bare i − ∑_{j ∈ lowJ μ i} m k i j • bare j`.
* `sclR N μ k i = e^{lz k i} / a_k^{cdim i}`, `a_k = dySpacing N k`; non-zero for `1 ≤ N` (`sclR_ne`).
* `offF μ bare k i = sclR N μ k i • subF μ bare k i`.
* `renR ρ bare μ k i`: `mixF ρ k α` at `i = eI α` (as in `build`), `offF μ bare k i` elsewhere.
* `buildRen ρ bare μ`: `Ix0`, `Subtype.val`, `bare`, `renR ρ bare μ`, `repF`.

No constant is subtracted: `cField` already subtracts `ν_k(ren k i)`.

## 2. The composites clauses

* `buildRen_he1`, `buildRen_he2`, `buildRen_hrep`: the first two clauses of `TIn` and the tensor
  representation, as for `build`.
* `buildRen_tied_iff`: `Tied` is `TiedB bare`, as for `build`.
* `buildRen_covers`, `buildRen_repTie`: as for `build` (same `cl`, `rep`; the `RepTie` proof is
  `build_repTie`'s).
* `buildRen_renTri`: `RenTri` from `RenTensor ρ bare` (the hypothesis `build_renTri` takes) and `1 ≤ N`. The
  inverse direction is a strong induction on the dimension: the subtraction uses only strictly lower
  dimensions.
* `buildRen_compData`: `CompData` from `TiedB bare`, `RenTensor ρ bare`, `1 ≤ N`.
* `RenormMix`, `ScalarTie`: `ρ` is the same as `build`'s, so these clauses are those of `build`.
* `unifLocal_buildRen`: uniform locality (`JointRP.UnifLocal`): the mixing set `J i` does not depend on `k`.
* `reflCovLat_buildRen`: lattice reflection covariance at the plane `0`, from covariance of the bare fields
  and of the tensor mixing components. The parity filter in `lowJ` makes the subtraction covariant.

## 3. The off-tensor readings

* `latC_off`: on a family of off-tensor indices,
  `latC (buildRen …) k F = (∏ₓ sclR N μ k (F x).1) · latSk k (connected subF)`.
* `latC_noMix`, `latC_two_noMix`: with no mixing at the indices read (`J = ∅` there),
  `latC (buildRen …) k F = (∏ₓ sclR) · latC (build ρ bare) k F`; at two points the factor is
  `e^{lz k i + lz k j} / a_k^{cdim i + cdim j}` written as a product of the two `sclR`.
* `contC_two_noMix`: the two-point continuum reading of `buildRen` is the `ultra` limit of the rescaled
  reading of `build`.
* `offF_eq_zero_iff`: the renormalised field `offF` is the zero field exactly when `bare i` equals its
  lower-dimension combination `∑_{lowJ} m k i j • bare j`.

## 4. The capstone

* `mixConvG_of_cov`, `reflLimG_of_cov`, `jointRPKG_of_reflLim`, `linkCPreG_of_kernels`:
  `MixConvRP.mixConvF_of_cov`, `ReflAvg.reflLim_of_covF`, `ReflAvg.jointRPK_of_reflLimF`,
  `ReflAvg.linkCPre_of_kernelsF` for any composites `Cs` with `UnifLocal Cs` and `ReflCovLat Cs 0` (and for
  the link, a tensor index map `e` with the first two `TIn` clauses), not only `build`.
* `CRen N z μ = buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ`: the reflection-averaged bare fields of
  `ReflAvg`, with the renormalised off-tensor fields. `reflCovLat_CRen` from `reflAvg_refl`, `refl_bareT`
  and `refl_Ecomb`.
* `clayStatementAt_SU_ren`: the SU capstone at `CRen N z μ`. Its inputs are those of
  `MixConvRP.clayStatementAt_SU_reflAvg'` with `hCO`, `hA` read at `CRen N z μ` in place of `CbR N z`, plus
  the free inputs `μ`. `hK`, `hWard` read `rhoD (fR N) z` and `hObs` reads `z`, as in `clayStatementAt_SU_reflAvg'`. `TiedB`,
  `RenTensor`, `hMC`, `JointRPK`, `LinkCPre` and the cross reading are discharged as in `ReflAvg`/`MixConvRP`,
  through the generic lemmas above.

## 5. Argued (no declaration)

* `CompNondeg` at `CRen N z μ` is the remaining physics input on the new composites, inside `hCO`. Its
  hypothesis (a non-zero on-shell top-dimension classical part of `c`) reads only `cl`, which is the same as
  for `build`; its conclusion reads the renormalised readings. With no mixing, `latC_two_noMix` multiplies
  the `build` reading by `a_k^{−cdim i − cdim j}`; where the `build` reading is `a_k^{cdim i + cdim j}` times
  a reading with a non-zero limit (the expected short-distance behaviour, with logarithms absorbed by `lz`),
  the renormalised two-point limit is that non-zero limit. So the obligation is satisfiable in principle;
  it is not proved here.
* The mixing cannot make the renormalised field vanish trivially: by `offF_eq_zero_iff` it vanishes only if
  `bare i` is a combination of strictly lower-dimension bare fields; `Tied` gives `bare i` the classical lead
  `g^{cnF} cval` at dimension `cdim i`, which is expected not to be such a combination whenever that lead
  is non-zero. Not proved here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reflection constant and the empty sums; `1` the unit field, the
least colour count for `a_k > 0` and the unit sign; `2` the least colour count of the capstone, the two
points and the limits of the scalar and pseudoscalar factors; `4` the dimension of `tr F F`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CompositesRen

open Filter
open scoped Topology ContDiff

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.CompositesBuild

variable {N : ℕ}

/-! ## 1. The family -/

section Family

/-- **The off-tensor renormalisation inputs**: a log-factor `lz k i`, a finite mixing set `J i`
(independent of `k`), and mixing coefficients `m k i j`. DERIVED: no numeral. -/
structure OffMix where
  /-- The log-factor of the multiplicative renormalisation. -/
  lz : ℕ → Ix0 → ℝ
  /-- The mixing set. -/
  J : Ix0 → Finset Ix0
  /-- The mixing coefficients. -/
  m : ℕ → Ix0 → Ix0 → ℝ

open Classical in
/-- **The admitted mixing set**: the elements of `J i` of strictly lower dimension and the same
reflection parity at the plane `0`. DERIVED: `0` the plane; `−1` the sign. -/
def lowJ (μ : OffMix) (i : Ix0) : Finset Ix0 :=
  (μ.J i).filter fun j => cdim j.1 < cdim i.1 ∧ (-1 : ℝ) ^ ctau 0 j.1 = (-1 : ℝ) ^ ctau 0 i.1

theorem lowJ_spec {μ : OffMix} {i j : Ix0} (h : j ∈ lowJ μ i) :
    cdim j.1 < cdim i.1 ∧ (-1 : ℝ) ^ ctau 0 j.1 = (-1 : ℝ) ^ ctau 0 i.1 := by
  unfold lowJ at h
  exact (Finset.mem_filter.1 h).2

theorem lowJ_subset (μ : OffMix) (i : Ix0) : lowJ μ i ⊆ μ.J i := by
  unfold lowJ
  exact Finset.filter_subset _ _

/-- **The subtracted bare field** `bare i − ∑_{j ∈ lowJ μ i} m k i j • bare j`. DERIVED: no numeral. -/
def subF (μ : OffMix) (bare : Ix0 → LField (MassGap.SUN.SU N)) (k : ℕ) (i : Ix0) :
    LField (MassGap.SUN.SU N) :=
  ⟨(bare i).1 - ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1,
    Submodule.sub_mem _ (mem_lfSub _)
      (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (mem_lfSub _))⟩

/-- **The renormalisation factor** `e^{lz k i} / a_k^{cdim i}`, `a_k = dySpacing N k`.
DERIVED: no numeral. -/
def sclR (N : ℕ) (μ : OffMix) (k : ℕ) (i : Ix0) : ℝ :=
  Real.exp (μ.lz k i) / dySpacing N k ^ cdim i.1

/-- The factor is non-zero. DERIVED: `1` the least colour count. -/
theorem sclR_ne (hN : 1 ≤ N) (μ : OffMix) (k : ℕ) (i : Ix0) : sclR N μ k i ≠ 0 :=
  div_ne_zero (Real.exp_pos _).ne' (pow_ne_zero _ (dySpacing_pos hN k).ne')

/-- **The renormalised off-tensor field** `sclR N μ k i • subF μ bare k i`. DERIVED: no numeral. -/
def offF (μ : OffMix) (bare : Ix0 → LField (MassGap.SUN.SU N)) (k : ℕ) (i : Ix0) :
    LField (MassGap.SUN.SU N) :=
  ⟨sclR N μ k i • (subF μ bare k i).1, Submodule.smul_mem _ _ (mem_lfSub _)⟩

theorem offF_val (μ : OffMix) (bare : Ix0 → LField (MassGap.SUN.SU N)) (k : ℕ) (i : Ix0) :
    (offF μ bare k i).1 = sclR N μ k i • ((bare i).1 - ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1) :=
  rfl

/-- **The renormalised field**: the tensor mixing at `eI α`, `offF` elsewhere. DERIVED: no numeral. -/
def renR (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (μ : OffMix) (k : ℕ) (i : Ix0) :
    LField (MassGap.SUN.SU N) :=
  match dec i.1 with
  | some α => mixF ρ k α
  | none => offF μ bare k i

/-- **The family of all composites, renormalised off the tensor indices.** DERIVED: no numeral. -/
def buildRen (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (μ : OffMix) :
    Composites N where
  Ix := Ix0
  cl := Subtype.val
  bare := bare
  ren := renR ρ bare μ
  rep := repF

variable (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (μ : OffMix)

theorem renR_of_some {i : Ix0} {α : Idx4} (h : dec i.1 = some α) (k : ℕ) :
    renR ρ bare μ k i = mixF ρ k α := by
  simp only [renR, h]

theorem renR_of_none {i : Ix0} (h : dec i.1 = none) (k : ℕ) :
    renR ρ bare μ k i = offF μ bare k i := by
  simp only [renR, h]

end Family

/-! ## 2. The composites clauses -/

section Clauses

variable (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (μ : OffMix)

/-- `he1`. DERIVED: `0`–`3` the slots. -/
theorem buildRen_he1 (α : Idx4) :
    (buildRen ρ bare μ).cl (eI α) = [([([], α 0, α 1), ([], α 2, α 3)], true)] := rfl

/-- `he2`: the tensor components are the mixing, as for `build`. DERIVED: no numeral. -/
theorem buildRen_he2 (k : ℕ) (α : Idx4) :
    ((buildRen ρ bare μ).ren k (eI α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1 := by
  show (renR ρ bare μ k (eI α)).1 = _
  rw [renR_of_some ρ bare μ (dec_emono α)]
  rfl

/-- `hrep`. DERIVED: `1` the unit coefficient. -/
theorem buildRen_hrep (R : Matrix (Fin 4) (Fin 4) ℝ) (α : Idx4) :
    (buildRen ρ bare μ).rep R (eI α)
      = ∑ β : Idx4, ObserverNontrivial.tcoef R α β • Finsupp.single (eI β) (1 : ℝ) := by
  show repF R (eI α) = _
  simp only [repF, eI, dec_emono]

/-- `Tied` is `TiedB bare`. DERIVED: no numeral. -/
theorem buildRen_tied_iff : (buildRen ρ bare μ).Tied ↔ TiedB bare := Iff.rfl

/-- `Covers`. DERIVED: no numeral. -/
theorem buildRen_covers : (buildRen ρ bare μ).Covers := fun m h1 h2 => ⟨⟨m, h1, h2⟩, rfl⟩

/-- **`RepTie`** on `buildRen`: the proof of `build_repTie` (same `cl`, `rep`). DERIVED: no numeral. -/
theorem buildRen_repTie : (buildRen ρ bare μ).RepTie := by
  intro R _ i A hA g
  change Ix0 at i
  have hA' : ContDiff ℝ ∞ A := contDiff_infty.2 hA.1
  show cval g (rotPot R A) i.1 = ∑ j ∈ (repF R i).support, repF R i j * cval g A j.1
  rw [sum_support_eq_lc (repF R i) (fun j => cval g A j.1), cval_rotPot hA']
  cases h : dec i.1 with
  | some α =>
    have hi := eq_emono_of_dec h
    simp only [repF, h, map_sum, map_smul, Finsupp.linearCombination_single, smul_eq_mul]
    rw [hi, eval_rotM_emono]
    simp only [one_mul]
    rfl
  | none =>
    simp only [repF, h, repGen]
    rw [map_list_sum, List.map_map, FC.eval_eq_sum]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    have hs := rotM_shape i.2 hq
    simp only [Function.comp_apply, dif_pos hs, Finsupp.linearCombination_single, smul_eq_mul]

/-- The span of `1` and the renormalised fields of dimension `≤ n` at step `k`.
DERIVED: `1` the unit field. -/
def renSpan (k n : ℕ) : Submodule ℝ C(Cfg N, ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range fun i : {i : Ix0 // cdim i.1 ≤ n} => (renR ρ bare μ k i.1).1))

/-- **`RenTri`** from `RenTensor ρ bare`. The inverse direction is a strong induction on the
dimension: `bare i = sclR⁻¹ • ren k i + ∑_{lowJ} m k i j • bare j`, every `j` of strictly lower
dimension. DERIVED: `4` the dimension of `tr F F`; `1` the least colour count. -/
theorem buildRen_renTri (hN : 1 ≤ N) (h : RenTensor ρ bare) : (buildRen ρ bare μ).RenTri := by
  refine ⟨fun k i => ?_, fun k d => ?_⟩
  · show (renR ρ bare μ k i).1 ∈ bareSpan bare (cdim i.1)
    cases hd : dec i.1 with
    | some α =>
      rw [renR_of_some ρ bare μ hd, eI_of_dec hd]
      exact (h k α).1
    | none =>
      rw [renR_of_none ρ bare μ hd, offF_val]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨i, le_rfl⟩, rfl⟩))
        (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨j, (lowJ_spec hj).1.le⟩, rfl⟩))))
  · show bareSpan bare d ≤ renSpan ρ bare μ k d
    have hmono : ∀ {n n' : ℕ}, n ≤ n' → renSpan ρ bare μ k n ≤ renSpan ρ bare μ k n' :=
      fun hnn => Submodule.span_mono (Set.insert_subset_insert (by
        rintro _ ⟨⟨i, hi⟩, rfl⟩
        exact ⟨⟨i, hi.trans hnn⟩, rfl⟩))
    have hren : ∀ (n : ℕ) (i : Ix0), cdim i.1 ≤ n → (renR ρ bare μ k i).1 ∈ renSpan ρ bare μ k n :=
      fun n i hi => Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨i, hi⟩, rfl⟩)
    have h1 : ∀ n : ℕ, (1 : C(Cfg N, ℝ)) ∈ renSpan ρ bare μ k n :=
      fun n => Submodule.subset_span (Set.mem_insert _ _)
    have hoff : ∀ n : ℕ, (∀ m < n, ∀ i : Ix0, cdim i.1 ≤ m → (bare i).1 ∈ renSpan ρ bare μ k m) →
        ∀ i : Ix0, dec i.1 = none → cdim i.1 ≤ n → (bare i).1 ∈ renSpan ρ bare μ k n := by
      intro n IH i hd hi
      have hne : sclR N μ k i ≠ 0 := sclR_ne hN μ k i
      have e : (bare i).1 = (sclR N μ k i)⁻¹ • (renR ρ bare μ k i).1
          + ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1 := by
        rw [renR_of_none ρ bare μ hd, offF_val, inv_smul_smul₀ hne, sub_add_cancel]
      rw [e]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hren n i hi))
        (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
      have hj' := (lowJ_spec hj).1
      exact hmono (hj'.le.trans hi) (IH _ (lt_of_lt_of_le hj' hi) j le_rfl)
    have hall : ∀ (n : ℕ) (i : Ix0), cdim i.1 ≤ n → (bare i).1 ∈ renSpan ρ bare μ k n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n IH =>
        intro i hi
        cases hd : dec i.1 with
        | none => exact hoff n IH i hd hi
        | some α =>
          have h4 : 4 ≤ n := by rw [eq_emono_of_dec hd, cdim_emono] at hi; exact hi
          have hi' := eI_of_dec hd
          subst hi'
          refine (Submodule.span_le.2 ?_) (h k α).2
          rintro _ (rfl | ⟨β, rfl⟩ | ⟨⟨j, hj, hjd⟩, rfl⟩)
          · exact h1 n
          · have := hren n (eI β) (by rw [show (eI β).1 = emono β from rfl, cdim_emono]; exact h4)
            rwa [renR_of_some ρ bare μ (dec_emono β)] at this
          · exact hoff n IH j hjd (hj.trans h4)
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | ⟨⟨i, hi⟩, rfl⟩)
    · exact h1 d
    · exact hall d i hi

/-- **`CompData (buildRen ρ bare μ)`** from `TiedB bare` and `RenTensor ρ bare`, the hypotheses of
`build_compData`. DERIVED: `1` the least colour count. -/
theorem buildRen_compData (hN : 1 ≤ N) (hT : TiedB bare) (hR : RenTensor ρ bare) :
    CompData (buildRen ρ bare μ) :=
  ⟨hT, buildRen_covers ρ bare μ, buildRen_renTri ρ bare μ hN hR, buildRen_repTie ρ bare μ⟩

/-- **Uniform locality**: `offF` is local on the supports of `bare i` and of the `bare j`, `j ∈ J i`,
for every `k`; the tensor components as in `JointRP.build_unifLocal`. DERIVED: no numeral. -/
theorem unifLocal_buildRen : JointRP.UnifLocal (buildRen ρ bare μ) := by
  classical
  intro i
  choose S hS using fun j : Ix0 => (bare j).2.1
  cases h : dec i.1 with
  | none =>
    refine ⟨S i ∪ (μ.J i).biUnion S, fun k => ?_⟩
    rw [show (buildRen ρ bare μ).ren k i = offF μ bare k i from renR_of_none ρ bare μ h k]
    intro U V hUV
    rw [offF_val]
    simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, smul_eq_mul]
    rw [hS i U V fun l hl => hUV l (Finset.mem_union_left _ hl)]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hS j U V fun l hl => hUV l (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨j, lowJ_subset μ i hj, hl⟩))]
  | some α =>
    choose S' hS' using fun b => (ρ.op b).2.1
    refine ⟨Finset.univ.biUnion S', fun k => ?_⟩
    rw [show (buildRen ρ bare μ).ren k i = mixF ρ k α from renR_of_some ρ bare μ h k]
    intro U V hUV
    show (∑ b, ρ.M k α b • (ρ.op b).1) U = (∑ b, ρ.M k α b • (ρ.op b).1) V
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hS' b U V fun l hl => hUV l (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hl⟩)]

/-- **Lattice reflection covariance at the plane `0`** from the covariance of the bare fields and of
the tensor mixing components. The subtraction admits only fields of the same parity (`lowJ`).
DERIVED: `0` the plane and the reflection constant; `−1` the sign. -/
theorem reflCovLat_buildRen
    (hb : ∀ j : Ix0, LatticeReflection.ireflObs 0 0 (bare j).1
      = ((-1 : ℝ) ^ ctau 0 j.1) • (bare j).1)
    (ht : ∀ k α, LatticeReflection.ireflObs 0 0 (mixF ρ k α).1
      = ((-1 : ℝ) ^ ctau 0 (emono α)) • (mixF ρ k α).1) :
    JointRP.ReflCovLat (buildRen ρ bare μ) 0 := by
  intro k i
  show LatticeReflection.ireflObs 0 0 (renR ρ bare μ k i).1
    = ((-1 : ℝ) ^ ctau 0 i.1) • (renR ρ bare μ k i).1
  cases hd : dec i.1 with
  | some α =>
    have hi : i = eI α := eI_of_dec hd
    subst hi
    rw [renR_of_some ρ bare μ hd]
    exact ht k α
  | none =>
    rw [renR_of_none ρ bare μ hd, offF_val]
    simp only [map_smul, map_sub, map_sum, hb]
    have hs : ∑ j ∈ lowJ μ i, μ.m k i j • (((-1 : ℝ) ^ ctau 0 j.1) • (bare j).1)
        = ((-1 : ℝ) ^ ctau 0 i.1) • ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1 := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(lowJ_spec hj).2, smul_comm]
    rw [hs, ← smul_sub]
    exact smul_comm _ _ _

end Clauses

/-! ## 3. The off-tensor readings -/

section Readings

variable (ρ : RenormMix N) (bare : Ix0 → LField (MassGap.SUN.SU N)) (μ : OffMix)

/-- **The off-tensor readings carry the renormalisation factors**: on a family of off-tensor indices,
`latC (buildRen …) k F = (∏ₓ sclR N μ k (F x).1) · latSk k ((subF − ν_k(subF)), f)`.
DERIVED: `0` the excluded colour count. -/
theorem latC_off (hN : N ≠ 0) {ι : Type} [Fintype ι] (F : ι → Ix0 × TestFn)
    (hF : ∀ x, dec (F x).1.1 = none) (k : ℕ) :
    latC hN (buildRen ρ bare μ) k F
      = (∏ x, sclR N μ k (F x).1) * latSk hN k (fun x =>
          ((subF μ bare k (F x).1).sub (stateK hN k (subF μ bare k (F x).1).1), (F x).2)) := by
  unfold latC
  rw [latSk_eq, latSk_eq]
  refine JointRP.latS_scale (stateK hN k) (dySpacing N k) _ _ (fun x => sclR N μ k (F x).1)
    fun x => ?_
  have hr : ((buildRen ρ bare μ).ren k (F x).1).1 = sclR N μ k (F x).1 • (subF μ bare k (F x).1).1 := by
    show (renR ρ bare μ k (F x).1).1 = _
    rw [renR_of_none ρ bare μ (hF x)]
    rfl
  show smear (dySpacing N k) (((buildRen ρ bare μ).ren k (F x).1).1
      - stateK hN k ((buildRen ρ bare μ).ren k (F x).1).1 • (1 : C(Cfg N, ℝ))) (F x).2
    = sclR N μ k (F x).1 • smear (dySpacing N k) ((subF μ bare k (F x).1).1
      - stateK hN k (subF μ bare k (F x).1).1 • (1 : C(Cfg N, ℝ))) (F x).2
  rw [hr, MassGap.DLRLimit.State.map_smul, ← smul_smul, ← smul_sub,
    ContinuumFlow.smear_smul (dySpacing_pos (one_le_of_ne_zero hN) k)]

/-- With no mixing at `i`, `subF μ bare k i = bare i`. DERIVED: no numeral. -/
theorem subF_of_empty {i : Ix0} (h : μ.J i = ∅) (k : ℕ) : subF μ bare k i = bare i := by
  have hl : lowJ μ i = ∅ := Finset.subset_empty.1 (by rw [← h]; exact lowJ_subset μ i)
  exact Subtype.ext (by
    show (bare i).1 - ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1 = (bare i).1
    rw [hl, Finset.sum_empty, sub_zero])

/-- **With no mixing, the renormalised reading is the bare reading times the factors**:
`latC (buildRen …) k F = (∏ₓ sclR N μ k (F x).1) · latC (build ρ bare) k F` on off-tensor indices
with `J = ∅`. DERIVED: `0` the excluded colour count. -/
theorem latC_noMix (hN : N ≠ 0) {ι : Type} [Fintype ι] (F : ι → Ix0 × TestFn)
    (hF : ∀ x, dec (F x).1.1 = none) (hJ : ∀ x, μ.J (F x).1 = ∅) (k : ℕ) :
    latC hN (buildRen ρ bare μ) k F = (∏ x, sclR N μ k (F x).1) * latC hN (build ρ bare) k F := by
  rw [latC_off ρ bare μ hN F hF k]
  congr 1
  unfold latC
  congr 1
  funext x
  rw [subF_of_empty bare μ (hJ x) k]
  show _ = ((renF ρ bare k (F x).1).sub (stateK hN k (renF ρ bare k (F x).1).1), (F x).2)
  rw [renF_of_none ρ bare (hF x)]

/-- **The two-point reading with no mixing**:
`latC (buildRen …) k ![(i,f),(j,h)] = sclR i · sclR j · latC (build ρ bare) k ![(i,f),(j,h)]`,
`sclR i · sclR j = e^{lz k i + lz k j} / a_k^{cdim i + cdim j}`.
DERIVED: `2` the two points; `0`, `1` their slots. -/
theorem latC_two_noMix (hN : N ≠ 0) {i j : Ix0} (hi : dec i.1 = none) (hj : dec j.1 = none)
    (hJi : μ.J i = ∅) (hJj : μ.J j = ∅) (f h : TestFn) (k : ℕ) :
    latC hN (buildRen ρ bare μ) k (![(i, f), (j, h)] : Fin 2 → Ix0 × TestFn)
      = sclR N μ k i * sclR N μ k j
        * latC hN (build ρ bare) k (![(i, f), (j, h)] : Fin 2 → Ix0 × TestFn) := by
  rw [latC_noMix ρ bare μ hN _ (fun x => by fin_cases x; exacts [hi, hj])
    (fun x => by fin_cases x; exacts [hJi, hJj]) k, Fin.prod_univ_two]
  rfl

/-- The product of the two factors. DERIVED: no numeral. -/
theorem sclR_mul (μ : OffMix) (k : ℕ) (i j : Ix0) :
    sclR N μ k i * sclR N μ k j
      = Real.exp (μ.lz k i + μ.lz k j) / dySpacing N k ^ (cdim i.1 + cdim j.1) := by
  rw [sclR, sclR, Real.exp_add, pow_add, div_mul_div_comm]

/-- **The two-point continuum reading with no mixing** is the `ultra` limit of the rescaled reading of
`build ρ bare`. DERIVED: `2` the two points. -/
theorem contC_two_noMix (hN : N ≠ 0) {i j : Ix0} (hi : dec i.1 = none) (hj : dec j.1 = none)
    (hJi : μ.J i = ∅) (hJj : μ.J j = ∅) (f h : TestFn) :
    contC hN (buildRen ρ bare μ) (![(i, f), (j, h)] : Fin 2 → Ix0 × TestFn)
      = limUnder (ultra : Filter ℕ) (fun k => sclR N μ k i * sclR N μ k j
          * latC hN (build ρ bare) k (![(i, f), (j, h)] : Fin 2 → Ix0 × TestFn)) := by
  unfold contC
  congr 1
  funext k
  exact latC_two_noMix ρ bare μ hN hi hj hJi hJj f h k

/-- **The renormalised field vanishes exactly when `bare i` is its lower-dimension combination.**
DERIVED: `0` the zero field; `1` the least colour count. -/
theorem offF_eq_zero_iff (hN : 1 ≤ N) (k : ℕ) (i : Ix0) :
    (offF μ bare k i).1 = 0 ↔ (bare i).1 = ∑ j ∈ lowJ μ i, μ.m k i j • (bare j).1 := by
  rw [offF_val, smul_eq_zero, or_iff_right (sclR_ne hN μ k i), sub_eq_zero]

end Readings

/-! ## 4. The reflection-positivity chain at any uniformly local, reflection-covariant composites -/

section Chain

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.ObsLead MassGap.ClayData
  MassGap.CompositeLink MassGap.JointRP MassGap.ReflAvg MassGap.MixConvRP

/-- `CompositeLink.mixKC` at composites `Cs`, plane `0`. DERIVED: `0` the plane. -/
abbrev mixKG (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N) (r : ℝ)
    (P : TSepG Cs.Ix 0) (Q : MarginMono N 0 r) : ℝ :=
  mixKC (ne_zero_of_two_le hN2) Cs (Φ0 W) 0 P Q.1

/-- `ReflAvg.MixConvF` at composites `Cs`. DERIVED: `0` the plane. -/
def MixConvG (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N) (r : ℝ) : Prop :=
  ∀ (P : TSepG Cs.Ix 0) (Q : MarginMono N 0 r),
    ∃ x, Tendsto (fun k => mixLatC (ne_zero_of_two_le hN2) Cs (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 x)

/-- `ReflAvg.ReflLimF` at composites `Cs`. DERIVED: `0` the plane. -/
def ReflLimG (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N) (r : ℝ) : Prop :=
  (∀ P P' : TSepG Cs.Ix 0,
    Tendsto (fun k => rReadC (ne_zero_of_two_le hN2) Cs 0 k P.1 P'.1)
      (ultra : Filter ℕ) (𝓝 (kernC (ne_zero_of_two_le hN2) Cs 0 P P')))
  ∧ ∀ (P : TSepG Cs.Ix 0) (Q : MarginMono N 0 r),
    Tendsto (fun k => rMixC (ne_zero_of_two_le hN2) Cs (Φ0 W) 0 k P.1 Q.1)
      (ultra : Filter ℕ) (𝓝 (mixKG hN2 W Cs r P Q))

/-- **`MixConvG` from lattice covariance, uniform locality, `CompOS` and the observer's bound**:
`MixConvRP.mixConvF_of_cov` with `UnifLocal Cs` in place of `build_unifLocal`.
DERIVED: `0` the plane; `1` the unit bound margin. -/
theorem mixConvG_of_cov (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (Cs : Composites N) (hUL : UnifLocal Cs)
    (hcov : ReflCovLat Cs 0) (hCO : CompOS (ne_zero_of_two_le hN2) Cs) :
    MixConvG hN2 W Cs r := by
  intro P Q
  have hN := ne_zero_of_two_le hN2
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  have hL := hCO.1 _ _ (adm_pairC Cs P P)
  set x := contC hN Cs (pairC Cs 0 P.1 P.1)
  have hLb : ∀ᶠ k in (ultra : Filter ℕ), |latC hN Cs k (pairC Cs 0 P.1 P.1)| ≤ |x| + 1 := by
    have hball := hL.eventually (Metric.ball_mem_nhds x one_pos)
    filter_upwards [hball] with k hk
    rw [Real.dist_eq] at hk
    calc |latC hN Cs k (pairC Cs 0 P.1 P.1)|
        = |(latC hN Cs k (pairC Cs 0 P.1 P.1) - x) + x| := by rw [sub_add_cancel]
      _ ≤ |latC hN Cs k (pairC Cs 0 P.1 P.1) - x| + |x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  obtain ⟨D, hD⟩ := ClaySUGap.uB hN W hU (Fin Q.1.1 ⊕ Fin Q.1.1) (pairFam 0 Q.1 Q.1)
  have hDb : ∀ᶠ k in atTop, |latSF hN (Φ0 W) k (pairFam 0 Q.1 Q.1)| ≤ D := by
    have h0 := hD 0 (fun _ => 0)
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
    exact h0
  have hev : ∀ᶠ k in atTop,
      prodSmear (dySpacing N k) (cMono hN Cs k P.1)
          ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
        ∧ prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
          ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
        ∧ |latSF hN (Φ0 W) k (pairFam 0 Q.1 Q.1)| ≤ D :=
    (eventually_cMono_mem hN Cs hUL P).and ((eventually_flow_mem (Φ0 W) hpos Q).and hDb)
  refine exists_tendsto_ultra_of_ultra _ (Real.sqrt ((|x| + 1) * D)) ?_
  filter_upwards [hev.filter_mono ultra_le, hLb] with k hk hLk
  obtain ⟨hPk, hQk, hDk⟩ := hk
  refine Real.abs_le_sqrt ?_
  have hsq := mixLatC_sq_le hN Cs (Φ0 W) 0 hcov k P.1 Q.1 hPk hQk
  exact hsq.trans (mul_le_mul hLk hDk (abs_nonneg _) (by positivity))

/-- `ReflAvg.reflLim_of_covF` at composites `Cs`. DERIVED: `0` the plane. -/
theorem reflLimG_of_cov (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N) (r : ℝ)
    (hcov : ReflCovLat Cs 0) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hMC : MixConvG hN2 W Cs r) : ReflLimG hN2 W Cs r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine ⟨fun P P' => ?_, fun P Q => ?_⟩
  · have h := (hCO.1 _ _ (adm_pairC Cs P P')).const_mul (sgnC Cs 0 P.1)
    refine h.congr fun k => ?_
    exact (rReadC_of_cov _ _ 0 hcov k P.1 P'.1).symm
  · obtain ⟨x, hx⟩ := hMC P Q
    have h := hx.const_mul (sgnC Cs 0 P.1)
    have hlim : mixKG hN2 W Cs r P Q = sgnC Cs 0 P.1 * x := by
      show sgnC Cs 0 P.1 * limUnder (ultra : Filter ℕ) _ = _
      rw [hx.limUnder_eq]
    rw [hlim]
    refine h.congr fun k => ?_
    exact (rMixC_of_cov _ _ _ 0 hcov k P.1 Q.1).symm

/-- `ReflAvg.jointRPK_of_reflLimF` at uniformly local composites `Cs`. DERIVED: `0` the plane. -/
theorem jointRPKG_of_reflLim (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (Cs : Composites N) (hUL : UnifLocal Cs)
    (hRL : ReflLimG hN2 W Cs r) :
    JointRPK (kernC (ne_zero_of_two_le hN2) Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r) := by
  have hN := ne_zero_of_two_le hN2
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  refine jointRPK_of_tendsto
    (fun k P P' => rReadC hN Cs 0 k P.1 P'.1)
    (fun k P Q => rMixC hN Cs (Φ0 W) 0 k P.1 Q.1)
    (fun k Q Q' => latSF hN (Φ0 W) k (pairFam 0 Q.1 Q'.1))
    hRL.1 hRL.2
    (fun Q Q' => tendsto_contSF hN (Φ0 W) (ClaySUGap.uB hN W hU) (pairFam 0 Q.1 Q'.1))
    fun P P' s c => ?_
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ c.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset c.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  filter_upwards [eventually_cMono_mem hN Cs hUL P, eventually_cMono_mem hN Cs hUL P', hQ]
    with k hP hP' hQk
  exact latJointC hN Cs (Φ0 W) 0 k (fun Q : MarginMono N 0 r => Q.1) P.1 P'.1 s c hP hP' hQk

/-- `ReflAvg.linkCPre_of_kernelsF` at composites `Cs` with a tensor index map `e` satisfying the first
two clauses of `TIn` for the mixing `ρ`. DERIVED: `0` the plane; `0`–`3` the four indices of an
`Idx4 = Fin 4 → Fin 4` read by the plaquette pair. -/
theorem linkCPreG_of_kernels (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (ρ : RenormMix N) (Cs : Composites N) (e : Idx4 → Cs.Ix)
    (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r))
    (hMC : MixConvG hN2 W Cs r) :
    ∃ wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys,
      LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
        (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC
      ∧ ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
        Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ (Φ0 W) 0 k P.1 Q.1.1)
            (ultra : Filter ℕ) (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (Φ0 W) 0 P.1 Q.1.1))
          ∧ inner ℂ (LinkReduce.wOfC e wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
            = (mixT (ne_zero_of_two_le hN2) ρ (Φ0 W) 0 P.1 Q.1.1 : ℂ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨hG1, hG2, hG3⟩ := obsGen_flow (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)
  have hG : ∀ Q Q' : MarginMono N 0 r, inner ℂ (vO hN2 W hU hphys Q) (vO hN2 W hU hphys Q')
      = (gramF hN2 W r Q Q' : ℂ) := hG1
  have hG2' : ∀ (m : ℕ) (Q : MarginMono N 0 r),
      vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)
        = preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (vO hN2 W hU hphys Q) :=
    fun m Q => hG2 m Q _ rfl
  obtain ⟨w, hwX, hwK⟩ := exists_link (gramF hN2 W r) hG ((jointRP_iff_K _ hG).mpr hJ)
    ((approx_iff_K _ hG).mpr hA)
  refine ⟨w, ⟨fun P Q => ⟨hCO.1 _ _ (adm_pairC Cs P Q), hwK P Q⟩, fun m P => ?_, ?_⟩,
    fun P Q => ?_⟩
  · refine eq_of_inner_eq hG3 fun Q => ?_
    calc inner ℂ (w (shiftT (ne_zero_of_two_le hN2) 0 m P)) (vO hN2 W hU hphys Q)
        = (mixKG hN2 W Cs r P (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q) : ℂ) := by
          rw [hwX]
          exact congrArg Complex.ofReal (mixKC_shift _ _ _ 0 m P Q.1)
      _ = inner ℂ (w P) (vO hN2 W hU hphys (MarginMono.shift (ne_zero_of_two_le hN2) 0 m Q)) :=
          (hwX _ _).symm
      _ = inner ℂ (w P) (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m)
            (vO hN2 W hU hphys Q)) := by
          rw [hG2' m Q]
      _ = inner ℂ (preTime (ne_zero_of_two_le hN2) W hU hphys (dySpacing N m) (w P))
            (vO hN2 W hU hphys Q) :=
          ((isSelfAdjoint_powT (a := stepT (ne_zero_of_two_le hN2) (Φ0 W)
            (preB (ne_zero_of_two_le hN2) W hU) 0
            (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0) 0)
            (dySpacing N m / dySpacing N 0)).isSymmetric (w P) (vO hN2 W hU hphys Q)).symm
  · have hvac : preVac (ne_zero_of_two_le hN2) W hU hphys
        = vO hN2 W hU hphys (emptyMargin N 0 r) := rfl
    refine eq_of_inner_eq hG3 fun Q => ?_
    rw [hvac, hG, hwX]
    exact congrArg Complex.ofReal (mixKC_empty _ _ _ 0 r Q.1)
  · have hT := tendsto_mixLatT (ne_zero_of_two_le hN2) ρ Cs e he1 he2 (Φ0 W) 0 P Q.1.1
      (fun α => hMC (LinkReduce.monoAt e P α) Q.1)
    have hmix : mixT (ne_zero_of_two_le hN2) ρ (Φ0 W) 0 P.1 Q.1.1
        = ∑ α : Fin P.1.1 → Idx4, LinkReduce.coefAt P α
            * mixKC (ne_zero_of_two_le hN2) Cs (Φ0 W) 0
              (LinkReduce.monoAt e P α) Q.1.1 :=
      hT.limUnder_eq
    refine ⟨by rw [hmix]; exact hT, ?_⟩
    rw [hmix]
    unfold LinkReduce.wOfC
    rw [sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_smul_left, Complex.conj_ofReal, Complex.ofReal_mul]
    exact congrArg (fun x => ((LinkReduce.coefAt P α : ℝ) : ℂ) * x) (hwX _ Q.1)

end Chain

/-! ## 5. The reflection-averaged instance and the capstone -/

section Capstone

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.ObsLead MassGap.ClayData
  MassGap.CompositeLink MassGap.JointRP MassGap.ReflAvg MassGap.MixConvRP

/-- **The bare tensor field at the averaged fields is reflection covariant**:
`θ (bareT (fR N) α) = s_α bareT (fR N) α`. DERIVED: no numeral. -/
theorem refl_bareT (α : Idx4) :
    LatticeReflection.ireflObs 0 0 (bareT (fR N) α).1 = sθ α • (bareT (fR N) α).1 := by
  rw [bareT_val, map_add, map_smul, obs_refl, map_sum, smul_add, smul_smul, Finset.smul_sum]
  congr 1
  · congr 1
    calc wD N * tv α = wD N * (sθ α * tv α) := by rw [tv_parity]
      _ = sθ α * (wD N * tv α) := by ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c = .sc
    · simp [hc]
    · simp only [hc, if_false]
      exact refl_Fv (fR N) fR_refl c α

/-- **The averaged bare fields are reflection covariant**: off the tensor indices by `reflAvg_refl`, at
`eI β` by `refl_bareT`. DERIVED: `0` the plane; `−1` the sign. -/
theorem bareD_R_refl (j : Ix0) :
    LatticeReflection.ireflObs 0 0 (bareD (fR N) (bR N) j).1
      = ((-1 : ℝ) ^ ctau 0 j.1) • (bareD (fR N) (bR N) j).1 := by
  cases hd : dec j.1 with
  | none =>
    have e : bareD (fR N) (bR N) j = bareR j.1 := by
      show (match dec j.1 with | some α => bareT (fR N) α | none => bR N j) = _
      rw [hd]
    rw [e]
    exact reflAvg_refl _ _
  | some β =>
    have hj : j = eI β := eI_of_dec hd
    subst hj
    rw [bareD_eI, show (eI β).1 = emono β from rfl, sign_emono]
    exact refl_bareT β

/-- **The renormalised averaged composites** `buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ`.
DERIVED: no numeral. -/
abbrev CRen (N : ℕ) (z : Chan → ℕ → ℝ) (μ : OffMix) : Composites N :=
  buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ

/-- **The renormalised averaged composites are reflection covariant on the lattice** at every step.
DERIVED: `0` the plane. -/
theorem reflCovLat_CRen (z : Chan → ℕ → ℝ) (μ : OffMix) : ReflCovLat (CRen N z μ) 0 :=
  reflCovLat_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ bareD_R_refl fun k α => by
    rw [mixF_rhoD, sign_emono]
    exact refl_Ecomb (fR N) fR_u1 fR_refl _ α

/-- **The SU capstone at the renormalised reflection-averaged composites.** The tensor fields are
`fR N`, the bare fields `bareD (fR N) (bR N)`, the composites `CRen N z μ`: tensor components the mixing
of `rhoD (fR N) z`, off-tensor components `e^{lz k i} a_k^{−cdim i} (bare i − ∑_{lowJ} m k i j bare j)`.
Discharged: `CompData` (`buildRen_compData` with `tiedB_R`, `renTensor_D`), `MixConvG`
(`mixConvG_of_cov` with `unifLocal_buildRen`, `reflCovLat_CRen`), `JointRPK` (`jointRPKG_of_reflLim`,
`reflLimG_of_cov`), the composites' vectors with `LinkCPre` and the cross reading
(`linkCPreG_of_kernels`), `NonGaussianT` from `hObs`, `hRie` from `coefRiemann_mD`, `hTie` from `hzS` (`scalarTie_D`), `hCT` from `hzP` (`channelTie_D`).

The inputs: `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hObs`,
`hWard` (as in `MixConvRP.clayStatementAt_SU_reflAvg'`), the free renormalisation inputs `μ`, and
`hCO`, `hA` read at `CRen N z μ`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_ren (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (μ : OffMix)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CRen N z μ))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hN := ne_zero_of_two_le hN2
  have hUL := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  obtain ⟨wC, hLC, hX⟩ := linkCPreG_of_kernels hN2 W hU hphys (rhoD (fR N) z) (CRen N z μ) eI
    (fun α => buildRen_he1 _ _ μ α) (fun k α => buildRen_he2 _ _ μ k α) hCO
    (jointRPKG_of_reflLim hN2 W hU hphys (CRen N z μ) hUL
      (reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC)) hA hMC
  exact ClaySUFinal.clayStatementAt_SU_final hN2 W ht hU hphys hfar (rhoD (fR N) z)
    (riemann_mixOfZ (opD (fR N)) (mD N) (ZD z) (coefRiemann_mD N))
    (scalarTie_D hN (fR N) z hzS).2
    (channelTie_D (fR N) (bR N) z hzP (tiedB_R hN)) G hK hAF
    (NonGaussLink.nonGaussianT_rhoD_of_obs hN (fR N) z hObs) hWard
    (CRen N z μ) wC eI (fun α => buildRen_he1 _ _ μ α) (fun k α => buildRen_he2 _ _ μ k α)
    (buildRen_compData _ _ μ (by omega) (tiedB_R hN) (renTensor_D hN (fR N) (bR N) z hz)) hCO
    (fun R _ α => buildRen_hrep _ _ μ R α) hLC hX

end Capstone

end MassGap.CompositesRen

end

#print axioms MassGap.CompositesRen.buildRen_he2
#print axioms MassGap.CompositesRen.buildRen_hrep
#print axioms MassGap.CompositesRen.buildRen_covers
#print axioms MassGap.CompositesRen.buildRen_repTie
#print axioms MassGap.CompositesRen.buildRen_renTri
#print axioms MassGap.CompositesRen.buildRen_compData
#print axioms MassGap.CompositesRen.unifLocal_buildRen
#print axioms MassGap.CompositesRen.reflCovLat_buildRen
#print axioms MassGap.CompositesRen.latC_off
#print axioms MassGap.CompositesRen.latC_noMix
#print axioms MassGap.CompositesRen.latC_two_noMix
#print axioms MassGap.CompositesRen.sclR_mul
#print axioms MassGap.CompositesRen.contC_two_noMix
#print axioms MassGap.CompositesRen.offF_eq_zero_iff
#print axioms MassGap.CompositesRen.mixConvG_of_cov
#print axioms MassGap.CompositesRen.reflLimG_of_cov
#print axioms MassGap.CompositesRen.jointRPKG_of_reflLim
#print axioms MassGap.CompositesRen.linkCPreG_of_kernels
#print axioms MassGap.CompositesRen.refl_bareT
#print axioms MassGap.CompositesRen.bareD_R_refl
#print axioms MassGap.CompositesRen.reflCovLat_CRen
#print axioms MassGap.CompositesRen.clayStatementAt_SU_ren
