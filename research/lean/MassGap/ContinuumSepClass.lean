import Mathlib
import MassGap.ClayReduce

noncomputable section

/-!
# MassGap.ContinuumSepClass — the reconstruction on a class of test functions

`ContinuumSep` reconstructs the continuum transfer data from the separated positive-time monomials with
bounded test functions of compact support, `SepMono N τ`, and needs E (`PairBoundSepAlong`) on all of
them. The Wightman and Osterwalder–Schrader axioms smear fields with smooth test functions only. This
module runs the same reconstruction on the monomials whose test functions lie in a class `𝒯` closed
under translation (`TestClass`), with E asked only there.

* `ClassMono N τ 𝒯`: the separated positive-time monomials whose test functions lie in `𝒯`, a subtype of
  `SepMono N τ`; `ClassMono.shift` the dyadic time step (the class is closed under it).
* `PairBoundClassAlong`, `DiagBoundClassAlong`: E on reflected pairs and on the reflection diagonal of
  class monomials; `pairBoundClass_of_diagBoundClass`.
* `formClassAlong`: the form `ContinuumSep.formSepAlong` read through the embedding
  `embClass : AmodClass →ₗ AmodSep`; `TmClass` the time step. Under `PairBoundClassAlong`:
  `contTransferClassAlong`, a `Transfer.TransferData` on `AmodClass N τ 𝒯`.
* `continuum_gap_class_of_towerGapAt`: the gap at every dyadic step from the tower gap, as
  `ContinuumSep.continuum_gap_sep_of_towerGapAt`.
* `ClayContinuumPairClassAlong`, `clay_class_of_diagBound_towerGapAt`: the Clay continuum conclusion
  (gap and a non-trivial vacuum) on the class, from E on the class, the tower gap and a class monomial
  with reflected reading bounded below (`PairLowerBoundClassAlong`).
* `TestClass.all`: every test function; `classMonoAllEquiv`: at it `ClassMono` is in bijection with
  `SepMono`.

DERIVED (module-wide): `0` the excluded colour count, the reflection plane, the empty monomial and the
lower end of a margin; `1` the vacuum coefficient and the half step; `2` the square and the doubling; `4`
the spacetime dimension.
-/

namespace MassGap.ContinuumSepClass

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumSep Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Classes and monomials -/

/-- **A class of test functions closed under translation.** -/
structure TestClass where
  /-- Membership. -/
  mem : TestFn → Prop
  /-- Translates of members are members. -/
  translate_mem : ∀ (f : TestFn) (v : Fin 4 → ℝ), mem f → mem (f.translate v)

/-- Every test function. -/
def TestClass.all : TestClass := ⟨fun _ => True, fun _ _ _ => trivial⟩

/-- **Separated positive-time monomials with every test function in the class.** -/
abbrev ClassMono (N : ℕ) (τ : Fin 4) (𝒯 : TestClass) : Type :=
  {P : SepMono N τ // ∀ i, 𝒯.mem (P.1.2 i).2}

/-- **At the class of all test functions, class monomials are the separated monomials.** -/
def classMonoAllEquiv (N : ℕ) (τ : Fin 4) : ClassMono N τ TestClass.all ≃ SepMono N τ where
  toFun P := P.1
  invFun P := ⟨P, fun _ => trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dyadic time step on class monomials. -/
def ClassMono.shift {𝒯 : TestClass} (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : ClassMono N τ 𝒯) :
    ClassMono N τ 𝒯 :=
  ⟨SepMono.shift hN τ m P.1, fun i => 𝒯.translate_mem _ _ (P.2 i)⟩

theorem ClassMono.shift_iterate_val {𝒯 : TestClass} (hN : N ≠ 0) (τ : Fin 4) (m n : ℕ)
    (P : ClassMono N τ 𝒯) : ((ClassMono.shift hN τ m)^[n] P).1 = (SepMono.shift hN τ m)^[n] P.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem ClassMono.shift_half {𝒯 : TestClass} (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : ClassMono N τ 𝒯) :
    ClassMono.shift hN τ (m + 1) (ClassMono.shift hN τ (m + 1) P) = ClassMono.shift hN τ m P :=
  Subtype.ext (SepMono.shift_half hN τ m P.1)

/-- The empty class monomial. -/
def emptyClass (N : ℕ) (τ : Fin 4) (𝒯 : TestClass) : ClassMono N τ 𝒯 :=
  ⟨emptySep N τ, fun i => i.elim0⟩

theorem shift_emptyClass {𝒯 : TestClass} (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) :
    ClassMono.shift hN τ m (emptyClass N τ 𝒯) = emptyClass N τ 𝒯 :=
  Subtype.ext (shift_emptySep hN τ m)

/-! ## 2. E on class monomials -/

section Pairs

variable (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) (τ : Fin 4) (𝒯 : TestClass)

/-- **E on reflected pairs of class monomials**, at every common dyadic time shift. -/
def PairBoundClassAlong : Prop :=
  ∀ P Q : ClassMono N τ 𝒯, ∃ C : ℝ, ∀ m n : ℕ, ∀ᶠ k in atTop,
    |latSkRAlong hN βs ρ k (pairFam τ ((ClassMono.shift hN τ m)^[n] P).1.1
      ((ClassMono.shift hN τ m)^[n] Q).1.1)| ≤ C

/-- **E on the reflection diagonal of class monomials.** -/
def DiagBoundClassAlong : Prop :=
  ∀ P : ClassMono N τ 𝒯, ∃ C : ℝ, ∀ᶠ k in atTop, latSkRAlong hN βs ρ k (pairFam τ P.1.1 P.1.1) ≤ C

/-- **The diagonal bound gives the pair bound**, as `ContinuumSep.pairBoundSep_of_diagBoundSep_along`. -/
theorem pairBoundClass_of_diagBoundClass (hR : ρ.ReflCompat τ) (hD : DiagBoundClassAlong hN βs ρ τ 𝒯) :
    PairBoundClassAlong hN βs ρ τ 𝒯 := by
  intro P Q
  obtain ⟨CP, hCP⟩ := hD P
  obtain ⟨CQ, hCQ⟩ := hD Q
  refine ⟨Real.sqrt (CP * CQ), fun m n => ?_⟩
  rw [ClassMono.shift_iterate_val, ClassMono.shift_iterate_val]
  filter_upwards [Filter.eventually_ge_atTop m, hCP, hCQ, eventually_Yv_mem_sep hN ρ τ P.1,
    eventually_Yv_mem_sep hN ρ τ Q.1,
    eventually_Yv_mem_sep hN ρ τ ((SepMono.shift hN τ m)^[n] P.1),
    eventually_Yv_mem_sep hN ρ τ ((SepMono.shift hN τ m)^[n] Q.1)]
    with k hk hkP hkQ hYP hYQ hYP' hYQ'
  have hcs := sq_latSkR_pairFam_le_along hN βs ρ τ hR k _ _ hYP' hYQ'
  have h0P := latSkR_pairFam_self_nonneg_along hN βs ρ τ hR k _ hYP'
  have h0Q := latSkR_pairFam_self_nonneg_along hN βs ρ τ hR k _ hYQ'
  have hPP := (latSkR_iterate_self_le_along hN βs ρ τ hR hk n P.1 hYP).trans hkP
  have hQQ := (latSkR_iterate_self_le_along hN βs ρ τ hR hk n Q.1 hYQ).trans hkQ
  exact Real.abs_le_sqrt (hcs.trans (mul_le_mul hPP hQQ h0Q (h0P.trans hPP)))

variable {hN βs ρ τ 𝒯}

/-- **Existence of the limit on every reflected pair of class monomials.** -/
theorem tendsto_class (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (P Q : ClassMono N τ 𝒯) :
    Tendsto (fun k => latSkRAlong hN βs ρ k (pairFam τ P.1.1 Q.1.1)) (ultra : Filter ℕ)
      (𝓝 (kernAlong hN βs ρ τ P.1.1 Q.1.1)) := by
  obtain ⟨C, hC⟩ := hB P Q
  have h0 : ∀ᶠ k in atTop, |latSkRAlong hN βs ρ k (pairFam τ P.1.1 Q.1.1)| ≤ C := by
    have h := hC 0 0
    rwa [Function.iterate_zero_apply, Function.iterate_zero_apply] at h
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **OS0 along the shifts on class monomials.** -/
theorem kernClass_iterate_bound (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (m : ℕ) (P Q : ClassMono N τ 𝒯) :
    ∃ C : ℝ, ∀ n : ℕ, |kernAlong hN βs ρ τ ((ClassMono.shift hN τ m)^[n] P).1.1
      ((ClassMono.shift hN τ m)^[n] Q).1.1| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB P Q
  exact ⟨C, fun n => le_of_tendsto (tendsto_class hB _ _).abs ((hC m n).filter_mono ultra_le)⟩

/-- **OS2 on class monomials.** -/
theorem contS_gram_nonneg_class (hR : ρ.ReflCompat τ) (hB : PairBoundClassAlong hN βs ρ τ 𝒯)
    (s : Finset (ClassMono N τ 𝒯))
    (c : ClassMono N τ 𝒯 → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernAlong hN βs ρ τ P.1.1 Q.1.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have htend : Tendsto
      (fun k => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkRAlong hN βs ρ k (pairFam τ P.1.1 Q.1.1))
      (ultra : Filter ℕ) (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernAlong hN βs ρ τ P.1.1 Q.1.1)) :=
    tendsto_finsetSum _ (fun P _ => tendsto_finsetSum _
      (fun Q _ => (tendsto_class hB P Q).const_mul (c P * c Q)))
  refine ge_of_tendsto htend ?_
  have hmem : ∀ᶠ k in atTop, ∀ P ∈ s, ∀ i : Fin P.1.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.1.2 i).1.sub r).1 (P.1.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    (Filter.eventually_all_finset s).mpr (fun P _ =>
      Filter.eventually_all.mpr
        (fun i => eventually_smear_sub_mem (one_le_of_ne_zero hN) τ _ _ (sepMono_posTime P.1 i)))
  have hev : ∀ᶠ k in atTop,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkRAlong hN βs ρ k (pairFam τ P.1.1 Q.1.1) := by
    filter_upwards [hmem] with k hk
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hsum : ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSkRAlong hN βs ρ k (pairFam τ P.1.1 Q.1.1)
        = ∑ P ∈ s, ∑ Q ∈ s, (c P * ρ.zmono k P.1.1) * (c Q * ρ.zmono k Q.1.1) * stateAlong hN βs k
            (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (ρ.mono k P.1.1))
              * prodSmear (dySpacing N k) (ρ.mono k Q.1.1)) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
      rw [latSkRAlong_pairFam hN βs ρ τ hR, latSkAlong, latS_pairFam _ ha]
      ring
    have hX : (∑ P ∈ s, (c P * ρ.zmono k P.1.1) • prodSmear (dySpacing N k) (ρ.mono k P.1.1))
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
      Submodule.sum_mem _ (fun P hP => Submodule.smul_mem _ _
        (HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
          (fun i _ => hk P hP i (ρ.c k (P.1.1.2 i).1))))
    rw [hsum]
    exact le_of_le_of_eq (stateAlong_rp hN βs k τ _ hX)
      (gram_expand (stateAlong hN βs k) (LatticeReflection.ireflObs τ 0) s
        (fun P => c P * ρ.zmono k P.1.1) (fun P => prodSmear (dySpacing N k) (ρ.mono k P.1.1)))
  exact hev.filter_mono ultra_le

end Pairs

/-! ## 3. The form and the transfer data -/

section Form

variable (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) (τ : Fin 4) (𝒯 : TestClass)

/-- Finite real combinations of class monomials. -/
abbrev AmodClass (N : ℕ) (τ : Fin 4) (𝒯 : TestClass) : Type := ClassMono N τ 𝒯 →₀ ℝ

/-- **The embedding into the combinations of separated monomials.** -/
def embClass : AmodClass N τ 𝒯 →ₗ[ℝ] AmodSep N τ := Finsupp.lmapDomain ℝ ℝ Subtype.val

/-- **The reflection form on class monomials**: `ContinuumSep.formSepAlong` read through `embClass`. -/
def formClassAlong (c d : AmodClass N τ 𝒯) : ℝ :=
  formSepAlong hN βs ρ τ (embClass τ 𝒯 c) (embClass τ 𝒯 d)

theorem formClass_eq (c d : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 c d
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernAlong hN βs ρ τ P.1.1 Q.1.1)) := by
  unfold formClassAlong formSepAlong embClass
  simp only [Finsupp.lmapDomain_apply]
  rw [Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun P _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun Q => by simp) (fun Q b₁ b₂ => by simp only [mul_add, add_mul])]
  rfl

theorem formClass_mapDomain (g : ClassMono N τ 𝒯 → ClassMono N τ 𝒯) (c d : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 (Finsupp.mapDomain g c) (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernAlong hN βs ρ τ (g P).1.1 (g Q).1.1)) := by
  rw [formClass_eq, Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun P _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun Q => by simp) (fun Q b₁ b₂ => by simp only [mul_add, add_mul])]

/-- **The time step at level `m`** on class monomials. -/
def TmClass (m : ℕ) : AmodClass N τ 𝒯 →ₗ[ℝ] AmodClass N τ 𝒯 :=
  Finsupp.lmapDomain ℝ ℝ (ClassMono.shift hN τ m)

theorem embClass_TmClass (m : ℕ) (c : AmodClass N τ 𝒯) :
    embClass τ 𝒯 (TmClass hN τ 𝒯 m c) = TmSep hN τ m (embClass τ 𝒯 c) := by
  show Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (ClassMono.shift hN τ m) c)
    = Finsupp.mapDomain (SepMono.shift hN τ m) (Finsupp.mapDomain Subtype.val c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

theorem TmClass_iterate (m n : ℕ) (c : AmodClass N τ 𝒯) :
    (⇑(TmClass hN τ 𝒯 m))^[n] c = Finsupp.mapDomain ((ClassMono.shift hN τ m)^[n]) c := by
  induction n with
  | zero => exact Finsupp.mapDomain_id.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
    show Finsupp.mapDomain (ClassMono.shift hN τ m)
        (Finsupp.mapDomain ((ClassMono.shift hN τ m)^[n]) c) = _
    rw [← Finsupp.mapDomain_comp]

theorem TmClass_half (m : ℕ) (c : AmodClass N τ 𝒯) :
    TmClass hN τ 𝒯 m c = TmClass hN τ 𝒯 (m + 1) (TmClass hN τ 𝒯 (m + 1) c) := by
  show Finsupp.mapDomain (ClassMono.shift hN τ m) c
    = Finsupp.mapDomain (ClassMono.shift hN τ (m + 1))
        (Finsupp.mapDomain (ClassMono.shift hN τ (m + 1)) c)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  exact (ClassMono.shift_half hN τ m P).symm

theorem TmClass_symm (m : ℕ) (c d : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 (TmClass hN τ 𝒯 m c) d
      = formClassAlong hN βs ρ τ 𝒯 c (TmClass hN τ 𝒯 m d) := by
  unfold formClassAlong
  rw [embClass_TmClass, embClass_TmClass]
  exact TmSep_symm_along hN βs ρ τ m _ _

variable {hN βs ρ τ 𝒯}

/-- **The reflection form on class monomials**, a `Transfer.ReflForm`. -/
def contReflFormClassAlong (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) :
    Transfer.ReflForm (AmodClass N τ 𝒯) where
  form := formClassAlong hN βs ρ τ 𝒯
  form_symm c d := formSep_symm_along hN βs ρ τ hR _ _
  form_add_left c c' d := by
    unfold formClassAlong
    rw [map_add]
    exact formSep_add_left_along hN βs ρ τ _ _ _
  form_smul_left r c d := by
    unfold formClassAlong
    rw [map_smul]
    exact formSep_smul_left_along hN βs ρ τ r _ _
  form_nonneg c := by
    rw [formClass_eq]
    exact contS_gram_nonneg_class hR hB c.support (fun P => c P)

theorem formClass_iterate_le (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (m : ℕ) (c : AmodClass N τ 𝒯) :
    ∃ B : ℝ, ∀ n : ℕ, formClassAlong hN βs ρ τ 𝒯 ((⇑(TmClass hN τ 𝒯 m))^[n] c)
      ((⇑(TmClass hN τ 𝒯 m))^[n] c) ≤ B := by
  choose C hC using kernClass_iterate_bound hB m
  refine ⟨∑ P ∈ c.support, ∑ Q ∈ c.support, |c P| * |c Q| * C P Q, fun n => ?_⟩
  rw [TmClass_iterate, formClass_mapDomain]
  show ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q
      * kernAlong hN βs ρ τ ((ClassMono.shift hN τ m)^[n] P).1.1 ((ClassMono.shift hN τ m)^[n] Q).1.1
    ≤ _
  refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
  calc c P * c Q * kernAlong hN βs ρ τ ((ClassMono.shift hN τ m)^[n] P).1.1
        ((ClassMono.shift hN τ m)^[n] Q).1.1
      ≤ |c P * c Q * kernAlong hN βs ρ τ ((ClassMono.shift hN τ m)^[n] P).1.1
          ((ClassMono.shift hN τ m)^[n] Q).1.1| := le_abs_self _
    _ = |c P| * |c Q| * |kernAlong hN βs ρ τ ((ClassMono.shift hN τ m)^[n] P).1.1
          ((ClassMono.shift hN τ m)^[n] Q).1.1| := by rw [abs_mul, abs_mul]
    _ ≤ |c P| * |c Q| * C P Q :=
        mul_le_mul_of_nonneg_left (hC P Q n) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem TmClass_contract (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) (m : ℕ)
    (c : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 (TmClass hN τ 𝒯 m c) (TmClass hN τ 𝒯 m c)
      ≤ formClassAlong hN βs ρ τ 𝒯 c c := by
  obtain ⟨B, hB'⟩ := formClass_iterate_le hB m c
  exact SchwarzIteration.contract_of_bounded_orbit (contReflFormClassAlong hB hR)
    (⇑(TmClass hN τ 𝒯 m)) (TmClass_symm hN βs ρ τ 𝒯 m) c B hB'

theorem formClass_single (P Q : ClassMono N τ 𝒯) (a b : ℝ) :
    formClassAlong hN βs ρ τ 𝒯 (Finsupp.single P a) (Finsupp.single Q b)
      = a * b * kernAlong hN βs ρ τ P.1.1 Q.1.1 := by
  rw [formClass_eq, Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals simp

/-- **The continuum transfer data on class monomials at the dyadic step `dySpacing N m`.** -/
def contTransferClassAlong (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) (m : ℕ) :
    Transfer.TransferData (AmodClass N τ 𝒯) where
  toReflForm := contReflFormClassAlong hB hR
  T := TmClass hN τ 𝒯 m
  vac := Finsupp.single (emptyClass N τ 𝒯) 1
  T_symm := TmClass_symm hN βs ρ τ 𝒯 m
  T_contract := TmClass_contract hB hR m
  T_vac := by
    show Finsupp.mapDomain (ClassMono.shift hN τ m) (Finsupp.single (emptyClass N τ 𝒯) 1)
      = Finsupp.single (emptyClass N τ 𝒯) 1
    rw [Finsupp.mapDomain_single, shift_emptyClass]
  vac_norm := by
    show formClassAlong hN βs ρ τ 𝒯 (Finsupp.single (emptyClass N τ 𝒯) 1)
      (Finsupp.single (emptyClass N τ 𝒯) 1) = 1
    rw [formClass_single, one_mul, one_mul]
    exact kernAlong_empty hN ρ τ βs

theorem positiveTransfer_class (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) (m : ℕ) :
    GNSHilbert.PositiveTransfer (contTransferClassAlong hB hR m) := by
  intro c
  show 0 ≤ formClassAlong hN βs ρ τ 𝒯 c (TmClass hN τ 𝒯 m c)
  rw [TmClass_half, ← TmClass_symm hN βs ρ τ 𝒯 (m + 1)]
  exact (contReflFormClassAlong hB hR).form_nonneg _

end Form

/-! ## 4. Clustering and the gap -/

section Gap

variable {hN : N ≠ 0} {βs : ℕ → ℝ} {ρ : Renorm N} {τ : Fin 4} {𝒯 : TestClass}

/-- **OS4 on class monomials along a coupling tower with a uniform physical gap**, as
`ContinuumSep.contS_cluster_sep_of_towerGapAt`. -/
theorem contS_cluster_class (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) {M : ℝ}
    (hG : TowerGapAt hN τ βs M) (P Q : ClassMono N τ 𝒯) (m n : ℕ) :
    (kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1)
        - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1) ^ 2
      ≤ Real.exp (-(2 * M) * (dySpacing N m * n))
        * (kernAlong hN βs ρ τ P.1.1 P.1.1
          * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hN1 := one_le_of_ne_zero hN
  have hmemP : ∀ᶠ k in atTop, ∀ i : Fin P.1.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((P.1.1.2 i).1.sub r).1 (P.1.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (sepMono_posTime P.1 i))
  have hmemQ : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1.1, ∀ r : ℝ,
      smear (dySpacing N k) ((Q.1.1.2 i).1.sub r).1 (Q.1.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    Filter.eventually_all.mpr (fun i => eventually_smear_sub_mem hN1 τ _ _ (sepMono_posTime Q.1 i))
  have tPQ : Tendsto (fun k => latSkRAlong hN βs ρ k
      (pairFam τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1))) (ultra : Filter ℕ)
      (𝓝 (kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1))) := by
    have h := tendsto_class hB P ((ClassMono.shift hN τ m)^[n] Q)
    rwa [ClassMono.shift_iterate_val, SepMono.shift_iterate] at h
  have tPe : Tendsto (fun k => latSkRAlong hN βs ρ k (pairFam τ P.1.1 (emptyMono N)))
      (ultra : Filter ℕ) (𝓝 (kernAlong hN βs ρ τ P.1.1 (emptyMono N))) :=
    tendsto_class hB P (emptyClass N τ 𝒯)
  have teQ : Tendsto (fun k => latSkRAlong hN βs ρ k (pairFam τ (emptyMono N) Q.1.1))
      (ultra : Filter ℕ) (𝓝 (kernAlong hN βs ρ τ (emptyMono N) Q.1.1)) :=
    tendsto_class hB (emptyClass N τ 𝒯) Q
  have hf : Tendsto (fun k =>
        (latSkRAlong hN βs ρ k (pairFam τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1))
          - latSkRAlong hN βs ρ k (pairFam τ P.1.1 (emptyMono N))
            * latSkRAlong hN βs ρ k (pairFam τ (emptyMono N) Q.1.1)) ^ 2) (ultra : Filter ℕ)
      (𝓝 ((kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1)
          - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1) ^ 2)) :=
    (tPQ.sub (tPe.mul teQ)).pow 2
  have hg : Tendsto (fun k => Real.exp (-(2 * M) * (dySpacing N m * n))
        * (latSkRAlong hN βs ρ k (pairFam τ P.1.1 P.1.1)
          * (latSkRAlong hN βs ρ k (pairFam τ Q.1.1 Q.1.1)
            - latSkRAlong hN βs ρ k (pairFam τ (emptyMono N) Q.1.1) ^ 2))) (ultra : Filter ℕ)
      (𝓝 (Real.exp (-(2 * M) * (dySpacing N m * n))
        * (kernAlong hN βs ρ τ P.1.1 P.1.1
          * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)))) :=
    ((tendsto_class hB P P).mul ((tendsto_class hB Q Q).sub (teQ.pow 2))).const_mul _
  refine le_of_tendsto_of_tendsto hf hg ?_
  have hevLE : ∀ᶠ k in atTop,
      (latSkRAlong hN βs ρ k (pairFam τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1))
        - latSkRAlong hN βs ρ k (pairFam τ P.1.1 (emptyMono N))
          * latSkRAlong hN βs ρ k (pairFam τ (emptyMono N) Q.1.1)) ^ 2
      ≤ Real.exp (-(2 * M) * (dySpacing N m * n))
        * (latSkRAlong hN βs ρ k (pairFam τ P.1.1 P.1.1)
          * (latSkRAlong hN βs ρ k (pairFam τ Q.1.1 Q.1.1)
            - latSkRAlong hN βs ρ k (pairFam τ (emptyMono N) Q.1.1) ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop m, hG, hmemP, hmemQ] with k hk hkr hkP hkQ
    obtain ⟨r, hr0, hg, hrate⟩ := hkr
    have hvec : site (dySpacing N k) (axisVec τ ((2 ^ (k - m) * n : ℕ) : ℤ))
        = timeVec N m τ n := by
      unfold timeVec
      rw [site_dySpacing N hk, scaleSite_axisVec]
      congr 2
    obtain ⟨hcl, hY⟩ := lattice_cluster_along hN βs ρ τ hR k hr0.le hg P.1.1 Q.1.1
      (Yv_mem hN ρ τ k P.1.1 hkP) (Yv_mem hN ρ τ k Q.1.1 hkQ) (2 ^ (k - m) * n)
    rw [hvec] at hcl
    have hlog : Real.log r ≤ -M * dySpacing N k := by
      rw [neg_mul]
      linarith
    have hr_le : r ≤ Real.exp (-M * dySpacing N k) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.mpr hlog
    have hpow : r ^ (2 * (2 ^ (k - m) * n)) ≤ Real.exp (-(2 * M) * (dySpacing N m * n)) := by
      calc r ^ (2 * (2 ^ (k - m) * n))
          ≤ Real.exp (-M * dySpacing N k) ^ (2 * (2 ^ (k - m) * n)) :=
            pow_le_pow_left₀ hr0.le hr_le _
        _ = Real.exp (((2 * (2 ^ (k - m) * n) : ℕ) : ℝ) * (-M * dySpacing N k)) :=
            (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-(2 * M) * (dySpacing N m * n)) := by
            rw [← dySpacing_mul_pow N hk]
            push_cast
            congr 1
            ring
    exact hcl.trans (mul_le_mul_of_nonneg_right hpow hY)
  exact hevLE.filter_mono ultra_le

theorem formClass_pow (m j : ℕ) (x : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 x ((TmClass hN τ 𝒯 m ^ j) x)
      = ∑ P ∈ x.support, ∑ Q ∈ x.support,
          x P * x Q * kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ j) Q.1.1) := by
  rw [Module.End.pow_apply, TmClass_iterate, formClass_eq]
  show ∑ P ∈ x.support, (Finsupp.mapDomain ((ClassMono.shift hN τ m)^[j]) x).sum
      (fun Q b => x P * b * kernAlong hN βs ρ τ P.1.1 Q.1.1) = _
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun Q => by simp) (fun Q b₁ b₂ => by simp only [mul_add, add_mul])]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  show x P * x Q * kernAlong hN βs ρ τ P.1.1 ((ClassMono.shift hN τ m)^[j] Q).1.1 = _
  rw [ClassMono.shift_iterate_val, SepMono.shift_iterate]

theorem formClass_vac_right (x : AmodClass N τ 𝒯) :
    formClassAlong hN βs ρ τ 𝒯 x (Finsupp.single (emptyClass N τ 𝒯) 1)
      = ∑ P ∈ x.support, x P * kernAlong hN βs ρ τ P.1.1 (emptyMono N) := by
  rw [formClass_eq]
  show ∑ P ∈ x.support, (Finsupp.single (emptyClass N τ 𝒯) (1 : ℝ)).sum
      (fun Q b => x P * b * kernAlong hN βs ρ τ P.1.1 Q.1.1) = _
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finsupp.sum_single_index]
  · show x P * 1 * kernAlong hN βs ρ τ P.1.1 (emptyMono N) = x P * kernAlong hN βs ρ τ P.1.1 (emptyMono N)
    rw [mul_one]
  · simp

/-- **Per-vector decay from clustering on class monomials**, as
`ContinuumSep.form_pow_le_of_cluster_sep_along`. -/
theorem form_pow_le_of_cluster_class (hR : ρ.ReflCompat τ) (m : ℕ) {γ : ℝ}
    (hcl : ∀ (P Q : ClassMono N τ 𝒯) (n : ℕ),
      (kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ n) Q.1.1)
          - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1) ^ 2
        ≤ Real.exp (-(2 * γ) * (dySpacing N m * n))
          * (kernAlong hN βs ρ τ P.1.1 P.1.1
            * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)))
    (x : AmodClass N τ 𝒯)
    (hx : formClassAlong hN βs ρ τ 𝒯 x (Finsupp.single (emptyClass N τ 𝒯) 1) = 0) :
    ∃ K : ℝ, ∀ j : ℕ,
      formClassAlong hN βs ρ τ 𝒯 x ((TmClass hN τ 𝒯 m ^ j) x)
        ≤ K * Real.exp (-γ * dySpacing N m) ^ j := by
  have hr0 : 0 ≤ Real.exp (-γ * dySpacing N m) := (Real.exp_pos _).le
  have hexp : ∀ j : ℕ, Real.exp (-(2 * γ) * (dySpacing N m * j))
      = (Real.exp (-γ * dySpacing N m) ^ j) ^ 2 := by
    intro j
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hvacR : ∑ P ∈ x.support, x P * kernAlong hN βs ρ τ P.1.1 (emptyMono N) = 0 := by
    rw [← formClass_vac_right x]
    exact hx
  have hvacL : ∑ Q ∈ x.support, x Q * kernAlong hN βs ρ τ (emptyMono N) Q.1.1 = 0 := by
    have h : ∀ Q ∈ x.support, x Q * kernAlong hN βs ρ τ (emptyMono N) Q.1.1
        = x Q * kernAlong hN βs ρ τ Q.1.1 (emptyMono N) :=
      fun Q _ => by rw [kernAlong_symm hN βs ρ τ hR (emptyMono N) Q.1.1]
    rw [Finset.sum_congr rfl h]
    exact hvacR
  refine ⟨∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Real.sqrt
      (kernAlong hN βs ρ τ P.1.1 P.1.1
        * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)),
    fun j => ?_⟩
  have hconn : ∀ P Q : ClassMono N τ 𝒯,
      |kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ j) Q.1.1)
          - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1|
        ≤ Real.exp (-γ * dySpacing N m) ^ j * Real.sqrt
          (kernAlong hN βs ρ τ P.1.1 P.1.1
            * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)) := by
    intro P Q
    have h := hcl P Q j
    rw [hexp j] at h
    exact abs_le_mul_sqrt_of_sq_le_sep (pow_nonneg hr0 j) h
  have hsplit : ∑ P ∈ x.support, ∑ Q ∈ x.support,
        x P * x Q * kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ j) Q.1.1)
      = ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ j) Q.1.1)
            - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1)
        + ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  have hzero : ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
      * (kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1) = 0 := by
    have h : ∀ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
        * (kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1)
        = x P * kernAlong hN βs ρ τ P.1.1 (emptyMono N)
          * ∑ Q ∈ x.support, x Q * kernAlong hN βs ρ τ (emptyMono N) Q.1.1 := by
      intro P _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      ring
    rw [Finset.sum_congr rfl h, hvacL]
    simp
  rw [formClass_pow, hsplit, hzero, add_zero]
  calc ∑ P ∈ x.support, ∑ Q ∈ x.support, x P * x Q
          * (kernAlong hN βs ρ τ P.1.1 (Mono.shift (timeVec N m τ j) Q.1.1)
            - kernAlong hN βs ρ τ P.1.1 (emptyMono N) * kernAlong hN βs ρ τ (emptyMono N) Q.1.1)
      ≤ ∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q|
          * (Real.exp (-γ * dySpacing N m) ^ j * Real.sqrt
            (kernAlong hN βs ρ τ P.1.1 P.1.1 * (kernAlong hN βs ρ τ Q.1.1 Q.1.1
              - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2))) := by
        refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hconn P Q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ P ∈ x.support, ∑ Q ∈ x.support, |x P| * |x Q| * Real.sqrt
          (kernAlong hN βs ρ τ P.1.1 P.1.1
            * (kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2)))
          * Real.exp (-γ * dySpacing N m) ^ j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        ring

/-- **The continuum gap on class monomials along a coupling tower**, as
`ContinuumSep.continuum_gap_sep_of_towerGapAt`. -/
theorem continuum_gap_class_of_towerGapAt (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ)
    {M : ℝ} (hM : 0 < M) (hG : TowerGapAt hN τ βs M) (m : ℕ) :
    0 < Real.exp (-M * dySpacing N m) ∧ Real.exp (-M * dySpacing N m) < 1
      ∧ TransferGap.GapAt (contTransferClassAlong hB hR m) (Real.exp (-M * dySpacing N m))
      ∧ (∀ u : GNSHilbert.H (contTransferClassAlong hB hR m).toReflForm,
          inner ℂ (GNSHilbert.Omega (contTransferClassAlong hB hR m).toReflForm
            (contTransferClassAlong hB hR m).vac) u = (0 : ℂ) →
          ‖GNSHilbert.opT (contTransferClassAlong hB hR m) u‖
            ≤ Real.exp (-M * dySpacing N m) * ‖u‖)
      ∧ spectrum ℝ (GNSHilbert.opT (contTransferClassAlong hB hR m))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-M * dySpacing N m))
      ∧ IsGreatest (spectrum ℝ (GNSHilbert.opT (contTransferClassAlong hB hR m))) 1 := by
  have hr0 : 0 < Real.exp (-M * dySpacing N m) := Real.exp_pos _
  have hr1 : Real.exp (-M * dySpacing N m) < 1 := by
    rw [Real.exp_lt_one_iff, neg_mul]
    exact neg_lt_zero.mpr (mul_pos hM (dySpacing_pos (one_le_of_ne_zero hN) m))
  have hg : TransferGap.GapAt (contTransferClassAlong hB hR m) (Real.exp (-M * dySpacing N m)) := by
    refine gapAt_of_per_vector_form_decay _ hr0.le (fun x hx => ?_)
    obtain ⟨K, hK⟩ := form_pow_le_of_cluster_class hR m (γ := M)
      (fun P Q n => contS_cluster_class hB hR hG P Q m n) x hx
    exact ⟨K, fun n => hK (2 * n)⟩
  refine ⟨hr0, hr1, hg, fun u hu => GapToOperator.norm_opT_le_of_orth _ hr0.le hg u hu, ?_,
    GNSHilbert.isGreatest_one_spectrum_opT _⟩
  intro x hx
  rcases GapToOperator.spectrum_opT_subset _ hr0.le hg hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Set.mem_Ici.mp
      (GNSHilbert.spectrum_opT_nonneg _ (positiveTransfer_class hB hR m) hx), h.2⟩

/-- **A non-zero connected two-point function on a class monomial.** -/
def ConnectedTwoPointNonzeroClassAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) (τ : Fin 4)
    (𝒯 : TestClass) : Prop :=
  ∃ Q : ClassMono N τ 𝒯,
    kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ (emptyMono N) Q.1.1 ^ 2 ≠ 0

/-- **Non-triviality of the reconstructed space on class monomials.** -/
theorem exists_orth_ne_zero_class (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ) (m : ℕ)
    (h : ConnectedTwoPointNonzeroClassAlong hN βs ρ τ 𝒯) :
    ∃ u : GNSHilbert.H (contTransferClassAlong hB hR m).toReflForm,
      inner ℂ (GNSHilbert.Omega (contTransferClassAlong hB hR m).toReflForm
        (contTransferClassAlong hB hR m).vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega (contTransferClassAlong hB hR m).toReflForm
        (contTransferClassAlong hB hR m).vac := by
  obtain ⟨Q, hQ⟩ := h
  have hx : (contTransferClassAlong hB hR m).form (Finsupp.single Q 1) (Finsupp.single Q 1)
      - (contTransferClassAlong hB hR m).form (Finsupp.single Q 1)
          (contTransferClassAlong hB hR m).vac ^ 2 ≠ 0 := by
    show formClassAlong hN βs ρ τ 𝒯 (Finsupp.single Q 1) (Finsupp.single Q 1)
      - formClassAlong hN βs ρ τ 𝒯 (Finsupp.single Q 1) (Finsupp.single (emptyClass N τ 𝒯) 1) ^ 2 ≠ 0
    rw [formClass_single, formClass_single]
    simp only [one_mul]
    show kernAlong hN βs ρ τ Q.1.1 Q.1.1 - kernAlong hN βs ρ τ Q.1.1 (emptyMono N) ^ 2 ≠ 0
    rw [← kernAlong_symm hN βs ρ τ hR (emptyMono N) Q.1.1]
    exact hQ
  obtain ⟨u, hu, hu0⟩ := exists_orth_ne_zero (contTransferClassAlong hB hR m) _ hx
  exact ⟨u, hu, hu0, not_mem_span_vac _ hu hu0⟩

end Gap

/-! ## 5. The Clay continuum conclusion on a class -/

section Clay

/-- **The Clay continuum conclusion on the class `𝒯` at window `L` along `βs`**: some `c > 0` has, at
every dyadic step `m`, the reconstructed transfer data on class monomials `GappedAt` the rate
`e^{−(c/L)·dySpacing N m}` and `NontrivialVacuum`. -/
def ClayContinuumPairClassAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (𝒯 : TestClass)
    (hB : PairBoundClassAlong hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯) (L : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
    ContinuumClay.GappedAt
        (contTransferClassAlong hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m)
        (Real.exp (-(c / L) * dySpacing N m))
      ∧ ContinuumClay.NontrivialVacuum
        (contTransferClassAlong hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m)

/-- **One class monomial with reflected reading bounded below**: a single insertion of a field `O`
against a test function of the class supported in `y_τ ≥ d > 0`. -/
def PairLowerBoundClassAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (𝒯 : TestClass) : Prop :=
  ∃ (O : LField (MassGap.SUN.SU N)) (f : TestFn) (d c : ℝ), 0 < d ∧ 0 < c ∧ 𝒯.mem f ∧
    (∀ y, f.1 y ≠ 0 → d ≤ y τ) ∧
    ∀ᶠ k in atTop, c ≤ latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k
      (pairFam τ (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)))

/-- **The lower bound and E on the class give a non-zero connected two-point function.** -/
theorem connectedTwoPointNonzero_of_pairLowerBoundClass (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    {𝒯 : TestClass} (hB : PairBoundClassAlong hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯)
    (hP : PairLowerBoundClassAlong hN βs Z τ 𝒯) :
    ConnectedTwoPointNonzeroClassAlong hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨O, f, d, c, hd, hc, hf, hfs, hev⟩ := hP
  set Q : ClassMono N τ 𝒯 := ⟨⟨ContinuumNontrivial.mono1 (O, f), d, hd,
    ⟨fun _ y hy => hfs y hy, fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij⟩⟩,
    fun _ => hf⟩ with hQ
  have htend := tendsto_class hB Q Q
  have hge : c ≤ kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ
      (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)) :=
    ge_of_tendsto htend (hev.filter_mono ultra_le)
  refine ⟨Q, ?_⟩
  show kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ
      (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f))
    - kernAlong hN βs (Renorm.connectedAlong hN βs Z) τ (emptyMono N)
      (ContinuumNontrivial.mono1 (O, f)) ^ 2 ≠ 0
  rw [ContinuumNontrivial.kern_empty_mono1_along hN βs Z τ hZ O f, zero_pow two_ne_zero, sub_zero]
  exact (lt_of_lt_of_le hc hge).ne'

/-- **The Clay continuum statement on a class along a coupling tower**: E on the reflection diagonal
of class monomials, the tower gap and one class monomial with reflected reading bounded below give
`ClayContinuumPairClassAlong` at every window `L > 0`. -/
theorem clay_class_of_diagBound_towerGapAt (hN : N ≠ 0) (βs : ℕ → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    {𝒯 : TestClass} (hD : DiagBoundClassAlong hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯) {M : ℝ}
    (hM : 0 < M) (hG : TowerGapAt hN τ βs M) {L : ℝ} (hL : 0 < L)
    (hP : PairLowerBoundClassAlong hN βs Z τ 𝒯) :
    ClayContinuumPairClassAlong hN βs Z τ hZ 𝒯
      (pairBoundClass_of_diagBoundClass hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯
        (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) hD) L := by
  set hB := pairBoundClass_of_diagBoundClass hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯
    (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) hD
  have hne := connectedTwoPointNonzero_of_pairLowerBoundClass hN βs Z τ hZ hB hP
  have e : M * L / L = M := mul_div_cancel_right₀ M hL.ne'
  refine ⟨M * L, mul_pos hM hL, fun m => ?_⟩
  rw [e]
  obtain ⟨hr0, hr1, hg, hop, hspec, hgr⟩ := continuum_gap_class_of_towerGapAt hB
    (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) hM hG m
  exact ⟨⟨hr0, hr1, hg, hop, hspec, hgr⟩,
    exists_orth_ne_zero_class hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m hne⟩

end Clay

end MassGap.ContinuumSepClass

#print axioms MassGap.ContinuumSepClass.pairBoundClass_of_diagBoundClass
#print axioms MassGap.ContinuumSepClass.contS_gram_nonneg_class
#print axioms MassGap.ContinuumSepClass.contTransferClassAlong
#print axioms MassGap.ContinuumSepClass.positiveTransfer_class
#print axioms MassGap.ContinuumSepClass.contS_cluster_class
#print axioms MassGap.ContinuumSepClass.continuum_gap_class_of_towerGapAt
#print axioms MassGap.ContinuumSepClass.exists_orth_ne_zero_class
#print axioms MassGap.ContinuumSepClass.connectedTwoPointNonzero_of_pairLowerBoundClass
#print axioms MassGap.ContinuumSepClass.clay_class_of_diagBound_towerGapAt
