import Mathlib
import MassGap.RegularDense
import MassGap.PreObserver

/-!
# MassGap.RegularFull — the regular sector on every local field, and what the Clay statement reads of it

`RegularDense` reduces the reconstruction to the regular sector `RH` of a class `D`. This module removes
the fields from the question, says what non-triviality of a sector is, and shows what the split into a
sector and its complement changes in the statement. Declarations are in the namespace
`MassGap.RegularFull`.

## Every local field is regular (proved)

`energy0` leaves a field outside `D` unscaled, so it reads `O ∘ V_k`, a continuous function on a compact
space. Its smear is bounded by `‖O‖ M (2R + 3)⁴` at every step with spacing below `1` (`norm_smear_le`), which is stronger than
the cube moments of a field of `D`. `allMom_energy0`: every local field has smeared moments on every
cube (`AllMom`). The sup-norm estimates then hold with no condition on the field:
`abs_contSF_le_of_mom`, `exists_sup_const`, `tendsto_contSF_of_sup_all`, `tendsto_contSF_translate_all`,
and OS1 for every real vector, `contSF_translate_real_all`.

So the sector to use is `RH … (UF N)`, `UF N` being all local fields: its monomials are the uniformly
continuous test functions at any fields. `aU` is the strongly continuous unitary representation of
`spatial τ` on it (`inner_aU`, `aU_add`, `aU_zero`, `aU_vac`, `continuous_aU`, `commute_aU_aTime`).
`observerAll` is the `OSDataS` on it and `allSpatial` its real translations, on the input
`RegConnectedNonzero … (UF N)`, which `regConnected_uf` gives from the input at any smaller class.

## Non-triviality (proved)

`exists_orth_iff`: a GNS space has a non-zero vector orthogonal to the vacuum exactly when some generator
has a non-zero connected reading. `flowConnected_iff`, `regConnected_iff`: `FlowConnectedNonzero` is
exactly non-triviality of `FlowH`, `RegConnectedNonzero` exactly that of the sector.
`not_regConnected_iff`: failing it, every regular reflected reading factorises.
`regConnected_of_cross`, `regConnected_of_mix`, `regConnected_of_lattice`: the routes to it. A vector of
`FlowH` that does not factorise against a regular `Q` suffices, in particular a connected `mixT`.

The tree has no witness of `FlowConnectedNonzero`: every capstone takes it as a hypothesis or, in
`PreObserver`, replaces it by a vector built from the composites' link. `flowConnected_of_link` derives
it from that vector. That proof does not name a monomial: the vector exists because the span of all
margin monomials is dense.

## What the sector holds (proved)

`gvecT_mem_range`: every regular monomial. `vecD_mem_range`: every decaying monomial with uniformly
continuous functions, so with Schwartz functions (`uc_ofE4`): the vectors of the Schwartz reconstruction,
at fields of `D`, lie in the sector. `range_J_eq_univ_iff`: the sector is all of `FlowH` exactly when it
holds every margin monomial's vector.

## The split (proved)

For any `SubSector`: the complement carries no vacuum (`orth_vac`), the times keep it (`orth_time`), it
decays at the gap of `X` (`norm_time_orth`), and the time acts sector by sector (`norm_sq_time_split`).
`gap_iff_sector`: for `g ≤ X.gap`, contraction at rate `g` on the vacuum complement of `X` is the same
statement as on that of the reduced reconstruction.

The clauses of `ClayData` read the Schwinger functions, the time semigroup and the gap on `X.base.H`,
`HLs` and `HLC`. None reads a spatial translation operator on `X.base.H`, so `realT` and its identity
branch do not enter the statement. The zero-momentum reading needs no identity branch either:
`ShellMomentum.observerSpatial` translates all of `FlowH` by the physical dyadic action, and
`mem_zeroMom_allSpatial_iff` says that on the sector its zero-momentum space is that of the real
translations (`dyadic_fixed_iff`).

## What does not follow

Plainly:

* `RegConnectedNonzero` is not discharged, at `D` or at `UF N`. `not_regConnected_of_zero`: it fails for
  a class of zero fields, where `hD`, `hpos` and `hcube` all hold, so no argument from those three proves
  it at `D`. The link inputs give `FlowConnectedNonzero`, and no regular witness: nothing in the tree
  connects the composites to the flowed readings except `mixT`, whose connected part is not bounded
  below. What is left is one lattice lower bound at a Lipschitz monomial (`regConnected_of_lattice`) or
  one connected `mixT` (`regConnected_of_mix`). `observerAll` takes it as an input.
* `V = FlowH` is neither proved nor refuted, at any `D`. With `UF N` the fields play no part, and what is
  left is the test functions. `contSF_sampleCopy`: a test function that is zero almost everywhere can
  read as any other, because the readings sample the sites of the steps. So the Schwinger functions are
  not continuous in the `L¹` norm of Lebesgue measure, and approximation in that norm cannot give
  `V = FlowH`. Whether a monomial oscillating at the scale of the cell lies in `V` asks how the state
  reads that scale, and the tree bounds no such reading. A sampled `L¹` estimate for Riemann-integrable
  test functions is not proved here.
* The vectors `w`, `wC` of the composites in `ClayData` are not shown to lie in the sector. Their gap
  (`SpectralGapOn`) does not need it. Real translations on `HLC`, and on `FlowH` beyond the sector, are not
  built, and `observerSpatial` gives dyadic translations there, with no continuity in the vector.
* `gap_iff_sector` stops at `X.gap`. A gap on the sector above `X.gap` says nothing about the complement.
* `ClayFull` and `ClayStatement` still name `observerOSDataS` on `FlowH`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.RegularFull

open Filter Topology MeasureTheory
open scoped NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyMoments
open MassGap.ShellTranslate
open MassGap.ShellMomentum (SpatialData zeroMom opS opS_coe inner_opS opS_mul opS_eq_one opS_Omega
  opS_commute_opT gForm_mapDomain_inv spT spShift site_time_zero SpIdx observerSpatial)
open MassGap.ObserverOSReconstructionS (OSDataS observerOSDataS)
open MassGap.RegularDense (SubSector reduce RegConnectedNonzero)

noncomputable section

variable {N : ℕ}

/-! ## 1. Every field has smeared moments -/

section Moments

/-- **The smeared moment of one field on one cube**: eventually in the step, for every test function
in the cube bounded by `L`, the moment of order `2 p` is at most `c L^{2p}`. DERIVED: `0` the sign of
`L`; `2` makes the power even. -/
def SmearMom (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) (R c : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ k in atTop, ∀ (f : TestFn) (L : ℝ), 0 < L → IsTest f.1 R L →
    stateK hN k (smear (dySpacing N k) (Φ.map k O).1 f ^ (2 * p)) ≤ c * L ^ (2 * p)

/-- **Every field has a smeared moment on every cube.** DERIVED: `0` the lower end of `R`, `c`. -/
def AllMom (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (O : LField (MassGap.SUN.SU N)) (R : ℝ), 0 ≤ R → ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ SmearMom hN Φ O R c p

/-- DERIVED: `2` makes the power even; `0` the sign of `L`. -/
theorem SmearMom.mono {hN : N ≠ 0} {Φ : Flow N} {O : LField (MassGap.SUN.SU N)} {R c c' : ℝ} {p : ℕ}
    (h : SmearMom hN Φ O R c p) (hc : c ≤ c') : SmearMom hN Φ O R c' p :=
  Filter.Eventually.mono h fun _ hk f L hL hf =>
    (hk f L hL hf).trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hL.le _))

/-- **The fields outside `D` are the easy ones.** `energy0` does not scale a field outside `D`: it reads
`O ∘ V_k`, a continuous function on a compact space, so its smear is bounded by
`‖O‖ M (2R + 3)⁴` at every step with spacing below `1` (`norm_smear_le`). Inside `D` this is `moment_smear_energy0_le`.
So all of `hpos`, `hcube` reach every local field. DERIVED: `0` the sign of `L`, the excluded colour
count and the subtraction; `1` the spacing bound; `2`, `3`, `4` are `norm_smear_le`'s. -/
theorem allMom_energy0 (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) :
    AllMom hN (energy0 W D hD) := by
  intro O R hR p
  by_cases hO : O ∈ D
  · obtain ⟨C, hC⟩ := hcube O hO R hR p
    refine ⟨|C|, abs_nonneg _, ?_⟩
    filter_upwards [hC, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)]
      with k hk hk1 f L hL hf
    calc stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 f ^ (2 * p))
        ≤ L ^ (2 * p) * stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p)) :=
          moment_smear_energy0_le hN W hD hpos hO hk1.le f hf p
      _ ≤ L ^ (2 * p) * |C| :=
          mul_le_mul_of_nonneg_left (hk.trans (le_abs_self _)) (pow_nonneg hL.le _)
      _ = |C| * L ^ (2 * p) := mul_comm _ _
  · refine ⟨(‖O.1‖ * (2 * R + 3) ^ 4) ^ (2 * p), by positivity, ?_⟩
    filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk1 f L hL hf
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hmap : ((energy0 W D hD).map k O).1 = (W.fieldMap k O).1 := by
      show zOn D k O • ((W.fieldMap k O).1 - sOn D (s0 N) k O • (1 : C(Cfg N, ℝ))) = _
      rw [zOn_of_not_mem hO, sOn_of_not_mem hO, zero_smul, sub_zero, one_smul]
    rw [hmap]
    have h1 : ‖(W.fieldMap k O).1‖ ≤ ‖O.1‖ :=
      (ContinuousMap.norm_le (W.fieldMap k O).1 (norm_nonneg O.1)).mpr
        (fun U => O.1.norm_coe_le_norm (W.V k U))
    have h23 : (0 : ℝ) ≤ (2 * R + 3) ^ 4 := by positivity
    have h2 := norm_smear_le ha hk1.le (W.fieldMap k O).1 f hf
    have h3 : ‖smear (dySpacing N k) (W.fieldMap k O).1 f‖ ≤ ‖O.1‖ * (2 * R + 3) ^ 4 * L := by
      refine h2.trans ?_
      calc ‖(W.fieldMap k O).1‖ * (L * (2 * R + 3) ^ 4)
          ≤ ‖O.1‖ * (L * (2 * R + 3) ^ 4) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hL.le h23)
        _ = _ := by ring
    have hq : Even (2 * p) := even_two_mul p
    calc stateK hN k (smear (dySpacing N k) (W.fieldMap k O).1 f ^ (2 * p))
        ≤ stateK hN k ((‖O.1‖ * (2 * R + 3) ^ 4 * L) ^ (2 * p) • (1 : C(Cfg N, ℝ))) :=
          (stateK hN k).mono fun U => by
            simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply,
              ContinuousMap.one_apply, smul_eq_mul, mul_one]
            rw [← hq.pow_abs]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (((smear (dySpacing N k) (W.fieldMap k O).1 f).norm_coe_le_norm U).trans h3) _
      _ = (‖O.1‖ * (2 * R + 3) ^ 4 * L) ^ (2 * p) := by
          rw [(stateK hN k).map_smul, (stateK hN k).map_one, mul_one]
      _ = _ := mul_pow _ _ _

/-- **OS0 from the smeared moments**, on one cube. The proof of `abs_contSF_energy0_le` with the moment
of any field in place of the cube moment of a field of `D`. DERIVED: `0` the lower end of `ε`, the limit
point and the excluded colour count; `1`, `2` as in `abs_contSF_energy0_le`. -/
theorem abs_contSF_le_of_mom (hN : N ≠ 0) (Φ : Flow N) {ι : Type} [Fintype ι] (G : ι → SField N)
    {R c : ℝ} (hc : ∀ i, SmearMom hN Φ (G i).1 R c (Fintype.card ι)) (M : ι → ℝ)
    (hM : ∀ i, IsTest (G i).2.1 R (M i)) :
    |contSF hN Φ G| ≤ (1 + Fintype.card ι * c) * ∏ i, M i := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hM i).M_nonneg
  have key : ∀ ε : ℝ, 0 < ε →
      |contSF hN Φ G| ≤ (1 + Fintype.card ι * c) * ∏ i, (M i + ε) := by
    intro ε hε
    have hev : ∀ᶠ k in atTop, |latSF hN Φ k G| ≤ (1 + Fintype.card ι * c) * ∏ i, (M i + ε) := by
      filter_upwards [Filter.eventually_all.mpr hc] with k hck
      show |latSk hN k (fun i => Φ.field k (G i))| ≤ _
      rw [latSk_eq]
      show |stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (G i).1).1 (G i).2)| ≤ _
      exact abs_state_prod_le (stateK hN k) _ (fun i => M i + ε)
        (fun i => by linarith [hM0 i])
        (fun i => hck i _ _ (by linarith [hM0 i]) (isTest_mono (hM i) (by linarith)))
    obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hev
    have hlim : contSF hN Φ G = x := hx.limUnder_eq
    rw [hlim]
    exact le_of_tendsto hx.abs (hev.filter_mono ultra_le)
  have hcont : Continuous (fun ε : ℝ => (1 + Fintype.card ι * c) * ∏ i, (M i + ε)) :=
    continuous_const.mul (continuous_finset_prod _ (fun i _ => continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ => (1 + Fintype.card ι * c) * ∏ i, (M i + ε)) (𝓝[>] 0)
      (𝓝 ((1 + Fintype.card ι * c) * ∏ i, (M i + 0))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun ε hε => key ε hε))
  simpa only [add_zero] using h

/-- **Sup-norm continuity of the Schwinger functions for every local field.** One constant `K` for the
fields `O` and the cube, whatever the test functions. The hybrids of `abs_contSF_energy0_sub_le`, with
`abs_contSF_le_of_mom` in place of the bound for fields of `D`. DERIVED: `0` the lower end of `K`, the
sign of `R`; `1` the coefficient of the replaced test function, `-1` of the subtracted one. -/
theorem exists_sup_const (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (hM : AllMom hN Φ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (O : ι → LField (MassGap.SUN.SU N)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F F' : ι → SField N, (∀ i, (F i).1 = O i) → (∀ i, (F' i).1 = O i) →
      ∀ (M : ι → ℝ) (δ : ℝ), (∀ i, IsTest (F i).2.1 R (M i)) → (∀ i, IsTest (F' i).2.1 R (M i)) →
      (∀ i y, |(F' i).2.1 y - (F i).2.1 y| ≤ δ) →
      |contSF hN Φ F' - contSF hN Φ F| ≤ K * ∑ a, δ * ∏ i ∈ Finset.univ \ {a}, M i := by
  have hex := fun i => hM (O i) R hR (Fintype.card ι)
  choose c hc0 hc using hex
  have hsum0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc0 i
  have hcO : ∀ i, SmearMom hN Φ (O i) R (∑ i, c i) (Fintype.card ι) := fun i =>
    (hc i).mono (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (Finset.mem_univ i))
  refine ⟨1 + Fintype.card ι * ∑ i, c i, by positivity, ?_⟩
  intro F F' hFO hFO' M δ hF hF' hclose
  have hfield : ∀ i, (F' i).1 = (F i).1 := fun i => by rw [hFO, hFO']
  let hyb : Finset ι → ι → SField N := fun s i => if i ∈ s then F' i else F i
  have hyb_field : ∀ s i, (hyb s i).1 = (F i).1 := by
    intro s i
    by_cases h : i ∈ s
    · simp only [hyb, if_pos h]; exact hfield i
    · simp only [hyb, if_neg h]
  have hyb_test : ∀ s i, IsTest (hyb s i).2.1 R (M i) := by
    intro s i
    by_cases h : i ∈ s
    · simp only [hyb, if_pos h]; exact hF' i
    · simp only [hyb, if_neg h]; exact hF i
  have step : ∀ s : Finset ι, |contSF hN Φ (hyb s) - contSF hN Φ F|
      ≤ (1 + Fintype.card ι * ∑ i, c i) * ∑ a ∈ s, δ * ∏ i ∈ Finset.univ \ {a}, M i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : hyb ∅ = F := funext (fun i => by simp [hyb])
      rw [e, sub_self, abs_zero, Finset.sum_empty, mul_zero]
    | insert a s ha ih =>
      let d : TestFn := testAdd (F' a).2 (testSmul (-1) (F a).2)
      have hd : IsTest d.1 R δ := by
        refine ⟨hR, fun y => ?_, fun y hy j => ?_⟩
        · show |(F' a).2.1 y + -1 * (F a).2.1 y| ≤ δ
          have := hclose a y
          rwa [neg_one_mul, ← sub_eq_add_neg]
        · by_cases h1 : (F' a).2.1 y = 0
          · have h2 : (F a).2.1 y ≠ 0 := by
              intro h2
              exact hy (show (F' a).2.1 y + -1 * (F a).2.1 y = 0 by rw [h1, h2]; ring)
            exact (hF a).2.2 y h2 j
          · exact (hF' a).2.2 y h1 j
      have e1 : hyb (insert a s) = Function.update (hyb s) a ((F a).1, testAdd (F a).2 d) := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp only [hyb, if_pos (Finset.mem_insert_self i s)]
          refine Prod.ext (hfield i) (Subtype.ext (funext (fun y => ?_)))
          show (F' i).2.1 y = (F i).2.1 y + ((F' i).2.1 y + -1 * (F i).2.1 y)
          ring
        · rw [Function.update_of_ne hi]
          simp only [hyb, Finset.mem_insert, hi, false_or]
      have e2 : Function.update (hyb s) a ((F a).1, (F a).2) = hyb s := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp only [hyb, if_neg ha]
        · rw [Function.update_of_ne hi]
      have hadd := contSF_update_add hN Φ hB (hyb s) a (F a).1 (F a).2 d
      have hfu : ∀ i, (Function.update (hyb s) a ((F a).1, d) i).1 = (F i).1 := by
        intro i
        by_cases hi : i = a
        · subst hi; rw [Function.update_self]
        · rw [Function.update_of_ne hi]; exact hyb_field s i
      have hbound := abs_contSF_le_of_mom hN Φ (Function.update (hyb s) a ((F a).1, d))
        (R := R) (c := ∑ i, c i)
        (fun i => by rw [hfu i, hFO i]; exact hcO i) (Function.update M a δ)
        (fun i => by
          by_cases hi : i = a
          · subst hi; rw [Function.update_self, Function.update_self]; exact hd
          · rw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hyb_test s i)
      rw [Finset.prod_update_of_mem (Finset.mem_univ a)] at hbound
      rw [e1, hadd, e2, Finset.sum_insert ha, mul_add]
      have htri : |contSF hN Φ (hyb s) + contSF hN Φ (Function.update (hyb s) a ((F a).1, d))
            - contSF hN Φ F|
          ≤ |contSF hN Φ (Function.update (hyb s) a ((F a).1, d))|
            + |contSF hN Φ (hyb s) - contSF hN Φ F| := by
        have := abs_add_le (contSF hN Φ (Function.update (hyb s) a ((F a).1, d)))
          (contSF hN Φ (hyb s) - contSF hN Φ F)
        calc _ = |contSF hN Φ (Function.update (hyb s) a ((F a).1, d))
              + (contSF hN Φ (hyb s) - contSF hN Φ F)| := by
              congr 1; ring
          _ ≤ _ := this
      refine htri.trans (add_le_add ?_ ih)
      have e3 : ∏ x ∈ Finset.univ \ {a}, Function.update M a δ x
          = ∏ x ∈ Finset.univ \ {a}, M x :=
        Finset.prod_congr rfl fun x hx => Function.update_of_ne (by simpa using hx) _ _
      simpa [e3] using hbound
  have e : hyb Finset.univ = F' := funext (fun i => by simp [hyb])
  have := step Finset.univ
  rwa [e] at this

/-- **Continuity in the translation vector, every local field.** `ShellTranslate.tendsto_contSF_translate`
with `exists_sup_const`. DERIVED: `0` the zero translation and the signs; `1` bounds `‖dᵢ‖`, keeping the
translates in one cube, and makes `A + 1` positive; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_contSF_translate_all (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (hM : AllMom hN Φ) {ι : Type} [Fintype ι] (F : ι → SField N)
    (hU : ∀ i, UniformContinuous (F i).2.1) :
    Tendsto (fun d : ι → Fin 4 → ℝ => contSF hN Φ (fun i => ((F i).1, (F i).2.translate (d i))))
      (𝓝 0) (𝓝 (contSF hN Φ F)) := by
  classical
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i + 1 := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, R0 i := Finset.sum_nonneg (fun i _ => (hRM i).1)
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith
  have hRi : ∀ i, R0 i + 1 ≤ R := fun i => by
    have h4 : R0 i ≤ ∑ i, R0 i :=
      Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
    rw [hRdef]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_sup_const hN Φ hB hM (fun i => (F i).1) hR0
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hK0
      (Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => (hRM i).M_nonneg)))
  have hF : ∀ i, IsTest (F i).2.1 R (M i) := fun i =>
    ⟨hR0, (hRM i).2.1, fun y hy j => ((hRM i).2.2 y hy j).trans (by linarith [hRi i])⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA1 : 0 < A + 1 := by linarith
  have hδ : 0 < ε / (A + 1) := div_pos hε hA1
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      ∀ a b : Fin 4 → ℝ, dist a b < η → dist ((F i).2.1 a) ((F i).2.1 b) < ε / (A + 1) := by
    intro i
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp (hU i) _ hδ
    exact ⟨η, hη, fun a b hab => h hab⟩
  choose η hη0 hηf using hη
  have hev : ∀ᶠ d : ι → Fin 4 → ℝ in 𝓝 0, ∀ i, ‖d i‖ < η i ∧ ‖d i‖ < 1 := by
    rw [Filter.eventually_all]
    intro i
    have ht : Tendsto (fun d : ι → Fin 4 → ℝ => ‖d i‖) (𝓝 0) (𝓝 0) := by
      have h := ((continuous_apply i).tendsto (0 : ι → Fin 4 → ℝ)).norm
      simpa using h
    exact (ht.eventually (gt_mem_nhds (hη0 i))).and (ht.eventually (gt_mem_nhds one_pos))
  filter_upwards [hev] with d hd
  have hF' : ∀ i, IsTest ((F i).2.translate (d i)).1 R (M i) := by
    intro i
    refine ⟨hR0, fun y => (hRM i).2.1 _, fun y hy j => ?_⟩
    have h1 : |(y - d i) j| ≤ R0 i := (hRM i).2.2 (y - d i) hy j
    have h2 : |d i j| ≤ ‖d i‖ := by
      have := norm_le_pi_norm (d i) j
      rwa [Real.norm_eq_abs] at this
    have h3 : |y j| ≤ |(y - d i) j| + |d i j| := by
      have h7 := abs_add_le ((y - d i) j) (d i j)
      have e : (y - d i) j + d i j = y j := by simp
      rw [e] at h7
      exact h7
    linarith [hRi i, (hd i).2]
  have hclose : ∀ i y, |((F i).2.translate (d i)).1 y - (F i).2.1 y| ≤ ε / (A + 1) := by
    intro i y
    have h := hηf i (y - d i) y (by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact (hd i).1)
    rw [Real.dist_eq] at h
    exact h.le
  have hdiff := hK F (fun i => ((F i).1, (F i).2.translate (d i))) (fun i => rfl) (fun i => rfl)
    M (ε / (A + 1)) hF hF' hclose
  have hsum : K * ∑ a, ε / (A + 1) * ∏ i ∈ Finset.univ \ {a}, M i = ε / (A + 1) * A := by
    rw [hAdef, ← Finset.mul_sum]
    ring
  rw [hsum] at hdiff
  rw [Real.dist_eq]
  calc |contSF hN Φ (fun i => ((F i).1, (F i).2.translate (d i))) - contSF hN Φ F|
      ≤ ε / (A + 1) * A := hdiff
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hA1]
      nlinarith

/-- **OS1 on all of `ℝ⁴`, every local field.** The dyadic translates have the limit of the family
(`contSF_translate`) and they are dense, so continuity carries the invariance to `v`. DERIVED: `0` the
excluded colour count; `4` in `Fin 4` the spacetime dimension. -/
theorem contSF_translate_real_all (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (hM : AllMom hN Φ) {ι : Type} [Fintype ι] (F : ι → SField N)
    (hU : ∀ i, UniformContinuous (F i).2.1) (v : Fin 4 → ℝ) :
    contSF hN Φ (fun i => ((F i).1, (F i).2.translate v)) = contSF hN Φ F := by
  have ht := tendsto_contSF_translate_all hN Φ hB hM (fun i => ((F i).1, (F i).2.translate v))
    (fun i => uniformContinuous_translate (hU i) v)
  have h1 : Tendsto (fun w : Fin 4 → ℝ => fun _ : ι => w - v) (𝓝 v) (𝓝 0) :=
    tendsto_pi_nhds.mpr fun _ =>
      (continuous_id.sub continuous_const).tendsto' v 0 (sub_self v)
  have e : ∀ w : Fin 4 → ℝ,
      (fun i => (((F i).1, (F i).2.translate v).1, (((F i).1, (F i).2.translate v) : SField N).2.translate
        (w - v))) = fun i => ((F i).1, (F i).2.translate w) := fun w => funext fun i => by
    show ((F i).1, ((F i).2.translate v).translate (w - v)) = ((F i).1, (F i).2.translate w)
    rw [TestFn.translate_translate]
    simp
  have h2 : Tendsto (fun w : Fin 4 → ℝ => contSF hN Φ (fun i => ((F i).1, (F i).2.translate w)))
      (𝓝 v) (𝓝 (contSF hN Φ fun i => ((F i).1, (F i).2.translate v))) :=
    (ht.comp h1).congr fun w => congrArg (contSF hN Φ) (e w)
  refine (eq_of_forall_dist_le fun ε hε => ?_)
  obtain ⟨m, n, hw⟩ := ContinuumHypercubic.exists_dyadic_of_eventually (one_le_of_ne_zero hN)
    ((Metric.tendsto_nhds.mp h2) ε hε)
  rw [contSF_translate hN Φ F m n] at hw
  rw [dist_comm]
  exact hw.le

/-- **Sup-norm continuity for any local field**, in the sequential form of `tendsto_contSF_of_sup`. The
fields may lie outside `D`. DERIVED: `0` the limit, the lower end of `R`; `1` the cube margin. -/
theorem tendsto_contSF_of_sup_all (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (hM : AllMom hN Φ) {ι : Type} [Fintype ι] (F : ι → SField N)
    (G : ℕ → ι → SField N) (hfield : ∀ k i, (G k i).1 = (F i).1)
    (hdom : ∀ k i y, |(G k i).2.1 y| ≤ |(F i).2.1 y|) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k i y, |(G k i).2.1 y - (F i).2.1 y| ≤ δ k) :
    Tendsto (fun k => contSF hN Φ (G k)) atTop (𝓝 (contSF hN Φ F)) := by
  classical
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i + 1 := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, R0 i := Finset.sum_nonneg (fun i _ => (hRM i).1)
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith
  have hRi : ∀ i, R0 i + 1 ≤ R := fun i => by
    have h4 : R0 i ≤ ∑ i, R0 i :=
      Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
    rw [hRdef]; linarith
  obtain ⟨K, -, hK⟩ := exists_sup_const hN Φ hB hM (fun i => (F i).1) hR0
  have hF : ∀ i, IsTest (F i).2.1 R (M i) := fun i =>
    ⟨hR0, (hRM i).2.1, fun y hy j => ((hRM i).2.2 y hy j).trans (by linarith [hRi i])⟩
  have hF' : ∀ k i, IsTest (G k i).2.1 R (M i) := fun k i =>
    ⟨hR0, fun y => (hdom k i y).trans ((hF i).2.1 y), fun y hy j => (hF i).2.2 y (fun h0 => hy (by
      have h1 := hdom k i y
      rw [h0, abs_zero] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _)))) j⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = K * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hbound : ∀ k, |contSF hN Φ (G k) - contSF hN Φ F| ≤ δ k * A := fun k => by
    have h := hK F (G k) (fun _ => rfl) (hfield k) M (δ k) hF (hF' k) (hclose k)
    have hsum : K * ∑ a, δ k * ∏ i ∈ Finset.univ \ {a}, M i = δ k * A := by
      rw [hAdef, ← Finset.mul_sum]
      ring
    rwa [hsum] at h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) (g := fun k => δ k * A)
    (by simpa using hδ.mul_const A)
  rw [Real.dist_eq]
  exact hbound k

end Moments

/-! ## 2. The sector of all local fields -/

section AllSector

/-- **All local fields.** DERIVED: no numeral. -/
abbrev UF (N : ℕ) : Set (LField (MassGap.SUN.SU N)) := Set.univ

/-- DERIVED: `4` in `Fin 4` the spacetime dimension. -/
theorem uf_refl (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) : O.refl τ ∈ UF N ↔ O ∈ UF N :=
  iff_of_true trivial trivial

/-- DERIVED: no numeral. -/
theorem reg_uf_of_uc {P : Mono N} (h : ∀ i, UniformContinuous (P.2 i).2.1) : Reg (UF N) P :=
  fun i => ⟨trivial, h i⟩

/-- **A regular monomial of any class is regular for `UF`.** DERIVED: no numeral. -/
theorem reg_uf {D : Set (LField (MassGap.SUN.SU N))} {P : Mono N} (h : Reg D P) : Reg (UF N) P :=
  fun i => ⟨trivial, (h i).2⟩

/-- **`RegConnectedNonzero` at any class gives it at `UF`.** DERIVED: no numeral. -/
theorem regConnected_uf {hN : N ≠ 0} {Φ : Flow N} {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4}
    {r : ℝ} (h : RegConnectedNonzero hN Φ D τ r) : RegConnectedNonzero hN Φ (UF N) τ r := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨⟨Q.1, reg_uf Q.2⟩, hQ⟩

variable (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (hM : AllMom hN Φ)

include hB hM in
/-- **The reflection kernel is continuous in the translation of its second monomial.** DERIVED: `0`
the zero translation; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_kernF_shift_all (τ : Fin 4) {P Q : Mono N} (hP : Reg (UF N) P)
    (hQ : Reg (UF N) Q) :
    Tendsto (fun v : Fin 4 → ℝ => kernF hN Φ τ P (Mono.shift v Q)) (𝓝 0)
      (𝓝 (kernF hN Φ τ P Q)) := by
  have ht := tendsto_contSF_translate_all hN Φ hB hM (pairFam τ P Q)
    (fun x => (reg_pairFam uf_refl τ hP hQ x).2)
  have hc : Continuous (fun v : Fin 4 → ℝ => fun x : Fin P.1 ⊕ Fin Q.1 =>
      Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x) :=
    continuous_pi fun x => by
      cases x with
      | inl i => exact continuous_const
      | inr j => exact continuous_id
  have h0 : (fun x : Fin P.1 ⊕ Fin Q.1 => Sum.elim (fun _ => (0 : Fin 4 → ℝ))
      (fun _ => (0 : Fin 4 → ℝ)) x) = 0 := funext fun x => by cases x <;> rfl
  refine (ht.comp (hc.tendsto' 0 0 h0)).congr fun v => ?_
  exact congrArg (fun G => contSF hN Φ G) (pairFam_shift_right τ P Q v).symm

include hB hM in
/-- **OS1 for the reflection kernel, every local field.** DERIVED: `0` the time component; `4` in
`Fin 4` the spacetime dimension. -/
theorem kernF_shift_real_all (τ : Fin 4) {v : Fin 4 → ℝ} (hv : v τ = 0) {P Q : Mono N}
    (hP : Reg (UF N) P) (hQ : Reg (UF N) Q) :
    kernF hN Φ τ (Mono.shift v P) (Mono.shift v Q) = kernF hN Φ τ P Q := by
  unfold kernF
  rw [pairFam_shift_both τ hv]
  exact contSF_translate_real_all hN Φ hB hM (pairFam τ P Q)
    (fun x => (reg_pairFam uf_refl τ hP hQ x).2) v

variable (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)

include hM in
/-- **A real spatial translation preserves the form of the sector.** DERIVED: `0` the reference
step. -/
theorem form_aLin (x : spatial τ) (a b : RMono N (UF N) τ r →₀ ℝ) :
    (rTransfer hN Φ hB (UF N) τ hpp 0).toReflForm.form (rLin (UF N) r x a) (rLin (UF N) r x b)
      = (rTransfer hN Φ hB (UF N) τ hpp 0).toReflForm.form a b := by
  show gForm (rKern hN Φ τ)
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) a)
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) b)
    = gForm (rKern hN Φ τ) a b
  exact gForm_mapDomain_inv _ _
    (fun (P Q : RMono N (UF N) τ r) => kernF_shift_real_all hN Φ hB hM τ (spatial_time x) P.2 Q.2) a b

/-- **The real spatial translation of the sector of all local fields.** DERIVED: no numeral. -/
def aU (x : spatial τ) : RH hN Φ hB (UF N) τ hpp →L[ℂ] RH hN Φ hB (UF N) τ hpp :=
  opS (form_aLin hN Φ hB hM τ hpp x)

/-- DERIVED: no numeral. -/
theorem inner_aU (x : spatial τ) (y z : RH hN Φ hB (UF N) τ hpp) :
    inner ℂ (aU hN Φ hB hM τ hpp x y) (aU hN Φ hB hM τ hpp x z) = inner ℂ y z :=
  inner_opS _ y z

/-- **The group law.** DERIVED: no numeral. -/
theorem aU_add (x y : spatial τ) :
    aU hN Φ hB hM τ hpp (x + y) = aU hN Φ hB hM τ hpp x * aU hN Φ hB hM τ hpp y := by
  unfold aU
  refine (opS_mul _ _ _ fun c => ?_).symm
  show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x))
      (Finsupp.mapDomain (rShift (y : Fin 4 → ℝ) (spatial_time y)) c)
    = Finsupp.mapDomain (rShift ((x + y : spatial τ) : Fin 4 → ℝ) (spatial_time (x + y))) c
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  refine Subtype.ext (Subtype.ext ?_)
  show Mono.shift (x : Fin 4 → ℝ) (Mono.shift (y : Fin 4 → ℝ) P.1.1)
    = Mono.shift ((x : Fin 4 → ℝ) + y) P.1.1
  rw [Mono.shift_shift, add_comm]

/-- DERIVED: `0` the zero vector; `1` the identity. -/
theorem aU_zero : aU hN Φ hB hM τ hpp 0 = 1 := by
  unfold aU
  refine opS_eq_one _ fun c => ?_
  show Finsupp.mapDomain (rShift ((0 : spatial τ) : Fin 4 → ℝ) (spatial_time (0 : spatial τ))) c = c
  have h : rShift ((0 : spatial τ) : Fin 4 → ℝ) (spatial_time (0 : spatial τ))
      = (id : RMono N (UF N) τ r → RMono N (UF N) τ r) :=
    funext fun P => Subtype.ext (Subtype.ext (Mono.shift_zero P.1.1))
  rw [h, Finsupp.mapDomain_id]

/-- **It fixes the vacuum.** DERIVED: `1` the vacuum coefficient; `0` the number of factors. -/
theorem aU_vac (x : spatial τ) :
    aU hN Φ hB hM τ hpp x (rVac hN Φ hB (UF N) τ hpp) = rVac hN Φ hB (UF N) τ hpp := by
  unfold aU rVac
  refine opS_Omega _ ?_
  show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x))
      (Finsupp.single (rEmpty N (UF N) τ r) 1) = Finsupp.single (rEmpty N (UF N) τ r) 1
  rw [Finsupp.mapDomain_single]
  congr 1
  exact Subtype.ext (Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0)))

/-- **It commutes with every step.** DERIVED: `1` the unit step. -/
theorem commute_aU_rStep (x : spatial τ) (m : ℕ) :
    Commute (aU hN Φ hB hM τ hpp x) (rStep hN Φ hB (UF N) τ hpp m) := by
  unfold aU rStep
  exact opS_commute_opT (rTransfer hN Φ hB (UF N) τ hpp m)
    (form_aLin hN Φ hB hM τ hpp x) fun c => by
      show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x))
          (Finsupp.mapDomain (rTime hN τ m) c)
        = Finsupp.mapDomain (rTime hN τ m)
          (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) c)
      rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      congr 1
      funext P
      refine Subtype.ext (Subtype.ext ?_)
      show Mono.shift (x : Fin 4 → ℝ) (Mono.shift (timeVec N m τ 1) P.1.1)
        = Mono.shift (timeVec N m τ 1) (Mono.shift (x : Fin 4 → ℝ) P.1.1)
      rw [Mono.shift_shift, Mono.shift_shift, add_comm]

include hM in
/-- **The form against the translate tends to the form.** DERIVED: `0` the zero translation and the
reference step. -/
theorem tendsto_form_aLin (a : RMono N (UF N) τ r →₀ ℝ) :
    Tendsto (fun x : spatial τ =>
        (rTransfer hN Φ hB (UF N) τ hpp 0).toReflForm.form a (rLin (UF N) r x a)) (𝓝 0)
      (𝓝 ((rTransfer hN Φ hB (UF N) τ hpp 0).toReflForm.form a a)) := by
  show Tendsto (fun x : spatial τ => gForm (rKern hN Φ τ) a
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) a)) (𝓝 0)
    (𝓝 (gForm (rKern hN Φ τ) a a))
  simp only [gForm_mapDomain_right]
  unfold gForm
  simp only [Finsupp.sum]
  refine tendsto_finset_sum _ fun P _ => tendsto_finset_sum _ fun Q _ => tendsto_const_nhds.mul ?_
  exact (tendsto_kernF_shift_all hN Φ hB hM τ P.2 Q.2).comp
    (continuous_subtype_val.tendsto' (0 : spatial τ) 0 rfl)

/-- **Strong continuity at the identity.** DERIVED: `0` the zero translation. -/
theorem tendsto_aU (y : RH hN Φ hB (UF N) τ hpp) :
    Tendsto (fun x : spatial τ => aU hN Φ hB hM τ hpp x y) (𝓝 0) (𝓝 y) :=
  tendsto_opS_of_coe (fun x => form_aLin hN Φ hB hM τ hpp x)
    (fun z => tendsto_opS_coe (fun x => form_aLin hN Φ hB hM τ hpp x) z
      (tendsto_form_aLin hN Φ hB hM τ hpp _) (tendsto_form_aLin hN Φ hB hM τ hpp _)) y

/-- **Strong continuity.** DERIVED: no numeral. -/
theorem continuous_aU (y : RH hN Φ hB (UF N) τ hpp) :
    Continuous (fun x : spatial τ => aU hN Φ hB hM τ hpp x y) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have h1 : Tendsto (fun x : spatial τ => x - x0) (𝓝 x0) (𝓝 0) :=
    (continuous_id.sub continuous_const).tendsto' x0 0 (sub_self x0)
  have h2 := ((aU hN Φ hB hM τ hpp x0).continuous.tendsto y).comp
    ((tendsto_aU hN Φ hB hM τ hpp y).comp h1)
  unfold ContinuousAt
  refine h2.congr fun x => ?_
  show aU hN Φ hB hM τ hpp x0 (aU hN Φ hB hM τ hpp (x - x0) y) = aU hN Φ hB hM τ hpp x y
  rw [← ContinuousLinearMap.mul_apply, ← aU_add, show x0 + (x - x0) = x by abel]

/-- **`J` carries the dyadic translation to `spT`.** DERIVED: `0` the time component. -/
theorem J_aU_dyadic (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (y : RH hN Φ hB (UF N) τ hpp) :
    J hN Φ hB (UF N) τ hpp
        (aU hN Φ hB hM τ hpp ⟨site (dySpacing N m) n, mem_spatial (site_time_zero _ hn)⟩ y)
      = spT hN Φ hB τ hpp m n hn (J hN Φ hB (UF N) τ hpp y) := by
  unfold J aU spT
  refine opJ_opS _ _ _ (fun c => ?_) y
  show Finsupp.mapDomain Subtype.val
      (Finsupp.mapDomain (rShift (site (dySpacing N m) n) (site_time_zero _ hn)) c)
    = Finsupp.mapDomain (spShift τ m n hn) (Finsupp.mapDomain Subtype.val c)
  have hf : (Subtype.val : RMono N (UF N) τ r → MarginMono N τ r)
      ∘ rShift (site (dySpacing N m) n) (site_time_zero _ hn) = spShift τ m n hn ∘ Subtype.val := rfl
  rw [← Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_comp]

omit hM in
/-- **The range projection commutes with the reference step.** DERIVED: `0` the reference step. -/
theorem commute_proj_stepT (A : Set (LField (MassGap.SUN.SU N))) :
    Commute ((J hN Φ hB A τ hpp).comp (Jd hN Φ hB A τ hpp)) (stepT hN Φ hB τ hpp 0) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  rw [Jd_step, ← J_step]

omit hM in
/-- **So does it with every time.** DERIVED: `0` the reference step. -/
theorem commute_proj_timeT (A : Set (LField (MassGap.SUN.SU N))) (t : ℝ) :
    Commute ((J hN Φ hB A τ hpp).comp (Jd hN Φ hB A τ hpp)) (timeT hN Φ hB τ hpp t) :=
  (Commute.cfc_real (commute_proj_stepT hN Φ hB τ hpp A).symm
    (fun s : ℝ => s ^ (t / dySpacing N 0))).symm

/-- **The extension of `aU` to `FlowH`**, used only to commute it with the times: the identity on the
complement. DERIVED: `1` the identity. -/
def aT (x : spatial τ) : FlowH hN Φ hB τ hpp →L[ℂ] FlowH hN Φ hB τ hpp :=
  (J hN Φ hB (UF N) τ hpp).comp ((aU hN Φ hB hM τ hpp x).comp (Jd hN Φ hB (UF N) τ hpp))
    + (1 - (J hN Φ hB (UF N) τ hpp).comp (Jd hN Φ hB (UF N) τ hpp))

/-- DERIVED: no numeral. -/
theorem aT_apply (x : spatial τ) (z : FlowH hN Φ hB τ hpp) :
    aT hN Φ hB hM τ hpp x z = J hN Φ hB (UF N) τ hpp (aU hN Φ hB hM τ hpp x
        (Jd hN Φ hB (UF N) τ hpp z))
      + (z - J hN Φ hB (UF N) τ hpp (Jd hN Φ hB (UF N) τ hpp z)) := rfl

/-- DERIVED: no numeral. -/
theorem aU_rStep_apply (x : spatial τ) (m : ℕ) (y : RH hN Φ hB (UF N) τ hpp) :
    aU hN Φ hB hM τ hpp x (rStep hN Φ hB (UF N) τ hpp m y)
      = rStep hN Φ hB (UF N) τ hpp m (aU hN Φ hB hM τ hpp x y) := by
  have h := congrArg (fun F => F y) (commute_aU_rStep hN Φ hB hM τ hpp x m).eq
  simp only [ContinuousLinearMap.mul_apply] at h
  exact h

/-- DERIVED: no numeral. -/
theorem commute_aT_stepT (x : spatial τ) (m : ℕ) :
    Commute (aT hN Φ hB hM τ hpp x) (stepT hN Φ hB τ hpp m) := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, aT_apply, aT_apply,
    Jd_step, aU_rStep_apply, ← J_step, ← J_step, map_add, map_sub]

/-- DERIVED: `0` the reference step. -/
theorem commute_aT_timeT (x : spatial τ) (t : ℝ) :
    Commute (aT hN Φ hB hM τ hpp x) (timeT hN Φ hB τ hpp t) :=
  (Commute.cfc_real (commute_aT_stepT hN Φ hB hM τ hpp x 0).symm
    (fun s : ℝ => s ^ (t / dySpacing N 0))).symm

/-- `aT` on the range of `J` is `aU`. DERIVED: `0` the vanishing remainder. -/
theorem aT_J (x : spatial τ) (y : RH hN Φ hB (UF N) τ hpp) :
    aT hN Φ hB hM τ hpp x (J hN Φ hB (UF N) τ hpp y)
      = J hN Φ hB (UF N) τ hpp (aU hN Φ hB hM τ hpp x y) := by
  rw [aT_apply, JdJ, sub_self, add_zero]

/-- **The time of the sector.** DERIVED: no numeral. -/
def aTime (t : ℝ) : RH hN Φ hB (UF N) τ hpp →L[ℂ] RH hN Φ hB (UF N) τ hpp :=
  (Jd hN Φ hB (UF N) τ hpp).comp ((timeT hN Φ hB τ hpp t).comp (J hN Φ hB (UF N) τ hpp))

omit hM in
/-- DERIVED: no numeral. -/
theorem J_aTime (t : ℝ) (y : RH hN Φ hB (UF N) τ hpp) :
    J hN Φ hB (UF N) τ hpp (aTime hN Φ hB τ hpp t y)
      = timeT hN Φ hB τ hpp t (J hN Φ hB (UF N) τ hpp y) := by
  have h := congrArg (fun F => F (J hN Φ hB (UF N) τ hpp y))
    (commute_proj_timeT hN Φ hB τ hpp (UF N) t).eq
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, JdJ] at h
  exact h

/-- **`aU` commutes with the time of the sector.** DERIVED: no numeral. -/
theorem commute_aU_aTime (x : spatial τ) (t : ℝ) :
    Commute (aU hN Φ hB hM τ hpp x) (aTime hN Φ hB τ hpp t) := by
  refine ContinuousLinearMap.ext fun y => ?_
  have hinj : ∀ {a b : RH hN Φ hB (UF N) τ hpp},
      J hN Φ hB (UF N) τ hpp a = J hN Φ hB (UF N) τ hpp b → a = b := fun {a b} h => by
    rw [← JdJ hN Φ hB (UF N) τ hpp a, ← JdJ hN Φ hB (UF N) τ hpp b, h]
  refine hinj ?_
  have hc := congrArg (fun F => F (J hN Φ hB (UF N) τ hpp y))
    (commute_aT_timeT hN Φ hB hM τ hpp x t).eq
  simp only [ContinuousLinearMap.mul_apply] at hc ⊢
  rw [← aT_J hN Φ hB hM τ hpp, J_aTime, J_aTime, ← aT_J hN Φ hB hM τ hpp]
  exact hc

end AllSector

/-! ## 3. Non-triviality: the iff, the source of `hNT`, the dichotomy -/

section Connected

variable {M : Type} (D : Transfer.TransferData (M →₀ ℝ)) (K : M → M → ℝ)
  (hD : ∀ c d, D.form c d = gForm K c d) (e : M) (hv : D.vac = Finsupp.single e 1)

include hD in
/-- **A vector whose connected reading vanishes is on the vacuum line.** DERIVED: `1` the coefficient;
`2` the square; `0` the vanishing norm. -/
theorem gVec_eq_of_connected {Q : M} (hee : K e e = 1) (hK : K e Q = K Q e)
    (h : K Q Q - K e Q ^ 2 = 0) : gVec D Q = (K e Q : ℂ) • gVec D e := by
  have hin := inner_gVec D K hD
  have h0 : ‖gVec D Q - (K e Q : ℂ) • gVec D e‖ ^ 2 = 0 := by
    have e1 : ‖gVec D Q - (K e Q : ℂ) • gVec D e‖ ^ 2
        = K Q Q - 2 * (K e Q * K Q e) + K e Q ^ 2 * K e e := by
      have n1 : ∀ A : M, ‖gVec D A‖ ^ 2 = K A A := fun A => by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ), hin]
        exact Complex.ofReal_re _
      rw [norm_sub_sq (𝕜 := ℂ), norm_smul, mul_pow, inner_smul_right, hin, n1, n1, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, ← Complex.ofReal_mul]
      have e3 : RCLike.re ((K e Q * K Q e : ℝ) : ℂ) = K e Q * K Q e := Complex.ofReal_re _
      rw [e3]
    rw [e1, hee, ← hK]
    linarith
  have h1 : gVec D Q - (K e Q : ℂ) • gVec D e = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  exact sub_eq_zero.mp h1

include hD hv in
/-- **Non-triviality of a GNS space is a connected reading.** A non-zero vector orthogonal to the
vacuum exists exactly when some generator has a non-zero connected reading. DERIVED: `0` the vanishing
pairing, the zero vector; `1` the coefficient; `2` the square. -/
theorem exists_orth_iff (hee : K e e = 1) (hK : ∀ P Q, K P Q = K Q P) :
    (∃ u : GNSHilbert.H D.toReflForm,
        inner ℂ (GNSHilbert.Omega D.toReflForm D.vac) u = (0 : ℂ) ∧ u ≠ 0)
      ↔ ∃ Q, K Q Q - K e Q ^ 2 ≠ 0 := by
  constructor
  · rintro ⟨u, hu, hu0⟩
    by_contra hall
    push_neg at hall
    have hO : gVec D e = GNSHilbert.Omega D.toReflForm D.vac := by
      unfold gVec GNSHilbert.Omega
      rw [hv]
    obtain ⟨S, hS⟩ : ∃ S : Submodule ℂ (GNSHilbert.H D.toReflForm),
        S = Submodule.span ℂ {gVec D e} := ⟨_, rfl⟩
    have hcl : IsClosed (S : Set (GNSHilbert.H D.toReflForm)) := by
      rw [hS]
      exact Submodule.closed_of_finiteDimensional _
    have hle : Submodule.span ℂ (Set.range fun a : M => gVec D a) ≤ S := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨Q, rfl⟩
      show gVec D Q ∈ S
      rw [gVec_eq_of_connected D K hD e hee (hK e Q) (hall Q), hS]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hdense := MassGap.ClayStatement.span_single_dense D.toReflForm
    have htop : (⊤ : Submodule ℂ (GNSHilbert.H D.toReflForm)) ≤ S := by
      have h2 := Submodule.topologicalClosure_minimal _ hle hcl
      rw [← hdense]
      exact h2
    have hmem : u ∈ S := htop trivial
    rw [hS, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    have hvv : inner ℂ (GNSHilbert.Omega D.toReflForm D.vac)
        (GNSHilbert.Omega D.toReflForm D.vac) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, GNSHilbert.norm_Omega_vac]
      simp
    rw [inner_smul_right, ← hO, hO, hvv, mul_one] at hu
    exact hu0 (by rw [hu, zero_smul])
  · rintro ⟨Q, hQ⟩
    refine ContinuumSep.exists_orth_ne_zero D (Finsupp.single Q 1) ?_
    rw [hD, hD, hv, gForm_single, gForm_single]
    simp only [one_mul]
    rw [hK Q e]
    exact hQ

variable {N : ℕ} (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
  (hpp : Φ.PosPreserving τ r)

/-- **`FlowConnectedNonzero` says exactly that `FlowH` is more than the vacuum line.** DERIVED: `0` the
vanishing pairing and the zero vector; `2` the square. -/
theorem flowConnected_iff :
    FlowConnectedNonzero hN Φ τ r
      ↔ ∃ u : FlowH hN Φ hB τ hpp, inner ℂ (vacT hN Φ hB τ hpp) u = 0 ∧ u ≠ 0 :=
  (exists_orth_iff (flowTransfer hN Φ hB τ hpp 0) (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
    (fun _ _ => rfl) (emptyMargin N τ r) rfl (kernF_empty hN Φ τ r)
    (fun P Q => kernF_symm hN Φ τ P.1 Q.1)).symm

/-- **`RegConnectedNonzero` says exactly that `RH` is more than the vacuum line.** DERIVED: `0` the
vanishing pairing and the zero vector; `2` the square. -/
theorem regConnected_iff (A : Set (LField (MassGap.SUN.SU N))) :
    RegConnectedNonzero hN Φ A τ r
      ↔ ∃ u : RH hN Φ hB A τ hpp, inner ℂ (rVac hN Φ hB A τ hpp) u = 0 ∧ u ≠ 0 :=
  (exists_orth_iff (rTransfer hN Φ hB A τ hpp 0) (rKern hN Φ τ) (fun _ _ => rfl)
    (rEmpty N A τ r) rfl (kernF_empty hN Φ τ r) (fun P Q => kernF_symm hN Φ τ P.1.1 Q.1.1)).symm

include hB hpp in
/-- **The dichotomy of the regular sector**: either `RegConnectedNonzero`, or every regular reflected
reading factorises. DERIVED: `0`, `1`, `2` as in `gVec_eq_of_connected`. -/
theorem not_regConnected_iff (A : Set (LField (MassGap.SUN.SU N))) :
    ¬ RegConnectedNonzero hN Φ A τ r
      ↔ ∀ P Q : RMono N A τ r, kernF hN Φ τ P.1.1 Q.1.1
          = kernF hN Φ τ (emptyMargin N τ r).1 P.1.1 * kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 := by
  constructor
  · intro h P Q
    have hall : ∀ Q : RMono N A τ r,
        kernF hN Φ τ Q.1.1 Q.1.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 ^ 2 = 0 := fun Q => by
      by_contra hQ
      exact h ⟨Q, hQ⟩
    have hgv := fun Q : RMono N A τ r =>
      gVec_eq_of_connected (rTransfer hN Φ hB A τ hpp 0) (rKern hN Φ τ) (fun _ _ => rfl)
        (rEmpty N A τ r) (kernF_empty hN Φ τ r) (kernF_symm hN Φ τ _ _) (hall Q)
    have hin := inner_gVec (rTransfer hN Φ hB A τ hpp 0) (rKern hN Φ τ) (fun _ _ => rfl)
    have h1 := hin P Q
    rw [hgv P, hgv Q, inner_smul_left, inner_smul_right, hin] at h1
    have he : rKern hN Φ τ (rEmpty N A τ r) (rEmpty N A τ r) = 1 := kernF_empty hN Φ τ r
    rw [he] at h1
    have h2 : ((rKern hN Φ τ (rEmpty N A τ r) P : ℝ) * (rKern hN Φ τ (rEmpty N A τ r) Q : ℝ) : ℂ)
        = (rKern hN Φ τ P Q : ℝ) := by
      simpa using h1
    have h3 : rKern hN Φ τ (rEmpty N A τ r) P * rKern hN Φ τ (rEmpty N A τ r) Q
        = rKern hN Φ τ P Q := by
      exact_mod_cast h2
    exact h3.symm
  · rintro h ⟨Q, hQ⟩
    apply hQ
    rw [h Q Q]
    ring

/-- **A connected cross reading with any vector gives `RegConnectedNonzero`.** A vector `z` of `FlowH`
whose pairing with a regular `Q` does not factorise through the vacuum, such as a composite's vector,
makes the regular sector non-trivial. DERIVED: `0` the vanishing connected reading; `1` the unit
vacuum. -/
theorem regConnected_of_cross (A : Set (LField (MassGap.SUN.SU N))) (z : FlowH hN Φ hB τ hpp)
    (Q : RMono N A τ r)
    (h : inner ℂ z (gvecT hN Φ hB τ hpp Q.1)
      ≠ inner ℂ z (vacT hN Φ hB τ hpp) * inner ℂ (vacT hN Φ hB τ hpp) (gvecT hN Φ hB τ hpp Q.1)) :
    RegConnectedNonzero hN Φ A τ r := by
  by_contra hn
  have hall : kernF hN Φ τ Q.1.1 Q.1.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 ^ 2 = 0 := by
    by_contra hQ
    exact hn ⟨Q, hQ⟩
  have hg : gvecT hN Φ hB τ hpp Q.1
      = (kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 : ℂ) • vacT hN Φ hB τ hpp :=
    gVec_eq_of_connected (flowTransfer hN Φ hB τ hpp 0)
      (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (fun _ _ => rfl) (emptyMargin N τ r)
      (kernF_empty hN Φ τ r) (kernF_symm hN Φ τ _ _) hall
  have hvv : inner ℂ (vacT hN Φ hB τ hpp) (vacT hN Φ hB τ hpp) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    have : ‖vacT hN Φ hB τ hpp‖ = 1 := GNSHilbert.norm_Omega_vac _
    rw [this]
    simp
  apply h
  rw [hg, inner_smul_right, inner_smul_right, hvv, mul_one, mul_comm]

include hB in
/-- **`RegConnectedNonzero` from a lattice lower bound at one regular monomial.** By `exists_lip_connected`
the monomial can be taken Lipschitz. DERIVED: `0` the excluded value and the sign of `c`; `2` the
square. -/
theorem regConnected_of_lattice (A : Set (LField (MassGap.SUN.SU N))) (Q : RMono N A τ r) {c : ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ k in atTop, c ≤ |latSF hN Φ k (pairFam τ Q.1.1 Q.1.1)
      - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 Q.1.1) ^ 2|) :
    RegConnectedNonzero hN Φ A τ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have h1 := tendsto_contSF hN Φ hB (pairFam τ Q.1.1 Q.1.1)
  have h2 := tendsto_contSF hN Φ hB (pairFam τ (emptyMargin N τ r).1 Q.1.1)
  have hle := ge_of_tendsto (h1.sub (h2.pow 2)).abs (h.filter_mono ultra_le)
  refine ⟨Q, fun h0 => ?_⟩
  have e : contSF hN Φ (pairFam τ Q.1.1 Q.1.1)
      - contSF hN Φ (pairFam τ (emptyMargin N τ r).1 Q.1.1) ^ 2 = 0 := h0
  rw [e, abs_zero] at hle
  linarith

/-- **A class of zero fields has no regular connected reading**, though `hD`, `hpos` and `hcube` all
hold for it. So `RegConnectedNonzero` at `D` does not follow from those three, whatever `W`. DERIVED:
`0` the zero field, the vanishing reading; `1` the empty reading; `2` the square. -/
theorem not_regConnected_of_zero (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (h0 : ∀ O ∈ D, O.1 = 0) : ¬ RegConnectedNonzero hN (energy0 W D hD) D τ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hzero : ∀ {ι : Type} [Fintype ι] (G : ι → SField N) (i : ι), (G i).1 ∈ D →
      contSF hN (energy0 W D hD) G = 0 := by
    intro ι _ G i hi
    have hk : ∀ k, latSF hN (energy0 W D hD) k G = 0 := fun k => by
      show stateK hN k (∏ i, smear (dySpacing N k) ((energy0 W D hD).map k (G i).1).1 (G i).2) = 0
      have hm : ((energy0 W D hD).map k (G i).1).1 = 0 := by
        rw [energy0, energyOn_map_of_mem W hD (s0_refl N) hi k]
        have h1 : (W.fieldMap k (G i).1).1 = 0 := by
          show (G i).1.1.comp _ = 0
          rw [h0 _ hi]
          rfl
        rw [h1]
        simp [s0]
      have hs : smear (dySpacing N k) ((energy0 W D hD).map k (G i).1).1 (G i).2 = 0 := by
        rw [hm]
        unfold smear
        simp
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hs]
      exact (stateK hN k).map_zero
    show limUnder _ _ = (0 : ℝ)
    rw [show (fun k => latSF hN (energy0 W D hD) k G) = fun _ => (0 : ℝ) from funext hk]
    exact tendsto_const_nhds.limUnder_eq
  rintro ⟨⟨⟨⟨n, a⟩, hm⟩, hr⟩, hQ⟩
  cases n with
  | zero =>
    apply hQ
    have e : (⟨0, a⟩ : Mono N) = (emptyMargin N τ r).1 :=
      congrArg (Sigma.mk 0) (funext fun i => i.elim0)
    show kernF hN (energy0 W D hD) τ ⟨0, a⟩ ⟨0, a⟩
      - kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 ⟨0, a⟩ ^ 2 = 0
    rw [e, kernF_empty]
    ring
  | succ n =>
    apply hQ
    have h1 : kernF hN (energy0 W D hD) τ ⟨n + 1, a⟩ ⟨n + 1, a⟩ = 0 :=
      hzero (pairFam τ ⟨n + 1, a⟩ ⟨n + 1, a⟩) (Sum.inr 0) (hr 0).1
    have h2 : kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 ⟨n + 1, a⟩ = 0 :=
      hzero (pairFam τ (emptyMargin N τ r).1 ⟨n + 1, a⟩) (Sum.inr 0) (hr 0).1
    show kernF hN (energy0 W D hD) τ ⟨n + 1, a⟩ ⟨n + 1, a⟩
      - kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 ⟨n + 1, a⟩ ^ 2 = 0
    rw [h1, h2]
    ring

end Connected

/-! ## 4. What the sector holds -/

section Holds

variable (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
  (hpp : Φ.PosPreserving τ r) (A : Set (LField (MassGap.SUN.SU N)))

/-- DERIVED: `2` the square. -/
theorem norm_J (y : RH hN Φ hB A τ hpp) : ‖J hN Φ hB A τ hpp y‖ = ‖y‖ := by
  have h : ‖J hN Φ hB A τ hpp y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_J]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The sector is a closed subspace.** DERIVED: no numeral. -/
theorem isClosed_range_J : IsClosed (Set.range (J hN Φ hB A τ hpp)) :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_J hN Φ hB τ hpp A)).isClosedEmbedding.isClosed_range

/-- **A regular monomial's vector lies in the sector.** DERIVED: no numeral. -/
theorem gvecT_mem_range (Q : RMono N A τ r) :
    gvecT hN Φ hB τ hpp Q.1 ∈ Set.range (J hN Φ hB A τ hpp) :=
  ⟨gVec (rTransfer hN Φ hB A τ hpp 0) Q, MassGap.DiniHolder.J_gVec hN Φ hB A τ hpp Q⟩

/-- **The sector is all of `FlowH` exactly when it holds every margin monomial's vector.** With
`A = UF N` the fields play no part: this is a statement about the test functions alone.
DERIVED: `0` the reference step. -/
theorem range_J_eq_univ_iff :
    Set.range (J hN Φ hB A τ hpp) = Set.univ
      ↔ ∀ Q : MarginMono N τ r, gvecT hN Φ hB τ hpp Q ∈ Set.range (J hN Φ hB A τ hpp) := by
  constructor
  · intro h Q
    rw [h]
    exact Set.mem_univ _
  · intro h
    have hle : Submodule.span ℂ (Set.range fun Q : MarginMono N τ r =>
        gVec (flowTransfer hN Φ hB τ hpp 0) Q)
        ≤ LinearMap.range (J hN Φ hB A τ hpp).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨Q, rfl⟩
      obtain ⟨y, hy⟩ := h Q
      exact ⟨y, hy⟩
    have hcl : IsClosed ((LinearMap.range (J hN Φ hB A τ hpp).toLinearMap :
        Submodule ℂ (FlowH hN Φ hB τ hpp)) : Set (FlowH hN Φ hB τ hpp)) := by
      have e : ((LinearMap.range (J hN Φ hB A τ hpp).toLinearMap :
          Submodule ℂ (FlowH hN Φ hB τ hpp)) : Set (FlowH hN Φ hB τ hpp))
          = Set.range (J hN Φ hB A τ hpp) := rfl
      rw [e]
      exact isClosed_range_J hN Φ hB τ hpp A
    have htop := Submodule.topologicalClosure_minimal _ hle hcl
    rw [show (Submodule.span ℂ (Set.range fun Q : MarginMono N τ r =>
        gVec (flowTransfer hN Φ hB τ hpp 0) Q)).topologicalClosure = ⊤ from
      MassGap.ClayStatement.span_single_dense _] at htop
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨y, hy⟩ := htop (Submodule.mem_top (x := z))
    exact ⟨y, hy⟩

/-- **The Schwinger functions read test functions only at the sites.** DERIVED: no numeral. -/
theorem contSF_congr_sample {ι : Type} [Fintype ι] (F F' : ι → SField N)
    (hfield : ∀ i, (F' i).1 = (F i).1)
    (hs : ∀ i k x, (F' i).2.1 (site (dySpacing N k) x) = (F i).2.1 (site (dySpacing N k) x)) :
    contSF hN Φ F' = contSF hN Φ F := by
  unfold contSF
  refine congrArg _ (funext fun k => ?_)
  show stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (F' i).1).1 (F' i).2)
    = stateK hN k (∏ i, smear (dySpacing N k) (Φ.map k (F i).1).1 (F i).2)
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  rw [hfield i]
  unfold smear
  refine finsum_congr fun x => ?_
  rw [hs]

/-- **All the sites of all the steps.** DERIVED: no numeral. -/
def sampleSet (N : ℕ) : Set (Fin 4 → ℝ) := ⋃ k : ℕ, Set.range (site (dySpacing N k))

/-- DERIVED: `0` the null measure. -/
theorem sampleSet_null (N : ℕ) : volume (sampleSet N) = 0 :=
  (Set.countable_iUnion fun _ => Set.countable_range _).measure_zero _

/-- DERIVED: no numeral. -/
theorem site_mem_sampleSet (k : ℕ) (x : ISite) : site (dySpacing N k) x ∈ sampleSet N :=
  Set.mem_iUnion.mpr ⟨k, x, rfl⟩

/-- **The copy of a test function on the sites**, zero elsewhere. DERIVED: `0` the value off the
sites. -/
def sampleCopy (N : ℕ) (f : TestFn) : TestFn :=
  ⟨(sampleSet N).indicator f.1, by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    refine ⟨R, M, hR, fun y => ?_, fun y hy => ?_⟩
    · by_cases h : y ∈ sampleSet N
      · rw [Set.indicator_of_mem h]; exact hM y
      · rw [Set.indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hM y)
    · exact hs y fun h0 => hy (by
        by_cases h : y ∈ sampleSet N
        · rw [Set.indicator_of_mem h, h0]
        · rw [Set.indicator_of_notMem h])⟩

/-- DERIVED: `0` the null set. -/
theorem sampleCopy_ae_zero (f : TestFn) : ∀ᵐ y, (sampleCopy N f).1 y = 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (sampleSet_null N)
  by_contra h
  exact hy (Set.indicator_of_notMem h _)

/-- **No `L¹` norm of Lebesgue measure can carry the reading.** `sampleCopy` is zero almost everywhere
and every Schwinger function reads it as the original test function. DERIVED: no numeral. -/
theorem contSF_sampleCopy {ι : Type} [Fintype ι] (F : ι → SField N) :
    contSF hN Φ (fun i => ((F i).1, sampleCopy N (F i).2)) = contSF hN Φ F :=
  contSF_congr_sample hN Φ F _ (fun _ => rfl) fun i k x =>
    Set.indicator_of_mem (site_mem_sampleSet k x) _

end Holds

/-! ## 5. The cut-offs and Schwartz functions are regular -/

section Decay

/-- **A product of bounded uniformly continuous functions is uniformly continuous.** DERIVED: `0` the
signs; `1` keeps the bounds positive; `4` splits the error into a part below `ε`. -/
theorem uc_mul {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) {A B : ℝ} (hA : ∀ y, |f y| ≤ A) (hB : ∀ y, |g y| ≤ B) :
    UniformContinuous fun y => f y * g y := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = |A| + 1 := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = |B| + 1 := ⟨_, rfl⟩
  have hA0 : 0 < A' := by rw [hA']; positivity
  have hB0 : 0 < B' := by rw [hB']; positivity
  obtain ⟨d1, hd1, h1⟩ := Metric.uniformContinuous_iff.mp hf (ε / (4 * B')) (by positivity)
  obtain ⟨d2, hd2, h2⟩ := Metric.uniformContinuous_iff.mp hg (ε / (4 * A')) (by positivity)
  refine ⟨min d1 d2, lt_min hd1 hd2, fun {a b} hab => ?_⟩
  have h3 := h1 (hab.trans_le (min_le_left _ _))
  have h4 := h2 (hab.trans_le (min_le_right _ _))
  rw [Real.dist_eq] at h3 h4 ⊢
  have e : f a * g a - f b * g b = (f a - f b) * g a + f b * (g a - g b) := by ring
  have hg1 : |g a| ≤ B' := (hB a).trans (by rw [hB']; linarith [le_abs_self B])
  have hf1 : |f b| ≤ A' := (hA b).trans (by rw [hA']; linarith [le_abs_self A])
  have h5 : |f a - f b| * |g a| ≤ ε / (4 * B') * B' :=
    mul_le_mul h3.le hg1 (abs_nonneg _) (by positivity)
  have h6 : |f b| * |g a - g b| ≤ A' * (ε / (4 * A')) :=
    mul_le_mul hf1 h4.le (abs_nonneg _) hA0.le
  have e1 : ε / (4 * B') * B' = ε / 4 := by field_simp
  have e2 : A' * (ε / (4 * A')) = ε / 4 := by field_simp
  rw [e]
  have h7 : |(f a - f b) * g a + f b * (g a - g b)| ≤ |f a - f b| * |g a| + |f b| * |g a - g b| := by
    rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rw [e1] at h5
  rw [e2] at h6
  linarith

open MassGap.ObserverOSSchwartz MassGap.ObserverOSEuclidS MassGap.ObserverOSTempered
  MassGap.ObserverOSLinked

/-- DERIVED: `0` the lower value; `1` the upper value. -/
theorem abs_chi_le (R : ℕ) (y : Fin 4 → ℝ) : |chi R y| ≤ 1 := by
  rw [abs_of_nonneg (chi_nonneg R y)]
  exact chi_le_one R y

/-- **The cut-off is Lipschitz.** DERIVED: `0`, `1` the clamp. -/
theorem uc_chi (R : ℕ) : UniformContinuous (chi R) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε, hε, fun {a b} hab => ?_⟩
  rw [Real.dist_eq]
  unfold chi
  rw [max_comm (0 : ℝ), max_comm (0 : ℝ)]
  refine (abs_max_sub_max_le_abs _ _ _).trans_lt ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans_lt ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  have e : (R : ℝ) + 1 - ‖a‖ - ((R : ℝ) + 1 - ‖b‖) = ‖b‖ - ‖a‖ := by ring
  rw [e, abs_sub_comm]
  exact (abs_norm_sub_norm_le a b).trans_lt (by rwa [← dist_eq_norm])

/-- **A cut-off of a uniformly continuous decaying function is uniformly continuous.** DERIVED: `1` the
bound of `chi`. -/
theorem uc_cut (g : Decaying) (R : ℕ) (hg : UniformContinuous g.1) :
    UniformContinuous (cut g R).1 := by
  obtain ⟨B, hB⟩ := g.2
  exact uc_mul (uc_chi R) hg (abs_chi_le R) (hB := fun y => hB.abs_le y)

/-- **A Schwartz function is uniformly continuous.** DERIVED: `2` the Euclidean exponent. -/
theorem uc_ofE4 (φ : MassGap.WightmanData.TestFn) : UniformContinuous (ofE4 φ).1 :=
  (ZeroAtInftyContinuousMap.uniformContinuous φ.toZeroAtInfty).comp
    (PiLp.uniformContinuous_toLp 2 fun _ : Fin 4 => ℝ)

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

/-- **The vector of a decaying monomial with uniformly continuous functions lies in the sector.**
It is the limit of its cut-offs, which are regular, and the sector is closed. DERIVED: no numeral. -/
theorem vecD_mem_range {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (A : Set (LField (MassGap.SUN.SU N)))
    (P : DMarginMonoD N D τ r) (hA : ∀ i, (P.1.1.2 i).1 ∈ A)
    (hP : ∀ i, UniformContinuous (P.1.1.2 i).2.1) :
    vecD hN W hD hpos hcube τ hphys P ∈ Set.range (J hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) A τ
      (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) :=
  (isClosed_range_J hN _ _ τ _ A).mem_of_tendsto (tendsto_vecD hN W hD hpos hcube ht hC0 hU τ hphys P)
    (Eventually.of_forall fun R => gvecT_mem_range hN _ _ τ _ A
      ⟨cutM R P.1, fun i => ⟨hA i, uc_cut _ R (hP i)⟩⟩)

end Decay

/-! ## 6. The two sectors under the time translations -/

section Split

open ContinuousLinearMap (adjoint)
open MassGap.RegularDense (J_redTime norm_reduce_time)

variable {X : OSDataS} {R : Type} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  (Y : SubSector X R)

/-- **The complement of a sub-reconstruction is orthogonal to the vacuum.** DERIVED: `0` the vanishing
pairing. -/
theorem orth_vac {z : X.H} (hz : adjoint Y.J z = 0) : inner ℂ X.vac z = 0 := by
  rw [← Y.J_vac, ← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]

/-- **The times keep the complement.** DERIVED: `0` the sign of `t`, the vanishing image. -/
theorem orth_time {z : X.H} (hz : adjoint Y.J z = 0) {t : ℝ} (ht : 0 ≤ t) :
    adjoint Y.J (X.time t z) = 0 := by
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right,
    ← inner_sa (X.time_selfAdjoint t ht).1, ← J_redTime Y ht,
    ← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]

/-- **The complement decays at the gap of `X`, and carries no vacuum**: nothing below that gap sits
there. DERIVED: `0` the sign of `t`. -/
theorem norm_time_orth {z : X.H} (hz : adjoint Y.J z = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖X.time t z‖ ≤ Real.exp (-(X.gap * t)) * ‖z‖ :=
  X.time_gap t ht z (orth_vac Y hz)

/-- DERIVED: `0` the vanishing image. -/
theorem adj_sub (z : X.H) : adjoint Y.J (z - Y.J (adjoint Y.J z)) = 0 := by
  rw [map_sub, Y.adj_J, sub_self]

/-- **Pythagoras for the split.** DERIVED: `0` the cross term; `2` the square. -/
theorem norm_sq_add_of_orth (y : R) {w : X.H} (hw : adjoint Y.J w = 0) :
    ‖Y.J y + w‖ ^ 2 = ‖y‖ ^ 2 + ‖w‖ ^ 2 := by
  have h : inner ℂ (Y.J y) w = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hw, inner_zero_right]
  rw [norm_add_sq (𝕜 := ℂ), h, Y.norm_J]
  simp

/-- **The time acts sector by sector.** DERIVED: `0` the sign of `t`; `2` the square. -/
theorem norm_sq_time_split (z : X.H) {t : ℝ} (ht : 0 ≤ t) :
    ‖X.time t z‖ ^ 2 = ‖(reduce Y).time t (adjoint Y.J z)‖ ^ 2
      + ‖X.time t (z - Y.J (adjoint Y.J z))‖ ^ 2 := by
  have e : X.time t z = Y.J ((reduce Y).time t (adjoint Y.J z))
      + X.time t (z - Y.J (adjoint Y.J z)) := by
    rw [MassGap.RegularDense.J_reduce_time Y ht, ← map_add, add_sub_cancel]
  rw [e, norm_sq_add_of_orth Y _ (orth_time Y (adj_sub Y z) ht)]
  rfl

/-- **The gap up to `X.gap` is read on the sector.** For `g ≤ X.gap`, the contraction at rate `g` on the
vacuum complement of `X` is the same statement as on the vacuum complement of the sub-reconstruction: the
complement contributes nothing below `X.gap`. DERIVED: `0` the vanishing pairing and the sign of `t`;
`2` the square. -/
theorem gap_iff_sector {g : ℝ} (hg : g ≤ X.gap) :
    (∀ t, 0 ≤ t → ∀ u : X.H, inner ℂ X.vac u = 0 → ‖X.time t u‖ ≤ Real.exp (-(g * t)) * ‖u‖)
      ↔ ∀ t, 0 ≤ t → ∀ y : R, inner ℂ Y.vac y = 0 →
          ‖(reduce Y).time t y‖ ≤ Real.exp (-(g * t)) * ‖y‖ := by
  constructor
  · intro h t ht y hy
    have hJ : inner ℂ X.vac (Y.J y) = 0 := by rw [← Y.J_vac, Y.inner_J]; exact hy
    rw [norm_reduce_time Y ht, ← Y.norm_J y]
    exact h t ht _ hJ
  · intro h t ht u hu
    obtain ⟨y, hy⟩ : ∃ y, y = adjoint Y.J u := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = u - Y.J y := ⟨_, rfl⟩
    have hw0 : adjoint Y.J w = 0 := by rw [hw, hy]; exact adj_sub Y u
    have hy0 : inner ℂ Y.vac y = 0 := by
      rw [hy, ContinuousLinearMap.adjoint_inner_right, Y.J_vac]
      exact hu
    have hsplit : ‖u‖ ^ 2 = ‖y‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [← norm_sq_add_of_orth Y y hw0, hw, add_sub_cancel]
    have h1 := h t ht y hy0
    have h2 : ‖X.time t w‖ ≤ Real.exp (-(g * t)) * ‖w‖ := by
      refine (norm_time_orth Y hw0 ht).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h3 := norm_sq_time_split Y u ht
    rw [← hy, ← hw] at h3
    have hE : 0 ≤ Real.exp (-(g * t)) := (Real.exp_pos _).le
    refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hE (norm_nonneg _))).mp ?_
    rw [h3, mul_pow, hsplit, mul_add, ← mul_pow, ← mul_pow]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pow_le_pow_left₀ (norm_nonneg _) h2 2)

end Split

/-! ## 7. The observer's reconstruction on all local fields -/

section ObserverData

/-- **The sector of all local fields as a sub-reconstruction of `observerOSDataS`.** DERIVED: `0` the
excluded colour count and the reference step; `1` the top of `ρ` and the unit step. -/
def observerAllSub (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (energy0 W D hD) (UF N) τ r) :
    SubSector (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR.flow)
      (RH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) (UF N) τ
        (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) :=
  let hB := uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ
  { J := J hN (energy0 W D hD) hB (UF N) τ hpp
    inner_J := inner_J hN (energy0 W D hD) hB (UF N) τ hpp
    vac := rVac hN (energy0 W D hD) hB (UF N) τ hpp
    J_vac := J_vac hN (energy0 W D hD) hB (UF N) τ hpp
    comm := commute_proj_timeT hN (energy0 W D hD) hB τ hpp (UF N) 1
    nontrivial := MassGap.RegularDense.exists_orth_rH hN (energy0 W D hD) hB (UF N) τ hpp hR }

/-- **The observer's reconstruction on all local fields**: an `OSDataS` on the sector, with the Schwinger
functions and the gap of `observerOSDataS`. DERIVED: `0`, `1` as in `observerAllSub`. -/
def observerAll (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (energy0 W D hD) (UF N) τ r) : OSDataS :=
  reduce (observerAllSub hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR)

/-- **The real translations of `observerAll`.** No identity branch, and no field left out. DERIVED:
`-1` the sign of the inverse translation; `0`, `1` as in `observerAllSub`. -/
def allSpatial (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (energy0 W D hD) (UF N) τ r) :
    SpatialData (observerAll hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR) :=
  let Φ := energy0 W D hD
  let hB := uniformBoundF_energy0 hN W D hD hpos hcube
  let hM := allMom_energy0 hN W hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN Φ hphys τ
  { ι := spatial τ
    U := fun x => aU hN Φ hB hM τ hpp x
    Uinv := fun x => aU hN Φ hB hM τ hpp (-x)
    inner_U := fun x z w => inner_aU hN Φ hB hM τ hpp x z w
    U_Uinv := fun x => by
      have h1 := aU_add hN Φ hB hM τ hpp x (-x)
      rw [add_neg_cancel, aU_zero] at h1
      exact h1.symm
    Uinv_U := fun x => by
      have h1 := aU_add hN Φ hB hM τ hpp (-x) x
      rw [neg_add_cancel, aU_zero] at h1
      exact h1.symm
    commute := fun x => commute_aU_aTime hN Φ hB hM τ hpp x 1
    U_vac := fun x => aU_vac hN Φ hB hM τ hpp x }

/-- **Fixed by every dyadic spatial translation of `FlowH` is fixed by every real one**, on the sector.
The real fixed set is closed and the dyadic vectors with zero time component are dense in `spatial τ`.
DERIVED: `0` the time component; `1` the excluded colour count. -/
theorem dyadic_fixed_iff (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (hM : AllMom hN Φ)
    (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) (y : RH hN Φ hB (UF N) τ hpp) :
    (∀ i : SpIdx τ, spT hN Φ hB τ hpp i.1.1 i.1.2 i.2 (J hN Φ hB (UF N) τ hpp y)
        = J hN Φ hB (UF N) τ hpp y)
      ↔ ∀ x : spatial τ, aU hN Φ hB hM τ hpp x y = y := by
  constructor
  · intro h x
    have hcl : IsClosed {x : spatial τ | aU hN Φ hB hM τ hpp x y = y} :=
      isClosed_eq (continuous_aU hN Φ hB hM τ hpp y) continuous_const
    refine hcl.closure_subset_iff.mpr subset_rfl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    have hev : ∀ᶠ w in 𝓝 (x : Fin 4 → ℝ), dist w (x : Fin 4 → ℝ) < ε :=
      Metric.eventually_nhds_iff.mpr ⟨ε, hε, fun _ hw => hw⟩
    obtain ⟨m, n, hw⟩ := ContinuumHypercubic.exists_dyadic_of_eventually (one_le_of_ne_zero hN) hev
    have hn' : (Function.update n τ 0) τ = 0 := Function.update_self _ _ _
    refine ⟨⟨site (dySpacing N m) (Function.update n τ 0), mem_spatial (site_time_zero _ hn')⟩, ?_, ?_⟩
    · have h1 := J_aU_dyadic hN Φ hB hM τ hpp m hn' y
      rw [h ⟨(m, Function.update n τ 0), hn'⟩] at h1
      have h2 := congrArg (Jd hN Φ hB (UF N) τ hpp) h1
      rwa [JdJ, JdJ] at h2
    · rw [Subtype.dist_eq, dist_pi_lt_iff hε]
      intro j
      by_cases hj : j = τ
      · subst hj
        have e1 : site (dySpacing N m) (Function.update n j 0) j = 0 := site_time_zero _ hn'
        show dist ((x : Fin 4 → ℝ) j) (site (dySpacing N m) (Function.update n j 0) j) < ε
        rw [spatial_time x, e1, dist_self]
        exact hε
      · have e1 : site (dySpacing N m) (Function.update n τ 0) j = site (dySpacing N m) n j := by
          show dySpacing N m * ((Function.update n τ 0 j : ℤ) : ℝ) = dySpacing N m * ((n j : ℤ) : ℝ)
          rw [Function.update_of_ne hj]
        show dist ((x : Fin 4 → ℝ) j) (site (dySpacing N m) (Function.update n τ 0) j) < ε
        rw [e1, dist_comm]
        exact (dist_le_pi_dist _ _ j).trans_lt hw
  · rintro h ⟨⟨m, n⟩, hn⟩
    show spT hN Φ hB τ hpp m n hn _ = _
    rw [← J_aU_dyadic hN Φ hB hM τ hpp m hn y, h]

/-- **The real zero-momentum space of `observerAll` is the dyadic zero-momentum space of
`observerOSDataS`, read on the sector.** The dyadic data `observerSpatial` translates all of `FlowH` with
the physical action and has no identity branch. DERIVED: `0`, `1` as in `observerAllSub`. -/
theorem mem_zeroMom_allSpatial_iff (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (energy0 W D hD) (UF N) τ r)
    (u : RH hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) (UF N) τ
      (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)) :
    u ∈ zeroMom (allSpatial hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR)
      ↔ (observerAllSub hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR).J u
          ∈ zeroMom (observerSpatial hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR.flow) :=
  (dyadic_fixed_iff hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
    (allMom_energy0 hN W hD hpos hcube) τ
    (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) u).symm

end ObserverData

/-! ## 8. Where `hNT` comes from -/

section Link

open MassGap.ClayFull MassGap.ClayStatement MassGap.ClayWiring MassGap.ObserverSymField
  MassGap.PreObserver MassGap.ObserverNontrivial MassGap.ObserverOSEuclidS MassGap.ContinuumHypercubic
  MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered
  MassGap.ObserverOSLinked MassGap.ObserverRotation

/-- **`FlowConnectedNonzero` follows from the composites' link.** No proof in the tree discharges `hNT`:
it is a hypothesis of every capstone that takes it, and `PreObserver` replaces it by `preNontrivial`.
`flowConnected_iff` gives the input itself from that vector. The witness `Q` is not named: it comes from
density of the span of all margin monomials. DERIVED: `2` the least colour count; `0` the plane; `1`–`3`
the slots. -/
theorem flowConnected_of_link (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (ρ : RenormMix N) (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G)
    (hAF : AFCoefficient N G) (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC) :
    FlowConnectedNonzero (ne_zero_of_two_le hN2) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r :=
  (flowConnected_iff (ne_zero_of_two_le hN2) (energy0 W (SymPlaqClass N) (symPlaq_refl N))
    (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0)).mpr
    (preNontrivial hN2 W hU hphys ρ G hK hAF Cs wC e he1 he2 hLC)

/-- **`RegConnectedNonzero` at the observer's class from a connected cross reading of a composite.** The
reading is the tree's own `mixT`: if the composite `P` and the regular monomial `Q` do not factorise
through the vacuum, the regular sector is non-trivial. DERIVED: `0` the plane; `1`–`3` the slots. -/
theorem regConnected_of_mix (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (ρ : RenormMix N) (w : TSep 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      inner ℂ (w P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
        = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1 : ℂ))
    (P : TSep 0) (Q : RMono N (SymPlaqClass N) 0 r)
    (h : mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1
      ≠ mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1
          (emptyMargin N 0 r).1
        * kernF (ne_zero_of_two_le hN2) (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            (emptyMargin N 0 r).1 Q.1.1) :
    RegConnectedNonzero (ne_zero_of_two_le hN2) (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (SymPlaqClass N) 0 r := by
  have hin := inner_gVec (flowTransfer (ne_zero_of_two_le hN2)
    (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0) 0)
    (fun P Q : MarginMono N 0 r => kernF (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1) (fun _ _ => rfl)
    (emptyMargin N 0 r) Q.1
  refine regConnected_of_cross (ne_zero_of_two_le hN2) _ (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0) _ (w P) Q fun he => h ?_
  have e1 := hX P ⟨Q.1, fun i => (Q.2 i).1⟩
  have e2 := hX P ⟨emptyMargin N 0 r, fun i => i.elim0⟩
  have e3 : inner ℂ (w P) (gvecT (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0
      (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0) Q.1) = _ := e1
  have e4 : inner ℂ (w P) (vacT (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0
      (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0)) = _ := e2
  have e5 : inner ℂ (vacT (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0
      (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0))
      (gvecT (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0
      (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) _ hphys 0) Q.1) = _ := hin
  rw [e3, e4, e5] at he
  exact_mod_cast he

end Link

end

end MassGap.RegularFull

#print axioms MassGap.RegularFull.SmearMom
#print axioms MassGap.RegularFull.AllMom
#print axioms MassGap.RegularFull.SmearMom.mono
#print axioms MassGap.RegularFull.allMom_energy0
#print axioms MassGap.RegularFull.abs_contSF_le_of_mom
#print axioms MassGap.RegularFull.exists_sup_const
#print axioms MassGap.RegularFull.tendsto_contSF_translate_all
#print axioms MassGap.RegularFull.contSF_translate_real_all
#print axioms MassGap.RegularFull.tendsto_contSF_of_sup_all
#print axioms MassGap.RegularFull.UF
#print axioms MassGap.RegularFull.uf_refl
#print axioms MassGap.RegularFull.reg_uf_of_uc
#print axioms MassGap.RegularFull.reg_uf
#print axioms MassGap.RegularFull.regConnected_uf
#print axioms MassGap.RegularFull.tendsto_kernF_shift_all
#print axioms MassGap.RegularFull.kernF_shift_real_all
#print axioms MassGap.RegularFull.form_aLin
#print axioms MassGap.RegularFull.aU
#print axioms MassGap.RegularFull.inner_aU
#print axioms MassGap.RegularFull.aU_add
#print axioms MassGap.RegularFull.aU_zero
#print axioms MassGap.RegularFull.aU_vac
#print axioms MassGap.RegularFull.commute_aU_rStep
#print axioms MassGap.RegularFull.tendsto_form_aLin
#print axioms MassGap.RegularFull.tendsto_aU
#print axioms MassGap.RegularFull.continuous_aU
#print axioms MassGap.RegularFull.J_aU_dyadic
#print axioms MassGap.RegularFull.commute_proj_stepT
#print axioms MassGap.RegularFull.commute_proj_timeT
#print axioms MassGap.RegularFull.aT
#print axioms MassGap.RegularFull.aT_apply
#print axioms MassGap.RegularFull.aU_rStep_apply
#print axioms MassGap.RegularFull.commute_aT_stepT
#print axioms MassGap.RegularFull.commute_aT_timeT
#print axioms MassGap.RegularFull.aT_J
#print axioms MassGap.RegularFull.aTime
#print axioms MassGap.RegularFull.J_aTime
#print axioms MassGap.RegularFull.commute_aU_aTime
#print axioms MassGap.RegularFull.gVec_eq_of_connected
#print axioms MassGap.RegularFull.exists_orth_iff
#print axioms MassGap.RegularFull.flowConnected_iff
#print axioms MassGap.RegularFull.regConnected_iff
#print axioms MassGap.RegularFull.not_regConnected_iff
#print axioms MassGap.RegularFull.regConnected_of_cross
#print axioms MassGap.RegularFull.regConnected_of_lattice
#print axioms MassGap.RegularFull.not_regConnected_of_zero
#print axioms MassGap.RegularFull.norm_J
#print axioms MassGap.RegularFull.isClosed_range_J
#print axioms MassGap.RegularFull.gvecT_mem_range
#print axioms MassGap.RegularFull.range_J_eq_univ_iff
#print axioms MassGap.RegularFull.contSF_congr_sample
#print axioms MassGap.RegularFull.sampleSet
#print axioms MassGap.RegularFull.sampleSet_null
#print axioms MassGap.RegularFull.site_mem_sampleSet
#print axioms MassGap.RegularFull.sampleCopy
#print axioms MassGap.RegularFull.sampleCopy_ae_zero
#print axioms MassGap.RegularFull.contSF_sampleCopy
#print axioms MassGap.RegularFull.uc_mul
#print axioms MassGap.RegularFull.abs_chi_le
#print axioms MassGap.RegularFull.uc_chi
#print axioms MassGap.RegularFull.uc_cut
#print axioms MassGap.RegularFull.uc_ofE4
#print axioms MassGap.RegularFull.vecD_mem_range
#print axioms MassGap.RegularFull.orth_vac
#print axioms MassGap.RegularFull.orth_time
#print axioms MassGap.RegularFull.norm_time_orth
#print axioms MassGap.RegularFull.adj_sub
#print axioms MassGap.RegularFull.norm_sq_add_of_orth
#print axioms MassGap.RegularFull.norm_sq_time_split
#print axioms MassGap.RegularFull.gap_iff_sector
#print axioms MassGap.RegularFull.observerAllSub
#print axioms MassGap.RegularFull.observerAll
#print axioms MassGap.RegularFull.allSpatial
#print axioms MassGap.RegularFull.dyadic_fixed_iff
#print axioms MassGap.RegularFull.mem_zeroMom_allSpatial_iff
#print axioms MassGap.RegularFull.flowConnected_of_link
#print axioms MassGap.RegularFull.regConnected_of_mix
