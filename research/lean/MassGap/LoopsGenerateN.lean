import Mathlib
import MassGap.RunSeedN
import MassGap.LoopsGenerate

/-!
# MassGap.LoopsGenerateN — which `SU(N)` loop states generate the excited zero-flux levels

`RunSeedN.SliceEndN.gen` asks every excited zero-flux level of `trivKN N` to lie in the `L²` closure of the span
of the loop states of the record's family (`RunSeedN.LoopFam`). This module settles the two families.

## 1. Single loops: charge conjugation (proved, every `N`)

`cconj : SU(N) →* SU(N)`, `U ↦ Ū` (entrywise complex conjugate; `Ū` is special unitary), `conjCfg` on slice
configurations. `holN_conjCfg` (`hol_C(V̄) = (hol_C V)‾`), **`wlN_conjCfg`** (`Re tr` is unchanged),
**`measurePreserving_cconj`** (Haar uniqueness: the image of `probHaar` under the continuous automorphism `cconj`
is a left-invariant probability measure), **`measurePreserving_conjCfg`** on `RectTransfer.hS`.
`Cop` is composition with `conjCfg` on `L²`. **`closure_single_le`**: if `Ω(V̄) = s Ω(V)`, every vector `f` in
the closed span of the single-loop states has `Cop f = s f`. **`not_mem_closure_single_of_odd`**: a non-zero
`f` with `Cop f = −s f` (`s ≠ 0`) is not in that closed span; **`not_gen_single_of_odd`** is the statement on a
level: a `C`-odd excited level (`φ_j(V̄) = −s φ_j(V)`) is not in the closed span of the single-loop states of
`Ω = φ_{g₀}`. At `N = 2`, `Ū = σ_y U σ_y` is a gauge transformation, so no zero-flux level is `C`-odd; at `N ≥ 3`
the `C`-odd levels are the levels of the odd part of the zero-flux sector (for instance the levels that
`Im tr` of a contractible loop times `φ_{g₀}` overlaps; argued, not proved), so `gen` on `single` fails on
every `C`-odd excited level there.

## 2. Words: Stone–Weierstrass (proved, every `N`, from orbit separation)

`lfC` (the letters `Re tr hol_C`, `Im tr hol_C` as continuous functions). `pfN_mem` (every element of the monoid
the letters generate is a word `pfN L`), `stateFnN`, **`stateFnN_mem_span`** (the state of an element of the
algebra the letters generate lies in the span of the word states). **`mem_closure_words`**: for a probability
measure on the slice, `Ω` continuous and nowhere zero with `∫ Ω² = 1`, and `φ` continuous with `∫ Ω φ = 0`, if
`φ/Ω` takes one value on configurations no letter separates, then `φ` is in the closed span of the word states
(`LoopsGenerate.exists_adjoin_near`).

## 3. The levels at `SU(N)` (proved)

`iter_gact_leftN`, `trivKN_gact_leftN`, `continuous_trivKN_leftN`, `eigen_ne_zeroN`, `level_eqN`,
**`level_gactN`**, **`continuous_levelN`**, `continuous_trivKN_rowN`, **`ground_ne_zeroN`** (`β > 0`: the ground
level of `trivKN N` vanishes nowhere; the argument of `LoopsGenerate.ground_ne_zero`, with its `SU(N)`-free steps
`qform_le`, `integral_defect_sq`, `summable_sq` reused).

## 4. `gen` on words

`TracesSeparateN N n i`: configurations with equal complex traces `tr hol_C` on every loop are gauge related
(`gact`). **`excited_mem_closure_wordsN`**: at `β > 0`, for measurable levels, `TracesSeparateN` gives `gen` on
`LoopFam.words`. **`gen_words_of_separation`** packages it in the form of the `SliceEndN.gen` field.
**`tracesSeparateN_two`**: at `N = 2` (`n > 0`) it holds (`LoopsGenerate.giles`). At every `N ≠ 0` it holds
(`ProcesiSeparation.tracesSeparateN_all`: the complex traces of words separate simultaneous-conjugacy orbits of
unitary tuples, Procesi).

DERIVED (module-wide): `2` the `L²` exponent and the square; `4` in `δ = ε / (4 (B + 1))` makes `2 δ B < ε`; `1`
the norm of `Ω`; `0` the empty-word junction count. `G/(q+1)` as in `LoopsGenerate`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LoopsGenerateN

open MeasureTheory Filter
open MassGap.ElectricLoops (Loop Dir vecOf memLp_of_norm)
open MassGap.RectWilson (SpT TT)
open MassGap.RunSeedN
open MassGap.CompactGauge (probHaar)
open MassGap.LoopsGenerate (exists_adjoin_near BM bm_row_fun qform qform_le integral_defect_sq summable_sq)

/-! ## 1. Charge conjugation -/

section Conj

variable {N : ℕ}

/-- Entrywise complex conjugation as a ring endomorphism of the matrices. -/
abbrev cmat (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →+* Matrix (Fin N) (Fin N) ℂ :=
  (starRingEnd ℂ).mapMatrix

theorem cmat_star (M : Matrix (Fin N) (Fin N) ℂ) : star (cmat N M) = cmat N (star M) := by
  ext a b
  simp [Matrix.star_apply]

theorem cmat_mem (U : SUN.SU N) : cmat N (U : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  have hU := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, cmat_star, ← map_mul, Matrix.mem_unitaryGroup_iff.mp hU.1, map_one]
  · have h := RingHom.map_det (starRingEnd ℂ) (U : Matrix (Fin N) (Fin N) ℂ)
    rw [hU.2, map_one] at h
    exact h.symm

/-- **Charge conjugation** `U ↦ Ū` on `SU(N)`. -/
def cconj (N : ℕ) : SUN.SU N →* SUN.SU N where
  toFun U := ⟨cmat N U, cmat_mem U⟩
  map_one' := Subtype.ext (by simp)
  map_mul' U V := Subtype.ext (by simp)

theorem coe_cconj (U : SUN.SU N) :
    ((cconj N U : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = cmat N U := rfl

theorem cconj_cconj (U : SUN.SU N) : cconj N (cconj N U) = U := by
  apply Subtype.ext
  rw [coe_cconj, coe_cconj]
  ext a b
  simp

theorem continuous_cconj : Continuous (cconj N) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.matrix_map Complex.continuous_conj)

/-- **Charge conjugation preserves the Haar measure of `SU(N)`.** -/
theorem measurePreserving_cconj :
    MeasurePreserving (cconj N) (probHaar (SUN.SU N)) (probHaar (SUN.SU N)) := by
  have hsurj : Function.Surjective (cconj N) := fun U => ⟨cconj N U, cconj_cconj U⟩
  have hm : Measurable (cconj N) := continuous_cconj.measurable
  refine ⟨hm, ?_⟩
  set ν := Measure.map (cconj N) (probHaar (SUN.SU N))
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  haveI : ν.IsMulLeftInvariant :=
    isMulLeftInvariant_map (cconj N).toMulHom hm hsurj
  have h := Measure.haarMeasure_unique ν (default : TopologicalSpace.PositiveCompacts (SUN.SU N))
  have hd : ((default : TopologicalSpace.PositiveCompacts (SUN.SU N)) : Set (SUN.SU N)) = Set.univ :=
    TopologicalSpace.PositiveCompacts.coe_top
  rw [hd, measure_univ, one_smul] at h
  exact h

variable {i : Fin 4} {T : Dir i → ℕ}

/-- Charge conjugation of a slice configuration. -/
def conjCfg (V : SpT i T → SUN.SU N) : SpT i T → SUN.SU N := fun l => cconj N (V l)

/-- **Charge conjugation preserves the slice Haar measure.** -/
theorem measurePreserving_conjCfg :
    MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) (RectTransfer.hS i T N) (RectTransfer.hS i T N) :=
  measurePreserving_pi _ _ fun _ => measurePreserving_cconj

theorem whN_conjCfg (w : List (SpT i T × Bool)) (V : SpT i T → SUN.SU N) :
    whN w (conjCfg V) = cconj N (whN w V) := by
  induction w with
  | nil => simp [whN]
  | cons x w ih =>
      have e : ∀ W : SpT i T → SUN.SU N, whN (x :: w) W = (if x.2 then W x.1 else (W x.1)⁻¹) * whN w W :=
        fun W => by simp [whN]
      rw [e, e, ih, map_mul]
      congr 1
      by_cases h : x.2 <;> simp [h, conjCfg]

theorem holN_conjCfg (C : Loop i T) (V : SpT i T → SUN.SU N) :
    holN C (conjCfg V) = cconj N (holN C V) :=
  whN_conjCfg _ V

/-- **A Wilson loop is unchanged by charge conjugation**: `Re tr Ū = Re tr U`. -/
theorem wlN_conjCfg (C : Loop i T) (V : SpT i T → SUN.SU N) : wlN C (conjCfg V) = wlN C V := by
  unfold wlN
  rw [holN_conjCfg, coe_cconj]
  simp [Matrix.trace, Complex.re_sum]

variable {μ : Measure (SpT i T → SUN.SU N)}

/-- Composition with charge conjugation on `L²`. -/
def Cop (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (conjCfg (N := N) (i := i) (T := T)) hμ).toContinuousLinearMap

theorem coeFn_Cop (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ) (f : Lp ℝ 2 μ) :
    (Cop hμ f : (SpT i T → SUN.SU N) → ℝ) =ᵐ[μ] (f : (SpT i T → SUN.SU N) → ℝ) ∘ conjCfg :=
  Lp.coeFn_compMeasurePreserving f hμ

/-- The vectors of `C`-parity `s`, a closed subspace. -/
def paritySub (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ) (s : ℝ) :
    Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | Cop hμ f = s • f}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hf, hg, smul_add]
  zero_mem' := by simp
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hf, smul_comm]

theorem isClosed_paritySub (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ) (s : ℝ) :
    IsClosed (paritySub hμ s : Set (Lp ℝ 2 μ)) :=
  isClosed_eq (Cop hμ).continuous (continuous_const_smul s)

/-- **The closed span of the single-loop states has the parity of `Ω`.** If `Ω(V̄) = s Ω(V)`, every vector `f`
in the closure of the span of `allLoopsN μ Ω single` has `f ∘ conj = s f`. -/
theorem closure_single_le (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ)
    {Ω : (SpT i T → SUN.SU N) → ℝ} {s : ℝ} (hΩ : ∀ V, Ω (conjCfg V) = s * Ω V) :
    closure (Submodule.span ℝ (allLoopsN μ Ω .single) : Set (Lp ℝ 2 μ)) ⊆ paritySub hμ s := by
  refine closure_minimal ?_ (isClosed_paritySub hμ s)
  rw [SetLike.coe_subset_coe, Submodule.span_le]
  rintro g ⟨L, ⟨C, rfl⟩, he⟩
  show Cop hμ g = s • g
  have hpt : ∀ V, loopStateN μ Ω [(C, true)] (conjCfg V) = s * loopStateN μ Ω [(C, true)] V := by
    intro V
    simp only [loopStateN, pfN_single, wlN_conjCfg, hΩ]
    ring
  apply Lp.ext
  filter_upwards [coeFn_Cop hμ g, hμ.quasiMeasurePreserving.ae_eq_comp he, Lp.coeFn_smul s g, he]
    with V h1 h2 h3 h4
  rw [h1, h2, h3, Function.comp_apply, hpt, Pi.smul_apply, smul_eq_mul, h4]

/-- **A vector of the opposite parity is not in the closed span of the single-loop states.** -/
theorem not_mem_closure_single_of_odd (hμ : MeasurePreserving (conjCfg (N := N) (i := i) (T := T)) μ μ)
    {Ω : (SpT i T → SUN.SU N) → ℝ} {s : ℝ} (hs : s ≠ 0) (hΩ : ∀ V, Ω (conjCfg V) = s * Ω V)
    {f : Lp ℝ 2 μ} (hf : Cop hμ f = -(s • f)) (hf0 : f ≠ 0) :
    f ∉ closure (Submodule.span ℝ (allLoopsN μ Ω .single) : Set (Lp ℝ 2 μ)) := by
  intro hmem
  have h : Cop hμ f = s • f := closure_single_le hμ hΩ hmem
  rw [hf] at h
  have h1 : s • f + s • f = 0 := by
    calc s • f + s • f = s • f + -(s • f) := by rw [h]
      _ = 0 := add_neg_cancel _
  have h2 : (2 * s) • f = 0 := by rw [mul_smul, two_smul, h1]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hs (by linarith)
  · exact hf0 h3

end Conj

section ConjLevel

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.CentreSectorSeed (Tr)

variable {N : ℕ} [NeZero N]

/-- **`gen` on single loops fails on a `C`-odd excited level.** If `Ω = φ_{g₀}` has `C`-parity `s ≠ 0` and an
excited level `φ_j` has parity `−s`, then `φ_j` is not in the closed span of the single-loop states. -/
theorem not_gen_single_of_odd {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) {s : ℝ} (hs : s ≠ 0) (hΩ : ∀ V, φ g₀ (conjCfg V) = s * φ g₀ V)
    (j : ι) (hodd : ∀ V, φ j (conjCfg V) = -(s * φ j V)) :
    vecOf (hm j) (hL.norm j)
      ∉ closure (Submodule.span ℝ (allLoopsN (hSN N n i) (φ g₀) .single) : Set (Lp ℝ 2 (hSN N n i))) := by
  have hμ := measurePreserving_conjCfg (N := N) (i := i) (T := Tr n i)
  refine not_mem_closure_single_of_odd hμ hs hΩ ?_ ?_
  · have hv := (memLp_of_norm (hm j) (hL.norm j)).coeFn_toLp
    apply Lp.ext
    filter_upwards [coeFn_Cop hμ (vecOf (hm j) (hL.norm j)), hμ.quasiMeasurePreserving.ae_eq_comp hv,
      Lp.coeFn_neg (s • vecOf (hm j) (hL.norm j)), Lp.coeFn_smul s (vecOf (hm j) (hL.norm j)), hv]
      with V h1 h2 h3 h4 h5
    unfold vecOf at h1 h3 h4 ⊢
    rw [h1, h2, h3, Pi.neg_apply, h4, Pi.smul_apply, smul_eq_mul, h5, Function.comp_apply]
    exact hodd V
  · intro h0
    have h := ElectricLoops.norm_vecOf (hm j) (hL.norm j)
    rw [h0, norm_zero] at h
    exact zero_ne_one h

end ConjLevel

/-! ## 2. Words: Stone–Weierstrass on the slice -/

section Words

variable {N : ℕ} {i : Fin 4} {T : Dir i → ℕ}

/-- The letters as continuous functions. -/
def lfC (c : Loop i T × Bool) : C(SpT i T → SUN.SU N, ℝ) := ⟨lfN c, continuous_lfN c⟩

/-- Every element of the monoid the letters generate is a word. -/
theorem pfN_mem {q : C(SpT i T → SUN.SU N, ℝ)} (hq : q ∈ Submonoid.closure (Set.range (lfC (N := N) (i := i) (T := T)))) :
    ∃ L : List (Loop i T × Bool), (q : (SpT i T → SUN.SU N) → ℝ) = pfN L := by
  let M : Submonoid C(SpT i T → SUN.SU N, ℝ) :=
    { carrier := {q | ∃ L : List (Loop i T × Bool), (q : (SpT i T → SUN.SU N) → ℝ) = pfN L}
      mul_mem' := by
        rintro a b ⟨L, hL⟩ ⟨L', hL'⟩
        refine ⟨L ++ L', ?_⟩
        funext V
        simp only [ContinuousMap.coe_mul, Pi.mul_apply, pfN, List.map_append, List.prod_append]
        rw [show a V = pfN L V from congrFun hL V, show b V = pfN L' V from congrFun hL' V]
        rfl
      one_mem' := ⟨[], by funext V; simp [pfN]⟩ }
  have hle : Submonoid.closure (Set.range (lfC (N := N) (i := i) (T := T))) ≤ M := by
    rw [Submonoid.closure_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨[c], by funext V; simp [pfN, lfC]⟩
  exact hle hq

variable {μ : Measure (SpT i T → SUN.SU N)} [IsProbabilityMeasure μ]

theorem abs_le_normN {g : (SpT i T → SUN.SU N) → ℝ} (hg : Continuous g) (V : SpT i T → SUN.SU N) :
    |g V| ≤ ‖(⟨g, hg⟩ : C(SpT i T → SUN.SU N, ℝ))‖ := by
  have h := ContinuousMap.norm_coe_le_norm (⟨g, hg⟩ : C(SpT i T → SUN.SU N, ℝ)) V
  rwa [Real.norm_eq_abs] at h

omit [IsProbabilityMeasure μ] in
theorem integrable_of_contN [IsFiniteMeasure μ] {g : (SpT i T → SUN.SU N) → ℝ} (hg : Continuous g) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun V => by rw [Real.norm_eq_abs]; exact abs_le_normN hg V)

omit [IsProbabilityMeasure μ] in
theorem memLp_of_contN [IsFiniteMeasure μ] {g : (SpT i T → SUN.SU N) → ℝ} (hg : Continuous g) :
    MemLp g 2 μ :=
  MemLp.of_bound hg.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun V => by rw [Real.norm_eq_abs]; exact abs_le_normN hg V)

/-- The state `(g − ∫ g Ω²) Ω` of a function `g`. -/
def stateFnN (μ : Measure (SpT i T → SUN.SU N)) (Ω g : (SpT i T → SUN.SU N) → ℝ) :
    (SpT i T → SUN.SU N) → ℝ :=
  fun V => (g V - ∫ U, g U * Ω U ^ 2 ∂μ) * Ω V

omit [IsProbabilityMeasure μ] in
theorem continuous_stateFnN {Ω g : (SpT i T → SUN.SU N) → ℝ} (hΩ : Continuous Ω) (hg : Continuous g) :
    Continuous (stateFnN μ Ω g) :=
  (hg.sub continuous_const).mul hΩ

/-- **The state of an element of the algebra the letters generate lies in the span of the word states.** -/
theorem stateFnN_mem_span {Ω : (SpT i T → SUN.SU N) → ℝ} (hΩ : Continuous Ω)
    {p : C(SpT i T → SUN.SU N, ℝ)} (hp : p ∈ Algebra.adjoin ℝ (Set.range (lfC (N := N) (i := i) (T := T)))) :
    (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ p.continuous)).toLp (stateFnN μ Ω p)
      ∈ Submodule.span ℝ (allLoopsN μ Ω .words) := by
  have hint : ∀ q : C(SpT i T → SUN.SU N, ℝ), Integrable (fun U => q U * Ω U ^ 2) μ :=
    fun q => integrable_of_contN (q.continuous.mul (hΩ.pow 2))
  have hp' : p ∈ Submodule.span ℝ (Submonoid.closure (Set.range (lfC (N := N) (i := i) (T := T))) :
      Set C(SpT i T → SUN.SU N, ℝ)) := by
    rw [← Algebra.adjoin_eq_span]; exact hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨L, hL⟩ := pfN_mem hx
      refine Submodule.subset_span ⟨L, trivial, ?_⟩
      refine (MemLp.coeFn_toLp _).trans (Filter.Eventually.of_forall fun V => ?_)
      simp only [stateFnN, loopStateN, vevN, hL]
  | zero =>
      have h0 : stateFnN μ Ω (0 : C(SpT i T → SUN.SU N, ℝ)) = 0 := by
        funext V; simp [stateFnN]
      have : (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ
          (0 : C(SpT i T → SUN.SU N, ℝ)).continuous)).toLp (stateFnN μ Ω (0 : C(SpT i T → SUN.SU N, ℝ)))
          = 0 := by
        rw [← MemLp.toLp_zero (memLp_of_contN (μ := μ) (g := (0 : (SpT i T → SUN.SU N) → ℝ))
          continuous_zero)]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [h0])
      rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      have he : stateFnN μ Ω (x + y : C(SpT i T → SUN.SU N, ℝ))
          = stateFnN μ Ω x + stateFnN μ Ω y := by
        funext V
        simp only [stateFnN, ContinuousMap.add_apply, Pi.add_apply, add_mul]
        rw [integral_add (hint x) (hint y)]
        ring
      have : (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ
          (x + y : C(SpT i T → SUN.SU N, ℝ)).continuous)).toLp
            (stateFnN μ Ω (x + y : C(SpT i T → SUN.SU N, ℝ)))
          = (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ x.continuous)).toLp
              (stateFnN μ Ω x)
            + (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ y.continuous)).toLp
              (stateFnN μ Ω y) := by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [he])
      rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      have he : stateFnN μ Ω (a • x : C(SpT i T → SUN.SU N, ℝ)) = a • stateFnN μ Ω x := by
        funext V
        simp only [stateFnN, ContinuousMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]
        rw [integral_const_mul]
        ring
      have : (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ
          (a • x : C(SpT i T → SUN.SU N, ℝ)).continuous)).toLp
            (stateFnN μ Ω (a • x : C(SpT i T → SUN.SU N, ℝ)))
          = a • (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩ x.continuous)).toLp
              (stateFnN μ Ω x) := by
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun V => by rw [he])
      rw [this]; exact Submodule.smul_mem _ _ hx

/-- **Closed span of the word states, from separation by the letters.** Let `Ω` be continuous, nowhere zero,
with `∫ Ω² = 1`, and `φ` continuous with `∫ Ω φ = 0`. If `φ / Ω` takes one value on any two configurations that
no letter (`Re tr hol_C`, `Im tr hol_C`) tells apart, then `φ` is in the `L²` closure of the span of the word
states of `Ω`. -/
theorem mem_closure_words {Ω φ : (SpT i T → SUN.SU N) → ℝ}
    (hΩc : Continuous Ω) (hΩ0 : ∀ V, Ω V ≠ 0) (h1 : ∫ V, Ω V ^ 2 ∂μ = 1)
    (hφc : Continuous φ) (horth : ∫ V, Ω V * φ V ∂μ = 0)
    (hfib : ∀ V V', (∀ c : Loop i T × Bool, lfN c V = lfN c V') → φ V / Ω V = φ V' / Ω V')
    (hφ : MemLp φ 2 μ) :
    hφ.toLp φ ∈ closure (Submodule.span ℝ (allLoopsN μ Ω .words) : Set (Lp ℝ 2 μ)) := by
  set f : (SpT i T → SUN.SU N) → ℝ := fun V => φ V / Ω V with hfdef
  have hfc : Continuous f := hφc.div hΩc hΩ0
  set B := ‖(⟨Ω, hΩc⟩ : C(SpT i T → SUN.SU N, ℝ))‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have hΩB : ∀ V, |Ω V| ≤ B := abs_le_normN hΩc
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := ε / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hpA, hp⟩ := exists_adjoin_near (lfC (N := N) (i := i) (T := T)) f hfc
    (fun x y h => hfib x y h) hδ0
  have hmem := stateFnN_mem_span (μ := μ) hΩc hpA
  refine ⟨_, hmem, ?_⟩
  set c := ∫ U, p U * Ω U ^ 2 ∂μ with hc
  have hfΩ : ∀ U, f U * Ω U ^ 2 = Ω U * φ U := by
    intro U; simp only [hfdef]; field_simp [hΩ0 U]
  have hint2 : Integrable (fun U => Ω U ^ 2) μ := integrable_of_contN (hΩc.pow 2)
  have hcf : c = ∫ U, (p U - f U) * Ω U ^ 2 ∂μ := by
    have e : (fun U => (p U - f U) * Ω U ^ 2) = fun U => p U * Ω U ^ 2 - Ω U * φ U := by
      funext U; rw [sub_mul, hfΩ]
    rw [e, integral_sub (f := fun U => p U * Ω U ^ 2) (g := fun U => Ω U * φ U)
      (integrable_of_contN (p.continuous.mul (hΩc.pow 2))) (integrable_of_contN (hΩc.mul hφc)), horth,
      sub_zero]
  have hcδ : |c| ≤ δ := by
    rw [hcf, ← Real.norm_eq_abs]
    calc ‖∫ U, (p U - f U) * Ω U ^ 2 ∂μ‖ ≤ ∫ U, δ * Ω U ^ 2 ∂μ :=
          norm_integral_le_of_norm_le (hint2.const_mul δ) (Filter.Eventually.of_forall fun U => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Ω U))]
            exact mul_le_mul_of_nonneg_right (hp U).le (sq_nonneg _))
      _ = δ := by rw [integral_const_mul, h1, mul_one]
  have hpt : ∀ U, |φ U - stateFnN μ Ω p U| ≤ 2 * δ * B := by
    intro U
    have hφU : φ U = f U * Ω U := by simp only [hfdef]; field_simp [hΩ0 U]
    have e : φ U - stateFnN μ Ω p U = (f U - p U) * Ω U + c * Ω U := by
      simp only [stateFnN]; rw [hφU, ← hc]; ring
    rw [e]
    calc |(f U - p U) * Ω U + c * Ω U| ≤ |(f U - p U) * Ω U| + |c * Ω U| := abs_add_le _ _
      _ = |p U - f U| * |Ω U| + |c| * |Ω U| := by rw [abs_mul, abs_mul, abs_sub_comm]
      _ ≤ δ * B + δ * B := add_le_add
          (mul_le_mul (hp U).le (hΩB U) (abs_nonneg _) hδ0.le)
          (mul_le_mul hcδ (hΩB U) (abs_nonneg _) hδ0.le)
      _ = 2 * δ * B := by ring
  rw [dist_eq_norm, ← MemLp.toLp_sub]
  have hbd := Lp.norm_le_of_ae_bound (μ := μ) (p := 2)
    (f := (hφ.sub (memLp_of_contN (μ := μ) (continuous_stateFnN (μ := μ) hΩc p.continuous))).toLp
      (φ - stateFnN μ Ω p)) (by positivity : (0 : ℝ) ≤ 2 * δ * B)
    (by
      filter_upwards [(hφ.sub (memLp_of_contN (μ := μ)
        (continuous_stateFnN (μ := μ) hΩc p.continuous))).coeFn_toLp] with U hU
      rw [hU, Real.norm_eq_abs]; exact hpt U)
  have hone : (measureUnivNNReal μ : ℝ) = 1 := by simp [measureUnivNNReal]
  have hlt : 2 * δ * B < ε := by
    rw [hδ]
    have hB1 : 0 < B + 1 := by linarith
    rw [div_eq_mul_inv]
    have : 2 * (ε * (4 * (B + 1))⁻¹) * B = ε * (B / (2 * (B + 1))) := by field_simp; ring
    rw [this]
    have : B / (2 * (B + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  calc _ ≤ (measureUnivNNReal μ : ℝ) ^ ((2 : ENNReal).toReal⁻¹) * (2 * δ * B) := by
        exact_mod_cast hbd
    _ = 2 * δ * B := by rw [hone, Real.one_rpow, one_mul]
    _ < ε := hlt

end Words

/-! ## 3. The zero-flux levels at `SU(N)` -/

section Levels

open MassGap.CentreSectorSeedN (trivKN hSN halfKN bdd_trivKN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.KernelPower (iter conv hs Bdd)
open MassGap.RectTransfer (kT)
open MassGap.ZeroFluxSector (zk)
open MassGap.SliceKernelDefinite (gact)

variable {N : ℕ} [NeZero N] {i : Fin 4}

omit [NeZero N] in
/-- The kernel powers of the slice transfer are gauge invariant in their first argument. -/
theorem iter_gact_leftN {T : Dir i → ℕ} (β : ℝ) (h : TT i T → SUN.SU N) :
    ∀ (m : ℕ) (x y : SpT i T → SUN.SU N),
      iter (RectTransfer.hS i T N) (kT i T N β) m (gact h x) y
        = iter (RectTransfer.hS i T N) (kT i T N β) m x y
  | 0, x, y => SliceKernelPower.kT_gact_left β h x y
  | m + 1, x, y => by
      simp only [iter, conv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show kT i T N β (gact h x) z * _ = kT i T N β x z * _
      rw [SliceKernelPower.kT_gact_left β h x z]

/-- **The zero-flux kernel is gauge invariant in its first argument.** -/
theorem trivKN_gact_leftN (β : ℝ) (n : ℕ) (h : TT i (Tr n i) → SUN.SU N) (x y : SliceN N n i) :
    trivKN N β n i (gact h x) y = trivKN N β n i x y := by
  unfold trivKN zk halfKN
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  exact iter_gact_leftN β h _ x _

/-- The zero-flux kernel is continuous in its first argument. -/
theorem continuous_trivKN_leftN (β : ℝ) (n : ℕ) (y : SliceN N n i) :
    Continuous fun x => trivKN N β n i x y := by
  unfold trivKN zk halfKN
  have hc := SliceKernelPower.continuous_iter (μ := i) (T := Tr n i) (N := N) β (n / 2 - 1)
  exact continuous_const.mul (continuous_finsetSum _ fun g _ =>
    hc.comp (continuous_id.prodMk continuous_const))

/-- A level's eigenvalue is not zero. -/
theorem eigen_ne_zeroN {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv) (j : ι) : μv j ≠ 0 := by
  intro h0
  have := hL.energy j
  rw [h0] at this
  have hp := Real.exp_pos (-(E j * ((n : ℝ) * AsymptoticScaling.aRun N β)))
  rw [← this] at hp
  norm_num at hp

/-- A level is `μ_j⁻¹ ∫ trivKN(·, y) φ_j(y)`. -/
theorem level_eqN {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv) (j : ι) (x : SliceN N n i) :
    φ j x = (μv j)⁻¹ * ∫ y, trivKN N β n i x y * φ j y ∂(hSN N n i) := by
  rw [hL.eigen j x, ← mul_assoc, inv_mul_cancel₀ (eigen_ne_zeroN hL j), one_mul]

/-- **Every zero-flux level is gauge invariant.** -/
theorem level_gactN {β : ℝ} {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ}
    {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv) (j : ι) (h : TT i (Tr n i) → SUN.SU N)
    (x : SliceN N n i) : φ j (gact h x) = φ j x := by
  rw [level_eqN hL j (gact h x), level_eqN hL j x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show trivKN N β n i (gact h x) y * φ j y = trivKN N β n i x y * φ j y
  rw [trivKN_gact_leftN]

/-- A row integral of the zero-flux kernel against an integrable function is continuous. -/
theorem continuous_trivKN_rowN {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) {f : SliceN N n i → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (hSN N n i)) :
    Continuous fun x => ∫ y, trivKN N β n i x y * f y ∂(hSN N n i) := by
  have hb := bdd_trivKN (N := N) hβ n i
  obtain ⟨C, hC⟩ := hb.bdd
  refine continuous_of_dominated (bound := fun y => C * |f y|) (fun x => ?_)
    (fun x => Filter.Eventually.of_forall fun y => ?_) (hfi.abs.const_mul C)
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((hb.meas.comp (measurable_const.prodMk measurable_id)).mul hfm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC x y) (abs_nonneg _)
  · exact (continuous_trivKN_leftN β n y).mul continuous_const

/-- **Every zero-flux level is continuous** (at `β ≥ 0`, for measurable levels). -/
theorem continuous_levelN {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (j : ι) : Continuous (φ j) := by
  have hint : Integrable (φ j) (hSN N n i) :=
    (memLp_of_norm (hm j) (hL.norm j)).integrable one_le_two
  have he : φ j = fun x => (μv j)⁻¹ * ∫ y, trivKN N β n i x y * φ j y ∂(hSN N n i) :=
    funext (level_eqN hL j)
  rw [he]
  exact continuous_const.mul (continuous_trivKN_rowN hβ n (hm j) hint)

/-- **The ground level of the zero-flux kernel vanishes nowhere** (`SU(N)`, `β > 0`): the argument of
`LoopsGenerate.ground_ne_zero`. -/
theorem ground_ne_zeroN {β : ℝ} (hβ : 0 < β) {n : ℕ} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (x : SliceN N n i) : φ g₀ x ≠ 0 := by
  classical
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hk : Bdd (trivKN N β n i) := bdd_trivKN (N := N) hβ.le n i
  have hsym := MassGap.FiniteReadingFlux.symm_trivKN (N := N) hβ.le n i
  have hk0 : ∀ x y, 0 ≤ trivKN N β n i x y := fun x y =>
    (CentreSectorSeed.floor_pos β n i).le.trans
      (MassGap.FiniteReadingFlux.low_trivKN (N := N) hβ.le n i x y)
  have hφB : ∀ j, BM (φ j) := fun j =>
    ⟨hm j, _, abs_le_normN (continuous_levelN hβ.le hL hm j)⟩
  have horth : ∀ j l, ∫ x, φ j x * φ l x ∂(hSN N n i) = if j = l then 1 else 0 := by
    intro j l
    split_ifs with h
    · subst h; exact hL.norm j
    · exact hL.orth j l h
  have hen : (fun j => μv j ^ 2)
      = fun j => Real.exp (-(E j * ((n : ℝ) * AsymptoticScaling.aRun N β))) :=
    funext hL.energy
  have hsum : HasSum (fun j => μv j ^ 2) (hs (hSN N n i) (trivKN N β n i)) := by
    have hS := summable_sq (μ := hSN N n i) hk hφB horth hL.eigen
    have h := hS.hasSum
    rwa [hen, ← hL.hs_eq, ← hen] at h
  have ht : 0 ≤ (n : ℝ) * AsymptoticScaling.aRun N β :=
    mul_nonneg (Nat.cast_nonneg _) (AsymptoticScaling.aRun_pos hN1 hβ).le
  have hM : ∀ j, μv j ≤ |μv g₀| := by
    intro j
    have h1 : μv j ^ 2 ≤ μv g₀ ^ 2 := by
      rw [hL.energy, hL.energy, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right (hL.ground j) ht
      linarith
    exact (le_abs_self _).trans (sq_le_sq.mp h1 |>.trans_eq rfl)
  have hform : ∀ u : SliceN N n i → ℝ, BM u →
      qform (hSN N n i) (trivKN N β n i) u ≤ |μv g₀| * ∫ x, u x ^ 2 ∂(hSN N n i) :=
    fun u hu => qform_le hk hφB horth hL.eigen hsum (abs_nonneg _) hM hu
  have hdef := integral_defect_sq hk hsym hk0 (hφB g₀) (hL.eigen g₀) hform
  have hΩc := continuous_levelN hβ.le hL hm g₀
  have hAc : Continuous (fun x => |φ g₀ x|) := hΩc.abs
  have hAint : Integrable (fun x => |φ g₀ x|) (hSN N n i) := (hφB g₀).integrable.abs
  have hrow := continuous_trivKN_rowN hβ.le n (hm g₀).abs hAint
  have hpt : ∀ x, ∫ y, trivKN N β n i x y * |φ g₀ y| ∂(hSN N n i) = |μv g₀| * |φ g₀ x| := by
    intro x
    have h0 := SliceKernelPower.eq_zero_of_integral_eq_zero (μ := i) (T := Tr n i) (N := N)
      (f := fun x => (∫ y, trivKN N β n i x y * |φ g₀ y| ∂(hSN N n i) - |μv g₀| * |φ g₀ x|) ^ 2)
      ((hrow.sub (continuous_const.mul hAc)).pow 2) (fun _ => sq_nonneg _) hdef x
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  have hApos : 0 < ∫ y, |φ g₀ y| ∂(hSN N n i) := by
    rcases (integral_nonneg (fun y => abs_nonneg (φ g₀ y)) :
        0 ≤ ∫ y, |φ g₀ y| ∂(hSN N n i)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ y, |φ g₀ y| = 0 := fun y =>
        SliceKernelPower.eq_zero_of_integral_eq_zero (μ := i) (T := Tr n i) (N := N)
          hAc (fun _ => abs_nonneg _) h.symm y
      have h1 := hL.norm g₀
      have : (fun x => φ g₀ x * φ g₀ x) = fun _ => (0 : ℝ) := by
        funext y; rw [abs_eq_zero.mp (hz y), mul_zero]
      rw [this, integral_const, smul_zero] at h1
      exact zero_ne_one h1
  have hlow : CentreSectorSeed.floor β n i * ∫ y, |φ g₀ y| ∂(hSN N n i)
      ≤ ∫ y, trivKN N β n i x y * |φ g₀ y| ∂(hSN N n i) := by
    rw [← integral_const_mul]
    refine integral_mono (hAint.const_mul _)
      ((bm_row_fun hk x).mul ⟨(hm g₀).abs, _, fun y => by
        rw [abs_abs]; exact abs_le_normN hΩc y⟩).integrable fun y => ?_
    exact mul_le_mul_of_nonneg_right
      (MassGap.FiniteReadingFlux.low_trivKN (N := N) hβ.le n i x y) (abs_nonneg _)
  have hpos : 0 < |μv g₀| * |φ g₀ x| := by
    rw [← hpt x]
    exact lt_of_lt_of_le (mul_pos (CentreSectorSeed.floor_pos β n i) hApos) hlow
  intro h0
  rw [h0, abs_zero, mul_zero] at hpos
  exact lt_irrefl _ hpos

end Levels

/-! ## 4. `gen` on words -/

section Gen

open MassGap.CentreSectorSeedN (trivKN hSN)
open MassGap.CentreSectorSeed (Tr)
open MassGap.SliceKernelDefinite (gact)

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **Orbit separation by loop traces** on the slice of step `i` at side `n`: two configurations with the same
complex trace `tr hol_C` on every loop are gauge related. -/
def TracesSeparateN (n : ℕ) (i : Fin 4) : Prop :=
  ∀ V V' : SliceN N n i,
    (∀ C : Loop i (Tr n i), Matrix.trace (holN C V : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.trace (holN C V' : Matrix (Fin N) (Fin N) ℂ)) →
    ∃ h : TT i (Tr n i) → SUN.SU N, V' = gact h V

/-- **Orbit separation at `N = 2`** (`LoopsGenerate.giles`: the real traces of the loops at one site already
separate). -/
theorem tracesSeparateN_two {n : ℕ} (hn : 0 < n) (i : Fin 4) : TracesSeparateN 2 n i := by
  intro V V' h
  have hpos : ∀ j : {j : Fin 4 // j ≠ i}, 0 < CentreSectorSeed.Tr n i j := fun j => by
    simp only [CentreSectorSeed.Tr, RectWilson.tr, DoublingWilson.ext]
    positivity
  obtain ⟨g, hg⟩ := MassGap.LoopsGenerate.giles (fun j => ⟨0, hpos j⟩) V V'
    (fun C _ => congrArg Complex.re (h C))
  exact ⟨g, hg⟩

/-- **`gen` on words at every `N`, from orbit separation.** At `β > 0`, for measurable zero-flux levels, if the
loop traces separate gauge orbits, every excited level is in the `L²` closure of the span of the word states of
`Ω = φ_{g₀}`. -/
theorem excited_mem_closure_wordsN {β : ℝ} (hβ : 0 < β) {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι}
    {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (hsep : TracesSeparateN N n i) :
    ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoopsN (hSN N n i) (φ g₀) .words) : Set (Lp ℝ 2 (hSN N n i))) := by
  intro j hj
  have h1 : ∫ V, φ g₀ V ^ 2 ∂(hSN N n i) = 1 := by
    simpa only [sq] using hL.norm g₀
  refine mem_closure_words (continuous_levelN hβ.le hL hm g₀) (ground_ne_zeroN hβ hL hm) h1
    (continuous_levelN hβ.le hL hm j) (hL.orth g₀ j (Ne.symm hj)) (fun V V' hW => ?_) _
  have htr : ∀ C : Loop i (Tr n i), Matrix.trace (holN C V : Matrix (Fin N) (Fin N) ℂ)
      = Matrix.trace (holN C V' : Matrix (Fin N) (Fin N) ℂ) := by
    intro C
    have hre := hW (C, true)
    have him := hW (C, false)
    simp only [lfN, if_true, Bool.false_eq_true, if_false, wlN, imN] at hre him
    exact Complex.ext hre him
  obtain ⟨h, rfl⟩ := hsep V V' htr
  rw [level_gactN hL j h V, level_gactN hL g₀ h V]

/-- **`gen` in the form of the `SliceEndN.gen` field**, on `LoopFam.words`. -/
theorem gen_words_of_separation {β : ℝ} (hβ : 0 < β) {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι}
    {E : ι → ℝ} {φ : ι → SliceN N n i → ℝ} {μv : ι → ℝ} (hL : EigenLevelsN N β n i g₀ E φ μv)
    (hm : ∀ j, Measurable (φ j)) (hsep : TracesSeparateN N n i) (F : LoopFam) (hF : F = .words) :
    ∀ j, j ≠ g₀ → vecOf (hm j) (hL.norm j)
      ∈ closure (Submodule.span ℝ (allLoopsN (hSN N n i) (φ g₀) F) : Set (Lp ℝ 2 (hSN N n i))) := by
  subst hF
  exact excited_mem_closure_wordsN hβ hL hm hsep

end Gen

end MassGap.LoopsGenerateN

end

#print axioms MassGap.LoopsGenerateN.measurePreserving_cconj
#print axioms MassGap.LoopsGenerateN.measurePreserving_conjCfg
#print axioms MassGap.LoopsGenerateN.wlN_conjCfg
#print axioms MassGap.LoopsGenerateN.closure_single_le
#print axioms MassGap.LoopsGenerateN.not_mem_closure_single_of_odd
#print axioms MassGap.LoopsGenerateN.not_gen_single_of_odd
#print axioms MassGap.LoopsGenerateN.stateFnN_mem_span
#print axioms MassGap.LoopsGenerateN.mem_closure_words
#print axioms MassGap.LoopsGenerateN.level_gactN
#print axioms MassGap.LoopsGenerateN.continuous_levelN
#print axioms MassGap.LoopsGenerateN.ground_ne_zeroN
#print axioms MassGap.LoopsGenerateN.tracesSeparateN_two
#print axioms MassGap.LoopsGenerateN.excited_mem_closure_wordsN
#print axioms MassGap.LoopsGenerateN.gen_words_of_separation
