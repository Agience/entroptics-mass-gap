import Mathlib
import MassGap.VortexTwo
import MassGap.ChunkActivity
import MassGap.GapSideSheetPolymerWrap

/-!
# MassGap.VortexStrong — condensation of the rectangular vortex free energy at small `β > 0`

`VortexTwo.floor_of_vortexR_condensation_two` takes, at every zoom, condensation of
`vortexR (Lc (2^{K+1}) i) i ν β` along the doubling corner tori. `VortexTorus.condenses_vortexR_zero`
gives it at `β = 0`, where `VortexTwo.not_hyps_two_zero` shows the remaining inputs fail. This module
proves it at every `β ∈ (0, β₀]`, `β₀ = 1/4000000`, on the real `SU(2)` objects, with the explicit rate
`rhoS β = −log (4225 e (1 − e^{−2β}))`.

## 1. The patterned polymer gas (`zwP`, `actP`, `ZRp_eq_polymerZ`)

For a plaquette pattern `ζ`, `zwP L β ζ E = ∫ ∏_{q∈E} (e^{−β φ(ζ_q U_q)} − 1)` (product Haar).
`ZRp_eq_sum`: `ZRp L β ζ = Σ_E zwP L β ζ E`. `zwP_union`, `zwP_sup_eq_prod`: the weight factorises
over plaquette sets with disjoint link supports (`WilsonReal.block_integral_factor`), so over every
family compatible under `ChunkActivity.Inc`. With `actP` the weight on nonempty touch-connected sets
and `0` elsewhere, `ZRp_eq_polymerZ`: `ZRp L β ζ = MatchAt.Z (Inc (rbd L)) (actP L β ζ) univ.powerset`
at every `β` and every pattern; `ζ = 1` is `ZR L 2 β`. `actP_abs_le`: `|actP| ≤ (1 − e^{−2β})^{|X|}`.

## 2. Small sets do not see the sheet (`actP_sheet_eq`)

`zwP_coboundary`: a centre-valued link field `χ` moves the pattern by its coboundary.
`rhol_strip`: flipping the `b`-links with `0 < x_a ≤ s`, `x_b = c` has coboundary
`sheetAt 0 c · sheetAt s c`. Two strips carry `sheetR L a b` to `sheetAt s t` for every `s < L a`,
`t < L b` (`zwP_sheet_move`). A set whose weight sees the sheet meets every positioned sheet, so it has
at least `L a · L b` plaquettes (`card_ge_of_zwP_ne`); every set of fewer plaquettes carries the
untwisted activity (`actP_sheet_eq`).

## 3. Dobrushin's criterion (`touchDeg_rbd_le`, `dob_actP`)

`linkMult_rbd_le`, `touchDeg_rbd_le`: a link of the rectangular torus lies in at most `16`
plaquettes, a plaquette touches at most `64`, at every extent. So at most `4225ⁿ` connected sets of
size `n` contain a plaquette (`card_connSets_rbd_le`). With `cw y X = yᴺ` (`N = |X|`) on the nonempty
touch-connected sets, `y = (1 − e^{−2β}) e`, and `x = 4225 y ≤ 1/128`:
`sum_site_cw_le`: `Σ_{X∋v} cw ≤ x/(1 − x)`; `sum_site_cw_tail_le`: the sets of size at least `m`
give at most `xᵐ/(1 − x)`; `dob_actP`: `MatchAt.Dob (Inc (rbd L)) (actP L β ζ) (cw y)` for every
pattern `ζ`.

## 4. The vortex free energy (`vortexR_le_tail`, `vortexR_le_card`)

`Z_le_exp_sdiff` (with `MatchAt.Z_sdiff_le`): removing a set `B` of polymers changes `log Z` by at most
`Σ_B c` under `Dob c`. The twisted and untwisted gases agree off the sets of at least `L a L b`
plaquettes, so `vortexR L a b β ≤ 2 Σ_{|X| ≥ L_a L_b} cw y X ≤ 4 |RPlaq L| x^{L_a L_b}`
(`vortexR_le_card`), for `a ≠ b`, `β > 0`, `x ≤ 1/128`, `L_a L_b ≥ 1`.

## 5. Condensation along the doubling tori (`condenses_vortexR_strong`)

On `Lc (2^{K+1}) i`, `|RPlaq| ≤ 256 A²` with `A = L_i L_ν` (`card_rplaq_Lc_le`), so
`vortexR ≤ 1024 A² x^A` and `VortexCondense.condenses_of_sublinear` gives
`Condenses (vortexR (Lc (2^{K+1}) i) i ν β) A (rhoS β)` for `0 < β ≤ β₀`, `ν ≠ i`, with
`rhoS β ≥ log 128 > 0` (`rhoS_pos`).

## 6. What this gives the zoom theorems (`StrongLoopTension`, `floor_of_strong`)

`StrongLoopTension β i ν` names the remaining inputs at one coupling: for every corner family `o`,
the limit `K → ∞` of `wloopR (Lc (2^{K+1}) i) i ν (2^p) (2^p) (o K) β` exists for every `p` and has
`HasTension` with some `σ > 0`. No declaration proves it. `floor_of_strong`: at one `β ∈ (0, β₀]`,
`ChessboardFlux` on every doubling torus and `StrongLoopTension β i ν` give the hypotheses of
`floor_of_vortexR_condensation_two` on the constant zoom (`β j = β`, `a j = 1`,
`ρ₀ = rhoS β`), with condensation discharged by `condenses_vortexR_strong`, and its conclusion
`Floor (fun _ => σ)` together with `rhoS β ≤ σ`. At such a `β` the condensation input of that
theorem is proved; `ChessboardFlux` and `StrongLoopTension` are inputs. On the constant zoom
`Floor (fun _ => σ)` is `0 < σ`: it is a floor at one coupling and carries no uniformity in the zoom
or in physical units. `(0, β₀]` is strong coupling; condensation at the rate `ρ₀ (a j)²` along a zoom
with `β j` toward weak coupling is not given here.

DERIVED (module-wide): `2` the `SU(2)` matrix size and the top of the Wilson density's range in
`1 − e^{−2β}`; `16 = 4 · 4` boundary-word slots times second directions; `64 = 4 · 16`;
`4225 = (64 + 1)²` the connected-set entropy of `StrongCoupling.card_connSets_le`; `e` the Dobrushin
weight `a = 1` per plaquette; `128 = 2 · 64` the per-site sum `2x` times the touch degree;
`1/2 ≥ x` makes `x/(1 − x) ≤ 2x`; `4 = 2 · 2` the two gases times that `2`; `256 = 16 · 16`,
`1024 = 4 · 256`; `3 > e`; `β₀ = 1/4000000` places `4225 · 3 · 2β₀ < 1/128`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.VortexStrong

open MeasureTheory Filter Topology Finset
open MassGap.RectWilson MassGap.GapSideVortexRect MassGap.VortexCondense MassGap.CompactGauge
open MassGap.StrongCoupling (wfun wfun_apply Touch linkSupp touchNbrs mem_touchNbrs touchDeg
  touchNbrs_card_le touchNbrs_card_le_touchDeg linkMult connSets mem_connSets card_connSets_le
  supp_subset_biUnion)
open MassGap.PolymerCount (TouchConnected ConnSupp Decay CountAt countAt_of_connSets_card)
open MassGap.ChunkActivity (Inc comps comps_mem comps_sup comps_compat comps_family Admissible
  rate rate_nonneg rate_pos rate_lt_one wfun_abs_le)
open MassGap.TwistedTraceBound (negOne negOne_mul_self)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 1. The patterned polymer gas -/

section Patterned

variable (L : Fin 4 → ℕ)

/-- **The weight of an activated set under a pattern**:
`∫ ∏_{q∈E} (e^{−β φ(ζ_q U_q)} − 1)` against product Haar. -/
def zwP (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (E : Finset (RPlaq L)) : ℝ :=
  ∫ U : RLink L → SUN.SU 2, ∏ q ∈ E, wfun β (wd (ζ q * rhol L q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))

theorem continuous_wfun (β : ℝ) : Continuous (wfun β) := by
  have h : wfun β = fun x => Real.exp (-(β * x)) - 1 := funext (wfun_apply β)
  rw [h]
  fun_prop

theorem continuous_prodP (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (E : Finset (RPlaq L)) :
    Continuous fun U : RLink L → SUN.SU 2 => ∏ q ∈ E, wfun β (wd (ζ q * rhol L q U)) :=
  continuous_finsetProd _ fun q _ => (continuous_wfun β).comp
    (WilsonAction.continuous_wilsonDensity.comp (continuous_const.mul (continuous_rhol L q)))

/-- **The subset expansion of the patterned torus**: `ZRp L β ζ = Σ_E zwP L β ζ E`. -/
theorem ZRp_eq_sum (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ZRp L β ζ = ∑ E ∈ (univ : Finset (RPlaq L)).powerset, zwP L β ζ E := by
  unfold ZRp zwP
  rw [← integral_finsetSum _ fun E _ =>
    MovedTorusDecimation.integrable_of_continuous (continuous_prodP L β ζ E)]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))
    = ∑ E ∈ (univ : Finset (RPlaq L)).powerset, ∏ q ∈ E, wfun β (wd (ζ q * rhol L q U))
  have h1 : -β * ∑ q, wd (ζ q * rhol L q U) = ∑ q, -(β * wd (ζ q * rhol L q U)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [h1, Real.exp_sum]
  have hone : ∏ q : RPlaq L, Real.exp (-(β * wd (ζ q * rhol L q U)))
      = ∏ q : RPlaq L, (wfun β (wd (ζ q * rhol L q U)) + 1) :=
    Finset.prod_congr rfl fun q _ => by rw [wfun_apply]; ring
  rw [hone, Finset.prod_add]
  exact Finset.sum_congr rfl fun X _ => by simp

/-- `U` read on the links of `S`, extended by `1`. -/
def extU (S : Finset (RLink L)) (v : S → SUN.SU 2) : RLink L → SUN.SU 2 :=
  fun l => if h : l ∈ S then v ⟨l, h⟩ else 1

theorem continuous_extU (S : Finset (RLink L)) : Continuous (extU L S) := by
  refine continuous_pi fun l => ?_
  by_cases h : l ∈ S
  · have e : (fun v : S → SUN.SU 2 => extU L S v l) = fun v => v ⟨l, h⟩ :=
      funext fun v => dif_pos h
    rw [e]
    exact continuous_apply _
  · have e : (fun v : S → SUN.SU 2 => extU L S v l) = fun _ => 1 :=
      funext fun v => dif_neg h
    rw [e]
    exact continuous_const

theorem extU_eq (S : Finset (RLink L)) (U : RLink L → SUN.SU 2) {l : RLink L} (hl : l ∈ S) :
    extU L S (fun i : S => U i.val) l = U l := by
  unfold extU
  rw [dif_pos hl]

theorem rhol_extU (S : Finset (RLink L)) (U : RLink L → SUN.SU 2) (q : RPlaq L)
    (hq : ∀ l ∈ (rbd L q).map Prod.fst, l ∈ S) :
    rhol L q (extU L S (fun i : S => U i.val)) = rhol L q U := by
  have h1 : (q.1.1, q.2) ∈ S := hq _ (by simp [rbd])
  have h2 : (q.1.2, rshift L q.1.1 q.2) ∈ S := hq _ (by simp [rbd])
  have h3 : (q.1.1, rshift L q.1.2 q.2) ∈ S := hq _ (by simp [rbd])
  have h4 : (q.1.2, q.2) ∈ S := hq _ (by simp [rbd])
  unfold rhol
  rw [extU_eq L S U h1, extU_eq L S U h2, extU_eq L S U h3, extU_eq L S U h4]

/-- **The weight factorises across link-disjoint plaquette sets.** -/
theorem zwP_union (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (X Y : Finset (RPlaq L))
    (S T : Finset (RLink L)) (hST : Disjoint S T) (hXY : Disjoint X Y)
    (hX : ∀ q ∈ X, ∀ l ∈ (rbd L q).map Prod.fst, l ∈ S)
    (hY : ∀ q ∈ Y, ∀ l ∈ (rbd L q).map Prod.fst, l ∈ T) :
    zwP L β ζ (X ∪ Y) = zwP L β ζ X * zwP L β ζ Y := by
  have hfac := WilsonReal.block_integral_factor (N := 2) S T hST
    (fun v => ∏ q ∈ X, wfun β (wd (ζ q * rhol L q (extU L S v))))
    (fun v => ∏ q ∈ Y, wfun β (wd (ζ q * rhol L q (extU L T v))))
    ((continuous_prodP L β ζ X).comp (continuous_extU L S)).measurable
    ((continuous_prodP L β ζ Y).comp (continuous_extU L T)).measurable
  have e1 : ∀ U : RLink L → SUN.SU 2,
      ∏ q ∈ X, wfun β (wd (ζ q * rhol L q (extU L S (fun i : S => U i.val))))
        = ∏ q ∈ X, wfun β (wd (ζ q * rhol L q U)) := fun U =>
    Finset.prod_congr rfl fun q hq => by rw [rhol_extU L S U q (hX q hq)]
  have e2 : ∀ U : RLink L → SUN.SU 2,
      ∏ q ∈ Y, wfun β (wd (ζ q * rhol L q (extU L T (fun i : T => U i.val))))
        = ∏ q ∈ Y, wfun β (wd (ζ q * rhol L q U)) := fun U =>
    Finset.prod_congr rfl fun q hq => by rw [rhol_extU L T U q (hY q hq)]
  unfold zwP
  calc ∫ U, ∏ q ∈ X ∪ Y, wfun β (wd (ζ q * rhol L q U))
        ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = ∫ U, (∏ q ∈ X, wfun β (wd (ζ q * rhol L q (extU L S (fun i : S => U i.val)))))
          * ∏ q ∈ Y, wfun β (wd (ζ q * rhol L q (extU L T (fun i : T => U i.val))))
          ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
        integral_congr_ae (Eventually.of_forall fun U => by
          dsimp only
          rw [e1 U, e2 U, Finset.prod_union hXY])
    _ = (∫ U, ∏ q ∈ X, wfun β (wd (ζ q * rhol L q (extU L S (fun i : S => U i.val))))
          ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)))
        * ∫ U, ∏ q ∈ Y, wfun β (wd (ζ q * rhol L q (extU L T (fun i : T => U i.val))))
          ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := hfac
    _ = _ := congrArg₂ (fun a b => a * b)
        (integral_congr_ae (Eventually.of_forall fun U => e1 U))
        (integral_congr_ae (Eventually.of_forall fun U => e2 U))

/-- **The weight factorises over a compatible family.** -/
theorem zwP_sup_eq_prod (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (T : Finset (Finset (RPlaq L)))
    (hT : MatchAt.Compat (Inc (rbd L)) T) :
    zwP L β ζ (T.sup id) = ∏ X ∈ T, zwP L β ζ X := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.prod_empty]
      unfold zwP
      simp
  | @insert X T hX ih =>
      have hT' : MatchAt.Compat (Inc (rbd L)) T := fun x hx y hy hxy =>
        hT x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have hXT : ∀ Y ∈ T, ¬ Inc (rbd L) X Y := fun Y hY =>
        hT X (Finset.mem_insert_self _ _) Y (Finset.mem_insert_of_mem hY)
          (fun e => hX (e ▸ hY))
      rw [Finset.sup_insert, Finset.prod_insert hX, ← ih hT', id_eq, Finset.sup_eq_union]
      have hdisj : Disjoint X (T.sup id) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        obtain ⟨Y, hY, hpY⟩ := Finset.mem_sup.1 hp'
        exact hXT Y hY ⟨p, hp, p, hpY, Or.inl rfl⟩
      have hlinks : Disjoint (X.biUnion (linkSupp (rbd L)))
          ((T.sup id).biUnion (linkSupp (rbd L))) := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.1 hl
        obtain ⟨q, hq, hlq⟩ := Finset.mem_biUnion.1 hl'
        obtain ⟨Y, hY, hqY⟩ := Finset.mem_sup.1 hq
        exact hXT Y hY ⟨p, hp, q, hqY, Or.inr ⟨l, hlp, hlq⟩⟩
      exact zwP_union L β ζ X (T.sup id) _ _ hlinks hdisj (supp_subset_biUnion (rbd L) X)
        (supp_subset_biUnion (rbd L) (T.sup id))

open scoped Classical in
/-- **The patterned polymer activity**: `zwP` on nonempty touch-connected sets, `0` elsewhere. -/
def actP (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)) : ℝ :=
  if X.Nonempty ∧ TouchConnected (rbd L) X then zwP L β ζ X else 0

theorem actP_of (β : ℝ) (ζ : RPlaq L → SUN.SU 2) {X : Finset (RPlaq L)}
    (h : X.Nonempty ∧ TouchConnected (rbd L) X) : actP L β ζ X = zwP L β ζ X := by
  classical
  unfold actP
  exact if_pos h

theorem actP_ne_zero (β : ℝ) (ζ : RPlaq L → SUN.SU 2) {X : Finset (RPlaq L)}
    (h : actP L β ζ X ≠ 0) : X.Nonempty ∧ TouchConnected (rbd L) X := by
  classical
  by_contra hn
  unfold actP at h
  exact h (if_neg hn)

theorem actP_of_not (β : ℝ) (ζ : RPlaq L → SUN.SU 2) {X : Finset (RPlaq L)}
    (h : ¬ (X.Nonempty ∧ TouchConnected (rbd L) X)) : actP L β ζ X = 0 := by
  classical
  unfold actP
  exact if_neg h

/-- **The weight of a set is the product of its component activities.** -/
theorem zwP_eq_prod_comps (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (E : Finset (RPlaq L)) :
    zwP L β ζ E = ∏ C ∈ comps (rbd L) E, actP L β ζ C := by
  conv_lhs => rw [← comps_sup (rbd L) E]
  rw [zwP_sup_eq_prod L β ζ _ (comps_compat (rbd L) E)]
  exact Finset.prod_congr rfl (fun C hC =>
    (actP_of L β ζ ⟨(comps_mem hC).1, (comps_mem hC).2.1⟩).symm)

/-- **The patterned torus is a hard-core polymer gas**: `ZRp L β ζ` is the polymer partition function
of `actP L β ζ` under `Inc (rbd L)`, at every coupling and every pattern. -/
theorem ZRp_eq_polymerZ (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ZRp L β ζ = MatchAt.Z (Inc (rbd L)) (actP L β ζ) (univ : Finset (RPlaq L)).powerset := by
  classical
  rw [ZRp_eq_sum L β ζ]
  unfold MatchAt.Z
  symm
  refine Finset.sum_bij_ne_zero (fun (T : Finset (Finset (RPlaq L))) _ _ => T.sup id) ?_ ?_ ?_ ?_
  · intro T hT _
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨X, hX, hxX⟩ := Finset.mem_sup.1 hx
    have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1) hX
    exact Finset.mem_powerset.1 this hxX
  · intro T₁ h₁ hn₁ T₂ h₂ hn₂ heq
    have ha₁ : Admissible (rbd L) T₁ := ⟨fun X hX =>
      actP_ne_zero L β ζ (Finset.prod_ne_zero_iff.1 hn₁ X hX), (Finset.mem_filter.1 h₁).2⟩
    have ha₂ : Admissible (rbd L) T₂ := ⟨fun X hX =>
      actP_ne_zero L β ζ (Finset.prod_ne_zero_iff.1 hn₂ X hX), (Finset.mem_filter.1 h₂).2⟩
    rw [← comps_family (rbd L) ha₁, ← comps_family (rbd L) ha₂]
    exact congrArg (comps (rbd L)) heq
  · intro E hE hne
    refine ⟨comps (rbd L) E, ?_, ?_, comps_sup (rbd L) E⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (fun C hC => ?_), comps_compat (rbd L) E⟩
      exact Finset.mem_powerset.2 ((comps_mem hC).2.2.trans (Finset.mem_powerset.1 hE))
    · rw [← zwP_eq_prod_comps]
      exact hne
  · intro T hT hn
    have ha : Admissible (rbd L) T := ⟨fun X hX =>
      actP_ne_zero L β ζ (Finset.prod_ne_zero_iff.1 hn X hX), (Finset.mem_filter.1 hT).2⟩
    rw [zwP_sup_eq_prod L β ζ T ha.2]
    exact Finset.prod_congr rfl (fun X hX => actP_of L β ζ (ha.1 X hX))

/-- **The weight bound**: `|zwP L β ζ X| ≤ (1 − e^{−2β})^{|X|}` for `β ≥ 0`, every pattern. -/
theorem zwP_abs_le {β : ℝ} (hβ : 0 ≤ β) (ζ : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)) :
    |zwP L β ζ X| ≤ rate β ^ X.card := by
  have hpt : ∀ U : RLink L → SUN.SU 2,
      ‖∏ q ∈ X, wfun β (wd (ζ q * rhol L q U))‖ ≤ rate β ^ X.card := by
    intro U
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ q ∈ X, |wfun β (wd (ζ q * rhol L q U))| ≤ ∏ _q ∈ X, rate β :=
          Finset.prod_le_prod (fun q _ => abs_nonneg _) (fun q _ =>
            wfun_abs_le hβ (WilsonAction.wilsonDensity_nonneg (by norm_num) _)
              (WilsonAction.wilsonDensity_le_two (by norm_num) _))
      _ = rate β ^ X.card := Finset.prod_const _
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem actP_abs_le {β : ℝ} (hβ : 0 ≤ β) (ζ : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)) :
    |actP L β ζ X| ≤ rate β ^ X.card := by
  classical
  unfold actP
  split_ifs
  · exact zwP_abs_le L hβ ζ X
  · rw [abs_zero]
    exact pow_nonneg (rate_nonneg hβ) _

end Patterned

/-! ## 2. Small sets do not see the sheet -/

section Sheet

variable (L : Fin 4 → ℕ)

theorem rhol_mul_central (m U : RLink L → SUN.SU 2) (hm : ∀ l g, m l * g = g * m l)
    (q : RPlaq L) : rhol L q (fun l => m l * U l) = rhol L q m * rhol L q U := by
  unfold rhol
  exact GapSideVortexStepSign.four_central _ _ _ _ (hm _) (hm _) (hm _)

/-- **A centre relabelling moves the pattern by its coboundary.** -/
theorem zwP_coboundary (β : ℝ) (ζ : RPlaq L → SUN.SU 2) (χ : RLink L → SUN.SU 2)
    (hχ : ∀ l g, χ l * g = g * χ l) (X : Finset (RPlaq L)) :
    zwP L β ζ X = zwP L β (fun q => ζ q * rhol L q χ) X := by
  let e : (RLink L → SUN.SU 2) ≃ᵐ (RLink L → SUN.SU 2) :=
    MeasurableEquiv.piCongrRight fun l => MeasurableEquiv.mulLeft (χ l)
  have mp : MeasurePreserving e (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
    measurePreserving_pi _ _ fun l => measurePreserving_mul_left (probHaar (SUN.SU 2)) (χ l)
  unfold zwP
  calc ∫ U, ∏ q ∈ X, wfun β (wd (ζ q * rhol L q U))
        ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      = ∫ U, ∏ q ∈ X, wfun β (wd (ζ q * rhol L q (e U)))
          ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
        (mp.integral_comp' (fun U => ∏ q ∈ X, wfun β (wd (ζ q * rhol L q U)))).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        show ∏ q ∈ X, wfun β (wd (ζ q * rhol L q (fun l => χ l * U l)))
          = ∏ q ∈ X, wfun β (wd (ζ q * rhol L q χ * rhol L q U))
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [rhol_mul_central L χ U hχ q, mul_assoc]

/-- **The sheet at position `(u, v)`** of the plane `(a, b)`. -/
def sheetAt (a b : Fin 4) (u v : ℕ) (q : RPlaq L) : SUN.SU 2 :=
  if (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ (q.2 a).val = u ∧ (q.2 b).val = v then negOne else 1

/-- **A strip**: `−1` on the `b`-links with `0 < x_a ≤ s`, `x_b = c`. -/
def strip (a b : Fin 4) (s c : ℕ) (l : RLink L) : SUN.SU 2 :=
  if l.1 = b ∧ 0 < (l.2 a).val ∧ (l.2 a).val ≤ s ∧ (l.2 b).val = c then negOne else 1

theorem sheetR_eq_sheetAt (a b : Fin 4) : sheetR L a b = sheetAt L a b 0 0 := rfl

theorem sheetAt_swap (a b : Fin 4) (u v : ℕ) : sheetAt L b a v u = sheetAt L a b u v := by
  funext q
  unfold sheetAt
  exact if_congr (by tauto) rfl rfl

theorem sheetAt_mul_self (a b : Fin 4) (u v : ℕ) (q : RPlaq L) :
    sheetAt L a b u v q * sheetAt L a b u v q = 1 := by
  unfold sheetAt
  split_ifs
  · exact negOne_mul_self
  · exact mul_one 1

theorem strip_central (a b : Fin 4) (s c : ℕ) (l : RLink L) (g : SUN.SU 2) :
    strip L a b s c l * g = g * strip L a b s c l := by
  unfold strip
  split_ifs
  · exact GapSideVortexStepSign.negOne_central g
  · rw [one_mul, mul_one]

theorem rshift_self (κ : Fin 4) (x : RSite L) : rshift L κ x κ = finRotate (L κ) (x κ) := by
  simp [rshift]

theorem rshift_apply_ne {κ ν : Fin 4} (h : κ ≠ ν) (x : RSite L) : rshift L ν x κ = x κ := by
  unfold rshift
  exact Function.update_of_ne h _ _

theorem rhol_diag (i : Fin 4) (x : RSite L) (U : RLink L → SUN.SU 2) :
    rhol L ((i, i), x) U = 1 := by
  simp only [rhol]
  group

/-- **The coboundary of a strip** is the sheet at `(0, c)` times the sheet at `(s, c)`. -/
theorem rhol_strip {a b : Fin 4} (hab : a ≠ b) {s : ℕ} (hs : s < L a) (c : ℕ) (q : RPlaq L) :
    rhol L q (strip L a b s c) = sheetAt L a b 0 c q * sheetAt L a b s c q := by
  have hz : (negOne : SUN.SU 2)⁻¹ = negOne := GapSideTwistFlat.negOne_inv
  have hzz : (negOne : SUN.SU 2) * negOne = 1 := negOne_mul_self
  have hba : b ≠ a := Ne.symm hab
  obtain ⟨⟨i, j⟩, x⟩ := q
  have hxa := (x a).isLt
  by_cases hij : i = j
  · subst hij
    rw [rhol_diag]
    have hd : ¬ ((i, i) = (a, b) ∨ (i, i) = (b, a)) := by
      rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;> exact hab (by rw [← h.1, ← h.2])
    simp only [sheetAt, hd, false_and, if_false, mul_one]
  by_cases hib : i = b
  · subst hib
    by_cases hja : j = a
    · subst hja
      simp only [rhol, strip, sheetAt, rshift_self, rshift_apply_ne L hab, rshift_apply_ne L hba, hab,
        false_and, if_false, inv_one, mul_one, true_and, or_true]
      rcases GapSideSheetPolymerWrap.rot_val (x j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;>
        split_ifs <;>
        first | rfl | (simp only [hz, hzz, inv_one, mul_one, one_mul]; done) | (exfalso; omega)
    · have hja' : j ≠ a := hja
      have hjb : j ≠ i := Ne.symm hij
      have hd : ¬ ((i, j) = (a, i) ∨ (i, j) = (i, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hba h.1
        · exact hja' h.2
      simp only [rhol, strip, sheetAt, hd, false_and, if_false, mul_one,
        rshift_apply_ne L hja'.symm, rshift_apply_ne L hjb.symm, hjb, inv_one]
      split_ifs <;> first | rfl | simp only [hz, hzz, inv_one, mul_one]
  · by_cases hjb : j = b
    · subst hjb
      by_cases hia : i = a
      · subst hia
        simp only [rhol, strip, sheetAt, rshift_self, rshift_apply_ne L hba, rshift_apply_ne L hab,
          hab, false_and, if_false, inv_one, mul_one, one_mul, true_and, true_or]
        rcases GapSideSheetPolymerWrap.rot_val (x i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;>
          split_ifs <;>
          first | rfl | (simp only [hz, hzz, inv_one, mul_one, one_mul]; done) | (exfalso; omega)
      · have hd : ¬ ((i, j) = (a, j) ∨ (i, j) = (j, a)) := by
          rintro (h | h) <;> simp only [Prod.mk.injEq] at h
          · exact hia h.1
          · exact hib h.1
        simp only [rhol, strip, sheetAt, hd, false_and, if_false, mul_one, one_mul,
          rshift_apply_ne L (Ne.symm hia), rshift_apply_ne L (Ne.symm hij), hib, inv_one]
        split_ifs <;> first | rfl | simp only [hz, hzz, inv_one, mul_one]
    · have hd : ¬ ((i, j) = (a, b) ∨ (i, j) = (b, a)) := by
        rintro (h | h) <;> simp only [Prod.mk.injEq] at h
        · exact hjb h.2
        · exact hib h.1
      simp only [rhol, strip, sheetAt, hd, hib, hjb, false_and, if_false, mul_one, inv_one]

/-- **Two strips carry the sheet to any position**: for `s < L a`, `t < L b`, the weight of every
set under `sheetR L a b` equals its weight under `sheetAt L a b s t`. -/
theorem zwP_sheet_move (β : ℝ) {a b : Fin 4} (hab : a ≠ b) {s t : ℕ} (hs : s < L a)
    (ht : t < L b) (X : Finset (RPlaq L)) :
    zwP L β (sheetR L a b) X = zwP L β (sheetAt L a b s t) X := by
  rw [zwP_coboundary L β _ (strip L a b s 0) (strip_central L a b s 0) X]
  have e1 : (fun q => sheetR L a b q * rhol L q (strip L a b s 0)) = sheetAt L a b s 0 := by
    funext q
    rw [rhol_strip L hab hs 0 q, sheetR_eq_sheetAt, ← mul_assoc, sheetAt_mul_self, one_mul]
  rw [e1, zwP_coboundary L β _ (strip L b a t s) (strip_central L b a t s) X]
  have e2 : (fun q => sheetAt L a b s 0 q * rhol L q (strip L b a t s)) = sheetAt L a b s t := by
    funext q
    rw [rhol_strip L (Ne.symm hab) ht s q, sheetAt_swap L a b s 0, sheetAt_swap L a b s t,
      ← mul_assoc, sheetAt_mul_self, one_mul]
  rw [e2]

/-- **A set whose weight sees the sheet wraps the plane**: it has at least `L a · L b` plaquettes. -/
theorem card_ge_of_zwP_ne (β : ℝ) {a b : Fin 4} (hab : a ≠ b) {X : Finset (RPlaq L)}
    (h : zwP L β (sheetR L a b) X ≠ zwP L β (fun _ => 1) X) : L a * L b ≤ X.card := by
  have key : ∀ p : Fin (L a) × Fin (L b),
      ∃ q ∈ X, (q.2 a).val = p.1.val ∧ (q.2 b).val = p.2.val := by
    intro p
    by_contra hn
    push Not at hn
    apply h
    rw [zwP_sheet_move L β hab p.1.isLt p.2.isLt X]
    unfold zwP
    refine integral_congr_ae (Eventually.of_forall fun U => Finset.prod_congr rfl fun q hq => ?_)
    have hq1 : sheetAt L a b p.1.val p.2.val q = 1 := by
      unfold sheetAt
      rw [if_neg]
      rintro ⟨_, h1, h2⟩
      exact hn q hq h1 h2
    rw [hq1]
  choose f hfX hf using key
  have hinj : Set.InjOn f ↑(Finset.univ : Finset (Fin (L a) × Fin (L b))) := by
    intro p _ p' _ he
    have h1 := (hf p).1
    have h2 := (hf p).2
    rw [he, (hf p').1] at h1
    rw [he, (hf p').2] at h2
    exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)
  have hc := Finset.card_le_card_of_injOn f (fun p _ => hfX p) hinj
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hc
  exact hc

/-- **Every set of fewer than `L a · L b` plaquettes carries the untwisted activity.** -/
theorem actP_sheet_eq (β : ℝ) {a b : Fin 4} (hab : a ≠ b) {X : Finset (RPlaq L)}
    (hX : X.card < L a * L b) :
    actP L β (sheetR L a b) X = actP L β (fun _ => 1) X := by
  classical
  unfold actP
  split_ifs
  · by_contra hne
    exact absurd (card_ge_of_zwP_ne L β hab hne) (not_le.2 hX)
  · rfl

end Sheet

/-! ## 3. Dobrushin's criterion -/

section Dob

variable (L : Fin 4 → ℕ)

theorem unshift_rshift (μ : Fin 4) (x : RSite L) : (rsiteShift L μ).symm (rshift L μ x) = x :=
  (rsiteShift L μ).symm_apply_apply x

open scoped Classical in
/-- **A link of the rectangular torus lies in at most `16` plaquettes**, at every extent. -/
theorem linkMult_rbd_le (l : RLink L) : linkMult (rbd L) l ≤ 16 := by
  classical
  obtain ⟨δ, y⟩ := l
  set g : Fin 4 × Fin 4 → RPlaq L := fun z =>
    if z.1 = 0 then ((δ, z.2), y)
    else if z.1 = 1 then ((z.2, δ), (rsiteShift L z.2).symm y)
    else if z.1 = 2 then ((δ, z.2), (rsiteShift L z.2).symm y)
    else ((z.2, δ), y) with hg
  have hsub : (Finset.univ.filter (fun q : RPlaq L => (δ, y) ∈ linkSupp (rbd L) q))
      ⊆ Finset.image g Finset.univ := by
    intro q hq
    obtain ⟨⟨μ, ν⟩, x⟩ := q
    have hmem := (Finset.mem_filter.mp hq).2
    simp only [linkSupp, rbd, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Prod.mk.injEq] at hmem
    refine Finset.mem_image.mpr ?_
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨(0, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · exact ⟨(1, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_rshift]⟩
    · exact ⟨(2, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_rshift]⟩
    · exact ⟨(3, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · simp at h
  unfold linkMult
  calc (Finset.univ.filter (fun q : RPlaq L => (δ, y) ∈ linkSupp (rbd L) q)).card
      ≤ (Finset.image g Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 × Fin 4)).card := Finset.card_image_le
    _ = 16 := by simp

theorem linkSupp_rbd_card_le (q : RPlaq L) : (linkSupp (rbd L) q).card ≤ 4 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simp [rbd]

open scoped Classical in
/-- **A plaquette of the rectangular torus touches at most `64` plaquettes**, at every extent. -/
theorem touchDeg_rbd_le : touchDeg (rbd L) ≤ 64 := by
  classical
  refine Finset.sup_le (fun p _ => ?_)
  refine le_trans (touchNbrs_card_le (rbd L) p) ?_
  calc ∑ l ∈ linkSupp (rbd L) p, linkMult (rbd L) l
      ≤ ∑ _l ∈ linkSupp (rbd L) p, 16 := Finset.sum_le_sum (fun l _ => linkMult_rbd_le L l)
    _ = (linkSupp (rbd L) p).card * 16 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * 16 := Nat.mul_le_mul_right _ (linkSupp_rbd_card_le L p)
    _ = 64 := by norm_num

open scoped Classical in
/-- **At most `4225ⁿ` touch-connected sets of size `n` contain a plaquette.** -/
theorem card_connSets_rbd_le (p₀ : RPlaq L) (m : ℕ) :
    (connSets (rbd L) p₀ m).card ≤ 4225 ^ m := by
  refine le_trans (card_connSets_le _ p₀ m) ?_
  have hdeg : touchDeg (rbd L) + 1 ≤ 65 := by
    have := touchDeg_rbd_le L
    omega
  have h2 : (touchDeg (rbd L) + 1) ^ 2 ≤ 4225 := by
    calc (touchDeg (rbd L) + 1) ^ 2 ≤ 65 ^ 2 := Nat.pow_le_pow_left hdeg 2
      _ = 4225 := by norm_num
  exact Nat.pow_le_pow_left h2 m

open scoped Classical in
/-- **The Dobrushin weight**: `y^{|X|}` on the nonempty touch-connected sets, `0` elsewhere. -/
def cw (y : ℝ) (X : Finset (RPlaq L)) : ℝ :=
  if X.Nonempty ∧ TouchConnected (rbd L) X then y ^ X.card else 0

theorem cw_nonneg {y : ℝ} (hy : 0 ≤ y) (X : Finset (RPlaq L)) : 0 ≤ cw L y X := by
  classical
  unfold cw
  split_ifs
  · exact pow_nonneg hy _
  · exact le_rfl

theorem cw_of_not {y : ℝ} {X : Finset (RPlaq L)}
    (h : ¬ (X.Nonempty ∧ TouchConnected (rbd L) X)) : cw L y X = 0 := by
  classical
  unfold cw
  exact if_neg h

/-- **The size-`n` count of the Dobrushin weight**: `Σ_{X∋v, |X|=n} cw y X ≤ (4225 y)ⁿ`. -/
theorem count_cw {y : ℝ} (hy : 0 < y) (v : RPlaq L) (n : ℕ) :
    ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), cw L y X ≤ (4225 * y) ^ n := by
  classical
  have hc : ConnSupp (rbd L) (cw L y) := by
    intro X hX
    by_contra hn
    exact hX (cw_of_not L (fun h => hn h.2))
  have hd : Decay (cw L y) (-Real.log y) := by
    intro X
    rw [abs_of_nonneg (cw_nonneg L hy.le X)]
    have e : Real.exp (-(-Real.log y * X.card)) = y ^ X.card := by
      rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hy]
    rw [e]
    unfold cw
    split_ifs
    · exact le_rfl
    · exact pow_nonneg hy.le _
  have h := countAt_of_connSets_card (rbd L) (K := 4225) (fun v m => card_connSets_rbd_le L v m)
    hc hd v n
  have e : Real.exp (-(-Real.log y)) = y := by rw [neg_neg, Real.exp_log hy]
  rw [e] at h
  push_cast at h
  calc ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), cw L y X
      = ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), |cw L y X| :=
        Finset.sum_congr rfl fun X _ => (abs_of_nonneg (cw_nonneg L hy.le X)).symm
    _ ≤ (4225 * y) ^ n := h

/-- **The tail of the per-site sum**: the sets of at least `m` plaquettes containing `v` give at
most `(4225 y)ᵐ / (1 − 4225 y)`. -/
theorem sum_site_cw_tail_le {y : ℝ} (hy : 0 < y) (hx : 4225 * y < 1) (v : RPlaq L) (m : ℕ) :
    ∑ X ∈ MatchAt.site v, (if m ≤ X.card then cw L y X else 0)
      ≤ (4225 * y) ^ m / (1 - 4225 * y) := by
  classical
  set x := 4225 * y with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hmaps : ∀ X ∈ MatchAt.site v, X.card ∈ Finset.Ico 1 (Fintype.card (RPlaq L) + 1) := by
    intro X hX
    rw [Finset.mem_Ico]
    exact ⟨Finset.card_pos.2 ⟨v, (Finset.mem_filter.1 hX).2⟩,
      Nat.lt_succ_of_le (Finset.card_le_univ X)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hn : ∀ n ∈ Finset.Ico 1 (Fintype.card (RPlaq L) + 1),
      ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), (if m ≤ X.card then cw L y X else 0)
        ≤ if m ≤ n then x ^ n else 0 := by
    intro n _
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      calc ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n),
            (if m ≤ X.card then cw L y X else 0)
          = ∑ X ∈ (MatchAt.site v).filter (fun X => X.card = n), cw L y X :=
            Finset.sum_congr rfl fun X hX => by
              rw [(Finset.mem_filter.1 hX).2, if_pos hmn]
        _ ≤ x ^ n := count_cw L hy v n
    · rw [if_neg hmn]
      refine le_of_eq (Finset.sum_eq_zero fun X hX => ?_)
      rw [(Finset.mem_filter.1 hX).2, if_neg hmn]
  refine (Finset.sum_le_sum hn).trans ?_
  rw [← Finset.sum_filter]
  refine le_trans ?_ (geom_sum_Ico_le_of_lt_one hx0 hx (m := m)
    (n := Fintype.card (RPlaq L) + 1))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => pow_nonneg hx0 n)
  intro n hn'
  rw [Finset.mem_filter, Finset.mem_Ico] at hn'
  rw [Finset.mem_Ico]
  exact ⟨hn'.2, hn'.1.2⟩

/-- **The per-site sum**: `Σ_{X∋v} cw y X ≤ 4225 y / (1 − 4225 y)`. -/
theorem sum_site_cw_le {y : ℝ} (hy : 0 < y) (hx : 4225 * y < 1) (v : RPlaq L) :
    ∑ X ∈ MatchAt.site v, cw L y X ≤ 4225 * y / (1 - 4225 * y) := by
  have h := sum_site_cw_tail_le L hy hx v 1
  rw [pow_one] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun X hX => ?_)) h
  rw [if_pos (show 1 ≤ X.card from Finset.card_pos.2 ⟨v, (Finset.mem_filter.1 hX).2⟩)]

theorem touch_self (q : RPlaq L) : Touch (rbd L) q q :=
  ⟨(q.1.1, q.2), by simp [linkSupp, rbd], by simp [linkSupp, rbd]⟩

/-- **Dobrushin's criterion for the patterned gas**: for `β > 0` and `4225 (1 − e^{−2β}) e ≤ 1/128`,
the activities `actP L β ζ` satisfy `Dob` with the weights `cw ((1 − e^{−2β}) e)`, every pattern. -/
theorem dob_actP {β : ℝ} (hβ : 0 < β) (ζ : RPlaq L → SUN.SU 2)
    (hx : 4225 * (rate β * Real.exp 1) ≤ 1 / 128) :
    MatchAt.Dob (Inc (rbd L)) (actP L β ζ) (cw L (rate β * Real.exp 1)) := by
  classical
  set y := rate β * Real.exp 1 with hydef
  have hy : 0 < y := mul_pos (rate_pos hβ) (Real.exp_pos 1)
  have hx1 : 4225 * y < 1 := by linarith
  intro γ
  refine ⟨cw_nonneg L hy.le γ, ?_⟩
  by_cases hγ : γ.Nonempty ∧ TouchConnected (rbd L) γ
  swap
  · rw [actP_of_not L β ζ hγ, cw_of_not L hγ, abs_zero, zero_mul, neg_zero, Real.exp_zero,
      sub_self]
  have hcγ : cw L y γ = y ^ γ.card := by unfold cw; exact if_pos hγ
  set B := γ.biUnion (touchNbrs (rbd L)) with hB
  have hBcard : B.card ≤ γ.card * 64 := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ p ∈ γ, (touchNbrs (rbd L) p).card ≤ ∑ _p ∈ γ, 64 :=
          Finset.sum_le_sum fun p _ =>
            (touchNbrs_card_le_touchDeg (rbd L) p).trans (touchDeg_rbd_le L)
      _ = γ.card * 64 := by rw [Finset.sum_const, smul_eq_mul]
  have hγn : γ ∉ MatchAt.nbr (Inc (rbd L)) γ := fun h => (Finset.mem_filter.1 h).2.1 rfl
  have hsite : ∀ v, ∑ Y ∈ MatchAt.site v, cw L y Y ≤ 2 * (4225 * y) := by
    intro v
    refine (sum_site_cw_le L hy hx1 v).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4225 * y)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - 4225 * y)]
  have hsum : cw L y γ + ∑ δ ∈ MatchAt.nbr (Inc (rbd L)) γ, cw L y δ ≤ γ.card := by
    rw [← Finset.sum_insert hγn]
    calc ∑ δ ∈ insert γ (MatchAt.nbr (Inc (rbd L)) γ), cw L y δ
        ≤ ∑ v ∈ B, ∑ Y ∈ MatchAt.site v, cw L y Y := by
          refine MatchAt.sum_meet_le _ (cw_nonneg L hy.le) B _ fun Y hY => ?_
          rcases Finset.mem_insert.1 hY with h | h
          · rw [h]
            obtain ⟨p, hp⟩ := hγ.1
            exact ⟨p, Finset.mem_inter.2 ⟨Finset.mem_biUnion.2 ⟨p, hp,
              mem_touchNbrs.2 (touch_self L p)⟩, hp⟩⟩
          · obtain ⟨p, hp, q, hq, hpq⟩ := (Finset.mem_filter.1 h).2.2
            have hqB : q ∈ B := by
              refine Finset.mem_biUnion.2 ⟨p, hp, mem_touchNbrs.2 ?_⟩
              rcases hpq with e | t
              · rw [← e]; exact touch_self L p
              · exact t
            exact ⟨q, Finset.mem_inter.2 ⟨hqB, hq⟩⟩
      _ ≤ ∑ _v ∈ B, 2 * (4225 * y) := Finset.sum_le_sum fun v _ => hsite v
      _ = B.card * (2 * (4225 * y)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (γ.card * 64 : ℕ) * (2 * (4225 * y)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hBcard
      _ ≤ γ.card := by
          push_cast
          have hc : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
          have := mul_le_mul_of_nonneg_left hx hc
          nlinarith
  have hw : |actP L β ζ γ| ≤ rate β ^ γ.card := actP_abs_le L hβ.le ζ γ
  have hc0 : 0 ≤ cw L y γ := cw_nonneg L hy.le γ
  have hkey : cw L y γ * Real.exp (-cw L y γ) ≤ 1 - Real.exp (-cw L y γ) := by
    have h1 := Real.add_one_le_exp (cw L y γ)
    have h2 : Real.exp (cw L y γ) * Real.exp (-cw L y γ) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos (-cw L y γ)
    nlinarith
  calc |actP L β ζ γ| * Real.exp (∑ δ ∈ MatchAt.nbr (Inc (rbd L)) γ, cw L y δ)
      ≤ rate β ^ γ.card * Real.exp (γ.card - cw L y γ) :=
        mul_le_mul hw (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
          (pow_nonneg (rate_nonneg hβ.le) _)
    _ = cw L y γ * Real.exp (-cw L y γ) := by
        have hen : Real.exp (γ.card : ℝ) = Real.exp 1 ^ γ.card := by
          rw [← Real.exp_nat_mul, mul_one]
        rw [sub_eq_add_neg, Real.exp_add, hen, hcγ, hydef, mul_pow]
        ring
    _ ≤ 1 - Real.exp (-cw L y γ) := hkey

end Dob

/-! ## 4. The vortex free energy -/

section Vortex

variable {Pol : Type*} [Fintype Pol] [DecidableEq Pol] {inc : Pol → Pol → Prop} [DecidableRel inc]
  {w : Pol → ℝ}

/-- **Removing a set raises `log Z` by at most its weights**: under `Dob c`,
`Z S ≤ exp(Σ_B c) · Z (S∖B)`. -/
theorem Z_le_exp_sdiff (hs : MatchAt.SymmRel inc) {c : Pol → ℝ} (hD : MatchAt.Dob inc w c)
    (S B : Finset Pol) :
    MatchAt.Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w (S \ B) := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
      rw [Finset.sdiff_insert, Finset.sum_insert hb, Real.exp_add]
      by_cases hbm : b ∈ S \ B
      · have h := ((MatchAt.dob_bounds hs hD (S \ B)).2 b hbm).2
        calc MatchAt.Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w (S \ B) := ih
          _ ≤ Real.exp (∑ δ ∈ B, c δ) * (Real.exp (c b) * MatchAt.Z inc w ((S \ B).erase b)) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = Real.exp (c b) * Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w ((S \ B).erase b) := by
              ring
      · rw [Finset.erase_eq_of_notMem hbm]
        have hZ := (MatchAt.Z_pos hs hD (S \ B)).le
        have h1 : 1 ≤ Real.exp (c b) := Real.one_le_exp (hD b).1
        calc MatchAt.Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w (S \ B) := ih
          _ ≤ Real.exp (c b) * Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w (S \ B) := by
              have := mul_le_mul_of_nonneg_right h1
                (mul_nonneg (Real.exp_pos (∑ δ ∈ B, c δ)).le hZ)
              linarith

/-- `Z S` reads `w` on `S` only. -/
theorem Z_congr {w' : Pol → ℝ} {S : Finset Pol} (h : ∀ γ ∈ S, w γ = w' γ) :
    MatchAt.Z inc w S = MatchAt.Z inc w' S := by
  unfold MatchAt.Z
  exact Finset.sum_congr rfl fun T hT => Finset.prod_congr rfl fun γ hγ =>
    h γ (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1 hγ)

/-- **Two gases that agree off `B`** have `log Z − log Z' ≤ Σ_B (c + c')`. -/
theorem Z_le_of_agree {w' : Pol → ℝ} (hs : MatchAt.SymmRel inc) {c c' : Pol → ℝ}
    (hD : MatchAt.Dob inc w c) (hD' : MatchAt.Dob inc w' c') (S B : Finset Pol)
    (hag : ∀ γ ∈ S \ B, w γ = w' γ) :
    MatchAt.Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ + ∑ δ ∈ B, c' δ) * MatchAt.Z inc w' S := by
  have h1 := Z_le_exp_sdiff hs hD S B
  have h2 := MatchAt.Z_sdiff_le (fun γ => (hD' γ).1) (fun T _ => MatchAt.Z_pos hs hD' T)
    (fun T _ δ hδ => MatchAt.erase_le hs hD' T δ hδ) B (s := S)
  rw [Z_congr hag] at h1
  calc MatchAt.Z inc w S ≤ Real.exp (∑ δ ∈ B, c δ) * MatchAt.Z inc w' (S \ B) := h1
    _ ≤ Real.exp (∑ δ ∈ B, c δ) * (Real.exp (∑ δ ∈ B, c' δ) * MatchAt.Z inc w' S) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (∑ δ ∈ B, c δ + ∑ δ ∈ B, c' δ) * MatchAt.Z inc w' S := by
        rw [Real.exp_add]; ring

variable (L : Fin 4 → ℕ)

/-- **The vortex free energy is a tail of the Dobrushin weights**: for `a ≠ b`, `β > 0` and
`4225 (1 − e^{−2β}) e ≤ 1/128`, `vortexR L a b β ≤ 2 Σ_{|X| ≥ L_a L_b} cw y X`. -/
theorem vortexR_le_tail {β : ℝ} (hβ : 0 < β) (hx : 4225 * (rate β * Real.exp 1) ≤ 1 / 128)
    {a b : Fin 4} (hab : a ≠ b) :
    vortexR L a b β ≤ 2 * ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter
      (fun X => L a * L b ≤ X.card), cw L (rate β * Real.exp 1) X := by
  classical
  have hD1 := dob_actP L hβ (fun _ => 1) hx
  have hD2 := dob_actP L hβ (sheetR L a b) hx
  have hs := ChunkActivity.inc_symm (rbd L)
  have hag : ∀ γ ∈ (univ : Finset (RPlaq L)).powerset \
      ((univ : Finset (RPlaq L)).powerset).filter (fun X => L a * L b ≤ X.card),
      actP L β (fun _ => 1) γ = actP L β (sheetR L a b) γ := by
    intro γ hγ
    have hγB := (Finset.mem_sdiff.1 hγ).2
    have hlt : γ.card < L a * L b := by
      by_contra hn
      exact hγB (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hγ).1, not_lt.1 hn⟩)
    exact (actP_sheet_eq L β hab hlt).symm
  have hZ := Z_le_of_agree hs hD1 hD2 (univ : Finset (RPlaq L)).powerset
    (((univ : Finset (RPlaq L)).powerset).filter (fun X => L a * L b ≤ X.card)) hag
  rw [← ZRp_eq_polymerZ, ← ZRp_eq_polymerZ, ← ZR_eq_ZRp] at hZ
  have hZ1 := ZR_pos L β
  have hZ2 := ZRp_pos L β (sheetR L a b)
  unfold vortexR zR
  rw [Real.log_div hZ2.ne' hZ1.ne']
  have hl := Real.log_le_log hZ1 hZ
  rw [Real.log_mul (Real.exp_pos _).ne' hZ2.ne', Real.log_exp] at hl
  linarith

/-- **The vortex free energy at small coupling**: `vortexR L a b β ≤ 4 |RPlaq L| x^{L_a L_b}`,
`x = 4225 (1 − e^{−2β}) e`, for `a ≠ b`, `β > 0`, `x ≤ 1/128` and `L_a L_b ≥ 1`. -/
theorem vortexR_le_card {β : ℝ} (hβ : 0 < β) (hx : 4225 * (rate β * Real.exp 1) ≤ 1 / 128)
    {a b : Fin 4} (hab : a ≠ b) (hA : 1 ≤ L a * L b) :
    vortexR L a b β
      ≤ 4 * Fintype.card (RPlaq L) * (4225 * (rate β * Real.exp 1)) ^ (L a * L b) := by
  classical
  refine (vortexR_le_tail L hβ hx hab).trans ?_
  set y := rate β * Real.exp 1 with hydef
  have hy : 0 < y := mul_pos (rate_pos hβ) (Real.exp_pos 1)
  have hx1 : 4225 * y < 1 := by linarith
  have hx0 : 0 ≤ 4225 * y := by positivity
  set m := L a * L b with hm
  have h1 : ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card), cw L y X
      = ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card),
          (if m ≤ X.card then cw L y X else 0) :=
    Finset.sum_congr rfl fun X hX => by rw [if_pos (Finset.mem_filter.1 hX).2]
  have h2 : ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card),
        (if m ≤ X.card then cw L y X else 0)
      ≤ ∑ v ∈ (univ : Finset (RPlaq L)), ∑ X ∈ MatchAt.site v,
          (if m ≤ X.card then cw L y X else 0) := by
    refine MatchAt.sum_meet_le _ (fun Y => ?_) _ _ fun Y hY => ?_
    · split_ifs
      · exact cw_nonneg L hy.le Y
      · exact le_rfl
    · have hc : 1 ≤ Y.card := hA.trans (Finset.mem_filter.1 hY).2
      obtain ⟨p, hp⟩ := Finset.card_pos.1 hc
      exact ⟨p, Finset.mem_inter.2 ⟨Finset.mem_univ _, hp⟩⟩
  have h3 : ∑ v ∈ (univ : Finset (RPlaq L)), ∑ X ∈ MatchAt.site v,
        (if m ≤ X.card then cw L y X else 0)
      ≤ Fintype.card (RPlaq L) * ((4225 * y) ^ m / (1 - 4225 * y)) := by
    calc _ ≤ ∑ _v ∈ (univ : Finset (RPlaq L)), (4225 * y) ^ m / (1 - 4225 * y) :=
          Finset.sum_le_sum fun v _ => sum_site_cw_tail_le L hy hx1 v m
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : (4225 * y) ^ m / (1 - 4225 * y) ≤ 2 * (4225 * y) ^ m := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_nonneg hx0 m
    nlinarith
  have hcard : (0 : ℝ) ≤ Fintype.card (RPlaq L) := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h4 hcard
  rw [h1]
  nlinarith [h2, h3, h5]

end Vortex

/-! ## 5. Condensation along the doubling tori -/

section Condense

/-- **The explicit coupling bound** `β₀ = 1/4000000`. CHOSEN: `1/4000000` a round value below
`1/(4225 · 3 · 2 · 128) = 1/3244800`, so `4225 · 3 · 2β₀ ≤ 1/128` (`x_le_of_le_β₀`); it costs only coupling range. -/
def β₀ : ℝ := 1 / 4000000

/-- **The condensation rate** `rhoS β = −log (4225 e (1 − e^{−2β}))`. DERIVED: `4225 = (64 + 1)²` the
connected-set entropy of `StrongCoupling.card_connSets_le`; `e` the Dobrushin weight `a = 1` per plaquette. -/
def rhoS (β : ℝ) : ℝ := -Real.log (4225 * (rate β * Real.exp 1))

theorem rate_le_two_mul {β : ℝ} : rate β ≤ 2 * β := by
  unfold rate
  have := Real.add_one_le_exp (-(2 * β))
  linarith

/-- **Below `β₀` the Dobrushin condition holds**: `4225 (1 − e^{−2β}) e ≤ 1/128`. -/
theorem x_le_of_le_β₀ {β : ℝ} (hβ : 0 < β) (hβ₀ : β ≤ β₀) :
    4225 * (rate β * Real.exp 1) ≤ 1 / 128 := by
  have h1 := rate_le_two_mul (β := β)
  have h0 := rate_nonneg hβ.le
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have he0 := Real.exp_pos 1
  unfold β₀ at hβ₀
  have h2 : rate β * Real.exp 1 ≤ 2 * β * 3 := by
    have := mul_le_mul h1 he.le he0.le (by linarith)
    linarith
  nlinarith

theorem x_pos {β : ℝ} (hβ : 0 < β) : 0 < 4225 * (rate β * Real.exp 1) :=
  mul_pos (by norm_num) (mul_pos (rate_pos hβ) (Real.exp_pos 1))

/-- **The rate is positive**, in fact at least `log 128`, for `0 < β ≤ β₀`. -/
theorem rhoS_pos {β : ℝ} (hβ : 0 < β) (hβ₀ : β ≤ β₀) : Real.log 128 ≤ rhoS β ∧ 0 < rhoS β := by
  have hx := x_le_of_le_β₀ hβ hβ₀
  have hx0 := x_pos hβ
  unfold rhoS
  have h1 : Real.log (4225 * (rate β * Real.exp 1)) ≤ Real.log (1 / 128) := Real.log_le_log hx0 hx
  rw [one_div, Real.log_inv] at h1
  have h2 : 0 < Real.log 128 := Real.log_pos (by norm_num)
  constructor <;> linarith

theorem Lc_le_two (n : ℕ) (i j : Fin 4) : Lc n i j ≤ 2 * n := by
  show 2 ^ (CentreSectorSeed.pathV i j) * n ≤ 2 * n
  have h : CentreSectorSeed.pathV i j ≤ 1 := by
    fin_cases i <;> fin_cases j <;> decide
  exact Nat.mul_le_mul_right n (by
    calc 2 ^ CentreSectorSeed.pathV i j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h
      _ = 2 := by norm_num)

/-- **The plaquette count of a corner torus against the area of a plane**:
`|RPlaq (Lc n i)| ≤ 256 (L_i L_ν)²`. -/
theorem card_rplaq_Lc_le (n : ℕ) (i ν : Fin 4) :
    (Fintype.card (RPlaq (Lc n i)) : ℝ)
      ≤ 256 * (((Lc n i i : ℕ) : ℝ) * ((Lc n i ν : ℕ) : ℝ)) ^ 2 := by
  have hc : Fintype.card (RPlaq (Lc n i)) = 16 * ∏ j : Fin 4, Lc n i j := by
    simp [RPlaq, RSite, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  have hprod : ∏ j : Fin 4, Lc n i j ≤ 16 * n ^ 4 := by
    rw [Fin.prod_univ_four]
    have h0 := Lc_le_two n i 0
    have h1 := Lc_le_two n i 1
    have h2 := Lc_le_two n i 2
    have h3 := Lc_le_two n i 3
    calc Lc n i 0 * Lc n i 1 * Lc n i 2 * Lc n i 3 ≤ (2 * n) * (2 * n) * (2 * n) * (2 * n) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
      _ = 16 * n ^ 4 := by ring
  have hii : Lc n i i = n := VortexTorus.Lc_self n i
  have hν : n ≤ Lc n i ν := VortexTorus.le_Lc n i ν
  have hcard : (Fintype.card (RPlaq (Lc n i)) : ℝ) ≤ 256 * (n : ℝ) ^ 4 := by
    rw [hc]
    have : (16 * ∏ j : Fin 4, Lc n i j : ℕ) ≤ 256 * n ^ 4 :=
      calc 16 * ∏ j : Fin 4, Lc n i j ≤ 16 * (16 * n ^ 4) := Nat.mul_le_mul_left 16 hprod
        _ = 256 * n ^ 4 := by ring
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hν' : (n : ℝ) ≤ ((Lc n i ν : ℕ) : ℝ) := by exact_mod_cast hν
  rw [hii]
  have : (n : ℝ) ^ 4 ≤ ((n : ℝ) * ((Lc n i ν : ℕ) : ℝ)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hν' hn0
    have h' : (n : ℝ) * n ≤ (n : ℝ) * ((Lc n i ν : ℕ) : ℝ) := h
    calc (n : ℝ) ^ 4 = ((n : ℝ) * n) ^ 2 := by ring
      _ ≤ ((n : ℝ) * ((Lc n i ν : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h' 2
  linarith

/-- **Condensation of the rectangular vortex free energy at small coupling.** For `0 < β ≤ β₀` and
`ν ≠ i`, `vortexR (Lc (2^{K+1}) i) i ν β` condenses at rate `rhoS β` per unit area of the plane
`(i, ν)` along the doubling corner tori. -/
theorem condenses_vortexR_strong {β : ℝ} (hβ : 0 < β) (hβ₀ : β ≤ β₀) (i ν : Fin 4) (hν : ν ≠ i) :
    Condenses (fun K => vortexR (Lc (2 ^ (K + 1)) i) i ν β)
      (fun K => ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)) (rhoS β) := by
  set x := 4225 * (rate β * Real.exp 1) with hxdef
  have hx := x_le_of_le_β₀ hβ hβ₀
  have hx0 : 0 < x := x_pos hβ
  set A : ℕ → ℝ := fun K => ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)
    with hAdef
  have hAge : ∀ K, ((2 ^ (K + 1) : ℕ) : ℝ) ≤ A K := by
    intro K
    have h1 : Lc (2 ^ (K + 1)) i i = 2 ^ (K + 1) := VortexTorus.Lc_self _ i
    have h2 : 1 ≤ Lc (2 ^ (K + 1)) i ν :=
      le_trans Nat.one_le_two_pow (VortexTorus.le_Lc _ i ν)
    show ((2 ^ (K + 1) : ℕ) : ℝ) ≤ ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ)
    rw [h1]
    have h2' : (1 : ℝ) ≤ ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ) := by exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hA1 : ∀ K, 1 ≤ A K := fun K =>
    le_trans (by exact_mod_cast Nat.one_le_two_pow) (hAge K)
  have hAinf : Tendsto A atTop atTop := by
    refine tendsto_atTop_mono hAge ?_
    have : Tendsto (fun K : ℕ => 2 ^ (K + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp (tendsto_add_atTop_nat 1)
    exact tendsto_natCast_atTop_atTop.comp this
  refine condenses_of_sublinear (g := fun K => Real.log (1024 * A K ^ 2)) ?_ hAinf ?_
  · refine Eventually.of_forall fun K => ?_
    have hab : i ≠ ν := Ne.symm hν
    have hA1' : 1 ≤ Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν := by
      have : (1 : ℝ) ≤ ((Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ) := by
        push_cast; exact hA1 K
      exact_mod_cast this
    have hv := vortexR_le_card (Lc (2 ^ (K + 1)) i) hβ hx hab hA1'
    have hcard := card_rplaq_Lc_le (2 ^ (K + 1)) i ν
    have hAK : A K = ((Lc (2 ^ (K + 1)) i i : ℕ) : ℝ) * ((Lc (2 ^ (K + 1)) i ν : ℕ) : ℝ) := rfl
    have hpow : x ^ (Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν)
        = Real.exp (-(rhoS β * A K)) := by
      unfold rhoS
      rw [← hxdef, neg_mul, neg_neg, hAK, ← Nat.cast_mul, mul_comm (Real.log x), Real.exp_nat_mul,
        Real.exp_log hx0]
    have hexp : Real.exp (Real.log (1024 * A K ^ 2)) = 1024 * A K ^ 2 :=
      Real.exp_log (by have := hA1 K; positivity)
    show vortexR (Lc (2 ^ (K + 1)) i) i ν β
      ≤ Real.exp (Real.log (1024 * A K ^ 2)) * Real.exp (-(rhoS β * A K))
    rw [hexp, ← hpow]
    have hxp : 0 ≤ x ^ (Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν) := pow_nonneg hx0.le _
    rw [← hAK] at hcard
    calc vortexR (Lc (2 ^ (K + 1)) i) i ν β
        ≤ 4 * Fintype.card (RPlaq (Lc (2 ^ (K + 1)) i))
          * x ^ (Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν) := hv
      _ ≤ 4 * (256 * A K ^ 2) * x ^ (Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν) := by
          refine mul_le_mul_of_nonneg_right ?_ hxp
          linarith
      _ = 1024 * A K ^ 2 * x ^ (Lc (2 ^ (K + 1)) i i * Lc (2 ^ (K + 1)) i ν) := by ring
  · have hl : Tendsto (fun a : ℝ => Real.log a / a) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h1 : Tendsto (fun K => Real.log (A K) / A K) atTop (𝓝 0) := hl.comp hAinf
    have h2 : Tendsto (fun K => Real.log 1024 / A K) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hAinf
    have h3 : Tendsto (fun K => Real.log 1024 / A K + 2 * (Real.log (A K) / A K)) atTop
        (𝓝 (0 + 2 * 0)) := h2.add (h1.const_mul 2)
    rw [show (0 : ℝ) + 2 * 0 = 0 by ring] at h3
    refine h3.congr' (Eventually.of_forall fun K => ?_)
    have hpos : 0 < A K := lt_of_lt_of_le one_pos (hA1 K)
    show Real.log 1024 / A K + 2 * (Real.log (A K) / A K) = Real.log (1024 * A K ^ 2) / A K
    rw [Real.log_mul (by norm_num) (pow_pos hpos 2).ne', Real.log_pow]
    push_cast
    ring

end Condense

/-! ## 6. What this gives the zoom theorems -/

section Zoom

open MassGap.TomboulisYaffe MassGap.VortexTwo

/-- **The remaining inputs at one coupling, named**: for every corner family `o` on the doubling tori
`Lc (2^{K+1}) i`, the square loops `wloopR … (2^p) (2^p) (o K) β` converge as `K → ∞` for every `p`
to `Winf (2^p) (2^p)`, and `Winf` has `HasTension` with some `σ`. No declaration proves this. With
`ChessboardFlux` at `0 < β ≤ β₀`, every such `σ` is at least `rhoS β > 0` (`floor_of_strong`). -/
def StrongLoopTension (β : ℝ) (i ν : Fin 4) : Prop :=
  ∀ o : ∀ K, RectWilson.RSite (Lc (2 ^ (K + 1)) i), ∃ (Winf : ℕ → ℕ → ℝ) (σ : ℝ),
    (∀ p, Tendsto (fun K => wloopR (Lc (2 ^ (K + 1)) i) i ν (2 ^ p) (2 ^ p) (o K) β) atTop
      (𝓝 (Winf (2 ^ p) (2 ^ p)))) ∧ HasTension Winf σ

/-- **The zoom theorem with condensation discharged.** At one `β ∈ (0, β₀]`, `ν ≠ i`, a corner family
`o`, `ChessboardFlux` on every doubling torus and `StrongLoopTension β i ν` give the hypotheses of
`floor_of_vortexR_condensation_two` on the constant zoom (`β j = β`, `a j = 1`, `ρ₀ = rhoS β`), the
condensation input supplied by `condenses_vortexR_strong`; its conclusion is a floor on the constant
tension `σ`, and `rhoS β ≤ σ`. The floor on a constant family is `0 < σ`; the content is
`rhoS β ≤ σ`. -/
theorem floor_of_strong {β : ℝ} (hβ : 0 < β) (hβ₀ : β ≤ β₀) (i ν : Fin 4) (hν : ν ≠ i)
    (o : ∀ K, RectWilson.RSite (Lc (2 ^ (K + 1)) i))
    (hCB : ∀ K, ChessboardFlux (Lc (2 ^ (K + 1)) i) i ν (o K) β)
    (hLT : StrongLoopTension β i ν) :
    ∃ σ : ℝ, 0 < σ ∧ rhoS β ≤ σ ∧ NoTransition.Floor (fun _ : ℕ => σ) := by
  obtain ⟨Winf, σ, hlim, hT⟩ := hLT o
  have hc1 : rhoS β * (1 : ℝ) ^ 2 = rhoS β := by ring
  have hfl := floor_of_vortexR_condensation_two (β := fun _ => β) (a := fun _ => 1)
    (σlat := fun _ => σ) (rhoS_pos hβ hβ₀).2 (fun _ => one_pos) (fun _ => hβ.le) i ν hν
    (fun _ => o) (fun _ K => hCB K)
    (fun _ => by
      show Condenses _ _ (rhoS β * (1 : ℝ) ^ 2)
      rw [hc1]
      exact condenses_vortexR_strong hβ hβ₀ i ν hν)
    (Winf := fun _ => Winf) (fun _ p => hlim p) (fun _ => hT)
  have harea := areaLaw_two_of_vortexR_condensation hβ.le i ν hν o hCB
    (condenses_vortexR_strong hβ hβ₀ i ν hν) hlim
  have hle := le_tension_of_area_two hT harea
  refine ⟨σ, lt_of_lt_of_le (rhoS_pos hβ hβ₀).2 hle, hle, ?_⟩
  simpa using hfl

end Zoom

#print axioms ZRp_eq_sum
#print axioms zwP_union
#print axioms zwP_sup_eq_prod
#print axioms ZRp_eq_polymerZ
#print axioms zwP_abs_le
#print axioms actP_abs_le
#print axioms zwP_coboundary
#print axioms rhol_strip
#print axioms zwP_sheet_move
#print axioms card_ge_of_zwP_ne
#print axioms actP_sheet_eq
#print axioms linkMult_rbd_le
#print axioms touchDeg_rbd_le
#print axioms card_connSets_rbd_le
#print axioms count_cw
#print axioms sum_site_cw_tail_le
#print axioms sum_site_cw_le
#print axioms dob_actP
#print axioms Z_le_exp_sdiff
#print axioms Z_le_of_agree
#print axioms vortexR_le_tail
#print axioms vortexR_le_card
#print axioms x_le_of_le_β₀
#print axioms rhoS_pos
#print axioms card_rplaq_Lc_le
#print axioms condenses_vortexR_strong
#print axioms floor_of_strong

end MassGap.VortexStrong
