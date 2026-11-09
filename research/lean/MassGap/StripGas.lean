import Mathlib
import MassGap.ChunkLinks
import MassGap.CumulantStrip

/-!
# MassGap.StripGas — the site gas of the mixed plaquettes, given the links

Layer 1 of the route of `StripTail`. Fix all the links `U`. Rotating the low links by i.i.d. Haar site variables `a`
(`MixCut.gT`) makes the tilted mixed plaquettes `g_p(a) = cT(φ(hol_p(gT a U)))` a finite-range system: `g_p` reads `a`
at the four corners of `p` only. This module proves that the conditional integral
`Y(U) = ∫ da ∏_p (1 + g_p(a))` is a hard-core polymer gas on the sites that satisfies Kotecký–Preiss at a width
independent of `β`, `N`, `n` and `U`, and writes `log Y(U)` as a sum over sites of local functions of `U`. Declarations
are in `MassGap.StripGas`.

## The result

For `|t| ≤ t₁ = e^{−88}/16` (`tOne`), every `N ≠ 0`, every side `n`, every `U` (`β` does not occur):

* `gasR_matchAt`: `MatchAt.MatchAt (siteAct cbd (gR N n t U)) 1 5`.
* `log_YR_eq_sum`: `log Y(U) = Σ_x y_x(U)`.
* `abs_yR_le`: `|y_x(U)| ≤ 1`.
* `abs_yR_sub_le`, `ratio_lt`, `yRT_congr`: for every `r`, `|y_x(U) − y_x^r(U)| ≤ 3 (65/e⁵)^r`, `65/e⁵ < 1/2`, where
  `y_x^r(U)` depends on `U` only through the links of the plaquettes with all corners in `ball cbd x (2 r + 1)`, a set of at
  most `65^{2 r + 1}` sites (`card_ball_le`).
* `ZG_eq_integral_YR`: `Z_gas(all) = ∫ e^{−β S_in(U)} Y(U) dU`, for any `β`: the mixed gas of `CumulantStrip` is
  the average of `Y` against the decoupled weight. `YR_pos`: `Y(U) > 0` for `|t| ≤ t₁`; with `log_YR_eq_sum` that reads `Y = exp(Σ_x y_x)` there, a corollary not stated separately.

## The method

§1 is generic: continuous bounded `g_p` on product Haar over sites, `g_p` reading the sites of `p` (`SiteGas`). Touch
components factor by `WilsonReal.block_integral_factor`, so `Y` is the gas of `ChunkActivity` with `zw` replaced by `zg`
(`Y_eq_Z`), transported to site polymers by `ChunkLinks.Z_push` (`Y_eq_siteZ`). §2: `ChunkLinks.countAt_link` and
`MatchAt.matchAt_of_count` give `MatchAt` from `|g| ≤ e^{−88}`. §3: `log Z` loses at most the Dobrushin weights of the removed
polymers; a polymer meeting the inner ball and leaving the outer ball is big; the rest is `MatchAt.cluster_sites`. §4:
the telescoping over an enumeration of the sites. §5: balls and capped levels. §7: the plaquettes.

The constants, evaluated: `|gAct X| ≤ ε^{|X|}`, `ε = 16 |t|`. No activity reads `N`, `β`, `n`, `U`: the only input is
`0 ≤ φ ≤ 2`, the range of the normalized density, through `CumulantStrip.abs_cT_le`.

DERIVED (module-wide): `4` the corners of a plaquette; `16` the plaquettes at a site (`card_star_le`) and the bound of
`abs_cT_le`; `64 = 4 · 16`, `65 = 64 + 1`; `4225 = 65²` the rooted count of `card_connSets_le`; `8 = 2 · 4`, so a cost `T` per
plaquette is `T/8` per site in `countAt_link`; `2 r + 1`, `2 r + 2` the outer ball and the level cap; `1` the Kotecký–Preiss
parameter `a` of `matchAt_of_count` and the mass of a probability measure; `0` the root level. CHOSEN: `κ = 5`, the
least integer with `e^κ > 2 · 65`; `T = 88 = 8 · 11`, so `τ = 11` and `1 + κ − τ = −5`. COMPUTED: `64 ≤ e⁵`; `8450 ≤ e⁴⁴`; `130 < e⁵`.

## What does not follow

* Nothing here reads the plane: `Y(U)` is local in `U`, but `∫ e^{−β S_in} exp(Σ_x y_x)` is the second layer, not touched.
  The missing inequality in the header of `StripTail`, `∃ K, |mixCut N β s w| ≤ K s³` on `[0, t]` with `K t⁴ ≤ 1/500` at infinitely
  many windows, for `t ≤ t₁` uniform in `N, β`, stays open. So the constant-width strip is not proved, `DA_le_tail` is not proved, and
  `t = β` is not reached.
* The next step is the oscillation bound, not proved or refuted here: `|y_x(U) − y_x(U')| ≤ C t⁴` for `U, U'` differing on one link or
  one plane face, summably over those positions, for a translation-covariant `y_x`. `|y_x| ≤ 1` is useless for the outer field.
* No smallness of `y_x` in `t` is stated: `|y_x| ≤ 1` is what `MatchAt` gives directly, and it is not small. `O(t⁴)` and
  dependence on in-plane loops only are not proved. The centring of `g_p` is not used, so this module holds for
  every bounded finite-range family and says nothing specific to holonomies.
* `y_x` depends on the enumeration of the sites `Fintype.equivFin`; the sum does not. Translation covariance of `y_x` is not
  stated and fails for that choice. Gauge invariance of `y_x` under the rotations is not stated.
* `t₁` is far below `2⁻¹⁷`, the width of `CumulantStrip.logZA_ext`.
* The statement is for `SU(N)`, the only group of `CumulantStrip`. The proof uses product Haar on sites and the bound on `g`;
  no non-abelian input enters. The `U(1)` form is argued, not a Lean statement.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StripGas

open Finset MeasureTheory Filter Topology
open MassGap.StrongCoupling MassGap.PolymerCount MassGap.ChunkActivity MassGap.ChunkLinks
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

/-! ## 1. The gas of a bounded finite-range family on product Haar -/

section Generic

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- Product Haar on the sites. No numeral. -/
abbrev νS (N : ℕ) (Lk : Type) [Fintype Lk] : Measure (Lk → SU N) := Measure.pi fun _ => probHaar (SU N)

/-- **A finite-range family**: `g_p` continuous, bounded by `ε`, reading the sites of `p` only. No numeral. -/
structure SiteGas (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) (ε : ℝ) : Prop where
  cont : ∀ p, Continuous (g p)
  abs_le : ∀ p a, |g p a| ≤ ε
  reads : ∀ p a a', (∀ z ∈ linkSupp bd p, a z = a' z) → g p a = g p a'

/-- `∫ ∏_E g`. No numeral. -/
def zg (g : Pq → (Lk → SU N) → ℝ) (E : Finset Pq) : ℝ := ∫ a, ∏ p ∈ E, g p a ∂(νS N Lk)

/-- **The conditional integral** `Y(W) = ∫ ∏_W (1 + g)`. DERIVED: `1` the unit of the product. -/
def Yg (g : Pq → (Lk → SU N) → ℝ) (W : Finset Pq) : ℝ := ∫ a, ∏ p ∈ W, (1 + g p a) ∂(νS N Lk)

theorem integrable_cont {F : (Lk → SU N) → ℝ} (hF : Continuous F) : Integrable F (νS N Lk) := by
  obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hF
  exact HeatBath.integrable_of_abs_le _ hF.measurable hC

variable {bd : Pq → List (Lk × Bool)} {g : Pq → (Lk → SU N) → ℝ} {ε : ℝ}

/-- The extension of a tuple on `S` by the identity. DERIVED: `1` the identity. -/
def ext1 (S : Finset Lk) (v : S → SU N) : Lk → SU N := fun l => if h : l ∈ S then v ⟨l, h⟩ else 1

theorem continuous_ext1 (S : Finset Lk) : Continuous (ext1 (N := N) S) := by
  refine continuous_pi fun l => ?_
  unfold ext1
  by_cases h : l ∈ S
  · simpa only [dif_pos h] using continuous_apply (⟨l, h⟩ : S)
  · simpa only [dif_neg h] using continuous_const

/-- **Sets with disjoint sites factor.** `WilsonReal.block_integral_factor`. No numeral. -/
theorem zg_union (h : SiteGas bd g ε) {A B : Finset Pq} (hd : Disjoint A B)
    (hl : Disjoint (supp bd A) (supp bd B)) : zg g (A ∪ B) = zg g A * zg g B := by
  have hc : ∀ (E : Finset Pq), Continuous fun a : Lk → SU N => ∏ p ∈ E, g p a :=
    fun E => continuous_finsetProd _ fun p _ => h.cont p
  have key := WilsonReal.block_integral_factor (N := N) (supp bd A) (supp bd B) hl
    (fun v => ∏ p ∈ A, g p (ext1 _ v)) (fun v => ∏ p ∈ B, g p (ext1 _ v))
    ((hc A).comp (continuous_ext1 _)).measurable ((hc B).comp (continuous_ext1 _)).measurable
  have e : ∀ (E : Finset Pq) (a : Lk → SU N),
      ∏ p ∈ E, g p (ext1 (supp bd E) fun i => a i.val) = ∏ p ∈ E, g p a := by
    intro E a
    refine Finset.prod_congr rfl fun p hp => h.reads p _ _ fun z hz => ?_
    have hzS : z ∈ supp bd E := mem_supp.2 ⟨p, hp, hz⟩
    simp only [ext1, dif_pos hzS]
  simp only [e] at key
  unfold zg
  simp only [Finset.prod_union hd]
  exact key

theorem zg_empty (g : Pq → (Lk → SU N) → ℝ) : zg g (∅ : Finset Pq) = 1 := by
  unfold zg
  simp

theorem zg_sup_eq_prod (h : SiteGas bd g ε) (T : Finset (Finset Pq))
    (hT : MatchAt.Compat (Inc bd) T) : zg g (T.sup id) = ∏ X ∈ T, zg g X := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.prod_empty]
      exact zg_empty g
  | @insert X T hX ih =>
      have hT' : MatchAt.Compat (Inc bd) T := fun x hx y hy hxy =>
        hT x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      have hXT : ∀ Y ∈ T, ¬ Inc bd X Y := fun Y hY =>
        hT X (Finset.mem_insert_self _ _) Y (Finset.mem_insert_of_mem hY)
          (fun e => hX (e ▸ hY))
      rw [Finset.sup_insert, Finset.prod_insert hX, ← ih hT']
      have hdisj : Disjoint X (T.sup id) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        obtain ⟨Y, hY, hpY⟩ := Finset.mem_sup.1 hp'
        exact hXT Y hY ⟨p, hp, p, hpY, Or.inl rfl⟩
      have hlinks : Disjoint (supp bd X) (supp bd (T.sup id)) := by
        rw [Finset.disjoint_left]
        intro l hl hl'
        obtain ⟨p, hp, hlp⟩ := mem_supp.1 hl
        obtain ⟨q, hq, hlq⟩ := mem_supp.1 hl'
        obtain ⟨Y, hY, hqY⟩ := Finset.mem_sup.1 hq
        exact hXT Y hY ⟨p, hp, q, hqY, Or.inr ⟨l, hlp, hlq⟩⟩
      exact zg_union h hdisj hlinks

open scoped Classical in
/-- **The activity** of a plaquette polymer: `∫ ∏_X g` on a nonempty touch-connected `X`, `0` elsewhere. DERIVED: `0`
the excluded sets. -/
def gAct (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) (X : Finset Pq) : ℝ :=
  if X.Nonempty ∧ TouchConnected bd X then zg g X else 0

theorem gAct_empty (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) : gAct bd g ∅ = 0 := by
  classical
  unfold gAct
  exact if_neg fun h => Finset.not_nonempty_empty h.1

theorem gAct_of {X : Finset Pq} (h : X.Nonempty ∧ TouchConnected bd X) : gAct bd g X = zg g X := by
  classical
  unfold gAct
  exact if_pos h

theorem gAct_ne_zero {X : Finset Pq} (h : gAct bd g X ≠ 0) : X.Nonempty ∧ TouchConnected bd X := by
  classical
  by_contra hn
  unfold gAct at h
  exact h (if_neg hn)

theorem zg_eq_prod_comps (h : SiteGas bd g ε) (E : Finset Pq) :
    zg g E = ∏ C ∈ comps bd E, gAct bd g C := by
  conv_lhs => rw [← comps_sup bd E]
  rw [zg_sup_eq_prod h _ (comps_compat bd E)]
  exact Finset.prod_congr rfl fun C hC => (gAct_of ⟨(comps_mem hC).1, (comps_mem hC).2.1⟩).symm

/-- `Y` is the sum of the moments over subsets. DERIVED: `1` the unit of the product. -/
theorem Yg_eq_sum (h : SiteGas bd g ε) (W : Finset Pq) : Yg g W = ∑ E ∈ W.powerset, zg g E := by
  classical
  unfold Yg zg
  rw [← integral_finset_sum _ fun E _ => integrable_cont
    (continuous_finsetProd _ fun p _ => h.cont p)]
  exact integral_congr_ae (Eventually.of_forall fun a => Finset.prod_one_add W)

/-- **`Y` is the hard-core gas of the connected polymers in `W`.** No numeral. -/
theorem Y_eq_Z (h : SiteGas bd g ε) (W : Finset Pq) :
    Yg g W = MatchAt.Z (Inc bd) (gAct bd g) W.powerset := by
  classical
  rw [Yg_eq_sum h]
  unfold MatchAt.Z
  symm
  refine Finset.sum_bij_ne_zero (fun (T : Finset (Finset Pq)) _ _ => T.sup id) ?_ ?_ ?_ ?_
  · intro T hT _
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨X, hX, hxX⟩ := Finset.mem_sup.1 hx
    have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1) hX
    exact Finset.mem_powerset.1 this hxX
  · intro T₁ h₁ hn₁ T₂ h₂ hn₂ heq
    have ha₁ : Admissible bd T₁ := ⟨fun X hX =>
      gAct_ne_zero (Finset.prod_ne_zero_iff.1 hn₁ X hX), (Finset.mem_filter.1 h₁).2⟩
    have ha₂ : Admissible bd T₂ := ⟨fun X hX =>
      gAct_ne_zero (Finset.prod_ne_zero_iff.1 hn₂ X hX), (Finset.mem_filter.1 h₂).2⟩
    rw [← comps_family bd ha₁, ← comps_family bd ha₂]
    exact congrArg (comps bd) heq
  · intro E hE hne
    refine ⟨comps bd E, ?_, ?_, comps_sup bd E⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (fun C hC => ?_), comps_compat bd E⟩
      exact Finset.mem_powerset.2 ((comps_mem hC).2.2.trans (Finset.mem_powerset.1 hE))
    · rw [← zg_eq_prod_comps h]
      exact hne
  · intro T hT hn
    have ha : Admissible bd T := ⟨fun X hX =>
      gAct_ne_zero (Finset.prod_ne_zero_iff.1 hn X hX), (Finset.mem_filter.1 hT).2⟩
    rw [zg_sup_eq_prod h T ha.2]
    exact Finset.prod_congr rfl fun X hX => gAct_of (ha.1 X hX)

/-- **The site activity**: `w(Λ) = Σ_{supp X = Λ} gAct X`. No numeral. -/
def siteAct (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) : Finset Lk → ℝ :=
  push (supp bd) (gAct bd g)

open scoped Classical in
/-- The plaquettes with all their sites in `Λ`. No numeral. -/
def inW (bd : Pq → List (Lk × Bool)) (Λ : Finset Lk) : Finset Pq :=
  univ.filter fun p => linkSupp bd p ⊆ Λ

theorem mem_inW {Λ : Finset Lk} {p : Pq} : p ∈ inW bd Λ ↔ linkSupp bd p ⊆ Λ := by
  classical
  simp [inW]

/-- **`Y` on the plaquettes inside `Λ` is the site gas on the subsets of `Λ`.** No numeral. -/
theorem Y_eq_siteZ (hbd : ∀ p, (linkSupp bd p).Nonempty) (h : SiteGas bd g ε) (Λ : Finset Lk) :
    Yg g (inW bd Λ) = MatchAt.Z MatchAt.meet (siteAct bd g) Λ.powerset := by
  classical
  have hp : pre (supp bd) Λ.powerset = (inW bd Λ).powerset := by
    ext E
    rw [mem_pre, Finset.mem_powerset, Finset.mem_powerset]
    constructor
    · intro hE p hp
      exact mem_inW.2 fun z hz => hE (mem_supp.2 ⟨p, hp, hz⟩)
    · intro hE z hz
      obtain ⟨p, hp, hzp⟩ := mem_supp.1 hz
      exact mem_inW.1 (hE hp) hzp
  rw [Y_eq_Z h, ← hp]
  exact (Z_push (inc_symm bd) MatchAt.meet_symm (supp bd) _ (inc_iff_meet bd hbd)
    (inc_of_supp_eq bd hbd) Λ.powerset).symm

theorem abs_zg_le (h : SiteGas bd g ε) (hε : 0 ≤ ε) (E : Finset Pq) : |zg g E| ≤ ε ^ E.card := by
  classical
  have hb : ∀ a, |∏ p ∈ E, g p a| ≤ ε ^ E.card := fun a => by
    rw [Finset.abs_prod]
    calc ∏ p ∈ E, |g p a| ≤ ∏ _p ∈ E, ε :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun p _ => h.abs_le p a
      _ = _ := by simp
  have hc : Continuous fun a : Lk → SU N => ∏ p ∈ E, g p a :=
    continuous_finsetProd _ fun p _ => h.cont p
  unfold zg
  calc |∫ a, ∏ p ∈ E, g p a ∂(νS N Lk)| ≤ ∫ a, |∏ p ∈ E, g p a| ∂(νS N Lk) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _a, ε ^ E.card ∂(νS N Lk) :=
        integral_mono (integrable_cont hc).abs (integrable_const _) hb
    _ = ε ^ E.card := ContactFloor.integral_const_prob _ _

theorem gAct_decay (h : SiteGas bd g ε) (hε : 0 ≤ ε) {T : ℝ} (hT : ε ≤ Real.exp (-T)) :
    Decay (gAct bd g) T := by
  classical
  intro X
  have h1 : Real.exp (-(T * X.card)) = Real.exp (-T) ^ X.card := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h1]
  by_cases hX : X.Nonempty ∧ TouchConnected bd X
  · rw [gAct_of hX]
    exact (abs_zg_le h hε X).trans (pow_le_pow_left₀ hε hT _)
  · unfold gAct
    rw [if_neg hX, abs_zero]
    positivity

/-! ## 2. The criterion -/

theorem exp_five_ge : (64 : ℝ) ≤ Real.exp 5 := by
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (64 : ℝ) ≤ 2.7 ^ 5 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 5

theorem exp_44_ge : (8450 : ℝ) ≤ Real.exp 44 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have e : Real.exp 44 = Real.exp 1 ^ 44 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (8450 : ℝ) ≤ 2 ^ 44 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 44

/-- **Kotecký–Preiss for the site gas.** At most `4` sites per plaquette, `16` plaquettes per site, a rooted count
`4225^m`, and `|g| ≤ e^{−88}`: `MatchAt (siteAct bd g) 1 5`. COMPUTED: `4 · 16 · e^{1 + 5 − 11} ≤ 1`, `2 · 4225 e^{−44} ≤ 1`.
CHOSEN: `88`, `5`. DERIVED: `4` the corners of a plaquette; `16` the plaquettes at a site (`card_star_le`);
`4225 = 65²` the rooted count of `card_connSets_le`. -/
theorem matchAt_gas (hbd : ∀ p, (linkSupp bd p).Nonempty) (h : SiteGas bd g ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-88)) (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hM : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16)
    (hK : ∀ v m, (connSets bd v m).card ≤ 4225 ^ m) : MatchAt.MatchAt (siteAct bd g) 1 5 := by
  have hq1 : 2 * (((4225 : ℕ) : ℝ) * Real.exp (-((88 : ℝ) / 2))) ≤ 1 := by
    have e : Real.exp (-((88 : ℝ) / 2)) = (Real.exp 44)⁻¹ := by
      rw [← Real.exp_neg]; norm_num
    rw [e]
    have h44 := exp_44_ge
    have hpos : 0 < Real.exp 44 := Real.exp_pos _
    push_cast
    rw [show (2 : ℝ) * (4225 * (Real.exp 44)⁻¹) = 8450 / Real.exp 44 by ring, div_le_one hpos]
    exact h44
  have hcount := countAt_link bd (w := gAct bd g) (t := 88) (c := 4) (M := 16) (K := 4225)
    (by norm_num) hc (by norm_num) hM hK (fun _ hX => (gAct_ne_zero hX).2) (gAct_decay h hε0 hε)
    (by norm_num) hq1
  refine MatchAt.matchAt_of_count (push_supp_empty hbd (gAct_empty bd g)) (z := ((16 : ℕ) : ℝ))
    (τ := 88 / (2 * ((4 : ℕ) : ℝ))) (κ := 5) (by positivity) (by norm_num) hcount ?_
  have e : (1 : ℝ) + 5 - 88 / (2 * ((4 : ℕ) : ℝ)) = -5 := by norm_num
  rw [e, Real.exp_neg]
  have h5 := exp_five_ge
  have hpos : 0 < Real.exp 5 := Real.exp_pos _
  push_cast
  rw [show (4 : ℝ) * 16 * (Real.exp 5)⁻¹ = 64 / Real.exp 5 by ring, div_le_one hpos]
  exact h5

end Generic

/-! ## 3. Removing polymers, and the truncation -/

section Local

variable {V : Type*} [Fintype V] [DecidableEq V] {w : Finset V → ℝ}

theorem cKP_le_eps (a : ℝ) (X : Finset V) : MatchAt.cKP w a X ≤ MatchAt.eps w a X := by
  have h := MatchAt.eps_nonneg w a X
  unfold MatchAt.cKP
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + MatchAt.eps w a X by linarith)
  linarith

/-- **Removing a family of polymers costs at most the sum of its Dobrushin weights.** No numeral. -/
theorem log_Z_sdiff_le {κ : ℝ} (hM : MatchAt.MatchAt w 1 κ) (T D : Finset (Finset V)) :
    |Real.log (MatchAt.Z MatchAt.meet w T) - Real.log (MatchAt.Z MatchAt.meet w (T \ D))|
      ≤ ∑ δ ∈ D, MatchAt.cKP w 1 δ := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d B hd ih =>
    have hG := MatchAt.G_insert (inc := MatchAt.meet) (w := w) (S := T) (B := B) (d := d)
    unfold MatchAt.G at hG
    have hL := MatchAt.abs_L_le MatchAt.meet_symm (MatchAt.dob_of_matchAt hM) (T \ B) d
    rw [hG, Finset.sum_insert hd]
    have := abs_add_le (Real.log (MatchAt.Z MatchAt.meet w T) - Real.log (MatchAt.Z MatchAt.meet w (T \ B)))
      (MatchAt.L MatchAt.meet w (T \ B) d)
    linarith

open scoped Classical in
/-- The polymers of `S` that contain `x`. No numeral. -/
def atSite (S : Finset (Finset V)) (x : V) : Finset (Finset V) := S.filter fun X => x ∈ X

open scoped Classical in
/-- **The local family**: the polymers of `S` that meet `Bin` and stay in `Bout`. No numeral. -/
def trunc (S : Finset (Finset V)) (Bin Bout : Finset V) : Finset (Finset V) :=
  S.filter fun X => (Bin ∩ X).Nonempty ∧ X ⊆ Bout

/-- `y = log Z(S) − log Z(S ∖ A)`, the log-ratio of adding the polymers at `x`. No numeral. -/
def yOf (w : Finset V → ℝ) (S : Finset (Finset V)) (x : V) : ℝ :=
  Real.log (MatchAt.Z MatchAt.meet w S) - Real.log (MatchAt.Z MatchAt.meet w (S \ atSite S x))

/-- `y` on the local family, with the polymers at `x` read from `S`. No numeral. -/
def yTr (w : Finset V → ℝ) (S : Finset (Finset V)) (Bin Bout : Finset V) (x : V) : ℝ :=
  Real.log (MatchAt.Z MatchAt.meet w (trunc S Bin Bout))
    - Real.log (MatchAt.Z MatchAt.meet w (trunc S Bin Bout \ atSite S x))

/-- **The truncation**: a polymer meeting `Bin` and leaving `Bout` is big, and the rest is `cluster_sites`. With `lev` a level
function, `Bin` the levels `≤ r`, `Bout` containing the levels `< 2 r + 2`, and active polymers of level spread at
most their size: `|y − y_tr| ≤ (2 |Bin| + 1) e^{−κ r}`. DERIVED: `2` the two removals of `D`; `1` the term of
`cluster_sites` at the single site `x`. -/
theorem abs_yOf_sub_le {κ : ℝ} (hM : MatchAt.MatchAt w 1 κ) (lev : V → ℕ) {x : V} {Bin Bout : Finset V}
    {r : ℕ} (hx0 : lev x = 0) (hxB : x ∈ Bin) (h3 : ∀ y, y ∉ Bin → r + 1 ≤ lev y)
    (h4 : ∀ y ∈ Bin, lev y ≤ r) (h5 : ∀ u, u ∉ Bout → 2 * r + 2 ≤ lev u)
    (hdiam : ∀ X, w X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X, (lev y : ℝ) - lev z ≤ X.card)
    (S : Finset (Finset V)) :
    |yOf w S x - yTr w S Bin Bout x| ≤ (2 * Bin.card + 1) * Real.exp (-(κ * r)) := by
  classical
  have hκ : 0 ≤ κ := hM.2.2.2.1
  set A := atSite S x with hA
  set D := S.filter (fun X => (Bin ∩ X).Nonempty ∧ ¬ X ⊆ Bout) with hD
  set U := S.filter (fun X => Disjoint X Bin) with hU
  set S0 := S \ D with hS0
  have hF : trunc S Bin Bout = S0 \ U := by
    ext X
    simp only [trunc, hS0, hD, hU, Finset.mem_filter, Finset.mem_sdiff, not_and, not_not]
    constructor
    · rintro ⟨hX, hm, hs⟩
      refine ⟨⟨hX, fun _ _ => hs⟩, fun _ hd => ?_⟩
      obtain ⟨z, hz⟩ := hm
      rw [Finset.mem_inter] at hz
      exact (Finset.disjoint_left.1 hd hz.2 hz.1).elim
    · rintro ⟨⟨hX, h1⟩, h2⟩
      have hm : (Bin ∩ X).Nonempty := by
        by_contra hc
        apply h2 hX
        rw [Finset.disjoint_left]
        intro z hz hb
        exact hc ⟨z, Finset.mem_inter.2 ⟨hb, hz⟩⟩
      exact ⟨hX, hm, h1 hX hm⟩
  have hdiam' : ∀ X, w X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X,
      (fun a b : V => |(lev a : ℝ) - lev b|) y z ≤ X.card := by
    intro X hw y hy z hz
    exact abs_le.2 ⟨by linarith [hdiam X hw z hz y hy], hdiam X hw y hy z hz⟩
  have hQ := MatchAt.cluster_sites hM (ρ := fun a b : V => |(lev a : ℝ) - lev b|)
    (dset := fun y => ((r : ℝ) + 1) - lev y)
    (fun a b => by
      have := neg_abs_le ((lev a : ℝ) - lev b)
      show ((r : ℝ) + 1) - lev a ≤ ((r : ℝ) + 1) - lev b + |(lev a : ℝ) - lev b|
      linarith)
    hdiam' (U := U)
    (fun Y hY _ y hy => by
      have hdisj := (Finset.mem_filter.1 hY).2
      have hyB : y ∉ Bin := fun hb => Finset.disjoint_left.1 hdisj hy hb
      have : ((r + 1 : ℕ) : ℝ) ≤ lev y := by exact_mod_cast h3 y hyB
      push_cast at this
      show ((r : ℝ) + 1) - lev y ≤ 0
      linarith)
    (Λ := {x}) (R := (r : ℝ) + 1)
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      subst hy
      simp [hx0])
    (A := A)
    (fun X hX => ⟨x, by
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_filter.1 hX).2, Finset.mem_singleton_self x⟩⟩)
    (fun X hX hU' => Finset.disjoint_left.1 (Finset.mem_filter.1 hU').2 (Finset.mem_filter.1 hX).2 hxB)
    S0
  have hsum : ∑ δ ∈ D, MatchAt.cKP w 1 δ ≤ Bin.card * Real.exp (-(κ * r)) := by
    have hpt : ∀ X ∈ D, MatchAt.cKP w 1 X ≤ Real.exp (-(κ * r)) * MatchAt.kp w 1 κ X := by
      intro X hX
      by_cases hw : w X = 0
      · have h0 : MatchAt.cKP w 1 X = 0 := by
          simp [MatchAt.cKP, MatchAt.eps, hw]
        rw [h0]
        exact mul_nonneg (Real.exp_pos _).le (MatchAt.kp_nonneg _ _ _ _)
      · obtain ⟨-, ⟨v, hv⟩, hns⟩ := Finset.mem_filter.1 hX
        rw [Finset.mem_inter] at hv
        obtain ⟨u, huX, huB⟩ := Finset.not_subset.1 hns
        have h1 := hdiam X hw u huX v hv.2
        have h2 : ((2 * r + 2 : ℕ) : ℝ) ≤ lev u := by exact_mod_cast h5 u huB
        have h3' : (lev v : ℝ) ≤ r := by exact_mod_cast h4 v hv.1
        push_cast at h2
        have hc : (r : ℝ) + 2 ≤ X.card := by linarith
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        have hexp : Real.exp (κ * r) ≤ Real.exp (κ * X.card) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hκ)
        have hkey : Real.exp (κ * r) ≤ 1 + (X.card : ℝ) * Real.exp (κ * X.card) := by
          have : Real.exp (κ * X.card) ≤ (X.card : ℝ) * Real.exp (κ * X.card) :=
            le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
          linarith
        have he := MatchAt.eps_nonneg w 1 X
        have hk : MatchAt.eps w 1 X * Real.exp (κ * r) ≤ MatchAt.kp w 1 κ X :=
          mul_le_mul_of_nonneg_left hkey he
        calc MatchAt.cKP w 1 X ≤ MatchAt.eps w 1 X := cKP_le_eps 1 X
          _ = Real.exp (-(κ * r)) * (MatchAt.eps w 1 X * Real.exp (κ * r)) := by
              rw [mul_comm (MatchAt.eps w 1 X), ← mul_assoc, ← Real.exp_add]
              simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    calc ∑ δ ∈ D, MatchAt.cKP w 1 δ ≤ ∑ δ ∈ D, Real.exp (-(κ * r)) * MatchAt.kp w 1 κ δ :=
          Finset.sum_le_sum hpt
      _ = Real.exp (-(κ * r)) * ∑ δ ∈ D, MatchAt.kp w 1 κ δ := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(κ * r)) * (Bin.card * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine (MatchAt.sum_meet_le _ (MatchAt.kp_nonneg w 1 κ) Bin D fun Y hY => ?_).trans
            (MatchAt.sum_site_le hM Bin)
          exact (Finset.mem_filter.1 hY).2.1
      _ = _ := by ring
  have t1 := log_Z_sdiff_le hM S D
  have t2 := log_Z_sdiff_le hM (S \ A) D
  have e0 : S0 \ A = (S \ A) \ D := sdiff_sdiff_comm
  have hexp1 : Real.exp (-(κ * ((r : ℝ) + 1))) ≤ Real.exp (-(κ * r)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hcard : (({x} : Finset V).card : ℝ) * 1 * Real.exp (-(κ * ((r : ℝ) + 1)))
      ≤ Real.exp (-(κ * r)) := by simpa using hexp1
  have hQ' := abs_le.1 (hQ.trans hcard)
  have hQ1 := hQ'.1
  have hQ2 := hQ'.2
  unfold MatchAt.Q at hQ1 hQ2
  rw [← hF] at hQ1 hQ2
  have ht1 := abs_le.1 (t1.trans hsum)
  have ht2 := abs_le.1 (t2.trans hsum)
  rw [← e0] at ht2
  unfold yOf yTr
  rw [← hA]
  have e1 : (2 * (Bin.card : ℝ) + 1) * Real.exp (-(κ * r))
      = 2 * ((Bin.card : ℝ) * Real.exp (-(κ * r))) + Real.exp (-(κ * r)) := by ring
  rw [e1]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]

theorem abs_yOf_le {κ : ℝ} (hM : MatchAt.MatchAt w 1 κ) (S : Finset (Finset V)) (x : V) :
    |yOf w S x| ≤ 1 := by
  classical
  refine (log_Z_sdiff_le hM S (atSite S x)).trans ?_
  have hpt : ∀ X ∈ atSite S x, MatchAt.cKP w 1 X ≤ MatchAt.kp w 1 κ X := fun X _ =>
    (cKP_le_eps 1 X).trans (MatchAt.eps_le_kp X)
  refine (Finset.sum_le_sum hpt).trans ?_
  have hsub : atSite S x ⊆ MatchAt.site x := by
    intro X hX
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hX).2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun X _ _ => MatchAt.kp_nonneg w 1 κ X).trans ?_
  exact hM.2.2.2.2 x

/-- `Z` reads the activities of its own family only. No numeral. -/
theorem Z_congr {w' : Finset V → ℝ} {F : Finset (Finset V)} (h : ∀ X ∈ F, w X = w' X) :
    MatchAt.Z MatchAt.meet w F = MatchAt.Z MatchAt.meet w' F := by
  unfold MatchAt.Z
  refine Finset.sum_congr rfl fun T hT => Finset.prod_congr rfl fun γ hγ => h γ ?_
  exact Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1 hγ

theorem yTr_congr {w' : Finset V → ℝ} {S : Finset (Finset V)} {Bin Bout : Finset V} {x : V}
    (h : ∀ X, X ⊆ Bout → w X = w' X) : yTr w S Bin Bout x = yTr w' S Bin Bout x := by
  classical
  have hF : ∀ X ∈ trunc S Bin Bout, w X = w' X := fun X hX => h X (Finset.mem_filter.1 hX).2.2
  unfold yTr
  rw [Z_congr hF, Z_congr fun X hX => hF X (Finset.mem_sdiff.1 hX).1]

/-! ## 4. The telescoping over the sites -/

/-- The sites before position `k` of the enumeration. No numeral. -/
def Bf (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) : Finset V :=
  univ.filter fun x => (Fintype.equivFin V x).val < k

theorem mem_Bf {k : ℕ} {x : V} : x ∈ Bf V k ↔ (Fintype.equivFin V x).val < k := by
  simp [Bf]

/-- The polymers on the sites up to `x`. DERIVED: `1` the next position. -/
def Sf (x : V) : Finset (Finset V) := (Bf V ((Fintype.equivFin V x).val + 1)).powerset

theorem Sf_sdiff (x : V) : Sf x \ atSite (Sf x) x = (Bf V (Fintype.equivFin V x).val).powerset := by
  classical
  ext X
  simp only [Sf, atSite, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_powerset, not_and]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    have hzx : z ≠ x := fun e => by
      subst e
      exact (h2 h1) hz
    have := mem_Bf.1 (h1 hz)
    have hne : (Fintype.equivFin V z).val ≠ (Fintype.equivFin V x).val := fun e =>
      hzx ((Fintype.equivFin V).injective (Fin.ext e))
    exact mem_Bf.2 (by omega)
  · intro h
    refine ⟨fun z hz => ?_, fun _ hc => ?_⟩
    · exact mem_Bf.2 (by have := mem_Bf.1 (h hz); omega)
    · exact absurd (mem_Bf.1 (h hc)) (lt_irrefl _)

/-- **`log Z` telescopes over the sites**: `Σ_x y_x = log Z(all) − log Z(∅)`. No numeral. -/
theorem sum_yOf (w : Finset V → ℝ) :
    ∑ x, yOf w (Sf x) x = Real.log (MatchAt.Z MatchAt.meet w univ)
      - Real.log (MatchAt.Z MatchAt.meet w (∅ : Finset V).powerset) := by
  classical
  set m := Fintype.card V with hm
  set f : ℕ → ℝ := fun k => Real.log (MatchAt.Z MatchAt.meet w (Bf V k).powerset) with hf
  have hy : ∀ x, yOf w (Sf x) x = f ((Fintype.equivFin V x).val + 1) - f (Fintype.equivFin V x).val := by
    intro x
    unfold yOf
    rw [Sf_sdiff]
    rfl
  simp_rw [hy]
  have h1 := Equiv.sum_comp (Fintype.equivFin V) fun i : Fin m => f (i.val + 1) - f i.val
  rw [h1, Fin.sum_univ_eq_sum_range (fun k => f (k + 1) - f k) m, Finset.sum_range_sub]
  have e0 : Bf V 0 = ∅ := by ext x; simp [Bf]
  have em : Bf V m = univ := by
    ext x
    simp only [Bf, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (Fintype.equivFin V x).isLt
  simp only [hf, e0, em, Finset.powerset_univ]

end Local

/-! ## 5. Balls and levels -/

section Levels

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]
  {bd : Pq → List (Lk × Bool)}

open scoped Classical in
/-- The sites sharing a plaquette with `u`. No numeral. -/
def nbS (bd : Pq → List (Lk × Bool)) (u : Lk) : Finset Lk :=
  (univ.filter fun p => u ∈ linkSupp bd p).biUnion (linkSupp bd)

/-- **The ball of radius `k` around `x`.** DERIVED: `0`, `1` the recursion. -/
def ball (bd : Pq → List (Lk × Bool)) (x : Lk) : ℕ → Finset Lk
  | 0 => {x}
  | k + 1 => ball bd x k ∪ (ball bd x k).biUnion (nbS bd)

theorem ball_subset_succ (x : Lk) (k : ℕ) : ball bd x k ⊆ ball bd x (k + 1) :=
  Finset.subset_union_left

theorem ball_mono (x : Lk) {j k : ℕ} (h : j ≤ k) : ball bd x j ⊆ ball bd x k := by
  induction k, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact ih.trans (ball_subset_succ x k)

/-- The neighbours of a site. DERIVED: `64 = 16 · 4`. -/
theorem card_nbS_le (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hM : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16) (u : Lk) : (nbS bd u).card ≤ 64 := by
  classical
  unfold nbS
  refine (Finset.card_biUnion_le_card_mul _ _ 4 fun p _ => hc p).trans ?_
  have : (univ.filter fun p => u ∈ linkSupp bd p).card ≤ 16 := by convert hM u
  omega

/-- **The size of a ball**: `|ball k| ≤ 65^k`. DERIVED: `65 = 64 + 1`, `64 = 4 · 16`; `4` the corners of a
plaquette; `16` the plaquettes at a site (`card_star_le`). -/
theorem card_ball_le (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hM : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16) (x : Lk) (k : ℕ) :
    (ball bd x k).card ≤ 65 ^ k := by
  induction k with
  | zero => simp [ball]
  | succ k ih =>
    have h1 := Finset.card_union_le (ball bd x k) ((ball bd x k).biUnion (nbS bd))
    have h2 := Finset.card_biUnion_le_card_mul (ball bd x k) (nbS bd) 64
      fun u _ => card_nbS_le hc hM u
    show (ball bd x k ∪ (ball bd x k).biUnion (nbS bd)).card ≤ _
    rw [pow_succ]
    omega

theorem exists_lev (x y : Lk) (R : ℕ) : ∃ k, y ∈ ball bd x k ∨ k = R := ⟨R, Or.inr rfl⟩

open scoped Classical in
/-- **The level of `y` from `x`, capped at `R`.** No numeral. -/
def lev (bd : Pq → List (Lk × Bool)) (x : Lk) (R : ℕ) (y : Lk) : ℕ := Nat.find (exists_lev (bd := bd) x y R)

theorem lev_spec (x : Lk) (R : ℕ) (y : Lk) : y ∈ ball bd x (lev bd x R y) ∨ lev bd x R y = R := by
  classical
  exact Nat.find_spec (exists_lev (bd := bd) x y R)

theorem lev_le_of_mem {x y : Lk} {R k : ℕ} (h : y ∈ ball bd x k) : lev bd x R y ≤ k := by
  classical
  exact Nat.find_min' _ (Or.inl h)

theorem lev_le (x y : Lk) (R : ℕ) : lev bd x R y ≤ R := by
  classical
  exact Nat.find_min' _ (Or.inr rfl)

theorem ge_lev_of_notMem {x y : Lk} {R k : ℕ} (hk : k < R) (h : y ∉ ball bd x k) :
    k + 1 ≤ lev bd x R y := by
  by_contra hc
  have hle : lev bd x R y ≤ k := by omega
  rcases lev_spec (bd := bd) x R y with h1 | h1
  · exact h (ball_mono x hle h1)
  · omega

theorem lev_root (x : Lk) (R : ℕ) : lev bd x R x = 0 := by
  have : lev bd x R x ≤ 0 := lev_le_of_mem (k := 0) (Finset.mem_singleton_self x)
  omega

/-- **The level is `1`-Lipschitz on a plaquette.** DERIVED: `1` one step. -/
theorem lev_lip (x : Lk) (R : ℕ) {p : Pq} {u v : Lk} (hu : u ∈ linkSupp bd p) (hv : v ∈ linkSupp bd p) :
    lev bd x R u ≤ lev bd x R v + 1 := by
  classical
  rcases lev_spec (bd := bd) x R v with h | h
  · refine lev_le_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, h, ?_⟩))
    exact Finset.mem_biUnion.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, hu⟩
  · have := lev_le (bd := bd) x u R
    omega

/-- **A connected polymer has no gap in its levels.** DERIVED: `1` as in `lev_lip`. -/
theorem lev_interval {lv : Lk → ℕ}
    (hlv : ∀ (p : Pq) (u v : Lk), u ∈ linkSupp bd p → v ∈ linkSupp bd p → lv u ≤ lv v + 1)
    {E : Finset Pq} (hE : TouchConnected bd E) {p q : Pq} (hp : p ∈ E) (hq : q ∈ E) {y z : Lk}
    (hy : y ∈ linkSupp bd p) (hz : z ∈ linkSupp bd q) {j : ℕ} (h1 : lv y ≤ j) (h2 : j ≤ lv z) :
    ∃ u ∈ supp bd E, lv u = j := by
  by_contra hno
  push Not at hno
  have hstart : ∀ u ∈ linkSupp bd p, lv u < j := by
    intro u hu
    have hyj : lv y ≠ j := hno y (mem_supp.2 ⟨p, hp, hy⟩)
    have huj : lv u ≠ j := hno u (mem_supp.2 ⟨p, hp, hu⟩)
    have := hlv p u y hu hy
    omega
  have key : ∀ q', Relation.ReflTransGen (fun a b => a ∈ E ∧ b ∈ E ∧ Touch bd a b) p q' →
      ∀ u ∈ linkSupp bd q', lv u < j := by
    intro q' hr
    induction hr with
    | refl => exact hstart
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hc, l, hlb, hlc⟩ := hbc
      intro u hu
      have hl := ih l hlb
      have huj : lv u ≠ j := hno u (mem_supp.2 ⟨c, hc, hu⟩)
      have := hlv c u l hu hlc
      omega
  have := key q (hE p hp q hq) z hz
  omega

/-- **An active polymer has level spread at most its size.** DERIVED: `0` the sign. -/
theorem lev_diam {N : ℕ} {g : Pq → (Lk → SU N) → ℝ} {lv : Lk → ℕ}
    (hlv : ∀ (p : Pq) (u v : Lk), u ∈ linkSupp bd p → v ∈ linkSupp bd p → lv u ≤ lv v + 1)
    (X : Finset Lk) (hw : siteAct bd g X ≠ 0) (y : Lk) (hy : y ∈ X) (z : Lk) (hz : z ∈ X) :
    (lv y : ℝ) - lv z ≤ X.card := by
  classical
  obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have hsup : supp bd E = X := mem_fib.1 hE
  have hc := (gAct_ne_zero hne).2
  by_cases hle : lv y ≤ lv z
  · have h1 : (lv y : ℝ) ≤ lv z := by exact_mod_cast hle
    have h2 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    linarith
  · obtain ⟨p, hp, hyp⟩ := mem_supp.1 (hsup ▸ hy)
    obtain ⟨q, hq, hzq⟩ := mem_supp.1 (hsup ▸ hz)
    have hsub : Finset.Icc (lv z) (lv y) ⊆ X.image lv := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨u, hu, huj⟩ := lev_interval hlv hc hq hp hzq hyp hj.1 hj.2
      exact Finset.mem_image.2 ⟨u, hsup ▸ hu, huj⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Nat.card_Icc] at h1
    have h2 : (lv y : ℝ) ≤ (X.card : ℝ) + lv z - 1 := by
      have : lv y + 1 ≤ X.card + lv z := by omega
      have h3 : ((lv y + 1 : ℕ) : ℝ) ≤ ((X.card + lv z : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h3
      linarith
    linarith

end Levels

/-! ## 6. The site sum, in general -/

section Assembly

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]
  {bd : Pq → List (Lk × Bool)} {g : Pq → (Lk → SU N) → ℝ} {ε : ℝ}

/-- The summand at `x`. No numeral. -/
def yG (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) (x : Lk) : ℝ := yOf (siteAct bd g) (Sf x) x

/-- The truncated summand at `x` and radius `r`. DERIVED: `2 r + 1` the outer ball. -/
def yGT (bd : Pq → List (Lk × Bool)) (g : Pq → (Lk → SU N) → ℝ) (r : ℕ) (x : Lk) : ℝ :=
  yTr (siteAct bd g) (Sf x) (ball bd x r) (ball bd x (2 * r + 1)) x

theorem inW_empty (hbd : ∀ p, (linkSupp bd p).Nonempty) : inW bd (∅ : Finset Lk) = ∅ := by
  classical
  ext p
  simp only [mem_inW, Finset.notMem_empty, iff_false, Finset.subset_empty]
  exact (hbd p).ne_empty

theorem inW_univ : inW bd (univ : Finset Lk) = univ := by
  classical
  ext p
  simp [mem_inW]

theorem Yg_empty (g : Pq → (Lk → SU N) → ℝ) : Yg g (∅ : Finset Pq) = 1 := by
  unfold Yg
  simp

/-- **`log Y` is a sum over the sites.** DERIVED: `1` the empty gas. -/
theorem log_Y_eq_sum (hbd : ∀ p, (linkSupp bd p).Nonempty) (h : SiteGas bd g ε) :
    Real.log (Yg g univ) = ∑ x, yG bd g x := by
  classical
  have h1 := Y_eq_siteZ hbd h (univ : Finset Lk)
  have h0 := Y_eq_siteZ hbd h (∅ : Finset Lk)
  rw [inW_univ, Finset.powerset_univ] at h1
  rw [inW_empty hbd, Yg_empty] at h0
  unfold yG
  rw [sum_yOf, ← h1, ← h0, Real.log_one, sub_zero]

/-- **The tail.** With `MatchAt` at `κ = 5`: `|y_x − y_x^r| ≤ (2 · 65^r + 1) e^{−5 r}`. DERIVED: `2 r + 2` the cap of the
level; `5` the rate `κ` of `matchAt_gas`; `4`, `16`, `65` the corners, the plaquettes at a site and the ball
growth of `card_ball_le`. -/
theorem abs_yG_sub_le (hM : MatchAt.MatchAt (siteAct bd g) 1 5) (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hMc : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16) (x : Lk) (r : ℕ) :
    |yG bd g x - yGT bd g r x| ≤ (2 * 65 ^ r + 1) * Real.exp (-(5 * r)) := by
  classical
  set R := 2 * r + 2 with hR
  have hlv : ∀ (p : Pq) (u v : Lk), u ∈ linkSupp bd p → v ∈ linkSupp bd p →
      lev bd x R u ≤ lev bd x R v + 1 := fun p u v hu hv => lev_lip x R hu hv
  have hb := abs_yOf_sub_le hM (lev bd x R) (x := x) (Bin := ball bd x r) (Bout := ball bd x (2 * r + 1))
    (r := r) (lev_root x R) (ball_mono x (Nat.zero_le r) (Finset.mem_singleton_self x))
    (fun y hy => ge_lev_of_notMem (by omega) hy)
    (fun y hy => lev_le_of_mem hy)
    (fun u hu => by
      have := ge_lev_of_notMem (R := R) (by omega) hu
      omega)
    (fun X hX y hy z hz => lev_diam hlv X hX y hy z hz) (Sf x)
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have : ((ball bd x r).card : ℝ) ≤ 65 ^ r := by exact_mod_cast card_ball_le hc hMc x r
  linarith

theorem abs_yG_le (hM : MatchAt.MatchAt (siteAct bd g) 1 5) (x : Lk) : |yG bd g x| ≤ 1 :=
  abs_yOf_le hM _ x

/-- **The truncated summand reads the plaquettes of the outer ball only.** No numeral. -/
theorem yGT_congr {g' : Pq → (Lk → SU N) → ℝ} {r : ℕ} {x : Lk}
    (h : ∀ p ∈ inW bd (ball bd x (2 * r + 1)), g p = g' p) : yGT bd g r x = yGT bd g' r x := by
  classical
  unfold yGT
  refine yTr_congr fun X hX => ?_
  unfold siteAct push
  refine Finset.sum_congr rfl fun E hE => ?_
  have hs : supp bd E = X := mem_fib.1 hE
  have hin : ∀ p ∈ E, g p = g' p := fun p hp => h p (mem_inW.2 fun z hz =>
    hX (hs ▸ mem_supp.2 ⟨p, hp, hz⟩))
  have hz : zg g E = zg g' E := by
    unfold zg
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    exact Finset.prod_congr rfl fun p hp => by rw [hin p hp]
  unfold gAct
  simp only [hz]

end Assembly

/-! ## 7. The mixed plaquettes -/

section Mixed

open MassGap.CumulantStrip MassGap.MixCut MassGap.MixExpand MassGap.MixEqui MassGap.RectWilson MassGap.StripWidth

variable {N n : ℕ}

/-- The four corners of a mixed plaquette, as a boundary list. DERIVED: `4` the corners. -/
def cbd (p : Pm n) : List (St n × Bool) :=
  [(fw p 0, true), (fw p 1, true), (fw p 2, true), (fw p 3, true)]

theorem mem_ls {p : Pm n} {z : St n} : z ∈ linkSupp cbd p ↔ Cn p z := by
  unfold linkSupp cbd Cn MassGap.MixEqui.IsCorner
  simp [fw]

theorem ls_nonempty (p : Pm n) : (linkSupp (cbd (n := n)) p).Nonempty := ⟨p.2, mem_ls.2 (Or.inl rfl)⟩

theorem ls_card (p : Pm n) : (linkSupp (cbd (n := n)) p).card ≤ 4 := by
  unfold linkSupp cbd
  exact List.toFinset_card_le _ |>.trans (by simp)

theorem ls_mult (z : St n) : (univ.filter fun p : Pm n => z ∈ linkSupp cbd p).card ≤ 16 := by
  refine (Finset.card_le_card fun p hp => ?_).trans (card_star_le z)
  exact mem_star (mem_ls.1 (Finset.mem_filter.1 hp).2)

theorem touchDeg_le : touchDeg (cbd (n := n)) ≤ 64 := by
  classical
  unfold touchDeg
  refine Finset.sup_le fun p _ => (Finset.card_le_card fun q hq => ?_).trans (card_Tch_le p)
  obtain ⟨l, h1, h2⟩ := mem_touchNbrs.1 hq
  exact mem_Tch.2 ⟨l, mem_ls.1 h1, mem_ls.1 h2⟩

theorem connSets_le (v : Pm n) (m : ℕ) : (connSets cbd v m).card ≤ 4225 ^ m := by
  refine (card_connSets_le cbd v m).trans (Nat.pow_le_pow_left ?_ m)
  have := touchDeg_le (n := n)
  have h2 : touchDeg (cbd (n := n)) + 1 ≤ 65 := by omega
  calc (touchDeg (cbd (n := n)) + 1) ^ 2 ≤ 65 ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 4225 := by norm_num

/-- **The tilted plaquette as a function of the rotation**, given the links `U`. No numeral. -/
def gR (N n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) (p : Pm n) (a : St n → SUN.SU N) : ℝ :=
  gg N n (cT N t) p (gT (fun _ => n) a U)

theorem continuous_gT_joint :
    Continuous fun q : (St n → SUN.SU N) × (Lk n → SUN.SU N) => gT (fun _ => n) q.1 q.2 := by
  refine continuous_pi fun l => ?_
  unfold gT
  by_cases h : l.1.val / 2 = 0
  · simp only [if_pos h]
    exact (((continuous_apply l.2).comp continuous_fst).mul ((continuous_apply l).comp continuous_snd)).mul
      ((continuous_apply _).comp continuous_fst).inv
  · simp only [if_neg h]
    exact (continuous_apply l).comp continuous_snd

theorem gR_reads (t : ℝ) (U : Lk n → SUN.SU N) (p : Pm n) (a a' : St n → SUN.SU N)
    (h : ∀ z ∈ linkSupp cbd p, a z = a' z) : gR N n t U p a = gR N n t U p a' := by
  have hc : ∀ z, Cn p z → a z = a' z := fun z hz => h z (mem_ls.2 hz)
  have h0 := hc p.2 (Or.inl rfl)
  have h1 := hc _ (Or.inr (Or.inl rfl))
  have h2 := hc _ (Or.inr (Or.inr (Or.inl rfl)))
  have h3 := hc _ (Or.inr (Or.inr (Or.inr rfl)))
  unfold gR gg plaq pl
  rw [hol_eq, hol_eq]
  simp only [gT, if_pos (dirLo_block _), if_neg (dirHi_block _)]
  rw [h0, h1, h2, h3]

theorem continuous_gR (t : ℝ) (U : Lk n → SUN.SU N) (p : Pm n) : Continuous (gR N n t U p) := by
  have h1 : Continuous fun a : St n → SUN.SU N => gT (fun _ => n) a U := by
    refine continuous_pi fun l => ?_
    unfold gT
    by_cases h : l.1.val / 2 = 0
    · simp only [if_pos h]
      exact ((continuous_apply l.2).mul continuous_const).mul (continuous_apply _).inv
    · simp only [if_neg h]
      exact continuous_const
  have h2 := (continuous_gg (N := N) n (continuous_cT N t) p).comp h1
  exact h2

theorem abs_gR_le (hN : N ≠ 0) {t : ℝ} (ht : 8 * |t| ≤ 1) (U : Lk n → SUN.SU N) (p : Pm n)
    (a : St n → SUN.SU N) : |gR N n t U p a| ≤ 16 * |t| := by
  have hb : ∀ V : Lk n → SUN.SU N, |gg N n (cT N t) p V| ≤ 16 * |t| := fun V => abs_cT_le hN ht _
  exact hb _

/-- **The site gas of the mixed plaquettes**, given `U`. Inherited: `8 |t| ≤ 1` the range of `abs_cT_le`, `16` its bound. -/
theorem gasR (hN : N ≠ 0) {t : ℝ} (ht : 8 * |t| ≤ 1) (U : Lk n → SUN.SU N) :
    SiteGas cbd (gR N n t U) (16 * |t|) :=
  SiteGas.mk (continuous_gR t U) (abs_gR_le hN ht U) (gR_reads t U)

/-- **The width of the first layer** `t₁ = e^{−88}/16`. No `N`, `β`, `n`, `U`. CHOSEN: `88`. Inherited: `16` of `abs_cT_le`. -/
def tOne : ℝ := Real.exp (-88) / 16

theorem tOne_pos : 0 < tOne := by unfold tOne; positivity

theorem range_of_le {t : ℝ} (ht : |t| ≤ tOne) : 8 * |t| ≤ 1 ∧ 16 * |t| ≤ Real.exp (-88) := by
  have h1 : Real.exp (-88) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  unfold tOne at ht
  constructor <;> linarith [abs_nonneg t]

/-- **Kotecký–Preiss, at a width independent of `β`, `N`, `n`, `U`.** CHOSEN: as in `matchAt_gas`, `1` and `5` its `MatchAt` constants. -/
theorem gasR_matchAt (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ tOne) (U : Lk n → SUN.SU N) :
    MatchAt.MatchAt (siteAct cbd (gR N n t U)) 1 5 :=
  matchAt_gas ls_nonempty (gasR hN (range_of_le ht).1 U) (by positivity) (range_of_le ht).2 ls_card
    ls_mult connSets_le

/-- **The conditional integral** `Y(U) = ∫ da ∏_p (1 + g_p(gT a U))`. No numeral. -/
def YR (N n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) : ℝ := Yg (gR N n t U) univ

/-- The summand `y_x(U)`, for the enumeration of the sites of `Fintype.equivFin`. No numeral. -/
def yR (N n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) (x : St n) : ℝ := yG cbd (gR N n t U) x

/-- The truncated summand `y_x^r(U)`. No numeral. -/
def yRT (N n : ℕ) (t : ℝ) (r : ℕ) (U : Lk n → SUN.SU N) (x : St n) : ℝ := yGT cbd (gR N n t U) r x

/-- **`Y(U) > 0`.** `Y` is the partition function of a Kotecký–Preiss gas, positive by `MatchAt.Z_pos`. DERIVED: `0` the sign. -/
theorem YR_pos (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ tOne) (U : Lk n → SUN.SU N) : 0 < YR N n t U := by
  have hM := gasR_matchAt (n := n) hN ht U
  have h1 := Y_eq_siteZ ls_nonempty (gasR hN (range_of_le ht).1 U) (univ : Finset (St n))
  rw [inW_univ, Finset.powerset_univ] at h1
  unfold YR
  rw [h1]
  exact MatchAt.Z_pos MatchAt.meet_symm (MatchAt.dob_of_matchAt hM) _

/-- **`log Y(U) = Σ_x y_x(U)`.** No numeral. -/
theorem log_YR_eq_sum (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ tOne) (U : Lk n → SUN.SU N) :
    Real.log (YR N n t U) = ∑ x, yR N n t U x :=
  log_Y_eq_sum ls_nonempty (gasR hN (range_of_le ht).1 U)

/-- **`|y_x(U)| ≤ 1`.** DERIVED: `1` the parameter `a`. -/
theorem abs_yR_le (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ tOne) (U : Lk n → SUN.SU N) (x : St n) :
    |yR N n t U x| ≤ 1 :=
  abs_yG_le (gasR_matchAt hN ht U) x

/-- **The tail**: `|y_x(U) − y_x^r(U)| ≤ 3 (65/e⁵)^r`, uniformly in `U`, `N`, `n`, `t`. COMPUTED: `2 · 65^r + 1 ≤ 3 · 65^r`. -/
theorem abs_yR_sub_le (hN : N ≠ 0) {t : ℝ} (ht : |t| ≤ tOne) (U : Lk n → SUN.SU N) (x : St n) (r : ℕ) :
    |yR N n t U x - yRT N n t r U x| ≤ 3 * (65 / Real.exp 5) ^ r := by
  refine (abs_yG_sub_le (gasR_matchAt hN ht U) ls_card ls_mult x r).trans ?_
  have h1 : (1 : ℝ) ≤ 65 ^ r := one_le_pow₀ (by norm_num)
  have e : Real.exp (-(5 * (r : ℝ))) = (Real.exp 5 ^ r)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring_nf
  rw [e, div_pow, div_eq_mul_inv, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **`65/e⁵ < 1/2`.** COMPUTED: `130 < e⁵`. -/
theorem ratio_lt : 65 / Real.exp 5 < 1 / 2 := by
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have e : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (130 : ℝ) < Real.exp 5 := by
    rw [e]
    calc (130 : ℝ) < 2.7 ^ 5 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 5
  rw [div_lt_iff₀ (Real.exp_pos _)]
  linarith

/-- The links read by `p`. DERIVED: `4` the links of a plaquette. -/
def plLinks (p : Pm n) : List (Lk n) :=
  [(dirLo p.1.1, p.2), (dirHi p.1.2, rshift (fun _ => n) (dirLo p.1.1) p.2),
    (dirLo p.1.1, rshift (fun _ => n) (dirHi p.1.2) p.2), (dirHi p.1.2, p.2)]

theorem gR_congr (t : ℝ) {U U' : Lk n → SUN.SU N} {p : Pm n} (h : ∀ l ∈ plLinks p, U l = U' l) :
    gR N n t U p = gR N n t U' p := by
  funext a
  unfold gR gg plaq pl
  rw [hol_eq, hol_eq]
  simp only [gT, if_pos (dirLo_block _), if_neg (dirHi_block _)]
  rw [h (dirLo p.1.1, p.2) (by simp [plLinks]),
    h (dirHi p.1.2, rshift (fun _ => n) (dirLo p.1.1) p.2) (by simp [plLinks]),
    h (dirLo p.1.1, rshift (fun _ => n) (dirHi p.1.2) p.2) (by simp [plLinks]),
    h (dirHi p.1.2, p.2) (by simp [plLinks])]

/-- **`y_x^r` is local**: it depends on `U` only through the links of the plaquettes with all corners in the ball of radius
`2 r + 1` at `x`. DERIVED: `2 r + 1` as in `yGT`. -/
theorem yRT_congr (t : ℝ) {U U' : Lk n → SUN.SU N} {r : ℕ} {x : St n}
    (h : ∀ p ∈ inW cbd (ball cbd x (2 * r + 1)), ∀ l ∈ plLinks p, U l = U' l) :
    yRT N n t r U x = yRT N n t r U' x :=
  yGT_congr fun p hp => gR_congr t (h p hp)

/-- **The mixed gas is the average of `Y` against the decoupled weight**: `Z_gas(all) = ∫ e^{−β S_in(U)} Y(U) dU`.
`gT` preserves product Haar and `S_in`. No numeral. -/
theorem ZG_eq_integral_YR (β t : ℝ) (n : ℕ) :
    ZG (piH N n) (fun U => Real.exp (-(β * sinR N n U))) (gg N n (cT N t)) univ
      = ∫ U, Real.exp (-(β * sinR N n U)) * YR N n t U ∂piH N n := by
  obtain ⟨W, hW⟩ : ∃ W : (Lk n → SUN.SU N) → ℝ, W = fun U => Real.exp (-(β * sinR N n U)) := ⟨_, rfl⟩
  have hWc : Continuous W := by
    rw [hW]
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hP : Continuous fun U : Lk n → SUN.SU N => ∏ q : Pm n, (1 + gg N n (cT N t) q U) :=
    continuous_finsetProd _ fun q _ => continuous_const.add (continuous_gg n (continuous_cT N t) q)
  have hF : Continuous fun U : Lk n → SUN.SU N => (∏ q : Pm n, (1 + gg N n (cT N t) q U)) * W U := hP.mul hWc
  have hinv : ∀ a : St n → SUN.SU N,
      ∫ U, (∏ q : Pm n, (1 + gg N n (cT N t) q (gT (fun _ => n) a U))) * W U ∂piH N n
        = ∫ U, (∏ q : Pm n, (1 + gg N n (cT N t) q U)) * W U ∂piH N n := by
    intro a
    have h := integral_gT (N := N) (fun _ => n) a _ hF
    refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans h
    show _ = (∏ q : Pm n, (1 + gg N n (cT N t) q (gT (fun _ => n) a U))) * W (gT (fun _ => n) a U)
    rw [hW]
    simp only [sinR_gT]
  have hJ : Continuous fun q : (St n → SUN.SU N) × (Lk n → SUN.SU N) =>
      (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) q.1 q.2))) * W q.2 :=
    (hP.comp continuous_gT_joint).mul (hWc.comp continuous_snd)
  obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hJ
  have hint : Integrable (fun q : (St n → SUN.SU N) × (Lk n → SUN.SU N) =>
      (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) q.1 q.2))) * W q.2)
      ((νS N (St n)).prod (piH N n)) :=
    HeatBath.integrable_of_abs_le _ hJ.measurable hC
  have hswap := integral_integral_swap (f := fun (a : St n → SUN.SU N) (U : Lk n → SUN.SU N) =>
    (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) a U))) * W U) hint
  have key : ∫ U, (∏ q : Pm n, (1 + gg N n (cT N t) q U)) * W U ∂piH N n
      = ∫ U, W U * YR N n t U ∂piH N n := by
    calc ∫ U, (∏ q : Pm n, (1 + gg N n (cT N t) q U)) * W U ∂piH N n
        = ∫ _a, ∫ U, (∏ q : Pm n, (1 + gg N n (cT N t) q U)) * W U ∂piH N n ∂(νS N (St n)) :=
          (ContactFloor.integral_const_prob _ _).symm
      _ = ∫ a, ∫ U, (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) a U))) * W U ∂piH N n
            ∂(νS N (St n)) :=
          integral_congr_ae (Eventually.of_forall fun a => (hinv a).symm)
      _ = ∫ U, ∫ a, (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) a U))) * W U ∂(νS N (St n))
            ∂piH N n := hswap
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun U => ?_)
          show (∫ a, (∏ r : Pm n, (1 + gg N n (cT N t) r (gT (fun _ => n) a U))) * W U ∂(νS N (St n)))
            = W U * YR N n t U
          rw [integral_mul_const, mul_comm]
          rfl
  unfold ZG
  rw [hW] at key
  exact key

end Mixed

end MassGap.StripGas

#print axioms MassGap.StripGas.zg_union
#print axioms MassGap.StripGas.Y_eq_Z
#print axioms MassGap.StripGas.Y_eq_siteZ
#print axioms MassGap.StripGas.matchAt_gas
#print axioms MassGap.StripGas.log_Z_sdiff_le
#print axioms MassGap.StripGas.abs_yOf_sub_le
#print axioms MassGap.StripGas.sum_yOf
#print axioms MassGap.StripGas.card_ball_le
#print axioms MassGap.StripGas.lev_diam
#print axioms MassGap.StripGas.log_Y_eq_sum
#print axioms MassGap.StripGas.abs_yG_sub_le
#print axioms MassGap.StripGas.yGT_congr
#print axioms MassGap.StripGas.gasR
#print axioms MassGap.StripGas.gasR_matchAt
#print axioms MassGap.StripGas.YR_pos
#print axioms MassGap.StripGas.log_YR_eq_sum
#print axioms MassGap.StripGas.abs_yR_le
#print axioms MassGap.StripGas.abs_yR_sub_le
#print axioms MassGap.StripGas.ratio_lt
#print axioms MassGap.StripGas.yRT_congr
#print axioms MassGap.StripGas.ZG_eq_integral_YR
#print axioms MassGap.StripGas.abs_yG_le
#print axioms MassGap.StripGas.abs_yOf_le
#print axioms MassGap.StripGas.abs_zg_le
#print axioms MassGap.StripGas.gR_congr
#print axioms MassGap.StripGas.connSets_le
#print axioms MassGap.StripGas.touchDeg_le
#print axioms MassGap.StripGas.range_of_le
