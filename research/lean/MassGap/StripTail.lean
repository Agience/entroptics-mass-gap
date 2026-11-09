import Mathlib
import MassGap.CumulantStrip

/-!
# MassGap.StripTail — the plane forgets its torus, and what the constant-width strip still needs

`CumulantStrip.DA_le_quartic` costs `C 16^w t⁴`, uniformly in `β`, so its strip shrinks with the seed window `w`. A strip of constant width needs that
cost to die with the window. This module proves the two statements that frame that target and the forgetting of the
2D torus measure, relative to the value of the observable. It does not prove the target. Declarations are in `MassGap.StripTail`.

## The result

* `tail_closes`, `tail_iff`: for `N ≠ 0`, `β, t ≥ 0`, the cost `DA(β, t, w) − DA(β, 0, w)` tends to `0` if and only if it is at
  most `1/2000` at infinitely many windows; then `DA(β, t, ·) → 0` and `StripLift.TransferGapAt` holds from a window on.
  So any rate suffices: no rate of `ρ`, and no comparison with `A_glue`, enters the strip.
* `cost_le_of_mixCut`: `|mixCut(β, s, w)| ≤ K s³` on `[0, t]` gives `|DA(β, t, w) − DA(β, 0, w)| ≤ K t⁴/4`.
* `sw_le_hole`, `prod_sw_le`: `sw ≤ (1 − e^{−4β}) wt` pointwise, so `∏_E sw ≤ (1 − e^{−4β})^{|E|} ∏_E wt` on every
  configuration. Argued, not a Lean statement: in the floor expansion `wt = fl + sw`, a face is a hole with conditional
  probability `fl/wt ≥ fl` given all the links, and this survives every nonnegative tilt, so it is uniform in `t`.
* `integral_mul_prod_peel`: `∫ G ∏_S s = (∫ s)^{|S|} ∫ G` for `S ⊊ E`, when every proper subset of `E` has a face
  with a link to a face outside the subset, unread by `G` (`Exits`). `TwoDVanish.integral_prod_proper` is the case `G = 1`.
* `forget_eq`: `∫ G ∏_E wt = (b^{|E|} − c^{|E|}) ∫ G + ∫ G ∏_E sw`, exactly. `forget_bounds`: for `G ≥ 0`, with
  `m = b^{|E|} − c^{|E|}`, `δ = (1 − fl)^{|E|}`: `m ∫ G ≤ ∫ G ∏_E wt` and `(1 − δ) ∫ G ∏_E wt ≤ m ∫ G`.
  Integrating out `E` leaves a weight that is constant up to the relative error `δ`, for every such `G`.
* `plane_forget`, `plane_compare`: for `N ≠ 0`, `2 ≤ n`, `r + 1 ≤ n`, on the side-`n` torus, every nonnegative continuous `G` of the links of an `r × r`
  rectangle has `(1 − δ_n) ⟨G⟩_box ≤ ⟨G⟩_n ≤ ⟨G⟩_box/(1 − δ_n)`, `δ_n = (1 − e^{−4β})^{n² − r²}`, `⟨·⟩_box` the free
  rectangle measure, which does not know `n`; `⟨·⟩_n` is `planeMean`, built from the product of `wt`, the Wilson
  torus expectation through `TwoDVanish.boltz_eq`. So two torus sides agree on `G` up to `δ_n`, `δ_{n'}`, relative to the
  value of `G` and not to its sup. No gauge invariance of `G` is used.

## The target, on paper

Argued, not proved.

* The route has two layers. Given all the links, the rotations `MixCut.gT` make the mixed plaquettes a gas of
  finite-range functions of i.i.d. Haar site variables; each `g_p` is centred in each of its four corners separately
  (`CumulantStrip.cent_factor_c`). Its Kotecký–Preiss criterion (`MatchAt`, `PolymerCount`) is met at a `t₁` independent
  of `β`, `N` and of the links. The criterion and `log ∫ ∏(1 + g) = Σ_x y_x(U)`, local in `U`, are `StripGas`, at `t₁ = e^{−88}/16`.
  That the dependence is on in-plane loops only is not proved.
* A plaquette gas at fixed hole set `Q` (the faces of the floor expansion above the floor): a set `B` of activated mixed plaquettes reads
  the faces of `Q` in the dual components of the complement of its links that contain no hole; every other face peels.
  Two sets with disjoint links and disjoint read faces factor, exactly, by Fubini. The outer layer averages over `Q`.
* At `U(1)`: nothing above is non-abelian, in agreement with the expectation that this strip does not separate the
  groups. At `β = 0`: `fl = 1`, every face is a hole, `δ_n = 0`, and only the wrapping clusters are left, the
  strong-coupling side.

## What does not follow

* `DA_le_tail` is not proved. What is missing is one inequality (all quantities in `MixCut`):
  `∃ t₁ > 0, ∀ N ≠ 0, ∀ β ≥ 0, ∀ t ∈ [0, t₁], ∃ᶠ w in atTop, ∃ K, (∀ s ∈ [0, t], |mixCut N β s w| ≤ K s³) ∧
  `K t⁴ ≤ 1/500`, with `K` free to depend on `N, β, t, w`. DERIVED: `500 = 2000/4`, the `1/2000` of `tail_closes` over the `1/4` of `cost_le_of_mixCut`. By
  `cost_le_of_mixCut` and `tail_closes` that gives the strip `0 ≤ t ≤ t₁`.
* `plane_forget` is at `t = 0`, for a `G` that leaves the exterior links free. At `t > 0` the factor `∏(1 + g)` reads every link of
  the plane, so the free link of `Exits` does not exist. Peeling needs the product expanded into activated sets, which are signed.
  `Gas.ratio` needs the far product positive. The two cannot be used at the same step. That is the missing step.
* The exact gas at fixed `Q` is not built. Its hard-core form needs that two link-disjoint activated sets do not jointly enclose
  a face unless they share a corner: a discrete Jordan statement on the plane, not in this tree. The outer average over `Q` is a
  tilted Bernoulli field on the faces, with the tilt of the first layer; its uniqueness is not built.
* The rate here is the floor, `δ_n ≈ exp(−e^{−4β} n²)`. It reads an area of order `e^{4β}`, not `A_glue`. The
  rate `e^{−n²/(2ℓ)}` is known only for the rows of `StripWiden.ratio_eq`, not for the exterior of a rectangle.
  By `tail_closes` the rate does not matter for the existence of the strip, only for the size of the seed window.
* The module is 2D. The product over planes of `plane_forget` is not written.
* `CouplingTower.StrongEnd`, `AnisoTorus.AnisoAnalytic`, `MixCutTest.VarGap`, `MixPlane.NoStallOnSegment` stay open.

DERIVED (module-wide): `0`, `1` the two directions, the first point, the units of the product; `2` the dimension and the
least side; `4` the exponent of the cost and the primitive of `s³`. Inherited: `1/1000`, `1/2000` of `StripWidth` and
`DoublingSharp`; `e^{−4β}` of `TwoDVanish.fl`.
-/

namespace MassGap.StripTail

open MeasureTheory Filter Topology MassGap MassGap.TorusDoubling MassGap.TwoDVanish
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)

variable {N n : ℕ}

/-! ## 1. Any rate suffices -/

/-- **A cost at most `1/2000` at infinitely many windows closes the strip at `(β, t)`.** The decoupled defect vanishes
(`TwoDVanish.decoupled_vanishes`), so the seed of `MixAnchor.tendsto_DA_of_seed` is reached at such a window. Inherited:
`1/1000`, `1/2000`. DERIVED: `0` the decoupled end and the limit; `1` the least seed window; `1/1000` the basin of
`MixAnchor.tendsto_DA_of_seed` and `1/2000` its half left to the cost (`StripWidth.strip_of_seed`). -/
theorem tail_closes (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (h : ∃ᶠ w in atTop, |AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w| ≤ 1 / 2000) :
    Tendsto (fun w => AnisoTorus.DA N β t w) atTop (𝓝 0) ∧
      ∃ w, 1 ≤ w ∧ AnisoTorus.DA N β t w ≤ 1 / 1000 ∧
        StripLift.TransferGapAt hN hβ ht (StripLift.seedMass w) w := by
  have h0 := TwoDVanish.decoupled_vanishes hN hβ
  have hev : ∀ᶠ w in atTop, 1 ≤ w ∧ AnisoTorus.DA N β 0 w ≤ 1 / 2000 :=
    (eventually_ge_atTop 1).and (h0.eventually (Iic_mem_nhds (by norm_num)))
  obtain ⟨w, h1, hw, h2⟩ := (h.and_eventually hev).exists
  have hs : AnisoTorus.DA N β t w ≤ 1 / 1000 := by
    have := (abs_le.1 h1).2
    linarith
  exact ⟨MixAnchor.tendsto_DA_of_seed hN hβ ht hw hs, w, hw, hs, StripLift.gap_of_seed hN hβ ht hw hs⟩

/-- **The rate is free**: the cost tends to `0` if and only if it is at most `1/2000` at infinitely many windows.
Inherited: `1/2000`. DERIVED: `0` the limit; `1/2000` the half of the basin `1/1000` left to the cost, as in
`tail_closes`. -/
theorem tail_iff (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    (∃ᶠ w in atTop, |AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w| ≤ 1 / 2000) ↔
      Tendsto (fun w => AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w) atTop (𝓝 0) := by
  constructor
  · intro h
    have := (tail_closes hN hβ ht h).1.sub (TwoDVanish.decoupled_vanishes hN hβ)
    simpa using this
  · intro h
    have h1 : ∀ᶠ w in atTop, |AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w| ≤ 1 / 2000 := by
      have := h.abs
      rw [abs_zero] at this
      exact this.eventually (Iic_mem_nhds (by norm_num))
    exact h1.frequently

/-! ## 2. The cost from the mixed cut -/

/-- A derivative at most `K s³` on `[0, t]` bounds the increment by `K t⁴/4`. DERIVED: `3` the exponent of the
derivative bound; `4 = 3 + 1` its primitive's exponent and denominator; `0` the left end. -/
theorem sub_le_of_deriv_le {f f' : ℝ → ℝ} (hd : ∀ s, HasDerivAt f (f' s) s) {t K : ℝ} (ht : 0 ≤ t)
    (hb : ∀ s ∈ Set.Icc 0 t, f' s ≤ K * s ^ 3) : f t - f 0 ≤ K * t ^ 4 / 4 := by
  have hφ : ∀ s, HasDerivAt (fun x => K * x ^ 4 / 4 - f x) (K * s ^ 3 - f' s) s := by
    intro s
    have h1 : HasDerivAt (fun x : ℝ => K * x ^ 4 / 4) (K * s ^ 3) s := by
      have := ((hasDerivAt_pow 4 s).const_mul K).div_const 4
      refine this.congr_deriv ?_
      norm_num
      ring
    exact h1.sub (hd s)
  have hm : MonotoneOn (fun x => K * x ^ 4 / 4 - f x) (Set.Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · exact fun s _ => (hφ s).continuousAt.continuousWithinAt
    · exact fun s _ => (hφ s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hφ s).deriv]
      linarith [hb s ⟨hs.1.le, hs.2.le⟩]
  have := hm (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  simp only at this
  norm_num at this
  linarith

/-- **The cost is the integral of the mixed cut**: `|mixCut(β, s, w)| ≤ K s³` on `[0, t]` gives
`|DA(β, t, w) − DA(β, 0, w)| ≤ K t⁴/4`. DERIVED: `3`, `4` the power and its primitive; `0` the decoupled end. -/
theorem cost_le_of_mixCut {β t K : ℝ} {w : ℕ} (ht : 0 ≤ t)
    (hK : ∀ s ∈ Set.Icc 0 t, |MixCut.mixCut N β s w| ≤ K * s ^ 3) :
    |AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w| ≤ K * t ^ 4 / 4 := by
  have h1 := sub_le_of_deriv_le (f := fun x => AnisoTorus.DA N β x w) (f' := fun s => MixCut.mixCut N β s w)
    (fun s => MixCut.hasDerivAt_DA_mix β s w) ht fun s hs => (le_abs_self _).trans (hK s hs)
  have h2 := sub_le_of_deriv_le (f := fun x => -AnisoTorus.DA N β x w) (f' := fun s => -MixCut.mixCut N β s w)
    (fun s => (MixCut.hasDerivAt_DA_mix β s w).neg) ht fun s hs => (neg_le_abs _).trans (hK s hs)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ## 3. Holes survive every tilt -/

theorem fl_le_one {β : ℝ} (hβ : 0 ≤ β) : fl β ≤ 1 := by
  unfold fl
  rw [Real.exp_le_one_iff]
  nlinarith

theorem wt_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : SU N) : wt β g ≤ 1 := by
  have h1 := WilsonAction.wilsonDensity_nonneg hN g
  have h2 := WilsonAction.wilsonDensity_nonneg hN g⁻¹
  unfold wt
  rw [Real.exp_le_one_iff]
  nlinarith

theorem wt_nonneg (β : ℝ) (g : SU N) : 0 ≤ wt β g := (Real.exp_pos _).le

/-- **The weight above the floor loses a fixed fraction**: `sw ≤ (1 − fl) wt`. Equivalently, a face is a hole with
probability `fl/wt ≥ fl` given its holonomy. DERIVED: `1` the bound on `wt`. -/
theorem sw_le_hole (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : SU N) : sw β g ≤ (1 - fl β) * wt β g := by
  have h1 := wt_le_one hN hβ g
  have h2 := fl_pos β
  unfold sw
  nlinarith

/-- **The product over a set of faces**: `∏_E sw ≤ (1 − fl)^{|E|} ∏_E wt` on every configuration. DERIVED: `1` as in
`sw_le_hole`. -/
theorem prod_sw_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (E : Finset (TSite 2 n)) (U : TLink 2 n → SU N) :
    ∏ x ∈ E, sw β (face x U) ≤ (1 - fl β) ^ E.card * ∏ x ∈ E, wt β (face x U) := by
  calc ∏ x ∈ E, sw β (face x U) ≤ ∏ x ∈ E, ((1 - fl β) * wt β (face x U)) :=
        Finset.prod_le_prod (fun x _ => sw_nonneg hN hβ _) fun x _ => sw_le_hole hN hβ _
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

/-! ## 4. Peeling a free link in the presence of a function that does not read it -/

/-- The link between `f` and `f + e_i`. DERIVED: `0`, `1` the two directions. -/
def sideLink (i : Fin 2) (f : TSite 2 n) : TLink 2 n :=
  if i = 0 then (1, tshift 0 f) else (0, tshift 1 f)

/-- `G` does not read the link `ℓ`. No numeral. -/
def NoRead (G : (TLink 2 n → SU N) → ℝ) (ℓ : TLink 2 n) : Prop :=
  ∀ (W : TLink 2 n → SU N) (g : SU N), G (Function.update W ℓ g) = G W

/-- **`E` peels past `G`**: every nonempty proper subset of `E` has a face with a neighbour outside the subset, across a
link `G` does not read. No numeral. -/
def Exits (E : Finset (TSite 2 n)) (G : (TLink 2 n → SU N) → ℝ) : Prop :=
  ∀ S, S ⊆ E → S.Nonempty → S ≠ E → ∃ f ∈ S, ∃ i : Fin 2, tshift i f ∉ S ∧ NoRead G (sideLink i f)

/-- The link between `f` and a neighbour outside `S` is free: it integrates the face `f` to its mean and enters no other
face of `S`. DERIVED: `2` the least side. -/
theorem free_link (hn : 2 ≤ n) {s : SU N → ℝ} {S : Finset (TSite 2 n)} {f : TSite 2 n} {i : Fin 2}
    (hi : tshift i f ∉ S) :
    (∀ W : TLink 2 n → SU N, ∫ g, s (face f (Function.update W (sideLink i f) g)) ∂(probHaar (SU N))
        = ∫ g, s g ∂(probHaar (SU N))) ∧
      (∀ x ∈ S.erase f, ∀ (W : TLink 2 n → SU N) g,
        face x (Function.update W (sideLink i f) g) = face x W) := by
  fin_cases i
  · have e : sideLink (0 : Fin 2) f = (1, tshift 0 f) := rfl
    have h0' : tshift 0 f ∉ S := hi
    show (∀ W : TLink 2 n → SU N, ∫ g, s (face f (Function.update W (sideLink (0 : Fin 2) f) g))
        ∂(probHaar (SU N)) = ∫ g, s g ∂(probHaar (SU N))) ∧
      (∀ x ∈ S.erase f, ∀ (W : TLink 2 n → SU N) g,
        face x (Function.update W (sideLink (0 : Fin 2) f) g) = face x W)
    rw [e]
    refine ⟨fun W => ?_, fun x hx W g => ?_⟩
    · simp_rw [face_update_e0 hn f W]
      exact HeatBath.integral_twoSided s _ _
    · have hxf : x ≠ f := Finset.ne_of_mem_erase hx
      have hxS : x ∈ S := Finset.mem_of_mem_erase hx
      exact face_update_other W g pair_ne (pair_ne_of fun h => hxf (tshift_injective 0 h)) pair_ne
        (pair_ne_of fun h => h0' (h ▸ hxS))
  · have e : sideLink (1 : Fin 2) f = (0, tshift 1 f) := rfl
    have h1' : tshift 1 f ∉ S := hi
    show (∀ W : TLink 2 n → SU N, ∫ g, s (face f (Function.update W (sideLink (1 : Fin 2) f) g))
        ∂(probHaar (SU N)) = ∫ g, s g ∂(probHaar (SU N))) ∧
      (∀ x ∈ S.erase f, ∀ (W : TLink 2 n → SU N) g,
        face x (Function.update W (sideLink (1 : Fin 2) f) g) = face x W)
    rw [e]
    refine ⟨fun W => ?_, fun x hx W g => ?_⟩
    · simp_rw [face_update_e1 hn f W]
      have hinv := integral_inv_eq_self
        (fun g => s (W (0, f) * W (1, tshift 0 f) * g * (W (1, f))⁻¹)) (probHaar (SU N))
      exact hinv.trans (HeatBath.integral_twoSided s _ _)
    · have hxf : x ≠ f := Finset.ne_of_mem_erase hx
      have hxS : x ∈ S := Finset.mem_of_mem_erase hx
      exact face_update_other W g (pair_ne_of fun h => h1' (h ▸ hxS)) pair_ne'
        (pair_ne_of fun h => hxf (tshift_injective 1 h)) pair_ne'

/-- **Peeling past `G`**: `∫ G ∏_S s = (∫ s)^{|S|} ∫ G` for `S ⊊ E`, when `E` peels past `G`. DERIVED: `0`, `1` the
range of `s`; `2` the least side. -/
theorem integral_mul_prod_peel (hn : 2 ≤ n) {s : SU N → ℝ} (hs : Continuous s) (h0 : ∀ g, 0 ≤ s g)
    (h1 : ∀ g, s g ≤ 1) {G : (TLink 2 n → SU N) → ℝ} (hG : Continuous G) {E : Finset (TSite 2 n)}
    (hE : Exits E G) (k : ℕ) :
    ∀ S : Finset (TSite 2 n), S.card = k → S ⊆ E → S ≠ E →
      ∫ U, G U * ∏ x ∈ S, s (face x U) ∂(μL n N)
        = (∫ g, s g ∂(probHaar (SU N))) ^ k * ∫ U, G U ∂(μL n N) := by
  induction k with
  | zero =>
    intro S hS _ _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hSE hne
    have hnon : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨f, hf, i, hi, hread⟩ := hE S hSE hnon hne
    have hcard : (S.erase f).card = k := by rw [Finset.card_erase_of_mem hf, hS]; rfl
    have hsub : S.erase f ⊆ E := (Finset.erase_subset _ _).trans hSE
    have hne' : S.erase f ≠ E := fun h =>
      Finset.notMem_erase f S (h ▸ hSE hf)
    have hIH := ih (S.erase f) hcard hsub hne'
    obtain ⟨hcf, hother⟩ := free_link (N := N) (s := s) hn hi
    set c := ∫ g, s g ∂(probHaar (SU N)) with hc
    set ℓ := sideLink i f with hℓ
    have hF : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ S, s (face x U) :=
      hG.mul (continuous_finsetProd _ fun x _ => hs.comp (continuous_face x))
    obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hF
    rw [HeatBath.integral_eq_integral_update (probHaar (SU N)) ℓ _ hF.measurable hC]
    have hin : ∀ W : TLink 2 n → SU N,
        ∫ g, G (Function.update W ℓ g) * ∏ x ∈ S, s (face x (Function.update W ℓ g)) ∂(probHaar (SU N))
          = c * (G W * ∏ x ∈ S.erase f, s (face x W)) := by
      intro W
      have hsplit : ∀ g, G (Function.update W ℓ g) * ∏ x ∈ S, s (face x (Function.update W ℓ g))
          = s (face f (Function.update W ℓ g)) * (G W * ∏ x ∈ S.erase f, s (face x W)) := by
        intro g
        rw [hread W g, ← Finset.mul_prod_erase S _ hf,
          Finset.prod_congr rfl fun x hx => by rw [hother x hx W g]]
        ring
      simp_rw [hsplit]
      rw [integral_mul_const, hcf W]
    simp_rw [hin]
    rw [integral_const_mul, hIH, pow_succ]
    ring

/-! ## 5. The exterior integrates to a constant, up to a relative error -/

/-- **The forgetting identity**: `∫ G ∏_E wt = (b^{|E|} − c^{|E|}) ∫ G + ∫ G ∏_E sw`, when `E` peels past `G`. The floor
expansion over `E`: every proper subset of `E` peels, and only `E` itself keeps a dependence on `G`. DERIVED: `2` the
least side. -/
theorem forget_eq (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) {G : (TLink 2 n → SU N) → ℝ}
    (hG : Continuous G) {E : Finset (TSite 2 n)} (hE : Exits E G) :
    ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N)
      = (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N)
        + ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N) := by
  have hexp : ∀ U : TLink 2 n → SU N, G U * ∏ x ∈ E, wt β (face x U)
      = ∑ t ∈ E.powerset, (G U * ∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ E \ t, fl β := by
    intro U
    have e : ∏ x ∈ E, wt β (face x U) = ∏ x ∈ E, (sw β (face x U) + fl β) :=
      Finset.prod_congr rfl fun x _ => by unfold sw; ring
    rw [e, Finset.prod_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hint : ∀ t : Finset (TSite 2 n), Integrable
      (fun U => (G U * ∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ E \ t, fl β) (μL n N) := fun t =>
    integrable_of_continuous ((hG.mul (continuous_finsetProd _ fun x _ =>
      (continuous_sw β).comp (continuous_face x))).mul continuous_const)
  simp_rw [hexp]
  rw [integral_finset_sum _ fun t _ => hint t]
  simp_rw [integral_mul_const, Finset.prod_const]
  have hconst : bk N β ^ E.card = ∑ t ∈ E.powerset, cm N β ^ t.card * fl β ^ (E \ t).card := by
    unfold bk
    rw [← Finset.prod_const, Finset.prod_add]
    simp only [Finset.prod_const]
  rw [hconst, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self E),
    ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self E)]
  have hrest : ∀ t ∈ E.powerset.erase E,
      (∫ U, G U * ∏ x ∈ t, sw β (face x U) ∂(μL n N)) * fl β ^ (E \ t).card
        = cm N β ^ t.card * fl β ^ (E \ t).card * ∫ U, G U ∂(μL n N) := by
    intro t ht
    have hsub := Finset.mem_powerset.1 (Finset.mem_of_mem_erase ht)
    rw [integral_mul_prod_peel hn (continuous_sw β) (sw_nonneg hN hβ) (sw_le_one hN hβ) hG hE t.card t
      rfl hsub (Finset.ne_of_mem_erase ht)]
    unfold cm
    ring
  rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul, Finset.sdiff_self, Finset.card_empty, pow_zero,
    mul_one, mul_one]
  ring

/-- **The two-sided forgetting**: for `G ≥ 0`, with `m = b^{|E|} − c^{|E|}`, `δ = (1 − fl)^{|E|}`,
`m ∫ G ≤ ∫ G ∏_E wt` and `(1 − δ) ∫ G ∏_E wt ≤ m ∫ G`. The error is relative to the value of `G`, by `prod_sw_le`.
DERIVED: `0` the sign of `G`; `2` the least side. -/
theorem forget_bounds (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) {G : (TLink 2 n → SU N) → ℝ}
    (hG : Continuous G) (hG0 : ∀ U, 0 ≤ G U) {E : Finset (TSite 2 n)} (hE : Exits E G) :
    (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N)
        ≤ ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N) ∧
      (1 - (1 - fl β) ^ E.card) * ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N)
        ≤ (bk N β ^ E.card - cm N β ^ E.card) * ∫ U, G U ∂(μL n N) := by
  have he := forget_eq hN hn hβ hG hE
  have hcw : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ E, wt β (face x U) :=
    hG.mul (continuous_finsetProd _ fun x _ =>
      (Real.continuous_exp.comp (continuous_const.mul
        (WilsonAction.continuous_wilsonDensity.add
          (WilsonAction.continuous_wilsonDensity.comp continuous_inv)))).comp (continuous_face x))
  have hcs : Continuous fun U : TLink 2 n → SU N => G U * ∏ x ∈ E, sw β (face x U) :=
    hG.mul (continuous_finsetProd _ fun x _ => (continuous_sw β).comp (continuous_face x))
  have hX0 : 0 ≤ ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N) :=
    integral_nonneg fun U => mul_nonneg (hG0 U) (Finset.prod_nonneg fun x _ => sw_nonneg hN hβ _)
  have hX1 : ∫ U, G U * ∏ x ∈ E, sw β (face x U) ∂(μL n N)
      ≤ (1 - fl β) ^ E.card * ∫ U, G U * ∏ x ∈ E, wt β (face x U) ∂(μL n N) := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_continuous hcs) ((integrable_of_continuous hcw).const_mul _)
      fun U => ?_
    have := mul_le_mul_of_nonneg_left (prod_sw_le hN hβ E U) (hG0 U)
    show G U * ∏ x ∈ E, sw β (face x U) ≤ (1 - fl β) ^ E.card * (G U * ∏ x ∈ E, wt β (face x U))
    linarith
  constructor <;> nlinarith

/-! ## 6. The exterior of a rectangle peels -/

/-- The faces outside the rectangle `[0, r)²`. No numeral. -/
noncomputable def outS (n r : ℕ) : Finset (TSite 2 n) :=
  Finset.univ.filter fun x => ¬ ∀ i, (x i).val < r

theorem mem_outS {r : ℕ} {x : TSite 2 n} : x ∈ outS n r ↔ ∃ i, r ≤ (x i).val := by
  simp only [outS, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt]

/-- The point with the given coordinates. DERIVED: `2` the dimension. -/
def pt (a b : Fin n) : TSite 2 n := ![a, b]

theorem pt_eta (x : TSite 2 n) : pt (x 0) (x 1) = x := by
  funext j
  fin_cases j <;> rfl

theorem update_pt_one (a b c : Fin n) : Function.update (pt a b) (1 : Fin 2) c = pt a c := by
  funext j
  fin_cases j
  · rfl
  · simp [pt]

theorem update_pt_zero (a b c : Fin n) : Function.update (pt a b) (0 : Fin 2) c = pt c b := by
  funext j
  fin_cases j
  · simp [pt]
  · rfl

/-- A set closed under the forward shift inside `E` contains the whole of any line of `E` it meets. DERIVED: `2` the least
side. -/
theorem line_fill (hn : 2 ≤ n) {S E : Finset (TSite 2 n)}
    (hstep : ∀ x ∈ S, ∀ i, tshift i x ∈ E → tshift i x ∈ S) {x : TSite 2 n} (hx : x ∈ S) {i : Fin 2}
    (hline : ∀ v, Function.update x i v ∈ E) (v : Fin n) : Function.update x i v ∈ S := by
  have hit : ∀ k : ℕ, (tshift i)^[k] x ∈ S := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine hstep _ ih i ?_
      have e : tshift i ((tshift i)^[k] x) = (tshift i)^[k + 1] x :=
        (Function.iterate_succ_apply' _ _ _).symm
      rw [e, tshift_iter]
      exact hline _
  obtain ⟨k, hk⟩ := reach hn (x i) v
  have := hit k
  rwa [tshift_iter, hk] at this

/-- **A nonempty set closed under the forward shifts inside the exterior of a rectangle is the exterior.** The rows and
columns beyond `r` are lines of the exterior, and the last row and column meet them all. DERIVED: `2` the least side; `1`
the last coordinate. -/
theorem fill_outS (hn : 2 ≤ n) {r : ℕ} (hr : r < n) {S : Finset (TSite 2 n)} (hS : S ⊆ outS n r)
    (hne : S.Nonempty) (hstep : ∀ x ∈ S, ∀ i, tshift i x ∈ outS n r → tshift i x ∈ S) : S = outS n r := by
  obtain ⟨f, hf⟩ := hne
  let m : Fin n := ⟨n - 1, by omega⟩
  have hm : r ≤ m.val := by show r ≤ n - 1; omega
  have hA : ∀ a b c, pt a b ∈ S → r ≤ a.val → pt a c ∈ S := by
    intro a b c h ha
    have := line_fill hn hstep h (i := 1) (fun v => by
      rw [update_pt_one]
      exact mem_outS.2 ⟨0, ha⟩) c
    rwa [update_pt_one] at this
  have hB : ∀ a b c, pt a b ∈ S → r ≤ b.val → pt c b ∈ S := by
    intro a b c h hb
    have := line_fill hn hstep h (i := 0) (fun v => by
      rw [update_pt_zero]
      exact mem_outS.2 ⟨1, hb⟩) c
    rwa [update_pt_zero] at this
  have hff : pt (f 0) (f 1) ∈ S := by rwa [pt_eta]
  have hmm : pt m m ∈ S := by
    obtain ⟨i, hi⟩ := mem_outS.1 (hS hf)
    fin_cases i
    · exact hB _ _ _ (hA _ _ m hff hi) hm
    · exact hA _ _ _ (hB _ _ m hff hi) hm
  refine Finset.Subset.antisymm hS fun y hy => ?_
  rw [← pt_eta y]
  obtain ⟨i, hi⟩ := mem_outS.1 hy
  fin_cases i
  · exact hA _ _ _ (hB _ _ (y 0) hmm hm) hi
  · exact hB _ _ _ (hA _ _ (y 1) hmm hm) hi

/-- **The exterior of a rectangle peels past `G`** when `G` reads no link between two exterior faces. DERIVED: `2` the least
side. -/
theorem exits_outS (hn : 2 ≤ n) {r : ℕ} (hr : r < n) {G : (TLink 2 n → SU N) → ℝ}
    (hG : ∀ f i, f ∈ outS n r → tshift i f ∈ outS n r → NoRead G (sideLink i f)) :
    Exits (outS n r) G := by
  intro S hS hne hSE
  by_contra hcon
  push Not at hcon
  refine hSE (fill_outS hn hr hS hne fun x hx i hi => ?_)
  by_contra hc
  exact hcon x hx i hc (hG x i (hS hx) hi)

/-! ## 7. The rectangle in its own coordinates -/

/-- The sites of the rectangle, corners included. DERIVED: `1` the far corner. -/
abbrev BS (r : ℕ) : Type := Fin 2 → Fin (r + 1)

/-- The links of the rectangle: a link leaves its site inside the rectangle. DERIVED: `1` as in `BS`. -/
abbrev BL (r : ℕ) : Type := {l : Fin 2 × BS r // (l.2 l.1).val < r}

/-- The product Haar measure on the links of the rectangle. It does not know `n`. No numeral. -/
noncomputable abbrev μB (r N : ℕ) : Measure (BL r → SU N) := Measure.pi fun _ : BL r => probHaar (SU N)

variable {r : ℕ}

/-- The site of the torus. DERIVED: `1` as in `BS`. -/
def eS (hr : r + 1 ≤ n) (v : BS r) : TSite 2 n := fun i => Fin.castLE hr (v i)

/-- The link of the torus. DERIVED: `1` as in `BS`. -/
def eL (hr : r + 1 ≤ n) (l : BL r) : TLink 2 n := (l.1.1, eS hr l.1.2)

theorem eS_injective (hr : r + 1 ≤ n) : Function.Injective (eS (n := n) hr) := by
  intro v w h
  funext i
  exact Fin.castLE_injective hr (congrFun h i)

theorem eL_injective (hr : r + 1 ≤ n) : Function.Injective (eL (n := n) hr) := by
  intro l l' h
  have h0 : (l.1.1, eS hr l.1.2) = (l'.1.1, eS hr l'.1.2) := h
  obtain ⟨h1, h3⟩ := Prod.mk.inj h0
  exact Subtype.ext (Prod.ext h1 (eS_injective hr h3))

/-- The restriction of a configuration to the rectangle. No numeral. -/
def res (hr : r + 1 ≤ n) (U : TLink 2 n → SU N) : BL r → SU N := fun l => U (eL hr l)

theorem continuous_res (hr : r + 1 ≤ n) : Continuous (res (N := N) hr) :=
  continuous_pi fun l => continuous_apply _

theorem measurable_res (hr : r + 1 ≤ n) : Measurable (res (N := N) hr) :=
  measurable_pi_lambda _ fun l => measurable_pi_apply _

/-- **The restriction carries product Haar to product Haar.** DERIVED: `1` the mass of a probability measure. -/
theorem map_res (hr : r + 1 ≤ n) : (μL n N).map (res hr) = μB r N := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  classical
  rw [Measure.map_apply (measurable_res hr) (MeasurableSet.univ_pi hs)]
  set s' : TLink 2 n → Set (SU N) := fun ℓ =>
    if h : ∃ l, eL hr l = ℓ then s h.choose else Set.univ with hs'
  have hval : ∀ l, s' (eL hr l) = s l := by
    intro l
    have h : ∃ l', eL hr l' = eL hr l := ⟨l, rfl⟩
    simp only [hs', dif_pos h]
    rw [eL_injective hr h.choose_spec]
  have hms' : ∀ ℓ, MeasurableSet (s' ℓ) := by
    intro ℓ
    simp only [hs']
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  have hpre : res hr ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h ℓ
      by_cases hℓ : ∃ l, eL hr l = ℓ
      · obtain ⟨l, rfl⟩ := hℓ
        rw [hval]
        exact h l
      · simp only [hs', dif_neg hℓ, Set.mem_univ]
    · intro h l
      have := h (eL hr l)
      rwa [hval] at this
  rw [hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective (eL hr) (eL_injective hr) (fun l => probHaar (SU N) (s l))
    (fun ℓ => probHaar (SU N) (s' ℓ)) (fun ℓ hℓ => ?_) fun l => ?_
  · have h : ¬ ∃ l, eL hr l = ℓ := fun ⟨l, hl⟩ => hℓ ⟨l, hl⟩
    simp only [hs', dif_neg h, measure_univ]
  · rw [hval]

theorem integral_res (hr : r + 1 ≤ n) {H : (BL r → SU N) → ℝ} (hH : Continuous H) :
    ∫ U, H (res hr U) ∂(μL n N) = ∫ V, H V ∂(μB r N) := by
  rw [← map_res hr, integral_map (measurable_res hr).aemeasurable hH.aestronglyMeasurable]

/-- The site `y` of the rectangle. DERIVED: `1` the far corner, unused. -/
def cs (y : Fin 2 → Fin r) : BS r := fun i => (y i).castSucc

/-- The site `y + e_i` of the rectangle. DERIVED: `1` the step. -/
def bs (i : Fin 2) (y : Fin 2 → Fin r) : BS r := Function.update (cs y) i (y i).succ

theorem bs_ne {i j : Fin 2} (h : j ≠ i) (y : Fin 2 → Fin r) : (bs i y j).val = (y j).val := by
  simp [bs, cs, Function.update_of_ne h]

/-- The four links of the face `y`, in the rectangle. DERIVED: `0`, `1` the two directions. -/
def l0a (y : Fin 2 → Fin r) : BL r := ⟨(0, cs y), (y 0).isLt⟩
/-- See `l0a`. -/
def l1b (y : Fin 2 → Fin r) : BL r := ⟨(1, bs 0 y), by
  show (bs 0 y 1).val < r
  rw [bs_ne (by decide)]
  exact (y 1).isLt⟩
/-- See `l0a`. -/
def l0c (y : Fin 2 → Fin r) : BL r := ⟨(0, bs 1 y), by
  show (bs 1 y 0).val < r
  rw [bs_ne (by decide)]
  exact (y 0).isLt⟩
/-- See `l0a`. -/
def l1d (y : Fin 2 → Fin r) : BL r := ⟨(1, cs y), (y 1).isLt⟩

/-- The holonomy of the face `y` in the rectangle. No numeral. -/
def bface (y : Fin 2 → Fin r) (V : BL r → SU N) : SU N :=
  V (l0a y) * V (l1b y) * (V (l0c y))⁻¹ * (V (l1d y))⁻¹

/-- **The weight of the rectangle.** No numeral. -/
noncomputable def bwt (β : ℝ) (V : BL r → SU N) : ℝ := ∏ y : Fin 2 → Fin r, wt β (bface y V)

theorem continuous_wt (β : ℝ) : Continuous (wt (N := N) β) := by
  unfold wt
  exact Real.continuous_exp.comp (continuous_const.mul (WilsonAction.continuous_wilsonDensity.add
    (WilsonAction.continuous_wilsonDensity.comp continuous_inv)))

theorem continuous_bwt (β : ℝ) : Continuous (bwt (N := N) (r := r) β) := by
  unfold bwt bface
  refine continuous_finsetProd _ fun y _ => (continuous_wt β).comp ?_
  have e : ∀ l : BL r, Continuous fun V : BL r → SU N => V l := fun l => continuous_apply l
  exact ((e _ |>.mul (e _)).mul (e _).inv).mul (e _).inv

theorem bwt_nonneg (β : ℝ) (V : BL r → SU N) : 0 ≤ bwt β V :=
  Finset.prod_nonneg fun _ _ => wt_nonneg _ _

/-- The corner `y` on the torus. DERIVED: `1` as in `BS`. -/
def cor (hr : r + 1 ≤ n) (y : Fin 2 → Fin r) : TSite 2 n := eS hr (cs y)

theorem cor_injective (hr : r + 1 ≤ n) : Function.Injective (cor (n := n) hr) := by
  intro y y' h
  funext i
  have := congrFun (eS_injective hr h) i
  exact Fin.castSucc_injective _ this

/-- **The rectangle's shift is the torus shift**, away from the wrap. DERIVED: `1` as in `BS`. -/
theorem tshift_cor (hr : r + 1 ≤ n) (i : Fin 2) (y : Fin 2 → Fin r) :
    tshift i (cor hr y) = eS hr (bs i y) := by
  funext j
  by_cases hj : j = i
  · subst hj
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hv : (y j).val + 1 < m + 1 := by have := (y j).isLt; omega
    refine Fin.ext ?_
    simp only [tshift, Function.update_self, eS, bs, cor, cs]
    have hne : Fin.castLE hr (y j).castSucc ≠ Fin.last m := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [coe_finRotate_of_ne_last hne]
    simp
  · simp [tshift, Function.update_of_ne hj, cor, eS, bs, cs]

theorem face_cor (hr : r + 1 ≤ n) (y : Fin 2 → Fin r) (U : TLink 2 n → SU N) :
    face (cor hr y) U = bface y (res hr U) := by
  unfold face bface
  rw [tshift_cor, tshift_cor]
  rfl

theorem filter_eq_image (hr : r + 1 ≤ n) :
    (Finset.univ.filter fun x : TSite 2 n => ∀ i, (x i).val < r)
      = Finset.univ.image (cor (n := n) hr) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    refine ⟨fun i => ⟨(x i).val, h i⟩, ?_⟩
    funext i
    exact Fin.ext rfl
  · rintro ⟨y, rfl⟩ i
    exact (y i).isLt

/-- **The torus weight splits at the rectangle.** No numeral. -/
theorem prod_split (hr : r + 1 ≤ n) (β : ℝ) (U : TLink 2 n → SU N) :
    ∏ x, wt β (face x U) = bwt β (res hr U) * ∏ x ∈ outS n r, wt β (face x U) := by
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun x : TSite 2 n => ∀ i, (x i).val < r) (fun x => wt β (face x U))
  have h1 : ∏ x ∈ Finset.univ.filter (fun x : TSite 2 n => ∀ i, (x i).val < r), wt β (face x U)
      = bwt β (res hr U) := by
    rw [filter_eq_image hr, Finset.prod_image fun a _ b _ hab => cor_injective hr hab]
    unfold bwt
    exact Finset.prod_congr rfl fun y _ => by rw [face_cor]
  rw [← h, h1]
  exact congrArg _ (Finset.prod_congr (by ext x; simp [outS]) fun _ _ => rfl)

theorem card_filter (hr : r + 1 ≤ n) :
    (Finset.univ.filter fun x : TSite 2 n => ∀ i, (x i).val < r).card = r ^ 2 := by
  rw [filter_eq_image hr, Finset.card_image_of_injective _ (cor_injective hr)]
  simp

/-- **The exterior has `n² − r²` faces.** DERIVED: `2` the dimension. -/
theorem card_outS (hr : r + 1 ≤ n) : (outS n r).card = n ^ 2 - r ^ 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (TSite 2 n)))
    (fun x : TSite 2 n => ∀ i, (x i).val < r)
  rw [card_filter hr, Finset.card_univ, card_site] at h
  unfold outS
  omega

theorem outS_card_pos (hr : r + 1 ≤ n) : 0 < (outS n r).card := by
  rw [card_outS hr]
  have : r ^ 2 < n ^ 2 := Nat.pow_lt_pow_left (by omega) two_ne_zero
  omega

/-- The coordinate facts behind `link_not_box`. DERIVED: `0` the wrap of the rotation; `1` the step. -/
theorem rot_ne {a : Fin n} (hr : r + 1 ≤ n) (h0 : r ≠ 0) (ha : r ≤ a.val) :
    (finRotate n a).val ≠ r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coe_finRotate]
  split_ifs with h <;> omega

/-- A link read by the rectangle has a rectangle face on one side. DERIVED: `0`, `1` the two directions. -/
theorem side_aux (hr : r + 1 ≤ n) {i j : Fin 2} (hj : j ≠ i) {f : TSite 2 n} {v : BS r}
    (hv : tshift i f = eS hr v) (hvj : (v j).val < r) (hf : f ∈ outS n r)
    (hf' : tshift i f ∈ outS n r) : False := by
  have hall : ∀ k : Fin 2, k = i ∨ k = j := by
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  have hcj : (f j).val = (v j).val := by
    have := congrFun hv j
    simp only [tshift, Function.update_of_ne hj] at this
    rw [this]
    rfl
  have hci : (finRotate n (f i)).val = (v i).val := by
    have := congrFun hv i
    simp only [tshift, Function.update_self] at this
    rw [this]
    rfl
  obtain ⟨k, hk⟩ := mem_outS.1 hf'
  rcases hall k with rfl | rfl
  · rw [hv] at hk
    have hk' : r ≤ (v k).val := hk
    have hvr : (v k).val = r := by have := (v k).isLt; omega
    obtain ⟨k', hk''⟩ := mem_outS.1 hf
    rcases hall k' with rfl | rfl
    · exact rot_ne hr (by omega) hk'' (hci.trans hvr)
    · omega
  · have hk' : r ≤ (tshift i f k).val := hk
    rw [hv] at hk'
    have hk2 : r ≤ (v k).val := hk'
    omega

theorem link_not_box (hr : r + 1 ≤ n) {f : TSite 2 n} {i : Fin 2} (hf : f ∈ outS n r)
    (hf' : tshift i f ∈ outS n r) (l : BL r) : eL hr l ≠ sideLink i f := by
  intro h
  fin_cases i
  · have h1 : eL hr l = (1, tshift 0 f) := h
    have h2 : l.1.1 = 1 := congrArg Prod.fst h1
    have h3 : tshift 0 f = eS hr l.1.2 := (congrArg Prod.snd h1).symm
    have h4 : (l.1.2 1).val < r := by have := l.2; rwa [h2] at this
    exact side_aux hr (i := 0) (j := 1) (by decide) h3 h4 hf hf'
  · have h1 : eL hr l = (0, tshift 1 f) := h
    have h2 : l.1.1 = 0 := congrArg Prod.fst h1
    have h3 : tshift 1 f = eS hr l.1.2 := (congrArg Prod.snd h1).symm
    have h4 : (l.1.2 0).val < r := by have := l.2; rwa [h2] at this
    exact side_aux hr (i := 1) (j := 0) (by decide) h3 h4 hf hf'

/-- **Every function of the rectangle's links leaves the exterior free.** DERIVED: `2` the least side. -/
theorem exits_res (hn : 2 ≤ n) (hr : r + 1 ≤ n) (H : (BL r → SU N) → ℝ) :
    Exits (outS n r) (fun U => H (res hr U)) := by
  refine exits_outS hn (by omega) fun f i hf hf' W g => ?_
  have e : res hr (Function.update W (sideLink i f) g) = res hr W := by
    funext l
    exact Function.update_of_ne (link_not_box hr hf hf' l) _ _
  show H (res hr _) = H (res hr W)
  rw [e]

/-! ## 8. The plane forgets its torus -/

/-- The unnormalized torus reading of `G`. No numeral. -/
noncomputable def planeNum (n : ℕ) (hr : r + 1 ≤ n) (β : ℝ) (G : (BL r → SU N) → ℝ) : ℝ :=
  ∫ U, G (res hr U) * ∏ x, wt β (face x U) ∂(μL n N)

/-- The unnormalized reading of `G` on the free rectangle. No numeral. -/
noncomputable def boxNum (β : ℝ) (G : (BL r → SU N) → ℝ) : ℝ := ∫ V, G V * bwt β V ∂(μB r N)

/-- **The torus against the free rectangle**, for `G ≥ 0` continuous: `m boxNum ≤ planeNum`, `(1 − δ) planeNum ≤ m boxNum`,
with `m = b^{n² − r²} − c^{n² − r²}` and `δ = (1 − fl)^{n² − r²}`. DERIVED: `2` the least side and the dimension. -/
theorem plane_bounds (hN : N ≠ 0) (hn : 2 ≤ n) (hr : r + 1 ≤ n) {β : ℝ} (hβ : 0 ≤ β)
    {G : (BL r → SU N) → ℝ} (hG : Continuous G) (hG0 : ∀ V, 0 ≤ G V) :
    (bk N β ^ (n ^ 2 - r ^ 2) - cm N β ^ (n ^ 2 - r ^ 2)) * boxNum β G ≤ planeNum n hr β G ∧
      (1 - (1 - fl β) ^ (n ^ 2 - r ^ 2)) * planeNum n hr β G
        ≤ (bk N β ^ (n ^ 2 - r ^ 2) - cm N β ^ (n ^ 2 - r ^ 2)) * boxNum β G := by
  have hH : Continuous fun V : BL r → SU N => G V * bwt β V := hG.mul (continuous_bwt β)
  have hcH : Continuous fun U : TLink 2 n → SU N => G (res hr U) * bwt β (res hr U) :=
    hH.comp (continuous_res hr)
  have hb := forget_bounds (N := N) hN hn hβ hcH
    (fun U => mul_nonneg (hG0 _) (bwt_nonneg _ _)) (exits_res hn hr fun V => G V * bwt β V)
  have e : ∫ U, G (res hr U) * bwt β (res hr U) * ∏ x ∈ outS n r, wt β (face x U) ∂(μL n N)
      = planeNum n hr β G := by
    unfold planeNum
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp only
    rw [prod_split hr β U]
    ring
  rw [e, integral_res hr hH, card_outS hr] at hb
  exact hb

/-- The torus mean of `G`. No numeral. -/
noncomputable def planeMean (n : ℕ) (hr : r + 1 ≤ n) (β : ℝ) (G : (BL r → SU N) → ℝ) : ℝ :=
  planeNum n hr β G / planeNum n hr β (N := N) (fun _ => 1)

/-- The mean of `G` on the free rectangle. It does not know `n`. No numeral. -/
noncomputable def boxMean (β : ℝ) (G : (BL r → SU N) → ℝ) : ℝ :=
  boxNum β G / boxNum (N := N) (r := r) β (fun _ => 1)

/-- The relative error of the side `n`. DERIVED: `1` the unit; `2` the dimension. -/
noncomputable def delt (β : ℝ) (n r : ℕ) : ℝ := (1 - fl β) ^ (n ^ 2 - r ^ 2)

theorem delt_nonneg {β : ℝ} (hβ : 0 ≤ β) (n r : ℕ) : 0 ≤ delt β n r :=
  pow_nonneg (by linarith [fl_le_one hβ]) _

theorem delt_lt_one {β : ℝ} (hβ : 0 ≤ β) (hr : r + 1 ≤ n) : delt β n r < 1 := by
  have h0 : n ^ 2 - r ^ 2 ≠ 0 := by
    have := outS_card_pos (n := n) hr
    rw [card_outS hr] at this
    omega
  exact pow_lt_one₀ (by linarith [fl_le_one hβ]) (by linarith [fl_pos β]) h0

/-- `δ_n → 0`. DERIVED: `0` the limit. -/
theorem tendsto_delt {β : ℝ} (hβ : 0 ≤ β) (r : ℕ) : Tendsto (fun n => delt β n r) atTop (𝓝 0) := by
  have h1 : (1 - fl β) < 1 := by linarith [fl_pos β]
  have h0 : 0 ≤ 1 - fl β := by linarith [fl_le_one hβ]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have he : Tendsto (fun n : ℕ => n ^ 2 - r ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.sub_le_sub_right (Nat.le_self_pow two_ne_zero n) _)
      (tendsto_sub_atTop_nat (r ^ 2))
  exact hp.comp he

/-- The torus mass is positive. DERIVED: `2` the least side. -/
theorem planeNum_one_pos (hN : N ≠ 0) (hn : 2 ≤ n) (hr : r + 1 ≤ n) {β : ℝ} (hβ : 0 ≤ β) :
    0 < planeNum n hr β (N := N) (fun _ => 1) := by
  have h : planeNum n hr β (N := N) (fun _ => 1) = ZT (SU N) 2 wilsonDensity β n := by
    unfold planeNum ZT LatticeGauge.System.partition LatticeGauge.System.vol
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    show 1 * ∏ x, wt β (face x U) = _
    rw [one_mul, boltz_eq hN β U]
  rw [h]
  exact ZT_pos hN hn hβ

/-- **The plane forgets its torus**: for `G ≥ 0` continuous on the links of the rectangle,
`(1 − δ_n) ⟨G⟩_box ≤ ⟨G⟩_n ≤ ⟨G⟩_box/(1 − δ_n)`, `δ_n = (1 − e^{−4β})^{n² − r²}`. The error is relative to the value of
`G`. DERIVED: `2` the least side and the dimension; `1` the unit of the ratio. -/
theorem plane_forget (hN : N ≠ 0) (hn : 2 ≤ n) (hr : r + 1 ≤ n) {β : ℝ} (hβ : 0 ≤ β)
    {G : (BL r → SU N) → ℝ} (hG : Continuous G) (hG0 : ∀ V, 0 ≤ G V) :
    (1 - delt β n r) * boxMean β G ≤ planeMean n hr β G ∧
      planeMean n hr β G ≤ boxMean β G / (1 - delt β n r) := by
  obtain ⟨hG1, hG2⟩ := plane_bounds hN hn hr hβ hG hG0
  obtain ⟨h1, h2⟩ := plane_bounds (N := N) hN hn hr hβ (G := fun _ => 1) continuous_const
    (fun _ => zero_le_one)
  have hZ := planeNum_one_pos (N := N) hN hn hr hβ
  have hd := delt_lt_one hβ hr
  have hd0 : 0 < 1 - delt β n r := by linarith
  set e := n ^ 2 - r ^ 2 with he
  have he0 : e ≠ 0 := by
    have := outS_card_pos (n := n) hr
    rw [card_outS hr] at this
    omega
  have hm : 0 < bk N β ^ e - cm N β ^ e := by
    have hlt : cm N β ^ e < bk N β ^ e := by
      unfold bk
      exact pow_lt_pow_left₀ (by linarith [fl_pos β]) (cm_nonneg hN hβ) he0
    linarith
  set m := bk N β ^ e - cm N β ^ e with hmdef
  set Z := planeNum n hr β (N := N) (fun _ => 1) with hZdef
  set A := planeNum n hr β G with hA
  set B := boxNum β G with hB
  set B1 := boxNum (N := N) (r := r) β (fun _ => 1) with hB1
  have hd' : (1 - fl β) ^ e = delt β n r := rfl
  rw [hd'] at hG2 h2
  have hB1pos : 0 < B1 := by
    by_contra hc
    have : m * B1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.1 hc)
    have := mul_pos hd0 hZ
    linarith
  unfold planeMean boxMean
  rw [← hA, ← hZdef, ← hB, ← hB1]
  have hB0 : 0 ≤ B := integral_nonneg fun V => mul_nonneg (hG0 _) (bwt_nonneg _ _)
  have hk1 : (1 - delt β n r) * Z * (m * B) ≤ m * B1 * A :=
    mul_le_mul h2 hG1 (by positivity) (by positivity)
  have hk2 : (1 - delt β n r) * A * (m * B1) ≤ m * B * Z :=
    mul_le_mul hG2 h1 (by positivity) (by positivity)
  constructor
  · rw [mul_div_assoc', div_le_div_iff₀ hB1pos hZ]
    have : m * ((1 - delt β n r) * B * Z) ≤ m * (A * B1) := by
      calc m * ((1 - delt β n r) * B * Z) = (1 - delt β n r) * Z * (m * B) := by ring
        _ ≤ m * B1 * A := hk1
        _ = m * (A * B1) := by ring
    exact le_of_mul_le_mul_left this hm
  · rw [div_div, div_le_div_iff₀ hZ (by positivity)]
    have : m * (A * (B1 * (1 - delt β n r))) ≤ m * (B * Z) := by
      calc m * (A * (B1 * (1 - delt β n r))) = (1 - delt β n r) * A * (m * B1) := by ring
        _ ≤ m * B * Z := hk2
        _ = m * (B * Z) := by ring
    exact le_of_mul_le_mul_left this hm

/-- **Two torus sides agree on the rectangle**: `(1 − δ_n)(1 − δ_{n'}) ⟨G⟩_{n'} ≤ ⟨G⟩_n`. DERIVED: `1` the unit of the
ratio; `2` the least side. -/
theorem plane_compare (hN : N ≠ 0) {n' : ℕ} (hn : 2 ≤ n) (hn' : 2 ≤ n') (hr : r + 1 ≤ n) (hr' : r + 1 ≤ n')
    {β : ℝ} (hβ : 0 ≤ β) {G : (BL r → SU N) → ℝ} (hG : Continuous G) (hG0 : ∀ V, 0 ≤ G V) :
    (1 - delt β n r) * (1 - delt β n' r) * planeMean n' hr' β G ≤ planeMean n hr β G := by
  obtain ⟨h1, -⟩ := plane_forget hN hn hr hβ hG hG0
  obtain ⟨-, h2⟩ := plane_forget hN hn' hr' hβ hG hG0
  have hd := delt_lt_one (n := n) hβ hr
  have hd' := delt_lt_one (n := n') hβ hr'
  have hp : 0 < 1 - delt β n' r := by linarith
  rw [le_div_iff₀ hp] at h2
  have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - delt β n r by linarith)
  nlinarith

end MassGap.StripTail

#print axioms MassGap.StripTail.tail_closes
#print axioms MassGap.StripTail.tail_iff
#print axioms MassGap.StripTail.cost_le_of_mixCut
#print axioms MassGap.StripTail.sw_le_hole
#print axioms MassGap.StripTail.prod_sw_le
#print axioms MassGap.StripTail.free_link
#print axioms MassGap.StripTail.integral_mul_prod_peel
#print axioms MassGap.StripTail.forget_eq
#print axioms MassGap.StripTail.forget_bounds
#print axioms MassGap.StripTail.fill_outS
#print axioms MassGap.StripTail.exits_outS
#print axioms MassGap.StripTail.map_res
#print axioms MassGap.StripTail.prod_split
#print axioms MassGap.StripTail.card_outS
#print axioms MassGap.StripTail.exits_res
#print axioms MassGap.StripTail.plane_bounds
#print axioms MassGap.StripTail.tendsto_delt
#print axioms MassGap.StripTail.plane_forget
#print axioms MassGap.StripTail.plane_compare
