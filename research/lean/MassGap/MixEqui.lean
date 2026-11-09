import Mathlib
import MassGap.MixCutTest

/-!
# MassGap.MixEqui — one-sided equicontinuity of the window defect along the segment

On the vertical segment above `β`, write `D(t, w) = AnisoTorus.DA N β t w`. The proof of `MixCut.vanish_of_cut_le`
reads `MixCut.MixCutBound N β` only through one consequence: the family `{t ↦ D(t, w)}_{w ≥ 1}` is one-sided
equicontinuous on `[0, β]`, uniformly in the window. This module names that consequence, `MixEquiUp N β`, and shows
that under `N ≠ 0`, `β ≥ 0` and `LayerSplit.TwoDCharacter N β` (whose consumed conclusion `TwoDVanish` proves) it is equivalent to
`MixPlane.NoStallOnSegment N β`. It also computes the mixed variance exactly at the decoupled end. Declarations are in `MassGap.MixEqui`.

## 1. The input and its source (proved)

* `MixEquiUp N β`: for every `ε > 0` some `δ > 0` with `D(t, w) ≤ D(s, w) + ε` whenever `w ≥ 1`,
  `0 ≤ s ≤ t ≤ β` and `t − s < δ`.
* `mixEquiUp_of_mixCutBound`: `MixCutBound N β ⇒ MixEquiUp N β`, with `δ = ε/(|M| + 1)`, by the mean value theorem
  on `MixCut.hasDerivAt_DA_mix`.
* `mixEquiUp_of_varGap`: `MixCutTest.VarGap N β ⇒ MixEquiUp N β`, through `MixCutTest.mixCutBound_of_varGap`.

## 2. The first stall (proved)

`noStallOnSegment_of_mixEquiUp`: under `TwoDCharacter N β` (conclusion proved in `TwoDVanish`), `MixEquiUp N β ⇒ NoStallOnSegment N β`. At a
first stall `t*` (`MixPlane.segment_first_stall`), take `ε = 1/2000` (half the seed), its `δ`, and
`s' = max 0 (t* − δ/2)`. The segment vanishes at `s'`, so some window `w ≥ 1` reads `D(s', w) < 1/2000`; then
`D(t*, w) < 1/1000`, a seed, so `t*` vanishes (`MixPlane.mem_vanishSet_iff_seed_lt`): contradiction.
`strongEnd_of_mixEquiUp`: frequently in `β`, `TwoDCharacter ∧ MixEquiUp` gives `CouplingTower.StrongEnd N`.

## 3. The converse (proved): `MixEquiUp` is a restatement

`mixEquiUp_of_noStallOnSegment`: `NoStallOnSegment N β ⇒ MixEquiUp N β` (no `TwoDCharacter`). Every point of
`[0, β]` has a seed window; the seed sets `{t | D(t, c) < 1/1000}` are open (`MixAnchor.continuous_DA`), and their
unions over `c ≤ C` increase with `C`, so one `C` covers the compact segment (`IsCompact.elim_directed_cover`).
`MixAnchor.DA_decay` from that seed then gives `D(t, w) ≤ 4^{−i}/1000` for every `t ∈ [0, β]` and `w ≥ C + i`:
the convergence `D(·, w) → 0` is uniform on the segment. For `w ≥ C + i` with `4^{−i} < ε` the one-sided bound
follows from `D(s, w) ≥ 0` (`MixAnchor.DA_nonneg`); for the finitely many windows below, from the uniform continuity
of `t ↦ (D(t, w))_{w < C + i}` on the compact segment (Heine–Cantor).

`mixEquiUp_iff_noStall`: under `N ≠ 0`, `β ≥ 0` and the cited `TwoDCharacter N β`,
`MixEquiUp N β ↔ NoStallOnSegment N β`. So `MixEquiUp` is the sharpest real-variable form of the segment
statement, and it is exactly that statement: a restatement, not a discharge. `MixCutBound` and `VarGap` are its
Lipschitz strengthenings.

## 4. The decoupled variance (proved)

At `t = 0` the weight reads only `S_in`, and the layer rotation `MixCut.gT` at one site `z` (links of directions
`0, 1` only) leaves `S_in` and every plaquette not cornered at `z` unchanged (`hol_gT_off`). For a mixed plaquette
`((i, j), y)` with `i ∈ {0, 1}`, `j ∈ {2, 3}`, the rotation at the base translates the holonomy
(`MixCut.hol_gT_mixA`); at the corners `y + j` and `y + i` it right-translates the holonomy read from that corner
(`psiJ_gT`, `psiI_gT`), whose density is the same (`plaq_eq_psiJ`, `plaq_eq_psiI`, conjugation).

* `base_sep`: on extent `n ≥ 3`, plaquettes based at `y ≠ y'` have `y'` not a corner of the first or `y` not a
  corner of the second (two steps never return, `finRotate2_ne`). A common base with different second directions
  is separated at `y + j`; with the same second direction, at `y + i`.
* `integral_pair_ne`: distinct such plaquettes give `∫ φ_p φ_{p'} e^{−β S_in} = ⟨φ⟩_Haar² Z`;
  `integral_diag`: `∫ φ_p² e^{−β S_in} = ⟨φ²⟩_Haar Z` (`integral_avg_gen`, the averaging lemma for any continuous
  function of the holonomy).
* The reverse orientation `((j, i), y)` has the inverse holonomy and the same density (`plaq_swap`);
  `integral_pair` reads every mixed pair through the normal orientation `onf`: `⟨φ²⟩` when the two are one
  plaquette up to orientation, `⟨φ⟩²` otherwise. `sum_pair_weight`: each mixed plaquette has exactly two such
  partners, itself and its reverse.
* `mixSq_zero`, `varMix_zero`: `Var_n(S_mix)(β, 0) = 16 n⁴ Var_Haar(φ)` for `n ≥ 3`, `Var_Haar(φ) = haarVar N`.
* `varGap_zero`: `16 Var_n − Var_{2n} = 0` at `t = 0` for every window `w ≥ 2`;
  `hasDerivAt_mixCut_zero`: `∂_t mixCut = 0` at `t = 0` there.

DERIVED (module-wide): `1/2000 = (1/1000)/2` the half seed split between the window read and the equicontinuity
increment; `2` the halving of `δ`; `4` the contraction of the basin (`1/4 = 250 · 1/1000`, inherited through
`MixAnchor.DA_contracts`); `1` the least window and the bound `1/4 < 1`; `0` the axis, the lower ends and the floor
of `D`; `3` the least extent on which two steps move (`2^w ≥ 3` at `w ≥ 2`); `8` the mixed ordered
orientations per site; `16 = 2 · 8` with `2` the two orientations of one plaquette, and `16 = 2⁴` the copies; `4`
the dimension; `2` the square and the doubling. Inherited: `1/1000` the seed of `DoublingSharp` (through `MixPlane`, `MixAnchor`). Cited:
`LayerSplit.TwoDCharacter N β`.

## What does not follow

`MixEquiUp N β` is not proved at any `β > 0`. By `mixEquiUp_iff_noStall` it is equivalent to
`NoStallOnSegment N β` under the cited anchor, so `noStallOnSegment_of_mixEquiUp` and `strongEnd_of_mixEquiUp`
discharge no hypothesis of the bridge: they restate it. Nothing here bounds `D`, `mixCut` or the mixed variances at
any `t > 0`. The variance identity holds at the single point `t = 0` and on extent `n ≥ 3`; the window `w = 1`
(`n = 2`, where the four bases of one plane square share all corners) is not computed. `varGap_zero` gives
`VarGap`'s left side `= 0` at `t = 0` only; it is not a bound on `[0, t₁]` for any `t₁ > 0`, and it does not give
`MixCutTest.VarGap N β`, `MixCut.MixCutBound N β` or `MixEquiUp N β` at any `β > 0`.
`LayerSplit.TwoDCharacter N β` is a hypothesis here; `TwoDVanish` proves the conclusion it supplies.
-/

namespace MassGap.MixEqui

open MeasureTheory Filter Topology Set MassGap
open MassGap.CouplingTower (StrongEnd)

variable {N : ℕ}

/-! ## 1. The input -/

/-- **`MixEquiUp N β`, a named input (not proved)**: the window defects `t ↦ DA N β t w` are one-sided
equicontinuous on the segment `[0, β]`, uniformly over the windows `w ≥ 1`. DERIVED: `1` the least window; `0` the
axis. -/
def MixEquiUp (N : ℕ) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, 1 ≤ w → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ β → t - s < δ →
    AnisoTorus.DA N β t w ≤ AnisoTorus.DA N β s w + ε

/-- **A bounded cut energy gives one-sided equicontinuity**: `MixCutBound N β ⇒ MixEquiUp N β`, with
`δ = ε/(|M| + 1)`, by the mean value theorem. DERIVED: `1` the shift keeping `|M| + 1 > 0`. -/
theorem mixEquiUp_of_mixCutBound {β : ℝ} (h : MixCut.MixCutBound N β) : MixEquiUp N β := by
  obtain ⟨M, hM⟩ := h
  intro ε hε
  have hM1 : (0 : ℝ) < |M| + 1 := by positivity
  refine ⟨ε / (|M| + 1), by positivity, fun w hw s t hs hst htβ hδ => ?_⟩
  rcases hst.eq_or_lt with rfl | hlt
  · linarith
  have hpos : 0 < t - s := sub_pos.mpr hlt
  obtain ⟨τ, hτ, hτeq⟩ := exists_hasDerivAt_eq_slope (fun x => AnisoTorus.DA N β x w)
    (fun x => MixCut.mixCut N β x w) hlt (MixAnchor.continuous_DA β w).continuousOn
    (fun x _ => MixCut.hasDerivAt_DA_mix β x w)
  have hCτ := hM w hw τ (hs.trans hτ.1.le) (hτ.2.le.trans htβ)
  rw [hτeq, div_le_iff₀ hpos] at hCτ
  have h1 : M * (t - s) ≤ |M| * (t - s) := mul_le_mul_of_nonneg_right (le_abs_self M) hpos.le
  have h2 : |M| * (t - s) ≤ |M| * (ε / (|M| + 1)) := mul_le_mul_of_nonneg_left hδ.le (abs_nonneg M)
  have h3 : |M| * (ε / (|M| + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hM1]
    nlinarith [abs_nonneg M]
  linarith

/-- **A bounded variance difference gives one-sided equicontinuity**, through
`MixCutTest.mixCutBound_of_varGap`. No numeral. -/
theorem mixEquiUp_of_varGap {β : ℝ} (h : MixCutTest.VarGap N β) : MixEquiUp N β :=
  mixEquiUp_of_mixCutBound (MixCutTest.mixCutBound_of_varGap h)

/-! ## 2. The first stall -/

/-- **One-sided equicontinuity excludes a stall on the segment**: under `TwoDCharacter N β` (conclusion proved in `TwoDVanish`),
`MixEquiUp N β ⇒ NoStallOnSegment N β`. Inherited: `1/1000` the seed. DERIVED: `1/2000` half the seed; `2` the
halving of `δ`; `1` the least window; `0` the axis. -/
theorem noStallOnSegment_of_mixEquiUp (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hC : LayerSplit.TwoDCharacter N β) (hE : MixEquiUp N β) : MixPlane.NoStallOnSegment N β := by
  by_contra h
  obtain ⟨ts, hts0, htsβ, hstall, hvan⟩ := MixPlane.segment_first_stall hN hβ hC h
  obtain ⟨δ, hδ, hE'⟩ := hE (1 / 2000) (by norm_num)
  set s' : ℝ := max 0 (ts - δ / 2) with hs'def
  have hs'0 : 0 ≤ s' := le_max_left _ _
  have hs't : s' < ts := max_lt hts0 (by linarith)
  have hgap : ts - s' < δ := by linarith [le_max_right 0 (ts - δ / 2)]
  have hv := hvan s' hs'0 hs't
  obtain ⟨w, hlt, hw⟩ := ((hv.2.2.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2000 by norm_num))).and
    (eventually_ge_atTop 1)).exists
  have hlt' : AnisoTorus.DA N β s' w < 1 / 2000 := hlt
  have hstep := hE' w hw s' ts hs'0 hs't.le htsβ hgap
  have hseed : AnisoTorus.DA N β ts w < 1 / 1000 := by linarith
  exact hstall.2 ((MixPlane.mem_vanishSet_iff_seed_lt hN).mpr ⟨⟨hβ, hts0.le⟩, w, hw, hseed⟩)

/-- **Frequently `TwoDCharacter ∧ MixEquiUp` gives the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_mixEquiUp (hN : N ≠ 0)
    (h : ∃ᶠ β in atTop, LayerSplit.TwoDCharacter N β ∧ MixEquiUp N β) : StrongEnd N :=
  MixPlane.strongEnd_of_noStallOnSegment ((h.and_eventually (eventually_ge_atTop (0 : ℝ))).mono
    fun _ hβ => noStallOnSegment_of_mixEquiUp hN hβ.2 hβ.1.1 hβ.1.2)

/-! ## 3. The converse -/

/-- The seed sets up to window `C`: `{t | ∃ c, 1 ≤ c ≤ C, DA N β t c < 1/1000}`. Inherited: `1/1000` the seed.
DERIVED: `1` the least window. -/
def seedUpTo (N : ℕ) (β : ℝ) (C : ℕ) : Set ℝ :=
  {t | ∃ c : ℕ, 1 ≤ c ∧ c ≤ C ∧ AnisoTorus.DA N β t c < 1 / 1000}

theorem isOpen_seedUpTo (β : ℝ) (C : ℕ) : IsOpen (seedUpTo N β C) := by
  have e : seedUpTo N β C = ⋃ c : ℕ, ⋃ (_ : 1 ≤ c ∧ c ≤ C), {t : ℝ | AnisoTorus.DA N β t c < 1 / 1000} := by
    ext t; simp only [seedUpTo, mem_setOf_eq, mem_iUnion, exists_prop, and_assoc]
  rw [e]
  exact isOpen_iUnion fun c => isOpen_iUnion fun _ =>
    isOpen_lt (MixAnchor.continuous_DA β c) continuous_const

theorem seedUpTo_mono (β : ℝ) : Monotone (seedUpTo N β) := by
  intro C C' hCC' t ⟨c, h1, hc, hlt⟩
  exact ⟨c, h1, hc.trans hCC', hlt⟩

/-- **The convergence is uniform on a vanishing segment**: if every point of `[0, β]` vanishes, one window `C`
gives `DA N β t w ≤ 4^{−i}/1000` for every `t ∈ [0, β]` and every `w ≥ C + i`. Inherited: `1/1000` the seed;
`1/4` the contraction. DERIVED: `1` the least window; `0` the axis; `1000` the denominator of the
inherited seed `1/1000` of `DoublingSharp`. -/
theorem uniform_decay (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : MixPlane.NoStallOnSegment N β) :
    ∃ C : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ β → ∀ i w : ℕ, C + i ≤ w →
      AnisoTorus.DA N β t w ≤ (1 / 1000) * (1 / 4) ^ i := by
  have hcov : Icc 0 β ⊆ ⋃ C : ℕ, seedUpTo N β C := by
    intro t ht
    have hv : (β, t) ∈ MixPlane.VanishSet N := by
      by_contra hv
      exact h t ht.1 ht.2 ⟨⟨hβ, ht.1⟩, hv⟩
    obtain ⟨_, c, hc, hlt⟩ := (MixPlane.mem_vanishSet_iff_seed_lt hN).mp hv
    exact mem_iUnion.mpr ⟨c, c, hc, le_rfl, hlt⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.elim_directed_cover (seedUpTo N β) (fun C => isOpen_seedUpTo β C) hcov
    (seedUpTo_mono β).directed_le
  refine ⟨C, fun t ht0 htβ i w hw => ?_⟩
  obtain ⟨c, hc1, hcC, hlt⟩ := hC ⟨ht0, htβ⟩
  have hd := MixAnchor.DA_decay hN hβ ht0 hc1 hlt.le (w - c)
  rw [Nat.add_sub_of_le (by omega)] at hd
  have hp : (1 / 4 : ℝ) ^ (w - c) ≤ (1 / 4) ^ i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  nlinarith

/-- **No stall on the segment gives one-sided equicontinuity** (no `TwoDCharacter` read). Inherited: `1/1000`,
`1/4`. DERIVED: `1` the least window and the bound `1/4 < 1`; `0` the floor of `DA` and the axis. -/
theorem mixEquiUp_of_noStallOnSegment (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (h : MixPlane.NoStallOnSegment N β) : MixEquiUp N β := by
  obtain ⟨C, hC⟩ := uniform_decay hN hβ h
  intro ε hε
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hε (show (1 / 4 : ℝ) < 1 by norm_num)
  set K : ℕ := C + i with hK
  let F : ℝ → (Fin K → ℝ) := fun t w => AnisoTorus.DA N β t w
  have hF : Continuous F := continuous_pi fun w => MixAnchor.continuous_DA β w
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc (0 : ℝ) β) hF.continuousOn) ε hε
  refine ⟨δ, hδ, fun w hw s t hs hst htβ hts => ?_⟩
  by_cases hwK : w < K
  · have hd : dist (F t) (F s) < ε := hU t ⟨hs.trans hst, htβ⟩ s ⟨hs, hst.trans htβ⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; exact hts)
    have hc := (dist_le_pi_dist (F t) (F s) ⟨w, hwK⟩).trans_lt hd
    rw [Real.dist_eq] at hc
    have hc' : AnisoTorus.DA N β t w - AnisoTorus.DA N β s w < ε := (le_abs_self _).trans_lt hc
    linarith
  · have hdec := hC t (hs.trans hst) htβ i w (by omega)
    have hnn := MixAnchor.DA_nonneg hN hβ hs hw
    have hp : (1 / 4 : ℝ) ^ i ≥ 0 := by positivity
    nlinarith

/-- **`MixEquiUp` is the segment statement**: under `N ≠ 0`, `β ≥ 0` and the cited `TwoDCharacter N β`,
`MixEquiUp N β ↔ NoStallOnSegment N β`. A restatement, not a discharge. DERIVED: `0` the axis. -/
theorem mixEquiUp_iff_noStall (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (hC : LayerSplit.TwoDCharacter N β) :
    MixEquiUp N β ↔ MixPlane.NoStallOnSegment N β :=
  ⟨noStallOnSegment_of_mixEquiUp hN hβ hC, mixEquiUp_of_noStallOnSegment hN hβ⟩

/-! ## 4. The decoupled variance -/

section Variance

open MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut

/-- **Averaging a continuous function over a translating family**: `MixCut.integral_haar_avg` with the plaquette
density replaced by any continuous `f`. No numeral. -/
theorem integral_avg_gen {L : Fin 4 → ℕ} (f : SUN.SU N → ℝ) (hf : Continuous f)
    (T : SUN.SU N → (RLink L → SUN.SU N) → (RLink L → SUN.SU N))
    (hT : ∀ (g : SUN.SU N) (F : (RLink L → SUN.SU N) → ℝ), Continuous F →
      ∫ U, F (T g U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
        = ∫ U, F U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)))
    (Φ : (RLink L → SUN.SU N) → SUN.SU N) (hΦ : Continuous Φ) (E : (RLink L → SUN.SU N) → ℝ)
    (hE : Continuous E) (m : SUN.SU N → SUN.SU N → SUN.SU N)
    (hm : Continuous fun p : SUN.SU N × SUN.SU N => m p.1 p.2)
    (hmΦ : ∀ g U, Φ (T g U) = m g (Φ U)) (hET : ∀ g U, E (T g U) = E U)
    (hmH : ∀ k, ∫ g, f (m g k) ∂(probHaar (SUN.SU N)) = ∫ g, f g ∂(probHaar (SUN.SU N))) :
    ∫ U, f (Φ U) * E U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      = (∫ g, f g ∂(probHaar (SUN.SU N)))
        * ∫ U, E U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  set π : Measure (RLink L → SUN.SU N) := Measure.pi fun _ : RLink L => probHaar (SUN.SU N) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  have hshift : ∀ g : SUN.SU N, ∫ U, f (m g (Φ U)) * E U ∂π = ∫ U, f (Φ U) * E U ∂π := by
    intro g
    rw [← hT g (fun U => f (Φ U) * E U) ((hf.comp hΦ).mul hE)]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp only [hmΦ, hET]
  have hjc : Continuous fun z : SUN.SU N × (RLink L → SUN.SU N) => f (m z.1 (Φ z.2)) * E z.2 :=
    (hf.comp (hm.comp (continuous_fst.prodMk (hΦ.comp continuous_snd)))).mul (hE.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (g : SUN.SU N) (U : RLink L → SUN.SU N) =>
      f (m g (Φ U)) * E U) ((probHaar (SUN.SU N)).prod π) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hjc.continuousOn
    exact ContactFloor.integrable_of_bounded hjc.measurable M
      (fun z => by have hz := hM z (mem_univ z); rw [Real.norm_eq_abs] at hz; exact hz)
  have hswap := integral_integral_swap hint
  calc ∫ U, f (Φ U) * E U ∂π
      = ∫ _g : SUN.SU N, (∫ U, f (Φ U) * E U ∂π) ∂(probHaar (SUN.SU N)) :=
        (ContactFloor.integral_const_prob _ _).symm
    _ = ∫ g, (∫ U, f (m g (Φ U)) * E U ∂π) ∂(probHaar (SUN.SU N)) := by simp only [hshift]
    _ = ∫ U, (∫ g, f (m g (Φ U)) * E U ∂(probHaar (SUN.SU N))) ∂π := hswap
    _ = ∫ U, (∫ g, f g ∂(probHaar (SUN.SU N))) * E U ∂π := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        simp only [integral_mul_const, hmH]
    _ = (∫ g, f g ∂(probHaar (SUN.SU N))) * ∫ U, E U ∂π := integral_const_mul _ _

/-- The Haar second moment of the plaquette density, `⟨φ²⟩_Haar`. DERIVED: `2` the square. -/
noncomputable def haarSq (N : ℕ) : ℝ :=
  ∫ g, WilsonAction.wilsonDensity (N := N) g ^ 2 ∂(probHaar (SUN.SU N))

/-- **The Haar variance of the plaquette density**, `Var_Haar(φ) = ⟨φ²⟩_Haar − ⟨φ⟩_Haar²`. DERIVED: `2` the
square. -/
noncomputable def haarVar (N : ℕ) : ℝ := haarSq N - WindowRead.haarMeanN N ^ 2

/-! ### Sites and corners on the side-`n` torus -/

theorem rshift_apply (n : ℕ) (i : Fin 4) (x : RSite (fun _ : Fin 4 => n)) (k : Fin 4) :
    rshift (fun _ : Fin 4 => n) i x k = if k = i then finRotate n (x i) else x k := by
  unfold rshift
  by_cases h : k = i
  · subst h; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne h, if_neg h]

/-- Two sites differing by one step in one coordinate are distinct. DERIVED: `2` the least extent. -/
theorem ne_of_rot {n : ℕ} (hn : 2 ≤ n) {x y : RSite (fun _ : Fin 4 => n)} {k : Fin 4}
    (h : x k = finRotate n (y k)) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  exact WindowRead.finRotate_ne hn (y k) h.symm

/-- **Two steps never return** along an extent `≥ 3`. DERIVED: `3` the least extent on which two steps move;
`2` the steps; `1` the step. -/
theorem finRotate2_ne {m : ℕ} (hm : 3 ≤ m) (a : Fin m) : finRotate m (finRotate m a) ≠ a := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  intro h
  rw [finRotate_succ_apply, finRotate_succ_apply] at h
  have h2 := congrArg Fin.val h
  have e1 := Fin.val_add_one a
  have e2 := Fin.val_add_one (a + 1)
  have ha := a.isLt
  split_ifs at e1 with c1 <;> split_ifs at e2 with c2 <;>
    simp only [Fin.ext_iff, Fin.val_last] at c1 c2 <;> omega

/-- The four corners `y, y + i, y + j, y + i + j` of the plaquette `((i, j), y)`. No numeral. -/
def IsCorner (n : ℕ) (i j : Fin 4) (y c : RSite (fun _ : Fin 4 => n)) : Prop :=
  c = y ∨ c = rshift (fun _ => n) i y ∨ c = rshift (fun _ => n) j y ∨
    c = rshift (fun _ => n) i (rshift (fun _ => n) j y)

/-- Each coordinate of a corner is the base coordinate or one step past it. No numeral. -/
theorem corner_comp {n : ℕ} {i j : Fin 4} (hij : i ≠ j) {y c : RSite (fun _ : Fin 4 => n)}
    (hc : IsCorner n i j y c) (k : Fin 4) : c k = y k ∨ c k = finRotate n (y k) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [rshift_apply]; split_ifs with h
    · subst h; exact Or.inr rfl
    · exact Or.inl rfl
  · rw [rshift_apply]; split_ifs with h
    · subst h; exact Or.inr rfl
    · exact Or.inl rfl
  · by_cases hki : k = i
    · subst hki; right; rw [rshift_apply, if_pos rfl, rshift_apply, if_neg hij]
    · rw [rshift_apply, if_neg hki, rshift_apply]; split_ifs with hkj
      · subst hkj; exact Or.inr rfl
      · exact Or.inl rfl

/-- A site one step past the base in a coordinate outside the plaquette's plane is not a corner.
DERIVED: `2` the least extent. -/
theorem not_corner {n : ℕ} (hn : 2 ≤ n) {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j)
    {y c : RSite (fun _ : Fin 4 => n)} (hc : c k = finRotate n (y k)) : ¬ IsCorner n i j y c := by
  intro h
  have e : c k = y k := by
    rcases h with rfl | rfl | rfl | rfl <;> simp [rshift_apply, hki, hkj]
  rw [e] at hc
  exact WindowRead.finRotate_ne hn (y k) hc.symm

/-- **Distinct bases separate** on extent `≥ 3`: for plaquettes based at `y ≠ y'`, either `y'` is not a corner of
the first or `y` is not a corner of the second. DERIVED: `3` the least extent on which two steps move. -/
theorem base_sep {n : ℕ} (hn : 3 ≤ n) {i j i' j' : Fin 4} (hij : i ≠ j) (hij' : i' ≠ j')
    {y y' : RSite (fun _ : Fin 4 => n)} (hyy : y ≠ y') :
    ¬ IsCorner n i j y y' ∨ ¬ IsCorner n i' j' y' y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hk : ∃ k, y' k = finRotate n (y k) := by
    by_contra hk
    push Not at hk
    exact hyy (funext fun k => ((corner_comp hij h1 k).resolve_right (hk k)).symm)
  obtain ⟨k, hk⟩ := hk
  rcases corner_comp hij' h2 k with h | h
  · rw [hk] at h; exact WindowRead.finRotate_ne (show 2 ≤ n by omega) (y k) h.symm
  · rw [hk] at h; exact finRotate2_ne hn (y k) h.symm

/-! ### The layer rotation at the corners of a mixed plaquette -/

/-- **A mixed plaquette that does not have `z` as a corner is unchanged** by the layer rotation at `z`.
DERIVED: `2`, `0` as in `MixCut.gT`. -/
theorem hol_gT_off {n : ℕ} {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y z : RSite (fun _ : Fin 4 => n)) (a : SUN.SU N) (U : Lk n → SUN.SU N) (hz : ¬ IsCorner n i j y z) :
    (sysR (fun _ => n) N).hol ((i, j), y) (gT (fun _ => n) (siteG (fun _ => n) z a) U)
      = (sysR (fun _ => n) N).hol ((i, j), y) U := by
  simp only [IsCorner, not_or] at hz
  obtain ⟨h0, h1, h2, h3⟩ := hz
  rw [hol_eq, hol_eq]
  simp only [gT, siteG, if_pos hi, if_neg hj, if_neg (Ne.symm h0), if_neg (Ne.symm h1),
    if_neg (Ne.symm h2), if_neg (Ne.symm h3), inv_one, mul_one, one_mul]

/-- The holonomy of `((i, j), y)` read from the corner `y + j`. No numeral. -/
noncomputable def psiJ {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) (U : Lk n → SUN.SU N) :
    SUN.SU N :=
  (U (j, y))⁻¹ * U (i, y) * U (j, rshift (fun _ => n) i y) * (U (i, rshift (fun _ => n) j y))⁻¹

/-- The holonomy of `((i, j), y)` read from the corner `y + i`. No numeral. -/
noncomputable def psiI {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) (U : Lk n → SUN.SU N) :
    SUN.SU N :=
  U (j, rshift (fun _ => n) i y) * (U (i, rshift (fun _ => n) j y))⁻¹ * (U (j, y))⁻¹ * U (i, y)

theorem continuous_psiJ {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) :
    Continuous (psiJ (N := N) i j y) := by
  unfold psiJ; fun_prop

theorem continuous_psiI {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) :
    Continuous (psiI (N := N) i j y) := by
  unfold psiI; fun_prop

/-- Reading from another corner conjugates the holonomy, so the density is the same. No numeral. -/
theorem plaq_eq_psiJ {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) (U : Lk n → SUN.SU N) :
    plaq N n ((i, j), y) U = WilsonAction.wilsonDensity (psiJ i j y U) := by
  unfold plaq
  rw [show psiJ i j y U = (U (j, y))⁻¹ * (sysR (fun _ => n) N).hol ((i, j), y) U * ((U (j, y))⁻¹)⁻¹ by
    unfold psiJ; rw [hol_eq]; group, WilsonAction.wilsonDensity_conj]

theorem plaq_eq_psiI {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) (U : Lk n → SUN.SU N) :
    plaq N n ((i, j), y) U = WilsonAction.wilsonDensity (psiI i j y U) := by
  unfold plaq
  rw [show psiI i j y U = (U (i, y))⁻¹ * (sysR (fun _ => n) N).hol ((i, j), y) U * ((U (i, y))⁻¹)⁻¹ by
    unfold psiI; rw [hol_eq]; group, WilsonAction.wilsonDensity_conj]

/-- **The rotation at the corner `y + j` right-translates the holonomy read there**, for a plaquette with first
direction in `{0, 1}` and second in `{2, 3}`. DERIVED: `2` the least extent; `2`, `0` as in `MixCut.gT`. -/
theorem psiJ_gT {n : ℕ} (hn : 2 ≤ n) {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y : RSite (fun _ : Fin 4 => n)) (a : SUN.SU N) (U : Lk n → SUN.SU N) :
    psiJ i j y (gT (fun _ => n) (siteG (fun _ => n) (rshift (fun _ => n) j y) a) U) = psiJ i j y U * a⁻¹ := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have h0 : y ≠ rshift (fun _ => n) j y := (WindowRead.rshift_ne _ hn y).symm
  have h1 : rshift (fun _ => n) i y ≠ rshift (fun _ => n) j y :=
    ne_of_rot hn (k := i) (by simp [rshift_apply, hij])
  have h3 : rshift (fun _ => n) i (rshift (fun _ => n) j y) ≠ rshift (fun _ => n) j y :=
    WindowRead.rshift_ne _ hn _
  unfold psiJ
  simp only [gT, siteG, if_pos hi, if_neg hj, if_neg h0, if_neg h1, if_neg h3, ↓reduceIte, inv_one,
    mul_one, one_mul]
  group

/-- **The rotation at the corner `y + i` right-translates the holonomy read there.** DERIVED: as in `psiJ_gT`. -/
theorem psiI_gT {n : ℕ} (hn : 2 ≤ n) {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y : RSite (fun _ : Fin 4 => n)) (a : SUN.SU N) (U : Lk n → SUN.SU N) :
    psiI i j y (gT (fun _ => n) (siteG (fun _ => n) (rshift (fun _ => n) i y) a) U) = psiI i j y U * a⁻¹ := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have h0 : y ≠ rshift (fun _ => n) i y := (WindowRead.rshift_ne _ hn y).symm
  have h1 : rshift (fun _ => n) j y ≠ rshift (fun _ => n) i y :=
    ne_of_rot hn (k := j) (by simp [rshift_apply, Ne.symm hij])
  have h3 : rshift (fun _ => n) i (rshift (fun _ => n) j y) ≠ rshift (fun _ => n) i y :=
    ne_of_rot hn (k := j) (by simp [rshift_apply, Ne.symm hij])
  unfold psiI
  simp only [gT, siteG, if_pos hi, if_neg hj, if_neg h0, if_neg h1, if_neg h3, ↓reduceIte, inv_one,
    mul_one, one_mul]
  group

/-! ### Pair integrals at the decoupled end -/

/-- A first direction in `{0, 1}` and a second in `{2, 3}` make a mixed orientation. DERIVED: `2`, `0` the
blocks. -/
theorem mixed_of_blocks : ∀ {a b : Fin 4}, a.val / 2 = 0 → ¬ b.val / 2 = 0 →
    ¬ AnisoTorus.inPlane (a, b) = true := by
  decide

/-- **The product of two mixed plaquettes averages to `⟨φ⟩_Haar²`** when a layer rotation family translates the
first (through a corner read `Φ`) and fixes the second. DERIVED: `2` the least extent and the square; `0` the
decoupled end. -/
theorem pair_of_move {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (q q' : Pq n) (hq' : ¬ AnisoTorus.inPlane q'.1 = true)
    (T : SUN.SU N → (Lk n → SUN.SU N) → (Lk n → SUN.SU N))
    (hTg : ∀ g, ∃ h : RSite (fun _ : Fin 4 => n) → SUN.SU N, T g = gT (fun _ => n) h)
    (hq'T : ∀ g U, plaq N n q' (T g U) = plaq N n q' U)
    (Φ : (Lk n → SUN.SU N) → SUN.SU N) (hΦ : Continuous Φ)
    (hφ : ∀ U, plaq N n q U = WilsonAction.wilsonDensity (Φ U))
    (m : SUN.SU N → SUN.SU N → SUN.SU N) (hm : Continuous fun p : SUN.SU N × SUN.SU N => m p.1 p.2)
    (hmΦ : ∀ g U, Φ (T g U) = m g (Φ U))
    (hmH : ∀ k, ∫ g, WilsonAction.wilsonDensity (m g k) ∂(probHaar (SUN.SU N)) = WindowRead.haarMeanN N) :
    ∫ U, plaq N n q U * plaq N n q' U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = WindowRead.haarMeanN N ^ 2 * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hG : Continuous fun U : Lk n → SUN.SU N => plaq N n q' U * Real.exp (-(β * sinR N n U)) :=
    (continuous_plaq n q').mul hE
  have hGT : ∀ g U, plaq N n q' (T g U) * Real.exp (-(β * sinR N n (T g U)))
      = plaq N n q' U * Real.exp (-(β * sinR N n U)) := by
    intro g U
    obtain ⟨h, hh⟩ := hTg g
    rw [hq'T g U, hh, sinR_gT]
  have key := integral_haar_avg (fun _ => n) T
    (fun g F hF => by obtain ⟨h, hh⟩ := hTg g; rw [hh]; exact integral_gT (fun _ => n) h F hF)
    Φ hΦ _ hG m hm hmΦ (fun g U => hGT g U) hmH
  calc ∫ U, plaq N n q U * plaq N n q' U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = ∫ U, WilsonAction.wilsonDensity (Φ U) * (plaq N n q' U * Real.exp (-(β * sinR N n U))) ∂piH N n := by
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        simp only [hφ U]; ring
    _ = WindowRead.haarMeanN N * ∫ U, plaq N n q' U * Real.exp (-(β * sinR N n U)) ∂piH N n := key
    _ = WindowRead.haarMeanN N ^ 2 * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
        rw [integral_plaq_mul_exp hn β q' hq']; ring

/-- **A mixed plaquette squared averages to `⟨φ²⟩_Haar`** at the decoupled end. DERIVED: `2` the least extent and
the square; `0` the decoupled end. -/
theorem integral_diag {n : ℕ} (hn : 2 ≤ n) (β : ℝ) {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y : RSite (fun _ : Fin 4 => n)) :
    ∫ U, plaq N n ((i, j), y) U * plaq N n ((i, j), y) U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = haarSq N * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hET : ∀ (g : SUN.SU N) (U : Lk n → SUN.SU N),
      Real.exp (-(β * sinR N n (gT (fun _ => n) (siteG (fun _ => n) y g) U))) = Real.exp (-(β * sinR N n U)) :=
    fun g U => by rw [sinR_gT]
  have key := integral_avg_gen (L := fun _ => n) (fun g => WilsonAction.wilsonDensity g ^ 2)
    (WilsonAction.continuous_wilsonDensity.pow 2)
    (fun g U => gT (fun _ => n) (siteG (fun _ => n) y g) U)
    (fun g F hF => integral_gT (fun _ => n) _ F hF)
    (fun U => (sysR (fun _ => n) N).hol ((i, j), y) U) (MixAnchor.continuous_hol _)
    (fun U => Real.exp (-(β * sinR N n U))) hE (fun g k => g * k) continuous_mul
    (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj y) (fun g U => hET g U)
    (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N))
      (fun g => WilsonAction.wilsonDensity g ^ 2) k)
  refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
  simp only [plaq]; ring

/-- **Distinct mixed plaquettes are uncorrelated at the decoupled end** on extent `≥ 3`: for plaquettes with
first direction in `{0, 1}` and second in `{2, 3}`, `∫ φ_p φ_{p'} e^{−β S_in} = ⟨φ⟩_Haar² ∫ e^{−β S_in}` when
`p ≠ p'`. Distinct bases are separated by `base_sep` and rotated at a base; a common base is rotated at the corner
`y + j` (different second directions) or `y + i` (same second direction). DERIVED: `3` the least extent on which
two steps move; `2` the square. -/
theorem integral_pair_ne {n : ℕ} (hn : 3 ≤ n) (β : ℝ) {i j i' j' : Fin 4} (hi : i.val / 2 = 0)
    (hj : ¬ j.val / 2 = 0) (hi' : i'.val / 2 = 0) (hj' : ¬ j'.val / 2 = 0) (y y' : RSite (fun _ : Fin 4 => n))
    (hne : (((i, j), y) : Pq n) ≠ ((i', j'), y')) :
    ∫ U, plaq N n ((i, j), y) U * plaq N n ((i', j'), y') U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = WindowRead.haarMeanN N ^ 2 * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hn2 : 2 ≤ n := by omega
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn2
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have hij' : i' ≠ j' := fun h => hj' (h ▸ hi')
  by_cases hy : y = y'
  · subst hy
    by_cases hjj : j = j'
    · subst hjj
      have hii : i ≠ i' := fun h => hne (by rw [h])
      have hz : ¬ IsCorner n i' j y (rshift (fun _ => n) i y) :=
        not_corner hn2 (k := i) hii hij (by simp [rshift_apply])
      exact pair_of_move hn2 β ((i, j), y) ((i', j), y) (mixed_of_blocks hi' hj')
        (fun g U => gT (fun _ => n) (siteG (fun _ => n) (rshift (fun _ => n) i y) g⁻¹) U)
        (fun g => ⟨_, rfl⟩)
        (fun g U => congrArg WilsonAction.wilsonDensity (hol_gT_off hi' hj y _ g⁻¹ U hz))
        (psiI i j y) (continuous_psiI i j y) (plaq_eq_psiI i j y) (fun g k => k * g)
        (continuous_snd.mul continuous_fst)
        (fun g U => by rw [psiI_gT hn2 hi hj y g⁻¹ U, inv_inv])
        (fun k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)
    · have hz : ¬ IsCorner n i' j' y (rshift (fun _ => n) j y) :=
        not_corner hn2 (k := j) (fun h => hj (h ▸ hi')) hjj (by simp [rshift_apply])
      exact pair_of_move hn2 β ((i, j), y) ((i', j'), y) (mixed_of_blocks hi' hj')
        (fun g U => gT (fun _ => n) (siteG (fun _ => n) (rshift (fun _ => n) j y) g⁻¹) U)
        (fun g => ⟨_, rfl⟩)
        (fun g U => congrArg WilsonAction.wilsonDensity (hol_gT_off hi' hj' y _ g⁻¹ U hz))
        (psiJ i j y) (continuous_psiJ i j y) (plaq_eq_psiJ i j y) (fun g k => k * g)
        (continuous_snd.mul continuous_fst)
        (fun g U => by rw [psiJ_gT hn2 hi hj y g⁻¹ U, inv_inv])
        (fun k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)
  · rcases base_sep hn hij hij' hy with h | h
    · have hc : ∫ U, plaq N n ((i, j), y) U * plaq N n ((i', j'), y') U * Real.exp (-(β * sinR N n U)) ∂piH N n
          = ∫ U, plaq N n ((i', j'), y') U * plaq N n ((i, j), y) U * Real.exp (-(β * sinR N n U)) ∂piH N n :=
        integral_congr_ae (Eventually.of_forall fun U => by simp only; ring)
      rw [hc]
      exact pair_of_move hn2 β ((i', j'), y') ((i, j), y) (mixed_of_blocks hi hj)
        (fun g U => gT (fun _ => n) (siteG (fun _ => n) y' g) U) (fun g => ⟨_, rfl⟩)
        (fun g U => congrArg WilsonAction.wilsonDensity (hol_gT_off hi hj y y' g U h))
        (fun U => (sysR (fun _ => n) N).hol ((i', j'), y') U) (MixAnchor.continuous_hol _) (fun U => rfl)
        (fun g k => g * k) continuous_mul (fun g U => hol_gT_mixA (fun _ => n) hL g U hi' hj' y')
        (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)
    · exact pair_of_move hn2 β ((i, j), y) ((i', j'), y') (mixed_of_blocks hi' hj')
        (fun g U => gT (fun _ => n) (siteG (fun _ => n) y g) U) (fun g => ⟨_, rfl⟩)
        (fun g U => congrArg WilsonAction.wilsonDensity (hol_gT_off hi' hj' y' y g U h))
        (fun U => (sysR (fun _ => n) N).hol ((i, j), y) U) (MixAnchor.continuous_hol _) (fun U => rfl)
        (fun g k => g * k) continuous_mul (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj y)
        (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) WilsonAction.wilsonDensity k)

/-! ### Normal orientation and the count -/

/-- The orientation with first direction in `{0, 1}`: a mixed orientation, or its reverse. DERIVED: `2`, `0`
the blocks. -/
def onf (o : Fin 4 × Fin 4) : Fin 4 × Fin 4 := if o.1.val / 2 = 0 then o else o.swap

theorem onf_low : ∀ o : Fin 4 × Fin 4, ¬ AnisoTorus.inPlane o = true →
    (onf o).1.val / 2 = 0 ∧ ¬ (onf o).2.val / 2 = 0 := by
  decide

theorem onf_iff : ∀ o o' : Fin 4 × Fin 4, ¬ AnisoTorus.inPlane o = true → ¬ AnisoTorus.inPlane o' = true →
    (onf o' = onf o ↔ o' = o ∨ o' = o.swap) := by
  decide

theorem inPlane_swap' : ∀ o : Fin 4 × Fin 4, AnisoTorus.inPlane o.swap = AnisoTorus.inPlane o := by
  decide

theorem swap_ne : ∀ o : Fin 4 × Fin 4, ¬ AnisoTorus.inPlane o = true → o.swap ≠ o := by
  decide

/-- The reversed plaquette has the inverse holonomy, hence the same density. No numeral. -/
theorem plaq_swap {n : ℕ} (i j : Fin 4) (y : RSite (fun _ : Fin 4 => n)) (U : Lk n → SUN.SU N) :
    plaq N n ((j, i), y) U = plaq N n ((i, j), y) U := by
  unfold plaq
  rw [show (sysR (fun _ => n) N).hol ((j, i), y) U = ((sysR (fun _ => n) N).hol ((i, j), y) U)⁻¹ by
    rw [hol_eq, hol_eq]; group, RectWilson.wilsonDensity_inv]

theorem plaq_onf {n : ℕ} (q : Pq n) (U : Lk n → SUN.SU N) : plaq N n (onf q.1, q.2) U = plaq N n q U := by
  obtain ⟨⟨a, b⟩, y⟩ := q
  unfold onf
  split_ifs
  · rfl
  · exact plaq_swap a b y U

/-- **The pair integral of two mixed plaquettes at the decoupled end**, extent `≥ 3`: `⟨φ²⟩_Haar` when the two
are the same plaquette up to orientation, `⟨φ⟩_Haar²` otherwise. DERIVED: `3` the least extent; `2` the square;
`0` the decoupled end. -/
theorem integral_pair {n : ℕ} (hn : 3 ≤ n) (β : ℝ) (q q' : Pq n) (hq : ¬ AnisoTorus.inPlane q.1 = true)
    (hq' : ¬ AnisoTorus.inPlane q'.1 = true) :
    ∫ U, plaq N n q U * plaq N n q' U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = (if onf q'.1 = onf q.1 ∧ q'.2 = q.2 then haarSq N else WindowRead.haarMeanN N ^ 2)
        * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have e : ∫ U, plaq N n q U * plaq N n q' U * Real.exp (-(β * sinR N n U)) ∂piH N n
      = ∫ U, plaq N n (onf q.1, q.2) U * plaq N n (onf q'.1, q'.2) U * Real.exp (-(β * sinR N n U)) ∂piH N n :=
    integral_congr_ae (Eventually.of_forall fun U => by simp only [plaq_onf])
  rw [e]
  obtain ⟨hi, hj⟩ := onf_low q.1 hq
  obtain ⟨hi', hj'⟩ := onf_low q'.1 hq'
  split_ifs with hc
  · rw [hc.1, hc.2]
    exact integral_diag (by omega) β hi hj q.2
  · exact integral_pair_ne hn β hi hj hi' hj' q.2 q'.2 (fun h => hc
      ⟨by have h1 := congrArg Prod.fst h; exact h1.symm, by have h2 := congrArg Prod.snd h; exact h2.symm⟩)

/-- **The one-plaquette count**: for a mixed `q`, the sum over mixed `q'` of the pair weight is
`8 n⁴ ⟨φ⟩² + 2 Var_Haar(φ)`: `q` itself and its reverse carry `⟨φ²⟩`. DERIVED: `8`, `4` as in
`MixCut.sum_mixed`; `2` the two orientations of one plaquette and the square. -/
theorem sum_pair_weight (n : ℕ) (q : Pq n) (hq : ¬ AnisoTorus.inPlane q.1 = true) :
    (∑ q' : Pq n, if AnisoTorus.inPlane q'.1 then (0 : ℝ)
      else (if onf q'.1 = onf q.1 ∧ q'.2 = q.2 then haarSq N else WindowRead.haarMeanN N ^ 2))
      = 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N ^ 2 + 2 * haarVar N := by
  have hsw : ((q.1.swap, q.2) : Pq n) ≠ q := fun h => swap_ne q.1 hq (congrArg Prod.fst h)
  have hpt : ∀ q' : Pq n, (if AnisoTorus.inPlane q'.1 then (0 : ℝ)
      else (if onf q'.1 = onf q.1 ∧ q'.2 = q.2 then haarSq N else WindowRead.haarMeanN N ^ 2))
      = (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else WindowRead.haarMeanN N ^ 2)
        + ((if q' = q then haarVar N else 0) + (if q' = (q.1.swap, q.2) then haarVar N else 0)) := by
    intro q'
    by_cases hq' : AnisoTorus.inPlane q'.1 = true
    · have h1 : q' ≠ q := fun h => hq (h ▸ hq')
      have h2 : q' ≠ (q.1.swap, q.2) := fun h => hq (by
        have := congrArg (fun r : Pq n => AnisoTorus.inPlane r.1) h
        simp only [inPlane_swap'] at this
        rw [← this]; exact hq')
      simp only [hq', if_true, if_neg h1, if_neg h2, add_zero]
    · have hiff := onf_iff q.1 q'.1 hq hq'
      simp only [hq', Bool.false_eq_true, if_false]
      by_cases e1 : q' = q
      · subst e1
        simp only [and_self, if_true, if_neg hsw.symm, add_zero]
        unfold haarVar; ring
      · by_cases e2 : q' = (q.1.swap, q.2)
        · subst e2
          have ho : onf q.1.swap = onf q.1 :=
            (onf_iff q.1 q.1.swap hq (by rw [inPlane_swap']; exact hq)).mpr (Or.inr rfl)
          rw [if_pos ⟨ho, rfl⟩, if_neg hsw, if_pos rfl]
          unfold haarVar; ring
        · have hc : ¬ (onf q'.1 = onf q.1 ∧ q'.2 = q.2) := by
            rintro ⟨ho, hy⟩
            rcases hiff.mp ho with h | h
            · exact e1 (Prod.ext h hy)
            · exact e2 (Prod.ext h hy)
          simp only [hc, if_false, if_neg e1, if_neg e2, add_zero]
  rw [Finset.sum_congr rfl (fun q' _ => hpt q'), Finset.sum_add_distrib, Finset.sum_add_distrib, sum_mixed,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

/-- **The mixed second moment at the decoupled end**, extent `≥ 3`:
`∫ S_mix² e^{−β S_in} = 8 n⁴ (8 n⁴ ⟨φ⟩² + 2 Var_Haar(φ)) ∫ e^{−β S_in}`. DERIVED: `8`, `4`, `2` as in
`sum_pair_weight`; `3` the least extent; `0` the decoupled end. -/
theorem mixSq_zero {n : ℕ} (hn : 3 ≤ n) (β : ℝ) :
    MixCutTest.mixSq N β 0 n = 8 * (n : ℝ) ^ 4
      * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N ^ 2 + 2 * haarVar N)
      * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hm : ∀ q : Pq n, Continuous fun U : Lk n → SUN.SU N =>
      if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U :=
    fun q => continuous_if_const _ (fun _ => continuous_const) (fun _ => continuous_plaq n q)
  have hint : ∀ F : (Lk n → SUN.SU N) → ℝ, Continuous F → Integrable F (piH N n) :=
    fun F hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e1 : ∀ U : Lk n → SUN.SU N, smixR N n U * smixR N n U * Real.exp (-(β * sinR N n U + 0 * smixR N n U))
      = ∑ q : Pq n, ∑ q' : Pq n, (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U)
          * (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else plaq N n q' U) * Real.exp (-(β * sinR N n U)) := by
    intro U
    simp only [zero_mul, add_zero]
    unfold smixR
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
  have hterm : ∀ q q' : Pq n,
      ∫ U, (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U)
          * (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else plaq N n q' U) * Real.exp (-(β * sinR N n U)) ∂piH N n
        = (if AnisoTorus.inPlane q.1 then (0 : ℝ) else if AnisoTorus.inPlane q'.1 then (0 : ℝ)
            else (if onf q'.1 = onf q.1 ∧ q'.2 = q.2 then haarSq N else WindowRead.haarMeanN N ^ 2))
          * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    intro q q'
    by_cases hq : AnisoTorus.inPlane q.1 = true
    · simp only [hq, if_true, zero_mul, integral_zero]
    · by_cases hq' : AnisoTorus.inPlane q'.1 = true
      · simp only [hq, hq', if_true, Bool.false_eq_true, if_false, mul_zero, zero_mul, integral_zero]
      · simp only [hq, hq', Bool.false_eq_true, if_false]
        exact integral_pair hn β q q' hq hq'
  unfold MixCutTest.mixSq
  simp only [e1]
  rw [integral_finsetSum _ (f := fun (q : Pq n) (U : Lk n → SUN.SU N) => ∑ q' : Pq n,
      (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U)
        * (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else plaq N n q' U) * Real.exp (-(β * sinR N n U)))
    (fun q _ => hint _ (continuous_finsetSum _ fun q' _ => ((hm q).mul (hm q')).mul hE))]
  have hrow : ∀ q : Pq n, ∫ U, ∑ q' : Pq n, (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U)
          * (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else plaq N n q' U) * Real.exp (-(β * sinR N n U)) ∂piH N n
        = (if AnisoTorus.inPlane q.1 then (0 : ℝ)
            else 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N ^ 2 + 2 * haarVar N)
          * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    intro q
    rw [integral_finsetSum _ (f := fun (q' : Pq n) (U : Lk n → SUN.SU N) =>
        (if AnisoTorus.inPlane q.1 then (0 : ℝ) else plaq N n q U)
          * (if AnisoTorus.inPlane q'.1 then (0 : ℝ) else plaq N n q' U) * Real.exp (-(β * sinR N n U)))
      (fun q' _ => hint _ (((hm q).mul (hm q')).mul hE))]
    simp only [hterm]
    rw [← Finset.sum_mul]
    by_cases hq : AnisoTorus.inPlane q.1 = true
    · simp only [hq, if_true, Finset.sum_const_zero]
    · simp only [hq, Bool.false_eq_true, if_false]
      rw [sum_pair_weight n q hq]
  simp only [hrow]
  rw [← Finset.sum_mul, sum_mixed]

/-- **The decoupled mixed variance is extensive and exact**: `Var_n(S_mix)(β, 0) = 16 n⁴ Var_Haar(φ)` on extent
`n ≥ 3`. Each of the `8 n⁴` mixed plaquettes is Haar and uncorrelated with every other plaquette except its own
reverse, which carries the same density. DERIVED: `16 = 2 · 8` the two orientations of each of the `8` mixed
ordered orientations per site; `4` the dimension; `3` the least extent; `0` the decoupled end. -/
theorem varMix_zero {n : ℕ} (hn : 3 ≤ n) (β : ℝ) :
    MixCutTest.varMix N β 0 n = 16 * (n : ℝ) ^ 4 * haarVar N := by
  have hZ : AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    rw [ZA_eq_int]; simp only [zero_mul, add_zero]
  have hZne : (∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n) ≠ 0 := by
    rw [← hZ]; exact (ZA_pos β 0 n).ne'
  unfold MixCutTest.varMix
  rw [mixSq_zero hn, meanMix_zero (by omega), hZ, mul_div_assoc, div_self hZne, mul_one]
  unfold haarVar
  ring

/-- **The variance difference vanishes at the decoupled end** for windows `w ≥ 2` (extent `2^w ≥ 4`):
`16 Var_n − Var_{2n} = 0` at `t = 0`. DERIVED: `16 = 2⁴` the copies; `2` the doubling and the least window with
extent `≥ 3`; `0` the decoupled end. -/
theorem varGap_zero (β : ℝ) {w : ℕ} (hw : 2 ≤ w) :
    16 * MixCutTest.varMix N β 0 (2 ^ w) - MixCutTest.varMix N β 0 (2 ^ (w + 1)) = 0 := by
  have h1 : 3 ≤ 2 ^ w :=
    le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hw)
  have h2 : 3 ≤ 2 ^ (w + 1) := le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [varMix_zero h1, varMix_zero h2]
  push_cast
  ring

/-- **The mixed cut energy is stationary at the decoupled end** for windows `w ≥ 2`:
`∂_{β_⊥} mixCut N β β_⊥ w = 0` at `β_⊥ = 0`. DERIVED: `2` the least window; `0` the decoupled end. -/
theorem hasDerivAt_mixCut_zero (β : ℝ) {w : ℕ} (hw : 2 ≤ w) :
    HasDerivAt (fun x => mixCut N β x w) 0 0 := by
  have h := MixCutTest.hasDerivAt_mixCut (N := N) β 0 w
  rwa [varGap_zero β hw] at h

end Variance

end MassGap.MixEqui

#print axioms MassGap.MixEqui.mixEquiUp_of_mixCutBound
#print axioms MassGap.MixEqui.mixEquiUp_of_varGap
#print axioms MassGap.MixEqui.noStallOnSegment_of_mixEquiUp
#print axioms MassGap.MixEqui.strongEnd_of_mixEquiUp
#print axioms MassGap.MixEqui.isOpen_seedUpTo
#print axioms MassGap.MixEqui.seedUpTo_mono
#print axioms MassGap.MixEqui.uniform_decay
#print axioms MassGap.MixEqui.mixEquiUp_of_noStallOnSegment
#print axioms MassGap.MixEqui.mixEquiUp_iff_noStall
#print axioms MassGap.MixEqui.integral_avg_gen
#print axioms MassGap.MixEqui.rshift_apply
#print axioms MassGap.MixEqui.ne_of_rot
#print axioms MassGap.MixEqui.finRotate2_ne
#print axioms MassGap.MixEqui.corner_comp
#print axioms MassGap.MixEqui.not_corner
#print axioms MassGap.MixEqui.base_sep
#print axioms MassGap.MixEqui.hol_gT_off
#print axioms MassGap.MixEqui.continuous_psiJ
#print axioms MassGap.MixEqui.continuous_psiI
#print axioms MassGap.MixEqui.plaq_eq_psiJ
#print axioms MassGap.MixEqui.plaq_eq_psiI
#print axioms MassGap.MixEqui.psiJ_gT
#print axioms MassGap.MixEqui.psiI_gT
#print axioms MassGap.MixEqui.mixed_of_blocks
#print axioms MassGap.MixEqui.pair_of_move
#print axioms MassGap.MixEqui.integral_diag
#print axioms MassGap.MixEqui.integral_pair_ne
#print axioms MassGap.MixEqui.onf_low
#print axioms MassGap.MixEqui.onf_iff
#print axioms MassGap.MixEqui.inPlane_swap'
#print axioms MassGap.MixEqui.swap_ne
#print axioms MassGap.MixEqui.plaq_swap
#print axioms MassGap.MixEqui.plaq_onf
#print axioms MassGap.MixEqui.integral_pair
#print axioms MassGap.MixEqui.sum_pair_weight
#print axioms MassGap.MixEqui.mixSq_zero
#print axioms MassGap.MixEqui.varMix_zero
#print axioms MassGap.MixEqui.varGap_zero
#print axioms MassGap.MixEqui.hasDerivAt_mixCut_zero
