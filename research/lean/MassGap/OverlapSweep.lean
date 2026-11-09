import Mathlib
import MassGap.OverlapGeometry
import MassGap.TileSweep

noncomputable section

/-!
# MassGap.OverlapSweep — the conversion for the overlapping block gap, and the tower with a linear loss

The tiling gap of `TileSweep` falls like `a/ℓ` at fixed physical box size (the free field's slow modes sit
on the box interfaces), so its block step fails. Boxes of two consecutive cells per direction
(`OverlapGeometry`) keep the gap bounded, with a correction of order `a/ℓ`. This module defines that gap,
proves the conversion to the transfer gap with an explicit constant, and closes the dyadic tower under a step
that allows a loss linear in the scale.

`detectability lemma (Detectability) → second-moment sweep gap → Chebyshev filter (SweepFilter.sweep_cov)
→ light cone (LightCone.cone) → TorusClusterAt → GapAt (HeatBathGapDecay.gapAt_of_torusClusterAt)`,
the same chain as `TileSweep`, with the overlapping geometry in place of the tiling.

## The gap (`overlapGap`, `gammaOverlap`)

`ovP β n j K`: the conditional expectation of the periodic Wilson measure given every link outside the
overlapping box `K` (`BlockHeatBath.torusBlkCondExp` on `OverlapGeometry.ovBox`). `OverlapPoincare hN β n j c`:
for every periodic gauge-invariant `u` with `⟨u, 1⟩ = 0`, `c ⟨u, u⟩ ≤ Σ_K ⟨u − E_K u, u − E_K u⟩`, the Poincaré
inequality of the dynamics that resamples one overlapping box from its conditional law. `overlapGapSet hN β n`:
the `c ∈ [0, 1]` attained at all large extents; `overlapGap = sSup` (`overlapGapSet_nonempty`,
`overlapGap_nonneg`, `overlapGap_le_one`), `gammaOverlap hN s β = overlapGap hN β (blockSide s β)`: cell side
`⌈1/s⌉`, box side twice that. The definition mentions the Wilson measure's block conditional expectations and
nothing of the transfer.

## What it gives

1. `ovSetting`, `layer_ov`: the overlapping boxes satisfy `LightCone.Setting`, and each of the 81 colour
   classes is a `LightCone.Layer` (`OverlapGeometry.not_near_of_ocol`).
2. `ov_sweep_gap`: `OverlapPoincare c` gives the second-moment gap of `S = R*R` at `δ = c/(624² + c)`
   (`Detectability.sweep_gap`, `624` from `OverlapGeometry.card_oadj_le`; boxes that are not adjacent are
   disjoint and share no plaquette, so their expectations commute exactly).
3. `torusClusterAt_ov`: `OverlapPoincare c` at all large extents, `0 < c`, gives
   `TorusClusterAt τ p hN β (e^{−√δ/(810 n)})`: a sweep has `162` layers, each moving the potential by at most
   `5n` (`OverlapGeometry.psiL_ov_le`).
4. `overlapConversion` (a theorem): for every scale `s` with `s β ≤ 1` from `βUV` on,
   `ChebyshevConversion (periodicGaugeInvData τ 0 hN) (gammaOverlap hN s) s (1/1012500) βUV`
   (`√δ ≥ √c/625` at `c ≤ 1`, `n ≤ 2/s`, `1012500 = 625 · 810 · 2`).
5. `BlockStepLin γ s βUV C`: `(1 − C s β) γ β ≤ γ β'` one dyadic step apart; `linBudget` (`Σ C s₀/2ⁱ ≤ 2 C s₀`),
   `gamma_eventually_ge_lin` (`γ ≥ γ β₀ (1 − 2 C s₀)` at every large `β`), `gapAt_eventually_of_blockStepLin`,
   `uniformPhysGapAlong_of_blockStepLin`, `clay_continuum_of_blockDynamicsLin`.
6. `clay_continuum_of_overlapDynamics`: `0 < gammaOverlap hN s β₀`, `OverlapBlockStep` (linear loss) with
   `2 C s β₀ < 1`, `s ≤ 1` from `βUV` on, `ScaleDominatesRun`, and E, N, Y give `ClayRoutes.ClayContinuum`.
   The conversion is proved, not assumed.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index of the even-extent family and
`+ 1` its successor; `0` the reflection plane, the signs and the vacuum pairing; `1` the constant observable,
the gap cap and the unit sweep; `2` the even lag, the endpoint factor and the geometric budget of a linear loss;
`81 = 3⁴` the colours, `162 = 2 · 81` the layers of `R*R`; `5` the box spread in cells; `810 = 162 · 5`;
`624 = 5⁴ − 1` the neighbour count and `389376 = 624²`; `625² = 390625 ≥ 389376 + 1`;
`1012500 = 625 · 810 · 2`; `3` the least cell count.
-/

namespace MassGap.OverlapSweep

open MassGap MassGap.KnabeCriterion MassGap.HeatBath MassGap.HeatBathLocal MassGap.HeatBathGapDecay
open MassGap.BlockHeatBath MassGap.BlockCommute MassGap.OverlapGeometry MassGap.Detectability
open MassGap.LightCone MassGap.PeriodicState MassGap.TileSweep
open MassGap.SUN (SU)
open Filter

variable {N : ℕ}

/-! ## 1. The overlapping dynamics and its gap -/

/-- **The overlapping box expectation** `E_K`.

DERIVED: `2 * j + 1` the index. -/
def ovP (β : ℝ) (n j : ℕ) (K : Fin 4 → Fin (qO n (2 * j + 1 + 1))) : TE N j →ₗ[ℝ] TE N j :=
  torusBlkCondExp β (2 * j + 1) (ovBox n (2 * j + 1) K)

/-- **The plaquette neighbourhood of a box.**

DERIVED: `2 * j + 1` the index. -/
def ovNb (n j : ℕ) (K : Fin 4 → Fin (qO n (2 * j + 1 + 1))) :
    Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :=
  {m | ∃ m'' ∈ ovBox n (2 * j + 1) K, m'' = m ∨ SharePlaq (bdT (2 * j + 1)) m'' m}

/-- **The Poincaré inequality of the overlapping dynamics at one volume.**

DERIVED: `0` orthogonality to the constants. -/
def OverlapPoincare (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (c : ℝ) : Prop :=
  ∀ u : TE N j, torusForm hN β j u (oneT j) = 0 →
    c * torusForm hN β j u u ≤ ∑ K, torusForm hN β j (u - ovP β n j K u) (u - ovP β n j K u)

/-- **The gaps attained at all large extents**, capped at `1`.

DERIVED: `0` the sign; `1` the cap. -/
def overlapGapSet (hN : N ≠ 0) (β : ℝ) (n : ℕ) : Set ℝ :=
  {c | 0 ≤ c ∧ c ≤ 1 ∧ ∀ᶠ j in atTop, OverlapPoincare hN β n j c}

/-- **The overlapping block gap** at coupling `β` and cell side `n` (box side `2n`).

DERIVED: no numeral. -/
def overlapGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) : ℝ := sSup (overlapGapSet hN β n)

/-- **The overlapping block gap at fixed physical size**: cell side `⌈1/s⌉`.

DERIVED: no numeral. -/
def gammaOverlap (hN : N ≠ 0) (s : ℝ → ℝ) (β : ℝ) : ℝ :=
  overlapGap hN β (BlockGapDef.blockSide s β)

/-- `0` is attained. DERIVED: `0` the attained gap. -/
theorem overlapGapSet_nonempty (hN : N ≠ 0) (β : ℝ) (n : ℕ) : (0 : ℝ) ∈ overlapGapSet hN β n := by
  refine ⟨le_rfl, zero_le_one, Filter.Eventually.of_forall (fun j u _ => ?_)⟩
  rw [zero_mul]
  exact Finset.sum_nonneg (fun K _ => torusForm_nonneg hN β j _)

#print axioms overlapGapSet_nonempty

/-- DERIVED: `0` the sign. -/
theorem overlapGap_nonneg (hN : N ≠ 0) (β : ℝ) (n : ℕ) : 0 ≤ overlapGap hN β n :=
  Real.sSup_nonneg (fun _ hc => hc.1)

#print axioms overlapGap_nonneg

/-- DERIVED: `1` the cap. -/
theorem overlapGap_le_one (hN : N ≠ 0) (β : ℝ) (n : ℕ) : overlapGap hN β n ≤ 1 :=
  csSup_le ⟨0, overlapGapSet_nonempty hN β n⟩ (fun _ hc => hc.2.1)

#print axioms overlapGap_le_one

/-! ## 2. The locality setting and the layers -/

/-- The box expectation fixes the constant observable.

DERIVED: `1` the constant. -/
theorem ovP_one (β : ℝ) (n j : ℕ) (K : Fin 4 → Fin (qO n (2 * j + 1 + 1))) :
    ovP (N := N) β n j K (oneT j) = oneT j := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT (2 * j + 1)) β (ovBox n (2 * j + 1) K)
      (torusObs (2 * j + 1) (1 : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf (2 * j + 1) U) = 1
  rw [blkAvg_of_readsNot (bdT (2 * j + 1)) β _ (fun W V => rfl)]
  rfl

#print axioms ovP_one

/-- **The overlapping expectations satisfy the light-cone setting.**

DERIVED: `2 * j + 1` the index. -/
theorem ovSetting (hN : N ≠ 0) (β : ℝ) (n j : ℕ) :
    LightCone.Setting (torusForm hN β j) (ovP (N := N) β n j)
      (fun m (x : TE N j) => ReadsNot j m (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (fun K => (ovBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (ovNb n j) where
  symm := torusForm_symm hN β j
  psd := torusForm_nonneg hN β j
  sa K := torusBlkCondExp_selfAdj hN β j _
  far K x m hm hx :=
    torusBlkCondExp_readsNot_far β j _ (fun h => hm ⟨m, h, Or.inl rfl⟩)
      (fun p ⟨l, hl, hlp⟩ hmp => hm ⟨l, hl, Or.inr ⟨p, hlp, hmp⟩⟩) x hx
  keep_reads K x hx m hm := by
    have hk := torusBlkCondExp_keeps β j (ovBox n (2 * j + 1) K) x (fun l hl => hx l hl)
    intro W g
    show torusObs (2 * j + 1) ((ovP β n j K x : TE N j) : C(GibbsSpec.IConf (SU N), ℝ))
        (Function.update W m g)
      = torusObs (2 * j + 1) ((ovP β n j K x : TE N j) : C(GibbsSpec.IConf (SU N), ℝ)) W
    unfold ovP
    rw [hk]
    exact hm W g
  keep_null K x hx :=
    null_of_torusObs_eq hN β j _ _
      (torusBlkCondExp_keeps β j (ovBox n (2 * j + 1) K) x (fun l hl => hx l hl))
  box_sub K m hm := ⟨m, hm, Or.inl rfl⟩

#print axioms ovSetting

/-- Distinct boxes of one colour: no plaquette visiting the first contains a link of the second.

DERIVED: `2 * j + 1` the index; `3` the colour modulus, `3 n ≤ L` giving at least three cells per
circle (`OverlapGeometry.three_le_qO`). -/
theorem sep_of_ocol {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    {K K' : Fin 4 → Fin (qO n (2 * j + 1 + 1))} (hne : K ≠ K') (hc : ocol K = ocol K') :
    ∀ p, Visits (bdT (2 * j + 1)) (ovBox n (2 * j + 1) K) p →
      ∀ l ∈ ovBox n (2 * j + 1) K', l ∉ (bdT (2 * j + 1) p).map Prod.fst :=
  fun p ⟨_l₀, hl₀, hp₀⟩ _l hl hlp =>
    not_near_of_ocol hn hL hne hc hl₀ hl (Or.inr ⟨p, hp₀, hlp⟩)

#print axioms sep_of_ocol

/-- **One colour class.**

DERIVED: `3` the colour modulus. -/
def layerOfO (n j : ℕ) (c : Fin 4 → Fin 3) : List (Fin 4 → Fin (qO n (2 * j + 1 + 1))) :=
  (Finset.univ.filter (fun K => ocol K = c)).toList

/-- **Each colour class is a layer.**

DERIVED: `3` the colour modulus. -/
theorem layer_ov (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1) (c : Fin 4 → Fin 3) :
    Layer (ovP (N := N) β n j)
      (fun K => (ovBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (ovNb n j) (layerOfO n j c) := by
  refine ⟨Finset.nodup_toList _, fun K hK K' hK' hne => ?_⟩
  have hcK : ocol K = c := (Finset.mem_filter.mp (Finset.mem_toList.mp hK)).2
  have hcK' : ocol K' = c := (Finset.mem_filter.mp (Finset.mem_toList.mp hK')).2
  have hcol : ocol K = ocol K' := hcK.trans hcK'.symm
  refine ⟨fun x => ?_, ?_⟩
  · exact torusBlkCondExp_comm β (2 * j + 1) (ovBox_disjoint_of_ocol hn hL hne hcol)
      (sep_of_ocol hn hL hne hcol) (sep_of_ocol hn hL (Ne.symm hne) hcol.symm) x
  · rw [Set.disjoint_left]
    rintro m hm ⟨m'', hm'', hrel⟩
    exact not_near_of_ocol hn hL hne hcol hm'' hm hrel

#print axioms layer_ov

/-- **The 81 colour classes**, in the order of `Finset.univ`.

DERIVED: `3` the colour modulus; `4` the dimension. -/
def laysO (n j : ℕ) : List (List (Fin 4 → Fin (qO n (2 * j + 1 + 1)))) :=
  (Finset.univ : Finset (Fin 4 → Fin 3)).toList.map (layerOfO n j)

/-- **The sweep order** `R`: the colour classes one after another.

DERIVED: no numeral. -/
def ovList (n j : ℕ) : List (Fin 4 → Fin (qO n (2 * j + 1 + 1))) := (laysO n j).flatten

/-- DERIVED: no numeral. -/
theorem ovList_nodup (n j : ℕ) : (ovList n j).Nodup := by
  refine List.nodup_flatten.mpr ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hl
    exact Finset.nodup_toList _
  · refine List.pairwise_map.mpr ((Finset.nodup_toList _).imp (fun {a b} hab => ?_))
    intro K hKa hKb
    have ha : ocol K = a := (Finset.mem_filter.mp (Finset.mem_toList.mp hKa)).2
    have hb : ocol K = b := (Finset.mem_filter.mp (Finset.mem_toList.mp hKb)).2
    exact hab (ha.symm.trans hb)

#print axioms ovList_nodup

/-- DERIVED: no numeral. -/
theorem mem_ovList (n j : ℕ) (K : Fin 4 → Fin (qO n (2 * j + 1 + 1))) : K ∈ ovList n j :=
  List.mem_flatten.mpr ⟨layerOfO n j (ocol K),
    List.mem_map.mpr ⟨ocol K, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)⟩

#print axioms mem_ovList

/-- **The layers of `R*R`**: the colour classes, then the same classes reversed.

DERIVED: no numeral. -/
def swLO (n j : ℕ) : List (List (Fin 4 → Fin (qO n (2 * j + 1 + 1)))) :=
  laysO n j ++ ((laysO n j).map List.reverse).reverse

/-- DERIVED: no numeral. -/
theorem flatten_swLO (n j : ℕ) : (swLO n j).flatten = ovList n j ++ (ovList n j).reverse := by
  unfold swLO ovList
  rw [List.flatten_append, List.reverse_flatten]

#print axioms flatten_swLO

/-- `R*R` has `162` layers.

DERIVED: `162 = 2 · 81`. -/
theorem length_swLO (n j : ℕ) : (swLO n j).length = 162 := by
  simp [swLO, laysO]

#print axioms length_swLO

/-- Every layer of `R*R` is a layer.

DERIVED: `3` the colour modulus, `3 n ≤ L` giving at least three cells per circle
(`OverlapGeometry.three_le_qO`). -/
theorem layer_swLO (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1) :
    ∀ c ∈ swLO n j, Layer (ovP (N := N) β n j)
      (fun K => (ovBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (ovNb n j) c := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨col, _, rfl⟩ := List.mem_map.mp h
    exact layer_ov β hn hL col
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
    obtain ⟨col, _, rfl⟩ := List.mem_map.mp hc'
    exact layer_reverse (layer_ov β hn hL col)

#print axioms layer_swLO

/-- `Sⁱ` is the product along `i` copies of the layers of `R*R`.

DERIVED: no numeral. -/
theorem pow_wordO (n j i : ℕ) :
    ((List.replicate i (swLO n j)).flatten).flatten
      = (List.replicate i (ovList n j ++ (ovList n j).reverse)).flatten := by
  rw [List.flatten_flatten, List.map_replicate, flatten_swLO]

#print axioms pow_wordO

/-- DERIVED: `162` the layers per sweep. -/
theorem length_pow_layersO (n j i : ℕ) :
    ((List.replicate i (swLO n j)).flatten).length = i * 162 := by
  simp [length_swLO]

#print axioms length_pow_layersO

/-! ## 3. The sweep gap from the overlapping gap -/

/-- **The second-moment gap of the sweep** from the overlapping Poincaré inequality
(`Detectability.sweep_gap` with `g = 624`).

DERIVED: `624` the neighbour count; `2` its square; `1` the whole; `3` the colour modulus, `3 n ≤ L`
giving at least three cells per circle (`OverlapGeometry.three_le_qO`). -/
theorem ov_sweep_gap (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    {c : ℝ} (hc : 0 ≤ c) (hP : OverlapPoincare hN β n j c) (u : TE N j)
    (hu : torusForm hN β j u (oneT j) = 0) :
    torusForm hN β j (seqLin (ovP β n j) (ovList n j ++ (ovList n j).reverse) u)
        (seqLin (ovP β n j) (ovList n j ++ (ovList n j).reverse) u)
      ≤ (1 - c / (((624 : ℕ) : ℝ) ^ 2 + c))
        * torusForm hN β j (seqLin (ovP β n j) (ovList n j ++ (ovList n j).reverse) u) u := by
  refine sweep_gap (torusForm hN β j) (ovP β n j) (OAdj n (2 * j + 1)) (torusForm_symm hN β j)
    (torusForm_nonneg hN β j) (fun K => torusBlkCondExp_selfAdj hN β j _)
    (fun K => torusBlkCondExp_idem β (2 * j + 1) _) ?_ 624 (card_oadj_le hn hL) (card_oadj_le' hn hL)
    (ovP_one β n j) hP (by positivity) (ovList n j) (ovList_nodup n j) (mem_ovList n j) u hu
  intro K K' hne hnadj x
  refine torusBlkCondExp_comm β (2 * j + 1) ?_ ?_ ?_ x
  · rw [Finset.disjoint_left]
    intro l hl hl'
    exact hnadj ⟨hne, l, hl, l, hl', Or.inl rfl⟩
  · intro p ⟨l₀, hl₀, hp₀⟩ l hl hlp
    exact hnadj ⟨hne, l₀, hl₀, l, hl, Or.inr ⟨p, hp₀, hlp⟩⟩
  · intro p ⟨l₀, hl₀, hp₀⟩ l hl hlp
    exact hnadj ⟨hne, l, hl, l₀, hl₀, Or.inr ⟨p, hlp, hp₀⟩⟩

#print axioms ov_sweep_gap

/-! ## 4. Clustering -/

/-- **The overlapping gap gives clustering.** See the module docstring, item 3.

DERIVED: `2` the even lag and the endpoint factor; `810 = 162 · 5` the potential per sweep;
`389376 = 624²`; `0` the signs; `3` the least cell count; `4` the dimension. -/
theorem torusClusterAt_ov (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hP : ∀ᶠ j in atTop, OverlapPoincare hN β n j c) :
    TorusClusterAt τ p hN β (Real.exp (-(Real.sqrt (c / (389376 + c)) / (810 * n)))) := by
  intro x hx
  obtain ⟨T, hTsub, hTloc⟩ := (Submodule.mem_inf.mp hx).1
  have hxg : GaugeInvariantAlgebra.IsIGaugeInvariant x := (Submodule.mem_inf.mp hx).2
  have hTp : ∀ l ∈ T, p ≤ l.2 τ := fun l hl => hTsub (Finset.mem_coe.mpr hl)
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ l ∈ T, l.2 τ ≤ p + R := by
    refine ⟨T.sup (fun l => (l.2 τ - p).toNat), fun l hl => ?_⟩
    have h1 : (l.2 τ - p).toNat ≤ T.sup (fun l => (l.2 τ - p).toNat) :=
      Finset.le_sup (f := fun l => (l.2 τ - p).toNat) hl
    have h2 : (((l.2 τ - p).toNat : ℕ) : ℤ) = l.2 τ - p :=
      Int.toNat_of_nonneg (by linarith [hTp l hl])
    omega
  have hθg := ContinuumField.isIGaugeInvariant_ireflObs hxg τ (2 * p)
  have hδ0 : 0 < c / (389376 + c) := div_pos hc0 (by linarith)
  have hδ1 : c / (389376 + c) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hθ0 : 0 ≤ Real.sqrt (c / (389376 + c)) := Real.sqrt_nonneg _
  have hθ1 : Real.sqrt (c / (389376 + c)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hδ1.le
  refine ⟨2 * Real.exp 1 * ‖x‖ ^ 2, fun k => ?_⟩
  have hSg := isIGaugeInvariant_iterate_shift hxg τ (2 * k)
  filter_upwards [hP, Filter.eventually_ge_atTop (3 * n + 2 * k + R + 1)] with j hPj hj
  have hL : 3 * n ≤ 2 * j + 1 + 1 := by omega
  -- the two observables
  set f : TE N j := ⟨LatticeReflection.ireflObs τ (2 * p) x,
    periodicGaugeInv_of_isIGaugeInvariant (2 * j + 1) hθg⟩ with hf
  set g : TE N j := ⟨(⇑(ReflectionShift.ishiftObsL τ))^[2 * k] x,
    periodicGaugeInv_of_isIGaugeInvariant (2 * j + 1) hSg⟩ with hg
  -- the potential vanishes on the reflected support
  have hA0 : ∀ a ∈ (T.image (LatticeReflection.ireflLink τ (2 * p))).image
      (InfiniteLattice.linkMod (2 * j + 1)), psiL j τ (p - 1 - R) R a = 0 := by
    intro a ha
    obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl1
    have hp0 := hTp l0 hl0
    have hr0 := hR l0 hl0
    have hz := ireflLink_coord τ (2 * p) l0
    have hb : p - 1 - (R : ℤ) ≤ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ
        ∧ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ ≤ p := by
      rw [hz]
      split_ifs <;> constructor <;> omega
    have h0 : 0 ≤ (LatticeReflection.ireflLink τ (2 * p) l0).2 τ - (p - 1 - R) := by omega
    have h1 : (LatticeReflection.ireflLink τ (2 * p) l0).2 τ - (p - 1 - R)
        < ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      omega
    have ht := Int.toNat_of_nonneg h0
    show psiT R (2 * j + 1)
        ((InfiniteLattice.finMod (2 * j + 1) ((LatticeReflection.ireflLink τ (2 * p) l0).2 τ)
          - InfiniteLattice.finMod (2 * j + 1) (p - 1 - R) : Fin (2 * j + 1 + 1)) : ℕ) = 0
    rw [off_eq (2 * j + 1) _ _ h0 h1]
    simp only [psiT, min_def]
    split_ifs <;> omega
  -- the potential is at least `2k` on the shifted support
  have hCk : ∀ c' ∈ (T.image ((InfiniteShift.ishiftLink τ)^[2 * k])).image
      (InfiniteLattice.linkMod (2 * j + 1)), 2 * k ≤ psiL j τ (p - 1 - R) R c' := by
    intro c' hc'
    obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hl1
    have hp0 := hTp l0 hl0
    have hr0 := hR l0 hl0
    have hz := ishiftLink_iterate_coord τ (2 * k) l0
    have h0 : 0 ≤ ((InfiniteShift.ishiftLink τ)^[2 * k] l0).2 τ - (p - 1 - R) := by omega
    have h1 : ((InfiniteShift.ishiftLink τ)^[2 * k] l0).2 τ - (p - 1 - R)
        < ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      omega
    have ht := Int.toNat_of_nonneg h0
    show 2 * k ≤ psiT R (2 * j + 1)
        ((InfiniteLattice.finMod (2 * j + 1) (((InfiniteShift.ishiftLink τ)^[2 * k] l0).2 τ)
          - InfiniteLattice.finMod (2 * j + 1) (p - 1 - R) : Fin (2 * j + 1 + 1)) : ℕ)
    rw [off_eq (2 * j + 1) _ _ h0 h1]
    simp only [psiT, min_def]
    split_ifs <;> omega
  -- reading sets
  have hfR : ReadsOnly (fun m (x : TE N j) => ReadsNot j m (x : C(GibbsSpec.IConf (SU N), ℝ)))
      {m | psiL j τ (p - 1 - R) R m ≤ 0} f := by
    intro m hm
    exact readsNot_of_isLocalOn (isLocalOn_ireflObs hTloc τ (2 * p)) j m
      (fun hmem => hm (hA0 m hmem).le)
  -- the light-cone identity at every power up to `d`
  set S := seqLin (ovP (N := N) β n j) (ovList n j ++ (ovList n j).reverse) with hS
  set d := (2 * k - 1) / (810 * n) with hd
  have hloc : ∀ i, i ≤ d → torusForm hN β j ((S ^ i) f) g = torusForm hN β j f g := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hipos
    · rw [h0, pow_zero, Module.End.one_apply]
    · rw [hS, seqLin_pow, ← pow_wordO]
      refine cone (ovSetting hN β n j) (psiL j τ (p - 1 - R) R) (5 * n)
        (fun K m hm m' ⟨m'', hm'', hrel⟩ => psiL_ov_le hn hL τ (p - 1 - R) R hm hm'' hrel)
        ((List.replicate i (swLO n j)).flatten) ?_ 0 f g hfR ?_
      · intro c' hc'
        obtain ⟨l, hl, hc'l⟩ := List.mem_flatten.mp hc'
        rw [(List.mem_replicate.mp hl).2] at hc'l
        exact layer_swLO β hn hL c' hc'l
      · intro m hm
        rw [length_pow_layersO] at hm
        have hdk : 810 * n * d ≤ 2 * k - 1 := Nat.mul_div_le (2 * k - 1) (810 * n)
        have hid : 810 * n * i ≤ 810 * n * d := Nat.mul_le_mul_left _ hi
        have hn810 : 810 ≤ 810 * n * i := by nlinarith
        have e : 5 * n * (i * 162) = 810 * n * i := by ring
        rw [e] at hm
        refine readsNot_of_isLocalOn (isLocalOn_iterate_shift hTloc τ (2 * k)) j m (fun hmem => ?_)
        have := hCk m hmem
        omega
  -- the sweep gap and the filter
  have hgap : ∀ u : TE N j, torusForm hN β j u (oneT j) = 0 →
      torusForm hN β j (S u) (S u) ≤ (1 - c / (389376 + c)) * torusForm hN β j (S u) u := by
    intro u hu
    have h := ov_sweep_gap hN β hn hL hc0.le hPj u hu
    have e : ((624 : ℕ) : ℝ) ^ 2 = 389376 := by norm_num
    rw [e] at h
    exact h
  have hcov := SweepFilter.sweep_cov (torusForm_symm hN β j) (torusForm_nonneg hN β j)
    (seqLin_selfAdj (torusForm hN β j) (ovP β n j) (fun K => torusBlkCondExp_selfAdj hN β j _)
      (ovList n j))
    (seqLin_vac (ovP β n j) (ovP_one β n j) _) (torusForm_one_one hN β j) hδ0 hδ1 hgap d hloc
  -- the connected pairing
  have hconn : MassGap.PeriodicReduce.torusConn τ p hN β j x (2 * k)
      = torusForm hN β j f g - torusForm hN β j f (oneT j) * torusForm hN β j (oneT j) g := by
    rw [torusForm_symm hN β j (oneT j) g, torusForm_one, torusForm_one]
    rfl
  have hff0 : torusState hN (2 * j + 1) β
      (LatticeReflection.ireflObs τ (2 * p) x * LatticeReflection.ireflObs τ (2 * p) x) ≤ ‖x‖ ^ 2 :=
    torusState_sq_le hN (2 * j + 1) β _ x (fun U => by
      rw [LatticeReflection.ireflObs_apply, ← Real.norm_eq_abs]
      exact x.norm_coe_le_norm _)
  have hgg0 : torusState hN (2 * j + 1) β
      ((⇑(ReflectionShift.ishiftObsL τ))^[2 * k] x * (⇑(ReflectionShift.ishiftObsL τ))^[2 * k] x)
        ≤ ‖x‖ ^ 2 :=
    torusState_sq_le hN (2 * j + 1) β _ x (fun U => by
      rw [ishiftObsL_iterate_apply, ← Real.norm_eq_abs]
      exact x.norm_coe_le_norm _)
  have hff : torusForm hN β j f f ≤ ‖x‖ ^ 2 := hff0
  have hgg : torusForm hN β j g g ≤ ‖x‖ ^ 2 := hgg0
  have hperp := form_perp (torusForm hN β j) (torusForm_symm hN β j) (torusForm_one_one hN β j) f
  rw [hperp] at hcov
  rw [hconn]
  -- the analytic chain
  set θ := Real.sqrt (c / (389376 + c)) with hθ
  set Rc := ChebyshevFilter.chebR (c / (389376 + c)) 1 with hRc
  set X := ‖x‖ ^ 2 with hX
  set t := torusForm hN β j f g - torusForm hN β j f (oneT j) * torusForm hN β j (oneT j) g with ht
  have hX0 : 0 ≤ X := sq_nonneg _
  have hRθ : Real.exp θ ≤ Rc := exp_le_chebR hδ0 hδ1
  have hRpos : 0 < Rc := lt_of_lt_of_le (Real.exp_pos _) hRθ
  have hRd : Real.exp (d * θ) ≤ Rc ^ d := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hRθ d
  set A := 2 / Rc ^ d with hA
  have hA0 : 0 ≤ A := div_nonneg (by norm_num) (pow_nonneg hRpos.le d)
  have hP0 : 0 ≤ torusForm hN β j f f - torusForm hN β j f (oneT j) ^ 2 := by
    rw [← hperp]; exact torusForm_nonneg hN β j _
  have hP1 : torusForm hN β j f f - torusForm hN β j f (oneT j) ^ 2 ≤ X := by
    nlinarith [sq_nonneg (torusForm hN β j f (oneT j))]
  have hQ0 := torusForm_nonneg hN β j g
  have ht2 : t ^ 2 ≤ (A * X) ^ 2 := by
    calc t ^ 2 ≤ A ^ 2 * (torusForm hN β j f f - torusForm hN β j f (oneT j) ^ 2)
          * torusForm hN β j g g := hcov
      _ ≤ A ^ 2 * X * X := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hP1 (sq_nonneg A)) hgg hQ0
            (mul_nonneg (sq_nonneg A) hX0)
      _ = (A * X) ^ 2 := by ring
  have htA : t ≤ A * X := by
    have := abs_le_of_sq_le_sq' ht2 (mul_nonneg hA0 hX0)
    exact this.2
  have hA2 : A ≤ 2 * Real.exp (-(d * θ)) := by
    rw [hA, Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hRd
  -- `2k ≤ 810 n (d + 1)`
  have hk810 : (2 * k : ℝ) ≤ 810 * n * (d + 1) := by
    have h := Nat.lt_mul_div_succ (2 * k - 1) (show 0 < 810 * n by omega)
    have h' : 2 * k ≤ 810 * n * (d + 1) := by rw [hd]; omega
    exact_mod_cast h'
  have hn0 : (0 : ℝ) < 810 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hexp : Real.exp (-(d * θ))
      ≤ Real.exp 1 * Real.exp (-(θ / (810 * n))) ^ (2 * k) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (2 * k : ℝ) * θ ≤ 810 * n * (d + 1) * θ := mul_le_mul_of_nonneg_right hk810 hθ0
    have h2 : ((2 * k : ℕ) : ℝ) * (-(θ / (810 * n))) = -((2 * k : ℝ) * θ / (810 * n)) := by
      push_cast; ring
    rw [h2]
    have h3 : (2 * k : ℝ) * θ / (810 * n) ≤ (d + 1) * θ := by
      rw [div_le_iff₀ hn0]; linarith
    linarith
  calc t ≤ A * X := htA
    _ ≤ 2 * Real.exp (-(d * θ)) * X := mul_le_mul_of_nonneg_right hA2 hX0
    _ ≤ 2 * (Real.exp 1 * Real.exp (-(θ / (810 * n))) ^ (2 * k)) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hX0
    _ = 2 * Real.exp 1 * X * Real.exp (-(θ / (810 * n))) ^ (2 * k) := by ring

#print axioms torusClusterAt_ov

/-- **The overlapping gap gives the transfer gap** at the rate of `torusClusterAt_ov`.

DERIVED: `810`, `389376` as there; `0` the sign of the rate. -/
theorem gapAt_ov (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hP : ∀ᶠ j in atTop, OverlapPoincare hN β n j c) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β)
      (Real.exp (-(Real.sqrt (c / (389376 + c)) / (810 * n)))) :=
  gapAt_of_torusClusterAt τ p hN β (Real.exp_pos _).le (torusClusterAt_ov τ p hN β hn hc0 hP)

#print axioms gapAt_ov

/-! ## 5. The conversion -/

/-- **The rate in `s`-units.** At `0 < c ≤ 1`, `0 < s`, `n ≤ 2/s`:
`e^{−√(c/(389376 + c))/(810 n)} ≤ e^{−√c s/1012500}` (squared).

DERIVED: `1012500 = 625 · 810 · 2`; `390625 = 625²`; `389376 = 624²`; `1620 = 810 · 2`. -/
theorem rate_le_ov {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {s : ℝ} (hs0 : 0 < s)
    (hns : (n : ℝ) ≤ 2 / s) :
    Real.exp (-(Real.sqrt (c / (389376 + c)) / (810 * n))) ^ 2
      ≤ Real.exp (-(1 / 1012500 * Real.sqrt c * s)) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply pow_le_pow_left₀ (Real.exp_pos _).le _ 2
  apply Real.exp_le_exp.mpr
  have hsq : Real.sqrt c / 625 ≤ Real.sqrt (c / (389376 + c)) := by
    have h625 : Real.sqrt c / 625 = Real.sqrt (c / 390625) := by
      rw [Real.sqrt_div' c (by norm_num : (0 : ℝ) ≤ 390625),
        show (390625 : ℝ) = 625 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h625]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hc0.le (by linarith) (by linarith)
  have hsc := Real.sqrt_nonneg c
  have h810 : 810 * (n : ℝ) ≤ 1620 / s := by
    have := mul_le_mul_of_nonneg_left hns (show (0 : ℝ) ≤ 810 by norm_num)
    calc 810 * (n : ℝ) ≤ 810 * (2 / s) := this
      _ = 1620 / s := by ring
  have hpos : 0 < 810 * (n : ℝ) := by linarith
  have key : 1 / 1012500 * Real.sqrt c * s ≤ Real.sqrt (c / (389376 + c)) / (810 * n) := by
    rw [le_div_iff₀ hpos]
    have h1 : 1 / 1012500 * Real.sqrt c * s * (810 * n)
        ≤ 1 / 1012500 * Real.sqrt c * s * (1620 / s) :=
      mul_le_mul_of_nonneg_left h810 (by positivity)
    have hs1620 : s * (1620 / s) = 1620 := by field_simp
    have h2 : 1 / 1012500 * Real.sqrt c * s * (1620 / s) = Real.sqrt c / 625 := by
      calc 1 / 1012500 * Real.sqrt c * s * (1620 / s)
            = 1 / 1012500 * Real.sqrt c * (s * (1620 / s)) := by ring
        _ = Real.sqrt c / 625 := by rw [hs1620]; ring
    linarith
  linarith

#print axioms rate_le_ov

/-- **The conversion for the overlapping gap.**

DERIVED: `0` the reflection plane. -/
def OverlapConversion (τ : Fin 4) (hN : N ≠ 0) (s : ℝ → ℝ) (c₀ βUV : ℝ) : Prop :=
  BlockDynamicStep.ChebyshevConversion (fun β => periodicGaugeInvData τ 0 hN β) (gammaOverlap hN s) s c₀ βUV

/-- **The conversion, proved.** For every scale `s` with `s β ≤ 1` from `βUV` on, the periodic transfer
has the gap `e^{−√(gammaOverlap β) s β / 1012500}` at every `β ≥ βUV`.

DERIVED: `1012500`; `1` the scale cap; `0` the reflection plane and the signs. -/
theorem overlapConversion (τ : Fin 4) (hN : N ≠ 0) (s : ℝ → ℝ) (βUV : ℝ)
    (hs1 : ∀ β, βUV ≤ β → s β ≤ 1) : OverlapConversion τ hN s (1 / 1012500) βUV := by
  intro β hβ
  rcases le_or_gt (s β) 0 with hs | hs
  · apply TransferGap.gapAt_of_one_le_sq
    have h0 : 0 ≤ -(1 / 1012500 * Real.sqrt (gammaOverlap hN s β) * s β) := by
      have := Real.sqrt_nonneg (gammaOverlap hN s β)
      nlinarith
    have h1 : 1 ≤ Real.exp (-(1 / 1012500 * Real.sqrt (gammaOverlap hN s β) * s β)) :=
      Real.one_le_exp h0
    nlinarith
  · obtain ⟨hn, hns⟩ := blockSide_le hs (hs1 β hβ)
    show TransferGap.GapAt (periodicGaugeInvData τ 0 hN β)
      (Real.exp (-(1 / 1012500 * Real.sqrt (sSup (overlapGapSet hN β (BlockGapDef.blockSide s β)))
        * s β)))
    refine gapAt_sSup _ _ ⟨0, overlapGapSet_nonempty hN β _⟩ (fun c hc => hc.1) (by norm_num) hs.le
      (fun c hc hc0 => ?_)
    exact TransferGap.gapAt_mono (rate_le_ov hn hc0 hc.2.1 hs hns)
      (gapAt_ov τ 0 hN β hn hc0 hc.2.2)

#print axioms overlapConversion

/-! ## 6. The tower with a loss linear in the scale -/

/-- **The block step with a linear loss**: one dyadic step apart, the gap falls by at most the fraction
`C s β`.

DERIVED: `2` the block factor. -/
def BlockStepLin (γ s : ℝ → ℝ) (βUV C : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → s β / 2 ≤ s β' → s β' ≤ s β →
    (1 - C * s β) * γ β ≤ γ β'

/-- **The linear losses along the dyadic tower sum to at most `2 C a₀`.**

DERIVED: `2` the geometric ratio's inverse and the budget. -/
theorem linBudget {C a₀ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a₀) (n : ℕ) :
    ∑ i ∈ Finset.range n, C * (a₀ / 2 ^ i) ≤ 2 * C * a₀ := by
  have hterm : ∀ i : ℕ, C * (a₀ / 2 ^ i) = C * a₀ * (1 / 2) ^ i := by
    intro i
    rw [one_div_pow, div_eq_mul_one_div a₀ (2 ^ i)]
    ring
  have hgeom : ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i ≤ 2 := by
    have h := geom_sum_eq (show ((1 : ℝ) / 2) ≠ 1 by norm_num) n
    rw [h]
    have hp : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  calc ∑ i ∈ Finset.range n, C * (a₀ / 2 ^ i)
        = C * a₀ * ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ C * a₀ * 2 := mul_le_mul_of_nonneg_left hgeom (mul_nonneg hC ha)
    _ = 2 * C * a₀ := by ring

#print axioms linBudget

/-- **The block-dynamics gap stays up along the tower under a linear loss.** At every large `β`,
`γ β ≥ γ β₀ (1 − 2 C s β₀)`.

DERIVED: `2` the budget and the block factor; `0`, `1` the signs and the whole gap. -/
theorem gamma_eventually_ge_lin {γ s : ℝ → ℝ} {β₀ βUV C : ℝ} (hs : ScaleAlong.ScaleFunction s β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 ≤ γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1)
    (hstep : BlockStepLin γ s βUV C) :
    ∀ᶠ β in atTop, γ β₀ * (1 - 2 * C * s β₀) ≤ γ β := by
  have hs₀ := hs.pos β₀ le_rfl
  set g₀ := γ β₀ with hg₀def
  have hgex : ∀ i : ℕ, ∃ g : ℝ, β₀ ≤ g ∧ s g = s β₀ / 2 ^ (i + 1) := by
    intro i
    have hlt : s β₀ / 2 ^ (i + 1) < s β₀ :=
      div_lt_self hs₀ (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i))
    exact hs.reach _ (div_pos hs₀ (by positivity)) hlt
  choose g hgβ hg using hgex
  obtain ⟨σ, hσ0, hσβ, hσ⟩ : ∃ σ : ℕ → ℝ, σ 0 = β₀ ∧ (∀ i : ℕ, β₀ ≤ σ i) ∧
      ∀ i : ℕ, s (σ i) = s β₀ / 2 ^ i :=
    ⟨(fun i => match i with | 0 => β₀ | k + 1 => g k),
     rfl,
     fun i => by
      cases i with
      | zero => exact le_rfl
      | succ k => exact hgβ k,
     fun i => by
      cases i with
      | zero =>
        show s β₀ = s β₀ / 2 ^ 0
        rw [pow_zero, div_one]
      | succ k =>
        show s (g k) = s β₀ / 2 ^ (k + 1)
        exact hg k⟩
  have hxn : ∀ i : ℕ, 0 ≤ C * (s β₀ / 2 ^ i) := fun i =>
    mul_nonneg hC (div_nonneg hs₀.le (by positivity))
  -- the clipped chain along the exact halvings
  have hchain : ∀ n : ℕ, g₀ - (∑ i ∈ Finset.range n, C * (s β₀ / 2 ^ i)) * g₀
      ≤ min (γ (σ n)) g₀ := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, sub_zero]
      rw [hσ0]
      exact le_min le_rfl le_rfl
    | succ n ih =>
      have hx1 : C * (s β₀ / 2 ^ n) ≤ 1 := by
        have := hCs (σ n) (hUVβ₀.trans (hσβ n))
        rwa [hσ n] at this
      have hst := hstep (σ n) (σ (n + 1)) (hUVβ₀.trans (hσβ n)) (hUVβ₀.trans (hσβ (n + 1)))
        (le_of_eq (by rw [hσ n, hσ (n + 1), pow_succ, div_div]))
        (by
          rw [hσ n, hσ (n + 1), pow_succ, ← div_div]
          have hnn : 0 ≤ s β₀ / 2 ^ n := div_nonneg hs₀.le (by positivity)
          linarith)
      rw [hσ n] at hst
      have h := BlockDynamicStep.clip_step (hxn n) hx1 hg₀ ih hst
      rw [Finset.sum_range_succ]
      linarith
  filter_upwards [hs.eventually_le, Filter.eventually_ge_atTop βUV] with β hβs hβUV
  obtain ⟨ha, hβa⟩ := hβs
  have hex : ∃ n : ℕ, s β₀ / 2 ^ (n + 1) < s β := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s β₀ / s β) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ ha] at hn
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1)), pow_succ]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith [hn, mul_pos h2n ha]
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, s β₀ / 2 ^ (n + 1) < s β ∧
      ∀ k : ℕ, k < n → ¬ (s β₀ / 2 ^ (k + 1) < s β) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hle : s β ≤ s β₀ / 2 ^ n := by
    cases n with
    | zero =>
      rw [pow_zero, div_one]
      exact hβa
    | succ k => exact not_lt.mp (hmin k (Nat.lt_succ_self k))
  have hlast := hstep (σ n) β (hUVβ₀.trans (hσβ n)) hβUV
    (by
      rw [hσ n, div_div, ← pow_succ]
      exact hn.le)
    (by
      rw [hσ n]
      exact hle)
  rw [hσ n] at hlast
  have hx1 : C * (s β₀ / 2 ^ n) ≤ 1 := by
    have := hCs (σ n) (hUVβ₀.trans (hσβ n))
    rwa [hσ n] at this
  have hfin := BlockDynamicStep.clip_step (hxn n) hx1 hg₀ (hchain n) hlast
  have hsum := linBudget hC hs₀.le (n + 1)
  rw [Finset.sum_range_succ] at hsum
  have hmul := mul_le_mul_of_nonneg_right hsum hg₀
  have : g₀ - (∑ i ∈ Finset.range n, C * (s β₀ / 2 ^ i)) * g₀ - C * (s β₀ / 2 ^ n) * g₀
      ≤ γ β := hfin.trans (min_le_left _ _)
  nlinarith [this, hmul]

#print axioms gamma_eventually_ge_lin

section Transfer

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The transfer gap at a uniform rate in `s`-units, linear loss.**

DERIVED: `2` the budget; `0` the signs. -/
theorem gapAt_eventually_of_blockStepLin (D : ℝ → Transfer.TransferData A) {γ s : ℝ → ℝ}
    {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 ≤ γ β₀)
    (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1) (hc₀ : 0 ≤ c₀)
    (hstep : BlockStepLin γ s βUV C) (hconv : BlockDynamicStep.ChebyshevConversion D γ s c₀ βUV) :
    ∀ᶠ β in atTop, TransferGap.GapAt (D β)
      (Real.exp (-(c₀ * Real.sqrt (γ β₀ * (1 - 2 * C * s β₀)) * s β))) := by
  filter_upwards [gamma_eventually_ge_lin hs hUVβ₀ hg₀ hC hCs hstep, hs.eventually_le,
    Filter.eventually_ge_atTop βUV] with β hγ hsβ hβ
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ (hconv β hβ)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have hsq := Real.sqrt_le_sqrt hγ
  have h1 := mul_le_mul_of_nonneg_left hsq hc₀
  exact mul_le_mul_of_nonneg_right h1 hsβ.1.le

#print axioms gapAt_eventually_of_blockStepLin

end Transfer

/-- **The uniform physical gap along `s` from the block dynamics, linear loss.**

DERIVED: `2` the least rank and the budget; `0`, `1` the signs. -/
theorem uniformPhysGapAlong_of_blockStepLin (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {γ s : ℝ → ℝ} {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1)
    (hb : 2 * C * s β₀ < 1) (hc₀ : 0 < c₀)
    (hstep : BlockStepLin γ s βUV C)
    (hconv : BlockDynamicStep.ChebyshevConversion
      (fun β => PeriodicState.periodicGaugeInvData τ p hN β) γ s c₀ βUV) :
    ConstantPhysics.UniformPhysGapAlong τ p hN s := by
  set M := c₀ * Real.sqrt (γ β₀ * (1 - 2 * C * s β₀)) with hM
  have hMpos : 0 < M := mul_pos hc₀ (Real.sqrt_pos.mpr (mul_pos hg₀ (by linarith)))
  refine ⟨M, hMpos, ?_⟩
  filter_upwards [gapAt_eventually_of_blockStepLin _ hs hUVβ₀ hg₀.le hC hCs hc₀.le hstep hconv,
    hs.eventually_le, Filter.eventually_ge_atTop β₀] with β hg hsβ hββ
  obtain ⟨hpos, _⟩ := hsβ
  have hβ0 : 0 ≤ β := (hβ₀.trans_le hββ).le
  have hr0 : 0 < Real.exp (-(M * s β)) := Real.exp_pos _
  have hr1 : Real.exp (-(M * s β)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ0 hr0 hr1 hg, ?_⟩
  rw [Real.log_exp, neg_neg, mul_div_assoc, div_self hpos.ne', mul_one]

#print axioms uniformPhysGapAlong_of_blockStepLin

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from a block dynamics with a linear-loss step.**

DERIVED: `2` the least rank and the budget; `0` the reflection plane and the signs; `4` the spacetime
dimension; `1` the least colour count. -/
theorem clay_continuum_of_blockDynamicsLin (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {γ s : ℝ → ℝ} {β₀ βUV C c₀ : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < γ β₀) (hC : 0 ≤ C) (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1)
    (hb : 2 * C * s β₀ < 1) (hc₀ : 0 < c₀)
    (hstep : BlockStepLin γ s βUV C)
    (hconv : BlockDynamicStep.ChebyshevConversion
      (fun β => PeriodicState.periodicGaugeInvData τ 0 hN β) γ s c₀ βUV)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hS := uniformPhysGapAlong_of_blockStepLin τ 0 hN2 hN hs hβ₀ hUVβ₀ hg₀ hC hCs hb hc₀ hstep hconv
  obtain ⟨κ, hκ, hdom⟩ := hdomR
  have hR : ConstantPhysics.UniformPhysGapAlong τ 0 hN (AsymptoticScaling.aRun N) :=
    ScaleAlong.uniformPhysGapAlong_of_dominates τ 0 hN hκ hdom
      (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
      (hs.eventually_le.mono (fun _ h => h.1)) hS
  have hW : WeakCouplingWindow.FixedWindowDecay τ 0 hN L :=
    (ConstantPhysics.fixedWindowDecayAlong_aRun τ 0 hN L).mp
      (ConstantPhysics.fixedWindowDecayAlong_of_uniformPhysGapAlong τ 0 hN hL
        (Filter.eventually_gt_atTop (0 : ℝ) |>.mono (fun _ h => AsymptoticScaling.aRun_pos hN1 h))
        (fun b hb => WeakCouplingWindow.eventually_aRun_le hN1 hb) hR)
  exact ClayRoutes.clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL hW O G hconvK hY

#print axioms clay_continuum_of_blockDynamicsLin

/-- **The block step for the overlapping gap**, linear loss.

DERIVED: no numeral. -/
def OverlapBlockStep (hN : N ≠ 0) (s : ℝ → ℝ) (βUV C : ℝ) : Prop :=
  BlockStepLin (gammaOverlap hN s) s βUV C

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the overlapping block dynamics.** The overlapping block gap at one
coupling, its linear-loss step along a scale function with `2 C s β₀ < 1`, `s ≤ 1` from `βUV` on,
`ScaleDominatesRun`, and E, N, Y. The conversion is `overlapConversion`.

DERIVED: `2` the least rank and the budget; `0` the signs; `4` the spacetime dimension; `1012500` the
conversion constant; `1` the scale cap. -/
theorem clay_continuum_of_overlapDynamics (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {s : ℝ → ℝ} {β₀ βUV C : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < gammaOverlap hN s β₀) (hC : 0 ≤ C)
    (hCs : ∀ β, βUV ≤ β → C * s β ≤ 1) (hb : 2 * C * s β₀ < 1)
    (hs1 : ∀ β, βUV ≤ β → s β ≤ 1)
    (hstep : OverlapBlockStep hN s βUV C)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_blockDynamicsLin hN2 hN Z τ hZ hB hL hs hβ₀ hUVβ₀ hg₀ hC hCs hb
    (by norm_num : (0 : ℝ) < 1 / 1012500) hstep (overlapConversion τ hN s βUV hs1) hdomR O G hconvK hY

#print axioms clay_continuum_of_overlapDynamics

end MassGap.OverlapSweep
