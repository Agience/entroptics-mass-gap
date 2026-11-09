import Mathlib
import MassGap.TileGeometry
import MassGap.BlockCommute
import MassGap.LightCone
import MassGap.BlockGapDef

noncomputable section

/-!
# MassGap.TileSweep — the conversion from the tiling block gap to the transfer gap, proved

`BlockGapDef.WilsonConversion` asks the transfer gap at the rate `e^{−c₀ √γ s}` from a block-dynamics gap
`γ`. This module defines the block gap of the 16-colour tiling of `TileGeometry` and proves the conversion
for it, with an explicit `c₀ = 1/15552`, through the symmetrised colour sweep:

`detectability lemma (Detectability) → second-moment sweep gap → Chebyshev filter (SweepFilter.sweep_cov)
→ light cone (LightCone.cone) → TorusClusterAt → GapAt (HeatBathGapDecay.gapAt_of_torusClusterAt)`.

## The gap (`tileGap`, `gammaTile`)

`tileP β n j K`: the conditional expectation of the periodic Wilson measure given every link outside the
tiling box `K` (`BlockHeatBath.torusBlkCondExp` on `TileGeometry.tileBox`). `TilePoincare hN β n j c`: for
every periodic gauge-invariant `u` with `⟨u, 1⟩ = 0`, `c ⟨u, u⟩ ≤ Σ_K ⟨u − E_K u, u − E_K u⟩` — the Poincaré
(spectral-gap) inequality of the dynamics that resamples one tiling box from its conditional law.
`tileGapSet hN β n`: the `c ∈ [0, 1]` attained at all large extents; `tileGap = sSup`, and
`gammaTile hN s β = tileGap hN β (blockSide s β)`. The gap is capped at `1`: a function of one box's links
has `Σ_K ‖Q_K u‖² ≤ ‖u‖²`, so the true gap is at most `1` whenever such a function is not constant, and
the cap only fixes the value of the supremum when it would not be. `tileGapSet_nonempty`, `tileGap_nonneg`,
`tileGap_le_one`. The definition mentions the Wilson measure's block conditional expectations and nothing of
the transfer.

## What it gives

1. `tileSetting`: the block expectations of the tiling satisfy `LightCone.Setting` (self-adjoint, local
   off the plaquette neighbourhood `tileNb`, the identity up to null vectors on what does not read the box).
   `layer_tile`: each colour class is a `LightCone.Layer` (`BlockCommute.torusBlkCondExp_comm`,
   `TileGeometry.not_sharePlaq_of_col`).
2. `tile_sweep_gap`: `TilePoincare c` gives the second-moment gap of `S = R*R` at `δ = c/(80² + c)`
   (`Detectability.sweep_gap`, `80` from `TileGeometry.card_adj_le`).
3. `torusClusterAt_tile`: `TilePoincare c` for all large extents, `0 < c`, gives
   `TorusClusterAt τ p hN β (e^{−√δ/(96 n)})`: a sweep has `32` layers, each moving the potential
   `HeatBathLocal.psiL` by at most `3n` (`TileGeometry.psiL_nb_le`), so `⌊(2k − 1)/(96 n)⌋` sweeps fit
   between `θx` and the lag-`2k` shift of `x`; `sweep_cov` with `chebR δ 1 ≥ e^{√δ}` gives
   `torusConn ≤ 2e‖x‖² e^{−2k√δ/(96 n)}`.
4. `gapAt_tile`, `rate_le`, `gapAt_sSup`, and `tileConversion`: for every scale `s` with `s β ≤ 1` from `βUV`
   on, `BlockDynamicStep.ChebyshevConversion (periodicGaugeInvData τ 0 hN) (gammaTile hN s) s (1/15552) βUV`
   (`√δ ≥ √c/81` at `c ≤ 1`, `n = ⌈1/s⌉ ≤ 2/s`, `81 · 96 · 2 = 15552`).
5. `clay_continuum_of_tileDynamics`: `0 < gammaTile hN s β₀`, `TileBlockStep` (the block gap falls by at most
   `C s²` per dyadic step) with `(4/3) C (s β₀)² < 1`, `s ≤ 1` from `βUV` on, `ScaleDominatesRun`, and E, N, Y
   give `ClayRoutes.ClayContinuum`. The conversion is proved, not assumed.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index of the even-extent family and
`+ 1` its successor; `0` the reflection plane, the signs and the vacuum pairing; `1` the constant
observable, the gap cap and the unit sweep; `2` the even lag and the factor of the filter's endpoint;
`16` the colours, `32 = 2 · 16` the layers of `R*R`; `3` the box spread; `96 = 32 · 3`; `80 = 3⁴ − 1` the
neighbour count and `6400 = 80²`; `81² = 6561 ≥ 6400 + 1`; `15552 = 81 · 96 · 2`.
-/

namespace MassGap.TileSweep

open MassGap MassGap.KnabeCriterion MassGap.HeatBath MassGap.HeatBathLocal MassGap.HeatBathGapDecay
open MassGap.BlockHeatBath MassGap.BlockCommute MassGap.TileGeometry MassGap.Detectability
open MassGap.LightCone MassGap.PeriodicState
open MassGap.SUN (SU)
open Filter

variable {N : ℕ}

/-- The periodic gauge-invariant observables at extent index `j`.

DERIVED: `2 * j + 1` the index. -/
abbrev TE (N j : ℕ) : Type := ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))

/-! ## 1. The tiling dynamics and its gap -/

/-- **The tiling box expectation** `E_K`.

DERIVED: `2 * j + 1` the index. -/
def tileP (β : ℝ) (n j : ℕ) (K : Fin 4 → Fin (qT n (2 * j + 1 + 1))) : TE N j →ₗ[ℝ] TE N j :=
  torusBlkCondExp β (2 * j + 1) (tileBox n (2 * j + 1) K)

/-- **The plaquette neighbourhood of a box**: its links and the links sharing a plaquette with one of them.

DERIVED: `2 * j + 1` the index. -/
def tileNb (n j : ℕ) (K : Fin 4 → Fin (qT n (2 * j + 1 + 1))) :
    Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) :=
  {m | ∃ m'' ∈ tileBox n (2 * j + 1) K, m'' = m ∨ SharePlaq (bdT (2 * j + 1)) m'' m}

/-- **The Poincaré inequality of the tiling dynamics at one volume.**

DERIVED: `0` orthogonality to the constants. -/
def TilePoincare (hN : N ≠ 0) (β : ℝ) (n j : ℕ) (c : ℝ) : Prop :=
  ∀ u : TE N j, torusForm hN β j u (oneT j) = 0 →
    c * torusForm hN β j u u ≤ ∑ K, torusForm hN β j (u - tileP β n j K u) (u - tileP β n j K u)

/-- **The gaps attained at all large extents**, capped at `1`.

DERIVED: `0` the sign; `1` the cap. -/
def tileGapSet (hN : N ≠ 0) (β : ℝ) (n : ℕ) : Set ℝ :=
  {c | 0 ≤ c ∧ c ≤ 1 ∧ ∀ᶠ j in atTop, TilePoincare hN β n j c}

/-- **The tiling block gap** at coupling `β` and box side `n`.

DERIVED: no numeral. -/
def tileGap (hN : N ≠ 0) (β : ℝ) (n : ℕ) : ℝ := sSup (tileGapSet hN β n)

/-- **The tiling block gap at fixed physical block size.**

DERIVED: no numeral. -/
def gammaTile (hN : N ≠ 0) (s : ℝ → ℝ) (β : ℝ) : ℝ := tileGap hN β (BlockGapDef.blockSide s β)

/-- **The block step for the tiling gap.**

DERIVED: no numeral. -/
def TileBlockStep (hN : N ≠ 0) (s : ℝ → ℝ) (βUV C : ℝ) : Prop :=
  BlockDynamicStep.BlockStep (gammaTile hN s) s βUV C

/-- **The conversion for the tiling gap**, proved below (`tileConversion`).

DERIVED: `0` the reflection plane. -/
def TileConversion (τ : Fin 4) (hN : N ≠ 0) (s : ℝ → ℝ) (c₀ βUV : ℝ) : Prop :=
  BlockDynamicStep.ChebyshevConversion (fun β => periodicGaugeInvData τ 0 hN β) (gammaTile hN s) s c₀ βUV

/-- `0` is attained. DERIVED: `0` the attained gap. -/
theorem tileGapSet_nonempty (hN : N ≠ 0) (β : ℝ) (n : ℕ) : (0 : ℝ) ∈ tileGapSet hN β n := by
  refine ⟨le_rfl, zero_le_one, Filter.Eventually.of_forall (fun j u _ => ?_)⟩
  rw [zero_mul]
  exact Finset.sum_nonneg (fun K _ => torusForm_nonneg hN β j _)

#print axioms tileGapSet_nonempty

/-- DERIVED: `0` the sign. -/
theorem tileGap_nonneg (hN : N ≠ 0) (β : ℝ) (n : ℕ) : 0 ≤ tileGap hN β n :=
  Real.sSup_nonneg (fun _ hc => hc.1)

#print axioms tileGap_nonneg

/-- DERIVED: `1` the cap. -/
theorem tileGap_le_one (hN : N ≠ 0) (β : ℝ) (n : ℕ) : tileGap hN β n ≤ 1 :=
  csSup_le ⟨0, tileGapSet_nonempty hN β n⟩ (fun _ hc => hc.2.1)

#print axioms tileGap_le_one

/-! ## 2. The locality setting -/

/-- The box expectation fixes the constant observable.

DERIVED: `1` the constant. -/
theorem tileP_one (β : ℝ) (n j : ℕ) (K : Fin 4 → Fin (qT n (2 * j + 1 + 1))) :
    tileP (N := N) β n j K (oneT j) = oneT j := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show blkAvg (bdT (2 * j + 1)) β (tileBox n (2 * j + 1) K)
      (torusObs (2 * j + 1) (1 : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf (2 * j + 1) U) = 1
  rw [blkAvg_of_readsNot (bdT (2 * j + 1)) β _ (fun W V => rfl)]
  rfl

#print axioms tileP_one

/-- **The tiling expectations satisfy the light-cone setting.**

DERIVED: `2 * j + 1` the index. -/
theorem tileSetting (hN : N ≠ 0) (β : ℝ) (n j : ℕ) :
    LightCone.Setting (torusForm hN β j) (tileP (N := N) β n j)
      (fun m (x : TE N j) => ReadsNot j m (x : C(GibbsSpec.IConf (SU N), ℝ)))
      (fun K => (tileBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (tileNb n j) where
  symm := torusForm_symm hN β j
  psd := torusForm_nonneg hN β j
  sa K := torusBlkCondExp_selfAdj hN β j _
  far K x m hm hx :=
    torusBlkCondExp_readsNot_far β j _ (fun h => hm ⟨m, h, Or.inl rfl⟩)
      (fun p ⟨l, hl, hlp⟩ hmp => hm ⟨l, hl, Or.inr ⟨p, hlp, hmp⟩⟩) x hx
  keep_reads K x hx m hm := by
    have hk := torusBlkCondExp_keeps β j (tileBox n (2 * j + 1) K) x (fun l hl => hx l hl)
    intro W g
    show torusObs (2 * j + 1) ((tileP β n j K x : TE N j) : C(GibbsSpec.IConf (SU N), ℝ))
        (Function.update W m g)
      = torusObs (2 * j + 1) ((tileP β n j K x : TE N j) : C(GibbsSpec.IConf (SU N), ℝ)) W
    unfold tileP
    rw [hk]
    exact hm W g
  keep_null K x hx :=
    null_of_torusObs_eq hN β j _ _
      (torusBlkCondExp_keeps β j (tileBox n (2 * j + 1) K) x (fun l hl => hx l hl))
  box_sub K m hm := ⟨m, hm, Or.inl rfl⟩

#print axioms tileSetting

/-- Distinct boxes of one colour: no plaquette visiting the first contains a link of the second.

DERIVED: `2 * j + 1` the index. -/
theorem sep_of_col {n j : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ 2 * j + 1 + 1)
    {K K' : Fin 4 → Fin (qT n (2 * j + 1 + 1))} (hne : K ≠ K') (hc : tcol K = tcol K') :
    ∀ p, Visits (bdT (2 * j + 1)) (tileBox n (2 * j + 1) K) p →
      ∀ l ∈ tileBox n (2 * j + 1) K', l ∉ (bdT (2 * j + 1) p).map Prod.fst :=
  fun p ⟨_l₀, hl₀, hp₀⟩ _l hl hlp => not_sharePlaq_of_col hn hL hne hc hl₀ hl ⟨p, hp₀, hlp⟩

#print axioms sep_of_col

/-- **One colour class.**

DERIVED: `2` the parity. -/
def layerOf (n j : ℕ) (c : Fin 4 → Fin 2) : List (Fin 4 → Fin (qT n (2 * j + 1 + 1))) :=
  (Finset.univ.filter (fun K => tcol K = c)).toList

/-- **Each colour class is a layer.**

DERIVED: `2` the parity. -/
theorem layer_tile (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ 2 * j + 1 + 1)
    (c : Fin 4 → Fin 2) :
    Layer (tileP (N := N) β n j)
      (fun K => (tileBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (tileNb n j) (layerOf n j c) := by
  refine ⟨Finset.nodup_toList _, fun K hK K' hK' hne => ?_⟩
  have hcK : tcol K = c := (Finset.mem_filter.mp (Finset.mem_toList.mp hK)).2
  have hcK' : tcol K' = c := (Finset.mem_filter.mp (Finset.mem_toList.mp hK')).2
  have hcol : tcol K = tcol K' := hcK.trans hcK'.symm
  refine ⟨fun x => ?_, ?_⟩
  · exact torusBlkCondExp_comm β (2 * j + 1) (tileBox_disjoint hne)
      (sep_of_col hn hL hne hcol) (sep_of_col hn hL (Ne.symm hne) hcol.symm) x
  · rw [Set.disjoint_left]
    rintro m hm ⟨m'', hm'', hrel | hrel⟩
    · subst hrel
      exact Finset.disjoint_left.mp (tileBox_disjoint hne) hm'' hm
    · exact not_sharePlaq_of_col hn hL hne hcol hm'' hm hrel

#print axioms layer_tile

/-- A reversed layer is a layer.

DERIVED: no numeral. -/
theorem layer_reverse {E ι Λ : Type*} [AddCommGroup E] [Module ℝ E] {P : ι → E →ₗ[ℝ] E}
    {box nb : ι → Set Λ} {c : List ι} (h : Layer P box nb c) : Layer P box nb c.reverse :=
  ⟨List.nodup_reverse.mpr h.1, fun i hi j hj hij =>
    h.2 i (List.mem_reverse.mp hi) j (List.mem_reverse.mp hj) hij⟩

#print axioms layer_reverse

/-- **The sixteen colour classes**, in the order of `Finset.univ`.

DERIVED: `2` the parity; `4` the dimension. -/
def lays (n j : ℕ) : List (List (Fin 4 → Fin (qT n (2 * j + 1 + 1)))) :=
  (Finset.univ : Finset (Fin 4 → Fin 2)).toList.map (layerOf n j)

/-- **The sweep order** `R`: the colour classes one after another.

DERIVED: no numeral. -/
def tileList (n j : ℕ) : List (Fin 4 → Fin (qT n (2 * j + 1 + 1))) := (lays n j).flatten

/-- DERIVED: no numeral. -/
theorem tileList_nodup (n j : ℕ) : (tileList n j).Nodup := by
  refine List.nodup_flatten.mpr ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hl
    exact Finset.nodup_toList _
  · refine List.pairwise_map.mpr ((Finset.nodup_toList _).imp (fun {a b} hab => ?_))
    intro K hKa hKb
    have ha : tcol K = a := (Finset.mem_filter.mp (Finset.mem_toList.mp hKa)).2
    have hb : tcol K = b := (Finset.mem_filter.mp (Finset.mem_toList.mp hKb)).2
    exact hab (ha.symm.trans hb)

#print axioms tileList_nodup

/-- DERIVED: no numeral. -/
theorem mem_tileList (n j : ℕ) (K : Fin 4 → Fin (qT n (2 * j + 1 + 1))) : K ∈ tileList n j :=
  List.mem_flatten.mpr ⟨layerOf n j (tcol K),
    List.mem_map.mpr ⟨tcol K, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)⟩

#print axioms mem_tileList

/-- **The layers of `R*R`**: the colour classes, then the same classes reversed.

DERIVED: no numeral. -/
def swL (n j : ℕ) : List (List (Fin 4 → Fin (qT n (2 * j + 1 + 1)))) :=
  lays n j ++ ((lays n j).map List.reverse).reverse

/-- DERIVED: no numeral. -/
theorem flatten_swL (n j : ℕ) : (swL n j).flatten = tileList n j ++ (tileList n j).reverse := by
  unfold swL tileList
  rw [List.flatten_append, List.reverse_flatten]

#print axioms flatten_swL

/-- `R*R` has `32` layers.

DERIVED: `32 = 2 · 16`. -/
theorem length_swL (n j : ℕ) : (swL n j).length = 32 := by
  simp [swL, lays]

#print axioms length_swL

/-- Every layer of `R*R` is a layer.

DERIVED: no numeral. -/
theorem layer_swL (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ 2 * j + 1 + 1) :
    ∀ c ∈ swL n j, Layer (tileP (N := N) β n j)
      (fun K => (tileBox n (2 * j + 1) K : Set (WilsonHypercubic.Link 4 (2 * j + 1 + 1))))
      (tileNb n j) c := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨col, _, rfl⟩ := List.mem_map.mp h
    exact layer_tile β hn hL col
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
    obtain ⟨col, _, rfl⟩ := List.mem_map.mp hc'
    exact layer_reverse (layer_tile β hn hL col)

#print axioms layer_swL

/-- `Sⁱ` is the product along `i` copies of the layers of `R*R`.

DERIVED: no numeral. -/
theorem pow_word (n j i : ℕ) :
    ((List.replicate i (swL n j)).flatten).flatten
      = (List.replicate i (tileList n j ++ (tileList n j).reverse)).flatten := by
  rw [List.flatten_flatten, List.map_replicate, flatten_swL]

#print axioms pow_word

/-- DERIVED: `32` the layers per sweep. -/
theorem length_pow_layers (n j i : ℕ) : ((List.replicate i (swL n j)).flatten).length = i * 32 := by
  simp [length_swL]

#print axioms length_pow_layers

/-! ## 3. The sweep gap from the tiling gap -/

/-- **The second-moment gap of the sweep** from the tiling Poincaré inequality
(`Detectability.sweep_gap` with `g = 80`).

DERIVED: `80` the neighbour count; `2` its square; `1` the whole. -/
theorem tile_sweep_gap (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 2 * n ≤ 2 * j + 1 + 1)
    {c : ℝ} (hc : 0 ≤ c) (hP : TilePoincare hN β n j c) (u : TE N j)
    (hu : torusForm hN β j u (oneT j) = 0) :
    torusForm hN β j (seqLin (tileP β n j) (tileList n j ++ (tileList n j).reverse) u)
        (seqLin (tileP β n j) (tileList n j ++ (tileList n j).reverse) u)
      ≤ (1 - c / (((80 : ℕ) : ℝ) ^ 2 + c))
        * torusForm hN β j (seqLin (tileP β n j) (tileList n j ++ (tileList n j).reverse) u) u := by
  refine sweep_gap (torusForm hN β j) (tileP β n j) (TAdj n (2 * j + 1)) (torusForm_symm hN β j)
    (torusForm_nonneg hN β j) (fun K => torusBlkCondExp_selfAdj hN β j _)
    (fun K => torusBlkCondExp_idem β (2 * j + 1) _) ?_ 80 (card_adj_le hn hL) (card_adj_le' hn hL)
    (tileP_one β n j) hP (by positivity) (tileList n j) (tileList_nodup n j) (mem_tileList n j) u hu
  intro K K' hne hnadj x
  refine torusBlkCondExp_comm β (2 * j + 1) (tileBox_disjoint (Ne.symm hne)) ?_ ?_ x
  · intro p ⟨l₀, hl₀, hp₀⟩ l hl hlp
    exact hnadj ⟨hne, l₀, hl₀, l, hl, p, hp₀, hlp⟩
  · intro p ⟨l₀, hl₀, hp₀⟩ l hl hlp
    exact hnadj ⟨hne, l, hl, l₀, hl₀, p, hlp, hp₀⟩

#print axioms tile_sweep_gap

/-! ## 4. Clustering -/

/-- `B(f − ⟨f, v⟩v, f − ⟨f, v⟩v) = B(f, f) − ⟨f, v⟩²` at `⟨v, v⟩ = 1`.

DERIVED: `2` the square; `1` the normalisation. -/
theorem form_perp {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) {v : E} (hv : B v v = 1) (f : E) :
    B (f - B f v • v) (f - B f v • v) = B f f - B f v ^ 2 := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv]
  rw [hsymm v f]
  ring

#print axioms form_perp

/-- **The rate per lattice step is at least `e^{√δ}` per sweep**: `chebR δ 1 ≥ e^{√δ}`.

DERIVED: `1` the upper bound of the sweep. -/
theorem exp_le_chebR {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    Real.exp (Real.sqrt δ) ≤ ChebyshevFilter.chebR δ 1 := by
  rw [ChebyshevFilter.chebR_eq h0 h1, Real.sqrt_one]
  have hθ1 : Real.sqrt δ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt h0.le h1
  have hθ0 := Real.sqrt_nonneg δ
  rw [le_div_iff₀ (by linarith)]
  have h := Real.add_one_le_exp (-Real.sqrt δ)
  have he := Real.exp_pos (Real.sqrt δ)
  have hm : Real.exp (Real.sqrt δ) * Real.exp (-Real.sqrt δ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith

#print axioms exp_le_chebR

/-- **The tiling gap gives clustering.** See the module docstring, item 3.

DERIVED: `2` the even lag and the endpoint factor; `96 = 32 · 3` the potential per sweep; `6400 = 80²`;
`0` the signs; `4` the dimension. -/
theorem torusClusterAt_tile (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hP : ∀ᶠ j in atTop, TilePoincare hN β n j c) :
    TorusClusterAt τ p hN β (Real.exp (-(Real.sqrt (c / (6400 + c)) / (96 * n)))) := by
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
  have hδ0 : 0 < c / (6400 + c) := div_pos hc0 (by linarith)
  have hδ1 : c / (6400 + c) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hθ0 : 0 ≤ Real.sqrt (c / (6400 + c)) := Real.sqrt_nonneg _
  have hθ1 : Real.sqrt (c / (6400 + c)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hδ1.le
  refine ⟨2 * Real.exp 1 * ‖x‖ ^ 2, fun k => ?_⟩
  have hSg := isIGaugeInvariant_iterate_shift hxg τ (2 * k)
  filter_upwards [hP, Filter.eventually_ge_atTop (n + 2 * k + R + 1)] with j hPj hj
  have hL : 2 * n ≤ 2 * j + 1 + 1 := by omega
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
  set S := seqLin (tileP (N := N) β n j) (tileList n j ++ (tileList n j).reverse) with hS
  set d := (2 * k - 1) / (96 * n) with hd
  have hloc : ∀ i, i ≤ d → torusForm hN β j ((S ^ i) f) g = torusForm hN β j f g := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hipos
    · rw [h0, pow_zero, Module.End.one_apply]
    · rw [hS, seqLin_pow, ← pow_word]
      refine cone (tileSetting hN β n j) (psiL j τ (p - 1 - R) R) (3 * n)
        (fun K m hm m' ⟨m'', hm'', hrel⟩ => psiL_nb_le hn hL τ (p - 1 - R) R hm hm'' hrel)
        ((List.replicate i (swL n j)).flatten) ?_ 0 f g hfR ?_
      · intro c' hc'
        obtain ⟨l, hl, hc'l⟩ := List.mem_flatten.mp hc'
        rw [(List.mem_replicate.mp hl).2] at hc'l
        exact layer_swL β hn hL c' hc'l
      · intro m hm
        rw [length_pow_layers] at hm
        have hdk : 96 * n * d ≤ 2 * k - 1 := Nat.mul_div_le (2 * k - 1) (96 * n)
        have hid : 96 * n * i ≤ 96 * n * d := Nat.mul_le_mul_left _ hi
        have hn96 : 96 ≤ 96 * n * i := by nlinarith
        have e : 3 * n * (i * 32) = 96 * n * i := by ring
        rw [e] at hm
        refine readsNot_of_isLocalOn (isLocalOn_iterate_shift hTloc τ (2 * k)) j m (fun hmem => ?_)
        have := hCk m hmem
        omega
  -- the sweep gap and the filter
  have hgap : ∀ u : TE N j, torusForm hN β j u (oneT j) = 0 →
      torusForm hN β j (S u) (S u) ≤ (1 - c / (6400 + c)) * torusForm hN β j (S u) u := by
    intro u hu
    have h := tile_sweep_gap hN β hn hL hc0.le hPj u hu
    have e : ((80 : ℕ) : ℝ) ^ 2 = 6400 := by norm_num
    rw [e] at h
    exact h
  have hcov := SweepFilter.sweep_cov (torusForm_symm hN β j) (torusForm_nonneg hN β j)
    (seqLin_selfAdj (torusForm hN β j) (tileP β n j) (fun K => torusBlkCondExp_selfAdj hN β j _)
      (tileList n j))
    (seqLin_vac (tileP β n j) (tileP_one β n j) _) (torusForm_one_one hN β j) hδ0 hδ1 hgap d hloc
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
  set θ := Real.sqrt (c / (6400 + c)) with hθ
  set Rc := ChebyshevFilter.chebR (c / (6400 + c)) 1 with hRc
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
  -- `2k ≤ 96 n (d + 1)`
  have hk96 : (2 * k : ℝ) ≤ 96 * n * (d + 1) := by
    have h := Nat.lt_mul_div_succ (2 * k - 1) (show 0 < 96 * n by omega)
    have h' : 2 * k ≤ 96 * n * (d + 1) := by rw [hd]; omega
    exact_mod_cast h'
  have hn0 : (0 : ℝ) < 96 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hexp : Real.exp (-(d * θ))
      ≤ Real.exp 1 * Real.exp (-(θ / (96 * n))) ^ (2 * k) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (2 * k : ℝ) * θ ≤ 96 * n * (d + 1) * θ := mul_le_mul_of_nonneg_right hk96 hθ0
    have h2 : ((2 * k : ℕ) : ℝ) * (-(θ / (96 * n))) = -((2 * k : ℝ) * θ / (96 * n)) := by
      push_cast; ring
    rw [h2]
    have h3 : (2 * k : ℝ) * θ / (96 * n) ≤ (d + 1) * θ := by
      rw [div_le_iff₀ hn0]; linarith
    linarith
  calc t ≤ A * X := htA
    _ ≤ 2 * Real.exp (-(d * θ)) * X := mul_le_mul_of_nonneg_right hA2 hX0
    _ ≤ 2 * (Real.exp 1 * Real.exp (-(θ / (96 * n))) ^ (2 * k)) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hX0
    _ = 2 * Real.exp 1 * X * Real.exp (-(θ / (96 * n))) ^ (2 * k) := by ring

#print axioms torusClusterAt_tile

/-- **The tiling gap gives the transfer gap** at the rate of `torusClusterAt_tile`.

DERIVED: `96`, `6400` as there; `0` the sign of the rate. -/
theorem gapAt_tile (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hP : ∀ᶠ j in atTop, TilePoincare hN β n j c) :
    TransferGap.GapAt (periodicGaugeInvData τ p hN β)
      (Real.exp (-(Real.sqrt (c / (6400 + c)) / (96 * n)))) :=
  gapAt_of_torusClusterAt τ p hN β (Real.exp_pos _).le (torusClusterAt_tile τ p hN β hn hc0 hP)

#print axioms gapAt_tile

/-! ## 5. The conversion -/

/-- **The rate in `s`-units.** At `0 < c ≤ 1`, `0 < s ≤ 1`, `n ≤ 2/s`:
`e^{−√(c/(6400 + c))/(96 n)} ≤ e^{−√c s/15552}` (squared).

DERIVED: `15552 = 81 · 96 · 2`; `6561 = 81²`; `6400 = 80²`. -/
theorem rate_le {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {s : ℝ} (hs0 : 0 < s)
    (hns : (n : ℝ) ≤ 2 / s) :
    Real.exp (-(Real.sqrt (c / (6400 + c)) / (96 * n))) ^ 2
      ≤ Real.exp (-(1 / 15552 * Real.sqrt c * s)) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply pow_le_pow_left₀ (Real.exp_pos _).le _ 2
  apply Real.exp_le_exp.mpr
  have hsq : Real.sqrt c / 81 ≤ Real.sqrt (c / (6400 + c)) := by
    have h81 : Real.sqrt c / 81 = Real.sqrt (c / 6561) := by
      rw [Real.sqrt_div' c (by norm_num : (0 : ℝ) ≤ 6561),
        show (6561 : ℝ) = 81 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h81]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hc0.le (by linarith) (by linarith)
  have hsc := Real.sqrt_nonneg c
  have h96 : 96 * (n : ℝ) ≤ 192 / s := by
    have := mul_le_mul_of_nonneg_left hns (show (0 : ℝ) ≤ 96 by norm_num)
    calc 96 * (n : ℝ) ≤ 96 * (2 / s) := this
      _ = 192 / s := by ring
  have hpos : 0 < 96 * (n : ℝ) := by linarith
  have key : 1 / 15552 * Real.sqrt c * s ≤ Real.sqrt (c / (6400 + c)) / (96 * n) := by
    rw [le_div_iff₀ hpos]
    have h1 : 1 / 15552 * Real.sqrt c * s * (96 * n) ≤ 1 / 15552 * Real.sqrt c * s * (192 / s) :=
      mul_le_mul_of_nonneg_left h96 (by positivity)
    have hs192 : s * (192 / s) = 192 := by field_simp
    have h2 : 1 / 15552 * Real.sqrt c * s * (192 / s) = Real.sqrt c / 81 := by
      calc 1 / 15552 * Real.sqrt c * s * (192 / s) = 1 / 15552 * Real.sqrt c * (s * (192 / s)) := by
            ring
        _ = Real.sqrt c / 81 := by rw [hs192]; ring
    linarith
  linarith

#print axioms rate_le

/-- **The box side at scale `s ≤ 1` is at most `2/s`.**

DERIVED: `2`, `1`. -/
theorem blockSide_le {s : ℝ → ℝ} {β : ℝ} (hs0 : 0 < s β) (hs1 : s β ≤ 1) :
    1 ≤ BlockGapDef.blockSide s β ∧ (BlockGapDef.blockSide s β : ℝ) ≤ 2 / s β := by
  unfold BlockGapDef.blockSide
  have hinv : 1 ≤ 1 / s β := by rw [le_div_iff₀ hs0]; linarith
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (one_div_pos.mpr hs0)).ne', ?_⟩
  have h := Nat.ceil_lt_add_one (one_div_pos.mpr hs0).le
  have e : 2 / s β = 1 / s β + 1 / s β := by ring
  linarith

#print axioms blockSide_le

/-- **The gap at the supremum.** If every positive member `c` of a set of non-negative reals gives
`GapAt D (e^{−c₀ √c s})`, the supremum does.

DERIVED: `2` the square; `0` the signs. -/
theorem gapAt_sSup {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    (T : Set ℝ) (hne : T.Nonempty) (hT0 : ∀ c ∈ T, 0 ≤ c) {c₀ s : ℝ} (hc₀ : 0 ≤ c₀) (hs : 0 ≤ s)
    (h : ∀ c ∈ T, 0 < c → TransferGap.GapAt D (Real.exp (-(c₀ * Real.sqrt c * s)))) :
    TransferGap.GapAt D (Real.exp (-(c₀ * Real.sqrt (sSup T) * s))) := by
  intro x hx
  set Av := D.form (D.T x) (D.T x)
  set Xv := D.form x x
  have hAX : Av ≤ Xv := D.T_contract x
  have hX0 : 0 ≤ Xv := D.toReflForm.form_nonneg x
  have hA0 : 0 ≤ Av := D.toReflForm.form_nonneg (D.T x)
  have hsq : ∀ u : ℝ, Real.exp (-(c₀ * u * s)) ^ 2 = Real.exp (-(2 * (c₀ * s) * u)) := by
    intro u
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq]
  by_contra hlt
  rw [not_le] at hlt
  have hApos : 0 < Av := lt_of_le_of_lt (mul_nonneg (Real.exp_pos _).le hX0) hlt
  have hXpos : 0 < Xv := lt_of_lt_of_le hApos hAX
  set a := 2 * (c₀ * s) with ha
  have ha0 : 0 ≤ a := by positivity
  rcases eq_or_lt_of_le ha0 with ha00 | hapos
  · rw [← ha00, zero_mul, neg_zero, Real.exp_zero, one_mul] at hlt
    linarith
  set u := Real.log (Xv / Av) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hApos]; linarith)
  -- every positive member is at most `(u/a)²`
  have hbound : ∀ c ∈ T, c ≤ (u / a) ^ 2 := by
    intro c hc
    rcases eq_or_lt_of_le (hT0 c hc) with hc0 | hcpos
    · rw [← hc0]; positivity
    · have hg := h c hc hcpos x hx
      rw [hsq] at hg
      have h1 : Av / Xv ≤ Real.exp (-(a * Real.sqrt c)) := by
        rw [div_le_iff₀ hXpos]; exact hg
      have h2 : Real.log (Av / Xv) ≤ -(a * Real.sqrt c) := by
        rw [← Real.exp_le_exp, Real.exp_log (div_pos hApos hXpos)]; exact h1
      have h3 : Real.log (Av / Xv) = -u := by
        rw [hu, ← Real.log_inv, inv_div]
      have h4 : Real.sqrt c ≤ u / a := by
        rw [le_div_iff₀ hapos]; linarith
      calc c = Real.sqrt c ^ 2 := (Real.sq_sqrt hcpos.le).symm
        _ ≤ (u / a) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
  have hsup : sSup T ≤ (u / a) ^ 2 := csSup_le hne hbound
  have hsqrt : Real.sqrt (sSup T) ≤ u / a := by
    calc Real.sqrt (sSup T) ≤ Real.sqrt ((u / a) ^ 2) := Real.sqrt_le_sqrt hsup
      _ = u / a := Real.sqrt_sq (by positivity)
  have h5 : -u ≤ -(a * Real.sqrt (sSup T)) := by
    have := (le_div_iff₀ hapos).mp hsqrt
    linarith
  have h6 : Av / Xv ≤ Real.exp (-(a * Real.sqrt (sSup T))) := by
    calc Av / Xv = Real.exp (Real.log (Av / Xv)) := (Real.exp_log (div_pos hApos hXpos)).symm
      _ = Real.exp (-u) := by rw [hu, ← Real.log_inv, inv_div]
      _ ≤ _ := Real.exp_le_exp.mpr h5
  rw [div_le_iff₀ hXpos] at h6
  linarith

#print axioms gapAt_sSup

/-- **The conversion, proved.** For every scale `s` with `s β ≤ 1` from `βUV` on, the periodic transfer
has the gap `e^{−√(gammaTile β) s β / 15552}` at every `β ≥ βUV`.

DERIVED: `15552`; `1` the scale cap; `0` the reflection plane and the signs. -/
theorem tileConversion (τ : Fin 4) (hN : N ≠ 0) (s : ℝ → ℝ) (βUV : ℝ)
    (hs1 : ∀ β, βUV ≤ β → s β ≤ 1) : TileConversion τ hN s (1 / 15552) βUV := by
  intro β hβ
  rcases le_or_gt (s β) 0 with hs | hs
  · apply TransferGap.gapAt_of_one_le_sq
    have h0 : 0 ≤ -(1 / 15552 * Real.sqrt (gammaTile hN s β) * s β) := by
      have := Real.sqrt_nonneg (gammaTile hN s β)
      nlinarith
    have h1 : 1 ≤ Real.exp (-(1 / 15552 * Real.sqrt (gammaTile hN s β) * s β)) :=
      Real.one_le_exp h0
    nlinarith
  · obtain ⟨hn, hns⟩ := blockSide_le hs (hs1 β hβ)
    show TransferGap.GapAt (periodicGaugeInvData τ 0 hN β)
      (Real.exp (-(1 / 15552 * Real.sqrt (sSup (tileGapSet hN β (BlockGapDef.blockSide s β))) * s β)))
    refine gapAt_sSup _ _ ⟨0, tileGapSet_nonempty hN β _⟩ (fun c hc => hc.1) (by norm_num) hs.le
      (fun c hc hc0 => ?_)
    exact TransferGap.gapAt_mono (rate_le hn hc0 hc.2.1 hs hns)
      (gapAt_tile τ 0 hN β hn hc0 hc.2.2)

#print axioms tileConversion

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the tiling block dynamics.** The tiling block gap at one
coupling, its step along a scale function, `s ≤ 1` from `βUV` on, `ScaleDominatesRun`, and E, N, Y. The
conversion is `tileConversion`.

DERIVED: `2` the least rank; `0` the signs; `4` the spacetime dimension; `4/3` the budget; `15552` the
conversion constant; `1` the scale cap. -/
theorem clay_continuum_of_tileDynamics (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {s : ℝ → ℝ} {β₀ βUV C : ℝ} (hs : ScaleAlong.ScaleFunction s β₀) (hβ₀ : 0 < β₀)
    (hUVβ₀ : βUV ≤ β₀) (hg₀ : 0 < gammaTile hN s β₀) (hC : 0 ≤ C)
    (hCs : ∀ β, βUV ≤ β → C * s β ^ 2 ≤ 1) (hb : 4 / 3 * C * s β₀ ^ 2 < 1)
    (hs1 : ∀ β, βUV ≤ β → s β ≤ 1)
    (hstep : TileBlockStep hN s βUV C)
    (hdomR : ScaleAlong.ScaleDominatesRun s N)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  BlockDynamicStep.clay_continuum_of_blockDynamics hN2 hN Z τ hZ hB hL hs hβ₀ hUVβ₀ hg₀ hC hCs hb
    (by norm_num : (0 : ℝ) < 1 / 15552) hstep (tileConversion τ hN s βUV hs1) hdomR O G hconvK hY

#print axioms clay_continuum_of_tileDynamics

end MassGap.TileSweep
