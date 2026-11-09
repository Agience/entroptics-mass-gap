import Mathlib
import MassGap.DSOllivier

noncomputable section

/-!
# MassGap.DSBoxFloor — the Dobrushin–Shlosman box criterion gives the overlapping floor

One box `V` of side `L` at one coupling, the outside frozen; `C l k` its influence matrix (`DSBlockContract.BlkInfl`
for the Wilson block average of `V`, in a link-independent continuous separating metric cost). The criterion is
`DSBoxInfluence`: per link direction `μ`, the box average of the summed outside influence is at most `ρ`,
`Σ_{x : (μ,x) ∈ V} Σ_{k ∉ V} C (μ,x) k ≤ ρ · #{x : (μ,x) ∈ V}`. It names one coupling, one torus extent, and the
conditional law of the one box; it mentions no transfer matrix, no gap, and no second coupling.

1. **Translation covariance** (`trL`, `wt_tr`, `blkAvg_tr`, `blkInfl_tr`, `gain_tr`): a torus translation preserves
   the Wilson weight and the product Haar measure, so the block average of `V + z` is the block average of `V`
   conjugated by the translation, and `C` moves with it.
2. **The translate count** (`sum_gain_ge`): every link of direction `μ` lies in the translates `V + z` with
   `z = l − x`, `(μ, x) ∈ V`, so `Σ_z gain_z l = Σ_{x} gain_V (μ, x) ≥ (1 − ρ) L⁴`.
3. **Ollivier** (`DSOllivier.translate_poincare`) then gives `(1 − ρ) L⁴ ‖u‖² ≤ Σ_z ‖u − E_{V+z} u‖²`.
4. **Nested comparison** (`blk_nested_le`, `boxV_sub_ovBox`, `card_fibre_le`, `overlapPoincare_of_DS`): for
   `L ≤ n` every translate lies in the overlapping box of the cells of its corner, `‖u − E_{V+z}u‖ ≤ ‖u − E_K u‖`
   for `V + z ⊆ K`, at most `(4n)⁴` corners share a box, and at `L = n` the overlapping dynamics has the Poincaré
   constant `(1 − ρ)/256`.
5. **The Clay statement** (`clay_continuum_of_DSBoxRun`): `DSBoxInfluence` with one `ρ < 1` at every large
   coupling and extent, at box side `⌈1/(κ aRun β)⌉₊`, with E, N, Y, gives `ClayContinuum` through
   `OverlapFloor.clay_continuum_of_overlapFloorRun`.
6. **Vacuity check** (`entryCost`, `dsBoxInfluence_zero`): at `β = 0` the box law ignores the outside, `C = 0`
   is an influence matrix in the entrywise cost, and `DSBoxInfluence` holds with `ρ = 0`; the hypothesis is
   satisfiable, and at `β = 0` the chain returns the floor `1/256`.

## Gaussian unit

`research/code/lab/ds_unit.py`: for the free field the influence is the linear response and the box average
is the mean escape probability of the killed walk; massless it is `1` at every `L`, so the criterion fails,
as it must; massive it converges in `L` at fixed `mL` with `ρ∞ ≈ 5–6/(mL)`, and in 4D `ρ_V ≤ 0.82` at
`mL = 4`, `L ≤ 40`.

DERIVED (module-wide): `4` the spacetime dimension and the box-side power; `2 * j + 1` the index; `256 = 4⁴` the
corner multiplicity bound `(4n)⁴/n⁴`; `0`, `1` the range of `ρ`.
-/

namespace MassGap.DSBoxFloor

open MeasureTheory Filter
open MassGap MassGap.DSBlockContract MassGap.DSOllivier
open MassGap.DobrushinMixed (LipD)
open MassGap.KnabeCriterion MassGap.HeatBath MassGap.HeatBathLocal MassGap.BlockHeatBath
open MassGap.OverlapGeometry MassGap.OverlapSweep MassGap.TileSweep
open MassGap.PeriodicState (torusObs torusState)
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

variable {N : ℕ}

/-! ## 1. Translations of the torus -/

section Transl

variable {M : ℕ}

/-- **The translate of a link** by `z`. DERIVED: `4` the dimension; `1` the successor. -/
def trL (z : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    WilsonHypercubic.Link 4 (M + 1) := (l.1, l.2 + z)

/-- DERIVED: no numeral. -/
theorem trL_neg_trL (z : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    trL (-z) (trL z l) = l := by
  unfold trL; simp

/-- DERIVED: no numeral. -/
theorem trL_trL_neg (z : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    trL z (trL (-z) l) = l := by
  unfold trL; simp

/-- The translation as a permutation of the links. DERIVED: no numeral. -/
def trE (z : WilsonHypercubic.Site 4 (M + 1)) : Equiv.Perm (WilsonHypercubic.Link 4 (M + 1)) where
  toFun := trL z
  invFun := trL (-z)
  left_inv := trL_neg_trL z
  right_inv := trL_trL_neg z

/-- **The translate of a configuration**: `(A z U) l = U (l + z)`. DERIVED: no numeral. -/
def trC (z : WilsonHypercubic.Site 4 (M + 1)) (U : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    WilsonHypercubic.Link 4 (M + 1) → SU N := fun l => U (trL z l)

/-- DERIVED: no numeral. -/
theorem continuous_trC (z : WilsonHypercubic.Site 4 (M + 1)) : Continuous (trC (N := N) z) :=
  continuous_pi fun _ => continuous_apply _

/-- DERIVED: `1` the step. -/
theorem shift_add (μ : Fin 4) (x z : WilsonHypercubic.Site 4 (M + 1)) :
    WilsonHypercubic.shift μ x + z = WilsonHypercubic.shift μ (x + z) := by
  funext ν
  simp only [WilsonHypercubic.shift, Pi.add_apply, Function.update_apply]
  split_ifs with h
  · subst h; abel
  · rfl

/-- **The Wilson weight is translation invariant.** DERIVED: no numeral. -/
theorem wt_tr (β : ℝ) (z : WilsonHypercubic.Site 4 (M + 1)) (U : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    wt (bdT M) β (trC z U) = wt (bdT M) β U := by
  have hq : ∀ q : WilsonHypercubic.Plaq 4 (M + 1),
      WilsonLattice.wilsonHol (bdT M) q (trC z U) = WilsonLattice.wilsonHol (bdT M) (q.1, q.2 + z) U := by
    intro q
    rw [Reflect.hol_bd, Reflect.hol_bd]
    simp only [trC, trL, shift_add]
  have hact : ∑ q : WilsonHypercubic.Plaq 4 (M + 1),
        WilsonAction.wilsonDensity (WilsonLattice.wilsonHol (bdT M) q (trC z U))
      = ∑ q : WilsonHypercubic.Plaq 4 (M + 1),
        WilsonAction.wilsonDensity (WilsonLattice.wilsonHol (bdT M) q U) := by
    simp only [hq]
    exact Equiv.sum_comp (Equiv.prodCongr (Equiv.refl _) (Equiv.addRight z))
      (fun q => WilsonAction.wilsonDensity (WilsonLattice.wilsonHol (bdT M) q U))
  show Real.exp (-β * ∑ q : WilsonHypercubic.Plaq 4 (M + 1),
        WilsonAction.wilsonDensity (WilsonLattice.wilsonHol (bdT M) q (trC z U)))
    = Real.exp (-β * ∑ q : WilsonHypercubic.Plaq 4 (M + 1),
        WilsonAction.wilsonDensity (WilsonLattice.wilsonHol (bdT M) q U))
  rw [hact]

#print axioms wt_tr

/-- **The block average of a translated block.** For `Sz` the translate of `S0` by `z`,
`E_{Sz} f (W) = E_{S0} (f ∘ A(−z)) (A z W)`.

DERIVED: no numeral. -/
theorem blkAvg_tr (β : ℝ) (z : WilsonHypercubic.Site 4 (M + 1))
    {S0 Sz : Finset (WilsonHypercubic.Link 4 (M + 1))} (hmem : ∀ l, l ∈ Sz ↔ trL (-z) l ∈ S0)
    (f : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    blkAvg (bdT M) β Sz f W = blkAvg (bdT M) β S0 (fun U => f (trC (-z) U)) (trC z W) := by
  have hglue : ∀ V', trC (-z) (glue S0 (trC z W) V') = glue Sz W (trC (-z) V') := by
    intro V'
    funext l
    simp only [trC]
    by_cases hl : l ∈ Sz
    · rw [glue_of_mem ((hmem l).mp hl), glue_of_mem hl]; rfl
    · rw [glue_of_not_mem (fun h => hl ((hmem l).mpr h)), glue_of_not_mem hl]
      show W (trL z (trL (-z) l)) = W l
      rw [trL_trL_neg]
  have hwt : ∀ V', wt (bdT M) β (glue S0 (trC z W) V') = wt (bdT M) β (glue Sz W (trC (-z) V')) := by
    intro V'
    rw [← hglue, wt_tr]
  have hmp := ReflectionPositivity.relabel_measurePreserving (N := N) (trE (M := M) (-z))
  have hrel : ∀ V', ReflectionPositivity.relabel (N := N) (trE (M := M) (-z)) V' = trC (-z) V' :=
    fun _ => rfl
  unfold blkAvg blkNum blkPart
  congr 1
  · calc ∫ V, f (glue Sz W V) * wt (bdT M) β (glue Sz W V) ∂(Measure.pi fun _ => probHaar (SU N))
        = ∫ V', f (glue Sz W (ReflectionPositivity.relabel (N := N) (trE (M := M) (-z)) V'))
            * wt (bdT M) β (glue Sz W (ReflectionPositivity.relabel (N := N) (trE (M := M) (-z)) V'))
            ∂(Measure.pi fun _ => probHaar (SU N)) :=
          (hmp.integral_comp' (fun V => f (glue Sz W V) * wt (bdT M) β (glue Sz W V))).symm
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun V' => ?_)
          simp only [hrel]
          rw [hglue, hwt]
  · calc ∫ V, wt (bdT M) β (glue Sz W V) ∂(Measure.pi fun _ => probHaar (SU N))
        = ∫ V', wt (bdT M) β (glue Sz W (ReflectionPositivity.relabel (N := N) (trE (M := M) (-z)) V'))
            ∂(Measure.pi fun _ => probHaar (SU N)) :=
          (hmp.integral_comp' (fun V => wt (bdT M) β (glue Sz W V))).symm
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun V' => ?_)
          simp only [hrel]
          rw [hwt]

#print axioms blkAvg_tr

/-- **The influence matrix moves with the box.**

DERIVED: no numeral. -/
theorem blkInfl_tr (β : ℝ) (z : WilsonHypercubic.Site 4 (M + 1))
    {S0 Sz : Finset (WilsonHypercubic.Link 4 (M + 1))} (hmem : ∀ l, l ∈ Sz ↔ trL (-z) l ∈ S0)
    {d0 : SU N → SU N → ℝ} {C : WilsonHypercubic.Link 4 (M + 1) → WilsonHypercubic.Link 4 (M + 1) → ℝ}
    (hC : BlkInfl (wilsonKer (bdT M) β S0) (fun _ => d0) C) :
    BlkInfl (wilsonKer (bdT M) β Sz) (fun _ => d0) (fun l k => C (trL (-z) l) (trL (-z) k)) := by
  intro g hg hR v hv W k hk x
  have hupd : ∀ (U : WilsonHypercubic.Link 4 (M + 1) → SU N) (l : WilsonHypercubic.Link 4 (M + 1)) (y : SU N),
      trC (-z) (Function.update U l y) = Function.update (trC (-z) U) (trL z l) y := by
    intro U l y
    funext l''
    simp only [trC, Function.update_apply]
    by_cases h : l'' = trL z l
    · subst h; rw [if_pos (trL_neg_trL z l), if_pos rfl]
    · have h' : trL (-z) l'' ≠ l := fun h2 => h (by rw [← h2, trL_trL_neg])
      rw [if_neg h', if_neg h]
  have hupdW : trC z (Function.update W k x) = Function.update (trC z W) (trL (-z) k) x := by
    funext l''
    simp only [trC, Function.update_apply]
    by_cases h : l'' = trL (-z) k
    · subst h; rw [if_pos (trL_trL_neg z k), if_pos rfl]
    · have h' : trL z l'' ≠ k := fun h2 => h (by rw [← h2, trL_neg_trL])
      rw [if_neg h', if_neg h]
  set g' : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ := fun U => g (trC (-z) U)
  have hg' : Continuous g' := hg.comp (continuous_trC (-z))
  have hR' : ReadsOnly S0 g' := by
    intro U U' h
    show g (trC (-z) U) = g (trC (-z) U')
    refine hR _ _ fun l hl => ?_
    exact h _ ((hmem l).mp hl)
  have hv' : LipD (fun _ => d0) g' (fun l => v (trL z l)) := by
    refine ⟨fun l => hv.1 _, fun U l y => ?_⟩
    show |g (trC (-z) (Function.update U l y)) - g (trC (-z) U)| ≤ v (trL z l) * d0 y (U l)
    rw [hupd]
    have h := hv.2 (trC (-z) U) (trL z l) y
    simp only [trC, trL_neg_trL] at h
    exact h
  have hk' : trL (-z) k ∉ S0 := fun h => hk ((hmem k).mpr h)
  have h := hC g' hg' hR' (fun l => v (trL z l)) hv' (trC z W) (trL (-z) k) hk' x
  show |blkAvg (bdT M) β Sz g (Function.update W k x) - blkAvg (bdT M) β Sz g W| ≤ _
  rw [blkAvg_tr β z hmem, blkAvg_tr β z hmem, hupdW]
  have hW : trC z W (trL (-z) k) = W k := by simp only [trC, trL_trL_neg]
  rw [hW] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_equiv (trE (M := M) (-z)) (fun i => hmem i) (fun i _ => by
    show C (trL (-z) i) (trL (-z) k) * v i = C (trL (-z) i) (trL (-z) k) * v (trL z (trL (-z) i))
    rw [trL_trL_neg]) |>.symm

#print axioms blkInfl_tr

/-- **The gain moves with the box.** DERIVED: no numeral. -/
theorem gain_tr (z : WilsonHypercubic.Site 4 (M + 1))
    {S0 Sz : Finset (WilsonHypercubic.Link 4 (M + 1))} (hmem : ∀ l, l ∈ Sz ↔ trL (-z) l ∈ S0)
    (C : WilsonHypercubic.Link 4 (M + 1) → WilsonHypercubic.Link 4 (M + 1) → ℝ)
    (l : WilsonHypercubic.Link 4 (M + 1)) :
    gain Sz (fun l k => C (trL (-z) l) (trL (-z) k)) l = gain S0 C (trL (-z) l) := by
  unfold gain
  by_cases hl : l ∈ Sz
  · rw [if_pos hl, if_pos ((hmem l).mp hl)]
    congr 1
    exact Finset.sum_equiv (trE (M := M) (-z))
      (fun i => by simp only [Finset.mem_compl]; exact not_congr (hmem i)) (fun i _ => rfl)
  · rw [if_neg hl, if_neg (fun h => hl ((hmem l).mpr h))]

#print axioms gain_tr

end Transl

/-! ## 2. The box and its translates -/

section Box

variable {M : ℕ}

/-- **The box of side `L` with corner `z`**: the links whose base site lies in `z + [0, L)⁴`.

DERIVED: `4` the dimension; `1` the successor. -/
def boxV (M L : ℕ) (z : WilsonHypercubic.Site 4 (M + 1)) : Finset (WilsonHypercubic.Link 4 (M + 1)) :=
  Finset.univ.filter (fun l => ∀ ν, ((l.2 ν - z ν : Fin (M + 1)) : ℕ) < L)

/-- DERIVED: no numeral. -/
theorem mem_boxV_tr (L : ℕ) (z : WilsonHypercubic.Site 4 (M + 1)) (l : WilsonHypercubic.Link 4 (M + 1)) :
    l ∈ boxV M L z ↔ trL (-z) l ∈ boxV M L 0 := by
  simp only [boxV, Finset.mem_filter, Finset.mem_univ, true_and, trL, Pi.add_apply, Pi.neg_apply,
    Pi.zero_apply, neg_zero, add_zero, sub_eq_add_neg]

/-- **The box sites of one direction**. DERIVED: no numeral. -/
def boxSites (M L : ℕ) (μ : Fin 4) : Finset (WilsonHypercubic.Site 4 (M + 1)) :=
  Finset.univ.filter (fun x => (μ, x) ∈ boxV M L 0)

/-- **The box has at least `L⁴` sites** when it fits. DERIVED: `4` the dimension. -/
theorem card_boxSites (L : ℕ) (hL : L ≤ M + 1) (μ : Fin 4) : L ^ 4 ≤ (boxSites M L μ).card := by
  have h1 : (Finset.univ : Finset (Fin 4 → Fin L)).card = L ^ 4 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← h1]
  refine Finset.card_le_card_of_injOn (fun y ν => (⟨(y ν : ℕ), lt_of_lt_of_le (y ν).2 hL⟩ : Fin (M + 1)))
    (fun y _ => ?_) (fun y _ y' _ h => ?_)
  · simp only [Finset.mem_coe, boxSites, boxV, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.zero_apply, sub_zero]
    exact fun ν => (y ν).2
  · funext ν
    have := congrFun h ν
    simp only [Fin.mk.injEq] at this
    exact Fin.ext this

/-- **The DS box hypothesis** at coupling `β`, box side `L`, extent `j`: a link-independent continuous separating
metric cost `d0` and an influence matrix `C ≥ 0` of the Wilson block average of the one box `boxV L 0` whose
per-direction box average of the summed outside influence is at most `ρ`.

DERIVED: `2 * j + 1` the index; `0` the box corner and the sign. -/
def DSBoxInfluence (β : ℝ) (L j : ℕ) (ρ : ℝ) : Prop :=
  ∃ d0 : SU N → SU N → ℝ, CostMetric (fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => d0) ∧
    ∃ C : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ,
      (∀ l k, 0 ≤ C l k) ∧
      BlkInfl (wilsonKer (bdT (2 * j + 1)) β (boxV (2 * j + 1) L 0)) (fun _ => d0) C ∧
      ∀ μ : Fin 4, ∑ x ∈ boxSites (2 * j + 1) L μ, ∑ k ∈ (boxV (2 * j + 1) L 0)ᶜ, C (μ, x) k
        ≤ ρ * (boxSites (2 * j + 1) L μ).card

/-- **The translate count**: the gains of all translates at one link sum to at least `(1 − ρ) L⁴`.

DERIVED: `4` the dimension; `1` the unit of the gain. -/
theorem sum_gain_ge (L : ℕ) (hL : L ≤ M + 1)
    (C : WilsonHypercubic.Link 4 (M + 1) → WilsonHypercubic.Link 4 (M + 1) → ℝ) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hρ : ∀ μ : Fin 4, ∑ x ∈ boxSites M L μ, ∑ k ∈ (boxV M L 0)ᶜ, C (μ, x) k
      ≤ ρ * (boxSites M L μ).card)
    (l : WilsonHypercubic.Link 4 (M + 1)) :
    (1 - ρ) * (L : ℝ) ^ 4
      ≤ ∑ z, gain (boxV M L z) (fun l k => C (trL (-z) l) (trL (-z) k)) l := by
  rw [Finset.sum_congr rfl fun z _ => gain_tr z (mem_boxV_tr L z) C l]
  have e1 : ∑ z : WilsonHypercubic.Site 4 (M + 1), gain (boxV M L 0) C (trL (-z) l)
      = ∑ x : WilsonHypercubic.Site 4 (M + 1), gain (boxV M L 0) C (l.1, x) := by
    refine Fintype.sum_equiv (Equiv.subLeft l.2) _ _ fun z => ?_
    simp only [trL, Equiv.subLeft_apply, sub_eq_add_neg]
  have e2 : ∑ x : WilsonHypercubic.Site 4 (M + 1), gain (boxV M L 0) C (l.1, x)
      = ∑ x ∈ boxSites M L l.1, (1 - ∑ k ∈ (boxV M L 0)ᶜ, C (l.1, x) k) := by
    rw [boxSites, Finset.sum_filter]
    rfl
  rw [e1, e2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc := card_boxSites L hL l.1
  have hcR : (L : ℝ) ^ 4 ≤ (boxSites M L l.1).card := by exact_mod_cast hc
  have h := hρ l.1
  nlinarith

#print axioms sum_gain_ge

end Box

/-! ## 3. Nested comparison with the overlapping boxes -/

section Nested

/-- **Nested block projections**: for `S' ⊆ S`, `‖v − E_{S'} v‖² ≤ ‖v − E_S v‖²`.

DERIVED: `2` the cross term. -/
theorem blk_nested_le (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    {S' S : Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1))} (hsub : S' ⊆ S) (v : TE N j) :
    torusForm hN β j (v - torusBlkCondExp β (2 * j + 1) S' v) (v - torusBlkCondExp β (2 * j + 1) S' v)
      ≤ torusForm hN β j (v - torusBlkCondExp β (2 * j + 1) S v) (v - torusBlkCondExp β (2 * j + 1) S v) := by
  set B := torusForm hN β j
  set El := torusBlkCondExp (N := N) β (2 * j + 1) S'
  set ES := torusBlkCondExp (N := N) β (2 * j + 1) S
  have hnull : B (El (ES v) - ES v) (El (ES v) - ES v) = 0 :=
    null_of_torusObs_eq hN β j _ _
      (torusBlkCondExp_keeps β j S' (ES v) (fun l hl => torusBlkCondExp_readsNot β j S v l (hsub hl)))
  have hzero : ∀ w, B w (El (ES v) - ES v) = 0 := by
    intro w
    have hcs := MassGap.HeatBathGapDecay.form_sq_le_mul B (torusForm_symm hN β j)
      (torusForm_nonneg hN β j) w (El (ES v) - ES v)
    rw [hnull, mul_zero] at hcs
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hcs (sq_nonneg _))
  have hperp : ∀ w, B (v - El v) (El w) = 0 := by
    intro w
    rw [← torusBlkCondExp_selfAdj hN β j S', map_sub, torusBlkCondExp_idem, sub_self, map_zero]
    rfl
  set a := v - El v
  set b := El v - ES v
  have hab : B a b = 0 := by
    have : b = El (v - ES v) + (El (ES v) - ES v) := by
      simp only [b, map_sub]; abel
    rw [this, map_add, hperp, hzero, add_zero]
  have hsum : v - ES v = a + b := by simp only [a, b]; abel
  rw [hsum]
  simp only [map_add, LinearMap.add_apply]
  rw [torusForm_symm hN β j b a, hab]
  have := torusForm_nonneg hN β j b
  linarith

#print axioms blk_nested_le

/-- **A window of at most `n + 1` sites starting in a cell stays in its pair of cells.**

DERIVED: `1` the step; `3` the colour period. -/
theorem inPair_window {n T : ℕ} (hn : 1 ≤ n) (hT : 3 * n ≤ T) {a y : ℕ} (ha : a < T) (hy : y ≤ n) :
    InPair (qO n T) (cellO n T a) (cellO n T ((a + y) % T)) := by
  have hq3 := three_le_qO hn hT
  have hqT := qO_mul_le n T
  have hn0 : 0 < n := hn
  unfold InPair cellO
  rcases lt_or_ge (a + y) T with hw | hw
  · rw [Nat.mod_eq_of_lt hw]
    have hd1 : a / n ≤ (a + y) / n := Nat.div_le_div_right (by omega)
    have hd2 : (a + y) / n ≤ a / n + 1 := by
      have : (a + y) / n ≤ (a + n) / n := Nat.div_le_div_right (by omega)
      rwa [Nat.add_div_right a hn0] at this
    rcases le_or_gt (qO n T - 1) (a / n) with hc | hc
    · left
      rw [min_eq_right hc, min_eq_right (le_trans hc hd1)]
    · rw [min_eq_left hc.le]
      rcases eq_or_lt_of_le hd1 with he | hlt
      · left; rw [← he, min_eq_left hc.le]
      · right
        have he : (a + y) / n = a / n + 1 := by omega
        rw [he, min_eq_left (by omega), Nat.mod_eq_of_lt (by omega)]
  · have hlt : a + y - T < T := by omega
    rw [Nat.mod_eq_sub_mod hw, Nat.mod_eq_of_lt hlt]
    have h0 : (a + y - T) / n = 0 := Nat.div_eq_of_lt (by omega)
    have hc : qO n T - 1 ≤ a / n := by
      rw [Nat.le_div_iff_mul_le hn0]
      have : (qO n T - 1) * n = qO n T * n - n := by
        rw [Nat.sub_mul, one_mul]
      omega
    right
    rw [h0, min_eq_right hc, min_eq_left (Nat.zero_le _), Nat.sub_add_cancel (by omega), Nat.mod_self]

#print axioms inPair_window

/-- **The corner's overlapping box**: the pair of cells starting at the cell of each corner coordinate.

DERIVED: `2 * j + 1` the index; `3` the colour period. -/
def cornerBox {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1) (z : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    Fin 4 → Fin (qO n (2 * j + 1 + 1)) :=
  fun ν => ⟨cellO n (2 * j + 1 + 1) (z ν), cellO_lt hn hL _⟩

/-- **Every translate of a box of side `n` lies in its corner's overlapping box.**

DERIVED: `2 * j + 1` the index; `3` the least cell count of `OverlapGeometry` (`3n ≤ L`). -/
theorem boxV_sub_ovBox {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    (z : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    boxV (2 * j + 1) n z ⊆ ovBox n (2 * j + 1) (cornerBox hn hL z) := by
  intro l hl
  rw [mem_ovBox]
  intro ν
  simp only [boxV, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  have hy := hl ν
  have e : ((l.2 ν : Fin (2 * j + 1 + 1)) : ℕ)
      = ((z ν : ℕ) + ((l.2 ν - z ν : Fin (2 * j + 1 + 1)) : ℕ)) % (2 * j + 1 + 1) := by
    rw [← Fin.val_add, add_sub_cancel]
  show InPair _ (cellO n (2 * j + 1 + 1) (z ν)) (cellO n (2 * j + 1 + 1) (l.2 ν))
  rw [e]
  exact inPair_window hn hL (z ν).2 hy.le

#print axioms boxV_sub_ovBox

/-- **At most `4n` coordinates share a cell.** DERIVED: `4` the last cell's length bound; `3` the least
cell count of `OverlapGeometry` (`3n ≤ T`). -/
theorem card_cell_le {n T : ℕ} (hn : 1 ≤ n) (hT : 3 * n ≤ T) (c : ℕ) :
    (Finset.univ.filter (fun t : Fin T => cellO n T t = c)).card ≤ 4 * n := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun t : Fin T => cellO n T t = c))
    (t := Finset.range (4 * n)) (fun t : Fin T => (t : ℕ) - c * n) (fun t ht => ?_) (fun t ht t' ht' h => ?_)
  · simpa using h
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
    have hw := cellO_window hn hT t.2
    rw [ht] at hw
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
    have hw := cellO_window hn hT t.2
    have hw' := cellO_window hn hT t'.2
    rw [ht] at hw
    rw [ht'] at hw'
    exact Fin.ext (by simp only at h; omega)

#print axioms card_cell_le

/-- **At most `(4n)⁴` corners share an overlapping box.** DERIVED: `4` the dimension and the cell bound;
`3` the least cell count of `OverlapGeometry` (`3n ≤ L`). -/
theorem card_fibre_le {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    (K : Fin 4 → Fin (qO n (2 * j + 1 + 1))) :
    (Finset.univ.filter (fun z : WilsonHypercubic.Site 4 (2 * j + 1 + 1) => cornerBox hn hL z = K)).card
      ≤ (4 * n) ^ 4 := by
  have hsub : Finset.univ.filter (fun z : WilsonHypercubic.Site 4 (2 * j + 1 + 1) => cornerBox hn hL z = K)
      ⊆ Fintype.piFinset (fun ν => Finset.univ.filter
          (fun t : Fin (2 * j + 1 + 1) => cellO n (2 * j + 1 + 1) t = (K ν : ℕ))) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Fintype.mem_piFinset]
    intro ν
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := congrFun hz ν
    simp only [cornerBox] at this
    exact congrArg Fin.val this
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ ν : Fin 4, (Finset.univ.filter
          (fun t : Fin (2 * j + 1 + 1) => cellO n (2 * j + 1 + 1) t = (K ν : ℕ))).card
      ≤ ∏ _ν : Fin 4, 4 * n := Finset.prod_le_prod' fun ν _ => card_cell_le hn hL _
    _ = (4 * n) ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

#print axioms card_fibre_le

end Nested

/-! ## 4. The floor -/

section Floor

/-- **The DS box hypothesis at box side `n` gives the overlapping Poincaré constant `(1 − ρ)/256`.**

DERIVED: `256 = 4⁴`; `4` the dimension; `0`, `1` the range of `ρ`; `3` the colour period. -/
theorem overlapPoincare_of_DS (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hL : 3 * n ≤ 2 * j + 1 + 1)
    {ρ : ℝ} (hρ1 : ρ ≤ 1) (hDS : DSBoxInfluence (N := N) β n j ρ) :
    OverlapPoincare hN β n j ((1 - ρ) / 256) := by
  obtain ⟨d0, hd, Cm, hC0, hC, hρ⟩ := hDS
  intro u hu
  have hnT : n ≤ (2 * j + 1 + 1) := by omega
  set S : WilsonHypercubic.Site 4 (2 * j + 1 + 1) → Finset (WilsonHypercubic.Link 4 (2 * j + 1 + 1)) := fun z => boxV (2 * j + 1) n z
  set Cz : WilsonHypercubic.Site 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ :=
    fun z l k => Cm (trL (-z) l) (trL (-z) k)
  have hZ : (Fintype.card (WilsonHypercubic.Site 4 (2 * j + 1 + 1)) : ℝ) = ((2 * j + 1 + 1) : ℝ) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  have hTpos : (0 : ℝ) < ((2 * j + 1 + 1) : ℝ) ^ 4 := by positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (1 - ρ) * (n : ℝ) ^ 4 / ((2 * j + 1 + 1) : ℝ) ^ 4 := ⟨_, rfl⟩
  have hκZ : κ * Fintype.card (WilsonHypercubic.Site 4 (2 * j + 1 + 1)) = (1 - ρ) * (n : ℝ) ^ 4 := by
    rw [hZ, hκdef]; exact div_mul_cancel₀ _ hTpos.ne'
  have hnT' : (n : ℝ) ^ 4 ≤ ((2 * j + 1 + 1) : ℝ) ^ 4 := by
    have : (n : ℝ) ≤ (2 * j + 1 + 1) := by exact_mod_cast hnT
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 4
  have hρ0' : 0 ≤ 1 - ρ := by linarith
  have hκ1 : κ ≤ 1 := by
    rw [hκdef, div_le_one hTpos]
    have hρ0 : 0 ≤ ρ := by
      have h := hρ 0
      have hs : 0 ≤ ∑ x ∈ boxSites (2 * j + 1) n 0, ∑ k ∈ (boxV (2 * j + 1) n 0)ᶜ, Cm (0, x) k :=
        Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun k _ => hC0 _ _
      have hc : (0 : ℝ) < (boxSites (2 * j + 1) n 0).card := by
        have := card_boxSites n hnT (0 : Fin 4)
        have h4 : 0 < n ^ 4 := pow_pos hn 4
        exact_mod_cast lt_of_lt_of_le h4 this
      nlinarith
    have h1 : (1 - ρ) * (n : ℝ) ^ 4 ≤ 1 * (n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hCz : ∀ z, BlkInfl (wilsonKer (bdT (2 * j + 1)) β (S z)) (fun _ => d0) (Cz z) :=
    fun z => blkInfl_tr β z (mem_boxV_tr n z) hC
  have hCz0 : ∀ z l k, 0 ≤ Cz z l k := fun z l k => hC0 _ _
  have hcol : ∀ l, κ * Fintype.card (WilsonHypercubic.Site 4 (2 * j + 1 + 1)) ≤ ∑ z, gain (S z) (Cz z) l := by
    intro l
    rw [hκZ]
    exact sum_gain_ge n hnT Cm hρ1 hρ l
  have hP := translate_poincare hN β j S hd hCz hCz0 hκ1 hcol u hu
  rw [hκZ] at hP
  -- nested comparison and the corner multiplicity
  set F : (Fin 4 → Fin (qO n (2 * j + 1 + 1))) → ℝ := fun K => torusForm hN β j (u - ovP β n j K u) (u - ovP β n j K u)
  have hF0 : ∀ K, 0 ≤ F K := fun K => torusForm_nonneg hN β j _
  have hnest : ∀ z, torusForm hN β j (u - torusBlkCondExp β (2 * j + 1) (S z) u)
      (u - torusBlkCondExp β (2 * j + 1) (S z) u) ≤ F (cornerBox hn hL z) :=
    fun z => blk_nested_le hN β j (boxV_sub_ovBox hn hL z) u
  have hmult : ∑ z, F (cornerBox hn hL z) ≤ ((4 * n : ℕ) : ℝ) ^ 4 * ∑ K, F K := by
    rw [← Finset.sum_fiberwise Finset.univ (cornerBox hn hL) (fun z => F (cornerBox hn hL z)), Finset.mul_sum]
    refine Finset.sum_le_sum fun K _ => ?_
    rw [Finset.sum_congr rfl fun z hz => congrArg F (Finset.mem_filter.mp hz).2]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := card_fibre_le hn hL K
    have hcR : ((Finset.univ.filter fun z => cornerBox hn hL z = K).card : ℝ) ≤ ((4 * n : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hcR (hF0 K)
  have hsum : ∑ z, torusForm hN β j (u - torusBlkCondExp β (2 * j + 1) (S z) u)
      (u - torusBlkCondExp β (2 * j + 1) (S z) u) ≤ ((4 * n : ℕ) : ℝ) ^ 4 * ∑ K, F K :=
    (Finset.sum_le_sum fun z _ => hnest z).trans hmult
  have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos (by exact_mod_cast hn) 4
  have e4 : ((4 * n : ℕ) : ℝ) ^ 4 = 256 * (n : ℝ) ^ 4 := by push_cast; ring
  have hfin : (1 - ρ) * (n : ℝ) ^ 4 * torusForm hN β j u u ≤ 256 * (n : ℝ) ^ 4 * ∑ K, F K := by
    rw [← e4]; exact hP.trans hsum
  show (1 - ρ) / 256 * torusForm hN β j u u ≤ ∑ K, F K
  have : (n : ℝ) ^ 4 * ((1 - ρ) / 256 * torusForm hN β j u u) ≤ (n : ℝ) ^ 4 * ∑ K, F K := by
    nlinarith
  exact le_of_mul_le_mul_left this hn4

#print axioms overlapPoincare_of_DS

/-- **The overlapping gap from the DS box hypothesis at every large extent.**

DERIVED: `256 = 4⁴`; `1` the cap; `3` the colour period. -/
theorem overlapGap_ge_of_DS (hN : N ≠ 0) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) {ρ : ℝ} (hρ : ρ < 1)
    (hDS : ∀ᶠ j in atTop, DSBoxInfluence (N := N) β n j ρ) :
    min ((1 - ρ) / 256) 1 ≤ overlapGap hN β n := by
  apply le_csSup ⟨1, fun _ h => h.2.1⟩
  refine ⟨le_min (by linarith) zero_le_one, min_le_right _ _, ?_⟩
  filter_upwards [hDS, Filter.eventually_ge_atTop (3 * n)] with j hj hjL
  have hP := overlapPoincare_of_DS hN β hn (by omega) hρ.le hj
  intro u hu
  have h1 := hP u hu
  have h2 : min ((1 - ρ) / 256) 1 * torusForm hN β j u u ≤ (1 - ρ) / 256 * torusForm hN β j u u :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (torusForm_nonneg hN β j u)
  linarith

#print axioms overlapGap_ge_of_DS

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the DS box criterion at each coupling.** At every large `β` and every
large extent, `DSBoxInfluence` with one `ρ < 1` for the box of side `⌈1/(κ aRun β)⌉₊`; with E, N, Y,
`ClayContinuum`.

DERIVED: `2` the least rank; `0` the signs; `4` the spacetime dimension; `1` the cap and the least cell side;
`256 = 4⁴`. -/
theorem clay_continuum_of_DSBoxRun (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ < 1)
    (hDS : ∀ᶠ β in atTop, ∀ᶠ j in atTop, DSBoxInfluence (N := N) β
      (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β) j ρ)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  have hN1 : 1 ≤ N := by omega
  have hs := OverlapFloor.scaleFunction_const_mul_aRun hN1 hκ one_pos
  have hg : 0 < min ((1 - ρ) / 256) 1 := lt_min (by linarith) one_pos
  refine OverlapFloor.clay_continuum_of_overlapFloorRun hN2 hN Z τ hZ hB hL hκ hg ?_ O G hconvK hY
  filter_upwards [hDS, hs.eventually_small 1 one_pos, hs.eventually_le] with β hβ hs1 hs0
  exact overlapGap_ge_of_DS hN β (blockSide_le hs0.1 hs1).1 hρ hβ

#print axioms clay_continuum_of_DSBoxRun

end Floor

/-! ## 5. Vacuity check: the hypothesis holds at `β = 0` -/

section Vacuity

/-- **The entrywise cost on `SU(N)`**: `Σ_{i,j} ‖a_{ij} − b_{ij}‖`. DERIVED: no numeral. -/
def entryCost (a b : SU N) : ℝ :=
  ∑ i, ∑ j, ‖(a : Matrix (Fin N) (Fin N) ℂ) i j - (b : Matrix (Fin N) (Fin N) ℂ) i j‖

/-- **The entrywise cost is a continuous separating metric.** DERIVED: `0` the diagonal. -/
theorem entryCost_metric {Lk : Type} : CostMetric (fun _ : Lk => entryCost (N := N)) where
  cont _ := by
    unfold entryCost
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).sub
      ((continuous_subtype_val.comp continuous_snd).matrix_elem i j) |>.norm
  nonneg _ a b := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refl _ a := by simp [entryCost]
  sep _ a b h := by
    unfold entryCost at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => norm_nonneg _).mp h
    apply Subtype.ext
    funext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg _).mp (h1 i (Finset.mem_univ _))
      j (Finset.mem_univ _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  symm _ a b := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => norm_sub_rev _ _
  tri _ a b c := by
    unfold entryCost
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- At `β = 0` the weight is `1`. DERIVED: `0` the coupling; `1` the weight. -/
theorem wt_zero {M : ℕ} (W : WilsonHypercubic.Link 4 (M + 1) → SU N) : wt (bdT M) 0 W = 1 := by
  show Real.exp (-0 * _) = 1
  simp

/-- **At `β = 0` the DS box hypothesis holds with `ρ = 0`**: the block law ignores the outside, so `C = 0` is an
influence matrix. The hypothesis is satisfiable, and the chain gives the floor `1/256` there.

DERIVED: `0` the coupling, the matrix and `ρ`. -/
theorem dsBoxInfluence_zero (L j : ℕ) : DSBoxInfluence (N := N) 0 L j 0 := by
  refine ⟨entryCost, entryCost_metric, fun _ _ => 0, fun _ _ => le_rfl, ?_, fun μ => by simp⟩
  intro g _ hR v _ W k hk x
  have hQ : blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g (Function.update W k x)
      = blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g W := by
    unfold blkAvg blkNum blkPart
    simp only [wt_zero, mul_one]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    refine hR _ _ fun l hl => ?_
    have hl' : l ∈ boxV (2 * j + 1) L 0 := hl
    rw [glue_of_mem hl', glue_of_mem hl']
  show |blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g (Function.update W k x)
    - blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g W| ≤ _
  rw [hQ, sub_self, abs_zero]
  simp

#print axioms dsBoxInfluence_zero

/-- **The floor at `β = 0` through the DS chain.** DERIVED: `256 = 4⁴`; `1` the least cell side. -/
theorem overlapGap_zero_ge (hN : N ≠ 0) {n : ℕ} (hn : 1 ≤ n) : 1 / 256 ≤ overlapGap hN 0 n := by
  have h := overlapGap_ge_of_DS hN 0 hn (ρ := 0) zero_lt_one
    (Filter.Eventually.of_forall fun j => dsBoxInfluence_zero n j)
  norm_num at h
  exact h

#print axioms overlapGap_zero_ge

end Vacuity

end MassGap.DSBoxFloor
