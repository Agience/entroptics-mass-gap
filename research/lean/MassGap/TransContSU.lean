import Mathlib
import MassGap.CutSU
import MassGap.SUInputs

/-!
# Continuity in a real translation from the kernel bound on the basis readings

`ClayWiring.TransContT hN (mixOfZ B op m Z)` asks that `v ↦ contT (F + v)` be continuous on `ℝ⁴` for
every admissible family `F`. This module proves it from three inputs of the SU capstone:
`hZ` (the factor does not see the reflection), `hD` (`DiagBoundSep` at `Z`) and `h0` (`OS0Own`).

The route, for one admissible family:

* `contT (F + w) = ∑_b ∏ᵢ coefC · contS ((op bᵢ, fᵢ(· − w)))ᵢ` (`ClayWiring.contT_mixOfZ`), so it is
  enough that each basis reading is continuous in `w` at `0`.
* For `|w_μ| ≤ d₀/2`, `d₀ = min d 1`, every family whose slot `i` vanishes outside
  `supp fᵢ ∪ supp fᵢ(· − w)` is `d₀/2`-separated (`sepBy_half`), so its lattice readings converge
  (`tendsto_latSkR_connected`, from `hD`, `hZ`) and the basis reading is additive in each slot
  (`contS_update_testAdd`).
* Replacing the slots one at a time by their translates, each step changes one slot by
  `fᵢ(· − w) − fᵢ`, and `OS0Own` at separation `d₀/2` bounds that step by
  `K · ‖fᵢ(· − w) − fᵢ‖_{L¹} · ∏_{j ≠ i} ‖f_j‖_{L¹}` with one constant `K` (`abs_contS_le_of_os0`;
  `l1_translate` for the translated slots).
* `‖f(· − w) − f‖_{L¹} → 0` as `w → 0` for a continuous `f` of bounded support, by dominated
  convergence with the bound `2M` on a closed ball (`tendsto_l1_tDiff`).

`transContT_of_os0` is the result. `clayStatementAt_of_inputs_TC` is
`SUInputs.clayStatementAt_of_inputs''` with `hTC` removed; `clayStatementAt_of_inputs'''` is
`CutSU.clayStatementAt_of_inputs'` with `hTC` removed.

DERIVED (module-wide): `0` the reflection plane, the zero vector and the vanishing value; `1` the cap
on the separation and the radius margin; `2` the halving of the separation and of `M + M`; `-1` the
coefficient of the subtracted test function; `4` the dimension.
-/

noncomputable section

namespace MassGap.TransContSU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. Supports near a family and its translate -/

/-- `h` vanishes outside the support of `g` and of its translate `g(· − w)`. -/
def SuppIn (g : TestFn) (w : Fin 4 → ℝ) (h : TestFn) : Prop :=
  ∀ y, h.1 y ≠ 0 → g.1 y ≠ 0 ∨ g.1 (y - w) ≠ 0

/-- **Half the separation survives a translation by at most half of it**: if `g, g'` are
`d`-separated and `|w_μ| ≤ d/2`, then any `f` near `g` and `h` near `g'` (`SuppIn`) are
`d/2`-separated. -/
theorem sepBy_half {d : ℝ} {g g' f h : TestFn} {w : Fin 4 → ℝ}
    (hs : ContinuumSep.sepBy d g g') (hw : ∀ μ, |w μ| ≤ d / 2)
    (hf : SuppIn g w f) (hh : SuppIn g' w h) : ContinuumSep.sepBy (d / 2) f h := by
  intro y z hy hz
  rcases hf y hy with h1 | h1 <;> rcases hh z hz with h2 | h2
  · obtain ⟨μ, hμ⟩ := hs y z h1 h2
    have h3 := hw μ
    have h4 : 0 ≤ |w μ| := abs_nonneg _
    exact ⟨μ, by linarith⟩
  · obtain ⟨μ, hμ⟩ := hs y (z - w) h1 h2
    have e : y μ - (z - w) μ = (y μ - z μ) + w μ := by simp only [Pi.sub_apply]; ring
    rw [e] at hμ
    have h3 := abs_add_le (y μ - z μ) (w μ)
    have h4 := hw μ
    exact ⟨μ, by linarith⟩
  · obtain ⟨μ, hμ⟩ := hs (y - w) z h1 h2
    have e : (y - w) μ - z μ = (y μ - z μ) + -w μ := by simp only [Pi.sub_apply]; ring
    rw [e] at hμ
    have h3 := abs_add_le (y μ - z μ) (-w μ)
    rw [abs_neg] at h3
    have h4 := hw μ
    exact ⟨μ, by linarith⟩
  · obtain ⟨μ, hμ⟩ := hs (y - w) (z - w) h1 h2
    have e : (y - w) μ - (z - w) μ = y μ - z μ := by simp only [Pi.sub_apply]; ring
    rw [e] at hμ
    have h3 := hw μ
    have h4 : 0 ≤ |w μ| := abs_nonneg _
    exact ⟨μ, by linarith⟩

/-! ## 2. Convergence and additivity on separated families -/

/-- **The lattice readings at `connected Z` converge on every separated family**, from `hZ` and
`DiagBoundSep` at `Z`. -/
theorem tendsto_latSkR_connected (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ι : Type} [Fintype ι]
    (F : ι → SField N) {d : ℝ} (hd : 0 < d) (hF : ContinuumSep.FamSep d F) :
    Tendsto (fun k => latSkR hN (Renorm.connected hN Z) k F) (ultra : Filter ℕ)
      (𝓝 (contS hN (Renorm.connected hN Z) F)) := by
  have hR := Renorm.connected_reflCompat hN Z 0 hZ
  have hDC : ContinuumSepClass.DiagBoundClassAlong hN (dyBeta (one_le_of_ne_zero hN))
      (Renorm.connected hN Z) 0 ContinuumSepClass.TestClass.all := fun P => hD P.1
  exact ClayTiltedFull.tendsto_contSAlong_of_diagBoundClass hN _ _ hR hDC F hd hF (fun _ => trivial)

/-- The lattice reading with slot `a` replaced by `x`: the prefactor times the state of the
replaced factor times the product of the others. -/
theorem latSkR_update (hN : N ≠ 0) (ρ : Renorm N) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → LField (MassGap.SUN.SU N)) (h : ι → TestFn) (a : ι) (x : TestFn) :
    latSkR hN ρ k (fun i => (L i, Function.update h a x i))
      = (∏ i, ρ.Z k (L i)) * stateK hN k
          (smear (dySpacing N k) ((L a).sub (ρ.c k (L a))).1 x
            * ∏ i ∈ Finset.univ.erase a,
                smear (dySpacing N k) ((L i).sub (ρ.c k (L i))).1 (h i)) := by
  show (∏ i, ρ.Z k (L i)) * stateK hN k (∏ i, smear (dySpacing N k) ((L i).sub (ρ.c k (L i))).1
      (Function.update h a x i)) = _
  congr 1
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **The basis reading is additive in one slot** on separated families. -/
theorem contS_update_testAdd (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] (L : ι → LField (MassGap.SUN.SU N)) (h : ι → TestFn) (a : ι) (f e : TestFn)
    {d : ℝ} (hd : 0 < d)
    (h1 : ContinuumSep.FamSep d (fun i => (L i, Function.update h a f i)))
    (h2 : ContinuumSep.FamSep d (fun i => (L i, Function.update h a e i)))
    (h3 : ContinuumSep.FamSep d (fun i => (L i, Function.update h a (testAdd f e) i))) :
    contS hN (Renorm.connected hN Z) (fun i => (L i, Function.update h a (testAdd f e) i))
      = contS hN (Renorm.connected hN Z) (fun i => (L i, Function.update h a f i))
        + contS hN (Renorm.connected hN Z) (fun i => (L i, Function.update h a e i)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique (tendsto_latSkR_connected hN Z hZ hD _ hd h3)
    (((tendsto_latSkR_connected hN Z hZ hD _ hd h1).add
      (tendsto_latSkR_connected hN Z hZ hD _ hd h2)).congr (fun k => ?_))
  rw [latSkR_update, latSkR_update, latSkR_update,
    smear_testAdd (dySpacing_pos (one_le_of_ne_zero hN) k), add_mul, (stateK hN k).map_add,
    mul_add]

/-! ## 3. The kernel bound on families indexed by any finite type -/

/-- **`OS0Own` on a family indexed by `ι`**, through `Fintype.equivFin ι`. -/
theorem abs_contS_le_of_os0 (hN : N ≠ 0) {B : Type} (op : B → LField (MassGap.SUN.SU N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) {α γ β κ : ℝ}
    (hαγ : ∀ (n : ℕ) (b : Fin n → B) (f : Fin n → TestFn) (d : ℝ), 0 < d → d ≤ 1 →
      (∀ i, Continuous (f i).1) → (∀ i j, i ≠ j → ContinuumSep.sepBy d (f i) (f j)) →
        |contS hN (Renorm.connected hN Z) (fun i => (op (b i), f i))|
          ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹ * ∏ i, l1 (f i))
    {ι : Type} [Fintype ι] (b : ι → B) (T : ι → TestFn) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hc : ∀ i, Continuous (T i).1) (hs : ∀ i j, i ≠ j → ContinuumSep.sepBy d (T i) (T j)) :
    |contS hN (Renorm.connected hN Z) (fun i => (op (b i), T i))|
      ≤ α * γ ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ) ^ β
        * (d ^ (κ * Fintype.card ι))⁻¹ * ∏ i, l1 (T i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hαγ (Fintype.card ι) (fun j => b (e j)) (fun j => T (e j)) d hd hd1
    (fun j => hc (e j)) (fun i j hij => hs (e i) (e j) (e.injective.ne hij))
  have e1 : contS hN (Renorm.connected hN Z) (fun i => (op (b i), T i))
      = contS hN (Renorm.connected hN Z) (fun j => (op (b (e j)), T (e j))) :=
    (MassGap.ContinuumSchwinger.contS_comp_equiv hN (Renorm.connected hN Z) e
      (fun i => (op (b i), T i))).symm
  have e2 : ∏ i, l1 (T i) = ∏ j, l1 (T (e j)) := (Equiv.prod_comp e (fun i => l1 (T i))).symm
  rw [e1, e2]
  exact h

/-! ## 4. The `L¹` norm under translation -/

/-- The `L¹` norm is unchanged by a translation. -/
theorem l1_translate (g : TestFn) (w : Fin 4 → ℝ) : l1 (g.translate w) = l1 g := by
  unfold l1
  exact MeasureTheory.integral_sub_right_eq_self (fun x => |g.1 x|) w

/-- The difference `g(· − w) − g`. -/
def tDiff (g : TestFn) (w : Fin 4 → ℝ) : TestFn := testAdd (g.translate w) (testSmul (-1) g)

/-- **Continuity of translation in `L¹`** for a continuous test function: `‖g(· − w) − g‖_{L¹} → 0`
as `w → 0`. Dominated convergence, with the bound `M + M` on the closed ball of radius `R + 1`. -/
theorem tendsto_l1_tDiff (g : TestFn) (hg : Continuous g.1) :
    Tendsto (fun w => l1 (tDiff g w)) (𝓝 0) (𝓝 0) := by
  obtain ⟨R, M, hR, hM, hs⟩ := g.2
  have hlim : Tendsto (fun w : Fin 4 → ℝ => ∫ y, |g.1 (y - w) + -1 * g.1 y|) (𝓝 0)
      (𝓝 (∫ _y : Fin 4 → ℝ, (0 : ℝ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := fun w y => |g.1 (y - w) + -1 * g.1 y|) (f := fun _ => (0 : ℝ))
      (Set.indicator (Metric.closedBall (0 : Fin 4 → ℝ) (R + 1)) (fun _ => M + M)) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun w => ?_
      have hcw : Continuous fun y : Fin 4 → ℝ => |g.1 (y - w) + -1 * g.1 y| :=
        continuous_abs.comp ((hg.comp (continuous_id.sub continuous_const)).add
          (continuous_const.mul hg))
      exact hcw.aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds (0 : Fin 4 → ℝ) one_pos] with w hw
      refine Filter.Eventually.of_forall fun y => ?_
      show ‖|g.1 (y - w) + -1 * g.1 y|‖ ≤ _
      have hw' : ‖w‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw
      by_cases hy : y ∈ Metric.closedBall (0 : Fin 4 → ℝ) (R + 1)
      · rw [Set.indicator_of_mem hy, Real.norm_eq_abs, abs_abs]
        calc |g.1 (y - w) + -1 * g.1 y| ≤ |g.1 (y - w)| + |-1 * g.1 y| := abs_add_le _ _
          _ ≤ M + M := by
            rw [abs_mul, abs_neg, abs_one, one_mul]
            exact add_le_add (hM _) (hM _)
      · rw [Set.indicator_of_notMem hy]
        have hy' : ¬ ‖y‖ ≤ R + 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hy
        rw [pi_norm_le_iff_of_nonneg (by linarith)] at hy'
        push Not at hy'
        obtain ⟨μ, hμ⟩ := hy'
        rw [Real.norm_eq_abs] at hμ
        have h1 : g.1 y = 0 := by
          by_contra hne
          have h3 := hs y hne μ
          linarith
        have h2 : g.1 (y - w) = 0 := by
          by_contra hne
          have h3 := hs (y - w) hne μ
          have h4 : |w μ| ≤ ‖w‖ := by
            have h5 := norm_le_pi_norm w μ
            rwa [Real.norm_eq_abs] at h5
          have h5 : |y μ| ≤ |(y - w) μ| + |w μ| := by
            have h6 := abs_add_le ((y - w) μ) (w μ)
            rwa [show (y - w) μ + w μ = y μ by simp] at h6
          linarith
        rw [h1, h2]
        simp
    · exact (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
        (s := Metric.closedBall (0 : Fin 4 → ℝ) (R + 1)) (C := M + M)
        MeasureTheory.measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
    · refine Filter.Eventually.of_forall fun y => ?_
      have hc : Continuous fun w : Fin 4 → ℝ => |g.1 (y - w) + -1 * g.1 y| :=
        continuous_abs.comp ((hg.comp (continuous_const.sub continuous_id)).add continuous_const)
      convert hc.tendsto 0 using 2
      simp
  simp only [MeasureTheory.integral_zero] at hlim
  exact hlim

/-! ## 5. Continuity of one basis reading at the zero translation -/

/-- **The basis reading of a separated continuous family is continuous in a common translation at
`0`**, from `hZ`, `hD` and `OS0Own`. -/
theorem tendsto_contS_translate (hN : N ≠ 0) {B : Type} (op : B → LField (MassGap.SUN.SU N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) (h0 : OS0Own hN op Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → B) (g : ι → TestFn)
    (hc : ∀ i, Continuous (g i).1) {d : ℝ} (hd : 0 < d)
    (hs : ∀ i j, i ≠ j → ContinuumSep.sepBy d (g i) (g j)) :
    Tendsto (fun w => contS hN (Renorm.connected hN Z) (fun i => (op (b i), (g i).translate w)))
      (𝓝 0) (𝓝 (contS hN (Renorm.connected hN Z) (fun i => (op (b i), g i)))) := by
  obtain ⟨α, γ, β, κ, hαγ⟩ := h0
  obtain ⟨d0, hd0, hd01, hs0⟩ : ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧
      ∀ i j, i ≠ j → ContinuumSep.sepBy d0 (g i) (g j) :=
    ⟨min d 1, lt_min hd one_pos, min_le_right _ _, fun i j hij y z hy hz => by
      obtain ⟨μ, hμ⟩ := hs i j hij y z hy hz
      exact ⟨μ, (min_le_left _ _).trans hμ⟩⟩
  have hδ : 0 < d0 / 2 := half_pos hd0
  have hδ1 : d0 / 2 ≤ 1 := by linarith
  let K : ℝ := α * γ ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ) ^ β
    * ((d0 / 2) ^ (κ * Fintype.card ι))⁻¹
  let S : (ι → TestFn) → ℝ := fun H => contS hN (Renorm.connected hN Z) (fun i => (op (b i), H i))
  have hmain : ∀ w : Fin 4 → ℝ, (∀ μ, |w μ| ≤ d0 / 2) →
      |S (fun i => (g i).translate w) - S g|
        ≤ ∑ a, K * (l1 (tDiff (g a) w) * ∏ i ∈ Finset.univ.erase a, l1 (g i)) := by
    intro w hw
    let g' : ι → TestFn := fun i => (g i).translate w
    let hyb : Finset ι → ι → TestFn := fun s i => if i ∈ s then g' i else g i
    have supp_g : ∀ i, SuppIn (g i) w (g i) := fun i y hy => Or.inl hy
    have supp_g' : ∀ i, SuppIn (g i) w (g' i) := fun i y hy => Or.inr hy
    have supp_d : ∀ i, SuppIn (g i) w (tDiff (g i) w) := fun i y hy => by
      by_contra hne
      push Not at hne
      apply hy
      show (g i).1 (y - w) + -1 * (g i).1 y = 0
      rw [hne.1, hne.2]
      ring
    have supp_ad : ∀ i, SuppIn (g i) w (testAdd (g i) (tDiff (g i) w)) := fun i y hy => by
      right
      intro h
      apply hy
      show (g i).1 y + ((g i).1 (y - w) + -1 * (g i).1 y) = 0
      rw [h]
      ring
    have cont_g' : ∀ i, Continuous (g' i).1 :=
      fun i => (hc i).comp (continuous_id.sub continuous_const)
    have cont_d : ∀ i, Continuous (tDiff (g i) w).1 :=
      fun i => (cont_g' i).add (continuous_const.mul (hc i))
    have supp_upd : ∀ (H : ι → TestFn) (a : ι) (x : TestFn), (∀ i, SuppIn (g i) w (H i)) →
        SuppIn (g a) w x → ∀ i, SuppIn (g i) w (Function.update H a x i) := by
      intro H a x hH hx i
      by_cases hi : i = a
      · subst hi
        rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne hi]
        exact hH i
    have cont_upd : ∀ (H : ι → TestFn) (a : ι) (x : TestFn), (∀ i, Continuous (H i).1) →
        Continuous x.1 → ∀ i, Continuous (Function.update H a x i).1 := by
      intro H a x hH hx i
      by_cases hi : i = a
      · subst hi
        rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne hi]
        exact hH i
    have supp_hyb : ∀ s i, SuppIn (g i) w (hyb s i) := fun s i => by
      by_cases h : i ∈ s
      · simp only [hyb, if_pos h]
        exact supp_g' i
      · simp only [hyb, if_neg h]
        exact supp_g i
    have cont_hyb : ∀ s i, Continuous (hyb s i).1 := fun s i => by
      by_cases h : i ∈ s
      · simp only [hyb, if_pos h]
        exact cont_g' i
      · simp only [hyb, if_neg h]
        exact hc i
    have good_sep : ∀ H : ι → TestFn, (∀ i, SuppIn (g i) w (H i)) →
        ∀ i j, i ≠ j → ContinuumSep.sepBy (d0 / 2) (H i) (H j) :=
      fun H hH i j hij => sepBy_half (hs0 i j hij) hw (hH i) (hH j)
    have famsep : ∀ H : ι → TestFn, (∀ i, SuppIn (g i) w (H i)) →
        ContinuumSep.FamSep (d0 / 2) (fun i => (op (b i), H i)) :=
      fun H hH i j hij => good_sep H hH i j hij
    have step : ∀ s : Finset ι, |S (hyb s) - S g|
        ≤ ∑ a ∈ s, K * (l1 (tDiff (g a) w) * ∏ i ∈ Finset.univ.erase a, l1 (g i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : hyb ∅ = g := funext fun i => by simp [hyb]
        rw [e, sub_self, abs_zero, Finset.sum_empty]
      | insert a s ha ih =>
        have e1 : hyb (insert a s)
            = Function.update (hyb s) a (testAdd (g a) (tDiff (g a) w)) := by
          funext i
          by_cases hi : i = a
          · subst hi
            rw [Function.update_self]
            simp only [hyb, if_pos (Finset.mem_insert_self i s)]
            refine Subtype.ext (funext fun y => ?_)
            show (g i).1 (y - w) = (g i).1 y + ((g i).1 (y - w) + -1 * (g i).1 y)
            ring
          · rw [Function.update_of_ne hi]
            simp only [hyb, Finset.mem_insert, hi, false_or]
        have e2 : Function.update (hyb s) a (g a) = hyb s := by
          funext i
          by_cases hi : i = a
          · subst hi
            rw [Function.update_self]
            simp only [hyb, if_neg ha]
          · rw [Function.update_of_ne hi]
        have hadd : S (Function.update (hyb s) a (testAdd (g a) (tDiff (g a) w)))
            = S (Function.update (hyb s) a (g a))
              + S (Function.update (hyb s) a (tDiff (g a) w)) :=
          contS_update_testAdd hN Z hZ hD (fun i => op (b i)) (hyb s) a (g a) (tDiff (g a) w) hδ
            (famsep _ (supp_upd _ _ _ (supp_hyb s) (supp_g a)))
            (famsep _ (supp_upd _ _ _ (supp_hyb s) (supp_d a)))
            (famsep _ (supp_upd _ _ _ (supp_hyb s) (supp_ad a)))
        have hT : |S (Function.update (hyb s) a (tDiff (g a) w))|
            ≤ K * ∏ i, l1 (Function.update (hyb s) a (tDiff (g a) w) i) :=
          abs_contS_le_of_os0 hN op Z hαγ b (Function.update (hyb s) a (tDiff (g a) w)) hδ hδ1
            (cont_upd _ _ _ (cont_hyb s) (cont_d a))
            (good_sep _ (supp_upd _ _ _ (supp_hyb s) (supp_d a)))
        have hprod : ∏ i, l1 (Function.update (hyb s) a (tDiff (g a) w) i)
            = l1 (tDiff (g a) w) * ∏ i ∈ Finset.univ.erase a, l1 (g i) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
          by_cases h : i ∈ s
          · simp only [hyb, if_pos h]
            exact l1_translate (g i) w
          · simp only [hyb, if_neg h]
        rw [e1, hadd, e2, Finset.sum_insert ha]
        have htri : |S (hyb s) + S (Function.update (hyb s) a (tDiff (g a) w)) - S g|
            ≤ |S (Function.update (hyb s) a (tDiff (g a) w))| + |S (hyb s) - S g| := by
          have h4 := abs_add_le (S (Function.update (hyb s) a (tDiff (g a) w))) (S (hyb s) - S g)
          calc _ = |S (Function.update (hyb s) a (tDiff (g a) w)) + (S (hyb s) - S g)| := by
                congr 1
                ring
            _ ≤ _ := h4
        refine htri.trans (add_le_add ?_ ih)
        calc |S (Function.update (hyb s) a (tDiff (g a) w))|
            ≤ K * ∏ i, l1 (Function.update (hyb s) a (tDiff (g a) w) i) := hT
          _ = K * (l1 (tDiff (g a) w) * ∏ i ∈ Finset.univ.erase a, l1 (g i)) := by rw [hprod]
    have e : hyb Finset.univ = fun i => (g i).translate w :=
      funext fun i => by simp [hyb, g']
    have h5 := step Finset.univ
    rwa [e] at h5
  have hR : Tendsto (fun w => ∑ a, K * (l1 (tDiff (g a) w) * ∏ i ∈ Finset.univ.erase a, l1 (g i)))
      (𝓝 0) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι) (fun a _ =>
      ((tendsto_l1_tDiff (g a) (hc a)).mul_const (∏ i ∈ Finset.univ.erase a, l1 (g i))).const_mul K)
    have e : ∑ a ∈ (Finset.univ : Finset ι), K * ((0 : ℝ) * ∏ i ∈ Finset.univ.erase a, l1 (g i))
        = 0 := by simp
    rw [e] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hR
  filter_upwards [Metric.ball_mem_nhds (0 : Fin 4 → ℝ) hδ] with w hw
  have hw' : ‖w‖ < d0 / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hw
  rw [Real.norm_eq_abs]
  exact hmain w (fun μ => by
    have h6 := norm_le_pi_norm w μ
    rw [Real.norm_eq_abs] at h6
    linarith)

/-! ## 6. `TransContT` -/

/-- **`TransContT` for the mixing of a per-field factor**, from `hZ`, `DiagBoundSep` at `Z` and
`OS0Own`. -/
theorem transContT_of_os0 (hN : N ≠ 0) {B : Type} [Fintype B] (op : B → LField (MassGap.SUN.SU N))
    (m : Idx4 → B → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0) (h0 : OS0Own hN op Z) :
    TransContT hN (mixOfZ B op m Z) := by
  intro ι _ _ F hF
  have key : ∀ G : ι → TDatum, Adm G →
      Tendsto (fun w => contT hN (mixOfZ B op m Z) (fun i => translateD w (G i))) (𝓝 0)
        (𝓝 (contT hN (mixOfZ B op m Z) G)) := by
    intro G hG
    obtain ⟨hc, d, hd, hs⟩ := hG
    have e : (fun w => contT hN (mixOfZ B op m Z) (fun i => translateD w (G i)))
        = fun w => ∑ b : ι → B, (∏ i, coefC m (G i).1 (b i))
          * contS hN (Renorm.connected hN Z) (fun i => (op (b i), (G i).2.translate w)) :=
      funext fun w => contT_mixOfZ hN op m Z hZ hD _ (adm_translate ⟨hc, d, hd, hs⟩ w)
    rw [e, contT_mixOfZ hN op m Z hZ hD G ⟨hc, d, hd, hs⟩]
    exact tendsto_finsetSum _ fun b _ =>
      (tendsto_contS_translate hN op Z hZ hD h0 b (fun i => (G i).2) hc hd hs).const_mul _
  rw [continuous_iff_continuousAt]
  intro v0
  have hG : Adm (fun i => translateD v0 (F i)) := adm_translate hF v0
  have hsub : Tendsto (fun v : Fin 4 → ℝ => v - v0) (𝓝 v0) (𝓝 0) := by
    have h : Tendsto (fun v : Fin 4 → ℝ => v - v0) (𝓝 v0) (𝓝 (v0 - v0)) :=
      (continuous_id.sub continuous_const).tendsto v0
    rwa [sub_self] at h
  have h := (key _ hG).comp hsub
  show Tendsto (fun v => contT hN (mixOfZ B op m Z) (fun i => translateD v (F i))) (𝓝 v0)
    (𝓝 (contT hN (mixOfZ B op m Z) (fun i => translateD v0 (F i))))
  refine h.congr (fun v => ?_)
  show contT hN (mixOfZ B op m Z) (fun i => translateD (v - v0) (translateD v0 (F i)))
    = contT hN (mixOfZ B op m Z) (fun i => translateD v (F i))
  congr 1
  funext i
  show ((F i).1, ((F i).2.translate v0).translate (v - v0)) = ((F i).1, (F i).2.translate v)
  rw [TestFn.translate_translate, add_sub_cancel]

/-! ## 7. The capstone without `hTC` -/

/-- **`ClayStatementAt` from the inputs of `CutSU.clayStatementAt_of_inputs'` without `hTC`.** The
continuity in the translation is `transContT_of_os0` from `hZ`, `hD`, `h0`. -/
theorem clayStatementAt_of_inputs''' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z)
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (w : TSep 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) (mixOfZ B op m Z) w)
    (hnt : ∃ u ∈ HLs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w,
      inner ℂ (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.vac u = 0 ∧ u ≠ 0)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  CutSU.clayStatementAt_of_inputs' hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar op m Z hZ hD hRie
    b0 κ htr hop hZtie h0 (transContT_of_os0 hN op m Z hZ hD h0) hCov G hK hAF hNG hND w hL hnt
    Cs wC hCT hWard hCD hCO hLC hTI

/-- **`ClayStatementAt` from the inputs of `SUInputs.clayStatementAt_of_inputs''` without `hTC`.**
The continuity in the translation is `transContT_of_os0` from `hZ`, `hD`, `h0`. -/
theorem clayStatementAt_of_inputs_TC (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z)
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (w : TSep 0 → (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) (mixOfZ B op m Z) w)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (SUInputs.obsX' hN2 hN W ht hU hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  SUInputs.clayStatementAt_of_inputs'' hN2 hN W ht hU hphys hNT hfar op m Z hZ hD hRie b0 κ htr hop
    hZtie h0 (transContT_of_os0 hN op m Z hZ hD h0) hCov G hK hAF hNG hND w hL Cs wC hCT hWard
    hCD hCO hLC hTI

end MassGap.TransContSU

end

#print axioms MassGap.TransContSU.sepBy_half
#print axioms MassGap.TransContSU.tendsto_latSkR_connected
#print axioms MassGap.TransContSU.latSkR_update
#print axioms MassGap.TransContSU.contS_update_testAdd
#print axioms MassGap.TransContSU.abs_contS_le_of_os0
#print axioms MassGap.TransContSU.l1_translate
#print axioms MassGap.TransContSU.tendsto_l1_tDiff
#print axioms MassGap.TransContSU.tendsto_contS_translate
#print axioms MassGap.TransContSU.transContT_of_os0
#print axioms MassGap.TransContSU.clayStatementAt_of_inputs'''
#print axioms MassGap.TransContSU.clayStatementAt_of_inputs_TC
