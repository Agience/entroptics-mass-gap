import Mathlib
import MassGap.MixConvRP
import MassGap.ClaySUBest

/-!
# MassGap.InputsTriage — what the three-point input and the composites' convergence clause still ask

`MixConvRP.clayStatementAt_SU_reflAvg'` and `ClaySUBest.clayStatementAt_SU_best` take
`hObs : NonGaussLink.ObsThreePoint hN z`: a separated triple of continuous test functions whose
connected three-point reading of the observer's field at the factor `z_sc` lies eventually in
`[κ, C]`, `κ > 0`, in absolute value. Both capstones also take `hCO : CompOS` of the built composites.
This module shows that, given `hCO`, the input `hObs` asks exactly for the target clause
`NonGaussianT` and nothing more, and gives both capstones with the weaker input.

## 1. The convergence clause of `CompOS` is a bound

`convC_iff_boundC`: `ConvC hN C`, the first conjunct of `CompOS`, holds exactly when the lattice
reading of every admissible family of composites is bounded on some set of `ultra` (`BoundC`).
`convC_of_boundAtTop`: an eventual bound along `atTop` is enough. Proof: a bounded real sequence
converges along an ultrafilter (`MixConvRP.exists_tendsto_ultra_of_ultra`); a convergent one is
eventually within `1` of its limit.

## 2. The three-point input

* `ObsLower hN z`: a separated triple of continuous test functions and `κ > 0` with
  `κ ≤ |obsRead hN z k (a, b, c)|` on a set of `ultra`. It is the lower half of `ObsThreePoint`,
  read along `ultra` rather than `atTop`; `obsLower_of_obsThreePoint` proves it from `ObsThreePoint`.
* `sepConv_build`: `SepConv (rhoD f z)` from the first conjunct of `CompOS` of the built composites
  (`CompReduce.sepConv_of_comp` at `eI`, `CompositesBuild.build_he2`).
* `tendsto_trace3`: under `SepConv (rhoD f z)`, `(N/16)³ · obsRead hN z k (a, b, c)` converges along
  `ultra` to `cum3T (rhoD f z) a b c` on every continuous separated triple.
* `nonGaussianT_rhoD_iff_lower`: under `SepConv (rhoD f z)`,
  `NonGaussianT hN (rhoD f z) ↔ ObsLower hN z`.

So, given `hCO`, the upper bound `C` of `ObsThreePoint` is not needed (the reading converges along
`ultra`), and its reading along `atTop` is not needed either: `ObsLower` reads along `ultra`. What is
left is `NonGaussianT` itself, a clause of `ClayData`. Under `SepConv (rhoD f z)` the equivalence also
shows that any statement giving `NonGaussianT` gives `ObsLower`: the input is the clause.

## 3. The capstones with `ObsLower`

* `clayStatementAt_SU_reflAvg_low`: `MixConvRP.clayStatementAt_SU_reflAvg'` with `ObsLower` in place of
  `hObs`. Inputs: `hU`, `hphys`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hLow`,
  `hWard`, `hCO`, `hA`.
* `clayStatementAt_SU_best_low`: `ClaySUBest.clayStatementAt_SU_best` with `ObsLower` in place of
  `hObs`. Inputs: those of `clayStatementAt_SU_best` with `hLow` for `hObs`.

Each has the same inputs as the original capstone, with `ObsLower` for `hObs`; `ObsThreePoint` implies
`ObsLower` (`obsLower_of_obsThreePoint`), and by `nonGaussianT_rhoD_iff_lower` `ObsLower` is
equivalent, given `hCO`, to the target clause `NonGaussianT`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `3` the number of insertions; `16` the trace coefficient of `coefC_mD`; `1`
the margin around a limit; `2` the halving of a non-zero limit; `0` the plane, the signs and the
Gaussian value.
-/

noncomputable section

namespace MassGap.InputsTriage

open Filter
open scoped Topology

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayData MassGap.CompositesBuild

variable {N : ℕ}

/-! ## 1. `ConvC` is a bound -/

section Conv

/-- **The bound form of `ConvC`**: on every admissible family of composites the lattice reading is
bounded on some set of `ultra`. DERIVED: no numeral. -/
def BoundC (hN : N ≠ 0) (C : Composites N) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum C), Adm F →
    ∃ B : ℝ, ∀ᶠ k in (ultra : Filter ℕ), |latC hN C k F| ≤ B

/-- **`ConvC` holds exactly when every admissible reading is bounded on a set of `ultra`.**

DERIVED: `1` the margin around the limit. -/
theorem convC_iff_boundC (hN : N ≠ 0) (C : Composites N) : ConvC hN C ↔ BoundC hN C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  constructor
  · intro h ι _ _ F hF
    refine ⟨|contC hN C F| + 1, ?_⟩
    exact ((h ι F hF).abs.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ hk => hk.le
  · intro h ι _ _ F hF
    obtain ⟨B, hB⟩ := h ι F hF
    obtain ⟨x, hx⟩ := MixConvRP.exists_tendsto_ultra_of_ultra _ B hB
    show Tendsto _ _ (𝓝 (limUnder (ultra : Filter ℕ) (fun k => latC hN C k F)))
    rw [hx.limUnder_eq]
    exact hx

/-- **`ConvC` from an eventual bound along `atTop`** on every admissible family. DERIVED: no
numeral. -/
theorem convC_of_boundAtTop (hN : N ≠ 0) (C : Composites N)
    (h : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum C), Adm F →
      ∃ B : ℝ, ∀ᶠ k in atTop, |latC hN C k F| ≤ B) : ConvC hN C :=
  (convC_iff_boundC hN C).2 fun ι _ _ F hF =>
    let ⟨B, hB⟩ := h ι F hF
    ⟨B, hB.filter_mono ultra_le⟩

end Conv

/-! ## 2. The three-point input -/

section Three

/-- **The lower half of `ObsThreePoint`, along `ultra`.** A triple of continuous, pairwise
`d`-separated test functions and `κ > 0` with `κ ≤ |obsRead hN z k (a, b, c)|` on a set of `ultra`.

DERIVED: `0` the signs of `κ` and of the separation. -/
def ObsLower (hN : N ≠ 0) (z : Chan → ℕ → ℝ) : Prop :=
  ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
    ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
        ∧ ContinuumSep.sepBy d b c)
    ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ k in (ultra : Filter ℕ),
        κ ≤ |NonGaussLink.obsRead hN z k ![a, b, c]|

/-- **`ObsThreePoint` gives `ObsLower`.** DERIVED: no numeral. -/
theorem obsLower_of_obsThreePoint (hN : N ≠ 0) (z : Chan → ℕ → ℝ)
    (h : NonGaussLink.ObsThreePoint hN z) : ObsLower hN z := by
  obtain ⟨a, b, c, ha, hb, hc, hsep, κ, _C, hκ, hev⟩ := h
  exact ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, (hev.filter_mono ultra_le).mono fun _ hk => hk.1⟩

/-- **`SepConv (rhoD f z)` from `CompOS` of the built composites** (its first conjunct).
DERIVED: no numeral. -/
theorem sepConv_build (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N))
    (bareO : Ix0 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (hCO : CompOS hN (build (rhoD f z) bareO)) : SepConv hN (rhoD f z) :=
  CompReduce.sepConv_of_comp hN (rhoD f z) (build (rhoD f z) bareO) eI
    (fun k α => build_he2 (rhoD f z) bareO k α) hCO.1

/-- A continuous separated triple, as a family of three trace insertions, is admissible.
DERIVED: `3` the number of insertions. -/
theorem adm_trace3 {a b c : TestFn} (ha : Continuous a.1) (hb : Continuous b.1)
    (hc : Continuous c.1)
    (hsep : ∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
        ∧ ContinuumSep.sepBy d b c) :
    Adm (fun i : Fin 3 => (trC, (![a, b, c] : Fin 3 → TestFn) i)) := by
  obtain ⟨d, hd, hab, hac, hbc⟩ := hsep
  refine ⟨fun i => ?_, d, hd, fun i j hij => ?_⟩
  · fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hab
    · exact hac
    · exact CompReduce.sepBy_symm hab
    · exact absurd rfl hij
    · exact hbc
    · exact CompReduce.sepBy_symm hac
    · exact CompReduce.sepBy_symm hbc
    · exact absurd rfl hij

/-- **The scaled three-point reading converges to `cum3T`** under `SepConv (rhoD f z)`, on every
continuous separated triple.

DERIVED: `3` the order; `16` as in `NonGaussLink.latT_trace_rhoD`. -/
theorem tendsto_trace3 (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (hS : SepConv hN (rhoD f z)) {a b c : TestFn} (ha : Continuous a.1) (hb : Continuous b.1)
    (hc : Continuous c.1)
    (hsep : ∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
        ∧ ContinuumSep.sepBy d b c) :
    Tendsto (fun k => ((N : ℝ) / 16) ^ 3 * NonGaussLink.obsRead hN z k ![a, b, c])
      (ultra : Filter ℕ) (𝓝 (cum3T hN (rhoD f z) a b c)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hT := hS (Fin 3) (fun i => (trC, (![a, b, c] : Fin 3 → TestFn) i))
    (adm_trace3 ha hb hc hsep)
  have e : (fun k => latT hN (rhoD f z) k (fun i => (trC, (![a, b, c] : Fin 3 → TestFn) i)))
      = fun k => ((N : ℝ) / 16) ^ 3 * NonGaussLink.obsRead hN z k ![a, b, c] :=
    funext fun k => NonGaussLink.latT_trace_rhoD hN f z k ![a, b, c]
  rw [e] at hT
  rw [NonGaussLink.cum3T_rhoD, hT.limUnder_eq]
  exact hT

/-- **`NonGaussianT` at `rhoD f z` from `ObsLower`**, under `SepConv (rhoD f z)`.

DERIVED: `0` the Gaussian value; `16`, `3` as in `tendsto_trace3`. -/
theorem nonGaussianT_rhoD_of_lower (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (hS : SepConv hN (rhoD f z)) (h : ObsLower hN z) :
    NonGaussianT hN (rhoD f z) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨a, b, c, ha, hb, hc, hsep, κ, hκ, hev⟩ := h
  refine ⟨a, b, c, ha, hb, hc, hsep, ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hq : 0 < ((N : ℝ) / 16) ^ 3 := pow_pos (div_pos hN0 (by norm_num)) 3
  have hT := tendsto_trace3 hN f z hS ha hb hc hsep
  have hle : ((N : ℝ) / 16) ^ 3 * κ ≤ |cum3T hN (rhoD f z) a b c| :=
    ge_of_tendsto hT.abs (hev.mono fun k hk => by
      show ((N : ℝ) / 16) ^ 3 * κ ≤ |((N : ℝ) / 16) ^ 3 * NonGaussLink.obsRead hN z k ![a, b, c]|
      rw [abs_mul, abs_of_pos hq]
      exact mul_le_mul_of_nonneg_left hk hq.le)
  intro h0
  rw [h0, abs_zero] at hle
  linarith [mul_pos hq hκ]

/-- **`ObsLower` from `NonGaussianT` at `rhoD f z`**, under `SepConv (rhoD f z)`: at the triple of
`NonGaussianT`, `κ = |cum3T| / (2 (N/16)³)`.

DERIVED: `2` the halving of the limit; `16`, `3` as in `tendsto_trace3`. -/
theorem obsLower_of_nonGaussianT (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (hS : SepConv hN (rhoD f z)) (h : NonGaussianT hN (rhoD f z)) :
    ObsLower hN z := by
  obtain ⟨a, b, c, ha, hb, hc, hsep, hne⟩ := h
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hq : 0 < ((N : ℝ) / 16) ^ 3 := pow_pos (div_pos hN0 (by norm_num)) 3
  have hx : 0 < |cum3T hN (rhoD f z) a b c| := abs_pos.mpr hne
  have hT := (tendsto_trace3 hN f z hS ha hb hc hsep).abs
  have hev := hT.eventually (lt_mem_nhds (half_lt_self hx))
  refine ⟨a, b, c, ha, hb, hc, hsep, |cum3T hN (rhoD f z) a b c| / 2 / ((N : ℝ) / 16) ^ 3,
    div_pos (half_pos hx) hq, hev.mono fun k hk => ?_⟩
  rw [div_le_iff₀ hq]
  have hk' : |cum3T hN (rhoD f z) a b c| / 2
      < |NonGaussLink.obsRead hN z k ![a, b, c]| * ((N : ℝ) / 16) ^ 3 := by
    have := hk
    simp only [abs_mul, abs_of_pos hq] at this
    linarith
  exact hk'.le

/-- **Under `SepConv (rhoD f z)`, `NonGaussianT` at `rhoD f z` is `ObsLower`.** DERIVED: no
numeral. -/
theorem nonGaussianT_rhoD_iff_lower (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (hS : SepConv hN (rhoD f z)) :
    NonGaussianT hN (rhoD f z) ↔ ObsLower hN z :=
  ⟨obsLower_of_nonGaussianT hN f z hS, nonGaussianT_rhoD_of_lower hN f z hS⟩

end Three

/-! ## 3. The capstones with `ObsLower` -/

section Capstone

open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.ObsLead MassGap.CompositeLink MassGap.ReflAvg

/-- **The reflection-averaged capstone with `ObsLower` for `ObsThreePoint`**:
`MixConvRP.clayStatementAt_SU_reflAvg'` with `NonGaussianT` from `ObsLower`
(`nonGaussianT_rhoD_of_lower`) and `SepConv` from `hCO` (`sepConv_build`).

The inputs: `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hLow`,
`hWard`, `hCO`, `hA`; `hK`, `hWard` read `rhoD (fR N) z`, and `hCO`, `hA` the averaged composites
`CbR N z`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_reflAvg_low (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hLow : ObsLower (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (mixKR hN2 W z r) (gramF hN2 W r)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hMC := MixConvRP.mixConvF_R hN2 W hU hphys z hCO
  obtain ⟨wC, hLC, hX⟩ := linkCPre_of_kernelsF hN2 W hU hphys (fR N) (bR N) z hCO
    (jointRPK_R hN2 W hU hphys z hCO hMC) hA hMC
  exact clayStatementAt_SU_data hN2 W ht hU hphys hfar (fR N) (bR N) z hz hzS hzP G hK hAF
    (nonGaussianT_rhoD_of_lower (ne_zero_of_two_le hN2) (fR N) z
      (sepConv_build (ne_zero_of_two_le hN2) (fR N) (bareD (fR N) (bR N)) z hCO) hLow)
    hWard (tiedB_R (ne_zero_of_two_le hN2)) hCO wC hLC hX

/-- **The best capstone with `ObsLower` for `ObsThreePoint`**:
`ClaySUBest.clayStatementAt_SU_best` with `NonGaussianT` from `ObsLower`
(`nonGaussianT_rhoD_of_lower`) and `SepConv` from `hCO` (`sepConv_build`). The other inputs are
those of `clayStatementAt_SU_best`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_best_low (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hLow : ObsLower (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (hJ : JointRPK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) (Cb N z) 0) (mixK hN2 W z r) (gramF hN2 W r))
    (hMC : MixConv hN2 W z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  obtain ⟨wC, hLC, hX⟩ := linkCPre_of_kernels hN2 W hU hphys z hCO hJ hA hMC
  exact clayStatementAt_SU_obs hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF
    (nonGaussianT_rhoD_of_lower (ne_zero_of_two_le hN2) (fT N) z
      (sepConv_build (ne_zero_of_two_le hN2) (fT N) (bareD (fT N) (bT N)) z hCO) hLow)
    hWard hCO wC hLC hX

end Capstone

end MassGap.InputsTriage

end

#print axioms MassGap.InputsTriage.convC_iff_boundC
#print axioms MassGap.InputsTriage.convC_of_boundAtTop
#print axioms MassGap.InputsTriage.obsLower_of_obsThreePoint
#print axioms MassGap.InputsTriage.sepConv_build
#print axioms MassGap.InputsTriage.adm_trace3
#print axioms MassGap.InputsTriage.tendsto_trace3
#print axioms MassGap.InputsTriage.nonGaussianT_rhoD_of_lower
#print axioms MassGap.InputsTriage.obsLower_of_nonGaussianT
#print axioms MassGap.InputsTriage.nonGaussianT_rhoD_iff_lower
#print axioms MassGap.InputsTriage.clayStatementAt_SU_reflAvg_low
#print axioms MassGap.InputsTriage.clayStatementAt_SU_best_low
