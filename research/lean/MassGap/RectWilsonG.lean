import Mathlib
import MassGap.RectWilson
import MassGap.GaugeWilson
import MassGap.TorusDoubling

/-!
# MassGap.RectWilsonG — the Wilson model of a gauge group `G` on a rectangular 4-torus, sliced

`RectWilson` with `SUN.SU N` replaced by a `GaugeGroup G` and `WilsonAction.wilsonDensity` by
`GaugeGroup.wilsonDensityG G`. The geometry (`RectWilson.TT`, `SpT`, `tsh`, `RSite`, `RLink`, `rbd`,
`join`, `eLink`, …) does not mention the group and is reused.

* `ZRG G L β`: the partition function on the torus with extents `L`, product Haar on the links.
* `measurePreserving_ΦG`: the slice coordinates carry `∏_t ∏ Haar` to the link Haar measure.
* `action_ΦG`: `S(Φ W) = Σ_t [sp(V_t) + 2 tp(A_t, V_t, V_{t+1})]`.
* `ZRG_eq_integral`: `ZRG` as an integral over cyclic sequences of slice configurations.
* `ZT_four_eqG`: `TorusDoubling.ZT G 4 (wilsonDensityG G) β n = ZRG G (fun _ => n) β`, by `rfl`.

Of the density the proofs use `wilsonDensityG_one` and `wilsonDensityG_inv`.

DERIVED (module-wide): `4` the dimension; `2` the two orientations of each temporal plaquette.
-/

namespace MassGap.RectWilsonG

open MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
  MassGap.RectWilson MassGap.GaugeGroup

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

section Transverse

variable (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)

/-- Spatial plaquette action of one slice. -/
noncomputable def spTG (V : SpT μ T → G) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ ν' : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    wilsonDensityG G (V (ν, y) * V (ν', tsh μ T ν y) * (V (ν, tsh μ T ν' y))⁻¹ * (V (ν', y))⁻¹)

/-- Temporal plaquette action between two slices, at axis configuration `A`. -/
noncomputable def tpTG (A : TT μ T → G) (V V' : SpT μ T → G) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    wilsonDensityG G (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹)

end Transverse

variable (L : Fin 4 → ℕ)

/-- The rectangular Wilson system of `G`. -/
noncomputable def sysRG : System G := wilsonSystem (rbd L) (wilsonDensityG G)

/-- The rectangular Wilson partition function of `G`. -/
noncomputable def ZRG (β : ℝ) : ℝ := (sysRG G L).partition (probHaar G) β

/-- At `d = 4` the torus partition function of `TorusDoubling` is `ZRG` at constant extents. -/
theorem ZT_four_eqG (β : ℝ) (n : ℕ) :
    TorusDoubling.ZT G 4 (wilsonDensityG G) β n = ZRG G (fun _ => n) β := rfl

variable {G L}

theorem hol_eqG (U : RLink L → G) (i j : Fin 4) (x : RSite L) :
    (sysRG G L).hol ((i, j), x) U
      = U (i, x) * U (j, rshift L i x) * (U (i, rshift L j x))⁻¹ * (U (j, x))⁻¹ := by
  simp [sysRG, wilsonSystem, wilsonHol, rbd, mul_assoc]

variable (L) (μ : Fin 4)

/-- A cyclic sequence of slice configurations as a link configuration. -/
def ΦG (W : Fin (L μ) → SlIdx L μ → G) : RLink L → G :=
  fun l => W (eLink (L := L) (μ := μ) l).1 (eLink (L := L) (μ := μ) l).2

variable {L μ}

theorem ΦG_axis (W : Fin (L μ) → SlIdx L μ → G) (t : Fin (L μ)) (y : TS L μ) :
    ΦG L μ W (μ, join L μ t y) = W t (Sum.inl y) := by
  simp [ΦG, eLink, sIdx]

theorem ΦG_sp (W : Fin (L μ) → SlIdx L μ → G) (t : Fin (L μ)) (y : TS L μ)
    (ν : {j : Fin 4 // j ≠ μ}) :
    ΦG L μ W (ν.1, join L μ t y) = W t (Sum.inr (ν, y)) := by
  simp [ΦG, eLink, sIdx, ν.2]

variable (G) in
theorem measurePreserving_ΦG :
    MeasurePreserving (ΦG (G := G) L μ)
      (Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar G)
      (Measure.pi fun _ : RLink L => probHaar G) := by
  have h1 := SliceTrace.measurePreserving_sigmaUncurry (κ := Fin (L μ))
    (B := fun _ => SlIdx L μ) (Ω := G) (probHaar G)
  have h2 := measurePreserving_arrowCongr' (fun _ : (Σ _ : Fin (L μ), SlIdx L μ) => probHaar G)
    (fun _ : RLink L => probHaar G)
    ((eLink (L := L) (μ := μ)).trans (Equiv.sigmaEquivProd _ _).symm).symm
    (MeasurableEquiv.refl G) (fun _ => MeasurePreserving.id _)
  have hc := h2.comp h1
  convert hc using 1
  funext W l
  simp [ΦG, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Sigma.uncurry]

variable (L μ)

/-- Spatial plaquette action of one slice. -/
noncomputable abbrev spG (V : SpIdx L μ → G) : ℝ := spTG G μ (tr L μ) V

/-- Temporal plaquette action between two slices. -/
noncomputable abbrev tpG (A : TS L μ → G) (V V' : SpIdx L μ → G) : ℝ :=
  tpTG G μ (tr L μ) A V V'

variable {L μ}

/-- The axis part of a slice configuration. -/
def axisOfG (X : SlIdx L μ → G) : TS L μ → G := fun y => X (Sum.inl y)
/-- The spatial part of a slice configuration. -/
def spOfG (X : SlIdx L μ → G) : SpIdx L μ → G := fun p => X (Sum.inr p)

theorem hol_μμG (U : RLink L → G) (x : RSite L) :
    (sysRG G L).hol ((μ, μ), x) U = 1 := by
  rw [hol_eqG]; group

section Slice

variable (W : Fin (L μ) → SlIdx L μ → G) (t : Fin (L μ)) (y : TS L μ)
  (ν : {j : Fin 4 // j ≠ μ})

theorem hol_μνG :
    (sysRG G L).hol ((μ, ν.1), join L μ t y) (ΦG L μ W)
      = axisOfG (W t) y * spOfG (W (finRotate (L μ) t)) (ν, y)
        * (axisOfG (W t) (tshift L μ ν y))⁻¹ * (spOfG (W t) (ν, y))⁻¹ := by
  rw [hol_eqG, rshift_join_self, rshift_join_ne, ΦG_axis, ΦG_axis, ΦG_sp, ΦG_sp]
  rfl

theorem hol_νμG :
    (sysRG G L).hol ((ν.1, μ), join L μ t y) (ΦG L μ W)
      = (axisOfG (W t) y * spOfG (W (finRotate (L μ) t)) (ν, y)
        * (axisOfG (W t) (tshift L μ ν y))⁻¹ * (spOfG (W t) (ν, y))⁻¹)⁻¹ := by
  rw [hol_eqG, rshift_join_self, rshift_join_ne, ΦG_axis, ΦG_axis, ΦG_sp, ΦG_sp]
  simp only [axisOfG, spOfG]
  group

theorem hol_ννG (ν' : {j : Fin 4 // j ≠ μ}) :
    (sysRG G L).hol ((ν.1, ν'.1), join L μ t y) (ΦG L μ W)
      = spOfG (W t) (ν, y) * spOfG (W t) (ν', tshift L μ ν y)
        * (spOfG (W t) (ν, tshift L μ ν' y))⁻¹ * (spOfG (W t) (ν', y))⁻¹ := by
  rw [hol_eqG, rshift_join_ne, rshift_join_ne, ΦG_sp, ΦG_sp, ΦG_sp, ΦG_sp]
  rfl

theorem slice_sumG :
    ∑ i : Fin 4, ∑ j : Fin 4, ∑ y : TS L μ,
      wilsonDensityG G ((sysRG G L).hol ((i, j), join L μ t y) (ΦG L μ W))
      = spG L μ (spOfG (W t))
        + 2 * tpG L μ (axisOfG (W t)) (spOfG (W t)) (spOfG (W (finRotate (L μ) t))) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ μ, Fintype.sum_eq_add_sum_subtype_ne _ μ]
  simp_rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => ∑ y : TS L μ,
    wilsonDensityG G ((sysRG G L).hol ((_, j), join L μ t y) (ΦG L μ W))) μ]
  simp only [hol_μμG, wilsonDensityG_one, Finset.sum_const_zero, zero_add,
    hol_μνG, hol_νμG, wilsonDensityG_inv, hol_ννG, Finset.sum_add_distrib]
  unfold spG tpG spTG tpTG
  ring

end Slice

theorem action_ΦG (W : Fin (L μ) → SlIdx L μ → G) :
    (sysRG G L).action (ΦG L μ W) = ∑ t, (spG L μ (spOfG (W t))
      + 2 * tpG L μ (axisOfG (W t)) (spOfG (W t)) (spOfG (W (finRotate (L μ) t)))) := by
  have hsite : ∀ (F : RSite L → ℝ), ∑ x, F x = ∑ t : Fin (L μ), ∑ y : TS L μ, F (join L μ t y) := by
    intro F
    rw [← Fintype.sum_prod_type', ← (siteEquiv (L := L) (μ := μ)).sum_comp]
    rfl
  set D : Fin 4 → Fin 4 → RSite L → ℝ := fun i j x =>
    wilsonDensityG G ((sysRG G L).hol ((i, j), x) (ΦG L μ W))
  calc (sysRG G L).action (ΦG L μ W) = ∑ i, ∑ j, ∑ x, D i j x := by
        unfold System.action
        change ∑ q : RPlaq L, wilsonDensityG G ((sysRG G L).hol q (ΦG L μ W)) = _
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, ∑ t, ∑ y, D i j (join L μ t y) := by simp_rw [hsite]
    _ = ∑ i, ∑ t, ∑ j, ∑ y, D i j (join L μ t y) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, ∑ y, D i j (join L μ t y) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => slice_sumG W t

variable (G L) in
theorem continuous_boltzRG (β : ℝ) : Continuous ((sysRG G L).boltz β) := by
  show Continuous fun U => Real.exp (-β * (sysRG G L).action U)
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  show Continuous fun U => ∑ p : RPlaq L, wilsonDensityG G (wilsonHol (rbd L) p U)
  exact continuous_finsetSum _ (fun p _ =>
    continuous_wilsonDensityG.comp (GibbsPositive.continuous_hol (rbd L) p))

/-- `ZRG` as an integral over cyclic sequences of slice configurations. -/
theorem ZRG_eq_integral (β : ℝ) :
    ZRG G L β = ∫ W : Fin (L μ) → SlIdx L μ → G, ∏ t, Real.exp (-β * (spG L μ (spOfG (W t))
      + 2 * tpG L μ (axisOfG (W t)) (spOfG (W t)) (spOfG (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar G) := by
  have hmp := measurePreserving_ΦG G (L := L) (μ := μ)
  unfold ZRG System.partition System.vol
  change ∫ U : RLink L → G, (sysRG G L).boltz β U
      ∂(Measure.pi fun _ : RLink L => probHaar G) = _
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (continuous_boltzRG G L β).measurable.aestronglyMeasurable]
  congr 1; funext W
  unfold System.boltz
  rw [action_ΦG W, Finset.mul_sum, Real.exp_sum]

end MassGap.RectWilsonG

#print axioms MassGap.RectWilsonG.ZT_four_eqG
#print axioms MassGap.RectWilsonG.measurePreserving_ΦG
#print axioms MassGap.RectWilsonG.action_ΦG
#print axioms MassGap.RectWilsonG.ZRG_eq_integral
