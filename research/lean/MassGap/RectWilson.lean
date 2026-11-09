import Mathlib
import MassGap.SliceTrace
import MassGap.Reflect
import MassGap.WilsonLattice
import MassGap.GibbsPositive

/-!
# MassGap.RectWilson — the Wilson model on a rectangular 4-torus, sliced along one direction

`ZR L N β` is the `SU(N)` Wilson partition function on the periodic 4-torus with extents
`L : Fin 4 → ℕ`, in the tree's convention: `LatticeGauge.System` with link type `Fin 4 × Site`,
plaquette type `(Fin 4 × Fin 4) × Site` (ordered pairs, each plane counted twice, diagonal
included), holonomy along the boundary word `rbd` (the hypercubic `WilsonHypercubic.bd` with the
neighbour taken by `finRotate` in each coordinate), density `WilsonAction.wilsonDensity`, and the
product Haar probability measure over links. For `L` constant this is `WilsonHypercubic.sysWilson`.

For a direction `μ`, a site is a pair (time `t : Fin (L μ)`, transverse site `y`), `join t y`, and a
link configuration is a cyclic sequence of slice configurations `W : Fin (L μ) → (TS ⊕ SpIdx → SU N)`
— axis links (direction `μ`) and spatial links of each time slice — through `Φ` (`eLink`).

* `measurePreserving_Φ` — `Φ` carries `∏_t ∏ Haar` to the link Haar measure.
* `action_Φ` — `S(Φ W) = Σ_t [sp(V_t) + 2 tp(A_t, V_t, V_{t+1})]` (`N ≠ 0`), with `A_t, V_t` the axis
  and spatial parts of `W t`, `sp` the spatial plaquettes and `tp` the temporal ones.
* `ZR_eq_integral` — `ZR L N β = ∫ ∏_t exp(−β(sp V_t + 2 tp(A_t,V_t,V_{t+1}))) dW`.
-/

namespace MassGap.RectWilson

open MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge

/-! ## Transverse geometry, as a function of the transverse extents alone -/

section Transverse

variable (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)

/-- Transverse sites for transverse extents `T`. -/
abbrev TT : Type := ∀ j : {j : Fin 4 // j ≠ μ}, Fin (T j)
/-- Spatial link indices of one slice. -/
abbrev SpT : Type := {j : Fin 4 // j ≠ μ} × TT μ T

/-- One transverse step. -/
def tsh (ν : {j : Fin 4 // j ≠ μ}) (y : TT μ T) : TT μ T :=
  Function.update y ν (finRotate (T ν) (y ν))

/-- Spatial plaquette action of one slice. -/
noncomputable def spT {N : ℕ} (V : SpT μ T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ ν' : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    WilsonAction.wilsonDensity (V (ν, y) * V (ν', tsh μ T ν y) * (V (ν, tsh μ T ν' y))⁻¹
      * (V (ν', y))⁻¹)

/-- Temporal plaquette action between two slices, at axis configuration `A`. -/
noncomputable def tpT {N : ℕ} (A : TT μ T → SUN.SU N) (V V' : SpT μ T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ μ}, ∑ y : TT μ T,
    WilsonAction.wilsonDensity (A y * V' (ν, y) * (A (tsh μ T ν y))⁻¹ * (V (ν, y))⁻¹)

end Transverse

variable (L : Fin 4 → ℕ)

/-- The transverse extents of `L` in direction `μ`. -/
abbrev tr (μ : Fin 4) : {j : Fin 4 // j ≠ μ} → ℕ := fun j => L j.1

/-- Sites of the rectangular torus. -/
abbrev RSite : Type := ∀ i : Fin 4, Fin (L i)
/-- Links: a direction and the site the link leaves. -/
abbrev RLink : Type := Fin 4 × RSite L
/-- Plaquettes: an ordered pair of directions and a site. -/
abbrev RPlaq : Type := (Fin 4 × Fin 4) × RSite L

/-- One step in direction `i`, periodically. -/
def rshift (i : Fin 4) (x : RSite L) : RSite L := Function.update x i (finRotate (L i) (x i))

/-- The plaquette boundary word `U_i(x) U_j(x+i) U_i(x+j)⁻¹ U_j(x)⁻¹`. -/
def rbd (q : RPlaq L) : List (RLink L × Bool) :=
  [((q.1.1, q.2), true), ((q.1.2, rshift L q.1.1 q.2), true),
   ((q.1.1, rshift L q.1.2 q.2), false), ((q.1.2, q.2), false)]

/-- The rectangular Wilson system. -/
noncomputable def sysR (N : ℕ) : System (SUN.SU N) :=
  wilsonSystem (rbd L) (WilsonAction.wilsonDensity (N := N))

/-- The rectangular Wilson partition function. -/
noncomputable def ZR (N : ℕ) (β : ℝ) : ℝ := (sysR L N).partition (probHaar (SUN.SU N)) β

theorem hol_eq {N : ℕ} (U : RLink L → SUN.SU N) (i j : Fin 4) (x : RSite L) :
    (sysR L N).hol ((i, j), x) U
      = U (i, x) * U (j, rshift L i x) * (U (i, rshift L j x))⁻¹ * (U (j, x))⁻¹ := by
  simp [sysR, wilsonSystem, wilsonHol, rbd, mul_assoc]

/-! ## Slicing along `μ` -/

variable (μ : Fin 4)

/-- Transverse sites. -/
abbrev TS : Type := TT μ (tr L μ)
/-- Spatial link indices of one slice. -/
abbrev SpIdx : Type := SpT μ (tr L μ)
/-- Link indices of one slice: axis links (`inl`) and spatial links (`inr`). -/
abbrev SlIdx : Type := TS L μ ⊕ SpIdx L μ

/-- The site with time `t` and transverse site `y`. -/
def join (t : Fin (L μ)) (y : TS L μ) : RSite L :=
  fun i => if h : i = μ then h ▸ t else y ⟨i, h⟩

/-- The transverse part of a site. -/
def perp (x : RSite L) : TS L μ := fun j => x j.1

/-- One transverse step. -/
abbrev tshift (ν : {j : Fin 4 // j ≠ μ}) (y : TS L μ) : TS L μ := tsh μ (tr L μ) ν y

variable {L μ}

@[simp] theorem join_self (t : Fin (L μ)) (y : TS L μ) : join L μ t y μ = t := by simp [join]

@[simp] theorem join_ne (t : Fin (L μ)) (y : TS L μ) (j : {j : Fin 4 // j ≠ μ}) :
    join L μ t y j.1 = y j := by simp [join, j.2]

@[simp] theorem perp_join (t : Fin (L μ)) (y : TS L μ) : perp L μ (join L μ t y) = y := by
  funext j; simp [perp]

theorem join_perp (x : RSite L) : join L μ (x μ) (perp L μ x) = x := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [join, h, perp]

theorem rshift_join_self (t : Fin (L μ)) (y : TS L μ) :
    rshift L μ (join L μ t y) = join L μ (finRotate (L μ) t) y := by
  funext i
  by_cases h : i = μ
  · subst h; simp [rshift]
  · rw [rshift, Function.update_of_ne h]
    simp [join, h]

theorem rshift_join_ne (t : Fin (L μ)) (y : TS L μ) (ν : {j : Fin 4 // j ≠ μ}) :
    rshift L ν.1 (join L μ t y) = join L μ t (tshift L μ ν y) := by
  obtain ⟨ν, hν⟩ := ν
  funext i
  by_cases h : i = μ
  · subst h
    rw [rshift, Function.update_of_ne (Ne.symm hν)]
    simp
  · by_cases hi : i = ν
    · subst hi
      simp [rshift, join, h, tshift, tsh]
    · rw [rshift, Function.update_of_ne hi]
      have hne : (⟨i, h⟩ : {j : Fin 4 // j ≠ μ}) ≠ ⟨ν, hν⟩ := fun e => hi (congrArg Subtype.val e)
      simp [join, h, tshift, tsh, Function.update_of_ne hne]

/-- Time and transverse site, as an equivalence. -/
def siteEquiv : Fin (L μ) × TS L μ ≃ RSite L where
  toFun p := join L μ p.1 p.2
  invFun x := (x μ, perp L μ x)
  left_inv p := by simp
  right_inv x := join_perp x

/-- The slice index of a link. -/
def sIdx (ν : Fin 4) (y : TS L μ) : SlIdx L μ :=
  if h : ν = μ then Sum.inl y else Sum.inr (⟨ν, h⟩, y)

/-- Links as (time, slice index). -/
def eLink : RLink L ≃ Fin (L μ) × SlIdx L μ where
  toFun l := (l.2 μ, sIdx l.1 (perp L μ l.2))
  invFun p := match p.2 with
    | Sum.inl y => (μ, join L μ p.1 y)
    | Sum.inr (ν, y) => (ν.1, join L μ p.1 y)
  left_inv l := by
    obtain ⟨ν, x⟩ := l
    by_cases h : ν = μ
    · subst h; simp [sIdx, join_perp]
    · simp [sIdx, h, join_perp]
  right_inv p := by
    obtain ⟨t, s⟩ := p
    rcases s with y | ⟨ν, y⟩
    · simp [sIdx]
    · simp [sIdx, ν.2]

variable (L μ)

/-- A cyclic sequence of slice configurations as a link configuration. -/
def Φ {N : ℕ} (W : Fin (L μ) → SlIdx L μ → SUN.SU N) : RLink L → SUN.SU N :=
  fun l => W (eLink (L := L) (μ := μ) l).1 (eLink (L := L) (μ := μ) l).2

variable {L μ}

theorem Φ_axis {N : ℕ} (W : Fin (L μ) → SlIdx L μ → SUN.SU N) (t : Fin (L μ)) (y : TS L μ) :
    Φ L μ W (μ, join L μ t y) = W t (Sum.inl y) := by
  simp [Φ, eLink, sIdx]

theorem Φ_sp {N : ℕ} (W : Fin (L μ) → SlIdx L μ → SUN.SU N) (t : Fin (L μ)) (y : TS L μ)
    (ν : {j : Fin 4 // j ≠ μ}) :
    Φ L μ W (ν.1, join L μ t y) = W t (Sum.inr (ν, y)) := by
  simp [Φ, eLink, sIdx, ν.2]

theorem measurePreserving_Φ (N : ℕ) :
    MeasurePreserving (Φ L μ (N := N))
      (Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  have h1 := SliceTrace.measurePreserving_sigmaUncurry (κ := Fin (L μ))
    (B := fun _ => SlIdx L μ) (Ω := SUN.SU N) (probHaar (SUN.SU N))
  have e : RLink L ≃ Σ _ : Fin (L μ), SlIdx L μ :=
    (eLink (L := L) (μ := μ)).trans (Equiv.sigmaEquivProd _ _).symm
  have h2 := measurePreserving_arrowCongr' (fun _ : (Σ _ : Fin (L μ), SlIdx L μ) => probHaar (SUN.SU N))
    (fun _ : RLink L => probHaar (SUN.SU N))
    ((eLink (L := L) (μ := μ)).trans (Equiv.sigmaEquivProd _ _).symm).symm
    (MeasurableEquiv.refl (SUN.SU N)) (fun _ => MeasurePreserving.id _)
  have hc := h2.comp h1
  convert hc using 1
  funext W l
  simp [Φ, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Sigma.uncurry]

/-! ## The action in slice variables -/

variable (L μ)

/-- Spatial plaquette action of one slice. -/
noncomputable abbrev sp {N : ℕ} (V : SpIdx L μ → SUN.SU N) : ℝ := spT μ (tr L μ) V

/-- Temporal plaquette action between two slices. -/
noncomputable abbrev tp {N : ℕ} (A : TS L μ → SUN.SU N) (V V' : SpIdx L μ → SUN.SU N) : ℝ :=
  tpT μ (tr L μ) A V V'

variable {L μ}

theorem wilsonDensity_inv {N : ℕ} (g : SUN.SU N) :
    WilsonAction.wilsonDensity g⁻¹ = WilsonAction.wilsonDensity g := by
  unfold WilsonAction.wilsonDensity
  congr 2
  have hg : ((g⁻¹ : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = star (g : Matrix (Fin N) (Fin N) ℂ) := by
    rfl
  rw [hg, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp

/-- The axis part of a slice configuration. -/
def axisOf {N : ℕ} (X : SlIdx L μ → SUN.SU N) : TS L μ → SUN.SU N := fun y => X (Sum.inl y)
/-- The spatial part of a slice configuration. -/
def spOf {N : ℕ} (X : SlIdx L μ → SUN.SU N) : SpIdx L μ → SUN.SU N := fun p => X (Sum.inr p)

theorem hol_μμ {N : ℕ} (U : RLink L → SUN.SU N) (x : RSite L) :
    (sysR L N).hol ((μ, μ), x) U = 1 := by
  rw [hol_eq]; group

section Slice

variable {N : ℕ} (W : Fin (L μ) → SlIdx L μ → SUN.SU N) (t : Fin (L μ)) (y : TS L μ)
  (ν : {j : Fin 4 // j ≠ μ})

theorem hol_μν :
    (sysR L N).hol ((μ, ν.1), join L μ t y) (Φ L μ W)
      = axisOf (W t) y * spOf (W (finRotate (L μ) t)) (ν, y)
        * (axisOf (W t) (tshift L μ ν y))⁻¹ * (spOf (W t) (ν, y))⁻¹ := by
  rw [hol_eq, rshift_join_self, rshift_join_ne, Φ_axis, Φ_axis, Φ_sp, Φ_sp]
  rfl

theorem hol_νμ :
    (sysR L N).hol ((ν.1, μ), join L μ t y) (Φ L μ W)
      = (axisOf (W t) y * spOf (W (finRotate (L μ) t)) (ν, y)
        * (axisOf (W t) (tshift L μ ν y))⁻¹ * (spOf (W t) (ν, y))⁻¹)⁻¹ := by
  rw [hol_eq, rshift_join_self, rshift_join_ne, Φ_axis, Φ_axis, Φ_sp, Φ_sp]
  simp only [axisOf, spOf]
  group

theorem hol_νν (ν' : {j : Fin 4 // j ≠ μ}) :
    (sysR L N).hol ((ν.1, ν'.1), join L μ t y) (Φ L μ W)
      = spOf (W t) (ν, y) * spOf (W t) (ν', tshift L μ ν y)
        * (spOf (W t) (ν, tshift L μ ν' y))⁻¹ * (spOf (W t) (ν', y))⁻¹ := by
  rw [hol_eq, rshift_join_ne, rshift_join_ne, Φ_sp, Φ_sp, Φ_sp, Φ_sp]
  rfl

theorem slice_sum (hN : N ≠ 0) :
    ∑ i : Fin 4, ∑ j : Fin 4, ∑ y : TS L μ,
      WilsonAction.wilsonDensity ((sysR L N).hol ((i, j), join L μ t y) (Φ L μ W))
      = sp L μ (spOf (W t))
        + 2 * tp L μ (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t))) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ μ, Fintype.sum_eq_add_sum_subtype_ne _ μ]
  simp_rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => ∑ y : TS L μ,
    WilsonAction.wilsonDensity ((sysR L N).hol ((_, j), join L μ t y) (Φ L μ W))) μ]
  simp only [hol_μμ, WilsonAction.wilsonDensity_one hN, Finset.sum_const_zero, zero_add,
    hol_μν, hol_νμ, wilsonDensity_inv, hol_νν, Finset.sum_add_distrib]
  unfold sp tp spT tpT
  ring

end Slice

theorem action_Φ {N : ℕ} (hN : N ≠ 0) (W : Fin (L μ) → SlIdx L μ → SUN.SU N) :
    (sysR L N).action (Φ L μ W) = ∑ t, (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))) := by
  have hsite : ∀ (F : RSite L → ℝ), ∑ x, F x = ∑ t : Fin (L μ), ∑ y : TS L μ, F (join L μ t y) := by
    intro F
    rw [← Fintype.sum_prod_type', ← (siteEquiv (L := L) (μ := μ)).sum_comp]
    rfl
  set D : Fin 4 → Fin 4 → RSite L → ℝ := fun i j x =>
    WilsonAction.wilsonDensity ((sysR L N).hol ((i, j), x) (Φ L μ W))
  calc (sysR L N).action (Φ L μ W) = ∑ i, ∑ j, ∑ x, D i j x := by
        unfold System.action
        change ∑ q : RPlaq L, WilsonAction.wilsonDensity ((sysR L N).hol q (Φ L μ W)) = _
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = ∑ i, ∑ j, ∑ t, ∑ y, D i j (join L μ t y) := by simp_rw [hsite]
    _ = ∑ i, ∑ t, ∑ j, ∑ y, D i j (join L μ t y) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, ∑ y, D i j (join L μ t y) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun t _ => slice_sum W t hN

theorem measurable_boltzR (N : ℕ) (β : ℝ) : Measurable ((sysR L N).boltz β) :=
  (GibbsPositive.continuous_boltz (N := N) (rbd L) β).measurable

/-- `ZR` as an integral over cyclic sequences of slice configurations. -/
theorem ZR_eq_integral {N : ℕ} (hN : N ≠ 0) (β : ℝ) :
    ZR L N β = ∫ W : Fin (L μ) → SlIdx L μ → SUN.SU N, ∏ t, Real.exp (-β * (sp L μ (spOf (W t))
      + 2 * tp L μ (axisOf (W t)) (spOf (W t)) (spOf (W (finRotate (L μ) t)))))
      ∂(Measure.pi fun _ : Fin (L μ) => Measure.pi fun _ : SlIdx L μ => probHaar (SUN.SU N)) := by
  have hmp := measurePreserving_Φ (L := L) (μ := μ) N
  unfold ZR System.partition System.vol
  change ∫ U : RLink L → SUN.SU N, (sysR L N).boltz β U
      ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) = _
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (measurable_boltzR (L := L) N β).aestronglyMeasurable]
  congr 1; funext W
  unfold System.boltz
  rw [action_Φ hN W, Finset.mul_sum, Real.exp_sum]

#print axioms measurePreserving_Φ
#print axioms action_Φ
#print axioms ZR_eq_integral

end MassGap.RectWilson
