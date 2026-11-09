import Mathlib
import MassGap.AdjacentFibre
import MassGap.ObserverBox

noncomputable section

/-!
# MassGap.LocalPotential — the fibre step for Wilson times a general local potential

The coarse theory an observer sees is Wilson at an effective coupling times `e^V` with `V` a sum of
small local terms, not one specific coupling. This file states that family and proves its fibre step:
at a link pair `(l, m)` the terms split by what they read of the pair, the single-link parts ride in
the reference densities (`PairFibreDens`), and only the terms reading both links pay the perturbation
cost, `ε_lm = Σ_{X ∋ l, m} v_X` (`fibreHyp_localPot`).
-/

namespace MassGap.LocalPotential

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (bdT wt wt_pos continuous_wt exists_abs_le)
open MassGap.PairInterface (FE realFeature fibreWeight continuous_realFeature norm_realFeature)
open MassGap.PairCount (n2)
open MassGap.PairFibreDens (Dens nearTilt DensFibreBound densWeight)
open MassGap.FibrePerturb (CovBoundOn covBoundOn_perturb_cont)
open MassGap.WeightedHeatBath (FibreHyp fibreHyp_iff)

variable {N : ℕ}

/-- **A local potential on the periodic lattice of extent `M + 1`**: finitely many terms `V X`, each
continuous, reading only the links of its support, bounded by `v X`. -/
structure LocalPot (N M : ℕ) where
  ι : Type
  [fι : Fintype ι]
  supp : ι → Finset (WilsonHypercubic.Link 4 (M + 1))
  V : ι → (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ
  v : ι → ℝ
  cont : ∀ X, Continuous (V X)
  reads : ∀ X W l g, l ∉ supp X → V X (Function.update W l g) = V X W
  bound : ∀ X W, |V X W| ≤ v X

attribute [instance] LocalPot.fι

/-- The total potential. -/
def LocalPot.tot {M : ℕ} (P : LocalPot N M) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) : ℝ :=
  ∑ X, P.V X W

/-- **Wilson times the local potential.** -/
def wtV {M : ℕ} (β : ℝ) (P : LocalPot N M) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) : ℝ :=
  wt (bdT M) β W * Real.exp (P.tot W)

/-- The local weight at a link: `Σ_{X ∋ l} v X`. -/
def LocalPot.at {M : ℕ} (P : LocalPot N M) (l : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X), P.v X

/-- The mixed weight of a pair: `Σ_{X ∋ l, m} v X`. -/
def LocalPot.mix {M : ℕ} (P : LocalPot N M) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ m ∈ P.supp X), P.v X

/-- **The potential on the pair fibre splits by what each term reads**: a constant, a part reading
only the `l`-variable `g`, a part reading only the `m`-variable `h`, and the mixed part.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem tot_split {M : ℕ} (P : LocalPot N M) {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (h g : SU N) :
    P.tot (Function.update (Function.update W m h) l g)
      = (∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ ¬ m ∈ P.supp X), P.V X W)
        + (∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ ¬ m ∈ P.supp X),
            P.V X (Function.update W l g))
        + (∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ m ∈ P.supp X),
            P.V X (Function.update W m h))
        + (∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ m ∈ P.supp X),
            P.V X (Function.update (Function.update W m h) l g)) := by
  classical
  unfold LocalPot.tot
  have hsplit : ∀ F : P.ι → ℝ, ∑ X, F X
      = (∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ ¬ m ∈ P.supp X), F X)
        + (∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ ¬ m ∈ P.supp X), F X)
        + (∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ m ∈ P.supp X), F X)
        + (∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ m ∈ P.supp X), F X) := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun X => l ∈ P.supp X),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun X => l ∈ P.supp X)
        (fun X => m ∈ P.supp X),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun X => ¬ l ∈ P.supp X)
        (fun X => m ∈ P.supp X)]
    simp only [Finset.filter_filter]
    ring
  rw [hsplit]
  have e1 : ∀ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ ¬ m ∈ P.supp X),
      P.V X (Function.update (Function.update W m h) l g) = P.V X W := by
    intro X hX
    obtain ⟨hl, hm⟩ := (Finset.mem_filter.mp hX).2
    rw [P.reads X _ l g hl, P.reads X W m h hm]
  have e2 : ∀ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ ¬ m ∈ P.supp X),
      P.V X (Function.update (Function.update W m h) l g) = P.V X (Function.update W l g) := by
    intro X hX
    obtain ⟨-, hm⟩ := (Finset.mem_filter.mp hX).2
    rw [Function.update_comm (Ne.symm hlm) h g W, P.reads X _ m h hm]
  have e3 : ∀ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ m ∈ P.supp X),
      P.V X (Function.update (Function.update W m h) l g) = P.V X (Function.update W m h) := by
    intro X hX
    obtain ⟨hl, -⟩ := (Finset.mem_filter.mp hX).2
    rw [P.reads X _ l g hl]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3]

#print axioms tot_split

/-- A sub-sum of the terms is bounded by the sum of their bounds.

DERIVED: no numeral. -/
theorem abs_sum_le_v {M : ℕ} (P : LocalPot N M) (s : Finset P.ι)
    (F : P.ι → (WilsonHypercubic.Link 4 (M + 1) → SU N)) :
    |∑ X ∈ s, P.V X (F X)| ≤ ∑ X ∈ s, P.v X :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun X _ => P.bound X _)

#print axioms abs_sum_le_v

/-- **The fibre hypothesis of Wilson times a local potential**: a density fibre bound at `c` on the
Wilson coupling `β n2` and the densities within `e^{±η}` of a tilt of norm `κ`, with `η` at least the
local weights at `l` and at `m`, gives the fibre hypothesis at `e^ε (c + 2 (e^ε − 1))`,
`ε = Σ_{X ∋ l, m} v X` (`PairWeight.wt_fibre_eq`, `tot_split`,
`FibrePerturb.covBoundOn_perturb_cont`).

DERIVED: `4` is the spacetime dimension; `1` is the least `M` and the successor writing the extent;
`0` is the excluded rank and the lower end of `β`, `c`; `12` is the non-diagonal plaquette count per
link; `2` is the perturbation lemma's two additive terms. -/
theorem fibreHyp_localPot (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M : ℕ} (hM : 1 ≤ M) (P : LocalPot N M)
    {l m : WilsonHypercubic.Link 4 (M + 1)} (hlm : l ≠ m) {c κ η : ℝ} (hc : 0 ≤ c)
    (hκ : β * (12 - (n2 M l m : ℝ)) ≤ κ) (hηl : P.at l ≤ η) (hηm : P.at m ≤ η)
    (hB : DensFibreBound (probHaar (SU N)) (realFeature N) c (β * (n2 M l m : ℝ))
      (nearTilt (realFeature N) κ η)) :
    FibreHyp (wtV (N := N) β P) l m
      (Real.exp (P.mix l m) * (c + 2 * (Real.exp (P.mix l m) - 1))) := by
  classical
  rw [fibreHyp_iff _ hlm]
  intro W
  obtain ⟨K, T, α, γ, hK, hT, hα, hγ, hw⟩ := MassGap.PairWeight.wt_fibre_eq hN hβ hM hlm W
  have hX := continuous_realFeature N
  -- the four parts
  set C := ∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ ¬ m ∈ P.supp X), P.V X W with hC
  set Vg : SU N → ℝ := fun g => ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ ¬ m ∈ P.supp X),
      P.V X (Function.update W l g) with hVg
  set Vh : SU N → ℝ := fun h => ∑ X ∈ Finset.univ.filter (fun X => ¬ l ∈ P.supp X ∧ m ∈ P.supp X),
      P.V X (Function.update W m h) with hVh
  set Vm : SU N → SU N → ℝ := fun h g => ∑ X ∈ Finset.univ.filter
      (fun X => l ∈ P.supp X ∧ m ∈ P.supp X), P.V X (Function.update (Function.update W m h) l g)
    with hVm
  have cVg : Continuous Vg := continuous_finset_sum _ fun X _ =>
    (P.cont X).comp (continuous_const.update l continuous_id)
  have cVh : Continuous Vh := continuous_finset_sum _ fun X _ =>
    (P.cont X).comp (continuous_const.update m continuous_id)
  have cVm : Continuous (Function.uncurry Vm) := by
    have hu : Continuous (fun p : SU N × SU N => Function.update (Function.update W m p.1) l p.2) :=
      ((continuous_const : Continuous fun _ : SU N × SU N => W).update m continuous_fst).update l
        continuous_snd
    exact continuous_finset_sum _ fun X _ => (P.cont X).comp hu
  have bVg : ∀ g, |Vg g| ≤ η := fun g => by
    refine (abs_sum_le_v P _ _).trans (le_trans ?_ hηl)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun X hX => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.1⟩)
      (fun X _ _ => le_trans (abs_nonneg _) (P.bound X W))
  have bVh : ∀ h, |Vh h| ≤ η := fun h => by
    refine (abs_sum_le_v P _ _).trans (le_trans ?_ hηm)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun X hX => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.2⟩)
      (fun X _ _ => le_trans (abs_nonneg _) (P.bound X W))
  have bVm : ∀ h g, |Vm h g| ≤ P.mix l m := fun h g => abs_sum_le_v P _ _
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ : Dens (SU N),
      ∀ h, θ.f h = Real.exp (inner ℝ α (realFeature N h) + Vh h) :=
    ⟨⟨fun h => Real.exp (inner ℝ α (realFeature N h) + Vh h),
      Real.continuous_exp.comp ((continuous_const.inner hX).add cVh), fun h => Real.exp_pos _⟩,
      fun h => rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ : Dens (SU N),
      ∀ g, θ.f g = Real.exp (inner ℝ γ (realFeature N g) + Vg g) :=
    ⟨⟨fun g => Real.exp (inner ℝ γ (realFeature N g) + Vg g),
      Real.continuous_exp.comp ((continuous_const.inner hX).add cVg), fun g => Real.exp_pos _⟩,
      fun g => rfl⟩
  have near : ∀ (θ : Dens (SU N)) (δ : FE N) (V : SU N → ℝ), ‖δ‖ ≤ κ → (∀ x, |V x| ≤ η) →
      (∀ x, θ.f x = Real.exp (inner ℝ δ (realFeature N x) + V x)) →
      θ ∈ nearTilt (realFeature N) κ η := fun θ δ V hδ hV hθ =>
    ⟨δ, hδ, fun x => by
      rw [hθ x, ← Real.exp_add, ← Real.exp_add]
      have := abs_le.mp (hV x)
      exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩⟩
  have h₁ := near θ₁ α Vh (hα.trans hκ) bVh hθ₁
  have h₂ := near θ₂ γ Vg (hγ.trans hκ) bVg hθ₂
  have hK' : 0 < K * Real.exp C := mul_pos hK (Real.exp_pos _)
  have hcov : CovBoundOn (fun a : SU N → ℝ => Continuous a ∧ ∃ C, ∀ x, |a x| ≤ C)
      (probHaar (SU N)) (densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂) c := fun a b ha hb hz =>
    hB (K * Real.exp C) T θ₁ θ₂ hK' hT h₁ h₂ a b ha.1 hb.1 hz
  have hwc : Continuous (Function.uncurry (densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂)) := by
    show Continuous fun z : SU N × SU N => densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂ z.1 z.2
    unfold densWeight
    exact ((continuous_const.mul (Real.continuous_exp.comp
      ((hX.comp continuous_fst).inner (T.continuous.comp (hX.comp continuous_snd))))).mul
      (θ₁.cont.comp continuous_fst)).mul (θ₂.cont.comp continuous_snd)
  have hwG : MassGap.FibrePerturb.Good (densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂) := by
    obtain ⟨C', hC'⟩ := exists_abs_le hwc
    exact ⟨hwc.measurable, C', fun h g => hC' (h, g)⟩
  have hw0 : ∀ h g, 0 ≤ densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂ h g := fun h g => by
    unfold densWeight
    exact mul_nonneg (mul_nonneg (mul_nonneg hK'.le (Real.exp_pos _).le) (θ₁.pos h).le)
      (θ₂.pos g).le
  have hε : 0 ≤ P.mix l m := le_trans (abs_nonneg _) (bVm (W m) (W l))
  have hp := covBoundOn_perturb_cont (probHaar (SU N)) hc hε hwG hw0 cVm.measurable bVm hcov
  have e : (fun h g => densWeight (realFeature N) (K * Real.exp C) T θ₁ θ₂ h g * Real.exp (Vm h g))
      = fun h g => wtV β P (Function.update (Function.update W m h) l g) := by
    funext h g
    unfold wtV
    rw [tot_split P hlm W h g, hw h g]
    unfold densWeight fibreWeight
    rw [hθ₁ h, hθ₂ g]
    simp only [Real.exp_add, hVg, hVh, hVm, hC]
    ring
  rw [e] at hp
  exact hp

#print axioms fibreHyp_localPot

/-- The bounds of a local potential are non-negative.

DERIVED: `0` is the sign. -/
theorem LocalPot.v_nonneg {M : ℕ} (P : LocalPot N M) (X : P.ι) : 0 ≤ P.v X :=
  le_trans (abs_nonneg _) (P.bound X (fun _ => 1))

#print axioms LocalPot.v_nonneg

/-- **The mixed weights of a link, summed over its partners, are at most its local norm**:
`Σ_{m ≠ l} Σ_{X ∋ l, m} v X ≤ Σ_{X ∋ l} |supp X| v X`.

DERIVED: `1` is the successor writing the extent. -/
theorem sum_mix_le {M : ℕ} (P : LocalPot N M) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ∑ m ∈ Finset.univ.erase l, P.mix l m
      ≤ ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X), ((P.supp X).card : ℝ) * P.v X := by
  classical
  unfold LocalPot.mix
  calc ∑ m ∈ Finset.univ.erase l, ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ m ∈ P.supp X), P.v X
      ≤ ∑ m, ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X ∧ m ∈ P.supp X), P.v X :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l _)
          (fun m _ _ => Finset.sum_nonneg fun X _ => P.v_nonneg X)
    _ = ∑ m, ∑ X, (if l ∈ P.supp X ∧ m ∈ P.supp X then P.v X else 0) := by
        simp only [Finset.sum_filter]
    _ = ∑ X, ∑ m, (if l ∈ P.supp X ∧ m ∈ P.supp X then P.v X else 0) := Finset.sum_comm
    _ = ∑ X, (if l ∈ P.supp X then ((P.supp X).card : ℝ) * P.v X else 0) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        split_ifs with hl
        · simp only [hl, true_and]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 2
          simp
        · simp [hl]
    _ = _ := by rw [Finset.sum_filter]

#print axioms sum_mix_le

/-! ## The box local gap of Wilson times a local potential -/

open MassGap.WeightedTorus (TorusWeight WBoxLocalGap wBoxLocalGap_of_pairCorr wPairCorrAt_of_fibreHyp)
open MassGap.BoxGap (DefectMatrix)
open MassGap.PairCount (n2_symm n2_cases sum_n2_le)
open MassGap.ObserverBox (DensCheck densFibreBound_of_check exp_le_inv_one_sub)

/-- **A gauge-invariant local potential on every periodic lattice.** -/
structure LocalPotFam (N : ℕ) where
  P : ∀ M : ℕ, LocalPot N M
  gauge : ∀ M (X : (P M).ι) (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
    (W : WilsonHypercubic.Link 4 (M + 1) → SU N),
    (P M).V X (LocalGauge.gaugeTransform g W) = (P M).V X W

/-- The total potential is continuous.

DERIVED: no numeral. -/
theorem LocalPot.continuous_tot {M : ℕ} (P : LocalPot N M) : Continuous P.tot :=
  continuous_finset_sum _ fun X _ => P.cont X

#print axioms LocalPot.continuous_tot

/-- **Wilson times a gauge-invariant local potential, as a torus weight.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def potWeight (β : ℝ) (F : LocalPotFam N) : TorusWeight N where
  Φ M := wtV β (F.P M)
  pos M W := mul_pos (wt_pos _ _ _) (Real.exp_pos _)
  cont M := (continuous_wt _ _).mul (Real.continuous_exp.comp (F.P M).continuous_tot)
  gauge M g W := by
    show wt (bdT M) β (LocalGauge.gaugeTransform g W) * Real.exp ((F.P M).tot (LocalGauge.gaugeTransform g W))
      = wt (bdT M) β W * Real.exp ((F.P M).tot W)
    have ht : (F.P M).tot (LocalGauge.gaugeTransform g W) = (F.P M).tot W :=
      Finset.sum_congr rfl fun X _ => F.gauge M X g W
    rw [ht, show wt (bdT M) β (LocalGauge.gaugeTransform g W) = wt (bdT M) β W from
      LocalGauge.boltz_gauge_invariant_local g β W]

/-- **The local norm of a potential at a link**: `Σ_{X ∋ l} |supp X| v X`. -/
def LocalPot.norm {M : ℕ} (P : LocalPot N M) (l : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  ∑ X ∈ Finset.univ.filter (fun X => l ∈ P.supp X), ((P.supp X).card : ℝ) * P.v X

/-- The local weight is at most the local norm (each support through `l` has at least one link).

DERIVED: `1` is the least support size. -/
theorem LocalPot.at_le_norm {M : ℕ} (P : LocalPot N M) (l : WilsonHypercubic.Link 4 (M + 1)) :
    P.at l ≤ P.norm l := by
  unfold LocalPot.at LocalPot.norm
  refine Finset.sum_le_sum fun X hX => ?_
  have hl := (Finset.mem_filter.mp hX).2
  have h1 : (1 : ℝ) ≤ (P.supp X).card := by exact_mod_cast Finset.card_pos.mpr ⟨l, hl⟩
  nlinarith [P.v_nonneg X]

#print axioms LocalPot.at_le_norm

/-- The mixed weight is at most the local weight.

DERIVED: no numeral. -/
theorem LocalPot.mix_le_at {M : ℕ} (P : LocalPot N M) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    P.mix l m ≤ P.at l :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun X hX => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.1⟩)
    (fun X _ _ => P.v_nonneg X)

#print axioms LocalPot.mix_le_at

/-- The mixed weight is symmetric.

DERIVED: no numeral. -/
theorem LocalPot.mix_symm {M : ℕ} (P : LocalPot N M) (l m : WilsonHypercubic.Link 4 (M + 1)) :
    P.mix l m = P.mix m l := by
  unfold LocalPot.mix
  exact Finset.sum_congr (Finset.filter_congr fun X _ => and_comm) fun _ _ => rfl

#print axioms LocalPot.mix_symm

/-- **The density check of the potential box**, `SU(2)`: `τ₀ = 1/50`, `κ = 3/50`, `E = 5/4`,
`dstar ≤ 1/125`.

DERIVED: `4`, `1/8`, `0` are the `SU(2)` Haar constants; `1/50 = 4/200` and `3/50 = 12/200` are the
largest Wilson coupling and tilt at `β ≤ 1/200`; `5/4 = 1/(1 − 1/5)` bounds `e^{1/5}`. CHOSEN:
`1768/10000 ≥ √(1/32)`; `6253/10000 ≥ √M₂ = √0.390983…`; `1/125 = 0.008` rounds the computed
`0.0079688…` up. -/
theorem densCheck_pot :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (6253 / 10000) (1 / 50) (3 / 50) (5 / 4) (1 / 125) := by
  norm_num [DensCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms densCheck_pot

/-- **The defect matrix of the potential box**: `e^ε ((β n2 / τ₀) D₀ + 2 (e^ε − 1))` with
`ε = mix l m`, `τ₀ = 1/50`, `D₀ = 1/125`.

DERIVED: `1/50`, `1/125` are `densCheck_pot`'s; `2` is the perturbation lemma's additive terms. -/
def deltaPot {M : ℕ} (β : ℝ) (P : LocalPot N M) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = m then 0 else
    Real.exp (P.mix l m) * (β * (n2 M l m : ℝ) / (1 / 50) * (1 / 125)
      + 2 * (Real.exp (P.mix l m) - 1))

/-- **Every pair of the potential box has its fibre hypothesis at `deltaPot`**
(`fibreHyp_localPot`, `ObserverBox.densFibreBound_of_check`, `densCheck_pot`).

DERIVED: `2` is the rank; `1` is the least `M`; `1/200` and `1/5` are the box; `4` is `n2`'s
largest value; `12` the plaquette count per link. -/
theorem fibreHyp_pot {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) {M : ℕ} (hM : 1 ≤ M)
    (P : LocalPot 2 M) (hν : ∀ l, P.norm l ≤ 1 / 5) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) : FibreHyp (wtV (N := 2) β P) l m (deltaPot β P l m) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hn : (n2 M l m : ℝ) ≤ 4 := by
    rcases n2_cases hM hlm with h | h | h <;> rw [h] <;> norm_num
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have hτ0 : 0 ≤ β * (n2 M l m : ℝ) := mul_nonneg hβ0 hn0
  have hττ : β * (n2 M l m : ℝ) ≤ 1 / 50 := by nlinarith
  have hE : Real.exp (1 / 5) ≤ 5 / 4 := by
    have := exp_le_inv_one_sub (x := 1 / 5) (q := 1 / 5) (by norm_num) le_rfl (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
  have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 (by norm_num) hE
    densCheck_pot hτ0 hττ
  have hκ : β * (12 - (n2 M l m : ℝ)) ≤ 3 / 50 := by nlinarith
  have H := fibreHyp_localPot h2 hβ0 hM P hlm (c := β * (n2 M l m : ℝ) / (1 / 50) * (1 / 125))
    (by positivity) hκ ((P.at_le_norm l).trans (hν l)) ((P.at_le_norm m).trans (hν m)) hB
  unfold deltaPot
  rw [if_neg hlm]
  exact H

#print axioms fibreHyp_pot

/-- **The pointwise bound of a defect entry**: `deltaPot ≤ (5/4)(2/5) β n2 + (25/8) mix`
(`e^x ≤ 5/4` and `e^x − 1 ≤ x e^x` for `0 ≤ x ≤ 1/5`).

DERIVED: `5/4 ≥ e^{1/5}`; `2/5 = (1/125)/(1/50)`; `25/8 = 2 (5/4)²`. -/
theorem deltaPot_le {β : ℝ} (hβ0 : 0 ≤ β) {M : ℕ} (P : LocalPot N M) (hν : ∀ l, P.norm l ≤ 1 / 5)
    (l m : WilsonHypercubic.Link 4 (M + 1)) :
    deltaPot β P l m ≤ (5 / 4) * (2 / 5) * β * (n2 M l m : ℝ) + 25 / 8 * P.mix l m := by
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have he0 : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
  by_cases hlm : l = m
  · unfold deltaPot
    rw [if_pos hlm]
    positivity
  unfold deltaPot
  rw [if_neg hlm]
  set e := P.mix l m with he
  have hle : e ≤ 1 / 5 := (P.mix_le_at l m).trans ((P.at_le_norm l).trans (hν l))
  have hE : Real.exp e ≤ 5 / 4 := by
    have := exp_le_inv_one_sub he0 hle (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
  have hsub : Real.exp e - 1 ≤ e * Real.exp e := by
    have h1 := Real.add_one_le_exp (-e)
    have h2 : Real.exp (-e) * Real.exp e = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos e]
  have hin : β * (n2 M l m : ℝ) / (1 / 50) * (1 / 125) + 2 * (Real.exp e - 1)
      ≤ (2 / 5) * β * (n2 M l m : ℝ) + 2 * (e * (5 / 4)) := by
    have : e * Real.exp e ≤ e * (5 / 4) := mul_le_mul_of_nonneg_left hE he0
    have e2 : β * (n2 M l m : ℝ) / (1 / 50) * (1 / 125) = (2 / 5) * β * (n2 M l m : ℝ) := by ring
    linarith
  have hin0 : 0 ≤ (2 / 5) * β * (n2 M l m : ℝ) + 2 * (e * (5 / 4)) := by positivity
  calc Real.exp e * (β * (n2 M l m : ℝ) / (1 / 50) * (1 / 125) + 2 * (Real.exp e - 1))
      ≤ Real.exp e * ((2 / 5) * β * (n2 M l m : ℝ) + 2 * (e * (5 / 4))) :=
        mul_le_mul_of_nonneg_left hin (Real.exp_pos e).le
    _ ≤ (5 / 4) * ((2 / 5) * β * (n2 M l m : ℝ) + 2 * (e * (5 / 4))) :=
        mul_le_mul_of_nonneg_right hE hin0
    _ = _ := by ring

#print axioms deltaPot_le

/-- **The defect matrix of the potential box has row and column sums at most `143/200`**
(`deltaPot_le`, `PairCount.sum_n2_le`, `sum_mix_le`).

DERIVED: `143/200 = (5/4)(2/5)(36/200) + (25/8)(1/5)`; `36` is `sum_n2_le`'s bound; `1` is the least
`M`; `0` is the lower end of the entries. -/
theorem defectMatrix_pot {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) {M : ℕ} (hM : 1 ≤ M)
    (P : LocalPot N M) (hν : ∀ l, P.norm l ≤ 1 / 5) : DefectMatrix (deltaPot β P) (143 / 200) := by
  have h0 : ∀ l m, 0 ≤ deltaPot β P l m := fun l m => by
    unfold deltaPot
    split_ifs
    · exact le_rfl
    · have he : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
      have := Real.one_le_exp he
      have : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
      positivity
  have hsymm : ∀ l m, deltaPot β P l m = deltaPot β P m l := fun l m => by
    unfold deltaPot
    by_cases h : l = m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), n2_symm M l m, P.mix_symm l m]
  have hrow : ∀ l, ∑ m, deltaPot β P l m ≤ 143 / 200 := fun l => by
    have hdiag : deltaPot β P l l = 0 := by unfold deltaPot; rw [if_pos rfl]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hdiag, zero_add]
    have hn : (∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)) ≤ 36 := by exact_mod_cast sum_n2_le hM l
    have hm : ∑ m ∈ Finset.univ.erase l, P.mix l m ≤ 1 / 5 := (sum_mix_le P l).trans (hν l)
    calc _ ≤ ∑ m ∈ Finset.univ.erase l, ((5 / 4) * (2 / 5) * β * (n2 M l m : ℝ) + 25 / 8 * P.mix l m) :=
          Finset.sum_le_sum fun m _ => deltaPot_le hβ0 P hν l m
      _ = (5 / 4) * (2 / 5) * β * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)
            + 25 / 8 * ∑ m ∈ Finset.univ.erase l, P.mix l m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (5 / 4) * (2 / 5) * β * 36 + 25 / 8 * (1 / 5) := by gcongr
      _ ≤ 143 / 200 := by nlinarith
  refine ⟨h0, hrow, fun m => ?_⟩
  calc ∑ l, deltaPot β P l m = ∑ l, deltaPot β P m l := Finset.sum_congr rfl fun l _ => hsymm l m
    _ ≤ 143 / 200 := hrow m

#print axioms defectMatrix_pot

/-- **The box local gap of Wilson times a local potential**: `SU(2)`, `β ≤ 1/200` (`β_std ≤ 1/100`),
and a gauge-invariant local potential of local norm `Σ_{X ∋ l} |supp X| v X ≤ 1/5` at every link
and extent, has local gap `57/200` at every box side and extent.

DERIVED: `57/200 = 1 − 143/200`; `2` is the rank; `1` bounds the entries; `1/200` and `1/5` are the box's
coupling and potential-norm bounds, as in `fibreHyp_pot` and `defectMatrix_pot`. -/
theorem potBox_localGap {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 200) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 5) (n : ℕ) :
    WBoxLocalGap (potWeight β F) n (57 / 200) := by
  have h := wBoxLocalGap_of_pairCorr (potWeight β F) (Δ := 143 / 200) n (fun j => by
    have hM : 1 ≤ 2 * j + 1 := by omega
    have hD := defectMatrix_pot hβ0 hβ hM (F.P (2 * j + 1)) (hν _)
    refine ⟨deltaPot β (F.P (2 * j + 1)), hD, fun l m => ?_,
      wPairCorrAt_of_fibreHyp (potWeight β F) j _ hD.1
        (fun l m hlm => fibreHyp_pot hβ0 hβ hM (F.P (2 * j + 1)) (hν _) hlm)⟩
    calc deltaPot β (F.P (2 * j + 1)) l m ≤ ∑ m', deltaPot β (F.P (2 * j + 1)) l m' :=
          Finset.single_le_sum (fun m' _ => hD.1 l m') (Finset.mem_univ m)
      _ ≤ 143 / 200 := hD.2.1 l
      _ ≤ 1 := by norm_num)
  have e : (1 : ℝ) - 143 / 200 = 57 / 200 := by norm_num
  rw [e] at h
  exact h

#print axioms potBox_localGap

/-! ## The potential box at general constants -/

/-- **The defect matrix of the potential box at check constants `τ₀`, `D₀`.**

DERIVED: `2` is the perturbation lemma's additive terms; `0` is the diagonal. -/
def deltaPotG {M : ℕ} (τ₀ D₀ β : ℝ) (P : LocalPot N M) (l m : WilsonHypercubic.Link 4 (M + 1)) : ℝ :=
  if l = m then 0 else
    Real.exp (P.mix l m) * (β * (n2 M l m : ℝ) / τ₀ * D₀ + 2 * (Real.exp (P.mix l m) - 1))

/-- **The fibre hypothesis at general constants**: a density check at `(τ₀, κ₀, E, D₀)` with
`4 βb ≤ τ₀`, `12 βb ≤ κ₀` and `e^ν ≤ E` gives every pair its fibre hypothesis at `deltaPotG`
(`fibreHyp_localPot`, `ObserverBox.densFibreBound_of_check`).

DERIVED: `2` is the rank; `4` is `n2`'s largest value; `12` the plaquette count per link; `1` is the
least `M`; `0` is the lower end of `β`, `ν`; `4`, `1/8`, `0` in `DensCheck` are the `SU(2)` Haar constants. -/
theorem fibreHyp_potG {β βb ν τ₀ κ₀ E D₀ s σ : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ βb) (hτ₀ : 4 * βb ≤ τ₀)
    (hκ₀ : 12 * βb ≤ κ₀) (hν0 : 0 ≤ ν) (hE : Real.exp ν ≤ E) (hD0 : 0 ≤ D₀)
    (hc : DensCheck 4 (1 / 8) 0 s σ τ₀ κ₀ E D₀) {M : ℕ} (hM : 1 ≤ M)
    (P : LocalPot 2 M) (hν : ∀ l, P.norm l ≤ ν) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) : FibreHyp (wtV (N := 2) β P) l m (deltaPotG τ₀ D₀ β P l m) := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hτpos : 0 < τ₀ := hc.1
  have hn : (n2 M l m : ℝ) ≤ 4 := by
    rcases n2_cases hM hlm with h | h | h <;> rw [h] <;> norm_num
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have hτ0 : 0 ≤ β * (n2 M l m : ℝ) := mul_nonneg hβ0 hn0
  have hττ : β * (n2 M l m : ℝ) ≤ τ₀ := by nlinarith
  have hB := densFibreBound_of_check h2 MassGap.HaarMomentsSU2.haarConsts_su2 hν0 hE hc hτ0 hττ
  have hκ : β * (12 - (n2 M l m : ℝ)) ≤ κ₀ := by nlinarith
  have H := fibreHyp_localPot h2 hβ0 hM P hlm (c := β * (n2 M l m : ℝ) / τ₀ * D₀)
    (by positivity) hκ ((P.at_le_norm l).trans (hν l)) ((P.at_le_norm m).trans (hν m)) hB
  unfold deltaPotG
  rw [if_neg hlm]
  exact H

#print axioms fibreHyp_potG

/-- **The pointwise bound at general constants**: `deltaPotG ≤ E (D₀/τ₀) β n2 + 2 E² mix`.

DERIVED: `2` is the additive terms; `1` is `e⁰`; `0` is the sign of the mixed weight. -/
theorem deltaPotG_le {β ν τ₀ E D₀ : ℝ} (hβ0 : 0 ≤ β) (hτ : 0 < τ₀) (hD0 : 0 ≤ D₀)
    (hE : Real.exp ν ≤ E) {M : ℕ} (P : LocalPot N M) (hν : ∀ l, P.norm l ≤ ν)
    (l m : WilsonHypercubic.Link 4 (M + 1)) :
    deltaPotG τ₀ D₀ β P l m ≤ E * (D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * E ^ 2 * P.mix l m := by
  have hn0 : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
  have he0 : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
  have hE1 : 1 ≤ E := (Real.one_le_exp (he0.trans ((P.mix_le_at l m).trans
    ((P.at_le_norm l).trans (hν l))))).trans hE
  by_cases hlm : l = m
  · unfold deltaPotG
    rw [if_pos hlm]
    have : 0 ≤ D₀ / τ₀ := div_nonneg hD0 hτ.le
    positivity
  unfold deltaPotG
  rw [if_neg hlm]
  set e := P.mix l m with he
  have hle : e ≤ ν := (P.mix_le_at l m).trans ((P.at_le_norm l).trans (hν l))
  have hEe : Real.exp e ≤ E := (Real.exp_le_exp.mpr hle).trans hE
  have hsub : Real.exp e - 1 ≤ e * Real.exp e := by
    have h1 := Real.add_one_le_exp (-e)
    have h2 : Real.exp (-e) * Real.exp e = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos e]
  have e2 : β * (n2 M l m : ℝ) / τ₀ * D₀ = (D₀ / τ₀) * β * (n2 M l m : ℝ) := by
    field_simp
  have hDt : 0 ≤ (D₀ / τ₀) * β * (n2 M l m : ℝ) := by
    have : 0 ≤ D₀ / τ₀ := div_nonneg hD0 hτ.le
    positivity
  have hin : β * (n2 M l m : ℝ) / τ₀ * D₀ + 2 * (Real.exp e - 1)
      ≤ (D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * (e * E) := by
    have : e * Real.exp e ≤ e * E := mul_le_mul_of_nonneg_left hEe he0
    linarith
  have hin0 : 0 ≤ (D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * (e * E) := by
    have : 0 ≤ e * E := mul_nonneg he0 (by linarith)
    linarith
  calc Real.exp e * (β * (n2 M l m : ℝ) / τ₀ * D₀ + 2 * (Real.exp e - 1))
      ≤ Real.exp e * ((D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * (e * E)) :=
        mul_le_mul_of_nonneg_left hin (Real.exp_pos e).le
    _ ≤ E * ((D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * (e * E)) := mul_le_mul_of_nonneg_right hEe hin0
    _ = _ := by ring

#print axioms deltaPotG_le

/-- **Row and column sums at general constants**: at most `Δ` when
`E (D₀/τ₀) βb 36 + 2 E² ν ≤ Δ` (`deltaPotG_le`, `PairCount.sum_n2_le`, `sum_mix_le`).

DERIVED: `36` is `sum_n2_le`'s bound; `2` is the additive terms; `1` is the least `M`; `0` is the
lower end of the entries. -/
theorem defectMatrix_potG {β βb ν τ₀ E D₀ Δ : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ βb) (hτ : 0 < τ₀)
    (hD0 : 0 ≤ D₀) (hE : Real.exp ν ≤ E) (hΔ : E * (D₀ / τ₀) * βb * 36 + 2 * E ^ 2 * ν ≤ Δ)
    {M : ℕ} (hM : 1 ≤ M) (P : LocalPot N M) (hν : ∀ l, P.norm l ≤ ν) :
    DefectMatrix (deltaPotG τ₀ D₀ β P) Δ := by
  have hν0 : 0 ≤ ν := le_trans (Finset.sum_nonneg fun X _ =>
    mul_nonneg (Nat.cast_nonneg _) (P.v_nonneg X)) (hν (Classical.arbitrary _))
  have hE1 : 1 ≤ E := (Real.one_le_exp hν0).trans hE
  have hDt : 0 ≤ D₀ / τ₀ := div_nonneg hD0 hτ.le
  have h0 : ∀ l m, 0 ≤ deltaPotG τ₀ D₀ β P l m := fun l m => by
    unfold deltaPotG
    split_ifs
    · exact le_rfl
    · have he : 0 ≤ P.mix l m := Finset.sum_nonneg fun X _ => P.v_nonneg X
      have := Real.one_le_exp he
      have : (0 : ℝ) ≤ n2 M l m := Nat.cast_nonneg _
      have : 0 ≤ β * (n2 M l m : ℝ) / τ₀ * D₀ := by positivity
      positivity
  have hsymm : ∀ l m, deltaPotG τ₀ D₀ β P l m = deltaPotG τ₀ D₀ β P m l := fun l m => by
    unfold deltaPotG
    by_cases h : l = m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), n2_symm M l m, P.mix_symm l m]
  have hrow : ∀ l, ∑ m, deltaPotG τ₀ D₀ β P l m ≤ Δ := fun l => by
    have hdiag : deltaPotG τ₀ D₀ β P l l = 0 := by unfold deltaPotG; rw [if_pos rfl]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hdiag, zero_add]
    have hn : (∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)) ≤ 36 := by exact_mod_cast sum_n2_le hM l
    have hm : ∑ m ∈ Finset.univ.erase l, P.mix l m ≤ ν := (sum_mix_le P l).trans (hν l)
    calc _ ≤ ∑ m ∈ Finset.univ.erase l, (E * (D₀ / τ₀) * β * (n2 M l m : ℝ) + 2 * E ^ 2 * P.mix l m) :=
          Finset.sum_le_sum fun m _ => deltaPotG_le hβ0 hτ hD0 hE P hν l m
      _ = E * (D₀ / τ₀) * β * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)
            + 2 * E ^ 2 * ∑ m ∈ Finset.univ.erase l, P.mix l m := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ E * (D₀ / τ₀) * βb * 36 + 2 * E ^ 2 * ν := by
          have hA : 0 ≤ E * (D₀ / τ₀) := mul_nonneg (by linarith) hDt
          have hn0 : 0 ≤ ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ) :=
            Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
          have h1 : E * (D₀ / τ₀) * β * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)
              ≤ E * (D₀ / τ₀) * βb * 36 := by
            calc E * (D₀ / τ₀) * β * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ)
                ≤ E * (D₀ / τ₀) * βb * ∑ m ∈ Finset.univ.erase l, (n2 M l m : ℝ) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hA) hn0
              _ ≤ E * (D₀ / τ₀) * βb * 36 :=
                  mul_le_mul_of_nonneg_left hn (mul_nonneg hA (hβ0.trans hβ))
          have h2 : 2 * E ^ 2 * ∑ m ∈ Finset.univ.erase l, P.mix l m ≤ 2 * E ^ 2 * ν :=
            mul_le_mul_of_nonneg_left hm (by positivity)
          linarith
      _ ≤ Δ := hΔ
  refine ⟨h0, hrow, fun m => ?_⟩
  calc ∑ l, deltaPotG τ₀ D₀ β P l m = ∑ l, deltaPotG τ₀ D₀ β P m l :=
        Finset.sum_congr rfl fun l _ => hsymm l m
    _ ≤ Δ := hrow m

#print axioms defectMatrix_potG

/-- **The box local gap at general constants**: under a density check and
`E (D₀/τ₀) βb 36 + 2 E² ν ≤ Δ ≤ 1`, Wilson at `β ≤ βb` times a local potential of local norm `≤ ν`
has local gap `1 − Δ` at every box side and extent.

DERIVED: `1` bounds the entries; the rest as in `fibreHyp_potG`, `defectMatrix_potG`: `4`, `1/8`, `0` the
`SU(2)` Haar constants, `4` also `n2`'s largest value, `12` the plaquette count per link, `36` the bound of
`PairCount.sum_n2_le`, `2` the additive terms. -/
theorem potBox_localGapG {β βb ν τ₀ κ₀ E D₀ s σ Δ : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ βb)
    (hτ₀ : 4 * βb ≤ τ₀) (hκ₀ : 12 * βb ≤ κ₀) (hν0 : 0 ≤ ν) (hE : Real.exp ν ≤ E) (hD0 : 0 ≤ D₀)
    (hc : DensCheck 4 (1 / 8) 0 s σ τ₀ κ₀ E D₀)
    (hΔ : E * (D₀ / τ₀) * βb * 36 + 2 * E ^ 2 * ν ≤ Δ) (hΔ1 : Δ ≤ 1) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ ν) (n : ℕ) :
    WBoxLocalGap (potWeight β F) n (1 - Δ) :=
  wBoxLocalGap_of_pairCorr (potWeight β F) (Δ := Δ) n (fun j => by
    have hM : 1 ≤ 2 * j + 1 := by omega
    have hD := defectMatrix_potG hβ0 hβ hc.1 hD0 hE hΔ hM (F.P (2 * j + 1)) (hν _)
    refine ⟨deltaPotG τ₀ D₀ β (F.P (2 * j + 1)), hD, fun l m => ?_,
      wPairCorrAt_of_fibreHyp (potWeight β F) j _ hD.1
        (fun l m hlm => fibreHyp_potG hβ0 hβ hτ₀ hκ₀ hν0 hE hD0 hc hM (F.P (2 * j + 1)) (hν _) hlm)⟩
    calc deltaPotG τ₀ D₀ β (F.P (2 * j + 1)) l m ≤ ∑ m', deltaPotG τ₀ D₀ β (F.P (2 * j + 1)) l m' :=
          Finset.single_le_sum (fun m' _ => hD.1 l m') (Finset.mem_univ m)
      _ ≤ Δ := hD.2.1 l
      _ ≤ 1 := hΔ1)

#print axioms potBox_localGapG

/-- **The wide density check**, `SU(2)`: `τ₀ = 1/10`, `κ = 3/10`, `E = 8/7`, `dstar ≤ 91/2500`.

DERIVED: `4`, `1/8`, `0` are the `SU(2)` Haar constants; `1/10 = 4/40`, `3/10 = 12/40` at
`β ≤ 1/40`; `8/7 = 1/(1 − 1/8)` bounds `e^{1/8}`. CHOSEN: `1768/10000 ≥ √(1/32)`;
`2893/5000 ≥ √M₂`; `91/2500 = 0.0364` rounds the computed `0.03635…` up. -/
theorem densCheck_wide :
    DensCheck 4 (1 / 8) 0 (1768 / 10000) (2893 / 5000) (1 / 10) (3 / 10) (8 / 7) (91 / 2500) := by
  norm_num [DensCheck, MassGap.PairInterface.dstar, MassGap.PairInterface.dstarNum,
    MassGap.PairInterface.dstarDen, MassGap.PairInterface.dstarE, MassGap.PairInterface.dstarZ,
    MassGap.PairInterface.M2bound, MassGap.PairInterface.mbarBound, MassGap.PairInterface.cR,
    MassGap.PairInterface.cR3]

#print axioms densCheck_wide

/-- **The wide potential box**: `SU(2)`, `β ≤ 1/40` (`β_std ≤ 1/20`) and a gauge-invariant local
potential of local norm `≤ 1/8` have local gap `299/1000` at every box side and extent.

DERIVED: `299/1000 = 1 − 701/1000`; `701/1000` bounds `(8/7)(0.364)(36/40) + 2 (8/7)² /8 = 0.70093…`;
`8/7 = 1/(1 − 1/8)`. -/
theorem potBox_localGap_wide {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) (F : LocalPotFam 2)
    (hν : ∀ M l, (F.P M).norm l ≤ 1 / 8) (n : ℕ) :
    WBoxLocalGap (potWeight β F) n (299 / 1000) := by
  have hE : Real.exp (1 / 8) ≤ 8 / 7 := by
    have := exp_le_inv_one_sub (x := 1 / 8) (q := 1 / 8) (by norm_num) le_rfl (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 8) = 8 / 7 by norm_num]
  have h := potBox_localGapG hβ0 hβ (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)
    densCheck_wide (Δ := 701 / 1000) (by norm_num) (by norm_num) F hν n
  have e : (1 : ℝ) - 701 / 1000 = 299 / 1000 := by norm_num
  rw [e] at h
  exact h

#print axioms potBox_localGap_wide

end MassGap.LocalPotential
