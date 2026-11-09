import Mathlib
import MassGap.KernelPower

/-!
# MassGap.CyclicKernel — the cyclic product integral of a kernel is a trace of its iterate

For a bounded measurable kernel `a` on a probability space `(X, μ)`:

* `cyc μ a m = ∫ ∏_{t : Fin m} a(W t, W (t+1 mod m)) d(μ^m)(W)`, the periodic chain of `m` copies;
* `chain μ a m x z = ∫ ∏_{t : Fin (m+1)} a(path t, path (t+1)) d(μ^m)`, the open chain from `x`
  to `z` through `m` free points.

`chain_eq_iter`: `chain μ a m = iter μ a m` (`= a^{∗(m+1)}`), by peeling the first free point
(`MeasureTheory.measurePreserving_piFinSuccAbove` at `0`). `cyc_succ`: `cyc μ a (m+1) =
∫ a^{∗(m+1)}(x,x) dμ(x)` (`Fin.snoc_eq_cons_rotate` closes the cycle). For symmetric `a`,
`iter_symm` and `cyc_even`: `cyc μ a (2j) = hs(a^{∗j}) = KernelPower.traceSeq μ a (2j)` for `j ≥ 1`.
-/

namespace MassGap.CyclicKernel

open MeasureTheory MassGap.KernelPower

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The periodic chain integral. -/
noncomputable def cyc (μ : Measure X) (a : X → X → ℝ) (m : ℕ) : ℝ :=
  ∫ W : Fin m → X, ∏ t, a (W t) (W (finRotate m t)) ∂(Measure.pi fun _ => μ)

/-- The open chain from `x` to `z` through `m` free points. -/
noncomputable def chain (μ : Measure X) (a : X → X → ℝ) (m : ℕ) (x z : X) : ℝ :=
  ∫ V : Fin m → X, ∏ t : Fin (m + 1),
    a (Fin.cons (α := fun _ => X) x V t) (Fin.snoc (α := fun _ => X) V z t)
    ∂(Measure.pi fun _ => μ)

/-- Integrate out the point at index `0`. -/
theorem integral_cons {m : ℕ} {F : (Fin (m + 1) → X) → ℝ} (hF : Measurable F) {C : ℝ}
    (hb : ∀ W, |F W| ≤ C) :
    ∫ W, F W ∂(Measure.pi fun _ => μ)
      = ∫ y, ∫ V : Fin m → X, F (Fin.cons (α := fun _ => X) y V) ∂(Measure.pi fun _ => μ) ∂μ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0
  have h1 : ∫ W, F W ∂(Measure.pi fun _ => μ)
      = ∫ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin m => μ)) := by
    rw [← hmp.integral_comp' (g := fun p => F (e.symm p))]
    simp
  rw [h1, integral_prod]
  · congr 1; funext y; congr 1; funext V
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    change F (Fin.insertNth 0 y V) = F (Fin.cons y V)
    rw [Fin.insertNth_zero']
  · exact integrable_of_bdd (hF.comp e.symm.measurable) (fun p => hb _)

theorem measurable_prod_path {n : ℕ} {a : X → X → ℝ} (ha : Bdd a) {f g : (Fin n → X) → Fin (n + 1) → X}
    (hf : ∀ t, Measurable fun W => f W t) (hg : ∀ t, Measurable fun W => g W t) :
    Measurable fun W => ∏ t : Fin (n + 1), a (f W t) (g W t) :=
  Finset.measurable_prod _ fun t _ => ha.meas.comp ((hf t).prodMk (hg t))

theorem abs_prod_le {ι : Type*} [Fintype ι] {u : ι → ℝ} {C : ℝ} (hu : ∀ i, |u i| ≤ C) :
    |∏ i, u i| ≤ C ^ Fintype.card ι := by
  rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hu i)

theorem chain_zero (a : X → X → ℝ) (x z : X) : chain μ a 0 x z = a x z := by
  unfold chain
  have hc : ∀ V : Fin 0 → X, Fin.cons (α := fun _ => X) x V 0 = x := fun V => Fin.cons_zero _ _
  have hs : ∀ V : Fin 0 → X, Fin.snoc (α := fun _ => X) V z 0 = z := fun V => by
    simpa using (Fin.snoc_last (α := fun _ => X) z V)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, hc, hs]
  rw [integral_const]; simp

theorem chain_succ {a : X → X → ℝ} (ha : Bdd a) (m : ℕ) (x z : X) :
    chain μ a (m + 1) x z = ∫ y, a x y * chain μ a m y z ∂μ := by
  obtain ⟨C, hC⟩ := ha.bdd
  unfold chain
  have hmeas : Measurable fun V : Fin (m + 1) → X => ∏ t : Fin (m + 2),
      a (Fin.cons (α := fun _ => X) x V t) (Fin.snoc (α := fun _ => X) V z t) := by
    refine Finset.measurable_prod _ fun t _ => ?_
    have h1 : Measurable fun V : Fin (m + 1) → X => Fin.cons (α := fun _ => X) x V t := by
      refine Fin.cases ?_ (fun s => ?_) t
      · simp
      · simpa using measurable_pi_apply s
    have h2 : Measurable fun V : Fin (m + 1) → X => Fin.snoc (α := fun _ => X) V z t := by
      refine Fin.lastCases ?_ (fun s => ?_) t
      · simp
      · simpa using measurable_pi_apply s
    simpa [Function.comp_def] using ha.meas.comp (h1.prodMk h2)
  rw [integral_cons hmeas (C := C ^ Fintype.card (Fin (m + 2))) (fun W => abs_prod_le fun t => hC _ _)]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext V
  rw [Fin.prod_univ_succ]
  simp [← Fin.cons_snoc_eq_snoc_cons]

theorem chain_eq_iter {a : X → X → ℝ} (ha : Bdd a) : ∀ m x z, chain μ a m x z = iter μ a m x z
  | 0, x, z => chain_zero a x z
  | m + 1, x, z => by
    rw [chain_succ ha m x z]
    change _ = ∫ y, a x y * iter μ a m y z ∂μ
    congr 1; funext y; rw [chain_eq_iter ha m y z]

theorem cyc_succ {a : X → X → ℝ} (ha : Bdd a) (m : ℕ) :
    cyc μ a (m + 1) = ∫ x, iter μ a m x x ∂μ := by
  obtain ⟨C, hC⟩ := ha.bdd
  unfold cyc
  have hmeas : Measurable fun W : Fin (m + 1) → X => ∏ t, a (W t) (W (finRotate (m + 1) t)) :=
    Finset.measurable_prod _ fun t _ => by
      have h1 : Measurable fun W : Fin (m + 1) → X => W t := measurable_pi_apply t
      have h2 : Measurable fun W : Fin (m + 1) → X => W (finRotate (m + 1) t) :=
        measurable_pi_apply _
      simpa [Function.comp_def] using ha.meas.comp (h1.prodMk h2)
  rw [integral_cons hmeas (C := C ^ Fintype.card (Fin (m + 1))) (fun W => abs_prod_le fun t => hC _ _)]
  congr 1; funext y
  rw [← chain_eq_iter ha m y y]
  unfold chain
  congr 1; funext V
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Fin.snoc_eq_cons_rotate]

theorem iter_symm {a : X → X → ℝ} (ha : Bdd a) (hs : ∀ x y, a x y = a y x) :
    ∀ i x z, iter μ a i x z = iter μ a i z x
  | 0, x, z => hs x z
  | i + 1, x, z => by
    have e := iter_add (μ := μ) ha i 0
    simp only [Nat.add_zero] at e
    change ∫ y, a x y * iter μ a i y z ∂μ = _
    rw [e]
    change _ = ∫ y, iter μ a i z y * iter μ a 0 y x ∂μ
    congr 1; funext y
    rw [iter_symm ha hs i z y]
    change _ = iter μ a i y z * a y x
    rw [hs y x, mul_comm]

/-- `cyc μ a (2j) = hs(a^{∗j})` for symmetric `a`, `j ≥ 1`. -/
theorem cyc_even {a : X → X → ℝ} (ha : Bdd a) (hsy : ∀ x y, a x y = a y x) (j : ℕ) (hj : 1 ≤ j) :
    cyc μ a (2 * j) = traceSeq μ a (2 * j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h2 : 2 * (i + 1) = (i + i + 1) + 1 := by ring
  have h3 : (i + i + 1 + 1) / 2 - 1 = i := by omega
  rw [h2, cyc_succ ha, iter_add ha i i]
  unfold traceSeq
  rw [h3]
  unfold hs conv
  congr 1; funext x
  congr 1; funext y
  rw [iter_symm ha hsy i y x, sq]

#print axioms chain_eq_iter
#print axioms cyc_succ
#print axioms cyc_even

end MassGap.CyclicKernel
