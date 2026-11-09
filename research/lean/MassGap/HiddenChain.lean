import Mathlib
import MassGap.KernelPower
import MassGap.CyclicKernel

/-!
# MassGap.HiddenChain — open chains whose steps carry a hidden variable

Two probability spaces `(X, μ)` (a slice) and `(Y, ν)` (the hidden variable of one step) and a weight
`w : X → Y → X → ℝ`. A path is a pair of sequences `V : ℕ → X`, `A : ℕ → Y`; step `t` goes from
`V t` to `V (t+1)` through `A t` with weight `w (V t) (A t) (V (t+1))`.

* `chain μ ν w m G x` integrates `G V A · ∏_{t<m} w (V t) (A t) (V (t+1))` over `V 1, …, V m` and
  `A 0, …, A (m−1)`, with `V 0 = x`, by peeling the first step.
* `chain_split` — Markov property: an insertion local on the first `a` steps times one read from step
  `a` on splits into two chains joined at `V a`.
* `chain_end_succ`, `chain_end_kern`, `chain_end_iter` — a chain whose insertion reads only its end
  point is the iterated step kernel `kern ν w x y = ∫ w x a y dν(a)` applied to it.
* `bridge` — `chain` is the product-measure integral over `Fin`-indexed paths.
* `chain_rev` — for a weight symmetric under `x ↔ y`, `a ↦ ι a` (`ι` measure preserving and
  involutive), reading a path backwards exchanges its two end vectors.
-/

namespace MassGap.HiddenChain

open MeasureTheory MassGap.KernelPower

/-! ## Sequences -/

/-- Push a point onto the front of a sequence. -/
def scons {α : Type} (a : α) (s : ℕ → α) : ℕ → α
  | 0 => a
  | i + 1 => s i

/-- Drop the first `d` points of a sequence. -/
def sshift {α : Type} (s : ℕ → α) (d : ℕ) : ℕ → α := fun i => s (i + d)

theorem sshift_sshift {α : Type} (s : ℕ → α) (a b : ℕ) : sshift (sshift s a) b = sshift s (b + a) := by
  funext i; simp only [sshift, add_assoc]

theorem measurable_scons {α : Type} [MeasurableSpace α] :
    Measurable (fun p : α × (ℕ → α) => scons p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  cases i with
  | zero => exact measurable_fst
  | succ i => exact (measurable_pi_apply i).comp measurable_snd

theorem measurable_sshift {α : Type} [MeasurableSpace α] (d : ℕ) :
    Measurable (fun s : ℕ → α => sshift s d) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i + d)

set_option linter.unusedSectionVars false

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty Y]

/-! ## The chain -/

/-- The open chain of `m` steps from `x`, with insertion `G`. -/
noncomputable def chain (μ : Measure X) (ν : Measure Y) (w : X → Y → X → ℝ) :
    ℕ → ((ℕ → X) → (ℕ → Y) → ℝ) → X → ℝ
  | 0, G, x => G (fun _ => x) (fun _ => Classical.arbitrary Y)
  | m + 1, G, x => ∫ y, ∫ a, w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y ∂ν ∂μ

variable {μ : Measure X} {ν : Measure Y} {w : X → Y → X → ℝ}

theorem chain_zero (G : (ℕ → X) → (ℕ → Y) → ℝ) (x : X) :
    chain μ ν w 0 G x = G (fun _ => x) (fun _ => Classical.arbitrary Y) := rfl

theorem chain_succ (m : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) (x : X) :
    chain μ ν w (m + 1) G x
      = ∫ y, ∫ a, w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y ∂ν ∂μ := rfl

/-- Joint measurability of the step weight. -/
def WMeas (w : X → Y → X → ℝ) : Prop := Measurable (fun p : X × Y × X => w p.1 p.2.1 p.2.2)

/-- Measurability in a parameter. -/
theorem measurable_chain [SFinite μ] [SFinite ν] (hw : WMeas w) :
    ∀ (m : ℕ) {P : Type} [MeasurableSpace P] {G : P → (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : P × (ℕ → X) × (ℕ → Y) => G q.1 q.2.1 q.2.2) →
      Measurable (fun q : P × X => chain μ ν w m (G q.1) q.2)
  | 0, P, _, G, hG => by
    show Measurable (fun q : P × X => G q.1 (fun _ => q.2) (fun _ => Classical.arbitrary Y))
    exact hG.comp (measurable_fst.prodMk
      ((measurable_pi_lambda _ fun _ => measurable_snd).prodMk measurable_const))
  | m + 1, P, _, G, hG => by
    have hG' : Measurable (fun q : ((P × X) × Y) × (ℕ → X) × (ℕ → Y) =>
        G q.1.1.1 (scons q.1.1.2 q.2.1) (scons q.1.2 q.2.2)) := by
      refine hG.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_scons.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_fst.comp measurable_snd))).prodMk
        (measurable_scons.comp ((measurable_snd.comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))))
    have ih := measurable_chain hw m (P := (P × X) × Y)
      (G := fun r V A => G r.1.1 (scons r.1.2 V) (scons r.2 A)) hG'
    have h1 : Measurable (fun q : ((P × X) × X) × Y =>
        w q.1.1.2 q.2 q.1.2 * chain μ ν w m
          (fun V A => G q.1.1.1 (scons q.1.1.2 V) (scons q.2 A)) q.1.2) := by
      refine (hw.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).mul ?_
      exact ih.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
    have h2 := (h1.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have h3 := (h2.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
    exact h3

theorem measurable_chain' [SFinite μ] [SFinite ν] (hw : WMeas w) (m : ℕ)
    {G : (ℕ → X) → (ℕ → Y) → ℝ} (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2)) :
    Measurable (chain μ ν w m G) := by
  have := measurable_chain (μ := μ) (ν := ν) hw m (P := Unit) (G := fun _ => G) (hG.comp measurable_snd)
  exact this.comp ((measurable_const : Measurable (fun _ : X => ())).prodMk measurable_id)

theorem abs_chain_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C : ℝ}
    (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ} {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∀ x, |chain μ ν w m G x| ≤ C ^ m * B
  | 0, G, B, hG, x => by rw [chain_zero, pow_zero, one_mul]; exact hG _ _
  | m + 1, G, B, hG, x => by
    rw [chain_succ]
    refine abs_integral_le fun y => abs_integral_le fun a => ?_
    rw [abs_mul]
    have h1 := abs_chain_le hwb m (G := fun V A => G (scons x V) (scons a A)) (fun V A => hG _ _) y
    have hC : 0 ≤ C := (abs_nonneg _).trans (hwb x a y)
    calc |w x a y| * |chain μ ν w m (fun V A => G (scons x V) (scons a A)) y|
        ≤ C * (C ^ m * B) := mul_le_mul (hwb x a y) h1 (abs_nonneg _) hC
      _ = C ^ (m + 1) * B := by ring

theorem chain_const_mul (c : ℝ) :
    ∀ (m : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) (x : X),
      chain μ ν w m (fun V A => c * G V A) x = c * chain μ ν w m G x
  | 0, G, x => rfl
  | m + 1, G, x => by
    rw [chain_succ, chain_succ, ← integral_const_mul]
    congr 1; funext y
    rw [← integral_const_mul]
    congr 1; funext a
    rw [chain_const_mul c m (fun V A => G (scons x V) (scons a A)) y]
    ring

/-- `chain` reads `G` only on paths starting at `x`. -/
theorem chain_congr :
    ∀ (m : ℕ) {G H : (ℕ → X) → (ℕ → Y) → ℝ} {x : X},
      (∀ V A, V 0 = x → G V A = H V A) → chain μ ν w m G x = chain μ ν w m H x
  | 0, G, H, x, h => h _ _ rfl
  | m + 1, G, H, x, h => by
    rw [chain_succ, chain_succ]
    congr 1; funext y; congr 1; funext a; congr 1
    exact chain_congr m (fun V A _ => h _ _ rfl)

theorem chain_mul_start (g : X → ℝ) (m : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) (x : X) :
    chain μ ν w m (fun V A => g (V 0) * G V A) x = g x * chain μ ν w m G x := by
  rw [← chain_const_mul]
  exact chain_congr m (fun V A hV => by rw [hV])

/-! ## Integrability of one step -/

section Step

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem step_meas (hw : WMeas w) (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ}
    (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2)) (x : X) :
    Measurable (fun q : X × Y => w x q.2 q.1
      * chain μ ν w m (fun V A => G (scons x V) (scons q.2 A)) q.1) := by
  have hG' : Measurable (fun q : Y × (ℕ → X) × (ℕ → Y) => G (scons x q.2.1) (scons q.1 q.2.2)) :=
    hG.comp ((measurable_scons.comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_scons.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
  have ih := measurable_chain (μ := μ) (ν := ν) hw m (P := Y) (G := fun a V A => G (scons x V) (scons a A)) hG'
  refine (hw.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).mul ?_
  exact ih.comp (measurable_snd.prodMk measurable_fst)

theorem step_int_inner (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) (m : ℕ)
    {G : (ℕ → X) → (ℕ → Y) → ℝ} (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2))
    {B : ℝ} (hGb : ∀ V A, |G V A| ≤ B) (x y : X) :
    Integrable (fun a => w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y) ν := by
  refine integrable_of_bdd ((step_meas hw m hG x).comp (measurable_const.prodMk measurable_id))
    (C := C * (C ^ m * B)) (fun a => ?_)
  rw [abs_mul]
  exact mul_le_mul (hwb x a y) (abs_chain_le hwb m (fun V A => hGb _ _) y) (abs_nonneg _)
    ((abs_nonneg _).trans (hwb x a y))

theorem step_int_outer (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) (m : ℕ)
    {G : (ℕ → X) → (ℕ → Y) → ℝ} (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2))
    {B : ℝ} (hGb : ∀ V A, |G V A| ≤ B) (x : X) :
    Integrable (fun y => ∫ a, w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y ∂ν) μ := by
  refine integrable_of_bdd
    ((step_meas hw m hG x).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    (C := C * (C ^ m * B)) (fun y => abs_integral_le fun a => ?_)
  rw [abs_mul]
  exact mul_le_mul (hwb x a y) (abs_chain_le hwb m (fun V A => hGb _ _) y) (abs_nonneg _)
    ((abs_nonneg _).trans (hwb x a y))

theorem chain_add (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G H : (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) →
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => H q.1 q.2) →
      ∀ {BG BH : ℝ}, (∀ V A, |G V A| ≤ BG) → (∀ V A, |H V A| ≤ BH) →
      ∀ x, chain μ ν w m (fun V A => G V A + H V A) x = chain μ ν w m G x + chain μ ν w m H x
  | 0, G, H, _, _, _, _, _, _, x => rfl
  | m + 1, G, H, hG, hH, BG, BH, hGb, hHb, x => by
    rw [chain_succ, chain_succ, chain_succ,
      ← integral_add (step_int_outer hw hwb m hG hGb x) (step_int_outer hw hwb m hH hHb x)]
    congr 1; funext y
    rw [← integral_add (step_int_inner hw hwb m hG hGb x y) (step_int_inner hw hwb m hH hHb x y)]
    congr 1; funext a
    have hG' : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G (scons x q.1) (scons a q.2)) :=
      hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    have hH' : Measurable (fun q : (ℕ → X) × (ℕ → Y) => H (scons x q.1) (scons a q.2)) :=
      hH.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    rw [chain_add hw hwb m (G := fun V A => G (scons x V) (scons a A))
      (H := fun V A => H (scons x V) (scons a A)) hG' hH' (fun V A => hGb _ _) (fun V A => hHb _ _) y]
    ring

theorem chain_mono (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C)
    (hw0 : ∀ x a y, 0 ≤ w x a y) :
    ∀ (m : ℕ) {G H : (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) →
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => H q.1 q.2) →
      ∀ {BG BH : ℝ}, (∀ V A, |G V A| ≤ BG) → (∀ V A, |H V A| ≤ BH) →
      (∀ V A, G V A ≤ H V A) → ∀ x, chain μ ν w m G x ≤ chain μ ν w m H x
  | 0, G, H, _, _, _, _, _, _, hle, x => hle _ _
  | m + 1, G, H, hG, hH, BG, BH, hGb, hHb, hle, x => by
    rw [chain_succ, chain_succ]
    refine integral_mono (step_int_outer hw hwb m hG hGb x) (step_int_outer hw hwb m hH hHb x)
      fun y => ?_
    refine integral_mono (step_int_inner hw hwb m hG hGb x y) (step_int_inner hw hwb m hH hHb x y)
      fun a => ?_
    have hG' : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G (scons x q.1) (scons a q.2)) :=
      hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    have hH' : Measurable (fun q : (ℕ → X) × (ℕ → Y) => H (scons x q.1) (scons a q.2)) :=
      hH.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))
    exact mul_le_mul_of_nonneg_left
      (chain_mono hw hwb hw0 m (G := fun V A => G (scons x V) (scons a A))
        (H := fun V A => H (scons x V) (scons a A)) hG' hH' (fun V A => hGb _ _) (fun V A => hHb _ _)
        (fun V A => hle _ _) y) (hw0 x a y)

theorem abs_chain_le_chain_abs (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C)
    (hw0 : ∀ x a y, 0 ≤ w x a y) (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ}
    (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2)) {B : ℝ}
    (hGb : ∀ V A, |G V A| ≤ B) (x : X) :
    |chain μ ν w m G x| ≤ chain μ ν w m (fun V A => |G V A|) x := by
  have hA : Measurable (fun q : (ℕ → X) × (ℕ → Y) => |G q.1 q.2|) := hG.abs
  have hAb : ∀ V A, |(|G V A|)| ≤ B := fun V A => by rw [abs_abs]; exact hGb V A
  have hN : Measurable (fun q : (ℕ → X) × (ℕ → Y) => (-1) * G q.1 q.2) := hG.const_mul _
  have hNb : ∀ V A, |(-1) * G V A| ≤ B := fun V A => by
    rw [abs_mul, abs_neg, abs_one, one_mul]; exact hGb V A
  have h1 := chain_mono (μ := μ) (ν := ν) hw hwb hw0 m (G := G) (H := fun V A => |G V A|) hG hA hGb hAb
    (fun V A => le_abs_self _) x
  have h2 := chain_mono (μ := μ) (ν := ν) hw hwb hw0 m (G := fun V A => (-1) * G V A) (H := fun V A => |G V A|)
    hN hA hNb hAb (fun V A => by rw [neg_one_mul]; exact neg_le_abs _) x
  rw [chain_const_mul] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

end Step

/-! ## The Markov property -/

/-- `G` reads only `V 0, …, V a` and `A 0, …, A (a−1)`. -/
def LocalUpTo (a : ℕ) (G : (ℕ → X) → (ℕ → Y) → ℝ) : Prop :=
  ∀ V V' A A', (∀ i ≤ a, V i = V' i) → (∀ i < a, A i = A' i) → G V A = G V' A'

theorem LocalUpTo.mono {a b : ℕ} {G : (ℕ → X) → (ℕ → Y) → ℝ} (h : LocalUpTo a G) (hab : a ≤ b) :
    LocalUpTo b G :=
  fun V V' A A' hV hA => h V V' A A' (fun i hi => hV i (hi.trans hab)) (fun i hi => hA i (by omega))

theorem localUpTo_const (a : ℕ) (c : ℝ) : LocalUpTo (X := X) (Y := Y) a (fun _ _ => c) :=
  fun _ _ _ _ _ _ => rfl

theorem LocalUpTo.mul {a : ℕ} {G H : (ℕ → X) → (ℕ → Y) → ℝ} (hG : LocalUpTo a G)
    (hH : LocalUpTo a H) : LocalUpTo a (fun V A => G V A * H V A) :=
  fun V V' A A' hV hA => by
    show G V A * H V A = G V' A' * H V' A'
    rw [hG V V' A A' hV hA, hH V V' A A' hV hA]

/-- **Markov property.** -/
theorem chain_split :
    ∀ (a b : ℕ) {G1 : (ℕ → X) → (ℕ → Y) → ℝ} (G2 : (ℕ → X) → (ℕ → Y) → ℝ) (x : X),
      LocalUpTo a G1 →
      chain μ ν w (a + b) (fun V A => G1 V A * G2 (sshift V a) (sshift A a)) x
        = chain μ ν w a (fun V A => G1 V A * chain μ ν w b G2 (V a)) x
  | 0, b, G1, G2, x, hl => by
    rw [Nat.zero_add, chain_zero]
    have h : ∀ V A, V 0 = x → G1 V A * G2 (sshift V 0) (sshift A 0)
        = G1 (fun _ => x) (fun _ => Classical.arbitrary Y) * G2 V A := by
      intro V A hV
      rw [hl V (fun _ => x) A (fun _ => Classical.arbitrary Y)
        (fun i hi => by rw [Nat.le_zero.mp hi]; exact hV) (fun i hi => absurd hi (Nat.not_lt_zero _))]
      rfl
    rw [chain_congr b h, chain_const_mul]
  | a + 1, b, G1, G2, x, hl => by
    rw [show a + 1 + b = (a + b) + 1 by omega, chain_succ, chain_succ]
    congr 1; funext y; congr 1; funext a'; congr 1
    have hl' : LocalUpTo a (fun V A => G1 (scons x V) (scons a' A)) := by
      intro V V' A A' hV hA
      refine hl _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
      · cases i with
        | zero => rfl
        | succ i => exact hV i (by omega)
      · cases i with
        | zero => rfl
        | succ i => exact hA i (by omega)
    exact chain_split a b G2 y hl'

/-! ## The step kernel -/

/-- One step with the hidden variable integrated. -/
noncomputable def kern (ν : Measure Y) (w : X → Y → X → ℝ) : X → X → ℝ := fun x y => ∫ a, w x a y ∂ν

theorem chain_end_succ (g : X → ℝ) (m : ℕ) (x : X) :
    chain μ ν w (m + 1) (fun V _ => g (V (m + 1))) x
      = ∫ y, kern ν w x y * chain μ ν w m (fun V _ => g (V m)) y ∂μ := by
  rw [chain_succ]
  congr 1; funext y
  exact integral_mul_const _ _

theorem chain_end_kern (x' : X) :
    ∀ (m : ℕ) (z : X), chain μ ν w m (fun V _ => kern ν w (V m) x') z = iter μ (kern ν w) m z x'
  | 0, z => rfl
  | m + 1, z => by
    rw [chain_end_succ (fun y => kern ν w y x') m z]
    change _ = ∫ y, kern ν w z y * iter μ (kern ν w) m y x' ∂μ
    congr 1; funext y; rw [chain_end_kern x' m y]

theorem chain_end_eig {φ : X → ℝ} {c : ℝ} (heig : ∀ z, ∫ y, kern ν w z y * φ y ∂μ = c * φ z) :
    ∀ (m : ℕ) (z : X), chain μ ν w m (fun V _ => φ (V m)) z = c ^ m * φ z
  | 0, z => by rw [chain_zero, pow_zero, one_mul]
  | m + 1, z => by
    rw [chain_end_succ]
    simp_rw [chain_end_eig heig m]
    have : (fun y => kern ν w z y * (c ^ m * φ y)) = fun y => c ^ m * (kern ν w z y * φ y) := by
      funext y; ring
    rw [this, integral_const_mul, heig z]
    ring

section Kern

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem measurable_kern [SFinite ν] (hw : WMeas w) : Measurable (Function.uncurry (kern ν w)) := by
  have h : Measurable (fun q : (X × X) × Y => w q.1.1 q.2 q.1.2) :=
    hw.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem abs_kern_le {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) (x y : X) : |kern ν w x y| ≤ C :=
  abs_integral_le fun a => hwb x a y

theorem bdd_kern (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) : Bdd (kern ν w) :=
  ⟨measurable_kern hw, C, abs_kern_le hwb⟩

/-- A chain reading only its end point is the iterated kernel applied to it. -/
theorem chain_end_iter (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) {g : X → ℝ}
    (hg : Measurable g) {Bg : ℝ} (hgb : ∀ z, |g z| ≤ Bg) :
    ∀ (m : ℕ) (x : X), chain μ ν w (m + 1) (fun V _ => g (V (m + 1))) x
      = ∫ z, iter μ (kern ν w) m x z * g z ∂μ
  | 0, x => chain_end_succ g 0 x
  | m + 1, x => by
    rw [chain_end_succ]
    simp_rw [chain_end_iter hw hwb hg hgb m]
    have hk := bdd_kern (ν := ν) hw hwb
    have hki := hk.iter (μ := μ) m
    obtain ⟨Ci, hCi⟩ := hki.bdd
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (abs_kern_le (ν := ν) hwb x x)
    have hF : Measurable (Function.uncurry
        (fun y z => kern ν w x y * (iter μ (kern ν w) m y z * g z))) :=
      ((hk.row x).comp measurable_fst).mul (hki.meas.mul (hg.comp measurable_snd))
    have hFb : ∀ y z, |kern ν w x y * (iter μ (kern ν w) m y z * g z)| ≤ C * (Ci * Bg) := by
      intro y z
      rw [abs_mul, abs_mul]
      exact mul_le_mul (abs_kern_le hwb x y) (mul_le_mul (hCi y z) (hgb z) (abs_nonneg _)
        ((abs_nonneg _).trans (hCi y z))) (by positivity) hC0
    calc ∫ y, kern ν w x y * ∫ z, iter μ (kern ν w) m y z * g z ∂μ ∂μ
        = ∫ y, ∫ z, kern ν w x y * (iter μ (kern ν w) m y z * g z) ∂μ ∂μ := by
          congr 1; funext y; rw [integral_const_mul]
      _ = ∫ z, ∫ y, kern ν w x y * (iter μ (kern ν w) m y z * g z) ∂μ ∂μ := swap_bdd hF hFb
      _ = ∫ z, iter μ (kern ν w) (m + 1) x z * g z ∂μ := by
          congr 1; funext z
          change _ = (∫ y, kern ν w x y * iter μ (kern ν w) m y z ∂μ) * g z
          rw [← integral_mul_const]; congr 1; funext y; ring

end Kern

/-! ## `Fin`-indexed paths -/

/-- A `Fin`-indexed sequence of slices, extended by its last point. -/
def extX {m : ℕ} (V : Fin (m + 1) → X) : ℕ → X :=
  fun i => if h : i < m + 1 then V ⟨i, h⟩ else V (Fin.last m)

/-- A `Fin`-indexed sequence of hidden variables, extended arbitrarily. -/
noncomputable def extY {m : ℕ} (A : Fin m → Y) : ℕ → Y :=
  fun i => if h : i < m then A ⟨i, h⟩ else Classical.arbitrary Y

theorem extX_zero {m : ℕ} (V : Fin (m + 1) → X) : extX V 0 = V 0 := by
  simp only [extX]
  rw [dif_pos (show 0 < m + 1 by omega)]
  exact congrArg V (Fin.ext (by simp))

theorem extX_last {m : ℕ} (V : Fin (m + 1) → X) : extX V m = V (Fin.last m) := by
  simp only [extX]
  rw [dif_pos (show m < m + 1 by omega)]
  rfl

theorem extX_cons {m : ℕ} (x : X) (V : Fin (m + 1) → X) :
    extX (Fin.cons x V : Fin (m + 1 + 1) → X) = scons x (extX V) := by
  funext i
  cases i with
  | zero =>
    simp only [extX, scons]
    rw [dif_pos (show 0 < m + 1 + 1 by omega)]
    rfl
  | succ i =>
    simp only [extX, scons]
    by_cases h : i < m + 1
    · rw [dif_pos (show i + 1 < m + 1 + 1 by omega), dif_pos h]
      exact Fin.cons_succ (α := fun _ => X) x V ⟨i, h⟩
    · rw [dif_neg (show ¬ (i + 1 < m + 1 + 1) by omega), dif_neg h]
      exact Fin.cons_succ (α := fun _ => X) x V (Fin.last m)

theorem extY_cons {m : ℕ} (a : Y) (A : Fin m → Y) :
    extY (Fin.cons a A : Fin (m + 1) → Y) = scons a (extY A) := by
  funext i
  cases i with
  | zero =>
    simp only [extY, scons]
    rw [dif_pos (show 0 < m + 1 by omega)]
    rfl
  | succ i =>
    simp only [extY, scons]
    by_cases h : i < m
    · rw [dif_pos (show i + 1 < m + 1 by omega), dif_pos h]
      exact Fin.cons_succ (α := fun _ => Y) a A ⟨i, h⟩
    · rw [dif_neg (show ¬ (i + 1 < m + 1) by omega), dif_neg h]

theorem measurable_extX {m : ℕ} : Measurable (extX (X := X) (m := m)) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < m + 1
  · simp only [extX, dif_pos h]; exact measurable_pi_apply _
  · simp only [extX, dif_neg h]; exact measurable_pi_apply _

theorem measurable_extY {m : ℕ} : Measurable (extY (Y := Y) (m := m)) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < m
  · simp only [extY, dif_pos h]; exact measurable_pi_apply _
  · simp only [extY, dif_neg h]; exact measurable_const

/-- The step product along a `Fin`-indexed path. -/
noncomputable def pathW (w : X → Y → X → ℝ) {m : ℕ} (V : Fin (m + 1) → X) (A : Fin m → Y) : ℝ :=
  ∏ t : Fin m, w (V t.castSucc) (A t) (V t.succ)

theorem measurable_pathW (hw : WMeas w) (m : ℕ) :
    Measurable (fun q : (Fin (m + 1) → X) × (Fin m → Y) => pathW w q.1 q.2) := by
  unfold pathW
  refine Finset.measurable_prod _ fun t _ => ?_
  have hw' : Measurable (fun p : X × Y × X => w p.1 p.2.1 p.2.2) := hw
  have h1 : Measurable (fun q : (Fin (m + 1) → X) × (Fin m → Y) => (q.1 t.castSucc, q.2 t, q.1 t.succ)) :=
    ((measurable_pi_apply t.castSucc).comp measurable_fst).prodMk
      (((measurable_pi_apply t).comp measurable_snd).prodMk
        ((measurable_pi_apply t.succ).comp measurable_fst))
  exact hw'.comp h1

theorem abs_pathW_le {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) {m : ℕ} (V : Fin (m + 1) → X)
    (A : Fin m → Y) : |pathW w V A| ≤ C ^ m := by
  have := CyclicKernel.abs_prod_le (u := fun t : Fin m => w (V t.castSucc) (A t) (V t.succ))
    (fun t => hwb _ _ _)
  simpa [pathW, Fintype.card_fin] using this

theorem pathW_cons {m : ℕ} (x : X) (V : Fin (m + 1) → X) (a : Y) (A : Fin m → Y) :
    pathW w (Fin.cons x V : Fin (m + 1 + 1) → X) (Fin.cons a A : Fin (m + 1) → Y)
      = w x a (V 0) * pathW w V A := by
  unfold pathW
  rw [Fin.prod_univ_succ]
  congr 1

theorem abs_mul_le_of {a b B D : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ D) : |a * b| ≤ B * D := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

section Bridge

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem swap2 {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α} {μb : Measure β}
    [IsFiniteMeasure μa] [IsFiniteMeasure μb] {F : α → β → ℝ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hb : ∀ a b, |F a b| ≤ C) :
    ∫ a, ∫ b, F a b ∂μb ∂μa = ∫ b, ∫ a, F a b ∂μa ∂μb :=
  integral_integral_swap (integrable_of_bdd hF (fun p => hb p.1 p.2))

/-- **The bridge.** `chain` is the integral over `Fin`-indexed paths. -/
theorem bridge (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C) :
    ∀ (m : ℕ) {G : (ℕ → X) → (ℕ → Y) → ℝ},
      Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2) → ∀ {B : ℝ}, (∀ V A, |G V A| ≤ B) →
      ∫ V : Fin (m + 1) → X, ∫ A : Fin m → Y, G (extX V) (extY A) * pathW w V A
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => μ)
        = ∫ x, chain μ ν w m G x ∂μ
  | 0, G, hG, B, hGb => by
    have e1 : ∀ (V : Fin 1 → X) (A : Fin 0 → Y), G (extX V) (extY A) * pathW w V A
        = G (fun _ => V 0) (fun _ => Classical.arbitrary Y) := by
      intro V A
      have hx : extX V = fun _ => V 0 := by
        funext i; simp only [extX]; split_ifs with h
        · exact congrArg V (Fin.ext (by simp; omega))
        · rfl
      have hy : extY A = fun _ => Classical.arbitrary Y := by
        funext i; simp only [extY]; rw [dif_neg (show ¬ (i < 0) by omega)]
      rw [hx, hy]; simp [pathW]
    simp_rw [e1]
    have hF : Measurable (fun V : Fin 1 → X => G (fun _ => V 0) (fun _ => Classical.arbitrary Y)) :=
      hG.comp (f := fun V : Fin 1 → X => ((fun _ : ℕ => V 0), (fun _ : ℕ => Classical.arbitrary Y)))
        ((measurable_pi_lambda _ fun _ => measurable_pi_apply 0).prodMk measurable_const)
    have hc : ∀ V : Fin 1 → X, ∫ _A : Fin 0 → Y, G (fun _ => V 0) (fun _ => Classical.arbitrary Y)
        ∂(Measure.pi fun _ => ν) = G (fun _ => V 0) (fun _ => Classical.arbitrary Y) := by
      intro V; rw [integral_const]; simp
    simp_rw [hc]
    rw [CyclicKernel.integral_cons hF (C := B) (fun V => hGb _ _)]
    congr 1; funext y
    simp [chain_zero]
  | m + 1, G, hG, B, hGb => by
    -- joint measurability and bound of the path integrand at length `m + 1`
    have hJ : ∀ (n : ℕ) {H : (ℕ → X) → (ℕ → Y) → ℝ},
        Measurable (fun q : (ℕ → X) × (ℕ → Y) => H q.1 q.2) →
        Measurable (fun q : (Fin (n + 1) → X) × (Fin n → Y) => H (extX q.1) (extY q.2) * pathW w q.1 q.2) :=
      fun n H hH => (hH.comp ((measurable_extX.comp measurable_fst).prodMk
        (measurable_extY.comp measurable_snd))).mul (measurable_pathW hw n)
    -- outer peel
    have hO : Measurable (fun V : Fin (m + 1 + 1) → X => ∫ A : Fin (m + 1) → Y,
        G (extX V) (extY A) * pathW w V A ∂(Measure.pi fun _ => ν)) :=
      ((hJ (m + 1) hG).stronglyMeasurable.integral_prod_right' (ν := Measure.pi fun _ => ν)).measurable
    rw [CyclicKernel.integral_cons hO (C := B * C ^ (m + 1)) (fun V => abs_integral_le fun A =>
      abs_mul_le_of (hGb _ _) (abs_pathW_le hwb V A))]
    -- the hidden-variable peel and the rewrite of the integrand
    set Gxa : X → Y → (ℕ → X) → (ℕ → Y) → ℝ := fun x a V A => G (scons x V) (scons a A) * w x a (V 0)
    have hGxa : ∀ x a, Measurable (fun q : (ℕ → X) × (ℕ → Y) => Gxa x a q.1 q.2) := by
      intro x a
      refine (hG.comp ((measurable_scons.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_scons.comp (measurable_const.prodMk measurable_snd)))).mul ?_
      exact hw.comp (measurable_const.prodMk (measurable_const.prodMk
        ((measurable_pi_apply 0).comp measurable_fst)))
    have hGxab : ∀ x a V A, |Gxa x a V A| ≤ B * C := fun x a V A =>
      abs_mul_le_of (hGb _ _) (hwb _ _ _)
    have hinner : ∀ (x : X) (V' : Fin (m + 1) → X),
        ∫ A : Fin (m + 1) → Y, G (extX (Fin.cons x V' : Fin (m + 1 + 1) → X)) (extY A)
            * pathW w (Fin.cons x V' : Fin (m + 1 + 1) → X) A ∂(Measure.pi fun _ => ν)
          = ∫ a, ∫ A' : Fin m → Y, Gxa x a (extX V') (extY A') * pathW w V' A'
              ∂(Measure.pi fun _ => ν) ∂ν := by
      intro x V'
      have hI : Measurable (fun A : Fin (m + 1) → Y => G (extX (Fin.cons x V' : Fin (m + 1 + 1) → X)) (extY A)
          * pathW w (Fin.cons x V' : Fin (m + 1 + 1) → X) A) :=
        (hJ (m + 1) hG).comp (measurable_const.prodMk measurable_id)
      rw [CyclicKernel.integral_cons hI (C := B * C ^ (m + 1)) (fun A =>
        abs_mul_le_of (hGb _ _) (abs_pathW_le hwb _ A))]
      congr 1; funext a; congr 1; funext A'
      simp only [Gxa]
      rw [extX_cons, extY_cons, pathW_cons, extX_zero]
      ring
    simp_rw [hinner]
    -- swap `V'` and `a`
    have hS1 : ∀ x : X, Measurable (Function.uncurry (fun (V' : Fin (m + 1) → X) (a : Y) =>
        ∫ A' : Fin m → Y, Gxa x a (extX V') (extY A') * pathW w V' A' ∂(Measure.pi fun _ => ν))) := by
      intro x
      have h3 : Measurable (fun q : ((Fin (m + 1) → X) × Y) × (Fin m → Y) =>
          Gxa x q.1.2 (extX q.1.1) (extY q.2) * pathW w q.1.1 q.2) := by
        refine Measurable.mul ?_ ((measurable_pathW hw m).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        simp only [Gxa]
        refine (hG.comp ((measurable_scons.comp (measurable_const.prodMk
          (measurable_extX.comp (measurable_fst.comp measurable_fst)))).prodMk
          (measurable_scons.comp ((measurable_snd.comp measurable_fst).prodMk
            (measurable_extY.comp measurable_snd))))).mul ?_
        exact hw.comp (measurable_const.prodMk ((measurable_snd.comp measurable_fst).prodMk
          ((measurable_pi_apply 0).comp (measurable_extX.comp (measurable_fst.comp measurable_fst)))))
      exact (h3.stronglyMeasurable.integral_prod_right' (ν := Measure.pi fun _ => ν)).measurable
    have hS1b : ∀ (x : X) (V' : Fin (m + 1) → X) (a : Y),
        |∫ A' : Fin m → Y, Gxa x a (extX V') (extY A') * pathW w V' A' ∂(Measure.pi fun _ => ν)|
          ≤ B * C * C ^ m := fun x V' a => abs_integral_le fun A' =>
      abs_mul_le_of (hGxab _ _ _ _) (abs_pathW_le hwb V' A')
    have hstep1 : ∀ x : X, ∫ V' : Fin (m + 1) → X, ∫ a, ∫ A' : Fin m → Y,
          Gxa x a (extX V') (extY A') * pathW w V' A' ∂(Measure.pi fun _ => ν) ∂ν
          ∂(Measure.pi fun _ => μ)
        = ∫ a, ∫ y, w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y ∂μ ∂ν := by
      intro x
      rw [swap2 (hS1 x) (hS1b x)]
      congr 1; funext a
      rw [bridge hw hwb m (hGxa x a) (hGxab x a)]
      congr 1; funext y
      have hc : ∀ V A, V 0 = y → Gxa x a V A = w x a y * G (scons x V) (scons a A) := by
        intro V A hV; simp only [Gxa]; rw [hV, mul_comm]
      rw [chain_congr m hc, chain_const_mul]
    simp_rw [hstep1]
    congr 1; funext x
    rw [chain_succ]
    -- swap `a` and `y`
    have hS2 : Measurable (Function.uncurry (fun (a : Y) (y : X) =>
        w x a y * chain μ ν w m (fun V A => G (scons x V) (scons a A)) y)) :=
      (step_meas hw m hG x).comp (measurable_snd.prodMk measurable_fst)
    exact swap2 hS2 (C := C * (C ^ m * B)) (fun a y =>
      abs_mul_le_of (hwb x a y) (abs_chain_le hwb m (fun V A => hGb _ _) y))

/-! ## Reading a path backwards -/

/-- The slices of a path of length `m`, read backwards. -/
def revX (m : ℕ) (V : ℕ → X) : ℕ → X := fun i => V (m - i)

/-- The hidden variables of a path of length `m`, read backwards and mapped by `ι`. -/
def revY (ι : Y → Y) (m : ℕ) (A : ℕ → Y) : ℕ → Y := fun i => ι (A (m - 1 - i))

theorem chain_rev (hw : WMeas w) {C : ℝ} (hwb : ∀ x a y, |w x a y| ≤ C)
    (ι : Y ≃ᵐ Y) (hι : MeasurePreserving ι ν ν) (hinv : ∀ a, ι (ι a) = a)
    (hsym : ∀ x a y, w x a y = w y (ι a) x) (m : ℕ)
    {G G' : (ℕ → X) → (ℕ → Y) → ℝ}
    (hG : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G q.1 q.2))
    (hG' : Measurable (fun q : (ℕ → X) × (ℕ → Y) => G' q.1 q.2))
    {B : ℝ} (hGb : ∀ V A, |G V A| ≤ B) (hG'b : ∀ V A, |G' V A| ≤ B)
    (hl : LocalUpTo m G) (hrev : ∀ V A, G' V A = G (revX m V) (revY ι m A))
    {g h : X → ℝ} (hg : Measurable g) (hh : Measurable h) {Bg Bh : ℝ}
    (hgb : ∀ z, |g z| ≤ Bg) (hhb : ∀ z, |h z| ≤ Bh) :
    ∫ x, h x * chain μ ν w m (fun V A => G V A * g (V m)) x ∂μ
      = ∫ x, g x * chain μ ν w m (fun V A => G' V A * h (V m)) x ∂μ := by
  -- both sides as path integrals
  have hL : ∀ x, h x * chain μ ν w m (fun V A => G V A * g (V m)) x
      = chain μ ν w m (fun V A => h (V 0) * (G V A * g (V m))) x := fun x =>
    (chain_mul_start h m _ x).symm
  have hR : ∀ x, g x * chain μ ν w m (fun V A => G' V A * h (V m)) x
      = chain μ ν w m (fun V A => g (V 0) * (G' V A * h (V m))) x := fun x =>
    (chain_mul_start g m _ x).symm
  simp_rw [hL, hR]
  have mL : Measurable (fun q : (ℕ → X) × (ℕ → Y) => h (q.1 0) * (G q.1 q.2 * g (q.1 m))) :=
    (hh.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (hG.mul (hg.comp ((measurable_pi_apply m).comp measurable_fst)))
  have mR : Measurable (fun q : (ℕ → X) × (ℕ → Y) => g (q.1 0) * (G' q.1 q.2 * h (q.1 m))) :=
    (hg.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (hG'.mul (hh.comp ((measurable_pi_apply m).comp measurable_fst)))
  have bL : ∀ V A, |h (V 0) * (G V A * g (V m))| ≤ Bh * (B * Bg) := fun V A =>
    abs_mul_le_of (hhb _) (abs_mul_le_of (hGb _ _) (hgb _))
  have bR : ∀ V A, |g (V 0) * (G' V A * h (V m))| ≤ Bg * (B * Bh) := fun V A =>
    abs_mul_le_of (hgb _) (abs_mul_le_of (hG'b _ _) (hhb _))
  rw [← bridge hw hwb m (G := fun V A => h (V 0) * (G V A * g (V m))) mL bL,
    ← bridge hw hwb m (G := fun V A => g (V 0) * (G' V A * h (V m))) mR bR]
  -- change variables on the right
  set eV : (Fin (m + 1) → X) ≃ᵐ (Fin (m + 1) → X) :=
    MeasurableEquiv.arrowCongr' Fin.revPerm (MeasurableEquiv.refl X)
  set eA : (Fin m → Y) ≃ᵐ (Fin m → Y) := MeasurableEquiv.arrowCongr' Fin.revPerm ι
  have hV : MeasurePreserving eV (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => MeasurePreserving.id _)
  have hA : MeasurePreserving eA (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ => hι)
  have eVa : ∀ (V : Fin (m + 1) → X) (i : Fin (m + 1)), eV V i = V (Fin.rev i) := fun V i => rfl
  have eAa : ∀ (A : Fin m → Y) (i : Fin m), eA A i = ι (A (Fin.rev i)) := fun A i => rfl
  conv_rhs => rw [← hV.integral_comp']
  congr 1; funext V
  try dsimp only
  conv_rhs => rw [← hA.integral_comp']
  congr 1; funext A
  try dsimp only
  -- the integrand, pointwise
  have h0 : extX (eV V) 0 = extX V m := by
    rw [extX_zero, extX_last, eVa, Fin.rev_zero]
  have hm : extX (eV V) m = extX V 0 := by
    rw [extX_last, eVa, Fin.rev_last, extX_zero]
  have hGG : G' (extX (eV V)) (extY (eA A)) = G (extX V) (extY A) := by
    rw [hrev]
    refine hl _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
    · simp only [revX, extX, dif_pos (show m - i < m + 1 by omega), dif_pos (show i < m + 1 by omega),
        eVa]
      exact congrArg V (Fin.ext (by simp only [Fin.val_rev]; omega))
    · simp only [revY, extY, dif_pos (show m - 1 - i < m by omega), dif_pos hi, eAa, hinv]
      exact congrArg A (Fin.ext (by simp only [Fin.val_rev]; omega))
  have hP : pathW w (eV V) (eA A) = pathW w V A := by
    unfold pathW
    have : ∀ t : Fin m, w (eV V t.castSucc) (eA A t) (eV V t.succ)
        = w (V (Fin.rev t).castSucc) (A (Fin.rev t)) (V (Fin.rev t).succ) := by
      intro t
      rw [eVa, eVa, eAa, Fin.rev_castSucc, Fin.rev_succ, hsym, hinv]
    simp_rw [this]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun t => rfl)
  rw [h0, hm, hGG, hP]
  ring

end Bridge

#print axioms measurable_chain
#print axioms chain_split
#print axioms chain_end_iter
#print axioms bridge
#print axioms chain_rev

end MassGap.HiddenChain
