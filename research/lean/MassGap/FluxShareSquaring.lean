import Mathlib
import MassGap.CentreSectorSeed

/-!
# MassGap.FluxShareSquaring — the flux share is the mean twisted deficit, and doubling the time squares its odds

Let `a` be a bounded kernel on a probability space and `l` a list of commuting measure-preserving
involutions (`SectorDefect.Flips`). For a sublist `S` of `l`, `comp S` is the composite of its flips,
and `twist a (comp S)` is the trace of `a` with those flips inserted at one time slice.

**The trivial sector is the average of the twisted traces** (`hs_evL_eq`):

    hs(evL a l) = 2^{−|l|} Σ_{S ⊆ l} twist(a, comp S).

On the lattice (`fluxShare_eq_mean`) this reads, at step `i` of the corner path and side `n`,

    fluxShare β n i = 1 − (1/8) Σ_{S ⊆ flips} Z_S / Z,

with `Z = hs(halfK)` and `Z_S = twist(halfK, comp S)`: the share of the trace outside the trivial
electric-flux sector is the mean deficit of the eight twisted traces. `Z_S` is the trace with the
centre flips of `S` inserted at one time slice, i.e. the partition function whose time–space
plaquettes in the planes `(i, ν)`, `ν ∈ S`, carry the sign `−1` along one sheet ('t Hooft's twist).
Each ratio lies in `[0, 1]` (`twistRatio_nonneg`, `twistRatio_le_one`), and
* `one_sub_twistRatio_le`: every deficit `1 − Z_S/Z` is at most `8 · fluxShare`;
* `fluxShare_le_of_twistRatio`: if every `Z_S/Z ≥ 1 − δ`, then `fluxShare ≤ δ`.

So the flux part of `CentreSectorSeed.SectorSeedPow` (`FluxPart`) says that the twisted partition
functions come within a fixed small fraction of the untwisted one, equivalently that the electric-flux
sectors `Z_e`, `e ≠ 0` (their Fourier transforms), carry a small share of the trace.

**Doubling the time squares the flux odds** (`odds_conv_le`, lattice form `fluxShareDoubled_le`).
With `e = evL a l`,

    (hs(a∗a) − hs(e∗e)) / hs(a∗a) ≤ ((hs a − hs e)/hs e)² · exp(dd e).

`a ∗ a` is the transfer over twice the time extent, and `evL (a ∗ a) l = e ∗ e` (`evL_conv`), so the
left side is the flux share of the torus doubled along the transfer direction. The flux odds
`fluxShare/(1 − fluxShare)` square, at the cost of the trivial sector's own defect. The inequality
uses only positivity, symmetry and flip invariance of the kernel, so it holds for every lattice
theory with a positive transfer and a centre flip: U(1), Z₂, Georgi–Glashow and Banks–Zaks included.
It doubles a direction lying in every twisted plane. The steps of a cubic doubling that move a
direction transverse to a twisted plane are not of this form.

The fully even sector is at most each one-flip even sector (`hs_evL_le_ev`).

DERIVED (module-wide): `2` is the even/odd halving; `2` in `exp(dd)` is the square of the trace.
-/

noncomputable section

namespace MassGap.FluxShareSquaring

open MeasureTheory Filter MassGap.KernelPower MassGap.FluxSectorBound MassGap.SectorDefect

/-! ## 1. Sums over lists -/

section Lists

variable {β : Type*}

theorem sum_map_half_add (L : List β) (f g : β → ℝ) :
    (L.map (fun S => (f S + g S) / 2)).sum = ((L.map f).sum + (L.map g).sum) / 2 := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_div_const (L : List β) (f : β → ℝ) (A : ℝ) :
    (L.map (fun S => f S / A)).sum = (L.map f).sum / A := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_map_one_sub (L : List β) (f : β → ℝ) :
    (L.map (fun S => 1 - f S)).sum = L.length - (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

end Lists

/-! ## 2. Composites of flips -/

section Abstract

variable {X : Type*}

/-- The composite of a list of maps, the head applied first: `comp (σ :: S) = comp S ∘ σ`. -/
def comp : List (X → X) → X → X
  | [] => id
  | σ :: S => comp S ∘ σ

theorem comp_cons (σ : X → X) (S : List (X → X)) : comp (σ :: S) = comp S ∘ σ := rfl

theorem comm_comp (σ : X → X) : ∀ S : List (X → X), (∀ τ ∈ S, ∀ x, σ (τ x) = τ (σ x)) →
    ∀ x, σ (comp S x) = comp S (σ x)
  | [], _, _ => rfl
  | τ :: S, h, x => by
    show σ (comp S (τ x)) = comp S (τ (σ x))
    rw [comm_comp σ S (fun ρ hρ => h ρ (List.mem_cons_of_mem τ hρ)) (τ x), h τ List.mem_cons_self x]

variable [MeasurableSpace X] {μ : Measure X}

theorem measurable_comp : ∀ S : List (X → X), (∀ σ ∈ S, Measurable σ) → Measurable (comp S)
  | [], _ => measurable_id
  | σ :: S, h =>
    (measurable_comp S (fun τ hτ => h τ (List.mem_cons_of_mem σ hτ))).comp (h σ List.mem_cons_self)

theorem mp_comp : ∀ S : List (X → X), (∀ σ ∈ S, MeasurePreserving σ μ μ) →
    MeasurePreserving (comp S) μ μ
  | [], _ => MeasurePreserving.id μ
  | σ :: S, h =>
    (mp_comp S (fun τ hτ => h τ (List.mem_cons_of_mem σ hτ))).comp (h σ List.mem_cons_self)

/-! ## 3. Twisted traces of the even part -/

theorem twist_id (a : X → X → ℝ) : twist μ a id = hs μ a := by
  unfold twist hs
  congr 1; funext x; congr 1; funext y
  simp [sq]

theorem bdd_right {a : X → X → ℝ} {τ : X → X} (ha : Bdd a) (hτ : Measurable τ) :
    Bdd (fun x y => a x (τ y)) := by
  obtain ⟨C, hC⟩ := ha.bdd
  exact ⟨ha.meas.comp (measurable_fst.prodMk (hτ.comp measurable_snd)), C, fun x y => hC x (τ y)⟩

variable [IsProbabilityMeasure μ]

/-- **The twisted trace of the even part**: `twist(ev a σ, τ) = (twist(a, τ) + twist(a, σ ∘ τ))/2`,
for a flip `σ` commuting with a measurable `τ`. -/
theorem twist_ev {a : X → X → ℝ} {σ τ : X → X} (ha : Bdd a) (hf : Flip μ σ) (hτ : Measurable τ)
    (hc : ∀ x, σ (τ x) = τ (σ x)) :
    twist μ (ev a σ) τ = (twist μ a τ + twist μ a (σ ∘ τ)) / 2 := by
  have bσ : Bdd (fun x y => a x (σ y)) := bdd_right ha hf.meas
  have bτ : Bdd (fun x y => a x (τ y)) := bdd_right ha hτ
  have bστ : Bdd (fun x y => a x (σ (τ y))) := bdd_right ha (hf.meas.comp hτ)
  have hin : ∀ x, ∫ y, ev a σ x y * ev a σ x (τ y) ∂μ
      = ((∫ y, a x y * a x (τ y) ∂μ) + ∫ y, a x y * a x (σ (τ y)) ∂μ) / 2 := by
    intro x
    have i1 : Integrable (fun y => a x y * a x (τ y)) μ := bdd_rows ha bτ x x
    have i2 : Integrable (fun y => a x y * a x (σ (τ y))) μ := bdd_rows ha bστ x x
    have i3 : Integrable (fun y => a x (σ y) * a x (τ y)) μ := bdd_rows bσ bτ x x
    have i4 : Integrable (fun y => a x (σ y) * a x (σ (τ y))) μ := bdd_rows bσ bστ x x
    have i12 : Integrable (fun y => a x y * a x (τ y) + a x y * a x (σ (τ y))) μ := i1.add i2
    have i123 : Integrable (fun y => a x y * a x (τ y) + a x y * a x (σ (τ y))
        + a x (σ y) * a x (τ y)) μ := i12.add i3
    have e3 : ∫ y, a x (σ y) * a x (τ y) ∂μ = ∫ y, a x y * a x (σ (τ y)) ∂μ := by
      have h : ∫ y, a x (σ y) * a x (σ (τ (σ y))) ∂μ = ∫ y, a x y * a x (σ (τ y)) ∂μ :=
        hf.integral_comp (fun y => a x y * a x (σ (τ y)))
      rw [← h]
      congr 1; funext y
      rw [hc (σ y), hf.invol]
    have e4 : ∫ y, a x (σ y) * a x (σ (τ y)) ∂μ = ∫ y, a x y * a x (τ y) ∂μ := by
      have h : ∫ y, a x (σ y) * a x (τ (σ y)) ∂μ = ∫ y, a x y * a x (τ y) ∂μ :=
        hf.integral_comp (fun y => a x y * a x (τ y))
      rw [← h]
      congr 1; funext y
      rw [hc y]
    have e0 : (fun y => ev a σ x y * ev a σ x (τ y))
        = fun y => (a x y * a x (τ y) + a x y * a x (σ (τ y)) + a x (σ y) * a x (τ y)
            + a x (σ y) * a x (σ (τ y))) / 4 := by
      funext y; simp only [ev]; ring
    rw [e0, integral_div, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, e3, e4]
    ring
  unfold twist
  simp_rw [hin]
  rw [integral_div, integral_add (int_row (bdd_mul ha bτ)) (int_row (bdd_mul ha bστ))]
  rfl

/-- **The twisted traces of the fully even part are averages**:
`twist(evL a l, τ) = 2^{−|l|} Σ_{S ⊆ l} twist(a, comp S ∘ τ)`. -/
theorem twist_evL : ∀ (l : List (X → X)) (a : X → X → ℝ) (τ : X → X), Flips μ l → Bdd a →
    Measurable τ → (∀ σ ∈ l, ∀ x, σ (τ x) = τ (σ x)) →
    twist μ (evL a l) τ = (l.sublists'.map (fun S => twist μ a (comp S ∘ τ))).sum / 2 ^ l.length
  | [], a, τ, _, _, _, _ => by simp [evL, comp]
  | σ :: l, a, τ, hl, ha, hτ, hc => by
    have hf : Flip μ σ := hl.1 σ List.mem_cons_self
    have hl' : Flips μ l := hl.tail
    have hc' : ∀ ρ ∈ l, ∀ x, ρ (τ x) = τ (ρ x) := fun ρ hρ => hc ρ (List.mem_cons_of_mem σ hρ)
    have ih := twist_evL l (ev a σ) τ hl' (bdd_ev ha hf) hτ hc'
    rw [evL_cons, ih]
    have hterm : ∀ S ∈ l.sublists', twist μ (ev a σ) (comp S ∘ τ)
        = (twist μ a (comp S ∘ τ) + twist μ a (comp (σ :: S) ∘ τ)) / 2 := by
      intro S hS
      have hSl : ∀ ρ ∈ S, ρ ∈ l := fun ρ hρ => (List.mem_sublists'.mp hS).subset hρ
      have hσS : ∀ ρ ∈ S, ∀ x, σ (ρ x) = ρ (σ x) := fun ρ hρ =>
        hl.2 σ List.mem_cons_self ρ (List.mem_cons_of_mem σ (hSl ρ hρ))
      have hmeas : Measurable (comp S ∘ τ) :=
        (measurable_comp S (fun ρ hρ => (hl'.1 ρ (hSl ρ hρ)).meas)).comp hτ
      have hcomm : ∀ x, σ ((comp S ∘ τ) x) = (comp S ∘ τ) (σ x) := by
        intro x
        show σ (comp S (τ x)) = comp S (τ (σ x))
        rw [comm_comp σ S hσS (τ x), hc σ List.mem_cons_self x]
      have hfun : σ ∘ (comp S ∘ τ) = comp (σ :: S) ∘ τ := by
        funext x
        show σ (comp S (τ x)) = comp S (σ (τ x))
        exact comm_comp σ S hσS (τ x)
      rw [twist_ev ha hf hmeas hcomm, hfun]
    rw [List.map_congr_left hterm,
      sum_map_half_add _ (fun S => twist μ a (comp S ∘ τ)) (fun S => twist μ a (comp (σ :: S) ∘ τ)),
      List.sublists'_cons, List.map_append, List.sum_append, List.map_map, List.length_cons,
      pow_succ]
    have e : ((fun S => twist μ a (comp S ∘ τ)) ∘ List.cons σ)
        = fun S => twist μ a (comp (σ :: S) ∘ τ) := rfl
    rw [e]
    ring

/-- **The trivial sector's trace is the average of the twisted traces.** -/
theorem hs_evL_eq (l : List (X → X)) (a : X → X → ℝ) (hl : Flips μ l) (ha : Bdd a) :
    hs μ (evL a l) = (l.sublists'.map (fun S => twist μ a (comp S))).sum / 2 ^ l.length := by
  have h := twist_evL l a id hl ha measurable_id (fun _ _ _ => rfl)
  rw [twist_id] at h
  simpa using h

/-- A twisted trace is at most the trace. -/
theorem twist_le_hs {a : X → X → ℝ} {τ : X → X} (ha : Bdd a) (hτ : MeasurePreserving τ μ μ) :
    twist μ a τ ≤ hs μ a := by
  have bτ : Bdd (fun x y => a x (τ y)) := bdd_right ha hτ.measurable
  have bsq : Bdd (fun x y => a x y ^ 2) := bdd_sq ha
  have bτsq : Bdd (fun x y => a x (τ y) ^ 2) := bdd_sq bτ
  have hin : ∀ x, ∫ y, a x y * a x (τ y) ∂μ ≤ ∫ y, a x y ^ 2 ∂μ := by
    intro x
    have i1 : Integrable (fun y => a x y * a x (τ y)) μ := bdd_rows ha bτ x x
    have i2 : Integrable (fun y => a x y ^ 2) μ := irow bsq x
    have i3 : Integrable (fun y => a x (τ y) ^ 2) μ := irow bτsq x
    have i23 : Integrable (fun y => (a x y ^ 2 + a x (τ y) ^ 2) / 2) μ := (i2.add i3).div_const 2
    have h1 : ∫ y, a x y * a x (τ y) ∂μ ≤ ∫ y, (a x y ^ 2 + a x (τ y) ^ 2) / 2 ∂μ :=
      integral_mono i1 i23 (fun y => by nlinarith [sq_nonneg (a x y - a x (τ y))])
    have h2 : ∫ y, a x (τ y) ^ 2 ∂μ = ∫ y, a x y ^ 2 ∂μ := by
      have hm : AEStronglyMeasurable (fun y => a x y ^ 2) (Measure.map τ μ) := by
        rw [hτ.map_eq]; exact ((bsq.row x)).aestronglyMeasurable
      rw [← integral_map hτ.measurable.aemeasurable hm, hτ.map_eq]
    rw [integral_div, integral_add i2 i3, h2] at h1
    linarith
  unfold twist hs
  exact integral_mono (int_row (bdd_mul ha bτ)) (int_row bsq) hin

/-! ## 4. Doubling the time -/

theorem int_prod {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {C : ℝ}
    (hfC : ∀ y, |f y| ≤ C) (hgC : ∀ y, |g y| ≤ C) : Integrable (fun y => f y * g y) μ :=
  integrable_of_bdd (hf.mul hg) (C := C * C) (fun y => by
    rw [abs_mul]; exact mul_le_mul (hfC y) (hgC y) (abs_nonneg _) ((abs_nonneg _).trans (hfC y)))

/-- **The even part of the doubled kernel is the doubled even part.** -/
theorem ev_conv {a : X → X → ℝ} {σ : X → X} (ha : Bdd a) (hf : Flip μ σ)
    (hinv : ∀ x y, a (σ x) (σ y) = a x y) :
    ev (conv μ a a) σ = conv μ (ev a σ) (ev a σ) := by
  obtain ⟨C, hC⟩ := ha.bdd
  funext x z
  have mxa : Measurable (fun y => a x y) := ha.row x
  have mxs : Measurable (fun y => a x (σ y)) := (ha.row x).comp hf.meas
  have mz : Measurable (fun y => a y z) := ha.col z
  have mzs : Measurable (fun y => a y (σ z)) := ha.col (σ z)
  have i1 : Integrable (fun y => a x y * a y z) μ := int_prod mxa mz (fun y => hC x y) (fun y => hC y z)
  have i2 : Integrable (fun y => a x y * a y (σ z)) μ :=
    int_prod mxa mzs (fun y => hC x y) (fun y => hC y (σ z))
  have i3 : Integrable (fun y => a x (σ y) * a y z) μ :=
    int_prod mxs mz (fun y => hC x (σ y)) (fun y => hC y z)
  have i4 : Integrable (fun y => a x (σ y) * a y (σ z)) μ :=
    int_prod mxs mzs (fun y => hC x (σ y)) (fun y => hC y (σ z))
  have i12 : Integrable (fun y => a x y * a y z + a x y * a y (σ z)) μ := i1.add i2
  have i123 : Integrable (fun y => a x y * a y z + a x y * a y (σ z) + a x (σ y) * a y z) μ :=
    i12.add i3
  have e3 : ∫ y, a x (σ y) * a y z ∂μ = ∫ y, a x y * a y (σ z) ∂μ := by
    have h : ∫ y, a x (σ y) * a (σ (σ y)) z ∂μ = ∫ y, a x y * a (σ y) z ∂μ :=
      hf.integral_comp (fun y => a x y * a (σ y) z)
    calc ∫ y, a x (σ y) * a y z ∂μ = ∫ y, a x (σ y) * a (σ (σ y)) z ∂μ := by
          congr 1; funext y; rw [hf.invol]
      _ = ∫ y, a x y * a (σ y) z ∂μ := h
      _ = ∫ y, a x y * a y (σ z) ∂μ := by
          congr 1; funext y; rw [a_flip_left hf hinv y z]
  have e4 : ∫ y, a x (σ y) * a y (σ z) ∂μ = ∫ y, a x y * a y z ∂μ := by
    have h : ∫ y, a x (σ y) * a (σ y) z ∂μ = ∫ y, a x y * a y z ∂μ :=
      hf.integral_comp (fun y => a x y * a y z)
    rw [← h]
    congr 1; funext y
    rw [a_flip_left hf hinv y z]
  have e0 : (fun y => ev a σ x y * ev a σ y z)
      = fun y => (a x y * a y z + a x y * a y (σ z) + a x (σ y) * a y z
          + a x (σ y) * a y (σ z)) / 4 := by
    funext y; simp only [ev]; ring
  show (conv μ a a x z + conv μ a a x (σ z)) / 2 = ∫ y, ev a σ x y * ev a σ y z ∂μ
  rw [e0, integral_div, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, e3, e4]
  unfold conv
  ring

theorem evL_conv {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l → Adm l c a →
    evL (conv μ a a) l = conv μ (evL a l) (evL a l)
  | [], _, _, _ => rfl
  | σ :: l, a, hl, ha => by
    rw [evL_cons, ev_conv ha.bdd (hl.1 σ List.mem_cons_self) (ha.inv σ List.mem_cons_self), evL_cons]
    exact evL_conv l (ev a σ) hl.tail (Adm.ev hl ha)

theorem hs_conv_evL_le {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ), Flips μ l → Adm l c a →
    hs μ (conv μ (evL a l) (evL a l)) ≤ hs μ (conv μ a a)
  | [], _, _, _ => le_rfl
  | σ :: l, a, hl, ha => by
    have hf := hl.1 σ List.mem_cons_self
    have h1 := hs_conv_evL_le l (ev a σ) hl.tail (Adm.ev hl ha)
    have hsplit := hs_conv_split ha.bdd ha.symm hf (ha.inv σ List.mem_cons_self)
    rw [evL_cons]
    linarith [hs_nonneg (μ := μ) (conv μ (od a σ) (od a σ))]

/-- The real-number step of `odds_conv_le`. -/
theorem odds_step {A B A2 E2 d : ℝ} (hB : 0 < B) (hE2 : 0 < E2) (hEA : E2 ≤ A2)
    (h1 : A2 - E2 ≤ (A - B) ^ 2) (hd : d = 2 * Real.log B - Real.log E2) :
    (A2 - E2) / A2 ≤ ((A - B) / B) ^ 2 * Real.exp d := by
  have hA2 : 0 < A2 := lt_of_lt_of_le hE2 hEA
  have hexp : Real.exp d = B ^ 2 / E2 := by
    rw [hd, Real.exp_sub, Real.exp_log hE2,
      show (2 : ℝ) * Real.log B = Real.log (B ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (pow_pos hB 2)]
  have hR : ((A - B) / B) ^ 2 * (B ^ 2 / E2) = (A - B) ^ 2 / E2 := by
    rw [div_pow, div_mul_div_comm, mul_comm ((A - B) ^ 2) (B ^ 2),
      mul_div_mul_left _ _ (pow_pos hB 2).ne']
  rw [hexp, hR]
  exact (div_le_div_of_nonneg_right h1 hA2.le).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) hE2 hEA)

omit [MeasurableSpace X] in
/-- Two even parts commute. -/
theorem ev_ev_comm {a : X → X → ℝ} {σ τ : X → X} (hc : ∀ x, σ (τ x) = τ (σ x)) :
    ev (ev a σ) τ = ev (ev a τ) σ := by
  funext x y
  simp only [ev]
  rw [hc y]
  ring

/-- **The fully even sector carries at most the trace of each one-flip even sector.** -/
theorem hs_evL_le_ev {c : ℝ} : ∀ (l : List (X → X)) (a : X → X → ℝ) (σ : X → X), Flips μ l →
    Adm l c a → σ ∈ l → hs μ (evL a l) ≤ hs μ (ev a σ)
  | [], _, _, _, _, h => by simp at h
  | τ :: l, a, σ, hl, ha, hσ => by
    rcases List.mem_cons.mp hσ with rfl | hσ'
    · rw [evL_cons]
      exact hs_evL_le l (ev a _) hl.tail (Adm.ev hl ha)
    · rw [evL_cons]
      have ih := hs_evL_le_ev l (ev a τ) σ hl.tail (Adm.ev hl ha) hσ'
      have hcomm : ∀ x, σ (τ x) = τ (σ x) :=
        hl.2 σ (List.mem_cons_of_mem τ hσ') τ List.mem_cons_self
      rw [← ev_ev_comm hcomm] at ih
      have hfτ : Flip μ τ := hl.1 τ List.mem_cons_self
      have hfσ : Flip μ σ := hl.1 σ (List.mem_cons_of_mem τ hσ')
      exact ih.trans (hs_ev_le (bdd_ev ha.bdd hfσ) hfτ)

/-- **Doubling the time squares the flux odds**, at the cost of the trivial sector's defect. -/
theorem odds_conv_le {c : ℝ} (hc : 0 < c) (l : List (X → X)) (a : X → X → ℝ) (hl : Flips μ l)
    (ha : Adm l c a) :
    (hs μ (conv μ a a) - hs μ (conv μ (evL a l) (evL a l))) / hs μ (conv μ a a)
      ≤ ((hs μ a - hs μ (evL a l)) / hs μ (evL a l)) ^ 2 * Real.exp (dd μ (evL a l)) := by
  have he := adm_evL l a hl ha
  have hB : 0 < hs μ (evL a l) := CentreSectorSeed.hs_pos_of_adm hc he
  have hE2 : 0 < hs μ (conv μ (evL a l) (evL a l)) := CentreSectorSeed.hs_conv_pos_of_adm hc he
  have h1 : hs μ (conv μ a a) - hs μ (conv μ (evL a l) (evL a l))
      ≤ (hs μ a - hs μ (evL a l)) ^ 2 := by
    have := hs_conv_le_evL l a hl ha
    linarith
  exact odds_step hB hE2 (hs_conv_evL_le l a hl ha) h1 rfl

end Abstract

/-! ## 5. The lattice: the flux share of a step of the corner path -/

section Lattice

open MassGap.CentreSectorSeed MassGap.RectWilson MassGap.RectTransfer

/-- **The twisted ratio** `Z_S/Z` at step `i`, side `n`: the trace with the centre flips of `S`
inserted, over the trace. -/
def twistRatio (β : ℝ) (n : ℕ) (i : Fin 4) (S : List (Cfg i (Tr n i) → Cfg i (Tr n i))) : ℝ :=
  twist (hSi n i) (halfK β n i) (comp S) / hs (hSi n i) (halfK β n i)

theorem flips_mp {i : Fin 4} {n : ℕ} :
    ∀ σ ∈ flips i (Tr n i), MeasurePreserving σ (hSi n i) (hSi n i) :=
  fun σ hσ => (flips_spec.1 σ hσ).mp

theorem mp_comp_sub {i : Fin 4} {n : ℕ} {S : List (Cfg i (Tr n i) → Cfg i (Tr n i))}
    (hS : S ∈ (flips i (Tr n i)).sublists') : MeasurePreserving (comp S) (hSi n i) (hSi n i) :=
  mp_comp S (fun σ hσ => flips_mp σ ((List.mem_sublists'.mp hS).subset hσ))

theorem hs_halfK_pos {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    0 < hs (hSi n i) (halfK β n i) :=
  hs_pos_of_adm (CentreSectorSeed.floor_pos β n i) (adm_halfK hβ n i)

/-- **The flux share is one minus the mean twisted ratio.** -/
theorem fluxShare_eq_mean {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    fluxShare β n i = 1 - ((flips i (Tr n i)).sublists'.map (twistRatio β n i)).sum / 8 := by
  have hA := hs_halfK_pos hβ n i
  have hB := hs_evL_eq (flips i (Tr n i)) (halfK β n i) flips_spec (adm_halfK hβ n i).bdd
  rw [flips_length] at hB
  have hR : ((flips i (Tr n i)).sublists'.map (twistRatio β n i)).sum
      = ((flips i (Tr n i)).sublists'.map
          (fun S => twist (hSi n i) (halfK β n i) (comp S))).sum / hs (hSi n i) (halfK β n i) :=
    sum_map_div_const _ (fun S => twist (hSi n i) (halfK β n i) (comp S)) _
  unfold fluxShare trivK
  rw [hB, hR, sub_div, div_self hA.ne']
  ring

theorem twistRatio_le_one {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    {S : List (Cfg i (Tr n i) → Cfg i (Tr n i))} (hS : S ∈ (flips i (Tr n i)).sublists') :
    twistRatio β n i S ≤ 1 := by
  unfold twistRatio
  rw [div_le_one (hs_halfK_pos hβ n i)]
  exact twist_le_hs (adm_halfK hβ n i).bdd (mp_comp_sub hS)

theorem twistRatio_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    (S : List (Cfg i (Tr n i) → Cfg i (Tr n i))) : 0 ≤ twistRatio β n i S := by
  unfold twistRatio
  refine div_nonneg ?_ (hs_halfK_pos hβ n i).le
  have hlow := (adm_halfK hβ n i).low
  have hc := (CentreSectorSeed.floor_pos β n i).le
  exact integral_nonneg fun x => integral_nonneg fun y =>
    mul_nonneg (hc.trans (hlow _ _)) (hc.trans (hlow _ _))

theorem length_sublists_flips (n : ℕ) (i : Fin 4) :
    (((flips i (Tr n i)).sublists'.length : ℕ) : ℝ) = 8 := by
  rw [List.length_sublists', flips_length]; norm_num

/-- The eight twisted deficits sum to eight times the flux share. -/
theorem sum_deficits {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    ((flips i (Tr n i)).sublists'.map (fun S => 1 - twistRatio β n i S)).sum
      = 8 * fluxShare β n i := by
  rw [sum_map_one_sub _ (twistRatio β n i), length_sublists_flips, fluxShare_eq_mean hβ]
  ring

/-- **Every twisted deficit is at most eight times the flux share.** -/
theorem one_sub_twistRatio_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    {S : List (Cfg i (Tr n i) → Cfg i (Tr n i))} (hS : S ∈ (flips i (Tr n i)).sublists') :
    1 - twistRatio β n i S ≤ 8 * fluxShare β n i := by
  have hmem : 1 - twistRatio β n i S
      ∈ (flips i (Tr n i)).sublists'.map (fun S => 1 - twistRatio β n i S) :=
    List.mem_map_of_mem hS
  have hnn : ∀ x ∈ (flips i (Tr n i)).sublists'.map (fun S => 1 - twistRatio β n i S), 0 ≤ x := by
    intro x hx
    obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hx
    linarith [twistRatio_le_one hβ n i hS']
  rw [← sum_deficits hβ n i]
  exact List.single_le_sum hnn _ hmem

/-- **Twisted ratios near one give a small flux share.** -/
theorem fluxShare_le_of_twistRatio {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) {δ : ℝ}
    (h : ∀ S ∈ (flips i (Tr n i)).sublists', 1 - δ ≤ twistRatio β n i S) :
    fluxShare β n i ≤ δ := by
  have hle : ((flips i (Tr n i)).sublists'.map (fun S => 1 - twistRatio β n i S)).sum
      ≤ ((flips i (Tr n i)).sublists'.map (fun _ => δ)).sum :=
    List.sum_le_sum (fun S hS => by linarith [h S hS])
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul, length_sublists_flips,
    sum_deficits hβ n i] at hle
  linarith

/-- The flux share of the torus doubled along the transfer direction `i`. -/
def fluxShareDoubled (β : ℝ) (n : ℕ) (i : Fin 4) : ℝ :=
  (hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
    - hs (hSi n i) (evL (conv (hSi n i) (halfK β n i) (halfK β n i)) (flips i (Tr n i))))
    / hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))

/-- **Doubling the time squares the flux odds on the lattice**:
`fluxShareDoubled ≤ (fluxShare/(1 − fluxShare))² · exp(trivialDefect)`. -/
theorem fluxShareDoubled_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    fluxShareDoubled β n i
      ≤ (fluxShare β n i / (1 - fluxShare β n i)) ^ 2 * Real.exp (trivialDefect β n i) := by
  have hadm := adm_halfK hβ n i
  have h := odds_conv_le (CentreSectorSeed.floor_pos β n i) (flips i (Tr n i)) (halfK β n i)
    flips_spec hadm
  have hA := hs_halfK_pos hβ n i
  have hodds : fluxShare β n i / (1 - fluxShare β n i)
      = (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) / hs (hSi n i) (trivK β n i) := by
    unfold fluxShare
    have e : 1 - (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i))
        / hs (hSi n i) (halfK β n i) = hs (hSi n i) (trivK β n i) / hs (hSi n i) (halfK β n i) := by
      rw [sub_div, div_self hA.ne']; ring
    rw [e, div_div_div_cancel_right₀ hA.ne']
  unfold fluxShareDoubled
  rw [evL_conv (flips i (Tr n i)) (halfK β n i) flips_spec hadm, hodds]
  exact h

/-! ## 6. On a fixed torus the weak-coupling end forces the flux share up -/

/-- A twisted-trace bound on the torus `TwistedTraceBound.Tn m` (the hypothesis `h`, stated with
`TwistedTraceBound.flip`), moved to the slice of step `0` with `centreFlip`. -/
theorem twist_transport {m : ℕ} {T : {j : Fin 4 // j ≠ 0} → ℕ} (hT : T = TwistedTraceBound.Tn m)
    (β : ℝ) (k : ℕ)
    (h : twist (hS 0 (TwistedTraceBound.Tn m) 2)
          (iter (hS 0 (TwistedTraceBound.Tn m) 2) (kT 0 (TwistedTraceBound.Tn m) 2 β) k)
          (TwistedTraceBound.flip TwistedTraceBound.d1)
        + twist (hS 0 (TwistedTraceBound.Tn m) 2)
          (iter (hS 0 (TwistedTraceBound.Tn m) 2) (kT 0 (TwistedTraceBound.Tn m) 2 β) k)
          (TwistedTraceBound.flip TwistedTraceBound.d2)
        ≤ 3 / 2 * hs (hS 0 (TwistedTraceBound.Tn m) 2)
          (iter (hS 0 (TwistedTraceBound.Tn m) 2) (kT 0 (TwistedTraceBound.Tn m) 2 β) k)) :
    twist (hS 0 T 2) (iter (hS 0 T 2) (kT 0 T 2 β) k) (centreFlip TwistedTraceBound.d1)
        + twist (hS 0 T 2) (iter (hS 0 T 2) (kT 0 T 2 β) k) (centreFlip TwistedTraceBound.d2)
      ≤ 3 / 2 * hs (hS 0 T 2) (iter (hS 0 T 2) (kT 0 T 2 β) k) := by
  subst hT
  exact h

/-! ## 7. The flux part -/

/-- **The flux part of the sector seed**: eventually in `β`, some power-of-two side has flux share at
most `1/80000` at every step of the corner path.

DERIVED: Inherited: `1/80000` the sector bound of `CentreSectorSeed`, chosen so that `15 · 5/80000 ≤ 1/1000`. -/
def FluxPart : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ ∀ i : Fin 4, fluxShare β (2 ^ b) i ≤ 1 / 80000

/-- **The flux part as twisted partition functions**: eventually in `β`, some power-of-two side has
every twisted ratio `Z_S/Z` at least `1 − δ` at every step of the corner path. -/
def TwistPart (δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ ∀ i : Fin 4,
    ∀ S ∈ (flips i (Tr (2 ^ b) i)).sublists', 1 - δ ≤ twistRatio β (2 ^ b) i S

theorem fluxPart_of_sectorSeedPow (h : SectorSeedPow) : FluxPart := by
  filter_upwards [h] with β ⟨b, hb, hs⟩
  exact ⟨b, hb, fun i => (hs i).1⟩

theorem fluxPart_of_twistPart (h : TwistPart (1 / 80000)) : FluxPart := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hs⟩ hβ
  exact ⟨b, hb, fun i => fluxShare_le_of_twistRatio hβ _ i (hs i)⟩

theorem twistPart_of_fluxPart (h : FluxPart) : TwistPart (1 / 10000) := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hs⟩ hβ
  refine ⟨b, hb, fun i S hS => ?_⟩
  have := one_sub_twistRatio_le hβ (2 ^ b) i hS
  linarith [hs i]

end Lattice

end MassGap.FluxShareSquaring

end

#print axioms MassGap.FluxShareSquaring.twist_evL
#print axioms MassGap.FluxShareSquaring.hs_evL_eq
#print axioms MassGap.FluxShareSquaring.evL_conv
#print axioms MassGap.FluxShareSquaring.odds_conv_le
#print axioms MassGap.FluxShareSquaring.fluxShare_eq_mean
#print axioms MassGap.FluxShareSquaring.one_sub_twistRatio_le
#print axioms MassGap.FluxShareSquaring.fluxShare_le_of_twistRatio
#print axioms MassGap.FluxShareSquaring.fluxShareDoubled_le
#print axioms MassGap.FluxShareSquaring.fluxPart_of_twistPart
#print axioms MassGap.FluxShareSquaring.twistPart_of_fluxPart
