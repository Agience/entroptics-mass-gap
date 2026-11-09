import Mathlib
import MassGap.StallRigid
import MassGap.ZoomContract

/-!
# MassGap.DefectBound — the bound on the doubling defect along the windows: two exact reductions and the surface bound

`D(w)` is the doubling defect at side `2^w` (`StallRigid.Dw`), for the Wilson measure of every compact group
(`GaugeGroup G`). `StallRigid.vanishes_iff_read`: `D → 0` exactly when `D` is bounded along the windows and the window
read `Y → 0`. This module is about the first clause, (H): `∃ A, D(w) ≤ A` eventually. Declarations are in the namespace
`MassGap.DefectBound`.

Notation. Step `i` of window `w` is the slice transfer `K_i` of the slice `sliceT (2^w) i`, `λ₀ = ‖K_i‖`, and
`stepD G β w i = p_i(uP i + e_i)` its doubling defect at time `2^{w+1}`. The weighted level count of the step is
`levCount G hβ w i = Tr K_i^{2^{w+1}} / λ₀^{2^{w+1}} − 1 = Σ_{k≠0} (λ_k/λ₀)^{2^{w+1}}`, read with `traceSeq` and the
operator norm, with no eigenvalue list.

## 1. The level-count reduction (proved, every `G`, every `β ≥ 0`)

* `path_eq`, `Dw_succ_eq`: `D(w+1) = 8 P₀ + 4 P₁ + 2 P₂ + P₃`, `P_i = stepD G β w i`, an identity of the corner path
  `(1,1,1,1) → (2,2,2,2)`.
* `step_sandwich`: `0 ≤ n_i`, `log(1 + n_i) ≤ P_i ≤ 2 log(1 + n_i)`, `n_i = levCount G hβ w i`. The lower side is purity
  (`DoublingPower.excited_le`), the upper side is `Tr K^{2m} ≥ λ₀^{2m}`.
* `count_sandwich`: `log(1 + n_i(w)) ≤ D(w+1) ≤ 2 (8 log(1+n₀) + 4 log(1+n₁) + 2 log(1+n₂) + log(1+n₃))`.
* `bounded_iff_count`: (H) holds exactly when the weighted count of transfer levels at the window time is bounded on
  the four step slices: `(∃ A, ∀ᶠ w, D(w) ≤ A) ↔ (∃ B, ∀ᶠ w, ∀ i, n_i(w) ≤ B)`. `bounded_iff_count_SU` at `SU(N)`.

## 2. The free-energy reduction (proved, `SU(N)`)

`f_w = log Z(2^w) / 16^w` (`ZoomContract.freeSite`), `f_∞` its limit (`ZoomContract.zoomLimit`).

* `freeEnergy_partial`, `freeEnergy_rate`: `D(u) ≤ A` for all `u ≥ w` gives `16^w (f_w − f_∞) ≤ max(A, 0)/15`.
* `bounded_iff_freeEnergy`: (H) holds exactly when `log Z(2^w) = 16^w f_∞ + O(1)` along the windows: the finite-size
  correction to the torus free energy, in total and not per site, is bounded. `ZoomContract` gives `f_w − f_∞ → 0`;
  (H) asks for the rate `O(16^{−w})`.
* `log_term`, `log_term_unbounded`: a term `a w` in `log Z(2^w)` (a power of the volume in `Z`, `a = c log 2` for
  `Z ∝ L^c`) enters `D` as `15 a w − a + 15 b`; for `a > 0`, `D` is unbounded. So (H) is the absence of every such term.

## 3. The surface bound (proved, every `G`, every `β ≥ 0`, unconditional)

* `norm_trace_le`: the normalized trace descends under doubling, `Tr K^{2·2^n}/λ₀^{2·2^n} ≤ hs(K)/λ₀²`
  (`PowerFacts.dbl_le`, iterated).
* `top_ge_min`: a kernel `k ≥ a` with a positive top eigenfunction has top value `c ≥ a` (integrate the eigen equation).
* `hs_le_one`: `hs(k) ≤ 1` for `|k| ≤ 1` on a probability space.
* `defect_le_min`: so `1 + n ≤ 1/a²` and the step defect is at most `−4 log a`.
* `stepD_le_surface`, `neg_log_kTmin`, `surface_bound`: `P_i ≤ 4 β (spMax_i + 2 tpMax_i)`, and
  `D(w+1) ≤ 4 β Σ c_i (spMax_i + 2 tpMax_i)`, where `spMax`, `tpMax` are `RectTransfer`'s plaquette counts of the step
  slice. The slice is three-dimensional with sides of order `2^w`, so this is `D = O(β 8^w)`: the surface order. The
  per-volume read `D/16^w` is `O(β 2^{−w})`, which is a rate for `ZoomContract.tendsto_perVolume`.

## 4. Tests (proved)

`count_tests`, `surface_tests`: both reductions and the surface bound hold at `U(1)` (`StallRigid.instGaugeGroupCircle`),
`A₅`, `G₂` by the same proof. They exclude nothing by themselves.

## The routes (argued)

(a) Chessboard / Hölder in the transverse directions. Every reflection-positivity inequality bounds `log Z(2L)` above by
`16 log Z(L)`; that is `D ≥ 0` (`p ≥ 0`). (H) is the reverse, a lower bound on `Z(2L)` by `Z(L)^16`, a decoupling
statement. The reverse that positivity and compactness give is the cut at the slice: `surface_bound`. No recursion of the
`p_μ` closes at a bounded fixed point without a lower bound on `Z(2L)/Z(L)^16` better than the surface cost.

(b) Free energy. `bounded_iff_freeEnergy` is the exact form: the monotone convergence of `f_w` is the per-volume read
and gives no rate; (H) is the rate `O(16^{−w})`. Subadditivity in the transverse directions gives the surface rate
`O(2^{−w})` and no better.

(c) Groups. (H) is not a theorem about reflection-positive lattice systems in general: a massless field with a compact
zero mode puts `a log L`, `a ≠ 0`, into `log Z`, and `log_term_unbounded` then gives `D → ∞`. The Gaussian photon in
`d` dimensions has `log L` coefficient of `D` equal to `(2^d − 1)(d − 1)(d − 4)/2` (`PhotonStall`, with the `det′`
asymptotics cited): zero at `d = 4`, so the four-dimensional `U(1)` photon model has `D` bounded in `w` at fixed `β`
(value `45/2 log β + const`, cited, `PhotonStall`), and `D` grows like `w` in the five-dimensional Coulomb phase. A spin model with a broken
continuous global symmetry in `d = 4` (Goldstone, `O(2)` at low temperature, argued from spin-wave counting) has
`a = (d − 2)/2 > 0`. `A₅` (finite group, cited stall) has `D` bounded by the count of vacua. So (H) for every compact
`G` in `d = 4` is expected and holds in every model in the tree, and a proof of it has to use `d = 4`: the cancellation
of the zero-mode volume against the `det′` count. No input used here (positivity, compactness, PF, the cut) sees the
dimension except through the surface count.

DERIVED (module-wide): `8, 4, 2, 1` the corner-path weights, `15 = 16 − 1` their sum and the copies less the doubled
torus; `30 = 2 · 15`; `2` the square in the purity and the doubling; `4 = 2 · 2` the purity square times the `λ₀²` of
`hs(K)/λ₀²`; `16 = 2⁴` the copies; `1` the least window and the bound `|k| ≤ 1`; `0` signs and limits. Inherited:
`spMax`, `tpMax`, `kTmin` of `RectTransfer`. No CHOSEN constants.

## What does not follow

(H) is not proved at any `β > 0` for any `G`. The surface bound `O(β 8^w)` is the strongest unconditional bound here;
`O(w)` and `O(1)` are not reached. The two reductions are exact restatements of (H): a bounded weighted level count at
the window time, and a bounded total finite-size correction `log Z(2^w) − 16^w f_∞`; neither is discharged. The
identification of the surface order with `8^w` reads the plaquette counts `spMax`, `tpMax` of the step slices and is not
stated as a separate theorem. The statements about `d = 5`, the Goldstone phase and `A₅` in §(c) are argued or cited,
not proved: the Gaussian models are not the Wilson measures. `Y → 0` is untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.DefectBound

open MeasureTheory Filter Topology MassGap.KernelPower MassGap.SlabKernelOperator

/-! ## 0. The purity sandwich for one trace sequence -/

section Facts

open MassGap.DoublingPower

variable {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}

/-- **The defect is at least `log(1 + e)`.** DERIVED: `1` the top. -/
theorem log_one_add_le_defect (h : PowerFacts a lam s m) : Real.log (1 + s) ≤ defect a m := by
  have h1 := excited_le h
  have hs := h.s_nonneg
  have h2 : 1 + s ≤ Real.exp (defect a m) := by linarith
  have h3 := Real.log_le_log (by linarith) h2
  rwa [Real.log_exp] at h3

/-- **The defect is at most `2 log(1 + e)`.** DERIVED: `2` the square in the purity. -/
theorem defect_le_two_log_one_add (h : PowerFacts a lam s m) : defect a m ≤ 2 * Real.log (1 + s) := by
  have hl := h.lam_pow_pos (2 * m)
  have hl1 := h.lam_pow_pos m
  have h1s : 0 < 1 + s := by linarith [h.s_nonneg]
  have hge := h.dbl_ge
  have hlog := Real.log_le_log hl hge
  have e2 : lam ^ (2 * m) = (lam ^ m) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [e2, Real.log_pow] at hlog
  unfold DoublingPower.defect
  rw [h.base, Real.log_mul hl1.ne' h1s.ne']
  push_cast at hlog
  linarith

/-- **The normalized trace descends under doubling.** DERIVED: `2` the doubling. -/
theorem norm_trace_succ (h : PowerFacts a lam s m) :
    a (2 * m) / lam ^ (2 * m) ≤ a m / lam ^ m := by
  have hl := h.lam_pow_pos m
  have hl2 := h.lam_pow_pos (2 * m)
  rw [div_le_div_iff₀ hl2 hl]
  have e : lam ^ (2 * m) = lam ^ m * lam ^ m := by rw [two_mul, pow_add]
  rw [e]
  calc a (2 * m) * lam ^ m ≤ (lam ^ m * a m) * lam ^ m := mul_le_mul_of_nonneg_right h.dbl_le hl.le
    _ = a m * (lam ^ m * lam ^ m) := by ring

end Facts

/-! ## 1. Kernels: the level count is bounded by the kernel's minimum -/

section Kernel

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
variable {k : X → X → ℝ} {C : ℝ} {hkm : Measurable (Function.uncurry k)} {hC0 : 0 ≤ C}
  {hkb : ∀ x y, |k x y| ≤ C} {c : ℝ} {φ : X → ℝ} {ρ : ℝ}

/-- **The normalized trace at dyadic time is at most its value at time `2`.**
DERIVED: `2` the doubling and the least even time. -/
theorem norm_trace_le (h : StallRigid.IsTop ν k C hkm hC0 hkb c φ ρ) (hsym : ∀ x y, k x y = k y x) :
    ∀ n : ℕ, traceSeq ν k (2 * 2 ^ n) / |c| ^ (2 * 2 ^ n) ≤ hs ν k / |c| ^ 2 := by
  intro n
  induction n with
  | zero =>
    have e0 : traceSeq ν k (2 * 2 ^ 0) = hs ν k := rfl
    have e1 : (2 * 2 ^ 0 : ℕ) = 2 := rfl
    rw [e0, e1]
  | succ n ih =>
    have hf := StallRigid.IsTop.powerFacts h hsym (2 ^ n) Nat.one_le_two_pow
    have hd := norm_trace_succ hf
    have e : 2 * 2 ^ (n + 1) = 2 * (2 * 2 ^ n) := by ring
    rw [e]
    exact hd.trans ih

/-- **The top value is at least the kernel's minimum.** Integrate `c φ(z) = ∫ k(z, y) φ(y)` against `ν`.
DERIVED: `0` the sign of `φ`. -/
theorem top_ge_min {a : ℝ} (hk : ∀ x y, a ≤ k x y) (h : StallRigid.IsTop ν k C hkm hC0 hkb c φ ρ)
    (hpos : ∀ x, 0 < φ x) : a ≤ c := by
  obtain ⟨B, hB⟩ := h.bdd
  have hφi : Integrable φ ν := integrable_of_bdd h.meas hB
  have hrow : ∀ z, a * ∫ y, φ y ∂ν ≤ c * φ z := by
    intro z
    rw [← h.eig z, ← integral_const_mul]
    refine integral_mono (hφi.const_mul a) ?_ (fun y => ?_)
    · exact integrable_of_bdd ((hkm.comp measurable_prodMk_left).mul h.meas) (C := C * B)
        (fun y => by
          rw [abs_mul]
          exact mul_le_mul (hkb z y) (hB y) (abs_nonneg _) hC0)
    · exact mul_le_mul_of_nonneg_right (hk z y) (hpos y).le
  have hint : ∫ _z, a * ∫ y, φ y ∂ν ∂ν ≤ ∫ z, c * φ z ∂ν :=
    integral_mono (integrable_const _) (hφi.const_mul c) hrow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  rw [integral_const_mul] at hint
  have hpos' : 0 < ∫ y, φ y ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hφi]
    have hs : Function.support φ = Set.univ := Set.eq_univ_of_forall fun x => (hpos x).ne'
    rw [hs, measure_univ]
    exact zero_lt_one
  nlinarith

/-- **`hs(k) ≤ 1` for a kernel bounded by `1` on a probability space.** DERIVED: `1` the bound and the mass. -/
theorem hs_le_one {k : X → X → ℝ} (hk : ∀ x y, |k x y| ≤ 1) : hs ν k ≤ 1 := by
  have hin : ∀ x, ‖∫ z, k x z ^ 2 ∂ν‖ ≤ 1 := by
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => k x z ^ 2) (C := 1)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (hk x z))
    rwa [probReal_univ, mul_one] at h
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => ∫ z, k x z ^ 2 ∂ν) (C := 1)
    (Eventually.of_forall hin)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  show ∫ x, ∫ z, k x z ^ 2 ∂ν ∂ν ≤ 1
  exact (le_abs_self _).trans h

/-- **The step defect is at most `−4 log a`** for a symmetric kernel `a ≤ k`, `|k| ≤ 1`, with a positive top, at
every dyadic time. DERIVED: `4 = 2 · 2`, the purity square times the `λ₀²` of `hs(K)/λ₀²`. -/
theorem defect_le_min (h : StallRigid.IsTop ν k C hkm hC0 hkb c φ ρ) (hsym : ∀ x y, k x y = k y x)
    {a : ℝ} (ha : 0 < a) (hk : ∀ x y, a ≤ k x y) (hk1 : ∀ x y, |k x y| ≤ 1) (hpos : ∀ x, 0 < φ x)
    (n : ℕ) : DoublingPower.defect (traceSeq ν k) (2 * 2 ^ n) ≤ -4 * Real.log a := by
  have hf := StallRigid.IsTop.powerFacts h hsym (2 ^ n) Nat.one_le_two_pow
  have hd := defect_le_two_log_one_add hf
  have hl := hf.lam_pow_pos (2 * 2 ^ n)
  have hn := norm_trace_le h hsym n
  rw [hf.base, mul_div_cancel_left₀ _ hl.ne'] at hn
  have hc : 0 < |c| := abs_pos.mpr h.ne
  have hac : a ≤ |c| := (top_ge_min hk h hpos).trans (le_abs_self c)
  have hc2 : a ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ ha.le hac 2
  have h1 : hs ν k / |c| ^ 2 ≤ 1 / |c| ^ 2 :=
    div_le_div_of_nonneg_right (hs_le_one hk1) (by positivity)
  have h2 : 1 / |c| ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) hc2
  have hs0 := hf.s_nonneg
  have h3 := Real.log_le_log (by linarith) (hn.trans (h1.trans h2))
  have e : Real.log (1 / a ^ 2) = -2 * Real.log a := by
    rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  linarith

end Kernel

/-! ## 2. The Wilson torus of a compact group -/

section Group

open MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.DoublingWilsonG MassGap.RectWilson
  MassGap.RectWilsonG MassGap.RectTransferG MassGap.GaugeGroup MassGap.StallRigid

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The defect of step `i` of window `w`: `p_i(uP i + e_i)`, at time `2^{w+1}` on the slice `sliceT (2^w) i`. -/
def stepD (β : ℝ) (w : ℕ) (i : Fin 4) : ℝ := p (xWG G (2 ^ w) β) i (uP i + E i)

/-- The top value `λ₀ = ‖K‖` of the slice transfer. -/
def topNorm {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) : ℝ :=
  ‖kernelCLM (kTG G i T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ) (hSG G i T) (hSG G i T)‖

/-- **The weighted level count** of step `i` at the window time: `Tr K^{2^{w+1}}/λ₀^{2^{w+1}} − 1`.
DERIVED: `2` the doubled time. -/
def levCount {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) : ℝ :=
  traceSeq (hSG G i (sliceT (2 ^ w) i)) (kTG G i (sliceT (2 ^ w) i) β) (2 * 2 ^ w)
    / topNorm G hβ i (sliceT (2 ^ w) i) ^ (2 * 2 ^ w) - 1

variable {G} {β : ℝ}

/-- **The corner path of the next window.** DERIVED: `8, 4, 2, 1` the path weights; `0`, `1`, `2`, `3` the
four step directions of `Fin 4`. -/
theorem path_eq (x : Pt → ℝ) :
    Δ x (corner 1) = 8 * p x 0 (uP 0 + E 0) + 4 * p x 1 (uP 1 + E 1) + 2 * p x 2 (uP 2 + E 2)
      + p x 3 (uP 3 + E 3) := by
  have e11 : (corner 1 : Pt) = ![1, 1, 1, 1] := by decide
  have e111 : (![1, 1, 1, 1] : Pt) + one = ![2, 2, 2, 2] := by decide
  have e0 : p x 0 (uP 0 + E 0) = 2 * x ![1, 1, 1, 1] - x ![2, 1, 1, 1] :=
    p_eq 0 (by decide) (by decide)
  have e1 : p x 1 (uP 1 + E 1) = 2 * x ![2, 1, 1, 1] - x ![2, 2, 1, 1] :=
    p_eq 1 (by decide) (by decide)
  have e2 : p x 2 (uP 2 + E 2) = 2 * x ![2, 2, 1, 1] - x ![2, 2, 2, 1] :=
    p_eq 2 (by decide) (by decide)
  have e3 : p x 3 (uP 3 + E 3) = 2 * x ![2, 2, 2, 1] - x ![2, 2, 2, 2] :=
    p_eq 3 (by decide) (by decide)
  rw [e0, e1, e2, e3]
  simp only [Δ, e11, e111]
  ring

/-- **The next window is the weighted sum of its four steps.** DERIVED: `8, 4, 2, 1` the path weights;
`0`, `1`, `2`, `3` the four step directions of `Fin 4`. -/
theorem Dw_succ_eq (β : ℝ) (w : ℕ) :
    Dw G β (w + 1) = 8 * stepD G β w 0 + 4 * stepD G β w 1 + 2 * stepD G β w 2 + stepD G β w 3 := by
  rw [← Dw_corner1 (G := G) β w]
  exact path_eq _

/-- **The step defect is the trace defect of the slice transfer at time `2^{w+1}`.** -/
theorem stepD_eq (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    stepD G β w i = DoublingPower.defect
      (traceSeq (hSG G i (sliceT (2 ^ w) i)) (kTG G i (sliceT (2 ^ w) i) β)) (2 * 2 ^ w) := by
  obtain ⟨j, -, -, -, hn, he⟩ := window_data hw
  have e1 : ext (2 ^ w) (uP i) i = 2 ^ w := by simp [ext, uP_self]
  have x2 := xWG_eq (G := G) hβ hn he (uP i + E i) i
  have x3 := xWG_eq (G := G) hβ hn he (uP i + E i + E i) i
  rw [tr_ext_add, ext_add_self, e1] at x2
  rw [tr_ext_add, tr_ext_add, ext_add_self, ext_add_self, e1] at x3
  rw [stepD, p, x2, x3]
  rfl

/-- **One step: the defect is pinned between `log(1 + n)` and `2 log(1 + n)`**, `n` the weighted level count.
DERIVED: `2` the square in the purity. -/
theorem step_sandwich (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    0 ≤ levCount G hβ w i ∧ Real.log (1 + levCount G hβ w i) ≤ stepD G β w i ∧
      stepD G β w i ≤ 2 * Real.log (1 + levCount G hβ w i) := by
  obtain ⟨c, φ, ρ, hT, -, -, -⟩ := exists_topG (G := G) hβ i (sliceT (2 ^ w) i)
  have hf := IsTop.powerFacts hT (kTG_symm β) (2 ^ w) Nat.one_le_two_pow
  have hlev : levCount G hβ w i = KernelPower.excited (hSG G i (sliceT (2 ^ w) i))
      (kTG G i (sliceT (2 ^ w) i) β) c φ (2 ^ w) := by
    have htop : topNorm G hβ i (sliceT (2 ^ w) i) = |c| := (IsTop.top hT).symm
    rw [levCount, htop, hf.base, mul_div_cancel_left₀ _ (hf.lam_pow_pos _).ne']
    ring
  rw [stepD_eq hβ hw i, hlev]
  exact ⟨hf.s_nonneg, log_one_add_le_defect hf, defect_le_two_log_one_add hf⟩

theorem stepD_nonneg (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) : 0 ≤ stepD G β w i := by
  have h := step_sandwich (G := G) hβ hw i
  exact (Real.log_nonneg (by linarith [h.1])).trans h.2.1

/-- **The level-count sandwich of a window.** DERIVED: `8, 4, 2, 1` the path weights, `2` the purity square;
`0`, `1`, `2`, `3` the four step directions of `Fin 4`. -/
theorem count_sandwich (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    (∀ i, Real.log (1 + levCount G hβ w i) ≤ Dw G β (w + 1)) ∧
      Dw G β (w + 1) ≤ 2 * (8 * Real.log (1 + levCount G hβ w 0) + 4 * Real.log (1 + levCount G hβ w 1)
        + 2 * Real.log (1 + levCount G hβ w 2) + Real.log (1 + levCount G hβ w 3)) := by
  have hD := Dw_succ_eq (G := G) β w
  have n0 := stepD_nonneg (G := G) hβ hw 0
  have n1 := stepD_nonneg (G := G) hβ hw 1
  have n2 := stepD_nonneg (G := G) hβ hw 2
  have n3 := stepD_nonneg (G := G) hβ hw 3
  refine ⟨fun i => ?_, ?_⟩
  · have hle : stepD G β w i ≤ Dw G β (w + 1) := by
      rw [hD]
      fin_cases i
      · show stepD G β w 0 ≤ _
        linarith
      · show stepD G β w 1 ≤ _
        linarith
      · show stepD G β w 2 ≤ _
        linarith
      · show stepD G β w 3 ≤ _
        linarith
    exact (step_sandwich hβ hw i).2.1.trans hle
  · rw [hD]
    linarith [(step_sandwich (G := G) hβ hw 0).2.2, (step_sandwich (G := G) hβ hw 1).2.2,
      (step_sandwich (G := G) hβ hw 2).2.2, (step_sandwich (G := G) hβ hw 3).2.2]

/-- **(H) is a bounded weighted level count.** `D` is bounded along the windows exactly when the weighted count of
transfer levels at the window time is bounded on the four step slices, at every `β ≥ 0`, for every compact group.
DERIVED: `30 = 2 · 15`; `2` the window offset. -/
theorem bounded_iff_count (hβ : 0 ≤ β) :
    (∃ A : ℝ, ∀ᶠ w in atTop, Dw G β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, ∀ i, levCount G hβ w i ≤ B := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨Real.exp A - 1, ?_⟩
    obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp hA
    refine eventually_atTop.mpr ⟨max w₀ 1, fun w hw i => ?_⟩
    have h1 : 1 ≤ w := (le_max_right _ _).trans hw
    have h0 : w₀ ≤ w := (le_max_left _ _).trans hw
    have hD := hw₀ (w + 1) (by omega)
    have hs := (count_sandwich (G := G) hβ h1).1 i
    have hc := (step_sandwich (G := G) hβ h1 i).1
    have h2 : Real.log (1 + levCount G hβ w i) ≤ A := hs.trans hD
    have h3 := Real.exp_le_exp.mpr h2
    rw [Real.exp_log (by linarith)] at h3
    linarith
  · rintro ⟨B, hB⟩
    obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp hB
    refine ⟨30 * Real.log (1 + max B 0), eventually_atTop.mpr ⟨w₀ + 2, fun w hw => ?_⟩⟩
    obtain ⟨u, rfl⟩ : ∃ u, w = u + 1 := ⟨w - 1, by omega⟩
    have hu : 1 ≤ u := by omega
    have hb := hw₀ u (by omega)
    have hS := (count_sandwich (G := G) hβ hu).2
    have hl : ∀ i, Real.log (1 + levCount G hβ u i) ≤ Real.log (1 + max B 0) := fun i =>
      Real.log_le_log (by linarith [(step_sandwich (G := G) hβ hu i).1])
        (by linarith [hb i, le_max_left B 0])
    linarith [hl 0, hl 1, hl 2, hl 3]

/-- **The log of the kernel minimum is minus the coupling times the slice plaquette bound.** DERIVED: `2` the two
temporal plaquette factors of `kTmin`. -/
theorem neg_log_kTmin (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) (β : ℝ) :
    -Real.log (RectTransfer.kTmin i T β) = β * (RectTransfer.spMax i T + 2 * RectTransfer.tpMax i T) := by
  unfold RectTransfer.kTmin
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  ring

/-- **The step defect is at most the surface cost of its slice.** DERIVED: `4` from `defect_le_min`. -/
theorem stepD_le_surface (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    stepD G β w i ≤ 4 * β * (RectTransfer.spMax i (sliceT (2 ^ w) i)
      + 2 * RectTransfer.tpMax i (sliceT (2 ^ w) i)) := by
  obtain ⟨c, φ, ρ, hT, -, -, hφ⟩ := exists_topG (G := G) hβ i (sliceT (2 ^ w) i)
  rw [stepD_eq hβ hw i]
  have h := defect_le_min hT (kTG_symm β) (a := RectTransfer.kTmin i (sliceT (2 ^ w) i) β)
    (RectTransfer.kTmin_pos β) (kTG_lower hβ) (abs_kTG_le hβ) hφ w
  have e := neg_log_kTmin i (sliceT (2 ^ w) i) β
  nlinarith

/-- **The surface bound.** At every `β ≥ 0`, every window `w ≥ 1`, every compact group:
`D(w+1) ≤ 4 β Σ c_i (spMax_i + 2 tpMax_i)`, the plaquette counts of the four step slices: `D = O(β 8^w)`.
DERIVED: `8, 4, 2, 1` the path weights, `4` from `defect_le_min`; `0`, `1`, `2`, `3` the four step
directions of `Fin 4`; `2` the time-plaquette weight of `stepD_le_surface`. -/
theorem surface_bound (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    Dw G β (w + 1) ≤ 4 * β *
      (8 * (RectTransfer.spMax 0 (sliceT (2 ^ w) 0) + 2 * RectTransfer.tpMax 0 (sliceT (2 ^ w) 0))
        + 4 * (RectTransfer.spMax 1 (sliceT (2 ^ w) 1) + 2 * RectTransfer.tpMax 1 (sliceT (2 ^ w) 1))
        + 2 * (RectTransfer.spMax 2 (sliceT (2 ^ w) 2) + 2 * RectTransfer.tpMax 2 (sliceT (2 ^ w) 2))
        + (RectTransfer.spMax 3 (sliceT (2 ^ w) 3) + 2 * RectTransfer.tpMax 3 (sliceT (2 ^ w) 3))) := by
  rw [Dw_succ_eq]
  have h0 := stepD_le_surface (G := G) hβ hw 0
  have h1 := stepD_le_surface (G := G) hβ hw 1
  have h2 := stepD_le_surface (G := G) hβ hw 2
  have h3 := stepD_le_surface (G := G) hβ hw 3
  linarith

end Group

/-! ## 3. `SU(N)`: the level count and the torus free energy -/

section SU

open MassGap.ZoomContract MassGap.CouplingTower MassGap.StallRigid

variable {N : ℕ} {β : ℝ}

theorem bounded_iff_count_SU [NeZero N] (hβ : 0 ≤ β) :
    (∃ A : ℝ, ∀ᶠ w in atTop, windowCoupling N β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, ∀ i, levCount (MassGap.SUN.SU N) hβ w i ≤ B := by
  have e : Dw (MassGap.SUN.SU N) β = windowCoupling N β := funext (Dw_SU β)
  have h := bounded_iff_count (G := MassGap.SUN.SU N) hβ
  rw [e] at h
  exact h

theorem zoomLimit_le (hN : N ≠ 0) (hβ : 0 ≤ β) (k : ℕ) : zoomLimit N β ≤ freeSite N β (k + 1) := by
  unfold zoomLimit
  exact ciInf_le ⟨-(32 * β), by rintro _ ⟨j, rfl⟩; exact (freeSite_bounds hN hβ (j + 1)).1⟩ k

/-- **The partial sums of the per-site drop.** `D(u) ≤ A` from `w` on bounds the drop of the free energy per site from
`w` to `w + n` by `16^{−w} (A/15 − A/(15·16ⁿ))`. DERIVED: `15 = 16 − 1`, `16 = 2⁴`. -/
theorem freeEnergy_partial {A : ℝ} {w : ℕ} (hA : ∀ u, w ≤ u → windowCoupling N β u ≤ A) :
    ∀ n : ℕ, 16 ^ w * (freeSite N β w - freeSite N β (n + w)) ≤ A / 15 - A / (15 * 16 ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hD := hA (n + w) (by omega)
    rw [windowCoupling_eq] at hD
    have e1 : n + 1 + w = n + w + 1 := by omega
    rw [e1]
    have hq : (0 : ℝ) < 16 ^ n := by positivity
    have hw0 : (0 : ℝ) < 16 ^ w := by positivity
    have e2 : (16 : ℝ) ^ (n + w + 1) = 16 ^ w * (16 * 16 ^ n) := by ring
    rw [e2] at hD
    have hY : 16 ^ w * (freeSite N β (n + w) - freeSite N β (n + w + 1)) ≤ A / (16 * 16 ^ n) := by
      rw [le_div_iff₀ (by positivity)]
      calc 16 ^ w * (freeSite N β (n + w) - freeSite N β (n + w + 1)) * (16 * 16 ^ n)
          = 16 ^ w * (16 * 16 ^ n) * (freeSite N β (n + w) - freeSite N β (n + w + 1)) := by ring
        _ ≤ A := hD
    have e3 : A / 15 - A / (15 * 16 ^ n) + A / (16 * 16 ^ n) = A / 15 - A / (15 * 16 ^ (n + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    have e4 : 16 ^ w * (freeSite N β w - freeSite N β (n + w + 1))
        = 16 ^ w * (freeSite N β w - freeSite N β (n + w))
          + 16 ^ w * (freeSite N β (n + w) - freeSite N β (n + w + 1)) := by ring
    rw [e4]
    linarith

/-- **A bounded defect is a bounded total finite-size correction.** `D(u) ≤ A` for all `u ≥ w` gives
`16^w (f_w − f_∞) ≤ max(A, 0)/15`. DERIVED: `15 = 16 − 1`. -/
theorem freeEnergy_rate (hN : N ≠ 0) (hβ : 0 ≤ β) {A : ℝ} {w : ℕ}
    (hA : ∀ u, w ≤ u → windowCoupling N β u ≤ A) :
    16 ^ w * (freeSite N β w - zoomLimit N β) ≤ max A 0 / 15 := by
  have hA' : ∀ u, w ≤ u → windowCoupling N β u ≤ max A 0 :=
    fun u hu => (hA u hu).trans (le_max_left _ _)
  have hp := freeEnergy_partial hA'
  have hT : Tendsto (fun n => 16 ^ w * (freeSite N β w - freeSite N β (n + w))) atTop
      (𝓝 (16 ^ w * (freeSite N β w - zoomLimit N β))) := by
    have h1 : Tendsto (fun n => freeSite N β (n + w)) atTop (𝓝 (zoomLimit N β)) :=
      (tendsto_add_atTop_iff_nat w).mpr (tendsto_freeSite hN hβ)
    exact (tendsto_const_nhds.sub h1).const_mul _
  refine le_of_tendsto' hT fun n => (hp n).trans ?_
  have : 0 ≤ max A 0 / (15 * 16 ^ n) := div_nonneg (le_max_right _ _) (by positivity)
  linarith

/-- **(H) is `log Z(2^w) = 16^w f_∞ + O(1)`.** At `SU(N)`, `β ≥ 0`: the defect is bounded along the windows exactly
when `16^w (f_w − f_∞)` is. DERIVED: `16 = 2⁴`. -/
theorem bounded_iff_freeEnergy (hN : N ≠ 0) (hβ : 0 ≤ β) :
    (∃ A : ℝ, ∀ᶠ w in atTop, windowCoupling N β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, 16 ^ w * (freeSite N β w - zoomLimit N β) ≤ B := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp hA
    exact ⟨max A 0 / 15, eventually_atTop.mpr ⟨w₀, fun w hw =>
      freeEnergy_rate hN hβ (fun u hu => hw₀ u (hw.trans hu))⟩⟩
  · rintro ⟨B, hB⟩
    refine ⟨16 * B, hB.mono fun w hw => ?_⟩
    rw [windowCoupling_eq]
    have h1 := zoomLimit_le hN hβ w
    have hw0 : (0 : ℝ) ≤ 16 ^ w := by positivity
    have h2 : 16 ^ w * (freeSite N β w - freeSite N β (w + 1))
        ≤ 16 ^ w * (freeSite N β w - zoomLimit N β) :=
      mul_le_mul_of_nonneg_left (by linarith) hw0
    calc (16 : ℝ) ^ (w + 1) * (freeSite N β w - freeSite N β (w + 1))
        = 16 * (16 ^ w * (freeSite N β w - freeSite N β (w + 1))) := by ring
      _ ≤ 16 * B := by linarith

end SU

/-! ## 4. The shape of a failure: a volume power in `Z` -/

/-- **A term `a w + b` in `log Z(2^w)` enters `D` as `15 a w − a + 15 b`.** DERIVED: `16 = 2⁴`, `15 = 16 − 1`. -/
theorem log_term (f a b : ℝ) (w : ℕ) :
    16 * ((16 : ℝ) ^ w * f + a * w + b) - ((16 : ℝ) ^ (w + 1) * f + a * ((w + 1 : ℕ) : ℝ) + b)
      = 15 * a * w - a + 15 * b := by
  push_cast
  ring

/-- **A positive volume power makes `D` unbounded.** DERIVED: `15` from `log_term`. -/
theorem log_term_unbounded {a b : ℝ} (ha : 0 < a) (A : ℝ) :
    ∀ᶠ w : ℕ in atTop, A < 15 * a * w - a + 15 * b := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((A + a - 15 * b) / (15 * a))
  refine eventually_atTop.mpr ⟨n, fun w hw => ?_⟩
  have hw' : (n : ℝ) ≤ w := by exact_mod_cast hw
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith

/-! ## 5. Tests -/

section Tests

open MassGap.StallRigid

/-- **The level-count reduction at `U(1)`, `A₅`, `G₂`**, by the one proof. -/
theorem count_tests {β : ℝ} (hβ : 0 ≤ β) :
    ((∃ A : ℝ, ∀ᶠ w in atTop, Dw Circle β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, ∀ i, levCount Circle hβ w i ≤ B) ∧
    ((∃ A : ℝ, ∀ᶠ w in atTop, Dw CoverCompact.A5 β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, ∀ i, levCount CoverCompact.A5 hβ w i ≤ B) ∧
    ((∃ A : ℝ, ∀ᶠ w in atTop, Dw GaugeG2.G2 β w ≤ A) ↔
      ∃ B : ℝ, ∀ᶠ w in atTop, ∀ i, levCount GaugeG2.G2 hβ w i ≤ B) :=
  ⟨bounded_iff_count hβ, bounded_iff_count hβ, bounded_iff_count hβ⟩

/-- **The surface bound at `U(1)`, `A₅`, `G₂`**: each step defect is at most `4 β (spMax + 2 tpMax)` of its slice. -/
theorem surface_tests {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    stepD Circle β w i ≤ 4 * β * (RectTransfer.spMax i (sliceT (2 ^ w) i)
      + 2 * RectTransfer.tpMax i (sliceT (2 ^ w) i)) ∧
    stepD CoverCompact.A5 β w i ≤ 4 * β * (RectTransfer.spMax i (sliceT (2 ^ w) i)
      + 2 * RectTransfer.tpMax i (sliceT (2 ^ w) i)) ∧
    stepD GaugeG2.G2 β w i ≤ 4 * β * (RectTransfer.spMax i (sliceT (2 ^ w) i)
      + 2 * RectTransfer.tpMax i (sliceT (2 ^ w) i)) :=
  ⟨stepD_le_surface hβ hw i, stepD_le_surface hβ hw i, stepD_le_surface hβ hw i⟩

end Tests

end MassGap.DefectBound

#print axioms MassGap.DefectBound.log_one_add_le_defect
#print axioms MassGap.DefectBound.defect_le_two_log_one_add
#print axioms MassGap.DefectBound.norm_trace_succ
#print axioms MassGap.DefectBound.norm_trace_le
#print axioms MassGap.DefectBound.top_ge_min
#print axioms MassGap.DefectBound.hs_le_one
#print axioms MassGap.DefectBound.defect_le_min
#print axioms MassGap.DefectBound.path_eq
#print axioms MassGap.DefectBound.Dw_succ_eq
#print axioms MassGap.DefectBound.stepD_eq
#print axioms MassGap.DefectBound.step_sandwich
#print axioms MassGap.DefectBound.stepD_nonneg
#print axioms MassGap.DefectBound.count_sandwich
#print axioms MassGap.DefectBound.bounded_iff_count
#print axioms MassGap.DefectBound.neg_log_kTmin
#print axioms MassGap.DefectBound.stepD_le_surface
#print axioms MassGap.DefectBound.surface_bound
#print axioms MassGap.DefectBound.bounded_iff_count_SU
#print axioms MassGap.DefectBound.zoomLimit_le
#print axioms MassGap.DefectBound.freeEnergy_partial
#print axioms MassGap.DefectBound.freeEnergy_rate
#print axioms MassGap.DefectBound.bounded_iff_freeEnergy
#print axioms MassGap.DefectBound.log_term
#print axioms MassGap.DefectBound.log_term_unbounded
#print axioms MassGap.DefectBound.count_tests
#print axioms MassGap.DefectBound.surface_tests
