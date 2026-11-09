import Mathlib
import MassGap.JentzschKT
import MassGap.ReadsSlabWilson

/-!
# MassGap.SlabMeasure — the slab on `L²(π)` of a measure, the Doob slab of a positive kernel, and `ReadsSlab` for Wilson

`RelativeGap.Slab` and every statement of `GapL2` live on a finite state space. This module states the
same objects on `L²(π)` of a probability measure, builds the Doob slab of a symmetric positive kernel
from a strictly positive top eigenfunction (`JentzschKT`), and runs the (A)-chain of `RelativeGap` on
the Wilson slice transfer `RectTransfer.kT`. Everything is at one finite volume; no gap is proved.

## 1. Contraction on the complement of a fixed vector (proved)

`E` a real inner product space, `P : E →L[ℝ] E`, `e ∈ E`.

* `ContrH P e r`: `‖P g‖ ≤ r ‖g‖` for every `g ⊥ e`, `r ≥ 0`. `rhoH P e = sInf {r | ContrH P e r}`;
  `contrH_rhoH`: the infimum is a rate.
* For `P` symmetric with `P e = e` (`hsym`, `hfix`): `ContrH.pow`; `rhoH_pow`:
  `rhoH (Pⁿ) e = (rhoH P e)ⁿ` for `n ≥ 1`. The `≥` half: the norms `bⱼ = ‖Pʲ g‖` are log-convex
  (`b_{j+1}² = ⟪Pʲ g, P^{j+2} g⟫ ≤ bⱼ b_{j+2}`), so `‖P g‖ > r ‖g‖` propagates to `bₙ ≥ rⁿ b₀`.
* `lam1H P e = sInf {s ≥ 0 | ∀ g ⊥ e, ⟪g, P g⟫ ≤ s ‖g‖²}` (`lam1H_spec`: a bound). `lam1H_le_rhoH`
  always; `rhoH_eq_lam1H`: equality when `⟪g, P g⟫ ≥ 0` on `e⊥` (Cauchy–Schwarz for the form).

## 2. The slab on `L²(π)` (defined)

`SlabM`: a probability space `(Ω, π)` and `P : L²(π) →L L²(π)` symmetric, `P 1 = 1`, positivity
preserving. `ContrM S r`: `‖P g‖ ≤ r ‖g‖` for `∫ g dπ = 0` (`contrM_iff`: it is `ContrH P 1 r`).
`SlabM.rho = rhoH P 1`. `stat`: `∫ P g dπ = ∫ g dπ`. `SlabM.pow S n` (the slab of `n` steps) and
`rho_pow`: `(S.pow n).rho = S.rhoⁿ`, `n ≥ 1`.

`ReadsSlabM`, `RelFloorM`, `fixedApertureFloor_of_relFloorM` are `RelativeGap.ReadsSlab`,
`RelFloor`, `fixedApertureFloor_of_relFloor` with `SlabM` in place of `Slab`.

## 3. The Doob slab of a positive kernel (proved)

`PerronKernel`: `(X, μ)` a probability space, `k` measurable, symmetric, `0 ≤ k ≤ C`; `φ` measurable,
`φ ≥ c > 0`, `∫ φ² dμ = 1`, `∫ k(z,y) φ(y) dμ(y) = λ₀ φ(z)` at every `z`, `λ₀ > 0`.

* `piD = φ² μ`, a probability measure; `kPi x y = k(x,y)/(λ₀ φ(x) φ(y))`, bounded by `C/(λ₀ c²)`;
  `PD = kernelCLM kPi` on `L²(piD)`. `doob`: the `SlabM` `(piD, PD)`. `PD_density`: `PD g (x) =
  ∫ kD(x,y) g(y) dμ(y)` with the Doob density `kD x y = k(x,y) φ(y) / (λ₀ φ(x))`.
* `U g = φ g`, `L²(piD) → L²(μ)`: `inner_U` (isometric), `U_V` (onto), and
  `inner_U_K`: `⟪U g, K (U g)⟫ = λ₀ ⟪g, PD g⟫` with `K = kernelCLM k` on `L²(μ)`. `phiL = U 1`
  (`coeFn_phiL`: `= φ`; `K_phiL`: `K phiL = λ₀ phiL`).
* `lam1 = lam1H K phiL`: the top of the Rayleigh quotient of `K` on `φ⊥` in `L²(μ)`.
  `lam1H_PD`: `lam1H PD 1 = lam1 / λ₀`. `ratio = doob.rho` (the one-step rate);
  `lam1_div_le_ratio`; `ratio_eq` (`ratio = lam1/λ₀`) when `K` is semidefinite on `φ⊥`;
  `rho_slab`: `(slab n).rho = ratioⁿ`, `n ≥ 1`.
* `boxGap a = −log ratio / a`; `readsSlabM_transfer`, `readsSlabM_box`: the measure analogue of
  `ReadsSlabWilson.readsSlab_transfer`/`readsSlab_box`.

## 4. Wilson (proved)

`perronKT`: the `PerronKernel` of `RectTransfer.kT μ T N β` (`N ≠ 0`, `β ≥ 0`) with the eigenfunction of
`JentzschKT.exists_pos_eigen_kT` and `λ₀ = ‖kernelCLM kT‖`. `readsSlabM_wilson`: the box gap
`−log ratio / a_k` reads the Doob slab of `m 2ᵏ` steps, under the hypothesis that every one-step
rate `ratio` is positive; `fixedApertureFloor_wilson`: with that hypothesis, `RelFloorM` for that
family gives `FixedApertureFloor`. `ratio_eq_wilson`: `ratio = λ₁/λ₀` under semidefiniteness
of `kT` on `φ⊥` in `L²(Haar)`, a hypothesis here: the tree proves the form nonnegative on continuous
gauge-invariant functions (`SliceKernelDefinite.sliceKernel_form_nonneg`), not on all of `L²`.
`ratio_pos_of_form_pos`: `ratio > 0` when the form of `K` is positive at some `h ⊥ φ`.

DERIVED (module-wide): `0` the inner product selecting `e⊥` and the sign of every rate; `1` the
fixed vector of a Markov operator, the least number of steps and the mass of `π`; `2` the `L²`
exponent and the degree of `φ` in `φ²`.
-/

noncomputable section

namespace MassGap.SlabMeasure

open MeasureTheory Filter Topology MassGap.SlabKernelOperator MassGap.SlabTransferAdjoint
open MassGap.FixedAperture
open scoped NNReal ENNReal

/-! ## 1. Contraction on the complement of a fixed vector -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **`‖P g‖ ≤ r ‖g‖` on `e⊥`.** -/
def ContrH (P : E →L[ℝ] E) (e : E) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ g : E, inner ℝ g e = 0 → ‖P g‖ ≤ r * ‖g‖

/-- The least contraction rate on `e⊥`. -/
def rhoH (P : E →L[ℝ] E) (e : E) : ℝ := sInf {r | ContrH P e r}

variable (P : E →L[ℝ] E) (e : E)

theorem contrH_norm : ContrH P e ‖P‖ := ⟨norm_nonneg _, fun g _ => P.le_opNorm g⟩

theorem rhoH_nonneg : 0 ≤ rhoH P e := le_csInf ⟨_, contrH_norm P e⟩ fun _ h => h.1

variable {P e} in
theorem rhoH_le {r : ℝ} (h : ContrH P e r) : rhoH P e ≤ r := csInf_le ⟨0, fun _ h => h.1⟩ h

/-- **The infimum is a rate.** -/
theorem contrH_rhoH : ContrH P e (rhoH P e) := by
  refine ⟨rhoH_nonneg P e, fun g hg => ?_⟩
  rcases (norm_nonneg g).lt_or_eq with hp | hz
  · have : ‖P g‖ / ‖g‖ ≤ rhoH P e :=
      le_csInf ⟨_, contrH_norm P e⟩ fun r hr => (div_le_iff₀ hp).2 (hr.2 g hg)
    rwa [div_le_iff₀ hp] at this
  · have : g = 0 := norm_eq_zero.1 hz.symm
    subst this; simp

variable {P e}

theorem ContrH.mono {r s : ℝ} (h : ContrH P e r) (hrs : r ≤ s) : ContrH P e s :=
  ⟨h.1.trans hrs, fun g hg => (h.2 g hg).trans (mul_le_mul_of_nonneg_right hrs (norm_nonneg _))⟩

section Sym

variable (hsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v)) (hfix : P e = e)

theorem pow_succ_apply (j : ℕ) (g : E) : (P ^ (j + 1)) g = P ((P ^ j) g) := by
  rw [pow_succ']; rfl

theorem pow_succ_apply' (j : ℕ) (g : E) : (P ^ (j + 1)) g = (P ^ j) (P g) := by
  rw [pow_succ]; rfl

include hsym hfix in
theorem inner_pow_e (g : E) (hg : inner ℝ g e = 0) (j : ℕ) : inner ℝ ((P ^ j) g) e = 0 := by
  induction j with
  | zero => simpa using hg
  | succ j ih => rw [pow_succ_apply, hsym, hfix, ih]

include hsym hfix in
/-- Stacking: a rate `r` of `P` gives the rate `rⁿ` of `Pⁿ`. -/
theorem ContrH.pow {r : ℝ} (h : ContrH P e r) (n : ℕ) : ContrH (P ^ n) e (r ^ n) := by
  induction n with
  | zero => exact ⟨by simp, fun g _ => by simp⟩
  | succ n ih =>
    refine ⟨pow_nonneg h.1 _, fun g hg => ?_⟩
    rw [pow_succ_apply']
    have hPg : inner ℝ (P g) e = 0 := by rw [hsym, hfix, hg]
    calc ‖(P ^ n) (P g)‖ ≤ r ^ n * ‖P g‖ := ih.2 _ hPg
      _ ≤ r ^ n * (r * ‖g‖) := mul_le_mul_of_nonneg_left (h.2 g hg) (pow_nonneg h.1 _)
      _ = r ^ (n + 1) * ‖g‖ := by ring

include hsym in
/-- The norms `‖Pʲ g‖` of a symmetric operator are log-convex. -/
theorem norm_pow_logconvex (g : E) (j : ℕ) :
    ‖(P ^ (j + 1)) g‖ ^ 2 ≤ ‖(P ^ j) g‖ * ‖(P ^ (j + 1 + 1)) g‖ := by
  rw [pow_succ_apply j g, pow_succ_apply (j + 1) g, pow_succ_apply j g,
    ← real_inner_self_eq_norm_sq, hsym]
  exact real_inner_le_norm _ _

include hsym hfix in
/-- **The rate of a power is the power of the rate** for a symmetric `P` fixing `e`, `n ≥ 1`. -/
theorem rhoH_pow {n : ℕ} (hn : 1 ≤ n) : rhoH (P ^ n) e = rhoH P e ^ n := by
  refine le_antisymm (rhoH_le ((contrH_rhoH P e).pow hsym hfix n)) ?_
  have hs := contrH_rhoH (P ^ n) e
  refine MassGap.ReadsSlabWilson.pow_le_of_forall_lt (by omega) hs.1 (rhoH_nonneg P e) fun r hr0 hrρ => ?_
  have hnc : ¬ ContrH P e r := fun hc => absurd (rhoH_le hc) (not_le.2 hrρ)
  obtain ⟨g, hg, hlt⟩ : ∃ g, inner ℝ g e = 0 ∧ r * ‖g‖ < ‖P g‖ := by
    by_contra hne
    push Not at hne
    exact hnc ⟨hr0, hne⟩
  set b : ℕ → ℝ := fun j => ‖(P ^ j) g‖ with hb
  have hb0 : b 0 = ‖g‖ := by simp [hb]
  have hb1 : b 1 = ‖P g‖ := by simp [hb]
  have hnn : ∀ j, 0 ≤ b j := fun j => norm_nonneg _
  have hlc : ∀ j, b (j + 1) ^ 2 ≤ b j * b (j + 1 + 1) := norm_pow_logconvex hsym g
  have hstep : ∀ j, r * b j ≤ b (j + 1) := by
    intro j
    induction j with
    | zero => rw [hb0, hb1]; exact hlt.le
    | succ j ih =>
      have h1 := hlc j
      rcases (hnn j).lt_or_eq with hp | hz
      · have h2 : r * b j * b (j + 1) ≤ b j * b (j + 1 + 1) :=
          (mul_le_mul_of_nonneg_right ih (hnn (j + 1))).trans (by nlinarith)
        have h3 : b j * (r * b (j + 1)) ≤ b j * b (j + 1 + 1) := by linarith
        exact le_of_mul_le_mul_left h3 hp
      · have : b (j + 1) = 0 := by
          rw [← hz, zero_mul] at h1
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
        rw [this, mul_zero]; exact hnn _
  have hgrow : ∀ j, r ^ j * b 0 ≤ b j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc r ^ (j + 1) * b 0 = r * (r ^ j * b 0) := by ring
        _ ≤ r * b j := mul_le_mul_of_nonneg_left ih hr0
        _ ≤ b (j + 1) := hstep j
  have hpos : 0 < b 0 := by
    rcases (hnn 0).lt_or_eq with hp | hz
    · exact hp
    · exfalso
      have hg0 : g = 0 := by rw [hb0] at hz; exact norm_eq_zero.1 hz.symm
      rw [hg0] at hlt
      simp at hlt
  have hn' : b n ≤ rhoH (P ^ n) e * b 0 := by rw [hb0]; exact hs.2 g hg
  have h4 : r ^ n * b 0 ≤ rhoH (P ^ n) e * b 0 := (hgrow n).trans hn'
  exact le_of_mul_le_mul_right h4 hpos

end Sym

variable (P e) in
/-- The Rayleigh bounds of `P` on `e⊥`. -/
def raySetH : Set ℝ := {s | 0 ≤ s ∧ ∀ g : E, inner ℝ g e = 0 → inner ℝ g (P g) ≤ s * ‖g‖ ^ 2}

variable (P e) in
/-- **`λ₁`**: the top of the Rayleigh quotient of `P` on `e⊥` (and `0` if that top is negative). -/
def lam1H : ℝ := sInf (raySetH P e)

/-- A rate bounds the Rayleigh quotient. -/
theorem rayleigh_of_contrH {r : ℝ} (h : ContrH P e r) (g : E) (hg : inner ℝ g e = 0) :
    inner ℝ g (P g) ≤ r * ‖g‖ ^ 2 :=
  calc inner ℝ g (P g) ≤ ‖g‖ * ‖P g‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * (r * ‖g‖) := mul_le_mul_of_nonneg_left (h.2 g hg) (norm_nonneg _)
    _ = r * ‖g‖ ^ 2 := by ring

theorem norm_mem_raySetH : ‖P‖ ∈ raySetH P e :=
  ⟨norm_nonneg _, rayleigh_of_contrH (contrH_norm P e)⟩

theorem lam1H_nonneg : 0 ≤ lam1H P e := le_csInf ⟨_, norm_mem_raySetH⟩ fun _ hs => hs.1

theorem lam1H_le {s : ℝ} (hs : s ∈ raySetH P e) : lam1H P e ≤ s :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ hs

/-- **The infimum is a Rayleigh bound.** -/
theorem lam1H_spec (g : E) (hg : inner ℝ g e = 0) : inner ℝ g (P g) ≤ lam1H P e * ‖g‖ ^ 2 := by
  rcases (norm_nonneg g).lt_or_eq with hp | hz
  · have hp2 : 0 < ‖g‖ ^ 2 := by positivity
    have : inner ℝ g (P g) / ‖g‖ ^ 2 ≤ lam1H P e :=
      le_csInf ⟨_, norm_mem_raySetH⟩ fun s hs => (div_le_iff₀ hp2).2 (hs.2 g hg)
    rwa [div_le_iff₀ hp2] at this
  · have : g = 0 := norm_eq_zero.1 hz.symm
    subst this; simp

theorem lam1H_mem : lam1H P e ∈ raySetH P e := ⟨lam1H_nonneg, lam1H_spec⟩

/-- `λ₁ ≤ ρ` always. -/
theorem lam1H_le_rhoH : lam1H P e ≤ rhoH P e :=
  lam1H_le ⟨rhoH_nonneg P e, rayleigh_of_contrH (contrH_rhoH P e)⟩

section Psd

variable (hsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v)) (hfix : P e = e)
  (hpsd : ∀ g : E, inner ℝ g e = 0 → 0 ≤ inner ℝ g (P g))

include hsym hpsd in
/-- **Cauchy–Schwarz for a form nonnegative on `e⊥`.** -/
theorem form_cs {u v : E} (hu : inner ℝ u e = 0) (hv : inner ℝ v e = 0) :
    inner ℝ u (P v) ^ 2 ≤ inner ℝ u (P u) * inner ℝ v (P v) := by
  have hvu : inner ℝ v (P u) = inner ℝ u (P v) := by rw [← hsym, real_inner_comm]
  refine MassGap.ReadsSlabWilson.sq_le_of_quad (hpsd v hv) fun l => ?_
  have hw := hpsd (u - l • v) (by rw [inner_sub_left, real_inner_smul_left, hu, hv]; ring)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hvu] at hw
  nlinarith [hw]

include hsym hfix hpsd in
/-- **A semidefinite symmetric operator contracts at the top of its Rayleigh quotient.** -/
theorem contrH_of_rayleigh {c : ℝ} (hc : 0 ≤ c)
    (hray : ∀ g : E, inner ℝ g e = 0 → inner ℝ g (P g) ≤ c * ‖g‖ ^ 2) : ContrH P e c := by
  refine ⟨hc, fun g hg => ?_⟩
  have hk : inner ℝ (P g) e = 0 := by rw [hsym, hfix, hg]
  have e1 : ‖P g‖ ^ 2 = inner ℝ g (P (P g)) := by rw [← real_inner_self_eq_norm_sq, hsym]
  have cs := form_cs hsym hpsd hg hk
  have r1 := hray g hg
  have r2 := hray _ hk
  have p1 := hpsd g hg
  have p2 := hpsd _ hk
  have h3 : (‖P g‖ ^ 2) ^ 2 ≤ (c * ‖g‖ ^ 2) * (c * ‖P g‖ ^ 2) := by
    calc (‖P g‖ ^ 2) ^ 2 = inner ℝ g (P (P g)) ^ 2 := by rw [e1]
      _ ≤ inner ℝ g (P g) * inner ℝ (P g) (P (P g)) := cs
      _ ≤ (c * ‖g‖ ^ 2) * (c * ‖P g‖ ^ 2) := mul_le_mul r1 r2 p2 (by positivity)
  rcases (norm_nonneg (P g)).lt_or_eq with hp | hz
  · have hp2 : 0 < ‖P g‖ ^ 2 := by positivity
    have h4 : ‖P g‖ ^ 2 ≤ (c * ‖g‖) ^ 2 := by
      have : ‖P g‖ ^ 2 * ‖P g‖ ^ 2 ≤ (c * ‖g‖) ^ 2 * ‖P g‖ ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right this hp2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4
  · rw [← hz]; positivity

include hsym hfix hpsd in
/-- **`ρ = λ₁`** for a symmetric operator fixing `e` and semidefinite on `e⊥`. -/
theorem rhoH_eq_lam1H : rhoH P e = lam1H P e :=
  le_antisymm (rhoH_le (contrH_of_rayleigh hsym hfix hpsd lam1H_nonneg lam1H_spec))
    lam1H_le_rhoH

end Psd

end Hilbert

/-! ## 2. The slab on `L²(π)` -/

section Mean

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} [IsProbabilityMeasure π]

/-- `⟪g, 1⟫ = ∫ g dπ`. -/
theorem inner_oneLp (g : Lp ℝ 2 π) : inner ℝ g (oneLp π) = ∫ x, (g : Ω → ℝ) x ∂π := by
  rw [real_inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_const (1 : ℝ) (μ := π) (p := 2)).coeFn_toLp] with y hy
  rw [show ((oneLp π : Lp ℝ 2 π) : Ω → ℝ) y = (1 : ℝ) from hy, mul_one]

end Mean

/-- **One time slab on `L²(π)`**: a probability space, and a symmetric positivity-preserving operator
on `L²(π)` fixing the constant. -/
structure SlabM where
  Ω : Type
  [ms : MeasurableSpace Ω]
  π : Measure Ω
  [prob : IsProbabilityMeasure π]
  P : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π
  symm : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v)
  fix : P (oneLp π) = oneLp π
  pos : ∀ f : Lp ℝ 2 π, 0 ≤ᵐ[π] (f : Ω → ℝ) → 0 ≤ᵐ[π] ((P f : Lp ℝ 2 π) : Ω → ℝ)

attribute [instance] SlabM.ms SlabM.prob

namespace SlabM

variable (S : SlabM)

/-- **The `L²(π)` contraction on mean-zero functions.** -/
def ContrM (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ g : Lp ℝ 2 S.π, ∫ x, (g : S.Ω → ℝ) x ∂S.π = 0 → ‖S.P g‖ ≤ r * ‖g‖

theorem contrM_iff (r : ℝ) : S.ContrM r ↔ ContrH S.P (oneLp S.π) r := by
  simp only [ContrM, ContrH, inner_oneLp]

/-- The maximal correlation across the slab: the least `L²(π)` rate on mean-zero functions. -/
def rho : ℝ := rhoH S.P (oneLp S.π)

theorem rho_nonneg : 0 ≤ S.rho := rhoH_nonneg _ _

theorem contrM_rho : S.ContrM S.rho := (S.contrM_iff _).2 (contrH_rhoH _ _)

variable {S} in
theorem rho_le {r : ℝ} (h : S.ContrM r) : S.rho ≤ r := rhoH_le ((S.contrM_iff r).1 h)

variable {S} in
theorem ContrM.mono {r s : ℝ} (h : S.ContrM r) (hrs : r ≤ s) : S.ContrM s :=
  (S.contrM_iff s).2 (((S.contrM_iff r).1 h).mono hrs)

/-- **Stationarity**: `∫ P g dπ = ∫ g dπ`. -/
theorem stat (g : Lp ℝ 2 S.π) :
    ∫ x, ((S.P g : Lp ℝ 2 S.π) : S.Ω → ℝ) x ∂S.π = ∫ x, (g : S.Ω → ℝ) x ∂S.π := by
  rw [← inner_oneLp, ← inner_oneLp, S.symm, S.fix]

theorem symm_pow (n : ℕ) :
    ∀ u v : Lp ℝ 2 S.π, inner ℝ ((S.P ^ n) u) v = inner ℝ u ((S.P ^ n) v) := by
  induction n with
  | zero => intro u v; simp
  | succ n ih =>
    intro u v
    rw [pow_succ_apply, S.symm, ih, pow_succ_apply']

theorem fix_pow (n : ℕ) : (S.P ^ n) (oneLp S.π) = oneLp S.π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ_apply, ih, S.fix]

theorem pos_pow (n : ℕ) (f : Lp ℝ 2 S.π) (hf : 0 ≤ᵐ[S.π] (f : S.Ω → ℝ)) :
    0 ≤ᵐ[S.π] (((S.P ^ n) f : Lp ℝ 2 S.π) : S.Ω → ℝ) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [pow_succ_apply]; exact S.pos _ ih

/-- **The slab of `n` steps**: `(π, Pⁿ)`. -/
def pow (n : ℕ) : SlabM where
  Ω := S.Ω
  π := S.π
  P := S.P ^ n
  symm := S.symm_pow n
  fix := S.fix_pow n
  pos := S.pos_pow n

/-- **The rate of `n ≥ 1` steps is the `n`-th power of the one-step rate.** -/
theorem rho_pow {n : ℕ} (hn : 1 ≤ n) : (S.pow n).rho = S.rho ^ n :=
  rhoH_pow S.symm S.fix hn

end SlabM

/-- **The box gap reads the slab** (measure form of `RelativeGap.ReadsSlab`). -/
def ReadsSlabM (gL : ℕ → ℕ → ℝ) (S : ℕ → ℕ → SlabM) (τ : ℕ → ℝ) : Prop :=
  ∀ m, 0 < m → 0 < τ m ∧ ∀ k r, 0 < r → (S m k).ContrM r → -Real.log r / τ m ≤ gL m k

/-- **(A_L²) on `L²(π)`** (measure form of `RelativeGap.RelFloor`). -/
def RelFloorM (S : ℕ → ℕ → SlabM) (ρ : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ m, 0 < m → 0 < ρ m ∧ ρ m < 1 ∧ ∀ k, K m ≤ k → (S m k).rho ≤ ρ m

/-- The gap per unit physical time read from the slab. -/
def relGapM (S : ℕ → ℕ → SlabM) (τ : ℕ → ℝ) (m k : ℕ) : ℝ := -Real.log (S m k).rho / τ m

/-- **The gap `−log ρ / τ` reads the slab** when every rate is positive. -/
theorem readsSlabM_relGap {S : ℕ → ℕ → SlabM} {τ : ℕ → ℝ} (hτ : ∀ m, 0 < m → 0 < τ m)
    (hρ : ∀ m k, 0 < m → 0 < (S m k).rho) : ReadsSlabM (relGapM S τ) S τ := by
  intro m hm
  refine ⟨hτ m hm, fun k r _ hc => ?_⟩
  have hlog : Real.log (S m k).rho ≤ Real.log r := Real.log_le_log (hρ m k hm) (SlabM.rho_le hc)
  exact div_le_div_of_nonneg_right (by linarith) (hτ m hm).le

/-- **(A_L²) gives (A)** on `L²(π)`: the measure form of
`RelativeGap.fixedApertureFloor_of_relFloor`. -/
theorem fixedApertureFloor_of_relFloorM {gL : ℕ → ℕ → ℝ} {rLat : ℕ → ℝ} {S : ℕ → ℕ → SlabM}
    {τ ρ : ℕ → ℝ} {K : ℕ → ℕ} {R : ℝ} (hS : ReadsSlabM gL S τ) (hA : RelFloorM S ρ K)
    (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) :
    FixedApertureFloor gL rLat (MassGap.RelativeGap.relValue ρ τ R) K := by
  intro m hm0
  obtain ⟨hρ0, hρ1, hk⟩ := hA m hm0
  obtain ⟨hτ, hg⟩ := hS m hm0
  have hlog : 0 < -Real.log (ρ m) := neg_pos.2 (Real.log_neg hρ0 hρ1)
  have hm : 0 < -Real.log (ρ m) / τ m := div_pos hlog hτ
  refine ⟨div_pos hm hR, fun k hkK => ?_⟩
  have hc : (S m k).ContrM (ρ m) := ((S m k).contrM_rho).mono (hk k hkK)
  have hgk : -Real.log (ρ m) / τ m ≤ gL m k := hg k (ρ m) hρ0 hc
  obtain ⟨hr0, hrR⟩ := hr k
  show -Real.log (ρ m) / τ m / R ≤ gL m k / rLat k
  calc -Real.log (ρ m) / τ m / R ≤ -Real.log (ρ m) / τ m / rLat k :=
        div_le_div_of_nonneg_left hm.le hr0 hrR
    _ ≤ gL m k / rLat k := div_le_div_of_nonneg_right hgk hr0.le

/-! ## 3. The Doob slab of a positive kernel -/

/-- **A positive symmetric kernel with a strictly positive eigenfunction.** -/
structure PerronKernel where
  X : Type
  [ms : MeasurableSpace X]
  μ : Measure X
  [prob : IsProbabilityMeasure μ]
  k : X → X → ℝ
  C : ℝ
  hk : Measurable (Function.uncurry k)
  hC0 : 0 ≤ C
  hkb : ∀ x y, |k x y| ≤ C
  symm : ∀ x y, k x y = k y x
  nonneg : ∀ x y, 0 ≤ k x y
  φ : X → ℝ
  φ_meas : Measurable φ
  c : ℝ
  c_pos : 0 < c
  φ_lower : ∀ x, c ≤ φ x
  φ_sq : ∫ x, φ x ^ 2 ∂μ = 1
  lam0 : ℝ
  lam0_pos : 0 < lam0
  eig : ∀ z, ∫ y, k z y * φ y ∂μ = lam0 * φ z

attribute [instance] PerronKernel.ms PerronKernel.prob

namespace PerronKernel

variable (P : PerronKernel)

theorem φ_pos (x : P.X) : 0 < P.φ x := P.c_pos.trans_le (P.φ_lower x)

/-- The operator of the kernel on `L²(μ)`. -/
def K : Lp ℝ 2 P.μ →L[ℝ] Lp ℝ 2 P.μ := kernelCLM P.k P.C P.hk P.hC0 P.hkb P.μ P.μ

/-- The density `φ²`. -/
def dens (x : P.X) : ℝ≥0 := Real.toNNReal (P.φ x ^ 2)

theorem dens_meas : Measurable P.dens := (P.φ_meas.pow_const 2).real_toNNReal

theorem coe_dens (x : P.X) : (P.dens x : ℝ) = P.φ x ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)

/-- **The stationary measure** `π = φ² μ`. -/
def piD : Measure P.X := P.μ.withDensity fun x => (P.dens x : ℝ≥0∞)

theorem integral_piD (g : P.X → ℝ) : ∫ x, g x ∂P.piD = ∫ x, P.φ x ^ 2 * g x ∂P.μ := by
  rw [piD, integral_withDensity_eq_integral_smul P.dens_meas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show P.dens x • g x = P.φ x ^ 2 * g x
  rw [NNReal.smul_def, smul_eq_mul, coe_dens]

theorem integrable_piD_iff (g : P.X → ℝ) :
    Integrable g P.piD ↔ Integrable (fun x => P.φ x ^ 2 * g x) P.μ := by
  rw [piD, integrable_withDensity_iff_integrable_smul P.dens_meas]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  show P.dens x • g x = P.φ x ^ 2 * g x
  rw [NNReal.smul_def, smul_eq_mul, coe_dens]

instance isProbabilityMeasure_piD : IsProbabilityMeasure P.piD := by
  constructor
  have hfun : (fun x => (P.dens x : ℝ)) = fun x => P.φ x ^ 2 := funext P.coe_dens
  have hint : Integrable (fun x => (P.dens x : ℝ)) P.μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hfun, P.φ_sq]
    exact one_ne_zero
  rw [piD, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral _ hint, hfun, P.φ_sq, ENNReal.ofReal_one]

theorem ac : P.μ ≪ P.piD := by
  refine withDensity_absolutelyContinuous' P.dens_meas.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine ENNReal.coe_ne_zero.2 fun h => ?_
  have := Real.toNNReal_eq_zero.1 (show Real.toNNReal (P.φ x ^ 2) = 0 from h)
  have := pow_pos (P.φ_pos x) 2
  linarith

/-- The Doob kernel against `π`: `k(x,y) / (λ₀ φ(x) φ(y))`. -/
def kPi (x y : P.X) : ℝ := P.k x y / (P.lam0 * P.φ x * P.φ y)

/-- Its bound `C / (λ₀ c²)`. -/
def CPi : ℝ := P.C / (P.lam0 * P.c ^ 2)

theorem CPi_nonneg : 0 ≤ P.CPi := div_nonneg P.hC0 (by have := P.lam0_pos; have := P.c_pos; positivity)

theorem kPi_meas : Measurable (Function.uncurry P.kPi) := by
  show Measurable fun p : P.X × P.X => P.k p.1 p.2 / (P.lam0 * P.φ p.1 * P.φ p.2)
  exact P.hk.div ((measurable_const.mul (P.φ_meas.comp measurable_fst)).mul
    (P.φ_meas.comp measurable_snd))

theorem kPi_bound (x y : P.X) : |P.kPi x y| ≤ P.CPi := by
  have hx := P.φ_pos x
  have hy := P.φ_pos y
  have hl := P.lam0_pos
  have hc := P.c_pos
  have hden : 0 < P.lam0 * P.φ x * P.φ y := by positivity
  have hcc : P.c * P.c ≤ P.φ x * P.φ y :=
    mul_le_mul (P.φ_lower x) (P.φ_lower y) hc.le hx.le
  have hge : P.lam0 * P.c ^ 2 ≤ P.lam0 * P.φ x * P.φ y := by nlinarith
  rw [kPi, CPi, abs_div, abs_of_pos hden]
  exact div_le_div₀ P.hC0 (P.hkb x y) (by positivity) hge

theorem kPi_symm (x y : P.X) : P.kPi x y = P.kPi y x := by
  unfold kPi; rw [P.symm x y]; ring

theorem kPi_nonneg (x y : P.X) : 0 ≤ P.kPi x y :=
  div_nonneg (P.nonneg x y) (by have := P.φ_pos x; have := P.φ_pos y; have := P.lam0_pos; positivity)

/-- The Doob kernel acting: `∫ kPi(x,y) g(y) dπ(y) = (λ₀ φ(x))⁻¹ ∫ k(x,y) φ(y) g(y) dμ(y)`. -/
theorem kernelFun_kPi (g : P.X → ℝ) (x : P.X) :
    kernelFun P.kPi P.piD g x = (P.lam0 * P.φ x)⁻¹ * ∫ y, P.k x y * (P.φ y * g y) ∂P.μ := by
  unfold kernelFun
  rw [integral_piD, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have := P.φ_pos x
  have := P.φ_pos y
  have := P.lam0_pos
  show P.φ y ^ 2 * (P.k x y / (P.lam0 * P.φ x * P.φ y) * g y)
    = (P.lam0 * P.φ x)⁻¹ * (P.k x y * (P.φ y * g y))
  field_simp

theorem stochastic : KernelStochastic P.kPi P.piD := by
  intro x
  have h := P.kernelFun_kPi (fun _ => 1) x
  unfold kernelFun at h
  simp only [mul_one] at h
  rw [h, P.eig x]
  have := P.φ_pos x
  have := P.lam0_pos
  field_simp

/-- **The Doob operator** on `L²(π)`. -/
def PD : Lp ℝ 2 P.piD →L[ℝ] Lp ℝ 2 P.piD :=
  kernelCLM P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD P.piD

theorem PD_symm (u v : Lp ℝ 2 P.piD) : inner ℝ (P.PD u) v = inner ℝ u (P.PD v) :=
  (isSelfAdjoint_kernelCLM_of_symm P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD
    P.kPi_symm).isSymmetric u v

/-- The Doob density `kD(x,y) = k(x,y) φ(y) / (λ₀ φ(x))` with respect to `μ`. -/
def kD (x y : P.X) : ℝ := P.k x y * P.φ y / (P.lam0 * P.φ x)

/-- **The Doob operator is given by the density `kD` against `μ`.** -/
theorem PD_density (g : Lp ℝ 2 P.piD) :
    ((P.PD g : Lp ℝ 2 P.piD) : P.X → ℝ) =ᵐ[P.piD]
      fun x => ∫ y, P.kD x y * (g : P.X → ℝ) y ∂P.μ := by
  filter_upwards [coeFn_kernelCLM P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD P.piD g]
    with x hx
  rw [PD, hx, kernelFun_kPi, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have := P.φ_pos x
  have := P.lam0_pos
  show (P.lam0 * P.φ x)⁻¹ * (P.k x y * (P.φ y * (g : P.X → ℝ) y))
    = P.k x y * P.φ y / (P.lam0 * P.φ x) * (g : P.X → ℝ) y
  field_simp

/-- `PD 1 = 1`. -/
theorem PD_fix : P.PD (oneLp P.piD) = oneLp P.piD :=
  kernelCLM_oneLp_eq_oneLp P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD P.piD P.stochastic

/-- **The Doob slab**: `(π, PD)`. -/
def doob : SlabM where
  Ω := P.X
  π := P.piD
  P := P.PD
  symm := P.PD_symm
  fix := P.PD_fix
  pos := kernelCLM_nonneg P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD P.piD P.kPi_nonneg

/-! ### The ground-state map `U g = φ g` -/

theorem memU (g : Lp ℝ 2 P.piD) : MemLp (fun x => P.φ x * (g : P.X → ℝ) x) 2 P.μ := by
  refine (memLp_two_iff_integrable_sq
    (P.φ_meas.mul (Lp.stronglyMeasurable g).measurable).aestronglyMeasurable).2 ?_
  have h := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  rw [integrable_piD_iff] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show P.φ x ^ 2 * (g : P.X → ℝ) x ^ 2 = (P.φ x * (g : P.X → ℝ) x) ^ 2
  ring

/-- `U g = φ g`, from `L²(π)` to `L²(μ)`. -/
def U (g : Lp ℝ 2 P.piD) : Lp ℝ 2 P.μ := (P.memU g).toLp _

theorem coeFn_U (g : Lp ℝ 2 P.piD) :
    ((P.U g : Lp ℝ 2 P.μ) : P.X → ℝ) =ᵐ[P.μ] fun x => P.φ x * (g : P.X → ℝ) x :=
  (P.memU g).coeFn_toLp

/-- **`U` is isometric**: `⟪U f, U g⟫ = ⟪f, g⟫`. -/
theorem inner_U (f g : Lp ℝ 2 P.piD) : inner ℝ (P.U f) (P.U g) = inner ℝ f g := by
  rw [real_inner_Lp, real_inner_Lp, integral_piD]
  refine integral_congr_ae ?_
  filter_upwards [P.coeFn_U f, P.coeFn_U g] with x h1 h2
  rw [h1, h2]; ring

theorem norm_U (g : Lp ℝ 2 P.piD) : ‖P.U g‖ = ‖g‖ := by
  have h : ‖P.U g‖ ^ 2 = ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_U]
  rw [← Real.sqrt_sq (norm_nonneg (P.U g)), h, Real.sqrt_sq (norm_nonneg g)]

theorem memV (h : Lp ℝ 2 P.μ) : MemLp (fun x => (h : P.X → ℝ) x / P.φ x) 2 P.piD := by
  refine (memLp_two_iff_integrable_sq
    ((Lp.stronglyMeasurable h).measurable.div P.φ_meas).aestronglyMeasurable).2 ?_
  rw [integrable_piD_iff]
  have h2 := (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  have := (P.φ_pos x).ne'
  show (h : P.X → ℝ) x ^ 2 = P.φ x ^ 2 * ((h : P.X → ℝ) x / P.φ x) ^ 2
  field_simp

/-- `V h = h / φ`, from `L²(μ)` to `L²(π)`. -/
def V (h : Lp ℝ 2 P.μ) : Lp ℝ 2 P.piD := (P.memV h).toLp _

/-- **`U` is onto**: `U (V h) = h`. -/
theorem U_V (h : Lp ℝ 2 P.μ) : P.U (P.V h) = h := by
  refine Lp.ext ?_
  filter_upwards [P.coeFn_U (P.V h), P.ac.ae_eq (P.memV h).coeFn_toLp] with x h1 h2
  rw [h1]
  have h2' : ((P.V h : Lp ℝ 2 P.piD) : P.X → ℝ) x = (h : P.X → ℝ) x / P.φ x := h2
  rw [h2']
  have := (P.φ_pos x).ne'
  field_simp

/-- **The transfer form under `U`**: `⟪U g, K (U g)⟫ = λ₀ ⟪g, PD g⟫`. -/
theorem inner_U_K (g : Lp ℝ 2 P.piD) :
    inner ℝ (P.U g) (P.K (P.U g)) = P.lam0 * inner ℝ g (P.PD g) := by
  set J : P.X → ℝ := fun x => ∫ y, P.k x y * (P.φ y * (g : P.X → ℝ) y) ∂P.μ with hJ
  have hKU : ∀ x, kernelFun P.k P.μ ((P.U g : Lp ℝ 2 P.μ) : P.X → ℝ) x = J x := by
    intro x
    unfold kernelFun
    refine integral_congr_ae ?_
    filter_upwards [P.coeFn_U g] with y hy
    rw [hy]
  have hL : inner ℝ (P.U g) (P.K (P.U g))
      = ∫ x, P.φ x * (g : P.X → ℝ) x * J x ∂P.μ := by
    rw [real_inner_Lp]
    refine integral_congr_ae ?_
    filter_upwards [P.coeFn_U g,
      coeFn_kernelCLM P.k P.C P.hk P.hC0 P.hkb P.μ P.μ (P.U g)] with x h1 h2
    rw [h1, K, h2, hKU]
  have hR : inner ℝ g (P.PD g)
      = ∫ x, P.φ x ^ 2 * ((g : P.X → ℝ) x * ((P.lam0 * P.φ x)⁻¹ * J x)) ∂P.μ := by
    rw [real_inner_Lp, ← integral_piD]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_kernelCLM P.kPi P.CPi P.kPi_meas P.CPi_nonneg P.kPi_bound P.piD P.piD g]
      with x hx
    rw [PD, hx, kernelFun_kPi]
  rw [hL, hR, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have := (P.φ_pos x).ne'
  have := P.lam0_pos.ne'
  show P.φ x * (g : P.X → ℝ) x * J x
    = P.lam0 * (P.φ x ^ 2 * ((g : P.X → ℝ) x * ((P.lam0 * P.φ x)⁻¹ * J x)))
  field_simp

/-- **The Perron vector** `φ` in `L²(μ)`: `U 1`. -/
def phiL : Lp ℝ 2 P.μ := P.U (oneLp P.piD)

theorem coeFn_phiL : ((P.phiL : Lp ℝ 2 P.μ) : P.X → ℝ) =ᵐ[P.μ] P.φ := by
  filter_upwards [P.coeFn_U (oneLp P.piD),
    P.ac.ae_eq (memLp_const (1 : ℝ) (μ := P.piD) (p := 2)).coeFn_toLp] with x h1 h2
  rw [phiL, h1]
  have h2' : ((oneLp P.piD : Lp ℝ 2 P.piD) : P.X → ℝ) x = 1 := h2
  rw [h2', mul_one]

/-- `K φ = λ₀ φ` in `L²(μ)`. -/
theorem K_phiL : P.K P.phiL = P.lam0 • P.phiL := by
  refine Lp.ext ?_
  filter_upwards [coeFn_kernelCLM P.k P.C P.hk P.hC0 P.hkb P.μ P.μ P.phiL,
    Lp.coeFn_smul P.lam0 P.phiL, P.coeFn_phiL] with x h1 h2 h3
  rw [K, h1, h2, Pi.smul_apply, h3, smul_eq_mul, ← P.eig x]
  unfold kernelFun
  refine integral_congr_ae ?_
  filter_upwards [P.coeFn_phiL] with y hy
  rw [hy]

theorem inner_U_phiL (g : Lp ℝ 2 P.piD) :
    inner ℝ (P.U g) P.phiL = ∫ x, (g : P.X → ℝ) x ∂P.piD := by
  rw [phiL, inner_U, inner_oneLp]

/-- **`λ₁`**: the top of the Rayleigh quotient of `K` on `φ⊥` in `L²(μ)`. -/
def lam1 : ℝ := lam1H P.K P.phiL

/-- **The one-step `L²(π)` rate of the Doob slab.** -/
def ratio : ℝ := P.doob.rho

/-- **`λ₁(PD) = λ₁/λ₀`.** -/
theorem lam1H_PD : lam1H P.PD (oneLp P.piD) = P.lam1 / P.lam0 := by
  have hl := P.lam0_pos
  apply le_antisymm
  · refine lam1H_le ⟨div_nonneg lam1H_nonneg hl.le, fun g hg => ?_⟩
    have hUg : inner ℝ (P.U g) P.phiL = 0 := by rw [inner_U_phiL, ← inner_oneLp, hg]
    have h1 := lam1H_spec (P := P.K) (P.U g) hUg
    rw [inner_U_K, norm_U] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hl]
    change P.lam0 * inner ℝ g (P.PD g) ≤ P.lam1 * ‖g‖ ^ 2 at h1
    linarith
  · have hmem : P.lam0 * lam1H P.PD (oneLp P.piD) ∈ raySetH P.K P.phiL := by
      refine ⟨mul_nonneg hl.le lam1H_nonneg, fun h hh => ?_⟩
      have hV : inner ℝ (P.V h) (oneLp P.piD) = 0 := by
        rw [← P.inner_U, P.U_V h]; exact hh
      have h1 := lam1H_spec (P := P.PD) (P.V h) hV
      have e1 := P.inner_U_K (P.V h)
      rw [P.U_V h] at e1
      have e2 := P.norm_U (P.V h)
      rw [P.U_V h] at e2
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left h1 hl.le
      linarith
    have := lam1H_le hmem
    rw [div_le_iff₀ hl, mul_comm]
    exact this

/-- **`λ₁/λ₀ ≤ ratio`**, with no semidefiniteness. -/
theorem lam1_div_le_ratio : P.lam1 / P.lam0 ≤ P.ratio := by
  rw [← lam1H_PD]; exact lam1H_le_rhoH

/-- The form of `PD` is nonnegative on mean-zero functions when that of `K` is on `φ⊥`. -/
theorem psd_PD (hpsd : ∀ h : Lp ℝ 2 P.μ, inner ℝ h P.phiL = 0 → 0 ≤ inner ℝ h (P.K h))
    (g : Lp ℝ 2 P.piD) (hg : inner ℝ g (oneLp P.piD) = 0) : 0 ≤ inner ℝ g (P.PD g) := by
  have hUg : inner ℝ (P.U g) P.phiL = 0 := by rw [inner_U_phiL, ← inner_oneLp, hg]
  have h1 := hpsd _ hUg
  rw [inner_U_K] at h1
  nlinarith [P.lam0_pos]

/-- **The one-step rate is `λ₁/λ₀`** when `K` is semidefinite on `φ⊥`. -/
theorem ratio_eq (hpsd : ∀ h : Lp ℝ 2 P.μ, inner ℝ h P.phiL = 0 → 0 ≤ inner ℝ h (P.K h)) :
    P.ratio = P.lam1 / P.lam0 := by
  rw [← lam1H_PD]
  exact rhoH_eq_lam1H P.PD_symm P.PD_fix (P.psd_PD hpsd)

/-- **The Doob slab of `n` steps.** -/
def slab (n : ℕ) : SlabM := P.doob.pow n

/-- **The rate of the slab of `n ≥ 1` steps is `ratioⁿ`.** -/
theorem rho_slab {n : ℕ} (hn : 1 ≤ n) : (P.slab n).rho = P.ratio ^ n := P.doob.rho_pow hn

theorem ratio_nonneg : 0 ≤ P.ratio := P.doob.rho_nonneg

/-- `ratio > 0` when the form of `K` is positive at some `h ⊥ φ`. -/
theorem ratio_pos_of_form_pos {h : Lp ℝ 2 P.μ} (hh : inner ℝ h P.phiL = 0)
    (hp : 0 < inner ℝ h (P.K h)) : 0 < P.ratio := by
  have h1 := lam1H_spec (P := P.K) h hh
  have hl : 0 < P.lam1 := by
    by_contra hle
    push Not at hle
    have h0 : P.lam1 = 0 := le_antisymm hle (lam1H_nonneg (P := P.K) (e := P.phiL))
    have h1' : inner ℝ h (P.K h) ≤ P.lam1 * ‖h‖ ^ 2 := h1
    rw [h0, zero_mul] at h1'
    linarith
  exact (div_pos hl P.lam0_pos).trans_le P.lam1_div_le_ratio

/-- The gap per unit time of one step of length `a`: `−log ratio / a`. -/
def boxGap (a : ℝ) : ℝ := -Real.log P.ratio / a

/-- **The gap read from the slab is the box gap**: `−log ρ_slab / (n a) = −log ratio / a`. -/
theorem relGap_slab {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    -Real.log (P.slab n).rho / (n * a) = P.boxGap a := by
  rw [P.rho_slab hn, Real.log_pow, boxGap]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- **One slab reads the box gap**: every rate `r` of the slab of `n ≥ 1` steps of length `a > 0` has
`−log r / (n a) ≤ −log ratio / a`, when `ratio > 0`. -/
theorem le_boxGap_of_contr {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (hpos : 0 < P.ratio)
    {r : ℝ} (hc : (P.slab n).ContrM r) : -Real.log r / (n * a) ≤ P.boxGap a := by
  have hle : P.ratio ^ n ≤ r := by rw [← P.rho_slab hn]; exact SlabM.rho_le hc
  have hlog : Real.log (P.ratio ^ n) ≤ Real.log r := Real.log_le_log (pow_pos hpos n) hle
  rw [← P.relGap_slab hn ha, P.rho_slab hn]
  have hna : 0 < (n : ℝ) * a := mul_pos (by exact_mod_cast (by omega : 0 < n)) ha
  exact div_le_div_of_nonneg_right (by linarith) hna.le

end PerronKernel

/-- **`ReadsSlabM` for a family of positive kernels**: at aperture `m` and zoom `k`, the Doob slab of
`n m k ≥ 1` steps of `T m k`, of thickness `τ m = n m k · a_k`, with `ratio > 0`. -/
theorem readsSlabM_transfer (T : ℕ → ℕ → PerronKernel) {a₀ : ℝ} (ha : 0 < a₀) (n : ℕ → ℕ → ℕ)
    (τ : ℕ → ℝ) (hn : ∀ m k, 0 < m → 1 ≤ n m k)
    (hτ : ∀ m k, 0 < m → (n m k : ℝ) * aZ a₀ k = τ m)
    (hpos : ∀ m k, 0 < m → 0 < (T m k).ratio) :
    ReadsSlabM (fun m k => (T m k).boxGap (aZ a₀ k)) (fun m k => (T m k).slab (n m k)) τ := by
  intro m hm
  refine ⟨?_, fun k r _ hc => ?_⟩
  · rw [← hτ m 0 hm]
    exact mul_pos (by exact_mod_cast (by have := hn m 0 hm; omega : 0 < n m 0)) (aZ_pos ha 0)
  · rw [← hτ m k hm]
    exact (T m k).le_boxGap_of_contr (hn m k hm) (aZ_pos ha k) (hpos m k hm) hc

/-- **The slab across the whole periodic side**: `τ m = L_m = m a₀`, `n m k = m 2ᵏ` steps. -/
theorem readsSlabM_box (T : ℕ → ℕ → PerronKernel) {a₀ : ℝ} (ha : 0 < a₀)
    (hpos : ∀ m k, 0 < m → 0 < (T m k).ratio) :
    ReadsSlabM (fun m k => (T m k).boxGap (aZ a₀ k)) (fun m k => (T m k).slab (m * 2 ^ k))
      (LA a₀) := by
  refine readsSlabM_transfer T ha (fun m k => m * 2 ^ k) (LA a₀) (fun m k hm => ?_)
    (fun m k _ => ?_) hpos
  · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ two_ne_zero))
  · simp only [aZ, LA]
    push_cast
    field_simp

/-! ## 4. Wilson -/

section Wilson

open MassGap.RectTransfer MassGap.RectWilson MassGap.JentzschKT

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- **The Perron kernel of the Wilson slice transfer** `kT μ T N β` (`N ≠ 0`, `β ≥ 0`), with the
eigenfunction of `JentzschKT.exists_pos_eigen_kT` and `λ₀ = ‖kernelCLM kT‖`. -/
def perronKT (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (hN : N ≠ 0) (β : ℝ)
    (hβ : 0 ≤ β) : PerronKernel :=
  have h := (exists_pos_eigen_kT (μ := μ) (T := T) hN hβ).2
  { X := SpT μ T → MassGap.SUN.SU N
    μ := hS μ T N
    k := kT μ T N β
    C := 1
    hk := (continuous_kT β).measurable
    hC0 := zero_le_one
    hkb := abs_kT_le hN hβ
    symm := kT_symm β
    nonneg := fun x y => (kTmin_pos β).le.trans (kT_lower hN hβ x y)
    φ := h.choose
    φ_meas := h.choose_spec.1
    c := h.choose_spec.2.2.1.choose
    c_pos := h.choose_spec.2.2.1.choose_spec.1
    φ_lower := h.choose_spec.2.2.1.choose_spec.2
    φ_sq := h.choose_spec.2.2.2.1
    lam0 := ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
      (hS μ T N) (hS μ T N)‖
    lam0_pos := (exists_pos_eigen_kT (μ := μ) (T := T) hN hβ).1
    eig := h.choose_spec.2.2.2.2 }

theorem perronKT_K (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    (perronKT μ T N hN β hβ).K = kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
      (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) := rfl

theorem perronKT_lam0 (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    (perronKT μ T N hN β hβ).lam0 = ‖(perronKT μ T N hN β hβ).K‖ := rfl

/-- **`ReadsSlabM` for the Wilson slice transfer**: for transverse extents `T m k` and couplings
`β m k ≥ 0`, the box gap `−log ratio / a_k` reads the Doob slab of `m 2ᵏ` steps (thickness `L_m`),
when every one-step rate is positive. -/
theorem readsSlabM_wilson (μ : Fin 4) (T : ℕ → ℕ → {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) (hN : N ≠ 0)
    (β : ℕ → ℕ → ℝ) (hβ : ∀ m k, 0 ≤ β m k) {a₀ : ℝ} (ha : 0 < a₀)
    (hpos : ∀ m k, 0 < m → 0 < (perronKT μ (T m k) N hN (β m k) (hβ m k)).ratio) :
    ReadsSlabM (fun m k => (perronKT μ (T m k) N hN (β m k) (hβ m k)).boxGap (aZ a₀ k))
      (fun m k => (perronKT μ (T m k) N hN (β m k) (hβ m k)).slab (m * 2 ^ k)) (LA a₀) :=
  readsSlabM_box (fun m k => perronKT μ (T m k) N hN (β m k) (hβ m k)) ha hpos

/-- **The (A)-chain on the Wilson box**: `RelFloorM` for the Wilson Doob slabs, the reading of the
slab and an observer reading in `(0, R]` give `FixedApertureFloor` for the box gap
`−log ratio / a_k`. -/
theorem fixedApertureFloor_wilson (μ : Fin 4) (T : ℕ → ℕ → {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ)
    (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (hβ : ∀ m k, 0 ≤ β m k) {a₀ : ℝ} (ha : 0 < a₀)
    (hpos : ∀ m k, 0 < m → 0 < (perronKT μ (T m k) N hN (β m k) (hβ m k)).ratio)
    {rLat : ℕ → ℝ} {ρ : ℕ → ℝ} {K : ℕ → ℕ} {R : ℝ}
    (hA : RelFloorM (fun m k => (perronKT μ (T m k) N hN (β m k) (hβ m k)).slab (m * 2 ^ k)) ρ K)
    (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) :
    FixedApertureFloor (fun m k => (perronKT μ (T m k) N hN (β m k) (hβ m k)).boxGap (aZ a₀ k))
      rLat (MassGap.RelativeGap.relValue ρ (LA a₀) R) K :=
  fixedApertureFloor_of_relFloorM (readsSlabM_wilson μ T N hN β hβ ha hpos) hA hR hr

/-- **The Wilson one-step rate is `λ₁/λ₀`** when `kT` is semidefinite on `φ⊥` in `L²(Haar)`. -/
theorem ratio_eq_wilson (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (hpsd : ∀ h : Lp ℝ 2 (hS μ T N), inner ℝ h (perronKT μ T N hN β hβ).phiL = 0 →
      0 ≤ inner ℝ h (kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable zero_le_one
        (abs_kT_le hN hβ) (hS μ T N) (hS μ T N) h)) :
    (perronKT μ T N hN β hβ).ratio
      = (perronKT μ T N hN β hβ).lam1 / ‖kernelCLM (kT μ T N β) 1 (continuous_kT β).measurable
          zero_le_one (abs_kT_le hN hβ) (hS μ T N) (hS μ T N)‖ :=
  (perronKT μ T N hN β hβ).ratio_eq hpsd

end Wilson

#print axioms contrH_rhoH
#print axioms ContrH.pow
#print axioms rhoH_pow
#print axioms lam1H_spec
#print axioms lam1H_le_rhoH
#print axioms form_cs
#print axioms contrH_of_rayleigh
#print axioms rhoH_eq_lam1H
#print axioms inner_oneLp
#print axioms SlabM.contrM_iff
#print axioms SlabM.contrM_rho
#print axioms SlabM.stat
#print axioms SlabM.rho_pow
#print axioms readsSlabM_relGap
#print axioms fixedApertureFloor_of_relFloorM
#print axioms PerronKernel.isProbabilityMeasure_piD
#print axioms PerronKernel.stochastic
#print axioms PerronKernel.PD_density
#print axioms PerronKernel.doob
#print axioms PerronKernel.inner_U
#print axioms PerronKernel.U_V
#print axioms PerronKernel.inner_U_K
#print axioms PerronKernel.K_phiL
#print axioms PerronKernel.lam1H_PD
#print axioms PerronKernel.lam1_div_le_ratio
#print axioms PerronKernel.ratio_eq
#print axioms PerronKernel.rho_slab
#print axioms PerronKernel.ratio_pos_of_form_pos
#print axioms PerronKernel.relGap_slab
#print axioms PerronKernel.le_boxGap_of_contr
#print axioms readsSlabM_transfer
#print axioms readsSlabM_box
#print axioms perronKT
#print axioms readsSlabM_wilson
#print axioms fixedApertureFloor_wilson
#print axioms ratio_eq_wilson

end MassGap.SlabMeasure
