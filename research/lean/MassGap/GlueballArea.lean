import Mathlib
import MassGap.ObserverTheory
import MassGap.GapL2
import MassGap.ShortDistanceY
import MassGap.PolymerCount

/-!
# MassGap.GlueballArea — the zero-flux defect from a gap and a level count; what "loops cost area" gives

The open piece is `ObserverTheory.HiddenCostAt N σ A ℓ`: at every side `n` of physical length `n a ∈ [2ℓ, 5ℓ]`,
eventually in `β`, the zero-flux doubling defect `trivialDefectN N β n i = 2 log hs(trivKN) − log hs(trivKN ∗ trivKN)`
is at most `A e^{−σ n a}`. This module reduces it to two named statements about the levels of the zero-flux kernel
(a gap and a count), and then asks what a loop-gas bound gives for the count.

## 1. The doubling defect from an excited weight (proved)

* `defect_le_of_excited`: `g ≤ Z₁ ≤ g(1 + δ)` and `g² ≤ Z₂` give `2 log Z₁ − log Z₂ ≤ 2δ`. The proof is
  `GapL2.doubling_of_excited` at `T₁ = Z₁/g`, `T₂ = Z₂/g²`.
* `log_doubling_transport`: the logarithmic form of `GapL2.doubling_transport` for a finite reversible Markov kernel:
  `2 log trc(K^{2m+q}) − log trc(K^{4m+2q}) ≤ 2 s (trc(K^{2m}) − 1)` when `Contr π (K^q) s`. Its two inputs are the
  gap (`s`, through `GapL2.trace_transport`) and the level count (`trc(K^{2m}) − 1`). §2 is the same reduction for
  the zero-flux kernel, written in its levels.

## 2. The zero-flux kernel in its levels (defined; the reduction proved)

`t = n a` is the physical time extent of the side-`n` torus (`a = aRun N β`). `heatW g₀ E t j = e^{−(E_j − E_{g₀}) t}`
is the ground-normalised weight of level `j`.

* `ZeroFluxLevels N β n i g₀ E`: an orthonormal family of eigenfunctions of `trivKN` with eigenvalues `μ_j`,
  `μ_j² = e^{−E_j t}`, `E_{g₀} ≤ E_j`, that exhausts both traces: `hs(trivKN) = Σ_j e^{−E_j t}`,
  `hs(trivKN ∗ trivKN) = Σ_j e^{−2 E_j t}`. The eigen-equation ties `E` to the spectrum: a family reproducing the
  two traces without being eigenfunctions does not qualify, and by Bessel a family missing an eigenvalue cannot
  reach `hs`, so `ι` counts the nonzero eigenvalues with multiplicity. Existence of such a family is the
  Hilbert–Schmidt spectral theorem for the symmetric bounded kernel `trivKN`; it is not proved here (an input).
  Reading (argued): `trivKN` is the zero-flux part of `kT^{n/2}` (`halfKN` is the `n/2`-fold composite and the
  centre average commutes with composition of centre-invariant kernels; `ZeroFluxSector.zk_conv` is the case
  `a = b`), so for even `n`, `E_j = −log|κ_j| / a` with
  `κ_j` the zero-flux eigenvalues of the one-step transfer; for odd `n` the `E_j` are still defined by
  `μ_j² = e^{−E_j n a}` but are not those energies. `UniformGlueball` uses powers of two `n ≥ 2` only.
* `ZeroFluxGap g₀ E m`: every level other than `g₀` lies at least `m` above it (the gap clause; for `m > 0` it
  includes uniqueness of the zero-flux ground level).
* `ZeroFluxCount g₀ E t₀ C`: the normalised heat trace at the physical time `t₀` is summable and at most `1 + C`
  (the count clause: `Σ_{j ≠ g₀} e^{−(E_j − E_{g₀}) t₀} ≤ C`). For the spectral levels, summability at `t₀ ≥ n a`
  follows from `hs_trivKN_pos` (`β ≥ 0`) and comparison with the level at `t = n a`; at small `t₀` it is part of
  the clause. Measurability of each `φ_j` follows from `trivKN > 0` and the pointwise eigen-equation.
* `level_transport`: gap and count give `1 ≤ Σ_j heatW t ≤ 1 + C e^{−m (t − t₀)}` at every `t ≥ t₀`. This is the
  level form of `GapL2.trace_transport`: the gap carries the count from `t₀` to every longer time.
* **`trivialDefectN_le_of_levels`**: `ZeroFluxLevels`, `ZeroFluxGap m`, `ZeroFluxCount t₀ C` (`0 ≤ t₀ ≤ n a`) give
  `trivialDefectN N β n i ≤ 2 C e^{m t₀} e^{−m n a}`.
* `UniformGlueball N m t₀ C ℓ`: eventually in `β`, at every power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and
  every step `i`, the zero-flux kernel has spectral levels with gap `m` and count `(t₀, C)`; the same `m`, `t₀`,
  `C` at every `β` (uniform in the zoom).
* **`hiddenCostAt_of_uniformGlueball`**: `UniformGlueball N m t₀ C ℓ` with `0 ≤ t₀ ≤ 2ℓ` gives
  `ObserverTheory.HiddenCostAt N m (2 C e^{m t₀}) ℓ`.

So (T) follows from a gap and a count on the spectrum of the zero-flux kernel at the box, uniform in the zoom,
given the spectral theorem: the gap clause (`m`, "a glueball has a fixed mass") and the count clause (`C` at one
physical time `t₀`).

## 3. Loops cost area: the count clause from a loop gas (proved, conditional)

* `LoopEntropy size V K`: every finite family of loop configurations of lattice size `s` has at most `V Kˢ` members.
* `loopGas_finset_le`, `loopGas_tsum_le`: sizes `≥ 1`, `LoopEntropy size V K`, `V ≥ 0`, `K ≥ 0` and
  `q = K e^{−c} < 1` give `Σ_γ e^{−c·size γ} ≤ V q/(1 − q)` (entropy against energy).
* `LoopsCarry g₀ E t₀ c size p`: the excited levels are carried injectively by loop configurations `p j`, each
  costing `(E_j − E_{g₀}) t₀ ≥ c · size(p j)`.
* `count_of_loops`: `LoopsCarry` with a `LoopEntropy` bound gives `ZeroFluxCount g₀ E t₀ (V q/(1 − q))`.
* `count_of_area`: the energy form. An excitation carried by a configuration of `s` plaquettes lies at least
  `σ (s a)` above the ground (`σ a` per plaquette); its heat weight at time `t₀` is then at most `e^{−σ (s a) t₀}`,
  the tension times the area `(s a) · t₀` swept in time `t₀`. With `c = σ a t₀` the count clause holds with
  `C = V q/(1 − q)`, `q = K e^{−σ a t₀}`, provided `q < 1`.
* `q_lt_one_iff`: `q < 1 ↔ log K < σ a t₀` (`K > 0`).
* `loopEntropy_hypercubic`: on the periodic `dim`-dimensional lattice of extent `n`, the nonempty touch-connected
  plaquette sets (`LoopConf`) satisfy `LoopEntropy` with `V = |Plaq dim n| = dim² nᵈⁱᵐ` (`card_plaq`) and
  `K = (16 dim + 1)²` (`StrongCoupling.card_connSets_le_hypercubic`): `2401` at `dim = 3`, `4225` at `dim = 4`.
* `count_of_area_hypercubic`: the two combined.
* `finite_excited_of_loopsCarry`, `finite_excited_hypercubic`: an injective assignment into a finite type of
  configurations forces finitely many excited levels. `LoopConf dim n` is finite, so `count_of_area_hypercubic`
  applies only to finitely many levels. The spectral levels of `trivKN` are infinitely many (argued: the character
  expansion of the Wilson weight has infinitely many nonzero zero-`N`-ality coefficients for `β > 0`, so `kT`
  restricted to zero flux is not of finite rank), so for them the plaquette sets
  must be decorated (for instance by representation labels) and the decorated count needs its own entropy constant.

## 4. Where the loop-gas route fails at fine lattice

* `eventually_entropy_wins` (proved): for `N ≥ 1`, `K > 1`, `t₀ ≥ 0` and any tension `σ(β)` bounded above
  eventually, eventually in `β` the ratio is `q = K e^{−σ a t₀} > 1`, because `a = aRun N β → 0`
  (`ShortDistanceY.tendsto_aRun_nhdsGT_zero`).
* `not_eventually_area_beats_entropy` (proved): hence `q < 1` does not hold eventually in `β` for any such `σ`. The
  cost per plaquette at a fixed physical time is `σ a t₀ → 0`; the entropy per plaquette `log K` is fixed. The
  sufficient hypothesis of `count_of_area` with lattice-size configurations is consistent with the zoom only if
  `σ(β) a(β) t₀ > log K`, i.e. the tension in physical units grows like `1/a`. This shows the hypothesis fails, not
  that the count clause fails.
* `volume_le` (proved): at a side in the window, `(2ℓ/a)ᵈⁱᵐ ≤ nᵈⁱᵐ`, so the volume factor `V = dim² nᵈⁱᵐ` of
  `count_of_area_hypercubic` is at least `dim² (2ℓ/a)ᵈⁱᵐ`, unbounded as `a → 0`. Argued from it: since
  `C ≥ V q`, the constant is uniform in the zoom only if `q ≲ (a/ℓ)ᵈⁱᵐ`.

## What remains (argued, not proved)

(T) needs the gap clause and the count clause on the spectrum of the zero-flux kernel, uniformly in the zoom (§2).
"Loops are glueballs" is the gap clause. "Loops cost area" proves the count clause only when the cost per unit of
configuration size beats the entropy `log K` and the number of roots `V` is bounded. With configurations counted on
the lattice, the first fails as `a → 0` (proved, §4) and the second grows like `(L/a)ᵈⁱᵐ` (`volume_le`; the
consequence for `C` is argued). The statement that would make the route uniform is the same theorem with
configurations counted at a fixed physical resolution `b` (block size): `V = (L/b)ᵈⁱᵐ`, `K` the block-lattice
animal constant (with its decoration), and cost `σ b t₀` per block, all independent of `a`. That is the author's "finer
lattice only adds tiny loops that carry nothing across" in the form needed: the excited zero-flux levels are
carried injectively by decorated configurations on a fixed physical block lattice, each costing `σ b t₀` per block
(`LoopsCarry` at block resolution). This is a block-spin (renormalisation) statement about the Wilson measure; no
declaration constructs it.

DERIVED (module-wide): `2` in `2 log Z₁ − log Z₂` and `2t` is the doubling; `2δ` is `doubling_of_excited`'s;
`1` is the ground level's own weight `e^0`; `[2ℓ, 5ℓ]`, powers of two and `n ≥ 2` are `HiddenCostAt`'s window;
`16 dim + 1` and the square are `card_connSets_le_hypercubic`'s; `dim²` counts the ordered direction pairs of the
type `Plaq`, the degenerate diagonal pairs and both orientations included.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.GlueballArea

open Filter Topology Finset
open MassGap.KernelPower MassGap.SectorDefect MassGap.CentreSectorSeedN
open MassGap.AsymptoticScaling (aRun aRun_pos)

/-! ## 1. The doubling defect from an excited weight -/

/-- **The doubling defect from an excited weight**: `g ≤ Z₁ ≤ g(1 + δ)`, `g² ≤ Z₂` give
`2 log Z₁ − log Z₂ ≤ 2δ` (`GapL2.doubling_of_excited` at `Z₁/g`, `Z₂/g²`). -/
theorem defect_le_of_excited {Z₁ Z₂ g δ : ℝ} (hg : 0 < g) (h1lo : g ≤ Z₁) (h1 : Z₁ ≤ g * (1 + δ))
    (h2 : g ^ 2 ≤ Z₂) : 2 * Real.log Z₁ - Real.log Z₂ ≤ 2 * δ := by
  have hZ₁ : 0 < Z₁ := hg.trans_le h1lo
  have hg2 : 0 < g ^ 2 := pow_pos hg 2
  have hZ₂ : 0 < Z₂ := hg2.trans_le h2
  have hT₁ : |Z₁ / g - 1| ≤ δ := by
    have hlo : 1 ≤ Z₁ / g := (one_le_div hg).2 h1lo
    have hhi : Z₁ / g ≤ 1 + δ := by rw [div_le_iff₀ hg]; linarith
    rw [abs_le]; constructor <;> linarith
  have hT₂ : 1 ≤ Z₂ / g ^ 2 := (one_le_div hg2).2 h2
  have hd := GapL2.doubling_of_excited hT₁ hT₂
  have hpos : 0 < Real.exp (-(2 * δ)) * (Z₁ / g) ^ 2 :=
    mul_pos (Real.exp_pos _) (pow_pos (div_pos hZ₁ hg) 2)
  have hl := Real.log_le_log hpos hd
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos (div_pos hZ₁ hg) 2).ne', Real.log_exp,
    Real.log_pow, Real.log_div hZ₁.ne' hg.ne', Real.log_div hZ₂.ne' hg2.ne', Real.log_pow] at hl
  push_cast at hl
  linarith

section Finite

open GapL2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The logarithmic form of `GapL2.doubling_transport`**: for a finite reversible Markov kernel with
`Contr π (K^q) s`, `2 log trc(K^{2m+q}) − log trc(K^{2(2m+q)}) ≤ 2 s (trc(K^{2m}) − 1)`. -/
theorem log_doubling_transport {π : α → ℝ} {K : Matrix α α ℝ} {s : ℝ} (M : Markov π K)
    (hrev : Rev π K) (hπ : ∀ x, 0 < π x) (m q : ℕ) (h : Contr π (K ^ q) s) :
    2 * Real.log (trc (K ^ (2 * m + q))) - Real.log (trc (K ^ (2 * (2 * m + q))))
      ≤ 2 * (s * (trc (K ^ (2 * m)) - 1)) := by
  have hd := doubling_transport M hrev hπ m q h
  have hT₂ : 1 ≤ trc (K ^ (2 * (2 * m + q))) := one_le_trace_even M hrev hπ _
  have hτ : 0 ≤ trc (K ^ (2 * m)) - 1 := by linarith [one_le_trace_even M hrev hπ m]
  have hx : 0 ≤ s * (trc (K ^ (2 * m)) - 1) := mul_nonneg h.1 hτ
  have hlog2 : 0 ≤ Real.log (trc (K ^ (2 * (2 * m + q)))) := Real.log_nonneg hT₂
  rcases eq_or_ne (trc (K ^ (2 * m + q))) 0 with h0 | h0
  · rw [h0, Real.log_zero]; linarith
  · have hsq : 0 < trc (K ^ (2 * m + q)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    have hpos : 0 < Real.exp (-(2 * (s * (trc (K ^ (2 * m)) - 1)))) * trc (K ^ (2 * m + q)) ^ 2 :=
      mul_pos (Real.exp_pos _) hsq
    have hl := Real.log_le_log hpos hd
    rw [Real.log_mul (Real.exp_pos _).ne' hsq.ne', Real.log_exp, Real.log_pow] at hl
    push_cast at hl
    linarith

end Finite

/-! ## 2. The zero-flux kernel in its levels -/

section Levels

variable {ι : Type*}

/-- **The ground-normalised weight of level `j` at time `t`**: `e^{−(E_j − E_{g₀}) t}`. -/
def heatW (g₀ : ι) (E : ι → ℝ) (t : ℝ) (j : ι) : ℝ := Real.exp (-((E j - E g₀) * t))

/-- **The gap clause**: every level other than `g₀` lies at least `m` above it. -/
def ZeroFluxGap (g₀ : ι) (E : ι → ℝ) (m : ℝ) : Prop := ∀ j, j ≠ g₀ → E g₀ + m ≤ E j

/-- **The count clause**: the normalised heat trace at the physical time `t₀` is summable and at most
`1 + C`, i.e. `Σ_{j ≠ g₀} e^{−(E_j − E_{g₀}) t₀} ≤ C`. -/
def ZeroFluxCount (g₀ : ι) (E : ι → ℝ) (t₀ C : ℝ) : Prop :=
  Summable (heatW g₀ E t₀) ∧ ∑' j, heatW g₀ E t₀ j ≤ 1 + C

theorem heatW_pos (g₀ : ι) (E : ι → ℝ) (t : ℝ) (j : ι) : 0 < heatW g₀ E t j := Real.exp_pos _

theorem heatW_ground (g₀ : ι) (E : ι → ℝ) (t : ℝ) : heatW g₀ E t g₀ = 1 := by
  simp [heatW]

theorem heatW_anti {g₀ : ι} {E : ι → ℝ} (hground : ∀ j, E g₀ ≤ E j) {t t' : ℝ} (ht : t ≤ t')
    (j : ι) : heatW g₀ E t' j ≤ heatW g₀ E t j := by
  unfold heatW
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  exact mul_le_mul_of_nonneg_left ht (sub_nonneg.2 (hground j))

/-- **The gap carries the count to every longer time** (the level form of `GapL2.trace_transport`):
`1 ≤ Σ_j heatW t ≤ 1 + C e^{−m (t − t₀)}` at `t ≥ t₀`. -/
theorem level_transport {g₀ : ι} {E : ι → ℝ} {m t₀ t C : ℝ} (hground : ∀ j, E g₀ ≤ E j)
    (hgap : ZeroFluxGap g₀ E m) (hcount : ZeroFluxCount g₀ E t₀ C) (ht : t₀ ≤ t) :
    Summable (heatW g₀ E t) ∧ 1 ≤ ∑' j, heatW g₀ E t j ∧
      ∑' j, heatW g₀ E t j ≤ 1 + C * Real.exp (-(m * (t - t₀))) := by
  classical
  obtain ⟨hs0, hc⟩ := hcount
  have hst : Summable (heatW g₀ E t) :=
    Summable.of_nonneg_of_le (fun j => (heatW_pos g₀ E t j).le) (heatW_anti hground ht) hs0
  have hge : 1 ≤ ∑' j, heatW g₀ E t j := by
    have := hst.le_tsum g₀ (fun j _ => (heatW_pos g₀ E t j).le)
    rwa [heatW_ground] at this
  refine ⟨hst, hge, ?_⟩
  set ρ := Real.exp (-(m * (t - t₀))) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  set f : ι → ℝ := fun j => if j = g₀ then 0 else heatW g₀ E t j with hf
  set f₀ : ι → ℝ := fun j => if j = g₀ then 0 else heatW g₀ E t₀ j with hf₀
  have hf₀s : Summable f₀ := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs0
    · simp only [hf₀]; split_ifs
      · exact le_rfl
      · exact (heatW_pos g₀ E t₀ j).le
    · simp only [hf₀]; split_ifs
      · exact (heatW_pos g₀ E t₀ j).le
      · exact le_rfl
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hst
    · simp only [hf]; split_ifs
      · exact le_rfl
      · exact (heatW_pos g₀ E t j).le
    · simp only [hf]; split_ifs
      · exact (heatW_pos g₀ E t j).le
      · exact le_rfl
  have hterm : ∀ j, f j ≤ ρ * f₀ j := by
    intro j
    simp only [hf, hf₀]
    split_ifs with h
    · simp
    · have hΔ : m ≤ E j - E g₀ := by linarith [hgap j h]
      unfold heatW
      have hsplit : -((E j - E g₀) * t) = -((E j - E g₀) * t₀) + -((E j - E g₀) * (t - t₀)) := by
        ring
      rw [hsplit, Real.exp_add, mul_comm ρ]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      have := mul_nonneg (sub_nonneg.2 hΔ) (sub_nonneg.2 ht)
      nlinarith
  have hsum_t := hst.tsum_eq_add_tsum_ite g₀
  have hsum_t₀ := hs0.tsum_eq_add_tsum_ite g₀
  rw [heatW_ground] at hsum_t hsum_t₀
  have hle : ∑' j, f j ≤ ρ * ∑' j, f₀ j := by
    rw [← tsum_mul_left]
    exact hfs.tsum_le_tsum hterm (hf₀s.mul_left ρ)
  have hf₀C : ∑' j, f₀ j ≤ C := by
    have : ∑' j, heatW g₀ E t₀ j = 1 + ∑' j, f₀ j := hsum_t₀
    linarith
  have h1 : ∑' j, heatW g₀ E t j = 1 + ∑' j, f j := hsum_t
  have h2 : ρ * ∑' j, f₀ j ≤ ρ * C := mul_le_mul_of_nonneg_left hf₀C hρ0
  linarith

end Levels

section Kernel

variable {N : ℕ} [NeZero N]

/-- **The zero-flux kernel in its levels**: an orthonormal family `φ` of eigenfunctions of `trivKN` with
eigenvalues `μ_j`, `μ_j² = e^{−E_j t}` (`t = n a`), complete in the sense that the eigenvalues exhaust both
traces: `hs(trivKN) = Σ_j μ_j²` and `hs(trivKN ∗ trivKN) = Σ_j μ_j⁴` (so `ι` counts eigenvalues with
multiplicity; by Bessel, a family missing an eigenvalue has `Σ μ_j² < hs`). `g₀` is a lowest level. The
existence of such a family is the Hilbert–Schmidt spectral theorem for the symmetric bounded kernel `trivKN`
(nonzero eigenvalues only); it is not proved here. -/
structure ZeroFluxLevels (N : ℕ) [NeZero N] (β : ℝ) (n : ℕ) (i : Fin 4) {ι : Type*} (g₀ : ι)
    (E : ι → ℝ) : Prop where
  ground : ∀ j, E g₀ ≤ E j
  eigen : ∃ (φ : ι → (RectWilson.SpT i (CentreSectorSeed.Tr n i) → SUN.SU N) → ℝ) (μ : ι → ℝ),
    (∀ j, ∫ x, φ j x * φ j x ∂(hSN N n i) = 1) ∧
    (∀ j k, j ≠ k → ∫ x, φ j x * φ k x ∂(hSN N n i) = 0) ∧
    (∀ j x, ∫ y, trivKN N β n i x y * φ j y ∂(hSN N n i) = μ j * φ j x) ∧
    (∀ j, μ j ^ 2 = Real.exp (-(E j * ((n : ℝ) * aRun N β))))
  hs_eq : hs (hSN N n i) (trivKN N β n i) = ∑' j, Real.exp (-(E j * ((n : ℝ) * aRun N β)))
  hs_conv_eq : hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i))
      = ∑' j, Real.exp (-(E j * (2 * ((n : ℝ) * aRun N β))))

/-- **The reduction**: spectral levels with gap `m` and count `(t₀, C)`, `0 ≤ t₀ ≤ n a`, give
`trivialDefectN N β n i ≤ 2 C e^{m t₀} e^{−m n a}`. -/
theorem trivialDefectN_le_of_levels {β : ℝ} {n : ℕ} {i : Fin 4} {ι : Type*} {g₀ : ι} {E : ι → ℝ}
    {m t₀ C : ℝ} (hL : ZeroFluxLevels N β n i g₀ E) (hgap : ZeroFluxGap g₀ E m)
    (hcount : ZeroFluxCount g₀ E t₀ C) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ (n : ℝ) * aRun N β) :
    trivialDefectN N β n i
      ≤ 2 * C * Real.exp (m * t₀) * Real.exp (-(m * ((n : ℝ) * aRun N β))) := by
  set t := (n : ℝ) * aRun N β with htdef
  set G := Real.exp (-(E g₀ * t)) with hG
  have hGpos : 0 < G := Real.exp_pos _
  have hZ1 : hs (hSN N n i) (trivKN N β n i) = G * ∑' j, heatW g₀ E t j := by
    rw [hL.hs_eq, ← tsum_mul_left]
    congr 1; funext j
    unfold heatW
    rw [hG, ← Real.exp_add]; congr 1; ring
  have hZ2 : hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i))
      = G ^ 2 * ∑' j, heatW g₀ E (2 * t) j := by
    rw [hL.hs_conv_eq, ← tsum_mul_left]
    congr 1; funext j
    unfold heatW
    rw [hG, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  obtain ⟨-, h1lo, h1hi⟩ := level_transport hL.ground hgap hcount ht
  have ht2 : t₀ ≤ 2 * t := by linarith
  obtain ⟨-, h2lo, -⟩ := level_transport hL.ground hgap hcount ht2
  have hdef : trivialDefectN N β n i
      = 2 * Real.log (hs (hSN N n i) (trivKN N β n i))
        - Real.log (hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i))) := rfl
  have key := defect_le_of_excited (Z₁ := hs (hSN N n i) (trivKN N β n i))
    (Z₂ := hs (hSN N n i) (conv (hSN N n i) (trivKN N β n i) (trivKN N β n i)))
    (δ := C * Real.exp (-(m * (t - t₀)))) hGpos
    (by rw [hZ1]; nlinarith) (by rw [hZ1]; exact mul_le_mul_of_nonneg_left h1hi hGpos.le)
    (by rw [hZ2]; nlinarith [pow_pos hGpos 2])
  rw [hdef]
  have hρ : Real.exp (-(m * (t - t₀))) = Real.exp (m * t₀) * Real.exp (-(m * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hρ] at key
  linarith

/-- **The uniform glueball statement at the window `[2ℓ, 5ℓ]`**: eventually in `β`, at every power-of-two side
`n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and every step, the zero-flux kernel has levels with gap `m` and count `(t₀, C)`,
the same `m`, `t₀`, `C` at every `β`. DERIVED: `2` and `5` the window of `ObserverTheory.HiddenCostAt`
(`5` leaves room for the power of two at or above `⌈2ℓ/a⌉`, below `4ℓ + 2a`); `2` also the least side. -/
def UniformGlueball (N : ℕ) [NeZero N] (m t₀ C ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun N β → (n : ℝ) * aRun N β ≤ 5 * ℓ → ∀ i : Fin 4,
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ),
        ZeroFluxLevels N β n i g₀ E ∧ ZeroFluxGap g₀ E m ∧ ZeroFluxCount g₀ E t₀ C

/-- **(T) from the gap clause and the count clause**: `UniformGlueball N m t₀ C ℓ` and `0 ≤ t₀ ≤ 2ℓ` give
`HiddenCostAt N m (2 C e^{m t₀}) ℓ`. -/
theorem hiddenCostAt_of_uniformGlueball {m t₀ C ℓ : ℝ} (ht₀ : 0 ≤ t₀) (hℓ : t₀ ≤ 2 * ℓ)
    (h : UniformGlueball N m t₀ C ℓ) :
    ObserverTheory.HiddenCostAt N m (2 * C * Real.exp (m * t₀)) ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, hL, hg, hc⟩ := hβ n hn h2 hlo hhi i
  exact trivialDefectN_le_of_levels hL hg hc ht₀ (hℓ.trans hlo)

end Kernel

/-! ## 3. Loops cost area: the count clause from a loop gas -/

section LoopGas

variable {P : Type*} {ι : Type*}

/-- **Loop entropy**: every finite family of loop configurations of lattice size `s` has at most `V Kˢ`
members. -/
def LoopEntropy (size : P → ℕ) (V K : ℝ) : Prop :=
  ∀ (s : ℕ) (F : Finset P), (∀ γ ∈ F, size γ = s) → (F.card : ℝ) ≤ V * K ^ s

/-- **Entropy against energy, finite form**: `Σ_{γ ∈ F} e^{−c·size γ} ≤ V q/(1 − q)`, `q = K e^{−c} < 1`. -/
theorem loopGas_finset_le {size : P → ℕ} {V K c : ℝ} (hsize : ∀ γ, 1 ≤ size γ)
    (hent : LoopEntropy size V K) (hV : 0 ≤ V) (hK : 0 ≤ K) (hq : K * Real.exp (-c) < 1)
    (F : Finset P) :
    ∑ γ ∈ F, Real.exp (-(c * size γ))
      ≤ V * (K * Real.exp (-c) / (1 - K * Real.exp (-c))) := by
  classical
  have hq0 : 0 ≤ K * Real.exp (-c) := mul_nonneg hK (Real.exp_pos _).le
  have hmaps : ∀ γ ∈ F, size γ ∈ Finset.Ico 1 (F.sup size + 1) := fun γ hγ => by
    rw [Finset.mem_Ico]; exact ⟨hsize γ, Nat.lt_succ_of_le (Finset.le_sup hγ)⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun s : ℕ => Real.exp (-(c * s)))]
  calc ∑ s ∈ Finset.Ico 1 (F.sup size + 1), ∑ _γ ∈ F with size _γ = s, Real.exp (-(c * s))
      ≤ ∑ s ∈ Finset.Ico 1 (F.sup size + 1), V * (K * Real.exp (-c)) ^ s := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((F.filter (fun γ => size γ = s)).card : ℝ) ≤ V * K ^ s :=
          hent s _ (fun γ hγ => (Finset.mem_filter.1 hγ).2)
        have he : Real.exp (-(c * s)) = Real.exp (-c) ^ s := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [he, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcard (pow_nonneg (Real.exp_pos _).le s)
    _ = V * ∑ s ∈ Finset.Ico 1 (F.sup size + 1), (K * Real.exp (-c)) ^ s := by
        rw [Finset.mul_sum]
    _ ≤ V * (K * Real.exp (-c) / (1 - K * Real.exp (-c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hV
        have := geom_sum_Ico_le_of_lt_one (m := 1) (n := F.sup size + 1) hq0 hq
        rwa [pow_one] at this

/-- **Entropy against energy**: the loop gas sum is summable and at most `V q/(1 − q)`. -/
theorem loopGas_tsum_le {size : P → ℕ} {V K c : ℝ} (hsize : ∀ γ, 1 ≤ size γ)
    (hent : LoopEntropy size V K) (hV : 0 ≤ V) (hK : 0 ≤ K) (hq : K * Real.exp (-c) < 1) :
    Summable (fun γ => Real.exp (-(c * size γ))) ∧
      ∑' γ, Real.exp (-(c * size γ)) ≤ V * (K * Real.exp (-c) / (1 - K * Real.exp (-c))) :=
  ⟨summable_of_sum_le (fun _ => (Real.exp_pos _).le) (loopGas_finset_le hsize hent hV hK hq),
    Real.tsum_le_of_sum_le (fun _ => (Real.exp_pos _).le) (loopGas_finset_le hsize hent hV hK hq)⟩

/-- **The loops carry the levels**: the excited levels are carried injectively by loop configurations `p j`,
each costing `(E_j − E_{g₀}) t₀ ≥ c · size(p j)`. -/
structure LoopsCarry (g₀ : ι) (E : ι → ℝ) (t₀ c : ℝ) (size : P → ℕ) (p : ι → P) : Prop where
  inj : ∀ j k, j ≠ g₀ → k ≠ g₀ → p j = p k → j = k
  cost : ∀ j, j ≠ g₀ → c * size (p j) ≤ (E j - E g₀) * t₀

/-- **The count clause from a loop gas**: `LoopsCarry` and `LoopEntropy size V K` with `q = K e^{−c} < 1`
give `ZeroFluxCount g₀ E t₀ (V q/(1 − q))`. -/
theorem count_of_loops {g₀ : ι} {E : ι → ℝ} {t₀ c V K : ℝ} {size : P → ℕ} {p : ι → P}
    (hL : LoopsCarry g₀ E t₀ c size p) (hsize : ∀ γ, 1 ≤ size γ) (hent : LoopEntropy size V K)
    (hV : 0 ≤ V) (hK : 0 ≤ K) (hq : K * Real.exp (-c) < 1) :
    ZeroFluxCount g₀ E t₀ (V * (K * Real.exp (-c) / (1 - K * Real.exp (-c)))) := by
  classical
  set B := V * (K * Real.exp (-c) / (1 - K * Real.exp (-c)))
  have hfin : ∀ u : Finset ι, ∑ j ∈ u, heatW g₀ E t₀ j ≤ 1 + B := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not u (fun j => j = g₀)]
    have hA : ∑ j ∈ u.filter (fun j => j = g₀), heatW g₀ E t₀ j ≤ 1 := by
      have hsub : u.filter (fun j => j = g₀) ⊆ {g₀} := by
        intro j hj; rw [Finset.mem_singleton]; exact (Finset.mem_filter.1 hj).2
      calc ∑ j ∈ u.filter (fun j => j = g₀), heatW g₀ E t₀ j
          ≤ ∑ j ∈ ({g₀} : Finset ι), heatW g₀ E t₀ j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (heatW_pos g₀ E t₀ j).le)
        _ = 1 := by rw [Finset.sum_singleton, heatW_ground]
    have hBnd : ∑ j ∈ u.filter (fun j => ¬ j = g₀), heatW g₀ E t₀ j ≤ B := by
      set u' := u.filter (fun j => ¬ j = g₀)
      have hinj : Set.InjOn p u' := by
        intro j hj k hk hjk
        exact hL.inj j k (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hk).2 hjk
      calc ∑ j ∈ u', heatW g₀ E t₀ j ≤ ∑ j ∈ u', Real.exp (-(c * size (p j))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            unfold heatW
            exact Real.exp_le_exp.2 (neg_le_neg (hL.cost j (Finset.mem_filter.1 hj).2))
        _ = ∑ γ ∈ u'.image p, Real.exp (-(c * size γ)) :=
            (Finset.sum_image (f := fun γ => Real.exp (-(c * size γ))) hinj).symm
        _ ≤ B := loopGas_finset_le hsize hent hV hK hq _
    linarith
  have hnn : 0 ≤ heatW g₀ E t₀ := fun j => (heatW_pos g₀ E t₀ j).le
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- **Loops cost area, energy form**: if every excitation carried by a configuration of lattice size `s` lies at
least `σ (s a)` above the ground (`σ a` per unit of size), then the count clause holds at `t₀ ≥ 0` with `C = V q/(1 − q)`,
`q = K e^{−σ a t₀}`, provided `q < 1`. -/
theorem count_of_area {g₀ : ι} {E : ι → ℝ} {σ a t₀ V K : ℝ} {size : P → ℕ} {p : ι → P}
    (hinj : ∀ j k, j ≠ g₀ → k ≠ g₀ → p j = p k → j = k)
    (harea : ∀ j, j ≠ g₀ → σ * (a * size (p j)) ≤ E j - E g₀) (ht₀ : 0 ≤ t₀)
    (hsize : ∀ γ, 1 ≤ size γ) (hent : LoopEntropy size V K) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hq : K * Real.exp (-(σ * a * t₀)) < 1) :
    ZeroFluxCount g₀ E t₀
      (V * (K * Real.exp (-(σ * a * t₀)) / (1 - K * Real.exp (-(σ * a * t₀))))) := by
  refine count_of_loops ⟨hinj, fun j hj => ?_⟩ hsize hent hV hK hq
  have := mul_le_mul_of_nonneg_right (harea j hj) ht₀
  calc σ * a * t₀ * (size (p j) : ℝ) = σ * (a * size (p j)) * t₀ := by ring
    _ ≤ (E j - E g₀) * t₀ := this

/-- **Finitely many loop configurations carry finitely many levels**: `LoopsCarry` into a finite type forces
the excited levels to be finite. -/
theorem finite_excited_of_loopsCarry [Finite P] {g₀ : ι} {E : ι → ℝ} {t₀ c : ℝ} {size : P → ℕ}
    {p : ι → P} (hL : LoopsCarry g₀ E t₀ c size p) : Finite {j : ι // j ≠ g₀} :=
  Finite.of_injective (fun j : {j : ι // j ≠ g₀} => p j.1)
    (fun j k h => Subtype.ext (hL.inj j.1 k.1 j.2 k.2 h))

/-- **When the loop gas converges**: `K e^{−c} < 1 ↔ log K < c` (`K > 0`). -/
theorem q_lt_one_iff {K c : ℝ} (hK : 0 < K) : K * Real.exp (-c) < 1 ↔ Real.log K < c := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _), ← Real.exp_log hK,
    Real.exp_lt_exp, Real.log_exp]

end LoopGas

/-! ### The concrete loop configurations: touch-connected plaquette sets -/

section Plaquettes

open MassGap.WilsonHypercubic MassGap.StrongCoupling MassGap.PolymerCount

variable (dim n : ℕ) [NeZero n]

/-- **The loop configurations of the periodic `dim`-dimensional lattice of extent `n`**: nonempty touch-connected
plaquette sets. -/
def LoopConf : Type :=
  {X : Finset (Plaq dim n) // X.Nonempty ∧ TouchConnected (bd (d := dim) (n := n)) X}

/-- The lattice size of a loop configuration: its number of plaquettes. -/
def loopSize (γ : LoopConf dim n) : ℕ := γ.1.card

theorem one_le_loopSize (γ : LoopConf dim n) : 1 ≤ loopSize dim n γ :=
  Finset.card_pos.2 γ.2.1

omit [NeZero n] in
theorem card_plaq : (Fintype.card (Plaq dim n) : ℝ) = (dim : ℝ) ^ 2 * (n : ℝ) ^ dim := by
  simp only [Plaq, Site, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast; ring

/-- **The loop entropy of the lattice**: plaquette sets of size `s` number at most
`|Plaq dim n| · ((16 dim + 1)²)ˢ` (`StrongCoupling.card_connSets_le_hypercubic`, summed over the roots). -/
theorem loopEntropy_hypercubic :
    LoopEntropy (loopSize dim n) (Fintype.card (Plaq dim n) : ℝ) (((16 * dim + 1) ^ 2 : ℕ) : ℝ) := by
  classical
  intro s F hF
  have hsub : F.map ⟨Subtype.val, Subtype.val_injective⟩
      ⊆ Finset.univ.biUnion (fun p₀ => connSets (bd (d := dim) (n := n)) p₀ s) := by
    intro X hX
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.1 hX
    obtain ⟨p₀, hp₀⟩ := γ.2.1
    refine Finset.mem_biUnion.2 ⟨p₀, Finset.mem_univ _, ?_⟩
    exact mem_connSets.2 ⟨hp₀, fun q hq => γ.2.2 p₀ hp₀ q hq, hF γ hγ⟩
  have hcard : F.card ≤ Fintype.card (Plaq dim n) * ((16 * dim + 1) ^ 2) ^ s := by
    calc F.card = (F.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
      _ ≤ (Finset.univ.biUnion (fun p₀ => connSets (bd (d := dim) (n := n)) p₀ s)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p₀ : Plaq dim n, (connSets (bd (d := dim) (n := n)) p₀ s).card := Finset.card_biUnion_le
      _ ≤ ∑ _p₀ : Plaq dim n, ((16 * dim + 1) ^ 2) ^ s :=
          Finset.sum_le_sum fun p₀ _ => card_connSets_le_hypercubic p₀ s
      _ = Fintype.card (Plaq dim n) * ((16 * dim + 1) ^ 2) ^ s := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact_mod_cast hcard

/-- **Loops cost area on the lattice**: excited levels carried injectively by touch-connected plaquette sets,
each lying at least `σ (s a)` above the ground (`s` its plaquette count), give the count clause with
`C = dim² nᵈⁱᵐ q/(1 − q)`, `q = (16 dim + 1)² e^{−σ a t₀}`, provided `q < 1`. -/
theorem count_of_area_hypercubic {ι : Type*} {g₀ : ι} {E : ι → ℝ} {σ a t₀ : ℝ} {p : ι → LoopConf dim n}
    (hinj : ∀ j k, j ≠ g₀ → k ≠ g₀ → p j = p k → j = k)
    (harea : ∀ j, j ≠ g₀ → σ * (a * loopSize dim n (p j)) ≤ E j - E g₀) (ht₀ : 0 ≤ t₀)
    (hq : (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Real.exp (-(σ * a * t₀)) < 1) :
    ZeroFluxCount g₀ E t₀
      ((dim : ℝ) ^ 2 * (n : ℝ) ^ dim * ((((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Real.exp (-(σ * a * t₀))
        / (1 - (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Real.exp (-(σ * a * t₀))))) := by
  rw [← card_plaq]
  exact count_of_area hinj harea ht₀ (one_le_loopSize dim n) (loopEntropy_hypercubic dim n)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hq

/-- **Undecorated plaquette sets carry only finitely many levels**: an injective assignment of the excited
levels to `LoopConf dim n` (a finite type) forces finitely many excited levels. -/
theorem finite_excited_hypercubic {ι : Type*} {g₀ : ι} {p : ι → LoopConf dim n}
    (hinj : ∀ j k, j ≠ g₀ → k ≠ g₀ → p j = p k → j = k) : Finite {j : ι // j ≠ g₀} := by
  classical
  haveI : Finite (LoopConf dim n) := by unfold LoopConf; infer_instance
  exact finite_excited_of_loopsCarry (E := fun _ => (0 : ℝ)) (t₀ := 0) (c := 0)
    (size := loopSize dim n) ⟨hinj, fun _ _ => by simp⟩

end Plaquettes

/-! ## 4. Where the loop-gas route fails at fine lattice -/

/-- **Entropy wins at fine lattice**: for `N ≥ 1`, `K > 1`, `t₀ ≥ 0` and a tension `σ(β)` bounded above
eventually, eventually in `β`, `K e^{−σ a t₀} > 1` (`a = aRun N β → 0`). -/
theorem eventually_entropy_wins {N : ℕ} (hN : 1 ≤ N) {K t₀ S : ℝ} (hK : 1 < K) (ht₀ : 0 ≤ t₀)
    {σ : ℝ → ℝ} (hσ : ∀ᶠ β in atTop, σ β ≤ S) :
    ∀ᶠ β in atTop, 1 < K * Real.exp (-(σ β * aRun N β * t₀)) := by
  have hK0 : 0 < K := one_pos.trans hK
  have hlog : 0 < Real.log K := Real.log_pos hK
  have ha : Tendsto (aRun N) atTop (𝓝 0) :=
    (ShortDistanceY.tendsto_aRun_nhdsGT_zero hN).mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun β => max S 0 * t₀ * aRun N β) atTop (𝓝 0) := by
    have := ha.const_mul (max S 0 * t₀)
    rwa [mul_zero] at this
  have hev := hlim (Iio_mem_nhds hlog)
  filter_upwards [hev, hσ, eventually_gt_atTop (0 : ℝ)] with β hβ hσβ hβ0
  have hlt : max S 0 * t₀ * aRun N β < Real.log K := hβ
  have hapos := aRun_pos hN hβ0
  have hat : 0 ≤ aRun N β * t₀ := mul_nonneg hapos.le ht₀
  have hle : σ β * aRun N β * t₀ ≤ max S 0 * t₀ * aRun N β := by
    have h1 : σ β ≤ max S 0 := hσβ.trans (le_max_left _ _)
    have := mul_le_mul_of_nonneg_right h1 hat
    linarith [this]
  have hc : σ β * aRun N β * t₀ < Real.log K := hle.trans_lt hlt
  have he : Real.exp (-Real.log K) < Real.exp (-(σ β * aRun N β * t₀)) :=
    Real.exp_lt_exp.2 (by linarith)
  rw [Real.exp_neg, Real.exp_log hK0] at he
  calc (1 : ℝ) = K * K⁻¹ := (mul_inv_cancel₀ hK0.ne').symm
    _ < K * Real.exp (-(σ β * aRun N β * t₀)) := mul_lt_mul_of_pos_left he hK0

/-- **The loop-gas hypothesis is not uniform in the zoom**: for `N ≥ 1`, `K > 1`, `t₀ ≥ 0` and a tension
bounded above eventually, `K e^{−σ a t₀} < 1` does not hold eventually in `β`. -/
theorem not_eventually_area_beats_entropy {N : ℕ} (hN : 1 ≤ N) {K t₀ S : ℝ} (hK : 1 < K)
    (ht₀ : 0 ≤ t₀) {σ : ℝ → ℝ} (hσ : ∀ᶠ β in atTop, σ β ≤ S) :
    ¬ ∀ᶠ β in atTop, K * Real.exp (-(σ β * aRun N β * t₀)) < 1 := by
  intro h
  obtain ⟨β, h1, h2⟩ := ((eventually_entropy_wins hN hK ht₀ hσ).and h).exists
  exact lt_asymm h1 h2

/-- **The volume factor at the window**: `2ℓ ≤ n a`, `a > 0`, `ℓ ≥ 0` give `(2ℓ/a)ᵈⁱᵐ ≤ nᵈⁱᵐ`. -/
theorem volume_le {dim n : ℕ} {ℓ a : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) (h : 2 * ℓ ≤ (n : ℝ) * a) :
    (2 * ℓ / a) ^ dim ≤ (n : ℝ) ^ dim := by
  have h1 : 2 * ℓ / a ≤ n := by rw [div_le_iff₀ ha]; exact h
  exact pow_le_pow_left₀ (div_nonneg (by linarith) ha.le) h1 dim

end MassGap.GlueballArea

#print axioms MassGap.GlueballArea.defect_le_of_excited
#print axioms MassGap.GlueballArea.log_doubling_transport
#print axioms MassGap.GlueballArea.level_transport
#print axioms MassGap.GlueballArea.trivialDefectN_le_of_levels
#print axioms MassGap.GlueballArea.hiddenCostAt_of_uniformGlueball
#print axioms MassGap.GlueballArea.loopGas_finset_le
#print axioms MassGap.GlueballArea.loopGas_tsum_le
#print axioms MassGap.GlueballArea.count_of_loops
#print axioms MassGap.GlueballArea.count_of_area
#print axioms MassGap.GlueballArea.q_lt_one_iff
#print axioms MassGap.GlueballArea.loopEntropy_hypercubic
#print axioms MassGap.GlueballArea.count_of_area_hypercubic
#print axioms MassGap.GlueballArea.eventually_entropy_wins
#print axioms MassGap.GlueballArea.not_eventually_area_beats_entropy
#print axioms MassGap.GlueballArea.volume_le
#print axioms MassGap.GlueballArea.finite_excited_of_loopsCarry
#print axioms MassGap.GlueballArea.finite_excited_hypercubic
