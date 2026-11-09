import Mathlib
import MassGap.FreeLevels
import MassGap.ModeHyper
import MassGap.ExpandMatch
import MassGap.BulkBound

/-!
# MassGap.FreeBridge — one comparison of the interacting aperture reading with the free one

`ApertureCount.ApertureCountAt` carries two single-observer inputs about the interacting state `ν_k`
(`stateK`): H1, per-mode hypercontractivity of the screen's eigenmodes, and H3, the level decay of the
screen's Gram spectrum. `FreeLevels` proves H3 for the free flowed spectrum (`FreeScreenSpectrum`, through
`WeylGrowth`), and `ModeHyper` proves H1's form for a finite chaos on the spin cube (`bonami`). This module
replaces H1 and H3 by one input, `FreeComparable`: the observer's reading at every aperture is within one
factor `e^δ` of the free reading, in the law of each eigenmode and in the Gram spectrum. It proves that the
input gives what H1 and H3 feed, and it closes the root with it. Declarations are in the namespace
`MassGap.FreeBridge`.

## 1. What the comparison is stated on

The comparison is stated on what the observer reads: the finite screen of `apL⁴` readings and its Gram
matrix, whose eigenmodes are the modes the measured count `apDim` counts. Two forms were tested and set
aside.

* A density ratio between the full configurations of an aperture is `e^{O(volume)}` and grows with the
  step; no uniform bound holds there.
* A two-sided density ratio of the reading's law against the Gaussian of its own Gram matrix fails twice.
  On the compact `SU(N)` configurations every reading is bounded, so its law never dominates a multiple of a
  Gaussian. And the plaquette density is quadratic in the gauge field: a free reading of degree `q ≥ 2` in
  the Gaussian field has tails `exp(−c |x|^{2/q})`, so its density against the Gaussian of the same variance
  is unbounded already in the free theory (argued: the Gaussian chaos tails are cited, not proved).

So the law clause compares each eigenmode with the free reading of the same channel: its even moments are
at most `e^δ` times the free chaos envelope of its own variance, `((2p − 1)^{q_j})^p λ^p` (Nelson's constant
of a chaos of order `q_j`), at the order `q_j = chaosOrd j` read from the composite. A one-sided density
ratio `e^δ` of the mode's law against a free chaos law of the same variance gives this clause (integrate
`x^{2p}`; argued). It is the part of that comparison H1 reads.

The order is counted per lattice factor `(W, flag)`: `factorOrd = |W| + 2`, `chaosOrd (inl m)` the sum over
the factors of the monomial, `chaosOrd (inr q) = 2` (the plaquette density, one quadratic factor), and
`wickB j = ⌈chaosOrd j / 2⌉` (`1` at a plaquette). The count covers the free leading degree of every factor
(argued; the lattice readings are not polynomials in the field, so this is not proved). The trace of the
linear term of `U_p − 1` vanishes, so a single letter of the imaginary part reads quadratically:
`BulkBound.p1` reads `N − Re tr U_p` (`BulkBound.facV_p1`), of degree `2`. A single letter of the real part
reads `Im tr U_p`; the quadratic term `tr X²` is real, so at `N ≥ 3` its leading term is `−tr X³ / 6`, of
degree `3`. A word of length `L ≥ 2` reads with degree `L` or `L + 1`. Proved about the count:
`factorOrd_true_letter` (`3` at a single letter of the real part), `factorOrd_word` (`≥ |W| + 1`),
`factorOrd_p1` (`≥ cdim [p1] = 2`), `chaosOrd_jn_eq` and `chaosOrd_jn` (`6(n + 1) ≥ d = 4(n + 1)` at
`BulkBound.mono n`, which reads `(N − Re tr U_p)^{2(n+1)}`), `chaosOrd_le_two_wickB`, and
`wickIx_lt_wickB_jn`: `ZoomFree.wickIx = ⌈d/4⌉` is `n + 1` at `mono n`, below the bridge's `3(n + 1)`.

## 2. The clauses (stated)

* `LawClause ν F q δ`: every unit eigenvector `v` of `gram ν F` at `λ` has
  `ν((∑_y v y • F_y)^{2p}) ≤ e^δ ((2p − 1)^q)^p λ^p` for every `p`. Basis-free, as H1.
* `SpecClause λ λ₀ δ`: `e^{−δ} λ₀ ≤ λ ≤ e^δ λ₀` mode by mode. `specClause_zero_iff`: at `δ = 0` it is
  `λ = λ₀`.
* `FreeSpecAt λ τ κ δ`: `λ` is in `SpecClause` with a relabelled free box heat spectrum `w e^{−2tμ}` of the
  Dirichlet box in `d = 4` with `2t/L² ≥ τ` and local weight ratio `κ`, exactly the data of
  `FreeLevels.FreeScreenSpectrum`. A two-sided comparison of the Gram forms, `e^{−δ} G₀ ≤ G ≤ e^δ G₀`, gives
  it by Courant–Fischer (cited: no min-max theorem for matrices is in Mathlib at this pin or in the
  repository).
* `FreeComparable Wf b`: one `δ ≥ 0`, `τ > 0`, `κ ≥ 0` with, at every aperture `s ∈ (0, b]`, eventually in
  the step, for every channel `j`, `LawClause` of the screen at `q_j = chaosOrd j` and `FreeSpecAt` of its
  spectrum (`BridgeAt`). The quantifier shape is H1's and H3's in `ApertureCountAt`. It is one structure
  with two clauses and one `δ`.

## 3. The comparison carries the moments and the count (proved)

* `p_le_of_spec`: the normalized spectra are within `e^{2δ}`. `spRenyi_le_of_spec`: `R ≤ e^{2δ} R₀`.
  `levelCount_le_of_spec`: the `i`-th rung holds at most the free rung `i + M` when `e^{2δ} a^{2M} ≤ 1`.
  `one_le_spDim`: `exp H ≥ 1` on a nonnegative spectrum.
* `freeSpec_renyi`, `freeSpec_spDim`, `freeSpec_level` (from `FreeLevels.free_h3_local` at the ladder
  `a = e^{−1/2}`): `R ≤ R̄ = e^{2δ} A_κ² e² D₀`, `exp H ≤ R̄`, and
  `levelCount_i ≤ c₀ D₀ (M + 1)² · exp H · (i + 1)²` with `M = ⌈2δ⌉`, `D₀ = A_κ² e ((1/τ + π²)/4)²`,
  `c₀ = π⁴ e (1 − 8(1 + κ) log a)²`.
* `h3_of_freeComparable`: `FreeComparable` gives the H3 clause of `ApertureCountAt` exactly.
* `h1_of_lawClause`: `LawClause` at order `q ≤ 2w` gives `ν(e^{2p}) ≤ ((2p)!)^w (e^{δ + 2w} λ)^p` for every
  unit eigenvector (`ModeHyper.wick_const`). `h1_of_freeComparable`: H1's form at every channel at the
  Wick index `wickB j` (not `ZoomFree.wickIx j`), with `C_j = e^{δ + 2 wickB j}`.

H1 in `ApertureCountAt` asks one `C` for every channel of `MIx`, whose canonical dimensions are unbounded
(`CompositesBuild.Ix0` is every admissible monomial). The free chaos needs `C_j` growing with the channel:
for a Gaussian monomial of degree `q` the least `C` over all orders is about `(e/2)^q / √2` (argued from
Stirling, not proved), and `ModeHyper.cube_H1` gives `e^{2w}`. So the uniform-`C` H1 is not met by the free
reading over the whole tower, and `FreeComparable` does not give it. Nor does it give `ZoomFree.ApertureOneAt`,
whose Wick index `wickIx` is below the reading's at the tower (`wickIx_lt_wickB_jn`). The chain needs
neither: `ScaleControlChan` asks one index per channel, existentially. `ApertureSettlesAtW wix`,
`ApertureOneAtW wix` are `ZoomFree`'s clauses at a per-channel index `wix`;
`scaleControlChan_of_apertureW` is `ZoomFree.scaleControlChan_of_aperture` at that index (the proof reads
the index only as the channel's existential index), and `apertureSettlesAtW_of_one` the one-mode witness.
`apertureOneAt_of_bridge` gives `ApertureOneAtW wickB` at noise `√(max(C_j R̄, 1)) σⱼ` and, at the
plaquettes (`wickB = 1`, as the plaquette clause's `(2m)!` asks), `√(max(e^{δ+2} R̄, 1)) σP`.

## 4. The free reading meets the comparison (proved)

* `lawClause_cube`: on the spin cube every screen of degree-`q` readings meets `LawClause` at `δ = 0`, at
  every order, every screen and every number of spins (`ModeHyper.bonami`). The Gaussian statement is its
  moment limit (`ModeHyper` §5, argued).
* `freeSpec_of_freeScreen`: `FreeScreenSpectrum` gives `FreeSpecAt` at `δ = 0`, and
  `specClause_zero_iff` makes the spectral clause at `δ = 0` the same as `FreeScreenSpectrum`.
* `freeComparable_of_free`: `FreeScreenSpectrum` and the law clause at `δ = 0` give `FreeComparable`. The
  law clause there is a hypothesis on `ν_k`, at the order `chaosOrd j`; it is proved only on the cube (any
  screen of readings of degree at most `chaosOrd j`), and that the free lattice readings are such readings
  is argued (§1).

## 5. The comparison is a constraint, and it carries the conclusion (proved)

The spike reading `cubeRead m = ∏_i (1 + sgn xᵢ)` is `2^m` at one point of the cube and `0` elsewhere; as a
one-site screen its Gram matrix is `(2^m)` (`spike_unitEig`) and `ν(F⁴) = 2^m (2^m)²` (`spike_four`).

* `lawClause_spike_fails`: for every order `q` and every `δ` some `m` fails `LawClause`. So no `δ` works
  over the family: the clause is a real constraint, and its constant is not absolute.
* `h1_spike_fails` (load test): for every Wick exponent `w` no `C` gives H1's form over the family. Without
  the comparison the per-mode moments fail; with it they hold (`h1_of_lawClause`).
* For the spectral clause, `FreeLevels.spRenyi_unbounded_pos` is the load test: Shannon alone leaves `R`
  unbounded, and the clause bounds it (`spRenyi_le_of_spec`).

## 6. The root (proved, from the inputs)

* `ApertureBridgeAt b₀ z b Wf`: `ApertureCountAt` with H1 and H3 replaced by `FreeComparable Wf b`; H2, the
  plaquette observable and (af) unchanged. `apertureOneAt_of_bridge`; `substrateCoreCL_of_bridge` through
  `apertureSettlesAtW_of_one`, `scaleControlChan_of_apertureW` at `wickB` and
  `ZoomFree.afCoefficient_of_settles`.
* Copied over the coupling family by `#along_generalize_more` (no copy mentions `dyBeta`).
* `CoreInputsAlongWFB N βs`: `ExpandMatch.CoreInputsAlongWAM` with the copy of `ApertureBridge` in place
  of the copy of `ApertureCount`. `openAlongW_of_coreWFB`; `clayStatementOf_of_freeBridge`: `StrongEnd N`,
  the settling window reading and `CoreInputsAlongWFB` along the towers near `0⁺` give
  `ClayStatementOf (SU N)`. Neither bundle implies the other (argued; no separation is proved):
  `FreeComparable` asks a fixed excess `e^δ` over the free envelope where H1 allows a geometric `C^p`, and H1
  asks one `C` over the tower where the bridge allows `C_j`.

## 7. What the comparison does not give

`ProxyCov.MixGerm` and `ExpandMatch.RPGerm` compare the reflection form of the bare renormalized product
`prodSmear (cMono …)` with the flowed proxy `proxB Wf cf`. `FreeComparable` reads only the flowed screen
at one step and aperture; it does not contain `cf`, `z` or `μ`, so it does not constrain the bare product
or the proxy's coefficients (argued; no lattice witness of `FreeComparable` exists to build a proved
separation).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lowest mode, the free value of `δ` and the limit point; `1` the
unit, the floor of `max(·, 1)`, the first order and the shift; `2` the even powers, the squares, the factor
of `e^{2δ}` (two normalizations), the exponent `r = d/2` and the order of the spike test; `4 = 2 · 2` the
spacetime dimension and the fourth moment; `2p − 1` Nelson's constant; `|W| + 2` the order of a factor, `2`
the plaquette's order, `⌈q/2⌉` the Wick index; `3`, `4` in `wickIx`; `e^{2w}` from
`n^n ≤ n! eⁿ`; `e^{−1/2}` the ladder of one e-fold per rung; `M = ⌈2δ⌉` the rung shift (from `e^{2δ} a^{2M} ≤ 1`); `π`, `e`, `A_κ`, `D₀`, `c₀` as in
`FreeLevels`; `δ`, `τ`, `κ` existential, `δ = 0` at the free reading and no `δ` at the spike family.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FreeBridge

open Filter
open scoped Topology Real
open MassGap.ApertureModes MassGap.ApertureCount MassGap.FreeLevels

/-! ## 2. The clauses -/

section Clauses

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The law clause: every unit eigenvector's mode has even moments at most `e^δ` times the free chaos
envelope `((2p − 1)^q)^p λ^p` of its own variance. DERIVED: `2p − 1` Nelson's constant; `2` the even
power. -/
def LawClause (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι] (F : ι → C(X, ℝ)) (q : ℕ)
    (δ : ℝ) : Prop :=
  ∀ (p : ℕ) (lam : ℝ) (v : ι → ℝ), IsUnitEig (gram ν F) lam v →
    ν ((∑ y, v y • F y) ^ (2 * p)) ≤ Real.exp δ * ((2 * (p : ℝ) - 1) ^ q) ^ p * lam ^ p

/-- The spectral clause: `e^{−δ} λ₀ ≤ λ ≤ e^δ λ₀` mode by mode. DERIVED: no numeral. -/
def SpecClause {κ' : Type*} (lam lam0 : κ' → ℝ) (δ : ℝ) : Prop :=
  ∀ α, Real.exp (-δ) * lam0 α ≤ lam α ∧ lam α ≤ Real.exp δ * lam0 α

/-- DERIVED: `0` the free value. -/
theorem specClause_refl {κ' : Type*} (lam : κ' → ℝ) : SpecClause lam lam 0 := fun α => by
  simp

/-- At `δ = 0` the spectral clause is equality. DERIVED: `0` the free value. -/
theorem specClause_zero_iff {κ' : Type*} (lam lam0 : κ' → ℝ) : SpecClause lam lam0 0 ↔ lam = lam0 := by
  constructor
  · intro h
    funext α
    have := h α
    simp only [neg_zero, Real.exp_zero, one_mul] at this
    exact le_antisymm this.2 this.1
  · rintro rfl
    exact specClause_refl lam

/-- The spectral data of `FreeLevels.FreeScreenSpectrum` with the equality relaxed to `SpecClause`: `λ` is
within `e^{±δ}` of a relabelled box heat spectrum `w e^{−2tμ}` of the Dirichlet box in `d = 4`, with
`2t/L² ≥ τ`, positive weights largest at the lowest mode and local weight ratio `κ`. DERIVED: `4 = 2 · 2`
the spacetime dimension; `2` the flow; `0` the signs and the lowest mode. -/
def FreeSpecAt {κ' : Type*} [Fintype κ'] (lam : κ' → ℝ) (τ κ δ : ℝ) : Prop :=
  ∃ (K : ℕ) (hK : 0 < K) (L t : ℝ) (w : (Fin (2 * 2) → Fin K) → ℝ) (e : κ' ≃ (Fin (2 * 2) → Fin K)),
    0 < L ∧ 0 < t ∧ τ ≤ 2 * t / L ^ 2 ∧ (∀ x, 0 < w x) ∧ (∀ x, w x ≤ w (fun _ => ⟨0, hK⟩))
      ∧ (∀ x, Real.log (w (fun _ => ⟨0, hK⟩) / w x)
          ≤ κ * (boxU L t K x - boxU L t K (fun _ : Fin (2 * 2) => (⟨0, hK⟩ : Fin K))))
      ∧ SpecClause lam (heatSpec w (boxU L t K) ∘ e) δ

end Clauses

/-! ## 3. The comparison carries the moments and the count -/

section Spec

variable {κ' : Type*} [Fintype κ'] {lam lam0 : κ' → ℝ} {δ : ℝ}

/-- DERIVED: no numeral. -/
theorem sum_ge_of_spec (h : SpecClause lam lam0 δ) : Real.exp (-δ) * ∑ α, lam0 α ≤ ∑ α, lam α := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun α _ => (h α).1

/-- The normalized spectra are within `e^{2δ}`. DERIVED: `2` the two normalizations. -/
theorem p_le_of_spec (h : SpecClause lam lam0 δ) (h0 : ∀ α, 0 ≤ lam0 α) (hS : 0 < ∑ α, lam0 α) (α : κ') :
    lam α / ∑ β, lam β ≤ Real.exp (2 * δ) * (lam0 α / ∑ β, lam0 β) := by
  have hl0 : 0 ≤ lam α := le_trans (mul_nonneg (Real.exp_pos _).le (h0 α)) (h α).1
  have hSl : Real.exp (-δ) * ∑ β, lam0 β ≤ ∑ β, lam β := sum_ge_of_spec h
  have hpos : 0 < Real.exp (-δ) * ∑ β, lam0 β := mul_pos (Real.exp_pos _) hS
  calc lam α / ∑ β, lam β ≤ lam α / (Real.exp (-δ) * ∑ β, lam0 β) :=
        div_le_div_of_nonneg_left hl0 hpos hSl
    _ ≤ (Real.exp δ * lam0 α) / (Real.exp (-δ) * ∑ β, lam0 β) :=
        div_le_div_of_nonneg_right (h α).2 hpos.le
    _ = Real.exp δ / Real.exp (-δ) * (lam0 α / ∑ β, lam0 β) := mul_div_mul_comm _ _ _ _
    _ = Real.exp (2 * δ) * (lam0 α / ∑ β, lam0 β) := by
        rw [← Real.exp_sub, show δ - -δ = 2 * δ by ring]

/-- The Rényi-½ count moves by at most `e^{2δ}`. DERIVED: `2` the square and the two normalizations. -/
theorem spRenyi_le_of_spec (h : SpecClause lam lam0 δ) (h0 : ∀ α, 0 ≤ lam0 α) (hS : 0 < ∑ α, lam0 α) :
    spRenyi lam ≤ Real.exp (2 * δ) * spRenyi lam0 := by
  unfold spRenyi
  have hs : ∀ α, Real.sqrt (lam α / ∑ β, lam β) ≤ Real.exp δ * Real.sqrt (lam0 α / ∑ β, lam0 β) :=
    fun α => by
      calc Real.sqrt (lam α / ∑ β, lam β) ≤ Real.sqrt (Real.exp (2 * δ) * (lam0 α / ∑ β, lam0 β)) :=
            Real.sqrt_le_sqrt (p_le_of_spec h h0 hS α)
        _ = Real.exp δ * Real.sqrt (lam0 α / ∑ β, lam0 β) := by
            rw [Real.sqrt_mul (Real.exp_pos _).le, show (2 : ℝ) * δ = δ + δ by ring, Real.exp_add,
              Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsum : ∑ α, Real.sqrt (lam α / ∑ β, lam β)
      ≤ Real.exp δ * ∑ α, Real.sqrt (lam0 α / ∑ β, lam0 β) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun α _ => hs α
  calc (∑ α, Real.sqrt (lam α / ∑ β, lam β)) ^ 2
      ≤ (Real.exp δ * ∑ α, Real.sqrt (lam0 α / ∑ β, lam0 β)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _) hsum 2
    _ = Real.exp (2 * δ) * (∑ α, Real.sqrt (lam0 α / ∑ β, lam0 β)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num

/-- A rung of the comparison spectrum holds at most the free rung `M` lower, when `e^{2δ} a^{2M} ≤ 1`.
DERIVED: `1`, `2` as in `levelCount`. -/
theorem levelCount_le_of_spec (h : SpecClause lam lam0 δ) (h0 : ∀ α, 0 ≤ lam0 α)
    (hS : 0 < ∑ α, lam0 α) {a : ℝ} (ha0 : 0 < a) {M : ℕ} (hM : Real.exp (2 * δ) * a ^ (2 * M) ≤ 1)
    (i : ℕ) : levelCount lam a i ≤ levelCount lam0 a (i + M) := by
  unfold levelCount
  refine Finset.card_le_card fun α hα => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  have hp := p_le_of_spec h h0 hS α
  have hq0 : 0 ≤ lam0 α / ∑ β, lam0 β := div_nonneg (h0 α) hS.le
  have haM : 0 < a ^ (2 * M) := pow_pos ha0 _
  calc a ^ (2 * (i + M + 1)) = a ^ (2 * (i + 1)) * a ^ (2 * M) := by
        rw [← pow_add]
        congr 1
        ring
    _ < (Real.exp (2 * δ) * (lam0 α / ∑ β, lam0 β)) * a ^ (2 * M) :=
        mul_lt_mul_of_pos_right (hα.trans_le hp) haM
    _ = (Real.exp (2 * δ) * a ^ (2 * M)) * (lam0 α / ∑ β, lam0 β) := by ring
    _ ≤ 1 * (lam0 α / ∑ β, lam0 β) := mul_le_mul_of_nonneg_right hM hq0
    _ = lam0 α / ∑ β, lam0 β := one_mul _

/-- A nonnegative spectrum reads at least one mode. DERIVED: `0`, `1` the bounds of a probability. -/
theorem one_le_spDim {w : κ' → ℝ} (hw : ∀ α, 0 ≤ w α) : 1 ≤ spDim w := by
  unfold spDim
  apply Real.one_le_exp
  refine Finset.sum_nonneg fun α _ => ?_
  have hS : 0 ≤ ∑ β, w β := Finset.sum_nonneg fun β _ => hw β
  exact Real.negMulLog_nonneg (div_nonneg (hw α) hS)
    (div_le_one_of_le₀ (Finset.single_le_sum (fun β _ => hw β) (Finset.mem_univ α)) hS)

end Spec

/-! ### The constants -/

/-- The ladder of one e-fold per rung, as in `FreeLevels.h3_of_freeScreen`. DERIVED: `1/2` one e-fold
per rung of `a²`. -/
def bridgeLadder : ℝ := Real.exp (-(1 / 2))

/-- DERIVED: `0` the sign. -/
theorem bridgeLadder_pos : 0 < bridgeLadder := Real.exp_pos _

/-- DERIVED: `1` the bound. -/
theorem bridgeLadder_lt_one : bridgeLadder < 1 := Real.exp_lt_one_iff.2 (by norm_num)

/-- The free count bound `D₀ = A_κ² e ((1/τ + π²)/4)²` of `FreeLevels.free_h3_local` at `d = 4`.
DERIVED: `2` the half-dimension; `4` and `π` as in `FreeLevels`. -/
def freeD (τ κ : ℝ) : ℝ := renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 * ((1 / τ + π ^ 2) / 4) ^ 2

/-- The free level constant `c₀ = π⁴ e (1 − 2 · 4 (1 + κ) log a)²`. DERIVED: as in `FreeLevels`. -/
def freeC (κ : ℝ) : ℝ := (π ^ 2) ^ 2 * Real.exp 1 * (1 - 2 * (((2 * 2 : ℕ) : ℝ) * (1 + κ)) * Real.log bridgeLadder) ^ 2

/-- The rung shift `M = ⌈2δ⌉`. DERIVED: `2` the factor of `e^{2δ}`. -/
def rungShift (δ : ℝ) : ℕ := ⌈2 * δ⌉₊

/-- The Rényi-½ bound `R̄ = e^{2δ} A_κ² e² D₀`. DERIVED: `2` as in `spRenyi_le_of_spec`. -/
def bridgeRenyi (δ τ κ : ℝ) : ℝ := Real.exp (2 * δ) * (renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 ^ 2) * freeD τ κ

/-- The level bound `c₀ D₀ (M + 1)²`. DERIVED: `1` the shift; `2` the exponent `r`. -/
def bridgeLevel (δ τ κ : ℝ) : ℝ := freeC κ * freeD τ κ * ((rungShift δ : ℝ) + 1) ^ 2

/-- DERIVED: `0` the sign. -/
theorem bridgeLevel_nonneg (δ τ κ : ℝ) : 0 ≤ bridgeLevel δ τ κ := by
  unfold bridgeLevel freeC freeD
  positivity

/-- The shift absorbs the excess: `e^{2δ} a^{2M} ≤ 1`. DERIVED: `2`, `1/2` as in `bridgeLadder`, `rungShift`. -/
theorem shift_ok (δ : ℝ) : Real.exp (2 * δ) * bridgeLadder ^ (2 * rungShift δ) ≤ 1 := by
  unfold bridgeLadder
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_one_iff]
  have h := Nat.le_ceil (2 * δ)
  unfold rungShift
  push_cast
  linarith

section FreeSpec

variable {κ' : Type*} [Fintype κ'] {lam : κ' → ℝ} {τ κ δ : ℝ}

/-- The free side of `FreeSpecAt`: the heat spectrum is positive with positive sum, and it meets
`free_h3_local`. DERIVED: as in `FreeLevels.free_h3_local`. -/
theorem freeSpec_core (hτ : 0 < τ) (hκ : 0 ≤ κ) (h : FreeSpecAt lam τ κ δ) :
    ∃ lam0 : κ' → ℝ, SpecClause lam lam0 δ ∧ (∀ α, 0 ≤ lam0 α) ∧ 0 < ∑ α, lam0 α
      ∧ spDim lam0 ≤ freeD τ κ
      ∧ (∀ i : ℕ, (levelCount lam0 bridgeLadder i : ℝ) ≤ freeC κ * spDim lam0 * ((i : ℝ) + 1) ^ 2)
      ∧ spRenyi lam0 ≤ renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 ^ 2 * spDim lam0 := by
  obtain ⟨K, hK, L, t, w, e, hL, ht, hτσ, hw, htop, hloc, hS⟩ := h
  obtain ⟨hD, hlev, hR⟩ := free_h3_local hK hL ht (m := 2) (by norm_num) hτ hτσ hκ hw htop hloc e rfl
    bridgeLadder_pos bridgeLadder_lt_one
  have hpos : ∀ α, 0 < (heatSpec w (boxU L t K) ∘ e) α := fun α =>
    mul_pos (hw _) (Real.exp_pos _)
  refine ⟨heatSpec w (boxU L t K) ∘ e, hS, fun α => (hpos α).le,
    Finset.sum_pos (fun α _ => hpos α) ⟨e.symm (fun _ => ⟨0, hK⟩), Finset.mem_univ _⟩, hD,
    fun i => (hlev i).trans_eq ?_, hR⟩
  unfold freeC
  ring

/-- `R ≤ R̄`. DERIVED: as in `bridgeRenyi`. -/
theorem freeSpec_renyi (hτ : 0 < τ) (hκ : 0 ≤ κ) (h : FreeSpecAt lam τ κ δ) :
    spRenyi lam ≤ bridgeRenyi δ τ κ := by
  obtain ⟨lam0, hS, h0, hsum, hD, -, hR⟩ := freeSpec_core hτ hκ h
  have hA : 0 ≤ renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 ^ 2 := by positivity
  calc spRenyi lam ≤ Real.exp (2 * δ) * spRenyi lam0 := spRenyi_le_of_spec hS h0 hsum
    _ ≤ Real.exp (2 * δ) * (renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 ^ 2 * spDim lam0) :=
        mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
    _ ≤ Real.exp (2 * δ) * (renyiFactorL 2 κ bridgeLadder ^ 2 * Real.exp 1 ^ 2 * freeD τ κ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hA) (Real.exp_pos _).le
    _ = bridgeRenyi δ τ κ := by unfold bridgeRenyi; ring

/-- The comparison spectrum is nonnegative with positive sum. DERIVED: `0` the signs. -/
theorem freeSpec_nonneg (hτ : 0 < τ) (hκ : 0 ≤ κ) (h : FreeSpecAt lam τ κ δ) :
    (∀ α, 0 ≤ lam α) ∧ 0 < ∑ α, lam α := by
  obtain ⟨lam0, hS, h0, hsum, -⟩ := freeSpec_core hτ hκ h
  refine ⟨fun α => le_trans (mul_nonneg (Real.exp_pos _).le (h0 α)) (hS α).1, ?_⟩
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hsum) (sum_ge_of_spec hS)

/-- `exp H ≤ R̄`. DERIVED: as in `bridgeRenyi`. -/
theorem freeSpec_spDim (hτ : 0 < τ) (hκ : 0 ≤ κ) (h : FreeSpecAt lam τ κ δ) :
    spDim lam ≤ bridgeRenyi δ τ κ := by
  obtain ⟨h0, hsum⟩ := freeSpec_nonneg hτ hκ h
  exact (spDim_le_spRenyi h0 hsum).trans (freeSpec_renyi hτ hκ h)

/-- The level decay in the spectrum's own units: `levelCount_i ≤ c₀ D₀ (M + 1)² · exp H · (i + 1)²`.
DERIVED: `1` the shift; `2` the exponent `r`. -/
theorem freeSpec_level (hτ : 0 < τ) (hκ : 0 ≤ κ) (h : FreeSpecAt lam τ κ δ) (i : ℕ) :
    (levelCount lam bridgeLadder i : ℝ) ≤ bridgeLevel δ τ κ * spDim lam * ((i : ℝ) + 1) ^ 2 := by
  obtain ⟨lam0, hS, h0, hsum, hD, hlev, -⟩ := freeSpec_core hτ hκ h
  obtain ⟨hl0, -⟩ := freeSpec_nonneg hτ hκ h
  have hsh := levelCount_le_of_spec hS h0 hsum bridgeLadder_pos (shift_ok δ) i
  have hc : 0 ≤ freeC κ := by unfold freeC; positivity
  have hD0 : 0 ≤ spDim lam0 := (spDim_pos _).le
  have hM : (0 : ℝ) ≤ (rungShift δ : ℝ) := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hidx : ((i + rungShift δ : ℕ) : ℝ) + 1 ≤ ((rungShift δ : ℝ) + 1) * ((i : ℝ) + 1) := by
    push_cast
    nlinarith
  have h1 : 1 ≤ spDim lam := one_le_spDim hl0
  have hDf : 0 ≤ freeD τ κ := hD0.trans hD
  calc (levelCount lam bridgeLadder i : ℝ) ≤ (levelCount lam0 bridgeLadder (i + rungShift δ) : ℝ) := by exact_mod_cast hsh
    _ ≤ freeC κ * spDim lam0 * (((i + rungShift δ : ℕ) : ℝ) + 1) ^ 2 := hlev _
    _ ≤ freeC κ * freeD τ κ * (((rungShift δ : ℝ) + 1) * ((i : ℝ) + 1)) ^ 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hD hc) (pow_le_pow_left₀ (by positivity) hidx 2)
          (by positivity) (mul_nonneg hc hDf)
    _ = bridgeLevel δ τ κ * 1 * ((i : ℝ) + 1) ^ 2 := by unfold bridgeLevel; ring
    _ ≤ bridgeLevel δ τ κ * spDim lam * ((i : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (bridgeLevel_nonneg δ τ κ))
          (by positivity)

end FreeSpec

/-! ### The moments -/

section Moments

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The law clause gives H1's form: at order `q ≤ 2w`, every unit eigenvector's mode has
`ν(e^{2p}) ≤ ((2p)!)^w (e^{δ + 2w} λ)^p`. DERIVED: `e^{2w}` from `ModeHyper.wick_const`; `1` the floor of
`p`; `2` the even power. -/
theorem h1_of_lawClause {ν : MassGap.DLRLimit.State X} {ι : Type*} [Fintype ι] {F : ι → C(X, ℝ)}
    {q w : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hqw : q ≤ 2 * w) (h : LawClause ν F q δ) (p : ℕ) {lam : ℝ}
    {v : ι → ℝ} (hv : IsUnitEig (gram ν F) lam v) :
    ν ((∑ y, v y • F y) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) ^ w * (Real.exp (δ + 2 * w) * lam) ^ p := by
  have hlam : 0 ≤ lam := by
    rw [← ModeHyper.state_unitEig_sq ν F hv]
    exact ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    exact le_of_eq ν.map_one
  have hb := h p lam v hv
  have hwc := ModeHyper.wick_const hp hqw
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h2p : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
  have he : Real.exp δ ≤ Real.exp δ ^ p := by
    calc Real.exp δ = Real.exp δ ^ 1 := (pow_one _).symm
      _ ≤ Real.exp δ ^ p := pow_le_pow_right₀ (Real.one_le_exp hδ) hp
  calc ν ((∑ y, v y • F y) ^ (2 * p)) ≤ Real.exp δ * ((2 * (p : ℝ) - 1) ^ q) ^ p * lam ^ p := hb
    _ ≤ Real.exp δ ^ p * (((2 * p).factorial : ℝ) ^ w * Real.exp (2 * w) ^ p) * lam ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul he hwc (pow_nonneg (pow_nonneg h2p q) p)
          (pow_nonneg (Real.exp_pos _).le p)) (pow_nonneg hlam p)
    _ = ((2 * p).factorial : ℝ) ^ w * (Real.exp (δ + 2 * w) * lam) ^ p := by
        rw [Real.exp_add, mul_pow, mul_pow]
        ring

end Moments

/-! ## 4. The free reading meets the comparison -/

section FreeCube

/-- On the spin cube every screen of degree-`q` readings meets the law clause at `δ = 0`, at every order,
screen and number of spins (`ModeHyper.bonami`). DERIVED: `0` the free value; `2` the even power. -/
theorem lawClause_cube {m : ℕ} {ι : Type*} [Fintype ι] (F : ι → C(Fin m → Bool, ℝ)) {q : ℕ}
    (hF : ∀ y, ModeHyper.Deg m q (F y)) : LawClause (cubeState m) F q 0 := by
  intro p lam v hv
  set G := ∑ y, v y • F y with hG
  have hcoe : ∀ x, G x = ∑ y, v y * F y x := fun x => by
    simp only [hG, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hdeg : ModeHyper.Deg m q (fun x => G x) := by
    have := ModeHyper.deg_sum Finset.univ v (fun y => (F y : (Fin m → Bool) → ℝ)) hF
    simpa only [← hcoe] using this
  have hvar := ModeHyper.state_unitEig_sq (cubeState m) F hv
  rw [← hG] at hvar
  rw [Real.exp_zero, one_mul]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp only [mul_zero, pow_zero, mul_one]
    exact le_of_eq (cubeState m).map_one
  have hb := ModeHyper.bonami m q (fun x => G x) hdeg p hp
  have h2 : cubeState m (G ^ 2) = ModeHyper.avg m (fun x => G x ^ 2) := by
    rw [ModeHyper.cubeState_eq]; rfl
  have h2p : cubeState m (G ^ (2 * p)) = ModeHyper.avg m (fun x => G x ^ (2 * p)) := by
    rw [ModeHyper.cubeState_eq]; rfl
  rw [h2p]
  rw [← h2, hvar] at hb
  exact hb

end FreeCube

/-! ## 5. The spike test -/

section Spike

/-- The spike's one-site screen has the unit eigenvector `1` at `2^m`. DERIVED: `1` the unit vector; `2`
the variance. -/
theorem spike_unitEig (m : ℕ) :
    IsUnitEig (gram (cubeState m) (fun _ : Unit => cubeRead m)) (2 ^ m) (fun _ => 1) := by
  refine ⟨by simp, ?_⟩
  funext y
  simp only [Matrix.mulVec, dotProduct, gram, Fintype.sum_unique, mul_one, Pi.smul_apply, smul_eq_mul]
  rw [← sq, cube_two]

/-- DERIVED: `4 = 2 · 2` the fourth moment; `2` the variance. -/
theorem spike_four (m : ℕ) : cubeState m (cubeRead m ^ 4) = 2 ^ m * (2 ^ m) ^ 2 := by
  rw [cube_four, cube_two]

/-- The comparison is a constraint: for every order `q` and every `δ`, some spike fails the law clause.
DERIVED: `2` the order `p = 2` of the test; `3 = 2 · 2 − 1` Nelson's constant there. -/
theorem lawClause_spike_fails (q : ℕ) (δ : ℝ) :
    ∃ m : ℕ, ¬ LawClause (cubeState m) (fun _ : Unit => cubeRead m) q δ := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Real.exp δ * ((2 * ((2 : ℕ) : ℝ) - 1) ^ q) ^ 2)
    (one_lt_two : (1 : ℝ) < 2)
  refine ⟨m, fun h => ?_⟩
  have h4 : cubeState m (cubeRead m ^ 4) ≤ Real.exp δ * ((2 * ((2 : ℕ) : ℝ) - 1) ^ q) ^ 2 * (2 ^ m) ^ 2 := by
    have h' := h 2 (2 ^ m) (fun _ => 1) (spike_unitEig m)
    simp only [Fintype.sum_unique, one_smul] at h'
    exact h'
  rw [spike_four] at h4
  have hpos : (0 : ℝ) < (2 ^ m) ^ 2 := by positivity
  have := le_of_mul_le_mul_right h4 hpos
  linarith

/-- The load test: for every Wick exponent `w` no `C` gives H1's form over the spike family; the law clause
is what carries the per-mode moments (`h1_of_lawClause`). DERIVED: `2` the order of the test. -/
theorem h1_spike_fails (w : ℕ) :
    ¬ ∃ C : ℝ, ∀ (m p : ℕ) (lam : ℝ) (v : Unit → ℝ),
      IsUnitEig (gram (cubeState m) (fun _ : Unit => cubeRead m)) lam v →
      cubeState m ((∑ y, v y • (fun _ : Unit => cubeRead m) y) ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ w * (C * lam) ^ p := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (((2 * 2).factorial : ℝ) ^ w * C ^ 2)
    (one_lt_two : (1 : ℝ) < 2)
  have h4 : cubeState m (cubeRead m ^ 4) ≤ ((2 * 2).factorial : ℝ) ^ w * (C * 2 ^ m) ^ 2 := by
    have h' := hC m 2 (2 ^ m) (fun _ => 1) (spike_unitEig m)
    simp only [Fintype.sum_unique, one_smul] at h'
    exact h'
  rw [spike_four, mul_pow, ← mul_assoc] at h4
  have hpos : (0 : ℝ) < (2 ^ m) ^ 2 := by positivity
  have := le_of_mul_le_mul_right h4 hpos
  linarith

end Spike

/-! ## 2. The bridge on the lattice -/

section Lattice

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute MassGap.MeasuredSpacing MassGap.ZoomFree
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ} [NeZero N]

/-- The free order of one lattice factor `(W, flag)`: `|W| + 2`. It covers the leading free degree of every
factor (argued): `2` at a single letter of the imaginary part (`BulkBound.facV_p1`: `p1` reads
`N − Re tr U_p`), `3` at a single letter of the real part (`Im tr U_p`, leading term `−tr X³/6` at
`N ≥ 3`), and `|W|` or `|W| + 1` at a word of length `|W| ≥ 2`. DERIVED: `2` the quadratic order of a
single letter, plus the one cubic step of the other part. -/
def factorOrd (p : Word × Bool) : ℕ := p.1.length + 2

/-- The free chaos order of a channel's reading: the sum of the factor orders of the monomial, `2` at a
plaquette (one quadratic factor). DERIVED: `2` the plaquette's quadratic order. -/
def chaosOrd : MIx → ℕ
  | Sum.inl i => (i.1.map factorOrd).sum
  | Sum.inr _ => 2

/-- The Wick index of a channel, `⌈chaosOrd / 2⌉`; `1` at a plaquette. DERIVED: `1`, `2` the ceiling. -/
def wickB (j : MIx) : ℕ := (chaosOrd j + 1) / 2

/-- DERIVED: `2` as in `wickB`. -/
theorem chaosOrd_le_two_wickB (j : MIx) : chaosOrd j ≤ 2 * wickB j := by
  unfold wickB
  omega

/-- The plaquette's Wick index is `1`. DERIVED: `1`, `2` as in `wickB`. -/
theorem wickB_plaq (q : MassGap.GibbsSpec.IPlaq) : wickB (Sum.inr q) = 1 := by
  unfold wickB chaosOrd
  norm_num

/-- A single letter of the real part has factor order `3`: the cubic leading term of `Im tr U_p` is
covered. DERIVED: `3 = 1 + 2`. -/
theorem factorOrd_true_letter (l : Letter) : 3 ≤ factorOrd ([l], true) := by
  simp [factorOrd]

/-- A word of length `L` has factor order `L + 2 ≥ L + 1`. DERIVED: `1`, `2` as in `factorOrd`. -/
theorem factorOrd_word (p : Word × Bool) : p.1.length + 1 ≤ factorOrd p := by
  unfold factorOrd
  omega

/-- At the single-trace factor `p1` the order `3` covers its free degree `2`, its canonical dimension.
DERIVED: `2`, `3` as in `factorOrd`. -/
theorem factorOrd_p1 : cdim [BulkBound.p1] ≤ factorOrd BulkBound.p1 := by
  simp [cdim, factorOrd, BulkBound.p1, letDim]

/-- At the tower monomial `mono n` the order is `6(n + 1)`. DERIVED: `2`, `3` as in `BulkBound.mono`,
`factorOrd`; `6 = 2 · 3`, `2(n + 1)` factors `p1` each of order `3`. -/
theorem chaosOrd_jn_eq (n : ℕ) : chaosOrd (Sum.inl (BulkBound.jn n)) = 6 * (n + 1) := by
  show ((BulkBound.mono n).map factorOrd).sum = 6 * (n + 1)
  simp [BulkBound.mono, BulkBound.p1, factorOrd, List.map_replicate, List.sum_replicate]
  ring

/-- At `mono n` the order covers the free degree `4(n + 1) = d` (`BulkBound.cdim_mono`). DERIVED: `4`, `6`
as above. -/
theorem chaosOrd_jn (n : ℕ) : mDim (Sum.inl (BulkBound.jn n)) ≤ chaosOrd (Sum.inl (BulkBound.jn n)) := by
  have hd : mDim (Sum.inl (BulkBound.jn n)) = 4 * (n + 1) := BulkBound.cdim_mono n
  rw [hd, chaosOrd_jn_eq]
  omega

/-- `ZoomFree.wickIx` undercounts the tower: at `mono n` it is `n + 1`, the bridge's index `3(n + 1)`.
DERIVED: `3`, `4` as in `wickIx`. -/
theorem wickIx_lt_wickB_jn (n : ℕ) : wickIx (Sum.inl (BulkBound.jn n)) < wickB (Sum.inl (BulkBound.jn n)) := by
  have hd : mDim (Sum.inl (BulkBound.jn n)) = 4 * (n + 1) := BulkBound.cdim_mono n
  show (mDim (Sum.inl (BulkBound.jn n)) + 3) / 4 < (chaosOrd (Sum.inl (BulkBound.jn n)) + 1) / 2
  rw [hd, chaosOrd_jn_eq]
  omega

/-- The comparison at one step, aperture and channel: the law clause of the screen at the free chaos order
`chaosOrd j`, and the spectral clause of its Gram spectrum. DERIVED: `chaosOrd` as there. -/
def BridgeAt (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) (δ τ κ : ℝ) : Prop :=
  LawClause (stateK (NeZero.ne N) k) (screen Wf k s j) (chaosOrd j) δ ∧ FreeSpecAt (apEig Wf k s j) τ κ δ

/-- The bridge: one `δ ≥ 0` (and the free data `τ > 0`, `κ ≥ 0`) with, at every aperture `s ∈ (0, b]`,
eventually in the step, the comparison at every channel. DERIVED: `0` the signs. -/
def FreeComparable (Wf : ℝ → ConfFlow N) (b : ℝ) : Prop :=
  ∃ δ τ κ : ℝ, 0 ≤ δ ∧ 0 < τ ∧ 0 ≤ κ ∧
    ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ j : MIx, BridgeAt Wf k s j δ τ κ

/-- The bridge gives the H3 clause of `ApertureCountAt` exactly, at the ladder `e^{−1/2}` and `r = 2`.
DERIVED: `2` the exponent `r = d/2`. -/
theorem h3_of_freeComparable {Wf : ℝ → ConfFlow N} {b : ℝ} (h : FreeComparable Wf b) :
    ∃ (D c a : ℝ) (r : ℕ), 0 < a ∧ a < 1 ∧ 0 ≤ c ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop,
      ∀ j : MIx, apDim Wf k s j ≤ D
        ∧ ∀ i : ℕ, (levelCount (apEig Wf k s j) a i : ℝ) ≤ c * apDim Wf k s j * ((i : ℝ) + 1) ^ r := by
  obtain ⟨δ, τ, κ, -, hτ, hκ, hB⟩ := h
  refine ⟨bridgeRenyi δ τ κ, bridgeLevel δ τ κ, bridgeLadder, 2, bridgeLadder_pos, bridgeLadder_lt_one,
    bridgeLevel_nonneg δ τ κ, fun s hs hsb => ?_⟩
  filter_upwards [hB s hs hsb] with k hk j
  obtain ⟨-, hS⟩ := hk j
  exact ⟨freeSpec_spDim hτ hκ hS, freeSpec_level hτ hκ hS⟩

/-- The bridge gives H1's form at every channel, with `C_j = e^{δ + 2 wickB j}`. DERIVED: `2` as in
`h1_of_lawClause`. -/
theorem h1_of_freeComparable {Wf : ℝ → ConfFlow N} {b : ℝ} (h : FreeComparable Wf b) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ (j : MIx) (p : ℕ) (lam : ℝ)
      (v : (Fin 4 → Fin (apL N k s)) → ℝ),
      IsUnitEig (gram (stateK (NeZero.ne N) k) (screen Wf k s j)) lam v →
      stateK (NeZero.ne N) k ((∑ y, v y • screen Wf k s j y) ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickB j * (Real.exp (δ + 2 * wickB j) * lam) ^ p := by
  obtain ⟨δ, τ, κ, hδ, -, -, hB⟩ := h
  refine ⟨δ, hδ, fun s hs hsb => ?_⟩
  filter_upwards [hB s hs hsb] with k hk j p lam v hv
  exact h1_of_lawClause hδ (chaosOrd_le_two_wickB j) (hk j).1 p hv

/-- `FreeScreenSpectrum` gives the spectral clause at `δ = 0`. DERIVED: `0` the free value. -/
theorem freeSpec_of_freeScreen {Wf : ℝ → ConfFlow N} {b τ κ : ℝ} (h : FreeScreenSpectrum Wf b τ κ) :
    ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ j : MIx, FreeSpecAt (apEig Wf k s j) τ κ 0 := by
  intro s hs hsb
  filter_upwards [h s hs hsb] with k hk j
  obtain ⟨K, hK, L, t, w, e, hL, ht, hτσ, hw, htop, hloc, heq⟩ := hk j
  exact ⟨K, hK, L, t, w, e, hL, ht, hτσ, hw, htop, hloc, by rw [heq]; exact specClause_refl _⟩

/-- The free reading meets the bridge at `δ = 0`: `FreeScreenSpectrum` and the law clause at `δ = 0`.
DERIVED: `0` the free value. -/
theorem freeComparable_of_free {Wf : ℝ → ConfFlow N} {b τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 ≤ κ)
    (hS : FreeScreenSpectrum Wf b τ κ)
    (hL : ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ j : MIx,
      LawClause (stateK (NeZero.ne N) k) (screen Wf k s j) (chaosOrd j) 0) :
    FreeComparable Wf b :=
  ⟨0, τ, κ, le_rfl, hτ, hκ, fun s hs hsb => by
    filter_upwards [freeSpec_of_freeScreen hS s hs hsb, hL s hs hsb] with k h1 h2 j
    exact ⟨h2 j, h1 j⟩⟩

/-- `ZoomFree.ApertureSettlesAt` with the Wick index of each channel a parameter `wix`; the plaquette and
af clauses unchanged. At `wix = ZoomFree.wickIx` it is `ApertureSettlesAt`. DERIVED: as in
`ApertureSettlesAt`. -/
def ApertureSettlesAtW (wix : MIx → ℕ) (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ (M : ℕ) (σ : ℝ) (e : ℕ → ℝ → Fin M → C(Cfg N, ℝ)), 1 ≤ M ∧ 0 < σ ∧
      (∀ k s, msFlow Wf k s j = ∑ i, e k s i)
      ∧ (∀ k s i, stateK (NeZero.ne N) k (e k s i) = 0)
      ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ, ∀ᶠ k in atTop, ∀ i,
        stateK (NeZero.ne N) k (e k s i ^ (2 * p))
          ≤ ((2 * p).factorial : ℝ) ^ wix j * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p))
    ∧ (∃ (MP : ℕ) (eP : ℕ → MassGap.GibbsSpec.IPlaq → Fin MP → C(Cfg N, ℝ)) (σP E : ℝ),
        1 ≤ MP ∧ 0 < σP ∧
        (∀ k q, msFlow Wf k b (Sum.inr q) = ∑ i, eP k q i)
        ∧ (∀ k q i, stateK (NeZero.ne N) k (eP k q i) = 0)
        ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
          |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
          ∧ ∀ i m, stateK (NeZero.ne N) k (eP k q i ^ (2 * m)) ≤ ((2 * m).factorial : ℝ) * σP ^ (2 * m))
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- `ZoomFree.scaleControlChan_of_aperture` at a per-channel index `wix`: the proof reads the index only as
the channel's existential index of `ScaleControlChan`. DERIVED: as in `scaleControlChan_of_aperture`. -/
theorem scaleControlChan_of_apertureW (wix : MIx → ℕ) {b₀ : ℝ} (hb₀ : 0 ≤ b₀) {z : Chan → ℕ → ℝ} {b : ℝ}
    (hb : 0 < b) {Wf : ℝ → ConfFlow N} (h : ApertureSettlesAtW wix b₀ z b Wf) : ScaleControlChan b Wf := by
  obtain ⟨u, γ, γP, hu, hchan, ⟨MP, eP, σP, E, hMP, hσP, hdecP, -, hobs⟩, -⟩ := h
  refine ⟨fun i => max (-γ i) 0, max (-γP) 0, ⟨fun j => ?_, ?_⟩⟩
  · obtain ⟨M, σ, e, hM, hσ, hdec, -, hj⟩ := hchan j
    obtain ⟨Q, hQ, hQb⟩ := runG_rpow_neg_le hb₀ hu (-anom γ γP j)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have ht : 0 < ((M : ℝ) * σ * Q)⁻¹ := inv_pos.2 (mul_pos (mul_pos hM0 hσ) hQ)
    refine ⟨wix j, ((M : ℝ) * σ * Q)⁻¹, 1, ht, fun s hs hsb p => ?_⟩
    filter_upwards [hj s hs hsb p] with k hk
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j := ⟨_, rfl⟩
    rw [← hc] at hk
    have hsd : 0 < s ^ mDim j := pow_pos hs _
    have hc0 : 0 ≤ c := by
      rw [hc]
      exact div_nonneg (mul_nonneg hσ.le (Real.rpow_nonneg (runG_pos hb₀ hu s).le _)) hsd.le
    have hmom := state_pow_sum_le (stateK (NeZero.ne N) k) hM (e k s) (even_two_mul p) hk
    rw [← hdec] at hmom
    have hmu := msMu_pos ht (fun i => max (-γ i) 0) (max (-γP) 0) hs j
    have hcmu :
        (M : ℝ) * c ≤ (msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s)⁻¹ := by
      rw [msMu_anom_neg, inv_div, hc, mul_div_assoc', div_le_div_iff₀ hsd (mul_pos ht hsd)]
      have hQs := hQb s
      rw [neg_neg] at hQs
      have hg : runG b₀ u s ^ anom γ γP j / Q ≤ afLog (max (-anom γ γP j) 0) s :=
        (div_le_iff₀ hQ).2 (by linarith)
      have e2 : (M : ℝ) * (σ * runG b₀ u s ^ anom γ γP j) * (((M : ℝ) * σ * Q)⁻¹ * s ^ mDim j)
          = runG b₀ u s ^ anom γ γP j / Q * s ^ mDim j := by
        field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_right hg hsd.le
    unfold ScaleChanPM
    calc stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ (M : ℝ) ^ (2 * p) * (((2 * p).factorial : ℝ) ^ wix j * c ^ (2 * p)) := hmom
      _ = ((2 * p).factorial : ℝ) ^ wix j * ((M : ℝ) * c) ^ (2 * p) := by ring
      _ ≤ ((2 * p).factorial : ℝ) ^ wix j
            * ((msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s)⁻¹) ^ (2 * p) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hM0.le hc0) hcmu _)
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ((2 * p).factorial : ℝ) ^ wix j
            / msMu ((M : ℝ) * σ * Q)⁻¹ (fun i => max (-γ i) 0) (max (-γP) 0) j s ^ (2 * p) * 1 := by
          rw [inv_pow, mul_one, div_eq_mul_inv]
  · have hM0 : (0 : ℝ) < MP := by exact_mod_cast hMP
    have hM' := hM0.ne'
    have hσ' := hσP.ne'
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (2 * σP * MP)⁻¹ := ⟨_, rfl⟩
    have hl0 : 0 < l := by
      rw [hl]
      exact inv_pos.2 (mul_pos (mul_pos two_pos hσP) hM0)
    have hlM : l * MP = (2 * σP)⁻¹ := by
      rw [hl]
      field_simp
    have hb4 : 0 < 2 * σP * MP * b ^ 4 := mul_pos (mul_pos (mul_pos two_pos hσP) hM0) (pow_pos hb 4)
    refine ⟨afLog (max (-γP) 0) b / (2 * σP * MP * b ^ 4), Real.exp (l * E) * 2 * (4 / 3),
      div_pos (afLog_pos _ _) hb4, ?_⟩
    filter_upwards [hobs] with k hk q
    obtain ⟨hmean, hmode⟩ := hk q
    have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
    have ha4 : 0 < dySpacing N k ^ 4 := pow_pos ha 4
    have hcosh : ∀ i, stateK (NeZero.ne N) k (coshC ((2 * σP)⁻¹ • eP k q i)) ≤ 4 / 3 :=
      fun i => state_coshC_le (stateK (NeZero.ne N) k) (eP k q i) hσP (hmode i)
    have hmu : msMu (afLog (max (-γP) 0) b / (2 * σP * MP * b ^ 4)) (fun i => max (-γ i) 0) (max (-γP) 0)
        (Sum.inr q) b = l := by
      have hA := (afLog_pos (max (-γP) 0) b).ne'
      have hb' := hb.ne'
      rw [msMu_inr, hl]
      field_simp
    unfold ScaleChan
    rw [hmu, mDim_inr]
    have hpt : ∀ U, expC ((l / dySpacing N k ^ 4) • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1) U
        ≤ ((Real.exp (l * E) * 2 / MP) • ∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) U := by
      intro U
      have hXU : msFlow Wf k b (Sum.inr q) U = (dySpacing N k ^ 4)⁻¹
          * (((Wf b).fieldMap k (mField (Sum.inr q))).1 U
            - stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 * 1) := rfl
      have hY : ((Wf b).fieldMap k (mField (Sum.inr q))).1 U
          = dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U
            + stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1 := by
        rw [hXU, ← mul_assoc, mul_inv_cancel₀ ha4.ne', one_mul]
        ring
      have hsumU : msFlow Wf k b (Sum.inr q) U = ∑ i, eP k q i U := by
        rw [hdecP k q]
        simp only [ContinuousMap.coe_sum, Finset.sum_apply]
      have hYU : |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ dySpacing N k ^ 4 * ∑ i, |eP k q i U| + E * dySpacing N k ^ 4 := by
        rw [hY]
        have h1 := abs_add_le (dySpacing N k ^ 4 * msFlow Wf k b (Sum.inr q) U)
          (stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1)
        have h2 : |msFlow Wf k b (Sum.inr q) U| ≤ ∑ i, |eP k q i U| := by
          rw [hsumU]
          exact Finset.abs_sum_le_sum_abs _ _
        rw [abs_mul, abs_of_pos ha4] at h1
        linarith [mul_le_mul_of_nonneg_left h2 ha4.le]
      simp only [expC_apply, ContinuousMap.smul_apply, msAbs_apply, smul_eq_mul, ContinuousMap.coe_sum,
        Finset.sum_apply]
      show Real.exp (l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
        ≤ Real.exp (l * E) * 2 / MP * ∑ i, Real.cosh ((2 * σP)⁻¹ * eP k q i U)
      have hexp : l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
          ≤ l * ∑ i, 1 * |eP k q i U| + l * E := by
        calc l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|
            ≤ l / dySpacing N k ^ 4 * (dySpacing N k ^ 4 * ∑ i, |eP k q i U| + E * dySpacing N k ^ 4) :=
              mul_le_mul_of_nonneg_left hYU (div_nonneg hl0.le ha4.le)
          _ = l * ∑ i, 1 * |eP k q i U| + l * E := by
              simp only [one_mul]
              field_simp
      have hJ := MassGap.FlowUV.exp_mul_wsum_le Finset.univ (fun _ : Fin MP => (1 : ℝ))
        (fun i => |eP k q i U|) (fun _ _ => zero_le_one) hM0 (by simp) l
      calc Real.exp (l / dySpacing N k ^ 4 * |((Wf b).fieldMap k (mField (Sum.inr q))).1 U|)
          ≤ Real.exp (l * ∑ i, 1 * |eP k q i U| + l * E) := Real.exp_le_exp.2 hexp
        _ = Real.exp (l * E) * Real.exp (l * ∑ i, 1 * |eP k q i U|) := by
            rw [Real.exp_add, mul_comm]
        _ ≤ Real.exp (l * E) * ∑ i, (1 / (MP : ℝ)) * Real.exp (l * MP * |eP k q i U|) :=
            mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le
        _ ≤ Real.exp (l * E) * ∑ i, (1 / (MP : ℝ)) * (2 * Real.cosh ((2 * σP)⁻¹ * eP k q i U)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hab : l * MP * |eP k q i U| = |(2 * σP)⁻¹ * eP k q i U| := by
              rw [hlM, abs_mul, abs_of_pos (inv_pos.2 (mul_pos two_pos hσP))]
            rw [hab]
            exact exp_abs_le_two_cosh _
        _ = Real.exp (l * E) * 2 / MP * ∑ i, Real.cosh ((2 * σP)⁻¹ * eP k q i U) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    have hsum : stateK (NeZero.ne N) k (∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) ≤ MP * (4 / 3) := by
      rw [(stateK (NeZero.ne N) k).map_sum]
      calc ∑ i, stateK (NeZero.ne N) k (coshC ((2 * σP)⁻¹ • eP k q i)) ≤ ∑ _i : Fin MP, (4 / 3 : ℝ) :=
            Finset.sum_le_sum fun i _ => hcosh i
        _ = MP * (4 / 3) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc stateK (NeZero.ne N) k (expC ((l / dySpacing N k ^ 4)
          • msAbs ((Wf b).fieldMap k (mField (Sum.inr q))).1))
        ≤ stateK (NeZero.ne N) k ((Real.exp (l * E) * 2 / MP) • ∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) :=
          (stateK (NeZero.ne N) k).mono hpt
      _ = Real.exp (l * E) * 2 / MP * stateK (NeZero.ne N) k (∑ i, coshC ((2 * σP)⁻¹ • eP k q i)) :=
          (stateK (NeZero.ne N) k).map_smul _ _
      _ ≤ Real.exp (l * E) * 2 / MP * (MP * (4 / 3)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (l * E) * 2 * (4 / 3) := by field_simp

/-- `ZoomFree.ApertureOneAt` with the Wick index of each channel a parameter `wix`. DERIVED: as in
`ApertureOneAt`. -/
def ApertureOneAtW (wix : MIx → ℕ) (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ, ∀ᶠ k in atTop,
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wix j * (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p))
    ∧ (∃ σP E : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ ∀ m : ℕ, stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ (2 * m))
          ≤ ((2 * m).factorial : ℝ) * σP ^ (2 * m))
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- One mode is a witness (`ZoomFree.apertureSettlesAt_iff_one`, the reverse direction, at the index `wix`).
DERIVED: `1` the one mode. -/
theorem apertureSettlesAtW_of_one (wix : MIx → ℕ) {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (h : ApertureOneAtW wix b₀ z b Wf) : ApertureSettlesAtW wix b₀ z b Wf := by
  obtain ⟨u, γ, γP, hu, hchan, ⟨σP, E, hσP, hobs⟩, haf⟩ := h
  refine ⟨u, γ, γP, hu, fun j => ?_, ⟨1, fun k q _ => msFlow Wf k b (Sum.inr q), σP, E, le_rfl, hσP,
    fun k q => by rw [Fin.sum_univ_one], fun k q _ => state_msFlow Wf k b _, ?_⟩, haf⟩
  · obtain ⟨σ, hσ, hj⟩ := hchan j
    refine ⟨1, σ, fun k s _ => msFlow Wf k s j, le_rfl, hσ, fun k s => by rw [Fin.sum_univ_one],
      fun k s _ => state_msFlow Wf k s j, fun s hs hsb p => ?_⟩
    filter_upwards [hj s hs hsb p] with k hk _
    exact hk
  · filter_upwards [hobs] with k hk q
    exact ⟨(hk q).1, fun _ m => (hk q).2 m⟩

/-! ## 6. The root -/

/-- `ApertureCountAt` with H1 and H3 replaced by the bridge; H2, the plaquette observable and (af)
unchanged. DERIVED: as in `ApertureCountAt`. -/
def ApertureBridgeAt (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧ FreeComparable Wf b
    ∧ (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop,
        stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) ≤ (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ 2)
    ∧ (∃ σP E : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ 2) ≤ σP ^ 2)
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

/-- The bridge bundle at the one-loop coefficient of `SU(N)`. DERIVED: no numeral beyond `b0`'s. -/
def ApertureBridge (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ApertureBridgeAt (MassGap.ClayStatement.b0 N) z b Wf

/-- The bridge carries the moments: `ApertureBridgeAt` gives `ApertureOneAtW wickB` at noise
`√(max(C_j R̄, 1)) σⱼ`, `C_j = e^{δ + 2 wickB j}`, and `√(max(e^{δ+2} R̄, 1)) σP` at the plaquettes
(`wickB = 1` there).
DERIVED: `1` the floor; `2` the even powers; `0` the signs. -/
theorem apertureOneAt_of_bridge {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (hb : 0 < b) (h : ApertureBridgeAt b₀ z b Wf) : ApertureOneAtW wickB b₀ z b Wf := by
  obtain ⟨u, γ, γP, hu, ⟨δ, τ, κ, hδ, hτ, hκ, hB⟩, h2, ⟨σP, E, hσP, hobs⟩, haf⟩ := h
  have step : ∀ (s : ℝ) (k : ℕ) (j : MIx) (p : ℕ) (X : ℝ), 0 < s → BridgeAt Wf k s j δ τ κ →
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) ≤ X ^ 2 →
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickB j
          * (Real.sqrt (max (Real.exp (δ + 2 * wickB j) * bridgeRenyi δ τ κ) 1) * X) ^ (2 * p) := by
    intro s k j p X hs hk hk2
    obtain ⟨hL, hS⟩ := hk
    have hC : 0 ≤ Real.exp (δ + 2 * wickB j) := (Real.exp_pos _).le
    have hf : (0 : ℝ) ≤ ((2 * p).factorial : ℝ) ^ wickB j := by positivity
    have hK : 0 ≤ ((2 * p).factorial : ℝ) ^ wickB j * Real.exp (δ + 2 * wickB j) ^ p :=
      mul_nonneg hf (pow_nonneg hC p)
    have hmom := msFlow_moment_le_renyi (Wf := Wf) (k := k) hs j hK fun α =>
      (h1_of_lawClause hδ (chaosOrd_le_two_wickB j) hL p
        (evec_isUnitEig (stateK (NeZero.ne N) k) (screen Wf k s j) α)).trans_eq
        (by rw [mul_pow, mul_assoc]; rfl)
    have hm0 : 0 ≤ stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) :=
      (stateK (NeZero.ne N) k).nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
    exact moment_chain hf hC (sq_nonneg _) hm0 hmom (freeSpec_renyi hτ hκ hS) hk2
  have hlam : ∀ c : ℝ, 0 < Real.sqrt (max c 1) := fun c =>
    Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨u, γ, γP, hu, fun j => ?_,
    ⟨Real.sqrt (max (Real.exp (δ + 2 * ((1 : ℕ) : ℝ)) * bridgeRenyi δ τ κ) 1) * σP, E,
      mul_pos (hlam _) hσP, ?_⟩, haf⟩
  · obtain ⟨σ, hσ, hj⟩ := h2 j
    refine ⟨Real.sqrt (max (Real.exp (δ + 2 * wickB j) * bridgeRenyi δ τ κ) 1) * σ, mul_pos (hlam _) hσ,
      fun s hs hsb p => ?_⟩
    filter_upwards [hB s hs hsb, hj s hs hsb] with k hk1 hk2
    have := step s k j p _ hs (hk1 j) hk2
    calc _ ≤ _ := this
      _ = ((2 * p).factorial : ℝ) ^ wickB j
            * (Real.sqrt (max (Real.exp (δ + 2 * wickB j) * bridgeRenyi δ τ κ) 1) * σ
              * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p) := by ring
  · filter_upwards [hB b hb le_rfl, hobs] with k hk1 hko q
    obtain ⟨hmean, hk2⟩ := hko q
    refine ⟨hmean, fun m => ?_⟩
    have := step b k (Sum.inr q) m σP hb (hk1 _) hk2
    rwa [wickB_plaq, pow_one] at this

/-- The coincident-point core from the bridge: `ApertureBridge z b Wf`, `b > 0` and `Wf b = W` give
`SubstrateCoreCL W z b Wf`, through `apertureSettlesAtW_of_one`, `scaleControlChan_of_apertureW` at the
index `wickB` and `ZoomFree.afCoefficient_of_settles`. DERIVED: `2` the least colour count; `0` the sign. -/
theorem substrateCoreCL_of_bridge (hN2 : 2 ≤ N) {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b) (htop : Wf b = W) (h : ApertureBridge z b Wf) :
    SubstrateCoreCL W z b Wf := by
  have hS := apertureSettlesAtW_of_one wickB (apertureOneAt_of_bridge hb h)
  have hsc := scaleControlChan_of_apertureW wickB b0_pos.le hb hS
  obtain ⟨u, -, -, hu, -, -, G, hG, hset⟩ := hS
  exact ⟨hb, htop, hsc, ⟨G, hG, afCoefficient_of_settles hN2 hu hset⟩⟩

end Lattice

end MassGap.FreeBridge

end

/-! ### The copy over a coupling family -/

namespace MassGap.FreeBridge

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from
  MassGap.FreeBridge.substrateCoreCL_of_bridge

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.FreeBridge

/-! ## 6. The root, along the towers -/

noncomputable section

namespace MassGap.FreeBridge

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl schedAlongG_eq)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverTower (OpenAlongW ApproxAlongW physRangeG_of_physRange energy0G_alongW
  clayStatementOf_of_openW)
open MassGap.ScaleLightCone (ZoomSettlesUV uvConverges_of_zoomSettlesUV)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- The flow-side bundle along `βs` with the bridge: `ExpandMatch.CoreInputsAlongWAM` with the copy of
`ApertureBridge z b Wf` in place of the copy of `ApertureCount z b Wf`, every other field unchanged.
DERIVED: `0` the signs. -/
def CoreInputsAlongWFB (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.FreeBridge.ApertureBridge (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.ExpandMatch.ExpandMatch (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

set_option maxRecDepth 100000 in
/-- `CoreInputsAlongWFB ⇒ OpenAlongW`: as `ExpandMatch.openAlongW_of_coreWAM`, with the coincident-point
core from the copy of `substrateCoreCL_of_bridge` at `cpl βs`. DERIVED: `0` the signs; `2`, `1`, `3`, `4` in
`(2 · 1 + 3)⁴` the unit cube's site count; `2` the least rank. -/
theorem openAlongW_of_coreWFB {βs : ℕ → ℝ} (h : CoreInputsAlongWFB N βs) : OpenAlongW N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, hz, hV, hW, hP, hL, h3⟩ := h
  have S := CouplingGen.Along.FreeBridge.substrateCoreCL_of_bridge (cpl βs) (Fact.out : 2 ≤ N)
    hb htop hZ
  have hcl := CouplingGen.Along.ScaleLightCone.clusterPM_of_zoomSettles (cpl βs) hz
  obtain ⟨⟨t, C, ht, hSE⟩, ⟨Gk, hK, hAF⟩, hNG, hWT, hCO, hA⟩ :=
    CouplingGen.Along.ExpandMatch.coreClausesWAM (cpl βs) (Fact.out : 2 ≤ N) hphys S hE hcl hV hW hP
      hL h3
  have hsched := schedAlongG_eq (N := N) βs
  refine ⟨W.toG, r, physRangeG_of_physRange βs hphys, t * (2 * 1 + 3) ^ 4, C, by positivity, ?_, zri, zwe,
    hri, hwe, μ, ⟨Gk, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hsched]
    exact hSE
  · rw [hsched]
    exact hK
  · rw [constsG_SU N]
    exact hAF
  · rw [hsched]
    exact hNG
  · rw [hsched]
    exact hWT
  · rw [hsched]
    exact hCO
  · unfold ApproxAlongW
    rw [hsched, energy0G_alongW βs W]
    exact hA

/-- The root at `SU(N)` from the strong end, the separated zoom and the bridge: `StrongEnd N`, the
settling window reading and `CoreInputsAlongWFB` along the towers near `0⁺` give `ClayStatementOf (SU N)`.
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_freeBridge (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWFB N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_openW hS (hUV.mono fun _ h βs hT => uvConverges_of_zoomSettlesUV (h βs hT))
    (hF.mono fun _ h βs hT => openAlongW_of_coreWFB (h βs hT))

end MassGap.FreeBridge

end

#print axioms MassGap.FreeBridge.specClause_zero_iff
#print axioms MassGap.FreeBridge.p_le_of_spec
#print axioms MassGap.FreeBridge.spRenyi_le_of_spec
#print axioms MassGap.FreeBridge.levelCount_le_of_spec
#print axioms MassGap.FreeBridge.one_le_spDim
#print axioms MassGap.FreeBridge.shift_ok
#print axioms MassGap.FreeBridge.freeSpec_renyi
#print axioms MassGap.FreeBridge.freeSpec_spDim
#print axioms MassGap.FreeBridge.freeSpec_level
#print axioms MassGap.FreeBridge.h1_of_lawClause
#print axioms MassGap.FreeBridge.lawClause_cube
#print axioms MassGap.FreeBridge.spike_unitEig
#print axioms MassGap.FreeBridge.spike_four
#print axioms MassGap.FreeBridge.lawClause_spike_fails
#print axioms MassGap.FreeBridge.h1_spike_fails
#print axioms MassGap.FreeBridge.chaosOrd_le_two_wickB
#print axioms MassGap.FreeBridge.wickB_plaq
#print axioms MassGap.FreeBridge.factorOrd_true_letter
#print axioms MassGap.FreeBridge.factorOrd_word
#print axioms MassGap.FreeBridge.factorOrd_p1
#print axioms MassGap.FreeBridge.chaosOrd_jn_eq
#print axioms MassGap.FreeBridge.chaosOrd_jn
#print axioms MassGap.FreeBridge.wickIx_lt_wickB_jn
#print axioms MassGap.FreeBridge.scaleControlChan_of_apertureW
#print axioms MassGap.FreeBridge.apertureSettlesAtW_of_one
#print axioms MassGap.FreeBridge.h3_of_freeComparable
#print axioms MassGap.FreeBridge.h1_of_freeComparable
#print axioms MassGap.FreeBridge.freeSpec_of_freeScreen
#print axioms MassGap.FreeBridge.freeComparable_of_free
#print axioms MassGap.FreeBridge.apertureOneAt_of_bridge
#print axioms MassGap.FreeBridge.substrateCoreCL_of_bridge
#print axioms MassGap.CouplingGen.Along.FreeBridge.substrateCoreCL_of_bridge
#print axioms MassGap.FreeBridge.openAlongW_of_coreWFB
#print axioms MassGap.FreeBridge.clayStatementOf_of_freeBridge
