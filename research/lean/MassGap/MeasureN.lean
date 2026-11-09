import Mathlib
import MassGap.RectTorusState
import MassGap.Reflect
import MassGap.GibbsPositive

/-!
# MassGap.MeasureN — the colour count read from the capture by counting phases

The substrate decode is given a capture `ν : State (Cfg N)` and measures each coordinate from it: the mass
(`SubstrateDecode.measMass`), the side of the box (`SubstrateFluxRead.measPeriod`, exact on the torus states by
`RectTorusState.measPeriod_torusState`) and the flux reads (`FluxDuality`). This module measures the colour count
`N`, the remaining coordinate, by counting. It reads the law of the trace of the winding holonomy at the measured
period and counts the phases on the unit circle that leave that law unchanged. On every Wilson torus state with `N ≥ 2`, at every real coupling, the count is exactly `N`; the read applies to
torus captures, not to `periodicState` (§4). No Haar moment is computed. Declarations are in the namespace
`MassGap.MeasureN`.

## 1. The read (defined)

* **`trP L U`**: `tr P`, the trace in `ℂ` of the holonomy `SubstrateFluxRead.polyHol 0 L 0 U` of the line of `L`
  links of direction `0` from the origin. **`trCM L`**: the same map as a continuous function `Cfg N → ℂ`.
* **`rot ω`**: multiplication by `ω` on `ℂ`.
* **`PhaseInv ν L ω`**: for every continuous `f : ℂ → ℝ`, `ν (f ∘ tr P) = ν (f ∘ (ω ·) ∘ tr P)`. This says the law
  of `tr P` under `ν` is unchanged by the rotation `z ↦ ω z`. It is a Prop over `ν` that reads `ν` only on
  continuous functions of one winding trace.
* **`phases ν`**: the phases `ω` with `‖ω‖ = 1` and `PhaseInv ν (measPeriod ν) ω`. The line is read at the measured
  period, so no length is supplied.
* **`measN ν = (phases ν).ncard`**: the number of such phases, and `0` when there are infinitely many
  (`Set.ncard`). On the torus states these phases are the `N`-th roots of unity (`phases_torusState`); that they form a group for
  every capture is argued (invariance composes and inverts), not built.

## 2. The count is exact on the torus states (proved)

* **`cen hN hω`**: for `ω ^ N = 1`, the central element `ω · 1` of `SU(N)` (`norm_of_pow_eq_one`: such an `ω`
  has norm `1`). `cen_comm`: it commutes with every element.
* **`twist c W`**: on the periodic lattice of extent `M + 1`, multiply each link of direction `0` whose base
  has time coordinate `0` by `c` (`tw c l` is `c` there and `1` elsewhere). `hol_twist`: when `c` is central,
  every plaquette holonomy is unchanged. In a `(0, j)` plaquette the two direction-`0` links have the same
  time coordinate, so their factors cancel (`central_hol`), and a degenerate plaquette has holonomy `1` either
  way. So `action_twist`: the Wilson action is unchanged. `twist_mp`: the product Haar measure is preserved
  (left multiplication on each link). **`EW_twist`**: the torus Gibbs expectation is invariant, at every real
  `β` (`LatticeGauge.System.expect_invariant_of_mp`).
* `polyHol_twist`, **`trP_twist`**: the winding line of length `M + 1` from the origin crosses the twisted slice
  exactly once, at its first link, so `tr P` of the twisted configuration is `ω · tr P`.
* **`phaseInv_torusState`**: every `ω` with `ω ^ N = 1` leaves the law of `tr P` (length `M + 1`) unchanged
  under `torusState hN M β`, at every real `β`.
* `pow_eq_one_of_trace` and **`exists_trace_gap`** (pure `SU(N)` linear algebra): if `‖ω‖ = 1` and `ω ^ N ≠ 1`,
  there is `m > 0` with `m ≤ ‖ω tr g − N‖` for every `g ∈ SU(N)`. The case `ω tr g = N` would force every
  diagonal entry of `ω g` to be `1` (the real parts sum to `N` and each is at most `1`). Then each column of
  `g` is a unit vector whose diagonal entry has norm `1`, so `g = ω̄ · 1` and `det g = ω̄ ^ N = 1`.
  Compactness of `SU(N)` turns the pointwise statement into a uniform gap.
* `torusState_pos`: a nonnegative continuous observable that is positive on one periodic configuration has
  positive torus expectation, at every real `β` (the Gibbs weight is positive and product Haar charges every open
  set; the argument is that of `GibbsPositive.corrNum_plaqObs_pos`).
* **`not_phaseInv_torusState`**: for `‖ω‖ = 1` and `ω ^ N ≠ 1`, at every length `L` and every real `β`, the law
  is not invariant. The test `max 0 (m − ‖z − N‖)` has positive expectation, because the flat configuration has
  `tr P = N`. Rotated by `ω` it vanishes identically, because of the gap.
* **`phases_torusState`**: for `N ≥ 2`, `phases (torusState hN M β) = {ω | ω ^ N = 1}`.
* **`measN_torusState`**: for `N ≥ 2`, every extent `M + 1` and every real `β`,
  `measN (torusState hN M β) = N`.

## 3. The power that closes (proved)

* **`moments_vanish`**: for any capture, if `ω` leaves the law of `tr P` unchanged and `ω ^ k ≠ 1`, then
  `ν (Re (tr P)^k) = ν (Im (tr P)^k) = 0`. This is the one-line centre argument, written for a real state.
* **`moments_vanish_torusState`**: on every torus state, at every real `β`, the `k`-th moment of `tr P`
  (length `M + 1`) vanishes for `N ∤ k`. At `β = 0` the winding holonomy is a product of `M + 1` independent Haar links,
  so this is the Haar statement `∫ (tr U)^k dU = 0` for `N ∤ k` (that identification is argued, not built),
  obtained with no Haar computation.

## 4. What is argued, and what is not proved

* By definition (`Set.ncard`), `measN` reads `0` on a capture whose phase set is infinite. Argued, not built: the
  point capture at a configuration with `tr P = 0` is such a capture (its law is the point mass at `0`, invariant
  under every rotation).
* Not proved, and not needed for the count: the nonvanishing half, `ν ((tr P)^N) ≠ 0` on the torus states. At
  `β = 0` it is `∫ (tr U)^N dU = 1` on Haar `SU(N)` (the determinant is the only invariant in `V^{⊗N}`), which
  needs Weyl integration or Schur–Weyl duality, and no module proves it. The count route reads `N` from the
  invariance group, not from the first nonvanishing moment, so it uses only the vanishing half and a support
  argument.
* Not proved: `measN` on `periodicState hN β`. Its measured period is argued to be `0`
  (`SubstrateFluxRead` §1), and then the line has length `0`, `tr P = N` identically, and `PhaseInv` at a phase
  `ω` asks `f(N) = f(ω N)`, which fails for `ω ≠ 1`. The read on that capture is then `1`, not `N`. The winding
  read is a torus read.
* Where `N` enters the read: the type `Cfg N` fixes the size of the matrices, and `tr` sums `N` diagonal entries.
  The read never uses the number `N`. It counts phases of `ℂ`. The bound `|tr g| ≤ N` and the value
  `tr 1 = N` enter the proofs only.

## 5. Parameters

| argument | where | status |
|---|---|---|
| `ν` (the capture) | every read | the input |
| `L` (line length) | `trP`, `PhaseInv` | measured: `measPeriod ν` in `phases`, `measN`; `not_phaseInv_torusState` holds at every `L` |
| `μ = 0`, `x = 0` (winding axis, base point) | `trP` | chosen: one axis and the origin; the torus states are translation invariant, and the count is the same at every base point and axis (argued, by translation and rotation invariance) |
| `ω` (phase) | `PhaseInv`, `phases` | swept over the unit circle |
| `f` (test) | `PhaseInv` | swept over all of `C(ℂ, ℝ)` |
| `N` (colour count) | the type `State (Cfg N)` | measured: `measN`; equal to `N` on the torus states for `N ≥ 2` (`measN_torusState`) |
| `M` (extent minus one) | `torusState`, `twist` | the capture's own; read back as `measPeriod = M + 1` |
| `β` (coupling) | `torusState` | shared; the count is exact at every real `β`, with no sign or size condition |
| `m` (trace gap) | `exists_trace_gap` | existential, from compactness; used only in the proof |
| `k` (power) | `moments_vanish` | swept; the statement is for every `k` with `ω ^ k ≠ 1` |

DERIVED (module-wide): `0` the winding axis, the base point, the twisted time slice and the empty line; `1` the
identity, the unit circle and the unit step; `2` the least colour count at which the period is exact
(`RectTorusState.measPeriod_torusState`); `4` the dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MeasureN

open MeasureTheory
open MassGap.DLRLimit (State)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg)
open MassGap.PeriodicState (torusState torusObs measurable_torusObs)
open MassGap.InfiniteLattice (pullback linkMod siteMod finMod continuous_pullback bounded_of_continuous)
open MassGap.SubstrateFluxRead (polyHol continuous_polyHol lineSite lineSite_self measPeriod)
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge MassGap.WilsonReal
open MassGap.WilsonHypercubic (Link Plaq bd sysWilson)

variable {N : ℕ}

/-! ## 1. The read -/

/-- **The winding trace**: `tr P` of the line of `L` links of direction `0` from the origin. DERIVED: `0` the
axis and the base point. -/
def trP (L : ℕ) (U : Cfg N) : ℂ :=
  Matrix.trace ((polyHol (N := N) 0 L 0 U : SU N) : Matrix (Fin N) (Fin N) ℂ)

/-- DERIVED: `0` the axis and the base point. -/
theorem continuous_trP (L : ℕ) : Continuous (trP (N := N) L) :=
  Continuous.matrix_trace (continuous_subtype_val.comp (continuous_polyHol 0 L 0))

/-- **The winding trace as a continuous map.** DERIVED: no numeral. -/
def trCM (L : ℕ) : C(Cfg N, ℂ) := ⟨trP L, continuous_trP L⟩

/-- **Rotation by `ω`.** DERIVED: no numeral. -/
def rot (ω : ℂ) : C(ℂ, ℂ) := ⟨fun z => ω * z, continuous_const.mul continuous_id⟩

/-- **The law of the winding trace is invariant under the rotation by `ω`.** DERIVED: no numeral. -/
def PhaseInv (ν : State (Cfg N)) (L : ℕ) (ω : ℂ) : Prop :=
  ∀ f : C(ℂ, ℝ), ν (f.comp (trCM L)) = ν ((f.comp (rot ω)).comp (trCM L))

/-- **The centre phases of a capture**: the unit phases leaving the law of the winding trace at the measured
period unchanged. DERIVED: `1` the unit circle. -/
def phases (ν : State (Cfg N)) : Set ℂ := {ω | ‖ω‖ = 1 ∧ PhaseInv ν (measPeriod ν) ω}

/-- **The measured colour count**: the number of centre phases (`0` if infinitely many). DERIVED: no numeral. -/
def measN (ν : State (Cfg N)) : ℕ := (phases ν).ncard

/-! ## 2. The central elements and the slice twist -/

/-- An `N`-th root of unity has norm `1`. DERIVED: `0` the excluded rank; `1` the unit. -/
theorem norm_of_pow_eq_one (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) : ‖ω‖ = 1 := by
  have h : ‖ω‖ ^ N = 1 := by rw [← norm_pow, hω, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg ω) hN).mp h

/-- DERIVED: `1` the unit. -/
theorem mul_star_of_norm {ω : ℂ} (h : ‖ω‖ = 1) : ω * star ω = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

/-- **The central element `ω · 1`** of `SU(N)`, for `ω ^ N = 1`. DERIVED: `0` the excluded rank; `1` the
identity. -/
def cen (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) : SU N :=
  ⟨ω • (1 : Matrix (Fin N) (Fin N) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, Matrix.one_mul,
        mul_star_of_norm (norm_of_pow_eq_one hN hω), one_smul]
    · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hω]⟩

/-- DERIVED: `1` the identity. -/
theorem coe_cen (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) :
    ((cen hN hω : SU N) : Matrix (Fin N) (Fin N) ℂ) = ω • (1 : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- **The central element commutes with every element.** DERIVED: `1` the identity. -/
theorem cen_comm (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) (g : SU N) : cen hN hω * g = g * cen hN hω := by
  apply Subtype.ext
  show ((cen hN hω : SU N) : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ)
    = (g : Matrix (Fin N) (Fin N) ℂ) * ((cen hN hω : SU N) : Matrix (Fin N) (Fin N) ℂ)
  rw [coe_cen, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-- **Holonomy of a plaquette with central factors**: two central factors, each entering once forwards and once
inverted, cancel. DERIVED: no numeral. -/
theorem central_hol {G : Type} [Group G] {a b : G} (ha : ∀ g, a * g = g * a) (hb : ∀ g, b * g = g * b)
    (x y z w : G) : (a * x) * ((b * y) * ((a * z)⁻¹ * (b * w)⁻¹)) = x * (y * (z⁻¹ * w⁻¹)) := by
  calc (a * x) * ((b * y) * ((a * z)⁻¹ * (b * w)⁻¹))
      = x * ((a * (b * (y * z⁻¹))) * a⁻¹) * w⁻¹ * b⁻¹ := by rw [ha x]; group
    _ = x * (b * (y * z⁻¹)) * w⁻¹ * b⁻¹ := by rw [ha (b * (y * z⁻¹)), mul_inv_cancel_right]
    _ = x * ((b * (y * z⁻¹ * w⁻¹)) * b⁻¹) := by group
    _ = x * (y * (z⁻¹ * w⁻¹)) := by rw [hb, mul_inv_cancel_right]; group

section Twist

variable {M : ℕ}

/-- **The twist factor**: `c` on a link of direction `0` based at time `0`, `1` elsewhere. DERIVED: `0` the
axis and the slice; `1` the identity; `4` the dimension. -/
def tw (c : SU N) (l : Link 4 (M + 1)) : SU N := if l.1 = 0 ∧ l.2 0 = 0 then c else 1

/-- **The slice twist** of a periodic configuration. DERIVED: `1` the successor of the extent; `4` the
dimension. -/
def twist (c : SU N) (W : Link 4 (M + 1) → SU N) : Link 4 (M + 1) → SU N := fun l => tw c l * W l

/-- DERIVED: `1` the identity. -/
theorem tw_comm {c : SU N} (hc : ∀ g, c * g = g * c) (l : Link 4 (M + 1)) (g : SU N) :
    tw c l * g = g * tw c l := by
  unfold tw
  split_ifs
  · exact hc g
  · rw [one_mul, mul_one]

/-- **The twist factor does not see a step transverse to the link.** DERIVED: `0` the axis and the slice. -/
theorem tw_shift_ne (c : SU N) {μ ν : Fin 4} (h : μ ≠ ν) (x : WilsonHypercubic.Site 4 (M + 1)) :
    tw c (μ, WilsonHypercubic.shift ν x) = tw c (μ, x) := by
  show (if μ = 0 ∧ WilsonHypercubic.shift ν x 0 = 0 then c else 1) = (if μ = 0 ∧ x 0 = 0 then c else 1)
  by_cases hμ : μ = 0
  · subst hμ
    have hs : WilsonHypercubic.shift ν x 0 = x 0 := by
      unfold WilsonHypercubic.shift; exact Function.update_of_ne h _ _
    rw [hs]
  · simp only [hμ, false_and, if_false]

/-- **Every plaquette holonomy is unchanged by a central slice twist.** DERIVED: no numeral beyond the
dimension `4` and the successor `1`. -/
theorem hol_twist {c : SU N} (hc : ∀ g, c * g = g * c) (q : Plaq 4 (M + 1)) (W : Link 4 (M + 1) → SU N) :
    wilsonHol (bd (d := 4) (n := M + 1)) q (twist c W) = wilsonHol (bd (d := 4) (n := M + 1)) q W := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  rw [MassGap.Reflect.hol_bd, MassGap.Reflect.hol_bd]
  dsimp only [twist]
  by_cases h : μ = ν
  · subst h; group
  · rw [tw_shift_ne c h, tw_shift_ne c (Ne.symm h)]
    exact central_hol (tw_comm hc _) (tw_comm hc _) _ _ _ _

/-- **The Wilson action is unchanged by a central slice twist.** DERIVED: `4` the dimension; `1` the
successor. -/
theorem action_twist {c : SU N} (hc : ∀ g, c * g = g * c) (W : Link 4 (M + 1) → SU N) :
    (sysWilson N 4 (M + 1)).action (twist c W) = (sysWilson N 4 (M + 1)).action W := by
  show ∑ q : Plaq 4 (M + 1), wilsonDensity (wilsonHol (bd (d := 4) (n := M + 1)) q (twist c W))
    = ∑ q : Plaq 4 (M + 1), wilsonDensity (wilsonHol (bd (d := 4) (n := M + 1)) q W)
  exact Finset.sum_congr rfl fun q _ => by rw [hol_twist hc q W]

/-- **The slice twist preserves the product Haar measure**: on each link it is a left multiplication.
DERIVED: `4` the dimension; `1` the successor. -/
theorem twist_mp (c : SU N) :
    MeasurePreserving (twist (M := M) c) ((sysWilson N 4 (M + 1)).vol (probHaar (SU N)))
      ((sysWilson N 4 (M + 1)).vol (probHaar (SU N))) := by
  have hf : ∀ l : Link 4 (M + 1), MeasurePreserving (fun u : SU N => tw c l * u)
      (probHaar (SU N)) (probHaar (SU N)) := fun l => measurePreserving_mul_left _ _
  refine ⟨measurable_pi_lambda _ (fun l => (hf l).measurable.comp (measurable_pi_apply l)), ?_⟩
  show Measure.map (fun (V : Link 4 (M + 1) → SU N) (l : Link 4 (M + 1)) =>
      (fun u : SU N => tw c l * u) (V l)) (Measure.pi fun _ => probHaar (SU N))
      = Measure.pi fun _ => probHaar (SU N)
  rw [Measure.pi_map_pi (fun l => (hf l).aemeasurable)]
  exact congrArg Measure.pi (funext fun l => (hf l).map_eq)

/-- DERIVED: `1` the identity. -/
theorem twist_inv_twist (c : SU N) (W : Link 4 (M + 1) → SU N) : twist c⁻¹ (twist c W) = W := by
  funext l
  show tw c⁻¹ l * (tw c l * W l) = W l
  unfold tw
  split_ifs
  · rw [inv_mul_cancel_left]
  · rw [one_mul, one_mul]

/-- DERIVED: `1` the identity. -/
theorem twist_twist_inv (c : SU N) (W : Link 4 (M + 1) → SU N) : twist c (twist c⁻¹ W) = W := by
  funext l
  show tw c l * (tw c⁻¹ l * W l) = W l
  unfold tw
  split_ifs
  · rw [mul_inv_cancel_left]
  · rw [one_mul, one_mul]

/-- **The slice twist as a measurable equivalence.** DERIVED: no numeral. -/
def twistE (c : SU N) : (Link 4 (M + 1) → SU N) ≃ᵐ (Link 4 (M + 1) → SU N) where
  toFun := twist c
  invFun := twist c⁻¹
  left_inv := twist_inv_twist c
  right_inv := twist_twist_inv c
  measurable_toFun := (twist_mp (M := M) c).measurable
  measurable_invFun := (twist_mp (M := M) c⁻¹).measurable

/-- **The torus Gibbs expectation is invariant under a central slice twist**, at every real `β`.
DERIVED: `4` the dimension; `1` the successor. -/
theorem EW_twist {c : SU N} (hc : ∀ g, c * g = g * c) (β : ℝ) (O : (Link 4 (M + 1) → SU N) → ℝ) :
    MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (fun W => O (twist c W))
      = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β O :=
  System.expect_invariant_of_mp (sysWilson N 4 (M + 1)) (probHaar (SU N)) β O
    (twistE c) (twist_mp c)
    (fun W => by
      show (sysWilson N 4 (M + 1)).boltz β (twist c W) = (sysWilson N 4 (M + 1)).boltz β W
      unfold System.boltz
      rw [action_twist hc])

/-- The reduction of a time coordinate below the extent is itself. DERIVED: `1` the successor. -/
theorem finMod_val {k : ℕ} (hk : k ≤ M) : (finMod M (k : ℤ)).val = k := by
  show ((k : ℤ) % ((M : ℤ) + 1)).toNat = k
  rw [Int.emod_eq_of_lt (by positivity) (by omega)]
  simp

/-- **The twist factor along the winding line**: `c` on the first link, `1` on the others. DERIVED: `0` the
axis, the base point and the first link; `1` the identity. -/
theorem tw_line (c : SU N) {k : ℕ} (hk : k ≤ M) :
    tw c (linkMod M ((0 : Fin 4), lineSite 0 0 (k : ℤ))) = if k = 0 then c else 1 := by
  show (if (0 : Fin 4) = 0 ∧ finMod M (lineSite 0 0 (k : ℤ) 0) = 0 then c else 1) = _
  rw [lineSite_self]
  simp only [Pi.zero_apply, zero_add, true_and]
  have hiff : finMod M (k : ℤ) = 0 ↔ k = 0 := by
    rw [Fin.ext_iff, finMod_val hk, Fin.val_zero]
  by_cases h0 : k = 0
  · rw [if_pos (hiff.mpr h0), if_pos h0]
  · rw [if_neg (fun h => h0 (hiff.mp h)), if_neg h0]

/-- **The winding holonomy of a twisted configuration**: the twist enters once, at the first link. DERIVED:
`0` the axis and the base point; `1` the successor. -/
theorem polyHol_twist (c : SU N) (W : Link 4 (M + 1) → SU N) :
    ∀ k : ℕ, k ≤ M → polyHol 0 (k + 1) 0 (pullback M (twist c W)) = c * polyHol 0 (k + 1) 0 (pullback M W) := by
  intro k
  induction k with
  | zero =>
    intro hk
    show polyHol 0 0 0 (pullback M (twist c W)) * twist c W (linkMod M (0, lineSite 0 0 ((0 : ℕ) : ℤ)))
      = c * (polyHol 0 0 0 (pullback M W) * W (linkMod M (0, lineSite 0 0 ((0 : ℕ) : ℤ))))
    show 1 * (tw c (linkMod M (0, lineSite 0 0 ((0 : ℕ) : ℤ))) * W (linkMod M (0, lineSite 0 0 ((0 : ℕ) : ℤ))))
      = c * (1 * W (linkMod M (0, lineSite 0 0 ((0 : ℕ) : ℤ))))
    rw [tw_line c hk, if_pos rfl, one_mul, one_mul]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    show polyHol 0 (k + 1) 0 (pullback M (twist c W))
        * twist c W (linkMod M (0, lineSite 0 0 ((k + 1 : ℕ) : ℤ)))
      = c * (polyHol 0 (k + 1) 0 (pullback M W) * W (linkMod M (0, lineSite 0 0 ((k + 1 : ℕ) : ℤ))))
    rw [h1]
    show c * polyHol 0 (k + 1) 0 (pullback M W)
        * (tw c (linkMod M (0, lineSite 0 0 ((k + 1 : ℕ) : ℤ))) * W (linkMod M (0, lineSite 0 0 ((k + 1 : ℕ) : ℤ))))
      = _
    rw [tw_line c hk, if_neg (Nat.succ_ne_zero k), one_mul, mul_assoc]

/-- **The winding trace of a twisted configuration is rotated by `ω`.** DERIVED: `1` the successor. -/
theorem trP_twist (hN : N ≠ 0) {ω : ℂ} (hω : ω ^ N = 1) (W : Link 4 (M + 1) → SU N) :
    trP (M + 1) (pullback M (twist (cen hN hω) W)) = ω * trP (M + 1) (pullback M W) := by
  unfold trP
  rw [polyHol_twist (cen hN hω) W M le_rfl]
  rw [Submonoid.coe_mul, coe_cen, smul_mul_assoc, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

/-- **Every `N`-th root of unity leaves the law of the winding trace unchanged** on the torus state, at every
real `β`. DERIVED: `1` the successor. -/
theorem phaseInv_torusState (hN : N ≠ 0) (M : ℕ) (β : ℝ) {ω : ℂ} (hω : ω ^ N = 1) :
    PhaseInv (torusState hN M β) (M + 1) ω := by
  intro f
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M (f.comp (trCM (M + 1))))
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M ((f.comp (rot ω)).comp (trCM (M + 1))))
  have h : torusObs M ((f.comp (rot ω)).comp (trCM (M + 1)))
      = fun W => torusObs M (f.comp (trCM (M + 1))) (twist (cen hN hω) W) := by
    funext W
    show f (ω * trP (M + 1) (pullback M W)) = f (trP (M + 1) (pullback M (twist (cen hN hω) W)))
    rw [trP_twist hN hω W]
  rw [h]
  exact (EW_twist (cen_comm hN hω) β _).symm

end Twist

/-! ## 3. The trace gap and the support of the torus state -/

/-- **A unitary trace of norm `N` along `ω` forces `ω ^ N = 1`**: if `‖ω‖ = 1` and `ω tr g = N` for
`g ∈ SU(N)`, then `ω ^ N = 1`. DERIVED: `0` the off-diagonal entries; `1` the unit circle and the diagonal;
`2` the square of a norm. -/
theorem pow_eq_one_of_trace (g : SU N) {ω : ℂ} (hn : ‖ω‖ = 1)
    (h : ω * Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ) = N) : ω ^ N = 1 := by
  set G : Matrix (Fin N) (Fin N) ℂ := (g : Matrix (Fin N) (Fin N) ℂ) with hG
  have hU : G ∈ Matrix.unitaryGroup (Fin N) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have hdet : G.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  have hle : ∀ i j, ‖G i j‖ ≤ 1 := fun i j => MassGap.SUN.unitary_entry_norm_le_one N hU i j
  -- the column identity `∑ₖ ‖G k j‖² = 1`
  have hcol : ∀ j, ∑ k, ‖G k j‖ ^ 2 = 1 := by
    intro j
    have hMM : star G * G = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have h1 : ∑ k, (star G) j k * G k j = (1 : ℂ) := by
      have h0 : (star G * G) j j = (1 : Matrix (Fin N) (Fin N) ℂ) j j := by rw [hMM]
      rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h0
    have hsum : ((∑ k, ‖G k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h1]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.conj_mul]
      norm_cast
    exact_mod_cast hsum
  -- the real parts of the diagonal of `ω g` sum to `N`, each at most `1`
  have hD : ∀ i, ‖ω * G i i‖ ≤ 1 := fun i => by rw [norm_mul, hn, one_mul]; exact hle i i
  have hsumre : ∑ i, (ω * G i i).re = N := by
    have : ∑ i, ω * G i i = (N : ℂ) := by rw [← Finset.mul_sum]; exact h
    have h2 := congrArg Complex.re this
    rw [Complex.re_sum] at h2
    simpa using h2
  have hre : ∀ i, (ω * G i i).re = 1 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ 1 - (ω * G i i).re :=
      fun i _ => by linarith [Complex.re_le_norm (ω * G i i), hD i]
    have hz : ∑ i, (1 - (ω * G i i).re) = 0 := by
      rw [Finset.sum_sub_distrib, hsumre]; simp
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i (Finset.mem_univ i)
    linarith
  have hone : ∀ i, ω * G i i = 1 := by
    intro i
    have hn1 : ‖ω * G i i‖ = 1 := le_antisymm (hD i) (by rw [← hre i]; exact Complex.re_le_norm _)
    have him : (ω * G i i).im ^ 2 = 0 := by
      rw [← Complex.sq_norm_sub_sq_re, hn1, hre i]; norm_num
    apply Complex.ext
    · rw [hre i]; simp
    · rw [pow_eq_zero_iff two_ne_zero] at him; rw [him]; simp
  have hdiag : ∀ i, ‖G i i‖ = 1 := fun i => by
    have := congrArg norm (hone i)
    rwa [norm_mul, hn, one_mul, norm_one] at this
  have hoff : ∀ k j, k ≠ j → G k j = 0 := by
    intro k j hkj
    have hc := hcol j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag j] at hc
    have hz : ∑ x ∈ Finset.univ.erase j, ‖G x j‖ ^ 2 = 0 := by rw [one_pow] at hc; linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg ‖G x j‖)).mp hz k
      (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    exact this
  have hstar : ω * star ω = 1 := mul_star_of_norm hn
  have hGii : ∀ i, G i i = star ω := fun i => by
    have h1 := hone i
    calc G i i = (star ω * ω) * G i i := by rw [mul_comm (star ω), hstar, one_mul]
      _ = star ω * (ω * G i i) := by ring
      _ = star ω := by rw [h1, mul_one]
  have hGeq : G = star ω • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, hGii, smul_eq_mul, mul_one]
    · rw [if_neg hij, hoff i j hij, smul_zero]
  rw [hGeq, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have := congrArg star hdet
  rwa [star_pow, star_star, star_one] at this

/-- **The trace gap**: for `‖ω‖ = 1` and `ω ^ N ≠ 1` there is `m > 0` with `m ≤ ‖ω tr g − N‖` on all of `SU(N)`.
DERIVED: `0` the strict lower bound; `1` the unit circle. -/
theorem exists_trace_gap {ω : ℂ} (hn : ‖ω‖ = 1) (hω : ω ^ N ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ g : SU N, m ≤ ‖ω * Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ) - N‖ := by
  have hc : Continuous fun g : SU N => ‖ω * Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ) - N‖ :=
    ((continuous_const.mul (Continuous.matrix_trace continuous_subtype_val)).sub continuous_const).norm
  obtain ⟨g₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨‖ω * Matrix.trace (g₀ : Matrix (Fin N) (Fin N) ℂ) - N‖, ?_, fun g => isMinOn_iff.mp hmin g (Set.mem_univ g)⟩
  refine norm_pos_iff.mpr fun h0 => hω (pow_eq_one_of_trace g₀ hn ?_)
  exact sub_eq_zero.mp h0

/-- **A positive observable has positive torus expectation**: nonnegative, continuous, positive on one
periodic configuration. At every real `β`. DERIVED: `0` the bounds. -/
theorem torusState_pos (hN : N ≠ 0) (M : ℕ) (β : ℝ) (f : C(Cfg N, ℝ)) (hf : ∀ U, 0 ≤ f U)
    (W₀ : Link 4 (M + 1) → SU N) (h₀ : 0 < f (pullback M W₀)) : 0 < torusState hN M β f := by
  classical
  haveI : IsProbabilityMeasure ((sysWilson N 4 (M + 1)).vol (probHaar (SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Link 4 (M + 1) => probHaar (SU N))))
  have hwpos : ∀ U, 0 < (sysWilson N 4 (M + 1)).boltz β U := fun U => wilsonSystem_boltz_pos _ β U
  have hnn : (0 : (sysWilson N 4 (M + 1)).Config → ℝ) ≤ fun U => torusObs M f U * (sysWilson N 4 (M + 1)).boltz β U :=
    fun U => mul_nonneg (hf _) (hwpos U).le
  obtain ⟨C, hC⟩ := bounded_of_continuous f.continuous
  have hint : Integrable (fun U => torusObs M f U * (sysWilson N 4 (M + 1)).boltz β U) ((sysWilson N 4 (M + 1)).vol (probHaar (SU N))) :=
    wilsonSystem_mul_boltz_integrable hN _ β (torusObs M f) (measurable_torusObs M f) C (fun W => hC _)
  have hcont : Continuous fun U : Link 4 (M + 1) → SU N => torusObs M f U * (sysWilson N 4 (M + 1)).boltz β U :=
    (f.continuous.comp continuous_pullback).mul (MassGap.GibbsPositive.continuous_boltz _ β)
  have hnum : 0 < (sysWilson N 4 (M + 1)).corrNum (probHaar (SU N)) β (torusObs M f) := by
    unfold System.corrNum
    refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => ?_)
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
    have hzero := (Continuous.ae_eq_iff_eq (Measure.pi fun _ : Link 4 (M + 1) => probHaar (SU N)) hcont
      continuous_const).mp hae
    have hU : torusObs M f W₀ * (sysWilson N 4 (M + 1)).boltz β W₀ = 0 := congrFun hzero W₀
    exact h₀.ne' ((mul_eq_zero.mp hU).resolve_right (hwpos W₀).ne')
  show 0 < (sysWilson N 4 (M + 1)).corrNum (probHaar (SU N)) β (torusObs M f) / (sysWilson N 4 (M + 1)).partition (probHaar (SU N)) β
  exact div_pos hnum (wilsonSystem_partition_pos hN _ β)

/-- The winding holonomy of the flat configuration is the identity. DERIVED: `0` the axis and the base
point; `1` the identity. -/
theorem polyHol_one (L : ℕ) : polyHol (N := N) 0 L 0 (fun _ => 1) = 1 := by
  induction L with
  | zero => rfl
  | succ L ih =>
    show polyHol 0 L 0 (fun _ => 1) * 1 = 1
    rw [ih, mul_one]

/-- **The flat configuration has `tr P = N`.** DERIVED: `1` the identity. -/
theorem trP_one (L : ℕ) : trP (N := N) L (fun _ => 1) = N := by
  unfold trP
  rw [polyHol_one]
  show Matrix.trace (1 : Matrix (Fin N) (Fin N) ℂ) = N
  rw [Matrix.trace_one, Fintype.card_fin]

/-- **No other phase leaves the law unchanged**: for `‖ω‖ = 1` and `ω ^ N ≠ 1`, at every line length `L` and
every real `β`, the law of the winding trace under the torus state is not invariant under the rotation by `ω`.
DERIVED: `0` the floor of the test; `1` the unit circle and the flat configuration. -/
theorem not_phaseInv_torusState (hN : N ≠ 0) (M : ℕ) (β : ℝ) (L : ℕ) {ω : ℂ} (hn : ‖ω‖ = 1)
    (hω : ω ^ N ≠ 1) : ¬ PhaseInv (torusState hN M β) L ω := by
  intro hinv
  obtain ⟨m, hm, hgap⟩ := exists_trace_gap hn hω
  let f : C(ℂ, ℝ) := ⟨fun z => max 0 (m - ‖z - N‖),
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)⟩
  have hL : 0 < torusState hN M β (f.comp (trCM L)) := by
    refine torusState_pos hN M β _ (fun U => le_max_left _ _) (fun _ => 1) ?_
    show 0 < max 0 (m - ‖trP L (pullback M (fun _ => 1)) - N‖)
    have hp : pullback M (fun _ : Link 4 (M + 1) => (1 : SU N)) = fun _ => 1 := rfl
    rw [hp, trP_one, sub_self, norm_zero, sub_zero]
    exact lt_max_of_lt_right hm
  have hR : (f.comp (rot ω)).comp (trCM (N := N) L) = 0 := by
    ext U
    show max 0 (m - ‖ω * trP L U - N‖) = 0
    exact max_eq_left (sub_nonpos.mpr (hgap (polyHol 0 L 0 U)))
  rw [hinv f, hR, (torusState hN M β).map_zero] at hL
  exact lt_irrefl _ hL

/-- **The centre phases of the torus state are the `N`-th roots of unity**, for `N ≥ 2`, at every real `β`.
DERIVED: `2` the least colour count at which the period is exact. -/
theorem phases_torusState (hN : N ≠ 0) (hN2 : 2 ≤ N) (M : ℕ) (β : ℝ) :
    phases (torusState hN M β) = {ω : ℂ | ω ^ N = 1} := by
  ext ω
  simp only [phases, Set.mem_setOf_eq, MassGap.RectTorusState.measPeriod_torusState hN hN2 M β]
  constructor
  · rintro ⟨hn, hinv⟩
    by_contra hω
    exact not_phaseInv_torusState hN M β (M + 1) hn hω hinv
  · intro hω
    exact ⟨norm_of_pow_eq_one hN hω, phaseInv_torusState hN M β hω⟩

/-- **The measured colour count is exact on the torus states**: `measN (torusState hN M β) = N` for `N ≥ 2`,
every extent and every real `β`. DERIVED: `2` as in `phases_torusState`; `0` the excluded rank. -/
theorem measN_torusState (hN : N ≠ 0) (hN2 : 2 ≤ N) (M : ℕ) (β : ℝ) :
    measN (torusState hN M β) = N := by
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hset : {ω : ℂ | ω ^ N = 1} = ↑(Polynomial.nthRootsFinset N (1 : ℂ)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Polynomial.mem_nthRootsFinset hpos]
  rw [measN, phases_torusState hN hN2 M β, hset, Set.ncard_coe_finset,
    (Complex.isPrimitiveRoot_exp N hN).card_nthRootsFinset]

/-! ## 4. The power that closes -/

/-- **The real part of the `k`-th power of the winding trace.** DERIVED: no numeral. -/
def reMom (L k : ℕ) : C(Cfg N, ℝ) := ⟨fun U => (trP L U ^ k).re,
  Complex.continuous_re.comp ((continuous_trP L).pow k)⟩

/-- **The imaginary part of the `k`-th power of the winding trace.** DERIVED: no numeral. -/
def imMom (L k : ℕ) : C(Cfg N, ℝ) := ⟨fun U => (trP L U ^ k).im,
  Complex.continuous_im.comp ((continuous_trP L).pow k)⟩

/-- The test `z ↦ Re(θ z^k)`. DERIVED: no numeral. -/
def reTest (θ : ℂ) (k : ℕ) : C(ℂ, ℝ) := ⟨fun z => (θ * z ^ k).re,
  Complex.continuous_re.comp (continuous_const.mul (continuous_id.pow k))⟩

/-- A capture reads the test `Re(θ (tr P)^k)` as `Re θ · ν(Re (tr P)^k) − Im θ · ν(Im (tr P)^k)`.
DERIVED: no numeral. -/
theorem read_reTest (ν : State (Cfg N)) (L k : ℕ) (θ : ℂ) :
    ν ((reTest θ k).comp (trCM L)) = θ.re * ν (reMom L k) - θ.im * ν (imMom L k) := by
  have e : (reTest θ k).comp (trCM (N := N) L) = θ.re • reMom L k - θ.im • imMom L k := by
    ext U
    show (θ * trP L U ^ k).re = θ.re * (trP L U ^ k).re - θ.im * (trP L U ^ k).im
    rw [Complex.mul_re]
  rw [e, ν.map_sub, ν.map_smul, ν.map_smul]

/-- **The power that closes**: if `ω` leaves the law of the winding trace unchanged and `ω ^ k ≠ 1`, both
the real and the imaginary part of the `k`-th moment of `tr P` vanish, for any capture. DERIVED: `0` the
moments; `1` the unit; `2` the squares of the determinant `(1 − p)² + q²`. -/
theorem moments_vanish {ν : State (Cfg N)} {L : ℕ} {ω : ℂ} (h : PhaseInv ν L ω) {k : ℕ} (hk : ω ^ k ≠ 1) :
    ν (reMom L k) = 0 ∧ ν (imMom L k) = 0 := by
  have hrot : ∀ θ : ℂ, ν ((reTest θ k).comp (trCM L)) = ν ((reTest (θ * ω ^ k) k).comp (trCM L)) := by
    intro θ
    rw [h (reTest θ k)]
    congr 1
    ext U
    show (θ * (ω * trP L U) ^ k).re = (θ * ω ^ k * trP L U ^ k).re
    rw [mul_pow, mul_assoc]
  have c1 : ((1 : ℂ) * ω ^ k).re = (ω ^ k).re := by rw [one_mul]
  have c2 : ((1 : ℂ) * ω ^ k).im = (ω ^ k).im := by rw [one_mul]
  have c3 : (Complex.I * ω ^ k).re = -(ω ^ k).im := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring
  have c4 : (Complex.I * ω ^ k).im = (ω ^ k).re := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im]; ring
  have e1 := hrot 1
  have e2 := hrot Complex.I
  rw [read_reTest, read_reTest, c1, c2, Complex.one_re, Complex.one_im] at e1
  rw [read_reTest, read_reTest, c3, c4, Complex.I_re, Complex.I_im] at e2
  have hd : (1 - (ω ^ k).re) ^ 2 + (ω ^ k).im ^ 2 ≠ 0 := by
    intro h0
    have hp : 1 - (ω ^ k).re = 0 := by nlinarith [sq_nonneg (1 - (ω ^ k).re), sq_nonneg (ω ^ k).im]
    have hq : (ω ^ k).im = 0 := by nlinarith [sq_nonneg (1 - (ω ^ k).re), sq_nonneg (ω ^ k).im]
    exact hk (Complex.ext (by rw [Complex.one_re]; linarith) (by rw [Complex.one_im]; exact hq))
  have hA : ((1 - (ω ^ k).re) ^ 2 + (ω ^ k).im ^ 2) * ν (reMom L k) = 0 := by
    linear_combination (1 - (ω ^ k).re) * e1 + (ω ^ k).im * e2
  have hB : ((1 - (ω ^ k).re) ^ 2 + (ω ^ k).im ^ 2) * ν (imMom L k) = 0 := by
    linear_combination (ω ^ k).im * e1 - (1 - (ω ^ k).re) * e2
  exact ⟨(mul_eq_zero.mp hA).resolve_left hd, (mul_eq_zero.mp hB).resolve_left hd⟩

/-- **On every torus state, at every real `β`, the `k`-th moment of the winding trace vanishes for `N ∤ k`.**
At `β = 0` this is the Haar vanishing `∫ (tr U)^k dU = 0` for `N ∤ k` on the winding holonomy, with no Haar
computation. DERIVED: `0` the moments; `1` the successor; `2`, `π` the primitive root `e^{2πi/N}`. -/
theorem moments_vanish_torusState (hN : N ≠ 0) (M : ℕ) (β : ℝ) {k : ℕ} (hk : ¬ N ∣ k) :
    torusState hN M β (reMom (M + 1) k) = 0 ∧ torusState hN M β (imMom (M + 1) k) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N hN
  refine moments_vanish (phaseInv_torusState hN M β hζ.pow_eq_one) ?_
  rw [Ne, hζ.pow_eq_one_iff_dvd]
  exact hk

end MassGap.MeasureN

#print axioms MassGap.MeasureN.continuous_trP
#print axioms MassGap.MeasureN.norm_of_pow_eq_one
#print axioms MassGap.MeasureN.cen_comm
#print axioms MassGap.MeasureN.central_hol
#print axioms MassGap.MeasureN.tw_shift_ne
#print axioms MassGap.MeasureN.hol_twist
#print axioms MassGap.MeasureN.action_twist
#print axioms MassGap.MeasureN.twist_mp
#print axioms MassGap.MeasureN.EW_twist
#print axioms MassGap.MeasureN.finMod_val
#print axioms MassGap.MeasureN.tw_line
#print axioms MassGap.MeasureN.polyHol_twist
#print axioms MassGap.MeasureN.trP_twist
#print axioms MassGap.MeasureN.phaseInv_torusState
#print axioms MassGap.MeasureN.pow_eq_one_of_trace
#print axioms MassGap.MeasureN.exists_trace_gap
#print axioms MassGap.MeasureN.torusState_pos
#print axioms MassGap.MeasureN.polyHol_one
#print axioms MassGap.MeasureN.trP_one
#print axioms MassGap.MeasureN.not_phaseInv_torusState
#print axioms MassGap.MeasureN.phases_torusState
#print axioms MassGap.MeasureN.measN_torusState
#print axioms MassGap.MeasureN.read_reTest
#print axioms MassGap.MeasureN.moments_vanish
#print axioms MassGap.MeasureN.moments_vanish_torusState
