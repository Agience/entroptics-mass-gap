import Mathlib
import MassGap.WilsonAnalytic
import MassGap.PeriodicState
import MassGap.ClayStatement

/-!
# MassGap.ThreePointAnomaly — the coupling derivative of a connected two-point function is a summed three-point function

The per-`N` open input `∃ ℓ > 0, NonGaussFromScale.ThreePointAtScale hN ℓ` is, by
`ThreePointN.exists_threePointAtScale_iff`, the non-vanishing along `ultra` of the normalised connected
three-point reading `ThreePointN.bareNorm3` at one separated continuous triple. The argued link to the
two-point input `AFCoefficient` is the lattice trace-anomaly identity
`∂_β ν_β(F G)ᶜ = −Σ_p ν_β(F G φ_p)ᶜ`, `φ_p` the plaquette action density. This module proves that
identity at every finite volume, splits the plaquette sum into a contact part and a separated part,
bounds the contact part by its plaquette count, and proves a qualitative two-point fact: under
`AFCoefficient` the profile `r⁸ G(r)` is not a pure power, already along every dyadic sequence.
Declarations are in the namespace `MassGap.ThreePointAnomaly`.

## 1. The identity on an arbitrary `SU(N)` Wilson system (proved)

`ex bd β O` is the Gibbs expectation of `wilsonSystem bd wilsonDensity` against product Haar measure;
`cum2` is the connected two-point function and `cum3` the connected three-point function (third joint
cumulant). The sign convention is that of `LatticeGauge.System.boltz`: weight `exp (−β S)`,
`S = Σ_p φ_p ≥ 0`.

* `cum2_hasDerivAt`: `d/dβ cum2 β F G = −cum3 β F G S` for bounded measurable `F`, `G`.
* `cum3_sum`: `cum3` is additive in its third slot over a finite sum of uniformly bounded measurable
  observables.
* **`cum2_hasDerivAt_plaq`**: `d/dβ cum2 β F G = −Σ_p cum3 β F G φ_p`, the trace-anomaly identity.
* `abs_cum3_plaq_le`: `|cum3 β F G φ_p| ≤ 12 · M_F · M_G` at every plaquette (`12 = 6 · 2`: the
  five terms of `cum3`, total coefficient `6`, with `φ_p ≤ 2`).
* `sum_cum3_split`, `abs_contact_le`: for any contact predicate `C` on plaquettes the sum splits as
  contact plus separated, and the contact part is at most `12 · M_F · M_G · #C`.
* `cum2_sub_eq`: the mean-value form along any coupling interval `x < y`:
  `cum2 y − cum2 x = −(y − x) Σ_p cum3 ξ F G φ_p` at some `ξ ∈ (x, y)`.
* **`separated_lower`**: at some `ξ ∈ (x, y)`,
  `|cum2 y − cum2 x| / (y − x) − 12 M_F M_G #C ≤ |cum3 ξ F G H_sep|`, where
  `H_sep = Σ_{p ∉ C} φ_p` is the separated action. A two-point difference above the contact budget is a
  three-point reading with a separated third insertion, at an intermediate coupling.

## 2. The same on the periodic torus states (proved)

`torusCum2 hN M β f g` is the connected two-point function of continuous `ℤ⁴` observables in
`PeriodicState.torusState hN M β`; it is `cum2` at the hypercubic boundary word (`torusCum2_eq`, `rfl`).
`torusCum2_hasDerivAt` and `torus_separated_lower` are §1 there. The smeared observer fields
`ContinuumField.smear a (obs N).1 f` are continuous, so they are admissible `f`, `g`.

## 3. The two-point half of the link (proved)

* **`af_dyadic_frequently`**: under `AFCoefficient N G`, `N ≥ 2`, for every `r₀ > 0` the profile
  `h(r) = r⁸ G(r)` satisfies `h(r₀/2^(j+1)) ≠ h(r₀/2^j)` for infinitely many `j`. If it were eventually
  constant along the sequence, `h log² r` would either vanish (limit `0 ≠ afConst N`) or diverge.
* `af_not_pure_power`: no `C`, `ε > 0` with `r⁸ G(r) = C` on `(0, ε)`.

## 4. What remains between §1–§3 and `¬ Tendsto bareNorm3` (stated, not proved)

`ThreePointN.bareNorm3 hN k a b c` reads `stateK hN k = PeriodicState.periodicState hN (dyBeta k)`, an
infinite-volume state chosen at each coupling separately (`PeriodicState.periodicUltra hN β` depends on
`β`). The identity of §1 is at finite volume. Four statements stand between them, each separate:

1. **(β-family)** a family of infinite-volume states differentiable in `β` that agrees with `stateK` at
   the step couplings, together with the exchange of the volume limit and the `β`-derivative. On the
   torus the derivative is `−Σ_p cum3`, a sum over the whole volume; its limit exists only if the
   separated three-point function `p ↦ cum3 β F G φ_p` is summable uniformly in the volume (clustering
   of the connected three-point function). Nothing in the tree supplies this; `WilsonAnalytic`
   carries the one-point analogue as the hypothesis `hclust`.
2. **(steps vs derivative)** `dyBeta` is a sequence, and `ThreePointAtScale` reads couplings
   `dyBeta k` with the smearing at `dySpacing N k`. `separated_lower` gives the three-point reading at an
   intermediate coupling `ξ ∈ (dyBeta k, dyBeta (k+1))` with the smearing held at a fixed lattice
   geometry. Passing to `bareRead3 hN k` needs continuity of the separated three-point reading in the
   coupling at the scale `a_k¹²`, and a comparison of the smearings at `a_k` and `a_{k+1}`.
3. **(two-point running)** the lattice side of `AFCoefficient`: the normalised smeared two-point reading
   at fixed physical separation changes between consecutive steps by at least `κ · a_k⁸ · (dyBeta (k+1)
   − dyBeta k)` on a set of `ultra`. §3 proves the continuum profile is not a pure power along dyadic
   scales; the statement that the lattice reading converges to that profile with the field strength
   `a_k⁴` per insertion is the continuum-limit input, not proved here.
4. **(contact budget at the scale)** the contact part `Σ_{p ∈ C}` with `C` the plaquettes within
   physical distance `δ` of the supports of the two insertions. §1 bounds it by
   `12 M_F M_G #C`; with `F`, `G` the smeared fields that bound grows with `#C ~ a_k⁻⁴`, so it does not
   fall below the two-point difference at the scale `a_k⁸`. The needed statement is the short-distance
   one: the contact contribution is `o(a_k⁸)` relative to the two-point running as `δ → 0`, i.e. the
   operator-product coefficient of `obs × obs → obs` does not cancel the running.

Comparability of the insertions. The insertion of §1 is the plaquette action density
`wilsonPlaqObs bd p = wilsonDensity (hol p)`. The observer's field `obs N = sym (plaqField q0)`
(`ClayData.obs`) is the same density, `ObserverEnergyMoments.plaqField q = wilsonDensity (ihol q)`,
summed over the `384` hypercubic images of the plaquette `q0`; those images are the `24` plaquettes with
a corner at the origin, each counted `16` times. So `Σ_x obs_x = 64 · S` on a torus (each plaquette has
`4` corners), and `Σ_p cum3 β F G φ_p = (1/64) Σ_x cum3 β F G obs_x`: the third insertion of §1 is the
observer's own field summed over the volume. The identity `Σ_x obs_x = 64 · S` is argued here, not
formalised. A separated block `Σ_{p ∈ B} φ_p` is a smearing of the same field against the indicator of
`B`; `cum3_sum` makes `Σ_{p ∈ B} cum3 β F G φ_p = cum3 β F G (Σ_{p ∈ B} φ_p)`, a three-point reading
with one block-smeared insertion.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the coefficient of the fully factorised term of a third cumulant and the
upper bound of `wilsonDensity`; `12 = 6 · 2`; `8` and `2` the powers of `AFCoefficient`; `2` the dyadic
halving; `0` the signs and limit points.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ThreePointAnomaly

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonReal MassGap.WilsonAction
open MassGap.CompactGauge MeasureTheory Filter
open scoped Topology

/-! ## 1. The identity on an arbitrary `SU(N)` Wilson system -/

section Finite

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- The Gibbs expectation of the `SU(N)` Wilson system with boundary word `bd` at coupling `β`.
DERIVED: no numeral. -/
abbrev ex (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O

/-- **The connected two-point function** `⟨F G⟩ − ⟨F⟩⟨G⟩`. DERIVED: no numeral. -/
def cum2 (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) : ℝ :=
  ex bd β (fun U => F U * G U) - ex bd β F * ex bd β G

/-- **The connected three-point function** (third joint cumulant)
`⟨FGH⟩ − ⟨FG⟩⟨H⟩ − ⟨FH⟩⟨G⟩ − ⟨GH⟩⟨F⟩ + 2⟨F⟩⟨G⟩⟨H⟩`.
DERIVED: `2` the coefficient of the fully factorised term. -/
def cum3 (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G H : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) : ℝ :=
  ex bd β (fun U => F U * G U * H U) - ex bd β (fun U => F U * G U) * ex bd β H
    - ex bd β (fun U => F U * H U) * ex bd β G - ex bd β (fun U => G U * H U) * ex bd β F
    + 2 * ex bd β F * ex bd β G * ex bd β H

/-- A bound `|F U| ≤ M` at any configuration makes `M` non-negative. DERIVED: `1` the unit of `SU(N)`. -/
theorem bound_nonneg (bd : Pq → List (Lk × Bool))
    {F : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ} {M : ℝ} (hb : ∀ U, |F U| ≤ M) :
    0 ≤ M :=
  le_trans (abs_nonneg _) (hb (fun _ => (1 : MassGap.SUN.SU N)))

/-- **The coupling derivative of the connected two-point function is minus the connected three-point
function with the action**: `d/dβ cum2 β F G = −cum3 β F G S`. `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`
at `F G`, `F`, `G`, and the product rule. DERIVED: `0` the excluded rank. -/
theorem cum2_hasDerivAt (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) :
    HasDerivAt (fun x => cum2 bd x F G)
      (-cum3 bd β F G (wilsonSystem bd (wilsonDensity (N := N))).action) β := by
  have hFG := MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd β
    (fun U => F U * G U) (hF.mul hG) (MF * MG) (fun U => by
      rw [abs_mul]
      exact mul_le_mul (hFb U) (hGb U) (abs_nonneg _) (bound_nonneg bd hFb))
  have h1 := MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd β F hF MF hFb
  have h2 := MassGap.WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN bd β G hG MG hGb
  refine HasDerivAt.congr_deriv (f := fun x => cum2 bd x F G) (hFG.sub (h1.mul h2)) ?_
  unfold cum3
  ring

/-- `⟨K · Σ_{p ∈ s} h_p⟩ = Σ_{p ∈ s} ⟨K h_p⟩` for bounded measurable `K` and a uniformly bounded
measurable family `h`. `WilsonAnalytic.expect_finset_sum`. DERIVED: `0` the excluded rank. -/
theorem ex_mul_sum (hN : N ≠ 0) [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (K : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hK : Measurable K) (MK : ℝ) (hKb : ∀ U, |K U| ≤ MK)
    (h : Pq → (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hh : ∀ p, Measurable (h p)) (Mh : ℝ) (hhb : ∀ p U, |h p U| ≤ Mh) (s : Finset Pq) :
    ex bd β (fun U => K U * ∑ p ∈ s, h p U) = ∑ p ∈ s, ex bd β (fun U => K U * h p U) := by
  have hfun : (fun U => K U * ∑ p ∈ s, h p U) = fun U => ∑ p ∈ s, K U * h p U :=
    funext fun U => Finset.mul_sum _ _ _
  rw [hfun]
  exact MassGap.WilsonAnalytic.expect_finset_sum hN bd β (fun p U => K U * h p U)
    (fun p => hK.mul (hh p)) (MK * Mh) (fun p U => by
      rw [abs_mul]
      exact mul_le_mul (hKb U) (hhb p U) (abs_nonneg _) (le_trans (abs_nonneg _) (hKb U))) s

/-- **`cum3` is additive in its third slot** over a finite sum of uniformly bounded measurable
observables. DERIVED: `0` the excluded rank. -/
theorem cum3_sum (hN : N ≠ 0) [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG)
    (h : Pq → (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hh : ∀ p, Measurable (h p)) (Mh : ℝ) (hhb : ∀ p U, |h p U| ≤ Mh) (s : Finset Pq) :
    cum3 bd β F G (fun U => ∑ p ∈ s, h p U) = ∑ p ∈ s, cum3 bd β F G (h p) := by
  have hMF := bound_nonneg bd hFb
  have hFGb : ∀ U, |F U * G U| ≤ MF * MG := fun U => by
    rw [abs_mul]; exact mul_le_mul (hFb U) (hGb U) (abs_nonneg _) hMF
  have e1 : ex bd β (fun U => F U * G U * ∑ p ∈ s, h p U)
      = ∑ p ∈ s, ex bd β (fun U => F U * G U * h p U) :=
    ex_mul_sum hN bd β (fun U => F U * G U) (hF.mul hG) (MF * MG) hFGb h hh Mh hhb s
  have e2 : ex bd β (fun U => F U * ∑ p ∈ s, h p U) = ∑ p ∈ s, ex bd β (fun U => F U * h p U) :=
    ex_mul_sum hN bd β F hF MF hFb h hh Mh hhb s
  have e3 : ex bd β (fun U => G U * ∑ p ∈ s, h p U) = ∑ p ∈ s, ex bd β (fun U => G U * h p U) :=
    ex_mul_sum hN bd β G hG MG hGb h hh Mh hhb s
  have e4 : ex bd β (fun U => ∑ p ∈ s, h p U) = ∑ p ∈ s, ex bd β (h p) :=
    MassGap.WilsonAnalytic.expect_finset_sum hN bd β h hh Mh hhb s
  unfold cum3
  rw [e1, e2, e3, e4]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

/-- The action is the sum of the plaquette densities, as a function. DERIVED: no numeral. -/
theorem action_eq_fun (bd : Pq → List (Lk × Bool)) :
    (wilsonSystem bd (wilsonDensity (N := N))).action = fun U => ∑ p, wilsonPlaqObs bd p U :=
  funext fun U => MassGap.WilsonAnalytic.action_eq_sum_plaqObs bd U

/-- `|φ_p| ≤ 2`. DERIVED: `2` the upper bound of `wilsonDensity`. -/
theorem abs_plaq_le (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) : |wilsonPlaqObs bd p U| ≤ 2 := by
  rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd p U)]
  exact wilsonPlaqObs_le_two hN bd p U

/-- **The trace-anomaly identity at finite volume**: `d/dβ cum2 β F G = −Σ_p cum3 β F G φ_p`.
DERIVED: `0` the excluded rank; `2` the bound of `φ_p`. -/
theorem cum2_hasDerivAt_plaq (hN : N ≠ 0) [DecidableEq Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) :
    HasDerivAt (fun x => cum2 bd x F G) (-∑ p, cum3 bd β F G (wilsonPlaqObs bd p)) β := by
  have h := cum2_hasDerivAt hN bd β F G hF MF hFb hG MG hGb
  rw [action_eq_fun bd, cum3_sum hN bd β F G hF MF hFb hG MG hGb (wilsonPlaqObs bd)
    (measurable_wilsonPlaqObs bd) 2 (abs_plaq_le hN bd) Finset.univ] at h
  exact h

/-- **The per-plaquette bound**: `|cum3 β F G φ_p| ≤ 12 · M_F · M_G`.
DERIVED: `12 = 2 + 2 + 2 + 2 + 4`, the five terms of `cum3` (coefficients 1, 1, 1, 1, 2) with `φ_p ≤ 2`. -/
theorem abs_cum3_plaq_le (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) (p : Pq) :
    |cum3 bd β F G (wilsonPlaqObs bd p)| ≤ 12 * (MF * MG) := by
  have hMF := bound_nonneg bd hFb
  have hMG := bound_nonneg bd hGb
  have hφ := abs_plaq_le hN bd p
  have hφm := measurable_wilsonPlaqObs (N := N) bd p
  have mul2 : ∀ {a b A B : ℝ}, |a| ≤ A → |b| ≤ B → 0 ≤ A → |a * b| ≤ A * B :=
    fun ha hb hA => by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA
  have bFGφ := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β
    (fun U => F U * G U * wilsonPlaqObs bd p U) ((hF.mul hG).mul hφm) (MF * MG * 2)
    (fun U => mul2 (mul2 (hFb U) (hGb U) hMF) (hφ U) (by positivity))
  have bFG := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β
    (fun U => F U * G U) (hF.mul hG) (MF * MG) (fun U => mul2 (hFb U) (hGb U) hMF)
  have bφ := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β _ hφm 2 hφ
  have bFφ := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β
    (fun U => F U * wilsonPlaqObs bd p U) (hF.mul hφm) (MF * 2)
    (fun U => mul2 (hFb U) (hφ U) hMF)
  have bGφ := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β
    (fun U => G U * wilsonPlaqObs bd p U) (hG.mul hφm) (MG * 2)
    (fun U => mul2 (hGb U) (hφ U) hMG)
  have bF := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β F hF MF hFb
  have bG := MassGap.WilsonReal.wilsonSystem_expect_abs_le hN bd β G hG MG hGb
  have t2 := mul2 bFG bφ (by positivity)
  have t3 := mul2 bFφ bG (by positivity)
  have t4 := mul2 bGφ bF (by positivity)
  have t5 := mul2 (mul2 bF bG hMF) bφ (by positivity)
  unfold cum3
  rw [abs_le]
  have a1 := abs_le.mp bFGφ
  have a2 := abs_le.mp t2
  have a3 := abs_le.mp t3
  have a4 := abs_le.mp t4
  have a5 := abs_le.mp t5
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2]

/-- **Contact plus separated**: for any predicate `C` on plaquettes,
`Σ_p cum3 φ_p = Σ_{p ∈ C} cum3 φ_p + Σ_{p ∉ C} cum3 φ_p`. DERIVED: no numeral. -/
theorem sum_cum3_split (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) (C : Pq → Prop)
    [DecidablePred C] :
    ∑ p, cum3 bd β F G (wilsonPlaqObs bd p)
      = ∑ p ∈ Finset.univ.filter C, cum3 bd β F G (wilsonPlaqObs bd p)
        + ∑ p ∈ Finset.univ.filter (fun p => ¬ C p), cum3 bd β F G (wilsonPlaqObs bd p) :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ C _).symm

/-- **The contact budget**: `|Σ_{p ∈ C} cum3 β F G φ_p| ≤ 12 · M_F · M_G · #C`.
DERIVED: `12` as in `abs_cum3_plaq_le`. -/
theorem abs_contact_le (hN : N ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) (s : Finset Pq) :
    |∑ p ∈ s, cum3 bd β F G (wilsonPlaqObs bd p)| ≤ 12 * (MF * MG) * s.card := by
  calc |∑ p ∈ s, cum3 bd β F G (wilsonPlaqObs bd p)|
      ≤ ∑ p ∈ s, |cum3 bd β F G (wilsonPlaqObs bd p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ s, 12 * (MF * MG) :=
        Finset.sum_le_sum fun p _ => abs_cum3_plaq_le hN bd β F G hF MF hFb hG MG hGb p
    _ = 12 * (MF * MG) * s.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The mean-value form along a coupling interval**: for `x < y` there is `ξ ∈ (x, y)` with
`cum2 y − cum2 x = −(y − x) Σ_p cum3 ξ F G φ_p`. DERIVED: `0` the excluded rank. -/
theorem cum2_sub_eq (hN : N ≠ 0) [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) {x y : ℝ} (hxy : x < y) :
    ∃ ξ ∈ Set.Ioo x y,
      cum2 bd y F G - cum2 bd x F G = -(y - x) * ∑ p, cum3 bd ξ F G (wilsonPlaqObs bd p) := by
  have hd := fun t => cum2_hasDerivAt_plaq hN bd t F G hF MF hFb hG MG hGb
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => cum2 bd t F G)
    (fun t => -∑ p, cum3 bd t F G (wilsonPlaqObs bd p)) hxy
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
  refine ⟨ξ, hξ, ?_⟩
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  rw [neg_mul, ← mul_neg, hslope, mul_div_assoc', mul_div_cancel_left₀ _ hne]

/-- **A two-point difference above the contact budget is a separated three-point reading**: for
`x < y` and any contact predicate `C`, at some `ξ ∈ (x, y)`,
`|cum2 y − cum2 x| / (y − x) − 12 M_F M_G #C ≤ |cum3 ξ F G (Σ_{p ∉ C} φ_p)|`.
DERIVED: `12` as in `abs_cum3_plaq_le`; `0` the excluded rank. -/
theorem separated_lower (hN : N ≠ 0) [DecidableEq Pq] (bd : Pq → List (Lk × Bool))
    (F G : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hF : Measurable F) (MF : ℝ) (hFb : ∀ U, |F U| ≤ MF)
    (hG : Measurable G) (MG : ℝ) (hGb : ∀ U, |G U| ≤ MG) {x y : ℝ} (hxy : x < y)
    (C : Pq → Prop) [DecidablePred C] :
    ∃ ξ ∈ Set.Ioo x y,
      |cum2 bd y F G - cum2 bd x F G| / (y - x)
          - 12 * (MF * MG) * (Finset.univ.filter C).card
        ≤ |cum3 bd ξ F G
            (fun U => ∑ p ∈ Finset.univ.filter (fun p => ¬ C p), wilsonPlaqObs bd p U)| := by
  obtain ⟨ξ, hξ, heq⟩ := cum2_sub_eq hN bd F G hF MF hFb hG MG hGb hxy
  refine ⟨ξ, hξ, ?_⟩
  have hpos : 0 < y - x := sub_pos.mpr hxy
  rw [cum3_sum hN bd ξ F G hF MF hFb hG MG hGb (wilsonPlaqObs bd)
    (measurable_wilsonPlaqObs bd) 2 (abs_plaq_le hN bd)]
  have hc := abs_contact_le hN bd ξ F G hF MF hFb hG MG hGb (Finset.univ.filter C)
  have hdiv : |cum2 bd y F G - cum2 bd x F G| / (y - x)
      = |∑ p, cum3 bd ξ F G (wilsonPlaqObs bd p)| := by
    rw [heq, abs_mul, abs_neg, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne']
  rw [hdiv, sum_cum3_split bd ξ F G C]
  have := abs_add_le (∑ p ∈ Finset.univ.filter C, cum3 bd ξ F G (wilsonPlaqObs bd p))
    (∑ p ∈ Finset.univ.filter (fun p => ¬ C p), cum3 bd ξ F G (wilsonPlaqObs bd p))
  linarith

end Finite

/-! ## 2. The same on the periodic torus states -/

section Torus

variable {N : ℕ}

open MassGap.PeriodicState

/-- **The connected two-point function of the periodic torus state** of extent `M + 1` on continuous
`ℤ⁴` observables. DERIVED: `4` the dimension; `1` in `M + 1` the extent's successor. -/
def torusCum2 (hN : N ≠ 0) (M : ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) : ℝ :=
  torusState hN M β (f * g) - torusState hN M β f * torusState hN M β g

/-- `torusCum2` is `cum2` at the hypercubic boundary word, on `torusObs`. DERIVED: `4` the dimension. -/
theorem torusCum2_eq (hN : N ≠ 0) (M : ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    torusCum2 hN M β f g
      = cum2 (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (torusObs M g) :=
  rfl

/-- **The trace-anomaly identity on the periodic torus**: `d/dβ torusCum2 = −Σ_p cum3 β f g φ_p`, the
sum over the plaquettes of the torus. DERIVED: `4` the dimension; `0` the excluded rank. -/
theorem torusCum2_hasDerivAt (hN : N ≠ 0) (M : ℕ) (β : ℝ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    HasDerivAt (fun x => torusCum2 hN M x f g)
      (-∑ p, cum3 (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (torusObs M g)
        (wilsonPlaqObs (WilsonHypercubic.bd (d := 4) (n := M + 1)) p)) β := by
  obtain ⟨Cf, hCf⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  obtain ⟨Cg, hCg⟩ := MassGap.InfiniteLattice.bounded_of_continuous g.continuous
  exact cum2_hasDerivAt_plaq hN (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f)
    (torusObs M g) (measurable_torusObs M f) Cf (fun _ => hCf _)
    (measurable_torusObs M g) Cg (fun _ => hCg _)

/-- **The separated lower bound on the periodic torus**: for `x < y` and any contact predicate `C` on
the torus plaquettes, at some `ξ ∈ (x, y)`,
`|torusCum2 y − torusCum2 x| / (y − x) − 12 M_f M_g #C ≤ |cum3 ξ f g (Σ_{p ∉ C} φ_p)|`, with `M_f`, `M_g`
any bounds of `f`, `g`. DERIVED: `12` as in `abs_cum3_plaq_le`; `4` the dimension. -/
theorem torus_separated_lower (hN : N ≠ 0) (M : ℕ)
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (Mf Mg : ℝ)
    (hfb : ∀ V, |f V| ≤ Mf) (hgb : ∀ V, |g V| ≤ Mg) {x y : ℝ} (hxy : x < y)
    (C : WilsonHypercubic.Plaq 4 (M + 1) → Prop) [DecidablePred C] :
    ∃ ξ ∈ Set.Ioo x y,
      |torusCum2 hN M y f g - torusCum2 hN M x f g| / (y - x)
          - 12 * (Mf * Mg) * (Finset.univ.filter C).card
        ≤ |cum3 (WilsonHypercubic.bd (d := 4) (n := M + 1)) ξ (torusObs M f) (torusObs M g)
            (fun U => ∑ p ∈ Finset.univ.filter (fun p => ¬ C p),
              wilsonPlaqObs (WilsonHypercubic.bd (d := 4) (n := M + 1)) p U)| :=
  separated_lower hN (WilsonHypercubic.bd (d := 4) (n := M + 1)) (torusObs M f) (torusObs M g)
    (measurable_torusObs M f) Mf (fun _ => hfb _)
    (measurable_torusObs M g) Mg (fun _ => hgb _) hxy C

end Torus

/-! ## 3. The two-point half of the link -/

section AF

variable {N : ℕ}

/-- `r₀ / 2^j → 0⁺`. DERIVED: `2` the halving; `0` the limit. -/
theorem tendsto_dyadic {r₀ : ℝ} (hr₀ : 0 < r₀) :
    Tendsto (fun j : ℕ => r₀ / 2 ^ j) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
  · exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  · exact div_pos hr₀ (by positivity)

/-- **Under `AFCoefficient` the profile `r⁸ G(r)` changes under dyadic halving infinitely often**: for
every `r₀ > 0`, `h(r₀/2^(j+1)) ≠ h(r₀/2^j)` for infinitely many `j`, `h(r) = r⁸ G(r)`.
DERIVED: `2` the least colour count and the halving; `8` the power of `AFCoefficient`. -/
theorem af_dyadic_frequently (hN2 : 2 ≤ N) {G : ℝ → ℝ} (hG : ClayStatement.AFCoefficient N G)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ᶠ j in atTop, (r₀ / 2 ^ (j + 1)) ^ 8 * G (r₀ / 2 ^ (j + 1)) ≠ (r₀ / 2 ^ j) ^ 8 * G (r₀ / 2 ^ j) := by
  set r : ℕ → ℝ := fun j => r₀ / 2 ^ j with hr
  set h : ℕ → ℝ := fun j => r j ^ 8 * G (r j) with hh
  by_contra hne
  rw [not_frequently] at hne
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hne
  have hconst : ∀ j, J ≤ j → h j = h J := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have := hJ n hn
      rw [not_not] at this
      show r (n + 1) ^ 8 * G (r (n + 1)) = h J
      rw [← ih]
      exact this
  have hlim : Tendsto (fun j => h j * Real.log (r j) ^ 2) atTop (𝓝 (ClayStatement.afConst N)) :=
    hG.comp (tendsto_dyadic hr₀)
  have hlog : Tendsto (fun j => Real.log (r j) ^ 2) atTop atTop := by
    have h1 := tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp (tendsto_dyadic hr₀))
    have h2 := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp h1
    refine h2.congr fun j => ?_
    show |Real.log (r₀ / 2 ^ j)| ^ 2 = Real.log (r₀ / 2 ^ j) ^ 2
    exact sq_abs _
  have hev : ∀ᶠ j in atTop, h j * Real.log (r j) ^ 2 = h J * Real.log (r j) ^ 2 :=
    eventually_atTop.mpr ⟨J, fun j hj => by rw [hconst j hj]⟩
  have hpos := ClayStatement.afConst_pos hN2
  by_cases hC : h J = 0
  · have h0 : Tendsto (fun j => h j * Real.log (r j) ^ 2) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hev.mono fun j hj => ?_)
      dsimp only
      rw [hj, hC, zero_mul]
    have := tendsto_nhds_unique hlim h0
    linarith
  · have habs : Tendsto (fun j => |h j * Real.log (r j) ^ 2|) atTop atTop := by
      have hc : Tendsto (fun j => |h J| * Real.log (r j) ^ 2) atTop atTop :=
        hlog.const_mul_atTop (abs_pos.mpr hC)
      refine hc.congr' (hev.mono fun j hj => ?_)
      dsimp only
      rw [hj, abs_mul (h J), abs_of_nonneg (sq_nonneg (Real.log (r j)))]
    exact not_tendsto_nhds_of_tendsto_atTop habs _ ((continuous_abs.tendsto _).comp hlim)

/-- **Under `AFCoefficient` the profile is not a pure power near `0`**: no `C`, `ε > 0` with
`r⁸ G(r) = C` on `(0, ε)`. DERIVED: `2` the least colour count; `8` the power of `AFCoefficient`. -/
theorem af_not_pure_power (hN2 : 2 ≤ N) {G : ℝ → ℝ} (hG : ClayStatement.AFCoefficient N G) :
    ¬ ∃ C ε : ℝ, 0 < ε ∧ ∀ r ∈ Set.Ioo 0 ε, r ^ 8 * G r = C := by
  rintro ⟨C, ε, hε, hC⟩
  have hsmall : ∀ᶠ j : ℕ in atTop, (1 : ℝ) / 2 ^ j ∈ Set.Ioo 0 ε :=
    (tendsto_dyadic one_pos).eventually (Ioo_mem_nhdsGT hε)
  obtain ⟨j, hj1, hj2⟩ := ((af_dyadic_frequently hN2 hG one_pos).and_eventually
    (hsmall.and ((tendsto_add_atTop_nat 1).eventually hsmall))).exists
  exact hj1 ((hC _ hj2.2).trans (hC _ hj2.1).symm)

end AF

end MassGap.ThreePointAnomaly

end

#print axioms MassGap.ThreePointAnomaly.cum2_hasDerivAt
#print axioms MassGap.ThreePointAnomaly.ex_mul_sum
#print axioms MassGap.ThreePointAnomaly.cum3_sum
#print axioms MassGap.ThreePointAnomaly.cum2_hasDerivAt_plaq
#print axioms MassGap.ThreePointAnomaly.abs_cum3_plaq_le
#print axioms MassGap.ThreePointAnomaly.sum_cum3_split
#print axioms MassGap.ThreePointAnomaly.abs_contact_le
#print axioms MassGap.ThreePointAnomaly.cum2_sub_eq
#print axioms MassGap.ThreePointAnomaly.separated_lower
#print axioms MassGap.ThreePointAnomaly.torusCum2_eq
#print axioms MassGap.ThreePointAnomaly.torusCum2_hasDerivAt
#print axioms MassGap.ThreePointAnomaly.torus_separated_lower
#print axioms MassGap.ThreePointAnomaly.tendsto_dyadic
#print axioms MassGap.ThreePointAnomaly.af_dyadic_frequently
#print axioms MassGap.ThreePointAnomaly.af_not_pure_power
