import Mathlib
import MassGap.BareRatioProof
import MassGap.ReflPosG
import MassGap.ShiftInvG
import MassGap.SymPlaqG
import MassGap.PeriodicState

/-!
# MassGap.PlaqPositive — signs and log-convexity of the bare plaquette correlator from reflection positivity

`BareRatioProof` reduces the count bound to `RelSum` (the bare correlator `C ≥ 0` on the box and
`∑_z C(z) ≤ K₀ C(0)`) or to the weaker `LowModeRatio`. This module proves what reflection positivity and
translation invariance give for a reflection-invariant local reading `F` (every member of
`SymPlaqG.SymPlaqClassG`, by `SymPlaqG.symG_refl`), and states what they do not give. Declarations are in the
namespace `MassGap.PlaqPositive`.

Throughout, `Γ_F(n) = ν(F · T_{n e_τ} F)` (`lag`), `T` the lattice translation `ContinuumField.transObs`, and
`D` a depth of the support of `F` below the plane `x_τ = 0` (every support link has `l.2 τ ≥ −D`; every finite
support has one, `ContinuumField.exists_depth`).

## 1. Reflection of a translate (proved)

`ireflSite_add`, `ireflSite_axisVec`, `ireflObs_transObs`: `θ_c(T_x F) = T_{ρ_c x}(θ_0 F)` with
`ρ_c x = ireflSite τ c x`, at every reflection constant `c` of either parity. So for `θ_0 F = F`,
`θ_c(T_{a e_τ} F) = T_{(c − a) e_τ} F`: the reflected translate is the translate at the mirror point.

## 2. Reflected pairs and the Cauchy–Schwarz inequality (proved)

`rp_quadratic`: if `ν` is translation invariant and reflection positive at constant `c` on `halfSpaceAlg τ 0`,
`θ_0 F = F`, and `T_{a e_τ} F`, `T_{b e_τ} F` lie in `halfSpaceAlg τ 0`, then for every real `t`,
`0 ≤ Γ(2a − c) + 2t Γ(a + b − c) + t² Γ(2b − c)`. No reflection invariance of `ν` enters: both cross terms
are `Γ(a + b − c)` by translation invariance alone. `rp_lag_nonneg`: `0 ≤ Γ(2a − c)`. `rp_lag_cs`:
`Γ(a + b − c)² ≤ Γ(2a − c) Γ(2b − c)`. `lag_abs_le`: `|Γ(n)| ≤ ‖F‖²`.

## 3. Axis positivity (proved)

`Deep τ D F`: every translate `T_x F` with `x_τ ≥ D` lies in `halfSpaceAlg τ 0` (`deep_of_local` from a support
of depth `D`). With site reflection positivity (constant `0`): `lag_even_nonneg`, `Γ(2a) ≥ 0` for `a ≥ D`. With
link reflection positivity (constant `−1`): `lag_odd_nonneg`, `Γ(2a + 1) ≥ 0` for `a ≥ D`. `lag_nonneg_of_both`:
with both, `Γ(n) ≥ 0` for every `n ≥ 2D`. Pairs at separation below `2D` have overlapping supports and are not
reflected pairs; nothing here signs them, apart from `Γ(0) = ν(F²) ≥ 0`.

## 4. Log-convexity and monotonicity (proved)

`antitone_of_logConvex` (scalar): a non-negative sequence, bounded above, with `g_{j+1}² ≤ g_j g_{j+2}`, is
non-increasing (log-convex gives convex by AM–GM; a convex sequence bounded above does not increase).

Site reflection positivity alone: `lag_even_antitone`, `Γ(2a + 2) ≤ Γ(2a)` for `a ≥ D` (the even lags are
log-convex in steps of `2`); `lag_odd_cs`, `Γ(2a + 1)² ≤ Γ(2a) Γ(2a + 2)`; `lag_odd_abs_le`,
`|Γ(2a + 1)| ≤ Γ(2a)`. With link reflection positivity as well: `lag_logConvex`,
`Γ(n)² ≤ Γ(n − 1) Γ(n + 1)` for `n ≥ 2D + 1`, and `lag_antitone`, `Γ(n + 1) ≤ Γ(n)` for `n ≥ 2D`.

## 5. Slice sums (proved)

`sliceSum Y F = ∑_{y ∈ Y} T_y F` for a finite set `Y` of transverse vectors (`y_τ = 0`). `sliceSum_refl`: it is
again `θ_0`-invariant; `sliceSum_deep`: it has the depth of `F`. `sliceSum_lag`:
`Γ_{sliceSum}(n) = ∑_{y, y' ∈ Y} ν(T_y F · T_{y' + n e_τ} F)`, the time-slice-summed correlator on `Y`. So every
statement of §3–§4 holds for the slice-summed correlator: non-negative at `n ≥ 2D` (even `n` from site
reflection positivity), log-convex, and non-increasing along the even lags; at every lag `n ≥ 2D` when link
reflection positivity is available. This is the content of `Γ(n) = ∑_λ |c_λ|² λ^{n − 2D}` beyond the overlap
without the transfer operator: `lag_logConvex` and boundedness are the two facts the spectral form is used for.

## 6. The Wilson tower (proved)

`canon_bareScreen_axis`: for every gauge group with `GaugeSimple`, every `O ∈ SymPlaqClassG G` and every
direction `τ`, one `D` with `0 ≤ ν_k(P_x P_y)` for every step `k` and every pair of screen sites with
`y = x + 2a e_τ`, `a ≥ D`: site reflection positivity of `canonSched G` (`ReflPosG.periodicStateG_reflPositive`)
and its translation invariance (`ShiftInvG.periodicStateG_shift`). `canon_slice_even_antitone`: the slice sums of
the bare reading are non-increasing along the even lags `≥ 2D`, at every step. `su_bareScreen_axis`: at
`schedSU N`, the same for every separation `n ≥ 2D` of either parity, from the link reflection positivity
`PeriodicState.periodicState_reflPositive_odd` (coupling `dyBeta ≥ 1`). `su_slice_antitone`: the slice sums are
non-increasing at every lag `≥ 2D`.

## 7. Which orientations

`SymPlaqClassG` is `symG (plaqFieldG q)`: the sum of the Wilson density over all `384` hypercubic images
(`4!` axis permutations, `2⁴` sign flips) of the plaquette `q`. Its reflection invariance `θ_0 O = O` is
`SymPlaqG.symG_refl`, a theorem about the sum: the reflected copy of each oriented image is another summand. The
orientation reversal of a plaquette in a plane containing `τ` (`LatticeReflection.ihol_ireflConf`: the reflected
holonomy is conjugate to the holonomy of the transposed, reversed plaquette) never needs `Re tr U⁻¹ = Re tr U`
here, because the reversed loop is a summand. The covered correlator is that of the symmetrized field: all six
planes and both orientations enter together, not an oriented plaquette alone. For one oriented plaquette
`plaqFieldG q`, `θ_0` maps it to the mirror plaquette's field (for planes transverse to `τ`, conjugator `1`)
or to the reversed one (planes containing `τ`), so it is not a `θ_0`-invariant reading and §3 does not apply
to it directly. For `q₀` (the `(0, 1)` plaquette at the origin) the images have support links with base
coordinate in `{−1, 0, 1}` along every axis, so the depth is `D = 1` (argued from `ireflLink`; the Lean
statements take `D` from `exists_depth`): axis positivity at `n = 0` and `n ≥ 2`, and `n = 1` is the overlap.

## 8. The paper tests of `LowModeRatio`

Argued, not formalized.

* Point-like readings (`D = 0`). With site and link reflection positivity, `Γ_{p⊥}(n) = ∫ λ^{|n|} dρ_{p⊥}(λ)`,
  `ρ_{p⊥} ≥ 0` on `[0, 1]`, for the slice sums weighted by `cos(p⊥ · y)` (transverse weights keep `θ_0`
  invariance, §5). So `Ĉ(p_τ, p⊥) = ∫ (1 − λ²)/(1 − 2λ cos p_τ + λ²) dρ_{p⊥}` is non-increasing in `|p_τ|`, and
  iterating over the four directions, `sup_p Ĉ(p) = Ĉ(0)` and `Ĉ(0) ≥ Γ(0) ≥ … ≥ C(0)`. Off-axis negative entries
  cannot break this: the slice sums absorb them. In the box, a light state (`1 − λ ≪ 1/L`) acts as a near-constant
  block, whose operator norm is at most `(π²/8)⁴` times its lowest-mode variance (per axis: `L` for the constant
  block against `(∑_n sin(π(n + 1)/(L + 1)))² · 2/(L + 1) → 8L/π²`); a heavy state (`1 − λ ≫ 1/L`) has both near
  `Ĉ_λ(0)`. So `LowModeRatio` holds for point-like readings with a fixed `Q'`.
* Free composite (`C ≥ 0` everywhere, `C ~ |z|^{−8}`): `RelSum` holds (`BareRatioProof` §5), so `LowModeRatio`
  holds at `Q' = K₀`. Consistent with §3: the overlap entries are positive there.
* The class has `D = 1`. The even sublattice `(2ℤ)⁴` sees the field as point-like for site reflections (supports
  of fields two apart meet only on the mirror plane, which `halfSpaceAlg` contains), and the transfer by two steps
  is a square, so the point-like bullet holds on `(2ℤ)⁴` from site reflection positivity alone: `Ĉ₂(p) ≤ Ĉ₂(0)` and
  `Ĉ₂(0) = ∑_{z ∈ (2ℤ)⁴} C(z) ≥ C(0)`. The full box covariance is a `16 × 16` block matrix over the cosets; positive
  semidefiniteness gives `‖C‖ ≤ 16 max_a ‖C_{aa}‖`, and each diagonal block is the sublattice covariance, for
  which the point-like bullet gives `‖C_{aa}‖ ≤ Q₂ ν((∑_{x even} v_x P_x)²)` with `v` the lowest Dirichlet mode. The
  upper side is therefore controlled by the even sublattice. The sublattice step uses the transfer by two lattice
  steps as a positive contraction (`T²`, from site reflection positivity and reflection invariance), which
  `lag_even_antitone` and `lag_even_cs` express without the operator.
* The lower side is not. The lowest Dirichlet mode reads `∑_z C(z)`, which includes the odd cosets, whose nearest
  entries (separation `1` in a direction) are overlap pairs. The one-dimensional profile `Γ(0) = 1`,
  `Γ(±1) = −1/2`, `Γ(n) = 0` for `|n| ≥ 2` satisfies every constraint of §2–§4 (the reflected part vanishes,
  `Ĉ(p) = 1 − cos p ≥ 0`) and has `Ĉ(0) = 0`: the lowest-mode variance tends to `0` while the operator norm stays
  `2`. So reflection positivity does not give `LowModeRatio` for a reading of depth `1`, and the obstruction is
  exactly the overlap.

## What does not follow

* `LowModeRatio` and `RelSum` are not proved. The upper half of `LowModeRatio` (the operator norm against the even
  sublattice's integrated correlator) is argued in §8, not formalized; the Toeplitz bound and the spectral form in
  infinite volume are not in the tree.
* The remaining inequality: one `κ > 0` with, eventually along the tower and for every `O ∈ D`,
  `ν_k((∑_x v_x P_x)²) ≥ κ ν_k((∑_{x ∈ (2ℤ)⁴} v_x P_x)²)` for the lowest Dirichlet mode `v` of the screen box —
  the full lowest-mode variance is at least a fixed fraction of its even-sublattice part, so the overlap
  correlations do not cancel it. With §8's upper half it gives `LowModeRatio` at `Q' = 16 Q₂ / κ` (argued). In
  momentum form, `∑_z C(z) ≥ κ ∑_{z ∈ (2ℤ)⁴} C(z)`. Reflection positivity is silent on it (the profile of §8).
* Separations below `2D` (for `q₀`'s class: separation `1` along an axis, and every pair whose separation is
  below `2D` in every direction) are not signed. Off-axis entries are not signed individually at any separation;
  only their slice sums are.
* Link reflection positivity is in the tree for `SU(N)` at `β ≥ 0` only (`PeriodicState.periodicState_reflPositive_odd`);
  `ReflPosG` has the even constant only, so for a general `G` the odd lags are bounded (`lag_odd_abs_le`) but not
  signed.
* The transfer operator's spectral representation is not used; the log-convexity is proved directly by
  Cauchy–Schwarz for the reflected pairing.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the plane `x_τ = 0`, the site reflection constant, the signs and the transverse
coordinate; `−1` the link reflection constant (`2 · 0 − 1`), the plane between `x_τ = −1` and `x_τ = 0`; `1` the
lattice step and the next lag; `2` the reflected separation `2a − c`, the square, the even lags and the AM–GM
halving; `4` the dimension and the discriminant. `16` (the cosets of `(2ℤ)⁴`), `384`, `π²/8` and the `8` of `8L/π²` appear only in the
argued §7–§8, COMPUTED there from `2⁴`, `4! 2⁴` and the lowest sine. `D` is from `exists_depth`; `τ`, `a`, `b`,
`t`, `Y` are hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.PlaqPositive

open Finset Filter
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.LatticeReflection
  MassGap.HalfSpaceAlgebra MassGap.InfiniteReflection MassGap.ClayTreeG MassGap.CountMoments
  MassGap.ApertureFinite
open MassGap.ApertureModes (apSite)

/-! ## 1. Reflection of a translate -/

/-- **The site reflection of a sum**: `ρ_{c'}(s + x) = ρ_d s + ρ_c x` when `c' = d + c`. DERIVED: no numeral. -/
theorem ireflSite_add (τ : Fin 4) (c c' d : ℤ) (h : c' = d + c) (s x : ISite) :
    ireflSite τ c' (s + x) = ireflSite τ d s + ireflSite τ c x := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp only [ireflSite, Pi.add_apply, Function.update_self]
    omega
  · simp only [ireflSite, Pi.add_apply, Function.update_of_ne hj]

/-- **The reflection of an axis vector**: `ρ_c(a e_τ) = (c − a) e_τ`. DERIVED: `0` the off-axis value. -/
theorem ireflSite_axisVec (τ : Fin 4) (c a : ℤ) : ireflSite τ c (axisVec τ a) = axisVec τ (c - a) := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp [ireflSite, axisVec]
  · simp [ireflSite, axisVec, hj]

/-- **A transverse vector is fixed by the site reflection at `0`**. DERIVED: `0` the constant and the
coordinate. -/
theorem ireflSite_zero_of_transverse (τ : Fin 4) (y : ISite) (hy : y τ = 0) : ireflSite τ 0 y = y := by
  funext j
  by_cases hj : j = τ
  · subst hj
    simp [ireflSite, hy]
  · simp [ireflSite, Function.update_of_ne hj]

/-- **The difference of two axis vectors**. DERIVED: `0` the off-axis value. -/
theorem axisVec_sub (τ : Fin 4) (a b : ℤ) : axisVec τ b - axisVec τ a = axisVec τ (b - a) := by
  funext j
  by_cases hj : j = τ
  · simp [axisVec, hj]
  · simp [axisVec, hj]

section Geometry

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The reflection of a translate is the translate at the mirror point**:
`θ_c(T_x F) = T_{ρ_c x}(θ_0 F)`, at every reflection constant `c`. DERIVED: `1` the link offset `c − 1` of
`ireflLink`; `0` the reference reflection. -/
theorem ireflObs_transObs (τ : Fin 4) (c : ℤ) (x : ISite) (F : C(IConf G, ℝ)) :
    ireflObs τ c (transObs x F) = transObs (ireflSite τ c x) (ireflObs τ 0 F) := by
  ext U
  show F (transConf x (ireflConf τ c U)) = F (ireflConf τ 0 (transConf (ireflSite τ c x) U))
  congr 1
  funext l
  obtain ⟨d, s⟩ := l
  have e1 : ireflSite τ (c - 1) (s + x) = ireflSite τ (0 - 1) s + ireflSite τ c x :=
    ireflSite_add τ c (c - 1) (0 - 1) (by ring) s x
  have e0 : ireflSite τ c (s + x) = ireflSite τ 0 s + ireflSite τ c x :=
    ireflSite_add τ c c 0 (by ring) s x
  show (if d = τ then (U (d, if d = τ then ireflSite τ (c - 1) (s + x) else ireflSite τ c (s + x)))⁻¹
      else U (d, if d = τ then ireflSite τ (c - 1) (s + x) else ireflSite τ c (s + x)))
    = (if d = τ then (U (d, (if d = τ then ireflSite τ (0 - 1) s else ireflSite τ 0 s) + ireflSite τ c x))⁻¹
      else U (d, (if d = τ then ireflSite τ (0 - 1) s else ireflSite τ 0 s) + ireflSite τ c x))
  by_cases h : d = τ
  · simp only [if_pos h, e1]
  · simp only [if_neg h, e0]

/-- **A reflection-invariant reading, translated along the axis**: `θ_c(T_{a e_τ} F) = T_{(c − a) e_τ} F`.
DERIVED: `0` the reference reflection. -/
theorem ireflObs_transObs_axis (τ : Fin 4) (c a : ℤ) {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) :
    ireflObs τ c (transObs (axisVec τ a) F) = transObs (axisVec τ (c - a)) F := by
  rw [ireflObs_transObs, ireflSite_axisVec, hF]

end Geometry

#print axioms ireflSite_add
#print axioms ireflSite_axisVec
#print axioms ireflSite_zero_of_transverse
#print axioms axisVec_sub
#print axioms ireflObs_transObs
#print axioms ireflObs_transObs_axis

/-! ## 2. Reflected pairs and the Cauchy–Schwarz inequality -/

section Pair

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  (ν : MassGap.DLRLimit.State (IConf G))

/-- **The axis lag correlator** `Γ_F(n) = ν(F · T_{n e_τ} F)`. DERIVED: no numeral. -/
def lag (τ : Fin 4) (F : C(IConf G, ℝ)) (n : ℤ) : ℝ := ν (F * transObs (axisVec τ n) F)

/-- **A pair of translates under a translation-invariant state**: `ν(T_u F · T_v H) = ν(F · T_{v − u} H)`.
DERIVED: no numeral. -/
theorem pair_trans (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (u v : ISite) (F H : C(IConf G, ℝ)) :
    ν (transObs u F * transObs v H) = ν (F * transObs (v - u) H) := by
  have e : transObs v H = transObs u (transObs (v - u) H) := by
    rw [transObs_transObs]
    congr 1
    abel_nf
  rw [e, ← transObs_mul, hT]

/-- **A pair of axis translates**: `ν(T_{u e_τ} F · T_{v e_τ} F) = Γ(v − u)`. DERIVED: no numeral. -/
theorem pair_axis (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (F : C(IConf G, ℝ)) (u v : ℤ) :
    ν (transObs (axisVec τ u) F * transObs (axisVec τ v) F) = lag ν τ F (v - u) := by
  rw [pair_trans ν hT, axisVec_sub]
  rfl

/-- **The reflected quadratic form**: under translation invariance and reflection positivity at constant `c`
on `halfSpaceAlg τ 0`, for `θ_0 F = F` and both translates in the half-space algebra,
`0 ≤ Γ(2a − c) + 2t Γ(a + b − c) + t² Γ(2b − c)`. DERIVED: `2` the reflected separations and the cross term. -/
theorem rp_quadratic (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (c : ℤ) (hRP : ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {a b : ℤ}
    (ha : transObs (axisVec τ a) F ∈ halfSpaceAlg (G := G) τ 0)
    (hb : transObs (axisVec τ b) F ∈ halfSpaceAlg (G := G) τ 0) (t : ℝ) :
    0 ≤ lag ν τ F (2 * a - c) + 2 * t * lag ν τ F (a + b - c) + t * t * lag ν τ F (2 * b - c) := by
  set A := transObs (axisVec τ a) F
  set B := transObs (axisVec τ b) F
  have hf : A + t • B ∈ halfSpaceAlg (G := G) τ 0 := (halfSpaceAlg τ 0).add_mem ha ((halfSpaceAlg τ 0).smul_mem t hb)
  have h := hRP _ hf
  have hθ : (latticeReflection (G := G) τ c).θ (A + t • B)
      = transObs (axisVec τ (c - a)) F + t • transObs (axisVec τ (c - b)) F := by
    show ireflObs τ c (A + t • B) = _
    rw [map_add, map_smul, ireflObs_transObs_axis τ c a hF, ireflObs_transObs_axis τ c b hF]
  rw [hθ] at h
  have hexp : ν ((transObs (axisVec τ (c - a)) F + t • transObs (axisVec τ (c - b)) F) * (A + t • B))
      = ν (transObs (axisVec τ (c - a)) F * A) + t * ν (transObs (axisVec τ (c - a)) F * B)
        + t * ν (transObs (axisVec τ (c - b)) F * A)
        + t * t * ν (transObs (axisVec τ (c - b)) F * B) := by
    rw [add_mul, mul_add, mul_add, ν.map_add, ν.map_add, ν.map_add]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, MassGap.DLRLimit.State.map_smul]
    ring
  rw [hexp, pair_axis ν hT, pair_axis ν hT, pair_axis ν hT, pair_axis ν hT] at h
  have e1 : a - (c - a) = 2 * a - c := by ring
  have e2 : b - (c - a) = a + b - c := by ring
  have e3 : a - (c - b) = a + b - c := by ring
  have e4 : b - (c - b) = 2 * b - c := by ring
  rw [e1, e2, e3, e4] at h
  linarith

/-- **Reflected pairs are non-negative**: `0 ≤ Γ(2a − c)`. DERIVED: `0` the test coefficient `t`. -/
theorem rp_lag_nonneg (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (c : ℤ) (hRP : ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {a : ℤ}
    (ha : transObs (axisVec τ a) F ∈ halfSpaceAlg (G := G) τ 0) :
    0 ≤ lag ν τ F (2 * a - c) := by
  have h := rp_quadratic ν hT τ c hRP hF ha ha 0
  simpa using h

/-- **Cauchy–Schwarz for the reflected pairing**: `Γ(a + b − c)² ≤ Γ(2a − c) Γ(2b − c)`.
DERIVED: `2` the square; `4` the discriminant. -/
theorem rp_lag_cs (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (c : ℤ) (hRP : ReflPositiveOn (latticeReflection τ c) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {a b : ℤ}
    (ha : transObs (axisVec τ a) F ∈ halfSpaceAlg (G := G) τ 0)
    (hb : transObs (axisVec τ b) F ∈ halfSpaceAlg (G := G) τ 0) :
    lag ν τ F (a + b - c) ^ 2 ≤ lag ν τ F (2 * a - c) * lag ν τ F (2 * b - c) := by
  have hq : ∀ x : ℝ, 0 ≤ lag ν τ F (2 * b - c) * (x * x) + 2 * lag ν τ F (a + b - c) * x
      + lag ν τ F (2 * a - c) := fun x => by
    have := rp_quadratic ν hT τ c hRP hF ha hb x
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  linarith

/-- **The lag correlator is bounded**: `|Γ(n)| ≤ ‖F‖²`. DERIVED: `2` the square. -/
theorem lag_abs_le (τ : Fin 4) (F : C(IConf G, ℝ)) (n : ℤ) : |lag ν τ F n| ≤ ‖F‖ ^ 2 := by
  unfold lag
  calc |ν (F * transObs (axisVec τ n) F)| ≤ ‖F * transObs (axisVec τ n) F‖ := ν.abs_le_norm _
    _ ≤ ‖F‖ * ‖transObs (axisVec τ n) F‖ := norm_mul_le _ _
    _ ≤ ‖F‖ * ‖F‖ := mul_le_mul_of_nonneg_left (norm_transObs_le _ _) (norm_nonneg _)
    _ = ‖F‖ ^ 2 := (sq _).symm

end Pair

#print axioms pair_trans
#print axioms pair_axis
#print axioms rp_quadratic
#print axioms rp_lag_nonneg
#print axioms rp_lag_cs
#print axioms lag_abs_le

/-! ## 3. Axis positivity -/

section Axis

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  (ν : MassGap.DLRLimit.State (IConf G))

/-- **Depth `D` in direction `τ`**: every translate `T_x F` with `x_τ ≥ D` lies in `halfSpaceAlg τ 0`.
DERIVED: `0` the plane. -/
def Deep (τ : Fin 4) (D : ℕ) (F : C(IConf G, ℝ)) : Prop :=
  ∀ x : ISite, (D : ℤ) ≤ x τ → transObs x F ∈ halfSpaceAlg (G := G) τ 0

/-- **A support of depth `D` gives `Deep τ D`**. DERIVED: `0` the plane. -/
theorem deep_of_local {τ : Fin 4} {D : ℕ} {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hS : IsLocalOn S (F : IConf G → ℝ)) (hD : ∀ l ∈ S, -(l.2 τ) ≤ (D : ℤ)) : Deep τ D F :=
  fun x hx => transObs_mem_halfSpaceAlg hS τ x fun l hl => by have := hD l hl; omega

/-- **Every local reading has a depth**. DERIVED: no numeral. -/
theorem exists_deep (τ : Fin 4) {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hS : IsLocalOn S (F : IConf G → ℝ)) : ∃ D : ℕ, Deep τ D F := by
  obtain ⟨D, hD⟩ := exists_depth τ S
  exact ⟨D, deep_of_local hS hD⟩

/-- The axis translate of a deep reading. DERIVED: no numeral. -/
theorem deep_axis {τ : Fin 4} {D : ℕ} {F : C(IConf G, ℝ)} (h : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    transObs (axisVec τ a) F ∈ halfSpaceAlg (G := G) τ 0 :=
  h _ (by simpa [axisVec] using ha)

/-- **Even lags beyond the overlap are non-negative** (site reflection positivity, constant `0`):
`Γ(2a) ≥ 0` for `a ≥ D`. DERIVED: `0` the site reflection constant; `2` the reflected separation. -/
theorem lag_even_nonneg (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    0 ≤ lag ν τ F (2 * a) := by
  have h := rp_lag_nonneg ν hT τ 0 hRP hF (deep_axis hD ha)
  simpa using h

/-- **Odd lags beyond the overlap are non-negative** (link reflection positivity, constant `−1`):
`Γ(2a + 1) ≥ 0` for `a ≥ D`. DERIVED: `−1` the link reflection constant; `2`, `1` the separation. -/
theorem lag_odd_nonneg (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ (-1)) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    0 ≤ lag ν τ F (2 * a + 1) := by
  have h := rp_lag_nonneg ν hT τ (-1) hRP hF (deep_axis hD ha)
  have e : 2 * a - -1 = 2 * a + 1 := by ring
  rwa [e] at h

/-- **Every lag beyond the overlap is non-negative**, given both reflection positivities: `Γ(n) ≥ 0` for
`n ≥ 2D`. DERIVED: `2` the overlap width `2D` and the parity split. -/
theorem lag_nonneg_of_both (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP0 : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    (hRP1 : ReflPositiveOn (latticeReflection τ (-1)) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {n : ℤ}
    (hn : 2 * (D : ℤ) ≤ n) : 0 ≤ lag ν τ F n := by
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' n
  · exact lag_even_nonneg ν hT τ hRP0 hF hD (by omega)
  · exact lag_odd_nonneg ν hT τ hRP1 hF hD (by omega)

end Axis

#print axioms deep_of_local
#print axioms exists_deep
#print axioms deep_axis
#print axioms lag_even_nonneg
#print axioms lag_odd_nonneg
#print axioms lag_nonneg_of_both

/-! ## 4. Log-convexity and monotonicity -/

/-- **A bounded, non-negative, log-convex sequence is non-increasing**: `g ≥ 0`, `g ≤ M`,
`g_{j+1}² ≤ g_j g_{j+2}` give `g_{j+1} ≤ g_j`. DERIVED: `2` the square and the AM–GM step; `1` the index step. -/
theorem antitone_of_logConvex (g : ℕ → ℝ) (hpos : ∀ j, 0 ≤ g j) {M : ℝ} (hM : ∀ j, g j ≤ M)
    (hlc : ∀ j, g (j + 1) ^ 2 ≤ g j * g (j + 2)) (j : ℕ) : g (j + 1) ≤ g j := by
  have hcv : ∀ i, 2 * g (i + 1) ≤ g i + g (i + 2) := by
    intro i
    have h1 : (2 * g (i + 1)) ^ 2 ≤ (g i + g (i + 2)) ^ 2 := by
      nlinarith [hlc i, sq_nonneg (g i - g (i + 2))]
    exact le_of_pow_le_pow_left₀ two_ne_zero (add_nonneg (hpos i) (hpos (i + 2))) h1
  have hinc : ∀ i, g (j + 1) - g j ≤ g (j + i + 1) - g (j + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hcv (j + i)
      have e1 : j + (i + 1) + 1 = j + i + 2 := by ring
      have e2 : j + (i + 1) = j + i + 1 := by ring
      rw [e1, e2]
      linarith
  have hlin : ∀ i : ℕ, g j + (i : ℝ) * (g (j + 1) - g j) ≤ g (j + i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hinc i
      push_cast
      have e : j + (i + 1) = j + i + 1 := by ring
      have e' : g j + ((i : ℝ) + 1) * (g (j + 1) - g j)
          = (g j + (i : ℝ) * (g (j + 1) - g j)) + (g (j + 1) - g j) := by ring
      rw [e, e']
      linarith
  by_contra hcon
  have hd : 0 < g (j + 1) - g j := by linarith [not_le.mp hcon]
  obtain ⟨i, hi⟩ := exists_nat_gt ((M - g j) / (g (j + 1) - g j))
  have h1 : M - g j < (i : ℝ) * (g (j + 1) - g j) := by
    rwa [div_lt_iff₀ hd] at hi
  have := hlin i
  linarith [hM (j + i)]

#print axioms antitone_of_logConvex

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  (ν : MassGap.DLRLimit.State (IConf G))

/-- **The odd lags between even ones** (site reflection positivity): `Γ(2a + 1)² ≤ Γ(2a) Γ(2a + 2)` for
`a ≥ D`. DERIVED: `0` the site constant; `2`, `1` the lags. -/
theorem lag_odd_cs (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    lag ν τ F (2 * a + 1) ^ 2 ≤ lag ν τ F (2 * a) * lag ν τ F (2 * a + 2) := by
  have h := rp_lag_cs ν hT τ 0 hRP hF (deep_axis hD ha) (deep_axis hD (a := a + 1) (by omega))
  have e1 : a + (a + 1) - 0 = 2 * a + 1 := by ring
  have e2 : 2 * a - 0 = 2 * a := by ring
  have e3 : 2 * (a + 1) - 0 = 2 * a + 2 := by ring
  rwa [e1, e2, e3] at h

/-- **The even lags are log-convex in steps of two** (site reflection positivity):
`Γ(2a + 2)² ≤ Γ(2a) Γ(2a + 4)` for `a ≥ D`. DERIVED: `0` the site constant; `2`, `4` the lags. -/
theorem lag_even_cs (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    lag ν τ F (2 * a + 2) ^ 2 ≤ lag ν τ F (2 * a) * lag ν τ F (2 * a + 4) := by
  have h := rp_lag_cs ν hT τ 0 hRP hF (deep_axis hD ha) (deep_axis hD (a := a + 2) (by omega))
  have e1 : a + (a + 2) - 0 = 2 * a + 2 := by ring
  have e2 : 2 * a - 0 = 2 * a := by ring
  have e3 : 2 * (a + 2) - 0 = 2 * a + 4 := by ring
  rwa [e1, e2, e3] at h

/-- **The even lags beyond the overlap are non-increasing** (site reflection positivity):
`Γ(2a + 2) ≤ Γ(2a)` for `a ≥ D`. DERIVED: `2` the even lags; `1` the index step. -/
theorem lag_even_antitone (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    lag ν τ F (2 * a + 2) ≤ lag ν τ F (2 * a) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, a = (D : ℤ) + j := ⟨(a - D).toNat, by omega⟩
  let g : ℕ → ℝ := fun i => lag ν τ F (2 * ((D : ℤ) + i))
  have hg : ∀ i, 0 ≤ g i := fun i => lag_even_nonneg ν hT τ hRP hF hD (by omega)
  have hM : ∀ i, g i ≤ ‖F‖ ^ 2 := fun i => (le_abs_self _).trans (lag_abs_le ν τ F _)
  have hlc : ∀ i, g (i + 1) ^ 2 ≤ g i * g (i + 2) := by
    intro i
    have h := lag_even_cs ν hT τ hRP hF hD (a := (D : ℤ) + i) (by omega)
    have e1 : 2 * ((D : ℤ) + ((i + 1 : ℕ) : ℤ)) = 2 * ((D : ℤ) + i) + 2 := by push_cast; ring
    have e2 : 2 * ((D : ℤ) + ((i + 2 : ℕ) : ℤ)) = 2 * ((D : ℤ) + i) + 4 := by push_cast; ring
    show lag ν τ F (2 * ((D : ℤ) + ((i + 1 : ℕ) : ℤ))) ^ 2
      ≤ lag ν τ F (2 * ((D : ℤ) + (i : ℤ))) * lag ν τ F (2 * ((D : ℤ) + ((i + 2 : ℕ) : ℤ)))
    rw [e1, e2]
    exact h
  have h := antitone_of_logConvex g hg hM hlc j
  have e : 2 * ((D : ℤ) + ((j + 1 : ℕ) : ℤ)) = 2 * ((D : ℤ) + j) + 2 := by push_cast; ring
  show lag ν τ F (2 * ((D : ℤ) + j) + 2) ≤ g j
  rw [← e]
  exact h

/-- **The odd lags are bounded by the even ones** (site reflection positivity): `|Γ(2a + 1)| ≤ Γ(2a)` for
`a ≥ D`. DERIVED: `2`, `1` the lags; `0` the sign. -/
theorem lag_odd_abs_le (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {a : ℤ} (ha : (D : ℤ) ≤ a) :
    |lag ν τ F (2 * a + 1)| ≤ lag ν τ F (2 * a) := by
  have h1 := lag_odd_cs ν hT τ hRP hF hD ha
  have h2 := lag_even_antitone ν hT τ hRP hF hD ha
  have h0 := lag_even_nonneg ν hT τ hRP hF hD ha
  have h3 : 0 ≤ lag ν τ F (2 * a + 2) := by
    have := lag_even_nonneg ν hT τ hRP hF hD (a := a + 1) (by omega)
    have e : 2 * (a + 1) = 2 * a + 2 := by ring
    rwa [e] at this
  have h4 : lag ν τ F (2 * a + 1) ^ 2 ≤ lag ν τ F (2 * a) ^ 2 := by
    calc lag ν τ F (2 * a + 1) ^ 2 ≤ lag ν τ F (2 * a) * lag ν τ F (2 * a + 2) := h1
      _ ≤ lag ν τ F (2 * a) * lag ν τ F (2 * a) := mul_le_mul_of_nonneg_left h2 h0
      _ = lag ν τ F (2 * a) ^ 2 := (sq _).symm
  rw [← abs_of_nonneg h0]
  exact sq_le_sq.mp h4

/-- **Log-convexity at every lag beyond the overlap**, given both reflection positivities:
`Γ(n)² ≤ Γ(n − 1) Γ(n + 1)` for `n ≥ 2D + 1`. DERIVED: `1` the neighbouring lags; `2` the overlap width. -/
theorem lag_logConvex (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP0 : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    (hRP1 : ReflPositiveOn (latticeReflection τ (-1)) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {n : ℤ}
    (hn : 2 * (D : ℤ) + 1 ≤ n) : lag ν τ F n ^ 2 ≤ lag ν τ F (n - 1) * lag ν τ F (n + 1) := by
  obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' n
  · -- `n = 2a` with `a ≥ D + 1`: the odd constant, at the pair `(a − 1, a)`.
    have h := rp_lag_cs ν hT τ (-1) hRP1 hF (deep_axis hD (a := a - 1) (by omega))
      (deep_axis hD (a := a) (by omega))
    have e1 : a - 1 + a - -1 = 2 * a := by ring
    have e2 : 2 * (a - 1) - -1 = 2 * a - 1 := by ring
    have e3 : 2 * a - -1 = 2 * a + 1 := by ring
    rwa [e1, e2, e3] at h
  · -- `n = 2a + 1` with `a ≥ D`: the even constant, at the pair `(a, a + 1)`.
    have h := lag_odd_cs ν hT τ hRP0 hF hD (a := a) (by omega)
    have e1 : 2 * a + 1 - 1 = 2 * a := by ring
    have e2 : 2 * a + 1 + 1 = 2 * a + 2 := by ring
    rw [e1, e2]
    exact h

/-- **Every lag beyond the overlap is non-increasing**, given both reflection positivities:
`Γ(n + 1) ≤ Γ(n)` for `n ≥ 2D`. DERIVED: `1` the index step; `2` the overlap width. -/
theorem lag_antitone (hT : ∀ (x : ISite) (f : C(IConf G, ℝ)), ν (transObs x f) = ν f)
    (τ : Fin 4) (hRP0 : ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ν)
    (hRP1 : ReflPositiveOn (latticeReflection τ (-1)) (halfSpaceAlg (G := G) τ 0) ν)
    {F : C(IConf G, ℝ)} (hF : ireflObs τ 0 F = F) {D : ℕ} (hD : Deep τ D F) {n : ℤ}
    (hn : 2 * (D : ℤ) ≤ n) : lag ν τ F (n + 1) ≤ lag ν τ F n := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = 2 * (D : ℤ) + j := ⟨(n - 2 * D).toNat, by omega⟩
  let g : ℕ → ℝ := fun i => lag ν τ F (2 * (D : ℤ) + i)
  have hg : ∀ i, 0 ≤ g i := fun i => lag_nonneg_of_both ν hT τ hRP0 hRP1 hF hD (by omega)
  have hM : ∀ i, g i ≤ ‖F‖ ^ 2 := fun i => (le_abs_self _).trans (lag_abs_le ν τ F _)
  have hlc : ∀ i, g (i + 1) ^ 2 ≤ g i * g (i + 2) := by
    intro i
    have h := lag_logConvex ν hT τ hRP0 hRP1 hF hD (n := 2 * (D : ℤ) + ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
    have e1 : 2 * (D : ℤ) + ((i + 1 : ℕ) : ℤ) - 1 = 2 * (D : ℤ) + (i : ℤ) := by push_cast; ring
    have e2 : 2 * (D : ℤ) + ((i + 1 : ℕ) : ℤ) + 1 = 2 * (D : ℤ) + ((i + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h
    exact h
  have h := antitone_of_logConvex g hg hM hlc j
  have e : 2 * (D : ℤ) + ((j + 1 : ℕ) : ℤ) = 2 * (D : ℤ) + j + 1 := by push_cast; ring
  show lag ν τ F (2 * (D : ℤ) + j + 1) ≤ g j
  rw [← e]
  exact h

end Mono

#print axioms lag_odd_cs
#print axioms lag_even_cs
#print axioms lag_even_antitone
#print axioms lag_odd_abs_le
#print axioms lag_logConvex
#print axioms lag_antitone

/-! ## 5. Slice sums -/

section Slice

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  (ν : MassGap.DLRLimit.State (IConf G))

/-- **The slice sum** `∑_{y ∈ Y} T_y F`. DERIVED: no numeral. -/
def sliceSum (Y : Finset ISite) (F : C(IConf G, ℝ)) : C(IConf G, ℝ) := ∑ y ∈ Y, transObs y F

/-- **A transverse slice sum is reflection invariant**: `θ_0(∑_{y ∈ Y} T_y F) = ∑_{y ∈ Y} T_y F` for
`θ_0 F = F` and `y_τ = 0` on `Y`. DERIVED: `0` the constant and the transverse coordinate. -/
theorem sliceSum_refl (τ : Fin 4) {Y : Finset ISite} (hY : ∀ y ∈ Y, y τ = 0) {F : C(IConf G, ℝ)}
    (hF : ireflObs τ 0 F = F) : ireflObs τ 0 (sliceSum Y F) = sliceSum Y F := by
  unfold sliceSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [ireflObs_transObs, ireflSite_zero_of_transverse τ y (hY y hy), hF]

/-- **A transverse slice sum keeps the depth**. DERIVED: `0` the transverse coordinate. -/
theorem sliceSum_deep (τ : Fin 4) {Y : Finset ISite} (hY : ∀ y ∈ Y, y τ = 0) {F : C(IConf G, ℝ)}
    {D : ℕ} (hD : Deep τ D F) : Deep τ D (sliceSum Y F) := by
  intro x hx
  unfold sliceSum
  rw [map_sum]
  refine Submodule.sum_mem _ fun y hy => ?_
  rw [transObs_transObs]
  exact hD _ (by simp only [Pi.add_apply, hY y hy, add_zero]; exact hx)

/-- **The slice-summed lag correlator**: `Γ_{sliceSum}(n) = ∑_{y, y' ∈ Y} ν(T_y F · T_{y' + n e_τ} F)`.
DERIVED: no numeral. -/
theorem sliceSum_lag (τ : Fin 4) (Y : Finset ISite) (F : C(IConf G, ℝ)) (n : ℤ) :
    lag ν τ (sliceSum Y F) n = ∑ y ∈ Y, ∑ y' ∈ Y, ν (transObs y F * transObs (y' + axisVec τ n) F) := by
  unfold lag sliceSum
  rw [map_sum, Finset.sum_mul_sum, ν.map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ν.map_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [transObs_transObs, add_comm (axisVec τ n) y']

end Slice

#print axioms sliceSum_refl
#print axioms sliceSum_deep
#print axioms sliceSum_lag

/-! ## 6. The Wilson tower -/

section Tower

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The bare reading of a reflection-invariant field is reflection invariant**. DERIVED: `0` the
constant; `1` the unit observable. -/
theorem bareRead_refl (S : Sched G) (k : ℕ) (τ : Fin 4) {O : LField G} (hO : O.refl τ = O) :
    ireflObs τ 0 (bareRead S k O) = bareRead S k O := by
  have h1 : ireflObs τ 0 O.1 = O.1 := congrArg Subtype.val hO
  have h2 : ireflObs (G := G) τ 0 (1 : C(IConf G, ℝ)) = 1 := rfl
  unfold bareRead
  rw [map_sub, map_smul, h1, h2]

/-- **The bare reading has a depth**. DERIVED: no numeral. -/
theorem bareRead_deep (S : Sched G) (τ : Fin 4) (O : LField G) :
    ∃ D : ℕ, ∀ k, Deep τ D (bareRead S k O) := by
  obtain ⟨S₀, hS₀⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth τ S₀
  exact ⟨D, fun k => deep_of_local (isLocalOn_sub_const hS₀ _) hD⟩

/-- Members of the symmetrized class are reflection invariant in every direction. DERIVED: no numeral. -/
theorem symPlaq_refl_eq {O : LField G} (hO : O ∈ MassGap.SymPlaqG.SymPlaqClassG G) (τ : Fin 4) :
    O.refl τ = O := by
  obtain ⟨q, rfl⟩ := hO
  exact MassGap.SymPlaqG.symG_refl _ τ

/-- The bare screen entry at sites `x`, `y` is the pair of translates. DERIVED: no numeral. -/
theorem bareScreen_pair (S : Sched G) (ρ : ℝ) (k : ℕ) (O : LField G) (x y : Fin 4 → Fin (scrSide S ρ k)) :
    S.ν k (bareScreen S ρ k O x * bareScreen S ρ k O y)
      = S.ν k (transObs (apSite x) (bareRead S k O) * transObs (apSite y) (bareRead S k O)) := rfl

variable [GaugeSimple G]

/-- The canonical schedule is translation invariant at every step. DERIVED: no numeral. -/
theorem canon_trans (k : ℕ) (x : ISite) (f : C(IConf G, ℝ)) :
    (canonSched G).ν k (transObs x f) = (canonSched G).ν k f :=
  state_transObs (ν := GaugeWilson.periodicStateG G (dyBetaG G k))
    (fun τ F => MassGap.ShiftInvG.periodicStateG_shift G (dyBetaG G k) τ F) x f

/-- The canonical schedule is site reflection positive at the plane `x_τ = 0`. DERIVED: `0` the plane and
the constant `2 · 0`. -/
theorem canon_rp0 (k : ℕ) (τ : Fin 4) :
    ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := G) τ 0) ((canonSched G).ν k) := by
  have h := MassGap.ReflPosG.periodicStateG_reflPositive G (dyBetaG G k) τ 0
  rw [mul_zero] at h
  exact h

/-- **Axis positivity on the screen, canonical schedule**: for `O ∈ SymPlaqClassG G` and a direction `τ`,
one `D` with `0 ≤ ν_k(P_x P_y)` at every step `k` and every pair of screen sites with `y = x + 2a e_τ`,
`a ≥ D`. DERIVED: `2` the even separation. -/
theorem canon_bareScreen_axis {O : LField G} (hO : O ∈ MassGap.SymPlaqG.SymPlaqClassG G) (τ : Fin 4) :
    ∃ D : ℕ, ∀ (ρ : ℝ) (k : ℕ) (x y : Fin 4 → Fin (scrSide (canonSched G) ρ k)) (a : ℤ), (D : ℤ) ≤ a →
      apSite y = apSite x + axisVec τ (2 * a) →
      0 ≤ (canonSched G).ν k (bareScreen (canonSched G) ρ k O x * bareScreen (canonSched G) ρ k O y) := by
  obtain ⟨D, hD⟩ := bareRead_deep (canonSched G) τ O
  refine ⟨D, fun ρ k x y a ha hxy => ?_⟩
  rw [bareScreen_pair, hxy, pair_trans _ (canon_trans k), add_sub_cancel_left]
  exact lag_even_nonneg _ (canon_trans k) τ (canon_rp0 k τ)
    (bareRead_refl _ k τ (symPlaq_refl_eq hO τ)) (hD k) ha

/-- **Slice sums of the bare reading are non-increasing along the even lags, canonical schedule**: for a
finite transverse set `Y`, `Γ_Y(2a + 2) ≤ Γ_Y(2a)` and `0 ≤ Γ_Y(2a)` for `a ≥ D`, at every step.
DERIVED: `2` the even lags; `0` the transverse coordinate. -/
theorem canon_slice_even_antitone {O : LField G} (hO : O ∈ MassGap.SymPlaqG.SymPlaqClassG G) (τ : Fin 4) :
    ∃ D : ℕ, ∀ (k : ℕ) (Y : Finset ISite), (∀ y ∈ Y, y τ = 0) → ∀ a : ℤ, (D : ℤ) ≤ a →
      0 ≤ lag ((canonSched G).ν k) τ (sliceSum Y (bareRead (canonSched G) k O)) (2 * a) ∧
      lag ((canonSched G).ν k) τ (sliceSum Y (bareRead (canonSched G) k O)) (2 * a + 2)
        ≤ lag ((canonSched G).ν k) τ (sliceSum Y (bareRead (canonSched G) k O)) (2 * a) := by
  obtain ⟨D, hD⟩ := bareRead_deep (canonSched G) τ O
  refine ⟨D, fun k Y hY a ha => ⟨?_, ?_⟩⟩
  · exact lag_even_nonneg _ (canon_trans k) τ (canon_rp0 k τ)
      (sliceSum_refl τ hY (bareRead_refl _ k τ (symPlaq_refl_eq hO τ))) (sliceSum_deep τ hY (hD k)) ha
  · exact lag_even_antitone _ (canon_trans k) τ (canon_rp0 k τ)
      (sliceSum_refl τ hY (bareRead_refl _ k τ (symPlaq_refl_eq hO τ))) (sliceSum_deep τ hY (hD k)) ha

end Tower

#print axioms bareRead_refl
#print axioms bareRead_deep
#print axioms symPlaq_refl_eq
#print axioms bareScreen_pair
#print axioms canon_trans
#print axioms canon_rp0
#print axioms canon_bareScreen_axis
#print axioms canon_slice_even_antitone

section TowerSU

variable {N : ℕ} [NeZero N]

/-- The `SU(N)` schedule is translation invariant at every step. DERIVED: no numeral. -/
theorem su_trans (k : ℕ) (x : ISite) (f : C(IConf (MassGap.SUN.SU N), ℝ)) :
    (schedSU N).ν k (transObs x f) = (schedSU N).ν k f :=
  state_transObs (ν := (schedSU N).ν k)
    (fun τ F => MassGap.PeriodicState.periodicState_shift (NeZero.ne N) _ τ F) x f

/-- The `SU(N)` schedule is site reflection positive at the plane `x_τ = 0`. DERIVED: `0` the plane and the
constant `2 · 0`. -/
theorem su_rp0 (k : ℕ) (τ : Fin 4) :
    ReflPositiveOn (latticeReflection τ 0) (halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) ((schedSU N).ν k) := by
  have h := MassGap.PeriodicState.periodicState_reflPositive (NeZero.ne N)
    (MassGap.ContinuumSchwinger.dyBeta (MassGap.ContinuumSchwinger.one_le_of_ne_zero (NeZero.ne N)) k) τ 0
  rw [mul_zero] at h
  exact h

/-- The `SU(N)` schedule is link reflection positive at the plane between `x_τ = −1` and `x_τ = 0`
(`dyBeta ≥ 1 ≥ 0`). DERIVED: `−1` the constant `2 · 0 − 1`; `0` the sign of the coupling. -/
theorem su_rp1 (k : ℕ) (τ : Fin 4) :
    ReflPositiveOn (latticeReflection τ (-1)) (halfSpaceAlg (G := MassGap.SUN.SU N) τ 0) ((schedSU N).ν k) := by
  have h := MassGap.PeriodicState.periodicState_reflPositive_odd (NeZero.ne N)
    (zero_le_one.trans (MassGap.ContinuumSchwinger.one_le_dyBeta
      (MassGap.ContinuumSchwinger.one_le_of_ne_zero (NeZero.ne N)) k)) τ 0
  rw [mul_zero, zero_sub] at h
  exact h

/-- **Axis positivity on the screen at every separation beyond the overlap, `SU(N)`**: for
`O ∈ SymPlaqClassG (SU N)` and a direction `τ`, one `D` with `0 ≤ ν_k(P_x P_y)` at every step and every pair of
screen sites with `y = x + n e_τ`, `n ≥ 2D`, of either parity. DERIVED: `2` the overlap width. -/
theorem su_bareScreen_axis {O : LField (MassGap.SUN.SU N)}
    (hO : O ∈ MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) (τ : Fin 4) :
    ∃ D : ℕ, ∀ (ρ : ℝ) (k : ℕ) (x y : Fin 4 → Fin (scrSide (schedSU N) ρ k)) (n : ℤ), 2 * (D : ℤ) ≤ n →
      apSite y = apSite x + axisVec τ n →
      0 ≤ (schedSU N).ν k (bareScreen (schedSU N) ρ k O x * bareScreen (schedSU N) ρ k O y) := by
  obtain ⟨D, hD⟩ := bareRead_deep (schedSU N) τ O
  refine ⟨D, fun ρ k x y n hn hxy => ?_⟩
  rw [bareScreen_pair, hxy, pair_trans _ (su_trans k), add_sub_cancel_left]
  exact lag_nonneg_of_both _ (su_trans k) τ (su_rp0 k τ) (su_rp1 k τ)
    (bareRead_refl _ k τ (symPlaq_refl_eq hO τ)) (hD k) hn

/-- **Slice sums of the bare reading are non-negative, log-convex and non-increasing beyond the overlap,
`SU(N)`**: for a finite transverse set `Y` and every lag `n ≥ 2D`, `0 ≤ Γ_Y(n)`, `Γ_Y(n + 1) ≤ Γ_Y(n)` and
`Γ_Y(n + 1)² ≤ Γ_Y(n) Γ_Y(n + 2)`, at every step. DERIVED: `1`, `2` the neighbouring lags; `0` the transverse
coordinate. -/
theorem su_slice_antitone {O : LField (MassGap.SUN.SU N)}
    (hO : O ∈ MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) (τ : Fin 4) :
    ∃ D : ℕ, ∀ (k : ℕ) (Y : Finset ISite), (∀ y ∈ Y, y τ = 0) → ∀ n : ℤ, 2 * (D : ℤ) ≤ n →
      0 ≤ lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) n ∧
      lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) (n + 1)
        ≤ lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) n ∧
      lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) (n + 1) ^ 2
        ≤ lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) n
          * lag ((schedSU N).ν k) τ (sliceSum Y (bareRead (schedSU N) k O)) (n + 2) := by
  obtain ⟨D, hD⟩ := bareRead_deep (schedSU N) τ O
  refine ⟨D, fun k Y hY n hn => ?_⟩
  have hF := sliceSum_refl τ hY (bareRead_refl (schedSU N) k τ (symPlaq_refl_eq hO τ))
  have hDY := sliceSum_deep τ hY (hD k)
  refine ⟨lag_nonneg_of_both _ (su_trans k) τ (su_rp0 k τ) (su_rp1 k τ) hF hDY hn,
    lag_antitone _ (su_trans k) τ (su_rp0 k τ) (su_rp1 k τ) hF hDY hn, ?_⟩
  have h := lag_logConvex _ (su_trans k) τ (su_rp0 k τ) (su_rp1 k τ) hF hDY (n := n + 1) (by omega)
  have e1 : n + 1 - 1 = n := by ring
  have e2 : n + 1 + 1 = n + 2 := by ring
  rwa [e1, e2] at h

end TowerSU

#print axioms su_trans
#print axioms su_rp0
#print axioms su_rp1
#print axioms su_bareScreen_axis
#print axioms su_slice_antitone

end MassGap.PlaqPositive

end
