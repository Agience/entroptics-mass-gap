import Mathlib
import MassGap.ActionSplit
import MassGap.ReflectPositive
import MassGap.Transfer

/-!
# MassGap.LogConvex — log-convexity of the lag correlation, with constant one

    ρ(e₁ + e₂)²  ≤  ρ(2e₁) · ρ(2e₂)

for the connected plaquette correlation `ρ = corrClay`, at every even lattice extent and every real
coupling. The `2` is the exponent of a square, and no constant multiplies the right-hand side.

## Where it comes from

Reflection positivity is a statement about a bilinear form. `ActionSplit.pairing_nonneg_of_local` is
that general statement — nonnegativity of `∫ W·O·(O∘Θ)` for any bounded measurable `O` reading one
half-space plus the plane — so the diagonal holds on a whole vector space of observables, and
Cauchy–Schwarz on that space is the off-diagonal.
`Transfer.ReflForm.cauchy_schwarz` is the abstract half of that and needs only symmetry, bilinearity
and diagonal nonnegativity; `localObs` is the space and `wilsonReflForm` the instance.

## The geometry, which is what makes the constant one

One reflection plane at site `a` along the lag axis, reflection constant `a + a`. A plaquette based
at level `s` below the plane is carried by the reflection to level `−s`, so

* `⟨F_s , F_s ∘ Θ⟩` is the correlation at lag `s + s`,
* `⟨F_t , F_t ∘ Θ⟩` is the correlation at lag `t + t`,
* `⟨F_s , F_t ∘ Θ⟩` is the correlation at lag `s + t`,

all three from the same reflection, and all three carrying the same partition function, so no
constant enters. The identification of a pairing with a correlation based at the origin is
`EW_plaqE_pair_shift`, which is translation invariance obtained from the reflection itself —
`⟨φ_P φ_Q⟩ = ⟨φ_0 φ_{P−Q}⟩`, one application of `Reflect.expect_reflect_invariant` at constant `P`.

## Scope

The extent must be even (`n = 2m`) and both levels strictly below the plane (`s.val < m`,
`t.val < m`). There is no hypothesis `0 ≤ β`: the argument runs on `ActionSplit`'s even-lag weld,
which is a conditional square against a positive Boltzmann weight and does not read the sign of the
coupling. The odd-lag link reflection is not used either, though the lag `s + t` on the left may be
odd — that lag arises as an off-diagonal pairing under an even reflection, not as a diagonal one, so
no axis link is inverted and no dagger has to be reconciled.

The cross lag `s + t` and the diagonal lags `s + s`, `t + t` are all below `n` when `s.val, t.val < m`,
so the `Fin n` sums here are the arithmetic sums and nothing wraps.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.LogConvex`.
-/

namespace MassGap.LogConvex

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity MassGap.WilsonLattice
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonAction
open MassGap.ActionSplit MassGap.ReflectPositive MassGap.WilsonBridge

/-! ## Part 1 — the three-block factorisation with two observables

`ActionSplit.integrand_eq_paired` collapses the two half-space observables to one at its last line.
The mirror identity `actPlus ∘ Θ = actMinus` is a statement about the action, not about the
observable, so the same factorisation holds with the two observables kept apart.
-/

section Factor

variable {d n N : ℕ} [NeZero n]

/-- **The three-block factorisation, with two observables.** The centred density of the plaquette `p`
read on `U`, times the centred density of `q` read on the reflected configuration, times the Boltzmann
weight, equals the plane weight `wPlane` times `obsPlus` at `p` times `obsPlus` at `q` on the
reflected configuration. This is `ActionSplit.integrand_eq_paired` with the two plaquettes kept
apart: the shared plane weight sits outside the product, and only the left and right factors differ.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m` and the `0` in
`0 < m`. The first excludes the empty gauge group; the second says the extent is even, which is what
lets a reflection plane cut it into two halves, and the third says a half is nonempty. All three are
`ActionSplit.action_eq_split`'s own hypotheses, carried. -/
theorem integrand_eq_paired_pair (τ : Fin d) (a : Fin n) (m : ℕ) (hN : N ≠ 0)
    (hm : n = 2 * m) (hm0 : 0 < m) (p q : Plaq d n) (aC β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    (wilsonDensity (wilsonHol (bd (d := d) (n := n)) p U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) - aC)
        * (sysWilson N d n).boltz β U
      = wPlane τ a m β U * obsPlus τ a m p aC β U
          * obsPlus τ a m q aC β (reflConf τ (a + a) U) := by
  have hmir : actPlus τ a m (reflConf τ (a + a) U) = actMinus τ a m U :=
    (sum_plqMinus_eq_plus_refl τ a m hm hm0 U).symm
  show _ * _ * Real.exp (-β * (sysWilson N d n).action U) = _
  rw [action_eq_split τ a m hN U]
  unfold wPlane obsPlus
  rw [hmir]
  rw [show -β * (actPlus τ a m U + actMinus τ a m U + actZero τ a m U)
      = (-β * actZero τ a m U) + ((-β * actPlus τ a m U) + (-β * actMinus τ a m U)) by ring,
    Real.exp_add, Real.exp_add]
  ring

end Factor

/-! ## Part 2 — the vector space the form lives on

`pairing_nonneg_of_local` is quantified over observables, so its hypotheses cut out a set of
observables, and that set is closed under addition and scaling: measurability, a bound and reading a
fixed pair of blocks all survive both. So it is a submodule of the functions on configurations, which
is the carrier type a `Transfer.ReflForm` takes.
-/

section Space

variable {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω]

/-- **Observables reading `S ∪ R`**: the submodule of real functions on `ι → Ω` that are measurable,
bounded by some constant, and determined by the configuration on `S ∪ R` alone. These are the three
hypotheses `ActionSplit.pairing_nonneg_of_local` places on its observable, collected so that they can
be carried as membership in a module rather than as three side conditions per call.

DERIVED: the carrier carries no numeral — the bound `C` is existentially quantified. The `0` in
`zero_mem'` is the bound exhibited for the zero function, `|0| ≤ 0`, forced by the element being
tested; `add_mem'` and `smul_mem'` carry the bound forward as `CF + CG` and `|r| · CF`, both read off
the operation rather than chosen. -/
def localObs (S R : Finset ι) : Submodule ℝ ((ι → Ω) → ℝ) where
  carrier := {F | Measurable F ∧ (∃ C : ℝ, ∀ U, |F U| ≤ C)
      ∧ ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → F U = F V}
  zero_mem' := by
    refine ⟨measurable_const, ⟨0, fun U => by simp⟩, fun _ _ _ _ => rfl⟩
  add_mem' := by
    rintro F G ⟨hFm, ⟨CF, hFb⟩, hFl⟩ ⟨hGm, ⟨CG, hGb⟩, hGl⟩
    refine ⟨hFm.add hGm, ⟨CF + CG, fun U => ?_⟩, fun U V hS hR => ?_⟩
    · show |F U + G U| ≤ CF + CG
      have hf := abs_le.mp (hFb U)
      have hg := abs_le.mp (hGb U)
      rw [abs_le]
      exact ⟨by linarith [hf.1, hg.1], by linarith [hf.2, hg.2]⟩
    · show F U + G U = F V + G V
      rw [hFl U V hS hR, hGl U V hS hR]
  smul_mem' := by
    rintro r F ⟨hFm, ⟨CF, hFb⟩, hFl⟩
    refine ⟨hFm.const_mul r, ⟨|r| * CF, fun U => ?_⟩, fun U V hS hR => ?_⟩
    · show |r * F U| ≤ |r| * CF
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hFb U) (abs_nonneg r)
    · show r * F U = r * F V
      rw [hFl U V hS hR]

omit [Fintype ι] in
theorem mem_localObs {S R : Finset ι} {F : (ι → Ω) → ℝ} :
    F ∈ localObs S R ↔ (Measurable F ∧ (∃ C : ℝ, ∀ U, |F U| ≤ C)
      ∧ ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → F U = F V) := Iff.rfl

omit [Fintype ι] in
theorem localObs_measurable {S R : Finset ι} {F : (ι → Ω) → ℝ} (hF : F ∈ localObs S R) :
    Measurable F := hF.1

omit [Fintype ι] in
theorem localObs_bounded {S R : Finset ι} {F : (ι → Ω) → ℝ} (hF : F ∈ localObs S R) :
    ∃ C : ℝ, ∀ U, |F U| ≤ C := hF.2.1

omit [Fintype ι] in
theorem localObs_local {S R : Finset ι} {F : (ι → Ω) → ℝ} (hF : F ∈ localObs S R) :
    ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → F U = F V := hF.2.2

/-- **`localObs` is closed under pointwise multiplication.** If `F` and `G` are both measurable,
bounded and determined by the configuration on `S ∪ R`, so is `F * G`. `localObs` is a `Submodule`,
so it carries additive and scalar closure only; this supplies the product, which is what a
block-by-block estimate needs.

Locality here is stated at one fixed pair `(S, R)`, so two observables local on that pair have a
product local on that same pair and no union of supports enters. Compare
`HalfSpaceAlgebra.halfSpaceAlg_mul_mem`, the infinite-lattice statement.

The bound exhibited in the proof is `|CF| · |CG|` rather than `CF · CG`, because nothing here makes
the configuration space nonempty and so neither `C` can be shown nonnegative; taking absolute values
needs no inhabitant.

DERIVED: no numeral. -/
theorem localObs_mul_mem {S R : Finset ι} {F G : (ι → Ω) → ℝ}
    (hF : F ∈ localObs S R) (hG : G ∈ localObs S R) : F * G ∈ localObs S R := by
  obtain ⟨hFm, ⟨CF, hFb⟩, hFl⟩ := hF
  obtain ⟨hGm, ⟨CG, hGb⟩, hGl⟩ := hG
  refine ⟨hFm.mul hGm, ⟨|CF| * |CG|, fun U => ?_⟩, fun U V hS hR => ?_⟩
  · show |F U * G U| ≤ |CF| * |CG|
    rw [abs_mul]
    exact mul_le_mul (le_trans (hFb U) (le_abs_self CF)) (le_trans (hGb U) (le_abs_self CG))
      (abs_nonneg _) (abs_nonneg _)
  · show F U * G U = F V * G V
    rw [hFl U V hS hR, hGl U V hS hR]


end Space

/-! ## Part 3 — the Wilson reflection pairing, as a `ReflForm` -/

section Form

variable {d n N : ℕ} [NeZero n]

/-- **The reflection pairing of two observables.** The integral of the plane weight `wPlane` times
`F` times `G` composed with the reflection at constant `a + a`, against the product Haar measure on
configurations. This is `ActionSplit.wilson_pairing_nonneg_even`'s integral with the two slots kept
apart, and `Transfer.reflForm`'s shape with the Gibbs weight split at the plane. No integrability or
locality hypothesis is imposed here; those are hypotheses of the theorems below.

DERIVED: no numeral. -/
noncomputable def pairing (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) : ℝ :=
  ∫ U, wPlane τ a m β U * F U * G (reflConf τ (a + a) U)
    ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))

/-- The plane weight is measurable, as a function of the configuration.

DERIVED: no numeral. -/
theorem measurable_wPlane (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ) :
    Measurable (wPlane (N := N) τ a m β) := by
  unfold wPlane actZero
  exact Real.measurable_exp.comp ((measurable_actSum _).const_mul _)

/-- The plane weight is nonnegative at every configuration, because it is an exponential.

DERIVED: the `0` is the floor `Real.exp` cannot go below; it is not a bound anyone chose. -/
theorem wPlane_nonneg (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) : 0 ≤ wPlane τ a m β U := le_of_lt (Real.exp_pos _)

/-- The plane weight is bounded in absolute value by `exp (|β| · 2 · |plqZero|)`, uniformly in the
configuration — the same exponential bound `ActionSplit.abs_exp_actSum_le` supplies. Requires
`N ≠ 0`.

DERIVED: the `0` in `N ≠ 0` excludes the empty gauge group. The `2` is the range of the Wilson
plaquette density on `SU(N)`, not a chosen bound, and the cardinality is the plane block's own
plaquette count. -/
theorem wPlane_abs_le (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    |wPlane τ a m β U| ≤ Real.exp (|β| * (2 * ((plqZero (d := d) (n := n) τ a m).card : ℝ))) :=
  abs_exp_actSum_le hN β _ U

/-- The reflection at constant `c` along axis `τ` is measurable, as a map of configurations. It comes
from `reflConf_measurePreserving`, which gives measure preservation and measurability together.

DERIVED: no numeral. -/
theorem measurable_reflConf (τ : Fin d) (c : Fin n) :
    Measurable (reflConf (G := MassGap.SUN.SU N) τ c) :=
  (reflConf_measurePreserving τ c).measurable

/-- The integrand of the pairing is integrable when both observables lie in
`localObs (blkS τ a m) (blkR τ a m)`: it is then bounded and measurable, against a probability
measure. Requires `N ≠ 0`, which is what `wPlane_abs_le` needs for the weight's bound.

DERIVED: the only numeral in the statement is the `0` in `N ≠ 0`, the excluded gauge rank. -/
theorem integrable_pairing (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    {F G : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObs (blkS τ a m) (blkR τ a m)) :
    Integrable (fun U => wPlane τ a m β U * F U * G (reflConf τ (a + a) U))
      (cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  obtain ⟨CF, hCF⟩ := localObs_bounded hF
  obtain ⟨CG, hCG⟩ := localObs_bounded hG
  set K : ℝ := Real.exp (|β| * (2 * ((plqZero (d := d) (n := n) τ a m).card : ℝ))) with hK
  have hKnn : 0 ≤ K := le_of_lt (Real.exp_pos _)
  have hCFnn : 0 ≤ CF := le_trans (abs_nonneg _) (hCF (fun _ => 1))
  refine integrable_of_bounded _
    (((measurable_wPlane τ a m β).mul (localObs_measurable hF)).mul
      ((localObs_measurable hG).comp (measurable_reflConf τ (a + a)))) (C := K * CF * CG) ?_
  intro U
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (wPlane_abs_le hN τ a m β U) (hCF U) (abs_nonneg _) hKnn)
    (hCG _) (abs_nonneg _) (mul_nonneg hKnn hCFnn)

/-- **The pairing is additive in its first slot**, for observables of
`localObs (blkS τ a m) (blkR τ a m)`. All three observables are required to lie in the module,
because the proof splits one integral into two and needs each to be integrable. Requires `N ≠ 0`.

DERIVED: the only numeral in the statement is the `0` in `N ≠ 0`, the excluded gauge rank. -/
theorem pairing_add_left (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ)
    {F₁ F₂ G : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF₁ : F₁ ∈ localObs (blkS τ a m) (blkR τ a m))
    (hF₂ : F₂ ∈ localObs (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObs (blkS τ a m) (blkR τ a m)) :
    pairing τ a m β (F₁ + F₂) G = pairing τ a m β F₁ G + pairing τ a m β F₂ G := by
  have i1 := integrable_pairing hN τ a m β hF₁ hG
  have i2 := integrable_pairing hN τ a m β hF₂ hG
  show (∫ U, wPlane τ a m β U * (F₁ U + F₂ U) * G (reflConf τ (a + a) U)
      ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
    = (∫ U, wPlane τ a m β U * F₁ U * G (reflConf τ (a + a) U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      + ∫ U, wPlane τ a m β U * F₂ U * G (reflConf τ (a + a) U)
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))
  rw [← integral_add i1 i2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)

/-- **The pairing is homogeneous in its first slot**: scaling `F` by a real `r` scales the pairing by
`r`. Unlike `pairing_add_left`, this needs no membership and no integrability — the scalar comes out
of the integral by `integral_const_mul`, which holds whether or not the integrand is integrable.

DERIVED: no numeral. -/
theorem pairing_smul_left (τ : Fin d) (a : Fin n) (m : ℕ) (β : ℝ) (r : ℝ)
    (F G : (Link d n → MassGap.SUN.SU N) → ℝ) :
    pairing τ a m β (r • F) G = r * pairing τ a m β F G := by
  show (∫ U, wPlane τ a m β U * (r * F U) * G (reflConf τ (a + a) U)
      ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))) = _
  rw [show (r * pairing τ a m β F G)
      = ∫ U, r * (wPlane τ a m β U * F U * G (reflConf τ (a + a) U))
        ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) from (integral_const_mul _ _).symm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)

/-- **The plane weight is unchanged by the reflection**, at even extent `n = 2 * m`. It reads only
the plane block `blkR`; the reflection fixes every link of that block (`blkR_fixed`), and no link of
it runs along the axis (`blkR_axis_free`), so the dagger branch never fires. This is what makes the
pairing symmetric rather than merely bilinear.

DERIVED: the `2` in `n = 2 * m` says the extent is even, which is what `blkR_fixed` requires of the
plane block. -/
theorem wPlane_reflConf (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    wPlane τ a m β (reflConf τ (a + a) U) = wPlane τ a m β U := by
  refine wPlane_local τ a m β _ _ (fun l hl => ?_)
  show (if l.1 = τ then (U (reflLink τ (a + a) l))⁻¹ else U (reflLink τ (a + a) l)) = U l
  rw [if_neg (blkR_axis_free τ a m hl), blkR_fixed τ a m hm hl]

/-- **The pairing is symmetric** in its two observables, at even extent `n = 2 * m`, for `F` and `G`
in `localObs (blkS τ a m) (blkR τ a m)`. The reflection preserves the product Haar measure and is an
involution, and the plane weight does not move under it (`wPlane_reflConf`), so the change of
variables `U ↦ ΘU` carries the reflection from one slot to the other.

DERIVED: the `2` in `n = 2 * m` is the even extent `wPlane_reflConf` requires. -/
theorem pairing_symm (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (β : ℝ)
    {F G : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (blkS τ a m) (blkR τ a m))
    (hG : G ∈ localObs (blkS τ a m) (blkR τ a m)) :
    pairing τ a m β F G = pairing τ a m β G F := by
  have hHm : Measurable (fun V : Link d n → MassGap.SUN.SU N =>
      wPlane τ a m β V * G V * F (reflConf τ (a + a) V)) :=
    ((measurable_wPlane τ a m β).mul (localObs_measurable hG)).mul
      ((localObs_measurable hF).comp (measurable_reflConf τ (a + a)))
  show (∫ U, wPlane τ a m β U * F U * G (reflConf τ (a + a) U)
      ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
    = ∫ U, wPlane τ a m β U * G U * F (reflConf τ (a + a) U)
      ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))
  rw [← integral_comp_of_mp (reflConf_measurePreserving (N := N) τ (a + a)) hHm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show wPlane τ a m β U * F U * G (reflConf τ (a + a) U)
    = wPlane τ a m β (reflConf τ (a + a) U) * G (reflConf τ (a + a) U)
      * F (reflConf τ (a + a) (reflConf τ (a + a) U))
  rw [wPlane_reflConf τ a m hm β U, reflConf_involutive τ (a + a) U]
  ring

/-- **The pairing is nonnegative on the diagonal** — reflection positivity, for every observable of
the module rather than for one plaquette. Requires `N ≠ 0`, even extent `n = 2 * m` and `0 < m`.
This is `ActionSplit.pairing_nonneg_of_local` read at the Wilson lattice's own blocks `blkS`, `blkT`,
`blkR`; `reflConf` is the twist by `ActionSplit.reflConf_eq_twist`.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m`, the `0` in `0 < m`
and the `0` the pairing is bounded below by. The first excludes the empty gauge group, the next two
are the reflection geometry's even extent and nonempty half, and the last is the sign the
conclusion asserts. -/
theorem pairing_nonneg (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → MassGap.SUN.SU N) → ℝ}
    (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    0 ≤ pairing τ a m β F F := by
  obtain ⟨CF, hCF⟩ := localObs_bounded hF
  set K : ℝ := Real.exp (|β| * (2 * ((plqZero (d := d) (n := n) τ a m).card : ℝ))) with hK
  have hKnn : 0 ≤ K := le_of_lt (Real.exp_pos _)
  have hCFnn : 0 ≤ CF := le_trans (abs_nonneg _) (hCF (fun _ => 1))
  refine pairing_nonneg_of_local (probHaar (MassGap.SUN.SU N))
    (blkS τ a m) (blkT τ a m) (blkR τ a m)
    (blkS_disjoint_blkT τ a m) (blkS_disjoint_blkR τ a m) (blkT_disjoint_blkR τ a m)
    (reflLinkPerm τ (a + a)) (axisDagger (N := N) τ)
    (fun l => axisDagger_measurePreserving τ l)
    (fun l hl => blkR_fixed τ a m hm hl)
    (fun l hl u => by simp [axisDagger, blkR_axis_free τ a m hl])
    (fun l hl => blkS_maps_blkT τ a m hm hm0 hl)
    (fun _ => 1)
    F (localObs_measurable hF) (localObs_local hF)
    (wPlane τ a m β) (measurable_wPlane τ a m β) (wPlane_nonneg τ a m β)
    (fun U V hR => wPlane_local τ a m β U V hR)
    (K * CF * CF) (fun U => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (wPlane_abs_le hN τ a m β U) (hCF U) (abs_nonneg _) hKnn)
    (hCF _) (abs_nonneg _) (mul_nonneg hKnn hCFnn)

/-- **The Wilson lattice's reflection form**, on the half-space observables
`localObs (blkS τ a m) (blkR τ a m)` of an even-extent lattice. Every field of
`Transfer.ReflForm` is supplied: `form_symm` from `pairing_symm`, `form_add_left` and
`form_smul_left` from the integral, and `form_nonneg` — which `Transfer.ReflForm` carries as a field
rather than a hypothesis — from `pairing_nonneg`. Requires `N ≠ 0`, `n = 2 * m` and `0 < m`.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m` and the `0` in
`0 < m`: the excluded gauge rank, and the even extent and nonempty half the reflection geometry
needs. `τ`, `a`, `m` and `β` are the caller's. -/
noncomputable def wilsonReflForm (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    MassGap.Transfer.ReflForm
      ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ a m) (blkR τ a m)) where
  form F G := pairing τ a m β F.1 G.1
  form_symm F G := pairing_symm τ a m hm β F.2 G.2
  form_add_left F₁ F₂ G := by
    show pairing τ a m β (F₁.1 + F₂.1) G.1
      = pairing τ a m β F₁.1 G.1 + pairing τ a m β F₂.1 G.1
    exact pairing_add_left hN τ a m β F₁.2 F₂.2 G.2
  form_smul_left r F G := by
    show pairing τ a m β (r • F.1) G.1 = r * pairing τ a m β F.1 G.1
    exact pairing_smul_left τ a m β r _ _
  form_nonneg F := pairing_nonneg hN τ a m hm hm0 β F.2

end Form

/-! ## Part 4 — the plaquette observables live in the module -/

section Members

variable {d n N : ℕ} [NeZero n]

/-- **The half-space plaquette observable lies in the module.** `obsPlus τ a m q aC β` — the centred
Wilson density of the plaquette `q` times the half-space Boltzmann factor — is measurable, bounded
and determined by `blkS ∪ blkR`, so it is an element of `localObs (blkS τ a m) (blkR τ a m)`. The
three facts are `ActionSplit`'s: measurability of the density and of the half action, the range of
the Wilson density, and `obsPlus_local`. The plaquette must not have both its directions equal to the
reflection axis (`hqdeg`), and its level must be strictly below the plane (`hqlv`).

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m` and the `0` in
`0 < m` — the excluded gauge rank and the reflection geometry's even extent and nonempty half. The
bound exhibited in the proof is `(2 + |aC|) · exp (|β| · 2 · |plqPlus|)`, where `2` is the range of
the Wilson plaquette density and the cardinality is the half-space's own plaquette count. -/
theorem obsPlus_mem (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    (q : Plaq d n) (hqdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hqlv : lv a (q.2 τ) < m) (aC β : ℝ) :
    obsPlus (N := N) τ a m q aC β ∈ localObs (blkS τ a m) (blkR τ a m) := by
  refine ⟨?_, ⟨(2 + |aC|)
      * Real.exp (|β| * (2 * ((plqPlus (d := d) (n := n) τ a m).card : ℝ))), ?_⟩,
    fun U V hS hR => obsPlus_local τ a m hm hm0 q hqdeg hqlv aC β U V hS hR⟩
  · unfold obsPlus actPlus
    exact ((measurable_density_hol q).sub measurable_const).mul
      (Real.measurable_exp.comp ((measurable_actSum _).const_mul _))
  · intro U
    unfold obsPlus
    rw [abs_mul]
    refine mul_le_mul ?_ (abs_exp_actSum_le hN β _ U) (abs_nonneg _) (by
      have := abs_nonneg aC; linarith)
    have h1 : 0 ≤ wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) :=
      wilsonDensity_nonneg hN _
    have h2 : wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) ≤ 2 :=
      wilsonDensity_le_two hN _
    have h3 : -|aC| ≤ aC := neg_abs_le _
    have h4 : aC ≤ |aC| := le_abs_self _
    rw [abs_le]
    constructor <;> linarith

/-- **The pairing of two half-space plaquette observables is the unnormalised centred correlation.**
`pairing` at `obsPlus p` and `obsPlus q` equals `(sysWilson N d n).corrNum` of the product of the two
centred plaquette energies, the second read on the reflected configuration. This is
`integrand_eq_paired_pair` integrated. Requires `N ≠ 0`, `n = 2 * m` and `0 < m`.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m` and the `0` in
`0 < m`, all carried from `integrand_eq_paired_pair`. `corrNum` is the unnormalised correlation, so
no partition function appears. -/
theorem pairing_obsPlus (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m)
    (p q : Plaq d n) (aC β : ℝ) :
    pairing τ a m β (obsPlus (N := N) τ a m p aC β) (obsPlus τ a m q aC β)
      = (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β
          (fun U => (plaqE N p U - aC) * (plaqE N q (reflConf τ (a + a) U) - aC)) := by
  symm
  show (∫ U, ((wilsonDensity (wilsonHol (bd (d := d) (n := n)) p U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) - aC))
      * (sysWilson N d n).boltz β U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N)))) = _
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun U => integrand_eq_paired_pair τ a m hN hm hm0 p q aC β U))

/-- **Cauchy–Schwarz on the Gibbs state**, for two plaquette observables below one plane, at one
reflection: the square of the mixed centred reflected expectation is at most the product of the two
diagonal ones. Requires `N ≠ 0`, `n = 2 * m` and `0 < m`, and both plaquettes non-degenerate along
the axis and strictly below the plane. The partition function cancels because the same `Z` appears in
all three places, so the inequality carries no constant.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m`, the `0` in `0 < m`
and the exponent `2` of the square Cauchy–Schwarz produces. None is a level. -/
theorem EW_refl_cauchy_schwarz (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) (p q : Plaq d n)
    (hpdeg : ¬ (p.1.1 = τ ∧ p.1.2 = τ)) (hplv : lv a (p.2 τ) < m)
    (hqdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hqlv : lv a (q.2 τ) < m) (aC β : ℝ) :
    (EW N β (fun U => (plaqE N p U - aC) * (plaqE N q (reflConf τ (a + a) U) - aC))) ^ 2
      ≤ (EW N β (fun U => (plaqE N p U - aC) * (plaqE N p (reflConf τ (a + a) U) - aC)))
        * (EW N β (fun U => (plaqE N q U - aC) * (plaqE N q (reflConf τ (a + a) U) - aC))) := by
  have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
    wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  set Z := (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β with hZdef
  have hnum : ∀ O : (Link d n → MassGap.SUN.SU N) → ℝ,
      (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O = EW N β O * Z := by
    intro O
    show _ = ((sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O / Z) * Z
    field_simp
  set P := wilsonReflForm hN τ a m hm hm0 β with hP
  have hpm := obsPlus_mem hN τ a m hm hm0 p hpdeg hplv aC β
  have hqm := obsPlus_mem hN τ a m hm hm0 q hqdeg hqlv aC β
  have h := P.cauchy_schwarz ⟨obsPlus τ a m p aC β, hpm⟩ ⟨obsPlus τ a m q aC β, hqm⟩
  show _ ≤ _
  have hpq : P.form ⟨obsPlus τ a m p aC β, hpm⟩ ⟨obsPlus τ a m q aC β, hqm⟩
      = EW N β (fun U => (plaqE N p U - aC) * (plaqE N q (reflConf τ (a + a) U) - aC)) * Z := by
    show pairing τ a m β (obsPlus τ a m p aC β) (obsPlus τ a m q aC β) = _
    rw [pairing_obsPlus hN τ a m hm hm0 p q aC β]
    exact hnum _
  have hpp : P.form ⟨obsPlus τ a m p aC β, hpm⟩ ⟨obsPlus τ a m p aC β, hpm⟩
      = EW N β (fun U => (plaqE N p U - aC) * (plaqE N p (reflConf τ (a + a) U) - aC)) * Z := by
    show pairing τ a m β (obsPlus τ a m p aC β) (obsPlus τ a m p aC β) = _
    rw [pairing_obsPlus hN τ a m hm hm0 p p aC β]
    exact hnum _
  have hqq : P.form ⟨obsPlus τ a m q aC β, hqm⟩ ⟨obsPlus τ a m q aC β, hqm⟩
      = EW N β (fun U => (plaqE N q U - aC) * (plaqE N q (reflConf τ (a + a) U) - aC)) * Z := by
    show pairing τ a m β (obsPlus τ a m q aC β) (obsPlus τ a m q aC β) = _
    rw [pairing_obsPlus hN τ a m hm hm0 q q aC β]
    exact hnum _
  rw [hpq, hpp, hqq] at h
  refine le_of_mul_le_mul_right ?_ (pow_pos hZ 2)
  nlinarith [h]

end Members

/-! ## Part 5 — the pairings ARE the correlation, at three lags

The pairing of the plaquette at level `P` with the reflected plaquette at level `Q` is the two-point
function at separation `P − (a+a) + Q`. Turning that into `corrHyper`, which is based at the origin,
needs translation invariance; a translation is a product of two reflections, so one application of
`Reflect.expect_reflect_invariant` moves both plaquettes at once.
-/

section Identify

variable {d n Nc : ℕ} [NeZero n]

/-- The site at lag zero along axis `τ` is the origin of `Site d n`.

DERIVED: the `0` on the left is the lag and the `0` on the right is the coordinate value at every
axis; both are `Fin n`'s zero, and the identity is what makes the two spellings of the origin
interchangeable. -/
theorem siteAtHyper_zero (τ : Fin d) :
    siteAtHyper (d := d) (n := n) τ 0 = (fun _ => 0 : Site d n) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [siteAtHyper]
  · simp [siteAtHyper, Function.update_of_ne h]

/-- The `τ`-coordinate of the site at lag `P` along `τ` is `P`. A simp lemma.

DERIVED: no numeral. -/
@[simp] theorem siteAtHyper_axis (τ : Fin d) (P : Fin n) :
    siteAtHyper (d := d) (n := n) τ P τ = P := by
  simp [siteAtHyper]

/-- **The reflection carries the plaquette at lag `P` to the plaquette at lag `c − P`.** Both
directions `μ`, `ν` spanning the plaquette plane must differ from the reflection axis `τ`; the plane
is then untouched and only the base site moves, by `reflSite`. This is
`ReflectPositive.reflPlaq_origin` for a base that need not be the origin.

DERIVED: no numeral. -/
theorem reflPlaq_siteAtHyper {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c P : Fin n) :
    reflPlaq τ c (((μ, ν), siteAtHyper τ P) : Plaq d n)
      = ((μ, ν), siteAtHyper τ (c - P)) := by
  have h : reflSite τ c (siteAtHyper (d := d) (n := n) τ P) = siteAtHyper τ (c - P) := by
    funext j
    by_cases hj : j = τ
    · subst hj; simp [reflSite, siteAtHyper]
    · simp [reflSite, siteAtHyper, Function.update_of_ne hj]
  simp only [reflPlaq, hμ, hν, if_false, h]

/-- **Translation invariance of the two-point function, from the reflection.**
`⟨φ_P · φ_Q⟩ = ⟨φ_0 · φ_{P−Q}⟩`, for plaquettes whose plane directions `μ`, `ν` both differ from the
lag axis `τ`, at every real coupling and with no hypothesis on the extent.

The reflection at constant `P` sends level `x` to `P − x`, so it sends the pair `(0, P − Q)` to the
pair `(P, Q)` — both plaquettes move under the same reflection, which is why one application of
`Reflect.expect_reflect_invariant` suffices and no separate translation symmetry is needed.

DERIVED: the `0` is the base lag the right-hand side is written at, which is `Fin n`'s zero and the
lag `corrHyper` is based at. -/
theorem EW_plaqE_pair_shift {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (P Q : Fin n) :
    EW Nc β (fun U => plaqE Nc (((μ, ν), siteAtHyper τ P) : Plaq d n) U
        * plaqE Nc (((μ, ν), siteAtHyper τ Q) : Plaq d n) U)
      = EW Nc β (fun U => plaqE Nc (((μ, ν), siteAtHyper τ (0 : Fin n)) : Plaq d n) U
          * plaqE Nc (((μ, ν), siteAtHyper τ (P - Q)) : Plaq d n) U) := by
  have h : EW Nc β (fun U =>
        plaqE Nc (((μ, ν), siteAtHyper τ (0 : Fin n)) : Plaq d n) (reflConf τ P U)
          * plaqE Nc (((μ, ν), siteAtHyper τ (P - Q)) : Plaq d n) (reflConf τ P U))
      = EW Nc β (fun U => plaqE Nc (((μ, ν), siteAtHyper τ (0 : Fin n)) : Plaq d n) U
          * plaqE Nc (((μ, ν), siteAtHyper τ (P - Q)) : Plaq d n) U) :=
    expect_reflect_invariant (n := n) Nc τ P β
      (fun U => plaqE Nc (((μ, ν), siteAtHyper τ (0 : Fin n)) : Plaq d n) U
        * plaqE Nc (((μ, ν), siteAtHyper τ (P - Q)) : Plaq d n) U)
  rw [← h]
  refine congrArg (EW Nc β) (funext fun U => ?_)
  show plaqE Nc (((μ, ν), siteAtHyper τ P) : Plaq d n) U
      * plaqE Nc (((μ, ν), siteAtHyper τ Q) : Plaq d n) U
    = plaqE Nc (((μ, ν), siteAtHyper τ (0 : Fin n)) : Plaq d n) (reflConf τ P U)
      * plaqE Nc (((μ, ν), siteAtHyper τ (P - Q)) : Plaq d n) (reflConf τ P U)
  rw [plaqE_reflConf Nc τ P _ U, plaqE_reflConf Nc τ P _ U,
    reflPlaq_siteAtHyper hμ hν P (0 : Fin n), reflPlaq_siteAtHyper hμ hν P (P - Q),
    sub_zero, sub_sub_cancel]

/-- **The centred reflected pairing is the connected correlation at lag `P − c + Q`.** The
expectation of the plaquette at lag `P`, centred at the one-point function at the origin, times the
plaquette at lag `Q` read on the configuration reflected at constant `c` and centred the same way,
equals `corrHyper` at lag `P − c + Q`. Requires `Nc ≠ 0` and both plane directions different from the
lag axis; there is no hypothesis on the extent or the coupling.

Centring at the one-point function at the origin is legitimate because that function is the same at
every lag (`ReflectPositive.EW_plaqE_lag`), and `EW_plaqE_pair_shift` moves the base back to the
origin.

DERIVED: the statement's numerals are the `0` in `Nc ≠ 0` and the `0`s of the origin site
`fun _ => 0` that the centring one-point function is read at. -/
theorem EW_centred_refl_eq_corrHyper (hNc : Nc ≠ 0) {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (β : ℝ) (c P Q : Fin n) :
    EW Nc β (fun U =>
        (plaqE Nc (((μ, ν), siteAtHyper τ P) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
        * (plaqE Nc (((μ, ν), siteAtHyper τ Q) : Plaq d n) (reflConf τ c U)
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))))
      = corrHyper (d := d) Nc n μ ν τ β (P - c + Q) := by
  have hzero : siteAtHyper (d := d) (n := n) τ (0 : Fin n) = (fun _ => 0 : Site d n) :=
    siteAtHyper_zero τ
  have hlag : P - (c - Q) = P - c + Q := by abel
  -- move the reflection onto the plaquette
  have hrefl : EW Nc β (fun U =>
        (plaqE Nc (((μ, ν), siteAtHyper τ P) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
        * (plaqE Nc (((μ, ν), siteAtHyper τ Q) : Plaq d n) (reflConf τ c U)
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))))
      = EW Nc β (fun U => (plaqE Nc (((μ, ν), siteAtHyper τ P) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))
        * (plaqE Nc (((μ, ν), siteAtHyper τ (c - Q)) : Plaq d n) U
          - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)))) :=
    congrArg (EW Nc β)
      (funext fun U => by rw [plaqE_reflConf Nc τ c _ U, reflPlaq_siteAtHyper hμ hν c Q])
  rw [hrefl,
    -- expand the centring
    EW_pair_sub_const hNc β (((μ, ν), siteAtHyper τ P) : Plaq d n)
      (((μ, ν), siteAtHyper τ (c - Q)) : Plaq d n) _,
    -- the one-point functions do not move with the lag
    EW_plaqE_lag Nc hμ hν P β, EW_plaqE_lag Nc hμ hν (c - Q) β,
    -- translation invariance on the two-point function
    EW_plaqE_pair_shift hμ hν β P (c - Q), hzero, hlag,
    -- and the correlation itself
    corrHyper_unfold Nc μ ν τ β (P - c + Q), EW_plaqE_lag Nc hμ hν (P - c + Q) β]
  ring

end Identify

/-! ## Part 6 — log-convexity -/

section Convex

variable {d n N : ℕ} [NeZero n]

/-- **Log-convexity of the lag correlation, at a general plane.**

    ρ(P − c + Q)²  ≤  ρ(P − c + P) · ρ(Q − c + Q),     c = a + a.

Holds for `ρ = corrHyper` on an even-extent lattice `n = 2 * m` with `0 < m`, gauge rank `N ≠ 0`,
plane directions `μ`, `ν` both different from the lag axis `τ`, every real coupling, and both levels
strictly below the plane at `a` (`lv a P < m`, `lv a Q < m`). No constant multiplies the right-hand
side: the three pairings share one partition function and one reflection.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m`, the `0` in `0 < m`
and the exponent `2`. The exponent is the square Cauchy–Schwarz produces; the others are the gauge
rank and the reflection geometry's even extent and nonempty half. `m` is half the extent and is a
variable, not a level. -/
theorem corrHyper_log_convex_at_plane (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {P Q : Fin n} (hP : lv a P < m) (hQ : lv a Q < m) :
    corrHyper (d := d) N n μ ν τ β (P - (a + a) + Q) ^ 2
      ≤ corrHyper (d := d) N n μ ν τ β (P - (a + a) + P)
        * corrHyper (d := d) N n μ ν τ β (Q - (a + a) + Q) := by
  have hdeg : ∀ R : Fin n, ¬ ((((μ, ν), siteAtHyper τ R) : Plaq d n).1.1 = τ
      ∧ (((μ, ν), siteAtHyper τ R) : Plaq d n).1.2 = τ) := fun R h => hμ h.1
  have hlvP : lv a ((((μ, ν), siteAtHyper τ P) : Plaq d n).2 τ) < m := by
    show lv a (siteAtHyper (d := d) (n := n) τ P τ) < m
    rwa [siteAtHyper_axis]
  have hlvQ : lv a ((((μ, ν), siteAtHyper τ Q) : Plaq d n).2 τ) < m := by
    show lv a (siteAtHyper (d := d) (n := n) τ Q τ) < m
    rwa [siteAtHyper_axis]
  have h := EW_refl_cauchy_schwarz hN τ a m hm hm0
    (((μ, ν), siteAtHyper τ P) : Plaq d n) (((μ, ν), siteAtHyper τ Q) : Plaq d n)
    (hdeg P) hlvP (hdeg Q) hlvQ
    (EW N β (plaqE N (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))) β
  rwa [EW_centred_refl_eq_corrHyper hN hμ hν β (a + a) P Q,
    EW_centred_refl_eq_corrHyper hN hμ hν β (a + a) P P,
    EW_centred_refl_eq_corrHyper hN hμ hν β (a + a) Q Q] at h

/-- **Log-convexity at the plane through the origin** — the statement in the form the lag carries it:

    ρ(e₁ + e₂)²  ≤  ρ(e₁ + e₁) · ρ(e₂ + e₂)

for every pair of lags strictly below half the extent, at even extent `n = 2 * m` with `0 < m`,
gauge rank `N ≠ 0`, plane directions `μ`, `ν` different from the lag axis, and every real coupling.
Taking the plane at the origin makes the reflection constant zero and the three lags read off
directly. This is `corrHyper_log_convex_at_plane` at `a = 0`.

DERIVED: the statement's numerals are the `0` in `N ≠ 0`, the `2` in `n = 2 * m`, the `0` in `0 < m`
and the exponent `2` of the square. The bound `m` on the lags is the reflection geometry's own — the
levels must sit strictly between the two fixed planes, which are `m` apart — and is a variable, not a
threshold chosen to make the inequality true. -/
theorem corrHyper_log_convex (hN : N ≠ 0) (τ : Fin d) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {e₁ e₂ : Fin n} (h1 : e₁.val < m) (h2 : e₂.val < m) :
    corrHyper (d := d) N n μ ν τ β (e₁ + e₂) ^ 2
      ≤ corrHyper (d := d) N n μ ν τ β (e₁ + e₁)
        * corrHyper (d := d) N n μ ν τ β (e₂ + e₂) := by
  have hlv : ∀ R : Fin n, lv (0 : Fin n) R = R.val := by
    intro R; show (R - 0).val = R.val; rw [sub_zero]
  have hshift : ∀ R S : Fin n, R - ((0 : Fin n) + (0 : Fin n)) + S = R + S := by
    intro R S; rw [add_zero, sub_zero]
  have h := corrHyper_log_convex_at_plane (N := N) hN τ (0 : Fin n) m hm hm0 hμ hν β
    (P := e₁) (Q := e₂) (by rw [hlv]; exact h1) (by rw [hlv]; exact h2)
  rwa [hshift e₁ e₂, hshift e₁ e₁, hshift e₂ e₂] at h

/-- **Log-convexity of the Clay correlation.** `corrClay` is `corrHyper` at `SU(3)` in four
dimensions, on the lattice `WilsonGauge`'s Osterwalder–Schrader measure is built on:

    corrClay (e₁ + e₂)²  ≤  corrClay (e₁ + e₁) · corrClay (e₂ + e₂)

at even extent `Nap + 1 = 2 * m` with `0 < m`, for lags `e₁`, `e₂` strictly below `m`, and at every
real coupling. The sign of the coupling is not a hypothesis: the even-lag weld is a conditional
square against a strictly positive Boltzmann weight and does not read it.

DERIVED: the statement's numerals are the `1` in `Nap + 1`, which is the lag arity at aperture `Nap`
and is the extent, the `2` in `2 * m`, which says that extent is even, the `0` in `0 < m`, and the
exponent `2` of the square. The `3` and `4` that fix `SU(3)` and four dimensions appear in the proof,
not in the statement — they are `WilsonBridge.corrClay`'s own. -/
theorem corrClay_log_convex (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {e₁ e₂ : Fin (Nap + 1)} (h1 : e₁.val < m) (h2 : e₂.val < m) :
    MassGap.WilsonBridge.corrClay (Nap + 1) β (e₁ + e₂) ^ 2
      ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β (e₁ + e₁)
        * MassGap.WilsonBridge.corrClay (Nap + 1) β (e₂ + e₂) :=
  corrHyper_log_convex (N := 3) (d := 4) (by norm_num) (2 : Fin 4) m hm hm0
    (by decide) (by decide) β h1 h2

/-- **Non-vacuity: the smallest extent that meets the bound, with a lag pair that is not the
diagonal.** At extent four the half is two, so lags `0` and `1` are both admissible, and the
inequality reads `ρ(1)² ≤ ρ(0)·ρ(2)` — three distinct lags, not an identity.

DERIVED: `3 + 1` is the extent four, written as `Nap + 1` at `Nap = 3` so that it matches
`corrClay_log_convex`'s index type; the half `m = 2` is then forced by `Nap + 1 = 2 * m`. The lags
`0 + 1`, `0 + 0` and `1 + 1` are the sums `corrClay_log_convex` forms from `e₁ = 0` and `e₂ = 1`,
which are the only two lags strictly below `m = 2`. The exponent `2` is the square. -/
theorem corrClay_log_convex_at_extent_four (β : ℝ) :
    MassGap.WilsonBridge.corrClay (3 + 1) β (0 + 1) ^ 2
      ≤ MassGap.WilsonBridge.corrClay (3 + 1) β (0 + 0)
        * MassGap.WilsonBridge.corrClay (3 + 1) β (1 + 1) :=
  corrClay_log_convex 3 2 (by norm_num) (by norm_num) β
    (e₁ := (0 : Fin 4)) (e₂ := (1 : Fin 4)) (by decide) (by decide)

/-- **The diagonal case.** With `e₁ = e₂` the statement reads `ρ(e+e)² ≤ ρ(e+e) · ρ(e+e)`, which
holds with equality. Hypotheses are `corrClay_log_convex`'s: even extent `Nap + 1 = 2 * m`, `0 < m`,
and the lag strictly below `m`.

DERIVED: the statement's numerals are the `1` in `Nap + 1`, the extent, the `2` in `2 * m` saying it
is even, the `0` in `0 < m`, and the exponent `2` of the square. -/
theorem corrClay_log_convex_diagonal (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {e : Fin (Nap + 1)} (h : e.val < m) :
    MassGap.WilsonBridge.corrClay (Nap + 1) β (e + e) ^ 2
      ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β (e + e)
        * MassGap.WilsonBridge.corrClay (Nap + 1) β (e + e) :=
  corrClay_log_convex Nap m hm hm0 β h h

end Convex

section Audit
#print axioms integrand_eq_paired_pair
#print axioms localObs
#print axioms mem_localObs

#print axioms localObs_measurable
#print axioms localObs_bounded
#print axioms localObs_mul_mem
#print axioms localObs_local
#print axioms pairing
#print axioms measurable_wPlane
#print axioms wPlane_nonneg
#print axioms wPlane_abs_le
#print axioms measurable_reflConf
#print axioms integrable_pairing
#print axioms pairing_add_left
#print axioms pairing_smul_left
#print axioms wPlane_reflConf
#print axioms pairing_symm
#print axioms pairing_nonneg
#print axioms wilsonReflForm
#print axioms obsPlus_mem
#print axioms pairing_obsPlus
#print axioms EW_refl_cauchy_schwarz
#print axioms siteAtHyper_zero
#print axioms siteAtHyper_axis
#print axioms reflPlaq_siteAtHyper
#print axioms EW_plaqE_pair_shift
#print axioms EW_centred_refl_eq_corrHyper
#print axioms corrHyper_log_convex_at_plane
#print axioms corrHyper_log_convex
#print axioms corrClay_log_convex
#print axioms corrClay_log_convex_at_extent_four
#print axioms corrClay_log_convex_diagonal
end Audit

end MassGap.LogConvex
