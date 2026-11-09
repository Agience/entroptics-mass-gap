import Mathlib
import MassGap.ProxyCov
import MassGap.NonGaussFromScale
import MassGap.BandShell

/-!
# MassGap.NondegFold — `ProxyNondeg` against the reflection split, the other non-triviality clauses and the band read

`NondegFromProxy.ProxyNondeg` is the base form of the non-degeneracy clause that
`ProxBound.CoreInputsAlongWPB` carries at the coupling `cpl βs` (its coupling-generalised copy, which `CouplingGen` generates under the `CouplingGen.Along` prefix).
The results here are stated for the base form. Whether each carries to the `Along` copy is not proved; the
arguments do not use the coupling. The clause: for every combination `c`
with a non-zero on-shell top part, a separated pair `(f, h)` and `δ > 0` with `δ ≤ |proxRead c f h|` for
small flow times, along `ultra`. This module asks whether it folds into the rest of the bundle. It does
not; what is proved is the exact form of the obstruction. Declarations are in the namespace
`MassGap.NondegFold`.

## 1. The reflected read is additive over the parity split (proved)

`cE c`, `cO c`: the parts of `c` over the indices of even and of odd time parity (`cE_add_cO`: they sum
to `c`; `pureC_cE`, `pureC_cO`: each is of one reflection sign). Under `ProxyCov.CfParity`, at every step,
scale, positive-time `g` and gap `m`, at the reflected pair `(θg, T_{2m} g)`:

* `proxRead_cE`: the even part reads `gK(Y₊, m)`, `Y₊ = cXs (evenS c) c g`;
* `proxRead_cO`: the odd part reads `−gK(Y₋, m)`, `Y₋ = cXs (oddS c) c g`;
* `proxRead_refl_additive`: `proxRead c = proxRead (cE c) + proxRead (cO c)`. The even–odd cross term is
  identically zero at the reflected pair, not merely small: the time step is symmetric for the reflection
  form (`ProxyCov.proxRead_refl_split`).
* `abs_proxRead_mixed`: with `Y₊`, `Y₋` in the half-space algebra,
  `|proxRead c| = | |proxRead (cE c)| − |proxRead (cO c)| |`.

So the premise of question (a) is sharper than stated: there is no cross term to carry. The mixed read is
the difference of two reflection-positive reads (`ApertureThing.gK ≥ 0`, each log-convex in the gap by
`ApertureThing.stateK_far_ge`). The reflected read of `c` is the reflection form pairing `cE c − cO c`
with `c`; it is positive only on the diagonal, which is the pure case.

## 2. The obstruction (proved, an abstract model)

`mixed_zero_every_gap`: an abstract model on `ℝ²` with the dot product as the reflection form and
`θ = diag(1, −1)` (an even and an electric channel). The shift is `q · id` (`q ≠ 0`); the theorem states the
reads at the shifted vectors `(q^m, 0)`, `(0, q^m)` and `(q^m, q^m)`. The equal-weight mixed vector is the
counterexample's choice. At every gap `m` the even part reads `q^{2m} > 0`, the odd part reads
`−q^{2m} ≠ 0`, and the mixed vector reads `0`, their sum. The shift itself is not in the statement. The pure
one-dimensional part is the case `ApertureThing.geom_sharp` shows to meet log-convexity with equality. This
is a model of the abstract setting, not an instance of the tree's reads. It extends
`ProxyCov.parity_load_bearing` (one gap) and `ProxyCov.mixed_no_propagate` (two gaps, unequal parts) to
every gap.

## 3. Question (a), plainly

No fold. `ProxyNondeg` at a mixed combination does not follow from the reflection-positivity lower bound,
a pure-sign non-zero read and `MixGerm`:

* the reflection-positivity floor (`ApertureThing.stateK_far_ge`, `ProxyCov.gapRead_far`) bounds each pure
  read from below at every larger gap; it says nothing about their difference (§2);
* `ExpandMatch` carries `RPGerm ↔ MixGerm` (`ProxyCov.rpGerm_iff_mixGerm`). `MixGerm` is an upper bound
  `|⟪B, A⟫ − ⟪B, B⟫| ≤ η` on proxy products against composite products. It transfers reads between proxies
  and composites; it is met wherever proxies and composites agree, including where every read is `0`. A
  clause whose content is `≤ η` cannot give `δ ≤ |·|`. Nor does it read the combination `c` at the
  reflected pair: its monomials are products of single proxies, not `c`'s two-point form;
* the pure part of the route (`PureC c`): `ProxyCov.proxyNondeg_of_gapRead` with `gapRead_far` reduces it to
  one pinned reflected read per combination, which is `ProxyNondeg`'s own clause at a pinned pair. That is
  a restatement, not a discharge.

Choosing a non-reflected separated pair does not help either. With `f`, `h` invariant under the time
reflection (separated in space) the even–odd cross terms vanish by reflection invariance of the state,
and reflecting in a spatial axis instead sorts the indices by their full parity vector; the axis parity is
fixed within a class (the parities of a monomial sum to `0` mod `2`), so the read is again a signed sum
`Σ ± gK` over classes, with signs of both kinds. Argued, not formalised. The relative sign is argued to be structural:
the Euclidean read of an electric channel is the Minkowski read times `i`, so the Euclidean two-point
form of a real mixed combination is not a norm.

Count: 9 inputs before (`ApertureBridge`, `ExpandMatch`, `ProxBound`, `ZoomSettling`, `FlowCovLim`,
`FlowWard`, `ProxyNondeg`, `ProxyGenLimGerm`, `ThreePointAtScale`), 9 after. No input removed or folded;
no capstone is built.

## 4. Question (b): the other non-triviality clauses (proved in part)

* `cfFree_not_proxyNondeg`: for any proposition `X` not reading the coefficients, a derivation
  `∀ cf, X → ProxyNondeg Wf cf` refutes `X` (at `cf = 0` `ProxyNondeg` fails, `NondegFromProxy.not_proxyNondeg_zero`
  with `FlowChoice.exists_onShellTopN`). `threePoint_not_gives_proxyNondeg`: the instance at
  `ThreePointAtScale`, which reads only the bare Wilson states. So no argument that does not read the
  coefficients derives `ProxyNondeg` from `ThreePointAtScale`. A derivation must use properties of `cf`.
  This is proved for the base forms; the `Along` forms are not stated.
* The converse is argued, not formalised: `ProxyNondeg` is a two-point clause, `ThreePointAtScale` a
  three-point one; a Gaussian (free) field has non-zero separated two-point reads and vanishing connected
  three-point reads, so two-point non-degeneracy does not give the three-point floor.
* `ProxyGenLimGerm` is not a non-triviality clause: it is an approximation `kern − 2 xL + gForm ≤ η` (the
  reflection distance from the proxies to the observer's span is small), an upper bound of the same kind as
  `MixGerm`. It cannot give `δ ≤ |·|`; transferring a lower bound through it needs the lower bound on the
  observer side, which is the same clause again.

Plainly: a merged clause `ProxyNondeg ∧ ThreePointAtScale` (or with `ProxyGenLimGerm`) would be a
relabelling; the count would drop with no content removed.

## 5. Question (c): against `BandShell.gap_iff_band_excess` (proved in part)

`gap_iff_band_excess` reads a Källén–Lehmann measure `ρ` with `SpecBottom ρ M2`; it states
`0 < M2 ↔ √p² < r`, `r` the `τ → ∞` decay rate of `bandProfile ρ p² τ`.

* `bandProfile_pos_of_specBottom`: `SpecBottom ρ M2` already makes every finite read
  `bandProfile ρ p² τ`, `τ ≥ 0`, strictly positive. The non-zero read is a premise of the band-excess
  statement, not its content.
* `nondeg_without_excess`: at `δ₀ + δ_M` every finite read is positive and there is no band excess.

Precisely: a non-zero separated read is a finite-separation lower bound, `ρ ≠ 0` in spectral terms (for a
pure-sign combination the reflected read is `gK = ∫ e^{−tE} dμ_g`, non-zero iff `μ_g ≠ 0`, argued). A band
excess is a statement on the `τ → ∞` decay rate, the bottom of the support of `ρ`, and is not one
finite-scale read. They are not the same kind of statement: the first is strictly weaker and is presupposed
by the second (argued for the lattice proxies, proved for a measure here). `ProxyNondeg` is on the lattice
proxies along `s → 0⁺`, `ultra`; `gap_iff_band_excess` on a continuum measure, which the bundle does not
construct.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the time axis, the plane, the signs, the even parity residue, the zero
coefficients and the observable `0`; `1` the unit coordinates of the model, the sign of the even part and
the width of the window read in `SpecBottom`; `2` the parity modulus and the two steps of one gap; `−1` the
electric sign; `q`, `m`, `M`, `M2`, `p2`, `τ`, `r` hypotheses or reads.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.NondegFold

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
  MassGap.CompositesBuild MassGap.MultiScaleAll MassGap.CompositesRen MassGap.ApproxFromExpand
  MassGap.NondegFromProxy MassGap.ClayData MassGap.ReflAvg MassGap.ProxyCov

variable {N : ℕ}

/-! ## 1. The parity split -/

/-- The even-time-parity part of `c`. DERIVED: `2` the parity modulus; `0` the even residue. -/
def cE (c : Ix0 →₀ ℝ) : Ix0 →₀ ℝ := c.filter fun i => ctau 0 i.1 % 2 = 0

/-- The odd-time-parity part of `c`. DERIVED: `2` the parity modulus; `0` the even residue. -/
def cO (c : Ix0 →₀ ℝ) : Ix0 →₀ ℝ := c.filter fun i => ¬ ctau 0 i.1 % 2 = 0

/-- The two parts sum to `c`. DERIVED: no numeral. -/
theorem cE_add_cO (c : Ix0 →₀ ℝ) : cE c + cO c = c :=
  Finsupp.filter_add_filter_not c _

/-- The even part is of one reflection sign. DERIVED: no numeral. -/
theorem pureC_cE (c : Ix0 →₀ ℝ) : PureC (cE c) :=
  Or.inl fun i hi => by
    simp only [cE, Finsupp.support_filter, Finset.mem_filter] at hi
    exact hi.2

/-- The odd part is of one reflection sign. DERIVED: no numeral. -/
theorem pureC_cO (c : Ix0 →₀ ℝ) : PureC (cO c) :=
  Or.inr fun i hi => by
    simp only [cO, Finsupp.support_filter, Finset.mem_filter] at hi
    exact hi.2

/-- The even part's even indices are `c`'s, with `c`'s coefficients. DERIVED: no numeral. -/
theorem cXs_evenS_cE [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (g : TestFn) :
    cXs Wf cf k s (evenS (cE c)) (cE c) g = cXs Wf cf k s (evenS c) c g := by
  have hS : evenS (cE c) = evenS c := by
    unfold evenS cE
    rw [Finsupp.support_filter, Finset.filter_filter]
    simp only [and_self]
  rw [hS]
  unfold cXs
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cE, Finsupp.filter_apply, if_pos (Finset.mem_filter.1 hi).2]

/-- The even part has no odd index. DERIVED: `0` the empty sum. -/
theorem cXs_oddS_cE [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (g : TestFn) : cXs Wf cf k s (oddS (cE c)) (cE c) g = 0 := by
  unfold cXs
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [oddS, cE, Finsupp.support_filter, Finset.mem_filter] at hi
  exact absurd hi.1.2 hi.2

/-- The odd part has no even index. DERIVED: `0` the empty sum. -/
theorem cXs_evenS_cO [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (g : TestFn) : cXs Wf cf k s (evenS (cO c)) (cO c) g = 0 := by
  unfold cXs
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [evenS, cO, Finsupp.support_filter, Finset.mem_filter] at hi
  exact absurd hi.2 hi.1.2

/-- The odd part's odd indices are `c`'s, with `c`'s coefficients. DERIVED: no numeral. -/
theorem cXs_oddS_cO [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (g : TestFn) :
    cXs Wf cf k s (oddS (cO c)) (cO c) g = cXs Wf cf k s (oddS c) c g := by
  have hS : oddS (cO c) = oddS c := by
    unfold oddS cO
    rw [Finsupp.support_filter, Finset.filter_filter]
    simp only [and_self]
  rw [hS]
  unfold cXs
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cO, Finsupp.filter_apply, if_pos (Finset.mem_filter.1 hi).2]

/-- The even part reads its gap read at the reflected pair. DERIVED: `0` the plane; `2` the two steps
of one gap. -/
theorem proxRead_cE [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (c : Ix0 →₀ ℝ) (g : TestFn) (k : ℕ) (s : ℝ) (m : ℕ) :
    proxRead Wf cf (cE c) (g.reflect 0)
        (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s
      = ApertureThing.gK k (cXs Wf cf k s (evenS c) c g) m := by
  rw [proxRead_refl_split hP, cXs_evenS_cE, cXs_oddS_cE, gK_zero, sub_zero]

/-- The odd part reads minus its gap read at the reflected pair. DERIVED: `0` the plane; `2` the two
steps of one gap. -/
theorem proxRead_cO [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (c : Ix0 →₀ ℝ) (g : TestFn) (k : ℕ) (s : ℝ) (m : ℕ) :
    proxRead Wf cf (cO c) (g.reflect 0)
        (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s
      = -ApertureThing.gK k (cXs Wf cf k s (oddS c) c g) m := by
  rw [proxRead_refl_split hP, cXs_evenS_cO, cXs_oddS_cO, gK_zero, zero_sub]

/-- **The reflected read is additive over the parity split**: the cross term vanishes identically.
Module docstring, §1. DERIVED: `0` the plane; `2` the two steps of one gap. -/
theorem proxRead_refl_additive [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : CfParity cf) (c : Ix0 →₀ ℝ) (g : TestFn) (k : ℕ) (s : ℝ) (m : ℕ) :
    proxRead Wf cf c (g.reflect 0) (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s
      = proxRead Wf cf (cE c) (g.reflect 0)
          (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s
        + proxRead Wf cf (cO c) (g.reflect 0)
          (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s := by
  rw [proxRead_cE hP, proxRead_cO hP, proxRead_refl_split hP]
  ring

/-- **The mixed read is the difference of the two pure reads**, with both parts in the half-space
algebra. Module docstring, §1. DERIVED: `0` the plane; `2` the two steps of one gap. -/
theorem abs_proxRead_mixed [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : CfParity cf) (c : Ix0 →₀ ℝ) (g : TestFn) (k : ℕ) (s : ℝ) (m : ℕ)
    (hE : cXs Wf cf k s (evenS c) c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0)
    (hO : cXs Wf cf k s (oddS c) c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    |proxRead Wf cf c (g.reflect 0) (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s|
      = abs (|proxRead Wf cf (cE c) (g.reflect 0)
            (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s|
          - |proxRead Wf cf (cO c) (g.reflect 0)
            (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s|) := by
  rw [proxRead_cE hP, proxRead_cO hP, proxRead_refl_split hP, abs_neg,
    abs_of_nonneg (gK_nonneg k hE m), abs_of_nonneg (gK_nonneg k hO m)]

/-! ## 2. The obstruction -/

/-- **Two pure parts non-degenerate at every gap, the mixed read `0` at every gap**: module docstring,
§2. DERIVED: `0` the zero coordinate and the null read; `−1` the electric sign through `thetaE`; `q`, `m`
hypotheses. -/
theorem mixed_zero_every_gap (q : ℝ) (hq : q ≠ 0) (m : ℕ) :
    0 < ExpandMatch.dotF (thetaE (q ^ m, (0 : ℝ))) (q ^ m, (0 : ℝ))
      ∧ ExpandMatch.dotF (thetaE ((0 : ℝ), q ^ m)) ((0 : ℝ), q ^ m) < 0
      ∧ ExpandMatch.dotF (thetaE (q ^ m, q ^ m)) (q ^ m, q ^ m)
          = ExpandMatch.dotF (thetaE (q ^ m, (0 : ℝ))) (q ^ m, (0 : ℝ))
            + ExpandMatch.dotF (thetaE ((0 : ℝ), q ^ m)) ((0 : ℝ), q ^ m)
      ∧ ExpandMatch.dotF (thetaE (q ^ m, q ^ m)) (q ^ m, q ^ m) = 0 := by
  have ht : ∀ x : ℝ × ℝ, thetaE x = (x.1, -x.2) := fun _ => rfl
  have hpos : 0 < q ^ m * q ^ m := mul_self_pos.2 (pow_ne_zero m hq)
  simp only [ht, ExpandMatch.dotF, LinearMap.mk₂_apply]
  refine ⟨by linarith, by linarith, by ring, by ring⟩

/-! ## 4. The other non-triviality clauses -/

/-- **No coefficient-free clause gives `ProxyNondeg`**: module docstring, §4. DERIVED: `0` the zero
coefficients; `2` the least colour count. -/
theorem cfFree_not_proxyNondeg (hN2 : 2 ≤ N) [NeZero N] (Wf : ℝ → ConfFlow N) {X : Prop}
    (h : ∀ cf : Ix0 → ℝ → (MIx →₀ ℝ), X → ProxyNondeg Wf cf) : ¬ X := fun hx =>
  not_proxyNondeg_zero Wf (FlowChoice.exists_onShellTopN hN2).choose_spec (h 0 hx)

/-- **`ThreePointAtScale` does not give `ProxyNondeg` uniformly in the coefficients.** DERIVED: `2` the
least colour count. -/
theorem threePoint_not_gives_proxyNondeg (hN2 : 2 ≤ N) [NeZero N] (Wf : ℝ → ConfFlow N) (ℓ : ℝ)
    (h : ∀ cf : Ix0 → ℝ → (MIx →₀ ℝ),
      NonGaussFromScale.ThreePointAtScale (NeZero.ne N) ℓ → ProxyNondeg Wf cf) :
    ¬ NonGaussFromScale.ThreePointAtScale (NeZero.ne N) ℓ :=
  cfFree_not_proxyNondeg hN2 Wf h

/-! ## 5. Against the band read -/

open MeasureTheory BandShell in
/-- **`SpecBottom` makes every finite band read positive**: module docstring, §5. DERIVED: `1` the width
of the window read; `0` the sign of `τ`. -/
theorem bandProfile_pos_of_specBottom {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 : ℝ}
    (hb : SpecBottom ρ M2) (p2 : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 < bandProfile ρ p2 τ := by
  have hne : NeZero ρ := ⟨fun h => by
    have h1 := hb.2 1 one_pos
    rw [h] at h1
    simp at h1⟩
  unfold bandProfile
  exact integral_exp_pos (integrable_band ρ p2 hτ)

open MeasureTheory BandShell in
/-- **Every finite read non-zero, no band excess**, at `δ₀ + δ_M`: module docstring, §5. DERIVED: `0`
the bottom and the signs. -/
theorem nondeg_without_excess {M p2 r : ℝ} (hM : 0 ≤ M) (hp : 0 ≤ p2)
    (hr : Tendsto (fun τ => -Real.log (bandProfile (Measure.dirac 0 + Measure.dirac M) p2 τ) / τ)
      atTop (𝓝 r)) :
    (∀ τ : ℝ, 0 ≤ τ → 0 < bandProfile (Measure.dirac 0 + Measure.dirac M) p2 τ)
      ∧ ¬ Real.sqrt p2 < r :=
  ⟨fun _ hτ => bandProfile_pos_of_specBottom (specBottom_zero_add hM) p2 hτ,
    (zero_mass_no_excess hM hp hr).1⟩

end MassGap.NondegFold

end

#print axioms MassGap.NondegFold.cE_add_cO
#print axioms MassGap.NondegFold.pureC_cE
#print axioms MassGap.NondegFold.pureC_cO
#print axioms MassGap.NondegFold.proxRead_cE
#print axioms MassGap.NondegFold.proxRead_cO
#print axioms MassGap.NondegFold.proxRead_refl_additive
#print axioms MassGap.NondegFold.abs_proxRead_mixed
#print axioms MassGap.NondegFold.mixed_zero_every_gap
#print axioms MassGap.NondegFold.cfFree_not_proxyNondeg
#print axioms MassGap.NondegFold.threePoint_not_gives_proxyNondeg
#print axioms MassGap.NondegFold.bandProfile_pos_of_specBottom
#print axioms MassGap.NondegFold.nondeg_without_excess
#print axioms MassGap.NondegFold.cXs_evenS_cE
#print axioms MassGap.NondegFold.cXs_oddS_cE
#print axioms MassGap.NondegFold.cXs_evenS_cO
#print axioms MassGap.NondegFold.cXs_oddS_cO
