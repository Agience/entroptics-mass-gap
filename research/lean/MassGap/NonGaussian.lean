import Mathlib
import MassGap.Moment
import MassGap.ShareEnvelope
import MassGap.SpectralGap
import MassGap.WightmanData
import MassGap.PlaneVariance
import MassGap.ClayFromConfinement

/-!
# MassGap.NonGaussian — requirement N: what it has to separate, and what the lattice separates

## What N has to say

Clay's N asks that the continuum theory not be a free field. A free field is Gaussian: its truncated
Schwinger functions of order three and higher vanish, so it is fixed by its two-point function. A
statement witnesses N only if every Gaussian theory falsifies it. Three facts decide its form.

1. **It cannot read a two-point function alone.** The entroptic read `Moment.Read` is built from a
   correlation profile `ρ` and nothing else. `read_tension_eq_of_rho_eq` shows that its tension, and
   so every comparison with the floor `¼·log 3`, depends on `ρ` alone, and a Gaussian with the same
   covariance has the same `ρ`. The variance floor is a two-point statement at lag zero, and
   `gaussian_meets_variance_floor` gives a Gaussian law that meets any variance floor.
2. **On the lattice, non-Gaussianity is automatic.** Every observable of a compact gauge group is
   bounded. A bounded observable never has a non-degenerate Gaussian law
   (`not_lawIsGaussian_of_ne_zero`), and a positive variance rules out the degenerate one
   (`not_lawIsGaussian_zero_of_variance_pos`). With `PlaneVariance.nu_var_iplaqObs_ge` this makes the
   plaquette's law non-Gaussian under every `mixCube` limit state at every `β ≥ 0`
   (`nu_iplaqObs_law_not_gaussian`); the tree produces that state where
   `StrongCoupling.coreRate (16 * 4) β < 1` (`FreeLimit.exists_tendsto_stateFree`), which includes
   `β = 0` (`lattice_plaquette_not_gaussian_at_zero_coupling`), where the Boltzmann weight is `1`
   (`wtFree_at_zero_coupling`) and the plaquettes do not interact.
3. **What survives a continuum limit is scale-free.** The limit renormalises the observable,
   `O ↦ Z·O + c`. The variance scales by `Z²` (`kappa2_affine`), so a variance floor has no
   renormalisation-independent content (`exists_rescale_variance_lt`). The proved floor
   `e^{−32β}·varReTr N / N²` also tends to zero as `β → ∞` (`plane_floor_tendsto_zero`). The ratio
   `κ₄/κ₂²` does not change under `O ↦ Z·O + c` (`kurtRatio_affine`), and the entroptic read does
   not change under `ρ ↦ Z²·ρ` (`scaleRead_tension`).

`ContinuumNonGaussian ν O` is an order-four condition in that scale-free form, for one observable
along a family: the variance is eventually positive and `|κ₄/κ₂²|` is eventually at least one
positive constant. It is invariant under renormalising each member
(`continuumNonGaussian_renormalize`), satisfiable (`coin_continuumNonGaussian`), and not implied by a
variance floor together with a non-Gaussian law (`flat_floor_nonGaussian_not_continuum`). It is not
N by itself at a gauge-invariant observable: the free gauge theory satisfies it, and so does the
`β = 0` plaquette at `SU(2)` (neither is proved here).

It witnesses N for an observable linear in the elementary field. A gauge-invariant observable is a
composite, and a composite of a free field is itself non-Gaussian — the square of a standard Gaussian
has `κ₄/κ₂² = 12`, and the Wick square of a free field has a non-zero truncated three-point function.
So for gauge-invariant observables N is a separation from the free theory's value of the same
composite: `|κ₄/κ₂²|`, or a higher connected function, differing from what the free gauge field gives
for that observable, uniformly along the family.

## The built non-triviality conjuncts at zero coupling

`partIV_at_zero_coupling` proves Part IV of `VarianceBridge.clay_four_parts` at `β = 0`, where the
kernel's weight is `1` (`gibbsWt_at_zero_coupling`). `ne_zero_orth_vacuum_at_zero_coupling` proves
`PlaneVariance.exists_ne_zero_orth_vacuum` at `β = 0`. `trivial_theory_meets_partIII_shape` proves
Part III's `Nontrivial Space` for `WightmanData.trivialWightmanQFTData`, whose Hamiltonian is zero.
None of the three separates the Wilson theory from a theory with no interaction.

## Open

Nothing here, and nothing in the tree, produces `ContinuumNonGaussian` for a Wilson family, and that
predicate alone would not be N there. Its intended instance is `ν i`, the infinite-volume Wilson
state at couplings `β i → ∞`, with `O i` a gauge-invariant observable smeared over a region of fixed
physical size at the spacing of `β i`. Three things are missing: the spacing law (requirement Y), a
smeared observable with a finite continuum limit, and a lower bound on `|κ₄/κ₂²|` of that observable
away from the free gauge theory's value for the same composite; `ContinuumNonGaussian` bounds it
away from `0` only. A bare block sum of plaquettes is not a suitable `O i`: at weak coupling its
variance is dominated by lattice-scale fluctuations with short-range correlations, so by the
central-limit mechanism its `κ₄/κ₂²` is expected to tend to zero as the block grows, whether or not
the theory interacts. That expectation is not proved here.
-/

namespace MassGap.NonGaussian

open MeasureTheory ProbabilityTheory Filter

/-! ## 1. The built conjuncts, read at zero coupling -/

section ZeroCoupling

/-- **The free-box Boltzmann weight is `1` at coupling `0`.** `ReflectionHalfSpace.wtFree φ β Λ ω u`
is `Real.exp (-β * actionOn φ (iplqAll Λ) (splice Λ u ω))`. At `β = 0` the exponent is `0`.

DERIVED: `0` is the coupling; `1` is `Real.exp 0`. -/
theorem wtFree_at_zero_coupling {G : Type} [Group G] (φ : G → ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    MassGap.ReflectionHalfSpace.wtFree φ 0 Λ ω u = 1 := by
  unfold MassGap.ReflectionHalfSpace.wtFree
  simp

#print axioms wtFree_at_zero_coupling

/-- **The fixed-boundary kernel's Boltzmann weight is `1` at coupling `0`.** `GibbsSpec.wt φ β Λ u ω`
is `Real.exp (-β * actionOn φ (boundaryPlaqs Λ) (splice Λ u ω))`. At `β = 0` the exponent is `0`.

DERIVED: `0` is the coupling; `1` is `Real.exp 0`. -/
theorem gibbsWt_at_zero_coupling {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (φ : G → ℝ) (Λ : Finset MassGap.GibbsSpec.ILink)
    (u : MassGap.GibbsSpec.VConf G Λ) (ω : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.wt φ 0 Λ u ω = 1 := by
  unfold MassGap.GibbsSpec.wt
  simp

#print axioms gibbsWt_at_zero_coupling

/-- **Part IV of `VarianceBridge.clay_four_parts` holds at coupling `0`.** At `SU N`, `2 ≤ N`: a
state `ν` that is DLR for the Wilson kernel at `β = 0`, normalised, and not a point mass. The
boundary condition `ω` and the link `l₀` are consumed by the proof, which passes them to
`wilson_eventual_variance_floor`; the conclusion mentions neither.

`SpecVarianceFloor.wilson_eventual_variance_floor` at `β = 0` supplies the floor and
`VarianceBridge.clay_nontriviality_of_eventual_variance_floor` concludes. The kernel's weight is `1`
there (`gibbsWt_at_zero_coupling`), so this conclusion holds for a kernel with no plaquette
interaction, and it does not separate the Wilson theory from one.

DERIVED: `2` is the rank bound, the one `wilson_eventual_variance_floor` requires; `0` is the coupling
and the excluded rank; `1` is the unit observable and the normalisation. -/
theorem partIV_at_zero_coupling {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (l₀ : MassGap.GibbsSpec.ILink) :
    ∃ ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
          (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) 0
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν
        ∧ ν 1 = 1 ∧ ¬ MassGap.DLRLimit.IsPointMass ν := by
  obtain ⟨f₀, cvar, hcvar, hvar⟩ :=
    MassGap.SpecVarianceFloor.wilson_eventual_variance_floor hN2 hN (le_refl (0 : ℝ)) ω l₀
  exact MassGap.VarianceBridge.clay_nontriviality_of_eventual_variance_floor
    (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) 0
    (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) ω f₀ cvar hcvar hvar

#print axioms partIV_at_zero_coupling

/-- **A non-zero vector orthogonal to the vacuum exists at coupling `0`.** At `SU N`, `2 ≤ N`: the
free box states at `β = 0` converge along `mixCube` to a state `ν`, and the gauge-invariant GNS space
at `ν` has a non-zero vector orthogonal to the vacuum.

`FreeLimit.exists_tendsto_stateFree` at `β = 0` supplies `ν`; its rate hypothesis holds because
`StrongCoupling.coreRate_at_zero` makes the rate `0`. `PlaneVariance.exists_ne_zero_orth_vacuum`
supplies the vector. The free-box weight is `1` there (`wtFree_at_zero_coupling`), so this vector
exists in a theory with no plaquette interaction.

DERIVED: `2` is the rank bound; `0` is the coupling, the excluded rank and the vacuum pairing; `1` is
the identity boundary configuration and the rate threshold; `4` is the dimension and `16 * 4` the
box touch-degree bound inside `exists_tendsto_stateFree`, carried unchanged. -/
theorem ne_zero_orth_vacuum_at_zero_coupling {N : ℕ} (hN2 : 2 ≤ N) (τ : Fin 4) (p : ℤ) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
      (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
            (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg (by omega : N ≠ 0))
            (MassGap.WilsonAction.wilsonDensity_le_two (by omega : N ≠ 0)) 0
            (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f))),
      ∃ y : MassGap.Transfer.GNS
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) 0 ν htend).toReflForm,
        y ≠ 0 ∧ (inner ℝ
          (MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p (by omega) 0 ν htend).vacGNS y
            : ℝ) = 0 := by
  have hN : N ≠ 0 := by omega
  obtain ⟨ν, htend⟩ := MassGap.FreeLimit.exists_tendsto_stateFree hN (le_refl (0 : ℝ))
    (by rw [MassGap.StrongCoupling.coreRate_at_zero]; norm_num) τ p
  exact ⟨ν, htend, MassGap.PlaneVariance.exists_ne_zero_orth_vacuum τ p hN2 hN (le_refl 0) ν htend⟩

#print axioms ne_zero_orth_vacuum_at_zero_coupling

/-- **Part III's conclusion shape holds for the theory with nothing in it.**
`WightmanData.trivialWightmanQFTData` has a `Nontrivial` state space and a zero Hamiltonian.
`VarianceBridge.clay_four_parts`' Part III conjunct asserts `Nontrivial` of the reconstructed space,
and `WightmanData.reconstructed_space_nontrivial` proves that of every `WightmanQFTData`, from the
vacuum and `0`. So that conjunct holds for this theory as well.

DERIVED: `0` is the zero operator. -/
theorem trivial_theory_meets_partIII_shape :
    Nontrivial MassGap.WightmanData.trivialWightmanQFTData.Space
      ∧ MassGap.WightmanData.trivialWightmanQFTData.qft.ham = 0 :=
  ⟨MassGap.WightmanData.reconstructed_space_nontrivial _, rfl⟩

#print axioms trivial_theory_meets_partIII_shape

end ZeroCoupling

/-! ## 2. Two-point statements admit a Gaussian comparator -/

section TwoPoint

/-- **The entroptic read's tension depends on the correlation profile alone.** Two reads at the same
aperture with the same `ρ` have the same tension. `Read.p` is `ρ` normalised and `Read.θ` does not
read the correlation, so `Read.tension` is a function of `ρ`.

Every comparison of a read with the floor `κ₀YM = ¼·log 3` is therefore a statement about a
two-point profile. A Gaussian field with covariance `ρ` has the same profile; this declaration does
not construct that field.

DERIVED: no numeral. -/
theorem read_tension_eq_of_rho_eq {N : ℕ} (R₁ R₂ : MassGap.Moment.Read N) (h : R₁.ρ = R₂.ρ) :
    R₁.tension = R₂.tension := by
  have hρ : ∀ d, R₁.ρ d = R₂.ρ d := fun d => congrFun h d
  have hθ : ∀ d, R₁.θ d = R₂.θ d := fun _ => rfl
  simp only [MassGap.Moment.Read.tension, MassGap.Moment.Read.p, hρ, hθ]

#print axioms read_tension_eq_of_rho_eq

/-- **The read is scale-free.** `ShareEnvelope.scaleRead R ht` is the read of the profile `t · ρ`,
`t > 0`; its tension is `R`'s. A field renormalisation `O ↦ Z·O` scales a connected two-point profile
by `Z²`, so the tension, and every comparison with the floor, does not see it.
`ShareEnvelope.scaleRead_p` is the same fact for the normalised profile, and
`ShareEnvelope.mass_floor_is_not_scale_free` shows that a floor on the total mass is not
scale-free.

DERIVED: `0` is the strict lower bound on `t`. -/
theorem scaleRead_tension {N : ℕ} (R : MassGap.Moment.Read N) {t : ℝ} (ht : 0 < t) :
    (MassGap.ShareEnvelope.scaleRead R ht).tension = R.tension := by
  have hθ : ∀ d, (MassGap.ShareEnvelope.scaleRead R ht).θ d = R.θ d := fun _ => rfl
  simp only [MassGap.Moment.Read.tension, MassGap.ShareEnvelope.scaleRead_p, hθ]

#print axioms scaleRead_tension

/-- **A Gaussian law meets every variance floor.** For `0 ≤ v` and `c ≤ v`, the Gaussian law
`gaussianReal m v` has mean `m` and a variance at least `c`.

So a lower bound on a variance holds for a Gaussian law with the same mean and variance; it cannot
separate a state from its Gaussian comparator.

DERIVED: `0` is the lower bound on `v`. -/
theorem gaussian_meets_variance_floor (m : ℝ) {c v : ℝ} (hv : 0 ≤ v) (hcv : c ≤ v) :
    (∫ x, x ∂(gaussianReal m v.toNNReal)) = m
      ∧ c ≤ variance id (gaussianReal m v.toNNReal) := by
  refine ⟨integral_id_gaussianReal, ?_⟩
  rw [variance_id_gaussianReal, Real.coe_toNNReal v hv]
  exact hcv

#print axioms gaussian_meets_variance_floor

/-- **The plaquette variance floor is met by the plaquette's Gaussian comparator.** At `SU N`,
`2 ≤ N`, `0 ≤ β` and a `mixCube` limit state `ν`: the Gaussian law with the plaquette's mean and
variance under `ν` has variance at least `e^{−32β} · varReTr N / N²`, the floor of
`PlaneVariance.nu_var_iplaqObs_ge`.

DERIVED: `32` is `PlaneVariance.nu_var_iplaqObs_ge`'s constant, `2 · 16`; `2` is the rank bound and
the square; `0` is the sign of `β` and the excluded rank; `1` is the identity boundary configuration;
`4` is the dimension. -/
theorem nu_plaquette_floor_met_by_gaussian {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) :
    Real.exp (-(β * 32)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2)
      ≤ variance id (gaussianReal (ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q))
          (ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
                * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
            - (ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2).toNNReal) := by
  have hfloor := MassGap.PlaneVariance.nu_var_iplaqObs_ge hN2 hN hβ τ p ν htend q hq
  have hpos : 0 < Real.exp (-(β * 32)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2) :=
    mul_pos (Real.exp_pos _) (div_pos (MassGap.PlaneVariance.varReTr_pos hN2)
      (pow_pos (Nat.cast_pos.mpr (by omega)) 2))
  exact (gaussian_meets_variance_floor _ (le_trans hpos.le hfloor) hfloor).2

#print axioms nu_plaquette_floor_met_by_gaussian

end TwoPoint

/-! ## 3. On the lattice, a positive variance already excludes every Gaussian law -/

section LatticeLaw

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **`f` has the Gaussian law `gaussianReal m v` under the state `ν`**: every bounded continuous
`h : ℝ → ℝ` satisfies `ν (h ∘ f) = ∫ h d(gaussianReal m v)`.

Bounded continuous functions determine a Borel probability law on `ℝ`, so this is the statement that
`f`'s law under `ν` is `gaussianReal m v`. The equivalence with a pushforward of
`DLRLimit.gibbsMeasure ν` is not proved here. At `v = 0` the law is `Measure.dirac m`.

DERIVED: no numeral. -/
def LawIsGaussian (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (m : ℝ) (v : NNReal) : Prop :=
  ∀ h : C(ℝ, ℝ), (∃ C : ℝ, ∀ x, |h x| ≤ C) → ν (h.comp f) = ∫ x, h x ∂(gaussianReal m v)

#print axioms LawIsGaussian

/-- **A bounded observable never has a non-degenerate Gaussian law.** For every state `ν`, every
continuous `f` on the compact `X`, every `m` and every `v ≠ 0`, `f` does not have the law
`gaussianReal m v` under `ν`.

The test function is `SpectralGap.ramp M 1` at `M = ‖f‖ + 1`: it vanishes below `M`, so on the
range of `f`, and the state gives it `0`; it is `1` from `M + 1`. Lebesgue measure is absolutely
continuous with respect to the Gaussian law (`gaussianReal_absolutelyContinuous'`), so `(M + 1, ∞)`
has positive Gaussian mass and the ramp a positive Gaussian integral. No dynamics enters.

DERIVED: `0` is the excluded variance. The `1`s of the ramp's width and of the offset `‖f‖ + 1` are
in the proof, not the statement; CHOSEN there as any positive width and any positive margin above
`‖f‖` serve. -/
theorem not_lawIsGaussian_of_ne_zero (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (m : ℝ)
    {v : NNReal} (hv : v ≠ 0) : ¬ LawIsGaussian ν f m v := by
  intro hlaw
  set M : ℝ := ‖f‖ + 1 with hM
  let r : C(ℝ, ℝ) := ⟨MassGap.SpectralGap.ramp M 1, MassGap.SpectralGap.continuous_ramp M 1⟩
  have hr : ∀ x, r x = MassGap.SpectralGap.ramp M 1 x := fun _ => rfl
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]
    exact MassGap.SpectralGap.ramp_nonneg M 1 x
  have hr1 : ∀ x, r x ≤ 1 := fun x => by
    rw [hr]
    unfold MassGap.SpectralGap.ramp
    exact min_le_left _ _
  have hb : ∃ C : ℝ, ∀ x, |r x| ≤ C :=
    ⟨1, fun x => by rw [abs_of_nonneg (hr0 x)]; exact hr1 x⟩
  have hcomp : r.comp f = 0 := by
    ext y
    rw [ContinuousMap.comp_apply, ContinuousMap.zero_apply, hr]
    refine MassGap.SpectralGap.ramp_eq_zero one_pos ?_
    have h1 := f.norm_coe_le_norm y
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (f y)]
  have hL := hlaw r hb
  rw [hcomp, ν.map_zero] at hL
  have hint : Integrable (fun x => r x) (gaussianReal m v) :=
    (integrable_const (1 : ℝ)).mono' r.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr0 x)]
        exact hr1 x))
  have hsupp : Set.Ioi (M + 1) ⊆ Function.support (fun x => r x) := by
    intro x hx
    have hx1 : r x = 1 := by
      rw [hr]
      exact MassGap.SpectralGap.ramp_eq_one one_pos (le_of_lt (Set.mem_Ioi.mp hx))
    show r x ≠ 0
    rw [hx1]
    exact one_ne_zero
  have hmeas : 0 < gaussianReal m v (Function.support (fun x => r x)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsupp)
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := gaussianReal_absolutelyContinuous' m hv h0
    rw [Real.volume_Ioi] at h1
    exact ENNReal.top_ne_zero h1
  have hpos : 0 < ∫ x, r x ∂(gaussianReal m v) :=
    (integral_pos_iff_support_of_nonneg (fun x => hr0 x) hint).mpr hmeas
  linarith

#print axioms not_lawIsGaussian_of_ne_zero

/-- **A positive variance excludes the degenerate Gaussian law.** If `0 < ν (f * f) − (ν f)²`, then
`f` does not have the law `gaussianReal m 0 = Measure.dirac m` under `ν`, for any `m`.

The test function `x ↦ min ((x − m)²) K`, with `K = (‖f‖ + |m|)²`, agrees with `(x − m)²` on the
range of `f` and vanishes at `m`. So a Dirac law would give `ν ((f − m)²) = 0`, while
`PlaneVariance.state_centred_sq` makes that value the variance plus `(ν f − m)²`.

DERIVED: `0` is the degenerate variance and the strict lower bound on the variance; `2` is the
square. -/
theorem not_lawIsGaussian_zero_of_variance_pos (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ))
    (m : ℝ) (hvar : 0 < ν (f * f) - (ν f) ^ 2) : ¬ LawIsGaussian ν f m 0 := by
  intro hlaw
  set K : ℝ := (‖f‖ + |m|) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  let q : C(ℝ, ℝ) := ⟨fun x => min ((x - m) ^ 2) K, by fun_prop⟩
  have hq : ∀ x, q x = min ((x - m) ^ 2) K := fun _ => rfl
  have hb : ∃ C : ℝ, ∀ x, |q x| ≤ C :=
    ⟨K, fun x => by
      rw [hq, abs_of_nonneg (le_min (sq_nonneg _) hK0)]
      exact min_le_right _ _⟩
  have hcomp : q.comp f = (f - m • (1 : C(X, ℝ))) * (f - m • (1 : C(X, ℝ))) := by
    ext y
    rw [ContinuousMap.comp_apply, hq]
    have h1 := f.norm_coe_le_norm y
    rw [Real.norm_eq_abs] at h1
    obtain ⟨h1l, h1r⟩ := abs_le.mp h1
    obtain ⟨hml, hmr⟩ := abs_le.mp (le_refl |m|)
    have hle : (f y - m) ^ 2 ≤ K := by
      rw [hK]
      exact sq_le_sq' (by linarith) (by linarith)
    rw [min_eq_left hle]
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul]
    ring
  have hL := hlaw q hb
  rw [hcomp, MassGap.PlaneVariance.state_centred_sq, gaussianReal_zero_var, integral_dirac, hq,
    sub_self] at hL
  have hz : min ((0 : ℝ) ^ 2) K = 0 := by
    rw [zero_pow two_ne_zero]
    exact min_eq_left hK0
  rw [hz] at hL
  nlinarith [sq_nonneg (ν f - m)]

#print axioms not_lawIsGaussian_zero_of_variance_pos

/-- **A positive variance excludes every Gaussian law.** If `0 < ν (f * f) − (ν f)²`, then for every
`m` and every `v`, `f` does not have the law `gaussianReal m v` under `ν`.
`not_lawIsGaussian_of_ne_zero` at `v ≠ 0`, `not_lawIsGaussian_zero_of_variance_pos` at `v = 0`.

DERIVED: `0` is the strict lower bound on the variance; `2` is the square. -/
theorem not_lawIsGaussian_of_variance_pos (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ))
    (hvar : 0 < ν (f * f) - (ν f) ^ 2) (m : ℝ) (v : NNReal) : ¬ LawIsGaussian ν f m v := by
  by_cases hv : v = 0
  · subst hv
    exact not_lawIsGaussian_zero_of_variance_pos ν f m hvar
  · exact not_lawIsGaussian_of_ne_zero ν f m hv

#print axioms not_lawIsGaussian_of_variance_pos

/-- **The plaquette's law under a limit state is not Gaussian.** At `SU N`, `2 ≤ N`, `0 ≤ β`, and
`ν` a `mixCube` limit of the free box states: for every plaquette `q` with two distinct directions,
every `m` and every `v`, the plaquette observable does not have the law `gaussianReal m v` under `ν`.

`PlaneVariance.nu_var_iplaqObs_ge` makes the variance positive and
`not_lawIsGaussian_of_variance_pos` concludes. The statement allows `β = 0`. The limit `ν` is a
hypothesis; the tree produces it where `coreRate (16 * 4) β < 1`
(`FreeLimit.exists_tendsto_stateFree`).

DERIVED: `2` is the rank bound and the square; `0` is the sign of `β` and the excluded rank; `32` is
the floor's constant, inside the proof only; `1` is the identity boundary configuration; `4` is the
dimension. -/
theorem nu_iplaqObs_law_not_gaussian {N : ℕ} (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) (m : ℝ) (v : NNReal) :
    ¬ LawIsGaussian ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q) m v := by
  refine not_lawIsGaussian_of_variance_pos ν _ ?_ m v
  have hfloor := MassGap.PlaneVariance.nu_var_iplaqObs_ge hN2 hN hβ τ p ν htend q hq
  have hpos : 0 < Real.exp (-(β * 32)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2) :=
    mul_pos (Real.exp_pos _) (div_pos (MassGap.PlaneVariance.varReTr_pos hN2)
      (pow_pos (Nat.cast_pos.mpr (by omega)) 2))
  exact lt_of_lt_of_le hpos hfloor

#print axioms nu_iplaqObs_law_not_gaussian

/-- **The same holds at coupling `0`.** At `SU N`, `2 ≤ N`: the free box states at `β = 0` converge
along `mixCube` to a state `ν`, and under `ν` no plaquette with two distinct directions has a
Gaussian law.

The free-box weight is `1` at `β = 0` (`wtFree_at_zero_coupling`). So lattice non-Gaussianity holds in
a theory with no plaquette interaction, and it is not requirement N.

DERIVED: `2` is the rank bound; `0` is the coupling and the excluded rank; `1` is the identity
boundary configuration and the rate threshold; `4` is the dimension; `16 * 4` is
`exists_tendsto_stateFree`'s touch-degree bound, carried unchanged. -/
theorem lattice_plaquette_not_gaussian_at_zero_coupling {N : ℕ} (hN2 : 2 ≤ N) (τ : Fin 4)
    (p : ℤ) :
    ∃ ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
            (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg (by omega : N ≠ 0))
            (MassGap.WilsonAction.wilsonDensity_le_two (by omega : N ≠ 0)) 0
            (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f)))
      ∧ ∀ q : MassGap.GibbsSpec.IPlaq, q.1.1 ≠ q.1.2 → ∀ (m : ℝ) (v : NNReal),
          ¬ LawIsGaussian ν (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q) m v := by
  have hN : N ≠ 0 := by omega
  obtain ⟨ν, htend⟩ := MassGap.FreeLimit.exists_tendsto_stateFree hN (le_refl (0 : ℝ))
    (by rw [MassGap.StrongCoupling.coreRate_at_zero]; norm_num) τ p
  exact ⟨ν, htend, fun q hq m v =>
    nu_iplaqObs_law_not_gaussian hN2 hN (le_refl 0) τ p ν htend q hq m v⟩

#print axioms lattice_plaquette_not_gaussian_at_zero_coupling

end LatticeLaw

/-! ## 4. Scale: the floor is not renormalisation-invariant, the cumulant ratio is -/

section Scale

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The proved plaquette floor tends to zero as the coupling grows.**
`e^{−32β} · varReTr N / N² → 0` as `β → ∞`. The floor of `PlaneVariance.nu_var_iplaqObs_ge` gives
no bound uniform in `β`, and a continuum limit sends `β → ∞`.

This is a statement about the bound, not about the variance it bounds.

DERIVED: `32` is `PlaneVariance.nu_var_iplaqObs_ge`'s constant, `2 · 16`; `2` is the square; `0` is
the limit. -/
theorem plane_floor_tendsto_zero (N : ℕ) :
    Tendsto (fun β : ℝ => Real.exp (-(β * 32)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2))
      atTop (nhds 0) := by
  have h1 : Tendsto (fun β : ℝ => β * 32) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const (by norm_num)
  have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const
    (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2)
  rw [zero_mul] at h2
  exact h2

#print axioms plane_floor_tendsto_zero

/-- **A variance floor is not renormalisation-invariant.** For every state `ν`, every observable `f`
and every `c > 0`, some non-zero multiple `a • f` has variance below `c`.

`VarianceBridge.variance_smul` scales the variance by `a²`; with `V` the variance of `f`,
`a = √(c / (2(|V| + 1)))` puts it below `c`. A floor on an unnormalised observable therefore says
nothing a field renormalisation cannot undo.

DERIVED: `0` is the strict lower bound on `c` and the excluded scale; `2` is the square in the
variance. `2` and `1` inside the proof's witness `√(c / (2(|V| + 1)))` are CHOSEN: any positive `k`,
`j` with `|V| < k(|V| + j)` serve; `k = j = 1` already does, and the `2` is slack. -/
theorem exists_rescale_variance_lt (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) {c : ℝ}
    (hc : 0 < c) : ∃ a : ℝ, a ≠ 0 ∧ ν ((a • f) * (a • f)) - (ν (a • f)) ^ 2 < c := by
  obtain ⟨V, hV⟩ : ∃ V : ℝ, ν (f * f) - (ν f) ^ 2 = V := ⟨_, rfl⟩
  have hden : 0 < 2 * (|V| + 1) := by positivity
  set t : ℝ := c / (2 * (|V| + 1)) with ht
  have ht0 : 0 < t := div_pos hc hden
  refine ⟨Real.sqrt t, (Real.sqrt_pos.mpr ht0).ne', ?_⟩
  rw [MassGap.VarianceBridge.variance_smul, hV, Real.sq_sqrt ht0.le]
  have h1 : t * V ≤ t * |V| := mul_le_mul_of_nonneg_left (le_abs_self V) ht0.le
  have h2 : t * |V| < c := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [abs_nonneg V]
  linarith

#print axioms exists_rescale_variance_lt

/-- The `k`-th central moment of `f` in the state `ν`: `ν ((f − ν f)^k)`.

DERIVED: `1` is the constant observable the mean multiplies. -/
noncomputable def centMom (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (k : ℕ) : ℝ :=
  ν ((f - (ν f) • (1 : C(X, ℝ))) ^ k)

#print axioms centMom

/-- The second cumulant, the variance.

DERIVED: `2` is the cumulant's order. -/
noncomputable def kappa2 (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) : ℝ := centMom ν f 2

/-- The fourth cumulant, `μ₄ − 3 μ₂²`, which is `0` for a real random variable with a Gaussian law
(not proved here; no observable on a compact space has a non-degenerate Gaussian law,
`not_lawIsGaussian_of_ne_zero`).

DERIVED: `4` and `2` are the moments' orders; `3` is `E Z⁴ / (E Z²)²` for a centred Gaussian `Z`,
the coefficient that makes the fourth cumulant of a Gaussian zero. -/
noncomputable def kappa4 (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) : ℝ :=
  centMom ν f 4 - 3 * centMom ν f 2 ^ 2

/-- The normalised fourth cumulant `κ₄ / κ₂²`. At `κ₂ = 0` it is `0`, by `x / 0 = 0`;
`ContinuumNonGaussian` requires `0 < κ₂` separately.

DERIVED: `2` is the power that makes the ratio scale-free, `κ₄` scaling by `a⁴` and `κ₂` by `a²`.
CHOSEN: the fourth cumulant rather than the third. An odd cumulant can vanish by a symmetry of the
law — at `SU(2)` and `β = 0` the plaquette trace is symmetric under the centre — while an even one
does not vanish for that reason. -/
noncomputable def kurtRatio (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) : ℝ :=
  kappa4 ν f / kappa2 ν f ^ 2

#print axioms kurtRatio

/-- The second cumulant is the variance, `ν (f * f) − (ν f)²`.

DERIVED: `2` is the square. -/
theorem kappa2_eq_variance (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) :
    kappa2 ν f = ν (f * f) - (ν f) ^ 2 := by
  unfold kappa2 centMom
  rw [show (f - (ν f) • (1 : C(X, ℝ))) ^ 2 = (f - (ν f) • 1) * (f - (ν f) • 1) from sq _,
    MassGap.PlaneVariance.state_centred_sq]
  ring

#print axioms kappa2_eq_variance

/-- **Central moments under an affine change of the observable.**
`centMom ν (a • f + b • 1) k = a ^ k * centMom ν f k`: the shift `b` cancels against the mean and the
scale comes out as `a ^ k`.

DERIVED: `1` is the constant observable. -/
theorem centMom_affine (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (a b : ℝ) (k : ℕ) :
    centMom ν (a • f + b • (1 : C(X, ℝ))) k = a ^ k * centMom ν f k := by
  have hmean : ν (a • f + b • (1 : C(X, ℝ))) = a * ν f + b := by
    rw [ν.map_add, ν.map_smul, ν.map_smul, ν.map_one, mul_one]
  have hcen : a • f + b • (1 : C(X, ℝ)) - (ν (a • f + b • (1 : C(X, ℝ)))) • (1 : C(X, ℝ))
      = a • (f - (ν f) • (1 : C(X, ℝ))) := by
    rw [hmean]
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul]
    ring
  unfold centMom
  rw [hcen, smul_pow, ν.map_smul]

#print axioms centMom_affine

/-- **The variance scales by `a²`.** `kappa2 ν (a • f + b • 1) = a ^ 2 * kappa2 ν f`.

DERIVED: `2` is the cumulant's order; `1` is the constant observable. -/
theorem kappa2_affine (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) (a b : ℝ) :
    kappa2 ν (a • f + b • (1 : C(X, ℝ))) = a ^ 2 * kappa2 ν f :=
  centMom_affine ν f a b 2

#print axioms kappa2_affine

/-- **The normalised fourth cumulant is renormalisation-invariant.** For `a ≠ 0` and every `b`,
`kurtRatio ν (a • f + b • 1) = kurtRatio ν f`. When `κ₂ = 0` both sides are `0`, by Lean's `x / 0 = 0`.

DERIVED: `4` and `2` are the cumulants' orders, and `a ^ 4 = (a ^ 2) ^ 2` is why the ratio is
scale-free; `3` is `kappa4`'s coefficient; `1` is the constant observable; `0` is the excluded
scale. -/
theorem kurtRatio_affine (ν : MassGap.DLRLimit.State X) (f : C(X, ℝ)) {a : ℝ} (ha : a ≠ 0)
    (b : ℝ) : kurtRatio ν (a • f + b • (1 : C(X, ℝ))) = kurtRatio ν f := by
  unfold kurtRatio kappa4 kappa2
  simp only [centMom_affine]
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero 4 ha
  have hsq : (a ^ 2 * centMom ν f 2) ^ 2 = a ^ 4 * centMom ν f 2 ^ 2 := by ring
  rw [hsq, show a ^ 4 * centMom ν f 4 - 3 * (a ^ 4 * centMom ν f 2 ^ 2)
      = a ^ 4 * (centMom ν f 4 - 3 * centMom ν f 2 ^ 2) by ring]
  exact mul_div_mul_left _ _ ha4

#print axioms kurtRatio_affine

end Scale

/-! ## 5. An order-four condition in scale-free form -/

section Target

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **An order-four condition along a family, in scale-free form.** Along the states `ν i` and
observables `O i`, eventually in `i`: the variance of `O i` is positive, and `|κ₄/κ₂²|` of `O i` is
at least one positive constant `c`, the same for every `i`.

A Gaussian law of positive variance has `κ₄ = 0`, so a family converging in law to one, with its
moments up to order four converging, fails this; a family collapsing to a point mass need not
(`(1 / (i + 1)) • coinObs` under `coinState` has `κ₄/κ₂² = −2` at every `i`, by
`kurtRatio_affine`). The predicate is unchanged by renormalising each member
(`continuumNonGaussian_renormalize`), which a variance floor is not (`exists_rescale_variance_lt`).

Scope: every gauge-invariant local observable is at least quadratic in the gauge field, and a
quadratic form `ZᵀAZ` of a standard Gaussian vector `Z`, `A` symmetric and non-zero, has
`κ₄/κ₂² = 12·tr A⁴/(tr A²)² > 0` for each fixed `A`. The cumulants of one smeared composite carry
its contact terms; the separated three-point statistic `ThreePointN.sepRatio` of three disjoint
composites carries none, and duality zeroes its free value (`ThreePointN.freeSepRatio_of_duality`, a
matrix statement). Families with no interaction satisfy it too (`coin_continuumNonGaussian`; the `β = 0`
plaquette, `κ₄/κ₂² = −1` at `SU(2)`), and a non-Gaussian law need not (`flat_kurtRatio`). The
quadratic-form value, the free-theory instance and the `SU(2)` value are not proved here. N at a
gauge-invariant `O i` is `|κ₄/κ₂²|` bounded away from the free theory's value for the same
composite, uniformly along the family; this predicate bounds it away from `0` only.

Intended instance, NOT constructed anywhere: `X` the configuration space of `ℤ⁴`, `ν i` the
infinite-volume Wilson state at couplings `β i → ∞`, and `O i` a gauge-invariant observable smeared
over a region of fixed physical size at the spacing of `β i`. There the predicate alone is not N.

DERIVED: `0` is the strict lower bound on `c` and on the variance; `4` and `2` are inside
`kurtRatio`. -/
def ContinuumNonGaussian (ν : ℕ → MassGap.DLRLimit.State X) (O : ℕ → C(X, ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, 0 < kappa2 (ν i) (O i) ∧ c ≤ |kurtRatio (ν i) (O i)|

#print axioms ContinuumNonGaussian

/-- **`ContinuumNonGaussian` does not see field renormalisation.** For non-zero scales `a i` and any
shifts `b i`, the family `a i • O i + b i • 1` satisfies it exactly when `O i` does.

DERIVED: `0` is the excluded scale and the lower bound in the variance clause; `2` is the square
`a i ^ 2`; `1` is the constant observable. -/
theorem continuumNonGaussian_renormalize (ν : ℕ → MassGap.DLRLimit.State X) (O : ℕ → C(X, ℝ))
    (a b : ℕ → ℝ) (ha : ∀ i, a i ≠ 0) :
    ContinuumNonGaussian ν (fun i => a i • O i + b i • (1 : C(X, ℝ)))
      ↔ ContinuumNonGaussian ν O := by
  have hk : ∀ i, kurtRatio (ν i) (a i • O i + b i • (1 : C(X, ℝ))) = kurtRatio (ν i) (O i) :=
    fun i => kurtRatio_affine (ν i) (O i) (ha i) (b i)
  have h2 : ∀ i, (0 < kappa2 (ν i) (a i • O i + b i • (1 : C(X, ℝ))))
      ↔ 0 < kappa2 (ν i) (O i) := by
    intro i
    rw [kappa2_affine]
    have hsq : 0 < a i ^ 2 := sq_pos_iff.mpr (ha i)
    exact ⟨fun h => lt_of_mul_lt_mul_left (by rw [mul_zero]; exact h) hsq.le,
      fun h => mul_pos hsq h⟩
  unfold ContinuumNonGaussian
  simp only [hk, h2]

#print axioms continuumNonGaussian_renormalize

/-! ### A family that satisfies it -/

/-- The state on `Fin 2` giving each point weight `1/2`.

CHOSEN: the fair two-point law, the simplest law with `κ₄ ≠ 0`; `2` is the number of points and the
denominator of the equal weights. -/
noncomputable def coinState : MassGap.DLRLimit.State (Fin 2) where
  toFun f := (f 0 + f 1) / 2
  map_add' f g := by
    simp only [ContinuousMap.add_apply]
    ring
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring
  nonneg' f hf := div_nonneg (add_nonneg (hf 0) (hf 1)) (by norm_num)
  one' := by
    simp only [ContinuousMap.one_apply]
    norm_num

#print axioms coinState

/-- The observable `±1` on `Fin 2`.

CHOSEN: the values `1` and `-1`, symmetric about the mean so that the mean is `0`. DERIVED: `2` is
the number of points. -/
noncomputable def coinObs : C(Fin 2, ℝ) := ⟨(![1, -1] : Fin 2 → ℝ), continuous_of_discreteTopology⟩

/-- DERIVED: `0` and `1` are the two points; `2` is the denominator of the equal weights. -/
theorem coinState_apply (g : C(Fin 2, ℝ)) : coinState g = (g 0 + g 1) / 2 := rfl

/-- DERIVED: `0` is the mean of `±1` under equal weights. -/
theorem coin_mean : coinState coinObs = 0 := by
  rw [coinState_apply]
  norm_num [coinObs]

/-- DERIVED: `1` and `-1` are the two values; `2` is the denominator of the equal weights. -/
theorem coin_centMom (k : ℕ) : centMom coinState coinObs k = (1 + (-1) ^ k) / 2 := by
  unfold centMom
  rw [coin_mean, coinState_apply]
  norm_num [coinObs]

/-- DERIVED: `1` is `((1)² + (-1)²)/2`. -/
theorem coin_kappa2 : kappa2 coinState coinObs = 1 := by
  unfold kappa2
  rw [coin_centMom]
  norm_num

/-- DERIVED: `-2` is `(1 − 3·1²)/1²`, the fourth moment `1` less three times the squared variance. -/
theorem coin_kurtRatio : kurtRatio coinState coinObs = -2 := by
  unfold kurtRatio kappa4 kappa2
  simp only [coin_centMom]
  norm_num

#print axioms coin_kurtRatio

/-- **`ContinuumNonGaussian` is satisfiable.** The constant family `coinState`, `coinObs` satisfies it
with `c = 1`, since its variance is `1` and `|κ₄/κ₂²| = 2`.

DERIVED: no numeral in the statement. In the proof `c = 1` is CHOSEN: any `c` in `(0, 2]` serves,
`2` being `|κ₄/κ₂²|`. -/
theorem coin_continuumNonGaussian :
    ContinuumNonGaussian (fun _ : ℕ => coinState) (fun _ : ℕ => coinObs) := by
  refine ⟨1, one_pos, Filter.Eventually.of_forall (fun _ => ⟨?_, ?_⟩)⟩
  · show 0 < kappa2 coinState coinObs
    rw [coin_kappa2]
    norm_num
  · show 1 ≤ |kurtRatio coinState coinObs|
    rw [coin_kurtRatio, abs_neg, abs_two]
    norm_num

#print axioms coin_continuumNonGaussian

/-! ### A bounded family with a variance floor that fails it -/

/-- The state on `Fin 3` with weights `1/6, 2/3, 1/6`.

DERIVED: the three-point law on `−1, 0, 1` with weight `p/2` at `±1` has `κ₄/κ₂² = 1/p − 3`, which
vanishes at `p = 1/3`; the weights are `p/2 = 1/6` at `±1` and `1 − p = 2/3` at `0`. -/
noncomputable def flatState : MassGap.DLRLimit.State (Fin 3) where
  toFun f := f 0 / 6 + 2 * f 1 / 3 + f 2 / 6
  map_add' f g := by
    simp only [ContinuousMap.add_apply]
    ring
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring
  nonneg' f hf := by
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    show 0 ≤ f 0 / 6 + 2 * f 1 / 3 + f 2 / 6
    linarith
  one' := by
    simp only [ContinuousMap.one_apply]
    norm_num

#print axioms flatState

/-- The observable `−1, 0, 1` on `Fin 3`.

CHOSEN: the three values symmetric about `0`, so the mean under `flatState` is `0`. DERIVED: `3` is
the number of points. -/
noncomputable def flatObs : C(Fin 3, ℝ) :=
  ⟨(![-1, 0, 1] : Fin 3 → ℝ), continuous_of_discreteTopology⟩

/-- DERIVED: `6`, `2`, `3` are the weights `1/6, 2/3, 1/6`; `0`, `1`, `2` are the points. -/
theorem flatState_apply (g : C(Fin 3, ℝ)) : flatState g = g 0 / 6 + 2 * g 1 / 3 + g 2 / 6 := rfl

/-- DERIVED: `0` is the mean of `−1, 0, 1` under symmetric weights. -/
theorem flat_mean : flatState flatObs = 0 := by
  rw [flatState_apply]
  norm_num [flatObs, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- DERIVED: `2` is the moment's order; `1/3` is `1/6 + 1/6`, the weight at `±1`. -/
theorem flat_centMom_two : centMom flatState flatObs 2 = 1 / 3 := by
  unfold centMom
  rw [flat_mean, flatState_apply]
  norm_num [flatObs, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- DERIVED: `4` is the moment's order; `1/3` is `1/6 + 1/6`, the weight at `±1`, as the fourth
power of `±1` is `1`. -/
theorem flat_centMom_four : centMom flatState flatObs 4 = 1 / 3 := by
  unfold centMom
  rw [flat_mean, flatState_apply]
  norm_num [flatObs, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- DERIVED: `1/3` is the variance. -/
theorem flat_kappa2 : kappa2 flatState flatObs = 1 / 3 := by
  unfold kappa2
  exact flat_centMom_two

/-- DERIVED: `0` is `(1/3 − 3·(1/3)²)/(1/3)²`. -/
theorem flat_kurtRatio : kurtRatio flatState flatObs = 0 := by
  unfold kurtRatio kappa4 kappa2
  rw [flat_centMom_four, flat_centMom_two]
  norm_num

#print axioms flat_kurtRatio

/-- The constant family `flatState`, `flatObs` does not satisfy `ContinuumNonGaussian`: its
normalised fourth cumulant is `0`.

DERIVED: `0` is `κ₄` and the bound it forces on `c`. -/
theorem flat_not_continuumNonGaussian :
    ¬ ContinuumNonGaussian (fun _ : ℕ => flatState) (fun _ : ℕ => flatObs) := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨i, -, hi⟩ := hev.exists
  have hi' : c ≤ |kurtRatio flatState flatObs| := hi
  rw [flat_kurtRatio, abs_zero] at hi'
  linarith

#print axioms flat_not_continuumNonGaussian

/-- **A variance floor and a non-Gaussian law do not give `ContinuumNonGaussian`.** The constant
family `flatState`, `flatObs` has variance `1/3` at every index, its law is not Gaussian for any mean
and variance (`not_lawIsGaussian_of_variance_pos`), and it fails `ContinuumNonGaussian`.

So a variance floor uniform in the index and a non-Gaussian law at every index leave
`ContinuumNonGaussian` open; along `β → ∞` the lattice supplies less, its proved floor tending to
zero (`plane_floor_tendsto_zero`).

DERIVED: `1/3` is the variance; `0` is the strict lower bound on it. -/
theorem flat_floor_nonGaussian_not_continuum :
    1 / 3 ≤ kappa2 flatState flatObs
      ∧ (∀ (m : ℝ) (v : NNReal), ¬ LawIsGaussian flatState flatObs m v)
      ∧ ¬ ContinuumNonGaussian (fun _ : ℕ => flatState) (fun _ : ℕ => flatObs) := by
  refine ⟨le_of_eq flat_kappa2.symm,
    fun m v => not_lawIsGaussian_of_variance_pos flatState flatObs ?_ m v,
    flat_not_continuumNonGaussian⟩
  rw [← kappa2_eq_variance, flat_kappa2]
  norm_num

#print axioms flat_floor_nonGaussian_not_continuum

end Target

end MassGap.NonGaussian
