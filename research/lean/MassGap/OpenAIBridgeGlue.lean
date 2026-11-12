import Mathlib
import MassGap.OpenAIBridgeCompose
import MassGap.AxisInvG
import MassGap.ShiftInvG

/-!
# MassGap.OpenAIBridgeGlue — the lattice glue between their smeared insertions and the cubic bound

## 1. Symmetries of their law

* `pull` — their configuration relabelled by a permutation of our links, read through
  `OpenAIConfig.configEquiv`;
* `integral_pull` — their law `wilsonLaw g L β μ` is invariant under `pull ρ` for every link
  permutation `ρ` that keeps our Wilson action;
* `integral_pull_axis` — invariance under every axis permutation (`AxisInvG.axisSymmetryG`); at the
  transposition of axes `0` and `3` it moves their time axis `OpenAILink.timeAxis = 3` to the
  transfer direction `0` of `OpenAIBridgeCubic.wilson_slab_conn_cubicG`;
* `integral_pull_shift`, `integral_pull_shift_iter` — invariance under the one-step lattice shift
  along any axis (`ShiftInvG.shiftLinkPerm`) and under its iterates, which places a first slab at
  slice `0`.

## 2. Their law is a probability measure

* `isProbabilityMeasure_wilsonLaw` — for every left-invariant probability measure on `g.image`.

## 3. A complex connected correlation as four real ones

* `realConn`, `norm_le_abs_re_add_abs_im`;
* `norm_conn_le_four` — for bounded measurable `F`, `G` under a finite measure,
  `‖conn(F, G)‖ ≤ |conn(Re F, Re G)| + |conn(Im F, Im G)| + |conn(Re F, Im G)| + |conn(Im F, Re G)|`.

## 4. The smeared insertion and the tensor split

* `lawAt`, `smearIns` — their law at `(N, p)` and the random variable whose expectation is `smear`;
* `appendEquiv`, `smear_eq_integral`, `smear_append` (Fubini for tensor tests), `smear_conn_eq` —
  the smeared connected correlation of `t₁ ⊗ t₂` is the connected correlation of the two smeared
  insertions, when the products of insertions are integrable.

## 5. An observable local in a window of slices is a slab observable

* `WindowLocal`, `recon`, `recon_slab`, `slabOf` — an observable of the cubic torus reading only the
  links of the slices `s, …, s + m` along the transfer direction `0`, the configuration rebuilt
  from slab data, and the slab observable `slabOf l s O = O ∘ recon`;
* `localUpTo_slabOf`, `readAt_slabOf`, `measurable_recon`, `measurable_slabOf` — it is
  `HiddenChain.LocalUpTo m`, reads back as `O` at slice `s`, and is measurable when `O` is.

## 6. The per-torus inequality for complex window-local observables

* `windowLocal_comp`, `reImF`, `reImG`, `pairRHS`;
* `openAI_slab_conn_cubic_complex` — `OpenAIBridgeCompose.openAI_slab_conn_cubic` for continuous
  complex observables local in two windows: the complex connected correlation under their law is at
  most the sum over the four real pairs of `pairRHS`.

## 7. The symmetries as measure-preserving maps of their law

* `pullEquiv`, `pull_apply`, `pull_apply'`, `continuous_pull`, `measurePreserving_pull`, `conn_comp`;
* `transport`, `continuous_transport`, `measurePreserving_transport` — `k` shifts along `0` and the
  transposition of axes `0` and `3`: continuous, law preserving; their time `z₃` sits at transfer
  slice `z₃ + k`.

## 8. Continuous insertions

* `integrable_of_continuous`, `continuous_smearIns`, `smear_conn_eq_of_continuous` — with continuous
  insertions (their `WilsonRegularity`) every integrability hypothesis of section 4 holds.

## 9. The reflection of a slab observable

* `reflConf` — the time reflection of a configuration about a window of slices;
* `revG_slabOf` — `OpenAIBridgeRP.revG` of `slabOf l s O` is `slabOf l s (O ∘ reflConf l s m)`;
* `ReflectionClosed` — the named input: `G = conj (F ∘ reflConf)`;
* `reflO_slabOf_re`, `reflO_slabOf_im` — under it, `reflO` of the slab observable of `Re F`
  (`Im F`) is the slab observable of `Re G` (`−Im G`).

## 10. Their regularity and the window of a smeared insertion

* `offsetSite`, `StencilLocal` — locality on a stencil around a site;
* `WilsonRegularity` (`ChallengeSpec.lean:11–22`, restated), `stencilOf`,
  `stencilLocal_of_regularity` — their regularity, and their `localSupport` as `StencilLocal`;
* `pull_axis_apply`, `pull_shift_apply`, `transport_apply` — the symmetries in their coordinates;
* `TimeWindowLocal`, `windowLocal_of_timeWindowLocal` — locality in a window of transfer slices in
  their coordinates, and its reading as `WindowLocal`;
* `sumIns`, `timeWindowLocal_sumIns`, `smearIns_eq_sumIns`, `timeWindowLocal_smearIns` — a smeared
  insertion of a test supported in the time slab `[T₀, T₁]`, read through `transport k`, is local in
  the slices `lo + K, …, hi + K`, through `place` and `ZMod.valMinAbs`, the support taken up to
  multiples of the period so that a window may cross the seam of the torus;
* `timeWindowLocal_mono`, `pull_shift_iter_apply`, `siteEquiv_join_shift`, `readAt_slabOf_shift` —
  windows are monotone, and a slab observable read at slice `s'` is its observable on the
  configuration shifted by `s'` slices (the slice-shift lemma).

## 11. The reflection of their tokens

* `reflSite`, `reflConfT` — their time reflection of sites and configurations about a plane;
* `TokenReflection`, `ReflectedTest` — the named inputs: the insertion of `Θ v` at the reflected
  site in the reflected configuration is the conjugate of the insertion of `v`, and the reflected
  test at the reflected places is the conjugate of the test;
* `smearIns_reflect`, `smearIns_reflect'` — the reflected smeared insertion is the conjugate;
* `reflConfT_transport`, `siteEquiv_join_refl`, `reflConf_window`,
  `reflectionClosed_of_reflConfT` — their reflection in the transfer frame is `reflConf` on a
  window, so the transported pair is `ReflectionClosed`;
* `timeWindowLocal_reflConfT` — reading on their reflection about the centre of the window
  `0, …, w` keeps the window.

## 12. Their side as the cubic side

* `toSide`, `conn_toSide`, `continuous_toSide`, `timeWindowLocal_toSide` — an observable of their
  side `L = 2l + 2` read on the cubic torus;
* `smear_conn_cubic` — the per-torus inequality on their smeared moments: the smeared connected
  correlation of `t₁ ⊗ t₂` is at most the sum over the four real pairs of `pairRHS` of their
  transported slab observables, for any transport under which the two smeared insertions are local
  in the two windows.

## 13. The slab arithmetic

* `slab_split` — the six split equalities from three inequalities (compose-analysis §2a);
* `gap_ge` — the lattice gap in physical time, `(j + 1) · mesh ≥ τ − δ/2` (compose-analysis §2b).

## 14. The assembly of the cubic form

* `SlabPlacement`, `SlabPlacement.Valid` — a placement of the two slabs on one torus (seed side,
  transport, half-side, half-widths, separation, gap) and its validity at `(N, p)`;
* `slabF`, `slabG`, `momF`, `momG`, `eigOf`, `remD`, `chosenD` — the slab observables of the real
  pairs, their six reflected moments, the eigenpair chosen from `smear_conn_cubic`, the
  excited–excited terms, and the `D` of `CubicForm` at the chosen valid placement;
* `cubicForm_of_inputs` — `OpenAIBridgeCompose.CubicForm` from three inputs: valid placements exist
  eventually, a constant `K₀` bounds the reflected moments of every valid placement (with their
  nonnegativity), and the excited–excited terms of every valid placement vanish relative to
  `‖t₁‖₁ ‖t₂‖₁`;
* `time_bound_of_test`, `stencil_radius`, `placement_exists` — the placements: from the seed with
  `n · mesh ≤ ℓ`, even sides and the order tending to infinity, a valid placement exists
  eventually (compose-analysis §2a, §2b);
* `uniformDecayFrom_of_seed` — the floored (U) at the rate `log 2 / ℓ` from the seed, the sides, the
  order, `K₀` and the vanishing excited–excited terms.

## 15. Reflection positivity of the reflected moments

* `reflMoment_nonneg` — `⟨f₀ (θf)_s⟩` and `⟨(θf)₀ f_s⟩` under their law are nonnegative: each is
  `‖K^{b+1} F K^{a+1}‖²_HS` over the partition function (`OpenAIBridgeRP.hs_sand_eq2`);
* `partF`, `partG`, `reImF_apply`, `reImG_apply`, `part_facts`, `slabOf_part_facts`,
  `moments_nonneg` — the six moments of every valid placement are nonnegative.

## 16. Their volume order tends to infinity

* `tendsto_order_of_converges` — from their `Converges` and one token: a bump test far out in time
  is suitable eventually along the order, and the period is strictly increasing.

## 17. The floored (U) with positivity and the order discharged

* `uniformDecayFrom_of_seed'` — `uniformDecayFrom_of_seed` with `Tendsto order atTop atTop` from
  `Converges` and the sign of the moments from `moments_nonneg`: the input (K₀) is the upper bound
  alone.

## 18. The reflected moments as smeared moments of `(w, Θ ∘ w)`

* `toSide_transport`, `toSide_reflect` — `toSide` commutes with the transport and keeps a
  reflection identity at an integer plane;
* `timeWindowLocal_comp`, `timeWindowLocal_reflConfT'`, `siteEquiv_join_shift'`,
  `readAt_slabOf_shift'` — windows under functions and under the reflection about a window at any
  slice, and the slice-shift lemma for a slab built at a nonzero slice;
* `partFR`, `partGR`, `reflO_slabOf_partF`, `reflO_slabOf_partG` — `reflO` of the slab observable
  of a part is the slab observable of the reflected part of the reflected insertion;
* `pairMom`, `pairMom_toSide`, `SlabPlacement.plane₁`, `SlabPlacement.plane₂` — a smeared moment
  of two observables on their side, read on the cubic side, and the two reflection planes of a
  placement;
* `momF_theta`, `momG_theta` — under `TokenReflection` and `ReflectedTest` at the planes, the six
  reflected moments are `pairMom` readings of `(w, Θ ∘ w)` with `(t, tθ)`;
* `uniformDecayFrom_of_seed''` — the floored (U) from the seed, the sides, the token reflection with
  the existence of reflected tests, the bound `K₀` on those smeared moments, and the vanishing
  excited–excited terms.

## Scope

(U) and `OpenAIBridgeCompose.CubicForm` are stated for time-ordered tensor tests: some `T` bounds
every time of `t₁` and `T + τ` is below every time of `t₂`. The excited–excited input is stated on
`remD` at the chosen placement and eigenpair.

DERIVED: `0` and `3` are the transfer direction and their time axis; `4` the number of real pairs.
-/

namespace MassGap.OpenAIBridgeGlue

open MeasureTheory Real Filter

/-! ## 1. Symmetries of their law -/

section Symm

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- **A link permutation acting on their configurations**: `pull L ρ V` reads `V` through
`configEquiv⁻¹` as one of our configurations, relabels its links by `ρ`, and reads the result back.
On our side it is `LatticeGauge.Symmetry.reindex ρ`.

DERIVED: `4` is the spacetime dimension. -/
noncomputable def pull {g : OpenAIConfig.GaugeGroup}
    (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L)) (V : OpenAIConfig.Configuration g L) :
    OpenAIConfig.Configuration g L :=
  OpenAIConfig.configEquiv L (fun l => (OpenAIConfig.configEquiv L).symm V (ρ l))

/-- `pull` on one of our configurations read through `configEquiv` is the relabelling.

DERIVED: `4` is the spacetime dimension. -/
theorem pull_configEquiv (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L))
    (U : WilsonHypercubic.Link 4 L → g.image) :
    pull L ρ (OpenAIConfig.configEquiv L U) = OpenAIConfig.configEquiv L (fun l => U (ρ l)) := by
  unfold pull
  simp only [MeasurableEquiv.symm_apply_apply]

/-- **Their law is invariant under every action-preserving link permutation.** For their gauge
group `g`, a probability measure `μ` on `g.image`, every coupling `β` and every link permutation
`ρ` of our torus of side `L` that keeps our Wilson action of `g.image`,
`∫ O ∘ pull L ρ ∂(wilsonLaw g L β μ) = ∫ O ∂(wilsonLaw g L β μ)` for every real `O`. Our expectation
at `β/2` is their law at `β` (`OpenAIConfig.expect_eq_integral_openAILaw`), and the relabelling
preserves the product measure and the Boltzmann weight (`LatticeGauge.System.expect_invariant_of_mp`).
No integrability of `O` is used.

DERIVED: `2` halves their coupling; `4` is the spacetime dimension. -/
theorem integral_pull (μ : Measure g.image) [IsProbabilityMeasure μ] (β : ℝ)
    (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L))
    (hρ : ∀ U : WilsonHypercubic.Link 4 L → g.image,
      (GaugeWilson.sysWilsonG g.image 4 L).action (fun l => U (ρ l))
        = (GaugeWilson.sysWilsonG g.image 4 L).action U)
    (O : OpenAIConfig.Configuration g L → ℝ) :
    ∫ V, O (pull L ρ V) ∂(OpenAIConfig.wilsonLaw g L β μ)
      = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L β μ) := by
  have h1 := OpenAIConfig.expect_eq_integral_openAILaw L g (β / 2) μ O
  have h2 := OpenAIConfig.expect_eq_integral_openAILaw L g (β / 2) μ (fun V => O (pull L ρ V))
  rw [show 2 * (β / 2) = β by ring] at h1 h2
  rw [← h1, ← h2]
  simp only [pull_configEquiv]
  exact MassGap.LatticeGauge.System.expect_invariant_of_mp (GaugeWilson.sysWilsonG g.image 4 L) μ
    (β / 2) (fun U => O (OpenAIConfig.configEquiv L U))
    (MassGap.LatticeGauge.Symmetry.reindex (sys := GaugeWilson.sysWilsonG g.image 4 L) ρ)
    (MassGap.LatticeGauge.Symmetry.reindex_measurePreserving
      (sys := GaugeWilson.sysWilsonG g.image 4 L) μ ρ)
    (fun U => by
      unfold MassGap.LatticeGauge.System.boltz
      exact congrArg (fun s => Real.exp (-(β / 2) * s)) (hρ U))

/-- **Their law is invariant under every axis permutation**: `pull` by the link permutation of
`AxisInvG.axisSymmetryG` (direction `a ↦ e a`, site `x ↦ x ∘ e⁻¹`). At `e = swap 0 3` it exchanges
their time axis `OpenAILink.timeAxis = 3` with the transfer direction `0`.

DERIVED: `4` is the spacetime dimension. -/
theorem integral_pull_axis (μ : Measure g.image) [IsProbabilityMeasure μ] (β : ℝ)
    (e : Equiv.Perm (Fin 4)) (O : OpenAIConfig.Configuration g L → ℝ) :
    ∫ V, O (pull L (MassGap.WilsonHypercubic.axisLink e) V) ∂(OpenAIConfig.wilsonLaw g L β μ)
      = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L β μ) :=
  integral_pull g L μ β _
    (fun U => MassGap.LatticeGauge.Symmetry.action_invariant
      (MassGap.AxisInvG.axisSymmetryG g.image (d := 4) (n := L) e) U) O

/-- **Their law is invariant under the one-step shift along any axis** `τ`: `pull` by
`ShiftInvG.shiftLinkPerm τ` (`(a, x) ↦ (a, x + τ̂)`).

DERIVED: `4` is the spacetime dimension. -/
theorem integral_pull_shift [NeZero (L : ℕ)] (μ : Measure g.image) [IsProbabilityMeasure μ]
    (β : ℝ) (τ : Fin 4) (O : OpenAIConfig.Configuration g L → ℝ) :
    ∫ V, O (pull L (MassGap.ShiftInvG.shiftLinkPerm τ) V) ∂(OpenAIConfig.wilsonLaw g L β μ)
      = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L β μ) :=
  integral_pull g L μ β _
    (fun U => by
      have h2 := MassGap.ShiftInvG.shift_action_invariantG (G := g.image) τ U
      rw [← MassGap.ShiftInvG.reindex_shiftLinkPerm] at h2
      exact h2) O

/-- **Their law is invariant under every iterate of the one-step shift**: `k` steps along `τ`.

DERIVED: `4` is the spacetime dimension. -/
theorem integral_pull_shift_iter [NeZero (L : ℕ)] (μ : Measure g.image) [IsProbabilityMeasure μ]
    (β : ℝ) (τ : Fin 4) (k : ℕ) (O : OpenAIConfig.Configuration g L → ℝ) :
    ∫ V, O ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[k] V) ∂(OpenAIConfig.wilsonLaw g L β μ)
      = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L β μ) := by
  induction k generalizing O with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    exact (integral_pull_shift g L μ β τ
      (fun W => O ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[k] W))).trans (ih O)

end Symm

/-! ## 2. Their law is a probability measure -/

section Law

open MassGap.CompactGauge

/-- **Their law is a probability measure.** For every probability measure `μ` on `g.image` that is
left invariant, their law `wilsonLaw g L β μ` has total mass `1`: `μ` is `probHaar g.image`
(`OpenAIBridgeGroups.eq_probHaar_image`), the integral of `1` against their law at `β` is our
expectation of `1` at `β/2` (`OpenAIConfig.expect_eq_integral_openAILaw`), which is `1`
(`GaugeWilson.wilsonSystemG_expect_one`).

DERIVED: `1` is the total mass; `2` halves their coupling; `4` is the spacetime dimension. -/
theorem isProbabilityMeasure_wilsonLaw (g : OpenAIConfig.GaugeGroup) (L : ℕ+) (β : ℝ)
    (μ : Measure g.image) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    IsProbabilityMeasure (OpenAIConfig.wilsonLaw g L β μ) := by
  obtain rfl := MassGap.OpenAIBridgeGroups.eq_probHaar_image g μ
  have h1 := OpenAIConfig.expect_eq_integral_openAILaw L g (β / 2) (probHaar g.image)
    (fun _ => (1 : ℝ))
  rw [show 2 * (β / 2) = β by ring] at h1
  have h2 : (GaugeWilson.sysWilsonG g.image 4 L).expect (probHaar g.image) (β / 2)
      (fun _ => (1 : ℝ)) = 1 :=
    GaugeWilson.wilsonSystemG_expect_one _ _
  have h3 : ∫ _V, (1 : ℝ) ∂(OpenAIConfig.wilsonLaw g L β (probHaar g.image)) = 1 :=
    h1.symm.trans h2
  rw [integral_const, smul_eq_mul, mul_one] at h3
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 h3⟩

end Law

/-! ## 3. A complex connected correlation as four real ones -/

section Split

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- The real connected correlation `∫ a b − ∫ a ∫ b` under `ν`.

DERIVED: no numeral appears in the statement. -/
noncomputable def realConn (a b : X → ℝ) : ℝ :=
  ∫ x, a x * b x ∂ν - (∫ x, a x ∂ν) * ∫ x, b x ∂ν

/-- A complex number is at most the sum of the absolute values of its parts.

DERIVED: no numeral appears in the statement. -/
theorem norm_le_abs_re_add_abs_im (c : ℂ) : ‖c‖ ≤ |c.re| + |c.im| := by
  calc ‖c‖ = ‖(c.re : ℂ) + c.im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(c.re : ℂ)‖ + ‖(c.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |c.re| + |c.im| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]

/-- **The complex connected correlation is at most four real ones.** For bounded a.e. strongly
measurable `F = f₁ + i f₂`, `G = g₁ + i g₂` under a finite measure,
`conn(F, G) = conn(f₁, g₁) − conn(f₂, g₂) + i (conn(f₁, g₂) + conn(f₂, g₁))`, so
`‖conn(F, G)‖ ≤ |conn(f₁, g₁)| + |conn(f₂, g₂)| + |conn(f₁, g₂)| + |conn(f₂, g₁)|`.

DERIVED: no numeral appears in the statement. -/
theorem norm_conn_le_four [IsFiniteMeasure ν] {F G : X → ℂ} (hF : AEStronglyMeasurable F ν)
    (hG : AEStronglyMeasurable G ν) {A B : ℝ} (hFb : ∀ x, ‖F x‖ ≤ A) (hGb : ∀ x, ‖G x‖ ≤ B) :
    ‖∫ x, F x * G x ∂ν - (∫ x, F x ∂ν) * ∫ x, G x ∂ν‖
      ≤ |realConn ν (fun x => (F x).re) (fun x => (G x).re)|
        + |realConn ν (fun x => (F x).im) (fun x => (G x).im)|
        + |realConn ν (fun x => (F x).re) (fun x => (G x).im)|
        + |realConn ν (fun x => (F x).im) (fun x => (G x).re)| := by
  by_cases hX : Nonempty X
  swap
  · haveI := not_nonempty_iff.1 hX
    rw [Measure.eq_zero_of_isEmpty ν]
    simp [realConn]
  obtain ⟨x₀⟩ := hX
  have iF : Integrable F ν := Integrable.of_bound hF A (Filter.Eventually.of_forall hFb)
  have iG : Integrable G ν := Integrable.of_bound hG B (Filter.Eventually.of_forall hGb)
  have hA : 0 ≤ A := (norm_nonneg _).trans (hFb x₀)
  have bnd : ∀ (a b : ℝ) (z w : ℂ), |a| ≤ ‖z‖ → |b| ≤ ‖w‖ → ‖z‖ ≤ A → ‖w‖ ≤ B →
      ‖a * b‖ ≤ A * B := by
    intro a b z w ha hb hz hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ha.trans hz) (hb.trans hw) (abs_nonneg _) hA
  have iFG : Integrable (fun x => F x * G x) ν :=
    Integrable.of_bound (hF.mul hG) (A * B) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_mul (hFb x) (hGb x) (norm_nonneg _) hA)
  have fr := iF.re.aestronglyMeasurable
  have fi := iF.im.aestronglyMeasurable
  have gr := iG.re.aestronglyMeasurable
  have gi := iG.im.aestronglyMeasurable
  have irr : Integrable (fun x => (F x).re * (G x).re) ν :=
    Integrable.of_bound (fr.mul gr) (A * B) (Filter.Eventually.of_forall fun x =>
      bnd _ _ (F x) (G x) (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _) (hFb x) (hGb x))
  have iii : Integrable (fun x => (F x).im * (G x).im) ν :=
    Integrable.of_bound (fi.mul gi) (A * B) (Filter.Eventually.of_forall fun x =>
      bnd _ _ (F x) (G x) (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _) (hFb x) (hGb x))
  have iri : Integrable (fun x => (F x).re * (G x).im) ν :=
    Integrable.of_bound (fr.mul gi) (A * B) (Filter.Eventually.of_forall fun x =>
      bnd _ _ (F x) (G x) (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _) (hFb x) (hGb x))
  have iir : Integrable (fun x => (F x).im * (G x).re) ν :=
    Integrable.of_bound (fi.mul gr) (A * B) (Filter.Eventually.of_forall fun x =>
      bnd _ _ (F x) (G x) (Complex.abs_im_le_norm _) (Complex.abs_re_le_norm _) (hFb x) (hGb x))
  have hre : ∀ {f : X → ℂ}, Integrable f ν → ∫ x, (f x).re ∂ν = (∫ x, f x ∂ν).re :=
    fun hf => integral_re hf
  have him : ∀ {f : X → ℂ}, Integrable f ν → ∫ x, (f x).im ∂ν = (∫ x, f x ∂ν).im :=
    fun hf => integral_im hf
  have eRe : (∫ x, F x * G x ∂ν - (∫ x, F x ∂ν) * ∫ x, G x ∂ν).re
      = realConn ν (fun x => (F x).re) (fun x => (G x).re)
        - realConn ν (fun x => (F x).im) (fun x => (G x).im) := by
    rw [Complex.sub_re, Complex.mul_re, ← hre iFG, ← hre iF, ← hre iG, ← him iF, ← him iG]
    simp only [Complex.mul_re]
    rw [integral_sub irr iii]
    unfold realConn
    ring
  have eIm : (∫ x, F x * G x ∂ν - (∫ x, F x ∂ν) * ∫ x, G x ∂ν).im
      = realConn ν (fun x => (F x).re) (fun x => (G x).im)
        + realConn ν (fun x => (F x).im) (fun x => (G x).re) := by
    rw [Complex.sub_im, Complex.mul_im, ← him iFG, ← hre iF, ← hre iG, ← him iF, ← him iG]
    simp only [Complex.mul_im]
    rw [integral_add iri iir]
    unfold realConn
    ring
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [eRe, eIm]
  have h1 := abs_add_le (realConn ν (fun x => (F x).re) (fun x => (G x).re))
    (-realConn ν (fun x => (F x).im) (fun x => (G x).im))
  have h2 := abs_add_le (realConn ν (fun x => (F x).re) (fun x => (G x).im))
    (realConn ν (fun x => (F x).im) (fun x => (G x).re))
  rw [abs_neg, ← sub_eq_add_neg] at h1
  linarith

end Split

/-! ## 4. The smeared insertion and the tensor split -/

section Smear

open MassGap.OpenAILink

variable {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g)

/-- Their law at spacing index `N` and volume index `p`.

DERIVED: no numeral appears in the statement. -/
noncomputable abbrev lawAt (N p : ℕ) :
    Measure (OpenAIConfig.Configuration g (C.period p * C.denominator N)) :=
  OpenAIConfig.wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar

/-- **Their smeared insertion**: the random variable whose expectation is `smear`,
`F_t(U) = mesh^{4n} Σ_x t(place x) Π_i insertion (w i) (x i) U`.

DERIVED: `4` is the spacetime dimension; `2` the `L²` exponent. -/
noncomputable def smearIns (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n)
    (U : OpenAIConfig.Configuration g (C.period p * C.denominator N)) : ℂ :=
  (C.mesh N : ℂ) ^ (4 * n) * ∑ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N),
    t (WithLp.toLp 2 fun i => C.place N p (x i)) * ∏ i, C.insertion N p (w i) (x i) U

/-- The tuples of `n₁ + n₂` entries are the pairs of tuples of `n₁` and of `n₂` entries, by
`Fin.append`.

DERIVED: no numeral appears in the statement. -/
def appendEquiv (α : Type*) (n₁ n₂ : ℕ) : (Fin n₁ → α) × (Fin n₂ → α) ≃ (Fin (n₁ + n₂) → α) where
  toFun q := Fin.append q.1 q.2
  invFun x := (fun i => x (Fin.castAdd n₂ i), fun j => x (Fin.natAdd n₁ j))
  left_inv q := Prod.ext (funext fun i => Fin.append_left q.1 q.2 i)
    (funext fun j => Fin.append_right q.1 q.2 j)
  right_inv x := by
    funext i
    induction i using Fin.addCases with
    | left i => exact Fin.append_left _ _ i
    | right j => exact Fin.append_right _ _ j

/-- **`smear` is the expectation of the smeared insertion**, when every product of insertions is
integrable against their law.

DERIVED: `4` is the spacetime dimension. -/
theorem smear_eq_integral (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n)
    (hI : ∀ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N),
      Integrable (fun U => ∏ i, C.insertion N p (w i) (x i) U) (lawAt C N p)) :
    C.smear N p w t = ∫ U, smearIns C N p w t U ∂(lawAt C N p) := by
  unfold smearIns WilsonFamily.smear WilsonFamily.finiteMoment
  rw [integral_const_mul, integral_finsetSum _ (fun x _ => (hI x).const_mul _)]
  simp only [integral_const_mul]

/-- **Fubini for tensor tests**: for `t = t₁ ⊗ t₂`, the smeared moment of `w₁ ++ w₂` is the
expectation of the product of the two smeared insertions, when every product of insertions of
`w₁` with insertions of `w₂` is integrable. The site sum over `Fin (n₁ + n₂)` splits by
`appendEquiv`, the test by `t (y) = t₁ (leftPts y) t₂ (rightPts y)`, the product of insertions by
`Fin.prod_univ_add`, and `mesh^{4(n₁+n₂)} = mesh^{4n₁} mesh^{4n₂}`.

DERIVED: `4` is the spacetime dimension; `2` the `L²` exponent. -/
theorem smear_append (N p : ℕ) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token)
    (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (ht : ∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y))
    (hI : ∀ (x₁ : Fin n₁ → OpenAIConfig.Site (C.period p * C.denominator N))
      (x₂ : Fin n₂ → OpenAIConfig.Site (C.period p * C.denominator N)),
      Integrable (fun U => (∏ i, C.insertion N p (w₁ i) (x₁ i) U)
        * ∏ j, C.insertion N p (w₂ j) (x₂ j) U) (lawAt C N p)) :
    C.smear N p (Fin.append w₁ w₂) t
      = ∫ U, smearIns C N p w₁ t₁ U * smearIns C N p w₂ t₂ U ∂(lawAt C N p) := by
  have hprod : ∀ U, smearIns C N p w₁ t₁ U * smearIns C N p w₂ t₂ U
      = ((C.mesh N : ℂ) ^ (4 * n₁) * (C.mesh N : ℂ) ^ (4 * n₂)) *
        ∑ x₁ : Fin n₁ → OpenAIConfig.Site (C.period p * C.denominator N),
          ∑ x₂ : Fin n₂ → OpenAIConfig.Site (C.period p * C.denominator N),
            (t₁ (WithLp.toLp 2 fun i => C.place N p (x₁ i))
              * t₂ (WithLp.toLp 2 fun j => C.place N p (x₂ j)))
            * ((∏ i, C.insertion N p (w₁ i) (x₁ i) U)
              * ∏ j, C.insertion N p (w₂ j) (x₂ j) U) := by
    intro U
    unfold smearIns
    rw [mul_mul_mul_comm, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₂ _ => ?_
    ring
  simp only [hprod]
  rw [integral_const_mul, integral_finsetSum _ (fun x₁ _ => integrable_finsetSum _
    (fun x₂ _ => (hI x₁ x₂).const_mul _))]
  simp only [integral_finsetSum _ (fun x₂ _ => (hI _ x₂).const_mul _), integral_const_mul]
  unfold WilsonFamily.smear WilsonFamily.finiteMoment
  rw [← (appendEquiv (OpenAIConfig.Site (C.period p * C.denominator N)) n₁ n₂).sum_comp,
    Fintype.sum_prod_type, mul_add, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
  have hl : leftPts (WithLp.toLp 2 fun i : Fin (n₁ + n₂) =>
      C.place N p (appendEquiv _ n₁ n₂ (x₁, x₂) i)) = WithLp.toLp 2 fun i => C.place N p (x₁ i) :=
    PiLp.ext fun i => by simp [leftPts, appendEquiv, Fin.append_left]
  have hr : rightPts (WithLp.toLp 2 fun i : Fin (n₁ + n₂) =>
      C.place N p (appendEquiv _ n₁ n₂ (x₁, x₂) i)) = WithLp.toLp 2 fun j => C.place N p (x₂ j) :=
    PiLp.ext fun j => by simp [rightPts, appendEquiv, Fin.append_right]
  rw [ht, hl, hr]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [Fin.prod_univ_add, appendEquiv, Equiv.coe_fn_mk, Fin.append_left, Fin.append_right]

/-- **The smeared connected correlation of a tensor test is the connected correlation of the two
smeared insertions**, when every product of insertions is integrable.

DERIVED: no numeral appears in the statement. -/
theorem smear_conn_eq (N p : ℕ) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token)
    (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (ht : ∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y))
    (hI₁ : ∀ x₁ : Fin n₁ → OpenAIConfig.Site (C.period p * C.denominator N),
      Integrable (fun U => ∏ i, C.insertion N p (w₁ i) (x₁ i) U) (lawAt C N p))
    (hI₂ : ∀ x₂ : Fin n₂ → OpenAIConfig.Site (C.period p * C.denominator N),
      Integrable (fun U => ∏ j, C.insertion N p (w₂ j) (x₂ j) U) (lawAt C N p))
    (hI : ∀ (x₁ : Fin n₁ → OpenAIConfig.Site (C.period p * C.denominator N))
      (x₂ : Fin n₂ → OpenAIConfig.Site (C.period p * C.denominator N)),
      Integrable (fun U => (∏ i, C.insertion N p (w₁ i) (x₁ i) U)
        * ∏ j, C.insertion N p (w₂ j) (x₂ j) U) (lawAt C N p)) :
    C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂
      = ∫ U, smearIns C N p w₁ t₁ U * smearIns C N p w₂ t₂ U ∂(lawAt C N p)
        - (∫ U, smearIns C N p w₁ t₁ U ∂(lawAt C N p))
          * ∫ U, smearIns C N p w₂ t₂ U ∂(lawAt C N p) := by
  rw [smear_append C N p w₁ w₂ t t₁ t₂ ht hI, smear_eq_integral C N p w₁ t₁ hI₁,
    smear_eq_integral C N p w₂ t₂ hI₂]

end Smear

/-! ## 5. An observable local in a window of slices is a slab observable -/

section Slab

open MassGap.RectWilson MassGap.HiddenChain MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeCompose

variable {g : OpenAIConfig.GaugeGroup} (l : ℕ)

/-- **Locality in a window of slices along the transfer direction `0`**: `O` reads only the links
`(a, x)` of the cubic torus of side `2l + 2` with `s ≤ x₀ ≤ s + m`, the time links (`a = 0`) only
for `x₀ < s + m`.

DERIVED: `0` is the transfer direction; `1` the offsets of the side. -/
def WindowLocal {β : Type*} (s m : ℕ) (O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → β) :
    Prop :=
  ∀ U U' : RLink (TorusChain.Lc (l + l + 1)) → g.image,
    (∀ (a : Fin 4) (x : RSite (TorusChain.Lc (l + l + 1))), s ≤ (x 0 : ℕ) → (x 0 : ℕ) ≤ s + m →
      (a ≠ 0 ∨ (x 0 : ℕ) < s + m) → U (a, x) = U' (a, x)) → O U = O U'

/-- **A configuration rebuilt from slab data** starting at slice `s`: the spatial link `(a, x)`,
`a ≠ 0`, is entry `x₀ − s` of the slices `Vs`, the time link `(0, x)` entry `x₀ − s` of the time
links `As`, at the transverse site of `x`.

DERIVED: `0` is the transfer direction; `1` the offsets of the side. -/
def recon (s : ℕ) (Vs : ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
    (As : ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) :
    RLink (TorusChain.Lc (l + l + 1)) → g.image :=
  fun e => if h : e.1 = 0 then As ((e.2 0 : ℕ) - s) (perp _ 0 e.2)
    else Vs ((e.2 0 : ℕ) - s) (⟨e.1, h⟩, perp _ 0 e.2)

/-- **Rebuilding from the slabs of a configuration returns it** on every link at or past slice `s`.

DERIVED: `0` is the transfer direction; `1` the offsets of the side. -/
theorem recon_slab (s : ℕ) (U : RLink (TorusChain.Lc (l + l + 1)) → g.image) (a : Fin 4)
    (x : RSite (TorusChain.Lc (l + l + 1))) (hs : s ≤ (x 0 : ℕ)) :
    recon l s (slabV (TorusChain.Lc (l + l + 1)) 0 s U) (slabA (TorusChain.Lc (l + l + 1)) 0 s U)
      (a, x) = U (a, x) := by
  have hlt : s + ((x 0 : ℕ) - s) < TorusChain.Lc (l + l + 1) 0 := by
    have := (x 0).isLt
    simp only [TorusChain.Lc] at this ⊢
    omega
  have hj : join (TorusChain.Lc (l + l + 1)) 0 ⟨s + ((x 0 : ℕ) - s), hlt⟩
      (perp (TorusChain.Lc (l + l + 1)) 0 x) = x := by
    have : (⟨s + ((x 0 : ℕ) - s), hlt⟩ : Fin (TorusChain.Lc (l + l + 1) 0)) = x 0 :=
      Fin.ext (by simp only; omega)
    rw [this, join_perp]
  by_cases ha : a = 0
  · subst ha
    dsimp only [recon]
    rw [dif_pos rfl]
    simp only [slabA, dif_pos hlt]
    rw [hj]
  · dsimp only [recon]
    rw [dif_neg ha]
    simp only [slabV, dif_pos hlt]
    rw [hj]

/-- **The slab observable of an observable of the cubic torus**, read from slice `s`.

DERIVED: no numeral appears in the statement. -/
def slabOf (s : ℕ) (O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → ℝ) : SlabObs g l :=
  fun Vs As => O (recon l s Vs As)

/-- **A window-local observable gives a slab observable of the window's width.**

DERIVED: `0` is the transfer direction. -/
theorem localUpTo_slabOf {s m : ℕ} {O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → ℝ}
    (hO : WindowLocal l s m O) : LocalUpTo m (slabOf l s O) := by
  intro V V' A A' hV hA
  apply hO
  intro a x hs hx hor
  by_cases ha : a = 0
  · subst ha
    have h' : (x 0 : ℕ) < s + m := hor.resolve_left (fun h => h rfl)
    dsimp only [recon]
    rw [dif_pos rfl, dif_pos rfl, hA ((x 0 : ℕ) - s) (by omega)]
  · dsimp only [recon]
    rw [dif_neg ha, dif_neg ha, hV ((x 0 : ℕ) - s) (by omega)]

/-- **Reading the slab observable at slice `s` returns the observable**: for an observable `O` of
their configurations whose pullback through `configEquiv` is local in the window from slice `s`,
`readAt l (slabOf l s (O ∘ configEquiv)) s = O`.

DERIVED: `1` is the offset of the side. -/
theorem readAt_slabOf {s m : ℕ} (O : OpenAIConfig.Configuration g (sideP l) → ℝ)
    (hO : WindowLocal l s m (fun U => O (OpenAIConfig.configEquiv (sideP l) U)))
    (V : OpenAIConfig.Configuration g (sideP l)) :
    readAt l (slabOf l s (fun U => O (OpenAIConfig.configEquiv (sideP l) U))) s V = O V := by
  calc readAt l (slabOf l s (fun U => O (OpenAIConfig.configEquiv (sideP l) U))) s V
      = O (OpenAIConfig.configEquiv (sideP l)
          (recon l s
            (slabV (TorusChain.Lc (l + l + 1)) 0 s ((OpenAIConfig.configEquiv (sideP l)).symm V))
            (slabA (TorusChain.Lc (l + l + 1)) 0 s ((OpenAIConfig.configEquiv (sideP l)).symm V)))) :=
        rfl
    _ = O (OpenAIConfig.configEquiv (sideP l) ((OpenAIConfig.configEquiv (sideP l)).symm V)) :=
        hO _ _ (fun a x hs _ _ => recon_slab l s _ a x hs)
    _ = O V := by rw [MeasurableEquiv.apply_symm_apply]

/-- `recon l s` is measurable in the slab data.

DERIVED: `0` is the transfer direction. -/
theorem measurable_recon (s : ℕ) :
    Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
      × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) => recon l s r.1 r.2) := by
  refine measurable_pi_lambda _ fun e => ?_
  by_cases h : e.1 = 0
  · simp only [recon, dif_pos h]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  · simp only [recon, dif_neg h]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)

/-- A measurable observable gives a measurable slab observable.

DERIVED: no numeral appears in the statement. -/
theorem measurable_slabOf (s : ℕ) {O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → ℝ}
    (hO : Measurable O) :
    Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
      × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) => slabOf l s O r.1 r.2) :=
  hO.comp (measurable_recon l s)

end Slab

/-! ## 6. The per-torus inequality for complex window-local observables -/

section Complex

open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic
  MassGap.OpenAIBridgeCompose MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.CompactGauge MassGap.HiddenChain MassGap.OpenAIBridgeGroups

/-- Window locality passes to every function of the observable.

DERIVED: no numeral appears in the statement. -/
theorem windowLocal_comp {g : OpenAIConfig.GaugeGroup} {l s m : ℕ} {β γ : Type*}
    {O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → β} (h : WindowLocal l s m O)
    (k : β → γ) : WindowLocal l s m (fun U => k (O U)) :=
  fun U U' hU => congrArg k (h U U' hU)

/-- The first factors of the four real pairs of `F`: `Re F`, `Im F`, `Re F`, `Im F`.

DERIVED: `4` is the number of pairs. -/
def reImF {X : Type*} (F : X → ℂ) : Fin 4 → X → ℝ :=
  ![fun x => (F x).re, fun x => (F x).im, fun x => (F x).re, fun x => (F x).im]

/-- The second factors of the four real pairs of `G`: `Re G`, `Im G`, `Im G`, `Re G`.

DERIVED: `4` is the number of pairs. -/
def reImG {X : Type*} (G : X → ℂ) : Fin 4 → X → ℝ :=
  ![fun x => (G x).re, fun x => (G x).im, fun x => (G x).im, fun x => (G x).re]

/-- **The right side of the cubic bound for one pair of slab observables** `f`, `h` on their law
at side `2l + 2`: `cubicRHS` at the excited weight of `(φ, c)`, the six reflected moments of their
law at the separations `2a + 2`, `2a_F + 2`, `2a_G + 2`, and the excited–excited term
`√(remW_f remW_h)`; the right side of `OpenAIBridgeCompose.openAI_slab_conn_cubic`.

DERIVED: `2` doubles the widths and separations; `0` the first slice. -/
noncomputable def pairRHS (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image) (l : ℕ) (β c : ℝ)
    (φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ) (n j j' v v' a aF bF aG bG : ℕ)
    (f h : SlabObs g l) : ℝ :=
  cubicRHS n j j' (excW g l β c φ)
    (∫ V, readAt l f 0 V * readAt l (reflO l v f) (v + v + 2 + (a + a + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
    (∫ V, readAt l (reflO l v' h) 0 V * readAt l h (v' + v' + 2 + (a + a + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
    (∫ V, readAt l (reflO l v f) 0 V * readAt l f (v + v + 2 + (a + a + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
    (∫ V, readAt l h 0 V * readAt l (reflO l v' h) (v' + v' + 2 + (a + a + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
    (√(remW g l β c φ v f aF bF * remW g l β c φ v' h aG bG))
    (∫ V, readAt l f 0 V * readAt l (reflO l v f) (v + v + 2 + (aF + aF + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
    (∫ V, readAt l h 0 V * readAt l (reflO l v' h) (v' + v' + 2 + (aG + aG + 2)) V
      ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))

set_option maxHeartbeats 1600000 in
/-- **The per-torus inequality for complex window-local observables on their law.** Under the
hypotheses of `OpenAIBridgeCompose.openAI_slab_conn_cubic` (seed at `β/2` on an even side `n ≥ 2`,
torus side `2l + 2 ≥ 8n`) there is one eigenpair `(φ, c)` with excited weight
`0 ≤ σ₀ ≤ (1/2)^⌊(l+1)/n⌋` such that for continuous complex observables `F`, `G` of their
configurations, `F` local in the slices `0, …, 2v + 2` and `G` in the slices from
`2v + 2 + p + 1`, `p = 2a + j + 2`, along the transfer direction `0` (read through
`configEquiv⁻¹`), the complex connected correlation under their law is at most the sum over the four
real pairs `(Re F, Re G)`, `(Im F, Im G)`, `(Re F, Im G)`, `(Im F, Re G)` of `pairRHS` of their slab
observables (`slabOf`). Each pair is `openAI_slab_conn_cubic` (bounded by compactness, measurable
by continuity, `LocalUpTo` by `localUpTo_slabOf`, read back by `readAt_slabOf`), and the four add up
by `norm_conn_le_four` on their law, a probability measure (`isProbabilityMeasure_wilsonLaw`).

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `8` the side condition; `4` the number of
pairs and the spacetime dimension; `2` the halving of the coupling, the doubled side, widths and
separations; `1/2` the contraction; `0` the first slice and the transfer direction; `1` the
offsets. -/
theorem openAI_slab_conn_cubic_complex (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure] {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n)
    (h0 : 16 * Real.log (ZRG g.image (fun _ => n) (β / 2))
      - Real.log (ZRG g.image (fun _ => 2 * n) (β / 2)) ≤ 1 / 1000)
    (l : ℕ) (hL : 8 * n ≤ l + l + 2) :
    ∃ φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = 1 ∧
      (∀ z, ∫ y, (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2)) z y * φ y
        ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = c * φ z) ∧
      0 ≤ excW g l β c φ ∧ excW g l β c φ ≤ (1 / 2) ^ ((l + 1) / n) ∧
      ∀ (F G : OpenAIConfig.Configuration g (sideP l) → ℂ), Continuous F → Continuous G →
      ∀ v v' a j j' aF bF aG bG cF cG : ℕ,
      a + j + a + 2 = aF + bG + 1 → a + j' + a + 2 = aG + bF + 1 →
      v + v + 2 + aF + bF + 1 = l → v' + v' + 2 + aG + bG + 1 = l →
      v + v + 2 + a + cF + 1 = l → v' + v' + 2 + a + cG + 1 = l →
      WindowLocal l 0 (v + v + 2) (fun U => F (OpenAIConfig.configEquiv (sideP l) U)) →
      WindowLocal l (v + v + 2 + (a + j + a + 2 + 1)) (v' + v' + 2)
        (fun U => G (OpenAIConfig.configEquiv (sideP l) U)) →
      ‖∫ V, F V * G V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)
        - (∫ V, F V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
          * ∫ V, G V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)‖
        ≤ ∑ i : Fin 4, pairRHS g μ l β c φ n j j' v v' a aF bF aG bG
            (slabOf l 0 (fun U => reImF F i (OpenAIConfig.configEquiv (sideP l) U)))
            (slabOf l (v + v + 2 + (a + j + a + 2 + 1))
              (fun U => reImG G i (OpenAIConfig.configEquiv (sideP l) U))) := by
  obtain ⟨φ, c, hc0, hφ1, heig, hσ0, hσ, hb⟩ := openAI_slab_conn_cubic g μ hβ hn he h0 l hL
  refine ⟨φ, c, hc0, hφ1, heig, hσ0, hσ,
    fun F G hF hG v v' a j j' aF bF aG bG cF cG h1 h2 h3 h4 h5 h6 hFw hGw => ?_⟩
  haveI := isProbabilityMeasure_wilsonLaw g (sideP l) β μ
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  have pair : ∀ Of Og : OpenAIConfig.Configuration g (sideP l) → ℝ, Continuous Of →
      Continuous Og → (∀ V, |Of V| ≤ A) → (∀ V, |Og V| ≤ B) →
      WindowLocal l 0 (v + v + 2) (fun U => Of (OpenAIConfig.configEquiv (sideP l) U)) →
      WindowLocal l (v + v + 2 + (a + j + a + 2 + 1)) (v' + v' + 2)
        (fun U => Og (OpenAIConfig.configEquiv (sideP l) U)) →
      |realConn (OpenAIConfig.wilsonLaw g (sideP l) β μ) Of Og|
        ≤ pairRHS g μ l β c φ n j j' v v' a aF bF aG bG
            (slabOf l 0 (fun U => Of (OpenAIConfig.configEquiv (sideP l) U)))
            (slabOf l (v + v + 2 + (a + j + a + 2 + 1))
              (fun U => Og (OpenAIConfig.configEquiv (sideP l) U))) := by
    intro Of Og hOf hOg hfA hgB hfw hgw
    have key := hb (slabOf l 0 (fun U => Of (OpenAIConfig.configEquiv (sideP l) U)))
      (slabOf l (v + v + 2 + (a + j + a + 2 + 1))
        (fun U => Og (OpenAIConfig.configEquiv (sideP l) U)))
      (measurable_slabOf l 0 (hOf.measurable.comp (OpenAIConfig.configEquiv (sideP l)).measurable))
      (measurable_slabOf l _ (hOg.measurable.comp (OpenAIConfig.configEquiv (sideP l)).measurable))
      A B (fun _ _ => hfA _) (fun _ _ => hgB _) v v'
      (localUpTo_slabOf l hfw) (localUpTo_slabOf l hgw) a j j' aF bF aG bG cF cG h1 h2 h3 h4 h5 h6
    have e : realConn (OpenAIConfig.wilsonLaw g (sideP l) β μ) Of Og
        = ∫ V, readAt l (slabOf l 0 (fun U => Of (OpenAIConfig.configEquiv (sideP l) U))) 0 V
            * readAt l (slabOf l (v + v + 2 + (a + j + a + 2 + 1))
                (fun U => Og (OpenAIConfig.configEquiv (sideP l) U)))
                (v + v + 2 + (a + j + a + 2 + 1)) V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)
          - (∫ V, readAt l (slabOf l 0 (fun U => Of (OpenAIConfig.configEquiv (sideP l) U))) 0 V
              ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
            * ∫ V, readAt l (slabOf l (v + v + 2 + (a + j + a + 2 + 1))
                (fun U => Og (OpenAIConfig.configEquiv (sideP l) U)))
                (v + v + 2 + (a + j + a + 2 + 1)) V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) := by
      unfold realConn
      simp only [readAt_slabOf l Of hfw, readAt_slabOf l Og hgw]
    rw [e]
    exact key
  have four := norm_conn_le_four (OpenAIConfig.wilsonLaw g (sideP l) β μ) hF.aestronglyMeasurable
    hG.aestronglyMeasurable (fun V => hA V (Set.mem_univ _)) (fun V => hB V (Set.mem_univ _))
  refine four.trans ?_
  rw [Fin.sum_univ_four]
  have fre : ∀ V, |(F V).re| ≤ A := fun V => (Complex.abs_re_le_norm _).trans (hA V (Set.mem_univ _))
  have fim : ∀ V, |(F V).im| ≤ A := fun V => (Complex.abs_im_le_norm _).trans (hA V (Set.mem_univ _))
  have gre : ∀ V, |(G V).re| ≤ B := fun V => (Complex.abs_re_le_norm _).trans (hB V (Set.mem_univ _))
  have gim : ∀ V, |(G V).im| ≤ B := fun V => (Complex.abs_im_le_norm _).trans (hB V (Set.mem_univ _))
  have cFr := Complex.continuous_re.comp hF
  have cFi := Complex.continuous_im.comp hF
  have cGr := Complex.continuous_re.comp hG
  have cGi := Complex.continuous_im.comp hG
  exact add_le_add (add_le_add (add_le_add
    (pair _ _ cFr cGr fre gre (windowLocal_comp hFw Complex.re) (windowLocal_comp hGw Complex.re))
    (pair _ _ cFi cGi fim gim (windowLocal_comp hFw Complex.im) (windowLocal_comp hGw Complex.im)))
    (pair _ _ cFr cGi fre gim (windowLocal_comp hFw Complex.re) (windowLocal_comp hGw Complex.im)))
    (pair _ _ cFi cGr fim gre (windowLocal_comp hFw Complex.im) (windowLocal_comp hGw Complex.re))

end Complex

/-! ## 7. The symmetries as measure-preserving maps of their law -/

section Transport

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- `pull L ρ` as a measurable equivalence of their configurations.

DERIVED: `4` is the spacetime dimension. -/
noncomputable def pullEquiv (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L)) :
    OpenAIConfig.Configuration g L ≃ᵐ OpenAIConfig.Configuration g L :=
  ((OpenAIConfig.configEquiv L).symm.trans
    (MassGap.LatticeGauge.Symmetry.reindex (sys := GaugeWilson.sysWilsonG g.image 4 L) ρ)).trans
    (OpenAIConfig.configEquiv L)

/-- `pullEquiv` is `pull`.

DERIVED: `4` is the spacetime dimension. -/
theorem pullEquiv_apply (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L))
    (V : OpenAIConfig.Configuration g L) : pullEquiv g L ρ V = pull L ρ V := rfl

/-- **`pull` in their coordinates**: at their pair `(siteEquiv x, a)` it reads `V` at the pair of
the link `ρ (a, x)`.

DERIVED: `4` is the spacetime dimension. -/
theorem pull_apply (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L)) (V : OpenAIConfig.Configuration g L)
    (a : Fin 4) (x : WilsonHypercubic.Site 4 L) :
    pull L ρ V (OpenAIConfig.siteEquiv L x, a)
      = V (OpenAIConfig.siteEquiv L (ρ (a, x)).2, (ρ (a, x)).1) := by
  have h := OpenAIConfig.configEquiv_apply L ((OpenAIConfig.configEquiv L).symm V)
    (ρ (a, x)).1 (ρ (a, x)).2
  rw [MeasurableEquiv.apply_symm_apply] at h
  unfold pull
  rw [OpenAIConfig.configEquiv_apply]
  exact h.symm

/-- **`pull` is a relabelling of their coordinates**: `pull L ρ V k = V (σ k)` with
`σ = linkEquiv ∘ ρ ∘ linkEquiv⁻¹`.

DERIVED: `4` is the spacetime dimension. -/
theorem pull_apply' (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L))
    (V : OpenAIConfig.Configuration g L) (k : OpenAIConfig.Site L × OpenAIConfig.Axis) :
    pull L ρ V k
      = V (OpenAIConfig.linkEquiv L (ρ ((OpenAIConfig.linkEquiv L).symm k))) := by
  have h1 : k = (OpenAIConfig.siteEquiv L ((OpenAIConfig.linkEquiv L).symm k).2,
      ((OpenAIConfig.linkEquiv L).symm k).1) := by
    simp [OpenAIConfig.linkEquiv]
  conv_lhs => rw [h1]
  rw [pull_apply]
  rfl

/-- `pull L ρ` is continuous.

DERIVED: `4` is the spacetime dimension. -/
theorem continuous_pull (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L)) :
    Continuous (pull (g := g) L ρ) := by
  refine continuous_pi fun k => ?_
  simp only [pull_apply']
  exact continuous_apply _

/-- **`pull` preserves their law** for every action-preserving link permutation, when the single-link
measure is a left-invariant probability measure: the integral identity `integral_pull` at the
indicator of each measurable set, their law being a probability measure.

DERIVED: `4` is the spacetime dimension; `1` the value of the indicator. -/
theorem measurePreserving_pull (μ : Measure g.image) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (β : ℝ) (ρ : Equiv.Perm (WilsonHypercubic.Link 4 L))
    (hρ : ∀ U : WilsonHypercubic.Link 4 L → g.image,
      (GaugeWilson.sysWilsonG g.image 4 L).action (fun l => U (ρ l))
        = (GaugeWilson.sysWilsonG g.image 4 L).action U) :
    MeasurePreserving (pullEquiv g L ρ) (OpenAIConfig.wilsonLaw g L β μ)
      (OpenAIConfig.wilsonLaw g L β μ) := by
  haveI := isProbabilityMeasure_wilsonLaw g L β μ
  refine ⟨(pullEquiv g L ρ).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (pullEquiv g L ρ).measurable hs]
  have h := integral_pull g L μ β ρ hρ (s.indicator 1)
  have hpre : MeasurableSet (pullEquiv g L ρ ⁻¹' s) := (pullEquiv g L ρ).measurable hs
  have e : (fun V => s.indicator (1 : OpenAIConfig.Configuration g L → ℝ) (pull L ρ V))
      = (pullEquiv g L ρ ⁻¹' s).indicator 1 := by
    funext V
    by_cases hV : pull L ρ V ∈ s
    · rw [Set.indicator_of_mem hV,
        Set.indicator_of_mem (show V ∈ pullEquiv g L ρ ⁻¹' s from hV)]
      rfl
    · rw [Set.indicator_of_notMem hV,
        Set.indicator_of_notMem (show V ∉ pullEquiv g L ρ ⁻¹' s from hV)]
  rw [e, integral_indicator_one hpre, integral_indicator_one hs, measureReal_def,
    measureReal_def] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

/-- **The connected correlation is invariant under a measure-preserving map**: for every measurable
equivalence `T` preserving a measure `ν`, `conn(F ∘ T, G ∘ T) = conn(F, G)` for complex `F`, `G`.

DERIVED: no numeral appears in the statement. -/
theorem conn_comp {X : Type*} [MeasurableSpace X] {ν : Measure X} (T : X ≃ᵐ X)
    (hT : MeasurePreserving T ν ν) (F G : X → ℂ) :
    ∫ x, F (T x) * G (T x) ∂ν - (∫ x, F (T x) ∂ν) * ∫ x, G (T x) ∂ν
      = ∫ x, F x * G x ∂ν - (∫ x, F x ∂ν) * ∫ x, G x ∂ν := by
  rw [hT.integral_comp' (fun x => F x * G x), hT.integral_comp' F, hT.integral_comp' G]

/-- **The transport to the transfer frame**: `k` one-step shifts along axis `0`, then the
transposition of axes `0` and `3`. Read through it, their time coordinate `z₃`
(`OpenAILink.timeAxis = 3`) sits at slice `z₃ + k` of the transfer direction `0`
(`transport_apply`), so `k` moves a slab to slice `0`.

DERIVED: `0` is the transfer direction; `3` their time axis; `4` the spacetime dimension; `1` one
more step. -/
noncomputable def transport [NeZero (L : ℕ)] :
    ℕ → (OpenAIConfig.Configuration g L ≃ᵐ OpenAIConfig.Configuration g L)
  | 0 => pullEquiv g L (MassGap.WilsonHypercubic.axisLink (Equiv.swap 0 3))
  | k + 1 => (pullEquiv g L (MassGap.ShiftInvG.shiftLinkPerm 0)).trans (transport k)

/-- **The transport is continuous.**

DERIVED: `0` is the transfer direction; `1` one more step. -/
theorem continuous_transport [NeZero (L : ℕ)] (k : ℕ) : Continuous (transport g L k) := by
  induction k with
  | zero => exact continuous_pull g L _
  | succ k ih => exact ih.comp (continuous_pull g L _)

/-- **The transport preserves their law** (`measurePreserving_pull` at `AxisInvG.axisSymmetryG`
and at `ShiftInvG.shiftLinkPerm`).

DERIVED: `0` is the transfer direction; `3` their time axis; `4` the spacetime dimension; `1` one
more step. -/
theorem measurePreserving_transport [NeZero (L : ℕ)] (μ : Measure g.image) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (β : ℝ) (k : ℕ) :
    MeasurePreserving (transport g L k) (OpenAIConfig.wilsonLaw g L β μ)
      (OpenAIConfig.wilsonLaw g L β μ) := by
  induction k with
  | zero =>
    exact measurePreserving_pull g L μ β _ fun U =>
      MassGap.LatticeGauge.Symmetry.action_invariant
        (MassGap.AxisInvG.axisSymmetryG g.image (d := 4) (n := L) (Equiv.swap 0 3)) U
  | succ k ih =>
    refine ih.comp (measurePreserving_pull g L μ β _ fun U => ?_)
    have h2 := MassGap.ShiftInvG.shift_action_invariantG (G := g.image) (0 : Fin 4) U
    rw [← MassGap.ShiftInvG.reindex_shiftLinkPerm] at h2
    exact h2

end Transport

/-! ## 8. Continuous insertions: integrability and the smeared connected correlation -/

section Continuous

open MassGap.OpenAILink

variable {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g)

/-- **Products of continuous insertions are integrable against their law**: continuous on the
compact configuration space, hence bounded and measurable, against a probability measure
(`isProbabilityMeasure_wilsonLaw`).

DERIVED: no numeral appears in the statement. -/
theorem integrable_of_continuous (N p : ℕ)
    {F : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ} (hF : Continuous F) :
    Integrable F (lawAt C N p) := by
  haveI := C.probability
  haveI := C.invariantHaar
  haveI := isProbabilityMeasure_wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound hF.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun U => hM U (Set.mem_univ _))

/-- **The smeared insertion of continuous insertions is continuous.**

DERIVED: no numeral appears in the statement. -/
theorem continuous_smearIns (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ}
    (w : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n) :
    Continuous (smearIns C N p w t) :=
  continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_finsetProd _ fun i _ => hc (w i) (x i)))

/-- **The smeared connected correlation of continuous insertions** is the connected correlation of
the two smeared insertions under their law (`smear_conn_eq`, every product integrable by
`integrable_of_continuous`).

DERIVED: no numeral appears in the statement. -/
theorem smear_conn_eq_of_continuous (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x))
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token)
    (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (ht : ∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) :
    C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂
      = ∫ U, smearIns C N p w₁ t₁ U * smearIns C N p w₂ t₂ U ∂(lawAt C N p)
        - (∫ U, smearIns C N p w₁ t₁ U ∂(lawAt C N p))
          * ∫ U, smearIns C N p w₂ t₂ U ∂(lawAt C N p) :=
  smear_conn_eq C N p w₁ w₂ t t₁ t₂ ht
    (fun x₁ => integrable_of_continuous C N p
      (continuous_finsetProd _ fun i _ => hc (w₁ i) (x₁ i)))
    (fun x₂ => integrable_of_continuous C N p
      (continuous_finsetProd _ fun j _ => hc (w₂ j) (x₂ j)))
    (fun x₁ x₂ => integrable_of_continuous C N p
      ((continuous_finsetProd _ fun i _ => hc (w₁ i) (x₁ i)).mul
        (continuous_finsetProd _ fun j _ => hc (w₂ j) (x₂ j))))

end Continuous

/-! ## 9. The reflection of a slab observable -/

section Reflect

open MassGap.RectWilson MassGap.HiddenChain MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCompose

variable {g : OpenAIConfig.GaugeGroup} (l : ℕ)

/-- **The time reflection of a configuration about the window of slices `s, …, s + m + 1`** along the
transfer direction `0`: the spatial link at slice `s + i` is the one at slice `s + m + 1 − i`, the
time link from slice `s + i` is the inverse of the one from slice `s + m − i`, at the same
transverse site (slices are read modulo the side `2l + 2`).

DERIVED: `0` is the transfer direction; `1` the offsets of the side and of the window. -/
def reflConf (s m : ℕ) (U : RLink (TorusChain.Lc (l + l + 1)) → g.image) :
    RLink (TorusChain.Lc (l + l + 1)) → g.image :=
  fun e => if e.1 = 0 then
      (U (0, join (TorusChain.Lc (l + l + 1)) 0
        ⟨(s + (m - ((e.2 0 : ℕ) - s))) % (l + l + 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
        (perp _ 0 e.2)))⁻¹
    else U (e.1, join (TorusChain.Lc (l + l + 1)) 0
        ⟨(s + (m + 1 - ((e.2 0 : ℕ) - s))) % (l + l + 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
        (perp _ 0 e.2))

/-- **`revG` of a slab observable is the slab observable of the reflected configuration.** For an
observable `O` local in the window of slices `s, …, s + m + 1` inside the torus, the reflection
`revG` (time links inverted) of `slabOf l s O` over `m + 1` steps is `slabOf l s (O ∘ reflConf l s m)`.

DERIVED: `0` is the transfer direction; `1` the offsets of the side and of the window; `2` the
doubled half-side. -/
theorem revG_slabOf (s m : ℕ) (hL : s + m + 1 < l + l + 2)
    {O : (RLink (TorusChain.Lc (l + l + 1)) → g.image) → ℝ} (hO : WindowLocal l s (m + 1) O)
    (Vs : ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
    (As : ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) :
    revG (MeasurableEquiv.piCongrRight
        (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv g.image)) m
        (slabOf l s O) Vs As
      = slabOf l s (fun U => O (reflConf l s m U)) Vs As := by
  unfold revG slabOf
  apply hO
  intro a x hs hx hor
  by_cases ha : a = 0
  · subst ha
    have hlt : (x 0 : ℕ) < s + (m + 1) := hor.resolve_left (fun h => h rfl)
    have hle : (x 0 : ℕ) - s ≤ m := by omega
    have hmod : (s + (m - ((x 0 : ℕ) - s))) % (l + l + 1 + 1) = s + (m - ((x 0 : ℕ) - s)) :=
      Nat.mod_eq_of_lt (by omega)
    simp only [recon, reflConf, dif_pos, join_self, perp_join, hmod, add_tsub_cancel_left,
      if_pos hle]
    rfl
  · have hmod : (s + (m + 1 - ((x 0 : ℕ) - s))) % (l + l + 1 + 1)
        = s + (m + 1 - ((x 0 : ℕ) - s)) :=
      Nat.mod_eq_of_lt (by omega)
    simp only [recon, reflConf, dif_neg ha, if_neg ha, join_self, perp_join, hmod,
      add_tsub_cancel_left]

/-- **Named input: reflection closure of a pair of smeared insertions.** `G` is the reflection of
`F` about the window `s, …, s + m + 1`: `G = conj (F ∘ reflConf l s m)` on the cubic torus, read
through `configEquiv`. For their tokens it is the statement that the smeared insertion of `Θ ∘ w`
against the reflected test is the conjugate of the reflected smeared insertion of `w`, at the
transported frame (`transport`).

DERIVED: `1` is the offset of the side. -/
def ReflectionClosed (s m : ℕ) (F G : OpenAIConfig.Configuration g (sideP l) → ℂ) : Prop :=
  ∀ U : RLink (TorusChain.Lc (l + l + 1)) → g.image,
    G (OpenAIConfig.configEquiv (sideP l) U)
      = (starRingEnd ℂ) (F (OpenAIConfig.configEquiv (sideP l) (reflConf l s m U)))

/-- **The reflected real part is the real part of the reflected insertion.** Under
`ReflectionClosed l s (2v + 1) F G`, with `F` local in the window of width `2v + 2` from slice `s`
inside the torus, `reflO l v` of the slab observable of `Re F` is the slab observable of `Re G`.

DERIVED: `2` doubles the width; `1` the offsets. -/
theorem reflO_slabOf_re (s v : ℕ) (hL : s + (v + v + 1) + 1 < l + l + 2)
    {F G : OpenAIConfig.Configuration g (sideP l) → ℂ}
    (hF : WindowLocal l s (v + v + 1 + 1) (fun U => F (OpenAIConfig.configEquiv (sideP l) U)))
    (hG : ReflectionClosed l s (v + v + 1) F G) :
    reflO l v (slabOf l s (fun U => (F (OpenAIConfig.configEquiv (sideP l) U)).re))
      = slabOf l s (fun U => (G (OpenAIConfig.configEquiv (sideP l) U)).re) := by
  funext Vs As
  unfold reflO
  rw [revG_slabOf l s (v + v + 1) hL (windowLocal_comp hF Complex.re)]
  exact ((congrArg Complex.re (hG (recon l s Vs As))).trans (Complex.conj_re _)).symm

/-- **The reflected imaginary part is minus the imaginary part of the reflected insertion**, under
the same hypotheses as `reflO_slabOf_re`.

DERIVED: `2` doubles the width; `1` the offsets. -/
theorem reflO_slabOf_im (s v : ℕ) (hL : s + (v + v + 1) + 1 < l + l + 2)
    {F G : OpenAIConfig.Configuration g (sideP l) → ℂ}
    (hF : WindowLocal l s (v + v + 1 + 1) (fun U => F (OpenAIConfig.configEquiv (sideP l) U)))
    (hG : ReflectionClosed l s (v + v + 1) F G) :
    reflO l v (slabOf l s (fun U => (F (OpenAIConfig.configEquiv (sideP l) U)).im))
      = slabOf l s (fun U => -(G (OpenAIConfig.configEquiv (sideP l) U)).im) := by
  funext Vs As
  unfold reflO
  rw [revG_slabOf l s (v + v + 1) hL (windowLocal_comp hF Complex.im)]
  exact (neg_eq_iff_eq_neg.mpr
    ((congrArg Complex.im (hG (recon l s Vs As))).trans (Complex.conj_im _))).symm

end Reflect

/-! ## 10. Their regularity and the window of a smeared insertion -/

section Regularity

open MassGap.OpenAILink

/-- A site moved by an integer offset, `x + d` in `ZMod L` coordinatewise.

DERIVED: no numeral appears in the statement. -/
def offsetSite {L : ℕ+} (x : OpenAIConfig.Site L) (d : OpenAIConfig.Axis → ℤ) :
    OpenAIConfig.Site L :=
  fun a => x a + (d a : ZMod L.val)

/-- **Stencil locality**: `f x` reads only the links `(x + d, a)` whose other end `x + d + â` is
also `x + d'` with `d, d'` in the stencil `S`.

DERIVED: `1` is the unit step along an axis. -/
def StencilLocal {g : OpenAIConfig.GaugeGroup} {L : ℕ+} (S : Finset (OpenAIConfig.Axis → ℤ))
    (f : OpenAIConfig.Site L → OpenAIConfig.Configuration g L → ℂ) : Prop :=
  ∀ x U U', (∀ d ∈ S, ∀ d' ∈ S, ∀ a : OpenAIConfig.Axis,
    offsetSite x d' = offsetSite x d + Pi.single a 1 →
      U (offsetSite x d, a) = U' (offsetSite x d, a)) → f x U = f x U'

/-- **Their regularity of the insertions.** Restated from `ChallengeSpec.lean:11–22`
(`WilsonRegularity`) field for field: the couplings run logarithmically with a positive slope
(`running`, `:13–14`); every insertion is continuous in the configuration (`continuous`, `:15`) and
gauge invariant (`invariant`, `:16–18`); every token has a finite stencil such that its insertion at
`x` reads only the links with both ends in `stencil + x` (`localSupport`, `:19–22`).

DERIVED: `0` is the sign of the slope and of `ε`; `1` the unit step of a link. -/
structure WilsonRegularity {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) : Prop where
  running : ∃ slope : ℝ, 0 < slope ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ p, |C.beta N p / Real.log (C.mesh N)⁻¹ - slope| < ε
  continuous (N p v x) : Continuous (C.insertion N p v x)
  invariant (N p v x) (t : OpenAIConfig.Site (C.period p * C.denominator N) → g.image) (U) :
    C.insertion N p v x (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) =
      C.insertion N p v x U
  localSupport (v : C.Token) : ∃ stencil : Finset (OpenAIConfig.Axis → ℤ),
    ∀ N p (x : OpenAIConfig.Site (C.period p * C.denominator N)),
    let sites := stencil.image fun z => (fun i => (z i : ZMod (C.period p * C.denominator N).val)) + x
    ∀ U V, (∀ e, e.1 ∈ sites → e.1 + Pi.single e.2 1 ∈ sites → U e = V e) →
      C.insertion N p v x U = C.insertion N p v x V

/-- A stencil of the token `v` given by their `localSupport`.

DERIVED: no numeral appears in the statement. -/
noncomputable def stencilOf {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    (R : WilsonRegularity C) (v : C.Token) : Finset (OpenAIConfig.Axis → ℤ) :=
  Classical.choose (R.localSupport v)

/-- **Their `localSupport` is `StencilLocal`**: a link with both ends in `stencilOf R v + x` is a
link `(x + d, a)` with `x + d + â = x + d'`, `d, d'` in the stencil.

DERIVED: `1` is the unit step of a link. -/
theorem stencilLocal_of_regularity {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    (R : WilsonRegularity C) (N p : ℕ) (v : C.Token) :
    StencilLocal (stencilOf R v) (C.insertion N p v) := by
  intro x U U' h
  have hs := Classical.choose_spec (R.localSupport v) N p x
  refine hs U U' fun e he1 he2 => ?_
  obtain ⟨d, hd, hde⟩ := Finset.mem_image.1 he1
  obtain ⟨d', hd', hde'⟩ := Finset.mem_image.1 he2
  have ho : ∀ z : OpenAIConfig.Axis → ℤ,
      (fun i => (z i : ZMod (C.period p * C.denominator N).val)) + x = offsetSite x z :=
    fun z => funext fun i => add_comm _ _
  rw [ho] at hde hde'
  obtain ⟨y, a⟩ := e
  simp only at hde hde'
  subst hde
  exact h d hd d' hd' a hde'

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- **`pull` by an axis permutation in their coordinates**: `(z, a) ↦ (z ∘ e⁻¹, e a)`.

DERIVED: `4` is the spacetime dimension. -/
theorem pull_axis_apply (e : Equiv.Perm (Fin 4)) (V : OpenAIConfig.Configuration g L)
    (z : OpenAIConfig.Site L) (a : Fin 4) :
    pull L (MassGap.WilsonHypercubic.axisLink e) V (z, a) = V (fun i => z (e.symm i), e a) := by
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv L).surjective z
  rw [pull_apply]
  rfl

/-- **`pull` by the one-step shift in their coordinates**: `(z, a) ↦ (z + τ̂, a)`.

DERIVED: `1` is the unit step; `4` the spacetime dimension. -/
theorem pull_shift_apply [NeZero (L : ℕ)] (τ : Fin 4) (V : OpenAIConfig.Configuration g L)
    (z : OpenAIConfig.Site L) (a : Fin 4) :
    pull L (MassGap.ShiftInvG.shiftLinkPerm τ) V (z, a) = V (z + Pi.single τ 1, a) := by
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv L).surjective z
  rw [pull_apply, MassGap.ShiftInvG.shiftLinkPerm_apply]
  simp only [MassGap.WilsonTransfer.shiftLink_fst, MassGap.WilsonTransfer.shiftLink_snd]
  rw [OpenAIConfig.siteEquiv_shift]

/-- **The transport in their coordinates**: `transport k V (z, b) = V (z ∘ swap₀₃ + k·0̂, swap₀₃ b)`;
the transfer slice of their time coordinate `z₃` is `z₃ + k`.

DERIVED: `0` is the transfer direction; `3` their time axis. -/
theorem transport_apply [NeZero (L : ℕ)] (k : ℕ) (V : OpenAIConfig.Configuration g L)
    (z : OpenAIConfig.Site L) (b : Fin 4) :
    transport g L k V (z, b)
      = V ((fun i => z (Equiv.swap 0 3 i)) + Pi.single 0 (k : ZMod L.val), Equiv.swap 0 3 b) := by
  induction k generalizing V with
  | zero =>
    show pull L (MassGap.WilsonHypercubic.axisLink (Equiv.swap 0 3)) V (z, b) = _
    rw [pull_axis_apply]
    simp only [Equiv.symm_swap, Nat.cast_zero, Pi.single_zero, add_zero]
  | succ k ih =>
    show transport g L k (pull L (MassGap.ShiftInvG.shiftLinkPerm 0) V) (z, b) = _
    rw [ih, pull_shift_apply, add_assoc, ← Pi.single_add, ← Nat.cast_succ]

/-- `ZMod.val` of the cast of an integer in `[0, L)` is the integer, read in `ℤ`.

DERIVED: `0` is the lower end of the range. -/
theorem val_intCast_of_nonneg {u : ℤ} (h0 : 0 ≤ u) (h1 : u < (L.val : ℤ)) :
    ((((u : ZMod L.val)).val : ℕ) : ℤ) = u := by
  have e : (u : ZMod L.val) = ((u.toNat : ℕ) : ZMod L.val) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have h2 : (u.toNat : ℤ) < L.val := by rw [Int.toNat_of_nonneg h0]; exact h1
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by exact_mod_cast h2), Int.toNat_of_nonneg h0]

open Fin.CommRing in
/-- `ZMod.finEquiv i` is the cast of `i`.

DERIVED: no numeral appears in the statement. -/
theorem finEquiv_eq_natCast (i : Fin L.val) :
    ZMod.finEquiv L.val i = ((i.val : ℕ) : ZMod L.val) := by
  conv_lhs => rw [← Fin.cast_val_eq_self i]
  exact map_natCast (ZMod.finEquiv L.val) i.val

/-- `ZMod.val` of `ZMod.finEquiv i` is `i`.

DERIVED: no numeral appears in the statement. -/
theorem val_finEquiv (i : Fin L.val) : (ZMod.finEquiv L.val i).val = i.val := by
  rw [finEquiv_eq_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]

/-- **Locality in the slices `s, …, s + m` of the transfer direction, in their coordinates**: `O`
reads only the links `(y, a)` with `s ≤ y₀ ≤ s + m`, the links along `0` only for `y₀ < s + m`.

DERIVED: `0` is the transfer direction. -/
def TimeWindowLocal {β : Type*} (s m : ℕ) (O : OpenAIConfig.Configuration g L → β) : Prop :=
  ∀ V V' : OpenAIConfig.Configuration g L,
    (∀ (y : OpenAIConfig.Site L) (a : OpenAIConfig.Axis), s ≤ (y 0).val → (y 0).val ≤ s + m →
      (a ≠ 0 ∨ (y 0).val < s + m) → V (y, a) = V' (y, a)) → O V = O V'

/-- **Their window is ours**: on the cubic side `2l + 2`, an observable local in the slices
`s, …, s + m` in their coordinates is `WindowLocal l s m` read through `configEquiv`.

DERIVED: `0` is the transfer direction; `1` the offset of the side. -/
theorem windowLocal_of_timeWindowLocal {β : Type*} (l s m : ℕ)
    {O : OpenAIConfig.Configuration g (OpenAIBridgeCompose.sideP l) → β}
    (hO : TimeWindowLocal g (OpenAIBridgeCompose.sideP l) s m O) :
    WindowLocal l s m (fun U => O (OpenAIConfig.configEquiv (OpenAIBridgeCompose.sideP l) U)) := by
  intro U U' hU
  apply hO
  intro y a hs hy ha
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l)).surjective y
  rw [OpenAIConfig.configEquiv_apply, OpenAIConfig.configEquiv_apply]
  have hv : (OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l) x 0).val = (x 0 : ℕ) :=
    val_finEquiv (OpenAIBridgeCompose.sideP l) (x 0)
  have hs' : s ≤ (x 0 : ℕ) := by rw [← hv]; exact hs
  have hy' : (x 0 : ℕ) ≤ s + m := by rw [← hv]; exact hy
  have ha' : a ≠ 0 ∨ (x 0 : ℕ) < s + m := by rw [← hv]; exact ha
  exact hU a x hs' hy' ha'

/-- A smeared sum of insertion products, `c Σ_x coef(x) Π_i ins (w i) (x i) V`; `smearIns` is the
case `coef x = t(place x)`, `c = mesh^{4n}`.

DERIVED: no numeral appears in the statement. -/
noncomputable def sumIns {Tok : Type} {n : ℕ}
    (ins : Tok → OpenAIConfig.Site L → OpenAIConfig.Configuration g L → ℂ) (c : ℂ)
    (w : Fin n → Tok) (coef : (Fin n → OpenAIConfig.Site L) → ℂ)
    (V : OpenAIConfig.Configuration g L) : ℂ :=
  c * ∑ x : Fin n → OpenAIConfig.Site L, coef x * ∏ i, ins (w i) (x i) V

/-- **The window of a transported smeared sum.** If every insertion is stencil local, and at every
tuple of sites in the support of the coefficients each stencil point `d` of each insertion has
transported time `valMinAbs (x_i)₃ + d₃ + K ∈ [s, s + m]` up to a multiple of `L` (a window across
the seam of the torus), with `k ≡ K` and `s + m + 1 < L`, then
the sum read through `transport k` is local in the slices `s, …, s + m` of the transfer direction. The
wrap-around is handled by the representatives: `x₃ = valMinAbs x₃` in `ZMod L`, and two integers
of `[0, L)` with equal casts are equal.

DERIVED: `0` is the transfer direction; `3` their time axis; `1` the unit step of a time link and
the margin of the side. -/
theorem timeWindowLocal_sumIns [NeZero (L : ℕ)] {Tok : Type} {n : ℕ}
    {ins : Tok → OpenAIConfig.Site L → OpenAIConfig.Configuration g L → ℂ}
    {S : Tok → Finset (OpenAIConfig.Axis → ℤ)} (hS : ∀ v, StencilLocal (S v) (ins v))
    (c : ℂ) (w : Fin n → Tok) (coef : (Fin n → OpenAIConfig.Site L) → ℂ) (k : ℕ) (K : ℤ)
    (hk : ((k : ℕ) : ZMod L.val) = (K : ZMod L.val)) (s m : ℕ) (hm : s + m + 1 < L.val)
    (hsupp : ∀ x, coef x ≠ 0 → ∀ i, ∀ d ∈ S (w i), ∃ e : ℤ,
      (s : ℤ) ≤ (x i 3).valMinAbs + d 3 + K + e * (L.val : ℤ) ∧
        (x i 3).valMinAbs + d 3 + K + e * (L.val : ℤ) ≤ s + m) :
    TimeWindowLocal g L s m (fun V => sumIns g L ins c w coef (transport g L k V)) := by
  intro V V' hV
  show sumIns g L ins c w coef (transport g L k V) = sumIns g L ins c w coef (transport g L k V')
  unfold sumIns
  refine congrArg (c * ·) (Finset.sum_congr rfl fun x _ => ?_)
  by_cases hx : coef x = 0
  · rw [hx, zero_mul, zero_mul]
  refine congrArg (coef x * ·) (Finset.prod_congr rfl fun i _ => ?_)
  apply hS (w i) (x i)
  intro d hd d' hd' a hda
  rw [transport_apply, transport_apply]
  obtain ⟨e, h0, h1⟩ := hsupp x hx i d hd
  have hL0 : (((L.val : ℕ)) : ZMod L.val) = 0 := ZMod.natCast_self _
  have hy : (((fun j => offsetSite (x i) d (Equiv.swap 0 3 j)) + Pi.single 0 (k : ZMod L.val) :
      OpenAIConfig.Site L) 0)
      = (((x i 3).valMinAbs + d 3 + K + e * (L.val : ℤ) : ℤ) : ZMod L.val) := by
    simp only [Pi.add_apply, Equiv.swap_apply_left, Pi.single_eq_same, offsetSite]
    push_cast
    rw [hk]
    linear_combination (-(e : ZMod L.val)) * hL0
  apply hV
  · rw [hy]
    generalize e * (L.val : ℤ) = E at h0 h1 ⊢
    have hval := val_intCast_of_nonneg L (u := (x i 3).valMinAbs + d 3 + K + E) (by omega)
      (by omega)
    omega
  · rw [hy]
    generalize e * (L.val : ℤ) = E at h0 h1 ⊢
    have hval := val_intCast_of_nonneg L (u := (x i 3).valMinAbs + d 3 + K + E) (by omega)
      (by omega)
    omega
  · by_cases ha : a = 3
    · right
      subst ha
      obtain ⟨e', h0', h1'⟩ := hsupp x hx i d' hd'
      have e3 := congrFun hda 3
      simp only [offsetSite, Pi.add_apply, Pi.single_eq_same] at e3
      have ecast : (((x i 3).valMinAbs + d' 3 + K + e' * (L.val : ℤ) : ℤ) : ZMod L.val)
          = (((x i 3).valMinAbs + d 3 + K + e * (L.val : ℤ) + 1 : ℤ) : ZMod L.val) := by
        push_cast
        linear_combination e3 + ((e' : ZMod L.val) - e) * hL0
      rw [hy]
      generalize e * (L.val : ℤ) = E at h0 h1 ecast ⊢
      generalize e' * (L.val : ℤ) = E' at h0' h1' ecast
      have hval := val_intCast_of_nonneg L (u := (x i 3).valMinAbs + d 3 + K + E) (by omega)
        (by omega)
      have hv1 := val_intCast_of_nonneg L (u := (x i 3).valMinAbs + d' 3 + K + E') (by omega)
        (by omega)
      have hv2 := val_intCast_of_nonneg L (u := (x i 3).valMinAbs + d 3 + K + E + 1) (by omega)
        (by omega)
      rw [ecast] at hv1
      omega
    · left
      intro h
      apply ha
      have := congrArg (Equiv.swap (0 : Fin 4) 3) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this

/-- `smearIns` is a smeared sum of insertion products with coefficients `t(place x)`.

DERIVED: `4` is the spacetime dimension; `2` the `L²` exponent. -/
theorem smearIns_eq_sumIns {C : WilsonFamily g} (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n) :
    smearIns C N p w t = sumIns g (C.period p * C.denominator N) (C.insertion N p)
      ((C.mesh N : ℂ) ^ (4 * n)) w (fun x => t (WithLp.toLp 2 fun i => C.place N p (x i))) :=
  rfl

/-- **The window of their transported smeared insertion.** With their regularity `R`, a stencil
time radius `r` for the tokens of `w`, and a test whose support lies, up to multiples of the
period, in the time slab `[T₀, T₁]`: for integers `lo ≤ T₀/mesh − r` and `hi ≥ T₁/mesh + r`, `k ≡ K` with `lo + K ≥ 0`, and
`(lo + K) + (hi − lo) + 1 < L`, the smeared insertion read through `transport k` is local in the
slices `lo + K, …, hi + K` of the transfer direction. A site `x` in the support has
`time (place x) + e · period = mesh · (valMinAbs x₃ + e L) ∈ [T₀, T₁]`, so each stencil point lies
at transported time `valMinAbs x₃ + d₃ + K + e L ∈ [lo + K, hi + K]` (`timeWindowLocal_sumIns`).

DERIVED: `0` is the transfer direction; `3` their time axis; `1` the margin of the side. -/
theorem timeWindowLocal_smearIns {C : WilsonFamily g} (R : WilsonRegularity C) (N p : ℕ)
    [NeZero ((C.period p * C.denominator N : ℕ+) : ℕ)] {n : ℕ} (w : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n) (r : ℤ) (hr : ∀ i, ∀ d ∈ stencilOf R (w i), |d 3| ≤ r)
    (T₀ T₁ : ℝ) (ht : ∀ y ∈ tsupport t, ∀ i, ∃ e : ℤ, T₀ ≤ time (y i) + e * ((C.period p : ℕ) : ℝ) ∧
      time (y i) + e * ((C.period p : ℕ) : ℝ) ≤ T₁)
    (lo hi : ℤ) (hlo : (lo : ℝ) + r ≤ T₀ * (C.denominator N : ℝ))
    (hhi : T₁ * (C.denominator N : ℝ) ≤ (hi : ℝ) - r) (k : ℕ) (K : ℤ) (hK : 0 ≤ lo + K)
    (hk : ((k : ℕ) : ZMod (C.period p * C.denominator N : ℕ+).val) = (K : ZMod _))
    (hm : (lo + K).toNat + (hi - lo).toNat + 1 < (C.period p * C.denominator N : ℕ+).val) :
    TimeWindowLocal g (C.period p * C.denominator N) (lo + K).toNat (hi - lo).toNat
      (fun V => smearIns C N p w t (transport g (C.period p * C.denominator N) k V)) := by
  rw [show (fun V => smearIns C N p w t (transport g (C.period p * C.denominator N) k V))
      = fun V => sumIns g (C.period p * C.denominator N) (C.insertion N p)
          ((C.mesh N : ℂ) ^ (4 * n)) w (fun x => t (WithLp.toLp 2 fun i => C.place N p (x i)))
          (transport g (C.period p * C.denominator N) k V) from rfl]
  refine timeWindowLocal_sumIns g _ (stencilLocal_of_regularity R N p) _ w _ k K hk _ _ hm ?_
  intro x hx i d hd
  have hmem := subset_tsupport (⇑t) (Function.mem_support.2 hx)
  obtain ⟨e, h0, h1⟩ := ht _ hmem i
  have hD : (0 : ℝ) < (C.denominator N : ℝ) := by exact_mod_cast (C.denominator N).pos
  have ev : time ((WithLp.toLp 2 fun i => C.place N p (x i) : Points n) i)
      = (C.denominator N : ℝ)⁻¹ * ((x i 3).valMinAbs : ℝ) := rfl
  rw [ev] at h0 h1
  have hLr : (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℝ)
      = ((C.period p : ℕ) : ℝ) * (C.denominator N : ℝ) := by
    rw [PNat.mul_coe]; push_cast; rfl
  have hexp : (C.denominator N : ℝ) * ((C.denominator N : ℝ)⁻¹ * ((x i 3).valMinAbs : ℝ)
      + e * ((C.period p : ℕ) : ℝ))
      = ((x i 3).valMinAbs : ℝ) + e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℝ) := by
    rw [hLr]; field_simp
  have a0 := mul_le_mul_of_nonneg_left h0 hD.le
  have a1 := mul_le_mul_of_nonneg_left h1 hD.le
  rw [hexp] at a0 a1
  have b0 : (lo : ℝ) + r
      ≤ ((x i 3).valMinAbs : ℝ) + e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℝ) := by
    nlinarith
  have b1 : ((x i 3).valMinAbs : ℝ) + e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℝ)
      ≤ (hi : ℝ) - r := by nlinarith
  have c0 : lo + r
      ≤ (x i 3).valMinAbs + e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℤ) := by
    exact_mod_cast b0
  have c1 : (x i 3).valMinAbs + e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℤ)
      ≤ hi - r := by exact_mod_cast b1
  have hd3 := abs_le.1 (hr i d hd)
  have := Int.self_le_toNat (hi - lo)
  have := Int.toNat_of_nonneg hK
  refine ⟨e, ?_, ?_⟩
  · generalize e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℤ) = E at c0 c1 ⊢
    omega
  · generalize e * (((C.period p * C.denominator N : ℕ+).val : ℕ) : ℤ) = E at c0 c1 ⊢
    omega

/-- **Window locality is monotone in the window.**

DERIVED: no numeral appears in the statement. -/
theorem timeWindowLocal_mono {β : Type*} {s m s' m' : ℕ} {O : OpenAIConfig.Configuration g L → β}
    (h : TimeWindowLocal g L s m O) (h1 : s' ≤ s) (h2 : s + m ≤ s' + m') :
    TimeWindowLocal g L s' m' O :=
  fun V V' hV => h V V' fun y a hs hy ha =>
    hV y a (by omega) (by omega) (ha.imp id fun h => by omega)

/-- **`k` one-step shifts in their coordinates**: `(z, a) ↦ (z + k τ̂, a)`.

DERIVED: no numeral appears in the statement. -/
theorem pull_shift_iter_apply (τ : Fin 4) (k : ℕ) (V : OpenAIConfig.Configuration g L)
    (z : OpenAIConfig.Site L) (a : Fin 4) :
    (pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[k] V (z, a)
      = V (z + Pi.single τ (k : ZMod L.val), a) := by
  induction k generalizing V with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, pull_shift_apply, add_assoc, ← Pi.single_add,
      ← Nat.cast_succ]

/-- The slice `s' + x₀` of a site, read through `siteEquiv`, is the site moved by `s'` along `0`.

DERIVED: `0` is the transfer direction; `1` the offset of the side. -/
theorem siteEquiv_join_shift (l : ℕ) (x : WilsonHypercubic.Site 4 (OpenAIBridgeCompose.sideP l))
    (s' : ℕ) (h : s' + ((x 0 : ℕ) - 0) < TorusChain.Lc (l + l + 1) 0) :
    OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l)
        (MassGap.RectWilson.join (TorusChain.Lc (l + l + 1)) 0 ⟨s' + ((x 0 : ℕ) - 0), h⟩
          (MassGap.RectWilson.perp _ 0 x))
      = OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l) x
        + Pi.single 0 (s' : ZMod (OpenAIBridgeCompose.sideP l).val) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Pi.add_apply, Pi.single_eq_same, OpenAIConfig.siteEquiv_apply,
      OpenAIConfig.siteEquiv_apply, MassGap.RectWilson.join_self, finEquiv_eq_natCast,
      finEquiv_eq_natCast]
    show ((s' + ((x 0 : ℕ) - 0) : ℕ) : ZMod (OpenAIBridgeCompose.sideP l).val) = _
    rw [Nat.sub_zero]
    push_cast
    ring
  · rw [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, OpenAIConfig.siteEquiv_apply,
      OpenAIConfig.siteEquiv_apply]
    congr 1
    exact MassGap.RectWilson.join_ne _ _ ⟨j, hj⟩

/-- **The slice-shift lemma.** A slab observable built at slice `0` from an observable local in the
slices `0, …, m`, read at slice `s'` with `s' + m < 2l + 2`, is the observable of the configuration
shifted by `s'` slices along the transfer direction.

DERIVED: `0` is the first slice and the transfer direction; `1` the offset of the side; `2` the
doubled half-side. -/
theorem readAt_slabOf_shift (l s' m : ℕ) (hm : s' + m < l + l + 2)
    (O : OpenAIConfig.Configuration g (OpenAIBridgeCompose.sideP l) → ℝ)
    (hO : TimeWindowLocal g (OpenAIBridgeCompose.sideP l) 0 m O)
    (V : OpenAIConfig.Configuration g (OpenAIBridgeCompose.sideP l)) :
    OpenAIBridgeCompose.readAt l
        (slabOf l 0 (fun U => O (OpenAIConfig.configEquiv (OpenAIBridgeCompose.sideP l) U))) s' V
      = O ((pull (OpenAIBridgeCompose.sideP l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[s'] V) := by
  apply hO
  intro y a hs hy ha
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l)).surjective y
  have hv : (OpenAIConfig.siteEquiv (OpenAIBridgeCompose.sideP l) x 0).val = (x 0 : ℕ) :=
    val_finEquiv (OpenAIBridgeCompose.sideP l) (x 0)
  rw [hv] at hy
  have hlt : s' + ((x 0 : ℕ) - 0) < TorusChain.Lc (l + l + 1) 0 := by
    simp only [TorusChain.Lc]; omega
  rw [OpenAIConfig.configEquiv_apply, pull_shift_iter_apply, ← siteEquiv_join_shift l x s' hlt]
  conv_rhs => rw [← MeasurableEquiv.apply_symm_apply (OpenAIConfig.configEquiv
    (OpenAIBridgeCompose.sideP l)) V]
  rw [OpenAIConfig.configEquiv_apply]
  by_cases ha0 : a = 0
  · subst ha0
    dsimp only [recon]
    rw [dif_pos rfl]
    simp only [MassGap.OpenAIBridgeSlab.slabA, dif_pos hlt]
    rfl
  · dsimp only [recon]
    rw [dif_neg ha0]
    simp only [MassGap.OpenAIBridgeSlab.slabV, dif_pos hlt]
    rfl

end Regularity

/-! ## 11. The reflection of their tokens -/

section TokenReflect

open MassGap.OpenAILink MassGap.RectWilson MassGap.OpenAIBridgeCompose

/-- Their site reflected along the axis `τ` about `c`: `x_τ ↦ c − x_τ`.

DERIVED: no numeral appears in the statement. -/
def reflSite {L : ℕ+} (c : ZMod L.val) (τ : OpenAIConfig.Axis) (x : OpenAIConfig.Site L) :
    OpenAIConfig.Site L :=
  Function.update x τ (c - x τ)

/-- `reflSite c τ` is an involution.

DERIVED: no numeral appears in the statement. -/
theorem reflSite_reflSite {L : ℕ+} (c : ZMod L.val) (τ : OpenAIConfig.Axis)
    (x : OpenAIConfig.Site L) : reflSite c τ (reflSite c τ x) = x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp [reflSite]
  · simp [reflSite, Function.update_of_ne h]

/-- **Their configuration reflected along the axis `τ` about `c`**: a link `(x, a)` across `τ` is
read at `reflSite c τ x`; a link `(x, τ)` along `τ`, from `x` to `x + τ̂`, is the inverse of the link
from `reflSite (c − 1) τ x`.

DERIVED: `1` is the unit step of a link along `τ`. -/
def reflConfT {g : OpenAIConfig.GaugeGroup} {L : ℕ+} (c : ZMod L.val) (τ : OpenAIConfig.Axis)
    (V : OpenAIConfig.Configuration g L) : OpenAIConfig.Configuration g L :=
  fun e => if e.2 = τ then (V (reflSite (c - 1) τ e.1, τ))⁻¹ else V (reflSite c τ e.1, e.2)

/-- `reflConfT c τ` is an involution.

DERIVED: no numeral appears in the statement. -/
theorem reflConfT_reflConfT {g : OpenAIConfig.GaugeGroup} {L : ℕ+} (c : ZMod L.val)
    (τ : OpenAIConfig.Axis) (V : OpenAIConfig.Configuration g L) :
    reflConfT c τ (reflConfT c τ V) = V := by
  funext e
  obtain ⟨x, a⟩ := e
  by_cases h : a = τ
  · subst h
    simp [reflConfT, reflSite_reflSite]
  · simp [reflConfT, h, reflSite_reflSite]

/-- **Named input: a token reflection.** `Θ` sends each token to its time reflection: at every
spacing and volume, every reflection plane `c` of their time axis and every configuration, the
insertion of `Θ v` at the reflected site in the reflected configuration is the complex conjugate of
the insertion of `v`.

DERIVED: `3` is their time axis. -/
def TokenReflection {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (Θ : C.Token → C.Token) :
    Prop :=
  ∀ N p v x (c : ZMod (C.period p * C.denominator N : ℕ+).val) U,
    C.insertion N p (Θ v) (reflSite c 3 x) (reflConfT c 3 U)
      = (starRingEnd ℂ) (C.insertion N p v x U)

/-- **Named input: the reflected test on the lattice.** At every tuple of sites, `tθ` at the
reflected places is the conjugate of `t`.

DERIVED: `2` is the `L²` exponent; `3` their time axis. -/
def ReflectedTest {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (c : ZMod (C.period p * C.denominator N : ℕ+).val) (t tθ : WilsonFamily.SeparatedTest n) :
    Prop :=
  ∀ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N),
    tθ (WithLp.toLp 2 fun i => C.place N p (reflSite c 3 (x i)))
      = (starRingEnd ℂ) (t (WithLp.toLp 2 fun i => C.place N p (x i)))

/-- Tuples of sites reflected entrywise.

DERIVED: `3` is their time axis. -/
def reflTuple {L : ℕ+} {n : ℕ} (c : ZMod L.val) :
    (Fin n → OpenAIConfig.Site L) ≃ (Fin n → OpenAIConfig.Site L) where
  toFun x i := reflSite c 3 (x i)
  invFun x i := reflSite c 3 (x i)
  left_inv x := funext fun i => reflSite_reflSite c 3 (x i)
  right_inv x := funext fun i => reflSite_reflSite c 3 (x i)

/-- **The reflected smeared insertion.** Under `TokenReflection C Θ` and `ReflectedTest`, the
smeared insertion of `Θ ∘ w` against `tθ` in the reflected configuration is the conjugate of the
smeared insertion of `w` against `t`: reindex the site sum by `reflTuple`, and `mesh` is real.

DERIVED: `4` is the spacetime dimension; `3` their time axis. -/
theorem smearIns_reflect {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ) (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t tθ : WilsonFamily.SeparatedTest n) (c : ZMod (C.period p * C.denominator N : ℕ+).val)
    (htθ : ReflectedTest C N p c t tθ)
    (U : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    smearIns C N p (fun i => Θ (w i)) tθ (reflConfT c 3 U)
      = (starRingEnd ℂ) (smearIns C N p w t U) := by
  unfold smearIns
  rw [map_mul, map_sum, map_pow, Complex.conj_ofReal]
  congr 1
  refine (Equiv.sum_comp (reflTuple c) _).symm.trans (Finset.sum_congr rfl fun x _ => ?_)
  show tθ (WithLp.toLp 2 fun i => C.place N p (reflSite c 3 (x i)))
      * ∏ i, C.insertion N p (Θ (w i)) (reflSite c 3 (x i)) (reflConfT c 3 U) = _
  rw [htθ x, map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => hΘ N p (w i) (x i) c U

/-- The reflected smeared insertion, read the other way: `G(W) = conj F(reflConfT c 3 W)`.

DERIVED: `3` is their time axis. -/
theorem smearIns_reflect' {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}
    {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ) (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t tθ : WilsonFamily.SeparatedTest n) (c : ZMod (C.period p * C.denominator N : ℕ+).val)
    (htθ : ReflectedTest C N p c t tθ)
    (W : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    smearIns C N p (fun i => Θ (w i)) tθ W
      = (starRingEnd ℂ) (smearIns C N p w t (reflConfT c 3 W)) := by
  have h := smearIns_reflect hΘ N p w t tθ c htθ (reflConfT c 3 W)
  rwa [reflConfT_reflConfT] at h

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- **Reflection commutes with the transport**: the reflection of their time axis about `c₀` in
their frame is the reflection of the transfer direction about `c₀ + 2k` in the transfer frame.

DERIVED: `0` is the transfer direction; `3` their time axis; `2` the doubled shift. -/
theorem reflConfT_transport [NeZero (L : ℕ)] (k : ℕ) (c₀ : ZMod L.val)
    (V : OpenAIConfig.Configuration g L) :
    reflConfT c₀ 3 (transport g L k V)
      = transport g L k (reflConfT (c₀ + 2 * (k : ZMod L.val)) 0 V) := by
  funext e
  obtain ⟨z, b⟩ := e
  rw [transport_apply]
  by_cases hb : b = 3
  · subst hb
    have h0 : Equiv.swap (0 : Fin 4) 3 3 = 0 := Equiv.swap_apply_right _ _
    simp only [reflConfT, h0, ↓reduceIte]
    rw [transport_apply, h0]
    congr 4
    funext i
    fin_cases i
    all_goals simp [reflSite, Function.update_apply, Equiv.swap_apply_def]
    all_goals ring
  · have h0 : Equiv.swap (0 : Fin 4) 3 b ≠ 0 := by
      intro h
      apply hb
      have := congrArg (Equiv.swap (0 : Fin 4) 3) h
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    simp only [reflConfT, if_neg hb, if_neg h0]
    rw [transport_apply]
    congr 2
    funext i
    fin_cases i
    all_goals simp [reflSite, Function.update_apply, Equiv.swap_apply_def]
    all_goals ring

/-- `reflSite` on their side read through `siteEquiv`: the slice `q` with `q + x₀ = c` is the
reflection of `x₀` about `c`.

DERIVED: `0` is the transfer direction; `1` the offset of the side. -/
theorem siteEquiv_join_refl (l : ℕ) (x : WilsonHypercubic.Site 4 (sideP l)) (q c : ℕ)
    (hq : q + (x 0 : ℕ) = c) :
    OpenAIConfig.siteEquiv (sideP l)
        (join (TorusChain.Lc (l + l + 1)) 0 ⟨q % (l + l + 1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
          (perp _ 0 x))
      = reflSite ((c : ℕ) : ZMod (sideP l).val) 0 (OpenAIConfig.siteEquiv (sideP l) x) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [reflSite, Function.update_self, OpenAIConfig.siteEquiv_apply, OpenAIConfig.siteEquiv_apply,
      join_self, finEquiv_eq_natCast, finEquiv_eq_natCast]
    show (((q % (l + l + 1 + 1) : ℕ)) : ZMod (sideP l).val) = _
    rw [show (((q % (l + l + 1 + 1) : ℕ)) : ZMod (sideP l).val) = (q : ZMod (sideP l).val) from
      ZMod.natCast_mod q (sideP l).val]
    have hq' : ((q : ℕ) : ZMod (sideP l).val) + (((x 0 : ℕ)) : ZMod (sideP l).val)
        = ((c : ℕ) : ZMod (sideP l).val) := by
      rw [← hq]; push_cast; ring
    linear_combination hq'
  · rw [reflSite, Function.update_of_ne hj, OpenAIConfig.siteEquiv_apply,
      OpenAIConfig.siteEquiv_apply]
    congr 1
    exact join_ne _ _ ⟨j, hj⟩

/-- **The reflection of `reflConf` is their reflection, on a window.** For an observable local in
the slices `s, …, s + m + 1` of the transfer direction, reading it on `reflConf l s m U` is reading
it on their reflection `reflConfT (2s + m + 1) 0` of `U`.

DERIVED: `0` is the transfer direction; `1` the offsets of the window and of the side; `2` the
doubled offset of the plane. -/
theorem reflConf_window {β : Type*} (l s m : ℕ)
    {O : OpenAIConfig.Configuration g (sideP l) → β}
    (hO : TimeWindowLocal g (sideP l) s (m + 1) O)
    (U : RLink (TorusChain.Lc (l + l + 1)) → g.image) :
    O (OpenAIConfig.configEquiv (sideP l) (reflConf l s m U))
      = O (reflConfT (((s + s + m + 1 : ℕ)) : ZMod (sideP l).val) 0
          (OpenAIConfig.configEquiv (sideP l) U)) := by
  apply hO
  intro y a hs hy ha
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv (sideP l)).surjective y
  have hv : (OpenAIConfig.siteEquiv (sideP l) x 0).val = (x 0 : ℕ) := val_finEquiv (sideP l) (x 0)
  rw [hv] at hs hy ha
  rw [OpenAIConfig.configEquiv_apply]
  by_cases h0 : a = 0
  · subst h0
    have hlt : (x 0 : ℕ) < s + (m + 1) := ha.resolve_left (fun h => h rfl)
    have hc : (((s + s + m + 1 : ℕ)) : ZMod (sideP l).val) - 1 = (((s + s + m : ℕ)) : ZMod _) := by
      push_cast; ring
    simp only [reflConf, reflConfT, if_pos, hc]
    rw [← siteEquiv_join_refl l x _ _ (by omega : s + (m - ((x 0 : ℕ) - s)) + (x 0 : ℕ) = s + s + m),
      OpenAIConfig.configEquiv_apply]
    rfl
  · simp only [reflConf, reflConfT, if_neg h0]
    rw [← siteEquiv_join_refl l x _ _
      (by omega : s + (m + 1 - ((x 0 : ℕ) - s)) + (x 0 : ℕ) = s + s + m + 1),
      OpenAIConfig.configEquiv_apply]
    rfl

/-- **`ReflectionClosed` from a reflection in their frame.** On the cubic side `2l + 2`: if
`G W = conj F(reflConfT c₀ 3 W)` for every configuration (their time reflection about `c₀`), and
`F ∘ transport k` is local in the slices `s, …, s + m + 1` with `c₀ + 2k ≡ 2s + m + 1`, then the
transported pair is `ReflectionClosed l s m`.

DERIVED: `0` is the transfer direction; `3` their time axis; `2` the doubled shift and offset; `1`
the offsets. -/
theorem reflectionClosed_of_reflConfT (l s m k : ℕ)
    (c₀ : ZMod (sideP l).val)
    (hc : c₀ + 2 * (k : ZMod (sideP l).val) = (((s + s + m + 1 : ℕ)) : ZMod (sideP l).val))
    (F G : OpenAIConfig.Configuration g (sideP l) → ℂ)
    (hFG : ∀ W, G W = (starRingEnd ℂ) (F (reflConfT c₀ 3 W)))
    (hFw : TimeWindowLocal g (sideP l) s (m + 1) (fun V => F (transport g (sideP l) k V))) :
    ReflectionClosed l s m (fun V => F (transport g (sideP l) k V))
      (fun V => G (transport g (sideP l) k V)) := by
  intro U
  show G (transport g (sideP l) k (OpenAIConfig.configEquiv (sideP l) U))
    = (starRingEnd ℂ) (F (transport g (sideP l) k
        (OpenAIConfig.configEquiv (sideP l) (reflConf l s m U))))
  rw [hFG, reflConfT_transport, hc]
  congr 1
  exact (reflConf_window g l s m hFw U).symm

/-- **The reflected observable keeps the window.** For an observable local in the slices
`0, …, w` of the transfer direction, `w < L`, its reading on their reflection `reflConfT w 0` about
the window's centre is local in the same slices: a link across the transfer direction at slice
`y₀ ≤ w` is read at `w − y₀`, a link along it at `y₀ < w` at `w − 1 − y₀`.

DERIVED: `0` is the first slice and the transfer direction; `1` the unit step of a link. -/
theorem timeWindowLocal_reflConfT {β : Type*} (w : ℕ) (hw : w < L.val)
    {O : OpenAIConfig.Configuration g L → β} (hO : TimeWindowLocal g L 0 w O) :
    TimeWindowLocal g L 0 w (fun V => O (reflConfT ((w : ℕ) : ZMod L.val) 0 V)) := by
  intro V V' hV
  apply hO
  intro y a hs hy ha
  have hy0 : (((y 0).val : ℕ) : ZMod L.val) = y 0 := ZMod.natCast_zmod_val (y 0)
  by_cases h0 : a = 0
  · subst h0
    have hlt : (y 0).val < w := by
      have := ha.resolve_left (fun h => h rfl)
      omega
    have hr : (reflSite (((w : ℕ) : ZMod L.val) - 1) 0 y) 0
        = (((w - 1 - (y 0).val : ℕ)) : ZMod L.val) := by
      rw [reflSite, Function.update_self, Nat.cast_sub (by omega : (y 0).val ≤ w - 1),
        Nat.cast_sub (by omega : 1 ≤ w), Nat.cast_one, hy0]
    have hv : ((reflSite (((w : ℕ) : ZMod L.val) - 1) 0 y) 0).val = w - 1 - (y 0).val := by
      rw [hr, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [reflConfT, ↓reduceIte]
    congr 1
    apply hV
    · exact Nat.zero_le _
    · rw [hv]; omega
    · right; rw [hv]; omega
  · have hr : (reflSite ((w : ℕ) : ZMod L.val) 0 y) 0 = (((w - (y 0).val : ℕ)) : ZMod L.val) := by
      rw [reflSite, Function.update_self, Nat.cast_sub (by omega : (y 0).val ≤ w), hy0]
    have hv : ((reflSite ((w : ℕ) : ZMod L.val) 0 y) 0).val = w - (y 0).val := by
      rw [hr, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [reflConfT, if_neg h0]
    apply hV
    · exact Nat.zero_le _
    · rw [hv]; omega
    · left; exact h0

end TokenReflect

/-! ## 12. Their side as the cubic side -/

section Side

open MassGap.OpenAILink MassGap.OpenAIBridgeCompose MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.RectWilson MassGap.CompactGauge

variable {g : OpenAIConfig.GaugeGroup}

/-- **An observable of their side `L` read on the cubic side `2l + 2`**, through an equality
`L = sideP l` of sides; at `L = sideP l` itself it is the observable.

DERIVED: `1` is the offset of the side. -/
def toSide {β : Type*} {L : ℕ+} (l : ℕ) (hL : L = sideP l)
    (F : OpenAIConfig.Configuration g L → β) : OpenAIConfig.Configuration g (sideP l) → β :=
  hL ▸ F

/-- **The connected correlation is read on the cubic side**: for every equality of sides, the
connected correlation of `F`, `G` under their law of side `L` is that of `toSide F`, `toSide G`
under their law of side `2l + 2`.

DERIVED: `1` is the offset of the side. -/
theorem conn_toSide {L : ℕ+} (l : ℕ) (hL : L = sideP l) (β : ℝ) (μ : Measure g.image)
    (F G : OpenAIConfig.Configuration g L → ℂ) :
    ∫ V, F V * G V ∂(OpenAIConfig.wilsonLaw g L β μ)
        - (∫ V, F V ∂(OpenAIConfig.wilsonLaw g L β μ)) * ∫ V, G V ∂(OpenAIConfig.wilsonLaw g L β μ)
      = ∫ V, toSide l hL F V * toSide l hL G V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ)
        - (∫ V, toSide l hL F V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ))
          * ∫ V, toSide l hL G V ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) := by
  subst hL
  rfl

/-- `toSide` keeps continuity.

DERIVED: `1` is the offset of the side. -/
theorem continuous_toSide {β : Type*} [TopologicalSpace β] {L : ℕ+} (l : ℕ) (hL : L = sideP l)
    {F : OpenAIConfig.Configuration g L → β} (hF : Continuous F) : Continuous (toSide l hL F) := by
  subst hL
  exact hF

/-- `toSide` keeps window locality.

DERIVED: `1` is the offset of the side. -/
theorem timeWindowLocal_toSide {β : Type*} {L : ℕ+} (l : ℕ) (hL : L = sideP l) {s m : ℕ}
    {F : OpenAIConfig.Configuration g L → β} (hF : TimeWindowLocal g L s m F) :
    TimeWindowLocal g (sideP l) s m (toSide l hL F) := by
  subst hL
  exact hF

/-- **`toSide` commutes with the transport.**

DERIVED: `1` is the offset of the side. -/
theorem toSide_transport {β : Type*} {L : ℕ+} (l : ℕ) (hL : L = sideP l) (k : ℕ)
    (F : OpenAIConfig.Configuration g L → β) :
    toSide l hL (fun V => F (transport g L k V))
      = fun V => toSide l hL F (transport g (sideP l) k V) := by
  subst hL
  rfl

/-- **`toSide` keeps a reflection identity at an integer plane**: if `G W = conj F(reflConfT c 3 W)`
on their side `L` with `c` the cast of an integer, the same holds on the cubic side with the same
integer.

DERIVED: `3` is their time axis; `1` the offset of the side. -/
theorem toSide_reflect {L : ℕ+} (l : ℕ) (hL : L = sideP l) (cz : ℤ)
    {F G : OpenAIConfig.Configuration g L → ℂ}
    (h : ∀ W, G W = (starRingEnd ℂ) (F (reflConfT (cz : ZMod L.val) 3 W))) :
    ∀ W, toSide l hL G W
      = (starRingEnd ℂ) (toSide l hL F (reflConfT (cz : ZMod (sideP l).val) 3 W)) := by
  subst hL
  exact h

/-- **The per-torus inequality on their smeared moments.** For their family `C` with continuous
insertions at `(N, p)`, a side `period p · denominator N = 2l + 2` with `2l + 2 ≥ 8n` and the seed at
`β/2` on an even side `n ≥ 2`: there is one eigenpair `(φ, c)` with excited weight
`0 ≤ σ₀ ≤ (1/2)^⌊(l+1)/n⌋` such that for every tensor test `t = t₁ ⊗ t₂` and every transport `k`
under which the smeared insertion of `t₁` is local in the slices `0, …, 2v + 2` and that of `t₂` in
the slices from `2v + 2 + p + 1`, `p = 2a + j + 2`, the smeared connected correlation is at most the
sum over the four real pairs of `pairRHS` of their transported slab observables. Chain:
`smear_conn_eq_of_continuous` (Fubini), `conn_comp` with `measurePreserving_transport` (axis and
time translation), `conn_toSide` (the side), `openAI_slab_conn_cubic_complex` (the cubic bound),
`windowLocal_of_timeWindowLocal` (the windows).

DERIVED: `16` and `1000` are the seed; `8` the side condition; `4` the number of real pairs; `2`
the halved coupling, doubled side, widths and separations; `1/2` the contraction; `0` the first
slice and the transfer direction; `1` the offsets. -/
theorem smear_conn_cubic (C : WilsonFamily g) (N p : ℕ)
    (hc : ∀ v x, Continuous (C.insertion N p v x)) (l : ℕ)
    (hside : C.period p * C.denominator N = sideP l) (hβ : 0 ≤ C.beta N p) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n)
    (h0 : 16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
      - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000)
    (hL : 8 * n ≤ l + l + 2) :
    ∃ φ : (SpT 0 (TorusChain.Tc (l + l + 1)) → g.image) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = 1 ∧
      (∀ z, ∫ y, (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (C.beta N p / 2)) z y * φ y
        ∂(hSG g.image 0 (TorusChain.Tc (l + l + 1))) = c * φ z) ∧
      0 ≤ excW g l (C.beta N p) c φ ∧ excW g l (C.beta N p) c φ ≤ (1 / 2) ^ ((l + 1) / n) ∧
      ∀ {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token)
        (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂), (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
      ∀ k v v' a j j' aF bF aG bG cF cG : ℕ,
      a + j + a + 2 = aF + bG + 1 → a + j' + a + 2 = aG + bF + 1 →
      v + v + 2 + aF + bF + 1 = l → v' + v' + 2 + aG + bG + 1 = l →
      v + v + 2 + a + cF + 1 = l → v' + v' + 2 + a + cG + 1 = l →
      TimeWindowLocal g (C.period p * C.denominator N) 0 (v + v + 2)
        (fun V => smearIns C N p w₁ t₁ (transport g _ k V)) →
      TimeWindowLocal g (C.period p * C.denominator N) (v + v + 2 + (a + j + a + 2 + 1))
        (v' + v' + 2) (fun V => smearIns C N p w₂ t₂ (transport g _ k V)) →
      ‖C.smear N p (Fin.append w₁ w₂) t - C.smear N p w₁ t₁ * C.smear N p w₂ t₂‖
        ≤ ∑ i : Fin 4, pairRHS g C.haar l (C.beta N p) c φ n j j' v v' a aF bF aG bG
            (slabOf l 0 (fun U => reImF (toSide l hside
              (fun V => smearIns C N p w₁ t₁ (transport g _ k V))) i
                (OpenAIConfig.configEquiv (sideP l) U)))
            (slabOf l (v + v + 2 + (a + j + a + 2 + 1)) (fun U => reImG (toSide l hside
              (fun V => smearIns C N p w₂ t₂ (transport g _ k V))) i
                (OpenAIConfig.configEquiv (sideP l) U))) := by
  haveI := C.probability
  haveI := C.invariantHaar
  obtain ⟨φ, c, hc0, hφ1, heig, hσ0, hσ, hb⟩ :=
    openAI_slab_conn_cubic_complex g C.haar hβ hn he h0 l hL
  refine ⟨φ, c, hc0, hφ1, heig, hσ0, hσ, fun w₁ w₂ t t₁ t₂ ht k v v' a j j' aF bF aG bG cF cG
    h1 h2 h3 h4 h5 h6 hFw hGw => ?_⟩
  have key := hb
    (toSide l hside (fun V => smearIns C N p w₁ t₁ (transport g _ k V)))
    (toSide l hside (fun V => smearIns C N p w₂ t₂ (transport g _ k V)))
    (continuous_toSide l hside
      ((continuous_smearIns C N p hc w₁ t₁).comp (continuous_transport g _ k)))
    (continuous_toSide l hside
      ((continuous_smearIns C N p hc w₂ t₂).comp (continuous_transport g _ k)))
    v v' a j j' aF bF aG bG cF cG h1 h2 h3 h4 h5 h6
    (windowLocal_of_timeWindowLocal g l 0 (v + v + 2) (timeWindowLocal_toSide l hside hFw))
    (windowLocal_of_timeWindowLocal g l _ (v' + v' + 2) (timeWindowLocal_toSide l hside hGw))
  refine (le_of_eq ?_).trans key
  rw [smear_conn_eq_of_continuous C N p hc w₁ w₂ t t₁ t₂ ht,
    ← conn_comp (transport g _ k)
      (measurePreserving_transport g _ C.haar (C.beta N p) k)
      (smearIns C N p w₁ t₁) (smearIns C N p w₂ t₂)]
  exact congrArg norm (conn_toSide l hside (C.beta N p) C.haar
    (fun V => smearIns C N p w₁ t₁ (transport g _ k V))
    (fun V => smearIns C N p w₂ t₂ (transport g _ k V)))

end Side

/-! ## 13. The slab arithmetic -/

section Arith

/-- **The split of the torus into slabs** (compose-analysis §2a). For slab widths `2v + 2`,
`2v' + 2`, a separation half-width `a` and a gap `j` with `2v + 2 + a + 1 ≤ l`,
`2v' + 2 + a + j + 2 ≤ l` and `(2v + 2) + (2v' + 2) + 4a + j + 4 ≤ 2l`, the choice `a_F = a`,
`b_F = c_F = l − (2v+2) − a − 1`, `b_G = a + j + 1`, `a_G = l − (2v'+2) − a − j − 2`,
`c_G = l − (2v'+2) − a − 1` and the wrap gap `j' = 2l − (2v+2) − (2v'+2) − 4a − j − 4` satisfies the
six split equalities of `OpenAIBridgeCompose.openAI_slab_conn_cubic`.

DERIVED: `2` doubles the widths and separations; `4` is `2 · 2`, two separations on each side; `1`
the offsets. -/
theorem slab_split (l v v' a j : ℕ) (h1 : v + v + 2 + a + 1 ≤ l)
    (h2 : v' + v' + 2 + a + j + 2 ≤ l)
    (h3 : (v + v + 2) + (v' + v' + 2) + 4 * a + j + 4 ≤ l + l) :
    ∃ j' aF bF aG bG cF cG : ℕ,
      j' = l + l - (v + v + 2) - (v' + v' + 2) - 4 * a - j - 4 ∧
      a + j + a + 2 = aF + bG + 1 ∧ a + j' + a + 2 = aG + bF + 1 ∧
      v + v + 2 + aF + bF + 1 = l ∧ v' + v' + 2 + aG + bG + 1 = l ∧
      v + v + 2 + a + cF + 1 = l ∧ v' + v' + 2 + a + cG + 1 = l :=
  ⟨l + l - (v + v + 2) - (v' + v' + 2) - 4 * a - j - 4, a, l - (v + v + 2) - a - 1,
    l - (v' + v' + 2) - a - j - 2, a + j + 1, l - (v + v + 2) - a - 1, l - (v' + v' + 2) - a - 1,
    rfl, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The gap in physical time** (compose-analysis §2b). If the lattice gap `j` between the end of
the first window and the start of the second is at least the physical separation `τ` less the
two window margins `2a + 2` and the stencil slack `2r + 1`, in units of the spacing, and those
margins are at most `δ/2` in physical time, then `(j + 1) · mesh ≥ τ − δ/2`.

DERIVED: `2` halves the floor `δ` and doubles the margins and the stencil radius; `1` the step
offset. -/
theorem gap_ge (a j r : ℕ) {mesh τ δ : ℝ}
    (hj : τ ≤ ((j : ℝ) + 2 * a + 2 + 2 * r + 1 + 1) * mesh)
    (hslack : ((2 * a + 2 + 2 * r + 1 : ℕ) : ℝ) * mesh ≤ δ / 2) :
    τ - δ / 2 ≤ ((j : ℝ) + 1) * mesh := by
  push_cast at hslack
  nlinarith

end Arith

/-! ## 14. The assembly of the cubic form -/

section Assembly

open MassGap.OpenAILink MassGap.OpenAIBridgeCompose MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.RectWilson MassGap.CompactGauge

variable {g : OpenAIConfig.GaugeGroup}

/-- **A placement of the two slabs on one torus**: the seed side `n`, the transport `k`, the
half-side `l` (side `2l + 2`), the slab half-widths `v`, `v'`, the separation half-width `a` and the
gap `j`.

DERIVED: no numeral appears in the statement. -/
structure SlabPlacement where
  n : ℕ
  k : ℕ
  l : ℕ
  v : ℕ
  v' : ℕ
  a : ℕ
  j : ℕ

namespace SlabPlacement

variable (P : SlabPlacement)

/-- The wrap gap of `slab_split`.

DERIVED: `2` doubles the widths; `4` is `2 · 2`; `1` the offsets. -/
def j' : ℕ := P.l + P.l - (P.v + P.v + 2) - (P.v' + P.v' + 2) - 4 * P.a - P.j - 4

/-- `b_F` of `slab_split`.

DERIVED: `2` doubles the width; `1` the offset. -/
def bF : ℕ := P.l - (P.v + P.v + 2) - P.a - 1

/-- `a_G` of `slab_split`.

DERIVED: `2` doubles the width; `1` the offset. -/
def aG : ℕ := P.l - (P.v' + P.v' + 2) - P.a - P.j - 2

/-- `b_G` of `slab_split`.

DERIVED: `1` is the offset. -/
def bG : ℕ := P.a + P.j + 1

/-- `c_G` of `slab_split`.

DERIVED: `2` doubles the width; `1` the offset. -/
def cG : ℕ := P.l - (P.v' + P.v' + 2) - P.a - 1

/-- The first slice of the second slab, `2v + 2 + (2a + j + 2) + 1`.

DERIVED: `2` doubles the widths and separations; `1` the offset. -/
def start : ℕ := P.v + P.v + 2 + (P.a + P.j + P.a + 2 + 1)

/-- **A valid placement at `(N, p)`** for the token groups `w₁`, `w₂` and the tests `t₁`, `t₂`: their
side is the cubic side `2l + 2`; their coupling is nonnegative; the seed holds on the even side
`n ≥ 2` at half their coupling with `n · mesh ≤ ℓ` and `8n ≤ 2l + 2`; the slabs fit
(`slab_split`); the two transported smeared insertions are local in the slices `0, …, 2v + 2` and
from `start`; the gap and the wrap gap are at least `τ − δ/2` in physical time; the separation of
the reflected moments is at least `δ/4`.

DERIVED: `16` and `1000` are the seed; `8` the side condition; `2` doubles the widths and halves
the coupling and the floor; `4` quarters the floor and is `2 · 2`; `1` the offsets. -/
structure Valid (C : WilsonFamily g) (N p : ℕ) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token)
    (w₂ : Fin n₂ → C.Token) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (ℓ δ τ : ℝ) (P : SlabPlacement) : Prop where
  side : C.period p * C.denominator N = sideP P.l
  beta : 0 ≤ C.beta N p
  two_le : 2 ≤ P.n
  even : Even P.n
  seed : 16 * Real.log (ZRG g.image (fun _ => P.n) (C.beta N p / 2))
    - Real.log (ZRG g.image (fun _ => 2 * P.n) (C.beta N p / 2)) ≤ 1 / 1000
  scale : (P.n : ℝ) * C.mesh N ≤ ℓ
  eight : 8 * P.n ≤ P.l + P.l + 2
  fit₁ : P.v + P.v + 2 + P.a + 1 ≤ P.l
  fit₂ : P.v' + P.v' + 2 + P.a + P.j + 2 ≤ P.l
  fit₃ : (P.v + P.v + 2) + (P.v' + P.v' + 2) + 4 * P.a + P.j + 4 ≤ P.l + P.l
  win₁ : TimeWindowLocal g (C.period p * C.denominator N) 0 (P.v + P.v + 2)
    (fun V => smearIns C N p w₁ t₁ (transport g _ P.k V))
  win₂ : TimeWindowLocal g (C.period p * C.denominator N) P.start (P.v' + P.v' + 2)
    (fun V => smearIns C N p w₂ t₂ (transport g _ P.k V))
  gap : τ - δ / 2 ≤ ((P.j : ℝ) + 1) * C.mesh N
  gap' : τ - δ / 2 ≤ ((P.j' : ℝ) + 1) * C.mesh N
  sep : δ / 4 ≤ ((P.a : ℝ) + P.a + 2) * C.mesh N

end SlabPlacement

/-- The slab observable of the `i`-th real part of the first transported smeared insertion.

DERIVED: `4` is the number of real pairs; `0` the first slice. -/
noncomputable def slabF (C : WilsonFamily g) (N p : ℕ) {n₁ : ℕ} (w₁ : Fin n₁ → C.Token)
    (t₁ : WilsonFamily.SeparatedTest n₁) (P : SlabPlacement)
    (hside : C.period p * C.denominator N = sideP P.l) (i : Fin 4) : SlabObs g P.l :=
  slabOf P.l 0 (fun U => reImF (toSide P.l hside
    (fun V => smearIns C N p w₁ t₁ (transport g _ P.k V))) i
      (OpenAIConfig.configEquiv (sideP P.l) U))

/-- The slab observable of the `i`-th real part of the second transported smeared insertion.

DERIVED: `4` is the number of real pairs. -/
noncomputable def slabG (C : WilsonFamily g) (N p : ℕ) {n₂ : ℕ} (w₂ : Fin n₂ → C.Token)
    (t₂ : WilsonFamily.SeparatedTest n₂) (P : SlabPlacement)
    (hside : C.period p * C.denominator N = sideP P.l) (i : Fin 4) : SlabObs g P.l :=
  slabOf P.l P.start (fun U => reImG (toSide P.l hside
    (fun V => smearIns C N p w₂ t₂ (transport g _ P.k V))) i
      (OpenAIConfig.configEquiv (sideP P.l) U))

/-- **The three reflected moments of the first slab observable** of the pair `i`, at the
separation `2a + 2` (the slab first, the reflection first) and `2a_F + 2 = 2a + 2`: the moments
`M₁`, `M₃`, `M₅` of `pairRHS`.

DERIVED: `2` doubles the widths and separations; `0` the first slice; `3` the number of moments;
`4` the number of real pairs. -/
noncomputable def momF (C : WilsonFamily g) (N p : ℕ) {n₁ : ℕ} (w₁ : Fin n₁ → C.Token)
    (t₁ : WilsonFamily.SeparatedTest n₁) (P : SlabPlacement)
    (hside : C.period p * C.denominator N = sideP P.l) (i : Fin 4) : Fin 3 → ℝ :=
  ![∫ V, readAt P.l (slabF C N p w₁ t₁ P hside i) 0 V
        * readAt P.l (reflO P.l P.v (slabF C N p w₁ t₁ P hside i))
          (P.v + P.v + 2 + (P.a + P.a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar),
    ∫ V, readAt P.l (reflO P.l P.v (slabF C N p w₁ t₁ P hside i)) 0 V
        * readAt P.l (slabF C N p w₁ t₁ P hside i) (P.v + P.v + 2 + (P.a + P.a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar),
    ∫ V, readAt P.l (slabF C N p w₁ t₁ P hside i) 0 V
        * readAt P.l (reflO P.l P.v (slabF C N p w₁ t₁ P hside i))
          (P.v + P.v + 2 + (P.a + P.a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)]

/-- **The three reflected moments of the second slab observable** of the pair `i`, at the
separation `2a + 2` (the reflection first, the slab first) and `2a_G + 2`: the moments `M₂`, `M₄`,
`M₆` of `pairRHS`.

DERIVED: `2` doubles the widths and separations; `0` the first slice; `3` the number of moments;
`4` the number of real pairs. -/
noncomputable def momG (C : WilsonFamily g) (N p : ℕ) {n₂ : ℕ} (w₂ : Fin n₂ → C.Token)
    (t₂ : WilsonFamily.SeparatedTest n₂) (P : SlabPlacement)
    (hside : C.period p * C.denominator N = sideP P.l) (i : Fin 4) : Fin 3 → ℝ :=
  ![∫ V, readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hside i)) 0 V
        * readAt P.l (slabG C N p w₂ t₂ P hside i) (P.v' + P.v' + 2 + (P.a + P.a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar),
    ∫ V, readAt P.l (slabG C N p w₂ t₂ P hside i) 0 V
        * readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hside i))
          (P.v' + P.v' + 2 + (P.a + P.a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar),
    ∫ V, readAt P.l (slabG C N p w₂ t₂ P hside i) 0 V
        * readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hside i))
          (P.v' + P.v' + 2 + (P.aG + P.aG + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)]

/-- **The eigenpair of a valid placement**: the `(φ, c)` that `smear_conn_cubic` provides at the
placement's side and seed, chosen.

DERIVED: `0` is the transfer direction; `1` the offset of the side. -/
noncomputable def eigOf (C : WilsonFamily g) (R : WilsonRegularity C) (N p : ℕ) {n₁ n₂ : ℕ}
    {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {t₁ : WilsonFamily.SeparatedTest n₁}
    {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ} {P : SlabPlacement}
    (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) :
    ((SpT 0 (TorusChain.Tc (P.l + P.l + 1)) → g.image) → ℝ) × ℝ :=
  ((smear_conn_cubic C N p (R.continuous N p) P.l hP.side hP.beta hP.two_le hP.even hP.seed
      hP.eight).choose,
    (smear_conn_cubic C N p (R.continuous N p) P.l hP.side hP.beta hP.two_le hP.even hP.seed
      hP.eight).choose_spec.choose)

/-- **The excited–excited term of the pair `i` at a valid placement**, `√(remW_f · remW_h)` at the
chosen eigenpair.

DERIVED: `4` is the number of real pairs. -/
noncomputable def remD (C : WilsonFamily g) (R : WilsonRegularity C) (N p : ℕ) {n₁ n₂ : ℕ}
    {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {t₁ : WilsonFamily.SeparatedTest n₁}
    {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ} {P : SlabPlacement}
    (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) (i : Fin 4) : ℝ :=
  √(remW g P.l (C.beta N p) (eigOf C R N p hP).2 (eigOf C R N p hP).1 P.v
      (slabF C N p w₁ t₁ P hP.side i) P.a P.bF
    * remW g P.l (C.beta N p) (eigOf C R N p hP).2 (eigOf C R N p hP).1 P.v'
      (slabG C N p w₂ t₂ P hP.side i) P.aG P.bG)

/-- **The excited–excited term of `CubicForm`**: `remD` at the placement chosen among the valid
ones, and `0` where none is valid.

DERIVED: `0` is the value off the valid placements; `4` the number of real pairs. -/
noncomputable def chosenD (C : WilsonFamily g) (R : WilsonRegularity C) {n₁ n₂ : ℕ}
    (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (t₁ : WilsonFamily.SeparatedTest n₁)
    (t₂ : WilsonFamily.SeparatedTest n₂) (ℓ δ τ : ℝ) (i : Fin 4) (p N : ℕ) : ℝ := by
  classical
  exact if h : ∃ P : SlabPlacement, P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ then
    remD C R N p h.choose_spec i else 0

set_option maxHeartbeats 1600000 in
/-- **The ordered cubic form from its inputs.** For their family with regularity `R`, `CubicForm`
holds at `ℓ` if, for every floor `δ`, `ε` and every admissible ordered tensor test:
* (placement) eventually along their order and then in the spacing a valid placement exists
  (`SlabPlacement.Valid`: their side `2l + 2`, the seed with `n · mesh ≤ ℓ`, the slabs and the two
  windows, the gaps);
* (K₀) a constant `K₀ ≥ 0`, chosen before the test, bounds the six reflected moments `momF`,
  `momG` of every valid placement by `K₀ ‖t₁‖₁²`, `K₀ ‖t₂‖₁²`, and they are nonnegative;
* (D) the excited–excited terms `remD` of every valid placement vanish relative to
  `‖t₁‖₁ ‖t₂‖₁`.
The per-torus inequality is `smear_conn_cubic` at the chosen placement and its eigenpair, the
split equalities are those of `slab_split`, and `period = 2(l + 1) · mesh` is their side.

DERIVED: `2` halves the floor and doubles the half-side; `4` is the number of real pairs; `3` the
number of moments; `0` the signs; `1` the offsets. -/
theorem cubicForm_of_inputs (C : WilsonFamily g) (R : WilsonRegularity C) (order : ℕ → ℕ)
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (ℓ : ℝ)
    (hplace : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∃ P : SlabPlacement, P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ)
    (hK₀ : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) (i : Fin 4) (k : Fin 3),
            (0 ≤ momF C N p w₁ t₁ P hP.side i k ∧
              momF C N p w₁ t₁ P hP.side i k ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2) ∧
            (0 ≤ momG C N p w₂ t₂ P hP.side i k ∧
              momG C N p w₂ t₂ P hP.side i k ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2))
    (hD : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ (i : Fin 4) (η : ℝ), 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ),
            remD C R N p hP i ≤ η * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) :
    CubicForm C order w₁ w₂ ℓ := by
  intro δ ε hδ hε
  obtain ⟨K₀, hK0, hK⟩ := hK₀ δ ε hδ hε
  refine ⟨K₀, hK0, fun t t₁ t₂ τ hτ hs₁ hs₂ ht hord => ?_⟩
  have hA : 0 ≤ (∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖ :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨chosenD C R w₁ w₂ t₁ t₂ ℓ δ τ, fun i η hη => ?_, ?_⟩
  · filter_upwards [hD δ ε hδ hε t t₁ t₂ τ hτ hs₁ hs₂ ht hord i η hη] with p hp
    filter_upwards [hp] with N hN
    unfold chosenD
    split_ifs with h
    · exact hN _ h.choose_spec
    · exact mul_nonneg hη.le hA
  · filter_upwards [hplace δ ε hδ hε t t₁ t₂ τ hτ hs₁ hs₂ ht hord,
      hK t t₁ t₂ τ hτ hs₁ hs₂ ht hord] with p hp hkp
    filter_upwards [hp, hkp] with N hN hkN
    have hP : hN.choose.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ := hN.choose_spec
    obtain ⟨_, _, _, hσ0, hσ, hb⟩ := (smear_conn_cubic C N p (R.continuous N p) hN.choose.l
      hP.side hP.beta hP.two_le hP.even hP.seed hP.eight).choose_spec.choose_spec
    have f1 := hP.fit₁
    have f2 := hP.fit₂
    have f3 := hP.fit₃
    have key := hb w₁ w₂ t t₁ t₂ ht hN.choose.k hN.choose.v hN.choose.v' hN.choose.a
      hN.choose.j hN.choose.j' hN.choose.a hN.choose.bF hN.choose.aG hN.choose.bG
      hN.choose.bF hN.choose.cG
      (by unfold SlabPlacement.bG; omega)
      (by unfold SlabPlacement.j' SlabPlacement.aG SlabPlacement.bF; omega)
      (by unfold SlabPlacement.bF; omega)
      (by unfold SlabPlacement.aG SlabPlacement.bG; omega)
      (by unfold SlabPlacement.bF; omega)
      (by unfold SlabPlacement.cG; omega)
      hP.win₁ hP.win₂
    have hside : (C.period p : ℕ) * (C.denominator N : ℕ) = hN.choose.l + hN.choose.l + 1 + 1 :=
      congrArg PNat.val hP.side
    have hD0 : (0 : ℝ) < (C.denominator N : ℝ) := by exact_mod_cast (C.denominator N).pos
    have hsideR : ((C.period p : ℕ) : ℝ) * (C.denominator N : ℝ)
        = (hN.choose.l : ℝ) + hN.choose.l + 1 + 1 := by
      exact_mod_cast hside
    refine ⟨hN.choose.n, hN.choose.j, hN.choose.j', hN.choose.l, _,
      momF C N p w₁ t₁ hN.choose hP.side, momG C N p w₂ t₂ hN.choose hP.side,
      by have := hP.two_le; omega, hP.scale, hP.gap, hP.gap', hσ0, hσ, ?_,
      fun i k => (hkN hN.choose hP i k).1, fun i k => (hkN hN.choose hP i k).2, ?_⟩
    · apply le_of_eq
      rw [WilsonFamily.mesh]
      field_simp
      linarith
    · refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      have hc : chosenD C R w₁ w₂ t₁ t₂ ℓ δ τ i p N = remD C R N p hP i := by
        unfold chosenD
        rw [dif_pos hN]
      rw [hc]
      rfl

/-- **The times of a test are bounded**: its support is compact.

DERIVED: no numeral appears in the statement. -/
theorem time_bound_of_test {n : ℕ} (t : WilsonFamily.SeparatedTest n) :
    ∃ R : ℝ, ∀ y ∈ tsupport t, ∀ i, |time (y i)| ≤ R := by
  obtain ⟨R, hR⟩ := (t.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
  refine ⟨R, fun y hy i => ?_⟩
  have h1 := hR hy
  rw [mem_closedBall_zero_iff] at h1
  have h2 := PiLp.norm_apply_le y i
  have h3 := PiLp.norm_apply_le (y i) timeAxis
  rw [Real.norm_eq_abs] at h3
  exact h3.trans (h2.trans h1)

/-- **A time radius of the stencils of two token groups**: their stencils are finite.

DERIVED: `3` is their time axis; `0` the sign. -/
theorem stencil_radius {C : WilsonFamily g} (R : WilsonRegularity C) {n₁ n₂ : ℕ}
    (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) :
    ∃ r : ℤ, 0 ≤ r ∧ (∀ i, ∀ d ∈ stencilOf R (w₁ i), |d 3| ≤ r) ∧
      (∀ j, ∀ d ∈ stencilOf R (w₂ j), |d 3| ≤ r) := by
  have h1 : 0 ≤ ∑ i, ∑ d ∈ stencilOf R (w₁ i), |d 3| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ j, ∑ d ∈ stencilOf R (w₂ j), |d 3| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(∑ i, ∑ d ∈ stencilOf R (w₁ i), |d 3|) + ∑ j, ∑ d ∈ stencilOf R (w₂ j), |d 3|,
    add_nonneg h1 h2, fun i d hd => ?_, fun j d hd => ?_⟩
  · have e1 : |d 3| ≤ ∑ d' ∈ stencilOf R (w₁ i), |d' 3| :=
      Finset.single_le_sum (f := fun d' => |d' 3|) (fun _ _ => abs_nonneg _) hd
    have e2 : ∑ d' ∈ stencilOf R (w₁ i), |d' 3| ≤ ∑ i', ∑ d' ∈ stencilOf R (w₁ i'), |d' 3| :=
      Finset.single_le_sum (f := fun i' => ∑ d' ∈ stencilOf R (w₁ i'), |d' 3|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  · have e1 : |d 3| ≤ ∑ d' ∈ stencilOf R (w₂ j), |d' 3| :=
      Finset.single_le_sum (f := fun d' => |d' 3|) (fun _ _ => abs_nonneg _) hd
    have e2 : ∑ d' ∈ stencilOf R (w₂ j), |d' 3| ≤ ∑ j', ∑ d' ∈ stencilOf R (w₂ j'), |d' 3| :=
      Finset.single_le_sum (f := fun j' => ∑ d' ∈ stencilOf R (w₂ j'), |d' 3|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    linarith

set_option maxHeartbeats 3200000 in
/-- **A valid placement exists eventually** (compose-analysis §2a, §2b). For their family with
regularity `R` and their volume order tending to infinity: if eventually along the order and then
in the spacing their coupling is nonnegative and the seed holds on an even side `n ≥ 2` with
`n · mesh ≤ ℓ`, and every side `period · denominator` is even, then for every floor `δ`, `ε` and
every ordered tensor test, eventually along the order and then in the spacing a valid placement
exists. The choice: `r` a stencil time radius (`stencil_radius`), the times of the tests in
`[x₁, T]` and `[T + τ, X₂]` (`time_bound_of_test`), the windows
`lo₁ = ⌊x₁/mesh⌋ − r`, `hi₁ = ⌈T/mesh⌉ + r`, `lo₂ = ⌊(T+τ)/mesh⌋ − r`, `hi₂ = ⌈X₂/mesh⌉ + r`, the
transport `k ≡ −lo₁`, `a = ⌈δ/(8 mesh)⌉`, `v = ⌊(hi₁ − lo₁)/2⌋`, `v' = ⌊(hi₂ − lo₂)/2⌋`, the gap
`j` that starts the second slab at `lo₂ − lo₁`, and `2l + 2` their side; the windows are
`timeWindowLocal_smearIns` and `timeWindowLocal_mono`. The period is large once
`period ≥ 2(X₂ − x₁) + τ + δ + 4r + 40 + 8ℓ`, the spacing once `δ / mesh ≥ 4(2r + 12)`.

DERIVED: `16` and `1000` are the seed; `8` divides the floor into the separation and is the side
condition; `4` quarters the floor and doubles the radius; `2` halves and doubles; `40`, `12` the
slack of the floors and ceilings; `3` their time axis; `0` the first slice and the signs; `1` the
offsets. -/
theorem placement_exists (C : WilsonFamily g) (R : WilsonRegularity C) (order : ℕ → ℕ)
    (horder : Tendsto order atTop atTop) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token)
    (w₂ : Fin n₂ → C.Token) (ℓ : ℝ)
    (hseed : ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧ ∃ n : ℕ, 2 ≤ n ∧
      Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
      16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000)
    (hsides : ∀ p N, Even ((C.period p * C.denominator N : ℕ+) : ℕ)) :
    ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∃ P : SlabPlacement, P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ := by
  intro δ ε hδ _ t t₁ t₂ τ hτ _ _ _ hord
  obtain ⟨T, hT₁, hT₂⟩ := hord
  obtain ⟨r, hr0, hr₁, hr₂⟩ := stencil_radius R w₁ w₂
  obtain ⟨R₁, hR₁⟩ := time_bound_of_test t₁
  obtain ⟨R₂, hR₂⟩ := time_bound_of_test t₂
  set x₁ : ℝ := min (-R₁) T with hx₁
  set X₂ : ℝ := max R₂ (T + τ) with hX₂
  have hx₁T : x₁ ≤ T := min_le_right _ _
  have hX₂T : T + τ ≤ X₂ := le_max_right _ _
  have hper : ∀ᶠ p in Filter.map order atTop,
      2 * (X₂ - x₁) + τ + δ + 4 * (r : ℝ) + 40 + 8 * ℓ ≤ ((C.period p : ℕ) : ℝ) :=
    Filter.eventually_map.2 ((tendsto_natCast_atTop_atTop.comp
      (C.periodStrict.tendsto_atTop.comp horder)).eventually_ge_atTop _)
  have hden : ∀ᶠ N in atTop, 4 * (2 * (r : ℝ) + 12) / δ ≤ ((C.denominator N : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp C.denominatorStrict.tendsto_atTop).eventually_ge_atTop _
  filter_upwards [hseed, hper] with p hsp hpp
  filter_upwards [hsp, hden] with N hsN hdN
  obtain ⟨hβ, n, hn2, hne, hnm, hns⟩ := hsN
  -- the spacing and the side
  have hD1 : (1 : ℝ) ≤ ((C.denominator N : ℕ) : ℝ) := by exact_mod_cast (C.denominator N).pos
  have hDpos : (0 : ℝ) < ((C.denominator N : ℕ) : ℝ) := by linarith
  have hP1 : 1 ≤ (C.period p : ℕ) := (C.period p).pos
  have hLv : ((C.period p * C.denominator N : ℕ+) : ℕ) = (C.period p : ℕ) * (C.denominator N : ℕ) :=
    PNat.mul_coe _ _
  obtain ⟨h, hh⟩ := hsides p N
  have hDN1 : 1 ≤ (C.denominator N : ℕ) := (C.denominator N).pos
  have hL1 : 1 ≤ (C.period p : ℕ) * (C.denominator N : ℕ) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have hh1 : 1 ≤ h := by omega
  -- the δ-dependence of the spacing
  have hδD : 4 * (2 * (r : ℝ) + 12) ≤ δ * ((C.denominator N : ℕ) : ℝ) := by
    rw [div_le_iff₀ hδ] at hdN; linarith
  -- ℓ is positive
  have hmeshpos : 0 < C.mesh N := inv_pos.2 hDpos
  have hℓ : 0 < ℓ := lt_of_lt_of_le (mul_pos (by exact_mod_cast (show 0 < n by omega)) hmeshpos) hnm
  -- the integers
  set D : ℝ := ((C.denominator N : ℕ) : ℝ) with hDdef
  set lo₁ : ℤ := ⌊x₁ * D⌋ - r with hlo₁
  set hi₁ : ℤ := ⌈T * D⌉ + r with hhi₁
  set lo₂ : ℤ := ⌊(T + τ) * D⌋ - r with hlo₂
  set hi₂ : ℤ := ⌈X₂ * D⌉ + r with hhi₂
  set aI : ℤ := ⌈δ * D / 8⌉ with haI
  have f1 := Int.floor_le (x₁ * D)
  have f1' := Int.lt_floor_add_one (x₁ * D)
  have c1 := Int.le_ceil (T * D)
  have c1' := Int.ceil_lt_add_one (T * D)
  have f2 := Int.floor_le ((T + τ) * D)
  have f2' := Int.lt_floor_add_one ((T + τ) * D)
  have c2 := Int.le_ceil (X₂ * D)
  have c2' := Int.ceil_lt_add_one (X₂ * D)
  have ca := Int.le_ceil (δ * D / 8)
  have ca' := Int.ceil_lt_add_one (δ * D / 8)
  have hxT : x₁ * D ≤ T * D := mul_le_mul_of_nonneg_right hx₁T hDpos.le
  have hXT : (T + τ) * D ≤ X₂ * D := mul_le_mul_of_nonneg_right hX₂T hDpos.le
  have hτD : δ * D ≤ τ * D := mul_le_mul_of_nonneg_right hτ hDpos.le
  have hδpos : 0 < δ * D := mul_pos hδ hDpos
  -- integer facts
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have Z1 : lo₁ ≤ hi₁ := by
    have : ((lo₁ : ℤ) : ℝ) < (hi₁ : ℝ) + 1 := by rw [hlo₁, hhi₁]; push_cast; linarith
    exact_mod_cast (Int.lt_add_one_iff.mp (by exact_mod_cast this))
  have Zgap : 2 * aI + 5 ≤ lo₂ - hi₁ := by
    have : ((2 * aI + 5 : ℤ) : ℝ) < ((lo₂ - hi₁ : ℤ) : ℝ) + 1 := by
      rw [hlo₂, hhi₁, haI]; push_cast
      have : (T + τ) * D = T * D + τ * D := by ring
      nlinarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  have Z2 : lo₂ ≤ hi₂ := by
    have : ((lo₂ : ℤ) : ℝ) < (hi₂ : ℝ) + 1 := by rw [hlo₂, hhi₂]; push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  have ZaI : 0 ≤ aI := by
    have : (0 : ℝ) < (aI : ℝ) + 1 := by rw [haI]; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  have hPD : ((C.period p : ℕ) : ℝ) * D = ((h + h : ℕ) : ℝ) := by
    rw [hDdef]; exact_mod_cast (hLv.symm.trans hh)
  have hpp' : (2 * (X₂ - x₁) + τ + δ + 4 * (r : ℝ) + 40 + 8 * ℓ) * D
      ≤ ((C.period p : ℕ) : ℝ) * D := mul_le_mul_of_nonneg_right hpp hDpos.le
  have hX₂x₁ : 0 ≤ X₂ - x₁ := by linarith
  have Zfit : hi₂ - lo₁ + 2 * aI + 10 ≤ (h : ℤ) - 1 := by
    have : ((hi₂ - lo₁ + 2 * aI + 10 : ℤ) : ℝ) < ((h : ℤ) - 1 : ℝ) + 1 := by
      rw [hhi₂, hlo₁, haI]; push_cast
      have e : ((h + h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
      rw [e] at hPD
      nlinarith [mul_le_mul_of_nonneg_left hD1 (by linarith : (0 : ℝ) ≤ 4 * r + 40 + τ),
        mul_le_mul_of_nonneg_left hD1 (by linarith : (0 : ℝ) ≤ 8 * ℓ),
        mul_nonneg hX₂x₁ hDpos.le]
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  -- the naturals
  set m₁ : ℕ := (hi₁ - lo₁).toNat with hm₁
  set s₂ : ℕ := (lo₂ + -lo₁).toNat with hs₂
  set m₂ : ℕ := (hi₂ - lo₂).toNat with hm₂
  set a : ℕ := aI.toNat with ha
  have em₁ : (m₁ : ℤ) = hi₁ - lo₁ := Int.toNat_of_nonneg (by omega)
  have es₂ : (s₂ : ℤ) = lo₂ - lo₁ := by rw [hs₂, Int.toNat_of_nonneg (by omega)]; ring
  have em₂ : (m₂ : ℤ) = hi₂ - lo₂ := Int.toNat_of_nonneg (by omega)
  have ea : (a : ℤ) = aI := Int.toNat_of_nonneg ZaI
  set v : ℕ := m₁ / 2 with hv
  set v' : ℕ := m₂ / 2 with hv'
  set j : ℕ := s₂ - (v + v + 2) - (a + a + 3) with hj
  set l : ℕ := h - 1 with hl
  set K : ℤ := -lo₁ with hK
  have hLpos : (0 : ℤ) < (((C.period p * C.denominator N : ℕ+) : ℕ) : ℤ) := by
    exact_mod_cast (C.period p * C.denominator N).pos
  set k : ℕ := (K % (((C.period p * C.denominator N : ℕ+) : ℕ) : ℤ)).toNat with hk
  have hkK : ((k : ℕ) : ZMod (C.period p * C.denominator N : ℕ+).val) = (K : ZMod _) := by
    rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hLpos.ne'),
      ZMod.intCast_mod]
  have hLeq : ((C.period p * C.denominator N : ℕ+) : ℕ) = l + l + 2 := by
    rw [hLv]; omega
  -- the two windows
  have hw₁ := timeWindowLocal_smearIns g R N p w₁ t₁ r hr₁ x₁ T
    (fun y hy i => ⟨0, by
      have := hR₁ y hy i
      have := hT₁ y hy i
      simp only [Int.cast_zero, zero_mul, add_zero]
      exact ⟨(min_le_left _ _).trans (by linarith [neg_abs_le (time (y i))]), this⟩⟩)
    lo₁ hi₁ (by rw [hlo₁]; push_cast; linarith) (by rw [hhi₁]; push_cast; linarith) k K
    (by omega) hkK (by
      have : (lo₁ + K).toNat = 0 := by rw [hK]; simp
      rw [this, hLeq]; omega)
  have hw₂ := timeWindowLocal_smearIns g R N p w₂ t₂ r hr₂ (T + τ) X₂
    (fun z hz j' => ⟨0, by
      have := hR₂ z hz j'
      have := hT₂ z hz j'
      simp only [Int.cast_zero, zero_mul, add_zero]
      exact ⟨this, (le_abs_self _).trans (by linarith [le_max_left R₂ (T + τ)])⟩⟩)
    lo₂ hi₂ (by rw [hlo₂]; push_cast; linarith) (by rw [hhi₂]; push_cast; linarith) k K
    (by omega) hkK (by rw [hLeq]; omega)
  refine ⟨⟨n, k, l, v, v', a, j⟩, ?_⟩
  have hsP : C.period p * C.denominator N = sideP l := PNat.eq (by
    show ((C.period p * C.denominator N : ℕ+) : ℕ) = l + l + 1 + 1
    rw [hLeq])
  have hj1 : ((j : ℤ) + 1 : ℤ) ≥ lo₂ - hi₁ - 2 * aI - 4 := by omega
  have hjR : ((j : ℝ) + 1) ≥ ((lo₂ - hi₁ - 2 * aI - 4 : ℤ) : ℝ) := by exact_mod_cast hj1
  refine
    { side := hsP
      beta := hβ
      two_le := hn2
      even := hne
      seed := hns
      scale := hnm
      eight := ?_
      fit₁ := by dsimp only; omega
      fit₂ := by dsimp only; omega
      fit₃ := by dsimp only; omega
      win₁ := ?_
      win₂ := ?_
      gap := ?_
      gap' := ?_
      sep := ?_ }
  · dsimp only
    have h8 : (8 * (n : ℝ)) ≤ ((C.period p : ℕ) : ℝ) * D := by
      have hn' : (n : ℝ) ≤ ℓ * D := by
        have := mul_le_mul_of_nonneg_right hnm hDpos.le
        rw [WilsonFamily.mesh, mul_assoc, inv_mul_cancel₀ hDpos.ne', mul_one] at this
        exact this
      nlinarith [mul_le_mul_of_nonneg_right
        (show 8 * ℓ ≤ ((C.period p : ℕ) : ℝ) by nlinarith) hDpos.le]
    rw [hPD] at h8
    have : 8 * n ≤ h + h := by exact_mod_cast h8
    omega
  · dsimp only
    exact timeWindowLocal_mono g _ hw₁ (Nat.zero_le _) (by
      have : (lo₁ + K).toNat = 0 := by rw [hK]; simp
      rw [this]; omega)
  · dsimp only
    exact timeWindowLocal_mono g _ hw₂ (by unfold SlabPlacement.start; dsimp only; omega)
      (by unfold SlabPlacement.start; dsimp only; omega)
  · dsimp only
    rw [WilsonFamily.mesh, ← div_eq_mul_inv, le_div_iff₀ hDpos]
    push_cast at hjR
    rw [hlo₂, hhi₁, haI] at hjR
    push_cast at hjR
    have : (T + τ) * D = T * D + τ * D := by ring
    nlinarith
  · have hj'1 : ((SlabPlacement.j' ⟨n, k, l, v, v', a, j⟩ : ℕ) : ℤ) + 1
        ≥ (l + l + 2 : ℤ) - (hi₂ - lo₁) - 2 * aI - 4 := by
      unfold SlabPlacement.j'; dsimp only; omega
    have hj'R : ((SlabPlacement.j' ⟨n, k, l, v, v', a, j⟩ : ℕ) : ℝ) + 1
        ≥ (((l + l + 2 : ℕ) : ℤ) - (hi₂ - lo₁) - 2 * aI - 4 : ℤ) := by
      exact_mod_cast hj'1
    rw [WilsonFamily.mesh, ← div_eq_mul_inv, le_div_iff₀ hDpos]
    have hl2 : ((l + l + 2 : ℕ) : ℝ) = ((C.period p : ℕ) : ℝ) * D := by
      rw [hPD]; push_cast; rw [hl]; push_cast [Nat.cast_sub hh1]; ring
    rw [hhi₂, hlo₁, haI] at hj'R
    push_cast at hj'R hl2
    nlinarith [mul_le_mul_of_nonneg_left hD1 (by linarith : (0 : ℝ) ≤ 4 * r + 40),
      mul_nonneg hX₂x₁ hDpos.le]
  · dsimp only
    rw [WilsonFamily.mesh, ← div_eq_mul_inv, le_div_iff₀ hDpos]
    have : (a : ℝ) = (aI : ℝ) := by exact_mod_cast ea
    rw [this]
    linarith

/-- **The floored (U) at the seed's rate from the seed, the sides, the reflected-moment bound and
the vanishing excited–excited terms.** For their family with regularity `R`, their volume order
tending to infinity, `ℓ > 0`, the seed with `n · mesh ≤ ℓ` eventually along the order and then in
the spacing, even sides, and the inputs (K₀) and (D) of `cubicForm_of_inputs`:
`UniformDecayFrom C order w₁ w₂ (log 2 / ℓ)`. It is `cubicForm_of_inputs` with the placements of
`placement_exists`, then `OpenAIBridgeCompose.uniformDecayFrom_of_cubicForm`.

DERIVED: `16` and `1000` are the seed; `2` the base of the rate and the halved coupling; `4` the
number of real pairs; `3` the number of moments; `0` the signs. -/
theorem uniformDecayFrom_of_seed (C : WilsonFamily g) (R : WilsonRegularity C) (order : ℕ → ℕ)
    (horder : Tendsto order atTop atTop) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token)
    (w₂ : Fin n₂ → C.Token) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hseed : ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧ ∃ n : ℕ, 2 ≤ n ∧
      Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
      16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000)
    (hsides : ∀ p N, Even ((C.period p * C.denominator N : ℕ+) : ℕ))
    (hK₀ : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) (i : Fin 4) (k : Fin 3),
            (0 ≤ momF C N p w₁ t₁ P hP.side i k ∧
              momF C N p w₁ t₁ P hP.side i k ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2) ∧
            (0 ≤ momG C N p w₂ t₂ P hP.side i k ∧
              momG C N p w₂ t₂ P hP.side i k ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2))
    (hD : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ (i : Fin 4) (η : ℝ), 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ),
            remD C R N p hP i ≤ η * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) :
    UniformDecayFrom C order w₁ w₂ (Real.log 2 / ℓ) :=
  uniformDecayFrom_of_cubicForm hℓ horder
    (cubicForm_of_inputs C R order w₁ w₂ ℓ
      (placement_exists C R order horder w₁ w₂ ℓ hseed hsides) hK₀ hD)

end Assembly

/-! ## 15. Reflection positivity of the reflected moments -/

section Positivity

open MassGap.KernelPower MassGap.SlabKernelOperator MassGap.OpenAIBridgeCluster
  MassGap.OpenAIBridgeSlab MassGap.OpenAIBridgeRP MassGap.OpenAIBridgeCubic
  MassGap.OpenAIBridgeCompose MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.CompactGauge MassGap.HiddenChain MassGap.OpenAIBridgeGroups MassGap.OpenAILink

set_option maxHeartbeats 1600000 in
/-- **The reflected moments of a slab observable are nonnegative under their law.** For a bounded
measurable slab observable `f` of width `2v + 2` on the cubic torus of side `2l + 2` with
`2v + 2 + a + b + 1 = l`, both `⟨f₀ (θf)_{2v+2+2a+2}⟩` and `⟨(θf)₀ f_{2v+2+2a+2}⟩` under their law
at `β ≥ 0` are nonnegative: each is `Tr(F K^{2a+2} Fᵀ K^{2b+2}) / Tr K^{2l+2}` with `F` the slab
kernel (`OpenAIBridgeCubic.expect_pair_eqG`, `OpenAIBridgeRP.slabKer_rev_wtG`), the numerator is
`‖K^{b+1} F K^{a+1}‖²_HS ≥ 0` (`OpenAIBridgeRP.hs_sand_eq2`, reflection positivity in transfer form)
and the denominator is the partition function, positive.

DERIVED: `2` doubles the widths and separations and halves their coupling; `0` the first slice and
the sign; `1` the offsets. -/
theorem reflMoment_nonneg (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure] {β : ℝ} (hβ : 0 ≤ β) (l v a b : ℕ)
    (hl : v + v + 2 + a + b + 1 = l) (f : SlabObs g l)
    (hfm : Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
      × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) => f r.1 r.2))
    {B : ℝ} (hfb : ∀ V A, |f V A| ≤ B) (hf : LocalUpTo (v + v + 2) f) :
    0 ≤ ∫ V, readAt l f 0 V * readAt l (reflO l v f) (v + v + 2 + (a + a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) ∧
      0 ≤ ∫ V, readAt l (reflO l v f) 0 V * readAt l f (v + v + 2 + (a + a + 2)) V
        ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) := by
  have e : ∀ F : (RLink (fun _ : Fin 4 => l + l + 1 + 1) → g.image) → ℝ,
      (sysRG g.image (fun _ : Fin 4 => l + l + 1 + 1)).expect (probHaar g.image) (β / 2) F
        = ∫ V, F ((OpenAIConfig.configEquiv (sideP l)).symm V)
            ∂(OpenAIConfig.wilsonLaw g (sideP l) β μ) := by
    intro F
    have h1 := expect_eq_openAILawG g μ (sideP l) (β / 2)
      (fun V => F ((OpenAIConfig.configEquiv (sideP l)).symm V))
    simp only [MeasurableEquiv.symm_apply_apply, show 2 * (β / 2) = β by ring] at h1
    exact h1
  have hβ2 : 0 ≤ β / 2 := by linarith
  have hι : Measurable (MeasurableEquiv.piCongrRight
      (fun _ : TT 0 (TorusChain.Tc (l + l + 1)) => MeasurableEquiv.inv g.image)) :=
    (MeasurableEquiv.piCongrRight _).measurable
  have hf1 : LocalUpTo (v + v + 1 + 1) f := hf
  have hk : Bdd (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2)) := bdd_kTG hβ2
  have hsym : ∀ x y, kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2) x y
      = kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2) y x := kTG_symm (β / 2)
  have hw := TorusChainG.wmeas_wtG (G := g.image) (M := l + l + 1) (β / 2)
  have hwb := TorusChainG.abs_wtG_le (G := g.image) (M := l + l + 1) hβ2
  have hF := bdd_slabKer (μ := hSG g.image 0 (TorusChain.Tc (l + l + 1)))
    (ν := hAG g.image 0 (TorusChain.Tc (l + l + 1))) hw hwb (v + v + 1) hfm hfb
  have hZ : 0 < trPow (hSG g.image 0 (TorusChain.Tc (l + l + 1)))
      (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2)) (l + l + 1) := by
    rw [← ZRG_eq_trPowG g.image hβ2 _ _ rfl]
    exact GaugeWilson.wilsonSystemG_partition_pos _ _
  constructor
  · have E := expect_pair_eqG hβ2 (M := l + l + 1) (m := v + v + 1) (m' := v + v + 1)
      (p := a + a + 1) (q := b + b + 1) (by omega) hfm (measurable_revG hι (v + v + 1) hfm)
      hfb (abs_revG_le _ (v + v + 1) hfb) hf1 (localUpTo_revG _ (v + v + 1) hf1)
    rw [slabKer_rev_wtG hβ2 (v + v + 1) hfm hfb,
      ← hs_sand_eq2 (μ := hSG g.image 0 (TorusChain.Tc (l + l + 1))) hk hsym hF a b,
      show v + v + 1 + 1 + (a + a + 1 + 1) = v + v + 2 + (a + a + 2) by omega] at E
    have E2 := (e _).symm.trans E
    exact le_of_le_of_eq (div_nonneg (hs_nonneg _) hZ.le) E2.symm
  · have E := expect_pair_eqG hβ2 (M := l + l + 1) (m := v + v + 1) (m' := v + v + 1)
      (p := a + a + 1) (q := b + b + 1) (by omega) (measurable_revG hι (v + v + 1) hfm) hfm
      (abs_revG_le _ (v + v + 1) hfb) hfb (localUpTo_revG _ (v + v + 1) hf1) hf1
    have h' : trK (hSG g.image 0 (TorusChain.Tc (l + l + 1)))
        (kTG g.image 0 (TorusChain.Tc (l + l + 1)) (β / 2))
        (tp (slabKer (hSG g.image 0 (TorusChain.Tc (l + l + 1)))
          (hAG g.image 0 (TorusChain.Tc (l + l + 1))) (TorusChainG.wtG g.image (l + l + 1) (β / 2))
          (v + v + 1) f))
        (slabKer (hSG g.image 0 (TorusChain.Tc (l + l + 1)))
          (hAG g.image 0 (TorusChain.Tc (l + l + 1))) (TorusChainG.wtG g.image (l + l + 1) (β / 2))
          (v + v + 1) f) (a + a + 1) (b + b + 1)
        = hs (hSG g.image 0 (TorusChain.Tc (l + l + 1))) _ :=
      (hs_sand_eq2 (μ := hSG g.image 0 (TorusChain.Tc (l + l + 1))) hk hsym (bdd_tp hF) a b).symm
    rw [slabKer_rev_wtG hβ2 (v + v + 1) hfm hfb, h',
      show v + v + 1 + 1 + (a + a + 1 + 1) = v + v + 2 + (a + a + 2) by omega] at E
    have E2 := (e _).symm.trans E
    exact le_of_le_of_eq (div_nonneg (hs_nonneg _) hZ.le) E2.symm

variable {g : OpenAIConfig.GaugeGroup}

/-- The real part maps of the four pairs, first factor.

DERIVED: `4` is the number of pairs. -/
noncomputable def partF : Fin 4 → ℂ → ℝ := ![Complex.re, Complex.im, Complex.re, Complex.im]

/-- The real part maps of the four pairs, second factor.

DERIVED: `4` is the number of pairs. -/
noncomputable def partG : Fin 4 → ℂ → ℝ := ![Complex.re, Complex.im, Complex.im, Complex.re]

/-- `reImF` is `partF` after the observable.

DERIVED: `4` is the number of pairs. -/
theorem reImF_apply {X : Type*} (F : X → ℂ) (i : Fin 4) (x : X) :
    reImF F i x = partF i (F x) := by
  fin_cases i <;> rfl

/-- `reImG` is `partG` after the observable.

DERIVED: `4` is the number of pairs. -/
theorem reImG_apply {X : Type*} (F : X → ℂ) (i : Fin 4) (x : X) :
    reImG F i x = partG i (F x) := by
  fin_cases i <;> rfl

/-- The part maps are continuous and bounded by the modulus.

DERIVED: `4` is the number of pairs. -/
theorem part_facts (i : Fin 4) :
    Continuous (partF i) ∧ Continuous (partG i) ∧ (∀ z, |partF i z| ≤ ‖z‖) ∧
      ∀ z, |partG i z| ≤ ‖z‖ := by
  fin_cases i
  · exact ⟨Complex.continuous_re, Complex.continuous_re, Complex.abs_re_le_norm,
      Complex.abs_re_le_norm⟩
  · exact ⟨Complex.continuous_im, Complex.continuous_im, Complex.abs_im_le_norm,
      Complex.abs_im_le_norm⟩
  · exact ⟨Complex.continuous_re, Complex.continuous_im, Complex.abs_re_le_norm,
      Complex.abs_im_le_norm⟩
  · exact ⟨Complex.continuous_im, Complex.continuous_re, Complex.abs_im_le_norm,
      Complex.abs_re_le_norm⟩

/-- **The slab observable of a part of a continuous window-local observable** is measurable,
bounded and `LocalUpTo` the window's width.

DERIVED: `1` is the offset of the side. -/
theorem slabOf_part_facts (l s m : ℕ) (F : OpenAIConfig.Configuration g (sideP l) → ℂ)
    (hF : Continuous F) (hw : WindowLocal l s m (fun U => F (OpenAIConfig.configEquiv (sideP l) U)))
    (κ : ℂ → ℝ) (hκ : Continuous κ) (hκb : ∀ z, |κ z| ≤ ‖z‖) :
    Measurable (fun r : (ℕ → SpT 0 (TorusChain.Tc (l + l + 1)) → g.image)
        × (ℕ → TT 0 (TorusChain.Tc (l + l + 1)) → g.image) =>
          slabOf l s (fun U => κ (F (OpenAIConfig.configEquiv (sideP l) U))) r.1 r.2) ∧
      (∃ B : ℝ, ∀ V A, |slabOf l s (fun U => κ (F (OpenAIConfig.configEquiv (sideP l) U))) V A|
        ≤ B) ∧
      LocalUpTo m (slabOf l s (fun U => κ (F (OpenAIConfig.configEquiv (sideP l) U)))) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨measurable_slabOf l s ((hκ.comp hF).measurable.comp
    (OpenAIConfig.configEquiv (sideP l)).measurable), ⟨B, fun V A => ?_⟩,
    localUpTo_slabOf l (windowLocal_comp hw κ)⟩
  exact (hκb _).trans (hB _ (Set.mem_univ _))

/-- **The six reflected moments of a valid placement are nonnegative** (reflection positivity,
`reflMoment_nonneg`), for their family with regularity `R`.

DERIVED: `3` is the number of moments; `4` the number of real pairs. -/
theorem moments_nonneg (C : WilsonFamily g) (R : WilsonRegularity C) (N p : ℕ) {n₁ n₂ : ℕ}
    {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token} {t₁ : WilsonFamily.SeparatedTest n₁}
    {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ} {P : SlabPlacement}
    (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) (i : Fin 4) (k : Fin 3) :
    0 ≤ momF C N p w₁ t₁ P hP.side i k ∧ 0 ≤ momG C N p w₂ t₂ P hP.side i k := by
  haveI := C.probability
  haveI := C.invariantHaar
  have f1 := hP.fit₁
  have f2 := hP.fit₂
  have hc₁ := continuous_toSide P.l hP.side
    ((continuous_smearIns C N p (R.continuous N p) w₁ t₁).comp (continuous_transport g _ P.k))
  have hc₂ := continuous_toSide P.l hP.side
    ((continuous_smearIns C N p (R.continuous N p) w₂ t₂).comp (continuous_transport g _ P.k))
  have hw₁ := windowLocal_of_timeWindowLocal g P.l 0 _ (timeWindowLocal_toSide P.l hP.side hP.win₁)
  have hw₂ := windowLocal_of_timeWindowLocal g P.l _ _ (timeWindowLocal_toSide P.l hP.side hP.win₂)
  obtain ⟨cF, cG, bF, bG⟩ := part_facts i
  obtain ⟨m₁, ⟨B₁, hB₁⟩, l₁⟩ := slabOf_part_facts P.l 0 _ _ hc₁ hw₁ (partF i) cF bF
  obtain ⟨m₂, ⟨B₂, hB₂⟩, l₂⟩ := slabOf_part_facts P.l P.start _ _ hc₂ hw₂ (partG i) cG bG
  have eF : slabF C N p w₁ t₁ P hP.side i = slabOf P.l 0 (fun U => partF i (toSide P.l hP.side
      (fun V => smearIns C N p w₁ t₁ (transport g _ P.k V))
        (OpenAIConfig.configEquiv (sideP P.l) U))) := by
    unfold slabF
    simp only [reImF_apply]
  have eG : slabG C N p w₂ t₂ P hP.side i = slabOf P.l P.start (fun U => partG i (toSide P.l
      hP.side (fun V => smearIns C N p w₂ t₂ (transport g _ P.k V))
        (OpenAIConfig.configEquiv (sideP P.l) U))) := by
    unfold slabG
    simp only [reImG_apply]
  have hF1 := reflMoment_nonneg g C.haar hP.beta P.l P.v P.a P.bF
    (by unfold SlabPlacement.bF; omega) (slabF C N p w₁ t₁ P hP.side i) (eF ▸ m₁)
    (B := B₁) (eF ▸ hB₁) (eF ▸ l₁)
  have hG1 := reflMoment_nonneg g C.haar hP.beta P.l P.v' P.a P.cG
    (by unfold SlabPlacement.cG; omega) (slabG C N p w₂ t₂ P hP.side i) (eG ▸ m₂)
    (B := B₂) (eG ▸ hB₂) (eG ▸ l₂)
  have hG2 := reflMoment_nonneg g C.haar hP.beta P.l P.v' P.aG P.bG
    (by unfold SlabPlacement.aG SlabPlacement.bG; omega) (slabG C N p w₂ t₂ P hP.side i)
    (eG ▸ m₂) (B := B₂) (eG ▸ hB₂) (eG ▸ l₂)
  fin_cases k
  · exact ⟨hF1.1, hG1.2⟩
  · exact ⟨hF1.2, hG1.1⟩
  · exact ⟨hF1.1, hG2.1⟩

end Positivity

/-! ## 16. Their volume order tends to infinity -/

section Order

open MassGap.OpenAILink

/-- **Their volume order tends to infinity under their convergence**, when the family has a token:
a bump test at a point of time `R/2 + 1` is suitable eventually along the order, so the period
along the order eventually exceeds every `R`; the period is strictly increasing.

DERIVED: `1` is the radius of the bump, the number of points and the unit integral; `2` halves the
period. -/
theorem tendsto_order_of_converges {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g)
    {order : ℕ → ℕ} {S : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ}
    (hW : C.Converges order S) (v : C.Token) : Tendsto order atTop atTop := by
  have key : ∀ R : ℝ, ∀ᶠ k in atTop, R < ((C.period (order k) : ℕ) : ℝ) := by
    intro R
    set c : Points 1 := WithLp.toLp 2 fun _ => WithLp.toLp 2 fun _ => R / 2 + 1 with hc
    have hs : coordBox c 1 ⊆ WilsonFamily.separated 1 := fun y _ => mem_separated_one y
    obtain ⟨y, hy⟩ : ∃ y, bumpFun c 1 one_pos y ≠ 0 := by
      by_contra h
      have h1 := integral_bumpFun (n := 1) one_pos c 1 one_pos
      have h0 : (fun y => bumpFun c 1 one_pos y) = fun _ => 0 :=
        funext fun y => not_not.mp fun hne => h ⟨y, hne⟩
      rw [h0, integral_zero] at h1
      exact zero_ne_one h1
    filter_upwards [(hW 1 (fun _ => v) (bumpTest c 1 one_pos hs)).1] with k hk
    have hmem : y ∈ tsupport (bumpTest c 1 one_pos hs) := by
      apply subset_tsupport
      rw [Function.mem_support, bumpTest_apply]
      exact_mod_cast hy
    have h2 := (hk hmem 0 timeAxis).2
    have h3 := dist_lt_of_bumpFun_ne_zero hy 0
    have h4 := abs_time_sub_le (y 0) (c 0)
    have h5 : time (c 0) = R / 2 + 1 := rfl
    have h6 : time (y 0) = y 0 timeAxis := rfl
    rw [h5] at h4
    have := (abs_le.mp h4).1
    linarith
  refine Filter.tendsto_atTop.2 fun M => ?_
  filter_upwards [key ((C.period M : ℕ) : ℝ)] with k hk
  have h : (C.period M : ℕ) < (C.period (order k) : ℕ) := by exact_mod_cast hk
  exact (C.periodStrict.lt_iff_lt.mp h).le

end Order

/-! ## 17. The floored (U) from the seed, with positivity and the order discharged -/

section Capstone

open MassGap.OpenAILink MassGap.OpenAIBridgeCompose MassGap.RectWilsonG

variable {g : OpenAIConfig.GaugeGroup}

/-- **The floored (U) at the seed's rate, with the moments' sign and the order discharged.** As
`uniformDecayFrom_of_seed`, with the order tending to infinity from their convergence
(`tendsto_order_of_converges`, given a token) and the nonnegativity of the reflected moments from
reflection positivity (`moments_nonneg`): the input (K₀) is only the upper bound
`momF ≤ K₀ ‖t₁‖₁²`, `momG ≤ K₀ ‖t₂‖₁²`.

DERIVED: `16` and `1000` are the seed; `2` the base of the rate and the halved coupling; `4` the
number of real pairs; `3` the number of moments; `0` the signs. -/
theorem uniformDecayFrom_of_seed' (C : WilsonFamily g) (R : WilsonRegularity C) (order : ℕ → ℕ)
    {S : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ} (hW : C.Converges order S)
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (hn₁ : 0 < n₁) {ℓ : ℝ}
    (hℓ : 0 < ℓ)
    (hseed : ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧ ∃ n : ℕ, 2 ≤ n ∧
      Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
      16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000)
    (hsides : ∀ p N, Even ((C.period p * C.denominator N : ℕ+) : ℕ))
    (hK₀ : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) (i : Fin 4) (k : Fin 3),
            momF C N p w₁ t₁ P hP.side i k ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2 ∧
              momG C N p w₂ t₂ P hP.side i k ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2)
    (hD : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ (i : Fin 4) (η : ℝ), 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ),
            remD C R N p hP i ≤ η * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) :
    UniformDecayFrom C order w₁ w₂ (Real.log 2 / ℓ) :=
  uniformDecayFrom_of_seed C R order (tendsto_order_of_converges C hW (w₁ ⟨0, hn₁⟩)) w₁ w₂ hℓ
    hseed hsides
    (fun δ ε hδ hε => by
      obtain ⟨K₀, hK0, hK⟩ := hK₀ δ ε hδ hε
      refine ⟨K₀, hK0, fun t t₁ t₂ τ hτ hs₁ hs₂ ht hord => ?_⟩
      filter_upwards [hK t t₁ t₂ τ hτ hs₁ hs₂ ht hord] with p hp
      filter_upwards [hp] with N hN
      intro P hP i k
      exact ⟨⟨(moments_nonneg C R N p hP i k).1, (hN P hP i k).1⟩,
        ⟨(moments_nonneg C R N p hP i k).2, (hN P hP i k).2⟩⟩)
    hD

end Capstone

/-! ## 18. The reflected moments as smeared moments of `(w, Θ ∘ w)` -/

section Theta

open MassGap.OpenAILink MassGap.OpenAIBridgeCompose MassGap.RectWilson MassGap.RectWilsonG

variable {g : OpenAIConfig.GaugeGroup}

/-- Window locality passes to every function of the observable, in their coordinates.

DERIVED: no numeral appears in the statement. -/
theorem timeWindowLocal_comp {L : ℕ+} {β γ : Type*} {s m : ℕ}
    {O : OpenAIConfig.Configuration g L → β} (h : TimeWindowLocal g L s m O) (κ : β → γ) :
    TimeWindowLocal g L s m (fun V => κ (O V)) :=
  fun V V' hV => congrArg κ (h V V' hV)

/-- **The reflected observable keeps a window `s, …, s + w`**: reading on their reflection
`reflConfT (2s + w) 0` about the window's centre, `s + w < L`.

DERIVED: `0` is the transfer direction; `1` the unit step of a link; `2` doubles the offset. -/
theorem timeWindowLocal_reflConfT' {L : ℕ+} {β : Type*} (s w : ℕ) (hw : s + w < L.val)
    {O : OpenAIConfig.Configuration g L → β} (hO : TimeWindowLocal g L s w O) :
    TimeWindowLocal g L s w (fun V => O (reflConfT ((s + s + w : ℕ) : ZMod L.val) 0 V)) := by
  intro V V' hV
  apply hO
  intro y a hs hy ha
  have hy0 : (((y 0).val : ℕ) : ZMod L.val) = y 0 := ZMod.natCast_zmod_val (y 0)
  by_cases h0 : a = 0
  · subst h0
    have hlt : (y 0).val < s + w := ha.resolve_left (fun h => h rfl)
    have hr : (reflSite (((s + s + w : ℕ) : ZMod L.val) - 1) 0 y) 0
        = (((s + s + w - 1 - (y 0).val : ℕ)) : ZMod L.val) := by
      rw [reflSite, Function.update_self, Nat.cast_sub (by omega : (y 0).val ≤ s + s + w - 1),
        Nat.cast_sub (by omega : 1 ≤ s + s + w), Nat.cast_one, hy0]
    have hv : ((reflSite (((s + s + w : ℕ) : ZMod L.val) - 1) 0 y) 0).val
        = s + s + w - 1 - (y 0).val := by
      rw [hr, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [reflConfT, ↓reduceIte]
    congr 1
    apply hV
    · rw [hv]; omega
    · rw [hv]; omega
    · right; rw [hv]; omega
  · have hr : (reflSite ((s + s + w : ℕ) : ZMod L.val) 0 y) 0
        = (((s + s + w - (y 0).val : ℕ)) : ZMod L.val) := by
      rw [reflSite, Function.update_self, Nat.cast_sub (by omega : (y 0).val ≤ s + s + w), hy0]
    have hv : ((reflSite ((s + s + w : ℕ) : ZMod L.val) 0 y) 0).val = s + s + w - (y 0).val := by
      rw [hr, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [reflConfT, if_neg h0]
    apply hV
    · rw [hv]; omega
    · rw [hv]; omega
    · left; exact h0

/-- The slice `s'' + (x₀ − s)` of a site, read through `siteEquiv`, is the site moved by
`s'' + (2l + 2) − s` along `0`.

DERIVED: `0` is the transfer direction; `1`, `2` the offsets of the side. -/
theorem siteEquiv_join_shift' (l : ℕ) (x : WilsonHypercubic.Site 4 (sideP l)) (s'' s : ℕ)
    (hs : s ≤ (x 0 : ℕ)) (hsL : s ≤ l + l + 2)
    (h : s'' + ((x 0 : ℕ) - s) < TorusChain.Lc (l + l + 1) 0) :
    OpenAIConfig.siteEquiv (sideP l)
        (join (TorusChain.Lc (l + l + 1)) 0 ⟨s'' + ((x 0 : ℕ) - s), h⟩ (perp _ 0 x))
      = OpenAIConfig.siteEquiv (sideP l) x
        + Pi.single 0 ((s'' + (l + l + 2) - s : ℕ) : ZMod (sideP l).val) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Pi.add_apply, Pi.single_eq_same, OpenAIConfig.siteEquiv_apply,
      OpenAIConfig.siteEquiv_apply, join_self, finEquiv_eq_natCast, finEquiv_eq_natCast]
    show ((s'' + ((x 0 : ℕ) - s) : ℕ) : ZMod (sideP l).val) = _
    have e : s'' + ((x 0 : ℕ) - s) + (l + l + 2) = (x 0 : ℕ) + (s'' + (l + l + 2) - s) := by
      omega
    have hL0 : (((l + l + 2 : ℕ)) : ZMod (sideP l).val) = 0 := ZMod.natCast_self _
    have e' := congrArg (fun q : ℕ => (q : ZMod (sideP l).val)) e
    rw [Nat.cast_add (s'' + ((x 0 : ℕ) - s)) (l + l + 2), hL0, add_zero,
      Nat.cast_add ((x 0 : ℕ)) (s'' + (l + l + 2) - s)] at e'
    rw [e']
  · rw [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, OpenAIConfig.siteEquiv_apply,
      OpenAIConfig.siteEquiv_apply]
    congr 1
    exact join_ne _ _ ⟨j, hj⟩

/-- **The slice-shift lemma from a nonzero slice.** A slab observable built at slice `s` from an
observable local in the slices `s, …, s + m`, read at slice `s''` with `s'' + m < 2l + 2`, is the
observable of the configuration shifted by `s'' + (2l + 2) − s` slices (that is, by `s'' − s`
modulo the side).

DERIVED: `0` is the transfer direction; `1`, `2` the offsets of the side. -/
theorem readAt_slabOf_shift' (l s s'' m : ℕ) (hm : s'' + m < l + l + 2) (hsL : s ≤ l + l + 2)
    (O : OpenAIConfig.Configuration g (sideP l) → ℝ)
    (hO : TimeWindowLocal g (sideP l) s m O) (V : OpenAIConfig.Configuration g (sideP l)) :
    readAt l (slabOf l s (fun U => O (OpenAIConfig.configEquiv (sideP l) U))) s'' V
      = O ((pull (sideP l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[s'' + (l + l + 2) - s] V) := by
  apply hO
  intro y a hs hy ha
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv (sideP l)).surjective y
  have hv : (OpenAIConfig.siteEquiv (sideP l) x 0).val = (x 0 : ℕ) := val_finEquiv (sideP l) (x 0)
  rw [hv] at hs hy
  have hlt : s'' + ((x 0 : ℕ) - s) < TorusChain.Lc (l + l + 1) 0 := by
    simp only [TorusChain.Lc]; omega
  rw [OpenAIConfig.configEquiv_apply, pull_shift_iter_apply,
    ← siteEquiv_join_shift' l x s'' s hs hsL hlt]
  conv_rhs => rw [← MeasurableEquiv.apply_symm_apply (OpenAIConfig.configEquiv (sideP l)) V]
  rw [OpenAIConfig.configEquiv_apply]
  by_cases ha0 : a = 0
  · subst ha0
    dsimp only [recon]
    rw [dif_pos rfl]
    simp only [MassGap.OpenAIBridgeSlab.slabA, dif_pos hlt]
    rfl
  · dsimp only [recon]
    rw [dif_neg ha0]
    simp only [MassGap.OpenAIBridgeSlab.slabV, dif_pos hlt]
    rfl

/-- The reflected part maps of the first factor: `Re`, `−Im`, `Re`, `−Im`.

DERIVED: `4` is the number of pairs. -/
noncomputable def partFR : Fin 4 → ℂ → ℝ :=
  ![Complex.re, fun z => -z.im, Complex.re, fun z => -z.im]

/-- The reflected part maps of the second factor: `Re`, `−Im`, `−Im`, `Re`.

DERIVED: `4` is the number of pairs. -/
noncomputable def partGR : Fin 4 → ℂ → ℝ :=
  ![Complex.re, fun z => -z.im, fun z => -z.im, Complex.re]

/-- **`reflO` of the slab observable of a part is the slab observable of the reflected part** of
the reflected insertion, under `ReflectionClosed` (`reflO_slabOf_re`, `reflO_slabOf_im`).

DERIVED: `4` is the number of pairs; `2` doubles the width; `1` the offsets. -/
theorem reflO_slabOf_partF (l s v : ℕ) (hL : s + (v + v + 1) + 1 < l + l + 2)
    {F G : OpenAIConfig.Configuration g (sideP l) → ℂ}
    (hF : WindowLocal l s (v + v + 1 + 1) (fun U => F (OpenAIConfig.configEquiv (sideP l) U)))
    (hG : ReflectionClosed l s (v + v + 1) F G) (i : Fin 4) :
    reflO l v (slabOf l s (fun U => partF i (F (OpenAIConfig.configEquiv (sideP l) U))))
      = slabOf l s (fun U => partFR i (G (OpenAIConfig.configEquiv (sideP l) U))) := by
  fin_cases i
  · exact reflO_slabOf_re l s v hL hF hG
  · exact reflO_slabOf_im l s v hL hF hG
  · exact reflO_slabOf_re l s v hL hF hG
  · exact reflO_slabOf_im l s v hL hF hG

/-- The same for the parts of the second factor.

DERIVED: `4` is the number of pairs; `2` doubles the width; `1` the offsets. -/
theorem reflO_slabOf_partG (l s v : ℕ) (hL : s + (v + v + 1) + 1 < l + l + 2)
    {F G : OpenAIConfig.Configuration g (sideP l) → ℂ}
    (hF : WindowLocal l s (v + v + 1 + 1) (fun U => F (OpenAIConfig.configEquiv (sideP l) U)))
    (hG : ReflectionClosed l s (v + v + 1) F G) (i : Fin 4) :
    reflO l v (slabOf l s (fun U => partG i (F (OpenAIConfig.configEquiv (sideP l) U))))
      = slabOf l s (fun U => partGR i (G (OpenAIConfig.configEquiv (sideP l) U))) := by
  fin_cases i
  · exact reflO_slabOf_re l s v hL hF hG
  · exact reflO_slabOf_im l s v hL hF hG
  · exact reflO_slabOf_im l s v hL hF hG
  · exact reflO_slabOf_re l s v hL hF hG

/-- **A smeared moment of two observables on their side**: the expectation under their law of
`κ₁(A)` read through the transport after `q₁` shifts along `0` and `κ₂(B)` after `q₂` shifts.

DERIVED: `0` is the transfer direction. -/
noncomputable def pairMom (L : ℕ+) (β : ℝ) (μ : Measure g.image)
    (A B : OpenAIConfig.Configuration g L → ℂ) (κ₁ κ₂ : ℂ → ℝ) (k q₁ q₂ : ℕ) : ℝ :=
  ∫ V, κ₁ (A (transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V)))
    * κ₂ (B (transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V)))
    ∂(OpenAIConfig.wilsonLaw g L β μ)

/-- `pairMom` is read on the cubic side through `toSide`.

DERIVED: `1` is the offset of the side. -/
theorem pairMom_toSide {L : ℕ+} (l : ℕ) (hL : L = sideP l) (β : ℝ) (μ : Measure g.image)
    (A B : OpenAIConfig.Configuration g L → ℂ) (κ₁ κ₂ : ℂ → ℝ) (k q₁ q₂ : ℕ) :
    pairMom (sideP l) β μ (toSide l hL A) (toSide l hL B) κ₁ κ₂ k q₁ q₂
      = pairMom L β μ A B κ₁ κ₂ k q₁ q₂ := by
  subst hL
  rfl

/-- The plane of the first group's reflection: `2v + 2 − 2k`.

DERIVED: `2` doubles the width and the transport. -/
def SlabPlacement.plane₁ (P : SlabPlacement) : ℤ := ((P.v + P.v + 2 : ℕ) : ℤ) - 2 * P.k

/-- The plane of the second group's reflection: `2 · start + 2v' + 2 − 2k`.

DERIVED: `2` doubles the start, the width and the transport; `1` the offsets. -/
def SlabPlacement.plane₂ (P : SlabPlacement) : ℤ :=
  ((P.start + P.start + (P.v' + P.v' + 1) + 1 : ℕ) : ℤ) - 2 * P.k

set_option maxHeartbeats 3200000 in
/-- **The reflected moments of the first group are smeared moments of `(w₁, Θ ∘ w₁)`.** Under
`TokenReflection C Θ` and a test `tθ₁` with `ReflectedTest` at the plane `plane₁`, at a valid
placement: `momF i 0 = momF i 2 = pairMom (t₁) (tθ₁) (partF i) (partFR i) k 0 s₁` and
`momF i 1 = pairMom (tθ₁) (t₁) (partFR i) (partF i) k 0 s₁`, `s₁ = 2v + 2 + 2a + 2`.

DERIVED: `2` doubles the widths and separations; `0` the first slice; `3` the number of moments;
`4` the number of real pairs; `1` the offsets. -/
theorem momF_theta (C : WilsonFamily g) (N p : ℕ) {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token}
    {t₁ : WilsonFamily.SeparatedTest n₁} {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ}
    {P : SlabPlacement} (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ)
    (tθ₁ : WilsonFamily.SeparatedTest n₁)
    (htθ : ReflectedTest C N p ((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
      t₁ tθ₁) (i : Fin 4) :
    momF C N p w₁ t₁ P hP.side i 0
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₁ t₁)
          (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (partF i) (partFR i) P.k 0
          (P.v + P.v + 2 + (P.a + P.a + 2)) ∧
      momF C N p w₁ t₁ P hP.side i 1
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
          (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (smearIns C N p w₁ t₁) (partFR i) (partF i)
          P.k 0 (P.v + P.v + 2 + (P.a + P.a + 2)) ∧
      momF C N p w₁ t₁ P hP.side i 2
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₁ t₁)
          (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (partF i) (partFR i) P.k 0
          (P.v + P.v + 2 + (P.a + P.a + 2)) := by
  have f1 := hP.fit₁
  have f3 := hP.fit₃
  set F₁ := toSide P.l hP.side (smearIns C N p w₁ t₁) with hF₁
  set G₁ := toSide P.l hP.side (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) with hG₁
  set T := transport g (sideP P.l) P.k with hT
  have W1 : TimeWindowLocal g (sideP P.l) 0 (P.v + P.v + 2) (fun V => F₁ (T V)) := by
    have h := timeWindowLocal_toSide P.l hP.side hP.win₁
    rw [toSide_transport] at h
    exact h
  have hFG := toSide_reflect P.l hP.side P.plane₁
    (smearIns_reflect' hΘ N p w₁ t₁ tθ₁ _ htθ)
  have hc : ((P.plane₁ : ℤ) : ZMod (sideP P.l).val) + 2 * ((P.k : ℕ) : ZMod (sideP P.l).val)
      = (((0 + 0 + (P.v + P.v + 1) + 1 : ℕ)) : ZMod (sideP P.l).val) := by
    unfold SlabPlacement.plane₁; push_cast; ring
  have RC := reflectionClosed_of_reflConfT g P.l 0 (P.v + P.v + 1) P.k _ hc F₁ G₁ hFG W1
  have hw : P.v + P.v + 2 < (sideP P.l).val := by show _ < P.l + P.l + 1 + 1; omega
  have hGT : (fun V => G₁ (T V))
      = fun V => (starRingEnd ℂ) (F₁ (T (reflConfT ((P.v + P.v + 2 : ℕ) : ZMod (sideP P.l).val)
          0 V))) := by
    funext V
    have h1 := hFG (T V)
    rw [hT, reflConfT_transport, hc,
      show 0 + 0 + (P.v + P.v + 1) + 1 = P.v + P.v + 2 by omega] at h1
    exact h1
  have W2 : TimeWindowLocal g (sideP P.l) 0 (P.v + P.v + 2) (fun V => G₁ (T V)) := by
    rw [hGT]
    exact timeWindowLocal_comp (timeWindowLocal_reflConfT g (sideP P.l) (P.v + P.v + 2) hw W1)
      (starRingEnd ℂ)
  have WL1 := windowLocal_of_timeWindowLocal g P.l 0 (P.v + P.v + 2) W1
  have hslab : slabF C N p w₁ t₁ P hP.side i
      = slabOf P.l 0 (fun U => partF i (F₁ (T (OpenAIConfig.configEquiv (sideP P.l) U)))) := by
    unfold slabF
    rw [toSide_transport]
    simp only [reImF_apply]
    rfl
  have hrefl := reflO_slabOf_partF P.l 0 P.v (by omega) WL1 RC i
  have hm : P.v + P.v + 2 + (P.a + P.a + 2) + (P.v + P.v + 2) < P.l + P.l + 2 := by omega
  have p1 : ∀ V, readAt P.l (slabF C N p w₁ t₁ P hP.side i) 0 V
        * readAt P.l (reflO P.l P.v (slabF C N p w₁ t₁ P hP.side i))
          (P.v + P.v + 2 + (P.a + P.a + 2)) V
      = partF i (F₁ (T V)) * partFR i (G₁ (T ((pull (sideP P.l)
          (MassGap.ShiftInvG.shiftLinkPerm 0))^[P.v + P.v + 2 + (P.a + P.a + 2)] V))) := by
    intro V
    rw [hslab, hrefl, readAt_slabOf P.l (fun V => partF i (F₁ (T V)))
        (windowLocal_comp WL1 (partF i)),
      readAt_slabOf_shift g P.l _ _ hm (fun V => partFR i (G₁ (T V)))
        (timeWindowLocal_comp W2 (partFR i))]
  have p2 : ∀ V, readAt P.l (reflO P.l P.v (slabF C N p w₁ t₁ P hP.side i)) 0 V
        * readAt P.l (slabF C N p w₁ t₁ P hP.side i) (P.v + P.v + 2 + (P.a + P.a + 2)) V
      = partFR i (G₁ (T V)) * partF i (F₁ (T ((pull (sideP P.l)
          (MassGap.ShiftInvG.shiftLinkPerm 0))^[P.v + P.v + 2 + (P.a + P.a + 2)] V))) := by
    intro V
    rw [hslab, hrefl, readAt_slabOf P.l (fun V => partFR i (G₁ (T V)))
        (windowLocal_comp (windowLocal_of_timeWindowLocal g P.l 0 (P.v + P.v + 2) W2) (partFR i)),
      readAt_slabOf_shift g P.l _ _ hm (fun V => partF i (F₁ (T V)))
        (timeWindowLocal_comp W1 (partF i))]
  have I1 := integral_congr_ae (μ := OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)
    (Filter.Eventually.of_forall p1)
  have I2 := integral_congr_ae (μ := OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)
    (Filter.Eventually.of_forall p2)
  have e1 := pairMom_toSide P.l hP.side (C.beta N p) C.haar (smearIns C N p w₁ t₁)
    (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (partF i) (partFR i) P.k 0
    (P.v + P.v + 2 + (P.a + P.a + 2))
  have e2 := pairMom_toSide P.l hP.side (C.beta N p) C.haar
    (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (smearIns C N p w₁ t₁) (partFR i) (partF i) P.k 0
    (P.v + P.v + 2 + (P.a + P.a + 2))
  exact ⟨I1.trans e1, I2.trans e2, I1.trans e1⟩

set_option maxHeartbeats 3200000 in
/-- **The reflected moments of the second group are smeared moments of `(w₂, Θ ∘ w₂)`.** Under
`TokenReflection C Θ` and a test `tθ₂` with `ReflectedTest` at the plane `plane₂`, at a valid
placement, with `q₀ = 2l + 2 − start` (the second slab moved to slice `0`): `momG i 0` is
`pairMom (tθ₂) (t₂) (partGR i) (partG i) k q₀ (s₂ + q₀)`, `momG i 1` and `momG i 2` are
`pairMom (t₂) (tθ₂) (partG i) (partGR i) k q₀ (s + q₀)` at `s = 2v' + 2 + 2a + 2` and
`s = 2v' + 2 + 2a_G + 2`.

DERIVED: `2` doubles the widths, separations and the half-side; `0` the first slice; `3` the number
of moments; `4` the number of real pairs; `1` the offsets. -/
theorem momG_theta (C : WilsonFamily g) (N p : ℕ) {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token} {w₂ : Fin n₂ → C.Token}
    {t₁ : WilsonFamily.SeparatedTest n₁} {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ}
    {P : SlabPlacement} (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ)
    (tθ₂ : WilsonFamily.SeparatedTest n₂)
    (htθ : ReflectedTest C N p ((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
      t₂ tθ₂) (i : Fin 4) :
    momG C N p w₂ t₂ P hP.side i 0
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
          (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (smearIns C N p w₂ t₂) (partGR i) (partG i)
          P.k (0 + (P.l + P.l + 2) - P.start)
          (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start) ∧
      momG C N p w₂ t₂ P hP.side i 1
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₂ t₂)
          (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG i) (partGR i)
          P.k (0 + (P.l + P.l + 2) - P.start)
          (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start) ∧
      momG C N p w₂ t₂ P hP.side i 2
        = pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₂ t₂)
          (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG i) (partGR i)
          P.k (0 + (P.l + P.l + 2) - P.start)
          (P.v' + P.v' + 2 + (P.aG + P.aG + 2) + (P.l + P.l + 2) - P.start) := by
  have f1 := hP.fit₁
  have f2 := hP.fit₂
  have f3 := hP.fit₃
  have hstart : P.start = P.v + P.v + 2 + (P.a + P.j + P.a + 2 + 1) := rfl
  have haG : P.aG = P.l - (P.v' + P.v' + 2) - P.a - P.j - 2 := rfl
  set F₂ := toSide P.l hP.side (smearIns C N p w₂ t₂) with hF₂
  set G₂ := toSide P.l hP.side (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) with hG₂
  set T := transport g (sideP P.l) P.k with hT
  have W1 : TimeWindowLocal g (sideP P.l) P.start (P.v' + P.v' + 2) (fun V => F₂ (T V)) := by
    have h := timeWindowLocal_toSide P.l hP.side hP.win₂
    rw [toSide_transport] at h
    exact h
  have hFG := toSide_reflect P.l hP.side P.plane₂
    (smearIns_reflect' hΘ N p w₂ t₂ tθ₂ _ htθ)
  have hc : ((P.plane₂ : ℤ) : ZMod (sideP P.l).val) + 2 * ((P.k : ℕ) : ZMod (sideP P.l).val)
      = (((P.start + P.start + (P.v' + P.v' + 1) + 1 : ℕ)) : ZMod (sideP P.l).val) := by
    unfold SlabPlacement.plane₂; push_cast; ring
  have RC := reflectionClosed_of_reflConfT g P.l P.start (P.v' + P.v' + 1) P.k _ hc F₂ G₂ hFG W1
  have hw : P.start + (P.v' + P.v' + 2) < (sideP P.l).val := by
    show _ < P.l + P.l + 1 + 1; rw [hstart]; omega
  have hGT : (fun V => G₂ (T V))
      = fun V => (starRingEnd ℂ) (F₂ (T (reflConfT
          ((P.start + P.start + (P.v' + P.v' + 2) : ℕ) : ZMod (sideP P.l).val) 0 V))) := by
    funext V
    have h1 := hFG (T V)
    rw [hT, reflConfT_transport, hc,
      show P.start + P.start + (P.v' + P.v' + 1) + 1 = P.start + P.start + (P.v' + P.v' + 2) by
        omega] at h1
    exact h1
  have W2 : TimeWindowLocal g (sideP P.l) P.start (P.v' + P.v' + 2) (fun V => G₂ (T V)) := by
    rw [hGT]
    exact timeWindowLocal_comp
      (timeWindowLocal_reflConfT' P.start (P.v' + P.v' + 2) hw W1) (starRingEnd ℂ)
  have WL1 := windowLocal_of_timeWindowLocal g P.l P.start (P.v' + P.v' + 2) W1
  have WL2 := windowLocal_of_timeWindowLocal g P.l P.start (P.v' + P.v' + 2) W2
  have hslab : slabG C N p w₂ t₂ P hP.side i
      = slabOf P.l P.start
          (fun U => partG i (F₂ (T (OpenAIConfig.configEquiv (sideP P.l) U)))) := by
    unfold slabG
    rw [toSide_transport]
    simp only [reImG_apply]
    rfl
  have hrefl := reflO_slabOf_partG P.l P.start P.v' (by rw [hstart]; omega) WL1 RC i
  have hsL : P.start ≤ P.l + P.l + 2 := by rw [hstart]; omega
  have hm0 : 0 + (P.v' + P.v' + 2) < P.l + P.l + 2 := by omega
  have hm1 : P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.v' + P.v' + 2) < P.l + P.l + 2 := by omega
  have hm2 : P.v' + P.v' + 2 + (P.aG + P.aG + 2) + (P.v' + P.v' + 2) < P.l + P.l + 2 := by
    rw [haG]; omega
  have rF := fun (s'' : ℕ) (h : s'' + (P.v' + P.v' + 2) < P.l + P.l + 2) =>
    readAt_slabOf_shift' P.l P.start s'' (P.v' + P.v' + 2) h hsL (fun V => partG i (F₂ (T V)))
      (timeWindowLocal_comp W1 (partG i))
  have rG := fun (s'' : ℕ) (h : s'' + (P.v' + P.v' + 2) < P.l + P.l + 2) =>
    readAt_slabOf_shift' P.l P.start s'' (P.v' + P.v' + 2) h hsL (fun V => partGR i (G₂ (T V)))
      (timeWindowLocal_comp W2 (partGR i))
  have p0 : ∀ V, readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hP.side i)) 0 V
        * readAt P.l (slabG C N p w₂ t₂ P hP.side i) (P.v' + P.v' + 2 + (P.a + P.a + 2)) V
      = partGR i (G₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          0 + (P.l + P.l + 2) - P.start] V)))
        * partG i (F₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start] V))) := by
    intro V
    rw [hslab, hrefl, rG 0 hm0 V, rF _ hm1 V]
  have p1 : ∀ V, readAt P.l (slabG C N p w₂ t₂ P hP.side i) 0 V
        * readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hP.side i))
          (P.v' + P.v' + 2 + (P.a + P.a + 2)) V
      = partG i (F₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          0 + (P.l + P.l + 2) - P.start] V)))
        * partGR i (G₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start] V))) := by
    intro V
    rw [hslab, hrefl, rF 0 hm0 V, rG _ hm1 V]
  have p2 : ∀ V, readAt P.l (slabG C N p w₂ t₂ P hP.side i) 0 V
        * readAt P.l (reflO P.l P.v' (slabG C N p w₂ t₂ P hP.side i))
          (P.v' + P.v' + 2 + (P.aG + P.aG + 2)) V
      = partG i (F₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          0 + (P.l + P.l + 2) - P.start] V)))
        * partGR i (G₂ (T ((pull (sideP P.l) (MassGap.ShiftInvG.shiftLinkPerm 0))^[
          P.v' + P.v' + 2 + (P.aG + P.aG + 2) + (P.l + P.l + 2) - P.start] V))) := by
    intro V
    rw [hslab, hrefl, rF 0 hm0 V, rG _ hm2 V]
  have I0 := integral_congr_ae (μ := OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)
    (Filter.Eventually.of_forall p0)
  have I1 := integral_congr_ae (μ := OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)
    (Filter.Eventually.of_forall p1)
  have I2 := integral_congr_ae (μ := OpenAIConfig.wilsonLaw g (sideP P.l) (C.beta N p) C.haar)
    (Filter.Eventually.of_forall p2)
  refine ⟨I0.trans (pairMom_toSide P.l hP.side _ _ _ _ _ _ _ _ _),
    I1.trans (pairMom_toSide P.l hP.side _ _ _ _ _ _ _ _ _),
    I2.trans (pairMom_toSide P.l hP.side _ _ _ _ _ _ _ _ _)⟩

set_option maxHeartbeats 1600000 in
/-- **The floored (U) from the seed, the sides, the token reflection, the reflected-moment bound on
their smeared moments, and the vanishing excited–excited terms.** As `uniformDecayFrom_of_seed'`,
with the input (K₀) on the smeared moments of `(w, Θ ∘ w)`: for every valid placement and all tests
`tθ₁`, `tθ₂` that are `ReflectedTest`s of `t₁`, `t₂` at the placement's planes `plane₁`, `plane₂`,
the five `pairMom` readings are at most `K₀ ‖t‖₁²`; and an input that such tests exist. The
reflected moments `momF`, `momG` are these readings (`momF_theta`, `momG_theta`, under
`TokenReflection C Θ`).

DERIVED: `16` and `1000` are the seed; `2` the base of the rate, the halved coupling and doubles
the widths, separations and the half-side; `4` the number of real pairs; `3` the number of
moments; `0` the signs and the first slice; `1` the offsets. -/
theorem uniformDecayFrom_of_seed'' (C : WilsonFamily g) (R : WilsonRegularity C)
    (order : ℕ → ℕ) {S : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ} (hW : C.Converges order S)
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) (hn₁ : 0 < n₁) {ℓ : ℝ}
    (hℓ : 0 < ℓ)
    (hseed : ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧ ∃ n : ℕ, 2 ≤ n ∧
      Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
      16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000)
    (hsides : ∀ p N, Even ((C.period p * C.denominator N : ℕ+) : ℕ))
    (Θ : C.Token → C.Token) (hΘ : TokenReflection C Θ)
    (hθ : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement), P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ →
            (∃ tθ₁, ReflectedTest C N p
              ((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) t₁ tθ₁) ∧
            ∃ tθ₂, ReflectedTest C N p
              ((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) t₂ tθ₂)
    (hK₀ : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement), P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ →
          ∀ (tθ₁ : WilsonFamily.SeparatedTest n₁) (tθ₂ : WilsonFamily.SeparatedTest n₂),
            ReflectedTest C N p
              ((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) t₁ tθ₁ →
            ReflectedTest C N p
              ((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) t₂ tθ₂ →
            ∀ i : Fin 4,
              pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₁ t₁)
                  (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (partF i) (partFR i) P.k 0
                  (P.v + P.v + 2 + (P.a + P.a + 2)) ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2 ∧
              pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
                  (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (smearIns C N p w₁ t₁) (partFR i)
                  (partF i) P.k 0 (P.v + P.v + 2 + (P.a + P.a + 2)) ≤ K₀ * (∫ y, ‖t₁ y‖) ^ 2 ∧
              pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
                  (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (smearIns C N p w₂ t₂) (partGR i)
                  (partG i) P.k (0 + (P.l + P.l + 2) - P.start)
                  (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start)
                ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2 ∧
              pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₂ t₂)
                  (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG i) (partGR i)
                  P.k (0 + (P.l + P.l + 2) - P.start)
                  (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start)
                ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2 ∧
              pairMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w₂ t₂)
                  (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG i) (partGR i)
                  P.k (0 + (P.l + P.l + 2) - P.start)
                  (P.v' + P.v' + 2 + (P.aG + P.aG + 2) + (P.l + P.l + 2) - P.start)
                ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2)
    (hD : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ (t : WilsonFamily.SeparatedTest (n₁ + n₂)) (t₁ : WilsonFamily.SeparatedTest n₁)
        (t₂ : WilsonFamily.SeparatedTest n₂) (τ : ℝ), δ ≤ τ → GroupSep ε t₁ → GroupSep ε t₂ →
        (∀ y, t y = t₁ (leftPts y) * t₂ (rightPts y)) →
        (∃ T : ℝ, (∀ y ∈ tsupport t₁, ∀ i, time (y i) ≤ T) ∧
          ∀ z ∈ tsupport t₂, ∀ j, T + τ ≤ time (z j)) →
        ∀ (i : Fin 4) (η : ℝ), 0 < η → ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
          ∀ (P : SlabPlacement) (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ),
            remD C R N p hP i ≤ η * ((∫ y, ‖t₁ y‖) * ∫ y, ‖t₂ y‖)) :
    UniformDecayFrom C order w₁ w₂ (Real.log 2 / ℓ) :=
  uniformDecayFrom_of_seed' C R order hW w₁ w₂ hn₁ hℓ hseed hsides
    (fun δ ε hδ hε => by
      obtain ⟨K₀, hK0, hK⟩ := hK₀ δ ε hδ hε
      refine ⟨K₀, hK0, fun t t₁ t₂ τ hτ hs₁ hs₂ ht hord => ?_⟩
      filter_upwards [hK t t₁ t₂ τ hτ hs₁ hs₂ ht hord,
        hθ δ ε hδ hε t t₁ t₂ τ hτ hs₁ hs₂ ht hord] with p hp hq
      filter_upwards [hp, hq] with N hN hM
      intro P hP i k
      obtain ⟨⟨tθ₁, h₁⟩, ⟨tθ₂, h₂⟩⟩ := hM P hP
      obtain ⟨b1, b2, b3, b4, b5⟩ := hN P hP tθ₁ tθ₂ h₁ h₂ i
      obtain ⟨eF0, eF1, eF2⟩ := momF_theta C N p hΘ hP tθ₁ h₁ i
      obtain ⟨eG0, eG1, eG2⟩ := momG_theta C N p hΘ hP tθ₂ h₂ i
      fin_cases k
      · exact ⟨eF0 ▸ b1, eG0 ▸ b3⟩
      · exact ⟨eF1 ▸ b2, eG1 ▸ b4⟩
      · exact ⟨eF2 ▸ b1, eG2 ▸ b5⟩)
    hD

end Theta

end MassGap.OpenAIBridgeGlue

#print axioms MassGap.OpenAIBridgeGlue.pull_configEquiv
#print axioms MassGap.OpenAIBridgeGlue.integral_pull
#print axioms MassGap.OpenAIBridgeGlue.integral_pull_axis
#print axioms MassGap.OpenAIBridgeGlue.integral_pull_shift
#print axioms MassGap.OpenAIBridgeGlue.integral_pull_shift_iter
#print axioms MassGap.OpenAIBridgeGlue.isProbabilityMeasure_wilsonLaw
#print axioms MassGap.OpenAIBridgeGlue.norm_le_abs_re_add_abs_im
#print axioms MassGap.OpenAIBridgeGlue.norm_conn_le_four
#print axioms MassGap.OpenAIBridgeGlue.smear_eq_integral
#print axioms MassGap.OpenAIBridgeGlue.smear_append
#print axioms MassGap.OpenAIBridgeGlue.smear_conn_eq
#print axioms MassGap.OpenAIBridgeGlue.recon_slab
#print axioms MassGap.OpenAIBridgeGlue.localUpTo_slabOf
#print axioms MassGap.OpenAIBridgeGlue.readAt_slabOf
#print axioms MassGap.OpenAIBridgeGlue.measurable_recon
#print axioms MassGap.OpenAIBridgeGlue.measurable_slabOf
#print axioms MassGap.OpenAIBridgeGlue.windowLocal_comp
#print axioms MassGap.OpenAIBridgeGlue.openAI_slab_conn_cubic_complex
#print axioms MassGap.OpenAIBridgeGlue.pullEquiv_apply
#print axioms MassGap.OpenAIBridgeGlue.pull_apply
#print axioms MassGap.OpenAIBridgeGlue.pull_apply'
#print axioms MassGap.OpenAIBridgeGlue.continuous_pull
#print axioms MassGap.OpenAIBridgeGlue.measurePreserving_pull
#print axioms MassGap.OpenAIBridgeGlue.conn_comp
#print axioms MassGap.OpenAIBridgeGlue.continuous_transport
#print axioms MassGap.OpenAIBridgeGlue.measurePreserving_transport
#print axioms MassGap.OpenAIBridgeGlue.integrable_of_continuous
#print axioms MassGap.OpenAIBridgeGlue.continuous_smearIns
#print axioms MassGap.OpenAIBridgeGlue.smear_conn_eq_of_continuous
#print axioms MassGap.OpenAIBridgeGlue.revG_slabOf
#print axioms MassGap.OpenAIBridgeGlue.reflO_slabOf_re
#print axioms MassGap.OpenAIBridgeGlue.reflO_slabOf_im
#print axioms MassGap.OpenAIBridgeGlue.stencilLocal_of_regularity
#print axioms MassGap.OpenAIBridgeGlue.pull_axis_apply
#print axioms MassGap.OpenAIBridgeGlue.pull_shift_apply
#print axioms MassGap.OpenAIBridgeGlue.transport_apply
#print axioms MassGap.OpenAIBridgeGlue.val_intCast_of_nonneg
#print axioms MassGap.OpenAIBridgeGlue.finEquiv_eq_natCast
#print axioms MassGap.OpenAIBridgeGlue.val_finEquiv
#print axioms MassGap.OpenAIBridgeGlue.windowLocal_of_timeWindowLocal
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_sumIns
#print axioms MassGap.OpenAIBridgeGlue.smearIns_eq_sumIns
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_smearIns
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_mono
#print axioms MassGap.OpenAIBridgeGlue.pull_shift_iter_apply
#print axioms MassGap.OpenAIBridgeGlue.siteEquiv_join_shift
#print axioms MassGap.OpenAIBridgeGlue.readAt_slabOf_shift
#print axioms MassGap.OpenAIBridgeGlue.reflSite_reflSite
#print axioms MassGap.OpenAIBridgeGlue.reflConfT_reflConfT
#print axioms MassGap.OpenAIBridgeGlue.smearIns_reflect
#print axioms MassGap.OpenAIBridgeGlue.smearIns_reflect'
#print axioms MassGap.OpenAIBridgeGlue.reflConfT_transport
#print axioms MassGap.OpenAIBridgeGlue.siteEquiv_join_refl
#print axioms MassGap.OpenAIBridgeGlue.reflConf_window
#print axioms MassGap.OpenAIBridgeGlue.reflectionClosed_of_reflConfT
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_reflConfT
#print axioms MassGap.OpenAIBridgeGlue.conn_toSide
#print axioms MassGap.OpenAIBridgeGlue.continuous_toSide
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_toSide
#print axioms MassGap.OpenAIBridgeGlue.toSide_transport
#print axioms MassGap.OpenAIBridgeGlue.toSide_reflect
#print axioms MassGap.OpenAIBridgeGlue.smear_conn_cubic
#print axioms MassGap.OpenAIBridgeGlue.slab_split
#print axioms MassGap.OpenAIBridgeGlue.gap_ge
#print axioms MassGap.OpenAIBridgeGlue.cubicForm_of_inputs
#print axioms MassGap.OpenAIBridgeGlue.time_bound_of_test
#print axioms MassGap.OpenAIBridgeGlue.stencil_radius
#print axioms MassGap.OpenAIBridgeGlue.placement_exists
#print axioms MassGap.OpenAIBridgeGlue.uniformDecayFrom_of_seed
#print axioms MassGap.OpenAIBridgeGlue.reflMoment_nonneg
#print axioms MassGap.OpenAIBridgeGlue.reImF_apply
#print axioms MassGap.OpenAIBridgeGlue.reImG_apply
#print axioms MassGap.OpenAIBridgeGlue.part_facts
#print axioms MassGap.OpenAIBridgeGlue.slabOf_part_facts
#print axioms MassGap.OpenAIBridgeGlue.moments_nonneg
#print axioms MassGap.OpenAIBridgeGlue.tendsto_order_of_converges
#print axioms MassGap.OpenAIBridgeGlue.uniformDecayFrom_of_seed'
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_comp
#print axioms MassGap.OpenAIBridgeGlue.timeWindowLocal_reflConfT'
#print axioms MassGap.OpenAIBridgeGlue.siteEquiv_join_shift'
#print axioms MassGap.OpenAIBridgeGlue.readAt_slabOf_shift'
#print axioms MassGap.OpenAIBridgeGlue.reflO_slabOf_partF
#print axioms MassGap.OpenAIBridgeGlue.reflO_slabOf_partG
#print axioms MassGap.OpenAIBridgeGlue.pairMom_toSide
#print axioms MassGap.OpenAIBridgeGlue.momF_theta
#print axioms MassGap.OpenAIBridgeGlue.momG_theta
#print axioms MassGap.OpenAIBridgeGlue.uniformDecayFrom_of_seed''
