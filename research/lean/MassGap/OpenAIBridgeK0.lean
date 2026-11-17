import Mathlib
import MassGap.OpenAIBridgeGlue

/-!
# MassGap.OpenAIBridgeK0 — the reflected-moment input (K₀) from a bound on their finite moments

The input `hK₀` of `OpenAIBridgeGlue.uniformDecayFrom_of_seed''` bounds five real readings
`pairMom` of their smeared insertions against the reflected ones by `K₀ ‖t‖₁²`. This module reduces
it to one bound on their own lattice moments `WilsonFamily.finiteMoment` at reflected separated
configurations, `ReflectedMomentBound`; the placements keep those configurations apart
(`placement_clear`).

## 1. Reflection through a shift (L2)

* `reflSite_add_single`, `reflConfT_shift_iter` — the reflection about `c` after `s` shifts along
  the reflected axis is the reflection about `c + s`;
* `transport_shift_iter`, `reflConfT_transport_shift` — `s` shifts before the transport move the
  plane of their time reflection from `c` to `c + s`.

## 2. The real readings are below one complex moment (L1)

* `cMom` — the complex smeared moment whose real parts the readings are;
* `pairMom_re_add`, `pairMom_re_add'` — `Re·Re − Im·Im` of a product is its real part;
* `split_F`, `split_FR`, `split_G`, `split_GR`, `le_re_of_pairs` — under the nonnegativity of
  the companion reading (`moments_nonneg`), every reading is at most the real part of `cMom`.

## 3. The complex moment is a sum of their finite moments (L3)

* `pairSum`, `integral_pairSum` — the product of two smeared sums integrates to the double sum of
  `finiteMoment` of the appended token lists at the appended configurations;
* `conj_smearIns_refl`, `conj_smearIns_theta_refl` — the conjugated insertions at a reflected
  configuration, by `TokenReflection`;
* `cMom_A_first`, `cMom_B_first` — the two complex moments of the placement as `finiteMoment`
  sums: `w ++ Θ ∘ w` at `(x, refl_{c+s} x')`, and `Θ ∘ w ++ w` at
  `(refl_c x, refl_{c+s} (refl_c x'))`, weighted by `t (x) · conj t (x')`.

## 4. The lattice sum of a test (L4)

* `coordPts`, `latCoord`, `latCoord_bound`, `latCoord_int`, `tsum_lattice_eq`;
* `riemann_le_two` — eventually in the spacing, `mesh^{4n} Σ_x ‖t(place x)‖ ≤ 2 ‖t‖₁`, from
  Mathlib's `tendsto_tsum_div_pow_atTop_integral`.

## 5. The capstones

* `SlicesApart`, `ReflectedMomentBound` — two tuples apart in time, and the named input;
* `val_eq_of_eq_cast`, `reflSite_three`, `slicesApart_of_reads`, `placement_clear` — every valid
  placement keeps the supported configurations and their reflected copies `δ/4` apart;
* `norm_mesh_double_sum_le`, `re_cMom_A_first_le`, `re_cMom_B_first_le`, `le_four_mul_sq`;
* `hK0_of_reflectedMomentBound` — the input `hK₀` with `K₀ = 4 max(M₁, M₂)`, from the bounds `M₁`,
  `M₂` of the two groups;
* `uniformDecayFrom_of_seed'''` — the floored (U) with these inputs in place of `hK₀`.
-/

namespace MassGap.OpenAIBridgeK0

open MeasureTheory Real Filter
open MassGap.OpenAILink MassGap.OpenAIBridgeCompose MassGap.RectWilson MassGap.RectWilsonG
open MassGap.OpenAIBridgeGlue

/-! ## 1. Reflection through a shift -/

section Lattice

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- **A shifted reflected site**: `reflSite c τ z + s τ̂ = reflSite (c + s) τ z`.

DERIVED: no numeral appears in the statement. -/
theorem reflSite_add_single (c s : ZMod L.val) (τ : OpenAIConfig.Axis) (z : OpenAIConfig.Site L) :
    reflSite c τ z + Pi.single τ s = reflSite (c + s) τ z := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [reflSite, Pi.add_apply, Function.update_self, Pi.single_eq_same]
    ring
  · simp only [reflSite, Pi.add_apply, Function.update_of_ne h, Pi.single_eq_of_ne h, add_zero]

/-- **L2: the reflection after `s` shifts along its axis** is the reflection about `c + s`.

DERIVED: no numeral appears in the statement. -/
theorem reflConfT_shift_iter [NeZero (L : ℕ)] (c : ZMod L.val) (τ : OpenAIConfig.Axis) (s : ℕ)
    (V : OpenAIConfig.Configuration g L) :
    reflConfT c τ ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[s] V)
      = reflConfT (c + (s : ZMod L.val)) τ V := by
  funext e
  obtain ⟨z, a⟩ := e
  by_cases h : a = τ
  · have e1 : reflConfT c τ ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[s] V) (z, a)
        = ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[s] V (reflSite (c - 1) τ z, τ))⁻¹ :=
      if_pos h
    have e2 : reflConfT (c + (s : ZMod L.val)) τ V (z, a)
        = (V (reflSite (c + (s : ZMod L.val) - 1) τ z, τ))⁻¹ := if_pos h
    rw [e1, e2, pull_shift_iter_apply, reflSite_add_single, sub_add_eq_add_sub]
  · have e1 : reflConfT c τ ((pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[s] V) (z, a)
        = (pull L (MassGap.ShiftInvG.shiftLinkPerm τ))^[s] V (reflSite c τ z, a) := if_neg h
    have e2 : reflConfT (c + (s : ZMod L.val)) τ V (z, a)
        = V (reflSite (c + (s : ZMod L.val)) τ z, a) := if_neg h
    rw [e1, e2, pull_shift_iter_apply, reflSite_add_single]

/-- **`q` shifts before the transport** are `q` more steps of the transport.

DERIVED: `0` is the transfer direction. -/
theorem transport_shift_iter [NeZero (L : ℕ)] (k q : ℕ) (V : OpenAIConfig.Configuration g L) :
    transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[q] V)
      = transport g L (k + q) V := by
  induction q generalizing V with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

/-- **The reflection of their time axis after `s` shifts in the transfer frame** is the reflection
about `c + s`: `reflConfT_transport`, `reflConfT_shift_iter`, `reflConfT_transport`.

DERIVED: `0` is the transfer direction; `3` their time axis. -/
theorem reflConfT_transport_shift [NeZero (L : ℕ)] (k s : ℕ) (c : ZMod L.val)
    (V : OpenAIConfig.Configuration g L) :
    reflConfT c 3 (transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[s] V))
      = reflConfT (c + (s : ZMod L.val)) 3 (transport g L k V) := by
  rw [reflConfT_transport g L k c, reflConfT_shift_iter g L,
    reflConfT_transport g L k (c + (s : ZMod L.val)), add_right_comm]

end Lattice

/-! ## 2. The real readings are below one complex moment -/

section Readings

variable {g : OpenAIConfig.GaugeGroup}

/-- **The complex smeared moment** of two observables on their side: the expectation under their law
of `A` read through the transport after `q₁` shifts along `0` times `B` after `q₂` shifts. The
readings `pairMom` are real parts of its integrand.

DERIVED: `0` is the transfer direction. -/
noncomputable def cMom (L : ℕ+) (β : ℝ) (μ : Measure g.image)
    (A B : OpenAIConfig.Configuration g L → ℂ) (k q₁ q₂ : ℕ) : ℂ :=
  ∫ V, A (transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))
    * B (transport g L k ((pull L (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))
    ∂(OpenAIConfig.wilsonLaw g L β μ)

/-- **`Re·Re + Im·(−Im)` is the real part of the complex moment.**

DERIVED: `0` is the transfer direction. -/
theorem pairMom_re_add (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) :
    pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y Complex.re Complex.re k q₁ q₂
      + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y Complex.im
          (fun z => -z.im) k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  have hf : Continuous fun V => X (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V)) :=
    hX.comp ((continuous_transport g _ k).comp ((continuous_pull g _ _).iterate q₁))
  have hg : Continuous fun V => Y (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V)) :=
    hY.comp ((continuous_transport g _ k).comp ((continuous_pull g _ _).iterate q₂))
  haveI := C.probability
  haveI := C.invariantHaar
  haveI := isProbabilityMeasure_wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar
  have h1 : Integrable (fun V => (X (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))).re
        * (Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))).re)
      (lawAt C N p) :=
    OpenAIBridgeLimits.integrable_of_continuous
      ((Complex.continuous_re.comp hf).mul (Complex.continuous_re.comp hg))
  have h2 : Integrable (fun V => (X (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))).im
        * -(Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))).im)
      (lawAt C N p) :=
    OpenAIBridgeLimits.integrable_of_continuous
      ((Complex.continuous_im.comp hf).mul (Complex.continuous_im.comp hg).neg)
  have hI : Integrable (fun V => X (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))
        * Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V)))
      (lawAt C N p) :=
    integrable_of_continuous C N p (hf.mul hg)
  calc pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y Complex.re Complex.re k q₁ q₂
        + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y Complex.im
          (fun z => -z.im) k q₁ q₂
      = ∫ V, ((X (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))).re
          * (Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))).re
          + (X (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))).im
          * -(Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))).im)
          ∂(lawAt C N p) := (integral_add h1 h2).symm
    _ = ∫ V, (X (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))
          * Y (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₂] V))).re
          ∂(lawAt C N p) :=
        integral_congr_ae (Filter.Eventually.of_forall fun V => by
          simp only [Complex.mul_re]
          ring)
    _ = _ := integral_re hI

/-- `(−Im)·Im` and `Im·(−Im)` give the same reading.

DERIVED: no numeral appears in the statement. -/
theorem pairMom_negIm_swap (L : ℕ+) (β : ℝ) (μ : Measure g.image)
    (X Y : OpenAIConfig.Configuration g L → ℂ) (k q₁ q₂ : ℕ) :
    pairMom L β μ X Y (fun z => -z.im) Complex.im k q₁ q₂
      = pairMom L β μ X Y Complex.im (fun z => -z.im) k q₁ q₂ := by
  unfold pairMom
  congr 1
  funext V
  dsimp only
  ring

/-- **`Re·Re + (−Im)·Im` is the real part of the complex moment**, by `pairMom_negIm_swap`.

DERIVED: no numeral appears in the statement. -/
theorem pairMom_re_add' (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) :
    pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y Complex.re Complex.re k q₁ q₂
      + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (fun z => -z.im)
          Complex.im k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  rw [pairMom_negIm_swap]
  exact pairMom_re_add C N p hX hY k q₁ q₂

/-- **Every reading is at most the real part of the complex moment** when every reading of the
family is nonnegative and each pairs with a companion to that real part.

DERIVED: `4` is the number of pairs. -/
theorem le_re_of_pairs (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (κ₁ κ₂ : Fin 4 → ℂ → ℝ) (k q₁ q₂ : ℕ)
    (hn : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (κ₁ j) (κ₂ j)
      k q₁ q₂)
    (hs : ∀ j, ∃ j', pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (κ₁ j) (κ₂ j)
        k q₁ q₂ + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (κ₁ j') (κ₂ j')
        k q₁ q₂ = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re)
    (j : Fin 4) :
    pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (κ₁ j) (κ₂ j) k q₁ q₂
      ≤ (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  obtain ⟨j', h⟩ := hs j
  linarith [hn j']

/-- The pairs `(partF, partFR)`: `(Re, Re)`, `(Im, −Im)`, `(Re, Re)`, `(Im, −Im)`.

DERIVED: `4` is the number of pairs. -/
theorem split_F (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) (j : Fin 4) :
    ∃ j' : Fin 4, pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (partF j)
        (partFR j) k q₁ q₂ + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y
        (partF j') (partFR j') k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  have h := pairMom_re_add C N p hX hY k q₁ q₂
  fin_cases j
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩

/-- The pairs `(partFR, partF)`: `(Re, Re)`, `(−Im, Im)`, `(Re, Re)`, `(−Im, Im)`.

DERIVED: `4` is the number of pairs. -/
theorem split_FR (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) (j : Fin 4) :
    ∃ j' : Fin 4, pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (partFR j)
        (partF j) k q₁ q₂ + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y
        (partFR j') (partF j') k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  have h := pairMom_re_add' C N p hX hY k q₁ q₂
  fin_cases j
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩

/-- The pairs `(partG, partGR)`: `(Re, Re)`, `(Im, −Im)`, `(Im, −Im)`, `(Re, Re)`.

DERIVED: `4` is the number of pairs. -/
theorem split_G (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) (j : Fin 4) :
    ∃ j' : Fin 4, pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (partG j)
        (partGR j) k q₁ q₂ + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y
        (partG j') (partGR j') k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  have h := pairMom_re_add C N p hX hY k q₁ q₂
  fin_cases j
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨1, h⟩

/-- The pairs `(partGR, partG)`: `(Re, Re)`, `(−Im, Im)`, `(−Im, Im)`, `(Re, Re)`.

DERIVED: `4` is the number of pairs. -/
theorem split_GR (C : WilsonFamily g) (N p : ℕ)
    {X Y : OpenAIConfig.Configuration g (C.period p * C.denominator N) → ℂ}
    (hX : Continuous X) (hY : Continuous Y) (k q₁ q₂ : ℕ) (j : Fin 4) :
    ∃ j' : Fin 4, pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y (partGR j)
        (partG j) k q₁ q₂ + pairMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y
        (partGR j') (partG j') k q₁ q₂
      = (cMom (C.period p * C.denominator N) (C.beta N p) C.haar X Y k q₁ q₂).re := by
  have h := pairMom_re_add' C N p hX hY k q₁ q₂
  fin_cases j
  · exact ⟨1, h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨0, by rw [add_comm]; exact h⟩
  · exact ⟨1, h⟩

end Readings

/-! ## 3. The complex moment is a sum of their finite moments -/

section Moments

variable {g : OpenAIConfig.GaugeGroup}

/-- Their placed configuration of a tuple of lattice sites, `x ↦ (place x₁, …, place xₙ)`.

DERIVED: `2` is the `L²` exponent. -/
noncomputable abbrev ptsOf (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) : Points n :=
  WithLp.toLp 2 fun i => C.place N p (x i)

/-- **The product of two smeared sums** at one configuration: weights `a`, `b`, sites `y x`,
`y' x'`, tokens `u`, `u'`.

DERIVED: `4` is the spacetime dimension. -/
noncomputable def pairSum (C : WilsonFamily g) (N p : ℕ) {n : ℕ} (u u' : Fin n → C.Token)
    (a b : (Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) → ℂ)
    (y y' : (Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) →
      Fin n → OpenAIConfig.Site (C.period p * C.denominator N))
    (W : OpenAIConfig.Configuration g (C.period p * C.denominator N)) : ℂ :=
  ((C.mesh N : ℂ) ^ (4 * n) * ∑ x, a x * ∏ i, C.insertion N p (u i) (y x i) W)
    * ((C.mesh N : ℂ) ^ (4 * n) * ∑ x', b x' * ∏ i, C.insertion N p (u' i) (y' x' i) W)

/-- **The product of two smeared sums integrates to their finite moments** of the appended token
lists at the appended configurations: `Fin.prod_univ_add`, linearity, `finiteMoment`.

DERIVED: `4` is the spacetime dimension. -/
theorem integral_pairSum (C : WilsonFamily g) (N p : ℕ)
    (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ} (u u' : Fin n → C.Token)
    (a b : (Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) → ℂ)
    (y y' : (Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) →
      Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) :
    ∫ W, pairSum C N p u u' a b y y' W ∂(lawAt C N p)
      = (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) *
        ∑ x, ∑ x', a x * b x' * C.finiteMoment N p (Fin.append u u') (Fin.append (y x) (y' x')) := by
  have hP : ∀ x x', Continuous fun W =>
      ∏ i, C.insertion N p (Fin.append u u' i) (Fin.append (y x) (y' x') i) W :=
    fun x x' => continuous_finsetProd _ fun i _ => hc _ _
  have hI : ∀ x x', Integrable (fun W => a x * b x' *
      ∏ i, C.insertion N p (Fin.append u u' i) (Fin.append (y x) (y' x') i) W) (lawAt C N p) :=
    fun x x' => integrable_of_continuous C N p (continuous_const.mul (hP x x'))
  have hpt : ∀ W, pairSum C N p u u' a b y y' W
      = (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) * ∑ x, ∑ x', a x * b x' *
        ∏ i, C.insertion N p (Fin.append u u' i) (Fin.append (y x) (y' x') i) W := by
    intro W
    unfold pairSum
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring
  calc ∫ W, pairSum C N p u u' a b y y' W ∂(lawAt C N p)
      = ∫ W, (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) * ∑ x, ∑ x', a x * b x' *
          ∏ i, C.insertion N p (Fin.append u u' i) (Fin.append (y x) (y' x') i) W
          ∂(lawAt C N p) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) * ∑ x, ∫ W, ∑ x', a x * b x' *
          ∏ i, C.insertion N p (Fin.append u u' i) (Fin.append (y x) (y' x') i) W
          ∂(lawAt C N p) := by
        rw [integral_const_mul, integral_finsetSum Finset.univ fun x _ =>
          integrable_finsetSum Finset.univ fun x' _ => hI x x']
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [integral_finsetSum Finset.univ fun x' _ => hI x x']
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [integral_const_mul]
        rfl

/-- **The conjugated smeared insertion at a reflected configuration**: under `TokenReflection`,
`conj F_t(reflConfT c 3 W) = mesh^{4n} Σ_x conj t(x) Π_i insertion (Θ wᵢ) (reflSite c 3 xᵢ) W`.

DERIVED: `4` is the spacetime dimension; `3` their time axis. -/
theorem conj_smearIns_refl {C : WilsonFamily g} {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n) (c : ZMod (C.period p * C.denominator N : ℕ+).val)
    (W : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    (starRingEnd ℂ) (smearIns C N p w t (reflConfT c 3 W))
      = (C.mesh N : ℂ) ^ (4 * n) * ∑ x, (starRingEnd ℂ) (t (ptsOf C N p x))
        * ∏ i, C.insertion N p (Θ (w i)) (reflSite c 3 (x i)) W := by
  unfold smearIns
  rw [map_mul, map_sum, map_pow, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := hΘ N p (w i) (x i) c (reflConfT c 3 W)
  rw [reflConfT_reflConfT] at h
  exact h.symm

/-- **The conjugated reflected insertion at a second reflection**: under `TokenReflection` and a
`ReflectedTest` at `c`, reindexing the sites by `reflTuple c`,
`conj G(reflConfT c' 3 W) = mesh^{4n} Σ_x t(x) Π_i insertion wᵢ (reflSite c' 3 (reflSite c 3 xᵢ)) W`.

DERIVED: `4` is the spacetime dimension; `3` their time axis. -/
theorem conj_smearIns_theta_refl {C : WilsonFamily g} {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) (N p : ℕ) {n : ℕ} (w : Fin n → C.Token)
    (t tθ : WilsonFamily.SeparatedTest n) (c c' : ZMod (C.period p * C.denominator N : ℕ+).val)
    (htθ : ReflectedTest C N p c t tθ)
    (W : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    (starRingEnd ℂ) (smearIns C N p (fun j => Θ (w j)) tθ (reflConfT c' 3 W))
      = (C.mesh N : ℂ) ^ (4 * n) * ∑ x', t (ptsOf C N p x')
        * ∏ i, C.insertion N p (w i) (reflSite c' 3 (reflSite c 3 (x' i))) W := by
  unfold smearIns
  rw [map_mul, map_sum, map_pow, Complex.conj_ofReal]
  congr 1
  refine (Equiv.sum_comp (reflTuple c) _).symm.trans (Finset.sum_congr rfl fun x' _ => ?_)
  show (starRingEnd ℂ) (tθ (WithLp.toLp 2 fun i => C.place N p (reflSite c 3 (x' i)))
      * ∏ i, C.insertion N p (Θ (w i)) (reflSite c 3 (x' i)) (reflConfT c' 3 W)) = _
  rw [htθ x', map_mul, map_prod, Complex.conj_conj]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := hΘ N p (w i) (reflSite c' 3 (reflSite c 3 (x' i))) c' W
  rw [reflSite_reflSite] at h
  rw [h, Complex.conj_conj]

/-- **The integrand of the first complex moment** at a configuration, as a `pairSum` at the
transported configuration: `smearIns_reflect'`, `reflConfT_transport_shift`, `transport_shift_iter`,
`conj_smearIns_refl`.

DERIVED: `0` is the transfer direction; `3` their time axis. -/
theorem integrand_A {C : WilsonFamily g} {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ)
    (N p : ℕ) {n : ℕ} (w : Fin n → C.Token) (t tθ : WilsonFamily.SeparatedTest n)
    (c : ZMod (C.period p * C.denominator N : ℕ+).val) (htθ : ReflectedTest C N p c t tθ)
    (k q₁ s : ℕ) (V : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    smearIns C N p w t (transport g _ k ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))
      * smearIns C N p (fun j => Θ (w j)) tθ (transport g _ k
        ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁ + s] V))
      = pairSum C N p w (fun j => Θ (w j)) (fun x => t (ptsOf C N p x))
          (fun x' => (starRingEnd ℂ) (t (ptsOf C N p x'))) (fun x => x)
          (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3 (x' i))
          (transport g _ (k + q₁) V) := by
  rw [smearIns_reflect' hΘ N p w t tθ c htθ, add_comm q₁ s, Function.iterate_add_apply,
    reflConfT_transport_shift g _ k s c, transport_shift_iter g _ k q₁ V,
    conj_smearIns_refl hΘ N p w t]
  unfold pairSum smearIns
  rfl

/-- **The integrand of the second complex moment** at a configuration, as a `pairSum` at the
transported configuration.

DERIVED: `0` is the transfer direction; `3` their time axis. -/
theorem integrand_B {C : WilsonFamily g} {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ)
    (N p : ℕ) {n : ℕ} (w : Fin n → C.Token) (t tθ : WilsonFamily.SeparatedTest n)
    (c : ZMod (C.period p * C.denominator N : ℕ+).val) (htθ : ReflectedTest C N p c t tθ)
    (k q₁ s : ℕ) (V : OpenAIConfig.Configuration g (C.period p * C.denominator N)) :
    smearIns C N p (fun j => Θ (w j)) tθ (transport g _ k
        ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V))
      * smearIns C N p w t (transport g _ k
        ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁ + s] V))
      = pairSum C N p (fun j => Θ (w j)) w (fun x => (starRingEnd ℂ) (t (ptsOf C N p x)))
          (fun x' => t (ptsOf C N p x')) (fun x i => reflSite c 3 (x i))
          (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3
            (reflSite c 3 (x' i)))
          (transport g _ (k + q₁) V) := by
  have hAB : smearIns C N p w t (transport g _ k
        ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁ + s] V))
      = (starRingEnd ℂ) (smearIns C N p (fun j => Θ (w j)) tθ (reflConfT c 3 (transport g _ k
        ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁ + s] V)))) := by
    rw [smearIns_reflect hΘ N p w t tθ c htθ, Complex.conj_conj]
  rw [hAB, smearIns_reflect' hΘ N p w t tθ c htθ (transport g _ k
      ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V)),
    add_comm q₁ s, Function.iterate_add_apply,
    reflConfT_transport_shift g _ k s c ((pull _ (MassGap.ShiftInvG.shiftLinkPerm 0))^[q₁] V),
    transport_shift_iter g _ k q₁ V, conj_smearIns_refl hΘ N p w t c,
    conj_smearIns_theta_refl hΘ N p w t tθ c _ htθ]
  unfold pairSum
  rfl

/-- **L3, the reading with the insertion first**: under `TokenReflection` and a `ReflectedTest`
at `c`, with `q₂ = q₁ + s`, the complex moment of `(F_t, G_{tθ})` is
`mesh^{8n} Σ_{x,x'} t(x) conj t(x') finiteMoment (w ++ Θ ∘ w) (x ++ reflSite (c + s) 3 x')`:
the shift is absorbed into the plane (`reflConfT_transport_shift`) and the transport into their law
(`measurePreserving_transport`).

DERIVED: `4` is the spacetime dimension; `3` their time axis. -/
theorem cMom_A_first {C : WilsonFamily g} {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ)
    (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ} (w : Fin n → C.Token)
    (t tθ : WilsonFamily.SeparatedTest n) (c : ZMod (C.period p * C.denominator N : ℕ+).val)
    (htθ : ReflectedTest C N p c t tθ) (k q₁ q₂ s : ℕ) (hq : q₂ = q₁ + s) :
    cMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w t)
        (smearIns C N p (fun j => Θ (w j)) tθ) k q₁ q₂
      = (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) * ∑ x, ∑ x',
        t (ptsOf C N p x) * (starRingEnd ℂ) (t (ptsOf C N p x'))
        * C.finiteMoment N p (Fin.append w (fun j => Θ (w j)))
          (Fin.append x (fun i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val))
            3 (x' i))) := by
  haveI := C.probability
  haveI := C.invariantHaar
  subst hq
  have h1 : cMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w t)
        (smearIns C N p (fun j => Θ (w j)) tθ) k q₁ (q₁ + s)
      = ∫ V, pairSum C N p w (fun j => Θ (w j)) (fun x => t (ptsOf C N p x))
          (fun x' => (starRingEnd ℂ) (t (ptsOf C N p x'))) (fun x => x)
          (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3 (x' i))
          (transport g _ (k + q₁) V) ∂(lawAt C N p) :=
    integral_congr_ae (Filter.Eventually.of_forall (integrand_A hΘ N p w t tθ c htθ k q₁ s))
  have h2 := (measurePreserving_transport g (C.period p * C.denominator N) C.haar (C.beta N p)
    (k + q₁)).integral_comp' (pairSum C N p w (fun j => Θ (w j)) (fun x => t (ptsOf C N p x))
      (fun x' => (starRingEnd ℂ) (t (ptsOf C N p x'))) (fun x => x)
      (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3 (x' i)))
  rw [h1, h2]
  exact integral_pairSum C N p hc w (fun j => Θ (w j)) (fun x => t (ptsOf C N p x))
    (fun x' => (starRingEnd ℂ) (t (ptsOf C N p x'))) (fun x => x)
    (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3 (x' i))

/-- **L3, the reading with the reflected insertion first**: under `TokenReflection` and a
`ReflectedTest` at `c`, with `q₂ = q₁ + s`, the complex moment of `(G_{tθ}, F_t)` is
`mesh^{8n} Σ_{x,x'} conj t(x) t(x') finiteMoment (Θ ∘ w ++ w)
(reflSite c 3 x ++ reflSite (c + s) 3 (reflSite c 3 x'))`.

DERIVED: `4` is the spacetime dimension; `3` their time axis. -/
theorem cMom_B_first {C : WilsonFamily g} {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ)
    (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ} (w : Fin n → C.Token)
    (t tθ : WilsonFamily.SeparatedTest n) (c : ZMod (C.period p * C.denominator N : ℕ+).val)
    (htθ : ReflectedTest C N p c t tθ) (k q₁ q₂ s : ℕ) (hq : q₂ = q₁ + s) :
    cMom (C.period p * C.denominator N) (C.beta N p) C.haar
        (smearIns C N p (fun j => Θ (w j)) tθ) (smearIns C N p w t) k q₁ q₂
      = (C.mesh N : ℂ) ^ (4 * n) * (C.mesh N : ℂ) ^ (4 * n) * ∑ x, ∑ x',
        (starRingEnd ℂ) (t (ptsOf C N p x)) * t (ptsOf C N p x')
        * C.finiteMoment N p (Fin.append (fun j => Θ (w j)) w)
          (Fin.append (fun i => reflSite c 3 (x i))
            (fun i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3
              (reflSite c 3 (x' i)))) := by
  haveI := C.probability
  haveI := C.invariantHaar
  subst hq
  have h1 : cMom (C.period p * C.denominator N) (C.beta N p) C.haar
        (smearIns C N p (fun j => Θ (w j)) tθ) (smearIns C N p w t) k q₁ (q₁ + s)
      = ∫ V, pairSum C N p (fun j => Θ (w j)) w (fun x => (starRingEnd ℂ) (t (ptsOf C N p x)))
          (fun x' => t (ptsOf C N p x')) (fun x i => reflSite c 3 (x i))
          (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3
            (reflSite c 3 (x' i)))
          (transport g _ (k + q₁) V) ∂(lawAt C N p) :=
    integral_congr_ae (Filter.Eventually.of_forall (integrand_B hΘ N p w t tθ c htθ k q₁ s))
  have h2 := (measurePreserving_transport g (C.period p * C.denominator N) C.haar (C.beta N p)
    (k + q₁)).integral_comp' (pairSum C N p (fun j => Θ (w j)) w
      (fun x => (starRingEnd ℂ) (t (ptsOf C N p x))) (fun x' => t (ptsOf C N p x'))
      (fun x i => reflSite c 3 (x i))
      (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3
        (reflSite c 3 (x' i))))
  rw [h1, h2]
  exact integral_pairSum C N p hc (fun j => Θ (w j)) w
    (fun x => (starRingEnd ℂ) (t (ptsOf C N p x))) (fun x' => t (ptsOf C N p x'))
    (fun x i => reflSite c 3 (x i))
    (fun x' i => reflSite (c + (s : ZMod (C.period p * C.denominator N : ℕ+).val)) 3
      (reflSite c 3 (x' i)))

end Moments

/-! ## 4. The lattice sum of a test -/

section Riemann

variable {g : OpenAIConfig.GaugeGroup}

/-- **Coordinates of a configuration of `n` points**: the flat vector indexed by `(point, axis)`,
read as `n` points through `LinearIsometryEquiv.piLpCurry`.

DERIVED: `4` is the spacetime dimension; `2` the `L²` exponent. -/
noncomputable def coordPts (n : ℕ) (z : (Σ _ : Fin n, Fin 4) → ℝ) : Points n :=
  LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin n) (_ : Fin 4) => ℝ) (WithLp.toLp 2 z)

/-- **The flat coordinates of a tuple of their sites**: `mesh · valMinAbs (xᵢ a)`.

DERIVED: `4` is the spacetime dimension. -/
noncomputable def latCoord (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) :
    (Σ _ : Fin n, Fin 4) → ℝ :=
  fun ia => C.mesh N * ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ)

/-- The spacing is nonnegative.

DERIVED: no numeral appears in the statement. -/
theorem mesh_nonneg (C : WilsonFamily g) (N : ℕ) : 0 ≤ C.mesh N := by
  unfold WilsonFamily.mesh
  positivity

/-- **The coordinates of a site lie in the box of side twice their period.**

DERIVED: `4` is the spacetime dimension. -/
theorem latCoord_bound (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) (ia : Σ _ : Fin n, Fin 4) :
    -((C.period p).val : ℝ) ≤ latCoord C N p x ia ∧ latCoord C N p x ia ≤ ((C.period p).val : ℝ) := by
  obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc (x ia.1 ia.2)
  have hL : (((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ)
      = ((C.period p).val : ℝ) * ((C.denominator N).val : ℝ) := by
    rw [PNat.mul_coe, Nat.cast_mul]
  have hD : (0 : ℝ) < ((C.denominator N).val : ℝ) := by exact_mod_cast (C.denominator N).pos
  have hP : (0 : ℝ) ≤ ((C.period p).val : ℝ) := Nat.cast_nonneg _
  have r1 : ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ) * 2
      ≤ (((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ) := by exact_mod_cast h2
  have r2 : -((((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ))
      < ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ) * 2 := by exact_mod_cast h1
  rw [hL] at r1 r2
  have hPD : 0 ≤ ((C.period p).val : ℝ) * ((C.denominator N).val : ℝ) := mul_nonneg hP hD.le
  have hv1 : ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ)
      ≤ ((C.period p).val : ℝ) * ((C.denominator N).val : ℝ) := by linarith
  have hv2 : -(((C.period p).val : ℝ) * ((C.denominator N).val : ℝ))
      ≤ ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ) := by linarith
  have e : ((C.denominator N).val : ℝ)⁻¹ * (((C.period p).val : ℝ) * ((C.denominator N).val : ℝ))
      = ((C.period p).val : ℝ) := by
    rw [mul_comm, mul_assoc, mul_inv_cancel₀ hD.ne', mul_one]
  have hi : 0 ≤ ((C.denominator N).val : ℝ)⁻¹ := inv_nonneg.mpr hD.le
  unfold latCoord WilsonFamily.mesh
  constructor
  · have := mul_le_mul_of_nonneg_left hv2 hi
    rwa [mul_neg, e] at this
  · have := mul_le_mul_of_nonneg_left hv1 hi
    rwa [e] at this

/-- **The coordinates of a site are integers over the spacing.**

DERIVED: `4` is the spacetime dimension. -/
theorem latCoord_int (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) (ia : Σ _ : Fin n, Fin 4) :
    ((ZMod.valMinAbs (x ia.1 ia.2) : ℤ) : ℝ)
      = ((C.denominator N : ℕ) : ℝ) * latCoord C N p x ia := by
  have hD : ((C.denominator N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (C.denominator N).ne_zero
  unfold latCoord WilsonFamily.mesh
  rw [← mul_assoc, mul_inv_cancel₀ hD, one_mul]

/-- **The lattice sum of a suitable test is a sum over the lattice points of a box**: for a set `S`
of flat vectors in the box of side twice their period with integer coordinates over the spacing,
the sum of `‖t‖` over `S` is the sum over their sites, when the test is suitable at `p`.

DERIVED: `4` is the spacetime dimension. -/
theorem tsum_lattice_eq (C : WilsonFamily g) (N p : ℕ) {n : ℕ} (t : WilsonFamily.SeparatedTest n)
    (hp : C.suitable p t) (S : Set ((Σ _ : Fin n, Fin 4) → ℝ))
    (hS : ∀ z, z ∈ S ↔ (∀ ia, -((C.period p).val : ℝ) ≤ z ia ∧ z ia ≤ ((C.period p).val : ℝ)) ∧
      ∀ ia, ∃ q : ℤ, (q : ℝ) = ((C.denominator N : ℕ) : ℝ) * z ia) :
    ∑' z : S, ‖t (coordPts n z)‖
      = ∑ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N), ‖t (ptsOf C N p x)‖ := by
  classical
  have hD : (0 : ℝ) < ((C.denominator N : ℕ) : ℝ) := by exact_mod_cast (C.denominator N).pos
  have hL : (((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ)
      = ((C.period p).val : ℝ) * ((C.denominator N : ℕ) : ℝ) := by
    rw [PNat.mul_coe, Nat.cast_mul]
  have hz : ∀ z ∉ Finset.univ.image (latCoord C N p),
      S.indicator (fun z => ‖t (coordPts n z)‖) z = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hzS : z ∈ S := Set.mem_of_indicator_ne_zero hne
    have hFz : t (coordPts n z) ≠ 0 := by
      rw [Set.indicator_of_mem hzS] at hne
      exact norm_ne_zero_iff.mp hne
    obtain ⟨-, hq⟩ := (hS z).mp hzS
    choose q hq using hq
    have hm : coordPts n z ∈ tsupport t := subset_tsupport _ hFz
    have hb : ∀ ia : (Σ _ : Fin n, Fin 4), |z ia| < ((C.period p).val : ℝ) / 2 := by
      rintro ⟨i, a⟩
      exact abs_lt.mpr (hp hm i a)
    have hval : ∀ ia, ZMod.valMinAbs ((q ia : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
        = q ia := by
      intro ia
      have hzb := abs_lt.mp (hb ia)
      have r1 : -((((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ)) < (q ia : ℝ) * 2 := by
        rw [hL, hq ia]
        nlinarith [mul_lt_mul_of_pos_left hzb.1 hD]
      have r2 : (q ia : ℝ) * 2 ≤ (((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ) := by
        rw [hL, hq ia]
        nlinarith [mul_lt_mul_of_pos_left hzb.2 hD]
      rw [ZMod.valMinAbs_spec]
      exact ⟨rfl, by exact_mod_cast r1, by exact_mod_cast r2⟩
    refine Finset.mem_image.mpr ⟨fun i a => ((q ⟨i, a⟩ : ℤ) : ZMod _), Finset.mem_univ _, ?_⟩
    funext ia
    obtain ⟨i, a⟩ := ia
    show C.mesh N * ((ZMod.valMinAbs ((q ⟨i, a⟩ : ℤ) :
      ZMod (C.period p * C.denominator N : ℕ+).val) : ℤ) : ℝ) = z ⟨i, a⟩
    rw [hval, hq ⟨i, a⟩]
    unfold WilsonFamily.mesh
    rw [← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  have hinj : Set.InjOn (latCoord C N p)
      ((Finset.univ : Finset (Fin n → OpenAIConfig.Site (C.period p * C.denominator N))) :
        Set (Fin n → OpenAIConfig.Site (C.period p * C.denominator N))) := by
    intro x _ y _ hxy
    funext i a
    have h1 := congrFun hxy ⟨i, a⟩
    unfold latCoord at h1
    have hm : C.mesh N ≠ 0 := by
      unfold WilsonFamily.mesh
      exact inv_ne_zero hD.ne'
    have h2 := mul_left_cancel₀ hm h1
    have h3 : ZMod.valMinAbs (x i a) = ZMod.valMinAbs (y i a) := by exact_mod_cast h2
    exact ZMod.valMinAbs_inj.mp h3
  rw [tsum_subtype S (fun z => ‖t (coordPts n z)‖), tsum_eq_sum hz, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.indicator_of_mem ((hS _).mpr ⟨fun ia => latCoord_bound C N p x ia,
    fun ia => ⟨_, latCoord_int C N p x ia⟩⟩)]
  rfl

/-- **L4: the lattice sum of a suitable test is eventually at most twice its `L¹` norm**: the
Riemann sums of `‖t‖` at spacing `1/denominator N` tend to `∫ ‖t‖`
(`tendsto_tsum_div_pow_atTop_integral`, through `coordPts`, which preserves volume); if
`∫ ‖t‖ = 0` the test vanishes.

DERIVED: `4` is the spacetime dimension; `2` the slack of the bound. -/
theorem riemann_le_two (C : WilsonFamily g) (p : ℕ) {n : ℕ} (t : WilsonFamily.SeparatedTest n)
    (hp : C.suitable p t) :
    ∀ᶠ N in atTop, C.mesh N ^ (4 * n) *
      ∑ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N), ‖t (ptsOf C N p x)‖
        ≤ 2 * ∫ y, ‖t y‖ := by
  classical
  have hΨmp : MeasurePreserving (coordPts n) :=
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin n) (_ : Fin 4) => ℝ)).measurePreserving.comp
      (PiLp.volume_preserving_toLp (ι := Σ _ : Fin n, Fin 4))
  have hΨemb : MeasurableEmbedding (coordPts n) :=
    (LinearIsometryEquiv.piLpCurry ℝ 2
      (fun (_ : Fin n) (_ : Fin 4) => ℝ)).toHomeomorph.measurableEmbedding.comp
      (MeasurableEquiv.toLp 2 ((Σ _ : Fin n, Fin 4) → ℝ)).measurableEmbedding
  have hΨc : Continuous (coordPts n) :=
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin n) (_ : Fin 4) => ℝ)).continuous.comp
      (PiLp.continuous_toLp 2 _)
  have hFc : Continuous fun z => ‖t (coordPts n z)‖ := (t.continuous.comp hΨc).norm
  have hI : ∫ z, ‖t (coordPts n z)‖ = ∫ y, ‖t y‖ := hΨmp.integral_comp hΨemb fun y => ‖t y‖
  have hP0 : (0 : ℝ) ≤ ((C.period p).val : ℝ) := Nat.cast_nonneg _
  have hbox : ∀ z, ‖t (coordPts n z)‖ ≠ 0 → ∀ ia : (Σ _ : Fin n, Fin 4),
      |z ia| < ((C.period p).val : ℝ) / 2 := by
    rintro z hz ⟨i, a⟩
    have hm : coordPts n z ∈ tsupport t := subset_tsupport _ (norm_ne_zero_iff.mp hz)
    exact abs_lt.mpr (hp hm i a)
  have hzero : ∀ z, z ∉ Set.Icc (fun _ : (Σ _ : Fin n, Fin 4) => -((C.period p).val : ℝ))
      (fun _ => ((C.period p).val : ℝ)) → ‖t (coordPts n z)‖ = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hb := hbox z hne
    refine Set.mem_Icc.mpr ⟨fun ia => ?_, fun ia => ?_⟩
    · have := abs_lt.mp (hb ia)
      show -((C.period p).val : ℝ) ≤ z ia
      linarith
    · have := abs_lt.mp (hb ia)
      show z ia ≤ ((C.period p).val : ℝ)
      linarith
  have T := tendsto_tsum_div_pow_atTop_integral
    (Set.Icc (fun _ : (Σ _ : Fin n, Fin 4) => -((C.period p).val : ℝ))
      (fun _ => ((C.period p).val : ℝ))) (fun z => ‖t (coordPts n z)‖) hFc
    (Metric.isBounded_Icc _ _) measurableSet_Icc
    (Convex.addHaar_frontier volume (convex_Icc _ _))
  have hden : Tendsto (fun N => ((C.denominator N : ℕ))) atTop atTop :=
    C.denominatorStrict.tendsto_atTop
  have T' := T.comp hden
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hI] at T'
  have T'' : Tendsto (fun N => C.mesh N ^ (4 * n) *
      ∑ x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N), ‖t (ptsOf C N p x)‖)
      atTop (nhds (∫ y, ‖t y‖)) := by
    refine T'.congr fun N => ?_
    haveI : NeZero ((C.denominator N : ℕ)) := ⟨(C.denominator N).ne_zero⟩
    simp only [Function.comp_apply]
    rw [tsum_lattice_eq C N p t hp _ ?hS]
    · rw [Fintype.card_sigma]
      simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [div_eq_inv_mul, ← inv_pow, mul_comm n 4]
      rfl
    · intro z
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨h1a, h1b⟩ := Set.mem_Icc.mp h1
        have h3 := (BoxIntegral.unitPartition.mem_smul_span_iff (n := (C.denominator N : ℕ))).mp h2
        refine ⟨fun ia => ⟨h1a ia, h1b ia⟩, fun ia => ?_⟩
        obtain ⟨q, hq⟩ := h3 ia
        exact ⟨q, by simpa using hq⟩
      · rintro ⟨h1, h3⟩
        refine ⟨Set.mem_Icc.mpr ⟨fun ia => (h1 ia).1, fun ia => (h1 ia).2⟩, ?_⟩
        refine (BoxIntegral.unitPartition.mem_smul_span_iff (n := (C.denominator N : ℕ))).mpr
          fun ia => ?_
        obtain ⟨q, hq⟩ := h3 ia
        exact ⟨q, by simpa using hq⟩
  by_cases hI0 : (∫ y, ‖t y‖) = 0
  · have hint : Integrable (fun y => ‖t y‖) :=
      t.continuous.norm.integrable_of_hasCompactSupport t.hasCompactSupport.norm
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => norm_nonneg (t y)) hint).mp hI0
    have heq := (Continuous.ae_eq_iff_eq (μ := volume) t.continuous.norm continuous_zero).mp hae
    have ht0 : ∀ y, t y = 0 := fun y => norm_eq_zero.mp (congrFun heq y)
    refine Filter.Eventually.of_forall fun N => ?_
    simp [ht0]
  · have hIpos : 0 < ∫ y, ‖t y‖ :=
      lt_of_le_of_ne (integral_nonneg fun _ => norm_nonneg _) (Ne.symm hI0)
    filter_upwards [T''.eventually (gt_mem_nhds (by linarith : (∫ y, ‖t y‖) < 2 * ∫ y, ‖t y‖))]
      with N hN using hN.le

end Riemann

/-! ## 5. The capstones -/

section Capstone

variable {g : OpenAIConfig.GaugeGroup}

/-- **Two tuples of sites apart in time by `d`**: after a cyclic shift of their time axis by `k`,
every site of `x` lies in the slices `0, …, W` and every site of `y` in the slices
`W + a, …, L − a`, with `a · mesh ≥ d`: the physical time gap between the two tuples on the torus is
at least `d` on both sides.

DERIVED: `3` is their time axis. -/
def SlicesApart (C : WilsonFamily g) (N p : ℕ) (d : ℝ) {n m : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N))
    (y : Fin m → OpenAIConfig.Site (C.period p * C.denominator N)) : Prop :=
  ∃ k W a : ℕ, d ≤ (a : ℝ) * C.mesh N ∧
    (∀ i, (x i 3 + (k : ZMod (C.period p * C.denominator N : ℕ+).val)).val ≤ W) ∧
    ∀ j, W + a ≤ (y j 3 + (k : ZMod (C.period p * C.denominator N : ℕ+).val)).val ∧
      (y j 3 + (k : ZMod (C.period p * C.denominator N : ℕ+).val)).val + a
        ≤ ((C.period p * C.denominator N : ℕ+) : ℕ)

/-- **Named input: the reflected lattice moments are bounded.** For every time floor `δ > 0` and
internal separation `ε > 0` there is one `M` such that, eventually along their order of limits,
their finite moment of `w ++ Θ ∘ w` at `(x, reflSite c 3 x')`, and of `Θ ∘ w ++ w` at
`(reflSite c₀ 3 x, reflSite c 3 (reflSite c₀ 3 x'))`, is at most `M` in norm whenever the placed
points of `x` and of `x'` lie in the box of the volume, are `ε` apart and the two groups of the
configuration are `δ/4` apart in time (`SlicesApart`). The bound is uniform in the spacing, the
volume, the plane and the spread of the points: it is where the renormalization of their insertions
enters.

DERIVED: `3` is their time axis; `4` quarters the floor; `2` halves the side. -/
def ReflectedMomentBound (C : WilsonFamily g) (order : ℕ → ℕ) {n : ℕ} (w : Fin n → C.Token)
    (Θ : C.Token → C.Token) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
    ∀ (c c₀ : ZMod (C.period p * C.denominator N : ℕ+).val)
      (x x' : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)),
      (∀ i a, -((C.period p).val / (2:ℝ)) < ptsOf C N p x i a ∧
        ptsOf C N p x i a < (C.period p).val / (2:ℝ)) →
      (∀ i a, -((C.period p).val / (2:ℝ)) < ptsOf C N p x' i a ∧
        ptsOf C N p x' i a < (C.period p).val / (2:ℝ)) →
      PtsSep ε (ptsOf C N p x) → PtsSep ε (ptsOf C N p x') →
      (SlicesApart C N p (δ / 4) x (fun i => reflSite c 3 (x' i)) →
        ‖C.finiteMoment N p (Fin.append w (fun j => Θ (w j)))
          (Fin.append x (fun i => reflSite c 3 (x' i)))‖ ≤ M) ∧
      (SlicesApart C N p (δ / 4) (fun i => reflSite c₀ 3 (x i))
          (fun i => reflSite c 3 (reflSite c₀ 3 (x' i))) →
        ‖C.finiteMoment N p (Fin.append (fun j => Θ (w j)) w)
          (Fin.append (fun i => reflSite c₀ 3 (x i))
            (fun i => reflSite c 3 (reflSite c₀ 3 (x' i))))‖ ≤ M)

/-- `ZMod.val` of a residue equal to the cast of an integer in `[0, L)` is that integer.

DERIVED: `0` is the lower end of the range. -/
theorem val_eq_of_eq_cast {L : ℕ+} {w : ZMod L.val} {z : ℤ} (hw : w = (z : ZMod L.val))
    (h0 : 0 ≤ z) (h1 : z < (L.val : ℤ)) : ((w.val : ℕ) : ℤ) = z := by
  subst hw
  exact val_intCast_of_nonneg L h0 h1

/-- The time of a site reflected along their time axis about `c` is `c` minus its time.

DERIVED: `3` is their time axis. -/
theorem reflSite_three {L : ℕ+} (c : ZMod L.val) (y : OpenAIConfig.Site L) :
    reflSite c 3 y 3 = c - y 3 := by
  simp [reflSite]

/-- **Two tuples apart from integer readings of their shifted times**: if after the shift `k` the
time of every site of `x` reads `fx i ∈ [0, W]` and of every site of `y` reads `fy j` with
`W + a ≤ fy j` and `fy j + a ≤ L`, where `0 < a`, `W < L` and `d ≤ a · mesh`, the two tuples are
`SlicesApart` by `d`.

DERIVED: `3` is their time axis; `0` the first slice. -/
theorem slicesApart_of_reads (C : WilsonFamily g) (N p : ℕ) {d : ℝ} {n m : ℕ}
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N))
    (y : Fin m → OpenAIConfig.Site (C.period p * C.denominator N)) (k W a : ℕ)
    (kz : ZMod (C.period p * C.denominator N : ℕ+).val)
    (hk : (k : ZMod (C.period p * C.denominator N : ℕ+).val) = kz)
    (fx : Fin n → ℤ) (fy : Fin m → ℤ) (hd : d ≤ (a : ℝ) * C.mesh N) (ha : 0 < a)
    (hWL : (W : ℤ) < ((C.period p * C.denominator N : ℕ+) : ℕ))
    (hx : ∀ i, x i 3 + kz = ((fx i : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val))
    (hx₀ : ∀ i, 0 ≤ fx i) (hxW : ∀ i, fx i ≤ W)
    (hy : ∀ j, y j 3 + kz = ((fy j : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val))
    (hyW : ∀ j, (W : ℤ) + a ≤ fy j)
    (hyL : ∀ j, fy j + a ≤ ((C.period p * C.denominator N : ℕ+) : ℕ)) :
    SlicesApart C N p d x y := by
  refine ⟨k, W, a, hd, fun i => ?_, fun j => ?_⟩
  · have h₀ := hx₀ i
    have hW := hxW i
    have e := val_eq_of_eq_cast (hk ▸ hx i) h₀ (by omega)
    omega
  · have hW := hyW j
    have hL := hyL j
    have e := val_eq_of_eq_cast (hk ▸ hy j) (by omega) (by omega)
    omega

/-- **The placements clear their reflection planes.** At a valid placement every pair of sites
supported by `t₁` sits with its reflected copies at the planes of the two readings of the first
group (`plane₁ + s₁`, and `plane₁` then `plane₁ + s₁`) at least `δ/4` apart in time, and every pair
supported by `t₂` likewise at the planes of the three readings of the second group: the supports
lie in the slabs (`supp₁`, `supp₂`), the reflected slabs have room on the torus (`room₁`,
`room₂`), and the `2a + 2` slices between them span `δ/4` (`sep`).

DERIVED: `2` doubles the widths and separations; `3` is their time axis; `4` quarters the floor. -/
theorem placement_clear {C : WilsonFamily g} {N p : ℕ} {n₁ n₂ : ℕ} {w₁ : Fin n₁ → C.Token}
    {w₂ : Fin n₂ → C.Token} {t₁ : WilsonFamily.SeparatedTest n₁}
    {t₂ : WilsonFamily.SeparatedTest n₂} {ℓ δ τ : ℝ} {P : SlabPlacement}
    (hP : P.Valid C N p w₁ w₂ t₁ t₂ ℓ δ τ) :
    (∀ x x' : Fin n₁ → OpenAIConfig.Site (C.period p * C.denominator N),
      t₁ (ptsOf C N p x) ≠ 0 → t₁ (ptsOf C N p x') ≠ 0 →
      SlicesApart C N p (δ / 4) x (fun i => reflSite
        (((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          + ((P.v + P.v + 2 + (P.a + P.a + 2) : ℕ) : ZMod _)) 3 (x' i)) ∧
      SlicesApart C N p (δ / 4)
        (fun i => reflSite ((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          3 (x i))
        (fun i => reflSite (((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          + ((P.v + P.v + 2 + (P.a + P.a + 2) : ℕ) : ZMod _)) 3
          (reflSite ((P.plane₁ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) 3
            (x' i)))) ∧
    (∀ x x' : Fin n₂ → OpenAIConfig.Site (C.period p * C.denominator N),
      t₂ (ptsOf C N p x) ≠ 0 → t₂ (ptsOf C N p x') ≠ 0 →
      SlicesApart C N p (δ / 4)
        (fun i => reflSite ((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          3 (x i))
        (fun i => reflSite (((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          + ((P.v' + P.v' + 2 + (P.a + P.a + 2) : ℕ) : ZMod _)) 3
          (reflSite ((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val) 3
            (x' i))) ∧
      SlicesApart C N p (δ / 4) x (fun i => reflSite
        (((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          + ((P.v' + P.v' + 2 + (P.a + P.a + 2) : ℕ) : ZMod _)) 3 (x' i)) ∧
      SlicesApart C N p (δ / 4) x (fun i => reflSite
        (((P.plane₂ : ℤ) : ZMod (C.period p * C.denominator N : ℕ+).val)
          + ((P.v' + P.v' + 2 + (P.aG + P.aG + 2) : ℕ) : ZMod _)) 3 (x' i))) := by
  have hL : ((C.period p * C.denominator N : ℕ+) : ℕ) = P.l + P.l + 2 := by
    rw [hP.side]; rfl
  have hstart : P.start = P.v + P.v + 2 + (P.a + P.j + P.a + 2 + 1) := rfl
  have haG : P.aG = P.l - (P.v' + P.v' + 2) - P.a - P.j - 2 := rfl
  have hr₁ := hP.room₁
  have hr₂ := hP.room₂
  have hA : δ / 4 ≤ ((P.a + P.a + 2 : ℕ) : ℝ) * C.mesh N := by push_cast; exact hP.sep
  have key : ∀ y : OpenAIConfig.Site (C.period p * C.denominator N),
      y 3 = ((((y 3 + (P.k : ZMod (C.period p * C.denominator N : ℕ+).val)).val : ℕ) : ℤ) :
        ZMod (C.period p * C.denominator N : ℕ+).val) - P.k := by
    intro y
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  refine ⟨fun x x' hx hx' => ?_, fun x x' hx hx' => ?_⟩
  · have h := hP.supp₁ x hx
    have h' := hP.supp₁ x' hx'
    refine ⟨slicesApart_of_reads C N p _ _ P.k (P.v + P.v + 2) (P.a + P.a + 2) _ rfl
      (fun i => (((x i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      (fun i => ((P.v + P.v + 2 + (P.v + P.v + 2 + (P.a + P.a + 2)) : ℕ) : ℤ)
        - (((x' i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      hA (by omega) (by omega) (fun i => ?_) (fun i => by omega) (fun i => by have := h i; omega)
      (fun i => ?_) (fun i => by have := h' i; omega)
      (fun i => by have := h' i; omega),
      slicesApart_of_reads C N p _ _ P.k (P.v + P.v + 2) (P.a + P.a + 2) _ rfl
      (fun i => ((P.v + P.v + 2 : ℕ) : ℤ) - (((x i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      (fun i => ((P.v + P.v + 2 + (P.a + P.a + 2) : ℕ) : ℤ)
        + (((x' i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      hA (by omega) (by omega) (fun i => ?_) (fun i => by have := h i; omega)
      (fun i => by have := h i; omega)
      (fun i => ?_) (fun i => by have := h' i; omega)
      (fun i => by have := h' i; omega)⟩
    · rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    · rw [reflSite_three]
      conv_lhs => rw [key (x' i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · rw [reflSite_three]
      conv_lhs => rw [key (x i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · rw [reflSite_three, reflSite_three]
      conv_lhs => rw [key (x' i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
  · have h := hP.supp₂ x hx
    have h' := hP.supp₂ x' hx'
    have hst : P.start ≤ ((C.period p * C.denominator N : ℕ+) : ℕ) := by omega
    have hk : ((P.k + (((C.period p * C.denominator N : ℕ+) : ℕ) - P.start) : ℕ) :
        ZMod (C.period p * C.denominator N : ℕ+).val)
        = (P.k : ZMod (C.period p * C.denominator N : ℕ+).val)
          - (P.start : ZMod (C.period p * C.denominator N : ℕ+).val) := by
      rw [Nat.cast_add, Nat.cast_sub hst, ZMod.natCast_self]
      ring
    refine ⟨slicesApart_of_reads C N p _ _ _ (P.v' + P.v' + 2) (P.a + P.a + 2) _ hk
      (fun i => ((P.start + (P.v' + P.v' + 2) : ℕ) : ℤ)
        - (((x i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      (fun i => ((P.v' + P.v' + 2 + (P.a + P.a + 2) : ℕ) : ℤ)
        + (((x' i 3 + (P.k : ZMod _)).val : ℕ) : ℤ) - (P.start : ℤ))
      hA (by omega) (by omega) (fun i => ?_) (fun i => by have := h i; omega)
      (fun i => by have := h i; omega)
      (fun i => ?_) (fun i => by have := h' i; omega)
      (fun i => by have := h' i; omega),
      slicesApart_of_reads C N p _ _ _ (P.v' + P.v' + 2) (P.a + P.a + 2) _ hk
      (fun i => (((x i 3 + (P.k : ZMod _)).val : ℕ) : ℤ) - (P.start : ℤ))
      (fun i => ((P.start + (P.v' + P.v' + 2) + (P.v' + P.v' + 2 + (P.a + P.a + 2)) : ℕ) : ℤ)
        - (((x' i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      hA (by omega) (by omega) (fun i => ?_) (fun i => by have := h i; omega)
      (fun i => by have := h i; omega)
      (fun i => ?_) (fun i => by have := h' i; omega)
      (fun i => by have := h' i; omega),
      slicesApart_of_reads C N p _ _ _ (P.v' + P.v' + 2) (P.a + P.a + 2) _ hk
      (fun i => (((x i 3 + (P.k : ZMod _)).val : ℕ) : ℤ) - (P.start : ℤ))
      (fun i => ((P.start + (P.v' + P.v' + 2) + (P.v' + P.v' + 2 + (P.aG + P.aG + 2)) : ℕ) : ℤ)
        - (((x' i 3 + (P.k : ZMod _)).val : ℕ) : ℤ))
      hA (by omega) (by omega) (fun i => ?_) (fun i => by have := h i; omega)
      (fun i => by have := h i; omega)
      (fun i => ?_) (fun i => by have := h' i; omega)
      (fun i => by have := h' i; omega)⟩
    · rw [reflSite_three]
      conv_lhs => rw [key (x i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · rw [reflSite_three, reflSite_three]
      conv_lhs => rw [key (x' i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · conv_lhs => rw [key (x i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · rw [reflSite_three]
      conv_lhs => rw [key (x' i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · conv_lhs => rw [key (x i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring
    · rw [reflSite_three]
      conv_lhs => rw [key (x' i)]
      simp only [SlabPlacement.plane₁, SlabPlacement.plane₂, Int.cast_sub, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul]
      ring

/-- **The norm of a weighted double sum**: if `‖F x x'‖ ≤ M` wherever both weights are nonzero, then
`‖mᵏ mᵏ Σ_{x,x'} a(x) b(x') F(x, x')‖ ≤ M (mᵏ Σ‖a‖)(mᵏ Σ‖b‖)`.

DERIVED: no numeral appears in the statement. -/
theorem norm_mesh_double_sum_le {X : Type*} [Fintype X] (m : ℝ) (hm : 0 ≤ m) (k : ℕ)
    (a b : X → ℂ) (F : X → X → ℂ) {M : ℝ}
    (hF : ∀ x x', a x ≠ 0 → b x' ≠ 0 → ‖F x x'‖ ≤ M) :
    ‖(m : ℂ) ^ k * (m : ℂ) ^ k * ∑ x, ∑ x', a x * b x' * F x x'‖
      ≤ M * ((m ^ k * ∑ x, ‖a x‖) * (m ^ k * ∑ x', ‖b x'‖)) := by
  have hterm : ∀ x x', ‖a x * b x' * F x x'‖ ≤ M * (‖a x‖ * ‖b x'‖) := by
    intro x x'
    rw [norm_mul, norm_mul]
    by_cases ha : a x = 0
    · simp [ha]
    by_cases hb : b x' = 0
    · simp [hb]
    calc ‖a x‖ * ‖b x'‖ * ‖F x x'‖ ≤ ‖a x‖ * ‖b x'‖ * M :=
          mul_le_mul_of_nonneg_left (hF x x' ha hb) (by positivity)
      _ = M * (‖a x‖ * ‖b x'‖) := by ring
  have hsum : ‖∑ x, ∑ x', a x * b x' * F x x'‖ ≤ ∑ x, ∑ x', M * (‖a x‖ * ‖b x'‖) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun x' _ => hterm x x'))
  have heq : ∑ x, ∑ x', M * (‖a x‖ * ‖b x'‖) = M * ((∑ x, ‖a x‖) * ∑ x', ‖b x'‖) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  have hmk : 0 ≤ m ^ k * m ^ k := by positivity
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hm]
  calc m ^ k * m ^ k * ‖∑ x, ∑ x', a x * b x' * F x x'‖
      ≤ m ^ k * m ^ k * (M * ((∑ x, ‖a x‖) * ∑ x', ‖b x'‖)) :=
        mul_le_mul_of_nonneg_left (hsum.trans (le_of_eq heq)) hmk
    _ = M * ((m ^ k * ∑ x, ‖a x‖) * (m ^ k * ∑ x', ‖b x'‖)) := by ring

/-- **The real part of the first complex moment is bounded by the moment bound** times the square
of the lattice sum of the test (`cMom_A_first`, `norm_mesh_double_sum_le`).

DERIVED: `4` is the spacetime dimension; `3` their time axis; `2` the square. -/
theorem re_cMom_A_first_le {C : WilsonFamily g} {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ}
    (w : Fin n → C.Token) (t tθ : WilsonFamily.SeparatedTest n)
    (c : ZMod (C.period p * C.denominator N : ℕ+).val) (htθ : ReflectedTest C N p c t tθ)
    (k q₁ q₂ s : ℕ) (hq : q₂ = q₁ + s) {M : ℝ}
    (hF : ∀ x x', t (ptsOf C N p x) ≠ 0 → t (ptsOf C N p x') ≠ 0 →
      ‖C.finiteMoment N p (Fin.append w (fun j => Θ (w j)))
        (Fin.append x (fun i => reflSite (c + (s : ZMod _)) 3 (x' i)))‖ ≤ M) :
    (cMom (C.period p * C.denominator N) (C.beta N p) C.haar (smearIns C N p w t)
        (smearIns C N p (fun j => Θ (w j)) tθ) k q₁ q₂).re
      ≤ M * (C.mesh N ^ (4 * n) * ∑ x, ‖t (ptsOf C N p x)‖) ^ 2 := by
  rw [cMom_A_first hΘ N p hc w t tθ c htθ k q₁ q₂ s hq]
  refine (Complex.re_le_norm _).trans ((norm_mesh_double_sum_le (C.mesh N) (mesh_nonneg C N)
    (4 * n) _ _ _ fun x x' hx hx' =>
      hF x x' hx ((map_ne_zero (starRingEnd ℂ)).mp hx')).trans (le_of_eq ?_))
  simp only [Complex.norm_conj]
  ring

/-- **The real part of the second complex moment is bounded by the moment bound** times the square
of the lattice sum of the test (`cMom_B_first`, `norm_mesh_double_sum_le`).

DERIVED: `4` is the spacetime dimension; `3` their time axis; `2` the square. -/
theorem re_cMom_B_first_le {C : WilsonFamily g} {Θ : C.Token → C.Token}
    (hΘ : TokenReflection C Θ) (N p : ℕ) (hc : ∀ v x, Continuous (C.insertion N p v x)) {n : ℕ}
    (w : Fin n → C.Token) (t tθ : WilsonFamily.SeparatedTest n)
    (c : ZMod (C.period p * C.denominator N : ℕ+).val) (htθ : ReflectedTest C N p c t tθ)
    (k q₁ q₂ s : ℕ) (hq : q₂ = q₁ + s) {M : ℝ}
    (hF : ∀ x x', t (ptsOf C N p x) ≠ 0 → t (ptsOf C N p x') ≠ 0 →
      ‖C.finiteMoment N p (Fin.append (fun j => Θ (w j)) w)
        (Fin.append (fun i => reflSite c 3 (x i))
          (fun i => reflSite (c + (s : ZMod _)) 3 (reflSite c 3 (x' i))))‖ ≤ M) :
    (cMom (C.period p * C.denominator N) (C.beta N p) C.haar
        (smearIns C N p (fun j => Θ (w j)) tθ) (smearIns C N p w t) k q₁ q₂).re
      ≤ M * (C.mesh N ^ (4 * n) * ∑ x, ‖t (ptsOf C N p x)‖) ^ 2 := by
  rw [cMom_B_first hΘ N p hc w t tθ c htθ k q₁ q₂ s hq]
  refine (Complex.re_le_norm _).trans ((norm_mesh_double_sum_le (C.mesh N) (mesh_nonneg C N)
    (4 * n) _ _ _ fun x x' hx hx' =>
      hF x x' ((map_ne_zero (starRingEnd ℂ)).mp hx) hx').trans (le_of_eq ?_))
  simp only [Complex.norm_conj]
  ring

/-- `M R² ≤ 4 M I²` when `0 ≤ R ≤ 2I`.

DERIVED: `2` is the slack of the lattice sum and the square; `4` is `2²`. -/
theorem le_four_mul_sq {M R I : ℝ} (hM : 0 ≤ M) (hR0 : 0 ≤ R) (hR : R ≤ 2 * I) :
    M * R ^ 2 ≤ 4 * M * I ^ 2 := by
  have h := pow_le_pow_left₀ hR0 hR 2
  calc M * R ^ 2 ≤ M * (2 * I) ^ 2 := mul_le_mul_of_nonneg_left h hM
    _ = 4 * M * I ^ 2 := by ring

set_option maxHeartbeats 1600000 in
/-- **The input (K₀) of `uniformDecayFrom_of_seed''` from the reflected moment bound**, with
`K₀ = 4 max(M₁, M₂)`, from the bounds `M₁`, `M₂` of the two groups. Each of the five
readings is at most the real part of one complex moment, its companion reading being nonnegative
(`moments_nonneg` through `momF_theta`, `momG_theta`; `le_re_of_pairs`); that complex moment is
a double sum of their finite moments at reflected configurations (`cMom_A_first`, `cMom_B_first`), bounded by `ReflectedMomentBound` at the configurations that
`placement_clear` keeps `δ/4` apart and whose groups `GroupSep` keeps `ε` apart; and the lattice sum
of each test is eventually at most twice its `L¹` norm (`riemann_le_two`, at volumes where the test
is suitable, which their convergence clause gives).

DERIVED: `4` is the square of the Riemann factor `2`; `2` doubles the widths, separations and the
half-side and is the square; `3` is the number of moments; `0` the first
slice; `1` the offsets. -/
theorem hK0_of_reflectedMomentBound (C : WilsonFamily g) (R : WilsonRegularity C)
    (order : ℕ → ℕ) {S : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ} (hW : C.Converges order S)
    {n₁ n₂ : ℕ} (w₁ : Fin n₁ → C.Token) (w₂ : Fin n₂ → C.Token) {ℓ : ℝ}
    {Θ : C.Token → C.Token} (hΘ : TokenReflection C Θ)
    (hB₁ : ReflectedMomentBound C order w₁ Θ) (hB₂ : ReflectedMomentBound C order w₂ Θ) :
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ K₀ : ℝ, 0 ≤ K₀ ∧
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
                ≤ K₀ * (∫ y, ‖t₂ y‖) ^ 2 := by
  intro δ ε hδ hε
  obtain ⟨M₁, hM₁0, hM₁⟩ := hB₁ δ ε hδ hε
  obtain ⟨M₂, hM₂0, hM₂⟩ := hB₂ δ ε hδ hε
  have hM0 : 0 ≤ max M₁ M₂ := le_max_of_le_left hM₁0
  refine ⟨4 * max M₁ M₂, by positivity, fun t t₁ t₂ τ _ hs₁ hs₂ _ _ => ?_⟩
  have hu₁ : ∀ᶠ p in Filter.map order atTop, C.suitable p t₁ := (hW n₁ w₁ t₁).1
  have hu₂ : ∀ᶠ p in Filter.map order atTop, C.suitable p t₂ := (hW n₂ w₂ t₂).1
  filter_upwards [hM₁, hM₂, hu₁, hu₂] with p hp₁ hp₂ hp₃ hp₄
  filter_upwards [hp₁, hp₂, riemann_le_two C p t₁ hp₃, riemann_le_two C p t₂ hp₄]
    with N hN₁ hN₂ hR₁ hR₂
  intro P hP tθ₁ tθ₂ h₁ h₂ i
  obtain ⟨hc₁, hc₂⟩ := placement_clear hP
  have hc := R.continuous N p
  have cA₁ := continuous_smearIns C N p hc w₁ t₁
  have cB₁ := continuous_smearIns C N p hc (fun j => Θ (w₁ j)) tθ₁
  have cA₂ := continuous_smearIns C N p hc w₂ t₂
  have cB₂ := continuous_smearIns C N p hc (fun j => Θ (w₂ j)) tθ₂
  have hRn₁ : 0 ≤ C.mesh N ^ (4 * n₁) * ∑ x, ‖t₁ (ptsOf C N p x)‖ :=
    mul_nonneg (pow_nonneg (mesh_nonneg C N) _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hRn₂ : 0 ≤ C.mesh N ^ (4 * n₂) * ∑ x, ‖t₂ (ptsOf C N p x)‖ :=
    mul_nonneg (pow_nonneg (mesh_nonneg C N) _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have sep₁ : ∀ x, t₁ (ptsOf C N p x) ≠ 0 → PtsSep ε (ptsOf C N p x) :=
    fun x hx => hs₁ _ (subset_tsupport _ hx)
  have sep₂ : ∀ x, t₂ (ptsOf C N p x) ≠ 0 → PtsSep ε (ptsOf C N p x) :=
    fun x hx => hs₂ _ (subset_tsupport _ hx)
  have box₁ : ∀ x, t₁ (ptsOf C N p x) ≠ 0 → ∀ i a, -((C.period p).val / (2:ℝ)) < ptsOf C N p x i a ∧
      ptsOf C N p x i a < (C.period p).val / (2:ℝ) :=
    fun x hx => hp₃ (subset_tsupport _ hx)
  have box₂ : ∀ x, t₂ (ptsOf C N p x) ≠ 0 → ∀ i a, -((C.period p).val / (2:ℝ)) < ptsOf C N p x i a ∧
      ptsOf C N p x i a < (C.period p).val / (2:ℝ) :=
    fun x hx => hp₄ (subset_tsupport _ hx)
  have hst : P.start ≤ P.l + P.l + 2 := by
    have f1 := hP.fit₁
    have f2 := hP.fit₂
    have f3 := hP.fit₃
    unfold SlabPlacement.start
    omega
  have nF0 : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
      (smearIns C N p w₁ t₁) (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (partF j) (partFR j) P.k 0
      (P.v + P.v + 2 + (P.a + P.a + 2)) := fun j => by
    have h := (moments_nonneg C R N p hP j 0).1
    rwa [(momF_theta C N p hΘ hP tθ₁ h₁ j).1] at h
  have nF1 : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
      (smearIns C N p (fun j => Θ (w₁ j)) tθ₁) (smearIns C N p w₁ t₁) (partFR j) (partF j) P.k 0
      (P.v + P.v + 2 + (P.a + P.a + 2)) := fun j => by
    have h := (moments_nonneg C R N p hP j 1).1
    rwa [(momF_theta C N p hΘ hP tθ₁ h₁ j).2.1] at h
  have nG0 : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
      (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (smearIns C N p w₂ t₂) (partGR j) (partG j) P.k
      (0 + (P.l + P.l + 2) - P.start)
      (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start) := fun j => by
    have h := (moments_nonneg C R N p hP j 0).2
    rwa [(momG_theta C N p hΘ hP tθ₂ h₂ j).1] at h
  have nG1 : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
      (smearIns C N p w₂ t₂) (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG j) (partGR j) P.k
      (0 + (P.l + P.l + 2) - P.start)
      (P.v' + P.v' + 2 + (P.a + P.a + 2) + (P.l + P.l + 2) - P.start) := fun j => by
    have h := (moments_nonneg C R N p hP j 1).2
    rwa [(momG_theta C N p hΘ hP tθ₂ h₂ j).2.1] at h
  have nG2 : ∀ j, 0 ≤ pairMom (C.period p * C.denominator N) (C.beta N p) C.haar
      (smearIns C N p w₂ t₂) (smearIns C N p (fun j => Θ (w₂ j)) tθ₂) (partG j) (partGR j) P.k
      (0 + (P.l + P.l + 2) - P.start)
      (P.v' + P.v' + 2 + (P.aG + P.aG + 2) + (P.l + P.l + 2) - P.start) := fun j => by
    have h := (moments_nonneg C R N p hP j 2).2
    rwa [(momG_theta C N p hΘ hP tθ₂ h₂ j).2.2] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (le_re_of_pairs C N p partF partFR _ _ _ nF0
      (split_F C N p cA₁ cB₁ _ _ _) i).trans ((re_cMom_A_first_le hΘ N p hc w₁ t₁ tθ₁ _ h₁ P.k 0
        _ _ (zero_add _).symm fun x x' hx hx' =>
          ((hN₁ _ 0 x x' (box₁ x hx) (box₁ x' hx')
            (sep₁ x hx) (sep₁ x' hx')).1 (hc₁ x x' hx hx').1).trans
            (le_max_left _ _)).trans (le_four_mul_sq hM0 hRn₁ hR₁))
  · refine (le_re_of_pairs C N p partFR partF _ _ _ nF1
      (split_FR C N p cB₁ cA₁ _ _ _) i).trans ((re_cMom_B_first_le hΘ N p hc w₁ t₁ tθ₁ _ h₁ P.k 0
        _ _ (zero_add _).symm fun x x' hx hx' =>
          ((hN₁ _ _ x x' (box₁ x hx) (box₁ x' hx')
            (sep₁ x hx) (sep₁ x' hx')).2 (hc₁ x x' hx hx').2).trans
            (le_max_left _ _)).trans (le_four_mul_sq hM0 hRn₁ hR₁))
  · refine (le_re_of_pairs C N p partGR partG _ _ _ nG0
      (split_GR C N p cB₂ cA₂ _ _ _) i).trans ((re_cMom_B_first_le hΘ N p hc w₂ t₂ tθ₂ _ h₂ P.k
        _ _ (P.v' + P.v' + 2 + (P.a + P.a + 2)) (by omega) fun x x' hx hx' =>
          ((hN₂ _ _ x x' (box₂ x hx) (box₂ x' hx')
            (sep₂ x hx) (sep₂ x' hx')).2 (hc₂ x x' hx hx').1).trans
            (le_max_right _ _)).trans (le_four_mul_sq hM0 hRn₂ hR₂))
  · refine (le_re_of_pairs C N p partG partGR _ _ _ nG1
      (split_G C N p cA₂ cB₂ _ _ _) i).trans ((re_cMom_A_first_le hΘ N p hc w₂ t₂ tθ₂ _ h₂ P.k
        _ _ (P.v' + P.v' + 2 + (P.a + P.a + 2)) (by omega) fun x x' hx hx' =>
          ((hN₂ _ 0 x x' (box₂ x hx) (box₂ x' hx')
            (sep₂ x hx) (sep₂ x' hx')).1 (hc₂ x x' hx hx').2.1).trans
            (le_max_right _ _)).trans (le_four_mul_sq hM0 hRn₂ hR₂))
  · refine (le_re_of_pairs C N p partG partGR _ _ _ nG2
      (split_G C N p cA₂ cB₂ _ _ _) i).trans ((re_cMom_A_first_le hΘ N p hc w₂ t₂ tθ₂ _ h₂ P.k
        _ _ (P.v' + P.v' + 2 + (P.aG + P.aG + 2)) (by omega) fun x x' hx hx' =>
          ((hN₂ _ 0 x x' (box₂ x hx) (box₂ x' hx')
            (sep₂ x hx) (sep₂ x' hx')).1 (hc₂ x x' hx hx').2.2).trans
            (le_max_right _ _)).trans (le_four_mul_sq hM0 hRn₂ hR₂))

set_option maxHeartbeats 1600000 in
/-- **The floored (U) from the seed with the reflected moment bound in place of (K₀).** As
`uniformDecayFrom_of_seed''`, with its input `hK₀` replaced by `ReflectedMomentBound` for both token
groups (`hK0_of_reflectedMomentBound`).

DERIVED: `16` and `1000` are the seed; `2` the base of the rate, the halved coupling and doubles
the widths, separations and the half-side; `4` the number of real pairs; `0` the signs and the first
slice; `1` the offsets. -/
theorem uniformDecayFrom_of_seed''' (C : WilsonFamily g) (R : WilsonRegularity C)
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
    (hB₁ : ReflectedMomentBound C order w₁ Θ) (hB₂ : ReflectedMomentBound C order w₂ Θ)
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
  uniformDecayFrom_of_seed'' C R order hW w₁ w₂ hn₁ hℓ hseed hsides Θ hΘ hθ
    (hK0_of_reflectedMomentBound C R order hW w₁ w₂ hΘ hB₁ hB₂) hD

end Capstone

#print axioms reflSite_add_single
#print axioms reflConfT_shift_iter
#print axioms transport_shift_iter
#print axioms reflConfT_transport_shift
#print axioms pairMom_re_add
#print axioms pairMom_negIm_swap
#print axioms pairMom_re_add'
#print axioms le_re_of_pairs
#print axioms split_F
#print axioms split_FR
#print axioms split_G
#print axioms split_GR
#print axioms integral_pairSum
#print axioms conj_smearIns_refl
#print axioms conj_smearIns_theta_refl
#print axioms integrand_A
#print axioms integrand_B
#print axioms cMom_A_first
#print axioms cMom_B_first
#print axioms mesh_nonneg
#print axioms latCoord_bound
#print axioms latCoord_int
#print axioms tsum_lattice_eq
#print axioms riemann_le_two
#print axioms norm_mesh_double_sum_le
#print axioms re_cMom_A_first_le
#print axioms re_cMom_B_first_le
#print axioms le_four_mul_sq
#print axioms val_eq_of_eq_cast
#print axioms reflSite_three
#print axioms slicesApart_of_reads
#print axioms placement_clear
#print axioms hK0_of_reflectedMomentBound
#print axioms uniformDecayFrom_of_seed'''

end MassGap.OpenAIBridgeK0
