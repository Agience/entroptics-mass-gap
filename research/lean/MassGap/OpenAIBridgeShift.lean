import Mathlib
import MassGap.OpenAIBridgeGlue

/-!
# MassGap.OpenAIBridgeShift — time-translation invariance of the mixed correlation

Their open input `OpenAILink.MixedTimeInvariance` is derived from two conditions on their Wilson
family and their convergence `WilsonFamily.Converges`.

## 1. One time step of their configurations

* `timeTranslate` — `pull` at the one-step link shift along their time axis
  (`ShiftInvG.shiftLinkPerm OpenAILink.timeAxis`);
* `timeTranslate_apply` — it reads `V` at the site one step later in time;
* `measurePreserving_timeTranslate` — it preserves their law (`measurePreserving_pull`).

## 2. The two lattice conditions

* `InsertionCovariance` — an insertion at the site one step later in time is the insertion read on
  the time-translated configuration;
* `DenominatorsDivide` — each spacing denominator divides infinitely many later ones;
* `finiteMoment_shift` — under `InsertionCovariance`, the finite moments are invariant under every
  lattice time shift.

## 3. Moving tests along the time axis

* `shiftPts_eq_add`, `mem_separated_shiftPts`, `shiftHomeo`;
* `tshift` — the test `t` moved by `τ` along the time axis.

## 4. The smeared lattice moments

* `place_add_single` — a lattice time shift by `k` moves the placed site by `k · mesh`, up to a
  multiple of the period;
* `smear_tshift` — when `t` and `t` moved by `k · mesh N` are both suitable at `p`, their smeared
  moments agree.

## 5. The limit

* `integral_tshift` — at every `τ` that is a lattice multiple at infinitely many spacings, the
  smeared limit correlation of `t` moved by `τ` is that of `t`;
* `invariant_of_tshift` — with continuity on `separated`, the limit correlation itself is invariant
  under `τ` (the fundamental lemma of the calculus of variations on `separated`);
* `invariant_all` — by `DenominatorsDivide`, these `τ` are dense, and the limit correlation is
  invariant under every time shift on `separated`;
* `mixedTimeInvariance_of_covariance` — `MixedTimeInvariance T` from `ReconstructedFields T`, their
  convergence to `correlation none`, `InsertionCovariance` and `DenominatorsDivide`.
-/

namespace MassGap.OpenAIBridgeShift

open MeasureTheory Filter Topology Set
open scoped ContDiff
open MassGap.OpenAIConfig MassGap.OpenAILink MassGap.OpenAIBridgeGlue

/-! ## 1. One time step of their configurations -/

section Step

variable (g : OpenAIConfig.GaugeGroup) (L : ℕ+)

/-- **One time step**: `pull` at the one-step link shift along their time axis.

DERIVED: no numeral appears in the statement. -/
noncomputable def timeTranslate [NeZero (L : ℕ)] :
    OpenAIConfig.Configuration g L ≃ᵐ OpenAIConfig.Configuration g L :=
  pullEquiv g L (MassGap.ShiftInvG.shiftLinkPerm timeAxis)

/-- **`timeTranslate` in their coordinates**: it reads `V` at the site one step later in time.

DERIVED: `1` is one step. -/
theorem timeTranslate_apply [NeZero (L : ℕ)] (V : OpenAIConfig.Configuration g L)
    (y : OpenAIConfig.Site L) (a : OpenAIConfig.Axis) :
    timeTranslate g L V (y, a) = V (y + Pi.single timeAxis 1, a) := by
  obtain ⟨x, rfl⟩ := (OpenAIConfig.siteEquiv L).surjective y
  rw [timeTranslate, pullEquiv_apply, pull_apply, MassGap.ShiftInvG.shiftLinkPerm_apply]
  exact congrArg (fun s => V (s, a)) (OpenAIConfig.siteEquiv_shift (l := L) timeAxis x)

/-- **`timeTranslate` preserves their law** (`measurePreserving_pull` at
`ShiftInvG.shiftLinkPerm`).

DERIVED: no numeral appears in the statement. -/
theorem measurePreserving_timeTranslate [NeZero (L : ℕ)] (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (β : ℝ) :
    MeasurePreserving (timeTranslate g L) (OpenAIConfig.wilsonLaw g L β μ)
      (OpenAIConfig.wilsonLaw g L β μ) :=
  measurePreserving_pull g L μ β _ (action_shiftLinkPerm g L timeAxis)

end Step

/-! ## 2. The two lattice conditions -/

section Covariance

variable {g : OpenAIConfig.GaugeGroup} (C : WilsonFamily g)

/-- **Time covariance of the insertions**: an insertion at the site one step later in time is the
insertion read on the time-translated configuration.

DERIVED: `1` is one step. -/
def InsertionCovariance : Prop :=
  ∀ (N p : ℕ) (w : C.Token) (y : OpenAIConfig.Site (C.period p * C.denominator N))
    (U : OpenAIConfig.Configuration g (C.period p * C.denominator N)),
    C.insertion N p w (y + Pi.single timeAxis 1) U
      = C.insertion N p w y (timeTranslate g (C.period p * C.denominator N) U)

/-- **Nested spacings**: each spacing denominator divides infinitely many later ones.

DERIVED: no numeral appears in the statement. -/
def DenominatorsDivide : Prop :=
  ∀ N₀ : ℕ, ∃ᶠ N in atTop, ((C.denominator N₀ : ℕ+) : ℕ) ∣ ((C.denominator N : ℕ+) : ℕ)

variable {C}

/-- One time step does not change a finite moment (`measurePreserving_timeTranslate`).

DERIVED: `1` is one step. -/
theorem finiteMoment_step (hI : InsertionCovariance C) (N p : ℕ) {n : ℕ} (v : Fin n → C.Token)
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) :
    C.finiteMoment N p v (fun i => x i + Pi.single timeAxis 1) = C.finiteMoment N p v x := by
  haveI := C.probability
  haveI := C.invariantHaar
  have h : ∀ U, (∏ i, C.insertion N p (v i) (x i + Pi.single timeAxis 1) U)
      = ∏ i, C.insertion N p (v i) (x i) (timeTranslate g _ U) :=
    fun U => Finset.prod_congr rfl fun i _ => hI N p (v i) (x i) U
  unfold WilsonFamily.finiteMoment
  refine (integral_congr_ae (Eventually.of_forall h)).trans ?_
  exact (measurePreserving_timeTranslate g _ C.haar _).integral_comp'
    (fun U => ∏ i, C.insertion N p (v i) (x i) U)

/-- `k` time steps do not change a finite moment.

DERIVED: `0` starts the induction; `1` is one step. -/
theorem finiteMoment_nat (hI : InsertionCovariance C) (N p : ℕ) {n : ℕ} (v : Fin n → C.Token)
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N)) (k : ℕ) :
    C.finiteMoment N p v
        (fun i => x i + Pi.single timeAxis (k : ZMod (C.period p * C.denominator N : ℕ+).val))
      = C.finiteMoment N p v x := by
  induction k with
  | zero =>
    congr 1
    funext i
    rw [Nat.cast_zero, Pi.single_zero, add_zero]
  | succ k ih =>
    have e : (fun i => x i + Pi.single timeAxis
          (((k + 1 : ℕ)) : ZMod (C.period p * C.denominator N : ℕ+).val))
        = fun i => (x i + Pi.single timeAxis (k : ZMod (C.period p * C.denominator N : ℕ+).val))
          + Pi.single timeAxis 1 := by
      funext i
      rw [Nat.cast_succ, Pi.single_add, add_assoc]
    rw [e, finiteMoment_step hI N p v, ih]

/-- **Every lattice time shift keeps the finite moments** under `InsertionCovariance`.

DERIVED: no numeral appears in the statement. -/
theorem finiteMoment_shift (hI : InsertionCovariance C) (N p : ℕ) {n : ℕ} (v : Fin n → C.Token)
    (x : Fin n → OpenAIConfig.Site (C.period p * C.denominator N))
    (z : ZMod (C.period p * C.denominator N : ℕ+).val) :
    C.finiteMoment N p v (fun i => x i + Pi.single timeAxis z) = C.finiteMoment N p v x := by
  have h := finiteMoment_nat hI N p v x z.val
  rwa [ZMod.natCast_zmod_val] at h

end Covariance

/-! ## 3. Moving tests along the time axis -/

section Tests

/-- The configuration with every point at `s` along the time axis.

DERIVED: `2` is the `L²` exponent. -/
noncomputable def cst (n : ℕ) (s : ℝ) : Points n :=
  WithLp.toLp 2 fun _ => WithLp.toLp 2 (Pi.single timeAxis s : Axis → ℝ)

/-- `shiftPts s` is the translation by `cst n s`.

DERIVED: no numeral appears in the statement. -/
theorem shiftPts_eq_add {n : ℕ} (s : ℝ) (y : Points n) : shiftPts s y = y + cst n s :=
  PiLp.ext fun i => PiLp.ext fun a => by simp [shiftPts, timeShift, cst, Pi.single_apply]

/-- `cst` is additive.

DERIVED: no numeral appears in the statement. -/
theorem cst_add (n : ℕ) (s r : ℝ) : cst n (s + r) = cst n s + cst n r :=
  PiLp.ext fun i => PiLp.ext fun a => by simp [cst, Pi.single_add]

/-- `cst n 0 = 0`.

DERIVED: `0` is the zero shift. -/
theorem cst_zero (n : ℕ) : cst n 0 = 0 :=
  PiLp.ext fun i => PiLp.ext fun a => by simp [cst]

/-- **A time shift keeps a configuration separated, and back.**

DERIVED: no numeral appears in the statement. -/
theorem mem_separated_shiftPts {n : ℕ} (s : ℝ) (y : Points n) :
    shiftPts s y ∈ WilsonFamily.separated n ↔ y ∈ WilsonFamily.separated n :=
  (timeShift_injective s).of_comp_iff y.ofLp

/-- The time shift by `s` as a homeomorphism of configurations.

DERIVED: no numeral appears in the statement. -/
noncomputable def shiftHomeo (n : ℕ) (s : ℝ) : Points n ≃ₜ Points n :=
  Homeomorph.addRight (cst n s)

/-- `shiftHomeo n s` is `shiftPts s`.

DERIVED: no numeral appears in the statement. -/
theorem shiftHomeo_apply {n : ℕ} (s : ℝ) (y : Points n) : shiftHomeo n s y = shiftPts s y :=
  (shiftPts_eq_add s y).symm

/-- **The test `t` moved by `τ` along the time axis**: `x ↦ t (x − τ e₃)`.

DERIVED: no numeral appears in the statement. -/
noncomputable def tshift {n : ℕ} (τ : ℝ) (t : WilsonFamily.SeparatedTest n) :
    WilsonFamily.SeparatedTest n where
  toFun x := t (shiftHomeo n (-τ) x)
  contDiff' := (TestFunctionClass.map_contDiff t).comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := (TestFunctionClass.map_hasCompactSupport t).comp_homeomorph _
  tsupport_subset' := by
    rw [show (fun x => t (shiftHomeo n (-τ) x)) = t ∘ shiftHomeo n (-τ) from rfl,
      tsupport_comp_eq_preimage]
    intro x hx
    have h := TestFunctionClass.tsupport_map_subset t hx
    rw [shiftHomeo_apply] at h
    exact (mem_separated_shiftPts (-τ) x).1 h

/-- `tshift τ t` at `x` is `t` at `x` moved back by `τ`.

DERIVED: no numeral appears in the statement. -/
theorem tshift_apply {n : ℕ} (τ : ℝ) (t : WilsonFamily.SeparatedTest n) (x : Points n) :
    tshift τ t x = t (shiftPts (-τ) x) := by
  rw [← shiftHomeo_apply]
  rfl

end Tests

/-! ## 4. The smeared lattice moments -/

section Smear

variable {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}

/-- `mesh N · (period p · denominator N) = period p`.

DERIVED: no numeral appears in the statement. -/
theorem mesh_mul_side (N p : ℕ) :
    C.mesh N * (((C.period p * C.denominator N : ℕ+) : ℕ) : ℝ) = ((C.period p : ℕ) : ℝ) := by
  have hd : (((C.denominator N : ℕ+) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [WilsonFamily.mesh, PNat.mul_coe, Nat.cast_mul]
  field_simp

/-- **A lattice time shift by `k`** moves the placed site by `k · mesh N` along the time axis, up to
a multiple of the period.

DERIVED: no numeral appears in the statement. -/
theorem place_add_single (N p : ℕ) (y : OpenAIConfig.Site (C.period p * C.denominator N)) (k : ℤ) :
    ∃ m : ℤ, C.place N p (y + Pi.single timeAxis (k : ZMod (C.period p * C.denominator N : ℕ+).val))
      = timeShift (k * C.mesh N - m * ((C.period p : ℕ) : ℝ)) (C.place N p y) := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub ((y timeAxis).valMinAbs + k)
    ((y timeAxis + (k : ZMod _)).valMinAbs) _).1
    (by rw [ZMod.coe_valMinAbs, Int.cast_add, ZMod.coe_valMinAbs])
  set l := ((C.period p * C.denominator N : ℕ+) : ℕ) with hl
  refine ⟨-m, PiLp.ext fun a => ?_⟩
  by_cases ha : a = timeAxis
  · subst ha
    have hm' : (((y timeAxis + (k : ZMod l)).valMinAbs : ℤ) : ℝ)
        = ((y timeAxis).valMinAbs : ℝ) + k + (l : ℝ) * m := by
      have e : (y timeAxis + (k : ZMod l)).valMinAbs = (y timeAxis).valMinAbs + k + (l : ℤ) * m := by
        linarith
      rw [e]
      push_cast
      ring
    have hs := mesh_mul_side (C := C) N p
    rw [← hl] at hs
    simp only [WilsonFamily.place, timeShift, WithLp.ofLp_toLp, Pi.add_apply, Pi.single_eq_same]
    rw [hm']
    push_cast
    linear_combination (m : ℝ) * hs
  · simp [WilsonFamily.place, timeShift, Pi.single_eq_of_ne ha]
    left
    show y a + (Pi.single timeAxis (k : ZMod l) : Axis → ZMod l) a = y a
    rw [Pi.single_eq_of_ne ha, add_zero]

/-- **The placed coordinates lie in `(−period/2, period/2]`** (`ZMod.valMinAbs_mem_Ioc`).

DERIVED: `2` halves the period. -/
theorem place_mem (N p : ℕ) (y : OpenAIConfig.Site (C.period p * C.denominator N)) (a : Axis) :
    -(((C.period p : ℕ) : ℝ) / 2) < C.place N p y a ∧ C.place N p y a ≤ ((C.period p : ℕ) : ℝ) / 2 := by
  have h := ZMod.valMinAbs_mem_Ioc (y a)
  have hs := mesh_mul_side (C := C) N p
  have hmesh : 0 < C.mesh N := by unfold WilsonFamily.mesh; positivity
  set l := ((C.period p * C.denominator N : ℕ+) : ℕ)
  have h1 : (-(l : ℝ)) < ((y a).valMinAbs : ℝ) * 2 := by exact_mod_cast h.1
  have h2 : ((y a).valMinAbs : ℝ) * 2 ≤ l := by exact_mod_cast h.2
  simp only [WilsonFamily.place, WithLp.ofLp_toLp]
  constructor
  · nlinarith
  · nlinarith

/-- **An integer multiple of the period that keeps a point of `(−P/2, P/2]` inside `(−P/2, P/2)`
is `0`.**

DERIVED: `0` is the conclusion; `2` halves the period; `1` the integer step. -/
theorem int_eq_zero_of_mem {P u : ℝ} (hP : 0 < P) {m : ℤ} (hu : -(P / 2) < u ∧ u ≤ P / 2)
    (hv : -(P / 2) < u + m * P ∧ u + m * P < P / 2) : m = 0 := by
  have h1 : (-1 : ℝ) < m := by
    by_contra h
    push Not at h
    nlinarith
  have h2 : (m : ℝ) < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < 1 := by exact_mod_cast h2
  omega

/-- **Smearing commutes with a lattice time shift**: when `t` and `t` moved by `k · mesh N` are both
suitable at `p`, their smeared moments agree under `InsertionCovariance`. The sum is reindexed by
the lattice shift (`finiteMoment_shift`); each term of `t` moved then equals the term of `t`: the
placed sites of the two sums differ by multiples of the period (`place_add_single`), and a nonzero
multiple puts a nonzero value outside the open box of one of the two tests (`place_mem`,
`int_eq_zero_of_mem`).

DERIVED: no numeral appears in the statement. -/
theorem smear_tshift (hI : InsertionCovariance C) (N p : ℕ) {n : ℕ} (v : Fin n → C.Token)
    (t : WilsonFamily.SeparatedTest n) (k : ℤ) (ht : C.suitable p t)
    (hs : C.suitable p (tshift (k * C.mesh N) t)) :
    C.smear N p v (tshift (k * C.mesh N) t) = C.smear N p v t := by
  classical
  set τ : ℝ := k * C.mesh N
  set P : ℝ := ((C.period p : ℕ) : ℝ)
  have hP : 0 < P := by positivity
  let e : Fin n → OpenAIConfig.Site (C.period p * C.denominator N) :=
    fun _ => Pi.single timeAxis (k : ZMod (C.period p * C.denominator N : ℕ+).val)
  unfold WilsonFamily.smear
  congr 1
  rw [← Equiv.sum_comp (Equiv.addRight e)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Equiv.coe_addRight]
  have hM : C.finiteMoment N p v (x + e) = C.finiteMoment N p v x :=
    finiteMoment_shift hI N p v x _
  rw [hM]
  congr 1
  choose m hm using fun i => place_add_single (C := C) N p (x i) k
  set Y : Points n := WithLp.toLp 2 fun i => C.place N p (x i)
  have hW : (WithLp.toLp 2 fun i => C.place N p ((x + e) i) : Points n)
      = WithLp.toLp 2 fun i => timeShift (τ - m i * P) (Y i) :=
    congrArg (WithLp.toLp 2) (funext fun i => hm i)
  rw [tshift_apply, hW]
  by_cases h0 : ∀ i, m i = 0
  · congr 1
    exact PiLp.ext fun i => PiLp.ext fun a => by
      by_cases ha : a = timeAxis <;> simp [h0 i, timeShift, Y, add_assoc, Pi.single_apply, ha]
  · push Not at h0
    obtain ⟨j, hj⟩ := h0
    have hY := place_mem (C := C) N p (x j) timeAxis
    have lhs : t (shiftPts (-τ) (WithLp.toLp 2 fun i => timeShift (τ - m i * P) (Y i))) = 0 := by
      by_contra hne
      have hmem := ht (subset_tsupport _ hne)
      have hb := hmem j timeAxis
      simp only [shiftPts_apply, timeShift, Y, WithLp.ofLp_toLp,
        Pi.single_eq_same] at hb
      exact hj (by
        have := int_eq_zero_of_mem hP hY (m := -m j) ⟨by push_cast; linarith [hb.1],
          by push_cast; linarith [hb.2]⟩
        omega)
    have rhs : t Y = 0 := by
      by_contra hne
      have hne' : tshift τ t (shiftPts τ Y) ≠ 0 := by
        rw [tshift_apply]
        convert hne using 2
        exact PiLp.ext fun i => PiLp.ext fun a => by
          by_cases ha : a = timeAxis <;> simp [timeShift, add_assoc, Pi.single_apply, ha]
      have hmem := hs (subset_tsupport _ hne')
      have hb := hmem j timeAxis
      have hXj := place_mem (C := C) N p
        (x j + Pi.single timeAxis (k : ZMod (C.period p * C.denominator N : ℕ+).val)) timeAxis
      rw [hm j] at hXj
      have hτ : τ = k * C.mesh N := rfl
      have hPd : P = ((C.period p : ℕ) : ℝ) := rfl
      simp only [shiftPts_apply, timeShift, Y, WithLp.ofLp_toLp,
        Pi.single_eq_same] at hb hXj
      exact hj (int_eq_zero_of_mem hP (u := C.place N p (x j) timeAxis + τ - m j * P) (m := m j)
        ⟨by linarith [hXj.1], by linarith [hXj.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩)
    rw [lhs, rhs]

end Smear

/-! ## 5. The limit -/

section Limit

variable {g : OpenAIConfig.GaugeGroup} {C : WilsonFamily g}

/-- **The smeared limit is invariant under a lattice time shift** at infinitely many spacings: from
`Converges` at `t` and at `t` moved, the rows agree at every volume where both are suitable
(`smear_tshift`, `tendsto_nhds_unique_of_frequently_eq`), and the two limits agree.

DERIVED: no numeral appears in the statement. -/
theorem integral_tshift (hI : InsertionCovariance C) {order : ℕ → ℕ}
    {G : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ} (hW : C.Converges order G) {n : ℕ}
    (v : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n) {τ : ℝ}
    (hτ : ∃ᶠ N in atTop, ∃ k : ℤ, τ = k * C.mesh N) :
    ∫ x, tshift τ t x * G v x = ∫ x, t x * G v x := by
  obtain ⟨ev1, row1, hrow1, hlim1⟩ := hW n v t
  obtain ⟨ev2, row2, hrow2, hlim2⟩ := hW n v (tshift τ t)
  have hrow : ∀ p, C.suitable p t → C.suitable p (tshift τ t) → row2 p = row1 p := fun p h1 h2 =>
    tendsto_nhds_unique_of_frequently_eq (hrow2 p h2) (hrow1 p h1) (hτ.mono fun N ⟨k, hk⟩ => by
      subst hk
      exact smear_tshift hI N p v t k h1 h2)
  refine tendsto_nhds_unique hlim2 (hlim1.congr' ?_)
  filter_upwards [ev1, ev2] with k h1 h2
  exact (hrow _ h1 h2).symm

/-- **A test times a function continuous on `separated` is integrable.**

DERIVED: no numeral appears in the statement. -/
theorem integrable_test_mul {n : ℕ} (t : WilsonFamily.SeparatedTest n) {f : Points n → ℂ}
    (hf : ContinuousOn f (WilsonFamily.separated n)) : Integrable (fun x => t x * f x) := by
  have hsub := TestFunctionClass.tsupport_map_subset t
  have hc : ContinuousOn (fun x => t x * f x) (tsupport t) :=
    ((TestFunctionClass.map_contDiff t).continuous.continuousOn).mul (hf.mono hsub)
  refine (hc.integrableOn_compact (TestFunctionClass.map_hasCompactSupport t)).integrable_of_forall_notMem_eq_zero
    fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- **Invariance from the smeared identity**: when the smeared limit of every test moved by `τ`
equals that of the test, a limit correlation continuous on `separated` is invariant under `τ` on
`separated`. The change of variables `x ↦ x + τ e₃` turns the identity into `∫ t · H = 0` with
`H = f(· + τ e₃) − f`; the fundamental lemma on the open set `separated`
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, real tests lifted to complex ones) and
continuity give `H = 0` there.

DERIVED: `0` is the value of `H`. -/
theorem invariant_of_tshift {n : ℕ} {f : Points n → ℂ}
    (hf : ContinuousOn f (WilsonFamily.separated n)) {τ : ℝ}
    (h : ∀ t : WilsonFamily.SeparatedTest n, ∫ x, tshift τ t x * f x = ∫ x, t x * f x) :
    ∀ x ∈ WilsonFamily.separated n, f (shiftPts τ x) = f x := by
  set U := (WilsonFamily.separated n : Set (Points n))
  have hU : IsOpen U := (WilsonFamily.separated n).isOpen
  have hmaps : ∀ x ∈ U, x + cst n τ ∈ U := fun x hx => by
    rw [← shiftPts_eq_add]; exact (mem_separated_shiftPts τ x).2 hx
  have hfs : ContinuousOn (fun x => f (x + cst n τ)) U :=
    hf.comp (continuous_id.add continuous_const).continuousOn hmaps
  set H : Points n → ℂ := fun x => f (x + cst n τ) - f x
  have hH : ContinuousOn H U := hfs.sub hf
  have hint : ∀ t : WilsonFamily.SeparatedTest n, ∫ x, t x * H x = 0 := fun t => by
    have hcv : ∫ x, tshift τ t x * f x = ∫ x, t x * f (x + cst n τ) := by
      rw [← integral_add_right_eq_self (fun x => tshift τ t x * f x) (cst n τ)]
      congr 1
      funext x
      rw [tshift_apply, shiftPts_eq_add, add_assoc, ← cst_add, add_neg_cancel, cst_zero, add_zero]
    have i1 := integrable_test_mul t hfs
    have i2 := integrable_test_mul t hf
    simp only [H, mul_sub]
    rw [integral_sub i1 i2, ← hcv, h t, sub_self]
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hH.locallyIntegrableOn hU.measurableSet) fun φ hφ hφc hφs => by
      let tc : WilsonFamily.SeparatedTest n :=
        { toFun := fun x => (φ x : ℂ)
          contDiff' := Complex.ofRealCLM.contDiff.comp hφ
          hasCompactSupport' := hφc.comp_left Complex.ofReal_zero
          tsupport_subset' := (tsupport_comp_subset Complex.ofReal_zero φ).trans hφs }
      have := hint tc
      simp only [Complex.real_smul]
      exact this
  have heq : EqOn H 0 U := Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hU.measurableSet).2 hae) hU hH continuousOn_const
  intro x hx
  have := heq hx
  simp only [H, Pi.zero_apply, sub_eq_zero] at this
  rw [shiftPts_eq_add]
  exact this

/-- **The spacing tends to `0`** (`WilsonFamily.denominatorStrict`).

DERIVED: `0` is the limit. -/
theorem tendsto_mesh (C : WilsonFamily g) : Tendsto C.mesh atTop (𝓝 0) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp C.denominatorStrict.tendsto_atTop
  exact tendsto_inv_atTop_zero.comp (h.congr fun N => rfl)

/-- **Every time shift keeps the limit correlation**: by `DenominatorsDivide` each `j · mesh N₀` is
a lattice multiple at infinitely many spacings (`integral_tshift`, `invariant_of_tshift`); the set
of invariant shifts is closed, and `⌊τ / mesh N⌋ · mesh N → τ`.

DERIVED: `1` bounds the floor error. -/
theorem invariant_all (hI : InsertionCovariance C) (hD : DenominatorsDivide C) {order : ℕ → ℕ}
    {G : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ} (hW : C.Converges order G) {n : ℕ}
    (v : Fin n → C.Token) (hG : ContinuousOn (G v) (WilsonFamily.separated n)) (τ : ℝ) :
    ∀ x ∈ WilsonFamily.separated n, G v (shiftPts τ x) = G v x := by
  intro x hx
  have hgood : ∀ (N₀ : ℕ) (j : ℤ), G v (shiftPts (j * C.mesh N₀) x) = G v x := fun N₀ j =>
    invariant_of_tshift hG (fun t => integral_tshift hI hW v t ((hD N₀).mono fun N ⟨q, hq⟩ => by
      refine ⟨j * q, ?_⟩
      have hd : (((C.denominator N : ℕ+) : ℕ) : ℝ) ≠ 0 := by positivity
      have hd0 : (((C.denominator N₀ : ℕ+) : ℕ) : ℝ) ≠ 0 := by positivity
      have hq' : (((C.denominator N : ℕ+) : ℕ) : ℝ) = ((C.denominator N₀ : ℕ+) : ℕ) * q := by
        exact_mod_cast hq
      have hq0 : (q : ℝ) ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hq'
        exact hd hq'
      simp only [WilsonFamily.mesh]
      rw [hq']
      push_cast
      field_simp)) x hx
  have hcl : IsClosed {s : ℝ | G v (shiftPts s x) = G v x} := by
    have hc : Continuous fun s : ℝ => G v (shiftPts s x) := by
      have hs : Continuous fun s : ℝ => x + cst n s :=
        continuous_const.add ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ =>
          (PiLp.continuous_toLp 2 _).comp (continuous_single (A := fun _ : Axis => ℝ) timeAxis)))
      simp_rw [shiftPts_eq_add]
      exact hG.comp_continuous hs fun s => by
        rw [← shiftPts_eq_add]; exact (mem_separated_shiftPts s x).2 hx
    exact isClosed_eq hc continuous_const
  let q : ℕ → ℝ := fun N => (⌊τ * ((C.denominator N : ℕ+) : ℕ)⌋ : ℝ) * C.mesh N
  have hq : Tendsto q atTop (𝓝 τ) := by
    have hlo : Tendsto (fun N => τ - C.mesh N) atTop (𝓝 τ) := by
      simpa using tendsto_const_nhds.sub (tendsto_mesh C)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun N => ?_) fun N => ?_
    · have hd : (0 : ℝ) < ((C.denominator N : ℕ+) : ℕ) := by positivity
      have := Int.sub_one_lt_floor (τ * ((C.denominator N : ℕ+) : ℕ))
      simp only [q, WilsonFamily.mesh]
      rw [le_mul_inv_iff₀ hd, sub_mul, inv_mul_cancel₀ hd.ne']
      linarith
    · have hd : (0 : ℝ) < ((C.denominator N : ℕ+) : ℕ) := by positivity
      have := Int.floor_le (τ * ((C.denominator N : ℕ+) : ℕ))
      simp only [q, WilsonFamily.mesh]
      rw [mul_inv_le_iff₀ hd]
      linarith
  exact hcl.mem_of_tendsto hq (Eventually.of_forall fun N => hgood N _)

/-- **Time-translation invariance of the mixed correlation** (`OpenAILink.MixedTimeInvariance`)
from `ReconstructedFields T` (`represents`, `smooth`), their convergence to `correlation none`,
`InsertionCovariance` and `DenominatorsDivide` (`invariant_all`).

DERIVED: no numeral appears in the statement. -/
theorem mixedTimeInvariance_of_covariance (T : HierarchyFields C) (hR : ReconstructedFields T)
    {order : ℕ → ℕ} (hW : C.Converges order (fun v => T.correlation none (T.project ∘ v)))
    (hI : InsertionCovariance C) (hD : DenominatorsDivide C) : MixedTimeInvariance T := by
  intro a τ
  obtain ⟨v, hv⟩ : ∃ v : Fin a.n → C.Token, T.project ∘ v = a.tags :=
    ⟨fun i => (hR.represents (a.tags i)).choose,
      funext fun i => (hR.represents (a.tags i)).choose_spec⟩
  have h := invariant_all hI hD hW v ((hR.smooth none (T.project ∘ v)).continuousOn) τ a.pts a.sep
  rw [hv] at h
  exact h

end Limit

end MassGap.OpenAIBridgeShift

#print axioms MassGap.OpenAIBridgeShift.timeTranslate_apply
#print axioms MassGap.OpenAIBridgeShift.measurePreserving_timeTranslate
#print axioms MassGap.OpenAIBridgeShift.finiteMoment_shift
#print axioms MassGap.OpenAIBridgeShift.smear_tshift
#print axioms MassGap.OpenAIBridgeShift.integral_tshift
#print axioms MassGap.OpenAIBridgeShift.invariant_of_tshift
#print axioms MassGap.OpenAIBridgeShift.invariant_all
#print axioms MassGap.OpenAIBridgeShift.mixedTimeInvariance_of_covariance
