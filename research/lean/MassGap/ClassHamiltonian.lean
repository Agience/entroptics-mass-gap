import Mathlib
import MassGap.ContinuumTimeGroup
import MassGap.ClayTiltedFull

noncomputable section

/-!
# MassGap.ClassHamiltonian — the Hamiltonian of the class reconstruction

`ContinuumSepClass.contTransferClassAlong hB hR m` is the reconstructed transfer data on class
monomials at the dyadic step `m`. Every step has the same reflection form and the same vacuum; only
the time step `TmClass m` changes. So the reconstructed Hilbert spaces of all steps are one type,
`ClassSpace hB hR`, and the vacuum is one vector, `classVac hB hR`. On it the steps are the operators
`classStep hB hR m`, positive, self-adjoint, with spectrum in `[0, 1]`, and two half steps are one
step, `classStep (m + 1) * classStep (m + 1) = classStep m` (`classStep_sq`, from
`ContinuumSepClass.TmClass_half` on the pre-Hilbert space and density).

## The semigroup

A positive square root is unique, so `classStep m = A ^ (1/2)^m` with `A = classStep 0`, the real power
taken in the continuous functional calculus (`ContinuumTimeGroup.eq_powT_of_sq`). The time
translation by `t ≥ 0` is `classTime t = A ^ (t / a_0)`, `a_0 = dySpacing N 0`. It agrees with the
dyadic steps, `classTime (n a_m) = classStep m ^ n`; it is a semigroup of positive self-adjoint
contractions; it is strongly continuous on `t ≥ 0`. Strong continuity at `0` is `ker A = 0`
(`classStep_zero_injective`): every class monomial is one step forward of another class monomial
once the step is below its separation margin (the class is closed under every translation), so a
vector killed by `A` is killed by every step and is orthogonal to every reconstructed monomial, and
these span a dense subspace.

## The Hamiltonian

`generator S` is the generator of a family `S : ℝ → E →L[ℂ] E`: its domain is the set of `u` at which
`t⁻¹ (u − S t u)` converges as `t → 0⁺`, and its value there is the limit. For
`S t = A ^ (t / a_0)` (`powSemigroup`), with `A` positive, injective, spectrum in `[0, 1]`:

* `resolvent A a_0 = cfc g A`, `g x = (1 − log x / a_0)⁻¹` for `x > 0` and `g 0 = 0`, continuous on
  `[0, 1]` (`continuousOn_resolventFun`), maps every vector into the domain with
  `H (R y) = y − R y` (`generator_resolvent`): `R = (1 + H)⁻¹`. The convergence is in norm on the dense
  range of `A`, with rate `4 t / a_0²`, and the difference operators are contractions
  (`resolventDiff_bounds`).
* `R` is injective (`A = cfc k A * R`, `k x = x − x log x / a_0`), so the domain is dense.
* The generator is symmetric (`generator_symm`, from the self-adjointness of every `S t`), and every
  pair `(w, z)` with `⟪z, x⟫ = ⟪w, H x⟫` on the domain has `w` in the domain with `H w = z`
  (`generator_of_inner`, through `R`). So `H† = H` (`powSemigroup_generator_isSelfAdjoint`).
* `H` is positive and annihilates the vacuum; on the vacuum complement
  `μ ‖u‖² ≤ re ⟪u, H u⟫` when `‖S t u‖ ≤ e^{−μ t} ‖u‖` there (`le_re_inner_generator`), and `ker H` is
  the vacuum line (`generator_ker`).

`classHamiltonian hB hR` is the generator of `classTime`. `HamiltonianAt hB hR μ` collects the
semigroup, its generator `H`, `H` self-adjoint and positive with `H Ω = 0`, the gap `μ` of `H` on the
vacuum complement, the vacuum the only ground state, and the spectrum of every `e^{−tH}` in
`{1} ∪ [0, e^{−μ t}]`. `hamiltonianAt_of_gapped`: the dyadic gaps at rate `μ > 0` give it.

## The capstone

`hamiltonian_of_clayClass`: `ClayContinuumPairClassAlong` at window `L > 0` names `c > 0` that gaps
every dyadic step at `e^{−(c/L) a_m}`; at that `c`, the class reconstruction carries `HamiltonianAt`
at `c / L`.

DERIVED (module-wide): `0` the time origin, the reference step, the zero vector, the vanishing vacuum
pairing and the bottom of the order; `1` the identity, the vacuum eigenvalue, the norm bound and the
unit coefficient; `1/2` the dyadic ratio; `2` the square of the norm; `4` in `Fin 4` the spacetime
dimension and the `4` of `4 t / a_0²`, which is `(2/a_0)²` from `e^{y} ≥ 1 + y` at `y = a_0 ℓ / 2`.
-/

namespace MassGap.ClassHamiltonian

open Filter Topology MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumSep MassGap.ContinuumSepClass
  MassGap.ContinuumTimeGroup

/-! ## 1. The generator of an operator family -/

section Generator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ℝ → E →L[ℂ] E)

/-- **The difference quotient** `t⁻¹ (u − S t u)`. -/
def diffQuot (u : E) (t : ℝ) : E := ((t⁻¹ : ℝ) : ℂ) • (u - S t u)

theorem diffQuot_add (u w : E) (t : ℝ) :
    diffQuot S (u + w) t = diffQuot S u t + diffQuot S w t := by
  unfold diffQuot
  rw [map_add, add_sub_add_comm, smul_add]

theorem diffQuot_smul (c : ℂ) (u : E) (t : ℝ) :
    diffQuot S (c • u) t = c • diffQuot S u t := by
  unfold diffQuot
  rw [map_smul, ← smul_sub, smul_comm]

/-- The vectors at which the difference quotient converges as `t → 0⁺`. -/
def genDomain : Submodule ℂ E where
  carrier := {u | ∃ v, Tendsto (diffQuot S u) (𝓝[>] 0) (𝓝 v)}
  zero_mem' := ⟨0, by
    have h : diffQuot S 0 = fun _ => 0 := by
      funext t
      simp [diffQuot]
    rw [h]
    exact tendsto_const_nhds⟩
  add_mem' := by
    rintro u w ⟨v, hv⟩ ⟨v', hv'⟩
    refine ⟨v + v', ?_⟩
    have h : diffQuot S (u + w) = fun t => diffQuot S u t + diffQuot S w t :=
      funext (diffQuot_add S u w)
    rw [h]
    exact hv.add hv'
  smul_mem' := by
    rintro c u ⟨v, hv⟩
    refine ⟨c • v, ?_⟩
    have h : diffQuot S (c • u) = fun t => c • diffQuot S u t := funext (diffQuot_smul S c u)
    rw [h]
    exact hv.const_smul c

/-- The limit of the difference quotient, linear on the domain. -/
def genLin : genDomain S →ₗ[ℂ] E where
  toFun u := limUnder (𝓝[>] (0 : ℝ)) (diffQuot S u)
  map_add' u w := by
    obtain ⟨v, hv⟩ := u.2
    obtain ⟨v', hv'⟩ := w.2
    have h : diffQuot S ((u + w : genDomain S) : E) = fun t => diffQuot S u t + diffQuot S w t :=
      funext (diffQuot_add S u w)
    rw [hv.limUnder_eq, hv'.limUnder_eq, h, (hv.add hv').limUnder_eq]
  map_smul' c u := by
    obtain ⟨v, hv⟩ := u.2
    have h : diffQuot S ((c • u : genDomain S) : E) = fun t => c • diffQuot S u t :=
      funext (diffQuot_smul S c u)
    rw [hv.limUnder_eq, h, (hv.const_smul c).limUnder_eq, RingHom.id_apply]

/-- **The generator** of `S`: the derivative `lim_{t → 0⁺} t⁻¹ (u − S t u)` on the vectors where it
exists. -/
def generator : E →ₗ.[ℂ] E := ⟨genDomain S, genLin S⟩

theorem mem_generator_domain_iff (u : E) :
    u ∈ (generator S).domain ↔ ∃ v, Tendsto (diffQuot S u) (𝓝[>] 0) (𝓝 v) := Iff.rfl

theorem mem_generator_domain {u v : E} (h : Tendsto (diffQuot S u) (𝓝[>] 0) (𝓝 v)) :
    u ∈ (generator S).domain := ⟨v, h⟩

theorem generator_apply {u : (generator S).domain} {v : E}
    (h : Tendsto (diffQuot S u) (𝓝[>] 0) (𝓝 v)) : generator S u = v :=
  h.limUnder_eq

theorem tendsto_generator (u : (generator S).domain) :
    Tendsto (diffQuot S u) (𝓝[>] 0) (𝓝 (generator S u)) := by
  obtain ⟨v, hv⟩ := u.2
  rw [generator_apply S hv]
  exact hv

#print axioms tendsto_generator

/-- **A vector fixed at every positive time is annihilated by the generator.** -/
theorem generator_vac {Ω : E} (hΩ : ∀ t : ℝ, 0 < t → S t Ω = Ω) :
    ∃ h : Ω ∈ (generator S).domain, generator S ⟨Ω, h⟩ = 0 := by
  have ht : Tendsto (diffQuot S Ω) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    show (0 : E) = ((t⁻¹ : ℝ) : ℂ) • (Ω - S t Ω)
    rw [hΩ t ht, sub_self, smul_zero]
  exact ⟨mem_generator_domain S ht, generator_apply S (u := ⟨Ω, mem_generator_domain S ht⟩) ht⟩

#print axioms generator_vac

theorem inner_diffQuot_symm [CompleteSpace E] (hsym : ∀ t : ℝ, 0 < t → IsSelfAdjoint (S t)) (u w : E) {t : ℝ}
    (ht : 0 < t) : inner ℂ (diffQuot S u t) w = inner ℂ u (diffQuot S w t) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hsym t ht)
  have h1 := hs u w
  simp only [ContinuousLinearMap.coe_coe] at h1
  unfold diffQuot
  rw [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, h1, Complex.conj_ofReal]

/-- **The generator is symmetric** when every `S t`, `t > 0`, is self-adjoint. -/
theorem generator_symm [CompleteSpace E] (hsym : ∀ t : ℝ, 0 < t → IsSelfAdjoint (S t))
    (u w : (generator S).domain) :
    inner ℂ (generator S u) (w : E) = inner ℂ (u : E) (generator S w) := by
  have h1 : Tendsto (fun t => inner ℂ (diffQuot S u t) (w : E)) (𝓝[>] 0)
      (𝓝 (inner ℂ (generator S u) (w : E))) :=
    (tendsto_generator S u).inner tendsto_const_nhds
  have h2 : Tendsto (fun t => inner ℂ (u : E) (diffQuot S w t)) (𝓝[>] 0)
      (𝓝 (inner ℂ (u : E) (generator S w))) :=
    tendsto_const_nhds.inner (tendsto_generator S w)
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact inner_diffQuot_symm S hsym u w ht

#print axioms generator_symm

theorem re_inner_diffQuot (u : E) (t : ℝ) :
    (inner ℂ u (diffQuot S u t)).re = t⁻¹ * (‖u‖ ^ 2 - (inner ℂ u (S t u)).re) := by
  unfold diffQuot
  rw [inner_smul_right, inner_sub_right, Complex.re_ofReal_mul, Complex.sub_re,
    ← inner_self_eq_norm_sq (𝕜 := ℂ) u]
  rfl

/-- **A form lower bound for the generator**: if `re ⟪u, S t u⟫ ≤ e^{−μ t} ‖u‖²` at every `t > 0`,
`μ ≥ 0`, then `μ ‖u‖² ≤ re ⟪u, H u⟫`. Through `t⁻¹ (1 − e^{−μ t}) ≥ μ / (1 + μ t)`. -/
theorem le_re_inner_generator {μ : ℝ} (hμ : 0 ≤ μ) (u : (generator S).domain)
    (hu : ∀ t : ℝ, 0 < t → (inner ℂ (u : E) (S t u)).re ≤ Real.exp (-(μ * t)) * ‖(u : E)‖ ^ 2) :
    μ * ‖(u : E)‖ ^ 2 ≤ (inner ℂ (u : E) (generator S u)).re := by
  have hlim : Tendsto (fun t => (inner ℂ (u : E) (diffQuot S u t)).re) (𝓝[>] 0)
      (𝓝 (inner ℂ (u : E) (generator S u)).re) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_const_nhds.inner (tendsto_generator S u))
  have hc : ContinuousAt (fun t : ℝ => μ / (1 + μ * t) * ‖(u : E)‖ ^ 2) 0 := by
    refine ContinuousAt.mul (ContinuousAt.div continuousAt_const ?_ ?_) continuousAt_const
    · exact continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    · simp
  have hlow : Tendsto (fun t : ℝ => μ / (1 + μ * t) * ‖(u : E)‖ ^ 2) (𝓝[>] 0)
      (𝓝 (μ * ‖(u : E)‖ ^ 2)) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [mul_zero, add_zero, div_one] at h
    exact h
  refine le_of_tendsto_of_tendsto hlow hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [re_inner_diffQuot]
  have h1t : 0 < 1 + μ * t := by positivity
  have hexp : Real.exp (-(μ * t)) ≤ 1 / (1 + μ * t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le h1t (by linarith [Real.add_one_le_exp (μ * t)])
  have h1 := hu t ht'
  have hn := sq_nonneg ‖(u : E)‖
  have e : t⁻¹ * (1 - 1 / (1 + μ * t)) = μ / (1 + μ * t) := by
    field_simp
    ring
  have h2 : (1 - 1 / (1 + μ * t)) * ‖(u : E)‖ ^ 2
      ≤ ‖(u : E)‖ ^ 2 - (inner ℂ (u : E) (S t u)).re := by
    nlinarith [mul_le_mul_of_nonneg_right hexp hn]
  calc μ / (1 + μ * t) * ‖(u : E)‖ ^ 2
      = t⁻¹ * ((1 - 1 / (1 + μ * t)) * ‖(u : E)‖ ^ 2) := by rw [← e]; ring
    _ ≤ t⁻¹ * (‖(u : E)‖ ^ 2 - (inner ℂ (u : E) (S t u)).re) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ht'.le)

#print axioms le_re_inner_generator

/-- **The generator is positive** when every `S t`, `t > 0`, is a contraction. -/
theorem re_inner_generator_nonneg (hc : ∀ t : ℝ, 0 < t → ‖S t‖ ≤ 1) (u : (generator S).domain) :
    0 ≤ (inner ℂ (u : E) (generator S u)).re := by
  have h := le_re_inner_generator S le_rfl u (fun t ht => by
    rw [zero_mul, neg_zero, Real.exp_zero, one_mul, sq]
    refine (re_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖S t u‖ ≤ ‖S t‖ * ‖(u : E)‖ := (S t).le_opNorm _
      _ ≤ 1 * ‖(u : E)‖ := mul_le_mul_of_nonneg_right (hc t ht) (norm_nonneg _)
      _ = ‖(u : E)‖ := one_mul _)
  simpa using h

#print axioms re_inner_generator_nonneg

/-- **The gap of the generator on the vacuum complement**: `‖S t u‖ ≤ e^{−μ t} ‖u‖` on the vacuum
complement at every `t > 0` gives `μ ‖u‖² ≤ re ⟪u, H u⟫` there. -/
theorem generator_gap {μ : ℝ} (hμ : 0 ≤ μ) {Ω : E}
    (hdec : ∀ t : ℝ, 0 < t → ∀ u : E, inner ℂ Ω u = 0 → ‖S t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
    (u : (generator S).domain) (hu : inner ℂ Ω (u : E) = 0) :
    μ * ‖(u : E)‖ ^ 2 ≤ (inner ℂ (u : E) (generator S u)).re :=
  le_re_inner_generator S hμ u (fun t ht => by
    refine (re_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    calc ‖(u : E)‖ * ‖S t u‖ ≤ ‖(u : E)‖ * (Real.exp (-(μ * t)) * ‖(u : E)‖) :=
          mul_le_mul_of_nonneg_left (hdec t ht u hu) (norm_nonneg _)
      _ = Real.exp (-(μ * t)) * ‖(u : E)‖ ^ 2 := by ring)

#print axioms generator_gap

/-- **The vacuum is the only ground state of the generator**: under a form gap `μ > 0` on the vacuum
complement, `H u = 0` puts `u` on the vacuum line. -/
theorem generator_ker {μ : ℝ} (hμ : 0 < μ) {Ω : E} (hΩn : ‖Ω‖ = 1)
    (hΩ : ∀ t : ℝ, 0 < t → S t Ω = Ω)
    (hgap : ∀ u : (generator S).domain, inner ℂ Ω (u : E) = 0 →
      μ * ‖(u : E)‖ ^ 2 ≤ (inner ℂ (u : E) (generator S u)).re)
    (u : (generator S).domain) (hu : generator S u = 0) : ∃ c : ℂ, (u : E) = c • Ω := by
  obtain ⟨hΩd, hG⟩ := generator_vac S hΩ
  set c : ℂ := inner ℂ Ω (u : E)
  set w : (generator S).domain := u - c • ⟨Ω, hΩd⟩ with hw
  have hΩΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩn]
    norm_num
  have hwo : inner ℂ Ω (w : E) = 0 := by
    rw [hw, Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right, hΩΩ,
      mul_one, sub_self]
  have hGw : generator S w = 0 := by
    rw [hw, LinearPMap.map_sub, LinearPMap.map_smul, hu, hG, smul_zero, sub_zero]
  have h := hgap w hwo
  rw [hGw, inner_zero_right, Complex.zero_re] at h
  have hn : ‖(w : E)‖ = 0 := by
    have h2 : ‖(w : E)‖ ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hμ hc
      linarith
    nlinarith [norm_nonneg (w : E)]
  refine ⟨c, ?_⟩
  have h0 : (w : E) = 0 := norm_eq_zero.mp hn
  rw [hw, Submodule.coe_sub, Submodule.coe_smul, sub_eq_zero] at h0
  exact h0

#print axioms generator_ker

end Generator

/-! ## 2. The generator of the real powers of a positive contraction -/

section Resolvent

/-- **The resolvent function** `g x = (1 − log x / a_0)⁻¹` for `x > 0`, `g x = 0` for `x ≤ 0`: the
function `(1 + H)⁻¹` of `A = e^{−a_0 H}`. -/
def resolventFun (a0 x : ℝ) : ℝ := if x ≤ 0 then 0 else (1 - Real.log x / a0)⁻¹

/-- **`g` is continuous on `[0, 1]`**: at `x > 0` it is a continuous expression, and at `0` it tends
to `0` because `log x → −∞`. -/
theorem continuousOn_resolventFun {a0 : ℝ} (ha0 : 0 < a0) :
    ContinuousOn (resolventFun a0) (Set.Icc 0 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with h0 | h0
  · subst h0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨Real.exp (-(a0 / ε)), Real.exp_pos _, fun {y} hy hyd => ?_⟩
    have hy0 : 0 ≤ y := hy.1
    have hlt : y < Real.exp (-(a0 / ε)) := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0] at hyd
      exact hyd
    have hg0 : resolventFun a0 0 = 0 := by simp [resolventFun]
    rw [hg0, Real.dist_eq, sub_zero]
    by_cases hy' : y ≤ 0
    · simp [resolventFun, hy', hε]
    · push Not at hy'
      have hlog : Real.log y < -(a0 / ε) := (Real.log_lt_iff_lt_exp hy').mpr hlt
      have h2 : ε⁻¹ < -Real.log y / a0 := by
        rw [lt_div_iff₀ ha0]
        have : ε⁻¹ * a0 = a0 / ε := by ring
        linarith
      have hD : ε⁻¹ < 1 - Real.log y / a0 := by
        have : -Real.log y / a0 = -(Real.log y / a0) := by ring
        linarith
      have hDpos : 0 < 1 - Real.log y / a0 := lt_trans (inv_pos.mpr hε) hD
      simp only [resolventFun, not_le.mpr hy', if_false]
      rw [abs_of_pos (inv_pos.mpr hDpos)]
      exact (inv_lt_comm₀ hDpos hε).mpr hD
  · have hx1 : x ≤ 1 := hx.2
    have hev : (fun y => (1 - Real.log y / a0)⁻¹) =ᶠ[𝓝 x] resolventFun a0 := by
      filter_upwards [lt_mem_nhds h0] with y hy
      simp [resolventFun, not_le.mpr hy]
    have hD : 1 - Real.log x / a0 ≠ 0 := by
      have h1 : Real.log x ≤ 0 := Real.log_nonpos h0.le hx1
      have h2 : Real.log x / a0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 ha0.le
      intro h
      linarith
    have hc : ContinuousAt (fun y => (1 - Real.log y / a0)⁻¹) x :=
      (continuousAt_const.sub ((Real.continuousAt_log h0.ne').div_const a0)).inv₀ hD
    exact (hc.congr hev).continuousWithinAt

#print axioms continuousOn_resolventFun

/-- **The difference function** `t⁻¹ (1 − x^{t/a_0}) g x − (1 − g x)`: the spectral function of
`t⁻¹ (R − S_t R) − (1 − R)`. -/
def resolventDiff (a0 t x : ℝ) : ℝ :=
  t⁻¹ * ((1 - x ^ (t / a0)) * resolventFun a0 x) - (1 - resolventFun a0 x)

/-- **The difference function is bounded by `1`, and by `4 t / a_0²` after multiplication by `x`**, on
`[0, 1]`. With `ℓ = −log x / a_0`, `y = t ℓ`: the value is `−(e^{−y} − 1 + y) / (t (1 + ℓ))`, and
`0 ≤ e^{−y} − 1 + y ≤ min(y, y²)` by `1 + z ≤ e^z`; `ℓ² e^{−a_0 ℓ} ≤ 4 / a_0²` by the same. -/
theorem resolventDiff_bounds {a0 t x : ℝ} (ha0 : 0 < a0) (ht : 0 < t) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |resolventDiff a0 t x| ≤ 1 ∧ |resolventDiff a0 t x * x| ≤ 4 * t / a0 ^ 2 := by
  rcases hx0.eq_or_lt with h0 | h0
  · subst h0
    have hz : resolventDiff a0 t 0 = -1 := by
      simp [resolventDiff, resolventFun]
    rw [hz, mul_zero, abs_zero]
    exact ⟨by norm_num, by positivity⟩
  · set L := Real.log x with hL
    have hLle : L ≤ 0 := Real.log_nonpos h0.le hx1
    set ℓ := -L / a0 with hℓ
    have hℓ0 : 0 ≤ ℓ := div_nonneg (by linarith) ha0.le
    have hD : 1 - L / a0 = 1 + ℓ := by rw [hℓ]; ring
    have hg : resolventFun a0 x = (1 + ℓ)⁻¹ := by
      simp only [resolventFun, not_le.mpr h0, if_false]
      rw [← hL, hD]
    have hpow : x ^ (t / a0) = Real.exp (-(t * ℓ)) := by
      rw [Real.rpow_def_of_pos h0, ← hL, hℓ]
      congr 1
      field_simp
    have hxe : x = Real.exp (-(a0 * ℓ)) := by
      rw [hℓ, ← Real.exp_log h0, ← hL]
      congr 1
      field_simp
    set Ee := Real.exp (-(t * ℓ)) with hEe
    have hy0 : 0 ≤ t * ℓ := mul_nonneg ht.le hℓ0
    have F1 : 1 - t * ℓ ≤ Ee := by linarith [Real.add_one_le_exp (-(t * ℓ))]
    have F2 : Ee ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have F3 : Ee * (1 + t * ℓ) ≤ 1 := by
      have h1 := Real.add_one_le_exp (t * ℓ)
      have h2 : Ee * Real.exp (t * ℓ) = 1 := by
        rw [hEe, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h3 : 0 ≤ Ee := (Real.exp_pos _).le
      nlinarith
    have hD1 : 0 < 1 + ℓ := by linarith
    have hval : resolventDiff a0 t x = -(Ee - 1 + t * ℓ) / (t * (1 + ℓ)) := by
      unfold resolventDiff
      rw [hg, hpow]
      field_simp
      ring
    have hq0 : 0 ≤ Ee - 1 + t * ℓ := by linarith
    have hq1 : Ee - 1 + t * ℓ ≤ t * ℓ := by linarith
    have hq2 : Ee - 1 + t * ℓ ≤ (t * ℓ) ^ 2 := by nlinarith
    have htD : 0 < t * (1 + ℓ) := mul_pos ht hD1
    have habs : |resolventDiff a0 t x| = (Ee - 1 + t * ℓ) / (t * (1 + ℓ)) := by
      rw [hval, neg_div, abs_neg, abs_of_nonneg (div_nonneg hq0 htD.le)]
    -- ℓ² e^{−a_0 ℓ} ≤ 4 / a_0²
    have F4 : ℓ ^ 2 * x ≤ 4 / a0 ^ 2 := by
      set Y := Real.exp (a0 * ℓ / 2) with hY
      have hY0 : 0 < Y := Real.exp_pos _
      have hY1 : a0 * ℓ / 2 + 1 ≤ Y := Real.add_one_le_exp _
      have hxY : x * (Y * Y) = 1 := by
        rw [hxe, hY, ← Real.exp_add, ← Real.exp_add]
        rw [show -(a0 * ℓ) + (a0 * ℓ / 2 + a0 * ℓ / 2) = 0 by ring, Real.exp_zero]
      have hlY : a0 * ℓ ≤ 2 * Y := by linarith
      have hsq : (a0 * ℓ) ^ 2 ≤ (2 * Y) ^ 2 := pow_le_pow_left₀ (by positivity) hlY 2
      rw [le_div_iff₀ (by positivity)]
      have hx0' : 0 ≤ x := h0.le
      nlinarith [mul_le_mul_of_nonneg_left hsq hx0']
    refine ⟨?_, ?_⟩
    · rw [habs, div_le_one htD]
      nlinarith
    · rw [abs_mul, habs, abs_of_pos h0]
      have hb : (Ee - 1 + t * ℓ) / (t * (1 + ℓ)) ≤ t * ℓ ^ 2 := by
        rw [div_le_iff₀ htD]
        nlinarith
      calc (Ee - 1 + t * ℓ) / (t * (1 + ℓ)) * x ≤ t * ℓ ^ 2 * x :=
            mul_le_mul_of_nonneg_right hb h0.le
        _ = t * (ℓ ^ 2 * x) := by ring
        _ ≤ t * (4 / a0 ^ 2) := mul_le_mul_of_nonneg_left F4 ht.le
        _ = 4 * t / a0 ^ 2 := by ring

#print axioms resolventDiff_bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The semigroup of real powers**: `S t = A ^ (t / a_0)`. -/
def powSemigroup (a : E →L[ℂ] E) (a0 : ℝ) (t : ℝ) : E →L[ℂ] E := powT a (t / a0)

/-- **The resolvent** `R = g(A)`, `(1 + H)⁻¹` for the generator `H` of `powSemigroup`. -/
def resolvent (a : E →L[ℂ] E) (a0 : ℝ) : E →L[ℂ] E := cfc (resolventFun a0) a

variable {a : E →L[ℂ] E} {a0 : ℝ}

theorem isSelfAdjoint_resolvent : IsSelfAdjoint (resolvent a a0) := by
  unfold resolvent
  exact cfc_predicate (resolventFun a0) a

/-- `t⁻¹ (R y − S_t R y) − (y − R y) = (cfc (resolventDiff a0 t) A) y`. -/
theorem diffQuot_resolvent_sub (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (ha0 : 0 < a0) {t : ℝ} (ht : 0 < t) (y : E) :
    diffQuot (powSemigroup a a0) (resolvent a a0 y) t - (y - resolvent a a0 y)
      = cfc (resolventDiff a0 t) a y := by
  have hg : ContinuousOn (resolventFun a0) (spectrum ℝ a) :=
    (continuousOn_resolventFun ha0).mono hsp
  have hh : 0 ≤ t / a0 := div_nonneg ht.le ha0.le
  have hp : ContinuousOn (fun x : ℝ => x ^ (t / a0)) (spectrum ℝ a) :=
    (Real.continuous_rpow_const hh).continuousOn
  have h1p : ContinuousOn (fun x : ℝ => 1 - x ^ (t / a0)) (spectrum ℝ a) :=
    continuousOn_const.sub hp
  have hpg : ContinuousOn (fun x : ℝ => (1 - x ^ (t / a0)) * resolventFun a0 x) (spectrum ℝ a) :=
    h1p.mul hg
  have hcpg : ContinuousOn (fun x : ℝ => t⁻¹ * ((1 - x ^ (t / a0)) * resolventFun a0 x))
      (spectrum ℝ a) := continuousOn_const.mul hpg
  have h1g : ContinuousOn (fun x : ℝ => 1 - resolventFun a0 x) (spectrum ℝ a) :=
    continuousOn_const.sub hg
  have hop : cfc (resolventDiff a0 t) a
      = t⁻¹ • ((cfc (fun _ : ℝ => (1 : ℝ)) a - powT a (t / a0)) * resolvent a a0)
        - (cfc (fun _ : ℝ => (1 : ℝ)) a - resolvent a a0) := by
    unfold resolventDiff powT resolvent
    rw [cfc_sub _ _ a hcpg h1g, cfc_const_mul _ _ a hpg, cfc_mul _ _ a h1p hg,
      cfc_sub _ _ a continuousOn_const hp, cfc_sub _ _ a continuousOn_const hg]
  rw [hop, cfc_const_one ℝ a ha]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  unfold diffQuot powSemigroup
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

#print axioms diffQuot_resolvent_sub

/-- **The resolvent maps into the domain of the generator**, with `H (R y) = y − R y`. The
difference operators `cfc (resolventDiff a0 t) A` are contractions and, composed with `A`, have
norm at most `4 t / a_0²`; the range of `A` is dense. -/
theorem tendsto_diffQuot_resolvent (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) (y : E) :
    Tendsto (diffQuot (powSemigroup a a0) (resolvent a a0 y)) (𝓝[>] 0)
      (𝓝 (y - resolvent a a0 y)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨w, hw, z, rfl⟩ :=
    Metric.dense_iff.mp (dense_range_of_injective ha hker) y (ε / 2) (by positivity)
  rw [Metric.mem_ball] at hw
  refine ⟨ε * a0 ^ 2 / (8 * (‖z‖ + 1)), by positivity, fun {t} ht htd => ?_⟩
  have ht0 : 0 < t := ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at htd
  rw [dist_eq_norm, diffQuot_resolvent_sub ha hsp ha0 ht0]
  have hcont : ContinuousOn (resolventDiff a0 t) (spectrum ℝ a) := by
    have hg : ContinuousOn (resolventFun a0) (spectrum ℝ a) :=
      (continuousOn_resolventFun ha0).mono hsp
    have hp : ContinuousOn (fun x : ℝ => x ^ (t / a0)) (spectrum ℝ a) :=
      (Real.continuous_rpow_const (div_nonneg ht0.le ha0.le)).continuousOn
    exact (continuousOn_const.mul ((continuousOn_const.sub hp).mul hg)).sub
      (continuousOn_const.sub hg)
  have hF : ‖cfc (resolventDiff a0 t) a‖ ≤ 1 :=
    norm_cfc_le zero_le_one (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (resolventDiff_bounds ha0 ht0 (hsp hx).1 (hsp hx).2).1)
  have hFa : ‖cfc (resolventDiff a0 t) a * a‖ ≤ 4 * t / a0 ^ 2 := by
    have hm : cfc (fun x => resolventDiff a0 t x * x) a = cfc (resolventDiff a0 t) a * a := by
      rw [cfc_mul (resolventDiff a0 t) (fun x : ℝ => x) a hcont (continuousOn_id' _), cfc_id' ℝ a ha]
    rw [← hm]
    exact norm_cfc_le (by positivity) (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (resolventDiff_bounds ha0 ht0 (hsp hx).1 (hsp hx).2).2)
  have hsplit : cfc (resolventDiff a0 t) a y
      = cfc (resolventDiff a0 t) a (y - a z) + (cfc (resolventDiff a0 t) a * a) z := by
    rw [map_sub, ContinuousLinearMap.mul_apply]
    abel
  have hA : ‖cfc (resolventDiff a0 t) a (y - a z)‖ ≤ ‖y - a z‖ :=
    ((cfc (resolventDiff a0 t) a).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hF)
  have hB : ‖(cfc (resolventDiff a0 t) a * a) z‖ ≤ 4 * t / a0 ^ 2 * ‖z‖ :=
    ((cfc (resolventDiff a0 t) a * a).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hFa (norm_nonneg _))
  have hC : 4 * t / a0 ^ 2 * ‖z‖ ≤ ε / 2 := by
    have hz1 : 0 < ‖z‖ + 1 := by positivity
    have h1 : 4 * t / a0 ^ 2 * ‖z‖
        ≤ 4 * (ε * a0 ^ 2 / (8 * (‖z‖ + 1))) / a0 ^ 2 * (‖z‖ + 1) := by
      apply mul_le_mul _ (by linarith) (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 4 * (ε * a0 ^ 2 / (8 * (‖z‖ + 1))) / a0 ^ 2 * (‖z‖ + 1) = ε / 2 := by
      field_simp
      ring
    linarith
  have hD : ‖y - a z‖ < ε / 2 := by rw [← dist_eq_norm, dist_comm]; exact hw
  rw [hsplit]
  calc ‖cfc (resolventDiff a0 t) a (y - a z) + (cfc (resolventDiff a0 t) a * a) z‖
      ≤ ‖cfc (resolventDiff a0 t) a (y - a z)‖ + ‖(cfc (resolventDiff a0 t) a * a) z‖ :=
        norm_add_le _ _
    _ < ε := by linarith

#print axioms tendsto_diffQuot_resolvent

theorem resolvent_mem_domain (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) (y : E) :
    resolvent a a0 y ∈ (generator (powSemigroup a a0)).domain :=
  mem_generator_domain _ (tendsto_diffQuot_resolvent ha hsp hker ha0 y)

/-- **`H (R y) = y − R y`**: `R = (1 + H)⁻¹`. -/
theorem generator_resolvent (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) (y : E) :
    generator (powSemigroup a a0) ⟨resolvent a a0 y, resolvent_mem_domain ha hsp hker ha0 y⟩
      = y - resolvent a a0 y :=
  generator_apply _ (u := ⟨resolvent a a0 y, resolvent_mem_domain ha hsp hker ha0 y⟩)
    (tendsto_diffQuot_resolvent ha hsp hker ha0 y)

#print axioms generator_resolvent

/-- **The resolvent is injective**: `A = cfc k A * R` with `k x = x − x log x / a_0`, and `A` is. -/
theorem resolvent_injective (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) (y : E) (hy : resolvent a a0 y = 0) : y = 0 := by
  have hg : ContinuousOn (resolventFun a0) (spectrum ℝ a) :=
    (continuousOn_resolventFun ha0).mono hsp
  have hk : ContinuousOn (fun x : ℝ => x - x * Real.log x / a0) (spectrum ℝ a) :=
    (continuous_id.sub (Real.continuous_mul_log.div_const a0)).continuousOn
  have hprod : cfc (fun x : ℝ => (x - x * Real.log x / a0) * resolventFun a0 x) a = a := by
    refine (cfc_congr (a := a) (g := fun x : ℝ => x) (fun x hx => ?_)).trans (cfc_id' ℝ a ha)
    have hx0 : 0 ≤ x := (hsp hx).1
    have hx1 : x ≤ 1 := (hsp hx).2
    rcases hx0.eq_or_lt with h0 | h0
    · subst h0
      simp
    · simp only [resolventFun, not_le.mpr h0, if_false]
      have hD : 1 - Real.log x / a0 ≠ 0 := by
        have h1 : Real.log x ≤ 0 := Real.log_nonpos h0.le hx1
        have h2 : Real.log x / a0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 ha0.le
        intro h
        linarith
      have e : x - x * Real.log x / a0 = x * (1 - Real.log x / a0) := by ring
      rw [e, mul_assoc, mul_inv_cancel₀ hD, mul_one]
  rw [cfc_mul _ _ a hk hg] at hprod
  apply hker
  rw [← hprod, ContinuousLinearMap.mul_apply]
  show cfc (fun x : ℝ => x - x * Real.log x / a0) a (resolvent a a0 y) = 0
  rw [hy, map_zero]

#print axioms resolvent_injective

/-- **The domain of the generator is dense**: it contains the range of the injective self-adjoint
resolvent. -/
theorem dense_generator_domain (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) :
    Dense ((generator (powSemigroup a a0)).domain : Set E) := by
  refine (dense_range_of_injective isSelfAdjoint_resolvent
    (resolvent_injective ha hsp hker ha0)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact resolvent_mem_domain ha hsp hker ha0 y

#print axioms dense_generator_domain

theorem isSelfAdjoint_powSemigroup (t : ℝ) : IsSelfAdjoint (powSemigroup a a0 t) :=
  isSelfAdjoint_powT _

/-- **The adjoint relation closes in the domain**: if `⟪z, x⟫ = ⟪w, H x⟫` for every `x` in the
domain, then `w = R (w + z)` is in the domain and `H w = z`. -/
theorem generator_of_inner (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) (w z : E)
    (h : ∀ x : (generator (powSemigroup a a0)).domain,
      inner ℂ z (x : E) = inner ℂ w (generator (powSemigroup a a0) x)) :
    ∃ hw : w ∈ (generator (powSemigroup a a0)).domain,
      generator (powSemigroup a a0) ⟨w, hw⟩ = z := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_resolvent (a := a) (a0 := a0))
  have key : ∀ y : E, inner ℂ z (resolvent a a0 y) = inner ℂ w (y - resolvent a a0 y) := by
    intro y
    rw [← generator_resolvent ha hsp hker ha0 y]
    exact h ⟨resolvent a a0 y, resolvent_mem_domain ha hsp hker ha0 y⟩
  have hu : resolvent a a0 (w + z) = w := by
    apply ext_inner_right ℂ
    intro y
    have h1 := hRsym (w + z) y
    simp only [ContinuousLinearMap.coe_coe] at h1
    rw [h1, inner_add_left, key y, inner_sub_right]
    ring
  have hdom : w ∈ (generator (powSemigroup a a0)).domain :=
    hu ▸ resolvent_mem_domain ha hsp hker ha0 (w + z)
  refine ⟨hdom, ?_⟩
  have e : generator (powSemigroup a a0) ⟨w, hdom⟩
      = generator (powSemigroup a a0)
          ⟨resolvent a a0 (w + z), resolvent_mem_domain ha hsp hker ha0 (w + z)⟩ :=
    congrArg (generator (powSemigroup a a0)) (Subtype.ext hu.symm)
  rw [e, generator_resolvent ha hsp hker ha0, hu]
  abel

#print axioms generator_of_inner

/-- **The generator of `A ^ (t / a_0)` is self-adjoint**: `H ≤ H†` by symmetry and density, and
`H† ≤ H` by `generator_of_inner`. -/
theorem powSemigroup_generator_isSelfAdjoint (ha : IsSelfAdjoint a)
    (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) (hker : ∀ x, a x = 0 → x = 0) (ha0 : 0 < a0) :
    IsSelfAdjoint (generator (powSemigroup a a0)) := by
  have hd := dense_generator_domain ha hsp hker ha0
  have hsym : ∀ t : ℝ, 0 < t → IsSelfAdjoint (powSemigroup a a0 t) :=
    fun t _ => isSelfAdjoint_powSemigroup t
  have hfa : (generator (powSemigroup a a0)).IsFormalAdjoint (generator (powSemigroup a a0)) :=
    fun x y => generator_symm _ hsym x y
  have h1 : generator (powSemigroup a a0) ≤ (generator (powSemigroup a a0)).adjoint :=
    hfa.le_adjoint hd
  have hadj := LinearPMap.adjoint_isFormalAdjoint hd (T := generator (powSemigroup a a0))
  have h2 : (generator (powSemigroup a a0)).adjoint ≤ generator (powSemigroup a a0) := by
    refine ⟨?_, ?_⟩
    · intro w hw
      exact (generator_of_inner ha hsp hker ha0 w _ (fun x => hadj ⟨w, hw⟩ x)).1
    · intro x y hxy
      obtain ⟨hw, hval⟩ := generator_of_inner ha hsp hker ha0 x _ (fun v => hadj x v)
      rw [← hval]
      exact congrArg (generator (powSemigroup a a0)) (Subtype.ext hxy)
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm h2 h1

#print axioms powSemigroup_generator_isSelfAdjoint

end Resolvent

/-! ## 3. The class reconstruction on one space -/

section ClassSpace

variable {N : ℕ}

/-- **Every class monomial is one step forward of a class monomial**, at a step finer than its
margin: shift it back by `a_m < d`; the class is closed under translation and the separation is
kept. -/
theorem exists_shift_preimage_class (hN : N ≠ 0) {τ : Fin 4} {𝒯 : TestClass}
    (Q : ClassMono N τ 𝒯) : ∃ (m : ℕ) (Q' : ClassMono N τ 𝒯), ClassMono.shift hN τ m Q' = Q := by
  obtain ⟨⟨P1, d, hd, hP⟩, hmem⟩ := Q
  obtain ⟨m, hm⟩ := ((tendsto_dySpacing N).eventually (gt_mem_nhds hd)).exists
  have ham := dySpacing_pos (one_le_of_ne_zero hN) m
  refine ⟨m, ⟨⟨Mono.shift (timeVec N m τ (-1)) P1, d - dySpacing N m, by linarith, ?_⟩,
    fun i => 𝒯.translate_mem _ _ (hmem i)⟩, ?_⟩
  · refine ⟨fun i y hy => ?_, fun i j hij =>
      sepBy_translate ((sepPos_mono hP (by linarith : d - dySpacing N m ≤ d)).2 i j hij) _⟩
    have h1 := hP.1 i (y - timeVec N m τ (-1)) hy
    have h2 : (y - timeVec N m τ (-1)) τ = y τ - timeVec N m τ (-1) τ := rfl
    rw [h2, timeVec_self] at h1
    push_cast at h1
    linarith
  · apply Subtype.ext
    apply Subtype.ext
    show Mono.shift (timeVec N m τ 1) (Mono.shift (timeVec N m τ (-1)) P1) = P1
    rw [Mono.shift_shift, timeVec_add, neg_add_cancel, timeVec_zero, Mono.shift_zero]

#print axioms exists_shift_preimage_class

variable {hN : N ≠ 0} {βs : ℕ → ℝ} {ρ : Renorm N} {τ : Fin 4} {𝒯 : TestClass}
  (hB : PairBoundClassAlong hN βs ρ τ 𝒯) (hR : ρ.ReflCompat τ)

/-- **The one reconstructed Hilbert space** of the class transfers: every step has the reflection
form of step `0`. -/
abbrev ClassSpace : Type :=
  GNSHilbert.H (contTransferClassAlong hB hR 0).toReflForm

/-- **The step-`m` transfer on the one space**: the time translation by `dySpacing N m`. -/
def classStep (m : ℕ) : ClassSpace hB hR →L[ℂ] ClassSpace hB hR :=
  GNSHilbert.opT (contTransferClassAlong hB hR m)

/-- **The one vacuum.** -/
def classVac : ClassSpace hB hR :=
  GNSHilbert.Omega (contTransferClassAlong hB hR 0).toReflForm (contTransferClassAlong hB hR 0).vac

theorem classStep_coe (m : ℕ) (z : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) :
    classStep hB hR m (z : ClassSpace hB hR)
      = ((GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm
          ((contTransferClassAlong hB hR m).T (z : _ × _).1)
          ((contTransferClassAlong hB hR m).T (z : _ × _).2)
          : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) : ClassSpace hB hR) :=
  GNSHilbert.opT_coe (contTransferClassAlong hB hR m) z

/-- **Two half steps are one step**: `classStep (m+1)² = classStep m` (`TmClass_half` on the
pre-Hilbert space, then density). -/
theorem classStep_sq (m : ℕ) :
    classStep hB hR (m + 1) * classStep hB hR (m + 1) = classStep hB hR m := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (classStep hB hR (m + 1) * classStep hB hR (m + 1)).continuous
      (classStep hB hR m).continuous) (fun z => ?_)
  rw [ContinuousLinearMap.mul_apply, classStep_coe, classStep_coe, classStep_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show TmClass hN τ 𝒯 (m + 1) (TmClass hN τ 𝒯 (m + 1) _) = TmClass hN τ 𝒯 m _
    exact (TmClass_half hN τ 𝒯 m _).symm
  · show TmClass hN τ 𝒯 (m + 1) (TmClass hN τ 𝒯 (m + 1) _) = TmClass hN τ 𝒯 m _
    exact (TmClass_half hN τ 𝒯 m _).symm

#print axioms classStep_sq

theorem isSelfAdjoint_classStep (m : ℕ) : IsSelfAdjoint (classStep hB hR m) :=
  GNSHilbert.isSelfAdjoint_opT _

/-- **Every step is positive** (`positiveTransfer_class`). -/
theorem classStep_nonneg (m : ℕ) : 0 ≤ classStep hB hR m :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (GNSHilbert.isPositive_opT _ (positiveTransfer_class hB hR m))

theorem spectrum_classStep (m : ℕ) : spectrum ℝ (classStep hB hR m) ⊆ Set.Icc 0 1 :=
  fun _ hx => ⟨GNSHilbert.spectrum_opT_nonneg _ (positiveTransfer_class hB hR m) hx,
    (GNSHilbert.spectrum_opT_subset_unit_interval _ hx).2⟩

theorem classStep_vac (m : ℕ) : classStep hB hR m (classVac hB hR) = classVac hB hR :=
  GNSHilbert.opT_Omega (contTransferClassAlong hB hR m)

theorem norm_classVac : ‖classVac hB hR‖ = 1 :=
  GNSHilbert.norm_Omega_vac (contTransferClassAlong hB hR 0)

/-- **The steps are the dyadic roots of step `0`**: `classStep m = (classStep 0) ^ (1/2)^m`. -/
theorem classStep_eq_powT (m : ℕ) :
    classStep hB hR m = powT (classStep hB hR 0) ((1 / 2 : ℝ) ^ m) :=
  eq_powT_of_sq (isSelfAdjoint_classStep hB hR 0) (spectrum_classStep hB hR 0)
    (classStep hB hR) rfl (classStep_nonneg hB hR) (classStep_sq hB hR) m

#print axioms classStep_eq_powT

/-! ### The kernel of step `0` is trivial -/

/-- The reconstructed vector of a class monomial. -/
def classVec (Q : ClassMono N τ 𝒯) : ClassSpace hB hR :=
  ((GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm (Finsupp.single Q 1) 0
    : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) : ClassSpace hB hR)

/-- **The step moves a monomial forward.** -/
theorem classStep_classVec (m : ℕ) (Q : ClassMono N τ 𝒯) :
    classStep hB hR m (classVec hB hR Q) = classVec hB hR (ClassMono.shift hN τ m Q) := by
  unfold classVec
  rw [classStep_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (ClassMono.shift hN τ m) (Finsupp.single Q 1)
      = Finsupp.single (ClassMono.shift hN τ m Q) 1
    exact Finsupp.mapDomain_single
  · show (contTransferClassAlong hB hR m).T 0 = 0
    exact map_zero _

/-- A vector killed by step `m` is killed by step `m + 1`. -/
theorem classStep_succ_eq_zero {m : ℕ} {x : ClassSpace hB hR}
    (hx : classStep hB hR m x = 0) : classStep hB hR (m + 1) x = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_classStep hB hR (m + 1))
  have h1 : classStep hB hR (m + 1) (classStep hB hR (m + 1) x) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, classStep_sq, hx]
  have h2 : inner ℂ (classStep hB hR (m + 1) x) (classStep hB hR (m + 1) x) = 0 := by
    have := hsym x (classStep hB hR (m + 1) x)
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h2

/-- **Orthogonal to the monomials is orthogonal to the pre-Hilbert space.** -/
theorem inner_pre_eq_zero_class (x : ClassSpace hB hR)
    (horth : ∀ Q : ClassMono N τ 𝒯, inner ℂ x (classVec hB hR Q) = 0)
    (z : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) :
    inner ℂ x (z : ClassSpace hB hR) = 0 := by
  have hlin : ∀ c : ClassMono N τ 𝒯 →₀ ℝ,
      inner ℂ x ((GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm c 0
        : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) : ClassSpace hB hR) = 0 := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      have h0 : (GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm
          (0 : ClassMono N τ 𝒯 →₀ ℝ) 0
          : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm) = 0 :=
        GNSHilbert.Pre.ext rfl rfl
      rw [h0, UniformSpace.Completion.coe_zero, inner_zero_right]
    | add f g hf hg =>
      have h0 : (GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm (f + g) 0
          : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm)
          = GNSHilbert.Pre.ofPair _ f 0 + GNSHilbert.Pre.ofPair _ g 0 :=
        GNSHilbert.Pre.ext rfl
          (show (0 : ClassMono N τ 𝒯 →₀ ℝ) = 0 + 0 from (add_zero 0).symm)
      rw [h0, UniformSpace.Completion.coe_add, inner_add_right, hf, hg, add_zero]
    | single Q b =>
      have h0 : (GNSHilbert.Pre.ofPair (contTransferClassAlong hB hR 0).toReflForm
          (Finsupp.single Q b) 0 : GNSHilbert.Pre (contTransferClassAlong hB hR 0).toReflForm)
          = (b : ℂ) • GNSHilbert.Pre.ofPair _ (Finsupp.single Q 1) 0 := by
        refine GNSHilbert.Pre.ext ?_ ?_
        · show Finsupp.single Q b
            = (b : ℂ).re • Finsupp.single Q (1 : ℝ) + (-(b : ℂ).im) • (0 : ClassMono N τ 𝒯 →₀ ℝ)
          simp only [Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_smul, add_zero,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        · show (0 : ClassMono N τ 𝒯 →₀ ℝ)
            = (b : ℂ).re • (0 : ClassMono N τ 𝒯 →₀ ℝ) + (b : ℂ).im • Finsupp.single Q (1 : ℝ)
          simp only [Complex.ofReal_im, zero_smul, smul_zero, add_zero]
      rw [h0, UniformSpace.Completion.coe_smul, inner_smul_right]
      exact mul_eq_zero_of_right _ (horth Q)
  have hz : z = GNSHilbert.Pre.ofPair _ (z : _ × _).1 0
      + Complex.I • GNSHilbert.Pre.ofPair _ (z : _ × _).2 0 := by
    refine GNSHilbert.Pre.ext ?_ ?_
    · show (z : _ × _).1 = (z : _ × _).1 + (Complex.I.re • (z : _ × _).2
        + (-Complex.I.im) • (0 : ClassMono N τ 𝒯 →₀ ℝ))
      simp only [Complex.I_re, Complex.I_im, zero_smul, smul_zero, add_zero]
    · show (z : _ × _).2 = (0 : ClassMono N τ 𝒯 →₀ ℝ)
        + (Complex.I.re • (0 : ClassMono N τ 𝒯 →₀ ℝ) + Complex.I.im • (z : _ × _).2)
      simp only [Complex.I_re, Complex.I_im, smul_zero, one_smul, zero_add]
  rw [hz, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul, inner_add_right,
    inner_smul_right, hlin, hlin, mul_zero, add_zero]

/-- **Step `0` has trivial kernel.** A vector killed by step `0` is killed by every step, hence
orthogonal to every reconstructed class monomial (`exists_shift_preimage_class`), hence to the dense
pre-Hilbert space. -/
theorem classStep_zero_injective (x : ClassSpace hB hR) (hx : classStep hB hR 0 x = 0) :
    x = 0 := by
  have hall : ∀ m, classStep hB hR m x = 0 := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih => exact classStep_succ_eq_zero hB hR ih
  have horth : ∀ Q : ClassMono N τ 𝒯, inner ℂ x (classVec hB hR Q) = 0 := by
    intro Q
    obtain ⟨m, Q', hQ'⟩ := exists_shift_preimage_class hN Q
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_classStep hB hR m)
    rw [← hQ', ← classStep_classVec]
    have := hsym x (classVec hB hR Q')
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hall m, inner_zero_left]
  have hall' : ∀ y : ClassSpace hB hR, inner ℂ x y = 0 := fun y =>
    UniformSpace.Completion.induction_on y
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (inner_pre_eq_zero_class hB hR x horth)
  exact inner_self_eq_zero.mp (hall' x)

#print axioms classStep_zero_injective

/-! ### The time translations and the Hamiltonian -/

/-- **The time translation by `t`**: `(classStep 0) ^ (t / a_0)`. -/
def classTime (t : ℝ) : ClassSpace hB hR →L[ℂ] ClassSpace hB hR :=
  powSemigroup (classStep hB hR 0) (dySpacing N 0) t

/-- **The Hamiltonian of the class reconstruction**: the generator of `classTime`. -/
def classHamiltonian : ClassSpace hB hR →ₗ.[ℂ] ClassSpace hB hR :=
  generator (classTime hB hR)

theorem classTime_dyadic (m n : ℕ) :
    classTime hB hR (n * dySpacing N m) = classStep hB hR m ^ n := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  unfold classTime powSemigroup
  rw [dySpacing_eq_mul N m, classStep_eq_powT hB hR m,
    ← powT_nat_mul (isSelfAdjoint_classStep hB hR 0) (spectrum_classStep hB hR 0)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m) n]
  congr 1
  field_simp

theorem classTime_zero : classTime hB hR 0 = 1 := by
  unfold classTime powSemigroup
  rw [zero_div, powT_zero (isSelfAdjoint_classStep hB hR 0)]

theorem classTime_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    classTime hB hR (s + t) = classTime hB hR s * classTime hB hR t := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  unfold classTime powSemigroup
  rw [add_div, powT_add (spectrum_classStep hB hR 0) (div_nonneg hs ha0.le)
    (div_nonneg ht ha0.le)]

theorem classTime_nonneg_norm (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ classTime hB hR t ∧ IsSelfAdjoint (classTime hB hR t) ∧ ‖classTime hB hR t‖ ≤ 1 :=
  ⟨powT_nonneg (spectrum_classStep hB hR 0) _, isSelfAdjoint_powT _,
    norm_powT_le_one (spectrum_classStep hB hR 0)
      (div_nonneg ht (dySpacing_pos (one_le_of_ne_zero hN) 0).le)⟩

/-- **Strong continuity on `[0, ∞)`.** -/
theorem continuousOn_classTime (y : ClassSpace hB hR) :
    ContinuousOn (fun t => classTime hB hR t y) (Set.Ici 0) := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hc := continuousOn_powT_apply (isSelfAdjoint_classStep hB hR 0)
    (spectrum_classStep hB hR 0) (classStep_zero_injective hB hR) y
  have hd : ContinuousOn (fun t : ℝ => t / dySpacing N 0) (Set.Ici 0) :=
    (continuous_id.div_const _).continuousOn
  exact hc.comp hd (fun t ht => div_nonneg ht ha0.le)

#print axioms continuousOn_classTime

theorem classTime_vac {t : ℝ} (ht : 0 ≤ t) :
    classTime hB hR t (classVac hB hR) = classVac hB hR := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  refine powT_apply_fixed (isSelfAdjoint_classStep hB hR 0)
    (spectrum_classStep hB hR 0) (fun m n => ?_) (div_nonneg ht ha0.le)
  rw [powT_nat_mul (isSelfAdjoint_classStep hB hR 0) (spectrum_classStep hB hR 0)
    (by positivity) n, ← classStep_eq_powT]
  induction n with
  | zero => rw [pow_zero, ContinuousLinearMap.one_apply]
  | succ n ih => rw [pow_succ, ContinuousLinearMap.mul_apply, classStep_vac, ih]

/-- **The dyadic gaps give the gap at every time.** -/
theorem classTime_gap {μ : ℝ} (hμ : 0 ≤ μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (contTransferClassAlong hB hR m)
      (Real.exp (-μ * dySpacing N m))) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u : ClassSpace hB hR, inner ℂ (classVac hB hR) u = 0 →
        ‖classTime hB hR t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
      ∧ spectrum ℝ (classTime hB hR t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))) := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hsa := isSelfAdjoint_classStep hB hR 0
  have hsp := spectrum_classStep hB hR 0
  have htime : μ * dySpacing N 0 * (t / dySpacing N 0) = μ * t := by field_simp
  refine ⟨fun u hu => ?_, ?_⟩
  · have hd : ∀ m n : ℕ, ‖powT (classStep hB hR 0) (n * (1 / 2 : ℝ) ^ m) u‖
        ≤ Real.exp (-(μ * dySpacing N 0 * (n * (1 / 2 : ℝ) ^ m))) * ‖u‖ := by
      intro m n
      rw [powT_nat_mul hsa hsp (by positivity) n, ← classStep_eq_powT]
      have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (isSelfAdjoint_classStep hB hR m)
      have hstep : ∀ v : ClassSpace hB hR, inner ℂ (classVac hB hR) v = 0 →
          ‖classStep hB hR m v‖ ≤ Real.exp (-μ * dySpacing N m) * ‖v‖ :=
        fun v hv => (hgap m).2.2.2.1 v hv
      have hinv : ∀ v : ClassSpace hB hR, inner ℂ (classVac hB hR) v = 0 →
          inner ℂ (classVac hB hR) (classStep hB hR m v) = 0 := by
        intro v hv
        have := hsym (classVac hB hR) v
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [← this, classStep_vac, hv]
      have hpow : ∀ k : ℕ, inner ℂ (classVac hB hR) ((classStep hB hR m ^ k) u) = 0
          ∧ ‖(classStep hB hR m ^ k) u‖ ≤ Real.exp (-μ * dySpacing N m) ^ k * ‖u‖ := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero, ContinuousLinearMap.one_apply, pow_zero, one_mul]
          exact ⟨hu, le_rfl⟩
        | succ k ih =>
          rw [pow_succ', ContinuousLinearMap.mul_apply]
          refine ⟨hinv _ ih.1, (hstep _ ih.1).trans ?_⟩
          rw [pow_succ', mul_assoc]
          exact mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
      refine (hpow n).2.trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul, dySpacing_eq_mul N m]
      congr 2
      ring
    have h := norm_powT_apply_le hsa hsp (mul_nonneg hμ ha0.le) hd (div_nonneg ht ha0.le)
    rw [htime] at h
    exact h
  · have hgap0 : spectrum ℝ (classStep hB hR 0)
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-μ * dySpacing N 0)) := (hgap 0).2.2.2.2.1
    have h := spectrum_powT_subset hsa hsp hgap0 (div_nonneg ht ha0.le)
    rw [← Real.exp_mul] at h
    have e : -μ * dySpacing N 0 * (t / dySpacing N 0) = -(μ * t) := by field_simp
    rw [e] at h
    exact h

#print axioms classTime_gap

/-- **The Hamiltonian on the class reconstruction at gap `μ`.** On the one reconstructed space:

* the time translations `classTime t = e^{−tH}`, `t ≥ 0`: `classTime 0 = 1`, the semigroup law,
  agreement with the dyadic steps, positive self-adjoint contractions, strong continuity on
  `[0, ∞)`;
* `H = classHamiltonian` is their generator: its domain is the set where `t⁻¹ (u − e^{−tH} u)`
  converges as `t → 0⁺`, and `H u` is the limit;
* `H` is self-adjoint and positive, and `H Ω = 0`;
* the gap: `μ ‖u‖² ≤ re ⟪u, H u⟫` on the vacuum complement in the domain, `‖e^{−tH} u‖ ≤ e^{−μ t} ‖u‖`
  on the vacuum complement, `spectrum (e^{−tH}) ⊆ {1} ∪ [0, e^{−μ t}]`;
* the vacuum is the only ground state: `H u = 0` and `e^{−tH} u = u` (`t > 0`) each put `u` on the
  vacuum line. -/
def HamiltonianAt (μ : ℝ) : Prop :=
  classTime hB hR 0 = 1
    ∧ (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        classTime hB hR (s + t) = classTime hB hR s * classTime hB hR t)
    ∧ (∀ m n : ℕ, classTime hB hR (n * dySpacing N m) = classStep hB hR m ^ n)
    ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ classTime hB hR t ∧ IsSelfAdjoint (classTime hB hR t)
        ∧ ‖classTime hB hR t‖ ≤ 1)
    ∧ (∀ y : ClassSpace hB hR, ContinuousOn (fun t => classTime hB hR t y) (Set.Ici 0))
    ∧ (∀ u : ClassSpace hB hR, u ∈ (classHamiltonian hB hR).domain
        ↔ ∃ v, Tendsto (diffQuot (classTime hB hR) u) (𝓝[>] 0) (𝓝 v))
    ∧ (∀ u : (classHamiltonian hB hR).domain,
        Tendsto (diffQuot (classTime hB hR) u) (𝓝[>] 0) (𝓝 (classHamiltonian hB hR u)))
    ∧ IsSelfAdjoint (classHamiltonian hB hR)
    ∧ (∀ u : (classHamiltonian hB hR).domain,
        0 ≤ (inner ℂ (u : ClassSpace hB hR) (classHamiltonian hB hR u)).re)
    ∧ (∃ h : classVac hB hR ∈ (classHamiltonian hB hR).domain,
        classHamiltonian hB hR ⟨classVac hB hR, h⟩ = 0)
    ∧ (∀ u : (classHamiltonian hB hR).domain, inner ℂ (classVac hB hR) (u : ClassSpace hB hR) = 0 →
        μ * ‖(u : ClassSpace hB hR)‖ ^ 2
          ≤ (inner ℂ (u : ClassSpace hB hR) (classHamiltonian hB hR u)).re)
    ∧ (∀ t : ℝ, 0 ≤ t → classTime hB hR t (classVac hB hR) = classVac hB hR)
    ∧ (∀ t : ℝ, 0 ≤ t → ∀ u : ClassSpace hB hR, inner ℂ (classVac hB hR) u = 0 →
        ‖classTime hB hR t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
    ∧ (∀ t : ℝ, 0 ≤ t →
        spectrum ℝ (classTime hB hR t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))))
    ∧ (∀ u : (classHamiltonian hB hR).domain, classHamiltonian hB hR u = 0 →
        ∃ c : ℂ, (u : ClassSpace hB hR) = c • classVac hB hR)
    ∧ (∀ t : ℝ, 0 < t → ∀ u : ClassSpace hB hR, classTime hB hR t u = u →
        ∃ c : ℂ, u = c • classVac hB hR)

/-- **A vector fixed at one positive time is on the vacuum line**, under the decay on the vacuum
complement at rate `μ > 0`. -/
theorem fixed_eq_smul_classVac {μ : ℝ} (hμ : 0 < μ)
    (hdec : ∀ t : ℝ, 0 ≤ t → ∀ u : ClassSpace hB hR, inner ℂ (classVac hB hR) u = 0 →
      ‖classTime hB hR t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
    {t : ℝ} (ht : 0 < t) (u : ClassSpace hB hR) (hu : classTime hB hR t u = u) :
    ∃ c : ℂ, u = c • classVac hB hR := by
  set c : ℂ := inner ℂ (classVac hB hR) u
  set w : ClassSpace hB hR := u - c • classVac hB hR with hw
  have hΩΩ : inner ℂ (classVac hB hR) (classVac hB hR) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, norm_classVac]
    norm_num
  have hwo : inner ℂ (classVac hB hR) w = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hΩΩ, mul_one, sub_self]
  have hfix : classTime hB hR t w = w := by
    rw [hw, map_sub, map_smul, hu, classTime_vac hB hR ht.le]
  have h := hdec t ht.le w hwo
  rw [hfix] at h
  have hlt : Real.exp (-(μ * t)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := mul_pos hμ ht
    linarith
  have hn : ‖w‖ = 0 := by
    have h0 := norm_nonneg w
    nlinarith
  refine ⟨c, ?_⟩
  have h0 : w = 0 := norm_eq_zero.mp hn
  rw [hw, sub_eq_zero] at h0
  exact h0

#print axioms fixed_eq_smul_classVac

/-- **The dyadic gaps at rate `μ > 0` give the Hamiltonian with gap `μ`.** -/
theorem hamiltonianAt_of_gapped {μ : ℝ} (hμ : 0 < μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (contTransferClassAlong hB hR m)
      (Real.exp (-μ * dySpacing N m))) : HamiltonianAt hB hR μ := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hsa := isSelfAdjoint_classStep hB hR 0
  have hsp := spectrum_classStep hB hR 0
  have hker := classStep_zero_injective hB hR
  have hdec : ∀ t : ℝ, 0 ≤ t → ∀ u : ClassSpace hB hR, inner ℂ (classVac hB hR) u = 0 →
      ‖classTime hB hR t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖ :=
    fun t ht => (classTime_gap hB hR hμ.le hgap ht).1
  have hsym : ∀ t : ℝ, 0 < t → IsSelfAdjoint (classTime hB hR t) :=
    fun t ht => (classTime_nonneg_norm hB hR t ht.le).2.1
  have hc : ∀ t : ℝ, 0 < t → ‖classTime hB hR t‖ ≤ 1 :=
    fun t ht => (classTime_nonneg_norm hB hR t ht.le).2.2
  have hvac : ∀ t : ℝ, 0 < t → classTime hB hR t (classVac hB hR) = classVac hB hR :=
    fun t ht => classTime_vac hB hR ht.le
  have hgapH : ∀ u : (classHamiltonian hB hR).domain,
      inner ℂ (classVac hB hR) (u : ClassSpace hB hR) = 0 →
      μ * ‖(u : ClassSpace hB hR)‖ ^ 2
        ≤ (inner ℂ (u : ClassSpace hB hR) (classHamiltonian hB hR u)).re :=
    generator_gap (classTime hB hR) hμ.le (fun t ht => hdec t ht.le)
  exact ⟨classTime_zero hB hR, fun _ _ hs ht => classTime_add hB hR hs ht,
    classTime_dyadic hB hR, classTime_nonneg_norm hB hR, continuousOn_classTime hB hR,
    mem_generator_domain_iff (classTime hB hR), tendsto_generator (classTime hB hR),
    powSemigroup_generator_isSelfAdjoint hsa hsp hker ha0,
    re_inner_generator_nonneg (classTime hB hR) hc,
    generator_vac (classTime hB hR) hvac, hgapH,
    fun _ ht => classTime_vac hB hR ht, hdec,
    fun _ ht => (classTime_gap hB hR hμ.le hgap ht).2,
    generator_ker (classTime hB hR) hμ (norm_classVac hB hR) hvac hgapH,
    fun _ ht u hu => fixed_eq_smul_classVac hB hR hμ hdec ht u hu⟩

#print axioms hamiltonianAt_of_gapped

end ClassSpace

/-! ## 4. The capstone -/

section Capstone

variable {N : ℕ}

/-- **The class conclusion gives the Hamiltonian at its rate.** `ClayContinuumPairClassAlong` at
window `L > 0` names `c > 0` with every dyadic step gapped at `e^{−(c/L) a_m}`; at that `c`, the
class reconstruction carries `HamiltonianAt (c / L)`. -/
theorem hamiltonian_of_clayClass (hN : N ≠ 0) {βs : ℕ → ℝ} {Z : ℕ → LField (MassGap.SUN.SU N) → ℝ}
    {τ : Fin 4} {hZ : ∀ k O, Z k (O.refl τ) = Z k O} {𝒯 : TestClass}
    {hB : PairBoundClassAlong hN βs (Renorm.connectedAlong hN βs Z) τ 𝒯} {L : ℝ} (hL : 0 < L)
    (h : ClayContinuumPairClassAlong hN βs Z τ hZ 𝒯 hB L) :
    ∃ c : ℝ, 0 < c
      ∧ (∀ m : ℕ,
          ContinuumClay.GappedAt
              (contTransferClassAlong hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m)
              (Real.exp (-(c / L) * dySpacing N m))
            ∧ ContinuumClay.NontrivialVacuum
              (contTransferClassAlong hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) m))
      ∧ HamiltonianAt hB (Renorm.connectedAlong_reflCompat hN βs Z τ hZ) (c / L) := by
  obtain ⟨c, hc, hm⟩ := h
  exact ⟨c, hc, hm, hamiltonianAt_of_gapped hB _ (div_pos hc hL) (fun m => (hm m).1)⟩

#print axioms hamiltonian_of_clayClass

end Capstone

end MassGap.ClassHamiltonian
