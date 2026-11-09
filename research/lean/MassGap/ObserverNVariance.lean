import Mathlib
import MassGap.ObserverClay

noncomputable section

/-!
# MassGap.ObserverNVariance — what non-triviality asks of a bounded observer

`ContinuumFlow.FlowConnectedNonzero hN Φ τ r` asks for one margin monomial `Q` whose connected
reflected pairing `kernF Q Q − (kernF ∅ Q)²` is non-zero. For a bounded flow (`Flow.Bounded`, the
setting of `ObserverClay.observer_clay`) the pairing is the limit along `ultra` of the lattice
connected pairings `ν_k(θX_k · X_k) − ν_k(X_k)²`, `X_k` the product of the smeared flowed fields of
`Q`. This file bounds that lattice pairing by the variances of the flowed fields at one site.

## The bound

* `cov_le`: in any state, `|ν(AB) − ν(A)ν(B)|` is at most the sum of the mean-square deviations of
  `A` and `B` from any one constant.
* `prod_sub_prod_sq_le`: a product of `n` reals bounded by `B` moves by at most
  `(2(B² + 1))ⁿ` times the sum of the squared moves of its factors.
* `var_smear_le`: in a translation-invariant state the smeared field has variance at most
  `(M (2R + 3)⁴)²` times the variance of the field at one site, at every spacing `0 < a ≤ 1`. The
  smearing weights `a⁴ f(a x)` sum to at most `M (2R + 3)⁴` in absolute value, so averaging over
  `a⁻⁴` cells never raises the variance above the single-site variance times that constant.
* `abs_conn_le`: hence the lattice connected pairing of `Q` at step `k` is at most
  `2 (2(B² + 1))ⁿ ∑ᵢ mᵢ² Var_{ν_k}(Φ_k Oᵢ)`, with constants independent of `k`.

## The results

* `conn_tendsto_zero`, `not_flowConnectedNonzero_of_var`: if every flowed local field's single-site
  variance tends to `0` along `ultra`, every connected reflected pairing of the limit vanishes and
  `FlowConnectedNonzero` fails.
* `exists_var_not_tendsto_of_flowConnectedNonzero`: so `FlowConnectedNonzero` for a bounded flow needs
  one local field whose flowed single-site variance does not tend to `0` along `ultra`.
* `flowConnectedNonzero_iff`, `flowConnectedNonzero_of_eventually_ge`: under the uniform bound,
  `FlowConnectedNonzero` is the statement that some margin monomial's lattice connected pairing does
  not tend to `0` along `ultra`; a lower bound `ε > 0` holding eventually along `ultra` gives it.
* `observer_N_needs_variance`: for the smeared `SU(2)` observer `ObserverClay.obsFlowF`,
  `FlowConnectedNonzero` needs a local gauge-invariant `O` with `Var_{ν_k}(O ∘ V_k)` not tending to `0`,
  `V_k` the localised APE smearing of step `k` and `ν_k` the periodic Wilson state at the coupling
  `dyBeta k`, which tends to infinity (`ContinuumSchwinger.tendsto_dyBeta`).

## What the necessary condition says about the smeared observer

`O ∘ V_k` reads the smeared configuration on loops of lattice size: `O` is a fixed local field. A
smearing of physical radius makes the configuration smooth on that radius, so its lattice-size loops
approach the identity as the spacing shrinks, and their single-site variance is expected to vanish.
At a bounded number of smearing steps in a bounded box the field reads a fixed finite set of fine links,
whose plaquettes concentrate at the identity as `β → ∞`. In both regimes the necessary condition is
expected to fail, so `FlowConnectedNonzero` for `obsFlowF` is expected false. Non-triviality needs a
field of scaling dimension zero at the observer's resolution: a loop of physical size (the block
view), or the flowed field at the canonical factor `a⁻⁴` (`ContinuumFlow.canonZ`), which is not
bounded, so its uniform bound `ContinuumFlow.UniformBoundF` becomes an input.
-/

namespace MassGap.ObserverNVariance

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow Filter
open scoped Topology

/-! ## 1. Variances in a state -/

section StateVar

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **The variance of `F` in the state `ν`**: `ν((F − ν F)²)`.

DERIVED: `1` is the unit observable the mean multiplies. -/
def var (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) : ℝ :=
  ν ((F - ν F • (1 : C(X, ℝ))) * (F - ν F • (1 : C(X, ℝ))))

/-- The mean-square deviation from a constant, expanded.

DERIVED: `1` is the unit observable; `2` the cross term and the square. -/
theorem msd_eq (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) (c : ℝ) :
    ν ((F - c • (1 : C(X, ℝ))) * (F - c • (1 : C(X, ℝ))))
      = ν (F * F) - 2 * c * ν F + c ^ 2 := by
  have h : (F - c • (1 : C(X, ℝ))) * (F - c • (1 : C(X, ℝ)))
      = F * F - (2 * c) • F + (c ^ 2) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [h, ν.map_add, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_one]
  ring

#print axioms msd_eq

/-- DERIVED: `2` is the square. -/
theorem var_eq (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) :
    var ν F = ν (F * F) - ν F ^ 2 := by
  unfold var
  rw [msd_eq]
  ring

#print axioms var_eq

/-- A mean-square deviation from a constant is non-negative.

DERIVED: `0` is the lower bound; `1` the unit observable. -/
theorem msd_nonneg (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) (c : ℝ) :
    0 ≤ ν ((F - c • (1 : C(X, ℝ))) * (F - c • (1 : C(X, ℝ)))) :=
  ν.nonneg _ (fun x => by
    simp only [ContinuousMap.mul_apply]
    exact mul_self_nonneg _)

#print axioms msd_nonneg

/-- DERIVED: `0` is the lower bound. -/
theorem var_nonneg (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) : 0 ≤ var ν F :=
  msd_nonneg ν F (ν F)

#print axioms var_nonneg

/-- `(ν F)² ≤ ν(F²)`.

DERIVED: `2` is the square. -/
theorem sq_le (ν : MassGap.DLRLimit.State X) (F : C(X, ℝ)) : ν F ^ 2 ≤ ν (F * F) := by
  have h := var_nonneg ν F
  rw [var_eq] at h
  linarith

#print axioms sq_le

/-- `|ν(AB)| ≤ (ν(A²) + ν(B²))/2`.

DERIVED: `2` halves the sum, from `2|ab| ≤ a² + b²`; `1/2` is the same half. -/
theorem abs_mul_le (ν : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) :
    |ν (A * B)| ≤ (ν (A * A) + ν (B * B)) / 2 := by
  have hup : ν (A * B) ≤ ν ((1 / 2 : ℝ) • (A * A + B * B)) :=
    ν.mono (fun x => by
      simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
        smul_eq_mul]
      nlinarith [sq_nonneg (A x - B x)])
  have hlo : ν (-((1 / 2 : ℝ) • (A * A + B * B))) ≤ ν (A * B) :=
    ν.mono (fun x => by
      simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
        ContinuousMap.neg_apply, smul_eq_mul]
      nlinarith [sq_nonneg (A x + B x)])
  rw [ν.map_smul, ν.map_add] at hup
  rw [ν.map_neg, ν.map_smul, ν.map_add] at hlo
  rw [abs_le]
  constructor <;> linarith

#print axioms abs_mul_le

/-- `|ab| ≤ (a² + b²)/2`.

DERIVED: `2` is the square and the halving. -/
theorem abs_mul_le_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

#print axioms abs_mul_le_sq

/-- **The covariance against two mean-square deviations**: for any constant `c`,
`|ν(AB) − ν(A)ν(B)| ≤ ν((A − c)²) + ν((B − c)²)`. The covariance does not see the shift by `c`; the
shifted product is at most the half-sum of the two deviations, and so is the product of the shifted
means, since `(ν A')² ≤ ν(A'²)`.

DERIVED: `1` is the unit observable; `2` the square. -/
theorem cov_le (ν : MassGap.DLRLimit.State X) (A B : C(X, ℝ)) (c : ℝ) :
    |ν (A * B) - ν A * ν B|
      ≤ ν ((A - c • (1 : C(X, ℝ))) * (A - c • (1 : C(X, ℝ))))
        + ν ((B - c • (1 : C(X, ℝ))) * (B - c • (1 : C(X, ℝ)))) := by
  have hprod : (A - c • (1 : C(X, ℝ))) * (B - c • (1 : C(X, ℝ)))
      = A * B - c • A - c • B + (c ^ 2) • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have hA : ν (A - c • (1 : C(X, ℝ))) = ν A - c := by
    rw [ν.map_sub, ν.map_smul, ν.map_one, mul_one]
  have hB : ν (B - c • (1 : C(X, ℝ))) = ν B - c := by
    rw [ν.map_sub, ν.map_smul, ν.map_one, mul_one]
  have e1 : ν (A * B) - ν A * ν B
      = ν ((A - c • (1 : C(X, ℝ))) * (B - c • (1 : C(X, ℝ))))
        - ν (A - c • (1 : C(X, ℝ))) * ν (B - c • (1 : C(X, ℝ))) := by
    rw [hprod, hA, hB, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul,
      ν.map_one]
    ring
  have h1 := abs_mul_le ν (A - c • (1 : C(X, ℝ))) (B - c • (1 : C(X, ℝ)))
  have h2 := sq_le ν (A - c • (1 : C(X, ℝ)))
  have h3 := sq_le ν (B - c • (1 : C(X, ℝ)))
  have h4 := abs_mul_le_sq (ν (A - c • (1 : C(X, ℝ)))) (ν (B - c • (1 : C(X, ℝ))))
  rw [e1]
  calc _ ≤ |ν ((A - c • (1 : C(X, ℝ))) * (B - c • (1 : C(X, ℝ))))|
        + |ν (A - c • (1 : C(X, ℝ))) * ν (B - c • (1 : C(X, ℝ)))| := abs_sub _ _
    _ ≤ _ := by linarith

#print axioms cov_le

end StateVar

/-! ## 2. Products of bounded reals -/

/-- **A product moves by at most the sum of its factors' moves**: for reals bounded by `B`,
`(∏ yᵢ − ∏ cᵢ)² ≤ (2(B² + 1))ⁿ ∑ᵢ (yᵢ − cᵢ)²`. Induction on `n`: `y₀P − c₀p = (y₀ − c₀)P + c₀(P − p)`,
`(u + v)² ≤ 2u² + 2v²`, `P² ≤ B²ⁿ ≤ (B² + 1)ⁿ`, `c₀² ≤ B² + 1`.

DERIVED: `2` is the square and the factor of `(u + v)² ≤ 2u² + 2v²`; `1` makes `B² + 1 ≥ 1`; `0` is
the empty product's count. -/
theorem prod_sub_prod_sq_le : ∀ (n : ℕ) (y c : Fin n → ℝ) (B : ℝ), (∀ i, |y i| ≤ B) →
    (∀ i, |c i| ≤ B) →
    (∏ i, y i - ∏ i, c i) ^ 2 ≤ (2 * (B ^ 2 + 1)) ^ n * ∑ i, (y i - c i) ^ 2
  | 0, y, c, B, _, _ => by simp
  | n + 1, y, c, B, hy, hc => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have ih := prod_sub_prod_sq_le n (fun i => y i.succ) (fun i => c i.succ) B
      (fun i => hy i.succ) (fun i => hc i.succ)
    set P := ∏ i : Fin n, y i.succ with hP
    set p := ∏ i : Fin n, c i.succ with hp
    set S := ∑ i : Fin n, (y i.succ - c i.succ) ^ 2 with hS
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hy 0)
    have hPabs : |P| ≤ B ^ n := by
      rw [hP, Finset.abs_prod]
      calc ∏ i : Fin n, |y i.succ| ≤ ∏ _i : Fin n, B :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hy i.succ)
        _ = B ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hP2 : P ^ 2 ≤ (B ^ 2 + 1) ^ n := by
      have h1 : P ^ 2 ≤ (B ^ n) ^ 2 := by
        rw [← sq_abs P]
        exact pow_le_pow_left₀ (abs_nonneg _) hPabs 2
      have h2 : (B ^ n) ^ 2 = (B ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      have h3 : (B ^ 2) ^ n ≤ (B ^ 2 + 1) ^ n :=
        pow_le_pow_left₀ (sq_nonneg B) (by linarith) n
      linarith
    have hc0 : c 0 ^ 2 ≤ B ^ 2 + 1 := by
      have : c 0 ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs (c 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc 0) 2
      linarith
    have hK1 : (1 : ℝ) ≤ B ^ 2 + 1 := by nlinarith [sq_nonneg B]
    have hKn : (B ^ 2 + 1) ^ n ≤ (2 * (B ^ 2 + 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have hKpos : 0 ≤ (2 * (B ^ 2 + 1)) ^ n := by positivity
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hsplit : (y 0 * P - c 0 * p) ^ 2
        ≤ 2 * ((y 0 - c 0) ^ 2 * P ^ 2) + 2 * (c 0 ^ 2 * (P - p) ^ 2) := by
      have e : y 0 * P - c 0 * p = (y 0 - c 0) * P + c 0 * (P - p) := by ring
      rw [e]
      nlinarith [sq_nonneg ((y 0 - c 0) * P - c 0 * (P - p))]
    have t1 : (y 0 - c 0) ^ 2 * P ^ 2 ≤ (y 0 - c 0) ^ 2 * (2 * (B ^ 2 + 1)) ^ n :=
      mul_le_mul_of_nonneg_left (hP2.trans hKn) (sq_nonneg _)
    have t2 : c 0 ^ 2 * (P - p) ^ 2 ≤ (B ^ 2 + 1) * ((2 * (B ^ 2 + 1)) ^ n * S) :=
      mul_le_mul hc0 ih (sq_nonneg _) (by linarith)
    have hpow : (2 * (B ^ 2 + 1)) ^ (n + 1) = 2 * (B ^ 2 + 1) * (2 * (B ^ 2 + 1)) ^ n := by
      rw [pow_succ]; ring
    rw [hpow]
    have t3 : 2 * ((y 0 - c 0) ^ 2 * (2 * (B ^ 2 + 1)) ^ n)
        ≤ 2 * (B ^ 2 + 1) * (2 * (B ^ 2 + 1)) ^ n * (y 0 - c 0) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hK1 (mul_nonneg (sq_nonneg (y 0 - c 0)) hKpos)
      nlinarith
    nlinarith

#print axioms prod_sub_prod_sq_le

/-- **The deviation of a product of observables**: for observables bounded by `B` in sup norm,
`ν((∏ Yᵢ − ∏ ν(Yᵢ))²) ≤ (2(B² + 1))ⁿ ∑ᵢ Var(Yᵢ)`, pointwise from `prod_sub_prod_sq_le` (every value
`Yᵢ(U)` and every mean `ν(Yᵢ)` lies in `[-B, B]`).

DERIVED: `1` is the unit observable and makes the base at least `1`; `2` is the square and the factor
of `prod_sub_prod_sq_le`. -/
theorem msd_prod_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {n : ℕ} (Y : Fin n → C(X, ℝ)) (B : ℝ) (hB : ∀ i, ‖Y i‖ ≤ B) :
    ν ((∏ i, Y i - (∏ i, ν (Y i)) • (1 : C(X, ℝ))) * (∏ i, Y i - (∏ i, ν (Y i)) • (1 : C(X, ℝ))))
      ≤ (2 * (B ^ 2 + 1)) ^ n * ∑ i, var ν (Y i) := by
  have h : ν ((∏ i, Y i - (∏ i, ν (Y i)) • (1 : C(X, ℝ)))
        * (∏ i, Y i - (∏ i, ν (Y i)) • (1 : C(X, ℝ))))
      ≤ ν ((2 * (B ^ 2 + 1)) ^ n • ∑ i, (Y i - ν (Y i) • (1 : C(X, ℝ)))
        * (Y i - ν (Y i) • (1 : C(X, ℝ)))) :=
    ν.mono (fun U => by
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, ContinuousMap.sum_apply, ContinuousMap.prod_apply, smul_eq_mul,
        mul_one]
      have hy : ∀ i, |Y i U| ≤ B := fun i => by
        have := (Y i).norm_coe_le_norm U
        rw [Real.norm_eq_abs] at this
        exact this.trans (hB i)
      have := prod_sub_prod_sq_le n (fun i => Y i U) (fun i => ν (Y i)) B hy
        (fun i => (ν.abs_le_norm (Y i)).trans (hB i))
      simpa only [sq] using this)
  rw [ν.map_smul, ν.map_sum] at h
  exact h

#print axioms msd_prod_le

/-! ## 3. The variance of a smeared field -/

section Smear

variable {N : ℕ}

/-- **Smearing does not raise the variance beyond a constant**: in a translation-invariant state,
at every spacing `0 < a ≤ 1`, `Var(smear a F f) ≤ (M (2R + 3)⁴)² Var(F)` for `f` bounded by `M` with
support in `[-R, R]⁴`. The centred smeared field is `∑ₓ wₓ T_x(F − ν F)`, `wₓ = a⁴ f(a x)`;
pointwise `(∑ wₓ zₓ)² ≤ (∑ |wₓ|)(∑ |wₓ| zₓ²)`, each `ν(T_x(F − νF)²)` is `Var(F)`, and
`∑ |wₓ| ≤ M (2R + 3)⁴` (`ContinuumNontrivial.riemann_le`).

DERIVED: `0` is the sign of `a`; `1` bounds `a`; `2` is the square; `3` and `4` are
`ContinuumNontrivial.riemann_le`'s. -/
theorem var_smear_le (ν : MassGap.DLRLimit.State (Cfg N))
    (htr : ∀ (x : ISite) (F : C(Cfg N, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (F : C(Cfg N, ℝ)) (f : TestFn) {R M : ℝ} (hf : IsTest f.1 R M) :
    var ν (smear a F f) ≤ (M * (2 * R + 3) ^ 4) ^ 2 * var ν F := by
  classical
  set s := box ⌈R / a⌉₊ with hs
  set w : ISite → ℝ := fun x => a ^ 4 * f.1 (site a x) with hw
  set ψ : C(Cfg N, ℝ) := F - ν F • (1 : C(Cfg N, ℝ)) with hψ
  have hsm : smear a F f = ∑ x ∈ s, w x • transObs x F := smear_eq_sum ha F f hf (subset_refl _)
  have hmean : ν (smear a F f) = (∑ x ∈ s, w x) * ν F := by
    rw [hsm, ν.map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [ν.map_smul, htr]
  have hval : ∀ U : Cfg N, (smear a F f - ν (smear a F f) • (1 : C(Cfg N, ℝ))) U
      = ∑ x ∈ s, w x * ψ (transConf x U) := by
    intro U
    rw [hmean, hsm]
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      ContinuousMap.coe_sum, Finset.sum_apply, transObs_apply, smul_eq_mul, hψ]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  set W : ℝ := ∑ x ∈ s, |w x| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have hbound : var ν (smear a F f)
      ≤ ν (W • ∑ x ∈ s, |w x| • transObs x (ψ * ψ)) := by
    unfold var
    refine ν.mono (fun U => ?_)
    rw [ContinuousMap.mul_apply, hval U]
    simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      transObs_apply, ContinuousMap.mul_apply, smul_eq_mul]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun x => w x * ψ (transConf x U)) (f := fun x => |w x|)
      (g := fun x => |w x| * (ψ (transConf x U) * ψ (transConf x U)))
      (fun x _ => abs_nonneg _)
      (fun x _ => mul_nonneg (abs_nonneg _) (mul_self_nonneg _))
      (fun x _ => by
        have : w x ^ 2 = |w x| * |w x| := by rw [← sq, sq_abs]
        rw [mul_pow, this]
        nlinarith [mul_self_nonneg (ψ (transConf x U))])
    rw [← sq]
    exact hcs
  have hrhs : ν (W • ∑ x ∈ s, |w x| • transObs x (ψ * ψ)) = W ^ 2 * var ν F := by
    rw [ν.map_smul, ν.map_sum]
    have : ∀ x ∈ s, ν (|w x| • transObs x (ψ * ψ)) = |w x| * var ν F := by
      intro x _
      rw [ν.map_smul, htr]
      rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← hW]
    ring
  have hWle : W ≤ M * (2 * R + 3) ^ 4 := by
    have hg : IsTest (fun y => |f.1 y|) R M :=
      ⟨hf.1, fun y => by rw [abs_abs]; exact hf.2.1 y,
        fun y hy i => hf.2.2 y (fun h => hy (by simp [h])) i⟩
    have h := ContinuumNontrivial.riemann_le ha ha1 hg
    have e : W = ∑ x ∈ s, a ^ 4 * |f.1 (site a x)| := by
      rw [hW]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hw, abs_mul, abs_of_nonneg (pow_nonneg ha.le 4)]
    rw [e]
    exact h
  have hW2 : W ^ 2 ≤ (M * (2 * R + 3) ^ 4) ^ 2 := pow_le_pow_left₀ hW0 hWle 2
  calc var ν (smear a F f) ≤ W ^ 2 * var ν F := hbound.trans hrhs.le
    _ ≤ (M * (2 * R + 3) ^ 4) ^ 2 * var ν F :=
        mul_le_mul_of_nonneg_right hW2 (var_nonneg ν F)

#print axioms var_smear_le

end Smear

/-! ## 4. The connected pairing of a bounded flow -/

section Flow

variable {N : ℕ}

/-- **The lattice connected reflected pairing of `Q` at step `k`**:
`latSF(θQ ∪ Q) − latSF(θ∅ ∪ Q)²`. Its limit along `ultra` is the quantity of
`ContinuumFlow.FlowConnectedNonzero`.

DERIVED: `0` is the excluded colour count; `2` the square; `4` in `Fin 4` is the spacetime
dimension. -/
def latConn (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (Q : Mono N) (k : ℕ) : ℝ :=
  latSF hN Φ k (pairFam τ Q Q) - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 Q) ^ 2

/-- The product of the smeared flowed fields of `Q` at step `k`.

DERIVED: no numeral. -/
abbrev flowProd (Φ : Flow N) (Q : Mono N) (k : ℕ) : C(Cfg N, ℝ) :=
  prodSmear (dySpacing N k) (Φ.mono k Q)

/-- The reflected pair of `Q` with itself is `ν_k(θX · X)`.

DERIVED: `0` is the excluded colour count and the reflection constant; `4` in `Fin 4` is the
spacetime dimension. -/
theorem latSF_pair_self (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (Q : Mono N) (k : ℕ) :
    latSF hN Φ k (pairFam τ Q Q)
      = stateK hN k (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k) * flowProd Φ Q k) := by
  rw [latSF_pairFam, latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]

#print axioms latSF_pair_self

/-- The empty monomial against `Q` is `ν_k(X)`.

DERIVED: `0` is the excluded colour count, the reflection constant and the empty count; `1` the
empty product; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSF_pair_empty (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (Q : Mono N) (k : ℕ) :
    latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 Q) = stateK hN k (flowProd Φ Q k) := by
  rw [latSF_pairFam, latSk_eq, latS_pairFam _ (dySpacing_pos (one_le_of_ne_zero hN) k)]
  have h1 : prodSmear (dySpacing N k) (Φ.mono k (emptyMargin N τ r).1) = 1 := by
    show (∏ i : Fin 0, _) = 1
    exact Fintype.prod_empty _
  rw [h1]
  have h2 : LatticeReflection.ireflObs τ 0 (1 : C(Cfg N, ℝ)) = 1 := rfl
  rw [h2, one_mul]

#print axioms latSF_pair_empty


/-- **The lattice connected pairing against the single-site variances.** For a factor bound `Bc`
(every smeared flowed factor of `Q` bounded by `Bc` in sup norm) and weights `m i` (each smeared
factor's variance at most `m i²` times its field's single-site variance),
`|latConn k| ≤ 2 (2(Bc² + 1))ⁿ ∑ᵢ mᵢ² Var_{ν_k}(Φ_k Oᵢ)`. The covariance `ν(θX·X) − ν(θX)ν(X)` is at
most twice the mean-square deviation of `X` from `∏ ν(Yᵢ)` (`cov_le` with the reflection invariance of
the state), which `msd_prod_le` bounds by the factors' variances.

DERIVED: `0` is the excluded colour count and the reflection constant; `1` makes the base at least
`1`; `2` counts the two deviations and is the square; `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_latConn_le (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (Q : Mono N) (k : ℕ)
    (Bc : ℝ) (hBc : ∀ i, ‖smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2‖ ≤ Bc)
    (m : Fin Q.1 → ℝ)
    (hm : ∀ i, var (stateK hN k) (smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2)
      ≤ m i ^ 2 * var (stateK hN k) (Φ.map k (Q.2 i).1).1) :
    |latConn hN Φ τ r Q k|
      ≤ 2 * ((2 * (Bc ^ 2 + 1)) ^ Q.1
        * ∑ i, m i ^ 2 * var (stateK hN k) (Φ.map k (Q.2 i).1).1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = ∏ i, stateK hN k (smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2) := ⟨_, rfl⟩
  have hθX : stateK hN k (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k))
      = stateK hN k (flowProd Φ Q k) := ContinuumNontrivial.stateK_refl hN k τ _
  have hθmsd : stateK hN k ((LatticeReflection.ireflObs τ 0 (flowProd Φ Q k)
        - c • (1 : C(Cfg N, ℝ))) * (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k)
        - c • (1 : C(Cfg N, ℝ))))
      = stateK hN k ((flowProd Φ Q k - c • (1 : C(Cfg N, ℝ)))
        * (flowProd Φ Q k - c • (1 : C(Cfg N, ℝ)))) := by
    have e : (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k) - c • (1 : C(Cfg N, ℝ)))
        * (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k) - c • (1 : C(Cfg N, ℝ)))
        = LatticeReflection.ireflObs τ 0
            ((flowProd Φ Q k - c • (1 : C(Cfg N, ℝ)))
              * (flowProd Φ Q k - c • (1 : C(Cfg N, ℝ)))) := by
      ext U
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, LatticeReflection.ireflObs_apply, smul_eq_mul]
    rw [e]
    exact ContinuumNontrivial.stateK_refl hN k τ _
  have hcov := cov_le (stateK hN k) (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k))
    (flowProd Φ Q k) c
  rw [hθX, hθmsd] at hcov
  have hmsd : stateK hN k ((flowProd Φ Q k - c • (1 : C(Cfg N, ℝ)))
        * (flowProd Φ Q k - c • (1 : C(Cfg N, ℝ))))
      ≤ (2 * (Bc ^ 2 + 1)) ^ Q.1 * ∑ i, var (stateK hN k)
          (smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2) := by
    rw [hc]
    exact msd_prod_le (stateK hN k)
      (fun i => smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2) Bc hBc
  have hsum : ∑ i, var (stateK hN k) (smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2)
      ≤ ∑ i, m i ^ 2 * var (stateK hN k) (Φ.map k (Q.2 i).1).1 :=
    Finset.sum_le_sum (fun i _ => hm i)
  have hK : 0 ≤ (2 * (Bc ^ 2 + 1)) ^ Q.1 := by positivity
  have hconn : latConn hN Φ τ r Q k
      = stateK hN k (LatticeReflection.ireflObs τ 0 (flowProd Φ Q k) * flowProd Φ Q k)
        - stateK hN k (flowProd Φ Q k) * stateK hN k (flowProd Φ Q k) := by
    unfold latConn
    rw [latSF_pair_self, latSF_pair_empty]
    ring
  rw [hconn]
  have hKs := mul_le_mul_of_nonneg_left hsum hK
  linarith

#print axioms abs_latConn_le

/-- **The connected pairing vanishes when the single-site variances do.** For a bounded flow, if
every flowed local field's single-site variance `Var_{ν_k}(Φ_k O)` tends to `0` along `ultra`, then
every lattice connected pairing `latConn Q` tends to `0` along `ultra`. The constants of
`abs_latConn_le` are fixed by `Q` and the flow's bounds, once `aₖ ≤ 1`.

DERIVED: `0` is the limit and the excluded colour count; `1` bounds the spacing; `2`, `3`, `4` are
`ContinuumField.norm_smear_le`'s and `var_smear_le`'s; `4` in `Fin 4` is also the spacetime
dimension. -/
theorem conn_tendsto_zero (hN : N ≠ 0) (Φ : Flow N) (hΦ : Φ.Bounded) (τ : Fin 4) (r : ℝ)
    (hvar : ∀ O : LField (MassGap.SUN.SU N),
      Tendsto (fun k => var (stateK hN k) (Φ.map k O).1) (ultra : Filter ℕ) (𝓝 0))
    (Q : Mono N) : Tendsto (latConn hN Φ τ r Q) (ultra : Filter ℕ) (𝓝 0) := by
  have hΦ' : ∀ O : LField (MassGap.SUN.SU N), ∃ B : ℝ, ∀ k, ‖(Φ.map k O).1‖ ≤ B := hΦ
  choose B hB using hΦ'
  have hex : ∀ i, ∃ R M : ℝ, IsTest (Q.2 i).2.1 R M := fun i => (Q.2 i).2.2
  choose R M hRM using hex
  have hm0 : ∀ i, 0 ≤ M i * (2 * R i + 3) ^ 4 := fun i =>
    mul_nonneg (hRM i).M_nonneg (by have := (hRM i).1; positivity)
  obtain ⟨Bc, hBcdef⟩ : ∃ Bc : ℝ, Bc = ∑ j, |B (Q.2 j).1| * (M j * (2 * R j + 3) ^ 4) :=
    ⟨_, rfl⟩
  have hBc : ∀ k, dySpacing N k ≤ 1 →
      ∀ i, ‖smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2‖ ≤ Bc := by
    intro k hk i
    have h1 := norm_smear_le (dySpacing_pos (one_le_of_ne_zero hN) k) hk
      (Φ.map k (Q.2 i).1).1 (Q.2 i).2 (hRM i)
    have h2 : ‖(Φ.map k (Q.2 i).1).1‖ * (M i * (2 * R i + 3) ^ 4)
        ≤ |B (Q.2 i).1| * (M i * (2 * R i + 3) ^ 4) :=
      mul_le_mul_of_nonneg_right ((hB _ k).trans (le_abs_self _)) (hm0 i)
    have h3 : |B (Q.2 i).1| * (M i * (2 * R i + 3) ^ 4) ≤ Bc := by
      rw [hBcdef]
      exact Finset.single_le_sum (f := fun j => |B (Q.2 j).1| * (M j * (2 * R j + 3) ^ 4))
        (fun j _ => mul_nonneg (abs_nonneg _) (hm0 j)) (Finset.mem_univ i)
    exact h1.trans (h2.trans h3)
  have hvs : ∀ k, dySpacing N k ≤ 1 → ∀ i,
      var (stateK hN k) (smear (dySpacing N k) (Φ.map k (Q.2 i).1).1 (Q.2 i).2)
        ≤ (M i * (2 * R i + 3) ^ 4) ^ 2 * var (stateK hN k) (Φ.map k (Q.2 i).1).1 :=
    fun k hk i => var_smear_le (stateK hN k)
      (fun x F => ContinuumNontrivial.stateK_transObs hN k x F)
      (dySpacing_pos (one_le_of_ne_zero hN) k) hk _ _ (hRM i)
  have hsum : Tendsto (fun k => ∑ i, (M i * (2 * R i + 3) ^ 4) ^ 2
      * var (stateK hN k) (Φ.map k (Q.2 i).1).1) (ultra : Filter ℕ) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin Q.1))
      (fun i _ => (hvar (Q.2 i).1).const_mul ((M i * (2 * R i + 3) ^ 4) ^ 2))
    simpa only [mul_zero, Finset.sum_const_zero] using h
  have hg : Tendsto (fun k => 2 * ((2 * (Bc ^ 2 + 1)) ^ Q.1 * ∑ i, (M i * (2 * R i + 3) ^ 4) ^ 2
      * var (stateK hN k) (Φ.map k (Q.2 i).1).1)) (ultra : Filter ℕ) (𝓝 0) := by
    simpa only [mul_zero] using (hsum.const_mul ((2 * (Bc ^ 2 + 1)) ^ Q.1)).const_mul 2
  have h1 : ∀ᶠ k in atTop, dySpacing N k ≤ 1 :=
    (tendsto_dySpacing N).eventually (ge_mem_nhds one_pos)
  have hev : ∀ᶠ k in (ultra : Filter ℕ), ‖latConn hN Φ τ r Q k‖
      ≤ 2 * ((2 * (Bc ^ 2 + 1)) ^ Q.1 * ∑ i, (M i * (2 * R i + 3) ^ 4) ^ 2
        * var (stateK hN k) (Φ.map k (Q.2 i).1).1) := by
    filter_upwards [ultra_le h1] with k hk
    rw [Real.norm_eq_abs]
    exact abs_latConn_le hN Φ τ r Q k Bc (hBc k hk) _ (hvs k hk)
  exact squeeze_zero_norm' hev hg

#print axioms conn_tendsto_zero

/-- Under the uniform bound the lattice connected pairing tends along `ultra` to the connected
pairing of the limit, `kernF Q Q − (kernF ∅ Q)²`.

DERIVED: `0` is the excluded colour count; `2` the square; `4` in `Fin 4` is the spacetime
dimension. -/
theorem tendsto_latConn (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) (r : ℝ)
    (Q : Mono N) :
    Tendsto (latConn hN Φ τ r Q) (ultra : Filter ℕ)
      (𝓝 (kernF hN Φ τ Q Q - kernF hN Φ τ (emptyMargin N τ r).1 Q ^ 2)) :=
  (tendsto_contSF hN Φ hB (pairFam τ Q Q)).sub
    ((tendsto_contSF hN Φ hB (pairFam τ (emptyMargin N τ r).1 Q)).pow 2)

#print axioms tendsto_latConn

/-- **A bounded flow whose single-site variances vanish has a trivial view**: if every flowed local
field's single-site variance tends to `0` along `ultra`, `FlowConnectedNonzero` fails.

DERIVED: `0` is the limit and the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem not_flowConnectedNonzero_of_var (hN : N ≠ 0) (Φ : Flow N) (hΦ : Φ.Bounded) (τ : Fin 4)
    (r : ℝ) (hvar : ∀ O : LField (MassGap.SUN.SU N),
      Tendsto (fun k => var (stateK hN k) (Φ.map k O).1) (ultra : Filter ℕ) (𝓝 0)) :
    ¬ FlowConnectedNonzero hN Φ τ r := by
  rintro ⟨Q, hQ⟩
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact hQ (tendsto_nhds_unique
    (tendsto_latConn hN Φ (uniformBoundF_of_bounded hN Φ hΦ) τ r Q.1)
    (conn_tendsto_zero hN Φ hΦ τ r hvar Q.1))

#print axioms not_flowConnectedNonzero_of_var

/-- **What non-triviality asks of a bounded observer**: `FlowConnectedNonzero` gives a local field
whose flowed single-site variance does not tend to `0` along `ultra`.

DERIVED: `0` is the limit and the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem exists_var_not_tendsto_of_flowConnectedNonzero (hN : N ≠ 0) (Φ : Flow N)
    (hΦ : Φ.Bounded) (τ : Fin 4) (r : ℝ) (h : FlowConnectedNonzero hN Φ τ r) :
    ∃ O : LField (MassGap.SUN.SU N),
      ¬ Tendsto (fun k => var (stateK hN k) (Φ.map k O).1) (ultra : Filter ℕ) (𝓝 0) := by
  by_contra hc
  exact not_flowConnectedNonzero_of_var hN Φ hΦ τ r
    (fun O => by
      by_contra h'
      exact hc ⟨O, h'⟩) h

#print axioms exists_var_not_tendsto_of_flowConnectedNonzero

/-- **Non-triviality as a lattice statement**: under the uniform bound, `FlowConnectedNonzero` holds
iff some margin monomial's lattice connected pairing does not tend to `0` along `ultra`.

DERIVED: `0` is the limit and the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem flowConnectedNonzero_iff (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    (r : ℝ) :
    FlowConnectedNonzero hN Φ τ r
      ↔ ∃ Q : MarginMono N τ r, ¬ Tendsto (latConn hN Φ τ r Q.1) (ultra : Filter ℕ) (𝓝 0) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, fun h => hQ (tendsto_nhds_unique (tendsto_latConn hN Φ hB τ r Q.1) h)⟩
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun h0 => hQ ?_⟩
    have h := tendsto_latConn hN Φ hB τ r Q.1
    rw [h0] at h
    exact h

#print axioms flowConnectedNonzero_iff

/-- **A uniform lower bound gives non-triviality**: under the uniform bound, a margin monomial whose
lattice connected pairing is at least `ε > 0` in absolute value eventually along `ultra` gives
`FlowConnectedNonzero`.

DERIVED: `0` is the sign of `ε`, the limit and the excluded colour count; `4` in `Fin 4` is the
spacetime dimension. -/
theorem flowConnectedNonzero_of_eventually_ge (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) (r : ℝ) (Q : MarginMono N τ r) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᶠ k in (ultra : Filter ℕ), ε ≤ |latConn hN Φ τ r Q.1 k|) :
    FlowConnectedNonzero hN Φ τ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine (flowConnectedNonzero_iff hN Φ hB τ r).mpr ⟨Q, fun h0 => ?_⟩
  have h2 : Tendsto (fun k => |latConn hN Φ τ r Q.1 k|) (ultra : Filter ℕ) (𝓝 0) := by
    simpa using h0.abs
  obtain ⟨k, hk1, hk2⟩ := ((h2.eventually (gt_mem_nhds hε)).and h).exists
  linarith

#print axioms flowConnectedNonzero_of_eventually_ge

/-- The unscaled configuration flow's field is `O ∘ V k`.

DERIVED: `1` and `0` are the identity factor and subtraction. -/
theorem ofConf_map_val (W : ConfFlow N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) :
    ((Flow.ofConf W).map k O).1 = (W.fieldMap k O).1 := by
  show (1 : ℝ) • ((W.fieldMap k O).1 - (0 : ℝ) • (1 : C(Cfg N, ℝ))) = _
  simp

#print axioms ofConf_map_val

/-- **What non-triviality asks of a configuration flow**: for `Flow.ofConf W`, `FlowConnectedNonzero`
gives a local gauge-invariant `O` with `Var_{ν_k}(O ∘ V k)` not tending to `0` along `ultra`.

DERIVED: `0` is the limit and the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem confFlow_N_needs_variance (hN : N ≠ 0) (W : ConfFlow N) (τ : Fin 4) (r : ℝ)
    (h : FlowConnectedNonzero hN (Flow.ofConf W) τ r) :
    ∃ O : LField (MassGap.SUN.SU N),
      ¬ Tendsto (fun k => var (stateK hN k) (W.fieldMap k O).1) (ultra : Filter ℕ) (𝓝 0) := by
  obtain ⟨O, hO⟩ :=
    exists_var_not_tendsto_of_flowConnectedNonzero hN _ (Flow.ofConf_bounded W) τ r h
  refine ⟨O, fun h' => hO ?_⟩
  simp only [ofConf_map_val]
  exact h'

#print axioms confFlow_N_needs_variance

end Flow

/-! ## 5. The smeared `SU(2)` observer -/

/-- **What non-triviality asks of the smeared observer.** `FlowConnectedNonzero` for
`ObserverClay.obsFlowF` gives a local gauge-invariant `O` whose smeared field `O ∘ V_k` (`V_k` the
localised APE smearing of step `k`) has single-site variance in the periodic Wilson state at
`dyBeta k` not tending to `0` along `ultra`.

DERIVED: `2` is the rank; `0` is the limit and the lower end of `c`; `1/6` the dominance bound; `4`
in `Fin 4` is the spacetime dimension. -/
theorem observer_N_needs_variance {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (τ : Fin 4) {r : ℝ}
    (hNT : FlowConnectedNonzero ObserverClay.two_ne (ObserverClay.obsFlowF c hc0 hc n R) τ r) :
    ∃ O : LField (MassGap.SUN.SU 2),
      ¬ Tendsto (fun k => var (stateK ObserverClay.two_ne k)
        ((ObserverFlow.obsConfFlow c hc0 hc n R).fieldMap k O).1) (ultra : Filter ℕ) (𝓝 0) :=
  confFlow_N_needs_variance ObserverClay.two_ne _ τ r hNT

#print axioms observer_N_needs_variance

end MassGap.ObserverNVariance
