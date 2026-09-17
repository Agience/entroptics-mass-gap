import Mathlib
import MassGap.Moment
import MassGap.WilsonBridge
import MassGap.ReflectionPositivity

/-!
# MassGap.StrongCoupling — geometric clustering at small coupling

WHAT THIS IS FOR. `Complete.confinement_of_lag_decay` takes `p d ≤ C·rᵈ` with `r < 1` and returns
confinement at every large enough aperture; `Complete.ym_mass_gap_of_lag_decay` takes it to the gap.
Everything downstream of that hypothesis is proved. This file is about supplying it — and at SMALL
COUPLING it can be supplied, because that is the one regime where the coupled correction to the
product measure is controlled.

THE ARGUMENT, AND WHERE IT SPLITS. Write the Boltzmann weight as a product over plaquettes and expand
each factor as `1 + (e^{−βφ_p} − 1)`. At `β = 0` every correction vanishes and the measure is product
Haar, under which two plaquettes sharing no link are independent — so the CONNECTED correlation is
exactly zero. At `β > 0` a term survives the connected subtraction only if the chosen plaquettes
CONNECT `p₀` to `p_d`, and the shortest connecting chain has length at least `d`. Each plaquette in
the chain pays a factor `|e^{−βφ} − 1| ≤ e^{2|β|} − 1`, and the number of connected chains of length
`n` from a fixed plaquette is at most `Kⁿ` for a connectivity constant `K` of the lattice. Hence

    |ρ_conn(d)| ≤ ∑_{n ≥ d} Kⁿ (e^{2|β|} − 1)ⁿ = (1 − q)⁻¹ qᵈ,   q = K(e^{2|β|} − 1),

which is geometric as soon as `q < 1`, i.e. `β < ½log(1 + 1/K)`.

That argument has an ANALYTIC half and a COMBINATORIAL half, and they are very different in size:

* the analytic half — the per-plaquette weight, the geometric resummation, and the threshold on `β`
  at which the rate drops below one — is PROVED here, foundation-only;
* the combinatorial half splits again, and the two pieces are now in different states:
  * the VOLUME CANCELLATION — that every configuration failing to connect `p₀` to `p_d` contributes
    exactly nothing — is PROVED here, foundation-only, in `nonbridging_sum_eq_zero` and applied to
    the Wilson correlation itself in `wilsonCorrConn_eq_bridging_sum`;
  * the COUNT — that the surviving, connecting configurations number at most `Kⁿ` at size `n` and
    carry a chain of length at least `d` — is NOT proved here. `ChainBound` states the bound that
    count would give.

The volume cancellation is the reason a naive perturbative bound fails: term by term the correction
is `O(β · #plaquettes)`, which grows with the lattice, and only the connected (subtracted) quantity
has the volume factors cancel. That cancellation is an exchange between PAIRS of activated subsets
across a separator — proved below at every coupling and every lattice size — not an estimate, and
nothing in it is perturbative.

WHERE THIS SITS IN THE EXISTING PROGRAMME. Two milestones toward nontrivial clustering are already
in the tree and this is the piece between them and the gap:

* `HaarMoments` — the SU(2) integration engine: `∫U_ij = 0`, Schur orthogonality
  `∫U_ij Ū_kl = ½δδ`, and the two-point form `∫tr(UA)tr(U*B) = ½tr(AB)`, all by explicit-element
  invariance with no Peter–Weyl. This is what evaluates ONE link's integral in a chain.
* `InteractingTwoPoint` — `sysInt`'s two plaquettes SHARE a link, and integrating THAT LINK ALONE
  gives `½tr(C₀C₁)`, generically nonzero, while the product of the marginals is `0`. Read it for
  exactly what it says: it is a statement about `tr(hol)` after one link integral, not about
  `⟨φ_p φ_q⟩_c`. The full connected correlation of those two plaquettes at `β = 0` is ZERO — the
  remaining links integrate `tr(C₀C₁) = tr(U₀·U₁U₂⁻¹U₄U₅⁻¹U₆⁻¹)` to nothing by
  `HaarMoments.haar_su2_trace_mul_zero` (measured by Monte-Carlo at 2·10⁶ samples:
  `7.7·10⁻⁵ ± 1.1·10⁻³`). Sharing a link is what makes a nonzero connected correlation POSSIBLE at
  `β > 0`; it does not produce one at `β = 0`.

`WilsonAnalytic` then records what remains: "clustering — that the connected plaquette correlator has
a volume-independent reach — is now the single open input". Between a nonzero connected pair at
separation one and a bound that decays in separation lies the chain sum, and that is what `ChainBound`
names and what this file resums.

WHAT IT WOULD BUY. `ChainBound` discharged for the Wilson measure makes
`Complete.ym_mass_gap_of_lag_decay` UNCONDITIONAL for `β` below the threshold — the first result in
this development with no open hypothesis, and a genuine spectral statement rather than a definitional
one. It does not reach the continuum limit, where `β → ∞` and the expansion diverges.
-/

namespace MassGap.StrongCoupling

open Filter

/-! ### The analytic half -/

/-- **A chain bound gives geometric decay.** Summing `qⁿ` over chains of length at least `d` gives
`qᵈ/(1−q)`; nothing else is needed, and the aperture never enters.

DERIVED: `(1−q)⁻¹` is the geometric series' own value, not a chosen constant. -/
theorem decay_of_chain_bound {ρ : ℕ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hchain : ∀ d : ℕ, |ρ d| ≤ ∑' n : ℕ, q ^ (d + n)) :
    ∀ d : ℕ, |ρ d| ≤ (1 - q)⁻¹ * q ^ d := by
  intro d
  refine (hchain d).trans (le_of_eq ?_)
  have hsplit : (fun n : ℕ => q ^ (d + n)) = fun n : ℕ => q ^ d * q ^ n := by
    funext n; rw [pow_add]
  rw [hsplit, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  ring

#print axioms decay_of_chain_bound

/-- **The per-plaquette weight a strong-coupling expansion pays.** The Wilson density `φ_W` lies in
`[0,2]`, so the Boltzmann factor sits within `e^{2|β|} − 1` of one. This is the only place the
coupling enters the rate.

DERIVED: `2` is the range of the Wilson plaquette density `φ_W(g) = 1 − ½ Re tr g` on `SU(N)`
(`WilsonReal.plaqObs_le_two`), not a chosen bound. -/
theorem boltz_factor_bound {β φ : ℝ} (h0 : 0 ≤ φ) (h2 : φ ≤ 2) :
    |Real.exp (-(β * φ)) - 1| ≤ Real.exp (2 * |β|) - 1 := by
  have habs : |β * φ| ≤ 2 * |β| := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg β]
  obtain ⟨hlo', hup'⟩ := abs_le.mp habs
  have hup : Real.exp (-(β * φ)) ≤ Real.exp (2 * |β|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hlo : Real.exp (-(2 * |β|)) ≤ Real.exp (-(β * φ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp (2 * |β|) * Real.exp (-(2 * |β|)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (2 * |β|)
  have hposn := Real.exp_pos (-(2 * |β|))
  have hsum : 2 ≤ Real.exp (2 * |β|) + Real.exp (-(2 * |β|)) := by
    nlinarith [sq_nonneg (Real.exp (2 * |β|) - 1)]
  rw [abs_le]
  constructor <;> linarith

#print axioms boltz_factor_bound

/-- **The chain rate is below one at small coupling.** For a connectivity constant `K > 0` the rate
`q = K(e^{2β} − 1)` is strictly below one exactly when `β < ½ log(1 + 1/K)`.

This is the threshold `β_c` of the expansion, DERIVED from `K` rather than chosen: it is where the
per-plaquette weight times the number of chains stops contracting. It is also why the argument cannot
reach the continuum — `β → ∞` sends `q → ∞`. -/
theorem chain_rate_lt_one {K β : ℝ} (hK : 0 < K) (hβ0 : 0 ≤ β)
    (hβ : β < Real.log (1 + 1 / K) / 2) :
    K * (Real.exp (2 * β) - 1) < 1 := by
  have hbase : (0 : ℝ) < 1 + 1 / K := by positivity
  have hlt : Real.exp (2 * β) < 1 + 1 / K := by
    have h2 : 2 * β < Real.log (1 + 1 / K) := by linarith
    calc Real.exp (2 * β) < Real.exp (Real.log (1 + 1 / K)) := Real.exp_lt_exp.mpr h2
      _ = 1 + 1 / K := Real.exp_log hbase
  have hKne : K ≠ 0 := ne_of_gt hK
  have : K * (1 / K) = 1 := by field_simp
  nlinarith

#print axioms chain_rate_lt_one

/-- **The rate is nonnegative.** Recorded because `decay_of_chain_bound` needs it and it is not
automatic from the definition. -/
theorem chain_rate_nonneg {K β : ℝ} (hK : 0 ≤ K) (hβ0 : 0 ≤ β) :
    0 ≤ K * (Real.exp (2 * β) - 1) := by
  have : (1 : ℝ) ≤ Real.exp (2 * β) := Real.one_le_exp (by linarith)
  nlinarith

#print axioms chain_rate_nonneg

/-! ### From the correlation to the read's weights -/

/-- **A geometric bound on the correlation is a geometric bound on the normalised weights**, once the
total mass is bounded below. `Moment.Read.p` is `ρ/∑ρ`, so a lower bound `m ≤ ∑ρ` turns a bound on
`ρ` into one on `p` with constant divided by `m`.

The lower bound is a hypothesis and has to be: the constant `C` that
`Complete.confinement_of_lag_decay` consumes must not depend on the aperture, so `m` must hold at
every `N`. Reflection positivity gives `0 < ∑ρ` at each `N` separately, which is not the same thing —
this is exactly the sort of uniformity the aperture argument is sensitive to. -/
theorem read_decay_of_correlation_decay {N : ℕ} (R : Moment.Read N) {C q m : ℝ}
    (hm : 0 < m) (hmass : m ≤ ∑ d, R.ρ d) (hC : 0 ≤ C) (hq0 : 0 ≤ q)
    (hdecay : ∀ d : Fin (N + 1), R.ρ d ≤ C * q ^ (d : ℕ)) :
    ∀ d : Fin (N + 1), R.p d ≤ (C / m) * q ^ (d : ℕ) := by
  intro d
  have hsum : 0 < ∑ d', R.ρ d' := lt_of_lt_of_le hm hmass
  have hpd : R.p d = R.ρ d / ∑ d', R.ρ d' := rfl
  rw [hpd, div_le_iff₀ hsum]
  have hqd : 0 ≤ q ^ (d : ℕ) := pow_nonneg hq0 _
  have hstep : R.ρ d ≤ C * q ^ (d : ℕ) := hdecay d
  have hmul : (C / m) * q ^ (d : ℕ) * m = C * q ^ (d : ℕ) := by field_simp
  calc R.ρ d ≤ C * q ^ (d : ℕ) := hstep
    _ = (C / m) * q ^ (d : ℕ) * m := hmul.symm
    _ ≤ (C / m) * q ^ (d : ℕ) * (∑ d', R.ρ d') := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        exact mul_nonneg (div_nonneg hC hm.le) hqd

#print axioms read_decay_of_correlation_decay

/-! ### The TAYLOR route — a more tractable shape for the same obligation

The chain sum above is one way to reach geometric decay and it is the expensive one: proving
`ChainBound` means running a polymer expansion and showing the volume cancels. There is a second
route to the SAME conclusion which asks for something local instead.

`WilsonAnalytic` proves the Gibbs expectation is analytic in `β` at finite volume, by
differentiation under the integral against a constant dominating function (the action is bounded in
`[0,4]`). At `β = 0` the measure is product Haar and two plaquettes sharing no link are INDEPENDENT
(`WilsonReal.block_integral_factor`), so the connected correlation is exactly `0` there. The same
argument applies order by order: the `k`-th Taylor coefficient activates `k` plaquette corrections,
and `k < d` of them cannot link two plaquettes at separation `d` — every such configuration
factorises and cancels in the connected part.

So the obligation becomes **`ρ_conn(d)` vanishes to order `d` in `β`**, which is a statement about
finitely many derivatives at a single point rather than about a sum over all polymers. A function
vanishing to that order with Cauchy-bounded coefficients decays geometrically, at rate `β/R` with `R`
the radius of analyticity — which is the lemma below.

Both routes need the same fact (unlinked configurations factorise). They differ in what has to be
controlled: the chain route needs a bound on a sum over all connected chains at once, the Taylor
route needs a coefficient bound on a disc. Mathlib supplies Cauchy estimates; it supplies no polymer
combinatorics. -/

/-- **A series supported on orders `≥ d`, with Cauchy-bounded coefficients, decays geometrically.**

If `|a_k| ≤ M/Rᵏ` — the Cauchy estimate for a function analytic and bounded by `M` on a disc of
radius `R` — and the series carries no term below order `d`, then its sum at `x < R` is at most
`M(x/R)ᵈ/(1 − x/R)`.

This is the analytic half of the Taylor route, and it is where `d` becomes an exponent. The rate is
`x/R`: the coupling measured against the radius of analyticity, with no lattice and no volume in it.

DERIVED: `(1 − x/R)⁻¹` is the geometric series' own value; `x/R` is forced by the Cauchy estimate.
Nothing is chosen. -/
theorem decay_of_tail_series {a : ℕ → ℝ} {M R x : ℝ} (d : ℕ)
    (hM : 0 ≤ M) (hR : 0 < R) (hx0 : 0 ≤ x) (hxR : x < R)
    (hcoef : ∀ n : ℕ, |a (d + n)| ≤ M / R ^ (d + n)) :
    |∑' n : ℕ, a (d + n) * x ^ (d + n)| ≤ M * (x / R) ^ d / (1 - x / R) := by
  have hq0 : 0 ≤ x / R := div_nonneg hx0 hR.le
  have hq1 : x / R < 1 := (div_lt_one hR).mpr hxR
  -- each term is under the geometric one
  have hterm : ∀ n : ℕ, ‖a (d + n) * x ^ (d + n)‖ ≤ M * (x / R) ^ (d + n) := by
    intro n
    have hRpow : (0 : ℝ) < R ^ (d + n) := pow_pos hR _
    have hxpow : (0 : ℝ) ≤ x ^ (d + n) := pow_nonneg hx0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxpow]
    calc |a (d + n)| * x ^ (d + n) ≤ M / R ^ (d + n) * x ^ (d + n) :=
          mul_le_mul_of_nonneg_right (hcoef n) hxpow
      _ = M * (x / R) ^ (d + n) := by rw [div_pow]; ring
  -- the dominating series sums, and to the claimed value
  have hgeom : HasSum (fun n : ℕ => M * (x / R) ^ (d + n))
      (M * (x / R) ^ d * (1 - x / R)⁻¹) := by
    have hbase := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * (x / R) ^ d)
    refine hbase.congr_fun ?_
    intro n; rw [pow_add]; ring
  refine le_trans (tsum_of_norm_bounded hgeom hterm) (le_of_eq ?_)
  field_simp

#print axioms decay_of_tail_series

/-! ### The combinatorial obligation, stated

Everything above is proved. What follows names the one thing that is not, so it cannot be mistaken
for part of the argument. -/

/-- **THE OBLIGATION.** `ChainBound bd ρconn K` says: the connected correlation at separation `d` is
dominated by the sum over connected plaquette chains of length at least `d`, each chain weighted by
its per-plaquette Boltzmann corrections, with at most `Kⁿ` chains of length `n`.

This is the cluster expansion's conclusion. Half of it is proved below and half is not, and the line
between them is sharp:

* the volume DOES cancel — `nonbridging_sum_eq_zero`, and on the Wilson correlation itself
  `wilsonCorrConn_eq_bridging_sum`: every pair of activated subsets that fails to carry a touching
  chain from `p₀` to `p_d` contributes exactly zero, at every coupling and every lattice size;
* what is NOT proved is the COUNT of the pairs that survive. Discharging `ChainBound` from
  `wilsonCorrConn_eq_bridging_sum` requires exactly: a bound of the form `Kⁿ` on the number of pairs
  `(E, F)` whose union touch-connects `p₀` to `p_d` with `|E| + |F| = n`, the fact that such a union
  must contain a touching chain of at least `d` plaquettes when `p₀` and `p_d` are at separation `d`,
  and the per-pair weight `(e^{2|β|}−1)ⁿ` (`subset_weight_bound`) divided by `Z²`. None of those
  three is supplied here.

`ρconn` is an ABSTRACT sequence: nothing in this definition ties it to `WilsonBridge.wilsonCorrConn`
or to `Complete.readYMAt`. Discharging the obligation means proving this predicate OF a specific
correlation, and that instantiation does not exist in the tree.

For the four-dimensional periodic lattice the constant `K` is a property of the geometry alone —
how many plaquettes meet a given one — so it carries no coupling and no volume.

DERIVED: `2` is the exponent of `boltz_factor_bound`'s `e^{2|β|} − 1`, which is the per-plaquette
Boltzmann factor over `φ ∈ [0,2]` — the range of the plaquette action, not a chosen scale. `1` is
subtracted because the connected correction is what remains after the product measure, and it is the
same `1` as in `chain_rate_lt_one`. `K` is supplied by the caller and never given a value here. -/
def ChainBound (ρconn : ℕ → ℝ) (K β : ℝ) : Prop :=
  ∀ d : ℕ, |ρconn d| ≤ ∑' n : ℕ, (K * (Real.exp (2 * β) - 1)) ^ (d + n)

/-- **The obligation discharged gives geometric clustering** — the analytic half applied to it. The
rate is `K(e^{2β} − 1)`, below one for `β < ½log(1 + 1/K)` (`chain_rate_lt_one`), and the constant is
the geometric series'. Nothing else is required.

WHAT IT IS NOT. It is NOT the hypothesis `Complete.confinement_of_lag_decay` consumes, and three
things stand between them. That hypothesis is `∀ N β d, (readYMAt N β).p d ≤ C·rᵈ`, where
`Moment.Read.p` is `ρ / ∑ρ` and `readYMAt`'s `ρ` is `WilsonBridge.corrClay`. So reaching it needs
(i) the normalisation — `read_decay_of_correlation_decay`, which carries a lower bound `0 < m ≤ ∑ρ`
as a hypothesis because reflection positivity gives positivity at each `N` separately and not
uniformly; (ii) uniformity in `N` AND in `β`, which a fixed-`β` bound does not give; and (iii) an
instantiation of `ρconn` at the Wilson correlation, which this file does not perform. -/
theorem clustering_of_chainBound {ρconn : ℕ → ℝ} {K β : ℝ}
    (hK : 0 < K) (hβ0 : 0 ≤ β) (hβ : β < Real.log (1 + 1 / K) / 2)
    (h : ChainBound ρconn K β) :
    ∀ d : ℕ, |ρconn d| ≤ (1 - K * (Real.exp (2 * β) - 1))⁻¹ * (K * (Real.exp (2 * β) - 1)) ^ d :=
  decay_of_chain_bound (chain_rate_nonneg hK.le hβ0) (chain_rate_lt_one hK hβ0 hβ) h

#print axioms clustering_of_chainBound

/-! ### Discharging the obligation at order zero

The `k = 0` coefficient of the Taylor route: at `β = 0` the Gibbs measure IS product Haar, so two
plaquettes drawing on disjoint link sets are independent and the CONNECTED correlation is exactly
zero. Proved below for an arbitrary geometry, with the disjointness carried as the hypothesis it is.

WHY THIS IS NOT THE FREE-FIELD TRAP. `WilsonBridge` warns that a flagship whose non-vacuity comes
from a free case is worthless, and it is right. This is a different use: `β = 0` here is the FIRST of
`d` vanishing Taylor coefficients in a bound at `β > 0`, not a claim about the theory at `β = 0`. The
base case of an induction is not a result about the base case. -/

section ZeroCoupling

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

open scoped Classical in
/-- Extend a tuple on `S` to a full link configuration, with the identity outside `S`. The value
outside is immaterial: every use is guarded by a support hypothesis.

DERIVED: `1` is the group identity of `SU(Nc)`, the only canonical element available to fill links
outside `S`. It is not a magnitude, and nothing depends on it — `wilsonCorrConn_eq_zero_of_split`
and its callers each carry the support hypothesis that makes the choice immaterial. -/
noncomputable def extendOn (S : Finset Lk) (v : S → MassGap.SUN.SU Nc) : Lk → MassGap.SUN.SU Nc :=
  fun i => if h : i ∈ S then v ⟨i, h⟩ else 1

/-- The plaquette observable read as a function of `S`'s links alone. -/
noncomputable def plaqOn (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  wilsonPlaqObs (N := Nc) bd p (extendOn (Lk := Lk) (Nc := Nc) S v)

/-- **The restriction is faithful**: on any configuration, reading only `S` gives the same value,
provided `S` contains the plaquette's boundary links. This is `hol_congr_on_support` — a holonomy
reads only the links its own word names — and it is what makes `plaqOn` an observable of `S`. -/
theorem plaqOn_eq (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk)
    (hsupp : ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    plaqOn (Nc := Nc) bd p S (fun i : S => U i.val) = wilsonPlaqObs (N := Nc) bd p U := by
  unfold plaqOn wilsonPlaqObs
  congr 1
  refine MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => ?_)
  have hmem : l ∈ S := hsupp l hl
  simp only [extendOn, dif_pos hmem]

/-- `plaqOn` is measurable — the extension is a coordinatewise projection-or-constant. -/
theorem measurable_plaqOn (bd : Pq → List (Lk × Bool)) (p : Pq) (S : Finset Lk) :
    Measurable (plaqOn (Nc := Nc) bd p S) := by
  refine (measurable_wilsonPlaqObs bd p).comp ?_
  classical
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i ∈ S
  · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
  · simp only [extendOn, dif_neg h]; exact measurable_const

/-- **CLUSTERING AT ZERO COUPLING, at any geometry.** If two plaquettes draw their boundary words
from disjoint link sets then their CONNECTED correlation vanishes identically at `β = 0`.

At zero coupling the Boltzmann weight is `1`, so the state is product Haar
(`wilsonSystem_expect_at_zero`) and observables reading disjoint blocks are independent
(`WilsonReal.block_integral_factor`). The unconnected correlation is then exactly the product of the
two marginals, which is what the connected correlation subtracts.

This is the `k = 0` coefficient of the strong-coupling expansion, and it is the only one that costs
nothing: at order `k` one must show that `k` activated plaquettes cannot link two at separation `d`
when `k < d`, which is the combinatorial heart and is not proved here. -/
theorem wilsonCorrConn_at_zero_of_disjoint (bd : Pq → List (Lk × Bool)) (p₀ p : Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (h0 : ∀ l ∈ (bd p₀).map Prod.fst, l ∈ S)
    (h1 : ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ 0 p = 0 := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (plaqOn (Nc := Nc) bd p₀ S) (plaqOn (Nc := Nc) bd p T)
    (measurable_plaqOn bd p₀ S) (measurable_plaqOn bd p T)
  -- rewrite both sides of the factorisation into the full-configuration observables
  have hprod : ∀ U : Lk → MassGap.SUN.SU Nc,
      plaqOn (Nc := Nc) bd p₀ S (fun i : S => U i.val)
        * plaqOn (Nc := Nc) bd p T (fun i : T => U i.val)
      = wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U := by
    intro U; rw [plaqOn_eq bd p₀ S h0 U, plaqOn_eq bd p T h1 U]
  simp only [hprod] at hfac
  simp only [plaqOn_eq bd p₀ S h0, plaqOn_eq bd p T h1] at hfac
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  rw [wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero, wilsonSystem_expect_at_zero]
  show (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
      ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
    - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc))))
      * (∫ U, wilsonPlaqObs (N := Nc) bd p U
        ∂((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))) = 0
  rw [show ((wilsonSystem bd (wilsonDensity (N := Nc))).vol (probHaar (MassGap.SUN.SU Nc)))
      = Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) from rfl]
  -- the same equation, stated at the `Config` binder so `rw` matches it syntactically
  have hfac' : (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
        wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
          wilsonPlaqObs (N := Nc) bd p₀ U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config,
          wilsonPlaqObs (N := Nc) bd p U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := hfac
  exact sub_eq_zero_of_eq hfac'

#print axioms wilsonCorrConn_at_zero_of_disjoint

/-! ### The engine every order needs: factorisation across a link-disjoint SPLIT

At order `k` the Taylor coefficient of `⟨φ₀ φ_d⟩_β` at `β = 0` is a Haar moment of
`φ₀ · φ_d · Sᵏ`, and `S = ∑_p φ_p` expands it over `k`-tuples of plaquettes. A tuple contributes to
the CONNECTED correlation only if it links `p₀` to `p_d`; otherwise the whole product splits into two
groups drawing on disjoint links, the Haar expectation factorises, and the connected subtraction
removes it.

`block_integral_factor` is stated for two observables. What the expansion needs is the same fact for
two GROUPS of plaquettes, which is below: bundle each group into a single observable of its own
links, and the two-block lemma applies unchanged. This is the step used once per order, and it is
where `k < d` will do its work — a group of `k` plaquettes cannot bridge a separation of `d`. -/

/-- A finite product of plaquette observables, read as a function of `S`'s links alone. -/
noncomputable def prodOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ A, plaqOn (Nc := Nc) bd p S v

/-- The bundled product is faithful on any configuration, given a support hypothesis for every
plaquette in the group. -/
theorem prodOn_eq (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    prodOn (Nc := Nc) bd A S (fun i : S => U i.val)
      = ∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U := by
  unfold prodOn
  exact Finset.prod_congr rfl (fun p hp => plaqOn_eq bd p S (hsupp p hp) U)

/-- The bundled product is measurable — a finite product of measurable factors. -/
theorem measurable_prodOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk) :
    Measurable (prodOn (Nc := Nc) bd A S) :=
  Finset.measurable_prod _ (fun p _ => measurable_plaqOn bd p S)

/-- **HAAR FACTORISES ACROSS A LINK-DISJOINT SPLIT OF TWO GROUPS.** If every plaquette of `A` draws
its boundary word from `S`, every plaquette of `B` from `T`, and `S` and `T` are disjoint, then the
Haar expectation of the whole product is the product of the two group expectations.

This is `block_integral_factor` with each group bundled into one observable, and it is the fact that
makes an unlinked configuration contribute nothing to a connected correlation — at EVERY order of the
strong-coupling expansion, not just the zeroth. -/
theorem haar_prod_factor_of_split (bd : Pq → List (Lk × Bool)) (A B : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ B, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U) * (∏ p ∈ B, wilsonPlaqObs (N := Nc) bd p U)
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ A, wilsonPlaqObs (N := Nc) bd p U)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ B, wilsonPlaqObs (N := Nc) bd p U)
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (prodOn (Nc := Nc) bd A S) (prodOn (Nc := Nc) bd B T)
    (measurable_prodOn bd A S) (measurable_prodOn bd B T)
  simp only [prodOn_eq bd A S hA, prodOn_eq bd B T hB] at hfac
  exact hfac

#print axioms haar_prod_factor_of_split

/-! ### Order one, and why the cumulant machinery is not needed

The obstacle at order `k` looked like cumulants, and Mathlib has none. The cumulant structure is an
artefact of the RATIO `⟨·⟩ = N/Z`, and the ratio can be cleared. Writing `N(O,β) = ∫O e^{−βS}` and
`Z(β) = ∫e^{−βS}`,

    ρ_conn = [ N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) ] / Z²,      Z(0) = 1 ≠ 0,

so `ρ_conn` vanishes to order `d` at `β = 0` exactly when its NUMERATOR does — and the numerator is a
difference of products of integrals, with no division in it. Its coefficients are

    [βᵏ] = (−1)ᵏ ∑_{i+j=k} 1/(i!j!) [ ∫φ₀φ_d Sⁱ · ∫Sʲ − ∫φ₀Sⁱ · ∫φ_d Sʲ ],

a polynomial identity in Haar moments whose engine is `haar_prod_factor_of_split`.

Order one is below. Its proof is four applications of that lemma and `ring`, and the two cases — the
extra plaquette joining either side of the split — cancel by the same mechanism. That is the pattern
the general order follows. -/

/-- **ORDER ONE CANCELS.** The `k = 1` coefficient of the connected correlation's numerator vanishes
whenever the three plaquettes admit a link-disjoint split with `p₀` and `p_d` on opposite sides — that
is, whenever the single available plaquette `q` fails to bridge them.

Both cases collapse for the same reason. With `q` on `p₀`'s side the first two terms are equal and the
last two are equal; with `q` on `p_d`'s side the pairing is the mirror image. Neither case needs to
know anything about `q` beyond which side of the split it lies on, which is exactly the content of
"fewer than `d` plaquettes cannot bridge a separation of `d`" at `d = 2`. -/
theorem order_one_cancels (bd : Pq → List (Lk × Bool)) (p₀ pd q : Pq)
    (hq0 : q ≠ p₀) (hqd : q ≠ pd) (h0d : p₀ ≠ pd)
    (S T : Finset Lk) (hST : Disjoint S T)
    (h0 : ∀ l ∈ (bd p₀).map Prod.fst, l ∈ S)
    (hd : ∀ l ∈ (bd pd).map Prod.fst, l ∈ T)
    (hq : (∀ l ∈ (bd q).map Prod.fst, l ∈ S) ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ T)) :
    (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      + (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      - (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) = 0 := by
  classical
  -- the split with `p₀` alone against `p_d` alone, used in both cases
  have hsplit0d := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd} S T hST
    (by simpa using h0) (by simpa using hd)
  simp only [Finset.prod_singleton] at hsplit0d
  rcases hq with hqS | hqT
  · -- `q` joins `p₀`'s side
    have hA := haar_prod_factor_of_split (Nc := Nc) bd {p₀, q} {pd} S T hST
      (by
        intro p hp l hl
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact h0 l hl
        · rw [Finset.mem_singleton] at hp'; subst hp'; exact hqS l hl)
      (by simpa using hd)
    have hB := haar_prod_factor_of_split (Nc := Nc) bd {q} {pd} S T hST
      (by simpa using hqS) (by simpa using hd)
    have hC := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd} S T hST
      (by simpa using h0) (by simpa using hd)
    simp only [Finset.prod_pair hq0.symm, Finset.prod_singleton] at hA
    simp only [Finset.prod_singleton] at hB hC
    -- the `p_d`-side integral of `φ_d · φ_q` factorises the other way
    have hD := haar_prod_factor_of_split (Nc := Nc) bd {q} {pd} S T hST
      (by simpa using hqS) (by simpa using hd)
    simp only [Finset.prod_singleton] at hD
    have hDcomm : (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hD]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    have hAcomm : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hA]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    rw [hAcomm, hC, hDcomm]
    ring
  · -- `q` joins `p_d`'s side — the mirror image
    have hA := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {pd, q} S T hST
      (by simpa using h0)
      (by
        intro p hp l hl
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact hd l hl
        · rw [Finset.mem_singleton] at hp'; subst hp'; exact hqT l hl)
    have hB := haar_prod_factor_of_split (Nc := Nc) bd {p₀} {q} S T hST
      (by simpa using h0) (by simpa using hqT)
    simp only [Finset.prod_singleton, Finset.prod_pair hqd.symm] at hA
    simp only [Finset.prod_singleton] at hB
    have hAcomm : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
          * wilsonPlaqObs (N := Nc) bd q U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          * (∫ U, wilsonPlaqObs (N := Nc) bd pd U * wilsonPlaqObs (N := Nc) bd q U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
      rw [← hA]; exact integral_congr_ae (Filter.Eventually.of_forall (fun U => by ring))
    rw [hAcomm, hB, hsplit0d]
    ring

#print axioms order_one_cancels

/-! ### Connected means connected — at EVERY coupling, not order by order

Working the general order turned up a stronger statement than order-by-order vanishing, and a simpler
one. Suppose the plaquette set splits as `A ⊎ Aᶜ` with `A`'s links inside `S`, `Aᶜ`'s inside `T`, and
`S`, `T` disjoint — `p₀ ∈ A`, `p_d ∈ Aᶜ`. Then the action splits, `S = S_A + S_{Aᶜ}`, each half a
function of its own links, so the Boltzmann weight factorises and every integral does:

    N(φ₀φ_d) = N_A(φ₀)·N_B(φ_d)     Z      = Z_A·Z_B
    N(φ₀)    = N_A(φ₀)·Z_B          N(φ_d) = Z_A·N_B(φ_d)

and therefore

    D = N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) = N_A(φ₀)N_B(φ_d)Z_A Z_B − N_A(φ₀)Z_B Z_A N_B(φ_d) = 0

**identically in `β`**, not merely to order `d`. The `β = 0` result above is the special case where
the split is free; this is the statement for every coupling.

WHAT IT IS AND IS NOT. It says the connected correlation vanishes when the two plaquettes sit in
non-interacting halves — "connected means connected", exactly. It does NOT apply to a real lattice,
which is connected and admits no such split; that is precisely why the expansion exists. Its value is
that it is the statement each TERM of the expansion needs, with the activated plaquettes in place of
the whole set, and it fixes the shape of the general argument: the term vanishes when its activated
set fails to bridge, and that failure is a split. -/

/-- The half-action carried by `A`, read on `S`'s links alone. -/
noncomputable def actOn (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p (extendOn (Lk := Lk) (Nc := Nc) S v))

/-- The half-action is faithful on any configuration, given a support hypothesis for the group. -/
theorem actOn_eq (bd : Pq → List (Lk × Bool)) (A : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    actOn (Nc := Nc) bd A S (fun i : S => U i.val)
      = ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U) := by
  unfold actOn
  exact Finset.sum_congr rfl (fun p hp => by
    rw [MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => by
      have hmem : l ∈ S := hsupp p hp l hl
      simp only [extendOn, dif_pos hmem])])

/-- A plaquette product times its half's Boltzmann factor — the observable each of the four integrals
in `D` restricts to on one side of the split. -/
noncomputable def wtOn (bd : Pq → List (Lk × Bool)) (E : Finset Pq) (A : Finset Pq)
    (S : Finset Lk) (β : ℝ) (v : S → MassGap.SUN.SU Nc) : ℝ :=
  prodOn (Nc := Nc) bd E S v * Real.exp (-β * actOn (Nc := Nc) bd A S v)

theorem wtOn_eq (bd : Pq → List (Lk × Bool)) (E A : Finset Pq) (S : Finset Lk) (β : ℝ)
    (hE : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    wtOn (Nc := Nc) bd E A S β (fun i : S => U i.val)
      = (∏ p ∈ E, wilsonPlaqObs (N := Nc) bd p U)
        * Real.exp (-β * ∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold wtOn
  rw [prodOn_eq bd E S hE U, actOn_eq bd A S hA U]

theorem measurable_wtOn (bd : Pq → List (Lk × Bool)) (E A : Finset Pq) (S : Finset Lk) (β : ℝ) :
    Measurable (wtOn (Nc := Nc) bd E A S β) := by
  refine (measurable_prodOn bd E S).mul ?_
  refine (Real.measurable_exp.comp ?_)
  refine (measurable_const.mul ?_)
  exact Finset.measurable_sum _ (fun p _ =>
    measurable_wilsonDensity.comp ((measurable_wilsonHol bd p).comp
      (by
        classical
        refine measurable_pi_lambda _ (fun i => ?_)
        by_cases h : i ∈ S
        · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
        · simp only [extendOn, dif_neg h]; exact measurable_const)))

#print axioms actOn_eq
#print axioms wtOn_eq

/-- **CONNECTED MEANS CONNECTED — the connected correlation vanishes across a link-disjoint split, at
EVERY coupling.**

If the plaquettes split as `A ⊎ Aᶜ` with `A` drawing only on `S`, `Aᶜ` only on `T`, `S` and `T`
disjoint, and `p₀ ∈ A`, `p_d ∈ Aᶜ`, then `ρ_conn(p₀, p_d) = 0` for every `β`.

The action splits into two halves, each a function of its own links, so the Boltzmann weight
factorises and all four integrals do:

    N(φ₀φ_d) = a·b,  Z = c·d,  N(φ₀) = a·d,  N(φ_d) = c·b

whence `N(φ₀φ_d)·Z − N(φ₀)·N(φ_d) = abcd − adcb = 0`. Nothing is expanded and no coupling is small:
two non-interacting halves have no connected correlation, and this says exactly that.

WHY IT MATTERS AND WHAT IT DOES NOT DO. A real lattice is connected and admits no such split, so this
does not apply to it directly — which is why the expansion exists at all. What it fixes is the SHAPE
of the general order: an expansion term vanishes when its activated plaquettes fail to bridge `p₀` to
`p_d`, and failing to bridge IS a split of this kind. The order-`k` statement is this theorem applied
to the activated set rather than to the whole lattice. -/
theorem wilsonCorrConn_eq_zero_of_split (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (A : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ Aᶜ, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (h0 : p₀ ∈ A) (hd : pd ∈ Aᶜ) (β : ℝ) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd = 0 := by
  classical
  set vol := Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)) with hvol
  -- the action splits into the two halves, each a function of its own links
  have hact : ∀ U : Lk → MassGap.SUN.SU Nc,
      (wilsonSystem bd (wilsonDensity (N := Nc))).action U
        = (∑ p ∈ A, wilsonDensity (N := Nc) (wilsonHol bd p U))
          + ∑ p ∈ Aᶜ, wilsonDensity (N := Nc) (wilsonHol bd p U) := by
    intro U
    show (∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U)) = _
    rw [← Finset.sum_add_sum_compl A]
  -- the four factorisations, one per integral in the connected combination
  have hsplit : ∀ (E F : Finset Pq),
      (∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) →
      (∀ p ∈ F, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) →
      (∫ U, ((∏ p ∈ E, wilsonPlaqObs (N := Nc) bd p U)
              * (∏ p ∈ F, wilsonPlaqObs (N := Nc) bd p U))
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        = (∫ U, wtOn (Nc := Nc) bd E A S β (fun i : S => U i.val) ∂vol)
          * (∫ U, wtOn (Nc := Nc) bd F Aᶜ T β (fun i : T => U i.val) ∂vol) := by
    intro E F hE hF
    have hfac := block_integral_factor (N := Nc) S T hST
      (wtOn (Nc := Nc) bd E A S β) (wtOn (Nc := Nc) bd F Aᶜ T β)
      (measurable_wtOn bd E A S β) (measurable_wtOn bd F Aᶜ T β)
    rw [← hfac]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    dsimp only
    rw [wtOn_eq bd E A S β hE hA U, wtOn_eq bd F Aᶜ T β hF hB U]
    unfold System.boltz
    rw [hact U, mul_add, neg_mul, neg_mul, Real.exp_add]
    ring
  -- name the four halves
  have hN2 := hsplit {p₀} {pd} (by simpa using hA p₀ h0) (by simpa using hB pd hd)
  have hZ := hsplit ∅ ∅ (by simp) (by simp)
  have hN0 := hsplit {p₀} ∅ (by simpa using hA p₀ h0) (by simp)
  have hNd := hsplit ∅ {pd} (by simp) (by simpa using hB pd hd)
  simp only [Finset.prod_singleton, Finset.prod_empty, one_mul, mul_one] at hN2 hZ hN0 hNd
  -- assemble
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  unfold System.expect System.corrNum System.partition
  show ((∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
      / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol))
    - ((∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol))
      * ((∫ U, wilsonPlaqObs (N := Nc) bd pd U
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)
        / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U ∂vol)) = 0
  rw [hN2, hZ, hN0, hNd]
  set a := ∫ U, wtOn (Nc := Nc) bd {p₀} A S β (fun i : S => U i.val) ∂vol with ha
  set b := ∫ U, wtOn (Nc := Nc) bd {pd} Aᶜ T β (fun i : T => U i.val) ∂vol with hb
  set c := ∫ U, wtOn (Nc := Nc) bd (∅ : Finset Pq) A S β (fun i : S => U i.val) ∂vol with hc
  set e := ∫ U, wtOn (Nc := Nc) bd (∅ : Finset Pq) Aᶜ T β (fun i : T => U i.val) ∂vol with he
  rcases eq_or_ne (c * e) 0 with hz | hz
  · rw [hz]; simp
  · field_simp
    ring

#print axioms wilsonCorrConn_eq_zero_of_split

/-! ### The expansion is EXACT and FINITE — no series, no convergence

The strong-coupling expansion is usually presented as a power series in `β` whose convergence is the
hard part. On a FINITE lattice it is neither: it is an algebraic identity. Writing
`w_p = e^{−βφ_p} − 1`,

    e^{−βS} = ∏_p e^{−βφ_p} = ∏_p (1 + w_p) = ∑_{E ⊆ P} ∏_{p∈E} w_p

by `Finset.prod_add` — a finite sum over SUBSETS of plaquettes, exact at every `β`, with nothing to
converge. This is what removes the analytic difficulty from the combinatorial one: there is no
radius, no remainder, and no Taylor coefficient to bound. What is left is which subsets contribute.

Each factor obeys `|w_p| ≤ e^{2|β|} − 1` (`boltz_factor_bound`), so a subset of size `n` contributes
at most `(e^{2|β|}−1)ⁿ`, and a subset whose plaquettes fail to bridge `p₀` to `p_d` contributes
NOTHING, by `wilsonCorrConn_eq_zero_of_split` applied to that subset's own split. Both halves of the
chain bound are then in hand, and what remains is counting the bridging subsets. -/

/-- **THE BOLTZMANN WEIGHT EXPANDS OVER SUBSETS, EXACTLY.** A finite identity at every coupling, not
a truncated series: `e^{−βS} = ∑_{E ⊆ P} ∏_{p∈E} (e^{−βφ_p} − 1)`.

DERIVED: the `1` split off each factor is `e^{−βφ_p} = (e^{−βφ_p} − 1) + 1`, and the sum over subsets
is `Finset.prod_add`. Nothing is approximated and no coupling is assumed small. -/
theorem boltz_eq_subset_sum (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) :
    (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
      = ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) := by
  classical
  have hexp : (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
      = ∏ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) := by
    unfold System.boltz
    show Real.exp (-β * ∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U)) = _
    rw [Finset.mul_sum, ← Real.exp_sum]
    exact congrArg Real.exp (Finset.sum_congr rfl (fun p _ => by ring))
  rw [hexp]
  -- split each factor as `w_p + 1`, by congruence rather than rewriting (which would loop)
  have hone : ∏ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = ∏ p : Pq, ((Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) + 1) :=
    Finset.prod_congr rfl (fun p _ => by ring)
  rw [hone, Finset.prod_add]
  exact Finset.sum_congr rfl (fun E _ => by simp)

#print axioms boltz_eq_subset_sum

/-- **A subset's weight is bounded by the per-plaquette weight to its size.** With
`boltz_factor_bound` per factor, a subset of `n` plaquettes contributes at most `(e^{2|β|}−1)ⁿ` — the
`qⁿ` the chain bound sums.

DERIVED: nothing beyond `boltz_factor_bound` and `Finset.prod_le_prod`; the exponent is the subset's
cardinality. -/
theorem subset_weight_bound (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : Lk → MassGap.SUN.SU Nc) (E : Finset Pq) :
    |∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1)|
      ≤ (Real.exp (2 * |β|) - 1) ^ E.card := by
  classical
  rw [Finset.abs_prod]
  calc ∏ p ∈ E, |Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1|
      ≤ ∏ _p ∈ E, (Real.exp (2 * |β|) - 1) := by
        refine Finset.prod_le_prod (fun p _ => abs_nonneg _) (fun p _ => ?_)
        exact boltz_factor_bound (wilsonDensity_nonneg hN _) (wilsonDensity_le_two hN _)
    _ = (Real.exp (2 * |β|) - 1) ^ E.card := by rw [Finset.prod_const]

#print axioms subset_weight_bound

/-- **THE NUMERATOR EXPANDS OVER SUBSETS, EXACTLY.** `boltz_eq_subset_sum` moved inside the integral:
since the sum is FINITE, linearity applies with no convergence condition — only integrability of each
term, which is carried as a hypothesis rather than assumed away.

This is what makes a term-by-term analysis possible at all: every Gibbs numerator is a finite sum of
Haar integrals, one per subset of activated plaquettes, exact at every coupling. -/
theorem corrNum_eq_subset_sum (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (Lk → MassGap.SUN.SU Nc) → ℝ)
    (hint : ∀ E ∈ (Finset.univ : Finset Pq).powerset,
      Integrable (fun U => O U * ∏ p ∈ E,
          (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
        (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) :
    (∫ U, O U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          ∫ U, O U * (∏ p ∈ E,
              (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hfun : (fun U => O U * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U)
      = fun U => ∑ E ∈ (Finset.univ : Finset Pq).powerset,
          O U * ∏ p ∈ E,
            (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1) := by
    funext U
    rw [boltz_eq_subset_sum bd β U, Finset.mul_sum]
  rw [hfun]
  exact integral_finsetSum _ hint

#print axioms corrNum_eq_subset_sum

/-! ### Plaquette connectivity — the combinatorial side of the split

Every route to the chain bound needs the same structure and the tree has it nowhere: when do two
plaquettes interact, and what does it mean for a set of them to separate `p₀` from `p_d`. Two
plaquettes interact exactly when they SHARE A LINK — that is the only way the Haar measure couples
them, which is the content of `haar_prod_factor_of_split`.

The theorems above take two explicit link sets `S`, `T` and a disjointness hypothesis. That is the
right analytic interface and the wrong combinatorial one: what a counting argument produces is a SET
OF PLAQUETTES closed under touching, not a pair of link sets. The bridge is below, and after it the
vanishing theorem can be stated in purely combinatorial terms. -/

/-- The links a plaquette's boundary word names. -/
def linkSupp (bd : Pq → List (Lk × Bool)) (p : Pq) : Finset Lk :=
  ((bd p).map Prod.fst).toFinset

/-- Two plaquettes TOUCH when they share a link — the only way the Haar measure couples them. -/
def Touch (bd : Pq → List (Lk × Bool)) (p q : Pq) : Prop :=
  ∃ l ∈ linkSupp bd p, l ∈ linkSupp bd q

/-- A plaquette's own links lie in the union over any set containing it. -/
theorem supp_subset_biUnion (bd : Pq → List (Lk × Bool)) (A : Finset Pq) :
    ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ A.biUnion (linkSupp bd) := by
  intro p hp l hl
  exact Finset.mem_biUnion.mpr ⟨p, hp, by simpa [linkSupp] using hl⟩

/-- **A set closed under touching has links disjoint from its complement's.** This is the bridge from
the combinatorial condition a counting argument produces to the analytic hypothesis the vanishing
theorem consumes: no plaquette inside touches one outside, so the two link unions cannot meet. -/
theorem split_links_disjoint (bd : Pq → List (Lk × Bool)) (A : Finset Pq)
    (hclosed : ∀ p ∈ A, ∀ q, q ∉ A → ¬ Touch bd p q) :
    Disjoint (A.biUnion (linkSupp bd)) (Aᶜ.biUnion (linkSupp bd)) := by
  classical
  rw [Finset.disjoint_left]
  intro l hl hl'
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨q, hq, hlq⟩ := Finset.mem_biUnion.mp hl'
  exact hclosed p hp q (Finset.mem_compl.mp hq) ⟨l, hlp, hlq⟩

/-- **CONNECTED MEANS CONNECTED, COMBINATORIALLY.** If some set of plaquettes containing `p₀` is
closed under touching and excludes `p_d`, the connected correlation vanishes at every coupling.

This is `wilsonCorrConn_eq_zero_of_split` with the link bookkeeping discharged: the hypothesis is now
a statement about the plaquette graph alone — "`p₀`'s side is closed and `p_d` is not in it" — which
is what a connectivity or counting argument actually delivers. No link sets appear in it. -/
theorem wilsonCorrConn_eq_zero_of_touch_closed (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (A : Finset Pq) (hclosed : ∀ p ∈ A, ∀ q, q ∉ A → ¬ Touch bd p q)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) (β : ℝ) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd = 0 := by
  classical
  exact wilsonCorrConn_eq_zero_of_split bd p₀ pd A
    (A.biUnion (linkSupp bd)) (Aᶜ.biUnion (linkSupp bd))
    (split_links_disjoint bd A hclosed)
    (supp_subset_biUnion bd A) (supp_subset_biUnion bd Aᶜ)
    h0 (Finset.mem_compl.mpr hd) β

#print axioms split_links_disjoint
#print axioms wilsonCorrConn_eq_zero_of_touch_closed

/-! ### The polymer structure — weights multiply across components

A polymer model is exactly a weight that MULTIPLIES over connected components, and that is what
`haar_prod_factor_of_split` says once one notices that the Boltzmann correction `w_p = e^{−βφ_p} − 1`
reads only `p`'s own links, just as `φ_p` does. So for any per-plaquette function `f`,

    ∫ ∏_{p ∈ E₁ ⊎ E₂} f(φ_p)  =  (∫ ∏_{E₁} f(φ_p)) · (∫ ∏_{E₂} f(φ_p))

whenever `E₁` and `E₂` are link-disjoint. Setting `f = id` recovers the plaquette observables; setting
`f x = e^{−βx} − 1` gives the activated-subset weights `ζ(E) = ∫W_E` of the expansion. With
`ζ` multiplicative over components, `Z = ∑_E ζ(E)` IS a polymer partition function — which is the
object Mayer's theorem is about.

This is the entry point, not the theorem: Mayer says `log Z` is a sum over CONNECTED clusters, and
that is what supplies the `Kⁿ` count. Multiplicativity is its hypothesis. -/

/-- A per-plaquette function of the plaquette's own energy, over a group, read on `S`'s links. -/
noncomputable def locOn (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p (extendOn (Lk := Lk) (Nc := Nc) S v)))

theorem locOn_eq (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (E : Finset Pq) (S : Finset Lk)
    (hsupp : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    locOn (Nc := Nc) bd f E S (fun i : S => U i.val)
      = ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold locOn
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [MassGap.ReflectionPositivity.hol_congr_on_support bd p _ U (fun l hl => by
    have hmem : l ∈ S := hsupp p hp l hl
    simp only [extendOn, dif_pos hmem])]

theorem measurable_locOn (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (E : Finset Pq) (S : Finset Lk) :
    Measurable (locOn (Nc := Nc) bd f E S) := by
  classical
  refine Finset.measurable_prod _ (fun p _ => hf.comp ?_)
  exact measurable_wilsonDensity.comp ((measurable_wilsonHol bd p).comp
    (by
      refine measurable_pi_lambda _ (fun i => ?_)
      by_cases h : i ∈ S
      · simp only [extendOn, dif_pos h]; exact measurable_pi_apply (⟨i, h⟩ : S)
      · simp only [extendOn, dif_neg h]; exact measurable_const))

/-- **THE POLYMER WEIGHT IS MULTIPLICATIVE ACROSS A LINK-DISJOINT SPLIT.** For any per-plaquette
function `f` — in particular `f x = e^{−βx} − 1`, the activated-subset weight — the Haar integral of
a product over two link-disjoint groups factorises.

This is the hypothesis of a polymer model, and it is what makes `Z = ∑_E ζ(E)` with `ζ` multiplicative
over components. Mayer's theorem takes it from here; nothing below supplies Mayer. -/
theorem weight_mult_of_split (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (A B : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hA : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hB : ∀ p ∈ B, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, (∏ p ∈ A, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          * (∏ p ∈ B, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ A, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ B, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (locOn (Nc := Nc) bd f A S) (locOn (Nc := Nc) bd f B T)
    (measurable_locOn bd hf A S) (measurable_locOn bd hf B T)
  simp only [locOn_eq bd f A S hA, locOn_eq bd f B T hB] at hfac
  exact hfac

#print axioms weight_mult_of_split

/-! ### THE VOLUME CANCELLATION, EXACTLY — non-bridging PAIRS cancel under an exchange

`boltz_eq_subset_sum` makes every Gibbs numerator a FINITE sum over activated subsets, so the
connected correlation's numerator

    D(β) = N(φ₀φ_d)·Z − N(φ₀)·N(φ_d)

is a finite DOUBLE sum over pairs `(E, F)` of activated subsets, with summand

    T(E,F) = ζ_{p₀p_d}(E)·ζ_∅(F) − ζ_{p₀}(E)·ζ_{p_d}(F),   ζ_D(E) = ∫ (∏_{p∈D} φ_p)·∏_{p∈E} w_p,

`ζ_D(E)` being `zw` below. `wilsonCorrConn_eq_zero_of_split` says `D = 0` when the WHOLE lattice
splits, and this file already says that never happens on a real lattice. What does happen is that a
single PAIR splits, and the content here is that such pairs cancel — not term by term, which is
false, but two at a time, under an explicit exchange.

Let `A` be touch-closed relative to `V = E ∪ F ∪ {p₀, p_d}` with `p₀ ∈ A` and `p_d ∉ A`: `A`
separates the two plaquettes inside the union of the two activated sets. Writing `X = E ∩ A`,
`Y = E \ A`, `X' = F ∩ A`, `Y' = F \ A`, all four integrals factorise across the split and

    T(E,F) = ζ₀(X)·ζ(X')·(ζ_d(Y)·ζ(Y') − ζ(Y)·ζ_d(Y')),

so the EXCHANGE `(E,F) ↦ (X ∪ Y', X' ∪ Y)` — swap the far halves, keep the near ones — sends `T` to
its negative. It preserves `E ∪ F`, hence `A`, hence the separating condition, and it is an
involution. So the entire non-bridging part of the double sum is zero.

That is the volume cancellation, PROVED rather than assumed: nothing in it is perturbative, no
coupling is small, and the lattice may be as large as one likes. It is the step the prose above calls
"the whole content of a cluster expansion".

WHAT IS LEFT, PRECISELY. The surviving pairs are exactly those in which `p₀` reaches `p_d` by a chain
of TOUCHING plaquettes lying inside `E ∪ F`. Bounding their number and weight is the counting
statement `ChainBound` still needs, and nothing here supplies it. -/

/-- The activated weight of one plaquette, `w(x) = e^{−βx} − 1`. Named so that the splitting lemmas
below match it syntactically; `wfun_apply` is the `rfl` that connects it to `boltz_eq_subset_sum`.

DERIVED: the `1` is the `1` split off `e^{−βφ_p} = (e^{−βφ_p} − 1) + 1` in `boltz_eq_subset_sum`. -/
noncomputable def wfun (β x : ℝ) : ℝ := Real.exp (-(β * x)) - 1

theorem wfun_apply (β x : ℝ) : wfun β x = Real.exp (-(β * x)) - 1 := rfl

theorem measurable_wfun (β : ℝ) : Measurable (wfun β) :=
  (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).sub measurable_const

/-- One side of a link-disjoint split carries BOTH plaquette observables and activated weights. The
two existing bundles (`prodOn`, `locOn`) are each half of what a term of the expansion restricts to;
this is the whole of it. -/
noncomputable def mixOn (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (D E : Finset Pq) (S : Finset Lk)
    (v : S → MassGap.SUN.SU Nc) : ℝ :=
  prodOn (Nc := Nc) bd D S v * locOn (Nc := Nc) bd f E S v

theorem mixOn_eq (bd : Pq → List (Lk × Bool)) (f : ℝ → ℝ) (D E : Finset Pq) (S : Finset Lk)
    (hD : ∀ p ∈ D, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE : ∀ p ∈ E, ∀ l ∈ (bd p).map Prod.fst, l ∈ S) (U : Lk → MassGap.SUN.SU Nc) :
    mixOn (Nc := Nc) bd f D E S (fun i : S => U i.val)
      = (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, f (wilsonDensity (N := Nc) (wilsonHol bd p U)) := by
  unfold mixOn
  rw [prodOn_eq bd D S hD U, locOn_eq bd f E S hE U]

theorem measurable_mixOn (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (D E : Finset Pq) (S : Finset Lk) : Measurable (mixOn (Nc := Nc) bd f D E S) :=
  (measurable_prodOn bd D S).mul (measurable_locOn bd hf E S)

/-- **HAAR FACTORISES ACROSS A LINK-DISJOINT SPLIT, OBSERVABLES AND WEIGHTS TOGETHER.** The common
generalisation of `haar_prod_factor_of_split` (observables only) and `weight_mult_of_split` (weights
only): a term of the subset expansion carries both, and both must cross the split at once. -/
theorem haar_mix_factor (bd : Pq → List (Lk × Bool)) {f : ℝ → ℝ} (hf : Measurable f)
    (D₁ E₁ D₂ E₂ : Finset Pq) (S T : Finset Lk) (hST : Disjoint S T)
    (hD₁ : ∀ p ∈ D₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hD₂ : ∀ p ∈ D₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    (∫ U, ((∏ p ∈ D₁, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
          * ((∏ p ∈ D₂, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U)))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = (∫ U, (∏ p ∈ D₁, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₁, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        * (∫ U, (∏ p ∈ D₂, wilsonPlaqObs (N := Nc) bd p U)
            * ∏ p ∈ E₂, f (wilsonDensity (N := Nc) (wilsonHol bd p U))
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) := by
  classical
  have hfac := block_integral_factor (N := Nc) S T hST
    (mixOn (Nc := Nc) bd f D₁ E₁ S) (mixOn (Nc := Nc) bd f D₂ E₂ T)
    (measurable_mixOn bd hf D₁ E₁ S) (measurable_mixOn bd hf D₂ E₂ T)
  simp only [mixOn_eq bd f D₁ E₁ S hD₁ hE₁, mixOn_eq bd f D₂ E₂ T hD₂ hE₂] at hfac
  exact hfac

#print axioms haar_mix_factor

/-- **A TERM OF THE EXPANSION.** `zw bd β D E` is `∫ (∏_{p ∈ D} φ_p) · ∏_{p ∈ E} w_p` against product
Haar: the plaquette observables `D` read against the activated subset `E`. The four integrals the
connected numerator is built from are the four choices `D = {p₀,p_d}, ∅, {p₀}, {p_d}`. -/
noncomputable def zw (bd : Pq → List (Lk × Bool)) (β : ℝ) (D E : Finset Pq) : ℝ :=
  ∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
      * ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
    ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

/-- **A TERM SPLITS WHEN ITS PLAQUETTES DO.** If the observables and the activated plaquettes each
divide into two groups drawing on disjoint link sets, the term is the product of the two half-terms.
This is the one computational step the exchange below uses, applied eight times. -/
theorem zw_split (bd : Pq → List (Lk × Bool)) (β : ℝ) (D D₁ D₂ E E₁ E₂ : Finset Pq)
    (S T : Finset Lk) (hST : Disjoint S T)
    (hDu : D = D₁ ∪ D₂) (hEu : E = E₁ ∪ E₂)
    (hDd : Disjoint D₁ D₂) (hEd : Disjoint E₁ E₂)
    (hD₁ : ∀ p ∈ D₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hE₁ : ∀ p ∈ E₁, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (hD₂ : ∀ p ∈ D₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T)
    (hE₂ : ∀ p ∈ E₂, ∀ l ∈ (bd p).map Prod.fst, l ∈ T) :
    zw (Nc := Nc) bd β D E = zw (Nc := Nc) bd β D₁ E₁ * zw (Nc := Nc) bd β D₂ E₂ := by
  classical
  subst hDu; subst hEu
  unfold zw
  rw [← haar_mix_factor (Nc := Nc) bd (measurable_wfun β) D₁ E₁ D₂ E₂ S T hST hD₁ hE₁ hD₂ hE₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  simp only [Finset.prod_union hDd, Finset.prod_union hEd]
  ring

#print axioms zw_split

/-- The summand of the connected numerator's double sum, at the pair `q = (E, F)` of activated
subsets: `ζ_{p₀p_d}(E)·ζ_∅(F) − ζ_{p₀}(E)·ζ_{p_d}(F)`. -/
noncomputable def pairTerm (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (q : Finset Pq × Finset Pq) : ℝ :=
  zw (Nc := Nc) bd β {p₀, pd} q.1 * zw (Nc := Nc) bd β ∅ q.2
    - zw (Nc := Nc) bd β {p₀} q.1 * zw (Nc := Nc) bd β {pd} q.2

/-- **THE EXCHANGE.** Across a separator `A`, swap the two pairs' far halves and keep their near
halves. It preserves the union of the pair, so it preserves the separator it was built from. -/
def pairFlip (A : Finset Pq) (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  ((q.1 ∩ A) ∪ (q.2 \ A), (q.2 ∩ A) ∪ (q.1 \ A))

/-- **THE CANCELLATION, FOR ONE PAIR.** If some `A` separates `p₀` from `p_d` inside
`E ∪ F ∪ {p₀,p_d}` — touch-closed there, containing `p₀`, missing `p_d` — then the pair's term and
its exchange's term sum to zero.

The eight factorisations are all `zw_split` across the same two link sets, and the algebra is
`ac(be − gh) + ac(hg − eb) = 0`. Nothing is small and nothing is expanded: this is an identity in `β`
on a lattice of any size. -/
theorem pairTerm_add_exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    (zw (Nc := Nc) bd β {p₀, pd} E * zw (Nc := Nc) bd β ∅ F
        - zw (Nc := Nc) bd β {p₀} E * zw (Nc := Nc) bd β {pd} F)
      + (zw (Nc := Nc) bd β {p₀, pd} ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β ∅ ((F ∩ A) ∪ (E \ A))
          - zw (Nc := Nc) bd β {p₀} ((E ∩ A) ∪ (F \ A))
            * zw (Nc := Nc) bd β {pd} ((F ∩ A) ∪ (E \ A))) = 0 := by
  classical
  set V : Finset Pq := E ∪ F ∪ {p₀, pd} with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hp0V : p₀ ∈ V := by rw [hV]; simp
  have hpdV : pd ∈ V := by rw [hV]; simp
  -- the six groups, each on its own side of the split
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have g0 : ({p₀} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
  have gd : ({pd} : Finset Pq) ⊆ V \ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_sdiff.mpr ⟨hpdV, hd⟩
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  -- the set identities the split needs
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDu : ({p₀, pd} : Finset Pq) = {p₀} ∪ {pd} := by ext x; simp
  have hD0 : ({p₀} : Finset Pq) = {p₀} ∪ ∅ := (Finset.union_empty _).symm
  have hDd : ({pd} : Finset Pq) = ∅ ∪ {pd} := (Finset.empty_union _).symm
  have hDz : (∅ : Finset Pq) = ∅ ∪ ∅ := (Finset.union_empty _).symm
  have hd0d : Disjoint ({p₀} : Finset Pq) {pd} := by
    simp [hne]
  -- the eight factorisations
  have e1 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀} {pd} E (E ∩ A) (E \ A) S T hST hDu hEu
    hd0d (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST hDz hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ E (E ∩ A) (E \ A) S T hST hD0 hEu
    (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β {pd} ∅ {pd} F (F ∩ A) (F \ A) S T hST hDd hFu
    (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gFc)
  have e5 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀} {pd} ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hDu rfl hd0d (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gd) (hinT _ gFc)
  have e6 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDz rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gEc)
  have e7 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ ((E ∩ A) ∪ (F \ A)) (E ∩ A) (F \ A)
    S T hST hD0 rfl (by simp) (hIO E F) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gFc)
  have e8 := zw_split (Nc := Nc) bd β {pd} ∅ {pd} ((F ∩ A) ∪ (E \ A)) (F ∩ A) (E \ A)
    S T hST hDd rfl (by simp) (hIO F E) (hinS _ gEm) (hinS _ gFA) (hinT _ gd) (hinT _ gEc)
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

#print axioms pairTerm_add_exchange

/-- The pair form of `pairTerm_add_exchange` — the shape the involution consumes. -/
theorem pairTerm_add_pairFlip (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    pairTerm (Nc := Nc) bd p₀ pd β (E, F)
      + pairTerm (Nc := Nc) bd p₀ pd β (pairFlip A (E, F)) = 0 := by
  simp only [pairTerm, pairFlip]
  exact pairTerm_add_exchange bd p₀ pd hne β E F A hclosed h0 hd

#print axioms pairTerm_add_pairFlip

/-! ### The separator a pair supplies by itself

The hypothesis of `pairTerm_add_exchange` is an existential over separators, and a sum needs a
FUNCTION. `compOf` supplies one: `p₀`'s touch-reachable component inside the pair's own union. It is
touch-closed there by construction, it contains `p₀`, and it misses `p_d` exactly when `p₀` does not
reach `p_d` — which is the definition of a non-bridging pair. -/

/-- Touch-reachability inside a plaquette set — a chain of plaquettes each sharing a link with the
next, all of them lying in `V`. -/
def Reach (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a b : Pq) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ V ∧ y ∈ V ∧ Touch bd x y) a b

open scoped Classical in
/-- `a`'s touch-reachable component inside `V`. -/
noncomputable def compOf (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) : Finset Pq :=
  V.filter (fun p => Reach bd V a p)

open scoped Classical in
theorem mem_compOf {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a p : Pq} :
    p ∈ compOf bd V a ↔ p ∈ V ∧ Reach bd V a p := by
  unfold compOf; exact Finset.mem_filter

open scoped Classical in
theorem self_mem_compOf {bd : Pq → List (Lk × Bool)} {V : Finset Pq} {a : Pq} (ha : a ∈ V) :
    a ∈ compOf bd V a :=
  mem_compOf.mpr ⟨ha, Relation.ReflTransGen.refl⟩

open scoped Classical in
/-- **A COMPONENT IS TOUCH-CLOSED IN ITS OWN SET.** Nothing inside the component touches anything of
`V` outside it: a touch would extend the chain. This is the hypothesis `pairTerm_add_exchange`
consumes, produced rather than assumed. -/
theorem compOf_closed (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (a : Pq) :
    ∀ p ∈ V ∩ compOf bd V a, ∀ r ∈ V \ compOf bd V a, ¬ Touch bd p r := by
  intro p hp r hr ht
  rw [Finset.mem_inter] at hp
  rw [Finset.mem_sdiff] at hr
  exact hr.2 (mem_compOf.mpr ⟨hr.1, (mem_compOf.mp hp.2).2.tail ⟨hp.1, hr.1, ht⟩⟩)

#print axioms compOf_closed

open scoped Classical in
/-- The exchange a pair supplies for itself: flip across `p₀`'s component inside the pair's union. -/
noncomputable def exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq)
    (q : Finset Pq × Finset Pq) : Finset Pq × Finset Pq :=
  pairFlip (compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀) q

/-- The exchange preserves the pair's union — which is why the separator it is built from survives
it, and why it is an involution. -/
theorem pairFlip_union (A : Finset Pq) (q : Finset Pq × Finset Pq) :
    (pairFlip A q).1 ∪ (pairFlip A q).2 = q.1 ∪ q.2 := by
  classical
  ext x
  by_cases hx : x ∈ A <;> simp [pairFlip, hx] <;> tauto

/-- Flipping twice across the same separator is the identity. -/
theorem pairFlip_pairFlip (A : Finset Pq) (q : Finset Pq × Finset Pq) :
    pairFlip A (pairFlip A q) = q := by
  classical
  obtain ⟨X, Y⟩ := q
  simp only [pairFlip, Prod.mk.injEq]
  constructor <;> · ext x; by_cases hx : x ∈ A <;> simp [hx]

theorem exchange_union (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (q : Finset Pq × Finset Pq) :
    (exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 = q.1 ∪ q.2 := by
  unfold exchange; exact pairFlip_union _ q

theorem exchange_exchange (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (q : Finset Pq × Finset Pq) :
    exchange bd p₀ pd (exchange bd p₀ pd q) = q := by
  have h : (exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 ∪ {p₀, pd}
      = q.1 ∪ q.2 ∪ {p₀, pd} := by rw [exchange_union]
  show pairFlip (compOf bd ((exchange bd p₀ pd q).1 ∪ (exchange bd p₀ pd q).2 ∪ {p₀, pd}) p₀)
      (exchange bd p₀ pd q) = q
  rw [h]
  exact pairFlip_pairFlip _ q

#print axioms exchange_exchange

open scoped Classical in
/-- **THE VOLUME CANCELLATION.** The connected numerator's double sum, restricted to the pairs in
which `p₀` does NOT reach `p_d` by a chain of touching plaquettes inside the pair's own union, is
EXACTLY ZERO — at every coupling, on a lattice of any size.

This is what a cluster expansion is for and what this file said was not proved here. The proof is the
exchange `pairFlip` across `p₀`'s own component: it is an involution on the non-bridging pairs
(`exchange_exchange`), it preserves the union and hence the component (`exchange_union`), and it
negates the summand (`pairTerm_add_pairFlip`). A sum equal to its own negation is zero.

WHAT REMAINS is the complementary sum — over pairs whose union DOES carry a touching chain from `p₀`
to `p_d` — and that is a counting problem: how many such pairs there are at each total size, against
the `(e^{2|β|}−1)` each activated plaquette costs (`subset_weight_bound`). `ChainBound`'s `Kⁿ` is
that count and it is not supplied here. -/
theorem nonbridging_sum_eq_zero (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ) :
    ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
        (fun q => ¬ Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
      pairTerm (Nc := Nc) bd p₀ pd β q = 0 := by
  classical
  set s : Finset (Finset Pq × Finset Pq) :=
    (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => ¬ Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd) with hs
  have hmem : ∀ q ∈ s, exchange bd p₀ pd q ∈ s := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [exchange_union]
    exact hq.2
  have hcancel : ∀ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
      + pairTerm (Nc := Nc) bd p₀ pd β (exchange bd p₀ pd q) = 0 := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    have hpdV : pd ∈ q.1 ∪ q.2 ∪ {p₀, pd} := by simp
    have hp0V : p₀ ∈ q.1 ∪ q.2 ∪ {p₀, pd} := by simp
    have hnotin : pd ∉ compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ := by
      intro hc; exact hq.2 (mem_compOf.mp hc).2
    have := pairTerm_add_pairFlip (Nc := Nc) bd p₀ pd hne β q.1 q.2
      (compOf bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
      (compOf_closed bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀)
      (self_mem_compOf hp0V) hnotin
    simpa [exchange] using this
  have hinj : ∀ x ∈ s, ∀ y ∈ s, exchange bd p₀ pd x = exchange bd p₀ pd y → x = y := by
    intro x _ y _ hxy
    rw [← exchange_exchange bd p₀ pd x, ← exchange_exchange bd p₀ pd y, hxy]
  have himg : s.image (exchange bd p₀ pd) = s := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact hmem r hr
    · intro q hq
      exact Finset.mem_image.mpr ⟨exchange bd p₀ pd q, hmem q hq, exchange_exchange bd p₀ pd q⟩
  have key : ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
      = - ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q := by
    calc ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q
        = ∑ q ∈ s.image (exchange bd p₀ pd), pairTerm (Nc := Nc) bd p₀ pd β q := by rw [himg]
      _ = ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β (exchange bd p₀ pd q) :=
          Finset.sum_image hinj
      _ = ∑ q ∈ s, (- pairTerm (Nc := Nc) bd p₀ pd β q) :=
          Finset.sum_congr rfl (fun q hq => by have := hcancel q hq; linarith)
      _ = - ∑ q ∈ s, pairTerm (Nc := Nc) bd p₀ pd β q := by simp
  linarith

#print axioms nonbridging_sum_eq_zero

/-- **NEGATIVE CONTROL — the separator hypothesis is refutable exactly where it must be.** If `p₀`
touches `p_d` there is NO separator at all, so `pairTerm_add_exchange` says nothing about a pair at
separation one. A lemma whose hypothesis could not fail would be vacuous; this is where it fails. -/
theorem no_separator_of_touch (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F A : Finset Pq)
    (ht : Touch bd p₀ pd) (h0 : p₀ ∈ A) (hd : pd ∉ A) :
    ¬ (∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r) := by
  intro hclosed
  exact hclosed p₀ (Finset.mem_inter.mpr ⟨by simp, h0⟩) pd
    (Finset.mem_sdiff.mpr ⟨by simp, hd⟩) ht

#print axioms no_separator_of_touch

/-- **A SURVIVING PAIR FACTORISES INTO A CORE AND AN OUTSIDE.** For a pair that DOES bridge, take `A`
containing both `p₀` and `p_d` and touch-closed in the pair's union. Then the term is the term of the
pair restricted to `A` — the connected core anchored on `p₀` and `p_d` — times the plain weights of
whatever lies outside it. The outside carries no observable and no cancellation; it is a vacuum
factor.

This is the companion of `pairTerm_add_exchange` on the other side of the split, and it is what turns
the surviving sum into a POLYMER sum: a sum over cores, each multiplied by a sum over outside sets
constrained not to touch its core. Bounding that constrained sum against `Z²` is the hard core of a
Mayer expansion and is NOT done here; what is done is the factorisation it starts from. -/
theorem pairTerm_eq_core_mul_outside (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (E F A : Finset Pq)
    (hclosed : ∀ p ∈ (E ∪ F ∪ {p₀, pd}) ∩ A, ∀ r ∈ (E ∪ F ∪ {p₀, pd}) \ A, ¬ Touch bd p r)
    (h0 : p₀ ∈ A) (hd : pd ∈ A) :
    pairTerm (Nc := Nc) bd p₀ pd β (E, F)
      = pairTerm (Nc := Nc) bd p₀ pd β (E ∩ A, F ∩ A)
        * (zw (Nc := Nc) bd β ∅ (E \ A) * zw (Nc := Nc) bd β ∅ (F \ A)) := by
  classical
  set V : Finset Pq := E ∪ F ∪ {p₀, pd} with hV
  set S : Finset Lk := (V ∩ A).biUnion (linkSupp bd) with hS
  set T : Finset Lk := (V \ A).biUnion (linkSupp bd) with hT
  have hST : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl'
    exact hclosed p hp r hr ⟨l, hlp, hlr⟩
  have hinS : ∀ W : Finset Pq, W ⊆ V ∩ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ S := by
    intro W hW p hp l hl
    rw [hS]; exact supp_subset_biUnion bd (V ∩ A) p (hW hp) l hl
  have hinT : ∀ W : Finset Pq, W ⊆ V \ A →
      ∀ p ∈ W, ∀ l ∈ (bd p).map Prod.fst, l ∈ T := by
    intro W hW p hp l hl
    rw [hT]; exact supp_subset_biUnion bd (V \ A) p (hW hp) l hl
  have hEV : E ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hFV : F ⊆ V := by rw [hV]; intro x hx; simp [hx]
  have hp0V : p₀ ∈ V := by rw [hV]; simp
  have hpdV : pd ∈ V := by rw [hV]; simp
  have hsubIn : ∀ W : Finset Pq, W ⊆ V → (W ∩ A) ⊆ V ∩ A := by
    intro W hW x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have hsubOut : ∀ W : Finset Pq, W ⊆ V → (W \ A) ⊆ V \ A := by
    intro W hW x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hW hx.1, hx.2⟩
  have gcore : ({p₀, pd} : Finset Pq) ⊆ V ∩ A := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
    · rw [Finset.mem_singleton] at hx'; subst hx'
      exact Finset.mem_inter.mpr ⟨hpdV, hd⟩
  have g0 : ({p₀} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hp0V, h0⟩
  have gd : ({pd} : Finset Pq) ⊆ V ∩ A := by
    intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_inter.mpr ⟨hpdV, hd⟩
  have gEA := hsubIn E hEV
  have gFA := hsubIn F hFV
  have gEc := hsubOut E hEV
  have gFc := hsubOut F hFV
  have gEm : (∅ : Finset Pq) ⊆ V ∩ A := Finset.empty_subset _
  have gEn : (∅ : Finset Pq) ⊆ V \ A := Finset.empty_subset _
  have hIO : ∀ X Y : Finset Pq, Disjoint (X ∩ A) (Y \ A) := by
    intro X Y
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  have hEu : E = (E ∩ A) ∪ (E \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hFu : F = (F ∩ A) ∪ (F \ A) := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  have hDr : ∀ W : Finset Pq, W = W ∪ ∅ := fun W => (Finset.union_empty W).symm
  have e1 := zw_split (Nc := Nc) bd β {p₀, pd} {p₀, pd} ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ gcore) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e2 := zw_split (Nc := Nc) bd β ∅ ∅ ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gEm) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  have e3 := zw_split (Nc := Nc) bd β {p₀} {p₀} ∅ E (E ∩ A) (E \ A) S T hST
    (hDr _) hEu (by simp) (hIO E E) (hinS _ g0) (hinS _ gEA) (hinT _ gEn) (hinT _ gEc)
  have e4 := zw_split (Nc := Nc) bd β {pd} {pd} ∅ F (F ∩ A) (F \ A) S T hST
    (hDr _) hFu (by simp) (hIO F F) (hinS _ gd) (hinS _ gFA) (hinT _ gEn) (hinT _ gFc)
  simp only [pairTerm]
  rw [e1, e2, e3, e4]
  ring

#print axioms pairTerm_eq_core_mul_outside

/-! ### The cancellation, applied to the Wilson connected correlation itself

`nonbridging_sum_eq_zero` is an identity about the double sum; below it is the same identity about
`WilsonBridge.wilsonCorrConn`, the object `Complete` consumes. The four Gibbs integrals expand over
activated subsets (`corrNum_eq_subset_sum`), their two products become one sum over PAIRS, and the
non-bridging pairs drop out. What is left is a sum over pairs whose union carries a touching chain
from `p₀` to `p_d`, divided by `Z²`.

The integrability side condition is the one `corrNum_eq_subset_sum` already carries, stated once for
all the observable/subset pairs the proof uses. -/

open scoped Classical in
/-- **THE CONNECTED CORRELATION IS A SUM OVER BRIDGING PAIRS ALONE.** Every pair of activated subsets
whose union fails to carry a touching chain from `p₀` to `p_d` contributes exactly nothing — at every
coupling, on a lattice of any size. This is the volume cancellation done, on the actual object.

WHAT THIS DOES NOT DO. It does not bound the surviving sum. `ChainBound` needs `Kⁿ` bridging
configurations at size `n` and a chain of length at least `d`; this supplies the reduction to that
count, and nothing more. -/
theorem wilsonCorrConn_eq_bridging_sum (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) (β : ℝ)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd
      = (∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
            (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
          pairTerm (Nc := Nc) bd p₀ pd β q)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
            (probHaar (MassGap.SUN.SU Nc)) β) ^ 2 := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  -- every Gibbs numerator is a finite sum over activated subsets
  have hz : ∀ D : Finset Pq,
      (∫ U, (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
          * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
          ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        = ∑ E : Finset Pq, zw (Nc := Nc) bd β D E := by
    intro D
    have h := corrNum_eq_subset_sum (Nc := Nc) bd β
      (fun U => ∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U) (fun E _ => hint D E)
    rw [Finset.powerset_univ] at h
    exact h
  have h2 : (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀, pd} E := by
    refine Eq.trans ?_ (hz {p₀, pd})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_pair hne]
  have hA : (∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀} E := by
    refine Eq.trans ?_ (hz {p₀})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_singleton]
  have hB : (∫ U, wilsonPlaqObs (N := Nc) bd pd U
        * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β {pd} E := by
    refine Eq.trans ?_ (hz {pd})
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_singleton]
  have hZ : (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
      = ∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E := by
    refine Eq.trans ?_ (hz ∅)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul]
  -- two sums over subsets become one sum over pairs
  have hprod : ∀ f g : Finset Pq → ℝ,
      (∑ E : Finset Pq, f E) * (∑ F : Finset Pq, g F)
        = ∑ q : Finset Pq × Finset Pq, f q.1 * g q.2 := by
    intro f g
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hnum : (∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀, pd} E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β ∅ F)
      - (∑ E : Finset Pq, zw (Nc := Nc) bd β {p₀} E)
        * (∑ F : Finset Pq, zw (Nc := Nc) bd β {pd} F)
      = ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
          (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
        pairTerm (Nc := Nc) bd p₀ pd β q := by
    rw [hprod, hprod, ← Finset.sum_sub_distrib]
    have hpt : ∀ q : Finset Pq × Finset Pq,
        zw (Nc := Nc) bd β {p₀, pd} q.1 * zw (Nc := Nc) bd β ∅ q.2
          - zw (Nc := Nc) bd β {p₀} q.1 * zw (Nc := Nc) bd β {pd} q.2
        = pairTerm (Nc := Nc) bd p₀ pd β q := fun q => rfl
    rw [Finset.sum_congr rfl (fun q _ => hpt q),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset Pq × Finset Pq))
        (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd)
        (pairTerm (Nc := Nc) bd p₀ pd β),
      nonbridging_sum_eq_zero bd p₀ pd hne β, add_zero]
  -- the connected correlation, written out over the same measure
  have hconn : MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd
      = (∫ U, (wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd pd U)
            * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
          / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
            ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
        - ((∫ U, wilsonPlaqObs (N := Nc) bd p₀ U
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))))
          * ((∫ U, wilsonPlaqObs (N := Nc) bd pd U
              * (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
            / (∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
              ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))) := rfl
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  have hne0 : (∑ E : Finset Pq, zw (Nc := Nc) bd β ∅ E) ≠ 0 := by
    rw [← hZ, ← hpart]; exact hZpos.ne'
  rw [hconn, hpart, h2, hA, hB, hZ, ← hnum]
  field_simp

#print axioms wilsonCorrConn_eq_bridging_sum

/-! ### SEPARATION FORCES SIZE — what makes the bridging sum decay in the lag at all

`wilsonCorrConn_eq_bridging_sum` is exact but says nothing about the LAG on its own: it would read the
same at separation one as at separation a hundred. What makes `d` an exponent is that a surviving
pair has to be BIG: its union must carry a chain of touching plaquettes from `p₀` to `p_d`, and if
`p_d` is more than `k` touch-steps from `p₀` then that chain needs `k` plaquettes strictly between
them, all of which lie in `E ∪ F`.

The proof is a level function rather than a path argument, which is what makes it short. Let
`lvl p` be the touch-distance from `p₀`. It is `0` at `p₀`, it rises by at most one across a touch,
and it exceeds `k` at `p_d`. Walking any reaching chain, the level starts at `0` and ends above `k`
with steps of at most `+1`, so it takes EVERY value `1, …, k` somewhere on the chain. Those `k`
witnesses have distinct levels, hence are distinct; none is `p₀` (level `0`) or `p_d` (level `> k`);
and all lie in the chain's ambient set. So `E ∪ F` has at least `k` elements.

The converse is proved too, and it is what makes the bound EXACT rather than merely true:
`mem_ball_of_bridging` says a bridging pair always puts `p_d` within `|E| + |F| + 1` steps, so the
hypothesis `p_d ∉ ball p₀ k` is false for every `k ≥ |E| + |F| + 1`. There is no slack to recover. -/

/-- Touching is symmetric — sharing a link is. -/
theorem touch_symm {bd : Pq → List (Lk × Bool)} {p q : Pq} (h : Touch bd p q) : Touch bd q p := by
  obtain ⟨l, hp, hq⟩ := h
  exact ⟨l, hq, hp⟩

open scoped Classical in
/-- The plaquettes within `n` touch-steps of `p₀`. No set `V` restricts it: this is the geometry of
`bd` alone, which is what the lag has to be measured against. -/
noncomputable def ball (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : ℕ → Finset Pq
  | 0 => {p₀}
  | n + 1 => ball bd p₀ n ∪ Finset.univ.filter (fun q => ∃ p ∈ ball bd p₀ n, Touch bd p q)

theorem self_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : ∀ n, p₀ ∈ ball bd p₀ n
  | 0 => Finset.mem_singleton_self p₀
  | n + 1 => Finset.mem_union_left _ (self_mem_ball bd p₀ n)

theorem ball_subset_succ (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (n : ℕ) :
    ball bd p₀ n ⊆ ball bd p₀ (n + 1) := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem ball_mono (bd : Pq → List (Lk × Bool)) (p₀ : Pq) {m n : ℕ} (h : m ≤ n) :
    ball bd p₀ m ⊆ ball bd p₀ n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (ball_subset_succ bd p₀ k)
      · rw [Nat.le_antisymm h hge]

theorem mem_ball_succ_of_touch (bd : Pq → List (Lk × Bool)) (p₀ : Pq) {p q : Pq} (n : ℕ)
    (hp : p ∈ ball bd p₀ n) (ht : Touch bd p q) : q ∈ ball bd p₀ (n + 1) := by
  classical
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hp, ht⟩⟩

/-- Reaching inside any `V` is reaching in the geometry: a chain confined to `V` is still a chain. -/
theorem exists_mem_ball_of_reach (bd : Pq → List (Lk × Bool)) {V : Finset Pq} {a b : Pq}
    (h : Reach bd V a b) : ∃ n, b ∈ ball bd a n := by
  induction h with
  | refl => exact ⟨0, self_mem_ball bd a 0⟩
  | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, mem_ball_succ_of_touch bd a n hn hbc.2.2⟩

open scoped Classical in
/-- The touch-distance from `p₀`, with a value off the component that no lemma below reads. -/
noncomputable def touchLvl (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) : ℕ :=
  if h : ∃ n, p ∈ ball bd p₀ n then Nat.find h else Fintype.card Pq + 1

theorem touchLvl_self (bd : Pq → List (Lk × Bool)) (p₀ : Pq) : touchLvl bd p₀ p₀ = 0 := by
  classical
  have hex : ∃ n, p₀ ∈ ball bd p₀ n := ⟨0, self_mem_ball bd p₀ 0⟩
  rw [touchLvl, dif_pos hex]
  exact Nat.le_zero.mp (Nat.find_le (self_mem_ball bd p₀ 0))

theorem mem_ball_touchLvl (bd : Pq → List (Lk × Bool)) (p₀ p : Pq)
    (hex : ∃ n, p ∈ ball bd p₀ n) : p ∈ ball bd p₀ (touchLvl bd p₀ p) := by
  classical
  rw [touchLvl, dif_pos hex]
  exact Nat.find_spec hex

/-- **The level rises by at most one across a touch.** Off the component both sides take the same
constant, and a touch cannot cross from the component to its outside — that is `touch_symm`. -/
theorem touchLvl_lipschitz (bd : Pq → List (Lk × Bool)) (p₀ : Pq) :
    ∀ p q : Pq, Touch bd p q → touchLvl bd p₀ q ≤ touchLvl bd p₀ p + 1 := by
  classical
  intro p q ht
  by_cases hp : ∃ n, p ∈ ball bd p₀ n
  · have hstep : q ∈ ball bd p₀ (touchLvl bd p₀ p + 1) :=
      mem_ball_succ_of_touch bd p₀ _ (mem_ball_touchLvl bd p₀ p hp) ht
    have hq : ∃ n, q ∈ ball bd p₀ n := ⟨_, hstep⟩
    rw [touchLvl, dif_pos hq]
    exact Nat.find_le hstep
  · have hq : ¬ ∃ n, q ∈ ball bd p₀ n := by
      rintro ⟨n, hn⟩
      exact hp ⟨n + 1, mem_ball_succ_of_touch bd p₀ n hn (touch_symm ht)⟩
    simp only [touchLvl, dif_neg hp, dif_neg hq]
    omega

theorem lt_touchLvl_of_not_mem_ball (bd : Pq → List (Lk × Bool)) (p₀ p : Pq) (k : ℕ)
    (hex : ∃ n, p ∈ ball bd p₀ n) (hk : p ∉ ball bd p₀ k) : k < touchLvl bd p₀ p := by
  classical
  rw [touchLvl, dif_pos hex]
  by_contra hcon
  exact hk (ball_mono bd p₀ (Nat.le_of_not_lt hcon) (Nat.find_spec hex))

/-- **A reaching chain realises every intermediate level.** The level starts at `0`, ends at
`lvl b`, and moves by at most `+1`, so it cannot skip a value. Each witness is `p₀` itself or lies in
the ambient set. -/
theorem exists_of_level_le (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (lvl : Pq → ℕ) (a : Pq)
    (hlip : ∀ p q : Pq, Touch bd p q → lvl q ≤ lvl p + 1) (h0 : lvl a = 0) {b : Pq}
    (h : Reach bd V a b) : ∀ j ≤ lvl b, ∃ c, (c = a ∨ c ∈ V) ∧ lvl c = j := by
  induction h with
  | refl =>
      intro j hj
      rw [h0] at hj
      exact ⟨a, Or.inl rfl, by omega⟩
  | tail _ hbc ih =>
      rename_i b' c' _
      intro j hj
      obtain ⟨_, hcV, ht⟩ := hbc
      have hlc := hlip b' c' ht
      rcases Nat.lt_or_ge j (lvl b' + 1) with hjb | hjb
      · exact ih j (by omega)
      · exact ⟨c', Or.inr hcV, by omega⟩

/-- **SEPARATION FORCES SIZE, in the level form.** If the level of `b` exceeds `k`, any chain from
`a` to `b` inside `V` forces `k` distinct members of `V` other than `a` and `b`. -/
theorem card_ge_of_reach_of_lvl (bd : Pq → List (Lk × Bool)) (V : Finset Pq) (lvl : Pq → ℕ)
    (a b : Pq) (k : ℕ) (hlip : ∀ p q : Pq, Touch bd p q → lvl q ≤ lvl p + 1) (h0 : lvl a = 0)
    (hk : k < lvl b) (hreach : Reach bd V a b) :
    k ≤ ((V.erase a).erase b).card := by
  classical
  have hsub : Finset.Icc 1 k ⊆ ((V.erase a).erase b).image lvl := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨c, hc, hlv⟩ := exists_of_level_le bd V lvl a hlip h0 hreach j (by omega)
    have hca : c ≠ a := by
      rintro rfl; rw [h0] at hlv; omega
    have hcb : c ≠ b := by
      rintro rfl; omega
    have hcV : c ∈ V := by
      rcases hc with rfl | hcV
      · exact absurd rfl hca
      · exact hcV
    exact Finset.mem_image.mpr
      ⟨c, Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, hcV⟩⟩, hlv⟩
  calc k = (Finset.Icc 1 k).card := by rw [Nat.card_Icc]; omega
    _ ≤ (((V.erase a).erase b).image lvl).card := Finset.card_le_card hsub
    _ ≤ ((V.erase a).erase b).card := Finset.card_image_le

#print axioms card_ge_of_reach_of_lvl

/-- **SEPARATION FORCES SIZE — the statement the expansion needs.** If `p_d` is more than `k`
touch-steps from `p₀`, every pair of activated subsets that BRIDGES them has `k ≤ |E| + |F|`.

Together with `wilsonCorrConn_eq_bridging_sum` this is what puts the lag in the exponent: at
separation `d` (`p_d ∉ ball p₀ (d−1)`) every surviving pair carries at least `d − 1` activated
plaquettes, each costing `e^{2|β|} − 1` (`subset_weight_bound`). It supplies the `qᵈ`; it does not
supply the `Kⁿ`. -/
theorem card_ge_of_bridging (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq) (k : ℕ)
    (hk : pd ∉ ball bd p₀ k)
    (hreach : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    k ≤ E.card + F.card := by
  classical
  have hex : ∃ n, pd ∈ ball bd p₀ n := exists_mem_ball_of_reach bd hreach
  have hlt : k < touchLvl bd p₀ pd := lt_touchLvl_of_not_mem_ball bd p₀ pd k hex hk
  have hcore := card_ge_of_reach_of_lvl bd (E ∪ F ∪ {p₀, pd}) (touchLvl bd p₀) p₀ pd k
    (touchLvl_lipschitz bd p₀) (touchLvl_self bd p₀) hlt hreach
  have hsub : (((E ∪ F ∪ {p₀, pd}).erase p₀).erase pd) ⊆ E ∪ F := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨hxd, hx0, hxV⟩ := hx
    rcases Finset.mem_union.mp hxV with hEF | hpair
    · exact hEF
    · rcases Finset.mem_insert.mp hpair with rfl | hx'
      · exact absurd rfl hx0
      · rw [Finset.mem_singleton] at hx'; exact absurd hx' hxd
  exact le_trans (le_trans hcore (Finset.card_le_card hsub)) (Finset.card_union_le E F)

#print axioms card_ge_of_bridging

/-- **NEGATIVE CONTROL — the bound is EXACT, with no slack.** A bridging pair always puts `p_d`
within `|E| + |F| + 1` touch-steps of `p₀`, so the hypothesis `p_d ∉ ball p₀ k` of
`card_ge_of_bridging` is FALSE for every `k ≥ |E| + |F| + 1`. The largest `k` the hypothesis can
carry is exactly `|E| + |F|`, which is what the conclusion returns: strengthening it to
`k + 1 ≤ |E| + |F|` would make it unsatisfiable rather than stronger. -/
theorem mem_ball_of_bridging (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (E F : Finset Pq)
    (hreach : Reach bd (E ∪ F ∪ {p₀, pd}) p₀ pd) :
    pd ∈ ball bd p₀ (E.card + F.card + 1) := by
  by_contra hcon
  have hbig := card_ge_of_bridging bd p₀ pd E F (E.card + F.card + 1) hcon hreach
  omega

#print axioms mem_ball_of_bridging

/-- **NEGATIVE CONTROL — touching kills the hypothesis at once.** At separation one there is nothing
to prove and the lemma says nothing: `p_d ∈ ball p₀ 1`, so `card_ge_of_bridging` can only be used
with `k = 0`. -/
theorem mem_ball_one_of_touch (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (ht : Touch bd p₀ pd) :
    pd ∈ ball bd p₀ 1 :=
  mem_ball_succ_of_touch bd p₀ 0 (self_mem_ball bd p₀ 0) ht

#print axioms mem_ball_one_of_touch

/-! ### The connectivity constant, DERIVED from `bd`

`ChainBound`'s `K` is "a connectivity constant of the lattice" and must be computed from the geometry,
never chosen. Everything below reads it off `bd`: `linkMult` counts how many plaquettes name a given
link, `touchNbrs` is the set of plaquettes touching a given one, and `touchDeg` is the largest such
set. No numeral appears in any of them.

`ball_card_le` is what makes the constant do work: the number of plaquettes within `n` touch-steps
grows at most like `(touchDeg + 1)ⁿ`, with no reference to the lattice's size. That is the
volume-independence `ChainBound` needs, on the geometric side. -/

open scoped Classical in
/-- How many plaquettes name the link `l` in their boundary word. -/
noncomputable def linkMult (bd : Pq → List (Lk × Bool)) (l : Lk) : ℕ :=
  (Finset.univ.filter (fun q : Pq => l ∈ linkSupp bd q)).card

open scoped Classical in
/-- The plaquettes touching `p`. -/
noncomputable def touchNbrs (bd : Pq → List (Lk × Bool)) (p : Pq) : Finset Pq :=
  Finset.univ.filter (fun q => Touch bd p q)

open scoped Classical in
theorem mem_touchNbrs {bd : Pq → List (Lk × Bool)} {p q : Pq} :
    q ∈ touchNbrs bd p ↔ Touch bd p q := by
  unfold touchNbrs
  simp

open scoped Classical in
/-- **THE DEGREE IS A SUM OVER THE PLAQUETTE'S OWN LINKS.** A plaquette can only touch through a link
it names, so its neighbour count is at most the total multiplicity of its own links. Both sides are
read off `bd`; nothing is chosen. -/
theorem touchNbrs_card_le (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (touchNbrs bd p).card ≤ ∑ l ∈ linkSupp bd p, linkMult bd l := by
  classical
  have hsub : touchNbrs bd p
      ⊆ (linkSupp bd p).biUnion (fun l => Finset.univ.filter (fun q : Pq => l ∈ linkSupp bd q)) := by
    intro q hq
    obtain ⟨l, hlp, hlq⟩ := mem_touchNbrs.mp hq
    exact Finset.mem_biUnion.mpr ⟨l, hlp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlq⟩⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)

#print axioms touchNbrs_card_le

open scoped Classical in
/-- The largest number of plaquettes any one plaquette touches — the connectivity constant of `bd`. -/
noncomputable def touchDeg (bd : Pq → List (Lk × Bool)) : ℕ :=
  Finset.univ.sup (fun p => (touchNbrs bd p).card)

open scoped Classical in
theorem touchNbrs_card_le_touchDeg (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (touchNbrs bd p).card ≤ touchDeg bd :=
  Finset.le_sup (f := fun p => (touchNbrs bd p).card) (Finset.mem_univ p)

open scoped Classical in
/-- **THE GEOMETRY GROWS AT MOST GEOMETRICALLY.** The `n`-step ball has at most `(touchDeg + 1)ⁿ`
plaquettes, whatever the size of the lattice. This is the volume-independent input a chain bound
needs from the geometry, and `touchDeg` in it is derived from `bd` by `touchNbrs_card_le`. -/
theorem ball_card_le (bd : Pq → List (Lk × Bool)) (p₀ : Pq) :
    ∀ n : ℕ, (ball bd p₀ n).card ≤ (touchDeg bd + 1) ^ n := by
  classical
  intro n
  induction n with
  | zero => simp [ball]
  | succ m ih =>
      have hstep : ball bd p₀ (m + 1)
          ⊆ ball bd p₀ m ∪ (ball bd p₀ m).biUnion (touchNbrs bd) := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq' | hq'
        · exact Finset.mem_union_left _ hq'
        · obtain ⟨p, hp, ht⟩ := (Finset.mem_filter.mp hq').2
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨p, hp, mem_touchNbrs.mpr ht⟩)
      have hbi : ((ball bd p₀ m).biUnion (touchNbrs bd)).card
          ≤ (ball bd p₀ m).card * touchDeg bd := by
        refine le_trans Finset.card_biUnion_le ?_
        calc ∑ p ∈ ball bd p₀ m, (touchNbrs bd p).card
            ≤ ∑ _p ∈ ball bd p₀ m, touchDeg bd :=
              Finset.sum_le_sum (fun p _ => touchNbrs_card_le_touchDeg bd p)
          _ = (ball bd p₀ m).card * touchDeg bd := by rw [Finset.sum_const, smul_eq_mul]
      have hcard : (ball bd p₀ (m + 1)).card ≤ (ball bd p₀ m).card * (touchDeg bd + 1) := by
        refine le_trans (Finset.card_le_card hstep) ?_
        refine le_trans (Finset.card_union_le _ _) ?_
        calc (ball bd p₀ m).card + ((ball bd p₀ m).biUnion (touchNbrs bd)).card
            ≤ (ball bd p₀ m).card + (ball bd p₀ m).card * touchDeg bd := by omega
          _ = (ball bd p₀ m).card * (touchDeg bd + 1) := by ring
      calc (ball bd p₀ (m + 1)).card ≤ (ball bd p₀ m).card * (touchDeg bd + 1) := hcard
        _ ≤ (touchDeg bd + 1) ^ m * (touchDeg bd + 1) := by
            exact Nat.mul_le_mul_right _ ih
        _ = (touchDeg bd + 1) ^ (m + 1) := by ring

#print axioms ball_card_le

open scoped Classical in
/-- **A SET IS CARRIED BY AT MOST `4^{|S|}` PAIRS.** Each side of a pair whose union is `S` is a
subset of `S`, so the pair sum over a fixed union costs at most `4^{|S|}` — a factor that a chain
bound absorbs into its own constant. This is the bridge from the double sum over PAIRS to a sum over
their unions, and it is the only part of the counting obligation that is volume-free without further
input. -/
theorem card_pairs_with_union_le (S : Finset Pq) :
    ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)).card
      ≤ 4 ^ S.card := by
  classical
  have hsub : ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S))
      ⊆ S.powerset ×ˢ S.powerset := by
    intro q hq
    have hu : q.1 ∪ q.2 = S := (Finset.mem_filter.mp hq).2
    refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_powerset.mpr ?_⟩
    · rw [← hu]; exact Finset.subset_union_left
    · rw [← hu]; exact Finset.subset_union_right
  calc ((Finset.univ : Finset (Finset Pq × Finset Pq)).filter (fun q => q.1 ∪ q.2 = S)).card
      ≤ (S.powerset ×ˢ S.powerset).card := Finset.card_le_card hsub
    _ = 2 ^ S.card * 2 ^ S.card := by rw [Finset.card_product, Finset.card_powerset]
    _ = 4 ^ S.card := by rw [← mul_pow]; norm_num

#print axioms card_pairs_with_union_le

end ZeroCoupling

/-! ### The constant EVALUATED on the lattice the flagship uses

`touchDeg` is derived from `bd` for any geometry. This section computes a bound on it for
`WilsonHypercubic.bd` — the periodic `dim`-dimensional lattice `WilsonBridge.corrClay` and hence
`Complete.readYMAt` are built on — and the point of the computation is WHAT IT DOES NOT CONTAIN: the
extent `n` does not appear. A link is named by at most `4·dim` plaquettes (four word slots times the
choice of the plane's other direction) and a plaquette names at most four links, so the connectivity
constant is at most `16·dim`, whatever the volume.

That is the whole reason a cluster expansion can beat the volume on the geometric side, and it is
DERIVED here rather than chosen: `4` is the length of the plaquette boundary word and `dim` is the
number of directions a plane's second axis can take.

HOW LOOSE IT IS. Measured by brute force on the actual `bd` (d, n over 2..4 × 3..5): the true
`touchDeg` is `16·dim − 14` — `18, 34, 50` at `dim = 2, 3, 4` — and independent of `n`, exactly as
proved. So at `dim = 4` the bound `64` over-counts the truth `50` by a factor `1.28`. It is an upper
bound and it is not vacuous. -/

section Hypercubic

open MassGap.WilsonHypercubic

variable {dim n : ℕ} [NeZero n]

/-- One periodic step back — the left inverse of `WilsonHypercubic.shift`. -/
def unshift (μ : Fin dim) (x : Site dim n) : Site dim n :=
  Function.update x μ (x μ - 1)

theorem unshift_shift (μ : Fin dim) (x : Site dim n) :
    unshift (n := n) μ (shift μ x) = x := by
  unfold unshift shift
  rw [Function.update_self, Function.update_idem]
  simp

open scoped Classical in
/-- **A LINK IS NAMED BY AT MOST `4·dim` PLAQUETTES.** Four word slots, and each slot fixes one of
the plane's two directions and the site, leaving only the other direction free. The extent `n` does
not enter. -/
theorem linkMult_bd_le (l : Link dim n) :
    linkMult (bd (d := dim) (n := n)) l ≤ 4 * dim := by
  classical
  obtain ⟨δ, y⟩ := l
  set g : Fin 4 × Fin dim → Plaq dim n := fun z =>
    if z.1 = 0 then ((δ, z.2), y)
    else if z.1 = 1 then ((z.2, δ), unshift (n := n) z.2 y)
    else if z.1 = 2 then ((δ, z.2), unshift (n := n) z.2 y)
    else ((z.2, δ), y) with hg
  have hsub : (Finset.univ.filter
        (fun q : Plaq dim n => (δ, y) ∈ linkSupp (bd (d := dim) (n := n)) q))
      ⊆ Finset.image g Finset.univ := by
    intro q hq
    obtain ⟨⟨μ, ν⟩, x⟩ := q
    have hmem := (Finset.mem_filter.mp hq).2
    simp only [linkSupp, bd, List.map_cons, List.map_nil, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
    refine Finset.mem_image.mpr ?_
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨(0, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · exact ⟨(1, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_shift]⟩
    · exact ⟨(2, ν), Finset.mem_univ _, by subst h1; subst h2; simp [hg, unshift_shift]⟩
    · exact ⟨(3, μ), Finset.mem_univ _, by subst h1; subst h2; simp [hg]⟩
    · simp at h
  unfold linkMult
  calc (Finset.univ.filter
        (fun q : Plaq dim n => (δ, y) ∈ linkSupp (bd (d := dim) (n := n)) q)).card
      ≤ (Finset.image g Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 × Fin dim)).card := Finset.card_image_le
    _ = 4 * dim := by simp

#print axioms linkMult_bd_le

/-- A hypercubic plaquette names at most four links — the length of its boundary word. -/
theorem linkSupp_bd_card_le (q : Plaq dim n) :
    (linkSupp (bd (d := dim) (n := n)) q).card ≤ 4 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  simp [bd]

open scoped Classical in
/-- **THE CONNECTIVITY CONSTANT OF THE HYPERCUBIC LATTICE, DERIVED AND VOLUME-FREE.** At most
`16·dim`, with no dependence on the extent `n`. Combined with `ball_card_le` this says the `n`-step
neighbourhood of a plaquette has at most `(16·dim + 1)ⁿ` members however large the lattice is. -/
theorem touchDeg_bd_le : touchDeg (bd (d := dim) (n := n)) ≤ 16 * dim := by
  classical
  refine Finset.sup_le (fun p _ => ?_)
  refine le_trans (touchNbrs_card_le (bd (d := dim) (n := n)) p) ?_
  calc ∑ l ∈ linkSupp (bd (d := dim) (n := n)) p, linkMult (bd (d := dim) (n := n)) l
      ≤ ∑ _l ∈ linkSupp (bd (d := dim) (n := n)) p, 4 * dim :=
        Finset.sum_le_sum (fun l _ => linkMult_bd_le l)
    _ = (linkSupp (bd (d := dim) (n := n)) p).card * (4 * dim) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * (4 * dim) := Nat.mul_le_mul_right _ (linkSupp_bd_card_le p)
    _ = 16 * dim := by ring

#print axioms touchDeg_bd_le

end Hypercubic

end MassGap.StrongCoupling

/-! ### THE POLYMER HARD CORE — the constrained outside sum, measured against `Z²`

`pairTerm_eq_core_mul_outside` factorises a surviving pair into a CORE anchored on `p₀` and `p_d`
and an OUTSIDE that carries no observable. Resumming the surviving double sum by its core turns
`wilsonCorrConn_eq_bridging_sum` into

    ρ_conn = ∑_{cores A}  (core term)  ·  ( ∑_{E' not touching A} ζ_∅(E') )² / Z²,

because the two outside sets are independent and each is constrained only by not touching `A`. The
UNCONSTRAINED version of that inner sum is exactly `Z`. So everything turns on one ratio, and it is
the ratio this section bounds:

    R(A) = ( ∑_{E ⊆ Ω(A)} ζ_∅(E) ) / Z,      Ω(A) = { p : p touches nothing in A }.

WHY IT IS THE WHOLE BALL GAME. `Z = ∫e^{−βS}` is exponentially small in the volume, so an absolute
bound on the numerator divided by `Z²` blows up with the lattice. The exchange involution removed the
non-bridging volume; `R(A)` is where the REST of it has to cancel. If `R(A)` grew with the lattice
the cluster route would give nothing in infinite volume.

IT CANCELS, AND ELEMENTARILY. The key is that the constrained sum is itself a partition function.
Summing `ζ_∅` over the subsets of `W` reassembles the product that was split:

    ∑_{E ⊆ W} ∫ ∏_{p∈E} w_p  =  ∫ ∏_{p∈W} (1 + w_p)  =  ∫ ∏_{p∈W} e^{−βφ_p}  =  Z_W,

the partition function of the SUB-SYSTEM carrying only `W`'s plaquettes (`subset_sum_eq_subPart`).
Both `Z_W` and `Z = Z_P` are integrals of strictly positive weights, so no cancellation is involved
and no absolute values are needed. Writing `S_P = S_W + S_{P∖W}` and using `φ ∈ [0,2]`,

    e^{−2β·|P∖W|} ≤ Z_P / Z_W ≤ 1        (β ≥ 0),

so `1 ≤ Z_W/Z ≤ e^{2β·|P∖W|}`. With `W = Ω(A)` the excluded set `P∖Ω(A)` is exactly the plaquettes
touching the core, of which there are at most `touchDeg bd · |A|` — a count read off the geometry by
`touchNbrs_card_le_touchDeg`, with no reference to the lattice's size. Hence

    1 ≤ R(A) ≤ exp(2β · touchDeg(bd) · |A|),

which depends on the CORE SIZE and on the connectivity constant, and NOT on the volume. That is the
statement `hard_core_ratio_le` and `hard_core_outside_sq_div_partition_sq_le` carry.

WHAT MUST BE ASSUMED ABOUT `β`, LOUDLY. The upper bound needs `β ≥ 0`, and so does the lower bound.
At `β < 0` each factor `e^{−βφ}` exceeds one, the sub-system's partition function is SMALLER than the
full one, and `R(A) ≤ 1` while the claimed bound `e^{2βK|A|}` is below one: BOTH inequalities fail,
and the finite-group control below reports them failing. Nothing beyond `β ≥ 0` is required —
there is no small-coupling threshold in this ratio, which is why it is stated without one.

A THRESHOLD APPEARS ONLY WHEN THIS IS COMBINED WITH THE COUNT, and it is derived rather than chosen.
Each activated plaquette costs `e^{2β} − 1` (`subset_weight_bound`), a connected core of `n`
plaquettes anchored at `p₀` is one of at most `(touchDeg + 1)ⁿ` (`ball_card_le`), and this section
contributes `e^{4β·touchDeg}` per core plaquette. The product

    q_eff(β) = (touchDeg + 1) · (e^{2β} − 1) · e^{4β·touchDeg}

is the per-plaquette rate of the core sum, and `hard_core_rate_lt_one_of_small` says it drops below
one on a neighbourhood of `β = 0` whose existence comes from `q_eff(0) = 0` and continuity — not from
a number. The core sum itself is NOT summed here: that is the counting obligation, and it is the one
place the volume could still return.

MEASURED. An exact-rational `Z₂` model (product uniform measure = product Haar; block independence
across link-disjoint sets holds verbatim) confirms all three things a theorem can hide: the
constrained and unconstrained sums genuinely differ (`Z_Ω/Z = 2.3703…` against `1`), the bound holds
on every core of every geometry tried, and it FAILS when either hypothesis is dropped — at `β < 0`,
and when the degree constant is replaced by one smaller than `touchDeg`. `R(A)` at a fixed core was
measured on rings of 5 to 14 plaquettes and moved from `2.36066` to `2.37037`, converging rather than
growing: the volume cancels. -/

namespace MassGap.StrongCoupling

section HardCore

open MeasureTheory MassGap.WilsonReal MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.LatticeGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]

/-- **The Boltzmann weight of the SUB-SYSTEM carrying only `W`'s plaquettes.** The whole lattice's
weight is the case `W = univ`; every constrained outside sum is one of these. -/
noncomputable def subBoltz (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) : ℝ :=
  ∏ p ∈ W, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))

/-- The sub-weight is `e^{−β S_W}` — the product of exponentials is the exponential of the partial
action. Every bound below is read off this form. -/
theorem subBoltz_eq_exp (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W U
      = Real.exp (-(β * ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U))) := by
  unfold subBoltz
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  simp

theorem subBoltz_pos (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) : 0 < subBoltz (Nc := Nc) bd β W U := by
  rw [subBoltz_eq_exp]; exact Real.exp_pos _

theorem measurable_subBoltz (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    Measurable (subBoltz (Nc := Nc) bd β W) := by
  refine Finset.measurable_prod _ (fun p _ => Real.measurable_exp.comp ?_)
  exact (measurable_const.mul
    (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p))).neg

/-- The partial action is nonnegative — each plaquette density is. -/
theorem partial_action_nonneg (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    0 ≤ ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) :=
  Finset.sum_nonneg (fun _ _ => wilsonDensity_nonneg hN _)

/-- The partial action is at most `2·|W|` — the Wilson density's range is `[0,2]`. This `2` is
`WilsonAction.wilsonDensity_le_two`, not a chosen scale. -/
theorem partial_action_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (W : Finset Pq)
    (U : Lk → MassGap.SUN.SU Nc) :
    ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) ≤ 2 * (W.card : ℝ) := by
  calc ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U) ≤ ∑ _p ∈ W, (2 : ℝ) :=
        Finset.sum_le_sum (fun p _ => wilsonDensity_le_two hN _)
    _ = 2 * (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **MORE PLAQUETTES, SMALLER WEIGHT** — at `β ≥ 0`. Adding plaquettes only adds nonnegative energy.
This is the lower half of the ratio bound, and it fails at `β < 0`. -/
theorem subBoltz_le_of_subset (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W' U ≤ subBoltz (Nc := Nc) bd β W U := by
  rw [subBoltz_eq_exp, subBoltz_eq_exp, Real.exp_le_exp]
  have hle : ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      ≤ ∑ p ∈ W', wilsonDensity (N := Nc) (wilsonHol bd p U) :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun p _ _ => wilsonDensity_nonneg hN _)
  nlinarith

/-- **AND NOT MUCH SMALLER.** Dropping `n` plaquettes costs at most `e^{2βn}`, because each carries at
most `2` of action. This is the upper half of the ratio bound; `2` is the density's range. -/
theorem subBoltz_le_mul (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') (U : Lk → MassGap.SUN.SU Nc) :
    subBoltz (Nc := Nc) bd β W U
      ≤ Real.exp (2 * β * ((W' \ W).card : ℝ)) * subBoltz (Nc := Nc) bd β W' U := by
  rw [subBoltz_eq_exp, subBoltz_eq_exp, ← Real.exp_add, Real.exp_le_exp]
  have hsplit : ∑ p ∈ W' \ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      + ∑ p ∈ W, wilsonDensity (N := Nc) (wilsonHol bd p U)
      = ∑ p ∈ W', wilsonDensity (N := Nc) (wilsonHol bd p U) := Finset.sum_sdiff h
  have hgap := partial_action_le hN bd (W' \ W) U
  nlinarith

/-- **THE SUB-SYSTEM'S PARTITION FUNCTION.** `Z_W = ∫ e^{−βS_W}`; the full `Z` is `W = univ`. -/
noncomputable def subPart (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) : ℝ :=
  ∫ U, subBoltz (Nc := Nc) bd β W U ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc)))

theorem integrable_subBoltz (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    Integrable (subBoltz (Nc := Nc) bd β W)
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  refine (integrable_const (Real.exp (2 * |β| * (Fintype.card Pq : ℝ)))).mono'
    (measurable_subBoltz bd β W).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [Real.norm_of_nonneg (subBoltz_pos bd β W U).le, subBoltz_eq_exp, Real.exp_le_exp]
  have h0 := partial_action_nonneg hN bd W U
  have h2 := partial_action_le hN bd W U
  have hW : (W.card : ℝ) ≤ (Fintype.card Pq : ℝ) := Nat.cast_le.mpr (Finset.card_le_univ W)
  have hb : -β ≤ |β| := neg_le_abs β
  have habs : (0 : ℝ) ≤ |β| := abs_nonneg β
  nlinarith

/-- The sub-partition function is strictly positive: the weight is bounded below by a positive
constant on a probability space. -/
theorem subPart_pos (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    0 < subPart (Nc := Nc) bd β W := by
  unfold subPart
  rw [integral_pos_iff_support_of_nonneg (fun U => (subBoltz_pos bd β W U).le)
      (integrable_subBoltz hN bd β W)]
  have hsupp : Function.support (subBoltz (Nc := Nc) bd β W) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (subBoltz_pos bd β W U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

theorem subPart_le_of_subset (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') :
    subPart (Nc := Nc) bd β W' ≤ subPart (Nc := Nc) bd β W :=
  integral_mono (integrable_subBoltz hN bd β W') (integrable_subBoltz hN bd β W)
    (fun U => subBoltz_le_of_subset hN bd hβ h U)

theorem subPart_le_mul (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    {W W' : Finset Pq} (h : W ⊆ W') :
    subPart (Nc := Nc) bd β W
      ≤ Real.exp (2 * β * ((W' \ W).card : ℝ)) * subPart (Nc := Nc) bd β W' := by
  unfold subPart
  have hmono := integral_mono (integrable_subBoltz hN bd β W)
    ((integrable_subBoltz hN bd β W').const_mul (Real.exp (2 * β * ((W' \ W).card : ℝ))))
    (fun U => subBoltz_le_mul hN bd hβ h U)
  rwa [integral_const_mul] at hmono

/-- A product of activated weights is integrable: it is measurable and bounded, and the measure is a
probability measure. Carried rather than assumed, so no hypothesis reaches the headline. -/
theorem integrable_wprod (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (E : Finset Pq) :
    Integrable (fun U => ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
  classical
  have hmeas : Measurable (fun U : Lk → MassGap.SUN.SU Nc =>
      ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))) :=
    Finset.measurable_prod _ (fun p _ => (measurable_wfun β).comp
      (measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU Nc) bd p)))
  refine (integrable_const (Real.exp (2 * |β|) ^ (Fintype.card Pq))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun U => ?_))
  rw [Real.norm_eq_abs, Finset.abs_prod]
  have hone : (1 : ℝ) ≤ Real.exp (2 * |β|) := Real.one_le_exp (by positivity)
  have hstep : ∀ p ∈ E, |wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
      ≤ Real.exp (2 * |β|) := by
    intro p _
    rw [wfun_apply]
    have := boltz_factor_bound (β := β) (wilsonDensity_nonneg hN (wilsonHol bd p U))
      (wilsonDensity_le_two hN (wilsonHol bd p U))
    linarith
  calc ∏ p ∈ E, |wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))|
      ≤ ∏ _p ∈ E, Real.exp (2 * |β|) := Finset.prod_le_prod (fun p _ => abs_nonneg _) hstep
    _ = Real.exp (2 * |β|) ^ E.card := by rw [Finset.prod_const]
    _ ≤ Real.exp (2 * |β|) ^ (Fintype.card Pq) :=
        pow_le_pow_right₀ hone (Finset.card_le_univ E)

/-- **THE CONSTRAINED OUTSIDE SUM IS A PARTITION FUNCTION.** Summing the activated weight over the
subsets of `W` reassembles `∏_{p∈W}(1 + w_p) = ∏_{p∈W} e^{−βφ_p}`: the outside sum over `W` IS the
sub-system's `Z_W`, exactly, at every coupling.

This is the whole reason the hard core is elementary here. `Z_W` is an integral of a strictly
positive weight, so the ratio `Z_W/Z` involves no cancellation, no Mayer resummation and no
convergence criterion — only the two pointwise bounds above.

DERIVED: the `1` split off each factor is the same `1` as in `boltz_eq_subset_sum`. -/
theorem subset_sum_eq_subPart (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (β : ℝ) (W : Finset Pq) :
    ∑ E ∈ W.powerset, zw (Nc := Nc) bd β ∅ E = subPart (Nc := Nc) bd β W := by
  classical
  have hzw : ∀ E : Finset Pq, zw (Nc := Nc) bd β ∅ E
      = ∫ U, ∏ p ∈ E, wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U))
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := by
    intro E
    unfold zw
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [Finset.prod_empty, one_mul]
  rw [Finset.sum_congr rfl (fun E _ => hzw E),
    ← integral_finsetSum _ (fun E _ => integrable_wprod hN bd β E)]
  unfold subPart
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  unfold subBoltz
  have hone : ∀ p : Pq, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)) + 1 := by
    intro p; rw [wfun_apply]; ring
  have hprod : (∏ p ∈ W, Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))))
      = ∏ p ∈ W, (wfun β (wilsonDensity (N := Nc) (wilsonHol bd p U)) + 1) :=
    Finset.prod_congr rfl (fun p _ => hone p)
  rw [hprod, Finset.prod_add]
  exact Finset.sum_congr rfl (fun E _ => by simp)

#print axioms subset_sum_eq_subPart

/-- The UNCONSTRAINED outside sum is `Z` itself: `subPart` at the full plaquette set is the Wilson
partition function. -/
theorem subPart_univ_eq_partition (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    subPart (Nc := Nc) bd β Finset.univ
      = (wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β := by
  have hpart : (wilsonSystem bd (wilsonDensity (N := Nc))).partition
        (probHaar (MassGap.SUN.SU Nc)) β
      = ∫ U, (wilsonSystem bd (wilsonDensity (N := Nc))).boltz β U
        ∂(Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))) := rfl
  rw [hpart]
  unfold subPart
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  rw [subBoltz_eq_exp]
  unfold System.boltz
  show Real.exp (-(β * ∑ p ∈ (Finset.univ : Finset Pq),
        wilsonDensity (N := Nc) (wilsonHol bd p U)))
      = Real.exp (-β * ∑ p, wilsonDensity (N := Nc) (wilsonHol bd p U))
  congr 1
  ring

#print axioms subPart_univ_eq_partition

/-- **THE CONSTRAINED SUM IS AT LEAST THE UNCONSTRAINED ONE** — at `β ≥ 0`. Removing plaquettes
removes nonnegative energy, so the constrained outside sum can only be larger than `Z`. Recorded
because it is what makes the upper bound the only thing that has to be proved, and because it is the
half that fails first at `β < 0`. -/
theorem one_le_outside_sum_div_partition (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (Ω : Finset Pq) :
    1 ≤ (∑ E ∈ Ω.powerset, zw (Nc := Nc) bd β ∅ E)
      / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β) := by
  have hpos : 0 < subPart (Nc := Nc) bd β Finset.univ := subPart_pos hN bd β _
  rw [subset_sum_eq_subPart hN bd β Ω, ← subPart_univ_eq_partition bd β, le_div_iff₀ hpos,
    one_mul]
  exact subPart_le_of_subset hN bd hβ (Finset.subset_univ Ω)

#print axioms one_le_outside_sum_div_partition

/-- **THE HARD CORE, BOUNDED BY WHAT THE CONSTRAINT EXCLUDES.** The constrained outside sum divided
by `Z` is at most `e^{2βn}`, where `n` bounds the number of plaquettes the constraint removes. The
volume does not appear: only `n` and the coupling.

This is the general form; `hard_core_ratio_le` instantiates `n` at the core's touch-neighbourhood.

DERIVED: `2` is the range of the Wilson plaquette density, so `2βn` is the most action `n` excluded
plaquettes can carry. `β ≥ 0` is REQUIRED and is not a smallness assumption — see the section
docstring for what fails without it. -/
theorem outside_sum_div_partition_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (Ω : Finset Pq) (n : ℕ) (hn : Ωᶜ.card ≤ n) :
    (∑ E ∈ Ω.powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
      ≤ Real.exp (2 * β * (n : ℝ)) := by
  classical
  have hpos : 0 < subPart (Nc := Nc) bd β Finset.univ := subPart_pos hN bd β _
  rw [subset_sum_eq_subPart hN bd β Ω, ← subPart_univ_eq_partition bd β, div_le_iff₀ hpos]
  have hcard : (((Finset.univ : Finset Pq) \ Ω).card : ℝ) ≤ (n : ℝ) := by
    have hEq : (Finset.univ : Finset Pq) \ Ω = Ωᶜ := (Finset.compl_eq_univ_sdiff Ω).symm
    rw [hEq]
    exact_mod_cast hn
  have hmono : Real.exp (2 * β * (((Finset.univ : Finset Pq) \ Ω).card : ℝ))
      ≤ Real.exp (2 * β * (n : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc subPart (Nc := Nc) bd β Ω
      ≤ Real.exp (2 * β * (((Finset.univ : Finset Pq) \ Ω).card : ℝ))
          * subPart (Nc := Nc) bd β Finset.univ :=
        subPart_le_mul hN bd hβ (Finset.subset_univ Ω)
    _ ≤ Real.exp (2 * β * (n : ℝ)) * subPart (Nc := Nc) bd β Finset.univ :=
        mul_le_mul_of_nonneg_right hmono hpos.le

#print axioms outside_sum_div_partition_le

open scoped Classical in
/-- **THE PLAQUETTES AN OUTSIDE SET MAY DRAW ON**: those touching nothing in the core `A`. This is
exactly the constraint `pairTerm_eq_core_mul_outside` leaves behind — `compOf_closed` says the core
is touch-closed in the pair's union, so the outside is confined to `outsideOf`. -/
noncomputable def outsideOf (bd : Pq → List (Lk × Bool)) (A : Finset Pq) : Finset Pq :=
  Finset.univ.filter (fun p => ∀ a ∈ A, ¬ Touch bd p a)

open scoped Classical in
/-- **WHAT THE CONSTRAINT EXCLUDES IS THE CORE'S NEIGHBOURHOOD, AND IT IS GEOMETRIC.** At most
`touchDeg bd · |A|` plaquettes are forbidden: each is a touch-neighbour of some core plaquette, and
`touchNbrs_card_le_touchDeg` bounds each core plaquette's neighbourhood by a constant read off `bd`.
The lattice's size does not enter. -/
theorem card_compl_outsideOf_le (bd : Pq → List (Lk × Bool)) (A : Finset Pq) :
    (outsideOf bd A)ᶜ.card ≤ touchDeg bd * A.card := by
  classical
  have hsub : (outsideOf bd A)ᶜ ⊆ A.biUnion (touchNbrs bd) := by
    intro p hp
    obtain ⟨a, ha, ht⟩ : ∃ a ∈ A, Touch bd p a := by
      by_contra hcon
      exact (Finset.mem_compl.mp hp)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun a ha ht => hcon ⟨a, ha, ht⟩⟩)
    exact Finset.mem_biUnion.mpr ⟨a, ha, mem_touchNbrs.mpr (touch_symm ht)⟩
  calc (outsideOf bd A)ᶜ.card ≤ (A.biUnion (touchNbrs bd)).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (touchNbrs bd a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, touchDeg bd :=
        Finset.sum_le_sum (fun a _ => touchNbrs_card_le_touchDeg bd a)
    _ = touchDeg bd * A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

#print axioms card_compl_outsideOf_le

open scoped Classical in
/-- **THE POLYMER HARD CORE — THE VOLUME CANCELS.** For every core `A`, the outside sum constrained
not to touch `A`, divided by the UNCONSTRAINED sum `Z`, lies between `1` and
`exp(2β · touchDeg(bd) · |A|)`.

Read the bound: it is a function of the CORE SIZE and the lattice's connectivity constant, and there
is no `Fintype.card Pq` in it. The rest of the volume — everything the exchange involution did not
already cancel — cancels here, exactly and without any expansion.

WHAT IT RESTS ON, and nothing more: `β ≥ 0`, the Wilson density's range `[0,2]`, and the geometric
degree. There is NO smallness assumption, no Kotecky–Preiss criterion, and no Mayer resummation; the
constrained sum is a partition function of a sub-system (`subset_sum_eq_subPart`) and the comparison
is pointwise.

WHAT IT DOES NOT DO. It bounds one factor of the core resummation. It does not sum over cores: that
needs the count of connected cores of each size (`ball_card_le` bounds the ball, not the cores) and
the per-plaquette weight (`subset_weight_bound`), and only their product carries a threshold in `β`.
-/
theorem hard_core_ratio_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β)
    (A : Finset Pq) :
    1 ≤ (∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
    ∧ (∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition (probHaar (MassGap.SUN.SU Nc)) β)
      ≤ Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) :=
  ⟨one_le_outside_sum_div_partition hN bd hβ (outsideOf bd A),
   outside_sum_div_partition_le hN bd hβ (outsideOf bd A) (touchDeg bd * A.card)
     (card_compl_outsideOf_le bd A)⟩

#print axioms hard_core_ratio_le

open scoped Classical in
/-- **THE SHAPE THE POLYMER SUM ACTUALLY CONSUMES.** `pairTerm_eq_core_mul_outside` leaves TWO
outside sets, each constrained by the same core, and the connected correlation carries `Z²` in its
denominator (`wilsonCorrConn_eq_bridging_sum`). So what multiplies each core term is the SQUARE of
the ratio above, and it is bounded by `exp(4β · touchDeg · |A|)` — still a function of the core size
alone. -/
theorem hard_core_outside_sq_div_partition_sq_le (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) {β : ℝ}
    (hβ : 0 ≤ β) (A : Finset Pq) :
    ((∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E)
        * ∑ F ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ F)
      / ((wilsonSystem bd (wilsonDensity (N := Nc))).partition
          (probHaar (MassGap.SUN.SU Nc)) β) ^ 2
      ≤ Real.exp (4 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) := by
  classical
  obtain ⟨hlo, hup⟩ := hard_core_ratio_le hN bd hβ A
  set S := ∑ E ∈ (outsideOf bd A).powerset, zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq : S * S / Z ^ 2 = S / Z * (S / Z) := by
    rw [div_mul_div_comm, pow_two]
  have hexp : Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ))
      * Real.exp (2 * β * ((touchDeg bd * A.card : ℕ) : ℝ))
      = Real.exp (4 * β * ((touchDeg bd * A.card : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsq, ← hexp]
  have hrnn : (0 : ℝ) ≤ S / Z := le_trans zero_le_one hlo
  exact mul_le_mul hup hup hrnn (Real.exp_pos _).le

#print axioms hard_core_outside_sq_div_partition_sq_le

/-! ### The threshold this creates, derived rather than pinned

The ratio bound carries no smallness assumption. A threshold in `β` appears only when it is
multiplied by the two things the core sum also pays — the per-plaquette Boltzmann weight
`e^{2β} − 1` (`subset_weight_bound`) and the geometric branching `touchDeg + 1` (`ball_card_le`) —
and the product is the rate below. It is `0` at `β = 0` and continuous, so it is below one on a
neighbourhood of zero whose existence is a consequence of the estimate and not a chosen number. -/

/-- **THE EFFECTIVE PER-PLAQUETTE RATE OF THE CORE SUM.** Branching times weight times the hard
core's own factor. Each of the three is derived: `K + 1` from `ball_card_le`, `e^{2β} − 1` from
`boltz_factor_bound`, `e^{4βK}` from `hard_core_outside_sq_div_partition_sq_le`. -/
noncomputable def hardCoreRate (K : ℕ) (β : ℝ) : ℝ :=
  ((K : ℝ) + 1) * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ))

theorem hardCoreRate_at_zero (K : ℕ) : hardCoreRate K 0 = 0 := by
  unfold hardCoreRate; simp

theorem continuous_hardCoreRate (K : ℕ) : Continuous (hardCoreRate K) := by
  unfold hardCoreRate
  fun_prop

/-- **A THRESHOLD EXISTS, AND IT IS THE ESTIMATE'S OWN.** The rate vanishes at `β = 0` and is
continuous, so some `b > 0` puts it below one on `[0, b)`. No numeral is chosen here and none could
be: `b` is whatever the geometry's `K` makes it. -/
theorem hard_core_rate_lt_one_of_small (K : ℕ) :
    ∃ b > 0, ∀ β : ℝ, 0 ≤ β → β < b → hardCoreRate K β < 1 := by
  have hlt : hardCoreRate K 0 < 1 := by rw [hardCoreRate_at_zero]; norm_num
  have ht : Filter.Tendsto (hardCoreRate K) (nhds 0) (nhds (hardCoreRate K 0)) :=
    (continuous_hardCoreRate K).continuousAt
  have hev : ∀ᶠ x in nhds (0 : ℝ), hardCoreRate K x < 1 := ht.eventually_lt_const hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun β hβ0 hβ => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hβ0]
  exact hβ

#print axioms hard_core_rate_lt_one_of_small

/-! ### What is left, stated so it cannot be mistaken for done

With the hard core bounded, the surviving sum is

    ρ_conn = ∑_{cores (X,Y)} pairTerm(X,Y) · R(A)²,   1 ≤ R(A) ≤ e^{2β·touchDeg·|A|},

and `|pairTerm(X,Y)| ≤ 4·(e^{2|β|}−1)^{|X|+|Y|}` by `subset_weight_bound` with the two plaquette
observables bounded by `2` each. Every factor in that expression is now volume-free EXCEPT the number
of cores at each size, which is the remaining obligation: how many touch-connected sets containing
`p₀` and `p_d` have `|X| + |Y| = n`. `ball_card_le` bounds the `n`-step BALL by `(touchDeg + 1)ⁿ`,
which is the right shape but is not the same count.

Nothing below the core count depends on the volume, and nothing above it has been assumed. -/

/-! ### Where the hard-core bound plugs in — and the one obligation it leaves

The ratio bound is worth nothing unless something consumes it, so this states exactly what it buys
and against which missing step. `pairTerm_eq_core_mul_outside` factorises each surviving pair; the
resummation that turns the double sum over PAIRS into a sum over CORES times the constrained outside
sum is `CoreResummation`, and it is NOT proved here. Given it, the hard-core bound converts a bound
on the cores alone into a bound on the connected correlation, with `Z²` fully discharged. -/

open scoped Classical in
/-- **THE OBLIGATION.** `CoreResummation` says the bridging sum regroups by core: some finite family
of cores, with an assignment `core` naming each one's touch-closed set, reproduces the bridging sum
with the outside sums factored out.

This is the bijection `(E,F) ↦ ((E∩A, F∩A), (E∖A, F∖A))` between bridging pairs and
cores × (outside pairs confined to `outsideOf A`). `pairTerm_eq_core_mul_outside` supplies the
summand identity and `compOf_closed` supplies the separator; what is missing is the reindexing of the
sum, which is a `Finset` bijection and nothing analytic.

VERIFIED BUT NOT PROVED. In an exact-rational `Z₂` model the regrouping reproduces the connected
numerator to the last digit on every geometry tried; it is stated here rather than assumed away
because a numerical check is not a proof. -/
def CoreResummation (bd : Pq → List (Lk × Bool)) (p₀ pd : Pq) (β : ℝ)
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq) : Prop :=
  ∑ q ∈ (Finset.univ : Finset (Finset Pq × Finset Pq)).filter
      (fun q => Reach bd (q.1 ∪ q.2 ∪ {p₀, pd}) p₀ pd),
    pairTerm (Nc := Nc) bd p₀ pd β q
  = ∑ c ∈ cores, pairTerm (Nc := Nc) bd p₀ pd β c
      * ((∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E)
        * ∑ F ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ F)

open scoped Classical in
/-- **`Z²` IS DISCHARGED.** Given the resummation, a bound on the CORES alone — each core term times
`e^{4β·touchDeg·|A|}`, with no partition function in it — bounds the connected correlation itself.

This is what the hard core was for. The exponentially small `Z²` that made a naive numerator bound
blow up with the lattice does not appear in the hypothesis: it has been cancelled against the
constrained outside sums, core by core, by `hard_core_outside_sq_div_partition_sq_le`.

What is left in the hypothesis is volume-free per core — `|pairTerm|` is bounded by
`subset_weight_bound` and the factor is bounded by the core's own size — so the only way the volume
can return is through the NUMBER of cores at each size, which is the counting obligation this file
has said all along is open. -/
theorem wilsonCorrConn_abs_le_of_coreResummation (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool))
    (p₀ pd : Pq) (hne : p₀ ≠ pd) {β : ℝ} (hβ : 0 ≤ β)
    (hint : ∀ D E : Finset Pq, Integrable
      (fun U => (∏ p ∈ D, wilsonPlaqObs (N := Nc) bd p U)
        * ∏ p ∈ E, (Real.exp (-(β * wilsonDensity (N := Nc) (wilsonHol bd p U))) - 1))
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU Nc))))
    (cores : Finset (Finset Pq × Finset Pq)) (core : Finset Pq × Finset Pq → Finset Pq)
    (hres : CoreResummation (Nc := Nc) bd p₀ pd β cores core) (M : ℝ)
    (hM : ∑ c ∈ cores, |pairTerm (Nc := Nc) bd p₀ pd β c|
            * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) ≤ M) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := Nc) bd p₀ β pd| ≤ M := by
  classical
  have hZpos : 0 < (wilsonSystem bd (wilsonDensity (N := Nc))).partition
      (probHaar (MassGap.SUN.SU Nc)) β := wilsonSystem_partition_pos hN bd β
  rw [wilsonCorrConn_eq_bridging_sum hN bd p₀ pd hne β hint, hres, Finset.sum_div]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum ?_) hM)
  intro c _
  set S := ∑ E ∈ (outsideOf bd (core c)).powerset, zw (Nc := Nc) bd β ∅ E with hSdef
  set Z := (wilsonSystem bd (wilsonDensity (N := Nc))).partition
    (probHaar (MassGap.SUN.SU Nc)) β with hZdef
  have hsq := hard_core_outside_sq_div_partition_sq_le hN bd hβ (core c)
  have hone := one_le_outside_sum_div_partition hN bd hβ (outsideOf bd (core c))
  have hSpos : 0 < S := by
    have h1 : 1 * Z ≤ S := (le_div_iff₀ hZpos).mp hone
    rw [one_mul] at h1
    exact lt_of_lt_of_le hZpos h1
  have hrnn : 0 ≤ S * S / Z ^ 2 := div_nonneg (by positivity) (by positivity)
  calc |pairTerm (Nc := Nc) bd p₀ pd β c * (S * S) / Z ^ 2|
      = |pairTerm (Nc := Nc) bd p₀ pd β c| * (S * S / Z ^ 2) := by
        rw [mul_div_assoc, abs_mul, abs_of_nonneg hrnn]
    _ ≤ |pairTerm (Nc := Nc) bd p₀ pd β c|
          * Real.exp (4 * β * ((touchDeg bd * (core c).card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

#print axioms wilsonCorrConn_abs_le_of_coreResummation

open scoped Classical in
/-- **NEGATIVE CONTROL — the constraint is REAL, so the ratio is not `Z/Z`.** A core plaquette that
names at least one link touches itself, so it is excluded from its own outside set. Hence
`outsideOf bd A` is a proper subset of the plaquettes whenever `A` is nonempty and its plaquettes
have boundary words, and the constrained and unconstrained sums genuinely differ.

Without this the whole section could be true and empty: if `outsideOf bd A` were everything, the
ratio would be `Z/Z = 1` and `hard_core_ratio_le` would say nothing about any lattice. Measured in an
exact-rational `Z₂` model the two sums differ by a factor `2.37` at `|A| = 1` on a ring, and that
factor converges rather than growing as the ring is enlarged. -/
theorem not_mem_outsideOf_self (bd : Pq → List (Lk × Bool)) (A : Finset Pq) {a : Pq} (ha : a ∈ A)
    (hne : (linkSupp bd a).Nonempty) : a ∉ outsideOf bd A := by
  classical
  intro hmem
  obtain ⟨l, hl⟩ := hne
  exact (Finset.mem_filter.mp hmem).2 a ha ⟨l, hl, hl⟩

#print axioms not_mem_outsideOf_self

end HardCore

end MassGap.StrongCoupling
