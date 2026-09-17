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
* the combinatorial half — that the connected correlation really is dominated by such a chain sum,
  which is where the VOLUME CANCELS — is stated as `ChainBound` and is NOT proved here.

The volume cancellation is the whole content of a cluster expansion and the reason a naive
perturbative bound fails: term by term the correction is `O(β · #plaquettes)`, which grows with the
lattice, and only the connected (subtracted) quantity has the volume factors cancel. Nothing in this
file shortcuts that.

WHERE THIS SITS IN THE EXISTING PROGRAMME. Two milestones toward nontrivial clustering are already
in the tree and this is the piece between them and the gap:

* `HaarMoments` — the SU(2) integration engine: `∫U_ij = 0`, Schur orthogonality
  `∫U_ij Ū_kl = ½δδ`, and the two-point form `∫tr(UA)tr(U*B) = ½tr(AB)`, all by explicit-element
  invariance with no Peter–Weyl. This is what evaluates ONE link's integral in a chain.
* `InteractingTwoPoint` — `sysInt`'s two plaquettes SHARE a link, and integrating it out gives
  `½tr(C₀C₁)`, generically nonzero, while the product of the marginals is `0`. That is the connected
  mechanism `⟨φ_p φ_q⟩_c ≠ 0` at separation ONE.

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

This is the cluster expansion's conclusion, and proving it is where the VOLUME CANCELS. Term by term
the correction to the product measure is `O(β · #plaquettes)` and grows with the lattice; only after
the connected subtraction do the volume factors cancel and leave a sum over chains anchored at `p₀`.
Nothing in this file establishes that, and no bound proved here implies it.

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

So `ChainBound` is not merely SUFFICIENT for the hypothesis `Complete.confinement_of_lag_decay`
consumes — it is that hypothesis, with the resummation done. -/
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

end ZeroCoupling

end MassGap.StrongCoupling
