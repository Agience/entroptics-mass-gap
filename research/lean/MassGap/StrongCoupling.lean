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
how many plaquettes meet a given one — so it carries no coupling and no volume. -/
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
open MassGap.CompactGauge

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq]

open scoped Classical in
/-- Extend a tuple on `S` to a full link configuration, with the identity outside `S`. The value
outside is immaterial: every use is guarded by a support hypothesis. -/
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

end ZeroCoupling

end MassGap.StrongCoupling
