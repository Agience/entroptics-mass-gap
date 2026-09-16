import Mathlib
import MassGap.Moment

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

end MassGap.StrongCoupling
