/-
# MassGap.WilsonBridge — plaquette correlations of the constructed Wilson ensemble, as `Moment.Read`s

`Complete.wilsonCorrAt` is `opaque`, so theorems about it quantify over an arbitrary nonnegative
sequence. This module defines constructed correlations instead, from `WilsonReal`'s ingredients —
`SU(Nc)` as Mathlib's `specialUnitaryGroup`, the Wilson density `wilsonDensity`, the product Haar
measure over links, and the ordered-loop holonomy — and packages them as `Moment.Read`s.

## The correlations

* `wilsonCorr bd p₀ β p` — the Gibbs expectation `⟨φ_{p₀} · φ_p⟩_β`, for an arbitrary boundary-word
  map `bd`, arbitrary rank and arbitrary coupling. `wilsonCorr_nonneg` and `wilsonCorr_le_four` are
  proved, not assumed.
* `wilsonCorrConn` — the same with the disconnected part `⟨φ_{p₀}⟩⟨φ_p⟩` subtracted. Its sign is not
  proved and is not available from the argument that gives `wilsonCorr_nonneg`.
* `wilsonCorrF`, `wilsonCorrConnF` — the same two for finsets of plaquettes in place of single ones,
  with `wilsonCorrF_singleton` and `wilsonCorrConnF_singleton` checking the alignment.

## The geometries

* `bdChain` — a periodic ladder of `N + 1` plaquettes with three link roles per rung.
  `bdChain_shares_link` shows consecutive plaquettes share a vertical link. `chainCorr`,
  `chainCorrConn` and `chainRead` are its correlations and read.
* `Site3`, `Link3`, `Plaq3`, `shift`, `bd3` — a periodic cubic lattice in three dimensions,
  plaquettes indexed by their normal. `bd3_link_not_private` shows the first link of a plaquette also
  occurs in the plaquette of normal `k + 2` at the same site. `corr3` is its connected correlation.
* `siteAtHyper`, `corrHyper` — the same connected correlation on `WilsonHypercubic`'s lattice, whose
  plaquettes carry both spanning directions and therefore exist in any dimension; `corrClay` is the
  instance at `d = 4`, `Nc = 3`, plane `(0, 1)`, lag along `2`.

## The reads and the chain

`wilsonRead` packages a `Fin (N+1)`-indexed `wilsonCorr` as a `Moment.Read N`, taking positivity of
the total weight as a hypothesis `hpos` rather than proving it.
`tension_lt_floor_of_cosAvg_wilson`, `wilson_correlation_decays` and `wilson_correlation_gap` are
`Moment.Read.tension_lt_floor_of_cosAvg`, `ZeroMode.correlation_decays_of_tension` and
`ZeroMode.correlation_gap_of_tension` at that read.

## Scope

The three chain theorems carry their inputs as hypotheses: the spectral form `hspec`, the positivity
`hcpos`, and the tension bound `htens`. None of the three is established here for any ensemble, and
their conclusions are about the mode family `∑ₖ wₖ λₖ^d` that `hspec` supplies, not about
`wilsonCorr` directly.
-/
import Mathlib
import MassGap.Moment
import MassGap.ZeroMode
import MassGap.WilsonReal
import MassGap.WilsonRead
import MassGap.WilsonHypercubic

namespace MassGap.WilsonBridge

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge
open MassGap.WilsonReal
open MeasureTheory Finset

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- The Gibbs expectation `⟨φ_{p₀} · φ_p⟩_β` of the product of two plaquette observables, against
the product Haar measure with the Wilson Boltzmann weight at coupling `β`.

`bd`, `Lk`, `Pq`, `Nc` and `β` are all arbitrary, subject only to `Lk` and `Pq` being finite, so no
geometry is built into the definition. `WilsonRead.wilsonCorrReal` is the two-plaquette instance.

Unconnected: the disconnected part is not subtracted. `wilsonCorrConn` is the connected form.

DERIVED: no numeral. Every constant is the caller's. -/
noncomputable def wilsonCorr (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
    (fun U => wilsonPlaqObs bd p₀ U * wilsonPlaqObs bd p U)

/-- `0 ≤ wilsonCorr bd p₀ β p`, for `Nc ≠ 0` and every `bd`, `p₀`, `β`, `p`. The integrand is a
product of two nonnegative plaquette densities (`wilsonPlaqObs_nonneg`) and the Gibbs state preserves
nonnegativity (`wilsonSystem_expect_nonneg`).

The correlation is unconnected, which is why the sign follows pointwise. `wilsonCorrConn` subtracts a
disconnected part and has no corresponding theorem.

DERIVED: `0` is the value `Nc` is required to differ from in `hN` — `wilsonDensity` normalises by
`Nc` — and the lower bound asserted of the correlation. -/
theorem wilsonCorr_nonneg (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    0 ≤ wilsonCorr (Nc := Nc) bd p₀ β p :=
  wilsonSystem_expect_nonneg hN bd β _
    (fun U => mul_nonneg (wilsonPlaqObs_nonneg hN bd p₀ U) (wilsonPlaqObs_nonneg hN bd p U))

/-- `wilsonCorr bd p₀ β p ≤ 4`, for `Nc ≠ 0`. Each plaquette density is at most `2`
(`wilsonPlaqObs_le_two`), so the product is at most `4`, and `wilsonSystem_expect_abs_le` carries a
uniform bound on an observable to a bound on its expectation.

Holds at every real `β`, including negative ones; the bound does not improve with `Nc`.

DERIVED: `0` is the value `Nc` is required to differ from in `hN`. `4` is `2 * 2`: `2` is
`wilsonPlaqObs_le_two`'s bound on one plaquette density, which is `1 − Re tr/Nc` at its largest, and
the correlation is a product of two of them. Neither is a chosen tolerance. -/
theorem wilsonCorr_le_four (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    wilsonCorr (Nc := Nc) bd p₀ β p ≤ 4 := by
  have hmeas : Measurable (fun U : (wilsonSystem bd (wilsonDensity (N := Nc))).Config =>
      wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U) :=
    (measurable_wilsonPlaqObs (N := Nc) bd p₀).mul (measurable_wilsonPlaqObs (N := Nc) bd p)
  have habs := wilsonSystem_expect_abs_le hN bd β
    (fun U => wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U) hmeas 4
    (fun U => by
      rw [abs_of_nonneg (mul_nonneg (wilsonPlaqObs_nonneg hN bd p₀ U)
        (wilsonPlaqObs_nonneg hN bd p U))]
      calc wilsonPlaqObs (N := Nc) bd p₀ U * wilsonPlaqObs (N := Nc) bd p U
          ≤ 2 * 2 := mul_le_mul (wilsonPlaqObs_le_two hN bd p₀ U)
              (wilsonPlaqObs_le_two hN bd p U) (wilsonPlaqObs_nonneg hN bd p U) (by norm_num)
        _ = 4 := by norm_num)
  exact le_trans (le_abs_self _) habs

/-! ### The correlation as a `Moment.Read`

`Moment.Read N` carries a nonnegative `Fin (N+1)`-indexed sequence of positive total weight.
`wilsonCorr_nonneg` supplies the first; the second is carried as the hypothesis `hpos`, which
`WilsonRead.sum_wilsonCorrReal_pos_of_haar` reduces to one Haar fact on the two-plaquette instance
and which no theorem here discharges. -/

/-- `wilsonCorr bd p₀ β` packaged as a `Moment.Read N`: the `ρ` field is that correlation, `hρ` is
`wilsonCorr_nonneg`, and `hpos` is the caller's.

The plaquette type is `Fin (N + 1)` here, so the lag index is a plaquette label; whether it is a
spatial separation depends on the `bd` supplied — `bdChain` and `bd3` are two choices, with
different answers.

DERIVED: `0` is the value `Nc` is required to differ from in `hN` and the strict lower bound on the
total weight in `hpos`. `1` in `Fin (N + 1)` is the number of plaquettes indexed, which
`Moment.Read N` fixes. The `Bool` in the boundary word's type carries orientation flags, not
numerals. The base point `p₀` is an argument, not a literal. -/
noncomputable def wilsonRead (hN : Nc ≠ 0) {N : ℕ} (bd : Fin (N + 1) → List (Lk × Bool))
    (p₀ : Fin (N + 1)) (β : ℝ)
    (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p) : Moment.Read N where
  ρ := fun p => wilsonCorr (Nc := Nc) bd p₀ β p
  hρ := fun p => wilsonCorr_nonneg hN bd p₀ β p
  hpos := hpos

@[simp] theorem wilsonRead_rho (hN : Nc ≠ 0) {N : ℕ} (bd : Fin (N + 1) → List (Lk × Bool))
    (p₀ : Fin (N + 1)) (β : ℝ) (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p) :
    (wilsonRead hN bd p₀ β hpos).ρ = fun p => wilsonCorr (Nc := Nc) bd p₀ β p := rfl

/-- If the cosine average of the read `wilsonRead hN bd p₀ β hpos` exceeds `3^{-1/4}`, then its
tension is below `(1/4) log 3`. The body is `Moment.Read.tension_lt_floor_of_cosAvg` at that read.

The hypothesis `hc` is about the read's own `p` and `θ` fields. Nothing here establishes it for any
`bd`, `β` or `Nc`; it is supplied by the caller.

DERIVED: `0` is the value `Nc` is required to differ from and the strict lower bound in `hpos`. `1`
in `Fin (N + 1)` is the number of plaquettes. `3` and the exponent `-(1)/4` spell the constant
`3^{-1/4}`, and `(1/4) * log 3` is its negated logarithm, so the `1`, `4` and `3` of the conclusion
are the same three numerals as in `hc`. All are `Moment.Read.tension_lt_floor_of_cosAvg`'s. -/
theorem tension_lt_floor_of_cosAvg_wilson (hN : Nc ≠ 0) {N : ℕ}
    (bd : Fin (N + 1) → List (Lk × Bool)) (p₀ : Fin (N + 1)) (β : ℝ)
    (hpos : 0 < ∑ p, wilsonCorr (Nc := Nc) bd p₀ β p)
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) <
      ∑ d, (wilsonRead hN bd p₀ β hpos).p d * Real.cos ((wilsonRead hN bd p₀ β hpos).θ d)) :
    (wilsonRead hN bd p₀ β hpos).tension < (1 / 4) * Real.log 3 :=
  Moment.Read.tension_lt_floor_of_cosAvg _ hc

/-- Given a finite mode family `w`, `lam` with `0 ≤ w k`, `0 ≤ lam k ≤ 1` on `s`, a spectral form
`hspec` writing `wilsonCorr (bd N) (p₀ N) β d` as `∑ₖ wₖ λₖ^d` at every aperture, and the two
eventual hypotheses `hcpos` and `htens` on the corresponding reads, the sequence
`d ↦ ∑ₖ wₖ λₖ^d` tends to `0`. The body is `ZeroMode.correlation_decays_of_tension`.

The conclusion is about the mode family, not about `wilsonCorr`: `hspec` is what connects them, and
it is a hypothesis. `hcpos` and `htens` hold eventually in `N`, not at every `N`.

DERIVED: `0` is the value `Nc` is required to differ from, the lower bound on each `w k` and each
`lam k`, the strict lower bound in `hpos` and `hcpos`, and the limit point. `1` is the upper bound on
each `lam k` — below it the powers decay, at it they do not — and the `+1` of `Fin (N + 1)`.
`(1/4) * log 3` in `htens` is the floor constant, `ZeroMode`'s. -/
theorem wilson_correlation_decays (hN : Nc ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (bd : (N : ℕ) → Fin (N + 1) → List (Lk × Bool)) (p₀ : (N : ℕ) → Fin (N + 1)) (β : ℝ)
    (hpos : ∀ N, 0 < ∑ p, wilsonCorr (Nc := Nc) (bd N) (p₀ N) β p)
    (hspec : ∀ (N : ℕ) (d : Fin (N + 1)),
      wilsonCorr (Nc := Nc) (bd N) (p₀ N) β d = ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).p d * Real.cos ((wilsonRead hN (bd N) (p₀ N) β (hpos N)).θ d))
    (htens : ∀ᶠ N in Filter.atTop,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).tension < (1 / 4) * Real.log 3) :
    Filter.Tendsto (fun d : ℕ => ∑ k ∈ s, w k * lam k ^ d) Filter.atTop (nhds 0) :=
  ZeroMode.correlation_decays_of_tension s w lam hw hlam hle
    (fun N => wilsonRead hN (bd N) (p₀ N) β (hpos N))
    (fun N => by funext d; exact hspec N d) hcpos htens

/-! ### A periodic ladder

`WilsonReal.bd2` puts its two plaquettes on disjoint link sets, so under the product Haar measure
their observables are independent and the correlation is constant in the lag.

`bdChain` is a periodic ladder at arbitrary aperture: `N + 1` plaquettes around a circle, three link
roles per rung (bottom, top, vertical), with plaquette `p` the loop `h_p · v_{p+1} · (h'_p)⁻¹ · v_p⁻¹`.
`bdChain_shares_link` proves that consecutive plaquettes share the vertical link `v_{p+1}`. -/

/-- The link type of the ladder: a role in `Fin 3` together with a rung in `Fin (N + 1)`. The three
roles are the bottom, top and vertical links of a rung.

DERIVED: `3` is the number of distinct link roles a rung of a ladder has; changing it would describe
a different graph. `1` in `Fin (N + 1)` is the number of rungs, matching the number of
plaquettes. -/
abbrev ChainLink (N : ℕ) : Type := Fin 3 × Fin (N + 1)

/-- The boundary word of the ladder: plaquette `p` is the four-letter loop
`(0, p) · (2, p+1) · (1, p)⁻¹ · (2, p)⁻¹`, that is `h_p · v_{p+1} · (h'_p)⁻¹ · v_p⁻¹`, with the
`Bool` recording orientation.

The rung index `p + 1` is `Fin (N + 1)` addition, so the ladder closes around.

DERIVED: `0`, `1` and `2` are the bottom, top and vertical link roles named in `ChainLink`, and `3`
their count. The `1` in `p + 1` is one rung, the ladder's periodic step; the `1` in `Fin (N + 1)` is
the number of rungs. The four entries are the four sides of a plaquette. No literal sets a scale. -/
def bdChain (N : ℕ) (p : Fin (N + 1)) : List (ChainLink N × Bool) :=
  [((0, p), true), ((2, p + 1), true), ((1, p), false), ((2, p), false)]

/-- The vertical link `(2, p + 1)` occurs in the boundary word of plaquette `p` and in that of
plaquette `p + 1`. Both by `simp [bdChain]`: it is the second entry of the first word and the fourth
entry of the second.

So consecutive plaquettes of the ladder share a link. The statement is about membership in the two
words and says nothing about the correlation between their observables.

DERIVED: `2` is the vertical link role from `ChainLink` and `3` the number of roles. The `1` in
`p + 1` is one rung, the ladder's periodic step, and the `1` in `Fin (N + 1)` is the number of
rungs. -/
theorem bdChain_shares_link (N : ℕ) (p : Fin (N + 1)) :
    ((2 : Fin 3), p + 1) ∈ (bdChain N p).map Prod.fst ∧
    ((2 : Fin 3), p + 1) ∈ (bdChain N (p + 1)).map Prod.fst := by
  constructor
  · simp [bdChain]
  · simp [bdChain]

/-- `wilsonCorr` on the ladder at base plaquette `0`: the lag-indexed unconnected correlation at
aperture `N` and rank `Nc`.

Unconnected, so `chainCorr_nonneg` holds but the disconnected part is still present.
`chainCorrConn` is the connected form.

DERIVED: `0` is the base plaquette against which the lag is measured; the ladder is periodic, so
every base point gives the same correlation and the choice is a labelling. `1` in `Fin (N + 1)` is
the number of plaquettes, `ChainLink`'s and `bdChain`'s. -/
noncomputable def chainCorr (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorr (Nc := Nc) (bdChain N) 0 β d

/-- `0 ≤ chainCorr Nc N β d`, for `Nc ≠ 0`. `wilsonCorr_nonneg` at the ladder's boundary word.

DERIVED: `0` is the value `Nc` is required to differ from, the base plaquette of `chainCorr`, and the
lower bound asserted. `1` in `Fin (N + 1)` is the number of plaquettes. -/
theorem chainCorr_nonneg (hN : Nc ≠ 0) (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    0 ≤ chainCorr Nc N β d :=
  wilsonCorr_nonneg hN _ _ _ _

/-! ### The connected correlation

`wilsonCorr` is `⟨φ_{p₀}·φ_p⟩`, and its nonnegativity follows pointwise because it is a product of
two nonnegative densities. That leaves the disconnected part `⟨φ_{p₀}⟩⟨φ_p⟩` in it, which does not
decay with the lag: at `β = 0` each factor is `1` by `WilsonRead.integral_plaqObs_eq_one`, so the
correlation is bounded below by a constant in the lag.

`wilsonCorrConn` subtracts that part. Its sign is not available from the pointwise argument, and no
 theorem here establishes it. -/

/-- `wilsonCorr bd p₀ β p` with the product of the two single-plaquette expectations subtracted: the
connected correlation.

No sign is proved of this definition. The argument giving `wilsonCorr_nonneg` does not apply, since
the subtraction is not pointwise.

DERIVED: no numeral. Every constant is the caller's. -/
noncomputable def wilsonCorrConn (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) : ℝ :=
  wilsonCorr (Nc := Nc) bd p₀ β p
    - (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd p₀)
      * (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd p)

/-- `wilsonCorr` with each single plaquette replaced by a `Finset` of them: the Gibbs expectation of
`(∏_{p ∈ Ao} φ_p) · (∏_{p ∈ Bo} φ_p)`. `wilsonCorrF_singleton` recovers `wilsonCorr` at
`Ao = {p₀}`, `Bo = {p}`.

`Ao` and `Bo` may overlap; nothing requires them disjoint.

DERIVED: no numeral. The empty product is `1` by `Finset.prod`'s own convention, not by a literal
here. -/
noncomputable def wilsonCorrF (bd : Pq → List (Lk × Bool)) (Ao : Finset Pq) (β : ℝ)
    (Bo : Finset Pq) : ℝ :=
  (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
    (fun U => (∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
      * ∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)

/-- `wilsonCorrF` with the product of the two finset expectations subtracted: the connected form for
finsets of plaquettes. `wilsonCorrConnF_singleton` recovers `wilsonCorrConn`.

A definition, not a bound: no inequality relating it to any expansion is stated here, and it has no
proved sign.

DERIVED: no numeral. -/
noncomputable def wilsonCorrConnF (bd : Pq → List (Lk × Bool)) (Ao : Finset Pq) (β : ℝ)
    (Bo : Finset Pq) : ℝ :=
  wilsonCorrF (Nc := Nc) bd Ao β Bo
    - (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (fun U => ∏ p ∈ Ao, wilsonPlaqObs (N := Nc) bd p U)
      * (wilsonSystem bd (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (fun U => ∏ p ∈ Bo, wilsonPlaqObs (N := Nc) bd p U)

/-- `wilsonCorrF bd {p₀} β {p} = wilsonCorr bd p₀ β p`: at singleton finsets the product collapses
to a single factor, by `simp`. The alignment check for the generalisation.

DERIVED: no numeral. -/
theorem wilsonCorrF_singleton (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    wilsonCorrF (Nc := Nc) bd {p₀} β {p} = wilsonCorr (Nc := Nc) bd p₀ β p := by
  unfold wilsonCorrF wilsonCorr
  simp

#print axioms wilsonCorrF_singleton

/-- `wilsonCorrConnF bd {p₀} β {p} = wilsonCorrConn bd p₀ β p`: the same collapse, applied to both
the joint term (via `wilsonCorrF_singleton`) and the two single-finset expectations.

DERIVED: no numeral. -/
theorem wilsonCorrConnF_singleton (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    wilsonCorrConnF (Nc := Nc) bd {p₀} β {p} = wilsonCorrConn (Nc := Nc) bd p₀ β p := by
  unfold wilsonCorrConnF wilsonCorrConn
  rw [wilsonCorrF_singleton]
  simp

#print axioms wilsonCorrConnF_singleton

/-- `wilsonCorrConn` on the ladder at base plaquette `0`: the lag-indexed connected correlation.

No sign is proved of it, unlike `chainCorr`.

DERIVED: `0` is the base plaquette, immaterial by the ladder's periodicity, exactly as in
`chainCorr`. `1` in `Fin (N + 1)` is the number of plaquettes. -/
noncomputable def chainCorrConn (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bdChain N) 0 β d

/-! ### A three-dimensional lattice, where no plaquette owns a private link

In the ladder, plaquette `p` owns the links `(0, p)` and `(1, p)`, which occur in no other
plaquette's boundary word. Under the product Haar measure such a link can be integrated out first,
and left-translation by it carries that plaquette's holonomy through Haar.

The geometry below has no such link: `bd3_link_not_private` exhibits, for each plaquette, a second
plaquette containing its first link. On a periodic cubic lattice in `D` dimensions every link lies in
`2(D − 1)` plaquettes, so this needs `D ≥ 3`. -/

/-- The site type of a periodic cubic lattice in three dimensions: one `Fin n` coordinate per
direction.

CHOSEN: three dimensions. Three is the smallest dimension in which no plaquette owns a private link,
which is what `bd3_link_not_private` establishes and the ladder fails. It is not the dimension of the
Yang–Mills problem, which is four, and nothing proved on this geometry is transported to `d = 4`;
`corrHyper` is the dimension-general construction and `corrClay` its four-dimensional instance. Every
`Fin 3` below inherits this choice and is not an independent one. -/
abbrev Site3 (n : ℕ) : Type := Fin 3 → Fin n

/-- The link type of the three-dimensional lattice: a direction in `Fin 3` and a base site.

DERIVED: `3` is the dimension chosen at `Site3`, appearing here as the direction index and inside
`Site3 n`; it is not a second choice. -/
abbrev Link3 (n : ℕ) : Type := Fin 3 × Site3 n

/-- The plaquette type of the three-dimensional lattice: a normal direction in `Fin 3` and a base
site. In three dimensions a plane is fixed by its normal; `bd3` reads the plane of normal `k` as
spanned by `k + 1` and `k + 2`.

The type is identical to `Link3 n`; what distinguishes them is how `bd3` reads the first component.

DERIVED: `3` is the dimension chosen at `Site3`, appearing as the normal's index type and inside
`Site3 n`. The offsets `1` and `2` to the two spanning directions belong to `bd3`, not to this type,
which carries no other numeral. -/
abbrev Plaq3 (n : ℕ) : Type := Fin 3 × Site3 n

/-- `Function.update x μ (x μ + 1)`: translate a site by one step in direction `μ`. The coordinate
lives in `Fin n`, so the step wraps and the lattice is periodic; `[NeZero n]` is what makes `Fin n`
nonempty.

DERIVED: `1` is one lattice step — the definition of a neighbour, not a length. `3` is the dimension
chosen at `Site3`. -/
def shift {n : ℕ} [NeZero n] (μ : Fin 3) (x : Site3 n) : Site3 n :=
  Function.update x μ (x μ + 1)

/-- The boundary word of the three-dimensional plaquette of normal `k` at site `x`: the four-letter
loop `U_{k+1}(x) · U_{k+2}(x + ê_{k+1}) · U_{k+1}(x + ê_{k+2})⁻¹ · U_{k+2}(x)⁻¹`, the `Bool`
recording orientation.

Direction arithmetic is in `Fin 3`, so `k + 1` and `k + 2` wrap and are the two directions other
than `k`.

DERIVED: `1` and `2` are the offsets from the normal to the two in-plane directions, forced by `k`
being the normal itself. `3` is the dimension chosen at `Site3`. The four entries are the four sides
of one plaquette. -/
def bd3 {n : ℕ} [NeZero n] (q : Plaq3 n) : List (Link3 n × Bool) :=
  let k := q.1; let x := q.2
  [((k + 1, x), true), ((k + 2, shift (k + 1) x), true),
   ((k + 1, shift (k + 2) x), false), ((k + 2, x), false)]

/-- The link `(k + 1, x)` occurs in the boundary word of the plaquette of normal `k` at `x`, occurs
in the boundary word of the plaquette of normal `k + 2` at the same site, and those two plaquettes
are distinct because `k + 2 ≠ k` in `Fin 3`.

In the second word it is the fourth entry, since `(k + 2) + 2 = k + 1` in `Fin 3`; both that identity
and `k + 2 ≠ k` are settled by `decide` over the three directions.

A membership statement about two boundary words. It exhibits one such pair for one link of each
plaquette; it does not quantify over all links.

DERIVED: `1` and `2` are `bd3`'s offsets from the normal to the two in-plane directions, and `3` is
the dimension chosen at `Site3`. The fact that `(k + 2) + 2 = k + 1` holds is what makes `2` the
offset that finds a second plaquette, and it is particular to three directions. -/
theorem bd3_link_not_private {n : ℕ} [NeZero n] (k : Fin 3) (x : Site3 n) :
    ((k + 1, x) ∈ (bd3 (k, x)).map Prod.fst) ∧
    ((k + 1, x) ∈ (bd3 (k + 2, x)).map Prod.fst) ∧ (k + 2 ≠ k) := by
  -- both are statements about `Fin 3` alone, decided by exhausting the three directions
  have h : (k + 2) + 2 = k + 1 := by revert k; decide
  have hne : k + 2 ≠ k := by revert k; decide
  refine ⟨by simp [bd3], ?_, hne⟩
  -- in the plaquette of normal `k+2` the fourth entry is `U_{(k+2)+2}(x) = U_{k+1}(x)`
  simp [bd3, h]

/-- `Function.update (fun _ => 0) μ d`: the site whose `μ` coordinate is `d` and whose other
coordinates are `0`.

DERIVED: `0` is the origin of a periodic lattice, so displacing from it is the same as displacing
from anywhere; it is also the value of every coordinate other than `μ`. `3` is the dimension chosen
at `Site3`. -/
def siteAt {n : ℕ} [NeZero n] (μ : Fin 3) (d : Fin n) : Site3 n :=
  Function.update (fun _ => 0) μ d

/-- `wilsonCorrConn` on the three-dimensional lattice: both plaquettes have normal `0`, one is at the
origin and the other at `siteAt 0 d`, so they are displaced by `d` steps along direction `0`, which
is the normal and therefore transverse to their common plane.

Connected, so no sign is proved of it. The geometry has no plaquette owning a private link
(`bd3_link_not_private`), unlike `bdChain`.

DERIVED: no literal sets a scale. `0` is the normal direction shared by both plaquettes, the
direction the lag runs along, and the origin they are displaced from — immaterial by periodicity and
by the freedom to name the axes. `3` is the dimension chosen at `Site3`, and `1` in `Fin (N + 1)` is
the number of lags, with `N + 1` also serving as the extent. `1` and `2` inside the boundary word
are `bd3`'s in-plane offsets. -/
noncomputable def corr3 (Nc N : ℕ) (β : ℝ) (d : Fin (N + 1)) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bd3 (n := N + 1)) (0, fun _ => 0) β (0, siteAt 0 d)

/-! ### The same correlation in any dimension

`corr3` lives on `Site3`, whose plaquettes are indexed by a normal, which determines a plane only in
three dimensions. `WilsonHypercubic.sysWilson`'s plaquettes carry both spanning directions and so
exist in any dimension, and it is the lattice `WilsonGauge`'s measure is built on.

`corrHyper` is the same connected correlation there: `wilsonCorrConn` is already general in the
boundary-word map, so this is that map instantiated at `WilsonHypercubic.bd` rather than at `bd3`.

`WilsonHypercubic.link_not_private` is the private-link statement in any dimension `d ≥ 3`, of which
`bd3_link_not_private` is the three-dimensional case. -/

/-- `Function.update (fun _ => 0) μ lag` on `WilsonHypercubic.Site d n`: the site whose `μ`
coordinate is `lag` and whose other coordinates are `0`. The `siteAt` of the dimension-general
lattice.

`d` is a variable, so the direction `μ` is an argument rather than a literal.

DERIVED: `0` is the origin of a periodic lattice, so displacing from it is the same as displacing
from anywhere; it is also the value of every coordinate other than `μ`. -/
def siteAtHyper {d n : ℕ} [NeZero n] (μ : Fin d) (lag : Fin n) :
    MassGap.WilsonHypercubic.Site d n :=
  Function.update (fun _ => 0) μ lag

/-- `wilsonCorrConn` on `WilsonHypercubic`'s `d`-dimensional periodic lattice: both plaquettes span
the ordered plane `(μ, ν)`, one based at the origin and the other at `siteAtHyper τ lag`.

The three directions `μ`, `ν`, `τ` are arguments. Nothing in the statement requires them distinct, so
whether `τ` is transverse to the plane — and hence whether `lag` is a separation rather than an
in-plane offset — is the caller's to arrange, and needs `d ≥ 3` to be possible at all. Connected, so
no sign is proved of it.

DERIVED: no literal sets a scale. The directions are the caller's and which two span the plane is a
naming freedom; `0` is the origin the first plaquette sits at and the value of every coordinate other
than `τ` in the second, immaterial by periodicity. -/
noncomputable def corrHyper {d : ℕ} (Nc n : ℕ) [NeZero n] (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) : ℝ :=
  wilsonCorrConn (Nc := Nc) (MassGap.WilsonHypercubic.bd (d := d) (n := n))
    ((μ, ν), fun _ => 0) β ((μ, ν), siteAtHyper τ lag)

/-- `0 ≤ wilsonCorr` at `corrHyper`'s two plaquettes, for `Nc ≠ 0`. `wilsonCorr_nonneg` applied
directly, since it never inspects the geometry.

About the unconnected correlation. `corrHyper` itself is connected and has no corresponding
statement.

DERIVED: `0` is the value `Nc` is required to differ from, the origin the first plaquette sits at and
the other coordinates of the second, and the lower bound asserted. -/
theorem corrHyper_unconnected_nonneg {d : ℕ} (hN : Nc ≠ 0) (n : ℕ) [NeZero n]
    (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) :
    0 ≤ wilsonCorr (Nc := Nc) (MassGap.WilsonHypercubic.bd (d := d) (n := n))
          ((μ, ν), fun _ => 0) β ((μ, ν), siteAtHyper τ lag) :=
  wilsonCorr_nonneg hN _ _ _ _

#print axioms corrHyper_unconnected_nonneg

/-- `corrHyper` at `d = 4`, `Nc = 3`, plane `(0, 1)` and lag direction `2`: the connected plaquette
correlation of four-dimensional `SU(3)` Wilson theory at extent `n`, on the lattice `WilsonGauge`'s
measure is built on.

The lag direction `2` differs from both plane directions, so here the lag is transverse to the
plane; `corrHyper` leaves that to the caller and this instance settles it.

DERIVED: `4` is the spacetime dimension and `3` the colour rank of `SU(3)` — the problem's data, not
choices made here. `0` and `1` are the two directions spanning the plane and `2` the transverse
direction the lag runs along; which three of `Fin 4` are used is a naming freedom, and only their
distinctness matters. `n` is the periodic extent and stays the caller's. -/
noncomputable def corrClay (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) : ℝ :=
  corrHyper (d := 4) 3 n 0 1 2 β lag

#print axioms corrClay

/-- `wilsonRead` at the ladder's boundary word and base plaquette `0`: `chainCorr Nc N β` as a
`Moment.Read N`. Positivity of the total weight is the carried hypothesis `hpos`.

Built from the unconnected `chainCorr`, since `Moment.Read` requires a nonnegative sequence and
`chainCorrConn` has no proved sign.

DERIVED: `0` is the value `Nc` is required to differ from, the base plaquette of the periodic ladder
— immaterial by its periodicity, as in `chainCorr` — and the strict lower bound in `hpos`. `1` in
`Fin (N + 1)` is the number of plaquettes. -/
noncomputable def chainRead (hN : Nc ≠ 0) (N : ℕ) (β : ℝ)
    (hpos : 0 < ∑ d, chainCorr Nc N β d) : Moment.Read N :=
  wilsonRead hN (bdChain N) 0 β hpos

/-- The same hypotheses as `wilson_correlation_decays`, with a stronger conclusion: there is a
`ρ ∈ [0, 1)` with `∑ₖ wₖ λₖ^d ≤ (∑ₖ wₖ) · ρ^d` for every `d : ℕ`. The body is
`ZeroMode.correlation_gap_of_tension`.

A geometric envelope with a positive rate `−log ρ`, where `wilson_correlation_decays` gives only
convergence to `0`, which a power law also satisfies.

What supplies the rate is the finiteness of the mode family `s` in `hspec`: `ρ` is bounded away from
`1` because finitely many `λₖ` below `1` have a largest. The bound is over the mode family, and
`hspec` is what ties it to `wilsonCorr`.

DERIVED: `0` is the value `Nc` is required to differ from, the lower bound on each `w k` and each
`lam k`, the strict lower bounds in `hpos` and `hcpos`, and the lower bound on `ρ`. `1` is the upper
bound on each `lam k`, the strict upper bound on `ρ` that makes the envelope decay, and the `+1` of
`Fin (N + 1)`. `(1/4) * log 3` in `htens` is the floor constant, `ZeroMode`'s. -/
theorem wilson_correlation_gap (hN : Nc ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (bd : (N : ℕ) → Fin (N + 1) → List (Lk × Bool)) (p₀ : (N : ℕ) → Fin (N + 1)) (β : ℝ)
    (hpos : ∀ N, 0 < ∑ p, wilsonCorr (Nc := Nc) (bd N) (p₀ N) β p)
    (hspec : ∀ (N : ℕ) (d : Fin (N + 1)),
      wilsonCorr (Nc := Nc) (bd N) (p₀ N) β d = ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).p d * Real.cos ((wilsonRead hN (bd N) (p₀ N) β (hpos N)).θ d))
    (htens : ∀ᶠ N in Filter.atTop,
      (wilsonRead hN (bd N) (p₀ N) β (hpos N)).tension < (1 / 4) * Real.log 3) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ d : ℕ, ∑ k ∈ s, w k * lam k ^ d ≤ (∑ k ∈ s, w k) * ρ ^ d :=
  ZeroMode.correlation_gap_of_tension s w lam hw hlam hle
    (fun N => wilsonRead hN (bd N) (p₀ N) β (hpos N))
    (fun N => by funext d; exact hspec N d) hcpos htens

section Audit
#print axioms wilson_correlation_gap
#print axioms bdChain_shares_link
#print axioms bd3_link_not_private
#print axioms chainCorr_nonneg
#print axioms chainRead
#print axioms wilsonCorr_nonneg
#print axioms wilsonRead
#print axioms tension_lt_floor_of_cosAvg_wilson
#print axioms wilson_correlation_decays
end Audit

end MassGap.WilsonBridge
