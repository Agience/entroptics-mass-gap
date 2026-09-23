import Mathlib
import MassGap.Complete
import MassGap.ContactFloor

/-!
# MassGap.InfiniteVolume — the thermodynamic limit of the Clay correlation

## The limit is in one variable

`MassGap.wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β` lives on
`WilsonHypercubic.bd (d := 4) (n := N + 1)`, whose site type is `Fin 4 → Fin (N + 1)`
(`clay_site_def`). The extent is `N + 1` in every one of the four directions at once, so there is no
separate spatial extent, temporal extent or box to send to infinity independently: `N → ∞` IS the
infinite-volume limit of this object, and the plaquette count `16(N+1)⁴` diverges with it
(`clay_plaq_card`, `clay_volume_tendsto_atTop`). A6 is therefore a limit in one variable.

## The sequence

`Fin (N + 1)` changes with `N`, so a lag has to be named by a natural number to be followed across
extents. `corrLag k β N` does that, clamping the index to `min k N` so the sequence is total in `N`.
For `k ≤ N` the clamp does nothing (`corrLag_index_val`) and for `2k ≤ N` the circle distance of the
index is `k` (`circLag_cast`), so at all large `N` the entry really is the lag-`k` correlation of the
extent-`(N+1)` lattice.

## What is proved

* `wilsonCorrConn_abs_le_four` / `wilsonCorrAt_abs_le_four` — `|ρ_N(β,d)| ≤ 4` at every extent,
  every real coupling and every lag, with no hypothesis. The Wilson plaquette observable takes
  values in `[0,2]` and the Gibbs state is a probability state, so the unconnected correlation lies
  in `[0,4]` and the product of the two one-point functions lies in `[0,4]`. Nothing in the constant
  refers to the extent.
* `exists_subseq_tendsto` — consequently, at each lag and each coupling the sequence of finite-volume
  values has a convergent subsequence.
* `exists_filter_tendsto_all_lags` / `exists_subseq_tendsto_all_lags` — one subsequence along which
  every lag converges simultaneously, so the whole finite-volume correlation function converges
  pointwise to a limit function `L : ℕ → ℝ`. This is subsequential, not full: nothing here shows the
  sequence itself converges.
* `exists_uniform_contact_floor` — `e^{−128β}·δ₀ ≤ ρ_N(β,0)` with `δ₀ > 0` independent of the
  extent, at every `β ≥ 0`, from `ContactFloor.corrClay_zero_ge` and `ContactFloor.exists_haar_floor`.
* `corrLag_abs_le_geometric` — on the coupling interval where `StrongCoupling.coreRate (16·4) β < 1`,
  `|ρ_N(β,k)| ≤ coreConst·coreRate^{k−1}` for every `N ≥ 2k`, with the extent in neither factor.
* `exists_infinite_volume_gapped_limit` — the assembly. On a DERIVED coupling interval `[0,b)` the
  limit function exists along a single subsequence, its contact value is bounded below by a positive
  number fixed before the extent is chosen, and its lag-`k` value decays geometrically. That is a
  non-degenerate infinite-volume two-point function with exponential clustering.

## Scope

The convergence is subsequential. Boundedness plus compactness gives a subsequence; no
monotonicity, Cauchy estimate or volume-difference bound appears here, so the limit function `L` is
not claimed to be unique or to be the limit of the full sequence. The gapped statement holds on
`[0, b)` only: `coreRate` is unbounded in the coupling (`StrongCoupling.coreRate_exceeds`), so the
geometric factor is unavailable at large `β`. `confinement_at_strong_coupling` is uniform in the
aperture at a fixed coupling, not uniform in the coupling.

DERIVED: `4` is the problem's dimension and the bound on the connected correlation, `4 = 2 * 2`
being the square of the plaquette density's range; `3` is `SU(3)`'s rank; `2` is the range of the
Wilson plaquette density, the exponent in the aperture window, and the factor in `2 * k ≤ N`;
`128 = 2 * 16 * 4` is `ContactFloor.corrClay_zero_ge`'s own exponent; `16 = 4 * 4` is
`WilsonHypercubic.card_plaq` at `d = 4`, and `16 * 4` is `StrongCoupling.touchDeg_bd_le` there; `1`
is the extent offset in `N + 1`, the level a rate is compared against, and the lag offset `k - 1`;
`0` is the origin site, the contact lag, and the lower end of the coupling range. No constant is
chosen here and none is fitted.
-/

namespace MassGap.InfiniteVolume

open Filter
open scoped Topology
open MeasureTheory
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge
open MassGap.WilsonReal MassGap.WilsonBridge

/-! ### The geometry: one variable, every direction -/

/-- `WilsonHypercubic.Site 4 (N + 1) = (Fin 4 → Fin (N + 1))`, by `rfl`: at aperture `N` the site
type has extent `N + 1` in each of the four directions, set by the single variable `N`, so there is
no separate spatial or temporal extent.

DERIVED: `4` is the problem's dimension; `1` is the extent offset in `N + 1`. -/
theorem clay_site_def (N : ℕ) :
    MassGap.WilsonHypercubic.Site 4 (N + 1) = (Fin 4 → Fin (N + 1)) := rfl

#print axioms clay_site_def

/-- `wilsonCorrAt N β d` unfolds, by `rfl`, to the connected Wilson correlation on the periodic
four-dimensional `SU(3)` lattice of extent `N + 1` between the plane-`(0,1)` plaquette at the origin
and the plaquette displaced `d` steps along direction `2`.

DERIVED: `3` is `SU(3)`'s rank; `4` is the dimension; `1` is the extent offset in `N + 1`; `(0, 1)`
is the plaquette plane; `0` is the origin site; `2` is the direction the displacement runs
along. -/
theorem wilsonCorrAt_eq_wilsonCorrConn (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    MassGap.wilsonCorrAt N β d
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
          ((0, 1), fun _ => 0) β ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d) := rfl

#print axioms wilsonCorrAt_eq_wilsonCorrConn

/-- `Fintype.card (WilsonHypercubic.Plaq 4 (N + 1)) = 16 * (N + 1) ^ 4`: the plaquette count of the
lattice at aperture `N`.

DERIVED: `4` is the dimension, both as the lattice's and as the exponent on the extent;
`16 = 4 * 4` is the plaquette count per site at `d = 4`, from `WilsonHypercubic.card_plaq`; `1` is
the extent offset in `N + 1`. -/
theorem clay_plaq_card (N : ℕ) :
    Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) = 16 * (N + 1) ^ 4 := by
  simp

#print axioms clay_plaq_card

/-- The plaquette count, as a real-valued function of the aperture, tends to infinity along
`atTop`. Since `clay_site_def` makes `N` the extent in every direction at once, the divergence of
this single variable is the divergence of the volume, and no second extent remains.

DERIVED: `4` is the dimension; `1` is the extent offset in `N + 1`. -/
theorem clay_volume_tendsto_atTop :
    Tendsto (fun N : ℕ => (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ))
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨m, hm⟩ := exists_nat_gt b
  refine ⟨m, fun a ha => ?_⟩
  have hma : (m : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hcard : ((Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (a + 1)) : ℕ) : ℝ)
      = 16 * ((a : ℝ) + 1) ^ 4 := by
    rw [clay_plaq_card]; push_cast; ring
  rw [hcard]
  have h1 : (0 : ℝ) ≤ (a : ℝ) ^ 4 := by positivity
  have h2 : (0 : ℝ) ≤ (a : ℝ) ^ 3 := by positivity
  have h3 : (0 : ℝ) ≤ (a : ℝ) ^ 2 := by positivity
  nlinarith [h1, h2, h3, ha0, hma, hm]

#print axioms clay_volume_tendsto_atTop

/-! ### The extent-free bound

The bound is `4` at every extent, every real coupling and every lag. Its derivation uses only the
range of the plaquette observable and the normalisation of the Gibbs state, so no extent enters.

DERIVED: `4 = 2 * 2` is the square of the plaquette density's range `[0, 2]`. -/

/-- `|wilsonCorrConn bd p₀ β p| ≤ 4` for any finite link and plaquette types, any boundary map, any
base plaquette, any real coupling and any plaquette, given `Nc ≠ 0`. The unconnected correlation lies
in `[0, 4]` by `wilsonCorr_nonneg` and `wilsonCorr_le_four`, and each one-point function lies in
`[0, 2]` because `wilsonPlaqObs` does and the Gibbs state is a probability state; the difference
therefore lies in `[-4, 4]`.

No geometry enters: `bd` is an arbitrary boundary map and the bound does not mention it.

DERIVED: `0` is the rank value excluded by `hN`; `4 = 2 * 2` is the bound, the square of the
plaquette density's range `[0, 2]`. -/
theorem wilsonCorrConn_abs_le_four {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (hN : Nc ≠ 0) (bd : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    |wilsonCorrConn (Nc := Nc) bd p₀ β p| ≤ 4 := by
  have hE : ∀ q : Pq, 0 ≤ (wilsonSystem bd (wilsonDensity (N := Nc))).expect
      (probHaar (MassGap.SUN.SU Nc)) β (wilsonPlaqObs (N := Nc) bd q) := fun q =>
    wilsonSystem_expect_nonneg hN bd β _ (fun U => wilsonPlaqObs_nonneg hN bd q U)
  have hE2 : ∀ q : Pq, (wilsonSystem bd (wilsonDensity (N := Nc))).expect
      (probHaar (MassGap.SUN.SU Nc)) β (wilsonPlaqObs (N := Nc) bd q) ≤ 2 := by
    intro q
    have hphi : ∀ U, |wilsonPlaqObs (N := Nc) bd q U| ≤ 2 := fun U => by
      rw [abs_of_nonneg (wilsonPlaqObs_nonneg hN bd q U)]
      exact wilsonPlaqObs_le_two hN bd q U
    exact le_trans (le_abs_self _)
      (wilsonSystem_expect_abs_le hN bd β _ (measurable_wilsonPlaqObs bd q) 2 hphi)
  have h0 := wilsonCorr_nonneg hN bd p₀ β p
  have h4 := wilsonCorr_le_four hN bd p₀ β p
  unfold wilsonCorrConn
  rw [abs_le]
  constructor
  · nlinarith [hE p₀, hE p, hE2 p₀, hE2 p]
  · nlinarith [hE p₀, hE p, hE2 p₀, hE2 p]

#print axioms wilsonCorrConn_abs_le_four

/-- `|wilsonCorrAt N β d| ≤ 4` at every aperture `N`, every real `β` and every lag `d`, with no
hypothesis. It is `wilsonCorrConn_abs_le_four` at `Nc = 3` through
`wilsonCorrAt_eq_wilsonCorrConn`. The constant does not depend on `N`.

DERIVED: `4 = 2 * 2` is the bound, the square of the plaquette density's range; `1` is the extent
offset in `N + 1`. -/
theorem wilsonCorrAt_abs_le_four (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    |MassGap.wilsonCorrAt N β d| ≤ 4 := by
  rw [wilsonCorrAt_eq_wilsonCorrConn]
  exact wilsonCorrConn_abs_le_four (Nc := 3) (by norm_num) _ _ _ _

#print axioms wilsonCorrAt_abs_le_four

/-! ### Following one lag across extents -/

/-- The correlation at a fixed natural lag `k`, as a function of the aperture: `wilsonCorrAt N β`
evaluated at the index `min k N` of `Fin (N + 1)`. Naming the lag by a natural number is what lets
one lag be followed across extents, since `Fin (N + 1)` changes with `N`; the clamp `min k N` makes
the definition total in `N`, and `corrLag_index_val` shows it does nothing once `k ≤ N`, which is
the regime every estimate below uses.

DERIVED: no numeral appears in the statement. -/
noncomputable def corrLag (k : ℕ) (β : ℝ) (N : ℕ) : ℝ :=
  MassGap.wilsonCorrAt N β ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩

#print axioms corrLag

/-- For `k ≤ N`, the underlying natural number of the clamped index is `k`: the clamp in `corrLag`
has no effect once the aperture reaches the lag.

DERIVED: `1` is the extent offset in `N + 1`. -/
theorem corrLag_index_val {k N : ℕ} (h : k ≤ N) :
    ((⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) : ℕ) = k := by
  show min k N = k
  omega

#print axioms corrLag_index_val

/-- `corrLag 0 β N = wilsonCorrAt N β 0`: at lag zero the clamped index is the zero of
`Fin (N + 1)`.

DERIVED: `0` is the contact lag, as the argument of `corrLag` and as the index of
`wilsonCorrAt`. -/
theorem corrLag_zero (β : ℝ) (N : ℕ) : corrLag 0 β N = MassGap.wilsonCorrAt N β 0 := by
  unfold corrLag
  congr 1

#print axioms corrLag_zero

/-- For `2 * k ≤ N`, the circle distance `Moment.circLag` of the clamped index is `k`: the periodic
wrap has not shortened it. This is what lets a lag-`k` estimate stated in terms of `circLag` be read
as an estimate at lag `k`.

DERIVED: `2` is the factor in the condition `2 * k ≤ N`, the point at which the wrap would begin to
shorten the distance; `1` is the extent offset in `N + 1`. -/
theorem circLag_cast {k N : ℕ} (h : 2 * k ≤ N) :
    Moment.circLag (⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) = k := by
  show min (min k N) (N + 1 - min k N) = k
  omega

#print axioms circLag_cast

/-- `corrLag k β N ∈ Set.Icc (-4 : ℝ) 4` at every lag, coupling and aperture, from
`wilsonCorrAt_abs_le_four`. The interval does not depend on `N`, which is what the compactness
arguments below use.

DERIVED: `4` is the extent-free bound of `wilsonCorrAt_abs_le_four`, appearing as both
endpoints. -/
theorem corrLag_mem_Icc (k : ℕ) (β : ℝ) (N : ℕ) : corrLag k β N ∈ Set.Icc (-4 : ℝ) 4 :=
  Set.mem_Icc.mpr (abs_le.mp (wilsonCorrAt_abs_le_four N β _))

#print axioms corrLag_mem_Icc

/-! ### The limit exists along a subsequence

Bolzano–Weierstrass on the extent-free bound. This is the first `Filter.Tendsto` in the development
whose index is the lattice extent. -/

/-- At each lag `k` and coupling `β` there is an `L` with `|L| ≤ 4` and a strictly monotone
`φ : ℕ → ℕ` along which `corrLag k β (φ j)` converges to `L`. It is
`IsCompact.tendsto_subseq` on `Set.Icc (-4) 4` applied to `corrLag_mem_Icc`. The subsequence depends
on the lag.

DERIVED: `4` is the extent-free bound inherited from `corrLag_mem_Icc`. -/
theorem exists_subseq_tendsto (k : ℕ) (β : ℝ) :
    ∃ L : ℝ, |L| ≤ 4 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => corrLag k β (φ j)) atTop (𝓝 L) := by
  obtain ⟨L, hL, φ, hφ, htend⟩ :=
    isCompact_Icc.tendsto_subseq (fun N => corrLag_mem_Icc k β N)
  exact ⟨L, abs_le.mpr (Set.mem_Icc.mp hL), φ, hφ, htend⟩

#print axioms exists_subseq_tendsto

/-- One filter serving every lag: there is a `NeBot` filter `l ≤ atTop` and a function
`L : ℕ → ℝ` with `|L k| ≤ 4` such that `corrLag k β` tends to `L k` along `l` for every `k`. The
filter is `Ultrafilter.of atTop`, which converges in each compact interval by
`IsCompact.ultrafilter_le_nhds`, and the same ultrafilter serves every lag.

DERIVED: `4` is the extent-free bound inherited from `corrLag_mem_Icc`. -/
theorem exists_filter_tendsto_all_lags (β : ℝ) :
    ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧ ∃ L : ℕ → ℝ, (∀ k, |L k| ≤ 4) ∧
      ∀ k, Tendsto (fun N => corrLag k β N) l (𝓝 (L k)) := by
  classical
  let u : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hle : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le (atTop : Filter ℕ)
  have hk : ∀ k : ℕ, ∃ a ∈ Set.Icc (-4 : ℝ) 4,
      Tendsto (fun N => corrLag k β N) (u : Filter ℕ) (𝓝 a) := by
    intro k
    have hmem : Set.Icc (-4 : ℝ) 4
        ∈ (Ultrafilter.map (fun N => corrLag k β N) u : Filter ℝ) := by
      rw [Ultrafilter.coe_map]
      exact Filter.mem_map.mpr (Filter.univ_mem' (fun N => corrLag_mem_Icc k β N))
    obtain ⟨a, ha, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds
      (Ultrafilter.map (fun N => corrLag k β N) u) (le_principal_iff.mpr hmem)
    refine ⟨a, ha, ?_⟩
    have : Filter.map (fun N => corrLag k β N) (u : Filter ℕ) ≤ 𝓝 a := by
      rw [← Ultrafilter.coe_map]
      exact hlim
    exact this
  choose L hLmem hLtend using hk
  exact ⟨(u : Filter ℕ), u.neBot', hle, L,
    fun k => abs_le.mpr (Set.mem_Icc.mp (hLmem k)), hLtend⟩

#print axioms exists_filter_tendsto_all_lags

/-- The diagonal extraction of a two-argument choice function: `diagSeq F 0 = F 0 0` and
`diagSeq F (n + 1) = F (n + 1) (diagSeq F n)`, so each extent already chosen is fed back into the
next choice. Defined by `Nat.rec`.

DERIVED: `0` is the recursion's base index and `1` the successor step; both are the shape of
`Nat.rec`, not quantities. -/
def diagSeq (F : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  fun n => Nat.rec (motive := fun _ => ℕ) (F 0 0) (fun m ih => F (m + 1) ih) n

#print axioms diagSeq

theorem diagSeq_zero (F : ℕ → ℕ → ℕ) : diagSeq F 0 = F 0 0 := rfl

#print axioms diagSeq_zero

theorem diagSeq_succ (F : ℕ → ℕ → ℕ) (n : ℕ) :
    diagSeq F (n + 1) = F (n + 1) (diagSeq F n) := rfl

#print axioms diagSeq_succ

/-- `j ≤ φ j` for every `j`, when `φ : ℕ → ℕ` is strictly monotone. By induction on `j`. It is used
to turn an eventual condition on the aperture into one on the subsequence index.

DERIVED: no numeral appears in the statement. -/
theorem self_le_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) : ∀ j, j ≤ φ j := by
  intro j
  induction j with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))

#print axioms self_le_of_strictMono

/-- One strictly monotone sequence of apertures `φ` along which `corrLag k β (φ j)` converges to
`L k` for every lag `k`, with `|L k| ≤ 4`. The finite-volume correlation functions therefore converge
pointwise in the lag to a single function `L : ℕ → ℝ`.

The construction is a diagonal argument: `exists_filter_tendsto_all_lags` gives a filter, `hstep`
extracts from it one aperture past any given one at which all lags up to `n` are within
`1 / (n + 1)` of their limits, and `diagSeq` chains those choices.

Convergence along `φ` is what is proved; the full sequence is not shown to converge.

DERIVED: `4` is the extent-free bound inherited from `corrLag_mem_Icc`. -/
theorem exists_subseq_tendsto_all_lags (β : ℝ) :
    ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ k, |L k| ≤ 4) ∧
      ∀ k, Tendsto (fun j => corrLag k β (φ j)) atTop (𝓝 (L k)) := by
  classical
  obtain ⟨l, hNeBot, hle, L, hLbound, hLtend⟩ := exists_filter_tendsto_all_lags β
  haveI : l.NeBot := hNeBot
  -- one extent, past any given one, on which all lags up to `n` are within `1/(n+1)` of the limit
  have hstep : ∀ n m : ℕ, ∃ N, m < N ∧ ∀ k, k ≤ n →
      |corrLag k β N - L k| < 1 / ((n : ℝ) + 1) := by
    intro n m
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 : ∀ k : ℕ, ∀ᶠ N in l, |corrLag k β N - L k| < 1 / ((n : ℝ) + 1) := by
      intro k
      have hx := (Metric.tendsto_nhds.mp (hLtend k)) (1 / ((n : ℝ) + 1)) hpos
      filter_upwards [hx] with N hN
      rwa [Real.dist_eq] at hN
    have hall : ∀ᶠ N in l, ∀ i : Fin (n + 1),
        |corrLag (i : ℕ) β N - L (i : ℕ)| < 1 / ((n : ℝ) + 1) :=
      Filter.eventually_all.mpr (fun i => h1 (i : ℕ))
    have hgt : ∀ᶠ N in l, m < N := (Filter.eventually_gt_atTop m).filter_mono hle
    obtain ⟨N, hN1, hN2⟩ := (hall.and hgt).exists
    refine ⟨N, hN2, fun k hk => ?_⟩
    exact hN1 ⟨k, by omega⟩
  choose F hF1 hF2 using hstep
  refine ⟨L, diagSeq F, ?_, hLbound, ?_⟩
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    rw [diagSeq_succ]
    exact hF1 (n + 1) (diagSeq F n)
  · -- the diagonal estimate
    have hdiag : ∀ n k : ℕ, k ≤ n →
        |corrLag k β (diagSeq F n) - L k| < 1 / ((n : ℝ) + 1) := by
      intro n
      cases n with
      | zero =>
          intro k hk
          rw [diagSeq_zero]
          exact hF2 0 0 k hk
      | succ m =>
          intro k hk
          rw [diagSeq_succ]
          exact hF2 (m + 1) (diagSeq F m) k hk
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    refine ⟨max k M, fun j hj => ?_⟩
    have hkj : k ≤ j := le_trans (le_max_left _ _) hj
    have hMj : M ≤ j := le_trans (le_max_right _ _) hj
    have hMjr : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hMj
    rw [Real.dist_eq]
    calc |corrLag k β (diagSeq F j) - L k|
        < 1 / ((j : ℝ) + 1) := hdiag j k hkj
      _ ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          linarith
      _ < ε := hM

#print axioms exists_subseq_tendsto_all_lags

/-! ### The limit is not trivial, and it decays -/

/-- There is a `δ₀ > 0`, fixed before any aperture is chosen, with
`Real.exp (-(128 * β)) * δ₀ ≤ wilsonCorrAt N β 0` at every aperture `N` and every `β ≥ 0`. It
combines `ContactFloor.exists_haar_floor`, which supplies `δ₀` and bounds `corrClay (N+1) 0 0`
below by it at every `N`, with `ContactFloor.corrClay_zero_ge`.

The order of quantifiers is the content: `δ₀` is outside the quantifier over `N`, so the contact
value does not collapse as the extent grows. The bound holds on the half-line `0 ≤ β` only.

DERIVED: `0` is the positivity threshold on `δ₀`, the lower end of the coupling range, and the
contact lag; `128 = 2 * 16 * 4` is `ContactFloor.corrClay_zero_ge`'s own exponent, inherited. -/
theorem exists_uniform_contact_floor :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (N : ℕ) (β : ℝ), 0 ≤ β →
      Real.exp (-(128 * β)) * δ₀ ≤ MassGap.wilsonCorrAt N β 0 := by
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.ContactFloor.exists_haar_floor
  refine ⟨δ₀, hδ₀, fun N β hβ => ?_⟩
  have h1 := MassGap.ContactFloor.corrClay_zero_ge N hβ
  have h2 : Real.exp (-(128 * β)) * δ₀
      ≤ Real.exp (-(128 * β)) * MassGap.WilsonBridge.corrClay (N + 1) 0 0 :=
    mul_le_mul_of_nonneg_left (hfloor N) (Real.exp_pos _).le
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  linarith

#print axioms exists_uniform_contact_floor

/-- `|corrLag k β N| ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ (k - 1)` for `1 ≤ k`,
`2 * k ≤ N`, `0 ≤ β` and `coreRate (16 * 4) β < 1`. It is
`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at the clamped index, with `circLag_cast`
identifying that index's circle distance as `k`.

Neither factor on the right depends on `N`, so the bound is uniform in the extent above `2 * k`.

DERIVED: `1` is the lower bound on the lag and the offset in the exponent `k - 1`, and the level
`coreRate` is required to fall below; `2` is the factor in `2 * k ≤ N`, the point below which the
periodic wrap would shorten the lag; `0` is the lower end of the coupling range; `16 * 4` is
`StrongCoupling.touchDeg_bd_le` at `dim = 4`, inherited and not chosen. -/
theorem corrLag_abs_le_geometric {k N : ℕ} (hk : 1 ≤ k) (hN : 2 * k ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) :
    |corrLag k β N| ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
      * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1) := by
  have hc : Moment.circLag (⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) = k :=
    circLag_cast hN
  have hlt : k - 1
      < Moment.circLag (⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) := by
    rw [hc]; omega
  have hbnd := MassGap.StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow N hβ hr
    (⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) (k - 1) hlt
  unfold corrLag
  rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
  exact hbnd

#print axioms corrLag_abs_le_geometric

/-! ### The assembly -/

/-- The assembly. There are `b > 0` and `δ₀ > 0` such that for every `β` with `0 ≤ β < b`:
`coreRate (16 * 4) β < 1`, and there exist a limit function `L : ℕ → ℝ` and a strictly monotone
sequence of apertures `φ` with

* `corrLag k β (φ j) → L k` as `j → ∞`, at every lag `k`;
* `Real.exp (-(128 * β)) * δ₀ ≤ L 0`, so the contact value of the limit is positive;
* `|L k| ≤ coreConst (16 * 4) β * coreRate (16 * 4) β ^ (k - 1)` for `1 ≤ k`, with
  `coreRate (16 * 4) β < 1`, so the limit decays geometrically in the lag.

`b` comes from `StrongCoupling.core_rate_lt_one_of_small`, `δ₀` from `exists_uniform_contact_floor`,
`φ` and `L` from `exists_subseq_tendsto_all_lags`, and the two bounds pass to the limit by
`ge_of_tendsto'` and `le_of_tendsto` with `corrLag_abs_le_geometric` eventually in `j`.

Both `b` and `δ₀` are bound outside the quantifier over `β` and over the aperture. The convergence
is along `φ` only; the limit is not claimed to be unique or to be the limit of the full sequence,
and the statement is confined to `[0, b)`.

DERIVED: `0` is the positivity threshold on `b` and `δ₀`, the lower end of the coupling range, and
the contact lag; `1` is the level `coreRate` falls below, the lower bound on the lag, and the offset
in `k - 1`; `128 = 2 * 16 * 4` is `ContactFloor.corrClay_zero_ge`'s own exponent; `16 * 4` is
`StrongCoupling.touchDeg_bd_le` at `dim = 4`. -/
theorem exists_infinite_volume_gapped_limit :
    ∃ b : ℝ, 0 < b ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ β : ℝ, 0 ≤ β → β < b →
        MassGap.StrongCoupling.coreRate (16 * 4) β < 1 ∧
        ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
          (∀ k : ℕ, Tendsto (fun j => corrLag k β (φ j)) atTop (𝓝 (L k))) ∧
          Real.exp (-(128 * β)) * δ₀ ≤ L 0 ∧
          (∀ k : ℕ, 1 ≤ k → |L k| ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
              * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1)) := by
  obtain ⟨b, hb, hrate⟩ := MassGap.StrongCoupling.core_rate_lt_one_of_small (16 * 4)
  obtain ⟨δ₀, hδ₀, hfloor⟩ := exists_uniform_contact_floor
  refine ⟨b, hb, δ₀, hδ₀, fun β hβ0 hβb => ?_⟩
  have hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1 := hrate β hβ0 hβb
  refine ⟨hr, ?_⟩
  obtain ⟨L, φ, hφ, _hLb, htend⟩ := exists_subseq_tendsto_all_lags β
  have hid := self_le_of_strictMono hφ
  refine ⟨L, φ, hφ, fun k => htend k, ?_, ?_⟩
  · refine ge_of_tendsto' (htend 0) (fun j => ?_)
    show Real.exp (-(128 * β)) * δ₀ ≤ corrLag 0 β (φ j)
    rw [corrLag_zero]
    exact hfloor (φ j) β hβ0
  · intro k hk1
    have habs : Tendsto (fun j => |corrLag k β (φ j)|) atTop (𝓝 |L k|) := (htend k).abs
    refine le_of_tendsto habs ?_
    filter_upwards [eventually_ge_atTop (2 * k)] with j hj
    exact corrLag_abs_le_geometric hk1 (le_trans hj (hid j)) hβ0 hr

#print axioms exists_infinite_volume_gapped_limit

/-- `μYMAt N β < κ₀YM` for all large enough `N`, at a fixed `β` with `0 < β` and
`coreRate (16 * 4) β < 1`. The conclusion is `∀ᶠ N in atTop`, so the aperture is quantified
eventually while the coupling is fixed by the hypotheses.

The chain: `ContactFloor.read_p_le_aperture_uniform` bounds the read's weights by
`C * r ^ circLag d` with `C` and `r` free of the aperture, the contact floor `δ` replacing the
per-aperture `m` that `StrongCoupling.read_p_le_of_corrClay` would carry;
`Moment.circ_moment_le_of_geometric` turns those weights into the bound
`B = 2 * C * ∑' k, k^2 * r^k` on `d2At N β`, a convergent series with no aperture in it;
`Moment.aperture_factor_tendsto_zero` drives the `(2 * π / (N + 1))^2` window below the floor gap
eventually; and `Read.tension_lt_floor_of_circ_moment` closes it.

The strict hypothesis `0 < β` is used to make `r` strictly positive, since `coreRate` vanishes at
zero and the weight bound divides by it. `coreConst` and `coreRate` both depend on `β`, and
`coreRate (16 * 4) β < 1` holds only near zero
(`StrongCoupling.core_rate_lt_one_of_small_hypercubic`), so this is not
`Complete.confinement_of_geometric_decay`, which quantifies over every `β` with one `C` and one `r`.
What is uniform here is the aperture.

DERIVED: `0` is the strict lower bound on `β`; `1` is the level `coreRate` falls below; `16 * 4` is
`StrongCoupling.touchDeg_bd_le` at `dim = 4`, inherited and not chosen. The `2` and the `1`
appearing in the moment bound inside the proof are `circ_moment_le_of_geometric`'s own. -/
theorem confinement_at_strong_coupling {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, MassGap.μYMAt N β < MassGap.κ₀YM := by
  classical
  obtain ⟨δ, hδ, hbound⟩ := MassGap.ContactFloor.read_p_le_aperture_uniform β
  set r : ℝ := MassGap.StrongCoupling.coreRate (16 * 4) β with hrdef
  have hr0 : 0 ≤ r := MassGap.StrongCoupling.coreRate_nonneg _ hβ.le
  -- the rate is a product of strictly positive factors at `β > 0`, exactly as
  -- `read_p_le_of_corrClay` establishes it internally
  have hq : (0 : ℝ) < Real.exp (2 * β) - 1 := by
    have h1 : Real.exp 0 < Real.exp (2 * β) := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at h1; linarith
  have hrpos : 0 < r := by
    rw [hrdef]
    unfold MassGap.StrongCoupling.coreRate
    exact mul_pos (mul_pos (by positivity) hq) (Real.exp_pos _)
  have hconst : 0 ≤ MassGap.StrongCoupling.coreConst (16 * 4) β := by
    unfold MassGap.StrongCoupling.coreConst
    refine div_nonneg (le_trans zero_le_one
      (MassGap.StrongCoupling.one_le_corePrefactor _ hβ.le)) ?_
    rw [← hrdef]
    linarith
  set C : ℝ := MassGap.StrongCoupling.coreConst (16 * 4) β / (r * δ) + 1 with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    have : 0 ≤ MassGap.StrongCoupling.coreConst (16 * 4) β / (r * δ) :=
      div_nonneg hconst (mul_nonneg hr0 hδ.le)
    linarith
  -- the read's weights decay, with `C` and `r` free of the aperture
  have hdecay : ∀ (N : ℕ) (d : Fin (N + 1)), (MassGap.readYMAt N β).p d ≤ C * r ^ (Moment.circLag d) := by
    intro N d
    exact hbound N (MassGap.readYMAt N β) β
      (fun d' => MassGap.StrongArm.wilsonCorrAt_eq_corrClay N β d') hβ le_rfl hr d
  -- hence a bounded circle moment, with no aperture in the bound
  set B : ℝ := 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k with hBdef
  have hmom : ∀ N : ℕ, MassGap.d2At N β ≤ B := by
    intro N
    exact Moment.circ_moment_le_of_geometric (MassGap.readYMAt N β) hC hr0 hr (hdecay N)
  -- and the aperture window drives it under the floor gap
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  filter_upwards [hev] with N hN
  exact (MassGap.readYMAt N β).tension_lt_floor_of_circ_moment (hmom N) hN

#print axioms confinement_at_strong_coupling

end MassGap.InfiniteVolume
