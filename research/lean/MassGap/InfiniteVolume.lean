import Mathlib
import MassGap.Complete
import MassGap.ContactFloor

/-!
# MassGap.InfiniteVolume — the thermodynamic limit of the Clay correlation

## The limit is in ONE variable

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

* `wilsonCorrConn_abs_le_four` / `wilsonCorrAt_abs_le_four` — `|ρ_N(β,d)| ≤ 4` at EVERY extent,
  EVERY real coupling and EVERY lag, with no hypothesis. The Wilson plaquette observable takes
  values in `[0,2]` and the Gibbs state is a probability state, so the unconnected correlation lies
  in `[0,4]` and the product of the two one-point functions lies in `[0,4]`. Nothing in the constant
  refers to the extent.
* `exists_subseq_tendsto` — consequently, at each lag and each coupling the sequence of finite-volume
  values has a convergent subsequence.
* `exists_filter_tendsto_all_lags` / `exists_subseq_tendsto_all_lags` — ONE subsequence along which
  EVERY lag converges simultaneously, so the whole finite-volume correlation function converges
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

## What is NOT proved

Full convergence. Boundedness plus compactness gives a subsequence; nothing here supplies the
monotonicity, Cauchy estimate or volume-difference bound that would make the limit unique. The
gapped statement is also confined to `[0,b)`: `coreRate` is unbounded in the coupling
(`StrongCoupling.coreRate_exceeds`), so the geometric factor is not available at large `β`.

DERIVED: `4` is the problem's dimension, `3` is `SU(3)`, `2` is the range of the Wilson plaquette
density and `4 = 2·2` its square, `128 = 2·16·4` is `ContactFloor.corrClay_zero_ge`'s own exponent,
`16 = 4·4` is `WilsonHypercubic.card_plaq` at `d = 4`. No constant is chosen here and none is fitted.
-/

namespace MassGap.InfiniteVolume

open Filter
open scoped Topology
open MeasureTheory
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge
open MassGap.WilsonReal MassGap.WilsonBridge

/-! ### The geometry: one variable, every direction -/

/-- The Clay lattice's site type at aperture `N` is `Fin 4 → Fin (N + 1)` — extent `N + 1` in every
one of the four directions, set by the single variable `N`. -/
theorem clay_site_def (N : ℕ) :
    MassGap.WilsonHypercubic.Site 4 (N + 1) = (Fin 4 → Fin (N + 1)) := rfl

#print axioms clay_site_def

/-- The correlation the read consumes, written out on that lattice: `wilsonCorrAt N β d` is the
connected Wilson correlation between the plane-`(0,1)` plaquette at the origin and the one displaced
`d` steps along direction `2`, on the periodic four-dimensional `SU(3)` lattice of extent `N + 1`. -/
theorem wilsonCorrAt_eq_wilsonCorrConn (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    MassGap.wilsonCorrAt N β d
      = wilsonCorrConn (Nc := 3) (MassGap.WilsonHypercubic.bd (d := 4) (n := N + 1))
          ((0, 1), fun _ => 0) β ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 d) := rfl

#print axioms wilsonCorrAt_eq_wilsonCorrConn

/-- The plaquette count at aperture `N`. -/
theorem clay_plaq_card (N : ℕ) :
    Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) = 16 * (N + 1) ^ 4 := by
  simp

#print axioms clay_plaq_card

/-- **`N → ∞` IS the infinite-volume limit.** The lattice's plaquette count diverges as the single
aperture variable grows, so there is no second extent left to send to infinity. -/
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

The constant is `4` at every extent, every real coupling and every lag, and the extent appears
nowhere in its derivation: the observable's range and the normalisation of the Gibbs state are all
that enter. -/

/-- **The connected Wilson correlation is bounded by `4`, at any geometry.** The unconnected
correlation lies in `[0,4]` (`WilsonBridge.wilsonCorr_nonneg`, `wilsonCorr_le_four`) and each
one-point function lies in `[0,2]`, so their difference lies in `[-4,4]`. -/
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

/-- **The Clay correlation is bounded by `4`, uniformly in the extent.** No hypothesis: every
aperture, every real coupling, every lag. This is the aperture-uniform control a thermodynamic limit
needs, and the constant carries no extent. -/
theorem wilsonCorrAt_abs_le_four (N : ℕ) (β : ℝ) (d : Fin (N + 1)) :
    |MassGap.wilsonCorrAt N β d| ≤ 4 := by
  rw [wilsonCorrAt_eq_wilsonCorrConn]
  exact wilsonCorrConn_abs_le_four (Nc := 3) (by norm_num) _ _ _ _

#print axioms wilsonCorrAt_abs_le_four

/-! ### Following one lag across extents -/

/-- The correlation at the FIXED natural lag `k`, as a function of the aperture. The index is
clamped to the aperture so that the sequence is total in `N`; once `k ≤ N` the clamp does nothing
(`corrLag_index_val`), which is the only regime the estimates below use. -/
noncomputable def corrLag (k : ℕ) (β : ℝ) (N : ℕ) : ℝ :=
  MassGap.wilsonCorrAt N β ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩

#print axioms corrLag

/-- Once the aperture reaches the lag, the index really is the lag. -/
theorem corrLag_index_val {k N : ℕ} (h : k ≤ N) :
    ((⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) : ℕ) = k := by
  show min k N = k
  omega

#print axioms corrLag_index_val

/-- At lag zero the index is the zero of `Fin (N+1)`. -/
theorem corrLag_zero (β : ℝ) (N : ℕ) : corrLag 0 β N = MassGap.wilsonCorrAt N β 0 := by
  unfold corrLag
  congr 1

#print axioms corrLag_zero

/-- Once the extent is at least twice the lag, the circle distance of the index IS the lag: the
periodic wrap has not yet shortened it. -/
theorem circLag_cast {k N : ℕ} (h : 2 * k ≤ N) :
    Moment.circLag (⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩ : Fin (N + 1)) = k := by
  show min (min k N) (N + 1 - min k N) = k
  omega

#print axioms circLag_cast

/-- The sequence lives in a fixed compact interval. -/
theorem corrLag_mem_Icc (k : ℕ) (β : ℝ) (N : ℕ) : corrLag k β N ∈ Set.Icc (-4 : ℝ) 4 :=
  Set.mem_Icc.mpr (abs_le.mp (wilsonCorrAt_abs_le_four N β _))

#print axioms corrLag_mem_Icc

/-! ### The limit exists along a subsequence

Bolzano–Weierstrass on the extent-free bound. This is the first `Filter.Tendsto` in the development
whose index is the lattice extent. -/

/-- **A convergent subsequence at each lag.** -/
theorem exists_subseq_tendsto (k : ℕ) (β : ℝ) :
    ∃ L : ℝ, |L| ≤ 4 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => corrLag k β (φ j)) atTop (𝓝 L) := by
  obtain ⟨L, hL, φ, hφ, htend⟩ :=
    isCompact_Icc.tendsto_subseq (fun N => corrLag_mem_Icc k β N)
  exact ⟨L, abs_le.mpr (Set.mem_Icc.mp hL), φ, hφ, htend⟩

#print axioms exists_subseq_tendsto

/-- **Every lag converges along ONE filter.** An ultrafilter refining `atTop` converges in each
compact interval, and the same ultrafilter serves every lag, so the whole correlation function has a
limit along it. -/
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

/-- The diagonal extraction: start at `F 0 0` and feed each extent back into the next choice.

DERIVED: `0` is the recursion's base index and `1` the successor step. Both are the shape of
`Nat.rec`, not quantities. -/
def diagSeq (F : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  fun n => Nat.rec (motive := fun _ => ℕ) (F 0 0) (fun m ih => F (m + 1) ih) n

#print axioms diagSeq

theorem diagSeq_zero (F : ℕ → ℕ → ℕ) : diagSeq F 0 = F 0 0 := rfl

#print axioms diagSeq_zero

theorem diagSeq_succ (F : ℕ → ℕ → ℕ) (n : ℕ) :
    diagSeq F (n + 1) = F (n + 1) (diagSeq F n) := rfl

#print axioms diagSeq_succ

/-- A strictly monotone map of `ℕ` into itself dominates the identity. -/
theorem self_le_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) : ∀ j, j ≤ φ j := by
  intro j
  induction j with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))

#print axioms self_le_of_strictMono

/-- **ONE subsequence of extents along which EVERY lag converges.** The finite-volume correlation
functions converge pointwise, as functions of the lag, to a single limit function `L`. -/
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

/-- **A positive contact value, uniform in the extent.** `ContactFloor.corrClay_zero_ge` against
`ContactFloor.exists_haar_floor`: one `δ₀ > 0`, fixed before the aperture is chosen, with
`e^{−128β}·δ₀ ≤ ρ_N(β,0)` at every aperture and every `β ≥ 0`. -/
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

/-- **Geometric decay in the lag, uniformly in the extent.**
`StrongCoupling.corrClay_abs_le_coreConst_mul_rate_pow` at the cast lag, with `circLag_cast`
identifying the circle distance for `N ≥ 2k`. Neither `coreConst` nor `coreRate` carries an
extent. -/
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

/-- **THE INFINITE-VOLUME CORRELATION FUNCTION EXISTS AND IS GAPPED, ON A DERIVED COUPLING
INTERVAL.**

On `[0, b)` — `b` from `StrongCoupling.core_rate_lt_one_of_small`, carrying no numeral — there is a
strictly increasing sequence of apertures `φ` along which the finite-volume correlation converges at
EVERY lag to a limit function `L`, and the limit satisfies

* `e^{−128β}·δ₀ ≤ L 0` with `δ₀ > 0` fixed before the coupling and the aperture are chosen, so the
  contact term does not collapse in the limit;
* `|L k| ≤ coreConst · coreRate^{k−1}` with `coreRate < 1`, so the limit clusters exponentially.

The subsequence is genuinely indexed by the lattice extent and `φ` occurs in the conclusion. What is
NOT claimed is uniqueness of the limit: this is subsequential convergence. -/
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

end MassGap.InfiniteVolume
