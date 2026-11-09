import Mathlib
import MassGap.ReflInvG

/-!
# MassGap.ReflPosG — the reflection positivity of the periodic Wilson state of a gauge group `G`

At `SU(N)` the periodic state is reflection positive at the constant `2p` (mirror plane `x_τ = p`) on
`halfSpaceAlg τ p`, at every real `β` (`PeriodicState.periodicState_reflPositive`), and
`ContinuumSchwinger.stateAlong_rp` / `stateK_rp` read that at the plane `x_τ = 0`. This module proves
both for every `GaugeGroup G`, by the same route with `SU N` replaced by `G`:

| step | `SU(N)` | here (any `G`) |
|---|---|---|
| plaquette holonomy congruence | `ReflectionPositivity.hol_congr_on_support` | `hol_congr_on_supportG` |
| partial action congruence | `ReflectionPositivity.action_on_congr_of_support` | `actSum_congrG` |
| degenerate plaquettes cost nothing | `ActionSplit.sum_plqDeg_zero` | `sum_plqDeg_zeroG` |
| density at the mirrored holonomy | `ActionSplit.density_reflConf` | `density_reflConfG` |
| the two halves exchanged | `ActionSplit.sum_plqMinus_eq_plus_refl` | `sum_plqMinus_eq_plus_reflG` |
| the three partial actions | `ActionSplit.actPlus`, `actMinus`, `actZero` | `actPlusG`, `actMinusG`, `actZeroG` |
| the action split | `ActionSplit.action_eq_split` | `action_eq_splitG` |
| bound on a partial Boltzmann factor | `ActionSplit.abs_exp_actSum_le` | `abs_exp_actSumG_le` |
| plane weight, and it reads the planes | `ActionSplit.wPlane`, `wPlane_local` | `wPlaneG`, `wPlaneG_local` |
| half-space factor is an observable of the slab | `ReflectionStrong.halfBoltz_mem` | `halfBoltzG_mem` |
| dressing | `ReflectionStrong.dressed`, `dressed_mem` | `dressedG`, `dressedG_mem` |
| split pairing | `LogConvex.pairing` | `pairingG` |
| split pairing nonnegative | `LogConvex.pairing_nonneg` | `pairingG_nonneg` |
| Gibbs numerator is the split pairing | `ReflectionStrong.corrNum_refl_eq_pairing` | `corrNum_refl_eq_pairingG` |
| Gibbs reflection positivity on the slab | `ReflectionStrong.wilson_expect_nonneg_module` | `wilson_expect_nonneg_moduleG` |
| half-space observable reads the slab | `PeriodicState.torusObs_mem_localObs_even` | `torusObsG_mem_localObs_even` |
| torus states positive, eventually | `PeriodicState.torusState_reflPositive_even_eventually` | `torusStateG_reflPositive_even_eventually` |
| every limit positive | `PeriodicState.reflPositive_even_of_tendsto_torus` | `reflPositive_even_of_tendsto_torusG` |
| infinite-volume state positive | `PeriodicState.periodicState_reflPositive` | `periodicStateG_reflPositive` |
| positivity at the plane `x_τ = 0` | `ContinuumSchwinger.stateAlong_rp`, `stateK_rp` | `periodicStateG_rp_zero`, `canonSched_rp` |

The finite-lattice core is `ActionSplit.pairing_nonneg_of_local`, which is stated over an arbitrary
probability space of link values; this module supplies its hypotheses at `probHaar G`. The coordinate
map of the reflection is `ReflInvG.axisDaggerG`, measure preserving because `probHaar G` is
inversion invariant. Of the Wilson density the proofs use `wilsonDensityG_one` (degenerate plaquettes),
`wilsonDensityG_conj` (the mirrored holonomy is a conjugate), and `wilsonDensityG_nonneg`,
`wilsonDensityG_le_two` (the bounds that make every factor integrable).

The odd constant `2p - 1` (`PeriodicState.periodicState_reflPositive_odd`) is not ported here.

`SchedRP S` asks that the state of every step be reflection positive at the plane `x_τ = 0` on
`halfSpaceAlg τ 0`; `schedRP_canonSched` proves it at `canonSched G`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `2` in `n = 2 * m` the even extent of a periodic reflection
and in `2 * p` the plane-to-constant doubling; `2k + 1` the extent index of the torus family; `0` the
plane `x_τ = 0` and the sign concluded; `2` in the action bounds the range of `wilsonDensityG`.
-/

noncomputable section

namespace MassGap.ReflPosG

open MeasureTheory MassGap.CompactGauge MassGap.GaugeGroup
open MassGap.WilsonHypercubic MassGap.WilsonLattice MassGap.Reflect MassGap.ActionSplit
  MassGap.LogConvex

/-! ## 1. The action split over `G` -/

section Split

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [NeZero n] in
/-- `wilsonHol bd p U = wilsonHol bd p V` when `U` and `V` agree on every link of the word `bd p`, over
any group.

DERIVED: no numeral. -/
theorem hol_congr_on_supportG {L P : Type} (bd : P → List (L × Bool)) (p : P) (U V : L → G)
    (h : ∀ l ∈ (bd p).map Prod.fst, U l = V l) :
    wilsonHol bd p U = wilsonHol bd p V := by
  unfold wilsonHol
  congr 1
  refine List.map_congr_left ?_
  intro lo hlo
  have : U lo.1 = V lo.1 := h lo.1 (List.mem_map_of_mem hlo)
  rw [this]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [NeZero n] in
/-- If every plaquette of `A` reads only links of `S`, and `U`, `V` agree on `S`, the partial sums of
any plaquette function over `A` agree.

DERIVED: no numeral. -/
theorem actSum_congrG {L P : Type} (bd : P → List (L × Bool)) (φ : G → ℝ) (A : Finset P)
    (S : Finset L) (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (U V : L → G) (h : ∀ l ∈ S, U l = V l) :
    (∑ p ∈ A, φ (wilsonHol bd p U)) = ∑ p ∈ A, φ (wilsonHol bd p V) :=
  Finset.sum_congr rfl fun p hp => by
    rw [hol_congr_on_supportG bd p U V (fun l hl => h l (hsupp p hp l hl))]

variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- The Wilson density of `G` summed over the degenerate plaquettes `plqDeg τ` is `0`:
`hol_diag_one` and `wilsonDensityG_one`.

DERIVED: `0` the value of the sum. -/
theorem sum_plqDeg_zeroG (U : Link d n → G) :
    ∑ q ∈ plqDeg (d := d) (n := n) τ, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U) = 0 := by
  refine Finset.sum_eq_zero (fun q hq => ?_)
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨h1, h2⟩ := (mem_plqDeg τ _).mp hq
  have hνμ : ν = μ := by
    show ν = μ
    rw [show ν = τ from h2, show μ = τ from h1]
  rw [show (((μ, ν), x) : Plaq d n) = ((μ, μ), x) by rw [hνμ], hol_diag_one, wilsonDensityG_one]

/-- `wilsonDensityG` of `q`'s holonomy at the reflected configuration is `wilsonDensityG` of the
reflected plaquette's holonomy: `Reflect.hol_reflConf` and `wilsonDensityG_conj`.

DERIVED: no numeral. -/
theorem density_reflConfG (c : Fin n) (q : Plaq d n) (U : Link d n → G) :
    wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U))
      = wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ c q) U) := by
  obtain ⟨g, hg⟩ := hol_reflConf (G := G) τ c q U
  rw [hg, wilsonDensityG_conj]

/-- The Wilson density of `G` summed over `plqMinus τ a m` at `U` is the sum over `plqPlus τ a m` at
`reflConf τ (a + a) U`.

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent. -/
theorem sum_plqMinus_eq_plus_reflG (hm : n = 2 * m) (hm0 : 0 < m) (U : Link d n → G) :
    ∑ q ∈ plqMinus τ a m, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ plqPlus τ a m,
          wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) := by
  have himg : (plqPlus (d := d) (n := n) τ a m).image (reflPlaq τ (a + a)) = plqMinus τ a m := by
    ext q
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact reflPlaq_plus_mem_minus τ a m hm hm0 hp
    · intro hq
      exact ⟨reflPlaq τ (a + a) q, reflPlaq_minus_mem_plus τ a m hm hm0 hq,
        reflPlaq_involutive τ (a + a) q⟩
  have hinj : ∀ x ∈ plqPlus (d := d) (n := n) τ a m, ∀ y ∈ plqPlus (d := d) (n := n) τ a m,
      reflPlaq τ (a + a) x = reflPlaq τ (a + a) y → x = y :=
    fun x _ y _ h => (reflPlaq_involutive τ (a + a)).injective h
  calc ∑ q ∈ plqMinus τ a m, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ (plqPlus τ a m).image (reflPlaq τ (a + a)),
          wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U) := by rw [himg]
    _ = ∑ q ∈ plqPlus τ a m,
          wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ (a + a) q) U) :=
        Finset.sum_image hinj
    _ = ∑ q ∈ plqPlus τ a m,
          wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) :=
        Finset.sum_congr rfl (fun q _ => (density_reflConfG τ (a + a) q U).symm)

/-- The Wilson density of `G` summed over `plqPlus τ a m`.

DERIVED: no numeral. -/
def actPlusG (U : Link d n → G) : ℝ :=
  ∑ q ∈ plqPlus τ a m, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)

/-- The Wilson density of `G` summed over `plqMinus τ a m`.

DERIVED: no numeral. -/
def actMinusG (U : Link d n → G) : ℝ :=
  ∑ q ∈ plqMinus τ a m, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)

/-- The Wilson density of `G` summed over `plqZero τ a m`, the plaquettes inside the two planes.

DERIVED: no numeral. -/
def actZeroG (U : Link d n → G) : ℝ :=
  ∑ q ∈ plqZero τ a m, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)

/-- **The action split over `G`**: `action U = actPlusG U + actMinusG U + actZeroG U`.

DERIVED: no numeral. -/
theorem action_eq_splitG (U : Link d n → G) :
    (GaugeWilson.sysWilsonG G d n).action U
      = actPlusG τ a m U + actMinusG τ a m U + actZeroG τ a m U := by
  show (∑ q, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)) = _
  rw [sum_plaq_split τ a m, sum_plqDeg_zeroG τ U]
  show 0 + actZeroG τ a m U + (actPlusG τ a m U + actMinusG τ a m U) = _
  ring

/-- A partial Wilson action of `G` is measurable in the configuration.

DERIVED: no numeral. -/
theorem measurable_actSumG (A : Finset (Plaq d n)) :
    Measurable (fun U : Link d n → G =>
      ∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)) :=
  Finset.measurable_sum _ (fun q _ =>
    measurable_wilsonDensityG.comp (measurable_wilsonHol (G := G) _ q))

/-- `|exp(−β · ∑_{q ∈ A} φ_G)| ≤ exp(|β| · 2 · |A|)`.

DERIVED: `2` the upper bound of `wilsonDensityG`. -/
theorem abs_exp_actSumG_le (β : ℝ) (A : Finset (Plaq d n)) (U : Link d n → G) :
    |Real.exp (-β * ∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U))|
      ≤ Real.exp (|β| * (2 * A.card)) := by
  have hsum : |∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)|
      ≤ 2 * A.card := by
    calc |∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)|
        ≤ ∑ q ∈ A, |wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _q ∈ A, (2 : ℝ) := by
          refine Finset.sum_le_sum (fun q _ => ?_)
          rw [abs_of_nonneg (wilsonDensityG_nonneg _)]
          exact wilsonDensityG_le_two _
      _ = (A.card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * A.card := by ring
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc -β * (∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U))
      ≤ |(-β) * ∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)| :=
        le_abs_self _
    _ = |β| * |∑ q ∈ A, wilsonDensityG G (wilsonHol (bd (d := d) (n := n)) q U)| := by
        rw [abs_mul, abs_neg]
    _ ≤ |β| * (2 * A.card) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- **The plane weight of `G`**: `exp(−β · actZeroG)`.

DERIVED: no numeral. -/
def wPlaneG (β : ℝ) (U : Link d n → G) : ℝ := Real.exp (-β * actZeroG τ a m U)

/-- **The half-space Boltzmann factor of `G`**: `exp(−β · actPlusG)`.

DERIVED: no numeral. -/
def halfBoltzG (β : ℝ) (U : Link d n → G) : ℝ := Real.exp (-β * actPlusG τ a m U)

/-- An observable times the half-space Boltzmann factor.

DERIVED: no numeral. -/
def dressedG (β : ℝ) (F : (Link d n → G) → ℝ) : (Link d n → G) → ℝ :=
  fun U => F U * halfBoltzG τ a m β U

/-- `wPlaneG` reads only the plane block `blkR τ a m`.

DERIVED: no numeral. -/
theorem wPlaneG_local (β : ℝ) (U V : Link d n → G) (hR : ∀ l ∈ blkR τ a m, U l = V l) :
    wPlaneG τ a m β U = wPlaneG τ a m β V := by
  have h2 : actZeroG τ a m U = actZeroG τ a m V :=
    actSum_congrG (bd (d := d) (n := n)) (wilsonDensityG G) (plqZero τ a m) (blkR τ a m)
      (fun p hp => plaq_links_plane τ a m ((mem_plqZero τ a m p).mp hp).1
        ((mem_plqZero τ a m p).mp hp).2.1 ((mem_plqZero τ a m p).mp hp).2.2) U V hR
  unfold wPlaneG
  rw [h2]

/-- `actPlusG` reads only `blkS τ a m ∪ blkR τ a m`.

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent. -/
theorem actPlusG_local (hm : n = 2 * m) (hm0 : 0 < m) (U V : Link d n → G)
    (hS : ∀ l ∈ blkS τ a m, U l = V l) (hR : ∀ l ∈ blkR τ a m, U l = V l) :
    actPlusG τ a m U = actPlusG τ a m V := by
  have hUV : ∀ l ∈ blkS τ a m ∪ blkR τ a m, U l = V l := by
    intro l hl
    rcases Finset.mem_union.mp hl with h | h
    · exact hS l h
    · exact hR l h
  exact actSum_congrG (bd (d := d) (n := n)) (wilsonDensityG G) (plqPlus τ a m)
    (blkS τ a m ∪ blkR τ a m)
    (fun p hp => plaq_links_le τ a m hm hm0 ((mem_plqPlus τ a m p).mp hp).1
      ((mem_plqPlus τ a m p).mp hp).2.2) U V hUV

/-- **The half-space Boltzmann factor of `G` is an observable of the slab**:
`halfBoltzG τ a m β ∈ localObs (blkS τ a m) (blkR τ a m)`.

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent, and in the bound the
range of `wilsonDensityG`. -/
theorem halfBoltzG_mem (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    halfBoltzG (G := G) τ a m β ∈ localObs (blkS τ a m) (blkR τ a m) := by
  refine mem_localObs.mpr ⟨?_, ⟨Real.exp (|β| * (2 * ((plqPlus (d := d) (n := n) τ a m).card : ℝ))),
    ?_⟩, fun U V hS hR => ?_⟩
  · unfold halfBoltzG actPlusG
    exact Real.measurable_exp.comp ((measurable_actSumG _).const_mul _)
  · intro U
    unfold halfBoltzG actPlusG
    exact abs_exp_actSumG_le β _ U
  · show Real.exp (-β * actPlusG τ a m U) = Real.exp (-β * actPlusG τ a m V)
    rw [actPlusG_local τ a m hm hm0 U V hS hR]

/-- `dressedG τ a m β F ∈ localObs (blkS τ a m) (blkR τ a m)` whenever `F` is.

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent. -/
theorem dressedG_mem (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → G) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    dressedG τ a m β F ∈ localObs (blkS τ a m) (blkR τ a m) :=
  MassGap.ReflectionStrong.mul_mem_localObs hF (halfBoltzG_mem τ a m hm hm0 β)

end Split

/-! ## 2. Reflection positivity on the finite periodic lattice -/

section Positive

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {d n : ℕ} [NeZero n] (τ : Fin d) (a : Fin n) (m : ℕ)

/-- **The split reflection pairing over `G`**:
`∫ wPlaneG · F · (H ∘ reflConf τ (a + a))` against the product Haar measure of `G`.

DERIVED: no numeral. -/
def pairingG (β : ℝ) (F H : (Link d n → G) → ℝ) : ℝ :=
  ∫ U, wPlaneG τ a m β U * F U * H (reflConf τ (a + a) U) ∂(cvol (Link d n) (probHaar G))

/-- **The split pairing over `G` is nonnegative on the diagonal**, for every `F` of
`localObs (blkS τ a m) (blkR τ a m)`, at every real `β`: `ActionSplit.pairing_nonneg_of_local` at
`probHaar G`, with the twist `reflLinkPerm τ (a + a)`, `ReflInvG.axisDaggerG τ`.

DERIVED: `0` the strict lower bound on `m` and the sign concluded; `2` in `n = 2 * m` the even extent,
and in the bound the range of `wilsonDensityG`. -/
theorem pairingG_nonneg (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → G) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    0 ≤ pairingG τ a m β F F := by
  obtain ⟨CF, hCF⟩ := localObs_bounded hF
  set K : ℝ := Real.exp (|β| * (2 * ((plqZero (d := d) (n := n) τ a m).card : ℝ))) with hK
  have hKnn : 0 ≤ K := le_of_lt (Real.exp_pos _)
  have hCFnn : 0 ≤ CF := le_trans (abs_nonneg _) (hCF (fun _ => 1))
  have hWm : Measurable (wPlaneG (G := G) τ a m β) := by
    unfold wPlaneG actZeroG
    exact Real.measurable_exp.comp ((measurable_actSumG _).const_mul _)
  refine pairing_nonneg_of_local (probHaar G)
    (blkS τ a m) (blkT τ a m) (blkR τ a m)
    (blkS_disjoint_blkT τ a m) (blkS_disjoint_blkR τ a m) (blkT_disjoint_blkR τ a m)
    (reflLinkPerm τ (a + a)) (MassGap.ReflInvG.axisDaggerG τ)
    (fun l => MassGap.ReflInvG.axisDaggerG_measurePreserving τ l)
    (fun l hl => blkR_fixed τ a m hm hl)
    (fun l hl u => by simp [MassGap.ReflInvG.axisDaggerG, blkR_axis_free τ a m hl])
    (fun l hl => blkS_maps_blkT τ a m hm hm0 hl)
    (fun _ => 1)
    F (localObs_measurable hF) (localObs_local hF)
    (wPlaneG τ a m β) hWm (fun U => le_of_lt (Real.exp_pos _))
    (fun U V hR => wPlaneG_local τ a m β U V hR)
    (K * CF * CF) (fun U => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (abs_exp_actSumG_le β _ U) (hCF U) (abs_nonneg _) hKnn)
    (hCF _) (abs_nonneg _) (mul_nonneg hKnn hCFnn)

/-- **The factorisation over `G`**: the Gibbs integrand of `F · (H ∘ Θ)` is the plane weight times the
two dressings, `Θ = reflConf τ (a + a)`.

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent. -/
theorem integrand_eq_paired_obsG (hm : n = 2 * m) (hm0 : 0 < m) (F H : (Link d n → G) → ℝ)
    (β : ℝ) (U : Link d n → G) :
    F U * H (reflConf τ (a + a) U) * (GaugeWilson.sysWilsonG G d n).boltz β U
      = wPlaneG τ a m β U * dressedG τ a m β F U
          * dressedG τ a m β H (reflConf τ (a + a) U) := by
  have hmir : actPlusG τ a m (reflConf τ (a + a) U) = actMinusG (G := G) τ a m U :=
    (sum_plqMinus_eq_plus_reflG τ a m hm hm0 U).symm
  show F U * H (reflConf τ (a + a) U) * Real.exp (-β * (GaugeWilson.sysWilsonG G d n).action U) = _
  rw [action_eq_splitG τ a m U]
  unfold wPlaneG dressedG halfBoltzG
  rw [hmir]
  rw [show -β * (actPlusG τ a m U + actMinusG τ a m U + actZeroG τ a m U)
      = (-β * actZeroG τ a m U) + ((-β * actPlusG τ a m U) + (-β * actMinusG τ a m U)) by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **The Gibbs correlation numerator of `F · (H ∘ Θ)` over `G` is the split pairing of the dressed
observables.**

DERIVED: `0` the strict lower bound on `m`; `2` in `n = 2 * m` the even extent. -/
theorem corrNum_refl_eq_pairingG (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    (F H : (Link d n → G) → ℝ) :
    (GaugeWilson.sysWilsonG G d n).corrNum (probHaar G) β
        (fun U => F U * H (reflConf τ (a + a) U))
      = pairingG τ a m β (dressedG τ a m β F) (dressedG τ a m β H) := by
  symm
  show (∫ U, wPlaneG τ a m β U * dressedG τ a m β F U
          * dressedG τ a m β H (reflConf τ (a + a) U) ∂(cvol (Link d n) (probHaar G)))
    = ∫ U, (F U * H (reflConf τ (a + a) U)) * (GaugeWilson.sysWilsonG G d n).boltz β U
        ∂(cvol (Link d n) (probHaar G))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
  exact (integrand_eq_paired_obsG τ a m hm hm0 F H β U).symm

/-- **Reflection positivity of the Wilson Gibbs state of `G` on the slab algebra**:
`0 ≤ EWG G β (fun U => F U * F (reflConf τ (a + a) U))` for every `F` of
`localObs (blkS τ a m) (blkR τ a m)`, at every real `β`, at even extent `n = 2 * m`.

DERIVED: `0` the strict lower bound on `m` and the sign concluded; `2` in `n = 2 * m` the even
extent. -/
theorem wilson_expect_nonneg_moduleG (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {F : (Link d n → G) → ℝ} (hF : F ∈ localObs (blkS τ a m) (blkR τ a m)) :
    0 ≤ GaugeWilson.EWG G (d := d) (n := n) β (fun U => F U * F (reflConf τ (a + a) U)) := by
  have hZ : 0 < (GaugeWilson.sysWilsonG G d n).partition (probHaar G) β :=
    GaugeWilson.wilsonSystemG_partition_pos (bd (d := d) (n := n)) β
  have hN : 0 ≤ (GaugeWilson.sysWilsonG G d n).corrNum (probHaar G) β
      (fun U => F U * F (reflConf τ (a + a) U)) := by
    rw [corrNum_refl_eq_pairingG τ a m hm hm0 β F F]
    exact pairingG_nonneg τ a m hm hm0 β (dressedG_mem τ a m hm hm0 β hF)
  show 0 ≤ (GaugeWilson.sysWilsonG G d n).corrNum (probHaar G) β
      (fun U => F U * F (reflConf τ (a + a) U))
    / (GaugeWilson.sysWilsonG G d n).partition (probHaar G) β
  exact div_nonneg hN (le_of_lt hZ)

end Positive

/-! ## 3. The torus states and their limits -/

section Torus

open MassGap.InfiniteLattice

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **An observable of the half-space reads the periodic site slab**: if `f` is local on a finite `S`
inside `posHalf τ p` whose links are based at most `k` above the plane, then `torusObsG G (2k + 1) f`
belongs to `localObs (blkS τ a (k + 1)) (blkR τ a (k + 1))` at `a = finMod (2k + 1) p`.

DERIVED: the extent `2k + 1 + 1 = 2(k + 1)` is even, with half-extent `k + 1`; `4` the dimension. -/
theorem torusObsG_mem_localObs_even (k : ℕ) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf G, ℝ)) (S : Finset ILink)
    (hS : (S : Set ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p)
    (hloc : IsLocalOn S (f : MassGap.GibbsSpec.IConf G → ℝ))
    (hk : ∀ l ∈ S, l.2 τ - p ≤ (k : ℤ)) :
    GaugeWilson.torusObsG G (2 * k + 1) f
      ∈ localObs (blkS τ (finMod (2 * k + 1) p) (k + 1))
          (blkR τ (finMod (2 * k + 1) p) (k + 1)) := by
  refine mem_localObs.mpr
    ⟨GaugeWilson.measurable_torusObsG G (2 * k + 1) f, ?_, fun W W' hSeq hReq => ?_⟩
  · obtain ⟨C, hC⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
    exact ⟨C, fun W => hC _⟩
  · show f (pullback (2 * k + 1) W) = f (pullback (2 * k + 1) W')
    refine hloc (pullback (2 * k + 1) W) (pullback (2 * k + 1) W') (fun l hl => ?_)
    have hp : p ≤ l.2 τ := hS (Finset.mem_coe.mpr hl)
    have hle : l.2 τ - p ≤ (k : ℤ) := hk l hl
    have hlv : ((lv (finMod (2 * k + 1) p) (finMod (2 * k + 1) (l.2 τ)) : ℕ) : ℤ) = l.2 τ - p :=
      MassGap.PeriodicState.lv_finMod (2 * k + 1) (l.2 τ) p (by omega) (by push_cast; omega)
    have hb : lv (finMod (2 * k + 1) p) ((linkMod (2 * k + 1) l).2 τ) ≤ k := by
      show lv (finMod (2 * k + 1) p) (finMod (2 * k + 1) (l.2 τ)) ≤ k
      omega
    have hmem : linkMod (2 * k + 1) l
        ∈ blkS τ (finMod (2 * k + 1) p) (k + 1) ∪ blkR τ (finMod (2 * k + 1) p) (k + 1) := by
      rw [mem_blkS_union_blkR]
      split_ifs <;> omega
    show W (linkMod (2 * k + 1) l) = W' (linkMod (2 * k + 1) l)
    rcases Finset.mem_union.mp hmem with h | h
    · exact hSeq _ h
    · exact hReq _ h

/-- **Site-reflection positivity of the torus states of `G`, eventually**: for `f` in
`halfSpaceAlg τ p`, at every real `β`, eventually in `k`,
`0 ≤ torusStateG G (2k + 1) β (θ_{2p} f * f)`.

DERIVED: `2` in `2 * p` the plane-to-constant doubling; `2k + 1` the extent index; `0` the sign
concluded; `4` the dimension. -/
theorem torusStateG_reflPositive_even_eventually (β : ℝ) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf G, ℝ))
    (hf : f ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 ≤ GaugeWilson.torusStateG G (2 * k + 1) β
        ((MassGap.LatticeReflection.latticeReflection (G := G) τ (2 * p)).θ f * f) := by
  obtain ⟨S, hS, hloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  obtain ⟨K, hK⟩ := MassGap.PeriodicState.exists_depth_bound τ p S
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
  have hkS : ∀ l ∈ S, l.2 τ - p ≤ (k : ℤ) := fun l hl => by
    have := hK l hl
    omega
  have hrp := wilson_expect_nonneg_moduleG τ (finMod (2 * k + 1) p) (k + 1) (by omega) (by omega) β
    (torusObsG_mem_localObs_even G k τ p f S hS hloc hkS)
  have ha : finMod (2 * k + 1) (2 * p) = finMod (2 * k + 1) p + finMod (2 * k + 1) p := by
    rw [two_mul p, MassGap.PeriodicState.finMod_add]
  show 0 ≤ GaugeWilson.EWG G (d := 4) (n := 2 * k + 1 + 1) β
    (GaugeWilson.torusObsG G (2 * k + 1)
      ((MassGap.LatticeReflection.latticeReflection (G := G) τ (2 * p)).θ f * f))
  rw [MassGap.ReflInvG.torusObsG_refl_mul, ha]
  exact hrp

/-- **Every limit of the torus states of `G` along a non-trivial filter finer than `atTop` is
reflection positive at the constant `2p` on `halfSpaceAlg τ p`**, at every real `β`.

DERIVED: `2` in `2 * p` the plane-to-constant doubling; `2k + 1` the extent index; `4` the
dimension. -/
theorem reflPositive_even_of_tendsto_torusG (β : ℝ) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf G))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf G, ℝ),
      Filter.Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := G) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν :=
  MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _
    (fun f hf => (torusStateG_reflPositive_even_eventually G β τ p f hf).filter_mono hl)

/-- The ultrafilter of `periodicStateG G β` is finer than `atTop`.

DERIVED: no numeral. -/
theorem periodicUltraG_le (β : ℝ) :
    (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) : Filter ℕ)
      ≤ Filter.atTop :=
  le_trans (GaugeWilson.exists_periodic_limit_dvdG G β).choose_spec.choose_spec.1
    MassGap.PeriodicState.dyadicFilter_le_atTop

/-- **`periodicStateG G β` is reflection positive at the constant `2p` (mirror plane `x_τ = p`) on
`halfSpaceAlg τ p`**, at every real `β`: the mirror of `PeriodicState.periodicState_reflPositive`.

DERIVED: `2` in `2 * p` the plane-to-constant doubling; `4` the dimension. -/
theorem periodicStateG_reflPositive (β : ℝ) (τ : Fin 4) (p : ℤ) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := G) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p)
      (GaugeWilson.periodicStateG G β) := by
  haveI : (((GaugeWilson.exists_periodic_limit_dvdG G β).choose : Ultrafilter ℕ) :
      Filter ℕ).NeBot := (GaugeWilson.exists_periodic_limit_dvdG G β).choose.neBot'
  exact reflPositive_even_of_tendsto_torusG G β τ p (GaugeWilson.periodicStateG G β)
    (periodicUltraG_le G β) (MassGap.ShiftInvG.tendsto_periodicStateG G β)

/-- **Reflection positivity of `periodicStateG G β` at the plane `x_τ = 0`**, the mirror of
`ContinuumSchwinger.stateAlong_rp`: `0 ≤ periodicStateG G β (ireflObs τ 0 X * X)` for every `X` of
`halfSpaceAlg τ 0`, at every real `β`.

DERIVED: `0` the plane, the reflection constant and the sign concluded; `4` the dimension. -/
theorem periodicStateG_rp_zero (β : ℝ) (τ : Fin 4) (X : C(MassGap.GibbsSpec.IConf G, ℝ))
    (hX : X ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    0 ≤ GaugeWilson.periodicStateG G β (MassGap.LatticeReflection.ireflObs τ 0 X * X) := by
  have h := periodicStateG_reflPositive G β τ 0
  rw [mul_zero] at h
  exact h X hX

end Torus

/-! ## 4. Reflection positivity over a schedule -/

section Sched

open MassGap.ClayTreeG

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **A schedule whose states are reflection positive at the plane `x_τ = 0`**: for every step `k`,
direction `τ` and `X ∈ halfSpaceAlg τ 0`, `0 ≤ S.ν k (ireflObs τ 0 X * X)`.

DERIVED: `0` the plane, the reflection constant and the sign; `4` the dimension. -/
def SchedRP (S : Sched G) : Prop :=
  ∀ (k : ℕ) (τ : Fin 4) (X : C(MassGap.GibbsSpec.IConf G, ℝ)),
    X ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 →
      0 ≤ S.ν k (MassGap.LatticeReflection.ireflObs τ 0 X * X)

/-- **The canonical schedule of `G` is reflection positive**: `SchedRP (canonSched G)`, from
`periodicStateG_rp_zero` at the coupling `dyBetaG G k` of each step.

DERIVED: no numeral. -/
theorem schedRP_canonSched [GaugeSimple G] : SchedRP (canonSched G) :=
  fun k τ X hX => periodicStateG_rp_zero G (dyBetaG G k) τ X hX

/-- **The step form at the canonical schedule**, the mirror of `ContinuumSchwinger.stateK_rp`:
`0 ≤ (canonSched G).ν k (ireflObs τ 0 X * X)` for every `X ∈ halfSpaceAlg τ 0`.

DERIVED: `0` the plane and the sign concluded; `4` the dimension. -/
theorem canonSched_rp [GaugeSimple G] (k : ℕ) (τ : Fin 4) (X : C(MassGap.GibbsSpec.IConf G, ℝ))
    (hX : X ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0) :
    0 ≤ (canonSched G).ν k (MassGap.LatticeReflection.ireflObs τ 0 X * X) :=
  schedRP_canonSched k τ X hX

end Sched

end MassGap.ReflPosG

end

#print axioms MassGap.ReflPosG.hol_congr_on_supportG
#print axioms MassGap.ReflPosG.actSum_congrG
#print axioms MassGap.ReflPosG.sum_plqDeg_zeroG
#print axioms MassGap.ReflPosG.density_reflConfG
#print axioms MassGap.ReflPosG.sum_plqMinus_eq_plus_reflG
#print axioms MassGap.ReflPosG.action_eq_splitG
#print axioms MassGap.ReflPosG.measurable_actSumG
#print axioms MassGap.ReflPosG.abs_exp_actSumG_le
#print axioms MassGap.ReflPosG.wPlaneG_local
#print axioms MassGap.ReflPosG.actPlusG_local
#print axioms MassGap.ReflPosG.halfBoltzG_mem
#print axioms MassGap.ReflPosG.dressedG_mem
#print axioms MassGap.ReflPosG.pairingG_nonneg
#print axioms MassGap.ReflPosG.integrand_eq_paired_obsG
#print axioms MassGap.ReflPosG.corrNum_refl_eq_pairingG
#print axioms MassGap.ReflPosG.wilson_expect_nonneg_moduleG
#print axioms MassGap.ReflPosG.torusObsG_mem_localObs_even
#print axioms MassGap.ReflPosG.torusStateG_reflPositive_even_eventually
#print axioms MassGap.ReflPosG.reflPositive_even_of_tendsto_torusG
#print axioms MassGap.ReflPosG.periodicUltraG_le
#print axioms MassGap.ReflPosG.periodicStateG_reflPositive
#print axioms MassGap.ReflPosG.periodicStateG_rp_zero
#print axioms MassGap.ReflPosG.schedRP_canonSched
#print axioms MassGap.ReflPosG.canonSched_rp
