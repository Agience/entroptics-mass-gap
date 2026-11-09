import Mathlib
import MassGap.WDeltaRun
import MassGap.WilsonAnalytic
import MassGap.SeedZeroCoupling

/-!
# MassGap.DeltaLengthTower — the gap half along the theory's own scale

`defectW N β n = 16 log ZR(n⁴) − log ZR((2n)⁴)` is the doubling defect. The sharp seed is
`defectW N β n ≤ 1/1000` at an even side `n ≥ 2`. This module reads the seed on power-of-two sides
`2ᵇ`, `b ≥ 1`. There the seed climbs (`seedPow_mono`) and needs no torus-to-plane comparison
(`DoublingClay2.dyadicTorusDecay` covers every power-of-two seed).

* `continuous_defectW`: at fixed side the defect is continuous in `β`. The partition function is the
  correlator of the constant `1`, differentiable in `β` (`WilsonAnalytic.wilsonSystem_corrNum_hasDerivAt`),
  and positive (`WilsonReal.wilsonSystem_partition_pos`).
* `defectW_double_le`: one sharp squaring, `defectW(2n) ≤ 250 · defectW(n)² ≤ 1/4000`. So a seed at
  `2ᵇ` gives the seed at `2ᵇ⁺¹` with strict slack, and on a neighbourhood in `β`
  (`eventually_seed_succ`).
* `exists_crossing`: if `2ᵇ` is a seed at `a` and not at some `w ≥ a`, then some `β ≥ a` has no seed
  at `2ᵇ` and a seed at `2ᵇ⁺¹`. The Δ-length passes through every dyadic value.
* `tendsto_of_deltaLength`: where every coupling `≥ β₀` has a power-of-two seed, the Δ-length is
  locally bounded in `β`. So couplings whose Δ-length exceeds `2ᵏ` tend to infinity with `k`.
* **(A₂)** `SeedExistsPow N`: eventually in `β`, some `2ᵇ`, `b ≥ 1`, is a seed. One finite-volume
  statement per coupling, with no scale in it.
* **(B₂)** `DeltaLengthUnbounded N`: for every `b ≥ 1`, frequently in `β`, `2ᵇ` is not a seed.
  `deltaLengthUnbounded_of_scaleToZero` derives it from `ZoomSelfScale.ScaleToZero (nStar N)`.
* `exists_deltaLength_tower`: (A₂) and (B₂) give couplings `βs b → ∞` at which the Δ-length lies in
  `(2ᵇ, 2ᵇ⁺¹]` exactly: no seed at `2ᵇ`, a seed at `2ᵇ⁺¹`.
* `periodicClayGap_of_seedPow`: a seed at a power of two `n` gives the periodic Clay gap at rate
  `2^{−1/n}`, i.e. lattice mass at least `log 2 / n`.
* `selfScaledGap`: (A₂) and (B₂) give the tower `βs → ∞` with spacing `ℓ₀ / 2ᵇ⁺¹` at step `b`. At each
  step the periodic Clay gap holds at physical mass at least `log 2 / ℓ₀`, and the Δ-length is above
  `ℓ₀ / 2` in physical units.
* `towerGap_at_zero`: the gap clause alone, at spacing `ℓ₀ / 2ᵇ⁺¹`, holds at `β = 0` for every `b`
  (`SeedZeroCoupling.seed_at_zero`). Along a freely chosen coupling sequence the gap clause is
  therefore met by the ultralocal theory. The Δ-length lower bound in `selfScaledGap`, from (B₂), is
  what excludes it.
* `seedExistsPow_of_runSeed`: `WDeltaRun.RunSeed N` is (A₂) together with the bound `2ᵇ · aRun ≤ C` on
  the seed's side.

DERIVED (module-wide): `16 = 2⁴` and `2` are the doubling's; `1/1000` is the sharp seed of
`DoublingSharp`; `250` is `DoublingSharp.rec_sharp`'s; `1/4000 = 250 · (1/1000)²`; `1/2` is the
decay factor of `DoublingClay2.DyadicTorusDecay`; `0 0` in `PeriodicClayGapAt 0 0` are the time
direction and the reflection plane the dyadic decay is proved at; `1 ≤ b` makes `2ᵇ` even and at
least `2`; `b + 1` is the next dyadic side.
-/

noncomputable section

namespace MassGap.DeltaLengthTower

open Filter Topology MassGap MassGap.CompactGauge MassGap.DoublingRecursion MassGap.ZoomSelfScale

variable {N : ℕ}

/-! ## 1. The defect is continuous in the coupling -/

/-- The rectangular partition function is positive. -/
theorem ZR_pos (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) : 0 < RectWilson.ZR L N β :=
  WilsonReal.wilsonSystem_partition_pos hN (RectWilson.rbd L) β

/-- The rectangular partition function is continuous in the coupling: it is the correlator of the
constant `1`, which is differentiable in `β`. -/
theorem continuous_ZR (hN : N ≠ 0) (L : Fin 4 → ℕ) :
    Continuous (fun β => RectWilson.ZR L N β) := by
  refine continuous_iff_continuousAt.mpr fun β => ?_
  have h := WilsonAnalytic.wilsonSystem_corrNum_hasDerivAt hN (RectWilson.rbd L) β
    (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by simp)
  have e : (fun x => RectWilson.ZR L N x) = fun x =>
      (WilsonLattice.wilsonSystem (RectWilson.rbd L) (WilsonAction.wilsonDensity (N := N))).corrNum
        (probHaar (MassGap.SUN.SU N)) x (fun _ => 1) := by
    funext x
    simp only [RectWilson.ZR, RectWilson.sysR, LatticeGauge.System.corrNum,
      LatticeGauge.System.partition, one_mul]
    rfl
  rw [e]
  exact h.continuousAt

/-- **The doubling defect at a fixed side is continuous in the coupling.** -/
theorem continuous_defectW (hN : N ≠ 0) (n : ℕ) : Continuous (fun β => defectW N β n) := by
  unfold defectW
  exact (continuous_const.mul ((continuous_ZR hN _).log fun β => (ZR_pos hN _ β).ne')).sub
    ((continuous_ZR hN _).log fun β => (ZR_pos hN _ β).ne')

/-! ## 2. Power-of-two seeds -/

theorem two_le_two_pow {b : ℕ} (hb : 1 ≤ b) : 2 ≤ 2 ^ b :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb

theorem even_two_pow {b : ℕ} (hb : 1 ≤ b) : Even (2 ^ b) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

/-- **A power-of-two seed climbs**: a seed at `2ᵇ` is a seed at every `2ᶜ`, `c ≥ b`. -/
theorem seedPow_mono (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {b c : ℕ} (hb : 1 ≤ b) (hbc : b ≤ c)
    (h : defectW N β (2 ^ b) ≤ 1 / 1000) : defectW N β (2 ^ c) ≤ 1 / 1000 := by
  have := WDeltaRun.defectW_pow_le hN hβ (two_le_two_pow hb) (even_two_pow hb) h (c - b)
  rwa [← pow_add, Nat.sub_add_cancel hbc] at this

/-- **One sharp squaring**: a seed at an even side `n ≥ 2` gives `defectW(2n) ≤ 1/4000`. -/
theorem defectW_double_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : defectW N β n ≤ 1 / 1000) : defectW N β (2 * n) ≤ 1 / 4000 := by
  have hx := DoublingSharp.positiveS_of_facts (DoublingWilson.factRep hN hβ hn he)
  have hp := DoublingWilson.positive hN hβ hn he
  have h0 : Δ (DoublingWilson.xW N n β) (corner 0) ≤ 1 / 1000 := by
    rw [DoublingWilson.Δ_corner0]; exact h
  have hr := DoublingSharp.rec_sharp hx (corner 0) h0
  have hnn := Δ_nonneg hp (corner 0)
  have e1 : Δ (DoublingWilson.xW N n β) (corner 0 + one) = defectW N β (2 * n) := by
    rw [← corner_succ, WDeltaRun.Δ_corner]; norm_num
  rw [e1] at hr
  nlinarith

/-- **The next dyadic seed is open in the coupling.** A seed at `2ᵇ` at `β₀ ≥ 0` gives
`defectW N β (2ᵇ⁺¹) < 1/1000` for every `β` near `β₀`. -/
theorem eventually_seed_succ (hN : N ≠ 0) {β₀ : ℝ} (hβ : 0 ≤ β₀) {b : ℕ} (hb : 1 ≤ b)
    (h : defectW N β₀ (2 ^ b) ≤ 1 / 1000) :
    ∀ᶠ β in 𝓝 β₀, defectW N β (2 ^ (b + 1)) < 1 / 1000 := by
  have h2 := defectW_double_le hN hβ (two_le_two_pow hb) (even_two_pow hb) h
  have e : 2 * 2 ^ b = 2 ^ (b + 1) := by ring
  rw [e] at h2
  exact (((continuous_defectW hN (2 ^ (b + 1))).tendsto β₀).eventually
    (Iio_mem_nhds (by linarith))).mono fun _ h => h

/-! ## 3. The Δ-length passes through every dyadic value -/

/-- **The crossing.** If `2ᵇ` is a seed at `a ≥ 0` and not at some `w ≥ a`, some `β ≥ a` has no seed
at `2ᵇ` and a seed at `2ᵇ⁺¹`. Take `c` the last point of `[a, w]` with a seed at `2ᵇ`; past `c` there
is none, and near `c` there is one at `2ᵇ⁺¹` (`eventually_seed_succ`). -/
theorem exists_crossing (hN : N ≠ 0) {a w : ℝ} (ha : 0 ≤ a) (haw : a ≤ w) {b : ℕ} (hb : 1 ≤ b)
    (hsa : defectW N a (2 ^ b) ≤ 1 / 1000) (hw : 1 / 1000 < defectW N w (2 ^ b)) :
    ∃ β, a ≤ β ∧ 1 / 1000 < defectW N β (2 ^ b) ∧ defectW N β (2 ^ (b + 1)) ≤ 1 / 1000 := by
  set K : Set ℝ := Set.Icc a w ∩ {β | defectW N β (2 ^ b) ≤ 1 / 1000} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le (continuous_defectW hN _) continuous_const)
  have hKne : K.Nonempty := ⟨a, ⟨le_rfl, haw⟩, hsa⟩
  have hKb : BddAbove K := ⟨w, fun x hx => hx.1.2⟩
  set c := sSup K with hcdef
  have hc : c ∈ K := hKc.sSup_mem hKne
  have hac : a ≤ c := hc.1.1
  have hcw : c < w := by
    refine lt_of_le_of_ne hc.1.2 fun e => ?_
    have h2 : defectW N c (2 ^ b) ≤ 1 / 1000 := hc.2
    rw [e] at h2
    exact (not_le.mpr hw) h2
  have hc0 : 0 ≤ c := ha.trans hac
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_seed_succ hN hc0 hb hc.2)
  have hcβ : c < min (c + ε / 2) w := lt_min (by linarith) hcw
  have hβw : min (c + ε / 2) w ≤ w := min_le_right _ _
  have hdist : dist (min (c + ε / 2) w) c < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    have : min (c + ε / 2) w ≤ c + ε / 2 := min_le_left _ _
    linarith
  refine ⟨min (c + ε / 2) w, hac.trans hcβ.le, ?_, (hball hdist).le⟩
  by_contra hle
  push_neg at hle
  have hmem : min (c + ε / 2) w ∈ K := ⟨⟨hac.trans hcβ.le, hβw⟩, hle⟩
  have := le_csSup hKb hmem
  linarith

/-- **The Δ-length is locally bounded.** If every coupling `β ≥ β₀ ≥ 0` has a seed at some `2ᵇ`,
`b ≥ 1`, then couplings `βs k ≥ β₀` with no seed at `2ᵏ`, eventually in `k`, tend to infinity. On
`[β₀, B]` finitely many neighbourhoods carry a seed at a bounded dyadic side
(`eventually_seed_succ`, compactness), and the seed climbs (`seedPow_mono`). -/
theorem tendsto_of_deltaLength (hN : N ≠ 0) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hA : ∀ β, β₀ ≤ β → ∃ b : ℕ, 1 ≤ b ∧ defectW N β (2 ^ b) ≤ 1 / 1000)
    {βs : ℕ → ℝ} (hs : ∀ᶠ k in atTop, β₀ ≤ βs k ∧ 1 / 1000 < defectW N (βs k) (2 ^ k)) :
    Tendsto βs atTop atTop := by
  have hA' : ∀ x : ℝ, ∃ b : ℕ, β₀ ≤ x → 1 ≤ b ∧ defectW N x (2 ^ b) ≤ 1 / 1000 := by
    intro x
    by_cases hx : β₀ ≤ x
    · obtain ⟨b, hb⟩ := hA x hx
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose c hc using hA'
  refine tendsto_atTop.mpr fun B => ?_
  have hU : ∀ x ∈ Set.Icc β₀ B,
      (fun x => {β | defectW N β (2 ^ (c x + 1)) < 1 / 1000}) x ∈ 𝓝 x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hc x hx.1
    exact eventually_seed_succ hN (hβ₀.trans hx.1) h1 h2
  obtain ⟨t, -, hcover⟩ := isCompact_Icc.elim_nhds_subcover _ hU
  filter_upwards [hs, eventually_ge_atTop (t.sup fun x => c x + 1)] with k ⟨hk0, hk⟩ hkM
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover ⟨hk0, hlt.le⟩)
  have hle : c x + 1 ≤ k := le_trans (Finset.le_sup (f := fun x => c x + 1) hxt) hkM
  have hseed := seedPow_mono hN (hβ₀.trans hk0) (by omega) hle
    (show defectW N (βs k) (2 ^ (c x + 1)) < 1 / 1000 from hx).le
  linarith

/-! ## 4. The two statements and the tower -/

/-- **(A₂)**: eventually in `β`, some power of two `2ᵇ`, `b ≥ 1`, is a seed.
DERIVED: `1/1000` the sharp seed threshold of `DoublingSharp.rec_sharp`; `1 ≤ b` makes `2ᵇ` even. -/
def SeedExistsPow (N : ℕ) : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ defectW N β (2 ^ b) ≤ 1 / 1000

/-- **(B₂)**: for every `b ≥ 1`, frequently in `β`, `2ᵇ` is not a seed: the Δ-length is unbounded.
DERIVED: `1/1000` the sharp seed threshold of `DoublingSharp.rec_sharp`; `1 ≤ b` makes `2ᵇ` even. -/
def DeltaLengthUnbounded (N : ℕ) : Prop :=
  ∀ b : ℕ, 1 ≤ b → ∃ᶠ β in atTop, 1 / 1000 < defectW N β (2 ^ b)

/-- The least even seed side is at most any seed side. -/
theorem nStar_le {β : ℝ} {n : ℕ} (h : Seed N β n) : nStar N β ≤ n := by
  classical
  have hex : ∃ m, Seed N β m := ⟨n, h⟩
  have := Nat.find_min' hex h
  simpa [nStar, hex] using this

/-- `ScaleToZero (nStar N)` gives (B₂). -/
theorem deltaLengthUnbounded_of_scaleToZero (h : ScaleToZero (nStar N)) :
    DeltaLengthUnbounded N := by
  intro b hb
  refine (h.eventually (eventually_gt_atTop ((2 : ℝ) ^ b))).frequently.mono fun β hβ => ?_
  by_contra hle
  push_neg at hle
  have h1 : nStar N β ≤ 2 ^ b := nStar_le ⟨even_two_pow hb, two_le_two_pow hb, hle⟩
  have h2 : (nStar N β : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast h1
  linarith

/-- **The Δ-length tower.** (A₂) and (B₂) give couplings `βs b → ∞` with the Δ-length in
`(2ᵇ, 2ᵇ⁺¹]` at every large `b`. -/
theorem exists_deltaLength_tower (hN : N ≠ 0) (hA : SeedExistsPow N)
    (hU : DeltaLengthUnbounded N) :
    ∃ βs : ℕ → ℝ, Tendsto βs atTop atTop ∧ ∀ᶠ b in atTop, 0 ≤ βs b ∧
      1 / 1000 < defectW N (βs b) (2 ^ b) ∧ defectW N (βs b) (2 ^ (b + 1)) ≤ 1 / 1000 := by
  obtain ⟨β₁, hβ₁⟩ := eventually_atTop.mp hA
  obtain ⟨β₀, h0, hA0⟩ : ∃ β₀ : ℝ, 0 ≤ β₀ ∧
      ∀ β, β₀ ≤ β → ∃ b : ℕ, 1 ≤ b ∧ defectW N β (2 ^ b) ≤ 1 / 1000 :=
    ⟨max β₁ 0, le_max_right _ _, fun β hβ => hβ₁ β ((le_max_left _ _).trans hβ)⟩
  obtain ⟨b₀, hb₀, hs₀⟩ := hA0 β₀ le_rfl
  have hP : ∀ b : ℕ, ∃ β : ℝ, b₀ ≤ b → β₀ ≤ β ∧ 1 / 1000 < defectW N β (2 ^ b) ∧
      defectW N β (2 ^ (b + 1)) ≤ 1 / 1000 := by
    intro b
    by_cases hb : b₀ ≤ b
    · have hsb := seedPow_mono hN h0 hb₀ hb hs₀
      obtain ⟨w, hw, hwd⟩ := frequently_atTop.mp (hU b (hb₀.trans hb)) β₀
      obtain ⟨β, hβ, h1, h2⟩ := exists_crossing hN h0 hw (hb₀.trans hb) hsb hwd
      exact ⟨β, fun _ => ⟨hβ, h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose βs hβs using hP
  refine ⟨βs, tendsto_of_deltaLength hN h0 hA0 ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop b₀] with b hb
    exact ⟨(hβs b hb).1, (hβs b hb).2.1⟩
  · filter_upwards [eventually_ge_atTop b₀] with b hb
    exact ⟨h0.trans (hβs b hb).1, (hβs b hb).2.1, (hβs b hb).2.2⟩

/-! ## 5. The gap at a power-of-two seed, and along the tower -/

/-- **The periodic Clay gap from a power-of-two seed**, at rate `2^{−1/n}`: lattice mass at least
`log 2 / n`. `DoublingClay2.dyadicTorusDecay` gives the lag-`n` decay by `½`;
`WeakCouplingWindow.torusLagClear_iff_gapAt` turns it into `GapAt` and
`GapStep.periodic_clayGapAt_of_gapAt` into the Clay gap. -/
theorem periodicClayGap_of_seedPow (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hp : PeriodicState.IsPow2 n) (hn : 2 ≤ n) (hs : defectW N β n ≤ 1 / 1000) :
    ∃ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 hN β r ∧ Real.log 2 / n ≤ -Real.log r := by
  have hm : n ≠ 0 := by omega
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hg : TransferGap.GapAt (PeriodicState.periodicGaugeInvData 0 0 hN β)
      (WeakCouplingWindow.stepRate (1 / 2) n) :=
    (WeakCouplingWindow.torusLagClear_iff_gapAt 0 0 hN hβ hm
      (WeakCouplingWindow.stepRate_pos hq0 n).le).mp
      (WeakCouplingWindow.torusLagClear_stepRate 0 0 hN β hq0.le hm
        (fun x hx ε hε => DoublingClay2.dyadicTorusDecay hN β hβ n hp hn hs x hx ε hε))
  refine ⟨_, GapStep.periodic_clayGapAt_of_gapAt 0 0 hN2 hN hβ
    (WeakCouplingWindow.stepRate_pos hq0 n)
    (WeakCouplingWindow.stepRate_lt_one hq0.le (by norm_num) hm) hg, ?_⟩
  rw [WeakCouplingWindow.neg_log_stepRate hq0 n, one_div (2 : ℝ), Real.log_inv, neg_neg]

/-- **The gap at one tower step**: a seed at `2ᵇ⁺¹` gives the periodic Clay gap at physical mass at
least `log 2 / ℓ₀` at spacing `ℓ₀ / 2ᵇ⁺¹`. -/
theorem towerGap (hN2 : 2 ≤ N) (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) {β : ℝ} (hβ : 0 ≤ β) {b : ℕ}
    (hs : defectW N β (2 ^ (b + 1)) ≤ 1 / 1000) :
    ∃ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 hN β r ∧
      Real.log 2 / ℓ₀ ≤ -Real.log r / (ℓ₀ / 2 ^ (b + 1)) := by
  obtain ⟨r, hcl, hr⟩ :=
    periodicClayGap_of_seedPow hN2 hN hβ ⟨b + 1, rfl⟩ (two_le_two_pow (by omega)) hs
  refine ⟨r, hcl, ?_⟩
  have hn : (0 : ℝ) < ((2 ^ (b + 1) : ℕ) : ℝ) := by positivity
  have h1 : Real.log 2 ≤ -Real.log r * ((2 ^ (b + 1) : ℕ) : ℝ) := (div_le_iff₀ hn).mp hr
  push_cast at h1
  rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hℓ]
  linarith

/-- **The gap half along the theory's own scale.** (A₂) and (B₂) give couplings `βs b → ∞` such
that, eventually in `b`, at spacing `ℓ₀ / 2ᵇ⁺¹` the periodic Clay gap holds at physical mass at
least `log 2 / ℓ₀`, and `2ᵇ` is not a seed (the Δ-length exceeds `ℓ₀ / 2` in physical units). -/
theorem selfScaledGap (hN2 : 2 ≤ N) (hN : N ≠ 0) (hA : SeedExistsPow N)
    (hU : DeltaLengthUnbounded N) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) :
    ∃ βs : ℕ → ℝ, Tendsto βs atTop atTop ∧ ∀ᶠ b in atTop,
      (∃ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 hN (βs b) r ∧
        Real.log 2 / ℓ₀ ≤ -Real.log r / (ℓ₀ / 2 ^ (b + 1)))
      ∧ 1 / 1000 < defectW N (βs b) (2 ^ b) := by
  obtain ⟨βs, hT, hev⟩ := exists_deltaLength_tower hN hA hU
  exact ⟨βs, hT, hev.mono fun b ⟨h0, hlo, hhi⟩ => ⟨towerGap hN2 hN hℓ h0 hhi, hlo⟩⟩

/-- **The gap clause alone is met at zero coupling**, at every step `b`. A coupling sequence chosen
without the Δ-length lower bound can sit at `β = 0`, where the theory is ultralocal. -/
theorem towerGap_at_zero (hN2 : 2 ≤ N) (hN : N ≠ 0) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (b : ℕ) :
    ∃ r : ℝ, PeriodicContent.PeriodicClayGapAt 0 0 hN 0 r ∧
      Real.log 2 / ℓ₀ ≤ -Real.log r / (ℓ₀ / 2 ^ (b + 1)) :=
  towerGap hN2 hN hℓ le_rfl (SeedZeroCoupling.seed_at_zero N _)

/-- **`RunSeed` contains (A₂).** -/
theorem seedExistsPow_of_runSeed (h : WDeltaRun.RunSeed N) : SeedExistsPow N := by
  obtain ⟨C, _, hev⟩ := h
  filter_upwards [hev] with β ⟨n, ⟨b, hb⟩, h2, _, hd⟩
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; simp at hb; omega
    · exact h0
  exact ⟨b, hb1, by rw [← hb]; exact hd⟩

end MassGap.DeltaLengthTower

#print axioms MassGap.DeltaLengthTower.continuous_defectW
#print axioms MassGap.DeltaLengthTower.exists_crossing
#print axioms MassGap.DeltaLengthTower.tendsto_of_deltaLength
#print axioms MassGap.DeltaLengthTower.deltaLengthUnbounded_of_scaleToZero
#print axioms MassGap.DeltaLengthTower.exists_deltaLength_tower
#print axioms MassGap.DeltaLengthTower.periodicClayGap_of_seedPow
#print axioms MassGap.DeltaLengthTower.selfScaledGap
#print axioms MassGap.DeltaLengthTower.towerGap_at_zero
#print axioms MassGap.DeltaLengthTower.seedExistsPow_of_runSeed
