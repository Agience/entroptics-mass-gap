import Mathlib
import MassGap.CoarseBoundary

/-!
# MassGap.EffectiveDensityBound — one Prop on the exact effective density feeds `hW` and the coarse constant of `hpos`

The open clauses of `hpos` (1b) on the coarse route (`CoarseBoundary`) and of `hW` on the exact route
(`GapSideExactDecimation.ExactEffectiveSmall`) both ask for a bound on the same object: the exact effective density
`effIter` at a fixed coarse scale, uniform in the number of decimation steps. This module states that bound as one
Prop, `UnitOsc`, and proves what each ledger item gets from it.

## The shared Prop

`UnitOsc ρ cP cL`: the log of the density family `ρ`, read as one function of the background plaquettes and the
links together (index `TPlaq ⊕ TLink`), has per-unit oscillation `cP` at every background plaquette and `cL` at
every link (`CoarseBoundary.BlockOsc`). It is a statement about one density at one scale; the uniformity in `k` is
the statement that `cP` and `cL` do not depend on `k`.

## What is proved

* **The effective density stays positive** (`Banded`, `effStep_banded`, `effIter_banded`, `fineDens_banded`,
  `effIter_fineDens_pos`): a density family measurable and banded between two positive constants at every background
  stays so under every exact step; `fineDens Φ` of a continuous `Φ` is banded (compactness); so every
  `effIter k n (fineDens Φ)` is positive everywhere. The logs below are of positive numbers.
* **The two readings of `UnitOsc`.** `UnitOsc.link`: at a fixed background, the per-link log-oscillation in the
  links is `cL`. `UnitOsc.background`: at fixed links, two backgrounds that agree off `T` give log-densities within
  `|T| cP` (`abs_sub_le_sum_of_eqOn`, the block sum over the changed units only).
* **`hW`: `ExactEffectiveSmall` is the pointwise twist ratio, up to the factor `32`.** `EffRatioSmall η` is the
  pointwise bound `|log ρ_k(sheet_P, V) − log ρ_k(1, V)| ≤ η` at the first crossing.
  `exactEffectiveSmall_of_ratio`: `EffRatioSmall η` and `32 η ≤ ε` give `ExactEffectiveSmall ε`, through the
  one-polymer representation (`onePolymer`: `X = univ`, `R = log ρ_k`, `φ = 0`).
  `ratio_of_exactEffectiveSmall`: `ExactEffectiveSmall ε` gives `EffRatioSmall ε` (`abs_actP_sub_le`, the pointwise
  form of `GapSideExactDecimation.abs_FE_le_polymer`). So `ExactEffectiveSmall ε → EffRatioSmall ε →
  ExactEffectiveSmall (32 ε)`: the Prop of `hW` is the pointwise twist ratio of one density.
  `CrossingUnitOsc cP` (eventually in `β`, at the first crossing, `UnitOsc` of the side-`4` effective density with
  plaquette constant `cP`): `exactEffectiveSmall_of_crossingUnitOsc` gives `ExactEffectiveSmall ε` from
  `1024 cP ≤ ε` (`32` sheet plaquettes at side `4`, then the factor `32`).
* **`hpos` (1b): the per-block constant of a coarse reading** (`coarseRead_osc`). Blocks `ι` placed on coarse links
  `e b`, interior variables `z`, and a `join` that changes only link `e b` when block `b` changes: the reading of any
  interior observable `h` with values in `[lo, lo + δ]` under the weight `ρ ζ (join y z)` moves by at most
  `(1 − e^{−2 |ι| cL}) δ` between any two block configurations (`CoarseBoundary.coarseGibbs_osc` on
  `UnitOsc.link`). The constant contains `|ι|` and `cL` and nothing else; it is the `cb` clause of
  `CoarseBoundary.CoarseGibbsBound` with `cb = cL`.
* **The a priori flow of the shared Prop** (`unitOsc_effStep`, `unitOsc_effIter`): for a banded family, one exact
  step carries `UnitOsc ρ cP cL` to `UnitOsc (effStep ρ) (16 cP) cL`, and `k` steps to `(16^k cP, cL)`. The link
  constant passes unchanged (`CoarseBoundary.effStep_blockOsc_of_fine`); a coarse background plaquette is read by
  the fine plaquettes of `pullSet q` (`pullTw_eq_off`), at most `16` of them (`card_pullSet_le`; the plaquettes
  that carry a non-trivial pulled-back value are the `4` with odd coordinates in the plaquette plane, argued), and a
  pointwise log-ratio bound passes through the integral (`abs_log_integral_sub_le`).

## What is not proved

* `UnitOsc` itself, for the Wilson effective density, with `cP`, `cL` uniform in `k`. The a priori constants are
  the ones the flow carries from the finest torus: `cL` unchanged, which is `12 β_k` there (argued, as in
  `CoarseBoundary`: a link is in `6` plaquettes and the density is in `[0, 2]` per plaquette in Lean `β`), and `cP`
  multiplied by at most `16` per step. Neither shrinks along the flow; a `k`-uniform constant needs cancellation in
  the integral over the fine variables, which the per-unit bounds do not see.
* The bridge from `UnitOsc` of the torus effective density to `CoarseGibbsBound` on the infinite-volume box kernel:
  a screen invariant for both states whose reading factors through the effective density at scale `a_{k₀}`
  (argued; `CoarseBoundary`, open item 1). `coarseRead_osc` supplies the per-block constant of that reading, not
  the screen.

## The two mechanisms looked at (argued)

1. Two-sided MK sandwich. `HolderBondMoving.zF_le_moveField` gives `Z_true ≤ Z_moved`, an inequality between
   partition functions, and the tree has no reverse (lower) bound. A ratio of effective densities is bounded by
   such inequalities only when they hold at every fixed coarse configuration on both sides, `W⁻(V) ≤ ρ_k(V) ≤
   W⁺(V)`, with `W⁺/W⁻` controlled per link. The proved move is not of that form even on the upper side: it needs
   a field invariant along the move direction and uses the unit translation of the whole configuration
   (`integral_exp_move_le`), and fixing the coarse links breaks that invariance. A pointwise sandwich would need a
   different inequality on both sides; none is in the tree or supplied here.
2. Ratio of integrals. The coarse link enters one fine link (`CoarseBoundary.glueStep_eq_off`), and the integral
   over the second fine link `u₂` is a group convolution, `∫ f(V u₂⁻¹, u₂) du₂`. For a product `a(u₁) b(u₂)` its
   log-oscillation in `V` is at most the smaller of those of `a` and `b`: two links in series, effective coupling
   about half, not independent of `β`. Bond moving in four dimensions puts `2^{d−2} = 4` plaquettes' weight on each
   moved plaquette, and the series halving acts on each of its two directions, so the per-step change of the coupling
   is marginal: it runs logarithmically (asymptotic freedom), and a `k`-uniform `cL` at a fixed physical scale is the
   statement that this running is controlled through every step. That is the multi-scale content (Bałaban type),
   not a one-step cancellation.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.EffectiveDensityBound

open MeasureTheory Filter MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling
  MassGap.HolderBondMoving MassGap.ChainCoarseSeed MassGap.ChainFirstCrossing
  MassGap.ElectricStepChain MassGap.MovedTorusDecimation MassGap.ElectricExactProof
  MassGap.GapSideVortexAntiDiagonal MassGap.WilsonChainExists
  MassGap.GapSideExactDecimation MassGap.CoarseBoundary
open MassGap.TwistedTraceBound (negOne coe_negOne)

/-! ## 1. A block bound over the changed blocks only -/

section Diff

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- **Only the changed blocks count**: two configurations that agree off `s` give values within `Σ_{b ∈ s} ε b`. -/
theorem abs_sub_le_sum_of_eqOn {g : (∀ b, Y b) → ℝ} {ε : ι → ℝ} (h : BlockOsc g ε) (y y' : ∀ b, Y b)
    (s : Finset ι) (hs : ∀ b ∉ s, y b = y' b) : |g y - g y'| ≤ ∑ b ∈ s, ε b := by
  have e : mix s y y' = y' := by
    funext b
    by_cases hb : b ∈ s
    · simp [mix, hb]
    · simp [mix, hb, hs b hb]
  have := abs_sub_mix_le h y y' s
  rwa [e] at this

end Diff

/-! ## 2. The effective density stays positive -/

section Band

/-- **A banded density family**: at every background, measurable and between two positive constants. -/
def Banded {N : ℕ} (ρ : DensE N) : Prop :=
  ∀ ζ, Measurable (ρ ζ) ∧ ∃ a b : ℝ, 0 < a ∧ ∀ U, a ≤ ρ ζ U ∧ ρ ζ U ≤ b

/-- **One exact step keeps the band.** -/
theorem effStep_banded (n : ℕ) {ρ : DensE (2 * n)} (h : Banded ρ) : Banded (effStep n ρ) := by
  intro ζ
  obtain ⟨hm, a, b, ha, hab⟩ := h (pullTw ζ)
  have hmz : Measurable (fun z : (TLink 4 n → SU 2) × RestV n => ρ (pullTw ζ) (glueStep n z)) :=
    hm.comp (measurePreserving_glueStep n).measurable
  have hint : ∀ V, Integrable (fun R => ρ (pullTw ζ) (glueStep n (V, R))) (restM n) := fun V =>
    Integrable.mono' (integrable_const b)
      ((hmz.comp measurable_prodMk_left).aestronglyMeasurable)
      (Eventually.of_forall fun R => by
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le ha (hab _).1)]
        exact (hab _).2)
  refine ⟨?_, a, b, ha, fun V => ⟨?_, ?_⟩⟩
  · exact (hmz.stronglyMeasurable.integral_prod_right' (ν := restM n)).measurable
  · have h1 := integral_mono (integrable_const a) (hint V) (fun R => (hab (glueStep n (V, R))).1)
    rw [integral_const, probReal_univ, one_smul] at h1
    exact h1
  · have h1 := integral_mono (hint V) (integrable_const b) (fun R => (hab (glueStep n (V, R))).2)
    rw [integral_const, probReal_univ, one_smul] at h1
    exact h1

/-- **`k` exact steps keep the band.** -/
theorem effIter_banded : ∀ (k n : ℕ) (ρ : DensE (sideOf k n)), Banded ρ → Banded (effIter k n ρ)
  | 0, _, _, h => h
  | k + 1, n, ρ, h => by
    show Banded (effStep n (effIter k (2 * n) ρ))
    exact effStep_banded n (effIter_banded k (2 * n) ρ h)

/-- **The fine density of a continuous class field is banded** (a continuous function on a compact space). -/
theorem fineDens_banded {N : ℕ} {Φ : SU 2 → ℝ} (hΦ : Continuous Φ) : Banded (fineDens (N := N) Φ) := by
  intro ζ
  have hc := continuous_fineDens (N := N) hΦ ζ
  refine ⟨hc.measurable, ?_⟩
  have hne : (Set.univ : Set (TLink 4 N → SU 2)).Nonempty := ⟨fun _ => 1, Set.mem_univ _⟩
  obtain ⟨U₀, -, hU₀⟩ := isCompact_univ.exists_isMinOn hne hc.continuousOn
  obtain ⟨U₁, -, hU₁⟩ := isCompact_univ.exists_isMaxOn hne hc.continuousOn
  exact ⟨fineDens Φ ζ U₀, fineDens Φ ζ U₁, Real.exp_pos _, fun U =>
    ⟨isMinOn_iff.mp hU₀ U (Set.mem_univ U), isMaxOn_iff.mp hU₁ U (Set.mem_univ U)⟩⟩

/-- **Every exact effective density of a continuous class field is positive.** -/
theorem effIter_fineDens_pos {Φ : SU 2 → ℝ} (hΦ : Continuous Φ) (k n : ℕ) (ζ : TPlaq 4 n → SU 2)
    (V : TLink 4 n → SU 2) : 0 < effIter k n (fineDens Φ) ζ V := by
  obtain ⟨_, a, _, ha, hab⟩ := effIter_banded k n _ (fineDens_banded hΦ) ζ
  exact lt_of_lt_of_le ha (hab V).1

/-- **The sections integrated by one exact step of a banded family are positive and integrable.** -/
theorem banded_section {n : ℕ} {ρ : DensE (2 * n)} (h : Banded ρ) (ζ : TPlaq 4 (2 * n) → SU 2) :
    (∀ V R, 0 < ρ ζ (glueStep n (V, R))) ∧
      ∀ V, Integrable (fun R => ρ ζ (glueStep n (V, R))) (restM n) := by
  obtain ⟨hm, a, b, ha, hab⟩ := h ζ
  have hmz : Measurable (fun z : (TLink 4 n → SU 2) × RestV n => ρ ζ (glueStep n z)) :=
    hm.comp (measurePreserving_glueStep n).measurable
  refine ⟨fun V R => lt_of_lt_of_le ha (hab _).1, fun V => ?_⟩
  exact Integrable.mono' (integrable_const b)
    ((hmz.comp measurable_prodMk_left).aestronglyMeasurable)
    (Eventually.of_forall fun R => by
      rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le ha (hab _).1)]
      exact (hab _).2)

end Band

/-! ## 3. The shared Prop -/

section Unit

variable {N : ℕ}

/-- **The per-unit oscillation of the effective action.** The log of `ρ`, as one function of the background
plaquettes and the links (index `TPlaq ⊕ TLink`), moves by at most `cP` when one background plaquette changes and
by at most `cL` when one link changes. -/
def UnitOsc (ρ : DensE N) (cP cL : ℝ) : Prop :=
  BlockOsc (Y := fun _ : TPlaq 4 N ⊕ TLink 4 N => SU 2)
    (fun x => Real.log (ρ (fun q => x (Sum.inl q)) (fun l => x (Sum.inr l))))
    (Sum.elim (fun _ => cP) (fun _ => cL))

/-- **The link reading**: at a fixed background, the per-link log-oscillation is `cL`. -/
theorem UnitOsc.link {ρ : DensE N} {cP cL : ℝ} (h : UnitOsc ρ cP cL) (ζ : TPlaq 4 N → SU 2) :
    BlockOsc (Y := fun _ : TLink 4 N => SU 2) (fun V => Real.log (ρ ζ V)) (fun _ => cL) := by
  intro l V V' hV
  exact h (Sum.inr l) (Sum.elim ζ V) (Sum.elim ζ V') fun b hb => by
    cases b with
    | inl q => rfl
    | inr l' => exact hV l' fun e => hb (congrArg Sum.inr e)

/-- **The background reading**: at fixed links, two backgrounds that agree off `T` give log-densities within
`|T| cP`. -/
theorem UnitOsc.background {ρ : DensE N} {cP cL : ℝ} (h : UnitOsc ρ cP cL) (ζ ζ' : TPlaq 4 N → SU 2)
    (T : Finset (TPlaq 4 N)) (hT : ∀ q ∉ T, ζ q = ζ' q) (V : TLink 4 N → SU 2) :
    |Real.log (ρ ζ V) - Real.log (ρ ζ' V)| ≤ T.card * cP := by
  have := abs_sub_le_sum_of_eqOn h (Sum.elim ζ V) (Sum.elim ζ' V) (T.map Function.Embedding.inl)
    fun b hb => by
      cases b with
      | inl q => exact hT q fun hq => hb (Finset.mem_map_of_mem _ hq)
      | inr l => rfl
  rw [Finset.sum_map] at this
  have hs : ∑ x ∈ T, Sum.elim (fun _ : TPlaq 4 N => cP) (fun _ : TLink 4 N => cL)
      (Function.Embedding.inl x) = T.card * cP := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hs] at this
  exact this

end Unit

/-! ## 4. `hW`: `ExactEffectiveSmall` is the pointwise twist ratio -/

section Ratio

variable {N : ℕ}

/-- **The pointwise twist-odd action bound** of a polymer density: `|actP(ζ) − actP(1)| ≤ |T| δ + Σ_{q ∈ T}
Σ_{i : q ∈ S_i} D_i`, at every link configuration. -/
theorem abs_actP_sub_le (ζ : TPlaq 4 N → SU 2) (T : Finset (TPlaq 4 N))
    (hT : ∀ q ∉ T, ζ q = 1) {ι : Type} [Fintype ι] (φ : SU 2 → ℝ) (S : ι → Finset (TPlaq 4 N))
    (R : ι → (TPlaq 4 N → SU 2) → (TLink 4 N → SU 2) → ℝ)
    (hloc : ∀ i, (∀ q ∈ T, q ∉ S i) → ∀ V, R i ζ V = R i (fun _ => 1) V)
    {δ : ℝ} (hδ : ∀ q ∈ T, ∀ g, |φ (ζ q * g) - φ g| ≤ δ)
    (D : ι → ℝ) (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i V, |R i ζ V - R i (fun _ => 1) V| ≤ D i)
    (V : TLink 4 N → SU 2) :
    |actP φ R ζ V - actP φ R (fun _ => 1) V|
      ≤ T.card * δ + ∑ q ∈ T, ∑ i, (if q ∈ S i then D i else 0) := by
  have hnn : ∀ i q, 0 ≤ (if q ∈ S i then D i else 0) := fun i q => by
    split_ifs
    exacts [hD0 i, le_rfl]
  have hR1 : ∀ i, |R i ζ V - R i (fun _ => 1) V| ≤ ∑ q ∈ T, (if q ∈ S i then D i else 0) := by
    intro i
    by_cases hm : ∃ q ∈ T, q ∈ S i
    · obtain ⟨q0, hq0, hqS⟩ := hm
      calc |R i ζ V - R i (fun _ => 1) V| ≤ D i := hD i V
        _ = (if q0 ∈ S i then D i else 0) := (if_pos hqS).symm
        _ ≤ ∑ q ∈ T, (if q ∈ S i then D i else 0) :=
          Finset.single_le_sum (f := fun q => if q ∈ S i then D i else 0) (fun q _ => hnn i q) hq0
    · push Not at hm
      rw [hloc i hm V, sub_self, abs_zero]
      exact Finset.sum_nonneg fun q _ => hnn i q
  have hact : |fAct (fun q g => φ (ζ q * g)) V
      - fAct (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) V| ≤ T.card * δ := by
    refine GapSideSheetPolymer.fAct_sub_abs_le
      (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) (fun q g => φ (ζ q * g)) T ?_ ?_ V
    · intro q hq
      funext g
      simp only [hT q hq]
    · intro q hq g
      simp only [one_mul]
      exact hδ q hq g
  have h2 : |∑ i, R i ζ V - ∑ i, R i (fun _ => 1) V|
      ≤ ∑ q ∈ T, ∑ i, (if q ∈ S i then D i else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hR1 i).trans ?_
    exact (Finset.sum_comm).le
  have e : actP φ R ζ V - actP φ R (fun _ => 1) V
      = (fAct (fun q g => φ (ζ q * g)) V
          - fAct (fun q g => φ ((fun _ : TPlaq 4 N => (1 : SU 2)) q * g)) V)
        - (∑ i, R i ζ V - ∑ i, R i (fun _ => 1) V) := by
    unfold actP
    ring
  rw [e]
  exact (abs_sub _ _).trans (add_le_add hact h2)

/-- **The one-polymer representation**: the single polymer `X = univ` carries `log ρ`. -/
def onePolymer (ρ : DensE N) (X : Finset (TPlaq 4 N)) (ζ : TPlaq 4 N → SU 2) (V : TLink 4 N → SU 2) : ℝ :=
  if X = Finset.univ then Real.log (ρ ζ V) else 0

theorem sum_onePolymer (ρ : DensE N) (ζ : TPlaq 4 N → SU 2) (V : TLink 4 N → SU 2) :
    ∑ X, onePolymer ρ X ζ V = Real.log (ρ ζ V) := by
  rw [Finset.sum_eq_single (Finset.univ : Finset (TPlaq 4 N))]
  · exact if_pos rfl
  · intro X _ hX
    exact if_neg hX
  · intro hu
    exact absurd (Finset.mem_univ _) hu

/-- **The one-polymer representation is the density** wherever the density is positive. -/
theorem exp_neg_actP_onePolymer (ρ : DensE N) {ζ : TPlaq 4 N → SU 2} {V : TLink 4 N → SU 2}
    (hpos : 0 < ρ ζ V) : Real.exp (-actP (fun _ => 0) (onePolymer ρ) ζ V) = ρ ζ V := by
  have hf : fAct (fun q g => (fun _ : SU 2 => (0 : ℝ)) (ζ q * g)) V = 0 := by simp [fAct]
  unfold actP
  rw [hf, sum_onePolymer, zero_sub, neg_neg, Real.exp_log hpos]

/-- **The one polymer depends on the background only on its support** (its support is everything). -/
theorem onePolymer_local (ρ : DensE N) :
    ∀ (X : Finset (TPlaq 4 N)) (ζ1 ζ2 : TPlaq 4 N → SU 2), (∀ q ∈ X, ζ1 q = ζ2 q) →
      onePolymer ρ X ζ1 = onePolymer ρ X ζ2 := by
  intro X ζ1 ζ2 h
  funext V
  unfold onePolymer
  split_ifs with hX
  · subst hX
    rw [show ζ1 = ζ2 from funext fun q => h q (Finset.mem_univ q)]
  · rfl

/-- **The pointwise twist ratio at the first crossing**: eventually in `β`, at the first crossing `k`, for every
sheet plane and every link configuration of the side-`4` torus, the `k`-step exact effective density of the
Wilson weight `W₀` of the chain from `2β` changes its log by at most `η` when the sheet is put in.

DERIVED: Inherited: `1/1000` the doubling-defect seed of `ChainFirstCrossing.FirstCrossingComparison`. -/
def EffRatioSmall (η : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ (P : Plane) (V : TLink 4 4 → SU 2),
      |Real.log (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))
          (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) V)
        - Real.log (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))
          (fun _ => 1) V)| ≤ η

/-- **The pointwise twist ratio gives `ExactEffectiveSmall`** (the one-polymer representation, `32 η ≤ ε`). -/
theorem exactEffectiveSmall_of_ratio {η ε : ℝ} (h : EffRatioSmall η) (hε : 32 * η ≤ ε) :
    ExactEffectiveSmall ε := by
  filter_upwards [h] with β hβ
  intro k hk hmin P
  have hr := hβ k hk hmin P
  have hpos : ∀ ζ V, 0 < effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau)) ζ V :=
    effIter_fineDens_pos (continuous_halfField (wilsonChainOf (2 * β)) 0) k 4
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hr fun _ => 1)
  refine ⟨fun _ => 0,
    onePolymer (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))),
    fun X => if X = Finset.univ then η else 0, 0, η, ?_, onePolymer_local _, ?_, ?_, ?_, ?_, hη0,
    by linarith⟩
  · intro ζ' _ V
    exact (exp_neg_actP_onePolymer _ (hpos ζ' V)).symm
  · intro g
    simp
  · intro X
    show 0 ≤ (if X = Finset.univ then η else 0)
    split_ifs
    exacts [hη0, le_rfl]
  · intro X V
    show |onePolymer _ X _ V - onePolymer _ X _ V| ≤ (if X = Finset.univ then η else 0)
    unfold onePolymer
    split_ifs
    · exact hr V
    · simp
  · intro q _
    rw [Finset.sum_eq_single (Finset.univ : Finset (TPlaq 4 4))]
    · simp
    · intro X _ hX
      simp [hX]
    · intro hu
      exact absurd (Finset.mem_univ _) hu

/-- **`ExactEffectiveSmall` gives the pointwise twist ratio** with the same `ε`. -/
theorem ratio_of_exactEffectiveSmall {ε : ℝ} (h : ExactEffectiveSmall ε) : EffRatioSmall ε := by
  filter_upwards [h] with β hβ
  intro k hk hmin P V
  obtain ⟨φ, R, D, δ, η, hform, hloc, hδ, hD0, hD, hη, hη0, hε⟩ := hβ k hk hmin P
  rw [hform _ (Or.inl rfl) V, hform _ (Or.inr rfl) V, Real.log_exp, Real.log_exp, neg_sub_neg,
    abs_sub_comm]
  have hb := abs_actP_sub_le (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne)
    (GapSideSheetPolymer.sheetSet P.1.1 P.1.2)
    (fun q hq => sheet_off _ _ q hq) φ (fun X => X) R
    (fun X hX V => congrFun (hloc X _ _ (fun q hqX => sheet_off _ _ q (fun hqT => hX q hqT hqX))) V)
    (δ := δ) (fun q hq g => by rw [sheet_on _ _ q hq]; exact hδ g) D hD0 hD V
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 1)
  have hc : ((GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card : ℝ) ≤ 32 := by
    have h1 : (GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card ≤ 32 :=
      (GapSideSheetPolymer.card_sheetSet_le (N := 4) (ne_of_lt P.2)).trans (by norm_num)
    exact_mod_cast h1
  have hs : ∑ q ∈ GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2,
      ∑ X, (if q ∈ X then D X else 0)
      ≤ (GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card * η := by
    calc _ ≤ ∑ _q ∈ GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2, η := Finset.sum_le_sum hη
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have m1 := mul_le_mul_of_nonneg_right hc hδ0
  have m2 := mul_le_mul_of_nonneg_right hc hη0
  linarith

/-- **The shared Prop at the crossing**: eventually in `β`, at the first crossing `k`, the side-`4` exact
effective density of `W₀` has per-unit oscillation with background-plaquette constant `cP`.

DERIVED: Inherited: `1/1000` the doubling-defect seed of `ChainFirstCrossing.FirstCrossingComparison`. -/
def CrossingUnitOsc (cP : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∃ cL : ℝ, UnitOsc (effIter k 4 (fineDens (halfField ((wilsonChainOf (2 * β)).W 0) suTau))) cP cL

/-- **The shared Prop gives the pointwise twist ratio** with `η = 32 cP` (at most `32` sheet plaquettes at
side `4`). -/
theorem ratio_of_crossingUnitOsc {cP : ℝ} (h : CrossingUnitOsc cP) (hcP : 0 ≤ cP) :
    EffRatioSmall (32 * cP) := by
  filter_upwards [h] with β hβ
  intro k hk hmin P V
  obtain ⟨cL, hU⟩ := hβ k hk hmin
  have hb := hU.background (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne) (fun _ => 1)
    (GapSideSheetPolymer.sheetSet P.1.1 P.1.2) (fun q hq => sheet_off _ _ q hq) V
  have hc : ((GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card : ℝ) ≤ 32 := by
    have h1 : (GapSideSheetPolymer.sheetSet (N := 4) P.1.1 P.1.2).card ≤ 32 :=
      (GapSideSheetPolymer.card_sheetSet_le (N := 4) (ne_of_lt P.2)).trans (by norm_num)
    exact_mod_cast h1
  have m := mul_le_mul_of_nonneg_right hc hcP
  linarith

/-- **The shared Prop gives `hW`'s input**: `CrossingUnitOsc cP` with `1024 cP ≤ ε` gives
`ExactEffectiveSmall ε`. -/
theorem exactEffectiveSmall_of_crossingUnitOsc {cP ε : ℝ} (h : CrossingUnitOsc cP) (hcP : 0 ≤ cP)
    (hε : 1024 * cP ≤ ε) : ExactEffectiveSmall ε :=
  exactEffectiveSmall_of_ratio (ratio_of_crossingUnitOsc h hcP) (by linarith)

end Ratio

/-! ## 5. `hpos` (1b): the per-block constant of a coarse reading -/

section Coarse

/-- **The per-block constant of a coarse reading from the shared Prop.** Blocks `ι` sit on coarse links `e b`;
`join y z` assembles the coarse configuration from the block variables `y` and the interior variables `z`, and
changing block `b` alone changes only link `e b`. The reading of an interior observable `h` with values in
`[lo, lo + δ]` under the weight `ρ ζ (join y z)` moves by at most `(1 − e^{−2 |ι| cL}) δ` between any two block
configurations. The constant contains `|ι|` and `cL` only. -/
theorem coarseRead_osc {n : ℕ} {ρ : DensE n} {cP cL : ℝ} (hρ : UnitOsc ρ cP cL) (hcL : 0 ≤ cL)
    (ζ : TPlaq 4 n → SU 2) {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → TLink 4 n)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (join : (ι → SU 2) → Z → TLink 4 n → SU 2)
    (hjoin : ∀ z b (y y' : ι → SU 2), (∀ b', b' ≠ b → y b' = y' b') →
      ∀ l, l ≠ e b → join y z l = join y' z l)
    (h : Z → ℝ) {lo δ : ℝ} (hw : ∀ y z, 0 < ρ ζ (join y z))
    (iw : ∀ y, Integrable (fun z => ρ ζ (join y z)) μ)
    (ihw : ∀ y, Integrable (fun z => h z * ρ ζ (join y z)) μ)
    (hZ : ∀ y, 0 < ∫ z, ρ ζ (join y z) ∂μ) (hh : ∀ z, lo ≤ h z ∧ h z ≤ lo + δ) (y y' : ι → SU 2) :
    |wRead μ h (fun z => ρ ζ (join y z)) - wRead μ h (fun z => ρ ζ (join y' z))|
      ≤ (1 - Real.exp (-(2 * (Fintype.card ι * cL)))) * δ := by
  have hosc : ∀ z, BlockOsc (Y := fun _ : ι => SU 2) (fun y => Real.log (ρ ζ (join y z)))
      (fun _ => cL) :=
    fun z b y y' hy => hρ.link ζ (e b) (join y z) (join y' z) (hjoin z b y y' hy)
  have := coarseGibbs_osc (μ := μ) (Y := fun _ : ι => SU 2) h (fun y z => ρ ζ (join y z)) hw iw ihw
    hZ hh hosc (fun _ => hcL) y y'
  have hs : ∑ _b : ι, cL = Fintype.card ι * cL := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rwa [hs] at this

end Coarse

/-! ## 6. The a priori flow of the shared Prop -/

section Flow

/-- The fine plaquettes of the coarse plaquette `q` under `x ↦ ⌊x/2⌋`: same orientation, coarse site `q.2`. -/
def pullSet {n : ℕ} (q : TPlaq 4 n) : Finset (TPlaq 4 (2 * n)) :=
  Finset.univ.filter fun q' => q'.1 = q.1 ∧ halfSite q'.2 = q.2

/-- **A coarse plaquette changes the pulled-back background only on its fine plaquettes.** -/
theorem pullTw_eq_off {n : ℕ} (ζ ζ' : TPlaq 4 n → SU 2) (q : TPlaq 4 n)
    (h : ∀ q₀, q₀ ≠ q → ζ q₀ = ζ' q₀) (q' : TPlaq 4 (2 * n)) (hq' : q' ∉ pullSet q) :
    pullTw ζ q' = pullTw ζ' q' := by
  unfold pullTw
  split_ifs
  · apply h
    intro e
    apply hq'
    simp only [pullSet, Finset.mem_filter, Finset.mem_univ, true_and]
    subst e
    exact ⟨rfl, rfl⟩
  · rfl

/-- **At most `16` fine plaquettes per coarse plaquette** (a fine site is its coarse site and four parities). -/
theorem card_pullSet_le {n : ℕ} (q : TPlaq 4 n) : (pullSet q).card ≤ 16 := by
  have hinj : Set.InjOn (fun q' : TPlaq 4 (2 * n) => fun i : Fin 4 =>
      (⟨(q'.2 i).val % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) (pullSet q : Set (TPlaq 4 (2 * n))) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [pullSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine Prod.ext (ha1.trans hb1.symm) (funext fun i => Fin.ext ?_)
    have h2 : (a.2 i).val / 2 = (b.2 i).val / 2 := by
      have := congrArg (fun x => (x i).val) (ha2.trans hb2.symm)
      simpa [halfSite] using this
    have h3 : (a.2 i).val % 2 = (b.2 i).val % 2 := by
      have := congrArg Fin.val (congrFun hab i)
      simpa using this
    omega
  calc (pullSet q).card ≤ (Finset.univ : Finset (Fin 4 → Fin 2)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => by simp) hinj
    _ = 16 := by simp

/-- **A pointwise log-ratio bound passes through the integral** (probability measure, positive integrands). -/
theorem abs_log_integral_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : ∀ x, 0 < f x) (hg : ∀ x, 0 < g x) (if' : Integrable f μ) (ig : Integrable g μ)
    {c : ℝ} (h : ∀ x, |Real.log (f x) - Real.log (g x)| ≤ c) :
    |Real.log (∫ x, f x ∂μ) - Real.log (∫ x, g x ∂μ)| ≤ c := by
  have hI : ∀ {u : Ω → ℝ}, (∀ x, 0 < u x) → Integrable u μ → 0 < ∫ x, u x ∂μ := fun {u} hu iu => by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hu x).le) iu]
    rw [show Function.support u = Set.univ from Set.eq_univ_of_forall fun x => (hu x).ne',
      measure_univ]
    exact one_pos
  have r : ∀ x, Real.exp (-c) * f x ≤ g x ∧ g x ≤ Real.exp c * f x :=
    fun x => ratio_of_log (hf x) (hg x) (h x)
  have h1 : ∫ x, g x ∂μ ≤ Real.exp c * ∫ x, f x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono ig (if'.const_mul _) fun x => (r x).2
  have h2 : Real.exp (-c) * ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (if'.const_mul _) ig fun x => (r x).1
  exact abs_log_le_of_ratio (hI hf if') (hI hg ig) h2 h1

/-- **One exact step carries the shared Prop**, with the link constant unchanged and the background constant at
most `16` times larger (one coarse plaquette is read by at most `16` fine ones). -/
theorem unitOsc_effStep {n : ℕ} {ρ : DensE (2 * n)} {cP cL : ℝ} (h : UnitOsc ρ cP cL) (hcP : 0 ≤ cP)
    (hb : Banded ρ) : UnitOsc (effStep n ρ) (16 * cP) cL := by
  intro b x x' hx
  cases b with
  | inl q =>
    have hV : (fun l => x (Sum.inr l)) = (fun l => x' (Sum.inr l)) :=
      funext fun l => hx (Sum.inr l) Sum.inr_ne_inl
    have hζ : ∀ q₀, q₀ ≠ q → x (Sum.inl q₀) = x' (Sum.inl q₀) :=
      fun q₀ hq₀ => hx (Sum.inl q₀) fun e => hq₀ (Sum.inl_injective e)
    show |Real.log (effStep n ρ (fun q => x (Sum.inl q)) (fun l => x (Sum.inr l)))
      - Real.log (effStep n ρ (fun q => x' (Sum.inl q)) (fun l => x' (Sum.inr l)))| ≤ 16 * cP
    rw [hV]
    unfold effStep effDens
    have s1 := banded_section hb (pullTw fun q => x (Sum.inl q))
    have s2 := banded_section hb (pullTw fun q => x' (Sum.inl q))
    refine abs_log_integral_sub_le (restM n) (s1.1 _) (s2.1 _) (s1.2 _) (s2.2 _) fun R => ?_
    have hbg := h.background (pullTw fun q => x (Sum.inl q)) (pullTw fun q => x' (Sum.inl q))
      (pullSet q) (pullTw_eq_off _ _ q hζ) (glueStep n (fun l => x' (Sum.inr l), R))
    have hc : ((pullSet q).card : ℝ) ≤ 16 := by exact_mod_cast card_pullSet_le q
    have m := mul_le_mul_of_nonneg_right hc hcP
    linarith
  | inr l =>
    have hζ : (fun q => x (Sum.inl q)) = (fun q => x' (Sum.inl q)) :=
      funext fun q => hx (Sum.inl q) Sum.inl_ne_inr
    show |Real.log (effStep n ρ (fun q => x (Sum.inl q)) (fun l => x (Sum.inr l)))
      - Real.log (effStep n ρ (fun q => x' (Sum.inl q)) (fun l => x' (Sum.inr l)))| ≤ cL
    rw [hζ]
    have s := banded_section hb (pullTw fun q => x' (Sum.inl q))
    exact effStep_blockOsc_of_fine n ρ (fun q => x' (Sum.inl q)) s.1 s.2
      (h.link (pullTw fun q => x' (Sum.inl q))) l (fun l => x (Sum.inr l)) (fun l => x' (Sum.inr l))
      fun l' hl' => hx (Sum.inr l') fun e => hl' (Sum.inr_injective e)

/-- **`k` exact steps carry the shared Prop**: link constant unchanged, background constant at most `16^k`
times larger. -/
theorem unitOsc_effIter : ∀ (k n : ℕ) (ρ : DensE (sideOf k n)) {cP cL : ℝ}, Banded ρ →
    UnitOsc ρ cP cL → 0 ≤ cP → UnitOsc (effIter k n ρ) (16 ^ k * cP) cL
  | 0, _, _, _, _, _, h, _ => by
    rw [pow_zero, one_mul]
    exact h
  | k + 1, n, ρ, cP, cL, hb, h, hcP => by
    show UnitOsc (effStep n (effIter k (2 * n) ρ)) _ cL
    have ih := unitOsc_effIter k (2 * n) ρ hb h hcP
    have := unitOsc_effStep ih (mul_nonneg (pow_nonneg (by norm_num) k) hcP)
      (effIter_banded k (2 * n) ρ hb)
    rw [pow_succ, mul_comm (16 ^ k) 16, mul_assoc]
    exact this

end Flow

end MassGap.EffectiveDensityBound

end

#print axioms MassGap.EffectiveDensityBound.abs_sub_le_sum_of_eqOn
#print axioms MassGap.EffectiveDensityBound.effStep_banded
#print axioms MassGap.EffectiveDensityBound.effIter_banded
#print axioms MassGap.EffectiveDensityBound.fineDens_banded
#print axioms MassGap.EffectiveDensityBound.effIter_fineDens_pos
#print axioms MassGap.EffectiveDensityBound.UnitOsc.link
#print axioms MassGap.EffectiveDensityBound.UnitOsc.background
#print axioms MassGap.EffectiveDensityBound.abs_actP_sub_le
#print axioms MassGap.EffectiveDensityBound.sum_onePolymer
#print axioms MassGap.EffectiveDensityBound.exp_neg_actP_onePolymer
#print axioms MassGap.EffectiveDensityBound.onePolymer_local
#print axioms MassGap.EffectiveDensityBound.exactEffectiveSmall_of_ratio
#print axioms MassGap.EffectiveDensityBound.ratio_of_exactEffectiveSmall
#print axioms MassGap.EffectiveDensityBound.ratio_of_crossingUnitOsc
#print axioms MassGap.EffectiveDensityBound.exactEffectiveSmall_of_crossingUnitOsc
#print axioms MassGap.EffectiveDensityBound.coarseRead_osc
#print axioms MassGap.EffectiveDensityBound.banded_section
#print axioms MassGap.EffectiveDensityBound.pullTw_eq_off
#print axioms MassGap.EffectiveDensityBound.card_pullSet_le
#print axioms MassGap.EffectiveDensityBound.abs_log_integral_sub_le
#print axioms MassGap.EffectiveDensityBound.unitOsc_effStep
#print axioms MassGap.EffectiveDensityBound.unitOsc_effIter
