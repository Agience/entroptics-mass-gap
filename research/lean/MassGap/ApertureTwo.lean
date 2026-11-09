import Mathlib
import MassGap.ApertureBridge
import MassGap.EnergySeed

/-!
# MassGap.ApertureTwo — the four aperture remainders against one far and one near statement

`ApertureBridge.Aperture` is the conjunction of four remainders: the volume clause of `hpos`
(`PassageLow.RefPassageLow`), the physical-side doubling defect of `hW` (`ApertureBridge.PhysDefect`), and the
two short-distance clauses of `hD` (`DiagBoundRunning.ScaleUpAlong`, `ShortDistanceRunning.PointCubeLocalAlong`).
This module asks which of them follow from one far statement and one near statement.

## Near: one statement (proved)

`Near hN βs O s₀` is `PointReadingRatio.PointRatioAlong hN βs O s₀ s₀`: every unit-strength reflected point
reading at margin `d`, read against the reference reading at the aperture scale `s₀`, is at most `C · a_k^{8n}`
eventually in the step. It is one relative criterion, with one constant per list and margin.

* `near_of_scaleUp_pointCube`: `ScaleUpAlong ∧ PointCubeLocalAlong ⇒ Near`.
* `diagBoundSep_of_near`: `Near ⇒` `hD` at the single factor `zCanAlong` (`DiagBoundSepAlong`). `Near` is the
  existing `PointRatioAlong`, the point form of that `hD`. At `zCan` it inherits the single-factor defect (a field
  `~ p^s`, `s < 1`, read against the plaquette; `DiagBoundGram.sqrtPlaq_ratio_of_diagBoundSep_planePlaq`); the
  pinned target is the per-field `ExistenceReduceOwn.clay_canonical_own`.
* `scaleUp_of_near`: at an eventually positive reference reading, `Near ⇒ ScaleUpAlong`.
* `pointCube_of_near_scaleDown`: `Near ∧ ScaleDownAlong ⇒ PointCubeLocalAlong`.

So the scale clause is a consequence of `Near`, and the field clause is a consequence of `Near` plus the reverse
scale comparison. The split into a scale clause and a field clause at an intermediate scale `d` is a choice of
route, not two remainders: the near remainder of the pinned path is `Near`, one statement.

Per field (the re-pin). `NearOwn hN βs s₀` reads every list against the product of each field's own reference
reading at `s₀`. `nearOwn_of_own`: `ApertureBridge.ScaleUpOwnAlong ∧ ApertureBridge.PointCubeOwnAlong ⇒
NearOwn`. On a constant list it is `Near` at that field (`ApertureBridge.prod_own_const`). Its consumer, `hD` at the
per-field factor, is `ApertureFinal.diagBoundSep_zOwn_of_nearOwn`.

## Far: not one statement in the tree (proved parts, and a no-go)

`hW`'s far clause is relative finite-size extensivity of the Wilson torus.
`farRel_physDefect`: `FarRel L δ ⇒ PhysDefect L δ`, where `FarRel` asks that, at every coupling below `β`, the mean
action of the doubled torus exceed `16` copies of the side-`n` torus's by at most the fraction
`δ / (16 F_n(β))` of the latter, `F_n(β) = −log Z_n(β)` the free energy of the side-`n` torus
(`defectW_le_rel`: the defect is at most `16 η F_n(β)` when the relative excess is at most `η` on `[0, β)`).
Since `defectW = ∫₀^β finiteSize` exactly, `FarRel` is the pointwise form of `∫ finiteSize ≤ δ` with the budget
spread along the density `⟨S⟩_n / F_n(β)`: a strengthening of `PhysDefect`, not a weaker far input.

`hpos`'s far clause compares the reference reading on the torus `stateT` with the infinite-volume one. Both are a
torus reading against a larger-volume reading, but they read different functionals (the mean action against the
reference cube-pair reading) on different families (the rectangular Wilson tori at real `β`, the cubic torus
states at `dyBeta k`), and no lemma in the tree passes from one to the other.

The transfer model (`Model` section) places both on one torus and shows what one far statement can and cannot
carry. Eigenvalue ratios `r i = λ_i/λ_0 ∈ [0, 1]`, `r 0 = 1`; the torus of length `n` has `Z = Σ r_iⁿ`, a diagonal
insertion `x` has torus reading `R_T = Σ r_iⁿ x_i / Z` and vacuum reading `R_∞ = x_0`; the relative excited
weight is `τ_n = Σ_{i ≥ 1} r_iⁿ = Z/λ_0ⁿ − 1`.

* `stepDefect_le`: the one-direction doubling defect `2 log Z(n) − log Z(2n)` is at most `2 log(1 + τ_n)`.
* `lowSide`: if the insertion's excited diagonal elements are at most `K` times its vacuum element, then
  `(1 + K τ_n)⁻¹ R_T ≤ R_∞`: `RefPassageLow` at `c = (1 + K τ_n)⁻¹`.
* `lowSide_fails`: at `r = (1, μ)`, `x = (0, 1)`, every `c > 0` has `R_∞ < c R_T`, while `τ_n = μⁿ`.

So the spectral statement `τ_n ≤ τ` is one far statement that carries the defect side of a one-direction
doubling and does not carry the volume side: the volume side needs, in addition, the overlap ratio `K` of the
reference insertion, a property of the insertion and not a finite-size property of the torus. `defectW` is
`16 log Z(n) − log Z(2n)`, a weighted sum of four one-direction doublings on four cross-sections (argued, not
built here), so on the Wilson torus the spectral form would be four excited weights. Against the Wilson
objects the spectral form is not built in either direction: the built defect-side form is `FarRel`, and the
model fixes the shape of the volume side.

## Verdict

Three remainders: one near (`Near`, which replaces `ScaleUpAlong` and `PointCubeLocalAlong`), and two far
(`RefPassageLow`, and `PhysDefect` or its relative energy form `FarRel`). The far pair shares a finite-size
spectral part `τ`; what separates them is the overlap ratio `K` of the reference insertion.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the doubling and
the two directions of a one-direction doubling; `8n` the spacing power of `PointRatio`; `0`, `1` the vacuum index
and its weight.
-/

noncomputable section

namespace MassGap.ApertureTwo

open Real Filter Set MassGap MassGap.PhysicalScaleSmall MassGap.ZoomSelfScale MassGap.EffectiveCoupling
  MassGap.EnergySeed

/-! ## 1. Near: one statement -/

section Near

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumCluster
  MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint

variable {N : ℕ}

/-- **The near statement**: point readings at every margin against the reference reading at the aperture scale
`s₀`, with one constant per list and margin. -/
def Near (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  PointReadingRatio.PointRatioAlong hN βs O s₀ s₀

/-- **The scale and field clauses give `Near`.** -/
theorem near_of_scaleUp_pointCube (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hU : DiagBoundRunning.ScaleUpAlong hN βs O s₀)
    (hL : ShortDistanceRunning.PointCubeLocalAlong hN βs O s₀) : Near hN βs O s₀ :=
  DiagBoundRunning.pointRatio_of_scaleUp_along hN βs O hs₀ hU hL

/-- **`Near` gives the pinned `hD`.** -/
theorem diagBoundSep_of_near (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (h : Near hN βs O s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O s₀ s₀)) 0 :=
  PointReadingRatio.diagBoundSep_zCan_of_pointRatio_along hN βs O s₀ s₀ h

/-- **`Near` gives the scale clause** at an eventually positive reference reading. -/
theorem scaleUp_of_near (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hpos : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O s₀ s₀ k) (h : Near hN βs O s₀) :
    DiagBoundRunning.ScaleUpAlong hN βs O s₀ :=
  DiagBoundRunning.scaleUp_of_diagBoundSep_along hN βs O hpos (diagBoundSep_of_near hN βs O h)

/-- **`Near` and the reverse scale comparison give the field clause.** -/
theorem pointCube_of_near_scaleDown (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hD : DiagBoundRunning.ScaleDownAlong hN βs O s₀) (h : Near hN βs O s₀) :
    ShortDistanceRunning.PointCubeLocalAlong hN βs O s₀ := by
  intro n L d hd hds
  obtain ⟨C, hC⟩ := h n L d hd
  obtain ⟨m, hm⟩ := hD d hd hds
  refine ⟨max C 0 * m ^ n, ?_⟩
  filter_upwards [hC, hm, FieldDomination.refReadingAlong_eventually_nonneg hN βs O (ℓ := s₀) hs₀]
    with k hk hmk hx p hp
  have hu := hk p hp
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hpow := DiagBoundRunning.pow_le_of_le_mul n hx hmk
  calc _ ≤ C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O s₀ s₀ k ^ n := hu
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O s₀ s₀ k ^ n := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg ha (pow_nonneg hx n))
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * (m ^ n * refReadingAlong hN βs O d d k ^ n) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) ha)
    _ = max C 0 * m ^ n * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d d k ^ n := by ring

/-- **The near statement per field**: point readings at every margin against the product of each field's own
reference reading at `s₀`.

DERIVED: `8 n = 4 · 2n`, the cell volume `a_k⁴` of each of the `2n` point insertions, as in
`ExistencePoint.PointDiagSepAlong` and `ApertureBridge.PointCubeOwnAlong`; `0` the plane's height. -/
def NearOwn (hN : N ≠ 0) (βs : ℕ → ℝ) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ C : ℝ,
    ∀ᶠ k in atTop, ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      latSkRAlong hN βs (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k

/-- **The per-field scale and field clauses give `NearOwn`.** -/
theorem nearOwn_of_own (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hU : ApertureBridge.ScaleUpOwnAlong hN βs s₀) (hL : ApertureBridge.PointCubeOwnAlong hN βs s₀) :
    NearOwn hN βs s₀ := by
  intro n L d hd
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨C, hC⟩ := hL n L d' hd' hd's
  have hM : ∀ i : Fin n, ∃ M : ℝ, ∀ᶠ k in atTop,
      refReadingAlong hN βs (L i) d' d' k ≤ M * refReadingAlong hN βs (L i) s₀ s₀ k :=
    fun i => hU (L i) d' hd' hd's
  choose M hM using hM
  refine ⟨max C 0 * ∏ i, M i, ?_⟩
  filter_upwards [hC, Filter.eventually_all.2 hM,
    Filter.eventually_all.2 fun i => FieldDomination.refReadingAlong_eventually_nonneg hN βs (L i)
      (ℓ := d') hd'] with k hk hm hx p hp
  have hu := hk p (ContinuumSep.sepPos_mono hp (min_le_left d (s₀ / 2)))
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hx' : 0 ≤ ∏ i, refReadingAlong hN βs (L i) d' d' k := Finset.prod_nonneg fun i _ => hx i
  have hprod : ∏ i, refReadingAlong hN βs (L i) d' d' k
      ≤ (∏ i, M i) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => hx i) fun i _ => hm i
  calc _ ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) d' d' k := hu
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) d' d' k := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg ha hx')
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) *
          ((∏ i, M i) * ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (le_max_right _ _) ha)
    _ = max C 0 * (∏ i, M i) * dySpacing N k ^ (8 * n) *
          ∏ i, refReadingAlong hN βs (L i) s₀ s₀ k := by ring

end Near

/-! ## 2. Far, defect side: relative finite-size extensivity -/

section Far

variable {N : ℕ}

/-- **The defect from a relative finite-size excess of the mean action.** If, at every coupling in `[0, β)`, the
mean action of the doubled torus exceeds `16` copies of the side-`n` one by at most the fraction `η` of the latter,
the defect at `β` is at most `16 η` times the free energy `−log Z_n(β)`. -/
theorem defectW_le_rel (hN : N ≠ 0) {n : ℕ} {β η : ℝ} (hβ : 0 ≤ β)
    (h : ∀ x ∈ Ico 0 β, finiteSize N n x ≤ η * (16 * meanAction N (fun _ => n) x)) :
    defectW N β n ≤ η * (16 * -Real.log (RectWilson.ZR (fun _ => n) N β)) := by
  have hd : ∀ x ∈ Icc (0 : ℝ) β,
      HasDerivAt (fun y => η * (16 * -Real.log (RectWilson.ZR (fun _ => n) N y)))
        (η * (16 * meanAction N (fun _ => n) x)) x := fun x _ =>
    (((hasDerivAt_logZR hN (fun _ => n) x).neg.const_mul 16).const_mul η).congr_deriv (by ring)
  refine defectW_le_of_budget hN (Φ := fun y => η * (16 * -Real.log (RectWilson.ZR (fun _ => n) N y)))
    (φ := fun x => η * (16 * meanAction N (fun _ => n) x)) ?_ hd h β ⟨hβ, le_rfl⟩
  show defectW N 0 n ≤ η * (16 * -Real.log (RectWilson.ZR (fun _ => n) N 0))
  rw [defectW_zero, SeedZeroCoupling.ZR_at_zero, Real.log_one]
  simp

/-- **Relative extensivity at the physical side.** Eventually in `β`, at `n = 2^{kPhys L β + 2}` and at every
coupling below `β`, the doubled torus's mean action exceeds `16` copies of the side-`n` torus's by at most the
fraction `δ / (16 F_n(β))` of the latter, `F_n(β) = −log Z_n(β)`.

DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the rank, the doubling and the
dyadic base; `0` the bottom coupling. -/
def FarRel (L δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ x ∈ Ico 0 β,
    finiteSize 2 (2 ^ (kPhys L β + 2)) x
      ≤ δ / (16 * -Real.log (RectWilson.ZR (fun _ => 2 ^ (kPhys L β + 2)) 2 β))
        * (16 * meanAction 2 (fun _ => 2 ^ (kPhys L β + 2)) x)

/-- **Relative extensivity gives the physical-side defect.** -/
theorem farRel_physDefect {L δ : ℝ} (hδ : 0 ≤ δ) (h : FarRel L δ) : ApertureBridge.PhysDefect L δ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hx hβ
  have hb := defectW_le_rel (N := 2) (by norm_num) hβ hx
  set F := 16 * -Real.log (RectWilson.ZR (fun _ => 2 ^ (kPhys L β + 2)) 2 β)
  by_cases hF : F = 0
  · rw [hF, div_zero, zero_mul] at hb
    linarith
  · rwa [div_mul_cancel₀ δ hF] at hb

/-- **`RunSeed 2` from relative extensivity**, at `δ = 1/1000`. -/
theorem runSeed_of_farRel {L : ℝ} (hL : 0 < L) (h : FarRel L (1 / 1000)) : WDeltaRun.RunSeed 2 :=
  ApertureBridge.runSeed_of_physDefect hL (farRel_physDefect (by norm_num) h)

end Far

/-! ## 3. Far, both sides on one torus: the transfer model -/

section Model

variable {m : ℕ} (r : Fin (m + 1) → ℝ)

/-- The torus of length `n`: `Σ r_iⁿ`, the trace of the `n`-th power of the transfer at top eigenvalue `1`. -/
def trZ (n : ℕ) : ℝ := ∑ i, r i ^ n

/-- A diagonal insertion `x` on the torus of length `n`: `Σ r_iⁿ x_i`. -/
def trX (x : Fin (m + 1) → ℝ) (n : ℕ) : ℝ := ∑ i, r i ^ n * x i

/-- The relative excited weight of the torus of length `n`: `Σ_{i ≥ 1} r_iⁿ`. -/
def tau (n : ℕ) : ℝ := ∑ i : Fin m, r i.succ ^ n

theorem trZ_eq (hr0 : r 0 = 1) (n : ℕ) : trZ r n = 1 + tau r n := by
  simp [trZ, tau, Fin.sum_univ_succ, hr0]

theorem tau_nonneg (hr : ∀ i, 0 ≤ r i) (n : ℕ) : 0 ≤ tau r n :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (hr _) _

/-- **The one-direction doubling defect is at most `2 log(1 + τ_n)`.** -/
theorem stepDefect_le (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (n : ℕ) :
    2 * Real.log (trZ r n) - Real.log (trZ r (2 * n)) ≤ 2 * Real.log (1 + tau r n) := by
  rw [trZ_eq r hr0, trZ_eq r hr0]
  have : 0 ≤ Real.log (1 + tau r (2 * n)) :=
    Real.log_nonneg (by linarith [tau_nonneg r hr (2 * n)])
  linarith

/-- **The torus reading against the vacuum reading** for an insertion whose excited diagonal elements are at
most `K` times its vacuum element. -/
theorem torus_le (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) {x : Fin (m + 1) → ℝ} (hx : ∀ i, 0 ≤ x i) {K : ℝ}
    (hK : ∀ i : Fin m, x i.succ ≤ K * x 0) (n : ℕ) :
    trX r x n / trZ r n ≤ (1 + K * tau r n) * x 0 := by
  have hZ : 1 ≤ trZ r n := by rw [trZ_eq r hr0]; linarith [tau_nonneg r hr n]
  have hX0 : 0 ≤ trX r x n := Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (hr i) n) (hx i)
  have hXeq : trX r x n = x 0 + ∑ i : Fin m, r i.succ ^ n * x i.succ := by
    simp [trX, Fin.sum_univ_succ, hr0]
  have hs : ∑ i : Fin m, r i.succ ^ n * x i.succ ≤ K * tau r n * x 0 := by
    calc _ ≤ ∑ i : Fin m, r i.succ ^ n * (K * x 0) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hK i) (pow_nonneg (hr _) n)
      _ = K * tau r n * x 0 := by rw [← Finset.sum_mul]; unfold tau; ring
  have he : (1 + K * tau r n) * x 0 = x 0 + K * tau r n * x 0 := by ring
  calc trX r x n / trZ r n ≤ trX r x n := div_le_self hX0 hZ
    _ ≤ _ := by rw [hXeq, he]; linarith

/-- **The lower side of the passage in the model**: `(1 + K τ_n)⁻¹ R_T ≤ R_∞`. -/
theorem lowSide (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) {x : Fin (m + 1) → ℝ} (hx : ∀ i, 0 ≤ x i) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i : Fin m, x i.succ ≤ K * x 0) (n : ℕ) :
    (1 + K * tau r n)⁻¹ * (trX r x n / trZ r n) ≤ x 0 := by
  have hp : 0 < 1 + K * tau r n := by nlinarith [tau_nonneg r hr n]
  rw [inv_mul_le_iff₀ hp]
  exact torus_le r hr0 hr hx hK n

/-- **The excited weight alone does not give the lower side.** At `r = (1, μ)`, `x = (0, 1)`: `τ_n = μⁿ`, and
every `c > 0` has `R_∞ < c R_T`. -/
theorem lowSide_fails {μ : ℝ} (hμ : 0 < μ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    tau (![1, μ] : Fin 2 → ℝ) n = μ ^ n ∧
      (![0, 1] : Fin 2 → ℝ) 0 < c * (trX ![1, μ] ![0, 1] n / trZ (![1, μ] : Fin 2 → ℝ) n) := by
  refine ⟨by simp [tau], ?_⟩
  have hX : trX ![1, μ] ![0, 1] n = μ ^ n := by simp [trX, Fin.sum_univ_succ]
  have hZ : trZ (![1, μ] : Fin 2 → ℝ) n = 1 + μ ^ n := by simp [trZ, Fin.sum_univ_succ]
  have hp : 0 < μ ^ n := pow_pos hμ n
  rw [hX, hZ]
  simp only [Matrix.cons_val_zero]
  exact mul_pos hc (div_pos hp (by linarith))

end Model

end MassGap.ApertureTwo

end

#print axioms MassGap.ApertureTwo.near_of_scaleUp_pointCube
#print axioms MassGap.ApertureTwo.diagBoundSep_of_near
#print axioms MassGap.ApertureTwo.scaleUp_of_near
#print axioms MassGap.ApertureTwo.pointCube_of_near_scaleDown
#print axioms MassGap.ApertureTwo.nearOwn_of_own
#print axioms MassGap.ApertureTwo.defectW_le_rel
#print axioms MassGap.ApertureTwo.farRel_physDefect
#print axioms MassGap.ApertureTwo.runSeed_of_farRel
#print axioms MassGap.ApertureTwo.stepDefect_le
#print axioms MassGap.ApertureTwo.torus_le
#print axioms MassGap.ApertureTwo.lowSide
#print axioms MassGap.ApertureTwo.lowSide_fails
