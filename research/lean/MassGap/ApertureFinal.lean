import Mathlib
import MassGap.ApertureTwo
import MassGap.ExistenceReduceOwn

/-!
# MassGap.ApertureFinal — the near side closed at `zOwn`, and what the far side still reads

The pinned target is `ExistenceReduceOwn.clay_canonical_own`, `ClayContinuumPair` at the per-field factor `zOwn`.
This module closes its `hD` from the single near statement `ApertureTwo.NearOwn`, places the overlap ratio `K` of
the volume clause, and lines up the two far clauses along the tower.

## Near: one statement, closed (proved)

* `pointDiagSep_zOwn_of_nearOwn_along`, `diagBoundSep_zOwn_of_nearOwn_along`, `diagBoundSep_zOwn_of_nearOwn`:
  `NearOwn hN βs s₀ ⇒ DiagBoundSep` at `zOwn hN s₀ s₀`. `NearOwn` already reads every list against the product of
  each field's own reading at `s₀`, which is the reading `zOwn` divides by; the bound passes through
  `ExistenceReduceOwn.prod_inv_mul_le` with every scale constant equal to `1`. No positivity of any reading is used.
  With `ApertureTwo.nearOwn_of_own`, the per-field pair `ScaleUpOwnAlong ∧ PointCubeOwnAlong` is one route to
  `NearOwn`, not a second remainder.

## The overlap ratio `K` (model, proved)

`ApertureTwo`'s model had a diagonal insertion. Here the insertion is a matrix: eigenvalue ratios `r i = λ_i/λ_0`,
`r 0 = 1`, `0 ≤ r ≤ 1`, and `q i j = |⟨i|Q|j⟩|² ≥ 0`, symmetric. On the torus of length `a + b` with the two
insertions `b` apart, the reading is `trW a b / trZ (a + b)` with `trW a b = Σ_{i,j} q_ij r_iᵃ r_jᵇ`; the
infinite-volume reading at separation `b` is `vac b = Σ_j q_0j r_jᵇ`.

* `trW_split`: `trW a b = vac a + vac b − q_00 + dbl a b`, with `dbl a b = Σ_{i,j ≥ 1} q_ij r_iᵃ r_jᵇ`. The torus
  reading is the vacuum reading the short way, the vacuum reading the long way, and a doubly excited part.
* `vac_anti`: `b ≤ a ⇒ vac a ≤ vac b`. The long-way vacuum term needs no hypothesis.
* `dbl_le`: if every excited row reads at most `K` times the vacuum, `Σ_{j ≥ 1} q_ij r_jᵇ ≤ K · vac b` for
  `i ≥ 1`, then `dbl a b ≤ K τ_a vac b`, `τ_a = Σ_{i ≥ 1} r_iᵃ` (`ApertureTwo.tau`).
* `lowSide_pair`: under that row bound, `(2 + K τ_a)⁻¹ R_T ≤ R_∞` at `b ≤ a`. `lowSide_pair_of_tau`: a spectral
  bound `τ_a ≤ τ₀` gives it at the fixed fraction `(2 + K τ₀)⁻¹`.
* `model_far`: one spectral bound `τ_a ≤ τ₀` gives both far clauses of the model at every length `n ≥ a`: the
  one-direction doubling defect at most `2 log(1 + τ₀)` (`ApertureTwo.stepDefect_le`, `tau_anti`), and, with the
  row bound `K`, the lower side at `(2 + K τ₀)⁻¹`.
* `overlap_blind`: at `r = (1, μ)`, `q = [[u, v], [v, t]]`, the vacuum readings `vac b = u + v μᵇ` and the torus
  partition function `trZ` do not depend on `t`, and for every `c > 0` some `t ≥ 0` has `R_∞ < c R_T`.

So `K` is a property of the reference insertion in the excited states: its doubly excited matrix elements
`q_ij`, `i, j ≥ 1`, relative to its vacuum row. No function of the vacuum two-point readings and no function of
the spectrum or the partition functions (what `PhysDefect`, `FarRel`, `τ` read) bounds it (`overlap_blind`).
Vacuum multi-point readings, which `NearOwn` bounds, do see `t` in this model (the 4-point reading contains a
`v · t` term), so whether `NearOwn` supplies `K` is open. In the aperture picture `K` is a near-type statement (one
insertion at the aperture scale, read in excited states against the vacuum). The model's readings are not
connected (`q₀₀ = ⟨Q⟩²` sits in `vac` and `trW`), while `RefPassageLow` compares connected readings; the
connected leftover is again an excited-state matrix element, but the `(2 + Kτ)⁻¹` form does not carry over.
The spectral part of the volume clause is the same `τ` as the defect's (`model_far`).

## The two far clauses along the tower (proved)

* `physDefect_along`: `PhysDefect L δ`, eventually in `β`, holds eventually in `k` at `β = dyBeta k`
  (`ContinuumSchwinger.tendsto_dyBeta`).
* `kPhys_dyBeta`: at `L = 2ᵖ · aRun 2 1`, `kPhys L (dyBeta k) + 2 = p + k + 1` once `1 ≤ p + k`.
* `physSide_stateT`: at `M₀ = 2ᵖ`, `L = M₀ · aRun 2 1`, the Wilson torus that `PhysDefect` reads at step `k` has
  side `2(M₀ 2ᵏ)`, and `stateT hN M₀ k` has extent `2(M₀ 2ᵏ) + 2`, at the same coupling `dyBeta k`. The uniformities
  line up: `RefPassageLow` is eventually in `k` at fixed physical side `M₀ · aRun 2 1 + 2a_k`, and `PhysDefect` at
  that `L` is eventually in `k` at physical side `M₀ · aRun 2 1`, two sites apart.

## The capstone

`clay_final`: at `N = 2`, `O = planePlaq 2`, `(t, ℓ) = (s₀, s₀)`, `0 < s₀`, `4 s₀ < M₀ · aRun 2 1`, `0 < L`:
`NearOwn` (near), `∃ c > 0, RefPassageLow` (far, volume) and `PhysDefect L (1/1000)` (far, defect) give a witness
of `hD` at `zOwn` and `ClayContinuumPair` at `zOwn`, at window `5 · L/2`. `clay_final_rel` takes `FarRel L (1/1000)`
in place of `PhysDefect`.

## Count

Three remainders: one near (`NearOwn`) and two far (`RefPassageLow`; `PhysDefect` or `FarRel`). The two far
clauses share the spectral part `τ` (`model_far`) and separate on `K`, which no spectral statement and no
vacuum two-point reading supplies (`overlap_blind`); whether `NearOwn`'s multi-point readings supply it is open. Built against the tree, no lemma passes between `RefPassageLow` and the
Wilson-torus objects: the slice transfer `RectTransfer.kT` gives `ZR = cyc kT` (`RectTransfer.ZR_eq_cyc`), but the
reference reading on `stateT` is not written in the eigenbasis of `kT` anywhere in the tree.

DERIVED (module-wide): `0`, `1` the vacuum index and its weight, and the unit scale constant; `2` the two vacuum
terms of `trW_split`, the doubling, and the base of the tower; `1/1000` the `RunSeed` threshold.
-/

noncomputable section

namespace MassGap.ApertureFinal

open Filter MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint
  MassGap.PhysicalScaleSmall

/-! ## 1. Near: `NearOwn ⇒ hD` at `zOwn` -/

section Near

variable {N : ℕ}

/-- **`NearOwn` gives bounded point readings at `zOwn`.** -/
theorem pointDiagSep_zOwn_of_nearOwn_along (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (h : ApertureTwo.NearOwn hN βs s₀) :
    PointDiagSepAlong hN βs (ExistenceReduceOwn.zOwnAlong hN βs s₀ s₀) := by
  intro n L d hd
  obtain ⟨C, hC⟩ := h n L d hd
  refine ⟨max C 0 * ∏ _i : Fin n, max (1 : ℝ) 0, ?_⟩
  have hr0 : ∀ᶠ k in atTop, ∀ i, 0 ≤ refReadingAlong hN βs (L i) s₀ s₀ k :=
    Filter.eventually_all.mpr
      (fun i => FieldDomination.refReadingAlong_eventually_nonneg hN βs (L i) hs₀)
  filter_upwards [hC, hr0] with k hk hr p hp
  have hu := hk p hp
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hu' := hu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 0) ha) (Finset.prod_nonneg fun i _ => hr i))
  have hz : (∏ i : Fin n, ExistenceReduceOwn.zOwnAlong hN βs s₀ s₀ k (L i)) ^ 2
      = ∏ i : Fin n, (ExistenceReduceOwn.ownReadingAlong hN βs s₀ s₀ k (L i))⁻¹ := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ =>
      ExistenceReduceOwn.zOwnAlong_sq hN βs s₀ s₀ k (L i) ((hr i).trans (le_max_left _ _)))
  rw [ExistenceReduceOwn.latSkR_pairFam_connectedAlong hN βs _
    (ExistenceReduceOwn.zOwnAlong_refl hN βs s₀ s₀)]
  show (∏ i : Fin n, ExistenceReduceOwn.zOwnAlong hN βs s₀ s₀ k (L i)) ^ 2 * _ ≤ _
  rw [hz]
  exact ExistenceReduceOwn.prod_inv_mul_le
    (fun i => ExistenceReduceOwn.ownReadingAlong hN βs s₀ s₀ k (L i))
    (fun i => refReadingAlong hN βs (L i) s₀ s₀ k) (fun i => refReadingAlong hN βs (L i) s₀ s₀ k)
    (fun _ => 1) (max C 0) (dySpacing N k ^ (8 * n)) _ (le_max_right _ _) ha hr
    (fun _ => le_max_left _ _) hr (fun i => by show _ ≤ 1 * _; rw [one_mul]) hu'

/-- **`NearOwn` gives `hD` at `zOwn`**, along `βs`. -/
theorem diagBoundSep_zOwn_of_nearOwn_along (hN : N ≠ 0) (βs : ℕ → ℝ) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (h : ApertureTwo.NearOwn hN βs s₀) :
    ContinuumSep.DiagBoundSepAlong hN βs
      (Renorm.connectedAlong hN βs (ExistenceReduceOwn.zOwnAlong hN βs s₀ s₀)) 0 :=
  diagBoundSep_of_pointDiagSep_along hN βs _ (ExistenceReduceOwn.zOwnAlong_refl hN βs s₀ s₀)
    (pointDiagSep_zOwn_of_nearOwn_along hN βs hs₀ h)

/-- **`NearOwn` gives the pinned `hD` at `zOwn`** at the couplings `dyBeta`. -/
theorem diagBoundSep_zOwn_of_nearOwn (hN : N ≠ 0) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (h : ApertureTwo.NearOwn hN (dyBeta (one_le_of_ne_zero hN)) s₀) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0 :=
  diagBoundSep_zOwn_of_nearOwn_along hN (dyBeta (one_le_of_ne_zero hN)) hs₀ h

end Near

/-! ## 2. The overlap ratio in the transfer model -/

section Model

variable {m : ℕ} (r : Fin (m + 1) → ℝ) (q : Fin (m + 1) → Fin (m + 1) → ℝ)

/-- The torus numerator `Tr(Tᵃ Q Tᵇ Q)/λ₀^{a+b}` in the eigenbasis: `Σ_{i,j} q_ij r_iᵃ r_jᵇ`. -/
def trW (a b : ℕ) : ℝ := ∑ i, ∑ j, q i j * r i ^ a * r j ^ b

/-- The infinite-volume reading at separation `b`: `⟨Ω|Q Tᵇ Q|Ω⟩/λ₀ᵇ = Σ_j q_0j r_jᵇ`. -/
def vac (b : ℕ) : ℝ := ∑ j, q 0 j * r j ^ b

/-- The doubly excited part `Σ_{i,j ≥ 1} q_ij r_iᵃ r_jᵇ`. -/
def dbl (a b : ℕ) : ℝ := ∑ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r i.succ ^ a * r j.succ ^ b

/-- **The torus numerator splits** into the vacuum reading both ways round and the doubly excited part. -/
theorem trW_split (hr0 : r 0 = 1) (hq : ∀ i j, q i j = q j i) (a b : ℕ) :
    trW r q a b = vac r q a + vac r q b - q 0 0 + dbl r q a b := by
  have hsym : ∀ i : Fin m, q i.succ 0 = q 0 i.succ := fun i => hq _ _
  simp only [trW, vac, dbl, Fin.sum_univ_succ, hr0, one_pow, mul_one, Finset.sum_add_distrib, hsym]
  ring

/-- **The vacuum reading decreases with the separation.** -/
theorem vac_anti (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) (hq0 : ∀ i j, 0 ≤ q i j) {a b : ℕ}
    (hab : b ≤ a) : vac r q a ≤ vac r q b :=
  Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (hr j) (hr1 j) hab) (hq0 0 j)

/-- **The doubly excited part from the row bound `K`.** -/
theorem dbl_le (hr : ∀ i, 0 ≤ r i) {K : ℝ} {a b : ℕ}
    (hK : ∀ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b ≤ K * vac r q b) :
    dbl r q a b ≤ K * ApertureTwo.tau r a * vac r q b := by
  have h : dbl r q a b
      = ∑ i : Fin m, r i.succ ^ a * ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b := by
    unfold dbl
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  calc _ ≤ ∑ i : Fin m, r i.succ ^ a * (K * vac r q b) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hK i) (pow_nonneg (hr _) a)
    _ = K * ApertureTwo.tau r a * vac r q b := by
        rw [← Finset.sum_mul]; unfold ApertureTwo.tau; ring

/-- **The lower side of the passage at a matrix insertion**: `(2 + K τ_a)⁻¹ R_T ≤ R_∞` at `b ≤ a`. -/
theorem lowSide_pair (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hq : ∀ i j, q i j = q j i) (hq0 : ∀ i j, 0 ≤ q i j) {K : ℝ} (hK0 : 0 ≤ K) {a b : ℕ}
    (hab : b ≤ a) (hK : ∀ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b ≤ K * vac r q b) :
    (2 + K * ApertureTwo.tau r a)⁻¹ * (trW r q a b / ApertureTwo.trZ r (a + b)) ≤ vac r q b := by
  have ht := ApertureTwo.tau_nonneg r hr a
  have hp : 0 < 2 + K * ApertureTwo.tau r a := by nlinarith
  rw [inv_mul_le_iff₀ hp]
  have hZ : 1 ≤ ApertureTwo.trZ r (a + b) := by
    rw [ApertureTwo.trZ_eq r hr0]; linarith [ApertureTwo.tau_nonneg r hr (a + b)]
  have hW0 : 0 ≤ trW r q a b := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hq0 i j) (pow_nonneg (hr i) a)) (pow_nonneg (hr j) b)
  have hva := vac_anti r q hr hr1 hq0 hab
  have hd := dbl_le r q hr (a := a) hK
  have h00 : 0 ≤ q 0 0 := hq0 0 0
  have hsplit := trW_split r q hr0 hq a b
  have he : (2 + K * ApertureTwo.tau r a) * vac r q b
      = 2 * vac r q b + K * ApertureTwo.tau r a * vac r q b := by ring
  calc trW r q a b / ApertureTwo.trZ r (a + b) ≤ trW r q a b := div_le_self hW0 hZ
    _ ≤ (2 + K * ApertureTwo.tau r a) * vac r q b := by rw [hsplit, he]; linarith

/-- The vacuum reading is nonnegative. -/
theorem vac_nonneg (hr : ∀ i, 0 ≤ r i) (hq0 : ∀ i j, 0 ≤ q i j) (b : ℕ) : 0 ≤ vac r q b :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hq0 0 j) (pow_nonneg (hr j) b)

/-- **The lower side at a fixed fraction** from a spectral bound `τ_a ≤ τ₀`. -/
theorem lowSide_pair_of_tau (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hq : ∀ i j, q i j = q j i) (hq0 : ∀ i j, 0 ≤ q i j) {K τ₀ : ℝ} (hK0 : 0 ≤ K) {a b : ℕ}
    (hab : b ≤ a) (hK : ∀ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b ≤ K * vac r q b)
    (hτ : ApertureTwo.tau r a ≤ τ₀) :
    (2 + K * τ₀)⁻¹ * (trW r q a b / ApertureTwo.trZ r (a + b)) ≤ vac r q b := by
  have h := lowSide_pair r q hr0 hr hr1 hq hq0 hK0 hab hK
  have ht := ApertureTwo.tau_nonneg r hr a
  have hp : 0 < 2 + K * ApertureTwo.tau r a := by nlinarith
  have hZ : 0 < ApertureTwo.trZ r (a + b) := by
    rw [ApertureTwo.trZ_eq r hr0]; linarith [ApertureTwo.tau_nonneg r hr (a + b)]
  have hW0 : 0 ≤ trW r q a b := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hq0 i j) (pow_nonneg (hr i) a)) (pow_nonneg (hr j) b)
  have hR : 0 ≤ trW r q a b / ApertureTwo.trZ r (a + b) := div_nonneg hW0 hZ.le
  have hinv : (2 + K * τ₀)⁻¹ ≤ (2 + K * ApertureTwo.tau r a)⁻¹ :=
    inv_anti₀ hp (by nlinarith)
  exact le_trans (mul_le_mul_of_nonneg_right hinv hR) h

/-- The excited weight decreases with the length. -/
theorem tau_anti (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) {a n : ℕ} (han : a ≤ n) :
    ApertureTwo.tau r n ≤ ApertureTwo.tau r a :=
  Finset.sum_le_sum fun _ _ => pow_le_pow_of_le_one (hr _) (hr1 _) han

/-- **One spectral bound carries both far clauses of the model.** `τ_a ≤ τ₀` gives, at every length `n ≥ a`,
the one-direction doubling defect at most `2 log(1 + τ₀)`, and, with the row bound `K`, the lower side at the
fraction `(2 + K τ₀)⁻¹`. -/
theorem model_far (hr0 : r 0 = 1) (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (hq : ∀ i j, q i j = q j i) (hq0 : ∀ i j, 0 ≤ q i j) {K τ₀ : ℝ} (hK0 : 0 ≤ K) {a b : ℕ}
    (hab : b ≤ a) (hτ : ApertureTwo.tau r a ≤ τ₀) :
    (∀ n, a ≤ n → 2 * Real.log (ApertureTwo.trZ r n) - Real.log (ApertureTwo.trZ r (2 * n))
      ≤ 2 * Real.log (1 + τ₀)) ∧
    ((∀ i : Fin m, ∑ j : Fin m, q i.succ j.succ * r j.succ ^ b ≤ K * vac r q b) →
      (2 + K * τ₀)⁻¹ * (trW r q a b / ApertureTwo.trZ r (a + b)) ≤ vac r q b) := by
  refine ⟨fun n han => ?_, fun hK => lowSide_pair_of_tau r q hr0 hr hr1 hq hq0 hK0 hab hK hτ⟩
  have hs := ApertureTwo.stepDefect_le r hr0 hr n
  have htn := tau_anti r hr hr1 han
  have h0 := ApertureTwo.tau_nonneg r hr n
  have hlog : Real.log (1 + ApertureTwo.tau r n) ≤ Real.log (1 + τ₀) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- The two-level insertion matrix `[[u, v], [v, t]]`. -/
def qm (u v t : ℝ) : Fin 2 → Fin 2 → ℝ := ![![u, v], ![v, t]]

/-- **The overlap ratio is invisible to the vacuum readings and to the spectrum.** At `r = (1, μ)` and
`q = [[u, v], [v, t]]` the vacuum readings are `u + v μᵇ` at every `t`, the partition function does not read `q`,
and for every `c > 0` some `t ≥ 0` has `R_∞ < c R_T`. -/
theorem overlap_blind {μ : ℝ} (hμ : 0 < μ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (a b : ℕ) {c : ℝ}
    (hc : 0 < c) :
    (∀ s, vac ![1, μ] (qm u v s) b = u + v * μ ^ b) ∧
      ∃ t : ℝ, 0 ≤ t ∧
        vac ![1, μ] (qm u v t) b
          < c * (trW ![1, μ] (qm u v t) a b / ApertureTwo.trZ (![1, μ] : Fin 2 → ℝ) (a + b)) := by
  have hP : 0 < μ ^ (a + b) := pow_pos hμ _
  have hvac : ∀ s, vac ![1, μ] (qm u v s) b = u + v * μ ^ b := fun s => by
    simp [vac, qm, Fin.sum_univ_two]
  have hZ : ApertureTwo.trZ (![1, μ] : Fin 2 → ℝ) (a + b) = 1 + μ ^ (a + b) := by
    simp [ApertureTwo.trZ, Fin.sum_univ_two]
  have hW : ∀ s, trW ![1, μ] (qm u v s) a b
      = u + v * μ ^ b + v * μ ^ a + s * μ ^ (a + b) := fun s => by
    simp [trW, qm, Fin.sum_univ_two, pow_add]; ring
  have hB : 0 ≤ u + v * μ ^ b := add_nonneg hu (mul_nonneg hv (pow_pos hμ b).le)
  refine ⟨hvac, (u + v * μ ^ b + 1) * (1 + μ ^ (a + b)) / (c * μ ^ (a + b)),
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hc hP).le, ?_⟩
  rw [hvac, hW, hZ]
  have key : c * ((u + v * μ ^ b + v * μ ^ a
        + (u + v * μ ^ b + 1) * (1 + μ ^ (a + b)) / (c * μ ^ (a + b)) * μ ^ (a + b))
          / (1 + μ ^ (a + b)))
      = c * (u + v * μ ^ b + v * μ ^ a) / (1 + μ ^ (a + b)) + (u + v * μ ^ b + 1) := by
    field_simp
  rw [key]
  have : 0 ≤ c * (u + v * μ ^ b + v * μ ^ a) / (1 + μ ^ (a + b)) := by positivity
  linarith

end Model

/-! ## 3. The two far clauses along the tower -/

section Tower

/-- **`PhysDefect` along the tower**: eventually in `k` at `β = dyBeta k`. -/
theorem physDefect_along (hN : (2 : ℕ) ≠ 0) {L δ : ℝ} (h : ApertureBridge.PhysDefect L δ) :
    ∀ᶠ k in atTop, ZoomSelfScale.defectW 2 (dyBeta (one_le_of_ne_zero hN) k)
      (2 ^ (kPhys L (dyBeta (one_le_of_ne_zero hN) k) + 2)) ≤ δ :=
  (tendsto_dyBeta (one_le_of_ne_zero hN)).eventually h

/-- **The physical-side exponent at the step-`k` coupling**: at `L = 2ᵖ · aRun 2 1`,
`kPhys L (dyBeta k) + 2 = p + k + 1`. -/
theorem kPhys_dyBeta (hN : (2 : ℕ) ≠ 0) (p k : ℕ) (hpk : 1 ≤ p + k) :
    kPhys (2 ^ p * AsymptoticScaling.aRun 2 1) (dyBeta (one_le_of_ne_zero hN) k) + 2 = p + k + 1 := by
  unfold kPhys
  rw [aRun_dyBeta, dySpacing]
  have ha : 0 < AsymptoticScaling.aRun 2 1 := AsymptoticScaling.aRun_pos (by norm_num) one_pos
  have h : 2 ^ p * AsymptoticScaling.aRun 2 1 / (AsymptoticScaling.aRun 2 1 / 2 ^ (k + 1))
      = ((2 ^ (p + k + 1) : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [h, Nat.floor_natCast, Nat.log_pow (by norm_num)]
  omega

/-- **The two far clauses read tori two sites apart at the same coupling.** At `M₀ = 2ᵖ`, `L = M₀ · aRun 2 1`,
the side of the Wilson torus that `PhysDefect L` reads at `β = dyBeta k` is `2(M₀ 2ᵏ)`; `stateT hN M₀ k`
(`torusState (2 M₀ 2ᵏ + 1)`, which has `2 M₀ 2ᵏ + 2` sites) is two sites longer. This lemma is the arithmetic
identity only. -/
theorem physSide_stateT (hN : (2 : ℕ) ≠ 0) (p k : ℕ) (hpk : 1 ≤ p + k) :
    2 ^ (kPhys (2 ^ p * AsymptoticScaling.aRun 2 1) (dyBeta (one_le_of_ne_zero hN) k) + 2) + 1
      = 2 * (2 ^ p * 2 ^ k) + 1 := by
  rw [kPhys_dyBeta hN p k hpk]
  ring

end Tower

/-! ## 4. The capstone -/

section Capstone

/-- **The pinned path at `zOwn` from one near and two far statements.** At `N = 2`, `O = planePlaq 2`,
`(t, ℓ) = (s₀, s₀)`: `NearOwn` (near), `RefPassageLow` at some `c > 0` (far, volume) and
`PhysDefect L (1/1000)` (far, defect) give a witness of `hD` at `zOwn` and `ClayContinuumPair` at `zOwn`, at
window `5 · L/2`. -/
theorem clay_final (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (hM : 2 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : ApertureTwo.NearOwn hN (dyBeta (one_le_of_ne_zero hN)) s₀)
    (hP : ∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq 2) s₀ s₀ c)
    (hW : ApertureBridge.PhysDefect L (1 / 1000)) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
          (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
              (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) := by
  have hD := diagBoundSep_zOwn_of_nearOwn hN hs₀ hNear
  exact ⟨hD, L / 2, by positivity,
    ExistenceReduceOwn.clay_canonical_own_planePlaq_low le_rfl hN hs₀ hs₀ hM hP hD (by positivity)
      (ApertureBridge.wDelta2_two_of_physDefect hL hW (L / 2) (by linarith))⟩

/-- **The capstone with the defect in its relative energy form** `FarRel L (1/1000)`. -/
theorem clay_final_rel (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (hM : 2 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : ApertureTwo.NearOwn hN (dyBeta (one_le_of_ne_zero hN)) s₀)
    (hP : ∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq 2) s₀ s₀ c)
    (hF : ApertureTwo.FarRel L (1 / 1000)) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
          (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
              (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) :=
  clay_final hN hs₀ hM hL hNear hP (ApertureTwo.farRel_physDefect (by norm_num) hF)

end Capstone

end MassGap.ApertureFinal

end

#print axioms MassGap.ApertureFinal.pointDiagSep_zOwn_of_nearOwn_along
#print axioms MassGap.ApertureFinal.diagBoundSep_zOwn_of_nearOwn_along
#print axioms MassGap.ApertureFinal.diagBoundSep_zOwn_of_nearOwn
#print axioms MassGap.ApertureFinal.trW_split
#print axioms MassGap.ApertureFinal.vac_anti
#print axioms MassGap.ApertureFinal.dbl_le
#print axioms MassGap.ApertureFinal.lowSide_pair
#print axioms MassGap.ApertureFinal.vac_nonneg
#print axioms MassGap.ApertureFinal.lowSide_pair_of_tau
#print axioms MassGap.ApertureFinal.tau_anti
#print axioms MassGap.ApertureFinal.model_far
#print axioms MassGap.ApertureFinal.overlap_blind
#print axioms MassGap.ApertureFinal.physDefect_along
#print axioms MassGap.ApertureFinal.kPhys_dyBeta
#print axioms MassGap.ApertureFinal.physSide_stateT
#print axioms MassGap.ApertureFinal.clay_final
#print axioms MassGap.ApertureFinal.clay_final_rel
