import Mathlib
import MassGap.ToronSector
import MassGap.ThickSheetCost
import MassGap.FloorModes

/-!
# MassGap.FluctSheet — the fluctuation entropy of a thick centre sheet, read from the charged spectrum

`ThickSheetCost` and `NonCartanTwist` show that at fixed coupling the classical cost of a thick centre sheet is
the same for `SU(2)` and `U(1)`, about `θ²/2` per coarse cell at every thickness. This module computes the next
term of the free energy, the fluctuation entropy, in the Gaussian model, and reads it the way the tree reads a
window: as the log-determinant over the kept band of the mode spectrum (`WindowFreq.logDetD`,
`ToronSector.logDetQ`; the kept band is the non-zero modes, the cut of `FreqRead.kept_iff`) and as the
entropy-effective mode count `FloorModes.occ` of the power `1/ω²`. No mode count is chosen: every count below
is the spectrum's own. Declarations are in `MassGap.FluctSheet`.

The model is Gaussian: quadratic fluctuations around a fixed background. It is not the Wilson measure, and
nothing in this module links the two.

## 1. The abelian sheet: no fluctuation entropy (proved, Gaussian model)

The Gaussian abelian action is `(β/2)‖D a + n‖²`, with `D` the lattice curl, `a` the fluctuation and `n` the
twist (the sheet's plaquette pattern). CHOSEN: the quadratic (Gaussian) form of the abelian action.

* `fluct_form`: around any background `b`, `‖D(b + a) + n‖² = ‖D b + n‖² + 2⟪D b + n, D a⟫ + ‖D a‖²`. The
  quadratic part `‖D a‖²` does not see the background: the photon carries no charge.
* `twist_split`: if `n = D a₀ + r` with `r` orthogonal to the range of `D`, then
  `‖D a + n‖² = ‖D(a + a₀)‖² + ‖r‖²`; `twist_min`: the classical cost of the twisted sector is `‖r‖²`.
* `u1_twisted_Z`: for every translation-invariant measure, `Z_tw = e^{−(β/2)‖r‖²} Z₀`.
  `u1_freeEnergy`: `log Z_tw − log Z₀ = −(β/2)‖r‖²` when `Z₀ > 0`. The twisted free energy is the classical
  cost exactly; the fluctuation entropy is zero at every thickness.

## 2. The charged modes of `SU(2)` across the sheet (proved)

The off-diagonal gluons of `SU(2)` have charge `2` under the Cartan angle (`ToronSector`). A centre twist puts
fundamental angles `θ_μ ∈ {0, π}`, so the charged modes see `2θ_μ ∈ 2πℤ`.

* `cos_shift`, `omegaQ_centre_shift`: if `q θ_μ = 2π c_μ` with `c_μ` a whole number of turns, then
  `ω²_k(qθ) = ω²_{k+c}(0)`: the charged spectrum is the neutral spectrum relabelled.
* `logDetQ_centre`, `entropicShift_centre`: the kept-band log-determinant read of the charged modes equals the
  photon's, `logDetD 0 d L`, so the twisted-minus-untwisted read is `0`, at every side `L`, every dimension
  `d` and every centre background. `occ_centre`: the mode-count read `FloorModes.occ` of the power `1/ω²`
  agrees as well (`occ_comp_equiv`: the count is a read of the spectrum, not of its labels).
* `su2_centre_entropicShift`: the `SU(2)` instance, `θ_μ ∈ {0, π}`.

A layered profile across the sheet (phases `φ_k` on the `L + 1` links of a ring through it) is not the uniform
one. The covariant form of a charged field on a graph is `covForm src tgt U ψ = Σ_e ‖ψ(tgt e) − U_e ψ(src e)‖²`.

* `covForm_gauge`: a unit-modulus relabelling `ψ ↦ gψ` carries the form with link phases `U` to the form with
  `U_e g(src e) conj g(tgt e)`.
* `ring_gauge`: on a ring of `L + 1` sites, two phase profiles whose totals differ by a multiple of `2π` give
  the same form up to a unit-modulus relabelling. `su2_ring_profile_free`: every layered `SU(2)` profile whose
  fundamental angles total `π` (the centre twist) gives, at charge `2`, the untwisted form up to that
  relabelling. Across the sheet the profile is pure gauge for the charged gluons, and the centre twist is
  invisible to them.
* `covForm_diamagnetic`: on any graph, `covForm U ψ ≥ covForm 1 |ψ|`: a background raises the charged form
  pointwise against the neutral form of the moduli (the diamagnetic inequality).

## 3. The sheet free energy as a function of `(β, L)` (proved)

`sheetF β cost c L = β · cost − c · log L`: the classical cost per coarse cell less an entropic term
`c log L`.

* `sheetF_falls`: if `c > 0`, at every `β` there is `L₀` beyond which `sheetF < ¼ ln 3`.
* `sheetF_stays`: if `c ≤ 0` and `β · cost > ¼ ln 3`, then `sheetF > ¼ ln 3` at every `L ≥ 1`.
* `chain_model_no_separator`: with the entropic coefficient the chain read gives (`c = 0`, both groups, by
  §1 and §2), every admissible Cartan profile at `β > π² ln 3/(8θ²)` has `sheetF > ¼ ln 3` at every
  thickness. In this model the fluctuation entropy does not separate `SU(2)` from `U(1)`.

## The answer

At the level asked, the charged fluctuation entropy is zero for both groups: for `U(1)` because the photon is
neutral (§1), for `SU(2)` because the gluons are adjoint and the centre twist is a whole turn for them, and a
profile across the sheet is pure gauge on the ring (§2). The coefficient of `log L` from the chain is `0`;
there is no separator from it.

What remains, and where the term would live. A thick sheet in four dimensions is a flux of `θ` through the
`L × L` transverse plane, spread over its plaquettes. There the field strength is gauge invariant and the
charged gluons see one flux quantum (`2π`) through the transverse torus: a lattice Landau (Hofstadter)
problem at flux `2π/L²` per plaquette. Two parts are known (cited, not proved here):
* the scalar (orbital) part raises the charged spectrum (`covForm_diamagnetic` is its pointwise form; the
  log-determinant inequality follows from the walk expansion, Kato–Simon diamagnetism), which screens: it
  adds `+c' log L` to the sheet free energy, `c' ≥ 0`, the wrong sign for a separator;
* the spin (magnetic moment) part of the vector gluon operator `−D² − 2iqF` shifts the lowest Landau level
  from `qB` to `−qB < 0` (Nielsen–Olesen), which antiscreens and carries the one-loop asymptotic-freedom
  coefficient `−11/3 = 1/3 − 4` (orbital `1/3`, spin `−4`), and makes the Gaussian model around a uniform
  transverse flux unbounded below.

The read that does not exist yet: the kept-band log-determinant of the charged vector-gluon operator in the
transverse plane with one flux quantum, `logDet(−D_B² − 2qF) − logDet(−∂²)`, as a function of `L`. That read
carries the separator if the separator is entropic at one loop, and its Gaussian form is undefined because
of the negative mode.

## What does not follow

* No statement about the `SU(2)` Wilson measure, `vortexR`, `FluxConfinedAt`, `StrongEnd` or the bridge. All
  of §1 and §2 is the Gaussian model.
* `c = 0` is proved for the chain (one-dimensional) read and for constant centre backgrounds; it is not
  proved, and is not expected, for the transverse Landau read, whose sign is the open item above.
* The screening sign of the scalar transverse read and the Nielsen–Olesen mode are cited, not proved.
* `sheetF_falls` is arithmetic on a chosen shape `β · cost − c log L`; it says what a positive `c` would give,
  not that any group has one.

DERIVED (module-wide): `2` the square, the Gaussian `β/2` and the `su(2)` root charge; `2π` the period and the
whole turn `2 · π`; `0` the neutral charge, the sign and the kept-band cut; `1` the unit modulus and the
least ring; `¼ ln 3`, `π² ln 3/(8θ²)` inherited from `VortexEntropy` and `ThickSheetCost`; `4 = 1/(¼)`.
CHOSEN: the Gaussian form of the action (§1), the shape `β · cost − c log L` of the sheet free energy (§3).
Cited (not proved here): Kato–Simon diamagnetism for the log-determinant, Nielsen–Olesen, the `−11/3`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.FluctSheet

open Real Finset MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
open MassGap.ToronSector (omegaQ chargedDet logDetQ omegaQ_zero_charge)
open MassGap.WindowFreq (omega2D logDetD)

/-! ## 1. The abelian sheet -/

section Abelian

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] [MeasurableAdd E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The abelian fluctuation form does not see the background.** DERIVED: `2` the cross term. -/
theorem fluct_form (D : E →ₗ[ℝ] F) (b a : E) (n : F) :
    ‖D (b + a) + n‖ ^ 2 = ‖D b + n‖ ^ 2 + 2 * ⟪D b + n, D a⟫_ℝ + ‖D a‖ ^ 2 := by
  rw [map_add, show D b + D a + n = (D b + n) + D a by abel]
  exact norm_add_sq_real _ _

/-- **The twist splits** into a gauge part and its orthogonal remainder `r`. -/
theorem twist_split (D : E →ₗ[ℝ] F) {n r : F} {a₀ : E} (hn : n = D a₀ + r)
    (hr : ∀ a, ⟪D a, r⟫_ℝ = 0) (a : E) : ‖D a + n‖ ^ 2 = ‖D (a + a₀)‖ ^ 2 + ‖r‖ ^ 2 := by
  rw [hn, ← add_assoc, ← map_add, norm_add_sq_real, hr]
  ring

/-- **The classical cost of the twisted sector is `‖r‖²`.** DERIVED: `0` the sign. -/
theorem twist_min (D : E →ₗ[ℝ] F) {n r : F} {a₀ : E} (hn : n = D a₀ + r)
    (hr : ∀ a, ⟪D a, r⟫_ℝ = 0) (a : E) : ‖r‖ ^ 2 ≤ ‖D a + n‖ ^ 2 := by
  rw [twist_split D hn hr a]
  nlinarith [sq_nonneg ‖D (a + a₀)‖]

/-- **The Gaussian twisted partition function** of the abelian sheet. CHOSEN: the quadratic action. -/
def gaussZ (μ : Measure E) (β : ℝ) (D : E →ₗ[ℝ] F) (n : F) : ℝ :=
  ∫ a, Real.exp (-(β / 2) * ‖D a + n‖ ^ 2) ∂μ

/-- **The abelian twisted partition function is the classical weight times the untwisted one**, for every
translation-invariant measure. -/
theorem u1_twisted_Z (μ : Measure E) [μ.IsAddRightInvariant] (β : ℝ) (D : E →ₗ[ℝ] F) {n r : F}
    {a₀ : E} (hn : n = D a₀ + r) (hr : ∀ a, ⟪D a, r⟫_ℝ = 0) :
    gaussZ μ β D n = Real.exp (-(β / 2) * ‖r‖ ^ 2) * gaussZ μ β D 0 := by
  unfold gaussZ
  have h1 : ∀ a, Real.exp (-(β / 2) * ‖D a + n‖ ^ 2)
      = Real.exp (-(β / 2) * ‖r‖ ^ 2) * Real.exp (-(β / 2) * ‖D (a + a₀) + 0‖ ^ 2) := by
    intro a
    rw [twist_split D hn hr a, add_zero, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h1]
  rw [integral_const_mul]
  congr 1
  exact integral_add_right_eq_self (fun a => Real.exp (-(β / 2) * ‖D a + 0‖ ^ 2)) a₀

/-- **The abelian twisted free energy is the classical cost exactly**: no fluctuation entropy. -/
theorem u1_freeEnergy (μ : Measure E) [μ.IsAddRightInvariant] (β : ℝ) (D : E →ₗ[ℝ] F) {n r : F}
    {a₀ : E} (hn : n = D a₀ + r) (hr : ∀ a, ⟪D a, r⟫_ℝ = 0) (hZ : 0 < gaussZ μ β D 0) :
    Real.log (gaussZ μ β D n) - Real.log (gaussZ μ β D 0) = -(β / 2) * ‖r‖ ^ 2 := by
  rw [u1_twisted_Z μ β D hn hr, Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  ring

end Abelian

/-! ## 2. The charged modes of `SU(2)` -/

/-- **A whole number of turns is invisible to the ring frequency.** DERIVED: `2π` the period. -/
theorem cos_shift {L : ℕ} (hL : 0 < L) (a b : ℕ) :
    Real.cos ((2 * π * (a : ℝ) + 2 * π * (b : ℝ)) / L) = Real.cos (2 * π * (((a + b) % L : ℕ) : ℝ) / L) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h := Nat.mod_add_div (a + b) L
  have hc : ((a : ℝ) + b) = (((a + b) % L : ℕ) : ℝ) + L * (((a + b) / L : ℕ) : ℝ) := by
    exact_mod_cast h.symm
  have e : (2 * π * (a : ℝ) + 2 * π * (b : ℝ)) / L
      = 2 * π * (((a + b) % L : ℕ) : ℝ) / L + (((a + b) / L : ℕ) : ℝ) * (2 * π) := by
    rw [show 2 * π * (a : ℝ) + 2 * π * (b : ℝ) = 2 * π * ((a : ℝ) + b) by ring, hc]
    field_simp
  rw [e, Real.cos_add_nat_mul_two_pi]

/-- **A whole number of turns as a relabelling of the momenta**: `c_μ = n_μ mod L`. -/
def turnShift {d L : ℕ} [NeZero L] (n : Fin d → ℕ) : Fin d → Fin L :=
  fun μ => ⟨n μ % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩

/-- **At a whole-turn background the charged spectrum is the neutral one, relabelled.** -/
theorem omegaQ_centre_shift (q : ℝ) {d L : ℕ} [NeZero L] (θ : Fin d → ℝ) (n : Fin d → ℕ)
    (hc : ∀ μ, q * θ μ = 2 * π * (n μ : ℝ)) (k : Fin d → Fin L) :
    omegaQ q d L θ k = omega2D 0 d L (k + turnShift n) := by
  rw [← omegaQ_zero_charge d L θ]
  unfold omegaQ
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc μ, zero_mul, add_zero, cos_shift (Nat.pos_of_ne_zero (NeZero.ne L)) (k μ) (n μ)]
  have hv : (((k + turnShift n : Fin d → Fin L) μ : Fin L) : ℕ) = ((k μ : ℕ) + n μ) % L := by
    rw [Pi.add_apply, Fin.val_add]
    exact Nat.add_mod_mod _ _ _
  rw [hv]

/-- **The kept-band log-determinant read of the charged modes at a whole-turn background is the photon's.** -/
theorem logDetQ_centre (q : ℝ) {d L : ℕ} [NeZero L] (θ : Fin d → ℝ) (n : Fin d → ℕ)
    (hc : ∀ μ, q * θ μ = 2 * π * (n μ : ℝ)) : logDetQ q d L θ = logDetD 0 d L := by
  unfold logDetQ logDetD
  rw [Finset.sum_filter, Finset.sum_filter]
  simp_rw [omegaQ_centre_shift q θ n hc]
  exact Equiv.sum_comp (Equiv.addRight (turnShift n))
    (fun k => if omega2D 0 d L k ≠ 0 then Real.log (omega2D 0 d L k) else 0)

/-- **The twisted-minus-untwisted entropy read** of the charged modes: the kept-band log-determinant at the
background `θ` less the photon's. DERIVED: `0` the neutral reference. -/
def entropicShift (q : ℝ) (d L : ℕ) (θ : Fin d → ℝ) : ℝ := logDetQ q d L θ - logDetD 0 d L

/-- **The entropy read vanishes at every whole-turn background**, at every side and dimension. -/
theorem entropicShift_centre (q : ℝ) {d L : ℕ} [NeZero L] (θ : Fin d → ℝ) (n : Fin d → ℕ)
    (hc : ∀ μ, q * θ μ = 2 * π * (n μ : ℝ)) : entropicShift q d L θ = 0 := by
  rw [entropicShift, logDetQ_centre q θ n hc, sub_self]

/-- **The mode-count read is a read of the spectrum, not of its labels.** -/
theorem occ_comp_equiv {ι : Type*} [Fintype ι] (σ : ι ≃ ι) (w : ι → ℝ) :
    FloorModes.occ Finset.univ (w ∘ σ) = FloorModes.occ Finset.univ w := by
  unfold FloorModes.occ
  have hs : ∑ i, (w ∘ σ) i = ∑ i, w i := Equiv.sum_comp σ w
  rw [hs]
  congr 1
  exact Equiv.sum_comp σ (fun j => Real.negMulLog (w j / ∑ i, w i))

/-- **The mode-count read of the charged power `1/ω²` at a whole-turn background is the photon's.** -/
theorem occ_centre (q : ℝ) {d L : ℕ} [NeZero L] (θ : Fin d → ℝ) (n : Fin d → ℕ)
    (hc : ∀ μ, q * θ μ = 2 * π * (n μ : ℝ)) :
    FloorModes.occ Finset.univ (fun k => (omegaQ q d L θ k)⁻¹)
      = FloorModes.occ Finset.univ (fun k => (omega2D 0 d L k)⁻¹) := by
  have h : (fun k => (omegaQ q d L θ k)⁻¹)
      = (fun k => (omega2D 0 d L k)⁻¹) ∘ (Equiv.addRight (turnShift n)) := by
    funext k
    simp only [Function.comp_apply, Equiv.coe_addRight, omegaQ_centre_shift q θ n hc]
  rw [h, occ_comp_equiv]

/-- **The `SU(2)` centre twist**: charge `2`, fundamental angles in `{0, π}`; the charged entropy read is
`0`. DERIVED: `2` the root charge, `π` the centre angle, `1` the single turn. -/
theorem su2_centre_entropicShift {d L : ℕ} [NeZero L] (θ : Fin d → ℝ) (hθ : ∀ μ, θ μ = 0 ∨ θ μ = π) :
    entropicShift 2 d L θ = 0 := by
  classical
  refine entropicShift_centre 2 θ (fun μ => if θ μ = 0 then 0 else 1) fun μ => ?_
  rcases hθ μ with h | h
  · simp [h]
  · have hne : θ μ ≠ 0 := by rw [h]; exact Real.pi_pos.ne'
    rw [if_neg hne, h, Nat.cast_one, mul_one]

/-! ### The ring across the sheet -/

/-- **The covariant form of a charged field on a graph**: `Σ_e ‖ψ(tgt e) − U_e ψ(src e)‖²`. DERIVED: `2`
the square. -/
def covForm {V ε : Type*} [Fintype ε] (src tgt : ε → V) (U : ε → ℂ) (ψ : V → ℂ) : ℝ :=
  ∑ e, ‖ψ (tgt e) - U e * ψ (src e)‖ ^ 2

/-- **Gauge covariance**: a unit-modulus relabelling moves the phases to `U_e g(src e) conj g(tgt e)`. -/
theorem covForm_gauge {V ε : Type*} [Fintype ε] (src tgt : ε → V) (U : ε → ℂ) (g : V → ℂ)
    (hg : ∀ v, ‖g v‖ = 1) (ψ : V → ℂ) :
    covForm src tgt U (fun v => g v * ψ v)
      = covForm src tgt (fun e => U e * g (src e) * conj (g (tgt e))) ψ := by
  unfold covForm
  refine Finset.sum_congr rfl fun e _ => ?_
  have hgt : g (tgt e) * conj (g (tgt e)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hg]
    norm_num
  have h : g (tgt e) * ψ (tgt e) - U e * (g (src e) * ψ (src e))
      = g (tgt e) * (ψ (tgt e) - U e * g (src e) * conj (g (tgt e)) * ψ (src e)) := by
    linear_combination (U e * g (src e) * ψ (src e)) * hgt
  rw [h, norm_mul, hg, one_mul]

/-- **The diamagnetic inequality**: unit link phases never lower the form below the neutral form of the
moduli. DERIVED: `1` the unit modulus and the neutral phase. -/
theorem covForm_diamagnetic {V ε : Type*} [Fintype ε] (src tgt : ε → V) (U : ε → ℂ)
    (hU : ∀ e, ‖U e‖ = 1) (ψ : V → ℂ) :
    covForm src tgt (fun _ => 1) (fun v => ((‖ψ v‖ : ℝ) : ℂ)) ≤ covForm src tgt U ψ := by
  unfold covForm
  refine Finset.sum_le_sum fun e _ => ?_
  have h1 : ‖((‖ψ (tgt e)‖ : ℝ) : ℂ) - 1 * ((‖ψ (src e)‖ : ℝ) : ℂ)‖
      = |‖ψ (tgt e)‖ - ‖U e * ψ (src e)‖| := by
    rw [one_mul, norm_mul, hU, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  beta_reduce
  rw [h1]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le _ _) 2

/-- **The link phases of a ring** of `L + 1` sites. -/
def ringU {L : ℕ} (φ : Fin (L + 1) → ℝ) (e : Fin (L + 1)) : ℂ := Complex.exp ((φ e : ℂ) * Complex.I)

/-- A profile read on `ℕ`, `0` past the ring. -/
def extend {L : ℕ} (φ : Fin (L + 1) → ℝ) (k : ℕ) : ℝ := if h : k < L + 1 then φ ⟨k, h⟩ else 0

/-- **The gauge angle** carrying the profile `φ` to `ψ`: the running sum of their differences. -/
def gaugeAngle {L : ℕ} (φ ψ : Fin (L + 1) → ℝ) (j : ℕ) : ℝ := ∑ k ∈ range j, (extend φ k - extend ψ k)

theorem extend_fin {L : ℕ} (φ : Fin (L + 1) → ℝ) (i : Fin (L + 1)) : extend φ i = φ i := by
  simp [extend, i.isLt]

/-- **The gauge angle closes the ring up to whole turns.** DERIVED: `2π` the period. -/
theorem ring_angle {L : ℕ} (φ ψ : Fin (L + 1) → ℝ) (n : ℤ) (h : ∑ i, φ i = ∑ i, ψ i + n * (2 * π))
    (e : Fin (L + 1)) : ∃ m : ℤ,
      φ e + gaugeAngle φ ψ e - gaugeAngle φ ψ (finRotate (L + 1) e) = ψ e + m * (2 * π) := by
  by_cases he : e = Fin.last L
  · refine ⟨n, ?_⟩
    have hall : ∑ k ∈ range (L + 1), (extend φ k - extend ψ k) = n * (2 * π) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => extend φ k - extend ψ k)]
      simp only [extend_fin]
      rw [Finset.sum_sub_distrib, h]
      ring
    rw [Finset.sum_range_succ] at hall
    have hl : extend φ L = φ e ∧ extend ψ L = ψ e := by
      subst he
      exact ⟨by simpa using extend_fin φ (Fin.last L), by simpa using extend_fin ψ (Fin.last L)⟩
    have hr : ((finRotate (L + 1) e : Fin (L + 1)) : ℕ) = 0 := by
      subst he
      simp
    have hv : (e : ℕ) = L := by subst he; simp
    rw [hr, hv, ← hl.1, ← hl.2]
    simp only [gaugeAngle, Finset.range_zero, Finset.sum_empty]
    linarith
  · refine ⟨0, ?_⟩
    have hv : ((finRotate (L + 1) e : Fin (L + 1)) : ℕ) = e + 1 := coe_finRotate_of_ne_last he
    rw [hv]
    simp only [gaugeAngle, Finset.sum_range_succ, extend_fin]
    push_cast
    ring

/-- **On a ring, a profile is pure gauge up to its total.** Two profiles whose totals differ by whole turns
give the same covariant form up to a unit-modulus relabelling. -/
theorem ring_gauge {L : ℕ} (φ ψ : Fin (L + 1) → ℝ) (n : ℤ) (h : ∑ i, φ i = ∑ i, ψ i + n * (2 * π)) :
    ∃ g : Fin (L + 1) → ℂ, (∀ v, ‖g v‖ = 1) ∧ ∀ f : Fin (L + 1) → ℂ,
      covForm id (finRotate (L + 1)) (ringU φ) (fun v => g v * f v)
        = covForm id (finRotate (L + 1)) (ringU ψ) f := by
  have hg : ∀ v : Fin (L + 1), ‖Complex.exp ((gaugeAngle φ ψ v : ℂ) * Complex.I)‖ = 1 :=
    fun v => Complex.norm_exp_ofReal_mul_I _
  refine ⟨fun v => Complex.exp ((gaugeAngle φ ψ v : ℂ) * Complex.I), hg, fun f => ?_⟩
  rw [covForm_gauge id (finRotate (L + 1)) (ringU φ)
    (fun v => Complex.exp ((gaugeAngle φ ψ v : ℂ) * Complex.I)) hg f]
  refine congrArg (fun U => covForm id (finRotate (L + 1)) U f) (funext fun e => ?_)
  obtain ⟨m, hm⟩ := ring_angle φ ψ n h e
  simp only [id, ringU]
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  have hc := congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hm
  push_cast at hc
  have harg : (φ e : ℂ) * Complex.I + (gaugeAngle φ ψ e : ℂ) * Complex.I
      + (gaugeAngle φ ψ (finRotate (L + 1) e) : ℂ) * -Complex.I
      = (ψ e : ℂ) * Complex.I + (m : ℂ) * (2 * π * Complex.I) := by
    linear_combination hc
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Every layered `SU(2)` centre profile is invisible to the charged gluons on the ring.** Fundamental
angles totalling `π`, seen at charge `2`, give the untwisted form up to a unit-modulus relabelling.
DERIVED: `2` the root charge, `π` the centre angle, `1` the single turn. -/
theorem su2_ring_profile_free {L : ℕ} (θ : Fin (L + 1) → ℝ) (hθ : ∑ i, θ i = π) :
    ∃ g : Fin (L + 1) → ℂ, (∀ v, ‖g v‖ = 1) ∧ ∀ f : Fin (L + 1) → ℂ,
      covForm id (finRotate (L + 1)) (ringU fun i => 2 * θ i) (fun v => g v * f v)
        = covForm id (finRotate (L + 1)) (ringU fun _ => 0) f := by
  refine ring_gauge _ _ 1 ?_
  rw [← Finset.mul_sum, hθ]
  simp only [Finset.sum_const_zero, Int.cast_one]
  ring

/-! ## 3. The sheet free energy -/

/-- **The sheet free energy per coarse cell**: classical cost less the entropic term `c log L`. CHOSEN: the
shape. -/
def sheetF (β cost c : ℝ) (L : ℕ) : ℝ := β * cost - c * Real.log L

/-- **A positive entropic coefficient brings every coupling below the entropy** for thick enough sheets.
DERIVED: `¼ ln 3` from `VortexEntropy.floorTerm_summable_iff`. -/
theorem sheetF_falls {c : ℝ} (hc : 0 < c) (β cost : ℝ) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → sheetF β cost c L < 1 / 4 * Real.log 3 := by
  have ht : Tendsto (fun L : ℕ => Real.log L) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (ht.eventually_gt_atTop ((β * cost - 1 / 4 * Real.log 3) / c))
  refine ⟨L₀, fun L hL => ?_⟩
  have h := (div_lt_iff₀ hc).mp (hL₀ L hL)
  have h' : β * cost - 1 / 4 * Real.log 3 < c * Real.log L := by rw [mul_comm c]; exact h
  unfold sheetF
  linarith

/-- **A non-positive entropic coefficient never does.** DERIVED: `1` the least side; `¼ ln 3`, the `1 / 4`
and `3` of `1 / 4 * Real.log 3`, from `VortexEntropy.floorTerm_summable_iff`. -/
theorem sheetF_stays {c : ℝ} (hc : c ≤ 0) {L : ℕ} (hL : 1 ≤ L) {β cost : ℝ}
    (h : 1 / 4 * Real.log 3 < β * cost) : 1 / 4 * Real.log 3 < sheetF β cost c L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have h2 := mul_le_mul_of_nonneg_right hc hlog
  rw [zero_mul] at h2
  unfold sheetF
  linarith

/-- **The chain read gives no separator.** With the entropic coefficient `0` (both groups: `u1_freeEnergy`,
`su2_centre_entropicShift`, `su2_ring_profile_free`), every admissible Cartan profile at
`β > π² ln 3/(8θ²)` keeps the sheet free energy above the entropy at every thickness.
DERIVED: `π² ln 3/(8θ²)` from `ThickSheetCost.trial_summable`. -/
theorem chain_model_no_separator {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : θ ≠ 0) {Φ : Fin m → Fin m → ℝ}
    (hsum : ∀ s, ∑ i, Φ s i = θ) (hπ : ∀ s i, |Φ s i| ≤ π) {β : ℝ}
    (hβ : π ^ 2 * Real.log 3 / (8 * θ ^ 2) < β) {L : ℕ} (hL : 1 ≤ L) :
    1 / 4 * Real.log 3 < sheetF β (ThickSheetCost.cellCost Φ) 0 L := by
  have hc := ThickSheetCost.cellCost_ge hm hsum hπ
  have hθ2 : 0 < θ ^ 2 := lt_of_le_of_ne (sq_nonneg θ) (Ne.symm (pow_ne_zero 2 hθ))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hπ2 : 0 < π ^ 2 := pow_pos Real.pi_pos 2
  have h8 : 0 < 8 * θ ^ 2 := mul_pos (by norm_num) hθ2
  have hβpos : 0 < β := lt_of_le_of_lt (div_nonneg (mul_nonneg hπ2.le hlog3.le) h8.le) hβ
  have h1 : π ^ 2 * Real.log 3 < β * (8 * θ ^ 2) := (div_lt_iff₀ h8).mp hβ
  have key : 1 / 4 * Real.log 3 < β * (2 * θ ^ 2 / π ^ 2) := by
    rw [mul_div_assoc', lt_div_iff₀ hπ2]
    nlinarith [h1]
  exact sheetF_stays le_rfl hL (lt_of_lt_of_le key (mul_le_mul_of_nonneg_left hc hβpos.le))

end MassGap.FluctSheet

#print axioms MassGap.FluctSheet.fluct_form
#print axioms MassGap.FluctSheet.twist_split
#print axioms MassGap.FluctSheet.twist_min
#print axioms MassGap.FluctSheet.u1_twisted_Z
#print axioms MassGap.FluctSheet.u1_freeEnergy
#print axioms MassGap.FluctSheet.cos_shift
#print axioms MassGap.FluctSheet.omegaQ_centre_shift
#print axioms MassGap.FluctSheet.logDetQ_centre
#print axioms MassGap.FluctSheet.entropicShift_centre
#print axioms MassGap.FluctSheet.occ_comp_equiv
#print axioms MassGap.FluctSheet.occ_centre
#print axioms MassGap.FluctSheet.su2_centre_entropicShift
#print axioms MassGap.FluctSheet.covForm_gauge
#print axioms MassGap.FluctSheet.covForm_diamagnetic
#print axioms MassGap.FluctSheet.extend_fin
#print axioms MassGap.FluctSheet.ring_angle
#print axioms MassGap.FluctSheet.ring_gauge
#print axioms MassGap.FluctSheet.su2_ring_profile_free
#print axioms MassGap.FluctSheet.sheetF_falls
#print axioms MassGap.FluctSheet.sheetF_stays
#print axioms MassGap.FluctSheet.chain_model_no_separator
