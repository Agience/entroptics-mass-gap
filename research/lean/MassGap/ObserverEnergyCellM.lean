import Mathlib
import MassGap.DobrushinUnbounded
import MassGap.ObserverEnergyMDob

noncomputable section

/-!
# MassGap.ObserverEnergyCellM — M for the energy density from the cell-energy view in Dobrushin's class

`ObserverEnergyMDob.CoarseViewDobrushin` asks every reading of `S` to be a bounded function of a fixed
number of coarse links, uniformly in the spacing. An energy-density reading smeared against a test
function spans `(R/a_k)⁴` fine sites, so no non-trivial one qualifies. This module takes as the coarse
view the field of physical-cell energies instead: the observer's energy density smeared against the
cells of a grid fixed at the coarse step `m0`. A fixed physical region holds a fixed number of cells at
every spacing, and the energy density smeared against a cell is, by definition, that cell's energy.

1. **The cell grid** (`cellDatum`, `cellE`, `cellDist`): a cell is a base datum (a field of the class
   and a base test function) translated by `a_{m0} z`, `z ∈ ℤ⁴`; its energy at step `k` is the field of
   step `k` smeared against it. Cells are `cellDist` apart by their time separation in grid units.
2. **E gives the cell moments** (`CellMoments`, `cellMoments_of_cube`): the cube moment bound E on the
   class, the positivity of the class and the subtraction bound give, eventually in `k`, every even
   moment of every cell energy, uniformly over the cells (`smearedMoments_of_cubeMoments` at the base
   cells, `smear_translate`, translation invariance `stateK_transObs`).
3. **The hypothesis** (`CellViewDobrushin`): for every truncation level `L > 0`, eventually in `k`, the
   step-`k` state read through the cell-energy field truncated at `L` has a truncated Dobrushin law of
   TV class `α` whose influence moves one cell per step (`DobrushinUnbounded.TruncLaw`); and the
   reflected and shifted readings of `S` are affine in finitely many cell energies, with weights and
   offsets bounded uniformly in the time separation, and cells more than `lv · n` apart at separation
   `n`.
4. **The chain** (`latClusterRateOn_of_cellView`, `energy_M_of_cellView`,
   `energy_M_of_cellView_cube`, `energy_M_of_cellView_90`): `CellViewDobrushin` and the cell moments
   give `LatClusterRateOn` at `(√θ)^{lv}` for every `θ ∈ (α, 1]` (`DobrushinUnbounded.cov_affine_rate`
   at the level `θ^{−lv n/4}`), hence M. At `α = 9/10`, `θ = 91/100`, `lv = 1`, the measured leakage
   `η = 0.093` passes.
5. **Non-vacuity of the readers** (`cellMono`, `cellSet`, `cellView_readers`, `exists_cell_margin`): the
   single-cell monomials of the grid, with `∅`, satisfy the reader clause at `lv = 1`; every base datum
   gives such a monomial beyond any margin. Each is a non-trivial energy-density reading.

## Scope

The truncated Dobrushin law of the cell-energy field is a hypothesis; nothing here derives it from the
fine measure. The reader clause is proved for single-cell monomials; a monomial with several factors
is a product of cell energies, not an affine reading, and is not in the set covered here.
-/

namespace MassGap.ObserverEnergyCellM

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.ObserverEnergyBox Filter
open MassGap.ContinuumNontrivial (stateK_transObs)
open MassGap.DobrushinUnbounded (TruncLaw affF cov_affine_rate)
open MassGap.ObserverEnergyMDob (eta_of_margin)
open scoped Topology

/-! ## 1. The cell grid and its moments -/

section Grid

/-- **A cell of the grid of step `m0`**: a base index and a lattice site of step `m0`.

DERIVED: no numeral. -/
abbrev Cell (nb : ℕ) : Type := Fin nb × ISite

/-- **The smeared-field datum of a cell**: the base field and the base test function translated by
`a_{m0} z`.

DERIVED: `2` the rank. -/
def cellDatum {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (c : Cell nb) : SField 2 :=
  ((base c.1).1, (base c.1).2.translate (site (dySpacing 2 m0) c.2))

/-- **The energy of a cell at step `k`**: the field of step `k` smeared against the cell.

DERIVED: `2` the rank. -/
def cellE (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 k : ℕ) (c : Cell nb) :
    C(Cfg 2, ℝ) :=
  smear (dySpacing 2 k) (Φ.map k (cellDatum base m0 c).1).1 (cellDatum base m0 c).2

/-- **The time separation of two cells** in grid units along `τ`.

DERIVED: `4` in `Fin 4` the spacetime dimension. -/
def cellDist (τ : Fin 4) {nb : ℕ} (c c' : Cell nb) : ℕ := (c.2 τ - c'.2 τ).natAbs

/-- **Uniform cell moments**: every even moment of every cell energy is bounded eventually in the
step, uniformly over the cells.

DERIVED: `2` makes the power even. -/
def CellMoments {Cl : Type} (e : ℕ → Cl → C(Cfg 2, ℝ)) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ c, stateK two_ne k (e k c ^ (2 * p)) ≤ C

/-- Translation commutes with powers.

DERIVED: no numeral. -/
theorem transObs_pow (x : ISite) (F : C(Cfg 2, ℝ)) (m : ℕ) :
    transObs x (F ^ m) = transObs x F ^ m := by
  ext U
  simp only [transObs_apply, ContinuousMap.pow_apply]

#print axioms transObs_pow

/-- **E gives the cell moments.** For a configuration flow `W`, a reflection-closed class `D` of
non-negative fields with subtraction of the order of the cell volume and the cube moment bound E on
`D`, and base data with fields in `D`, the cell energies of the class-scaled flow have uniform cell
moments (`smearedMoments_of_cubeMoments` at each base cell; for `k ≥ m0` the cell `z` is the lattice
translate by `2^{k−m0} z` of its base cell, `site_dySpacing`, `smear_translate`, and the state is
translation invariant, `stateK_transObs`).

DERIVED: `2` the rank and the even power; `0` the sign of the bound. -/
theorem cellMoments_of_cube (W : ConfFlow 2) (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne W O) {nb : ℕ} (base : Fin nb → SField 2)
    (hbase : ∀ i, (base i).1 ∈ D) (m0 : ℕ) :
    CellMoments (fun k => cellE (energyOn W D hD s hs) base m0 k) := by
  intro p
  have h := smearedMoments_of_cubeMoments two_ne W D hD s hs hpos hsub hcube
  choose C hC using fun i : Fin nb => h (base i).1 (hbase i) (base i).2 p
  refine ⟨∑ i, max (C i) 0, ?_⟩
  filter_upwards [Filter.eventually_all.2 hC, Filter.eventually_ge_atTop m0] with k hk hkm c
  have e1 : cellE (energyOn W D hD s hs) base m0 k c
      = transObs (scaleSite (2 ^ (k - m0)) c.2)
          (smear (dySpacing 2 k) ((energyOn W D hD s hs).map k (base c.1).1).1 (base c.1).2) := by
    unfold cellE cellDatum
    rw [site_dySpacing 2 hkm c.2, smear_translate (dySpacing_pos (by norm_num) k)]
  show stateK two_ne k (cellE (energyOn W D hD s hs) base m0 k c ^ (2 * p)) ≤ _
  rw [e1, ← transObs_pow, stateK_transObs]
  calc _ ≤ C c.1 := hk c.1
    _ ≤ max (C c.1) 0 := le_max_left _ _
    _ ≤ ∑ i, max (C i) 0 :=
        Finset.single_le_sum (fun i _ => le_max_right (C i) 0) (Finset.mem_univ c.1)

#print axioms cellMoments_of_cube

end Grid

/-! ## 2. The hypothesis and the chain to M -/

section Chain

/-- **The observer's cell-energy view is in Dobrushin's TV class, on the readers of `S`.** For a
cell type `Cl` with a cell distance `cd` and cell energies `e k c`:

* for every truncation level `L > 0`, eventually in the step `k`, the step-`k` state read through the
  cell-energy field truncated at `L` has a truncated Dobrushin law of TV class `α`, its influence
  moving at most one unit of `cd` per step (`DobrushinUnbounded.TruncLaw`);
* for every pair `P, Q ∈ S` there are bounds `W_b`, `B_b` such that at every time separation `n` the
  reflected smeared product of `P` and the smeared product of `Q` shifted by `aₘ₀ n` are, eventually
  in `k`, affine readings `b + Σ_{c ∈ A} w_c e_k c` with `Σ|w| ≤ W_b`, `|b| ≤ B_b`, and every cell of
  `A_P` more than `lv · n` from every cell of `A_Q`.

DERIVED: `2` the rank; `0` the reflection plane and the sign of `L`; `4` in `Fin 4` the spacetime
dimension. -/
def CellViewDobrushin (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 lv : ℕ) (α : ℝ)
    (S : Set (MarginMono 2 τ r)) {Cl : Type} [DecidableEq Cl] (cd : Cl → Cl → ℕ)
    (e : ℕ → Cl → C(Cfg 2, ℝ)) : Prop :=
  (∀ L : ℝ, 0 < L → ∀ᶠ k in atTop, TruncLaw (stateK two_ne k) (e k) L α cd) ∧
  ∀ P ∈ S, ∀ Q ∈ S, ∃ Wb Bb : ℝ, ∀ n : ℕ, ∃ (AP AQ : Finset Cl) (wP wQ : Cl → ℝ) (bP bQ : ℝ),
    ∑ c ∈ AP, |wP c| ≤ Wb ∧ ∑ c ∈ AQ, |wQ c| ≤ Wb ∧ |bP| ≤ Bb ∧ |bQ| ≤ Bb ∧
    (∀ c ∈ AP, ∀ c' ∈ AQ, lv * n < cd c c') ∧
    ∀ᶠ k in atTop,
      LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1))
          = affF (e k) AP wP bP ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1))
          = affF (e k) AQ wQ bQ

/-- The reflection of the unit observable is the unit observable.

DERIVED: `0` the reflection plane; `1` the unit. -/
theorem ireflObs_one (τ : Fin 4) :
    LatticeReflection.ireflObs τ 0 (1 : C(Cfg 2, ℝ)) = 1 := ContinuousMap.ext fun _ => rfl

#print axioms ireflObs_one

/-- **The cell view in Dobrushin's class gives lattice clustering at `(√θ)^{lv}`** for every
`θ ∈ (α, 1]`, with constant `4 W_b² θ²/(θ − α) + 2 μ₆ · 2 W_b Q`, `Q = 2 (B_b + W_b μ₂)`, `μ₂², μ₆²`
the second and sixth cell moments (`DobrushinUnbounded.cov_affine_rate` at `d = lv · n`, level
`θ^{−lv n/4}`; `latSF_pair_eq`, `prodSmear_empty`, `FlowCapstone.mono_empty`).

DERIVED: `2`, `4`, `6` as in `cov_affine_rate`; `1`, `3` the moment orders `2 · 1`, `2 · 3`; `0` the
reflection plane and the signs. -/
theorem latClusterRateOn_of_cellView {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ} {α : ℝ}
    {S : Set (MarginMono 2 τ r)} {Cl : Type} [DecidableEq Cl] {cd : Cl → Cl → ℕ}
    {e : ℕ → Cl → C(Cfg 2, ℝ)} (hV : CellViewDobrushin Φ τ r m0 lv α S cd e)
    (hM : CellMoments e) {θ : ℝ} (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) :
    LatClusterRateOn two_ne Φ τ r m0 (Real.sqrt θ ^ lv) S := by
  obtain ⟨hlaw, hread⟩ := hV
  intro P hP Q hQ
  obtain ⟨Wb, Bb, h⟩ := hread P hP Q hQ
  obtain ⟨C2, hC2⟩ := hM 1
  obtain ⟨C6, hC6⟩ := hM 3
  have hm2 : Real.sqrt (max C2 0) ^ 2 = max C2 0 := Real.sq_sqrt (le_max_right _ _)
  have hm6 : Real.sqrt (max C6 0) ^ 2 = max C6 0 := Real.sq_sqrt (le_max_right _ _)
  refine ⟨4 * Wb * Wb * θ ^ 2 / (θ - α) + 2 * Real.sqrt (max C6 0)
    * (Wb * (2 * (Bb + Wb * Real.sqrt (max C2 0)))
      + 2 * (Bb + Wb * Real.sqrt (max C2 0)) * Wb), fun n => ?_⟩
  obtain ⟨AP, AQ, wP, wQ, bP, bQ, hWP, hWQ, hBP, hBQ, hsep, hrd⟩ := h n
  have hθ : 0 < θ := lt_of_le_of_lt hα0 hαθ
  have hLpos : 0 < (Real.sqrt (Real.sqrt θ))⁻¹ ^ (lv * n) :=
    pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hθ))) _
  filter_upwards [hlaw _ hLpos, hrd, hC2, hC6] with k hk hrk h2 h6
  obtain ⟨hPk, hQk⟩ := hrk
  have e1 : latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k (affF (e k) AP wP bP * affF (e k) AQ wQ bQ) := by
    rw [latSF_pair_eq, hPk, hQk]
  have e2 : latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2))
      = stateK two_ne k (affF (e k) AP wP bP) := by
    rw [latSF_pair_eq, hPk, mono_empty, prodSmear_empty, mul_one]
  have e3 : latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k (affF (e k) AQ wQ bQ) := by
    rw [latSF_pair_eq, hQk, mono_empty, prodSmear_empty, ireflObs_one, one_mul]
  rw [e1, e2, e3]
  have hb := cov_affine_rate (lv * n) hk hα0 hαθ hθ1 AP AQ wP wQ bP bQ hWP hWQ hBP hBQ
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun c _ => by
      have := h2 c
      rw [show 2 * 1 = 2 from rfl, pow_two] at this
      rw [hm2]; exact this.trans (le_max_left _ _))
    (fun c _ => by
      have := h6 c
      rw [show 2 * 3 = 6 from rfl] at this
      rw [hm6]; exact this.trans (le_max_left _ _))
    hsep
  rw [← pow_mul]
  exact hb

#print axioms latClusterRateOn_of_cellView

/-- **M for the energy density from the cell view in Dobrushin's class.** `CellViewDobrushin` of
class `α` on a set `S ∋ ∅` with `lv ≥ 1`, uniform cell moments, any `θ ∈ (α, 1)`, and the leakage
inputs on `coarseSpan S` at time `k ≥ 1` with `ρr² < 1` and `η² < (1 − (√θ)^{2 lv k})(1 − ρr²)` give
`FlowClusterAbs` (`latClusterRateOn_of_cellView`, `ObserverEnergyMClose.energy_M_of_rate_leak`).

DERIVED: `2` the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_cellView {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    {Cl : Type} [DecidableEq Cl] (cd : Cl → Cl → ℕ) (e : ℕ → Cl → C(Cfg 2, ℝ))
    (hV : CellViewDobrushin (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S cd e)
    (hM : CellMoments e) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((Real.sqrt θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hs1 : Real.sqrt θ < 1 := (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hθ1)
  exact energy_M_of_rate_leak hc0 hc n R D hD s hs hB τ hphys m0 S hS
    (pow_nonneg (Real.sqrt_nonneg θ) lv) (pow_lt_one₀ (Real.sqrt_nonneg θ) hs1 hlv.ne')
    (latClusterRateOn_of_cellView hV hM hα0 hαθ hθ1.le) hk hρr hη hL hLw

#print axioms energy_M_of_cellView

/-- **M from E and the cell view.** The cube moment bound E on a class `D` of non-negative fields
with subtraction of the order of the cell volume supplies the cell moments of the grid of base data in
`D` (`cellMoments_of_cube`); with `CellViewDobrushin` on that grid, M follows as in
`energy_M_of_cellView`.

DERIVED: `2` the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_cellView_cube {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D)
    (hV : CellViewDobrushin (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S (cellDist τ)
      (fun k => cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k))
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((Real.sqrt θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellView hc0 hc n R D hD s hs hB τ hphys m0 S hS hlv (cellDist τ) _ hV
    (cellMoments_of_cube (obsConfFlow c hc0 hc n R) D hD s hs hpos hsub hcube base hbase m0)
    hα0 hαθ hθ1 hk hρr hη hL hLw

#print axioms energy_M_of_cellView_cube

/-- **The η demand at the rate `(√θ)^{lv}`, reduced to one step.** For `0 ≤ θ ≤ 1`, `lv · k ≥ 1`
and `ρr² ≤ 13/20`, `η² < (1 − θ) · 7/20` gives `η² < (1 − (√θ)^{2 lv k})(1 − ρr²)`
(`ObserverEnergyMDob.eta_of_margin` at `√θ`).

DERIVED: `13/20`, `7/20` as in `eta_of_margin`; `1` the least `lv · k`; `2` the degree. -/
theorem eta_cell_of_margin {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {lv k : ℕ} (hlk : 1 ≤ lv * k)
    {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20) (hη : η ^ 2 < (1 - θ) * (7 / 20)) :
    η ^ 2 < (1 - ((Real.sqrt θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (Real.sqrt_nonneg θ) (Real.sqrt_le_one.mpr hθ1) hlk hρr
    (by rw [Real.sq_sqrt hθ0]; exact hη)

#print axioms eta_cell_of_margin

/-- **M from E and the cell view at `α = 9/10`, at the measured leakage.** If the cell view is in TV
class `9/10` with `lv ≥ 1`, E holds on the class, and the leakage inputs hold at time `k ≥ 1` with
`η = 0.093` and `ρr² ≤ 13/20`, then `FlowClusterAbs` holds (`energy_M_of_cellView_cube` at
`θ = 91/100`; `0.008649 < (1 − 0.91) · 0.35 = 0.0315`).

DERIVED: `9/10` the class; `91/100` the rate; `93/1000` the leakage `η = 0.093` measured at one coarse
step; `13/20`, `7/20` as in `eta_of_margin`; `2` the rank; `1/6` the dominance bound; `0` and `1`
bracket `lv`, `k`, `L`. -/
theorem energy_M_of_cellView_90 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hsub : ∀ O ∈ D, ScaledSubtractionBound 2 s O)
    (hcube : ∀ O ∈ D, CubeMomentBound two_ne (obsConfFlow c hc0 hc n R) O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv)
    {nb : ℕ} (base : Fin nb → SField 2) (hbase : ∀ i, (base i).1 ∈ D)
    (hV : CellViewDobrushin (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv (9 / 10) S (cellDist τ)
      (fun k => cellE (obsEnergyOn c hc0 hc n R D hD s hs) base m0 k))
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr
      (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_cellView_cube hc0 hc n R D hD s hs hpos hsub hcube hB τ hphys m0 S hS hlv base hbase
    hV (by norm_num) (by norm_num : (9 / 10 : ℝ) < 91 / 100) (by norm_num) hk (by linarith)
    (eta_cell_of_margin (by norm_num) (by norm_num)
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hlv.ne' hk.ne')) hρr (by norm_num)) hL hLw

#print axioms energy_M_of_cellView_90

end Chain

/-! ## 3. Non-vacuity: single-cell monomials are affine cell readings -/

section NonVacuity

/-- **The single-cell monomial**: one factor, the datum of the cell.

DERIVED: `1` the number of factors; `2` the rank. -/
def cellMono {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (c : Cell nb) : Mono 2 :=
  ⟨1, fun _ => cellDatum base m0 c⟩

/-- **The reflected lattice site**: the `τ` coordinate negated.

DERIVED: `4` in `Fin 4` the spacetime dimension. -/
def reflZ (τ : Fin 4) (z : ISite) : ISite := Function.update z τ (-z τ)

/-- The reflection of a lattice vector is the lattice vector of the reflected site.

DERIVED: `4` in `Fin 4` the spacetime dimension. -/
theorem reflR_site (τ : Fin 4) (a : ℝ) (z : ISite) : reflR τ (site a z) = site a (reflZ τ z) := by
  funext i
  by_cases h : i = τ
  · subst h
    simp [reflR, reflZ, site]
  · simp [reflR, reflZ, site, Function.update_of_ne h]

#print axioms reflR_site

/-- **The reflection of a translated test function** is the reflected test function translated by
the reflected vector. An alias of `ContinuumField.TestFn.reflect_translate`. -/
alias reflect_translate := MassGap.ContinuumField.TestFn.reflect_translate

#print axioms reflect_translate

/-- **A shifted single-cell monomial reads one cell**: shifted by `aₘ₀ n` along `τ` it is the energy
of the cell `z + n e_τ`, an affine reading with one unit weight and no offset.

DERIVED: `1` the weight; `0` the offset; `2` the rank. -/
theorem prodSmear_cellMono_shift (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 k : ℕ)
    (τ : Fin 4) (n : ℤ) (c : Cell nb) :
    prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) (cellMono base m0 c)))
      = affF (cellE Φ base m0 k) {(c.1, c.2 + axisVec τ n)} (fun _ => 1) 0 := by
  ext U
  show (∏ i : Fin 1, smear (dySpacing 2 k) (Φ.map k (base c.1).1).1
      (((base c.1).2.translate (site (dySpacing 2 m0) c.2)).translate (timeVec 2 m0 τ n))) U
    = 0 + ∑ c' ∈ {(c.1, c.2 + axisVec τ n)}, 1 * cellE Φ base m0 k c' U
  rw [Fin.prod_univ_one, Finset.sum_singleton, zero_add, one_mul, TestFn.translate_translate]
  unfold cellE cellDatum timeVec
  rw [site_add]

#print axioms prodSmear_cellMono_shift

/-- **A reflected single-cell monomial reads one cell**: if the base datum `ρ i` is the reflection
of the base datum `i`, the reflected reading of the cell `(i, z)` is the energy of the cell
`(ρ i, reflZ z)` (`ireflObs_smear`, `Flow.map_refl`, `reflect_translate`, `reflR_site`).

DERIVED: `0` the reflection plane and the offset; `1` the weight; `2` the rank. -/
theorem ireflObs_cellMono (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 k : ℕ) (τ : Fin 4)
    (ρ : Fin nb → Fin nb) (c : Cell nb) (hρ : base (ρ c.1) = SField.refl τ (base c.1)) :
    LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k (cellMono base m0 c)))
      = affF (cellE Φ base m0 k) {(ρ c.1, reflZ τ c.2)} (fun _ => 1) 0 := by
  have ha : 0 < dySpacing 2 k := dySpacing_pos (by norm_num) k
  have e0 : prodSmear (dySpacing 2 k) (Φ.mono k (cellMono base m0 c))
      = smear (dySpacing 2 k) (Φ.map k (base c.1).1).1
          ((base c.1).2.translate (site (dySpacing 2 m0) c.2)) := by
    show (∏ i : Fin 1, smear (dySpacing 2 k) (Φ.map k (base c.1).1).1
      ((base c.1).2.translate (site (dySpacing 2 m0) c.2))) = _
    rw [Fin.prod_univ_one]
  rw [e0, ireflObs_smear ha]
  have e1 : LatticeReflection.ireflObs τ 0 (Φ.map k (base c.1).1).1
      = (Φ.map k ((base c.1).1.refl τ)).1 := by
    rw [Φ.map_refl]; rfl
  rw [e1, reflect_translate, reflR_site]
  ext U
  show _ = 0 + ∑ c' ∈ {(ρ c.1, reflZ τ c.2)}, 1 * cellE Φ base m0 k c' U
  rw [Finset.sum_singleton, zero_add, one_mul]
  unfold cellE cellDatum
  rw [hρ]
  rfl

#print axioms ireflObs_cellMono

/-- **The set of single-cell margin monomials and `∅`**: the empty monomial, and the monomials of one
cell `(i, z)` with `i ∈ I` and `z_τ ≥ 1`.

DERIVED: `1` the least time coordinate in grid units; `2` the rank. -/
def cellSet {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (I : Set (Fin nb)) : Set (MarginMono 2 τ r) :=
  {P | P.1 = emptyMono 2 ∨ ∃ c : Cell nb, c.1 ∈ I ∧ 1 ≤ c.2 τ ∧ P.1 = cellMono base m0 c}

/-- The empty monomial reads the unit observable, shifted or not.

DERIVED: `0` the number of factors. -/
theorem prodSmear_shift_empty (Φ : Flow 2) (k : ℕ) (v : Fin 4 → ℝ) :
    prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift v (emptyMono 2))) = 1 := by
  unfold prodSmear
  exact Fin.prod_univ_zero _

#print axioms prodSmear_shift_empty

/-- The unit observable is the affine reading of no cell with offset `1`.

DERIVED: `1` the offset. -/
theorem affF_empty {Cl : Type} (e : Cl → C(Cfg 2, ℝ)) (w : Cl → ℝ) :
    affF e ∅ w 1 = 1 := by
  ext U
  show 1 + ∑ c ∈ (∅ : Finset Cl), w c * e c U = 1
  rw [Finset.sum_empty, add_zero]

#print axioms affF_empty

/-- **The reader clause holds on the single-cell monomials.** For a base family with a reflection
map `ρ` on `I` (`base (ρ i) = θ_τ (base i)`), every pair `P, Q` of `cellSet` has, at every time
separation `n`, the reflected reading of `P` and the shifted reading of `Q` affine in at most one
cell energy each, with unit weights and offsets `≤ 1`, and their cells more than `n` apart in time:
the reflected cell of `P` sits at time `≤ −1`, the shifted cell of `Q` at time `≥ n + 1`. This is the
reader clause of `CellViewDobrushin` at `lv = 1` with `cd = cellDist τ`.

DERIVED: `1` the weight, the offset bound, `lv` and the least time coordinate; `0` the offsets and the
reflection plane; `2` the rank. -/
theorem cellView_readers (Φ : Flow 2) {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4)
    (r : ℝ) (I : Set (Fin nb)) (ρ : Fin nb → Fin nb)
    (hρ : ∀ i ∈ I, base (ρ i) = SField.refl τ (base i)) :
    ∀ P ∈ cellSet base m0 τ r I, ∀ Q ∈ cellSet base m0 τ r I, ∃ Wb Bb : ℝ, ∀ n : ℕ,
      ∃ (AP AQ : Finset (Cell nb)) (wP wQ : Cell nb → ℝ) (bP bQ : ℝ),
        ∑ c ∈ AP, |wP c| ≤ Wb ∧ ∑ c ∈ AQ, |wQ c| ≤ Wb ∧ |bP| ≤ Bb ∧ |bQ| ≤ Bb ∧
        (∀ c ∈ AP, ∀ c' ∈ AQ, 1 * n < cellDist τ c c') ∧
        ∀ᶠ k in atTop,
          LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1))
              = affF (cellE Φ base m0 k) AP wP bP ∧
            prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1))
              = affF (cellE Φ base m0 k) AQ wQ bQ := by
  -- the reflected reading of `P`: cells at time `≤ -1`
  have hPr : ∀ P ∈ cellSet base m0 τ r I, ∃ (AP : Finset (Cell nb)) (bP : ℝ),
      ∑ c ∈ AP, |(fun _ : Cell nb => (1 : ℝ)) c| ≤ 1 ∧ |bP| ≤ 1 ∧ (∀ c ∈ AP, c.2 τ ≤ -1) ∧
      ∀ k, LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1))
        = affF (cellE Φ base m0 k) AP (fun _ => 1) bP := by
    intro P hP
    rcases hP with h0 | ⟨c, hcI, hc1, hc⟩
    · refine ⟨∅, 1, by simp, by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun k => ?_⟩
      rw [h0, mono_empty, prodSmear_empty, ireflObs_one, affF_empty]
    · refine ⟨{(ρ c.1, reflZ τ c.2)}, 0, by simp, by simp, fun c' hc' => ?_, fun k => ?_⟩
      · rw [Finset.mem_singleton.1 hc']
        have h1 := hc1
        simp only [reflZ, Function.update_self]
        omega
      · rw [hc]
        exact ireflObs_cellMono Φ base m0 k τ ρ c (hρ c.1 hcI)
  -- the shifted reading of `Q`: cells at time `≥ n + 1`
  have hQr : ∀ Q ∈ cellSet base m0 τ r I, ∀ n : ℕ, ∃ (AQ : Finset (Cell nb)) (bQ : ℝ),
      ∑ c ∈ AQ, |(fun _ : Cell nb => (1 : ℝ)) c| ≤ 1 ∧ |bQ| ≤ 1 ∧
      (∀ c ∈ AQ, (n : ℤ) + 1 ≤ c.2 τ) ∧
      ∀ k, prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1))
        = affF (cellE Φ base m0 k) AQ (fun _ => 1) bQ := by
    intro Q hQ n
    rcases hQ with h0 | ⟨c, -, hc1, hc⟩
    · refine ⟨∅, 1, by simp, by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun k => ?_⟩
      rw [h0, prodSmear_shift_empty, affF_empty]
    · refine ⟨{(c.1, c.2 + axisVec τ n)}, 0, by simp, by simp, fun c' hc' => ?_, fun k => ?_⟩
      · rw [Finset.mem_singleton.1 hc']
        show (n : ℤ) + 1 ≤ c.2 τ + axisVec τ n τ
        have hax : axisVec τ (n : ℤ) τ = n := by simp [axisVec]
        rw [hax]
        linarith
      · rw [hc]
        exact prodSmear_cellMono_shift Φ base m0 k τ n c
  intro P hP Q hQ
  refine ⟨1, 1, fun n => ?_⟩
  obtain ⟨AP, bP, hWP, hBP, hAP, hrP⟩ := hPr P hP
  obtain ⟨AQ, bQ, hWQ, hBQ, hAQ, hrQ⟩ := hQr Q hQ n
  refine ⟨AP, AQ, fun _ => 1, fun _ => 1, bP, bQ, hWP, hWQ, hBP, hBQ, fun c hc c' hc' => ?_,
    Filter.Eventually.of_forall fun k => ⟨hrP k, hrQ k⟩⟩
  have h1 := hAP c hc
  have h2 := hAQ c' hc'
  unfold cellDist
  omega

#print axioms cellView_readers

/-- **Every base datum gives a single-cell margin monomial beyond any margin.** For a base datum `i`
and any margin `r`, some cell `(i, N e_τ)` with `N ≥ 1` has its test function supported at times
`≥ d` for a `d > max r 0` (the base test function is supported in `[-R, R]⁴`; take `aₘ₀ N > R + |r| + 1`).

DERIVED: `1` the least `N` and the margin gap; `0` the sign of `d`; `2` the rank. -/
theorem exists_cell_margin {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (i : Fin nb) : ∃ c : Cell nb, c.1 = i ∧ 1 ≤ c.2 τ ∧
      ∃ d : ℝ, 0 < d ∧ r < d ∧ posAt τ d (cellMono base m0 c) := by
  obtain ⟨R, M, hR, hM, hs⟩ := (base i).2.2
  have ha : 0 < dySpacing 2 m0 := dySpacing_pos (by norm_num) m0
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + |r| + 1) / dySpacing 2 m0)
  have hN' : R + |r| + 1 < dySpacing 2 m0 * ((N + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ ha] at hN
    push_cast
    nlinarith
  refine ⟨(i, axisVec τ ((N + 1 : ℕ) : ℤ)), rfl, ?_, dySpacing 2 m0 * ((N + 1 : ℕ) : ℝ) - R,
    by linarith [abs_nonneg r], by linarith [le_abs_self r], ?_⟩
  · show (1 : ℤ) ≤ axisVec τ ((N + 1 : ℕ) : ℤ) τ
    simp [axisVec]
  · intro j y hy
    have h1 := hs (y - site (dySpacing 2 m0) (axisVec τ ((N + 1 : ℕ) : ℤ))) hy τ
    have e : (y - site (dySpacing 2 m0) (axisVec τ ((N + 1 : ℕ) : ℤ))) τ
        = y τ - dySpacing 2 m0 * ((N + 1 : ℕ) : ℝ) := by
      simp [site, axisVec]
    rw [e] at h1
    linarith [(abs_le.mp h1).1]

#print axioms exists_cell_margin

/-- **The cell set holds non-trivial energy-density readings.** For every base datum `i ∈ I` and every
margin `r`, `cellSet` contains a single-cell margin monomial on the base `i` (one factor, field
`(base i).1`), besides `∅` (`exists_cell_margin`).

DERIVED: `1` the number of factors; `2` the rank. -/
theorem cellSet_nontrivial {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (I : Set (Fin nb)) {i : Fin nb} (hi : i ∈ I) :
    ∃ P ∈ cellSet base m0 τ r I, P.1.1 = 1 ∧ ∃ c : Cell nb, c.1 = i ∧ P.1 = cellMono base m0 c := by
  obtain ⟨c, hci, hc1, d, hd, hrd, hpos⟩ := exists_cell_margin base m0 τ r i
  exact ⟨⟨cellMono base m0 c, d, hd, hrd, hpos⟩, Or.inr ⟨c, hci ▸ hi, hc1, rfl⟩, rfl, c, hci, rfl⟩

#print axioms cellSet_nontrivial

/-- The empty margin monomial is in the cell set.

DERIVED: no numeral. -/
theorem emptyMargin_mem_cellSet {nb : ℕ} (base : Fin nb → SField 2) (m0 : ℕ) (τ : Fin 4) (r : ℝ)
    (I : Set (Fin nb)) : emptyMargin 2 τ r ∈ cellSet base m0 τ r I :=
  Or.inl rfl

#print axioms emptyMargin_mem_cellSet

end NonVacuity

end MassGap.ObserverEnergyCellM
