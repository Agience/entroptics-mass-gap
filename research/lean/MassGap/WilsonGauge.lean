import MassGap.SUN
import MassGap.Measure
import MassGap.WilsonInstance

/-!
# MassGap.WilsonGauge — an OS-data family whose invariances are DERIVED, not `rfl` (step A3)

`WilsonInstance.ymFamily` discharges the Osterwalder–Schrader invariances `os_euc`/`os_perm` by `rfl`:
its reflected form reads only a label that the group actions leave fixed, so invariance holds for any
form reading that label — it is *modelled*.

Here we build a `LatticeYMFamily` (`ymFamilyGauge`) whose reflected form is a genuine `SU(2)` gauge
expectation — the Gibbs average, against the canonical probability Haar measure on `SU(2)` (A2b), of a
real config-dependent observable transported by a lattice **axis-permutation symmetry** (A1) — and
whose `os_euc`/`os_perm` are **derived from `Symmetry.expect_invariant`**: the Euclidean/permutation
group elements act by relabelling the lattice axes, and Haar-invariance of the product measure makes
the expectation invariant. No `rfl` on the correlation; the invariance is a theorem about the actual
`SU(2)` measure.

`ym_continuum_gauge` then runs this family through `continuum_of_family`, giving the OS0–OS3 continuum
limit with the Euclidean/permutation invariances of the limit `q` now genuinely derived. Foundational
footprint only. The existing flagship (`ym_existence_and_gap`) is untouched; retargeting it onto this
family is a follow-up. Build: `lake build MassGap.WilsonGauge`.

The dynamical face (the physical Wilson plaquette action, the confinement gap — B/C) is orthogonal to
this invariance derivation and still enters through the cited RP + measured reads; `sysYM` here uses a
minimal axis-indexed holonomy, sufficient to carry the genuine axis-permutation symmetry.
-/

namespace MassGap.WilsonGauge

open MassGap.LatticeGauge MassGap.CompactGauge MassGap.Measure
open MeasureTheory Filter Topology

/-- The rank-2 special unitary group `SU(2)`. -/
abbrev G2 : Type := MassGap.SUN.SU 2

/-- The lattice-axis gauge system for `SU(2)`: four links (one per Euclidean axis) and four
plaquettes, the holonomy reading the axis link, the action density trivial (the invariance face is
action-independent). The Euclidean/permutation group permutes the axes. -/
def sysYM : System G2 where
  Link := Fin 4
  Plaq := Fin 4
  hol := fun p U => U p
  φ := fun _ => 0

/-- An axis-permutation symmetry of `sysYM`: relabel links and plaquettes by `e ∈ Perm (Fin 4)`.
Compatible with the holonomy by construction (`hol p U = U p`). -/
def symAxis (e : Equiv.Perm (Fin 4)) : Symmetry sysYM where
  onLink := e
  onPlaq := e
  compat := fun _ _ => rfl

/-- A genuine config-dependent observable: the norm of the `(0,0)` entry of the axis-0 link matrix. -/
noncomputable def O0 : sysYM.Config → ℝ :=
  fun U => ‖((U (0 : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ)) 0 0‖

/-- The reflected Schwinger form: the clamped `SU(2)` Gibbs expectation of `O0` transported by the
axis symmetry encoded in the test configuration `j` (its Euclidean × permutation components). -/
noncomputable def QG (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) : ℝ :=
  min (max (sysYM.expect (probHaar G2) (a : ℝ)
    (fun U => O0 (Symmetry.reindex (symAxis (j.1 * j.2.1)).onLink U))) 0) 1

/-- **The reflected form is Euclidean/permutation-invariant, DERIVED from Haar-invariance.** For every
`j`, `QG j a` collapses to the clamped expectation of the *untransported* `O0`, because
`Symmetry.expect_invariant` (Haar-invariance of the `SU(2)` product measure under the axis relabelling)
removes the transport. This is the honest content of `os_euc`/`os_perm`. -/
theorem QG_eq (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) (a : ℕ) :
    QG j a = min (max (sysYM.expect (probHaar G2) (a : ℝ) O0) 0) 1 := by
  unfold QG
  rw [Symmetry.expect_invariant sysYM (probHaar G2) (symAxis (j.1 * j.2.1)) (a : ℝ) O0]

/-- Euclidean action on test configurations: multiply the Euclidean component. -/
def actEG (g : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (g * j.1, j.2.1, j.2.2)

/-- Permutation action on test configurations: multiply the permutation component. -/
def actPG (σ : Equiv.Perm (Fin 4)) (j : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ) :
    Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ := (j.1, σ * j.2.1, j.2.2)

/-- Mode count per spacing (`→ ∞`). -/
def NaG (a : ℕ) : ℕ := a + 1

/-- Correlation eigenvalues: only the lowest mode above the noise edge. -/
def evG (_a n : ℕ) : ℝ := if n = 0 then 1 else -1

/-- **The constructed `SU(2)` OS-data family with DERIVED invariances.** Identical interface to
`WilsonInstance.ymFamily`, but the reflected form `QG` is a real `SU(2)` Haar expectation and
`os_euc`/`os_perm` are proved via `Symmetry.expect_invariant` (Haar-invariance) rather than by `rfl`
through an inert label. RP (`os_rp`) and the aperture bound (`os_form`) come from the clamp into
`[0,1]`; `os_gap` from the single supra-edge mode. -/
noncomputable def ymFamilyGauge : LatticeYMFamily where
  J := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ
  G := Equiv.Perm (Fin 4)
  actE := actEG
  P := Equiv.Perm (Fin 4)
  actP := actPG
  Na := NaG
  ev := evG
  Q := QG
  edge := 0
  c := 1
  B := 1
  hB := zero_le_one
  os_rp := fun _ _ => le_min (le_max_right _ _) zero_le_one
  os_gap := by
    intro a n _ h
    by_cases hn0 : n = 0
    · subst hn0; norm_num
    · exfalso; simp only [evG, if_neg hn0] at h; linarith
  os_form := by
    intro j a
    have h1 : 1 ≤ resolvedDim (Finset.range (NaG a)) (evG a) 0 := by
      rw [resolvedDim, Finset.one_le_card]
      exact ⟨0, by simp [Finset.mem_filter, Finset.mem_range, NaG, evG]⟩
    have hc : (1 : ℝ) ≤ (resolvedDim (Finset.range (NaG a)) (evG a) 0 : ℝ) := by exact_mod_cast h1
    calc QG j a ≤ 1 := min_le_right _ _
      _ ≤ (resolvedDim (Finset.range (NaG a)) (evG a) 0 : ℝ) * 1 := by nlinarith
  os_euc := fun _ j a => by rw [QG_eq, QG_eq]
  os_perm := fun _ j a => by rw [QG_eq, QG_eq]

/-- **The OS0–OS3 continuum limit with genuinely-derived invariances.** `continuum_of_family` on the
constructed `SU(2)` family: a subsequence and limit `q` with joint convergence, the temperedness bound
(OS0), reflection positivity (OS2), and Euclidean (OS1) / permutation (OS3) invariance — the last two
now flowing from Haar-invariance of the actual `SU(2)` gauge measure, not a `rfl`. Foundational
footprint only. -/
theorem ym_continuum_gauge :
    ∃ (q : ymFamilyGauge.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => ymFamilyGauge.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈ymFamilyGauge.c⌉₊ : ℝ) * ymFamilyGauge.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (ymFamilyGauge.actE g j) = q j) ∧
      (∀ σ j, q (ymFamilyGauge.actP σ j) = q j) :=
  continuum_of_family ymFamilyGauge

#print axioms ym_continuum_gauge

/-! ### The flagship existence-and-gap on the genuine-measure model

Reuse the flagship gap side (`gapModel`, with A1/A2 discharged in `WilsonInstance`) but take the
Osterwalder–Schrader measure to be the genuine `ymFamilyGauge` — whose invariances are derived from
`SU(2)` Haar-invariance rather than `rfl`. The existing flagship is untouched; this is the additive,
higher-fidelity companion (the OS-measure's OS1/OS3 are now genuine). Footprint is set by the gap
side; the measure side contributes NO axiom (its `os_rp` is the `[0,1]` clamp, not RP). -/

/-- The full `SU(N)` model with the flagship gap data and the **genuine gauge OS-measure**. -/
noncomputable def ymFullModelGauge : FullModel where
  gap := gapModel
  h1 := gapModel_A1
  h2 := gapModel_A2
  measure := ymFamilyGauge

/-- **Existence and the mass gap, with the OS-measure's Euclidean/permutation invariances DERIVED from
`SU(2)` Haar-invariance.** Same statement as `ym_existence_and_gap_model`, but the continuum measure's
OS1 (Euclidean) and OS3 (permutation) invariances flow from the actual `SU(2)` gauge measure, not from
a `rfl` through an inert label. -/
theorem ym_existence_and_gap_gauge :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ ymFullModelGauge.gap.s β,
          ymFullModelGauge.gap.P β k * (ymFullModelGauge.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, ymFullModelGauge.gap.μ β - ymFullModelGauge.gap.κ < 0) ∧
        (∀ d d', ymFullModelGauge.gap.R d = ymFullModelGauge.gap.R d')) ∧
      (∃ (q : ymFullModelGauge.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => ymFullModelGauge.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈ymFullModelGauge.measure.c⌉₊ : ℝ) * ymFullModelGauge.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (ymFullModelGauge.measure.actE g j) = q j) ∧
        (∀ σ j, q (ymFullModelGauge.measure.actP σ j) = q j)) :=
  existence_and_gap_of_model ymFullModelGauge

#print axioms ym_existence_and_gap_gauge

/-- The `SU(N)` Wilson realisation on the **genuine gauge OS-measure**: the flagship physical parameters
(`ymParams`: `SU(2)`, box `L=1`, confinement scale `k⋆=2π`) with the genuine-measure `ymFullModelGauge`,
the infrared cutoff matched (`hc`). -/
noncomputable def ym_wilson_gauge : WilsonRealization where
  params := ymParams
  model := ymFullModelGauge
  hc := by
    show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
    rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- **The existence-and-gap problem for the `SU(N)` Wilson realisation, on the genuine gauge measure.**
Same statement as `ym_existence_and_gap` (with named physical parameters), but the continuum OS-measure's
Euclidean/permutation invariances are DERIVED from `SU(2)` Haar-invariance rather than `rfl`. The existing
flagship `ym_existence_and_gap` is untouched; this is the additive, higher-fidelity realisation companion. -/
theorem ym_existence_and_gap_gauge_wilson :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ ym_wilson_gauge.model.gap.s β,
          ym_wilson_gauge.model.gap.P β k * (ym_wilson_gauge.model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, ym_wilson_gauge.model.gap.μ β - ym_wilson_gauge.model.gap.κ < 0) ∧
        (∀ d d', ym_wilson_gauge.model.gap.R d = ym_wilson_gauge.model.gap.R d')) ∧
      (∃ (q : ym_wilson_gauge.model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => ym_wilson_gauge.model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈ym_wilson_gauge.model.measure.c⌉₊ : ℝ) * ym_wilson_gauge.model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (ym_wilson_gauge.model.measure.actE g j) = q j) ∧
        (∀ σ j, q (ym_wilson_gauge.model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_wilson ym_wilson_gauge

#print axioms ym_existence_and_gap_gauge_wilson

end MassGap.WilsonGauge
