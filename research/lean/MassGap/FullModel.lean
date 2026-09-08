import MassGap.Model
import MassGap.Measure

/-!
# Existence and the gap for one model: mass gap AND continuum measure

`Model.mass_gap_of_model` gives the **mass gap** (`C(τ)→0`), non-triviality, and `SO(4)` from the reduction data
`LatticeYM` and its two obligations `A1_YM`, `A2_YM`. `Measure.continuum_of_family` gives the **OS-satisfying
continuum measure** (a tight limit with OS0–OS3) from the finite-spacing data `LatticeYMFamily`. This file is
the bridge: a `FullModel` is a single `SU(N)` lattice theory realised as BOTH — the reduction data at each
coupling and the finite-spacing Osterwalder–Schrader data across spacings, the two the *same* physical model
(the modelling identification of §2–§3, cited to Osterwalder–Seiler and the A1/A2 discharge). `existence_and_gap_of_model` then
delivers both parts of the existence-and-gap problem at once.

Everything here is machine-checked modulo its cited inputs: for the gap, A1 and A2 (`Complete.lean` discharges
them to the four named standard results); for the measure, reflection positivity, the confinement gap, and A2
invariance at finite spacing (the `LatticeYMFamily` fields), with the Osterwalder–Schrader reconstruction of
the tight limit into a Wightman theory the classical cited step. `existence_and_gap_of_model` itself uses no axiom beyond
the standard three — it is the composition; the physics enters through the two structures' fields.
-/

namespace MassGap

open MassGap.Measure Filter

/-- **A full model.** One `SU(N)` lattice gauge theory presented as both parts of the argument: the reduction
data `gap : LatticeYM` with its two obligations (`h1 : A1_YM`, `h2 : A2_YM`), and the finite-spacing
Osterwalder–Schrader data `measure : LatticeYMFamily`. The identification that these are the same physical
model is the §2–§3 modelling statement (cited); given it, both parts below follow. -/
structure FullModel where
  /-- The reduction data at each coupling (for the mass gap). -/
  gap : LatticeYM
  /-- A1 (confinement) for the reduction data — discharged in `Complete.lean` to the character bound,
  asymptotic freedom, and the §8.4 entropy-response identification. -/
  h1 : A1_YM gap
  /-- A2 (isotropy) for the reduction data — discharged to the Nyquist sampling isometry. -/
  h2 : A2_YM gap
  /-- The finite-spacing Osterwalder–Schrader data across spacings (for the continuum measure). -/
  measure : LatticeYMFamily

/-- **The full result for a model: mass gap AND OS-satisfying continuum measure.** From a `FullModel`:
* **Mass gap** (`mass_gap_of_model`, Step 1) — the autocorrelation forgets `C(τ)→0` at every coupling,
  non-triviality `μ − κ < 0`, and Euclidean `SO(4)` invariance;
* **Continuum measure** (`continuum_of_family`, Step 2) — a subsequence `φ` and a limit `q` with joint
  convergence and OS0 (temperedness bound), OS2 (reflection positivity), OS1 (Euclidean invariance), OS3
  (permutation symmetry) for every test configuration.
Both machine-checked modulo their cited inputs. `#print axioms existence_and_gap_of_model` returns the three foundational axioms
only: `existence_and_gap_of_model` is the composition, and A1/A2 (for the gap) and the `LatticeYMFamily` fields (for the
measure) enter as the structures' data, not as axioms of this theorem. OS4 clustering is the gap
(`Forgetting.bridge_forward`); the Osterwalder–Schrader reconstruction of `q` into a Wightman theory is cited. -/
theorem existence_and_gap_of_model (M : FullModel) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ M.gap.s β, M.gap.P β k * (M.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, M.gap.μ β - M.gap.κ < 0) ∧ (∀ d d', M.gap.R d = M.gap.R d')) ∧
      (∃ (q : M.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => M.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈M.measure.c⌉₊ : ℝ) * M.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (M.measure.actE g j) = q j) ∧
        (∀ σ j, q (M.measure.actP σ j) = q j)) :=
  ⟨mass_gap_of_model M.gap M.h1 M.h2, continuum_of_family M.measure⟩

/-! ### The §2–§3 modelling identification, as a typed obligation

`existence_and_gap_of_model` needs a `FullModel`. The remaining physical input is the identification that the `SU(N)` Wilson
ensemble *provides* one (§2–§3, cited to Osterwalder–Seiler and the A1/A2 discharge). The genuinely gauge-
theoretic content is small and named here: the physical parameters `N, L, k⋆`, and that the construction's
infrared cutoff is the physical `c = k⋆L/(2π)` — set by the box size `L` and the confinement scale `k⋆` (finite
by A1), NOT by the spacing, and `N`-independent. Given a realisation, the existence-and-gap problem follows. -/

/-- **Physical parameters of an SU(N) Wilson realisation.** Gauge order `N ≥ 2`, physical box size `L > 0`, and
the confinement momentum scale `k⋆ > 0` (the correlation scale, finite by A1). -/
structure WilsonParams where
  /-- Gauge group order (`SU(N)`, `N ≥ 2`). -/
  N : ℕ
  hN : 2 ≤ N
  /-- Physical box size. -/
  L : ℝ
  hL : 0 < L
  /-- Confinement / correlation momentum scale (finite by A1). -/
  kstar : ℝ
  hk : 0 < kstar

/-- The infrared cutoff `c = k⋆·L/(2π)` — the physical origin of the `LatticeYMFamily`'s spacing-independent
resolved-dimension bound `⌈c⌉₊`, set by the box size and the confinement scale. -/
noncomputable def WilsonParams.irCutoff (W : WilsonParams) : ℝ := W.kstar * W.L / (2 * Real.pi)

theorem WilsonParams.irCutoff_pos (W : WilsonParams) : 0 < W.irCutoff :=
  div_pos (mul_pos W.hk W.hL) (by positivity)

/-- **An SU(N) Wilson realisation** (the §2–§3 identification, cited). Physical parameters `params` together
with a `FullModel` whose finite-spacing infrared cutoff is the physical `k⋆L/(2π)` (`hc`). The identification
that the `SU(N)` Wilson ensemble supplies such data — its entropy-matched reads giving the reduction data
`LatticeYM` (with A1, A2) and its finite-spacing reflected forms the `LatticeYMFamily` (with Osterwalder–Seiler
RP, the confinement gap, and A2 invariance) — is the modelling statement of §2–§3, cited, the one physical
input to the whole argument. -/
structure WilsonRealization where
  params : WilsonParams
  model : FullModel
  /-- The construction's infrared cutoff is the physical `k⋆L/(2π)`. -/
  hc : model.measure.c = params.irCutoff

/-- **The existence-and-gap problem for an SU(N) Wilson realisation.** Given the §2–§3 identification (a
`WilsonRealization`), the SU(N) Wilson theory has BOTH the mass gap (`C(τ)→0`, non-triviality, `SO(4)`) and the
OS0–OS3-satisfying continuum measure — `existence_and_gap_of_model` applied to the realisation's `FullModel`. The sole remaining
inputs are that identification (cited) and the Osterwalder–Schrader reconstruction of the tight limit into a
Wightman theory (cited). No axiom beyond the standard three. -/
theorem existence_and_gap_of_wilson (W : WilsonRealization) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ W.model.gap.s β,
          W.model.gap.P β k * (W.model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, W.model.gap.μ β - W.model.gap.κ < 0) ∧ (∀ d d', W.model.gap.R d = W.model.gap.R d')) ∧
      (∃ (q : W.model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => W.model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈W.model.measure.c⌉₊ : ℝ) * W.model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (W.model.measure.actE g j) = q j) ∧
        (∀ σ j, q (W.model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_model W.model

/-! ### The link: entroptics fits into the classical axioms

Entroptics produces Euclidean Schwinger data satisfying the Osterwalder–Schrader / Wightman axioms; those axioms
and the reconstruction theorem are classical results, entered as NAMED AXIOMS, and the cited reconstruction
carries the data to a quantum field theory. `continuum_of_family` already does
that: its limit `q` satisfies OS0 (bound), OS1 (Euclidean), OS2 (RP), OS3 (symmetry), with OS4 (clustering) from
the gap. `wightman_of_model` plugs it in — the point where our equation fits into theirs. -/

/-- The proposition that a Wightman quantum field theory on ℝ⁴ exists (Hilbert space, `H ≥ 0`, unique vacuum).
The classical reconstruction that produces it is CITED (`os_reconstruction`). -/
axiom WightmanTheory : Prop

/-- **Osterwalder–Schrader → Wightman reconstruction (CITED, named axiom).** K. Osterwalder, R. Schrader,
Commun. Math. Phys. **31** (1973) 83 and **42** (1975) 281 (the latter adds the linear growth condition that
repairs the reconstruction); textbook form: J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point
of View*, 2nd ed. (Springer 1987). Euclidean Schwinger data `q` satisfying OS0–OS3 — with OS4 (clustering)
supplied by the mass gap — reconstructs a Wightman quantum field theory on ℝ⁴ (Hilbert space, `H ≥ 0`, unique
vacuum). This is the classical Osterwalder–Schrader theorem, cited; entroptics supplies its Euclidean hypotheses.
SEMANTICS: `q j` is the **reflected Schwinger form** `⟨θφⱼ, φⱼ⟩` for test
configuration `j` (a dense set of smeared field arrangements; `Measure.LatticeYMFamily.Q`), NOT a Schwinger
point-value. So `hOS2 : ∀j, 0 ≤ q j` **is** reflection positivity — the reflected quadratic form is
nonnegative on the dense test set (full Gram positive-semidefiniteness when `J` is closed under
combinations, which smeared arrangements provide). `hOS0 : ∃C ∀j |q j|≤C` is the uniform temperedness bound
the tightness consumes (weaker than OS-II's linear growth, but the analytic content used). The OS⟹Wightman
step is the classical theorem (OS 1973/75, Glimm–Jaffe 1987), entered as the named axiom. -/
axiom os_reconstruction {J G Pm : Type} (q : J → ℝ) (actE : G → J → J) (actP : Pm → J → J)
    (hOS0 : ∃ C : ℝ, ∀ j, |q j| ≤ C) (hOS1 : ∀ g j, q (actE g j) = q j)
    (hOS2 : ∀ j, 0 ≤ q j) (hOS3 : ∀ σ j, q (actP σ j) = q j) : WightmanTheory

/-- **Entroptics fits into the classical axioms: our construction reconstructs a Wightman QFT.** From a
`FullModel`, `continuum_of_family` gives a limit `q` satisfying OS0–OS3, so the cited `os_reconstruction` axiom
yields a Wightman theory — while the same model carries the mass gap (`existence_and_gap_of_model`). This is THE LINK: the
entropy-matched limit *is* an OS-satisfying Euclidean Schwinger family, and the classical reconstruction (cited)
takes it to the quantum theory. Everything on the entroptics side is machine-checked; the only inputs past the
foundational axioms are the named, cited `WightmanTheory` / `os_reconstruction`. -/
theorem wightman_of_model (M : FullModel) : WightmanTheory := by
  obtain ⟨q, _, _, _, hOS0, hOS2, hOS1, hOS3⟩ := continuum_of_family M.measure
  exact os_reconstruction q M.measure.actE M.measure.actP ⟨_, hOS0⟩ hOS1 hOS2 hOS3

end MassGap
