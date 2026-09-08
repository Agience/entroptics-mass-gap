import Mathlib

/-!
# Reflection positivity survives the continuum limit (PAPER §11)

Existence on `ℝ⁴` needs the limit measure to be reflection-positive, not merely each finite-spacing
screen. Reflection positivity is the condition `⟨θφ, φ⟩ ≥ 0` for the time-reflection `θ`, a pointwise
inequality on the Schwinger functions and hence a CLOSED condition: nonnegativity is stable under
limits. So if the reflected form is nonnegative at every spacing (Osterwalder-Seiler, cited) and the
forms converge (the uniform gap gives tightness and convergence of the moments, §6), the limit form is
nonnegative: RP is inherited by the continuum measure.

This is the framework-agnostic analytic core, `0 ≤ Qₐ ∧ Qₐ → Q ⟹ 0 ≤ Q`. It uses NO transfer matrix:
RP at finite spacing is cited (Osterwalder-Seiler), and this closes the limit. Only the SIGN is
formalized here; that the `Qₐ` are the physical reflected forms and that they converge is the cited/§6
input.
-/

namespace MassGap

/-- **Reflection positivity survives the limit** (PAPER §11). The reflected form is nonnegative at every
finite spacing (`hnn`) and the forms converge to the continuum form (`hlim`); then the continuum form is
nonnegative. Nonnegativity is closed under limits, so RP is inherited by the limit measure. No transfer
matrix enters: RP at finite spacing is cited, this closes the limit. -/
theorem rp_survives_limit {Q : ℕ → ℝ} {q : ℝ}
    (hnn : ∀ n, 0 ≤ Q n) (hlim : Filter.Tendsto Q Filter.atTop (nhds q)) :
    0 ≤ q :=
  ge_of_tendsto' hlim hnn

/-!
## The tightness step of the continuum limit (PAPER §11)

Existence on `ℝ⁴` is the `a→0` limit of the finite-spacing Schwinger functions. It needs two things: a
**uniform-in-`a` bound** (so the family is tight and a limit point exists) and that each Osterwalder–Schrader
condition, being CLOSED, is inherited by that limit. `rp_survives_limit` handles the closedness of RP; the
bound is the piece the entropy-matched read supplies. Asymptotic freedom puts the ultraviolet modes below the
Tracy–Widom noise edge (§11), so the **resolved dimension `K_signal` stays bounded as `a→0`**: the reflected
form lives in a fixed interval `[0, C]` uniformly in the spacing. A bounded sequence in a compact interval has
a convergent subsequence (tightness), whose limit inherits RP and the bound. This is the first analytic step
of the construction; identifying the limit as a Wightman theory is Osterwalder–Schrader reconstruction (cited).
-/

/-- **Tightness ⟹ a convergent subsequence inheriting RP.** The reflected Schwinger forms `Q n` at spacing
`aₙ` are reflection-positive (`0 ≤ Q n`, Osterwalder–Seiler) and **uniformly bounded** (`Q n ≤ C`, the
uniform-in-`a` estimate: the entropy-matched noise-floor cut keeps the resolved dimension bounded as `a→0`,
the ultraviolet modes sitting below the edge). Then some subsequence converges to a limit `q` that is itself
reflection-positive and within the bound, `0 ≤ q ≤ C`. This is the tightness step of the continuum limit —
the uniform bound produces a limit point and RP (a closed condition) is inherited (`rp_survives_limit` on the
subsequence, here via compactness of `[0, C]`). The remaining OS conditions are inherited likewise; the
reconstruction of the limit into a QFT is cited. -/
theorem tight_limit_rp {Q : ℕ → ℝ} {C : ℝ}
    (hrp : ∀ n, 0 ≤ Q n) (hbdd : ∀ n, Q n ≤ C) :
    ∃ q, 0 ≤ q ∧ q ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (Q ∘ φ) Filter.atTop (nhds q) := by
  have hmem : ∀ n, Q n ∈ Set.Icc (0 : ℝ) C := fun n => ⟨hrp n, hbdd n⟩
  obtain ⟨q, hq, φ, hmono, htend⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨q, hq.1, hq.2, φ, hmono, htend⟩

/-- **Joint tightness of the full Schwinger-function vector.** A COUNTABLE family `Q : J → ℕ → ℝ` of
finite-spacing form values — one sequence per test-function configuration `j`, in the spacing `n` — each
uniformly bounded `|Q j n| ≤ C`, has a SINGLE subsequence `φ` along which EVERY component converges,
`Q j (φ k) → q j` with `|q j| ≤ C`. The countable product of the compact intervals `[-C, C]` is compact and,
being a countable product, first-countable, so the joint (diagonal) subsequence is one application of
sequential compactness. This lifts the scalar tightness (`tight_limit_rp`) to the whole vector of Schwinger
functions on a countable dense set of test configurations — the joint convergence Osterwalder–Schrader
reconstruction consumes; and reflection positivity is inherited on every nonnegative component
(`rp_survives_limit` applied to `Q j ∘ φ`, so `0 ≤ Q j n ⟹ 0 ≤ q j`). -/
theorem tight_limit_vector {J : Type*} [Countable J] {Q : J → ℕ → ℝ} {C : ℝ}
    (hbdd : ∀ j n, |Q j n| ≤ C) :
    ∃ q : J → ℝ, (∀ j, |q j| ≤ C) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)) := by
  have hmem : ∀ n, (fun j => Q j n) ∈ Set.pi Set.univ (fun _ : J => Set.Icc (-C) C) :=
    fun n j _ => abs_le.mp (hbdd j n)
  obtain ⟨q, hq, φ, hmono, htend⟩ :=
    (isCompact_univ_pi (fun _ : J => isCompact_Icc)).tendsto_subseq hmem
  exact ⟨q, fun j => abs_le.mpr (hq j (Set.mem_univ j)), φ, hmono,
    fun j => tendsto_pi_nhds.mp htend j⟩

/-- **Reflection positivity of the joint limit.** Along the common subsequence of `tight_limit_vector`, every
component that is reflection-positive at each spacing (`0 ≤ Q j n`) has a reflection-positive limit
(`0 ≤ q j`). So the full family of reflected Schwinger forms is nonnegative in the continuum limit. -/
theorem rp_of_tight_limit_vector {J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (hrp : ∀ j n, 0 ≤ Q j n)
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j))) :
    ∀ j, 0 ≤ q j :=
  fun j => rp_survives_limit (fun k => hrp j (φ k)) (htend j)

/-!
## Survival of the closed Osterwalder–Schrader conditions (OS0, OS1, OS3)

Every OS condition is a *closed* statement about the Schwinger functions, so it passes to the joint limit of
`tight_limit_vector`: OS2 (RP) is `rp_of_tight_limit_vector`; OS0 (the uniform bound) is the `|q j| ≤ C` in the
tightness conclusion; OS1 (Euclidean invariance) and OS3 (permutation symmetry) are EQUALITIES between forms,
handled uniformly below. Each is: a symmetry of the finite-spacing forms (a reindexing of the test
configurations leaving every form invariant) is inherited by the limit, by uniqueness of limits along the
common subsequence.
-/

/-- **A symmetry of the finite-spacing forms survives the joint limit.** If a reindexing `τ : J → J` leaves
every finite-spacing form invariant (`Q (τ j) n = Q j n`, the symmetry at each spacing), the joint limit
inherits it, `q (τ j) = q j` — uniqueness of limits along the common subsequence. The survival mechanism for
every closed *equality* condition of Osterwalder–Schrader: state the symmetry as a reindexing of the test
configurations, verify it at finite spacing, and it passes to the continuum. -/
theorem symmetry_survives_limit {J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (τ : J → J) (hinv : ∀ j n, Q (τ j) n = Q j n) :
    ∀ j, q (τ j) = q j := by
  intro j
  refine tendsto_nhds_unique (htend (τ j)) ?_
  have heq : (fun k => Q (τ j) (φ k)) = (fun k => Q j (φ k)) := funext fun k => hinv j (φ k)
  rw [heq]; exact htend j

/-- **A group symmetry survives the joint limit.** A group `G` acting on the test configurations that leaves
every finite-spacing form invariant passes to the continuum: `q (act g j) = q j` for all `g, j`. -/
theorem invariant_limit_of_action {G J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : G → J → J) (hinv : ∀ g j n, Q (act g j) n = Q j n) :
    ∀ g j, q (act g j) = q j :=
  fun g => symmetry_survives_limit htend (act g) (fun j => hinv g j)

/-- **OS1 (Euclidean invariance) survives the limit.** With the Euclidean group `E` acting on the test
configurations and the finite-spacing forms Euclidean-invariant (`hinv`), the joint limit is
Euclidean-invariant. At finite spacing the discrete hypercubic part holds by `Apriori.A2_hypercubic_holds` and
the continuous `SO(4)` by the sampling isometry (§8.6, A2); those supply `hinv`, and this passes it to the
continuum. An instance of `invariant_limit_of_action`. -/
theorem os1_euclidean_survives {E J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : E → J → J) (hinv : ∀ g j n, Q (act g j) n = Q j n) :
    ∀ g j, q (act g j) = q j :=
  invariant_limit_of_action htend act hinv

/-- **OS3 (symmetry) survives the limit.** With the symmetric group on the arguments acting on the test
configurations and the finite-spacing forms permutation-symmetric (bosonic Euclidean fields), the joint limit
is permutation-symmetric. An instance of `invariant_limit_of_action`. -/
theorem os3_symmetry_survives {Perm J : Type*} {Q : J → ℕ → ℝ} {q : J → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ j, Filter.Tendsto (fun k => Q j (φ k)) Filter.atTop (nhds (q j)))
    (act : Perm → J → J) (hinv : ∀ σ j n, Q (act σ j) n = Q j n) :
    ∀ σ j, q (act σ j) = q j :=
  invariant_limit_of_action htend act hinv

end MassGap
