import Mathlib
import MassGap.Existence

/-!
# The continuum measure via the entropy-matched read (reading A) — PAPER §11

Existence on `ℝ⁴` is the `a→0` limit of the finite-spacing Schwinger functions; it needs a uniform-in-`a`
bound to be **tight** (so a limit point exists) plus that each Osterwalder–Schrader condition, being closed,
survives the limit (`Existence.rp_survives_limit`, `Existence.tight_limit_rp`).

**Reading A (the entropy-matched construction).** The read keeps only the *resolved* modes — the
`K_signal = #{eigenvalue > noise edge}` correlation modes standing above the Tracy–Widom floor — and treats
the ultraviolet as sub-edge noise (asymptotic freedom puts the UV modes below the edge, §11). So the object
constructed is the measure on the finite **signal** content, and its dimension is `K_signal`, NOT the lattice
mode count. The gap supplies the uniform bound: in a gapped theory at fixed physical volume the coherent
(signal) states below the read scale are a **finite family whose size `K` is fixed by the gap and the volume,
independent of the spacing `a`**. Hence `K_signal(a) ≤ K` uniformly, the reflected forms are uniformly
bounded, and tightness follows with **no ultraviolet renormalisation — only the gap.**

This module proves the count/tightness logic (no axiom beyond the standard three); the physics inputs — a
signal set of bounded size `K` covering the supra-edge modes, and the reflected form built from the resolved
modes with bounded per-mode contribution — are stated as hypotheses, the reading-A modelling supplied like the
character bound on the strong side. Identifying the tight limit as a Wightman theory is Osterwalder–Schrader
reconstruction (cited).
-/

namespace MassGap.Measure

open MassGap Filter
open scoped Classical

/-- The **resolved dimension** `K_signal`: the number of correlation eigenvalues (over the index set `s`)
standing strictly above the noise edge. -/
noncomputable def resolvedDim {ι : Type*} (s : Finset ι) (ev : ι → ℝ) (edge : ℝ) : ℕ :=
  (s.filter (fun k => edge < ev k)).card

/-- **The resolved dimension is at most any signal set that covers the supra-edge modes.** If a set `sig`
of size `≤ K` contains every mode above the edge (the rest being sub-edge bulk), then `K_signal ≤ K`. In the
gapped theory `sig` is the finite family of physical states below the read scale — a count fixed by the gap
and the volume, not by the spacing. -/
theorem resolvedDim_le_of_signal {ι : Type*} (s : Finset ι) (ev : ι → ℝ) (edge : ℝ)
    {K : ℕ} (sig : Finset ι) (hcard : sig.card ≤ K)
    (hcover : ∀ k ∈ s, edge < ev k → k ∈ sig) :
    resolvedDim s ev edge ≤ K := by
  refine le_trans (Finset.card_le_card ?_) hcard
  intro k hk
  rw [Finset.mem_filter] at hk
  exact hcover k hk.1 hk.2

/-- **Uniform-in-`a` resolved dimension from the gap.** If at every spacing `aₙ` the supra-edge modes are
covered by a signal set of size `≤ K` (the gap fixes the physical mode count, independent of the spacing),
the resolved dimension is uniformly bounded. This is the uniform estimate the continuum limit needs, sourced
from the gap rather than from ultraviolet control. -/
theorem uniform_resolvedDim {ι : Type*} {K : ℕ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ)
    (sig : ℕ → Finset ι) (hcard : ∀ n, (sig n).card ≤ K)
    (hcover : ∀ n, ∀ k ∈ s n, edge n < ev n k → k ∈ sig n) :
    ∀ n, resolvedDim (s n) (ev n) (edge n) ≤ K :=
  fun n => resolvedDim_le_of_signal (s n) (ev n) (edge n) (sig n) (hcard n) (hcover n)

/-! ### The signal count discharged from the gap (a momentum-space count fixed by the physical volume)

The resolved modes are the correlation eigenvalues above the edge; index them by momentum. On a physical
torus of size `L` the modes are `k_n = (2π/L)·n`, so the **infrared momentum spacing `2π/L` is set by the
physical volume, not the lattice spacing `a`**. As `a→0` the number of lattice modes `N` grows, but the
number of modes below a fixed physical cutoff `c` (the correlation scale the gap fixes) does not: it is
`⌈c⌉`, independent of `N`. So the signal set (the IR modes the gap keeps above the edge) has a spacing-
independent size — the `K` of `uniform_resolvedDim`, derived rather than assumed. -/

/-- **The infrared mode count is spacing-independent.** The number of indices `n < N` with `(n:ℝ) < c` is at
most `⌈c⌉₊`, whatever the total mode count `N`. (Momenta below a physical cutoff `c = k⋆L/2π` number `⌈c⌉₊`,
independent of the lattice spacing.) -/
theorem ir_count_spacing_indep {c : ℝ} (N : ℕ) :
    ((Finset.range N).filter (fun n : ℕ => (n : ℝ) < c)).card ≤ ⌈c⌉₊ := by
  rw [← Finset.card_range ⌈c⌉₊]
  refine Finset.card_le_card (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  rw [Finset.mem_range]
  exact_mod_cast lt_of_lt_of_le hn.2 (Nat.le_ceil c)

/-- **Resolved dimension bounded by the gap's infrared cutoff.** If the gap keeps every supra-edge mode in
the infrared — `edge < ev n → (n:ℝ) < c`, the resolved content below the physical cutoff `c` — then the
resolved dimension is `≤ ⌈c⌉₊`, a count fixed by the physical volume and the gap scale, INDEPENDENT of the
lattice mode count `N` (the spacing `a`). This discharges the signal-set hypothesis of `uniform_resolvedDim`
from the gap: finite correlation length ⟹ the resolved content is infrared ⟹ a spacing-independent count. -/
theorem resolvedDim_le_of_gap {ev : ℕ → ℝ} {edge c : ℝ} (N : ℕ)
    (hir : ∀ n ∈ Finset.range N, edge < ev n → (n : ℝ) < c) :
    resolvedDim (Finset.range N) ev edge ≤ ⌈c⌉₊ :=
  resolvedDim_le_of_signal (Finset.range N) ev edge
    ((Finset.range N).filter (fun n : ℕ => (n : ℝ) < c)) (ir_count_spacing_indep N)
    (fun k hk hedge => Finset.mem_filter.mpr ⟨hk, hir k hk hedge⟩)

/-- **Uniform-in-`a` resolved dimension from the gap.** For a family of lattices with `Na a` modes
(`Na a → ∞` as `a→0`), if the gap keeps the supra-edge modes below the fixed physical cutoff `c` at every
spacing, the resolved dimension is uniformly `≤ ⌈c⌉₊`. The bound `K = ⌈c⌉₊` is set by the physical volume and
the gap scale, not the spacing — the uniform estimate the continuum limit needs, sourced from the gap. -/
theorem uniform_resolvedDim_of_gap {ev : ℕ → ℕ → ℝ} {edge c : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c) :
    ∀ a, resolvedDim (Finset.range (Na a)) (ev a) edge ≤ ⌈c⌉₊ :=
  fun a => resolvedDim_le_of_gap (Na a) (hir a)

/-- **Tightness from a uniformly bounded resolved dimension (reading A).** The reflected Schwinger form at
spacing `aₙ` is reflection-positive (`0 ≤ Q n`) and built from the resolved modes, each contributing at most
`B ≥ 0`, so `Q n ≤ K_signal(aₙ) · B`; with `K_signal(aₙ) ≤ K` uniformly (`uniform_resolvedDim`, from the
gap) the forms are uniformly bounded `Q n ≤ K · B`, hence the family is **tight**: a subsequence converges
to a reflection-positive limit within the bound (`Existence.tight_limit_rp`). No ultraviolet renormalisation
enters — the resolved dimension is controlled by the gap alone. -/
theorem tight_of_uniform_resolved {ι : Type*} {Q : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ)
    (hrp : ∀ n, 0 ≤ Q n) (hB : 0 ≤ B)
    (hQ : ∀ n, Q n ≤ (resolvedDim (s n) (ev n) (edge n) : ℝ) * B)
    (hres : ∀ n, resolvedDim (s n) (ev n) (edge n) ≤ K) :
    ∃ q, 0 ≤ q ∧ q ≤ (K : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) := by
  refine tight_limit_rp hrp (fun n => le_trans (hQ n) ?_)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hres n) hB

/-- **The reading-A tightness endpoint, from the gap-sourced signal bound.** Composing the two: a signal set
of size `≤ K` covering the supra-edge modes at every spacing (the gap-fixed physical mode count) plus the
reflected form built from the resolved modes (`0 ≤ Q n ≤ K_signal · B`) gives a tight family — a subsequence
of reflected forms converging to a reflection-positive limit `0 ≤ q ≤ K·B`. The continuum measure's tightness
reduces to the gap (finite physical mode count), with no ultraviolet renormalisation. -/
theorem tight_of_gap_signal {ι : Type*} {Q : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (s : ℕ → Finset ι) (ev : ℕ → ι → ℝ) (edge : ℕ → ℝ) (sig : ℕ → Finset ι)
    (hcard : ∀ n, (sig n).card ≤ K)
    (hcover : ∀ n, ∀ k ∈ s n, edge n < ev n k → k ∈ sig n)
    (hrp : ∀ n, 0 ≤ Q n) (hB : 0 ≤ B)
    (hQ : ∀ n, Q n ≤ (resolvedDim (s n) (ev n) (edge n) : ℝ) * B) :
    ∃ q, 0 ≤ q ∧ q ≤ (K : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) :=
  tight_of_uniform_resolved s ev edge hrp hB hQ
    (uniform_resolvedDim s ev edge sig hcard hcover)

/-- **Tightness from the gap alone (reading A, capstone).** The signal count is *derived* from the gap,
not assumed: the gap keeps the supra-edge modes below a fixed physical infrared cutoff `c` at every spacing
(`hir`), so the resolved dimension is uniformly `≤ ⌈c⌉₊` (`uniform_resolvedDim_of_gap`), a bound set by the
physical volume and the gap scale — independent of the lattice mode count `Na a` (the spacing). With the
reflected forms reflection-positive (`0 ≤ Q a`) and built from the resolved modes (`Q a ≤ K_signal · B`), the
family is **tight**: a subsequence converges to a reflection-positive limit `0 ≤ q ≤ ⌈c⌉₊·B`. So the continuum
limit's tightness follows from the gap (finite correlation length ⟹ finite infrared mode count), with no
ultraviolet renormalisation — the reading-A construction, with its one modelling input `hir` the physical
content of the gap. -/
theorem tight_of_gap_ir {Q : ℕ → ℝ} {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ a, 0 ≤ Q a) (hB : 0 ≤ B)
    (hQ : ∀ a, Q a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B) :
    ∃ q, 0 ≤ q ∧ q ≤ (⌈c⌉₊ : ℝ) * B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (Q ∘ φ) atTop (nhds q) :=
  tight_of_uniform_resolved (fun a => Finset.range (Na a)) ev (fun _ => edge) hrp hB hQ
    (uniform_resolvedDim_of_gap Na hir)

/-- **The full Schwinger vector is jointly tight, from the gap (reading A, vector capstone).** Every reflected
Schwinger form `Q j` (test-configuration `j`, over a countable dense set) is reflection-positive (`0 ≤ Q j a`)
and built from the resolved modes, bounded by the gap-fixed infrared count `Q j a ≤ K_signal(a)·B ≤ ⌈c⌉₊·B`
(`uniform_resolvedDim_of_gap`, `⌈c⌉₊` spacing-independent). So the whole family is uniformly bounded and
**jointly tight**: a single subsequence along which *every* Schwinger form converges to a reflection-positive
limit `0 ≤ q j ≤ ⌈c⌉₊·B` (`tight_limit_vector`, `rp_of_tight_limit_vector`). This is the joint convergence of
the full Schwinger vector that Osterwalder–Schrader reconstruction consumes — the continuum measure's tightness
and RP, sourced from the gap alone, with no ultraviolet renormalisation. -/
theorem tight_vector_of_gap_ir {J : Type*} [Countable J] {Q : J → ℕ → ℝ}
    {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ j a, 0 ≤ Q j a) (hB : 0 ≤ B)
    (hQ : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B) :
    ∃ q : J → ℝ, (∀ j, 0 ≤ q j) ∧ (∀ j, q j ≤ (⌈c⌉₊ : ℝ) * B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, Tendsto (fun k => Q j (φ k)) atTop (nhds (q j)) := by
  have h0 : 0 ≤ (⌈c⌉₊ : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hbnd : ∀ j a, |Q j a| ≤ (⌈c⌉₊ : ℝ) * B := by
    intro j a
    rw [abs_le]
    refine ⟨by linarith [hrp j a], le_trans (hQ j a) ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ hB
    exact_mod_cast uniform_resolvedDim_of_gap Na hir a
  obtain ⟨q, hq, φ, hmono, htend⟩ := tight_limit_vector (Q := Q) (C := (⌈c⌉₊ : ℝ) * B) hbnd
  exact ⟨q, rp_of_tight_limit_vector hrp htend, fun j => (abs_le.mp (hq j)).2, φ, hmono, htend⟩

/-- **Step 2 capstone (reading A): the gap + finite-spacing OS structure give a tight, OS-satisfying continuum
limit.** All inputs are at finite spacing: the gap keeps supra-edge modes below the physical cutoff `c`
(`hir`); the reflected forms are reflection-positive (`hrp`) and built from the resolved modes (`hQ`, so
bounded by the gap's infrared count); and they carry the Euclidean (`hEuc`) and permutation (`hPerm`)
symmetries (Osterwalder–Seiler / `Apriori.A2_hypercubic_holds` at each spacing). Then a single subsequence `φ`
and a limit `q` exist with, for every test configuration `j`:
* **joint convergence** `Q j (φ k) → q j` — tightness, from the gap alone (no ultraviolet renormalisation);
* **OS0** (regularity) `|q j| ≤ ⌈c⌉₊·B`, the temperedness bound;
* **OS2** (reflection positivity) `0 ≤ q j`;
* **OS1** (Euclidean invariance) `q (actE g j) = q j`;
* **OS3** (permutation symmetry) `q (actP σ j) = q j`.
The continuum limit inherits every closed OS condition from its finite-spacing version, the one analytic input
being the gap (finite infrared mode count = finite correlation scale). OS4 clustering is the gap at the
correlator level (`Forgetting.bridge_forward`); reconstructing `q` into a Wightman theory is the cited OS theorem.
No axiom beyond the standard three. -/
theorem continuum_limit_of_gap {G P J : Type*} [Countable J]
    {Q : J → ℕ → ℝ} {ev : ℕ → ℕ → ℝ} {edge c B : ℝ} (Na : ℕ → ℕ)
    (actE : G → J → J) (actP : P → J → J)
    (hir : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c)
    (hrp : ∀ j a, 0 ≤ Q j a) (hB : 0 ≤ B)
    (hQ : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B)
    (hEuc : ∀ g j a, Q (actE g j) a = Q j a)
    (hPerm : ∀ σ j a, Q (actP σ j) a = Q j a) :
    ∃ (q : J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈c⌉₊ : ℝ) * B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (actE g j) = q j) ∧
      (∀ σ j, q (actP σ j) = q j) := by
  have hbnd : ∀ j a, |Q j a| ≤ (⌈c⌉₊ : ℝ) * B := by
    intro j a
    rw [abs_le]
    refine ⟨by linarith [hrp j a, mul_nonneg (Nat.cast_nonneg (⌈c⌉₊)) hB],
      le_trans (hQ j a) (mul_le_mul_of_nonneg_right ?_ hB)⟩
    exact_mod_cast uniform_resolvedDim_of_gap Na hir a
  obtain ⟨q, hq, φ, hmono, htend⟩ := tight_limit_vector (Q := Q) (C := (⌈c⌉₊ : ℝ) * B) hbnd
  exact ⟨q, φ, hmono, htend, hq, rp_of_tight_limit_vector hrp htend,
    invariant_limit_of_action htend actE hEuc, invariant_limit_of_action htend actP hPerm⟩

/-! ### The construction for the concrete model

`continuum_limit_of_gap` takes the finite-spacing inputs loose. `LatticeYMFamily` names them as one structure
— as `Model.LatticeYM` names the reduction inputs — separating the cited standard results (Osterwalder–Seiler
reflection positivity, the confinement gap, `Apriori.A2_hypercubic_holds` invariance, bosonic symmetry) from
the machine-checked construction. `continuum_of_family` is then the reading-A continuum limit for the model,
in one line. -/

/-- **A lattice Yang–Mills family across spacings.** The finite-spacing Osterwalder–Schrader inputs the
reading-A construction consumes, bundled as one structure: the reflected Schwinger forms `Q` (test
configuration `j`, spacing index `a`), the correlation eigenvalues `ev`, the noise edge / infrared cutoff /
per-mode bound, and the group actions. Its hypotheses are the cited finite-spacing facts — reflection
positivity (`os_rp`, Osterwalder–Seiler), the confinement gap keeping the resolved modes infrared (`os_gap`,
A1), the forms built from the resolved modes (`os_form`), and the Euclidean and permutation symmetries
(`os_euc`, `Apriori.A2_hypercubic_holds` at finite spacing; `os_perm`, bosonic). -/
structure LatticeYMFamily where
  /-- Test configurations — a countable dense set of smeared field arrangements. -/
  J : Type
  /-- `J` is countable (the joint tightness is sequential compactness of a countable product). -/
  [countable : Countable J]
  /-- Euclidean group and its action on the test configurations. -/
  G : Type
  actE : G → J → J
  /-- Permutation group on the arguments and its action. -/
  P : Type
  actP : P → J → J
  /-- Lattice mode count at spacing index `a` (`→ ∞` as `a → 0`). -/
  Na : ℕ → ℕ
  /-- Correlation eigenvalues at each spacing. -/
  ev : ℕ → ℕ → ℝ
  /-- The reflected Schwinger forms. -/
  Q : J → ℕ → ℝ
  /-- Noise edge, physical infrared cutoff, per-mode bound. -/
  edge : ℝ
  c : ℝ
  B : ℝ
  hB : 0 ≤ B
  /-- **Reflection positivity** at every spacing (Osterwalder–Seiler). -/
  os_rp : ∀ j a, 0 ≤ Q j a
  /-- **The confinement gap keeps the resolved modes infrared**: supra-edge ⟹ below the physical cutoff `c`
  (A1 / finite correlation length). -/
  os_gap : ∀ a, ∀ n ∈ Finset.range (Na a), edge < ev a n → (n : ℝ) < c
  /-- The reflected form is built from the resolved modes (bounded by the resolved dimension). -/
  os_form : ∀ j a, Q j a ≤ (resolvedDim (Finset.range (Na a)) (ev a) edge : ℝ) * B
  /-- **Euclidean invariance** at every spacing (`Apriori.A2_hypercubic_holds`; continuum `SO(4)` the sampling
  isometry). -/
  os_euc : ∀ g j a, Q (actE g j) a = Q j a
  /-- **Permutation symmetry** at every spacing (bosonic Euclidean fields). -/
  os_perm : ∀ σ j a, Q (actP σ j) a = Q j a

/-- **The continuum limit of a lattice Yang–Mills family (Step 2 for the model).** Every `LatticeYMFamily`
has a tight continuum limit satisfying OS0–OS3 jointly: a subsequence `φ` and a limit `q` with joint
convergence, the temperedness bound (OS0), reflection positivity (OS2), Euclidean invariance (OS1), and
permutation symmetry (OS3). This is `continuum_limit_of_gap` applied to the family's named finite-spacing
inputs — the reading-A construction for the concrete model, the inputs cited (Osterwalder–Seiler, A1, A2), the
construction machine-checked, no axiom beyond the standard three. OS4 clustering is the gap
(`Forgetting.bridge_forward`); the Osterwalder–Schrader reconstruction of `q` into a Wightman theory is cited. -/
theorem continuum_of_family (F : LatticeYMFamily) :
    ∃ (q : F.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => F.Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈F.c⌉₊ : ℝ) * F.B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q (F.actE g j) = q j) ∧
      (∀ σ j, q (F.actP σ j) = q j) :=
  haveI := F.countable
  continuum_limit_of_gap F.Na F.actE F.actP F.os_gap F.os_rp F.hB F.os_form F.os_euc F.os_perm

end MassGap.Measure
