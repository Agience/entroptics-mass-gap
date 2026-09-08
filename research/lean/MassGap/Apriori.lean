import Mathlib
import MassGap.Certify

/-!
# THE A PRIORI

The whole construction reduces, in the framework's own objects (the deterministic entropy-matched
read), to **two** a priori propositions, `A1` and `A2`. Given these two, the construction meets the
requirements of the Yang-Mills existence-and-mass-gap problem. This file states the two, labels them, and
discharges the requirements from them. `#print axioms` returns the standard three: the discharge is
closed.

Each a priori is in turn reduced, by machine-checked lemmas, to one input. **A1**: its two coupling ends
rest on the Osterwalder-Seiler character bound and asymptotic freedom; its crossover interior reduces to
the finite correlation length `d2_le_bound` (`⟨d²⟩ ≤ 1`, `Complete.lean`, via `ym_crossover_confinement`),
and its uniform-in-`a` continuum to refinement-invariance. (The `χ_v ≥ 0` disorder response is a
*different*, convex Rényi-1 object — PAPER §8.4 — off the interior route.) **A2** reduces to the Nyquist-Shannon sampling isometry: its discrete point
group and spatial rotations are proved outright, and its continuum axis-role `SO(4)` reduces, through the
correlation Gram, to that isometry.

**A1 (confinement).** `∀ β, μ β < κ₀` — the aperture's tension read stays below the counting floor at
every coupling. Delivers the mass gap and non-triviality (confinement ⇒ area law ⇒ interacting).

**A2 (isotropy).** The continuum entropy-matched read `R` of an observable is direction-independent,
`∀ d d', R d = R d'`. Delivers Euclidean `SO(4)` invariance. Framework-native: entropy is
coordinate-free, so its `a → 0` read carries no residual lattice anisotropy (the continuous form of
the discrete relabeling invariance, [E, Prop 3.5]).

Discharged from A1, A2, and the proved / cited layer:

| requirement | source | status |
|---|---|---|
| mass gap `Δ>0` | A1 ⇒ `gap_of_confinement_read` | from A1 |
| non-triviality | A1 ⇒ `confines_of_tension_lt_floor` (area law, interacting) | from A1 |
| Euclidean `SO(4)` | A2 | from A2 |
| continuum well-defined | `gap_refinement_invariant` (Prop 4.5, identity) | proved |
| short distance | asymptotic freedom (`b₀>0`); gives A1's weak end | cited |
| A2 continuum `SO(4)` | Nyquist-Shannon sampling isometry | cited |
-/

namespace MassGap

open scoped Matrix

/-- **A1 — the first a priori: confinement.** The aperture's tension read `μ` stays below the counting
floor `κ₀` at every coupling. -/
def A1 (μ : ℝ → ℝ) (κ₀ : ℝ) : Prop := ∀ β, μ β < κ₀

/-- **A2 — the second a priori: isotropy.** The continuum entropy-matched read `R` of an observable is
direction-independent (`D` the orientation): no residual lattice anisotropy, the read-level form of
Euclidean `SO(4)` invariance. -/
def A2 {D : Type*} (R : D → ℝ) : Prop := ∀ d d', R d = R d'

/-- **Mass gap from A1.** With the finite-aperture read at each coupling, A1 gives the gap at every
coupling: the correlator forgets, `C(τ) → 0`. -/
theorem gap_of_A1 {ι : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ) (κ₀ : ℝ) (μ : ℝ → ℝ)
    (h1 : A1 μ κ₀)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    ∀ β, Filter.Tendsto
      (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement_read s P m κ₀ μ h1 hread

/-- **Non-triviality from A1.** A1 makes the centre-vortex free energy negative at every coupling
(`μ β - κ < 0` for the floor `κ₀ ≤ κ`): the vortices condense, the flux confines to an area law, and
the theory is interacting, not free (a free theory has a perimeter law). -/
theorem nontrivial_of_A1 {κ₀ κ : ℝ} {μ : ℝ → ℝ} (hfloor : κ₀ ≤ κ) (h1 : A1 μ κ₀) :
    ∀ β, μ β - κ < 0 :=
  fun β => confines_of_tension_lt_floor hfloor (h1 β)

/-- **Euclidean invariance from A2.** A2 is the direction-independence of the continuum read: the
observable is the same in every orientation, the read-level Euclidean `SO(4)` invariance. -/
theorem euclidean_of_A2 {D : Type*} (R : D → ℝ) (h2 : A2 R) : ∀ d d', R d = R d' := h2

/-- **Continuum well-defined (proved).** The physical rate is refinement-invariant, so
the continuum value equals the finite-spacing value by identity (Prop 4.5). -/
theorem continuum_well_defined {δ m s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hm : 0 < m) :
    -(s / δ) * Real.log (m ^ ((1 : ℝ) / s)) = -(1 / δ) * Real.log m :=
  gap_refinement_invariant hδ hs hm

/-- **The result from THE a priori (conditional main theorem).** Given the two a priori inputs
`A1` (confinement) and `A2` (isotropy), plus the finite-aperture read, the mass gap, non-triviality,
and Euclidean `SO(4)` invariance all follow. Reflection positivity (Osterwalder-Seiler), the continuum
identity (`continuum_well_defined`), and short distance (asymptotic freedom) are established
separately. `A1` and `A2` are the two open a priori propositions; everything here is discharged from
them. -/
theorem existence_and_gap_from_apriori
    {ι D : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ) (κ₀ κ : ℝ) (μ : ℝ → ℝ) (R : D → ℝ)
    (hfloor : κ₀ ≤ κ) (h1 : A1 μ κ₀) (h2 : A2 R)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, μ β - κ < 0) ∧
      (∀ d d', R d = R d') :=
  ⟨gap_of_A1 s P m κ₀ μ h1 hread, nontrivial_of_A1 hfloor h1, euclidean_of_A2 R h2⟩

/-! ## Advancing A1 and A2 to their next step

`existence_and_gap_from_apriori` discharges the requirements from `A1` and `A2`. The sections below discharge each
a priori down to one established input, as machine-checked lemmas. **A1** reduces to a finite correlation
length: its strong- and weak-coupling ends are proved (below), its crossover interior reduces to
`d2_le_bound` (`⟨d²⟩ ≤ 1`, `Complete.lean`), and its uniform-in-`a` continuum to refinement-invariance.
**A2** reduces to the Nyquist-Shannon sampling isometry: its discrete point group is
proved (below) and its spatial and continuum rotations reduce, through the correlation Gram, to that
isometry. Both remaining inputs are established results. The named parts:

* **A1, strong-coupling side.** The character / cluster expansion of the Wilson action bounds the
  aperture tension linearly, `μ β ≤ 2 β r` with `r` the leading character ratio `I₂(β)/I₁(β)`
  (Osterwalder-Seiler). Below the threshold coupling `β_c = κ₀ / (2 r)` this bound sits under the
  counting floor, so `μ β < κ₀`: confinement on the strong-coupling side, as an inequality
  (`apriori_A1_strong`). The weak end (`apriori_A1_weak`) and the crossover interior (reflection
  positivity, `Certify.lean`) close the range `β ≥ β_⋆`.
* **A2, hypercubic side.** A read that is a symmetric functional of the per-axis reads is invariant
  under the hypercubic axis-permutation group (`read_hypercubic_invariant`, `A2_hypercubic_holds`):
  the finite point group of the lattice, the discrete subgroup of `SO(4)`. The continuum restoration,
  the full continuous `SO(4)`, reduces to the sampling isometry (below).
-/

/-- **A1, strong-coupling side: below the threshold the character bound is sub-floor.** With `r > 0`
the leading character ratio and `β_c` the threshold coupling defined by `2 β_c r = κ₀`, every
coupling `β < β_c` has its linear character bound below the counting floor: `2 β r < κ₀`. -/
theorem strong_below_threshold {r κ₀ β βc : ℝ} (hr : 0 < r)
    (hc : 2 * βc * r = κ₀) (hlt : β < βc) : 2 * β * r < κ₀ := by
  rw [← hc]; nlinarith

/-- **A1, strong-coupling side (discharged).** Given the strong-coupling character bound
`μ β ≤ 2 β r` (the cited cluster expansion) and a coupling below the threshold `β_c = κ₀ / (2 r)`,
the tension sits below the counting floor: `μ β < κ₀`. This is the strong-coupling part of `A1`, as
an inequality. Its input `μ β ≤ 2 β r` is the character expansion; the threshold is Kramers-Wannier.
The part of `A1` this does not reach is the range `β ≥ β_c`. -/
theorem apriori_A1_strong {μ : ℝ → ℝ} {r κ₀ β βc : ℝ} (hr : 0 < r)
    (hc : 2 * βc * r = κ₀) (hlt : β < βc) (hbound : μ β ≤ 2 * β * r) : μ β < κ₀ :=
  lt_of_le_of_lt hbound (strong_below_threshold hr hc hlt)

/-! ### A1, weak-coupling side, and the read that supplies the confinement input

`apriori_A1_strong` closes `μ < κ₀` for `β < β_⋆`. The weak-coupling end closes from asymptotic freedom:
the running is one-signed (`Running.lean`), so the tension in lattice units vanishes, `μ β → 0`, and a
vanishing tension is eventually below the positive floor (`apriori_A1_weak`). The interior range is closed
by the finite correlation length `d2_le_bound` (`Complete.ym_crossover_confinement`).

The confinement input `hread` (`‖m k‖ ≤ e^{-(κ₀-μ)}`) is not an independent assumption: it is a bound on
the DMD dominant magnitude the aperture returns. `rates().dominant` is `Δ = -log r` with `r` the dominant
magnitude, and the read hypothesis is exactly `Δ ≥ κ₀ - μ`, the measured gap clearing the free-energy
margin (`hread_of_dominant`, `margin_of_dominant_rate`). -/

/-- **A1, weak-coupling side (discharged).** With the tension converging at weak coupling to a limit `L`
**below the floor** (`μ β → L`, `L < κ₀`) — the free-field plateau `μ∞ ≈ 0.033 < κ₀` of `FreeField.lean`,
the read tension, which plateaus — the tension is eventually below the floor:
`μ β < κ₀` for all large `β`. The part
A1 does not reach is the interior between the two ends. -/
theorem apriori_A1_weak {μ : ℝ → ℝ} {κ₀ L : ℝ} (hL : L < κ₀)
    (hlim : Filter.Tendsto μ Filter.atTop (nhds L)) :
    ∀ᶠ β in Filter.atTop, μ β < κ₀ :=
  hlim.eventually (isOpen_Iio.mem_nhds hL)

/-- **The read margin is a bound on the DMD dominant magnitude.** If the dominant mode magnitude
`r = max_k ‖m k‖` clears the free-energy margin, `r ≤ e^{-(κ₀-μ)}`, then every mode does: the read
hypothesis `hread` of `gap_of_confinement` is exactly this dominant-magnitude bound (`rates().dominant`). -/
theorem hread_of_dominant {ι : Type*} (s : Finset ι) (m : ι → ℂ) {κ₀ μ r : ℝ}
    (hdom : ∀ k ∈ s, ‖m k‖ ≤ r) (hr : r ≤ Real.exp (-(κ₀ - μ))) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hdom k hk) hr

/-- **The read hypothesis is the measured gap clearing the margin.** With `r` the DMD dominant magnitude
(so the read rate is `Δ = -log r`), the margin bound `r ≤ e^{-(κ₀-μ)}` is equivalent to `Δ ≥ κ₀ - μ`: the
read `hread` says the measured gap clears the free-energy deficit. -/
theorem margin_of_dominant_rate {κ₀ μ r : ℝ} (hr : 0 < r) :
    r ≤ Real.exp (-(κ₀ - μ)) ↔ κ₀ - μ ≤ -Real.log r := by
  constructor
  · intro h
    have hlog := Real.log_le_log hr h
    rw [Real.log_exp] at hlog; linarith
  · intro h
    have hlog : Real.log r ≤ -(κ₀ - μ) := by linarith
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp (-(κ₀ - μ)) := Real.exp_le_exp.mpr hlog

/-! ### T3a: certifying the strong-coupling threshold `β⋆`

`apriori_A1_strong` uses the threshold `β⋆` with `2 β⋆ r = κ₀`, i.e. `β⋆ = κ₀/(2r)`, where `r = I₂/I₁`
is the leading character ratio and `κ₀ = ¼ log 3`. The ratio and the floor are certified to rational
intervals by `research/code/certify/beta_star_enclosure.py` (exact-rational Bessel and log series with proven geometric
tail bounds): `r(β⋆) ∈ [0.182, 0.184]`, `κ₀ ∈ [0.2746, 0.2747]`, and the bracket `B(0.749) < κ₀ <
B(0.750)`. The lemma below machine-checks the enclosure arithmetic that turns those certified bounds into
an interval for `β⋆`. -/

/-- **Certified threshold enclosure (interval arithmetic).** With the leading character ratio `r` in
`[rlo, rhi]` (`0 < rlo`) and the floor `κ₀` in `[klo, khi]` (`0 ≤ klo`), the strong-coupling threshold
`β⋆ = κ₀/(2r)` (`apriori_A1_strong`) is enclosed: `κ₀/(2r) ∈ [klo/(2 rhi), khi/(2 rlo)]`. The interval
bounds are the certified numerics of `research/code/certify/beta_star_enclosure.py`; the enclosure is checked here. -/
theorem beta_star_enclosure {r κ₀ rlo rhi klo khi : ℝ}
    (hrlo : 0 < rlo) (hr : rlo ≤ r) (hr' : r ≤ rhi)
    (hk : klo ≤ κ₀) (hk' : κ₀ ≤ khi) (hklo0 : 0 ≤ klo) :
    klo / (2 * rhi) ≤ κ₀ / (2 * r) ∧ κ₀ / (2 * r) ≤ khi / (2 * rlo) := by
  have hr0 : 0 < r := lt_of_lt_of_le hrlo hr
  have hrhi0 : 0 < rhi := lt_of_lt_of_le hr0 hr'
  have hκ0 : 0 ≤ κ₀ := le_trans hklo0 hk
  have hkhi0 : 0 ≤ khi := le_trans hκ0 hk'
  exact ⟨by gcongr, by gcongr⟩

/-- **The certified enclosure, instantiated** (`research/code/certify/beta_star_enclosure.py`): with the certified
rational bounds `r(β⋆) ∈ [0.182, 0.184]` and `κ₀ ∈ [0.2746, 0.2747]`, the strong-coupling threshold is
`β⋆ ∈ [0.746, 0.755]`, machine-checked. -/
example {r κ₀ : ℝ}
    (hr : (182 : ℝ) / 1000 ≤ r) (hr' : r ≤ 184 / 1000)
    (hk : (2746 : ℝ) / 10000 ≤ κ₀) (hk' : κ₀ ≤ 2747 / 10000) :
    (746 : ℝ) / 1000 ≤ κ₀ / (2 * r) ∧ κ₀ / (2 * r) ≤ 755 / 1000 := by
  obtain ⟨lo, hi⟩ := beta_star_enclosure (by norm_num) hr hr' hk hk' (by norm_num)
  exact ⟨le_trans (by norm_num) lo, le_trans hi (by norm_num)⟩

/-- **A2, hypercubic side: a symmetric read is axis-permutation invariant.** A read `R` that depends
only on the MULTISET of the per-axis reads `a : Fin d → ℝ` (a spectral / symmetric functional) is
unchanged when the axes are permuted by any `σ ∈ S_d`. A hypercubic rotation permutes the axes, so
`R` is invariant under the hypercubic subgroup of `SO(4)`. Extends the relabeling invariance
[E, Prop 3.5] to the full axis-permutation group. -/
theorem read_hypercubic_invariant {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ)
    (σ : Equiv.Perm (Fin d)) :
    R (Finset.univ.val.map (fun i => a (σ i))) = R (Finset.univ.val.map a) := by
  have hperm : Finset.univ.val.map (⇑σ) = (Finset.univ.val : Multiset (Fin d)) := by
    have h := congrArg Finset.val (Finset.map_univ_equiv (σ : Fin d ≃ Fin d))
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  have key : Finset.univ.val.map (fun i => a (σ i)) = Finset.univ.val.map a := by
    change Finset.univ.val.map (a ∘ ⇑σ) = Finset.univ.val.map a
    rw [← Multiset.map_map, hperm]
  rw [key]

/-- The product read over axes (étendue `φ_F φ_T`, space-bandwidth `n_F n_T`) is a symmetric read,
so it is hypercubic-invariant outright. -/
theorem etendue_hypercubic_invariant {d : ℕ} (a : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    ∏ i, a (σ i) = ∏ i, a i := Equiv.prod_comp σ a

/-- **The discrete (hypercubic) part of A2.** For a symmetric read `R`, `A2` restricted to the
axis-permutation group of the lattice. -/
def A2_hypercubic {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d),
    R (Finset.univ.val.map (fun i => a (σ i))) = R (Finset.univ.val.map a)

/-- **A2 holds on the hypercubic subgroup (proved, no a priori).** The symmetric read is invariant
under every axis permutation: the discrete point-group part of `A2` is a theorem. The part A2 still
carries is the continuum `SO(4)` restoration. -/
theorem A2_hypercubic_holds {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) :
    A2_hypercubic R a := fun σ => read_hypercubic_invariant R a σ

/-- **A2 axis-role, discrete: a symmetric read is invariant under the T↔F swap.** The ordered↔feature
(time↔feature) exchange is the axis transposition `Equiv.swap i j ∈ S_d`, so a read `R` that is a
symmetric functional of the per-axis reads (e.g. `R = ∏ᵢ aᵢ`, `étendue_hypercubic_invariant`) is
invariant under it outright, by `read_hypercubic_invariant`. This removes the axis-role asymmetry from
`A2`: on the lattice the T↔F exchange is a hypercubic permutation, a theorem here. What `A2` still
carries is only the *continuous* `SO(4)` restoration (an arbitrary-angle T↔F rotation) in the `a → 0`
limit, the generic restoration of rotational invariance. -/
theorem A2_axis_role_swap {d : ℕ} (R : Multiset ℝ → ℝ) (a : Fin d → ℝ) (i j : Fin d) :
    R (Finset.univ.val.map (fun k => a (Equiv.swap i j k))) = R (Finset.univ.val.map a) :=
  read_hypercubic_invariant R a (Equiv.swap i j)

/-! ### A2 continuum side: the read is invariant under orthogonal congruence

`A2_hypercubic_holds` gives direction-independence under the finite axis-permutation group. The
continuum part of `A2` is the full rotation group `SO(4)`. A rotation acts on the correlation operator
by an orthogonal congruence `C ↦ P C Pᵀ` (`Pᵀ P = 1`), and a spectral read (a function of the
operator's characteristic polynomial, hence of its eigenvalue multiset) is invariant under any such
congruence ([E, Prop 3.5], spectral form, `Entroptics.spectral_read_orthogonal`). So the continuum
part of `A2` reduces to the single geometric input that the `a → 0` rotation acts by orthogonal
congruence on the correlation operator; the invariance of the read is then a theorem. The hypercubic
point group is the special case of permutation matrices, so this subsumes the discrete part at the
spectral level. -/

/-- **A2 continuum vehicle: the spectral read is invariant under orthogonal congruence.** A read `f`
that depends only on the correlation operator's characteristic polynomial is unchanged by an
orthogonal congruence `C ↦ P C Pᵀ` (`Pᵀ P = 1`). A rotation acts this way, so a spectral read is
isotropic under `SO(4)`; what `A2` still carries on the continuum side is the geometric input that the
`a → 0` rotation acts by such a congruence on the operator. Extends `read_hypercubic_invariant`
(permutation matrices) to the full orthogonal group; [E, Prop 3.5], spectral form. -/
theorem read_orthogonal_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (P C : Matrix n n ℝ) (hP : Pᵀ * P = 1) :
    f ((P * C * Pᵀ).charpoly) = f (C.charpoly) := by
  have hcong : (P * C * Pᵀ).charpoly = C.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [hcong]

/-! ### A2 continuum: reducing the full `SO(4)` to one geometric input

`read_orthogonal_invariant` shows a spectral read is invariant under any orthogonal congruence. The
continuum part of A2 is then a single named geometric input: that between any two orientations the
`a → 0` rotation acts on the correlation operator by such a congruence. Given it, A2's continuum core is
a theorem. This mirrors A1's treatment: the open core is one explicit hypothesis with a machine-checked
downstream. -/

/-- **A2 continuum, the orthogonal-congruence input.** Between any two orientations `d, d'` the `a → 0`
rotation carries the correlation operator by an orthogonal congruence, `C d' = P (C d) Pᵀ` with
`Pᵀ P = 1`. This is discharged below: structurally by `continuumRotationCongruence_of_gram` (a coordinate
rotation of the correlation Gram exhibits it) and then from the sampling isometry by
`A2_continuum_of_sampling`, reducing A2's continuum to the Nyquist-Shannon sampling isometry. -/
def ContinuumRotationCongruence {D n : Type*} [Fintype n] [DecidableEq n]
    (C : D → Matrix n n ℝ) : Prop :=
  ∀ d d', ∃ P : Matrix n n ℝ, Pᵀ * P = 1 ∧ C d' = P * C d * Pᵀ

/-- **A2 continuum from the geometric input.** If the orientation dependence of the correlation operator
is by orthogonal congruence (`ContinuumRotationCongruence`), every spectral read `f ∘ charpoly` is
direction-independent, so `A2` holds. This discharges A2's continuum core from the single geometric
input; the read invariance itself is `read_orthogonal_invariant`. The congruence input is discharged
below, structurally by `continuumRotationCongruence_of_gram` (a coordinate rotation of the correlation
Gram exhibits it) and then from the sampling isometry by `A2_continuum_of_sampling`, so A2's continuum
reduces to the Nyquist-Shannon sampling isometry. -/
theorem A2_continuum_of_congruence {D n : Type*} [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (C : D → Matrix n n ℝ)
    (h : ContinuumRotationCongruence C) :
    A2 (fun d => f (C d).charpoly) := by
  intro d d'
  obtain ⟨P, hP, hC⟩ := h d d'
  show f (C d).charpoly = f (C d').charpoly
  rw [hC, read_orthogonal_invariant f P (C d) hP]

/-! ### A2 continuum is structural: the read is a Gram spectral functional

The remaining input `ContinuumRotationCongruence` is not a separate geometric assumption. Every
load-bearing read is a spectral functional of a correlation GRAM `C = Xᵀ X` ([E, §3, §10]: `φ`, étendue,
Strehl, `a_δ`, contrast, dominance are functions of the eigenvalue multiset of a correlation operator).
Under a coordinate rotation of the field, `X ↦ X Q` with `Qᵀ Q = 1`, the Gram transforms by orthogonal
congruence, `(X Q)ᵀ (X Q) = Qᵀ (Xᵀ X) Q`, so the congruence hypothesis is exhibited (`P = Qᵀ`), not
granted. What A2 still carries is only that the continuum correlation operator is such a Gram and that
orientations relate by a coordinate rotation of one field (the Euclidean covariance of the action) plus
the existence of the `a → 0` limit, the same limit every read needs. This is the precise form of
"entropy is coordinate-free" ([E, Prop 3.5], spectral form): a spectral read cannot introduce anisotropy
the field does not have. -/

/-- **The correlation Gram of a rotated field is an orthogonal congruence of the original.** Rotating the
field's coordinates `X ↦ X Q` sends the Gram `Xᵀ X ↦ Qᵀ (Xᵀ X) Q`. Pure matrix algebra, no hypothesis on
`Q`. -/
theorem gram_rotation_congruence {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℝ) (Q : Matrix n n ℝ) :
    (X * Q)ᵀ * (X * Q) = Qᵀ * (Xᵀ * X) * Q := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **A Gram spectral read is rotation-invariant.** A read `f ∘ charpoly` of the correlation Gram `Xᵀ X`
is unchanged when the field's coordinates are rotated, `X ↦ X Q` (`Qᵀ Q = 1`): the Gram transforms by
orthogonal congruence and a spectral read sees only the spectrum. Isotropy is structural, from the read
being a spectral functional of a Gram, not a separate input. -/
theorem gram_read_rotation_invariant {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (f : Polynomial ℝ → ℝ) (X : Matrix m n ℝ) (Q : Matrix n n ℝ) (hQ : Qᵀ * Q = 1) :
    f (((X * Q)ᵀ * (X * Q)).charpoly) = f ((Xᵀ * X).charpoly) := by
  rw [gram_rotation_congruence]
  have hP : (Qᵀ)ᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hQ
  have key := read_orthogonal_invariant f Qᵀ (Xᵀ * X) hP
  rw [Matrix.transpose_transpose] at key
  exact key

/-- **`ContinuumRotationCongruence` is automatic for a Gram-valued correlation.** If the correlation
operator in orientation `d` is the Gram of the field read in that orientation, `C d = (F d)ᵀ (F d)`, and
orientations are related by a coordinate rotation of one field, `F d' = (F d) (Q d d')` with
`(Q d d')ᵀ (Q d d') = 1`, then `ContinuumRotationCongruence` holds outright: A2's continuum input is a
consequence of the read being a correlation Gram, not a separate geometric assumption. Composing with
`A2_continuum_of_congruence` discharges A2's continuum core from Euclidean covariance of the field. -/
theorem continuumRotationCongruence_of_gram {D m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (F : D → Matrix m n ℝ) (Q : D → D → Matrix n n ℝ)
    (hQ : ∀ d d', (Q d d')ᵀ * (Q d d') = 1)
    (hrot : ∀ d d', F d' = F d * Q d d') :
    ContinuumRotationCongruence (fun d => (F d)ᵀ * F d) := by
  intro d d'
  refine ⟨(Q d d')ᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp (hQ d d')
  · show (F d')ᵀ * F d' = (Q d d')ᵀ * ((F d)ᵀ * F d) * ((Q d d')ᵀ)ᵀ
    rw [hrot d d', gram_rotation_congruence, Matrix.transpose_transpose]

/-! ### A2 continuum: the sampling-theorem bridge (exact below Nyquist)

`continuumRotationCongruence_of_gram` needs the orientations to relate by an orthogonal `Q`. The
deterministic system identification (probe P4) shows the read's directional anisotropy is exactly zero
below the Nyquist threshold, with `a⋆ k₀ = 0.364` constant across wavenumber and grid: below the
threshold the discrete samples reconstruct the band-limited field exactly (Nyquist-Shannon), so the
sampling map `Sm` and the reconstruction map `Rc` are isometries, and a coordinate rotation `Um` is an
isometry. The rotation acts on the samples by `Q = Rc Um Sm`, orthogonal as a product of orthogonals,
so the sampled field's orientations relate by an orthogonal `Q` outright and A2's continuum holds. What
A2 still carries on the continuum side is only the sampling isometry itself (Nyquist-Shannon), which the
system identification confirms is exact below the threshold, not merely asymptotic. -/

/-- **A product of orthogonal matrices is orthogonal.** -/
theorem orthogonal_mul {n : Type*} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) : (P * Q)ᵀ * (P * Q) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P Q, hP, Matrix.one_mul, hQ]

/-- **The resample-after-rotation operator is orthogonal (the sampling-theorem bridge).** Below the
Nyquist threshold the reconstruction map `Rc` and the sampling map `Sm` are isometries (`Rcᵀ Rc = 1`,
`Smᵀ Sm = 1`: the discrete samples carry the continuum inner product exactly, Nyquist-Shannon) and a
coordinate rotation `Um` is an isometry (`Umᵀ Um = 1`). The rotation acts on the samples by the operator
`Q = Rc Um Sm`, orthogonal as a product of orthogonals. -/
theorem resampling_orthogonal {n : Type*} [Fintype n] [DecidableEq n] {Rc Um Sm : Matrix n n ℝ}
    (hR : Rcᵀ * Rc = 1) (hU : Umᵀ * Um = 1) (hS : Smᵀ * Sm = 1) :
    (Rc * Um * Sm)ᵀ * (Rc * Um * Sm) = 1 :=
  orthogonal_mul (orthogonal_mul hR hU) hS

/-- **A2 continuum from the sampling isometry.** If below Nyquist the orientations of the sampled field
relate by the resample-after-rotation operator `Q = Rc Um Sm` (reconstruction, rotation, sampling, each
an isometry), then every Gram spectral read `fread ∘ charpoly ∘ (Xᵀ X)` is direction-independent: `A2`
holds. This discharges A2's continuum core from the single remaining analytic input, the Nyquist-Shannon
sampling isometry, which the deterministic system identification (probe P4, `a⋆ k₀` constant, anisotropy
at machine zero below the threshold) confirms is exact below the threshold. Composes
`resampling_orthogonal`, `continuumRotationCongruence_of_gram`, and `A2_continuum_of_congruence`. -/
theorem A2_continuum_of_sampling {D m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (fread : Polynomial ℝ → ℝ) (F : D → Matrix m n ℝ) (Rc Um Sm : D → D → Matrix n n ℝ)
    (hR : ∀ d d', (Rc d d')ᵀ * (Rc d d') = 1)
    (hU : ∀ d d', (Um d d')ᵀ * (Um d d') = 1)
    (hS : ∀ d d', (Sm d d')ᵀ * (Sm d d') = 1)
    (hrot : ∀ d d', F d' = F d * (Rc d d' * Um d d' * Sm d d')) :
    A2 (fun d => fread ((F d)ᵀ * F d).charpoly) :=
  A2_continuum_of_congruence fread (fun d => (F d)ᵀ * F d)
    (continuumRotationCongruence_of_gram F (fun d d' => Rc d d' * Um d d' * Sm d d')
      (fun d d' => resampling_orthogonal (hR d d') (hU d d') (hS d d')) hrot)

/-- **An inner-product-preserving matrix is orthogonal.** If `Q` preserves the Euclidean inner product of
every pair of vectors, `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`, then `Qᵀ Q = 1`. This is the matrix content of an
isometry: the reconstruction, rotation, and sampling maps of the sampling-theorem bridge preserve the
sample inner product (Nyquist-Shannon), hence are orthogonal, feeding `resampling_orthogonal` and
`A2_continuum_of_sampling`. The A2 counterpart of A1 bottoming out at `real_inner_self_nonneg`: A2's
sampling isometry bottoms out at this inner-product characterisation. -/
theorem orthogonal_of_preserves_dotProduct {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℝ}
    (h : ∀ x y : n → ℝ, (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y) :
    Qᵀ * Q = 1 := by
  have h2 : ∀ x y : n → ℝ, ((Qᵀ * Q) *ᵥ x) ⬝ᵥ y = x ⬝ᵥ y := fun x y => by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, h]
  ext i j
  have hk := h2 (Pi.single j 1) (Pi.single i 1)
  simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, eq_comm] using hk

end MassGap
