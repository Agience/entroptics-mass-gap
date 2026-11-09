import Mathlib
import MassGap.ApertureFixed
import MassGap.NonAbelianForget
import MassGap.EdgeCost
import MassGap.LocalLink

/-!
# MassGap.ApertureInvariance — the aperture's readings have one law at every zoom; the observer fixes the units

The author: "When you zoom finer, the aperture does not change. It's the same aperture whether you are near
or far, zoomed or not. There's an invariance in the aperture that remains regardless of what you are
looking at." And: "I guess it could be the OBSERVER that is constant more than the aperture."

The invariant object is the law of the observer's readings at fixed physical scale, not a fine
profile. Exact repetition of fine block profiles is incompatible with a gap (refinement interpolates);
the readings `ApertureFixed.ApertureReading` live in one fixed space `Fin K → Y` at every zoom, so
their laws at different zooms are comparable as laws.

## 1. The law of the readings and its invariance

* `Admissible s g φ G B`: `g` a bounded measurable function of the readings of slabs `≤ s`
  (`|g| ≤ G`), `φ` a bounded measurable reading of one slab (`|φ| ≤ B`).
* `LawEq Ch Ch'`: the two reading chains give every bounded function of the readings, at every
  horizon and every boundary path, the same expectation. `cov_eq_of_lawEq`: equal laws, equal
  connected correlations.
* `EnvLe Ch n b`: every admissible connected correlation at slab distance `n` is at most `G B b`
  (the normalised envelope at physical separation `n · slab`).
* `ClusterAt Ch m slab`: `EnvLe Ch n (4 e^{−m n slab})` at every `n`, the form `reading_cluster`
  produces.
* `ApertureInvariant A ref C`: `0 ≤ C` and at every zoom `k` and every slab distance `n`, every
  envelope bound `b` of the reference law gives the envelope bound `C b` at zoom `k`. This is the
  relative form: the zoom-`k` connected correlations at a physical separation are within the factor
  `C` of the reference ones; it compares readings with readings, no absolute scale. It is the weakest
  form the transfer below reads: only the envelope at each separation enters, only from above.
* `ApertureInvariantExact A ref`: `LawEq (A.chain k) ref` at every `k` (the author's "the same aperture").
  `apertureInvariant_of_exact`: it gives `ApertureInvariant A ref 1`.

## 2. The transfer (`gap_of_apertureInvariant`)

`ApertureInvariant A ref C` and `ClusterAt ref m A.slab` give `EnvLe (A.chain k) n (C · 4 e^{−m n slab})`
at every zoom; `expRate_of_apertureInvariant` puts it as `4 C G B ρⁿ` with `ρ = e^{−m slab} < 1`.
The proof is one line: clustering is a property of the envelope of the law, so a law whose envelope is
within `C` of a clustering one clusters at the same physical rate. The content is in the hypothesis.

`gapAt_of_apertureInvariant` wires it to the observer's gap: if every connected flowed lattice kernel
(step `m`, pair `P Q`) is, eventually in the zoom, a connected correlation of the zoom-`k` readings of
one aperture `Ap m P Q` at a slab distance covering the physical shift (`KernelReads`), each aperture
is `ApertureInvariant` against a reference law `ref m P Q`, and each reference clusters at one mass
`M > 0` in physical units, then `GapAt (transferN …) ρ`, `ρ < 1`, at every step: input 4 of
`ClayFull`, through `ApertureFixed.flowClusterAbs_of_lattice` and
`ObserverGapScale.flowClusterAbs_iff_gapAt`. `KernelReads` carries the caveat of
`ApertureFixed.ReadingRep`: no declaration constructs the aperture's chain from the Wilson measure, and
its content is the case where `A.chain k` is the law of the actual readings.

## 3. Where the coarse end sits

`dyBeta_not_strong`: every coupling of the zoom sequence has `dyBeta k ≥ 1 > 1/20`, so the
strong-coupling region `β ≤ 1/20` is no zoom of the sequence. In the statements `ref` is a free
`ReadingChain` on the reading space; the intended instance is the law of the same physical
aperture's readings in the strong-coupling Wilson measure, and no declaration ties `ref` to it.
Clustering of that measure in lattice units on the sharp box at `β ≤ 1/20` (heat-bath global gap
`7/100`) is a strong-coupling result cited here, not proved in this tree; `ClusterAt ref M slab` is
the reading-level form of that clustering and is a hypothesis here. The physical size of a strong-coupling cell is not given by the two-loop spacing:
`aRun 2 β`, extended below `β = 1`, is about `47` times coarser at `β = 1/20` than at `β = 1`, but it
peaks at `β ≈ 0.078` and falls to `0` as `β → 0`, and `1/20` is on the falling side (numerical,
`research/code/aperture_invariance_checks.py`). At the coarse end the unit is set by the observer
(Section 4).

## 4. The observer is the constant (`observer_constant_vacuous`, `gap_of_ratioInvariant`)

The observer fixes the units: every reading is measured relative to the observer's own reference
reading `r` (mass dimension one; e.g. `√σ`, or the program's `zOwn` normalisation). A zoom ↔ unit map
`a k` (the physical spacing) is a line of constant physics for the observer when `rLat k / a k = r₀`
at every zoom.

* `observer_constant_vacuous`: for every positive lattice reference reading `rLat`, `a k := rLat k / r₀`
  holds it fixed at `r₀`. As in `EdgeCost.spacing_from_sigma_is_vacuous`, holding the observer's own
  reading fixed is a choice of unit and asserts nothing about the measure.
* `ratio_indep_of_unit`: a second reading `gLat` (the gap) in physical units, divided by the observer's
  reading in the same units, is `gLat / rLat`: the unit drops out. On the observer's line the physical
  gap is `r₀ · gLat k / rLat k` (`phys_gap_on_line`). Pure Yang–Mills has one scale, so every other
  reading is a dimensionless ratio to the observer's.
* `RatioInvariant gLat rLat q C`: `q ≤ C · gLat k / rLat k` at every zoom; `q` is free (the intended
  value is the ratio at the coarse end, which the statement does not enforce). With `q, C > 0` it
  is exactly a uniform positive lower bound on `gLat k / rLat k`. `gap_of_ratioInvariant`: with `q > 0` it gives, on the observer's line, the
  physical gap `≥ r₀ q / C > 0` at every zoom, uniformly.
* `clusterAt_unit`: in the reading form only the product `m · slab` enters `ClusterAt`; changing the
  unit of length moves the factor between the mass and the slab. The reading rate is a ratio too.

Relation of the two forms. `ApertureInvariant` compares envelopes of connected correlations at fixed
physical separations; `RatioInvariant` compares one number, the gap in the observer's units. The
observer-constant line removes the unit as a free datum, but the unit was never content
(`observer_constant_vacuous`). No declaration here links the two forms (`gLat` and `rLat` are
sequences tied to no measure); the intended reading is that the ratio form is the reading form on its
slowest mode. Neither is weaker than the conclusion it feeds: `RatioInvariant` is a uniform lower
bound on the dimensionless gap, and `KernelReads` with `ApertureInvariant` and `ClusterAt` implies
the lattice clustering bound `FlowClusterAbs`. Each is the statement "the strong-coupling value of the ratio (or envelope) is carried to every
zoom", i.e. no phase transition along the line from strong to weak coupling.

## 5. The `U(1)` control

* `not_apertureInvariant_of_powerSector`: a reference law that clusters at a mass `m > 0`, and an
  aperture with a protected power sector at some zoom (`NonAbelianForget.PowerSector`: a bounded
  reading pair with covariance `≥ A₀/(n+1)^p` at every `n`; the free photon's perimeter-law readings)
  admit no `ApertureInvariant` at any `C`. Same for a long-wave sector across zooms
  (`not_apertureInvariant_of_eigenSector`). `not_exact_of_powerSector`: the laws cannot be equal.
* `u1_line_does_not_fix_ratio`: an observer line exists for any positive reference reading, and a
  zoom where the gap reading vanishes (the photon) breaks `RatioInvariant` at every `C`.
  `not_ratioInvariant_of_tendsto_zero`: the same when the ratio only tends to `0` along the line.
  Holding one reading fixed does not hold the others.

4D compact `U(1)` is confining at strong coupling and has a free photon at weak coupling (Guth 1980;
Fröhlich–Spencer 1982); its coarse and fine ends are separated by a transition, and these lemmas say
that its reading laws then fail `ApertureInvariant` and its gap ratio fails `RatioInvariant`. Which
readings of compact 4D `U(1)` carry a power floor is not proved here (the numerical check exhibits it
for the free photon).

## 6. What it asks of 4D `SU(N)`

`ApertureInvariant` for the Wilson readings of 4D `SU(N)` against the strong-coupling reference, at
some finite `C`, is the absence of a phase transition along the whole path from the strong-coupling
end to the weak-coupling end, quantitatively: the connected reading envelopes at fixed physical
separation stay within one factor of their strong-coupling values. It is not proved here and is not
discharged by anything in the tree; no lemma here touches the Wilson measure. The non-circularity is
only this: the hypothesis compares two laws, the conclusion is a decay rate; the transfer is formal,
and the comparison is where the physics is.

DERIVED (module-wide): `4` from `reading_cluster` (`cov_le` two terms, `osc φ ≤ 2B`); `1` the exact
factor and the slab of `g`; `0` the first slab and the sign of every bound; `1/20` the threshold of
the cited strong-coupling clustering.
-/

noncomputable section

namespace MassGap.ApertureInvariance

open MeasureTheory Filter Topology
open MassGap.ApertureFixed MassGap.NonAbelianForget

/-! ## 1. The law of the readings -/

section Law

variable {X : Type} [MeasurableSpace X]

/-- **An admissible reading pair**: `g` bounded measurable, read on slabs `≤ s`, `|g| ≤ G`; `φ`
measurable on one slab, `|φ| ≤ B`.

DERIVED: `1` the slab of `g`. -/
def Admissible (s : ℕ) (g : (ℕ → X) → ℝ) (φ : X → ℝ) (G B : ℝ) : Prop :=
  BM g ∧ ReadsBelow (s + 1) g ∧ (∀ ω, |g ω| ≤ G) ∧ Measurable φ ∧ ∀ x, |φ x| ≤ B

theorem Admissible.GB_nonneg {s : ℕ} {g : (ℕ → X) → ℝ} {φ : X → ℝ} {G B : ℝ}
    (h : Admissible s g φ G B) (ω₀ : ℕ → X) : 0 ≤ G * B :=
  mul_nonneg ((abs_nonneg _).trans (h.2.2.1 ω₀)) ((abs_nonneg _).trans (h.2.2.2.2 (ω₀ 0)))

/-- **Equal laws of the readings**: every function of the readings has the same expectation under
both chains, at every horizon and every boundary path.

DERIVED: `0` the first slab. -/
def LawEq (Ch Ch' : ReadingChain X) : Prop :=
  ∀ (T : ℕ) (F : (ℕ → X) → ℝ) (ω₀ : ℕ → X), Ch.seg 0 T F ω₀ = Ch'.seg 0 T F ω₀

/-- Equal laws give equal connected correlations. -/
theorem cov_eq_of_lawEq {Ch Ch' : ReadingChain X} (h : LawEq Ch Ch') (s n : ℕ)
    (g : (ℕ → X) → ℝ) (φ : X → ℝ) (ω₀ : ℕ → X) : cov Ch s n g φ ω₀ = cov Ch' s n g φ ω₀ := by
  unfold cov
  rw [h (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀, h (s + 1 + n) g ω₀,
    h (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀]

/-- **The normalised envelope at slab distance `n`**: every admissible connected correlation at that
distance is at most `G B b`. -/
def EnvLe (Ch : ReadingChain X) (n : ℕ) (b : ℝ) : Prop :=
  ∀ (s : ℕ) (g : (ℕ → X) → ℝ) (φ : X → ℝ) (G B : ℝ) (ω₀ : ℕ → X),
    Admissible s g φ G B → |cov Ch s n g φ ω₀| ≤ G * B * b

/-- **The readings cluster at mass `m`** (physical units, slabs of thickness `slab`).

DERIVED: `4` from `reading_cluster`. -/
def ClusterAt (Ch : ReadingChain X) (m slab : ℝ) : Prop :=
  ∀ n : ℕ, EnvLe Ch n (4 * Real.exp (-(m * (n * slab))))

/-- **Only `m · slab` enters**: a change of the unit of length moves a factor between the mass and
the slab. -/
theorem clusterAt_unit (Ch : ReadingChain X) (m l s : ℝ) :
    ClusterAt Ch m (l * s) ↔ ClusterAt Ch (m * l) s := by
  have e : ∀ n : ℕ, m * (n * (l * s)) = m * l * (n * s) := fun n => by ring
  simp only [ClusterAt, e]

/-- `reading_cluster` in envelope form: minorisation and memory give `ClusterAt`. -/
theorem clusterAt_of_doeblin_memory {c η θ : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) {slab : ℝ} (hs : 0 < slab) :
    ∃ m : ℝ, 0 < m ∧ ∀ (Ch : ReadingChain X) (μ₀ : Measure X), Ch.Doeblin c μ₀ → Ch.Memory η θ →
      ClusterAt Ch m slab := by
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc hη hθ0 hθ1 hsmall
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  refine ⟨-Real.log ρ / slab, div_pos (by linarith) hs, fun Ch μ₀ hD hM n s g φ G B ω₀ ha => ?_⟩
  have h := hcl Ch μ₀ hD hM s n g φ G B ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 ω₀
  have e : Real.exp (-(-Real.log ρ / slab * (n * slab))) = ρ ^ n := by
    rw [show -(-Real.log ρ / slab * (n * slab)) = n * Real.log ρ by field_simp [hs.ne']]
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  rw [e]
  calc |cov Ch s n g φ ω₀| ≤ 4 * G * B * ρ ^ n := h
    _ = G * B * (4 * ρ ^ n) := by ring

end Law

/-! ## 1b. Invariance of the aperture's law -/

/-- **The aperture's reading law is invariant up to a fixed relative factor.** At every zoom `k`
and every slab distance `n` (physical separation `n · slab`), an envelope bound `b` of the reference
law gives the envelope bound `C b` at zoom `k`. -/
def ApertureInvariant (A : ApertureReading) (ref : ReadingChain (Fin A.K → A.Y)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (k n : ℕ) (b : ℝ), EnvLe ref n b → EnvLe (A.chain k) n (C * b)

/-- **The same aperture at every zoom**: the zoom-`k` law of the readings is the reference law. -/
def ApertureInvariantExact (A : ApertureReading) (ref : ReadingChain (Fin A.K → A.Y)) : Prop :=
  ∀ k, LawEq (A.chain k) ref

/-- Exact invariance is invariance with factor `1`.

DERIVED: `1` the factor. -/
theorem apertureInvariant_of_exact {A : ApertureReading} {ref : ReadingChain (Fin A.K → A.Y)}
    (h : ApertureInvariantExact A ref) : ApertureInvariant A ref 1 := by
  refine ⟨zero_le_one, fun k n b hb s g φ G B ω₀ ha => ?_⟩
  rw [cov_eq_of_lawEq (h k), one_mul]
  exact hb s g φ G B ω₀ ha

/-! ## 2. The transfer -/

/-- **Invariance carries the reference clustering to every zoom.** `ApertureInvariant A ref C` and
`ClusterAt ref m A.slab` give the envelope `C · 4 e^{−m n slab}` at every zoom and every slab
distance.

DERIVED: `4` from `ClusterAt`. -/
theorem gap_of_apertureInvariant {A : ApertureReading} {ref : ReadingChain (Fin A.K → A.Y)}
    {C m : ℝ} (hinv : ApertureInvariant A ref C) (hcl : ClusterAt ref m A.slab) (k n : ℕ) :
    EnvLe (A.chain k) n (C * (4 * Real.exp (-(m * (n * A.slab))))) :=
  hinv.2 k n _ (hcl n)

/-- `e^{−m n slab} = (e^{−m slab})ⁿ`. -/
theorem exp_slab_pow (m slab : ℝ) (n : ℕ) :
    Real.exp (-(m * (n * slab))) = Real.exp (-(m * slab)) ^ n := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- **The transfer at a geometric rate**: one `ρ = e^{−m slab} ∈ (0, 1)` with
`|Cov_k| ≤ 4 C G B ρⁿ` at every zoom `k`, every admissible pair and every boundary.

DERIVED: `4` from `ClusterAt`. -/
theorem expRate_of_apertureInvariant {A : ApertureReading} {ref : ReadingChain (Fin A.K → A.Y)}
    {C m : ℝ} (hm : 0 < m) (hinv : ApertureInvariant A ref C) (hcl : ClusterAt ref m A.slab) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ (k s n : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ)
      (φ : (Fin A.K → A.Y) → ℝ) (G B : ℝ) (ω₀ : ℕ → Fin A.K → A.Y), Admissible s g φ G B →
        |cov (A.chain k) s n g φ ω₀| ≤ 4 * C * G * B * ρ ^ n := by
  refine ⟨Real.exp (-(m * A.slab)), Real.exp_pos _,
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (mul_pos hm A.slab_pos)), ?_⟩
  intro k s n g φ G B ω₀ ha
  have h := gap_of_apertureInvariant hinv hcl k n s g φ G B ω₀ ha
  rw [exp_slab_pow] at h
  calc _ ≤ G * B * (C * (4 * Real.exp (-(m * A.slab)) ^ n)) := h
    _ = 4 * C * G * B * Real.exp (-(m * A.slab)) ^ n := by ring

/-! ## 2b. Wiring to the observer's gap -/

section Wiring

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ContinuumSep MassGap.ContinuumFlow MassGap.ContinuumHypercubic

variable {N : ℕ}

/-- **The kernel is read by the aperture.** For every time shift `n`, eventually in the zoom, the
connected flowed lattice kernel of the pair `P Q` at step `m` is a connected correlation of the
zoom-`k` readings of `A`, of an admissible pair with `G B ≤ D`, at a slab distance `j` with
`aₘ n ≤ slab · j`.

DERIVED: `0` the first slab. -/
def KernelReads (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) {r : ℝ} (m : ℕ) (P Q : MarginMono N τ r)
    (A : ApertureReading) (D : ℝ) : Prop :=
  ∀ n : ℕ, ∀ᶠ k in atTop, ∃ (s j : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ)
    (G B : ℝ) (ω₀ : ℕ → Fin A.K → A.Y), Admissible s g φ G B ∧ G * B ≤ D ∧
      dySpacing N m * n ≤ A.slab * j ∧
      latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
          - latSF hN Φ k (pairFam τ P.1 (emptyMono N)) * latSF hN Φ k (pairFam τ (emptyMono N) Q.1)
        = cov (A.chain k) s j g φ ω₀

/-- **Input 4 from aperture invariance.** Apertures `Ap m P Q` reading the kernels, each invariant
against a reference law that clusters at one physical mass `M > 0`, give `GapAt (transferN …) ρ`,
`ρ ∈ (0, 1)`, at every step `m₀`.

DERIVED: `1` the length unit `L`; `4` from `ClusterAt`; `0`, `1` bracket the rate. -/
theorem gapAt_of_apertureInvariant (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r M : ℝ} (hphys : Φ.PhysRange r) (hM : 0 < M)
    (Ap : ℕ → MarginMono N τ r → MarginMono N τ r → ApertureReading)
    (ref : ∀ m P Q, ReadingChain (Fin (Ap m P Q).K → (Ap m P Q).Y))
    (C : ℕ → MarginMono N τ r → MarginMono N τ r → ℝ)
    (hrep : ∀ m P Q, ∃ D, KernelReads hN Φ τ m P Q (Ap m P Q) D)
    (hinv : ∀ m P Q, ApertureInvariant (Ap m P Q) (ref m P Q) (C m P Q))
    (hcl : ∀ m P Q, ClusterAt (ref m P Q) M (Ap m P Q).slab) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ := by
  have hlat : ∃ c' : ℝ, 0 < c' ∧ ∀ (m : ℕ) (P Q : MarginMono N τ r), ∃ C' : ℝ, ∀ n : ℕ,
      ∀ᶠ k in atTop,
        |latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
          - latSF hN Φ k (pairFam τ P.1 (emptyMono N)) * latSF hN Φ k (pairFam τ (emptyMono N) Q.1)|
          ≤ C' * Real.exp (-(c' / 1) * (dySpacing N m * n)) := by
    refine ⟨M, hM, fun m P Q => ?_⟩
    obtain ⟨D, hD⟩ := hrep m P Q
    refine ⟨D * (C m P Q * 4), fun n => ?_⟩
    filter_upwards [hD n] with k hk
    obtain ⟨s, j, g, φ, G, B, ω₀, ha, hGB, hsep, heq⟩ := hk
    rw [heq]
    have hC := (hinv m P Q).1
    have h := gap_of_apertureInvariant (hinv m P Q) (hcl m P Q) k j s g φ G B ω₀ ha
    have hGB0 := ha.GB_nonneg ω₀
    have hexp : Real.exp (-(M * (j * (Ap m P Q).slab)))
        ≤ Real.exp (-(M / 1) * (dySpacing N m * n)) := by
      rw [Real.exp_le_exp, div_one]
      have := mul_le_mul_of_nonneg_left hsep hM.le
      nlinarith
    calc _ ≤ G * B * (C m P Q * (4 * Real.exp (-(M * (j * (Ap m P Q).slab))))) := h
      _ ≤ D * (C m P Q * (4 * Real.exp (-(M / 1) * (dySpacing N m * n)))) :=
          mul_le_mul hGB (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num)) hC)
            (mul_nonneg hC (by positivity)) (hGB0.trans hGB)
      _ = D * (C m P Q * 4) * Real.exp (-(M / 1) * (dySpacing N m * n)) := by ring
  have hcl' := flowClusterAbs_of_lattice hN Φ hB τ (L := 1) hlat
  exact (ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
    (Flow.posPreserving_of_physRange hN Φ hphys τ) m0 one_pos).mp hcl'

end Wiring

/-! ## 3. The coarse end is not a zoom of the sequence -/

/-- **No coupling of the zoom sequence is in the strong-coupling region** `β ≤ 1/20` of the cited
strong-coupling clustering: `dyBeta k ≥ 1`.

DERIVED: `1/20` the threshold of the cited strong-coupling clustering; `1` the reference coupling. -/
theorem dyBeta_not_strong {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ¬ MassGap.ContinuumSchwinger.dyBeta hN k ≤ 1 / 20 := by
  have := MassGap.ContinuumSchwinger.one_le_dyBeta hN k
  intro h; linarith

/-! ## 4. The observer is the constant -/

section Observer

/-- **Holding the observer's reading fixed is a choice of unit.** For every positive lattice
reference reading, `a k := rLat k / r₀` makes the physical reading `r₀` at every zoom. -/
theorem observer_constant_vacuous {rLat : ℕ → ℝ} (h : ∀ k, 0 < rLat k) {r₀ : ℝ} (h0 : 0 < r₀) :
    ∃ a : ℕ → ℝ, (∀ k, 0 < a k) ∧ ∀ k, rLat k / a k = r₀ :=
  ⟨fun k => rLat k / r₀, fun k => div_pos (h k) h0, fun k => by
    have := (h k).ne'; field_simp⟩

/-- **The unit drops out of a ratio of two readings.** -/
theorem ratio_indep_of_unit (gLat rLat a : ℝ) (ha : a ≠ 0) (hr : rLat ≠ 0) :
    (gLat / a) / (rLat / a) = gLat / rLat := by
  field_simp

/-- **On the observer's line the physical gap is the observer's reading times the ratio.** -/
theorem phys_gap_on_line {gLat rLat a : ℝ} {r₀ : ℝ} (ha : a ≠ 0) (hr : rLat ≠ 0)
    (hline : rLat / a = r₀) : gLat / a = r₀ * (gLat / rLat) := by
  rw [← hline]; field_simp

/-- **The gap ratio at every zoom is within the factor `C` of its reference value `q`.** -/
def RatioInvariant (gLat rLat : ℕ → ℝ) (q C : ℝ) : Prop :=
  0 < C ∧ ∀ k, q ≤ C * (gLat k / rLat k)

/-- **The reference ratio, carried by invariance, gives a uniform physical gap on the observer's
line.** -/
theorem gap_of_ratioInvariant {gLat rLat a : ℕ → ℝ} {q C r₀ : ℝ} (hq : 0 < q) (hr0 : 0 < r₀)
    (hinv : RatioInvariant gLat rLat q C) (ha : ∀ k, a k ≠ 0) (hr : ∀ k, rLat k ≠ 0)
    (hline : ∀ k, rLat k / a k = r₀) :
    0 < r₀ * q / C ∧ ∀ k, r₀ * q / C ≤ gLat k / a k := by
  obtain ⟨hC, hk⟩ := hinv
  refine ⟨by positivity, fun k => ?_⟩
  rw [phys_gap_on_line (ha k) (hr k) (hline k), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀' hC).2 (hk k)) hr0.le

/-- **`U(1)` control, ratio form.** The observer's reading can be held fixed whatever the measure
does, and a zoom where the gap reading vanishes (the free photon) breaks `RatioInvariant` at every
factor. -/
theorem u1_line_does_not_fix_ratio {gLat rLat : ℕ → ℝ} (h : ∀ k, 0 < rLat k) {r₀ q : ℝ}
    (h0 : 0 < r₀) (hq : 0 < q) {k₁ : ℕ} (hk₁ : gLat k₁ = 0) :
    (∃ a : ℕ → ℝ, (∀ k, 0 < a k) ∧ ∀ k, rLat k / a k = r₀) ∧ ∀ C, ¬ RatioInvariant gLat rLat q C := by
  refine ⟨observer_constant_vacuous h h0, fun C hinv => ?_⟩
  have := hinv.2 k₁
  rw [hk₁, zero_div, mul_zero] at this
  linarith

/-- **A gap ratio tending to `0` along the line breaks `RatioInvariant`.** -/
theorem not_ratioInvariant_of_tendsto_zero {gLat rLat : ℕ → ℝ} {q : ℝ} (hq : 0 < q)
    (ht : Tendsto (fun k => gLat k / rLat k) atTop (𝓝 0)) (C : ℝ) :
    ¬ RatioInvariant gLat rLat q C := by
  rintro ⟨hC, hk⟩
  obtain ⟨k, hk'⟩ := (ht.eventually (gt_mem_nhds (div_pos hq hC))).exists
  have h1 := hk k
  have h2 : C * (gLat k / rLat k) < C * (q / C) := mul_lt_mul_of_pos_left hk' hC
  rw [mul_div_cancel₀ q hC.ne'] at h2
  linarith

end Observer

/-! ## 5. The `U(1)` control, reading form -/

/-- **A confined reference and a protected power sector exclude invariance.** If the reference law
clusters at `m > 0` and some zoom carries a bounded reading pair with a power floor, no factor `C`
gives `ApertureInvariant`. -/
theorem not_apertureInvariant_of_powerSector {A : ApertureReading}
    {ref : ReadingChain (Fin A.K → A.Y)} {m : ℝ} (hm : 0 < m) (hcl : ClusterAt ref m A.slab)
    (hP : PowerSector A) (C : ℝ) : ¬ ApertureInvariant A ref C := by
  intro hinv
  obtain ⟨ρ, hρ0, hρ1, hb⟩ := expRate_of_apertureInvariant hm hinv hcl
  obtain ⟨k, s, g, φ, G, B, ω₀, A₀, p, hg, hgr, hG, hφ, hB, hA₀, hfloor⟩ := hP
  exact not_exp_of_powerFloor hA₀ hfloor
    ⟨4 * C * G * B, ρ, hρ0.le, hρ1, fun n => hb k s n g φ G B ω₀ ⟨hg, hgr, hG, hφ, hB⟩⟩

/-- **The laws cannot be equal either.** -/
theorem not_exact_of_powerSector {A : ApertureReading} {ref : ReadingChain (Fin A.K → A.Y)}
    {m : ℝ} (hm : 0 < m) (hcl : ClusterAt ref m A.slab) (hP : PowerSector A) :
    ¬ ApertureInvariantExact A ref := fun h =>
  not_apertureInvariant_of_powerSector hm hcl hP 1 (apertureInvariant_of_exact h)

/-- **A confined reference and a long-wave sector across zooms exclude invariance.** -/
theorem not_apertureInvariant_of_eigenSector {A : ApertureReading}
    {ref : ReadingChain (Fin A.K → A.Y)} {m : ℝ} (hm : 0 < m) (hcl : ClusterAt ref m A.slab)
    (hE : EigenSector A) (C : ℝ) : ¬ ApertureInvariant A ref C := by
  intro hinv
  obtain ⟨ρ, hρ0, hρ1, hb⟩ := expRate_of_apertureInvariant hm hinv hcl
  obtain ⟨s, g, φ, G, B, ω₀, A₀, lam, hg, hgr, hG, hφ, hB, hA₀, hsup, hfloor⟩ := hE
  exact not_uniform_exp_of_eigenFloor (fun k n => |cov (A.chain k) s n (g k) (φ k) (ω₀ k)|) lam
    hA₀ hfloor hsup ⟨4 * C * G * B, ρ, hρ0.le, hρ1, fun k n =>
      hb k s n (g k) (φ k) G B (ω₀ k) ⟨hg k, hgr k, hG k, hφ k, hB k⟩⟩

#print axioms cov_eq_of_lawEq
#print axioms clusterAt_unit
#print axioms clusterAt_of_doeblin_memory
#print axioms apertureInvariant_of_exact
#print axioms gap_of_apertureInvariant
#print axioms expRate_of_apertureInvariant
#print axioms gapAt_of_apertureInvariant
#print axioms dyBeta_not_strong
#print axioms observer_constant_vacuous
#print axioms ratio_indep_of_unit
#print axioms phys_gap_on_line
#print axioms gap_of_ratioInvariant
#print axioms u1_line_does_not_fix_ratio
#print axioms not_ratioInvariant_of_tendsto_zero
#print axioms not_apertureInvariant_of_powerSector
#print axioms not_exact_of_powerSector
#print axioms not_apertureInvariant_of_eigenSector

end MassGap.ApertureInvariance
