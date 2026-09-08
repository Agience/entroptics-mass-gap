import MassGap.WilsonLattice
import MassGap.WilsonAction
import MassGap.SUN

/-!
# MassGap.WilsonReal — a concrete SU(2) Wilson system with a genuine symmetry (dynamical face, brick 2b)

Non-vacuousness for the `WilsonLattice` framework: a real `SU(2)` gauge theory with **two plaquettes**,
each a genuine four-link ordered Wilson loop `U₀ U₁ U₂⁻¹ U₃⁻¹`, the **real Wilson action density**
(`WilsonAction.wilsonDensity`), and a `ℤ/2` symmetry that **swaps the two plaquettes** (relabelling the
eight links by the block map `i ↦ i+4`). The boundary-word compatibility `hbd2` is a finite computation
(`decide`), and `sysReal_invariant` is the Euclidean/permutation invariance of the genuine Wilson Gibbs
correlation under that swap — derived from Haar-invariance, on the real action. Foundational footprint.

Build: `lake build MassGap.WilsonReal`.
-/

namespace MassGap.WilsonReal

open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.CompactGauge MeasureTheory
  ProbabilityTheory

/-- `SU(2)`. -/
abbrev G2 : Type := MassGap.SUN.SU 2

/-- Two plaquettes over eight links, each a four-link loop `U₀U₁U₂⁻¹U₃⁻¹`. -/
def bd2 (p : Fin 2) : List (Fin 8 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else [(4, true), (5, true), (6, false), (7, false)]

/-- Link relabelling `i ↦ i + 4` on `Fin 8` — the block swap exchanging the two plaquettes' links. -/
def σL2 : Equiv.Perm (Fin 8) := Equiv.addLeft (4 : Fin 8)

/-- Plaquette swap on `Fin 2`. -/
def σP2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The boundary words map compatibly under the swap — a finite check. -/
theorem hbd2 : ∀ p, bd2 (σP2 p) = (bd2 p).map (fun lo => (σL2 lo.1, lo.2)) := by decide

/-- The concrete two-plaquette `SU(2)` Wilson system (genuine ordered-loop holonomy, real action). -/
noncomputable def sysReal : System G2 := wilsonSystem bd2 wilsonDensity

/-- The `ℤ/2` plaquette-swap symmetry of the Wilson system. -/
noncomputable def symReal : Symmetry sysReal := wilsonSymmetry bd2 wilsonDensity σL2 σP2 hbd2

/-- **Invariance of the real `SU(2)` Wilson correlation under the plaquette swap.** For the canonical
probability Haar measure (or any left-invariant probability measure), the Gibbs expectation is invariant
under transporting the observable by the swap — derived from Haar-invariance, on the genuine Wilson
action. -/
theorem sysReal_invariant (μ : Measure G2) [IsProbabilityMeasure μ] (β : ℝ)
    (O : sysReal.Config → ℝ) :
    sysReal.expect μ β (fun U => O (Symmetry.reindex symReal.onLink U)) = sysReal.expect μ β O :=
  wilson_expect_invariant bd2 wilsonDensity σL2 σP2 hbd2 μ β O

/-- **The Wilson action density is invariant under a global gauge transformation.** Conjugating every
link by a fixed `g ∈ SU(N)` conjugates the plaquette holonomy (`wilsonHol_conj`), and `wilsonDensity`
is conjugation-invariant (`wilsonDensity_conj`) — so the plaquette Wilson action is gauge-invariant.
The algebraic content of gauge invariance, on the genuine ordered-loop holonomy; general `N`. -/
theorem wilsonAction_gauge_invariant {N : ℕ} {Lk Pq : Type}
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (p : Pq)
    (U : Lk → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol bd p (fun l => g * U l * g⁻¹))
      = wilsonDensity (wilsonHol bd p U) := by
  rw [wilsonHol_conj]
  exact wilsonDensity_conj g (wilsonHol bd p U)

/-- The Wilson action is invariant under a global gauge transformation (each plaquette term, from
`wilsonAction_gauge_invariant`). -/
theorem sysReal_action_gauge (g : G2) (U : sysReal.Config) :
    sysReal.action (confConj G2 g U) = sysReal.action U :=
  Finset.sum_congr rfl (fun p _ => wilsonAction_gauge_invariant bd2 g p U)

/-- The Boltzmann weight is invariant under a global gauge transformation. -/
theorem sysReal_boltz_gauge (g : G2) (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β (confConj G2 g U) = sysReal.boltz β U := by
  unfold System.boltz; rw [sysReal_action_gauge]

/-- **Gauge invariance of the real `SU(2)` Wilson correlation.** For the canonical probability Haar
measure, the Gibbs expectation is invariant under a global gauge transformation `U ↦ gUg⁻¹`: the
conjugation preserves the Haar measure (`confConjEquiv_measurePreserving`, from unimodularity) and the
Wilson action (`sysReal_boltz_gauge`), so `⟨O∘conj⟩ = ⟨O⟩` by the general mechanism
`expect_invariant_of_mp`. The defining symmetry of a gauge theory, on the genuine ordered-loop Wilson
action. -/
theorem sysReal_gauge_invariant (g : G2) (β : ℝ) (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) β (fun U => O (confConj G2 g U))
      = sysReal.expect (probHaar G2) β O :=
  System.expect_invariant_of_mp sysReal (probHaar G2) β O (confConjEquiv G2 g)
    (confConjEquiv_measurePreserving G2 g) (fun U => sysReal_boltz_gauge g β U)

/-! ### Gauge invariance for an arbitrary SU(N) Wilson system -/

/-- The Wilson action of ANY `SU(N)` Wilson system is gauge-invariant (each plaquette term). -/
theorem wilsonSystem_action_gauge {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N)
    (U : (wilsonSystem bd wilsonDensity).Config) :
    (wilsonSystem bd wilsonDensity).action (confConj (MassGap.SUN.SU N) g U)
      = (wilsonSystem bd wilsonDensity).action U :=
  Finset.sum_congr rfl (fun p _ => wilsonAction_gauge_invariant bd g p U)

/-- The Boltzmann weight of any `SU(N)` Wilson system is gauge-invariant. -/
theorem wilsonSystem_boltz_gauge {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (β : ℝ)
    (U : (wilsonSystem bd wilsonDensity).Config) :
    (wilsonSystem bd wilsonDensity).boltz β (confConj (MassGap.SUN.SU N) g U)
      = (wilsonSystem bd wilsonDensity).boltz β U := by
  unfold System.boltz; rw [wilsonSystem_action_gauge]

/-- **Gauge invariance of ANY `SU(N)` Wilson correlation** (general lattice, any `N`): for the canonical
probability Haar measure, `⟨O ∘ (U↦gUg⁻¹)⟩ = ⟨O⟩`. The 2-plaquette `sysReal_gauge_invariant` is the
concrete instance. -/
theorem wilsonSystem_gauge_invariant {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (β : ℝ)
    (O : (wilsonSystem bd wilsonDensity).Config → ℝ) :
    (wilsonSystem bd wilsonDensity).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O (confConj (MassGap.SUN.SU N) g U))
      = (wilsonSystem bd wilsonDensity).expect (probHaar (MassGap.SUN.SU N)) β O :=
  System.expect_invariant_of_mp (wilsonSystem bd wilsonDensity) (probHaar (MassGap.SUN.SU N)) β O
    (confConjEquiv (MassGap.SUN.SU N) g) (confConjEquiv_measurePreserving (MassGap.SUN.SU N) g)
    (fun U => wilsonSystem_boltz_gauge bd g β U)

/-! ### A translation-symmetric 3-plaquette ring (a genuine ℤ/3 lattice translation) -/

/-- Three plaquettes in a ring over twelve links (four per plaquette), each a `U₀U₁U₂⁻¹U₃⁻¹` loop. -/
def bd3 (p : Fin 3) : List (Fin 12 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else if p = 1 then [(4, true), (5, true), (6, false), (7, false)]
  else [(8, true), (9, true), (10, false), (11, false)]

/-- Link translation `i ↦ i + 4` on `Fin 12` — shifts each plaquette's links to the next plaquette's. -/
def σL3 : Equiv.Perm (Fin 12) := Equiv.addLeft (4 : Fin 12)

/-- Cyclic plaquette translation `p ↦ p + 1` on `Fin 3`. -/
def σP3 : Equiv.Perm (Fin 3) := Equiv.addLeft (1 : Fin 3)

/-- The boundary words map compatibly under the translation — a finite check. -/
theorem hbd3 : ∀ p, bd3 (σP3 p) = (bd3 p).map (fun lo => (σL3 lo.1, lo.2)) := by decide

/-- The 3-plaquette ring `SU(2)` Wilson system. -/
noncomputable def sysRing : System G2 := wilsonSystem bd3 wilsonDensity

/-- The ℤ/3 translation symmetry of the ring. -/
noncomputable def symRing : Symmetry sysRing := wilsonSymmetry bd3 wilsonDensity σL3 σP3 hbd3

/-- **Translation invariance of the ring Wilson correlation.** The Gibbs expectation is invariant under
the cyclic ℤ/3 lattice translation — a genuine translation symmetry (not merely a swap), derived from
Haar-invariance on the real ordered-loop Wilson action. -/
theorem sysRing_invariant (μ : Measure G2) [IsProbabilityMeasure μ] (β : ℝ)
    (O : sysRing.Config → ℝ) :
    sysRing.expect μ β (fun U => O (Symmetry.reindex symRing.onLink U)) = sysRing.expect μ β O :=
  wilson_expect_invariant bd3 wilsonDensity σL3 σP3 hbd3 μ β O

/-- The concrete `SU(2)` two-plaquette Wilson holonomy is measurable — confirming `SU(N)` carries the
measurable group operations (`MeasurableMul₂`/`MeasurableInv`, from its topology + Borel structure). -/
theorem measurable_bd2_hol (p : Fin 2) : Measurable (wilsonHol (G := G2) bd2 p) :=
  measurable_wilsonHol bd2 p

/-- The `SU(2)` Wilson action is measurable (sum of `wilsonDensity ∘ holonomy`). -/
theorem measurable_sysReal_action : Measurable sysReal.action :=
  Finset.measurable_sum _ (fun p _ => measurable_wilsonDensity.comp (measurable_bd2_hol p))

/-- The `SU(2)` Wilson Boltzmann weight `e^{-βS}` is measurable. -/
theorem measurable_sysReal_boltz (β : ℝ) : Measurable (sysReal.boltz β) :=
  Real.measurable_exp.comp (measurable_const.mul measurable_sysReal_action)

/-- The `SU(2)` Wilson action is nonnegative (`wilsonDensity ≥ 0` per plaquette). -/
theorem sysReal_action_nonneg (U : sysReal.Config) : 0 ≤ sysReal.action U :=
  Finset.sum_nonneg (fun p _ => wilsonDensity_nonneg (by norm_num) _)

/-- The `SU(2)` two-plaquette Wilson action is at most `4` (two plaquettes, each `wilsonDensity ≤ 2`). -/
theorem sysReal_action_le (U : sysReal.Config) : sysReal.action U ≤ 4 := by
  have h : sysReal.action U ≤ ∑ _p : Fin 2, (2 : ℝ) :=
    Finset.sum_le_sum (fun p _ => wilsonDensity_le_two (by norm_num) _)
  have he : (∑ _p : Fin 2, (2 : ℝ)) = 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  linarith

/-- The `SU(2)` Wilson Boltzmann weight is strictly positive. -/
theorem sysReal_boltz_pos (β : ℝ) (U : sysReal.Config) : 0 < sysReal.boltz β U := by
  unfold System.boltz; exact Real.exp_pos _

/-- **The `SU(2)` Wilson partition function is strictly positive** — so the Gibbs expectation
`⟨O⟩ = (∫ O e^{-βS})/Z` is well-defined (no `0/0`). The Boltzmann weight is measurable, bounded
(`e^{-βS} ≤ e^{4|β|}` since `S ∈ [0,4]`) hence integrable on the probability Haar measure, and
strictly positive everywhere, so its integral is positive. -/
theorem sysReal_partition_pos (β : ℝ) : 0 < sysReal.partition (probHaar G2) β := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  unfold System.partition
  have hbound : ∀ U, ‖sysReal.boltz β U‖ ≤ Real.exp (4 * |β|) := by
    intro U
    rw [Real.norm_of_nonneg (sysReal_boltz_pos β U).le]
    unfold System.boltz
    rw [Real.exp_le_exp]
    have h1 : -β * sysReal.action U ≤ |β| * sysReal.action U :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (sysReal_action_nonneg U)
    have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
      mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
    linarith
  have hint : Integrable (sysReal.boltz β) (sysReal.vol (probHaar G2)) :=
    (integrable_const (Real.exp (4 * |β|))).mono'
      (measurable_sysReal_boltz β).aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [integral_pos_iff_support_of_nonneg (fun U => (sysReal_boltz_pos β U).le) hint]
  have hsupp : Function.support (sysReal.boltz β) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (sysReal_boltz_pos β U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

/-- **Normalization: `⟨1⟩ = 1`.** The Gibbs expectation of the constant `1` is `1` (since `Z > 0`), so
the Wilson measure is a genuine probability average. -/
theorem sysReal_expect_one (β : ℝ) : sysReal.expect (probHaar G2) β (fun _ => (1 : ℝ)) = 1 := by
  unfold System.expect System.corrNum
  simp only [one_mul]
  rw [show (∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2)))
      = sysReal.partition (probHaar G2) β from rfl]
  exact div_self (sysReal_partition_pos β).ne'

/-- **Positivity: `⟨O⟩ ≥ 0` for `O ≥ 0`.** A nonnegative observable has nonnegative Gibbs expectation
(the Boltzmann weight is positive and `Z > 0`) — the positivity of the Wilson gauge state. -/
theorem sysReal_expect_nonneg (β : ℝ) (O : sysReal.Config → ℝ) (hO : ∀ U, 0 ≤ O U) :
    0 ≤ sysReal.expect (probHaar G2) β O := by
  unfold System.expect
  refine div_nonneg ?_ (sysReal_partition_pos β).le
  unfold System.corrNum
  exact integral_nonneg (fun U => mul_nonneg (hO U) (sysReal_boltz_pos β U).le)

/-- **Monotonicity: `⟨O⟩ ≤ ⟨O'⟩` for `O ≤ O'`** (with the honest integrability hypotheses). The Gibbs
expectation is monotone: `Z > 0` and the Boltzmann weight is nonnegative. -/
theorem sysReal_expect_mono (β : ℝ) (O O' : sysReal.Config → ℝ)
    (hint : Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hint' : Integrable (fun U => O' U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hO : ∀ U, O U ≤ O' U) :
    sysReal.expect (probHaar G2) β O ≤ sysReal.expect (probHaar G2) β O' := by
  unfold System.expect
  refine (div_le_div_iff_of_pos_right (sysReal_partition_pos β)).mpr ?_
  unfold System.corrNum
  exact integral_mono hint hint'
    (fun U => mul_le_mul_of_nonneg_right (hO U) (sysReal_boltz_pos β U).le)

/-- **Homogeneity: `⟨c·O⟩ = c·⟨O⟩`** (unconditional — `integral_const_mul` needs no integrability). -/
theorem sysReal_expect_smul (β c : ℝ) (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) β (fun U => c * O U)
      = c * sysReal.expect (probHaar G2) β O := by
  unfold System.expect System.corrNum
  have h : (fun U => (c * O U) * sysReal.boltz β U)
      = (fun U => c * (O U * sysReal.boltz β U)) := by funext U; ring
  rw [h, integral_const_mul, mul_div_assoc]

/-- **Additivity: `⟨O+O'⟩ = ⟨O⟩ + ⟨O'⟩`** (with the honest integrability hypotheses). Together with
`sysReal_expect_smul` this makes `⟨·⟩` linear; with `_one`/`_nonneg` it is a positive normalized linear
functional — a genuine *state* on the observables. -/
theorem sysReal_expect_add (β : ℝ) (O O' : sysReal.Config → ℝ)
    (hint : Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)))
    (hint' : Integrable (fun U => O' U * sysReal.boltz β U) (sysReal.vol (probHaar G2))) :
    sysReal.expect (probHaar G2) β (fun U => O U + O' U)
      = sysReal.expect (probHaar G2) β O + sysReal.expect (probHaar G2) β O' := by
  unfold System.expect System.corrNum
  have h : (fun U => (O U + O' U) * sysReal.boltz β U)
      = (fun U => O U * sysReal.boltz β U + O' U * sysReal.boltz β U) := by funext U; ring
  rw [h, integral_add hint hint', add_div]

/-- **Uniform bound on the Boltzmann weight: `e^{-βS} ≤ e^{4|β|}`** (since `S ∈ [0,4]`). The reusable
form of the bound used inside `sysReal_partition_pos`. -/
theorem sysReal_boltz_le (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β U ≤ Real.exp (4 * |β|) := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -β * sysReal.action U ≤ |β| * sysReal.action U :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (sysReal_action_nonneg U)
  have h2 : |β| * sysReal.action U ≤ |β| * 4 :=
    mul_le_mul_of_nonneg_left (sysReal_action_le U) (abs_nonneg β)
  linarith

/-- **`O·e^{-βS}` is integrable for any bounded measurable observable `O`** (`|O| ≤ M`): the integrand is
bounded by `M·e^{4|β|}` and measurable, hence integrable on the probability Haar measure. This
**discharges the integrability hypotheses** of `sysReal_expect_add`/`sysReal_expect_mono` for every
physical (bounded) observable, so linearity and monotonicity hold unconditionally on them. -/
theorem sysReal_mul_boltz_integrable (β : ℝ) (O : sysReal.Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Integrable (fun U => O U * sysReal.boltz β U) (sysReal.vol (probHaar G2)) := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  refine (integrable_const (M * Real.exp (4 * |β|))).mono'
    ((hmeas.mul (measurable_sysReal_boltz β)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [norm_mul, Real.norm_of_nonneg (sysReal_boltz_pos β U).le]
  have hO : ‖O U‖ ≤ M := by rw [Real.norm_eq_abs]; exact hbound U
  exact mul_le_mul hO (sysReal_boltz_le β U) (sysReal_boltz_pos β U).le
    (le_trans (norm_nonneg _) hO)

/-- **Boundedness (contractivity): `|⟨O⟩| ≤ M` for `|O| ≤ M`.** The state has operator norm `≤ 1`:
`|∫ O e^{-βS}| ≤ ∫ |O| e^{-βS} ≤ M·Z`, divided by `Z`. Completes `⟨·⟩` as a *bounded* positive normalized
linear functional — a state in the operator-algebra sense. -/
theorem sysReal_expect_abs_le (β : ℝ) (O : sysReal.Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    |sysReal.expect (probHaar G2) β O| ≤ M := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hZ := sysReal_partition_pos β
  have hint := sysReal_mul_boltz_integrable β O hmeas M hbound
  have hb : Integrable (sysReal.boltz β) (sysReal.vol (probHaar G2)) := by
    have := sysReal_mul_boltz_integrable β (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
    simpa using this
  have hintM := hb.const_mul M
  unfold System.expect
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  unfold System.corrNum
  calc |∫ U, O U * sysReal.boltz β U ∂(sysReal.vol (probHaar G2))|
      ≤ ∫ U, |O U * sysReal.boltz β U| ∂(sysReal.vol (probHaar G2)) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ U, M * sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := by
        refine integral_mono hint.abs hintM (fun U => ?_)
        rw [abs_mul, abs_of_pos (sysReal_boltz_pos β U)]
        exact mul_le_mul_of_nonneg_right (hbound U) (sysReal_boltz_pos β U).le
    _ = M * ∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2)) := integral_const_mul M _
    _ = M * sysReal.partition (probHaar G2) β := rfl

/-- **The β=0 (trivial-coupling) evaluation: `⟨O⟩ = ∫ O dHaar`.** At zero coupling the Boltzmann weight
is `1`, so `Z = 1` and the Wilson state reduces to the bare product-Haar average — the free/infinite-
temperature anchor of the theory. -/
theorem sysReal_expect_at_zero (O : sysReal.Config → ℝ) :
    sysReal.expect (probHaar G2) 0 O = ∫ U, O U ∂(sysReal.vol (probHaar G2)) := by
  haveI : IsProbabilityMeasure (sysReal.vol (probHaar G2)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin 8 => probHaar G2)))
  have hb : ∀ U, sysReal.boltz 0 U = 1 := fun U => by unfold System.boltz; simp
  have hvol : (sysReal.vol (probHaar G2)).real Set.univ = 1 := by
    change ((sysReal.vol (probHaar G2)) Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hden : sysReal.partition (probHaar G2) 0 = 1 := by
    unfold System.partition
    simp only [hb, integral_const, smul_eq_mul, mul_one, hvol]
  unfold System.expect System.corrNum
  simp only [hb, mul_one]
  rw [hden, div_one]

/-! ### General SU(N) Wilson systems: well-definedness at any N and any finite lattice

The `sysReal` well-definedness (`Z>0`) is generalized here to an **arbitrary** `SU(N)` Wilson system on any
finite lattice — the same nonnegativity/uniform-bound/integrability/positivity chain, with the plaquette
count `#Plaq` in place of the concrete `4`. So the Gibbs state is well-defined for every genuine Wilson
theory, not merely the 2-plaquette instance. -/

/-- The action of any `SU(N)` Wilson system is nonnegative (`N ≠ 0`). -/
theorem wilsonSystem_action_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).action U :=
  Finset.sum_nonneg (fun p _ => wilsonDensity_nonneg hN _)

/-- The action of any `SU(N)` Wilson system is at most `2·#Plaq` (each plaquette `≤ 2`). -/
theorem wilsonSystem_action_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).action U ≤ 2 * (Fintype.card Pq : ℝ) := by
  have h : (wilsonSystem bd wilsonDensity).action U ≤ ∑ _p : Pq, (2 : ℝ) :=
    Finset.sum_le_sum (fun p _ => wilsonDensity_le_two hN _)
  have he : (∑ _p : Pq, (2 : ℝ)) = 2 * (Fintype.card Pq : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  linarith

/-- The action of any `SU(N)` Wilson system is measurable. -/
theorem measurable_wilsonSystem_action {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) :
    Measurable (wilsonSystem bd (wilsonDensity (N := N))).action :=
  Finset.measurable_sum _ (fun p _ =>
    measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU N) bd p))

/-- The Boltzmann weight of any `SU(N)` Wilson system is measurable. -/
theorem measurable_wilsonSystem_boltz {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    Measurable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) :=
  Real.measurable_exp.comp (measurable_const.mul (measurable_wilsonSystem_action bd))

/-- The Boltzmann weight of any `SU(N)` Wilson system is strictly positive. -/
theorem wilsonSystem_boltz_pos {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).boltz β U := by
  unfold System.boltz; exact Real.exp_pos _

/-- **The partition function of any `SU(N)` Wilson system is strictly positive** — the Gibbs state is
well-defined for every genuine Wilson theory on a finite lattice, at any `N ≥ 1`. Same proof shape as the
2-plaquette `sysReal_partition_pos`, with the uniform weight bound `e^{2·#Plaq·|β|}`. -/
theorem wilsonSystem_partition_pos {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    0 < (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  unfold System.partition
  set B : ℝ := |β| * (2 * (Fintype.card Pq : ℝ)) with hB
  have hbound : ∀ U : (wilsonSystem bd (wilsonDensity (N := N))).Config,
      ‖(wilsonSystem bd (wilsonDensity (N := N))).boltz β U‖ ≤ Real.exp B := by
    intro U
    rw [Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]
    unfold System.boltz
    rw [Real.exp_le_exp]
    have h1 : -β * (wilsonSystem bd (wilsonDensity (N := N))).action U
        ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U :=
      mul_le_mul_of_nonneg_right (neg_le_abs β) (wilsonSystem_action_nonneg hN bd U)
    have h2 : |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U
        ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
      mul_le_mul_of_nonneg_left (wilsonSystem_action_le hN bd U) (abs_nonneg β)
    rw [hB]; linarith
  have hint : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (integrable_const (Real.exp B)).mono'
      (measurable_wilsonSystem_boltz bd β).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  rw [integral_pos_iff_support_of_nonneg
      (fun U => (wilsonSystem_boltz_pos bd β U).le) hint]
  have hsupp : Function.support ((wilsonSystem bd (wilsonDensity (N := N))).boltz β) = Set.univ :=
    Set.eq_univ_of_forall (fun U => Function.mem_support.mpr (wilsonSystem_boltz_pos bd β U).ne')
  rw [hsupp, measure_univ]
  exact one_pos

/-- **Normalization `⟨1⟩=1`** for any `SU(N)` Wilson system. -/
theorem wilsonSystem_expect_one {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
      (fun _ => (1 : ℝ)) = 1 := by
  unfold System.expect System.corrNum
  simp only [one_mul]
  rw [show (∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
      = (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β from rfl]
  exact div_self (wilsonSystem_partition_pos hN bd β).ne'

/-- **Positivity `⟨O⟩≥0` for `O≥0`** for any `SU(N)` Wilson system. -/
theorem wilsonSystem_expect_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) (hO : ∀ U, 0 ≤ O U) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O := by
  unfold System.expect
  refine div_nonneg ?_ (wilsonSystem_partition_pos hN bd β).le
  unfold System.corrNum
  exact integral_nonneg (fun U => mul_nonneg (hO U) (wilsonSystem_boltz_pos bd β U).le)

/-- **Homogeneity `⟨c·O⟩=c⟨O⟩`** for any `SU(N)` Wilson system (unconditional). -/
theorem wilsonSystem_expect_smul {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β c : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => c * O U)
      = c * (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O := by
  unfold System.expect System.corrNum
  have h : (fun U => (c * O U) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      = (fun U => c * (O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)) := by
    funext U; ring
  rw [h, integral_const_mul, mul_div_assoc]

/-- **Additivity `⟨O+O'⟩=⟨O⟩+⟨O'⟩`** for any `SU(N)` Wilson system (integrability hyps). -/
theorem wilsonSystem_expect_add {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O O' : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hint : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hint' : Integrable (fun U => O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (fun U => O U + O' U)
      = (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
        + (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  unfold System.expect System.corrNum
  have h : (fun U => (O U + O' U) * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      = (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
          + O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U) := by funext U; ring
  rw [h, integral_add hint hint', add_div]

/-- **Monotonicity `⟨O⟩≤⟨O'⟩` for `O≤O'`** for any `SU(N)` Wilson system (integrability hyps). So the
Gibbs state of every genuine `SU(N)` Wilson theory is a positive, normalized, linear, monotone
functional — not merely the 2-plaquette instance. -/
theorem wilsonSystem_expect_mono {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O O' : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hint : Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hint' : Integrable (fun U => O' U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))))
    (hO : ∀ U, O U ≤ O' U) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O
      ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O' := by
  unfold System.expect
  refine (div_le_div_iff_of_pos_right (wilsonSystem_partition_pos hN bd β)).mpr ?_
  unfold System.corrNum
  exact integral_mono hint hint'
    (fun U => mul_le_mul_of_nonneg_right (hO U) (wilsonSystem_boltz_pos bd β U).le)

/-- **Uniform weight bound `e^{-βS} ≤ e^{|β|·2·#Plaq}`** for any `SU(N)` Wilson system (reusable). -/
theorem wilsonSystem_boltz_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
      ≤ Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))) := by
  unfold System.boltz
  rw [Real.exp_le_exp]
  have h1 : -β * (wilsonSystem bd (wilsonDensity (N := N))).action U
      ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) (wilsonSystem_action_nonneg hN bd U)
  have h2 : |β| * (wilsonSystem bd (wilsonDensity (N := N))).action U
      ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
    mul_le_mul_of_nonneg_left (wilsonSystem_action_le hN bd U) (abs_nonneg β)
  linarith

/-- **`O·e^{-βS}` integrable for bounded measurable `O`** on any `SU(N)` Wilson system — discharges the
`_add`/`_mono` integrability hypotheses for every physical observable, at any `N`. -/
theorem wilsonSystem_mul_boltz_integrable {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    Integrable (fun U => O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  refine (integrable_const (M * Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))))).mono'
    ((hmeas.mul (measurable_wilsonSystem_boltz bd β)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun U => ?_))
  rw [norm_mul, Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]
  have hO : ‖O U‖ ≤ M := by rw [Real.norm_eq_abs]; exact hbound U
  exact mul_le_mul hO (wilsonSystem_boltz_le hN bd β U) (wilsonSystem_boltz_pos bd β U).le
    (le_trans (norm_nonneg _) hO)

/-- **Boundedness/contractivity `|⟨O⟩| ≤ M` for `|O| ≤ M`** on any `SU(N)` Wilson system — operator norm
`≤ 1`. Completes the elementary Gibbs-state theory at general `N`: every genuine `SU(N)` Wilson theory on
a finite lattice carries a bounded positive normalized linear functional. -/
theorem wilsonSystem_expect_abs_le {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ)
    (hmeas : Measurable O) (M : ℝ) (hbound : ∀ U, |O U| ≤ M) :
    |(wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β O| ≤ M := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hZ := wilsonSystem_partition_pos hN bd β
  have hint := wilsonSystem_mul_boltz_integrable hN bd β O hmeas M hbound
  have hb : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
    have := wilsonSystem_mul_boltz_integrable hN bd β (fun _ => (1 : ℝ)) measurable_const 1
      (fun _ => by norm_num)
    simpa using this
  have hintM := hb.const_mul M
  unfold System.expect
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  unfold System.corrNum
  calc |∫ U, O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))|
      ≤ ∫ U, |O U * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U|
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ U, M * (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
        refine integral_mono hint.abs hintM (fun U => ?_)
        rw [abs_mul, abs_of_pos (wilsonSystem_boltz_pos bd β U)]
        exact mul_le_mul_of_nonneg_right (hbound U) (wilsonSystem_boltz_pos bd β U).le
    _ = M * ∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
        integral_const_mul M _
    _ = M * (wilsonSystem bd (wilsonDensity (N := N))).partition
        (probHaar (MassGap.SUN.SU N)) β := rfl

/-- **The β=0 (trivial-coupling) reduction `⟨O⟩ = ∫ O dHaar`** for any `SU(N)` Wilson system: at zero
coupling the state is the bare product-Haar average — the free/infinite-temperature anchor at general `N`. -/
theorem wilsonSystem_expect_at_zero {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool))
    (O : (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ) :
    (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) 0 O
      = ∫ U, O U ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hb : ∀ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz 0 U = 1 :=
    fun U => by unfold System.boltz; simp
  have hvol : ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))).real Set.univ = 1 := by
    change (((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) Set.univ).toReal = 1
    rw [measure_univ, ENNReal.toReal_one]
  have hden : (wilsonSystem bd (wilsonDensity (N := N))).partition
      (probHaar (MassGap.SUN.SU N)) 0 = 1 := by
    unfold System.partition
    simp only [hb, integral_const, smul_eq_mul, mul_one, hvol]
  unfold System.expect System.corrNum
  simp only [hb, mul_one]
  rw [hden, div_one]

/-! ### The physical order parameter at general `N`: the plaquette-energy observable -/

/-- The **plaquette-energy observable** `U ↦ φ_W(hol_p U)` of an arbitrary `SU(N)` Wilson system. -/
noncomputable def wilsonPlaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq) :
    (wilsonSystem bd (wilsonDensity (N := N))).Config → ℝ :=
  fun U => wilsonDensity (wilsonHol bd p U)

theorem wilsonPlaqObs_nonneg {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) : 0 ≤ wilsonPlaqObs bd p U :=
  wilsonDensity_nonneg hN _

theorem wilsonPlaqObs_le_two {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) : wilsonPlaqObs bd p U ≤ 2 :=
  wilsonDensity_le_two hN _

theorem measurable_wilsonPlaqObs {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (p : Pq) : Measurable (wilsonPlaqObs (N := N) bd p) :=
  measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU N) bd p)

/-- The general plaquette-energy observable is gauge-invariant. -/
theorem wilsonPlaqObs_gauge_invariant {N : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (g : MassGap.SUN.SU N) (p : Pq)
    (U : (wilsonSystem bd (wilsonDensity (N := N))).Config) :
    wilsonPlaqObs bd p (confConj (MassGap.SUN.SU N) g U) = wilsonPlaqObs bd p U :=
  wilsonAction_gauge_invariant bd g p U

/-- **The plaquette order parameter of any `SU(N)` Wilson system has expectation in `[0,2]`** — the mean
plaquette energy is a well-defined, bounded, gauge-invariant number for every genuine Wilson theory. -/
theorem wilsonSystem_expect_plaqObs_mem {N : ℕ} (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) (β : ℝ) (p : Pq) :
    0 ≤ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonPlaqObs bd p)
      ∧ (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (MassGap.SUN.SU N)) β
        (wilsonPlaqObs bd p) ≤ 2 := by
  refine ⟨wilsonSystem_expect_nonneg hN bd β (wilsonPlaqObs bd p)
    (fun U => wilsonPlaqObs_nonneg hN bd p U), ?_⟩
  have habs := wilsonSystem_expect_abs_le hN bd β (wilsonPlaqObs bd p)
    (measurable_wilsonPlaqObs bd p) 2
    (fun U => abs_le.mpr ⟨by linarith [wilsonPlaqObs_nonneg hN bd p U],
      wilsonPlaqObs_le_two hN bd p U⟩)
  exact (abs_le.mp habs).2

/-! ### The physical order parameter: the plaquette-energy observable -/

/-- The **plaquette-energy observable** `U ↦ φ_W(hol_p U)` — the local Wilson action of plaquette `p`.
The physical order parameter of the theory (its lattice average is the mean plaquette energy). -/
noncomputable def plaqObs (p : Fin 2) : sysReal.Config → ℝ :=
  fun U => wilsonDensity (wilsonHol bd2 p U)

/-- The plaquette-energy observable is nonnegative. -/
theorem plaqObs_nonneg (p : Fin 2) (U : sysReal.Config) : 0 ≤ plaqObs p U :=
  wilsonDensity_nonneg (by norm_num) _

/-- The plaquette-energy observable is at most `2`. -/
theorem plaqObs_le_two (p : Fin 2) (U : sysReal.Config) : plaqObs p U ≤ 2 :=
  wilsonDensity_le_two (by norm_num) _

/-- The plaquette-energy observable is measurable. -/
theorem measurable_plaqObs (p : Fin 2) : Measurable (plaqObs p) :=
  measurable_wilsonDensity.comp (measurable_bd2_hol p)

/-- **The plaquette-energy observable is gauge-invariant** (`φ_W(hol_p (gUg⁻¹)) = φ_W(hol_p U)`) — the
physical order parameter is a genuine gauge-invariant quantity. -/
theorem plaqObs_gauge_invariant (g : G2) (p : Fin 2) (U : sysReal.Config) :
    plaqObs p (confConj G2 g U) = plaqObs p U :=
  wilsonAction_gauge_invariant bd2 g p U

/-- **The plaquette order parameter has a well-defined expectation in `[0,2]`.** The completed state
machinery, applied to the physical observable: `⟨φ_W(hol_p)⟩` exists (`Z>0`), is nonnegative (positivity),
and is bounded by `2` (contractivity), on the genuine SU(2) Wilson measure — the mean plaquette energy is
a well-defined, bounded, gauge-invariant number. -/
theorem expect_plaqObs_mem (β : ℝ) (p : Fin 2) :
    0 ≤ sysReal.expect (probHaar G2) β (plaqObs p)
      ∧ sysReal.expect (probHaar G2) β (plaqObs p) ≤ 2 := by
  refine ⟨sysReal_expect_nonneg β (plaqObs p) (fun U => plaqObs_nonneg p U), ?_⟩
  have habs := sysReal_expect_abs_le β (plaqObs p) (measurable_plaqObs p) 2
    (fun U => abs_le.mpr ⟨by linarith [plaqObs_nonneg p U], plaqObs_le_two p U⟩)
  exact (abs_le.mp habs).2

/-! ### The clustering seed: independence of disjoint plaquette blocks

At `β=0` the Wilson measure is exactly the product Haar measure (`sysReal_expect_at_zero`), under which
the link coordinates of the two disjoint plaquettes are **independent**. This is the probabilistic seed
of clustering — the exponential decay of connected correlations that underlies the mass gap. -/

/-- Block A = the four links of plaquette 0. -/
def blockA : Finset (Fin 8) := {0, 1, 2, 3}
/-- Block B = the four links of plaquette 1. -/
def blockB : Finset (Fin 8) := {4, 5, 6, 7}

theorem blockAB_disjoint : Disjoint blockA blockB := by decide

/-- **Reusable clustering kernel:** for any finite index type and any two disjoint blocks `S, T`, the
coordinate tuples on `S` and on `T` are independent under the product Haar measure on `SU(N)` links. From
`iIndepFun_pi` (coordinates of a product measure are mutually independent) grouped over the disjoint
blocks (`iIndepFun.indepFun_finset`). The general base for any disjoint-support factorization; the
concrete `coords_indep` is its `ι = Fin 8`, `N = 2` instance. -/
theorem coords_indep_SU {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun U (i : S) => (U : ι → MassGap.SUN.SU N) i.val)
      (fun U (i : T) => (U : ι → MassGap.SUN.SU N) i.val)
      (Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))) := by
  have hi : iIndepFun (fun (i : ι) (U : ι → MassGap.SUN.SU N) => U i)
      (Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)

/-- **The link coordinates on the two disjoint plaquette blocks are independent** under the product Haar
measure — the probabilistic seed of clustering (at `β=0` the Wilson measure is exactly this product). The
concrete instance of `coords_indep_SU`. -/
theorem coords_indep :
    IndepFun (fun U (i : blockA) => (U : sysReal.Config) i.val)
      (fun U (i : blockB) => (U : sysReal.Config) i.val)
      (sysReal.vol (probHaar G2)) :=
  coords_indep_SU blockA blockB blockAB_disjoint

/-- **General disjoint-support factorization:** any two observables that read only disjoint link-blocks
`S, T` have a factorizing product-Haar integral, `∫ φ(U|_S)·ψ(U|_T) = (∫φ(U|_S))(∫ψ(U|_T))`. The reusable
form of the β=0 clustering (`expect_plaqObs_factor_at_zero` is the `φ=ψ=φ_W∘hol` instance): the kernel
`coords_indep_SU` composed once with `IndepFun.integral_fun_mul_eq_mul_integral`. -/
theorem block_integral_factor {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (S T : Finset ι) (hST : Disjoint S T)
    (φ : (S → MassGap.SUN.SU N) → ℝ) (ψ : (T → MassGap.SUN.SU N) → ℝ)
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ U, φ (fun i : S => (U : ι → MassGap.SUN.SU N) i.val)
        * ψ (fun i : T => (U : ι → MassGap.SUN.SU N) i.val)
        ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))))
      = (∫ U, φ (fun i : S => (U : ι → MassGap.SUN.SU N) i.val)
          ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))))
        * (∫ U, ψ (fun i : T => (U : ι → MassGap.SUN.SU N) i.val)
          ∂(Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N)))) := by
  have hrS : Measurable (fun U : ι → MassGap.SUN.SU N => fun i : S => U i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hrT : Measurable (fun U : ι → MassGap.SUN.SU N => fun i : T => U i.val) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  exact ((coords_indep_SU S T hST).comp hφ hψ).integral_fun_mul_eq_mul_integral
    (hφ.comp hrS).aestronglyMeasurable (hψ.comp hrT).aestronglyMeasurable

/-- Extend a block-A tuple to a full config (junk `1` outside block A). -/
noncomputable def extendA (v : blockA → G2) : sysReal.Config :=
  fun j => if h : j ∈ blockA then v ⟨j, h⟩ else 1
/-- Extend a block-B tuple to a full config (junk `1` outside block B). -/
noncomputable def extendB (v : blockB → G2) : sysReal.Config :=
  fun j => if h : j ∈ blockB then v ⟨j, h⟩ else 1

theorem measurable_extendA : Measurable extendA := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j ∈ blockA
  · simp only [extendA, dif_pos h]; exact measurable_pi_apply (⟨j, h⟩ : ↥blockA)
  · simp only [extendA, dif_neg h]; exact measurable_const

theorem measurable_extendB : Measurable extendB := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j ∈ blockB
  · simp only [extendB, dif_pos h]; exact measurable_pi_apply (⟨j, h⟩ : ↥blockB)
  · simp only [extendB, dif_neg h]; exact measurable_const

/-- `plaqObs 0` factors through the block-A link restriction: it reads only the four links of plaquette 0.
(The `extendA`-of-restriction round-trip agrees with `U` on block A, and `plaqObs 0` only reads there —
definitionally, since the boundary word `bd2 0` lists exactly links `0,1,2,3`.) -/
theorem plaqObs0_factor :
    plaqObs 0
      = (fun v => plaqObs 0 (extendA v)) ∘ (fun U (i : blockA) => (U : sysReal.Config) i.val) := by
  funext U
  show plaqObs 0 U = plaqObs 0 (extendA (fun i => U i.val))
  rfl

/-- `plaqObs 1` factors through the block-B link restriction (reads only plaquette 1's four links). -/
theorem plaqObs1_factor :
    plaqObs 1
      = (fun v => plaqObs 1 (extendB v)) ∘ (fun U (i : blockB) => (U : sysReal.Config) i.val) := by
  funext U
  show plaqObs 1 U = plaqObs 1 (extendB (fun i => U i.val))
  rfl

/-- **The two plaquette-energy observables are independent** under the product Haar measure: each reads
only its own plaquette's links, and those disjoint blocks are independent (`coords_indep`, composed with
the measurable block-evaluations `plaqObs∘extend`). -/
theorem plaqObs_indep :
    IndepFun (plaqObs 0) (plaqObs 1) (sysReal.vol (probHaar G2)) := by
  rw [plaqObs0_factor, plaqObs1_factor]
  exact coords_indep.comp ((measurable_plaqObs 0).comp measurable_extendA)
    ((measurable_plaqObs 1).comp measurable_extendB)

/-- **β=0 clustering: the two plaquette energies factorize.** At zero coupling the connected correlation
of the two disjoint-plaquette observables vanishes — `⟨φ₀φ₁⟩ = ⟨φ₀⟩⟨φ₁⟩` — because the β=0 Wilson measure
is the product Haar measure and the observables live on independent blocks (`plaqObs_indep`,
`IndepFun.integral_fun_mul_eq_mul_integral`). This exact clustering, made exponential in the separation,
is the mass gap. -/
theorem expect_plaqObs_factor_at_zero :
    sysReal.expect (probHaar G2) 0 (fun U => plaqObs 0 U * plaqObs 1 U)
      = sysReal.expect (probHaar G2) 0 (plaqObs 0) * sysReal.expect (probHaar G2) 0 (plaqObs 1) := by
  rw [sysReal_expect_at_zero, sysReal_expect_at_zero, sysReal_expect_at_zero]
  exact plaqObs_indep.integral_fun_mul_eq_mul_integral
    (measurable_plaqObs 0).aestronglyMeasurable (measurable_plaqObs 1).aestronglyMeasurable

/-- **The Boltzmann weight factorizes over the two disjoint plaquette blocks.** `sysReal`'s two plaquettes
share no links, so `S = φ₀ + φ₁` splits and `e^{-βS} = e^{-βφ₀}·e^{-βφ₁}` — the two plaquettes are
non-interacting (at *every* coupling, not only `β=0`). -/
theorem sysReal_boltz_factor (β : ℝ) (U : sysReal.Config) :
    sysReal.boltz β U = Real.exp (-β * plaqObs 0 U) * Real.exp (-β * plaqObs 1 U) := by
  unfold System.boltz
  rw [← Real.exp_add]
  congr 1
  have hact : sysReal.action U = plaqObs 0 U + plaqObs 1 U := by
    show (∑ p : Fin 2, wilsonDensity (wilsonHol bd2 p U))
        = wilsonDensity (wilsonHol bd2 0 U) + wilsonDensity (wilsonHol bd2 1 U)
    rw [Fin.sum_univ_two]
  rw [hact]; ring

/-- **The partition function factorizes**: `Z = (∫e^{-βφ₀})(∫e^{-βφ₁})` — from the weight factorization
and the block independence (`plaqObs_indep`). The precise machine-checked statement that the toy is
non-interacting; the correlation of the two plaquettes is therefore trivial (factorizing) at all `β`,
which is exactly why nontrivial exponential clustering requires an *interacting* lattice. -/
theorem sysReal_partition_factor (β : ℝ) :
    sysReal.partition (probHaar G2) β
      = (∫ U, Real.exp (-β * plaqObs 0 U) ∂(sysReal.vol (probHaar G2)))
        * (∫ U, Real.exp (-β * plaqObs 1 U) ∂(sysReal.vol (probHaar G2))) := by
  have hg : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hind : IndepFun (fun U => Real.exp (-β * plaqObs 0 U))
      (fun U => Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hg hg
  show (∫ U, sysReal.boltz β U ∂(sysReal.vol (probHaar G2))) = _
  simp_rw [sysReal_boltz_factor β]
  exact hind.integral_fun_mul_eq_mul_integral
    (hg.comp (measurable_plaqObs 0)).aestronglyMeasurable
    (hg.comp (measurable_plaqObs 1)).aestronglyMeasurable

/-- **The two plaquette energies factorize at every coupling: `⟨φ₀φ₁⟩ = ⟨φ₀⟩⟨φ₁⟩` for all `β`.** Because
the plaquettes share no links, the weighted correlation splits (`∫φ₀φ₁e^{-βS} = A₀A₁`, `∫φ₀e^{-βS} = A₀Z₁`,
`∫φ₁e^{-βS} = Z₀A₁`) and, with `Z = Z₀Z₁ > 0`, `⟨φ₀⟩⟨φ₁⟩ = (A₀Z₁)(Z₀A₁)/Z² = A₀A₁/Z = ⟨φ₀φ₁⟩`. The exact
(trivial) clustering of this non-interacting toy at all couplings — the precise statement of what an
interacting lattice must upgrade to *nontrivial, exponential-in-separation* decay to exhibit the gap. -/
theorem expect_plaqObs_factor (β : ℝ) :
    sysReal.expect (probHaar G2) β (fun U => plaqObs 0 U * plaqObs 1 U)
      = sysReal.expect (probHaar G2) β (plaqObs 0) * sysReal.expect (probHaar G2) β (plaqObs 1) := by
  have hE : Measurable (fun x : ℝ => Real.exp (-β * x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hG : Measurable (fun x : ℝ => x * Real.exp (-β * x)) :=
    measurable_id.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have iGG : IndepFun (fun U => plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
      (fun U => plaqObs 1 U * Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hG hG
  have iGE : IndepFun (fun U => plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
      (fun U => Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hG hE
  have iEG : IndepFun (fun U => Real.exp (-β * plaqObs 0 U))
      (fun U => plaqObs 1 U * Real.exp (-β * plaqObs 1 U)) (sysReal.vol (probHaar G2)) :=
    plaqObs_indep.comp hE hG
  set μ := sysReal.vol (probHaar G2) with hμ
  set A0 := ∫ U, plaqObs 0 U * Real.exp (-β * plaqObs 0 U) ∂μ with hA0
  set A1 := ∫ U, plaqObs 1 U * Real.exp (-β * plaqObs 1 U) ∂μ with hA1
  set Z0 := ∫ U, Real.exp (-β * plaqObs 0 U) ∂μ with hZ0
  set Z1 := ∫ U, Real.exp (-β * plaqObs 1 U) ∂μ with hZ1
  have gm0 := (hG.comp (measurable_plaqObs 0)).aestronglyMeasurable (μ := μ)
  have gm1 := (hG.comp (measurable_plaqObs 1)).aestronglyMeasurable (μ := μ)
  have em0 := (hE.comp (measurable_plaqObs 0)).aestronglyMeasurable (μ := μ)
  have em1 := (hE.comp (measurable_plaqObs 1)).aestronglyMeasurable (μ := μ)
  have hc01 : sysReal.corrNum (probHaar G2) β (fun U => plaqObs 0 U * plaqObs 1 U) = A0 * A1 := by
    show (∫ U, (plaqObs 0 U * plaqObs 1 U) * sysReal.boltz β U ∂μ) = A0 * A1
    have h : (fun U => (plaqObs 0 U * plaqObs 1 U) * sysReal.boltz β U)
        = (fun U => (plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
            * (plaqObs 1 U * Real.exp (-β * plaqObs 1 U))) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iGG.integral_fun_mul_eq_mul_integral gm0 gm1
  have hc0 : sysReal.corrNum (probHaar G2) β (plaqObs 0) = A0 * Z1 := by
    show (∫ U, plaqObs 0 U * sysReal.boltz β U ∂μ) = A0 * Z1
    have h : (fun U => plaqObs 0 U * sysReal.boltz β U)
        = (fun U => (plaqObs 0 U * Real.exp (-β * plaqObs 0 U))
            * Real.exp (-β * plaqObs 1 U)) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iGE.integral_fun_mul_eq_mul_integral gm0 em1
  have hc1 : sysReal.corrNum (probHaar G2) β (plaqObs 1) = Z0 * A1 := by
    show (∫ U, plaqObs 1 U * sysReal.boltz β U ∂μ) = Z0 * A1
    have h : (fun U => plaqObs 1 U * sysReal.boltz β U)
        = (fun U => Real.exp (-β * plaqObs 0 U)
            * (plaqObs 1 U * Real.exp (-β * plaqObs 1 U))) := by
      funext U; rw [sysReal_boltz_factor]; ring
    rw [h]; exact iEG.integral_fun_mul_eq_mul_integral em0 gm1
  have hZeq : sysReal.partition (probHaar G2) β = Z0 * Z1 := sysReal_partition_factor β
  have hZne : sysReal.partition (probHaar G2) β ≠ 0 := (sysReal_partition_pos β).ne'
  unfold System.expect
  rw [hc01, hc0, hc1]
  rw [hZeq] at hZne ⊢
  field_simp

/-! ### The interacting frontier: two plaquettes sharing a link

`sysReal`/`sysRing` have non-interacting plaquettes (disjoint link sets), so their clustering is trivial
(exact factorization at all `β`, `expect_plaqObs_factor`). Nontrivial exponential clustering — the mass
gap — requires plaquettes that **share links**. Here is the first such object: a genuine two-plaquette
`SU(2)` Wilson system whose plaquettes share link `3`. It is a valid gauge theory (well-defined, gauge-
invariant, by the general lemmas), but its link-blocks **overlap**, so the independence argument behind
`plaqObs_indep`/`expect_plaqObs_factor` does *not* apply — this marks precisely the boundary between the
tractable non-interacting case and the interacting frontier where the quantitative gap lives. -/

/-- Two plaquettes over seven links **sharing link 3**: `U₀U₁U₂⁻¹U₃⁻¹` and `U₃U₄U₅⁻¹U₆⁻¹`. -/
def bdInt (p : Fin 2) : List (Fin 7 × Bool) :=
  if p = 0 then [(0, true), (1, true), (2, false), (3, false)]
  else [(3, true), (4, true), (5, false), (6, false)]

/-- The concrete **interacting** two-plaquette `SU(2)` Wilson system (plaquettes share link 3). -/
noncomputable def sysInt : System G2 := wilsonSystem bdInt wilsonDensity

/-- `sysInt` is a genuine gauge theory: its partition function is strictly positive (well-defined Gibbs
state), by the general `wilsonSystem_partition_pos`. -/
theorem sysInt_partition_pos (β : ℝ) : 0 < sysInt.partition (probHaar G2) β :=
  wilsonSystem_partition_pos (by norm_num) bdInt β

/-- `sysInt` is gauge-invariant, by the general `wilsonSystem_gauge_invariant`. -/
theorem sysInt_gauge_invariant (g : G2) (β : ℝ) (O : sysInt.Config → ℝ) :
    sysInt.expect (probHaar G2) β (fun U => O (confConj G2 g U))
      = sysInt.expect (probHaar G2) β O :=
  wilsonSystem_gauge_invariant bdInt g β O

/-- The link sets of the two interacting plaquettes. -/
def blockIntA : Finset (Fin 7) := {0, 1, 2, 3}
def blockIntB : Finset (Fin 7) := {3, 4, 5, 6}

/-- **The two plaquettes share link 3** — the system is interacting. -/
theorem sysInt_shares_link : (3 : Fin 7) ∈ blockIntA ∧ (3 : Fin 7) ∈ blockIntB := by decide

/-- **The interacting blocks are NOT disjoint** (they share link 3), so the coordinate-independence
argument (`coords_indep`, which required `Disjoint`) does not apply — the honest boundary where nontrivial
clustering becomes possible. -/
theorem blockInt_not_disjoint : ¬ Disjoint blockIntA blockIntB := by decide

#print axioms hbd2
#print axioms sysReal_invariant
#print axioms wilsonAction_gauge_invariant
#print axioms sysReal_gauge_invariant
#print axioms wilsonSystem_gauge_invariant
#print axioms hbd3
#print axioms sysRing_invariant
#print axioms measurable_bd2_hol
#print axioms sysReal_mul_boltz_integrable
#print axioms sysReal_expect_abs_le
#print axioms sysReal_expect_at_zero
#print axioms wilsonSystem_partition_pos
#print axioms wilsonSystem_expect_one
#print axioms wilsonSystem_expect_mono
#print axioms wilsonSystem_expect_abs_le
#print axioms wilsonSystem_expect_at_zero
#print axioms wilsonSystem_expect_plaqObs_mem
#print axioms coords_indep_SU
#print axioms block_integral_factor
#print axioms coords_indep
#print axioms plaqObs_indep
#print axioms expect_plaqObs_factor_at_zero
#print axioms sysReal_partition_factor
#print axioms expect_plaqObs_factor
#print axioms sysInt_partition_pos
#print axioms sysInt_gauge_invariant
#print axioms blockInt_not_disjoint
#print axioms plaqObs_gauge_invariant
#print axioms expect_plaqObs_mem

end MassGap.WilsonReal
