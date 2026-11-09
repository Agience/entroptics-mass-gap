import Mathlib
import MassGap.CentreSectorSeedTwo

/-!
# MassGap.TwistDeficitUnionN — the square root of a twist deficit is subadditive, and the single-plane twists carry the SU(N) flux part

Let `G` be a finite abelian group acting on a probability space by measure-preserving maps
(`FluxSectorFourier.CentreAction`), `a` a bounded symmetric kernel, `c_ψ` the trace of the flux
sector of character `ψ` (`FluxSectorFourier.sectorTrace`), and `deficit g = hs(a) − twist(a, act g)`.

**The twist in the sector basis** (`twist_act_eq_sum`, `twist_act_eq_sum_re`):

    twist(a, act g) = Σ_ψ conj ψ(g) · c_ψ = Σ_ψ c_ψ Re ψ(g).

Row by row, `a(x, act g ·) = Σ_ψ conj ψ(g) e_ψ(x, ·)` (`FluxSectorFourier.sec_act_right`), the
sectors are orthogonal (`integral_sec_mul_conj`), and `∫ |e_ψ(x, y)|² dy` integrates to `c_ψ`.
So `deficit g = Σ_ψ c_ψ (1 − Re ψ(g)) = Σ_ψ c_ψ |1 − ψ(g)|²/2` (`deficit_eq_sum`,
`deficit_eq_sum_sq`), the squared length of the vector `(√(c_ψ/2) |1 − ψ(g)|)_ψ`.

**The square root of the deficit is subadditive** (`sqrt_deficit_add_le`):
`√deficit(g + h) ≤ √deficit(g) + √deficit(h)`, from `|1 − ψ(g)ψ(h)| ≤ |1 − ψ(g)| + |1 − ψ(h)|`
and the triangle inequality in `ℓ²` (`sqrt_sum_sq_le`, Cauchy–Schwarz). The deficit itself is not
subadditive for `Z_N`, `N ≥ 5`: `1 − cos 2θ > 2(1 − cos θ)` for `0 < |θ| < π/2`.

**From the generators to the group** (`deficit_le_of_single`). For `G = V → Z_N`, every `g` is
`Σ_ν g(ν) e_ν` with `e_ν = Pi.single ν 1`, and `g(ν) = k e(1)` with `|k| ≤ ⌊N/2⌋`
(`ZMod.valMinAbs`), the deficit being even (`deficit_neg`). So single-generator deficits at most
`ε` give `deficit g ≤ (|V| ⌊N/2⌋)² ε` for every `g`.

**On the lattice** (`V` the three transverse directions of a slice, `|V| = 3`):
* `twistRatioN_ge_of_single`: single-plane ratios `Z_{e_ν}/Z ≥ 1 − δ` give `Z_g/Z ≥ 1 − 9⌊N/2⌋²δ`
  for every `g ∈ Z_N³`;
* `fluxShareN_le_of_single`: and the flux share, the mean deficit (`fluxShareN_eq_mean`), is at most
  `9⌊N/2⌋²δ`;
* **`fluxPartN_of_planePartN`**: `PlanePartN N (1/(720000 ⌊N/2⌋²)) → FluxPartN N`;
* `planePartN_of_fluxPartN`: `FluxPartN N → PlanePartN N (N³/80000)`, each single deficit being at
  most the sum of all `N³`.

At `N = 2`, `FluxPartN 2 ↔ FluxPart` (`fluxPartN_two_iff`).

DERIVED (module-wide): `2` in `|1 − ψ|²/2` is `|1 − z|² = 2(1 − Re z)` on the unit circle;
`9 = 3²`, `3 = |V|` (`CentreSectorSeed.card_transverse`); `⌊N/2⌋` bounds `|valMinAbs|`
(`ZMod.natAbs_valMinAbs_le`); `720000 = 9 · 80000`, so that `9⌊N/2⌋²δ` meets `FluxPartN`'s
`1/80000`; `N³ = |Z_N³|` (`SliceCentreAction.card_cen`); `1/80000` is `FluxPartN`'s threshold, that of
`FluxShareSquaring.FluxPart`.
-/

noncomputable section

namespace MassGap.TwistDeficitUnionN

open MeasureTheory Filter MassGap.KernelPower MassGap.FluxSectorFourier MassGap.ZeroFluxSector
open scoped ComplexConjugate

/-! ## 1. The twist in the sector basis -/

section Sectors

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

variable (μ) in
/-- **The deficit of the twist by `g`**: `hs(a) − twist(a, act g)`. -/
def deficit (a : X → X → ℝ) (act : G → X → X) (g : G) : ℝ :=
  hs μ a - FluxSectorBound.twist μ a (act g)

variable {act : G → X → X} {a : X → X → ℝ}

/-- One row of the twisted trace in the sector basis. -/
theorem row_twist_eq (ha : Bdd a) (hA : CentreAction μ act) (g : G) (x : X) :
    (((∫ y, a x y * a x (act g y) ∂μ : ℝ)) : ℂ)
      = ∑ ψ, conj (ψ g) * (secDiag μ a act ψ x : ℂ) := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  rw [← integral_complex_ofReal]
  have e : ∀ y, ((a x y * a x (act g y) : ℝ) : ℂ)
      = ∑ φ, ∑ ψ, conj (ψ g) * (sec a act ψ x y * conj (sec a act φ x y)) := by
    intro y
    have h1 : ((a x (act g y) : ℝ) : ℂ) = ∑ ψ, conj (ψ g) * sec a act ψ x y := by
      rw [← sum_sec (a := a) hA x (act g y)]
      exact Finset.sum_congr rfl fun ψ _ => sec_act_right hA ψ g x y
    have h2 : ((a x y : ℝ) : ℂ) = ∑ φ, conj (sec a act φ x y) := by
      rw [← map_sum, sum_sec (a := a) hA x y, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, h2, h1, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun φ _ => Finset.sum_congr rfl fun ψ _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun φ _ => integrable_finsetSum _ fun ψ _ =>
    (int_sec_conj ha hA hC ψ φ x x).const_mul _]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [integral_finsetSum _ fun ψ _ => (int_sec_conj ha hA hC ψ φ x x).const_mul _,
    Finset.sum_eq_single φ (fun ψ _ hψ => by
      rw [integral_const_mul, integral_sec_mul_conj hA hψ x x, mul_zero])
      (fun h => absurd (Finset.mem_univ φ) h),
    integral_const_mul]
  congr 1
  exact gramC_diag φ x

/-- **The twisted trace in the sector basis**: `twist(a, act g) = Σ_ψ conj ψ(g) c_ψ`. -/
theorem twist_act_eq_sum (ha : Bdd a) (hA : CentreAction μ act) (g : G) :
    ((FluxSectorBound.twist μ a (act g) : ℝ) : ℂ)
      = ∑ ψ, conj (ψ g) * (sectorTrace μ a act ψ : ℂ) := by
  obtain ⟨C, -, hC⟩ := exists_bound ha
  unfold FluxSectorBound.twist
  rw [← integral_complex_ofReal]
  simp_rw [row_twist_eq ha hA g]
  rw [integral_finsetSum _ fun ψ _ => ?_]
  · refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  · exact ((int_secDiag ha hA hC ψ).ofReal (𝕜 := ℂ)).const_mul _

/-- **The twisted trace in the sector basis, real form**: `twist(a, act g) = Σ_ψ c_ψ Re ψ(g)`. -/
theorem twist_act_eq_sum_re (ha : Bdd a) (hA : CentreAction μ act) (g : G) :
    FluxSectorBound.twist μ a (act g) = ∑ ψ, sectorTrace μ a act ψ * (ψ g).re := by
  have h := congrArg Complex.re (twist_act_eq_sum ha hA g)
  rw [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Complex.re_mul_ofReal, Complex.conj_re, mul_comm]

/-- On the unit circle, `1 − Re z = |1 − z|²/2`. -/
theorem one_sub_re_eq (ψ : AddChar G ℂ) (g : G) : 1 - (ψ g).re = ‖1 - ψ g‖ ^ 2 / 2 := by
  have h1 : (ψ g).re * (ψ g).re + (ψ g).im * (ψ g).im = 1 := by
    have h := Complex.normSq_eq_norm_sq (ψ g)
    rw [norm_char, Complex.normSq_apply, one_pow] at h
    exact h
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  linear_combination (-1 / 2 : ℝ) * h1

/-- **The deficit in the sector basis**: `deficit g = Σ_ψ c_ψ (1 − Re ψ(g))`. -/
theorem deficit_eq_sum (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (g : G) : deficit μ a act g = ∑ ψ, sectorTrace μ a act ψ * (1 - (ψ g).re) := by
  unfold deficit
  rw [twist_act_eq_sum_re ha hA g, ← sum_sectorTrace ha hsym hA, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  ring

/-- **The deficit is a squared length**: `deficit g = Σ_ψ (√(c_ψ/2) |1 − ψ(g)|)²`. -/
theorem deficit_eq_sum_sq (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (g : G) :
    deficit μ a act g = ∑ ψ, (Real.sqrt (sectorTrace μ a act ψ / 2) * ‖1 - ψ g‖) ^ 2 := by
  rw [deficit_eq_sum ha hsym hA]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [mul_pow, Real.sq_sqrt (div_nonneg (sectorTrace_nonneg ψ) zero_le_two), one_sub_re_eq]
  ring

end Sectors

/-! ## 2. The square root of the deficit is subadditive -/

/-- **The triangle inequality in `ℓ²`**: `r ≤ p + q` pointwise, all nonnegative, gives
`√Σr² ≤ √Σp² + √Σq²`. -/
theorem sqrt_sum_sq_le {ι : Type*} (s : Finset ι) {p q r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i, r i ≤ p i + q i) :
    Real.sqrt (∑ i ∈ s, r i ^ 2)
      ≤ Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2) := by
  have hP := Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ s) => sq_nonneg (p i))
  have hQ := Real.sq_sqrt (Finset.sum_nonneg fun i (_ : i ∈ s) => sq_nonneg (q i))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s p q
  have hpt : ∀ i ∈ s, r i ^ 2 ≤ p i ^ 2 + q i ^ 2 + 2 * (p i * q i) := fun i _ => by
    have := mul_self_le_mul_self (hr i) (h i)
    nlinarith
  have hle : ∑ i ∈ s, r i ^ 2
      ≤ (Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) ^ 2 := by
    calc ∑ i ∈ s, r i ^ 2 ≤ ∑ i ∈ s, (p i ^ 2 + q i ^ 2 + 2 * (p i * q i)) :=
          Finset.sum_le_sum hpt
      _ = ∑ i ∈ s, p i ^ 2 + ∑ i ∈ s, q i ^ 2 + 2 * ∑ i ∈ s, p i * q i := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by nlinarith [hcs, hP, hQ]
  calc Real.sqrt (∑ i ∈ s, r i ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i ∈ s, p i ^ 2) + Real.sqrt (∑ i ∈ s, q i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

section Subadditive

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {act : G → X → X} {a : X → X → ℝ}

/-- **The square root of the twist deficit is subadditive.** -/
theorem sqrt_deficit_add_le (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act)
    (g h : G) :
    Real.sqrt (deficit μ a act (g + h))
      ≤ Real.sqrt (deficit μ a act g) + Real.sqrt (deficit μ a act h) := by
  rw [deficit_eq_sum_sq ha hsym hA, deficit_eq_sum_sq ha hsym hA, deficit_eq_sum_sq ha hsym hA]
  refine sqrt_sum_sq_le _ (fun ψ => by positivity) fun ψ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [AddChar.map_add_eq_mul]
  calc ‖1 - ψ g * ψ h‖ = ‖(1 - ψ g) + ψ g * (1 - ψ h)‖ := by congr 1; ring
    _ ≤ ‖1 - ψ g‖ + ‖ψ g * (1 - ψ h)‖ := norm_add_le _ _
    _ = ‖1 - ψ g‖ + ‖1 - ψ h‖ := by rw [norm_mul, norm_char, one_mul]

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
theorem deficit_zero (hA : CentreAction μ act) : deficit μ a act 0 = 0 := by
  unfold deficit
  rw [act_zero_eq_id hA, FluxShareSquaring.twist_id, sub_self]

omit [Fintype G] [DecidableEq G] in
theorem deficit_nonneg (ha : Bdd a) (hA : CentreAction μ act) (g : G) : 0 ≤ deficit μ a act g :=
  sub_nonneg.mpr (FluxShareSquaring.twist_le_hs ha (hA.mp g))

/-- The deficit is even. -/
theorem deficit_neg (ha : Bdd a) (hsym : ∀ x y, a x y = a y x) (hA : CentreAction μ act) (g : G) :
    deficit μ a act (-g) = deficit μ a act g := by
  rw [deficit_eq_sum ha hsym hA, deficit_eq_sum ha hsym hA]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [AddChar.map_neg_eq_conj, Complex.conj_re]

theorem sqrt_deficit_nsmul_le (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) (g : G) :
    ∀ k : ℕ, Real.sqrt (deficit μ a act (k • g)) ≤ k * Real.sqrt (deficit μ a act g)
  | 0 => by simp [deficit_zero (a := a) hA]
  | k + 1 => by
    rw [succ_nsmul]
    have ih := sqrt_deficit_nsmul_le ha hsym hA g k
    have hadd := sqrt_deficit_add_le ha hsym hA (k • g) g
    push_cast
    linarith

end Subadditive

/-! ## 3. From the generators of `Z_N^V` to the group -/

theorem single_natCast_eq_nsmul {V : Type*} [DecidableEq V] {N : ℕ} (ν : V) (k : ℕ) :
    Pi.single ν (k : ZMod N) = k • (Pi.single ν (1 : ZMod N) : V → ZMod N) := by
  funext j
  by_cases hj : j = ν
  · subst hj
    simp
  · simp [hj]

section Generators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} [NeZero N]
variable {act : (V → ZMod N) → X → X} {a : X → X → ℝ}

/-- One generator times a residue: `√deficit(x e_ν) ≤ ⌊N/2⌋ √deficit(e_ν)`. -/
theorem sqrt_deficit_single_le (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) (ν : V) (x : ZMod N) :
    Real.sqrt (deficit μ a act (Pi.single ν x))
      ≤ ((N / 2 : ℕ) : ℝ) * Real.sqrt (deficit μ a act (Pi.single ν 1)) := by
  have hx : ((x.valMinAbs : ℤ) : ZMod N) = x := ZMod.coe_valMinAbs x
  have hk : x.valMinAbs.natAbs ≤ N / 2 := ZMod.natAbs_valMinAbs_le x
  generalize x.valMinAbs = z at hx hk
  subst hx
  have hb : Real.sqrt (deficit μ a act (Pi.single ν ((z.natAbs : ℕ) : ZMod N)))
      ≤ ((N / 2 : ℕ) : ℝ) * Real.sqrt (deficit μ a act (Pi.single ν 1)) := by
    rw [single_natCast_eq_nsmul]
    refine (sqrt_deficit_nsmul_le ha hsym hA _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Real.sqrt_nonneg _)
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz, Int.cast_natCast]
    exact hb
  · rw [hz, Int.cast_neg, Int.cast_natCast, Pi.single_neg, deficit_neg ha hsym hA]
    exact hb

/-- **Single-generator deficits bound every deficit**: if `deficit(e_ν) ≤ ε` for every
generator, then `deficit(g) ≤ (|V| ⌊N/2⌋)² ε` for every `g`. -/
theorem deficit_le_of_single (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ ν : V, deficit μ a act (Pi.single ν 1) ≤ ε) (g : V → ZMod N) :
    deficit μ a act g ≤ ((Fintype.card V : ℝ) * ((N / 2 : ℕ) : ℝ)) ^ 2 * ε := by
  have hone : ∀ ν (x : ZMod N), Real.sqrt (deficit μ a act (Pi.single ν x))
      ≤ ((N / 2 : ℕ) : ℝ) * Real.sqrt ε := fun ν x =>
    (sqrt_deficit_single_le ha hsym hA ν x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h ν)) (Nat.cast_nonneg _))
  have hsum : Real.sqrt (deficit μ a act g)
      ≤ ∑ ν, Real.sqrt (deficit μ a act (Pi.single ν (g ν))) := by
    have e := Finset.univ_sum_single g
    calc Real.sqrt (deficit μ a act g)
        = Real.sqrt (deficit μ a act (∑ ν, Pi.single ν (g ν))) := by rw [e]
      _ ≤ _ := Finset.le_sum_of_subadditive (fun g => Real.sqrt (deficit μ a act g))
          (by simp [deficit_zero (a := a) hA]) (sqrt_deficit_add_le ha hsym hA) _ _
  have hle : Real.sqrt (deficit μ a act g)
      ≤ (Fintype.card V : ℝ) * ((N / 2 : ℕ) : ℝ) * Real.sqrt ε := by
    calc Real.sqrt (deficit μ a act g)
        ≤ ∑ ν, Real.sqrt (deficit μ a act (Pi.single ν (g ν))) := hsum
      _ ≤ ∑ _ν : V, ((N / 2 : ℕ) : ℝ) * Real.sqrt ε := Finset.sum_le_sum fun ν _ => hone ν (g ν)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  calc deficit μ a act g = Real.sqrt (deficit μ a act g) ^ 2 :=
        (Real.sq_sqrt (deficit_nonneg ha hA g)).symm
    _ ≤ ((Fintype.card V : ℝ) * ((N / 2 : ℕ) : ℝ) * Real.sqrt ε) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hε]

end Generators

/-! ## 4. The lattice: single 't Hooft twists carry the SU(N) flux part -/

section Lattice

open MassGap.CentreSectorSeed (Tr)
open MassGap.CentreSectorSeedN (hSN halfKN fluxShareN twistRatioN bdd_halfKN symm_halfKN
  hs_halfKN_pos fluxShareN_eq_mean)
open MassGap.SliceCentreAction (Cen act centreAction card_cen)

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The single-plane twist part for SU(N)**: eventually in `β`, some power-of-two side has, at
every step of the corner path, every single 't Hooft twist ratio `Z_{e_ν}/Z` at least `1 − δ`,
`e_ν` the generator of `Z_N` in the transverse direction `ν`. -/
def PlanePartN (δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
    1 - δ ≤ twistRatioN N β (2 ^ b) i (Pi.single ν 1)

variable (N) in
/-- **The SU(N) flux part**: eventually in `β`, some power-of-two side has flux share at most
`1/80000` at every step of the corner path. CHOSEN: Inherited `1/80000` from
`CentreSectorSeed.SectorSeedPow`, so that `15 · 5/80000 ≤ 1/1000`, the `RunSeed` threshold; a smaller
value would only make the seed harder to meet. -/
def FluxPartN : Prop :=
  ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧ ∀ i : Fin 4, fluxShareN N β (2 ^ b) i ≤ 1 / 80000

theorem one_sub_twistRatioN {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) :
    1 - twistRatioN N β n i g
      = deficit (hSN N n i) (halfKN N β n i) (act (μ := i) (T := Tr n i) (N := N)) g
        / hs (hSN N n i) (halfKN N β n i) := by
  have hA := hs_halfKN_pos (N := N) hβ n i
  unfold twistRatioN deficit
  rw [sub_div, div_self hA.ne']

/-- **Single-plane ratios bound every twisted ratio**: `Z_{e_ν}/Z ≥ 1 − δ` for the three generators
gives `Z_g/Z ≥ 1 − 9⌊N/2⌋²δ` for every `g ∈ Z_N³`. -/
theorem twistRatioN_ge_of_single {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ ν : {j : Fin 4 // j ≠ i}, 1 - δ ≤ twistRatioN N β n i (Pi.single ν 1)) (g : Cen i N) :
    1 - 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * δ ≤ twistRatioN N β n i g := by
  have hA := hs_halfKN_pos (N := N) hβ n i
  have hsingle : ∀ ν : {j : Fin 4 // j ≠ i},
      deficit (hSN N n i) (halfKN N β n i) (act (μ := i) (T := Tr n i) (N := N)) (Pi.single ν 1)
        ≤ hs (hSN N n i) (halfKN N β n i) * δ := by
    intro ν
    have h1 := h ν
    have h2 := one_sub_twistRatioN (N := N) hβ n i (Pi.single ν 1)
    have h3 : deficit (hSN N n i) (halfKN N β n i) (act (μ := i) (T := Tr n i) (N := N))
        (Pi.single ν 1) / hs (hSN N n i) (halfKN N β n i) ≤ δ := by linarith
    rw [div_le_iff₀ hA] at h3
    linarith
  have hg := deficit_le_of_single (bdd_halfKN hβ n i) (symm_halfKN hβ n i) centreAction
    (mul_nonneg hA.le hδ) hsingle g
  rw [CentreSectorSeed.card_transverse] at hg
  have h2 := one_sub_twistRatioN (N := N) hβ n i g
  have h3 : deficit (hSN N n i) (halfKN N β n i) (act (μ := i) (T := Tr n i) (N := N)) g
      / hs (hSN N n i) (halfKN N β n i) ≤ 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * δ := by
    rw [div_le_iff₀ hA]
    refine hg.trans (le_of_eq ?_)
    push_cast
    ring
  linarith

/-- **Single-plane ratios bound the flux share**: `fluxShareN ≤ 9⌊N/2⌋²δ`. -/
theorem fluxShareN_le_of_single {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ ν : {j : Fin 4 // j ≠ i}, 1 - δ ≤ twistRatioN N β n i (Pi.single ν 1)) :
    fluxShareN N β n i ≤ 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * δ := by
  rw [fluxShareN_eq_mean hβ n i]
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  have hsum : ∑ _g : Cen i N, (1 - 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * δ)
      ≤ ∑ g, twistRatioN N β n i g :=
    Finset.sum_le_sum fun g _ => twistRatioN_ge_of_single hβ n i hδ h g
  rw [Finset.sum_const, Finset.card_univ, card_cen, nsmul_eq_mul, Nat.cast_pow] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN3.le)
  rw [← mul_assoc, inv_mul_cancel₀ hN3.ne', one_mul] at hm
  linarith

/-- **The single-plane twists carry the SU(N) flux part.** -/
theorem fluxPartN_of_planePartN (h : PlanePartN N (1 / (720000 * ((N / 2 : ℕ) : ℝ) ^ 2))) :
    FluxPartN N := by
  have hc : 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (1 / (720000 * ((N / 2 : ℕ) : ℝ) ^ 2)) ≤ 1 / 80000 := by
    rcases Nat.eq_zero_or_pos (N / 2) with h0 | hpos
    · rw [h0]
      norm_num
    · have hm2 : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) ^ 2 := by
        have : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := Nat.cast_pos.mpr hpos
        positivity
      calc 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (1 / (720000 * ((N / 2 : ℕ) : ℝ) ^ 2))
          = 9 / 720000 * (((N / 2 : ℕ) : ℝ) ^ 2 / ((N / 2 : ℕ) : ℝ) ^ 2) := by ring
        _ = 1 / 80000 := by rw [div_self hm2.ne']; norm_num
        _ ≤ 1 / 80000 := le_rfl
  have hδ : (0 : ℝ) ≤ 1 / (720000 * ((N / 2 : ℕ) : ℝ) ^ 2) := by positivity
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hp⟩ hβ
  exact ⟨b, hb, fun i => (fluxShareN_le_of_single hβ _ i hδ (hp i)).trans hc⟩

/-- **The SU(N) flux part gives the single-plane twist part**: each single deficit is at most the
sum of all `N³`, which is `N³` times the flux share. -/
theorem planePartN_of_fluxPartN (h : FluxPartN N) : PlanePartN N ((N : ℝ) ^ 3 / 80000) := by
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β ⟨b, hb, hf⟩ hβ
  refine ⟨b, hb, fun i ν => ?_⟩
  have hA := hs_halfKN_pos (N := N) hβ (2 ^ b) i
  have hle : ∀ g : Cen i N, 0 ≤ 1 - twistRatioN N β (2 ^ b) i g := fun g => by
    rw [one_sub_twistRatioN hβ]
    exact div_nonneg (deficit_nonneg (bdd_halfKN hβ _ i) centreAction g) hA.le
  have hsum : 1 - twistRatioN N β (2 ^ b) i (Pi.single ν 1)
      ≤ ∑ g : Cen i N, (1 - twistRatioN N β (2 ^ b) i g) :=
    Finset.single_le_sum (f := fun g => 1 - twistRatioN N β (2 ^ b) i g) (fun g _ => hle g)
      (Finset.mem_univ _)
  have hsum2 : ∑ g : Cen i N, (1 - twistRatioN N β (2 ^ b) i g)
      = (N : ℝ) ^ 3 - ∑ g, twistRatioN N β (2 ^ b) i g := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_cen, nsmul_eq_mul,
      mul_one, Nat.cast_pow]
  have hS : ∑ g, twistRatioN N β (2 ^ b) i g
      = (N : ℝ) ^ 3 * (1 - fluxShareN N β (2 ^ b) i) := by
    rw [fluxShareN_eq_mean hβ (2 ^ b) i, sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hN3.ne',
      one_mul]
  have hfm := mul_le_mul_of_nonneg_left (hf i) hN3.le
  rw [hsum2, hS] at hsum
  have e : (N : ℝ) ^ 3 / 80000 = (N : ℝ) ^ 3 * (1 / 80000) := by ring
  rw [e]
  nlinarith

theorem fluxPartN_of_sectorSeedPowN (h : CentreSectorSeedN.SectorSeedPowN N) : FluxPartN N := by
  filter_upwards [h] with β ⟨b, hb, hs⟩
  exact ⟨b, hb, fun i => (hs i).1⟩

/-- **At `N = 2` the flux part is the SU(2) one.** -/
theorem fluxPartN_two_iff : FluxPartN 2 ↔ FluxShareSquaring.FluxPart := by
  unfold FluxPartN FluxShareSquaring.FluxPart
  simp only [CentreSectorSeedTwo.fluxShareN_two]

end Lattice

end MassGap.TwistDeficitUnionN

end

#print axioms MassGap.TwistDeficitUnionN.twist_act_eq_sum
#print axioms MassGap.TwistDeficitUnionN.twist_act_eq_sum_re
#print axioms MassGap.TwistDeficitUnionN.deficit_eq_sum
#print axioms MassGap.TwistDeficitUnionN.sqrt_deficit_add_le
#print axioms MassGap.TwistDeficitUnionN.deficit_le_of_single
#print axioms MassGap.TwistDeficitUnionN.twistRatioN_ge_of_single
#print axioms MassGap.TwistDeficitUnionN.fluxShareN_le_of_single
#print axioms MassGap.TwistDeficitUnionN.fluxPartN_of_planePartN
#print axioms MassGap.TwistDeficitUnionN.planePartN_of_fluxPartN
#print axioms MassGap.TwistDeficitUnionN.fluxPartN_two_iff
