import Mathlib
import MassGap.CouplingTower
import MassGap.ContactFloor

/-!
# MassGap.WindowRead — the curvature of the window read: action variances and the cross-cut covariance

The window coupling `D(β) = windowCoupling N β w = 16 log ZR(n⁴) − log ZR((2n)⁴)`, `n = 2^w`, is the information
a window of side `n` shares with its neighbours (`ReadSaturates.freeI_XY = −D`). Its first `β`-derivative is the
cut energy `⟨S⟩_{2n} − 16 ⟨S⟩_n` (`CouplingTower.hasDerivAt_windowCoupling`). This module takes the second
derivative, the fluctuation–dissipation step, and reads what a positive window value forces.

* `hasDerivAt_meanAction`, `hasDerivAt_deriv_logZR`: `∂_β ⟨S⟩_L = −Var_L(S)`, so `∂²_β log ZR(L) = Var_L(S)`, the
  variance of the action (`varAction`). The template is the covariance identity
  `WilsonAnalytic.wilsonSystem_expect_hasDerivAt` at `O = S`.
* `hasDerivAt_cutEnergy`, `hasDerivAt_deriv_windowCoupling`: `∂²_β D = 16 Var_n − Var_{2n}`.
* `varAction_eq_sum_cov`: for any labelling `c` of plaquettes, `Var(S) = Σ_b Σ_{b'} Cov(S_b, S_{b'})` with `S_b`
  the action of the plaquettes labelled `b` (`blockAction`).
* `var_double_sub`: at the dyadic labelling of the `2n`-torus into its `16` blocks of side `n` (`dyadicBlock`,
  by the base site of the plaquette),
  `Var_{2n} − 16 Var_n = crossCut + Σ_b (Var_{2n}(S_b) − Var_n)`: the cross-block covariances (`crossCut`) plus
  `blockShift`, which subtracts `Var_n` of the whole `n`-torus from each block's variance inside the
  `2n`-torus. The identity is exact; the second term is not a cross-cut term.
* `meanAction_zero`, `cutEnergy_zero`: at `β = 0`, on a torus with every extent `≥ 2`, every plaquette with two
  different directions has Haar-distributed holonomy (`integral_comp_hol`, the single-link translation of
  `ContactFloor`), the diagonal ones have holonomy `1`, so `⟨S⟩_L = 12 |sites| ⟨φ⟩_Haar` and the cut energy
  vanishes at the ultralocal point for every window `w ≥ 1`.
* `exists_curvature`: for `β > 0` and `w ≥ 1`, some `η ∈ (0, β)` has
  `16 Var_n(η) − Var_{2n}(η) = 2 D(β) / β²` (Taylor at `0` with `D(0) = 0`, `D'(0) = 0`, by Rolle twice).
  `exists_crossCut`: at that `η`, `crossCut + blockShift = −2 D(β)/β²`.

Load tests. At `β = 0`: `cutEnergy_zero`, and the identity of `exists_curvature` is the statement `D(0) = 0`. In
the free (Gaussian) chain, `log Z = −(dof/2) log β + const`, so `β² Var = dof/2` and `β²(16 Var_n − Var_{2n})`
is half the zero-mode count difference: the bound `2 D(β)/β²` is the right shape, `β^{-2}` times a number.

What this does not give, plainly. Along a tower `D(β_k, k) ≈ u₀ > 0` gives
`crossCut + blockShift = −2u₀/β_k² < 0` at some `η_k ∈ (0, β_k)`: a deficit of the doubled torus's action
fluctuation against `16` independent copies. It does not give `ReadPos.ReflFloorAt`:
1. `crossCut` sums all pairs of plaquettes in different blocks, so it is dominated by the pairs at distance
   `1` across the cut faces; nothing here separates pairs at separation `~ 2^k` from those.
2. The sign runs against a reflected floor: reflection positivity makes a reflected self-covariance
   `⟨ΘF·F⟩ − ⟨F⟩²` nonnegative, while the deficit is negative. So the negative part sits in `blockShift`, in
   cross-cut pairs straddling the reflection plane, or in non-mirror block pairs; it is not a positive read.
3. `η_k` is not `β_k`, and the read is on the finite torus `(2^{k+1})⁴`, while `ReflFloorAt` reads the
   infinite-volume `periodicStateG (SU N) β_k` at gap `2m₁`.
The remaining gap is, eventually in `k`: a positive lower bound on a reflected two-point read at separation
`~ 2^k` of the periodic state at `β_k`, as in `ReflFloorAt`; the curvature identity bounds only the total
(short-range dominated, block-shift contaminated) cross-cut covariance at an intermediate coupling.
The Gaussian check and the reflection-positivity sign reasoning above are heuristic arguments, not Lean
statements; nothing in this file proves them.

DERIVED (module-wide): `16 = 2⁴` the blocks of side `n` in the side-`2n` torus; `2` the doubling, the two halves
per direction and the Taylor factor of `t²`; `12 = 4·4 − 4` the ordered pairs of distinct directions; `4` the
dimension; `1` the least window index; `0` the ultralocal coupling and the signs; `2 · |plaquettes|` the action
bound of `WilsonReal.wilsonSystem_action_le`, inherited.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.WindowRead

open MeasureTheory Filter Topology Set
open MassGap MassGap.CompactGauge MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
  MassGap.WilsonReal

variable {N : ℕ}

/-! ## 1. The variance of the action -/

/-- `Cov_L(A, B) = ⟨AB⟩ − ⟨A⟩⟨B⟩` under the Wilson Gibbs measure on the torus `L` at coupling `β`. -/
def gcov (N : ℕ) (L : Fin 4 → ℕ) (β : ℝ) (A B : (RectWilson.sysR L N).Config → ℝ) : ℝ :=
  (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β (fun U => A U * B U)
    - (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β A
      * (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β B

/-- The variance of the Wilson action on the torus `L`. -/
def varAction (N : ℕ) (L : Fin 4 → ℕ) (β : ℝ) : ℝ :=
  gcov N L β (RectWilson.sysR L N).action (RectWilson.sysR L N).action

/-- DERIVED: `2` the plaquette density bound, inherited from `wilsonSystem_action_le`. -/
theorem action_abs_le (hN : N ≠ 0) (L : Fin 4 → ℕ) (U : (RectWilson.sysR L N).Config) :
    |(RectWilson.sysR L N).action U| ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) := by
  have h0 : 0 ≤ (RectWilson.sysR L N).action U := wilsonSystem_action_nonneg hN (RectWilson.rbd L) U
  have h2 : (RectWilson.sysR L N).action U ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) :=
    wilsonSystem_action_le hN (RectWilson.rbd L) U
  exact abs_le.mpr ⟨by linarith, h2⟩

/-- **Fluctuation–dissipation: `∂_β ⟨S⟩_L = −Var_L(S)`.** -/
theorem hasDerivAt_meanAction (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    HasDerivAt (fun x => EffectiveCoupling.meanAction N L x) (-varAction N L β) β :=
  WilsonAnalytic.wilsonSystem_expect_hasDerivAt hN (RectWilson.rbd L) β
    (RectWilson.sysR L N).action (measurable_wilsonSystem_action (N := N) (RectWilson.rbd L))
    (2 * (Fintype.card (RectWilson.RPlaq L) : ℝ)) (action_abs_le hN L)

theorem deriv_logZR (hN : N ≠ 0) (L : Fin 4 → ℕ) :
    deriv (fun x => Real.log (RectWilson.ZR L N x)) = fun x => -EffectiveCoupling.meanAction N L x :=
  funext fun x => (EffectiveCoupling.hasDerivAt_logZR hN L x).deriv

/-- **`∂²_β log ZR(L) = Var_L(S)`.** -/
theorem hasDerivAt_deriv_logZR (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) :
    HasDerivAt (deriv fun x => Real.log (RectWilson.ZR L N x)) (varAction N L β) β := by
  rw [deriv_logZR hN L]
  have h := (hasDerivAt_meanAction hN L β).neg
  rw [neg_neg] at h
  exact h

/-- The cut energy `⟨S⟩_{2n} − 16 ⟨S⟩_n`, `n = 2^w`: the `β`-derivative of the window coupling.
DERIVED: `16 = 2⁴`, `2` the doubling. -/
def cutEnergy (N : ℕ) (β : ℝ) (w : ℕ) : ℝ :=
  EffectiveCoupling.meanAction N (fun _ => 2 * 2 ^ w) β - 16 * EffectiveCoupling.meanAction N (fun _ => 2 ^ w) β

theorem deriv_windowCoupling (hN : N ≠ 0) (w : ℕ) :
    deriv (fun x => CouplingTower.windowCoupling N x w) = fun x => cutEnergy N x w :=
  funext fun x => (CouplingTower.hasDerivAt_windowCoupling hN w x).deriv

/-- **`∂_β` of the cut energy is `16 Var_n − Var_{2n}`.** DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem hasDerivAt_cutEnergy (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (fun x => cutEnergy N x w)
      (16 * varAction N (fun _ => 2 ^ w) β - varAction N (fun _ => 2 * 2 ^ w) β) β :=
  ((hasDerivAt_meanAction hN (fun _ => 2 * 2 ^ w) β).sub
    ((hasDerivAt_meanAction hN (fun _ => 2 ^ w) β).const_mul 16)).congr_deriv (by ring)

/-- **`∂²_β D = 16 Var_n − Var_{2n}`.** DERIVED: `16 = 2⁴`, `2` the doubling. -/
theorem hasDerivAt_deriv_windowCoupling (hN : N ≠ 0) (w : ℕ) (β : ℝ) :
    HasDerivAt (deriv fun x => CouplingTower.windowCoupling N x w)
      (16 * varAction N (fun _ => 2 ^ w) β - varAction N (fun _ => 2 * 2 ^ w) β) β := by
  rw [deriv_windowCoupling hN w]
  exact hasDerivAt_cutEnergy hN w β

/-! ## 2. The variance as a sum of block covariances -/

/-- Linearity of the Gibbs expectation over a finite sum of bounded measurable observables. -/
theorem expect_sum (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) {ι : Type} (s : Finset ι)
    (f : ι → (RectWilson.sysR L N).Config → ℝ) (hm : ∀ i, Measurable (f i)) (M : ι → ℝ)
    (hb : ∀ i U, |f i U| ≤ M i) :
    (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β (fun U => ∑ i ∈ s, f i U)
      = ∑ i ∈ s, (RectWilson.sysR L N).expect (probHaar (SUN.SU N)) β (f i) := by
  have hi : ∀ i ∈ s, Integrable (fun U => f i U * (RectWilson.sysR L N).boltz β U)
      ((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) :=
    fun i _ => wilsonSystem_mul_boltz_integrable hN (RectWilson.rbd L) β (f i) (hm i) (M i) (hb i)
  unfold System.expect System.corrNum
  rw [← Finset.sum_div, ← integral_finsetSum s hi]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show (∑ i ∈ s, f i U) * (RectWilson.sysR L N).boltz β U = ∑ i ∈ s, f i U * (RectWilson.sysR L N).boltz β U
  rw [Finset.sum_mul]

theorem gcov_comm (L : Fin 4 → ℕ) (β : ℝ) (A B : (RectWilson.sysR L N).Config → ℝ) :
    gcov N L β A B = gcov N L β B A := by
  unfold gcov
  rw [show (fun U => A U * B U) = fun U => B U * A U from funext fun U => mul_comm _ _]
  ring

/-- `Cov(Σ_i A_i, B) = Σ_i Cov(A_i, B)` for bounded measurable observables. -/
theorem gcov_sum_left (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) {ι : Type} (s : Finset ι)
    (A : ι → (RectWilson.sysR L N).Config → ℝ) (hA : ∀ i, Measurable (A i)) (MA : ι → ℝ)
    (hAb : ∀ i U, |A i U| ≤ MA i) (B : (RectWilson.sysR L N).Config → ℝ) (hB : Measurable B) (MB : ℝ)
    (hBb : ∀ U, |B U| ≤ MB) :
    gcov N L β (fun U => ∑ i ∈ s, A i U) B = ∑ i ∈ s, gcov N L β (A i) B := by
  have hMB : 0 ≤ MB := le_trans (abs_nonneg _) (hBb (fun _ => 1))
  have e : (fun U => (∑ i ∈ s, A i U) * B U) = fun U => ∑ i ∈ s, A i U * B U :=
    funext fun U => Finset.sum_mul _ _ _
  unfold gcov
  rw [e, expect_sum hN L β s (fun i U => A i U * B U) (fun i => (hA i).mul hB) (fun i => MA i * MB)
      (fun i U => by
        rw [abs_mul]
        exact mul_le_mul (hAb i U) (hBb U) (abs_nonneg _) (le_trans (abs_nonneg _) (hAb i U))),
    expect_sum hN L β s A hA MA hAb, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- `Cov(A, Σ_j B_j) = Σ_j Cov(A, B_j)`. -/
theorem gcov_sum_right (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) {ι : Type} (s : Finset ι)
    (A : (RectWilson.sysR L N).Config → ℝ) (hA : Measurable A) (MA : ℝ) (hAb : ∀ U, |A U| ≤ MA)
    (B : ι → (RectWilson.sysR L N).Config → ℝ) (hB : ∀ j, Measurable (B j)) (MB : ι → ℝ)
    (hBb : ∀ j U, |B j U| ≤ MB j) :
    gcov N L β A (fun U => ∑ j ∈ s, B j U) = ∑ j ∈ s, gcov N L β A (B j) := by
  rw [gcov_comm, gcov_sum_left hN L β s B hB MB hBb A hA MA hAb]
  exact Finset.sum_congr rfl fun j _ => gcov_comm L β _ _

/-- The action of the plaquettes carrying label `b`. -/
def blockAction (L : Fin 4 → ℕ) {ι : Type} [DecidableEq ι] (c : RectWilson.RPlaq L → ι) (b : ι)
    (U : (RectWilson.sysR L N).Config) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => c p = b), wilsonDensity ((RectWilson.sysR L N).hol p U)

theorem measurable_blockAction (L : Fin 4 → ℕ) {ι : Type} [DecidableEq ι] (c : RectWilson.RPlaq L → ι)
    (b : ι) : Measurable (blockAction (N := N) L c b) :=
  Finset.measurable_sum _ fun p _ =>
    measurable_wilsonDensity.comp (measurable_wilsonHol (G := SUN.SU N) (RectWilson.rbd L) p)

theorem action_eq_sum_blockAction (L : Fin 4 → ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : RectWilson.RPlaq L → ι) (U : (RectWilson.sysR L N).Config) :
    (RectWilson.sysR L N).action U = ∑ b, blockAction L c b U := by
  unfold blockAction
  rw [Finset.sum_fiberwise]
  rfl

/-- DERIVED: `2` the plaquette density bound, inherited. -/
theorem blockAction_abs_le (hN : N ≠ 0) (L : Fin 4 → ℕ) {ι : Type} [DecidableEq ι]
    (c : RectWilson.RPlaq L → ι) (b : ι) (U : (RectWilson.sysR L N).Config) :
    |blockAction L c b U| ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) := by
  have h0 : 0 ≤ blockAction L c b U := Finset.sum_nonneg fun p _ => wilsonDensity_nonneg hN _
  have h1 : blockAction L c b U ≤ (RectWilson.sysR L N).action U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => wilsonDensity_nonneg hN _)
  have h2 := action_abs_le hN L U
  rw [abs_of_nonneg h0]
  exact le_trans h1 (le_trans (le_abs_self _) h2)

/-- **The variance of the action is the sum of all block covariances**, for any labelling. -/
theorem varAction_eq_sum_cov (hN : N ≠ 0) (L : Fin 4 → ℕ) (β : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : RectWilson.RPlaq L → ι) :
    varAction N L β = ∑ b, ∑ b', gcov N L β (blockAction L c b) (blockAction L c b') := by
  have hS : (RectWilson.sysR L N).action = fun U => ∑ b, blockAction L c b U :=
    funext (action_eq_sum_blockAction L c)
  have hSb : ∀ U, |∑ b, blockAction (N := N) L c b U| ≤ 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ) :=
    fun U => by rw [← action_eq_sum_blockAction L c U]; exact action_abs_le hN L U
  unfold varAction
  rw [hS, gcov_sum_left hN L β Finset.univ (blockAction L c) (measurable_blockAction L c)
      (fun _ => 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ)) (blockAction_abs_le hN L c)
      _ (Finset.measurable_sum _ fun b _ => measurable_blockAction L c b) _ hSb]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact gcov_sum_right hN L β Finset.univ _ (measurable_blockAction L c b) _ (blockAction_abs_le hN L c b)
    (blockAction L c) (measurable_blockAction L c) (fun _ => 2 * (Fintype.card (RectWilson.RPlaq L) : ℝ))
    (blockAction_abs_le hN L c)

/-- The dyadic block of a plaquette of the `2n`-torus: in each direction, the half of its base site.
DERIVED: `2` the doubling and the two halves; `4` the dimension. -/
def dyadicBlock (n : ℕ) (q : RectWilson.RPlaq (fun _ => 2 * n)) : Fin 4 → Fin 2 :=
  fun μ => if (q.2 μ).val < n then 0 else 1

/-- **The cross-cut covariance**: the covariances between the actions of distinct dyadic blocks of side
`n` inside the `2n`-torus. DERIVED: `2` the doubling. -/
def crossCut (N : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∑ b, ∑ b' ∈ Finset.univ.erase b,
    gcov N (fun _ => 2 * n) β (blockAction (N := N) _ (dyadicBlock n) b)
      (blockAction (N := N) _ (dyadicBlock n) b')

/-- **The block shift**: the change of each block's action variance between its own `n`-torus and its
place in the `2n`-torus. DERIVED: `2` the doubling. -/
def blockShift (N : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∑ b, (gcov N (fun _ => 2 * n) β (blockAction (N := N) _ (dyadicBlock n) b)
      (blockAction (N := N) _ (dyadicBlock n) b) - varAction N (fun _ => n) β)

/-- **`Var_{2n} − 16 Var_n = crossCut + blockShift`.** Exact. DERIVED: `16 = 2⁴` the number of blocks. -/
theorem var_double_sub (hN : N ≠ 0) (β : ℝ) (n : ℕ) :
    varAction N (fun _ => 2 * n) β - 16 * varAction N (fun _ => n) β = crossCut N β n + blockShift N β n := by
  rw [varAction_eq_sum_cov hN (fun _ => 2 * n) β (dyadicBlock n)]
  have hsplit : ∀ b : Fin 4 → Fin 2,
      ∑ b', gcov N (fun _ => 2 * n) β (blockAction (N := N) _ (dyadicBlock n) b)
          (blockAction (N := N) _ (dyadicBlock n) b')
        = gcov N (fun _ => 2 * n) β (blockAction (N := N) _ (dyadicBlock n) b)
            (blockAction (N := N) _ (dyadicBlock n) b)
          + ∑ b' ∈ Finset.univ.erase b, gcov N (fun _ => 2 * n) β
            (blockAction (N := N) _ (dyadicBlock n) b) (blockAction (N := N) _ (dyadicBlock n) b') :=
    fun b => (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
  have hcard : (Finset.univ : Finset (Fin 4 → Fin 2)).card = 16 := by simp
  rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_add_distrib]
  unfold crossCut blockShift
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  ring

/-! ## 3. The ultralocal point: the cut energy vanishes -/

theorem finRotate_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact Equiv.Perm.mem_support.1 (by rw [support_finRotate]; exact Finset.mem_univ i)

/-- A step along an extent `≥ 2` moves every site. DERIVED: `2` the least extent with two sites. -/
theorem rshift_ne (L : Fin 4 → ℕ) {i : Fin 4} (hL : 2 ≤ L i) (x : RectWilson.RSite L) :
    RectWilson.rshift L i x ≠ x := by
  intro h
  have h1 := congrFun h i
  simp only [RectWilson.rshift, Function.update_self] at h1
  exact finRotate_ne hL (x i) h1

/-- **A holonomy right-covariant under one link's translation pushes product Haar to Haar.** The proof of
`ContactFloor.integral_hol_clay`, at an arbitrary finite link set, `SU(N)` and holonomy. -/
theorem integral_comp_hol {Lk : Type} [Fintype Lk] [DecidableEq Lk]
    (hol : (Lk → SUN.SU N) → SUN.SU N) (hcont : Continuous hol) (i₀ : Lk)
    (hcov : ∀ (g : SUN.SU N) (U : Lk → SUN.SU N),
      hol (ContactFloor.linkTranslate (Nc := N) g⁻¹ i₀ U) = hol U * g)
    (f : SUN.SU N → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ g, |f g| ≤ M) :
    (∫ U, f (hol U) ∂(Measure.pi fun _ : Lk => probHaar (SUN.SU N)))
      = ∫ g, f g ∂(probHaar (SUN.SU N)) := by
  set π : Measure (Lk → SUN.SU N) := Measure.pi (fun _ => probHaar (SUN.SU N)) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  have hshift : ∀ g : SUN.SU N, (∫ U, f (hol U * g) ∂π) = ∫ U, f (hol U) ∂π := by
    intro g
    have hstep := ContactFloor.integral_comp_linkTranslate (Nc := N) g⁻¹ i₀ (fun U => f (hol U))
    calc (∫ U, f (hol U * g) ∂π)
        = ∫ U, f (hol (ContactFloor.linkTranslate (Nc := N) g⁻¹ i₀ U)) ∂π := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
          exact congrArg f (hcov g U).symm
      _ = ∫ U, f (hol U) ∂π := hstep
  have hmeas : Measurable (Function.uncurry
      (fun (g : SUN.SU N) (U : Lk → SUN.SU N) => f (hol U * g))) := by
    show Measurable fun z : SUN.SU N × (Lk → SUN.SU N) => f (hol z.2 * z.1)
    exact hf.comp (Continuous.measurable ((hcont.comp continuous_snd).mul continuous_fst))
  have hintg : Integrable (Function.uncurry
      (fun (g : SUN.SU N) (U : Lk → SUN.SU N) => f (hol U * g)))
      ((probHaar (SUN.SU N)).prod π) :=
    ContactFloor.integrable_of_bounded hmeas M (fun z => hb _)
  have hswap := MeasureTheory.integral_integral_swap hintg
  have hinner : ∀ U, (∫ g, f (hol U * g) ∂(probHaar (SUN.SU N)))
      = ∫ g, f g ∂(probHaar (SUN.SU N)) :=
    fun U => MeasureTheory.integral_mul_left_eq_self f (hol U)
  calc (∫ U, f (hol U) ∂π)
      = ∫ _g : SUN.SU N, (∫ U, f (hol U) ∂π) ∂(probHaar (SUN.SU N)) :=
        (ContactFloor.integral_const_prob (probHaar (SUN.SU N)) _).symm
    _ = ∫ g, (∫ U, f (hol U * g) ∂π) ∂(probHaar (SUN.SU N)) := by simp only [hshift]
    _ = ∫ U, (∫ g, f (hol U * g) ∂(probHaar (SUN.SU N))) ∂π := hswap
    _ = ∫ _U, (∫ g, f g ∂(probHaar (SUN.SU N))) ∂π := by simp only [hinner]
    _ = ∫ g, f g ∂(probHaar (SUN.SU N)) := ContactFloor.integral_const_prob π _

/-- Translating the last link `(j, x)` of the plaquette `((i, j), x)` by `g⁻¹` right-multiplies its holonomy
by `g`, when `i ≠ j` and the extent along `i` is `≥ 2`. DERIVED: `2` the least extent with two sites. -/
theorem hol_translate (L : Fin 4 → ℕ) {i j : Fin 4} (hij : i ≠ j) (hL : 2 ≤ L i) (x : RectWilson.RSite L)
    (g : SUN.SU N) (U : RectWilson.RLink L → SUN.SU N) :
    (RectWilson.sysR L N).hol ((i, j), x)
        (ContactFloor.linkTranslate (Nc := N) (Lk := RectWilson.RLink L) g⁻¹ (j, x) U)
      = (RectWilson.sysR L N).hol ((i, j), x) U * g := by
  have h1 : ((i, x) : RectWilson.RLink L) ≠ (j, x) := fun h => hij (congrArg Prod.fst h)
  have h2 : ((j, RectWilson.rshift L i x) : RectWilson.RLink L) ≠ (j, x) :=
    fun h => rshift_ne L hL x (congrArg Prod.snd h)
  have h3 : ((i, RectWilson.rshift L j x) : RectWilson.RLink L) ≠ (j, x) :=
    fun h => hij (congrArg Prod.fst h)
  rw [RectWilson.hol_eq, RectWilson.hol_eq, ContactFloor.linkTranslate_of_ne _ _ _ h1,
    ContactFloor.linkTranslate_of_ne _ _ _ h2, ContactFloor.linkTranslate_of_ne _ _ _ h3,
    ContactFloor.linkTranslate_self]
  group

/-- The Haar mean of the plaquette density. -/
def haarMeanN (N : ℕ) : ℝ := ∫ g, wilsonDensity (N := N) g ∂(probHaar (SUN.SU N))

/-- **The mean action at `β = 0`**: `12 |sites| ⟨φ⟩_Haar` on a torus with every extent `≥ 2`.
DERIVED: `12 = 4·4 − 4` the ordered pairs of distinct directions; `2` the least extent; `0` the coupling. -/
theorem meanAction_zero (hN : N ≠ 0) (L : Fin 4 → ℕ) (hL : ∀ i, 2 ≤ L i) :
    EffectiveCoupling.meanAction N L 0
      = 12 * (Fintype.card (RectWilson.RSite L) : ℝ) * haarMeanN N := by
  haveI : IsProbabilityMeasure ((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure
      (Measure.pi (fun _ : RectWilson.RLink L => probHaar (SUN.SU N))))
  have hb : ∀ U, (RectWilson.sysR L N).boltz 0 U = 1 := fun U => by simp [System.boltz]
  have hZ : (RectWilson.sysR L N).partition (probHaar (SUN.SU N)) 0 = 1 := by
    unfold System.partition
    simp only [hb]
    exact ContactFloor.integral_const_prob _ 1
  have hint : ∀ q : RectWilson.RPlaq L, Integrable (fun U => wilsonDensity ((RectWilson.sysR L N).hol q U))
      ((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) := fun q =>
    ContactFloor.integrable_of_bounded
      (measurable_wilsonDensity.comp (measurable_wilsonHol (G := SUN.SU N) (RectWilson.rbd L) q)) 2
      (fun U => abs_le.mpr ⟨by linarith [wilsonDensity_nonneg hN ((RectWilson.sysR L N).hol q U)],
        wilsonDensity_le_two hN _⟩)
  have hterm : ∀ q : RectWilson.RPlaq L,
      (∫ U, wilsonDensity ((RectWilson.sysR L N).hol q U) ∂((RectWilson.sysR L N).vol (probHaar (SUN.SU N))))
        = if q.1.1 = q.1.2 then 0 else haarMeanN N := by
    rintro ⟨⟨i, j⟩, x⟩
    by_cases hij : i = j
    · subst hij
      have h1 : ∀ U, (RectWilson.sysR L N).hol ((i, i), x) U = 1 := fun U => by
        rw [RectWilson.hol_eq]; group
      simp [h1, wilsonDensity_one hN]
    · rw [if_neg hij]
      exact integral_comp_hol (N := N) (Lk := RectWilson.RLink L)
        (fun (U : RectWilson.RLink L → SUN.SU N) => (RectWilson.sysR L N).hol ((i, j), x) U)
        (PlaqVariance.continuous_wilsonHol (G := SUN.SU N) (RectWilson.rbd L) ((i, j), x)) (j, x)
        (fun g U => hol_translate L hij (hL i) x g U) wilsonDensity measurable_wilsonDensity 2
        (fun g => abs_le.mpr ⟨by linarith [wilsonDensity_nonneg hN g], wilsonDensity_le_two hN g⟩)
  have hcorr : (RectWilson.sysR L N).corrNum (probHaar (SUN.SU N)) 0 (RectWilson.sysR L N).action
      = ∑ q : RectWilson.RPlaq L, (if q.1.1 = q.1.2 then (0 : ℝ) else haarMeanN N) := by
    calc (RectWilson.sysR L N).corrNum (probHaar (SUN.SU N)) 0 (RectWilson.sysR L N).action
        = ∫ U, ∑ q : RectWilson.RPlaq L, wilsonDensity ((RectWilson.sysR L N).hol q U)
            ∂((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) := by
          unfold System.corrNum
          refine integral_congr_ae (Eventually.of_forall fun U => ?_)
          show (RectWilson.sysR L N).action U * (RectWilson.sysR L N).boltz 0 U = _
          rw [hb U, mul_one]
          rfl
      _ = ∑ q : RectWilson.RPlaq L, ∫ U, wilsonDensity ((RectWilson.sysR L N).hol q U)
            ∂((RectWilson.sysR L N).vol (probHaar (SUN.SU N))) :=
          integral_finsetSum _ (fun q _ => hint q)
      _ = _ := Finset.sum_congr rfl (fun q _ => hterm q)
  have hsum : ∑ q : RectWilson.RPlaq L, (if q.1.1 = q.1.2 then (0 : ℝ) else haarMeanN N)
      = 12 * (Fintype.card (RectWilson.RSite L) : ℝ) * haarMeanN N := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp [Fin.sum_univ_four, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  unfold EffectiveCoupling.meanAction System.expect
  rw [hcorr, hZ, div_one, hsum]

/-- **The cut energy vanishes at the ultralocal point**, at every window `w ≥ 1`.
DERIVED: `1` the least window index; `0` the coupling; `16`, `2` the doubling. -/
theorem cutEnergy_zero (hN : N ≠ 0) {w : ℕ} (hw : 1 ≤ w) : cutEnergy N 0 w = 0 := by
  have h2 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  unfold cutEnergy
  rw [meanAction_zero hN (fun _ => 2 * 2 ^ w) (fun _ => by show 2 ≤ 2 * 2 ^ w; omega),
    meanAction_zero hN (fun _ => 2 ^ w) (fun _ => h2)]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  push_cast
  ring

/-! ## 4. The curvature forced by a positive window read -/

/-- **A positive window read forces curvature.** For `β > 0` and `w ≥ 1` some `η ∈ (0, β)` has
`16 Var_n(η) − Var_{2n}(η) = 2 D(β)/β²`, `n = 2^w`, `D = windowCoupling`. Taylor at `0` with `D(0) = 0`
(`windowCoupling_zero`) and `D'(0) = 0` (`cutEnergy_zero`), by Rolle twice.
DERIVED: `2` the Taylor factor of `t²`; `16 = 2⁴`; `1` the least window index; `0` the ultralocal coupling. -/
theorem exists_curvature (hN : N ≠ 0) {w : ℕ} (hw : 1 ≤ w) {β : ℝ} (hβ : 0 < β) :
    ∃ η ∈ Ioo 0 β, 16 * varAction N (fun _ => 2 ^ w) η - varAction N (fun _ => 2 * 2 ^ w) η
      = 2 * CouplingTower.windowCoupling N β w / β ^ 2 := by
  set c : ℝ := CouplingTower.windowCoupling N β w / β ^ 2 with hc
  have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ.ne'
  -- first Rolle: `g = D − t² c`
  have hg : ∀ x, HasDerivAt (fun y => CouplingTower.windowCoupling N y w - y * y * c)
      (cutEnergy N x w - 2 * x * c) x := fun x =>
    ((CouplingTower.hasDerivAt_windowCoupling hN w x).sub
      (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).mul_const c)).congr_deriv
      (by simp only [cutEnergy]; ring)
  have hg0 : (fun y => CouplingTower.windowCoupling N y w - y * y * c) 0
      = (fun y => CouplingTower.windowCoupling N y w - y * y * c) β := by
    simp only [CouplingTower.windowCoupling_zero, hc]
    field_simp
    ring
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hβ
    (fun x _ => (hg x).continuousAt.continuousWithinAt) hg0 (fun x _ => hg x)
  -- second Rolle: `h = D' − 2 t c`
  have hh : ∀ x, HasDerivAt (fun y => cutEnergy N y w - 2 * y * c)
      ((16 * varAction N (fun _ => 2 ^ w) x - varAction N (fun _ => 2 * 2 ^ w) x) - 2 * c) x := fun x =>
    ((hasDerivAt_cutEnergy hN w x).sub (((hasDerivAt_id' x).const_mul 2).mul_const c)).congr_deriv
      (by ring)
  have hh0 : (fun y => cutEnergy N y w - 2 * y * c) 0 = (fun y => cutEnergy N y w - 2 * y * c) ξ := by
    simp only [cutEnergy_zero hN hw]
    rw [hξ0]
    ring
  obtain ⟨η, hη, hη0⟩ := exists_hasDerivAt_eq_zero hξ.1
    (fun x _ => (hh x).continuousAt.continuousWithinAt) hh0 (fun x _ => hh x)
  refine ⟨η, ⟨hη.1, lt_trans hη.2 hξ.2⟩, ?_⟩
  rw [mul_div_assoc, ← hc]
  linarith

/-- **The cross-cut read at window scale.** At the `η` of `exists_curvature`,
`crossCut + blockShift = −2 D(β)/β²` on the `2^{w+1}`-torus with its `16` blocks of side `2^w`.
DERIVED: `2` the Taylor factor and the doubling; `16 = 2⁴`; `1` the least window index. -/
theorem exists_crossCut (hN : N ≠ 0) {w : ℕ} (hw : 1 ≤ w) {β : ℝ} (hβ : 0 < β) :
    ∃ η ∈ Ioo 0 β, crossCut N η (2 ^ w) + blockShift N η (2 ^ w)
      = -(2 * CouplingTower.windowCoupling N β w / β ^ 2) := by
  obtain ⟨η, hη, h⟩ := exists_curvature hN hw hβ
  refine ⟨η, hη, ?_⟩
  rw [← var_double_sub hN η (2 ^ w)]
  linarith

/-- **Along a positive read the cross-cut sum is negative and bounded away from `0` in units of `β⁻²`.**
If `D(β) ≥ u` then at some `η ∈ (0, β)`, `crossCut + blockShift ≤ −2u/β²`, negative when `u > 0`.
DERIVED: `2` the Taylor factor; `1` the least window index; `0` the sign. -/
theorem crossCut_le_of_read (hN : N ≠ 0) {w : ℕ} (hw : 1 ≤ w) {β u : ℝ} (hβ : 0 < β)
    (hu : u ≤ CouplingTower.windowCoupling N β w) :
    ∃ η ∈ Ioo 0 β, crossCut N η (2 ^ w) + blockShift N η (2 ^ w) ≤ -(2 * u / β ^ 2) := by
  obtain ⟨η, hη, h⟩ := exists_crossCut hN hw hβ
  refine ⟨η, hη, ?_⟩
  rw [h, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end MassGap.WindowRead

#print axioms MassGap.WindowRead.action_abs_le
#print axioms MassGap.WindowRead.hasDerivAt_meanAction
#print axioms MassGap.WindowRead.deriv_logZR
#print axioms MassGap.WindowRead.hasDerivAt_deriv_logZR
#print axioms MassGap.WindowRead.deriv_windowCoupling
#print axioms MassGap.WindowRead.hasDerivAt_cutEnergy
#print axioms MassGap.WindowRead.hasDerivAt_deriv_windowCoupling
#print axioms MassGap.WindowRead.expect_sum
#print axioms MassGap.WindowRead.gcov_comm
#print axioms MassGap.WindowRead.gcov_sum_left
#print axioms MassGap.WindowRead.gcov_sum_right
#print axioms MassGap.WindowRead.measurable_blockAction
#print axioms MassGap.WindowRead.action_eq_sum_blockAction
#print axioms MassGap.WindowRead.blockAction_abs_le
#print axioms MassGap.WindowRead.varAction_eq_sum_cov
#print axioms MassGap.WindowRead.var_double_sub
#print axioms MassGap.WindowRead.finRotate_ne
#print axioms MassGap.WindowRead.rshift_ne
#print axioms MassGap.WindowRead.integral_comp_hol
#print axioms MassGap.WindowRead.hol_translate
#print axioms MassGap.WindowRead.meanAction_zero
#print axioms MassGap.WindowRead.cutEnergy_zero
#print axioms MassGap.WindowRead.exists_curvature
#print axioms MassGap.WindowRead.exists_crossCut
#print axioms MassGap.WindowRead.crossCut_le_of_read
