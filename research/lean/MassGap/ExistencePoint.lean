import Mathlib
import MassGap.ClaySplitThreePoint
import MassGap.ContinuumFlow

noncomputable section

/-!
# MassGap.ExistencePoint — E from bounded point readings, and (N₃) in unit-strength form

`ContinuumSep.DiagBoundSep hN ρ 0` (E) asks one eventual bound on `latSkR(θP ∪ P)` for every separated
positive-time monomial `P`: any number of insertions, any local gauge-invariant fields, any bounded test
functions of compact support. This module removes the quantifier over test functions.

* `ptTest y`: the point test function, `1` at `y` and `0` elsewhere. At spacing `a` the point test
  function at a lattice site `a·x` smears to `a⁴ · T_x F` (`smear_ptTest`), so every smeared field is a
  finite combination of point smears with the test function's values as coefficients
  (`smear_eq_sum_pt`).
* `ptMono L y`: the monomial of the fields `L i` at the points `y i`.
* `PointDiagSep hN Z`: for every list of fields `L` and every margin `d > 0` one constant `C` bounds,
  eventually in the step and for every configuration of lattice points `p` that is `d`-separated and
  `d` above the plane, the reflected diagonal of the point monomial by `C · a_k^{8n}`. Each point
  insertion carries the cell volume `a_k⁴` twice (once in `θP`, once in `P`), so this says that the
  normalised point readings `ν_k(θ(∏ Z ôᵢ(xᵢ)) · ∏ Z ôᵢ(xᵢ))` are bounded: the canonical lattice
  Schwinger functions on reflected diagonals of separated points.
* `diagBoundSep_of_pointDiagSep`: at any reflection-compatible `Z`, `PointDiagSep` gives E. The
  smeared monomial is a combination of point monomials over the tuples of sites in its support; the
  reflection form's Cauchy–Schwarz over a finite sum (`form_finset_sum_le`) bounds its diagonal by the
  number of tuples times the sum of the point diagonals, and the number of tuples times `a^{4n}` is
  at most `∏ (2Rᵢ + 3)⁴` at `a ≤ 1`.
* `clay_of_splitThreePoint_point`: `ClaySplitThreePoint.clay_of_splitThreePoint` with E replaced by
  `PointDiagSep` at `zCan`.
* `SplitRatio`, `splitThreePoint_iff_splitRatio`: (N₃) is the same statement as a lower bound
  `c · refReading_k³ ≤ κ_k²` on the unit-strength split three-point reading, with no normalisation.

Scope. `PointDiagSep` is sufficient for E, not equivalent to it: a fixed test function averages the
points, and E alone gives the point readings only up to the cell volume. It holds for the massive free
field and fails for a lattice family whose short-distance exponent drifts with the step (the
generalised free field with Källén–Lehmann weight `μ^{γ_k}` on `[m, 1/a_k]`, `γ_k → ∞`, which is
reflection positive and has gap `m`); that family also fails E. `SplitRatio` holds for the Wick square
of a free massive field, fails for every Gaussian law and at `β = 0`, so it is not Clay
non-triviality.
-/

namespace MassGap.ExistencePoint

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Point test functions -/

/-- **The point test function at `y`**: `1` at `y`, `0` elsewhere. -/
def ptTest (y : Fin 4 → ℝ) : TestFn :=
  ⟨fun z => if z = y then 1 else 0, ∑ i, |y i|, 1,
    Finset.sum_nonneg (fun i _ => abs_nonneg (y i)),
    fun z => by
      by_cases h : z = y
      · simp [h]
      · simp [h],
    fun z hz i => by
      have hzy : z = y := by
        by_contra h
        exact hz (by simp [h])
      rw [hzy]
      exact Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg (y j))
        (Finset.mem_univ i)⟩

theorem ptTest_apply_self (y : Fin 4 → ℝ) : (ptTest y).1 y = 1 := by
  simp [ptTest]

theorem eq_of_ptTest_ne {y z : Fin 4 → ℝ} (h : (ptTest y).1 z ≠ 0) : z = y := by
  by_contra hzy
  exact h (by simp [ptTest, hzy])

theorem site_injective {a : ℝ} (ha : 0 < a) {x x' : ISite} (h : site a x' = site a x) : x' = x := by
  funext i
  have h1 := congrFun h i
  simp only [site] at h1
  have h2 : ((x' i : ℤ) : ℝ) = x i := mul_left_cancel₀ ha.ne' h1
  exact_mod_cast h2

/-- **A point test function at a lattice site smears to one translate**: `a⁴ · T_x F`. -/
theorem smear_ptTest {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (x : ISite) :
    smear a F (ptTest (site a x)) = a ^ 4 • transObs x F := by
  obtain ⟨R, M, hf⟩ := (ptTest (site a x)).2
  rw [smear_eq_sum ha F _ hf (Finset.Subset.refl _)]
  have hx : x ∈ box ⌈R / a⌉₊ :=
    mem_box_of_ne ha hf x (by rw [ptTest_apply_self]; exact one_ne_zero)
  rw [Finset.sum_eq_single x (fun x' _ hne => ?_) (fun hn => absurd hx hn), ptTest_apply_self,
    mul_one]
  have hz : (ptTest (site a x)).1 (site a x') = 0 := by
    by_contra h0
    exact hne (site_injective ha (eq_of_ptTest_ne h0))
  rw [hz, mul_zero, zero_smul]

/-- **A smeared field is the combination of point smears** with the test function's values at the
lattice sites as coefficients. -/
theorem smear_eq_sum_pt {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (f : TestFn) {R M : ℝ}
    (hf : IsTest f.1 R M) :
    smear a F f = ∑ x ∈ box ⌈R / a⌉₊, f.1 (site a x) • smear a F (ptTest (site a x)) := by
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smear_ptTest ha, smul_smul, mul_comm]

/-- The monomial of the fields `L i` at the points `y i`. -/
def ptMono {n : ℕ} (L : Fin n → LField (MassGap.SUN.SU N)) (y : Fin n → (Fin 4 → ℝ)) : Mono N :=
  ⟨n, fun i => (L i, ptTest (y i))⟩

/-! ## 2. The point statement -/

/-- **Bounded canonical point readings on reflected diagonals.** For every list of fields `L` and
every margin `d > 0` there is one `C` such that, eventually in the step, every configuration of
lattice points `p` whose physical points `a_k p_i` are `d` above the plane and pairwise `d`-separated
has reflected diagonal at most `C · a_k^{8n}`: the cell volume `a_k⁴` of each of the `2n` point
insertions, times a bounded normalised point reading.

DERIVED: `8 n = 4 · 2n`, the cell volume `a_k⁴` (`4` the dimension) of each of the `2n` insertions of the
reflected diagonal; `0` the plane's height. -/
def PointDiagSepAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → ∃ C : ℝ, ∀ᶠ k in atTop,
    ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      latSkRAlong hN βs (Renorm.connectedAlong hN βs Z) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n)

/-- `PointDiagSep` at the couplings `dyBeta`: `PointDiagSepAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def PointDiagSep (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : Prop :=
  PointDiagSepAlong hN (dyBeta (one_le_of_ne_zero hN)) Z


/-- **Cauchy–Schwarz over a finite sum** in a reflection form: `⟨∑ yᵢ, ∑ yᵢ⟩ ≤ |s| ∑ ⟨yᵢ, yᵢ⟩`. -/
theorem form_finset_sum_le {A α : Type*} [AddCommGroup A] [Module ℝ A] (P : Transfer.ReflForm A)
    (s : Finset α) (y : α → A) :
    P.form (∑ i ∈ s, y i) (∑ i ∈ s, y i) ≤ s.card * ∑ i ∈ s, P.form (y i) (y i) := by
  have hL : ∀ z, P.form (∑ i ∈ s, y i) z = ∑ i ∈ s, P.form (y i) z := fun z =>
    map_sum (AddMonoidHom.mk' (fun x => P.form x z) (fun a b => P.form_add_left a b z)) y s
  have hR : ∀ x, P.form x (∑ i ∈ s, y i) = ∑ i ∈ s, P.form x (y i) := fun x =>
    map_sum (AddMonoidHom.mk' (fun z => P.form x z)
      (fun a b => P.toPreForm.form_add_right x a b)) y s
  have hpair : ∀ i j, 2 * P.form (y i) (y j) ≤ P.form (y i) (y i) + P.form (y j) (y j) := by
    intro i j
    have h := P.form_nonneg (y i + (-1 : ℝ) • y j)
    simp only [P.toPreForm.form_add_self, P.toPreForm.form_smul_right, P.form_smul_left] at h
    nlinarith
  calc P.form (∑ i ∈ s, y i) (∑ i ∈ s, y i) = ∑ i ∈ s, ∑ j ∈ s, P.form (y i) (y j) := by
        rw [hL]; exact Finset.sum_congr rfl (fun i _ => hR (y i))
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (P.form (y i) (y i) + P.form (y j) (y j)) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by linarith [hpair i j]))
    _ = s.card * ∑ i ∈ s, P.form (y i) (y i) := by
        have e : ∀ i, ∑ j ∈ s, (P.form (y i) (y i) + P.form (y j) (y j)) / 2
            = ((s.card : ℝ) * P.form (y i) (y i) + ∑ j ∈ s, P.form (y j) (y j)) / 2 := by
          intro i
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring

/-- `a (2⌈R/a⌉ + 1) ≤ 2R + 3` at `0 < a ≤ 1`. -/
theorem mul_box_side_le {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 ≤ R) :
    a * (2 * (⌈R / a⌉₊ : ℝ) + 1) ≤ 2 * R + 3 := by
  have hK : (⌈R / a⌉₊ : ℝ) < R / a + 1 := Nat.ceil_lt_add_one (div_nonneg hR ha.le)
  have hK2 : ((⌈R / a⌉₊ : ℝ) - 1) * a < R := by
    have h1 : (⌈R / a⌉₊ : ℝ) - 1 < R / a := by linarith
    exact (lt_div_iff₀ ha).mp h1
  nlinarith

/-- **E from bounded point readings.** At any reflection-compatible field-strength factor `Z`,
`PointDiagSep` gives `DiagBoundSep`. -/
theorem diagBoundSep_of_pointDiagSep_along (hN : N ≠ 0) (βs : ℕ → ℝ) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O) (hP : PointDiagSepAlong hN βs Z) :
    ContinuumSep.DiagBoundSepAlong hN βs (Renorm.connectedAlong hN βs Z) 0 := by
  classical
  intro P
  have hR : (Renorm.connectedAlong hN βs Z).ReflCompat 0 := Renorm.connectedAlong_reflCompat hN βs Z 0 hZ
  obtain ⟨d, hd, hsep⟩ := P.2
  obtain ⟨C, hC⟩ := hP P.1.1 (fun i => (P.1.2 i).1) d hd
  choose R M hRM using fun i => (P.1.2 i).2.2
  choose S hS using fun i => (P.1.2 i).1.2.1
  choose D hD using fun i => exists_depth 0 (S i)
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hRM i).M_nonneg
  have hR0 : ∀ i, 0 ≤ R i := fun i => (hRM i).1
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * (∏ i, M i * (2 * R i + 3) ^ 4) ^ 2, ?_⟩
  have ha1 : ∀ᶠ k in atTop, dySpacing N k < 1 :=
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)
  have haD : ∀ᶠ k in atTop, ∀ i, dySpacing N k * (D i : ℝ) < d := by
    refine Filter.eventually_all.mpr (fun i => ?_)
    have ht : Tendsto (fun k => dySpacing N k * (D i : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_dySpacing N).mul_const (D i : ℝ)
    exact ht.eventually (gt_mem_nhds hd)
  filter_upwards [hC, ha1, haD] with k hk hk1 hkD
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  set a := dySpacing N k with ha_def
  set ρ := Renorm.connectedAlong hN βs Z with hρ
  -- the support boxes, the admissible tuples, their coefficients and point monomials
  let B : Fin P.1.1 → Finset ISite := fun i => box ⌈R i / a⌉₊
  let S' : Finset (Fin P.1.1 → ISite) :=
    (Fintype.piFinset B).filter (fun p => ∀ i, (P.1.2 i).2.1 (site a (p i)) ≠ 0)
  let Q : (Fin P.1.1 → ISite) → Mono N :=
    fun p => ptMono (fun i => (P.1.2 i).1) (fun i => site a (p i))
  -- the expansion of the smeared monomial over point monomials
  have hprod : prodSmear a (ρ.mono k P.1)
      = ∑ p ∈ Fintype.piFinset B,
          (∏ i, (P.1.2 i).2.1 (site a (p i))) • prodSmear a (ρ.mono k (Q p)) := by
    show (∏ i, smear a (((P.1.2 i).1.sub (ρ.c k (P.1.2 i).1)).1) (P.1.2 i).2)
      = ∑ p ∈ Fintype.piFinset B, (∏ i, (P.1.2 i).2.1 (site a (p i))) •
          ∏ i, smear a (((P.1.2 i).1.sub (ρ.c k (P.1.2 i).1)).1) (ptTest (site a (p i)))
    rw [Finset.prod_congr rfl (fun i _ => smear_eq_sum_pt ha _ (P.1.2 i).2 (hRM i)),
      Finset.prod_univ_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact ContinuumFlow.prod_smul_eq _ _ _
  have hfilt : ∑ p ∈ Fintype.piFinset B,
        (∏ i, (P.1.2 i).2.1 (site a (p i))) • prodSmear a (ρ.mono k (Q p))
      = ∑ p ∈ S', (∏ i, (P.1.2 i).2.1 (site a (p i))) • prodSmear a (ρ.mono k (Q p)) := by
    refine (Finset.sum_filter_of_ne (fun p _ hne i hzero => hne ?_)).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, zero_smul]
  have hexp : Yv ρ k P.1
      = ∑ p ∈ S', (∏ i, (P.1.2 i).2.1 (site a (p i))) • Yv ρ k (Q p) := by
    unfold Yv
    rw [hprod, hfilt, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_comm]
    rfl
  -- every admissible point monomial is separated and lies in the half-space algebra
  have hsepQ : ∀ p ∈ S', ContinuumSep.sepPos 0 d (Q p) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    refine ⟨fun i y hy => ?_, fun i j hij y z hy hz => ?_⟩
    · rw [eq_of_ptTest_ne (y := site a (p i)) hy]
      exact hsep.1 i _ (hp' i)
    · rw [eq_of_ptTest_ne (y := site a (p i)) hy, eq_of_ptTest_ne (y := site a (p j)) hz]
      exact hsep.2 i j hij _ _ (hp' i) (hp' j)
  have hmemQ : ∀ p ∈ S', Yv ρ k (Q p)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
    intro p hp
    refine Yv_mem hN ρ 0 k (Q p) (fun i r => ?_)
    exact smear_mem_halfSpaceAlg ha 0 (isLocalOn_sub_const (hS i) r) (hD i) (hkD i).le
      (ptTest (site a (p i))) ((hsepQ p hp).1 i)
  -- the reflection form on the admissible tuples
  let V := GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0
  let y : ↥S' → ↥V := fun p => ⟨Yv ρ k (Q p.1), hmemQ p.1 p.2⟩
  let cf : (Fin P.1.1 → ISite) → ℝ := fun p => ∏ i, (P.1.2 i).2.1 (site a (p i))
  have hsum : ((∑ p : ↥S', cf p.1 • y p : ↥V) : C(Cfg N, ℝ)) = Yv ρ k P.1 := by
    rw [Submodule.coe_sum, hexp, ← Finset.sum_coe_sort S']
    rfl
  have hlat : latSkRAlong hN βs ρ k (pairFam 0 P.1 P.1)
      = (DkAlong hN βs 0 k).form (∑ p : ↥S', cf p.1 • y p) (∑ p : ↥S', cf p.1 • y p) := by
    rw [latSkRAlong_pairFam_eq hN βs ρ 0 hR, DkAlong_form, hsum]
  have hyy : ∀ p : ↥S', (DkAlong hN βs 0 k).form (y p) (y p)
      = latSkRAlong hN βs ρ k (pairFam 0 (Q p.1) (Q p.1)) := by
    intro p
    rw [DkAlong_form, latSkRAlong_pairFam_eq hN βs ρ 0 hR]
  -- the point bound
  have hpt : ∀ p : ↥S', (DkAlong hN βs 0 k).form (y p) (y p) ≤ max C 0 * a ^ (8 * P.1.1) := by
    intro p
    rw [hyy p]
    exact (hk p.1 (hsepQ p.1 p.2)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ha.le _))
  have hcf : ∀ p : Fin P.1.1 → ISite, cf p ^ 2 ≤ (∏ i, M i) ^ 2 := by
    intro p
    have h1 : |cf p| ≤ ∏ i, M i := by
      show |∏ i, (P.1.2 i).2.1 (site a (p i))| ≤ ∏ i, M i
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => (hRM i).2.1 _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hterm : ∀ p : ↥S', (DkAlong hN βs 0 k).form (cf p.1 • y p) (cf p.1 • y p)
      ≤ (∏ i, M i) ^ 2 * (max C 0 * a ^ (8 * P.1.1)) := by
    intro p
    have e : (DkAlong hN βs 0 k).form (cf p.1 • y p) (cf p.1 • y p)
        = cf p.1 ^ 2 * (DkAlong hN βs 0 k).form (y p) (y p) := by
      rw [(DkAlong hN βs 0 k).form_smul_left, (DkAlong hN βs 0 k).toReflForm.toPreForm.form_smul_right]
      ring
    rw [e]
    exact mul_le_mul (hcf p.1) (hpt p) ((DkAlong hN βs 0 k).toReflForm.form_nonneg _) (sq_nonneg _)
  -- counting the tuples
  have hcardN : S'.card ≤ ∏ i, (2 * ⌈R i / a⌉₊ + 1) ^ 4 := by
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl (fun i _ => card_box _)
  have hcardR : (S'.card : ℝ) * a ^ (4 * P.1.1) ≤ ∏ i, (2 * R i + 3) ^ 4 := by
    have h1 : (S'.card : ℝ) ≤ ∏ i, (2 * (⌈R i / a⌉₊ : ℝ) + 1) ^ 4 := by
      exact_mod_cast hcardN
    have h2 : a ^ (4 * P.1.1) = ∏ _i : Fin P.1.1, a ^ 4 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    rw [h2]
    calc (S'.card : ℝ) * ∏ _i : Fin P.1.1, a ^ 4
        ≤ (∏ i, (2 * (⌈R i / a⌉₊ : ℝ) + 1) ^ 4) * ∏ _i : Fin P.1.1, a ^ 4 :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg (fun _ _ => pow_nonneg ha.le 4))
      _ = ∏ i, (a * (2 * (⌈R i / a⌉₊ : ℝ) + 1)) ^ 4 := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl (fun i _ => by ring)
      _ ≤ ∏ i, (2 * R i + 3) ^ 4 :=
          Finset.prod_le_prod (fun i _ => pow_nonneg (mul_nonneg ha.le (by positivity)) 4)
            (fun i _ => pow_le_pow_left₀ (mul_nonneg ha.le (by positivity))
              (mul_box_side_le ha hk1.le (hR0 i)) 4)
  -- assembling
  show latSkRAlong hN βs ρ k (pairFam 0 P.1 P.1) ≤ _
  rw [hlat]
  refine (form_finset_sum_le (DkAlong hN βs 0 k).toReflForm Finset.univ (fun p => cf p.1 • y p)).trans ?_
  have hsumle : ∑ p : ↥S', (DkAlong hN βs 0 k).toReflForm.form (cf p.1 • y p) (cf p.1 • y p)
      ≤ (S'.card : ℝ) * ((∏ i, M i) ^ 2 * (max C 0 * a ^ (8 * P.1.1))) := by
    refine (Finset.sum_le_sum (fun p _ => hterm p)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_coe]
  have h8 : a ^ (8 * P.1.1) = (a ^ (4 * P.1.1)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have hsA : 0 ≤ (S'.card : ℝ) * a ^ (4 * P.1.1) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha.le _)
  have hsq : ((S'.card : ℝ) * a ^ (4 * P.1.1)) ^ 2 ≤ (∏ i, (2 * R i + 3) ^ 4) ^ 2 :=
    pow_le_pow_left₀ hsA hcardR 2
  calc (S'.card : ℝ) * ∑ p : ↥S', (DkAlong hN βs 0 k).toReflForm.form (cf p.1 • y p) (cf p.1 • y p)
      ≤ (S'.card : ℝ) * ((S'.card : ℝ) * ((∏ i, M i) ^ 2 * (max C 0 * a ^ (8 * P.1.1)))) :=
        mul_le_mul_of_nonneg_left hsumle (Nat.cast_nonneg _)
    _ = max C 0 * (∏ i, M i) ^ 2 * ((S'.card : ℝ) * a ^ (4 * P.1.1)) ^ 2 := by
        rw [h8]; ring
    _ ≤ max C 0 * (∏ i, M i) ^ 2 * (∏ i, (2 * R i + 3) ^ 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hC'0 (sq_nonneg _))
    _ = max C 0 * (∏ i, M i * (2 * R i + 3) ^ 4) ^ 2 := by
        rw [Finset.prod_mul_distrib]
        ring

/-- `diagBoundSep_of_pointDiagSep` at the couplings `dyBeta`: `diagBoundSep_of_pointDiagSep_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem diagBoundSep_of_pointDiagSep (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl 0) = Z k O) (hP : PointDiagSep hN Z) :
    ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0 :=
  diagBoundSep_of_pointDiagSep_along hN (dyBeta (one_le_of_ne_zero hN)) Z hZ hP


/-- **The split three-point capstone with E replaced by bounded point readings.** -/
theorem clay_of_splitThreePoint_point (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    (ht : 0 < t) (h3 : ClaySplitThreePoint.SplitThreePoint hN O t ℓ)
    (hPt : PointDiagSep hN (zCan hN O t ℓ)) {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ)
        (ContinuumSep.pairBoundSep_of_diagBoundSep hN (Renorm.connected hN (zCan hN O t ℓ)) 0
          (Renorm.connected_reflCompat hN (zCan hN O t ℓ) 0 (zCan_refl hN O t ℓ))
          (diagBoundSep_of_pointDiagSep hN (zCan hN O t ℓ) (zCan_refl hN O t ℓ) hPt)) (5 * ℓ₀)
      ∧ ∃ (F : Fin 3 → SField N) (d : ℝ), (∀ i, (F i).1 = O) ∧ SepThree d F ∧
          contS hN (Renorm.connected hN (zCan hN O t ℓ)) F ≠ 0 :=
  ClaySplitThreePoint.clay_of_splitThreePoint hN2 hN O ht h3
    (diagBoundSep_of_pointDiagSep hN (zCan hN O t ℓ) (zCan_refl hN O t ℓ) hPt) hℓ hW

/-! ## 3. (N₃) at unit field strength -/

/-- **(N₃) with no normalisation.** Three insertions of `O` split across the plane as `θP ∪ Q`, whose
unit-strength connected reading `κ_k` satisfies `c · refReading_k³ ≤ κ_k²` eventually, at a positive
reference reading.

DERIVED: `3` the insertions of (N₃), the least order at which a connected reading vanishes for a Gaussian
law (`not_splitRatio_of_vanishing`); `3` in `refReading³` and `2` in `κ²` match the insertion count, `2 · 3`
on each side; `0` the plane. -/
def SplitRatioAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∃ (P Q : ContinuumSep.SepMono N 0), P.1.1 + Q.1.1 = 3 ∧
    (∀ x, (pairFam 0 P.1 Q.1 x).1 = O) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k ∧
      c * refReadingAlong hN βs O t ℓ k ^ 3 ≤ (latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1)) ^ 2

/-- `SplitRatio` at the couplings `dyBeta`: `SplitRatioAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def SplitRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  SplitRatioAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ


/-- **`SplitThreePoint` is `SplitRatio`.** -/
theorem splitThreePoint_iff_splitRatio_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ClaySplitThreePoint.SplitThreePointAlong hN βs O t ℓ ↔ SplitRatioAlong hN βs O t ℓ := by
  have key : ∀ (P Q : ContinuumSep.SepMono N 0), P.1.1 + Q.1.1 = 3 →
      ((∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
          c ≤ |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 P.1 Q.1)|) ↔
        (∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k ∧
          c * refReadingAlong hN βs O t ℓ k ^ 3 ≤ (latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1)) ^ 2)) := by
    intro P Q hcard
    have hc' : Fintype.card (Fin P.1.1 ⊕ Fin Q.1.1) = 3 := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      exact hcard
    obtain ⟨e⟩ : Nonempty (Fin 3 ≃ (Fin P.1.1 ⊕ Fin Q.1.1)) :=
      ⟨(Fintype.equivFinOfCardEq hc').symm⟩
    have hz : ∀ k, latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 P.1 Q.1 ∘ e)
        = latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 P.1 Q.1) :=
      fun k => latSkRAlong_comp_equiv hN βs _ k e _
    have h1 : ∀ k, latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1 ∘ e)
        = latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1) :=
      fun k => latSkRAlong_comp_equiv hN βs _ k e _
    have h : (∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
          c ≤ |latSkRAlong hN βs (Renorm.connectedAlong hN βs (zCanAlong hN βs O t ℓ)) k (pairFam 0 P.1 Q.1 ∘ e)|) ↔
        (∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O t ℓ k ∧
          c * refReadingAlong hN βs O t ℓ k ^ 3 ≤ (latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1 ∘ e)) ^ 2) :=
      threePointCanonical_iff_along hN βs O t ℓ (pairFam 0 P.1 Q.1 ∘ e)
    simp only [hz, h1] at h
    exact h
  constructor
  · rintro ⟨P, Q, hcard, hO, hc⟩
    exact ⟨P, Q, hcard, hO, (key P Q hcard).mp hc⟩
  · rintro ⟨P, Q, hcard, hO, hc⟩
    exact ⟨P, Q, hcard, hO, (key P Q hcard).mpr hc⟩

/-- `splitThreePoint_iff_splitRatio` at the couplings `dyBeta`: `splitThreePoint_iff_splitRatio_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem splitThreePoint_iff_splitRatio (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ClaySplitThreePoint.SplitThreePoint hN O t ℓ ↔ SplitRatio hN O t ℓ :=
  splitThreePoint_iff_splitRatio_along hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ


/-- **The control for (N₃).** If every split three-insertion reading vanishes eventually (a Gaussian
law, or independent supports as at `β = 0`), `SplitRatio` fails. -/
theorem not_splitRatio_of_vanishing (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    (h0 : ∀ P Q : ContinuumSep.SepMono N 0, P.1.1 + Q.1.1 = 3 →
      ∀ᶠ k in atTop, latSkR hN (rho1 hN) k (pairFam 0 P.1 Q.1) = 0) :
    ¬ SplitRatio hN O t ℓ := by
  rintro ⟨P, Q, hcard, _, c, hc, hev⟩
  obtain ⟨k, ⟨hr, hle⟩, hk0⟩ := (hev.and (h0 P Q hcard)).exists
  replace hle : c * refReading hN O t ℓ k ^ 3 ≤ (latSkR hN (rho1 hN) k (pairFam 0 P.1 Q.1)) ^ 2 :=
    hle
  rw [hk0] at hle
  have hpos : 0 < c * refReading hN O t ℓ k ^ 3 := mul_pos hc (pow_pos hr 3)
  norm_num at hle
  linarith

end MassGap.ExistencePoint

#print axioms MassGap.ExistencePoint.smear_ptTest
#print axioms MassGap.ExistencePoint.smear_eq_sum_pt
#print axioms MassGap.ExistencePoint.form_finset_sum_le
#print axioms MassGap.ExistencePoint.diagBoundSep_of_pointDiagSep
#print axioms MassGap.ExistencePoint.clay_of_splitThreePoint_point
#print axioms MassGap.ExistencePoint.splitThreePoint_iff_splitRatio
#print axioms MassGap.ExistencePoint.not_splitRatio_of_vanishing
