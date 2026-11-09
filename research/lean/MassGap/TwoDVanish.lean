import Mathlib
import MassGap.HeatBath
import MassGap.Reflect
import MassGap.MixAnchor

/-!
# MassGap.TwoDVanish — the 2D torus doubling defect vanishes, area-weighted, at every coupling

The decoupled end of the anisotropic route reads only
`n² D₂(n) → 0`, `D₂(n) = 4 log Z₂(n) − log Z₂(2n)`, `Z₂ = TorusDoubling.ZT (SU N) 2 wilsonDensity β`
(`LayerSplit.twoD_vanishes`, consumed by `AnisoTorus.decoupled_vanishes` and
`MixAnchor.weakMixAnchor_of_twoD`). This module proves it for `N ≠ 0`, `β ≥ 0`, with no character expansion.
Declarations are in `MassGap.TwoDVanish`.

## The route: a floor and free links

* `face x U = U₀(x) U₁(x + e₀) U₀(x + e₁)⁻¹ U₁(x)⁻¹`, the `(0,1)` holonomy. The tree counts each face as the
  ordered pairs `(0,1)`, `(1,0)` (holonomy `face⁻¹`, `hol_one_zero`) and the two diagonal pairs (holonomy `1`,
  `φ(1) = 0`), so `boltz_eq`: the Boltzmann weight is `∏ₓ wt(face x U)`, `wt g = e^{−β(φ(g) + φ(g⁻¹))}`.
* `0 ≤ φ ≤ 2` gives the floor `fl = e^{−4β} ≤ wt ≤ 1`; `sw = wt − fl ∈ [0, 1]`, `c = ∫ sw`, `b = c + fl`.
* `exists_free`: a nonempty proper set `S` of faces has a face `f ∈ S` with `f + e₀ ∉ S` or `f + e₁ ∉ S`; else
  `S` is closed under both shifts, which generate the torus (`finRotate` is a cycle). The link shared by `f`
  and that neighbour enters no other face of `S`, at `n ≥ 2`.
* `integral_prod_proper`: for a proper `S`, `∫ ∏_{x ∈ S} s(face x U) = (∫ s)^{|S|}`, for continuous
  `s ∈ [0, 1]`: integrate the free link (`HeatBath.integral_eq_integral_update`) by two-sided and inverse
  invariance of Haar measure, and induct.
* `ZT_eq`: expanding `∏ₓ (sw + fl)` over subsets, every proper subset contributes `c^{|t|} fl^{n² − |t|}`, so
  `Z₂(n) = b^{n²} − c^{n²} + R(n)`, `R(n) = ∫ ∏ₓ sw(face x U) ∈ [0, c^{n² − 1}]` (`R_nonneg`, `R_le`).
* `abs_ratio_sub_one_le`: `|Z₂(n)/b^{n²} − 1| ≤ ((1 + c)/b) q^{n² − 1}`, `q = c/b < 1`.
* `twoD_vanishes`: `n² D₂(n) → 0`; the bulk `b` cancels (`4 n² = (2n)²`) and the remainder is
  `n² q^{n² − 1} → 0`.

Downstream, with no cited input: `layer_vanishes`, `decoupled_vanishes` (`DA N β 0 · → 0`),
`weakMixAnchor` (`AnisoTorus.WeakMixAnchor N β` at `β ≥ 0`) and `strongEnd_of_aniso`: frequently
`AnisoAnalytic N β` gives `CouplingTower.StrongEnd N`.

## What does not follow

`LayerSplit.TwoDCharacter N β` itself (the exact character series with a `CharTail`) is not proved: only its
consumed conclusion is. Nothing here touches `AnisoTorus.AnisoAnalytic N β`, which stays the open input of
`strongEnd_of_aniso`. The floor argument does not separate the groups: it holds for every compact `G` and every
continuous density with `0 ≤ φ ≤ 2` and `φ(1) = 0`, `U(1)` included (the Lean statement is for `SU N`); the non-abelian content stays in `AnisoAnalytic`.
-/

namespace MassGap.TwoDVanish

open MeasureTheory Filter Topology MassGap MassGap.TorusDoubling
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)

variable {N n : ℕ}

/-! ## 1. The torus shifts -/

/-- `finRotate` moves every point once the side is at least `2`. DERIVED: `2` the least side with two
distinct sites. -/
theorem finRotate_ne (hn : 2 ≤ n) (a : Fin n) : finRotate n a ≠ a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro h
  rw [finRotate_apply] at h
  have h1 : (1 : Fin (m + 2)) = 0 := by simpa using congrArg (fun z => z - a) h
  exact absurd (congrArg Fin.val h1) (by simp)

/-- `finRotate` reaches every point from every point. DERIVED: `2` the least side. -/
theorem reach (hn : 2 ≤ n) (a b : Fin n) : ∃ k : ℕ, (finRotate n)^[k] a = b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨k, hk⟩ := (isCycle_finRotate (n := m)).exists_pow_eq (finRotate_ne hn a) (finRotate_ne hn b)
  exact ⟨k, by rw [Equiv.Perm.iterate_eq_pow]; exact hk⟩

theorem tshift_injective (i : Fin 2) : Function.Injective (tshift (d := 2) (n := n) i) := by
  intro x y h
  funext j
  by_cases hj : j = i
  · subst hj
    have := congrFun h j
    simp only [tshift, Function.update_self] at this
    exact (finRotate n).injective this
  · have := congrFun h j
    simpa [tshift, Function.update_of_ne hj] using this

/-- A shift moves every site, at `n ≥ 2`. DERIVED: `2` the least side. -/
theorem tshift_ne (hn : 2 ≤ n) (i : Fin 2) (x : TSite 2 n) : tshift i x ≠ x := by
  intro h
  have := congrFun h i
  simp only [tshift, Function.update_self] at this
  exact finRotate_ne hn _ this

theorem tshift_iter (i : Fin 2) (x : TSite 2 n) (k : ℕ) :
    (tshift i)^[k] x = Function.update x i ((finRotate n)^[k] (x i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [tshift, Function.update_idem]

/-- **A free face**: a nonempty proper set of faces has a face whose `e₀` or `e₁` neighbour is outside it.
DERIVED: `0`, `1` the two directions; `2` the least side. -/
theorem exists_free (hn : 2 ≤ n) {S : Finset (TSite 2 n)} (hne : S.Nonempty) (hS : S ≠ Finset.univ) :
    ∃ f ∈ S, tshift 0 f ∉ S ∨ tshift 1 f ∉ S := by
  by_contra hcon
  push_neg at hcon
  apply hS
  have hstep : ∀ i : Fin 2, ∀ x ∈ S, tshift i x ∈ S := by
    intro i x hx
    fin_cases i
    · exact (hcon x hx).1
    · exact (hcon x hx).2
  have hit : ∀ (i : Fin 2) (k : ℕ), ∀ x ∈ S, (tshift i)^[k] x ∈ S := by
    intro i k
    induction k with
    | zero => intro x hx; exact hx
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hstep i _ (ih x hx)
  obtain ⟨f1, hf1⟩ := hne
  refine Finset.eq_univ_of_forall fun y => ?_
  obtain ⟨k1, hk1⟩ := reach hn (f1 1) (y 1)
  have hz := hit 1 k1 f1 hf1
  rw [tshift_iter] at hz
  obtain ⟨k0, hk0⟩ := reach hn ((Function.update f1 1 ((finRotate n)^[k1] (f1 1))) 0) (y 0)
  have hy := hit 0 k0 _ hz
  rw [tshift_iter] at hy
  have hk0' : (finRotate n)^[k0] (f1 0) = y 0 := by simpa using hk0
  convert hy using 1
  funext j
  fin_cases j
  · simp [hk0']
  · simp [hk1]

/-! ## 2. Faces and the Boltzmann weight -/

/-- The `(0,1)` face holonomy at `x`. DERIVED: `0`, `1` the two directions. -/
def face (x : TSite 2 n) (U : TLink 2 n → SU N) : SU N :=
  U (0, x) * U (1, tshift 0 x) * (U (0, tshift 1 x))⁻¹ * (U (1, x))⁻¹

theorem continuous_face (x : TSite 2 n) : Continuous (face (N := N) x) := by
  unfold face
  have e1 : Continuous fun U : TLink 2 n → SU N => U (0, x) := continuous_apply _
  have e2 : Continuous fun U : TLink 2 n → SU N => U (1, tshift 0 x) := continuous_apply _
  have e3 : Continuous fun U : TLink 2 n → SU N => U (0, tshift 1 x) := continuous_apply _
  have e4 : Continuous fun U : TLink 2 n → SU N => U (1, x) := continuous_apply _
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem hol_zero_one (U : TLink 2 n → SU N) (x : TSite 2 n) :
    (sysT (SU N) 2 n wilsonDensity).hol ((0, 1), x) U = face x U := by
  rw [hol_eq]; rfl

theorem hol_one_zero (U : TLink 2 n → SU N) (x : TSite 2 n) :
    (sysT (SU N) 2 n wilsonDensity).hol ((1, 0), x) U = (face x U)⁻¹ := by
  rw [hol_eq]; unfold face; group

/-- The face weight `e^{−β(φ(g) + φ(g⁻¹))}`: the two ordered plaquettes of one face. -/
noncomputable def wt (β : ℝ) (g : SU N) : ℝ :=
  Real.exp (-β * (wilsonDensity g + wilsonDensity g⁻¹))

/-- **The Boltzmann weight is a product over faces**, at `N ≠ 0` (the diagonal plaquettes read `φ(1) = 0`).
DERIVED: `0` the excluded colour count. -/
theorem boltz_eq (hN : N ≠ 0) (β : ℝ) (U : TLink 2 n → SU N) :
    (sysT (SU N) 2 n wilsonDensity).boltz β U = ∏ x, wt β (face x U) := by
  obtain ⟨F, hF⟩ : ∃ F : TPlaq 2 n → ℝ,
      F = fun p => wilsonDensity ((sysT (SU N) 2 n wilsonDensity).hol p U) := ⟨_, rfl⟩
  have hdiag : ∀ (i : Fin 2) (x : TSite 2 n), F ((i, i), x) = 0 := by
    intro i x; rw [hF]; simp only [hol_diag, WilsonAction.wilsonDensity_one hN]
  have h01 : ∀ x : TSite 2 n, F ((0, 1), x) = wilsonDensity (face x U) := by
    intro x; rw [hF]; simp only [hol_zero_one]
  have h10 : ∀ x : TSite 2 n, F ((1, 0), x) = wilsonDensity (face x U)⁻¹ := by
    intro x; rw [hF]; simp only [hol_one_zero]
  have hact : (sysT (SU N) 2 n wilsonDensity).action U
      = ∑ x, (wilsonDensity (face x U) + wilsonDensity (face x U)⁻¹) := by
    have e : (sysT (SU N) 2 n wilsonDensity).action U = ∑ p, F p := by rw [hF]; rfl
    rw [e, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, hdiag, h01, h10, Finset.sum_const_zero, zero_add, add_zero]
    rw [Finset.sum_add_distrib]
  unfold LatticeGauge.System.boltz
  rw [hact, Finset.mul_sum, Real.exp_sum]
  rfl

/-! ## 3. The floor -/

/-- The floor `e^{−4β}` of the face weight. DERIVED: `4 = 2 + 2`, twice the largest density. -/
noncomputable def fl (β : ℝ) : ℝ := Real.exp (-β * 4)

/-- The face weight above the floor. -/
noncomputable def sw (β : ℝ) (g : SU N) : ℝ := wt β g - fl β

theorem fl_pos (β : ℝ) : 0 < fl β := Real.exp_pos _

theorem continuous_sw (β : ℝ) : Continuous (sw (N := N) β) := by
  unfold sw wt
  refine (Real.continuous_exp.comp (continuous_const.mul ?_)).sub continuous_const
  exact WilsonAction.continuous_wilsonDensity.add
    (WilsonAction.continuous_wilsonDensity.comp continuous_inv)

/-- DERIVED: `0` the sign. -/
theorem sw_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : SU N) : 0 ≤ sw β g := by
  unfold sw wt fl
  rw [sub_nonneg, Real.exp_le_exp]
  have h1 := WilsonAction.wilsonDensity_le_two hN g
  have h2 := WilsonAction.wilsonDensity_le_two hN g⁻¹
  nlinarith

/-- DERIVED: `1` the weight at zero action. -/
theorem sw_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : SU N) : sw β g ≤ 1 := by
  unfold sw
  have h1 := WilsonAction.wilsonDensity_nonneg hN g
  have h2 := WilsonAction.wilsonDensity_nonneg hN g⁻¹
  have : wt β g ≤ 1 := by
    unfold wt
    rw [Real.exp_le_one_iff]
    nlinarith
  linarith [fl_pos β]

/-! ## 4. Integrating a free link -/

/-- Product Haar measure on the links of the side-`n` 2D torus. -/
noncomputable abbrev μL (n N : ℕ) : Measure (TLink 2 n → SU N) :=
  Measure.pi fun _ : TLink 2 n => probHaar (SU N)

theorem integrable_of_continuous {F : (TLink 2 n → SU N) → ℝ} (hF : Continuous F) :
    Integrable F (μL n N) := by
  obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hF
  exact HeatBath.integrable_of_abs_le _ hF.measurable hC

theorem face_update_other {x : TSite 2 n} {ℓ : TLink 2 n} (W : TLink 2 n → SU N) (g : SU N)
    (h1 : ((0 : Fin 2), x) ≠ ℓ) (h2 : ((1 : Fin 2), tshift 0 x) ≠ ℓ)
    (h3 : ((0 : Fin 2), tshift 1 x) ≠ ℓ) (h4 : ((1 : Fin 2), x) ≠ ℓ) :
    face x (Function.update W ℓ g) = face x W := by
  unfold face
  rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4]

theorem pair_ne {a b : TSite 2 n} : ((0 : Fin 2), a) ≠ ((1 : Fin 2), b) := by
  intro h; have h1 := congrArg Prod.fst h; simp at h1

theorem pair_ne' {a b : TSite 2 n} : ((1 : Fin 2), a) ≠ ((0 : Fin 2), b) := fun h => pair_ne h.symm

theorem pair_ne_of {i : Fin 2} {a b : TSite 2 n} (h : a ≠ b) : (i, a) ≠ (i, b) := by
  intro h'; exact h (congrArg Prod.snd h')

/-- The free link of a face read off the `e₀` side. DERIVED: `2` the least side. -/
theorem face_update_e0 (hn : 2 ≤ n) (f : TSite 2 n) (W : TLink 2 n → SU N) (g : SU N) :
    face f (Function.update W (1, tshift 0 f) g)
      = W (0, f) * g * ((W (0, tshift 1 f))⁻¹ * (W (1, f))⁻¹) := by
  unfold face
  rw [Function.update_of_ne pair_ne, Function.update_self, Function.update_of_ne pair_ne,
    Function.update_of_ne (pair_ne_of (tshift_ne hn 0 f).symm)]
  group

/-- The free link of a face read off the `e₁` side. DERIVED: `2` the least side. -/
theorem face_update_e1 (hn : 2 ≤ n) (f : TSite 2 n) (W : TLink 2 n → SU N) (g : SU N) :
    face f (Function.update W (0, tshift 1 f) g)
      = (W (0, f) * W (1, tshift 0 f)) * g⁻¹ * (W (1, f))⁻¹ := by
  unfold face
  rw [Function.update_of_ne (pair_ne_of (tshift_ne hn 1 f).symm), Function.update_of_ne pair_ne',
    Function.update_self, Function.update_of_ne pair_ne']

/-- **Products over a proper set of faces factor**: `∫ ∏_{x ∈ S} s(face x U) = (∫ s)^{|S|}` for `S` proper,
`s` continuous in `[0, 1]`. DERIVED: `0`, `1` the range of `s`; `2` the least side. -/
theorem integral_prod_proper (hn : 2 ≤ n) {s : SU N → ℝ} (hs : Continuous s) (h0 : ∀ g, 0 ≤ s g)
    (h1 : ∀ g, s g ≤ 1) (k : ℕ) :
    ∀ S : Finset (TSite 2 n), S.card = k → S ≠ Finset.univ →
      ∫ U, ∏ x ∈ S, s (face x U) ∂(μL n N) = (∫ g, s g ∂(probHaar (SU N))) ^ k := by
  induction k with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hSu
    have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨f, hf, hfree⟩ := exists_free hn hne hSu
    have hcard : (S.erase f).card = k := by rw [Finset.card_erase_of_mem hf, hS]; rfl
    have hsub : S.erase f ≠ Finset.univ := fun h =>
      Finset.notMem_erase f S (h ▸ Finset.mem_univ f)
    have hIH := ih (S.erase f) hcard hsub
    set c := ∫ g, s g ∂(probHaar (SU N)) with hc
    -- the free link
    obtain ⟨ℓ, hcf, hother⟩ : ∃ ℓ : TLink 2 n,
        (∀ W : TLink 2 n → SU N, ∫ g, s (face f (Function.update W ℓ g)) ∂(probHaar (SU N)) = c) ∧
        (∀ x ∈ S.erase f, ∀ (W : TLink 2 n → SU N) g, face x (Function.update W ℓ g) = face x W) := by
      rcases hfree with h0' | h1'
      · refine ⟨(1, tshift 0 f), fun W => ?_, fun x hx W g => ?_⟩
        · simp_rw [face_update_e0 hn f W]
          exact HeatBath.integral_twoSided s _ _
        · have hxf : x ≠ f := Finset.ne_of_mem_erase hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          refine face_update_other W g pair_ne
            (pair_ne_of fun h => hxf (tshift_injective 0 h)) pair_ne
            (pair_ne_of fun h => h0' (h ▸ hxS))
      · refine ⟨(0, tshift 1 f), fun W => ?_, fun x hx W g => ?_⟩
        · simp_rw [face_update_e1 hn f W]
          have hinv := integral_inv_eq_self
            (fun g => s (W (0, f) * W (1, tshift 0 f) * g * (W (1, f))⁻¹)) (probHaar (SU N))
          exact hinv.trans (HeatBath.integral_twoSided s _ _)
        · have hxf : x ≠ f := Finset.ne_of_mem_erase hx
          have hxS : x ∈ S := Finset.mem_of_mem_erase hx
          refine face_update_other W g (pair_ne_of fun h => h1' (h ▸ hxS)) pair_ne'
            (pair_ne_of fun h => hxf (tshift_injective 1 h)) pair_ne'
    have hF : Continuous fun U : TLink 2 n → SU N => ∏ x ∈ S, s (face x U) :=
      continuous_finsetProd _ fun x _ => hs.comp (continuous_face x)
    have hC : ∀ U : TLink 2 n → SU N, |∏ x ∈ S, s (face x U)| ≤ 1 := by
      intro U
      rw [abs_of_nonneg (Finset.prod_nonneg fun x _ => h0 _)]
      exact Finset.prod_le_one (fun x _ => h0 _) fun x _ => h1 _
    rw [HeatBath.integral_eq_integral_update (probHaar (SU N)) ℓ _ hF.measurable hC]
    have hin : ∀ W : TLink 2 n → SU N,
        ∫ g, ∏ x ∈ S, s (face x (Function.update W ℓ g)) ∂(probHaar (SU N))
          = c * ∏ x ∈ S.erase f, s (face x W) := by
      intro W
      have hsplit : ∀ g, ∏ x ∈ S, s (face x (Function.update W ℓ g))
          = s (face f (Function.update W ℓ g)) * ∏ x ∈ S.erase f, s (face x W) := by
        intro g
        rw [← Finset.mul_prod_erase S _ hf]
        congr 1
        exact Finset.prod_congr rfl fun x hx => by rw [hother x hx W g]
      simp_rw [hsplit]
      rw [integral_mul_const, hcf W]
    simp_rw [hin]
    rw [integral_const_mul, hIH, pow_succ]
    ring

/-! ## 5. The closed form with a remainder -/

/-- `c = ∫ sw`, the mean of the weight above the floor. -/
noncomputable def cm (N : ℕ) (β : ℝ) : ℝ := ∫ g, sw β g ∂(probHaar (SU N))

/-- The full-torus remainder `R(n) = ∫ ∏ₓ sw(face x U)`. -/
noncomputable def R (N : ℕ) (β : ℝ) (n : ℕ) : ℝ := ∫ U, ∏ x, sw β (face x U) ∂(μL n N)

theorem card_site : Fintype.card (TSite 2 n) = n ^ 2 := by simp

/-- **The 2D torus in closed form up to the full-torus remainder**:
`Z₂(n) = (c + fl)^{n²} − c^{n²} + R(n)`. DERIVED: `2` the dimension and the least side. -/
theorem ZT_eq (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) :
    ZT (SU N) 2 wilsonDensity β n = (cm N β + fl β) ^ (n ^ 2) - cm N β ^ (n ^ 2) + R N β n := by
  have hZ : ZT (SU N) 2 wilsonDensity β n
      = ∫ U, ∑ t ∈ (Finset.univ : Finset (TSite 2 n)).powerset,
          (∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ Finset.univ \ t, fl β ∂(μL n N) := by
    have h1 : ZT (SU N) 2 wilsonDensity β n = ∫ U, ∏ x, wt β (face x U) ∂(μL n N) := by
      unfold ZT LatticeGauge.System.partition LatticeGauge.System.vol
      exact integral_congr_ae (Eventually.of_forall fun U => boltz_eq hN β U)
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    dsimp only
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun x _ => by unfold sw; ring
  have hint : ∀ t : Finset (TSite 2 n), Integrable
      (fun U => (∏ x ∈ t, sw β (face x U)) * ∏ _x ∈ Finset.univ \ t, fl β) (μL n N) := fun t =>
    integrable_of_continuous ((continuous_finsetProd _ fun x _ =>
      (continuous_sw β).comp (continuous_face x)).mul continuous_const)
  rw [hZ, integral_finsetSum _ fun t _ => hint t]
  simp_rw [integral_mul_const, Finset.prod_const]
  have hconst : (cm N β + fl β) ^ (n ^ 2) = ∑ t ∈ (Finset.univ : Finset (TSite 2 n)).powerset,
      cm N β ^ t.card * fl β ^ (Finset.univ \ t).card := by
    rw [← card_site, ← Finset.card_univ, ← Finset.prod_const, Finset.prod_add]
    simp only [Finset.prod_const]
  rw [hconst, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self Finset.univ),
    ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self Finset.univ)]
  have hrest : ∀ t ∈ (Finset.univ : Finset (TSite 2 n)).powerset.erase Finset.univ,
      (∫ U, ∏ x ∈ t, sw β (face x U) ∂(μL n N)) * fl β ^ (Finset.univ \ t).card
        = cm N β ^ t.card * fl β ^ (Finset.univ \ t).card := by
    intro t ht
    rw [integral_prod_proper (by omega) (continuous_sw β) (sw_nonneg hN hβ) (sw_le_one hN hβ) t.card t
      rfl (Finset.ne_of_mem_erase ht)]
    rfl
  rw [Finset.sum_congr rfl hrest, Finset.card_univ, card_site, Finset.sdiff_self, Finset.card_empty,
    pow_zero, mul_one, mul_one]
  unfold R
  ring

theorem cm_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ cm N β :=
  integral_nonneg fun g => sw_nonneg hN hβ g

theorem R_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : 0 ≤ R N β n :=
  integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => sw_nonneg hN hβ _

/-- **The remainder drops one face**: `R(n) ≤ c^{n² − 1}`. DERIVED: `1` the dropped face; `2` the least
side. -/
theorem R_le (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) : R N β n ≤ cm N β ^ (n ^ 2 - 1) := by
  let x0 : TSite 2 n := fun _ => ⟨0, by omega⟩
  have hcont : ∀ t : Finset (TSite 2 n), Continuous fun U : TLink 2 n → SU N => ∏ x ∈ t, sw β (face x U) :=
    fun t => continuous_finsetProd _ fun x _ => (continuous_sw β).comp (continuous_face x)
  have hsub : Finset.univ.erase x0 ≠ Finset.univ := fun h =>
    Finset.notMem_erase x0 _ (h ▸ Finset.mem_univ x0)
  have hcard : (Finset.univ.erase x0).card = n ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x0), Finset.card_univ, card_site]
  unfold R
  calc ∫ U, ∏ x, sw β (face x U) ∂(μL n N)
      ≤ ∫ U, ∏ x ∈ Finset.univ.erase x0, sw β (face x U) ∂(μL n N) := by
        refine integral_mono (integrable_of_continuous (hcont _)) (integrable_of_continuous (hcont _))
          fun U => ?_
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x0)]
        exact mul_le_of_le_one_left (Finset.prod_nonneg fun x _ => sw_nonneg hN hβ _)
          (sw_le_one hN hβ _)
    _ = cm N β ^ (n ^ 2 - 1) :=
        integral_prod_proper hn (continuous_sw β) (sw_nonneg hN hβ) (sw_le_one hN hβ) _ _ hcard hsub

/-! ## 6. The ratio to the bulk -/

/-- The bulk `b = c + fl`. -/
noncomputable def bk (N : ℕ) (β : ℝ) : ℝ := cm N β + fl β

theorem bk_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : 0 < bk N β := by
  unfold bk; linarith [cm_nonneg hN hβ, fl_pos β]

theorem ZT_pos (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) :
    0 < ZT (SU N) 2 wilsonDensity β n := by
  rw [ZT_eq hN hn hβ]
  have hc := cm_nonneg hN hβ
  have hlt : cm N β ^ (n ^ 2) < (cm N β + fl β) ^ (n ^ 2) :=
    pow_lt_pow_left₀ (by linarith [fl_pos β]) hc (by positivity)
  linarith [R_nonneg hN hβ n]

/-- **The ratio to the bulk**: `|Z₂(n)/b^{n²} − 1| ≤ ((1 + c)/b) (c/b)^{n² − 1}`. DERIVED: `1` the trivial
ratio and the dropped face; `2` the least side. -/
theorem abs_ratio_sub_one_le (hN : N ≠ 0) (hn : 2 ≤ n) {β : ℝ} (hβ : 0 ≤ β) :
    |ZT (SU N) 2 wilsonDensity β n / bk N β ^ (n ^ 2) - 1|
      ≤ (1 + cm N β) / bk N β * (cm N β / bk N β) ^ (n ^ 2 - 1) := by
  have hb := bk_pos hN hβ
  have hc := cm_nonneg hN hβ
  obtain ⟨j, hj⟩ : ∃ j, n ^ 2 = j + 1 := ⟨n ^ 2 - 1, by have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hR0 := R_nonneg hN hβ (N := N) n
  have hR1 := R_le hN hn hβ (N := N)
  rw [hj, Nat.add_sub_cancel] at hR1 ⊢
  have hZ := ZT_eq hN hn hβ (N := N)
  rw [hj] at hZ
  have hbj : 0 < bk N β ^ (j + 1) := pow_pos hb _
  have hkey : ZT (SU N) 2 wilsonDensity β n / bk N β ^ (j + 1) - 1
      = (R N β n - cm N β ^ (j + 1)) / bk N β ^ (j + 1) := by
    rw [eq_div_iff hbj.ne', sub_mul, div_mul_cancel₀ _ hbj.ne', hZ]; unfold bk; ring
  rw [hkey, abs_div, abs_of_pos hbj, div_le_iff₀ hbj]
  have hcj : 0 ≤ cm N β ^ j := pow_nonneg hc j
  have habs : |R N β n - cm N β ^ (j + 1)| ≤ cm N β ^ j * (1 + cm N β) := by
    rw [abs_le]; constructor <;> nlinarith [pow_succ (cm N β) j]
  calc |R N β n - cm N β ^ (j + 1)| ≤ cm N β ^ j * (1 + cm N β) := habs
    _ = (1 + cm N β) / bk N β * (cm N β / bk N β) ^ j * bk N β ^ (j + 1) := by
        rw [div_pow, pow_succ]; field_simp

/-! ## 7. The area-weighted defect -/

/-- `k q^{k − 1} → 0`. DERIVED: `1` the shift; `0` the limit. -/
theorem tendsto_mul_pow_pred {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Tendsto (fun k : ℕ => (k : ℝ) * q ^ (k - 1)) atTop (𝓝 0) := by
  refine ((LayerSplit.tendsto_succ_mul_pow h0 h1).comp (tendsto_sub_atTop_nat 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Function.comp]
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- **A ratio approaching `1` fast enough has a vanishing area-weighted logarithm**: `n²|e(n) − 1| → 0` gives
`n² log e(n) → 0`. DERIVED: `1/2` the range of `LayerSplit.abs_log_one_add_le`; `2` its constant and the
exponent of the area; `0` the limit. -/
theorem tendsto_sq_mul_log {e : ℕ → ℝ} (h : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * |e n - 1|) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.log (e n)) atTop (𝓝 0) := by
  have h2 := h.const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop 1, h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
    with n hn hlt
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hsmall : |e n - 1| ≤ 1 / 2 := by nlinarith [abs_nonneg (e n - 1)]
  have hl := LayerSplit.abs_log_one_add_le hsmall
  rw [add_sub_cancel] at hl
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  calc (n : ℝ) ^ 2 * |Real.log (e n)| ≤ (n : ℝ) ^ 2 * (2 * |e n - 1|) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 2 * ((n : ℝ) ^ 2 * |e n - 1|) := by ring

/-- The ratio `Z₂(n)/b^{n²}`. -/
noncomputable def ratio (N : ℕ) (β : ℝ) (n : ℕ) : ℝ := ZT (SU N) 2 wilsonDensity β n / bk N β ^ (n ^ 2)

/-- DERIVED: `2` the exponent of the area and the least side; `0` the limit. -/
theorem tendsto_sq_mul_ratio (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * |ratio N β n - 1|) atTop (𝓝 0) := by
  have hb := bk_pos hN hβ
  have hc := cm_nonneg hN hβ
  have hq0 : 0 ≤ cm N β / bk N β := div_nonneg hc hb.le
  have hq1 : cm N β / bk N β < 1 := by
    rw [div_lt_one hb]; unfold bk; linarith [fl_pos β]
  have hsq : Tendsto (fun n : ℕ => n ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hg := ((tendsto_mul_pow_pred hq0 hq1).comp hsq).const_mul ((1 + cm N β) / bk N β)
  rw [mul_zero] at hg
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hg
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h := abs_ratio_sub_one_le hN hn hβ
  simp only [Function.comp]
  push_cast
  calc (n : ℝ) ^ 2 * |ratio N β n - 1|
      ≤ (n : ℝ) ^ 2 * ((1 + cm N β) / bk N β * (cm N β / bk N β) ^ (n ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **The 2D doubling defect vanishes, area-weighted, at every `β ≥ 0`**: `n² D₂(n) → 0`, for `SU(N)`,
`N ≠ 0`, with no cited input. The conclusion of `LayerSplit.twoD_vanishes`. DERIVED: `4 = 2²` the copies;
`2` the doubling and the least side; `0` the limit. -/
theorem twoD_vanishes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * LayerSplit.D2 N β n) atTop (𝓝 0) := by
  have hA := tendsto_sq_mul_log (tendsto_sq_mul_ratio hN hβ)
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have hB0 := (tendsto_sq_mul_ratio hN hβ).comp h2n
  have hB1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * |ratio N β (2 * n) - 1|) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hB0
    simp only [Function.comp]
    push_cast
    have : (n : ℝ) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hB := tendsto_sq_mul_log (e := fun n => ratio N β (2 * n)) hB1
  have hlim := (hA.const_mul 4).sub hB
  rw [mul_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hb := bk_pos hN hβ
  have hlog : ∀ m : ℕ, 2 ≤ m →
      Real.log (ZT (SU N) 2 wilsonDensity β m) = (m : ℝ) ^ 2 * Real.log (bk N β) + Real.log (ratio N β m) := by
    intro m hm
    have hZ := ZT_pos hN hm hβ (N := N)
    unfold ratio
    rw [Real.log_div hZ.ne' (pow_pos hb _).ne', Real.log_pow]
    push_cast
    ring
  unfold LayerSplit.D2 LayerSplit.logZ2
  rw [hlog n hn, hlog (2 * n) (by omega)]
  push_cast
  ring

/-! ## 8. Downstream, with no cited input -/

/-- **The layered window defect vanishes along the windows**, at every `β ≥ 0`. DERIVED: `8` from
`LayerSplit.layerDefect_eq`; `2` the doubling; `0` the limit. -/
theorem layer_vanishes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (LayerSplit.layerDefect N β) atTop (𝓝 0) := by
  have hw : Tendsto (fun w : ℕ => 2 ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h8 := ((twoD_vanishes hN hβ).comp hw).const_mul 8
  rw [mul_zero] at h8
  refine h8.congr fun w => ?_
  rw [LayerSplit.layerDefect_eq]
  simp only [Function.comp]
  push_cast
  ring

/-- **The decoupled end vanishes**: `DA N β 0 · → 0` at every `β ≥ 0`. DERIVED: `0` the decoupled end and the
limit. -/
theorem decoupled_vanishes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun w => AnisoTorus.DA N β 0 w) atTop (𝓝 0) :=
  (layer_vanishes hN hβ).congr fun w =>
    (AnisoTorus.DA_decoupled (DecoupledSplit.decoupledFactor N β) w).symm

/-- **The mixed anchor holds at every `β ≥ 0`**, with no cited input. DERIVED: `0` the sign. -/
theorem weakMixAnchor (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : AnisoTorus.WeakMixAnchor N β :=
  MixAnchor.weakMixAnchor_of_decoupled hN hβ (decoupled_vanishes hN hβ)

/-- **The strong end from analyticity in `β_⊥` alone**: frequently `AnisoAnalytic N β` gives `StrongEnd N`.
DERIVED: `0` the sign. -/
theorem strongEnd_of_aniso (hN : N ≠ 0) (h : ∃ᶠ β in atTop, AnisoTorus.AnisoAnalytic N β) :
    CouplingTower.StrongEnd N := by
  refine AnisoTorus.strongEnd_of_aniso ?_
  refine (h.and_eventually (eventually_ge_atTop 0)).mono ?_
  rintro β ⟨hA, hβ⟩
  exact ⟨hA, weakMixAnchor hN hβ⟩

end MassGap.TwoDVanish

#print axioms MassGap.TwoDVanish.finRotate_ne
#print axioms MassGap.TwoDVanish.reach
#print axioms MassGap.TwoDVanish.tshift_injective
#print axioms MassGap.TwoDVanish.tshift_ne
#print axioms MassGap.TwoDVanish.tshift_iter
#print axioms MassGap.TwoDVanish.exists_free
#print axioms MassGap.TwoDVanish.continuous_face
#print axioms MassGap.TwoDVanish.hol_zero_one
#print axioms MassGap.TwoDVanish.hol_one_zero
#print axioms MassGap.TwoDVanish.boltz_eq
#print axioms MassGap.TwoDVanish.continuous_sw
#print axioms MassGap.TwoDVanish.sw_nonneg
#print axioms MassGap.TwoDVanish.sw_le_one
#print axioms MassGap.TwoDVanish.integrable_of_continuous
#print axioms MassGap.TwoDVanish.face_update_other
#print axioms MassGap.TwoDVanish.face_update_e0
#print axioms MassGap.TwoDVanish.face_update_e1
#print axioms MassGap.TwoDVanish.integral_prod_proper
#print axioms MassGap.TwoDVanish.ZT_eq
#print axioms MassGap.TwoDVanish.R_le
#print axioms MassGap.TwoDVanish.ZT_pos
#print axioms MassGap.TwoDVanish.abs_ratio_sub_one_le
#print axioms MassGap.TwoDVanish.tendsto_mul_pow_pred
#print axioms MassGap.TwoDVanish.tendsto_sq_mul_log
#print axioms MassGap.TwoDVanish.tendsto_sq_mul_ratio
#print axioms MassGap.TwoDVanish.twoD_vanishes
#print axioms MassGap.TwoDVanish.layer_vanishes
#print axioms MassGap.TwoDVanish.decoupled_vanishes
#print axioms MassGap.TwoDVanish.weakMixAnchor
#print axioms MassGap.TwoDVanish.strongEnd_of_aniso
