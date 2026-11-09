import Mathlib
import MassGap.StripWidth

/-!
# MassGap.StripWiden — the rows glued: the seed reads the area, and the strip widens by a power of `β`

`StripRow.ratio_row` reads the 2D torus ratio `ρ(n) = Z₂(n)/b^{n²}` one row at a time, so the seed of `StripWidth` is
a window of side `n₀ ≍ ℓ L` and the strip is `t ≲ (ℓ L)⁻²`. This module glues the rows into one convolution power
of the plaquette walk, so the decay is in the area and the seed is a window of area `≍ ℓ L`. Declarations are in
`MassGap.StripWiden`.

## The result

* `ratio_eq`: `ρ(m + 1) = ∫ dP ∫ dY ∏_r F_m(P_r Y_r P_{r+1}⁻¹ Y_r⁻¹)`, `F_m` the `(m + 1)`-fold convolution of
  `p = wt/b`. Each row of vertical links integrates to `F_m` of the products `P_r` of the row's horizontal links
  (`row_eq`, `oc_explicit`); the products of independent Haar rows are independent Haar (`mp_prodL`, `rowP_mp`).
* `ratio_glue`: so the `n` rows are one cyclic chain of class weights `F_{n−1}`, whose convolution power is
  `F_{n²−1}` (`Fk_Fk`): `|ρ(n) − 1| ≤ e^{−(n² − 2)/(2ℓ)}/b` for `n ≥ 2`. One factor `1/b`, not `n`.
* `seed_glue`: `DA(β, 0, w) ≤ 1/2000` once `4^w ≥ A_glue = 2 + 2 ℓ (2 L + 2 log ℓ + 26)`, `1/b ≤ e^L`.
* `strip_width_glue`: `DA(β, t, ·) → 0` for `0 ≤ t ≤ t_glue(N, β) = 1/(16192 A_glue(ℓ, L))`, with `ℓ = gapArea N β`,
  `L = bulkExp N β`, for every `N ≠ 0`, `β ≥ 0`.
* `tPoly_le_tGlue`: `t_poly ≤ t_glue`. `tGlue_le`: `t_glue ≤ 1/(16192 (7800 (N + 4) β + 2))`.

Read off the closed form of `tGlue` (not a Lean statement; only `tGlue_pos`, `tPoly_le_tGlue` and `tGlue_le` are proved): `t_glue ≍ 1/(ℓ L) ≍ c_N⁻¹ (β log β)⁻¹`, `c_N ≍ N³`, against `t_poly ≍ c_N⁻² (β log β)⁻²`: one power of `β log β`
gained. So the strip stays far from the diagonal: `t_glue/β ≍ c_N⁻¹ β⁻² (log β)⁻¹`, read off the closed form.

## The convolution algebra (§1)

`dens_Pop`: one step of the walk keeps a symmetric class density. `Pop_Pop`: `P_{P g} = P_g ∘ P_p`; so
`Pop_Fk`: convolution by `F_m` is the `(m + 1)`-st power of the walk, and `Fk_Fk`: `F_k[F_m] = F_{(m+1)k + m}`.

DERIVED (module-wide): `0`, `1` the two directions and the first point; `2` the dimension, the least side, the doubling;
`4 = 2²` the area of the doubling; `n² − 1` the faces of the chain less the closing one; `(m + 1) k + m` the length of
a glued chain. COMPUTED: `26 = 2 · 13` from `e^{13} ≥ 384000 = 192 · 2000` (`StripWidth.exp_thirteen`); `192 = 48 · 2 · 2`;
`16192` as in `StripWidth.tStar`; `7800 = 52 · 150`. Inherited: `1/2000` of `StripWidth.strip_of_seed`, `ℓ` of
`StripGap.gapArea`, `L` of `StripWidth.bulkExp`.

## Where the method stops

`StripWidth.DA_le` costs `8192 · 16^w t²`, so a seed of area `A = 4^w` opens `t ≲ 1/A`. The proved area `A_glue` is
at least `52 ℓ ≥ 7800 (N + 4) β` (`tGlue_le`). By the character expansion (not proved here) `ρ(n) − 1` is a sum over
the nontrivial classes of `λ^{n²}`, with `1 − λ ≍ 1/β` for the slowest class, so no seed of area `≪ β` exists and the
`t²` form of `DA_le` cannot open more than `t ≲ 1/β`. This module reaches that up to the factor `L ≍ N² log β`, the
cost of the single sup bound `1/b ≤ e^L`.

## What does not follow

* The bound of `DA_le` is quadratic: Hölder over the sixteen colours multiplies the `t²` coefficient by sixteen, so the
  `t²` terms of `n` and `2n` do not cancel. The quartic form is `CumulantStrip.DA_le_quartic`, and the strip here is
  contained in `CumulantStrip`'s (`CumulantStrip.tGlue_le_tQuart`). This strip ends at `t ≍ (β log β)⁻¹`.
* `CouplingTower.StrongEnd`, `AnisoTorus.AnisoAnalytic`, `MixCutTest.VarGap`, `MixPlane.NoStallOnSegment` stay open.
-/

namespace MassGap.StripWiden

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.TorusDoubling MassGap.StripGap
  MassGap.StripRow
open MassGap.SUN (SU)

variable {N : ℕ}

/-! ## 1. The convolution algebra of symmetric class densities -/

/-- **One step of the walk keeps a symmetric class density.** No numeral. -/
theorem dens_Pop {p f : SU N → ℝ} (hp : Dens p) (hf : Dens f) : Dens (Pop p f) where
  cont := cont_Pop hp.cont hf.cont
  nonneg x := integral_nonneg fun z => mul_nonneg (hf.nonneg _) (hp.nonneg _)
  mass := (mass_Pop hp hf.cont).trans hf.mass
  inv x := by
    unfold Pop
    have h := integral_inv_eq_self (fun z => f (x * z) * p z) (hm N)
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have e : f (x⁻¹ * z) = f (x * z⁻¹) := by
      rw [← hf.inv (x⁻¹ * z), mul_inv_rev, inv_inv, hf.cyc]
    simp only
    rw [e, hp.inv]
  cyc a b := by
    unfold Pop
    have h := HeatBath.integral_twoSided (fun z => f (b * a * z) * p z) b b⁻¹
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have e1 : b * a * (b * z * b⁻¹) = b * (a * b * z * b⁻¹) := by group
    have e2 : a * b * z * b⁻¹ * b = a * b * z := by group
    have e3 : p (b * z * b⁻¹) = p z := by
      rw [mul_assoc, hp.cyc, inv_mul_cancel_right]
    simp only
    rw [e1, hf.cyc b (a * b * z * b⁻¹), e2, e3]

theorem dens_Fk {p : SU N → ℝ} (hp : Dens p) : ∀ k, Dens (Fk p k)
  | 0 => hp
  | k + 1 => dens_Pop hp (dens_Fk hp k)

/-- **Convolution by `P_p g` is the walk after convolution by `g`**: `P_{P_p g} f = P_g (P_p f)`. Fubini, a right
translation and the inversion. No numeral. -/
theorem Pop_Pop {p g f : SU N → ℝ} (hp : Dens p) (hg : Continuous g) (hf : Continuous f) (x : SU N) :
    Pop (Pop p g) f x = Pop g (Pop p f) x := by
  have hpc : Continuous p := hp.cont
  unfold Pop
  have L1 : ∀ z, f (x * z) * ∫ w, g (z * w) * p w ∂hm N = ∫ w, f (x * z) * (g (z * w) * p w) ∂hm N :=
    fun z => (integral_const_mul _ _).symm
  simp_rw [L1]
  rw [swap_int (F := fun z w => f (x * z) * (g (z * w) * p w)) (by fun_prop)]
  have L2 : ∀ w, ∫ z, f (x * z) * (g (z * w) * p w) ∂hm N
      = ∫ u, f (x * (u * w⁻¹)) * p w * g u ∂hm N := by
    intro w
    have h := integral_mul_right_eq_self (μ := hm N) (fun z => f (x * z) * (g (z * w) * p w)) w⁻¹
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [inv_mul_cancel_right]
    ring
  simp_rw [L2]
  rw [swap_int (F := fun w u => f (x * (u * w⁻¹)) * p w * g u) (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [integral_mul_const]
  congr 1
  have h := integral_inv_eq_self (fun w => f (x * u * w) * p w) (hm N)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [hp.inv, mul_assoc]

/-- **Convolution by `F_m` is the `(m + 1)`-st power of the walk.** DERIVED: `1` the first step. -/
theorem Pop_Fk {p : SU N → ℝ} (hp : Dens p) :
    ∀ (m : ℕ) (f : SU N → ℝ), Continuous f → Pop (Fk p m) f = (Pop p)^[m + 1] f
  | 0, _, _ => rfl
  | m + 1, f, hf => by
    funext x
    show Pop (Pop p (Fk p m)) f x = _
    rw [Pop_Pop hp (cont_Fk hp.cont m) hf x, Pop_Fk hp m (Pop p f) (cont_Pop hp.cont hf)]
    rfl

theorem Fk_iter (p : SU N → ℝ) : ∀ j, Fk p j = (Pop p)^[j] p
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ← Fk_iter p j]
    rfl

/-- **A chain of chains is a chain**: `F_k[F_m] = F_{(m+1) k + m}`. DERIVED: `1` the step. -/
theorem Fk_Fk {p : SU N → ℝ} (hp : Dens p) (m : ℕ) : ∀ k, Fk (Fk p m) k = Fk p ((m + 1) * k + m)
  | 0 => by simp [Fk]
  | k + 1 => by
    show Pop (Fk p m) (Fk (Fk p m) k) = _
    rw [Pop_Fk hp m _ (cont_Fk (cont_Fk hp.cont m) k), Fk_Fk hp m k, Fk_iter p ((m + 1) * k + m),
      ← Function.iterate_add_apply, ← Fk_iter]
    congr 1
    ring

/-! ## 2. The products along a row -/

/-- **The ordered product** `a₀ a₁ ⋯ a_m`. DERIVED: `0`, `1` the first point and the step. -/
def prodL : (m : ℕ) → (Fin (m + 1) → SU N) → SU N
  | 0, a => a 0
  | m + 1, a => a 0 * prodL m (fun i => a i.succ)

/-- **The reversed product** `e_m ⋯ e₁ e₀`. DERIVED: `0`, `1` the first point and the step. -/
def prodR : (m : ℕ) → (Fin (m + 1) → SU N) → SU N
  | 0, e => e 0
  | m + 1, e => prodR m (fun i => e i.succ) * e 0

theorem prodR_inv : ∀ (m : ℕ) (a : Fin (m + 1) → SU N), prodR m (fun i => (a i)⁻¹) = (prodL m a)⁻¹
  | 0, _ => rfl
  | m + 1, a => by
    simp only [prodR, prodL]
    rw [prodR_inv m (fun i => a i.succ), mul_inv_rev]

/-- **The product of independent Haar elements is Haar.** The shear `(x, y) ↦ (x, x y)`. DERIVED: `0` the first
point. -/
theorem mp_prodL : ∀ m : ℕ, MeasurePreserving (prodL (N := N) m) (hmv N (m + 1)) (hm N)
  | 0 => by
    have h := measurePreserving_eval (μ := fun _ : Fin 1 => hm N) 0
    exact h
  | m + 1 => by
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => hm N) 0
    have h2 := (MeasurePreserving.id (hm N)).prod (mp_prodL m)
    have h3 := measurePreserving_prod_mul (hm N) (hm N)
    have h4 := measurePreserving_snd (μ := hm N) (ν := hm N)
    have h := h4.comp (h3.comp (h2.comp h1))
    convert h using 1
    funext a
    simp [prodL, Fin.insertNthEquiv]
    rfl

/-! ## 3. A row of class weights is a class weight of its two boundary products -/

/-- **An open chain, explicitly**: `oc = F_m(a₀ ⋯ a_m w e_m ⋯ e₀ u⁻¹)`. The free point is moved onto the argument
of `F` by inversion, a two-sided translation and the class property. DERIVED: `0` the first point. -/
theorem oc_explicit {p : SU N → ℝ} (hp : Dens p) :
    ∀ (m : ℕ) (a e : Fin (m + 1) → SU N) (u w : SU N),
      oc p m a e u w = Fk p m (prodL m a * w * prodR m e * u⁻¹)
  | 0, a, e, u, w => by rw [oc_zero]; rfl
  | m + 1, a, e, u, w => by
    rw [oc_succ hp.cont]
    simp_rw [oc_explicit hp m]
    set A' : SU N := prodL m (a ∘ Fin.succ) with hA'
    set E' : SU N := prodR m (e ∘ Fin.succ) with hE'
    have hL : prodL (m + 1) a = a 0 * A' := rfl
    have hR : prodR (m + 1) e = E' * e 0 := rfl
    rw [hL, hR]
    set G : SU N → ℝ := fun y => p (a 0 * y * e 0 * u⁻¹) * Fk p m (A' * w * E' * y⁻¹) with hG
    have h1 := integral_inv_eq_self (fun z => G ((a 0)⁻¹ * z * (u * (e 0)⁻¹))) (hm N)
    have h2 := HeatBath.integral_twoSided G (a 0)⁻¹ (u * (e 0)⁻¹)
    show ∫ y, G y ∂hm N = _
    rw [← h2, ← h1]
    show _ = ∫ z, Fk p m ((a 0 * A' * w * (E' * e 0) * u⁻¹) * z) * p z ∂hm N
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hG]
    have e1 : a 0 * ((a 0)⁻¹ * z⁻¹ * (u * (e 0)⁻¹)) * e 0 * u⁻¹ = z⁻¹ := by group
    have e2 : A' * w * E' * ((a 0)⁻¹ * z⁻¹ * (u * (e 0)⁻¹))⁻¹ = (A' * w * E' * e 0 * u⁻¹ * z) * a 0 := by
      group
    have e3 : Fk p m ((A' * w * E' * e 0 * u⁻¹ * z) * a 0) = Fk p m (a 0 * (A' * w * E' * e 0 * u⁻¹ * z)) :=
      (dens_Fk hp m).cyc _ _
    have e4 : a 0 * (A' * w * E' * e 0 * u⁻¹ * z) = a 0 * A' * w * (E' * e 0) * u⁻¹ * z := by group
    rw [e1, e2, e3, e4, hp.inv, mul_comm]

/-- **A cyclic row, explicitly**: `∫ ∏_t p(a_t v_{t+1} e_t v_t⁻¹) dv = ∫ F_m(a₀ ⋯ a_m y e_m ⋯ e₀ y⁻¹) dy`. DERIVED:
`1` the first point. -/
theorem row_eq {p : SU N → ℝ} (hp : Dens p) (m : ℕ) (a e : Fin (m + 1) → SU N) :
    ∫ v : Fin (m + 1) → SU N, ∏ t, p (a t * v (finRotate (m + 1) t) * e t * (v t)⁻¹) ∂hmv N (m + 1)
      = ∫ y, Fk p m (prodL m a * y * prodR m e * y⁻¹) ∂hm N := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hp.cont.continuousOn
  have hC' : ∀ g, |p g| ≤ C := fun g => by
    have := hC g (mem_univ g)
    rwa [Real.norm_eq_abs] at this
  have hcont : Continuous fun v : Fin (m + 1) → SU N =>
      ∏ t, p (a t * v (finRotate (m + 1) t) * e t * (v t)⁻¹) := by
    refine continuous_finsetProd _ fun t _ => hp.cont.comp ?_
    exact ((continuous_const.mul (continuous_apply _)).mul continuous_const).mul (continuous_apply _).inv
  rw [CyclicKernel.integral_cons hcont.measurable (C := C ^ Fintype.card (Fin (m + 1)))
    (fun W => CyclicKernel.abs_prod_le fun t => hC' _)]
  have hJ : ∀ y, ∫ V : Fin m → SU N, ∏ t, p (a t * (Fin.cons (α := fun _ => SU N) y V
        (finRotate (m + 1) t)) * e t * (Fin.cons (α := fun _ => SU N) y V t)⁻¹) ∂hmv N m
      = oc p m a e y y := by
    intro y
    unfold oc
    refine integral_congr_ae (Eventually.of_forall fun V => ?_)
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Fin.snoc_eq_cons_rotate]
  simp_rw [hJ, oc_explicit hp m]

/-! ## 4. The rows of horizontal links: products of independent Haar rows -/

variable {n : ℕ}

variable (n) in
/-- The sites by row and column. DERIVED: `0`, `1` the two directions. -/
def eRC : Fin n × Fin n ≃ TSite 2 n where
  toFun q := pt q.2 q.1
  invFun x := (x 1, x 0)
  left_inv := by rintro ⟨r, c⟩; simp [pt]
  right_inv := by
    intro x
    funext j
    fin_cases j <;> simp [pt]

variable (n N) in
/-- **The rows of horizontal links**: `A ↦ (r ↦ (c ↦ A(c, r)))`. No numeral. -/
noncomputable def rowsE : (TSite 2 n → SU N) ≃ᵐ (Fin n → Fin n → SU N) :=
  (MeasurableEquiv.piCongrLeft (fun _ : TSite 2 n => SU N) (eRC n)).symm.trans
    (MeasurableEquiv.curry (Fin n) (Fin n) (SU N))

theorem rowsE_apply (A : TSite 2 n → SU N) (r c : Fin n) : rowsE N n A r c = A (pt c r) := rfl

theorem rowsE_mp : MeasurePreserving (rowsE N n) (Measure.pi fun _ : TSite 2 n => hm N)
    (Measure.pi fun _ : Fin n => hmv N n) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : TSite 2 n => SU N) (eRC n))
      (Measure.pi fun _ : Fin n × Fin n => hm N) (Measure.pi fun _ : TSite 2 n => hm N) :=
    measurePreserving_piCongrLeft (μ := fun _ : TSite 2 n => hm N) (eRC n)
  have hmap := Measure.infinitePi_map_curry (X := SU N) (ι := Fin n) (κ := Fin n) (fun _ _ => hm N)
  simp only [Measure.infinitePi_eq_pi] at hmap
  have h3 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) (SU N))
      (Measure.pi fun _ : Fin n × Fin n => hm N) (Measure.pi fun _ : Fin n => hmv N n) :=
    ⟨(MeasurableEquiv.curry (Fin n) (Fin n) (SU N)).measurable, hmap⟩
  exact h3.comp (MeasurePreserving.symm _ h1)

/-- **The row products** `R(A)_r = A(0, r) ⋯ A(m, r)`. No numeral. -/
noncomputable def rowP (m : ℕ) (A : TSite 2 (m + 1) → SU N) (r : Fin (m + 1)) : SU N :=
  prodL m (fun c => A (pt c r))

/-- **The row products of Haar links are independent Haar.** No numeral. -/
theorem rowP_mp (m : ℕ) : MeasurePreserving (rowP (N := N) m)
    (Measure.pi fun _ : TSite 2 (m + 1) => hm N) (hmv N (m + 1)) := by
  have h2 := measurePreserving_pi (fun _ : Fin (m + 1) => hmv N (m + 1)) (fun _ : Fin (m + 1) => hm N)
    (f := fun _ => prodL m) (fun _ => mp_prodL m)
  exact h2.comp (rowsE_mp (n := m + 1))

/-! ## 5. The torus ratio as one cyclic chain of glued rows -/

theorem cont_chain {m : ℕ} {F : SU N → ℝ} (hF : Continuous F) :
    Continuous fun q : (Fin (m + 1) → SU N) × (Fin (m + 1) → SU N) =>
      ∏ r, F (q.1 r * q.2 r * (q.1 (finRotate (m + 1) r))⁻¹ * (q.2 r)⁻¹) := by
  refine continuous_finsetProd _ fun r _ => hF.comp ?_
  fun_prop

/-- **The ratio as a chain of glued rows**: `ρ(m + 1) = ∫ dP ∫ dY ∏_r F_m(P_r Y_r P_{r+1}⁻¹ Y_r⁻¹)`. Each row of
vertical links integrates to `b^{m+1} ∫ F_m(R_r y R_{r+1}⁻¹ y⁻¹) dy` (`row_eq`, `prodR_inv`), `R_r` the product of the
row's horizontal links, and the `R_r` are independent Haar (`rowP_mp`). DERIVED: `1` the ratio at equilibrium; `2`
the dimension. -/
theorem ratio_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) :
    TwoDVanish.ratio N β (m + 1)
      = ∫ P : Fin (m + 1) → SU N, ∫ Y : Fin (m + 1) → SU N,
          ∏ r, Fk (pW N β) m (P r * Y r * (P (finRotate (m + 1) r))⁻¹ * (Y r)⁻¹) ∂hmv N (m + 1)
          ∂hmv N (m + 1) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hpd := pW_dens hN hβ
  have hFc : Continuous (Fk (pW N β) m) := cont_Fk hpd.cont m
  set G : (Fin (m + 1) → SU N) → ℝ := fun P => ∫ Y, ∏ r, Fk (pW N β) m
    (P r * Y r * (P (finRotate (m + 1) r))⁻¹ * (Y r)⁻¹) ∂hmv N (m + 1) with hG
  have hGc : Continuous G := by
    have hf : Continuous (Function.uncurry fun (P : Fin (m + 1) → SU N) (Y : Fin (m + 1) → SU N) =>
        ∏ r, Fk (pW N β) m (P r * Y r * (P (finRotate (m + 1) r))⁻¹ * (Y r)⁻¹)) := cont_chain hFc
    have h := continuous_parametric_integral_of_continuous (μ := hmv N (m + 1)) hf isCompact_univ
    simp only [Measure.restrict_univ] at h
    exact h
  set Fq : RowCfg (m + 1) N → ℝ := fun q => ∏ r, ∏ c, faceR β q.1 r (q.2 r) c with hFq
  have hFqc : Continuous Fq :=
    continuous_finsetProd _ fun r _ => continuous_finsetProd _ fun c _ => cont_faceR β r c
  have hFi : Integrable Fq ((Measure.pi fun _ : TSite 2 (m + 1) => hm N).prod
      (Measure.pi fun _ : Fin (m + 1) => hmv N (m + 1))) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hFqc.continuousOn
    exact ContactFloor.integrable_of_bounded hFqc.measurable M fun z => by
      have hz := hM z (mem_univ z)
      rwa [Real.norm_eq_abs] at hz
  have hZ : TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β (m + 1)
      = ∫ A, ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin (m + 1) => hmv N (m + 1))
          ∂(Measure.pi fun _ : TSite 2 (m + 1) => hm N) := by
    have h1 : TorusDoubling.ZT (SU N) 2 WilsonAction.wilsonDensity β (m + 1)
        = ∫ U, Fq (splitR (m + 1) N U) ∂(Measure.pi fun _ : TLink 2 (m + 1) => hm N) := by
      unfold TorusDoubling.ZT LatticeGauge.System.partition LatticeGauge.System.vol
      refine integral_congr_ae (Eventually.of_forall fun U => ?_)
      show _ = Fq (splitR (m + 1) N U)
      rw [TwoDVanish.boltz_eq hN β U, boltz_split]
    rw [h1, (splitR_mp (n := m + 1) (N := N)).integral_comp' Fq, integral_prod _ hFi]
  have hin : ∀ A : TSite 2 (m + 1) → SU N,
      ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin (m + 1) => hmv N (m + 1))
        = TwoDVanish.bk N β ^ ((m + 1) ^ 2) * G (rowP m A) := by
    intro A
    have e0 : ∫ V, Fq (A, V) ∂(Measure.pi fun _ : Fin (m + 1) => hmv N (m + 1))
        = ∏ r, ∫ v, ∏ c, faceR β A r v c ∂hmv N (m + 1) :=
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun r v => ∏ c, faceR β A r v c)
    have e1 : ∀ r, ∫ v, ∏ c, faceR β A r v c ∂hmv N (m + 1)
        = TwoDVanish.bk N β ^ (m + 1) * ∫ y, Fk (pW N β) m
            (rowP m A r * y * (rowP m A (finRotate (m + 1) r))⁻¹ * y⁻¹) ∂hm N := by
      intro r
      have e : ∀ v : Fin (m + 1) → SU N, ∏ c, faceR β A r v c
          = TwoDVanish.bk N β ^ (m + 1) * ∏ c, pW N β (A (pt c r) * v (finRotate (m + 1) c)
              * (A (pt c (finRotate (m + 1) r)))⁻¹ * (v c)⁻¹) := by
        intro v
        have e' : ∀ c, faceR β A r v c = TwoDVanish.bk N β * pW N β (A (pt c r) * v (finRotate (m + 1) c)
            * (A (pt c (finRotate (m + 1) r)))⁻¹ * (v c)⁻¹) := by
          intro c
          unfold faceR pW
          rw [mul_div_cancel₀ _ hb.ne']
        simp_rw [e']
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp_rw [e]
      rw [integral_const_mul, row_eq hpd m (fun c => A (pt c r)) (fun c => (A (pt c (finRotate (m + 1) r)))⁻¹),
        prodR_inv m (fun c => A (pt c (finRotate (m + 1) r)))]
      rfl
    rw [e0]
    simp_rw [e1]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
      show (m + 1) * (m + 1) = (m + 1) ^ 2 by ring]
    congr 1
    simp only [hG]
    exact (integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun r y => Fk (pW N β) m (rowP m A r * y * (rowP m A (finRotate (m + 1) r))⁻¹ * y⁻¹))).symm
  have hmp := rowP_mp (N := N) m
  have hmap : ∫ A, G (rowP m A) ∂(Measure.pi fun _ : TSite 2 (m + 1) => hm N) = ∫ P, G P ∂hmv N (m + 1) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hGc.aestronglyMeasurable]
  unfold TwoDVanish.ratio
  rw [hZ, integral_congr_ae (Eventually.of_forall hin), integral_const_mul, hmap]
  field_simp

/-! ## 6. The glued bound: decay in the area -/

/-- **`ratio_glue`: the 2D torus ratio decays in the area.** `|ρ(k + 2) − 1| ≤ e^{−((k + 2)² − 2)/(2ℓ)}/b`. The
`n = k + 2` glued rows are one cyclic chain of the class density `F_{n−1}` (`ratio_eq`), whose `n`-fold convolution is
`F_{n²−1}` (`Fk_Fk`), and `StripGap.Fk_equil` bounds it. DERIVED: `2` the least side and the closing face; `1` the
mass. -/
theorem ratio_glue (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    |TwoDVanish.ratio N β (k + 2) - 1|
      ≤ Real.exp (-((((k + 2 : ℕ) : ℝ) ^ 2 - 2) / (2 * gapArea N β))) * (1 / TwoDVanish.bk N β) := by
  have hpd := pW_dens hN hβ
  have hFd : Dens (Fk (pW N β) (k + 1)) := dens_Fk hpd (k + 1)
  set η : ℝ := Real.exp (-((((k + 2 : ℕ) : ℝ) ^ 2 - 2) / (2 * gapArea N β))) * (1 / TwoDVanish.bk N β)
    with hη
  have hη' : ∀ x, |Fk (Fk (pW N β) (k + 1)) (k + 1) x - 1| ≤ η := by
    intro x
    have e : Fk (Fk (pW N β) (k + 1)) (k + 1) = Fk (pW N β) ((k ^ 2 + 4 * k + 2) + 1) := by
      rw [Fk_Fk hpd (k + 1) (k + 1)]
      congr 1
      ring
    rw [e]
    have hb := Fk_equil hN hβ (k ^ 2 + 4 * k + 2) x
    have ecast : (((k ^ 2 + 4 * k + 2 : ℕ) : ℝ)) = (((k + 2 : ℕ) : ℝ)) ^ 2 - 2 := by push_cast; ring
    rw [ecast] at hb
    exact hb
  have h : TwoDVanish.ratio N β (k + 2) = ∫ P : Fin (k + 1 + 1) → SU N, ∫ Y : Fin (k + 1 + 1) → SU N,
      ∏ r, Fk (pW N β) (k + 1) (P r * Y r * (P (finRotate (k + 1 + 1) r))⁻¹ * (Y r)⁻¹)
        ∂hmv N (k + 1 + 1) ∂hmv N (k + 1 + 1) :=
    ratio_eq hN hβ (k + 1)
  rw [h]
  have hH := cont_chain (m := k + 1) hFd.cont
  have hInt : Integrable (Function.uncurry fun (P Y : Fin (k + 1 + 1) → SU N) =>
      ∏ r, Fk (pW N β) (k + 1) (P r * Y r * (P (finRotate (k + 1 + 1) r))⁻¹ * (Y r)⁻¹))
      ((hmv N (k + 1 + 1)).prod (hmv N (k + 1 + 1))) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hH.continuousOn
    exact ContactFloor.integrable_of_bounded hH.measurable M fun z => by
      have hz := hM z (mem_univ z)
      rwa [Real.norm_eq_abs] at hz
  rw [integral_integral_swap hInt]
  set I : (Fin (k + 1 + 1) → SU N) → ℝ := fun Y => ∫ P, ∏ r, Fk (pW N β) (k + 1)
    (P r * Y r * (P (finRotate (k + 1 + 1) r))⁻¹ * (Y r)⁻¹) ∂hmv N (k + 1 + 1) with hI
  have hIc : Continuous I := by
    have hf : Continuous (Function.uncurry fun (Y : Fin (k + 1 + 1) → SU N) (P : Fin (k + 1 + 1) → SU N) =>
        ∏ r, Fk (pW N β) (k + 1) (P r * Y r * (P (finRotate (k + 1 + 1) r))⁻¹ * (Y r)⁻¹)) :=
      by
        show Continuous fun q : (Fin (k + 1 + 1) → SU N) × (Fin (k + 1 + 1) → SU N) =>
          ∏ r, Fk (pW N β) (k + 1) (q.2 r * q.1 r * (q.2 (finRotate (k + 1 + 1) r))⁻¹ * (q.1 r)⁻¹)
        have hc := hFd.cont
        refine continuous_finsetProd _ fun r _ => hc.comp ?_
        fun_prop
    have h := continuous_parametric_integral_of_continuous (μ := hmv N (k + 1 + 1)) hf isCompact_univ
    simp only [Measure.restrict_univ] at h
    exact h
  have hIb : ∀ Y, |I Y - 1| ≤ η := by
    intro Y
    have e : I Y = ∫ v : Fin (k + 1 + 1) → SU N, ∏ t, Fk (pW N β) (k + 1)
        (Y t * v (finRotate (k + 1 + 1) t) * (Y t)⁻¹ * (v t)⁻¹) ∂hmv N (k + 1 + 1) := by
      simp only [hI]
      refine integral_congr_ae (Eventually.of_forall fun P => ?_)
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← hFd.inv]
      congr 1
      group
    rw [e]
    exact row_bound hFd hη' Y (fun t => (Y t)⁻¹)
  have hIi : Integrable I (hmv N (k + 1 + 1)) :=
    ContactFloor.integrable_of_bounded hIc.measurable (η + 1) fun Y => by
      have := hIb Y
      have h2 := abs_sub_abs_le_abs_sub (I Y) 1
      rw [abs_one] at h2
      linarith
  show |∫ Y, I Y ∂hmv N (k + 1 + 1) - 1| ≤ η
  have e1 : ∫ Y, I Y ∂hmv N (k + 1 + 1) - 1 = ∫ Y, (I Y - 1) ∂hmv N (k + 1 + 1) := by
    rw [integral_sub hIi (integrable_const 1)]
    simp
  rw [e1]
  calc |∫ Y, (I Y - 1) ∂hmv N (k + 1 + 1)| ≤ ∫ Y, |I Y - 1| ∂hmv N (k + 1 + 1) := abs_integral_le_integral_abs
    _ ≤ ∫ _Y, η ∂hmv N (k + 1 + 1) := integral_mono (hIi.sub (integrable_const 1)).abs (integrable_const η) hIb
    _ = η := by simp

/-! ## 7. The seed at area `ℓ L` and the widened strip -/

/-- **The glued bound in the form of a seed**: `1/b ≤ e^L` and `y ≤ (j² − 2)/(2ℓ)` give `|ρ(j) − 1| ≤ e^{−y} e^L`.
DERIVED: `2` the least side. -/
theorem ratio_glue_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L)
    {j : ℕ} (hj : 2 ≤ j) {y : ℝ} (hy : y ≤ (((j : ℕ) : ℝ) ^ 2 - 2) / (2 * gapArea N β)) :
    |TwoDVanish.ratio N β j - 1| ≤ Real.exp (-y) * Real.exp L := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  refine (ratio_glue hN hβ k).trans
    (mul_le_mul (Real.exp_le_exp.2 (by linarith)) hL (one_div_nonneg.2 (TwoDVanish.bk_pos hN hβ).le)
      (Real.exp_pos _).le)

/-- **The seed area of the glued rows** `A_glue(ℓ, L) = 2 + 2 ℓ (2 L + 2 log ℓ + 26)`. DERIVED: `2` the closing face;
`2 L + 2 log ℓ + 26` read off `192 ℓ e^{L − y/2} ≤ 1/2000`. COMPUTED: `26 = 2 · 13`, `e^{13} ≥ 384000`. -/
noncomputable def glueArea (ℓ L : ℝ) : ℝ := 2 + 2 * ℓ * (2 * L + 2 * Real.log ℓ + 26)

/-- **The glued rows seed at area `A_glue`**: if `1/b ≤ e^L`, `L ≥ 0`, and `4^w ≥ A_glue(ℓ, L)`, then
`DA(β, 0, w) ≤ 1/2000`. With `y = (4^w − 2)/(2ℓ)`: `4^w ≤ 2ℓ(1 + y) ≤ 4ℓ e^{y/2}`, so
`48 · 4^w e^{L − y} ≤ 192 e^{log ℓ + L − y/2} ≤ 192 e^{−13}`. DERIVED: `4 = 2²` the area of the doubling; `48` of
`StripWidth.seed_of_ratio`; `192 = 48 · 2 · 2`. COMPUTED: `192/384000 = 1/2000`. -/
theorem seed_glue (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L) {w : ℕ} (hw : 1 ≤ w)
    (hA : glueArea (gapArea N β) L ≤ (4 : ℝ) ^ w) : AnisoTorus.DA N β 0 w ≤ 1 / 2000 := by
  set l : ℝ := gapArea N β with hl
  have hl240 : (240 : ℝ) ≤ l := gapArea_ge β hβ
  have hlpos : 0 < l := by linarith
  have hlog : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
  set a : ℝ := (4 : ℝ) ^ w with ha
  have ha0 : 0 ≤ a := by positivity
  have hn1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have hcn : (((2 ^ w : ℕ) : ℝ)) ^ 2 = a := by
    rw [ha]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hcn2 : (((2 * 2 ^ w : ℕ) : ℝ)) ^ 2 = 4 * a := by
    rw [← hcn]; push_cast; ring
  set y : ℝ := (a - 2) / (2 * l) with hy
  have hy0 : 2 * L + 2 * Real.log l + 26 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    unfold glueArea at hA
    nlinarith
  set E : ℝ := Real.exp (-y) * Real.exp L with hE
  have hEp : 0 ≤ E := by positivity
  have hE1 : |TwoDVanish.ratio N β (2 ^ w) - 1| ≤ E :=
    ratio_glue_le hN hβ hL hn1 (by rw [hcn, hy])
  have hE2 : |TwoDVanish.ratio N β (2 * 2 ^ w) - 1| ≤ E :=
    ratio_glue_le hN hβ hL (by omega) (by
      rw [hcn2, hy]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity))
  have hyp : 0 ≤ y := by linarith
  have ha2 : a ≤ 2 * l * (1 + y) := by
    have : a = 2 + 2 * l * y := by rw [hy]; field_simp; ring
    nlinarith
  have hc1 : 1 + y ≤ 2 * Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
  have hdecay : l * Real.exp (y / 2) * E ≤ 1 / 384000 := by
    have e : l * Real.exp (y / 2) * E = Real.exp (Real.log l + y / 2 + -y + L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hlpos, hE]
      ring
    rw [e]
    refine (Real.exp_le_exp.2 (show Real.log l + y / 2 + -y + L ≤ -13 by linarith)).trans ?_
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) StripWidth.exp_thirteen
  have hmain : 48 * a * E ≤ 1 / 2000 := by
    have h1 : a ≤ 2 * l * (2 * Real.exp (y / 2)) :=
      ha2.trans (mul_le_mul_of_nonneg_left hc1 (by positivity))
    calc 48 * a * E ≤ 48 * (2 * l * (2 * Real.exp (y / 2))) * E := by
          have := mul_le_mul_of_nonneg_right h1 hEp
          nlinarith
      _ = 192 * (l * Real.exp (y / 2) * E) := by ring
      _ ≤ 192 * (1 / 384000) := by linarith
      _ = 1 / 2000 := by norm_num
  have hEhalf : E ≤ 1 / 2 := by
    have h1 : 1 ≤ l * Real.exp (y / 2) := by
      have := Real.one_le_exp (show 0 ≤ y / 2 by linarith)
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 hEp
    linarith
  exact StripWidth.seed_of_ratio hN hβ hw hEhalf hE1 hE2 hmain

/-- **The strip from the glued seed**: `1/b ≤ e^L` gives `DA(β, t, ·) → 0` for `0 ≤ t ≤ 1/(16192 A_glue(ℓ, L))`.
COMPUTED: `16192` as in `StripWidth.tStar`. DERIVED: `0` the limit; `16192 = 4 · 4048` as in
`StripWidth.tStar`. -/
theorem strip_of_glue (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L)
    (hts : t ≤ 1 / (16192 * glueArea (gapArea N β) L)) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) := by
  have hl240 : (240 : ℝ) ≤ gapArea N β := gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (gapArea N β) := Real.log_nonneg (by linarith)
  have hA : 1 < glueArea (gapArea N β) L := by
    unfold glueArea
    nlinarith
  obtain ⟨w, hw, h1, h2⟩ := StripWidth.exists_window hA
  refine StripWidth.strip_of_seed hN hβ ht hw (seed_glue hN hβ hL0 hL hw h1) (hts.trans ?_)
  have hp : (0 : ℝ) < (4 : ℝ) ^ w := by positivity
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The glued width** `t_glue(N, β) = 1/(16192 A_glue(ℓ, L))`, `A_glue = 2 + 2 ℓ (2 L + 2 log ℓ + 26)`,
`ℓ = 240 + 150 (N + 4) β`, `L = 1 + 2 N² log K`, `K = ⌈2 √(2 N (β + 1))⌉ + 1`. Read off the closed form: `t_glue ≍ c_N⁻¹ (β log β)⁻¹`.
DERIVED: `16192 = 4 · 4048` as in `StripWidth.tStar`; `26 = 2 · 13` as in `glueArea`; `240`, `150` as in
`StripGap.gapArea`. COMPUTED: as in `glueArea`, `StripGap.gapArea`, `StripWidth.bulkExp`. -/
noncomputable def tGlue (N : ℕ) (β : ℝ) : ℝ :=
  1 / (16192 * glueArea (gapArea N β) (StripWidth.bulkExp N β))

/-- **`strip_width_glue`: the widened strip.** For every `N ≠ 0`, `β ≥ 0` and `0 ≤ t ≤ t_glue(N, β)`,
`DA(β, t, ·) → 0` along the windows. DERIVED: `0` the limit. COMPUTED: as in `tGlue`. -/
theorem strip_width_glue (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ tGlue N β) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) :=
  strip_of_glue hN hβ ht (StripWidth.bulkExp_nonneg β) (StripWidth.one_div_bk_le hN hβ) hts

theorem tGlue_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < tGlue N β := by
  have hl240 : (240 : ℝ) ≤ gapArea N β := gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (gapArea N β) := Real.log_nonneg (by linarith)
  have hL := StripWidth.bulkExp_nonneg (N := N) β
  have hA : 0 < glueArea (gapArea N β) (StripWidth.bulkExp N β) := by
    unfold glueArea
    nlinarith
  unfold tGlue
  positivity

/-- **The glued strip contains the row strip**: `t_poly ≤ t_glue`, since `A_glue ≤ n₀ ≤ n₀²`. DERIVED: `n₀ ≥ 2`. -/
theorem tPoly_le_tGlue {β : ℝ} (hβ : 0 ≤ β) : StripWidth.tPoly N β ≤ tGlue N β := by
  have hl240 : (240 : ℝ) ≤ gapArea N β := gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (gapArea N β) := Real.log_nonneg (by linarith)
  have hL := StripWidth.bulkExp_nonneg (N := N) β
  have hA : 0 < glueArea (gapArea N β) (StripWidth.bulkExp N β) := by
    unfold glueArea; nlinarith
  have hAS : glueArea (gapArea N β) (StripWidth.bulkExp N β)
      ≤ StripWidth.seedSide (gapArea N β) (StripWidth.bulkExp N β) := by
    unfold glueArea StripWidth.seedSide
    nlinarith
  have hS2 : 2 ≤ StripWidth.seedSide (gapArea N β) (StripWidth.bulkExp N β) := by
    unfold StripWidth.seedSide
    nlinarith
  have hSS : StripWidth.seedSide (gapArea N β) (StripWidth.bulkExp N β)
      ≤ StripWidth.seedSide (gapArea N β) (StripWidth.bulkExp N β) ^ 2 := by nlinarith
  unfold StripWidth.tPoly tGlue
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The glued strip still stops short of the diagonal**: `t_glue(N, β) ≤ 1/(16192 (7800 (N + 4) β + 2))`, so
`t_glue/β → 0` as `β → ∞`. DERIVED: `A_glue ≥ 2 + 52 ℓ`, `ℓ ≥ 150 (N + 4) β`; `7800 = 52 · 150`; `16192`
as in `tGlue`. -/
theorem tGlue_le {β : ℝ} (hβ : 0 ≤ β) :
    tGlue N β ≤ 1 / (16192 * (7800 * ((N : ℝ) + 4) * β + 2)) := by
  have hl240 : (240 : ℝ) ≤ gapArea N β := gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (gapArea N β) := Real.log_nonneg (by linarith)
  have hL := StripWidth.bulkExp_nonneg (N := N) β
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl : 150 * ((N : ℝ) + 4) * β ≤ gapArea N β := by
    unfold gapArea
    nlinarith
  have hA : 7800 * ((N : ℝ) + 4) * β + 2 ≤ glueArea (gapArea N β) (StripWidth.bulkExp N β) := by
    unfold glueArea
    have h1 : 0 ≤ gapArea N β * (2 * StripWidth.bulkExp N β + 2 * Real.log (gapArea N β)) := by positivity
    nlinarith
  unfold tGlue
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

end MassGap.StripWiden

#print axioms MassGap.StripWiden.dens_Pop
#print axioms MassGap.StripWiden.Pop_Pop
#print axioms MassGap.StripWiden.Pop_Fk
#print axioms MassGap.StripWiden.Fk_Fk
#print axioms MassGap.StripWiden.prodR_inv
#print axioms MassGap.StripWiden.mp_prodL
#print axioms MassGap.StripWiden.oc_explicit
#print axioms MassGap.StripWiden.row_eq
#print axioms MassGap.StripWiden.rowsE_mp
#print axioms MassGap.StripWiden.rowP_mp
#print axioms MassGap.StripWiden.ratio_eq
#print axioms MassGap.StripWiden.ratio_glue
#print axioms MassGap.StripWiden.ratio_glue_le
#print axioms MassGap.StripWiden.seed_glue
#print axioms MassGap.StripWiden.strip_of_glue
#print axioms MassGap.StripWiden.strip_width_glue
#print axioms MassGap.StripWiden.tGlue_pos
#print axioms MassGap.StripWiden.tPoly_le_tGlue
#print axioms MassGap.StripWiden.tGlue_le
