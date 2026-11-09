import Mathlib
import MassGap.CondGap
import MassGap.CubeFlux

/-!
# MassGap.CurveFloor — the curvature floor under zoom, and what the 4D geometry adds

The only gauge-invariant, parameter-free quantity in the tree that is zero for `U(1)` and positive for
`SU(N)` is the Ricci curvature of the group (`CondGap.beConst`: `Ric = N/4` on `SU(N)`, `0` on the circle).
This module asks whether that floor survives zoom and whether it separates the groups. Declarations are in
the namespace `MassGap.CurveFloor`.

## 1. The floor in the chain picture (proved)

This section is the one-dimensional picture: one class variable diffusing in the group, the picture of a
chain or of a bond-moved (Migdal–Kadanoff) step, where composing independent steps adds diffusion times.

* `ricSU_eq`, `ricU1_eq`, `ricSU_pos`: the curvature read off `CondGap.beConst` at `H = 0`, `β = 0` is
  `N/4` for `SU(N)` and `0` for `U(1)`; positive for `N > 0`.
* `modelConst R t = 1/t + R`, the model curvature constant at diffusion time `t`. `zoomTime t k = t·2^k`;
  `zoomTime_succ`: one doubling is two equal steps whose times add.
* `su_floor`: for `SU(N)` the constant exceeds `N/4` at every zoom and tends to `N/4 > 0`.
  `u1_no_floor`: for `U(1)` it tends to `0` and drops below every `ε > 0`.
* `heatConst R t = R/(1 − e^{−Rt})`, the closed form of the curvature constant of the heat semigroup at
  time `t` (the local log-Sobolev constant under `Ric ≥ R` has this form up to the convention factor `2` in
  the exponent, which rescales `t`; cited). `heatConst_bounds`: `max(R, 1/t) ≤ heatConst R t ≤ 1/t + R`,
  from `1 + x ≤ eˣ` alone. `heatConst_tendsto`: it tends to `R` along every zoom. So the model of the
  previous point and the closed form have the same floor.

## 2. The floor separates the bound, not the gap (proved)

* `circle_mode_decay`: a non-constant character `e^{inθ}` of the circle decays under the heat semigroup
  by `e^{−n²t} ≤ e^{−t}`. `su2_mode_decay`: a non-trivial character of `SU(2)` (unit `S³`) by
  `e^{−((k+1)²−1)t} ≤ e^{−3t}`. `mode_semigroup`: the decay factors compose by adding times.
  `circle_gap_every_zoom`: at every zoom every non-constant circle mode is below `e^{−t}`.

So in the chain picture both groups contract their non-constant class modes at a positive rate (`1` and
`3`) at every zoom. The curvature floor is a sufficient condition (Bakry–Émery) whose `U(1)` value is `0`
while the `U(1)` gap is not. In the chain picture `U(1)` disorders, as `BondMove`/`OneWayCost` record for
the Migdal–Kadanoff flow. The curvature floor survives zoom; it does not separate the groups.

## 3. What the 4D geometry adds for `U(1)` (proved)

* `closedForms G d N`: for a commutative group, the face functions with trivial plain cube product at
  every cube (closed 2-forms). It is a subgroup (`cubeFlux_inv`, `CubeFlux.cubeFlux_mul`); in angle
  coordinates, for a torus group, a linear subspace.
* `plaquette_closed`: every abelian plaquette field lies in it (`CubeFlux.bianchi_comm`).
* `single_not_closed`, `closedForms_ne_top`: on a side `N ≥ 2` with directions `i ≠ j`, `k ≠ i` it is a
  proper subgroup: one non-trivial face alone is not closed. The abelian plaquette field is confined to a
  proper linear subspace; this is the constraint that the chain picture drops.
* `sig_triple`, `trace_sigA`, `trace_sigB`, `trace_sigC`: in `SU(2)` the three elements `iσ₃`, `iσ₂` and
  `sigC = (iσ₃ iσ₂)⁻¹` have trace `0` and product `1`. `circle_no_triple`: in `U(1)` no three elements of
  real part `0` have product `1` (each squares to `−1`). Traces are conjugation invariant, so the traces
  `0, 0, 0` are class data. The product relation of the representatives is not gauge invariant, and the
  transported Bianchi identity holds in every group. This only shows that three trace-zero `SU(2)`
  elements can have product `1` while three `U(1)` elements of real part `0` cannot. It is not shown to
  describe lattice class data.

## 4. The remaining inequality (named, not proved)

* `BlockBE N H βeff`: a positive Bakry–Émery constant `N/4 − βeff k · H ≥ c > 0` for the effective
  single-block law at every zoom `k`. `blockBE_iff`: it is exactly a uniform bound
  `βeff k ≤ (N/4 − c)/H` on the effective block coupling. `not_blockBE_of_tendsto`: it fails along any
  coupling sequence tending to `∞` (bare couplings of the asymptotically free regime).
  `not_blockBE_U1`: at `Ric = 0` it fails as soon as one effective coupling is non-negative.

`BlockBE` with `βeff` the effective coupling of the Wilson block law is a strong-coupling statement at the
block scale: the effective coupling stays below `N/(4H)` along the zoom. `BlockBE` restates strong
coupling at the block scale. It is not connected to `ZoomStep.WilsonZoomStep` or to
`CouplingTower.windowCoupling`, and `βeff` is not defined from the Wilson measure.

## What does not follow

* `ZoomStep.WilsonZoomStep N` or `CouplingTower.StrongEnd N`. No implication from `BlockBE` (or from any
  curvature statement here) to either is proved; `βeff` is not defined from the Wilson measure.
* A separation of `SU(N)` from `U(1)` by the curvature floor. In the chain picture both groups have a
  positive gap at every zoom (section 2); the floor separates only the Bakry–Émery bound.
* That the abelian closed-form constraint keeps the Coulomb phase. That needs the spin-wave analysis
  (Guth; Fröhlich–Spencer), cited, not formalised. The `SU(2)` escape of section 3 is a relation among
  three group elements, not realised on a lattice cube, and is not shown to make the non-abelian field
  disorder.
* The Laplacian eigenvalues `n²` and `(k+1)² − 1` are inherited (the circle's characters and the
  archived `HeatKernelStiffening`); `heatConst` as the semigroup's log-Sobolev constant is cited.

DERIVED (module-wide): `0` the curvature of the circle, the signs and the bounds; `1` the unit of the
group, the circle gap `1²` and the unit in `1 + x ≤ eˣ`; `2` the doubling of `zoomTime` and the matrix
size of `SU(2)`; `3 = 2² − 1` the first Laplacian eigenvalue on the unit `S³`; `4` in `N/4` the Ricci
constant of `SU(N)` (inherited from `CondGap`); `2` in `N ≥ 2` the least torus side on which the cube's
faces are distinct (`CubeFlux.finRotate_ne_self`). CHOSEN: the triple `iσ₃`, `iσ₂`, `sigC`
(`GapSideTwistFlat.sigA`, `sigB` and their product's inverse).
-/

noncomputable section

namespace MassGap.CurveFloor

open Filter Topology
open MassGap.CondGap MassGap.CubeFlux MassGap.TorusDoubling MassGap.HolderBondMoving
open MassGap.GapSideTwistFlat (sigA sigB)

/-! ## 1. The floor in the chain picture -/

section Floor

/-- **The Ricci constant of `SU(N)`** in `CondGap`'s normalisation: `beConst` at `H = 0`, `β = 0`. -/
def ricSU (N : ℝ) : ℝ := beConst N 0 0

/-- **The Ricci constant of `U(1)`**: `beConst` on the torus at `H = 0`, `β = 0`. -/
def ricU1 : ℝ := beConst 0 0 0

/-- DERIVED: `4` the Ricci constant normalisation of `CondGap`. -/
theorem ricSU_eq (N : ℝ) : ricSU N = N / 4 := by unfold ricSU beConst; ring

theorem ricU1_eq : ricU1 = 0 := by unfold ricU1 beConst; ring

theorem ricSU_pos {N : ℝ} (hN : 0 < N) : 0 < ricSU N := by rw [ricSU_eq]; positivity

/-- **The model curvature constant** at diffusion time `t`: `1/t + R`. -/
def modelConst (R t : ℝ) : ℝ := t⁻¹ + R

/-- **The zoom time**: `k` doublings of the diffusion time `t`. DERIVED: `2` the doubling. -/
def zoomTime (t : ℝ) (k : ℕ) : ℝ := t * 2 ^ k

/-- **One doubling adds two equal times.** -/
theorem zoomTime_succ (t : ℝ) (k : ℕ) : zoomTime t (k + 1) = zoomTime t k + zoomTime t k := by
  unfold zoomTime; ring

theorem zoomTime_pos {t : ℝ} (ht : 0 < t) (k : ℕ) : 0 < zoomTime t k := by
  unfold zoomTime; positivity

theorem zoomTime_ge {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : t ≤ zoomTime t k := by
  unfold zoomTime
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith

theorem zoomTime_tendsto {t : ℝ} (ht : 0 < t) : Tendsto (zoomTime t) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop ht

theorem modelConst_gt {R t : ℝ} (ht : 0 < t) : R < modelConst R t := by
  unfold modelConst; have := inv_pos.2 ht; linarith

theorem modelConst_tendsto (R : ℝ) {ts : ℕ → ℝ} (h : Tendsto ts atTop atTop) :
    Tendsto (fun k => modelConst R (ts k)) atTop (𝓝 R) := by
  have := (tendsto_inv_atTop_zero.comp h).add_const R
  simpa [modelConst, Function.comp] using this

/-- **`SU(N)`: a positive floor at every zoom.** -/
theorem su_floor {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    (∀ k : ℕ, N / 4 < modelConst (ricSU N) (zoomTime t k)) ∧
      Tendsto (fun k => modelConst (ricSU N) (zoomTime t k)) atTop (𝓝 (N / 4)) ∧ 0 < N / 4 := by
  refine ⟨fun k => ?_, ?_, by positivity⟩
  · rw [← ricSU_eq]; exact modelConst_gt (zoomTime_pos ht k)
  · rw [← ricSU_eq]; exact modelConst_tendsto _ (zoomTime_tendsto ht)

/-- **`U(1)`: no floor.** The constant tends to `0` and drops below every `ε > 0`. -/
theorem u1_no_floor {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => modelConst ricU1 (zoomTime t k)) atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, modelConst ricU1 (zoomTime t k) < ε := by
  have h := modelConst_tendsto ricU1 (zoomTime_tendsto ht)
  rw [ricU1_eq] at h ⊢
  exact ⟨h, fun ε hε => (h.eventually (gt_mem_nhds hε)).exists⟩

/-- **The closed-form curvature constant of the heat semigroup**: `R/(1 − e^{−Rt})`. -/
def heatConst (R t : ℝ) : ℝ := R / (1 - Real.exp (-(R * t)))

/-- **The closed form is sandwiched**: `R ≤ heatConst R t`, `1/t ≤ heatConst R t`,
`heatConst R t ≤ 1/t + R`. From `1 + x ≤ eˣ` only. -/
theorem heatConst_bounds {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    R ≤ heatConst R t ∧ t⁻¹ ≤ heatConst R t ∧ heatConst R t ≤ modelConst R t := by
  set e := Real.exp (-(R * t)) with he_def
  have hx : 0 < R * t := mul_pos hR ht
  have he1 : e < 1 := by
    have := Real.exp_lt_exp.2 (show -(R * t) < 0 by linarith)
    simpa [he_def] using this
  have hd : 0 < 1 - e := by linarith
  have hep : 0 < e := Real.exp_pos _
  have h1 : -(R * t) + 1 ≤ e := Real.add_one_le_exp _
  have h2 : R * t + 1 ≤ Real.exp (R * t) := Real.add_one_le_exp _
  have hprod : e * Real.exp (R * t) = 1 := by rw [he_def, ← Real.exp_add]; simp
  have key : (R * t + 1) * e ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right h2 hep.le]
  unfold heatConst modelConst
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [le_div_iff₀ hd]
    calc t⁻¹ * (1 - e) ≤ t⁻¹ * (R * t) :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 ht.le)
      _ = R := by field_simp
  · rw [div_le_iff₀ hd]
    have hm : R * e ≤ t⁻¹ * (1 - e) := by
      rw [← div_eq_inv_mul, le_div_iff₀ ht]; nlinarith
    have : (t⁻¹ + R) * (1 - e) = t⁻¹ * (1 - e) + R - R * e := by ring
    linarith

/-- **The closed form tends to `R` along every zoom.** -/
theorem heatConst_tendsto {R : ℝ} (hR : 0 < R) {ts : ℕ → ℝ} (h : Tendsto ts atTop atTop) :
    Tendsto (fun k => heatConst R (ts k)) atTop (𝓝 R) := by
  have hpos : ∀ᶠ k in atTop, 0 < ts k := h.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (modelConst_tendsto R h) ?_ ?_
  · exact hpos.mono fun k hk => (heatConst_bounds hR hk).1
  · exact hpos.mono fun k hk => (heatConst_bounds hR hk).2.2

end Floor

/-! ## 2. The floor separates the bound, not the gap -/

section Gap

/-- **Heat decay factors compose by adding times.** -/
theorem mode_semigroup (lam s t : ℝ) :
    Real.exp (-(lam * s)) * Real.exp (-(lam * t)) = Real.exp (-(lam * (s + t))) := by
  rw [← Real.exp_add]; ring_nf

/-- **The circle gap**: a non-constant character decays by `e^{−n²t} ≤ e^{−t}`. DERIVED: `1` the
least `n²` over `n ≠ 0`. -/
theorem circle_mode_decay {n : ℤ} (hn : n ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((n : ℝ) ^ 2 * t)) ≤ Real.exp (-t) := by
  apply Real.exp_le_exp.2
  have h1 : (1 : ℤ) ≤ n ^ 2 := by nlinarith [sq_abs n, Int.one_le_abs hn]
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h1
  nlinarith

/-- **The `SU(2)` gap**: a non-trivial character decays by `e^{−((k+1)²−1)t} ≤ e^{−3t}`. DERIVED:
`3 = 2² − 1` at `k = 1`. -/
theorem su2_mode_decay {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((((k : ℝ) + 1) ^ 2 - 1) * t)) ≤ Real.exp (-(3 * t)) := by
  apply Real.exp_le_exp.2
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (3 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith
  nlinarith

/-- **The circle gap at every zoom**: every non-constant circle mode is below `e^{−t}`. -/
theorem circle_gap_every_zoom {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-((n : ℝ) ^ 2 * zoomTime t k)) ≤ Real.exp (-t) :=
  (circle_mode_decay hn (ht.trans (zoomTime_ge ht k))).trans
    (Real.exp_le_exp.2 (by linarith [zoomTime_ge ht k]))

end Gap

/-! ## 3. What the 4D geometry adds for `U(1)` -/

section Closed

variable {G : Type} [CommGroup G] {d N : ℕ}

/-- The plain cube product of the inverse face function is the inverse. -/
theorem cubeFlux_inv (F : TPlaq d N → G) (i j k : Fin d) (x : TSite d N) :
    cubeFlux (fun q => (F q)⁻¹) i j k x = (cubeFlux F i j k x)⁻¹ := by
  unfold cubeFlux
  simp only [mul_inv, inv_inv] <;> ac_rfl

variable (G d N) in
/-- **Closed 2-forms**: face functions with trivial plain cube product at every cube. -/
def closedForms : Subgroup (TPlaq d N → G) where
  carrier := {F | ∀ i j k x, cubeFlux F i j k x = 1}
  mul_mem' := by
    intro F F' hF hF'
    simp only [Set.mem_setOf_eq] at hF hF' ⊢
    intro i j k x
    exact (cubeFlux_mul F F' i j k x).trans (by rw [hF, hF', one_mul])
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro i j k x
    simp [cubeFlux]
  inv_mem' := by
    intro F hF
    simp only [Set.mem_setOf_eq] at hF ⊢
    intro i j k x
    exact (cubeFlux_inv F i j k x).trans (by rw [hF, inv_one])

/-- **The abelian plaquette field is closed** (`CubeFlux.bianchi_comm`). -/
theorem plaquette_closed (U : TLink d N → G) : (fun q => thol q U) ∈ closedForms G d N :=
  show ∀ i j k x, cubeFlux (fun q => thol q U) i j k x = 1 from
    fun i j k x => bianchi_comm i j k x U

/-- **One non-trivial face alone is not closed** on a side `N ≥ 2`. -/
theorem single_not_closed (hN : 2 ≤ N) {i j k : Fin d} (hij : i ≠ j) (hki : k ≠ i)
    (x : TSite d N) {g : G} (hg : g ≠ 1) :
    Pi.mulSingle ((i, j), x) g ∉ closedForms G d N := by
  intro h
  have h1 : cubeFlux (Pi.mulSingle ((i, j), x) g) i j k x = 1 :=
    (show ∀ a b c y, cubeFlux (Pi.mulSingle ((i, j), x) g) a b c y = 1 from h) i j k x
  have s : tshift k x ≠ x :=
    site_ne k (by simp only [tshift_self']; exact finRotate_ne_self hN _)
  apply hg
  rw [← h1]
  unfold cubeFlux
  simp [Ne.symm hij, hki, s]

/-- **The closed forms are a proper subgroup.** -/
theorem closedForms_ne_top (hN : 2 ≤ N) {i j k : Fin d} (hij : i ≠ j) (hki : k ≠ i)
    (x : TSite d N) {g : G} (hg : g ≠ 1) : closedForms G d N ≠ ⊤ := by
  intro h
  exact single_not_closed hN hij hki x hg (h ▸ Subgroup.mem_top _)

end Closed

section Escape

/-- `sigC = [[0, −i], [−i, 0]] = (iσ₃ · iσ₂)⁻¹`. -/
def sigC : SUN.SU 2 :=
  ⟨!![0, -Complex.I; -Complex.I, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- **Three trace-zero `SU(2)` elements with product `1`.** -/
theorem sig_triple : sigA * sigB * sigC = 1 := by
  apply Subtype.ext
  show (!![Complex.I, 0; 0, -Complex.I] * !![0, 1; -1, 0] * !![0, -Complex.I; -Complex.I, 0] :
    Matrix (Fin 2) (Fin 2) ℂ) = 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem trace_sigA : Matrix.trace (sigA : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  show Matrix.trace !![Complex.I, 0; 0, -Complex.I] = 0
  simp [Matrix.trace_fin_two]

theorem trace_sigB : Matrix.trace (sigB : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  show Matrix.trace (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace_fin_two]

theorem trace_sigC : Matrix.trace (sigC : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  show Matrix.trace (!![0, -Complex.I; -Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0
  simp [Matrix.trace_fin_two]

/-- A unit complex number of real part `0` squares to `−1`. -/
theorem sq_eq_neg_one {z : ℂ} (h1 : Complex.normSq z = 1) (h0 : z.re = 0) : z ^ 2 = -1 := by
  rw [Complex.normSq_apply, h0] at h1
  apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, h0] <;> nlinarith

/-- **No `U(1)` triple of real part `0` has product `1`.** -/
theorem circle_no_triple {z₁ z₂ z₃ : ℂ} (h₁ : Complex.normSq z₁ = 1) (r₁ : z₁.re = 0)
    (h₂ : Complex.normSq z₂ = 1) (r₂ : z₂.re = 0) (h₃ : Complex.normSq z₃ = 1) (r₃ : z₃.re = 0) :
    z₁ * z₂ * z₃ ≠ 1 := by
  intro h
  have hs : (z₁ * z₂ * z₃) ^ 2 = -1 := by
    rw [mul_pow, mul_pow, sq_eq_neg_one h₁ r₁, sq_eq_neg_one h₂ r₂, sq_eq_neg_one h₃ r₃]; norm_num
  rw [h] at hs
  have := congrArg Complex.re hs
  norm_num at this

end Escape

/-! ## 4. The remaining inequality -/

section Block

/-- **The block Bakry–Émery criterion**: a positive curvature constant `N/4 − βeff k · H ≥ c > 0` for
the effective single-block law at every zoom `k`. Named, not proved. -/
def BlockBE (N H : ℝ) (βeff : ℕ → ℝ) : Prop := ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ beConst N H (βeff k)

/-- **The block criterion is a uniform bound on the effective coupling.** -/
theorem blockBE_iff {N H : ℝ} (hH : 0 < H) (βeff : ℕ → ℝ) :
    BlockBE N H βeff ↔ ∃ c : ℝ, 0 < c ∧ ∀ k, βeff k ≤ (N / 4 - c) / H := by
  unfold BlockBE beConst
  refine exists_congr fun c => and_congr_right fun _ => forall_congr' fun k => ?_
  rw [le_div_iff₀ hH]
  constructor <;> intro h <;> linarith

/-- **It fails along couplings tending to `∞`.** -/
theorem not_blockBE_of_tendsto {N H : ℝ} (hH : 0 < H) {βeff : ℕ → ℝ}
    (h : Tendsto βeff atTop atTop) : ¬ BlockBE N H βeff := by
  rintro ⟨c, -, hk⟩
  obtain ⟨k, hk'⟩ := (((beConst_tendsto_atBot (N := N) hH).comp h).eventually
    (eventually_lt_atBot c)).exists
  exact absurd (hk k) (not_le.2 hk')

/-- **At `Ric = 0` it fails** as soon as one effective coupling is non-negative. -/
theorem not_blockBE_U1 {H : ℝ} (hH : 0 < H) {βeff : ℕ → ℝ} (h : ∃ k, 0 ≤ βeff k) :
    ¬ BlockBE 0 H βeff := by
  rintro ⟨c, hc, hk⟩
  obtain ⟨k, hβ⟩ := h
  have := hk k
  unfold beConst at this
  nlinarith [mul_nonneg hβ hH.le]

end Block

end MassGap.CurveFloor

#print axioms MassGap.CurveFloor.ricSU_eq
#print axioms MassGap.CurveFloor.ricU1_eq
#print axioms MassGap.CurveFloor.ricSU_pos
#print axioms MassGap.CurveFloor.zoomTime_succ
#print axioms MassGap.CurveFloor.zoomTime_pos
#print axioms MassGap.CurveFloor.zoomTime_ge
#print axioms MassGap.CurveFloor.zoomTime_tendsto
#print axioms MassGap.CurveFloor.modelConst_gt
#print axioms MassGap.CurveFloor.modelConst_tendsto
#print axioms MassGap.CurveFloor.su_floor
#print axioms MassGap.CurveFloor.u1_no_floor
#print axioms MassGap.CurveFloor.heatConst_bounds
#print axioms MassGap.CurveFloor.heatConst_tendsto
#print axioms MassGap.CurveFloor.mode_semigroup
#print axioms MassGap.CurveFloor.circle_mode_decay
#print axioms MassGap.CurveFloor.su2_mode_decay
#print axioms MassGap.CurveFloor.circle_gap_every_zoom
#print axioms MassGap.CurveFloor.cubeFlux_inv
#print axioms MassGap.CurveFloor.plaquette_closed
#print axioms MassGap.CurveFloor.single_not_closed
#print axioms MassGap.CurveFloor.closedForms_ne_top
#print axioms MassGap.CurveFloor.sig_triple
#print axioms MassGap.CurveFloor.trace_sigA
#print axioms MassGap.CurveFloor.trace_sigB
#print axioms MassGap.CurveFloor.trace_sigC
#print axioms MassGap.CurveFloor.sq_eq_neg_one
#print axioms MassGap.CurveFloor.circle_no_triple
#print axioms MassGap.CurveFloor.blockBE_iff
#print axioms MassGap.CurveFloor.not_blockBE_of_tendsto
#print axioms MassGap.CurveFloor.not_blockBE_U1
