import Mathlib
import MassGap.BulkBound

/-!
# MassGap.SunFamFlux — sign configurations are fixed by the `SU(N)` block step; `(M_W)` fails at `sunFam`

`BulkBound.facV_le_of_MW` turns the observer's moment condition `ObserverMultigrid.MW W` into a deterministic
bound `N − Re tr (W.V k U)_p ≤ a_k²` on the flowed origin plaquette at every input `U`, and
`BulkBound.not_MW_blFam` refutes it at the ray-averaged observer by a `π`-flux fixed point. This module gives
the same fixed point for the polar block step `ObserverFlowSUN.sunBlockStep`, and with it the no-go at the two
observers built from that step: the box observer `ObserverFlowSUN.sunFam` (the observer of the tower chain)
and the multigrid observer `ObserverMultigrid.mgFam`. Declarations are in the namespace
`MassGap.SunFamFlux`.

## 1. The block step at a sign link (proved)

A point `z` of the circle is a sign when `Im z = 0`, i.e. `z = ±1`. `sunStep_dg_sign`: for a sign `z` and
six sign staples `vᵢ`, `sunStep (D(z)) (D(vᵢ)) = D(z)`, `D(z) = diag(z, z̄, 1, …, 1)`. The block matrix is
`diag(w, w̄, 1 + 6c, …)` with `w = z + c Σ vᵢ = (1 + c Σ vᵢ z) z` (`ObserverBlock.blockMatI_dg`), and
`1 + c Σ vᵢ z ≥ 1 − 6c > 0`, so its projection is `D(w/|w|) = D(z)` (`ObserverBlock.projMat_dv`). The bound
`6c < 1` is read from the construction bound `12 c < sin(π/N)` of `sunBlockStep` itself (`sin ≤ 1`); no
further condition on `c` enters.

## 2. Sign configurations are fixed (proved)

`SignConf Z`: every link of the circle configuration `Z` is a sign. Products and inverses of signs are signs,
so every plaquette staple (`ObserverFlowSUN.stapleG`) and every strided staple (`ObserverMultigrid.stapleD`)
of a sign configuration is a sign. Hence:

* **`stepConf_sign`**: the plaquette smearing step `stepConf (sunBlockStep …)` fixes `dgConf Z`;
* **`sunFam_V_sign`**: every member of `sunFam hN c hc0 hc s`, at every step `k`, fixes `dgConf Z` (each local
  step `stepOn` is the identity on a fixed point of `stepConf`, whatever the box);
* **`mgStep_sign`**, **`mgFam_V_sign`**: the strided step at every stride and every member of
  `mgFam hN c hc0 hc m s` fix `dgConf Z`.

The `π`-flux configuration `dgConf (zeta fpi)` of `BulkBound` is a sign configuration (`signConf_zeta_fpi`),
with `N − Re tr = 4` at the origin plaquette (`BulkBound.facV_fpi`).

## 3. The no-go (proved)

Since `a_k → 0`, the bound `4 ≤ a_k²` fails eventually:

* **`not_MW_sunFam`**, **`not_MW_mgFam`**: `¬ MW (sunFam hN c hc0 hc s)` and `¬ MW (mgFam hN c hc0 hc m s)` at
  every `N ≥ 2`, `c`, `m`, `s`.
* **`not_scaleControlAll_sunFam_of_one_le`**, **`not_scaleControlAll_mgFam_of_one_le`**: no family `Wf` with
  `Wf 1` the observer meets `ScaleControlAll b` at any `b ≥ 1` (`BulkBound.facV_le_of_scaleControlAll`).
* **`not_substrateCoreAt_sunFam_one`**: `¬ SU2Best.SubstrateCoreAt (sunFam hN c hc0 hc s) z 1 Wf` for every
  `z`, `Wf` (through `top`, `Wf 1 = sunFam …`).

What this leaves open: the core `SubstrateCoreAt (sunFam …) z b Wf` at `b ≠ 1`. It reads `Wf 1` only through
`ScaleControlAll b` at `b ≥ 1`, where `Wf 1` is free (`top` fixes `Wf b`), and at `b < 1` it never reads
`Wf 1`; there the factor `(1 + |log b|)^{γ_j}` is free per channel (`BulkBound` §5).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the imaginary part of a sign, the plane and the origin; `1` the unit, the scale and
the bound `sin ≤ 1`; `2` the least rank, the squared spacing and the two entries `z`, `z̄`; `4` the `π`-flux
defect; `6` the staple count; `π` in `π/N` the angle of the centre of `SU(N)` and the staggered phase; `12`
the construction bound of `sunBlockStep`, inherited.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SunFamFlux

open MassGap.SUN (SU)
open MassGap.InfiniteLattice MassGap.ContinuumFlow MassGap.ContinuumSchwinger MassGap.MultiScaleAll
  MassGap.ObserverFlowSUN MassGap.ObserverMultigrid MassGap.ObserverBlock MassGap.BulkBound
open Filter Matrix

/-! ## 1. The block step at a sign link -/

section Step

/-- **A sign of the circle**: `Im z = 0`. DERIVED: `0` the imaginary part. -/
def IsSign (z : Circle) : Prop := ((z : ℂ)).im = 0

/-- DERIVED: no numeral. -/
theorem isSign_one : IsSign 1 := by simp [IsSign]

/-- DERIVED: no numeral. -/
theorem IsSign.mul {a b : Circle} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  unfold IsSign at *
  rw [Circle.coe_mul, Complex.mul_im, ha, hb]
  ring

/-- DERIVED: no numeral. -/
theorem IsSign.inv {a : Circle} (ha : IsSign a) : IsSign a⁻¹ := by
  unfold IsSign at *
  rw [Circle.coe_inv_eq_conj, Complex.conj_im, ha, neg_zero]

/-- A sign is its real part. DERIVED: no numeral. -/
theorem IsSign.eq_re {a : Circle} (ha : IsSign a) : (a : ℂ) = (((a : ℂ).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact ha)

/-- A sign squares to `1`. DERIVED: `1` the modulus; `2` the square. -/
theorem IsSign.re_sq {a : Circle} (ha : IsSign a) : (a : ℂ).re ^ 2 = 1 := by
  have h := Complex.normSq_apply (a : ℂ)
  rw [Complex.normSq_eq_norm_sq, Circle.norm_coe, ha] at h
  nlinarith

/-- `|Re a| ≤ 1` on the circle. DERIVED: `1` the modulus. -/
theorem abs_re_le_one (a : Circle) : |(a : ℂ).re| ≤ 1 := by
  have h := Complex.abs_re_le_norm (a : ℂ)
  rwa [Circle.norm_coe] at h

/-- **The averaged sum at a sign link with sign staples is a positive multiple of the link**:
`z + e Σ vᵢ = r z` with `r = 1 + e Σ Re vᵢ Re z > 0` when `#ι · e < 1`. DERIVED: `0` the sign; `1` the
unit and the weight bound. -/
theorem sign_avg {ι : Type} [Fintype ι] {z : Circle} (hz : IsSign z) {v : ι → Circle}
    (hv : ∀ i, IsSign (v i)) {e : ℝ} (he0 : 0 ≤ e) (he : (Fintype.card ι : ℝ) * e < 1) :
    ∃ r : ℝ, 0 < r ∧ (z : ℂ) + (e : ℂ) * ∑ i, (v i : ℂ) = (r : ℂ) * z := by
  have hx2 : (z : ℂ).re ^ 2 = 1 := hz.re_sq
  have hxa : |(z : ℂ).re| ≤ 1 := abs_re_le_one z
  refine ⟨1 + e * ∑ i, (v i : ℂ).re * (z : ℂ).re, ?_, ?_⟩
  · have hlo : -(Fintype.card ι : ℝ) ≤ ∑ i, (v i : ℂ).re * (z : ℂ).re := by
      calc -(Fintype.card ι : ℝ) = ∑ _i : ι, (-1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => by
            have h1 := abs_re_le_one (v i)
            have h2 : |(v i : ℂ).re * (z : ℂ).re| ≤ 1 := by
              rw [abs_mul]
              exact mul_le_one₀ h1 (abs_nonneg _) hxa
            linarith [neg_abs_le ((v i : ℂ).re * (z : ℂ).re)]
    nlinarith [mul_le_mul_of_nonneg_left hlo he0]
  · have hzc : (z : ℂ) = (((z : ℂ).re : ℝ) : ℂ) := hz.eq_re
    have hvi : ∀ i, (v i : ℂ) = (((v i : ℂ).re : ℝ) : ℂ) := fun i => (hv i).eq_re
    have hxx : (((z : ℂ).re : ℝ) : ℂ) * (((z : ℂ).re : ℝ) : ℂ) = 1 := by
      have h : (z : ℂ).re * (z : ℂ).re = 1 := by nlinarith
      exact_mod_cast h
    calc (z : ℂ) + (e : ℂ) * ∑ i, (v i : ℂ)
        = (((z : ℂ).re : ℝ) : ℂ) + (e : ℂ) * ∑ i, (((v i : ℂ).re : ℝ) : ℂ) := by
          exact congrArg₂ (· + ·) hzc
            (congrArg ((e : ℂ) * ·) (Finset.sum_congr rfl fun i _ => hvi i))
      _ = ((1 + e * ∑ i, (v i : ℂ).re * (z : ℂ).re : ℝ) : ℂ) * (((z : ℂ).re : ℝ) : ℂ) := by
          push_cast
          rw [add_mul, one_mul, mul_assoc, Finset.sum_mul]
          congr 2
          exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hxx, mul_one]
      _ = _ := by rw [← hzc]

/-- A positive multiple of a circle point has phase that point. DERIVED: `0` the sign. -/
theorem div_norm_of_eq {z : Circle} {w : ℂ} {r : ℝ} (hr : 0 < r) (hw : w = (r : ℂ) * z) :
    w / (‖w‖ : ℂ) = z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn : ‖w‖ = r := by
    rw [hw, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hn, hw, mul_div_cancel_left₀ _ hr0]

variable {n : ℕ}

/-- **The `SU(N)` block step fixes a sign link with sign staples**: `sunStep (D z) (D vᵢ) = D z`.
DERIVED: `2` the least rank; `6` the staple count; `1` the bound `sin ≤ 1`; `12` the construction bound,
inherited. -/
theorem sunStep_dg_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) {z : Circle} (hz : IsSign z)
    {v : Fin 6 → Circle} (hv : ∀ i, IsSign (v i)) :
    sunStep hN c hc0 hc (dgHom z) (fun i => dgHom (v i)) = dgHom z := by
  have h6 : (Fintype.card (Fin 6) : ℝ) * c < 1 := by
    rw [Fintype.card_fin]
    push_cast
    linarith [Real.sin_le_one (Real.pi / ((n + 2 : ℕ) : ℝ))]
  obtain ⟨r, hr, hw⟩ := sign_avg hz hv hc0 h6
  have hwne : (z : ℂ) + (c : ℂ) * ∑ i, (v i : ℂ) ≠ 0 := by
    rw [hw]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Circle.coe_ne_zero _)
  have hr' : (0 : ℝ) < 1 + c * Fintype.card (Fin 6) := by positivity
  apply Subtype.ext
  show projMat (blockMatI c (dgHom (n := n) z) (fun q => dgHom (v q)))
    = ((dgHom (n := n) z : SU (n + 2)) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
  rw [blockMatI_dg, projMat_dv hwne hr', dgHom_coe, div_norm_of_eq hr hw]

end Step

/-! ## 2. Sign configurations are fixed -/

section Conf

/-- **A sign configuration**: every link is a sign. DERIVED: no numeral. -/
def SignConf (Z : IConf Circle) : Prop := ∀ l, IsSign (Z l)

/-- DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem stapleG_map {G H : Type} [Group G] [Group H] (φ : G →* H) (U : IConf G) (μ : Fin 4) (x : ISite)
    (p : Fin 3 × Fin 2) : stapleG (fun l => φ (U l)) μ x p = φ (stapleG U μ x p) := by
  unfold stapleG
  split_ifs <;> simp only [map_mul, map_inv]

/-- DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem isSign_stapleG {Z : IConf Circle} (hZ : SignConf Z) (μ : Fin 4) (x : ISite) (p : Fin 3 × Fin 2) :
    IsSign (stapleG Z μ x p) := by
  unfold stapleG
  split_ifs
  · exact ((hZ _).mul (hZ _)).mul (hZ _).inv
  · exact ((hZ _).inv.mul (hZ _)).mul (hZ _)

/-- DERIVED: `0` the empty path. -/
theorem isSign_ptr {Z : IConf Circle} (hZ : SignConf Z) (ν : Fin 4) (t : ℕ) (x : ISite) :
    IsSign (ptr Z ν t x) := by
  induction t generalizing x with
  | zero => exact isSign_one
  | succ t ih => rw [ptr_succ]; exact (hZ _).mul (ih _)

/-- DERIVED: `0` names the upper side; `3 = 4 − 1` the transverse directions. -/
theorem isSign_stapleD {Z : IConf Circle} (hZ : SignConf Z) (d : ℕ) (μ : Fin 4) (x : ISite)
    (p : Fin 3 × Fin 2) : IsSign (stapleD Z d μ x p) := by
  unfold stapleD
  split_ifs
  · exact ((isSign_ptr hZ _ _ _).mul (hZ _)).mul (isSign_ptr hZ _ _ _).inv
  · exact ((isSign_ptr hZ _ _ _).inv.mul (hZ _)).mul (isSign_ptr hZ _ _ _)

variable {n : ℕ}

/-- **The plaquette smearing step fixes every sign configuration.** DERIVED: `2` the least rank; `12` the
construction bound, inherited. -/
theorem stepConf_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) {Z : IConf Circle} (hZ : SignConf Z) :
    stepConf (sunBlockStep hN c hc0 hc) (dgConf Z) = dgConf Z := by
  funext l
  show sunStep hN c hc0 hc (dgHom (Z l))
      (fun i => stapleG (fun l => dgHom (Z l)) l.1 l.2 (finProdFinEquiv.symm i)) = dgHom (Z l)
  simp only [stapleG_map]
  exact sunStep_dg_sign hN hc0 hc (hZ l) (fun i => isSign_stapleG hZ _ _ _)

/-- **A local step fixes a fixed point of the global step**, whatever the set of links.
DERIVED: no numeral. -/
theorem stepOn_fixed {G : Type} [Group G] [TopologicalSpace G] (B : BlockStep G) (S : Set ILink)
    {U : IConf G} (h : stepConf B U = U) : stepOn B S U = U := by
  classical
  funext l
  unfold stepOn
  split_ifs
  · exact congrFun h l
  · rfl

/-- **The box observer flow fixes a fixed point of the step**, at every step count and box.
DERIVED: no numeral. -/
theorem obsFlowG_fixed {G : Type} [Group G] [TopologicalSpace G] (B : BlockStep G) (m R : ℕ)
    {U : IConf G} (h : stepConf B U = U) : obsFlowG B m R U = U := by
  funext l
  show (stepOn B (MassGap.ObserverFlow.mbox l R))^[m] U l = U l
  rw [Function.iterate_fixed (stepOn_fixed B _ h) m]

/-- **Every member of `sunFam` fixes every sign configuration**, at every step.
DERIVED: `2` the least rank; `12` the construction bound, inherited. -/
theorem sunFam_V_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (s : ℝ) (k : ℕ) {Z : IConf Circle}
    (hZ : SignConf Z) : (sunFam hN c hc0 hc s).V k (dgConf Z) = dgConf Z :=
  obsFlowG_fixed _ _ _ (stepConf_sign hN hc0 hc hZ)

/-- **The strided step fixes every sign configuration**, at every stride. DERIVED: `2` the least rank;
`12` the construction bound, inherited. -/
theorem mgStep_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (d : ℕ) {Z : IConf Circle}
    (hZ : SignConf Z) : mgStep (sunBlockStep hN c hc0 hc) d (dgConf Z) = dgConf Z := by
  funext l
  show sunStep hN c hc0 hc (dgHom (Z l))
      (fun i => stapleD (fun l => dgHom (Z l)) d l.1 l.2 (finProdFinEquiv.symm i)) = dgHom (Z l)
  simp only [stapleD_map]
  exact sunStep_dg_sign hN hc0 hc (hZ l) (fun i => isSign_stapleD hZ _ _ _ _)

/-- **The multigrid map fixes every sign configuration.** DERIVED: `0` no level; `2` the stride ratio and
the least rank; `12` the construction bound, inherited. -/
theorem mgMap_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m J : ℕ) {Z : IConf Circle}
    (hZ : SignConf Z) : mgMap (sunBlockStep hN c hc0 hc) m J (dgConf Z) = dgConf Z := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [mgMap_succ, Function.comp_apply, ih]
    exact Function.iterate_fixed (mgStep_sign hN hc0 hc _ hZ) m

/-- **Every member of `mgFam` fixes every sign configuration**, at every step.
DERIVED: `2` the least rank; `12` the construction bound, inherited. -/
theorem mgFam_V_sign (hN : 2 ≤ n + 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / ((n + 2 : ℕ) : ℝ))) (m : ℕ) (s : ℝ) (k : ℕ) {Z : IConf Circle}
    (hZ : SignConf Z) : (mgFam hN c hc0 hc m s).V k (dgConf Z) = dgConf Z :=
  mgMap_sign hN hc0 hc m _ hZ

/-- **The `π`-flux slice configuration is a sign configuration.** DERIVED: `1` the slice direction. -/
theorem signConf_zeta_fpi : SignConf (zeta fpi) := by
  intro l
  unfold zeta
  split_ifs
  · exact fpi_im _
  · exact isSign_one

end Conf

/-! ## 3. The no-go -/

section NoGo

/-- The `π`-flux bound `4 ≤ a_k²` fails eventually. DERIVED: `2` the squared spacing and the least
rank; `4` the `π`-flux defect. -/
private theorem pi_flux_contra {n : ℕ} (hev : ∀ᶠ k in atTop, (4 : ℝ) ≤ dySpacing (n + 2) k ^ 2) : False := by
  have hsmall : ∀ᶠ k in atTop, dySpacing (n + 2) k < 2 :=
    (tendsto_dySpacing (n + 2)).eventually (gt_mem_nhds two_pos)
  obtain ⟨k, hk, hk2⟩ := (hev.and hsmall).exists
  have ha := dySpacing_pos (by omega : 1 ≤ n + 2) k
  nlinarith

/-- **`(M_W)` fails at every member of `sunFam`.** DERIVED: `2` the least rank; `4` the `π`-flux defect;
`12` the construction bound, inherited. -/
theorem not_MW_sunFam {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (s : ℝ) : ¬ MW (sunFam hN c hc0 hc s) := by
  intro hM
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine pi_flux_contra (n := n) ((facV_le_of_MW hM).mono fun k hk => ?_)
  have h := hk (dgConf (zeta fpi))
  rwa [sunFam_V_sign hN hc0 hc s k signConf_zeta_fpi, facV_fpi] at h

/-- **`(M_W)` fails at every member of `mgFam`.** DERIVED: `2` the least rank; `4` the `π`-flux defect;
`12` the construction bound, inherited. -/
theorem not_MW_mgFam {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) : ¬ MW (mgFam hN c hc0 hc m s) := by
  intro hM
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine pi_flux_contra (n := n) ((facV_le_of_MW hM).mono fun k hk => ?_)
  have h := hk (dgConf (zeta fpi))
  rwa [mgFam_V_sign hN hc0 hc m s k signConf_zeta_fpi, facV_fpi] at h

/-- **No family with `Wf 1 = sunFam …` meets `ScaleControlAll b` at any `b ≥ 1`.**
DERIVED: `1` the scale; `2` the least rank; `4` the `π`-flux defect; `12` the construction bound,
inherited. -/
theorem not_scaleControlAll_sunFam_of_one_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (s : ℝ) {b : ℝ} (hb : 1 ≤ b) {Wf : ℝ → ConfFlow N}
    (h1 : Wf 1 = sunFam hN c hc0 hc s) : ¬ ScaleControlAll b Wf := by
  intro h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine pi_flux_contra (n := n) ((facV_le_of_scaleControlAll hb h).mono fun k hk => ?_)
  have h' := hk (dgConf (zeta fpi))
  rwa [h1, sunFam_V_sign hN hc0 hc s k signConf_zeta_fpi, facV_fpi] at h'

/-- **No family with `Wf 1 = mgFam …` meets `ScaleControlAll b` at any `b ≥ 1`.**
DERIVED: `1` the scale; `2` the least rank; `4` the `π`-flux defect; `12` the construction bound,
inherited. -/
theorem not_scaleControlAll_mgFam_of_one_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (m : ℕ) (s : ℝ) {b : ℝ} (hb : 1 ≤ b) {Wf : ℝ → ConfFlow N}
    (h1 : Wf 1 = mgFam hN c hc0 hc m s) : ¬ ScaleControlAll b Wf := by
  intro h
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine pi_flux_contra (n := n) ((facV_le_of_scaleControlAll hb h).mono fun k hk => ?_)
  have h' := hk (dgConf (zeta fpi))
  rwa [h1, mgFam_V_sign hN hc0 hc m s k signConf_zeta_fpi, facV_fpi] at h'

/-- **No substrate core at `sunFam …` with scale `b = 1`**, for every `z` and `Wf`.
DERIVED: `1` the scale; `2` the least rank; `12` the construction bound, inherited. -/
theorem not_substrateCoreAt_sunFam_one {N : ℕ} [NeZero N] (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (s : ℝ) (z : MassGap.ClayData.Chan → ℕ → ℝ)
    (Wf : ℝ → ConfFlow N) : ¬ MassGap.SU2Best.SubstrateCoreAt (sunFam hN c hc0 hc s) z 1 Wf := fun S =>
  not_scaleControlAll_sunFam_of_one_le hN hc0 hc s le_rfl S.top S.scale

end NoGo

end MassGap.SunFamFlux

end

#print axioms MassGap.SunFamFlux.sign_avg
#print axioms MassGap.SunFamFlux.sunStep_dg_sign
#print axioms MassGap.SunFamFlux.stepConf_sign
#print axioms MassGap.SunFamFlux.sunFam_V_sign
#print axioms MassGap.SunFamFlux.mgStep_sign
#print axioms MassGap.SunFamFlux.mgFam_V_sign
#print axioms MassGap.SunFamFlux.signConf_zeta_fpi
#print axioms MassGap.SunFamFlux.not_MW_sunFam
#print axioms MassGap.SunFamFlux.not_MW_mgFam
#print axioms MassGap.SunFamFlux.not_scaleControlAll_sunFam_of_one_le
#print axioms MassGap.SunFamFlux.not_scaleControlAll_mgFam_of_one_le
#print axioms MassGap.SunFamFlux.not_substrateCoreAt_sunFam_one
