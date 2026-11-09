import Mathlib
import MassGap.NoTransitionFlow
import MassGap.GapSideVortexRect
import MassGap.TwistDeficitUnionN

/-!
# MassGap.VortexCondense — centre-vortex condensation and the string-tension floor

The owner's route: "vortices condense: centre vortices (the `ℤ_N` twists) are free to multiply at
large scales and scramble long loops — that disorder forces the cost". This module formalises the
rigorous implication behind that picture as far as the tree carries it, and places it against the
open statement of `NoTransitionFlow` (one uniform chunk cost at every zoom, equivalently a
zoom-uniform floor on the string tension, `NoTransitionFlow.uniform_length_iff_floor`).

## Sources

* 't Hooft, Nucl. Phys. B 138 (1978) 1 and B 153 (1979) 141: the Wilson and 't Hooft loops as dual
  order parameters; the twisted partition function `Z(τ)`, `τ ∈ ℤ_N` on a coclosed plaquette set
  winding through every `[μν]`-plane of the periodic lattice.
* Mack and Petkova, Ann. Phys. 123 (1979) 442 and 125 (1980) 117: if the free energy of a `ℤ_N`
  vortex through a cross-section of area `A` decays fast enough in `A`, static quarks are confined
  (area law). Fröhlich, Phys. Lett. B 83 (1979) 195, and Yaffe, Phys. Rev. D 21 (1980) 1574, on the
  vortex free energy.
* Tomboulis and Yaffe, Commun. Math. Phys. 100 (1985) 313: for a reflection-positive plaquette action
  and a rectangle `C` in a `[12]`-plane, `⟨W(C)⟩ ≤ 2 (exp(−F_el))^{A_C/A}`, `A = L₁L₂` the area of
  the `[12]`-cross-section, `exp(−F_el) = ½ (1 − Z_−/Z)` for `SU(2)` (the `ℤ₂` Fourier transform of
  the vortex ratio), for `L₁ = 2^p l₁`, `L₂ = 2^q l₂` (Kanazawa, arXiv:0808.3442, Thm 1, eqs.
  (40)–(41)). As quoted in Kovács–Tomboulis, Phys. Rev. Lett. 85 (2000) 704 (hep-lat/0002004),
  eqs. (1)–(4), with the three behaviours (a) Higgs `exp(−F) ~ e^{−αL}`, (b) Coulomb
  `exp(−F) ~ e^{−βcL/A}`, (c) confinement `exp(−F) ~ exp(−cL e^{−ρA})`, `L = L₃L₄`.
* Borgs and Seiler, Commun. Math. Phys. 91 (1983) 329, on twisted boundary conditions.

## 1. The vortex free energy (`vfe`, `elw`)

`vfe Z Zt = −log(Zt/Z)` (`F_v`, the 't Hooft flux free energy), `elw Z Zt = 1 − Zt/Z` (twice the
electric weight `exp(−F_el)` at `SU(2)`). `elw_eq`: `elw = 1 − e^{−F_v}`; `elw_le_vfe`: `elw ≤ F_v`;
`elw_nonneg`, `vfe_nonneg`: `Zt ≤ Z` makes both non-negative.

## 2. Tomboulis–Yaffe, from its reflection-positivity input to the area law

* `Adm La Lb m n`: the `m × n` rectangle tiles the `La × Lb` cross-section (`m ∣ La`, `n ∣ Lb`) and
  does not wrap (`m < La`, `n < Lb`). The published proof uses the stronger condition `La = 2^p m`,
  `Lb = 2^q n` (the chessboard doublings); the numerics show the prefactor-free inequality failing for
  non-tiling rectangles of large area on the 2D torus.
* `TYBound W e La Lb`: `W m n ≤ e^{mn/(La Lb)}` for every admissible rectangle. This is a
  prefactor-free strengthening of the Tomboulis–Yaffe inequality on all tiling rectangles; the
  published form has prefactor `2`, base `½ (1 − Z_−/Z)`, and needs `La/m`, `Lb/n` powers of two
  (`TomboulisYaffe.tyTwo_of_chessboard`). No proof of the strengthening is known; the predicate
  carries it as an input.
* `area_of_ty`: `TYBound`, `0 ≤ e` and `e ≤ exp(−s La Lb)` give `W m n ≤ exp(−s mn)` on every
  admissible rectangle: no prefactor, the cross-section rate becomes the loop rate.
* `Condenses e A ρ`: for every `ρ' < ρ`, eventually along the box family `e K ≤ exp(−ρ' A K)` (the
  electric weight, or the vortex free energy, decays at rate `ρ` per unit cross-section area).
  `condenses_of_sublinear`: `F K ≤ e^{g K} e^{−ρ A K}` with `g/A → 0` and `A → ∞` (case (c) with
  `e^{g} = c L₃L₄` of size `e^{o(A)}`); `condenses_of_const`: the form `F ≤ C e^{−ρA}`.
  `Condenses.mono`, `condenses_elw_of_vfe`: a condensing `F_v` makes `elw` condense.
* `areaLaw_limit`: `TYBound` on every box of a family, `Condenses`, every rectangle eventually
  admissible, and the Wilson loops converging to `Winf` (the thermodynamic limit, an input) give
  `Winf m n ≤ exp(−ρ mn)` for all `m, n ≥ 1`.
* `HasTension W σ`: `W n n > 0` and `−log W(n,n)/n² → σ`. `le_tension_of_area`: an area law
  `W n n ≤ exp(−ρ n²)` gives `ρ ≤ σ`.
* `adm_factorial`, `tendsto_area_factorial`: the boxes of side `(K+1)!` make every rectangle eventually
  admissible and the area tend to infinity, so the family hypotheses are satisfiable.

## 3. The Wilson `SU(2)` torus

On the rectangular torus of `GapSideVortexRect` (`RectWilson.RSite L`, product Haar on the links):

* `rectWord`, `rectHol`, `wloopR`: the boundary word of the `m × n` rectangle in the plane `(a, b)` at
  the corner `o`, its holonomy, and `⟨½ Re tr U[C]⟩ = ⟨1 − wilsonDensity(U[C])⟩` in the Wilson
  measure. `wloopR_zero`: the empty rectangle reads `1`.
* `zR_Lc_le_one`: on the corner-step torus `Lc n i` (`n ≥ 2` even, `β ≥ 0`) the sheet ratio of the
  plane `(i, ν)` is at most `1`, from the sector form of reflection positivity
  (`TwistDeficitUnionN.deficit_nonneg` through `GapSideVortexRect.twistRatioN_eq_zR`). So
  `vortexR_Lc_nonneg`: `F_v ≥ 0` and `exp(−F_el) = 1 − zR ≥ 0` on these tori, proved.
* `TYBoundR`: the sharpened (prefactor-free) Tomboulis–Yaffe input on the torus, `e = 1 − zR`,
  `La Lb` the extents of the plane; meaningful at `a ≠ b` only (`TomboulisYaffe.not_tyBoundR_diag`).
  `wloopR_area_of_vortexR`: with it, `vortexR ≤ exp(−s La Lb)` gives `wloopR m n ≤ exp(−s mn)`.
  `areaLaw_of_vortexR_condensation`: the family form on tori `Lc (n K) i`.

## 4. The zoom: condensation in physical units and the floor

A line of measures, zoom `j`, spacing `a j > 0`, lattice tension `σlat j`, physical tension
`σlat j / a j²` (`EdgeCost.sigmaPhys`).

* `floor_of_condensation`: at every zoom `TYBound`, the thermodynamic limit, `HasTension`, and
  condensation at the lattice rate `ρ₀ a_j²` (one physical rate `ρ₀ > 0` per unit physical
  cross-section area, the same at every zoom) give `NoTransition.Floor (σlat / a²)` with floor `ρ₀`.
* `count_uniform_of_floor`: a count at the per-zoom cost `σ_j f L²` with `σ_j ≥ ρ₀` is a count at the
  one cost `ρ₀ f L²`.
* `matchAt_uniform_of_condensation`: the above and the count hypothesis of `MatchAt.matchAt_of_count`
  at every zoom and length give one `L₀` with `MatchAt` at every zoom and every `L ≥ L₀` (through
  `NoTransitionFlow.uniform_length_of_floor`). The count hypothesis is separate: condensation
  supplies the floor, not the control of the block-spin chunk activities by it.

## 5. Strength

* Condensation (zoom-uniform, in physical units) gives the floor through the Tomboulis–Yaffe input:
  `floor_of_condensation`. It is at least as strong as the floor.
* `ty_floor_without_condensation`: on the interface of this module the converse fails. The data
  `W m n = e^{−mn}`, `e = 1/2` (that is `Zt/Z = 1/2`, `F_v = log 2` at every box), boxes `(K+1)!`
  satisfy `TYBound` at every box and `HasTension W 1`, and `elw` does not condense at any rate
  `ρ > 0`. So the floor does not imply condensation through the inequality alone; the 't Hooft
  duality picture asserts the converse for the gauge theory, and no declaration here proves it.
* `condensation_hyps_consistent`: the hypotheses of `floor_of_condensation` hold together at one
  zoom (`W = e^{−ρmn}`, `e = exp(−ρA)`, `TYBound` with equality, `HasTension W ρ`), so the
  implication is not vacuous.

## 6. The `U(1)` control

`coulomb_no_condensation`: a vortex free energy with the Coulomb form `F_v ≥ c L₃L₄/A`, `c > 0`,
`L₃L₄ ≥ A` (case (b)), condenses at no rate `ρ > 0`, and neither does `elw = 1 − e^{−F_v}`: the
Tomboulis–Yaffe bound then gives nothing. For `U(1)` a twist exists at every angle and none is
topologically protected; that its 4D weak-coupling vortex free energy has this form (the Coulomb
phase, Guth 1980, Fröhlich–Spencer 1982) is cited, not proved. `GapSideTwistFlat` proves that a
commutative group carries a centre twist at no configuration of zero action, while `SU(2)` does.

## The residual

Condensation itself — the vortex free energy of the 4D `SU(N)` Wilson measure decaying at a
positive rate per unit physical cross-section area, uniformly in the zoom — is open at weak
coupling. Kovács–Tomboulis measured it for `SU(2)` (Monte Carlo, outside this tree). With the
sharpened Tomboulis–Yaffe bound (`TYBound`, an unproved strengthening of the published inequality;
the published factor-2 form is `TomboulisYaffe.tyTwo_of_chessboard`), the thermodynamic limit and
`HasTension` it gives the floor; the count hypothesis stays as in `NoTransitionFlow`. Nothing here
proves confinement or the mass gap. The zoom theorems (`floor_of_condensation`,
`matchAt_uniform_of_condensation`) are stated on abstract data `W`, `e`, `La`, `Lb`; the `SU(2)`
torus result (`areaLaw_of_vortexR_condensation`) is at one zoom. `VortexTorus` instantiates the zoom
theorems with `wloopR`, `1 − zR` and the corner tori, and discharges `Adm` on the factorial side
family (it fails on the doubling family). The Coulomb control
uses `P ≥ A` (the twist plane at least the cross-section).

## Numerics (`research/code/vortex_checks.py`, under 10 s, no Monte Carlo)

2D `SU(2)` torus, exact character sums: `F_v → 0` as `2 r^A`, `r = I₂(β)/I₁(β)`, the prefactor-free inequality holds
on every tiling rectangle and fails on non-tiling ones of large area; the rate read from
`−log(1 − Z_−/Z)/A` tends to the exact tension `−log r`. 4D Migdal–Kadanoff proxy (labelled a proxy,
not the 4D Wilson measure): `SU(2)` `F_v` decays, `U(1)` at weak coupling stops at a positive value.

DERIVED (module-wide): `1` the unit loop side and the threshold `1 ≤ n`; `2` the square `n²`, the
half `ρ/2` in `not_condenses_of_lower` and the `SU(2)` matrix size; `1/2` the twisted ratio of the
interface example; `K + 1` the shift that makes `(K+1)! ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.VortexCondense

open Filter Topology Finset MeasureTheory
open MassGap.MatchAt

/-! ## 1. The vortex free energy -/

/-- **The vortex free energy** `F_v = −log(Zt/Z)`. -/
def vfe (Z Zt : ℝ) : ℝ := -Real.log (Zt / Z)

/-- **The electric weight** `1 − Zt/Z`, twice the `ℤ₂` Fourier transform `exp(−F_el)` of the
vortex ratio at `SU(2)`. -/
def elw (Z Zt : ℝ) : ℝ := 1 - Zt / Z

theorem elw_eq {Z Zt : ℝ} (hZ : 0 < Z) (hZt : 0 < Zt) :
    elw Z Zt = 1 - Real.exp (-vfe Z Zt) := by
  unfold elw vfe
  rw [neg_neg, Real.exp_log (div_pos hZt hZ)]

/-- **The electric weight is at most the vortex free energy.** -/
theorem elw_le_vfe {Z Zt : ℝ} (hZ : 0 < Z) (hZt : 0 < Zt) : elw Z Zt ≤ vfe Z Zt := by
  unfold elw vfe
  have := Real.log_le_sub_one_of_pos (div_pos hZt hZ)
  linarith

theorem elw_nonneg {Z Zt : ℝ} (hZ : 0 < Z) (hle : Zt ≤ Z) : 0 ≤ elw Z Zt := by
  unfold elw
  rw [sub_nonneg, div_le_one hZ]
  exact hle

theorem vfe_nonneg {Z Zt : ℝ} (hZ : 0 < Z) (hZt : 0 < Zt) (hle : Zt ≤ Z) : 0 ≤ vfe Z Zt := by
  unfold vfe
  have h1 : Zt / Z ≤ 1 := (div_le_one hZ).2 hle
  have := Real.log_nonpos (div_pos hZt hZ).le h1
  linarith

/-- **A lower bound on the vortex free energy bounds the electric weight below.** -/
theorem elw_ge_of_vfe_ge {Z Zt κ : ℝ} (hZ : 0 < Z) (hZt : 0 < Zt) (h : κ ≤ vfe Z Zt) :
    1 - Real.exp (-κ) ≤ elw Z Zt := by
  rw [elw_eq hZ hZt]
  have := Real.exp_le_exp.2 (neg_le_neg h)
  linarith

/-! ## 2. Tomboulis–Yaffe: from the inequality to the area law -/

/-- **An admissible rectangle**: `m × n` tiles the `La × Lb` cross-section and does not wrap. -/
def Adm (La Lb m n : ℕ) : Prop := m ∣ La ∧ n ∣ Lb ∧ m < La ∧ n < Lb

/-- **A sharpened Tomboulis–Yaffe bound as an input**: `W m n ≤ e^{mn/(La Lb)}` on every admissible
rectangle. The published inequality has prefactor `2`, base `e/2` and needs `La/m`, `Lb/n` powers of
two; no proof of this strengthening is known. -/
def TYBound (W : ℕ → ℕ → ℝ) (e : ℝ) (La Lb : ℕ) : Prop :=
  ∀ m n, Adm La Lb m n → W m n ≤ e ^ (((m : ℝ) * n) / ((La : ℝ) * Lb))

/-- **The cross-section rate becomes the loop rate**: `TYBound`, `0 ≤ e ≤ exp(−s La Lb)` give
`W m n ≤ exp(−s mn)` on every admissible rectangle. -/
theorem area_of_ty {W : ℕ → ℕ → ℝ} {e s : ℝ} {La Lb : ℕ} (hTY : TYBound W e La Lb) (he0 : 0 ≤ e)
    (he : e ≤ Real.exp (-(s * ((La : ℝ) * Lb)))) {m n : ℕ} (hadm : Adm La Lb m n) :
    W m n ≤ Real.exp (-(s * ((m : ℝ) * n))) := by
  have hLa : (0 : ℝ) < La := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le m) hadm.2.2.1
  have hLb : (0 : ℝ) < Lb := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le n) hadm.2.2.2
  have hA : (0 : ℝ) < (La : ℝ) * Lb := mul_pos hLa hLb
  have hx : 0 ≤ ((m : ℝ) * n) / ((La : ℝ) * Lb) := by positivity
  calc W m n ≤ e ^ (((m : ℝ) * n) / ((La : ℝ) * Lb)) := hTY m n hadm
    _ ≤ (Real.exp (-(s * ((La : ℝ) * Lb)))) ^ (((m : ℝ) * n) / ((La : ℝ) * Lb)) :=
        Real.rpow_le_rpow he0 he hx
    _ = Real.exp (-(s * ((La : ℝ) * Lb)) * (((m : ℝ) * n) / ((La : ℝ) * Lb))) :=
        (Real.exp_mul _ _).symm
    _ = Real.exp (-(s * ((m : ℝ) * n))) := by
        congr 1
        rw [mul_div_assoc', div_eq_iff hA.ne']
        ring

/-- **Condensation at rate `ρ` per unit cross-section area**: for every `ρ' < ρ`, eventually along
the box family `e K ≤ exp(−ρ' A K)`. -/
def Condenses (e A : ℕ → ℝ) (ρ : ℝ) : Prop :=
  ∀ ρ' < ρ, ∀ᶠ K in atTop, e K ≤ Real.exp (-(ρ' * A K))

theorem Condenses.mono {e e' A : ℕ → ℝ} {ρ : ℝ} (h : Condenses e A ρ)
    (hle : ∀ᶠ K in atTop, e' K ≤ e K) : Condenses e' A ρ := fun ρ' hρ' =>
  (h ρ' hρ').and hle |>.mono fun _ hK => hK.2.trans hK.1

/-- **A subexponential prefactor does not change the rate**: `F K ≤ e^{g K} e^{−ρ A K}` with
`g/A → 0` and `A → ∞` condenses at `ρ`. -/
theorem condenses_of_sublinear {F A g : ℕ → ℝ} {ρ : ℝ}
    (hF : ∀ᶠ K in atTop, F K ≤ Real.exp (g K) * Real.exp (-(ρ * A K)))
    (hA : Tendsto A atTop atTop) (hg : Tendsto (fun K => g K / A K) atTop (𝓝 0)) :
    Condenses F A ρ := by
  intro ρ' hρ'
  filter_upwards [hF, hg.eventually (gt_mem_nhds (sub_pos.2 hρ')), hA.eventually_gt_atTop 0]
    with K hK hgK hAK
  rw [div_lt_iff₀ hAK] at hgK
  refine hK.trans ?_
  rw [← Real.exp_add]
  have e1 : (ρ - ρ') * A K = ρ * A K - ρ' * A K := by ring
  exact Real.exp_le_exp.2 (by linarith)

/-- **The form `F ≤ C e^{−ρA}`** condenses at `ρ` when `A → ∞`. -/
theorem condenses_of_const {F A : ℕ → ℝ} {C ρ : ℝ} (hC : 0 < C)
    (hF : ∀ K, F K ≤ C * Real.exp (-(ρ * A K))) (hA : Tendsto A atTop atTop) :
    Condenses F A ρ :=
  condenses_of_sublinear (g := fun _ => Real.log C)
    (Eventually.of_forall fun K => by rw [Real.exp_log hC]; exact hF K) hA
    (tendsto_const_nhds.div_atTop hA)

/-- **A condensing vortex free energy makes the electric weight condense.** -/
theorem condenses_elw_of_vfe {Z Zt A : ℕ → ℝ} {ρ : ℝ} (hZ : ∀ K, 0 < Z K) (hZt : ∀ K, 0 < Zt K)
    (h : Condenses (fun K => vfe (Z K) (Zt K)) A ρ) :
    Condenses (fun K => elw (Z K) (Zt K)) A ρ :=
  h.mono (Eventually.of_forall fun K => elw_le_vfe (hZ K) (hZt K))

/-- **A positive lower bound forbids condensation** at every positive rate when `A → ∞`. -/
theorem not_condenses_of_lower {e A : ℕ → ℝ} {c ρ : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ K in atTop, c ≤ e K) (hA : Tendsto A atTop atTop) (hρ : 0 < ρ) :
    ¬ Condenses e A ρ := by
  intro h
  have h1 := h (ρ / 2) (by linarith)
  have h2 : Tendsto (fun K => Real.exp (-(ρ / 2 * A K))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hA.const_mul_atTop (by linarith)))
  obtain ⟨K, hK1, hK2, hK3⟩ := (h1.and (hlow.and (h2.eventually (gt_mem_nhds hc)))).exists
  linarith

/-- **The thermodynamic limit of the Tomboulis–Yaffe area law.** `TYBound` on every box of a
family, condensation of the electric weight, every rectangle eventually admissible and the loops
converging give `Winf m n ≤ exp(−ρ mn)`. -/
theorem areaLaw_limit {W : ℕ → ℕ → ℕ → ℝ} {Winf : ℕ → ℕ → ℝ} {e : ℕ → ℝ} {La Lb : ℕ → ℕ}
    {ρ : ℝ} (hTY : ∀ K, TYBound (W K) (e K) (La K) (Lb K)) (he0 : ∀ K, 0 ≤ e K)
    (hcond : Condenses e (fun K => (La K : ℝ) * Lb K) ρ)
    (hadm : ∀ m n, 1 ≤ m → 1 ≤ n → ∀ᶠ K in atTop, Adm (La K) (Lb K) m n)
    (hlim : ∀ m n, Tendsto (fun K => W K m n) atTop (𝓝 (Winf m n))) :
    ∀ m n, 1 ≤ m → 1 ≤ n → Winf m n ≤ Real.exp (-(ρ * ((m : ℝ) * n))) := by
  intro m n hm hn
  have hstep : ∀ ρ' < ρ, Winf m n ≤ Real.exp (-(ρ' * ((m : ℝ) * n))) := by
    intro ρ' hρ'
    refine le_of_tendsto (hlim m n) ?_
    filter_upwards [hcond ρ' hρ', hadm m n hm hn] with K hK hA
    exact area_of_ty (hTY K) (he0 K) hK hA
  have h1 : Tendsto (fun k : ℕ => ρ - 1 / ((k : ℝ) + 1)) atTop (𝓝 ρ) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ)).sub
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  have h2 : Tendsto (fun k : ℕ => Real.exp (-((ρ - 1 / ((k : ℝ) + 1)) * ((m : ℝ) * n)))) atTop
      (𝓝 (Real.exp (-(ρ * ((m : ℝ) * n))))) :=
    (Real.continuous_exp.tendsto _).comp ((h1.mul_const _).neg)
  refine ge_of_tendsto h2 (Eventually.of_forall fun k => hstep _ ?_)
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

/-- **The string tension**: `W n n > 0` and `−log W(n, n)/n² → σ`. -/
def HasTension (W : ℕ → ℕ → ℝ) (σ : ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < W n n) ∧
    Tendsto (fun n : ℕ => -Real.log (W n n) / (n : ℝ) ^ 2) atTop (𝓝 σ)

/-- **An area law bounds the tension below.** -/
theorem le_tension_of_area {W : ℕ → ℕ → ℝ} {σ ρ : ℝ} (hT : HasTension W σ)
    (harea : ∀ n, 1 ≤ n → W n n ≤ Real.exp (-(ρ * ((n : ℝ) * n)))) : ρ ≤ σ := by
  refine ge_of_tendsto hT.2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos := hT.1 n hn
  have hl : Real.log (W n n) ≤ -(ρ * ((n : ℝ) * n)) := by
    have := Real.log_le_log hpos (harea n hn)
    rwa [Real.log_exp] at this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hn2]
  nlinarith

/-- **Factorial boxes make every rectangle eventually admissible.** -/
theorem adm_factorial (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∀ᶠ K in atTop, Adm (Nat.factorial (K + 1)) (Nat.factorial (K + 1)) m n := by
  filter_upwards [eventually_ge_atTop (max m n)] with K hK
  have hmK : m ≤ K := (le_max_left _ _).trans hK
  have hnK : n ≤ K := (le_max_right _ _).trans hK
  have hf := Nat.self_le_factorial (K + 1)
  exact ⟨Nat.dvd_factorial hm (by omega), Nat.dvd_factorial hn (by omega), by omega, by omega⟩

/-- **The factorial cross-section area tends to infinity.** -/
theorem tendsto_area_factorial :
    Tendsto (fun K : ℕ => (Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ)) atTop
      atTop := by
  refine tendsto_atTop_mono (fun K => ?_) tendsto_natCast_atTop_atTop
  have h : K ≤ Nat.factorial (K + 1) * Nat.factorial (K + 1) :=
    (Nat.le_succ K).trans ((Nat.self_le_factorial _).trans (Nat.le_mul_self _))
  exact_mod_cast h

/-! ## 3. The Wilson `SU(2)` torus -/

section Torus

open MassGap.RectWilson MassGap.GapSideVortexRect MassGap.CompactGauge

local notation "wd" => WilsonAction.wilsonDensity

variable (L : Fin 4 → ℕ)

/-- **The boundary word of the `m × n` rectangle** in the plane `(a, b)` with corner `o`: `m` links
along `a`, `n` along `b`, then back. -/
def rectWord (a b : Fin 4) (m n : ℕ) (o : RSite L) : List (RLink L × Bool) :=
  (List.range m).map (fun t => ((a, (rshift L a)^[t] o), true)) ++
  (List.range n).map (fun t => ((b, (rshift L b)^[t] ((rshift L a)^[m] o)), true)) ++
  ((List.range m).map (fun t => ((a, (rshift L a)^[t] ((rshift L b)^[n] o)), false))).reverse ++
  ((List.range n).map (fun t => ((b, (rshift L b)^[t] o), false))).reverse

/-- The holonomy of the rectangle (the ordered product of `rectWord`). -/
def rectHol (a b : Fin 4) (m n : ℕ) (o : RSite L) (U : RLink L → SUN.SU 2) : SUN.SU 2 :=
  ((rectWord L a b m n o).map (fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹)).prod

/-- **The Wilson loop** `⟨½ Re tr U[C]⟩ = ⟨1 − wilsonDensity(U[C])⟩` on the `SU(2)` rectangular
torus at coupling `β`. -/
def wloopR (a b : Fin 4) (m n : ℕ) (o : RSite L) (β : ℝ) : ℝ :=
  (∫ U : RLink L → SUN.SU 2, (1 - wd (rectHol L a b m n o U)) *
      Real.exp (-β * ∑ q, wd (rhol L q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))) / ZRp L β (fun _ => 1)

/-- **The empty rectangle reads `1`.** -/
theorem wloopR_zero (a b : Fin 4) (o : RSite L) (β : ℝ) : wloopR L a b 0 0 o β = 1 := by
  have hZ := ZRp_pos L β (fun _ => 1)
  have h1 : ∀ U : RLink L → SUN.SU 2, rectHol L a b 0 0 o U = 1 := fun U => by
    simp [rectHol, rectWord]
  unfold ZRp at hZ
  unfold wloopR ZRp
  simp only [h1, WilsonAction.wilsonDensity_one (N := 2) (by norm_num), sub_zero, one_mul] at hZ ⊢
  exact div_self hZ.ne'

/-- **The sharpened Tomboulis–Yaffe input on the torus**: `e = 1 − zR`, the extents of the plane
`(a, b)`. False at `a = b` (`TomboulisYaffe.not_tyBoundR_diag`); at `a ≠ b` an unproved
strengthening of the published bound. -/
def TYBoundR (a b : Fin 4) (o : RSite L) (β : ℝ) : Prop :=
  TYBound (fun m n => wloopR L a b m n o β) (1 - zR L a b β) (L a) (L b)

end Torus

section CornerTorus

open MassGap.GapSideVortexRect

/-- **On the corner-step torus the sheet ratio is at most `1`** (the sector form of reflection
positivity: the twisted trace is at most the trace). -/
theorem zR_Lc_le_one {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) : zR (Lc n i) i ν.1 β ≤ 1 := by
  rw [← twistRatioN_eq_zR hβ hn he i ν]
  have hA := CentreSectorSeedN.hs_halfKN_pos (N := 2) hβ n i
  have h := TwistDeficitUnionN.one_sub_twistRatioN (N := 2) hβ n i (Pi.single ν 1)
  have h2 : 0 ≤ 1 - CentreSectorSeedN.twistRatioN 2 β n i (Pi.single ν 1) := by
    rw [h]
    exact div_nonneg (TwistDeficitUnionN.deficit_nonneg (CentreSectorSeedN.bdd_halfKN hβ _ i)
      SliceCentreAction.centreAction _) hA.le
  linarith

/-- **The vortex free energy and the electric weight are non-negative** on the corner-step torus. -/
theorem vortexR_Lc_nonneg {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) :
    0 ≤ vortexR (Lc n i) i ν.1 β ∧ 0 ≤ 1 - zR (Lc n i) i ν.1 β := by
  have h1 := zR_Lc_le_one hβ hn he i ν
  refine ⟨?_, by linarith⟩
  unfold vortexR
  have := Real.log_nonpos (zR_pos (Lc n i) i ν.1 β).le h1
  linarith

/-- **The area law on one torus**: the Tomboulis–Yaffe input and `vortexR ≤ exp(−s La Lb)` give
`wloopR m n ≤ exp(−s mn)` on every admissible rectangle. -/
theorem wloopR_area_of_vortexR {β s : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (o : RectWilson.RSite (Lc n i))
    (hTY : TYBoundR (Lc n i) i ν.1 o β)
    (hv : vortexR (Lc n i) i ν.1 β
      ≤ Real.exp (-(s * (((Lc n i i : ℕ) : ℝ) * ((Lc n i ν.1 : ℕ) : ℝ)))))
    {m k : ℕ} (hadm : Adm (Lc n i i) (Lc n i ν.1) m k) :
    wloopR (Lc n i) i ν.1 m k o β ≤ Real.exp (-(s * ((m : ℝ) * k))) :=
  area_of_ty (W := fun m k => wloopR (Lc n i) i ν.1 m k o β) hTY
    (vortexR_Lc_nonneg hβ hn he i ν).2
    ((one_sub_zR_le_vortexR (Lc n i) i ν.1 β).trans hv) hadm

/-- **The area law in the limit along corner-step tori** `Lc (n K) i`: the Tomboulis–Yaffe input on
every torus, condensation of `vortexR` at rate `ρ` per unit area of the plane `(i, ν)`, every
rectangle eventually admissible, and the loops converging give `Winf m k ≤ exp(−ρ mk)`. -/
theorem areaLaw_of_vortexR_condensation {β ρ : ℝ} (hβ : 0 ≤ β) {nK : ℕ → ℕ}
    (hn : ∀ K, 2 ≤ nK K) (he : ∀ K, Even (nK K)) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i})
    (o : ∀ K, RectWilson.RSite (Lc (nK K) i)) (hTY : ∀ K, TYBoundR (Lc (nK K) i) i ν.1 (o K) β)
    (hcond : Condenses (fun K => vortexR (Lc (nK K) i) i ν.1 β)
      (fun K => ((Lc (nK K) i i : ℕ) : ℝ) * ((Lc (nK K) i ν.1 : ℕ) : ℝ)) ρ)
    (hadm : ∀ m k, 1 ≤ m → 1 ≤ k → ∀ᶠ K in atTop, Adm (Lc (nK K) i i) (Lc (nK K) i ν.1) m k)
    {Winf : ℕ → ℕ → ℝ}
    (hlim : ∀ m k, Tendsto (fun K => wloopR (Lc (nK K) i) i ν.1 m k (o K) β) atTop
      (𝓝 (Winf m k))) :
    ∀ m k, 1 ≤ m → 1 ≤ k → Winf m k ≤ Real.exp (-(ρ * ((m : ℝ) * k))) :=
  areaLaw_limit (W := fun K m k => wloopR (Lc (nK K) i) i ν.1 m k (o K) β)
    (e := fun K => 1 - zR (Lc (nK K) i) i ν.1 β) hTY
    (fun K => (vortexR_Lc_nonneg hβ (hn K) (he K) i ν).2)
    (hcond.mono (Eventually.of_forall fun K => one_sub_zR_le_vortexR (Lc (nK K) i) i ν.1 β))
    hadm hlim

end CornerTorus

/-! ## 4. The zoom -/

/-- **Condensation in physical units gives the floor.** At every zoom `j`: the Tomboulis–Yaffe input
on a box family, condensation of the electric weight at the lattice rate `ρ₀ a_j²` (one physical
rate `ρ₀`), the thermodynamic limit and `HasTension` give `Floor (σlat / a²)`. -/
theorem floor_of_condensation {W : ℕ → ℕ → ℕ → ℕ → ℝ} {Winf : ℕ → ℕ → ℕ → ℝ} {e : ℕ → ℕ → ℝ}
    {La Lb : ℕ → ℕ → ℕ} {a σlat : ℕ → ℝ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (ha : ∀ j, 0 < a j)
    (hTY : ∀ j K, TYBound (W j K) (e j K) (La j K) (Lb j K)) (he0 : ∀ j K, 0 ≤ e j K)
    (hcond : ∀ j, Condenses (e j) (fun K => (La j K : ℝ) * Lb j K) (ρ₀ * a j ^ 2))
    (hadm : ∀ j m n, 1 ≤ m → 1 ≤ n → ∀ᶠ K in atTop, Adm (La j K) (Lb j K) m n)
    (hlim : ∀ j m n, Tendsto (fun K => W j K m n) atTop (𝓝 (Winf j m n)))
    (hT : ∀ j, HasTension (Winf j) (σlat j)) :
    NoTransition.Floor (fun j => σlat j / a j ^ 2) := by
  refine ⟨ρ₀, hρ₀, fun j => ?_⟩
  have harea := areaLaw_limit (hTY j) (he0 j) (hcond j) (hadm j) (hlim j)
  have h := le_tension_of_area (hT j) fun n hn => harea n n hn hn
  rw [le_div_iff₀ (pow_pos (ha j) 2)]
  exact h

/-- **A floor turns the per-zoom count into the uniform-cost count.** -/
theorem count_uniform_of_floor {V : ℕ → ℝ → Type*} [∀ j L, Fintype (V j L)]
    [∀ j L, DecidableEq (V j L)] (w : ∀ j L, Finset (V j L) → ℝ) {σ : ℕ → ℝ} {z f ρ₀ : ℝ}
    (hz : 0 ≤ z) (hf : 0 ≤ f) (hlow : ∀ j, ρ₀ ≤ σ j)
    (hcount : ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(σ j * f * L ^ 2))) ^ n) :
    ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(ρ₀ * f * L ^ 2))) ^ n := by
  intro j L v n
  refine (hcount j L v n).trans (pow_le_pow_left₀ (by positivity) ?_ n)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hz
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hlow j) hf) (sq_nonneg L)
  linarith

/-- **Condensation, the count, and one length for every zoom.** The hypotheses of
`floor_of_condensation` and the count of `MatchAt.matchAt_of_count` at cost `(σlat j / a j²) f L²`
at every zoom and length give one `L₀` with `MatchAt` at every zoom and every `L ≥ L₀`. -/
theorem matchAt_uniform_of_condensation {W : ℕ → ℕ → ℕ → ℕ → ℝ} {Winf : ℕ → ℕ → ℕ → ℝ}
    {e : ℕ → ℕ → ℝ} {La Lb : ℕ → ℕ → ℕ} {a σlat : ℕ → ℝ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (ha : ∀ j, 0 < a j)
    (hTY : ∀ j K, TYBound (W j K) (e j K) (La j K) (Lb j K)) (he0 : ∀ j K, 0 ≤ e j K)
    (hcond : ∀ j, Condenses (e j) (fun K => (La j K : ℝ) * Lb j K) (ρ₀ * a j ^ 2))
    (hadm : ∀ j m n, 1 ≤ m → 1 ≤ n → ∀ᶠ K in atTop, Adm (La j K) (Lb j K) m n)
    (hlim : ∀ j m n, Tendsto (fun K => W j K m n) atTop (𝓝 (Winf j m n)))
    (hT : ∀ j, HasTension (Winf j) (σlat j))
    {V : ℕ → ℝ → Type*} [∀ j L, Fintype (V j L)] [∀ j L, DecidableEq (V j L)]
    (w : ∀ j L, Finset (V j L) → ℝ) {z f κ : ℝ} (hz : 0 ≤ z) (hf : 0 < f) (hκ : 0 ≤ κ)
    (hw0 : ∀ j L, w j L ∅ = 0)
    (hcount : ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(σlat j / a j ^ 2 * f * L ^ 2))) ^ n) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ := by
  have hfl := floor_of_condensation hρ₀ ha hTY he0 hcond hadm hlim hT
  obtain ⟨L₀, hL₀, h⟩ := NoTransitionFlow.uniform_length_of_floor (κ := κ) hz hf hfl
  exact ⟨L₀, hL₀, fun j L hL => matchAt_of_count (hw0 j L) hz hκ (hcount j L) (h j L hL)⟩

/-! ## 5. Strength: the floor does not give condensation through the inequality -/

/-- **On this interface the floor does not imply condensation.** `W m n = e^{−mn}`, `e = 1/2`, boxes
`(K+1)!`: `TYBound` at every box, `HasTension W 1`, and `e` condenses at no positive rate. -/
theorem ty_floor_without_condensation :
    (∀ K, TYBound (fun m n => Real.exp (-((m : ℝ) * n))) (2⁻¹)
      (Nat.factorial (K + 1)) (Nat.factorial (K + 1))) ∧
    HasTension (fun m n => Real.exp (-((m : ℝ) * n))) 1 ∧
    ∀ ρ : ℝ, 0 < ρ → ¬ Condenses (fun _ => (2⁻¹ : ℝ))
      (fun K => (Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ)) ρ := by
  refine ⟨fun K m n _ => ?_, ⟨fun n _ => Real.exp_pos _, ?_⟩, fun ρ hρ =>
    not_condenses_of_lower (by norm_num) (Eventually.of_forall fun _ => le_rfl)
      tendsto_area_factorial hρ⟩
  · have hF : (1 : ℝ) ≤ (Nat.factorial (K + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hA : (1 : ℝ) ≤ (Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ) := by nlinarith
    have hmn : (0 : ℝ) ≤ (m : ℝ) * n := by positivity
    set x := ((m : ℝ) * n) / ((Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ))
    have hx0 : 0 ≤ x := by positivity
    have hx : x ≤ (m : ℝ) * n := div_le_self hmn hA
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
      linarith
    rw [Real.rpow_def_of_pos (by norm_num), Real.log_inv]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_right hl2 hx0]
  · have : (fun n : ℕ => -Real.log (Real.exp (-((n : ℝ) * n))) / (n : ℝ) ^ 2) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      rw [Real.log_exp, neg_neg, sq, div_self (mul_ne_zero hn0 hn0)]
    exact tendsto_const_nhds.congr' this.symm

/-- **The hypotheses of `floor_of_condensation` are consistent at one zoom.** `W m n = e^{−ρmn}`,
`e K = exp(−ρ A K)`, boxes `(K+1)!`: `TYBound` at every box (with equality), `Condenses e A ρ`, and
`HasTension W ρ`. -/
theorem condensation_hyps_consistent {ρ : ℝ} :
    (∀ K, TYBound (fun m n => Real.exp (-(ρ * ((m : ℝ) * n))))
      (Real.exp (-(ρ * ((Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ)))))
      (Nat.factorial (K + 1)) (Nat.factorial (K + 1))) ∧
    Condenses (fun K => Real.exp (-(ρ * ((Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ)))))
      (fun K => (Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ)) ρ ∧
    HasTension (fun m n => Real.exp (-(ρ * ((m : ℝ) * n)))) ρ := by
  refine ⟨fun K m n _ => ?_, fun ρ' hρ' => Eventually.of_forall fun K => ?_,
    ⟨fun n _ => Real.exp_pos _, ?_⟩⟩
  · have hF : (0 : ℝ) < (Nat.factorial (K + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hA : (0 : ℝ) < (Nat.factorial (K + 1) : ℝ) * (Nat.factorial (K + 1) : ℝ) := mul_pos hF hF
    beta_reduce
    rw [← Real.exp_mul]
    refine le_of_eq (congrArg Real.exp ?_)
    rw [mul_div_assoc', eq_div_iff hA.ne']
    ring
  · have hF : (0 : ℝ) ≤ (Nat.factorial (K + 1) : ℝ) := Nat.cast_nonneg _
    beta_reduce
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_right hρ'.le (mul_nonneg hF hF)]
  · have : (fun n : ℕ => -Real.log (Real.exp (-(ρ * ((n : ℝ) * n)))) / (n : ℝ) ^ 2) =ᶠ[atTop]
        fun _ => ρ := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      rw [Real.log_exp, neg_neg, sq, mul_div_assoc, div_self (mul_ne_zero hn0 hn0), mul_one]
    exact tendsto_const_nhds.congr' this.symm

/-! ## 6. The `U(1)` control -/

/-- **A Coulomb vortex free energy condenses at no rate.** `F_v ≥ c P/A` with `c > 0`, `P ≥ A > 0`
(the transverse volume at least the cross-section area) and `A → ∞`: neither `F_v` nor the
electric weight condenses at any `ρ > 0`. -/
theorem coulomb_no_condensation {Z Zt P A : ℕ → ℝ} {c ρ : ℝ} (hZ : ∀ K, 0 < Z K)
    (hZt : ∀ K, 0 < Zt K) (hc : 0 < c) (hρ : 0 < ρ) (hA0 : ∀ K, 0 < A K) (hPA : ∀ K, A K ≤ P K)
    (hF : ∀ K, c * P K / A K ≤ vfe (Z K) (Zt K)) (hA : Tendsto A atTop atTop) :
    ¬ Condenses (fun K => vfe (Z K) (Zt K)) A ρ ∧ ¬ Condenses (fun K => elw (Z K) (Zt K)) A ρ := by
  have hlow : ∀ K, c ≤ vfe (Z K) (Zt K) := fun K => by
    refine le_trans ?_ (hF K)
    rw [le_div_iff₀ (hA0 K)]
    exact mul_le_mul_of_nonneg_left (hPA K) hc.le
  have hc' : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_exp.2 (show -c < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  exact ⟨not_condenses_of_lower hc (Eventually.of_forall hlow) hA hρ,
    not_condenses_of_lower hc'
      (Eventually.of_forall fun K => elw_ge_of_vfe_ge (hZ K) (hZt K) (hlow K)) hA hρ⟩

#print axioms elw_eq
#print axioms elw_le_vfe
#print axioms elw_nonneg
#print axioms vfe_nonneg
#print axioms elw_ge_of_vfe_ge
#print axioms area_of_ty
#print axioms Condenses.mono
#print axioms condenses_of_sublinear
#print axioms condenses_of_const
#print axioms condenses_elw_of_vfe
#print axioms not_condenses_of_lower
#print axioms areaLaw_limit
#print axioms le_tension_of_area
#print axioms adm_factorial
#print axioms tendsto_area_factorial
#print axioms wloopR_zero
#print axioms zR_Lc_le_one
#print axioms vortexR_Lc_nonneg
#print axioms wloopR_area_of_vortexR
#print axioms areaLaw_of_vortexR_condensation
#print axioms floor_of_condensation
#print axioms count_uniform_of_floor
#print axioms matchAt_uniform_of_condensation
#print axioms ty_floor_without_condensation
#print axioms condensation_hyps_consistent
#print axioms coulomb_no_condensation

end MassGap.VortexCondense
