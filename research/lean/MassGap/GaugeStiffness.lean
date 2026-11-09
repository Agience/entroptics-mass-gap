import Mathlib
import MassGap.ExactIneq

/-!
# MassGap.GaugeStiffness — the gauge stiffness Ward identity on the Wilson torus

Source of the template: OpenAI, *The canonical massive continuum limit of the O(3) model*, preprint, October 2026,
github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, `build/sections/preliminary.tex`,
`prop:preliminary`, equations `eq:prelim-stiffness`, `eq:prelim-ward`, `eq:prelim-variance-identity`,
`eq:prelim-nonabelian`, `eq:prelim-variance-gain`. There the stiffness of a pinned square is contact minus the
variance of a bond current, the Ward identity for an exact gradient test carries one extra term
`½ X_Q(F × (ū_y + ū_x))` (a rotation of the current by the value of the profile), and that term, through an
integration-by-parts Cramér–Rao bound, lowers the stiffness by `(log ℓ)/(4π)` per factor `ℓ`.

## The gauge stiffness

The stiffness here is the response of the free energy to a plaquette twist: for a real `2`-form `ω` and a colour
`X ∈ su(N)`, the twisted action inserts `exp(θ ω_p X)` in each plaquette, and the stiffness is the second derivative of
`−log Z_θ` at `θ = 0`, contact minus variance of the curvature current `J_X(ω) = −(1/N) Σ_p c_p ω_p Re tr(X U_p)`.
For an exact twist `ω = dα` the twist is a link shift, which is a Haar flow; this module proves the exact identity
that the Haar flows give, at every `β`, `t`, side `n`, `N`.

## Proved

1. **The holonomy generator splits into curvature plus commutator residual** (`dHol_split`). Under the profile
   link shift `U_ℓ ↦ exp(s α_ℓ X) U_ℓ`, the generator of the plaquette holonomy `P = V₁ V₂ W₃ W₄` is
   `(α₁ + α₂ − α₃ − α₄) X P + R`, with `R = [V₁, a₂] V₂ W₃ W₄ − [V₁ V₂ W₃, a₃] W₄ − [P, a₄]`. The first term is the
   lattice curl `(dα)_p`. The residual is a sum of commutators of the colour with partial holonomies, and
   `[V, a] = [V − 1, a]` (`br_sub_one`), so it is linear in the partial-holonomy defects.
2. **The profile current on the torus** (`sum_dplaq`, `dSprof_eq`): `Σ_ℓ α_ℓ (β DS_in + t DS_mix)` along the link
   flows of `ExactIneq` equals `Σ_p c_p (−1/N)((dα)_p Re tr(X U_p) + Re tr R_p)`, `c_p = β` in plane, `t` mixed.
3. **The stiffness Ward identity** (`ward_profile`, `ward_mean`): for every continuous `O` with link generators,
   `⟨Σ_ℓ α_ℓ D_ℓ O⟩ = ⟨O · (J_X(dα) + R_α)⟩`, and `⟨J_X(dα)⟩ = −⟨R_α⟩`. So the covariance of any observable with the
   curvature current of an exact twist is the contact term `⟨D_α O⟩` minus `⟨O R_α⟩`: the analogue of
   `eq:prelim-ward`, with `R_α` in the place of `½ X_Q(F × ū)`.
4. **The `U(1)` / `SU(N)` contrast lies in `R`** (`resid_comm`, `resid_eq_zero_of_commute`, `residQ_eq_zero_of_commute`,
   `resid_su2`, `resid_su2_ne`). Over a commutative ring (`U(1) ⊂ ℂ`) `R = 0`; on the torus, when the colour commutes
   with every link `R_p = 0` for every plaquette; so an exact twist has a pure contact covariance and the free
   energy reads only the cohomology class of the twist. For `SU(2)` with `V₁ = iσ₁`, `X = iσ₃` the residual is
   `[[0, 2], [−2, 0]] ≠ 0`.
5. **The remaining link, as an inequality** (`freeEnergy_le`, `twistRatio_ge`): if `f = −log(Z_θ/Z_0)` along a twist
   path has `f(0) = f'(0) = 0` and stiffness `f'' ≤ ε` on `[0, θ₀]`, then `f(θ₀) ≤ ε θ₀²/2` and the twisted ratio is at
   least `exp(−ε θ₀²/2)`. These are calculus lemmas about an abstract `f`; no link to `Z_θ` is stated.

## Where the 2D gain has no counterpart

In `eq:prelim-nonabelian` the profile `u` rotates the current by its value at cost `v ‖∇u‖²`, and the Cramér–Rao
ratio per mode is `|u|²/‖∇u‖² = |k|⁻²`, summed to `(1/2π) log ℓ` in two dimensions. In the gauge identity (item 3)
the directions that rotate the current by their value are local gauge rotations, which are exact symmetries of cost
`0`: integration by parts along them is antisymmetric and gives Cauchy–Schwarz with no gain. The directions with cost
`‖dα‖²` are link shifts, and they rotate the current only through `R_α`, whose size is the partial-holonomy defect
(item 1), a fluctuation, not a profile value. A continuous non-commuting global symmetry acting on the curvature
current would be a non-abelian continuous `1`-form symmetry; the `1`-form symmetry of `SU(N)` is the centre `ℤ_N`
and that of `U(1)` is commutative.

DERIVED (module-wide): `1`, `2`, `3`, `4` the corners of a plaquette in their order; `−1/N` the Wilson normalization
of `ExactIneq.dplaq`; `2` in `resid_su2` the entry `1 − (−1)` of the commutator `[iσ₁, iσ₃]`; `2` in the
Taylor bound the square; `0` the base twist. No fitted constant.

This is an argument, not a theorem: in four dimensions the gauge identity has no profile direction that gives a
Cramér–Rao gain of the `(log ℓ)/(4π)` kind, and that absence is not formalized.

## What does not follow

Nothing here lower-bounds the variance of the curvature current, so no stiffness decrease `β − c log ℓ` is proved for
any `N`. The stiffness as the second derivative of `−log Z_θ` under a non-exact twist is not formalized: only the
exact-twist Haar-flow identity is, and the twisted partition function with a continuous Cartan twist is not built.
`freeEnergy_le` takes the stiffness bound, `f(0) = 0` and `f'(0) = 0` as hypotheses; it discharges none of them, and
it does not give `FluxConfinedAt`, which also needs the bound uniform in the side and along the whole path. The
statement on `1`-form symmetries is cited (Gaiotto–Kapustin–Seiberg–Willett, *Generalized global symmetries*, JHEP 2015), not proved.
-/

noncomputable section

namespace MassGap.GaugeStiffness

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut
open MassGap.MixEqui MassGap.MixExpand MassGap.ExactIneq
open scoped Matrix

/-! ## 1. The holonomy generator over a ring -/

section RingAlg

variable {R : Type*} [Ring R]

/-- **The plaquette holonomy** `V₁ V₂ W₃ W₄`, with `W` the inverse links. DERIVED: `1`–`4` the corners. -/
def hol4 (V₁ V₂ W₃ W₄ : R) : R := V₁ * V₂ * W₃ * W₄

/-- **The generator of the holonomy under a profile link shift**, the four-factor Leibniz rule with `a_k` the
generator on corner `k` (left on forward links, `−a` on the right of inverse links). DERIVED: `1`–`4` the corners. -/
def dHol (a₁ a₂ a₃ a₄ V₁ V₂ W₃ W₄ : R) : R :=
  a₁ * V₁ * V₂ * W₃ * W₄ + V₁ * (a₂ * V₂) * W₃ * W₄ + V₁ * V₂ * (W₃ * -a₃) * W₄
    + V₁ * V₂ * W₃ * (W₄ * -a₄)

/-- The commutator. No numeral. -/
def br (x y : R) : R := x * y - y * x

/-- **The commutator residual** of the holonomy generator. DERIVED: `2`–`4` the corners that carry it. -/
def resid (a₂ a₃ a₄ V₁ V₂ W₃ W₄ : R) : R :=
  br V₁ a₂ * (V₂ * W₃ * W₄) - br (V₁ * V₂ * W₃) a₃ * W₄ - br (hol4 V₁ V₂ W₃ W₄) a₄

/-- **The holonomy generator is curl times holonomy plus the commutator residual.** No numeral. -/
theorem dHol_split (a₁ a₂ a₃ a₄ V₁ V₂ W₃ W₄ : R) :
    dHol a₁ a₂ a₃ a₄ V₁ V₂ W₃ W₄
      = (a₁ + a₂ - a₃ - a₄) * hol4 V₁ V₂ W₃ W₄ + resid a₂ a₃ a₄ V₁ V₂ W₃ W₄ := by
  unfold dHol resid br hol4
  noncomm_ring

/-- **A commutator reads only the defect from the identity**: `[V, a] = [V − 1, a]`. DERIVED: `1` the identity. -/
theorem br_sub_one (x y : R) : br x y = br (x - 1) y := by
  unfold br
  noncomm_ring

/-- **The residual vanishes when the colour commutes with the partial holonomies.** No numeral. -/
theorem resid_eq_zero_of_commute {a₂ a₃ a₄ V₁ V₂ W₃ W₄ : R} (h₂ : Commute V₁ a₂)
    (h₃ : Commute (V₁ * V₂ * W₃) a₃) (h₄ : Commute (hol4 V₁ V₂ W₃ W₄) a₄) :
    resid a₂ a₃ a₄ V₁ V₂ W₃ W₄ = 0 := by
  unfold resid br
  rw [h₂.eq, h₃.eq, h₄.eq]
  simp

end RingAlg

/-- **The abelian residual is zero** (`U(1) ⊂ ℂ` is commutative). No numeral. -/
theorem resid_comm {R : Type*} [CommRing R] (a₂ a₃ a₄ V₁ V₂ W₃ W₄ : R) :
    resid a₂ a₃ a₄ V₁ V₂ W₃ W₄ = 0 := by
  unfold resid br hol4
  ring

/-! ## 2. The `SU(2)` residual -/

/-- `iσ₁ ∈ SU(2)`. No numeral. -/
def sV : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-- `iσ₃ ∈ su(2)`. No numeral. -/
def sX : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- **The `SU(2)` residual** at one rotated corner: `[iσ₁, iσ₃] = [[0, 2], [−2, 0]]`. DERIVED: `2 = 1 − (−1)`. -/
theorem resid_su2 : resid sX 0 0 sV 1 1 1 = !![0, 2; -2, 0] := by
  unfold resid br hol4 sV sX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem resid_su2_ne : resid sX 0 0 sV 1 1 1 ≠ 0 := by
  rw [resid_su2]
  intro h
  have := congrFun (congrFun h 0) 1
  simp at this

/-! ## 3. The profile current on the Wilson torus -/

variable {N n : ℕ}

/-- The first corner link. DERIVED: `1` the corner. -/
def e1 (q : Pq n) : Lk n := (q.1.1, q.2)
/-- The second corner link. DERIVED: `2` the corner. -/
def e2 (q : Pq n) : Lk n := (q.1.2, rshift (fun _ => n) q.1.1 q.2)
/-- The third corner link. DERIVED: `3` the corner. -/
def e3 (q : Pq n) : Lk n := (q.1.1, rshift (fun _ => n) q.1.2 q.2)
/-- The fourth corner link. DERIVED: `4` the corner. -/
def e4 (q : Pq n) : Lk n := (q.1.2, q.2)

/-- **The lattice curl** `(dα)_p`. DERIVED: `1`–`4` the corners. -/
def curl (α : Lk n → ℝ) (q : Pq n) : ℝ := α (e1 q) + α (e2 q) - α (e3 q) - α (e4 q)

/-- The holonomy of a plaquette as a matrix. No numeral. -/
def holM (U : Lk n → SUN.SU N) (q : Pq n) : Mat N :=
  hol4 (lk U (e1 q)) (lk U (e2 q)) (lki U (e3 q)) (lki U (e4 q))

/-- The profile generator on a link: `α_ℓ X`. No numeral. -/
def prof (α : Lk n → ℝ) (A : Su N) (m : Lk n) : Mat N := ((α m : ℝ) : ℂ) • A.X

/-- **The residual of a plaquette** under the profile `α`. No numeral. -/
def residQ (α : Lk n → ℝ) (A : Su N) (U : Lk n → SUN.SU N) (q : Pq n) : Mat N :=
  resid (prof α A (e2 q)) (prof α A (e3 q)) (prof α A (e4 q)) (lk U (e1 q)) (lk U (e2 q)) (lki U (e3 q))
    (lki U (e4 q))

/-- The generator of one link flow on one link, as a left factor. DERIVED: `0` the other links. -/
def cOf (l : Lk n) (A : Su N) (m : Lk n) : Mat N := if m = l then A.X else 0

theorem dLk_eq (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) (m : Lk n) :
    dLk l A U m = cOf l A m * lk U m := by
  unfold dLk cOf
  split_ifs <;> simp

theorem dLi_eq (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) (m : Lk n) :
    dLi l A U m = lki U m * -cOf l A m := by
  unfold dLi cOf
  split_ifs <;> simp

theorem dplaq_eq (l : Lk n) (A : Su N) (q : Pq n) (U : Lk n → SUN.SU N) :
    dplaq l A q U = -(1 / (N : ℝ)) * rt (dHol (cOf l A (e1 q)) (cOf l A (e2 q)) (cOf l A (e3 q))
      (cOf l A (e4 q)) (lk U (e1 q)) (lk U (e2 q)) (lki U (e3 q)) (lki U (e4 q))) := by
  unfold dplaq dHol e1 e2 e3 e4
  simp only [dLk_eq, dLi_eq]

theorem sum_cOf (α : Lk n → ℝ) (A : Su N) (m : Lk n) :
    ∑ l, ((α l : ℝ) : ℂ) • cOf l A m = prof α A m := by
  unfold cOf prof
  simp [smul_ite, Finset.sum_ite_eq]

theorem sum_smul_dHol {ι : Type*} (s : Finset ι) (r : ι → ℂ) (a₁ a₂ a₃ a₄ : ι → Mat N)
    (V₁ V₂ W₃ W₄ : Mat N) :
    ∑ i ∈ s, r i • dHol (a₁ i) (a₂ i) (a₃ i) (a₄ i) V₁ V₂ W₃ W₄
      = dHol (∑ i ∈ s, r i • a₁ i) (∑ i ∈ s, r i • a₂ i) (∑ i ∈ s, r i • a₃ i) (∑ i ∈ s, r i • a₄ i)
          V₁ V₂ W₃ W₄ := by
  unfold dHol
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, mul_neg, Finset.sum_neg_distrib, smul_neg, neg_mul, Matrix.neg_mul]

theorem curl_smul (α : Lk n → ℝ) (A : Su N) (q : Pq n) :
    prof α A (e1 q) + prof α A (e2 q) - prof α A (e3 q) - prof α A (e4 q) = ((curl α q : ℝ) : ℂ) • A.X := by
  unfold prof curl
  push_cast
  simp only [add_smul, sub_smul]

/-- **The profile derivative of one plaquette density** is curl times the curvature current plus the residual.
DERIVED: `−1/N` the Wilson normalization. -/
theorem sum_dplaq (α : Lk n → ℝ) (A : Su N) (q : Pq n) (U : Lk n → SUN.SU N) :
    ∑ l, α l * dplaq l A q U
      = -(1 / (N : ℝ)) * (curl α q * rt (A.X * holM U q) + rt (residQ α A U q)) := by
  simp only [dplaq_eq]
  have h1 : ∑ l, α l * (-(1 / (N : ℝ)) * rt (dHol (cOf l A (e1 q)) (cOf l A (e2 q)) (cOf l A (e3 q))
      (cOf l A (e4 q)) (lk U (e1 q)) (lk U (e2 q)) (lki U (e3 q)) (lki U (e4 q))))
      = -(1 / (N : ℝ)) * rt (∑ l, ((α l : ℝ) : ℂ) • dHol (cOf l A (e1 q)) (cOf l A (e2 q))
          (cOf l A (e3 q)) (cOf l A (e4 q)) (lk U (e1 q)) (lk U (e2 q)) (lki U (e3 q)) (lki U (e4 q))) := by
    rw [rt_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [rt_real_smul]
    ring
  rw [h1, sum_smul_dHol, sum_cOf, sum_cOf, sum_cOf, sum_cOf, dHol_split, curl_smul, rt_add, Matrix.smul_mul,
    rt_real_smul]
  rfl

/-- **The profile derivative of the action** `Σ_ℓ α_ℓ (β DS_in + t DS_mix)`. No numeral. -/
def dSprof (α : Lk n → ℝ) (A : Su N) (β t : ℝ) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ l, α l * (β * dSin l A U + t * dSmix l A U)

theorem act_split (l : Lk n) (A : Su N) (β t : ℝ) (U : Lk n → SUN.SU N) :
    β * dSin l A U + t * dSmix l A U
      = ∑ q : Pq n, (if AnisoTorus.inPlane q.1 then β else t) * dplaq l A q U := by
  unfold dSin dSmix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-- **The profile current on the torus**: curvature current of `dα` plus the residual, plaquette by plaquette.
DERIVED: `−1/N` the Wilson normalization. -/
theorem dSprof_eq (α : Lk n → ℝ) (A : Su N) (β t : ℝ) (U : Lk n → SUN.SU N) :
    dSprof α A β t U = ∑ q : Pq n, (if AnisoTorus.inPlane q.1 then β else t)
      * (-(1 / (N : ℝ)) * (curl α q * rt (A.X * holM U q) + rt (residQ α A U q))) := by
  unfold dSprof
  simp only [act_split, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← sum_dplaq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The residual of every plaquette vanishes when the colour commutes with every link.** No numeral. -/
theorem residQ_eq_zero_of_commute (α : Lk n → ℝ) (A : Su N) (U : Lk n → SUN.SU N)
    (hk : ∀ m, Commute (lk U m) A.X) (hi : ∀ m, Commute (lki U m) A.X) (q : Pq n) :
    residQ α A U q = 0 := by
  unfold residQ prof
  refine resid_eq_zero_of_commute ((hk _).smul_right _) ?_ ?_
  · exact (((hk _).mul_left (hk _)).mul_left (hi _)).smul_right _
  · unfold hol4
    exact ((((hk _).mul_left (hk _)).mul_left (hi _)).mul_left (hi _)).smul_right _

/-! ## 4. The stiffness Ward identity -/

/-- **The stiffness Ward identity of a profile link shift**, exact at every `β`, `t`, side `n`, `N`:
`⟨Σ_ℓ α_ℓ D_ℓ O − O · DS_α⟩ = 0`, with `DS_α` the curvature current of `dα` plus the residual (`dSprof_eq`).
No numeral. -/
theorem ward_profile (α : Lk n → ℝ) (A : Su N) (β t : ℝ) {O : (Lk n → SUN.SU N) → ℝ} (hO : Continuous O)
    {DO : Lk n → (Lk n → SUN.SU N) → ℝ} (hg : ∀ l, IsGen (linkFlow l A) O (DO l)) :
    ∫ U, ((∑ l, α l * DO l U) - O U * dSprof α A β t U) * wt N β t n U ∂piH N n = 0 := by
  have hc : ∀ l, Continuous fun U : Lk n → SUN.SU N =>
      α l * ((DO l U - O U * (β * dSin l A U + t * dSmix l A U)) * wt N β t n U) := fun l =>
    continuous_const.mul (((hg l).1.sub (hO.mul ((continuous_const.mul (isGen_sin_link l A).1).add
      (continuous_const.mul (isGen_smix_link l A).1)))).mul (continuous_wt β t))
  have e : ∀ U, ((∑ l, α l * DO l U) - O U * dSprof α A β t U) * wt N β t n U
      = ∑ l, α l * ((DO l U - O U * (β * dSin l A U + t * dSmix l A U)) * wt N β t n U) := by
    intro U
    unfold dSprof
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [e]
  rw [integral_finsetSum _ fun l _ => integrable_of_cont (hc l)]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_const_mul, sd_link l A β t hO (hg l), mul_zero]

/-- **The mean profile current vanishes**: `⟨J_X(dα)⟩ = −⟨R_α⟩` in the form `⟨DS_α⟩ = 0`. No numeral. -/
theorem ward_mean (α : Lk n → ℝ) (A : Su N) (β t : ℝ) :
    ∫ U, dSprof α A β t U * wt N β t n U ∂piH N n = 0 := by
  have h := ward_profile (N := N) (n := n) α A β t (O := fun _ => 1) continuous_const
    (DO := fun _ _ => 0) fun _ => IsGen.of_inv fun _ _ => rfl
  simpa [integral_neg] using h

/-! ## 5. From a stiffness bound to a twisted ratio -/

/-- **A stiffness bound along a twist path bounds the free-energy cost**: `f(0) = f'(0) = 0` and `f'' ≤ ε` on
`[0, θ₀]` give `f(θ₀) ≤ ε θ₀² / 2`. DERIVED: `2` the square. -/
theorem freeEnergy_le {f f' f'' : ℝ → ℝ} {ε θ₀ : ℝ} (hθ : 0 ≤ θ₀) (hf : ∀ θ, HasDerivAt f (f' θ) θ)
    (hf' : ∀ θ, HasDerivAt f' (f'' θ) θ) (h0 : f 0 = 0) (h0' : f' 0 = 0)
    (hb : ∀ θ ∈ Icc 0 θ₀, f'' θ ≤ ε) : f θ₀ ≤ ε * θ₀ ^ 2 / 2 := by
  have hg1 : ∀ x, HasDerivAt (fun θ => ε * θ - f' θ) (ε - f'' x) x := fun x => by
    exact (((hasDerivAt_id x).const_mul ε).sub (hf' x)).congr_deriv (by ring)
  have hm1 : MonotoneOn (fun θ => ε * θ - f' θ) (Icc 0 θ₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 θ₀) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun x => (hg1 x).continuousAt).continuousOn
    · exact fun x _ => (hg1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hg1 x).deriv]
      linarith [hb x (Ioo_subset_Icc_self hx)]
  have hg2 : ∀ x, HasDerivAt (fun θ => ε * (θ * θ) / 2 - f θ) (ε * x - f' x) x := fun x =>
    (((((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul ε).div_const 2).sub (hf x)).congr_deriv (by
      simp only [id]; ring)
  have hm2 : MonotoneOn (fun θ => ε * (θ * θ) / 2 - f θ) (Icc 0 θ₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 θ₀) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun x => (hg2 x).continuousAt).continuousOn
    · exact fun x _ => (hg2 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hg2 x).deriv]
      have := hm1 (left_mem_Icc.2 hθ) (Ioo_subset_Icc_self hx) (le_of_lt hx.1)
      simp only [h0', mul_zero, sub_zero] at this
      linarith
  have := hm2 (left_mem_Icc.2 hθ) (right_mem_Icc.2 hθ) hθ
  simp only [h0] at this
  rw [sq]
  linarith

/-- **The twisted ratio from a stiffness bound**: `Z_{θ₀}/Z_0 = e^{−f(θ₀)} ≥ e^{−ε θ₀²/2}`. DERIVED: `2` the
square. -/
theorem twistRatio_ge {f f' f'' : ℝ → ℝ} {ε θ₀ : ℝ} (hθ : 0 ≤ θ₀) (hf : ∀ θ, HasDerivAt f (f' θ) θ)
    (hf' : ∀ θ, HasDerivAt f' (f'' θ) θ) (h0 : f 0 = 0) (h0' : f' 0 = 0)
    (hb : ∀ θ ∈ Icc 0 θ₀, f'' θ ≤ ε) : Real.exp (-(ε * θ₀ ^ 2 / 2)) ≤ Real.exp (-f θ₀) :=
  Real.exp_le_exp.2 (neg_le_neg (freeEnergy_le hθ hf hf' h0 h0' hb))

end MassGap.GaugeStiffness

#print axioms MassGap.GaugeStiffness.dHol_split
#print axioms MassGap.GaugeStiffness.br_sub_one
#print axioms MassGap.GaugeStiffness.resid_eq_zero_of_commute
#print axioms MassGap.GaugeStiffness.resid_comm
#print axioms MassGap.GaugeStiffness.resid_su2
#print axioms MassGap.GaugeStiffness.resid_su2_ne
#print axioms MassGap.GaugeStiffness.dLk_eq
#print axioms MassGap.GaugeStiffness.dLi_eq
#print axioms MassGap.GaugeStiffness.dplaq_eq
#print axioms MassGap.GaugeStiffness.sum_cOf
#print axioms MassGap.GaugeStiffness.sum_smul_dHol
#print axioms MassGap.GaugeStiffness.curl_smul
#print axioms MassGap.GaugeStiffness.sum_dplaq
#print axioms MassGap.GaugeStiffness.act_split
#print axioms MassGap.GaugeStiffness.dSprof_eq
#print axioms MassGap.GaugeStiffness.residQ_eq_zero_of_commute
#print axioms MassGap.GaugeStiffness.ward_profile
#print axioms MassGap.GaugeStiffness.ward_mean
#print axioms MassGap.GaugeStiffness.freeEnergy_le
#print axioms MassGap.GaugeStiffness.twistRatio_ge
