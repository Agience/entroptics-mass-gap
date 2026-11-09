import Mathlib
import MassGap.StallRigid
import MassGap.TwoDVanish
import MassGap.AnisoTorus

/-!
# MassGap.U1Strip — the `U(1)` anisotropic torus, its character orthogonality, and the faces of a plane

The constant-width strip asks for a `t₁ > 0` independent of `β` such that `DA(β, t, ·) → 0` along the windows for every
`β ≥ 0` and `0 ≤ t ≤ t₁`, with a transfer gap uniform in the torus size. For `U(1)` the argued reason it is shorter than
for `SU(N)` is that the face variables of a plane are i.i.d. up to one torus constraint, so the second layer of
`StripTail` (the average of `exp Σ_x y_x` over the plane measures) is a weak interaction of i.i.d. variables whose
single-variable law is the only place `β` enters. This module builds the `U(1)` objects and proves the exact abelian
facts that argument rests on. It does not prove the strip. Declarations are in `MassGap.U1Strip`.

## The result

* `sys4 n`, `Sin`, `Smix`, `ZA`, `logZA`, `DA`: the anisotropic Wilson torus of `AnisoTorus` with `Circle` in place of
  `SU(N)` and the density `GaugeGroup.wilsonDensityG Circle = 1 − Re z` (`StallRigid.instGaugeGroupCircle`), the
  in-plane coupling `β` on the `(0,1)` and `(2,3)` orientations and `t` on the mixed ones. `sin_add_smix`, `ZA_iso`:
  `ZA β β n = TorusDoubling.ZT Circle 4 wd β n`; `DA_iso`: `DA β β w = TorusDoubling.defectWG Circle 4 wd β (2^w)`.
* `integral_zpow`: `∫ z^m d(Haar) = [m = 0]` on `Circle`, from left invariance and one element with `a^m ≠ 1`.
  `integral_prod_zpow`: on product Haar over any finite link set, `∫ ∏_l U_l^{m_l} = [m = 0]`.
* `word_prod`, `prod_hol_zpow`: in a commutative group the holonomy of a boundary word is `∏_l U_l^{cnt l}`, so
  `∏_p hol_p^{k_p} = ∏_l U_l^{(div k)_l}`, `(div k)_l = Σ_p cnt_p(l) k_p`, the signed incidence.
* `integral_hol_zpow`, `integral_hol_zpow_sys4`: for every Wilson system over `Circle`, the anisotropic torus included,
  `∫ ∏_p hol_p(U)^{k_p} = [div k = 0]`. This is the character orthogonality that gives the dual (integer-current)
  representation of the `U(1)` Wilson measure; at `SU(N)` the product of holonomies does not reduce to the links.
* `faces_char`: on the side-`n` plane torus, `n ≥ 2`, the faces `face x U = U₀(x) U₁(x+e₀) U₀(x+e₁)⁻¹ U₁(x)⁻¹` have
  `∫ ∏_x face(x)^{k_x} = [k constant]` for every `k : sites → ℤ`. These are the joint Fourier coefficients of the
  Haar measure of the subgroup `{∏_x z_x = 1}` of `Circle^{n²}`: under product Haar on the links the faces of a plane
  are i.i.d. Haar conditioned on their product. With the Wilson weight, which is a function of the faces, the faces
  of a plane are i.i.d. with law `∝ e^{−2β(1 − Re z)}` conditioned on their product (read off, not a Lean statement:
  the passage from Fourier coefficients to the measure needs uniqueness on `Circle^{n²}`, not built here).
* `face_eq_hol`: `face x U` is the tree's holonomy of the `(0,1)` plaquette at `x`. `faces_char` and `face_eq_hol` are
  about the stand-alone plane torus `sysT Circle 2 n`; their link to a plane slice of the four-dimensional torus is not stated.
* `Sin` ranges over ordered pairs of directions, so each in-plane orientation is counted in both orders and the diagonal
  terms vanish, as in the tree's `ZT`; this is why `ZA_iso` is exact.
* `cube_bianchi`: at `U(1)`, for the three-cube spanned by `e₀, e₁, e₂` at `x`,
  `hol₀₁(x) hol₀₁(x+e₂)⁻¹ = hol₁₂(x+e₀) hol₁₂(x)⁻¹ hol₀₂(x+e₁)⁻¹ hol₀₂(x)`. The four mixed faces of the cube read the
  two in-plane faces only through `hol₀₁(x) hol₀₁(x+e₂)⁻¹`, a product of face variables of two planes. At `SU(N)` the
  same tube reads `A P A⁻¹ P'` with a transport `A`, and this identity fails.

## The face-level argument (argued, not proved)

At `U(1)` the plane faces are i.i.d. up to their product (`faces_char`, in Fourier form), so a face-level Dobrushin
argument needs no contours, though a polymer count in the faces does not close. Given the faces, the residual
link freedom is a site field `ν` (the rotations of `MixCut.gT`), and every mixed angle is `Δ_a Δ_b ν + c`, with `c`
determined by the faces up to `ν`-shifts. The `ν`-invariant content of `c` is local: by `cube_bianchi` the sum of the
mixed angles over any closed tube is the sum of `θ(x, z) − θ(x, z + e₂)` over the enclosed faces. So a first-layer
term `y_x` reads the faces through flux sums over the hulls of its polymers. This is not finite range
in the faces, so the counting of `mass-gap-constant-strip.md` §3 (hulls of size `m²`) still fails for a polymer gas in
the faces. What survives is an influence bound: the derivative of a polymer of perimeter `m` in one enclosed face
is at most its activity `(c t)^m` times its charge, and at most `m²` positions of such a polymer enclose a given face,
so the Dobrushin column `Σ_f sup |∂_f Σ_x y_x|` is bounded by `Σ_m m² (C t)^m`, a function of `t` alone. Uniformity in
`β` is then the statement that Dobrushin's condition does not read the single-variable law. At `SU(N)` the tube reads
`χ(A P A⁻¹ P'⁻¹)` with `A` a column product of far faces, so a far face has influence of order one; there the
argument fails, as stated in `StripNest`. The sizes `m²`, `(c t)^m`, `C t`, `n^{−4}` in this paragraph are argued and not
claimed.

## What does not follow

* The constant-width strip is not proved for `U(1)`: no `t₁`, no `DA(β, t, ·) → 0`, no transfer gap. Nothing here
  crosses the crossover, and nothing here says anything about `SU(N)` at `t = β`, or about `U(1)` at `t = β`, where the
  four-dimensional theory at large `β` is in its Coulomb phase (Guth; Fröhlich–Spencer, cited).
* The port of the anisotropic chain is not done. `AnisoTorus`, `MixAnchor`, `StripLift` (through `StripGapThm`,
  `StripWidth`, `StripWiden`), `CumulantStrip`, `StripGas`, `StripOsc`, `StripTail` and `StripNest` are stated for
  `SUN.SU N` throughout (`StripGas.SiteGas` and `zg` integrate against `νS N`). `TorusDoubling` and the objects
  above are group-generic; the transfer kernel, the basin squaring and the seed-to-gap step are not.
* The missing step, in the order the argument needs it, all at `U(1)`, uniform in `β ≥ 0`:
  (i) the first layer of `StripGas` and `StripOsc` with `Circle` sites, and `y_x` written as a function of the faces
  and of the plane wrapping holonomies; (ii) the influence bound `Σ_f sup |∂_f Σ_x y_x| ≤ C(t)` with `C(t) → 0` as
  `t → 0`, not depending on `β` or `n`; (iii) Dobrushin uniqueness for i.i.d. faces conditioned on one product per
  plane, giving `|⟨y_x⟩_n − ⟨y_x⟩_{2n}| = o(n^{−4})` at fixed `β` (any rate, by `StripTail.tail_closes`); (iv) the
  interpolation `DA(β, t, w) − DA(β, 0, w) = 16 Σ ∫₀^t (⟨·⟩_n − ⟨·⟩_{2n})`, which closes the cost. None of these is
  proved here.
* `faces_char` is a statement about Fourier coefficients. The identification of the face law as a measure is not
  built. `n ≥ 2` is used for the reach of the shifts (`TwoDVanish.reach`).
* `integral_hol_zpow` gives the dual representation only for trigonometric-polynomial integrands. The Wilson weight
  is not expanded in characters here: no Bessel function is in the statement.

DERIVED (module-wide): `0`, `1`, `2`, `3` the directions; `4` the dimension; `2` the least side of `faces_char` and
the doubling; `16 = 2⁴` the copies; `1` the unit of the group and the empty product; `0` the zero current.
-/

namespace MassGap.U1Strip

open MeasureTheory Filter Topology Set MassGap MassGap.LatticeGauge MassGap.CompactGauge
open MassGap.TorusDoubling (TSite TLink TPlaq tshift tbd)

/-! ## 1. The `U(1)` anisotropic torus -/

/-- The `U(1)` Wilson density `1 − Re z`, the tree's `GaugeGroup.wilsonDensityG` at `Circle`. No numeral. -/
noncomputable abbrev wd : Circle → ℝ := GaugeGroup.wilsonDensityG Circle

/-- The `U(1)` Wilson system on the side-`n` four-torus. DERIVED: `4` the dimension. -/
noncomputable abbrev sys4 (n : ℕ) : System Circle := TorusDoubling.sysT Circle 4 n wd

/-- **The in-plane action** at `U(1)`: the density summed over the orientations of `AnisoTorus.inPlane`.
DERIVED: `0` the excluded terms; `4` the dimension. -/
noncomputable def Sin (n : ℕ) (U : (sys4 n).Config) : ℝ :=
  ∑ q : TPlaq 4 n, if AnisoTorus.inPlane q.1 then (sys4 n).φ ((sys4 n).hol q U) else 0

/-- **The mixed action** at `U(1)`. DERIVED: `0` the excluded terms; `4` the dimension. -/
noncomputable def Smix (n : ℕ) (U : (sys4 n).Config) : ℝ :=
  ∑ q : TPlaq 4 n, if AnisoTorus.inPlane q.1 then 0 else (sys4 n).φ ((sys4 n).hol q U)

/-- **The split of the action**: `S_in + S_mix = S`. DERIVED: `0` the excluded terms. -/
theorem sin_add_smix (n : ℕ) (U : (sys4 n).Config) : Sin n U + Smix n U = (sys4 n).action U := by
  unfold Sin Smix System.action
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : AnisoTorus.inPlane q.1 = true <;> simp [h]

/-- **The `U(1)` anisotropic partition function** `∫ e^{−(β S_in + t S_mix)}` against product Haar. No numeral. -/
noncomputable def ZA (β t : ℝ) (n : ℕ) : ℝ :=
  ∫ U, Real.exp (-(β * Sin n U + t * Smix n U)) ∂((sys4 n).vol (probHaar Circle))

/-- `log ZA`. No numeral. -/
noncomputable def logZA (β t : ℝ) (n : ℕ) : ℝ := Real.log (ZA β t n)

/-- **The `U(1)` anisotropic window defect** `16 log ZA(2^w) − log ZA(2^{w+1})`. DERIVED: `16 = 2⁴` the copies; `2`
the doubling; `1` the next window. -/
noncomputable def DA (β t : ℝ) (w : ℕ) : ℝ := 16 * logZA β t (2 ^ w) - logZA β t (2 ^ (w + 1))

/-- **The isotropic end**: `ZA β β n` is the tree's `U(1)` torus partition function. DERIVED: `4` the dimension. -/
theorem ZA_iso (β : ℝ) (n : ℕ) : ZA β β n = TorusDoubling.ZT Circle 4 wd β n := by
  unfold ZA TorusDoubling.ZT System.partition System.boltz
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  dsimp only
  rw [← mul_add, sin_add_smix, neg_mul]

/-- **The isotropic end of the defect**: `DA β β w` is the tree's `U(1)` doubling defect at side `2^w`. DERIVED: `4`
the dimension; `2` the doubling. -/
theorem DA_iso (β : ℝ) (w : ℕ) : DA β β w = TorusDoubling.defectWG Circle 4 wd β (2 ^ w) := by
  unfold DA logZA TorusDoubling.defectWG
  rw [ZA_iso, ZA_iso, pow_succ' 2 w]
  norm_num

/-! ## 2. Character orthogonality on `Circle` -/

/-- Every nonzero exponent has an element of `Circle` it does not send to `1`: `e^{iπ/m}`. DERIVED: `0` the
excluded exponent; `1` the unit. -/
theorem exists_zpow_ne_one {m : ℤ} (hm : m ≠ 0) : ∃ a : Circle, a ^ m ≠ 1 := by
  refine ⟨Circle.exp (Real.pi / m), ?_⟩
  rw [← Circle.exp_intCast_mul]
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
  rw [show (m : ℝ) * (Real.pi / m) = Real.pi by field_simp]
  exact Circle.exp_pi_ne_one

/-- **The characters of `Circle` are orthogonal to the constant**: `∫ z^m d(Haar) = [m = 0]`. DERIVED: `0` the
trivial character; `1` the mass of the probability measure. -/
theorem integral_zpow (m : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ m ∂(probHaar Circle) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp
  · obtain ⟨a, ha⟩ := exists_zpow_ne_one hm
    have h : (a : ℂ) ^ m * ∫ z : Circle, (z : ℂ) ^ m ∂(probHaar Circle)
        = ∫ z : Circle, (z : ℂ) ^ m ∂(probHaar Circle) := by
      rw [← integral_const_mul]
      conv_rhs => rw [← integral_mul_left_eq_self (μ := probHaar Circle) (fun z : Circle => (z : ℂ) ^ m) a]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Circle.coe_mul, mul_zpow]
    have ha' : (a : ℂ) ^ m ≠ 1 := by
      intro h1
      apply ha
      rw [← Circle.coe_zpow] at h1
      exact Circle.coe_eq_one.mp h1
    have h2 : ((a : ℂ) ^ m - 1) * ∫ z : Circle, (z : ℂ) ^ m ∂(probHaar Circle) = 0 := by
      rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) ha'
    · exact h0

/-- **Orthogonality on product Haar**: `∫ ∏_l U_l^{m_l} = [m = 0]` over any finite link set. DERIVED: `0` the zero
exponent field; `1` the empty product. -/
theorem integral_prod_zpow {L : Type} [Fintype L] [DecidableEq L] (m : L → ℤ) :
    ∫ U : L → Circle, ∏ l, (U l : ℂ) ^ m l ∂(Measure.pi fun _ => probHaar Circle)
      = if m = 0 then 1 else 0 := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun l (z : Circle) => (z : ℂ) ^ m l)
    (μ := fun _ : L => probHaar Circle)
  rw [show (∫ U : L → Circle, ∏ l, (U l : ℂ) ^ m l ∂(Measure.pi fun _ => probHaar Circle))
      = ∏ l, ∫ z : Circle, (z : ℂ) ^ m l ∂(probHaar Circle) from h]
  simp_rw [integral_zpow]
  split_ifs with hm
  · simp [hm]
  · obtain ⟨l, hl⟩ : ∃ l, m l ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hm (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])

/-! ## 3. Abelian holonomies -/

section Abelian

variable {G : Type} [CommGroup G] {L : Type} [Fintype L] [DecidableEq L]

/-- The sign of an orientation. DERIVED: `1`, `−1` the two orientations. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The signed number of times a word passes the link `l`. DERIVED: `0` the other links. -/
def cnt (w : List (L × Bool)) (l : L) : ℤ := (w.map fun lo => if lo.1 = l then sgn lo.2 else 0).sum

/-- **The signed incidence of a current** `k` on the plaquettes: `(div k)_l = Σ_p cnt_p(l) k_p`. No numeral. -/
def divK {P : Type} [Fintype P] (bd : P → List (L × Bool)) (k : P → ℤ) (l : L) : ℤ :=
  ∑ p, cnt (bd p) l * k p

/-- A product of powers of one element is the power of the sum. No numeral. -/
theorem prod_zpow_sum {ι : Type} (s : Finset ι) (a : G) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

/-- **An abelian word is a product of link powers**: `∏_{(l,b) ∈ w} U_l^{±1} = ∏_l U_l^{cnt w l}`. DERIVED: `0` the
other links. -/
theorem word_prod (w : List (L × Bool)) (U : L → G) :
    (w.map fun lo => if lo.2 then U lo.1 else (U lo.1)⁻¹).prod = ∏ l, U l ^ cnt w l := by
  induction w with
  | nil => simp [cnt]
  | cons lo w ih =>
    obtain ⟨l0, b0⟩ := lo
    rw [List.map_cons, List.prod_cons, ih]
    simp only [cnt, List.map_cons, List.sum_cons, zpow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single l0]
    · cases b0 <;> simp [sgn]
    · intro b _ hb
      simp [hb.symm]
    · simp

/-- **The product of plaquette powers is a product of link powers**: `∏_p hol_p^{k_p} = ∏_l U_l^{(div k)_l}`, in a
commutative group. No numeral. -/
theorem prod_hol_zpow {P : Type} [Fintype P] (bd : P → List (L × Bool)) (k : P → ℤ) (U : L → G) :
    ∏ p, WilsonLattice.wilsonHol bd p U ^ k p = ∏ l, U l ^ divK bd k l := by
  unfold WilsonLattice.wilsonHol divK
  simp_rw [word_prod, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun l _ => prod_zpow_sum _ _ _

end Abelian

/-- The coercion `Circle → ℂ` takes products to products. No numeral. -/
theorem coe_prod {ι : Type} (s : Finset ι) (f : ι → Circle) :
    ((∏ i ∈ s, f i : Circle) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod Circle.coeHom f s

/-- **The dual representation at `U(1)`**: for every Wilson system over `Circle` and every integer current `k` on
the plaquettes, `∫ ∏_p hol_p(U)^{k_p} = [div k = 0]` on product Haar. DERIVED: `0` the zero divergence; `1` the
empty product. -/
theorem integral_hol_zpow {P L : Type} [Fintype P] [Fintype L] [DecidableEq L]
    (bd : P → List (L × Bool)) (k : P → ℤ) :
    ∫ U : L → Circle, ∏ p, ((WilsonLattice.wilsonHol bd p U : Circle) : ℂ) ^ k p
        ∂(Measure.pi fun _ => probHaar Circle)
      = if divK bd k = 0 then 1 else 0 := by
  have h : ∀ U : L → Circle, ∏ p, ((WilsonLattice.wilsonHol bd p U : Circle) : ℂ) ^ k p
      = ∏ l, (U l : ℂ) ^ divK bd k l := by
    intro U
    have h1 := congrArg (fun g : Circle => (g : ℂ)) (prod_hol_zpow bd k U)
    simp only [coe_prod, Circle.coe_zpow] at h1
    exact h1
  simp_rw [h]
  exact integral_prod_zpow _

/-- **The dual representation on the `U(1)` anisotropic torus**: `∫ ∏_q hol_q(U)^{k_q} = [div k = 0]`. DERIVED: `4`
the dimension; `0` the zero divergence; `1` the empty product. -/
theorem integral_hol_zpow_sys4 (n : ℕ) (k : TPlaq 4 n → ℤ) :
    ∫ U, ∏ q, ((sys4 n).hol q U : ℂ) ^ k q ∂((sys4 n).vol (probHaar Circle))
      = if divK (tbd 4 n) k = 0 then 1 else 0 :=
  integral_hol_zpow (tbd 4 n) k

/-! ## 4. The faces of a plane are i.i.d. up to their product -/

section Plane

variable {n : ℕ}

/-- The shift in direction `i` as a permutation of the sites. No numeral. -/
def shiftE {d : ℕ} (i : Fin d) : TSite d n ≃ TSite d n where
  toFun := tshift i
  invFun x := Function.update x i ((finRotate n).symm (x i))
  left_inv x := by
    simp only [tshift, Function.update_self, Equiv.symm_apply_apply, Function.update_idem,
      Function.update_eq_self]
  right_inv x := by
    simp only [tshift, Function.update_self, Equiv.apply_symm_apply, Function.update_idem,
      Function.update_eq_self]

/-- The permutation acts as the shift. No numeral. -/
theorem shiftE_apply {d : ℕ} (i : Fin d) (x : TSite d n) : shiftE i x = tshift i x := rfl

/-- **The `(0,1)` face at `U(1)`**: `U₀(x) U₁(x+e₀) U₀(x+e₁)⁻¹ U₁(x)⁻¹`. DERIVED: `0`, `1` the two directions. -/
noncomputable def face (x : TSite 2 n) (U : TLink 2 n → Circle) : Circle :=
  U (0, x) * U (1, tshift 0 x) * (U (0, tshift 1 x))⁻¹ * (U (1, x))⁻¹

/-- The face is the tree's holonomy of the `(0,1)` plaquette. DERIVED: `0`, `1` the two directions; `2` the
dimension. -/
theorem face_eq_hol (φ : Circle → ℝ) (x : TSite 2 n) (U : TLink 2 n → Circle) :
    face x U = (TorusDoubling.sysT Circle 2 n φ).hol ((0, 1), x) U := by
  rw [TorusDoubling.hol_eq]
  rfl

/-- The second direction of the plane is not the first. DERIVED: `0`, `1` the two directions. -/
theorem fin_one_ne : ((1 : Fin 2) = 0) = False := eq_false (by decide)

/-- The link exponents of `∏_x face(x)^{k_x}`. DERIVED: `0` the first direction. -/
def faceExp (k : TSite 2 n → ℤ) (l : TLink 2 n) : ℤ :=
  if l.1 = 0 then k l.2 - k ((shiftE 1).symm l.2) else k ((shiftE 0).symm l.2) - k l.2

/-- `∏_x face(x)^{k_x} = ∏_l U_l^{faceExp k l}`. DERIVED: `0`, `1` the two directions; `2` the dimension. -/
theorem prod_face_zpow (k : TSite 2 n → ℤ) (U : TLink 2 n → Circle) :
    ∏ x, face x U ^ k x = ∏ l, U l ^ faceExp k l := by
  have hL : ∏ x, face x U ^ k x = (∏ x, U (0, x) ^ k x) * (∏ x, U (1, shiftE 0 x) ^ k x)
      * (∏ x, (U (0, shiftE 1 x) ^ k x)⁻¹) * (∏ x, (U (1, x) ^ k x)⁻¹) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp only [face, mul_zpow, inv_zpow, shiftE_apply]
  have hB : ∏ x, U (1, shiftE 0 x) ^ k x = ∏ y, U (1, y) ^ k ((shiftE 0).symm y) := by
    have := (shiftE (n := n) (0 : Fin 2)).prod_comp (fun y => U (1, y) ^ k ((shiftE 0).symm y))
    simp only [Equiv.symm_apply_apply] at this
    exact this
  have hC : ∏ x, (U (0, shiftE 1 x) ^ k x)⁻¹ = ∏ y, (U (0, y) ^ k ((shiftE 1).symm y))⁻¹ := by
    have := (shiftE (n := n) (1 : Fin 2)).prod_comp (fun y => (U (0, y) ^ k ((shiftE 1).symm y))⁻¹)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  have hR : ∏ l, U l ^ faceExp k l = (∏ y, U (0, y) ^ k y) * (∏ y, (U (0, y) ^ k ((shiftE 1).symm y))⁻¹)
      * ((∏ y, U (1, y) ^ k ((shiftE 0).symm y)) * ∏ y, (U (1, y) ^ k y)⁻¹) := by
    rw [Fintype.prod_prod_type, Fin.prod_univ_two]
    simp only [faceExp, fin_one_ne, ↓reduceIte, reduceIte, zpow_sub, Finset.prod_mul_distrib]
  rw [hL, hB, hC, hR]
  ac_rfl

/-- A site function invariant under both shifts is constant, at `n ≥ 2`. DERIVED: `0`, `1` the two directions; `2`
the least side. -/
theorem const_of_shift_inv (hn : 2 ≤ n) {k : TSite 2 n → ℤ}
    (h : ∀ (i : Fin 2) (x : TSite 2 n), k (tshift i x) = k x) (x y : TSite 2 n) : k x = k y := by
  have hit : ∀ (i : Fin 2) (j : ℕ) (z : TSite 2 n), k ((tshift i)^[j] z) = k z := by
    intro i j
    induction j with
    | zero => intro z; rfl
    | succ j ih => intro z; rw [Function.iterate_succ_apply', h, ih]
  have hupd : ∀ (i : Fin 2) (z : TSite 2 n) (b : Fin n), k (Function.update z i b) = k z := by
    intro i z b
    obtain ⟨j, hj⟩ := TwoDVanish.reach hn (z i) b
    rw [← hj, ← TwoDVanish.tshift_iter, hit]
  have hxy : Function.update (Function.update y 0 (x 0)) 1 (x 1) = x := by
    funext c
    fin_cases c <;> simp
  rw [← hxy, hupd, hupd]

/-- **The Fourier coefficients of the faces of a plane**: `∫ ∏_x face(x)^{k_x} = [k constant]` on product
Haar over the links of the side-`n` plane, `n ≥ 2`. DERIVED: `2` the least side; `0`, `1` the values of the
indicator. -/
theorem faces_char (hn : 2 ≤ n) (k : TSite 2 n → ℤ) :
    ∫ U : TLink 2 n → Circle, ∏ x, (face x U : ℂ) ^ k x ∂(Measure.pi fun _ => probHaar Circle)
      = if ∀ x y, k x = k y then 1 else 0 := by
  have h : ∀ U : TLink 2 n → Circle, ∏ x, (face x U : ℂ) ^ k x = ∏ l, (U l : ℂ) ^ faceExp k l := by
    intro U
    have h1 := congrArg (fun g : Circle => (g : ℂ)) (prod_face_zpow k U)
    simp only [coe_prod, Circle.coe_zpow] at h1
    exact h1
  simp_rw [h]
  rw [integral_prod_zpow]
  refine if_congr ?_ rfl rfl
  constructor
  · intro hm
    have h0 : ∀ y, k ((shiftE 1).symm y) = k y := fun y => by
      have := congrFun hm ((0 : Fin 2), y)
      simp only [faceExp, ↓reduceIte, reduceIte, Pi.zero_apply] at this
      omega
    have h1 : ∀ y, k ((shiftE 0).symm y) = k y := fun y => by
      have := congrFun hm ((1 : Fin 2), y)
      simp only [faceExp, fin_one_ne, ↓reduceIte, reduceIte, Pi.zero_apply] at this
      omega
    refine const_of_shift_inv hn fun i x => ?_
    fin_cases i
    · have := h1 (shiftE 0 x)
      rw [Equiv.symm_apply_apply] at this
      exact this.symm
    · have := h0 (shiftE 1 x)
      rw [Equiv.symm_apply_apply] at this
      exact this.symm
  · intro hc
    funext l
    simp only [faceExp, Pi.zero_apply]
    split_ifs
    · rw [hc ((shiftE 1).symm l.2) l.2, sub_self]
    · rw [hc ((shiftE 0).symm l.2) l.2, sub_self]

end Plane

/-! ## 5. The Bianchi identity of a three-cube at `U(1)` -/

/-- Shifts in different directions commute. No numeral. -/
theorem tshift_comm {d n : ℕ} {i j : Fin d} (h : i ≠ j) (x : TSite d n) :
    tshift i (tshift j x) = tshift j (tshift i x) := by
  unfold tshift
  rw [Function.update_of_ne h, Function.update_of_ne h.symm]
  exact Function.update_comm h.symm _ _ _

/-- **The three-cube at `U(1)`**: `hol₀₁(x) hol₀₁(x+e₂)⁻¹ = hol₁₂(x+e₀) hol₁₂(x)⁻¹ hol₀₂(x+e₁)⁻¹ hol₀₂(x)`. The four
mixed faces of the cube read its two in-plane faces through `hol₀₁(x) hol₀₁(x+e₂)⁻¹` only. DERIVED: `0`, `1`, `2` the
three directions of the cube; `4` the dimension. -/
theorem cube_bianchi (n : ℕ) (U : TLink 4 n → Circle) (x : TSite 4 n) :
    (sys4 n).hol ((0, 1), x) U * ((sys4 n).hol ((0, 1), tshift 2 x) U)⁻¹
      = (sys4 n).hol ((1, 2), tshift 0 x) U * ((sys4 n).hol ((1, 2), x) U)⁻¹
        * ((sys4 n).hol ((0, 2), tshift 1 x) U)⁻¹ * (sys4 n).hol ((0, 2), x) U := by
  simp only [sys4, TorusDoubling.hol_eq]
  rw [tshift_comm (i := (0 : Fin 4)) (j := 2) (by decide) x,
    tshift_comm (i := (1 : Fin 4)) (j := 2) (by decide) x,
    tshift_comm (i := (1 : Fin 4)) (j := 0) (by decide) x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end MassGap.U1Strip

#print axioms MassGap.U1Strip.sin_add_smix
#print axioms MassGap.U1Strip.ZA_iso
#print axioms MassGap.U1Strip.DA_iso
#print axioms MassGap.U1Strip.exists_zpow_ne_one
#print axioms MassGap.U1Strip.integral_zpow
#print axioms MassGap.U1Strip.integral_prod_zpow
#print axioms MassGap.U1Strip.prod_zpow_sum
#print axioms MassGap.U1Strip.word_prod
#print axioms MassGap.U1Strip.prod_hol_zpow
#print axioms MassGap.U1Strip.coe_prod
#print axioms MassGap.U1Strip.integral_hol_zpow
#print axioms MassGap.U1Strip.integral_hol_zpow_sys4
#print axioms MassGap.U1Strip.shiftE_apply
#print axioms MassGap.U1Strip.face_eq_hol
#print axioms MassGap.U1Strip.prod_face_zpow
#print axioms MassGap.U1Strip.const_of_shift_inv
#print axioms MassGap.U1Strip.fin_one_ne
#print axioms MassGap.U1Strip.faces_char
#print axioms MassGap.U1Strip.tshift_comm
#print axioms MassGap.U1Strip.cube_bianchi
