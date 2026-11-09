import Mathlib
import MassGap.TwoDVanish
import MassGap.CoverCompact

/-!
# MassGap.StripGap — the spectral gap of the plaquette walk on `SU(N)`, at scale `1/β`

The face weight of the 2D torus is `wt = e^{−2β φ}` (`wt_eq`), `b = ∫ wt`. Convolution by `p = wt/b` is the plaquette
walk. `TwoDVanish` reads it through the floor `wt ≥ e^{−4β}`, which is exponentially weak. This module proves the true
scale: the walk contracts mean-zero functions at rate `1 − 1/ℓ`, `ℓ = 240 + 150 (N + 4) β`, with no character
expansion, no heat kernel and no Lie theory beyond the diagonalization of a unitary matrix. Declarations are in
`MassGap.StripGap`.

## The gap (proved)

For a symmetric class density `p` (`Dens`), `P f (x) = ∫ f(xz) p(z) dz`, `Φ(g) = ∫ (f(xg) − f(x))² dx`,
`B(y) = ∫ (f(xy) − Pf(x))² dx`:

* `En_eq`: `E = ∫ B p = ∫ f² − ∫ (Pf)²`, the variance identity.
* `Phi_le`: `Φ(g) ≤ 2 B(y) + 2 B(y g)` for every `y`. Weighted by `min(p(y), p(yg))`, `Phi_mul_ovl`:
  `Φ(g) · ovl(g) ≤ 4 E`. So the energy of the walk controls `Φ` at every `g` whose translate of `p` overlaps `p`.
* `ovl_ge`: `ovl(h h) ≥ c²/2` from the pointwise Hellinger bound `(c p(y))² ≤ p(y h⁻¹) p(y h)`.
* `wilson_par`: `φ(y h) + φ(y h⁻¹) ≤ 2 φ(y) + 2 φ(h)`, from `tr(M M*) ≥ 0`, `M = (1 − h)(1 − y)`. There is no first-order
  term, so `pW_hellinger` holds with `c = e^{−2β φ(h)}`, a constant as soon as `φ(h) ≲ 1/β`. This is the step that
  makes the scale `1/β` and not `1/β²`.
* `exists_root`: every `x` is `(h h)^k` with `φ(h) ≤ π² (N + 4)/(8 k²)`. `Phi_pow`: `Φ(u^k) ≤ k² Φ(u)`.
* `Phi_mean`: `∫ Φ = 2 ∫ f²` for mean-zero `f`. So `contraction`, `walk_contract`, `walk_gap`.

## The powers and the bulk (proved)

`Fk p k` is the `(k + 1)`-fold convolution of `p`. `Fk_sq`: `∫ (F_k − 1)²` contracts. `Fk_sup`: Cauchy–Schwarz against
`p` turns that into a sup bound. `Fk_equil`: `|F_{m+1} − 1| ≤ e^{−m/(2ℓ)}/b`. `bk_ge`: `1 ≤ e K^{2N²} b`, `K` the bins of
a grid of mesh `1/√(2N(β+1))` in the real coordinates of a matrix: two elements of one bin have `φ(x⁻¹y) ≤ 1/(2(β+1))`
(`density_diff`), so `e · wt(x⁻¹ y) ≥ 1`, and integrating over `y` needs no measurability of the cells.

DERIVED (module-wide): `2` the squares, the parallelogram, the two translates; `4 = 2 + 2`; `8 = 2 · 4`; `N + 4` bounds
the mean square of the angles, one angle `(N + 1) π`, the others `π`; `2 N²` the real coordinates of a matrix; `1`
the mass. COMPUTED: `4 e² ≤ 30`, `π² ≤ 10`; `240 = 30 · 8`, `150 = 30 · 2 · 10/4` in `gapArea`. CHOSEN: `c = e⁻¹`, the
overlap at which `h` is called small; `k = ⌈√X⌉ + 1`; the mesh of `bk_ge`.

## What does not follow

`ℓ` is linear in `N`, from the crude choice of angles in `exists_root`; the sharp rate is not claimed. The sup bound
carries the factor `1/b`, polynomial in `β` of degree of order `N²`, so `|F_m − 1|` is small only from `m ~ ℓ N² log β`.
Nothing here is a statement about the 4D theory; `StripRow` and `StripWidth` carry it there. The gap is a property of
the walk on a compact group and does not separate `SU(N)` from any other group with the root property.
-/

namespace MassGap.StripGap

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)

variable {N : ℕ}

/-- Normalized Haar on `SU(N)`. No numeral. -/
noncomputable abbrev hm (N : ℕ) : Measure (SU N) := probHaar (SU N)

theorem int_of_cont {f : SU N → ℝ} (hf : Continuous f) : Integrable f (hm N) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem swap_int {F : SU N → SU N → ℝ} (hF : Continuous fun q : SU N × SU N => F q.1 q.2) :
    ∫ x, ∫ y, F x y ∂hm N ∂hm N = ∫ y, ∫ x, F x y ∂hm N ∂hm N := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact integral_integral_swap (f := F) (ContactFloor.integrable_of_bounded hF.measurable M fun z => by
    have hz := hM z (mem_univ z)
    rwa [Real.norm_eq_abs] at hz)

theorem cont_int {F : SU N → SU N → ℝ} (hF : Continuous fun q : SU N × SU N => F q.1 q.2) :
    Continuous fun x => ∫ y, F x y ∂hm N := by
  have hF' : Continuous (Function.uncurry F) := hF
  have h := continuous_parametric_integral_of_continuous (μ := hm N) hF' isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

theorem const_prob (c : ℝ) : ∫ _x : SU N, c ∂hm N = c := ContactFloor.integral_const_prob _ _

theorem c_cmul (c : ℝ) {g : SU N → ℝ} (hg : Continuous g) : Continuous fun x => c * g x :=
  continuous_const.mul hg

theorem c_mulc (c : ℝ) {g : SU N → ℝ} (hg : Continuous g) : Continuous fun x => g x * c :=
  hg.mul continuous_const

theorem c_add {f g : SU N → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x + g x := hf.add hg

theorem c_sub {f g : SU N → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x - g x := hf.sub hg

theorem iadd {f g : SU N → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x, (f x + g x) ∂hm N = ∫ x, f x ∂hm N + ∫ x, g x ∂hm N :=
  integral_add (int_of_cont hf) (int_of_cont hg)

theorem isub {f g : SU N → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x, (f x - g x) ∂hm N = ∫ x, f x ∂hm N - ∫ x, g x ∂hm N :=
  integral_sub (int_of_cont hf) (int_of_cont hg)

/-! ## 1. A symmetric class density and its walk -/

/-- **A symmetric class density**: continuous, nonnegative, of mass one, even, and a class function. -/
structure Dens (p : SU N → ℝ) : Prop where
  cont : Continuous p
  nonneg : ∀ g, 0 ≤ p g
  mass : ∫ g, p g ∂hm N = 1
  inv : ∀ g, p g⁻¹ = p g
  cyc : ∀ a b, p (a * b) = p (b * a)

/-- **One step of the walk**: `P f (x) = ∫ f(x z) p(z) dz`. No numeral. -/
noncomputable def Pop (p f : SU N → ℝ) (x : SU N) : ℝ := ∫ z, f (x * z) * p z ∂hm N

theorem cont_Pop {p f : SU N → ℝ} (hp : Continuous p) (hf : Continuous f) : Continuous (Pop p f) :=
  cont_int (F := fun x z => f (x * z) * p z)
    ((hf.comp (continuous_fst.mul continuous_snd)).mul (hp.comp continuous_snd))

/-- The squared displacement of `f` by `g`: `Φ(g) = ∫ (f(xg) − f(x))² dx`. DERIVED: `2` the square. -/
noncomputable def Phi (f : SU N → ℝ) (g : SU N) : ℝ := ∫ x, (f (x * g) - f x) ^ 2 ∂hm N

/-- The distance of the translate by `y` to the mean: `B(y) = ∫ (f(xy) − Pf(x))² dx`. DERIVED: `2` the square. -/
noncomputable def Bf (p f : SU N → ℝ) (y : SU N) : ℝ := ∫ x, (f (x * y) - Pop p f x) ^ 2 ∂hm N

/-- The energy `E = ∫ B(y) p(y) dy`. No numeral. -/
noncomputable def En (p f : SU N → ℝ) : ℝ := ∫ y, Bf p f y * p y ∂hm N

/-- The overlap of `p` with its translate by `g`. No numeral. -/
noncomputable def ovl (p : SU N → ℝ) (g : SU N) : ℝ := ∫ y, min (p y) (p (y * g)) ∂hm N

theorem Phi_nonneg (f : SU N → ℝ) (g : SU N) : 0 ≤ Phi f g := integral_nonneg fun _ => sq_nonneg _

theorem Bf_nonneg (p f : SU N → ℝ) (y : SU N) : 0 ≤ Bf p f y := integral_nonneg fun _ => sq_nonneg _

theorem cont_Bf {p f : SU N → ℝ} (hp : Continuous p) (hf : Continuous f) : Continuous (Bf p f) :=
  cont_int (F := fun y x => (f (x * y) - Pop p f x) ^ 2)
    (((hf.comp (continuous_snd.mul continuous_fst)).sub ((cont_Pop hp hf).comp continuous_snd)).pow 2)

theorem cont_Phi {f : SU N → ℝ} (hf : Continuous f) : Continuous (Phi f) :=
  cont_int (F := fun g x => (f (x * g) - f x) ^ 2)
    (((hf.comp (continuous_snd.mul continuous_fst)).sub (hf.comp continuous_snd)).pow 2)

/-- `∫ f(xy)² dx = ∫ f²`. DERIVED: `2` the square. -/
theorem sq_shift (f : SU N → ℝ) (y : SU N) : ∫ x, f (x * y) ^ 2 ∂hm N = ∫ x, f x ^ 2 ∂hm N :=
  integral_mul_right_eq_self (μ := hm N) (fun x => f x ^ 2) y

/-- **The energy is the loss of norm**: `E = ∫ f² − ∫ (Pf)²`. DERIVED: `2` the square. -/
theorem En_eq {p f : SU N → ℝ} (hp : Dens p) (hf : Continuous f) :
    En p f = ∫ x, f x ^ 2 ∂hm N - ∫ x, Pop p f x ^ 2 ∂hm N := by
  set h := Pop p f with hh
  have hhc : Continuous h := cont_Pop hp.cont hf
  have c1 : Continuous fun q : SU N × SU N => (f (q.2 * q.1) - h q.2) ^ 2 * p q.1 :=
    (((hf.comp (continuous_snd.mul continuous_fst)).sub (hhc.comp continuous_snd)).pow 2).mul
      (hp.cont.comp continuous_fst)
  have c2 : Continuous fun q : SU N × SU N => f (q.1 * q.2) ^ 2 * p q.2 :=
    ((hf.comp (continuous_fst.mul continuous_snd)).pow 2).mul (hp.cont.comp continuous_snd)
  have hin : ∀ x, ∫ y, (f (x * y) - h x) ^ 2 * p y ∂hm N
      = ∫ y, f (x * y) ^ 2 * p y ∂hm N - h x ^ 2 := by
    intro x
    have cx1 : Continuous fun y => f (x * y) ^ 2 * p y :=
      ((hf.comp (continuous_const.mul continuous_id)).pow 2).mul hp.cont
    have cx2 : Continuous fun y => f (x * y) * p y :=
      (hf.comp (continuous_const.mul continuous_id)).mul hp.cont
    have e : ∀ y, (f (x * y) - h x) ^ 2 * p y
        = f (x * y) ^ 2 * p y - 2 * h x * (f (x * y) * p y) + h x ^ 2 * p y := fun y => by ring
    simp_rw [e]
    rw [iadd (c_sub cx1 (c_cmul (2 * h x) cx2)) (c_cmul (h x ^ 2) hp.cont),
      isub cx1 (c_cmul (2 * h x) cx2), integral_const_mul, integral_const_mul, hp.mass]
    have : ∫ y, f (x * y) * p y ∂hm N = h x := rfl
    rw [this]
    ring
  have hE : En p f = ∫ x, ∫ y, (f (x * y) - h x) ^ 2 * p y ∂hm N ∂hm N := by
    unfold En Bf
    rw [swap_int (F := fun x y => (f (x * y) - h x) ^ 2 * p y)
      (by simpa using (show Continuous fun q : SU N × SU N => (f (q.1 * q.2) - h q.1) ^ 2 * p q.2 from
        (((hf.comp (continuous_fst.mul continuous_snd)).sub (hhc.comp continuous_fst)).pow 2).mul
          (hp.cont.comp continuous_snd)))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact (integral_mul_const _ _).symm
  have hA : ∫ x, ∫ y, f (x * y) ^ 2 * p y ∂hm N ∂hm N = ∫ x, f x ^ 2 ∂hm N := by
    rw [swap_int (F := fun x y => f (x * y) ^ 2 * p y) c2]
    have : ∀ y, ∫ x, f (x * y) ^ 2 * p y ∂hm N = (∫ x, f x ^ 2 ∂hm N) * p y := by
      intro y
      rw [integral_mul_const, sq_shift]
    simp_rw [this]
    rw [integral_const_mul, hp.mass, mul_one]
  rw [hE]
  simp_rw [hin]
  rw [isub (cont_int (F := fun x y => f (x * y) ^ 2 * p y) c2) (hhc.pow 2), hA]

/-- **`Φ` from any translate**: `Φ(g) ≤ 2 B(y) + 2 B(y g)`. DERIVED: `2` the parallelogram. -/
theorem Phi_le {p f : SU N → ℝ} (hp : Continuous p) (hf : Continuous f) (y g : SU N) :
    Phi f g ≤ 2 * Bf p f y + 2 * Bf p f (y * g) := by
  have hhc := cont_Pop hp hf
  have e : Phi f g = ∫ x, (f (x * (y * g)) - f (x * y)) ^ 2 ∂hm N := by
    unfold Phi
    rw [← integral_mul_right_eq_self (μ := hm N) (fun x => (f (x * g) - f x) ^ 2) y]
    simp only [mul_assoc]
  have c1 : ∀ u : SU N, Continuous fun x => (f (x * u) - Pop p f x) ^ 2 := fun u =>
    ((hf.comp (continuous_id.mul continuous_const)).sub hhc).pow 2
  have c2 : Continuous fun x => (f (x * (y * g)) - f (x * y)) ^ 2 :=
    ((hf.comp (continuous_id.mul continuous_const)).sub
      (hf.comp (continuous_id.mul continuous_const))).pow 2
  rw [e]
  unfold Bf
  rw [← integral_const_mul, ← integral_const_mul, ← iadd (c_cmul 2 (c1 y)) (c_cmul 2 (c1 (y * g)))]
  refine integral_mono (int_of_cont c2)
    (int_of_cont (c_add (c_cmul 2 (c1 y)) (c_cmul 2 (c1 (y * g))))) fun x => ?_
  simp only
  nlinarith [sq_nonneg (f (x * (y * g)) - Pop p f x + (f (x * y) - Pop p f x))]

/-- **The displacement is controlled by the energy over the overlap**: `Φ(g) · ovl(g) ≤ 4 E`. DERIVED: `4 = 2 + 2`
the two translates, each carrying `2 E`. -/
theorem Phi_mul_ovl {p f : SU N → ℝ} (hp : Dens p) (hf : Continuous f) (g : SU N) :
    Phi f g * ovl p g ≤ 4 * En p f := by
  have hB := cont_Bf hp.cont hf
  have hm0 : Continuous fun y => min (p y) (p (y * g)) :=
    hp.cont.min (hp.cont.comp (continuous_id.mul continuous_const))
  have hBp : Continuous fun y => Bf p f y * p y := hB.mul hp.cont
  have hBpg : Continuous fun y => Bf p f (y * g) * p (y * g) :=
    hBp.comp (continuous_id.mul continuous_const)
  have hshift : ∫ y, Bf p f (y * g) * p (y * g) ∂hm N = En p f :=
    integral_mul_right_eq_self (μ := hm N) (fun y => Bf p f y * p y) g
  have hmono : ∫ y, Phi f g * min (p y) (p (y * g)) ∂hm N
      ≤ ∫ y, (2 * (Bf p f y * p y) + 2 * (Bf p f (y * g) * p (y * g))) ∂hm N := by
    refine integral_mono (int_of_cont (c_cmul _ hm0))
      (int_of_cont (c_add (c_cmul 2 hBp) (c_cmul 2 hBpg))) fun y => ?_
    simp only
    have h0 := Phi_le hp.cont hf y g
    have hmn : 0 ≤ min (p y) (p (y * g)) := le_min (hp.nonneg _) (hp.nonneg _)
    have h1 := Bf_nonneg p f y
    have h2 := Bf_nonneg p f (y * g)
    have h3 : Bf p f y * min (p y) (p (y * g)) ≤ Bf p f y * p y :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) h1
    have h4 : Bf p f (y * g) * min (p y) (p (y * g)) ≤ Bf p f (y * g) * p (y * g) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) h2
    have h5 := mul_le_mul_of_nonneg_right h0 hmn
    nlinarith
  rw [integral_const_mul, iadd (c_cmul 2 hBp) (c_cmul 2 hBpg), integral_const_mul, integral_const_mul,
    hshift] at hmono
  unfold ovl En at *
  linarith

/-- Arithmetic of the overlap: `q² ≤ ab` gives `q ≤ (s min(a, b) + (a + b)/s)/2`. DERIVED: `2` the mean. -/
theorem le_min_mean {a b q s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hs : 0 < s) (h : q ^ 2 ≤ a * b) :
    q ≤ (s * min a b + (a + b) / s) / 2 := by
  have key : ∀ {m M : ℝ}, 0 ≤ m → m ≤ M → q ^ 2 ≤ m * M → q ≤ (s * m + M / s) / 2 := by
    intro m M hm hM hqq
    have ht1 : 0 ≤ s * m := by positivity
    have hM0 : 0 ≤ M := hm.trans hM
    have ht2 : 0 ≤ M / s := by positivity
    have hprod : s * m * (M / s) = m * M := by field_simp
    by_contra hcon
    push_neg at hcon
    nlinarith [sq_nonneg (s * m - M / s)]
  have hdiv : ∀ M : ℝ, M ≤ a + b → M / s ≤ (a + b) / s := fun M hM =>
    div_le_div_of_nonneg_right hM hs.le
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    have := key ha hab h
    have h2 := hdiv b (by linarith)
    linarith
  · rw [min_eq_right hab]
    have := key hb hab (by linarith [mul_comm a b])
    have h2 := hdiv a (by linarith)
    linarith

/-- **The overlap of `h²` from a pointwise Hellinger bound**: if `(c p(y))² ≤ p(y h⁻¹) p(y h)` for every `y`, then
`ovl(h h) ≥ c²/2`. DERIVED: `2` the mass of `p` and its translate; the weight `s = 2/c` optimizes the mean. -/
theorem ovl_ge {p : SU N → ℝ} (hp : Dens p) {c : ℝ} (hc : 0 < c) (h : SU N)
    (hH : ∀ y, (c * p y) ^ 2 ≤ p (y * h⁻¹) * p (y * h)) : c ^ 2 / 2 ≤ ovl p (h * h) := by
  have hshift : ovl p (h * h) = ∫ y, min (p (y * h⁻¹)) (p (y * h)) ∂hm N := by
    unfold ovl
    rw [← integral_mul_right_eq_self (μ := hm N) (fun y => min (p y) (p (y * (h * h)))) h⁻¹]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    have : y * h⁻¹ * (h * h) = y * h := by group
    rw [this]
  have hm1 : Continuous fun y => p (y * h⁻¹) := hp.cont.comp (continuous_id.mul continuous_const)
  have hm2 : Continuous fun y => p (y * h) := hp.cont.comp (continuous_id.mul continuous_const)
  have hmin : Continuous fun y => min (p (y * h⁻¹)) (p (y * h)) := hm1.min hm2
  set s : ℝ := 2 / c with hs
  have hspos : 0 < s := by positivity
  have hmass1 : ∫ y, p (y * h⁻¹) ∂hm N = 1 := by
    rw [integral_mul_right_eq_self (μ := hm N) p h⁻¹]; exact hp.mass
  have hmass2 : ∫ y, p (y * h) ∂hm N = 1 := by
    rw [integral_mul_right_eq_self (μ := hm N) p h]; exact hp.mass
  have hmono : ∫ y, c * p y ∂hm N
      ≤ ∫ y, (s / 2 * min (p (y * h⁻¹)) (p (y * h)) + (p (y * h⁻¹) + p (y * h)) * (1 / (2 * s))) ∂hm N := by
    refine integral_mono (int_of_cont (c_cmul _ hp.cont))
      (int_of_cont (c_add (c_cmul _ hmin) (c_mulc _ (c_add hm1 hm2)))) fun y => ?_
    simp only
    have := le_min_mean (hp.nonneg (y * h⁻¹)) (hp.nonneg (y * h))
      (mul_nonneg hc.le (hp.nonneg y)) hspos (hH y)
    calc c * p y ≤ _ := this
      _ = _ := by field_simp
  rw [integral_const_mul, hp.mass, iadd (c_cmul (s / 2) hmin) (c_mulc (1 / (2 * s)) (c_add hm1 hm2)),
    integral_const_mul, integral_mul_const, iadd hm1 hm2, hmass1, hmass2, ← hshift] at hmono
  have e1 : s / 2 = 1 / c := by rw [hs]; field_simp
  have e2 : (1 + 1) * (1 / (2 * s)) = c / 2 := by rw [hs]; field_simp; ring
  rw [e1, e2] at hmono
  have h3 : c / 2 ≤ 1 / c * ovl p (h * h) := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hc.le
  have e3 : c * (1 / c * ovl p (h * h)) = ovl p (h * h) := by field_simp
  rw [e3] at h4
  nlinarith

/-- **`Φ` is almost subadditive**: `Φ(xy) ≤ (1 + s) Φ(x) + (1 + 1/s) Φ(y)`. DERIVED: `1` the weights of
`(A + B)² ≤ (1 + 1/s) A² + (1 + s) B²`. -/
theorem Phi_mul {f : SU N → ℝ} (hf : Continuous f) (x y : SU N) {s : ℝ} (hs : 0 < s) :
    Phi f (x * y) ≤ (1 + s) * Phi f x + (1 + 1 / s) * Phi f y := by
  have e : Phi f y = ∫ z, (f (z * (x * y)) - f (z * x)) ^ 2 ∂hm N := by
    unfold Phi
    rw [← integral_mul_right_eq_self (μ := hm N) (fun z => (f (z * y) - f z) ^ 2) x]
    simp only [mul_assoc]
  have c1 : Continuous fun z => (f (z * (x * y)) - f (z * x)) ^ 2 :=
    ((hf.comp (continuous_id.mul continuous_const)).sub
      (hf.comp (continuous_id.mul continuous_const))).pow 2
  have c2 : Continuous fun z => (f (z * x) - f z) ^ 2 :=
    ((hf.comp (continuous_id.mul continuous_const)).sub hf).pow 2
  have c3 : Continuous fun z => (f (z * (x * y)) - f z) ^ 2 :=
    ((hf.comp (continuous_id.mul continuous_const)).sub hf).pow 2
  rw [e]
  unfold Phi
  rw [← integral_const_mul, ← integral_const_mul, ← iadd (c_cmul (1 + s) c2) (c_cmul (1 + 1 / s) c1)]
  refine integral_mono (int_of_cont c3)
    (int_of_cont (c_add (c_cmul (1 + s) c2) (c_cmul (1 + 1 / s) c1))) fun z => ?_
  simp only
  set A := f (z * (x * y)) - f (z * x)
  set B := f (z * x) - f z
  have e2 : f (z * (x * y)) - f z = A + B := by simp only [A, B]; ring
  rw [e2]
  have h1 : 0 ≤ (A / s - B * 1) ^ 2 * s := by positivity
  have e3 : (1 + s) * B ^ 2 + (1 + 1 / s) * A ^ 2 - (A + B) ^ 2 = (A / s - B * 1) ^ 2 * s := by
    field_simp
    ring
  linarith

/-- **`Φ` along a power**: `Φ(u^k) ≤ k² Φ(u)`. DERIVED: `2` the square; `1` the step. -/
theorem Phi_pow {f : SU N → ℝ} (hf : Continuous f) (u : SU N) (k : ℕ) :
    Phi f (u ^ k) ≤ (k : ℝ) ^ 2 * Phi f u := by
  induction k with
  | zero => simp [Phi]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := Phi_mul hf (u ^ k) u (s := 1 / k) (by positivity)
      rw [pow_succ]
      have hn := Phi_nonneg f u
      have h1 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ 1 + 1 / k)
      have e : (1 + 1 / (k : ℝ)) * ((k : ℝ) ^ 2 * Phi f u) + (1 + 1 / (1 / (k : ℝ))) * Phi f u
          = ((k + 1 : ℕ) : ℝ) ^ 2 * Phi f u := by
        push_cast
        field_simp
        ring
      linarith

/-- **The Haar mean of `Φ`**: `∫ Φ = 2 ∫ f²` when `∫ f = 0`. DERIVED: `2` the two squares. -/
theorem Phi_mean {f : SU N → ℝ} (hf : Continuous f) (h0 : ∫ x, f x ∂hm N = 0) :
    ∫ g, Phi f g ∂hm N = 2 * ∫ x, f x ^ 2 ∂hm N := by
  unfold Phi
  rw [swap_int (F := fun g x => (f (x * g) - f x) ^ 2)
    (((hf.comp (continuous_snd.mul continuous_fst)).sub (hf.comp continuous_snd)).pow 2)]
  have hin : ∀ x, ∫ g, (f (x * g) - f x) ^ 2 ∂hm N = ∫ z, f z ^ 2 ∂hm N + f x ^ 2 := by
    intro x
    have c1 : Continuous fun g => f (x * g) := hf.comp (continuous_const.mul continuous_id)
    have e : ∀ g, (f (x * g) - f x) ^ 2 = f (x * g) ^ 2 - 2 * f x * f (x * g) + f x ^ 2 :=
      fun g => by ring
    simp_rw [e]
    rw [iadd (c_sub (c1.pow 2) (c_cmul (2 * f x) c1)) continuous_const,
      isub (c1.pow 2) (c_cmul (2 * f x) c1),
      integral_const_mul, integral_mul_left_eq_self (μ := hm N) (fun z => f z ^ 2) x,
      integral_mul_left_eq_self (μ := hm N) f x, h0, const_prob]
    ring
  simp_rw [hin]
  rw [iadd continuous_const (hf.pow 2), const_prob]
  ring

/-! ## 2. The contraction -/

/-- **The walk contracts on mean-zero functions**: if every `x` is `(h h)^k` with `h` of Hellinger overlap `c`,
then `∫ (Pf)² ≤ (1 − c²/(4k²)) ∫ f²` for continuous mean-zero `f`. DERIVED: `4` from `8 k² E/c² ≥ 2 ∫ f²`. -/
theorem contraction {p : SU N → ℝ} (hp : Dens p) {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k)
    (hroot : ∀ x : SU N, ∃ h : SU N, x = (h * h) ^ k ∧ ∀ y, (c * p y) ^ 2 ≤ p (y * h⁻¹) * p (y * h))
    {f : SU N → ℝ} (hf : Continuous f) (h0 : ∫ x, f x ∂hm N = 0) :
    ∫ x, Pop p f x ^ 2 ∂hm N ≤ (1 - c ^ 2 / (4 * (k : ℝ) ^ 2)) * ∫ x, f x ^ 2 ∂hm N := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hbd : ∀ x, Phi f x ≤ (k : ℝ) ^ 2 * (8 * En p f / c ^ 2) := by
    intro x
    obtain ⟨h, rfl, hH⟩ := hroot x
    have h1 := Phi_mul_ovl hp hf (h * h)
    have h2 := ovl_ge hp hc h hH
    have hn := Phi_nonneg f (h * h)
    have h3 : Phi f (h * h) ≤ 8 * En p f / c ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h2 hn]
    exact (Phi_pow hf _ k).trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have hmean := Phi_mean hf h0
  have hle : ∫ g, Phi f g ∂hm N ≤ (k : ℝ) ^ 2 * (8 * En p f / c ^ 2) := by
    calc ∫ g, Phi f g ∂hm N ≤ ∫ _g : SU N, (k : ℝ) ^ 2 * (8 * En p f / c ^ 2) ∂hm N :=
          integral_mono (int_of_cont (cont_Phi hf)) (integrable_const _) hbd
      _ = _ := const_prob _
  rw [hmean] at hle
  have hEn := En_eq hp hf
  have e : (1 - c ^ 2 / (4 * (k : ℝ) ^ 2)) * ∫ x, f x ^ 2 ∂hm N
      = ∫ x, f x ^ 2 ∂hm N - c ^ 2 / (4 * (k : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂hm N := by ring
  rw [e]
  have h5 : c ^ 2 / (4 * (k : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂hm N ≤ En p f := by
    have h6 : c ^ 2 / (4 * (k : ℝ) ^ 2) * (2 * ∫ x, f x ^ 2 ∂hm N)
        ≤ c ^ 2 / (4 * (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 * (8 * En p f / c ^ 2)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have e7 : c ^ 2 / (4 * (k : ℝ) ^ 2) * ((k : ℝ) ^ 2 * (8 * En p f / c ^ 2)) = 2 * En p f := by
      field_simp
      ring
    rw [e7] at h6
    nlinarith
  linarith

/-! ## 3. The convolution powers -/

/-- **The convolution powers** `F₀ = p`, `F_{k+1} = P F_k`. No numeral. -/
noncomputable def Fk (p : SU N → ℝ) : ℕ → SU N → ℝ
  | 0 => p
  | k + 1 => Pop p (Fk p k)

theorem cont_Fk {p : SU N → ℝ} (hp : Continuous p) : ∀ k, Continuous (Fk p k)
  | 0 => hp
  | k + 1 => cont_Pop hp (cont_Fk hp k)

theorem Pop_sub_one {p f : SU N → ℝ} (hp : Dens p) (hf : Continuous f) (x : SU N) :
    Pop p (fun y => f y - 1) x = Pop p f x - 1 := by
  unfold Pop
  have c1 : Continuous fun z => f (x * z) * p z :=
    (hf.comp (continuous_const.mul continuous_id)).mul hp.cont
  have e : ∀ z, (f (x * z) - 1) * p z = f (x * z) * p z - p z := fun z => by ring
  simp_rw [e]
  rw [isub c1 hp.cont, hp.mass]

theorem mass_Pop {p f : SU N → ℝ} (hp : Dens p) (hf : Continuous f) :
    ∫ x, Pop p f x ∂hm N = ∫ x, f x ∂hm N := by
  unfold Pop
  rw [swap_int (F := fun x z => f (x * z) * p z)
    ((hf.comp (continuous_fst.mul continuous_snd)).mul (hp.cont.comp continuous_snd))]
  have : ∀ z, ∫ x, f (x * z) * p z ∂hm N = (∫ x, f x ∂hm N) * p z := by
    intro z
    rw [integral_mul_const, integral_mul_right_eq_self (μ := hm N) f z]
  simp_rw [this]
  rw [integral_const_mul, hp.mass, mul_one]

theorem mass_Fk {p : SU N → ℝ} (hp : Dens p) : ∀ k, ∫ x, Fk p k x ∂hm N = 1
  | 0 => hp.mass
  | k + 1 => (mass_Pop hp (cont_Fk hp.cont k)).trans (mass_Fk hp k)

/-- `∫ (F_k − 1)² ≤ r^{2k} ∫ (p − 1)²`, for `r²` a contraction of the walk on mean-zero functions. DERIVED: `1`
the mean of `F_k`; `2` the square. -/
theorem Fk_sq {p : SU N → ℝ} (hp : Dens p) {r : ℝ}
    (hr : ∀ f : SU N → ℝ, Continuous f → ∫ x, f x ∂hm N = 0 →
      ∫ x, Pop p f x ^ 2 ∂hm N ≤ r ^ 2 * ∫ x, f x ^ 2 ∂hm N) (k : ℕ) :
    ∫ x, (Fk p k x - 1) ^ 2 ∂hm N ≤ (r ^ 2) ^ k * ∫ x, (p x - 1) ^ 2 ∂hm N := by
  induction k with
  | zero => simp [Fk]
  | succ k ih =>
    have hc : Continuous fun y => Fk p k y - 1 := (cont_Fk hp.cont k).sub continuous_const
    have h0 : ∫ y, (Fk p k y - 1) ∂hm N = 0 := by
      rw [isub (cont_Fk hp.cont k) continuous_const, mass_Fk hp, const_prob]
      ring
    have h1 := hr _ hc h0
    have e : ∀ x, Pop p (fun y => Fk p k y - 1) x = Fk p (k + 1) x - 1 := fun x =>
      Pop_sub_one hp (cont_Fk hp.cont k) x
    simp_rw [e] at h1
    refine h1.trans ?_
    have e2 : (r ^ 2) ^ (k + 1) * ∫ x, (p x - 1) ^ 2 ∂hm N
        = r ^ 2 * ((r ^ 2) ^ k * ∫ x, (p x - 1) ^ 2 ∂hm N) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left ih (sq_nonneg r)

/-- **The sup bound on the powers**: `|F_{k+1}(x) − 1| ≤ r^k C`, with `∫ p² ≤ C`. Cauchy–Schwarz against `p`, in
the weighted form `u v ≤ (λ u² + v²/λ)/2`. DERIVED: `1` the mean; `2` the square and the mean of the weights. -/
theorem Fk_sup {p : SU N → ℝ} (hp : Dens p) {r C : ℝ} (hr0 : 0 < r)
    (hr : ∀ f : SU N → ℝ, Continuous f → ∫ x, f x ∂hm N = 0 →
      ∫ x, Pop p f x ^ 2 ∂hm N ≤ r ^ 2 * ∫ x, f x ^ 2 ∂hm N)
    (hC : ∫ x, p x ^ 2 ∂hm N ≤ C) (k : ℕ) (x : SU N) : |Fk p (k + 1) x - 1| ≤ r ^ k * C := by
  set u : SU N → ℝ := fun y => Fk p k y - 1 with hu
  have huc : Continuous u := (cont_Fk hp.cont k).sub continuous_const
  have e : Fk p (k + 1) x - 1 = ∫ z, u (x * z) * p z ∂hm N := Pop_sub_one hp (cont_Fk hp.cont k) x |>.symm
  have hmass2 : ∫ y, (p y - 1) ^ 2 ∂hm N ≤ C := by
    have e2 : ∀ y, (p y - 1) ^ 2 = p y ^ 2 - 2 * p y + 1 := fun y => by ring
    simp_rw [e2]
    rw [iadd (c_sub (hp.cont.pow 2) (c_cmul 2 hp.cont)) continuous_const,
      isub (hp.cont.pow 2) (c_cmul 2 hp.cont), integral_const_mul, hp.mass, const_prob]
    linarith
  have hsq : ∫ y, u y ^ 2 ∂hm N ≤ (r ^ 2) ^ k * C :=
    (Fk_sq hp hr k).trans (mul_le_mul_of_nonneg_left hmass2 (by positivity))
  have hshift : ∫ z, u (x * z) ^ 2 ∂hm N = ∫ y, u y ^ 2 ∂hm N :=
    integral_mul_left_eq_self (μ := hm N) (fun y => u y ^ 2) x
  have hrk : 0 < r ^ k := by positivity
  set l : ℝ := 1 / r ^ k with hl
  have hlpos : 0 < l := by positivity
  have c1 : Continuous fun z => u (x * z) := huc.comp (continuous_const.mul continuous_id)
  have hI1 : Integrable (fun z => u (x * z) * p z) (hm N) := int_of_cont (c1.mul hp.cont)
  have hbound : Integrable (fun z => l / 2 * u (x * z) ^ 2 + 1 / (2 * l) * p z ^ 2) (hm N) :=
    int_of_cont (c_add (c_cmul (l / 2) (c1.pow 2)) (c_cmul (1 / (2 * l)) (hp.cont.pow 2)))
  have hval : ∫ z, (l / 2 * u (x * z) ^ 2 + 1 / (2 * l) * p z ^ 2) ∂hm N ≤ r ^ k * C := by
    rw [iadd (c_cmul (l / 2) (c1.pow 2)) (c_cmul (1 / (2 * l)) (hp.cont.pow 2)), integral_const_mul,
      integral_const_mul, hshift]
    have h1 : l / 2 * ∫ y, u y ^ 2 ∂hm N ≤ l / 2 * ((r ^ 2) ^ k * C) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 1 / (2 * l) * ∫ z, p z ^ 2 ∂hm N ≤ 1 / (2 * l) * C :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    have e1 : l / 2 * ((r ^ 2) ^ k * C) = r ^ k * C / 2 := by
      rw [hl, ← pow_mul, mul_comm 2 k, pow_mul]
      field_simp
    have e2 : 1 / (2 * l) * C = r ^ k * C / 2 := by
      rw [hl]
      field_simp
    linarith
  have hpt : ∀ z, |u (x * z) * p z| ≤ l / 2 * u (x * z) ^ 2 + 1 / (2 * l) * p z ^ 2 := by
    intro z
    set a := u (x * z)
    set b := p z
    have h1 : 0 ≤ (l * |a| - |b|) ^ 2 / (2 * l) := by positivity
    have e3 : l / 2 * a ^ 2 + 1 / (2 * l) * b ^ 2 - |a * b| = (l * |a| - |b|) ^ 2 / (2 * l) := by
      rw [abs_mul]
      have ea : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      have eb : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      rw [ea, eb]
      field_simp
      ring
    linarith
  rw [e]
  calc |∫ z, u (x * z) * p z ∂hm N| ≤ ∫ z, |u (x * z) * p z| ∂hm N := abs_integral_le_integral_abs
    _ ≤ ∫ z, (l / 2 * u (x * z) ^ 2 + 1 / (2 * l) * p z ^ 2) ∂hm N :=
        integral_mono hI1.abs hbound hpt
    _ ≤ _ := hval

/-! ## 4. The parallelogram of the plaquette density -/

open scoped ComplexOrder in
/-- **The parallelogram of the density**: `φ(y h) + φ(y h⁻¹) ≤ 2 φ(y) + 2 φ(h)` on `SU(N)`, `N ≠ 0`, from
`tr(M M*) ≥ 0` at `M = (1 − h)(1 − y)`. There is no first-order term in `h`, which is what puts the walk at the
scale `1/β` and not `1/β²`. DERIVED: `2` the two translates; `4`, the coefficient in the expansion of the trace. -/
theorem wilson_par (hN : N ≠ 0) (y h : SU N) :
    wilsonDensity (y * h) + wilsonDensity (y * h⁻¹) ≤ 2 * wilsonDensity y + 2 * wilsonDensity h := by
  classical
  set Y : Matrix (Fin N) (Fin N) ℂ := (y : Matrix (Fin N) (Fin N) ℂ) with hY
  set H : Matrix (Fin N) (Fin N) ℂ := (h : Matrix (Fin N) (Fin N) ℂ) with hH
  have hYu : Y * star Y = 1 := Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 y.2).1
  have hHu : H * star H = 1 := Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 h.2).1
  have hHu' : star H * H = 1 := Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 h.2).1
  have c1 : ((y * h : SU N) : Matrix (Fin N) (Fin N) ℂ) = Y * H := rfl
  have c2 : ((y * h⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) = Y * star H := rfl
  set M : Matrix (Fin N) (Fin N) ℂ := (1 - H) * (1 - Y) with hM
  have hpos : 0 ≤ (Matrix.trace (M * M.conjTranspose)).re := by
    have := (Matrix.posSemidef_self_mul_conjTranspose M).trace_nonneg
    exact (Complex.le_def.1 this).1
  set Z : Matrix (Fin N) (Fin N) ℂ := 1 + 1 - Y - star Y with hZ
  have hMM : M * M.conjTranspose = (1 - H) * Z * (1 - star H) := by
    have e : M.conjTranspose = (1 - star Y) * (1 - star H) := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    have e2 : (1 - Y) * (1 - star Y) = Z := by
      rw [hZ, sub_mul, mul_sub, mul_sub, hYu]
      noncomm_ring
    rw [e, hM]
    calc (1 - H) * (1 - Y) * ((1 - star Y) * (1 - star H))
        = (1 - H) * ((1 - Y) * (1 - star Y)) * (1 - star H) := by noncomm_ring
      _ = _ := by rw [e2]
  have hexp : (1 - H) * Z * (1 - star H) = Z - H * Z - Z * star H + H * Z * star H := by noncomm_ring
  have ht1 : Matrix.trace (H * Z * star H) = Matrix.trace Z := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hHu', Matrix.one_mul]
  have hstar : ∀ A : Matrix (Fin N) (Fin N) ℂ, (Matrix.trace (star A)).re = (Matrix.trace A).re := by
    intro A
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
    simp
  have htrY : (Matrix.trace Z).re = 2 * (N : ℝ) - 2 * (Matrix.trace Y).re := by
    rw [hZ, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one]
    simp only [Complex.sub_re, Complex.add_re, hstar]
    simp
    ring
  have e3 : (Matrix.trace (H * star Y)).re = (Matrix.trace (Y * star H)).re := by
    have : H * star Y = star (Y * star H) := by rw [star_mul, star_star]
    rw [this, hstar]
  have e4 : (Matrix.trace (star Y * star H)).re = (Matrix.trace (Y * H)).re := by
    have : star Y * star H = star (H * Y) := by rw [star_mul]
    rw [this, hstar, Matrix.trace_mul_comm]
  have e5 : (Matrix.trace (H * Y)).re = (Matrix.trace (Y * H)).re := by rw [Matrix.trace_mul_comm]
  have htrHZ : (Matrix.trace (H * Z)).re
      = 2 * (Matrix.trace H).re - (Matrix.trace (Y * H)).re - (Matrix.trace (Y * star H)).re := by
    have : H * Z = H + H - H * Y - H * star Y := by rw [hZ]; noncomm_ring
    rw [this, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add]
    simp only [Complex.sub_re, Complex.add_re, e3, e5]
    ring
  have htrZH : (Matrix.trace (Z * star H)).re
      = 2 * (Matrix.trace H).re - (Matrix.trace (Y * star H)).re - (Matrix.trace (Y * H)).re := by
    have : Z * star H = star H + star H - Y * star H - star Y * star H := by rw [hZ]; noncomm_ring
    rw [this, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add]
    simp only [Complex.sub_re, Complex.add_re, e4, hstar]
    ring
  rw [hMM, hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, ht1] at hpos
  simp only [Complex.add_re, Complex.sub_re, htrHZ, htrZH, htrY] at hpos
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hkey : 2 * (Matrix.trace Y).re + 2 * (Matrix.trace H).re - (Matrix.trace (Y * H)).re
      - (Matrix.trace (Y * star H)).re ≤ 2 * (N : ℝ) := by linarith
  unfold wilsonDensity
  rw [c1, c2]
  have hdiv := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
  have e6 : 1 / (N : ℝ) * (2 * (N : ℝ)) = 2 := by field_simp
  rw [e6] at hdiv
  linarith

/-! ## 5. Roots in `SU(N)` -/

/-- **Every element of `SU(N)` is `(h h)^k` with `h` small**: `φ(h) ≤ π²(N + 4)/(8 k²)`. Diagonalise
(`CoverCompact.exists_diag`), take arguments, move the integer `2π m` of their sum onto one eigenvalue so that the
angles sum to `0`, and divide them by `2k`. DERIVED: `8 = 2 · 4`, `1 − cos u ≤ u²/2` at `u = θ/(2k)`; `N + 4` bounds
`((N − 1) + (N + 1)² + 1)/N`, the angles of size `π` and the one of size `(N + 1) π`. -/
theorem exists_root (hN : N ≠ 0) {k : ℕ} (hk : 1 ≤ k) (x : SU N) :
    ∃ h : SU N, x = (h * h) ^ k ∧ wilsonDensity h ≤ Real.pi ^ 2 * ((N : ℝ) + 4) / (8 * (k : ℝ) ^ 2) := by
  classical
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hxm := Matrix.mem_specialUnitaryGroup_iff.1 x.2
  obtain ⟨W, hWm, d, hx⟩ := CoverCompact.exists_diag hxm.1
  have hW1 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hWm
  have hW2 : W * star W = 1 := Matrix.mem_unitaryGroup_iff.1 hWm
  have hconj : ∀ A : Matrix (Fin N) (Fin N) ℂ, (W * A * star W).det = A.det := by
    intro A
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hW2, Matrix.det_one, one_mul]
  have hdprod : ∏ i, d i = 1 := by
    have := hxm.2
    rw [hx, hconj, Matrix.det_diagonal] at this
    exact this
  have hdu : ∀ i, star (d i) * d i = 1 := by
    intro i
    have hD : Matrix.diagonal d = star W * (x : Matrix (Fin N) (Fin N) ℂ) * W := by
      rw [hx]
      calc Matrix.diagonal d = (star W * W) * Matrix.diagonal d * (star W * W) := by
            rw [hW1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by noncomm_ring
    have hu : star (Matrix.diagonal d) * Matrix.diagonal d = 1 := by
      have hxu : star (x : Matrix (Fin N) (Fin N) ℂ) * (x : Matrix (Fin N) (Fin N) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.1 hxm.1
      have hhh : star (star W * (x : Matrix (Fin N) (Fin N) ℂ) * W)
          = star W * star (x : Matrix (Fin N) (Fin N) ℂ) * W := by
        rw [star_mul, star_mul, star_star, Matrix.mul_assoc]
      rw [hD, hhh]
      calc star W * star (x : Matrix (Fin N) (Fin N) ℂ) * W
            * (star W * (x : Matrix (Fin N) (Fin N) ℂ) * W)
          = star W * star (x : Matrix (Fin N) (Fin N) ℂ) * (W * star W)
            * (x : Matrix (Fin N) (Fin N) ℂ) * W := by noncomm_ring
        _ = star W * (star (x : Matrix (Fin N) (Fin N) ℂ) * (x : Matrix (Fin N) (Fin N) ℂ)) * W := by
            rw [hW2]; noncomm_ring
        _ = 1 := by rw [hxu, Matrix.mul_one, hW1]
    have := congrFun (congrFun hu i) i
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at this
    simpa using this
  have hnorm : ∀ i, ‖d i‖ = 1 := by
    intro i
    have h1 := hdu i
    have h2 : ((‖d i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1, Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    have h3 : ‖d i‖ ^ 2 = 1 := by exact_mod_cast h2
    nlinarith [norm_nonneg (d i), sq_nonneg (‖d i‖ - 1)]
  set θ : Fin N → ℝ := fun i => Complex.arg (d i) with hθ
  have hdexp : ∀ i, d i = Complex.exp ((θ i : ℂ) * Complex.I) := by
    intro i
    have := Complex.norm_mul_exp_arg_mul_I (d i)
    rw [hnorm i] at this
    simpa [hθ] using this.symm
  have hsum : Complex.exp (((∑ i, θ i : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← hdprod]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (hdexp i).symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hsum
  have hsumR : ∑ i, θ i = 2 * Real.pi * m := by
    have h1 : ((∑ i, θ i : ℝ) : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      apply mul_right_cancel₀ hI
      rw [hm]
      push_cast
      ring
    exact_mod_cast h1
  have hθb : ∀ i, |θ i| ≤ Real.pi := fun i => Complex.abs_arg_le_pi _
  have hmb : |2 * Real.pi * m| ≤ (N : ℝ) * Real.pi := by
    rw [← hsumR]
    calc |∑ i, θ i| ≤ ∑ i, |θ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, Real.pi := Finset.sum_le_sum fun i _ => hθb i
      _ = _ := by simp
  set j₀ : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩ with hj₀
  set a : Fin N → ℝ := fun i => θ i - (if i = j₀ then 2 * Real.pi * m else 0) with ha
  have hasum : ∑ i, a i = 0 := by
    simp only [ha]
    rw [Finset.sum_sub_distrib, hsumR, Finset.sum_ite_eq' Finset.univ j₀]
    simp
  have hasq : ∀ i, a i ^ 2 ≤ Real.pi ^ 2 + (if i = j₀ then (((N : ℝ) + 1) * Real.pi) ^ 2 else 0) := by
    intro i
    have hp := Real.pi_pos
    have hi := abs_le.1 (hθb i)
    by_cases h : i = j₀
    · simp only [ha, h, if_true]
      have hm2 := abs_le.1 hmb
      have hi0 := abs_le.1 (hθb j₀)
      have : (θ j₀ - 2 * Real.pi * m) ^ 2 ≤ (((N : ℝ) + 1) * Real.pi) ^ 2 := by
        apply sq_le_sq'
        · nlinarith
        · nlinarith
      nlinarith [sq_nonneg Real.pi]
    · simp only [ha, h, if_false, sub_zero, add_zero]
      exact sq_le_sq' (by linarith [hi.1]) hi.2
  have hasumsq : ∑ i, a i ^ 2 ≤ (N : ℝ) * (Real.pi ^ 2 * ((N : ℝ) + 4)) := by
    calc ∑ i, a i ^ 2 ≤ ∑ i, (Real.pi ^ 2 + (if i = j₀ then (((N : ℝ) + 1) * Real.pi) ^ 2 else 0)) :=
          Finset.sum_le_sum fun i _ => hasq i
      _ = (N : ℝ) * Real.pi ^ 2 + (((N : ℝ) + 1) * Real.pi) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j₀]
          simp
      _ ≤ _ := by
          have h1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero hN
          nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 h1), sq_nonneg Real.pi]
  set D : ℝ → Matrix (Fin N) (Fin N) ℂ :=
    fun t => Matrix.diagonal fun i => Complex.exp (((t * a i : ℝ) : ℂ) * Complex.I) with hDdef
  set V : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t => W * D t * star W with hV
  have hDmul : ∀ s t, D s * D t = D (s + t) := by
    intro s t
    simp only [hDdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hD0 : D 0 = 1 := by
    simp only [hDdef]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij]
  have hVmul : ∀ s t, V s * V t = V (s + t) := by
    intro s t
    simp only [hV]
    rw [← hDmul]
    calc W * D s * star W * (W * D t * star W) = W * D s * (star W * W) * D t * star W := by noncomm_ring
      _ = _ := by rw [hW1]; noncomm_ring
  have hV0 : V 0 = 1 := by simp only [hV]; rw [hD0, Matrix.mul_one, hW2]
  have hstarD : ∀ t, star (D t) = D (-t) := by
    intro t
    simp only [hDdef]
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  have hstarV : ∀ t, star (V t) = V (-t) := by
    intro t
    simp only [hV]
    rw [star_mul, star_mul, star_star, hstarD]
    noncomm_ring
  have hVmem : ∀ t, V t ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    intro t
    refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · rw [hstarV, hVmul, add_neg_cancel, hV0]
    · simp only [hV]
      rw [hconj]
      simp only [hDdef]
      rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul]
      have : ∑ i, ((t * a i : ℝ) : ℂ) = 0 := by
        rw [← Complex.ofReal_sum, ← Finset.mul_sum, hasum]
        simp
      rw [this, zero_mul, Complex.exp_zero]
  set s : ℝ := 1 / (2 * (k : ℝ)) with hs
  set h : SU N := ⟨V s, hVmem s⟩ with hh
  have hpow : ∀ n : ℕ, (((h * h) ^ n : SU N) : Matrix (Fin N) (Fin N) ℂ) = V (2 * s * n) := by
    intro n
    induction n with
    | zero => simp [hV0]
    | succ n ih =>
      rw [pow_succ]
      have e : (((h * h) ^ n * (h * h) : SU N) : Matrix (Fin N) (Fin N) ℂ)
          = (((h * h) ^ n : SU N) : Matrix (Fin N) (Fin N) ℂ) * (V s * V s) := rfl
      rw [e, ih, hVmul, hVmul]
      congr 1
      push_cast
      ring
  have hV1 : V 1 = (x : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hx]
    simp only [hV]
    congr 2
    simp only [hDdef]
    congr 1
    funext i
    rw [hdexp i]
    simp only [ha, one_mul]
    by_cases hi : i = j₀
    · simp only [hi, if_true]
      push_cast
      rw [sub_mul, Complex.exp_sub]
      have : Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
        rw [show 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I m
      rw [this, div_one]
    · simp [hi]
  refine ⟨h, ?_, ?_⟩
  · apply Subtype.ext
    rw [hpow k]
    have : 2 * s * (k : ℝ) = 1 := by rw [hs]; field_simp
    rw [this, hV1]
  · have htr : Matrix.trace (V s) = ∑ i, Complex.exp (((s * a i : ℝ) : ℂ) * Complex.I) := by
      simp only [hV]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW1, Matrix.one_mul]
      simp only [hDdef, Matrix.trace_diagonal]
    have hre : (Matrix.trace (V s)).re = ∑ i, Real.cos (s * a i) := by
      rw [htr, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => Complex.exp_ofReal_mul_I_re _
    have hcos : ∀ i, 1 - Real.cos (s * a i) ≤ (s * a i) ^ 2 / 2 := fun i => by
      linarith [Real.one_sub_sq_div_two_le_cos (x := s * a i)]
    have hsum1 : (N : ℝ) - ∑ i, Real.cos (s * a i) ≤ s ^ 2 / 2 * ∑ i, a i ^ 2 := by
      have e1 : (N : ℝ) = ∑ _i : Fin N, (1 : ℝ) := by simp
      rw [e1, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        have := hcos i
        calc 1 - Real.cos (s * a i) ≤ _ := this
          _ = _ := by ring
    have hw : wilsonDensity h = 1 - (1 / (N : ℝ)) * ∑ i, Real.cos (s * a i) := by
      unfold wilsonDensity
      rw [show ((h : SU N) : Matrix (Fin N) (Fin N) ℂ) = V s from rfl, hre]
    rw [hw]
    have hs2 : s ^ 2 = 1 / (4 * (k : ℝ) ^ 2) := by rw [hs]; field_simp; ring
    have h3 : s ^ 2 / 2 * ∑ i, a i ^ 2 ≤ s ^ 2 / 2 * ((N : ℝ) * (Real.pi ^ 2 * ((N : ℝ) + 4))) :=
      mul_le_mul_of_nonneg_left hasumsq (by positivity)
    have h4 := hsum1.trans h3
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
    have e7 : 1 / (N : ℝ) * ((N : ℝ) - ∑ i, Real.cos (s * a i))
        = 1 - 1 / (N : ℝ) * ∑ i, Real.cos (s * a i) := by
      field_simp
    have e8 : 1 / (N : ℝ) * (s ^ 2 / 2 * ((N : ℝ) * (Real.pi ^ 2 * ((N : ℝ) + 4))))
        = Real.pi ^ 2 * ((N : ℝ) + 4) / (8 * (k : ℝ) ^ 2) := by
      rw [hs2]
      field_simp
      ring
    rw [e7, e8] at h5
    exact h5

/-! ## 6. The plaquette walk -/

/-- **The plaquette density** `p = e^{−2β φ}/b` of one face of the 2D torus, normalized by
`b = TwoDVanish.bk N β`. No numeral. -/
noncomputable def pW (N : ℕ) (β : ℝ) (g : SU N) : ℝ := TwoDVanish.wt β g / TwoDVanish.bk N β

theorem wt_eq (β : ℝ) (g : SU N) : TwoDVanish.wt β g = Real.exp (-(2 * β * wilsonDensity g)) := by
  unfold TwoDVanish.wt
  rw [RectWilson.wilsonDensity_inv]
  congr 1
  ring

theorem continuous_wt (β : ℝ) : Continuous (TwoDVanish.wt (N := N) β) := by
  have e : TwoDVanish.wt (N := N) β = fun g => TwoDVanish.sw β g + TwoDVanish.fl β := by
    funext g
    unfold TwoDVanish.sw
    ring
  rw [e]
  exact (TwoDVanish.continuous_sw β).add continuous_const

theorem integral_wt (β : ℝ) : ∫ g, TwoDVanish.wt (N := N) β g ∂hm N = TwoDVanish.bk N β := by
  have e : ∀ g : SU N, TwoDVanish.wt β g = TwoDVanish.sw β g + TwoDVanish.fl β := fun g => by
    unfold TwoDVanish.sw
    ring
  simp_rw [e]
  rw [iadd (TwoDVanish.continuous_sw β) continuous_const, const_prob]
  rfl

theorem pW_dens (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : Dens (pW N β) where
  cont := (continuous_wt β).div_const _
  nonneg g := div_nonneg (Real.exp_pos _).le (TwoDVanish.bk_pos hN hβ).le
  mass := by
    unfold pW
    rw [integral_div, integral_wt]
    exact div_self (TwoDVanish.bk_pos hN hβ).ne'
  inv g := by
    unfold pW
    rw [wt_eq, wt_eq, RectWilson.wilsonDensity_inv]
  cyc a b := by
    unfold pW
    rw [wt_eq, wt_eq]
    have : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by group
    rw [this, WilsonAction.wilsonDensity_conj]

/-- **The Hellinger bound of a translate**: `(c p(y))² ≤ p(y h⁻¹) p(y h)` for `0 ≤ c ≤ e^{−2β φ(h)}`. DERIVED: `2`
as in `wt_eq`; the square of `c p(y)` reads `wilson_par`. -/
theorem pW_hellinger (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {c : ℝ} (hc0 : 0 ≤ c) (h y : SU N)
    (hc : c ≤ Real.exp (-(2 * β * wilsonDensity h))) :
    (c * pW N β y) ^ 2 ≤ pW N β (y * h⁻¹) * pW N β (y * h) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hpar := wilson_par hN y h
  have hc2 : c ^ 2 ≤ Real.exp (-(2 * β * wilsonDensity h)) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  unfold pW
  rw [wt_eq, wt_eq, wt_eq, mul_pow, div_pow, div_mul_div_comm, ← pow_two (TwoDVanish.bk N β),
    ← Real.exp_add, mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have hexp : Real.exp (-(2 * β * wilsonDensity h)) ^ 2 * Real.exp (-(2 * β * wilsonDensity y)) ^ 2
      ≤ Real.exp (-(2 * β * wilsonDensity (y * h⁻¹)) + -(2 * β * wilsonDensity (y * h))) := by
    rw [← mul_pow, ← Real.exp_add, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    nlinarith
  calc c ^ 2 * Real.exp (-(2 * β * wilsonDensity y)) ^ 2
      ≤ Real.exp (-(2 * β * wilsonDensity h)) ^ 2 * Real.exp (-(2 * β * wilsonDensity y)) ^ 2 :=
        mul_le_mul_of_nonneg_right hc2 (by positivity)
    _ ≤ _ := hexp

/-- **The spectral gap of the plaquette walk at the scale `1/β`**: if `k ≥ 1` and `β π² (N + 4)/4 ≤ k²`, then
`∫ (Pf)² ≤ (1 − e⁻²/(4k²)) ∫ f²` for continuous mean-zero `f`. So the gap is of order `1/(N β)`: the
`1/β` that `TwoDVanish`'s floor `e^{−4β}` does not see. DERIVED: `4`, `8` from `contraction` and `exists_root`; the
overlap constant `c = e⁻¹` is where `2 β φ(h) ≤ 1`. -/
theorem walk_contract (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {k : ℕ} (hk : 1 ≤ k)
    (hkβ : β * (Real.pi ^ 2 * ((N : ℝ) + 4)) / 4 ≤ (k : ℝ) ^ 2)
    {f : SU N → ℝ} (hf : Continuous f) (h0 : ∫ x, f x ∂hm N = 0) :
    ∫ x, Pop (pW N β) f x ^ 2 ∂hm N
      ≤ (1 - Real.exp (-2) / (4 * (k : ℝ) ^ 2)) * ∫ x, f x ^ 2 ∂hm N := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have e : Real.exp (-1) ^ 2 = Real.exp (-2) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h := contraction (pW_dens hN hβ) hc hk (fun x => by
    obtain ⟨h, hx, hφ⟩ := exists_root hN hk x
    refine ⟨h, hx, fun y => pW_hellinger hN hβ hc.le h y ?_⟩
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have h1 : 2 * β * wilsonDensity h ≤ 2 * β * (Real.pi ^ 2 * ((N : ℝ) + 4) / (8 * (k : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    have h2 : 2 * β * (Real.pi ^ 2 * ((N : ℝ) + 4) / (8 * (k : ℝ) ^ 2))
        = (β * (Real.pi ^ 2 * ((N : ℝ) + 4)) / 4) / (k : ℝ) ^ 2 := by
      field_simp
      ring
    have h3 : (β * (Real.pi ^ 2 * ((N : ℝ) + 4)) / 4) / (k : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hkβ
    linarith) hf h0
  rwa [e] at h

/-- **The gap area** `ℓ(N, β) = 240 + 150 (N + 4) β`. DERIVED: `240 = 30 · 8`, `150 = 30 · 2 · 10/4`, from
the bounds below on the walk of `walk_gap`. COMPUTED: `4 e² ≤ 30`, `π² ≤ 10`, `k² ≤ 8 + 2X` for
`k = ⌈√X⌉ + 1`, `X = β π² (N + 4)/4`. -/
noncomputable def gapArea (N : ℕ) (β : ℝ) : ℝ := 240 + 150 * ((N : ℝ) + 4) * β

/-- **The walk contracts at the gap area**: `∫ (Pf)² ≤ (1 − 1/ℓ) ∫ f²`. DERIVED: as in `gapArea`. -/
theorem walk_gap (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {f : SU N → ℝ} (hf : Continuous f)
    (h0 : ∫ x, f x ∂hm N = 0) :
    ∫ x, Pop (pW N β) f x ^ 2 ∂hm N ≤ (1 - 1 / gapArea N β) * ∫ x, f x ^ 2 ∂hm N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set X : ℝ := β * (Real.pi ^ 2 * ((N : ℝ) + 4)) / 4 with hX
  have hX0 : 0 ≤ X := by positivity
  set k : ℕ := ⌈Real.sqrt X⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs0 := Real.sqrt_nonneg X
  have hc1 : Real.sqrt X ≤ ⌈Real.sqrt X⌉₊ := Nat.le_ceil _
  have hc2 : (⌈Real.sqrt X⌉₊ : ℝ) < Real.sqrt X + 1 := Nat.ceil_lt_add_one hs0
  have hkR : (k : ℝ) = (⌈Real.sqrt X⌉₊ : ℝ) + 1 := by rw [hk]; push_cast; ring
  have hsq := Real.sq_sqrt hX0
  have hk2 : X ≤ (k : ℝ) ^ 2 := by
    rw [hkR]
    nlinarith
  have hk3 : (k : ℝ) ^ 2 ≤ 8 + 2 * X := by
    rw [hkR]
    nlinarith [sq_nonneg (Real.sqrt X - 2)]
  have hmain := walk_contract hN hβ hk1 hk2 hf h0
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => sq_nonneg _))
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  have he2 : (1 : ℝ) / 30 ≤ Real.exp (-2) / 4 := by
    have h1 : Real.exp 2 ≤ 7.5 := by
      have h2 := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [e]
      have h3 := Real.exp_pos 1
      nlinarith
    have h4 : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    rw [h4, div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hl : 30 * (k : ℝ) ^ 2 ≤ gapArea N β := by
    unfold gapArea
    have h1 : X ≤ β * (10 * ((N : ℝ) + 4)) / 4 := by
      rw [hX]
      have := mul_le_mul_of_nonneg_left hpi (by positivity : 0 ≤ β * ((N : ℝ) + 4))
      nlinarith
    nlinarith
  have hlpos : 0 < gapArea N β := lt_of_lt_of_le (by positivity) hl
  have hfin : 1 / gapArea N β ≤ Real.exp (-2) / (4 * (k : ℝ) ^ 2) := by
    calc 1 / gapArea N β ≤ 1 / (30 * (k : ℝ) ^ 2) := one_div_le_one_div_of_le (by positivity) hl
      _ = (1 / 30) / (k : ℝ) ^ 2 := by field_simp
      _ ≤ (Real.exp (-2) / 4) / (k : ℝ) ^ 2 := div_le_div_of_nonneg_right he2 (by positivity)
      _ = _ := by field_simp
  linarith

theorem gapArea_ge (β : ℝ) (hβ : 0 ≤ β) : (240 : ℝ) ≤ gapArea N β := by
  unfold gapArea
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2 : 0 ≤ 150 * ((N : ℝ) + 4) * β := by positivity
  linarith

/-- `∫ p² ≤ 1/b`: `p ≤ 1/b` against mass one. DERIVED: `1` the mass. -/
theorem pW_sq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ∫ x, pW N β x ^ 2 ∂hm N ≤ 1 / TwoDVanish.bk N β := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hd := pW_dens hN hβ
  have hle : ∀ x, pW N β x ^ 2 ≤ 1 / TwoDVanish.bk N β * pW N β x := by
    intro x
    have h0 := hd.nonneg x
    have h1 : pW N β x ≤ 1 / TwoDVanish.bk N β := by
      unfold pW
      refine div_le_div_of_nonneg_right ?_ hb.le
      rw [wt_eq, Real.exp_le_one_iff]
      have := WilsonAction.wilsonDensity_nonneg hN x
      have : 0 ≤ 2 * β * wilsonDensity x := by positivity
      linarith
    nlinarith
  calc ∫ x, pW N β x ^ 2 ∂hm N ≤ ∫ x, 1 / TwoDVanish.bk N β * pW N β x ∂hm N :=
        integral_mono (int_of_cont (hd.cont.pow 2)) (int_of_cont (c_cmul _ hd.cont)) hle
    _ = _ := by rw [integral_const_mul, hd.mass, mul_one]

/-- **The convolution powers of the plaquette walk equilibrate**: `|F_{m+1}(x) − 1| ≤ (1/b) e^{−m/(2ℓ)}`, uniformly
in `x`. DERIVED: `2` from `r = √(1 − 1/ℓ) ≤ e^{−1/(2ℓ)}`. -/
theorem Fk_equil (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (m : ℕ) (x : SU N) :
    |Fk (pW N β) (m + 1) x - 1| ≤ Real.exp (-((m : ℝ) / (2 * gapArea N β))) * (1 / TwoDVanish.bk N β) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hl := gapArea_ge (N := N) β hβ
  have hlpos : 0 < gapArea N β := by linarith
  have hg : 1 / gapArea N β ≤ 1 / 240 := one_div_le_one_div_of_le (by norm_num) hl
  have hg0 : 0 < 1 / gapArea N β := by positivity
  set r : ℝ := Real.sqrt (1 - 1 / gapArea N β) with hr
  have hr1 : r ^ 2 = 1 - 1 / gapArea N β := Real.sq_sqrt (by linarith)
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hrc : ∀ f : SU N → ℝ, Continuous f → ∫ y, f y ∂hm N = 0 →
      ∫ y, Pop (pW N β) f y ^ 2 ∂hm N ≤ r ^ 2 * ∫ y, f y ^ 2 ∂hm N := fun f hf h0 => by
    rw [hr1]
    exact walk_gap hN hβ hf h0
  have hs := Fk_sup (pW_dens hN hβ) hr0 hrc (pW_sq hN hβ) m x
  refine hs.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hre : r ≤ Real.exp (-(1 / (2 * gapArea N β))) := by
    have h1 : r ^ 2 ≤ Real.exp (-(1 / (2 * gapArea N β))) ^ 2 := by
      rw [hr1, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * -(1 / (2 * gapArea N β)) = -(1 / gapArea N β) := by
        push_cast
        field_simp
      rw [e]
      linarith [Real.add_one_le_exp (-(1 / gapArea N β))]
    exact (pow_le_pow_iff_left₀ hr0.le (Real.exp_pos _).le two_ne_zero).1 h1
  calc r ^ m ≤ Real.exp (-(1 / (2 * gapArea N β))) ^ m := pow_le_pow_left₀ hr0.le hre _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

/-! ## 7. A polynomial lower bound on the bulk -/

/-- **The density of a difference**: `2 N φ(x⁻¹ y) = ‖y − x‖²_F`, written through the trace. DERIVED: `2` the two
squares of norm `N`. -/
theorem density_diff (hN : N ≠ 0) (x y : SU N) :
    wilsonDensity (x⁻¹ * y) = (1 / (2 * (N : ℝ))) * ∑ i, ∑ j,
      Complex.normSq ((y : Matrix (Fin N) (Fin N) ℂ) i j - (x : Matrix (Fin N) (Fin N) ℂ) i j) := by
  classical
  set X : Matrix (Fin N) (Fin N) ℂ := (x : Matrix (Fin N) (Fin N) ℂ) with hX
  set Y : Matrix (Fin N) (Fin N) ℂ := (y : Matrix (Fin N) (Fin N) ℂ) with hY
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hXu : star X * X = 1 := Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 x.2).1
  have hYu : star Y * Y = 1 := Matrix.mem_unitaryGroup_iff'.1 (Matrix.mem_specialUnitaryGroup_iff.1 y.2).1
  have c1 : ((x⁻¹ * y : SU N) : Matrix (Fin N) (Fin N) ℂ) = star X * Y := rfl
  set D : Matrix (Fin N) (Fin N) ℂ := Y - X with hD
  have hsum : (Matrix.trace (star D * D)).re = ∑ i, ∑ j, Complex.normSq (D i j) := by
    have e : Matrix.trace (star D * D) = ∑ j, ∑ i, star (D i j) * D i j := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
    rw [e, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_re, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]
    ring
  have hstar : ∀ A : Matrix (Fin N) (Fin N) ℂ, (Matrix.trace (star A)).re = (Matrix.trace A).re := by
    intro A
    rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
    simp
  have hexp : star D * D = star Y * Y - star Y * X - star X * Y + star X * X := by
    rw [hD, star_sub]
    noncomm_ring
  have e2 : (Matrix.trace (star Y * X)).re = (Matrix.trace (star X * Y)).re := by
    have : star Y * X = star (star X * Y) := by rw [star_mul, star_star]
    rw [this, hstar]
  have htr : (Matrix.trace (star D * D)).re = 2 * (N : ℝ) - 2 * (Matrix.trace (star X * Y)).re := by
    rw [hexp, hXu, hYu, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one]
    simp only [Complex.add_re, Complex.sub_re, e2]
    simp
    ring
  show wilsonDensity (x⁻¹ * y) = 1 / (2 * (N : ℝ)) * ∑ i, ∑ j, Complex.normSq (D i j)
  rw [← hsum, htr]
  unfold wilsonDensity
  rw [c1]
  field_simp

/-- The number of bins of the grid. DERIVED: `2` the width of `[−1, 1]` and the real coordinates of an entry; `1`
the shift of `β` that keeps the mesh finite at `β = 0` and the bin past the ceiling. -/
noncomputable def binCount (N : ℕ) (β : ℝ) : ℕ :=
  ⌈2 * Real.sqrt (2 * (N : ℝ) * (β + 1))⌉₊ + 1

/-- **The bulk is polynomially small only**: `1 ≤ e · K^{2N²} · b`, with `K = binCount N β`. Bin the `2 N²` real
coordinates of a matrix at mesh `ε = 1/√(2N(β+1))`; two elements of one bin have `φ(x⁻¹ y) ≤ N ε²`, so
`e · wt(x⁻¹ y) ≥ 1`, and every `y` sits in the bin of its own coordinates. Integrate over `y`. No volume, no
measurability of the cells: only continuous integrands. DERIVED: `2 N²` the real coordinates; `1` the exponent of
`e`, from `2 β N ε² ≤ 1`. -/
theorem bk_ge (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    1 ≤ Real.exp 1 * (binCount N β : ℝ) ^ (N * (N * 2)) * TwoDVanish.bk N β := by
  classical
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  set R : ℝ := Real.sqrt (2 * (N : ℝ) * (β + 1)) with hR
  have hRpos : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hR2 : R ^ 2 = 2 * (N : ℝ) * (β + 1) := Real.sq_sqrt (by positivity)
  set K : ℕ := binCount N β with hK
  have hK1 : 2 * R < K := by
    rw [hK]
    unfold binCount
    push_cast
    linarith [Nat.le_ceil (2 * R), hR ▸ Nat.le_ceil (2 * Real.sqrt (2 * (N : ℝ) * (β + 1)))]
  let Idx : Type := Fin N × Fin N × Bool
  let coord : SU N → Idx → ℝ := fun x i =>
    if i.2.2 then ((x : Matrix (Fin N) (Fin N) ℂ) i.1 i.2.1).re
    else ((x : Matrix (Fin N) (Fin N) ℂ) i.1 i.2.1).im
  have hcoord : ∀ x i, |coord x i| ≤ 1 := by
    intro x i
    have hu : (x : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.1 x.2).1
    have h1 := MassGap.SUN.unitary_entry_norm_le_one N hu i.1 i.2.1
    simp only [coord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans h1
    · exact (Complex.abs_im_le_norm _).trans h1
  let bin : ℝ → ℕ := fun t => ⌊(t + 1) * R⌋₊
  have hbin : ∀ x i, bin (coord x i) < K := by
    intro x i
    have h1 := abs_le.1 (hcoord x i)
    have h2 : 0 ≤ (coord x i + 1) * R := mul_nonneg (by linarith) hRpos.le
    have h3 : (bin (coord x i) : ℝ) ≤ (coord x i + 1) * R := Nat.floor_le h2
    have h4 : (bin (coord x i) : ℝ) < K := by nlinarith
    exact_mod_cast h4
  let cell : SU N → Idx → Fin K := fun x i => ⟨bin (coord x i), hbin x i⟩
  have hclose : ∀ x y : SU N, cell x = cell y → 2 * β * wilsonDensity (x⁻¹ * y) ≤ 1 := by
    intro x y hxy
    have hsame : ∀ i, |coord y i - coord x i| ≤ 1 / R := by
      intro i
      have h0 : bin (coord x i) = bin (coord y i) := congrArg Fin.val (congrFun hxy i)
      have hx1 := abs_le.1 (hcoord x i)
      have hy1 := abs_le.1 (hcoord y i)
      have hxs : 0 ≤ (coord x i + 1) * R := mul_nonneg (by linarith) hRpos.le
      have hys : 0 ≤ (coord y i + 1) * R := mul_nonneg (by linarith) hRpos.le
      have a1 := Nat.floor_le hxs
      have a2 := Nat.lt_floor_add_one ((coord x i + 1) * R)
      have b1 := Nat.floor_le hys
      have b2 := Nat.lt_floor_add_one ((coord y i + 1) * R)
      have h0' : ((⌊(coord x i + 1) * R⌋₊ : ℕ) : ℝ) = ((⌊(coord y i + 1) * R⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast h0
      have hd : |(coord y i - coord x i) * R| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      rw [le_div_iff₀ hRpos]
      rwa [abs_mul, abs_of_pos hRpos] at hd
    have hentry : ∀ a b, Complex.normSq ((y : Matrix (Fin N) (Fin N) ℂ) a b
        - (x : Matrix (Fin N) (Fin N) ℂ) a b) ≤ 2 / R ^ 2 := by
      intro a b
      have h1 := hsame (a, b, true)
      have h2 := hsame (a, b, false)
      simp only [coord, if_true, Bool.false_eq_true, if_false] at h1 h2
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      have h3 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
      have h4 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
      have e : (1 / R) ^ 2 = 1 / R ^ 2 := by rw [div_pow, one_pow]
      rw [e] at h3 h4
      have e2 : 2 / R ^ 2 = 1 / R ^ 2 + 1 / R ^ 2 := by ring
      rw [e2]
      nlinarith
    have hsum : ∑ a, ∑ b, Complex.normSq ((y : Matrix (Fin N) (Fin N) ℂ) a b
        - (x : Matrix (Fin N) (Fin N) ℂ) a b) ≤ (N : ℝ) * ((N : ℝ) * (2 / R ^ 2)) := by
      calc _ ≤ ∑ _a : Fin N, ∑ _b : Fin N, 2 / R ^ 2 :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
        _ = _ := by simp
    rw [density_diff hN]
    have hφ : (1 / (2 * (N : ℝ))) * ∑ a, ∑ b, Complex.normSq ((y : Matrix (Fin N) (Fin N) ℂ) a b
        - (x : Matrix (Fin N) (Fin N) ℂ) a b) ≤ 1 / (2 * (β + 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)))
      refine h1.trans (le_of_eq ?_)
      rw [hR2]
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hφ (by positivity : (0 : ℝ) ≤ 2 * β)
    refine h2.trans ?_
    rw [show 2 * β * (1 / (2 * (β + 1))) = β / (β + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  let rep : (Idx → Fin K) → SU N := fun τ => if h : ∃ x, cell x = τ then h.choose else 1
  have hrep : ∀ y, cell (rep (cell y)) = cell y := by
    intro y
    have h : ∃ x, cell x = cell y := ⟨y, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  have hpt : ∀ y : SU N, (1 : ℝ) ≤ Real.exp 1 * ∑ τ : Idx → Fin K, TwoDVanish.wt β ((rep τ)⁻¹ * y) := by
    intro y
    have h1 := hclose _ _ (hrep y)
    have h2 : Real.exp (-1) ≤ TwoDVanish.wt β ((rep (cell y))⁻¹ * y) := by
      rw [wt_eq, Real.exp_le_exp]
      linarith
    have h3 : TwoDVanish.wt β ((rep (cell y))⁻¹ * y) ≤ ∑ τ : Idx → Fin K, TwoDVanish.wt β ((rep τ)⁻¹ * y) :=
      Finset.single_le_sum (f := fun τ => TwoDVanish.wt β ((rep τ)⁻¹ * y))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ (cell y))
    have h4 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := h4.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2.trans h3) (Real.exp_pos _).le
  have hc : ∀ τ : Idx → Fin K, Continuous fun y : SU N => TwoDVanish.wt β ((rep τ)⁻¹ * y) := fun τ =>
    (continuous_wt β).comp (continuous_const.mul continuous_id)
  have hcs : Continuous fun y : SU N => Real.exp 1 * ∑ τ : Idx → Fin K, TwoDVanish.wt β ((rep τ)⁻¹ * y) :=
    c_cmul _ (continuous_finsetSum _ fun τ _ => hc τ)
  have hint := integral_mono (μ := hm N) (integrable_const (1 : ℝ)) (int_of_cont hcs) hpt
  rw [const_prob, integral_const_mul, integral_finsetSum _ fun τ _ => int_of_cont (hc τ)] at hint
  have hτ : ∀ τ : Idx → Fin K, ∫ y, TwoDVanish.wt β ((rep τ)⁻¹ * y) ∂hm N = TwoDVanish.bk N β := fun τ => by
    rw [integral_mul_left_eq_self (μ := hm N) (TwoDVanish.wt β) (rep τ)⁻¹]
    exact integral_wt β
  simp_rw [hτ] at hint
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hint
  have hcard : Fintype.card (Idx → Fin K) = K ^ (N * (N * 2)) := by
    simp [Idx, Fintype.card_prod]
  rw [hcard] at hint
  push_cast at hint
  calc (1 : ℝ) ≤ _ := hint
    _ = _ := by ring

end MassGap.StripGap

#print axioms MassGap.StripGap.En_eq
#print axioms MassGap.StripGap.Phi_mul_ovl
#print axioms MassGap.StripGap.ovl_ge
#print axioms MassGap.StripGap.Phi_pow
#print axioms MassGap.StripGap.Phi_mean
#print axioms MassGap.StripGap.contraction
#print axioms MassGap.StripGap.Fk_sup
#print axioms MassGap.StripGap.wilson_par
#print axioms MassGap.StripGap.exists_root
#print axioms MassGap.StripGap.pW_dens
#print axioms MassGap.StripGap.pW_hellinger
#print axioms MassGap.StripGap.walk_contract
#print axioms MassGap.StripGap.walk_gap
#print axioms MassGap.StripGap.Fk_equil
#print axioms MassGap.StripGap.density_diff
#print axioms MassGap.StripGap.bk_ge
