import Mathlib
import MassGap.FreqRead
import MassGap.StrongAnchor

/-!
# MassGap.WindowFreq — the doubling defect of a free periodic chain is a frequency read, in closed form

`CouplingTower.windowCoupling N β w` is the doubling defect `16 log Z(n⁴) − log Z((2n)⁴)` of the periodic
Wilson torus of side `n = 2^w`: a free-energy (Casimir, finite-size) read of the spectrum at aperture `2^w`.
`FreqRead` reads the same box through its frequencies. This module computes the doubling defect of the free
one-dimensional Gaussian chain, `2 log Z(L) − log Z(2L)`, in closed form and shows it is a frequency read. That
defect is not the tree's Wilson read: it has one dimension, two copies, and a scalar field, where
`windowCoupling` has four dimensions, `16` copies and the `SU(N)` torus. Nothing in this module proves a
statement about `windowCoupling`. The results are mapped against `StrongEndVanishing.windowGap_of_vanishing`
and `StrongAnchor.NoStall`.

The free energy `log Z = (L/2) log 2π − logDet/2` is taken as the definition of the Gaussian determinant formula
`∫ e^{−φ·Kφ/2} dφ = (2π)^{L/2} det K^{−1/2}`; it is not derived from an integral here. Proved: the product over
the `L`-th roots of unity (`X_pow_sub_C_eq_prod`, `prod_one_sub_pow_eq_order`) and the closed forms that follow,
including the finite-size (Casimir / Lüscher) form of a massive free energy. Declarations are in
`MassGap.WindowFreq`.

## 1. The Casimir law (proved)

`casimirLaw x = log((1 + e^{−x})/(1 − e^{−x})) = log coth(x/2)`, at `x = L θ` (aperture times rate).

* `le_casimirLaw`, `casimirLaw_le` (the Lüscher form): `2e^{−x}/(1+e^{−x}) ≤ casimirLaw x ≤ 2e^{−x}/(1−e^{−x})`.
* `casimirLaw_anti`: non-increasing in `x > 0`.
* `tendsto_casimirLaw_atTop`: `→ 0` as `x → ∞`; `lt_casimirLaw`, `tendsto_casimirLaw_zero`: `→ ∞` as `x → 0⁺`.
* `tendsto_rate_read`: `−log(casimirLaw (L θ)) / L → θ`. The decay rate of the read along the aperture is `θ`:
  the read is a frequency read, measured from the read itself.

## 2. The free box (proved)

The periodic chain of `L` sites, spacing `1`, mass `m`: modes `ω²_j = m² + 4 sin²(π j/L)` (`FreqRead.omega2 m 1`).
`rate m = 2 arsinh(m/2)` is the lattice decay rate, the pole of the free propagator: `2 sinh(rate m / 2) = m`
(`two_sinh_half_rate`), `2 cosh(rate m) − 2 = m²` (`two_cosh_rate`), `rate m > 0 ↔ m > 0` (`rate_pos_iff`).

* `omega2_eq`: `ω²_j = 2 cosh θ − 2 cos(2π j/L)` at `m = 2 sinh(θ/2)`.
* `prod_cosh_sub_cos`: `∏_{j<L} (2 cosh θ − 2 cos(2π j/L)) = 2 cosh(L θ) − 2` (roots of unity).
* `prod_massless`: `∏_{1≤j<L} (2 − 2 cos(2π j/L)) = L²` (the zero-mode-removed massless product).
* `logDet m L`: the sum of `log ω²_j` over the modes with `ω²_j ≠ 0` (at `m = 0` this is `det′`, the zero mode
  removed, the standard massless regularisation). `logZ m L = (L/2) log 2π − logDet m L / 2`;
  `defect m L = 2 logZ m L − logZ m (2L)` (the one-dimensional doubling defect: `2 = 2¹` copies);
  `freeWindow m w = defect m (2^w)`, the free analogue of `windowCoupling`.
* `logDet_massive`: `logDet m L = L θ + 2 log(1 − e^{−Lθ})`, `θ = rate m`: a bulk term linear in the volume and
  an exponentially small finite-size term.
* `defect_massive`: `defect m L = casimirLaw (L · rate m)` (closed form).
* `logDet_massless`, `defect_massless`: `logDet 0 L = 2 log L`, `defect 0 L = log 2 − log L`.

## 3. Vanishing read ⇔ mass (proved)

* `defect_vanishes_iff`, `freeWindow_vanishes_iff`: for `m ≥ 0`, the free doubling defect tends to `0` (along all
  `L`, or along the windows `2^w`) exactly when `m > 0`. Load tests: massive passes, `defect 0 L → −∞`
  (`tendsto_defect_massless`) fails, and both reads are actual numbers (`defect_massive`, `defect_massless`).
  The massless free energy uses `det′` (the zero mode removed): it is a regularised free energy, not a
  convergent Gaussian integral.
* `defect_le`, `le_defect`: `2q/(1+q) ≤ defect m L ≤ 2q/(1−q)`, `q = e^{−L·rate m}` (Lüscher's `O(e^{−L·rate m})`).
* `tendsto_rate_of_defect`: `−log(defect m L)/L → rate m`. The free window coupling reads the mass.
* `uniform_iff_rate_bounded_below` (the free stall): over any set `S` of rates `θ > 0`, the settling of
  `casimirLaw (L θ)` is uniform in `θ ∈ S` exactly when `S` is bounded away from `0`. A loss of uniformity (the
  shape of a stall at `b`, `StrongAnchor.vanishes_of_uniformBelow`) is, at the free field, exactly the rate
  closing.

## 4. The converse direction, as a template, and what it does to NoStall (proved under the template)

`StrongEndVanishing.windowGap_of_vanishing` gives vanishing ⇒ periodic gap. The converse at the free field is
§3. In general it is the finite-size template:

* `GapGivesVanishing N hN` (template, not proved): at every `β ≥ 0`, a periodic Clay gap at some rate in `(0, 1)`
  gives the vanishing read. This is the statement that a massive (gapped) phase has finite-size corrections to
  the free energy that are exponentially small in the side (Lüscher's finite-volume formula; Borgs–Kotecký,
  proved where a convergent cluster/contour expansion holds). It is not proved for the Wilson torus at every
  `β`, and a transfer gap alone is not the hypothesis of either theorem: both also use a convergent expansion
  or a unique-vacuum cluster property uniform in the box.
* `gapAt_of_vanishes`, `gapAt_of_noStall` (proved, no template): `NoStall N` gives the periodic gap at every
  `β ≥ 0`.
* `vanishes_iff_gapAt`, `noStall_iff_gapAt`, `strongEnd_iff_frequently_gapAt` (proved under the template): the
  vanishing read at `β` is the gap at `β`; `NoStall N` is the gap at every `β ≥ 0`; `StrongEnd N` is the gap
  frequently at `∞`.

Plainly: nothing here reduces `NoStall N` or `StrongEnd N`. Under the template, `NoStall N` becomes "the periodic
gap persists at every coupling", which is the lattice gap itself at every `β`, so the template moves the input
from a free-energy read to a spectral read of the same strength; it removes nothing, and the template is itself
open for the Wilson torus. At large `β` the perturbative torus is massless-like and centre-symmetry sectors can
add `O(1)` terms to the doubling defect, so the template is not expected to be easy there. What is proved is the free-field identification: the free one-dimensional doubling
defect is a frequency read (its decay rate along the aperture is `rate m`, `tendsto_rate_of_defect`), it
vanishes exactly when the mass is positive, and its settling is uniform exactly when the rate stays away from
`0`. That is the free one-dimensional form of "a stall is the gap closing", and of `FreqRead.cross_strictMonoOn` read through the free energy. No capstone is
built: no input is weakened or removed.

## 5. The d-dimensional extension (stated, template)

`defectD m d L = 2^d logZD m d L − logZD m d (2L)` on the periodic box `L^d`, modes `k : Fin d → Fin L`,
`ω²_k = m² + Σ_μ 4 sin²(π k_μ/L)`. `FreeCasimirD d`: for every `m > 0`, `defectD m d L → 0`;
`FreeMasslessFailsD d`: `defectD 0 d L` does not tend to `0`. At `d = 4` they are the free scalar
counterparts of the `16 log ZR(n⁴) − log ZR((2n)⁴)` shape of `windowCoupling`; the gauge field and the Wilson
action are not in them. They are stated, not proved. The two statements are templates here: the massive case is the exponential convergence of the transverse Riemann
sums of an analytic periodic integrand (Poisson summation: corrections `O(L^{d−1} e^{−θL})`), and the massless
case is the `det′` asymptotics `log det′ = L^d f + 2 log L + c_d + o(1)` (Chinta–Jorgenson–Karlsson, cited, not checked here), which give
`defectD 0 d L = −(2^d − 1) log L + O(1) → −∞`. The one-dimensional case is §2–§3, proved exactly.

DERIVED (module-wide): `0` the limit of the read, the zero mode and the signs; `1` the lattice spacing (cell
units), the least box and the unit of `1 ± e^{−x}`; `2` the doubling, the copies `2 = 2¹` in one dimension, the
square, the Laplacian `4 sin²(p/2) = (2 sin(p/2))²`, the half-angle `θ/2` and the factor `1/2` of the Gaussian
determinant; `2π` the Gaussian normalisation and the full turn of the roots of unity; `2^d` the copies in `d`
dimensions; `16 = 2⁴` and `4` the copies and the dimension of the Wilson torus the shape is compared with
(comparison only, not used in any proof); `π` the half turn of `sin(π j/L)`, half of the full turn `2π`.
Proof-internal: `1` the level in `uniform_iff_rate_bounded_below` (any positive level works).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.WindowFreq

open Real Filter Topology Finset

/-! ## 1. The Casimir law -/

/-- **The Casimir law** at `x = L θ`: `log((1 + e^{−x})/(1 − e^{−x})) = log coth(x/2)`.
DERIVED: `1` the unit of `1 ± e^{−x}`. -/
def casimirLaw (x : ℝ) : ℝ := Real.log ((1 + Real.exp (-x)) / (1 - Real.exp (-x)))

/-- DERIVED: `0` the sign; `1` the unit. -/
theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  have h := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
  rwa [Real.exp_zero] at h

/-- **The Lüscher upper bound**: `casimirLaw x ≤ 2e^{−x}/(1 − e^{−x})`. DERIVED: `2` the two terms of
`log(1+q) − log(1−q)`; `0` the sign. -/
theorem casimirLaw_le {x : ℝ} (hx : 0 < x) :
    casimirLaw x ≤ 2 * Real.exp (-x) / (1 - Real.exp (-x)) := by
  have hq := Real.exp_pos (-x)
  have hq1 := exp_neg_lt_one hx
  have h1 : 0 < 1 - Real.exp (-x) := by linarith
  unfold casimirLaw
  refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) h1)).trans (le_of_eq ?_)
  field_simp
  ring

/-- **The Lüscher lower bound**: `2e^{−x}/(1 + e^{−x}) ≤ casimirLaw x`. DERIVED: `2` the two terms; `0` the
sign. -/
theorem le_casimirLaw {x : ℝ} (hx : 0 < x) :
    2 * Real.exp (-x) / (1 + Real.exp (-x)) ≤ casimirLaw x := by
  have hq := Real.exp_pos (-x)
  have hq1 := exp_neg_lt_one hx
  have h1 : 0 < 1 - Real.exp (-x) := by linarith
  have h2 : 0 < 1 + Real.exp (-x) := by linarith
  have hy : 0 < (1 + Real.exp (-x)) / (1 - Real.exp (-x)) := div_pos h2 h1
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h
  have e : ((1 + Real.exp (-x)) / (1 - Real.exp (-x)))⁻¹ - 1
      = -(2 * Real.exp (-x) / (1 + Real.exp (-x))) := by
    field_simp
    ring
  rw [e] at h
  unfold casimirLaw
  linarith

/-- **The read is positive** for `x > 0`. DERIVED: `0` the sign. -/
theorem casimirLaw_pos {x : ℝ} (hx : 0 < x) : 0 < casimirLaw x := by
  have hq := Real.exp_pos (-x)
  exact lt_of_lt_of_le (by positivity) (le_casimirLaw hx)

/-- **The read is non-increasing** in `x > 0`. DERIVED: `0` the sign. -/
theorem casimirLaw_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : casimirLaw y ≤ casimirLaw x := by
  have hqx := Real.exp_pos (-x)
  have hqy := Real.exp_pos (-y)
  have hq1 := exp_neg_lt_one hx
  have hle : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hy1 : 0 < 1 - Real.exp (-y) := by linarith
  have hx1 : 0 < 1 - Real.exp (-x) := by linarith
  unfold casimirLaw
  apply Real.log_le_log (div_pos (by linarith) hy1)
  rw [div_le_div_iff₀ hy1 hx1]
  nlinarith

/-- **The read settles** as the aperture opens: `casimirLaw x → 0` as `x → ∞`. DERIVED: `0` the limit; `1`
the unit. -/
theorem tendsto_casimirLaw_atTop : Tendsto casimirLaw atTop (𝓝 0) := by
  have hq : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h := ((hq.const_add 1).div ((tendsto_const_nhds (x := (1 : ℝ))).sub hq) (by norm_num)).log (by norm_num)
  have e : Real.log ((1 + 0) / (1 - 0)) = 0 := by norm_num
  rw [e] at h
  exact h

/-- **The read below the aperture scale**: for `0 < x < e^{−B}`, `B < casimirLaw x`. DERIVED: `0` the sign;
`1` the unit. -/
theorem lt_casimirLaw {x B : ℝ} (hx0 : 0 < x) (hxB : x < Real.exp (-B)) : B < casimirLaw x := by
  have hq := Real.exp_pos (-x)
  have hq1 := exp_neg_lt_one hx0
  have h1 : 0 < 1 - Real.exp (-x) := by linarith
  have hlow : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have hlog : Real.log x < -B := (Real.log_lt_iff_lt_exp hx0).2 hxB
  have hmono : 1 / x ≤ (1 + Real.exp (-x)) / (1 - Real.exp (-x)) :=
    calc 1 / x ≤ 1 / (1 - Real.exp (-x)) := one_div_le_one_div_of_le h1 hlow
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) h1.le
  have h := Real.log_le_log (by positivity) hmono
  rw [one_div, Real.log_inv] at h
  unfold casimirLaw
  linarith

/-- **The read diverges as the rate closes**: `casimirLaw x → ∞` as `x → 0⁺`. DERIVED: `0` the limit. -/
theorem tendsto_casimirLaw_zero : Tendsto casimirLaw (𝓝[>] 0) atTop := by
  refine tendsto_atTop.2 fun B => ?_
  filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-B))] with x hx
  exact (lt_casimirLaw hx.1 hx.2).le

/-- **The rate read**: `−log(casimirLaw x) − x` lies between `log(1 − e^{−x}) − log 2` and
`log(1 + e^{−x}) − log 2`. DERIVED: `2` the leading coefficient `2e^{−x}`. -/
theorem neg_log_casimirLaw_bounds {x : ℝ} (hx : 0 < x) :
    x + Real.log (1 - Real.exp (-x)) - Real.log 2 ≤ -Real.log (casimirLaw x) ∧
      -Real.log (casimirLaw x) ≤ x + Real.log (1 + Real.exp (-x)) - Real.log 2 := by
  have hq := Real.exp_pos (-x)
  have hq1 := exp_neg_lt_one hx
  have h1 : 0 < 1 - Real.exp (-x) := by linarith
  have h2 : 0 < 1 + Real.exp (-x) := by linarith
  have hD := casimirLaw_pos hx
  have e1 : Real.log (2 * Real.exp (-x) / (1 - Real.exp (-x)))
      = Real.log 2 - x - Real.log (1 - Real.exp (-x)) := by
    rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by norm_num) hq.ne', Real.log_exp]
    ring
  have e2 : Real.log (2 * Real.exp (-x) / (1 + Real.exp (-x)))
      = Real.log 2 - x - Real.log (1 + Real.exp (-x)) := by
    rw [Real.log_div (by positivity) h2.ne', Real.log_mul (by norm_num) hq.ne', Real.log_exp]
    ring
  have hu := Real.log_le_log hD (casimirLaw_le hx)
  have hl := Real.log_le_log (by positivity) (le_casimirLaw hx)
  rw [e1] at hu
  rw [e2] at hl
  constructor <;> linarith

/-- **The read is a frequency read**: along the aperture `L`, `−log(casimirLaw (L θ)) / L → θ`. The rate is the
read's own decay rate, not chosen. DERIVED: `0` the sign and the limit of `1/L`; `1` the least box; `2` the
leading coefficient. -/
theorem tendsto_rate_read {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun L : ℕ => -Real.log (casimirLaw (L * θ)) / L) atTop (𝓝 θ) := by
  have hx : Tendsto (fun L : ℕ => (L : ℝ) * θ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hθ
  have hq : Tendsto (fun L : ℕ => Real.exp (-((L : ℝ) * θ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hc (s : ℝ) : Tendsto (fun L : ℕ => θ + (Real.log (1 + s * Real.exp (-((L : ℝ) * θ)))
      - Real.log 2) * ((L : ℝ))⁻¹) atTop (𝓝 θ) := by
    have h := ((((tendsto_const_nhds (x := (1 : ℝ))).add (hq.const_mul s)).log (by norm_num)).sub
      (tendsto_const_nhds (x := Real.log 2))).mul hinv
    have h' := h.const_add θ
    simpa using h'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hc (-1)) (hc 1) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    have hb := (neg_log_casimirLaw_bounds (mul_pos hL0 hθ)).1
    rw [le_div_iff₀ hL0]
    have e : (θ + (Real.log (1 + -1 * Real.exp (-((L : ℝ) * θ))) - Real.log 2) * ((L : ℝ))⁻¹) * L
        = L * θ + Real.log (1 - Real.exp (-((L : ℝ) * θ))) - Real.log 2 := by
      field_simp
      ring_nf
    rw [e]
    exact hb
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    have hb := (neg_log_casimirLaw_bounds (mul_pos hL0 hθ)).2
    rw [div_le_iff₀ hL0]
    have e : (θ + (Real.log (1 + 1 * Real.exp (-((L : ℝ) * θ))) - Real.log 2) * ((L : ℝ))⁻¹) * L
        = L * θ + Real.log (1 + Real.exp (-((L : ℝ) * θ))) - Real.log 2 := by
      field_simp
      ring_nf
    rw [e]
    exact hb

/-- **The free stall**: over a set `S` of rates `θ > 0`, the settling of `casimirLaw (L θ)` is uniform in
`θ ∈ S` exactly when `S` is bounded away from `0`. DERIVED: `0` the sign and the lower end; `1` the least box.
Proof-internal: `1` the level (any positive level). -/
theorem uniform_iff_rate_bounded_below {S : Set ℝ} (hS : ∀ θ ∈ S, 0 < θ) :
    (∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ θ ∈ S, casimirLaw (L * θ) ≤ ε) ↔
      ∃ θ₀ > 0, ∀ θ ∈ S, θ₀ ≤ θ := by
  constructor
  · intro hU
    by_contra hne
    push Not at hne
    obtain ⟨L₀, hL₀⟩ := hU 1 one_pos
    have hLpos : (0 : ℝ) < ((max L₀ 1 : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_pos (le_max_right L₀ 1)
    have hδ : 0 < Real.exp (-1) / ((max L₀ 1 : ℕ) : ℝ) := div_pos (Real.exp_pos _) hLpos
    obtain ⟨θ, hθS, hθlt⟩ := hne _ hδ
    have hθ0 := hS θ hθS
    have hx0 : 0 < ((max L₀ 1 : ℕ) : ℝ) * θ := mul_pos hLpos hθ0
    have hxlt : ((max L₀ 1 : ℕ) : ℝ) * θ < Real.exp (-1) := by
      rw [lt_div_iff₀ hLpos] at hθlt
      linarith
    have h1 := lt_casimirLaw hx0 hxlt
    have h2 := hL₀ (max L₀ 1) (le_max_left _ _) θ hθS
    linarith
  · rintro ⟨θ₀, hθ₀, hge⟩ ε hε
    obtain ⟨X, hX⟩ := eventually_atTop.1 ((tendsto_order.1 tendsto_casimirLaw_atTop).2 ε hε)
    refine ⟨⌈X / θ₀⌉₊, fun L hL θ hθ => (hX _ ?_).le⟩
    have h1 : X / θ₀ ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
    have h2 : X ≤ L * θ₀ := by rwa [div_le_iff₀ hθ₀] at h1
    have h3 : (L : ℝ) * θ₀ ≤ L * θ := mul_le_mul_of_nonneg_left (hge θ hθ) (Nat.cast_nonneg L)
    linarith

/-! ## 2. The free box -/

/-- **The lattice rate** `θ = 2 arsinh(m/2)`: the decay rate of the free propagator, the pole of the lattice
dispersion. DERIVED: `2` the half-angle of the Laplacian `4 sinh²(θ/2)`. -/
def rate (m : ℝ) : ℝ := 2 * Real.arsinh (m / 2)

/-- DERIVED: `2` the half-angle. -/
theorem two_sinh_half_rate (m : ℝ) : 2 * Real.sinh (rate m / 2) = m := by
  rw [rate, show 2 * Real.arsinh (m / 2) / 2 = Real.arsinh (m / 2) by ring, Real.sinh_arsinh]
  ring

/-- DERIVED: `0` the sign; `2` the half-angle. -/
theorem rate_pos_iff {m : ℝ} : 0 < rate m ↔ 0 < m := by
  unfold rate
  constructor
  · intro h
    have h' : 0 < Real.arsinh (m / 2) := by linarith
    have := Real.arsinh_pos_iff.mp h'
    linarith
  · intro h
    have : 0 < Real.arsinh (m / 2) := Real.arsinh_pos_iff.mpr (by linarith)
    linarith

/-- **The free spectrum in the rate**: `ω²_j = 2 cosh θ − 2 cos(2π j/L)` at `m = 2 sinh(θ/2)`.
DERIVED: `1` the spacing; `2` the half-angles and the Laplacian. -/
theorem omega2_eq (θ : ℝ) (L j : ℕ) :
    FreqRead.omega2 (2 * Real.sinh (θ / 2)) 1 L j = 2 * Real.cosh θ - 2 * Real.cos (2 * π * j / L) := by
  have h1 : Real.cosh θ = 1 + 2 * Real.sinh (θ / 2) ^ 2 := by
    have h := Real.cosh_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring, Real.cosh_sq] at h
    rw [h]
    ring
  have h2 : Real.cos (2 * π * j / L) = 1 - 2 * Real.sin (π * j / L) ^ 2 := by
    have h := Real.cos_two_mul (π * j / L)
    rw [show 2 * (π * j / L) = 2 * π * j / L by ring, Real.cos_sq'] at h
    rw [h]
    ring
  simp only [FreqRead.omega2, FreqRead.phat2]
  rw [h1, h2]
  ring

/-- **The pole**: `2 cosh(rate m) − 2 = m²`, the zero-mode frequency of `FreqRead` (`ω₀² = m²`) read as a decay
rate. DERIVED: `2` the half-angle; `1` the spacing; `0` the zero mode. -/
theorem two_cosh_rate (m : ℝ) : 2 * Real.cosh (rate m) - 2 = m ^ 2 := by
  have h := omega2_eq (rate m) 1 0
  rw [two_sinh_half_rate] at h
  simp only [FreqRead.omega2, FreqRead.phat2, Nat.cast_zero, mul_zero, zero_div, Real.sin_zero,
    Real.cos_zero] at h
  linarith

/-- **The roots of unity read the cosine**: `ζ^j + ζ^{−j} = 2 cos(2π j/L)`, `ζ = e^{2πi/L}`.
DERIVED: `2` the two roots and the full turn `2π`. -/
theorem root_pow_add_inv_pow (L j : ℕ) :
    Complex.exp (2 * π * Complex.I / L) ^ j + (Complex.exp (2 * π * Complex.I / L))⁻¹ ^ j
      = 2 * Complex.cos (2 * π * j / L) := by
  rw [Complex.two_cos, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1 <;> congr 1 <;> ring

/-- **The massive product**: `∏_{j<L} (2 cosh θ − 2 cos(2π j/L)) = 2 cosh(L θ) − 2`.
DERIVED: `2` the two roots and the full turn; `0` the least box. -/
theorem prod_cosh_sub_cos (θ : ℝ) {L : ℕ} (hL : 0 < L) :
    ∏ j ∈ range L, (2 * Real.cosh θ - 2 * Real.cos (2 * π * j / L)) = 2 * Real.cosh (L * θ) - 2 := by
  have hζ := Complex.isPrimitiveRoot_exp L hL.ne'
  have hu : Complex.exp θ ≠ 0 := Complex.exp_ne_zero _
  have hP : ∀ μ : ℂ, IsPrimitiveRoot μ L →
      ∏ j ∈ range L, (Complex.exp θ - μ ^ j) = Complex.exp θ ^ L - 1 := by
    intro μ hμ
    have h := congrArg (Polynomial.eval (Complex.exp θ)) (X_pow_sub_C_eq_prod hμ hL (one_pow L))
    simpa [Polynomial.eval_prod] using h.symm
  have hterm : ∀ j ∈ range L, (((2 * Real.cosh θ - 2 * Real.cos (2 * π * j / L) : ℝ)) : ℂ) =
      (Complex.exp θ)⁻¹ * ((Complex.exp θ - Complex.exp (2 * π * Complex.I / L) ^ j) *
        (Complex.exp θ - (Complex.exp (2 * π * Complex.I / L))⁻¹ ^ j)) := by
    intro j _
    have hab : Complex.exp (2 * π * Complex.I / L) ^ j *
        (Complex.exp (2 * π * Complex.I / L))⁻¹ ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_pow]
    have e1 : ∀ u a b : ℂ, u⁻¹ * ((u - a) * (u - b))
        = u⁻¹ * u * u - (a + b) * (u⁻¹ * u) + u⁻¹ * (a * b) := by
      intro u a b
      ring
    rw [e1, hab, inv_mul_cancel₀ hu, root_pow_add_inv_pow]
    push_cast
    rw [Complex.two_cosh, Complex.exp_neg]
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hP _ hζ, hP _ hζ.inv]
  push_cast
  rw [Complex.two_cosh, Complex.exp_neg, Complex.exp_nat_mul, ← inv_pow]
  have hinv : (Complex.exp θ)⁻¹ ^ L * Complex.exp θ ^ L = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hu, one_pow]
  linear_combination (Complex.exp θ ^ L - 2) * hinv

/-- **The massless product**: `∏_{1≤j<L} (2 − 2 cos(2π j/L)) = L²`, `L = n + 1`.
DERIVED: `2` the two roots, the full turn and the square; `1` the first non-zero mode. -/
theorem prod_massless (n : ℕ) :
    ∏ k ∈ range n, (2 - 2 * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      = ((n : ℝ) + 1) ^ 2 := by
  have hζ := Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  have hterm : ∀ k ∈ range n,
      (((2 - 2 * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ)) : ℂ) =
        (1 - Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1)) *
          (1 - (Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)))⁻¹ ^ (k + 1)) := by
    intro k _
    have hab : Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (k + 1) *
        (Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)))⁻¹ ^ (k + 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_pow]
    have e1 : ∀ a b : ℂ, (1 - a) * (1 - b) = 1 - (a + b) + a * b := by
      intro a b
      ring
    rw [e1, hab, root_pow_add_inv_pow]
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
    hζ.prod_one_sub_pow_eq_order, hζ.inv.prod_one_sub_pow_eq_order]
  push_cast
  ring

/-- **The log-determinant** of `−Δ + m²` on the periodic chain of `L` sites: the sum of `log ω²_j` over the
modes with `ω²_j ≠ 0` (at `m = 0`, `det′`: the zero mode removed). DERIVED: `1` the spacing; `0` the excluded
zero frequency. -/
def logDet (m : ℝ) (L : ℕ) : ℝ :=
  ∑ j ∈ (range L).filter (fun j => FreqRead.omega2 m 1 L j ≠ 0), Real.log (FreqRead.omega2 m 1 L j)

/-- **The free energy** `log Z = (L/2) log 2π − logDet / 2` (the Gaussian determinant).
DERIVED: `2` the Gaussian factor `1/2` and `2π` its normalisation. -/
def logZ (m : ℝ) (L : ℕ) : ℝ := (L : ℝ) / 2 * Real.log (2 * π) - logDet m L / 2

/-- **The free doubling defect** in one dimension: `2 log Z(L) − log Z(2L)`. DERIVED: `2 = 2¹` the copies and the
doubling. -/
def defect (m : ℝ) (L : ℕ) : ℝ := 2 * logZ m L - logZ m (2 * L)

/-- **The free window coupling**: the defect at side `2^w`. DERIVED: `2` the doubling. -/
def freeWindow (m : ℝ) (w : ℕ) : ℝ := defect m (2 ^ w)

/-- The filter is only bookkeeping: `log 0 = 0` in Mathlib. DERIVED: `0` the zero frequency. -/
theorem logDet_eq_sum (m : ℝ) (L : ℕ) :
    logDet m L = ∑ j ∈ range L, Real.log (FreqRead.omega2 m 1 L j) := by
  unfold logDet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not.mp h, Real.log_zero]

/-- **The volume terms cancel**: `defect = logDet(2L)/2 − logDet(L)`. DERIVED: `2` the doubling and the
Gaussian factor. -/
theorem defect_eq (m : ℝ) (L : ℕ) : defect m L = logDet m (2 * L) / 2 - logDet m L := by
  unfold defect logZ
  push_cast
  ring

/-- DERIVED: `1`, `2` the units of `2 cosh y − 2`. -/
theorem two_cosh_sub_two (y : ℝ) :
    2 * Real.cosh y - 2 = (1 - Real.exp (-y)) ^ 2 / Real.exp (-y) := by
  have := Real.exp_pos y
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

/-- **The massive log-determinant in the rate**: `logDet = L θ + 2 log(1 − e^{−Lθ})` at `m = 2 sinh(θ/2)`.
DERIVED: `0` the sign and the least box; `2` the square. -/
theorem logDet_of_sinh {θ : ℝ} (hθ : 0 < θ) {L : ℕ} (hL : 0 < L) :
    logDet (2 * Real.sinh (θ / 2)) L = L * θ + 2 * Real.log (1 - Real.exp (-(L * θ))) := by
  have hLθ : 0 < (L : ℝ) * θ := mul_pos (by exact_mod_cast hL) hθ
  have hq := Real.exp_pos (-((L : ℝ) * θ))
  have h1 : 0 < 1 - Real.exp (-((L : ℝ) * θ)) := by linarith [exp_neg_lt_one hLθ]
  have hpos : ∀ j ∈ range L, 2 * Real.cosh θ - 2 * Real.cos (2 * π * j / L) ≠ 0 := by
    intro j _
    have := Real.one_lt_cosh.mpr hθ.ne'
    have := Real.cos_le_one (2 * π * j / L)
    linarith
  rw [logDet_eq_sum, Finset.sum_congr rfl (fun j _ => by rw [omega2_eq θ L j]), ← Real.log_prod hpos,
    prod_cosh_sub_cos θ hL, two_cosh_sub_two, Real.log_div (pow_ne_zero 2 h1.ne') hq.ne', Real.log_pow,
    Real.log_exp]
  push_cast
  ring

/-- DERIVED: `2` the doubling. -/
theorem exp_two_mul_neg (x : ℝ) : Real.exp (-(2 * x)) = Real.exp (-x) ^ 2 := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **The massive defect in closed form**: `defect (2 sinh(θ/2)) L = casimirLaw (L θ)`.
DERIVED: `2` the doubling; `0` the least box. -/
theorem defect_of_sinh {θ : ℝ} (hθ : 0 < θ) {L : ℕ} (hL : 0 < L) :
    defect (2 * Real.sinh (θ / 2)) L = casimirLaw (L * θ) := by
  have hLθ : 0 < (L : ℝ) * θ := mul_pos (by exact_mod_cast hL) hθ
  have hq := Real.exp_pos (-((L : ℝ) * θ))
  have hq1 := exp_neg_lt_one hLθ
  have h1 : 0 < 1 - Real.exp (-((L : ℝ) * θ)) := by linarith
  have h2 : 0 < 1 + Real.exp (-((L : ℝ) * θ)) := by linarith
  have hq2 : Real.exp (-(((2 * L : ℕ) : ℝ) * θ)) = Real.exp (-((L : ℝ) * θ)) ^ 2 := by
    rw [← exp_two_mul_neg]
    congr 1
    push_cast
    ring
  rw [defect_eq, logDet_of_sinh hθ (by omega : 0 < 2 * L), logDet_of_sinh hθ hL, hq2,
    show (1 : ℝ) - Real.exp (-((L : ℝ) * θ)) ^ 2
      = (1 - Real.exp (-((L : ℝ) * θ))) * (1 + Real.exp (-((L : ℝ) * θ))) by ring,
    Real.log_mul h1.ne' h2.ne']
  unfold casimirLaw
  rw [Real.log_div h2.ne' h1.ne']
  push_cast
  ring

/-- **The massive log-determinant**: `logDet m L = L θ + 2 log(1 − e^{−Lθ})`, `θ = rate m`: a bulk term linear
in the volume and an exponentially small finite-size term. DERIVED: `0` the sign and the least box; `2` the
square. -/
theorem logDet_massive {m : ℝ} (hm : 0 < m) {L : ℕ} (hL : 0 < L) :
    logDet m L = L * rate m + 2 * Real.log (1 - Real.exp (-(L * rate m))) := by
  have h := logDet_of_sinh (rate_pos_iff.mpr hm) hL
  rwa [two_sinh_half_rate] at h

/-- **The massive defect**: `defect m L = casimirLaw (L · rate m)`. DERIVED: `0` the sign and the least box. -/
theorem defect_massive {m : ℝ} (hm : 0 < m) {L : ℕ} (hL : 0 < L) :
    defect m L = casimirLaw (L * rate m) := by
  have h := defect_of_sinh (rate_pos_iff.mpr hm) hL
  rwa [two_sinh_half_rate] at h

/-- DERIVED: `0` the mass; `1` the spacing; `2` the Laplacian. -/
theorem omega2_zero_eq (L j : ℕ) :
    FreqRead.omega2 0 1 L j = 2 - 2 * Real.cos (2 * π * j / L) := by
  have h := omega2_eq 0 L j
  simp only [zero_div, Real.sinh_zero, mul_zero, Real.cosh_zero, mul_one] at h
  exact h

/-- **The massless log-determinant** (`det′`): `logDet 0 L = 2 log L`. DERIVED: `0` the mass and the zero
mode; `1` the least box; `2` the square. -/
theorem logDet_massless (n : ℕ) : logDet 0 (n + 1) = 2 * Real.log ((n : ℝ) + 1) := by
  rw [logDet_eq_sum, Finset.sum_range_succ']
  have h0 : FreqRead.omega2 0 1 (n + 1) 0 = 0 := by
    simp [FreqRead.omega2, FreqRead.phat2]
  rw [h0, Real.log_zero, add_zero]
  have hprod := prod_massless n
  have hne : ∏ k ∈ range n, (2 - 2 * Real.cos (2 * π * ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) ≠ 0 := by
    rw [hprod]
    positivity
  simp_rw [omega2_zero_eq]
  rw [← Real.log_prod (fun k hk => Finset.prod_ne_zero_iff.mp hne k hk), hprod, Real.log_pow]
  push_cast
  ring

/-- **The massless defect**: `defect 0 L = log 2 − log L`. DERIVED: `0` the mass; `1` the least box; `2` the
doubling. -/
theorem defect_massless (n : ℕ) : defect 0 (n + 1) = Real.log 2 - Real.log ((n : ℝ) + 1) := by
  rw [defect_eq, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, logDet_massless, logDet_massless]
  have e : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring
  rw [e, Real.log_mul (by norm_num) (by positivity)]
  ring

/-! ## 3. Vanishing read ⇔ mass -/

/-- **Load test (massless fails)**: `defect 0 L → −∞`. DERIVED: `0` the mass; `1` the least box; `2` the
doubling. -/
theorem tendsto_defect_massless : Tendsto (defect 0) atTop atBot := by
  have hlog : Tendsto (fun L : ℕ => Real.log L) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atBot.2 fun B => ?_
  filter_upwards [tendsto_atTop.1 hlog (Real.log 2 - B), eventually_ge_atTop 1] with L hL h1
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [defect_massless]
  push_cast at hL
  linarith

/-- **Load test (massive passes)**: `defect m L → 0` for `m > 0`. DERIVED: `0` the limit and the sign; `1` the
least box. -/
theorem tendsto_defect_massive {m : ℝ} (hm : 0 < m) : Tendsto (defect m) atTop (𝓝 0) := by
  have h : Tendsto (fun L : ℕ => casimirLaw (L * rate m)) atTop (𝓝 0) :=
    tendsto_casimirLaw_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (rate_pos_iff.mpr hm))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  rw [defect_massive hm (by omega)]

/-- **Vanishing read ⇔ mass** (free field, all boxes): for `m ≥ 0`, `defect m L → 0` iff `m > 0`.
DERIVED: `0` the limit and the sign. -/
theorem defect_vanishes_iff {m : ℝ} (hm : 0 ≤ m) : Tendsto (defect m) atTop (𝓝 0) ↔ 0 < m := by
  refine ⟨fun h => ?_, tendsto_defect_massive⟩
  rcases hm.lt_or_eq with hm | hm
  · exact hm
  · subst hm
    exact absurd h (not_tendsto_nhds_of_tendsto_atBot tendsto_defect_massless 0)

/-- **Vanishing read ⇔ mass** along the windows `2^w`, the shape of `StrongAnchor.Vanishes`.
DERIVED: `0` the limit and the sign; `2` the doubling. -/
theorem freeWindow_vanishes_iff {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (freeWindow m) atTop (𝓝 0) ↔ 0 < m := by
  have h2 : Tendsto (fun w : ℕ => (2 : ℕ) ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine ⟨fun h => ?_, fun hm' => (tendsto_defect_massive hm').comp h2⟩
  rcases hm.lt_or_eq with hm | hm
  · exact hm
  · subst hm
    exact absurd h (not_tendsto_nhds_of_tendsto_atBot (tendsto_defect_massless.comp h2) 0)

/-- **Lüscher's form for the free defect**: `defect m L ≤ 2q/(1−q)`, `q = e^{−L·rate m}`.
DERIVED: `0` the sign and the least box; `2` the leading coefficient. -/
theorem defect_le {m : ℝ} (hm : 0 < m) {L : ℕ} (hL : 0 < L) :
    defect m L ≤ 2 * Real.exp (-(L * rate m)) / (1 - Real.exp (-(L * rate m))) := by
  rw [defect_massive hm hL]
  exact casimirLaw_le (mul_pos (by exact_mod_cast hL) (rate_pos_iff.mpr hm))

/-- **The free defect is at least `2q/(1+q)`.** DERIVED: `0` the sign and the least box; `2` the leading
coefficient. -/
theorem le_defect {m : ℝ} (hm : 0 < m) {L : ℕ} (hL : 0 < L) :
    2 * Real.exp (-(L * rate m)) / (1 + Real.exp (-(L * rate m))) ≤ defect m L := by
  rw [defect_massive hm hL]
  exact le_casimirLaw (mul_pos (by exact_mod_cast hL) (rate_pos_iff.mpr hm))

/-- **The free window coupling reads the mass**: `−log(defect m L)/L → rate m`. DERIVED: `0` the sign; `1` the
least box. -/
theorem tendsto_rate_of_defect {m : ℝ} (hm : 0 < m) :
    Tendsto (fun L : ℕ => -Real.log (defect m L) / L) atTop (𝓝 (rate m)) := by
  refine (tendsto_rate_read (rate_pos_iff.mpr hm)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  rw [defect_massive hm (by omega)]

/-! ## 4. The converse direction, as a template, and NoStall -/

section Template

variable {N : ℕ}

/-- **The periodic gap at `β`** at some rate in `(0, 1)`. DERIVED: `0` the plane, the time axis and the lower
end; `1` the upper end. -/
def GapAt (N : ℕ) (hN : N ≠ 0) (β : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r

/-- **Template (Lüscher finite volume; Borgs–Kotecký)**, not proved: at every `β ≥ 0` the periodic gap gives the
vanishing read. The free-field instance is `defect_vanishes_iff` (gap `rate m > 0` ⇔ vanishing).
DERIVED: `0` the lower end. -/
def GapGivesVanishing (N : ℕ) (hN : N ≠ 0) : Prop :=
  ∀ β : ℝ, 0 ≤ β → GapAt N hN β → StrongAnchor.Vanishes N β

/-- **Vanishing gives the gap** (`StrongEndVanishing.windowGap_of_vanishing`). DERIVED: `2` the least rank;
`0` the lower end. -/
theorem gapAt_of_vanishes (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (h : StrongAnchor.Vanishes N β) : GapAt N hN β :=
  StrongEndVanishing.windowGap_of_vanishing hN2 hN hβ h

/-- **NoStall gives the gap at every coupling** (no template). DERIVED: `2` the least rank; `0` the lower
end. -/
theorem gapAt_of_noStall (hN2 : 2 ≤ N) (hN : N ≠ 0) (hR : StrongAnchor.NoStall N) :
    ∀ β : ℝ, 0 ≤ β → GapAt N hN β :=
  fun β hβ => gapAt_of_vanishes hN2 hN hβ ((StrongAnchor.noStall_iff hN).mp hR β hβ)

/-- **Under the template, the vanishing read is the gap.** DERIVED: `2` the least rank; `0` the lower end. -/
theorem vanishes_iff_gapAt (hN2 : 2 ≤ N) (hN : N ≠ 0) (hT : GapGivesVanishing N hN) {β : ℝ}
    (hβ : 0 ≤ β) : StrongAnchor.Vanishes N β ↔ GapAt N hN β :=
  ⟨gapAt_of_vanishes hN2 hN hβ, hT β hβ⟩

/-- **Under the template, NoStall is the gap at every coupling.** DERIVED: `2` the least rank; `0` the lower
end. -/
theorem noStall_iff_gapAt (hN2 : 2 ≤ N) (hN : N ≠ 0) (hT : GapGivesVanishing N hN) :
    StrongAnchor.NoStall N ↔ ∀ β : ℝ, 0 ≤ β → GapAt N hN β :=
  ⟨gapAt_of_noStall hN2 hN, fun h => (StrongAnchor.noStall_iff hN).mpr fun β hβ => hT β hβ (h β hβ)⟩

/-- **Under the template, StrongEnd is the gap frequently at `∞`.** DERIVED: `2` the least rank; `0` the lower
end. -/
theorem strongEnd_iff_frequently_gapAt (hN2 : 2 ≤ N) (hN : N ≠ 0) (hT : GapGivesVanishing N hN) :
    CouplingTower.StrongEnd N ↔ ∃ᶠ β in atTop, GapAt N hN β := by
  constructor
  · intro hS
    exact (StrongEndVanishing.frequently_windowGap hN2 hN hS).mono fun β h => h.2
  · intro h
    exact (h.and_eventually (eventually_ge_atTop 0)).mono fun β hb => hT β hb.2 hb.1

end Template

/-! ## 5. The d-dimensional extension (stated) -/

/-- **The free frequency on the box `L^d`**: `ω²_k = m² + Σ_μ 4 sin²(π k_μ/L)`. DERIVED: `1` the spacing. -/
def omega2D (m : ℝ) (d L : ℕ) (k : Fin d → Fin L) : ℝ :=
  m ^ 2 + ∑ μ, FreqRead.phat2 1 L (k μ)

/-- **The log-determinant on `L^d`** (`det′` at `m = 0`). DERIVED: `0` the excluded zero frequency. -/
def logDetD (m : ℝ) (d L : ℕ) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Fin d → Fin L)).filter (fun k => omega2D m d L k ≠ 0),
    Real.log (omega2D m d L k)

/-- **The free energy on `L^d`.** DERIVED: `2` the Gaussian factor and `2π` its normalisation. -/
def logZD (m : ℝ) (d L : ℕ) : ℝ := (L : ℝ) ^ d / 2 * Real.log (2 * π) - logDetD m d L / 2

/-- **The free doubling defect on `L^d`**: `2^d log Z(L^d) − log Z((2L)^d)`. At `d = 4`: `16 log Z(n⁴) −
log Z((2n)⁴)`, the shape of `windowCoupling`. DERIVED: `2^d` the copies; `2` the doubling. -/
def defectD (m : ℝ) (d L : ℕ) : ℝ := 2 ^ d * logZD m d L - logZD m d (2 * L)

/-- **Template**: the massive free defect on `L^d` vanishes (Poisson summation of the transverse modes).
DERIVED: `0` the limit and the sign. -/
def FreeCasimirD (d : ℕ) : Prop := ∀ m : ℝ, 0 < m → Tendsto (defectD m d) atTop (𝓝 0)

/-- **Template**: the massless free defect on `L^d` does not vanish (`det′` asymptotics).
DERIVED: `0` the mass and the limit. -/
def FreeMasslessFailsD (d : ℕ) : Prop := ¬ Tendsto (defectD 0 d) atTop (𝓝 0)

end MassGap.WindowFreq

end

#print axioms MassGap.WindowFreq.casimirLaw_le
#print axioms MassGap.WindowFreq.le_casimirLaw
#print axioms MassGap.WindowFreq.casimirLaw_pos
#print axioms MassGap.WindowFreq.casimirLaw_anti
#print axioms MassGap.WindowFreq.tendsto_casimirLaw_atTop
#print axioms MassGap.WindowFreq.lt_casimirLaw
#print axioms MassGap.WindowFreq.tendsto_casimirLaw_zero
#print axioms MassGap.WindowFreq.neg_log_casimirLaw_bounds
#print axioms MassGap.WindowFreq.tendsto_rate_read
#print axioms MassGap.WindowFreq.uniform_iff_rate_bounded_below
#print axioms MassGap.WindowFreq.two_sinh_half_rate
#print axioms MassGap.WindowFreq.rate_pos_iff
#print axioms MassGap.WindowFreq.omega2_eq
#print axioms MassGap.WindowFreq.two_cosh_rate
#print axioms MassGap.WindowFreq.root_pow_add_inv_pow
#print axioms MassGap.WindowFreq.prod_cosh_sub_cos
#print axioms MassGap.WindowFreq.prod_massless
#print axioms MassGap.WindowFreq.logDet_eq_sum
#print axioms MassGap.WindowFreq.defect_eq
#print axioms MassGap.WindowFreq.two_cosh_sub_two
#print axioms MassGap.WindowFreq.logDet_of_sinh
#print axioms MassGap.WindowFreq.defect_of_sinh
#print axioms MassGap.WindowFreq.logDet_massive
#print axioms MassGap.WindowFreq.defect_massive
#print axioms MassGap.WindowFreq.omega2_zero_eq
#print axioms MassGap.WindowFreq.logDet_massless
#print axioms MassGap.WindowFreq.defect_massless
#print axioms MassGap.WindowFreq.tendsto_defect_massless
#print axioms MassGap.WindowFreq.tendsto_defect_massive
#print axioms MassGap.WindowFreq.defect_vanishes_iff
#print axioms MassGap.WindowFreq.freeWindow_vanishes_iff
#print axioms MassGap.WindowFreq.defect_le
#print axioms MassGap.WindowFreq.le_defect
#print axioms MassGap.WindowFreq.tendsto_rate_of_defect
#print axioms MassGap.WindowFreq.gapAt_of_vanishes
#print axioms MassGap.WindowFreq.gapAt_of_noStall
#print axioms MassGap.WindowFreq.vanishes_iff_gapAt
#print axioms MassGap.WindowFreq.noStall_iff_gapAt
#print axioms MassGap.WindowFreq.strongEnd_iff_frequently_gapAt
#print axioms MassGap.WindowFreq.exp_neg_lt_one
#print axioms MassGap.WindowFreq.exp_two_mul_neg
