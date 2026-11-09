import Mathlib
import MassGap.MixExpand
import MassGap.TwoDVanish
import MassGap.StripRow

/-!
# MassGap.StripWidth — an explicit strip of vanishing in the mixed coupling

On the anisotropic torus (`AnisoTorus.DA N β t w`, in-plane `β`, mixed `t`) the defect vanishes along the windows
at `t = 0` for every `β` (`TwoDVanish.decoupled_vanishes`), and `MixAnchor.weakMixAnchor_of_decoupled` extends that
to an unquantified interval by continuity at one seed window. This module puts a number on the interval, at every
`β ≥ 0` and every `N ≠ 0`, with no named input. Declarations are in `MassGap.StripWidth`.

## The result

* `strip_width`: `DA(β, t, ·) → 0` for `0 ≤ t < t_low(β) = e^{−4β} / (16192 (16 β + 27))`, uniformly in `N`. Sharper,
  `strip_width_area` with `t*(N, β) = 1/(16192 (1 + L (16 β + 26)))`, `L = b e^{4β}` the coherence area of the floor.
* `strip_width_poly`: `DA(β, t, ·) → 0` for `0 ≤ t ≤ t_poly(N, β) = 1/(16192 n₀²)`, with
  `n₀ = 2 + 2 ℓ (2 L + 41 + 6 log ℓ)`, `ℓ = 240 + 150 (N + 4) β`, `L = 1 + 2 N² log K`, `K = ⌈2 √(2 N (β + 1))⌉ + 1`.
  So `t_poly ≍ c_N⁻¹ (β log β)⁻²`: the strip shrinks polynomially, not exponentially.
* `strip_width_max`: the larger of the two widths. `diag_small`: the strip contains the diagonal for
  `β ≤ 1/500000`, which quantifies `MixPlane.diag_anchor`.
* `tPoly_le`: `t_poly(N, β) ≤ 1/(16192 (300 (N + 4) β)² + 16192)`, so `t_poly/β → 0`.

## The mixed term: an extensive bound from the colouring (§2–§5)

Taylor expansion at `t = 0` with the trivial range `R = 16 n⁴` of `S_mix` gives `t R ≲ 1`, that is `t ≲ n⁻⁴`, at every
order: more derivatives do not help a range bound. This module replaces it by a moment generating function bound.
The base sites of a mixed orientation `(i, j)` are coloured by the parities of their coordinates `i`, `j`: sixteen
colours. On an even extent no site of a colour is a corner of the plaquette of another site of that colour
(`not_corner_of_par`), since a step flips a parity. So the plaquettes of one colour are independent and Haar under
`e^{−β S_in}` (`integral_family`: the layer rotation of `MixCut.gT` at each base in turn). Convexity of `exp` over the
colours and Hoeffding's lemma give the upper comparison `ZA_le`; the tangent line gives the lower one `ZA_ge`; the
bulk term cancels between `16 log Z_n` and `log Z_{2n}`:

  `DA(β, t, w) ≤ DA(β, 0, w) + 8192 · 16^w t²`  (`DA_le`).

So one seed window `w` opens `t ≤ 1/(4048 · 4^w)` (`strip_of_seed`): the strip is the inverse of the seed area.

## The seed (§6–§9)

`strip_of_seed` needs one window with `DA(β, 0, w) ≤ 1/2000`, and `DA_zero_eq` reads that off the ratio
`ρ(n) = Z₂(n)/b^{n²}`.

* The floor: `TwoDVanish.abs_ratio_sub_one_le` has `q = 1 − 1/L` with `L = b e^{4β}`, so `1 − q` is exponentially
  small in `β`, and `seed_floor` gives the area `1 + L (16 β + 26)`. This is `strip_width`.
* The walk: `StripGap.walk_gap` proves the spectral gap `1/ℓ` of the plaquette walk on `SU(N)`, `ℓ` linear in `β`;
  `StripRow.ratio_row` integrates each row of vertical links, so `ρ(n) ∈ [(1 − η)^n, (1 + η)^n]` with
  `η ≈ e^{−n/(2ℓ)}/b`. `StripGap.bk_ge` bounds `1/b` by `e^L`, `L` logarithmic in `β`. `seed_walk`: side `n₀`. This
  is `strip_width_poly`.

DERIVED (module-wide): `16 = 2⁴` the colours and the copies; `2` the doubling, the parity, the orientations of a
plaquette; `32 = 2 · 16`; `512 = 32²/2`; `8192 = 16 · 512`; `8` from `LayerSplit.layerDefect_eq`; `48 = 8 · 6`;
`4` the area of the doubling and the floor exponent; `0` the decoupled end and the limits; `1` the least window.
COMPUTED: `4048² ≥ 8192 · 2000`; `16192 = 4 · 4048`; `e^{13} ≥ 384000`; `e^{20.5} ≥ 663552000`; `26`, `41` the
corresponding exponents. CHOSEN: the half `1/2000` of the seed left to the decoupled term; the factors `e^{y/2}`
that absorb the prefactors; the factor `4` of `exists_window`. Inherited: `1/1000`, `250` from `DoublingSharp`.

## What does not follow

Nothing here reaches the diagonal at large `β`: `tPoly_le` and the shape of `DA_le` stop at `t ~ 1/(seed area)`, and
`t_poly/β → 0`. The gap between the strip and the diagonal is all of `t_poly(N, β) < t ≤ β`, and
`CouplingTower.StrongEnd`, `AnisoTorus.AnisoAnalytic`, `MixCutTest.VarGap` and `MixPlane.NoStallOnSegment` stay open.
`DA_le` keeps no cancellation between `16 log Z_n` and `log Z_{2n}` beyond the bulk: the term `16 κ₂(n) − κ₂(2n) = 0`
of `MixEqui.varGap_zero` is not used away from `t = 0`, and a bound of order `t⁴ n⁴` would need an extensive
fourth cumulant on `[0, t]`, not proved. The row bound reads decay in the side `n`, not in the area: the seed side is
`ℓ L`, where a gluing of the rows into one convolution power of `n²` faces would give seed area `ℓ L`, and so
`t ≍ 1/(β log β)`; that gluing is not built. No Dobrushin-type bound in `t` is built. The arguments here use no
non-abelian structure beyond the matrix form of `SU(N)`; if the `U(1)` analogue stalls at `t = β`, as argued in
`AnisoTorus` §5, these arguments cannot reach `t = β`.
-/

namespace MassGap.StripWidth

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut
  MassGap.MixEqui MassGap.MixExpand

variable {N : ℕ}

/-! ## 1. The Haar tilt -/

/-- **The Haar tilt** `H(s) = ∫ e^{s(φ − ⟨φ⟩)} dHaar`. No numeral. -/
noncomputable def haarTilt (N : ℕ) (s : ℝ) : ℝ :=
  ∫ g, Real.exp (s * (WilsonAction.wilsonDensity (N := N) g - WindowRead.haarMeanN N))
    ∂(probHaar (SUN.SU N))

theorem continuous_tilt (s : ℝ) : Continuous fun g : SUN.SU N =>
    Real.exp (s * (WilsonAction.wilsonDensity g - WindowRead.haarMeanN N)) :=
  Real.continuous_exp.comp (continuous_const.mul
    (WilsonAction.continuous_wilsonDensity.sub continuous_const))

theorem haarTilt_nonneg (s : ℝ) : 0 ≤ haarTilt N s :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- **Hoeffding's lemma for the plaquette density**: `H(s) ≤ e^{s²/2}`. DERIVED: `2` the range of `φ`, which
makes the sub-Gaussian parameter `(2/2)² = 1`, and the exponent of the Gaussian. -/
theorem haarTilt_le (hN : N ≠ 0) (s : ℝ) : haarTilt N s ≤ Real.exp (s ^ 2 / 2) := by
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := probHaar (SUN.SU N))
    (X := WilsonAction.wilsonDensity (N := N)) (a := 0) (b := 2)
    WilsonAction.continuous_wilsonDensity.aemeasurable
    (Eventually.of_forall fun g =>
      ⟨WilsonAction.wilsonDensity_nonneg hN g, WilsonAction.wilsonDensity_le_two hN g⟩)
  have hm := h.mgf_le s
  have e2 : ‖(2 : ℝ) - 0‖₊ = 2 := NNReal.eq (by simp)
  have e : (‖(2 : ℝ) - 0‖₊ / 2) ^ 2 = 1 := by rw [e2]; norm_num
  rw [e] at hm
  unfold ProbabilityTheory.mgf at hm
  unfold haarTilt WindowRead.haarMeanN
  simpa using hm

/-! ## 2. Mixed plaquettes of one colour are independent at the decoupled end -/

/-- The low direction `k ∈ {0, 1}`. DERIVED: `4`, `2` the blocks. -/
def dirLo (k : Fin 2) : Fin 4 := ⟨k.val, by omega⟩

/-- The high direction `2 + k ∈ {2, 3}`. DERIVED: `4`, `2` the blocks. -/
def dirHi (k : Fin 2) : Fin 4 := ⟨k.val + 2, by omega⟩

theorem dirLo_block (k : Fin 2) : (dirLo k).val / 2 = 0 := by
  have := k.isLt; simp only [dirLo]; omega

theorem dirHi_block (k : Fin 2) : ¬ (dirHi k).val / 2 = 0 := by
  have := k.isLt; simp only [dirHi]; omega

theorem dirLo_ne_dirHi (a b : Fin 2) : dirLo a ≠ dirHi b := by
  intro h
  have h1 := congrArg Fin.val h
  have := a.isLt
  simp only [dirLo, dirHi] at h1
  omega

/-- The parities of the coordinates `i`, `j` of a site. DERIVED: `2` the parity. -/
def parOf {n : ℕ} (i j : Fin 4) (y : St n) : Bool × Bool :=
  (decide ((y i).val % 2 = 0), decide ((y j).val % 2 = 0))

/-- One step flips the parity on an even extent. DERIVED: `2` the parity and the least extent. -/
theorem parity_rot {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) (a : Fin n) :
    decide ((finRotate n a).val % 2 = 0) ≠ decide (a.val % 2 = 0) := by
  have h := rot_val he hn a
  intro e
  have e' : (finRotate n a).val % 2 = 0 ↔ a.val % 2 = 0 := by simpa using e
  omega

/-- **Sites of one parity pair are never corners of each other**: on an even extent, `y' ≠ y` with the same
parities in `i`, `j` is no corner of `((i, j), y)`, since each of the three other corners has a parity flipped.
DERIVED: `2` the parity and the least extent. -/
theorem not_corner_of_par {n : ℕ} (he : n % 2 = 0) (hn : 2 ≤ n) {i j : Fin 4} (hij : i ≠ j) {y y' : St n}
    (hp : parOf i j y' = parOf i j y) (hne : y ≠ y') : ¬ IsCorner n i j y y' := by
  have h1 : decide ((y' i).val % 2 = 0) = decide ((y i).val % 2 = 0) := congrArg Prod.fst hp
  have h2 : decide ((y' j).val % 2 = 0) = decide ((y j).val % 2 = 0) := congrArg Prod.snd hp
  rintro (h | h | h | h)
  · exact hne h.symm
  · refine parity_rot he hn (y i) ?_
    rw [← h1, h]
    have : rshift (fun _ : Fin 4 => n) i y i = finRotate n (y i) := by
      rw [rshift_apply, if_pos rfl]
    rw [this]
  · refine parity_rot he hn (y j) ?_
    rw [← h2, h]
    have : rshift (fun _ : Fin 4 => n) j y j = finRotate n (y j) := by
      rw [rshift_apply, if_pos rfl]
    rw [this]
  · refine parity_rot he hn (y i) ?_
    rw [← h1, h]
    have : rshift (fun _ : Fin 4 => n) i (rshift (fun _ : Fin 4 => n) j y) i = finRotate n (y i) := by
      rw [rshift_apply, if_pos rfl, rshift_apply, if_neg hij]
    rw [this]

/-- **A family of mixed plaquettes with no shared corner is independent and Haar at the decoupled end**:
`∫ ∏_{y ∈ T} f(hol_y) e^{−β S_in} = (∫ f)^{|T|} ∫ e^{−β S_in}` when no site of `T` is a corner of another's
plaquette. The layer rotation at `y₀` moves the plaquette at `y₀` and fixes `S_in` and the others. DERIVED: `2`
the least extent; `0` the decoupled end. -/
theorem integral_family {n : ℕ} (hn : 2 ≤ n) (β : ℝ) {i j : Fin 4} (hi : i.val / 2 = 0)
    (hj : ¬ j.val / 2 = 0) {f : SUN.SU N → ℝ} (hf : Continuous f) (T : Finset (St n))
    (hT : ∀ y ∈ T, ∀ y' ∈ T, y ≠ y' → ¬ IsCorner n i j y y') :
    ∫ U, (∏ y ∈ T, f ((sysR (fun _ => n) N).hol ((i, j), y) U)) * Real.exp (-(β * sinR N n U)) ∂piH N n
      = (∫ g, f g ∂(probHaar (SUN.SU N))) ^ T.card
        * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert y₀ S hy₀ ih =>
    have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
    have hE : Continuous fun U : Lk n → SUN.SU N =>
        (∏ y ∈ S, f ((sysR (fun _ => n) N).hol ((i, j), y) U)) * Real.exp (-(β * sinR N n U)) :=
      (continuous_finsetProd _ fun y _ => hf.comp (MixAnchor.continuous_hol _)).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg)
    have hET : ∀ (g : SUN.SU N) (U : Lk n → SUN.SU N),
        (∏ y ∈ S, f ((sysR (fun _ => n) N).hol ((i, j), y)
            (gT (fun _ => n) (siteG (fun _ => n) y₀ g) U)))
          * Real.exp (-(β * sinR N n (gT (fun _ => n) (siteG (fun _ => n) y₀ g) U)))
        = (∏ y ∈ S, f ((sysR (fun _ => n) N).hol ((i, j), y) U)) * Real.exp (-(β * sinR N n U)) := by
      intro g U
      rw [sinR_gT]
      congr 1
      refine Finset.prod_congr rfl fun y hy => ?_
      have hne : y ≠ y₀ := fun h => hy₀ (h ▸ hy)
      rw [hol_gT_off hi hj y y₀ g U
        (hT y (Finset.mem_insert_of_mem hy) y₀ (Finset.mem_insert_self _ _) hne)]
    have key := integral_avg_gen (L := fun _ => n) f hf
      (fun g U => gT (fun _ => n) (siteG (fun _ => n) y₀ g) U)
      (fun g F hF => integral_gT (fun _ => n) _ F hF)
      (fun U => (sysR (fun _ => n) N).hol ((i, j), y₀) U) (MixAnchor.continuous_hol _)
      _ hE (fun g k => g * k) continuous_mul
      (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj y₀) hET
      (fun k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) f k)
    have hS := ih fun y hy y' hy' =>
      hT y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy')
    rw [Finset.card_insert_of_notMem hy₀]
    have hrw : ∀ U : Lk n → SUN.SU N,
        (∏ y ∈ insert y₀ S, f ((sysR (fun _ => n) N).hol ((i, j), y) U))
            * Real.exp (-(β * sinR N n U))
          = f ((sysR (fun _ => n) N).hol ((i, j), y₀) U)
            * ((∏ y ∈ S, f ((sysR (fun _ => n) N).hol ((i, j), y) U))
              * Real.exp (-(β * sinR N n U))) := fun U => by
      rw [Finset.prod_insert hy₀]; ring
    simp_rw [hrw]
    rw [key, hS, pow_succ]
    ring

/-! ## 3. The colouring of the mixed plaquettes -/

/-- **The sixteen colours**: a low direction, a high direction, and the parities of the base in those two
directions. DERIVED: `2` each of the four binary choices. -/
abbrev Col : Type := (Fin 2 × Fin 2) × (Bool × Bool)

theorem card_col : Fintype.card Col = 16 := by simp [Fintype.card_prod]

/-- The base sites of one colour. No numeral. -/
def cls (n : ℕ) (c : Col) : Finset (St n) :=
  Finset.univ.filter fun y => parOf (dirLo c.1.1) (dirHi c.1.2) y = c.2

/-- The centred action of one colour. No numeral. -/
noncomputable def colSum (N n : ℕ) (c : Col) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ y ∈ cls n c, (plaq N n ((dirLo c.1.1, dirHi c.1.2), y) U - WindowRead.haarMeanN N)

theorem card_st (n : ℕ) : Fintype.card (St n) = n ^ 4 := by
  simp [Fintype.card_pi]

theorem card_cls_le (n : ℕ) (c : Col) : (cls n c).card ≤ n ^ 4 := by
  rw [← card_st]; exact Finset.card_le_univ _

/-- **The mixed action over the normal orientations**: each of the four unordered mixed orientations appears
twice. DERIVED: `2` the two orientations of a plaquette. -/
theorem smix_normal (n : ℕ) (U : Lk n → SUN.SU N) :
    smixR N n U = 2 * ∑ k : Fin 2 × Fin 2, ∑ y : St n, plaq N n ((dirLo k.1, dirHi k.2), y) U := by
  have hsw : ∀ (a b : Fin 4), ∑ y : St n, plaq N n ((b, a), y) U = ∑ y : St n, plaq N n ((a, b), y) U :=
    fun a b => Finset.sum_congr rfl fun y _ => plaq_swap a b y U
  have e : smixR N n U = ∑ i : Fin 4, ∑ j : Fin 4,
      (if AnisoTorus.inPlane (i, j) then (0 : ℝ) else ∑ y : St n, plaq N n ((i, j), y) U) := by
    unfold smixR
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · exact Finset.sum_eq_zero fun y _ => by simp [h]
    · exact Finset.sum_congr rfl fun y _ => by simp [h]
  rw [e, Fintype.sum_prod_type]
  have d0 : dirLo 0 = 0 := rfl
  have d1 : dirLo 1 = 1 := rfl
  have d2 : dirHi 0 = 2 := rfl
  have d3 : dirHi 1 = 3 := rfl
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, d0, d1, d2, d3]
  have i00 : AnisoTorus.inPlane ((0 : Fin 4), (0 : Fin 4)) = true := by decide
  have i01 : AnisoTorus.inPlane ((0 : Fin 4), (1 : Fin 4)) = true := by decide
  have i02 : AnisoTorus.inPlane ((0 : Fin 4), (2 : Fin 4)) = false := by decide
  have i03 : AnisoTorus.inPlane ((0 : Fin 4), (3 : Fin 4)) = false := by decide
  have i10 : AnisoTorus.inPlane ((1 : Fin 4), (0 : Fin 4)) = true := by decide
  have i11 : AnisoTorus.inPlane ((1 : Fin 4), (1 : Fin 4)) = true := by decide
  have i12 : AnisoTorus.inPlane ((1 : Fin 4), (2 : Fin 4)) = false := by decide
  have i13 : AnisoTorus.inPlane ((1 : Fin 4), (3 : Fin 4)) = false := by decide
  have i20 : AnisoTorus.inPlane ((2 : Fin 4), (0 : Fin 4)) = false := by decide
  have i21 : AnisoTorus.inPlane ((2 : Fin 4), (1 : Fin 4)) = false := by decide
  have i22 : AnisoTorus.inPlane ((2 : Fin 4), (2 : Fin 4)) = true := by decide
  have i23 : AnisoTorus.inPlane ((2 : Fin 4), (3 : Fin 4)) = true := by decide
  have i30 : AnisoTorus.inPlane ((3 : Fin 4), (0 : Fin 4)) = false := by decide
  have i31 : AnisoTorus.inPlane ((3 : Fin 4), (1 : Fin 4)) = false := by decide
  have i32 : AnisoTorus.inPlane ((3 : Fin 4), (2 : Fin 4)) = true := by decide
  have i33 : AnisoTorus.inPlane ((3 : Fin 4), (3 : Fin 4)) = true := by decide
  simp only [i00, i01, i02, i03, i10, i11, i12, i13, i20, i21, i22, i23, i30, i31, i32, i33,
    if_true, if_false, Bool.false_eq_true]
  rw [hsw 0 2, hsw 0 3, hsw 1 2, hsw 1 3]
  ring

/-- **The centred mixed action is twice the sum of the colours.** DERIVED: `8 = 2 · 4` the orientations of each
of the four unordered mixed orientations, `n⁴` the sites. -/
theorem smix_colours (n : ℕ) (U : Lk n → SUN.SU N) :
    smixR N n U - 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N = 2 * ∑ c : Col, colSum N n c U := by
  have hrow : ∀ k : Fin 2 × Fin 2, ∑ b : Bool × Bool, colSum N n (k, b) U
      = ∑ y : St n, plaq N n ((dirLo k.1, dirHi k.2), y) U
        - (n : ℝ) ^ 4 * WindowRead.haarMeanN N := by
    intro k
    unfold colSum cls
    simp only
    rw [Finset.sum_fiberwise (Finset.univ : Finset (St n)) (parOf (dirLo k.1) (dirHi k.2))
      (fun y => plaq N n ((dirLo k.1, dirHi k.2), y) U - WindowRead.haarMeanN N),
      Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, card_st, nsmul_eq_mul]
    push_cast
    ring
  rw [Fintype.sum_prod_type]
  simp only [hrow]
  rw [Finset.sum_sub_distrib, smix_normal]
  simp [Fintype.card_prod]
  ring

/-- `e^{mean}` is at most the mean of `e`, over the sixteen colours. DERIVED: `16` the colours. -/
theorem exp_sum_le (a : Col → ℝ) :
    Real.exp (∑ c, a c) ≤ (1 / 16) * ∑ c, Real.exp (16 * a c) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset Col)) (w := fun _ => (1 / 16 : ℝ))
    (p := fun c => 16 * a c) (fun _ _ => by norm_num)
    (by simp [Finset.card_univ]) (fun _ _ => mem_univ _)
  simp only [smul_eq_mul] at h
  have e : ∑ c, (1 / 16 : ℝ) * (16 * a c) = ∑ c, a c :=
    Finset.sum_congr rfl fun c _ => by ring
  rw [e, ← Finset.mul_sum] at h
  exact h

/-! ## 4. The two-sided comparison of the mixed tilt -/

theorem hint {n : ℕ} {F : (Lk n → SUN.SU N) → ℝ} (hF : Continuous F) : Integrable F (piH N n) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **One colour tilted**: the product over its base sites integrates to a power of the Haar tilt.
DERIVED: `2` the parity and the least extent. -/
theorem integral_colour (hN : N ≠ 0) {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) (β s : ℝ) (c : Col) :
    ∫ U, Real.exp (s * colSum N n c U) * Real.exp (-(β * sinR N n U)) ∂piH N n
      ≤ Real.exp ((n : ℝ) ^ 4 * (s ^ 2 / 2)) * ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
  have hZ : 0 ≤ ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := integral_nonneg fun _ => (Real.exp_pos _).le
  have hfam := integral_family (N := N) hn β (dirLo_block c.1.1) (dirHi_block c.1.2)
    (continuous_tilt (N := N) s) (cls n c) (by
      intro y hy y' hy' hne
      have h1 := (Finset.mem_filter.1 hy).2
      have h2 := (Finset.mem_filter.1 hy').2
      exact not_corner_of_par he hn (dirLo_ne_dirHi _ _) (h2.trans h1.symm) hne)
  have e : ∀ U : Lk n → SUN.SU N, Real.exp (s * colSum N n c U)
      = ∏ y ∈ cls n c, Real.exp (s * (WilsonAction.wilsonDensity
          ((sysR (fun _ => n) N).hol ((dirLo c.1.1, dirHi c.1.2), y) U) - WindowRead.haarMeanN N)) := by
    intro U
    unfold colSum
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  simp_rw [e]
  rw [hfam]
  refine mul_le_mul_of_nonneg_right ?_ hZ
  have hH : (0 : ℝ) ≤ s ^ 2 / 2 := by positivity
  have h1 : haarTilt N s ^ (cls n c).card ≤ Real.exp (s ^ 2 / 2) ^ (cls n c).card :=
    pow_le_pow_left₀ (haarTilt_nonneg s) (haarTilt_le hN s) _
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ hH))
  exact_mod_cast card_cls_le n c

/-- **The upper comparison**: `Z(t) ≤ e^{−t ⟨S⟩₀ + 512 n⁴ t²} Z(0)` on an even extent, with `⟨S⟩₀ = 8 n⁴ ⟨φ⟩`.
DERIVED: `32 = 2 · 16` the two orientations times the colours; `512 = 32²/2`; `8 = 2 · 4` the mixed
plaquettes per site, as in `smix_colours`. -/
theorem ZA_le (hN : N ≠ 0) {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) (β t : ℝ) :
    AnisoTorus.ZA N β t n
      ≤ Real.exp (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) + 512 * (n : ℝ) ^ 4 * t ^ 2)
        * AnisoTorus.ZA N β 0 n := by
  have hZ0 : AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    rw [ZA_eq_int]; simp only [zero_mul, add_zero]
  set M : ℝ := 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N with hM
  have hcol : ∀ c : Col, Continuous fun U : Lk n → SUN.SU N =>
      Real.exp (-(32 * t) * colSum N n c U) * Real.exp (-(β * sinR N n U)) := by
    intro c
    refine (Real.continuous_exp.comp (continuous_const.mul ?_)).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg)
    unfold colSum
    exact continuous_finsetSum _ fun y _ => (continuous_plaq n _).sub continuous_const
  have hpt : ∀ U : Lk n → SUN.SU N, Real.exp (-(β * sinR N n U + t * smixR N n U))
      ≤ Real.exp (-t * M) * ((1 / 16) * ∑ c : Col,
          Real.exp (-(32 * t) * colSum N n c U) * Real.exp (-(β * sinR N n U))) := by
    intro U
    have hs := smix_colours n U
    have e1 : -(β * sinR N n U + t * smixR N n U)
        = (-t * M + -(β * sinR N n U)) + ∑ c : Col, -(2 * t) * colSum N n c U := by
      have : smixR N n U = M + 2 * ∑ c : Col, colSum N n c U := by rw [hM]; linarith
      rw [this, ← Finset.mul_sum]; ring
    have hj := exp_sum_le fun c => -(2 * t) * colSum N n c U
    have e2 : ∀ c : Col, 16 * (-(2 * t) * colSum N n c U) = -(32 * t) * colSum N n c U :=
      fun c => by ring
    simp only [e2] at hj
    rw [e1, Real.exp_add, Real.exp_add]
    have hp : 0 ≤ Real.exp (-t * M) * Real.exp (-(β * sinR N n U)) := by positivity
    calc Real.exp (-t * M) * Real.exp (-(β * sinR N n U))
          * Real.exp (∑ c : Col, -(2 * t) * colSum N n c U)
        ≤ Real.exp (-t * M) * Real.exp (-(β * sinR N n U))
            * ((1 / 16) * ∑ c : Col, Real.exp (-(32 * t) * colSum N n c U)) :=
          mul_le_mul_of_nonneg_left hj hp
      _ = _ := by rw [← Finset.sum_mul]; ring
  set Z₀ : ℝ := ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n with hZdef
  have hZpos : 0 ≤ Z₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hint0 : Integrable (fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U + t * smixR N n U)))
      (piH N n) := hint (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_sinR n)).add (continuous_const.mul (continuous_smixR n))).neg)
  have hsum : Continuous fun U : Lk n → SUN.SU N => Real.exp (-t * M) * ((1 / 16) * ∑ c : Col,
      Real.exp (-(32 * t) * colSum N n c U) * Real.exp (-(β * sinR N n U))) :=
    continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun c _ => hcol c))
  rw [ZA_eq_int β t n, hZ0]
  calc ∫ U, Real.exp (-(β * sinR N n U + t * smixR N n U)) ∂piH N n
      ≤ ∫ U, Real.exp (-t * M) * ((1 / 16) * ∑ c : Col,
          Real.exp (-(32 * t) * colSum N n c U) * Real.exp (-(β * sinR N n U))) ∂piH N n :=
        integral_mono hint0 (hint hsum) hpt
    _ = Real.exp (-t * M) * ((1 / 16) * ∑ c : Col,
          ∫ U, Real.exp (-(32 * t) * colSum N n c U) * Real.exp (-(β * sinR N n U)) ∂piH N n) := by
        rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun c _ => hint (hcol c)]
    _ ≤ Real.exp (-t * M) * ((1 / 16) * ∑ _c : Col,
          Real.exp ((n : ℝ) ^ 4 * ((-(32 * t)) ^ 2 / 2)) * Z₀) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun c _ => integral_colour hN hn he β _ c) (by norm_num)) (Real.exp_pos _).le
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, card_col, Real.exp_add,
          show (n : ℝ) ^ 4 * ((-(32 * t)) ^ 2 / 2) = 512 * (n : ℝ) ^ 4 * t ^ 2 by ring]
        simp only [nsmul_eq_mul]
        push_cast
        ring

/-- **The lower comparison**: `e^{−t ⟨S⟩₀} Z(0) ≤ Z(t)`, the tangent line of the convex `log Z`. DERIVED: `8`,
`4` the mean of `MixCut.meanMix_zero`; `2` the least extent; `1` the tangent of `exp`. -/
theorem ZA_ge {n : ℕ} (hn : 2 ≤ n) (β t : ℝ) :
    Real.exp (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N)) * AnisoTorus.ZA N β 0 n
      ≤ AnisoTorus.ZA N β t n := by
  set M : ℝ := 8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N with hM
  have hZne := (ZA_pos (N := N) β 0 n).ne'
  have hnum : mixNum N β 0 n = M * AnisoTorus.ZA N β 0 n := by
    rw [hM, ← meanMix_zero (N := N) hn β]
    unfold meanMix
    rw [div_mul_cancel₀ _ hZne]
  have hZ0 : AnisoTorus.ZA N β 0 n = ∫ U, Real.exp (-(β * sinR N n U)) ∂piH N n := by
    rw [ZA_eq_int]; simp only [zero_mul, add_zero]
  have hnum' : ∫ U, smixR N n U * Real.exp (-(β * sinR N n U)) ∂piH N n = M * AnisoTorus.ZA N β 0 n := by
    rw [← hnum]
    unfold mixNum
    simp only [zero_mul, add_zero]
  have hE : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hSE : Continuous fun U : Lk n → SUN.SU N => smixR N n U * Real.exp (-(β * sinR N n U)) :=
    (continuous_smixR n).mul hE
  have hpt : ∀ U : Lk n → SUN.SU N,
      Real.exp (-t * M) * ((1 + t * M) * Real.exp (-(β * sinR N n U))
          - t * (smixR N n U * Real.exp (-(β * sinR N n U))))
        ≤ Real.exp (-(β * sinR N n U + t * smixR N n U)) := by
    intro U
    have h1 := Real.add_one_le_exp (-t * (smixR N n U - M))
    have e : Real.exp (-(β * sinR N n U + t * smixR N n U))
        = Real.exp (-t * M) * (Real.exp (-t * (smixR N n U - M)) * Real.exp (-(β * sinR N n U))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(β * sinR N n U))).le
    calc _ = (-t * (smixR N n U - M) + 1) * Real.exp (-(β * sinR N n U)) := by ring
      _ ≤ _ := h2
  have hc0 : Continuous fun U : Lk n → SUN.SU N => (1 + t * M) * Real.exp (-(β * sinR N n U)) :=
    continuous_const.mul hE
  have hc3 : Continuous fun U : Lk n → SUN.SU N => t * (smixR N n U * Real.exp (-(β * sinR N n U))) :=
    continuous_const.mul hSE
  have hc1 : Continuous fun U : Lk n → SUN.SU N =>
      Real.exp (-t * M) * ((1 + t * M) * Real.exp (-(β * sinR N n U))
          - t * (smixR N n U * Real.exp (-(β * sinR N n U)))) :=
    continuous_const.mul (hc0.sub hc3)
  have hc2 : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U + t * smixR N n U)) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (continuous_sinR n)).add (continuous_const.mul (continuous_smixR n))).neg
  have hmono := integral_mono (μ := piH N n) (hint hc1) (hint hc2) hpt
  rw [integral_const_mul, integral_sub (hint hc0) (hint hc3),
    integral_const_mul, integral_const_mul, ← hZ0, hnum', ← ZA_eq_int β t n] at hmono
  calc Real.exp (-t * M) * AnisoTorus.ZA N β 0 n
      = Real.exp (-t * M) * ((1 + t * M) * AnisoTorus.ZA N β 0 n
          - t * (M * AnisoTorus.ZA N β 0 n)) := by ring
    _ ≤ _ := hmono

/-- **The window defect across the mixed coupling**: `DA(β, t, w) ≤ DA(β, 0, w) + 8192 · 16^w t²`, for every
`β`, `t` and window `w ≥ 1`, uniformly in `N ≠ 0`. The bulk term `−t⟨S⟩₀` cancels between `16 log Z_n` and
`log Z_{2n}`. The bound is extensive: `n⁴`, not the `n⁸` of the trivial range. DERIVED: `8192 = 16 · 512` the
copies times the colour constant; `16` the copies; `2` the doubling and the least extent; `1` the least window;
`0` the decoupled end. -/
theorem DA_le (hN : N ≠ 0) (β t : ℝ) {w : ℕ} (hw : 1 ≤ w) :
    AnisoTorus.DA N β t w ≤ AnisoTorus.DA N β 0 w + 8192 * ((4 : ℝ) ^ w) ^ 2 * t ^ 2 := by
  have hn1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have hn2 : 2 ≤ 2 ^ (w + 1) := DeltaLengthTower.two_le_two_pow (by omega)
  have hu := ZA_le (N := N) hN hn1 (two_pow_mod hw) β t
  have hl := ZA_ge (N := N) hn2 β t
  have h1 : AnisoTorus.logZA N β t (2 ^ w)
      ≤ (-t * (8 * ((2 ^ w : ℕ) : ℝ) ^ 4 * WindowRead.haarMeanN N)
          + 512 * ((2 ^ w : ℕ) : ℝ) ^ 4 * t ^ 2) + AnisoTorus.logZA N β 0 (2 ^ w) := by
    unfold AnisoTorus.logZA
    have := Real.log_le_log (ZA_pos (N := N) β t (2 ^ w)) hu
    rwa [Real.log_mul (Real.exp_pos _).ne' (ZA_pos (N := N) β 0 _).ne', Real.log_exp] at this
  have h2 : -t * (8 * ((2 ^ (w + 1) : ℕ) : ℝ) ^ 4 * WindowRead.haarMeanN N)
        + AnisoTorus.logZA N β 0 (2 ^ (w + 1)) ≤ AnisoTorus.logZA N β t (2 ^ (w + 1)) := by
    unfold AnisoTorus.logZA
    have := Real.log_le_log (mul_pos (Real.exp_pos _) (ZA_pos (N := N) β 0 _)) hl
    rwa [Real.log_mul (Real.exp_pos _).ne' (ZA_pos (N := N) β 0 _).ne', Real.log_exp] at this
  have e4 : (4 : ℝ) ^ w = (2 ^ w) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  unfold AnisoTorus.DA
  rw [e4]
  push_cast at h1 h2
  rw [pow_succ] at h2
  linear_combination 16 * h1 + h2

/-! ## 5. The strip from one seed window -/

/-- **One decoupled seed window opens a strip**: `DA(β, 0, w) ≤ 1/2000` gives `DA(β, t, ·) → 0` for every
`0 ≤ t ≤ 1/(4048 · 4^w)`. COMPUTED: `4048² · 1/2000 ≥ 8192`, so the mixed term is at most `1/2000`. Inherited:
`1/1000` the basin of `MixAnchor.tendsto_DA_of_seed`, of which `1/2000` is the half left to each side. DERIVED:
`0` the limit and the decoupled end; `1` the least window; `1/2000` the half of the seed `1/1000` left to
the decoupled term (CHOSEN, module docstring); `4048` the least integer with `4048² ≥ 8192 · 2000 = 16384000`. -/
theorem strip_of_seed (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {w : ℕ} (hw : 1 ≤ w)
    (hs : AnisoTorus.DA N β 0 w ≤ 1 / 2000) (htw : t ≤ 1 / (4048 * (4 : ℝ) ^ w)) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) := by
  refine MixAnchor.tendsto_DA_of_seed hN hβ ht hw ?_
  have hpos : (0 : ℝ) < (4 : ℝ) ^ w := by positivity
  have h1 : (4 : ℝ) ^ w * t ≤ 1 / 4048 := by
    rw [le_div_iff₀ (by positivity)] at htw
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have h2 : ((4 : ℝ) ^ w * t) ^ 2 ≤ (1 / 4048) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hpos.le ht) h1 2
  have := DA_le hN β t hw
  nlinarith

/-! ## 6. The decoupled seed from the 2D ratio -/

/-- **The decoupled window defect in the 2D ratio**: `DA(β, 0, w) = 8 n² (4 log ρ(n) − log ρ(2n))`, `n = 2^w`,
`ρ = TwoDVanish.ratio`; the bulk cancels. DERIVED: `8` from `LayerSplit.layerDefect_eq`; `4 = 2²` the copies; `2`
the doubling and the least extent; `1` the least window. -/
theorem DA_zero_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    AnisoTorus.DA N β 0 w = 8 * ((4 : ℝ) ^ w)
      * (4 * Real.log (TwoDVanish.ratio N β (2 ^ w)) - Real.log (TwoDVanish.ratio N β (2 * 2 ^ w))) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hlog : ∀ m : ℕ, 2 ≤ m → LayerSplit.logZ2 N β m
      = (m : ℝ) ^ 2 * Real.log (TwoDVanish.bk N β) + Real.log (TwoDVanish.ratio N β m) := by
    intro m hm
    have hZ := TwoDVanish.ZT_pos hN hm hβ (N := N)
    unfold LayerSplit.logZ2 TwoDVanish.ratio
    rw [Real.log_div hZ.ne' (pow_pos hb _).ne', Real.log_pow]
    push_cast
    ring
  have hn1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have e4 : (4 : ℝ) ^ w = (2 ^ w) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [AnisoTorus.DA_decoupled (DecoupledSplit.decoupledFactor N β) w, LayerSplit.layerDefect_eq]
  unfold LayerSplit.D2
  rw [hlog _ hn1, hlog _ (by omega), e4]
  push_cast
  ring

/-- **A small ratio is a seed**: `|ρ(n) − 1|, |ρ(2n) − 1| ≤ E ≤ 1/2` and `48 · 4^w E ≤ 1/2000` give
`DA(β, 0, w) ≤ 1/2000`. DERIVED: `48 = 8 · (4 + 2)`, the prefactor of `DA_zero_eq` times `log ρ ≤ ρ − 1` on `n`
and `|log ρ| ≤ 2 |ρ − 1|` on `2n`; `1/2` the range of `LayerSplit.abs_log_one_add_le`; `1/2000` as in
`strip_of_seed`. -/
theorem seed_of_ratio (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) {E : ℝ} (hE : E ≤ 1 / 2)
    (h1 : |TwoDVanish.ratio N β (2 ^ w) - 1| ≤ E) (h2 : |TwoDVanish.ratio N β (2 * 2 ^ w) - 1| ≤ E)
    (hs : 48 * (4 : ℝ) ^ w * E ≤ 1 / 2000) : AnisoTorus.DA N β 0 w ≤ 1 / 2000 := by
  rw [DA_zero_eq hN hβ hw]
  have hp : (0 : ℝ) < (4 : ℝ) ^ w := by positivity
  have hb1 := abs_le.1 h1
  have hpos : 0 < TwoDVanish.ratio N β (2 ^ w) := by linarith [hb1.1]
  have hup : Real.log (TwoDVanish.ratio N β (2 ^ w)) ≤ E := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith [hb1.2]
  have hl := LayerSplit.abs_log_one_add_le (h2.trans hE)
  rw [add_sub_cancel] at hl
  have hlo : -Real.log (TwoDVanish.ratio N β (2 * 2 ^ w)) ≤ 2 * E := by
    have := neg_le_abs (Real.log (TwoDVanish.ratio N β (2 * 2 ^ w)))
    linarith
  have hE' : 4 * Real.log (TwoDVanish.ratio N β (2 ^ w)) - Real.log (TwoDVanish.ratio N β (2 * 2 ^ w))
      ≤ 6 * E := by linarith
  calc 8 * (4 : ℝ) ^ w * (4 * Real.log (TwoDVanish.ratio N β (2 ^ w))
        - Real.log (TwoDVanish.ratio N β (2 * 2 ^ w)))
      ≤ 8 * (4 : ℝ) ^ w * (6 * E) := mul_le_mul_of_nonneg_left hE' (by positivity)
    _ = 48 * (4 : ℝ) ^ w * E := by ring
    _ ≤ 1 / 2000 := hs

/-! ## 7. The floor: the proved 2D coherence area -/

/-- **The coherence area of the floor** `L = b / e^{−4β}`, so `q = c/b = 1 − 1/L` in `TwoDVanish`. No numeral. -/
noncomputable def cohArea (N : ℕ) (β : ℝ) : ℝ := TwoDVanish.bk N β / TwoDVanish.fl β

theorem bk_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : TwoDVanish.bk N β ≤ 1 := by
  have hle : ∀ g : SUN.SU N, TwoDVanish.sw β g ≤ 1 - TwoDVanish.fl β := by
    intro g
    unfold TwoDVanish.sw TwoDVanish.wt
    have h1 := WilsonAction.wilsonDensity_nonneg hN g
    have h2 := WilsonAction.wilsonDensity_nonneg hN g⁻¹
    have : Real.exp (-β * (WilsonAction.wilsonDensity g + WilsonAction.wilsonDensity g⁻¹)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    linarith
  have hint' : Integrable (TwoDVanish.sw (N := N) β) (probHaar (SUN.SU N)) :=
    (TwoDVanish.continuous_sw β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hint' (integrable_const (1 - TwoDVanish.fl β)) hle
  rw [ContactFloor.integral_const_prob] at h
  unfold TwoDVanish.bk
  have : TwoDVanish.cm N β ≤ 1 - TwoDVanish.fl β := h
  linarith

theorem cm_le_one (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : TwoDVanish.cm N β ≤ 1 := by
  have := bk_le_one hN hβ
  unfold TwoDVanish.bk at this
  linarith [TwoDVanish.fl_pos β]

theorem fl_le_bk (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : TwoDVanish.fl β ≤ TwoDVanish.bk N β := by
  unfold TwoDVanish.bk
  linarith [TwoDVanish.cm_nonneg hN hβ]

theorem one_le_cohArea (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : 1 ≤ cohArea N β := by
  unfold cohArea
  rw [one_le_div (TwoDVanish.fl_pos β)]
  exact fl_le_bk hN hβ

/-- `L ≤ e^{4β}`. DERIVED: `4` the floor exponent. -/
theorem cohArea_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : cohArea N β ≤ Real.exp (4 * β) := by
  unfold cohArea
  rw [div_le_iff₀ (TwoDVanish.fl_pos β)]
  have e : Real.exp (4 * β) * TwoDVanish.fl β = 1 := by
    unfold TwoDVanish.fl
    rw [← Real.exp_add, show 4 * β + -β * 4 = 0 by ring, Real.exp_zero]
  rw [e]
  exact bk_le_one hN hβ

/-- **The floor as a decay**: `|ρ(m) − 1| ≤ 2 e^{4β} e^{−(m² − 1)/L}` for `m ≥ 2`. DERIVED: `2` from `1 + c ≤ 2` and
the least side; `4` the floor exponent; `1` the dropped face. -/
theorem ratio_floor (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {m : ℕ} (hm : 2 ≤ m) :
    |TwoDVanish.ratio N β m - 1|
      ≤ 2 * Real.exp (4 * β) * Real.exp (-(((m : ℝ) ^ 2 - 1) / cohArea N β)) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hc := TwoDVanish.cm_nonneg hN hβ
  have hc1 := cm_le_one hN hβ
  have hL := one_le_cohArea hN hβ
  have hLpos : 0 < cohArea N β := by linarith
  have hq : TwoDVanish.cm N β / TwoDVanish.bk N β = 1 - 1 / cohArea N β := by
    have hb' := hb.ne'
    unfold cohArea
    rw [one_div_div, eq_sub_iff_add_eq, ← add_div]
    exact div_self hb'
  have hq0 : 0 ≤ TwoDVanish.cm N β / TwoDVanish.bk N β := div_nonneg hc hb.le
  have hqe : TwoDVanish.cm N β / TwoDVanish.bk N β ≤ Real.exp (-(1 / cohArea N β)) := by
    rw [hq]
    linarith [Real.add_one_le_exp (-(1 / cohArea N β))]
  have hk : (((m ^ 2 - 1 : ℕ) : ℝ)) = (m : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    ring
  have hpow : (TwoDVanish.cm N β / TwoDVanish.bk N β) ^ (m ^ 2 - 1)
      ≤ Real.exp (-(((m : ℝ) ^ 2 - 1) / cohArea N β)) := by
    calc _ ≤ Real.exp (-(1 / cohArea N β)) ^ (m ^ 2 - 1) := pow_le_pow_left₀ hq0 hqe _
      _ = _ := by
        rw [← Real.exp_nat_mul, hk]
        congr 1
        ring
  have hpre : (1 + TwoDVanish.cm N β) / TwoDVanish.bk N β ≤ 2 * Real.exp (4 * β) := by
    rw [div_le_iff₀ hb]
    have h1 : 1 ≤ Real.exp (4 * β) * TwoDVanish.bk N β := by
      have e : Real.exp (4 * β) * TwoDVanish.fl β = 1 := by
        unfold TwoDVanish.fl
        rw [← Real.exp_add, show 4 * β + -β * 4 = 0 by ring, Real.exp_zero]
      rw [← e]
      exact mul_le_mul_of_nonneg_left (fl_le_bk hN hβ) (Real.exp_pos _).le
    nlinarith
  have h := TwoDVanish.abs_ratio_sub_one_le hN hm hβ (N := N)
  unfold TwoDVanish.ratio
  refine h.trans ?_
  exact mul_le_mul hpre hpow (pow_nonneg hq0 _) (by positivity)

/-! ## 8. A window for a target area -/

/-- A power of four within a factor four of any target `A > 1`. DERIVED: `4 = 2²` the area of the doubling;
`1` the least window. -/
theorem exists_window {A : ℝ} (hA : 1 < A) : ∃ w : ℕ, 1 ≤ w ∧ A ≤ (4 : ℝ) ^ w ∧ (4 : ℝ) ^ w ≤ 4 * A := by
  have h4 : (1 : ℝ) < 4 := by norm_num
  have hx : 0 < Real.logb 4 A := Real.logb_pos h4 hA
  have hApos : 0 < A := by linarith
  refine ⟨⌈Real.logb 4 A⌉₊, Nat.ceil_pos.2 hx, ?_, ?_⟩
  · calc A = (4 : ℝ) ^ Real.logb 4 A := (Real.rpow_logb (by norm_num) h4.ne' hApos).symm
      _ ≤ (4 : ℝ) ^ (⌈Real.logb 4 A⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h4.le (Nat.le_ceil _)
      _ = _ := Real.rpow_natCast _ _
  · have hc : (⌈Real.logb 4 A⌉₊ : ℝ) ≤ Real.logb 4 A + 1 := (Nat.ceil_lt_add_one hx.le).le
    calc (4 : ℝ) ^ ⌈Real.logb 4 A⌉₊ = (4 : ℝ) ^ (⌈Real.logb 4 A⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (4 : ℝ) ^ (Real.logb 4 A + 1) := Real.rpow_le_rpow_of_exponent_le h4.le hc
      _ = 4 * A := by
        rw [Real.rpow_add_one (by norm_num), Real.rpow_logb (by norm_num) h4.ne' hApos]
        ring

/-- The numerical bound behind the floor seed. COMPUTED: `e^{13} ≥ 2.7^{13} ≥ 384000`. -/
theorem exp_thirteen : (384000 : ℝ) ≤ Real.exp 13 := by
  have h : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have e : Real.exp 13 = Real.exp 1 ^ 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  calc (384000 : ℝ) ≤ 2.7 ^ 13 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h.le _

/-- **The seed area of the floor** `A(β) = 1 + L (16 β + 26)`. DERIVED: `16 = 2 · 8` and `26 = 2 · 13` read off
`192 e^{8β − y/2} ≤ 1/2000` with `e^{13} ≥ 384000`. -/
noncomputable def seedArea (N : ℕ) (β : ℝ) : ℝ := 1 + cohArea N β * (16 * β + 26)

/-- **The floor seeds at area `A(β)`**: a window with `4^w ≥ A(β)` has `DA(β, 0, w) ≤ 1/2000`. The exponent
`y = (n² − 1)/L ≥ 16 β + 26` gives `n² ≤ (1 + y) L ≤ 2 e^{y/2} e^{4β}`, so `48 n² E ≤ 192 e^{8β − y/2}`. DERIVED: as
in `seedArea`; `2` the doubling and `1 + x ≤ e^x`; `1/2000` the seed half of `strip_of_seed`. -/
theorem seed_floor (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (hA : seedArea N β ≤ (4 : ℝ) ^ w) :
    AnisoTorus.DA N β 0 w ≤ 1 / 2000 := by
  have hL := one_le_cohArea hN hβ
  have hLpos : 0 < cohArea N β := by linarith
  have hL2 := cohArea_le hN hβ
  have hn1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have hn2 : 2 ≤ 2 * 2 ^ w := by omega
  set a : ℝ := (4 : ℝ) ^ w with ha
  have e4 : a = (((2 ^ w : ℕ) : ℝ)) ^ 2 := by
    rw [ha]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e8 : (((2 * 2 ^ w : ℕ) : ℝ)) ^ 2 = 4 * a := by
    rw [e4]; push_cast; ring
  have ha1 : 1 ≤ a := by rw [ha]; exact one_le_pow₀ (by norm_num)
  set y : ℝ := (a - 1) / cohArea N β with hy
  have hy0 : 16 * β + 26 ≤ y := by
    rw [hy, le_div_iff₀ hLpos]
    unfold seedArea at hA
    nlinarith
  have hE1 : |TwoDVanish.ratio N β (2 ^ w) - 1| ≤ 2 * Real.exp (4 * β) * Real.exp (-y) := by
    have := ratio_floor hN hβ hn1
    rwa [← e4] at this
  have hE2 : |TwoDVanish.ratio N β (2 * 2 ^ w) - 1| ≤ 2 * Real.exp (4 * β) * Real.exp (-y) := by
    have h := ratio_floor hN hβ hn2
    rw [e8] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Real.exp_le_exp, neg_le_neg_iff, hy]
    exact div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hexp : Real.exp (8 * β) * Real.exp (-(y / 2)) ≤ 1 / 384000 := by
    rw [← Real.exp_add]
    have h13 : Real.exp (8 * β + -(y / 2)) ≤ Real.exp (-13) :=
      Real.exp_le_exp.2 (by linarith)
    refine h13.trans ?_
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_thirteen
  have hsplit : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcosh : y + 1 ≤ 2 * Real.exp (y / 2) := by
    linarith [Real.add_one_le_exp (y / 2)]
  have ha2 : a ≤ (y + 1) * Real.exp (4 * β) := by
    have h1 : a = y * cohArea N β + 1 := by rw [hy, div_mul_cancel₀ _ hLpos.ne']; ring
    have h2 : y * cohArea N β + 1 ≤ (y + 1) * cohArea N β := by nlinarith
    have hy1 : 0 ≤ y + 1 := by nlinarith
    calc a = y * cohArea N β + 1 := h1
      _ ≤ (y + 1) * cohArea N β := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 hy1
  have hexp2 : 2 * Real.exp (4 * β) * Real.exp (-y) ≤ 1 / 2 := by
    have h0 : Real.exp (-(y / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have h4 : Real.exp (4 * β) * Real.exp (-(y / 2)) ≤ Real.exp (8 * β) * Real.exp (-(y / 2)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
    rw [hsplit]
    have hp1 := Real.exp_pos (-(y / 2))
    nlinarith
  refine seed_of_ratio hN hβ hw hexp2 hE1 hE2 ?_
  have hA2 : a * Real.exp (-(y / 2)) ≤ 2 * Real.exp (4 * β) := by
    calc a * Real.exp (-(y / 2)) ≤ (y + 1) * Real.exp (4 * β) * Real.exp (-(y / 2)) :=
          mul_le_mul_of_nonneg_right ha2 (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (y / 2) * Real.exp (4 * β) * Real.exp (-(y / 2)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcosh (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = 2 * Real.exp (4 * β) := by
          have : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination 2 * Real.exp (4 * β) * this
  have he8 : Real.exp (4 * β) * Real.exp (4 * β) = Real.exp (8 * β) := by
    rw [← Real.exp_add]; congr 1; ring
  calc 48 * a * (2 * Real.exp (4 * β) * Real.exp (-y))
      = 96 * (a * Real.exp (-(y / 2))) * Real.exp (4 * β) * Real.exp (-(y / 2)) := by
        rw [hsplit]; ring
    _ ≤ 96 * (2 * Real.exp (4 * β)) * Real.exp (4 * β) * Real.exp (-(y / 2)) := by
        have hp : 0 ≤ Real.exp (4 * β) * Real.exp (-(y / 2)) := by positivity
        nlinarith
    _ = 192 * (Real.exp (8 * β) * Real.exp (-(y / 2))) := by rw [← he8]; ring
    _ ≤ 192 * (1 / 384000) := by linarith
    _ = 1 / 2000 := by norm_num

/-- **The proved width**, in the coherence area: `t*(N, β) = 1/(16192 A(β))`. COMPUTED: `16192 = 4 · 4048`, the
window loss of `exists_window` times the constant of `strip_of_seed`. DERIVED: `4048` the constant of
`strip_of_seed`; `4` the window loss of `exists_window` (CHOSEN, module docstring). -/
noncomputable def tStar (N : ℕ) (β : ℝ) : ℝ := 1 / (16192 * seedArea N β)

/-- **The width in closed form**: `t_low(β) = e^{−4β} / (16192 (16 β + 27))`, for every `N`. DERIVED: `4` the
floor; `27 = 26 + 1`. COMPUTED: `16192`. -/
noncomputable def tLow (β : ℝ) : ℝ := Real.exp (-(4 * β)) / (16192 * (16 * β + 27))

theorem seedArea_gt (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : 1 < seedArea N β := by
  have := one_le_cohArea (N := N) hN hβ
  unfold seedArea
  nlinarith

theorem tLow_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < tLow β := by
  unfold tLow; positivity

theorem tLow_le_tStar (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) : tLow β ≤ tStar N β := by
  have hA := seedArea_gt (N := N) hN hβ
  have hL2 := cohArea_le (N := N) hN hβ
  have he : 1 ≤ Real.exp (4 * β) := Real.one_le_exp (by linarith)
  have hAle : seedArea N β ≤ Real.exp (4 * β) * (16 * β + 27) := by
    unfold seedArea
    nlinarith
  have hAp : 0 < seedArea N β := by linarith
  have e : tLow β = 1 / (16192 * (Real.exp (4 * β) * (16 * β + 27))) := by
    unfold tLow
    rw [Real.exp_neg, inv_eq_one_div, div_div]
    congr 1
    ring
  rw [e]
  unfold tStar
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The strip, with the coherence area**: `t ≤ t*(N, β)` gives `DA(β, t, ·) → 0`, for every `N ≠ 0`, `β ≥ 0`.
DERIVED: `0` the limit. COMPUTED: as in `tStar`. -/
theorem strip_width_area (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ tStar N β) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) := by
  have hA := seedArea_gt (N := N) hN hβ
  obtain ⟨w, hw, h1, h2⟩ := exists_window hA
  refine strip_of_seed hN hβ ht hw (seed_floor hN hβ hw h1) (hts.trans ?_)
  unfold tStar
  have hp : (0 : ℝ) < (4 : ℝ) ^ w := by positivity
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **`strip_width`: the explicit strip.** For every `N ≠ 0` and `β ≥ 0`, `t_low(β) > 0` and
`DA(β, t, ·) → 0` along the windows for every `t ∈ [0, t_low(β))`, with
`t_low(β) = e^{−4β} / (16192 (16 β + 27))`. DERIVED: `0` the decoupled end and the limit. COMPUTED: as in
`tLow`. -/
theorem strip_width (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    0 < tLow β ∧ ∀ t : ℝ, 0 ≤ t → t < tLow β → Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) :=
  ⟨tLow_pos hβ, fun _ ht hts =>
    strip_width_area hN hβ ht (hts.le.trans (tLow_le_tStar hN hβ))⟩

/-! ## 9. The polynomial strip: the seed from the spectral gap of the plaquette walk -/

open MassGap.StripGap (gapArea Fk_equil) in
/-- **The ratio from the walk**: if `1/b ≤ e^L` and `m η ≤ 1/2` with `η = e^{−(m − 2)/(2ℓ)} e^L`, then
`|ρ(m) − 1| ≤ 2 m η`. `StripRow.ratio_row` with the sup bound `StripGap.Fk_equil`. DERIVED: `2` the least side and
the slope in `e^x ≤ 1 + 2x` on `[0, 1/2]`. -/
theorem ratio_walk (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L)
    {m : ℕ} (hm : 2 ≤ m)
    (hsmall : (m : ℝ) * (Real.exp (-(((m : ℝ) - 2) / (2 * gapArea N β))) * Real.exp L) ≤ 1 / 2) :
    |TwoDVanish.ratio N β m - 1|
      ≤ 2 * ((m : ℝ) * (Real.exp (-(((m : ℝ) - 2) / (2 * gapArea N β))) * Real.exp L)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  set η : ℝ := Real.exp (-((((j + 2 : ℕ) : ℝ) - 2) / (2 * gapArea N β))) * Real.exp L with hη
  have hη0 : 0 ≤ η := by positivity
  have hm1 : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hη2 : η ≤ 1 / 2 := by nlinarith
  have hb : ∀ x, |StripGap.Fk (StripGap.pW N β) (j + 1) x - 1| ≤ η := by
    intro x
    refine (Fk_equil hN hβ j x).trans ?_
    have e : (((j + 2 : ℕ) : ℝ) - 2) = (j : ℝ) := by push_cast; ring
    rw [hη, e]
    exact mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
  obtain ⟨h1, h2⟩ := StripRow.ratio_row (m := j + 1) hN hβ (by linarith) hb
  set n : ℝ := ((j + 2 : ℕ) : ℝ) with hn
  set x : ℝ := n * η with hx
  have hx0 : 0 ≤ x := by positivity
  have hup : (1 + η) ^ (j + 2) ≤ 1 + 2 * x := by
    have h3 : (1 + η) ^ (j + 2) ≤ Real.exp η ^ (j + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp η]) _
    rw [← Real.exp_nat_mul] at h3
    refine h3.trans ?_
    have h4 := Real.add_one_le_exp (-x)
    have h5 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have h6 : 0 < 1 - x := by linarith
    have h7 : Real.exp x * (1 - x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (show -x + 1 ≤ Real.exp (-x) from h4) (Real.exp_pos x).le
      nlinarith
    have h8 : Real.exp x ≤ 1 / (1 - x) := by
      rw [le_div_iff₀ h6]; exact h7
    refine h8.trans ?_
    rw [div_le_iff₀ h6]
    nlinarith
  have hlo : 1 - x ≤ (1 - η) ^ (j + 2) := by
    have := one_add_mul_le_pow (a := -η) (by linarith) (j + 2)
    have e : (1 : ℝ) + -η = 1 - η := by ring
    rw [e] at this
    calc 1 - x = 1 + ((j + 2 : ℕ) : ℝ) * -η := by rw [hx, hn]; ring
      _ ≤ _ := this
  rw [abs_le]
  constructor <;> linarith

/-- The side of the seed window `n₀ = 2 + 2 ℓ (2 L + 41 + 6 log ℓ)`. DERIVED: `2`, `6` read off
`192 n³ η ≤ 1/2000`, with `n ≤ 2 ℓ (1 + y)`, `(1 + y)³ ≤ 216 e^{y/2}`; COMPUTED: `41 = 2 · 20.5`,
`e^{20.5} ≥ 663552000 = 2 · 192 · 8 · 216 · 2000 / 2`. -/
noncomputable def seedSide (ℓ L : ℝ) : ℝ := 2 + 2 * ℓ * (2 * L + 41 + 6 * Real.log ℓ)

theorem exp_twenty : (663552000 : ℝ) ≤ Real.exp (41 / 2) := by
  have h : (2.718 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have e : Real.exp (41 / 2) ^ 2 = Real.exp 1 ^ 41 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h2 : (663552000 : ℝ) ^ 2 ≤ Real.exp (41 / 2) ^ 2 := by
    rw [e]
    calc (663552000 : ℝ) ^ 2 ≤ 2.718 ^ 41 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h.le _
  exact (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le two_ne_zero).1 h2

open MassGap.StripGap (gapArea gapArea_ge) in
/-- **The walk seeds at side `n₀`**: if `1/b ≤ e^L`, `L ≥ 0`, and `2^w ≥ n₀`, then `DA(β, 0, w) ≤ 1/2000`. DERIVED:
as in `seedSide`; `4 n η` the error on `n` and `2n` together; `1/2000` the seed half of `strip_of_seed`. -/
theorem seed_walk (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L) {w : ℕ} (hw : 1 ≤ w)
    (hA : seedSide (gapArea N β) L ≤ (2 : ℝ) ^ w) : AnisoTorus.DA N β 0 w ≤ 1 / 2000 := by
  set l : ℝ := gapArea N β with hl
  have hl240 : (240 : ℝ) ≤ l := gapArea_ge β hβ
  have hlpos : 0 < l := by linarith
  have hlog : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
  set n : ℝ := (2 : ℝ) ^ w with hn
  have hn2 : (2 : ℝ) ≤ n := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hw
    simpa [hn] using this
  set y : ℝ := (n - 2) / (2 * l) with hy
  have hy0 : 2 * L + 41 + 6 * Real.log l ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    unfold seedSide at hA
    nlinarith
  have hypos : 0 ≤ y := by linarith
  set η : ℝ := Real.exp (-y) * Real.exp L with hη
  have hn0 : n = 2 + 2 * l * y := by rw [hy]; field_simp; ring
  have hnl : n ≤ 2 * l * (1 + y) := by rw [hn0]; nlinarith
  have hc1 : 1 + y ≤ 6 * Real.exp (y / 6) := by linarith [Real.add_one_le_exp (y / 6)]
  have hc3 : (1 + y) ^ 3 ≤ 216 * Real.exp (y / 2) := by
    have h1 : (1 + y) ^ 3 ≤ (6 * Real.exp (y / 6)) ^ 3 := pow_le_pow_left₀ (by linarith) hc1 3
    have e : (6 * Real.exp (y / 6)) ^ 3 = 216 * Real.exp (y / 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    rwa [e] at h1
  have hn3 : n ^ 3 ≤ 1728 * l ^ 3 * Real.exp (y / 2) := by
    have h1 : n ^ 3 ≤ (2 * l * (1 + y)) ^ 3 := pow_le_pow_left₀ (by linarith) hnl 3
    have e : (2 * l * (1 + y)) ^ 3 = 8 * l ^ 3 * (1 + y) ^ 3 := by ring
    rw [e] at h1
    have h2 := mul_le_mul_of_nonneg_left hc3 (by positivity : 0 ≤ 8 * l ^ 3)
    nlinarith
  have hlexp : l ^ 3 = Real.exp (3 * Real.log l) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hlpos]
    norm_cast
  have hdecay : l ^ 3 * Real.exp (y / 2) * η ≤ 1 / 663552000 := by
    have e : l ^ 3 * Real.exp (y / 2) * η = Real.exp (3 * Real.log l + y / 2 + -y + L) := by
      rw [hη, hlexp, Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    rw [e]
    have h1 : Real.exp (3 * Real.log l + y / 2 + -y + L) ≤ Real.exp (-(41 / 2)) :=
      Real.exp_le_exp.2 (by linarith)
    refine h1.trans ?_
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_twenty
  have hmain : n ^ 3 * η ≤ 1 / 384000 := by
    have hηp : 0 ≤ η := by positivity
    have h1 := mul_le_mul_of_nonneg_right hn3 hηp
    calc n ^ 3 * η ≤ 1728 * l ^ 3 * Real.exp (y / 2) * η := h1
      _ = 1728 * (l ^ 3 * Real.exp (y / 2) * η) := by ring
      _ ≤ 1728 * (1 / 663552000) := by linarith
      _ = 1 / 384000 := by norm_num
  have hηp : 0 ≤ η := by positivity
  have hnη : n * η ≤ 1 / 384000 := by
    have h1 : n ≤ n ^ 3 := by nlinarith [sq_nonneg (n - 1)]
    exact (mul_le_mul_of_nonneg_right h1 hηp).trans hmain
  have hcn : ((2 ^ w : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hcn2 : ((2 * 2 ^ w : ℕ) : ℝ) = 2 * n := by rw [hn]; push_cast; ring
  have hn1 : 2 ≤ 2 ^ w := DeltaLengthTower.two_le_two_pow hw
  have hη2n : Real.exp (-((2 * n - 2) / (2 * l))) * Real.exp L ≤ η := by
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    rw [neg_le_neg_iff, hy]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h1 : |TwoDVanish.ratio N β (2 ^ w) - 1| ≤ 2 * (n * η) := by
    have := ratio_walk hN hβ hL hn1 (by rw [hcn]; show n * η ≤ 1 / 2; linarith)
    rw [hcn] at this
    exact this
  have h2n : 2 * n * (Real.exp (-((2 * n - 2) / (2 * l))) * Real.exp L) ≤ 2 * (n * η) := by
    have := mul_le_mul_of_nonneg_left hη2n (by positivity : 0 ≤ 2 * n)
    linarith
  have h2 : |TwoDVanish.ratio N β (2 * 2 ^ w) - 1| ≤ 2 * (2 * (n * η)) := by
    have := ratio_walk hN hβ hL (show 2 ≤ 2 * 2 ^ w by omega)
      (by rw [hcn2]; show 2 * n * (Real.exp (-((2 * n - 2) / (2 * l))) * Real.exp L) ≤ 1 / 2; linarith)
    rw [hcn2] at this
    refine this.trans ?_
    linarith
  have e4 : (4 : ℝ) ^ w = n ^ 2 := by
    rw [hn, ← pow_mul, mul_comm, pow_mul]; norm_num
  refine seed_of_ratio hN hβ hw (E := 4 * (n * η)) (by linarith)
    (by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) hηp]) (by linarith) ?_
  rw [e4]
  have : 48 * n ^ 2 * (4 * (n * η)) = 192 * (n ^ 3 * η) := by ring
  rw [this]
  linarith

open MassGap.StripGap (gapArea gapArea_ge) in
/-- **The strip from a bulk bound**: `1/b ≤ e^L` gives `DA(β, t, ·) → 0` for `0 ≤ t ≤ 1/(16192 n₀²)`. COMPUTED:
`16192` as in `tStar`. DERIVED: `0` the limit; `16192 = 4 · 4048` as in `tStar`. -/
theorem strip_of_bulk (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : 1 / TwoDVanish.bk N β ≤ Real.exp L)
    (hts : t ≤ 1 / (16192 * seedSide (gapArea N β) L ^ 2)) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) := by
  set s : ℝ := seedSide (gapArea N β) L with hs
  have hl240 : (240 : ℝ) ≤ gapArea N β := gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (gapArea N β) := Real.log_nonneg (by linarith)
  have hs2 : 2 ≤ s := by
    rw [hs]
    unfold seedSide
    nlinarith
  have hA : 1 < s ^ 2 := by nlinarith
  obtain ⟨w, hw, h1, h2⟩ := exists_window hA
  have e4 : (4 : ℝ) ^ w = ((2 : ℝ) ^ w) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hside : s ≤ (2 : ℝ) ^ w := by
    rw [e4] at h1
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).1 h1
  refine strip_of_seed hN hβ ht hw (seed_walk hN hβ hL0 hL hw hside) (hts.trans ?_)
  have hp : (0 : ℝ) < (4 : ℝ) ^ w := by positivity
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

open MassGap.StripGap (binCount) in
/-- **The bulk exponent** `L(N, β) = 1 + 2 N² log K`, `K = binCount N β`. DERIVED: as in `StripGap.bk_ge`. -/
noncomputable def bulkExp (N : ℕ) (β : ℝ) : ℝ :=
  1 + ((N * (N * 2) : ℕ) : ℝ) * Real.log (binCount N β)

open MassGap.StripGap (binCount) in
theorem bulkExp_nonneg (β : ℝ) : 0 ≤ bulkExp N β := by
  unfold bulkExp
  have hK : (1 : ℝ) ≤ binCount N β := by
    unfold binCount
    push_cast
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (⌈2 * Real.sqrt (2 * (N : ℝ) * (β + 1))⌉₊ : ℝ))]
  have := Real.log_nonneg hK
  positivity

open MassGap.StripGap (binCount bk_ge) in
theorem one_div_bk_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    1 / TwoDVanish.bk N β ≤ Real.exp (bulkExp N β) := by
  have hb := TwoDVanish.bk_pos hN hβ
  have hK : (0 : ℝ) < binCount N β := by
    unfold binCount
    positivity
  rw [div_le_iff₀ hb]
  have e : Real.exp (bulkExp N β) = Real.exp 1 * (binCount N β : ℝ) ^ (N * (N * 2)) := by
    unfold bulkExp
    rw [Real.exp_add, mul_comm ((N * (N * 2) : ℕ) : ℝ), Real.exp_mul, Real.exp_log hK, Real.rpow_natCast]
  rw [e]
  exact bk_ge hN hβ

open MassGap.StripGap (gapArea) in
/-- **The polynomial width** `t_poly(N, β) = 1/(16192 n₀(N, β)²)`, `n₀ = 2 + 2 ℓ (2 L + 41 + 6 log ℓ)`,
`ℓ = 240 + 150 (N + 4) β`, `L = 1 + 2 N² log K`, `K = ⌈2 √(2 N (β + 1))⌉ + 1`. So `t_poly ≍ c_N⁻¹ (β log β)⁻²`. COMPUTED:
as in `seedSide`, `StripGap.gapArea`. DERIVED: `16192 = 4 · 4048` as in `tStar`; `41`, `6` as in
`seedSide`; Inherited: `240`, `150` from `StripGap.gapArea`. -/
noncomputable def tPoly (N : ℕ) (β : ℝ) : ℝ :=
  1 / (16192 * seedSide (gapArea N β) (bulkExp N β) ^ 2)

/-- **`strip_width_poly`: the strip shrinks only polynomially.** For every `N ≠ 0`, `β ≥ 0`, and `0 ≤ t ≤ t_poly(N, β)`,
`DA(β, t, ·) → 0` along the windows. DERIVED: `0` the limit. COMPUTED: as in `tPoly`. -/
theorem strip_width_poly (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ tPoly N β) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) :=
  strip_of_bulk hN hβ ht (bulkExp_nonneg β) (one_div_bk_le hN hβ) hts

theorem tPoly_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < tPoly N β := by
  have hl240 : (240 : ℝ) ≤ StripGap.gapArea N β := StripGap.gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (StripGap.gapArea N β) := Real.log_nonneg (by linarith)
  have hL := bulkExp_nonneg (N := N) β
  have hs : 0 < seedSide (StripGap.gapArea N β) (bulkExp N β) := by
    unfold seedSide
    nlinarith
  unfold tPoly
  positivity

/-- **`strip_width_max`: the larger of the two widths.** DERIVED: `0` the limit. -/
theorem strip_width_max (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t < max (tLow β) (tPoly N β)) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) := by
  rcases lt_max_iff.1 hts with h | h
  · exact (strip_width hN hβ).2 t ht h
  · exact strip_width_poly hN hβ ht h.le

/-- **The strip contains the diagonal at small `β`**: `DA(β, β, ·) → 0` for `0 ≤ β ≤ 1/500000`, for every `N ≠ 0`.
This quantifies `MixPlane.diag_anchor`. COMPUTED: `β · 16192 (16 β + 27) < e^{−4β}` on that interval. DERIVED: `0` the
limit. CHOSEN: `1/500000` a round value below the crossing near `β ≈ 1/(16192 · 27) ≈ 1/437000`; the cost is
a slightly shorter diagonal piece than the inequality allows. -/
theorem diag_small (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (hs : β ≤ 1 / 500000) :
    Tendsto (fun v => AnisoTorus.DA N β β v) atTop (𝓝 0) := by
  refine (strip_width hN hβ).2 β hβ ?_
  unfold tLow
  rw [lt_div_iff₀ (by positivity)]
  have h1 := Real.add_one_le_exp (-(4 * β))
  nlinarith

/-- **The method stops short of the diagonal**: `t_poly(N, β) ≤ 1/(16192 (300 (N + 4) β)² + 16192)`. So `t_poly/β → 0`.
DERIVED: `n₀ ≥ 2 ℓ + 2` and `2 L + 41 ≥ 1`; `300 = 2 · 150`; `16192 = 4 · 4048` as in `tStar`. -/
theorem tPoly_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    tPoly N β ≤ 1 / (16192 * (300 * ((N : ℝ) + 4) * β) ^ 2 + 16192) := by
  have hl240 : (240 : ℝ) ≤ StripGap.gapArea N β := StripGap.gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (StripGap.gapArea N β) := Real.log_nonneg (by linarith)
  have hL := bulkExp_nonneg (N := N) β
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set l := StripGap.gapArea N β with hl
  set X := 2 * bulkExp N β + 41 + 6 * Real.log l with hX
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hs : 2 * l ≤ seedSide l (bulkExp N β) - 2 := by
    unfold seedSide
    nlinarith
  have hl2 : 300 * ((N : ℝ) + 4) * β ≤ 2 * l := by
    rw [hl]
    unfold StripGap.gapArea
    nlinarith
  have hA : 300 * ((N : ℝ) + 4) * β + 2 ≤ seedSide l (bulkExp N β) := by linarith
  have hB : 0 ≤ 300 * ((N : ℝ) + 4) * β := by positivity
  have h2 : (300 * ((N : ℝ) + 4) * β) ^ 2 + 1 ≤ seedSide l (bulkExp N β) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hA 2
    nlinarith
  unfold tPoly
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

end MassGap.StripWidth

#print axioms MassGap.StripWidth.haarTilt_le
#print axioms MassGap.StripWidth.integral_family
#print axioms MassGap.StripWidth.smix_colours
#print axioms MassGap.StripWidth.ZA_le
#print axioms MassGap.StripWidth.ZA_ge
#print axioms MassGap.StripWidth.DA_le
#print axioms MassGap.StripWidth.strip_of_seed
#print axioms MassGap.StripWidth.seed_of_ratio
#print axioms MassGap.StripWidth.ratio_floor
#print axioms MassGap.StripWidth.seed_floor
#print axioms MassGap.StripWidth.strip_width_area
#print axioms MassGap.StripWidth.strip_width
#print axioms MassGap.StripWidth.ratio_walk
#print axioms MassGap.StripWidth.seed_walk
#print axioms MassGap.StripWidth.strip_of_bulk
#print axioms MassGap.StripWidth.one_div_bk_le
#print axioms MassGap.StripWidth.strip_width_poly
#print axioms MassGap.StripWidth.tPoly_pos
#print axioms MassGap.StripWidth.strip_width_max
#print axioms MassGap.StripWidth.diag_small
#print axioms MassGap.StripWidth.tPoly_le
