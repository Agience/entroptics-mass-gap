import Mathlib
import MassGap.StripGas

/-!
# MassGap.StripOsc — the site decomposition of `log Y(U)` is of order `t⁴`, with oscillation of order `t⁴`

`StripGas` writes `log Y(U) = Σ_x y_x(U)`, `Y(U) = ∫ da ∏_p (1 + g_p(gT a U))`, with `|y_x| ≤ 1` and a summand that
depends on an enumeration of the sites. This module uses the centring: a plaquette with a corner seen by no other
plaquette of a set integrates to zero, at every `U`. So activated sets have at least `4` plaquettes, every Kotecký–Preiss
weight carries `t⁴`, and the summand averaged over the enumerations is small, covariant and local. Declarations are in
`MassGap.StripOsc`.

## The result

For `0 < |t| ≤ t₂ = e^{−128}/16` (`tTwo`), `N ≠ 0`, `n ≥ 3` even, every `U`, with `Λ(t) = (16 |t|)⁴ e^{512}` (`lamT`):

* `gasR_matchAt_small`: `MatchAt.MatchAt (siteAct cbd (gR N n t U)) Λ(t) 10`.
* (a) `log_YR_eq_sum_sym`: `log Y(U) = Σ_x yS(U, x)`. `yS_shift`: `yS(τ_c U, x + e_c) = yS(U, x)`, for every direction `c`.
* (b) `abs_yS_le`: `|yS(U, x)| ≤ Λ(t)`. No constant is subtracted: the tilted `g_p` have Haar mean zero.
* (c) `osc_near`, `osc_far`: for every `U`, `U'`, `|yS(U, x) − yS(U', x)| ≤ 2 Λ(t)`; for `U`, `U'` equal on every link not based at `s`,
  `≤ 6 Λ(t) e^{−10 r}` once `s ∉ ball cbd x (2 r + 1)`. `osc_sum`: for any such pairs indexed by `s`,
  `Σ_s |yS(U_s, x) − yS(U'_s, x)| ≤ 3 · 10⁶ Λ(t)`.
* `yS_local`: for `U`, `U'` equal on every link based in `ball cbd x (2 r + 1)`,
  `|yS(U, x) − yS(U', x)| ≤ 2 (2 · 65^r + 1) Λ(t) e^{−10 r}`.

## The smallest polymer

Argued, not a Lean statement. Write `T(z) = a(z)⁻¹ V(z) a(z + j)` for the hi link at `z`. For fixed `V` these are i.i.d. Haar on
the four vertical edges of a three-cube, and `tr h_p = tr(U T U'⁻¹ T⁻¹)` with no `a` left. So the four mixed faces are the Wilson
tube with its two ends frozen, `∫ dT ∏ χ(h_p) = χ(P) χ̄(P')/N⁴` with `P`, `P'` the in-plane faces, on one orientation
of the tube. With `φ = 1 − Re tr/N` and `g = −2t(φ − ⟨φ⟩) + O(t²)`, for `N ≥ 3`:
`v(cube) = (2 t⁴/N⁶) Re[w(P) w̄(P')] + O(t⁵)`, `w = χ/N`; for `N = 2`, `(t⁴/4) w(P) w(P')`. There are `4` cubes per site. So at
`U = 1`, `log Y` is about `8 t⁴/N⁶` per site, and at a Haar-typical `U` it is of order `t⁴/N⁸`: the oscillation per site is of
order `t⁴`, with the factor `N⁻⁶`, and `t⁴` cannot be improved uniformly in `U`. The bounds of this module are the right
power; the constant `e^{512}` is not near the true one, and they do not see the `N⁻⁶`.

## The method

§1: `zg_private`, Fubini at the private corner. §2: `matchAt_small`: for `|E| ≥ 4`, `ε^{|E|} ≤ λ ε'^{|E|}` with
`λ = (ε/ε')⁴`, so `gAct/λ` satisfies `Decay` at `ε' = e^{−128}`, and `MatchAt.matchAt_of_count` applied to it gives `MatchAt` at
parameter `λ`. §3: the cost of removing the polymers that reach `Sg`, by `MatchAt.cluster_sites`. §4: the average over all
enumerations (the Shapley value of `Λ ↦ log Y(Λ)`). §5: shells. §6: the plaquettes.

DERIVED (module-wide): `4` the least activated set and the corners; `16`, `65`, `4225`, `2 r + 1` as in `StripGas`; `8 = 2 · 4` so
`128/8 = 16`; `512 = 4 · 128`; `2` the two removals in `osc_core`, one per gas; `6 = 2 (2 + 1)`, the single site of `Θ`. CHOSEN:
`κ = 10`, so `e^{10} > 65²` and shells sum; `T = 128 = 8 · 16`, so `1 + κ − τ = −5`. COMPUTED: `64 ≤ e⁵`, `8450 ≤ e⁶⁴`, `5 · 4225 ≤ e^{10}`.

## What does not follow

* The bounds have content only for `16 |t| < e^{−128}`: `Λ(t₂) = 1` exactly, where `abs_yS_le` gives no more than `StripGas.abs_yR_le`,
  and the constant `65536 e^{512}` is far from the true one.
* The constant-width strip is not proved, and `t = β` is not reached: `t` is capped at `t₂`.
* The second layer is not touched: `∫ e^{−β S_in} exp(Σ_x yS)` stays open, and the missing inequality of `StripTail` with it.
* `osc_sum` is a sum over `s` at fixed `x`. The sum over `x` at fixed `s`, the Dobrushin column, is not stated.
* The oscillation is per site `s` of the links based there, in `U`. It is not stated in the in-plane holonomies: dependence
  on `U` through in-plane loops only is not proved.
* The evaluation above is not a Lean statement, in particular no lower bound on the oscillation is proved.
* `t = 0` is excluded by `0 < |t|` only because `λ` is divided by; there `g = 0`.
* The hypothesis `n ≥ 3` even is that of `CumulantStrip.priv2` and `priv3`. Argued, not proved: at `n = 2` two plaquettes can share
  all four corners. Odd `n` is not treated.
* The statement is for `SU(N)`. The centring uses Haar translation only; the `U(1)` form is argued.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StripOsc

open Finset MeasureTheory Filter Topology
open MassGap.StrongCoupling MassGap.PolymerCount MassGap.ChunkActivity MassGap.ChunkLinks MassGap.StripGas
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

/-! ## 1. A private corner kills a moment -/

section Generic

variable {N : ℕ} {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]
  {bd : Pq → List (Lk × Bool)} {g : Pq → (Lk → SU N) → ℝ} {ε : ℝ}

/-- **A site seen by one plaquette of `E` kills `∫ ∏_E g`**, when `g_p` is centred in each of its sites. DERIVED: `0` the
mean. -/
theorem zg_private (h : SiteGas bd g ε)
    (hcent : ∀ p, ∀ z ∈ linkSupp bd p, ∀ a, ∫ b, g p (Function.update a z b) ∂(probHaar (SU N)) = 0)
    {E : Finset Pq} {p : Pq} (hp : p ∈ E) {z : Lk} (hz : z ∈ linkSupp bd p)
    (hpriv : ∀ q ∈ E, q ≠ p → z ∉ linkSupp bd q) : zg g E = 0 := by
  have hF : Continuous fun a : Lk → SU N => ∏ q ∈ E, g q a :=
    continuous_finsetProd _ fun q _ => h.cont q
  obtain ⟨C, hC⟩ := HeatBath.exists_abs_le hF
  unfold zg
  rw [HeatBath.integral_eq_integral_update (probHaar (SU N)) z _ hF.measurable hC]
  have hin : ∀ W : Lk → SU N, ∫ b, ∏ q ∈ E, g q (Function.update W z b) ∂(probHaar (SU N)) = 0 := by
    intro W
    have hs : ∀ b, ∏ q ∈ E, g q (Function.update W z b)
        = g p (Function.update W z b) * ∏ q ∈ E.erase p, g q W := by
      intro b
      rw [← Finset.mul_prod_erase E _ hp]
      congr 1
      refine Finset.prod_congr rfl fun q hq => h.reads q _ _ fun y hy => ?_
      have hne : y ≠ z := fun e => hpriv q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq) (e ▸ hy)
      exact Function.update_of_ne hne _ _
    simp_rw [hs]
    rw [integral_mul_const, hcent p z hz W, zero_mul]
  simp_rw [hin]
  simp

/-! ## 2. Kotecký–Preiss with a small parameter -/

/-- `8450 ≤ e⁶⁴`, the closing estimate of `matchAt_small`. DERIVED: `64 = 128/2`, half the decay rate
`128`; `8450 = 2 · 4225`, `4225` the connected-set growth. COMPUTED: `8450 ≤ 2⁶⁴` by `norm_num`. -/
theorem exp_64_ge : (8450 : ℝ) ≤ Real.exp 64 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have e : Real.exp 64 = Real.exp 1 ^ 64 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (8450 : ℝ) ≤ 2 ^ 64 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 64

/-- **`MatchAt` at parameter `λ`.** If moments of fewer than `4` plaquettes vanish and `ε⁴ ≤ λ e^{−512}`, every weight carries
`λ`. CHOSEN: `128`, `10`. COMPUTED: `4 · 16 e^{1 + 10 − 16} ≤ 1`, `2 · 4225 e^{−64} ≤ 1`. -/
theorem matchAt_small (hbd : ∀ p, (linkSupp bd p).Nonempty) (h : SiteGas bd g ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-128)) (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hM : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16)
    (hK : ∀ v m, (connSets bd v m).card ≤ 4225 ^ m)
    (hmin : ∀ E : Finset Pq, E.Nonempty → E.card < 4 → zg g E = 0)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hl : ε ^ 4 ≤ lam * Real.exp (-128) ^ 4) :
    MatchAt.MatchAt (siteAct bd g) lam 10 := by
  classical
  set e' := Real.exp (-128) with he'
  have he'0 : 0 < e' := Real.exp_pos _
  set wt : Finset Pq → ℝ := fun E => gAct bd g E / lam with hwt
  have hdec : Decay wt 128 := by
    intro E
    have h1 : Real.exp (-((128 : ℝ) * E.card)) = e' ^ E.card := by
      rw [he', ← Real.exp_nat_mul]
      congr 1
      ring
    rw [h1, hwt]
    show |gAct bd g E / lam| ≤ _
    rw [abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
    by_cases hX : E.Nonempty ∧ TouchConnected bd E
    · by_cases hcard : E.card < 4
      · rw [gAct_of hX, hmin E hX.1 hcard, abs_zero]
        positivity
      · rw [gAct_of hX]
        obtain ⟨k, hk⟩ : ∃ k, E.card = 4 + k := ⟨E.card - 4, by omega⟩
        refine (abs_zg_le h hε0 E).trans ?_
        rw [hk, pow_add, pow_add]
        calc ε ^ 4 * ε ^ k ≤ (lam * e' ^ 4) * e' ^ k :=
              mul_le_mul hl (pow_le_pow_left₀ hε0 hε k) (by positivity) (by positivity)
          _ = _ := by ring
    · unfold gAct
      rw [if_neg hX, abs_zero]
      positivity
  have hq1 : 2 * (((4225 : ℕ) : ℝ) * Real.exp (-((128 : ℝ) / 2))) ≤ 1 := by
    have e : Real.exp (-((128 : ℝ) / 2)) = (Real.exp 64)⁻¹ := by
      rw [← Real.exp_neg]; norm_num
    rw [e]
    have hpos : 0 < Real.exp 64 := Real.exp_pos _
    push_cast
    rw [show (2 : ℝ) * (4225 * (Real.exp 64)⁻¹) = 8450 / Real.exp 64 by ring, div_le_one hpos]
    exact exp_64_ge
  have hconn : ConnSupp bd wt := fun X hX => by
    have : gAct bd g X ≠ 0 := fun h0 => hX (by simp only [hwt, h0, zero_div])
    exact (gAct_ne_zero this).2
  have hcount := countAt_link bd (w := wt) (t := 128) (c := 4) (M := 16) (K := 4225)
    (by norm_num) hc (by norm_num) hM hK hconn hdec (by norm_num) hq1
  have hw0 : wt ∅ = 0 := by simp only [hwt, gAct_empty, zero_div]
  have hmat := MatchAt.matchAt_of_count (push_supp_empty hbd hw0) (z := ((16 : ℕ) : ℝ))
    (τ := 128 / (2 * ((4 : ℕ) : ℝ))) (κ := 10) (by positivity) (by norm_num) hcount (by
      have e : (1 : ℝ) + 10 - 128 / (2 * ((4 : ℕ) : ℝ)) = -5 := by norm_num
      rw [e, Real.exp_neg]
      have h5 := exp_five_ge
      have hpos : 0 < Real.exp 5 := Real.exp_pos _
      push_cast
      rw [show (4 : ℝ) * 16 * (Real.exp 5)⁻¹ = 64 / Real.exp 5 by ring, div_le_one hpos]
      exact h5)
  have hpush : ∀ X, siteAct bd g X = lam * push (supp bd) wt X := by
    intro X
    unfold siteAct push
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun E _ => by
      simp only [hwt]
      field_simp
  refine ⟨push_supp_empty hbd (gAct_empty bd g), hlam.le, hlam1, by norm_num, fun v => ?_⟩
  have hs := hmat.2.2.2.2 v
  calc ∑ X ∈ MatchAt.site v, |siteAct bd g X| * Real.exp (lam * X.card) * (1 + X.card * Real.exp (10 * X.card))
      ≤ ∑ X ∈ MatchAt.site v, lam * (|push (supp bd) wt X| * Real.exp (1 * X.card)
          * (1 + X.card * Real.exp (10 * X.card))) := by
        refine Finset.sum_le_sum fun X _ => ?_
        rw [hpush, abs_mul, abs_of_pos hlam]
        have h1 : Real.exp (lam * X.card) ≤ Real.exp (1 * X.card) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hlam1 (Nat.cast_nonneg _))
        have h2 : 0 ≤ lam * |push (supp bd) wt X| := by positivity
        have h3 : (0 : ℝ) ≤ 1 + X.card * Real.exp (10 * X.card) := by positivity
        calc _ = (lam * |push (supp bd) wt X|) * Real.exp (lam * X.card)
              * (1 + X.card * Real.exp (10 * X.card)) := by ring
          _ ≤ (lam * |push (supp bd) wt X|) * Real.exp (1 * X.card)
              * (1 + X.card * Real.exp (10 * X.card)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
          _ = _ := by ring
    _ = lam * ∑ X ∈ MatchAt.site v, |push (supp bd) wt X| * Real.exp (1 * X.card)
          * (1 + X.card * Real.exp (10 * X.card)) := by rw [Finset.mul_sum]
    _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hs hlam.le
    _ = lam := mul_one _

end Generic

/-! ## 3. The cost of a far change -/

section Local

variable {V : Type*} [Fintype V] [DecidableEq V] {w w' : Finset V → ℝ}

/-- As `StripGas.log_Z_sdiff_le`, at parameter `a`. No numeral. -/
theorem log_Z_sdiff_le' {a κ : ℝ} (hM : MatchAt.MatchAt w a κ) (T D : Finset (Finset V)) :
    |Real.log (MatchAt.Z MatchAt.meet w T) - Real.log (MatchAt.Z MatchAt.meet w (T \ D))|
      ≤ ∑ δ ∈ D, MatchAt.cKP w a δ := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d B hd ih =>
    have hG := MatchAt.G_insert (inc := MatchAt.meet) (w := w) (S := T) (B := B) (d := d)
    unfold MatchAt.G at hG
    have hL := MatchAt.abs_L_le MatchAt.meet_symm (MatchAt.dob_of_matchAt hM) (T \ B) d
    rw [hG, Finset.sum_insert hd]
    have := abs_add_le (Real.log (MatchAt.Z MatchAt.meet w T) - Real.log (MatchAt.Z MatchAt.meet w (T \ B)))
      (MatchAt.L MatchAt.meet w (T \ B) d)
    linarith

/-- `|y| ≤ a`. No numeral. -/
theorem abs_yOf_le' {a κ : ℝ} (hM : MatchAt.MatchAt w a κ) (S : Finset (Finset V)) (x : V) :
    |yOf w S x| ≤ a := by
  classical
  refine (log_Z_sdiff_le' hM S (atSite S x)).trans ?_
  have hpt : ∀ X ∈ atSite S x, MatchAt.cKP w a X ≤ MatchAt.kp w a κ X := fun X _ =>
    (cKP_le_eps a X).trans (MatchAt.eps_le_kp X)
  refine (Finset.sum_le_sum hpt).trans ?_
  have hsub : atSite S x ⊆ MatchAt.site x := by
    intro X hX
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hX).2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun X _ _ => MatchAt.kp_nonneg w a κ X).trans ?_
  exact hM.2.2.2.2 x

/-- **Removing the polymers that reach `Sg` changes `y` little.** `Bin`, `Bout`, `lev` as in `StripGas.abs_yOf_sub_le`; `Sg` outside
`Bout`; `Θ` a set met by every polymer that meets both `Bin` and `Sg`. DERIVED: `2`, `1` as in `abs_yOf_sub_le`. -/
theorem yOf_remove {a κ : ℝ} (hM : MatchAt.MatchAt w a κ) (lev : V → ℕ) {x : V} {Bin Bout : Finset V}
    {r : ℕ} (hx0 : lev x = 0) (hxB : x ∈ Bin) (h3 : ∀ y, y ∉ Bin → r + 1 ≤ lev y)
    (h4 : ∀ y ∈ Bin, lev y ≤ r) (h5 : ∀ u, u ∉ Bout → 2 * r + 2 ≤ lev u)
    (hdiam : ∀ X, w X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X, (lev y : ℝ) - lev z ≤ X.card)
    {Sg Θ : Finset V} (hfar : ∀ s ∈ Sg, s ∉ Bout)
    (hΘ : ∀ X : Finset V, (Bin ∩ X).Nonempty → ¬ Disjoint X Sg → (Θ ∩ X).Nonempty)
    (S : Finset (Finset V)) :
    |yOf w S x - yOf w (S.filter fun X => Disjoint X Sg) x|
      ≤ (2 * Θ.card + 1) * a * Real.exp (-(κ * r)) := by
  classical
  have hκ : 0 ≤ κ := hM.2.2.2.1
  have ha0 : 0 ≤ a := hM.2.1
  set A := atSite S x with hA
  set D2 := S.filter (fun X => (Bin ∩ X).Nonempty ∧ ¬ Disjoint X Sg) with hD2
  set U := S.filter (fun X => Disjoint X Bin ∧ ¬ Disjoint X Sg) with hU
  set S0 := S \ D2 with hS0
  set F := S.filter (fun X => Disjoint X Sg) with hF
  have hmeet : ∀ X : Finset V, (Bin ∩ X).Nonempty ↔ ¬ Disjoint X Bin := by
    intro X
    rw [Finset.disjoint_left]
    constructor
    · rintro ⟨z, hz⟩ hd
      rw [Finset.mem_inter] at hz
      exact hd hz.2 hz.1
    · intro hd
      push Not at hd
      obtain ⟨z, h1, h2⟩ := hd
      exact ⟨z, Finset.mem_inter.2 ⟨h2, h1⟩⟩
  have hF1 : F = S0 \ U := by
    ext X
    simp only [hF, hS0, hD2, hU, Finset.mem_filter, Finset.mem_sdiff, hmeet]
    tauto
  have hat : S0 \ atSite S0 x = (S \ A) \ D2 := by
    ext X
    simp only [hS0, hA, atSite, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hat0 : S0 \ A = (S \ A) \ D2 := sdiff_sdiff_comm
  have hatF : F \ atSite F x = (S0 \ U) \ A := by
    ext X
    rw [hF1]
    simp only [hA, atSite, Finset.mem_filter, Finset.mem_sdiff, hS0]
    tauto
  have hdiam' : ∀ X, w X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X,
      (fun a b : V => |(lev a : ℝ) - lev b|) y z ≤ X.card := by
    intro X hw y hy z hz
    exact abs_le.2 ⟨by linarith [hdiam X hw z hz y hy], hdiam X hw y hy z hz⟩
  have hQ := MatchAt.cluster_sites hM (ρ := fun a b : V => |(lev a : ℝ) - lev b|)
    (dset := fun y => ((r : ℝ) + 1) - lev y)
    (fun a b => by
      have := neg_abs_le ((lev a : ℝ) - lev b)
      show ((r : ℝ) + 1) - lev a ≤ ((r : ℝ) + 1) - lev b + |(lev a : ℝ) - lev b|
      linarith)
    hdiam' (U := U)
    (fun Y hY _ y hy => by
      have hdisj := (Finset.mem_filter.1 hY).2.1
      have hyB : y ∉ Bin := fun hb => Finset.disjoint_left.1 hdisj hy hb
      have : ((r + 1 : ℕ) : ℝ) ≤ lev y := by exact_mod_cast h3 y hyB
      push_cast at this
      show ((r : ℝ) + 1) - lev y ≤ 0
      linarith)
    (Λ := {x}) (R := (r : ℝ) + 1)
    (fun y hy => by
      rw [Finset.mem_singleton] at hy
      subst hy
      simp [hx0])
    (A := A)
    (fun X hX => ⟨x, by
      rw [Finset.mem_inter]
      exact ⟨(Finset.mem_filter.1 hX).2, Finset.mem_singleton_self x⟩⟩)
    (fun X hX hU' => Finset.disjoint_left.1 (Finset.mem_filter.1 hU').2.1 (Finset.mem_filter.1 hX).2 hxB)
    S0
  have hsum : ∑ δ ∈ D2, MatchAt.cKP w a δ ≤ Θ.card * a * Real.exp (-(κ * r)) := by
    have hpt : ∀ X ∈ D2, MatchAt.cKP w a X ≤ Real.exp (-(κ * r)) * MatchAt.kp w a κ X := by
      intro X hX
      by_cases hw : w X = 0
      · have h0 : MatchAt.cKP w a X = 0 := by
          simp [MatchAt.cKP, MatchAt.eps, hw]
        rw [h0]
        exact mul_nonneg (Real.exp_pos _).le (MatchAt.kp_nonneg _ _ _ _)
      · obtain ⟨-, ⟨v, hv⟩, hns⟩ := Finset.mem_filter.1 hX
        rw [Finset.mem_inter] at hv
        rw [Finset.disjoint_left] at hns
        push Not at hns
        obtain ⟨u, huX, huS⟩ := hns
        have h1 := hdiam X hw u huX v hv.2
        have h2 : ((2 * r + 2 : ℕ) : ℝ) ≤ lev u := by exact_mod_cast h5 u (hfar u huS)
        have h3' : (lev v : ℝ) ≤ r := by exact_mod_cast h4 v hv.1
        push_cast at h2
        have hc : (r : ℝ) + 2 ≤ X.card := by linarith
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        have hexp : Real.exp (κ * r) ≤ Real.exp (κ * X.card) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hκ)
        have hkey : Real.exp (κ * r) ≤ 1 + (X.card : ℝ) * Real.exp (κ * X.card) := by
          have : Real.exp (κ * X.card) ≤ (X.card : ℝ) * Real.exp (κ * X.card) :=
            le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
          linarith
        have he := MatchAt.eps_nonneg w a X
        have hk : MatchAt.eps w a X * Real.exp (κ * r) ≤ MatchAt.kp w a κ X :=
          mul_le_mul_of_nonneg_left hkey he
        calc MatchAt.cKP w a X ≤ MatchAt.eps w a X := cKP_le_eps a X
          _ = Real.exp (-(κ * r)) * (MatchAt.eps w a X * Real.exp (κ * r)) := by
              rw [mul_comm (MatchAt.eps w a X), ← mul_assoc, ← Real.exp_add]
              simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
    calc ∑ δ ∈ D2, MatchAt.cKP w a δ ≤ ∑ δ ∈ D2, Real.exp (-(κ * r)) * MatchAt.kp w a κ δ :=
          Finset.sum_le_sum hpt
      _ = Real.exp (-(κ * r)) * ∑ δ ∈ D2, MatchAt.kp w a κ δ := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(κ * r)) * (Θ.card * a) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine (MatchAt.sum_meet_le _ (MatchAt.kp_nonneg w a κ) Θ D2 fun Y hY => ?_).trans
            (MatchAt.sum_site_le hM Θ)
          have hY' := (Finset.mem_filter.1 hY).2
          exact hΘ Y hY'.1 hY'.2
      _ = _ := by ring
  have t1 := log_Z_sdiff_le' hM S D2
  have t2 := log_Z_sdiff_le' hM (S \ A) D2
  have hexp1 : Real.exp (-(κ * ((r : ℝ) + 1))) ≤ Real.exp (-(κ * r)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hcard : (({x} : Finset V).card : ℝ) * a * Real.exp (-(κ * ((r : ℝ) + 1)))
      ≤ a * Real.exp (-(κ * r)) := by
    simpa using mul_le_mul_of_nonneg_left hexp1 ha0
  have hQ' := abs_le.1 (hQ.trans hcard)
  have hQ1 := hQ'.1
  have hQ2 := hQ'.2
  unfold MatchAt.Q at hQ1 hQ2
  rw [← hF1] at hQ1 hQ2
  have ht1 := abs_le.1 (t1.trans hsum)
  have ht2 := abs_le.1 (t2.trans hsum)
  rw [← hat0] at ht2
  unfold yOf
  rw [hatF, ← hF1, ← hA]
  have e1 : (2 * (Θ.card : ℝ) + 1) * a * Real.exp (-(κ * r))
      = 2 * ((Θ.card : ℝ) * a * Real.exp (-(κ * r))) + a * Real.exp (-(κ * r)) := by ring
  rw [e1]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2, hQ1, hQ2]

/-- **Two gases that agree off `Sg` have nearly the same `y` far from `Sg`.** DERIVED: `2` one removal per gas. -/
theorem osc_core {a κ : ℝ} (hM : MatchAt.MatchAt w a κ) (hM' : MatchAt.MatchAt w' a κ) (lev : V → ℕ)
    {x : V} {Bin Bout : Finset V} {r : ℕ} (hx0 : lev x = 0) (hxB : x ∈ Bin)
    (h3 : ∀ y, y ∉ Bin → r + 1 ≤ lev y) (h4 : ∀ y ∈ Bin, lev y ≤ r)
    (h5 : ∀ u, u ∉ Bout → 2 * r + 2 ≤ lev u)
    (hdiam : ∀ X, w X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X, (lev y : ℝ) - lev z ≤ X.card)
    (hdiam' : ∀ X, w' X ≠ 0 → ∀ y ∈ X, ∀ z ∈ X, (lev y : ℝ) - lev z ≤ X.card)
    {Sg Θ : Finset V} (hfar : ∀ s ∈ Sg, s ∉ Bout)
    (hagree : ∀ X, Disjoint X Sg → w X = w' X)
    (hΘ : ∀ X : Finset V, (Bin ∩ X).Nonempty → ¬ Disjoint X Sg → (Θ ∩ X).Nonempty)
    (S : Finset (Finset V)) :
    |yOf w S x - yOf w' S x| ≤ 2 * ((2 * Θ.card + 1) * a * Real.exp (-(κ * r))) := by
  classical
  have h1 := yOf_remove hM lev hx0 hxB h3 h4 h5 hdiam hfar hΘ S
  have h2 := yOf_remove hM' lev hx0 hxB h3 h4 h5 hdiam' hfar hΘ S
  have e : yOf w (S.filter fun X => Disjoint X Sg) x = yOf w' (S.filter fun X => Disjoint X Sg) x := by
    unfold yOf
    rw [Z_congr fun X hX => hagree X (Finset.mem_filter.1 hX).2,
      Z_congr fun X hX => hagree X (Finset.mem_filter.1 (Finset.mem_sdiff.1 hX).1).2]
  rw [e] at h1
  have := abs_le.1 h1
  have := abs_le.1 h2
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 h2).1, (abs_le.1 h2).2]

/-! ## 4. The average over the enumerations -/

/-- The sites before `x`. No numeral. -/
def prE {m : ℕ} (e : V ≃ Fin m) (x : V) : Finset V := univ.filter fun y => (e y).val < (e x).val

/-- The marginal of `f` at `x` for the enumeration `e`. No numeral. -/
def yF {m : ℕ} (f : Finset V → ℝ) (e : V ≃ Fin m) (x : V) : ℝ := f (insert x (prE e x)) - f (prE e x)

/-- **The marginals telescope.** No numeral. -/
theorem sum_yF {m : ℕ} (f : Finset V → ℝ) (e : V ≃ Fin m) : ∑ x, yF f e x = f univ - f ∅ := by
  classical
  set Bk : ℕ → Finset V := fun k => univ.filter fun y => (e y).val < k with hBk
  have h1 : ∀ x, yF f e x = f (Bk ((e x).val + 1)) - f (Bk (e x).val) := by
    intro x
    have e1 : insert x (prE e x) = Bk ((e x).val + 1) := by
      ext y
      simp only [prE, hBk, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | h)
        · omega
        · omega
      · intro h
        by_cases hy : (e y).val = (e x).val
        · exact Or.inl (e.injective (Fin.ext hy))
        · exact Or.inr (by omega)
    unfold yF
    rw [e1]
    rfl
  simp_rw [h1]
  have h2 := Equiv.sum_comp e fun i : Fin m => f (Bk (i.val + 1)) - f (Bk i.val)
  rw [h2, Fin.sum_univ_eq_sum_range (fun k => f (Bk (k + 1)) - f (Bk k)) m,
    Finset.sum_range_sub (fun k => f (Bk k)) m]
  have e0 : Bk 0 = ∅ := by ext x; simp [hBk]
  have em : Bk m = univ := by
    ext x
    simp only [hBk, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (e x).isLt
  rw [e0, em]

/-- **The marginal averaged over the enumerations**, the Shapley value of `f`. DERIVED: `1` the mean. -/
def ySym (f : Finset V → ℝ) (x : V) : ℝ :=
  (Fintype.card (Equiv.Perm V) : ℝ)⁻¹ * ∑ π : Equiv.Perm V, yF f (π.trans (Fintype.equivFin V)) x

theorem card_perm_pos : (0 : ℝ) < Fintype.card (Equiv.Perm V) := by
  exact_mod_cast Fintype.card_pos

theorem sum_ySym (f : Finset V → ℝ) : ∑ x, ySym f x = f univ - f ∅ := by
  unfold ySym
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [sum_yF]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ card_perm_pos.ne', one_mul]

/-- **A bound on the marginals passes to the average.** No numeral. -/
theorem abs_ySym_sub_le {f f' : Finset V → ℝ} {x : V} {b : ℝ}
    (h : ∀ π : Equiv.Perm V, |yF f (π.trans (Fintype.equivFin V)) x - yF f' (π.trans (Fintype.equivFin V)) x| ≤ b) :
    |ySym f x - ySym f' x| ≤ b := by
  have hc := card_perm_pos (V := V)
  unfold ySym
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun π _ => h π).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The average is covariant**: if `f'(σ Λ) = f(Λ)` then `ySym f' (σ x) = ySym f x`. No numeral. -/
theorem ySym_cov (σ : Equiv.Perm V) {f f' : Finset V → ℝ} (hf : ∀ Λ, f' (Λ.image σ) = f Λ) (x : V) :
    ySym f' (σ x) = ySym f x := by
  unfold ySym
  congr 1
  have hstep : ∀ π : Equiv.Perm V,
      yF f' ((σ⁻¹ * π⁻¹)⁻¹.trans (Fintype.equivFin V)) (σ x) = 0 → True := fun _ _ => trivial
  have key : ∀ (π : Equiv.Perm V) {m : ℕ} (e : V ≃ Fin m), yF f' (σ.symm.trans (π.trans e)) (σ x) = yF f (π.trans e) x := by
    intro π m e
    have e1 : prE (σ.symm.trans (π.trans e)) (σ x) = (prE (π.trans e) x).image σ := by
      ext y
      simp only [prE, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Equiv.trans_apply,
        Equiv.symm_apply_apply]
      constructor
      · intro h
        exact ⟨σ.symm y, h, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    unfold yF
    rw [e1, ← Finset.image_insert, hf, hf]
  have hb := Equiv.sum_comp (Equiv.mulRight σ⁻¹ : Equiv.Perm V ≃ Equiv.Perm V)
    fun π : Equiv.Perm V => yF f' (π.trans (Fintype.equivFin V)) (σ x)
  rw [← hb]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e2 : ((Equiv.mulRight σ⁻¹ : Equiv.Perm V ≃ Equiv.Perm V) π).trans (Fintype.equivFin V)
      = σ.symm.trans (π.trans (Fintype.equivFin V)) := by
    ext z
    rfl
  rw [e2]
  exact key π _

/-- The sites before `x` and the polymers at `x`. No numeral. -/
theorem sf_sdiff (x : V) {P : Finset V} (hx : x ∉ P) :
    (insert x P).powerset \ atSite (insert x P).powerset x = P.powerset := by
  classical
  ext X
  simp only [atSite, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_powerset, not_and]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    have hzx : z ≠ x := fun e => (h2 h1) (e ▸ hz)
    exact (Finset.mem_insert.1 (h1 hz)).resolve_left hzx
  · intro h
    exact ⟨h.trans (Finset.subset_insert _ _), fun _ hc => hx (h hc)⟩

theorem notMem_prE {m : ℕ} (e : V ≃ Fin m) (x : V) : x ∉ prE e x := by
  simp [prE]

/-- The log of the gas on the subsets of `Λ`. No numeral. -/
def fZ (w : Finset V → ℝ) (Λ : Finset V) : ℝ := Real.log (MatchAt.Z MatchAt.meet w Λ.powerset)

/-- **The marginal is the `y` of `StripGas`.** No numeral. -/
theorem yF_eq_yOf {m : ℕ} (w : Finset V → ℝ) (e : V ≃ Fin m) (x : V) :
    yF (fZ w) e x = yOf w (insert x (prE e x)).powerset x := by
  unfold yF yOf fZ
  rw [sf_sdiff x (notMem_prE e x)]

/-! ## 5. Shells -/

variable {Lk Pq : Type} [Fintype Lk] [DecidableEq Lk] [Fintype Pq] [DecidableEq Pq]
  {bd : Pq → List (Lk × Bool)}

theorem exp_ten_ge : (21125 : ℝ) ≤ Real.exp 10 := by
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have e : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (21125 : ℝ) ≤ 2.718 ^ 10 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 10

/-- **The sum over shells.** A family bounded by `2 a`, and by `6 a e^{−10 r}` outside the ball of radius `2 r + 1`, sums to
at most `3 · 10⁶ a`. COMPUTED: `65² e^{−10} ≤ 1/5`; `130 + 6 · 65³ · 5/4 ≤ 3 · 10⁶`. DERIVED: `65` of `card_ball_le`; `16` the link
multiplicity it reads; `6 = 2 · 3` and `10` the far bound of `osc_far` (rate `10` chosen in `matchAt_small`);
`3000000 = 3 · 10⁶` the computed total. -/
theorem sum_le_of_shells (hc : ∀ p, (linkSupp bd p).card ≤ 4)
    (hMc : ∀ l, (univ.filter fun p => l ∈ linkSupp bd p).card ≤ 16) (x : Lk) {a : ℝ} (ha : 0 ≤ a)
    {D : Lk → ℝ} (h0 : ∀ s, 0 ≤ D s) (h1 : ∀ s, D s ≤ 2 * a)
    (h2 : ∀ (r : ℕ) (s : Lk), s ∉ ball bd x (2 * r + 1) → D s ≤ 6 * a * Real.exp (-(10 * r))) :
    ∑ s, D s ≤ 3000000 * a := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 6 * 65 ^ 3 * (5 / 4) := ⟨_, rfl⟩
  have hexp : ∀ R : ℕ, Real.exp (-(10 * (R : ℝ))) * 65 ^ (2 * R) ≤ (1 / 5) ^ R := by
    intro R
    have e1 : Real.exp (-(10 * (R : ℝ))) = (Real.exp 10 ^ R)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring_nf
    have e2 : ((65 : ℝ) ^ (2 * R)) = 4225 ^ R := by rw [pow_mul]; norm_num
    rw [e1, e2, ← div_eq_inv_mul, ← div_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ R
    rw [div_le_iff₀ (Real.exp_pos _)]
    linarith [exp_ten_ge]
  have hT : ∀ R : ℕ, ∑ s ∈ ball bd x (2 * R + 1), D s ≤ a * (130 + K - K * (1 / 5) ^ R) := by
    intro R
    induction R with
    | zero =>
      have hcard : ((ball bd x 1).card : ℝ) ≤ 65 := by
        have := card_ball_le hc hMc x 1
        exact_mod_cast (by simpa using this)
      calc ∑ s ∈ ball bd x (2 * 0 + 1), D s ≤ ∑ _s ∈ ball bd x 1, 2 * a :=
            Finset.sum_le_sum fun s _ => h1 s
        _ = (ball bd x 1).card * (2 * a) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 65 * (2 * a) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by simp only [pow_zero]; ring
    | succ R ih =>
      have hsub : ball bd x (2 * (R + 1) + 1) ⊆ ball bd x (2 * R + 1)
          ∪ (ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1)) := by
        intro s hs
        by_cases h : s ∈ ball bd x (2 * R + 1)
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hs, h⟩)
      have hsplit : ∑ s ∈ ball bd x (2 * (R + 1) + 1), D s
          ≤ ∑ s ∈ ball bd x (2 * R + 1), D s
            + ∑ s ∈ ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1), D s := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => h0 s).trans ?_
        rw [Finset.sum_union Finset.disjoint_sdiff]
      have hcard : ((ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1)).card : ℝ) ≤ 65 ^ (2 * R) * 65 ^ 3 := by
        have h3 := (Finset.card_le_card (Finset.sdiff_subset (s := ball bd x (2 * (R + 1) + 1))
          (t := ball bd x (2 * R + 1)))).trans (card_ball_le hc hMc x _)
        have h4 : 2 * (R + 1) + 1 = 2 * R + 3 := by ring
        rw [h4, pow_add] at h3
        exact_mod_cast h3
      have hshell : ∑ s ∈ ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1), D s
          ≤ 6 * 65 ^ 3 * a * (1 / 5) ^ R := by
        calc _ ≤ ∑ _s ∈ ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1), 6 * a * Real.exp (-(10 * (R : ℝ))) :=
              Finset.sum_le_sum fun s hs => h2 R s (Finset.mem_sdiff.1 hs).2
          _ = (ball bd x (2 * (R + 1) + 1) \ ball bd x (2 * R + 1)).card * (6 * a * Real.exp (-(10 * (R : ℝ)))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (65 ^ (2 * R) * 65 ^ 3) * (6 * a * Real.exp (-(10 * (R : ℝ)))) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 6 * 65 ^ 3 * a * (Real.exp (-(10 * (R : ℝ))) * 65 ^ (2 * R)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hexp R) (by positivity)
      have e : a * (130 + K - K * (1 / 5) ^ (R + 1))
          = a * (130 + K - K * (1 / 5) ^ R) + 6 * 65 ^ 3 * a * (1 / 5) ^ R := by
        rw [hK, pow_succ]
        ring
      rw [e]
      linarith
  have hlim : Tendsto (fun R : ℕ => a * (130 + K)
      + (Fintype.card Lk : ℝ) * (6 * a) * Real.exp (-(10 * (R : ℝ)))) atTop (𝓝 (a * (130 + K)
      + (Fintype.card Lk : ℝ) * (6 * a) * 0)) := by
    refine tendsto_const_nhds.add (Tendsto.const_mul _ ?_)
    have : Tendsto (fun R : ℕ => 10 * (R : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp this
  have hbound : ∀ R : ℕ, ∑ s, D s ≤ a * (130 + K)
      + (Fintype.card Lk : ℝ) * (6 * a) * Real.exp (-(10 * (R : ℝ))) := by
    intro R
    have hsplit := Finset.sum_add_sum_compl (ball bd x (2 * R + 1)) D
    have hout : ∑ s ∈ (ball bd x (2 * R + 1))ᶜ, D s
        ≤ (Fintype.card Lk : ℝ) * (6 * a) * Real.exp (-(10 * (R : ℝ))) := by
      calc _ ≤ ∑ _s ∈ (ball bd x (2 * R + 1))ᶜ, 6 * a * Real.exp (-(10 * (R : ℝ))) :=
            Finset.sum_le_sum fun s hs => h2 R s (Finset.mem_compl.1 hs)
        _ = ((ball bd x (2 * R + 1))ᶜ).card * (6 * a * Real.exp (-(10 * (R : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card Lk : ℝ) * (6 * a * Real.exp (-(10 * (R : ℝ)))) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (by positivity)
        _ = _ := by ring
    have hK0 : 0 ≤ K * (1 / 5 : ℝ) ^ R := by rw [hK]; positivity
    have := hT R
    have hm : a * (130 + K - K * (1 / 5) ^ R) ≤ a * (130 + K) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    linarith
  have hfin := ge_of_tendsto' hlim hbound
  rw [mul_zero, add_zero] at hfin
  have hk : 130 + K ≤ 3000000 := by rw [hK]; norm_num
  nlinarith

end Local

/-! ## 6. The mixed plaquettes -/

section Mixed

open MassGap.CumulantStrip MassGap.MixCut MassGap.MixExpand MassGap.MixEqui MassGap.RectWilson MassGap.StripWidth

variable {N n : ℕ}

/-- `∫ F(A b B) = ∫ F(A b⁻¹ B) = 0` for `F` of Haar mean zero. DERIVED: `0` the mean. -/
theorem mean_word {F : SU N → ℝ} (h0 : ∫ g, F g ∂(probHaar (SU N)) = 0) (A B : SU N) :
    ∫ b, F (A * b * B) ∂(probHaar (SU N)) = 0 ∧ ∫ b, F (A * b⁻¹ * B) ∂(probHaar (SU N)) = 0 := by
  have h1 := HeatBath.integral_twoSided F A B
  have h2 := integral_inv_eq_self (fun b => F (A * b * B)) (probHaar (SU N))
  rw [h0] at h1
  exact ⟨h1, h2.trans h1⟩

theorem rshift_ne_rshift (hn : 2 ≤ n) {i j : Fin 4} (hij : i ≠ j) (x : St n) :
    rshift (fun _ => n) i x ≠ rshift (fun _ => n) j x := by
  intro h
  have := congrFun h i
  simp only [rshift, Function.update_self, Function.update_of_ne hij] at this
  exact TwoDVanish.finRotate_ne hn _ this

/-- A word in four distinct site variables has Haar mean zero in each of them. DERIVED: `0` the mean. -/
theorem cent_word {F : SU N → ℝ} (hF0 : ∫ g, F g ∂(probHaar (SU N)) = 0) (a : St n → SUN.SU N)
    {x x1 x2 x12 : St n} (d1 : x1 ≠ x) (d2 : x2 ≠ x) (d3 : x12 ≠ x) (d4 : x1 ≠ x2) (d5 : x12 ≠ x2)
    (d6 : x12 ≠ x1) (A B C D : SU N) {z : St n} (hz : z = x ∨ z = x1 ∨ z = x2 ∨ z = x12) :
    ∫ b, F (Function.update a z b x * A * (Function.update a z b x1)⁻¹ * B * Function.update a z b x12 * C
      * (Function.update a z b x2)⁻¹ * D) ∂(probHaar (SU N)) = 0 := by
  rcases hz with rfl | rfl | rfl | rfl
  · simp only [Function.update_self, Function.update_of_ne d1, Function.update_of_ne d2,
      Function.update_of_ne d3]
    have := (mean_word hF0 (1 : SU N) (A * (a x1)⁻¹ * B * a x12 * C * (a x2)⁻¹ * D)).1
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans this
    simp only [one_mul, mul_assoc]
  · simp only [Function.update_self, Function.update_of_ne d1.symm, Function.update_of_ne d4.symm,
      Function.update_of_ne d6]
    have := (mean_word hF0 (a x * A) (B * a x12 * C * (a x2)⁻¹ * D)).2
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans this
    simp only [mul_assoc]
  · simp only [Function.update_self, Function.update_of_ne d2.symm, Function.update_of_ne d4,
      Function.update_of_ne d5]
    have := (mean_word hF0 (a x * A * (a x1)⁻¹ * B * a x12 * C) D).2
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans this
    simp only [mul_assoc]
  · simp only [Function.update_self, Function.update_of_ne d3.symm, Function.update_of_ne d6.symm,
      Function.update_of_ne d5.symm]
    have := (mean_word hF0 (a x * A * (a x1)⁻¹ * B) (C * (a x2)⁻¹ * D)).1
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans this
    simp only [mul_assoc]

/-- The rotated mixed holonomy as a word in the corner variables. No numeral. -/
theorem hol_word (c : St n → SUN.SU N) (U : Lk n → SUN.SU N) {i j : Fin 4} (hib : i.val / 2 = 0)
    (hjb : ¬ j.val / 2 = 0) (x : St n) :
    (sysR (fun _ => n) N).hol ((i, j), x) (gT (fun _ => n) c U)
      = c x * U (i, x) * (c (rshift (fun _ => n) i x))⁻¹ * U (j, rshift (fun _ => n) i x)
        * c (rshift (fun _ => n) i (rshift (fun _ => n) j x)) * (U (i, rshift (fun _ => n) j x))⁻¹
        * (c (rshift (fun _ => n) j x))⁻¹ * (U (j, x))⁻¹ := by
  rw [hol_eq]
  simp only [gT, if_pos hib, if_neg hjb]
  group

/-- **`g_p` is centred in each of its corners**, at every `U`. The rotated holonomy is `A b^{±1} B` in the corner variable.
DERIVED: `2` the least side; `0` the mean. -/
theorem gR_cent (hN : N ≠ 0) (hn : 2 ≤ n) (t : ℝ) (U : Lk n → SUN.SU N) (p : Pm n) (z : St n)
    (hz : z ∈ StrongCoupling.linkSupp cbd p) (a : St n → SUN.SU N) :
    ∫ b, gR N n t U p (Function.update a z b) ∂(probHaar (SU N)) = 0 := by
  have hF0 : ∫ g, cT N t (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SU N)) = 0 := integral_cT hN t
  have hij : dirLo p.1.1 ≠ dirHi p.1.2 := fun h => dirHi_block p.1.2 (h ▸ dirLo_block p.1.1)
  have hc : Cn p z := mem_ls.1 hz
  have key := cent_word hF0 a (x := p.2) (x1 := rshift (fun _ => n) (dirLo p.1.1) p.2)
    (x2 := rshift (fun _ => n) (dirHi p.1.2) p.2)
    (x12 := rshift (fun _ => n) (dirLo p.1.1) (rshift (fun _ => n) (dirHi p.1.2) p.2))
    (WindowRead.rshift_ne _ hn _) (WindowRead.rshift_ne _ hn _) (rshift2_ne _ hij hn _)
    (rshift_ne_rshift hn hij _) (WindowRead.rshift_ne _ hn _)
    (by
      rw [MixCut.rshift_comm]
      exact WindowRead.rshift_ne _ hn _)
    (U (dirLo p.1.1, p.2)) (U (dirHi p.1.2, rshift (fun _ => n) (dirLo p.1.1) p.2))
    (U (dirLo p.1.1, rshift (fun _ => n) (dirHi p.1.2) p.2))⁻¹ (U (dirHi p.1.2, p.2))⁻¹ hc
  refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans key
  unfold gR gg plaq pl
  rw [hol_word _ U (dirLo_block _) (dirHi_block _)]

/-- **Moments of fewer than `4` plaquettes vanish.** `CumulantStrip.priv2`, `priv3` give a private corner. DERIVED: `3` the least
extent; `2` the parity. Inherited: `8` the range `8 |t| ≤ 1` of `CumulantStrip.abs_cT_le`. -/
theorem zg_lt_four (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht : 8 * |t| ≤ 1)
    (U : Lk n → SUN.SU N) (E : Finset (Pm n)) (hE : E.Nonempty) (hc : E.card < 4) :
    zg (gR N n t U) E = 0 := by
  have hgas := gasR (n := n) hN ht U
  have hcent := gR_cent (n := n) hN (by omega) t U
  have pick : ∀ (p : Pm n) (z : St n), p ∈ E → Cn p z → (∀ q ∈ E, q ≠ p → ¬ Cn q z) →
      zg (gR N n t U) E = 0 := fun p z hp hz hq =>
    zg_private hgas hcent hp (mem_ls.2 hz) fun q hqE hne hc => hq q hqE hne (mem_ls.1 hc)
  have hcases : E.card = 1 ∨ E.card = 2 ∨ E.card = 3 := by
    have := Finset.card_pos.2 hE
    omega
  rcases hcases with h | h | h
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    refine pick p p.2 (Finset.mem_singleton_self p) (Or.inl rfl) fun q hq hne => ?_
    exact absurd (Finset.mem_singleton.1 hq) hne
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 h
    obtain ⟨z, h1, h2⟩ := priv2 hn he hpq
    refine pick p z (by simp) h1 fun r hr hne => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact absurd rfl hne
    · exact h2
  · obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.1 h
    obtain ⟨z, h' | h' | h'⟩ := priv3 hn he p q r fun h0 => hpq h0.1
    · refine pick p z (by simp) h'.1 fun s hs hne => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact h'.2.1
      · exact h'.2.2
    · refine pick q z (by simp) h'.1 fun s hs hne => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact h'.2.1
      · exact absurd rfl hne
      · exact h'.2.2
    · refine pick r z (by simp) h'.1 fun s hs hne => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact h'.2.1
      · exact h'.2.2
      · exact absurd rfl hne

/-- **The width** `t₂ = e^{−128}/16`. CHOSEN: `128`. DERIVED: `16` of `abs_cT_le`. -/
def tTwo : ℝ := Real.exp (-128) / 16

theorem tTwo_pos : 0 < tTwo := by unfold tTwo; positivity

/-- **The small parameter** `Λ(t) = (16 |t|)⁴ e^{512}`. DERIVED: `512 = 4 · 128`; `16` of `abs_cT_le`. -/
def lamT (t : ℝ) : ℝ := (16 * |t|) ^ 4 * Real.exp 512

theorem range_two {t : ℝ} (ht : |t| ≤ tTwo) :
    8 * |t| ≤ 1 ∧ 16 * |t| ≤ Real.exp (-128) := by
  have h1 : Real.exp (-128) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  unfold tTwo at ht
  constructor <;> linarith [abs_nonneg t]

theorem lamT_pos {t : ℝ} (ht0 : t ≠ 0) : 0 < lamT t := by
  have := abs_pos.2 ht0
  unfold lamT
  positivity

theorem lamT_le_one {t : ℝ} (ht : |t| ≤ tTwo) : lamT t ≤ 1 := by
  have h1 := (range_two ht).2
  have h0 : 0 ≤ 16 * |t| := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 4
  have e : Real.exp (-128) ^ 4 * Real.exp 512 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  unfold lamT
  calc _ ≤ Real.exp (-128) ^ 4 * Real.exp 512 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 1 := e

theorem lamT_spec (t : ℝ) : (16 * |t|) ^ 4 ≤ lamT t * Real.exp (-128) ^ 4 := by
  have e : Real.exp 512 * Real.exp (-128) ^ 4 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  unfold lamT
  rw [mul_assoc, e, mul_one]

/-- **Kotecký–Preiss at parameter `Λ(t)`**, at every `U`. CHOSEN: as in `matchAt_small`, the rate
`10`. DERIVED: `3` the least extent of `zg_lt_four`. -/
theorem gasR_matchAt_small (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0)
    (ht : |t| ≤ tTwo) (U : Lk n → SUN.SU N) :
    MatchAt.MatchAt (siteAct cbd (gR N n t U)) (lamT t) 10 :=
  matchAt_small ls_nonempty (gasR hN (range_two ht).1 U) (by positivity) (range_two ht).2 ls_card
    ls_mult connSets_le (fun E hE hc => zg_lt_four hN hn he (range_two ht).1 U E hE hc) (lamT_pos ht0)
    (lamT_le_one ht) (lamT_spec t)

/-- `log Y` on the plaquettes inside `Λ`. No numeral. -/
def fR (N n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) (Λ : Finset (St n)) : ℝ :=
  Real.log (Yg (gR N n t U) (inW cbd Λ))

/-- **The covariant summand** `yS(U, x)`: the marginal of `log Y` at `x`, averaged over all enumerations of the sites.
No numeral. -/
def yS (N n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) (x : St n) : ℝ := ySym (fR N n t U) x

theorem fR_eq (hN : N ≠ 0) {t : ℝ} (ht : 8 * |t| ≤ 1) (U : Lk n → SUN.SU N) :
    fR N n t U = fZ (siteAct cbd (gR N n t U)) := by
  funext Λ
  unfold fR fZ
  rw [Y_eq_siteZ ls_nonempty (gasR hN ht U) Λ]

/-- **(a) `log Y(U) = Σ_x yS(U, x)`.** DERIVED: `1` the empty gas. -/
theorem log_YR_eq_sum_sym (U : Lk n → SUN.SU N) (t : ℝ) :
    Real.log (YR N n t U) = ∑ x, yS N n t U x := by
  unfold yS
  rw [sum_ySym]
  unfold fR YR
  rw [inW_univ, inW_empty ls_nonempty, Yg_empty, Real.log_one, sub_zero]

/-- The marginal in the form of `yOf`. No numeral. -/
theorem yF_fR (hN : N ≠ 0) {t : ℝ} (ht : 8 * |t| ≤ 1) (U : Lk n → SUN.SU N) {m : ℕ} (e : St n ≃ Fin m)
    (x : St n) : yF (fR N n t U) e x = yOf (siteAct cbd (gR N n t U)) (insert x (prE e x)).powerset x := by
  rw [fR_eq hN ht U, yF_eq_yOf]

/-- **(b) `|yS(U, x)| ≤ Λ(t)`**, at every `U`. No numeral. -/
theorem abs_yS_le (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    (U : Lk n → SUN.SU N) (x : St n) : |yS N n t U x| ≤ lamT t := by
  have h := abs_ySym_sub_le (f := fR N n t U) (f' := fun _ => 0) (x := x) (b := lamT t) fun π => by
    have h0 : yF (fun _ : Finset (St n) => (0 : ℝ)) (π.trans (Fintype.equivFin (St n))) x = 0 := by
      simp [yF]
    rw [h0, sub_zero, yF_fR hN (range_two ht).1]
    exact abs_yOf_le' (gasR_matchAt_small hN hn he ht0 ht U) _ x
  have h0 : ySym (fun _ : Finset (St n) => (0 : ℝ)) x = 0 := by simp [ySym, yF]
  rw [h0, sub_zero] at h
  exact h

/-- `U`, `U'` equal on every link not based in `Sg`. No numeral. -/
def AgreeOff (Sg : Finset (St n)) (U U' : Lk n → SUN.SU N) : Prop := ∀ l : Lk n, l.2 ∉ Sg → U l = U' l

/-- The links a plaquette reads are based at its corners, so a polymer off `Sg` does not see a change on `Sg`. No numeral. -/
theorem siteAct_agree {Sg : Finset (St n)} {U U' : Lk n → SUN.SU N} {t : ℝ} (h : AgreeOff Sg U U')
    (X : Finset (St n)) (hX : Disjoint X Sg) :
    siteAct cbd (gR N n t U) X = siteAct cbd (gR N n t U') X := by
  classical
  unfold siteAct push
  refine Finset.sum_congr rfl fun E hE => ?_
  have hs : supp cbd E = X := mem_fib.1 hE
  have hin : ∀ p ∈ E, gR N n t U p = gR N n t U' p := by
    intro p hp
    refine gR_congr t fun l hl => h l fun hlS => ?_
    have hcorner : l.2 ∈ StrongCoupling.linkSupp cbd p := by
      refine mem_ls.2 ?_
      simp only [plLinks, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
    exact Finset.disjoint_left.1 hX (hs ▸ mem_supp.2 ⟨p, hp, hcorner⟩) hlS
  have hz : zg (gR N n t U) E = zg (gR N n t U') E := by
    unfold zg
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    exact Finset.prod_congr rfl fun p hp => by rw [hin p hp]
  unfold gAct
  simp only [hz]

/-- **The far estimate.** For `Sg` outside the ball of radius `2 r + 1` at `x`, and `U`, `U'` equal off `Sg`:
`|yS(U, x) − yS(U', x)| ≤ 2 (2 |Θ| + 1) Λ(t) e^{−10 r}`, `Θ` met by every polymer that meets the ball of radius `r` and `Sg`.
DERIVED: `2 r + 2` the cap of the level; `3` the least extent of `zg_lt_four`. -/
theorem yS_far (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    {U U' : Lk n → SUN.SU N} {x : St n} {r : ℕ} {Sg Θ : Finset (St n)}
    (hfar : ∀ s ∈ Sg, s ∉ ball cbd x (2 * r + 1)) (hag : AgreeOff Sg U U')
    (hΘ : ∀ X : Finset (St n), (ball cbd x r ∩ X).Nonempty → ¬ Disjoint X Sg → (Θ ∩ X).Nonempty) :
    |yS N n t U x - yS N n t U' x| ≤ 2 * ((2 * Θ.card + 1) * lamT t * Real.exp (-(10 * r))) := by
  refine abs_ySym_sub_le fun π => ?_
  rw [yF_fR hN (range_two ht).1, yF_fR hN (range_two ht).1]
  set R := 2 * r + 2 with hR
  have hlv : ∀ (p : Pm n) (u v : St n), u ∈ StrongCoupling.linkSupp cbd p → v ∈ StrongCoupling.linkSupp cbd p →
      lev cbd x R u ≤ lev cbd x R v + 1 := fun p u v hu hv => lev_lip x R hu hv
  exact osc_core (gasR_matchAt_small hN hn he ht0 ht U) (gasR_matchAt_small hN hn he ht0 ht U')
    (lev cbd x R) (Bin := ball cbd x r) (Bout := ball cbd x (2 * r + 1)) (lev_root x R)
    (ball_mono x (Nat.zero_le r) (Finset.mem_singleton_self x))
    (fun y hy => ge_lev_of_notMem (by omega) hy) (fun y hy => lev_le_of_mem hy)
    (fun u hu => by
      have := ge_lev_of_notMem (R := R) (by omega) hu
      omega)
    (fun X hX y hy z hz => lev_diam hlv X hX y hy z hz)
    (fun X hX y hy z hz => lev_diam hlv X hX y hy z hz) hfar
    (fun X hX => siteAct_agree hag X hX) hΘ _

/-- **(c) Near**: for every `U`, `U'`, with no hypothesis: `|yS(U, x) − yS(U', x)| ≤ 2 Λ(t)`. DERIVED: `2` the two
summands; `3` the least extent of `zg_lt_four`. -/
theorem osc_near (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    (U U' : Lk n → SUN.SU N) (x : St n) : |yS N n t U x - yS N n t U' x| ≤ 2 * lamT t := by
  have h1 := abs_yS_le hN hn he ht0 ht U x
  have h2 := abs_yS_le hN hn he ht0 ht U' x
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 h2).1, (abs_le.1 h2).2]

/-- **(c) Far**: `U`, `U'` equal on every link not based at `s`, `s` outside the ball of radius `2 r + 1` at `x`:
`|yS(U, x) − yS(U', x)| ≤ 6 Λ(t) e^{−10 r}`. DERIVED: `6 = 2 · 3`, `Θ = {s}`. -/
theorem osc_far (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    {U U' : Lk n → SUN.SU N} {x s : St n} {r : ℕ} (hs : s ∉ ball cbd x (2 * r + 1))
    (hag : AgreeOff {s} U U') :
    |yS N n t U x - yS N n t U' x| ≤ 6 * lamT t * Real.exp (-(10 * r)) := by
  have h := yS_far hN hn he ht0 ht (Sg := {s}) (Θ := {s}) (r := r) (x := x)
    (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hs) hag
    (fun X _ hd => by
      rw [Finset.disjoint_singleton_right, not_not] at hd
      exact ⟨s, Finset.mem_inter.2 ⟨Finset.mem_singleton_self s, hd⟩⟩)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.card_singleton, Nat.cast_one]
  ring

/-- **(c) Summed**: for any pairs `U_s`, `U'_s` equal on every link not based at `s`,
`Σ_s |yS(U_s, x) − yS(U'_s, x)| ≤ 3 · 10⁶ Λ(t)`. No numeral beyond `sum_le_of_shells`. -/
theorem osc_sum (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    (x : St n) (U U' : St n → Lk n → SUN.SU N) (hag : ∀ s, AgreeOff {s} (U s) (U' s)) :
    ∑ s, |yS N n t (U s) x - yS N n t (U' s) x| ≤ 3000000 * lamT t :=
  sum_le_of_shells (bd := cbd) ls_card ls_mult x (lamT_pos ht0).le (fun _ => abs_nonneg _)
    (fun s => osc_near hN hn he ht0 ht _ _ x) (fun _ s hs => osc_far hN hn he ht0 ht hs (hag s))

/-- **(a) Local**: for `U`, `U'` equal on every link based in the ball of radius `2 r + 1` at `x`,
`|yS(U, x) − yS(U', x)| ≤ 2 (2 · 65^r + 1) Λ(t) e^{−10 r}`. DERIVED: `Θ` the ball of radius `r`; `3` the least
extent of `zg_lt_four`. -/
theorem yS_local (hN : N ≠ 0) (hn : 3 ≤ n) (he : n % 2 = 0) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ tTwo)
    {U U' : Lk n → SUN.SU N} {x : St n} {r : ℕ} (hag : ∀ l : Lk n, l.2 ∈ ball cbd x (2 * r + 1) → U l = U' l) :
    |yS N n t U x - yS N n t U' x| ≤ 2 * ((2 * 65 ^ r + 1) * lamT t * Real.exp (-(10 * r))) := by
  have h := yS_far hN hn he ht0 ht (Sg := (ball cbd x (2 * r + 1))ᶜ) (Θ := ball cbd x r) (r := r) (x := x)
    (fun y hy => Finset.mem_compl.1 hy)
    (fun l hl => hag l (by simpa using hl)) (fun X hm _ => hm)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hc : ((ball cbd x r).card : ℝ) ≤ 65 ^ r := by exact_mod_cast card_ball_le ls_card ls_mult x r
  have h0 := (lamT_pos ht0).le
  have he0 := (Real.exp_pos (-(10 * (r : ℝ)))).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h0) he0

/-! ## 7. Translation -/

/-- The translation of the sites in direction `c`. DERIVED: `1` the step. -/
def shE (c : Fin 4) : Equiv.Perm (St n) where
  toFun := rshift (fun _ => n) c
  invFun := bk c
  left_inv y := bk_rshift c y
  right_inv y := by
    funext k
    unfold bk rshift
    by_cases h : k = c
    · subst h
      simp only [Function.update_self, Equiv.apply_symm_apply]
    · simp [Function.update_of_ne h]

/-- The translated configuration: `(τ_c U)(μ, x + e_c) = U(μ, x)`. No numeral. -/
def trU (c : Fin 4) (U : Lk n → SUN.SU N) : Lk n → SUN.SU N := fun l => U (l.1, (shE c).symm l.2)

theorem trU_apply (c : Fin 4) (U : Lk n → SUN.SU N) (μ : Fin 4) (y : St n) :
    trU c U (μ, rshift (fun _ => n) c y) = U (μ, y) := by
  unfold trU
  show U (μ, (shE c).symm (shE c y)) = _
  rw [Equiv.symm_apply_apply]

/-- The translated plaquette. No numeral. -/
def shP (c : Fin 4) : Equiv.Perm (Pm n) where
  toFun p := (p.1, shE c p.2)
  invFun p := (p.1, (shE c).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem gT_tr (c : Fin 4) (a : St n → SUN.SU N) (U : Lk n → SUN.SU N) (μ : Fin 4) (y : St n) :
    gT (fun _ => n) a (trU c U) (μ, rshift (fun _ => n) c y)
      = gT (fun _ => n) (fun z => a (shE c z)) U (μ, y) := by
  unfold gT
  dsimp only
  rw [trU_apply]
  have e : shE c (rshift (fun _ => n) μ y) = rshift (fun _ => n) μ (rshift (fun _ => n) c y) :=
    MixCut.rshift_comm _ c μ y
  simp only [e]
  rfl

/-- **The rotated plaquette is covariant.** No numeral. -/
theorem gR_tr (c : Fin 4) (t : ℝ) (U : Lk n → SUN.SU N) (p : Pm n) (a : St n → SUN.SU N) :
    gR N n t (trU c U) (shP c p) a = gR N n t U p fun z => a (shE c z) := by
  obtain ⟨⟨k1, k2⟩, x⟩ := p
  unfold gR gg plaq pl
  show cT N t (WilsonAction.wilsonDensity ((sysR (fun _ => n) N).hol ((dirLo k1, dirHi k2), rshift (fun _ => n) c x)
    (gT (fun _ => n) a (trU c U)))) = cT N t (WilsonAction.wilsonDensity ((sysR (fun _ => n) N).hol ((dirLo k1, dirHi k2), x)
    (gT (fun _ => n) (fun z => a (shE c z)) U)))
  rw [hol_eq, hol_eq, MixCut.rshift_comm _ (dirLo k1) c x, MixCut.rshift_comm _ (dirHi k2) c x]
  rw [gT_tr, gT_tr, gT_tr, gT_tr]

theorem corner_shift (c : Fin 4) {p : Pm n} {z : St n} : Cn (shP c p) (shE c z) ↔ Cn p z := by
  have hinj := (shE (n := n) c).injective
  obtain ⟨k, x⟩ := p
  have e1 : ∀ (μ : Fin 4) (y : St n), rshift (fun _ => n) μ (shE c y) = shE c (rshift (fun _ => n) μ y) :=
    fun μ y => (MixCut.rshift_comm _ c μ y).symm
  show (shE c z = shE c x ∨ shE c z = rshift (fun _ => n) (dirLo k.1) (shE c x) ∨
      shE c z = rshift (fun _ => n) (dirHi k.2) (shE c x) ∨
      shE c z = rshift (fun _ => n) (dirLo k.1) (rshift (fun _ => n) (dirHi k.2) (shE c x))) ↔ _
  simp only [e1, hinj.eq_iff]
  rfl

/-- **The product Haar measure is invariant under the translation of the sites.** No numeral. -/
theorem integral_shE (c : Fin 4) {F : (St n → SUN.SU N) → ℝ} (hF : Continuous F) :
    ∫ a, F (fun z => a (shE c z)) ∂(νS N (St n)) = ∫ a, F a ∂(νS N (St n)) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : St n => probHaar (SU N)) (shE (n := n) c).symm
  have h := hmp.integral_comp' F
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  show F _ = F _
  congr 1
  funext z
  rw [MeasurableEquiv.coe_piCongrLeft]
  have h2 := Equiv.piCongrLeft_apply_apply (fun _ : St n => SU N) (shE (n := n) c).symm a (shE c z)
  rw [Equiv.symm_apply_apply] at h2
  exact h2.symm

/-- `Y` is covariant. No numeral. -/
theorem Yg_shift (c : Fin 4) (t : ℝ) (U : Lk n → SUN.SU N) (Λ : Finset (St n)) :
    Yg (gR N n t (trU c U)) (inW cbd (Λ.image (shE c))) = Yg (gR N n t U) (inW cbd Λ) := by
  classical
  have himg : inW cbd (Λ.image (shE c)) = (inW cbd Λ).image (shP c) := by
    ext q
    obtain ⟨p, rfl⟩ := (shP (n := n) c).surjective q
    rw [(shP (n := n) c).injective.mem_finset_image, mem_inW, mem_inW]
    constructor
    · intro h z hz
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 (h (mem_ls.2 ((corner_shift c).2 (mem_ls.1 hz))))
      rw [(shE (n := n) c).injective hyz] at hy
      exact hy
    · intro h z hz
      obtain ⟨y, rfl⟩ := (shE (n := n) c).surjective z
      exact Finset.mem_image_of_mem _ (h (mem_ls.2 ((corner_shift c).1 (mem_ls.1 hz))))
  have h3 : ∀ a : St n → SUN.SU N, ∏ q ∈ (inW cbd Λ).image (shP c), (1 + gR N n t (trU c U) q a)
      = ∏ p ∈ inW cbd Λ, (1 + gR N n t U p fun z => a (shE c z)) := by
    intro a
    rw [Finset.prod_image fun x _ y _ hxy => (shP (n := n) c).injective hxy]
    exact Finset.prod_congr rfl fun p _ => by rw [gR_tr]
  have hc : Continuous fun a : St n → SUN.SU N => ∏ p ∈ inW cbd Λ, (1 + gR N n t U p a) :=
    continuous_finsetProd _ fun p _ => continuous_const.add (continuous_gR t U p)
  unfold Yg
  rw [himg, integral_congr_ae (Eventually.of_forall h3)]
  exact integral_shE c hc

/-- `log Y` is covariant. No numeral. -/
theorem fR_shift (c : Fin 4) (t : ℝ) (U : Lk n → SUN.SU N) (Λ : Finset (St n)) :
    fR N n t (trU c U) (Λ.image (shE c)) = fR N n t U Λ := by
  unfold fR
  rw [Yg_shift]

/-- **(a) Translation covariance**: `yS(τ_c U, x + e_c) = yS(U, x)`. No numeral. -/
theorem yS_shift (c : Fin 4) (t : ℝ) (U : Lk n → SUN.SU N) (x : St n) :
    yS N n t (trU c U) (shE c x) = yS N n t U x :=
  ySym_cov (shE c) (fR_shift c t U) x

end Mixed

end MassGap.StripOsc

#print axioms MassGap.StripOsc.zg_private
#print axioms MassGap.StripOsc.matchAt_small
#print axioms MassGap.StripOsc.yOf_remove
#print axioms MassGap.StripOsc.osc_core
#print axioms MassGap.StripOsc.sum_ySym
#print axioms MassGap.StripOsc.ySym_cov
#print axioms MassGap.StripOsc.sum_le_of_shells
#print axioms MassGap.StripOsc.gR_cent
#print axioms MassGap.StripOsc.zg_lt_four
#print axioms MassGap.StripOsc.gasR_matchAt_small
#print axioms MassGap.StripOsc.log_YR_eq_sum_sym
#print axioms MassGap.StripOsc.abs_yS_le
#print axioms MassGap.StripOsc.osc_near
#print axioms MassGap.StripOsc.osc_far
#print axioms MassGap.StripOsc.osc_sum
#print axioms MassGap.StripOsc.yS_local
#print axioms MassGap.StripOsc.yS_shift
