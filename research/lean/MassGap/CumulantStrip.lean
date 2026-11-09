import Mathlib
import MassGap.StripLift

/-!
# MassGap.CumulantStrip — the extensive cumulant bound and the quartic cost of the mixed coupling

`StripWidth.DA_le` costs `8192 · 16^w t²`: Hölder over the sixteen colours multiplies the `t²` coefficient of
`log Z` by sixteen, so the `t²` terms of the sides `n` and `2n` no longer cancel. This module proves the extensive
form of the cumulant generating function of `S_mix` at the decoupled end, with its Haar part exact at every order in
`t`: the cost is `6 · 2⁶⁰ · 16^w t⁴`, against `8192 · 16^w t²` in `StripWidth.DA_le`. Declarations are in `MassGap.CumulantStrip`.

## The result

* `logZA_ext`: for `|t| ≤ t₀ = 2⁻¹⁷`, every `β`, every `N ≠ 0`, every even `n ≥ 3`,
  `|log Z(β, t, n) − log Z(β, 0, n) − n⁴ ℓ(t)| ≤ 8 n⁴ η(t)`, `η(t) = 6 · 2⁵² t⁴`, with
  `ℓ(t) = 4 log H(−2t) − 8 t ⟨φ⟩`, `H` the Haar tilt of one plaquette (`ell`, `etaT`, `etaT_eq`). The main term is
  exactly `n⁴` times a function of `t` and `N` alone: no `β`.
* `DA_le_quartic`: `|DA(β, t, w) − DA(β, 0, w)| ≤ 6 · 2⁶⁰ · 16^w t⁴` for `|t| ≤ t₀`, `w ≥ 2`, since `n⁴ ℓ(t)` cancels
  exactly between `16 log Z_n` and `log Z_{2n}`.
* `strip_of_seed_quartic`: for `β ≥ 0`, `w ≥ 2`, a seed `DA(β, 0, w) ≤ 1/2000` opens `0 ≤ t ≤ 1/(2¹⁹ 2^w)`: the inverse seed side, where
  `StripWidth.strip_of_seed` has the inverse seed area.
* `strip_width_quartic`, `gap_quartic`: `DA(β, t, ·) → 0` and the size-uniform transfer gap of
  `StripLift.TransferGapAt` for `0 ≤ t ≤ t_quart(N, β) = 1/(2¹⁹ 2^{w₀})`, `w₀ = StripGapThm.seedWindow N β`.
  `tQuart_ge`: `t_quart ≥ 1/(2²⁰ √A_glue)`. `tGlue_le_tQuart`: the strip contains `StripWiden`'s at every `β`.
* `dependency_cgf`: the dependency-graph bound for real `z`. Bounded `X_p`, `|X_p| ≤ M`, with `X_p` independent of the
  variables outside a neighbourhood of size at most `D`: for `16 D |z| M ≤ 1`,
  `|log E e^{z S} − Σ_p log E e^{z X_p}| ≤ 192 |I| D z² M²`. So the real generating function is extensive on a
  radius `1/(16 D M)` independent of the number of variables. This is the real-variable form of the theorem of
  Janson (1988) and Féray–Méliot–Nikeghbali (2016); neither is used as an input.

## The method: a ratio induction with no cluster sum (§2)

For `g_p` bounded by `ε`, `Z(A) = ∫ Π_{A} (1 + g) W`, `W ≥ 0`, the ratio `Z(A ∪ p)/Z(A)` is read by induction on
`|A|` (`Gas.ratio`). The difference is `∫ g_p Π_{A}(1 + g) W`. Split `A` at a neighbourhood `K p` and expand only the
product over `A ∩ K p`: the terms `B ⊆ A ∩ K p` with `|B| < r` vanish (`Gas.van`), the others cost `ε^{1+|B|}` against
`Z(A ∖ K p)`, pointwise because the far product is positive, and `Z(A ∖ K p)` is within a factor `2` of `Z(A)` by the
induction. This is Dobrushin's recursion of `MatchAt.dob_bounds` run on the integral itself, without polymers.

No conditioning on the links is needed. The plaquettes are tilted to mean zero, `g_p = e^{−2t ψ_p}/H(−2t) − 1`, and
the only input is that a corner of `p` seen by nothing else in the integrand centres `g_p` out, for the weight
`e^{−β S_in}`, at every `β` (`cent_factor_c`, the rotation of `MixCut.gT`). By `MixExpand.exists_private` the terms
`|B| ≤ 2` vanish when `K p` is the two-step neighbourhood (`van3`); so `r = 3`, and the error per plaquette is `ε⁴`.

DERIVED (module-wide): `16 = 4 · 4` the corners of a plaquette at one site over the four orientations of the normal
mixed plaquettes; `64 = 4 · 16` the plaquettes touching one; `4096 = 64²` the two-step neighbourhood; `3` the terms
that vanish; `2` the orientations of a plaquette, the doubling, and the range of `φ`; `8 = 2 · 4`; `4` the normal
orientations and the tilt range `2 · 2`; `16 = 2⁴` the copies; `0` the decoupled end; `1` the unit of the tilt.
COMPUTED: `3 ≥ e`; `6 = 2 · 3`; `t₀ = 2⁻¹⁷`, the largest power of two with `4096 η ≤ 1/2`; `6 · 2⁵² = 6 · 16 · (4096 · 16)³`;
`6 · 2⁶⁰ = 256 · 6 · 2⁵²`; `2¹⁹` from `6 · 2⁶⁰ / 2⁷⁶ ≤ 1/2000`; `192 = 12 · 16`; `4225 = 65²`, the bound `A_glue ≥ 4225` of `area_ge`. Inherited: `1/2000`,
`1/1000` of `StripWidth` and `DoublingSharp`; `16192` of `StripWiden.tGlue`.

## What does not follow

* `DA_le_tail` is not proved: the bound here is `O(16^w t⁴)`. Argued, not proved: four mixed faces of a three-cube with all eight
  corners shared have no private corner, and their joint activity reads the two in-plane faces of the cube, so `κ₄(n)` depends on
  `β` through the two-dimensional torus measure. Up to `t³` the generating function is `β`-free, which follows from `logZA_ext`.
  Whether `κ₄(n)/n⁴` is constant in `n` up to finite-size terms is not settled here: on the open plane functions of separated
  rectangles are independent (`StripTail.plane_forget` is the torus form at `t = 0`).
* So the strip stays window dependent: `t₀` is a constant, but the cost `16^w t⁴` still needs `t ≲ 2^{−w}` at the seed,
  and `t_quart` shrinks with `β`: `t_quart ≥ 1/(2²⁰ √A_glue)` (`tQuart_ge`), and with `A_glue ≍ N³ β log β` read off
  `glueArea`, `gapArea`, `bulkExp` (not a Lean statement) the width is of order `(N³ β log β)^{−1/2}`. Neither `t₀` nor `t_quart` reaches `t = β` at large `β`.
* `dependency_cgf` is for real `z`. The bound `|κ_k| ≤ n (c (D + 1) M)^k k^{k−2}` needs the complex disc, where the far
  product is not positive and the pointwise step of §2 fails. It is not proved here.
* `CouplingTower.StrongEnd`, `AnisoTorus.AnisoAnalytic`, `MixCutTest.VarGap`, `MixPlane.NoStallOnSegment` stay open.
-/

namespace MassGap.CumulantStrip

open MeasureTheory Filter Topology MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut MassGap.MixEqui
  MassGap.MixExpand MassGap.StripWidth

/-! ## 1. The tail of a binomial sum -/

theorem sum_card_pow {ι : Type*} (D : Finset ι) (x : ℝ) :
    ∑ B ∈ D.powerset, x ^ B.card = (1 + x) ^ D.card := by
  have h := Finset.prod_one_add (f := fun _ : ι => x) D
  simp only [Finset.prod_const] at h
  exact h.symm

/-- **The tail of the subset sum**: `Σ_{B ⊆ D, |B| ≥ r} ε^{|B|} ≤ 3 (m ε)^r` for `|D| ≤ m`, `m ε ≤ 1`. Each term is
at most `(m ε)^r (1/m)^{|B|}` and `(1 + 1/m)^m ≤ e`. COMPUTED: `e ≤ 3`. -/
theorem tail_le {ι : Type*} (D : Finset ι) {m : ℕ} (hm : 0 < m) (hD : D.card ≤ m) {ε : ℝ} (h0 : 0 ≤ ε)
    (hε : (m : ℝ) * ε ≤ 1) (r : ℕ) :
    ∑ B ∈ D.powerset.filter (fun B => r ≤ B.card), ε ^ B.card ≤ 3 * ((m : ℝ) * ε) ^ r := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℝ := 1 / (m : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hmx : (m : ℝ) * x = 1 := by rw [hx]; exact mul_one_div_cancel hmR.ne'
  have hεx : ε ≤ x := by
    rw [hx, le_div_iff₀ hmR]
    linarith
  have hterm : ∀ B ∈ D.powerset.filter (fun B => r ≤ B.card),
      ε ^ B.card ≤ ((m : ℝ) * ε) ^ r * x ^ B.card := by
    intro B hB
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.mem_filter.1 hB).2
    rw [hd, pow_add, pow_add, mul_pow]
    have e : (m : ℝ) ^ r * ε ^ r * (x ^ r * x ^ d) = ((m : ℝ) * x) ^ r * ε ^ r * x ^ d := by
      rw [mul_pow]; ring
    rw [e, hmx, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hεx d) (by positivity)
  have hexp : (1 + x) ^ D.card ≤ 3 := by
    have h1 : (1 + x) ^ D.card ≤ (1 + x) ^ m := pow_le_pow_right₀ (by linarith) hD
    have h2 : (1 + x) ^ m ≤ Real.exp x ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) m
    have h3 : Real.exp x ^ m = Real.exp 1 := by
      rw [← Real.exp_nat_mul, hmx]
    have h4 := Real.exp_one_lt_d9
    rw [h3] at h2
    linarith
  have hp : 0 ≤ ((m : ℝ) * ε) ^ r := by positivity
  calc ∑ B ∈ D.powerset.filter (fun B => r ≤ B.card), ε ^ B.card
      ≤ ∑ B ∈ D.powerset.filter (fun B => r ≤ B.card), ((m : ℝ) * ε) ^ r * x ^ B.card :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ B ∈ D.powerset, ((m : ℝ) * ε) ^ r * x ^ B.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => mul_nonneg hp (by positivity)
    _ = ((m : ℝ) * ε) ^ r * (1 + x) ^ D.card := by rw [← Finset.mul_sum, sum_card_pow]
    _ ≤ 3 * ((m : ℝ) * ε) ^ r := by linarith [mul_le_mul_of_nonneg_left hexp hp]

/-! ## 2. The ratio induction -/

section Gas

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-- **The tilted mass** `Z(A) = ∫ Π_{q ∈ A} (1 + g_q) W`. DERIVED: `1` the unit of the product. -/
noncomputable def ZG (μ : Measure Ω) (W : Ω → ℝ) (g : ι → Ω → ℝ) (A : Finset ι) : ℝ :=
  ∫ x, (∏ q ∈ A, (1 + g q x)) * W x ∂μ

/-- **The hypotheses of the ratio induction**: `g` bounded by `ε ≤ 1/2`, `W ≥ 0` with positive mass, neighbourhoods
`K p` of size at most `m`, and the vanishing of every term with fewer than `r` near factors. DERIVED: `1/2` keeps
`1 + g` positive; `0` the vanishing and the sign of `W`. -/
structure Gas (μ : Measure Ω) (W : Ω → ℝ) (g : ι → Ω → ℝ) (K : ι → Finset ι) (m r : ℕ) (ε : ℝ) : Prop where
  W_nonneg : ∀ x, 0 ≤ W x
  mass_pos : 0 < ∫ x, W x ∂μ
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ 1 / 2
  bd : ∀ p x, |g p x| ≤ ε
  int : ∀ B F : Finset ι, Integrable (fun x => (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x) μ
  intp : ∀ (p : ι) (B F : Finset ι),
    Integrable (fun x => g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x) μ
  card_K : ∀ p, (K p).card ≤ m
  van : ∀ (p : ι) (B F : Finset ι), p ∉ B → Disjoint F (K p) → B.card < r →
    ∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x ∂μ = 0

variable {μ : Measure Ω} {W : Ω → ℝ} {g : ι → Ω → ℝ} {K : ι → Finset ι} {m r : ℕ} {ε : ℝ}

theorem Gas.one_add_ge (h : Gas μ W g K m r ε) (p : ι) (x : Ω) : 1 / 2 ≤ 1 + g p x := by
  have h1 := (abs_le.1 (h.bd p x)).1
  have h2 := h.eps_le
  linarith

theorem Gas.prod_nonneg (h : Gas μ W g K m r ε) (A : Finset ι) (x : Ω) : 0 ≤ ∏ q ∈ A, (1 + g q x) :=
  Finset.prod_nonneg fun q _ => by linarith [h.one_add_ge q x]

theorem Gas.intZ (h : Gas μ W g K m r ε) (A : Finset ι) :
    Integrable (fun x => (∏ q ∈ A, (1 + g q x)) * W x) μ := by
  simpa using h.int ∅ A

theorem Gas.ZG_pos (h : Gas μ W g K m r ε) (A : Finset ι) : 0 < ZG μ W g A := by
  have hW : Integrable W μ := by simpa using h.int ∅ ∅
  have hl : ∫ x, (1 / 2 : ℝ) ^ A.card * W x ∂μ ≤ ZG μ W g A := by
    refine integral_mono (hW.const_mul _) (h.intZ A) fun x => ?_
    refine mul_le_mul_of_nonneg_right ?_ (h.W_nonneg x)
    calc (1 / 2 : ℝ) ^ A.card = ∏ _q ∈ A, (1 / 2 : ℝ) := by simp
      _ ≤ ∏ q ∈ A, (1 + g q x) :=
        Finset.prod_le_prod (fun _ _ => by norm_num) fun q _ => h.one_add_ge q x
  rw [integral_const_mul] at hl
  have : 0 < (1 / 2 : ℝ) ^ A.card * ∫ x, W x ∂μ := mul_pos (by positivity) h.mass_pos
  linarith

/-- **One term costs `ε^{1+|B|}` against the far mass**, pointwise, the far product being positive. DERIVED: `1` the
factor `g_p`. -/
theorem Gas.abs_term (h : Gas μ W g K m r ε) (p : ι) (B F : Finset ι) :
    |∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x ∂μ| ≤ ε * ε ^ B.card * ZG μ W g F := by
  have hb : ∀ x, |g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x|
      ≤ ε * ε ^ B.card * ((∏ q ∈ F, (1 + g q x)) * W x) := by
    intro x
    have h1 := h.bd p x
    have h2 : |∏ q ∈ B, g q x| ≤ ε ^ B.card := by
      rw [Finset.abs_prod]
      calc ∏ q ∈ B, |g q x| ≤ ∏ _q ∈ B, ε :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun q _ => h.bd q x
        _ = ε ^ B.card := by simp
    have h3 : 0 ≤ (∏ q ∈ F, (1 + g q x)) * W x := mul_nonneg (h.prod_nonneg F x) (h.W_nonneg x)
    rw [show g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * W x
      = g p x * (∏ q ∈ B, g q x) * ((∏ q ∈ F, (1 + g q x)) * W x) by ring, abs_mul, abs_mul,
      abs_of_nonneg h3]
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) h.eps_nonneg) h3
  unfold ZG
  rw [← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (h.intp p B F).abs ((h.intZ F).const_mul _) hb)

/-- The difference of two masses, expanded over the near set `D`. DERIVED: `1` the unit of the product. -/
theorem Gas.delta_expand (h : Gas μ W g K m r ε) {p : ι} {T D : Finset ι} (hd : Disjoint T D)
    (hp : p ∉ T ∪ D) :
    ZG μ W g (insert p (T ∪ D)) - ZG μ W g (T ∪ D)
      = ∑ B ∈ D.powerset, ∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ := by
  have hs : ∫ x, ∑ B ∈ D.powerset, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ
      = ∑ B ∈ D.powerset, ∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ :=
    integral_finset_sum _ fun B _ => h.intp p B T
  unfold ZG
  rw [← hs, ← integral_sub (h.intZ _) (h.intZ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [Finset.prod_insert hp]
  have e : ∏ q ∈ T ∪ D, (1 + g q x)
      = (∏ q ∈ T, (1 + g q x)) * ∑ B ∈ D.powerset, ∏ q ∈ B, g q x := by
    rw [Finset.prod_union hd, Finset.prod_one_add D]
  have e2 : ∑ B ∈ D.powerset, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x
      = g p x * (∏ q ∈ T, (1 + g q x)) * (∑ B ∈ D.powerset, ∏ q ∈ B, g q x) * W x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun B _ => by ring
  rw [e, e2]
  ring

/-- **The step**: terms with fewer than `r` near factors vanish, the rest sum to `3 ε (m ε)^r` of the far mass.
DERIVED: `3` of `tail_le`. -/
theorem Gas.abs_delta (h : Gas μ W g K m r ε) (hm : 0 < m) (hmε : (m : ℝ) * ε ≤ 1) {p : ι} {T D : Finset ι}
    (hd : Disjoint T D) (hp : p ∉ T ∪ D) (hT : Disjoint T (K p)) (hD : D ⊆ K p) :
    |ZG μ W g (insert p (T ∪ D)) - ZG μ W g (T ∪ D)|
      ≤ ε * (3 * ((m : ℝ) * ε) ^ r) * ZG μ W g T := by
  have hZ := (h.ZG_pos T).le
  have hpD : p ∉ D := fun hc => hp (Finset.mem_union_right _ hc)
  rw [h.delta_expand hd hp]
  have hterm : ∀ B ∈ D.powerset,
      |∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ|
        ≤ if r ≤ B.card then ε * ZG μ W g T * ε ^ B.card else 0 := by
    intro B hB
    split_ifs with hc
    · exact (h.abs_term p B T).trans (le_of_eq (by ring))
    · rw [h.van p B T (fun hb => hpD (Finset.mem_powerset.1 hB hb)) hT (by omega), abs_zero]
  calc |∑ B ∈ D.powerset, ∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ|
      ≤ ∑ B ∈ D.powerset, |∫ x, g p x * (∏ q ∈ B, g q x) * (∏ q ∈ T, (1 + g q x)) * W x ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ B ∈ D.powerset, (if r ≤ B.card then ε * ZG μ W g T * ε ^ B.card else 0) :=
        Finset.sum_le_sum hterm
    _ = ε * ZG μ W g T * ∑ B ∈ D.powerset.filter (fun B => r ≤ B.card), ε ^ B.card := by
        rw [← Finset.sum_filter, Finset.mul_sum]
    _ ≤ ε * ZG μ W g T * (3 * ((m : ℝ) * ε) ^ r) :=
        mul_le_mul_of_nonneg_left
          (tail_le D hm ((Finset.card_le_card hD).trans (h.card_K p)) h.eps_nonneg hmε r)
          (mul_nonneg h.eps_nonneg hZ)
    _ = _ := by ring

/-- **The chain**: adding `D` to `T` loses at most `(1 − η)` per element, while the ratios hold below size `n`.
DERIVED: `1` the unit of the ratio. -/
theorem Gas.chain {n : ℕ} {η : ℝ} (hη : η ≤ 1)
    (ih : ∀ S : Finset ι, S.card < n → ∀ q, q ∉ S →
      |ZG μ W g (insert q S) - ZG μ W g S| ≤ η * ZG μ W g S)
    (T D : Finset ι) (hd : Disjoint T D) (hc : T.card + D.card ≤ n) :
    (1 - η) ^ D.card * ZG μ W g T ≤ ZG μ W g (T ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert q D hq IH =>
    obtain ⟨hqT, hd'⟩ := Finset.disjoint_insert_right.1 hd
    rw [Finset.card_insert_of_notMem hq] at hc ⊢
    have hI := IH hd' (by omega)
    have hS : (T ∪ D).card < n := by
      rw [Finset.card_union_of_disjoint hd']; omega
    have hqS : q ∉ T ∪ D := fun hm => (Finset.mem_union.1 hm).elim hqT hq
    have hr := (abs_le.1 (ih _ hS q hqS)).1
    rw [Finset.union_insert]
    have h1 : 0 ≤ 1 - η := by linarith
    calc (1 - η) ^ (D.card + 1) * ZG μ W g T
        = (1 - η) * ((1 - η) ^ D.card * ZG μ W g T) := by ring
      _ ≤ (1 - η) * ZG μ W g (T ∪ D) := mul_le_mul_of_nonneg_left hI h1
      _ ≤ _ := by linarith

/-- **The ratio**: `|Z(A ∪ p) − Z(A)| ≤ η Z(A)` at every `A ∌ p`, `η = 6 ε (m ε)^r`, for `m η ≤ 1/2`. The induction on
`|A|`: the far mass `Z(A ∖ K p)` is at most `2 Z(A)`, by the ratios below `A`. No sum over connected sets enters.
DERIVED: `6 = 2 · 3`, `2` from `(1 − η)^m ≥ 1/2`; `3` of `tail_le`. -/
theorem Gas.ratio (h : Gas μ W g K m r ε) (hm : 0 < m) (hmε : (m : ℝ) * ε ≤ 1) {η : ℝ}
    (hη : η = 6 * ε * ((m : ℝ) * ε) ^ r) (hmη : (m : ℝ) * η ≤ 1 / 2) :
    ∀ (A : Finset ι) (p : ι), p ∉ A → |ZG μ W g (insert p A) - ZG μ W g A| ≤ η * ZG μ W g A := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε0 := h.eps_nonneg
  have hη0 : 0 ≤ η := by
    rw [hη]
    positivity
  have hη1 : η ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hmR hη0
    linarith
  have key : ∀ (k : ℕ) (A : Finset ι), A.card = k → ∀ p, p ∉ A →
      |ZG μ W g (insert p A) - ZG μ W g A| ≤ η * ZG μ W g A := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro A hk p hp
      have hd : Disjoint (A \ K p) (A ∩ K p) := Finset.disjoint_sdiff_inter _ _
      have hU : (A \ K p) ∪ (A ∩ K p) = A := Finset.sdiff_union_inter _ _
      have hcard : (A \ K p).card + (A ∩ K p).card ≤ A.card := by
        have := Finset.card_union_of_disjoint hd
        rw [hU] at this
        omega
      have hc := Gas.chain (μ := μ) (W := W) (g := g) hη1 (n := A.card)
        (fun S hS q hq => IH S.card (by omega) S rfl q hq) _ _ hd hcard
      rw [hU] at hc
      have hDm : (A ∩ K p).card ≤ m :=
        (Finset.card_le_card Finset.inter_subset_right).trans (h.card_K p)
      have hb : (1 / 2 : ℝ) ≤ (1 - η) ^ (A ∩ K p).card := by
        have hB := one_add_mul_le_pow (a := -η) (by linarith) (A ∩ K p).card
        have hDR : ((A ∩ K p).card : ℝ) ≤ m := by exact_mod_cast hDm
        have hp2 := mul_le_mul_of_nonneg_right hDR hη0
        rw [show (1 : ℝ) + -η = 1 - η by ring] at hB
        linarith
      have hZT := (h.ZG_pos (A \ K p)).le
      have hfar : ZG μ W g (A \ K p) ≤ 2 * ZG μ W g A := by
        have := mul_le_mul_of_nonneg_right hb hZT
        linarith
      have hstep := h.abs_delta hm hmε hd (by rwa [hU]) Finset.sdiff_disjoint Finset.inter_subset_right
      rw [hU] at hstep
      have hc0 : 0 ≤ ε * (3 * ((m : ℝ) * ε) ^ r) := by positivity
      calc _ ≤ ε * (3 * ((m : ℝ) * ε) ^ r) * ZG μ W g (A \ K p) := hstep
        _ ≤ ε * (3 * ((m : ℝ) * ε) ^ r) * (2 * ZG μ W g A) := mul_le_mul_of_nonneg_left hfar hc0
        _ = η * ZG μ W g A := by rw [hη]; ring
  exact fun A p hp => key _ A rfl p hp

/-- **The extensive bound**: `|log Z(A) − log Z(∅)| ≤ 2 η |A|`. DERIVED: `2` of `LayerSplit.abs_log_one_add_le`;
`1/2` its range. -/
theorem Gas.abs_log_le (h : Gas μ W g K m r ε) {η : ℝ} (hη : η ≤ 1 / 2)
    (hr : ∀ (A : Finset ι) (p : ι), p ∉ A → |ZG μ W g (insert p A) - ZG μ W g A| ≤ η * ZG μ W g A)
    (A : Finset ι) :
    |Real.log (ZG μ W g A) - Real.log (ZG μ W g ∅)| ≤ 2 * η * A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert p A hp IH =>
    have hZ := h.ZG_pos A
    set x : ℝ := (ZG μ W g (insert p A) - ZG μ W g A) / ZG μ W g A with hx
    have hxη : |x| ≤ η := by
      rw [hx, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
      exact hr A p hp
    have e : ZG μ W g (insert p A) = ZG μ W g A * (1 + x) := by
      rw [hx, mul_add, mul_one, mul_div_cancel₀ _ hZ.ne']
      ring
    have hx1 : 0 < 1 + x := by
      have := (abs_le.1 hxη).1
      linarith
    have hl := LayerSplit.abs_log_one_add_le (hxη.trans hη)
    rw [e, Real.log_mul hZ.ne' hx1.ne', Finset.card_insert_of_notMem hp]
    push_cast
    have hab := abs_le.1 hl
    have hIH := abs_le.1 IH
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [hab.1, hab.2, hIH.1, hIH.2]

end Gas

/-! ## 3. The tilt, and the dependency-graph bound -/

/-- **The tilted variable is bounded by its range**: `|u| ≤ a`, `e^{−a} ≤ T ≤ e^{a}`, `2 a ≤ 1` give
`|e^u/T − 1| ≤ 4 a`. DERIVED: `2` of `Real.abs_exp_sub_one_le` and the sum `|u| + |log T|`; `4 = 2 · 2`. -/
theorem abs_tilt_le {u T a : ℝ} (hu : |u| ≤ a) (h1 : Real.exp (-a) ≤ T) (h2 : T ≤ Real.exp a)
    (ha : 2 * a ≤ 1) : |Real.exp u / T - 1| ≤ 4 * a := by
  have hT : 0 < T := lt_of_lt_of_le (Real.exp_pos _) h1
  have e : Real.exp u / T = Real.exp (u - Real.log T) := by
    rw [Real.exp_sub, Real.exp_log hT]
  have hl1 : -a ≤ Real.log T := (Real.le_log_iff_exp_le hT).2 h1
  have hl2 : Real.log T ≤ a := (Real.log_le_iff_le_exp hT).2 h2
  have hb := abs_le.1 hu
  have hy : |u - Real.log T| ≤ 2 * a := abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
  rw [e]
  have := Real.abs_exp_sub_one_le (hy.trans ha)
  linarith

/-- **The mean of `e^f` lies in the range of `e^f`**. DERIVED: `1` the mass of a probability measure. -/
theorem tilt_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hI : Integrable (fun x => Real.exp (f x)) μ) {a : ℝ} (hf : ∀ x, |f x| ≤ a) :
    Real.exp (-a) ≤ ∫ x, Real.exp (f x) ∂μ ∧ ∫ x, Real.exp (f x) ∂μ ≤ Real.exp a := by
  constructor
  · calc Real.exp (-a) = ∫ _x, Real.exp (-a) ∂μ := (ContactFloor.integral_const_prob μ _).symm
      _ ≤ _ := integral_mono (integrable_const _) hI fun x =>
        Real.exp_le_exp.2 (by linarith [(abs_le.1 (hf x)).1])
  · calc ∫ x, Real.exp (f x) ∂μ ≤ ∫ _x, Real.exp a ∂μ :=
        integral_mono hI (integrable_const _) fun x =>
          Real.exp_le_exp.2 (by linarith [(abs_le.1 (hf x)).2])
      _ = _ := ContactFloor.integral_const_prob μ _

theorem bdd_prod {Ω ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ} (h : ∀ q, ∃ C, ∀ x, |f q x| ≤ C) :
    ∃ C, ∀ x, |∏ q ∈ s, f q x| ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert q s hq ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨C', hC'⟩ := h q
    refine ⟨C' * C, fun x => ?_⟩
    rw [Finset.prod_insert hq, abs_mul]
    exact mul_le_mul (hC' x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hC' x))

/-- **The dependency-graph bound for real `z`.** Let `|X_p| ≤ M`, `D > 0`, let `Nb p` have at most `D` members, and let `X_p`
be independent of `(X_q)_{q ∈ F}` for every `F` disjoint from `Nb p`. The hypothesis forces `X_p` to be constant unless `p ∈ Nb p`. For `16 D |z| M ≤ 1`,
`|log E e^{z S} − Σ_p log E e^{z X_p}| ≤ 192 |I| D z² M²`. The real form of the extensive bound of Janson (1988) and
Féray–Méliot–Nikeghbali (2016), proved here by `Gas.ratio` at `r = 1`; neither theorem is an input. DERIVED: `4` of
`abs_tilt_le`; `1` the vanishing order. COMPUTED: `16 = 4 · 4`, so `D ε ≤ 1/4` and `D η = 6 (D ε)² ≤ 1/2`;
`192 = 2 · 6 · 16`. -/
theorem dependency_cgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hX : ∀ p, Measurable (X p)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p ω, |X p ω| ≤ M) (Nb : ι → Finset ι) {D : ℕ} (hD0 : 0 < D) (hD : ∀ p, (Nb p).card ≤ D)
    (hind : ∀ (p : ι) (F : Finset ι), Disjoint F (Nb p) →
      ProbabilityTheory.IndepFun (X p) (fun ω (q : F) => X q ω) μ)
    {z : ℝ} (hz : 16 * (D : ℝ) * |z| * M ≤ 1) :
    |Real.log (∫ ω, Real.exp (z * ∑ p, X p ω) ∂μ) - ∑ p, Real.log (∫ ω, Real.exp (z * X p ω) ∂μ)|
      ≤ 192 * (Fintype.card ι : ℝ) * D * z ^ 2 * M ^ 2 := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD0
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = |z| * M := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hDa : (D : ℝ) * a ≤ 1 / 16 := by
    rw [ha]
    linarith
  have ha1 : a ≤ 1 / 16 := by
    have := mul_le_mul_of_nonneg_right hDR ha0
    linarith
  have hIgen : ∀ f : Ω → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → Integrable f μ := by
    rintro f hf ⟨C, hC⟩
    exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have hzX : ∀ p ω, |z * X p ω| ≤ a := fun p ω => by
    rw [abs_mul, ha]
    exact mul_le_mul_of_nonneg_left (hb p ω) (abs_nonneg _)
  have hmE : ∀ p, Measurable fun ω => Real.exp (z * X p ω) := fun p =>
    Real.measurable_exp.comp ((hX p).const_mul z)
  have hIE : ∀ p, Integrable (fun ω => Real.exp (z * X p ω)) μ := fun p =>
    hIgen _ (hmE p) ⟨Real.exp a, fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hzX p ω))⟩
  obtain ⟨T, hT⟩ : ∃ T : ι → ℝ, T = fun p => ∫ ω, Real.exp (z * X p ω) ∂μ := ⟨_, rfl⟩
  have hTv : ∀ p, T p = ∫ ω, Real.exp (z * X p ω) ∂μ := fun p => by rw [hT]
  have hTb : ∀ p, Real.exp (-a) ≤ T p ∧ T p ≤ Real.exp a := fun p => by
    rw [hTv]
    exact tilt_bounds (hIE p) (hzX p)
  have hTpos : ∀ p, 0 < T p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hTb p).1
  obtain ⟨g, hg⟩ : ∃ g : ι → Ω → ℝ, g = fun p ω => Real.exp (z * X p ω) / T p - 1 := ⟨_, rfl⟩
  have hgv : ∀ p ω, g p ω = Real.exp (z * X p ω) / T p - 1 := fun p ω => by rw [hg]
  have hgm : ∀ p, Measurable (g p) := fun p => by
    rw [hg]
    exact ((hmE p).div_const _).sub_const 1
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 4 * a := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; linarith
  have hgb : ∀ p ω, |g p ω| ≤ ε := fun p ω => by
    rw [hgv, hε]
    exact abs_tilt_le (hzX p ω) (hTb p).1 (hTb p).2 (by linarith)
  have hgC : ∀ q, ∃ C, ∀ x, |g q x| ≤ C := fun q => ⟨ε, hgb q⟩
  have hgC1 : ∀ q, ∃ C, ∀ x, |1 + g q x| ≤ C := fun q =>
    ⟨1 + ε, fun x => (abs_add_le _ _).trans (by rw [abs_one]; linarith [hgb q x])⟩
  have hgas : Gas μ (fun _ => 1) g Nb D 1 ε := by
    refine ⟨fun _ => zero_le_one, by simp, hε0, by rw [hε]; linarith, hgb, ?_, ?_, hD, ?_⟩
    · intro B F
      obtain ⟨C1, h1⟩ := bdd_prod B hgC
      obtain ⟨C2, h2⟩ := bdd_prod F hgC1
      refine hIgen _ (((Finset.measurable_prod _ fun q _ => hgm q).mul
        (Finset.measurable_prod _ fun q _ => (hgm q).const_add 1)).mul measurable_const)
        ⟨C1 * C2, fun x => ?_⟩
      show |(∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * 1| ≤ _
      rw [mul_one, abs_mul]
      exact mul_le_mul (h1 x) (h2 x) (abs_nonneg _) ((abs_nonneg _).trans (h1 x))
    · intro p B F
      obtain ⟨C1, h1⟩ := bdd_prod B hgC
      obtain ⟨C2, h2⟩ := bdd_prod F hgC1
      refine hIgen _ ((((hgm p).mul (Finset.measurable_prod _ fun q _ => hgm q)).mul
        (Finset.measurable_prod _ fun q _ => (hgm q).const_add 1)).mul measurable_const)
        ⟨ε * C1 * C2, fun x => ?_⟩
      show |g p x * (∏ q ∈ B, g q x) * (∏ q ∈ F, (1 + g q x)) * 1| ≤ _
      rw [mul_one, abs_mul, abs_mul]
      have hnn : 0 ≤ C1 := (abs_nonneg _).trans (h1 x)
      exact mul_le_mul (mul_le_mul (hgb p x) (h1 x) (abs_nonneg _) hε0) (h2 x)
        (abs_nonneg _) (mul_nonneg hε0 hnn)
    · intro p B F _ hF hB
      obtain rfl : B = ∅ := Finset.card_eq_zero.1 (by omega)
      have hφm : Measurable fun u : ℝ => Real.exp (z * u) / T p - 1 :=
        ((Real.measurable_exp.comp (measurable_id.const_mul z)).div_const _).sub_const 1
      have hψm : Measurable fun v : F → ℝ => ∏ q : F, (1 + (Real.exp (z * v q) / T q - 1)) :=
        Finset.measurable_prod _ fun q _ => by fun_prop
      have hrm : Measurable fun ω => fun q : F => X q ω :=
        measurable_pi_lambda _ fun q => hX q
      have key : ∫ ω, (Real.exp (z * X p ω) / T p - 1)
            * (∏ q : F, (1 + (Real.exp (z * X q ω) / T q - 1))) ∂μ
          = (∫ ω, (Real.exp (z * X p ω) / T p - 1) ∂μ)
            * ∫ ω, (∏ q : F, (1 + (Real.exp (z * X q ω) / T q - 1))) ∂μ :=
        ((hind p F hF).comp hφm hψm).integral_fun_mul_eq_mul_integral
          (hφm.comp (hX p)).aestronglyMeasurable (hψm.comp hrm).aestronglyMeasurable
      have h0 : ∫ ω, (Real.exp (z * X p ω) / T p - 1) ∂μ = 0 := by
        rw [integral_sub ((hIE p).div_const _) (integrable_const _), integral_div,
          ContactFloor.integral_const_prob, ← hTv, div_self (hTpos p).ne', sub_self]
      rw [h0, zero_mul] at key
      refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans key
      have e : ∏ q : F, (1 + (Real.exp (z * X q ω) / T q - 1)) = ∏ q ∈ F, (1 + g q ω) := by
        rw [Finset.prod_coe_sort F fun q => 1 + (Real.exp (z * X q ω) / T q - 1)]
        exact Finset.prod_congr rfl fun q _ => by rw [hgv]
      simp only [Finset.prod_empty, mul_one]
      rw [e, hgv]
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 6 * ε * ((D : ℝ) * ε) ^ 1 := ⟨_, rfl⟩
  have hDε : (D : ℝ) * ε ≤ 1 / 4 := by rw [hε]; linarith
  have hDε0 : 0 ≤ (D : ℝ) * ε := mul_nonneg (by linarith) hε0
  have hmη : (D : ℝ) * η ≤ 1 / 2 := by
    have e : (D : ℝ) * η = 6 * ((D : ℝ) * ε) ^ 2 := by rw [hηdef]; ring
    rw [e]
    nlinarith
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hη1 : η ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hDR hη0
    linarith
  have hr := hgas.ratio hD0 (by linarith) hηdef hmη
  have hl := hgas.abs_log_le hη1 hr Finset.univ
  have hZ0 : ZG μ (fun _ => 1) g (∅ : Finset ι) = 1 := by
    unfold ZG
    simp
  have hPne : ∏ p, T p ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => (hTpos p).ne'
  have hZu : ∫ ω, Real.exp (z * ∑ p, X p ω) ∂μ = (∏ p, T p) * ZG μ (fun _ => 1) g Finset.univ := by
    unfold ZG
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hgv, add_sub_cancel, mul_one]
    rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.mul_sum]
    field_simp
  have hZpos := hgas.ZG_pos Finset.univ
  rw [hZ0, Real.log_one, sub_zero, Finset.card_univ] at hl
  have hTs : ∀ p, Real.log (∫ ω, Real.exp (z * X p ω) ∂μ) = Real.log (T p) := fun p => by rw [hTv]
  simp only [hTs]
  rw [hZu, Real.log_mul hPne hZpos.ne', Real.log_prod (fun p _ => (hTpos p).ne')]
  have e1 : ∀ c : ℝ, (∑ p, Real.log (T p)) + c - ∑ p, Real.log (T p) = c := fun c => by ring
  rw [e1]
  refine hl.trans (le_of_eq ?_)
  have hz2 : a ^ 2 = z ^ 2 * M ^ 2 := by rw [ha, mul_pow, sq_abs]
  rw [hηdef, hε]
  linear_combination (192 * (Fintype.card ι : ℝ) * D) * hz2

/-! ## 4. The corners of the normal mixed plaquettes -/

/-- The normal mixed plaquettes: an orientation of each block, and a base. No numeral. -/
abbrev Pm (n : ℕ) : Type := (Fin 2 × Fin 2) × St n

/-- The plaquette of the lattice. No numeral. -/
def pl {n : ℕ} (p : Pm n) : Pq n := ((dirLo p.1.1, dirHi p.1.2), p.2)

/-- `z` is a corner of `p`. No numeral. -/
def Cn {n : ℕ} (p : Pm n) (z : St n) : Prop := IsCorner n (dirLo p.1.1) (dirHi p.1.2) p.2 z

/-- Two plaquettes touch when they share a corner. No numeral. -/
def Touch {n : ℕ} (p q : Pm n) : Prop := ∃ z, Cn p z ∧ Cn q z

theorem pl_inj {n : ℕ} {p q : Pm n} (h : pl p = pl q) : p = q := by
  obtain ⟨⟨a, b⟩, y⟩ := p
  obtain ⟨⟨a', b'⟩, y'⟩ := q
  simp only [pl, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have e1 : a = a' := Fin.ext (by simpa [dirLo] using congrArg Fin.val h1)
  have e2 : b = b' := Fin.ext (by simpa [dirHi] using congrArg Fin.val h2)
  rw [e1, e2, h3]

theorem touch_self {n : ℕ} (p : Pm n) : Touch p p := ⟨p.2, Or.inl rfl, Or.inl rfl⟩

/-- **The private corner of `MixExpand.exists_private`, on `Pm`.** DERIVED: `3` the least extent; `2` the parity. -/
theorem priv3 {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (p q r : Pm n) (hne : ¬ (p = q ∧ q = r)) :
    ∃ z, (Cn p z ∧ ¬ Cn q z ∧ ¬ Cn r z) ∨ (Cn q z ∧ ¬ Cn p z ∧ ¬ Cn r z) ∨
      (Cn r z ∧ ¬ Cn p z ∧ ¬ Cn q z) :=
  exists_private hn he (dirLo_block _) (dirHi_block _) (dirLo_block _) (dirHi_block _) (dirLo_block _)
    (dirHi_block _) p.2 q.2 r.2 fun h => hne ⟨pl_inj h.1, pl_inj h.2⟩

theorem priv2 {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) {p q : Pm n} (hne : p ≠ q) : ∃ z, Cn p z ∧ ¬ Cn q z := by
  obtain ⟨z, h | h | h⟩ := priv3 hn he p q q fun h => hne h.1
  · exact ⟨z, h.1, h.2.1⟩
  · exact absurd h.1 h.2.2
  · exact absurd h.1 h.2.2

/-- The site one step back in direction `i`. DERIVED: `1` the step. -/
def bk {n : ℕ} (i : Fin 4) (z : St n) : St n := Function.update z i ((finRotate n).symm (z i))

theorem bk_rshift {n : ℕ} (i : Fin 4) (y : St n) : bk i (rshift (fun _ => n) i y) = y := by
  funext k
  unfold bk rshift
  by_cases h : k = i
  · subst h
    simp only [Function.update_self, Equiv.symm_apply_apply]
  · simp [Function.update_of_ne h]

/-- The four sites of `p`, read as bases of the plaquettes at `z`. DERIVED: `4` the corners. -/
def bw {n : ℕ} (k : Fin 2 × Fin 2) (z : St n) : Fin 4 → St n :=
  ![z, bk (dirLo k.1) z, bk (dirHi k.2) z, bk (dirHi k.2) (bk (dirLo k.1) z)]

/-- The four corners of `p`. DERIVED: `4` the corners. -/
def fw {n : ℕ} (p : Pm n) : Fin 4 → St n :=
  ![p.2, rshift (fun _ => n) (dirLo p.1.1) p.2, rshift (fun _ => n) (dirHi p.1.2) p.2,
    rshift (fun _ => n) (dirLo p.1.1) (rshift (fun _ => n) (dirHi p.1.2) p.2)]

/-- The plaquettes with corner `z`. DERIVED: `4` the corners. -/
def star {n : ℕ} (z : St n) : Finset (Pm n) :=
  (Finset.univ : Finset ((Fin 2 × Fin 2) × Fin 4)).image fun c => (c.1, bw c.1 z c.2)

theorem card_star_le {n : ℕ} (z : St n) : (star z).card ≤ 16 :=
  Finset.card_image_le.trans (by simp [Fintype.card_prod])

theorem mem_star {n : ℕ} {p : Pm n} {z : St n} (h : Cn p z) : p ∈ star z := by
  obtain ⟨k, y⟩ := p
  refine Finset.mem_image.2 ?_
  rcases h with h | h | h | h
  · exact ⟨(k, 0), Finset.mem_univ _, by simp [bw, h]⟩
  · exact ⟨(k, 1), Finset.mem_univ _, by simp [bw, h, bk_rshift]⟩
  · exact ⟨(k, 2), Finset.mem_univ _, by simp [bw, h, bk_rshift]⟩
  · exact ⟨(k, 3), Finset.mem_univ _, by simp [bw, h, bk_rshift]⟩

open scoped Classical in
/-- The plaquettes touching `p`, itself included. No numeral. -/
noncomputable def Tch {n : ℕ} (p : Pm n) : Finset (Pm n) := Finset.univ.filter (Touch p)

theorem mem_Tch {n : ℕ} {p q : Pm n} : q ∈ Tch p ↔ Touch p q := by
  classical
  simp [Tch]

theorem card_Tch_le {n : ℕ} (p : Pm n) : (Tch p).card ≤ 64 := by
  classical
  have hs : Tch p ⊆ (Finset.univ.image (fw p)).biUnion star := by
    intro q hq
    obtain ⟨z, h1, h2⟩ := mem_Tch.1 hq
    refine Finset.mem_biUnion.2 ⟨z, Finset.mem_image.2 ?_, mem_star h2⟩
    rcases h1 with h | h | h | h
    · exact ⟨0, Finset.mem_univ _, by simp [fw, h]⟩
    · exact ⟨1, Finset.mem_univ _, by simp [fw, h]⟩
    · exact ⟨2, Finset.mem_univ _, by simp [fw, h]⟩
    · exact ⟨3, Finset.mem_univ _, by simp [fw, h]⟩
  refine (Finset.card_le_card hs).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ 16 fun z _ => card_star_le z).trans ?_
  have : (Finset.univ.image (fw p)).card ≤ 4 := Finset.card_image_le.trans (by simp)
  omega

/-- **The two-step neighbourhood of `p`**: the plaquettes touching one that touches `p`. No numeral. -/
noncomputable def Kk {n : ℕ} (p : Pm n) : Finset (Pm n) := (Tch p).biUnion Tch

theorem card_Kk_le {n : ℕ} (p : Pm n) : (Kk p).card ≤ 4096 := by
  unfold Kk
  refine (Finset.card_biUnion_le_card_mul _ _ 64 fun q _ => card_Tch_le q).trans ?_
  have := card_Tch_le p
  omega

/-- A plaquette outside `Kk p` sees no corner of a plaquette touching `p`. No numeral. -/
theorem not_corner_of_far {n : ℕ} {p x f : Pm n} {z : St n} (hx : Touch p x) (hz : Cn x z)
    (hf : f ∉ Kk p) : ¬ Cn f z := by
  intro hc
  apply hf
  unfold Kk
  exact Finset.mem_biUnion.2 ⟨x, mem_Tch.2 hx, mem_Tch.2 ⟨z, hz, hc⟩⟩

/-! ## 5. The vanishing -/

variable {N : ℕ}

/-- **`MixExpand.cent_move` for a function `c` of the density of Haar mean zero.** DERIVED: `0` the decoupled end and
the mean. -/
theorem cent_move_c {n : ℕ} (β : ℝ) (c : ℝ → ℝ) (hc : Continuous c)
    (h0 : ∫ g, c (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0)
    (p : Pq n) (z : St n) (G : (Lk n → SUN.SU N) → ℝ) (hG : Continuous G)
    (hGz : ∀ a U, G (gT (fun _ => n) (siteG (fun _ => n) z a) U) = G U)
    (Φ : (Lk n → SUN.SU N) → SUN.SU N) (hΦ : Continuous Φ)
    (hφ : ∀ U, plaq N n p U = WilsonAction.wilsonDensity (Φ U))
    (σ : SUN.SU N → SUN.SU N) (mf : SUN.SU N → SUN.SU N → SUN.SU N)
    (hm : Continuous fun pr : SUN.SU N × SUN.SU N => mf pr.1 pr.2)
    (hmΦ : ∀ g U, Φ (gT (fun _ => n) (siteG (fun _ => n) z (σ g)) U) = mf g (Φ U))
    (hmH : ∀ (f : SUN.SU N → ℝ) (k : SUN.SU N),
      ∫ g, f (mf g k) ∂(probHaar (SUN.SU N)) = ∫ g, f g ∂(probHaar (SUN.SU N))) :
    ∫ U, c (plaq N n p U) * G U * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
  have hE : Continuous fun U : Lk n → SUN.SU N => G U * Real.exp (-(β * sinR N n U)) :=
    hG.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg)
  have hf : Continuous fun g : SUN.SU N => c (WilsonAction.wilsonDensity g) :=
    hc.comp WilsonAction.continuous_wilsonDensity
  have key := integral_avg_gen (L := fun _ => n)
    (fun g => c (WilsonAction.wilsonDensity g)) hf
    (fun g U => gT (fun _ => n) (siteG (fun _ => n) z (σ g)) U)
    (fun g F hF => integral_gT (fun _ => n) _ F hF) Φ hΦ
    (fun U => G U * Real.exp (-(β * sinR N n U))) hE mf hm hmΦ
    (fun g U => by simp only [hGz, sinR_gT])
    (fun k => hmH (fun g => c (WilsonAction.wilsonDensity g)) k)
  rw [h0, zero_mul] at key
  refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
  simp only [hφ U]
  ring

/-- **A corner of `p` that the rest does not see centres `c(φ_p)` out**, at every `β`. `MixExpand.cent_factor` for a
function of the density. DERIVED: `2` the least extent; `0` the decoupled end. -/
theorem cent_factor_c {n : ℕ} (hn : 2 ≤ n) (β : ℝ) (c : ℝ → ℝ) (hc : Continuous c)
    (h0 : ∫ g, c (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0)
    {i j : Fin 4} (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y z : St n) (hz : IsCorner n i j y z) (G : (Lk n → SUN.SU N) → ℝ) (hG : Continuous G)
    (hGz : ∀ a U, G (gT (fun _ => n) (siteG (fun _ => n) z a) U) = G U) :
    ∫ U, c (plaq N n ((i, j), y) U) * G U * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  rcases hz with h | h | h | h <;> rw [h] at hGz
  · exact cent_move_c β c hc h0 _ y G hG hGz (fun U => (sysR (fun _ => n) N).hol ((i, j), y) U)
      (MixAnchor.continuous_hol _) (fun U => rfl) (fun g => g) (fun g k => g * k) continuous_mul
      (fun g U => hol_gT_mixA (fun _ => n) hL g U hi hj y)
      (fun f k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move_c β c hc h0 _ _ G hG hGz (psiI i j y) (continuous_psiI i j y) (plaq_eq_psiI i j y)
      (fun g => g⁻¹) (fun g k => k * g) (continuous_snd.mul continuous_fst)
      (fun g U => by rw [psiI_gT hn hi hj y g⁻¹ U, inv_inv])
      (fun f k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move_c β c hc h0 _ _ G hG hGz (psiJ i j y) (continuous_psiJ i j y) (plaq_eq_psiJ i j y)
      (fun g => g⁻¹) (fun g k => k * g) (continuous_snd.mul continuous_fst)
      (fun g U => by rw [psiJ_gT hn hi hj y g⁻¹ U, inv_inv])
      (fun f k => integral_mul_left_eq_self (μ := probHaar (SUN.SU N)) f k)
  · exact cent_move_c β c hc h0 _ _ G hG hGz (psiK i j y) (continuous_psiK i j y) (plaq_eq_psiK i j y)
      (fun g => g) (fun g k => g * k) continuous_mul (fun g U => psiK_gT hn hi hj y g U)
      (fun f k => integral_mul_right_eq_self (μ := probHaar (SUN.SU N)) f k)

/-- The tilted plaquette. No numeral. -/
noncomputable def gg (N n : ℕ) (c : ℝ → ℝ) (p : Pm n) (U : Lk n → SUN.SU N) : ℝ := c (plaq N n (pl p) U)

theorem continuous_gg (n : ℕ) {c : ℝ → ℝ} (hc : Continuous c) (p : Pm n) :
    Continuous (gg N n c p) :=
  hc.comp (continuous_plaq n _)

theorem gg_off {n : ℕ} (c : ℝ → ℝ) (p : Pm n) (z : St n) (a : SUN.SU N) (U : Lk n → SUN.SU N)
    (h : ¬ Cn p z) : gg N n c p (gT (fun _ => n) (siteG (fun _ => n) z a) U) = gg N n c p U := by
  unfold gg pl
  rw [plaq_gT_off (dirLo_block _) (dirHi_block _) p.2 z a U h]

/-- **A private corner kills a term**: if `x ∈ A`, `z` is a corner of `x` and of nothing else in `A` or in `F`, the
integral of `Π_A g · Π_F (1 + g)` against `e^{−β S_in}` vanishes. DERIVED: `2` the least extent; `0` the vanishing. -/
theorem van_priv {n : ℕ} (hn : 2 ≤ n) (β : ℝ) {c : ℝ → ℝ} (hc : Continuous c)
    (h0 : ∫ g, c (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0)
    (A F : Finset (Pm n)) {x : Pm n} (hx : x ∈ A) {z : St n} (hz : Cn x z)
    (hA : ∀ y ∈ A, y ≠ x → ¬ Cn y z) (hF : ∀ f ∈ F, ¬ Cn f z) :
    ∫ U, (∏ q ∈ A, gg N n c q U) * (∏ q ∈ F, (1 + gg N n c q U)) * Real.exp (-(β * sinR N n U)) ∂piH N n
      = 0 := by
  have hG : Continuous fun U : Lk n → SUN.SU N =>
      (∏ q ∈ A.erase x, gg N n c q U) * ∏ q ∈ F, (1 + gg N n c q U) :=
    (continuous_finsetProd _ fun q _ => continuous_gg n hc q).mul
      (continuous_finsetProd _ fun q _ => continuous_const.add (continuous_gg n hc q))
  have key := cent_factor_c (N := N) hn β c hc h0 (dirLo_block x.1.1) (dirHi_block x.1.2) x.2 z hz _ hG
    (fun a U => by
      show (∏ q ∈ A.erase x, gg N n c q (gT (fun _ => n) (siteG (fun _ => n) z a) U))
          * (∏ q ∈ F, (1 + gg N n c q (gT (fun _ => n) (siteG (fun _ => n) z a) U)))
        = (∏ q ∈ A.erase x, gg N n c q U) * ∏ q ∈ F, (1 + gg N n c q U)
      congr 1
      · exact Finset.prod_congr rfl fun q hq =>
          gg_off c q z a U (hA q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq))
      · exact Finset.prod_congr rfl fun q hq => by rw [gg_off c q z a U (hF q hq)])
  refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
  have e : gg N n c x U * ∏ q ∈ A.erase x, gg N n c q U = ∏ q ∈ A, gg N n c q U :=
    Finset.mul_prod_erase A (fun q => gg N n c q U) hx
  have e' : gg N n c x U = c (plaq N n ((dirLo x.1.1, dirHi x.1.2), x.2) U) := rfl
  rw [← e, e']
  ring

/-- **The terms with at most two near factors vanish.** Far plaquettes see no corner of `p` or of a neighbour of `p`,
and `MixExpand.exists_private` gives a private corner among `p` and at most two more. DERIVED: `3` the least extent
and the first surviving order; `2` the parity. -/
theorem van3 {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) {c : ℝ → ℝ} (hc : Continuous c)
    (h0 : ∫ g, c (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0)
    (p : Pm n) (B F : Finset (Pm n)) (hpB : p ∉ B) (hF : Disjoint F (Kk p)) (hB : B.card < 3) :
    ∫ U, gg N n c p U * (∏ q ∈ B, gg N n c q U) * (∏ q ∈ F, (1 + gg N n c q U))
        * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
  have hn2 : 2 ≤ n := by omega
  have pick : ∀ (x : Pm n) (z : St n), x ∈ insert p B → Touch p x → Cn x z →
      (∀ y ∈ insert p B, y ≠ x → ¬ Cn y z) →
      ∫ U, gg N n c p U * (∏ q ∈ B, gg N n c q U) * (∏ q ∈ F, (1 + gg N n c q U))
        * Real.exp (-(β * sinR N n U)) ∂piH N n = 0 := by
    intro x z hx ht hz hA
    have key := van_priv (N := N) hn2 β hc h0 (insert p B) F hx hz hA
      fun f hf => not_corner_of_far ht hz (Finset.disjoint_left.1 hF hf)
    refine (integral_congr_ae (Eventually.of_forall fun U => ?_)).trans key
    rw [Finset.prod_insert hpB]
  have hcases : B = ∅ ∨ (∃ q, B = {q}) ∨ (∃ q r, q ≠ r ∧ B = {q, r}) := by
    have : B.card = 0 ∨ B.card = 1 ∨ B.card = 2 := by omega
    rcases this with h | h | h
    · exact Or.inl (Finset.card_eq_zero.1 h)
    · exact Or.inr (Or.inl (Finset.card_eq_one.1 h))
    · exact Or.inr (Or.inr (Finset.card_eq_two.1 h))
  rcases hcases with rfl | ⟨q, rfl⟩ | ⟨q, r, hqr, rfl⟩
  · refine pick p p.2 (Finset.mem_insert_self _ _) (touch_self p) (Or.inl rfl) fun y hy hne => ?_
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hy
    exact absurd hy hne
  · have hpq : p ≠ q := fun h => hpB (by simp [h])
    obtain ⟨z, h1, h2⟩ := priv2 hn he hpq
    refine pick p z (Finset.mem_insert_self _ _) (touch_self p) h1 fun y hy hne => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy
    · exact absurd hy hne
    · rw [hy]; exact h2
  · have hpq : p ≠ q := fun h => hpB (by simp [h])
    have hpr : p ≠ r := fun h => hpB (by simp [h])
    by_cases t1 : Touch p q
    · by_cases t2 : Touch p r
      · obtain ⟨z, h | h | h⟩ := priv3 hn he p q r fun h => hpq h.1
        · refine pick p z (by simp) (touch_self p) h.1 fun y hy hne => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hy | hy | hy
          · exact absurd hy hne
          · rw [hy]; exact h.2.1
          · rw [hy]; exact h.2.2
        · refine pick q z (by simp) t1 h.1 fun y hy hne => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hy | hy | hy
          · rw [hy]; exact h.2.1
          · exact absurd hy hne
          · rw [hy]; exact h.2.2
        · refine pick r z (by simp) t2 h.1 fun y hy hne => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hy | hy | hy
          · rw [hy]; exact h.2.1
          · rw [hy]; exact h.2.2
          · exact absurd hy hne
      · obtain ⟨z, h1, h2⟩ := priv2 hn he hpq
        refine pick p z (by simp) (touch_self p) h1 fun y hy hne => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with hy | hy | hy
        · exact absurd hy hne
        · rw [hy]; exact h2
        · rw [hy]; exact fun hc' => t2 ⟨z, h1, hc'⟩
    · obtain ⟨z, h1, h2⟩ := priv2 hn he hpr
      refine pick p z (by simp) (touch_self p) h1 fun y hy hne => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy
      · exact absurd hy hne
      · rw [hy]; exact fun hc' => t1 ⟨z, h1, hc'⟩
      · rw [hy]; exact h2

/-- **The gas of the normal mixed plaquettes** at the decoupled weight, for any `c` of Haar mean zero bounded by
`ε ≤ 1/2`. DERIVED: `4096`, `3` of `card_Kk_le`, `van3`; `0` the decoupled end. -/
theorem gas_mixed {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) {c : ℝ → ℝ} (hc : Continuous c)
    (h0 : ∫ g, c (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hb : ∀ (p : Pm n) U, |gg N n c p U| ≤ ε) :
    Gas (piH N n) (fun U => Real.exp (-(β * sinR N n U))) (gg N n c) Kk 4096 3 ε := by
  have hW : Continuous fun U : Lk n → SUN.SU N => Real.exp (-(β * sinR N n U)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_sinR n)).neg
  have hP : ∀ B : Finset (Pm n), Continuous fun U : Lk n → SUN.SU N => ∏ q ∈ B, gg N n c q U :=
    fun B => continuous_finsetProd _ fun q _ => continuous_gg n hc q
  have hP1 : ∀ B : Finset (Pm n), Continuous fun U : Lk n → SUN.SU N => ∏ q ∈ B, (1 + gg N n c q U) :=
    fun B => continuous_finsetProd _ fun q _ => continuous_const.add (continuous_gg n hc q)
  refine ⟨fun _ => (Real.exp_pos _).le, ?_, hε0, hε, hb, fun B F => hint (((hP B).mul (hP1 F)).mul hW),
    fun p B F => hint ((((continuous_gg n hc p).mul (hP B)).mul (hP1 F)).mul hW), card_Kk_le,
    fun p B F hpB hF hB => van3 hn he β hc h0 p B F hpB hF hB⟩
  have h := ZA_pos (N := N) β 0 n
  rw [ZA_eq_int] at h
  simpa using h

/-! ## 6. The extensive form of `log Z` -/

/-- **The tilt of one plaquette, normalized**: `c_t(x) = e^{−2t (x − ⟨φ⟩)}/H(−2t) − 1`. DERIVED: `2` the orientations
of a plaquette; `1` the normalization. -/
noncomputable def cT (N : ℕ) (t x : ℝ) : ℝ :=
  Real.exp (-(2 * t) * (x - WindowRead.haarMeanN N)) / haarTilt N (-(2 * t)) - 1

theorem continuous_cT (N : ℕ) (t : ℝ) : Continuous (cT N t) := by
  unfold cT
  fun_prop

theorem haarMean_mem (hN : N ≠ 0) : 0 ≤ WindowRead.haarMeanN N ∧ WindowRead.haarMeanN N ≤ 2 := by
  have hI : Integrable (WilsonAction.wilsonDensity (N := N)) (probHaar (SUN.SU N)) :=
    WilsonAction.continuous_wilsonDensity.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold WindowRead.haarMeanN
  constructor
  · exact integral_nonneg fun g => WilsonAction.wilsonDensity_nonneg hN g
  · calc ∫ g, WilsonAction.wilsonDensity (N := N) g ∂(probHaar (SUN.SU N))
        ≤ ∫ _g, (2 : ℝ) ∂(probHaar (SUN.SU N)) :=
          integral_mono hI (integrable_const _) fun g => WilsonAction.wilsonDensity_le_two hN g
      _ = 2 := ContactFloor.integral_const_prob _ _

theorem abs_tilt_range (hN : N ≠ 0) (t : ℝ) (g : SUN.SU N) :
    |-(2 * t) * (WilsonAction.wilsonDensity g - WindowRead.haarMeanN N)| ≤ 4 * |t| := by
  obtain ⟨h0, h2⟩ := haarMean_mem (N := N) hN
  have h3 := WilsonAction.wilsonDensity_nonneg hN g
  have h4 := WilsonAction.wilsonDensity_le_two hN g
  have hr : |WilsonAction.wilsonDensity g - WindowRead.haarMeanN N| ≤ 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  rw [abs_mul, abs_neg, abs_mul, abs_two]
  have := mul_le_mul_of_nonneg_left hr (abs_nonneg t)
  linarith

theorem haarTilt_bounds (hN : N ≠ 0) (t : ℝ) :
    Real.exp (-(4 * |t|)) ≤ haarTilt N (-(2 * t)) ∧ haarTilt N (-(2 * t)) ≤ Real.exp (4 * |t|) := by
  have hI : Integrable (fun g : SUN.SU N => Real.exp (-(2 * t) * (WilsonAction.wilsonDensity g
      - WindowRead.haarMeanN N))) (probHaar (SUN.SU N)) :=
    (continuous_tilt (-(2 * t))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact tilt_bounds hI (abs_tilt_range hN t)

theorem haarTilt_pos (hN : N ≠ 0) (t : ℝ) : 0 < haarTilt N (-(2 * t)) :=
  lt_of_lt_of_le (Real.exp_pos _) (haarTilt_bounds hN t).1

theorem abs_cT_le (hN : N ≠ 0) {t : ℝ} (ht : 8 * |t| ≤ 1) (g : SUN.SU N) :
    |cT N t (WilsonAction.wilsonDensity g)| ≤ 16 * |t| := by
  have h := abs_tilt_le (abs_tilt_range hN t g) (haarTilt_bounds hN t).1 (haarTilt_bounds hN t).2
    (by linarith)
  unfold cT
  linarith

theorem integral_cT (hN : N ≠ 0) (t : ℝ) :
    ∫ g, cT N t (WilsonAction.wilsonDensity (N := N) g) ∂(probHaar (SUN.SU N)) = 0 := by
  have hI : Integrable (fun g : SUN.SU N => Real.exp (-(2 * t) * (WilsonAction.wilsonDensity g
      - WindowRead.haarMeanN N))) (probHaar (SUN.SU N)) :=
    (continuous_tilt (-(2 * t))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold cT
  rw [integral_sub (hI.div_const _) (integrable_const _), integral_div, ContactFloor.integral_const_prob]
  show haarTilt N (-(2 * t)) / haarTilt N (-(2 * t)) - 1 = 0
  rw [div_self (haarTilt_pos hN t).ne', sub_self]

theorem card_Pm (n : ℕ) : Fintype.card (Pm n) = 4 * n ^ 4 := by
  rw [Fintype.card_prod, Fintype.card_prod, card_st]
  simp only [Fintype.card_fin]

theorem smix_Pm (n : ℕ) (U : Lk n → SUN.SU N) : smixR N n U = 2 * ∑ p : Pm n, plaq N n (pl p) U := by
  rw [smix_normal]
  congr 1
  exact (Fintype.sum_prod_type fun p : Pm n => plaq N n (pl p) U).symm

theorem prod_gg (n : ℕ) (t : ℝ) (U : Lk n → SUN.SU N) :
    ∏ p : Pm n, (1 + gg N n (cT N t) p U)
      = Real.exp (-(2 * t) * (∑ p : Pm n, plaq N n (pl p) U - 4 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N))
        / haarTilt N (-(2 * t)) ^ (4 * n ^ 4) := by
  have c4 : ((4 * n ^ 4 : ℕ) : ℝ) = 4 * (n : ℝ) ^ 4 := by norm_num
  have e : ∑ p : Pm n, -(2 * t) * (plaq N n (pl p) U - WindowRead.haarMeanN N)
      = -(2 * t) * (∑ p : Pm n, plaq N n (pl p) U - 4 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_Pm,
      nsmul_eq_mul, c4]
  simp only [gg, cT, add_sub_cancel]
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ, card_Pm, e]

/-- **`Z(t)` in the gas**: `Z(t) = e^{−t ⟨S⟩₀} H(−2t)^{4 n⁴} Z_gas(all)`. DERIVED: `8 = 2 · 4`; `4` the normal
orientations; `2` the orientations of a plaquette. -/
theorem ZA_eq_gas (hN : N ≠ 0) (β t : ℝ) (n : ℕ) :
    AnisoTorus.ZA N β t n = Real.exp (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N))
      * haarTilt N (-(2 * t)) ^ (4 * n ^ 4)
      * ZG (piH N n) (fun U => Real.exp (-(β * sinR N n U))) (gg N n (cT N t)) Finset.univ := by
  have hT := pow_ne_zero (4 * n ^ 4) (haarTilt_pos (N := N) hN t).ne'
  rw [ZA_eq_int]
  unfold ZG
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only
  rw [prod_gg, smix_Pm]
  have e : Real.exp (-(β * sinR N n U + t * (2 * ∑ p : Pm n, plaq N n (pl p) U)))
      = Real.exp (-t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N))
        * Real.exp (-(2 * t) * (∑ p : Pm n, plaq N n (pl p) U - 4 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N))
        * Real.exp (-(β * sinR N n U)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  generalize haarTilt N (-(2 * t)) ^ (4 * n ^ 4) = Y at hT ⊢
  field_simp

theorem ZA_zero_eq_gas (β : ℝ) (n : ℕ) (c : ℝ → ℝ) :
    AnisoTorus.ZA N β 0 n = ZG (piH N n) (fun U => Real.exp (-(β * sinR N n U))) (gg N n c) ∅ := by
  rw [ZA_eq_int]
  unfold ZG
  simp only [zero_mul, add_zero, Finset.prod_empty, one_mul]

/-- **The bulk per site** `ℓ(t) = 4 log H(−2t) − 8 t ⟨φ⟩`: the generating function of `4` independent Haar plaquettes,
twice each, per site. DERIVED: `4` the normal orientations; `2` the orientations of a plaquette; `8 = 2 · 4`. -/
noncomputable def ell (N : ℕ) (t : ℝ) : ℝ :=
  4 * Real.log (haarTilt N (-(2 * t))) - 8 * t * WindowRead.haarMeanN N

/-- **The error per plaquette**: `η(t) = 6 ε (4096 ε)³`, `ε = 16 |t|`. DERIVED: `6`, `4096`, `3` of `Gas.ratio`,
`card_Kk_le`, `van3`; `16` of `abs_cT_le`. -/
noncomputable def etaT (t : ℝ) : ℝ := 6 * (16 * |t|) * (((4096 : ℕ) : ℝ) * (16 * |t|)) ^ 3

theorem etaT_eq (t : ℝ) : etaT t = 6 * 2 ^ 52 * t ^ 4 := by
  have h : |t| ^ 4 = t ^ 4 := by
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = (t ^ 2) ^ 2 := by rw [sq_abs]
      _ = t ^ 4 := by ring
  unfold etaT
  rw [← h]
  push_cast
  ring

/-- **The extensive form of `log Z`**: for `|t| ≤ 2⁻¹⁷`, on an even extent `n ≥ 3`, at every `β`,
`|log Z(β, t, n) − log Z(β, 0, n) − n⁴ ℓ(t)| ≤ 8 n⁴ η(t)`. The main term has no `β`. DERIVED: `8 = 2 · 4`, `2` of
`Gas.abs_log_le`, `4 n⁴` the plaquettes. COMPUTED: `2⁻¹⁷` gives `4096 · 16 |t| ≤ 1` and `4096 η ≤ 1/2`; `131072 = 2¹⁷`. Inherited: `3` the
least extent `gas_mixed` takes. -/
theorem logZA_ext (hN : N ≠ 0) {n : ℕ} (hn : 3 ≤ n) (he : n % 2 = 0) (β : ℝ) {t : ℝ}
    (ht : |t| ≤ 1 / 131072) :
    |AnisoTorus.logZA N β t n - AnisoTorus.logZA N β 0 n - (n : ℝ) ^ 4 * ell N t|
      ≤ 8 * (n : ℝ) ^ 4 * etaT t := by
  have ht0 := abs_nonneg t
  have h8 : 8 * |t| ≤ 1 := by linarith
  have hb : ∀ (p : Pm n) (U : Lk n → SUN.SU N), |gg N n (cT N t) p U| ≤ 16 * |t| :=
    fun p U => abs_cT_le hN h8 _
  have hgas := gas_mixed (N := N) hn he β (continuous_cT N t) (integral_cT hN t) (by positivity)
    (by linarith) hb
  have ha4 : |t| ^ 4 ≤ (1 / 131072) ^ 4 := pow_le_pow_left₀ ht0 ht 4
  have hm1 : ((4096 : ℕ) : ℝ) * (16 * |t|) ≤ 1 := by
    push_cast
    linarith
  have hmη : ((4096 : ℕ) : ℝ) * etaT t ≤ 1 / 2 := by
    have e : ((4096 : ℕ) : ℝ) * etaT t = 4096 * 6 * 16 * (4096 * 16) ^ 3 * |t| ^ 4 := by
      unfold etaT
      push_cast
      ring
    rw [e]
    norm_num at ha4 ⊢
    linarith
  have hη1 : etaT t ≤ 1 / 2 := by
    have hη0 : 0 ≤ etaT t := by
      unfold etaT
      positivity
    push_cast at hmη
    linarith
  have hr := hgas.ratio (by norm_num) hm1 rfl hmη
  have hl := hgas.abs_log_le hη1 hr Finset.univ
  have hZ := hgas.ZG_pos Finset.univ
  have hTp := haarTilt_pos (N := N) hN t
  rw [Finset.card_univ, card_Pm, ← ZA_zero_eq_gas β n (cT N t)] at hl
  have e : AnisoTorus.logZA N β t n = -t * (8 * (n : ℝ) ^ 4 * WindowRead.haarMeanN N)
      + (4 * (n : ℝ) ^ 4) * Real.log (haarTilt N (-(2 * t)))
      + Real.log (ZG (piH N n) (fun U => Real.exp (-(β * sinR N n U))) (gg N n (cT N t)) Finset.univ) := by
    have c4 : ((4 * n ^ 4 : ℕ) : ℝ) = 4 * (n : ℝ) ^ 4 := by norm_num
    unfold AnisoTorus.logZA
    rw [ZA_eq_gas hN, Real.log_mul (mul_pos (Real.exp_pos _) (pow_pos hTp _)).ne' hZ.ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hTp _).ne', Real.log_exp, Real.log_pow, c4]
  have e0 : AnisoTorus.logZA N β 0 n = Real.log (AnisoTorus.ZA N β 0 n) := rfl
  have c4 : ((4 * n ^ 4 : ℕ) : ℝ) = 4 * (n : ℝ) ^ 4 := by norm_num
  rw [c4] at hl
  rw [e, e0]
  unfold ell
  refine le_trans (le_of_eq ?_) (hl.trans (le_of_eq (by ring)))
  congr 1
  ring

/-! ## 7. The quartic cost and the strip -/

/-- **`DA_le_quartic`**: `|DA(β, t, w) − DA(β, 0, w)| ≤ 6 · 2⁶⁰ · 16^w t⁴` for `|t| ≤ 2⁻¹⁷`, `w ≥ 2`, at every `β`,
uniformly in `N ≠ 0`. The bulk `n⁴ ℓ(t)` cancels exactly: `16 n⁴ = (2n)⁴`. DERIVED: `16 = 2⁴` the copies; `2` the
doubling, and the least window for which `n ≥ 3`. COMPUTED: `6 · 2⁶⁰ = 256 · 6 · 2⁵²`, `256 = 16 · 8 + 8 · 16`. Inherited: `131072 = 2¹⁷` the
width of `logZA_ext`. -/
theorem DA_le_quartic (hN : N ≠ 0) (β : ℝ) {t : ℝ} (ht : |t| ≤ 1 / 131072) {w : ℕ} (hw : 2 ≤ w) :
    |AnisoTorus.DA N β t w - AnisoTorus.DA N β 0 w| ≤ 6 * 2 ^ 60 * ((4 : ℝ) ^ w) ^ 2 * t ^ 4 := by
  have h1 := logZA_ext hN (n := 2 ^ w) (three_le hw) (two_pow_mod (by omega)) β ht
  have h2 := logZA_ext hN (n := 2 ^ (w + 1)) (three_le (by omega)) (two_pow_mod (by omega)) β ht
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((2 ^ w : ℕ) : ℝ) ^ 4 := ⟨_, rfl⟩
  have c1 : ((4 : ℝ) ^ w) ^ 2 = A := by
    rw [hA, show (4 : ℝ) = 2 ^ 2 by norm_num]
    push_cast
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have c2 : ((2 ^ (w + 1) : ℕ) : ℝ) ^ 4 = 16 * A := by
    rw [hA, pow_succ]
    push_cast
    ring
  rw [etaT_eq] at h1 h2
  rw [← hA] at h1
  rw [c2] at h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  unfold AnisoTorus.DA
  rw [c1]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

/-- **The seed at the quartic cost**: `DA(β, 0, w) ≤ 1/2000` gives `DA(β, t, w) ≤ 1/1000` for
`0 ≤ t ≤ 1/(2¹⁹ 2^w)`. COMPUTED: `6 · 2⁶⁰ / 2⁷⁶ ≤ 1/2000`; `2⁻¹⁹ ≤ 2⁻¹⁷`. Inherited: `1/2000`, `1/1000`. -/
theorem seed_quartic (hN : N ≠ 0) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) {w : ℕ} (hw : 2 ≤ w)
    (hs : AnisoTorus.DA N β 0 w ≤ 1 / 2000) (hts : t ≤ 1 / (524288 * (2 : ℝ) ^ w)) :
    AnisoTorus.DA N β t w ≤ 1 / 1000 := by
  have hp1 : (1 : ℝ) ≤ 2 ^ w := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ w := by positivity
  have h1 : (2 : ℝ) ^ w * t ≤ 1 / 524288 := by
    rw [le_div_iff₀ (by positivity)] at hts
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have ht' : |t| ≤ 1 / 131072 := by
    rw [abs_of_nonneg ht]
    have := mul_le_mul_of_nonneg_right hp1 ht
    norm_num at h1 this ⊢
    linarith
  have e4 : ((4 : ℝ) ^ w) ^ 2 * t ^ 4 = ((2 : ℝ) ^ w * t) ^ 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 2
    ring
  have h4 : ((2 : ℝ) ^ w * t) ^ 4 ≤ (1 / 524288) ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg hpos.le ht) h1 4
  have hD := (abs_le.1 (DA_le_quartic hN β ht' hw)).2
  rw [mul_assoc (6 * 2 ^ 60 : ℝ), e4] at hD
  norm_num at h4 hD ⊢
  linarith

/-- **One seed window opens the quartic strip**: `DA(β, 0, w) ≤ 1/2000` gives `DA(β, t, ·) → 0` for
`0 ≤ t ≤ 1/(2¹⁹ 2^w)`: the inverse of the seed side. DERIVED: `0` the limit. COMPUTED: as in `seed_quartic`; `524288 = 2¹⁹`. Inherited: `1/2000`
the seed of `seed_quartic`. -/
theorem strip_of_seed_quartic (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) {w : ℕ} (hw : 2 ≤ w)
    (hs : AnisoTorus.DA N β 0 w ≤ 1 / 2000) (hts : t ≤ 1 / (524288 * (2 : ℝ) ^ w)) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) :=
  MixAnchor.tendsto_DA_of_seed hN hβ ht (by omega) (seed_quartic hN β ht hw hs hts)

/-- **The quartic width** `t_quart(N, β) = 1/(2¹⁹ 2^{w₀})`, `w₀ = StripGapThm.seedWindow N β`. DERIVED: `524288 = 2¹⁹`
the width at which `seed_quartic` turns the `1/2000` seed into `1/1000`. COMPUTED: as in `seed_quartic`. -/
noncomputable def tQuart (N : ℕ) (β : ℝ) : ℝ := 1 / (524288 * (2 : ℝ) ^ StripGapThm.seedWindow N β)

theorem tQuart_pos (β : ℝ) : 0 < tQuart N β := by
  unfold tQuart
  positivity

theorem area_ge {β : ℝ} (hβ : 0 ≤ β) : 4225 ≤ StripGapThm.areaG N β := by
  have hl240 : (240 : ℝ) ≤ StripGap.gapArea N β := StripGap.gapArea_ge β hβ
  have hlog : 0 ≤ Real.log (StripGap.gapArea N β) := Real.log_nonneg (by linarith)
  have hL := StripWidth.bulkExp_nonneg (N := N) β
  unfold StripGapThm.areaG StripWiden.glueArea
  nlinarith

theorem two_le_seedWindow {β : ℝ} (hβ : 0 ≤ β) : 2 ≤ StripGapThm.seedWindow N β := by
  obtain ⟨-, h1, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  by_contra hc
  have hle : StripGapThm.seedWindow N β ≤ 1 := by omega
  have h4 : (4 : ℝ) ^ StripGapThm.seedWindow N β ≤ 4 ^ 1 := pow_le_pow_right₀ (by norm_num) hle
  have := area_ge (N := N) hβ
  norm_num at h4
  linarith

theorem seed_zero (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    AnisoTorus.DA N β 0 (StripGapThm.seedWindow N β) ≤ 1 / 2000 := by
  obtain ⟨hw, h1, -⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  exact StripWiden.seed_glue hN hβ (StripWidth.bulkExp_nonneg β) (StripWidth.one_div_bk_le hN hβ) hw h1

/-- **`strip_width_quartic`**: `DA(β, t, ·) → 0` for `0 ≤ t ≤ t_quart(N, β)`, at every `β ≥ 0`, `N ≠ 0`. DERIVED: `0`
the limit. COMPUTED: as in `tQuart`. -/
theorem strip_width_quartic (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ tQuart N β) :
    Tendsto (fun v => AnisoTorus.DA N β t v) atTop (𝓝 0) :=
  strip_of_seed_quartic hN hβ ht (two_le_seedWindow hβ) (seed_zero hN hβ) hts

/-- **The size-uniform transfer gap on the quartic strip**: for `0 ≤ t ≤ t_quart(N, β)`, `StripLift.TransferGapAt` at
rate `log 2 / 2^{w₀}` from window `w₀` on. DERIVED: `2` the doubling. COMPUTED: as in `tQuart`. -/
theorem gap_quartic (hN : N ≠ 0) {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hts : t ≤ tQuart N β) :
    StripLift.TransferGapAt hN hβ ht (StripLift.seedMass (StripGapThm.seedWindow N β))
      (StripGapThm.seedWindow N β) :=
  StripLift.gap_of_seed hN hβ ht (by have := two_le_seedWindow (N := N) hβ; omega)
    (seed_quartic hN β ht (two_le_seedWindow hβ) (seed_zero hN hβ) hts)

/-- **The width in the area**: `t_quart ≥ 1/(2²⁰ √A_glue)`. DERIVED: `4 = 2²`, so `2^{w₀} ≤ 2 √A_glue`. COMPUTED:
`2²⁰ = 2 · 2¹⁹`, `1048576 = 2²⁰`. -/
theorem tQuart_ge {β : ℝ} (hβ : 0 ≤ β) :
    1 / (1048576 * Real.sqrt (StripGapThm.areaG N β)) ≤ tQuart N β := by
  obtain ⟨-, -, h2⟩ := StripGapThm.seedWindow_spec (N := N) hβ
  have hA := StripGapThm.one_lt_areaG (N := N) hβ
  have e : (4 : ℝ) ^ StripGapThm.seedWindow N β = ((2 : ℝ) ^ StripGapThm.seedWindow N β) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsq : ((2 : ℝ) ^ StripGapThm.seedWindow N β) ^ 2 ≤ (2 * Real.sqrt (StripGapThm.areaG N β)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), ← e]; linarith
  have hs : (2 : ℝ) ^ StripGapThm.seedWindow N β ≤ 2 * Real.sqrt (StripGapThm.areaG N β) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  unfold tQuart
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **The quartic strip contains the glued strip**, at every `β`. COMPUTED: `√A_glue ≥ 65` from `A_glue ≥ 4225`, and
`16192 · 65 ≥ 2²⁰`. -/
theorem tGlue_le_tQuart {β : ℝ} (hβ : 0 ≤ β) : StripWiden.tGlue N β ≤ tQuart N β := by
  have hA := area_ge (N := N) hβ
  have hs : (65 : ℝ) ≤ Real.sqrt (StripGapThm.areaG N β) :=
    (Real.le_sqrt' (by norm_num)).2 (by norm_num; linarith)
  have hsq := Real.sq_sqrt (show 0 ≤ StripGapThm.areaG N β by linarith)
  have e : StripWiden.tGlue N β = 1 / (16192 * StripGapThm.areaG N β) := rfl
  rw [e]
  refine le_trans ?_ (tQuart_ge hβ)
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

end MassGap.CumulantStrip

#print axioms MassGap.CumulantStrip.tail_le
#print axioms MassGap.CumulantStrip.Gas.ratio
#print axioms MassGap.CumulantStrip.Gas.abs_log_le
#print axioms MassGap.CumulantStrip.dependency_cgf
#print axioms MassGap.CumulantStrip.priv3
#print axioms MassGap.CumulantStrip.card_Tch_le
#print axioms MassGap.CumulantStrip.card_Kk_le
#print axioms MassGap.CumulantStrip.cent_factor_c
#print axioms MassGap.CumulantStrip.van_priv
#print axioms MassGap.CumulantStrip.van3
#print axioms MassGap.CumulantStrip.gas_mixed
#print axioms MassGap.CumulantStrip.ZA_eq_gas
#print axioms MassGap.CumulantStrip.etaT_eq
#print axioms MassGap.CumulantStrip.logZA_ext
#print axioms MassGap.CumulantStrip.DA_le_quartic
#print axioms MassGap.CumulantStrip.seed_quartic
#print axioms MassGap.CumulantStrip.strip_of_seed_quartic
#print axioms MassGap.CumulantStrip.strip_width_quartic
#print axioms MassGap.CumulantStrip.gap_quartic
#print axioms MassGap.CumulantStrip.tQuart_ge
#print axioms MassGap.CumulantStrip.tGlue_le_tQuart
#print axioms MassGap.CumulantStrip.abs_cT_le
#print axioms MassGap.CumulantStrip.integral_cT
#print axioms MassGap.CumulantStrip.seed_zero
#print axioms MassGap.CumulantStrip.two_le_seedWindow
#print axioms MassGap.CumulantStrip.area_ge
#print axioms MassGap.CumulantStrip.tQuart_pos
