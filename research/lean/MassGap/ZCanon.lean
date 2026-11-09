import Mathlib
import MassGap.NonGaussLink
import MassGap.WardKernel

/-!
# MassGap.ZCanon — the scalar and pseudoscalar channel factors fixed at `2/a_k⁴`

`NonGaussLink.clayStatementAt_SU_ng` takes channel factors `z : Chan → ℕ → ℝ` with `hz`
(`z c k ≠ 0` for every channel), `hzS` (`z_sc k · a_k⁴ → 2`) and `hzP` (`z_ps k · a_k⁴ → 2`),
`a_k = dySpacing N k`. This module fixes the scalar and pseudoscalar factors at exactly `2/a_k⁴` and
leaves the traceless-Ricci and Weyl factors free.

## The factors

* `zFix N zri zwe`: `2/a_k⁴` on `sc` and `ps`, `zri k` on `ri`, `zwe k` on `we`.
* `zFix_ne`: every factor is non-zero when `zri` and `zwe` are (`dySpacing_pos`).
* `zFix_sc_mul`, `zFix_ps_mul`: `z_sc k · a_k⁴ = 2` and `z_ps k · a_k⁴ = 2` at every step, so the limits
  `hzS`, `hzP` hold as constant sequences (`tendsto_zFix_sc`, `tendsto_zFix_ps`).

## The observer's three-point statement is not made harder

`ObsThreePoint hN z` reads `z` only through `z_sc` (`NonGaussLink.obsRead_eq`).

* `obsThreePoint_of_scale`: if eventually `z'_sc k = q k · z_sc k` with `r ≤ |q k| ≤ R`, `r > 0`, then
  `ObsThreePoint hN z` gives `ObsThreePoint hN z'`.
* `obsThreePoint_zFix`: `ObsThreePoint hN z` at any `z` with `z_sc k · a_k⁴ → 2` gives
  `ObsThreePoint hN (zFix N zri zwe)`, with `q k = 2/(z_sc k · a_k⁴)`, eventually in `[2/3, 2]`.

## The trace readings and the two-point kernel are unchanged

* `limUnder_of_not`: two real sequences that both fail to converge along a filter have the same
  `limUnder` value.
* `limUnder_ultra_mul`: a factor `q k → 1` leaves the `ultra` limit value of `q k · s k` equal to that
  of `s k`, with no boundedness hypothesis.
* `contTr_zFix`: at every order `n`, `contTr (rhoD f (zFix N zri zwe)) u = contTr (rhoD f z) u` for
  any `z` with `z_sc k · a_k⁴ → 2` (`WardKernel.contTr_rhoD`, factor `q kⁿ`). So `NonGaussianT`, which
  reads only `contTr`, holds at `zFix` exactly when it holds at such a `z`.
* `twoPointKernel_zFix`: `TwoPointKernel (rhoD f z) G ↔ TwoPointKernel (rhoD f (zFix N zri zwe)) G`,
  same `G`. `hAF` reads only `G`.

## The capstone

* `clayStatementAt_SU_zcan`: `clayStatementAt_SU_ng` at `z = zFix N zri zwe`. The inputs `hz`,
  `hzS`, `hzP` are discharged; `zri`, `zwe` with `hri : ∀ k, zri k ≠ 0`, `hwe : ∀ k, zwe k ≠ 0` remain,
  and every other input is that of `clayStatementAt_SU_ng` at `zFix N zri zwe`.
* `hK`, `hAF` and `hObs` at any `z` with `z_sc k · a_k⁴ → 2` give the same inputs at `zFix`
  (`twoPointKernel_zFix`, `obsThreePoint_zFix`). `hWard`, `hCO`, `hLC`, `hX` read families that mix
  channels; their terms rescale by different factors `q_scᵐ q_psᵖ → 1`. Not proved here: they
  transfer when each channel-graded component converges along `ultra`; without that, fixing `z` can
  make them strictly harder to meet. So `clayStatementAt_SU_zcan` is an alternative to
  `NonGaussLink.clayStatementAt_SU_ng`, not a replacement for it.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the limit of `ScalarTie` and `TopNorm` read by `hzS`, `hzP`, and the least
colour count; `4` the dimension; `3` the order of the three-point reading; `1`, `3` the bracket of
`z_sc k · a_k⁴` around `2`, whose images `2/3`, `2` bound the ratio; `0` the plane and the signs.
-/

noncomputable section

namespace MassGap.ZCanon

open MassGap MassGap.ClayStatement MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayWiring MassGap.ClayData MassGap.NonGaussLink Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The factors -/

/-- **The channel factors with the scalar and pseudoscalar factors fixed**: `2/a_k⁴` on `sc` and
`ps`, `zri k` on `ri`, `zwe k` on `we`, `a_k = dySpacing N k`.

DERIVED: `2` the limit of `ScalarTie` and `TopNorm`; `4` the dimension. -/
def zFix (N : ℕ) (zri zwe : ℕ → ℝ) : Chan → ℕ → ℝ
  | .sc, k => 2 / dySpacing N k ^ 4
  | .ps, k => 2 / dySpacing N k ^ 4
  | .ri, k => zri k
  | .we, k => zwe k

/-- DERIVED: `4` the dimension. -/
theorem dySpacing_pow_ne (hN : 1 ≤ N) (k : ℕ) : dySpacing N k ^ 4 ≠ 0 :=
  pow_ne_zero 4 (dySpacing_pos hN k).ne'

/-- **Every factor is non-zero** when the traceless-Ricci and Weyl factors are.

DERIVED: `2` the numerator, non-zero. -/
theorem zFix_ne (hN : 1 ≤ N) {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) :
    ∀ c k, zFix N zri zwe c k ≠ 0 := by
  intro c k
  cases c
  · exact div_ne_zero two_ne_zero (dySpacing_pow_ne hN k)
  · exact div_ne_zero two_ne_zero (dySpacing_pow_ne hN k)
  · exact hri k
  · exact hwe k

/-- **`z_sc k · a_k⁴ = 2` at every step.** DERIVED: `2`, `4` as in `zFix`. -/
theorem zFix_sc_mul (hN : 1 ≤ N) (zri zwe : ℕ → ℝ) (k : ℕ) :
    zFix N zri zwe .sc k * dySpacing N k ^ 4 = 2 :=
  div_mul_cancel₀ 2 (dySpacing_pow_ne hN k)

/-- **`z_ps k · a_k⁴ = 2` at every step.** DERIVED: `2`, `4` as in `zFix`. -/
theorem zFix_ps_mul (hN : 1 ≤ N) (zri zwe : ℕ → ℝ) (k : ℕ) :
    zFix N zri zwe .ps k * dySpacing N k ^ 4 = 2 :=
  div_mul_cancel₀ 2 (dySpacing_pow_ne hN k)

/-- **`hzS` at `zFix`**: the sequence is the constant `2`. DERIVED: `2`, `4` as in `zFix`. -/
theorem tendsto_zFix_sc (hN : 1 ≤ N) (zri zwe : ℕ → ℝ) :
    Tendsto (fun k => zFix N zri zwe .sc k * dySpacing N k ^ 4) atTop (𝓝 2) := by
  simp only [zFix_sc_mul hN]
  exact tendsto_const_nhds

/-- **`hzP` at `zFix`**: the sequence is the constant `2`. DERIVED: `2`, `4` as in `zFix`. -/
theorem tendsto_zFix_ps (hN : 1 ≤ N) (zri zwe : ℕ → ℝ) :
    Tendsto (fun k => zFix N zri zwe .ps k * dySpacing N k ^ 4) atTop (𝓝 2) := by
  simp only [zFix_ps_mul hN]
  exact tendsto_const_nhds

/-! ## 2. `ObsThreePoint` under a bounded rescaling of `z_sc` -/

/-- **`ObsThreePoint` transfers along a bounded rescaling of the scalar factor.** If eventually
`z'_sc k = q k · z_sc k` with `r ≤ |q k| ≤ R`, `r > 0`, then the reading at `z'` is `q k³` times the
reading at `z` (`obsRead_eq`), and the bounds `[κ, C]` become `[r³ κ, R³ C]`.

DERIVED: `3` the order; `0` the signs. -/
theorem obsThreePoint_of_scale (hN : N ≠ 0) (z z' : Chan → ℕ → ℝ) (q : ℕ → ℝ) {r R : ℝ}
    (hr : 0 < r)
    (hq : ∀ᶠ k in atTop, z' .sc k = q k * z .sc k ∧ r ≤ |q k| ∧ |q k| ≤ R)
    (h : ObsThreePoint hN z) : ObsThreePoint hN z' := by
  obtain ⟨a, b, c, ha, hb, hc, hsep, κ, C, hκ, hev⟩ := h
  refine ⟨a, b, c, ha, hb, hc, hsep, r ^ 3 * κ, R ^ 3 * C, mul_pos (pow_pos hr 3) hκ, ?_⟩
  filter_upwards [hev, hq] with k hk hqk
  have e : obsRead hN z' k ![a, b, c] = q k ^ 3 * obsRead hN z k ![a, b, c] := by
    rw [obsRead_eq, obsRead_eq, hqk.1]
    ring
  have hq0 : 0 ≤ |q k| := abs_nonneg _
  rw [e, abs_mul, abs_pow]
  exact ⟨mul_le_mul (pow_le_pow_left₀ hr.le hqk.2.1 3) hk.1 hκ.le (pow_nonneg hq0 3),
    mul_le_mul (pow_le_pow_left₀ hq0 hqk.2.2 3) hk.2 (abs_nonneg _)
      (pow_nonneg (hq0.trans hqk.2.2) 3)⟩

/-- **`ObsThreePoint` at any admissible scalar factor gives it at `zFix`.** With
`z_sc k · a_k⁴ → 2`, eventually `1 < z_sc k · a_k⁴ < 3`; then `q k = 2/(z_sc k · a_k⁴)` lies in
`[2/3, 2]` and `2/a_k⁴ = q k · z_sc k`.

DERIVED: `1`, `3` the bracket around `2`; `2/3`, `2` its images under `x ↦ 2/x`. -/
theorem obsThreePoint_zFix (hN : N ≠ 0) (z : Chan → ℕ → ℝ)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (zri zwe : ℕ → ℝ) (h : ObsThreePoint hN z) : ObsThreePoint hN (zFix N zri zwe) := by
  have hev : ∀ᶠ k in atTop, z .sc k * dySpacing N k ^ 4 ∈ Set.Ioo (1 : ℝ) 3 :=
    hzS.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  refine obsThreePoint_of_scale hN z (zFix N zri zwe)
    (fun k => 2 / (z .sc k * dySpacing N k ^ 4)) (r := 2 / 3) (R := 2) (by norm_num) ?_ h
  filter_upwards [hev] with k hk
  obtain ⟨h1, h3⟩ := hk
  have hzk : z .sc k ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    linarith
  have hx : 0 < z .sc k * dySpacing N k ^ 4 := by linarith
  have hpos : 0 < 2 / (z .sc k * dySpacing N k ^ 4) := div_pos two_pos hx
  refine ⟨?_, ?_, ?_⟩
  · show 2 / dySpacing N k ^ 4 = 2 / (z .sc k * dySpacing N k ^ 4) * z .sc k
    rw [div_mul_eq_mul_div, mul_comm 2 (z .sc k), mul_div_mul_left _ _ hzk]
  · show 2 / 3 ≤ |2 / (z .sc k * dySpacing N k ^ 4)|
    rw [abs_of_pos hpos]
    exact div_le_div_of_nonneg_left (by norm_num) hx h3.le
  · show |2 / (z .sc k * dySpacing N k ^ 4)| ≤ 2
    rw [abs_of_pos hpos]
    exact div_le_self (by norm_num) h1.le

/-! ## 3. The trace readings and the two-point kernel -/

section Trace

open MassGap.InfiniteLattice

/-- **`limUnder` of a non-convergent real sequence is one fixed real**, whatever the sequence.

DERIVED: no numeral. -/
theorem limUnder_of_not {s t : ℕ → ℝ} {l : Filter ℕ}
    (hs : ¬ ∃ x, Tendsto s l (𝓝 x)) (ht : ¬ ∃ x, Tendsto t l (𝓝 x)) :
    limUnder l s = limUnder l t := by
  unfold limUnder lim Classical.epsilon Classical.strongIndefiniteDescription
  beta_reduce
  rw [dif_neg (show ¬∃ x, map s l ≤ 𝓝 x from hs), dif_neg (show ¬∃ x, map t l ≤ 𝓝 x from ht)]

/-- **A factor tending to `1` leaves the `ultra` limit value unchanged**, with no boundedness: if
`s` converges along `ultra` the product has the same limit; if not, neither does the product, and
`limUnder_of_not` applies.

DERIVED: `1` the limit of the factor. -/
theorem limUnder_ultra_mul {s q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 1)) :
    limUnder (ultra : Filter ℕ) (fun k => q k * s k) = limUnder (ultra : Filter ℕ) s := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hqu : Tendsto q (ultra : Filter ℕ) (𝓝 1) := hq.mono_left ultra_le
  by_cases hs : ∃ x, Tendsto s (ultra : Filter ℕ) (𝓝 x)
  · obtain ⟨x, hx⟩ := hs
    have h := hqu.mul hx
    rw [one_mul] at h
    rw [h.limUnder_eq, hx.limUnder_eq]
  · refine limUnder_of_not ?_ hs
    rintro ⟨y, hy⟩
    apply hs
    refine ⟨y, ?_⟩
    have hq0 : ∀ᶠ k in (ultra : Filter ℕ), q k ≠ 0 :=
      hqu.eventually (isOpen_ne.mem_nhds one_ne_zero)
    have h := hy.div hqu one_ne_zero
    rw [div_one] at h
    refine h.congr' (hq0.mono fun k hk => ?_)
    show q k * s k / q k = s k
    field_simp

/-- **The trace readings at `zFix` equal those at any `z` with `z_sc k · a_k⁴ → 2`**, at every
order `n`: the lattice sequences differ by the factor `q kⁿ`, `q k = 2/(z_sc k · a_k⁴) → 1`.

DERIVED: `2`, `4` as in `zFix`; `16` as in `WardKernel.contTr_rhoD`; `1` the limit of `q`. -/
theorem contTr_zFix (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (zri zwe : ℕ → ℝ) {n : ℕ} (u : Fin n → TestFn) :
    contTr hN (rhoD ft (zFix N zri zwe)) u = contTr hN (rhoD ft z) u := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  set q : ℕ → ℝ := fun k => 2 / (z .sc k * dySpacing N k ^ 4)
  have hq : Tendsto q atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).div hzS two_ne_zero
    rw [div_self two_ne_zero] at h
    exact h
  have hev : ∀ᶠ k in atTop, z .sc k ≠ 0 := by
    filter_upwards [hzS.eventually (isOpen_ne.mem_nhds two_ne_zero)] with k hk h0
    exact hk (by rw [h0, zero_mul])
  have hqn : Tendsto (fun k => q k ^ n) atTop (𝓝 1) := by
    have h := hq.pow n
    rwa [one_pow] at h
  rw [WardKernel.contTr_rhoD, WardKernel.contTr_rhoD]
  rw [← limUnder_ultra_mul (s := fun k => ((N : ℝ) / 16 * z .sc k) ^ n
      * latSk hN k (fun i => WardKernel.obsConn hN k (u i))) hqn]
  refine limUnder_congr_ultra (hev.mono fun k hk => ?_)
  show ((N : ℝ) / 16 * (2 / dySpacing N k ^ 4)) ^ n * _ = q k ^ n * (_ * _)
  have h4 := dySpacing_pow_ne hN1 k
  have : 2 / dySpacing N k ^ 4 = q k * z .sc k := by
    simp only [q]; field_simp
  rw [this]; ring_nf

/-- **`TwoPointKernel` at `zFix` is `TwoPointKernel` at any `z` with `z_sc k · a_k⁴ → 2`**, same `G`.

DERIVED: `2`, `4` as in `zFix`. -/
theorem twoPointKernel_zFix (hN : N ≠ 0) (ft : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (zri zwe : ℕ → ℝ) (G : ℝ → ℝ) :
    TwoPointKernel hN (rhoD ft z) G ↔ TwoPointKernel hN (rhoD ft (zFix N zri zwe)) G := by
  unfold TwoPointKernel
  simp only [contTr_zFix hN ft z hzS zri zwe]

end Trace

/-! ## 4. The capstone -/

section Capstone

open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.InfiniteLattice MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead

/-- **`NonGaussLink.clayStatementAt_SU_ng` at `z = zFix N zri zwe`**: the scalar and pseudoscalar
factors are `2/a_k⁴`, so `hz` reduces to `hri`, `hwe` (`zFix_ne`) and `hzS`, `hzP` hold exactly
(`tendsto_zFix_sc`, `tendsto_zFix_ps`). The traceless-Ricci factor `zri` and the Weyl factor `zwe`
are free non-zero sequences. The other inputs are those of `clayStatementAt_SU_ng` at
`zFix N zri zwe`.

`hK` at any `z` with `z_sc k · a_k⁴ → 2` is equivalent to `hK` here (`twoPointKernel_zFix`); `hAF`
reads only `G`; `hObs` transfers (`obsThreePoint_zFix`), and `NonGaussianT` at `rhoD` reads only
`contTr`, which is unchanged (`contTr_zFix`). `hWard`, `hCO`, `hLC`, `hX` read channel-mixing families
whose terms rescale by different factors `q_scᵐ q_psᵖ → 1`; they transfer when each channel-graded
component converges along `ultra` (argued, not proved here), and without that, fixing `z` can make
them strictly harder. This theorem is an alternative to `clayStatementAt_SU_ng`, not a replacement.

DERIVED: `2` the least colour count; `0` the plane; `4` the dimension. -/
theorem clayStatementAt_SU_zcan (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (zri zwe : ℕ → ℝ) (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0)
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) (zFix N zri zwe)) G)
    (hAF : AFCoefficient N G)
    (hObs : ObsThreePoint (ne_zero_of_two_le hN2) (zFix N zri zwe))
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) (zFix N zri zwe)))
    (hCO : CompOS (ne_zero_of_two_le hN2)
      (build (rhoD (fT N) (zFix N zri zwe)) (bareD (fT N) (bT N))))
    (wC : TSepG (build (rhoD (fT N) (zFix N zri zwe)) (bareD (fT N) (bT N))).Ix 0 →
      preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys)
      (build (rhoD (fT N) (zFix N zri zwe)) (bareD (fT N) (bT N))) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) (zFix N zri zwe))
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) (zFix N zri zwe))
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P)
            (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) (zFix N zri zwe))
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  have hN1 : 1 ≤ N := one_le_two.trans hN2
  clayStatementAt_SU_ng hN2 W ht hU hphys hfar (zFix N zri zwe) (zFix_ne hN1 hri hwe)
    (tendsto_zFix_sc hN1 zri zwe) (tendsto_zFix_ps hN1 zri zwe) G hK hAF hObs hWard hCO wC hLC hX

end Capstone

end MassGap.ZCanon

end

#print axioms MassGap.ZCanon.zFix_ne
#print axioms MassGap.ZCanon.zFix_sc_mul
#print axioms MassGap.ZCanon.zFix_ps_mul
#print axioms MassGap.ZCanon.tendsto_zFix_sc
#print axioms MassGap.ZCanon.tendsto_zFix_ps
#print axioms MassGap.ZCanon.obsThreePoint_of_scale
#print axioms MassGap.ZCanon.obsThreePoint_zFix
#print axioms MassGap.ZCanon.limUnder_of_not
#print axioms MassGap.ZCanon.limUnder_ultra_mul
#print axioms MassGap.ZCanon.contTr_zFix
#print axioms MassGap.ZCanon.twoPointKernel_zFix
#print axioms MassGap.ZCanon.clayStatementAt_SU_zcan
