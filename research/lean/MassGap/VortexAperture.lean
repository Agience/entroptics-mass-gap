import Mathlib
import MassGap.VortexStrong
import MassGap.FluxCost
import MassGap.RelativeGap
import MassGap.NonAbelianForget
import MassGap.CubeFlux

/-!
# MassGap.VortexAperture — the vortex form of the flux half at the aperture scale

`FluxCost.VortexCostAt σ A ℓ` asks, eventually in `β`, at every power-of-two side `n` with
`n a ∈ [2ℓ, 5ℓ]` (`a = aRun 2 β`), every corner step `i` and every `ν ≠ i`, that
`1 − zR (Lc n i) i ν β ≤ A e^{−σ n a}`. This module places three readings of that statement.

## 0. Calibration (`vortexCostAt_of_large`)

At one `ℓ` the statement is vacuous: `0 ≤ zR` gives `1 − zR ≤ 1`, so `σ ≥ 0` and `A ≥ e^{5σℓ}` give
`VortexCostAt σ A ℓ`. Its content is the constant `A` held fixed while `ℓ` grows, which is how
`FluxCost.runSeed_two_iff_vortex` asks for it (frequently in `ℓ` at one `σ, A`).

## 1. Condensation at the aperture scale (`EffGas`, `vortexCostAt_of_eff`)

`VortexStrong` proves condensation at `0 < β ≤ 1/4000000` from three properties of the Wilson
plaquette activities: they are centre-covariant and local (`zwP_coboundary`, the integrand reads the
pattern on `X` only), they are bounded by `r^{|X|}`, and `4225 r e ≤ 1/128`. This section runs the
same argument for an arbitrary activity with those properties.

* `CentreLocal L F`: `F ζ X` is unchanged when `ζ` is moved by the coboundary of a centre-valued link
  field (`cob`) and reads `ζ` on `X` only (`loc`).
* `CentreLocal.card_ge_of_ne`: a set whose activity sees the sheet has at least `L_a L_b`
  plaquettes (the argument of `VortexStrong.card_ge_of_zwP_ne`, from `cob` and `loc` alone).
* `dob_actF`: `|F ζ X| ≤ r^{|X|}` and `4225 r e ≤ 1/128` give Dobrushin's criterion with the weights
  `VortexStrong.cw (r e)`, for every pattern.
* `log_Zg_sub_le`: `log Z(F, 1) − log Z(F, sheet) ≤ 4 |RPlaq L| (4225 r e)^{L_a L_b}`.
* `EffGas L' a b z r`: an activity `F` on the torus `L'`, `CentreLocal`, bounded by `r^{|X|}`, whose
  polymer partition functions reproduce the ratio, `z = Z(F, sheet)/Z(F, 1)`.
  `EffGas.one_sub_le`: `1 − z ≤ 4 |RPlaq L'| (4225 r e)^{L'_a L'_b}`.
* `effGas_wilson`: at every `β ≥ 0` the Wilson plaquette activities `VortexStrong.zwP L β` are an
  `EffGas` for `zR L a b β` on the torus itself, with `r = 1 − e^{−2β}`. So `EffGas` is inhabited,
  and at `r` small it is the case of `VortexStrong` with no blocking. `EffCondensationAt` is not
  inhabited by it: that asks for `r` fixed as `β → ∞`, where `1 − e^{−2β} → 1`. It is inhabited by the
  one-polymer activity (section 4) whenever `elecRatio ≤ r^{Lc m i i · Lc m i ν}` on the window
  (`effCondensationAt_of_elec`).
* `one_sub_le_of_effGas_Lc`: on the corner torus `Lc m i` with `t ≤ m`,
  `1 − z ≤ 2048 e^{−t}`.
* `EffCondensationAt κ r ℓ`: on the window of `VortexCostAt`, the fine ratio `zR (Lc n i) i ν β` has
  an `EffGas` description on a corner torus `Lc m i` with `κ n a ≤ m` and activity bound `r`.
* **`vortexCostAt_of_eff`**: `0 < r`, `4225 r e ≤ 1/128` and `EffCondensationAt κ r ℓ` give
  `VortexCostAt κ 2048 ℓ`. The constant `2048` does not depend on `ℓ`, so
  `flux_half_of_eff`: `EffCondensationAt κ r ℓ` eventually in `ℓ` with `κ > 0` gives
  `∃ σ A, 0 < σ ∧ ∀ᶠ ℓ, VortexCostAt σ A ℓ`.

`EffGas` fixes only the number `z`. The one-polymer activity on a plane slice is an `EffGas` for every
`z ∈ (0, 1]` with `(1 − z)/(1 + z) ≤ r^{L'_a L'_b}` (`effGas_of_elec`). So `EffCondensationAt κ r ℓ`
follows from `elecRatio ≤ r^{Lc m i i · Lc m i ν}` for some `m ≥ κ n a` (`effCondensationAt_of_elec`),
and gives `1 − zR ≤ 2048 e^{−m}`. It is a decay bound on `zR`, quadratic in `κ n a`, not a block-spin
statement. No declaration constructs an `EffGas` from a block-spin map of the Wilson measure.
Evaluation, not a theorem: the threshold `r ≤ 1/(128 · 4225 · e) ≈ 6.8 · 10⁻⁷`, from the
connected-set entropy `4225`, is an obstruction only for a block-spin `F` of Wilson type, whose
activity at an effective coupling of order one (`1 − e^{−2β_eff}` of order one) does not meet it. For
`EffCondensationAt` as defined it sets the base of the decay, not a barrier.

## 2. 't Hooft duality: the vortex ratio is the electric-flux ratio (`elecRatio_eq`)

* `deficit_eq_two_oddTrace`: for `g` with `g + g = 0`, the twist deficit `hs(a) − twist(a, act g)` is
  twice the summed trace of the flux sectors `ψ` with `ψ(g) ≠ 1` (`ψ(g) = ±1`).
* `one_sub_zR_eq_oddFlux`: at `SU(2)`, `β ≥ 0`, `n ≥ 2` even,
  `1 − zR (Lc n i) i ν β = 2 · oddFlux / Z`, `oddFlux` the trace of the slice states with odd
  electric flux in direction `ν` (`TwistDeficitUnionN.deficit_eq_sum` at `g = e_ν`).
* `elecRatio β n i ν = oddFlux / (Z − oddFlux)`, the ratio of the `ν`-odd to the `ν`-even electric
  flux traces, each summed over the two transverse fluxes: `Σ_{e⊥} Z(e_ν = 1, e⊥) / Σ_{e⊥} Z(0, e⊥)`.
  `elecRatio_eq`: `elecRatio = (1 − zR)/(1 + zR)`, the `Z₂` Fourier transform in the single twist of
  the plane `(i, ν)`. It is not 't Hooft's `Z_{e=(1,0,0)}/Z_{e=0}`, which takes all eight twists.
* `elec_le_one_sub`, `one_sub_le_two_elec`: for `0 ≤ zR ≤ 1`, `E ≤ 1 − zR ≤ 2E`.
* `ElecCostAt σ A ℓ`: the window of `VortexCostAt` with `elecRatio ≤ A e^{−σ n a}`.
  `elecCostAt_of_vortexCostAt`: `VortexCostAt σ A ℓ → ElecCostAt σ A ℓ`;
  `vortexCostAt_of_elecCostAt`: `ElecCostAt σ A ℓ → VortexCostAt σ (2A) ℓ`. Both directions hold:
  `(V)` is, up to the factor `2`, the statement that the odd electric-flux sector of the slice carries
  at most `A e^{−σ n a}` of the even sector's trace.

Argued, not a declaration: `oddFlux` and `Z − oddFlux` are traces of the transfer over the time extent
of the torus restricted to the two sectors, so `−log elecRatio / (time extent)` estimates the energy of
one unit of electric flux winding direction `ν` above the zero-flux vacuum, marginal over the
transverse fluxes. Linear confinement puts
that energy at `σ_phys · L_ν a`, which makes `F_el` of order `σ_phys (n a)²`, more than the
`σ n a` that `VortexCostAt` asks. No declaration relates `elecRatio` to a sector energy.

## 3. Readings of the states and the ratio `zR` (`not_ratio_of_states`, `hidden_twist_agrees`)

A reading is the expectation of a function in a normalised state. `zR` is a ratio of normalisations.

* `read w f = Σ w f / Σ w`, `ratio w w' = Σ w' / Σ w`, `AgreeOn V w w'`: equal readings on `V`.
* `read_smul`, `ratio_smul`: scaling a weight by `k ≠ 0` changes no reading and multiplies the ratio by
  `k`. **`not_ratio_of_states`**: no function of the two states (all their readings) gives the ratio
  on positive weights.
* **`hidden_twist_agrees`**: on `α × γ`, a product weight `p(x) q(y)` twisted by `h(y)`, a factor on the
  coordinate the readings do not see, has exactly the same readings of every function of `x`
  (`RelativeGap.readings Prod.fst`), and ratio `Σ q h / Σ q`. `hidden_twist_any_ratio`: for every
  `k ∈ (0, 1]` such a twist with `0 < h ≤ 1` agrees on all those readings and has ratio `k`; its
  witness is the constant `h = k`, a rescaling, so it carries no more than `read_smul`. The content of
  the section is `hidden_twist_agrees` with `h` not constant: the twist acts on a mode hidden from the
  readings, leaves them unchanged and sets the ratio to the hidden mean `Σ q h / Σ q`, as
  `RelativeGap.hidden_maxCorr` does for the correlation. These results are about abstract weights;
  they say nothing about the two Wilson states, whose normalisations are fixed by `β`.
* On the Wilson torus, `ZRp_sheet_eq` and `zR_eq_read`: `zR L a b β` is the untwisted expectation of
  the one observable `sheetObs L a b β U = exp(−β Σ_q (φ(ζ_q U_q) − φ(U_q)))`, `ζ = sheetR`;
  `sheetObs_eq_filter`: the sum runs over the plaquettes where the sheet is not `1`.

So agreement of the twisted and untwisted states on a set of readings constrains `zR` only through
the readings' relation to `sheetObs`. Argued, not a declaration: on the corner torus the sheet of the
plane `(i, ν)` has a number of plaquettes growing like `n²`, and `sheetObs` ranges over
`e^{±2β|sheet|}`; a fixed finite set of readings at fixed physical size does not contain it, and
agreement on such readings is expected in confining and in Higgs-like phases alike, where `zR` tends to
`1` and to `0` respectively.

## 4. The one-polymer activity (`effGas_onePolymer`, `effGas_of_elec`, `effCondensationAt_of_elec`)

`wF c ζ X = c · Π_{q ∈ X₀} sg(ζ_q)` on the `(a, b)` plaquettes `X₀` of the plane through the origin and
`0` elsewhere, `sg` the centre sign (`1`, `−1`, `0` off the centre). It is `CentreLocal` (a centre
coboundary changes the product by a square), its gas has `Z = 1 + c Φ(ζ)` with `Φ(1) = 1`,
`Φ(sheet) = −1`, so it is an `EffGas` for `(1 − c)/(1 + c)` with bound `|c|^{1/(L_a L_b)}`.

DERIVED (module-wide): `4225`, `128`, `e`, `16`, `64`, `256` as in `VortexStrong`; `4 = 2 · 2` the two
gases and the geometric tail; `1024 = 4 · 256`; `2048 = 1024 · 2` with `t² ≤ 2 eᵗ`
(`Real.quadratic_le_exp_of_nonneg`); `e · x ≤ e^{−1}` from `x ≤ 1/128` and `e < 3`; `2` and `5` the
window of `ObserverTheory.FluxCostAt`; `2 = |1 − (−1)|` the deficit of a sector with `ψ(g) = −1`; `1/2`
the scale in `not_ratio_of_states`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.VortexAperture

open MeasureTheory Filter Topology Finset
open MassGap.RectWilson MassGap.GapSideVortexRect MassGap.CompactGauge
open MassGap.StrongCoupling (Touch touchNbrs mem_touchNbrs touchNbrs_card_le_touchDeg)
open MassGap.PolymerCount (TouchConnected)
open MassGap.ChunkActivity (Inc)
open MassGap.VortexStrong (sheetAt strip sheetR_eq_sheetAt sheetAt_swap sheetAt_mul_self
  strip_central rhol_strip cw cw_nonneg cw_of_not sum_site_cw_le sum_site_cw_tail_le touch_self
  touchDeg_rbd_le Z_le_of_agree card_rplaq_Lc_le)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 0. Calibration -/

/-- **At one `ℓ` the vortex form is vacuous**: `σ ≥ 0` and `A ≥ e^{5σℓ}` give it. -/
theorem vortexCostAt_of_large {σ A ℓ : ℝ} (hσ : 0 ≤ σ) (hA : Real.exp (5 * σ * ℓ) ≤ A) :
    FluxCost.VortexCostAt σ A ℓ := by
  refine Eventually.of_forall fun β n _ _ _ hup i ν => ?_
  have hz : 0 ≤ zR (Lc n i) i ν.1 β := by
    unfold zR
    exact div_nonneg (ZRp_pos _ β _).le (ZR_pos _ β).le
  have hk : σ * ((n : ℝ) * AsymptoticScaling.aRun 2 β) ≤ 5 * σ * ℓ := by
    have := mul_le_mul_of_nonneg_left hup hσ
    linarith
  have he : 1 ≤ Real.exp (5 * σ * ℓ) * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun 2 β))) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have := mul_le_mul_of_nonneg_right hA (Real.exp_pos (-(σ * ((n : ℝ) *
    AsymptoticScaling.aRun 2 β)))).le
  linarith

/-! ## 1. Condensation at the aperture scale -/

section Effective

variable (L : Fin 4 → ℕ)

/-- **A centre-covariant local activity** on the rectangular torus `L`: `F ζ X` is unchanged when the
pattern `ζ` is moved by the coboundary of a centre-valued link field, and reads `ζ` on `X` only. -/
structure CentreLocal (F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ) : Prop where
  cob : ∀ (ζ : RPlaq L → SUN.SU 2) (χ : RLink L → SUN.SU 2), (∀ l g, χ l * g = g * χ l) →
    ∀ X, F ζ X = F (fun q => ζ q * rhol L q χ) X
  loc : ∀ (ζ ζ' : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)), (∀ q ∈ X, ζ q = ζ' q) →
    F ζ X = F ζ' X

variable {L}

/-- **Two strips carry the sheet to any position**, for every centre-covariant activity. -/
theorem CentreLocal.sheet_move {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ}
    (hF : CentreLocal L F) {a b : Fin 4} (hab : a ≠ b) {s t : ℕ} (hs : s < L a) (ht : t < L b)
    (X : Finset (RPlaq L)) :
    F (sheetR L a b) X = F (sheetAt L a b s t) X := by
  rw [hF.cob (sheetR L a b) (strip L a b s 0) (strip_central L a b s 0) X]
  have e1 : (fun q => sheetR L a b q * rhol L q (strip L a b s 0)) = sheetAt L a b s 0 := by
    funext q
    rw [rhol_strip L hab hs 0 q, sheetR_eq_sheetAt, ← mul_assoc, sheetAt_mul_self, one_mul]
  rw [e1, hF.cob (sheetAt L a b s 0) (strip L b a t s) (strip_central L b a t s) X]
  have e2 : (fun q => sheetAt L a b s 0 q * rhol L q (strip L b a t s)) = sheetAt L a b s t := by
    funext q
    rw [rhol_strip L (Ne.symm hab) ht s q, sheetAt_swap L a b s 0, sheetAt_swap L a b s t,
      ← mul_assoc, sheetAt_mul_self, one_mul]
  rw [e2]

/-- **A set whose activity sees the sheet wraps the plane**: at least `L a · L b` plaquettes. -/
theorem CentreLocal.card_ge_of_ne {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ}
    (hF : CentreLocal L F) {a b : Fin 4} (hab : a ≠ b) {X : Finset (RPlaq L)}
    (h : F (sheetR L a b) X ≠ F (fun _ => 1) X) : L a * L b ≤ X.card := by
  have key : ∀ p : Fin (L a) × Fin (L b),
      ∃ q ∈ X, (q.2 a).val = p.1.val ∧ (q.2 b).val = p.2.val := by
    intro p
    by_contra hn
    push Not at hn
    apply h
    rw [hF.sheet_move hab p.1.isLt p.2.isLt X]
    refine hF.loc _ _ X fun q hq => ?_
    unfold sheetAt
    rw [if_neg]
    rintro ⟨_, h1, h2⟩
    exact hn q hq h1 h2
  choose f hfX hf using key
  have hinj : Set.InjOn f ↑(Finset.univ : Finset (Fin (L a) × Fin (L b))) := by
    intro p _ p' _ he
    have h1 := (hf p).1
    have h2 := (hf p).2
    rw [he, (hf p').1] at h1
    rw [he, (hf p').2] at h2
    exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)
  have hc := Finset.card_le_card_of_injOn f (fun p _ => hfX p) hinj
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hc
  exact hc

open scoped Classical in
/-- **The polymer activity of `F`**: `F` on the nonempty touch-connected sets, `0` elsewhere. -/
def actF (F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ) (ζ : RPlaq L → SUN.SU 2)
    (X : Finset (RPlaq L)) : ℝ :=
  if X.Nonempty ∧ TouchConnected (rbd L) X then F ζ X else 0

theorem actF_of_not {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} {ζ : RPlaq L → SUN.SU 2}
    {X : Finset (RPlaq L)} (h : ¬ (X.Nonempty ∧ TouchConnected (rbd L) X)) : actF F ζ X = 0 := by
  classical
  unfold actF
  exact if_neg h

theorem actF_abs_le {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ ζ X, |F ζ X| ≤ r ^ X.card) (ζ : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)) :
    |actF F ζ X| ≤ r ^ X.card := by
  classical
  unfold actF
  split_ifs
  · exact hb ζ X
  · rw [abs_zero]
    exact pow_nonneg hr _

/-- **Every set of fewer than `L a · L b` plaquettes carries the untwisted activity.** -/
theorem actF_sheet_eq {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} (hF : CentreLocal L F)
    {a b : Fin 4} (hab : a ≠ b) {X : Finset (RPlaq L)} (hX : X.card < L a * L b) :
    actF F (sheetR L a b) X = actF F (fun _ => 1) X := by
  classical
  unfold actF
  split_ifs
  · by_contra hne
    exact absurd (hF.card_ge_of_ne hab hne) (not_le.2 hX)
  · rfl

/-- **The polymer partition function of `F` at the pattern `ζ`.** -/
def Zg (F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ) (ζ : RPlaq L → SUN.SU 2) : ℝ :=
  MatchAt.Z (Inc (rbd L)) (actF F ζ) (univ : Finset (RPlaq L)).powerset

/-- **Dobrushin's criterion for a bounded activity**: `|F| ≤ r^{|X|}`, `r > 0` and
`4225 r e ≤ 1/128` give `Dob` with the weights `cw (r e)`, for every pattern. -/
theorem dob_actF {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} {r : ℝ} (hr : 0 < r)
    (hb : ∀ ζ X, |F ζ X| ≤ r ^ X.card) (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128)
    (ζ : RPlaq L → SUN.SU 2) :
    MatchAt.Dob (Inc (rbd L)) (actF F ζ) (cw L (r * Real.exp 1)) := by
  classical
  set y := r * Real.exp 1 with hydef
  have hy : 0 < y := mul_pos hr (Real.exp_pos 1)
  have hx1 : 4225 * y < 1 := by linarith
  intro γ
  refine ⟨cw_nonneg L hy.le γ, ?_⟩
  by_cases hγ : γ.Nonempty ∧ TouchConnected (rbd L) γ
  swap
  · rw [actF_of_not hγ, cw_of_not L hγ, abs_zero, zero_mul, neg_zero, Real.exp_zero, sub_self]
  have hcγ : cw L y γ = y ^ γ.card := by unfold VortexStrong.cw; exact if_pos hγ
  set B := γ.biUnion (touchNbrs (rbd L)) with hB
  have hBcard : B.card ≤ γ.card * 64 := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ p ∈ γ, (touchNbrs (rbd L) p).card ≤ ∑ _p ∈ γ, 64 :=
          Finset.sum_le_sum fun p _ =>
            (touchNbrs_card_le_touchDeg (rbd L) p).trans (touchDeg_rbd_le L)
      _ = γ.card * 64 := by rw [Finset.sum_const, smul_eq_mul]
  have hγn : γ ∉ MatchAt.nbr (Inc (rbd L)) γ := fun h => (Finset.mem_filter.1 h).2.1 rfl
  have hsite : ∀ v, ∑ Y ∈ MatchAt.site v, cw L y Y ≤ 2 * (4225 * y) := by
    intro v
    refine (sum_site_cw_le L hy hx1 v).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4225 * y)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - 4225 * y)]
  have hsum : cw L y γ + ∑ δ ∈ MatchAt.nbr (Inc (rbd L)) γ, cw L y δ ≤ γ.card := by
    rw [← Finset.sum_insert hγn]
    calc ∑ δ ∈ insert γ (MatchAt.nbr (Inc (rbd L)) γ), cw L y δ
        ≤ ∑ v ∈ B, ∑ Y ∈ MatchAt.site v, cw L y Y := by
          refine MatchAt.sum_meet_le _ (cw_nonneg L hy.le) B _ fun Y hY => ?_
          rcases Finset.mem_insert.1 hY with h | h
          · rw [h]
            obtain ⟨p, hp⟩ := hγ.1
            exact ⟨p, Finset.mem_inter.2 ⟨Finset.mem_biUnion.2 ⟨p, hp,
              mem_touchNbrs.2 (touch_self L p)⟩, hp⟩⟩
          · obtain ⟨p, hp, q, hq, hpq⟩ := (Finset.mem_filter.1 h).2.2
            have hqB : q ∈ B := by
              refine Finset.mem_biUnion.2 ⟨p, hp, mem_touchNbrs.2 ?_⟩
              rcases hpq with e | t
              · rw [← e]; exact touch_self L p
              · exact t
            exact ⟨q, Finset.mem_inter.2 ⟨hqB, hq⟩⟩
      _ ≤ ∑ _v ∈ B, 2 * (4225 * y) := Finset.sum_le_sum fun v _ => hsite v
      _ = B.card * (2 * (4225 * y)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (γ.card * 64 : ℕ) * (2 * (4225 * y)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hBcard
      _ ≤ γ.card := by
          push_cast
          have hc : (0 : ℝ) ≤ γ.card := Nat.cast_nonneg _
          have := mul_le_mul_of_nonneg_left hx hc
          nlinarith
  have hw : |actF F ζ γ| ≤ r ^ γ.card := actF_abs_le hr.le hb ζ γ
  have hc0 : 0 ≤ cw L y γ := cw_nonneg L hy.le γ
  have hkey : cw L y γ * Real.exp (-cw L y γ) ≤ 1 - Real.exp (-cw L y γ) := by
    have h1 := Real.add_one_le_exp (cw L y γ)
    have h2 : Real.exp (cw L y γ) * Real.exp (-cw L y γ) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos (-cw L y γ)
    nlinarith
  calc |actF F ζ γ| * Real.exp (∑ δ ∈ MatchAt.nbr (Inc (rbd L)) γ, cw L y δ)
      ≤ r ^ γ.card * Real.exp (γ.card - cw L y γ) :=
        mul_le_mul hw (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
          (pow_nonneg hr.le _)
    _ = cw L y γ * Real.exp (-cw L y γ) := by
        have hen : Real.exp (γ.card : ℝ) = Real.exp 1 ^ γ.card := by
          rw [← Real.exp_nat_mul, mul_one]
        rw [sub_eq_add_neg, Real.exp_add, hen, hcγ, hydef, mul_pow]
        ring
    _ ≤ 1 - Real.exp (-cw L y γ) := hkey

theorem Zg_pos {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} {r : ℝ} (hr : 0 < r)
    (hb : ∀ ζ X, |F ζ X| ≤ r ^ X.card) (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128)
    (ζ : RPlaq L → SUN.SU 2) : 0 < Zg F ζ :=
  MatchAt.Z_pos (ChunkActivity.inc_symm (rbd L)) (dob_actF hr hb hx ζ) _

/-- **The tail of the Dobrushin weights**: twice the weight of the sets of at least `m ≥ 1`
plaquettes is at most `4 |RPlaq L| (4225 y)^m`, for `0 < y` and `4225 y ≤ 1/128`. -/
theorem two_mul_tail_le {y : ℝ} (hy : 0 < y) (hx : 4225 * y ≤ 1 / 128) {m : ℕ} (hm : 1 ≤ m) :
    2 * ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card), cw L y X
      ≤ 4 * Fintype.card (RPlaq L) * (4225 * y) ^ m := by
  classical
  have hx1 : 4225 * y < 1 := by linarith
  have hx0 : 0 ≤ 4225 * y := by positivity
  have h1 : ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card), cw L y X
      = ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card),
          (if m ≤ X.card then cw L y X else 0) :=
    Finset.sum_congr rfl fun X hX => by rw [if_pos (Finset.mem_filter.1 hX).2]
  have h2 : ∑ X ∈ ((univ : Finset (RPlaq L)).powerset).filter (fun X => m ≤ X.card),
        (if m ≤ X.card then cw L y X else 0)
      ≤ ∑ v ∈ (univ : Finset (RPlaq L)), ∑ X ∈ MatchAt.site v,
          (if m ≤ X.card then cw L y X else 0) := by
    refine MatchAt.sum_meet_le _ (fun Y => ?_) _ _ fun Y hY => ?_
    · split_ifs
      · exact cw_nonneg L hy.le Y
      · exact le_rfl
    · have hc : 1 ≤ Y.card := hm.trans (Finset.mem_filter.1 hY).2
      obtain ⟨p, hp⟩ := Finset.card_pos.1 hc
      exact ⟨p, Finset.mem_inter.2 ⟨Finset.mem_univ _, hp⟩⟩
  have h3 : ∑ v ∈ (univ : Finset (RPlaq L)), ∑ X ∈ MatchAt.site v,
        (if m ≤ X.card then cw L y X else 0)
      ≤ Fintype.card (RPlaq L) * ((4225 * y) ^ m / (1 - 4225 * y)) := by
    calc _ ≤ ∑ _v ∈ (univ : Finset (RPlaq L)), (4225 * y) ^ m / (1 - 4225 * y) :=
          Finset.sum_le_sum fun v _ => sum_site_cw_tail_le L hy hx1 v m
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : (4225 * y) ^ m / (1 - 4225 * y) ≤ 2 * (4225 * y) ^ m := by
    rw [div_le_iff₀ (by linarith)]
    have := pow_nonneg hx0 m
    nlinarith
  have hcard : (0 : ℝ) ≤ Fintype.card (RPlaq L) := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_left h4 hcard
  rw [h1]
  nlinarith [h2, h3, h5]

/-- **The sheet free energy of a bounded centre-covariant activity**:
`log Z(F, 1) − log Z(F, sheet) ≤ 4 |RPlaq L| (4225 r e)^{L_a L_b}`. -/
theorem log_Zg_sub_le {F : (RPlaq L → SUN.SU 2) → Finset (RPlaq L) → ℝ} (hF : CentreLocal L F)
    {r : ℝ} (hr : 0 < r) (hb : ∀ ζ X, |F ζ X| ≤ r ^ X.card)
    (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128) {a b : Fin 4} (hab : a ≠ b)
    (hA : 1 ≤ L a * L b) :
    Real.log (Zg F (fun _ => 1)) - Real.log (Zg F (sheetR L a b))
      ≤ 4 * Fintype.card (RPlaq L) * (4225 * (r * Real.exp 1)) ^ (L a * L b) := by
  classical
  have hD1 := dob_actF hr hb hx (fun _ => 1)
  have hD2 := dob_actF hr hb hx (sheetR L a b)
  have hs := ChunkActivity.inc_symm (rbd L)
  have hag : ∀ γ ∈ (univ : Finset (RPlaq L)).powerset \
      ((univ : Finset (RPlaq L)).powerset).filter (fun X => L a * L b ≤ X.card),
      actF F (fun _ => 1) γ = actF F (sheetR L a b) γ := by
    intro γ hγ
    have hγB := (Finset.mem_sdiff.1 hγ).2
    have hlt : γ.card < L a * L b := by
      by_contra hn
      exact hγB (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hγ).1, not_lt.1 hn⟩)
    exact (actF_sheet_eq hF hab hlt).symm
  have hZ := Z_le_of_agree hs hD1 hD2 (univ : Finset (RPlaq L)).powerset
    (((univ : Finset (RPlaq L)).powerset).filter (fun X => L a * L b ≤ X.card)) hag
  have hZ1 : 0 < MatchAt.Z (Inc (rbd L)) (actF F (fun _ => 1)) (univ : Finset (RPlaq L)).powerset :=
    MatchAt.Z_pos hs hD1 _
  have hZ2 : 0 < MatchAt.Z (Inc (rbd L)) (actF F (sheetR L a b))
      (univ : Finset (RPlaq L)).powerset := MatchAt.Z_pos hs hD2 _
  have hl := Real.log_le_log hZ1 hZ
  rw [Real.log_mul (Real.exp_pos _).ne' hZ2.ne', Real.log_exp] at hl
  have ht := two_mul_tail_le (L := L) (mul_pos hr (Real.exp_pos 1)) hx hA
  unfold Zg
  linarith

/-- **An effective polymer description at a coarse scale** of a twisted/untwisted ratio `z`: an
activity `F` on the torus `L'`, centre-covariant and local, bounded by `r^{|X|}`, whose polymer
partition functions reproduce `z` as the ratio at the sheet of the plane `(a, b)` of `L'`. -/
structure EffGas (L' : Fin 4 → ℕ) (a b : Fin 4) (z r : ℝ) where
  /-- The effective activity. -/
  F : (RPlaq L' → SUN.SU 2) → Finset (RPlaq L') → ℝ
  centre : CentreLocal L' F
  bound : ∀ ζ X, |F ζ X| ≤ r ^ X.card
  ratio : z = Zg F (sheetR L' a b) / Zg F (fun _ => 1)

/-- **The Wilson activities describe the Wilson ratio at their own scale**: at every `β ≥ 0`,
`VortexStrong.zwP L β` is an `EffGas` for `zR L a b β` with the bound `1 − e^{−2β}`. -/
def effGas_wilson (L : Fin 4 → ℕ) (a b : Fin 4) {β : ℝ} (hβ : 0 ≤ β) :
    EffGas L a b (zR L a b β) (ChunkActivity.rate β) where
  F := VortexStrong.zwP L β
  centre := ⟨fun ζ χ hχ X => VortexStrong.zwP_coboundary L β ζ χ hχ X, fun ζ ζ' X h => by
    unfold VortexStrong.zwP
    refine integral_congr_ae (Eventually.of_forall fun U => Finset.prod_congr rfl fun q hq => ?_)
    rw [h q hq]⟩
  bound := VortexStrong.zwP_abs_le L hβ
  ratio := by
    unfold zR Zg
    rw [ZR_eq_ZRp, VortexStrong.ZRp_eq_polymerZ, VortexStrong.ZRp_eq_polymerZ]
    rfl

/-- **The deficit of an effectively described ratio**: `1 − z ≤ 4 |RPlaq L'| (4225 r e)^{L'_a L'_b}`. -/
theorem EffGas.one_sub_le {L' : Fin 4 → ℕ} {a b : Fin 4} {z r : ℝ} (G : EffGas L' a b z r)
    (hr : 0 < r) (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128) (hab : a ≠ b) (hA : 1 ≤ L' a * L' b) :
    1 - z ≤ 4 * Fintype.card (RPlaq L') * (4225 * (r * Real.exp 1)) ^ (L' a * L' b) := by
  have h := log_Zg_sub_le G.centre hr G.bound hx hab hA
  have hZ1 := Zg_pos hr G.bound hx (fun _ => 1)
  have hZ2 := Zg_pos hr G.bound hx (sheetR L' a b)
  have hz : 0 < z := by rw [G.ratio]; exact div_pos hZ2 hZ1
  have hq := G.ratio
  have hlog : Real.log z = Real.log (Zg G.F (sheetR L' a b)) - Real.log (Zg G.F (fun _ => 1)) := by
    calc Real.log z = Real.log (Zg G.F (sheetR L' a b) / Zg G.F (fun _ => 1)) := by rw [← hq]
      _ = _ := Real.log_div hZ2.ne' hZ1.ne'
  have := Real.log_le_sub_one_of_pos hz
  linarith

/-- **On a corner torus**: an `EffGas` on `Lc m i` in the plane `(i, ν)`, `ν ≠ i`, `m ≥ 1`, and
`t ≤ m` give `1 − z ≤ 2048 e^{−t}`. -/
theorem one_sub_le_of_effGas_Lc {m : ℕ} (hm : 1 ≤ m) {i ν : Fin 4} (hν : ν ≠ i) {z r t : ℝ}
    (G : EffGas (Lc m i) i ν z r) (hr : 0 < r) (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128)
    (ht : t ≤ m) : 1 - z ≤ 2048 * Real.exp (-t) := by
  obtain ⟨N, hN⟩ : ∃ N, N = Lc m i i * Lc m i ν := ⟨_, rfl⟩
  have hii : Lc m i i = m := VortexTorus.Lc_self m i
  have hνm : m ≤ Lc m i ν := VortexTorus.le_Lc m i ν
  have hNm : m ≤ N := by
    rw [hN, hii]
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * Lc m i ν := Nat.mul_le_mul_left m (by omega)
  have hA : 1 ≤ Lc m i i * Lc m i ν := by rw [← hN]; exact le_trans hm hNm
  have hv := G.one_sub_le hr hx (Ne.symm hν) hA
  rw [← hN] at hv
  have hcard := card_rplaq_Lc_le m i ν
  have hNR : ((N : ℕ) : ℝ) = ((Lc m i i : ℕ) : ℝ) * ((Lc m i ν : ℕ) : ℝ) := by
    rw [hN, Nat.cast_mul]
  rw [← hNR] at hcard
  obtain ⟨x, hxdef⟩ : ∃ x, x = 4225 * (r * Real.exp 1) := ⟨_, rfl⟩
  rw [← hxdef] at hv hx
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsq : ((N : ℕ) : ℝ) ^ 2 ≤ 2 * Real.exp N := by
    have := Real.quadratic_le_exp_of_nonneg hN0
    linarith
  have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hee : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have h1 : Real.exp 1 * x ≤ Real.exp (-1) := by
    have hh1 := mul_lt_mul_of_pos_left he3 (Real.exp_pos (-1))
    have hh2 := mul_le_mul_of_nonneg_right he3.le hx0.le
    linarith
  have hexN : Real.exp N * x ^ N ≤ Real.exp (-(N : ℝ)) := by
    calc Real.exp N * x ^ N = (Real.exp 1 * x) ^ N := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_one]
      _ ≤ (Real.exp (-1)) ^ N := pow_le_pow_left₀ (by positivity) h1 N
      _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hxN : 0 ≤ x ^ N := pow_nonneg hx0.le N
  have hc1 := mul_le_mul_of_nonneg_right hcard hxN
  have hc2 := mul_le_mul_of_nonneg_right hsq hxN
  have hc3 : Real.exp (-(N : ℝ)) ≤ Real.exp (-t) := by
    have : t ≤ (N : ℝ) := ht.trans (by exact_mod_cast hNm)
    exact Real.exp_le_exp.2 (by linarith)
  linarith [hv, hc1, hc2, hexN, hc3]

/-- **Condensation at the aperture scale**, on the window of `FluxCost.VortexCostAt`: eventually in
`β`, every fine ratio `zR (Lc n i) i ν β` with `n a ∈ [2ℓ, 5ℓ]` has an `EffGas` description with
activity bound `r` on a corner torus `Lc m i` with `κ n a ≤ m`. Since `EffGas` fixes only the number
`zR`, this is a decay bound on `zR` (`effCondensationAt_of_elec` gives it from
`elecRatio ≤ r^{Lc m i i · Lc m i ν}`), not a block-spin statement. DERIVED: `2` and `5` the window of
`FluxCost.VortexCostAt` (`5` leaves room for the power of two at or above `⌈2ℓ/a⌉`); `2` also the
least side and the rank of `SU(2)`. -/
def EffCondensationAt (κ r ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β → (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i}, ∃ m : ℕ, 1 ≤ m ∧
      κ * ((n : ℝ) * AsymptoticScaling.aRun 2 β) ≤ m ∧
      Nonempty (EffGas (Lc m i) i ν.1 (zR (Lc n i) i ν.1 β) r)

/-- **(V) from condensation at the aperture scale**: `0 < r`, `4225 r e ≤ 1/128` and
`EffCondensationAt κ r ℓ` give `VortexCostAt κ 2048 ℓ`. -/
theorem vortexCostAt_of_eff {κ r ℓ : ℝ} (hr : 0 < r) (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128)
    (h : EffCondensationAt κ r ℓ) : FluxCost.VortexCostAt κ 2048 ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hup i ν
  obtain ⟨m, hm1, hκm, ⟨G⟩⟩ := hβ n hn h2 hlo hup i ν
  exact one_sub_le_of_effGas_Lc hm1 ν.2 G hr hx hκm

/-- **The flux half of the binding statement at one constant**: condensation at the aperture scale
eventually in `ℓ`, at one `κ > 0` and `r`, gives `VortexCostAt κ 2048 ℓ` eventually in `ℓ`. -/
theorem flux_half_of_eff {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hx : 4225 * (r * Real.exp 1) ≤ 1 / 128) (h : ∀ᶠ ℓ in atTop, EffCondensationAt κ r ℓ) :
    ∃ σ A : ℝ, 0 < σ ∧ ∀ᶠ ℓ in atTop, FluxCost.VortexCostAt σ A ℓ :=
  ⟨κ, 2048, hκ, h.mono fun _ hℓ => vortexCostAt_of_eff hr hx hℓ⟩

end Effective

/-! ## 2. 't Hooft duality: the vortex ratio is the electric-flux ratio -/

section Electric

open MassGap.KernelPower MassGap.FluxSectorFourier MassGap.TwistDeficitUnionN

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {act : G → X → X} {a : X → X → ℝ}

omit [Fintype G] [DecidableEq G] in
/-- A character takes the values `±1` on an element of order two. -/
theorem char_two_torsion (ψ : AddChar G ℂ) {g : G} (hg : g + g = 0) : ψ g = 1 ∨ ψ g = -1 := by
  have h : ψ g * ψ g = 1 := by rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]
  exact mul_self_eq_one_iff.1 h

variable (μ) in
open scoped Classical in
/-- **The odd-sector trace of `g`**: the summed trace of the flux sectors `ψ` with `ψ(g) ≠ 1`. -/
def oddTrace (a : X → X → ℝ) (act : G → X → X) (g : G) : ℝ :=
  ∑ ψ ∈ univ.filter (fun ψ : AddChar G ℂ => ψ g ≠ 1), sectorTrace μ a act ψ

/-- **A twist of order two removes twice the odd sectors**: `deficit g = 2 · oddTrace g`. -/
theorem deficit_eq_two_oddTrace (ha : Bdd a) (hsym : ∀ x y, a x y = a y x)
    (hA : CentreAction μ act) {g : G} (hg : g + g = 0) :
    deficit μ a act g = 2 * oddTrace μ a act g := by
  classical
  rw [deficit_eq_sum ha hsym hA, oddTrace, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rcases char_two_torsion ψ hg with h | h
  · rw [if_neg (fun hne => hne h), h, Complex.one_re]
    ring
  · have hne : ψ g ≠ 1 := by rw [h]; norm_num
    rw [if_pos hne, h, Complex.neg_re, Complex.one_re]
    ring

open MassGap.CentreSectorSeedN
open MassGap.SliceCentreAction (Cen centreAction)

/-- **The trace of the odd electric flux in direction `ν`** on the slice of step `i` at side `n`. -/
def oddFlux (β : ℝ) (n : ℕ) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) : ℝ :=
  oddTrace (hSN 2 n i) (halfKN 2 β n i)
    (SliceCentreAction.act (μ := i) (T := CentreSectorSeed.Tr n i) (N := 2)) (Pi.single ν 1)

/-- **The vortex deficit is twice the odd electric-flux share**:
`1 − zR (Lc n i) i ν β = 2 · oddFlux / Z`, `Z = hs(halfKN)` the trace. -/
theorem one_sub_zR_eq_oddFlux {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) :
    1 - zR (Lc n i) i ν.1 β = 2 * oddFlux β n i ν / hs (hSN 2 n i) (halfKN 2 β n i) := by
  have hg : (Pi.single ν (1 : ZMod 2) : Cen i 2) + Pi.single ν 1 = 0 := by
    funext j
    rw [Pi.add_apply, Pi.zero_apply]
    rcases eq_or_ne j ν with rfl | h
    · rw [Pi.single_eq_same]; decide
    · rw [Pi.single_eq_of_ne h, add_zero]
  rw [← twistRatioN_eq_zR hβ hn he i ν, TwistDeficitUnionN.one_sub_twistRatioN (N := 2) hβ n i,
    deficit_eq_two_oddTrace (bdd_halfKN (N := 2) hβ n i) (symm_halfKN (N := 2) hβ n i)
      centreAction hg]
  rfl

/-- **The electric-flux ratio** `e^{−F_el}`: the odd-sector trace over the even-sector trace. -/
def elecRatio (β : ℝ) (n : ℕ) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) : ℝ :=
  oddFlux β n i ν / (hs (hSN 2 n i) (halfKN 2 β n i) - oddFlux β n i ν)

/-- **'t Hooft duality at `SU(2)`**: `e^{−F_el} = (1 − zR)/(1 + zR)`. -/
theorem elecRatio_eq {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) :
    elecRatio β n i ν = (1 - zR (Lc n i) i ν.1 β) / (1 + zR (Lc n i) i ν.1 β) := by
  unfold elecRatio
  have h := one_sub_zR_eq_oddFlux hβ hn he i ν
  have hH : 0 < hs (hSN 2 n i) (halfKN 2 β n i) := hs_halfKN_pos (N := 2) hβ n i
  have hz := zR_pos (Lc n i) i ν.1 β
  set z := zR (Lc n i) i ν.1 β
  set H := hs (hSN 2 n i) (halfKN 2 β n i)
  set O := oddFlux β n i ν
  have hO : 2 * O = (1 - z) * H := by
    rw [h, div_mul_cancel₀ _ hH.ne']
  have hHO : 0 < H - O := by nlinarith [mul_pos hz hH]
  have h1z : 1 + z ≠ 0 := by linarith
  rw [div_eq_div_iff hHO.ne' h1z]
  linarith

/-- **The electric ratio is at most the vortex deficit**, for `0 ≤ z ≤ 1`. -/
theorem elec_le_one_sub {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : (1 - z) / (1 + z) ≤ 1 - z := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The vortex deficit is at most twice the electric ratio**, for `0 ≤ z`. -/
theorem one_sub_le_two_elec {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : 1 - z ≤ 2 * ((1 - z) / (1 + z)) := by
  rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
  nlinarith

/-- **The electric flux costs `σ` per length** on the window of `FluxCost.VortexCostAt`. DERIVED: `2` and
`5` the window of `FluxCost.VortexCostAt`; `2` also the least side and the rank of `SU(2)`. -/
def ElecCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β → (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ 5 * ℓ →
    ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i},
      elecRatio β n i ν ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun 2 β)))

/-- **(V) gives the electric form at the same constants.** -/
theorem elecCostAt_of_vortexCostAt {σ A ℓ : ℝ} (h : FluxCost.VortexCostAt σ A ℓ) :
    ElecCostAt σ A ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  have he := FluxCost.even_of_pow2 hn h2
  have hz1 := VortexCondense.zR_Lc_le_one hβ0 h2 he i ν
  have hz0 := (zR_pos (Lc n i) i ν.1 β).le
  rw [elecRatio_eq hβ0 h2 he i ν]
  exact (elec_le_one_sub hz0 hz1).trans (hβ n hn h2 hlo hup i ν)

/-- **The electric form gives (V) at twice the constant.** -/
theorem vortexCostAt_of_elecCostAt {σ A ℓ : ℝ} (h : ElecCostAt σ A ℓ) :
    FluxCost.VortexCostAt σ (2 * A) ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  have he := FluxCost.even_of_pow2 hn h2
  have hz1 := VortexCondense.zR_Lc_le_one hβ0 h2 he i ν
  have hz0 := (zR_pos (Lc n i) i ν.1 β).le
  have hE := hβ n hn h2 hlo hup i ν
  rw [elecRatio_eq hβ0 h2 he i ν] at hE
  have h2E := one_sub_le_two_elec hz0 hz1
  linarith

end Electric

/-! ## 3. Readings of the states and the ratio `zR` -/

section Readings

variable {α : Type*} [Fintype α]

/-- **The reading of `f` in the state of the weight `w`**: `Σ w f / Σ w`. -/
def read (w f : α → ℝ) : ℝ := (∑ x, w x * f x) / ∑ x, w x

/-- **Agreement on a set `V` of readings.** -/
def AgreeOn (V : Set (α → ℝ)) (w w' : α → ℝ) : Prop := ∀ f ∈ V, read w f = read w' f

/-- **The partition-function ratio** `Σ w' / Σ w`. -/
def ratio (w w' : α → ℝ) : ℝ := (∑ x, w' x) / ∑ x, w x

/-- The weight `w` scaled by `k`. -/
def smulW (k : ℝ) (w : α → ℝ) : α → ℝ := fun x => k * w x

/-- **Scaling a weight changes no reading.** -/
theorem read_smul (w f : α → ℝ) {k : ℝ} (hk : k ≠ 0) : read (smulW k w) f = read w f := by
  show (∑ x, k * w x * f x) / ∑ x, k * w x = (∑ x, w x * f x) / ∑ x, w x
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ hk]

/-- **Scaling a weight multiplies the ratio.** -/
theorem ratio_smul (w : α → ℝ) (k : ℝ) (hw : ∑ x, w x ≠ 0) : ratio w (smulW k w) = k := by
  show (∑ x, k * w x) / ∑ x, w x = k
  rw [← Finset.mul_sum, mul_div_assoc, div_self hw, mul_one]

theorem agreeOn_smul (V : Set (α → ℝ)) (w : α → ℝ) {k : ℝ} (hk : k ≠ 0) :
    AgreeOn V w (smulW k w) := fun f _ => (read_smul w f hk).symm

/-- **No function of the two states gives the ratio**: there is no `Φ` with
`ratio w w' = Φ (read w) (read w')` for all positive weights `w, w'`. -/
theorem not_ratio_of_states [Nonempty α] :
    ¬ ∃ Φ : ((α → ℝ) → ℝ) → ((α → ℝ) → ℝ) → ℝ,
      ∀ w w' : α → ℝ, (∀ x, 0 < w x) → (∀ x, 0 < w' x) → ratio w w' = Φ (read w) (read w') := by
  rintro ⟨Φ, hΦ⟩
  have hw : ∀ _ : α, (0 : ℝ) < 1 := fun _ => one_pos
  have hs : (∑ _x : α, (1 : ℝ)) ≠ 0 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast Fintype.card_ne_zero
  have h1 := hΦ (fun _ => 1) (fun _ => 1) hw hw
  have h2 := hΦ (fun _ => 1) (smulW (1 / 2) (fun _ => 1)) hw
    (fun x => by unfold smulW; norm_num)
  have hr : read (smulW (1 / 2) (fun _ : α => (1 : ℝ))) = read (fun _ => 1) :=
    funext fun f => read_smul _ f (by norm_num)
  rw [hr, ratio_smul _ _ hs] at h2
  have h3 : ratio (fun _ : α => (1 : ℝ)) (fun _ => 1) = 1 := by
    unfold ratio; exact div_self hs
  rw [h3] at h1
  linarith

variable {γ : Type*} [Fintype γ]

/-- A sum over `α × γ` of a product of a function of each coordinate. -/
theorem sum_prod_mul (u : α → ℝ) (v : γ → ℝ) :
    ∑ z : α × γ, u z.1 * v z.2 = (∑ x, u x) * ∑ y, v y := by
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **A twist on a hidden coordinate agrees on every reading of the visible one**: for the product
weight `p(x) q(y)` and the twisted weight `p(x) q(y) h(y)`, every function of `x` reads the same,
and the ratio is `Σ q h / Σ q`. -/
theorem hidden_twist_agrees (p : α → ℝ) (q h : γ → ℝ) (hp : ∑ x, p x ≠ 0)
    (hq : ∑ y, q y ≠ 0) (hqh : ∑ y, q y * h y ≠ 0) :
    AgreeOn (RelativeGap.readings (Prod.fst : α × γ → α)) (fun z => p z.1 * q z.2)
        (fun z => p z.1 * q z.2 * h z.2) ∧
      ratio (fun z : α × γ => p z.1 * q z.2) (fun z => p z.1 * q z.2 * h z.2)
        = (∑ y, q y * h y) / ∑ y, q y := by
  have sP : ∑ z : α × γ, p z.1 * q z.2 = (∑ x, p x) * ∑ y, q y := sum_prod_mul p q
  have sPh : ∑ z : α × γ, p z.1 * q z.2 * h z.2 = (∑ x, p x) * ∑ y, q y * h y := by
    calc ∑ z : α × γ, p z.1 * q z.2 * h z.2 = ∑ z : α × γ, p z.1 * (q z.2 * h z.2) :=
          Finset.sum_congr rfl fun z _ => mul_assoc _ _ _
      _ = (∑ x, p x) * ∑ y, q y * h y := sum_prod_mul p (fun y => q y * h y)
  refine ⟨?_, ?_⟩
  · rintro f ⟨u, rfl⟩
    have nP : ∑ z : α × γ, p z.1 * q z.2 * (u ∘ Prod.fst) z = (∑ x, p x * u x) * ∑ y, q y := by
      calc ∑ z : α × γ, p z.1 * q z.2 * (u ∘ Prod.fst) z
          = ∑ z : α × γ, (p z.1 * u z.1) * q z.2 := Finset.sum_congr rfl fun z _ => by
            show p z.1 * q z.2 * u z.1 = p z.1 * u z.1 * q z.2
            ring
        _ = (∑ x, p x * u x) * ∑ y, q y := sum_prod_mul (fun x => p x * u x) q
    have nPh : ∑ z : α × γ, p z.1 * q z.2 * h z.2 * (u ∘ Prod.fst) z
        = (∑ x, p x * u x) * ∑ y, q y * h y := by
      calc ∑ z : α × γ, p z.1 * q z.2 * h z.2 * (u ∘ Prod.fst) z
          = ∑ z : α × γ, (p z.1 * u z.1) * (q z.2 * h z.2) := Finset.sum_congr rfl fun z _ => by
            show p z.1 * q z.2 * h z.2 * u z.1 = p z.1 * u z.1 * (q z.2 * h z.2)
            ring
        _ = (∑ x, p x * u x) * ∑ y, q y * h y :=
            sum_prod_mul (fun x => p x * u x) (fun y => q y * h y)
    show (∑ z : α × γ, p z.1 * q z.2 * (u ∘ Prod.fst) z) / ∑ z : α × γ, p z.1 * q z.2
      = (∑ z : α × γ, p z.1 * q z.2 * h z.2 * (u ∘ Prod.fst) z)
        / ∑ z : α × γ, p z.1 * q z.2 * h z.2
    rw [nP, nPh, sP, sPh, mul_div_mul_right _ _ hq, mul_div_mul_right _ _ hqh]
  · show (∑ z : α × γ, p z.1 * q z.2 * h z.2) / ∑ z : α × γ, p z.1 * q z.2 = _
    rw [sP, sPh, mul_div_mul_left _ _ hp]

/-- **The hidden twist reaches every ratio in `(0, 1]`**: for `k ∈ (0, 1]`, the twist `h = k`,
`0 < h ≤ 1`, of the uniform product weight agrees on every reading of the visible coordinate and has
ratio `k`. -/
theorem hidden_twist_any_ratio [Nonempty α] [Nonempty γ] {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) :
    ∃ h : γ → ℝ, (∀ y, 0 < h y ∧ h y ≤ 1) ∧
      AgreeOn (RelativeGap.readings (Prod.fst : α × γ → α)) (fun _ => 1)
        (fun z : α × γ => h z.2) ∧
      ratio (fun _ : α × γ => (1 : ℝ)) (fun z => h z.2) = k := by
  have hcα : (∑ _x : α, (1 : ℝ)) ≠ 0 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast Fintype.card_ne_zero
  have hcγ : (∑ _y : γ, (1 : ℝ)) ≠ 0 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact_mod_cast Fintype.card_ne_zero
  have hkγ : (∑ _y : γ, (1 : ℝ) * k) ≠ 0 := by
    rw [← Finset.sum_mul]; exact mul_ne_zero hcγ hk0.ne'
  obtain ⟨hA, -⟩ := hidden_twist_agrees (α := α) (fun _ => 1) (fun _ => 1) (fun _ => k) hcα hcγ hkγ
  have hcard : (Fintype.card (α × γ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ => k, fun _ => ⟨hk0, hk1⟩, ?_, ?_⟩
  · intro f hf
    have := hA f hf
    simpa using this
  · show (∑ _z : α × γ, k) / ∑ _z : α × γ, (1 : ℝ) = k
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one,
      mul_div_cancel_left₀ _ hcard]

end Readings

section Wilson

variable (L : Fin 4 → ℕ)

/-- **The sheet observable**: `exp(−β Σ_q (φ(ζ_q U_q) − φ(U_q)))` with `ζ = sheetR L a b`. -/
def sheetObs (a b : Fin 4) (β : ℝ) (U : RLink L → SUN.SU 2) : ℝ :=
  Real.exp (-β * ∑ q, (wd (sheetR L a b q * rhol L q U) - wd (rhol L q U)))

/-- **The twisted torus is the untwisted integral of the sheet observable.** -/
theorem ZRp_sheet_eq (a b : Fin 4) (β : ℝ) :
    ZRp L β (sheetR L a b) = ∫ U, sheetObs L a b β U * Real.exp (-β * ∑ q, wd (1 * rhol L q U))
      ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := by
  unfold ZRp
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp (-β * ∑ q, wd (sheetR L a b q * rhol L q U))
    = sheetObs L a b β U * Real.exp (-β * ∑ q, wd (1 * rhol L q U))
  unfold sheetObs
  rw [← Real.exp_add]
  congr 1
  simp only [one_mul, Finset.sum_sub_distrib]
  ring

/-- **`zR` is a reading of one observable**: the untwisted expectation of `sheetObs`. -/
theorem zR_eq_read (a b : Fin 4) (β : ℝ) :
    zR L a b β = (∫ U, sheetObs L a b β U * Real.exp (-β * ∑ q, wd (1 * rhol L q U))
      ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))) / ZRp L β (fun _ => 1) := by
  unfold zR
  rw [ZR_eq_ZRp, ZRp_sheet_eq]

open scoped Classical in
/-- **The sheet observable reads the sheet only**: its sum runs over the plaquettes where
`sheetR L a b` is not `1`. -/
theorem sheetObs_eq_filter (a b : Fin 4) (β : ℝ) (U : RLink L → SUN.SU 2) :
    sheetObs L a b β U = Real.exp (-β * ∑ q ∈ univ.filter (fun q => sheetR L a b q ≠ 1),
      (wd (sheetR L a b q * rhol L q U) - wd (rhol L q U))) := by
  unfold sheetObs
  congr 2
  refine (Finset.sum_filter_of_ne (p := fun q => sheetR L a b q ≠ 1) ?_).symm
  intro q _ hq h1
  exact hq (by rw [h1, one_mul, sub_self])

end Wilson

/-! ## 4. A one-polymer `EffGas` realises any ratio near `1` -/

section Witness

open MassGap.TwistedTraceBound (negOne coe_negOne negOne_mul_self)

/-- `-1 ≠ 1` in `SU(2)`. An alias of `CubeFlux.negOne_ne_one`. -/
alias w_negOne_ne_one := MassGap.CubeFlux.negOne_ne_one

theorem w_central_two {w : SUN.SU 2} (hw : ∀ g, w * g = g * w) : w = 1 ∨ w = negOne := by
  have hC : MassGap.NonAbelianForget.Commutes (w : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro g hg
    exact (congrArg Subtype.val (hw ⟨g, hg⟩)).symm
  obtain ⟨hoff, hdiag⟩ := MassGap.NonAbelianForget.commutant_SU hC
  set ω := (w : Matrix (Fin 2) (Fin 2) ℂ) 0 0 with hωdef
  have hM : (w : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (fun _ => ω) := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq]; exact hdiag i 0
    · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (w : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp w.2).2
  rw [hM, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have h2 : ω * ω = 1 := by rw [← sq]; exact hdet
  rcases mul_self_eq_one_iff.1 h2 with h | h
  · left; apply Subtype.ext; rw [hM, h]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · right; apply Subtype.ext; rw [hM, h, coe_negOne]
    ext i j; fin_cases i <;> fin_cases j <;> simp

open scoped Classical in
/-- The centre sign: `1` at `1`, `−1` at `−1`, `0` elsewhere. -/
def wsg (U : SUN.SU 2) : ℝ := if U = 1 then 1 else if U = negOne then -1 else 0

theorem wsg_one : wsg 1 = 1 := by unfold wsg; simp

theorem wsg_negOne : wsg negOne = -1 := by
  unfold wsg; rw [if_neg w_negOne_ne_one, if_pos rfl]

theorem wsg_abs_le (U : SUN.SU 2) : |wsg U| ≤ 1 := by
  unfold wsg; split_ifs <;> norm_num

theorem wsg_mul_c (U : SUN.SU 2) {w : SUN.SU 2} (hw : ∀ g, w * g = g * w) :
    wsg (U * w) = wsg U * wsg w := by
  rcases w_central_two hw with rfl | rfl
  · rw [mul_one, wsg_one, mul_one]
  · rw [wsg_negOne]
    by_cases h1 : U = 1
    · subst h1; rw [one_mul, wsg_negOne, wsg_one]; ring
    by_cases h2 : U = negOne
    · subst h2; rw [negOne_mul_self, wsg_one, wsg_negOne]; ring
    have e1 : U * negOne ≠ 1 := fun h => h2 (by
      calc U = U * negOne * negOne := by rw [mul_assoc, negOne_mul_self, mul_one]
        _ = negOne := by rw [h, one_mul])
    have e2 : U * negOne ≠ negOne := fun h => h1 (by
      calc U = U * negOne * negOne := by rw [mul_assoc, negOne_mul_self, mul_one]
        _ = 1 := by rw [h, negOne_mul_self])
    unfold wsg
    rw [if_neg e1, if_neg e2, if_neg h1, if_neg h2]; ring

theorem wsg_inv_c {w : SUN.SU 2} (hw : ∀ g, w * g = g * w) : wsg w⁻¹ = wsg w := by
  rcases w_central_two hw with rfl | rfl
  · rw [inv_one]
  · rw [inv_eq_of_mul_eq_one_right negOne_mul_self]

theorem wsg_sq_c {w : SUN.SU 2} (hw : ∀ g, w * g = g * w) : wsg w * wsg w = 1 := by
  rcases w_central_two hw with rfl | rfl
  · rw [wsg_one]; norm_num
  · rw [wsg_negOne]; norm_num

theorem w_rot_val {N : ℕ} (j : Fin N) (h : j.val + 1 < N) : (finRotate N j).val = j.val + 1 := by
  rcases N with _ | N
  · exact j.elim0
  · rw [coe_finRotate_of_ne_last]
    intro hj
    rw [hj, Fin.val_last] at h
    omega

variable (L : Fin 4 → ℕ) (hL : ∀ k, 0 < L k) {a b : Fin 4}

/-- A point of the `(a, b)` plane through the origin. -/
def wpt (s : Fin (L a)) (t : Fin (L b)) : RSite L :=
  Function.update (Function.update (fun k => (⟨0, hL k⟩ : Fin (L k))) a s) b t

/-- The `(a, b)` plaquette at `(s, t)`. -/
def wpq (p : Fin (L a) × Fin (L b)) : RPlaq L := ((a, b), wpt L hL p.1 p.2)

variable {L hL}

theorem wpt_a (hab : a ≠ b) (s : Fin (L a)) (t : Fin (L b)) : wpt L hL s t a = s := by
  unfold wpt; rw [Function.update_of_ne hab, Function.update_self]

theorem wpt_b (s : Fin (L a)) (t : Fin (L b)) : wpt L hL s t b = t := by
  unfold wpt; rw [Function.update_self]

theorem wshift_b (s : Fin (L a)) (t : Fin (L b)) :
    rshift L b (wpt L hL s t) = wpt L hL s (finRotate (L b) t) := by
  unfold rshift; rw [wpt_b]; unfold wpt; rw [Function.update_idem]

theorem wshift_a (hab : a ≠ b) (s : Fin (L a)) (t : Fin (L b)) :
    rshift L a (wpt L hL s t) = wpt L hL (finRotate (L a) s) t := by
  unfold rshift; rw [wpt_a hab]; unfold wpt
  rw [Function.update_comm hab.symm, Function.update_idem]

theorem wpq_inj (hab : a ≠ b) : Function.Injective (wpq L hL (a := a) (b := b)) := by
  intro p p' h
  have h2 := congrArg Prod.snd h
  dsimp only [wpq] at h2
  have ha := congrFun h2 a
  have hb := congrFun h2 b
  rw [wpt_a hab, wpt_a hab] at ha
  rw [wpt_b, wpt_b] at hb
  exact Prod.ext ha hb

/-- The plane slice. -/
def wX0 : Finset (RPlaq L) := univ.image (wpq L hL (a := a) (b := b))

theorem wX0_card (hab : a ≠ b) : (wX0 (L := L) (hL := hL) (a := a) (b := b)).card = L a * L b := by
  unfold wX0
  rw [Finset.card_image_of_injective _ (wpq_inj hab), Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

/-- The detector: the product of centre signs over the plane slice. -/
def wPhi (ζ : RPlaq L → SUN.SU 2) : ℝ := ∏ p : Fin (L a) × Fin (L b), wsg (ζ (wpq L hL p))

theorem wPhi_abs_le (ζ : RPlaq L → SUN.SU 2) : |wPhi (L := L) (hL := hL) (a := a) (b := b) ζ| ≤ 1 := by
  unfold wPhi
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => wsg_abs_le _)

theorem wPhi_one : wPhi (L := L) (hL := hL) (a := a) (b := b) (fun _ => 1) = 1 := by
  unfold wPhi; simp only [wsg_one, Finset.prod_const_one]

theorem wPhi_sheet (hab : a ≠ b) :
    wPhi (L := L) (hL := hL) (a := a) (b := b) (sheetR L a b) = -1 := by
  classical
  unfold wPhi
  set p0 : Fin (L a) × Fin (L b) := (⟨0, hL a⟩, ⟨0, hL b⟩)
  have hval : ∀ p : Fin (L a) × Fin (L b), wsg (sheetR L a b (wpq L hL p))
      = if p0 = p then -1 else 1 := by
    intro p
    have hs : sheetR L a b (wpq L hL p) = if p.1.val = 0 ∧ p.2.val = 0 then negOne else 1 := by
      simp only [sheetR, wpq, wpt_a hab, wpt_b, true_or, true_and]
    rw [hs]
    have hiff : (p.1.val = 0 ∧ p.2.val = 0) ↔ p0 = p := by
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)
      · rintro rfl; exact ⟨rfl, rfl⟩
    by_cases h : p0 = p
    · rw [if_pos (hiff.2 h), if_pos h, wsg_negOne]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, wsg_one]
  simp only [hval]
  simp

theorem wPhi_cob (hab : a ≠ b) (ζ : RPlaq L → SUN.SU 2) (χ : RLink L → SUN.SU 2)
    (hχ : ∀ l g, χ l * g = g * χ l) :
    wPhi (L := L) (hL := hL) (a := a) (b := b) (fun q => ζ q * rhol L q χ)
      = wPhi (L := L) (hL := hL) (a := a) (b := b) ζ := by
  unfold wPhi
  have hi : ∀ l g, (χ l)⁻¹ * g = g * (χ l)⁻¹ := fun l g =>
    GapSideVortexStepSign.inv_central (hχ l) g
  have hterm : ∀ p : Fin (L a) × Fin (L b), wsg (ζ (wpq L hL p) * rhol L (wpq L hL p) χ)
      = wsg (ζ (wpq L hL p)) * (wsg (χ (a, wpt L hL p.1 p.2))
        * wsg (χ (b, wpt L hL (finRotate _ p.1) p.2))
        * wsg (χ (a, wpt L hL p.1 (finRotate _ p.2))) * wsg (χ (b, wpt L hL p.1 p.2))) := by
    intro p
    unfold rhol
    simp only [wpq, wshift_a hab, wshift_b]
    simp only [← mul_assoc]
    rw [wsg_mul_c _ (hi _), wsg_mul_c _ (hi _), wsg_mul_c _ (hχ _), wsg_mul_c _ (hχ _),
      wsg_inv_c (hχ _), wsg_inv_c (hχ _)]
  beta_reduce
  simp only [hterm]
  rw [Finset.prod_mul_distrib]
  have hrest : ∏ p : Fin (L a) × Fin (L b), (wsg (χ (a, wpt L hL p.1 p.2))
        * wsg (χ (b, wpt L hL (finRotate _ p.1) p.2))
        * wsg (χ (a, wpt L hL p.1 (finRotate _ p.2))) * wsg (χ (b, wpt L hL p.1 p.2))) = 1 := by
    simp only [Finset.prod_mul_distrib]
    have eB : ∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL (finRotate _ p.1) p.2))
        = ∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL p.1 p.2)) :=
      Fintype.prod_equiv (Equiv.prodCongr (finRotate (L a)) (Equiv.refl _)) _ _ (fun _ => rfl)
    have eA : ∏ p : Fin (L a) × Fin (L b), wsg (χ (a, wpt L hL p.1 (finRotate _ p.2)))
        = ∏ p : Fin (L a) × Fin (L b), wsg (χ (a, wpt L hL p.1 p.2)) :=
      Fintype.prod_equiv (Equiv.prodCongr (Equiv.refl _) (finRotate (L b))) _ _ (fun _ => rfl)
    rw [eB, eA]
    have hA : (∏ p : Fin (L a) × Fin (L b), wsg (χ (a, wpt L hL p.1 p.2)))
        * (∏ p : Fin (L a) × Fin (L b), wsg (χ (a, wpt L hL p.1 p.2))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun p _ => wsg_sq_c (hχ _)
    have hB : (∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL p.1 p.2)))
        * (∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL p.1 p.2))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun p _ => wsg_sq_c (hχ _)
    linear_combination (∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL p.1 p.2)))
      * (∏ p : Fin (L a) × Fin (L b), wsg (χ (b, wpt L hL p.1 p.2))) * hA + hB
  rw [hrest, mul_one]

open scoped Classical in
/-- The one-polymer activity. -/
def wF (c : ℝ) (ζ : RPlaq L → SUN.SU 2) (X : Finset (RPlaq L)) : ℝ :=
  if X = wX0 (L := L) (hL := hL) (a := a) (b := b) then c * wPhi (L := L) (hL := hL) (a := a) (b := b) ζ
  else 0

theorem wF_centre (hab : a ≠ b) (c : ℝ) :
    CentreLocal L (wF (L := L) (hL := hL) (a := a) (b := b) c) := by
  classical
  refine ⟨fun ζ χ hχ X => ?_, fun ζ ζ' X h => ?_⟩
  · unfold wF; rw [wPhi_cob hab ζ χ hχ]
  · unfold wF
    split_ifs with hX
    · congr 1
      unfold wPhi
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [h (wpq L hL p) (by rw [hX]; unfold wX0; exact Finset.mem_image_of_mem _ (Finset.mem_univ p))]
    · rfl

/-- The plane slice is touch-connected. -/
theorem wX0_conn (hab : a ≠ b) :
    (wX0 (L := L) (hL := hL) (a := a) (b := b)).Nonempty ∧
      TouchConnected (rbd L) (wX0 (L := L) (hL := hL) (a := a) (b := b)) := by
  classical
  have mem : ∀ p, wpq L hL p ∈ wX0 (L := L) (hL := hL) (a := a) (b := b) := fun p => by
    unfold wX0; exact Finset.mem_image_of_mem _ (Finset.mem_univ p)
  refine ⟨⟨_, mem (⟨0, hL a⟩, ⟨0, hL b⟩)⟩, ?_⟩
  set R := fun x y => x ∈ wX0 (L := L) (hL := hL) (a := a) (b := b) ∧
    y ∈ wX0 (L := L) (hL := hL) (a := a) (b := b) ∧ StrongCoupling.Touch (rbd L) x y
  have hsymm : ∀ {x y}, R x y → R y x := fun ⟨hx, hy, l, h1, h2⟩ => ⟨hy, hx, l, h2, h1⟩
  have stepB : ∀ (s : Fin (L a)) (t : Fin (L b)), R (wpq L hL (s, t)) (wpq L hL (s, finRotate _ t)) := by
    intro s t
    refine ⟨mem _, mem _, (a, wpt L hL s (finRotate _ t)), ?_, ?_⟩
    · unfold StrongCoupling.linkSupp rbd wpq
      simp [wshift_b]
    · unfold StrongCoupling.linkSupp rbd wpq
      simp
  have stepA : ∀ (s : Fin (L a)) (t : Fin (L b)), R (wpq L hL (s, t)) (wpq L hL (finRotate _ s, t)) := by
    intro s t
    refine ⟨mem _, mem _, (b, wpt L hL (finRotate _ s) t), ?_, ?_⟩
    · unfold StrongCoupling.linkSupp rbd wpq
      simp [wshift_a hab]
    · unfold StrongCoupling.linkSupp rbd wpq
      simp
  have colB : ∀ (s : Fin (L a)) (j : ℕ) (hj : j < L b),
      Relation.ReflTransGen R (wpq L hL (s, ⟨0, hL b⟩)) (wpq L hL (s, ⟨j, hj⟩)) := by
    intro s j
    induction j with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj
      have h1 : j + 1 < L b := hj
      refine (ih (by omega)).tail ?_
      have e : finRotate (L b) ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := Fin.ext (w_rot_val _ h1)
      have := stepB s ⟨j, by omega⟩
      rw [e] at this
      exact this
  have rowA : ∀ (t : Fin (L b)) (i : ℕ) (hi : i < L a),
      Relation.ReflTransGen R (wpq L hL (⟨0, hL a⟩, t)) (wpq L hL (⟨i, hi⟩, t)) := by
    intro t i
    induction i with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      refine (ih (by omega)).tail ?_
      have e : finRotate (L a) ⟨i, by omega⟩ = ⟨i + 1, hi⟩ := Fin.ext (w_rot_val _ hi)
      have := stepA ⟨i, by omega⟩ t
      rw [e] at this
      exact this
  have fromO : ∀ p : Fin (L a) × Fin (L b), Relation.ReflTransGen R (wpq L hL (⟨0, hL a⟩, ⟨0, hL b⟩)) (wpq L hL p) := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact (colB ⟨0, hL a⟩ j hj).trans (rowA ⟨j, hj⟩ i hi)
  intro x hx y hy
  unfold wX0 at hx hy
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨p', -, rfl⟩ := Finset.mem_image.1 hy
  have rev : Relation.ReflTransGen R (wpq L hL p) (wpq L hL (⟨0, hL a⟩, ⟨0, hL b⟩)) :=
    Relation.ReflTransGen.mono (fun u v huv => hsymm huv) (Relation.ReflTransGen.swap (fromO p))
  exact rev.trans (fromO p')

theorem wZg (hab : a ≠ b) (c : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    Zg (wF (L := L) (hL := hL) (a := a) (b := b) c) ζ
      = 1 + c * wPhi (L := L) (hL := hL) (a := a) (b := b) ζ := by
  classical
  have hact : ∀ γ, actF (wF (L := L) (hL := hL) (a := a) (b := b) c) ζ γ
      = if γ = wX0 (L := L) (hL := hL) (a := a) (b := b)
        then c * wPhi (L := L) (hL := hL) (a := a) (b := b) ζ else 0 := by
    intro γ
    unfold actF wF
    by_cases h2 : γ = wX0 (L := L) (hL := hL) (a := a) (b := b)
    · rw [if_pos h2, if_pos (by rw [h2]; exact wX0_conn hab)]
    · rw [if_neg h2]; simp
  unfold Zg MatchAt.Z
  have hX0 : wX0 (L := L) (hL := hL) (a := a) (b := b) ∈ (univ : Finset (RPlaq L)).powerset :=
    Finset.mem_powerset.2 (Finset.subset_univ _)
  have m0 : (∅ : Finset (Finset (RPlaq L))) ∈
      ((univ : Finset (RPlaq L)).powerset).powerset.filter (MatchAt.Compat (Inc (rbd L))) :=
    Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, fun x hx => absurd hx (Finset.notMem_empty _)⟩
  have m1 : ({wX0 (L := L) (hL := hL) (a := a) (b := b)} : Finset (Finset (RPlaq L))) ∈
      ((univ : Finset (RPlaq L)).powerset).powerset.filter (MatchAt.Compat (Inc (rbd L))) :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hX0),
      fun x hx y hy hxy => absurd ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm) hxy⟩
  rw [Finset.sum_eq_add_of_mem ∅ {wX0 (L := L) (hL := hL) (a := a) (b := b)} m0 m1
    (Finset.singleton_ne_empty _).symm]
  · rw [Finset.prod_empty, Finset.prod_singleton, hact, if_pos rfl]
  · rintro T - ⟨h0, h1⟩
    obtain ⟨γ, hγT, hγ⟩ : ∃ γ ∈ T, γ ≠ wX0 (L := L) (hL := hL) (a := a) (b := b) := by
      by_contra hn
      push Not at hn
      apply h1
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, hn⟩
      obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.2 h0
      rw [← hn γ hγ]; exact hγ
    exact Finset.prod_eq_zero hγT (by rw [hact, if_neg hγ])

include hL in
/-- **The one-polymer activity**: for every `c` with `|c| ≤ r^{L_a L_b}`, `c · Π_{q ∈ X₀} sg(ζ_q)` on the
plane slice `X₀` of `(a, b)` through the origin (and `0` on every other set) is an `EffGas` for
`(1 − c)/(1 + c)`. -/
def effGas_onePolymer (hab : a ≠ b) {r c : ℝ} (hr : 0 ≤ r) (hc : |c| ≤ r ^ (L a * L b)) :
    EffGas L a b ((1 - c) / (1 + c)) r where
  F := wF (L := L) (hL := hL) (a := a) (b := b) c
  centre := wF_centre hab c
  bound := fun ζ X => by
    classical
    unfold wF
    split_ifs with hX
    · rw [hX, wX0_card hab, abs_mul]
      calc |c| * |wPhi (L := L) (hL := hL) (a := a) (b := b) ζ| ≤ |c| * 1 :=
            mul_le_mul_of_nonneg_left (wPhi_abs_le ζ) (abs_nonneg c)
        _ ≤ r ^ (L a * L b) := by rw [mul_one]; exact hc
    · rw [abs_zero]; exact pow_nonneg hr _
  ratio := by
    rw [wZg hab, wZg hab, wPhi_sheet hab, wPhi_one]
    ring

include hL in
/-- **Any ratio `z ∈ (0, 1]` with `(1 − z)/(1 + z) ≤ r^{L_a L_b}` has an `EffGas` description.** -/
theorem effGas_of_elec (hab : a ≠ b) {r z : ℝ} (hr : 0 ≤ r) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (he : (1 - z) / (1 + z) ≤ r ^ (L a * L b)) : Nonempty (EffGas L a b z r) := by
  have hc0 : 0 ≤ (1 - z) / (1 + z) := div_nonneg (by linarith) (by linarith)
  have G := effGas_onePolymer (L := L) (hL := hL) hab hr (by rw [abs_of_nonneg hc0]; exact he)
  have hzz : (1 - (1 - z) / (1 + z)) / (1 + (1 - z) / (1 + z)) = z := by
    have h1z : (1 + z) ≠ 0 := (by linarith : (0 : ℝ) < 1 + z).ne'
    field_simp
    ring
  rw [hzz] at G
  exact ⟨G⟩

end Witness

/-- **`EffCondensationAt` follows from a decay bound on the electric ratio alone**: on the window,
`elecRatio ≤ r^{Lc m i i · Lc m i ν}` for some `m ≥ κ n a` gives it, with `F` the one-polymer activity
of `effGas_onePolymer`; no block-spin structure enters. -/
theorem effCondensationAt_of_elec {κ r ℓ : ℝ} (hr : 0 ≤ r)
    (h : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun 2 β → (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ 5 * ℓ →
      ∀ i : Fin 4, ∀ ν : {j : Fin 4 // j ≠ i}, ∃ m : ℕ, 1 ≤ m ∧
        κ * ((n : ℝ) * AsymptoticScaling.aRun 2 β) ≤ m ∧
        elecRatio β n i ν ≤ r ^ (Lc m i i * Lc m i ν.1)) :
    EffCondensationAt κ r ℓ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0 n hn h2 hlo hup i ν
  obtain ⟨m, hm1, hκm, hE⟩ := hβ n hn h2 hlo hup i ν
  have he := FluxCost.even_of_pow2 hn h2
  have hz1 := VortexCondense.zR_Lc_le_one hβ0 h2 he i ν
  have hz0 := zR_pos (Lc n i) i ν.1 β
  rw [elecRatio_eq hβ0 h2 he i ν] at hE
  have hpos : ∀ k, 0 < Lc m i k := fun k => lt_of_lt_of_le hm1 (VortexTorus.le_Lc m i k)
  exact ⟨m, hm1, hκm, effGas_of_elec (L := Lc m i) (hL := hpos) (Ne.symm ν.2) hr hz0 hz1 hE⟩

#print axioms vortexCostAt_of_large
#print axioms CentreLocal.card_ge_of_ne
#print axioms dob_actF
#print axioms log_Zg_sub_le
#print axioms effGas_wilson
#print axioms EffGas.one_sub_le
#print axioms one_sub_le_of_effGas_Lc
#print axioms vortexCostAt_of_eff
#print axioms flux_half_of_eff
#print axioms deficit_eq_two_oddTrace
#print axioms one_sub_zR_eq_oddFlux
#print axioms elecRatio_eq
#print axioms elecCostAt_of_vortexCostAt
#print axioms vortexCostAt_of_elecCostAt
#print axioms not_ratio_of_states
#print axioms hidden_twist_agrees
#print axioms hidden_twist_any_ratio
#print axioms zR_eq_read
#print axioms sheetObs_eq_filter
#print axioms effGas_onePolymer
#print axioms effGas_of_elec
#print axioms effCondensationAt_of_elec

end MassGap.VortexAperture
