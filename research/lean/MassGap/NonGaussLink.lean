import Mathlib
import MassGap.ObsLead
import MassGap.NonTrivialCanonical

/-!
# MassGap.NonGaussLink — the trace channel of `rhoD` is the observer's field, and `NonGaussianT` reduces to it

`ObsLead.clayStatementAt_SU_obs` takes `hNG : NonGaussianT hN (rhoD (fT N) z)`. This module proves that
the trace channel of `rhoD f z` reads only the observer's field `obs N`, with constant coefficient
`N/16` (`ClayData.coefC_mD`) and per-field factor `z_sc k` (`ClayData.ZD_obs`), and reduces `hNG` to a
statement about the connected three-point lattice readings of `obs N` alone.

## The reduction

* `latT_trace_rhoD`: at every step `k` and every family `u` of `n` test functions,
  `latT (rhoD f z) k ((trC, uᵢ))ᵢ = (N/16)ⁿ · obsRead z k u`, where
  `obsRead z k u = latSkR (connected (ZD z)) k ((obs N, uᵢ))ᵢ` is the connected reading of `n`
  insertions of `obs N`. No hypothesis: the sum over the basis collapses to the single basis element
  `none` because every channel field has trace coefficient `0`.
* `contTr_one_rhoD`: the one-point function of the trace is `0` exactly. Each connected smeared field
  has mean zero in `stateK hN k` (`ContinuumNontrivial.stateK_smear_connected`), so the lattice
  sequence is identically `0` and its limit along `ultra` is `0`.
* `cum3T_rhoD`: hence `cum3T (rhoD f z) a b c = limUnder ultra ((N/16)³ · obsRead z k ![a, b, c])`,
  with no hypothesis.
* `nonGaussianT_rhoD_of_obs`: `ObsThreePoint hN z` (a separated triple of continuous test functions
  whose `obsRead` is eventually in `[κ, C]` in absolute value, `κ > 0`) gives
  `NonGaussianT hN (rhoD f z)` for every `f`.

## The link to `ThreePointCanonical`

* `obsRead_eq`: `obsRead z k u = z_sc(k)ⁿ · latSkR (rho1 hN) k ((obs N, uᵢ))ᵢ`.
* `obsRead_eq_canonical`: at a positive reference reading `r_k = refReading hN (obs N) t ℓ k`, on a
  family `F` of three insertions of `obs N`, `obsRead = (z_sc(k) √r_k)³ · latSkR (connected zCan) k F`.
* `obsThreePoint_of_canonical`: `ThreePointCanonical hN (obs N) t ℓ F` on such a family with continuous
  test functions and `SepThree`, its bound `hB` (E on that family) and the normalisation match
  `r ≤ |z_sc k| √r_k ≤ R` eventually, `r > 0`, give `ObsThreePoint hN z`.

## The capstones

* `clayStatementAt_SU_ng`: `ObsLead.clayStatementAt_SU_obs` with `hNG` replaced by `ObsThreePoint`.
* `clayStatementAt_SU_canon`: the same with `ObsThreePoint` replaced by the inputs of
  `obsThreePoint_of_canonical`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `16` the trace coefficient of `coefC_mD`; `3` the number of insertions; `1` the
one-point order; `0` the excluded colour count, the reflection plane, the Gaussian value and the signs;
`2` the least colour count and the limits of the scalar and pseudoscalar factors.
-/

noncomputable section

namespace MassGap.NonGaussLink

open MassGap MassGap.ClayStatement MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayWiring MassGap.ClayData MassGap.ExistenceReduce MassGap.NonTrivialCanonical Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The trace channel of `rhoD` -/

/-- **The connected reading of `n` insertions of the observer's field** at the data's per-field factor
`ZD z`. DERIVED: no numeral. -/
def obsRead (hN : N ≠ 0) (z : Chan → ℕ → ℝ) (k : ℕ) {n : ℕ} (u : Fin n → TestFn) : ℝ :=
  latSkR hN (Renorm.connected hN (ZD z)) k (fun i => (obs N, u i))

/-- **The trace reading of `rhoD` is `(N/16)ⁿ` times the observer's reading**, at every step.

DERIVED: `16` from `coefC_mD`. -/
theorem latT_trace_rhoD (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (k : ℕ) {n : ℕ} (u : Fin n → TestFn) :
    latT hN (rhoD f z) k (fun i => (trC, u i)) = ((N : ℝ) / 16) ^ n * obsRead hN z k u := by
  unfold rhoD
  rw [latT_mixOfZ, Finset.sum_eq_single (fun _ => (none : BD))]
  · refine congrArg₂ (· * ·) ?_ rfl
    calc (∏ i : Fin n, coefC (mD N) ((fun i => (trC, u i)) i).1 ((fun _ => (none : BD)) i))
        = ∏ _i : Fin n, ((N : ℝ) / 16) := Finset.prod_congr rfl fun i _ => by
            show coefC (mD N) trC none = _
            rw [coefC_mD N hN, if_pos rfl]
      _ = ((N : ℝ) / 16) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ none := by
      by_contra h
      exact hb (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    have h0 : coefC (mD N) trC (b i) = 0 := by rw [coefC_mD N hN, if_neg hi]
    apply mul_eq_zero_of_left
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **A connected one-point reading is `0`**: the connected smeared field has mean zero in
`stateK hN k`. DERIVED: `1` the order; `0` the mean. -/
theorem latSkR_connected_one (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (k : ℕ)
    (G : Fin 1 → SField N) : latSkR hN (Renorm.connected hN Z) k G = 0 := by
  have h : latSk hN k (fun i => (Renorm.connected hN Z).field k (G i)) = 0 := by
    unfold latSk latS
    rw [Fin.prod_univ_one]
    exact ContinuumNontrivial.stateK_smear_connected hN k (G 0).1 (G 0).2
  unfold latSkR
  rw [h, mul_zero]

/-- **The one-point function of the trace of `rhoD` is `0`.** DERIVED: `1` the order. -/
theorem contTr_one_rhoD (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (a : TestFn) : contTr hN (rhoD f z) ![a] = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have e : (fun k => latT hN (rhoD f z) k (fun i => (trC, (![a] : Fin 1 → TestFn) i)))
      = fun _ => (0 : ℝ) :=
    funext fun k => by rw [latT_trace_rhoD, obsRead, latSkR_connected_one, mul_zero]
  show limUnder (ultra : Filter ℕ)
      (fun k => latT hN (rhoD f z) k (fun i => (trC, (![a] : Fin 1 → TestFn) i))) = 0
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

/-- **The connected three-point function of the trace of `rhoD`** is the `ultra` limit value of
`(N/16)³` times the observer's three-point reading. No hypothesis.

DERIVED: `3` the order; `16` from `coefC_mD`. -/
theorem cum3T_rhoD (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N)) (z : Chan → ℕ → ℝ)
    (a b c : TestFn) :
    cum3T hN (rhoD f z) a b c
      = limUnder (ultra : Filter ℕ) (fun k => ((N : ℝ) / 16) ^ 3 * obsRead hN z k ![a, b, c]) := by
  unfold cum3T
  rw [contTr_one_rhoD, contTr_one_rhoD, contTr_one_rhoD]
  simp only [mul_zero, sub_zero, add_zero]
  show limUnder (ultra : Filter ℕ)
      (fun k => latT hN (rhoD f z) k (fun i => (trC, (![a, b, c] : Fin 3 → TestFn) i))) = _
  exact congrArg (limUnder (ultra : Filter ℕ))
    (funext fun k => latT_trace_rhoD hN f z k ![a, b, c])

/-! ## 2. The reduced statement -/

/-- **The observer's separated three-point statement at the data's normalisation.** A triple of
continuous, pairwise `d`-separated test functions whose connected three-point reading of `obs N` at
the factor `ZD z` is eventually in `[κ, C]` in absolute value, `κ > 0`.

DERIVED: `0` the sign of `c` and of the separation; `3` the order. -/
def ObsThreePoint (hN : N ≠ 0) (z : Chan → ℕ → ℝ) : Prop :=
  ∃ a b c : TestFn, Continuous a.1 ∧ Continuous b.1 ∧ Continuous c.1
    ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d a b ∧ ContinuumSep.sepBy d a c
        ∧ ContinuumSep.sepBy d b c)
    ∧ ∃ κ C : ℝ, 0 < κ ∧ ∀ᶠ k in atTop,
        κ ≤ |obsRead hN z k ![a, b, c]| ∧ |obsRead hN z k ![a, b, c]| ≤ C

/-- **`NonGaussianT` at `rhoD` from the observer's three-point statement.** The reading sequence is
eventually bounded, so it converges along `ultra` (`exists_tendsto_ultra`); its limit is
`cum3T` (`cum3T_rhoD`) and is at least `(N/16)³ κ > 0` in absolute value.

DERIVED: `0` the excluded colour count and the Gaussian value; `3`, `16` as in `cum3T_rhoD`. -/
theorem nonGaussianT_rhoD_of_obs (hN : N ≠ 0) (f : Idx4 → LField (MassGap.SUN.SU N))
    (z : Chan → ℕ → ℝ) (h : ObsThreePoint hN z) : NonGaussianT hN (rhoD f z) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨a, b, c, ha, hb, hc, hsep, κ, C, hκ, hev⟩ := h
  refine ⟨a, b, c, ha, hb, hc, hsep, ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hq : 0 < ((N : ℝ) / 16) ^ 3 := pow_pos (div_pos hN0 (by norm_num)) 3
  obtain ⟨x, hx⟩ := exists_tendsto_ultra
    (fun k => ((N : ℝ) / 16) ^ 3 * obsRead hN z k ![a, b, c]) (((N : ℝ) / 16) ^ 3 * C)
    (hev.mono fun k hk => by
      show |((N : ℝ) / 16) ^ 3 * obsRead hN z k ![a, b, c]| ≤ ((N : ℝ) / 16) ^ 3 * C
      rw [abs_mul, abs_of_pos hq]
      exact mul_le_mul_of_nonneg_left hk.2 hq.le)
  rw [cum3T_rhoD, hx.limUnder_eq]
  have hle : ((N : ℝ) / 16) ^ 3 * κ ≤ |x| :=
    ge_of_tendsto hx.abs ((hev.filter_mono ultra_le).mono fun k hk => by
      show ((N : ℝ) / 16) ^ 3 * κ ≤ |((N : ℝ) / 16) ^ 3 * obsRead hN z k ![a, b, c]|
      rw [abs_mul, abs_of_pos hq]
      exact mul_le_mul_of_nonneg_left hk.1 hq.le)
  intro h0
  rw [h0, abs_zero] at hle
  linarith [mul_pos hq hκ]

/-! ## 3. The link to `ThreePointCanonical` -/

/-- **A connected reading is the product of the factors times the unit-strength reading.**
DERIVED: `1` the unit strength. -/
theorem latSkR_connected_eq (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (k : ℕ)
    {ι : Type} [Fintype ι] (G : ι → SField N) :
    latSkR hN (Renorm.connected hN Z) k G = (∏ i, Z k (G i).1) * latSkR hN (rho1 hN) k G := by
  show (∏ i, Z k (G i).1) * latSk hN k (fun i => (Renorm.connected hN Z).field k (G i))
    = (∏ i, Z k (G i).1) * ((∏ _i : ι, (1 : ℝ)) * latSk hN k (fun i => (rho1 hN).field k (G i)))
  rw [Finset.prod_const_one, one_mul]
  rfl

/-- **The observer's reading is `z_sc(k)ⁿ` times the unit-strength reading.** DERIVED: no numeral. -/
theorem obsRead_eq (hN : N ≠ 0) (z : Chan → ℕ → ℝ) (k : ℕ) {n : ℕ} (u : Fin n → TestFn) :
    obsRead hN z k u = z .sc k ^ n * latSkR hN (rho1 hN) k (fun i => (obs N, u i)) := by
  rw [obsRead, latSkR_connected_eq]
  congr 1
  calc (∏ i : Fin n, ZD z k ((fun i => (obs N, u i)) i).1) = ∏ _i : Fin n, z .sc k :=
        Finset.prod_congr rfl fun i _ => ZD_obs z k
    _ = z .sc k ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The observer's reading against the canonical reading.** On a family of three insertions of
`obs N`, at a positive reference reading `r_k`, `obsRead = (z_sc(k) √r_k)³ · latSkR (connected zCan)`.

DERIVED: `3` the order. -/
theorem obsRead_eq_canonical (hN : N ≠ 0) (z : Chan → ℕ → ℝ) (t ℓ : ℝ) (k : ℕ)
    (F : Fin 3 → SField N) (hO : ∀ i, (F i).1 = obs N)
    (hr : 0 < refReading hN (obs N) t ℓ k) :
    obsRead hN z k ![(F 0).2, (F 1).2, (F 2).2]
      = (z .sc k * Real.sqrt (refReading hN (obs N) t ℓ k)) ^ 3
        * latSkR hN (Renorm.connected hN (zCan hN (obs N) t ℓ)) k F := by
  have hF : (fun i => (obs N, (![(F 0).2, (F 1).2, (F 2).2] : Fin 3 → TestFn) i)) = F := by
    funext i
    fin_cases i <;> exact Prod.ext (hO _).symm rfl
  have hs : 0 < Real.sqrt (refReading hN (obs N) t ℓ k) := Real.sqrt_pos.mpr hr
  rw [obsRead_eq, hF, latSkR_zCan_eq, Fintype.card_fin]
  set s := Real.sqrt (refReading hN (obs N) t ℓ k)
  have e : (z .sc k * s) ^ 3 * ((1 / s) ^ 3 * latSkR hN (rho1 hN) k F)
      = z .sc k ^ 3 * latSkR hN (rho1 hN) k F * (s * (1 / s)) ^ 3 := by ring
  rw [e, mul_one_div_cancel hs.ne', one_pow, mul_one]

/-- **`ObsThreePoint` from the canonical three-point statement.** A family `F` of three insertions of
`obs N` with continuous test functions, `SepThree d F` and `ThreePointCanonical hN (obs N) t ℓ F`,
its eventual bound `hB` (E on that family), and the normalisation match `hR`
(`r ≤ |z_sc k| √r_k ≤ R` eventually, `r > 0`) give `ObsThreePoint hN z` at the triple `(F i).2`.

DERIVED: `0`, `1`, `2` the indices of the triple; `3` the order; `0` the signs. -/
theorem obsThreePoint_of_canonical (hN : N ≠ 0) (z : Chan → ℕ → ℝ) {t ℓ d : ℝ}
    (F : Fin 3 → SField N) (hO : ∀ i, (F i).1 = obs N) (hcont : ∀ i, Continuous (F i).2.1)
    (hs : SepThree d F) (h3 : ThreePointCanonical hN (obs N) t ℓ F)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkR hN (Renorm.connected hN (zCan hN (obs N) t ℓ)) k F| ≤ C)
    (hR : ∃ r R : ℝ, 0 < r ∧ ∀ᶠ k in atTop,
      r ≤ |z .sc k| * Real.sqrt (refReading hN (obs N) t ℓ k)
        ∧ |z .sc k| * Real.sqrt (refReading hN (obs N) t ℓ k) ≤ R) :
    ObsThreePoint hN z := by
  have hpos := refPos_of_threePointCanonical hN (obs N) t ℓ F h3
  obtain ⟨c, hc, hlow⟩ := h3
  obtain ⟨C, hC⟩ := hB
  obtain ⟨r, R, hr, hrR⟩ := hR
  refine ⟨(F 0).2, (F 1).2, (F 2).2, hcont 0, hcont 1, hcont 2,
    ⟨d, hs.1, hs.2 0 1 (by decide), hs.2 0 2 (by decide), hs.2 1 2 (by decide)⟩,
    r ^ 3 * c, R ^ 3 * C, mul_pos (pow_pos hr 3) hc, ?_⟩
  filter_upwards [hpos, hlow, hC, hrR] with k hk hkl hkC hkr
  have habs : |obsRead hN z k ![(F 0).2, (F 1).2, (F 2).2]|
      = (|z .sc k| * Real.sqrt (refReading hN (obs N) t ℓ k)) ^ 3
        * |latSkR hN (Renorm.connected hN (zCan hN (obs N) t ℓ)) k F| := by
    rw [obsRead_eq_canonical hN z t ℓ k F hO hk, abs_mul, abs_pow, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hw0 : 0 ≤ |z .sc k| * Real.sqrt (refReading hN (obs N) t ℓ k) :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [habs]
  refine ⟨mul_le_mul (pow_le_pow_left₀ hr.le hkr.1 3) hkl hc.le (pow_nonneg hw0 3),
    mul_le_mul (pow_le_pow_left₀ hw0 hkr.2 3) hkC (abs_nonneg _)
      (pow_nonneg (hw0.trans hkr.2) 3)⟩

/-! ## 4. The capstones -/

section Capstone

open MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.InfiniteLattice MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead

/-- **`ObsLead.clayStatementAt_SU_obs` with `hNG` replaced by `ObsThreePoint`**
(`nonGaussianT_rhoD_of_obs`). The other inputs are those of `clayStatementAt_SU_obs`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_ng (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (wC : TSepG (build (rhoD (fT N) z) (bareD (fT N) (bT N))).Ix 0 →
      preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys)
      (build (rhoD (fT N) z) (bareD (fT N) (bT N))) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P)
            (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_obs hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF
    (nonGaussianT_rhoD_of_obs (ne_zero_of_two_le hN2) (fT N) z hObs) hWard hCO wC hLC hX

/-- **`clayStatementAt_SU_ng` with `ObsThreePoint` replaced by the canonical three-point inputs**
(`obsThreePoint_of_canonical`): a family `F` of three insertions of `obs N` with continuous test
functions, `SepThree`, `ThreePointCanonical`, its bound `hB`, and the normalisation match `hR`.

DERIVED: `2`, `0`, `4` as in `clayStatementAt_SU_ng`; `3` the order. -/
theorem clayStatementAt_SU_canon (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fT N) z) G)
    (hAF : AFCoefficient N G)
    {tr ℓ d : ℝ} (F : Fin 3 → SField N) (hO : ∀ i, (F i).1 = obs N)
    (hcont : ∀ i, Continuous (F i).2.1) (hs : SepThree d F)
    (h3 : ThreePointCanonical (ne_zero_of_two_le hN2) (obs N) tr ℓ F)
    (hB : ∃ C : ℝ, ∀ᶠ k in atTop,
      |latSkR (ne_zero_of_two_le hN2)
        (Renorm.connected (ne_zero_of_two_le hN2) (zCan (ne_zero_of_two_le hN2) (obs N) tr ℓ)) k F|
          ≤ C)
    (hR : ∃ r R : ℝ, 0 < r ∧ ∀ᶠ k in atTop,
      r ≤ |z .sc k| * Real.sqrt (refReading (ne_zero_of_two_le hN2) (obs N) tr ℓ k)
        ∧ |z .sc k| * Real.sqrt (refReading (ne_zero_of_two_le hN2) (obs N) tr ℓ k) ≤ R)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fT N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (build (rhoD (fT N) z) (bareD (fT N) (bT N))))
    (wC : TSepG (build (rhoD (fT N) z) (bareD (fT N) (bT N))).Ix 0 →
      preH (ne_zero_of_two_le hN2) W hU hphys)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0
      (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys)
      (build (rhoD (fT N) z) (bareD (fT N) (bT N))) wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
            (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC eI wC P)
            (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) (rhoD (fT N) z)
              (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_ng hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF
    (obsThreePoint_of_canonical (ne_zero_of_two_le hN2) z F hO hcont hs h3 hB hR)
    hWard hCO wC hLC hX

end Capstone

end MassGap.NonGaussLink

end

#print axioms MassGap.NonGaussLink.latT_trace_rhoD
#print axioms MassGap.NonGaussLink.latSkR_connected_one
#print axioms MassGap.NonGaussLink.contTr_one_rhoD
#print axioms MassGap.NonGaussLink.cum3T_rhoD
#print axioms MassGap.NonGaussLink.nonGaussianT_rhoD_of_obs
#print axioms MassGap.NonGaussLink.latSkR_connected_eq
#print axioms MassGap.NonGaussLink.obsRead_eq
#print axioms MassGap.NonGaussLink.obsRead_eq_canonical
#print axioms MassGap.NonGaussLink.obsThreePoint_of_canonical
#print axioms MassGap.NonGaussLink.clayStatementAt_SU_ng
#print axioms MassGap.NonGaussLink.clayStatementAt_SU_canon
