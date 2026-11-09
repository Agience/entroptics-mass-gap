import Mathlib
import MassGap.ReflPosG
import MassGap.PeriodicDyadic
import MassGap.PeriodicReduce
import MassGap.ChessboardRead

/-!
# MassGap.PeriodicReduceG — the periodic connected pairing of `G`, its limit, and the gap from one even lag

`PeriodicReduce`, `PeriodicDyadic` and the periodic part of `ChessboardRead` with `SUN.SU N` replaced by
a `GaugeGroup G` and `PeriodicState.periodicState` by `GaugeWilson.periodicStateG G`.

* `periodicUltraG G β`: the ultrafilter `periodicStateG G β` is the limit along;
  `periodicUltraG_seed_mem`: the doubling family of a power-of-two seed is one of its sets.
* `torusConnG G τ p β j x c`: the connected reflected-shifted pairing of `x` at lag `c` in
  `torusStateG G (2j + 1) β`; `tendsto_torusConnG`: it converges to the pairing in `periodicStateG G β`.
* `periodicGaugeInvDataG G τ p β`: the gauge-invariant transfer data at `periodicStateG G β`, built by
  `GaugeInvariantAlgebra.gaugeInvTransferData` from `ReflInvG.periodicStateG_reflInvariant`,
  `ReflPosG.periodicStateG_reflPositive` and `ShiftInvG.periodicStateG_shift`.
* `gapAt_of_even_lag`: on any `Transfer.TransferData`, a single bound at an even lag `2h ≠ 0`,
  `D.form x (T^{2h} x) ≤ r^{2h} D.form x x` for every `x` orthogonal to the vacuum, gives
  `TransferGap.GapAt D r`. The proof reads only the even part of the lag profile,
  `n ↦ D.form (Tⁿ x) (Tⁿ x)`, which is log-convex by Cauchy–Schwarz for the reflection form; it does not
  use `GNSHilbert.PositiveTransfer`.
* `TorusLagClearG`, `gapAt_of_torusLagClearG`: the single-lag inequality on the periodic lattices of
  `G` at an even lag gives `GapAt` at the periodic data.

DERIVED (module-wide): `4` the dimension; `2` in `2 * p` the plane-to-constant doubling and in
`2 * j + 1` the even-extent family; `2` in `2 * h` the even lag; `0` the vacuum pairing, the sign of
the slack and the contact lag.
-/

namespace MassGap.PeriodicReduceG

open MassGap MassGap.GNSHilbert MassGap.PeriodicState Filter

/-! ## 1. The gap from one even lag, on any transfer data -/

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **The gap from one even lag.** No positivity of `T` is used. -/
theorem gapAt_of_even_lag (D : Transfer.TransferData A) {h : ℕ} (hh : h ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hlag : ∀ x : A, D.form x D.vac = 0 →
      D.form x ((D.T ^ (2 * h)) x) ≤ r ^ (2 * h) * D.form x x) :
    TransferGap.GapAt D r := by
  intro x hx
  set c : ℕ → ℝ := fun n => D.form ((D.T ^ n) x) ((D.T ^ n) x) with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => D.form_nonneg _
  have hlc : ∀ n, c (n + 1) ^ 2 ≤ c n * c (n + 2) := by
    intro n
    have e : c (n + 1) = D.form ((D.T ^ n) x) ((D.T ^ (n + 2)) x) := by
      have h1 := ChessboardRead.lagProfile_even D x (n + 1)
      have h2 := ChessboardRead.lagProfile_add D x n (n + 2)
      have e2 : 2 * (n + 1) = n + (n + 2) := by ring
      rw [e2] at h1
      exact h1.symm.trans h2
    rw [e]
    exact D.toReflForm.cauchy_schwarz _ _
  have hch : c h ≤ (r ^ 2) ^ h * c 0 := by
    have e1 : c h = D.form x ((D.T ^ (2 * h)) x) := (ChessboardRead.lagProfile_even D x h).symm
    have e0 : c 0 = D.form x x := by simp [hc]
    rw [e1, e0, ← pow_mul]
    exact hlag x hx
  have key := ChessboardRead.le_mul_of_log_convex_lag hc0 hlc hh (sq_nonneg r) hch
  simpa [hc] using key

end Abstract

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## 2. The ultrafilter of `periodicStateG` -/

section Ultra

/-- The ultrafilter of `GaugeWilson.exists_periodic_limit_dvdG`. -/
noncomputable def periodicUltraG (β : ℝ) : Ultrafilter ℕ :=
  (GaugeWilson.exists_periodic_limit_dvdG G β).choose

theorem periodicUltraG_le_atTop (β : ℝ) :
    ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
  ReflPosG.periodicUltraG_le G β

theorem periodicUltraG_le_dyadic (β : ℝ) :
    ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ) ≤ dyadicFilter :=
  (GaugeWilson.exists_periodic_limit_dvdG G β).choose_spec.choose_spec.1

/-- **The doubling family of a power-of-two seed lies in `periodicUltraG`.** -/
theorem periodicUltraG_seed_mem (β : ℝ) (a : ℕ) :
    {j | ∃ k : ℕ, 2 * j + 2 = 2 ^ k * 2 ^ (a + 1)}
      ∈ ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ) :=
  periodicUltraG_le_dyadic G β (PeriodicDyadic.dyadic_seed_mem a)

theorem tendsto_periodicStateG' (β : ℝ) (f : C(GibbsSpec.IConf G, ℝ)) :
    Tendsto (fun k : ℕ => GaugeWilson.torusStateG G (2 * k + 1) β f)
      ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ)
      (nhds (GaugeWilson.periodicStateG G β f)) :=
  ShiftInvG.tendsto_periodicStateG G β f

end Ultra

/-! ## 3. The periodic connected pairing -/

section Torus

/-- The connected reflected-shifted pairing of `x` at lag `c` in `torusStateG G (2j + 1) β`. -/
noncomputable def torusConnG (τ : Fin 4) (p : ℤ) (β : ℝ) (j : ℕ)
    (x : C(GibbsSpec.IConf G, ℝ)) (c : ℕ) : ℝ :=
  GaugeWilson.torusStateG G (2 * j + 1) β
      (LatticeReflection.ireflObs τ (2 * p) x * (⇑(ReflectionShift.ishiftObsL τ))^[c] x)
    - GaugeWilson.torusStateG G (2 * j + 1) β (LatticeReflection.ireflObs τ (2 * p) x)
      * GaugeWilson.torusStateG G (2 * j + 1) β ((⇑(ReflectionShift.ishiftObsL τ))^[c] x)

theorem tendsto_torusConnG (τ : Fin 4) (p : ℤ) (β : ℝ) (x : C(GibbsSpec.IConf G, ℝ)) (c : ℕ) :
    Tendsto (fun j => torusConnG G τ p β j x c)
      ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ)
      (nhds (GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x
              * (⇑(ReflectionShift.ishiftObsL τ))^[c] x)
        - GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x)
          * GaugeWilson.periodicStateG G β ((⇑(ReflectionShift.ishiftObsL τ))^[c] x))) :=
  (tendsto_periodicStateG' G β _).sub
    ((tendsto_periodicStateG' G β _).mul (tendsto_periodicStateG' G β _))

end Torus

/-! ## 4. The transfer data at `periodicStateG` -/

section Form

/-- **The gauge-invariant transfer data at `periodicStateG G β`.** -/
noncomputable def periodicGaugeInvDataG (τ : Fin 4) (p : ℤ) (β : ℝ) :
    Transfer.TransferData ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p) :=
  GaugeInvariantAlgebra.gaugeInvTransferData τ p (GaugeWilson.periodicStateG G β)
    (ReflInvG.periodicStateG_reflInvariant G β τ (2 * p))
    (ReflPosG.periodicStateG_reflPositive G β τ p)
    (ShiftInvG.periodicStateG_shift G β τ)

theorem periodic_form_diagG (τ : Fin 4) (p : ℤ) (β : ℝ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p)) :
    (periodicGaugeInvDataG G τ p β).form x x
      = GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p)
          (x : C(GibbsSpec.IConf G, ℝ)) * (x : C(GibbsSpec.IConf G, ℝ))) := rfl

theorem periodic_form_vacG (τ : Fin 4) (p : ℤ) (β : ℝ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p)) :
    (periodicGaugeInvDataG G τ p β).form x (periodicGaugeInvDataG G τ p β).vac
      = GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p)
          (x : C(GibbsSpec.IConf G, ℝ))) := by
  have h : (periodicGaugeInvDataG G τ p β).form x (periodicGaugeInvDataG G τ p β).vac
      = GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p)
          (x : C(GibbsSpec.IConf G, ℝ)) * (1 : C(GibbsSpec.IConf G, ℝ))) := rfl
  rw [h, mul_one]

theorem periodic_form_powG (τ : Fin 4) (p : ℤ) (β : ℝ)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p)) (c : ℕ) :
    (periodicGaugeInvDataG G τ p β).form x (((periodicGaugeInvDataG G τ p β).T ^ c) x)
      = GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p)
            (x : C(GibbsSpec.IConf G, ℝ))
          * (⇑(ReflectionShift.ishiftObsL τ))^[c] (x : C(GibbsSpec.IConf G, ℝ))) :=
  GaugeInvariantAlgebra.gaugeInv_form_pow τ p (GaugeWilson.periodicStateG G β)
    (ReflInvG.periodicStateG_reflInvariant G β τ (2 * p))
    (ReflPosG.periodicStateG_reflPositive G β τ p)
    (ShiftInvG.periodicStateG_shift G β τ) x c

end Form

/-! ## 5. The single-lag input on the periodic lattices of `G` -/

section Lag

/-- **The single-lag input, on the periodic lattices of `G`.** At coupling `β`, lag `m` and rate
`r`: for every gauge-invariant half-space observable `x` and slack `ε > 0`, eventually along
`periodicUltraG G β`, `torusConnG … x m ≤ rᵐ · torusConnG … x 0 + ε`. -/
def TorusLagClearG (τ : Fin 4) (p : ℤ) (β : ℝ) (m : ℕ) (r : ℝ) : Prop :=
  ∀ x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ j in ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ),
      torusConnG G τ p β j x m ≤ r ^ m * torusConnG G τ p β j x 0 + ε

variable {G}

/-- The single-lag input at `periodicStateG`: both connected pairings converge
(`tendsto_torusConnG`) and `ChessboardRead.le_of_slack` closes it. -/
theorem periodic_conn_le_of_torusLagClearG (τ : Fin 4) (p : ℤ) (β : ℝ) (m : ℕ) (r : ℝ)
    (h : TorusLagClearG G τ p β m r) (x : C(GibbsSpec.IConf G, ℝ))
    (hx : x ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p) :
    GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x
          * (⇑(ReflectionShift.ishiftObsL τ))^[m] x)
        - GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x)
          * GaugeWilson.periodicStateG G β ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)
      ≤ r ^ m * (GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x * x)
          - GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p) x)
            * GaugeWilson.periodicStateG G β x) := by
  haveI : ((periodicUltraG G β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltraG G β).neBot'
  exact ChessboardRead.le_of_slack (tendsto_torusConnG G τ p β x m)
    ((tendsto_torusConnG G τ p β x 0).const_mul (r ^ m)) (h x hx)

/-- The single-lag input on the transfer form at `periodicGaugeInvDataG`. -/
theorem periodic_form_lag_of_torusLagClearG (τ : Fin 4) (p : ℤ) (β : ℝ) (m : ℕ) (r : ℝ)
    (h : TorusLagClearG G τ p β m r)
    (x : ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p))
    (hx : (periodicGaugeInvDataG G τ p β).form x (periodicGaugeInvDataG G τ p β).vac = 0) :
    (periodicGaugeInvDataG G τ p β).form x (((periodicGaugeInvDataG G τ p β).T ^ m) x)
      ≤ r ^ m * (periodicGaugeInvDataG G τ p β).form x x := by
  have hθ : GaugeWilson.periodicStateG G β (LatticeReflection.ireflObs τ (2 * p)
      (x : C(GibbsSpec.IConf G, ℝ))) = 0 :=
    (periodic_form_vacG G τ p β x).symm.trans hx
  have hc := periodic_conn_le_of_torusLagClearG τ p β m r h (x : C(GibbsSpec.IConf G, ℝ)) x.2
  simp only [hθ, zero_mul, sub_zero] at hc
  rw [periodic_form_powG G τ p β x m, periodic_form_diagG G τ p β x]
  exact hc

/-- **The gap from one even lag on the periodic lattices of `G`.** At an even lag `2h ≠ 0` and
`0 ≤ r`, `TorusLagClearG` gives `TransferGap.GapAt (periodicGaugeInvDataG G τ p β) r`. -/
theorem gapAt_of_torusLagClearG (τ : Fin 4) (p : ℤ) (β : ℝ) {h : ℕ} (hh : h ≠ 0) {r : ℝ}
    (hr : 0 ≤ r) (hl : TorusLagClearG G τ p β (2 * h) r) :
    TransferGap.GapAt (periodicGaugeInvDataG G τ p β) r :=
  gapAt_of_even_lag _ hh hr
    (fun x hx => periodic_form_lag_of_torusLagClearG τ p β (2 * h) r hl x hx)

end Lag

end MassGap.PeriodicReduceG

#print axioms MassGap.PeriodicReduceG.gapAt_of_even_lag
#print axioms MassGap.PeriodicReduceG.periodicUltraG_seed_mem
#print axioms MassGap.PeriodicReduceG.tendsto_torusConnG
#print axioms MassGap.PeriodicReduceG.gapAt_of_torusLagClearG
