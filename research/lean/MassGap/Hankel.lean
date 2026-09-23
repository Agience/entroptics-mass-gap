import Mathlib
import MassGap.LogConvex

/-!
# MassGap.Hankel — positive semidefiniteness of the Wilson reflection Gram matrix

Three statements of the shape

    0 ≤ ∑ᵢ ∑ⱼ cᵢ cⱼ ρ(eᵢ + eⱼ)

for a real coefficient family `c` and lags `e` taken strictly below half the extent, plus the
arithmetic lemma that fixes the lag range. The entry depends on the two indices only through their
sum, so the matrix is Hankel as well as Gram.

`corrHyper_hankel_psd` is the general case: `ρ = corrHyper N n μ ν τ β` at any `N ≠ 0`, any pair of
plaquette directions `μ`, `ν` distinct from the reflection axis `τ`, any real coupling `β`, and any
even extent `n = 2 * m` with `0 < m`. The proof takes the centred half-space plaquette observables
`obsPlus` at levels `e i`, places them in `LogConvex.localObs` by `LogConvex.obsPlus_mem`, applies
the `form_nonneg` field of `LogConvex.wilsonReflForm` to `∑ i, c i • v i`, expands by bilinearity of
`Transfer.ReflForm.bil`, and uses `LogConvex.EW_centred_refl_eq_corrHyper` to rewrite the `(i, j)`
entry as `corrHyper ... (e i + e j) * Z`. The partition function `Z` is the same factor in every
entry and is strictly positive (`wilsonSystem_partition_pos`), so it cancels from the whole double
sum at once.

`corrClay_hankel_psd` instantiates that at `N := 3`, `d := 4`, `τ := (2 : Fin 4)`, `μ := 0`,
`ν := 1`, which is the definition of `WilsonBridge.corrClay`.
`corrClay_hankel_psd_at_extent_four` evaluates the general statement at `n = 4`, `m = 2`, two levels
`0` and `1` and coefficients `(t, 1)`, producing an explicit inequality among `corrClay 4 β 0`,
`corrClay 4 β 1` and `corrClay 4 β 2`.

`hankel_lag_val` records the lag range: for `n = 2 * m` and `P.val, Q.val < m`, the `Fin n` sum
`P + Q` has value `P.val + Q.val` — no wrap-around — and `P.val + Q.val + 2 ≤ n`.

Scope: the extent must be even and positive, and the lags reached by these statements are `0` to
`n - 2`; lag `n - 1` is outside the range at every extent, because both levels sit strictly below
the reflection plane. The coupling `β` is an arbitrary real — no sign hypothesis. What is stated is
positive semidefiniteness of the matrix; no representation of `ρ` as a finite sum of exponentials,
and no bound on the number of modes, is stated or implied. Axiom footprint is recorded by the
`#print axioms` line after each declaration.
-/

namespace MassGap.Hankel

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity MassGap.WilsonLattice
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonAction
open MassGap.ActionSplit MassGap.ReflectPositive MassGap.WilsonBridge
open MassGap.LogConvex

/-! ## Part 1 — the lag range reached by two levels below the reflection plane -/

section Range

/-- For `n = 2 * m` and `P Q : Fin n` with `P.val < m` and `Q.val < m`, the `Fin n` sum satisfies
`((P + Q : Fin n) : ℕ) = P.val + Q.val`, and `P.val + Q.val + 2 ≤ n`.

The first conjunct says the addition does not wrap, so the entry lag is the arithmetic sum of the
two levels rather than a residue; `Fin.val_add` plus `Nat.mod_eq_of_lt` gives it. The second bounds
the reachable lags by `n - 2`, from `P.val ≤ m - 1` and `Q.val ≤ m - 1`; `omega` closes it.

Scope: `[NeZero n]` is required for `Fin n` arithmetic. The bound is sharp in the sense that lag
`n - 1` is never reached from two levels strictly below `m`.

DERIVED: `2` occurs twice — as the factor in the evenness hypothesis `n = 2 * m`, and as the offset
in `P.val + Q.val + 2 ≤ n`, which is `2 * m - 2` rewritten. `m` is a bound variable, half the
extent, carried in from the geometry of `LogConvex.obsPlus_mem`. -/
theorem hankel_lag_val {n m : ℕ} [NeZero n] (hm : n = 2 * m) {P Q : Fin n}
    (hP : P.val < m) (hQ : Q.val < m) :
    ((P + Q : Fin n) : ℕ) = P.val + Q.val ∧ P.val + Q.val + 2 ≤ n := by
  refine ⟨?_, by omega⟩
  rw [Fin.val_add]
  exact Nat.mod_eq_of_lt (by omega)

#print axioms hankel_lag_val

end Range

/-! ## Part 2 — positive semidefiniteness of the `corrHyper` Hankel form -/

section Psd

variable {d n N : ℕ} [NeZero n]

/-- Positive semidefiniteness of the Hankel matrix of `corrHyper`:
`0 ≤ ∑ i, ∑ j, c i * c j * corrHyper N n μ ν τ β (e i + e j)` for any finite index type `ι`, any
coefficients `c : ι → ℝ` and any levels `e : ι → Fin n` with `(e i).val < m`.

Hypotheses: `N ≠ 0`; a reflection axis `τ : Fin d` and plaquette directions `μ ν : Fin d` both
distinct from `τ`; an even extent `n = 2 * m` with `0 < m`; and a real coupling `β`.

The proof builds `v i` from `obsPlus τ 0 m ((μ, ν), siteAtHyper τ (e i)) aC β`, centred at the
one-point function `aC`, and `LogConvex.obsPlus_mem` places each in
`localObs (blkS τ 0 m) (blkR τ 0 m)`. Applying `form_nonneg` of `LogConvex.wilsonReflForm` to
`∑ i, c i • v i` and expanding through `Transfer.ReflForm.bil` gives the double sum;
`LogConvex.EW_centred_refl_eq_corrHyper` rewrites each entry as
`corrHyper N n μ ν τ β (e i + e j) * Z`, with the partition function `Z` common to every entry and
strictly positive, so `le_of_mul_le_mul_right` removes it.

Scope: the reflection plane is fixed at `0` inside the proof; the statement quantifies over levels
below `m` only, so lags above `n - 2` are not covered (see `hankel_lag_val`). `β` is an arbitrary
real — no sign hypothesis is used, since the argument is a square against a strictly positive
Boltzmann weight.

DERIVED: `0` occurs three times — in `N ≠ 0`, in `0 < m`, and as the lower bound of the double sum.
`2` is the factor in the evenness hypothesis `n = 2 * m`. `m`, `τ`, `μ`, `ν`, `β`, `e` and `c` are
bound variables supplied by the caller. -/
theorem corrHyper_hankel_psd (hN : N ≠ 0) (τ : Fin d) (m : ℕ)
    (hm : n = 2 * m) (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {ι : Type} [Fintype ι] (e : ι → Fin n) (he : ∀ i, (e i).val < m) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * corrHyper (d := d) N n μ ν τ β (e i + e j) := by
  classical
  -- the centring constant: the one-point function, which is the same at every lag
  set aC : ℝ := EW N β (plaqE N (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n)) with haC
  -- the plaquette at level `R`, and its membership in the observable module
  have hlv : ∀ R : Fin n, lv (0 : Fin n) R = R.val := by
    intro R; show (R - 0).val = R.val; rw [sub_zero]
  have hdeg : ∀ R : Fin n, ¬ ((((μ, ν), siteAtHyper τ R) : Plaq d n).1.1 = τ
      ∧ (((μ, ν), siteAtHyper τ R) : Plaq d n).1.2 = τ) := fun R h => hμ h.1
  have hmem : ∀ i : ι,
      obsPlus (N := N) τ (0 : Fin n) m (((μ, ν), siteAtHyper τ (e i)) : Plaq d n) aC β
        ∈ localObs (blkS τ (0 : Fin n) m) (blkR τ (0 : Fin n) m) := by
    intro i
    refine obsPlus_mem hN τ (0 : Fin n) m hm hm0 _ (hdeg (e i)) ?_ aC β
    show lv (0 : Fin n) (siteAtHyper (d := d) (n := n) τ (e i) τ) < m
    rw [siteAtHyper_axis, hlv]
    exact he i
  set Pf := wilsonReflForm (N := N) hN τ (0 : Fin n) m hm hm0 β with hPf
  set v : ι → ↥(localObs (Ω := MassGap.SUN.SU N) (blkS τ (0 : Fin n) m) (blkR τ (0 : Fin n) m)) :=
    fun i => ⟨obsPlus τ (0 : Fin n) m (((μ, ν), siteAtHyper τ (e i)) : Plaq d n) aC β, hmem i⟩
    with hv
  -- the partition function, the same in every entry
  set Z := (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β with hZdef
  have hZ : 0 < Z := wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  have hnum : ∀ O : (Link d n → MassGap.SUN.SU N) → ℝ,
      (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O = EW N β O * Z := by
    intro O
    show _ = ((sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O / Z) * Z
    field_simp
  -- THE ENTRY: the pairing of two plaquette observables is the correlation at the SUM of the levels
  have hshift : ∀ R S : Fin n, R - ((0 : Fin n) + (0 : Fin n)) + S = R + S := by
    intro R S; rw [add_zero, sub_zero]
  have hentry : ∀ i j : ι,
      Pf.form (v i) (v j) = corrHyper (d := d) N n μ ν τ β (e i + e j) * Z := by
    intro i j
    have hpq : Pf.form (v i) (v j)
        = EW N β (fun U =>
            (plaqE N (((μ, ν), siteAtHyper τ (e i)) : Plaq d n) U - aC)
              * (plaqE N (((μ, ν), siteAtHyper τ (e j)) : Plaq d n)
                  (reflConf τ ((0 : Fin n) + (0 : Fin n)) U) - aC)) * Z := by
      show pairing τ (0 : Fin n) m β
          (obsPlus τ (0 : Fin n) m (((μ, ν), siteAtHyper τ (e i)) : Plaq d n) aC β)
          (obsPlus τ (0 : Fin n) m (((μ, ν), siteAtHyper τ (e j)) : Plaq d n) aC β) = _
      rw [pairing_obsPlus hN τ (0 : Fin n) m hm hm0 _ _ aC β]
      exact hnum _
    rw [hpq, haC, EW_centred_refl_eq_corrHyper hN hμ hν β ((0 : Fin n) + (0 : Fin n)) (e i) (e j),
      hshift]
  -- THE EXPANSION: bilinearity of the reflection form over a finite linear combination
  have hexp : Pf.form (∑ i, c i • v i) (∑ i, c i • v i)
      = ∑ i, ∑ j, c i * c j * Pf.form (v i) (v j) := by
    have h1 : Pf.bil (∑ i, c i • v i) = ∑ i, c i • Pf.bil (v i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
    calc Pf.form (∑ i, c i • v i) (∑ i, c i • v i)
        = Pf.bil (∑ i, c i • v i) (∑ j, c j • v j) := rfl
      _ = (∑ i, c i • Pf.bil (v i)) (∑ j, c j • v j) := by rw [h1]
      _ = ∑ i, c i * Pf.bil (v i) (∑ j, c j • v j) := by
            rw [LinearMap.sum_apply]
            exact Finset.sum_congr rfl
              (fun i _ => by rw [LinearMap.smul_apply, smul_eq_mul])
      _ = ∑ i, ∑ j, c i * c j * Pf.form (v i) (v j) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have hrow : Pf.bil (v i) (∑ j, c j • v j) = ∑ j, c j * Pf.form (v i) (v j) := by
              rw [map_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [map_smul]
              show c j • Pf.form (v i) (v j) = _
              rw [smul_eq_mul]
            rw [hrow]
            simp only [Finset.mul_sum, mul_assoc]
  -- POSITIVITY, and the partition function divides out of the whole double sum at once
  have hnn := Pf.form_nonneg (∑ i, c i • v i)
  rw [hexp] at hnn
  have hZfac : ∑ i, ∑ j, c i * c j * Pf.form (v i) (v j)
      = (∑ i, ∑ j, c i * c j * corrHyper (d := d) N n μ ν τ β (e i + e j)) * Z := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by rw [hentry i j]; ring)
  rw [hZfac] at hnn
  exact le_of_mul_le_mul_right (by rw [zero_mul]; exact hnn) hZ

#print axioms corrHyper_hankel_psd

end Psd

/-! ## Part 3 — the `corrClay` instance, and an explicit two-level case -/

section Clay

/-- `corrHyper_hankel_psd` instantiated at the parameters that define
`MassGap.WilsonBridge.corrClay`: `0 ≤ ∑ i, ∑ j, c i * c j * corrClay n β (e i + e j)` for an even
extent `n = 2 * m` with `0 < m`, any real coupling `β`, any finite `ι`, any levels `e` with
`(e i).val < m`, and any coefficients `c`.

The proof unfolds `corrClay` and supplies `N := 3`, `d := 4`, reflection axis `(2 : Fin 4)` and
directions `0` and `1`, discharging the two distinctness side conditions by `decide`. Since
`MassGap.wilsonCorrAt N β` is `corrClay (N + 1) β` by definition, the same inequality reads off for
the aperture-carrying correlation.

Scope: the level range `(e i).val < m` is inherited, so lags above `n - 2` are not covered; `β` is
unconstrained in sign.

DERIVED: `2` is the factor in the evenness hypothesis `n = 2 * m`; `0` occurs twice, in `0 < m` and
as the lower bound of the double sum. The `3`, `4`, `2`, `0` and `1` fixing the gauge group, the
dimension, the reflection axis and the two plaquette directions appear in the proof term, not in the
statement — in the statement they are already absorbed into `corrClay`. -/
theorem corrClay_hankel_psd (n : ℕ) [NeZero n] (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {ι : Type} [Fintype ι] (e : ι → Fin n) (he : ∀ i, (e i).val < m) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * MassGap.WilsonBridge.corrClay n β (e i + e j) := by
  simp only [MassGap.WilsonBridge.corrClay]
  exact corrHyper_hankel_psd (N := 3) (d := 4) (by norm_num) (2 : Fin 4) m hm hm0
    (by decide) (by decide) β e he c

#print axioms corrClay_hankel_psd

/-- `corrClay_hankel_psd` evaluated at extent four. For any reals `β` and `t`,
`0 ≤ t * t * corrClay 4 β 0 + 2 * t * corrClay 4 β 1 + corrClay 4 β 2`.

The proof instantiates the general statement at `n = 4`, `m = 2`, index type `Fin 2`, levels
`fun i => if i = 0 then 0 else 1` and coefficients `fun i => if i = 0 then t else 1`, expands the
double sum with `Fin.sum_univ_two`, and rewrites `(1 + 1 : Fin 4) = 2` to name the off-diagonal
lag.

This is the `2 × 2` Hankel minor `[[ρ 0, ρ 1], [ρ 1, ρ 2]]` written out, so the statement is a
one-parameter family of constraints on three distinct lags rather than a quantification over a
possibly empty index range.

Scope: extent four is the smallest even extent with `0 < m`; at `m = 2` the only levels strictly
below the plane are `0` and `1`, so no larger minor is available at this extent. `β` and `t` are
unconstrained reals.

DERIVED: `0` occurs twice, as the lower bound of the inequality and as the lag of the first term;
`4` occurs three times, once as the extent argument of each `corrClay`; `2` occurs twice, as the
coefficient of the cross term (the two equal off-diagonal entries) and as the lag of the third
term; `1` occurs once, as the lag of the cross term. The second coefficient is fixed at `1` in the
proof, which is why `t` appears squared in the first term and linearly in the second. -/
theorem corrClay_hankel_psd_at_extent_four (β t : ℝ) :
    0 ≤ t * t * MassGap.WilsonBridge.corrClay 4 β 0
      + 2 * t * MassGap.WilsonBridge.corrClay 4 β 1
      + MassGap.WilsonBridge.corrClay 4 β 2 := by
  have h := corrClay_hankel_psd 4 2 (by norm_num) (by norm_num) β
    (ι := Fin 2) (fun i => if i = 0 then (0 : Fin 4) else 1)
    (by intro i; fin_cases i <;> norm_num) (fun i => if i = 0 then t else 1)
  simp only [Fin.sum_univ_two] at h
  norm_num at h
  have h11 : (1 + 1 : Fin 4) = 2 := rfl
  rw [h11] at h
  linarith

#print axioms corrClay_hankel_psd_at_extent_four

end Clay

end MassGap.Hankel
