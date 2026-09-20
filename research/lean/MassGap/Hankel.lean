import Mathlib
import MassGap.LogConvex

/-!
# MassGap.Hankel — the Wilson reflection Gram matrix is a POSITIVE-SEMIDEFINITE HANKEL matrix

    0 ≤ ∑ᵢ ∑ⱼ cᵢ cⱼ ρ(eᵢ + eⱼ)     for every real `c`, every family of lags `e` below half the extent

for `ρ = corrHyper` (and its `SU(3)`, four-dimensional instance `corrClay`), at every even lattice
extent and every real coupling. The matrix entry depends on the two indices only through their SUM,
which is what makes it a HANKEL matrix rather than merely a Gram matrix.

## Where it comes from, and why nothing new is assumed

`LogConvex.wilsonReflForm` is the reflection form of the Wilson measure — the first and still the only
`Transfer.ReflForm` built from that measure — and its `form_nonneg` field is positive
semidefiniteness of the reflection pairing on the whole module `LogConvex.localObs` of half-space
observables. `LogConvex.EW_centred_refl_eq_corrHyper` identifies the pairing of two centred plaquette
observables at levels `P` and `Q`, reflected at the plane through the origin, with the connected
correlation at lag `P + Q`.

So `form (v_P, v_Q) = Z · ρ(P + Q)`: a Gram matrix whose entries depend only on `P + Q`. Applying
`form_nonneg` to the linear combination `∑ᵢ cᵢ • v_{eᵢ}` and expanding through
`Transfer.ReflForm.bil` gives the quadratic form above; the partition function `Z` is the same in
every entry and is strictly positive, so it divides out.

`LogConvex.corrHyper_log_convex` is the `2 × 2` minor of exactly this statement — Cauchy–Schwarz is
positive semidefiniteness restricted to two vectors. This is the full matrix.

## The index range, which is the whole delicacy

`obsPlus_mem` requires each level strictly below the plane, `lv 0 P < m` with `n = 2m`, so the lags
`eᵢ` satisfy `eᵢ.val < m` and the entry lag `eᵢ + eⱼ` reaches `2m − 2 = n − 2` and no further —
`hankel_lag_val` records both that the `Fin n` sum does not wrap and that `n − 1` is out of reach.
The missing lag is not an accident of bookkeeping: `n − 1` is the lag at which
`MomentShape.corrClay_neg` (`ρ(n−1) = ρ(1)`) together with a half-line representation
`ρ(k) = ∑ w λᵏ` with `λ ∈ [0,1]` would feed `Spectral.flat_of_aperiodic` and force `ρ` flat from lag
one. A statement about lags `0 … n−2` is the largest one this geometry supports and the largest one
that is not self-refuting.

## What this is NOT

It is not a finite mode count. A positive-semidefinite Hankel matrix is the HYPOTHESIS of the
truncated Hamburger moment problem, whose conclusion `ρ(k) = ∑ᵢ wᵢ λᵢᵏ` with finitely many atoms is
the finite mode count the development wants — and that conclusion does not follow from this
hypothesis alone. The implication is FALSE at the singular Hankel matrices, and it is false inside
everything this tree proves about `ρ`: at extent six, `ρ = (1, s, s², s³, s², s)` with `0 < s < 1`
has Hankel matrix `v vᵀ + s²(1−s²)·e₂e₂ᵀ` at `v = (1, s, s²)`, positive semidefinite of rank two,
and it satisfies `ρ ≥ 0`, `corrHyper_log_convex`, `MomentShape.corrClay_even_antitone` and
`MomentShape.corrClay_neg` — yet `∫(x−s)² dμ = ρ(2) − 2sρ(1) + s²ρ(0) = 0` forces any representing
measure to be `δ_s`, which gives `ρ(4) = s⁴ ≠ s²`. So there is no representing measure and no atomic
decomposition. The missing ingredient is the flat-extension (Curto–Fialkow) condition, or positive
DEFINITENESS, under which the Gauss quadrature rule does produce `m` atoms; Mathlib v4.31 has
neither, and has no Hankel matrix, no moment problem and no general quadrature at all.

Nothing here closes that gap. What it does is put the hypothesis of the classical theorem on the
record as a proved property of the Wilson correlation.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.Hankel`.
-/

namespace MassGap.Hankel

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity MassGap.WilsonLattice
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonAction
open MassGap.ActionSplit MassGap.ReflectPositive MassGap.WilsonBridge
open MassGap.LogConvex

/-! ## Part 1 — the index range -/

section Range

/-- **THE ENTRY LAG IS THE ARITHMETIC SUM, AND IT STOPS AT `n − 2`.**

Both halves matter. The first says the `Fin n` addition in the entry lag does not wrap, so
"depends only on `P + Q`" is a statement about the SUM of the levels and not about a residue. The
second says the lags this construction reaches are exactly `0 … n − 2`: the last lag `n − 1` is
outside the range at every extent, because both levels must sit strictly below the plane and the two
fixed planes are `m` apart.

DERIVED: the `2` is `2m − 2` read off `P.val ≤ m − 1` and `Q.val ≤ m − 1`; the `m` is half the
extent, which is the reflection geometry's own bound carried in from `LogConvex.obsPlus_mem`. -/
theorem hankel_lag_val {n m : ℕ} [NeZero n] (hm : n = 2 * m) {P Q : Fin n}
    (hP : P.val < m) (hQ : Q.val < m) :
    ((P + Q : Fin n) : ℕ) = P.val + Q.val ∧ P.val + Q.val + 2 ≤ n := by
  refine ⟨?_, by omega⟩
  rw [Fin.val_add]
  exact Nat.mod_eq_of_lt (by omega)

#print axioms hankel_lag_val

end Range

/-! ## Part 2 — the positive-semidefinite Hankel form -/

section Psd

variable {d n N : ℕ} [NeZero n]

/-- **THE WILSON REFLECTION GRAM MATRIX IS POSITIVE SEMIDEFINITE, AND ITS ENTRY DEPENDS ONLY ON THE
SUM OF THE TWO INDICES.**

    0 ≤ ∑ᵢ ∑ⱼ cᵢ cⱼ ρ(eᵢ + eⱼ)

for every real coefficient family `c`, at every even extent `n = 2m`, every real coupling, and every
family of lags strictly below half the extent. The `2 × 2` case is `corrHyper_log_convex`'s
Cauchy–Schwarz; this is the whole matrix.

The vectors are the centred half-space plaquette observables `obsPlus` at levels `eᵢ`, which
`LogConvex.obsPlus_mem` places in `localObs`; `form_nonneg` of `LogConvex.wilsonReflForm` applied to
`∑ᵢ cᵢ • v_{eᵢ}` is the inequality, and `LogConvex.EW_centred_refl_eq_corrHyper` at the plane through
the origin is what turns the `(i, j)` entry into `ρ(eᵢ + eⱼ)`. The partition function is the same in
every entry — one reflection, one measure — so it factors out of the whole double sum rather than
entry by entry, and being strictly positive it divides out.

It does NOT require `0 ≤ β`: like everything downstream of the even-lag weld, the argument is a
conditional square against a strictly positive Boltzmann weight and never reads the coupling's sign.

DERIVED: no numeral. `m` is half the extent — the reflection geometry's own bound, the two fixed
planes being `m` apart — and `τ`, `μ`, `ν`, `β`, `e` and `c` are the caller's. -/
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

/-! ## Part 3 — the Clay instance, and a non-vacuous case -/

section Clay

/-- **THE CLAY CORRELATION'S REFLECTION GRAM MATRIX IS POSITIVE-SEMIDEFINITE HANKEL** — `SU(3)`, four
dimensions, every even extent, every real coupling, no hypothesis but the geometry.

`MassGap.wilsonCorrAt N β` is `corrClay (N + 1) β` by definition, so this is the same statement about
the aperture-carrying correlation.

DERIVED: `3` is the gauge group's rank and `4` the dimension, both `WilsonBridge.corrClay`'s own; the
directions `0`, `1` and the lag axis `2` are `corrClay`'s own as well. `m` is half the extent. -/
theorem corrClay_hankel_psd (n : ℕ) [NeZero n] (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {ι : Type} [Fintype ι] (e : ι → Fin n) (he : ∀ i, (e i).val < m) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * MassGap.WilsonBridge.corrClay n β (e i + e j) := by
  simp only [MassGap.WilsonBridge.corrClay]
  exact corrHyper_hankel_psd (N := 3) (d := 4) (by norm_num) (2 : Fin 4) m hm hm0
    (by decide) (by decide) β e he c

#print axioms corrClay_hankel_psd

/-- **NON-VACUITY — the `2 × 2` Hankel minor at extent four.**

At `n = 4`, `m = 2`, the admissible levels are `0` and `1`, so the matrix is
`[[ρ(0), ρ(1)], [ρ(1), ρ(2)]]` and its positive semidefiniteness at the coefficient family
`c = (t, 1)` is a genuine one-parameter family of constraints on three distinct lags. Written at an
explicit `c` so that the statement is not an empty quantification over a vacuous index range.

DERIVED: the extent `4` is the smallest even extent with `0 < m`; the levels `0` and `1` are the two
below the plane at half of it. Nothing is chosen. -/
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
