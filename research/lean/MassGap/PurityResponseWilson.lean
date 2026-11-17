import Mathlib
import MassGap.RectWilsonG
import MassGap.GaugeWilson
import MassGap.PurityResponse
import MassGap.OpenAIDictionary

/-!
# MassGap.PurityResponseWilson — Proposition 6.4 for the Wilson partition function

Proposition 6.4 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`),
for the Wilson model `RectWilsonG.sysRG` of a gauge group `G` on the rectangular 4-torus.

`RectWilsonG.sysRG` sums the plaquette density over ordered direction pairs. The diagonal pairs
`(i, i)` contribute `φ(1) = 0`, and `(j, i)` carries the inverse holonomy of `(i, j)`, which `φ` does
not see, so each unoriented plaquette appears twice (`action_eq_two_mul`). The paper's action is
`SW G L = action / 2`, with `0 ≤ SW ≤ 2 N`, `N = 6 V T`, `V T = ∏ L i`, and
`Z_b = ZRG G L (b / 2)`.

* `hol_swap`, `action_eq_two_mul`: `hol ((j, i), x) = (hol ((i, j), x))⁻¹`, so
  `action = 2 Σ_x Σ_{i<j} φ(hol ((i, j), x))`.
* `action_le`: the diagonal pairs contribute `φ(1) = 0` (`hol_μμG`), so `action ≤ 24 ∏ L i`.
* `SW_nonneg`, `SW_le`, `measurable_SW`: `0 ≤ SW ≤ 2 (6 ∏ L i)`, measurable.
* `mom_eq`, `psi_eq`: `Z_b = ZRG G L (b/2)`, so
  `ψ(b) = 2 log ZRG G L (b/2) − log ZRG G L' (b/2)`.
* `prod_eq`, `prod_double`: `∏ L i = L μ · V` with `V = ∏_{j ≠ μ} L j`; doubling the time extent
  at fixed spatial extents doubles `∏ L i`.
* `wilson_hasDerivAt`: (6.6), `dψ/db = 12 V T (e_{2T} − e_T)` at `N = 6 V T`.
* `wilson_psi_eq_integral`: (6.7). `wilson_lipschitz`: (6.8), `|ψ(b) − ψ(b₀)| ≤ 24 V T |b − b₀|`.
* `wilson_response_certified`: (6.9), the margin `ψ(b₀)/V ≤ ε_T/2` at `ε_T = 1/(161 (48T)³)`
  certifies `ψ(b)/V ≤ ε_T` for `|b − b₀| ≤ 1/(7728 · 48³ T⁴)`.

DERIVED (module-wide): `24 = 2 · 12`, the twelve ordered pairs of distinct directions times
`wilsonDensityG_le_two`; `6 = 24 / 4`, the halving of `SW` and the `2` of `0 ≤ S ≤ 2N`.
-/

namespace MassGap.PurityResponseWilson

open Real MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
  MassGap.RectWilson MassGap.RectWilsonG MassGap.GaugeGroup MassGap.GaugeWilson
  MassGap.PurityResponse

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The paper's Wilson action: each unoriented plaquette once (`action` counts each twice,
`action_eq_two_mul`). -/
noncomputable def SW (L : Fin 4 → ℕ) (U : (sysRG G L).Config) : ℝ := (sysRG G L).action U / 2

/-- The product Haar measure on the links. -/
noncomputable abbrev nu (L : Fin 4 → ℕ) : Measure (sysRG G L).Config := (sysRG G L).vol (probHaar G)

variable {G}

instance (L : Fin 4 → ℕ) : IsProbabilityMeasure (nu G L) := by
  unfold nu System.vol; infer_instance

variable {L : Fin 4 → ℕ}

/-- Reversing the orientation of a plaquette inverts its holonomy, in every group. -/
theorem hol_swap (U : (sysRG G L).Config) (i j : Fin 4) (x : RSite L) :
    (sysRG G L).hol ((j, i), x) U = ((sysRG G L).hol ((i, j), x) U)⁻¹ := by
  rw [hol_eqG, hol_eqG]; group

/-- The ordered-pair action is twice the sum over unoriented plaquettes `i < j`, by
`OpenAIDictionary.sum_pairs_eq_two_mul` with `hol_swap`, `wilsonDensityG_inv` and `hol_μμG`.

DERIVED: `2` counts the two orientations of one plaquette. -/
theorem action_eq_two_mul (U : (sysRG G L).Config) :
    (sysRG G L).action U = 2 * ∑ x : RSite L, ∑ p : OpenAIDictionary.Directions 4,
      wilsonDensityG G ((sysRG G L).hol (p.1, x) U) := by
  have hpt : ∀ x : RSite L, ∑ q : Fin 4 × Fin 4, (sysRG G L).φ ((sysRG G L).hol (q, x) U)
      = 2 * ∑ p : OpenAIDictionary.Directions 4, wilsonDensityG G ((sysRG G L).hol (p.1, x) U) :=
    fun x => OpenAIDictionary.sum_pairs_eq_two_mul
      (fun q => (sysRG G L).φ ((sysRG G L).hol (q, x) U))
      (fun a b => by rw [hol_swap]; exact wilsonDensityG_inv _)
      (fun a => by rw [hol_μμG]; exact wilsonDensityG_one)
  calc (sysRG G L).action U = ∑ q : RPlaq L, (sysRG G L).φ ((sysRG G L).hol q U) := rfl
    _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_congr rfl (fun x _ => hpt x),
          ← Finset.mul_sum]

/-- DERIVED: `24 = 2 · 12`, twelve ordered pairs of distinct directions. -/
theorem action_le (U : (sysRG G L).Config) :
    (sysRG G L).action U ≤ 24 * ∏ i, (L i : ℝ) := by
  have hpt : ∀ q : RPlaq L,
      (sysRG G L).φ ((sysRG G L).hol q U) ≤ if q.1.1 = q.1.2 then (0 : ℝ) else 2 := by
    rintro ⟨⟨i, j⟩, x⟩
    split_ifs with h
    · dsimp only at h
      subst h
      rw [hol_μμG]
      exact (wilsonDensityG_one (G := G)).le
    · exact wilsonDensityG_le_two _
  calc (sysRG G L).action U = ∑ q : RPlaq L, (sysRG G L).φ ((sysRG G L).hol q U) := rfl
    _ ≤ ∑ q : RPlaq L, (if q.1.1 = q.1.2 then (0 : ℝ) else 2) :=
        Finset.sum_le_sum fun q _ => hpt q
    _ = 24 * ∏ i, (L i : ℝ) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi,
          Fintype.card_fin, Nat.cast_prod, Fintype.sum_prod_type, Fin.sum_univ_four]
        simp (config := { decide := true }) only [↓reduceIte, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
        ring

theorem SW_nonneg (U : (sysRG G L).Config) : 0 ≤ SW G L U :=
  div_nonneg (wilsonSystemG_action_nonneg (rbd L) U) zero_le_two

theorem SW_le (U : (sysRG G L).Config) : SW G L U ≤ 2 * (6 * ∏ i, (L i : ℝ)) := by
  have := action_le U
  unfold SW
  linarith

theorem measurable_SW : Measurable (SW G L) :=
  (measurable_wilsonSystemG_action (rbd L)).div_const 2

theorem mom_eq (b : ℝ) : mom (nu G L) (fun _ => 1) (SW G L) b = ZRG G L (b / 2) := by
  unfold mom ZRG System.partition System.boltz SW
  congr 1
  funext U
  rw [one_mul]
  congr 1
  ring

theorem psi_eq (L' : Fin 4 → ℕ) (b : ℝ) :
    psi (nu G L) (nu G L') (SW G L) (SW G L') b
      = 2 * log (ZRG G L (b / 2)) - log (ZRG G L' (b / 2)) := by
  unfold psi
  rw [mom_eq, mom_eq]

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem prod_eq (L : Fin 4 → ℕ) (μ : Fin 4) :
    ∏ i, (L i : ℝ) = L μ * ∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ) :=
  Fintype.prod_eq_mul_prod_subtype_ne _ μ

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem prod_double {L L' : Fin 4 → ℕ} {μ : Fin 4} (hL' : L' μ = 2 * L μ)
    (htr : tr L' μ = tr L μ) : ∏ i, (L' i : ℝ) = 2 * ∏ i, (L i : ℝ) := by
  have hs : ∏ j : {j : Fin 4 // j ≠ μ}, (L' j.1 : ℝ) = ∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ) :=
    Finset.prod_congr rfl fun j _ => by rw [show L' j.1 = L j.1 from congrFun htr j]
  rw [prod_eq L' μ, prod_eq L μ, hs, hL']
  push_cast
  ring

section Response

variable {L L' : Fin 4 → ℕ} {μ : Fin 4}

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem VT_eq (L : Fin 4 → ℕ) (μ : Fin 4) :
    6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ = 6 * ∏ i, (L i : ℝ) := by
  rw [prod_eq L μ]; ring

theorem SW_le_VT (U : (sysRG G L).Config) :
    SW G L U ≤ 2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ) := by
  rw [VT_eq]; exact SW_le U

theorem SW_le_VT' (hL' : L' μ = 2 * L μ) (htr : tr L' μ = tr L μ) (U : (sysRG G L').Config) :
    SW G L' U ≤ 2 * (2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ)) := by
  have h := SW_le U
  rw [prod_double hL' htr] at h
  rw [VT_eq]
  linarith

omit [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] in
theorem VT_pos (hT : 0 < L μ) (hV : ∀ j : {j : Fin 4 // j ≠ μ}, 0 < L j.1) :
    0 < 6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ := by
  have : 0 < ∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast hV j
  have hT' : (0 : ℝ) < L μ := by exact_mod_cast hT
  positivity

/-- Paper, (6.6): `dψ/db = 12 V T (e_{2T} − e_T)`, `V = ∏_{j ≠ μ} L j`, `T = L μ`. -/
theorem wilson_hasDerivAt (hT : 0 < L μ) (hV : ∀ j : {j : Fin 4 // j ≠ μ}, 0 < L j.1)
    (hL' : L' μ = 2 * L μ) (htr : tr L' μ = tr L μ) (b : ℝ) :
    HasDerivAt (psi (nu G L) (nu G L') (SW G L) (SW G L'))
      (2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ)
        * (eT (2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ)) (nu G L') (SW G L') b
          - eT (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ) (nu G L) (SW G L) b)) b :=
  hasDerivAt_psi (VT_pos hT hV) measurable_SW measurable_SW SW_nonneg SW_le_VT SW_nonneg
    (SW_le_VT' hL' htr) b

/-- Paper, (6.7): `ψ(b) = 12 V T ∫₀^b (e_{2T}(u) − e_T(u)) du`. -/
theorem wilson_psi_eq_integral (hT : 0 < L μ) (hV : ∀ j : {j : Fin 4 // j ≠ μ}, 0 < L j.1)
    (hL' : L' μ = 2 * L μ) (htr : tr L' μ = tr L μ) (b : ℝ) :
    2 * log (ZRG G L (b / 2)) - log (ZRG G L' (b / 2))
      = 2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ)
        * ∫ u in (0 : ℝ)..b,
          (eT (2 * (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ)) (nu G L') (SW G L') u
            - eT (6 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ) (nu G L) (SW G L) u) := by
  rw [← psi_eq]
  exact psi_eq_integral (VT_pos hT hV) measurable_SW measurable_SW SW_nonneg SW_le_VT SW_nonneg
    (SW_le_VT' hL' htr) b

/-- Paper, (6.8): `|ψ(b) − ψ(b₀)| ≤ 24 V T |b − b₀|`. -/
theorem wilson_lipschitz (hT : 0 < L μ) (hV : ∀ j : {j : Fin 4 // j ≠ μ}, 0 < L j.1)
    (hL' : L' μ = 2 * L μ) (htr : tr L' μ = tr L μ) (b b₀ : ℝ) :
    |(2 * log (ZRG G L (b / 2)) - log (ZRG G L' (b / 2)))
        - (2 * log (ZRG G L (b₀ / 2)) - log (ZRG G L' (b₀ / 2)))|
      ≤ 24 * (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) * L μ * |b - b₀| := by
  rw [← psi_eq, ← psi_eq]
  have h := psi_lipschitz (ν₁ := nu G L) (ν₂ := nu G L') (VT_pos hT hV) measurable_SW measurable_SW
    SW_nonneg SW_le_VT SW_nonneg (SW_le_VT' hL' htr) b b₀
  linarith

/-- Paper, (6.9): a margin `ψ(b₀)/V ≤ ε_T/2` at `ε_T = 1/(161 (48T)³)` certifies `ψ(b)/V ≤ ε_T`
for `|b − b₀| ≤ 1/(7728 · 48³ T⁴)`, with `ψ(b) = 2 log ZRG G L (b/2) − log ZRG G L' (b/2)`. -/
theorem wilson_response_certified (hT : 0 < L μ) (hV : ∀ j : {j : Fin 4 // j ≠ μ}, 0 < L j.1)
    (hL' : L' μ = 2 * L μ) (htr : tr L' μ = tr L μ) {b b₀ : ℝ}
    (hm : (2 * log (ZRG G L (b₀ / 2)) - log (ZRG G L' (b₀ / 2)))
        / (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) ≤ 1 / (161 * (48 * (L μ : ℝ)) ^ 3) / 2)
    (hr : |b - b₀| ≤ 1 / (7728 * 48 ^ 3 * (L μ : ℝ) ^ 4)) :
    (2 * log (ZRG G L (b / 2)) - log (ZRG G L' (b / 2)))
        / (∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ)) ≤ 1 / (161 * (48 * (L μ : ℝ)) ^ 3) := by
  have hV' : 0 < ∏ j : {j : Fin 4 // j ≠ μ}, (L j.1 : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast hV j
  have hT' : (0 : ℝ) < L μ := by exact_mod_cast hT
  rw [← psi_eq] at hm ⊢
  exact response_certified hV' hT' measurable_SW measurable_SW SW_nonneg SW_le_VT SW_nonneg
    (SW_le_VT' hL' htr) hm hr

end Response

end MassGap.PurityResponseWilson

#print axioms MassGap.PurityResponseWilson.hol_swap
#print axioms MassGap.PurityResponseWilson.action_eq_two_mul
#print axioms MassGap.PurityResponseWilson.action_le
#print axioms MassGap.PurityResponseWilson.SW_nonneg
#print axioms MassGap.PurityResponseWilson.SW_le
#print axioms MassGap.PurityResponseWilson.measurable_SW
#print axioms MassGap.PurityResponseWilson.mom_eq
#print axioms MassGap.PurityResponseWilson.psi_eq
#print axioms MassGap.PurityResponseWilson.prod_eq
#print axioms MassGap.PurityResponseWilson.prod_double
#print axioms MassGap.PurityResponseWilson.VT_eq
#print axioms MassGap.PurityResponseWilson.SW_le_VT
#print axioms MassGap.PurityResponseWilson.SW_le_VT'
#print axioms MassGap.PurityResponseWilson.VT_pos
#print axioms MassGap.PurityResponseWilson.wilson_hasDerivAt
#print axioms MassGap.PurityResponseWilson.wilson_psi_eq_integral
#print axioms MassGap.PurityResponseWilson.wilson_lipschitz
#print axioms MassGap.PurityResponseWilson.wilson_response_certified
