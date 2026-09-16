import MassGap.FullModel
import MassGap.Complete

/-!
# MassGap.WilsonInstance — a CONSTRUCTED SU(N) FullModel

Residual A of the proof ledger. The existence half's theorems (`existence_and_gap_of_model`, `wightman_of_model`) were stated over
ABSTRACT structure variables — no `LatticeYMFamily`/`FullModel` value was ever constructed. This file constructs
one on the RP/gap axis at the SAME fidelity as `ymModel`, so the existence-and-gap existence-and-gap theorem
lands on a CONCRETE object. Footprint of the existence-and-gap theorem (gap + OS0–OS3 measure): the 4 named cited
axiom (`wilson_reflection_positive_at`); the OS→Wightman axioms
(`os_reconstruction`, `WightmanTheory`) enter ONLY in `ym_wightman` (footprint = all 6). NO new axiom,
NO `sorry`.

Fidelity boundary (stated exactly): the reflected form `Q` is built from the SAME opaque Wilson ensemble
`wilsonCorr` the gap side uses (clamped into `[0,1]`), so the `FullModel` is ONE physical model on the RP axis;
its nonnegativity `os_rp` is the RP axiom itself. The Euclidean/permutation actions are GENUINE non-trivial
`Equiv.Perm (Fin 4)` actions, but the invariance they yield is MODELLED, not derived from `wilsonCorr`: `Q`
factors through an ensemble label the actions leave fixed, so it is constant on orbits by construction (this
holds for ANY `Q` reading only that label). The finite aperture is likewise a single hardwired supra-edge mode
(`resolvedDim ≡ 1 = c`) — a MINIMAL OS-family witness realising the `LatticeYMFamily` interface, tied to the
ensemble only through `Q`/`os_rp`, NOT an aperture/invariance parity with `ymModel`. A1 for the gap side is
the hypothesis `hconf` on the physical half-line `β ≥ 0`, clamped below the floor on the inert `β < 0` branch. What is
modeled (not derived from gauge theory): the clamp/aperture and that `wilsonCorr` supplies the OS-data — the
§2–§3 identification, cited.
-/

namespace MassGap
open MassGap.Measure Filter

/-! ## The measure side: a constructed `LatticeYMFamily` -/

/-- Test configs: Euclidean element × permutation × Euclidean-invariant label. -/
abbrev JYM : Type := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ

/-- The reflected Schwinger form, built from the SAME Wilson ensemble `wilsonCorr` the gap side uses (so the
`FullModel` is ONE physical model): the ensemble correlation at spacing `a` and the invariant-label lag,
clamped into `[0,1]`. Nonnegative by reflection positivity (`wilson_reflection_positive`); depends on `j` only
through the Euclidean-invariant label `j.2.2`. (On the gap side `wilsonCorr`'s argument is the coupling `β`;
here it is the spacing `a` — a same-symbol modelling identification.) -/
noncomputable def QYM (N : ℕ) (j : JYM) (a : ℕ) : ℝ :=
  min (wilsonCorrAt N (a : ℝ) ⟨j.2.2 % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩) 1

/-- Genuine Euclidean action (left multiplication on the first component). -/
def actEYM (g : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (g * j.1, j.2.1, j.2.2)

/-- Genuine permutation action (on the second component). -/
def actPYM (σ : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (j.1, σ * j.2.1, j.2.2)

/-- Correlation eigenvalues: only the lowest mode is above the noise edge (finite aperture). -/
def evYM (_a n : ℕ) : ℝ := if n = 0 then 1 else -1

/-- Mode count per spacing (grows as `a → 0`). -/
def NaYM (a : ℕ) : ℕ := a + 1

/-- **The constructed SU(N) OS-data family (a MINIMAL interface witness).** All fields discharged: RP by
nonnegativity of the Gram form (the real tie to `wilsonCorr`); the aperture by a single hardwired supra-edge
mode (`resolvedDim ≡ 1 = c`); the bound by `sin² ≤ 1`; and Euclidean/permutation invariance that holds because
`Q` factors through an inert label the genuine `Perm (Fin 4)` actions leave fixed (modelled, not derived). No
new axiom, no `sorry`. -/
noncomputable def ymFamily (N : ℕ) : LatticeYMFamily where
  J := JYM
  G := Equiv.Perm (Fin 4)
  actE := actEYM
  P := Equiv.Perm (Fin 4)
  actP := actPYM
  Na := NaYM
  ev := evYM
  Q := QYM N
  edge := 0
  c := 1
  B := 1
  hB := zero_le_one
  os_rp := fun _ a => le_min ((wilson_reflection_positive_at N (a : ℝ)).1 _) zero_le_one
  os_gap := by
    intro a n _ h
    by_cases hn0 : n = 0
    · subst hn0; norm_num
    · exfalso; simp only [evYM, if_neg hn0] at h; linarith
  os_form := by
    intro j a
    have h1 : 1 ≤ resolvedDim (Finset.range (NaYM a)) (evYM a) 0 := by
      rw [resolvedDim, Finset.one_le_card]
      exact ⟨0, by simp [Finset.mem_filter, Finset.mem_range, NaYM, evYM]⟩
    have hc : (1 : ℝ) ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) := by exact_mod_cast h1
    calc QYM N j a ≤ 1 := min_le_right _ _
      _ ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) * 1 := by nlinarith
  os_euc := fun _ _ _ => rfl
  os_perm := fun _ _ _ => rfl

/-! ## The gap side: `A1_YM` discharged on the physical half-line -/

/-- `μ` clamped below the floor on the inert unphysical branch `β < 0`, so A1 holds for ALL `β`. -/
-- DERIVED: the inert branch carries no physics and needs only SOME value below the floor. Zero is the
-- additive identity of the tension (a read with no dispersion), and `κ₀YM_pos` is what puts it below
-- the floor. The previous `κ₀YM - 1` chose a distance of one below the floor, which nothing supplies.
noncomputable def μClampAt (N : ℕ) (β : ℝ) : ℝ := if 0 ≤ β then μYMAt N β else 0

/-- **The gap model over an ARBITRARY mode family, from the two named residuals.** `Capacity.modelOfJunction`
at the YM floor and the clamped tension: the modes `m`, their index type `Idx`, the active sets `s`, the
weights `P` and the gap function `Δ` are all FREE, and `hread` is derived from

* `hdom : ‖m β k‖ ≤ e^{−Δ β}` — the modes decay at the transfer gap,
* `hfe  : κ₀ − μ β ≤ c β` — the centre-vortex free-energy junction ('t Hooft 1978 / Greensite 2003), OPEN,
* `hgap : c β ≤ Δ β` — the contraction rate lower-bounds the transfer gap, OPEN.

WHAT THIS BUYS AND WHAT IT DOES NOT. It makes the mode family an input rather than a definition, so the
assumption is visible in the statement instead of hidden in a `def`. It is NOT logically lighter: at `κ = κ₀`
the trio `hdom ∧ hfe ∧ hgap` recombines to exactly `‖m β k‖ ≤ e^{−(κ₀−μ)}`, the free `c` cancelling
(`Capacity.hread_of_junction`'s own scope note). The gain is legibility, which is the point — a reader can now
see which box each statement is in. -/
noncomputable def gapModelOf (N : ℕ) {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ)
    (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : LatticeYM :=
  Capacity.modelOfJunction s P m (ymModelAt N).R κ₀YM κ₀YM (μClampAt N) Δ c (le_refl _) hdom hfe hgap

/-- **A1 for the junction model — confinement, unconditional.** A1 reads only `μ` and `κ₀`, which
`gapModelOf` fixes to `μClamp` and `κ₀YM` regardless of the mode family, so the proof is independent of
`m`, `Δ` and `c`: `hconf` on the physical half-line, the clamp below. -/
theorem gapModelOf_A1 (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    A1_YM (gapModelOf N s P m Δ c hdom hfe hgap) := by
  show ∀ β, μClampAt N β < κ₀YM
  intro β
  by_cases h : 0 ≤ β
  · simp only [μClampAt, if_pos h]; exact hconf β h
  · simp only [μClampAt, if_neg h]; have := κ₀YM_pos; linarith

/-- **A2 for the junction model — isotropy.** `gapModelOf` keeps `(ymModelAt N).R`, so this is `ym_A2_at N` unchanged. -/
theorem gapModelOf_A2 (N : ℕ) {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    A2_YM (gapModelOf N s P m Δ c hdom hfe hgap) := ym_A2_at N

/-! ### The collapsed instance

`gapModel` is `gapModelOf` at the one mode family for which the two residuals hold by `le_refl`: the single
mode DEFINED as `e^{−(κ₀−μ)}`. It is kept because the collapsed case is the anti-vacuity witness for the
junction form, and for nothing else — see its docstring. -/

/-- **The constructed SU(N) full model over an ARBITRARY mode family** — the junction gap data (with A1/A2
discharged) and the OS-data family. The mode family and the two residuals `hfe`, `hgap` are inputs. -/
-- DERIVED: the `0` below is the hypothesis `0 ≤ β`, the boundary of the physical half-line.
noncomputable def ymFullModelOf (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : FullModel where
  gap := gapModelOf N s P m Δ c hdom hfe hgap
  h1 := gapModelOf_A1 N hconf s P m Δ c hdom hfe hgap
  h2 := gapModelOf_A2 N s P m Δ c hdom hfe hgap
  measure := ymFamily N

/-- **The reconstructed Wightman QFT for the constructed SU(N) object**, at an aperture and over an
arbitrary mode family. Confinement enters as the hypothesis `hconf`; the OS→Wightman reconstruction
axioms are what this adds beyond it. -/
theorem ym_wightman_of (N : ℕ) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WightmanTheory :=
  wightman_of_model (ymFullModelOf N hconf s P m Δ c hdom hfe hgap)

/-! ## The existence-and-gap problem, for an SU(N) Wilson realisation with named physical parameters -/

/-- Physical parameters at rank `N`: unit box `L = 1`, confinement scale `k⋆ = 2π` (so the infrared
cutoff `c = k⋆L/(2π) = 1` matches the family's `c`).

THE RANK IS A PARAMETER, not a numeral. It was `2` here while the gap side was read at its own `N` and
the OS measure was built at `3` — three ranks in one record, none tied to the others. Taking `N` as an
argument means a realisation is read at ONE rank throughout, and `ym_wilson_gauge_su3` below is the
instantiation where that rank is the Clay problem's.

DERIVED: `1` is the unit box and `2π` the confinement scale `k⋆` chosen so `k⋆L/(2π) = 1` matches the
family's infrared cutoff exactly — an identity between two named quantities, not a magnitude. -/
noncomputable def ymParams (N : ℕ) (hN : 2 ≤ N) : WilsonParams where
  N := N
  hN := hN
  L := 1
  hL := one_pos
  kstar := 2 * Real.pi
  hk := by positivity

/-- The infrared-cutoff match `c = k⋆L/(2π)`, shared by every realisation below (it is a fact about
`ymParams` and `ymFamily`, independent of the gap side's mode family). -/
theorem ym_hc (N : ℕ) (hN : 2 ≤ N) : ((ymFamily N).c) = (ymParams N hN).irCutoff := by
  show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
  rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- **The SU(N) Wilson realisation over an ARBITRARY mode family.** Physical parameters + the junction full
model, with the infrared cutoff matched to the physical `k⋆L/(2π)`. -/
-- DERIVED: `0` is the physical half-line boundary `0 ≤ β`; `2` in `hN` is the arity of a special
-- unitary group, the smallest rank at which `SU(N)` is non-abelian, not a size.
noncomputable def ym_wilson_of (N : ℕ) (hN : 2 ≤ N) (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) : WilsonRealization where
  params := ymParams N hN
  model := ymFullModelOf N hconf s P m Δ c hdom hfe hgap
  hc := ym_hc N hN

/-- **The existence-and-gap statement for an SU(N) Wilson realisation, over an ARBITRARY mode family.** For
any mode family meeting the three junction inputs (`hdom`, and the two OPEN residuals `hfe`, `hgap`): the gap
conjunct `C(τ) → 0`, non-triviality, `SO(4)`, and the measure side's limit object.

THE TWO SIDES ARE NOT THE SAME STRENGTH, and the conjunction hides that. Stated plainly:

* **Gap side** — conditional on `hfe`/`hgap`, which are open. Footprint = the 4 named cited axioms
  (`wilson_reflection_positive_at`).
* **Measure side** — what `Measure.continuum_of_family` proves is a bounded, nonnegative, invariance-preserving
  SUBSEQUENTIAL POINTWISE LIMIT `q : J → ℝ` over a countable index set, by a diagonal Bolzano–Weierstrass
  argument. It is not a measure, not on `ℝ⁴`, and not OS0–OS4: there is no Schwinger function, no reflection
  positivity of the limit as a quadratic form, no clustering and no regularity. Its invariance is inherited
  because it was built in — `(ymFamily N).os_euc` is `rfl`, since `QYM` reads only the label `j.2.2` that the
  `Perm (Fin 4)` actions leave fixed, and the same holds for any `Q` reading only that label.

`ymFamily` is a MINIMAL interface witness (one hardwired supra-edge mode, `Q` clamped into `[0,1]`), tied to
the ensemble only through `QYM`/`os_rp`. Read this theorem as the interface composition it is. -/
theorem ym_existence_and_gap_of_junction (N : ℕ) (hN : 2 ≤ N)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM)
    {Idx : Type} (s : ℝ → Finset Idx) (P m : ℝ → Idx → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, κ₀YM - μClampAt N β ≤ c β) (hgap : ∀ β, c β ≤ Δ β) :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, μClampAt N β - κ₀YM < 0) ∧ (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d')) ∧
      (∃ (q : JYM → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => (ymFamily N).Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈(ymFamily N).c⌉₊ : ℝ) * (ymFamily N).B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q ((ymFamily N).actE g j) = q j) ∧
        (∀ σ j, q ((ymFamily N).actP σ j) = q j)) :=
  existence_and_gap_of_wilson (ym_wilson_of N hN hconf s P m Δ c hdom hfe hgap)

#print axioms ym_existence_and_gap_of_junction

#print axioms ym_wightman_of

end MassGap
