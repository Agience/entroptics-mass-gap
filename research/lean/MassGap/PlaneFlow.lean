import Mathlib
import MassGap.ZoomStep
import MassGap.OneStepZoom

/-!
# MassGap.PlaneFlow — anisotropic blocking of the coupling plane, and why it has no flow at tree level

`AnisoTorus.DA N β t w` is the window defect of the 4D torus with coupling `β` on the planes `(0,1)`, `(2,3)` and
`t` on the four mixed planes; `DA N β β w` is the window coupling (`AnisoTorus.DA_iso`). The lead: block only the
in-plane directions, where the 2D heat-kernel torus steps exactly (`OneStepZoom.hk_exact`, `β ↦ β/4`), and read
the induced map `Φ` on `(β, t)` against the proved regions (the strip `t < t*(β)` of `StripWidth`/`StripWiden`,
the box at small `β`). This module computes the tree-level map of every anisotropic blocking and proves that a
full window step is the identity on the coupling space, for every group. Declarations are in
`MassGap.PlaneFlow`.

## 1. The exponent of a blocking (a defined model, its algebra proved)

`blockExp` is a DEFINED bookkeeping rule modelling area-law series plus bond moving. It is not a theorem about the
Wilson measure. What is proved is the counting identity and the resulting algebra of the model.

Block a set `K` of directions by `2`. A coarse plaquette spanned by the directions `P` (`|P| = 2`) covers
`2^{|K ∩ P|}` fine plaquettes in series, which in heat-kernel units (coupling inversely proportional to area,
`OneStepZoom.hkZ_double`) divides its coupling by `2^{|K ∩ P|}`; and `2^{|K| − |K ∩ P|}` parallel copies along
the blocked directions transverse to it are moved onto it (bond moving), which multiplies the coupling by that
count. The net factor is `2^{blockExp K P}`, `blockExp K P = |K| − 2 |K ∩ P|`.

* `sum_card_inter`: over `k` blocking steps in which every direction is blocked `m` times,
  `Σ_i |K_i ∩ S| = m |S|` for every set `S` of directions.
* `sum_blockExp`: then `Σ_i blockExp K_i P = m (d − 4)` for every plaquette orientation `P`. At `d = 4` it is
  `0` (`sum_blockExp_four`): whatever the order and grouping of the directions (in-plane first, one family at a
  time, isotropic), a sequence that compares window `w + m` with window `w` has tree-level exponent zero on every
  plaquette orientation.

## 2. The plane families (proved)

`P01 = {0, 1}`, `P23 = {2, 3}`, `P02 = {0, 2}` (a mixed orientation; the other three follow by symmetry).
`exp_P01_P01 = −2`, `exp_P01_P23 = 2`, `exp_P01_P02 = 0`. Blocking the `(0,1)` family is the exact 2D step on
that family (`β ↦ β/4`, `OneStepZoom.quarter`), bond moving `×4` on the complementary family (the same `4 = 2^{d−2}`
as the transverse factor of `OneStepZoom.stack_step`), and a marginal mixed coupling: series `÷2` in the blocked
in-plane direction, parallel `×2` from the blocked transverse one.

* `step01 (a, b, t) = (a/4, 4b, t)`, `step23 (a, b, t) = (4a, b/4, t)`, `a` the `(0,1)` coupling, `b` the
  `(2,3)` coupling, `t` the mixed one. `step01_fst`: the first entry is `OneStepZoom.quarter`.
* `step23_step01`, `step01_step23`: the two family steps are inverse; `window_step_id`: the window step is the
  identity. `iterate_window_step`: every orbit is constant. `orbit_mem_iff`: the orbit of a point enters a region
  `R` iff the point is in `R`. So from the diagonal `(β, β, β)` at large `β` the model's tree flow never enters the strip
  (`t*(β) < β`) or the box (`β` small); for `SU(N)` and for `U(1)` alike. The `U(1)` test passes only in the
  trivial way: the flow reads no group, and it does not move.

## 3. A fixed-point flow carries no conclusion (proved)

`ZoomStep.ZoomStepMap g id` reads `g β (w + 1) ≤ g β w`, monotonicity along the windows.
`const_zoomStepMap_id`: a positive constant reading satisfies it; `const_not_tendsto`: it does not tend to `0`.
`id_not_noFixedAbove`: the identity has fixed points above `0`. So an exact, correctly signed comparison at the tree
map is still empty: the photon stall (`PhotonStall.photon4_stall_of`, a constant along the zoom) satisfies it.

## The obstruction

Three facts, each sufficient to stop the lead as posed.

* Covering. The planes `(0,1)`, `(2,3)` are complementary: every direction is in-plane for one family and
  transverse for the other. "Block in-plane, keep the transverse lattice" is possible for one family only; the
  other family is then bond-moved by `4` (`exp_P01_P23`), and the window comparison needs both
  (`sum_blockExp_four`).
* Power counting. The total exponent `m (d − 4)` is the classical marginality of the 4D gauge coupling; the
  anisotropic order of blocking redistributes the exponent between the steps and cancels it over the window. Any
  `Φ` built from area laws and bond moving (group-blind operations) has `Φ = id` on the window, and the motion of
  the true flow is the logarithmic one of asymptotic freedom, `β ↦ β − b₀ log 4 + O(1/β)` with
  `b₀ = 11N/(48π²)` for `SU(N)` and `b₀ = 0` for `U(1)` (cited, perturbative). That flow does reach the box at
  small `β` in about `β/(b₀ log 4)` steps along the diagonal, and reads the group; a one-step comparison at that
  map is the Bałaban-level two-sided control, not supplied by any one-sided bound.
* Exactness. Every in-plane link also lies on `2(d − 2) = 4` mixed plaquettes, so the in-plane decimation is
  exact only at `t = 0` (`DecoupledSplit`, `OneStepZoom`); at `t > 0` each side of the comparison is one-sided
  with its own bulk, and the step needs an upper bound at window `w + 1` and a lower bound at window `w + 2` with
  one bulk (`BondMove.defect_le_of_sandwich`), the mismatch being extensive.

DERIVED (module-wide): `2` the block factor and the plaquette dimension; `4 = 2²` the area factor and the
dimension; `0`, `1`, `2`, `3` the directions; `m` the blocking multiplicity. CHOSEN: `P02` as the representative
mixed orientation (symmetry). Cited, not used in a proof: the perturbative `b₀`.

## Where the one-family flow goes (argued, not built)

Iterating `step01` alone (anisotropic extents) sends `a → 0`, `b → ∞`, `t` fixed. At `b = ∞` the `(2,3)` planes are
flat, the transverse links gauge to `1`, and a mixed plaquette becomes `t φ(U_μ(x, y) U_μ(x, y + e)⁻¹)`; at `a → 0`
the in-plane weights are uniform. The limit is one 2D principal chiral model per `(0,1)` link, on the transverse
torus, at coupling `t`. It reads the group (for `U(1)` it is the XY model, with its Kosterlitz–Thouless phase at
large `t`), and its gap at large `t` is the asymptotically free 2D problem, open. So the one-family flow moves the
diagonal to the 2D chiral model at `t = β`: a reduction of kind, not a route into a proved region.

## What does not follow

* No map `Φ` with `DA(β, t, w + 1) ≤ DA(Φ(β, t), w)` is proved at any `t > 0`; the tree map is the identity
  and its comparison, were it proved, is empty (§3).
* The perturbative flow `β ↦ β − b₀ log 4` is not a comparison of partition functions; nothing here bounds `DA` at
  its image.
* `CouplingTower.StrongEnd`, `AnisoTorus.AnisoAnalytic`, `MixCutTest.VarGap`, `MixPlane.NoStallOnSegment` stay open.
-/

namespace MassGap.PlaneFlow

open Filter Topology

/-! ## 1. The exponent of a blocking -/

/-- **The tree-level exponent** (a defined bookkeeping rule, not a theorem about the Wilson measure) of the coupling on the orientation `P` when the directions `K` are blocked by `2`:
`|K| − 2 |K ∩ P|` (parallel copies `2^{|K| − |K ∩ P|}`, series area `2^{|K ∩ P|}`). DERIVED: `2` the two
factors of the series count. -/
def blockExp {d : ℕ} (K P : Finset (Fin d)) : ℤ := (K.card : ℤ) - 2 * ((K ∩ P).card : ℤ)

/-- **Counting by directions**: if every direction lies in exactly `m` of the blocking sets `K_i`, then
`Σ_i |K_i ∩ S| = m |S|`. No numeral. -/
theorem sum_card_inter {d k m : ℕ} (K : Fin k → Finset (Fin d))
    (hK : ∀ μ : Fin d, (Finset.univ.filter fun i => μ ∈ K i).card = m) (S : Finset (Fin d)) :
    ∑ i, (K i ∩ S).card = m * S.card := by
  have h1 : ∀ i, (K i ∩ S).card = ∑ μ ∈ S, if μ ∈ K i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ μ ∈ S, (∑ i, if μ ∈ K i then 1 else 0) = m := by
    intro μ _
    rw [← Finset.card_filter, hK μ]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The total exponent over a window**: if every one of the `d` directions is blocked `m` times, the summed
exponent on any orientation `P` with `|P| = 2` is `m (d − 4)`. DERIVED: `2` the plaquette dimension; `4 = 2 · 2`. -/
theorem sum_blockExp {d k m : ℕ} (K : Fin k → Finset (Fin d))
    (hK : ∀ μ : Fin d, (Finset.univ.filter fun i => μ ∈ K i).card = m) (P : Finset (Fin d))
    (hP : P.card = 2) : ∑ i, blockExp (K i) P = (m : ℤ) * ((d : ℤ) - 4) := by
  have hall := sum_card_inter K hK Finset.univ
  have hP' := sum_card_inter K hK P
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at hall
  unfold blockExp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e1 : (∑ i, ((K i).card : ℤ)) = ((m * d : ℕ) : ℤ) := by exact_mod_cast hall
  have e2 : (∑ i, ((K i ∩ P).card : ℤ)) = ((m * 2 : ℕ) : ℤ) := by rw [← hP]; exact_mod_cast hP'
  rw [e1, e2]
  push_cast
  ring

/-- **Four dimensions are marginal**: at `d = 4` the summed exponent over a window is `0`, for every order and
grouping of the blocked directions. DERIVED: `4` the dimension. -/
theorem sum_blockExp_four {k m : ℕ} (K : Fin k → Finset (Fin 4))
    (hK : ∀ μ : Fin 4, (Finset.univ.filter fun i => μ ∈ K i).card = m) (P : Finset (Fin 4))
    (hP : P.card = 2) : ∑ i, blockExp (K i) P = 0 := by
  rw [sum_blockExp K hK P hP]
  push_cast
  ring

/-! ## 2. The plane families -/

/-- The `(0,1)` plane directions. DERIVED: `0`, `1` the directions. -/
def P01 : Finset (Fin 4) := {0, 1}
/-- The `(2,3)` plane directions. DERIVED: `2`, `3` the directions. -/
def P23 : Finset (Fin 4) := {2, 3}
/-- A mixed orientation `(0,2)`. CHOSEN representative (the other mixed ones follow by symmetry). -/
def P02 : Finset (Fin 4) := {0, 2}

/-- In-plane blocking of `(0,1)` acts on its own family by `2^{−2}`: the exact 2D step `β ↦ β/4`.
DERIVED: `2` the plane. -/
theorem exp_P01_P01 : blockExp P01 P01 = -2 := by decide

/-- In-plane blocking of `(0,1)` bond-moves the complementary family by `2^2 = 4`, the transverse factor of
`OneStepZoom.stack_step`. DERIVED: `2` the plane. -/
theorem exp_P01_P23 : blockExp P01 P23 = 2 := by decide

/-- In-plane blocking of `(0,1)` leaves a mixed coupling marginal. DERIVED: `0` the exponent. -/
theorem exp_P01_P02 : blockExp P01 P02 = 0 := by decide

/-- **The `(0,1)` family step** on `(a, b, t)` (`a` on `(0,1)`, `b` on `(2,3)`, `t` mixed): `(a/4, 4b, t)`.
DERIVED: `4 = 2^2` from `exp_P01_P01`, `exp_P01_P23`. -/
noncomputable def step01 (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (x.1 / 4, 4 * x.2.1, x.2.2)

/-- **The `(2,3)` family step**: `(4a, b/4, t)`. DERIVED: `4 = 2^2` by the symmetry `(0,1) ↔ (2,3)`. -/
noncomputable def step23 (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (4 * x.1, x.2.1 / 4, x.2.2)

/-- **The window step**: both families blocked once. No numeral. -/
noncomputable def windowStep (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := step23 (step01 x)

/-- The `(0,1)` entry of the family step is the exact 2D heat-kernel map. No numeral. -/
theorem step01_fst (x : ℝ × ℝ × ℝ) : (step01 x).1 = OneStepZoom.quarter x.1 := rfl

/-- The two family steps are inverse, one way. No numeral. -/
theorem step23_step01 (x : ℝ × ℝ × ℝ) : step23 (step01 x) = x := by
  obtain ⟨a, b, t⟩ := x
  simp only [step01, step23, Prod.mk.injEq]
  refine ⟨by ring, by ring, trivial⟩

/-- The two family steps are inverse, the other way. No numeral. -/
theorem step01_step23 (x : ℝ × ℝ × ℝ) : step01 (step23 x) = x := by
  obtain ⟨a, b, t⟩ := x
  simp only [step01, step23, Prod.mk.injEq]
  refine ⟨by ring, by ring, trivial⟩

/-- **The window step is the identity** on the coupling space. No numeral. -/
theorem window_step_id : windowStep = id := funext step23_step01

/-- Every orbit of the window step is constant. No numeral. -/
theorem iterate_window_step (k : ℕ) (x : ℝ × ℝ × ℝ) : windowStep^[k] x = x := by
  rw [window_step_id, Function.iterate_id, id]

/-- **The orbit enters a region iff its start does**: for every region `R` (the strip, the box, any union), some
iterate of the window step lies in `R` exactly when the start does. No numeral. -/
theorem orbit_mem_iff (R : Set (ℝ × ℝ × ℝ)) (x : ℝ × ℝ × ℝ) :
    (∃ k : ℕ, windowStep^[k] x ∈ R) ↔ x ∈ R := by
  simp only [iterate_window_step]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

/-- **The diagonal never enters the strip**: for a strip profile `tStar` with `tStar β < β`, no iterate of the
window step from the diagonal point `(β, β, β)` has mixed coupling below `tStar` of its in-plane coupling.
DERIVED: the diagonal `t = β`. -/
theorem diag_not_strip (tStar : ℝ → ℝ) {β : ℝ} (h : tStar β < β) (k : ℕ) :
    ¬ ((windowStep^[k] (β, β, β)).2.2 < tStar (windowStep^[k] (β, β, β)).1) := by
  rw [iterate_window_step]
  exact not_lt.mpr h.le

/-! ## 3. A fixed-point flow carries no conclusion -/

/-- **A positive constant reading satisfies the identity step**. DERIVED: `0` the sign. -/
theorem const_zoomStepMap_id {c : ℝ} :
    ZoomStep.ZoomStepMap (fun _ _ => c) id :=
  ⟨fun _ h => h, fun _ _ _ _ => le_rfl⟩

/-- A positive constant reading does not tend to `0` along the windows. DERIVED: `0` the limit. -/
theorem const_not_tendsto {c : ℝ} (hc : 0 < c) :
    ¬ Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
  intro h
  exact hc.ne' (tendsto_nhds_unique tendsto_const_nhds h)

/-- The identity has a fixed point above `0`. DERIVED: `1` the witness. -/
theorem id_not_noFixedAbove : ¬ ZoomStep.NoFixedAbove id := by
  rintro ⟨_, h⟩
  exact lt_irrefl _ (h 1 one_pos)

end MassGap.PlaneFlow

#print axioms MassGap.PlaneFlow.sum_card_inter
#print axioms MassGap.PlaneFlow.sum_blockExp
#print axioms MassGap.PlaneFlow.sum_blockExp_four
#print axioms MassGap.PlaneFlow.exp_P01_P01
#print axioms MassGap.PlaneFlow.exp_P01_P23
#print axioms MassGap.PlaneFlow.exp_P01_P02
#print axioms MassGap.PlaneFlow.step01_fst
#print axioms MassGap.PlaneFlow.step23_step01
#print axioms MassGap.PlaneFlow.step01_step23
#print axioms MassGap.PlaneFlow.window_step_id
#print axioms MassGap.PlaneFlow.iterate_window_step
#print axioms MassGap.PlaneFlow.orbit_mem_iff
#print axioms MassGap.PlaneFlow.diag_not_strip
#print axioms MassGap.PlaneFlow.const_zoomStepMap_id
#print axioms MassGap.PlaneFlow.const_not_tendsto
#print axioms MassGap.PlaneFlow.id_not_noFixedAbove
