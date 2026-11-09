import Mathlib
import MassGap.ApproxFlow
import MassGap.ExistenceFlow
import MassGap.ObserverFlow

/-!
# MassGap.FlowZero — flows of vanishing range, the fixed-step identity, and the interchange

`ApproxFlow.FlowKernelConvR hN2 Ws z r` asks, for every averaged composite `P`, members `s n` and
coefficients `c n` with the mixed reading `xL (mixKR (Ws (s n)) z r P) (c n) → kernC(P, P)` and the
flowed Gram reading `gForm (gramF (Ws (s n)) r) (c n) (c n) → kernC(P, P)`. This module places
families of configuration flows with vanishing range, proves that at each fixed step a member of
small enough range is the identity, proves that this fixed-step fact does not enter the kernels, and
states `FlowKernelConvR` as an ε-bound on lattice readings (`UniformFlowRead`).

## 1. The kernels read only the tail of a flow (proved)

* `fieldMap_congr`, `phi0_map_congr`, `mixLatC_congr`, `latSF_congr`: at a step `k` where two flows
  agree, every lattice reading of `Φ0` agrees.
* `mixKR_eq_of_eventually`, `gramF_eq_of_eventually`: two flows that agree at every large step have
  the same `mixKR` and the same `gramF` (both are `limUnder` along `ultra`, and `ultra ≤ atTop`).
* `splice W W' p`: the flow equal to `W'` at the steps `p k` and to `W` elsewhere.
  `flowKernelConvR_splice_iff`: replacing each member on a set of steps that is eventually empty
  leaves `FlowKernelConvR` unchanged.

## 2. Families of vanishing range (proved)

* `flatFam N s = ExistenceFlow.flatFlow (k ↦ ⌊s / a_k⌋₊)`, every `N`: physical reach
  `a_k · range_k ≤ 2s` at every step (`flatFam_reach`), `PhysRange (2s)` of `Φ0` (`flatFam_physRange`),
  `ClassMoments … 1 1` on `SymPlaqClass N` for `s > 0` (`flatFam_classMoments`).
* `apeFam c s = ObserverFlow.obsConfFlow c (k ↦ ⌊(s/a_k)²⌋₊) (k ↦ ⌊s/a_k⌋₊)`, `N = 2`: localised
  APE smearing with `⌊(s/a_k)²⌋₊` steps in boxes of half-width `⌊s/a_k⌋₊`; `PhysRange r` of `Φ0` at
  every `r > s ≥ 0` (`apeFam_physRange`). `ClassMoments` for it is not proved here.
* Fixed-step identity: `flatFam_V_of_lt` (`s < a_k`) and `apeFam_V_of_lt` (`0 ≤ s < a_k`): the
  member is the identity configuration map at step `k`. `flatFam_eventually_id`,
  `apeFam_eventually_id`: at each fixed `k`, eventually as `s → 0` (from above for `apeFam`) the
  member is the identity at `k`, so every lattice reading of the member at step `k` equals that of
  `ConfFlow.identity` exactly (`flatFam_latSF_eventually`, `apeFam_latSF_eventually`,
  `apeFam_mixLatC_eventually`).
* `small_steps_finite`: for `s > 0` the steps with `s < a_k` are eventually absent. With §1
  (`flowKernelConvR_splice_small_iff`): replacing every member `s > 0` at those steps by any flow
  (the identity among them) leaves `FlowKernelConvR` unchanged. The fixed-step identity is therefore
  not an input of `FlowKernelConvR`.

## 3. FlowKernelConvR as a lattice ε-bound (proved equivalent)

* Lattice sequences at step `k`: `kLat P k = sgn(P) · latC(ΘP ∪ P)` (the composite's z-normalised
  connected reading), `xLat W P Q k = sgn(P) · mixLatC(P, Q)` and `gLat W Q Q' k = latSF(ΘQ ∪ Q')`.
* `UniformFlowRead hN2 Ws z r`: for every `P` and `ε > 0` there are a member `s` and real coefficients
  `c` with, on a set of steps in `ultra`,
  `|xL (xLat (Ws s) P · k) c − kLat P k| ≤ ε` and `|gForm (gLat (Ws s) · · k) c c − kLat P k| ≤ ε`.
  `uniformFlowRead_of_atTop`: the same bound for all large `k` gives it.
* `flowKernelConv_iff_uniform` (abstract) and `flowKernelConvR_iff_uniform`: when the composite's
  readings converge along `ultra`, every member meets `MixConvF` and `UniformBoundF` of `Φ0`,
  `FlowKernelConvR hN2 Ws z r ↔ UniformFlowRead hN2 Ws z r`.

The target of the bound is the composite's own z-normalised reading `kLat`, not a reading of any
member.

## Evaluation of the fixed-step route (ARGUED where marked)

* PROVED: at fixed `k` the members of both families are the identity once `s < a_k`, so their lattice
  readings equal the identity flow's. PROVED: these steps are finitely many for each `s > 0`, and the
  kernels that `FlowKernelConvR` reads do not see them (§1, §2). The order of limits is
  `lim_{s→0} ultra-lim_k`; the fixed-step identity is `lim_k lim_{s→0}`, and nothing proved here
  relates the two. `UniformFlowRead` is `FlowKernelConvR` with each ultra-limit written as an ε-bound
  on the lattice readings at one member; it keeps the order `lim_s ultra-lim_k` (§3).
* ARGUED: the identity flow's readings are not `kLat`. `Φ0` reads a margin monomial's
  `SymPlaqClass` factor as `a_k⁻⁴ O ∘ V_k` with no vacuum subtraction, and other factors as `O ∘ V_k`;
  `kLat` reads `cField`, `z(k) · (op − ν_k(op))`. The mixed reading is connected through the
  composite's factor, but the Gram reading of a single plaquette factor carries
  `a_k⁻⁸ ν_k(O)²`, which a `k`-independent coefficient on the empty monomial cannot remove; with the
  floor `PlaquetteFloor.stateK_plaq_ge` it diverges. The identity flow fails `ClassMoments`
  (`PlaquetteFloor.not_classMoments_identity`, proved there), so `ApproxFlow.approxKFlow_iff` does not
  apply to it either.
* ARGUED: `flatFam` meets `ClassMoments` but its flowed fields are eventually constant
  (`ExistenceFlow.flatFlow_fieldMap`), so `gramF` has rank one and `FlowKernelConvR` at `flatFam`
  asks every composite vector to be a multiple of the vacuum. `apeFam` is the non-degenerate family
  (`N = 2`); `ClassMoments` for it is the open input `hU` of `ExistenceFlow`.
* What remains for `FlowKernelConvR` is `UniformFlowRead` at a family meeting `ClassMoments`,
  `PhysRange r`, `MixConvF` and `UniformBoundF` at every member. ARGUED: it is the leading term of the
  small-flow-time expansion (flowed field = bare composite + O(s) with z-renormalisation) holding
  at all large steps (`uniformFlowRead_of_atTop`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the empty range and the limit; `1` the unit bound of a floor and
the shift in `1/(n+1)`; `2` the colour count of `apeFam`, the two half-widths and the square; `3` the
range beyond the box; `1/6` the APE dominance bound; `4` the dimension.
-/

noncomputable section

namespace MassGap.FlowZero

open Filter
open scoped Topology

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.JointRP MassGap.CompositeLink
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.ApproxFlow

/-! ## 1. The kernels read only the tail of a flow -/

section Tail

variable {N : ℕ}

/-- **Flowed fields at a step depend only on the configuration map at that step.**
DERIVED: no numeral. -/
theorem fieldMap_congr {W W' : ConfFlow N} {k : ℕ} (h : W.V k = W'.V k)
    (O : LField (MassGap.SUN.SU N)) : W.fieldMap k O = W'.fieldMap k O :=
  Subtype.ext (ContinuousMap.ext fun U => by
    show O.1 (W.V k U) = O.1 (W'.V k U)
    rw [h])

/-- `Φ0 W` at step `k` is the class-scaled flowed field. DERIVED: no numeral. -/
theorem phi0_map (W : ConfFlow N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) :
    (Φ0 W).map k O = scaleField ((W.fieldMap k O).sub (sOn (SymPlaqClass N) (s0 N) k O))
      (zOn (SymPlaqClass N) k O) := rfl

/-- DERIVED: no numeral. -/
theorem phi0_map_congr {W W' : ConfFlow N} {k : ℕ} (h : W.V k = W'.V k) :
    (Φ0 W).map k = (Φ0 W').map k := by
  funext O
  rw [phi0_map, phi0_map, fieldMap_congr h]

/-- **The mixed lattice reading at a step depends only on the flow at that step.**
DERIVED: no numeral. -/
theorem mixLatC_congr (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) {W W' : ConfFlow N} {k : ℕ}
    (h : W.V k = W'.V k) (P : TMonoG C.Ix) (Q : Mono N) :
    mixLatC hN C (Φ0 W) τ k P Q = mixLatC hN C (Φ0 W') τ k P Q := by
  unfold mixLatC Flow.field
  rw [phi0_map_congr h]

/-- **The flowed lattice reading at a step depends only on the flow at that step.**
DERIVED: no numeral. -/
theorem latSF_congr (hN : N ≠ 0) {W W' : ConfFlow N} {k : ℕ} (h : W.V k = W'.V k) {ι : Type}
    [Fintype ι] (F : ι → SField N) : latSF hN (Φ0 W) k F = latSF hN (Φ0 W') k F := by
  unfold latSF Flow.field
  rw [phi0_map_congr h]

/-- **`limUnder` along `ultra` reads only the tail.** DERIVED: no numeral. -/
theorem limUnder_congr_ultra {f g : ℕ → ℝ} (h : ∀ᶠ k in atTop, f k = g k) :
    limUnder (ultra : Filter ℕ) f = limUnder (ultra : Filter ℕ) g := by
  unfold limUnder
  rw [Filter.map_congr (h.filter_mono ultra_le)]

/-- **Flows agreeing at every large step have the same mixed kernel.** DERIVED: `0` the plane. -/
theorem mixKR_eq_of_eventually (hN2 : 2 ≤ N) {W W' : ConfFlow N}
    (h : ∀ᶠ k in atTop, W.V k = W'.V k) (z : Chan → ℕ → ℝ) (r : ℝ) :
    mixKR hN2 W z r = mixKR hN2 W' z r := by
  funext P Q
  unfold mixKR mixKF mixKC
  congr 1
  exact limUnder_congr_ultra (h.mono fun k hk => mixLatC_congr _ _ _ hk _ _)

/-- **Flows agreeing at every large step have the same flowed kernel.** DERIVED: `0` the plane. -/
theorem gramF_eq_of_eventually (hN2 : 2 ≤ N) {W W' : ConfFlow N}
    (h : ∀ᶠ k in atTop, W.V k = W'.V k) (r : ℝ) :
    gramF hN2 W r = gramF hN2 W' r := by
  funext Q Q'
  exact limUnder_congr_ultra (h.mono fun k hk => latSF_congr _ hk _)

/-- **The splice**: `W'` at the steps `p k`, `W` elsewhere. DERIVED: no numeral. -/
def splice (W W' : ConfFlow N) (p : ℕ → Prop) [DecidablePred p] : ConfFlow N where
  V k := if p k then W'.V k else W.V k
  continuous_V k := by
    by_cases h : p k
    · simp only [h, ↓reduceIte]; exact W'.continuous_V k
    · simp only [h, ↓reduceIte]; exact W.continuous_V k
  gauge k g U := by
    by_cases h : p k
    · simp only [h, ↓reduceIte]; exact W'.gauge k g U
    · simp only [h, ↓reduceIte]; exact W.gauge k g U
  refl k τ U := by
    by_cases h : p k
    · simp only [h, ↓reduceIte]; exact W'.refl k τ U
    · simp only [h, ↓reduceIte]; exact W.refl k τ U
  range k := if p k then W'.range k else W.range k
  local_V k l := by
    by_cases h : p k
    · simp only [h, ↓reduceIte]; exact W'.local_V k l
    · simp only [h, ↓reduceIte]; exact W.local_V k l

/-- DERIVED: no numeral. -/
theorem splice_V_of_not {W W' : ConfFlow N} {p : ℕ → Prop} [DecidablePred p] {k : ℕ}
    (hk : ¬ p k) : (splice W W' p).V k = W.V k := if_neg hk

/-- **Replacing each member on an eventually empty set of steps leaves `FlowKernelConvR`
unchanged.** DERIVED: no numeral. -/
theorem flowKernelConvR_splice_iff {S : Type} (hN2 : 2 ≤ N) (Ws W's : S → ConfFlow N)
    (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)] (hp : ∀ s, ∀ᶠ k in atTop, ¬ p s k)
    (z : Chan → ℕ → ℝ) (r : ℝ) :
    FlowKernelConvR hN2 (fun s => splice (Ws s) (W's s) (p s)) z r ↔ FlowKernelConvR hN2 Ws z r := by
  have hev : ∀ s, ∀ᶠ k in atTop, (splice (Ws s) (W's s) (p s)).V k = (Ws s).V k :=
    fun s => (hp s).mono fun k hk => splice_V_of_not hk
  have e1 : (fun s => mixKR hN2 (splice (Ws s) (W's s) (p s)) z r)
      = fun s => mixKR hN2 (Ws s) z r := funext fun s => mixKR_eq_of_eventually hN2 (hev s) z r
  have e2 : (fun s => gramF hN2 (splice (Ws s) (W's s) (p s)) r)
      = fun s => gramF hN2 (Ws s) r := funext fun s => gramF_eq_of_eventually hN2 (hev s) r
  show FlowKernelConv _ (fun s => mixKR hN2 (splice (Ws s) (W's s) (p s)) z r)
      (fun s => gramF hN2 (splice (Ws s) (W's s) (p s)) r)
    ↔ FlowKernelConv _ (fun s => mixKR hN2 (Ws s) z r) (fun s => gramF hN2 (Ws s) r)
  rw [e1, e2]

end Tail

/-! ## 2. Families of vanishing range -/

section Families

variable {N : ℕ}

/-- **The flat map at half-width `0` is the identity**: no link has both ends in the one-site box.
DERIVED: `0` the half-width; `1` the lattice step. -/
theorem flatV_zero (U : Cfg N) : ExistenceFlow.flatV 0 U = U := by
  funext l
  unfold ExistenceFlow.flatV
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have a := h1 l.1
  have b := h2 l.1
  have e : ishift l.1 l.2 l.1 = l.2 l.1 + 1 := by simp [ishift]
  rw [e] at b
  simp only [Nat.cast_zero] at a b
  have a0 : l.2 l.1 = 0 := abs_nonpos_iff.mp a
  rw [a0, zero_add, abs_one] at b
  exact absurd b (by norm_num)

/-- **The flat family**: `flatFlow` at half-width `⌊s / a_k⌋₊`. DERIVED: no numeral. -/
def flatFam (N : ℕ) (s : ℝ) : ConfFlow N :=
  ExistenceFlow.flatFlow (fun k => ⌊s / dySpacing N k⌋₊)

/-- **At a fixed step, a flat member of range below the spacing is the identity.**
DERIVED: `1` the floor threshold. -/
theorem flatFam_V_of_lt (hN : N ≠ 0) {s : ℝ} {k : ℕ} (hs : s < dySpacing N k) :
    (flatFam N s).V k = id := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hL : ⌊s / dySpacing N k⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one ha).mpr hs)
  funext U
  show ExistenceFlow.flatV ⌊s / dySpacing N k⌋₊ U = U
  rw [hL]
  exact flatV_zero U

/-- **The flat family's physical reach is at most `2s`** at every step. DERIVED: `2` the two
half-widths. -/
theorem flatFam_reach (hN : N ≠ 0) {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    dySpacing N k * ((flatFam N s).range k : ℝ) ≤ 2 * s := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hfl : (⌊s / dySpacing N k⌋₊ : ℝ) ≤ s / dySpacing N k := Nat.floor_le (div_nonneg hs ha.le)
  show dySpacing N k * (((2 * ⌊s / dySpacing N k⌋₊ : ℕ)) : ℝ) ≤ 2 * s
  push_cast
  have e : dySpacing N k * (s / dySpacing N k) = s := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]

/-- **`PhysRange (2s)` of the flat member's observer flow.** DERIVED: `2` the two half-widths. -/
theorem flatFam_physRange (hN : N ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (Φ0 (flatFam N s)).PhysRange (2 * s) :=
  Eventually.of_forall fun k => flatFam_reach hN hs k

/-- **`ClassMoments` at every flat member of positive range** (`ExistenceFlow.classMoments_flatFlow`).
DERIVED: `1` the strength and the constant; `0` the sign of `s`. -/
theorem flatFam_classMoments (hN : N ≠ 0) {s : ℝ} (hs : 0 < s) :
    ClassMoments hN (flatFam N s) (SymPlaqClass N) 1 1 := by
  have h0 : Tendsto (dySpacing N) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_dySpacing N,
      Eventually.of_forall fun k => Set.mem_Ioi.mpr (dySpacing_pos (one_le_of_ne_zero hN) k)⟩
  have hi : Tendsto (fun k => (dySpacing N k)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp h0
  have hd : Tendsto (fun k => s / dySpacing N k) atTop atTop := by
    simpa only [div_eq_mul_inv] using hi.const_mul_atTop hs
  exact ExistenceFlow.classMoments_flatFlow hN (tendsto_nat_floor_atTop.comp hd)

/-- **At each fixed step the flat member is eventually the identity as `s → 0`.**
DERIVED: `0` the limit. -/
theorem flatFam_eventually_id (hN : N ≠ 0) (k : ℕ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), (flatFam N s).V k = (ConfFlow.identity N).V k :=
  (eventually_lt_nhds (dySpacing_pos (one_le_of_ne_zero hN) k)).mono fun _ hs =>
    flatFam_V_of_lt hN hs

/-- **At each fixed step the flat member's flowed readings are eventually, as `s → 0`, exactly the
identity flow's.** DERIVED: `0` the limit. -/
theorem flatFam_latSF_eventually (hN : N ≠ 0) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    ∀ᶠ s in 𝓝 (0 : ℝ), latSF hN (Φ0 (flatFam N s)) k F = latSF hN (Φ0 (ConfFlow.identity N)) k F :=
  (flatFam_eventually_id hN k).mono fun _ hs => latSF_congr hN hs F

/-- **The APE family** (`N = 2`): `⌊(s/a_k)²⌋₊` localised APE steps in boxes of half-width
`⌊s/a_k⌋₊`. DERIVED: `2` the rank and the square; `1/6` the dominance bound. -/
def apeFam (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 6) (s : ℝ) : ConfFlow 2 :=
  ObserverFlow.obsConfFlow c hc0 hc (fun k => ⌊(s / dySpacing 2 k) ^ 2⌋₊)
    (fun k => ⌊s / dySpacing 2 k⌋₊)

/-- **At a fixed step, an APE member with `0 ≤ s < a_k` is the identity** (no smearing step).
DERIVED: `0` the step count; `1` the floor threshold; `2` the rank and the square; `1/6` the dominance
bound of `apeFam`. -/
theorem apeFam_V_of_lt {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {s : ℝ} {k : ℕ} (hs0 : 0 ≤ s)
    (hs : s < dySpacing 2 k) : (apeFam c hc0 hc s).V k = id := by
  have ha := dySpacing_pos (by norm_num : 1 ≤ 2) k
  have h1 : s / dySpacing 2 k < 1 := (div_lt_one ha).mpr hs
  have h0 : 0 ≤ s / dySpacing 2 k := div_nonneg hs0 ha.le
  have hn : ⌊(s / dySpacing 2 k) ^ 2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by nlinarith)
  funext U
  show ObserverFlow.obsFlow c hc0 hc ⌊(s / dySpacing 2 k) ^ 2⌋₊ ⌊s / dySpacing 2 k⌋₊ U = U
  rw [hn]
  rfl

/-- **`PhysRange r` of the APE member's observer flow at every `r > s ≥ 0`**: the reach is
`a_k (⌊s/a_k⌋₊ + 3) ≤ s + 3 a_k`. DERIVED: `3` the range beyond the box; `2` the rank; `1/6` the dominance bound of `apeFam`. -/
theorem apeFam_physRange {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) {s r : ℝ} (hs0 : 0 ≤ s)
    (hr : s < r) : (Φ0 (apeFam c hc0 hc s)).PhysRange r := by
  have hev : ∀ᶠ k in atTop, dySpacing 2 k < (r - s) / 3 :=
    (tendsto_dySpacing 2).eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hev] with k hk
  have ha := dySpacing_pos (by norm_num : 1 ≤ 2) k
  have hfl : (⌊s / dySpacing 2 k⌋₊ : ℝ) ≤ s / dySpacing 2 k := Nat.floor_le (div_nonneg hs0 ha.le)
  show dySpacing 2 k * (((⌊s / dySpacing 2 k⌋₊ + 3 : ℕ)) : ℝ) ≤ r
  push_cast
  have e : dySpacing 2 k * (s / dySpacing 2 k) = s := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]

/-- **At each fixed step the APE member is eventually the identity as `s → 0⁺`.**
DERIVED: `0` the limit; `2` the rank; `1/6` the dominance bound of `apeFam`. -/
theorem apeFam_eventually_id {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (k : ℕ) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ), (apeFam c hc0 hc s).V k = (ConfFlow.identity 2).V k := by
  have ha := dySpacing_pos (by norm_num : 1 ≤ 2) k
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds ha)] with s hs0 hs
  exact apeFam_V_of_lt hc0 hc (Set.mem_Ici.mp hs0) hs

/-- **At each fixed step the APE member's flowed readings are eventually, as `s → 0⁺`, exactly the
identity flow's.** DERIVED: `0` the limit; `2` the rank; `1/6` the dominance bound of `apeFam`. -/
theorem apeFam_latSF_eventually {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (k : ℕ) {ι : Type}
    [Fintype ι] (F : ι → SField 2) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ), latSF (by norm_num) (Φ0 (apeFam c hc0 hc s)) k F
      = latSF (by norm_num) (Φ0 (ConfFlow.identity 2)) k F :=
  (apeFam_eventually_id hc0 hc k).mono fun _ hs => latSF_congr _ hs F

/-- **The same for the composites' mixed readings.** DERIVED: `0` the limit; `2` the rank; `1/6` the
dominance bound of `apeFam`. -/
theorem apeFam_mixLatC_eventually {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (k : ℕ)
    (C : Composites 2) (τ : Fin 4) (P : TMonoG C.Ix) (Q : Mono 2) :
    ∀ᶠ s in 𝓝[≥] (0 : ℝ), mixLatC (by norm_num) C (Φ0 (apeFam c hc0 hc s)) τ k P Q
      = mixLatC (by norm_num) C (Φ0 (ConfFlow.identity 2)) τ k P Q :=
  (apeFam_eventually_id hc0 hc k).mono fun _ hs => mixLatC_congr _ C τ hs P Q

/-- **For `s > 0` the identity steps are eventually absent**: eventually `a_k ≤ s`.
DERIVED: `0` the sign of `s`. -/
theorem small_steps_finite (N : ℕ) {s : ℝ} (hs : 0 < s) : ∀ᶠ k in atTop, ¬ s < dySpacing N k :=
  ((tendsto_dySpacing N).eventually (eventually_lt_nhds hs)).mono fun _ hk => not_lt.mpr hk.le

/-- **The steps where a member of positive range is the identity do not enter `FlowKernelConvR`**:
replacing every member `s > 0` at the steps `s < a_k` by any flow leaves it unchanged.
DERIVED: `0` the sign of `s`. -/
theorem flowKernelConvR_splice_small_iff (hN2 : 2 ≤ N) (Ws W's : {s : ℝ // 0 < s} → ConfFlow N)
    (z : Chan → ℕ → ℝ) (r : ℝ) :
    FlowKernelConvR hN2
        (fun s => splice (Ws s) (W's s) (fun k => (s : ℝ) < dySpacing N k)) z r
      ↔ FlowKernelConvR hN2 Ws z r :=
  flowKernelConvR_splice_iff hN2 Ws W's _ (fun s => small_steps_finite N s.2) z r

end Families

/-! ## 3. The interchange statement -/

section Generic

variable {I M S : Type}

/-- **The real combination of convergent sequences converges.** DERIVED: no numeral. -/
theorem tendsto_xL {L : Filter ℕ} {x : M → ℕ → ℝ} {X : M → ℝ}
    (hx : ∀ Q, Tendsto (x Q) L (𝓝 (X Q))) (c : M →₀ ℝ) :
    Tendsto (fun k => xL (fun Q => x Q k) c) L (𝓝 (xL X c)) := by
  unfold xL Finsupp.sum
  exact tendsto_finsetSum _ fun Q _ => (hx Q).const_mul (c Q)

/-- **The form of convergent kernels converges.** DERIVED: no numeral. -/
theorem tendsto_gForm {L : Filter ℕ} {g : M → M → ℕ → ℝ} {G : M → M → ℝ}
    (hg : ∀ Q Q', Tendsto (g Q Q') L (𝓝 (G Q Q'))) (c d : M →₀ ℝ) :
    Tendsto (fun k => gForm (fun Q Q' => g Q Q' k) c d) L (𝓝 (gForm G c d)) := by
  unfold gForm Finsupp.sum
  exact tendsto_finsetSum _ fun Q _ => tendsto_finsetSum _ fun Q' _ =>
    (hg Q Q').const_mul (c Q * d Q')

/-- **`FlowKernelConv` is the uniform lattice bound** when every kernel is the limit along `L` of
its lattice sequence: for every `P` and `ε > 0`, a member and coefficients whose lattice readings are
within `ε` of the composite's lattice reading on a set of steps in `L`.

DERIVED: `1` the shift in `1/(n+1)`; `0` the limit and the sign of `ε`. -/
theorem flowKernelConv_iff_uniform {Kc : I → I → ℝ} {Xs : S → I → M → ℝ} {Gs : S → M → M → ℝ}
    (kk : I → ℕ → ℝ) (xk : S → I → M → ℕ → ℝ) (gk : S → M → M → ℕ → ℝ) (L : Filter ℕ) [L.NeBot]
    (hk : ∀ P, Tendsto (kk P) L (𝓝 (Kc P P)))
    (hx : ∀ s P Q, Tendsto (xk s P Q) L (𝓝 (Xs s P Q)))
    (hg : ∀ s Q Q', Tendsto (gk s Q Q') L (𝓝 (Gs s Q Q'))) :
    FlowKernelConv Kc Xs Gs ↔ ∀ (P : I) (ε : ℝ), 0 < ε → ∃ (s : S) (c : M →₀ ℝ), ∀ᶠ k in L,
      |xL (fun Q => xk s P Q k) c - kk P k| ≤ ε
        ∧ |gForm (fun Q Q' => gk s Q Q' k) c c - kk P k| ≤ ε := by
  constructor
  · intro h P ε hε
    obtain ⟨s, c, hX, hG⟩ := h P
    have h1 : ∀ᶠ n in atTop, |xL (Xs (s n) P) (c n) - Kc P P| < ε := by
      have t := (hX.sub_const (Kc P P)).abs
      rw [sub_self, abs_zero] at t
      exact t.eventually (eventually_lt_nhds hε)
    have h2 : ∀ᶠ n in atTop, |gForm (Gs (s n)) (c n) (c n) - Kc P P| < ε := by
      have t := (hG.sub_const (Kc P P)).abs
      rw [sub_self, abs_zero] at t
      exact t.eventually (eventually_lt_nhds hε)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    refine ⟨s n, c n, ?_⟩
    have t1 := ((tendsto_xL (hx (s n) P) (c n)).sub (hk P)).abs
    have t2 := ((tendsto_gForm (hg (s n)) (c n) (c n)).sub (hk P)).abs
    filter_upwards [t1.eventually (eventually_lt_nhds hn1),
      t2.eventually (eventually_lt_nhds hn2)] with k hk1 hk2
    exact ⟨hk1.le, hk2.le⟩
  · intro h P
    choose s c hc using fun n : ℕ => h P (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hb1 : ∀ n, |xL (Xs (s n) P) (c n) - Kc P P| ≤ 1 / ((n : ℝ) + 1) := fun n =>
      le_of_tendsto ((tendsto_xL (hx (s n) P) (c n)).sub (hk P)).abs
        ((hc n).mono fun _ hk' => hk'.1)
    have hb2 : ∀ n, |gForm (Gs (s n)) (c n) (c n) - Kc P P| ≤ 1 / ((n : ℝ) + 1) := fun n =>
      le_of_tendsto ((tendsto_gForm (hg (s n)) (c n) (c n)).sub (hk P)).abs
        ((hc n).mono fun _ hk' => hk'.2)
    have hlo : Tendsto (fun n : ℕ => Kc P P - 1 / ((n : ℝ) + 1)) atTop (𝓝 (Kc P P)) := by
      simpa using (tendsto_const_nhds (x := Kc P P)).sub tendsto_one_div_add_atTop_nhds_zero_nat
    have hhi : Tendsto (fun n : ℕ => Kc P P + 1 / ((n : ℝ) + 1)) atTop (𝓝 (Kc P P)) := by
      simpa using (tendsto_const_nhds (x := Kc P P)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have sq : ∀ u : ℕ → ℝ, (∀ n, |u n - Kc P P| ≤ 1 / ((n : ℝ) + 1)) →
        Tendsto u atTop (𝓝 (Kc P P)) := fun u hu =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
        (fun n => by linarith [(abs_le.mp (hu n)).1]) (fun n => by linarith [(abs_le.mp (hu n)).2])
    exact ⟨s, c, sq _ hb1, sq _ hb2⟩

end Generic

section Real

variable {N : ℕ}

/-- **The composite's z-normalised lattice reading** `sgn(P) · latC(ΘP ∪ P)` at step `k`; its
`limUnder` along `ultra` is `kernC(P, P)`. DERIVED: `0` the plane. -/
def kLat (hN2 : 2 ≤ N) (z : Chan → ℕ → ℝ) (P : TSepG (CbR N z).Ix 0) (k : ℕ) : ℝ :=
  sgnC (CbR N z) 0 P.1 * latC (ne_zero_of_two_le hN2) (CbR N z) k (pairC (CbR N z) 0 P.1 P.1)

/-- **The member's mixed lattice reading** `sgn(P) · mixLatC(P, Q)` at step `k`; its `limUnder` is
`mixKR W z r P Q`. DERIVED: `0` the plane. -/
def xLat (hN2 : 2 ≤ N) (W : ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) (P : TSepG (CbR N z).Ix 0)
    (Q : MarginMono N 0 r) (k : ℕ) : ℝ :=
  sgnC (CbR N z) 0 P.1 * mixLatC (ne_zero_of_two_le hN2) (CbR N z) (Φ0 W) 0 k P.1 Q.1

/-- **The member's flowed lattice reading** `latSF(ΘQ ∪ Q')` at step `k`; its `limUnder` is
`gramF W r Q Q'`. DERIVED: `0` the plane. -/
def gLat (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) (Q Q' : MarginMono N 0 r) (k : ℕ) : ℝ :=
  latSF (ne_zero_of_two_le hN2) (Φ0 W) k (pairFam 0 Q.1 Q'.1)

/-- **`FlowKernelConvR` read on the lattice.** For every averaged composite `P` and `ε > 0`, a
member `s` and real coefficients `c` on the margin monomials whose mixed and Gram lattice readings are
within `ε` of the composite's z-normalised lattice reading `kLat P k`, on a set of steps in `ultra`.
The set of steps may depend on `s`, `c` and `ε`; `uniformFlowRead_of_atTop` gives it from a bound at
all large steps. The target of the bound is `kLat`, not a reading of any member.

DERIVED: `0` the sign of `ε` and the plane. -/
def UniformFlowRead {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) :
    Prop :=
  ∀ (P : TSepG (CbR N z).Ix 0) (ε : ℝ), 0 < ε → ∃ (s : S) (c : MarginMono N 0 r →₀ ℝ),
    ∀ᶠ k in (ultra : Filter ℕ),
      |xL (fun Q => xLat hN2 (Ws s) z r P Q k) c - kLat hN2 z P k| ≤ ε
        ∧ |gForm (fun Q Q' => gLat hN2 (Ws s) r Q Q' k) c c - kLat hN2 z P k| ≤ ε

/-- **The bound at all large steps gives `UniformFlowRead`** (`ultra ≤ atTop`).
DERIVED: `0` the sign of `ε` and the plane. -/
theorem uniformFlowRead_of_atTop {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N)
    (z : Chan → ℕ → ℝ) (r : ℝ)
    (h : ∀ (P : TSepG (CbR N z).Ix 0) (ε : ℝ), 0 < ε → ∃ (s : S) (c : MarginMono N 0 r →₀ ℝ),
      ∀ᶠ k in atTop,
        |xL (fun Q => xLat hN2 (Ws s) z r P Q k) c - kLat hN2 z P k| ≤ ε
          ∧ |gForm (fun Q Q' => gLat hN2 (Ws s) r Q Q' k) c c - kLat hN2 z P k| ≤ ε) :
    UniformFlowRead hN2 Ws z r := fun P ε hε => by
  obtain ⟨s, c, hc⟩ := h P ε hε
  exact ⟨s, c, hc.filter_mono ultra_le⟩

/-- **`FlowKernelConvR` is the interchange statement**, when the composite's two-point readings
converge along `ultra` (`hK`, which `ConvC` gives on admissible families), and every member meets
`MixConvF` and `UniformBoundF` of `Φ0`.

DERIVED: `0` the plane. -/
theorem flowKernelConvR_iff_uniform {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N)
    (z : Chan → ℕ → ℝ) (r : ℝ)
    (hK : ∀ P : TSepG (CbR N z).Ix 0, ∃ x, Tendsto
      (fun k => latC (ne_zero_of_two_le hN2) (CbR N z) k (pairC (CbR N z) 0 P.1 P.1))
      (ultra : Filter ℕ) (𝓝 x))
    (hMC : ∀ s, MixConvF hN2 (Ws s) (fR N) (bR N) z r)
    (hB : ∀ s, UniformBoundF (ne_zero_of_two_le hN2) (Φ0 (Ws s))) :
    FlowKernelConvR hN2 Ws z r ↔ UniformFlowRead hN2 Ws z r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact flowKernelConv_iff_uniform (kLat hN2 z) (fun s => xLat hN2 (Ws s) z r)
    (fun s => gLat hN2 (Ws s) r) (ultra : Filter ℕ)
    (fun P => (tendsto_nhds_limUnder (hK P)).const_mul _)
    (fun s P Q => (tendsto_nhds_limUnder (hMC s P Q)).const_mul _)
    (fun s Q Q' => tendsto_contSF (ne_zero_of_two_le hN2) (Φ0 (Ws s)) (hB s) _)

end Real

end MassGap.FlowZero

end

#print axioms MassGap.FlowZero.fieldMap_congr
#print axioms MassGap.FlowZero.phi0_map_congr
#print axioms MassGap.FlowZero.mixLatC_congr
#print axioms MassGap.FlowZero.latSF_congr
#print axioms MassGap.FlowZero.limUnder_congr_ultra
#print axioms MassGap.FlowZero.mixKR_eq_of_eventually
#print axioms MassGap.FlowZero.gramF_eq_of_eventually
#print axioms MassGap.FlowZero.splice
#print axioms MassGap.FlowZero.flowKernelConvR_splice_iff
#print axioms MassGap.FlowZero.flatV_zero
#print axioms MassGap.FlowZero.flatFam_V_of_lt
#print axioms MassGap.FlowZero.flatFam_reach
#print axioms MassGap.FlowZero.flatFam_physRange
#print axioms MassGap.FlowZero.flatFam_classMoments
#print axioms MassGap.FlowZero.flatFam_eventually_id
#print axioms MassGap.FlowZero.flatFam_latSF_eventually
#print axioms MassGap.FlowZero.apeFam_V_of_lt
#print axioms MassGap.FlowZero.apeFam_physRange
#print axioms MassGap.FlowZero.apeFam_eventually_id
#print axioms MassGap.FlowZero.apeFam_latSF_eventually
#print axioms MassGap.FlowZero.apeFam_mixLatC_eventually
#print axioms MassGap.FlowZero.small_steps_finite
#print axioms MassGap.FlowZero.flowKernelConvR_splice_small_iff
#print axioms MassGap.FlowZero.tendsto_xL
#print axioms MassGap.FlowZero.tendsto_gForm
#print axioms MassGap.FlowZero.flowKernelConv_iff_uniform
#print axioms MassGap.FlowZero.uniformFlowRead_of_atTop
#print axioms MassGap.FlowZero.flowKernelConvR_iff_uniform
