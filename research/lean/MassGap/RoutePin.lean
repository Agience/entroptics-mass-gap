import Mathlib
import MassGap.ProxyCov

/-!
# MassGap.RoutePin — the coefficients' parity on the route and the range of the route flow

`ProxyCov.gapRead_far_of_range` carries a one-sign reflected gap read from one gap to every larger one
under two inputs beyond `ExpandLim` and `ConvC`: the coefficients' parity `ProxyCov.CfParity cf` and the
range condition (for all small `s`, the flow at `s` has physical range eventually below the margin of the
test function). This module adds the parity to the bundle and proves the range condition at the route
family `ObserverFlowSUN.sunFam`. Declarations are in the namespace `MassGap.RoutePin`.

## 1. The range of the route flow (proved)

* `sunFam_range_le`, `sunFam_range_gt`: at every step, `s + 2 a_k < a_k · range_k(sunFam s) ≤ s + 3 a_k`
  (`s ≥ 0` for the upper bound). The range of `ObserverFlowSUN.sunFam … s` is `⌊s/a_k⌋₊ + 3`
  (`ObserverFlowSUN.obsConfFlowN`).
* `RangeBelow Wf d`: the range condition of `gapRead_far_of_range` at the margin `d`.
* `sunFam_range_small`: the family `s ↦ sunFam … s` meets `RangeBelow` at every margin `d > 0`. For
  `s ∈ (0, d)` the physical range is eventually at most `(s + d)/2`, since `a_k → 0`.
* `rangeBelow_const_iff` (load test): the constant flow `Wf ≡ sunFam … s₀`, `s₀ ≥ 0`, meets `RangeBelow`
  at `d` exactly when `s₀ < d`. The condition is not met by every flow; it is met by the route family
  because its range is tied to the scale `s`.

## 2. The coefficients' parity (added, not discharged)

Projecting `cf` onto its same-sign part is not shown to preserve `ExpandLim`, so `CfParity` is not
discharged by projecting. Write the proxy as `Y = A + B`, `A` its same-sign part, `B` the rest. The
state is reflection invariant and the composite readings are reflection covariant, so the reading at a
reflected family forces to zero the terms with an odd number of `B` factors, and only those; a term with
two `B` factors is a two-point reading of `B` with itself, which no reflection identity removes.
`projection_load_bearing` is the abstract model (not a lattice one): on `ℝ²` with the dot product and
`θ = diag(1, −1)`, the reading is `θ`-invariant, `Y = (1, 1)` has same-sign part `A = (1, 0)`, and the
two-point readings are `2` and `1`: the projection changes the reading by `⟪B, B⟫ = 1`. That the lattice
term `⟪B, B⟫` stays away from `0` is not shown.

So the parity is an added input:

* `CoreFieldsAt`: the fields of `ExpandMatch.CoreInputsAlongWAM` after the existentials, at given data.
* `CoreInputsAlongWAMP N βs`: `CoreInputsAlongWAM` with `CfParity cf` added on the bundle's `cf`.
  `coreWAM_of_coreWAMP` forgets it; `clayStatementOf_of_apertureMatchP` is the capstone at the pinned
  bundle. The capstone's chain does not read `CfParity` (it holds from `CoreInputsAlongWAM`, so it adds
  nothing over `ExpandMatch.clayStatementOf_of_apertureMatch`); the parity is carried for the gap read of
  §3, whose copy at the bundle is not made (§4).
* `coreWAMP_of_cfParity`, `coreWAMP_of_cfScaled`, `coreWAMP_of_cfLead`: the fields at any parity-pinned
  `cf`, in particular at a one-sign leading-logarithm family `FlowChoice.cfScaled κ γ` and at
  `FlowChoice.cfLead`, give the pinned bundle (`ProxyCov.cfParity_cfScaled`, `ProxyCov.cfParity_cfLead`).
  No bundle witness exists in the repository at any `cf`.

## 3. The gap read on the route flow (proved)

* `gapRead_far_sunFam`: on `Wf = sunFam …`, under `ExpandLim`, `ConvC` and `CfParity`, for a combination of
  one reflection sign and a positive-time `g`, non-degeneracy at one physical gap `t₁` gives the floor
  `U · min(δ/U, 1)^{t/t₁}` at every larger resolved gap `t`, `U = |contRead c (θg) g| + δ`. No membership
  and no range hypothesis: the margin of `g` is read from `PosT g`, the range from `sunFam_range_small`.
* `gapRead_dyadic_sunFam`: `GapRead` at one dyadic gap `j₁ a₀/2^{k₀}` gives `GapRead` at every larger
  dyadic gap `j a₀/2^{k₀}` (`ProxyCov.rep_dyadic`). `gapRead_dyadic_sunFam_lead`: the same at
  `cf = cfLead`, with `CfParity` discharged.

## 4. What remains

* `CfParity` on the bundle's `cf` is an input (§2); every leading-logarithm family of one sign meets it.
* `ExpandLim` and `ConvC` at `sunFam` and `GapRead` at one gap, per combination of one sign, are inputs.
  No `(Wf, cf)` in the repository is shown to meet `ExpandLim`; at `cfLead` (unit coefficients, no log
  exponent, no mixing) it is not shown at any flow, so `gapRead_dyadic_sunFam_lead` is not known to be
  non-vacuous.
* §3 is stated along `dySpacing`, the coupling `dyBeta`; the bundle's fields are the copies at `cpl βs`.
  The copy of `ProxyCov` at `cpl βs` is not made.
* The bundle's `Wf` is existential: that it is `sunFam …` is not a field, so `sunFam_range_small` does not
  reach the bundle.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `3` the range of `obsConfFlowN` beyond the box and the factor of the upper bound;
`2` the factor of the lower bound (`3 − 1`, the floor's defect `1`) and the midpoint `(s + d)/2`; `1` the
floor's defect and the least `N` of the spacing; `0` the limit point, the plane and the signs; `2` the
least rank; `12` as in `ObserverFlowSUN.sunFam`; `1`, `0` the coordinates, `2`, `1` the readings and `−1`
the electric sign of the abstract model; `δ`, `U`, `t₁`, `t`,
`j₁`, `j`, `k₀`, `s₀`, `d` reads or hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.RoutePin

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
  MassGap.CompositesBuild MassGap.MultiScaleAll MassGap.CompositesRen MassGap.ApproxFromExpand
  MassGap.NondegFromProxy MassGap.ClayData MassGap.ReflAvg MassGap.ObserverFlowSUN MassGap.ProxyCov

variable {N : ℕ}

/-! ## 1. The range of the route flow -/

/-- The physical range of `sunFam … s` at step `k` is at most `s + 3 a_k`. DERIVED: `3` the range beyond
the box; `1` the least `N` of the spacing; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem sunFam_range_le (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    {s : ℝ} (hs0 : 0 ≤ s) (k : ℕ) :
    dySpacing N k * ((sunFam hN c hc0 hc s).range k : ℝ) ≤ s + 3 * dySpacing N k := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hfl : (⌊s / dySpacing N k⌋₊ : ℝ) ≤ s / dySpacing N k := Nat.floor_le (div_nonneg hs0 ha.le)
  show dySpacing N k * (((⌊s / dySpacing N k⌋₊ + 3 : ℕ)) : ℝ) ≤ s + 3 * dySpacing N k
  push_cast
  have e : dySpacing N k * (s / dySpacing N k) = s := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]

/-- The physical range of `sunFam … s` at step `k` exceeds `s + 2 a_k`. DERIVED: `3` the range beyond
the box; `1` the floor's defect and the least `N` of the spacing; `2 = 3 − 1`; `12 = 2 · 6` the coupling
bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem sunFam_range_gt (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (s : ℝ) (k : ℕ) :
    s + 2 * dySpacing N k < dySpacing N k * ((sunFam hN c hc0 hc s).range k : ℝ) := by
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hfl : s / dySpacing N k < (⌊s / dySpacing N k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  show s + 2 * dySpacing N k < dySpacing N k * (((⌊s / dySpacing N k⌋₊ + 3 : ℕ)) : ℝ)
  push_cast
  have e : dySpacing N k * (s / dySpacing N k) = s := by field_simp
  nlinarith [mul_lt_mul_of_pos_left hfl ha]

/-- The range condition of `ProxyCov.gapRead_far_of_range` at the margin `d`: for all small `s`, the
flow at `s` has physical range eventually at most some `r < d`. DERIVED: `0` the limit point. -/
def RangeBelow (Wf : ℝ → ConfFlow N) (d : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ r, r < d ∧ ∀ᶠ k in atTop, dySpacing N k * ((Wf s).range k : ℝ) ≤ r

/-- The route family meets the range condition at every positive margin. DERIVED: `0` the limit point;
`2` the midpoint; `3` the factor of the upper bound; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem sunFam_range_small (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    {d : ℝ} (hd : 0 < d) : RangeBelow (sunFam hN c hc0 hc) d := by
  filter_upwards [Ioo_mem_nhdsGT hd] with s hs
  refine ⟨(s + d) / 2, by linarith [hs.2], ?_⟩
  have hev : ∀ᶠ k in atTop, dySpacing N k < ((s + d) / 2 - s) / 3 :=
    (tendsto_dySpacing N).eventually (eventually_lt_nhds (by linarith [hs.2]))
  filter_upwards [hev] with k hk
  have h := sunFam_range_le hN hc0 hc hs.1.le k
  linarith

/-- The constant flow `Wf ≡ sunFam … s₀`, `s₀ ≥ 0`, meets the range condition at `d` exactly when
`s₀ < d`. DERIVED: `0` the limit point and the sign of `s₀`; `2` the midpoint and the lower bound's
factor; `3` the upper bound's factor; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem rangeBelow_const_iff (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} (hs0 : 0 ≤ s₀) {d : ℝ} :
    RangeBelow (fun _ => sunFam hN c hc0 hc s₀) d ↔ s₀ < d := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    obtain ⟨_, r, hr, hk⟩ := h.exists
    obtain ⟨k, hk⟩ := hk.exists
    have hk' : dySpacing N k * ((sunFam hN c hc0 hc s₀).range k : ℝ) ≤ r := hk
    have h1 := sunFam_range_gt hN hc0 hc s₀ k
    have ha := dySpacing_pos (by omega : 1 ≤ N) k
    linarith
  · intro h
    refine Eventually.of_forall fun _ => ⟨(s₀ + d) / 2, by linarith, ?_⟩
    have hev : ∀ᶠ k in atTop, dySpacing N k < ((s₀ + d) / 2 - s₀) / 3 :=
      (tendsto_dySpacing N).eventually (eventually_lt_nhds (by linarith))
    filter_upwards [hev] with k hk
    have h2 := sunFam_range_le hN hc0 hc hs0 k
    show dySpacing N k * ((sunFam hN c hc0 hc s₀).range k : ℝ) ≤ (s₀ + d) / 2
    linarith

/-! ## 2. The coefficients' parity -/

/-- A reflection-invariant reading does not fix the two-point reading under the projection onto the
same-sign part: module docstring, §2. An abstract model, not a lattice one. DERIVED: `1`, `0` the coordinates; `2`, `1` the
readings; `−1` the electric sign. -/
theorem projection_load_bearing :
    (∀ x y : ℝ × ℝ, ExpandMatch.dotF (thetaE x) (thetaE y) = ExpandMatch.dotF x y)
      ∧ thetaE ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ))
      ∧ thetaE ((0 : ℝ), (1 : ℝ)) = -((0 : ℝ), (1 : ℝ))
      ∧ ExpandMatch.dotF ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (1 : ℝ)) = 2
      ∧ ExpandMatch.dotF ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) = 1 := by
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · show ExpandMatch.dotF (x.1, -x.2) (y.1, -y.2) = _
    simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    ring
  · show ((1 : ℝ), -(0 : ℝ)) = _
    rw [neg_zero]
  · show ((0 : ℝ), -(1 : ℝ)) = _
    rw [Prod.neg_mk, neg_zero]
  · simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    norm_num
  · simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    norm_num

end MassGap.RoutePin

end

noncomputable section

namespace MassGap.RoutePin

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ScaleLightCone (ZoomSettlesUV)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- The fields of `ExpandMatch.CoreInputsAlongWAM` after its existentials, at given data. DERIVED: `0`
the sign of `b`. -/
def CoreFieldsAt (βs : ℕ → ℝ) (W : ConfFlow N) (r : ℝ) (zri zwe : ℕ → ℝ) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)) : Prop :=
  0 < b ∧ Wf b = W
    ∧ CouplingGen.Along.ApertureCount.ApertureCount (cpl βs) (ZCanon.zFix N zri zwe) b Wf
    ∧ CouplingGen.Along.ExpandMatch.ExpandMatch (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
    ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
    ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
    ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
    ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
    ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
    ∧ ∃ ℓ : ℝ, 0 < ℓ
        ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

variable (N) in
/-- The read-expansion bundle with the coefficients' parity added: module docstring, §2. DERIVED: no
numeral. -/
def CoreInputsAlongWAMP (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    ProxyCov.CfParity cf ∧ CoreFieldsAt N βs W r zri zwe μ b Wf cf

/-- The pinned bundle gives the read-expansion bundle. DERIVED: no numeral. -/
theorem coreWAM_of_coreWAMP {βs : ℕ → ℝ} (h : CoreInputsAlongWAMP N βs) :
    ExpandMatch.CoreInputsAlongWAM N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, _, hF⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hF⟩

/-- A read-expansion witness whose `cf` meets `CfParity` is a pinned witness. DERIVED: no numeral. -/
theorem coreWAMP_of_cfParity {βs : ℕ → ℝ} {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)}
    (hP : ProxyCov.CfParity cf) (hF : CoreFieldsAt N βs W r zri zwe μ b Wf cf) :
    CoreInputsAlongWAMP N βs :=
  ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hP, hF⟩

/-- At a one-sign leading-logarithm family the fields give the pinned bundle. DERIVED: `−1` the sign;
`0` the plane. -/
theorem coreWAMP_of_cfScaled {βs : ℕ → ℝ} {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {κ : CompositesBuild.Ix0 → MultiScaleAll.MIx →₀ ℝ}
    {γ : CompositesBuild.Ix0 → ℝ}
    (hκ : ∀ i j, j ∈ (κ i).support → (-1 : ℝ) ^ ProxyCov.mPar j = (-1 : ℝ) ^ ctau 0 i.1)
    (hF : CoreFieldsAt N βs W r zri zwe μ b Wf (FlowChoice.cfScaled κ γ)) :
    CoreInputsAlongWAMP N βs :=
  coreWAMP_of_cfParity hphys hri hwe (ProxyCov.cfParity_cfScaled κ γ hκ) hF

/-- At `cfLead` the fields give the pinned bundle. DERIVED: no numeral. -/
theorem coreWAMP_of_cfLead {βs : ℕ → ℝ} {W : ConfFlow N} {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (hF : CoreFieldsAt N βs W r zri zwe μ b Wf FlowChoice.cfLead) :
    CoreInputsAlongWAMP N βs :=
  coreWAMP_of_cfParity hphys hri hwe ProxyCov.cfParity_cfLead hF

/-- The root at `SU(N)` at the pinned bundle: `StrongEnd N`, the settling window reading and
`CoreInputsAlongWAMP` along the towers near `0⁺` give `ClayStatementOf (SU N)`
(`ExpandMatch.clayStatementOf_of_apertureMatch`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_apertureMatchP (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWAMP N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  ExpandMatch.clayStatementOf_of_apertureMatch hS hUV
    (hF.mono fun _ h βs hT => coreWAM_of_coreWAMP (h βs hT))

end MassGap.RoutePin

end

/-! ## 3. The gap read on the route flow -/

noncomputable section

namespace MassGap.RoutePin

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
  MassGap.CompositesBuild MassGap.MultiScaleAll MassGap.CompositesRen MassGap.ApproxFromExpand
  MassGap.NondegFromProxy MassGap.ClayData MassGap.ReflAvg MassGap.ObserverFlowSUN MassGap.ProxyCov

variable {N : ℕ}

/-- On the route flow, a one-sign reflected read at one gap gives the floor at every larger resolved
gap, with no membership and no range hypothesis: module docstring, §3. DERIVED: `0` the plane and the
contact gap; `1` the least inner gap and the cap; `2` the two steps of one gap; `12 = 2 · 6` the coupling
bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem gapRead_far_sunFam (hN : 2 ≤ N) [NeZero N] {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : 12 * c₀ < Real.sin (Real.pi / N)) {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hL : ExpandFam.ExpandLim (sunFam hN c₀ hc0 hc) cf z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hpc : PureC c)
    {g : TestFn} (hg : PosT g) {t₁ t : ℝ} (m₁ m : ℕ → ℕ)
    (hrep : ∀ᶠ k in atTop, 1 ≤ m₁ k ∧ m₁ k ≤ m k
      ∧ 2 * (m₁ k : ℝ) * dySpacing N k = t₁ ∧ 2 * (m k : ℝ) * dySpacing N k = t)
    {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      δ ≤ |proxRead (sunFam hN c₀ hc0 hc) cf c (g.reflect 0) (g.translate (Pi.single 0 t₁)) k s|) :
    ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      (|contRead (N := N) z μ c (g.reflect 0) g| + δ)
          * min (δ / (|contRead (N := N) z μ c (g.reflect 0) g| + δ)) 1 ^ (t / t₁)
        ≤ |proxRead (sunFam hN c₀ hc0 hc) cf c (g.reflect 0) (g.translate (Pi.single 0 t)) k s| := by
  obtain ⟨d, hd, hgd⟩ := hg.2
  exact gapRead_far_of_range hL hC hP hpc hg hgd (sunFam_range_small hN hc0 hc hd) m₁ m hrep hδ h1

/-- On the route flow, `GapRead` at one dyadic gap gives `GapRead` at every larger dyadic gap.
DERIVED: `1` the least numerator; `2` the dyadic base; `0` the plane; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem gapRead_dyadic_sunFam (hN : 2 ≤ N) [NeZero N] {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : 12 * c₀ < Real.sin (Real.pi / N)) {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hL : ExpandFam.ExpandLim (sunFam hN c₀ hc0 hc) cf z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hpc : PureC c)
    {g : TestFn} (hg : PosT g) {j₁ j k₀ : ℕ} (hj₁ : 1 ≤ j₁) (hj : j₁ ≤ j)
    (h : GapRead (sunFam hN c₀ hc0 hc) cf c g (j₁ * AsymptoticScaling.aRun N 1 / 2 ^ k₀)) :
    GapRead (sunFam hN c₀ hc0 hc) cf c g (j * AsymptoticScaling.aRun N 1 / 2 ^ k₀) := by
  obtain ⟨δ, hδ, h1⟩ := h
  exact ⟨_, far_floor_pos (C := contRead (N := N) z μ c (g.reflect 0) g) hδ,
    gapRead_far_sunFam hN hc0 hc hL hC hP hpc hg (fun k => j₁ * 2 ^ (k - k₀))
      (fun k => j * 2 ^ (k - k₀)) (rep_dyadic hj₁ hj) hδ h1⟩

/-- `gapRead_dyadic_sunFam` at `cfLead`, with `CfParity` discharged. DERIVED: `1` the least numerator;
`2` the dyadic base; `12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem gapRead_dyadic_sunFam_lead (hN : 2 ≤ N) [NeZero N] {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : 12 * c₀ < Real.sin (Real.pi / N)) {z : Chan → ℕ → ℝ} {μ : OffMix}
    (hL : ExpandFam.ExpandLim (sunFam hN c₀ hc0 hc) FlowChoice.cfLead z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) {c : Ix0 →₀ ℝ} (hpc : PureC c)
    {g : TestFn} (hg : PosT g) {j₁ j k₀ : ℕ} (hj₁ : 1 ≤ j₁) (hj : j₁ ≤ j)
    (h : GapRead (sunFam hN c₀ hc0 hc) FlowChoice.cfLead c g (j₁ * AsymptoticScaling.aRun N 1 / 2 ^ k₀)) :
    GapRead (sunFam hN c₀ hc0 hc) FlowChoice.cfLead c g (j * AsymptoticScaling.aRun N 1 / 2 ^ k₀) :=
  gapRead_dyadic_sunFam hN hc0 hc hL hC cfParity_cfLead hpc hg hj₁ hj h

end MassGap.RoutePin

end

#print axioms MassGap.RoutePin.sunFam_range_le
#print axioms MassGap.RoutePin.sunFam_range_gt
#print axioms MassGap.RoutePin.sunFam_range_small
#print axioms MassGap.RoutePin.rangeBelow_const_iff
#print axioms MassGap.RoutePin.projection_load_bearing
#print axioms MassGap.RoutePin.coreWAM_of_coreWAMP
#print axioms MassGap.RoutePin.coreWAMP_of_cfParity
#print axioms MassGap.RoutePin.coreWAMP_of_cfScaled
#print axioms MassGap.RoutePin.coreWAMP_of_cfLead
#print axioms MassGap.RoutePin.clayStatementOf_of_apertureMatchP
#print axioms MassGap.RoutePin.gapRead_far_sunFam
#print axioms MassGap.RoutePin.gapRead_dyadic_sunFam
#print axioms MassGap.RoutePin.gapRead_dyadic_sunFam_lead
