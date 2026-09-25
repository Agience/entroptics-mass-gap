import Mathlib
import MassGap.ContinuumNontrivial

noncomputable section

/-!
# MassGap.ContinuumFlow — flowed Schwinger functions along the running coupling

## The idea

A probe whose value is finite at every spacing, the same signal read at every zoom level, needs no
renormalisation beyond its canonical dimension. The standard realisation is the Yang–Mills gradient
flow (Lüscher 2010, 2011): the gauge field is smoothed by a heat-kernel diffusion of physical radius
`√(8t)`, flowed links stay in `SU(N)`, and flowed composite fields, in their canonical normalisation,
are finite in the continuum limit to all orders in perturbation theory. The flowed energy density
is `a⁻⁴ (1 − plaquette ∘ V_t)`: the canonical factor `a⁻⁴`, a fixed subtraction, and the flowed
configuration `V_t`.

## The data

A `Flow` is, at each step `k` of `ContinuumSchwinger.dyBeta`, a map `Φ.map k` on local
gauge-invariant fields that commutes with the time reflection of each axis (`map_refl`) and has a
finite lattice range `Φ.range k` (`map_local`). Gauge invariance and locality of the flowed field are
carried by its type `LField`.

`ConfFlow` is a deterministic flow of configurations `V k : Cfg N → Cfg N`: continuous, gauge
covariant, reflection covariant, of finite range. `Flow.ofConfScaled W z c` is the flowed field
`O ↦ z_k(O) · (O ∘ V k − c_k(O))`: `z` the canonical factor (`canonZ`, `a⁻⁴` for a dimension-four
field), `c` a subtraction. The localised gradient flow (the flow run inside the physical ball of
radius `r` about each link, the configuration held fixed outside) is a `ConfFlow` of physical range
`r` (`Flow.PhysRange r`), whatever the number `∝ t/a²` of flow steps inside the ball.

## What holds for every flow under the uniform bound

The flowed lattice Schwinger function of step `k` is `latSF hN Φ k F = ν_k (∏ᵢ smear aₖ (Φ_k Oᵢ) fᵢ)`.
`UniformBoundF hN Φ` is `ContinuumSchwinger.UniformBound` for it, over every family, overlapping
supports included. Under it:

* existence `tendsto_contSF`; OS0 `exists_abs_contSF_le`;
* OS3 `contSF_comp_equiv`, OS1 on the dyadic translations `contSF_translate` and on the axis
  reflections `contSF_reflect`, `kernF_symm`, all unconditional;
* OS2 `contSF_gram_nonneg` on `MarginMono N τ r`, the positive-time monomials whose factors vanish
  below a time `d > r`, under `Flow.PosPreserving τ r`: eventually in the step every flowed smeared
  field supported beyond the margin lies in the half-space algebra.
  `Flow.posPreserving_of_physRange` proves it from `Flow.PhysRange r`. The margin is the flow's reach
  across the reflection plane.
* the reconstruction `flow_reconstruction`: at each dyadic step a complete Hilbert space, a unit
  vacuum, a self-adjoint transfer operator fixing it with spectrum in `[0, 1]`, and
  `⟪gVec P, gVec Q⟫ = S(θP ∪ Q)` on margin monomials. It runs through the reconstruction from an
  abstract kernel of section 5 (`gTransfer`), which the flowed kernel instantiates.

## Where the uniform bound comes from

* `uniformBoundF_of_bounded`: a flow whose fields stay bounded in sup norm uniformly in the step
  (`Flow.Bounded`; for `ofConfScaled` at bounded `z`, `c`, `Flow.ofConfScaled_bounded`) has the uniform
  bound, with the bare constant. A bounded local field smeared over `a⁻⁴` cells is expected to
  average to its mean, as for the bare fields (`ContinuumReconstruction.continuum_reconstruction_bare`),
  so this case is expected degenerate.
* `latSF_zeroFlow`, `uniformBoundF_zeroFlow_iff`: at zero flow time (`ConfFlow.identity`) the scaled
  flow is the renormalised theory, `latSF = latSkR` for `Renorm ⟨z, c⟩`, and `UniformBoundF` is
  `ContinuumSchwinger.UniformBound`. `latKernelF_zeroFlow_connected`: its connected kernel is
  `ContinuumNontrivial.latKernel` for `Renorm.connected`.
* **The open input where the flow works**: `UniformBoundF` for `Flow.ofConfScaled W_t canonZ c`, `W_t`
  the localised gradient flow at a fixed physical time `t > 0`. The flowed composite has finite
  moments (Lüscher), so the bound is expected over all families; at `t = 0` it is `UniformBound` at
  the canonical factor, expected to fail at coincident points (`r⁻⁸ (log r)⁻²`, not integrable at
  `r = 0` in four dimensions).

## The other open inputs, stated

* **The beacon** `FlowBeacon hN Φ`: for every family the flowed lattice functions form a Cauchy
  sequence in the step. It gives `FlowConverges` (`flowConverges_of_beacon`), under which the limit
  along `atTop` is `contSF` (`tendsto_atTop_contSF`) for every ultrafilter below `atTop`
  (`limUnder_eq_contSF`).
* **Non-triviality** `FlowConnectedNonzero hN Φ τ r`: some margin monomial `Q` has
  `S(θQ ∪ Q) − S(Q)² ≠ 0`; it gives a non-zero vector orthogonal to the vacuum
  (`exists_orth_ne_zero_flow`).
* **The flowed kernel** `FlowKernelConverges hN Φ τ O G₂`: the connected flowed two-point function
  `latKernelF` converges to `G₂` uniformly on `sepBoxSet 0 R`, coincident points included;
  `flowKernelLimitOn_sep` restricts it to the separated sets of `ContinuumNontrivial.KernelConvergesSep`.
  At zero flow time with the connected subtraction it is that kernel extended to separation `0`.
  With `z = canonZ` the kernel carries `a⁻⁸`, the normalisation of `ShortDistanceY.latticeTwoPoint`;
  requirement Y describes the flowed profile `G_t(r)` in the window `√(8t) ≪ r`, where the flow
  changes the two-point function by terms of relative order `t/r²`.

## Scope

The gradient flow on `SU(N)^links` is not constructed: it needs the matrix exponential on `SU(N)` and
the flow equation, which the tree does not carry. The heat-bath maps of `MassGap.HeatBath` read one
period of the torus (`heatLift` through `restrictConf`) and keep periodic gauge invariance only; a
product of single-link heat baths is reflection covariant only for a reflection-symmetric order,
which neighbouring non-commuting baths do not admit; and a Markov smoothing preserves the state and
injects fresh noise at every sweep, so at a fixed physical number of sweeps it is stochastic
quantisation, whose composite fields keep their divergences. The flow therefore stays an interface,
with `ConfFlow` the slot for the gradient flow. The one `ConfFlow` the tree constructs is
`ConfFlow.identity`, of range `0`, where the flowed functions, the uniform bound and the kernel are
the `ContinuumSchwinger` ones (`latSF_zeroFlow`, `contSF_zeroFlow`, `uniformBoundF_zeroFlow_iff`,
`latKernelF_zeroFlow_connected`). What the flow adds (a margin `r > 0` from `Flow.PhysRange r`, and
`UniformBoundF`, `FlowBeacon` and `FlowKernelConverges` over coincident supports at the canonical
factor) has content at the localised gradient flow at `t > 0`, which the tree does not construct.
Clustering of the flowed functions and the small
flow-time limit `t → 0`, where local fields and their renormalisation return through the flow-time
expansion, are outside this file.
-/

namespace MassGap.ContinuumFlow

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The flow interface -/

section Interface

/-- **A flow of the local fields**: at each step `k` a map `map k` on local gauge-invariant fields,
commuting with the time reflection of each axis, and of lattice range `range k`: a field local on
`S` flows to a field local on links each within `range k`, in every coordinate of the base site, of a
link of `S`. Gauge invariance and locality of the flowed field are carried by `LField`. The flowed
field at the site `x` is the translate `T_x (map k O)` (`smear` translates after flowing); for a
configuration flow commuting with translations, as the gradient flow does, it is the flow of
`T_x O`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the reflection constant `0` enters through
`LField.refl`. -/
structure Flow (N : ℕ) where
  /-- The flowed field at step `k`. -/
  map : ℕ → LField (MassGap.SUN.SU N) → LField (MassGap.SUN.SU N)
  /-- The lattice range of the flow at step `k`. -/
  range : ℕ → ℕ
  /-- The flow commutes with the time reflection of each axis. -/
  map_refl : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)),
    map k (O.refl τ) = (map k O).refl τ
  /-- The flow has finite range. -/
  map_local : ∀ (k : ℕ) (O : LField (MassGap.SUN.SU N)) (S : Finset ILink),
    IsLocalOn S (O.1 : Cfg N → ℝ) →
      ∃ S' : Finset ILink, IsLocalOn S' ((map k O).1 : Cfg N → ℝ) ∧
        ∀ l' ∈ S', ∃ l ∈ S, ∀ i, |l'.2 i - l.2 i| ≤ (range k : ℤ)

/-- The flowed field datum of step `k`: the field flowed, the test function kept.

DERIVED: no numeral. -/
def Flow.field (Φ : Flow N) (k : ℕ) (p : SField N) : SField N := (Φ.map k p.1, p.2)

/-- The flowed monomial of step `k`.

DERIVED: no numeral. -/
abbrev Flow.mono (Φ : Flow N) (k : ℕ) (P : Mono N) : Mono N := ⟨P.1, fun i => Φ.field k (P.2 i)⟩

/-- **A bounded flow**: every flowed field is bounded in sup norm uniformly in the step.

DERIVED: no numeral. -/
def Flow.Bounded (Φ : Flow N) : Prop :=
  ∀ O : LField (MassGap.SUN.SU N), ∃ B : ℝ, ∀ k, ‖(Φ.map k O).1‖ ≤ B

/-- **Physical range `r`**: eventually in the step the lattice range times the spacing is at most
`r`.

DERIVED: no numeral; `r` is the caller's physical range. -/
def Flow.PhysRange (Φ : Flow N) (r : ℝ) : Prop :=
  ∀ᶠ k in atTop, dySpacing N k * (Φ.range k : ℝ) ≤ r

/-- **The flow keeps the positive half-space beyond the margin `r`**: for every field and every test
function vanishing below a time `δ > 0` with `δ > r` in direction `τ`, eventually in the step the
flowed smeared field lies in the half-space algebra of the plane `x_τ = 0`. This is what reflection
positivity of the flowed limit consumes (`contSF_gram_nonneg`).

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the plane `x_τ = 0` and the sign of `δ`.
-/
def Flow.PosPreserving (Φ : Flow N) (τ : Fin 4) (r : ℝ) : Prop :=
  ∀ (O : LField (MassGap.SUN.SU N)) (f : TestFn) (δ : ℝ), 0 < δ → r < δ →
    (∀ y, f.1 y ≠ 0 → δ ≤ y τ) →
      ∀ᶠ k in atTop, smear (dySpacing N k) (Φ.map k O).1 f
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0

/-- **A configuration map of finite range carries local observables to local observables.** If each
output link of `W` reads the input only on links within `R` of it, then `F ∘ W` is local on a finite
set each of whose links is within `R` of a link of the support of `F`.

DERIVED: no numeral; `R` is the caller's range. -/
theorem isLocalOn_comp {R : ℕ} {W : Cfg N → Cfg N}
    (hW : ∀ l : ILink, ∃ T : Finset ILink, (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ)) ∧
      ∀ U U' : Cfg N, (∀ l' ∈ T, U l' = U' l') → W U l = W U' l)
    {S : Finset ILink} {F : Cfg N → ℝ} (hS : IsLocalOn S F) :
    ∃ S' : Finset ILink, IsLocalOn S' (fun U => F (W U)) ∧
      ∀ l' ∈ S', ∃ l ∈ S, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ) := by
  classical
  choose T hTr hTl using hW
  refine ⟨S.biUnion T, fun U U' h => hS _ _ (fun l hl => hTl l U U' (fun l' hl' =>
    h l' (Finset.mem_biUnion.mpr ⟨l, hl, hl'⟩))), fun l' hl' => ?_⟩
  obtain ⟨l, hl, hl'T⟩ := Finset.mem_biUnion.mp hl'
  exact ⟨l, hl, hTr l l' hl'T⟩

#print axioms isLocalOn_comp

/-- The field `s · O`.

DERIVED: no numeral. -/
def scaleField (O : LField (MassGap.SUN.SU N)) (s : ℝ) : LField (MassGap.SUN.SU N) :=
  ⟨s • O.1,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      exact ⟨S, fun U V h => by
        show s * O.1 U = s * O.1 V
        rw [hS U V h]⟩,
     fun g U => by
      show s * O.1 (GaugeInvariantAlgebra.igaugeTransform g U) = s * O.1 U
      rw [O.2.2 g U]⟩⟩

/-- Reflection commutes with scaling.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the reflection constant `0` enters through
`LField.refl`. -/
theorem refl_scaleField (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (s : ℝ) :
    (scaleField O s).refl τ = scaleField (O.refl τ) s :=
  Subtype.ext (map_smul (LatticeReflection.ireflObs (G := MassGap.SUN.SU N) τ 0) s O.1)

#print axioms refl_scaleField

/-- `s · (F − r · 1)` is local wherever `F` is.

DERIVED: `1` is the unit observable. -/
theorem isLocalOn_scale_sub {S : Finset ILink} {F : C(Cfg N, ℝ)}
    (hF : IsLocalOn S (F : Cfg N → ℝ)) (r s : ℝ) :
    IsLocalOn S ((s • (F - r • (1 : C(Cfg N, ℝ))) : C(Cfg N, ℝ)) : Cfg N → ℝ) := by
  intro U V h
  show s * (F U - r * 1) = s * (F V - r * 1)
  rw [hF U V h]

#print axioms isLocalOn_scale_sub

/-- **A deterministic flow of configurations**: at each step `k` a continuous map `V k` of `SU(N)`
configurations on `ℤ⁴`, covariant under the local gauge group and under the time reflection of each
axis, whose output at each link reads the input only on links within `range k` of it. The localised
gradient flow (the flow run inside the physical ball of radius `r` about each link, the
configuration held fixed outside) is of this kind with `range k` about `r / aₖ`; it also commutes
with the lattice translations, which no statement here consumes.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant, the plane
`x_τ = 0`. -/
structure ConfFlow (N : ℕ) where
  /-- The flowed configuration at step `k`. -/
  V : ℕ → Cfg N → Cfg N
  /-- Continuity in the product topology. -/
  continuous_V : ∀ k, Continuous (V k)
  /-- Gauge covariance. -/
  gauge : ∀ (k : ℕ) (g : ISite → MassGap.SUN.SU N) (U : Cfg N),
    V k (GaugeInvariantAlgebra.igaugeTransform g U) = GaugeInvariantAlgebra.igaugeTransform g (V k U)
  /-- Reflection covariance. -/
  refl : ∀ (k : ℕ) (τ : Fin 4) (U : Cfg N),
    V k (LatticeReflection.ireflConf τ 0 U) = LatticeReflection.ireflConf τ 0 (V k U)
  /-- The lattice range at step `k`. -/
  range : ℕ → ℕ
  /-- Finite range. -/
  local_V : ∀ (k : ℕ) (l : ILink), ∃ T : Finset ILink,
    (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (range k : ℤ)) ∧
      ∀ U U' : Cfg N, (∀ l' ∈ T, U l' = U' l') → V k U l = V k U' l

/-- The flowed field `O ∘ V k`: continuous, local by `isLocalOn_comp`, gauge invariant by gauge
covariance of `V k`.

DERIVED: no numeral. -/
def ConfFlow.fieldMap (W : ConfFlow N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) :
    LField (MassGap.SUN.SU N) :=
  ⟨O.1.comp ⟨W.V k, W.continuous_V k⟩,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      obtain ⟨S', hS', -⟩ := isLocalOn_comp (W.local_V k) hS
      exact ⟨S', hS'⟩,
     fun g U => by
      show O.1 (W.V k (GaugeInvariantAlgebra.igaugeTransform g U)) = O.1 (W.V k U)
      rw [W.gauge]
      exact O.2.2 g (W.V k U)⟩⟩

/-- The flowed field of a reflected field is the reflected flowed field.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant. -/
theorem ConfFlow.fieldMap_refl (W : ConfFlow N) (k : ℕ) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) : W.fieldMap k (O.refl τ) = (W.fieldMap k O).refl τ :=
  Subtype.ext (ContinuousMap.ext (fun U => by
    show O.1 (LatticeReflection.ireflConf τ 0 (W.V k U))
      = O.1 (W.V k (LatticeReflection.ireflConf τ 0 U))
    rw [W.refl]))

#print axioms ConfFlow.fieldMap_refl

/-- **The scaled configuration flow**: `O ↦ z_k(O) · (O ∘ V k − c_k(O) · 1)`, with the factor and
the subtraction reflection compatible. Its range is that of `W`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the unit observable. -/
def Flow.ofConfScaled (W : ConfFlow N) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O) :
    Flow N where
  map k O := scaleField ((W.fieldMap k O).sub (c k O)) (z k O)
  range := W.range
  map_refl k τ O := by
    show scaleField ((W.fieldMap k (O.refl τ)).sub (c k (O.refl τ))) (z k (O.refl τ))
      = (scaleField ((W.fieldMap k O).sub (c k O)) (z k O)).refl τ
    rw [hz, hc, W.fieldMap_refl, ← LField.refl_sub, ← refl_scaleField]
  map_local k O S hS := by
    obtain ⟨S', h1, h2⟩ := isLocalOn_comp (W.local_V k) hS
    exact ⟨S', isLocalOn_scale_sub (F := (W.fieldMap k O).1) h1 (c k O) (z k O), h2⟩

/-- **A scaled flow at bounded factor and subtraction is bounded**:
`‖z · (O ∘ V − c)‖ ≤ B_z (‖O‖ + B_c)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the unit observable, through
`norm_sub_smul_one_le`. -/
theorem Flow.ofConfScaled_bounded (W : ConfFlow N) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O)
    (hzb : ∀ O, ∃ B : ℝ, ∀ k, |z k O| ≤ B) (hcb : ∀ O, ∃ B : ℝ, ∀ k, |c k O| ≤ B) :
    (Flow.ofConfScaled W z c hz hc).Bounded := by
  intro O
  obtain ⟨Bz, hBz⟩ := hzb O
  obtain ⟨Bc, hBc⟩ := hcb O
  refine ⟨Bz * (‖O.1‖ + Bc), fun k => ?_⟩
  show ‖z k O • ((W.fieldMap k O).1 - c k O • (1 : C(Cfg N, ℝ)))‖ ≤ Bz * (‖O.1‖ + Bc)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : ‖(W.fieldMap k O).1‖ ≤ ‖O.1‖ :=
    (ContinuousMap.norm_le (W.fieldMap k O).1 (norm_nonneg O.1)).mpr
      (fun U => O.1.norm_coe_le_norm (W.V k U))
  have h2 : ‖(W.fieldMap k O).1 - c k O • (1 : C(Cfg N, ℝ))‖ ≤ ‖O.1‖ + Bc :=
    (norm_sub_smul_one_le _ _).trans (by linarith [hBc k])
  exact mul_le_mul (hBz k) h2 (norm_nonneg _) ((abs_nonneg _).trans (hBz k))

#print axioms Flow.ofConfScaled_bounded

/-- **The unscaled configuration flow** `O ↦ O ∘ V k`: factor `1`, no subtraction.

DERIVED: `1` and `0` are the identity factor and subtraction. -/
def Flow.ofConf (W : ConfFlow N) : Flow N :=
  Flow.ofConfScaled W (fun _ _ => 1) (fun _ _ => 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- The unscaled configuration flow is bounded.

DERIVED: `1` and `0` bound the identity factor and subtraction. -/
theorem Flow.ofConf_bounded (W : ConfFlow N) : (Flow.ofConf W).Bounded :=
  Flow.ofConfScaled_bounded W (fun _ _ => 1) (fun _ _ => 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => ⟨1, fun _ => by simp⟩) (fun _ => ⟨0, fun _ => by simp⟩)

#print axioms Flow.ofConf_bounded

/-- **The canonical factor of a dimension-four field**, `aₖ⁻⁴`.

DERIVED: `4` is the canonical dimension of `tr F²` in four dimensions. -/
def canonZ (N : ℕ) (k : ℕ) (_O : LField (MassGap.SUN.SU N)) : ℝ := (dySpacing N k ^ 4)⁻¹

/-- The canonical factor is reflection compatible.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem canonZ_refl (N : ℕ) (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) :
    canonZ N k (O.refl τ) = canonZ N k O := rfl

#print axioms canonZ_refl

/-- **The zero-time configuration flow**: `V k = id`, range `0`. The fields of `ConfFlow` are jointly
satisfiable.

DERIVED: `0` is the range of the identity. -/
def ConfFlow.identity (N : ℕ) : ConfFlow N where
  V _ U := U
  continuous_V _ := continuous_id
  gauge _ _ _ := rfl
  refl _ _ _ := rfl
  range _ := 0
  local_V _ l := ⟨{l}, fun l' hl' i => by
      rw [Finset.mem_singleton.mp hl', sub_self, abs_zero]
      exact Nat.cast_nonneg _,
    fun U U' h => h l (Finset.mem_singleton_self l)⟩

end Interface

/-! ## 2. Flowed lattice Schwinger functions and the uniform bound -/

section Lattice

/-- **The flowed lattice Schwinger function of step `k`**:
`ν_k (∏ᵢ smear aₖ (Φ_k Oᵢ) fᵢ)`, `ν_k = stateK hN k`, `aₖ = aRun N (dyBeta k)`.

DERIVED: `0` is the excluded colour count. -/
noncomputable def latSF (hN : N ≠ 0) (Φ : Flow N) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SField N) : ℝ :=
  latSk hN k (fun i => Φ.field k (F i))

/-- **The flowed bound from a sup-norm bound on the flowed fields**, eventually in the step and
uniform over dyadic translations: `|latSF| ≤ ∏ᵢ B(Oᵢ) Mᵢ (2Rᵢ + 3)⁴` when `‖Φ_k O‖ ≤ B(O)` at every
step.

DERIVED: `0` is the excluded colour count; `2`, `3`, `4` are `ContinuumField.norm_smear_le`'s. The
spacing bound `1` enters in the proof, where `dySpacing N k` falls below one. -/
theorem eventually_abs_latSF_le (hN : N ≠ 0) (Φ : Flow N) (B : LField (MassGap.SUN.SU N) → ℝ)
    (hBd : ∀ k O, ‖(Φ.map k O).1‖ ≤ B O) {ι : Type} [Fintype ι] (F : ι → SField N)
    (R M : ι → ℝ) (hRM : ∀ i, IsTest (F i).2.1 (R i) (M i)) (m : ℕ) (n : ι → ISite) :
    ∀ᶠ k in atTop,
      |latSF hN Φ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))|
        ≤ ∏ i, B (F i).1 * (M i * (2 * R i + 3) ^ 4) := by
  filter_upwards [Filter.eventually_ge_atTop m,
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hfam : (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))
      = (fun i => ((Φ.field k (F i)).1, (Φ.field k (F i)).2.translate
          (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))) := by
    funext i
    show (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N m) (n i)))
      = (Φ.map k (F i).1, (F i).2.translate (site (dySpacing N k) (scaleSite (2 ^ (k - m)) (n i))))
    rw [site_dySpacing N hk]
  have hL := abs_latS_translate_le (stateK hN k) ha hk1.le (fun i => Φ.field k (F i))
    (fun i => scaleSite (2 ^ (k - m)) (n i)) R M hRM
  have hQ : ∏ i, ‖(Φ.field k (F i)).1.1‖ * (M i * (2 * R i + 3) ^ 4)
      ≤ ∏ i, B (F i).1 * (M i * (2 * R i + 3) ^ 4) :=
    Finset.prod_le_prod
      (fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hRM i).M_nonneg (by positivity)))
      (fun i _ => mul_le_mul_of_nonneg_right (hBd k (F i).1)
        (mul_nonneg (hRM i).M_nonneg (by positivity)))
  show |latSk hN k (fun i => Φ.field k ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))|
    ≤ _
  rw [latSk_eq, hfam]
  exact hL.trans hQ

#print axioms eventually_abs_latSF_le

/-- **The flowed uniform bound**, `ContinuumSchwinger.UniformBound` for the flowed functions: for
every family one constant bounds the flowed lattice functions eventually in the step, whatever
dyadic translation is applied to each factor. Families with overlapping test functions are included.

DERIVED: `0` is the excluded colour count. -/
def UniformBoundF (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
    ∀ᶠ k in atTop,
      |latSF hN Φ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C

/-- **A bounded flow has the uniform bound.**

DERIVED: `0` is the excluded colour count. -/
theorem uniformBoundF_of_bounded (hN : N ≠ 0) (Φ : Flow N) (hΦ : Φ.Bounded) :
    UniformBoundF hN Φ := by
  intro ι _ F
  have hΦ' : ∀ O : LField (MassGap.SUN.SU N), ∃ B : ℝ, ∀ k, ‖(Φ.map k O).1‖ ≤ B := hΦ
  choose B hB using hΦ'
  have hex : ∀ i, ∃ R M : ℝ, IsTest (F i).2.1 R M := fun i => (F i).2.2
  choose R M hRM using hex
  exact ⟨_, fun m n => eventually_abs_latSF_le hN Φ B (fun k O => hB O k) F R M hRM m n⟩

#print axioms uniformBoundF_of_bounded

end Lattice

/-! ## 3. The flowed limit and its covariances -/

section Limit

/-- **The flowed continuum Schwinger function**: `limUnder` along `ultra` of the flowed lattice
functions. Under `UniformBoundF` it is their limit along `ultra` for every family
(`tendsto_contSF`).

DERIVED: `0` is the excluded colour count. -/
noncomputable def contSF (hN : N ≠ 0) (Φ : Flow N) {ι : Type} [Fintype ι] (F : ι → SField N) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latSF hN Φ k F)

/-- **Existence of the flowed limit** under the uniform bound.

DERIVED: `0` is the zero translation. -/
theorem tendsto_contSF (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    Tendsto (fun k => latSF hN Φ k F) (ultra : Filter ℕ) (𝓝 (contSF hN Φ F)) := by
  obtain ⟨C, hC⟩ := hB ι F
  have h0 := hC 0 (fun _ => 0)
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ h0
  exact tendsto_nhds_limUnder ⟨x, hx⟩

#print axioms tendsto_contSF

/-- **OS0 for the flowed limit**: a bound per family, uniform over dyadic translations of the
factors.

DERIVED: `0` is the excluded colour count. -/
theorem exists_abs_contSF_le (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    ∃ C : ℝ, ∀ (m : ℕ) (n : ι → ISite),
      |contSF hN Φ (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) (n i))))| ≤ C := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨C, hC⟩ := hB ι F
  exact ⟨C, fun m n =>
    le_of_tendsto (tendsto_contSF hN Φ hB _).abs ((hC m n).filter_mono ultra_le)⟩

#print axioms exists_abs_contSF_le

/-- **OS0 explicitly for a flow bounded by `B`**: `|contSF F| ≤ ∏ᵢ B(Oᵢ) Mᵢ (2Rᵢ + 3)⁴`.

DERIVED: `0` is the excluded colour count; `2`, `3`, `4` as in `eventually_abs_latSF_le`. -/
theorem abs_contSF_le (hN : N ≠ 0) (Φ : Flow N) (B : LField (MassGap.SUN.SU N) → ℝ)
    (hBd : ∀ k O, ‖(Φ.map k O).1‖ ≤ B O) {ι : Type} [Fintype ι] (F : ι → SField N)
    (R M : ι → ℝ) (hRM : ∀ i, IsTest (F i).2.1 (R i) (M i)) :
    |contSF hN Φ F| ≤ ∏ i, B (F i).1 * (M i * (2 * R i + 3) ^ 4) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hB : UniformBoundF hN Φ :=
    uniformBoundF_of_bounded hN Φ (fun O => ⟨B O, fun k => hBd k O⟩)
  have h0 := eventually_abs_latSF_le hN Φ B hBd F R M hRM 0 (fun _ => 0)
  simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
  exact le_of_tendsto (tendsto_contSF hN Φ hB F).abs (h0.filter_mono ultra_le)

#print axioms abs_contSF_le

/-- **OS3, symmetry**: reindexing a family does not change its flowed continuum function. The
reindexed sequences agree term by term.

DERIVED: `0` is the excluded colour count. -/
theorem contSF_comp_equiv (hN : N ≠ 0) (Φ : Flow N) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (F : ι → SField N) : contSF hN Φ (F ∘ e) = contSF hN Φ F := by
  unfold contSF
  congr 1
  funext k
  show latSk hN k (fun i => Φ.field k ((F ∘ e) i)) = latSk hN k (fun i => Φ.field k (F i))
  rw [latSk_eq, latSk_eq]
  exact latS_comp_equiv _ _ e (fun i => Φ.field k (F i))

#print axioms contSF_comp_equiv

/-- **OS1, dyadic translations**: translating every test function by `dySpacing N m · n` leaves the
flowed continuum function unchanged. The sequences agree from step `m` on.

DERIVED: `0` is the excluded colour count. The halving enters in the proof, through
`site_dySpacing`. -/
theorem contSF_translate (hN : N ≠ 0) (Φ : Flow N) {ι : Type} [Fintype ι] (F : ι → SField N)
    (m : ℕ) (n : ISite) :
    contSF hN Φ (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n)))
      = contSF hN Φ F := by
  unfold contSF
  refine limUnder_congr_ultra ?_
  filter_upwards [Filter.eventually_ge_atTop m] with k hk
  show latSk hN k (fun i => ((Φ.field k (F i)).1,
      (Φ.field k (F i)).2.translate (site (dySpacing N m) n)))
    = latSk hN k (fun i => Φ.field k (F i))
  rw [latSk_eq, latSk_eq, site_dySpacing N hk n]
  exact latS_translate (stateK hN k) (fun τ => PeriodicState.periodicState_shift hN _ τ)
    (dySpacing_pos (one_le_of_ne_zero hN) k) (fun i => Φ.field k (F i))
    (scaleSite (2 ^ (k - m)) n)

#print axioms contSF_translate

/-- **OS1, the axis reflections**: reflecting every field and test function in the axis `τ` leaves
the flowed continuum function unchanged.

DERIVED: `0` is the excluded colour count and the reflection constant; `4` in `Fin 4` is the
spacetime dimension. -/
theorem contSF_reflect (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) {ι : Type} [Fintype ι]
    (F : ι → SField N) :
    contSF hN Φ (fun i => SField.refl τ (F i)) = contSF hN Φ F := by
  unfold contSF
  congr 1
  funext k
  have hfam : (fun i => Φ.field k (SField.refl τ (F i)))
      = fun i => SField.refl τ (Φ.field k (F i)) := by
    funext i
    show (Φ.map k ((F i).1.refl τ), (F i).2.reflect τ)
      = ((Φ.map k (F i).1).refl τ, (F i).2.reflect τ)
    rw [Φ.map_refl]
  show latSk hN k (fun i => Φ.field k (SField.refl τ (F i)))
    = latSk hN k (fun i => Φ.field k (F i))
  rw [hfam, latSk_eq, latSk_eq]
  exact latS_refl (stateK hN k) τ
    (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0)
    (dySpacing_pos (one_le_of_ne_zero hN) k) (fun i => Φ.field k (F i))

#print axioms contSF_reflect

/-- Smearing is homogeneous in the field.

DERIVED: `0` is the sign of `a`. -/
theorem smear_smul {a : ℝ} (ha : 0 < a) (s : ℝ) (F : C(Cfg N, ℝ)) (f : TestFn) :
    smear a (s • F) f = s • smear a F f := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha (s • F) f hf (Finset.Subset.refl _),
    smear_eq_sum ha F f hf (Finset.Subset.refl _), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_smul, smul_comm]

#print axioms smear_smul

/-- A product of scaled observables is the product of the scales times the product.

DERIVED: `1` is the empty product. -/
theorem prod_smul_eq {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (A : ι → C(X, ℝ)) : ∏ i ∈ s, (r i • A i) = (∏ i ∈ s, r i) • ∏ i ∈ s, A i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, Finset.prod_insert hb, ih,
      smul_mul_smul_comm]

#print axioms prod_smul_eq

/-- **At zero flow time the scaled flow is the renormalised theory**: `latSF` of
`ofConfScaled (ConfFlow.identity N) z c` is `latSkR` of `Renorm ⟨z, c⟩`.

DERIVED: `0` is the excluded colour count and the zero flow time; `4` in `Fin 4` is the spacetime
dimension. -/
theorem latSF_zeroFlow (hN : N ≠ 0) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O)
    (k : ℕ) {ι : Type} [Fintype ι] (F : ι → SField N) :
    latSF hN (Flow.ofConfScaled (ConfFlow.identity N) z c hz hc) k F = latSkR hN ⟨z, c⟩ k F := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hmap : ∀ O : LField (MassGap.SUN.SU N),
      ((Flow.ofConfScaled (ConfFlow.identity N) z c hz hc).map k O).1
        = z k O • (O.sub (c k O)).1 :=
    fun O => ContinuousMap.ext (fun U => rfl)
  show latSk hN k (fun i => (Flow.ofConfScaled (ConfFlow.identity N) z c hz hc).field k (F i))
    = (∏ i, z k (F i).1) * latSk hN k (fun i => ((F i).1.sub (c k (F i).1), (F i).2))
  rw [latSk_eq, latSk_eq]
  show stateK hN k (∏ i, smear (dySpacing N k)
      ((Flow.ofConfScaled (ConfFlow.identity N) z c hz hc).map k (F i).1).1 (F i).2)
    = (∏ i, z k (F i).1) * stateK hN k (∏ i, smear (dySpacing N k) ((F i).1.sub (c k (F i).1)).1
        (F i).2)
  simp only [hmap, smear_smul ha]
  rw [prod_smul_eq, (stateK hN k).map_smul]

#print axioms latSF_zeroFlow

/-- **At zero flow time the flowed uniform bound is `ContinuumSchwinger.UniformBound`** for
`Renorm ⟨z, c⟩`.

DERIVED: `0` is the excluded colour count and the zero flow time; `4` in `Fin 4` is the spacetime
dimension. -/
theorem uniformBoundF_zeroFlow_iff (hN : N ≠ 0) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O) :
    UniformBoundF hN (Flow.ofConfScaled (ConfFlow.identity N) z c hz hc)
      ↔ UniformBound hN ⟨z, c⟩ := by
  constructor
  · intro h ι _ F
    obtain ⟨C, hC⟩ := h ι F
    exact ⟨C, fun m n => (hC m n).mono (fun k hk => by rwa [latSF_zeroFlow] at hk)⟩
  · intro h ι _ F
    obtain ⟨C, hC⟩ := h ι F
    exact ⟨C, fun m n => (hC m n).mono (fun k hk => by rwa [latSF_zeroFlow])⟩

#print axioms uniformBoundF_zeroFlow_iff

/-- **At zero flow time the flowed limit is the renormalised limit**: `contSF` of the zero-time
scaled flow is `contS` of `Renorm ⟨z, c⟩`.

DERIVED: `0` is the excluded colour count and the zero flow time; `4` in `Fin 4` is the spacetime
dimension. -/
theorem contSF_zeroFlow (hN : N ≠ 0) (z c : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (hc : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), c k (O.refl τ) = c k O)
    {ι : Type} [Fintype ι] (F : ι → SField N) :
    contSF hN (Flow.ofConfScaled (ConfFlow.identity N) z c hz hc) F = contS hN ⟨z, c⟩ F := by
  unfold contSF contS
  congr 1
  funext k
  exact latSF_zeroFlow hN z c hz hc k F

#print axioms contSF_zeroFlow

end Limit

/-! ## 4. Reflection positivity of the flowed limit beyond the margin -/

section Positivity

/-- The flowed reflected pair is the reflected pair of the flowed monomials.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem field_pairFam (Φ : Flow N) (k : ℕ) (τ : Fin 4) (P Q : Mono N) :
    (fun x => Φ.field k (pairFam τ P Q x)) = pairFam τ (Φ.mono k P) (Φ.mono k Q) := by
  funext x
  cases x with
  | inl i =>
    show (Φ.map k ((P.2 i).1.refl τ), (P.2 i).2.reflect τ)
      = ((Φ.map k (P.2 i).1).refl τ, (P.2 i).2.reflect τ)
    rw [Φ.map_refl]
  | inr j => rfl

#print axioms field_pairFam

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem latSF_pairFam (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (P Q : Mono N) :
    latSF hN Φ k (pairFam τ P Q) = latSk hN k (pairFam τ (Φ.mono k P) (Φ.mono k Q)) := by
  show latSk hN k (fun x => Φ.field k (pairFam τ P Q x)) = _
  rw [field_pairFam Φ k τ P Q]

#print axioms latSF_pairFam

/-- **The flowed reflection kernel** `S(θP ∪ Q)`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def kernF (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (P Q : Mono N) : ℝ :=
  contSF hN Φ (pairFam τ P Q)

/-- **The flowed kernel is symmetric**: `S(θP ∪ Q) = S(θQ ∪ P)`.

DERIVED: `0` is the excluded colour count and the reflection constant; `4` in `Fin 4` is the
spacetime dimension. -/
theorem kernF_symm (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (P Q : Mono N) :
    kernF hN Φ τ P Q = kernF hN Φ τ Q P := by
  unfold kernF contSF
  congr 1
  funext k
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [latSF_pairFam hN Φ τ k P Q, latSF_pairFam hN Φ τ k Q P, latSk_eq, latSk_eq,
    latS_pairFam _ ha, latS_pairFam _ ha,
    refl_pair_symm (stateK hN k) τ
      (PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0)
      (prodSmear (dySpacing N k) (Φ.mono k P)) (prodSmear (dySpacing N k) (Φ.mono k Q))]

#print axioms kernF_symm

/-- **A flow of physical range `r` keeps the positive half-space beyond `r`.** For a field local on
`S` of depth `D` below the plane, the flowed field is local on links of depth at most `D + range k`,
and `aₖ (D + range k) ≤ aₖ D + r < δ` eventually, since `aₖ D → 0`.

DERIVED: `0` is the excluded colour count and the plane; `4` in `Fin 4` is the spacetime dimension.
-/
theorem Flow.posPreserving_of_physRange (hN : N ≠ 0) (Φ : Flow N) {r : ℝ} (hΦ : Φ.PhysRange r)
    (τ : Fin 4) : Φ.PosPreserving τ r := by
  intro O f δ _ hrδ hf
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth τ S
  have ht : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
  have hΦ' : ∀ᶠ k in atTop, dySpacing N k * (Φ.range k : ℝ) ≤ r := hΦ
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hrδ)), hΦ'] with k hk hkr
  have hk' : dySpacing N k * (D : ℝ) < δ - r := hk
  obtain ⟨S', hS', hrange⟩ := Φ.map_local k O S hS
  have hD' : ∀ l ∈ S', -(l.2 τ) ≤ ((D + Φ.range k : ℕ) : ℤ) := by
    intro l' hl'
    obtain ⟨l, hl, hll⟩ := hrange l' hl'
    have h1 := hD l hl
    have h2 := (abs_le.mp (hll τ)).1
    have e : ((D + Φ.range k : ℕ) : ℤ) = (D : ℤ) + (Φ.range k : ℤ) := Nat.cast_add _ _
    rw [e]
    omega
  have haD : dySpacing N k * ((D + Φ.range k : ℕ) : ℝ) ≤ δ := by
    have e : ((D + Φ.range k : ℕ) : ℝ) = (D : ℝ) + (Φ.range k : ℝ) := Nat.cast_add _ _
    rw [e, mul_add]
    linarith
  exact smear_mem_halfSpaceAlg (dySpacing_pos (one_le_of_ne_zero hN) k) τ hS' hD' haD f hf

#print axioms Flow.posPreserving_of_physRange

/-- Every factor of `P` vanishes below the time `d` in direction `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the support. -/
def posAt (τ : Fin 4) (d : ℝ) (P : Mono N) : Prop :=
  ∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ

/-- A translation forward in time keeps `posAt`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the time component. -/
theorem posAt_shift {τ : Fin 4} {d : ℝ} {P : Mono N} (h : posAt τ d P) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v τ) : posAt τ d (Mono.shift v P) := by
  intro i y hy
  have h1 := h i (y - v) hy
  have h2 : (y - v) τ = y τ - v τ := rfl
  rw [h2] at h1
  linarith

#print axioms posAt_shift

/-- **Margin monomials**: every factor vanishes below a time `d` with `0 < d` and `r < d`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the margin. -/
abbrev MarginMono (N : ℕ) (τ : Fin 4) (r : ℝ) : Type :=
  {P : Mono N // ∃ d : ℝ, 0 < d ∧ r < d ∧ posAt τ d P}

/-- **OS2 for the flowed limit, beyond the margin.** Under `UniformBoundF` and `PosPreserving τ r`,
for every finite set of margin monomials and real coefficients, `0 ≤ ∑_{P,Q} c_P c_Q S(θP ∪ Q)`. At
each large step the sum is `ν_k(θX · X)`, `X = ∑ c_P ∏ᵢ smear aₖ (Φ_k Oᵢ) fᵢ` in the half-space
algebra, nonnegative by the reflection positivity of the periodic state; `[0, ∞)` is closed.

DERIVED: `0` is the excluded colour count, the plane and the sign concluded; `4` in `Fin 4` is the
spacetime dimension. -/
theorem contSF_gram_nonneg (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (s : Finset (MarginMono N τ r))
    (c : MarginMono N τ r → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernF hN Φ τ P.1 Q.1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have htend : Tendsto
      (fun k => ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSF hN Φ k (pairFam τ P.1 Q.1))
      (ultra : Filter ℕ) (𝓝 (∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernF hN Φ τ P.1 Q.1)) :=
    tendsto_finset_sum _ (fun P _ => tendsto_finset_sum _
      (fun Q _ => (tendsto_contSF hN Φ hB (pairFam τ P.1 Q.1)).const_mul (c P * c Q)))
  refine ge_of_tendsto htend ?_
  have hmem : ∀ᶠ k in atTop, ∀ P ∈ s, ∀ i : Fin P.1.1,
      smear (dySpacing N k) (Φ.map k (P.1.2 i).1).1 (P.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
    (Filter.eventually_all_finset s).mpr (fun P _ =>
      Filter.eventually_all.mpr (fun i => by
        obtain ⟨d, hd, hrd, hP⟩ := P.2
        exact hpos (P.1.2 i).1 (P.1.2 i).2 d hd hrd (hP i)))
  have hev : ∀ᶠ k in atTop,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSF hN Φ k (pairFam τ P.1 Q.1) := by
    filter_upwards [hmem] with k hk
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hsum : ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * latSF hN Φ k (pairFam τ P.1 Q.1)
        = ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * stateK hN k
            (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (Φ.mono k P.1))
              * prodSmear (dySpacing N k) (Φ.mono k Q.1)) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
      rw [latSF_pairFam, latSk_eq, latS_pairFam _ ha]
    have hX : (∑ P ∈ s, c P • prodSmear (dySpacing N k) (Φ.mono k P.1))
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 0 :=
      Submodule.sum_mem _ (fun P hP => Submodule.smul_mem _ _
        (HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 0 Finset.univ _
          (fun i _ => hk P hP i)))
    rw [hsum]
    exact le_of_le_of_eq (stateK_rp hN k τ _ hX)
      (gram_expand (stateK hN k) (LatticeReflection.ireflObs τ 0) s c
        (fun P => prodSmear (dySpacing N k) (Φ.mono k P.1)))
  exact hev.filter_mono ultra_le

#print axioms contSF_gram_nonneg

end Positivity

/-! ## 5. Reconstruction from a kernel -/

section Generic

variable {M : Type}

/-- The form `⟨c, d⟩ = ∑_{P,Q} c_P d_Q K(P, Q)` on finite combinations.

DERIVED: no numeral. -/
noncomputable def gForm (K : M → M → ℝ) (c d : M →₀ ℝ) : ℝ :=
  c.sum (fun P a => d.sum (fun Q b => a * b * K P Q))

/-- DERIVED: no numeral. -/
theorem gForm_add_left (K : M → M → ℝ) (c c' d : M →₀ ℝ) :
    gForm K (c + c') d = gForm K c d + gForm K c' d := by
  unfold gForm
  exact Finsupp.sum_add_index' (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

#print axioms gForm_add_left

/-- DERIVED: no numeral. -/
theorem gForm_smul_left (K : M → M → ℝ) (r : ℝ) (c d : M →₀ ℝ) :
    gForm K (r • c) d = r * gForm K c d := by
  unfold gForm
  have h1 : (r • c).sum (fun P a => d.sum (fun Q b => a * b * K P Q))
      = c.sum (fun P a => d.sum (fun Q b => (r • a) * b * K P Q)) :=
    Finsupp.sum_smul_index' (fun P => by simp)
  rw [h1, Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun P _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun Q _ => ?_)
  rw [smul_eq_mul]
  ring

#print axioms gForm_smul_left

/-- DERIVED: no numeral. -/
theorem gForm_symm (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P) (c d : M →₀ ℝ) :
    gForm K c d = gForm K d c := by
  unfold gForm
  rw [Finsupp.sum_comm c d (fun P a Q b => a * b * K P Q)]
  refine Finsupp.sum_congr (fun Q _ => Finsupp.sum_congr (fun P _ => ?_))
  simp only [hK P Q]
  ring

#print axioms gForm_symm

/-- Positivity of the form is the Gram positivity of the kernel.

DERIVED: `0` is the sign. -/
theorem gForm_nonneg (K : M → M → ℝ)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (c : M →₀ ℝ) : 0 ≤ gForm K c c := by
  show 0 ≤ ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q * K P Q
  exact hG c.support (fun P => c P)

#print axioms gForm_nonneg

/-- DERIVED: `0` is the zero combination. -/
theorem gForm_zero_left (K : M → M → ℝ) (d : M →₀ ℝ) : gForm K 0 d = 0 := by
  unfold gForm
  exact Finsupp.sum_zero_index

#print axioms gForm_zero_left

/-- DERIVED: `0` is the zero combination. -/
theorem gForm_zero_right (K : M → M → ℝ) (c : M →₀ ℝ) : gForm K c 0 = 0 := by
  simp [gForm]

#print axioms gForm_zero_right

/-- DERIVED: no numeral. -/
theorem gForm_single (K : M → M → ℝ) (P Q : M) (a b : ℝ) :
    gForm K (Finsupp.single P a) (Finsupp.single Q b) = a * b * K P Q := by
  unfold gForm
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals simp

#print axioms gForm_single

/-- **The reflection form of a symmetric Gram-positive kernel**, a `Transfer.ReflForm`.

DERIVED: `0` is the sign in `hG`. -/
noncomputable def gReflForm (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q) :
    Transfer.ReflForm (M →₀ ℝ) where
  form := gForm K
  form_symm := gForm_symm K hK
  form_add_left := gForm_add_left K
  form_smul_left := gForm_smul_left K
  form_nonneg := gForm_nonneg K hG

/-- DERIVED: no numeral. -/
theorem gForm_mapDomain_left (K : M → M → ℝ) (g : M → M) (c d : M →₀ ℝ) :
    gForm K (Finsupp.mapDomain g c) d
      = c.sum (fun P a => d.sum (fun Q b => a * b * K (g P) Q)) := by
  unfold gForm
  exact Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

#print axioms gForm_mapDomain_left

/-- DERIVED: no numeral. -/
theorem gForm_mapDomain_right (K : M → M → ℝ) (g : M → M) (c d : M →₀ ℝ) :
    gForm K c (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * K P (g Q))) := by
  unfold gForm
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

#print axioms gForm_mapDomain_right

/-- DERIVED: no numeral. -/
theorem gForm_mapDomain (K : M → M → ℝ) (g : M → M) (c d : M →₀ ℝ) :
    gForm K (Finsupp.mapDomain g c) (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * K (g P) (g Q))) := by
  rw [gForm_mapDomain_left]
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

#print axioms gForm_mapDomain

/-- The step `sh` extended linearly.

DERIVED: no numeral. -/
noncomputable def gT (sh : M → M) : (M →₀ ℝ) →ₗ[ℝ] (M →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ sh

/-- DERIVED: no numeral. -/
theorem gT_symm (K : M → M → ℝ) (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (c d : M →₀ ℝ) : gForm K (gT sh c) d = gForm K c (gT sh d) := by
  show gForm K (Finsupp.mapDomain sh c) d = gForm K c (Finsupp.mapDomain sh d)
  rw [gForm_mapDomain_left, gForm_mapDomain_right]
  refine Finsupp.sum_congr (fun P _ => Finsupp.sum_congr (fun Q _ => ?_))
  simp only [hsh]

#print axioms gT_symm

/-- DERIVED: no numeral. -/
theorem gT_iterate (sh : M → M) (n : ℕ) (c : M →₀ ℝ) :
    (⇑(gT sh))^[n] c = Finsupp.mapDomain (sh^[n]) c := by
  induction n with
  | zero => exact Finsupp.mapDomain_id.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
    show Finsupp.mapDomain sh (Finsupp.mapDomain (sh^[n]) c) = _
    rw [← Finsupp.mapDomain_comp]

#print axioms gT_iterate

/-- A step that is the square of a half step, on combinations.

DERIVED: no numeral. -/
theorem gT_half (sh sh2 : M → M) (h : ∀ P, sh2 (sh2 P) = sh P) (c : M →₀ ℝ) :
    gT sh c = gT sh2 (gT sh2 c) := by
  show Finsupp.mapDomain sh c = Finsupp.mapDomain sh2 (Finsupp.mapDomain sh2 c)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  exact (h P).symm

#print axioms gT_half

/-- The form of iterated steps is bounded uniformly in the number of steps.

DERIVED: no numeral. -/
theorem gForm_iterate_le (K : M → M → ℝ) (sh : M → M)
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C) (c : M →₀ ℝ) :
    ∃ B : ℝ, ∀ n : ℕ, gForm K ((⇑(gT sh))^[n] c) ((⇑(gT sh))^[n] c) ≤ B := by
  choose C hC using hb
  refine ⟨∑ P ∈ c.support, ∑ Q ∈ c.support, |c P| * |c Q| * C P Q, fun n => ?_⟩
  rw [gT_iterate, gForm_mapDomain]
  show ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q * K (sh^[n] P) (sh^[n] Q) ≤ _
  refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
  calc c P * c Q * K (sh^[n] P) (sh^[n] Q)
      ≤ |c P * c Q * K (sh^[n] P) (sh^[n] Q)| := le_abs_self _
    _ = |c P| * |c Q| * |K (sh^[n] P) (sh^[n] Q)| := by rw [abs_mul, abs_mul]
    _ ≤ |c P| * |c Q| * C P Q :=
        mul_le_mul_of_nonneg_left (hC P Q n) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

#print axioms gForm_iterate_le

/-- **The step contracts the form**: iterated Schwarz with the bounded orbit.

DERIVED: `0` is the sign of the Gram positivity `hG`. -/
theorem gT_contract (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C) (c : M →₀ ℝ) :
    gForm K (gT sh c) (gT sh c) ≤ gForm K c c := by
  obtain ⟨B, hB'⟩ := gForm_iterate_le K sh hb c
  exact SchwarzIteration.contract_of_bounded_orbit (gReflForm K hK hG) (⇑(gT sh))
    (gT_symm K sh hsh) c B hB'

#print axioms gT_contract

/-- **Transfer data from a kernel**: the form of `K`, the step `sh`, the vacuum `e` fixed by the step
with `K(e, e) = 1`.

DERIVED: `1` is the vacuum coefficient and its norm; `0` is the sign of the Gram positivity `hG`. -/
noncomputable def gTransfer (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C)
    (e : M) (he : sh e = e) (hee : K e e = 1) : Transfer.TransferData (M →₀ ℝ) where
  toReflForm := gReflForm K hK hG
  T := gT sh
  vac := Finsupp.single e 1
  T_symm := gT_symm K sh hsh
  T_contract := gT_contract K hK hG sh hsh hb
  T_vac := by
    show Finsupp.mapDomain sh (Finsupp.single e 1) = Finsupp.single e 1
    rw [Finsupp.mapDomain_single, he]
  vac_norm := by
    show gForm K (Finsupp.single e 1) (Finsupp.single e 1) = 1
    rw [gForm_single, one_mul, one_mul]
    exact hee

/-- **Positivity of the transfer operator**: with a half step `sh2`, `⟨c, T c⟩ = ⟨T₂c, T₂c⟩ ≥ 0`.

DERIVED: `0` is the sign; `1` is the vacuum norm `K(e, e)`. -/
theorem gPositive (K : M → M → ℝ) (hK : ∀ P Q, K P Q = K Q P)
    (hG : ∀ (s : Finset M) (c : M → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q)
    (sh : M → M) (hsh : ∀ P Q, K (sh P) Q = K P (sh Q))
    (hb : ∀ P Q, ∃ C : ℝ, ∀ n : ℕ, |K (sh^[n] P) (sh^[n] Q)| ≤ C)
    (e : M) (he : sh e = e) (hee : K e e = 1) (sh2 : M → M)
    (hsh2 : ∀ P Q, K (sh2 P) Q = K P (sh2 Q)) (hhalf : ∀ P, sh2 (sh2 P) = sh P) :
    GNSHilbert.PositiveTransfer (gTransfer K hK hG sh hsh hb e he hee) := by
  intro c
  show 0 ≤ gForm K c (gT sh c)
  rw [gT_half sh sh2 hhalf, ← gT_symm K sh2 hsh2]
  exact gForm_nonneg K hG _

#print axioms gPositive

/-- **The reconstruction conclusions** for transfer data: complete Hilbert space, unit vacuum,
self-adjoint transfer operator fixing it, spectrum in `[0, 1]`.

DERIVED: `1` is the vacuum norm and the top of the spectrum; `0` its bottom. -/
def Reconstructed {A : Type} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A) :
    Prop :=
  CompleteSpace (GNSHilbert.H D.toReflForm)
    ∧ ‖GNSHilbert.Omega D.toReflForm D.vac‖ = 1
    ∧ IsSelfAdjoint (GNSHilbert.opT D)
    ∧ GNSHilbert.opT D (GNSHilbert.Omega D.toReflForm D.vac) = GNSHilbert.Omega D.toReflForm D.vac
    ∧ spectrum ℝ (GNSHilbert.opT D) ⊆ Set.Icc 0 1

/-- **Positive transfer data reconstruct** (`GNSHilbert`).

DERIVED: `0` and `1` as in `Reconstructed`. -/
theorem reconstructed_of_positive {A : Type} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (hpos : GNSHilbert.PositiveTransfer D) : Reconstructed D :=
  ⟨GNSHilbert.complete_H _, GNSHilbert.norm_Omega_vac _, GNSHilbert.isSelfAdjoint_opT _,
    GNSHilbert.opT_Omega _,
    fun x hx => ⟨GNSHilbert.spectrum_opT_nonneg _ hpos hx,
      (GNSHilbert.spectrum_opT_subset_unit_interval _ hx).2⟩⟩

#print axioms reconstructed_of_positive

/-- The vector of `P` in the reconstructed Hilbert space.

DERIVED: `1` the coefficient, `0` the imaginary component. -/
noncomputable def gVec (D : Transfer.TransferData (M →₀ ℝ)) (P : M) :
    GNSHilbert.H D.toReflForm :=
  ((GNSHilbert.Pre.ofPair D.toReflForm (Finsupp.single P 1) 0 : GNSHilbert.Pre D.toReflForm)
    : GNSHilbert.H D.toReflForm)

/-- **The reconstruction reads the kernel**: `⟪gVec P, gVec Q⟫ = K(P, Q)` whenever the form of `D`
is the form of `K`.

DERIVED: `1` the coefficients, `0` the imaginary parts. -/
theorem inner_gVec (D : Transfer.TransferData (M →₀ ℝ)) (K : M → M → ℝ)
    (hD : ∀ c d, D.form c d = gForm K c d) (P Q : M) :
    inner ℂ (gVec D P) (gVec D Q) = (K P Q : ℂ) := by
  unfold gVec
  rw [GNSHilbert.inner_coe]
  refine OSPositivity.ceq ?_ ?_
  · rw [OSPositivity.cform_re, Complex.ofReal_re]
    show D.form (Finsupp.single P 1) (Finsupp.single Q 1) + D.form 0 0 = K P Q
    rw [hD, hD, gForm_single, gForm_zero_left, one_mul, one_mul, add_zero]
  · rw [OSPositivity.cform_im, Complex.ofReal_im]
    show D.form (Finsupp.single P 1) 0 - D.form 0 (Finsupp.single Q 1) = 0
    rw [hD, hD, gForm_zero_right, gForm_zero_left, sub_zero]

#print axioms inner_gVec

end Generic

/-! ## 6. The flowed reconstruction -/

section FlowReconstruction

/-- The forward time step of a margin monomial by `dySpacing N m` in direction `τ`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The body steps
by one unit time step, whose time component is non-negative. -/
def MarginMono.shift (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) {r : ℝ} (P : MarginMono N τ r) :
    MarginMono N τ r :=
  ⟨Mono.shift (timeVec N m τ 1) P.1, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, posAt_shift hP (by
      rw [timeVec_self]
      exact mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) m).le (by norm_num))⟩⟩

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem MarginMono.shift_iterate (hN : N ≠ 0) (τ : Fin 4) (m n : ℕ) {r : ℝ}
    (P : MarginMono N τ r) :
    ((MarginMono.shift hN τ m)^[n] P).1 = Mono.shift (timeVec N m τ n) P.1 := by
  induction n with
  | zero =>
    show P.1 = Mono.shift (timeVec N m τ ((0 : ℕ) : ℤ)) P.1
    rw [Nat.cast_zero, timeVec_zero, Mono.shift_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show Mono.shift (timeVec N m τ 1) ((MarginMono.shift hN τ m)^[n] P).1 = _
    rw [ih, Mono.shift_shift, timeVec_add, Nat.cast_succ]

#print axioms MarginMono.shift_iterate

/-- Two half steps are one step, on margin monomials.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `1` is the
half-step offset. -/
theorem MarginMono.shift_half (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) {r : ℝ} (P : MarginMono N τ r) :
    MarginMono.shift hN τ (m + 1) (MarginMono.shift hN τ (m + 1) P) = MarginMono.shift hN τ m P := by
  apply Subtype.ext
  show Mono.shift (timeVec N (m + 1) τ 1) (Mono.shift (timeVec N (m + 1) τ 1) P.1)
    = Mono.shift (timeVec N m τ 1) P.1
  rw [Mono.shift_shift, timeVec_one_add]

#print axioms MarginMono.shift_half

/-- The empty margin monomial, the vacuum before completion.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the number of factors and the
sign of the margin. CHOSEN: the margin `max r 0 + 1`; the empty family has no factor, so every margin
above `max r 0` serves. -/
def emptyMargin (N : ℕ) (τ : Fin 4) (r : ℝ) : MarginMono N τ r :=
  ⟨⟨0, Fin.elim0⟩, max r 0 + 1, by linarith [le_max_right r 0], by linarith [le_max_left r 0],
    fun i => i.elim0⟩

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem shift_emptyMargin (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) {r : ℝ} :
    MarginMono.shift hN τ m (emptyMargin N τ r) = emptyMargin N τ r :=
  Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0))

#print axioms shift_emptyMargin

/-- **The time step is symmetric for the flowed kernel**: `S(θ(TP) ∪ Q) = S(θP ∪ TQ)`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `1` is the
unit step. -/
theorem kernF_shift (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (m : ℕ) (P Q : Mono N) :
    kernF hN Φ τ (Mono.shift (timeVec N m τ 1) P) Q
      = kernF hN Φ τ P (Mono.shift (timeVec N m τ 1) Q) := by
  unfold kernF
  rw [pairFam_shift]
  exact contSF_translate hN Φ _ m (axisVec τ (-1))

#print axioms kernF_shift

/-- The flowed kernel of iterated steps is bounded uniformly in the number of steps.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem kernF_iterate_bound (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (m : ℕ) (P Q : MarginMono N τ r) :
    ∃ C : ℝ, ∀ n : ℕ,
      |kernF hN Φ τ ((MarginMono.shift hN τ m)^[n] P).1 ((MarginMono.shift hN τ m)^[n] Q).1|
        ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_contSF_le hN Φ hB (pairFam τ P.1 Q.1)
  refine ⟨C, fun n => ?_⟩
  unfold kernF
  rw [MarginMono.shift_iterate, MarginMono.shift_iterate, pairFam_shiftN]
  exact hC m _

#print axioms kernF_iterate_bound

/-- `S(∅) = 1` for the flowed functions: the empty family reads `ν_k(1) = 1` at every step.

DERIVED: `1` is the normalisation of a state; `0` is the excluded colour count; `4` in `Fin 4` is the
spacetime dimension. -/
theorem kernF_empty (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) :
    kernF hN Φ τ (emptyMargin N τ r).1 (emptyMargin N τ r).1 = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hconst : ∀ k,
      latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 (emptyMargin N τ r).1) = 1 := by
    intro k
    show stateK hN k (∏ x : Fin 0 ⊕ Fin 0, _) = 1
    rw [Fintype.prod_empty]
    exact (stateK hN k).map_one
  have hfun : (fun k => latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 (emptyMargin N τ r).1))
      = fun _ => (1 : ℝ) := funext hconst
  show limUnder (ultra : Filter ℕ)
      (fun k => latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 (emptyMargin N τ r).1)) = 1
  rw [hfun]
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨1, tendsto_const_nhds⟩) tendsto_const_nhds

#print axioms kernF_empty

/-- **The flowed transfer data at the dyadic step `dySpacing N m`**, on margin monomials, from
`gTransfer` with the flowed kernel.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def flowTransfer (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m : ℕ) :
    Transfer.TransferData (MarginMono N τ r →₀ ℝ) :=
  gTransfer (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
    (fun P Q => kernF_symm hN Φ τ P.1 Q.1)
    (fun s c => contSF_gram_nonneg hN Φ hB τ hpos s c)
    (MarginMono.shift hN τ m) (fun P Q => kernF_shift hN Φ τ m P.1 Q.1)
    (fun P Q => kernF_iterate_bound hN Φ hB τ m P Q)
    (emptyMargin N τ r) (shift_emptyMargin hN τ m) (kernF_empty hN Φ τ r)

/-- **The flowed transfer operator is positive**, the step `m + 1` being the half step.

DERIVED: `1` is the half-step offset; `0` is the excluded colour count; `4` in `Fin 4` is the
spacetime dimension. -/
theorem flowTransfer_positive (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m : ℕ) :
    GNSHilbert.PositiveTransfer (flowTransfer hN Φ hB τ hpos m) :=
  gPositive (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
    (fun P Q => kernF_symm hN Φ τ P.1 Q.1)
    (fun s c => contSF_gram_nonneg hN Φ hB τ hpos s c)
    (MarginMono.shift hN τ m) (fun P Q => kernF_shift hN Φ τ m P.1 Q.1)
    (fun P Q => kernF_iterate_bound hN Φ hB τ m P Q)
    (emptyMargin N τ r) (shift_emptyMargin hN τ m) (kernF_empty hN Φ τ r)
    (MarginMono.shift hN τ (m + 1)) (fun P Q => kernF_shift hN Φ τ (m + 1) P.1 Q.1)
    (fun P => MarginMono.shift_half hN τ m P)

#print axioms flowTransfer_positive

/-- **Requirement E from a flow, what is built.** For every flow with the uniform bound, keeping the
positive half-space beyond a margin `r`, every time direction `τ` and every dyadic step
`dySpacing N m`, from the flowed limit Schwinger functions: a complete Hilbert space, a unit vacuum,
a self-adjoint transfer operator fixing it with spectrum in `[0, 1]`, and
`⟪gVec P, gVec Q⟫ = S(θP ∪ Q)` on margin monomials.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem flow_reconstruction (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m : ℕ) :
    Reconstructed (flowTransfer hN Φ hB τ hpos m)
      ∧ ∀ P Q : MarginMono N τ r,
        inner ℂ (gVec (flowTransfer hN Φ hB τ hpos m) P) (gVec (flowTransfer hN Φ hB τ hpos m) Q)
          = (kernF hN Φ τ P.1 Q.1 : ℂ) :=
  ⟨reconstructed_of_positive _ (flowTransfer_positive hN Φ hB τ hpos m),
    fun P Q => inner_gVec (flowTransfer hN Φ hB τ hpos m)
      (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (fun _ _ => rfl) P Q⟩

#print axioms flow_reconstruction

/-- **The reconstruction from a flow of physical range `r`**: `flow_reconstruction` with
`PosPreserving` from `Flow.posPreserving_of_physRange`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem flow_reconstruction_physRange (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    {r : ℝ} (hΦ : Φ.PhysRange r) (τ : Fin 4) (m : ℕ) :
    Reconstructed (flowTransfer hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hΦ τ) m) :=
  (flow_reconstruction hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hΦ τ) m).1

#print axioms flow_reconstruction_physRange

end FlowReconstruction

/-! ## 7. The open inputs -/

section Open

/-- **The flowed limit exists along the whole sequence (stated, not proved).** For every family the
flowed lattice functions converge as the step grows.

DERIVED: `0` is the excluded colour count. -/
def FlowConverges (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), ∃ L : ℝ,
    Tendsto (fun k => latSF hN Φ k F) atTop (𝓝 L)

/-- **The beacon (stated, not proved).** For every family the flowed lattice functions form a Cauchy
sequence in the step: every zoom level reads the same flowed signal, up to an error that vanishes as
both spacings shrink. Its quantifier includes coincident supports. For `Flow.ofConfScaled W_t canonZ c`,
`W_t` the localised gradient flow at a fixed physical time `t > 0`, it is expected over all families:
the flowed composite is smooth at the scale `√(8t)`, so overlapping test functions integrate a bounded
flowed correlator. At zero flow time it is, through `latSF_zeroFlow`, the Cauchy form of
`Beacon.SchwingerBeacon` for `Renorm ⟨z, c⟩`, expected to fail at coincident supports under the
canonical factor.

DERIVED: `0` is the excluded colour count. -/
def FlowBeacon (hN : N ≠ 0) (Φ : Flow N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), CauchySeq (fun k => latSF hN Φ k F)

/-- The beacon gives convergence (`ℝ` is complete).

DERIVED: `0` is the excluded colour count. -/
theorem flowConverges_of_beacon (hN : N ≠ 0) (Φ : Flow N) (h : FlowBeacon hN Φ) :
    FlowConverges hN Φ := by
  intro ι _ F
  exact cauchySeq_tendsto_of_complete (h ι F)

#print axioms flowConverges_of_beacon

/-- **Under convergence the ultrafilter limit is the limit**: the flowed lattice functions tend to
`contSF` along `atTop`. No uniform bound enters.

DERIVED: `0` is the excluded colour count. -/
theorem tendsto_atTop_contSF (hN : N ≠ 0) (Φ : Flow N) (hconv : FlowConverges hN Φ) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    Tendsto (fun k => latSF hN Φ k F) atTop (𝓝 (contSF hN Φ F)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨L, hL⟩ := hconv ι F
  have hU : Tendsto (fun k => latSF hN Φ k F) (ultra : Filter ℕ) (𝓝 L) := hL.mono_left ultra_le
  have hEq : contSF hN Φ F = L := hU.limUnder_eq
  rw [hEq]
  exact hL

#print axioms tendsto_atTop_contSF

/-- **Under convergence the limit does not depend on the ultrafilter**: every ultrafilter below
`atTop` gives `contSF`.

DERIVED: `0` is the excluded colour count. -/
theorem limUnder_eq_contSF (hN : N ≠ 0) (Φ : Flow N) (hconv : FlowConverges hN Φ)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) {ι : Type} [Fintype ι]
    (F : ι → SField N) :
    limUnder (U : Filter ℕ) (fun k => latSF hN Φ k F) = contSF hN Φ F := by
  haveI : (U : Filter ℕ).NeBot := U.neBot'
  exact ((tendsto_atTop_contSF hN Φ hconv F).mono_left hU).limUnder_eq

#print axioms limUnder_eq_contSF

/-- **Non-triviality of the flowed limit (stated, not proved).** Some margin monomial `Q` has
`S(θQ ∪ Q) − S(Q)² ≠ 0`, with `S(Q) = S(θ∅ ∪ Q)`.

DERIVED: `0` is the excluded colour count and the value excluded; `2` the square; `4` in `Fin 4` is
the spacetime dimension. -/
def FlowConnectedNonzero (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) : Prop :=
  ∃ Q : MarginMono N τ r,
    kernF hN Φ τ Q.1 Q.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1 ^ 2 ≠ 0

/-- **Non-triviality of the flowed reconstruction.** Under `FlowConnectedNonzero`, at every dyadic
step the Hilbert space has a non-zero vector orthogonal to the vacuum and not a complex multiple of
it.

DERIVED: `0` is the vanishing pairing, the zero vector and the excluded colour count; `1` the
vacuum coefficient; `2` the square; `4` in `Fin 4` is the spacetime dimension. -/
theorem exists_orth_ne_zero_flow (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m : ℕ) (h : FlowConnectedNonzero hN Φ τ r) :
    ∃ u : GNSHilbert.H (flowTransfer hN Φ hB τ hpos m).toReflForm,
      inner ℂ (GNSHilbert.Omega (flowTransfer hN Φ hB τ hpos m).toReflForm
        (flowTransfer hN Φ hB τ hpos m).vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega (flowTransfer hN Φ hB τ hpos m).toReflForm
        (flowTransfer hN Φ hB τ hpos m).vac := by
  obtain ⟨Q, hQ⟩ := h
  have hx : (flowTransfer hN Φ hB τ hpos m).form (Finsupp.single Q 1) (Finsupp.single Q 1)
      - (flowTransfer hN Φ hB τ hpos m).form (Finsupp.single Q 1)
          (flowTransfer hN Φ hB τ hpos m).vac ^ 2 ≠ 0 := by
    show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
        (Finsupp.single Q 1) (Finsupp.single Q 1)
      - gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
        (Finsupp.single Q 1) (Finsupp.single (emptyMargin N τ r) 1) ^ 2 ≠ 0
    rw [gForm_single, gForm_single]
    simp only [one_mul]
    show kernF hN Φ τ Q.1 Q.1 - kernF hN Φ τ Q.1 (emptyMargin N τ r).1 ^ 2 ≠ 0
    rw [← kernF_symm hN Φ τ (emptyMargin N τ r).1 Q.1]
    exact hQ
  obtain ⟨u, hu, hu0⟩ := ContinuumSep.exists_orth_ne_zero (flowTransfer hN Φ hB τ hpos m) _ hx
  exact ⟨u, hu, hu0, ContinuumSep.not_mem_span_vac _ hu hu0⟩

#print axioms exists_orth_ne_zero_flow

/-- **The connected flowed two-point kernel of step `k`** between the reflected flowed field at site
`x` and the flowed field at site `y`: `ν_k(T_x θ(Φ_k O) · T_y (Φ_k O)) − ν_k(Φ_k O)²`,
`θ = ireflObs τ 0`.

DERIVED: `0` is the excluded colour count and the reflection constant; `2` the square of the
one-point function; `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def latKernelF (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (k : ℕ) (x y : ISite) : ℝ :=
  stateK hN k (transObs x (LatticeReflection.ireflObs τ 0 (Φ.map k O).1) * transObs y (Φ.map k O).1)
    - stateK hN k (Φ.map k O).1 ^ 2

/-- **The flowed kernel under a sup-norm bound**: `|latKernelF| ≤ 2B²` at every separation,
coincident sites included, when `‖Φ_k O‖ ≤ B`.

DERIVED: `2` counts the two terms, each at most `B²`, the square of the field bound; `0` is the
excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_latKernelF_le (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (k : ℕ) (x y : ISite) {B : ℝ} (hO : ‖(Φ.map k O).1‖ ≤ B) :
    |latKernelF hN Φ τ O k x y| ≤ 2 * B ^ 2 := by
  have hθ : ‖LatticeReflection.ireflObs τ 0 (Φ.map k O).1‖ ≤ ‖(Φ.map k O).1‖ :=
    (ContinuousMap.norm_le (LatticeReflection.ireflObs τ 0 (Φ.map k O).1)
      (norm_nonneg (Φ.map k O).1)).mpr
      (fun U => (Φ.map k O).1.norm_coe_le_norm (LatticeReflection.ireflConf τ 0 U))
  have hA : ‖transObs x (LatticeReflection.ireflObs τ 0 (Φ.map k O).1)‖ ≤ B :=
    ((norm_transObs_le _ _).trans hθ).trans hO
  have hB : ‖transObs y (Φ.map k O).1‖ ≤ B := (norm_transObs_le _ _).trans hO
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hO
  have h1 : |stateK hN k (transObs x (LatticeReflection.ireflObs τ 0 (Φ.map k O).1)
      * transObs y (Φ.map k O).1)| ≤ B ^ 2 := by
    refine ((stateK hN k).abs_le_norm _).trans ((norm_mul_le _ _).trans ?_)
    rw [sq]
    exact mul_le_mul hA hB (norm_nonneg _) hB0
  have h2 : stateK hN k (Φ.map k O).1 ^ 2 ≤ B ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (((stateK hN k).abs_le_norm (Φ.map k O).1).trans hO) 2
    rwa [sq_abs] at h
  have h3 : 0 ≤ stateK hN k (Φ.map k O).1 ^ 2 := sq_nonneg _
  have h4 := abs_le.mp h1
  unfold latKernelF
  rw [abs_le]
  constructor <;> linarith [h4.1, h4.2]

#print axioms abs_latKernelF_le

/-- The connected subtraction `ν_k(O)` is reflection compatible, by the reflection invariance of the
periodic state.

DERIVED: `0` is the excluded colour count and the reflection constant; `4` in `Fin 4` is the
spacetime dimension. -/
theorem stateK_refl_field (hN : N ≠ 0) (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) :
    stateK hN k (O.refl τ).1 = stateK hN k O.1 :=
  PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0 O.1

#print axioms stateK_refl_field

/-- **At zero flow time with the connected subtraction the flowed kernel is
`ContinuumNontrivial.latKernel`** for `Renorm.connected hN z`: `z² ν(T_x θG · T_y G)` with
`G = O − ν_k(O)`, whose mean vanishes.

DERIVED: `0` is the excluded colour count, the zero flow time and the vanishing mean; `2` the square
of the factor; `4` in `Fin 4` is the spacetime dimension. -/
theorem latKernelF_zeroFlow_connected (hN : N ≠ 0) (z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hz : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), z k (O.refl τ) = z k O)
    (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (k : ℕ) (x y : ISite) :
    latKernelF hN (Flow.ofConfScaled (ConfFlow.identity N) z (fun k O => stateK hN k O.1) hz
        (fun k τ O => stateK_refl_field hN k τ O)) τ O k x y
      = ContinuumNontrivial.latKernel hN (Renorm.connected hN z) τ O k x y := by
  have hmap : ((Flow.ofConfScaled (ConfFlow.identity N) z (fun k O => stateK hN k O.1) hz
      (fun k τ O => stateK_refl_field hN k τ O)).map k O).1
        = z k O • (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))) :=
    ContinuousMap.ext (fun U => rfl)
  have hG0 : stateK hN k (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))) = 0 := by
    rw [(stateK hN k).map_sub, (stateK hN k).map_smul, (stateK hN k).map_one, mul_one, sub_self]
  unfold latKernelF
  rw [hmap]
  show stateK hN k (transObs x (LatticeReflection.ireflObs τ 0
        (z k O • (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ)))))
      * transObs y (z k O • (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ)))))
      - stateK hN k (z k O • (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ)))) ^ 2
    = z k O ^ 2 * stateK hN k (transObs x (LatticeReflection.ireflObs τ 0
        (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))))
      * transObs y (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))))
  rw [map_smul, map_smul, map_smul, smul_mul_smul_comm, (stateK hN k).map_smul,
    (stateK hN k).map_smul, hG0]
  ring

#print axioms latKernelF_zeroFlow_connected

/-- **Uniform convergence of the flowed kernel on a set of physical pairs (stated, not proved).**
For every `ε > 0`, eventually in the step, `|latKernelF k x y − G₂(a x, a y)| ≤ ε` for every pair of
sites whose physical points `(a x, a y)`, `a = dySpacing N k`, lie in `A`. The flowed form of
`ContinuumNontrivial.KernelLimitOn`.

DERIVED: `0` is the excluded colour count and the sign of `ε`; `4` in `Fin 4` is the spacetime
dimension. -/
def FlowKernelLimitOn (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) (A : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x y : ISite,
    (site (dySpacing N k) x, site (dySpacing N k) y) ∈ A →
      |latKernelF hN Φ τ O k x y - G₂ (site (dySpacing N k) x) (site (dySpacing N k) y)| ≤ ε

/-- **The open input for non-triviality: the flowed kernel converges on every bounded box (stated,
not proved).** For every radius `R`, `latKernelF → G₂` uniformly on `sepBoxSet 0 R`, which contains
coincident points. At zero flow time with the connected subtraction it is
`ContinuumNontrivial.KernelConvergesSep` for `Renorm.connected` extended to separation `0`
(`latKernelF_zeroFlow_connected`).

DERIVED: `0` is the separation, admitting coincident points, and the excluded colour count; `4` in
`Fin 4` is the spacetime dimension. -/
def FlowKernelConverges (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ R : ℝ, FlowKernelLimitOn hN Φ τ O G₂ (ContinuumNontrivial.sepBoxSet 0 R)

/-- A limit on a set is a limit on every subset.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem flowKernelLimitOn_mono (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    {A B : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ))} (hAB : A ⊆ B)
    (h : FlowKernelLimitOn hN Φ τ O G₂ B) : FlowKernelLimitOn hN Φ τ O G₂ A := by
  intro ε hε
  filter_upwards [h ε hε] with k hk
  exact fun x y hxy => hk x y (hAB hxy)

#print axioms flowKernelLimitOn_mono

/-- **The separated form**: `FlowKernelConverges` gives the flowed limit on every separated box
`sepBoxSet d R`, `d ≥ 0`, the shape `KernelConvergesSep` asks for.

DERIVED: `0` is the least separation and the excluded colour count; `4` in `Fin 4` is the spacetime
dimension. -/
theorem flowKernelLimitOn_sep (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    (h : FlowKernelConverges hN Φ τ O G₂) (d R : ℝ) (hd : 0 ≤ d) :
    FlowKernelLimitOn hN Φ τ O G₂ (ContinuumNontrivial.sepBoxSet d R) := by
  refine flowKernelLimitOn_mono hN Φ τ O G₂ ?_ (h R)
  rintro ⟨p, q⟩ hpq
  obtain ⟨⟨i, hi⟩, hbox⟩ := ContinuumNontrivial.mem_sepBoxSet.mp hpq
  exact ContinuumNontrivial.mem_sepBoxSet.mpr ⟨⟨i, le_trans hd hi⟩, hbox⟩

#print axioms flowKernelLimitOn_sep

/-- **A limit of the kernel of a bounded flow is bounded**: if `‖Φ_k O‖ ≤ B` at every step, then
under `FlowKernelLimitOn` on `A`, for every `ε > 0`, eventually `|G₂(a x, a y)| ≤ 2B² + ε` on the
lattice pairs in `A`.

DERIVED: `2` as in `abs_latKernelF_le`; `0` is the sign of `ε` and the excluded colour count; `4` in
`Fin 4` is the spacetime dimension. -/
theorem eventually_abs_G_le (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    {A : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ))} (h : FlowKernelLimitOn hN Φ τ O G₂ A) {B : ℝ}
    (hBd : ∀ k, ‖(Φ.map k O).1‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x y : ISite, (site (dySpacing N k) x, site (dySpacing N k) y) ∈ A →
      |G₂ (site (dySpacing N k) x) (site (dySpacing N k) y)| ≤ 2 * B ^ 2 + ε := by
  filter_upwards [h ε hε] with k hk
  intro x y hxy
  have h1 := abs_le.mp (hk x y hxy)
  have h2 := abs_le.mp (abs_latKernelF_le hN Φ τ O k x y (hBd k))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

#print axioms eventually_abs_G_le

end Open

end MassGap.ContinuumFlow
