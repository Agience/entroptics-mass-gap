import Mathlib
import MassGap.BoxWhole

/-!
# MassGap.ReplicaTwist — the second moment of the box twist ratio, exactly

`BoxWhole` option (B): `γ_Λ R = boxRatio` (`wspec_reweight`), so `ν(boxRatio) = ν(R)` (`mean_boxRatio`),
and `ν((boxRatio − 1)²) ≤ ν((R − 1)²)` (`mean_sq_boxRatio_le`, Jensen). This module computes the second
moment without Jensen.

## Objects

* `boxWeightR β Λ τ hτc ω u = R(splice u ω) · wt(u, ω)`: one box copy at boundary `ω`, weighted, with the
  twist reweighting `R` inserted.
* `replica Λ = vol Λ ⊗ vol Λ`: two independent box copies. At a fixed boundary `ω` both copies see the same
  `ω`; the integrand `boxWeightR(z.1) · boxWeightR(z.2)` is the two-replica integrand.
* `ExtLocal Λ h`: `h` reads no link of `Λ` (`h (splice Λ u ω) = h ω`).
* `B = wspec R` (`= boxRatio` pointwise, `wspec_reweight`), `R = reweight`.

## What is proved

1. **Replica identity** (`boxRatio_sq_replica`): `boxRatio(ω)² = (∫ boxWeightR(z.1) boxWeightR(z.2) d replica)
   / Z_Λ(ω)²`, i.e. `boxRatio² = (γ_Λ ⊗ γ_Λ)(R ⊗ R)` at the same `ω` (Fubini on the product of the two box
   volumes, then `num_reweight`).
2. **DLR with one replica as the system** (`mean_local_mul_wspec`, `replica_mean`): for every `ExtLocal`
   `h`, `ν(h · γ_Λ X) = ν(h · X)`. With `h = B`: `ν(B²) = ν(B · R)`. So the two-replica mean is a
   one-system expectation with the other replica's ratio inserted as an exterior observable.
3. **Exact second moment** (`mean_sq_eq_cross`): for every constant `c`,
   `ν((B − c)²) = ν((B − c)(R − c))`. At `c = 1`: `ν((boxRatio − 1)²) = ν(B R) − 2 ν(R) + 1
   = ν((B − 1)(R − 1))` (`mean_sq_sub_one`). At `c = ν(R)` it is `Var_ν(B) = Cov_ν(R, γ_Λ R)`, the
   instance `X = R` of `BoxFocusTest.kernel_var_eq_cov`.
4. **Lower bound** (`mean_sq_ge`): `(ν(R) − 1)² ≤ ν((boxRatio − 1)²)`. A typical-set `BoundaryV` (small
   `ν((boxRatio − 1)²)`) needs `ν(R)` near `1`; the first moment is a necessary input.
5. **`ℤ₂` involution** (`boxRatio_mul_twist`): if `τ ∘ τ = id` linkwise, `boxRatio(ω) · boxRatio(τ ω) = 1`.

## Evaluation

* (1)–(3) keep the cancellation: `ν((boxRatio − 1)²) = ν((B − 1)(R − 1))` is exact. Splitting at
  `m = ν(R)`: `ν((boxRatio − 1)²) = Var_ν(B) + (m − 1)²`, with `Var_ν(B) = Cov_ν(R, γ_Λ R)` (proved, item 3).
* The variance part is a covariance of `ν` between `R` and its own box kernel. `R` reads the links of the
  box-boundary plaquettes and `γ_Λ R` reads the links next to the box, so the two overlap and there is no
  separation for a decay estimate to use. This has the form `BoxFocusTest` identified as circular
  (`kernel_var_eq_cov`, `meanFocus_eq`): bounding it is a statement about covariances of `ν` at the box
  scale. (Argued: the identity is proved; its circularity is the `BoxFocusTest` classification.)
* The mean part `(ν(R) − 1)²` is not a covariance. What `ν(R)` is (argued, not formalised): for a centre
  twist `τ_l = z_l ·` on a link set `S` outside the box, every plaquette holonomy changes by the centre
  element `z_p = ∏_{l ∈ p ∩ S} z_l^{±1}`, so `ν(R) = Z[F]/Z`, the periodic partition function with the
  flux `z_p` inserted on `F = {p ∈ boundaryPlaqs Λ : z_p ≠ 1}`, over `Z`. A centre change of variables on
  the whole system moves `F` by a coboundary and keeps its dual boundary `C = ∂*F` fixed, so
  `ν(R) = ⟨T(C)⟩`, an 't Hooft loop. `F` is the dual sheet `δS` cut by the one-plaquette shell
  `boundaryPlaqs Λ`, so `C` is the pair of antiparallel curves where `δS` crosses the two faces of that shell,
  each of length of order the box size in lattice units. `C` is empty only if `F` is empty (then `R = 1`).
* Relation to `zR` (`FluxCost.VortexCostAt`), argued: `zR` is `Z[F']/Z` for `F'` a closed homologically
  non-trivial dual surface on the torus (`∂*F' = ∅`); `ν(R)` has `∂*F = C ≠ ∅`. No centre change of
  variables relates them (it fixes `∂*`), and no closing of the box sheet removes `C` (closing `S` around the
  contractible box gives a gauge transformation with `F` a coboundary, ratio `1`). In 't Hooft's phase
  classification `zR → 1` (magnetic flux free) and a perimeter law for `⟨T(C)⟩` hold together in the
  confined phase, so (V) does not bound `ν(R)` near `1`. Reflection-positivity bounds of the
  Tomboulis–Yaffe type run from the vortex free energy to Wilson loops, not to 't Hooft loops near `1`.
* Consequence for (B) (argued): with a perimeter law `⟨T(C)⟩ ≈ e^{−μ |C|}` and `|C|` of order `b/a(β)`, `ν(R)`
  tends to `0`, not `1`, as `β → ∞` at fixed physical size; by item 4 `ν((boxRatio − 1)²)` then tends to at
  least `1`. Option (B) then fails at the first moment, before Jensen enters.

## What remains for option (B)

Two inputs, both named, neither proved:
* `ν(R)` near `1`: a 't Hooft-loop expectation `⟨T(C)⟩` for the shell-hugging curve pair `C`. Not circular
  (not a covariance), but argued false at weak coupling (perimeter law in lattice units).
* `Var_ν(B) = Cov_ν(R, γ_Λ R)` small: a box-scale covariance of `ν`, the form `BoxFocusTest` classifies as
  circular.

No sorry, no axioms beyond Lean's standard three.

DERIVED (module-wide): `2` in `ν(B R) − 2 ν(R) + 1` is the binomial coefficient of `(B − 1)²` (with
`ν(B) = ν(R)`); `1` is the untwisted ratio.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ReplicaTwist

open MeasureTheory
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.PeriodicStateDLR (wspec wspec_apply periodicState_dlr)
open MassGap.PeriodicState (periodicState)
open MassGap.SUN (SU)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.WilsonDLR (twistConf)
open MassGap.FocusZoom (wspec_mul_outside)
open MassGap.BoxFocusTest (wspec_splice_self)
open MassGap.BoxWhole

variable {N : ℕ}

/-! ## 1. Two box copies at one boundary -/

/-- One box copy at boundary `ω`, weighted, with `R` inserted: `R(splice u ω) · wt(u, ω)`. -/
def boxWeightR (β : ℝ) (Λ : Finset ILink) (τ : ILink → SU N ≃ᵐ SU N) (hτc : ∀ l, Continuous (τ l))
    (ω : IConf (SU N)) (u : VConf (SU N) Λ) : ℝ :=
  reweight β Λ τ hτc (splice Λ u ω) * wt (wilsonDensity (N := N)) β Λ u ω

/-- Two independent box copies. -/
def replica (Λ : Finset ILink) : Measure (VConf (SU N) Λ × VConf (SU N) Λ) :=
  (vol (probHaar (SU N)) Λ).prod (vol (probHaar (SU N)) Λ)

/-- **Replica identity**: `boxRatio(ω)² = (γ_Λ ⊗ γ_Λ)(R ⊗ R)(ω)`, two box copies sharing `ω`. -/
theorem boxRatio_sq_replica (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) (ω : IConf (SU N)) :
    boxRatio β Λ τ ω ^ 2
      = (∫ z, boxWeightR β Λ τ hτc ω z.1 * boxWeightR β Λ τ hτc ω z.2 ∂(replica Λ))
        / boxPart β Λ ω ^ 2 := by
  have hn : (∫ u, boxWeightR β Λ τ hτc ω u ∂(vol (probHaar (SU N)) Λ))
      = boxPart β Λ (twistBd τ ω) := num_reweight β hτc hτΛ ω
  rw [replica, integral_prod_mul (boxWeightR β Λ τ hτc ω) (boxWeightR β Λ τ hτc ω), hn, boxRatio,
    div_pow, sq, sq]

/-! ## 2. DLR with one replica as the system -/

/-- `h` reads no link of `Λ`. -/
def ExtLocal (Λ : Finset ILink) (h : C(IConf (SU N), ℝ)) : Prop :=
  ∀ (u : VConf (SU N) Λ) (ω : IConf (SU N)), h (splice Λ u ω) = h ω

theorem extLocal_wspec (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (f : C(IConf (SU N), ℝ)) :
    ExtLocal Λ (wspec hN β Λ f) :=
  fun u ω => wspec_splice_self hN β Λ f u ω

theorem extLocal_sub_const {Λ : Finset ILink} {h : C(IConf (SU N), ℝ)} (hh : ExtLocal Λ h) (c : ℝ) :
    ExtLocal Λ (h - ContinuousMap.const (IConf (SU N)) c) := fun u ω => by
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, hh u ω]

/-- **An exterior observable passes through the box kernel in mean**: `ν(h · γ_Λ X) = ν(h · X)`. -/
theorem mean_local_mul_wspec (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) {h : C(IConf (SU N), ℝ)}
    (hh : ExtLocal Λ h) (X : C(IConf (SU N), ℝ)) :
    periodicState hN β (h * wspec hN β Λ X) = periodicState hN β (h * X) := by
  have e := wspec_mul_outside hN β Λ X h hh
  calc periodicState hN β (h * wspec hN β Λ X)
      = periodicState hN β (wspec hN β Λ X * h) := by rw [mul_comm]
    _ = periodicState hN β (wspec hN β Λ (X * h)) := by rw [e]
    _ = periodicState hN β (X * h) := periodicState_dlr hN β Λ _
    _ = periodicState hN β (h * X) := by rw [mul_comm]

/-- **The two-replica mean is a one-system expectation**: with `B = γ_Λ R` (`= boxRatio`),
`B(ω)²` is the replica integral over `Z_Λ(ω)²` at every `ω`, and `ν(B²) = ν(B R)`. -/
theorem replica_mean (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) (hτΛ : ∀ l ∈ Λ, ∀ g, τ l g = g) :
    (∀ ω, (wspec hN β Λ (reweight β Λ τ hτc) * wspec hN β Λ (reweight β Λ τ hτc)) ω
      = (∫ z, boxWeightR β Λ τ hτc ω z.1 * boxWeightR β Λ τ hτc ω z.2 ∂(replica Λ))
        / boxPart β Λ ω ^ 2) ∧
    periodicState hN β (wspec hN β Λ (reweight β Λ τ hτc) * wspec hN β Λ (reweight β Λ τ hτc))
      = periodicState hN β (wspec hN β Λ (reweight β Λ τ hτc) * reweight β Λ τ hτc) := by
  refine ⟨fun ω => ?_, mean_local_mul_wspec hN β Λ (extLocal_wspec hN β Λ _) _⟩
  rw [ContinuousMap.mul_apply, wspec_reweight hN β hτc hτΛ, ← sq, boxRatio_sq_replica β hτc hτΛ]

/-! ## 3. The exact second moment -/

/-- **Exact second moment about any constant**: `ν((B − c)²) = ν((B − c)(R − c))`, `B = γ_Λ R`. -/
theorem mean_sq_eq_cross (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (R : C(IConf (SU N), ℝ)) (c : ℝ) :
    periodicState hN β ((wspec hN β Λ R - ContinuousMap.const _ c) *
        (wspec hN β Λ R - ContinuousMap.const _ c))
      = periodicState hN β ((wspec hN β Λ R - ContinuousMap.const _ c) *
        (R - ContinuousMap.const _ c)) := by
  have hl := extLocal_sub_const (extLocal_wspec hN β Λ R) c
  have key := mean_local_mul_wspec hN β Λ hl R
  have e : (wspec hN β Λ R - ContinuousMap.const _ c) * (wspec hN β Λ R - ContinuousMap.const _ c)
      = (wspec hN β Λ R - ContinuousMap.const _ c) * (R - ContinuousMap.const _ c)
        + ((wspec hN β Λ R - ContinuousMap.const _ c) * wspec hN β Λ R
          - (wspec hN β Λ R - ContinuousMap.const _ c) * R) := by ring
  rw [e, State.map_add, State.map_sub, key, sub_self, add_zero]

/-- **At `c = 1`, for the box twist ratio**: `ν((boxRatio − 1)²) = ν(B R) − 2 ν(R) + 1
= ν((B − 1)(R − 1))`. -/
theorem mean_sq_sub_one (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) :
    periodicState hN β ((wspec hN β Λ (reweight β Λ τ hτc) - 1) *
        (wspec hN β Λ (reweight β Λ τ hτc) - 1))
      = periodicState hN β (wspec hN β Λ (reweight β Λ τ hτc) * reweight β Λ τ hτc)
        - 2 * periodicState hN β (reweight β Λ τ hτc) + 1 ∧
    periodicState hN β ((wspec hN β Λ (reweight β Λ τ hτc) - 1) *
        (wspec hN β Λ (reweight β Λ τ hτc) - 1))
      = periodicState hN β ((wspec hN β Λ (reweight β Λ τ hτc) - 1) *
        (reweight β Λ τ hτc - 1)) := by
  have h1 : (1 : C(IConf (SU N), ℝ)) = ContinuousMap.const _ 1 := rfl
  have hc := mean_sq_eq_cross hN β Λ (reweight β Λ τ hτc) 1
  rw [← h1] at hc
  refine ⟨?_, hc⟩
  set R := reweight β Λ τ hτc
  set B := wspec hN β Λ R
  have hB : periodicState hN β B = periodicState hN β R := periodicState_dlr hN β Λ R
  have hBR : periodicState hN β (B * B) = periodicState hN β (B * R) :=
    mean_local_mul_wspec hN β Λ (extLocal_wspec hN β Λ R) R
  have e : (B - 1) * (B - 1) = B * B - (2 : ℝ) • B + 1 := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e, State.map_add, State.map_sub, State.map_smul, State.map_one, hBR, hB]

/-- **The first moment is a necessary input**: `(ν(R) − 1)² ≤ ν((boxRatio − 1)²)`. -/
theorem mean_sq_ge (hN : N ≠ 0) (β : ℝ) {Λ : Finset ILink} {τ : ILink → SU N ≃ᵐ SU N}
    (hτc : ∀ l, Continuous (τ l)) :
    (periodicState hN β (reweight β Λ τ hτc) - 1) ^ 2
      ≤ periodicState hN β ((wspec hN β Λ (reweight β Λ τ hτc) - 1) *
        (wspec hN β Λ (reweight β Λ τ hτc) - 1)) := by
  have h := sq_state_le (periodicState hN β) (wspec hN β Λ (reweight β Λ τ hτc) - 1)
  rwa [State.map_sub, State.map_one, periodicState_dlr hN β Λ] at h

/-! ## 4. The `ℤ₂` involution -/

theorem twistBd_twistBd {τ : ILink → SU N ≃ᵐ SU N} (hτ : ∀ l g, τ l (τ l g) = g)
    (ω : IConf (SU N)) : twistBd τ (twistBd τ ω) = ω := by
  funext l
  simp only [twistBd, twistConf, Equiv.refl_apply, hτ]

/-- **For an involutive twist the ratio inverts along the orbit**: `boxRatio(ω) · boxRatio(τ ω) = 1`. -/
theorem boxRatio_mul_twist (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) {τ : ILink → SU N ≃ᵐ SU N}
    (hτ : ∀ l g, τ l (τ l g) = g) (ω : IConf (SU N)) :
    boxRatio β Λ τ ω * boxRatio β Λ τ (twistBd τ ω) = 1 := by
  unfold boxRatio
  rw [twistBd_twistBd hτ]
  have h1 := (boxPart_pos hN β Λ ω).ne'
  have h2 := (boxPart_pos hN β Λ (twistBd τ ω)).ne'
  field_simp

end MassGap.ReplicaTwist

#print axioms MassGap.ReplicaTwist.boxRatio_sq_replica
#print axioms MassGap.ReplicaTwist.replica_mean
#print axioms MassGap.ReplicaTwist.mean_sq_eq_cross
#print axioms MassGap.ReplicaTwist.mean_sq_sub_one
#print axioms MassGap.ReplicaTwist.mean_sq_ge
#print axioms MassGap.ReplicaTwist.boxRatio_mul_twist
