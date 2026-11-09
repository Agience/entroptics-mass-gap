import Mathlib
import MassGap.ProxyGenLimN

/-!
# MassGap.ApproxJoint — the joint Hilbert space of composites and observer, and the margin

`ProxyGenLimN.clayStatement_of_approx` takes, at each `N ≥ 2`, `ApproxK (kernC (CRen N z μ) 0)
(mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r)` at `W = sunFam hN2 c hc0 hc s₀`: every separated
positive-time monomial of renormalised composites, including those with times in `(0, r]`, is a
limit, in the joint reflection form, of real combinations of the observer's margin monomials beyond
`r`. This module builds one Hilbert space holding both families with one injective transfer, and
with it removes the margin: `ApproxK` holds iff it holds at the composite monomials whose times lie
beyond `r`. Declarations are in the namespace `MassGap.ApproxJoint`.

## 1. The joint kernel (any index types)

* `jK Kc X G`: the kernel on `I ⊕ M` with blocks `Kc` (composites), `X` (both cross blocks) and `G`
  (observer). `ApproxKAt Kc X G P`: the clause of `ApproxK` at one composite (`approxK_iff_forall`).
* `JointData I M`: the three kernels, dyadic steps `shI m`, `shM m`, a vacuum monomial `e`, and the
  clauses read: symmetry of `Kc`, `G`; Gram positivity of `jK` on every finite family; symmetry of
  every step in every block; `sh (m+1) ∘ sh (m+1) = sh m`; a bound on the diagonal along every step
  orbit; `sh m e = e`, `G e e = 1`; every monomial one step forward of a monomial.
* `jK_sq_le` (Cauchy–Schwarz from Gram positivity), `jK_bound`: bounded orbits of the joint kernel
  from the diagonal bounds.

## 2. The joint reconstruction

* `jT D m := ContinuumFlow.gTransfer (jK …) … (jSh D m) …`; all steps share one reflection form, so
  `JH D = GNSHilbert.H (jT D 0).toReflForm` is one complete complex Hilbert space, `jv D x` the vector
  of `x`, `step D m = GNSHilbert.opT (jT D m)`.
* `inner_jv`: `⟪jv x, jv y⟫ = jK x y`. `step_jv`: `step m (jv x) = jv (jSh m x)`. `step_sq`:
  `step (m+1)² = step m`. `isSelfAdjoint_step`, `step_symm`.
* `step_eq_zero_all`: all steps have one kernel (`‖T_{m+1} y‖² = ⟪y, T_m y⟫` and
  `T_m = T_{m+1}²`). `step_injective`: every step is injective; a vector it kills is orthogonal to
  `jv (jSh m' x') = jv x` for every `x`, hence to the dense pre-Hilbert space (`inner_pre_eq_zero`).
  No generator is formed: injectivity comes from every monomial being a step of a monomial, the
  joint form of `ContinuumTimeGroup.stepT_zero_injective`.

## 3. The margin reduction

* `approxKAt_iff_mem`: `ApproxKAt P` iff `jv (inl P)` lies in the closure of the real combinations
  of the observer's vectors `jv (inr Q)` (`CompositeLink.dist2_eq`, `norm_yL_sq`).
* **`approxKAt_of_shift`**: `ApproxKAt (shI m P) → ApproxKAt P`. With the real inner product on
  `JH D` (`InnerProductSpace.complexToReal`), `V` the closure of the real span of the observer's
  vectors, `T = step m` symmetric, injective, `T V ⊆ V` (`step_jv` on generators, continuity on the
  closure): `ApproxObserver.mem_of_apply_mem`.
* `approxKAt_of_iterate`: the same along `n` steps.

## 4. The capstone's kernels

Index sets `TSepG Cs.Ix 0` and `MarginMono N 0 r`, steps `shiftT hN 0 m` and `MarginMono.shift`,
vacuum `emptyMargin`. Every clause of `JointData` is proved from `ClassMoments`, `PhysRange r`,
`UnifLocal Cs`, `ReflCovLat Cs 0` and `CompOS Cs` (at `CRen` the second and third are theorems,
`CompositesRen.unifLocal_buildRen` and `CompositesRen.reflCovLat_CRen`):

* `joint_gram`: Gram positivity of the joint kernel. At each step `k` the lattice reflection form
  `rform (stateK k) θ` is positive on `∑ c_x U_k(x)` for the half-space vectors of composites and
  margin monomials (`stateK_rp`), and every entry converges along `ultra` (`ReflLimG`,
  `tendsto_contSF`, `rform_symm_k` for the transposed cross block). `JointRPK` is its
  two-composite case.
* `kernC_symm_of_reflLim`: `kernC` symmetric (limit of the symmetric lattice form).
* `kernC_shift_of_os1`: `kernC(T_m P, P') = kernC(P, T_m P')` from `OS1C`, since
  `Θ(T_m P) ∪ P'` is `ΘP ∪ T_m P'` translated back one step. The cross block is
  `CompositeLink.mixKC_shift`, the observer block `ContinuumFlow.kernF_shift`.
* `shiftT_half`, `exists_shiftT_preimage` (a step finer than the margin), and for margin monomials
  `MarginMono.shift_half`, `ContinuumTimeGroup.exists_shift_preimage`.
* `compOrbitBound_of_os0`: `kernC(T^n P, T^n P)` is bounded in `n` by `OS0C`. The family
  `Θ(T^n P) ∪ T^n P` stays separated at the margin of `P` (`posSepT_iterate`, `sepD_pairC`), keeps its
  indices and the `L¹` norms of its test functions (`l1_translate'`), so the bound at margin
  `min d 1` does not depend on `n`. `abs_sgnC`: the reflection sign has modulus one.
* `capData`: the joint data at the capstone's kernels.
* `exists_beyond_iterate`: every composite monomial has a step iterate whose times lie beyond `r`
  (`BeyondR`, `LowerT`, `lowerT_iterate`).
* **`approxK_of_beyond_core`**, **`approxK_iff_beyond_core`**: under `SubstrateCoreAt`,
  `GradientFlowPropsN` and `PhysRange r`, `ApproxK` at `CRen N z μ` holds iff `ApproxKAt` holds at
  every composite monomial `P` with `BeyondR r P`.
* `FlowBeyondInputsN`, `flowApproxInputsN_of_beyond`, **`clayStatement_of_beyond`**:
  `ProxyGenLimN.FlowApproxInputsN` with `ApproxK` replaced by its clause beyond the margin, and the
  `ClayStatementDy` from it at every `N ≥ 2`.

## What remains

The per-`N` input of `clayStatement_of_beyond` in place of `ApproxK` is the generation clause beyond
the margin: for every separated monomial `P` of renormalised composites of `CRen N z μ` whose test
functions vanish at times `< d` for some `d > r`, and every `ε > 0`, a finite real combination `c`
of the margin monomials of `W = sunFam hN2 c hc0 hc s₀` beyond `r` with
`kernC(P, P) − 2 ∑_Q c_Q mixKG(P, Q) + ∑_{Q,Q'} c_Q c_{Q'} gramF(Q, Q') ≤ ε`; equivalently, in `JH`
of `capData`, `jv (inl P)` lies in the closed real span of the observer's vectors. The composites
carry `a_k^{−d}` and their subtractions while `Φ0 W` scales only the plaquette class;
`ProxyGenLimN.decoupled_core` shows the clause does not follow from the kernels with joint
positivity alone. All other per-`N` inputs are those of `FlowApproxInputsN`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reference step, the signs and the zero vector; `1` the unit
step, the half-step offset, the unit coefficient, the vacuum norm and the cap on the margin; `-1` the
backward step; `2` the least colour count, the cross-term factor and the square; `12` the bound of
the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApproxJoint

open Filter
open scoped Topology
open MassGap MassGap.ContinuumFlow MassGap.CompositeLink

/-! ## 1. The joint kernel -/

section Joint

variable {I M : Type}

/-- **The joint kernel** on composites and observer monomials: `Kc` on composites, `X` across (in
both orders), `G` on the observer. DERIVED: no numeral. -/
def jK (Kc : I → I → ℝ) (X : I → M → ℝ) (G : M → M → ℝ) : I ⊕ M → I ⊕ M → ℝ
  | Sum.inl P, Sum.inl P' => Kc P P'
  | Sum.inl P, Sum.inr Q => X P Q
  | Sum.inr Q, Sum.inl P => X P Q
  | Sum.inr Q, Sum.inr Q' => G Q Q'

/-- **Approximability at one composite**: the clause of `ApproxK` at `P`. DERIVED: `2` the
cross-term factor; `0` the sign of `ε`. -/
def ApproxKAt (Kc : I → I → ℝ) (X : I → M → ℝ) (G : M → M → ℝ) (P : I) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : M →₀ ℝ, Kc P P - 2 * xL (X P) c + gForm G c c ≤ ε

/-- `ApproxK` is `ApproxKAt` at every composite. DERIVED: no numeral. -/
theorem approxK_iff_forall {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ} :
    ApproxK Kc X G ↔ ∀ P, ApproxKAt Kc X G P := Iff.rfl

/-- **Joint data**: the three kernels, a dyadic family of time steps on each side with a vacuum
monomial, and the clauses the joint reconstruction reads. `gram` is the Gram positivity of the joint
kernel on every finite family; `Kc_orbit`, `G_orbit` bound the diagonal along every step orbit;
`I_pre`, `M_pre` say every monomial is one step forward of a monomial. DERIVED: `1` the half step
offset and the vacuum norm; `0` the sign. -/
structure JointData (I M : Type) where
  Kc : I → I → ℝ
  X : I → M → ℝ
  G : M → M → ℝ
  shI : ℕ → I → I
  shM : ℕ → M → M
  e : M
  Kc_symm : ∀ P P', Kc P P' = Kc P' P
  G_symm : ∀ Q Q', G Q Q' = G Q' Q
  gram : ∀ (s : Finset (I ⊕ M)) (c : I ⊕ M → ℝ),
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * c y * jK Kc X G x y
  Kc_shift : ∀ m P P', Kc (shI m P) P' = Kc P (shI m P')
  X_shift : ∀ m P Q, X (shI m P) Q = X P (shM m Q)
  G_shift : ∀ m Q Q', G (shM m Q) Q' = G Q (shM m Q')
  I_half : ∀ m P, shI (m + 1) (shI (m + 1) P) = shI m P
  M_half : ∀ m Q, shM (m + 1) (shM (m + 1) Q) = shM m Q
  Kc_orbit : ∀ m P, ∃ C : ℝ, ∀ n : ℕ, Kc ((shI m)^[n] P) ((shI m)^[n] P) ≤ C
  G_orbit : ∀ m Q, ∃ C : ℝ, ∀ n : ℕ, G ((shM m)^[n] Q) ((shM m)^[n] Q) ≤ C
  e_shift : ∀ m, shM m e = e
  e_norm : G e e = 1
  I_pre : ∀ P, ∃ (m : ℕ) (P' : I), shI m P' = P
  M_pre : ∀ Q, ∃ (m : ℕ) (Q' : M), shM m Q' = Q

variable (D : JointData I M)

/-- The joint step. DERIVED: no numeral. -/
def jSh (m : ℕ) : I ⊕ M → I ⊕ M := Sum.map (D.shI m) (D.shM m)

/-- DERIVED: no numeral. -/
theorem jK_symm (x y : I ⊕ M) : jK D.Kc D.X D.G x y = jK D.Kc D.X D.G y x := by
  rcases x with P | Q <;> rcases y with P' | Q'
  · exact D.Kc_symm P P'
  · rfl
  · rfl
  · exact D.G_symm Q Q'

/-- DERIVED: no numeral. -/
theorem jK_shift (m : ℕ) (x y : I ⊕ M) :
    jK D.Kc D.X D.G (jSh D m x) y = jK D.Kc D.X D.G x (jSh D m y) := by
  rcases x with P | Q <;> rcases y with P' | Q'
  · exact D.Kc_shift m P P'
  · exact D.X_shift m P Q'
  · exact (D.X_shift m P' Q).symm
  · exact D.G_shift m Q Q'

/-- DERIVED: `1` the half-step offset. -/
theorem jSh_half (m : ℕ) (x : I ⊕ M) : jSh D (m + 1) (jSh D (m + 1) x) = jSh D m x := by
  rcases x with P | Q
  · exact congrArg Sum.inl (D.I_half m P)
  · exact congrArg Sum.inr (D.M_half m Q)

/-- DERIVED: no numeral. -/
theorem jSh_iterate_inl (m n : ℕ) (P : I) :
    (jSh D m)^[n] (Sum.inl P) = Sum.inl ((D.shI m)^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

/-- DERIVED: no numeral. -/
theorem jSh_iterate_inr (m n : ℕ) (Q : M) :
    (jSh D m)^[n] (Sum.inr Q) = Sum.inr ((D.shM m)^[n] Q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

/-- `gForm` is additive on the right for a symmetric kernel. DERIVED: no numeral. -/
theorem gForm_add_right' (K : I ⊕ M → I ⊕ M → ℝ) (hK : ∀ x y, K x y = K y x)
    (c d d' : I ⊕ M →₀ ℝ) : gForm K c (d + d') = gForm K c d + gForm K c d' := by
  rw [gForm_symm K hK, gForm_add_left, gForm_symm K hK d, gForm_symm K hK d']

/-- **The Cauchy–Schwarz bound of the joint kernel**: `K(x,y)² ≤ K(y,y) K(x,x)`.
DERIVED: `1` the unit coefficient; `2` the square. -/
theorem jK_sq_le (x y : I ⊕ M) :
    jK D.Kc D.X D.G x y ^ 2 ≤ jK D.Kc D.X D.G y y * jK D.Kc D.X D.G x x := by
  set K := jK D.Kc D.X D.G with hKdef
  have hK := jK_symm D
  refine sq_le_of_quad fun t => ?_
  have h := gForm_nonneg K D.gram (Finsupp.single x 1 + Finsupp.single y t)
  rw [gForm_add_left, gForm_add_right' K hK, gForm_add_right' K hK, gForm_single, gForm_single,
    gForm_single, gForm_single] at h
  have hyx : K y x = K x y := hK y x
  rw [hyx] at h
  nlinarith [h]

/-- DERIVED: `1` the unit coefficient; `0` the sign. -/
theorem jK_diag_nonneg (x : I ⊕ M) : 0 ≤ jK D.Kc D.X D.G x x := by
  have h := gForm_nonneg (jK D.Kc D.X D.G) D.gram (Finsupp.single x 1)
  rw [gForm_single] at h
  linarith

/-- **Bounded orbits of the joint kernel**, from the diagonal bounds and Cauchy–Schwarz.
DERIVED: `0` the sign; `2` the square. -/
theorem jK_bound (m : ℕ) (x y : I ⊕ M) :
    ∃ C : ℝ, ∀ n : ℕ, |jK D.Kc D.X D.G ((jSh D m)^[n] x) ((jSh D m)^[n] y)| ≤ C := by
  have hdiag : ∀ x : I ⊕ M, ∃ C : ℝ, ∀ n : ℕ,
      jK D.Kc D.X D.G ((jSh D m)^[n] x) ((jSh D m)^[n] x) ≤ C := by
    rintro (P | Q)
    · obtain ⟨C, hC⟩ := D.Kc_orbit m P
      exact ⟨C, fun n => by rw [jSh_iterate_inl]; exact hC n⟩
    · obtain ⟨C, hC⟩ := D.G_orbit m Q
      exact ⟨C, fun n => by rw [jSh_iterate_inr]; exact hC n⟩
  obtain ⟨Cx, hCx⟩ := hdiag x
  obtain ⟨Cy, hCy⟩ := hdiag y
  refine ⟨|Cx| + |Cy|, fun n => ?_⟩
  have h1 := jK_sq_le D ((jSh D m)^[n] x) ((jSh D m)^[n] y)
  have ha := jK_diag_nonneg D ((jSh D m)^[n] x)
  have hb := jK_diag_nonneg D ((jSh D m)^[n] y)
  have hax := (hCx n).trans (le_abs_self Cx)
  have hby := (hCy n).trans (le_abs_self Cy)
  have hS : 0 ≤ |Cx| + |Cy| := by positivity
  have h2 : jK D.Kc D.X D.G ((jSh D m)^[n] x) ((jSh D m)^[n] y) ^ 2 ≤ (|Cx| + |Cy|) ^ 2 := by
    have : jK D.Kc D.X D.G ((jSh D m)^[n] y) ((jSh D m)^[n] y)
        * jK D.Kc D.X D.G ((jSh D m)^[n] x) ((jSh D m)^[n] x) ≤ (|Cx| + |Cy|) * (|Cx| + |Cy|) :=
      mul_le_mul (by linarith [abs_nonneg Cx]) (by linarith [abs_nonneg Cy]) ha hS
    nlinarith
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hS]
  exact Real.sqrt_le_sqrt h2

/-! ## 2. The joint reconstruction -/

/-- **The joint transfer data at step `m`** (`ContinuumFlow.gTransfer`). DERIVED: no numeral. -/
def jT (m : ℕ) : Transfer.TransferData (I ⊕ M →₀ ℝ) :=
  gTransfer (jK D.Kc D.X D.G) (jK_symm D) D.gram (jSh D m) (jK_shift D m) (jK_bound D m)
    (Sum.inr D.e) (congrArg Sum.inr (D.e_shift m)) D.e_norm

/-- **The joint Hilbert space**: the completion of the joint reflection form (the same at every
step). DERIVED: `0` the reference step. -/
abbrev JH : Type := GNSHilbert.H (jT D 0).toReflForm

/-- The vector of a composite (`inl`) or an observer monomial (`inr`). DERIVED: `0` the reference
step. -/
def jv (x : I ⊕ M) : JH D := gVec (jT D 0) x

/-- **The step-`m` transfer on the joint space.** DERIVED: no numeral. -/
def step (m : ℕ) : JH D →L[ℂ] JH D := GNSHilbert.opT (jT D m)

/-- **The joint space reads the joint kernel.** DERIVED: `0` the reference step. -/
theorem inner_jv (x y : I ⊕ M) : inner ℂ (jv D x) (jv D y) = (jK D.Kc D.X D.G x y : ℂ) :=
  inner_gVec (jT D 0) (jK D.Kc D.X D.G) (fun _ _ => rfl) x y

/-- DERIVED: `0` the reference step. -/
theorem step_coe (m : ℕ) (z : GNSHilbert.Pre (jT D 0).toReflForm) :
    step D m (z : JH D)
      = ((GNSHilbert.Pre.ofPair (jT D 0).toReflForm ((jT D m).T (z : _ × _).1)
          ((jT D m).T (z : _ × _).2) : GNSHilbert.Pre (jT D 0).toReflForm) : JH D) :=
  GNSHilbert.opT_coe (jT D m) z

/-- **The step moves a monomial forward**: `step m (jv x) = jv (jSh m x)`. DERIVED: `1` the
coefficient; `0` the imaginary part. -/
theorem step_jv (m : ℕ) (x : I ⊕ M) : step D m (jv D x) = jv D (jSh D m x) := by
  unfold jv gVec
  rw [step_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (jSh D m) (Finsupp.single x 1) = Finsupp.single (jSh D m x) 1
    exact Finsupp.mapDomain_single
  · show (jT D m).T 0 = 0
    exact map_zero _

/-- The product of operators applied. DERIVED: no numeral. -/
theorem mul_apply' (f g : JH D →L[ℂ] JH D) (x : JH D) : (f * g) x = f (g x) := rfl

/-- **Two half steps are one step**. DERIVED: `1` the half-step offset. -/
theorem step_sq (m : ℕ) : step D (m + 1) * step D (m + 1) = step D m := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (step D (m + 1) * step D (m + 1)).continuous (step D m).continuous) (fun z => ?_)
  rw [mul_apply', step_coe, step_coe, step_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show (jT D (m + 1)).T ((jT D (m + 1)).T _) = (jT D m).T _
    exact (gT_half _ _ (fun x => jSh_half D m x) _).symm
  · show (jT D (m + 1)).T ((jT D (m + 1)).T _) = (jT D m).T _
    exact (gT_half _ _ (fun x => jSh_half D m x) _).symm

/-- DERIVED: no numeral. -/
theorem isSelfAdjoint_step (m : ℕ) : IsSelfAdjoint (step D m) := GNSHilbert.isSelfAdjoint_opT _

/-- DERIVED: no numeral. -/
theorem step_symm (m : ℕ) (x y : JH D) :
    inner ℂ (step D m x) y = inner ℂ x (step D m y) := by
  have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_step D m)) x y
  simpa only [ContinuousLinearMap.coe_coe] using this

/-- A vector killed by step `m` is killed by step `m + 1`. DERIVED: `0` the zero vector; `1` the
half-step offset. -/
theorem step_succ_eq_zero {m : ℕ} {y : JH D} (hy : step D m y = 0) : step D (m + 1) y = 0 := by
  have h1 : step D (m + 1) (step D (m + 1) y) = 0 := by
    rw [← mul_apply', step_sq, hy]
  have h2 : inner ℂ (step D (m + 1) y) (step D (m + 1) y) = 0 := by
    rw [step_symm, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h2

/-- A vector killed by step `m + 1` is killed by step `m`. DERIVED: `0` the zero vector; `1` the
half-step offset. -/
theorem step_pred_eq_zero {m : ℕ} {y : JH D} (hy : step D (m + 1) y = 0) : step D m y = 0 := by
  rw [← step_sq, mul_apply', hy, map_zero]

/-- **All steps have one kernel.** DERIVED: `0` the zero vector and the reference step. -/
theorem step_eq_zero_all {m : ℕ} {y : JH D} (hy : step D m y = 0) (m' : ℕ) : step D m' y = 0 := by
  have h0 : step D 0 y = 0 := by
    induction m with
    | zero => exact hy
    | succ m ih => exact ih (step_pred_eq_zero D hy)
  induction m' with
  | zero => exact h0
  | succ m' ih => exact step_succ_eq_zero D ih

/-- **Orthogonal to every monomial is orthogonal to the pre-Hilbert space.** DERIVED: `0` the zero
combination and the imaginary part; `1` the coefficient. -/
theorem inner_pre_eq_zero (y : JH D) (horth : ∀ x : I ⊕ M, inner ℂ y (jv D x) = 0)
    (z : GNSHilbert.Pre (jT D 0).toReflForm) : inner ℂ y (z : JH D) = 0 := by
  have hlin : ∀ c : I ⊕ M →₀ ℝ,
      inner ℂ y ((GNSHilbert.Pre.ofPair (jT D 0).toReflForm c 0
        : GNSHilbert.Pre (jT D 0).toReflForm) : JH D) = 0 := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      have h0 : (GNSHilbert.Pre.ofPair (jT D 0).toReflForm (0 : I ⊕ M →₀ ℝ) 0
          : GNSHilbert.Pre (jT D 0).toReflForm) = 0 :=
        GNSHilbert.Pre.ext rfl rfl
      rw [h0, UniformSpace.Completion.coe_zero, inner_zero_right]
    | add f g hf hg =>
      have h0 : (GNSHilbert.Pre.ofPair (jT D 0).toReflForm (f + g) 0
          : GNSHilbert.Pre (jT D 0).toReflForm)
          = GNSHilbert.Pre.ofPair _ f 0 + GNSHilbert.Pre.ofPair _ g 0 :=
        GNSHilbert.Pre.ext rfl (show (0 : I ⊕ M →₀ ℝ) = 0 + 0 from (add_zero 0).symm)
      rw [h0, UniformSpace.Completion.coe_add, inner_add_right, hf, hg, add_zero]
    | single x b =>
      have h0 : (GNSHilbert.Pre.ofPair (jT D 0).toReflForm (Finsupp.single x b) 0
          : GNSHilbert.Pre (jT D 0).toReflForm)
          = (b : ℂ) • GNSHilbert.Pre.ofPair _ (Finsupp.single x 1) 0 := by
        refine GNSHilbert.Pre.ext ?_ ?_
        · show Finsupp.single x b
            = (b : ℂ).re • Finsupp.single x (1 : ℝ) + (-(b : ℂ).im) • (0 : I ⊕ M →₀ ℝ)
          simp only [Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_smul, add_zero,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        · show (0 : I ⊕ M →₀ ℝ)
            = (b : ℂ).re • (0 : I ⊕ M →₀ ℝ) + (b : ℂ).im • Finsupp.single x (1 : ℝ)
          simp only [Complex.ofReal_im, zero_smul, smul_zero, add_zero]
      rw [h0, UniformSpace.Completion.coe_smul, inner_smul_right]
      exact mul_eq_zero_of_right _ (horth x)
  have hz : z = GNSHilbert.Pre.ofPair _ (z : _ × _).1 0
      + Complex.I • GNSHilbert.Pre.ofPair _ (z : _ × _).2 0 := by
    refine GNSHilbert.Pre.ext ?_ ?_
    · show (z : _ × _).1 = (z : _ × _).1 + (Complex.I.re • (z : _ × _).2
        + (-Complex.I.im) • (0 : I ⊕ M →₀ ℝ))
      simp only [Complex.I_re, Complex.I_im, zero_smul, smul_zero, add_zero]
    · show (z : _ × _).2 = (0 : I ⊕ M →₀ ℝ) + (Complex.I.re • (0 : I ⊕ M →₀ ℝ)
        + Complex.I.im • (z : _ × _).2)
      simp only [Complex.I_re, Complex.I_im, smul_zero, one_smul, zero_add]
  rw [hz, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul, inner_add_right,
    inner_smul_right, hlin, hlin, mul_zero, add_zero]

/-- **Every step of the joint transfer is injective.** A vector killed by one step is killed by all
(`step_eq_zero_all`); every monomial is a step of a monomial (`I_pre`, `M_pre`), so the vector is
orthogonal to every monomial, hence to the dense pre-Hilbert space. DERIVED: `0` the zero vector. -/
theorem step_injective (m : ℕ) {y : JH D} (hy : step D m y = 0) : y = 0 := by
  have horth : ∀ x : I ⊕ M, inner ℂ y (jv D x) = 0 := by
    intro x
    obtain ⟨m', x', hx'⟩ : ∃ (m' : ℕ) (x' : I ⊕ M), jSh D m' x' = x := by
      rcases x with P | Q
      · obtain ⟨m', P', h⟩ := D.I_pre P
        exact ⟨m', Sum.inl P', congrArg Sum.inl h⟩
      · obtain ⟨m', Q', h⟩ := D.M_pre Q
        exact ⟨m', Sum.inr Q', congrArg Sum.inr h⟩
    rw [← hx', ← step_jv, ← step_symm, step_eq_zero_all D hy m', inner_zero_left]
  have hall : ∀ w : JH D, inner ℂ y w = 0 := fun w =>
    UniformSpace.Completion.induction_on w
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (inner_pre_eq_zero D y horth)
  exact inner_self_eq_zero.mp (hall y)

/-! ## 3. The margin reduction -/

/-- **`ApproxKAt` is membership in the closure of the real combinations** of the observer's vectors
in the joint space. DERIVED: `2` the square; `1` the cap on the radius. -/
theorem approxKAt_iff_mem (P : I) :
    ApproxKAt D.Kc D.X D.G P
      ↔ jv D (Sum.inl P) ∈ closure (Set.range (yL (fun Q => jv D (Sum.inr Q)))) := by
  set w : I → JH D := fun P => jv D (Sum.inl P) with hw
  set v : M → JH D := fun Q => jv D (Sum.inr Q) with hv
  have hX : ∀ P Q, inner ℂ (w P) (v Q) = (D.X P Q : ℂ) := fun P Q => inner_jv D _ _
  have hK : ∀ P P', inner ℂ (w P) (w P') = (D.Kc P P' : ℂ) := fun P P' => inner_jv D _ _
  have hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (D.G Q Q' : ℂ) := fun Q Q' => inner_jv D _ _
  have hd : ∀ c : M →₀ ℝ, D.Kc P P - 2 * xL (D.X P) c + gForm D.G c c = ‖w P - yL v c‖ ^ 2 :=
    fun c => by
      rw [← norm_yL_sq D.G hG c]
      exact dist2_eq w hX hK P c
  constructor
  · intro hA
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨c, hc⟩ := hA (ε ^ 2 / 2) (by positivity)
    rw [hd] at hc
    refine ⟨yL v c, ⟨c, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have h4 : ‖w P - yL v c‖ ^ 2 < ε ^ 2 := by nlinarith
    nlinarith [norm_nonneg (w P - yL v c)]
  · intro h ε hε
    have hδ : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := Metric.mem_closure_iff.mp h (min ε 1) hδ
    refine ⟨c, ?_⟩
    rw [hd]
    rw [dist_eq_norm] at hc
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    have h2 : min ε 1 ≤ 1 := min_le_right _ _
    nlinarith [norm_nonneg (w P - yL v c)]

/-- **The margin step**: if the time translate `shI m P` of a composite is approximated by the
observer's monomials, so is `P`. In the joint space, with the real inner product, `V` the closure of
the real span of the observer's vectors, `T = step m` symmetric, injective (`step_injective`) and
mapping `V` into itself (`step_jv`): `ApproxObserver.mem_of_apply_mem`. DERIVED: no numeral. -/
theorem approxKAt_of_shift (m : ℕ) (P : I) (h : ApproxKAt D.Kc D.X D.G (D.shI m P)) :
    ApproxKAt D.Kc D.X D.G P := by
  rw [approxKAt_iff_mem] at h ⊢
  letI : InnerProductSpace ℝ (JH D) := InnerProductSpace.complexToReal
  set v : M → JH D := fun Q => jv D (Sum.inr Q) with hv
  have hspan : ((Submodule.span ℝ (Set.range v) : Submodule ℝ (JH D)) : Set (JH D))
      = Set.range (yL v) := by
    ext y
    rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, rfl⟩
  set V : Submodule ℝ (JH D) := (Submodule.span ℝ (Set.range v)).topologicalClosure with hVdef
  have hVc : (V : Set (JH D)) = closure (Set.range (yL v)) := by
    rw [hVdef, Submodule.topologicalClosure_coe, hspan]
  let T : JH D →ₗ[ℝ] JH D :=
    { toFun := step D m
      map_add' := map_add _
      map_smul' := fun r x => by
        show step D m ((r : ℂ) • x) = (r : ℂ) • step D m x
        exact map_smul _ _ _ }
  have hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y) := fun x y => by
    show RCLike.re (inner ℂ (step D m x) y) = RCLike.re (inner ℂ x (step D m y))
    rw [step_symm]
  have hinj : Function.Injective T := fun x y hxy => by
    have h0 : step D m (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (step_injective D m h0)
  have hTV : ∀ x ∈ V, T x ∈ V := by
    intro x hx
    have hle : Submodule.span ℝ (Set.range v) ≤ (Submodule.span ℝ (Set.range v)).comap T := by
      rw [Submodule.span_le]
      rintro _ ⟨Q, rfl⟩
      show step D m (v Q) ∈ Submodule.span ℝ (Set.range v)
      rw [hv, step_jv]
      exact Submodule.subset_span ⟨D.shM m Q, rfl⟩
    have hmaps : Set.MapsTo T (Submodule.span ℝ (Set.range v) : Set (JH D))
        (Submodule.span ℝ (Set.range v) : Set (JH D)) := fun y hy => hle hy
    have hx' : x ∈ closure (Submodule.span ℝ (Set.range v) : Set (JH D)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hx
    have := map_mem_closure (step D m).continuous hx' hmaps
    rw [← Submodule.topologicalClosure_coe] at this
    exact this
  have hw : T (jv D (Sum.inl P)) ∈ V := by
    show step D m (jv D (Sum.inl P)) ∈ V
    rw [step_jv]
    show jv D (Sum.inl (D.shI m P)) ∈ (V : Set (JH D))
    rw [hVc]
    exact h
  have hmem := ApproxObserver.mem_of_apply_mem V (Submodule.isClosed_topologicalClosure _) T hT
    hinj hTV hw
  rw [← hVc]
  exact hmem

/-- **The margin step, iterated.** DERIVED: no numeral. -/
theorem approxKAt_of_iterate (m n : ℕ) (P : I) (h : ApproxKAt D.Kc D.X D.G ((D.shI m)^[n] P)) :
    ApproxKAt D.Kc D.X D.G P := by
  induction n generalizing P with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact approxKAt_of_shift D m P (ih (D.shI m P) h)

end Joint

/-! ## 4. The capstone's kernels -/

section Capstone

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumReconstruction
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN

variable {N : ℕ}

/-- **The composites' diagonal orbit bound**: along every dyadic step orbit of a separated
positive-time composite monomial, its reflected two-point function is bounded above. DERIVED: `0`
the plane. -/
def CompOrbitBound (hN : N ≠ 0) (Cs : Composites N) : Prop :=
  ∀ (m : ℕ) (P : TSepG Cs.Ix 0), ∃ B : ℝ, ∀ n : ℕ,
    kernC hN Cs 0 ((shiftT hN 0 m)^[n] P) ((shiftT hN 0 m)^[n] P) ≤ B

/-- The `L¹` norm is unchanged by a translation. An alias of `TransContSU.l1_translate`. -/
alias l1_translate' := MassGap.TransContSU.l1_translate

/-- One step keeps positive time and separation at the same margin. DERIVED: `0` the plane; `1`
the unit step. -/
theorem posSepT_shiftT (hN : N ≠ 0) {Xd : Type} (m : ℕ) {d : ℝ} {P : TSepG Xd 0}
    (h : PosSepT 0 d P.1) : PosSepT 0 d (shiftT hN 0 m P).1 := by
  refine ⟨fun i y hy => ?_, fun i j hij => ContinuumSep.sepBy_translate (h.2 i j hij) _⟩
  have h1 := h.1 i (y - timeVec N m 0 1) hy
  have e : (y - timeVec N m 0 1) 0 = y 0 - timeVec N m 0 1 0 := rfl
  rw [e, timeVec_self, Int.cast_one, mul_one] at h1
  linarith [dySpacing_pos (one_le_of_ne_zero hN) m]

/-- DERIVED: `0` the plane. -/
theorem posSepT_iterate (hN : N ≠ 0) {Xd : Type} (m : ℕ) {d : ℝ} {P : TSepG Xd 0}
    (h : PosSepT 0 d P.1) (n : ℕ) : PosSepT 0 d ((shiftT hN 0 m)^[n] P).1 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact posSepT_shiftT hN m ih

/-- **`ΘQ ∪ Q` is separated at the margin of `Q`** (`ContinuumSep.famSep_pairFam`). DERIVED: `0`
the plane and the reference step. -/
theorem sepD_pairC (hN : N ≠ 0) (Cs : Composites N) {d : ℝ} (hd : 0 ≤ d) (Q : TSepG Cs.Ix 0)
    (hQ : PosSepT 0 d Q.1) : SepD d (pairC Cs 0 Q.1 Q.1) := by
  let Q' : Mono N := ⟨Q.1.1, fun i => cField hN Cs 0 (Q.1.2 i)⟩
  have hs := ContinuumSep.famSep_pairFam (τ := 0) (P := Q') (Q := Q') hd hQ hQ
  intro i j hij
  have h := hs i j hij
  rcases i with a | a <;> rcases j with b | b <;> exact h

/-- `|sgnC| = 1`. DERIVED: `1` the sign. -/
theorem abs_sgnC (Cs : Composites N) (P : TMonoG Cs.Ix) : |sgnC Cs 0 P| = 1 := by
  unfold sgnC
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => by rw [abs_pow, abs_neg, abs_one, one_pow]

/-- **The composites' orbit bound from `OS0C`**: along a step orbit the family `Θ(T^n P) ∪ T^n P`
stays separated at the margin of `P` (`posSepT_iterate`, `sepD_pairC`), keeps its indices, and keeps
the `L¹` norms of its test functions (`l1_translate'`); so the `OS0C` bound at margin `min d 1` is
the same at every `n`. DERIVED: `1` the cap on the margin; `0` the plane. -/
theorem compOrbitBound_of_os0 (hN : N ≠ 0) (Cs : Composites N) (h0 : OS0C hN Cs) :
    CompOrbitBound hN Cs := by
  obtain ⟨α, γ, β, Cc, κ, hB⟩ := h0
  intro m P
  obtain ⟨-, d, hd, hP⟩ := P.2
  have hd' : 0 < min d 1 := lt_min hd one_pos
  let wt : (Q : TSepG Cs.Ix 0) → Fin Q.1.1 ⊕ Fin Q.1.1 → ℝ := fun Q x =>
    Cc (pairC Cs 0 Q.1 Q.1 x).1 * (min d 1 ^ κ (pairC Cs 0 Q.1 Q.1 x).1)⁻¹
      * l1 (pairC Cs 0 Q.1 Q.1 x).2
  let bnd : TSepG Cs.Ix 0 → ℝ := fun Q =>
    α * γ ^ (Q.1.1 + Q.1.1) * ((Q.1.1 + Q.1.1).factorial : ℝ) ^ β * ∏ x, wt Q x
  have hstep : ∀ Q, bnd (shiftT hN 0 m Q) = bnd Q := by
    intro Q
    have hw : ∀ x : Fin Q.1.1 ⊕ Fin Q.1.1, wt (shiftT hN 0 m Q) x = wt Q x := by
      intro x
      rcases x with a | b
      · show Cc (Q.1.2 a).1 * (min d 1 ^ κ (Q.1.2 a).1)⁻¹
            * l1 (((Q.1.2 a).2.translate (timeVec N m 0 1)).reflect 0)
          = Cc (Q.1.2 a).1 * (min d 1 ^ κ (Q.1.2 a).1)⁻¹ * l1 ((Q.1.2 a).2.reflect 0)
        rw [TestFn.reflect_translate, l1_translate']
      · show Cc (Q.1.2 b).1 * (min d 1 ^ κ (Q.1.2 b).1)⁻¹
            * l1 ((Q.1.2 b).2.translate (timeVec N m 0 1))
          = Cc (Q.1.2 b).1 * (min d 1 ^ κ (Q.1.2 b).1)⁻¹ * l1 (Q.1.2 b).2
        rw [l1_translate']
    show α * γ ^ (Q.1.1 + Q.1.1) * ((Q.1.1 + Q.1.1).factorial : ℝ) ^ β
        * ∏ x : Fin Q.1.1 ⊕ Fin Q.1.1, wt (shiftT hN 0 m Q) x
      = α * γ ^ (Q.1.1 + Q.1.1) * ((Q.1.1 + Q.1.1).factorial : ℝ) ^ β
        * ∏ x : Fin Q.1.1 ⊕ Fin Q.1.1, wt Q x
    rw [Fintype.prod_congr _ _ hw]
  have hiter : ∀ n, bnd ((shiftT hN 0 m)^[n] P) = bnd P := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hstep, ih]
  have hQ : ∀ Q : TSepG Cs.Ix 0, PosSepT 0 d Q.1 →
      |contC hN Cs (pairC Cs 0 Q.1 Q.1)| ≤ bnd Q := by
    intro Q hQd
    have hsep := sepD_pairC hN Cs hd.le Q hQd
    have hc : ContD (pairC Cs 0 Q.1 Q.1) := (adm_pairC Cs Q Q).1
    let e : Fin Q.1.1 ⊕ Fin Q.1.1 ≃ Fin (Q.1.1 + Q.1.1) := finSumFinEquiv
    let F' : Fin (Q.1.1 + Q.1.1) → CDatum Cs := fun i => pairC Cs 0 Q.1 Q.1 (e.symm i)
    have hF : contC hN Cs F' = contC hN Cs (pairC Cs 0 Q.1 Q.1) := by
      unfold contC latC latSk
      congr 1
      funext k
      exact latS_comp_equiv (stateK hN k) (dySpacing N k) e.symm
        (fun i => cField hN Cs k (pairC Cs 0 Q.1 Q.1 i))
    have h := hB (Q.1.1 + Q.1.1) F' (min d 1) hd' (min_le_right _ _) (fun i => hc _)
      (fun i j hij y z hy hz => by
        obtain ⟨k, hk⟩ := hsep _ _ (fun h => hij (e.symm.injective h)) y z hy hz
        exact ⟨k, le_trans (min_le_left _ _) hk⟩)
    have hprod : ∏ i, wt Q (e.symm i) = ∏ x, wt Q x := Equiv.prod_comp e.symm (wt Q)
    calc |contC hN Cs (pairC Cs 0 Q.1 Q.1)| = |contC hN Cs F'| := by rw [hF]
      _ ≤ _ := h
      _ = bnd Q := by
        show _ = α * γ ^ (Q.1.1 + Q.1.1) * ((Q.1.1 + Q.1.1).factorial : ℝ) ^ β * ∏ x, wt Q x
        rw [← hprod]
  refine ⟨bnd P, fun n => ?_⟩
  have h1 := hQ _ (posSepT_iterate hN m hP n)
  rw [hiter n] at h1
  calc kernC hN Cs 0 ((shiftT hN 0 m)^[n] P) ((shiftT hN 0 m)^[n] P)
      ≤ |kernC hN Cs 0 ((shiftT hN 0 m)^[n] P) ((shiftT hN 0 m)^[n] P)| := le_abs_self _
    _ = |contC hN Cs (pairC Cs 0 ((shiftT hN 0 m)^[n] P).1 ((shiftT hN 0 m)^[n] P).1)| := by
        unfold kernC
        rw [abs_mul, abs_sgnC, one_mul]
    _ ≤ bnd P := h1

/-- **Times bounded below by `d`**: every test function of `P` vanishes at times below `d`.
DERIVED: `0` the plane and the vanishing value. -/
def LowerT {Xd : Type} (d : ℝ) (P : TSepG Xd 0) : Prop :=
  ∀ i y, (P.1.2 i).2.1 y ≠ 0 → d ≤ y 0

/-- **A composite monomial beyond the margin `r`**: its times are bounded below by some `d > r`.
DERIVED: no numeral. -/
def BeyondR {Xd : Type} (r : ℝ) (P : TSepG Xd 0) : Prop := ∃ d : ℝ, r < d ∧ LowerT d P

/-- One step moves the lower time bound by `a_m`. DERIVED: `1` the unit step; `0` the plane. -/
theorem lowerT_shiftT (hN : N ≠ 0) {Xd : Type} (m : ℕ) {d : ℝ} {P : TSepG Xd 0}
    (hP : LowerT d P) : LowerT (d + dySpacing N m) (shiftT hN 0 m P) := by
  intro i y hy
  have h := hP i (y - timeVec N m 0 1) hy
  have e : (y - timeVec N m 0 1) 0 = y 0 - timeVec N m 0 1 0 := rfl
  rw [e, timeVec_self, Int.cast_one, mul_one] at h
  linarith

/-- `n` steps move the lower time bound by `n a_m`. DERIVED: `0` the plane; `1` the step. -/
theorem lowerT_iterate (hN : N ≠ 0) {Xd : Type} (m : ℕ) {d : ℝ} {P : TSepG Xd 0}
    (hP : LowerT d P) (n : ℕ) : LowerT (d + n * dySpacing N m) ((shiftT hN 0 m)^[n] P) := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have e : d + ((n + 1 : ℕ) : ℝ) * dySpacing N m = d + n * dySpacing N m + dySpacing N m := by
      push_cast
      ring
    rw [e]
    exact lowerT_shiftT hN m ih

/-- **Every separated positive-time monomial has a step iterate beyond `r`.** DERIVED: `0` the
plane and the reference step. -/
theorem exists_beyond_iterate (hN : N ≠ 0) {Xd : Type} (r : ℝ) (P : TSepG Xd 0) :
    ∃ n : ℕ, BeyondR r ((shiftT hN 0 0)^[n] P) := by
  obtain ⟨-, d, -, h1, -⟩ := P.2
  have ha := dySpacing_pos (one_le_of_ne_zero hN) 0
  obtain ⟨n, hn⟩ := exists_nat_gt ((r - d) / dySpacing N 0)
  refine ⟨n, d + n * dySpacing N 0, ?_, lowerT_iterate hN 0 h1 n⟩
  rw [div_lt_iff₀ ha] at hn
  linarith

/-- **Two half steps are one step** on composite monomials. DERIVED: `1` the half-step offset; `0`
the plane. -/
theorem shiftT_half (hN : N ≠ 0) {Xd : Type} (m : ℕ) (P : TSepG Xd 0) :
    shiftT hN 0 (m + 1) (shiftT hN 0 (m + 1) P) = shiftT hN 0 m P := by
  apply Subtype.ext
  show (⟨P.1.1, fun i => translateD (timeVec N (m + 1) 0 1)
      (translateD (timeVec N (m + 1) 0 1) (P.1.2 i))⟩ : TMonoG Xd)
    = ⟨P.1.1, fun i => translateD (timeVec N m 0 1) (P.1.2 i)⟩
  refine congrArg (Sigma.mk P.1.1) (funext fun i => Prod.ext rfl ?_)
  show ((P.1.2 i).2.translate (timeVec N (m + 1) 0 1)).translate (timeVec N (m + 1) 0 1)
    = (P.1.2 i).2.translate (timeVec N m 0 1)
  rw [TestFn.translate_translate, timeVec_one_add]

/-- **Every separated positive-time monomial is one step forward of another**, at a step finer than
its margin. DERIVED: `0` the plane; `1` the unit step and its inverse `-1`. -/
theorem exists_shiftT_preimage (hN : N ≠ 0) {Xd : Type} (P : TSepG Xd 0) :
    ∃ (m : ℕ) (P' : TSepG Xd 0), shiftT hN 0 m P' = P := by
  obtain ⟨hc, d, hd, h1, h2⟩ := P.2
  obtain ⟨m, hm⟩ := ((tendsto_dySpacing N).eventually (gt_mem_nhds hd)).exists
  have hv : timeVec N m 0 (-1) 0 = -dySpacing N m := by
    rw [timeVec_self]
    push_cast
    ring
  refine ⟨m, ⟨⟨P.1.1, fun i => translateD (timeVec N m 0 (-1)) (P.1.2 i)⟩,
    fun i => (hc i).comp (continuous_id.sub continuous_const), d - dySpacing N m, by linarith,
    fun i y hy => ?_, fun i j hij => fun y z hy hz => ?_⟩, ?_⟩
  · have h := h1 i (y - timeVec N m 0 (-1)) hy
    have e : (y - timeVec N m 0 (-1)) 0 = y 0 - timeVec N m 0 (-1) 0 := rfl
    rw [e, hv] at h
    linarith
  · obtain ⟨k, hk⟩ := ContinuumSep.sepBy_translate (h2 i j hij) (timeVec N m 0 (-1)) y z hy hz
    exact ⟨k, le_trans (by linarith [dySpacing_pos (one_le_of_ne_zero hN) m]) hk⟩
  · apply Subtype.ext
    show (⟨P.1.1, fun i => translateD (timeVec N m 0 1)
        (translateD (timeVec N m 0 (-1)) (P.1.2 i))⟩ : TMonoG Xd) = ⟨P.1.1, P.1.2⟩
    refine congrArg (Sigma.mk P.1.1) (funext fun i => Prod.ext rfl ?_)
    show ((P.1.2 i).2.translate (timeVec N m 0 (-1))).translate (timeVec N m 0 1) = (P.1.2 i).2
    rw [TestFn.translate_translate, timeVec_add, neg_add_cancel, timeVec_zero,
      TestFn.translate_zero]

/-- **The composites' kernel is symmetric for the dyadic step**, from `OS1C`:
`kernC(T_m P, P') = kernC(P, T_m P')`, since `Θ(T_m P) ∪ P'` is `ΘP ∪ T_m P'` translated back by one
step. DERIVED: `0` the plane; `1` the unit step and `-1` its reflection. -/
theorem kernC_shift_of_os1 (hN : N ≠ 0) (Cs : Composites N) (h1 : OS1C hN Cs) (m : ℕ)
    (P P' : TSepG Cs.Ix 0) :
    kernC hN Cs 0 (shiftT hN 0 m P) P' = kernC hN Cs 0 P (shiftT hN 0 m P') := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hfam : pairC Cs 0 (shiftT hN 0 m P).1 P'.1
      = fun i => translateD (timeVec N m 0 (-1)) (pairC Cs 0 P.1 (shiftT hN 0 m P').1 i) := by
    funext i
    rcases i with a | b
    · refine Prod.ext rfl ?_
      show ((P.1.2 a).2.translate (timeVec N m 0 1)).reflect 0
        = ((P.1.2 a).2.reflect 0).translate (timeVec N m 0 (-1))
      rw [TestFn.reflect_translate, reflR_timeVec]
    · refine Prod.ext rfl ?_
      show (P'.1.2 b).2
        = ((P'.1.2 b).2.translate (timeVec N m 0 1)).translate (timeVec N m 0 (-1))
      rw [TestFn.translate_translate, timeVec_add, add_neg_cancel, timeVec_zero,
        TestFn.translate_zero]
  unfold kernC
  have hs : sgnC Cs 0 (shiftT hN 0 m P).1 = sgnC Cs 0 P.1 := rfl
  rw [hs, hfam]
  congr 1
  exact (h1 _ _ (adm_pairC Cs P (shiftT hN 0 m P')) (timeVec N m 0 (-1))).limUnder_eq

/-- `ReflLimG` at uniformly local, reflection-covariant composites with `CompOS`. DERIVED: no
numeral. -/
theorem reflLim_cap (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (Cs : Composites N) (hUL : UnifLocal Cs)
    (hcov : ReflCovLat Cs 0) (hCO : CompOS (ne_zero_of_two_le hN2) Cs) : ReflLimG hN2 W Cs r :=
  reflLimG_of_cov hN2 W Cs r hcov hCO (mixConvG_of_cov hN2 W hU hphys Cs hUL hcov hCO)

/-- **The composites' kernel is symmetric**, as the limit of the symmetric lattice reflection form.
DERIVED: `0` the plane. -/
theorem kernC_symm_of_reflLim [NeZero N] (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N)
    {r : ℝ} (hRL : ReflLimG hN2 W Cs r) (P P' : TSepG Cs.Ix 0) :
    kernC (NeZero.ne N) Cs 0 P P' = kernC (NeZero.ne N) Cs 0 P' P := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique (hRL.1 P P') ((hRL.1 P' P).congr fun k => ?_)
  rw [rReadC_eq, rReadC_eq]
  exact rform_symm_k k _ _

/-- **Gram positivity of the joint kernel** of composites and observer at the capstone's kernels:
the lattice reflection form is positive on every finite combination of the half-space vectors
(`stateK_rp`), and every entry converges along `ultra` (`ReflLimG`, `tendsto_contSF`). DERIVED: `0`
the plane and the sign. -/
theorem joint_gram [NeZero N] (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (Cs : Composites N) (hUL : UnifLocal Cs)
    (hRL : ReflLimG hN2 W Cs r) (s : Finset (TSepG Cs.Ix 0 ⊕ MarginMono N 0 r))
    (c : TSepG Cs.Ix 0 ⊕ MarginMono N 0 r → ℝ) :
    0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * c y
      * jK (kernC (NeZero.ne N) Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r) x y := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hN := NeZero.ne N
  have hpos := Flow.posPreserving_of_physRange hN (Φ0 W) hphys 0
  let U : ℕ → TSepG Cs.Ix 0 ⊕ MarginMono N 0 r → C(Cfg N, ℝ) := fun k =>
    Sum.elim (fun P => prodSmear (dySpacing N k) (cMono hN Cs k P.1))
      (fun Q => prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1))
  let B : ℕ → C(Cfg N, ℝ) →ₗ[ℝ] C(Cfg N, ℝ) →ₗ[ℝ] ℝ := fun k =>
    rform (stateK hN k) (LatticeReflection.ireflObs 0 0)
  have hlim : ∀ x y, Tendsto (fun k => B k (U k x) (U k y)) (ultra : Filter ℕ)
      (𝓝 (jK (kernC hN Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r) x y)) := by
    rintro (P | Q) (P' | Q')
    · exact (hRL.1 P P').congr fun k => rReadC_eq hN Cs 0 k P.1 P'.1
    · exact (hRL.2 P Q').congr fun k => rMixC_eq hN Cs (Φ0 W) 0 k P.1 Q'.1
    · exact (hRL.2 P' Q).congr fun k =>
        (rMixC_eq hN Cs (Φ0 W) 0 k P'.1 Q.1).trans (rform_symm_k k _ _)
    · exact (tendsto_contSF hN (Φ0 W) (ClaySUGap.uB hN W hU) (pairFam 0 Q.1 Q'.1)).congr
        fun k => latSF_pair_eq hN (Φ0 W) 0 k Q.1 Q'.1
  have hmem : ∀ᶠ k in atTop, ∀ x ∈ s,
      U k x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
    refine (Filter.eventually_all_finset s).mpr fun x _ => ?_
    rcases x with P | Q
    · exact eventually_cMono_mem hN Cs hUL P
    · exact eventually_flow_mem (Φ0 W) hpos Q
  have hlat : ∀ᶠ k in (ultra : Filter ℕ),
      0 ≤ ∑ x ∈ s, ∑ y ∈ s, c x * c y * B k (U k x) (U k y) := by
    filter_upwards [hmem.filter_mono ultra_le] with k hk
    have hY : ∑ x ∈ s, c x • U k x ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
      Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (hk x hx)
    have h0 : 0 ≤ B k (∑ x ∈ s, c x • U k x) (∑ x ∈ s, c x • U k x) := by
      show 0 ≤ rform (stateK hN k) (LatticeReflection.ireflObs 0 0) _ _
      rw [rform_apply]
      exact stateK_rp hN k 0 _ hY
    have e : B k (∑ x ∈ s, c x • U k x) (∑ x ∈ s, c x • U k x)
        = ∑ x ∈ s, ∑ y ∈ s, c x * c y * B k (U k x) (U k y) := by
      have h1 : ∀ v, B k (∑ x ∈ s, c x • U k x) v = ∑ x ∈ s, c x * B k (U k x) v := fun v => by
        rw [map_sum, LinearMap.sum_apply]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h2 : ∀ u, B k u (∑ y ∈ s, c y • U k y) = ∑ y ∈ s, c y * B k u (U k y) := fun u => by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
      rw [h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e] at h0
    exact h0
  have hT := tendsto_finsetSum s fun x _ => tendsto_finsetSum s fun y _ =>
    (hlim x y).const_mul (c x * c y)
  exact ge_of_tendsto hT hlat

/-- **The joint data at the capstone's kernels**: composites `Cs` (uniformly local,
reflection-covariant, with `CompOS`) and the margin monomials of `Φ0 W` beyond `r`, with the dyadic
steps `shiftT`, `MarginMono.shift` and the empty margin monomial. Every clause is a theorem:
`Kc_orbit` is `compOrbitBound_of_os0`, `Kc_shift` is `kernC_shift_of_os1`, `gram` is `joint_gram`. DERIVED: `0` the plane. -/
def capData [NeZero N] (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (Cs : Composites N) (hUL : UnifLocal Cs)
    (hcov : ReflCovLat Cs 0) (hCO : CompOS (NeZero.ne N) Cs) : JointData (TSepG Cs.Ix 0) (MarginMono N 0 r) where
  Kc := kernC (NeZero.ne N) Cs 0
  X := mixKG hN2 W Cs r
  G := gramF hN2 W r
  shI := shiftT (NeZero.ne N) 0
  shM := fun m Q => MarginMono.shift (NeZero.ne N) 0 m Q
  e := emptyMargin N 0 r
  Kc_symm := kernC_symm_of_reflLim hN2 W Cs (reflLim_cap hN2 W hU hphys Cs hUL hcov hCO)
  G_symm := fun Q Q' => kernF_symm (NeZero.ne N) (Φ0 W) 0 Q.1 Q'.1
  gram := joint_gram hN2 W hU hphys Cs hUL (reflLim_cap hN2 W hU hphys Cs hUL hcov hCO)
  Kc_shift := kernC_shift_of_os1 (NeZero.ne N) Cs hCO.2.2.1
  X_shift := fun m P Q => mixKC_shift (NeZero.ne N) Cs (Φ0 W) 0 m P Q.1
  G_shift := fun m Q Q' => kernF_shift (NeZero.ne N) (Φ0 W) 0 m Q.1 Q'.1
  I_half := shiftT_half (NeZero.ne N)
  M_half := fun m Q => MarginMono.shift_half (NeZero.ne N) 0 m Q
  Kc_orbit := compOrbitBound_of_os0 (NeZero.ne N) Cs hCO.2.1
  G_orbit := fun m Q => by
    obtain ⟨C', hC'⟩ := kernF_iterate_bound (NeZero.ne N) (Φ0 W) (ClaySUGap.uB (NeZero.ne N) W hU)
      0 m Q Q
    exact ⟨C', fun n => (le_abs_self _).trans (hC' n)⟩
  e_shift := fun m => shift_emptyMargin (NeZero.ne N) 0 m
  e_norm := kernF_empty (NeZero.ne N) (Φ0 W) 0 r
  I_pre := exists_shiftT_preimage (NeZero.ne N)
  M_pre := fun Q => ContinuumTimeGroup.exists_shift_preimage (NeZero.ne N) 0 Q

/-- **`ApproxK` from the composites beyond the margin**, at the renormalised composites under the
substrate core, the flow bundle and `PhysRange r`: if every composite
monomial whose times lie beyond `r` is approximated by the observer's margin monomials, every
composite monomial is (`exists_beyond_iterate`, `approxKAt_of_iterate`). DERIVED: `2` the least
colour count; `0` the plane and the reference step. -/
theorem approxK_of_beyond_core (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (F : GradientFlowPropsN Wf cf z μ) (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_core S F
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **`ApproxK` is its clause beyond the margin**, under the same inputs. DERIVED: `2` the least
colour count; `0` the plane. -/
theorem approxK_iff_beyond_core (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (F : GradientFlowPropsN Wf cf z μ) (hphys : (Φ0 W).PhysRange r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r)
      ↔ ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
        (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P :=
  ⟨fun hA P _ => approxK_iff_forall.1 hA P, approxK_of_beyond_core hN2 S F hphys⟩

/-- **The per-`N` inputs with `ApproxK` replaced by its clause beyond the margin**:
`ProxyGenLimN.FlowApproxInputsN` with that one clause changed.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of
the block-step flow. -/
def FlowBeyondInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ FlowCov Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`FlowBeyondInputsN` gives `FlowApproxInputsN`** (`approxK_of_beyond_core`). DERIVED: `2` the
least colour count. -/
theorem flowApproxInputsN_of_beyond (hN2 : 2 ≤ N) (h : FlowBeyondInputsN N hN2) :
    FlowApproxInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    hB, h3, hfar⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    approxK_of_beyond_core hN2 S ((gradientFlowPropsN_iff S.b_pos S.scale).2 ⟨hE, hC, hV, hW, hP⟩)
      (sunFam_physRange hN2 hc0 hc hs0 hr) hB, h3, hfar⟩

/-- **`ClayStatementDy` from `FlowBeyondInputsN` at every `N ≥ 2`** (`clayStatement_of_approx`).
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_beyond (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), FlowBeyondInputsN N hN2) :
    MassGap.ClayStatementDy :=
  clayStatement_of_approx fun N hN2 => flowApproxInputsN_of_beyond hN2 (h N hN2)

end Capstone

end MassGap.ApproxJoint

end

#print axioms MassGap.ApproxJoint.jK_sq_le
#print axioms MassGap.ApproxJoint.jK_bound
#print axioms MassGap.ApproxJoint.step_jv
#print axioms MassGap.ApproxJoint.step_sq
#print axioms MassGap.ApproxJoint.step_eq_zero_all
#print axioms MassGap.ApproxJoint.step_injective
#print axioms MassGap.ApproxJoint.approxKAt_iff_mem
#print axioms MassGap.ApproxJoint.approxKAt_of_shift
#print axioms MassGap.ApproxJoint.approxKAt_of_iterate
#print axioms MassGap.ApproxJoint.posSepT_iterate
#print axioms MassGap.ApproxJoint.sepD_pairC
#print axioms MassGap.ApproxJoint.compOrbitBound_of_os0
#print axioms MassGap.ApproxJoint.lowerT_shiftT
#print axioms MassGap.ApproxJoint.lowerT_iterate
#print axioms MassGap.ApproxJoint.exists_beyond_iterate
#print axioms MassGap.ApproxJoint.shiftT_half
#print axioms MassGap.ApproxJoint.exists_shiftT_preimage
#print axioms MassGap.ApproxJoint.kernC_shift_of_os1
#print axioms MassGap.ApproxJoint.reflLim_cap
#print axioms MassGap.ApproxJoint.kernC_symm_of_reflLim
#print axioms MassGap.ApproxJoint.joint_gram
#print axioms MassGap.ApproxJoint.approxK_of_beyond_core
#print axioms MassGap.ApproxJoint.approxK_iff_beyond_core
#print axioms MassGap.ApproxJoint.flowApproxInputsN_of_beyond
#print axioms MassGap.ApproxJoint.clayStatement_of_beyond
