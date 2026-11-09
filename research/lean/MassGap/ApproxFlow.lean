import Mathlib
import MassGap.MixConvRP

/-!
# MassGap.ApproxFlow — `ApproxK` through a family of observers `W_s`

`MixConvRP.clayStatementAt_SU_reflAvg'` takes `hA : ApproxK (kernC (CbR N z) 0) (mixKR W z r)
(gramF W r)` at one configuration flow `W`. This module replaces the one observer in that input by a
family `Ws : S → ConfFlow N` (read: the flows at flow times `s`, with `s → 0`), states the family
input on the real kernels, and proves what it gives at `W`.

## 1. Real combinations in a complex Hilbert space

* `range_yL`: the real combinations `yL v c` are the real span of `v`; `closure_yL_subset`: if every
  `u Q` lies in the closure of the real combinations of `v`, so does every real combination of `u`,
  and its closure.
* `mem_closure_of_real_inner`: if `v` has a real Gram matrix and its complex span is dense, every
  vector `x` whose pairings `⟪x, v Q⟫` are all real lies in the closure of the real combinations of
  `v`. (A complex approximant `∑ (aQ + i bQ) v_Q` is no closer to `x` than its real part
  `∑ aQ v_Q`: the cross term `2 Re ⟪x − ∑ aQ v_Q, i ∑ bQ v_Q⟫` vanishes, the pairing being real.)
* `approx_of_real_pairing`: so, in such a space, vectors `w P` with real cross pairings `X` and Gram
  matrix `Kc` satisfy `Approx Kc X v` with no further input.

## 2. The family form and what it gives at one observer

* `ApproxKFamily Kc Xs Gs`: for every composite `P` and `ε > 0` there are an index `s` and real
  coefficients `c` on the margin monomials with `Kc(P,P) − 2 Xs s (P, c) + Gs s (c, c) ≤ ε`.
  `approxKFamily_const`: at a constant family it is `ApproxK`.
* `exists_family_not_approxK` (on abstract kernels over `Unit`): `ApproxKFamily` together with
  `JointRPK` at the fixed observer and at every member does not give `ApproxK` there (one composite
  read exactly by the family, `X = 0` at the observer).
* `approxK_of_family`: in a complete space holding the observer's vectors `v` (Gram `G`) and the
  family's vectors `U s` (Gram `Gs s`) with all inner products real, joint positivity `JointRP` of
  the composites against the union family `v ⊔ U` (cross kernel `xU X Xs`), the nesting
  `U s Q ∈ closure (range (yL v))`, and `ApproxKFamily Kc Xs Gs`, give `ApproxK Kc X G`.
* `approxK_of_family_dense`: the same with the nesting replaced by density of the complex span of
  `v` (`mem_closure_of_real_inner`).

## 3. The kernel convergence form

* `FlowKernelConv Kc Xs Gs`: for every composite `P`, a sequence of indices `s n` and coefficients
  `c n` with `Xs (s n) (P, c n) → Kc(P,P)` and `Gs (s n) (c n, c n) → Kc(P,P)`: the mixed reading of
  the composite against the flowed combination, and the flowed combination's own two-point reading,
  both converge to the composite's two-point reading.
* `approxKFamily_of_flowKernelConv`, and `flowKernelConv_of_approxKFamily` under `JointRPK` at every
  member (`(K − X)² ≤ K · d` from `JointRPK` at `P' = P`); `approxKFamily_iff_flowKernelConv`.

## 4. On the real objects

* `ApproxKFlow hN2 Ws z r`: `ApproxKFamily` at `kernC (CbR N z) 0`, `mixKR (Ws s) z r`,
  `gramF (Ws s) r`. The margin monomials `MarginMono N 0 r` do not depend on the flow, so every
  member is read on the same index set.
* `approxKFlow_iff`: if every member meets `ClassMoments` and `PhysRange r`, and `CompOS (CbR N z)`
  holds, `ApproxKFlow` is equivalent to `FlowKernelConv` on those kernels (`ReflAvg.jointRPK_R` with
  `MixConvRP.mixConvF_R` at each member).
* `approxK_of_flow`: in `preH W`, vectors `U s` of the members' margin monomials with Gram
  `gramF (Ws s) r`, all inner products among `vO W` and `U` real, `JointRP` of the composites against
  `vO W ⊔ U` with cross kernel `xU (mixKR W z r) (mixKR (Ws s) z r)`, and `ApproxKFlow` give `hA`.
  The nesting is discharged by `obsGen_flow` (dense complex span of `gvecT`) and
  `mem_closure_of_real_inner`.
* `clayStatementAt_SU_flow`: `clayStatementAt_SU_reflAvg'` with `hA` replaced by those inputs.

## What the route generalises (proved reading, `approxKFamily_const`)

* With the constant family `Ws = fun _ : Unit => W`, `hF : ApproxKFlow` is literally `hA`
  (`approxKFamily_const`), so `clayStatementAt_SU_flow` generalises `clayStatementAt_SU_reflAvg'`
  and gains over it only through a non-constant family.
* Inside `preH W`, the vectors `U s` carry the members' fields in the fixed observer's space, and
  `approxK_of_flow` places them in the closure of the real combinations of `vO W`: for members other
  than `W` that is a generation statement of the same kind as `hA`.

## What is not proved here

* `FlowKernelConv` on the real kernels (the small-flow-time convergence of the members' readings to
  the composites' two-point readings). ARGUED: it is the leading term of the small-flow-time
  expansion of the flowed fields in the interacting state; `ObsLead.classicalLead_obs` and
  `ClassicalLimit` are statements on classical configurations and do not give it.
* The vectors `U s` in `preH W` and the joint inputs `hreal`, `hJ` of `approxK_of_flow`: the members'
  fields carried in the fixed observer's space. `exists_family_not_approxK` shows, on abstract
  kernels, that some input of this kind is needed. ARGUED: for members at larger flow time than `W` a semigroup flow makes the
  members' fields fields of `W`; for members at smaller flow time (`s → 0`), carrying them in `preH W`
  is a generation statement of the same kind as `hA`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the zero vector, the sign, the empty time and the plane; `1` the unit
coefficient and the unit kernel; `2` the cross-term factor and the square; `1/2` the tolerance.
-/

noncomputable section

namespace MassGap.ApproxFlow

open Filter
open scoped Topology

open MassGap.CompositeLink MassGap.ContinuumFlow

/-! ## 1. Real combinations in a complex Hilbert space -/

section RealSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {M : Type}

/-- `yL v c = ∑_Q c_Q • v_Q` with the real scalar action. DERIVED: no numeral. -/
theorem yL_eq_sum_real (v : M → H) (c : M →₀ ℝ) : yL v c = c.sum fun Q a => a • v Q := by
  unfold yL
  exact Finsupp.sum_congr fun Q _ => Complex.coe_smul _ _

/-- **The real combinations are the real span.** DERIVED: no numeral. -/
theorem range_yL (v : M → H) :
    Set.range (yL v) = (Submodule.span ℝ (Set.range v) : Set H) := by
  ext x
  rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (yL_eq_sum_real v c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, yL_eq_sum_real v c⟩

/-- DERIVED: no numeral. -/
theorem closure_range_yL (v : M → H) :
    closure (Set.range (yL v))
      = ((Submodule.span ℝ (Set.range v)).topologicalClosure : Set H) := by
  rw [Submodule.topologicalClosure_coe, range_yL]

/-- **Closure membership is transitive for real combinations**: if every `u Q` lies in the closure
of the real combinations of `v`, so does the closure of the real combinations of `u`.

DERIVED: no numeral. -/
theorem closure_yL_subset {M' : Type} (u : M' → H) (v : M → H)
    (h : ∀ Q, u Q ∈ closure (Set.range (yL v))) :
    closure (Set.range (yL u)) ⊆ closure (Set.range (yL v)) := by
  rw [closure_range_yL u, closure_range_yL v]
  have hle : Submodule.span ℝ (Set.range u)
      ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    rw [Submodule.span_le]
    rintro _ ⟨Q, rfl⟩
    have hQ := h Q
    rw [closure_range_yL v] at hQ
    exact hQ
  exact SetLike.coe_subset_coe.mpr
    (Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_topologicalClosure _))

/-- **A vector with real pairings lies in the closure of the real combinations.** If `v` has real
Gram matrix `G` and dense complex span, every `x` with `⟪x, v Q⟫ = g Q` real lies in the closure of
`range (yL v)`.

DERIVED: `2` the cross-term factor and the square; `0` the vanishing real part. -/
theorem mem_closure_of_real_inner (v : M → H) (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ))
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) {x : H} (g : M → ℝ)
    (hx : ∀ Q, inner ℂ x (v Q) = (g Q : ℂ)) : x ∈ closure (Set.range (yL v)) := by
  have hx' : x ∈ closure (Submodule.span ℂ (Set.range v) : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hd]
    exact Submodule.mem_top
  rw [Metric.mem_closure_iff] at hx' ⊢
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hx' ε hε
  obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  have hsplit : (d.sum fun Q a => a • v Q)
      = yL v (d.mapRange Complex.re Complex.zero_re)
        + Complex.I • yL v (d.mapRange Complex.im Complex.zero_im) := by
    unfold yL
    rw [Finsupp.sum_mapRange_index (fun _ => by simp),
      Finsupp.sum_mapRange_index (fun _ => by simp), Finsupp.smul_sum, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun Q _ => ?_
    rw [smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]
  set c := d.mapRange Complex.re Complex.zero_re
  set e := d.mapRange Complex.im Complex.zero_im
  refine ⟨yL v c, ⟨c, rfl⟩, ?_⟩
  rw [hsplit, dist_eq_norm] at hxy
  rw [dist_eq_norm]
  have h1 : inner ℂ x (yL v e) = (xL g e : ℂ) := inner_yL_right v e x g hx
  have h2 : inner ℂ (yL v c) (yL v e) = (xL (fun Q => xL (fun Q' => G Q' Q) c) e : ℂ) :=
    inner_yL_right v e (yL v c) (fun Q => xL (fun Q' => G Q' Q) c)
      (fun Q => inner_yL_left v c (v Q) (fun Q' => G Q' Q) (fun Q' => hG Q' Q))
  have hab : inner ℂ (x - yL v c) (yL v e)
      = ((xL g e - xL (fun Q => xL (fun Q' => G Q' Q) c) e : ℝ) : ℂ) := by
    rw [inner_sub_left, h1, h2, Complex.ofReal_sub]
  have hre : RCLike.re (inner ℂ (x - yL v c) (Complex.I • yL v e)) = 0 := by
    rw [inner_smul_right, hab, RCLike.re_to_complex]
    simp
  have key : ‖x - yL v c‖ ^ 2 ≤ ‖x - (yL v c + Complex.I • yL v e)‖ ^ 2 := by
    rw [show x - (yL v c + Complex.I • yL v e) = (x - yL v c) - Complex.I • yL v e by abel,
      norm_sub_sq (𝕜 := ℂ) (x - yL v c), hre]
    nlinarith [sq_nonneg ‖Complex.I • yL v e‖]
  have h3 : ‖x - yL v c‖ ^ 2 < ε ^ 2 := by
    have h4 := norm_nonneg (x - (yL v c + Complex.I • yL v e))
    nlinarith
  nlinarith [norm_nonneg (x - yL v c)]

/-- **Real cross pairings give `Approx`** when `v` has a real Gram matrix and dense complex span:
vectors `w P` with `⟪w P, v Q⟫ = X(P,Q)` and `⟪w P, w P'⟫ = Kc(P,P')` satisfy `Approx Kc X v`.

DERIVED: no numeral. -/
theorem approx_of_real_pairing {I : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} (v : M → H)
    (G : M → M → ℝ) (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ))
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (w : I → H)
    (hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ))
    (hK : ∀ P P', inner ℂ (w P) (w P') = (Kc P P' : ℂ)) : Approx Kc X v :=
  (approx_iff w hX hK).mpr fun P => mem_closure_of_real_inner v G hG hd (X P) (hX P)

end RealSpan

/-! ## 2. The family form -/

section Family

variable {M S I : Type}

/-- **Approximability by a family of observers**: for every composite `P` and `ε > 0` there are a
member `s` and real coefficients `c` with `Kc(P,P) − 2 Xs s (P, c) + Gs s (c, c) ≤ ε`.

DERIVED: `2` the cross-term factor; `0` the sign of `ε`. -/
def ApproxKFamily (Kc : I → I → ℝ) (Xs : S → I → M → ℝ) (Gs : S → M → M → ℝ) : Prop :=
  ∀ (P : I) (ε : ℝ), 0 < ε → ∃ (s : S) (c : M →₀ ℝ),
    Kc P P - 2 * xL (Xs s P) c + gForm (Gs s) c c ≤ ε

/-- **At a constant family the family form is `ApproxK`.** DERIVED: no numeral. -/
theorem approxKFamily_const {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ} :
    ApproxKFamily Kc (fun _ : Unit => X) (fun _ => G) ↔ ApproxK Kc X G := by
  constructor
  · intro h P ε hε
    obtain ⟨_, c, hc⟩ := h P ε hε
    exact ⟨c, hc⟩
  · intro h P ε hε
    obtain ⟨c, hc⟩ := h P ε hε
    exact ⟨(), c, hc⟩

/-- **The family alone does not give `ApproxK` at a fixed observer**: one composite with `Kc = 1`,
read exactly by the family (`Xs = Gs = 1`), and an observer with `X = 0` and any `G` with
`gForm G c c ≥ 0`: `ApproxKFamily` and `JointRPK Kc X G` hold, `ApproxK Kc X G` fails. The members
also meet `JointRPK` (the form is `(1 + t − c)²`), so `JointRPK` at every member does not close the
gap either.

DERIVED: `1` the unit kernel and the unit coefficient; `0` the vanishing cross kernel; `1/2` the
tolerance; `2` the cross-term factor and the square. -/
theorem exists_family_not_approxK {G : Unit → Unit → ℝ} (hG : ∀ c : Unit →₀ ℝ, 0 ≤ gForm G c c) :
    ApproxKFamily (fun _ _ : Unit => (1 : ℝ)) (fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℝ))
        (fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℝ))
      ∧ JointRPK (fun _ _ : Unit => (1 : ℝ)) (fun _ _ : Unit => (1 : ℝ)) (fun _ _ : Unit => (1 : ℝ))
      ∧ JointRPK (fun _ _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) G
      ∧ ¬ ApproxK (fun _ _ : Unit => (1 : ℝ)) (fun _ (_ : Unit) => (0 : ℝ)) G := by
  have hx : ∀ c : Unit →₀ ℝ, xL (fun _ : Unit => (0 : ℝ)) c = 0 := fun c => by
    unfold xL
    simp
  refine ⟨fun P ε hε => ⟨(), Finsupp.single () 1, ?_⟩, fun P P' t c => ?_, fun P P' t c => ?_,
    fun hA => ?_⟩
  · rw [xL_single, gForm_single]
    norm_num
    exact hε.le
  · show 0 ≤ 1 + 2 * t * 1 + t ^ 2 * 1 - 2 * xL (fun _ : Unit => (1 : ℝ)) c
      - 2 * t * xL (fun _ : Unit => (1 : ℝ)) c + gForm (fun _ _ : Unit => (1 : ℝ)) c c
    rw [Finsupp.unique_single c, xL_single, gForm_single]
    try dsimp only
    nlinarith [sq_nonneg (1 + t - c default)]
  · show 0 ≤ 1 + 2 * t * 1 + t ^ 2 * 1 - 2 * xL (fun _ : Unit => (0 : ℝ)) c
      - 2 * t * xL (fun _ : Unit => (0 : ℝ)) c + gForm G c c
    rw [hx]
    nlinarith [hG c, sq_nonneg (1 + t)]
  · obtain ⟨c, hc⟩ := hA () (1 / 2) (by norm_num)
    have hc' : 1 - 2 * xL (fun _ : Unit => (0 : ℝ)) c + gForm G c c ≤ 1 / 2 := hc
    rw [hx] at hc'
    linarith [hG c]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The union family** `v ⊔ U`: the observer's vectors on `inl`, the members' on `inr (s, Q)`.
DERIVED: no numeral. -/
def vU (v : M → H) (U : S → M → H) : M ⊕ (S × M) → H :=
  Sum.elim v fun p => U p.1 p.2

/-- **The union cross kernel** `X ⊔ Xs`. DERIVED: no numeral. -/
def xU (X : I → M → ℝ) (Xs : S → I → M → ℝ) (P : I) : M ⊕ (S × M) → ℝ :=
  Sum.elim (X P) fun p => Xs p.1 P p.2

/-- DERIVED: `0` the zero coefficient. -/
theorem xL_mapDomain_inr (X : I → M → ℝ) (Xs : S → I → M → ℝ) (P : I) (s : S) (c : M →₀ ℝ) :
    xL (xU X Xs P) (c.mapDomain fun Q => (Sum.inr (s, Q) : M ⊕ (S × M))) = xL (Xs s P) c := by
  unfold xL
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  rfl

/-- DERIVED: `0` the zero coefficient. -/
theorem yL_mapDomain_inr (v : M → H) (U : S → M → H) (s : S) (c : M →₀ ℝ) :
    yL (vU v U) (c.mapDomain fun Q => (Sum.inr (s, Q) : M ⊕ (S × M))) = yL (U s) c := by
  unfold yL
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by rw [Complex.ofReal_add, add_smul])]
  rfl

/-- **`ApproxK` at the observer from the family.** In a complete space, with the observer's vectors
`v` (Gram `G`) and the members' vectors `U s` (Gram `Gs s`), all inner products among `v ⊔ U` real,
joint positivity of the composites against `v ⊔ U` with cross kernel `X ⊔ Xs`, every `U s Q` in the
closure of the real combinations of `v`, and `ApproxKFamily Kc Xs Gs`: `ApproxK Kc X G`.

The composites' vectors are `exists_link` against `v ⊔ U` (the family approximants are combinations
of `v ⊔ U`); they lie in the closure of the real combinations of `v ⊔ U` (`approx_iff`), hence of
`v` (`closure_yL_subset`), and pair with `v` by `X`; `approx_iff` at `v` gives `ApproxK`.

DERIVED: `1` the unit coefficient. -/
theorem approxK_of_family [CompleteSpace H] {Kc : I → I → ℝ} {X : I → M → ℝ}
    {Xs : S → I → M → ℝ} (v : M → H) (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ)) (U : S → M → H) (Gs : S → M → M → ℝ)
    (hGs : ∀ s Q Q', inner ℂ (U s Q) (U s Q') = (Gs s Q Q' : ℂ))
    (hreal : ∀ a b, (inner ℂ (vU v U a) (vU v U b)).im = 0)
    (hJ : JointRP Kc (xU X Xs) (vU v U))
    (hnest : ∀ s Q, U s Q ∈ closure (Set.range (yL v)))
    (hF : ApproxKFamily Kc Xs Gs) : ApproxK Kc X G := by
  have hGU : ∀ a b, inner ℂ (vU v U a) (vU v U b)
      = (((inner ℂ (vU v U a) (vU v U b) : ℂ).re : ℝ) : ℂ) :=
    fun a b => Complex.ext (by simp) (by simp [hreal a b])
  have hAU : Approx Kc (xU X Xs) (vU v U) := by
    intro P ε hε
    obtain ⟨s, c, hc⟩ := hF P ε hε
    refine ⟨c.mapDomain fun Q => Sum.inr (s, Q), ?_⟩
    unfold dist2
    rw [xL_mapDomain_inr, yL_mapDomain_inr, norm_yL_sq (Gs s) (hGs s)]
    exact hc
  obtain ⟨w, hwX, hwK⟩ :=
    exists_link (fun a b => (inner ℂ (vU v U a) (vU v U b) : ℂ).re) hGU hJ hAU
  have hmem := (approx_iff w hwX hwK).mp hAU
  have hsub := closure_yL_subset (vU v U) v fun a => by
    rcases a with Q | ⟨s, Q⟩
    · refine subset_closure ⟨Finsupp.single Q 1, ?_⟩
      show yL v (Finsupp.single Q 1) = v Q
      rw [yL_single, Complex.ofReal_one, one_smul]
    · exact hnest s Q
  have hX : ∀ P Q, inner ℂ (w P) (v Q) = (X P Q : ℂ) := fun P Q => hwX P (Sum.inl Q)
  exact (approx_iff_K G hG).mp ((approx_iff w hX hwK).mpr fun P => hsub (hmem P))

/-- **`approxK_of_family` with the nesting from density**: if the complex span of `v` is dense, the
nesting holds (`mem_closure_of_real_inner`, the pairings `⟪U s Q, v Q'⟫` being real by `hreal`).

DERIVED: no numeral. -/
theorem approxK_of_family_dense [CompleteSpace H] {Kc : I → I → ℝ} {X : I → M → ℝ}
    {Xs : S → I → M → ℝ} (v : M → H) (G : M → M → ℝ)
    (hG : ∀ Q Q', inner ℂ (v Q) (v Q') = (G Q Q' : ℂ))
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (U : S → M → H) (Gs : S → M → M → ℝ)
    (hGs : ∀ s Q Q', inner ℂ (U s Q) (U s Q') = (Gs s Q Q' : ℂ))
    (hreal : ∀ a b, (inner ℂ (vU v U a) (vU v U b)).im = 0)
    (hJ : JointRP Kc (xU X Xs) (vU v U))
    (hF : ApproxKFamily Kc Xs Gs) : ApproxK Kc X G := by
  refine approxK_of_family v G hG U Gs hGs hreal hJ (fun s Q => ?_) hF
  refine mem_closure_of_real_inner v G hG hd (fun Q' => (inner ℂ (U s Q) (v Q') : ℂ).re)
    fun Q' => ?_
  have h := hreal (Sum.inr (s, Q)) (Sum.inl Q')
  simp only [vU, Sum.elim_inr, Sum.elim_inl] at h
  exact Complex.ext (by simp) (by simp [h])

end Family

/-! ## 3. The kernel convergence form -/

section Conv

variable {M S I : Type} {Kc : I → I → ℝ} {Xs : S → I → M → ℝ} {Gs : S → M → M → ℝ}

/-- **Convergence of the members' readings to the composite's two-point reading**: for every
composite `P`, members `s n` and coefficients `c n` with `Xs (s n) (P, c n) → Kc(P,P)` and
`Gs (s n) (c n, c n) → Kc(P,P)`.

DERIVED: no numeral. -/
def FlowKernelConv (Kc : I → I → ℝ) (Xs : S → I → M → ℝ) (Gs : S → M → M → ℝ) : Prop :=
  ∀ P : I, ∃ (s : ℕ → S) (c : ℕ → M →₀ ℝ),
    Tendsto (fun n => xL (Xs (s n) P) (c n)) atTop (𝓝 (Kc P P))
      ∧ Tendsto (fun n => gForm (Gs (s n)) (c n) (c n)) atTop (𝓝 (Kc P P))

/-- **Kernel convergence gives the family form**: the residual tends to `K − 2K + K = 0`.

DERIVED: `2` the cross-term factor; `0` the limit. -/
theorem approxKFamily_of_flowKernelConv (h : FlowKernelConv Kc Xs Gs) :
    ApproxKFamily Kc Xs Gs := by
  intro P ε hε
  obtain ⟨s, c, hX, hG⟩ := h P
  have hd := ((tendsto_const_nhds (x := Kc P P)).sub (hX.const_mul 2)).add hG
  have h0 : Kc P P - 2 * Kc P P + Kc P P = 0 := by ring
  rw [h0] at hd
  obtain ⟨n, hn⟩ := (hd.eventually (ge_mem_nhds hε)).exists
  exact ⟨s n, c n, hn⟩

/-- **Under `JointRPK` at every member, the family form gives kernel convergence.** With
`d = K − 2X + G`, `JointRPK` at `P' = P` reads `d + 2t(K − X) + t²K ≥ 0`, so `(K − X)² ≤ K d`;
`d → 0` gives `X → K` and `G = d − K + 2X → K`.

DERIVED: `1` the shift in `1/(n+1)`; `0` the limit and the empty time; `2` the cross-term factor. -/
theorem flowKernelConv_of_approxKFamily (hJ : ∀ s, JointRPK Kc (Xs s) (Gs s))
    (h : ApproxKFamily Kc Xs Gs) : FlowKernelConv Kc Xs Gs := by
  intro P
  choose s c hc using fun n : ℕ => h P (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hd0 : ∀ n, 0 ≤ Kc P P - 2 * xL (Xs (s n) P) (c n) + gForm (Gs (s n)) (c n) (c n) :=
    fun n => by
      have h0 := hJ (s n) P P 0 (c n)
      linarith
  have hd : Tendsto (fun n => Kc P P - 2 * xL (Xs (s n) P) (c n) + gForm (Gs (s n)) (c n) (c n))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hd0 hc
  have hq : ∀ n, (Kc P P - xL (Xs (s n) P) (c n)) ^ 2
      ≤ Kc P P * (Kc P P - 2 * xL (Xs (s n) P) (c n) + gForm (Gs (s n)) (c n) (c n)) :=
    fun n => sq_le_of_quad fun t => by
      have h0 := hJ (s n) P P t (c n)
      linarith
  have hB := tendsto_zero_of_sq_le hq hd
  have hX : Tendsto (fun n => xL (Xs (s n) P) (c n)) atTop (𝓝 (Kc P P)) := by
    have h1 := hB.neg.add_const (Kc P P)
    simp only [neg_sub, sub_add_cancel, neg_zero, zero_add] at h1
    exact h1
  refine ⟨s, c, hX, ?_⟩
  have h2 := (hd.sub_const (Kc P P)).add (hX.const_mul 2)
  have e : (0 : ℝ) - Kc P P + 2 * Kc P P = Kc P P := by ring
  rw [e] at h2
  refine h2.congr fun n => ?_
  ring

/-- **The family form is kernel convergence** under `JointRPK` at every member. DERIVED: no
numeral. -/
theorem approxKFamily_iff_flowKernelConv (hJ : ∀ s, JointRPK Kc (Xs s) (Gs s)) :
    ApproxKFamily Kc Xs Gs ↔ FlowKernelConv Kc Xs Gs :=
  ⟨flowKernelConv_of_approxKFamily hJ, approxKFamily_of_flowKernelConv⟩

end Conv

/-! ## 4. On the real objects -/

section Flow

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ClayStatement MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP

/-- **The family input on the real kernels**: `ApproxKFamily` at the averaged composites' kernel
`kernC (CbR N z) 0`, the members' mixed kernels `mixKR (Ws s) z r` and flowed kernels
`gramF (Ws s) r`. DERIVED: `0` the plane. -/
abbrev ApproxKFlow {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N) (z : Chan → ℕ → ℝ) (r : ℝ) :
    Prop :=
  ApproxKFamily (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (fun s => mixKR hN2 (Ws s) z r)
    (fun s => gramF hN2 (Ws s) r)

/-- **The kernel convergence on the real kernels.** DERIVED: `0` the plane. -/
abbrev FlowKernelConvR {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N) (z : Chan → ℕ → ℝ)
    (r : ℝ) : Prop :=
  FlowKernelConv (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (fun s => mixKR hN2 (Ws s) z r)
    (fun s => gramF hN2 (Ws s) r)

/-- **`ApproxKFlow` is the kernel convergence** when every member meets `ClassMoments` and
`PhysRange r` and `CompOS (CbR N z)` holds: `JointRPK` at each member is `ReflAvg.jointRPK_R` with
`MixConvRP.mixConvF_R`. DERIVED: no numeral. -/
theorem approxKFlow_iff {S : Type} (hN2 : 2 ≤ N) (Ws : S → ConfFlow N) {r : ℝ}
    (hUs : ∀ s, ∃ t C : ℝ, ClassMoments (ne_zero_of_two_le hN2) (Ws s) (SymPlaqClass N) t C)
    (hphys : ∀ s, (Φ0 (Ws s)).PhysRange r) (z : Chan → ℕ → ℝ)
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z)) :
    ApproxKFlow hN2 Ws z r ↔ FlowKernelConvR hN2 Ws z r :=
  approxKFamily_iff_flowKernelConv fun s => by
    obtain ⟨t, C, hU⟩ := hUs s
    exact jointRPK_R hN2 (Ws s) hU (hphys s) z hCO (mixConvF_R hN2 (Ws s) hU (hphys s) z hCO)

/-- **`hA` from the family, in the fixed observer's space.** In `preH W`: vectors `U s` of the
members' margin monomials with Gram `gramF (Ws s) r`, all inner products among `vO W ⊔ U` real,
`JointRP` of the composites against `vO W ⊔ U` with cross kernel `mixKR W ⊔ mixKR (Ws s)`, and
`ApproxKFlow` give `ApproxK` at `W`. The nesting is `obsGen_flow` (the complex span of `gvecT` is
dense) with `mem_closure_of_real_inner`.

DERIVED: `0` the plane. -/
theorem approxK_of_flow {S : Type} (hN2 : 2 ≤ N) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (Φ0 W).PhysRange r) (z : Chan → ℕ → ℝ) (Ws : S → ConfFlow N)
    (U : S → MarginMono N 0 r → preH (ne_zero_of_two_le hN2) W hU hphys)
    (hGs : ∀ s Q Q', inner ℂ (U s Q) (U s Q') = (gramF hN2 (Ws s) r Q Q' : ℂ))
    (hreal : ∀ a b, (inner ℂ (vU (vO hN2 W hU hphys) U a) (vU (vO hN2 W hU hphys) U b)).im = 0)
    (hJ : JointRP (kernC (ne_zero_of_two_le hN2) (CbR N z) 0)
      (xU (mixKR hN2 W z r) (fun s => mixKR hN2 (Ws s) z r)) (vU (vO hN2 W hU hphys) U))
    (hF : ApproxKFlow hN2 Ws z r) :
    ApproxK (kernC (ne_zero_of_two_le hN2) (CbR N z) 0) (mixKR hN2 W z r) (gramF hN2 W r) := by
  obtain ⟨hG1, -, hG3⟩ := obsGen_flow (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) (preB (ne_zero_of_two_le hN2) W hU) 0
    (Flow.posPreserving_of_physRange (ne_zero_of_two_le hN2) (Φ0 W) hphys 0)
  have hG : ∀ Q Q' : MarginMono N 0 r, inner ℂ (vO hN2 W hU hphys Q) (vO hN2 W hU hphys Q')
      = (gramF hN2 W r Q Q' : ℂ) := hG1
  exact approxK_of_family_dense (vO hN2 W hU hphys) (gramF hN2 W r) hG hG3 U
    (fun s => gramF hN2 (Ws s) r) hGs hreal hJ hF

/-- **The SU capstone at the reflection-averaged composites, with `hA` from a family of
observers**: `clayStatementAt_SU_reflAvg'` with `hA` given by `approxK_of_flow`.

The inputs: `ht`, `hU`, `hphys` at one `r`, `hfar`, `z` with `hz`, `hzS`, `hzP`, `G`, `hK`, `hAF`, `hObs`,
`hWard`, `hCO`, and in place of `hA`: the family `Ws`, its vectors `U` in `preH W` with `hGs`,
`hreal`, `hJ`, and `hF : ApproxKFlow`.

DERIVED: `2` the least colour count and the limits of the scalar and pseudoscalar factors; `0` the
plane; `4` the dimension. -/
theorem clayStatementAt_SU_flow {S : Type} (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N)
    (z : Chan → ℕ → ℝ) (hz : ∀ c k, z c k ≠ 0)
    (hzS : Tendsto (fun k => z .sc k * dySpacing N k ^ 4) atTop (𝓝 2))
    (hzP : Tendsto (fun k => z .ps k * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) (rhoD (fR N) z) G)
    (hAF : AFCoefficient N G)
    (hObs : NonGaussLink.ObsThreePoint (ne_zero_of_two_le hN2) z)
    (hWard : WardT (ne_zero_of_two_le hN2) (rhoD (fR N) z))
    (hCO : CompOS (ne_zero_of_two_le hN2) (CbR N z))
    (Ws : S → ConfFlow N)
    (U : S → MarginMono N 0 r → preH (ne_zero_of_two_le hN2) W hU hphys)
    (hGs : ∀ s Q Q', inner ℂ (U s Q) (U s Q') = (gramF hN2 (Ws s) r Q Q' : ℂ))
    (hreal : ∀ a b, (inner ℂ (vU (vO hN2 W hU hphys) U a) (vU (vO hN2 W hU hphys) U b)).im = 0)
    (hJ : JointRP (kernC (ne_zero_of_two_le hN2) (CbR N z) 0)
      (xU (mixKR hN2 W z r) (fun s => mixKR hN2 (Ws s) z r)) (vU (vO hN2 W hU hphys) U))
    (hF : ApproxKFlow hN2 Ws z r) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_reflAvg' hN2 W ht hU hphys hfar z hz hzS hzP G hK hAF hObs hWard hCO
    (approxK_of_flow hN2 W hU hphys z Ws U hGs hreal hJ hF)

end Flow

end MassGap.ApproxFlow

end

#print axioms MassGap.ApproxFlow.yL_eq_sum_real
#print axioms MassGap.ApproxFlow.range_yL
#print axioms MassGap.ApproxFlow.closure_range_yL
#print axioms MassGap.ApproxFlow.closure_yL_subset
#print axioms MassGap.ApproxFlow.mem_closure_of_real_inner
#print axioms MassGap.ApproxFlow.approx_of_real_pairing
#print axioms MassGap.ApproxFlow.approxKFamily_const
#print axioms MassGap.ApproxFlow.exists_family_not_approxK
#print axioms MassGap.ApproxFlow.xL_mapDomain_inr
#print axioms MassGap.ApproxFlow.yL_mapDomain_inr
#print axioms MassGap.ApproxFlow.approxK_of_family
#print axioms MassGap.ApproxFlow.approxK_of_family_dense
#print axioms MassGap.ApproxFlow.approxKFamily_of_flowKernelConv
#print axioms MassGap.ApproxFlow.flowKernelConv_of_approxKFamily
#print axioms MassGap.ApproxFlow.approxKFamily_iff_flowKernelConv
#print axioms MassGap.ApproxFlow.approxKFlow_iff
#print axioms MassGap.ApproxFlow.approxK_of_flow
#print axioms MassGap.ApproxFlow.clayStatementAt_SU_flow
