import Mathlib
import MassGap.UVIRSplit

noncomputable section

/-!
# MassGap.KnabeCriterion — a finite-size criterion for a gap, and the crossover without a step across it

## What it gives

1. **The finite-size engine, proved.** `knabe_bound`: on a module with a symmetric non-negative
   bilinear form `B`, a finite family of `B`-self-adjoint idempotents `hᵢ`, and patch weights
   `c k i` (a patch `k` is `A_k = Σᵢ c k i • hᵢ`), with every `hᵢ` covered with total weight `a₁`
   and squared weight `a₂`, every pair `i ≠ j` either commuting with pair weight at most `b`, or
   with pair weight within `w i j` of `b`, and excess weights `w ≥ 0` of row and column sum at most
   `e`: a patch gap `γ · B(A_k x, x) ≤ B(A_k x, A_k x)` at every patch gives, for the whole sum
   `H = Σᵢ hᵢ`,

       (γ·a₁ − a₂ + b − e) · B(H x, x)  ≤  b · B(H x, H x).

   The bound reads only the patch gap and the multiplicities, not the number of terms. With `0/1`
   weights of `n − 1` consecutive terms on a ring (`a₁ = a₂ = n − 1`, `b = n − 2`, `e = 0`) it is
   Knabe's `(n−1)/(n−2)·(γ − 1/(n−1))` (argued, not instantiated here). The proof is the algebra of
   Knabe's argument: expand `Σ_k B(A_k x, A_k x)` over pairs, bound each pair term by its
   multiplicity — a commuting pair has `B(hᵢx, hⱼx) ≥ 0` (`form_comm_nonneg`), any pair has
   `|B(hᵢx, hⱼx)| ≤ (B(hᵢx, hᵢx) + B(hⱼx, hⱼx))/2` (`abs_form_le`) — and sum the patch gaps.
2. **A positive control.** `knabe_commuting`: for pairwise commuting projections, one-term patches
   give `B(Hx, x) ≤ B(Hx, Hx)`, the gap bound `1` of a sum of commuting projections.
3. **Complements.** `selfAdj_id_sub`, `idem_id_sub`, `comm_id_sub`: if `E_l` is a `B`-self-adjoint
   idempotent, so is `id − E_l`, and complements of commuting maps commute; the heat-bath generator
   `Σ_l (id − E_l)` is a sum of the kind `knabe_bound` takes.
4. **The bundle.** `PatchSystem` packs the data and hypotheses; `PatchSystem.globalGap_of_localGap`
   is `knabe_bound` on it, with `PatchSystem.LocalGap γ` the patch gap and `PatchSystem.GlobalGap c`
   the bound `c · B(Hx, x) ≤ B(Hx, Hx)` for the whole sum.
5. **The heat-bath systems of the periodic Wilson measures.** `PeriodicGaugeInv M F`: `F` is
   invariant under every gauge transformation of period `M + 1`; `periodicGaugeInvSubmodule M` is the
   submodule of such observables. `torusForm hN β j` is the torus Wilson `L²` form
   `(x, y) ↦ torusState hN (2j+1) β (x y)` on it (`torusForm_symm`, `torusForm_nonneg`).
   `ReadsNot j l F`: the reading of `F` on the periodic lattice of extent `2(j + 1)` does not depend on
   the link `l`. `WilsonHeatBath hN β j` carries, for every link `l`, a `torusForm`-self-adjoint
   idempotent `condExp l` whose values do not read `l` and which keeps the reading of every
   observable not reading `l`, together with patch weights and their multiplicity hypotheses;
   `WilsonHeatBath.toPatchSystem` is its patch system with `hₗ = id − condExp l`.
6. **At the periodic Wilson state.** `HeatBathDecay τ p hN β` (open): every family of heat-bath
   systems at `β` with a uniform `GlobalGap c > 0` for all large `j` gives
   `ChessboardRead.TorusLagClear` at some lag and rate below one. `PatchGapCheck hN β γ` (open): a
   family of heat-bath systems at `β` whose patch gap `γ` has Knabe constant at least one `c₀ > 0`
   for all large `j`. `gapAt_of_patchGapCheck`, `periodicClayGapAt_of_patchGapCheck`,
   `irGapAt_of_patchGapCheck`: the two give `TransferGap.GapAt`, the Clay gap and
   `UVIRSplit.IRGapAt` at `β`. `fixedWindowDecay_of_patchGapCheck`: at a coupling `β₀` where the two
   hold, `UVLossStep` from any `βUV ≤ β₀` with loss budget below the rate they produce gives
   `FixedWindowDecay`; the ultraviolet step is used only from `βUV` on, and `β₀` may lie past the
   crossover.

## What `WilsonHeatBath` pins, and what it asks

`torusForm` reads an observable only through its torus reading, so on `periodicGaugeInvSubmodule`
the conditions `selfAdj`, `keeps` and `reads_not` on `condExp l` make `x − condExp l x` orthogonal to
every observable not reading `l` and put `condExp l x` among them: `condExp l` is the `torusForm`-orthogonal projection onto them, the conditional expectation of
the torus Wilson measure given every link but `l`, up to observables of zero `torusForm` norm
(`MassGap.HeatBath.expect_heatAvg_mul`). The heat-bath expectation of a torus-gauge-invariant function is
torus-gauge-invariant, so a representative in `periodicGaugeInvSubmodule` is the heat-bath of the
torus reading composed with the restriction of a `ℤ⁴` configuration to one period, which commutes
with periodic gauge transformations (`MassGap.HeatBath.torusCondExp`; `MassGap.BoxPatch.boxHeatBath`
builds the structure). Two conditional expectations at links in no common plaquette commute
(`MassGap.HeatBath.torusCondExp_comm`).

For box patches of side `n` in four dimensions, with links assigned to their base sites and the
torus large enough that no patch wraps: every link lies in `a₁ = a₂ = n⁴` patches, and a pair at base
displacement `v` in `Π_μ (n − |v_μ|)` of them. Take `b = n²(n − 1)²`. The pairs above `b` are the 3
other links at the same base (excess `n²(2n − 1)`) and the 32 links at displacement `±e_μ` (excess
`n²(n − 1)`); every other pair, commuting or not, has pair weight at most `b`, and the links of a
common plaquette sit at displacements with at most two non-zero entries of size one, so the
non-commuting pairs among them have pair weight exactly `b`. This gives `e = n²(38n − 35)` and the
Knabe constant `(γn² − 40n + 36)/(n − 1)²`, positive exactly when `γ > (40n − 36)/n²`
(`MassGap.BoxPatch.knabeConst_box`, `MassGap.BoxPatch.boxKnabe_pos_iff`). At `β = 0` the conditional expectations commute and every patch gap is `1`, so the
check holds at every `n ≥ 40`.

## The literature

* S. Knabe, J. Stat. Phys. 52 (1988) 627–638: for a frustration-free periodic chain of
  nearest-neighbour projections, the gap of the ring is at least `((n−1)/(n−2))(ε_n − 1/(n−1))`,
  `ε_n` the gap of an open chain of `n − 1` terms. D. Gosset, E. Mozgunov, J. Math. Phys. 57 (2016)
  091901, arXiv:1512.00088: thresholds `6/(n(n+1))` in one dimension and `8/n²` on a patch of the
  square lattice. M. Lemm, Contemp. Math. 741 (2020) 121–132, arXiv:1902.07141: in dimension
  `D ≥ 3`, gap `≥ γ_{B_n} − 1/n − 2/n²` for nearest-neighbour projections on a periodic box, by the
  operator inequality `−hh′ − h′h ≤ h + h′`, the operator form of `abs_form_le`. A. Anshu, Phys.
  Rev. B 101 (2020) 165104: thresholds of order `1/t²` in any dimension. A. Young,
  arXiv:2308.01405, Theorem 2.1: Knabe's bound for any projections with ring commutation.
* M. Kastoryano, F. Brandão, Commun. Math. Phys. 344 (2016) 915–957, arXiv:1409.3435: the heat-bath
  generator `Σ_k (E_k − id)` of a commuting local potential is mapped to a frustration-free sum of
  projections and Knabe's criterion is applied to it (their Theorem 30, eq. (118)).
* A. Guionnet, B. Zegarlinski, Sém. Probab. XXXVI, LNM 1801 (2003), Theorem 8.8: for finite-range
  potentials with finite or compact-manifold spins, strong mixing, complete analyticity, a spectral
  gap uniform in the volume and the boundary condition, and a uniform log-Sobolev inequality are
  equivalent; Remark 5 derives decay of covariances from the gap by approximate locality of the
  semigroup. The dynamics there is the Langevin diffusion; D. Stroock, B. Zegarlinski, J. Funct. Anal.
  104 (1992) 299–326 and Commun. Math. Phys. 144 (1992) 303–323.
* H. Shen, R. Zhu, X. Zhu, Commun. Math. Phys. 400 (2023) 805–851, arXiv:2204.12737: at
  `S = Nβ Σ_p Re Tr Q_p`, `SU(N)`, the Bakry–Émery constant `K_S = (N + 2)/2 − 1 − 8N|β|(d − 1)` is
  positive exactly when `|β| < 1/(16(d − 1))`; then log-Sobolev and Poincaré inequalities for the
  Langevin dynamics and exponential decay of covariances (Corollary 1.6). The window is `N`-uniform in
  the 't Hooft coupling: `β_W < N²/48` at `d = 4` in the normalisation `(β_W/N) Re Tr`, a factor of
  about `26` below the `SU(2)` crossover and `30` below `SU(3)`'s. S. Cao, R. Nissim, S. Sheffield,
  arXiv:2509.04688: the area law at `β < 1/(8(d − 1))` in the same normalisation, through the
  Durhuus–Fröhlich reduction (Commun. Math. Phys. 75 (1980) 103–151) to a slab σ-model.
* Comparisons between couplings for `SU(N)` that are theorems act on partition functions: convexity
  of `log Z` (the plaquette expectation is non-decreasing in `β`), monotonicity of `Z` in each
  character coefficient under reflection positivity, and the Migdal–Kadanoff bond-moving bounds
  (E. Tomboulis, arXiv:0707.2179, III.1–III.2). The step from those bounds to confinement at every
  coupling is disputed (K. R. Ito, E. Seiler, arXiv:0711.4930, 0803.3019, 0901.4246: the decimation
  treats `U(1)` and `SU(N)` alike). No published theorem carries decay or a gap from one coupling of
  four-dimensional `SU(N)` to another, and none gives a uniform heat-bath gap or a finite-size
  criterion for lattice Yang–Mills with a continuous group.

## Scope

`knabe_bound` and its corollaries are proved on any module with any symmetric non-negative bilinear
form. `HeatBathDecay` and `PatchGapCheck` are hypotheses, both about the heat-bath systems of the
periodic Wilson measures at `β`. `HeatBathDecay` is a gap-to-decay statement of the
Guionnet–Zegarlinski kind for the heat-bath dynamics on periodic-gauge-invariant observables, which
is not in the literature for lattice gauge theory. `PatchGapCheck` asks the patch gap for all large
torus indices `j`, with the patch data existential (a single patch covering every link makes it a
uniform heat-bath gap; the finite-size content is a witness with box patches); each patch operator acts fibrewise over the links outside its patch, so at box
patches it is one statement about one box of links under every boundary configuration
(`MassGap.BoxPatch.patchGapCheck_of_boxPatchGap`).
-/

namespace MassGap.KnabeCriterion

open MassGap MassGap.AsymptoticScaling MassGap.PeriodicState

/-! ## 1. Weights -/

section Weights

variable {ι κ : Type*} [Fintype κ]

/-- The pair weight `Σ_k c k i · c k j` of two terms: with `0/1` weights, the number of patches
containing both (`pairWeight_indicator`).

DERIVED: no numeral. -/
def pairWeight (c : κ → ι → ℝ) (i j : ι) : ℝ := ∑ k, c k i * c k j

/-- With the indicator weights of patches `S k`, the pair weight of `i` and `j` is the number of
patches containing both (`Finset.sum_boole`).

DERIVED: `1` and `0` are the indicator's values. -/
theorem pairWeight_indicator [DecidableEq ι] (S : κ → Finset ι) (i j : ι) :
    pairWeight (fun k l => if l ∈ S k then (1 : ℝ) else 0) i j
      = ((Finset.univ.filter (fun k => i ∈ S k ∧ j ∈ S k)).card : ℝ) := by
  rw [← Finset.sum_boole]
  unfold pairWeight
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hi : i ∈ S k <;> by_cases hj : j ∈ S k <;> simp [hi, hj]

#print axioms pairWeight_indicator

end Weights

/-! ## 2. The finite-size engine -/

section Engine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The whole sum `H = Σᵢ hᵢ`.

DERIVED: no numeral. -/
def totalOp (h : ι → E →ₗ[ℝ] E) : E →ₗ[ℝ] E := ∑ i, h i

/-- The patch operator `A_k = Σᵢ c k i • hᵢ`.

DERIVED: no numeral. -/
def patchOp (c : κ → ι → ℝ) (h : ι → E →ₗ[ℝ] E) (k : κ) : E →ₗ[ℝ] E := ∑ i, c k i • h i

/-- `H x = Σᵢ hᵢ x` (`LinearMap.sum_apply`).

DERIVED: no numeral. -/
theorem totalOp_apply (h : ι → E →ₗ[ℝ] E) (x : E) : totalOp h x = ∑ i, h i x := by
  simp only [totalOp, LinearMap.sum_apply]

#print axioms totalOp_apply

/-- `A_k x = Σᵢ c k i • hᵢ x` (`LinearMap.sum_apply`, `LinearMap.smul_apply`).

DERIVED: no numeral. -/
theorem patchOp_apply (c : κ → ι → ℝ) (h : ι → E →ₗ[ℝ] E) (k : κ) (x : E) :
    patchOp c h k x = ∑ i, c k i • h i x := by
  simp only [patchOp, LinearMap.sum_apply, LinearMap.smul_apply]

#print axioms patchOp_apply

/-- A bilinear form on two finite sums is the double sum of its values (`map_sum`,
`LinearMap.sum_apply`).

DERIVED: no numeral. -/
theorem form_sum_sum (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (u v : ι → E) :
    B (∑ i, u i) (∑ j, v j) = ∑ i, ∑ j, B (u i) (v j) := by
  have h1 : B (∑ i, u i) = ∑ i, B (u i) := map_sum B u Finset.univ
  rw [h1, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => map_sum (B (u i)) v Finset.univ)

#print axioms form_sum_sum

/-- For a `B`-self-adjoint idempotent `p`: `B(p x, x) = B(p x, p x)`.

DERIVED: no numeral. -/
theorem form_proj_self (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E →ₗ[ℝ] E)
    (hsa : ∀ x y, B (p x) y = B x (p y)) (hid : ∀ x, p (p x) = p x) (x : E) :
    B (p x) x = B (p x) (p x) := by
  rw [hsa x (p x), hid x]
  exact hsa x x

#print axioms form_proj_self

/-- **Two commuting projections pair non-negatively.** For `B`-self-adjoint idempotents `p`, `q`
that commute, and `B` non-negative: `0 ≤ B(p x, q x)`, since `B(p x, q x) = B(pq x, pq x)`.

DERIVED: `0` is the sign of the form. -/
theorem form_comm_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x) (p q : E →ₗ[ℝ] E)
    (hsp : ∀ x y, B (p x) y = B x (p y)) (hsq : ∀ x y, B (q x) y = B x (q y))
    (hip : ∀ x, p (p x) = p x) (hiq : ∀ x, q (q x) = q x)
    (hcomm : ∀ x, p (q x) = q (p x)) (x : E) :
    0 ≤ B (p x) (q x) := by
  have key : B (p (q x)) (p (q x)) = B (p x) (q x) := by
    rw [hsp (q x) (p (q x)), hip (q x), hcomm x, hsq x (q (p x)), hiq (p x), ← hcomm x,
      ← hsp x (q x)]
  rw [← key]
  exact hnn _

#print axioms form_comm_nonneg

/-- **The pair bound.** For a symmetric non-negative `B`: `|B(u, v)| ≤ (B(u, u) + B(v, v))/2`, from
`B(u − v, u − v) ≥ 0` and `B(u + v, u + v) ≥ 0`.

DERIVED: `0` is the sign of the form; `2` is the halving of the arithmetic–geometric mean. -/
theorem abs_form_le (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (u v : E) :
    |B u v| ≤ (B u u + B v v) / 2 := by
  have h1 := hnn (u - v)
  have h2 := hnn (u + v)
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply] at h1 h2
  rw [hsymm v u] at h1 h2
  rw [abs_le]
  constructor <;> linarith

#print axioms abs_form_le

/-- **THE FINITE-SIZE BOUND (Knabe's argument, weighted, with excess).** On a module with a
symmetric non-negative bilinear form `B`, let `hᵢ` be `B`-self-adjoint idempotents and
`A_k = Σᵢ c k i • hᵢ`. Suppose every `i` has cover weight `Σ_k c k i = a₁` and squared weight
`pairWeight c i i = a₂`; every pair `i ≠ j` either commutes with `pairWeight c i j ≤ b`, or has
`|pairWeight c i j − b| ≤ w i j`; `w ≥ 0` with row and column sums at most `e`; and every patch has
the gap `γ · B(A_k x, x) ≤ B(A_k x, A_k x)`. Then, for `H = Σᵢ hᵢ` and every `x`,
`(γ·a₁ − a₂ + b − e) · B(Hx, x) ≤ b · B(Hx, Hx)`.

The proof sums the patch gaps: `Σ_k B(A_k x, x) = a₁ · B(Hx, x)` and
`Σ_k B(A_k x, A_k x) = Σ_{i,j} pairWeight c i j · B(hᵢx, hⱼx)`; each pair term is at most
`b · B(hᵢx, hⱼx)` plus `(a₂ − b) · B(hᵢx, hᵢx)` on the diagonal plus
`w i j · (B(hᵢx, hᵢx) + B(hⱼx, hⱼx))/2` (`form_comm_nonneg`, `abs_form_le`), and the three sums are
`b · B(Hx, Hx)`, `(a₂ − b) · B(Hx, x)` and at most `e · B(Hx, x)`.

DERIVED: `0` is the sign of the form and of the excess weights. -/
theorem knabe_bound (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (c : κ → ι → ℝ) (w : ι → ι → ℝ) {a₁ a₂ b e γ : ℝ}
    (hcov : ∀ i, ∑ k, c k i = a₁) (hcov2 : ∀ i, pairWeight c i i = a₂)
    (hpair : ∀ i j, i ≠ j →
      ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ e) (hcol : ∀ j, ∑ i, w i j ≤ e)
    (hloc : ∀ k x, γ * B (patchOp c h k x) x ≤ B (patchOp c h k x) (patchOp c h k x)) (x : E) :
    (γ * a₁ - a₂ + b - e) * B (totalOp h x) x ≤ b * B (totalOp h x) (totalOp h x) := by
  classical
  -- the whole sum
  have hD : B (totalOp h x) x = ∑ i, B (h i x) (h i x) := by
    rw [totalOp_apply, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => form_proj_self B (h i) (hsa i) (hid i) x)
  have hHH : B (totalOp h x) (totalOp h x) = ∑ i, ∑ j, B (h i x) (h j x) := by
    rw [totalOp_apply]
    exact form_sum_sum B (fun i => h i x) (fun j => h j x)
  -- the patches
  have hA : ∀ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, c k i * c k j * B (h i x) (h j x) := by
    intro k
    rw [patchOp_apply, form_sum_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hAx : ∀ k, B (patchOp c h k x) x = ∑ i, c k i * B (h i x) (h i x) := by
    intro k
    rw [patchOp_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [form_proj_self B (h i) (hsa i) (hid i) x]
  have hsumA : ∑ k, B (patchOp c h k x) (patchOp c h k x)
      = ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x) := by
    simp only [hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pairWeight, Finset.sum_mul]
  have hsumAx : ∑ k, B (patchOp c h k x) x = a₁ * ∑ i, B (h i x) (h i x) := by
    simp only [hAx]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, hcov i]
  -- the patch gaps, summed
  have hlocsum : γ * (a₁ * ∑ i, B (h i x) (h i x))
      ≤ ∑ k, B (patchOp c h k x) (patchOp c h k x) := by
    rw [← hsumAx, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hloc k x)
  rw [hsumA] at hlocsum
  -- each pair term
  have hterm : ∀ i j, pairWeight c i j * B (h i x) (h j x)
      ≤ b * B (h i x) (h j x) + ((if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
        + w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
    intro i j
    have hii := hnn (h i x)
    have hjj := hnn (h j x)
    have hwP : 0 ≤ w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2 :=
      div_nonneg (mul_nonneg (hw i j) (add_nonneg hii hjj)) zero_le_two
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, hcov2 _]
      linarith
    · rw [if_neg hij]
      rcases hpair i j hij with ⟨hcomm, hle⟩ | hex
      · have hP0 : 0 ≤ B (h i x) (h j x) :=
          form_comm_nonneg B hnn (h i) (h j) (hsa i) (hsa j) (hid i) (hid j) hcomm x
        have hm := mul_le_mul_of_nonneg_right hle hP0
        linarith
      · have habs : |B (h i x) (h j x)| ≤ (B (h i x) (h i x) + B (h j x) (h j x)) / 2 :=
          abs_form_le B hsymm hnn (h i x) (h j x)
        have h1 : (pairWeight c i j - b) * B (h i x) (h j x)
            ≤ w i j * ((B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
          calc (pairWeight c i j - b) * B (h i x) (h j x)
              ≤ |(pairWeight c i j - b) * B (h i x) (h j x)| := le_abs_self _
            _ = |pairWeight c i j - b| * |B (h i x) (h j x)| := abs_mul _ _
            _ ≤ w i j * ((B (h i x) (h i x) + B (h j x) (h j x)) / 2) :=
                mul_le_mul hex habs (abs_nonneg _) (hw i j)
        linarith
  -- the three sums
  have hdiag : ∑ i, ∑ j, (if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
      = (a₂ - b) * ∑ i, B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  have hwsplit : ∑ i, ∑ j, w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2
      = (∑ i, ∑ j, w i j * B (h i x) (h i x) + ∑ i, ∑ j, w i j * B (h j x) (h j x)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hrowb : ∑ i, ∑ j, w i j * B (h i x) (h i x) ≤ e * ∑ i, B (h i x) (h i x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (hnn (h i x))
  have hcolb : ∑ i, ∑ j, w i j * B (h j x) (h j x) ≤ e * ∑ j, B (h j x) (h j x) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol j) (hnn (h j x))
  have hsumT : ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x)
      ≤ b * ∑ i, ∑ j, B (h i x) (h j x) + ((a₂ - b) * ∑ i, B (h i x) (h i x)
        + (∑ i, ∑ j, w i j * B (h i x) (h i x) + ∑ i, ∑ j, w i j * B (h j x) (h j x)) / 2) := by
    calc ∑ i, ∑ j, pairWeight c i j * B (h i x) (h j x)
        ≤ ∑ i, ∑ j, (b * B (h i x) (h j x)
            + ((if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
              + w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = b * ∑ i, ∑ j, B (h i x) (h j x)
            + (∑ i, ∑ j, (if i = j then (a₂ - b) * B (h i x) (h i x) else 0)
              + ∑ i, ∑ j, w i j * (B (h i x) (h i x) + B (h j x) (h j x)) / 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hdiag, hwsplit]
  rw [hD, hHH]
  linarith

#print axioms knabe_bound

/-- **Positive control: commuting projections.** If every two `hᵢ` commute, the one-term patches
(`κ = ι`, `c k i = 1` at `k = i` and `0` otherwise) have `a₁ = a₂ = 1`, pair weight `0` off the
diagonal and patch gap `1` (`form_proj_self`), and `knabe_bound` at `b = 1`, `e = 0` gives
`B(Hx, x) ≤ B(Hx, Hx)`: the gap bound `1` of a sum of commuting projections.

DERIVED: `0` is the sign of the form. CHOSEN: `b = 1` in the proof; every `b > 0` gives the same
constant `(1 − 1 + b)/b = 1`. -/
theorem knabe_commuting (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (h : ι → E →ₗ[ℝ] E)
    (hsa : ∀ i x y, B (h i x) y = B x (h i y)) (hid : ∀ i x, h i (h i x) = h i x)
    (hcomm : ∀ i j x, h i (h j x) = h j (h i x)) (x : E) :
    B (totalOp h x) x ≤ B (totalOp h x) (totalOp h x) := by
  classical
  have hprod : ∀ k i j : ι, (if k = i then (1 : ℝ) else 0) * (if k = j then 1 else 0)
      = if k = i ∧ k = j then 1 else 0 := by
    intro k i j
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj]
  have hcov : ∀ i, ∑ k, (fun (k l : ι) => if k = l then (1 : ℝ) else 0) k i = 1 := by
    intro i
    show ∑ k, (if k = i then (1 : ℝ) else 0) = 1
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hcov2 : ∀ i, pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i i = 1 := by
    intro i
    have hsq : ∀ k : ι, (if k = i then (1 : ℝ) else 0) * (if k = i then 1 else 0)
        = if k = i then 1 else 0 := by
      intro k
      split_ifs <;> norm_num
    show ∑ k, (if k = i then (1 : ℝ) else 0) * (if k = i then 1 else 0) = 1
    rw [Finset.sum_congr rfl (fun k _ => hsq k), Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
  have hpair : ∀ i j, i ≠ j →
      ((∀ y, h i (h j y) = h j (h i y))
        ∧ pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i j ≤ 1)
      ∨ |pairWeight (fun (k l : ι) => if k = l then (1 : ℝ) else 0) i j - 1|
          ≤ (fun _ _ => (0 : ℝ)) i j := by
    intro i j hij
    refine Or.inl ⟨hcomm i j, ?_⟩
    simp only [pairWeight, hprod]
    have hz : ∀ k ∈ (Finset.univ : Finset ι), (if k = i ∧ k = j then (1 : ℝ) else 0) = 0 :=
      fun k _ => if_neg (fun hk => hij (hk.1.symm.trans hk.2))
    rw [Finset.sum_eq_zero hz]
    norm_num
  have hAk : ∀ k y, patchOp (fun (k l : ι) => if k = l then (1 : ℝ) else 0) h k y = h k y := by
    intro k y
    rw [patchOp_apply, Finset.sum_eq_single k]
    · show (if k = k then (1 : ℝ) else 0) • h k y = h k y
      rw [if_pos rfl, one_smul]
    · intro i _ hik
      show (if k = i then (1 : ℝ) else 0) • h i y = 0
      rw [if_neg (fun hki => hik hki.symm), zero_smul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hk := knabe_bound (κ := ι) B hsymm hnn h hsa hid
    (fun (k l : ι) => if k = l then (1 : ℝ) else 0) (fun _ _ => (0 : ℝ))
    (a₁ := 1) (a₂ := 1) (b := 1) (e := 0) (γ := 1)
    hcov hcov2 hpair (fun _ _ => le_rfl) (fun _ => by simp) (fun _ => by simp)
    (fun k y => by
      rw [hAk k y, one_mul]
      exact (form_proj_self B (h k) (hsa k) (hid k) y).le) x
  linarith

#print axioms knabe_commuting

/-- `B(Hx, x) ≥ 0` for a sum of `B`-self-adjoint idempotents: each term is `B(hᵢx, hᵢx)`.

DERIVED: `0` is the sign of the form. -/
theorem totalOp_form_nonneg (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hnn : ∀ x, 0 ≤ B x x)
    (h : ι → E →ₗ[ℝ] E) (hsa : ∀ i x y, B (h i x) y = B x (h i y))
    (hid : ∀ i x, h i (h i x) = h i x) (x : E) :
    0 ≤ B (totalOp h x) x := by
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [form_proj_self B (h i) (hsa i) (hid i) x]
  exact hnn (h i x)

#print axioms totalOp_form_nonneg

/-- The complement of a `B`-self-adjoint map is `B`-self-adjoint.

DERIVED: no numeral. -/
theorem selfAdj_id_sub (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P : E →ₗ[ℝ] E)
    (hsa : ∀ x y, B (P x) y = B x (P y)) (x y : E) :
    B (((LinearMap.id : E →ₗ[ℝ] E) - P) x) y = B x (((LinearMap.id : E →ₗ[ℝ] E) - P) y) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hsa]

#print axioms selfAdj_id_sub

/-- The complement of an idempotent is idempotent.

DERIVED: no numeral. -/
theorem idem_id_sub (P : E →ₗ[ℝ] E) (hid : ∀ x, P (P x) = P x) (x : E) :
    ((LinearMap.id : E →ₗ[ℝ] E) - P) (((LinearMap.id : E →ₗ[ℝ] E) - P) x) = ((LinearMap.id : E →ₗ[ℝ] E) - P) x := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hid, sub_self, sub_zero]

#print axioms idem_id_sub

/-- Complements of commuting maps commute.

DERIVED: no numeral. -/
theorem comm_id_sub (P Q : E →ₗ[ℝ] E) (hcomm : ∀ x, P (Q x) = Q (P x)) (x : E) :
    ((LinearMap.id : E →ₗ[ℝ] E) - P) (((LinearMap.id : E →ₗ[ℝ] E) - Q) x) = ((LinearMap.id : E →ₗ[ℝ] E) - Q) (((LinearMap.id : E →ₗ[ℝ] E) - P) x) := by
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hcomm]
  abel

#print axioms comm_id_sub

end Engine

/-! ## 3. The bundle -/

/-- **A patch system**: a module with a symmetric non-negative bilinear form, a finite family of
self-adjoint idempotents, patch weights and the multiplicity hypotheses of `knabe_bound`: cover
weight `a₁`, squared weight `a₂`, every pair `i ≠ j` commuting with pair weight at most `b` or within
`w i j` of `b`, and `w ≥ 0` with row and column sums at most `e`.

DERIVED: `0` is the sign of the form and of the excess weights. -/
structure PatchSystem where
  E : Type
  [acg : AddCommGroup E]
  [mod : Module ℝ E]
  ι : Type
  [fι : Fintype ι]
  κ : Type
  [fκ : Fintype κ]
  B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ
  symm : ∀ x y, B x y = B y x
  nonneg : ∀ x, 0 ≤ B x x
  h : ι → E →ₗ[ℝ] E
  selfAdj : ∀ i x y, B (h i x) y = B x (h i y)
  idem : ∀ i x, h i (h i x) = h i x
  c : κ → ι → ℝ
  w : ι → ι → ℝ
  a₁ : ℝ
  a₂ : ℝ
  b : ℝ
  e : ℝ
  cover : ∀ i, ∑ k, c k i = a₁
  cover2 : ∀ i, pairWeight c i i = a₂
  pair : ∀ i j, i ≠ j →
    ((∀ x, h i (h j x) = h j (h i x)) ∧ pairWeight c i j ≤ b) ∨ |pairWeight c i j - b| ≤ w i j
  w_nonneg : ∀ i j, 0 ≤ w i j
  row : ∀ i, ∑ j, w i j ≤ e
  col : ∀ j, ∑ i, w i j ≤ e

attribute [instance] PatchSystem.acg PatchSystem.mod PatchSystem.fι PatchSystem.fκ

namespace PatchSystem

/-- The whole sum `H = Σᵢ hᵢ` of a patch system.

DERIVED: no numeral. -/
def H (S : PatchSystem) : S.E →ₗ[ℝ] S.E := totalOp S.h

/-- The patch operator `A_k` of a patch system.

DERIVED: no numeral. -/
def A (S : PatchSystem) (k : S.κ) : S.E →ₗ[ℝ] S.E := patchOp S.c S.h k

/-- **The patch gap** `γ`: `γ · B(A_k x, x) ≤ B(A_k x, A_k x)` at every patch `k` and every `x`.

DERIVED: no numeral. -/
def LocalGap (S : PatchSystem) (γ : ℝ) : Prop :=
  ∀ k x, γ * S.B (S.A k x) x ≤ S.B (S.A k x) (S.A k x)

/-- **The gap of the whole sum** `c`: `c · B(Hx, x) ≤ B(Hx, Hx)` at every `x`.

DERIVED: no numeral. -/
def GlobalGap (S : PatchSystem) (c : ℝ) : Prop :=
  ∀ x, c * S.B (S.H x) x ≤ S.B (S.H x) (S.H x)

/-- The Knabe constant `(γ·a₁ − a₂ + b − e)/b` of a patch system at patch gap `γ`.

DERIVED: no numeral. -/
def knabeConst (S : PatchSystem) (γ : ℝ) : ℝ := (γ * S.a₁ - S.a₂ + S.b - S.e) / S.b

/-- **The patch gap gives the gap of the whole sum.** At `0 < b`, `LocalGap γ` gives
`GlobalGap (knabeConst γ)` (`knabe_bound`, divided by `b`).

DERIVED: `0` is the sign of `b`. -/
theorem globalGap_of_localGap (S : PatchSystem) {γ : ℝ} (hb : 0 < S.b) (hloc : S.LocalGap γ) :
    S.GlobalGap (S.knabeConst γ) := by
  intro x
  have hk := knabe_bound S.B S.symm S.nonneg S.h S.selfAdj S.idem S.c S.w S.cover S.cover2
    S.pair S.w_nonneg S.row S.col hloc x
  have hH : S.H x = totalOp S.h x := rfl
  rw [hH]
  unfold PatchSystem.knabeConst
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  linarith

#print axioms globalGap_of_localGap

/-- `B(Hx, x) ≥ 0` in a patch system (`totalOp_form_nonneg`).

DERIVED: `0` is the sign of the form. -/
theorem H_form_nonneg (S : PatchSystem) (x : S.E) : 0 ≤ S.B (S.H x) x :=
  totalOp_form_nonneg S.B S.nonneg S.h S.selfAdj S.idem x

#print axioms H_form_nonneg

/-- `GlobalGap` is inherited downward: `c ≤ c'` and `GlobalGap c'` give `GlobalGap c`
(`H_form_nonneg`).

DERIVED: no numeral. -/
theorem globalGap_mono (S : PatchSystem) {c c' : ℝ} (hcc : c ≤ c') (hg : S.GlobalGap c') :
    S.GlobalGap c := by
  intro x
  have h1 := mul_le_mul_of_nonneg_right hcc (S.H_form_nonneg x)
  linarith [hg x]

#print axioms globalGap_mono

end PatchSystem

/-! ## 4. The heat-bath systems of the periodic Wilson measures -/

section Wilson

variable {N : ℕ}

/-- **Periodic gauge invariance at extent `M + 1`.** `F` is unchanged by the gauge transformation of
every gauge function of the periodic lattice of extent `M + 1`, read on `ℤ⁴` through
`InfiniteLattice.siteMod M`. Every gauge-invariant observable (`GaugeInvariantAlgebra.IsIGaugeInvariant`)
is periodic gauge invariant at every extent (`periodicGaugeInv_of_isIGaugeInvariant`).

DERIVED: `4` is the spacetime dimension; `1` is `siteMod`'s successor writing the extent. -/
def PeriodicGaugeInv (M : ℕ) (F : C(GibbsSpec.IConf (SUN.SU N), ℝ)) : Prop :=
  ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SUN.SU N) (U : GibbsSpec.IConf (SUN.SU N)),
    F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (InfiniteLattice.siteMod M x)) U) = F U

/-- Every gauge-invariant observable is periodic gauge invariant at every extent: a periodic gauge
function read through `siteMod M` is one gauge function of `ℤ⁴`.

DERIVED: `1` is `siteMod`'s successor writing the extent. -/
theorem periodicGaugeInv_of_isIGaugeInvariant (M : ℕ) {F : C(GibbsSpec.IConf (SUN.SU N), ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant (G := SUN.SU N) F) : PeriodicGaugeInv M F :=
  fun g U => hF (fun x => g (InfiniteLattice.siteMod M x)) U

#print axioms periodicGaugeInv_of_isIGaugeInvariant

/-- The periodic gauge-invariant observables at extent `M + 1`, a submodule of
`C(IConf (SU N), ℝ)`.

DERIVED: `1` is `siteMod`'s successor writing the extent. -/
def periodicGaugeInvSubmodule (M : ℕ) : Submodule ℝ C(GibbsSpec.IConf (SUN.SU N), ℝ) where
  carrier := {F | PeriodicGaugeInv M F}
  add_mem' := by
    intro F G hF hG g U
    simp only [ContinuousMap.add_apply]
    rw [hF g U, hG g U]
  zero_mem' := by
    intro g U
    rfl
  smul_mem' := by
    intro c F hF g U
    simp only [ContinuousMap.smul_apply]
    rw [hF g U]

/-- **The torus Wilson `L²` form** at extent index `j`:
`(x, y) ↦ torusState hN (2j+1) β (x y)` on the periodic gauge-invariant observables at the extent
`2(j + 1)` of `torusState hN (2j+1) β`. Bilinear by `DLRLimit.State.map_add`,
`DLRLimit.State.map_smul`.

DERIVED: `2 * j + 1` is the index of the even-extent family `torusState hN (2j+1) β` that
`periodicState` is the limit of; `0` is the excluded rank in `hN`. -/
def torusForm (hN : N ≠ 0) (β : ℝ) (j : ℕ) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => torusState hN (2 * j + 1) β
      ((x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) * (y : C(GibbsSpec.IConf (SUN.SU N), ℝ))))
    (fun x₁ x₂ y => by simp only [Submodule.coe_add, add_mul, DLRLimit.State.map_add])
    (fun c x y => by
      simp only [Submodule.coe_smul, smul_mul_assoc, DLRLimit.State.map_smul, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [Submodule.coe_add, mul_add, DLRLimit.State.map_add])
    (fun c x y => by
      simp only [Submodule.coe_smul, mul_smul_comm, DLRLimit.State.map_smul, smul_eq_mul])

/-- `torusForm hN β j x y = torusState hN (2j+1) β (x y)`, by definition.

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN`. -/
theorem torusForm_apply (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j x y = torusState hN (2 * j + 1) β
      ((x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) * (y : C(GibbsSpec.IConf (SUN.SU N), ℝ))) := rfl

#print axioms torusForm_apply

/-- `torusForm` is symmetric (`mul_comm`).

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN`. -/
theorem torusForm_symm (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j x y = torusForm hN β j y x := by
  rw [torusForm_apply, torusForm_apply, mul_comm (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))]

#print axioms torusForm_symm

/-- `torusForm` is non-negative: `x x ≥ 0` pointwise (`DLRLimit.State.nonneg`).

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN` and
the sign of the form. -/
theorem torusForm_nonneg (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    0 ≤ torusForm hN β j x x := by
  rw [torusForm_apply]
  exact DLRLimit.State.nonneg _ _ (fun U => by
    rw [ContinuousMap.mul_apply]
    exact mul_self_nonneg _)

#print axioms torusForm_nonneg

/-- **An observable not reading a torus link.** The reading of `F` on the periodic lattice of extent
`2(j + 1)` (`PeriodicState.torusObs (2j+1) F`) is unchanged by every change of the configuration at
the link `l`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def ReadsNot (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (F : C(GibbsSpec.IConf (SUN.SU N), ℝ)) : Prop :=
  ∀ (W : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SUN.SU N) (g : SUN.SU N),
    torusObs (2 * j + 1) F (Function.update W l g) = torusObs (2 * j + 1) F W

/-- **The heat-bath system of the periodic Wilson measure** at coupling `β` and extent index `j`.
For every torus link `l`, `condExp l` is a `torusForm`-self-adjoint idempotent of the periodic
gauge-invariant observables whose values do not read `l`, and which keeps the torus reading of every
observable not reading `l`: the conditional expectation given every link but `l`, up to observables
of zero `torusForm` norm (module docstring). With it, patch weights `c` over a finite patch type `κ`
and the multiplicity hypotheses of `knabe_bound` for the complements `id − condExp l`: cover weight
`a₁`, squared weight `a₂`, every pair of links either with commuting `condExp` and pair weight at most
`b`, or with pair weight within `w` of `b`, and `w ≥ 0` with row and column sums at most `e`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the sign of the excess
weights. -/
structure WilsonHeatBath (hN : N ≠ 0) (β : ℝ) (j : ℕ) where
  κ : Type
  [fκ : Fintype κ]
  condExp : WilsonHypercubic.Link 4 (2 * j + 1 + 1) →
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
  selfAdj : ∀ l x y, torusForm hN β j (condExp l x) y = torusForm hN β j x (condExp l y)
  idem : ∀ l x, condExp l (condExp l x) = condExp l x
  reads_not : ∀ l x, ReadsNot j l ((condExp l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    : C(GibbsSpec.IConf (SUN.SU N), ℝ))
  keeps : ∀ l (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))),
    ReadsNot j l (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) →
      torusObs (2 * j + 1) ((condExp l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SUN.SU N), ℝ))
        = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))
  c : κ → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ
  w : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ
  a₁ : ℝ
  a₂ : ℝ
  b : ℝ
  e : ℝ
  cover : ∀ l, ∑ k, c k l = a₁
  cover2 : ∀ l, pairWeight c l l = a₂
  pair : ∀ l l', l ≠ l' →
    ((∀ x, condExp l (condExp l' x) = condExp l' (condExp l x)) ∧ pairWeight c l l' ≤ b)
      ∨ |pairWeight c l l' - b| ≤ w l l'
  w_nonneg : ∀ l l', 0 ≤ w l l'
  row : ∀ l, ∑ l', w l l' ≤ e
  col : ∀ l', ∑ l, w l l' ≤ e

attribute [instance] WilsonHeatBath.fκ

/-- **The patch system of a heat-bath system**: the periodic gauge-invariant observables with
`torusForm`, the torus links, and `hₗ = id − condExp l` (`selfAdj_id_sub`, `idem_id_sub`,
`comm_id_sub`).

DERIVED: `2 * j + 1` is the index of the even-extent family; `0` is the excluded rank in `hN`. -/
def WilsonHeatBath.toPatchSystem {hN : N ≠ 0} {β : ℝ} {j : ℕ} (S : WilsonHeatBath hN β j) :
    PatchSystem where
  E := ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
  ι := WilsonHypercubic.Link 4 (2 * j + 1 + 1)
  κ := S.κ
  B := torusForm hN β j
  symm := torusForm_symm hN β j
  nonneg := torusForm_nonneg hN β j
  h := fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - S.condExp l
  selfAdj := fun l => selfAdj_id_sub (torusForm hN β j) (S.condExp l) (S.selfAdj l)
  idem := fun l => idem_id_sub (S.condExp l) (S.idem l)
  c := S.c
  w := S.w
  a₁ := S.a₁
  a₂ := S.a₂
  b := S.b
  e := S.e
  cover := S.cover
  cover2 := S.cover2
  pair := fun l l' hll' => (S.pair l l' hll').imp_left
    (fun hc => ⟨fun x => comm_id_sub (S.condExp l) (S.condExp l') hc.1 x, hc.2⟩)
  w_nonneg := S.w_nonneg
  row := S.row
  col := S.col

/-! ## 5. At the periodic Wilson state -/

/-- **A uniform heat-bath gap gives decay at the periodic state.** For
every family `S j` of heat-bath systems of the periodic Wilson measures at `β`, one per extent index
`j`, and every `c > 0` with `GlobalGap c` at `(S j).toPatchSystem` for all large `j`: some lag
`m ≠ 0` and rate `0 < r < 1` have `ChessboardRead.TorusLagClear τ p hN β m r`.

`GlobalGap c` at the heat-bath system is a Poincaré inequality for the heat-bath dynamics on
periodic gauge-invariant observables, uniform in the extent; the implication is a gap-to-decay
theorem of the kind of Guionnet–Zegarlinski's Theorem 8.8, Remark 5.
`MassGap.HeatBathGapDecay.heatBathDecay_of_locality` proves it from
`MassGap.HeatBathGapDecay.HeatBathLocality`, whose analytic content is fixed-volume ergodicity of the
heat bath (`MassGap.HeatBathGapDecay.ErgodicLimit`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the excluded lag and the sign of
`c` and `r`; `1` is the rate the gap must beat. -/
def HeatBathDecay (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) : Prop :=
  ∀ (S : ∀ j : ℕ, WilsonHeatBath hN β j) (c : ℝ), 0 < c →
    (∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap c) →
      ∃ m : ℕ, m ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ChessboardRead.TorusLagClear τ p hN β m r

/-- **THE FINITE CHECK.** A family `S j` of heat-bath systems of the periodic Wilson measures at `β`
and one `c₀ > 0` such that, for all large `j`, `S j` has `0 < b`, Knabe constant at patch gap `γ` at
least `c₀`, and patch gap `γ`. The patch data is existential: the one-patch witness (every weight
`1`, `a₁ = a₂ = b = 1`, `e = 0`, Knabe constant `γ`) makes the check equivalent to a uniform
heat-bath gap, so the finite-size content is carried by a witness with box patches. At box patches
the multiplicities are the same at every extent that holds a patch without wrapping, and the patch
gap is one statement about one box of links under every boundary configuration (`MassGap.BoxPatch.patchGapCheck_of_boxPatchGap`).

DERIVED: `0` is the excluded rank in `hN` and the sign of `b` and `c₀`. -/
def PatchGapCheck (hN : N ≠ 0) (β γ : ℝ) : Prop :=
  ∃ S : ∀ j : ℕ, WilsonHeatBath hN β j, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ j in Filter.atTop,
    0 < (S j).b ∧ c₀ ≤ (S j).toPatchSystem.knabeConst γ ∧ (S j).toPatchSystem.LocalGap γ

/-- **The single-lag input from the finite check.** Under `HeatBathDecay τ p hN β` and
`PatchGapCheck hN β γ`: some lag `m ≠ 0` and rate `0 < r < 1` have `TorusLagClear τ p hN β m r`.
`PatchSystem.globalGap_of_localGap` and `PatchSystem.globalGap_mono` give `GlobalGap c₀` at the
family for all large `j`, and `HeatBathDecay` gives the lag.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the excluded lag and the lower end
of `r`; `1` is the rate the gap must beat. -/
theorem torusLagClear_of_patchGapCheck (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β γ : ℝ}
    (hdec : HeatBathDecay τ p hN β) (hcheck : PatchGapCheck hN β γ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ChessboardRead.TorusLagClear τ p hN β m r := by
  obtain ⟨S, c₀, hc₀, hev⟩ := hcheck
  have hG : ∀ᶠ j in Filter.atTop, (S j).toPatchSystem.GlobalGap c₀ := hev.mono (fun j hj =>
    (S j).toPatchSystem.globalGap_mono hj.2.1
      ((S j).toPatchSystem.globalGap_of_localGap hj.1 hj.2.2))
  exact hdec S c₀ hc₀ hG

#print axioms torusLagClear_of_patchGapCheck

/-- **The gap at the periodic state from the finite check.** At `0 ≤ β`, under
`HeatBathDecay τ p hN β` and `PatchGapCheck hN β γ`: some `0 < r < 1` has `TransferGap.GapAt` at
`periodicGaugeInvData τ p hN β` (`torusLagClear_of_patchGapCheck`,
`ChessboardRead.periodic_form_lag_of_torusLagClear`, `ChessboardRead.gapAt_of_lag` with
`PeriodicState.periodic_positiveTransfer`).

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the lower end of `β` and `r`;
`1` is the rate the gap must beat. -/
theorem gapAt_of_patchGapCheck (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β γ : ℝ} (hβ : 0 ≤ β)
    (hdec : HeatBathDecay τ p hN β) (hcheck : PatchGapCheck hN β γ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ TransferGap.GapAt (periodicGaugeInvData τ p hN β) r := by
  obtain ⟨m, hm, r, hr0, hr1, hlag⟩ := torusLagClear_of_patchGapCheck τ p hN hdec hcheck
  exact ⟨r, hr0, hr1, ChessboardRead.gapAt_of_lag (periodicGaugeInvData τ p hN β)
    (periodic_positiveTransfer τ p hN hβ) hm hr0.le
    (fun x hx => ChessboardRead.periodic_form_lag_of_torusLagClear τ p hN β m r hlag x hx)⟩

#print axioms gapAt_of_patchGapCheck

/-- **The Clay gap at the periodic state from the finite check.** At `2 ≤ N`, `0 ≤ β`, under
`HeatBathDecay τ p hN β` and `PatchGapCheck hN β γ`: some `0 < r < 1` has
`PeriodicContent.PeriodicClayGapAt τ p hN β r` — spectrum in `{1} ∪ [0, r]`, the vacuum complement
contracted by `r`, and that complement non-zero (`ChessboardRead.periodic_clayGapAt_of_torusLag`).

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance of the
real trace; `0` is the excluded rank and the lower end of `β` and `r`; `1` is the rate the gap must
beat. -/
theorem periodicClayGapAt_of_patchGapCheck (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {β γ : ℝ} (hβ : 0 ≤ β) (hdec : HeatBathDecay τ p hN β) (hcheck : PatchGapCheck hN β γ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt τ p hN β r := by
  obtain ⟨m, hm, r, hr0, hr1, hlag⟩ := torusLagClear_of_patchGapCheck τ p hN hdec hcheck
  exact ⟨r, hr0, hr1,
    ChessboardRead.periodic_clayGapAt_of_torusLag τ p hN2 hN hβ hm hr0 hr1 hlag⟩

#print axioms periodicClayGapAt_of_patchGapCheck

/-- **The IR input from the finite check.** At `1 ≤ N`, `0 < β₀`, under `HeatBathDecay τ p hN β₀`
and `PatchGapCheck hN β₀ γ`: some `M₀ > 0` has `UVIRSplit.IRGapAt τ p hN β₀ M₀`. The proof takes
`M₀ = −log r / aRun N β₀` for the rate `r` of `gapAt_of_patchGapCheck`, so that
`e^{−M₀·aRun N β₀} = r`.

DERIVED: `4` is the spacetime dimension; `1` is the least colour count, for `aRun_pos`; `0` is the
excluded rank and the sign of `β₀` and `M₀`. -/
theorem irGapAt_of_patchGapCheck (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ γ : ℝ}
    (hβ₀ : 0 < β₀) (hdec : HeatBathDecay τ p hN β₀) (hcheck : PatchGapCheck hN β₀ γ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ UVIRSplit.IRGapAt τ p hN β₀ M₀ := by
  obtain ⟨r, hr0, hr1, hg⟩ := gapAt_of_patchGapCheck τ p hN hβ₀.le hdec hcheck
  have ha : 0 < aRun N β₀ := aRun_pos hN1 hβ₀
  refine ⟨-Real.log r / aRun N β₀, div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) ha, ?_⟩
  unfold UVIRSplit.IRGapAt
  rw [div_mul_cancel₀ _ ha.ne', neg_neg, Real.exp_log hr0]
  exact hg

#print axioms irGapAt_of_patchGapCheck

/-- **The uniform physical gap with no step across the crossover.** At `2 ≤ N`, `0 < L`, `0 < β₀`,
under `HeatBathDecay τ p hN β₀` and `PatchGapCheck hN β₀ γ`: there is `M₀ > 0` with
`UVIRSplit.IRGapAt τ p hN β₀ M₀` such that every loss function `ε` with a loss budget `E < M₀` for
the dyadic tower below `aRun N β₀`, and `UVIRSplit.UVLossStep τ p hN βUV ε` from any `βUV ≤ β₀`,
gives `WeakCouplingWindow.FixedWindowDecay τ p hN L` (`irGapAt_of_patchGapCheck`,
`UVIRSplit.fixedWindowDecay_of_uv_ir`). The ultraviolet step enters only above `βUV`, and `β₀` may
lie past the crossover, where `aRun N β₀` is a lattice spacing.

DERIVED: `4` is the spacetime dimension; `2` is the least rank with a non-zero Haar variance; `0` is
the excluded rank and the sign of `L`, `β₀` and `M₀`. -/
theorem fixedWindowDecay_of_patchGapCheck (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {L : ℝ} (hL : 0 < L) {β₀ βUV γ : ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hdec : HeatBathDecay τ p hN β₀) (hcheck : PatchGapCheck hN β₀ γ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ UVIRSplit.IRGapAt τ p hN β₀ M₀ ∧
      ∀ (ε : ℝ → ℝ) (E : ℝ), UVIRSplit.LossBudget ε (aRun N β₀) E → E < M₀ →
        UVIRSplit.UVLossStep τ p hN βUV ε → WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨M₀, hM₀, hir⟩ := irGapAt_of_patchGapCheck τ p (by omega : 1 ≤ N) hN hβ₀ hdec hcheck
  exact ⟨M₀, hM₀, hir, fun ε E hbud hEM huv =>
    UVIRSplit.fixedWindowDecay_of_uv_ir τ p hN2 hN hL hβ₀ hUVβ₀ hbud hEM huv hir⟩

#print axioms fixedWindowDecay_of_patchGapCheck

end Wilson

end MassGap.KnabeCriterion
