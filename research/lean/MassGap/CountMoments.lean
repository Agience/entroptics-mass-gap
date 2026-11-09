import Mathlib
import MassGap.ApertureCount
import MassGap.TowerOpen

/-!
# MassGap.CountMoments — the class-moment clause `hU` of (E) from the Rényi-½ count

`OneInput.clayStatement_of_strongEnd` has three open inputs, (S), (M) and (E) = `ConstantPhysicsLine.ExistAlong`. The
leading analytic clause of (E) is the class-moment bound `hU : ClassMomentsG (schedAlongG _ βs) W (SymPlaqClassG
(SU N)) t C₀`. This module derives `hU` from the count mechanism of `ApertureCount` stated on the tower's
own schedule. Declarations are in the namespace `MassGap.CountMoments`.

## 1. What `hU` asks

`ClassMomentsG S W D t C` (`ObserverLinkedG`, through `ObserverOSG.CubeMomentsAtG`): for every field
`O ∈ D`, eventually in the step, for every `R ≥ 0` and `p`,
`ν_k((∑_{x ∈ [−R,R]⁴ ∩ a_k ℤ⁴} O ∘ V_k ∘ T_x)^{2p}) ≤ ((2R + 1)⁴)^{2p} (2p)! t^{−2p} C`.
The cube sum carries no cell-volume weight, so `hU` forces the flowed reading of `O` to be of order
`a_k⁴` in every moment. `ObserverOSG.state_cubeSumG_pow_le` reduces every cube to the unit cube, and
`state_cubeSumG_one_pow_le` (below) reduces the unit cube to one site at the cost `(5⁴ / a_k⁴)^{2p}`. So
`hU` is a factorial bound on the single-site moments `ν_k(F_k^{2p}) ≤ (2p)! (c a_k⁴)^{2p}`, uniform over
the class and the zoom.

## 2. What the count delivers

`ApertureCount.state_pow_le_renyi`: for a finite screen of readings that all have the moments of one
observable `G₀`, if every eigenmode of the screen's Gram matrix has `ν(e_α^{2p}) ≤ K λ_α^p`, then
`ν(G₀^{2p}) ≤ K (R ν(G₀²))^p` with `R = spRenyi` the Rényi-½ count of the normalized spectrum. The volume
of the screen cancels: one second moment and the count give every even moment.

## 3. The bridge (proved)

On a schedule `S`, a flow `W` and a class `D`:

* `cRead S W k O = F_k − ν_k(F_k)`, `F_k = O ∘ V_k`, the connected flowed reading (the Gram the entroptics
  read measures is the centred one, as in `ApertureCount` §3);
* `cScreen S W ρ k O`: its translates over the box `{0, …, L_k − 1}⁴`, `L_k = ⌈ρ / a_k⌉` (`scrSide`), a
  box of fixed physical side `ρ`; its side grows without bound along the zoom;
* `ModeHyperG` (H1 of `ApertureCountAt` at the plaquette's Wick index `1`, on this screen, basis-free):
  one `C ≥ 0` with, eventually, for every field, order, eigenvalue `λ` and unit eigenvector `v`,
  `ν_k((∑_y v_y F_y)^{2p}) ≤ (2p)! (C λ)^p`;
* `CountBoundG` (H3 in the form that the proof reads): one `R̄` with `spRenyi ≤ R̄` eventually, for every
  field;
* `PhysVarG`, `PhysMeanG`: `ν_k(cRead²) ≤ (σ a_k⁴)²` and `|ν_k(F_k)| ≤ E a_k⁴` (the plaquette clause of
  `ApertureCountAt`'s H2, in the schedule's units).

`classMomentsG_of_count`: on a shift-invariant schedule and a non-negative class, the four give
`ClassMomentsG S W D t 2` at `t = 1 / (5⁴ · 2 · Z)`, `Z = max(√(C max(R̄, 0)) |σ|, |E|, 1)`. The steps:
`state_pow_le_renyi` on the centred screen (H1 at the columns of the eigenvector matrix,
`ApertureCount.evec_isUnitEig`), the count and the variance; the mean added back
(`add_pow_even_le`); one site to the unit cube (`state_cubeSumG_one_pow_le`); the unit cube to every cube
(`state_cubeSumG_pow_le`). `hU_of_count` is the clause of (E) at `schedAlongG _ βs` and
`SymPlaqClassG (SU N)`, for every flow `W`, in particular the observer `ConsolidatedRoot.obsW`.

`physMeanG_of_siteExpG`, `physVarG_of_siteExpG`: given `SiteExpG s C` with `s > 0`, the residual of the route `hU ⇐ SiteExpG`
(`TowerOpen.classMomentsG_of_siteExpG`) already gives `PhysMeanG` and `PhysVarG` on a non-negative class.
So against that route the count replaces one exponential moment at one site by H1 and H3; the
physical-units content of the mean and the variance is shared by both.

## 4. The comparison with the free flowed field (tested on paper)

`FreeBridge.FreeComparable` asks, mode by mode and two-sided, `e^{−δ} λ⁰ ≤ λ ≤ e^δ λ⁰` against a
relabelled box heat spectrum `λ⁰ = w e^{−u}`, `w ≤ w(k₀)`, `2t/L² ≥ τ`. On paper it is false in the free
limit, already at `U(1)` (argued, not proved here):

* Villain `U(1)` with the linear flow: the flowed plaquette angle `θ` is Gaussian with covariance `c`,
  and the compact reading `1 − cos θ` has the connected two-point function `e^{−c(0)} (cosh c(x) − 1)
  = e^{−c(0)} ∑_{n ≥ 1} c(x)^{2n} / (2n)!` (the Gaussian identity for `E[e^{iθ}]`). The `n`-th term is a
  `2n`-fold convolution in momentum, whose high-momentum decay is `e^{−t p² / n}` against `e^{−t p²}` for
  `n = 1`. Its coefficient is suppressed by `(a_k / √t)^{8(n−1)}`, a power of the box side, while at the
  top of the box spectrum (`p ~ π / a_k`) the ratio of the two Gaussians is `e^{t π² (1 − 1/n) / a_k²}`.
  So the interacting-free ratio of the sorted spectra is unbounded along the zoom at every fixed `δ` and
  `τ`, and the upper half of `SpecClause` fails. The same holds at `SU(N)`: the lattice reading
  `N − Re tr U_p` is not a polynomial in the flowed field (`FreeBridge` §1), and its higher terms carry
  the same slower tails.
* The count survives this: the modes where the comparison fails carry normalized weight
  `e^{−O(√t / a_k)}`, at most `L_k⁴` of them, so their share of `∑_α √p_α` tends to `0`. The level form of
  H3 survives with a larger exponent (`r = 4` in place of `2`; both values argued from the `n = 2` term's count).

So the comparison inequality does not close at the couplings of a tower; the missing input is the count
itself, stated one-sided, and H1.

## 5. The exact missing inequalities

At `S = schedAlongG _ βs`, `W` a flow of the observer and `D = SymPlaqClassG (SU N)`, for one `ρ > 0`:

* `CountBoundG S W D ρ`: `∃ R̄, ∀ᶠ k, ∀ O ∈ D, spRenyi (eig ν_k (cScreen S W ρ k O)) ≤ R̄`;
* `ModeHyperG S W D ρ`: `∃ C ≥ 0, ∀ᶠ k, ∀ O ∈ D, ∀ p λ v, IsUnitEig (gram ν_k screen) λ v →
  ν_k((∑_y v_y • screen_y)^{2p}) ≤ (2p)! (C λ)^p`;
* `PhysVarG`, `PhysMeanG` as above.

A sufficient form of `CountBoundG` on the two-point function alone (argued, on the periodic box; the
Dirichlet box needs a Szegő-type comparison): with `ĉ_k(p)` the connected spectral density of the flowed
reading in physical units, `R ≈ ρ⁴ (∫ √ĉ_k)² / ((2π)⁸ c_k(0))`, so `CountBoundG` follows from
`sup_k ∫_{|p| ≤ π/a_k} √ĉ_k(p) d⁴p < ∞` and `inf_k c_k(0) > 0`: a uniform decay of the flowed plaquette's
spectral density faster than `|p|^{−8}`.

## What does not follow

* None of `ModeHyperG`, `CountBoundG`, `PhysVarG`, `PhysMeanG` is proved at any tower or at any coupling
  of the interacting theory. `hU_of_count` moves `hU` onto them; it discharges nothing of (E) by itself.
* Where the Gram matrix is diagonal, `ModeHyperG` at a coordinate eigenvector is the per-site moment bound itself,
  and then H3 fails, the count growing like the box volume; the reduction carries content only where the screen's
  spectrum is concentrated. `ModeHyperG` quantifies over every unit vector of an eigenspace, more than the proof
  uses (the eigenvector columns).
* `ApertureCount.ApertureCountAt` does not imply the hypotheses here as stated: it reads `stateK` (the
  schedule at `dyBeta`), the `MIx` channels `mField (inr q)` and the flows `Wf s`, while `hU` reads
  `schedAlongG _ βs`, the symmetrized class `symG (plaqFieldG q)` and one `ConfFlowG`. The hypotheses
  here are its plaquette clauses (H1 at Wick index `1`, H3 at one aperture, H2's observer clause) moved to
  the tower's schedule and class.
* `FreeBridge.FreeComparable` is not used: §4 argues it fails in the free limit.
* The other clauses of (E) (`hK`, `hAF`, `hNG`, `hWard`, `hCO`, `ApproxAlong`) are untouched.
* The constant `2` and the rate `t` of the conclusion depend on `C`, `R̄`, `σ`, `E`; nothing here bounds
  them.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `8 = 2 · 4` in `8(n − 1)`, `(2π)⁸` and `|p|^{−8}`; `0` the signs, the lower ends and the empty box corner; `1` the unit cube `R = 1`,
the spacing bound `a_k ≤ 1`, the floor of `Z` and the factorial floor `(2p)! ≥ 1`; `2` the even powers,
the squares, the two summands of the mean split (`2^{2p}`) and the constant `2` of the conclusion (the two
summands); `2 · 1 + 3` and `4` the site-count bound `(2R + 3)⁴ / a⁴` of `sum_cubeInd_le` at `R = 1`;
`4` the spacetime dimension and the plaquette's canonical dimension in `a_k⁴`. `C`, `R̄`, `σ`, `E`, `ρ`
existential or given.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CountMoments

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ObserverEnergyBox MassGap.FlowUV MassGap.EnergyBoundG MassGap.ObserverOSG
  MassGap.ObserverLinkedG MassGap.ClayTreeG
open MassGap.ApertureModes (gram apSite)
open MassGap.ApertureCount (eig evec mode IsUnitEig spRenyi state_pow_le_renyi evec_isUnitEig)

/-! ## 1. Two scalar and state steps -/

/-- **The mean split for even powers**: `(x + y)^{2p} ≤ 2^{2p} (x^{2p} + y^{2p})`.
DERIVED: `2` the even power and the factor `|x + y| ≤ 2 max(|x|, |y|)`. -/
theorem add_pow_even_le (x y : ℝ) (p : ℕ) :
    (x + y) ^ (2 * p) ≤ 2 ^ (2 * p) * (x ^ (2 * p) + y ^ (2 * p)) := by
  have he := even_two_mul p
  rw [← he.pow_abs (x + y), ← he.pow_abs x, ← he.pow_abs y]
  have h1 : |x + y| ≤ 2 * max |x| |y| := by
    have := abs_add_le x y
    have hx := le_max_left |x| |y|
    have hy := le_max_right |x| |y|
    linarith
  have h2 : max |x| |y| ^ (2 * p) ≤ |x| ^ (2 * p) + |y| ^ (2 * p) := by
    rcases max_choice |x| |y| with h | h <;> rw [h]
    · linarith [pow_nonneg (abs_nonneg y) (2 * p)]
    · linarith [pow_nonneg (abs_nonneg x) (2 * p)]
  calc |x + y| ^ (2 * p) ≤ (2 * max |x| |y|) ^ (2 * p) := pow_le_pow_left₀ (abs_nonneg _) h1 _
    _ = 2 ^ (2 * p) * max |x| |y| ^ (2 * p) := mul_pow _ _ _
    _ ≤ 2 ^ (2 * p) * (|x| ^ (2 * p) + |y| ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- **The unit cube from one site, even moments**: in a translation-invariant state, for `0 < a ≤ 1`,
`ν((cubeSumG a 1 F)^{2p}) ≤ ((2·1 + 3)⁴ / a⁴)^{2p} ν(F^{2p})`. Jensen with the normalized cube weights,
then the site count `sum_cubeInd_le`. DERIVED: `1` the unit cube and the spacing bound; `2 · 1 + 3`, `4`
the site-count bound; `2` the even power; `0` the sign of `R`. -/
theorem state_cubeSumG_one_pow_le (ν : MassGap.DLRLimit.State (IConf G))
    (hT : ∀ (x : ISite) (F : C(IConf G, ℝ)), ν (transObs x F) = ν F) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (F : C(IConf G, ℝ)) (p : ℕ) :
    ν (cubeSumG a 1 F ^ (2 * p)) ≤ ((2 * 1 + 3) ^ 4 / a ^ 4) ^ (2 * p) * ν (F ^ (2 * p)) := by
  set M : ℝ := ∑ x ∈ box ⌈1 / a⌉₊, cubeInd 1 (site a x) with hMdef
  have hM1 : 1 ≤ M := one_le_sum_cubeInd zero_le_one
  have hM : 0 < M := by linarith
  have hML : M ≤ (2 * 1 + 3) ^ 4 / a ^ 4 := sum_cubeInd_le ha ha1 zero_le_one
  set H : C(IConf G, ℝ) := ∑ x ∈ box ⌈1 / a⌉₊,
    (cubeInd 1 (site a x) / M) • transObs x (F ^ (2 * p)) with hH
  have hpt : ∀ U, (cubeSumG a 1 F ^ (2 * p)) U ≤ (M ^ (2 * p) • H) U := by
    intro U
    have hHU : H U = ∑ x ∈ box ⌈1 / a⌉₊,
        (cubeInd 1 (site a x) / M) * F (transConf x U) ^ (2 * p) := by
      rw [hH]
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
        ContinuousMap.pow_apply, smul_eq_mul]
    rw [ContinuousMap.smul_apply, smul_eq_mul, hHU, ContinuousMap.pow_apply, cubeSumG_apply]
    have e1 : ∑ x ∈ box ⌈1 / a⌉₊, cubeInd 1 (site a x) * F (transConf x U)
        = M * ∑ x ∈ box ⌈1 / a⌉₊, (cubeInd 1 (site a x) / M) * F (transConf x U) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp
    rw [e1, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hM.le _)
    exact Real.pow_arith_mean_le_arith_mean_pow_of_even _ _ _
      (fun x _ => div_nonneg (cubeInd_nonneg _ _) hM.le)
      (by rw [← Finset.sum_div, ← hMdef, div_self hM.ne']) (even_two_mul p)
  have hνH : ν H = ν (F ^ (2 * p)) := by
    rw [hH, ν.map_sum]
    simp only [ν.map_smul, hT]
    rw [← Finset.sum_mul, ← Finset.sum_div, ← hMdef, div_self hM.ne', one_mul]
  have h0 : 0 ≤ ν (F ^ (2 * p)) := ν.nonneg _ fun U => by
    simp only [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _
  calc ν (cubeSumG a 1 F ^ (2 * p)) ≤ ν (M ^ (2 * p) • H) := ν.mono hpt
    _ = M ^ (2 * p) * ν (F ^ (2 * p)) := by rw [ν.map_smul, hνH]
    _ ≤ ((2 * 1 + 3) ^ 4 / a ^ 4) ^ (2 * p) * ν (F ^ (2 * p)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM.le hML _) h0

/-! ## 2. The screen on a schedule and the four clauses -/

/-- **The connected flowed reading** `F_k − ν_k(F_k)`, `F_k = O ∘ V_k`. DERIVED: `1` the constant. -/
def cRead (S : Sched G) (W : ConfFlowG G) (k : ℕ) (O : LField G) : C(IConf G, ℝ) :=
  (W.fieldMap k O).1 - S.ν k (W.fieldMap k O).1 • (1 : C(IConf G, ℝ))

/-- **The screen's side in lattice steps** at physical side `ρ`: `⌈ρ / a_k⌉`. DERIVED: no numeral. -/
def scrSide (S : Sched G) (ρ : ℝ) (k : ℕ) : ℕ := ⌈ρ / S.a k⌉₊

/-- **The screen**: the connected flowed reading at every site of the box `{0, …, L_k − 1}⁴`.
DERIVED: `4` the spacetime dimension. -/
def cScreen (S : Sched G) (W : ConfFlowG G) (ρ : ℝ) (k : ℕ) (O : LField G) :
    (Fin 4 → Fin (scrSide S ρ k)) → C(IConf G, ℝ) :=
  fun y => transObs (apSite y) (cRead S W k O)

/-- **H1 on the screen, at Wick index `1`, basis-free**: one `C ≥ 0` with, eventually in the step, for every
field of `D`, order `2p`, eigenvalue `λ` of the screen's Gram matrix and unit eigenvector `v`,
`ν_k((∑_y v_y • F_y)^{2p}) ≤ (2p)! (C λ)^p`. DERIVED: `2` the even power; `4` the dimension; `0` the sign. -/
def ModeHyperG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ O ∈ D, ∀ (p : ℕ) (lam : ℝ) (v : (Fin 4 → Fin (scrSide S ρ k)) → ℝ),
    IsUnitEig (gram (S.ν k) (cScreen S W ρ k O)) lam v →
    S.ν k ((∑ y, v y • cScreen S W ρ k O y) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (C * lam) ^ p

/-- **The count bounded along the zoom**: one `R̄` with `spRenyi ≤ R̄` for the screen of every field of `D`,
eventually in the step. DERIVED: no numeral. -/
def CountBoundG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (ρ : ℝ) : Prop :=
  ∃ Rb : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, spRenyi (eig (S.ν k) (cScreen S W ρ k O)) ≤ Rb

/-- **The variance in physical units**: `ν_k(cRead²) ≤ (σ a_k⁴)²`, eventually, over `D`.
DERIVED: `2` the square; `4` the canonical dimension. -/
def PhysVarG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) : Prop :=
  ∃ σ : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, S.ν k (cRead S W k O ^ 2) ≤ (σ * S.a k ^ 4) ^ 2

/-- **The mean in physical units**: `|ν_k(F_k)| ≤ E a_k⁴`, eventually, over `D`.
DERIVED: `4` the canonical dimension. -/
def PhysMeanG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) : Prop :=
  ∃ E : ℝ, ∀ᶠ k in atTop, ∀ O ∈ D, |S.ν k (W.fieldMap k O).1| ≤ E * S.a k ^ 4

/-! ## 3. The bridge -/

/-- **The class moments from the count**: on a shift-invariant schedule, a non-negative class and a
physical side `ρ > 0`, H1, the count, the variance and the mean give `ClassMomentsG S W D t 2` with
`t = 1 / ((2·1 + 3)⁴ · 2 · Z)`. DERIVED: `2` the constant (two summands of the mean split) and the even
powers; `2 · 1 + 3`, `4` the site count at the unit cube; `1` the floor of `Z` and the spacing bound;
`0` the signs. -/
theorem classMomentsG_of_count (S : Sched G) (hsh : SchedShiftInv S) (W : ConfFlowG G)
    {D : Set (LField G)} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {ρ : ℝ} (hρ : 0 < ρ)
    (h1 : ModeHyperG S W D ρ) (h3 : CountBoundG S W D ρ) (hv : PhysVarG S W D)
    (hm : PhysMeanG S W D) :
    ∃ t C₀ : ℝ, 0 < t ∧ 0 ≤ C₀ ∧ ClassMomentsG S W D t C₀ := by
  obtain ⟨C, hC, h1⟩ := h1
  obtain ⟨Rb, h3⟩ := h3
  obtain ⟨σ, hv⟩ := hv
  obtain ⟨E, hm⟩ := hm
  set Y : ℝ := Real.sqrt (C * max Rb 0) * |σ| with hYdef
  set Z : ℝ := max (max Y |E|) 1 with hZdef
  have hZ1 : 1 ≤ Z := le_max_right _ _
  have hZ0 : 0 < Z := by linarith
  have hY0 : 0 ≤ Y := by positivity
  have hYZ : Y ≤ Z := (le_max_left Y |E|).trans (le_max_left _ _)
  have hEZ : |E| ≤ Z := (le_max_right Y |E|).trans (le_max_left _ _)
  have hY2 : Y ^ 2 = C * max Rb 0 * σ ^ 2 := by
    rw [hYdef, mul_pow, Real.sq_sqrt (mul_nonneg hC (le_max_right _ _)), sq_abs]
  refine ⟨1 / ((2 * 1 + 3) ^ 4 * 2 * Z), 2, by positivity, by norm_num, ?_⟩
  intro O hO
  filter_upwards [h1, h3, hv, hm, S.a_lim.eventually (gt_mem_nhds one_pos)]
    with k hk1 hk3 hkv hkm hka
  intro R hR p
  have ha := S.a_pos k
  have hT := state_transObs (hsh k)
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have ha4 : 0 ≤ S.a k ^ 4 := by positivity
  haveI : Nonempty (Fin (scrSide S ρ k)) := ⟨⟨0, Nat.ceil_pos.2 (div_pos hρ ha)⟩⟩
  have hfac1 : (1 : ℝ) ≤ ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  -- the centred site, through the count
  have hA := state_pow_le_renyi (S.ν k) (cScreen S W ρ k O) (G₀ := cRead S W k O) (p := p)
    (K := ((2 * p).factorial : ℝ) * C ^ p) (by positivity)
    (fun y q => by simp only [cScreen]; rw [← transObs_powG, hT])
    (fun α => (hk1 O hO p _ _ (evec_isUnitEig _ _ α)).trans_eq (by rw [mul_pow, mul_assoc]))
  have hR0 : 0 ≤ spRenyi (eig (S.ν k) (cScreen S W ρ k O)) := by unfold spRenyi; positivity
  have hm20 : 0 ≤ S.ν k (cRead S W k O ^ 2) :=
    (S.ν k).nonneg _ fun U => by simp only [ContinuousMap.pow_apply]; positivity
  have hcent : S.ν k (cRead S W k O ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) * (Z * S.a k ^ 4) ^ (2 * p) := by
    have hRm : C * (spRenyi (eig (S.ν k) (cScreen S W ρ k O)) * S.ν k (cRead S W k O ^ 2))
        ≤ (Y * S.a k ^ 4) ^ 2 := by
      rw [mul_pow, hY2]
      have := mul_le_mul (hk3 O hO |>.trans (le_max_left Rb 0)) (hkv O hO) hm20
        (le_max_right Rb 0)
      calc C * (spRenyi (eig (S.ν k) (cScreen S W ρ k O)) * S.ν k (cRead S W k O ^ 2))
          ≤ C * (max Rb 0 * (σ * S.a k ^ 4) ^ 2) := mul_le_mul_of_nonneg_left this hC
        _ = C * max Rb 0 * σ ^ 2 * (S.a k ^ 4) ^ 2 := by ring
    have hYa : (Y * S.a k ^ 4) ^ 2 ≤ (Z * S.a k ^ 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hYZ ha4) _
    calc S.ν k (cRead S W k O ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) * C ^ p
            * (spRenyi (eig (S.ν k) (cScreen S W ρ k O)) * S.ν k (cRead S W k O ^ 2)) ^ p := hA
      _ = ((2 * p).factorial : ℝ)
            * (C * (spRenyi (eig (S.ν k) (cScreen S W ρ k O)) * S.ν k (cRead S W k O ^ 2))) ^ p := by
          ring
      _ ≤ ((2 * p).factorial : ℝ) * ((Z * S.a k ^ 4) ^ 2) ^ p :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg hC (mul_nonneg hR0 hm20)) (hRm.trans hYa) _) (by positivity)
      _ = ((2 * p).factorial : ℝ) * (Z * S.a k ^ 4) ^ (2 * p) := by rw [← pow_mul]
  -- the mean added back
  have hFU : ∀ U, (W.fieldMap k O).1 U = cRead S W k O U + S.ν k (W.fieldMap k O).1 := fun U => by
    simp [cRead]
  have hraw : S.ν k ((W.fieldMap k O).1 ^ (2 * p))
      ≤ 2 ^ (2 * p) * (S.ν k (cRead S W k O ^ (2 * p)) + S.ν k (W.fieldMap k O).1 ^ (2 * p)) := by
    have hpt : ∀ U, ((W.fieldMap k O).1 ^ (2 * p)) U
        ≤ ((2 : ℝ) ^ (2 * p) • (cRead S W k O ^ (2 * p)
            + S.ν k (W.fieldMap k O).1 ^ (2 * p) • (1 : C(IConf G, ℝ)))) U := by
      intro U
      simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
      rw [hFU U]
      exact add_pow_even_le _ _ p
    calc _ ≤ _ := (S.ν k).mono hpt
      _ = _ := by rw [(S.ν k).map_smul, (S.ν k).map_add, (S.ν k).map_smul, (S.ν k).map_one, mul_one]
  have hmean : S.ν k (W.fieldMap k O).1 ^ (2 * p) ≤ (Z * S.a k ^ 4) ^ (2 * p) := by
    rw [← (even_two_mul p).pow_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
    calc |S.ν k (W.fieldMap k O).1| ≤ E * S.a k ^ 4 := hkm O hO
      _ ≤ |E| * S.a k ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self E) ha4
      _ ≤ Z * S.a k ^ 4 := mul_le_mul_of_nonneg_right hEZ ha4
  have hsite : S.ν k ((W.fieldMap k O).1 ^ (2 * p))
      ≤ 2 * ((2 * p).factorial : ℝ) * (2 * Z * S.a k ^ 4) ^ (2 * p) := by
    have hZa : 0 ≤ (Z * S.a k ^ 4) ^ (2 * p) := by positivity
    calc S.ν k ((W.fieldMap k O).1 ^ (2 * p))
        ≤ 2 ^ (2 * p) * (((2 * p).factorial : ℝ) * (Z * S.a k ^ 4) ^ (2 * p)
            + ((2 * p).factorial : ℝ) * (Z * S.a k ^ 4) ^ (2 * p)) := by
          refine hraw.trans (mul_le_mul_of_nonneg_left (add_le_add hcent ?_) (by positivity))
          exact hmean.trans (le_mul_of_one_le_left hZa hfac1)
      _ = 2 * ((2 * p).factorial : ℝ) * (2 * Z * S.a k ^ 4) ^ (2 * p) := by ring
  -- one site to the unit cube, the unit cube to every cube
  have hunit := state_cubeSumG_one_pow_le (S.ν k) hT ha hka.le (W.fieldMap k O).1 p
  have hcube : S.ν k (cubeSumG (S.a k) 1 (W.fieldMap k O).1 ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) / (1 / ((2 * 1 + 3) ^ 4 * 2 * Z)) ^ (2 * p) * 2 := by
    refine hunit.trans ?_
    have hq : 0 ≤ ((2 * 1 + 3) ^ 4 / S.a k ^ 4 : ℝ) ^ (2 * p) := by positivity
    calc ((2 * 1 + 3) ^ 4 / S.a k ^ 4 : ℝ) ^ (2 * p) * S.ν k ((W.fieldMap k O).1 ^ (2 * p))
        ≤ ((2 * 1 + 3) ^ 4 / S.a k ^ 4 : ℝ) ^ (2 * p)
            * (2 * ((2 * p).factorial : ℝ) * (2 * Z * S.a k ^ 4) ^ (2 * p)) :=
          mul_le_mul_of_nonneg_left hsite hq
      _ = 2 * ((2 * p).factorial : ℝ)
            * ((2 * 1 + 3) ^ 4 / S.a k ^ 4 * (2 * Z * S.a k ^ 4)) ^ (2 * p) := by
          rw [mul_pow ((2 * 1 + 3) ^ 4 / S.a k ^ 4 : ℝ)]; ring
      _ = 2 * ((2 * p).factorial : ℝ) * ((2 * 1 + 3) ^ 4 * 2 * Z) ^ (2 * p) := by
          have ha0 : S.a k ^ 4 ≠ 0 := by positivity
          have e : (2 * 1 + 3) ^ 4 / S.a k ^ 4 * (2 * Z * S.a k ^ 4) = (2 * 1 + 3) ^ 4 * 2 * Z := by
            rw [div_mul_eq_mul_div, div_eq_iff ha0]; ring
          rw [e]
      _ = ((2 * p).factorial : ℝ) / (1 / ((2 * 1 + 3) ^ 4 * 2 * Z)) ^ (2 * p) * 2 := by
          rw [one_div, inv_pow, div_inv_eq_mul]; ring
  refine (state_cubeSumG_pow_le (S.ν k) hT ha hR _ hF p).trans ?_
  exact mul_le_mul_of_nonneg_left hcube (pow_nonneg (pow_nonneg (by linarith) 4) _)

#print axioms add_pow_even_le
#print axioms state_cubeSumG_one_pow_le
#print axioms classMomentsG_of_count

/-! ## 4. The residual of the exponential-moment route gives the mean and the variance -/

/-- **`SiteExpG` gives the mean in physical units** on a non-negative class: `ν_k(F_k) ≤ (|C| / s) a_k⁴`.
`ObserverEnergyBox.state_pow_le_exp` at order `1`. DERIVED: `1` the order; `4` the canonical dimension;
`0` the signs. -/
theorem physMeanG_of_siteExpG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {s C : ℝ} (hs : 0 < s)
    (h : MassGap.TowerOpen.SiteExpG S W D s C) : PhysMeanG S W D := by
  refine ⟨|C| / s, ?_⟩
  filter_upwards [h] with k hk O hO
  have ha := S.a_pos k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hst : 0 < s / S.a k ^ 4 := by positivity
  have hb := state_pow_le_exp (S.ν k) _ hF hst 1
  rw [pow_one, pow_one, Nat.factorial_one, Nat.cast_one] at hb
  have h0 : 0 ≤ S.ν k (W.fieldMap k O).1 := (S.ν k).nonneg _ hF
  rw [abs_of_nonneg h0]
  calc S.ν k (W.fieldMap k O).1 ≤ 1 / (s / S.a k ^ 4) * C :=
        hb.trans (mul_le_mul_of_nonneg_left (hk O hO) (by positivity))
    _ ≤ 1 / (s / S.a k ^ 4) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (by positivity)
    _ = |C| / s * S.a k ^ 4 := by field_simp

/-- **`SiteExpG` gives the variance in physical units** on a non-negative class:
`ν_k(cRead²) ≤ ν_k(F_k²) ≤ 2 |C| a_k⁸ / s² = (√(2|C|) / s · a_k⁴)²`. `state_pow_le_exp` at order `2`.
DERIVED: `2` the order and the factorial `2! = 2`; `4` the canonical dimension; `0` the signs. -/
theorem physVarG_of_siteExpG (S : Sched G) (W : ConfFlowG G) {D : Set (LField G)}
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {s C : ℝ} (hs : 0 < s)
    (h : MassGap.TowerOpen.SiteExpG S W D s C) : PhysVarG S W D := by
  refine ⟨Real.sqrt (2 * |C|) / s, ?_⟩
  filter_upwards [h] with k hk O hO
  have ha := S.a_pos k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hpos O hO (W.V k U)
  have hst : 0 < s / S.a k ^ 4 := by positivity
  have hb := state_pow_le_exp (S.ν k) _ hF hst 2
  have hsq : cRead S W k O ^ 2 = (W.fieldMap k O).1 ^ 2 + (-(2 * S.ν k (W.fieldMap k O).1)) •
      (W.fieldMap k O).1 + (S.ν k (W.fieldMap k O).1 ^ 2) • (1 : C(IConf G, ℝ)) := by
    ext U
    simp only [cRead, ContinuousMap.pow_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  have hvar : S.ν k (cRead S W k O ^ 2) ≤ S.ν k ((W.fieldMap k O).1 ^ 2) := by
    rw [hsq, (S.ν k).map_add, (S.ν k).map_add, (S.ν k).map_smul, (S.ν k).map_smul, (S.ν k).map_one]
    nlinarith [sq_nonneg (S.ν k (W.fieldMap k O).1)]
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfac] at hb
  have hC := (hk O hO).trans (le_abs_self C)
  calc S.ν k (cRead S W k O ^ 2) ≤ S.ν k ((W.fieldMap k O).1 ^ 2) := hvar
    _ ≤ 2 / (s / S.a k ^ 4) ^ 2 * |C| :=
        hb.trans (mul_le_mul_of_nonneg_left hC (by positivity))
    _ = (Real.sqrt (2 * |C|) / s * S.a k ^ 4) ^ 2 := by
        rw [show (Real.sqrt (2 * |C|) / s * S.a k ^ 4) ^ 2
            = Real.sqrt (2 * |C|) ^ 2 * (S.a k ^ 4) ^ 2 / s ^ 2 by ring,
          Real.sq_sqrt (by positivity)]
        field_simp

#print axioms physMeanG_of_siteExpG
#print axioms physVarG_of_siteExpG

/-! ## 5. The clause of (E) -/

open MassGap.MeasuredTower (schedAlongG)
open MassGap.MeasuredSpacing (schedShiftInv_alongG)

/-- **The class-moment clause `hU` of (E) from the count**, at the tower's schedule `schedAlongG _ βs`
and the symmetrized plaquette class of `SU(N)`, for every flow `W` (in particular the observer
`ConsolidatedRoot.obsW`) for a given physical side `ρ > 0`, on which H1 and H3 depend. DERIVED: `0` the signs. -/
theorem hU_of_count {N : ℕ} [NeZero N] [Fact (2 ≤ N)] (βs : ℕ → ℝ) (W : ConfFlowG (MassGap.SUN.SU N)) {ρ : ℝ}
    (hρ : 0 < ρ)
    (h1 : ModeHyperG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) ρ)
    (h3 : CountBoundG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) ρ)
    (hv : PhysVarG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)))
    (hm : PhysMeanG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N))) :
    ∃ t C₀ : ℝ, 0 < t ∧ 0 ≤ C₀ ∧
      ClassMomentsG (schedAlongG _ βs) W (MassGap.SymPlaqG.SymPlaqClassG (MassGap.SUN.SU N)) t C₀ :=
  classMomentsG_of_count _ (schedShiftInv_alongG _ βs) W MassGap.SymPlaqG.symPlaqG_nonneg hρ h1 h3 hv hm

#print axioms hU_of_count

end MassGap.CountMoments

end
