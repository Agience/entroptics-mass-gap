import Mathlib
import MassGap.RegularFull
import MassGap.ReadPos

/-!
# MassGap.RegNontrivial — what a witness of `RegConnectedNonzero` must be, and why a bare field is none

`RegularDense.RegConnectedNonzero` asks for one regular monomial `Q` whose connected reflected reading
`S(θQ ∪ Q) − S(Q)²` is not zero. This module states the exact lattice inequality that is equivalent to it,
and proves that the bare fields and the coupling-zero bounds cannot supply that inequality. Declarations
are in the namespace `MassGap.RegNontrivial`.

## The inequality (proved)

`connAt ν a τ P = ν(θX · X) − ν(X)²` with `X = prodSmear a P`, and `connAt_eq_cov` shows it is the
covariance `stateCov ν (θX) X` for a reflection-invariant `ν`. `regConnected_iff_floor`, under
`UniformBoundF`: `RegConnectedNonzero` holds exactly when some regular `Q` has, for some `c > 0`,

    c ≤ |stateCov ν_k (θ X_k) X_k|        eventually along `ultra`,        X_k the flowed monomial of step `k`.

It is the converse of `RegularFull.regConnected_of_lattice`, and it weakens `atTop` to `ultra`. The two
factors of the covariance stand at physical distance at least `2 (d − r)` up to `o(1)`, `d` the margin of `Q` and
`r` the flow's range (informal; not proved here), so at a lattice distance of that length over `a_k`. It is a correlation over a distance that diverges in lattice units. It is
not a variance.

## A bare field dominated by the class reads zero (proved)

`energy0` does not scale a field outside `D`, so such a field keeps the cell weight `a⁴`. If
`|O| ≤ c P` with `P ∈ D` and `O ∉ D` (`BareDom`), then `|smear a (O ∘ V) f| ≤ a⁴ c M · cubeSum a R (P ∘ V)`
pointwise (`abs_smear_dom_le`), and `cubeSum` of `P ∘ V` has bounded moments by `hcube`. So the smeared bare
field has moments of order `a⁴`, and every Schwinger function with such a factor is `0`
(`contSF_eq_zero_of_dom`), whatever the other factors. `kernF_eq_zero_of_dom` and
`conn_eq_zero_of_dom` are its readings: a monomial with a bare dominated factor has connected reading
exactly `0`. `exists_witness_free_of_dom`: any witness of `RegConnectedNonzero` has no such factor.

`bareDom_plaqField`: the plaquette density itself is dominated by its symmetrisation, so at
`SymPlaqClass N` the bare plaquette, if outside the class, is such a field. The proof uses no clustering and
no property of the couplings: the domination uses only non-negativity of the Wilson density, and the zero reading
(`conn_eq_zero_of_dom`) then needs `hpos` and `hcube` at `D = SymPlaqClass N`, which are hypotheses here. Taking a bare field to
avoid the factor `a_k⁻⁴` removes the scale that makes the reading finite and non-zero.

## Coupling zero (proved)

`wspec_zero_const`: at `β = 0` the DLR kernel of a field local on `S` does not read the boundary condition.
`haar_factorise`: `ν₀(F Y) = ν₀(F) ν₀(Y)` at disjoint supports. `haar_refl_mul`: the reflected read of
`X ∈ halfSpaceAlg τ 1` factorises. `haar_conn_zero`: for any flow of physical range `r`, any margin monomial,
scaled by anything, `connAt` at `β = 0` is exactly `0` at every large step. `floor_not_from_haar`: at the same
`β = 0` the Haar variance of `Re tr` is strictly positive. So a variance floor at `β = 0` does not
bound the reading below, and neither does continuity from `β = 0`, since `0` is what it continues.

## What does not follow

Plainly:

* `RegConnectedNonzero` is not discharged, at any class. What is left is `regConnected_iff_floor` at a
  monomial without bare dominated factors. At the fields of `D`, where `X_k` carries `a_k⁻⁴` per factor, it is
  a floor on `a_k⁻⁸` times a covariance of `O ∘ V_k` at lattice distance about `2 (d − r) / a_k` (informal): the continuum two-point
  function at separation `2 d`, bounded below.
* Non-triviality at a fixed `β` does not hold in general in this reading: `haar_conn_zero` refutes it for the
  reading at `β = 0`. At `β > 0`, and along a bounded coupling sequence, nothing in the tree bounds the covariance at
  distance about `2 (d − r) / a_k` below, and at small `β` the strong-coupling clustering is expected to send it to `0`. The
  positive reads of the tree do not reach it. `ReadPos.gE_zero_pos` is the contact read, at lattice distance
  `0`. `ReadPos.kernel_floor` is `e^{−2β|∂S|}` times a Haar integral on one link set: it is a conditional bound on
  a set of links next to its boundary, it reads no pair at distance about `2 (d − r) / a_k`, and it vanishes as `β_k → ∞`.
  Neither is an estimate at the margin, at any coupling.
* A field outside `D` not dominated by `D` is not treated: for example `1 − P`, a constant plus a dominated
  field, whose reading is expected to be the constant. A monomial of such fields is not excluded as a
  witness by this module, and no such witness is built.
* `D`-field readings: no lower bound is proved. `RegularFull.not_regConnected_of_zero` still applies, so the
  bound needs more than `hD`, `hpos` and `hcube`; `ContinuumNontrivial.connectedTwoPointNonzero_of_af` and the
  link inputs of `PreObserver` remain the routes that state what is needed.

DERIVED (module-wide): `0` the plane, the coupling zero, the zero reading and the signs; `1` the first
sheet above the plane, the shift of a bound away from `0`, the unit observable and the unit of the group; `2`
the square of the one-point reading, the two copies of the reflected read and the even power; `4` in
`Fin 4` the spacetime dimension and the exponent of the cell volume.

Foundational footprint only (`#print axioms` at the end).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.RegNontrivial

open Filter Topology MeasureTheory
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
  MassGap.ObserverEnergyMoments MassGap.ObserverSymField
open MassGap.ShellTranslate
open MassGap.RegularDense (RegConnectedNonzero)
open MassGap.RegularFull (allMom_energy0 SmearMom)
open MassGap.FocusZoom (stateCov)

variable {N : ℕ}

/-! ## 1. The connected reading as a covariance, and the exact floor -/

section Floor

/-- The empty monomial. DERIVED: `0` the number of factors. -/
def eMono (N : ℕ) : Mono N := ⟨0, Fin.elim0⟩

/-- **The connected reflected reading of `P` in the state `ν` at spacing `a`.** DERIVED: `2` the square of
the one-point reading. -/
def connAt (ν : MassGap.DLRLimit.State (Cfg N)) (a : ℝ) (τ : Fin 4) (P : Mono N) : ℝ :=
  latS ν a (pairFam τ P P) - latS ν a (pairFam τ (eMono N) P) ^ 2

/-- **A reflection-invariant state reads `connAt` as the covariance of `θX` and `X`.** DERIVED: `0` the
plane and the sign of `a`; `2` the square. -/
theorem connAt_eq_cov (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a) (τ : Fin 4)
    (hθ : ∀ f, ν (LatticeReflection.ireflObs τ 0 f) = ν f) (P : Mono N) :
    connAt ν a τ P = stateCov ν (LatticeReflection.ireflObs τ 0 (prodSmear a P)) (prodSmear a P) := by
  have h1 : LatticeReflection.ireflObs τ 0 (prodSmear a (eMono N)) = 1 :=
    ContinuousMap.ext fun U => by
      simp [prodSmear, eMono]
  unfold connAt stateCov
  rw [latS_pairFam ν ha, latS_pairFam ν ha, h1, one_mul, hθ, sq]

/-- `connAt` at step `k` of a flow, in terms of `latSF`. DERIVED: `2` the square. -/
theorem latSF_conn (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r : ℝ) (k : ℕ) (P : Mono N) :
    latSF hN Φ k (pairFam τ P P) - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 P) ^ 2
      = connAt (stateK hN k) (dySpacing N k) τ (Φ.mono k P) := by
  have e : Φ.mono k (emptyMargin N τ r).1 = eMono N :=
    congrArg (Sigma.mk 0) (funext fun i => i.elim0)
  rw [latSF_pairFam, latSF_pairFam, e]
  rfl

/-- **`RegConnectedNonzero` is exactly a floor on one covariance along `ultra`.** The converse half is
`RegularFull.regConnected_of_lattice`, with `ultra` in place of `atTop`. DERIVED: `0` the excluded value and
the sign of `c`; `2` the half of the limit and the square. -/
theorem regConnected_iff_floor (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (A : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) :
    RegConnectedNonzero hN Φ A τ r ↔ ∃ Q : RMono N A τ r, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in (ultra : Filter ℕ), c ≤ |stateCov (stateK hN k)
        (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (Φ.mono k Q.1.1)))
        (prodSmear (dySpacing N k) (Φ.mono k Q.1.1))| := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hcov : ∀ (k : ℕ) (P : Mono N), stateCov (stateK hN k)
      (LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing N k) (Φ.mono k P)))
      (prodSmear (dySpacing N k) (Φ.mono k P))
      = latSF hN Φ k (pairFam τ P P) - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 P) ^ 2 := by
    intro k P
    rw [latSF_conn hN Φ τ r k P]
    exact (connAt_eq_cov _ (dySpacing_pos (one_le_of_ne_zero hN) k) τ
      (MassGap.PeriodicState.periodicState_reflInvariant hN _ τ 0) _).symm
  have hlim : ∀ Q : RMono N A τ r, Tendsto
      (fun k => latSF hN Φ k (pairFam τ Q.1.1 Q.1.1)
        - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 Q.1.1) ^ 2) (ultra : Filter ℕ)
      (𝓝 (kernF hN Φ τ Q.1.1 Q.1.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 ^ 2)) := fun Q =>
    (tendsto_contSF hN Φ hB (pairFam τ Q.1.1 Q.1.1)).sub
      ((tendsto_contSF hN Φ hB (pairFam τ (emptyMargin N τ r).1 Q.1.1)).pow 2)
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, _, half_pos (abs_pos.mpr hQ), ?_⟩
    filter_upwards [(hlim Q).abs.eventually (lt_mem_nhds (half_lt_self (abs_pos.mpr hQ)))] with k hk
    rw [hcov]
    exact hk.le
  · rintro ⟨Q, c, hc, h⟩
    refine ⟨Q, fun h0 => ?_⟩
    have hle := ge_of_tendsto (hlim Q).abs (h.mono fun k hk => by rwa [hcov] at hk)
    rw [h0, abs_zero] at hle
    linarith

end Floor

/-! ## 2. Bare fields dominated by the class -/

section Dominated

/-- **A bare field dominated by the class**: outside `D`, so `energy0` does not scale it, and bounded by a
multiple of a field of `D`. DERIVED: `0` the sign of `c`. -/
def BareDom (D : Set (LField (MassGap.SUN.SU N))) (O : LField (MassGap.SUN.SU N)) : Prop :=
  O ∉ D ∧ ∃ P ∈ D, ∃ c : ℝ, 0 ≤ c ∧ ∀ U, |O.1 U| ≤ c * P.1 U

/-- **The smear of a dominated field carries the cell weight**. DERIVED: `0` the signs; `4` the cell
volume. -/
theorem abs_smear_dom_le {a : ℝ} (ha : 0 < a) (F P : C(Cfg N, ℝ)) {c : ℝ}
    (hFP : ∀ U, |F U| ≤ c * P U) (g : TestFn) {R M : ℝ} (hg : IsTest g.1 R M) (U : Cfg N) :
    |smear a F g U| ≤ a ^ 4 * c * M * cubeSum a R P U := by
  rw [smear_eq_sum ha F g hg (subset_refl _), cubeSum_apply]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, transObs_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have ha4 : 0 < a ^ 4 := pow_pos ha 4
  rw [abs_mul, abs_mul, abs_of_pos ha4]
  have h1 := abs_le_mul_cubeInd hg (site a x)
  have h2 := hFP (transConf x U)
  have h3 : 0 ≤ a ^ 4 * (M * cubeInd R (site a x)) := by
    exact mul_nonneg ha4.le (mul_nonneg hg.M_nonneg (cubeInd_nonneg _ _))
  calc a ^ 4 * |g.1 (site a x)| * |F (transConf x U)|
      ≤ a ^ 4 * (M * cubeInd R (site a x)) * (c * P (transConf x U)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 ha4.le) h2 (abs_nonneg _) h3
    _ = a ^ 4 * c * M * (cubeInd R (site a x) * P (transConf x U)) := by ring

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

include hpos hcube in
/-- **A Schwinger function with a bare dominated factor is `0`.** That factor has `2n`-th moment of order
`a⁸ⁿ` (`abs_smear_dom_le`, `hcube`), every other factor has its moment (`allMom_energy0`), so
`abs_state_prod_le` gives `|S_k| ≤ B a_k⁴ → 0`. DERIVED: `0` the limit and the signs; `1` the shift of the
bounds away from `0` and the unit factor; `2` the even power; `4` the cell volume. -/
theorem contSF_eq_zero_of_dom {ι : Type} [Fintype ι] (F : ι → SField N) (i0 : ι)
    (hO : BareDom D (F i0).1) : contSF hN (energy0 W D hD) F = 0 := by
  classical
  obtain ⟨hOD, P, hP, c, hc, hdom⟩ := hO
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Finset.sum_nonneg fun i _ => (hRM i).1
  have hRi : ∀ i, R0 i ≤ R := fun i => by
    rw [hRdef]
    exact Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
  have hM1 : ∀ i, 0 < M i + 1 := fun i => by linarith [(hRM i).M_nonneg]
  have hF : ∀ i, IsTest (F i).2.1 R (M i + 1) := fun i =>
    ⟨hR0, fun y => ((hRM i).2.1 y).trans (by linarith),
      fun y hy j => ((hRM i).2.2 y hy j).trans (hRi i)⟩
  have hMom := allMom_energy0 hN W hD hpos hcube
  have hex2 := fun i => hMom (F i).1 R hR0 (Fintype.card ι)
  choose cc hcc0 hcc using hex2
  obtain ⟨C, hC⟩ := hcube P hP R hR0 (Fintype.card ι)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ i, cc i + |C| := ⟨_, rfl⟩
  have hccB : ∀ i, cc i ≤ B := fun i => by
    rw [hBdef]
    have := Finset.single_le_sum (f := cc) (fun i _ => hcc0 i) (Finset.mem_univ i)
    linarith [abs_nonneg C]
  have hCB : |C| ≤ B := by
    rw [hBdef]
    have : 0 ≤ ∑ i, cc i := Finset.sum_nonneg fun i _ => hcc0 i
    linarith
  obtain ⟨L', hL'⟩ : ∃ L' : ι → ℝ, L' = fun i => if i = i0 then (c + 1) * (M i + 1) else M i + 1 :=
    ⟨_, rfl⟩
  have hL'pos : ∀ i, 0 < L' i := fun i => by
    rw [hL']
    show 0 < if i = i0 then (c + 1) * (M i + 1) else M i + 1
    split_ifs
    · exact mul_pos (by linarith) (hM1 i)
    · exact hM1 i
  have hev : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k F|
      ≤ (1 + Fintype.card ι * B) * (dySpacing N k ^ 4 * ∏ i, L' i) := by
    filter_upwards [Filter.eventually_all.mpr hcc, hC] with k hk hCk
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have ha4 : 0 < dySpacing N k ^ 4 := pow_pos ha 4
    let L : ι → ℝ := fun i => (if i = i0 then dySpacing N k ^ 4 else 1) * L' i
    have hLpos : ∀ i, 0 < L i := fun i => mul_pos (by split_ifs <;> positivity) (hL'pos i)
    have hprod : ∏ i, L i = dySpacing N k ^ 4 * ∏ i, L' i := by
      show ∏ i, ((if i = i0 then dySpacing N k ^ 4 else 1) * L' i) = _
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i0]
      simp
    show |latSk hN k (fun i => (energy0 W D hD).field k (F i))| ≤ _
    rw [latSk_eq, ← hprod]
    show |stateK hN k (∏ i, smear (dySpacing N k) ((energy0 W D hD).map k (F i).1).1 (F i).2)| ≤ _
    refine abs_state_prod_le (stateK hN k) _ L hLpos (fun i => ?_)
    by_cases hi : i = i0
    · subst hi
      have hmap : ((energy0 W D hD).map k (F i).1).1 = (W.fieldMap k (F i).1).1 := by
        show zOn D k (F i).1 • ((W.fieldMap k (F i).1).1 - sOn D (s0 N) k (F i).1 • (1 : C(Cfg N, ℝ))) = _
        rw [zOn_of_not_mem hOD, sOn_of_not_mem hOD, zero_smul, sub_zero, one_smul]
      rw [hmap]
      have hP0 : ∀ U, 0 ≤ (W.fieldMap k P).1 U := fun U => hpos P hP (W.V k U)
      have hdk : ∀ U, |(W.fieldMap k (F i).1).1 U| ≤ (c + 1) * (W.fieldMap k P).1 U := fun U =>
        (hdom (W.V k U)).trans (mul_le_mul_of_nonneg_right (by linarith) (hP0 U))
      have hLi : L i = dySpacing N k ^ 4 * (c + 1) * (M i + 1) := by
        show (if i = i then dySpacing N k ^ 4 else 1) * L' i = _
        rw [if_pos rfl, hL']
        show dySpacing N k ^ 4 * (if i = i then (c + 1) * (M i + 1) else M i + 1) = _
        rw [if_pos rfl]
        ring
      have hq : Even (2 * Fintype.card ι) := even_two_mul _
      calc stateK hN k (smear (dySpacing N k) (W.fieldMap k (F i).1).1 (F i).2
            ^ (2 * Fintype.card ι))
          ≤ stateK hN k (L i ^ (2 * Fintype.card ι) •
              cubeSum (dySpacing N k) R (W.fieldMap k P).1 ^ (2 * Fintype.card ι)) :=
            (stateK hN k).mono fun U => by
              simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
              rw [← hq.pow_abs, ← mul_pow, hLi]
              exact pow_le_pow_left₀ (abs_nonneg _)
                (abs_smear_dom_le ha _ _ hdk (F i).2 (hF i) U) _
        _ = L i ^ (2 * Fintype.card ι)
              * stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k P).1 ^ (2 * Fintype.card ι)) :=
            (stateK hN k).map_smul _ _
        _ ≤ L i ^ (2 * Fintype.card ι) * B :=
            mul_le_mul_of_nonneg_left (hCk.trans ((le_abs_self C).trans hCB))
              (pow_nonneg (hLpos i).le _)
        _ = B * L i ^ (2 * Fintype.card ι) := mul_comm _ _
    · have hLi : L i = M i + 1 := by
        show (if i = i0 then dySpacing N k ^ 4 else 1) * L' i = _
        rw [if_neg hi, one_mul, hL']
        show (if i = i0 then (c + 1) * (M i + 1) else M i + 1) = _
        rw [if_neg hi]
      rw [hLi]
      exact (hk i (F i).2 (M i + 1) (hM1 i) (hF i)).trans
        (mul_le_mul_of_nonneg_right (hccB i) (pow_nonneg (hM1 i).le _))
  have ht : Tendsto (fun k => (1 + Fintype.card ι * B) * (dySpacing N k ^ 4 * ∏ i, L' i)) atTop
      (𝓝 0) := by
    have h0 := (((tendsto_dySpacing N).pow 4).mul_const (∏ i, L' i)).const_mul
      (1 + Fintype.card ι * B)
    simpa using h0
  have hz : Tendsto (fun k => latSF hN (energy0 W D hD) k F) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr
      (squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hev ht)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact (hz.mono_left ultra_le).limUnder_eq

include hpos hcube in
/-- **The reflection kernel with a bare dominated factor is `0`.** DERIVED: `0` the zero reading. -/
theorem kernF_eq_zero_of_dom (τ : Fin 4) (P Q : Mono N) (i0 : Fin Q.1) (hO : BareDom D (Q.2 i0).1) :
    kernF hN (energy0 W D hD) τ P Q = 0 :=
  contSF_eq_zero_of_dom hN W hD hpos hcube (pairFam τ P Q) (Sum.inr i0) hO

include hpos hcube in
/-- **A monomial with a bare dominated factor has connected reading `0`.** DERIVED: `0` the zero reading;
`2` the square. -/
theorem conn_eq_zero_of_dom (τ : Fin 4) (r : ℝ) (Q : Mono N) (i0 : Fin Q.1)
    (hO : BareDom D (Q.2 i0).1) :
    kernF hN (energy0 W D hD) τ Q Q - kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 Q ^ 2 = 0 := by
  rw [kernF_eq_zero_of_dom hN W hD hpos hcube τ Q Q i0 hO,
    kernF_eq_zero_of_dom hN W hD hpos hcube τ _ Q i0 hO]
  simp

include hpos hcube in
/-- **A witness has no bare dominated factor**, at any class of fields `A`, `UF N` included. DERIVED: `0`
the excluded value; `2` the square. -/
theorem exists_witness_free_of_dom {A : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (h : RegConnectedNonzero hN (energy0 W D hD) A τ r) :
    ∃ Q : RMono N A τ r,
      kernF hN (energy0 W D hD) τ Q.1.1 Q.1.1
          - kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 Q.1.1 ^ 2 ≠ 0
        ∧ ∀ i, ¬ BareDom D (Q.1.1.2 i).1 := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, hQ, fun i hi => hQ (conn_eq_zero_of_dom hN W hD hpos hcube τ r Q.1.1 i hi)⟩

/-- **The plaquette density is dominated by its symmetrisation.** The identity is one of the images and
the others are non-negative. DERIVED: `1` the coefficient and the identity image; `0` the sign. -/
theorem plaqField_le_sym (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq) (U : Cfg N) :
    |(plaqField (N := N) q).1 U| ≤ 1 * (sym (plaqField (N := N) q)).1 U := by
  have h0 : ∀ V : Cfg N, 0 ≤ (plaqField (N := N) q).1 V := fun V =>
    MassGap.WilsonAction.wilsonDensity_nonneg hN _
  rw [abs_of_nonneg (h0 U), one_mul, sym_apply]
  have hid : reflAll (fun _ => false) (ContinuumHypercubic.iaxisConf 1 U) = U := by
    show ContinuumHypercubic.iaxisConf 1 U = U
    funext l
    show U (ContinuumHypercubic.iaxisLink 1 l) = U l
    congr 1
  have key := Finset.single_le_sum
    (f := fun g : Equiv.Perm (Fin 4) × (Fin 4 → Bool) =>
      (plaqField (N := N) q).1 (reflAll g.2 (ContinuumHypercubic.iaxisConf g.1 U)))
    (fun g _ => h0 _) (Finset.mem_univ ((1 : Equiv.Perm (Fin 4)), fun _ => false))
  have e : (plaqField (N := N) q).1 (reflAll (fun _ => false) (ContinuumHypercubic.iaxisConf 1 U))
      = (plaqField (N := N) q).1 U := congrArg _ hid
  exact e.symm.le.trans key

/-- **The bare plaquette at the symmetrised class.** Outside the class it is a bare dominated field, so
it reads `0` (`conn_eq_zero_of_dom`). DERIVED: `0` the sign of the coefficient; `1` the coefficient. -/
theorem bareDom_plaqField (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq)
    (hq : plaqField (N := N) q ∉ SymPlaqClass N) : BareDom (SymPlaqClass N) (plaqField (N := N) q) :=
  ⟨hq, sym (plaqField q), ⟨q, rfl⟩, 1, zero_le_one, plaqField_le_sym hN q⟩

end Dominated

/-! ## 3. Coupling zero -/

section Haar

open MassGap.GibbsSpec (spec num part wt VConf splice splice_mem splice_not_mem)
open MassGap.PeriodicStateDLR MassGap.WilsonAction
open MassGap.PeriodicState (periodicState)
open MassGap.CompactGauge (probHaar)

/-- **At coupling zero the DLR kernel of a field local on `S` does not read the boundary.** DERIVED: `0`
the coupling; `1` the weight. -/
theorem wspec_zero_const (hN : N ≠ 0) {S : Finset ILink} (F : C(IConf (MassGap.SUN.SU N), ℝ))
    (hF : IsLocalOn S (F : IConf (MassGap.SUN.SU N) → ℝ)) (ω ω' : IConf (MassGap.SUN.SU N)) :
    wspec hN 0 S F ω = wspec hN 0 S F ω' := by
  rw [wspec_apply, wspec_apply]
  unfold spec num part
  have hwt : ∀ (u : VConf (MassGap.SUN.SU N) S) (η : IConf (MassGap.SUN.SU N)),
      wt (wilsonDensity (N := N)) 0 S u η = 1 := fun u η => by
    unfold wt
    simp
  simp only [hwt, mul_one]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  exact hF _ _ fun l hl => by rw [splice_mem hl, splice_mem hl]

/-- **At coupling zero, disjoint supports are independent.** `ν₀(F Y) = ν₀(wspec (F Y)) =
ν₀(wspec F · Y)` and `wspec F` is constant. DERIVED: `0` the coupling; `1` the constant observable. -/
theorem haar_factorise (hN : N ≠ 0) {S T : Finset ILink} (hST : Disjoint S T)
    (F Y : C(IConf (MassGap.SUN.SU N), ℝ))
    (hF : IsLocalOn S (F : IConf (MassGap.SUN.SU N) → ℝ))
    (hY : IsLocalOn T (Y : IConf (MassGap.SUN.SU N) → ℝ)) :
    periodicState hN 0 (F * Y) = periodicState hN 0 F * periodicState hN 0 Y := by
  have hspl : ∀ (u : VConf (MassGap.SUN.SU N) S) (ω : IConf (MassGap.SUN.SU N)),
      Y (splice S u ω) = Y ω := fun u ω =>
    hY _ _ fun l hl => splice_not_mem (Finset.disjoint_right.mp hST hl)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, ∀ ω, wspec hN 0 S F ω = κ :=
    ⟨wspec hN 0 S F 1, fun ω => wspec_zero_const hN F hF ω 1⟩
  have e1 : wspec hN 0 S (F * Y) = κ • Y := ContinuousMap.ext fun ω => by
    rw [MassGap.ReadPos.wspec_mul_outside hN 0 S F Y hspl ω, hκ]
    rfl
  have e2 : wspec hN 0 S F = κ • (1 : C(IConf (MassGap.SUN.SU N), ℝ)) :=
    ContinuousMap.ext fun ω => by
      rw [hκ]
      simp
  rw [← periodicState_dlr hN 0 S (F * Y), e1, ← periodicState_dlr hN 0 S F, e2,
    (periodicState hN 0).map_smul, (periodicState hN 0).map_smul, (periodicState hN 0).map_one,
    mul_one]

/-- The periodic state reads a reflected observable as the observable. DERIVED: `0` the coupling and the
plane. -/
theorem haar_refl_read (hN : N ≠ 0) (τ : Fin 4) (X : C(IConf (MassGap.SUN.SU N), ℝ)) :
    periodicState hN 0 (LatticeReflection.ireflObs τ 0 X) = periodicState hN 0 X :=
  MassGap.PeriodicState.periodicState_reflInvariant hN 0 τ 0 X

/-- **At coupling zero the reflected read of the strict half-space factorises.** The support lies above
the first sheet, so its mirror about the plane is disjoint from it
(`HalfSpaceAlgebra.disjoint_image_ireflLink_posHalf` at `p = 1`). DERIVED: `0` the coupling and the plane;
`1` the first sheet; `2` the two copies of the read. -/
theorem haar_refl_mul (hN : N ≠ 0) (τ : Fin 4) {X : C(IConf (MassGap.SUN.SU N), ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1) :
    periodicState hN 0 (LatticeReflection.ireflObs τ 0 X * X) = periodicState hN 0 X ^ 2 := by
  classical
  obtain ⟨S, hS, hl⟩ := HalfSpaceAlgebra.mem_halfSpaceAlg.mp hX
  have hdis := HalfSpaceAlgebra.disjoint_image_ireflLink_posHalf τ 1 hS
  have e : (2 * (1 : ℤ) - 2) = 0 := by norm_num
  rw [e] at hdis
  rw [haar_factorise hN hdis _ X (HalfSpaceAlgebra.isLocalOn_ireflObs τ 0 hl) hl,
    haar_refl_read hN τ X, sq]

/-- `transObs_mem_halfSpaceAlg` at the first sheet. DERIVED: `1` the sheet. -/
theorem transObs_mem_sheet {S : Finset ILink} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    (hF : IsLocalOn S (F : IConf (MassGap.SUN.SU N) → ℝ)) (τ : Fin 4) (x : ISite)
    (hx : ∀ l ∈ S, 1 ≤ l.2 τ + x τ) :
    transObs x F ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1 := by
  refine HalfSpaceAlgebra.mem_halfSpaceAlg.mpr
    ⟨S.image (fun l : ILink => (l.1, l.2 + x)), ?_, isLocalOn_transObs hF x⟩
  intro l hl
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl)
  show (1 : ℤ) ≤ (m.2 + x) τ
  exact hx m hm

/-- `smear_mem_halfSpaceAlg` at the first sheet. DERIVED: `0` the sign of `a`; `1` the sheet. -/
theorem smear_mem_sheet {a : ℝ} (ha : 0 < a) (τ : Fin 4) {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {S : Finset ILink} (hS : IsLocalOn S (F : IConf (MassGap.SUN.SU N) → ℝ)) {D : ℕ}
    (hD : ∀ l ∈ S, 1 - l.2 τ ≤ (D : ℤ)) {δ : ℝ} (haD : a * D ≤ δ) (f : TestFn)
    (hδ : ∀ y, f.1 y ≠ 0 → δ ≤ y τ) :
    smear a F f ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1 := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _)]
  refine Submodule.sum_mem _ (fun x _ => ?_)
  by_cases h0 : f.1 (site a x) = 0
  · rw [h0, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (transObs_mem_sheet hS τ x ?_)
    intro l hl
    have h1 : δ ≤ a * (x τ : ℝ) := hδ _ h0
    have h2 : (D : ℝ) ≤ (x τ : ℝ) := by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_mul_of_pos_left hlt ha
      linarith
    have h3 : (D : ℤ) ≤ x τ := by exact_mod_cast h2
    have h4 := hD l hl
    omega

/-- **A flow of physical range `r` puts a smeared field beyond the margin above the first sheet.** The
proof of `Flow.posPreserving_of_physRange` with the depth raised by one. DERIVED: `0` the limit and the
excluded colour count; `1` the sheet. -/
theorem eventually_smear_mem_sheet (hN : N ≠ 0) (Φ : Flow N) {r : ℝ} (hΦ : Φ.PhysRange r) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) (f : TestFn) {δ : ℝ} (hrδ : r < δ)
    (hf : ∀ y, f.1 y ≠ 0 → δ ≤ y τ) :
    ∀ᶠ k in atTop, smear (dySpacing N k) (Φ.map k O).1 f
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1 := by
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D0, hD0⟩ := exists_depth τ S
  have ht : Tendsto (fun k => dySpacing N k * ((D0 + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const ((D0 + 1 : ℕ) : ℝ)
  have hΦ' : ∀ᶠ k in atTop, dySpacing N k * (Φ.range k : ℝ) ≤ r := hΦ
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hrδ)), hΦ'] with k hk hkr
  have hk' : dySpacing N k * ((D0 + 1 : ℕ) : ℝ) < δ - r := hk
  obtain ⟨S', hS', hrange⟩ := Φ.map_local k O S hS
  have hD' : ∀ l ∈ S', 1 - l.2 τ ≤ ((D0 + 1 + Φ.range k : ℕ) : ℤ) := by
    intro l' hl'
    obtain ⟨l, hl, hll⟩ := hrange l' hl'
    have h1 := hD0 l hl
    have h2 := (abs_le.mp (hll τ)).1
    have e : ((D0 + 1 + Φ.range k : ℕ) : ℤ) = (D0 : ℤ) + 1 + (Φ.range k : ℤ) := by push_cast; ring
    rw [e]
    omega
  have haD : dySpacing N k * ((D0 + 1 + Φ.range k : ℕ) : ℝ) ≤ δ := by
    have e : ((D0 + 1 + Φ.range k : ℕ) : ℝ) = ((D0 + 1 : ℕ) : ℝ) + (Φ.range k : ℝ) := by
      push_cast; ring
    rw [e, mul_add]
    linarith
  exact smear_mem_sheet (dySpacing_pos (one_le_of_ne_zero hN) k) τ hS' hD' haD f hf

/-- **At coupling zero every margin monomial has connected reading exactly `0`, eventually in the step,**
for any flow of physical range `r`, so at any normalisation of the fields. DERIVED: `0` the coupling, the
plane and the zero reading; `1` the sheet; `2` the square. -/
theorem haar_conn_zero (hN : N ≠ 0) (Φ : Flow N) {r : ℝ} (hΦ : Φ.PhysRange r) (τ : Fin 4)
    (Q : MarginMono N τ r) :
    ∀ᶠ k in atTop, connAt (periodicState hN 0) (dySpacing N k) τ (Φ.mono k Q.1) = 0 := by
  obtain ⟨d, _, hrd, hQ⟩ := Q.2
  have hmem : ∀ᶠ k in atTop, ∀ i : Fin Q.1.1,
      smear (dySpacing N k) (Φ.map k (Q.1.2 i).1).1 (Q.1.2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1 :=
    Filter.eventually_all.mpr fun i =>
      eventually_smear_mem_sheet hN Φ hΦ τ (Q.1.2 i).1 (Q.1.2 i).2 hrd (hQ i)
  filter_upwards [hmem] with k hk
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hX : prodSmear (dySpacing N k) (Φ.mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ 1 :=
    HalfSpaceAlgebra.halfSpaceAlg_prod_mem τ 1 Finset.univ _ (fun i _ => hk i)
  rw [connAt_eq_cov _ ha τ (MassGap.PeriodicState.periodicState_reflInvariant hN 0 τ 0)]
  unfold stateCov
  rw [haar_refl_mul hN τ hX, haar_refl_read hN τ, sq, sub_self]

/-- **The variance floor at coupling zero does not reach the reading**: at `β = 0` the Haar variance of
`Re tr` is strictly positive, and the connected reading of every margin monomial is `0`. DERIVED: `0` the
coupling, the floor and the zero reading; `2` the least rank. -/
theorem floor_not_from_haar (hN2 : 2 ≤ N) (Φ : Flow N) {r : ℝ} (hΦ : Φ.PhysRange r) (τ : Fin 4)
    (Q : MarginMono N τ r) :
    0 < ProbabilityTheory.variance (MassGap.HaarVariance.reTr (N := N)) (probHaar (MassGap.SUN.SU N))
      ∧ ∀ᶠ k in atTop,
        connAt (periodicState (by omega : N ≠ 0) 0) (dySpacing N k) τ (Φ.mono k Q.1) = 0 :=
  ⟨MassGap.HaarVariance.haar_variance_reTr_pos hN2, haar_conn_zero _ Φ hΦ τ Q⟩

end Haar

end MassGap.RegNontrivial

end

#print axioms MassGap.RegNontrivial.eMono
#print axioms MassGap.RegNontrivial.connAt
#print axioms MassGap.RegNontrivial.connAt_eq_cov
#print axioms MassGap.RegNontrivial.latSF_conn
#print axioms MassGap.RegNontrivial.regConnected_iff_floor
#print axioms MassGap.RegNontrivial.BareDom
#print axioms MassGap.RegNontrivial.abs_smear_dom_le
#print axioms MassGap.RegNontrivial.contSF_eq_zero_of_dom
#print axioms MassGap.RegNontrivial.kernF_eq_zero_of_dom
#print axioms MassGap.RegNontrivial.conn_eq_zero_of_dom
#print axioms MassGap.RegNontrivial.exists_witness_free_of_dom
#print axioms MassGap.RegNontrivial.plaqField_le_sym
#print axioms MassGap.RegNontrivial.bareDom_plaqField
#print axioms MassGap.RegNontrivial.wspec_zero_const
#print axioms MassGap.RegNontrivial.haar_factorise
#print axioms MassGap.RegNontrivial.haar_refl_read
#print axioms MassGap.RegNontrivial.haar_refl_mul
#print axioms MassGap.RegNontrivial.transObs_mem_sheet
#print axioms MassGap.RegNontrivial.smear_mem_sheet
#print axioms MassGap.RegNontrivial.eventually_smear_mem_sheet
#print axioms MassGap.RegNontrivial.haar_conn_zero
#print axioms MassGap.RegNontrivial.floor_not_from_haar
