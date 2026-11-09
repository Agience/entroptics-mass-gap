import Mathlib
import MassGap.ReadPos

/-!
# MassGap.PlaqIndep — the plaquette densities are linearly independent, and no combination of translates of the tensor reading is reflection-symmetric as a function

`BandClose.not_translate_combination` proves at the coefficient level that the mirror `θ` about `x₀ = 0` carries
no finitely supported combination of translates of `E = tensorEnergyG` into the span of translates of `E`.
This module proves the function-level statements. Declarations are in the namespace `MassGap.PlaqIndep`.

## The argument

A single-link configuration `U = 1` off a link `l` and `g` on it reads a plaquette density as `d(g)` when the
plaquette contains `l` and `0` otherwise (`Pq_single`, `d = wilsonDensityG`; the reversed link reads `g⁻¹`,
and `d(g⁻¹) = d(g)`). For `N ≥ 2` an element `g ≠ 1` (`HaarVariance.flipEl`, through `ReadPos.exists_ne_one`)
has `d(g) ≠ 0`.

* A time link `(0, x)` lies in the `(0, 1)`-plaquettes at `x` and `x − e₁` and in no `(2, 3)`-plaquette; a link
  `(2, x)` lies in the `(2, 3)`-plaquettes at `x` and `x − e₃` and in no `(0, 1)`-plaquette (`P01_at0`,
  `P23_at0`, `P23_at2`, `P01_at2`).
* So a vanishing combination `Σ_a α_a P₀₁(a) + γ_a P₂₃(a)` has `α(x) + α(x − e₁) = 0` and
  `γ(x) + γ(x − e₃) = 0` at every `x`; `|α|` and `|γ|` are constant along lines, so finite support forces
  `α = γ = 0` (`chain_zero`, `plaqFamily_linearIndependent`).
* `θ P₀₁(a) = P₀₁(ρa − e₀)` and `θ P₂₃(a) = P₂₃(ρa)` (`ρ` the site mirror). If `θ(Σ w_a E(a)) = Σ v_b E(b)`,
  the same two reads give `W(ρ(x + e₀)) = V(x) = W(ρx)` for every `x`, i.e. `W(c − e₀) = W(c)`, and
  `BandClose.not_translate_combination` gives `W = 0` (`not_translate_function`).

Linear independence is proved for the family the argument uses: the `(0, 1)`- and `(2, 3)`-plaquette densities
at all bases, as a `LinearIndependent ℝ` family over `Bool × ISite` (`plaqFamily_linearIndependent`). The swap identity `BandClose.plaqFieldG_swap` identifies `P₁₀` with `P₀₁`
and `P₃₂` with `P₂₃`, so the family is the one modulo swap.

## What does not follow, plainly

* Linear independence of all six oriented plane families together is not proved here. A time link lies in
  plaquettes of the three planes `(0, ν)`, so the single-link reads couple the planes; the two-plane family above
  is the one the tensor reading uses, and the chain argument closes only on it.
* At `N = 1` every density is `0` (`SU(1)` is trivial) and both statements fail; the hypothesis `2 ≤ N` is used.
* The function-level statement removes the "granting linear independence" proviso of `BandClose`: no nonzero
  finite combination of translates of `E` equals its own reflection, or lies in the span of translates of `E`
  after reflection, as a function on configurations. It says nothing about `measMassOfG`, does not bound the
  mirror defect read `R m` of `BandClose`, and closes none of the three open items (`StrongEnd N`, `ExistAlong`,
  `ReflFloorAt`).

DERIVED (module-wide): `0` the time axis, the mirror plane, the origin and the zero coefficient; `1` the unit
step, the group unit and the unit indicator; `2` the least rank and the first direction of the `(2, 3)` plane;
`3` the last plane direction. No measured number enters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.PlaqIndep

open MassGap MassGap.InfiniteLattice MassGap.ApertureThing MassGap.MeasuredTower
open MassGap.ReadPos (Conf Pq)

variable {N : ℕ} [NeZero N]

/-! ## 1. Single-link configurations read one plaquette's density -/

/-- The unit step in direction `μ`. DERIVED: `1` the unit step. -/
def eD (μ : Fin 4) : ISite := Pi.single μ 1

theorem eD_zero : eD 0 = eT := rfl

/-- A forward step is the site plus the unit vector. DERIVED: `1` the unit step. -/
theorem ishift_eq (μ : Fin 4) (x : ISite) : MassGap.GibbsSpec.ishift μ x = x + eD μ := by
  funext j
  by_cases h : j = μ
  · subst h; simp [MassGap.GibbsSpec.ishift, eD]
  · simp [MassGap.GibbsSpec.ishift, eD, Function.update_of_ne h, Pi.single_apply, h]

theorem ishift_ne (μ : Fin 4) (x : ISite) : MassGap.GibbsSpec.ishift μ x ≠ x := by
  intro e
  have := congrFun e μ
  simp [MassGap.GibbsSpec.ishift] at this

theorem sub_eD_ne (μ : Fin 4) (x : ISite) : x - eD μ ≠ x := by
  intro e
  have := congrFun e μ
  simp [eD] at this

/-- The configuration `1` off the link `l` and `g` on it. DERIVED: `1` the group unit. -/
abbrev single (l : MassGap.InfiniteLattice.ILink) (g : MassGap.SUN.SU N) : Conf N :=
  Function.update (1 : Conf N) l g

/-- **A single-link configuration reads a plaquette density as `d(g)` on the plaquette's links and `0` off
them.** DERIVED: `1` the group unit; `0` the off-plaquette read. -/
theorem Pq_single (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) (l : MassGap.InfiniteLattice.ILink)
    (g : MassGap.SUN.SU N) :
    Pq (N := N) q (single l g)
      = if l ∈ MassGap.GibbsSpec.ilinks q then GaugeGroup.wilsonDensityG _ g else 0 := by
  show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q (single l g)) = _
  split_ifs with hl
  · have hs1 := ishift_ne q.1.1 q.2
    have hs2 := ishift_ne q.1.2 q.2
    rw [MassGap.GibbsSpec.ilinks_eq] at hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [single, MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd,
        Function.update_apply, hq, hq.symm, hs1, hs2, hs1.symm, hs2.symm, GaugeGroup.wilsonDensityG_inv]
  · rw [MassGap.GibbsSpec.ihol_congr q _ 1 (fun l' hl' =>
      Function.update_of_ne (fun e => hl (by rw [← e]; exact hl')) _ _), ReadPos.ihol_one, GaugeGroup.wilsonDensityG_one]

/-- The `(0, 1)`-plaquette at `a`. DERIVED: `0`, `1` the plane. -/
abbrev q01 (a : ISite) : MassGap.GibbsSpec.IPlaq := (((0 : Fin 4), (1 : Fin 4)), a)
/-- The `(2, 3)`-plaquette at `a`. DERIVED: `2`, `3` the plane. -/
abbrev q23 (a : ISite) : MassGap.GibbsSpec.IPlaq := (((2 : Fin 4), (3 : Fin 4)), a)

theorem mem01_0 (a x : ISite) :
    (((0 : Fin 4), x) : MassGap.InfiniteLattice.ILink) ∈ MassGap.GibbsSpec.ilinks (q01 a)
      ↔ a = x ∨ a = x - eD 1 := by
  rw [MassGap.GibbsSpec.ilinks_eq]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, ishift_eq]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  simp only [h01, false_and, or_false, true_and, false_or]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (rfl | rfl) <;> simp

theorem mem23_2 (a x : ISite) :
    (((2 : Fin 4), x) : MassGap.InfiniteLattice.ILink) ∈ MassGap.GibbsSpec.ilinks (q23 a)
      ↔ a = x ∨ a = x - eD 3 := by
  rw [MassGap.GibbsSpec.ilinks_eq]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq, ishift_eq]
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [h23, false_and, or_false, true_and, false_or]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (rfl | rfl) <;> simp

theorem not_mem23_0 (a x : ISite) :
    (((0 : Fin 4), x) : MassGap.InfiniteLattice.ILink) ∉ MassGap.GibbsSpec.ilinks (q23 a) := by
  intro h
  rcases ReadPos.fst_of_mem_ilinks h with h | h <;> exact absurd h (by simp)

theorem not_mem01_2 (a x : ISite) :
    (((2 : Fin 4), x) : MassGap.InfiniteLattice.ILink) ∉ MassGap.GibbsSpec.ilinks (q01 a) := by
  intro h
  rcases ReadPos.fst_of_mem_ilinks h with h | h <;> exact absurd h (by simp)

/-- Two disjoint conditions: the read of their disjunction is the sum of the reads. DERIVED: `1` the unit
indicator; `0` the empty read. -/
theorem ite_or_split {x y a : ISite} (hxy : y ≠ x) (d : ℝ) :
    (if a = x ∨ a = y then d else 0)
      = d * ((if a = x then 1 else 0) + (if a = y then 1 else 0)) := by
  by_cases h1 : a = x
  · subst h1; simp [hxy.symm]
  · by_cases h2 : a = y <;> simp [h1, h2, hxy]

theorem P01_at0 (a x : ISite) (g : MassGap.SUN.SU N) :
    Pq (N := N) (q01 a) (single ((0 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g
        * ((if a = x then 1 else 0) + (if a = x - eD 1 then 1 else 0)) := by
  rw [Pq_single _ (by simp)]
  simp only [mem01_0]
  exact ite_or_split (sub_eD_ne 1 x) _

theorem P23_at2 (a x : ISite) (g : MassGap.SUN.SU N) :
    Pq (N := N) (q23 a) (single ((2 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g
        * ((if a = x then 1 else 0) + (if a = x - eD 3 then 1 else 0)) := by
  rw [Pq_single _ (by simp)]
  simp only [mem23_2]
  exact ite_or_split (sub_eD_ne 3 x) _

theorem P23_at0 (a x : ISite) (g : MassGap.SUN.SU N) :
    Pq (N := N) (q23 a) (single ((0 : Fin 4), x) g) = 0 := by
  rw [Pq_single _ (by simp), if_neg (not_mem23_0 a x)]

theorem P01_at2 (a x : ISite) (g : MassGap.SUN.SU N) :
    Pq (N := N) (q01 a) (single ((2 : Fin 4), x) g) = 0 := by
  rw [Pq_single _ (by simp), if_neg (not_mem01_2 a x)]

/-! ## 2. Finite sums of indicator reads -/

section Sums

variable {ι : Type} [DecidableEq ι]

/-- The coefficients `w` restricted to `S`. DERIVED: `0` the coefficient off `S`. -/
def W (S : Finset ι) (w : ι → ℝ) (y : ι) : ℝ := if y ∈ S then w y else 0

theorem W_support_finite (S : Finset ι) (w : ι → ℝ) : (Function.support (W S w)).Finite := by
  refine S.finite_toSet.subset fun y hy => ?_
  by_contra h
  exact hy (by simp [W, show y ∉ S from h])

theorem sum_ind (S : Finset ι) (w : ι → ℝ) (y : ι) :
    ∑ a ∈ S, w a * (if a = y then 1 else 0) = W S w y := by
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', W]

theorem sum_pair (S : Finset ι) (w : ι → ℝ) (d : ℝ) (y₁ y₂ : ι) :
    ∑ a ∈ S, w a * (d * ((if a = y₁ then 1 else 0) + (if a = y₂ then 1 else 0)))
      = d * (W S w y₁ + W S w y₂) := by
  rw [← sum_ind S w y₁, ← sum_ind S w y₂, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Sums

/-- **A finitely supported `f` with `f(x) + f(x − e_μ) = 0` everywhere is zero**: `|f|` is constant along the
line. DERIVED: `0` the zero function; `1` the unit step. -/
theorem chain_zero (μ : Fin 4) (f : ISite → ℝ) (hfin : (Function.support f).Finite)
    (hrel : ∀ x, f x + f (x - eD μ) = 0) : f = 0 := by
  funext c
  by_contra hne
  have hmem : ∀ n : ℕ, c - n • eD μ ∈ Function.support f := by
    intro n
    induction n with
    | zero => simpa using hne
    | succ n ih =>
      have e : c - (n + 1) • eD μ = (c - n • eD μ) - eD μ := by rw [add_smul, one_smul]; abel
      rw [Function.mem_support, e]
      have := hrel (c - n • eD μ)
      rw [Function.mem_support] at ih
      intro h0
      exact ih (by linarith)
  have hinj : Function.Injective fun n : ℕ => c - n • eD μ := by
    intro n n' h
    have h0 := congrFun h μ
    simp [eD] at h0
    exact_mod_cast h0
  exact (Set.infinite_of_injective_forall_mem hinj hmem) hfin

/-! ## 3. Linear independence of the plaquette densities -/

/-- `d(g) ≠ 0` for some `g` at `N ≥ 2`. DERIVED: `2` the least rank. -/
theorem exists_density_ne (hN : 2 ≤ N) :
    ∃ g : MassGap.SUN.SU N, GaugeGroup.wilsonDensityG _ g ≠ 0 := by
  obtain ⟨g, hg⟩ := ReadPos.exists_ne_one (N := N) hN
  exact ⟨g, fun e => hg ((GaugeGroup.wilsonDensityG_eq_zero_iff g).mp e)⟩

/-- The family of `(0, 1)`- (`false`) and `(2, 3)`- (`true`) plaquette densities, one per base. Modulo the
swap identity `BandClose.plaqFieldG_swap` these are all densities of the two planes. DERIVED: the planes. -/
def plaqFamily : Bool × ISite → C(Conf N, ℝ)
  | (false, a) => Pq (N := N) (q01 a)
  | (true, a) => Pq (N := N) (q23 a)

theorem fam_at0 (p : Bool × ISite) (x : ISite) (g : MassGap.SUN.SU N) :
    plaqFamily (N := N) p (single ((0 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g
        * ((if p = (false, x) then 1 else 0) + (if p = (false, x - eD 1) then 1 else 0)) := by
  obtain ⟨b, a⟩ := p
  cases b
  · show Pq (N := N) (q01 a) _ = _
    rw [P01_at0]
    simp
  · show Pq (N := N) (q23 a) _ = _
    rw [P23_at0]
    simp

theorem fam_at2 (p : Bool × ISite) (x : ISite) (g : MassGap.SUN.SU N) :
    plaqFamily (N := N) p (single ((2 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g
        * ((if p = (true, x) then 1 else 0) + (if p = (true, x - eD 3) then 1 else 0)) := by
  obtain ⟨b, a⟩ := p
  cases b
  · show Pq (N := N) (q01 a) _ = _
    rw [P01_at2]
    simp
  · show Pq (N := N) (q23 a) _ = _
    rw [P23_at2]
    simp

/-- The coefficients along one plane, as a function of the base, have finite support. -/
theorem slice_support_finite (s : Finset (Bool × ISite)) (c : Bool × ISite → ℝ) (b : Bool) :
    (Function.support fun y => W s c (b, y)).Finite := by
  refine (s.image Prod.snd).finite_toSet.subset fun y hy => ?_
  have hm : (b, y) ∈ s := by
    by_contra h
    exact hy (by simp [W, h])
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(b, y), hm, rfl⟩)

/-- **The `(0, 1)`- and `(2, 3)`-plaquette densities are linearly independent as functions on configurations**
at `N ≥ 2`. A vanishing finite combination is read at the single-link configurations `g` on `(0, x)` and on
`(2, x)`, `d(g) ≠ 0`: the coefficients satisfy `α(x) + α(x − e₁) = 0` and `γ(x) + γ(x − e₃) = 0`, and finite
support forces both to vanish. DERIVED: `2` the least rank; `0`, `1`, `2`, `3` the probing links and the
planes. -/
theorem plaqFamily_linearIndependent (hN : 2 ≤ N) : LinearIndependent ℝ (plaqFamily (N := N)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hs i hi
  obtain ⟨g, hg⟩ := exists_density_ne (N := N) hN
  have read : ∀ U : Conf N, ∑ p ∈ s, c p * plaqFamily (N := N) p U = 0 := fun U => by
    have := congrArg (fun F : C(Conf N, ℝ) => F U) hs
    simpa [ContinuousMap.coe_sum, Finset.sum_apply] using this
  have hA : (fun y => W s c (false, y)) = 0 := chain_zero 1 _ (slice_support_finite s c false) fun x => by
    have h := read (single ((0 : Fin 4), x) g)
    simp only [fam_at0] at h
    rw [sum_pair] at h
    exact (mul_eq_zero.mp h).resolve_left hg
  have hB : (fun y => W s c (true, y)) = 0 := chain_zero 3 _ (slice_support_finite s c true) fun x => by
    have h := read (single ((2 : Fin 4), x) g)
    simp only [fam_at2] at h
    rw [sum_pair] at h
    exact (mul_eq_zero.mp h).resolve_left hg
  obtain ⟨b, a⟩ := i
  cases b
  · simpa [W, hi] using congrFun hA a
  · simpa [W, hi] using congrFun hB a

/-! ## 4. No combination of translates of `E` is reflection-symmetric as a function -/

/-- The site mirror about `x₀ = 0`. DERIVED: `0` the axis and the mirror plane. -/
abbrev ρ : ISite → ISite := LatticeReflection.ireflSite 0 0

theorem ρ_eq_iff (a y : ISite) : ρ a = y ↔ a = ρ y := by
  constructor
  · rintro rfl; exact (LatticeReflection.ireflSite_involutive 0 0 a).symm
  · rintro rfl; exact LatticeReflection.ireflSite_involutive 0 0 y

theorem ρ_ρ (c : ISite) : ρ (ρ c) = c := LatticeReflection.ireflSite_involutive 0 0 c

theorem ρ_sub_eq_iff (a y : ISite) : ρ a - eT = y ↔ a = ρ (y + eT) := by
  rw [sub_eq_iff_eq_add, ρ_eq_iff]

/-- `ρ(x + e₀) = ρx − e₀`. DERIVED: `0` the axis; `1` the unit step. -/
theorem ρ_add_eT (x : ISite) : ρ (x + eT) = ρ x - eT := by
  funext i
  fin_cases i <;> simp [LatticeReflection.ireflSite, eT] <;> ring

/-- The reflected `(0, 1)`-base: the reflection about `−1` is the mirror image shifted by `−e₀`.
DERIVED: `0`, `1` the axis and the link length. -/
theorem ireflSite_sub_one (a : ISite) : LatticeReflection.ireflSite 0 (0 - 1) a = ρ a - eT := by
  funext i
  fin_cases i <;> simp [LatticeReflection.ireflSite, eT] <;> ring

/-- **The mirror on a translate of `E`**: `θ(E a) = P₀₁(ρa − e₀) − P₂₃(ρa)`. DERIVED: `0`, `1`, `2`, `3` the
two planes; `0` the mirror. -/
theorem ireflObs_tensorEnergyG (a : ISite) :
    LatticeReflection.ireflObs 0 0 (tensorEnergyG (MassGap.SUN.SU N) a)
      = Pq (N := N) (q01 (ρ a - eT)) - Pq (N := N) (q23 (ρ a)) := by
  unfold MassGap.MeasuredTower.tensorEnergyG
  rw [map_sub, BandClose.ireflObs_plaqFieldG, BandClose.ireflObs_plaqFieldG]
  have h1 : LatticeReflection.ireflPlaq 0 0 (((0 : Fin 4), (1 : Fin 4)), a)
      = (((1 : Fin 4), (0 : Fin 4)), ρ a - eT) := by
    simp only [LatticeReflection.ireflPlaq, if_true]
    rw [ireflSite_sub_one]
  have h2 : LatticeReflection.ireflPlaq 0 0 (((2 : Fin 4), (3 : Fin 4)), a)
      = (((2 : Fin 4), (3 : Fin 4)), ρ a) := by
    simp only [LatticeReflection.ireflPlaq]
    rw [if_neg (by decide), if_neg (by decide)]
  rw [h1, h2, BandClose.plaqFieldG_swap (N := N) 0 1]

/-- A finite combination of translates of `E` over `S`. DERIVED: no numeral. -/
def transComb (S : Finset ISite) (w : ISite → ℝ) : C(Conf N, ℝ) :=
  ∑ a ∈ S, w a • tensorEnergyG (MassGap.SUN.SU N) a

theorem E_at0 (a x : ISite) (g : MassGap.SUN.SU N) :
    tensorEnergyG (MassGap.SUN.SU N) a (single ((0 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g * ((if a = x then 1 else 0) + (if a = x - eD 1 then 1 else 0)) := by
  show Pq (N := N) (q01 a) _ - Pq (N := N) (q23 a) _ = _
  rw [P01_at0, P23_at0, sub_zero]

theorem E_at2 (a x : ISite) (g : MassGap.SUN.SU N) :
    tensorEnergyG (MassGap.SUN.SU N) a (single ((2 : Fin 4), x) g)
      = -GaugeGroup.wilsonDensityG _ g * ((if a = x then 1 else 0) + (if a = x - eD 3 then 1 else 0)) := by
  show Pq (N := N) (q01 a) _ - Pq (N := N) (q23 a) _ = _
  rw [P01_at2, P23_at2]
  ring

theorem θE_at0 (a x : ISite) (g : MassGap.SUN.SU N) :
    LatticeReflection.ireflObs 0 0 (tensorEnergyG (MassGap.SUN.SU N) a) (single ((0 : Fin 4), x) g)
      = GaugeGroup.wilsonDensityG _ g
        * ((if a = ρ (x + eT) then 1 else 0) + (if a = ρ (x - eD 1 + eT) then 1 else 0)) := by
  rw [ireflObs_tensorEnergyG, ContinuousMap.sub_apply, P01_at0, P23_at0, sub_zero]
  simp only [ρ_sub_eq_iff]

theorem θE_at2 (a x : ISite) (g : MassGap.SUN.SU N) :
    LatticeReflection.ireflObs 0 0 (tensorEnergyG (MassGap.SUN.SU N) a) (single ((2 : Fin 4), x) g)
      = -GaugeGroup.wilsonDensityG _ g
        * ((if a = ρ (x + 0) then 1 else 0) + (if a = ρ (x - eD 3) then 1 else 0)) := by
  rw [ireflObs_tensorEnergyG, ContinuousMap.sub_apply, P01_at2, P23_at2, add_zero]
  simp only [ρ_eq_iff]
  ring

/-- `x ↦ W(ρ(x + t))` keeps finite support (the mirror and the shift are injective). DERIVED: no numeral. -/
theorem comp_support_finite (S : Finset ISite) (w : ISite → ℝ) (t : ISite) :
    (Function.support fun x => W S w (ρ (x + t))).Finite := by
  have hinj : Function.Injective fun x : ISite => ρ (x + t) := fun x y h =>
    add_right_cancel ((LatticeReflection.ireflSite_involutive 0 0).injective h)
  exact (W_support_finite S w).preimage hinj.injOn

/-- **No finitely supported combination of translates of `E` is carried by `θ` into the span of translates of
`E`, as functions on configurations**, at `N ≥ 2`: if `θ(Σ_{a ∈ S} w_a E(a)) = Σ_{b ∈ T} v_b E(b)` then
`w = 0` on `S`. The reads at `g` on `(0, x)` and on `(2, x)` give `W(ρ(x + e₀)) = V(x) = W(ρx)`, so
`W(c − e₀) = W(c)` and `BandClose.not_translate_combination` closes. DERIVED: `2` the least rank; `0`, `2`
the probing directions; `1`, `3` the plane partners. -/
theorem not_translate_function (hN : 2 ≤ N) (S T : Finset ISite) (w v : ISite → ℝ)
    (h : LatticeReflection.ireflObs 0 0 (transComb (N := N) S w) = transComb (N := N) T v) :
    ∀ a ∈ S, w a = 0 := by
  obtain ⟨g, hg⟩ := exists_density_ne (N := N) hN
  have read : ∀ U : Conf N, ∑ a ∈ S, w a * LatticeReflection.ireflObs 0 0
      (tensorEnergyG (MassGap.SUN.SU N) a) U = ∑ b ∈ T, v b * tensorEnergyG (MassGap.SUN.SU N) b U :=
    fun U => by
      have := congrArg (fun F : C(Conf N, ℝ) => F U) h
      simpa [transComb, map_sum, map_smul, ContinuousMap.coe_sum, Finset.sum_apply] using this
  have hΦ : (fun x => W S w (ρ (x + eT)) - W T v x) = 0 := by
    refine chain_zero 1 _ (((comp_support_finite S w eT).union (W_support_finite T v)).subset
      (Function.support_sub _ _)) fun x => ?_
    have hr := read (single ((0 : Fin 4), x) g)
    simp only [θE_at0, E_at0, sum_pair] at hr
    have := mul_left_cancel₀ hg hr
    show (W S w (ρ (x + eT)) - W T v x) + (W S w (ρ (x - eD 1 + eT)) - W T v (x - eD 1)) = 0
    linarith
  have hΨ : (fun x => W S w (ρ (x + 0)) - W T v x) = 0 := by
    refine chain_zero 3 _ (((comp_support_finite S w 0).union (W_support_finite T v)).subset
      (Function.support_sub _ _)) fun x => ?_
    have hr := read (single ((2 : Fin 4), x) g)
    simp only [θE_at2, E_at2, sum_pair] at hr
    have := mul_left_cancel₀ (neg_ne_zero.mpr hg) hr
    show (W S w (ρ (x + 0)) - W T v x) + (W S w (ρ (x - eD 3 + 0)) - W T v (x - eD 3)) = 0
    rw [add_zero (x - eD 3)]
    linarith
  have hshift : ∀ c : ISite, W S w (c - eT) = W S w c := fun c => by
    have h1 := congrFun hΦ (ρ c)
    have h2 := congrFun hΨ (ρ c)
    simp only [Pi.zero_apply, add_zero, sub_eq_zero] at h1 h2
    rw [ρ_add_eT, ρ_ρ] at h1
    rw [ρ_ρ] at h2
    rw [h1, h2]
  have hW := BandClose.not_translate_combination (W S w) (W_support_finite S w) hshift
  intro a ha
  simpa [W, ha] using congrFun hW a

/-- **No combination of translates of `E` equals its own reflection as a function**, unless every coefficient
is zero. DERIVED: `2` the least rank. -/
theorem not_reflection_symmetric (hN : 2 ≤ N) (S : Finset ISite) (w : ISite → ℝ)
    (h : LatticeReflection.ireflObs 0 0 (transComb (N := N) S w) = transComb (N := N) S w) :
    ∀ a ∈ S, w a = 0 :=
  not_translate_function hN S S w w h

end MassGap.PlaqIndep

end

#print axioms MassGap.PlaqIndep.ishift_eq
#print axioms MassGap.PlaqIndep.ishift_ne
#print axioms MassGap.PlaqIndep.sub_eD_ne
#print axioms MassGap.PlaqIndep.Pq_single
#print axioms MassGap.PlaqIndep.mem01_0
#print axioms MassGap.PlaqIndep.mem23_2
#print axioms MassGap.PlaqIndep.P01_at0
#print axioms MassGap.PlaqIndep.P23_at2
#print axioms MassGap.PlaqIndep.P23_at0
#print axioms MassGap.PlaqIndep.P01_at2
#print axioms MassGap.PlaqIndep.sum_pair
#print axioms MassGap.PlaqIndep.chain_zero
#print axioms MassGap.PlaqIndep.exists_density_ne
#print axioms MassGap.PlaqIndep.fam_at0
#print axioms MassGap.PlaqIndep.fam_at2
#print axioms MassGap.PlaqIndep.plaqFamily_linearIndependent
#print axioms MassGap.PlaqIndep.ρ_add_eT
#print axioms MassGap.PlaqIndep.ireflObs_tensorEnergyG
#print axioms MassGap.PlaqIndep.θE_at0
#print axioms MassGap.PlaqIndep.θE_at2
#print axioms MassGap.PlaqIndep.not_translate_function
#print axioms MassGap.PlaqIndep.not_reflection_symmetric
#print axioms MassGap.PlaqIndep.eD_zero
#print axioms MassGap.PlaqIndep.not_mem23_0
#print axioms MassGap.PlaqIndep.not_mem01_2
#print axioms MassGap.PlaqIndep.ite_or_split
#print axioms MassGap.PlaqIndep.W_support_finite
#print axioms MassGap.PlaqIndep.sum_ind
#print axioms MassGap.PlaqIndep.slice_support_finite
#print axioms MassGap.PlaqIndep.ρ_eq_iff
#print axioms MassGap.PlaqIndep.ρ_ρ
#print axioms MassGap.PlaqIndep.ρ_sub_eq_iff
#print axioms MassGap.PlaqIndep.ireflSite_sub_one
#print axioms MassGap.PlaqIndep.E_at0
#print axioms MassGap.PlaqIndep.E_at2
#print axioms MassGap.PlaqIndep.comp_support_finite
