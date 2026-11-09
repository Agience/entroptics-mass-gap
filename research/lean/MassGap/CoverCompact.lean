import Mathlib
import MassGap.CurveFloor
import MassGap.GaugeG2

/-!
# MassGap.CoverCompact — the abelian lift, perfect groups, and what a conserved plaquette charge is

Clay covers every compact simple `G`, including `G₂`, whose centre is trivial. The argued separator from `U(1)` is
topological: `π₁(G)` finite, equivalently a compact universal cover, against `π₁(U(1)) = ℤ` with cover `ℝ`. This module
proves the exact structure on both sides on the tree's periodic torus (`TorusDoubling.TSite`, `TLink`, `TPlaq`, holonomy
`HolderBondMoving.thol`) and locates what a character does and does not give. Declarations are in
`MassGap.CoverCompact`.

## 1. Additive forms (proved)

* `cubeSum`, `curl`: the additive cube sum and the additive plaquette word, in any abelian group. `cubeSum_curl`: `d² = 0`
  on links. `curl_swap`: antisymmetry.
* `hyper_cubeSum`: `d² = 0` on faces. Every antisymmetric face function has a conserved cube sum, whatever the group.
  So a conserved integer defect current is available for every `G`; it is not what separates `U(1)`.

## 2. The `U(1)` structure (proved)

* `exists_link_lift`: every link field lifts to `ℝ`. `exists_angle`: an antisymmetric plaquette angle `a`
  (`IsAngle`) exists. `thol_exp`: the holonomy of a lifted field is the exponential of the curl.
* `exists_split`: `a = dθ + 2π n` with `n` integer and antisymmetric. `cubeSum_angle`: `cubeSum a = 2π cubeSum n`, so
  the integer charge is read off `a`. `charge_indep`: it does not depend on the lift. `charge_zero_of_small`: six faces
  with `|a| < π/3` carry no charge.
* `Liftable U a`: a real lift of `U` with `dθ = a`. `liftable_iff`: it exists exactly when `n` is the curl of an integer
  link field. `charge_zero_of_liftable`, `flux_zero_of_liftable` (from `sum_curl_slice`, real Stokes on a slice): its
  cube charges and slice fluxes vanish.
* `liftable_const`: holonomies are no obstruction: a constant field lifts with `a = 0`. `wa_isAngle`, `flux_witness`:
  on the `CHOSEN` side-`2` two-torus a field has every cube sum `0`, slice flux `2π`, and does not lift. So the lift is not
  characterized by cube charges and holonomies.
* `continuous_int_const`: on a connected `G` every continuous `ℤ`-valued function of a configuration is constant. This
  holds at `Circle`, so continuity of integer invariants does not separate the groups.

## 3. A conserved plaquette charge is a character (proved)

`conserved_iff_affine`: for `Q : G → A`, `A` any abelian group, any group `G`, a side `≥ 2` and three distinct directions,
the plain cube sum of `Q ∘ thol` vanishes at every configuration if and only if `Q(gh) + Q(1) = Q(g) + Q(h)`, that is,
`Q − Q(1)` is a homomorphism. The forward direction reads only the corner configurations `corner`
(`corner_relation`); the reverse applies the homomorphism to `CubeFlux.bianchi_transported`. This is the converse of
`CubeFlux.bianchi_comm`: exact conservation on plaquettes is the character and nothing else.

## 4. Perfect groups (proved at `SU(N)`, `SO(3)`, `A₅`; `G₂` given cited perfection)

* `hom_eq_one_of_perfect`: a perfect group has no non-trivial homomorphism to a commutative group, continuous or not.
  `conserved_const_of_perfect`: so a conserved plaquette charge on it is constant. `circle_not_perfect`.
* `exists_diag`: a unitary matrix is unitarily diagonal (Cayley transform at a regular unit, `exists_unit_regular`, then
  the Hermitian spectral theorem). `diag_commutator`: a diagonal element of `SU(N)` is `[μ P, ν C]`, `P` the cyclic
  permutation, `C = diag c`, `c(σ i) = d_i c_i` solved by partial products (`exists_cycle_solution`), and `∏ d = 1` closes
  the cycle. `su_everyCommutator`: every element of `SU(N)` is one commutator, at every `N`. `isPerfect_SU`,
  `su_no_character`.
* `exists_axis`, `exists_frame`, `stab_rot`, `rot_commutator`: `g = V R² V⁻¹` with `R` a rotation about `e₃`, and
  `R² = [R, H]`, `H` the half-turn about `e₂`. `so3_everyCommutator`, `isPerfect_SO3`.
* `conserved_const_G2`: the same at `G₂`, given the instance `Group.IsPerfect G2`. That instance is cited (Gotô: every
  element of a compact connected semisimple group is a commutator). `GaugeG2` carries no connectedness of `G2Sub`.
* `isPerfect_A5`, `instGaugeGroupA5`: the alternating group `A₅` is perfect and is a `GaugeGroup`, with the faithful
  permutation representation in `U(5)`. So perfection, the absence of characters, a trivial centre and a compact cover
  all hold at a finite group, which has a large-`β` phase of its own (below).
* `flat_twist`, `flat_twist_of_everyCommutator`, `twistedAction_flat_SU`: in a group where `z⁻¹` is a commutator the
  oriented twist `sheetO i j z` is absorbed at zero action on every torus, at every `N` and every `z`, extending
  `GapSideTwistFlat.twistedAction_flat_SU2`. At `U(1)` no such field exists (`GapSideTwistFlat.not_flat_of_comm`). On a
  2-torus the transported flux is the commutator of two holonomies: this is where perfection acts in the tree.

## Relation to the bridge (argued reading)

`D_∞ = 15 log(|Hom(ℤ⁴, G)| / |G|) > 0` at `β = ∞` for a finite `G` (by hand), and at large finite `β` a Peierls argument
(cited) keeps this constant along the windows in four dimensions. `D` vanishes at `β_⊥ = 0` for every compact group, so
argued: the segment of `A₅` has a stall and the `A₅` form of `MixCut.MixCutBound` fails at large `β`. Hence, as a statement
about method and not a theorem, a proof reading only the `GaugeGroup` interface and group facts true at `A₅` cannot give a
consumer: it must see elements arbitrarily near `1` and read `d = 4`. Compact `U(1)` in three dimensions has
the character and the lift and is massive at every `β` (Göpfert–Mack, Villain action, cited). So the character is neither
necessary nor sufficient for a stall. Argued: the conjunction "connected and no character" is, for a compact Lie group, positive
Ricci curvature (Milnor, cited), the floor of `CurveFloor`.

DERIVED (module-wide): `2π` the period of the circle; `π/3 = 2π/6` the charge quantum over the six faces of a cube; `2` the
least side on which the links of a cube are distinct (`CubeFlux.finRotate_ne_self`); `3` the dimension of `SO(3)`'s
matrices and the three directions of a cube; `5` the letters of `A₅`, the least `n` at which `A_n` is perfect and the
dimension of its permutation representation; `−1` the cosine of the half-turn; `0`, `1` the signs, the units and the charge
floor. CHOSEN: the witness angles `wθ`, `wa`, on `d = 2`, side `2`; the corner configuration `corner`; the regular unit in
`exists_unit_regular`, on which nothing depends. No inherited constants. Cited, not proved: `Group.IsPerfect G2`.

## What does not follow

Nothing here bounds `MixCut.mixCut`, `MixCutTest.VarGap`, `MixEqui.MixEquiUp`, `CouplingTower.StrongEnd` or a twisted ratio.
Every theorem is a statement about configurations and groups; none carries the Wilson measure. `conserved_iff_affine` is
sharp and no consumer reads a conserved charge. `twistedAction_flat_SU` gives a zero of the twisted action, not a bound on
`Z_g / Z`. The sufficiency of vanishing cube charges and slice fluxes for `Liftable` is not proved. The `A₅` stall is not
proved here: the `β = ∞` count is by hand, the finite-`β` step is cited, and the consumers are stated at `SU(N)` only.
`Group.IsPerfect G2` is not proved. Nothing here shows that `SU(N)` does not stall.
-/

noncomputable section

namespace MassGap.CoverCompact

open MassGap.TorusDoubling MassGap.HolderBondMoving MassGap.CubeFlux MassGap.GapSideTwistFlat
open scoped Real

/-! ## 1. Additive forms on the torus -/

section Forms

variable {A : Type} [AddCommGroup A] {d L : ℕ}

/-- **The additive cube sum** of a face function, the additive form of `CubeFlux.cubeFlux`. -/
def cubeSum (F : TPlaq d L → A) (i j k : Fin d) (x : TSite d L) : A :=
  F ((i, j), x) + F ((j, k), x) + F ((k, i), x) -
    (F ((i, j), tshift k x) + F ((j, k), tshift i x) + F ((k, i), tshift j x))

/-- **The curl** of a link field, the additive plaquette word of `HolderBondMoving.thol`. -/
def curl (θ : TLink d L → A) (q : TPlaq d L) : A :=
  θ (q.1.1, q.2) + θ (q.1.2, tshift q.1.1 q.2) - θ (q.1.1, tshift q.1.2 q.2) - θ (q.1.2, q.2)

/-- `d² = 0` on links: the cube sum of a curl vanishes. -/
theorem cubeSum_curl (θ : TLink d L → A) (i j k : Fin d) (x : TSite d L) :
    cubeSum (curl θ) i j k x = 0 := by
  unfold cubeSum curl
  simp only
  rw [tshift_comm i k x, tshift_comm j k x, tshift_comm j i x]
  abel

/-- `curl` is antisymmetric in the two directions. -/
theorem curl_swap (θ : TLink d L → A) (i j : Fin d) (x : TSite d L) :
    curl θ ((j, i), x) = - curl θ ((i, j), x) := by
  unfold curl
  simp only
  abel

/-- **`d² = 0` on faces: every antisymmetric face function has a conserved cube sum.** The oriented
sum of the cube sums over the eight cubes of a hypercube vanishes, in every abelian group, with no
relation to any gauge field. -/
theorem hyper_cubeSum (F : TPlaq d L → A) (hF : ∀ a b x, F ((b, a), x) = - F ((a, b), x))
    (i j k l : Fin d) (x : TSite d L) :
    (cubeSum F j k l (tshift i x) - cubeSum F j k l x)
      - (cubeSum F i k l (tshift j x) - cubeSum F i k l x)
      + (cubeSum F i j l (tshift k x) - cubeSum F i j l x)
      - (cubeSum F i j k (tshift l x) - cubeSum F i j k x) = 0 := by
  unfold cubeSum
  rw [tshift_comm j i x, tshift_comm k i x, tshift_comm l i x, tshift_comm k j x,
    tshift_comm l j x, tshift_comm l k x]
  simp only [hF j l, hF i l, hF i k]
  abel

end Forms

/-! ## 2. The `U(1)` structure -/

section Circle

variable {d L : ℕ}

theorem thol_exp (θ : TLink d L → ℝ) (q : TPlaq d L) :
    thol q (fun l => Circle.exp (θ l)) = Circle.exp (curl θ q) := by
  unfold thol curl
  rw [sub_eq_add_neg, sub_eq_add_neg, Circle.exp_add, Circle.exp_add, Circle.exp_add,
    Circle.exp_neg, Circle.exp_neg]

/-- Every `U(1)` link field has a real lift. -/
theorem exists_link_lift (U : TLink d L → Circle) :
    ∃ θ : TLink d L → ℝ, ∀ l, Circle.exp (θ l) = U l :=
  ⟨fun l => Complex.arg (U l), fun l => Circle.exp_arg (U l)⟩

/-- **A plaquette angle**: a real function with `exp(i a) = thol`, antisymmetric in the directions. -/
def IsAngle (U : TLink d L → Circle) (a : TPlaq d L → ℝ) : Prop :=
  (∀ q, Circle.exp (a q) = thol q U) ∧ ∀ i j x, a ((j, i), x) = - a ((i, j), x)

theorem thol_swap {G : Type} [Group G] (U : TLink d L → G) (i j : Fin d) (x : TSite d L) :
    thol ((j, i), x) U = (thol ((i, j), x) U)⁻¹ := by
  unfold thol
  simp only
  group

theorem thol_diag {G : Type} [Group G] (U : TLink d L → G) (i : Fin d) (x : TSite d L) :
    thol ((i, i), x) U = 1 := by
  unfold thol
  simp only
  group

/-- A plaquette angle exists: the principal argument on `i < j`, its negative on `i > j`. -/
theorem exists_angle (U : TLink d L → Circle) : ∃ a, IsAngle U a := by
  classical
  refine ⟨fun q => if q.1.1 < q.1.2 then Complex.arg ((thol q U : Circle) : ℂ)
    else if q.1.2 < q.1.1 then - Complex.arg ((thol ((q.1.2, q.1.1), q.2) U : Circle) : ℂ) else 0,
    ?_, ?_⟩
  · rintro ⟨⟨i, j⟩, x⟩
    simp only
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, Circle.exp_arg]
    · subst h
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), Circle.exp_zero, thol_diag]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, Circle.exp_neg, Circle.exp_arg, thol_swap U j i x]
  · intro i j x
    simp only
    rcases lt_trichotomy i j with h | h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_pos h]
    · subst h
      simp
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_pos h, neg_neg]

/-- **The split**: for a lift `θ` and an angle `a`, `a = dθ + 2π n` with `n` integer. -/
theorem exists_split {U : TLink d L → Circle} {θ : TLink d L → ℝ} {a : TPlaq d L → ℝ}
    (hθ : ∀ l, Circle.exp (θ l) = U l) (ha : IsAngle U a) :
    ∃ n : TPlaq d L → ℤ, (∀ q, a q = curl θ q + n q * (2 * π)) ∧
      ∀ i j x, n ((j, i), x) = - n ((i, j), x) := by
  have hU : U = fun l => Circle.exp (θ l) := funext fun l => (hθ l).symm
  have h : ∀ q, ∃ m : ℤ, a q = curl θ q + m * (2 * π) := by
    intro q
    refine Circle.exp_eq_exp.mp ?_
    rw [ha.1 q, hU, thol_exp]
  choose n hn using h
  refine ⟨n, hn, fun i j x => ?_⟩
  have h1 := hn ((j, i), x)
  have h2 := hn ((i, j), x)
  rw [ha.2 i j x, curl_swap] at h1
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have h3 : ((n ((j, i), x) : ℝ) + n ((i, j), x)) * (2 * π) = 0 := by linarith
  have h4 : (n ((j, i), x) : ℝ) + n ((i, j), x) = 0 :=
    (mul_eq_zero.mp h3).resolve_right hpi
  have h5 : n ((j, i), x) + n ((i, j), x) = 0 := by exact_mod_cast h4
  omega

/-- **The integer cube charge is read off the angle**: `cubeSum a = 2π · cubeSum n`. -/
theorem cubeSum_angle {θ : TLink d L → ℝ} {a : TPlaq d L → ℝ} {n : TPlaq d L → ℤ}
    (hn : ∀ q, a q = curl θ q + n q * (2 * π)) (i j k : Fin d) (x : TSite d L) :
    cubeSum a i j k x = (cubeSum n i j k x : ℤ) * (2 * π) := by
  have h := cubeSum_curl θ i j k x
  unfold cubeSum at h ⊢
  simp only [hn]
  push_cast
  linear_combination h

/-- **The charge does not depend on the lift.** -/
theorem charge_indep {θ θ' : TLink d L → ℝ} {a : TPlaq d L → ℝ} {n n' : TPlaq d L → ℤ}
    (hn : ∀ q, a q = curl θ q + n q * (2 * π)) (hn' : ∀ q, a q = curl θ' q + n' q * (2 * π))
    (i j k : Fin d) (x : TSite d L) : cubeSum n i j k x = cubeSum n' i j k x := by
  have h := cubeSum_angle hn i j k x
  rw [cubeSum_angle hn' i j k x] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  exact_mod_cast (mul_right_cancel₀ hpi h).symm

/-- **Small faces carry no charge**: if the six faces of a cube have `|a| < π/3` its charge is `0`.
DERIVED: `π/3 = 2π/6`, the charge quantum over the six faces. -/
theorem charge_zero_of_small {θ : TLink d L → ℝ} {a : TPlaq d L → ℝ} {n : TPlaq d L → ℤ}
    (hn : ∀ q, a q = curl θ q + n q * (2 * π)) (i j k : Fin d) (x : TSite d L)
    (h1 : |a ((i, j), x)| < π / 3) (h2 : |a ((j, k), x)| < π / 3) (h3 : |a ((k, i), x)| < π / 3)
    (h4 : |a ((i, j), tshift k x)| < π / 3) (h5 : |a ((j, k), tshift i x)| < π / 3)
    (h6 : |a ((k, i), tshift j x)| < π / 3) : cubeSum n i j k x = 0 := by
  have h := cubeSum_angle hn i j k x
  have hpi := Real.pi_pos
  have hb : |((cubeSum n i j k x : ℤ) : ℝ)| * (2 * π) < 1 * (2 * π) := by
    rw [one_mul]
    have e : |((cubeSum n i j k x : ℤ) : ℝ)| * (2 * π) = |cubeSum a i j k x| := by
      rw [h, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [e]
    unfold cubeSum
    rw [abs_lt] at h1 h2 h3 h4 h5 h6 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
  have hlt : |((cubeSum n i j k x : ℤ) : ℝ)| < 1 := lt_of_mul_lt_mul_right hb (by positivity)
  have : |cubeSum n i j k x| < 1 := by exact_mod_cast hlt
  exact Int.abs_lt_one_iff.mp this

/-- **The lifted field**: a real link field lifting `U` whose curl is the plaquette angle itself. -/
def Liftable (U : TLink d L → Circle) (a : TPlaq d L → ℝ) : Prop :=
  ∃ θ : TLink d L → ℝ, (∀ l, Circle.exp (θ l) = U l) ∧ curl θ = a

theorem curl_add_mul (θ : TLink d L → ℝ) (k : TLink d L → ℤ) (c : ℝ) (q : TPlaq d L) :
    curl (fun l => θ l + k l * c) q = curl θ q + (curl k q : ℤ) * c := by
  unfold curl
  push_cast
  ring

/-- **The lift criterion**: the lifted field exists exactly when the integer form `n` of a split is
the curl of an integer link field. -/
theorem liftable_iff {U : TLink d L → Circle} {θ₀ : TLink d L → ℝ} {a : TPlaq d L → ℝ}
    {n : TPlaq d L → ℤ} (hθ : ∀ l, Circle.exp (θ₀ l) = U l)
    (hn : ∀ q, a q = curl θ₀ q + n q * (2 * π)) :
    Liftable U a ↔ ∃ k : TLink d L → ℤ, n = curl k := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨θ, h1, h2⟩
    have h : ∀ l, ∃ m : ℤ, θ l = θ₀ l + m * (2 * π) := fun l =>
      Circle.exp_eq_exp.mp (by rw [h1 l, hθ l])
    choose k hk using h
    refine ⟨k, funext fun q => ?_⟩
    have e : θ = fun l => θ₀ l + k l * (2 * π) := funext hk
    have h3 := congrFun h2 q
    rw [e, curl_add_mul, hn q] at h3
    have h4 : (curl θ₀ q + (curl k q : ℤ) * (2 * π) : ℝ) - curl θ₀ q
        = (curl θ₀ q + n q * (2 * π)) - curl θ₀ q := by rw [h3]
    rw [add_sub_cancel_left, add_sub_cancel_left] at h4
    exact_mod_cast (mul_right_cancel₀ hpi h4).symm
  · rintro ⟨k, rfl⟩
    refine ⟨fun l => θ₀ l + k l * (2 * π), fun l => ?_, funext fun q => ?_⟩
    · rw [← hθ l]
      exact Circle.exp_eq_exp.mpr ⟨k l, rfl⟩
    · rw [curl_add_mul, hn q]

/-- A liftable field has no cube charge. -/
theorem charge_zero_of_liftable {U : TLink d L → Circle} {a : TPlaq d L → ℝ}
    (h : Liftable U a) (i j k : Fin d) (x : TSite d L) : cubeSum a i j k x = 0 := by
  obtain ⟨θ, -, rfl⟩ := h
  exact cubeSum_curl θ i j k x

/-- **Real Stokes on a 2-torus slice.** -/
theorem sum_curl_slice {i j : Fin d} (hij : i ≠ j) (x : TSite d L) (θ : TLink d L → ℝ) :
    ∑ s, ∑ t, curl θ ((i, j), slicePt i j x s t) = 0 := by
  set a : Fin L → Fin L → ℝ := fun s t => θ (i, slicePt i j x s t)
  set b : Fin L → Fin L → ℝ := fun s t => θ (j, slicePt i j x s t)
  have hq : ∀ s t, curl θ ((i, j), slicePt i j x s t)
      = a s t + b (finRotate L s) t - a s (finRotate L t) - b s t := by
    intro s t
    unfold curl
    simp only [a, b]
    rw [tshift_slicePt_i hij, tshift_slicePt_j]
  have h1 : ∑ s, ∑ t, b (finRotate L s) t = ∑ s, ∑ t, b s t :=
    Equiv.sum_comp (finRotate L) (fun s => ∑ t, b s t)
  have h2 : ∑ s, ∑ t, a s (finRotate L t) = ∑ s, ∑ t, a s t :=
    Finset.sum_congr rfl fun s _ => Equiv.sum_comp (finRotate L) (fun t => a s t)
  simp only [hq, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

/-- A liftable field has no slice flux. -/
theorem flux_zero_of_liftable {U : TLink d L → Circle} {a : TPlaq d L → ℝ} (h : Liftable U a)
    {i j : Fin d} (hij : i ≠ j) (x : TSite d L) : ∑ s, ∑ t, a ((i, j), slicePt i j x s t) = 0 := by
  obtain ⟨θ, -, rfl⟩ := h
  exact sum_curl_slice hij x θ

/-- **Holonomies are no obstruction**: a constant field lifts with curl `0`, whatever its holonomy. -/
theorem liftable_const (φ : Fin d → ℝ) :
    Liftable (fun l : TLink d L => Circle.exp (φ l.1)) 0 := by
  refine ⟨fun l => φ l.1, fun _ => rfl, funext fun q => ?_⟩
  unfold curl
  simp

/-- The `CHOSEN` link angles of the witness on the side-`2` two-torus. -/
def wθ (l : TLink 2 2) : ℝ :=
  if l.1 = 0 then (if l.2 1 = 0 then π / 2 else 0)
  else (if l.2 1 = 1 ∧ l.2 0 = 1 then π else 0)

/-- The `CHOSEN` plaquette angle of the witness: `π/2` on `(0, 1)`, `−π/2` on `(1, 0)`. -/
def wa (q : TPlaq 2 2) : ℝ :=
  if q.1.1 = q.1.2 then 0 else if q.1.1 = 0 then π / 2 else - (π / 2)

theorem finRotate_two_zero : finRotate 2 0 = 1 := by decide
theorem finRotate_two_one : finRotate 2 1 = 0 := by decide

theorem wa_isAngle : IsAngle (fun l => Circle.exp (wθ l)) wa := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, x⟩
    rw [thol_exp]
    refine Circle.exp_eq_exp.mpr ?_
    have hx0 : x 0 = 0 ∨ x 0 = 1 := by
      generalize x 0 = v; revert v; decide
    have hx1 : x 1 = 0 ∨ x 1 = 1 := by
      generalize x 1 = v; revert v; decide
    fin_cases i <;> fin_cases j <;>
      rcases hx0 with h0 | h0 <;> rcases hx1 with h1 | h1
    all_goals
      simp [wa, wθ, curl, tshift, Function.update, h0, h1, finRotate_two_zero, finRotate_two_one]
    all_goals first
      | (refine ⟨0, ?_⟩; push_cast; ring1)
      | (refine ⟨1, ?_⟩; push_cast; ring1)
      | (refine ⟨-1, ?_⟩; push_cast; ring1)
  · intro i j x
    fin_cases i <;> fin_cases j <;> simp [wa]

/-- **Vanishing cube charges do not give the lift.** The field `exp(i wθ)` on the side-`2` torus has
plaquette angle `wa`, every cube sum of `wa` is `0`, its slice flux is `2π`, and it does not lift. -/
theorem flux_witness :
    (∀ i j k x, cubeSum wa i j k x = 0) ∧
      ¬ Liftable (fun l => Circle.exp (wθ l)) wa := by
  refine ⟨fun i j k x => ?_, fun h => ?_⟩
  · unfold cubeSum wa
    simp
  · have h0 := flux_zero_of_liftable h (i := 0) (j := 1) (by decide) (fun _ => 0)
    simp only [wa, Fin.sum_univ_two] at h0
    have hpi := Real.pi_pos
    norm_num at h0

/-- A continuous `ℤ`-valued function on the configurations of a connected group is constant. In
particular at `Circle`, where the charge of a defect exists: the monopole charge is discontinuous, and
no continuity statement about integers separates the groups. -/
theorem continuous_int_const {G : Type} [TopologicalSpace G] [ConnectedSpace G]
    (f : (TLink d L → G) → ℤ) (hf : Continuous f) (U V : TLink d L → G) : f U = f V :=
  PreconnectedSpace.constant inferInstance hf

end Circle

/-! ## 3. A conserved plaquette charge is a character -/

section Conserved

variable {G A : Type} [Group G] [AddCommGroup A] {d L : ℕ}

/-- The `CHOSEN` corner configuration: `a`, `b`, `c` on the three links out of `x`, `1` elsewhere. -/
def corner (i j k : Fin d) (x : TSite d L) (a b c : G) (l : TLink d L) : G :=
  if l = (i, x) then a else if l = (j, x) then b else if l = (k, x) then c else 1

theorem corner_off (i j k : Fin d) (x : TSite d L) (a b c : G) (e : Fin d) {y : TSite d L}
    (h : y ≠ x) : corner i j k x a b c (e, y) = 1 := by
  unfold corner
  simp [h]

theorem shift_ne (hL : 2 ≤ L) (a : Fin d) (x : TSite d L) : tshift a x ≠ x :=
  site_ne a (by rw [tshift_self']; exact finRotate_ne_self hL _)

theorem shift2_ne (hL : 2 ≤ L) {a b : Fin d} (h : a ≠ b) (x : TSite d L) :
    tshift a (tshift b x) ≠ x :=
  site_ne b (by rw [tshift_apply_ne (Ne.symm h), tshift_self']; exact finRotate_ne_self hL _)

/-- The corner relation forced by exact conservation. -/
theorem corner_relation (Q : G → A) (hL : 2 ≤ L) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k)
    (hki : k ≠ i) (x : TSite d L)
    (h : ∀ U : TLink d L → G, cubeSum (fun q => Q (thol q U)) i j k x = 0) (a b c : G) :
    Q (a * b⁻¹) + Q (b * c⁻¹) + Q (c * a⁻¹) = Q 1 + Q 1 + Q 1 := by
  have h0 := h (corner i j k x a b c)
  have ci : corner i j k x a b c (i, x) = a := by simp [corner]
  have cj : corner i j k x a b c (j, x) = b := by simp [corner, hij.symm]
  have ck : corner i j k x a b c (k, x) = c := by simp [corner, hki, hjk.symm]
  have off : ∀ (e : Fin d) (y : TSite d L), y ≠ x → corner i j k x a b c (e, y) = 1 :=
    fun e y hy => corner_off i j k x a b c e hy
  have si := shift_ne hL i x
  have sj := shift_ne hL j x
  have sk := shift_ne hL k x
  have s1 := shift2_ne hL (a := i) (b := k) hki.symm x
  have s2 := shift2_ne hL (a := j) (b := k) hjk x
  have s3 := shift2_ne hL (a := j) (b := i) hij.symm x
  have s4 := shift2_ne hL (a := k) (b := i) hki x
  have s5 := shift2_ne hL (a := k) (b := j) hjk.symm x
  have s6 := shift2_ne hL (a := i) (b := j) hij x
  unfold cubeSum thol at h0
  simp only [ci, cj, ck, off _ _ si, off _ _ sj, off _ _ sk, off _ _ s1, off _ _ s2, off _ _ s3,
    off _ _ s4, off _ _ s5, off _ _ s6, inv_one, mul_one, one_mul] at h0
  exact sub_eq_zero.mp h0

/-- **Exact conservation of a plaquette charge is exactly the character law.** For `Q : G → A`, `A`
abelian, on a side `≥ 2` and three distinct directions: the plain cube sum of `Q ∘ thol` vanishes at
every configuration if and only if `Q(gh) + Q(1) = Q(g) + Q(h)`, that is, `Q − Q(1)` is a homomorphism. -/
theorem conserved_iff_affine (Q : G → A) (hL : 2 ≤ L) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k)
    (hki : k ≠ i) (x : TSite d L) :
    (∀ U : TLink d L → G, cubeSum (fun q => Q (thol q U)) i j k x = 0) ↔
      ∀ g h : G, Q (g * h) + Q 1 = Q g + Q h := by
  constructor
  · intro hc g h
    have e1 := corner_relation Q hL hij hjk hki x hc (g * h) h 1
    have e2 := corner_relation Q hL hij hjk hki x hc 1 (g * h)⁻¹ 1
    simp only [inv_one, mul_one, inv_inv, one_mul, mul_inv_cancel_right] at e1 e2
    have e4 : Q (g * h) + Q (g * h)⁻¹ = Q 1 + Q 1 := by
      have := e2
      have h1 : Q (g * h) + Q (g * h)⁻¹ + Q 1 = Q 1 + Q 1 + Q 1 := this
      exact add_right_cancel h1
    have e5 : Q g + Q h + Q (g * h)⁻¹ = Q 1 + Q 1 + Q 1 := e1
    have e6 : Q (g * h) + Q 1 - (Q g + Q h) = 0 := by
      have : Q (g * h) + Q 1 - (Q g + Q h)
          = (Q (g * h) + Q (g * h)⁻¹ - (Q 1 + Q 1)) - (Q g + Q h + Q (g * h)⁻¹ - (Q 1 + Q 1 + Q 1)) := by
        abel
      rw [this, e4, e5]
      abel
    exact sub_eq_zero.mp e6
  · intro hQ U
    set χ : G → A := fun g => Q g - Q 1 with hχdef
    have hχ : ∀ g h, χ (g * h) = χ g + χ h := by
      intro g h
      have := hQ g h
      simp only [hχdef]
      have e : Q (g * h) = Q g + Q h - Q 1 := eq_sub_of_add_eq this
      rw [e]
      abel
    have hone : χ 1 = 0 := by simp [hχdef]
    have hinv : ∀ g, χ g⁻¹ = - χ g := by
      intro g
      have := hχ g⁻¹ g
      rw [inv_mul_cancel, hone] at this
      exact eq_neg_of_add_eq_zero_left this.symm
    have hconj : ∀ u f, χ (u * f * u⁻¹) = χ f := by
      intro u f
      rw [hχ, hχ, hinv]
      abel
    have T := congrArg χ (bianchi_transported i j k x U)
    rw [hone] at T
    rw [hχ, hχ, hχ, hχ, hχ, hinv, hinv, hinv, hconj, hconj, hconj] at T
    unfold cubeSum
    simp only [hχdef] at T
    have e : Q (thol ((i, j), x) U) + Q (thol ((j, k), x) U) + Q (thol ((k, i), x) U) -
        (Q (thol ((i, j), tshift k x) U) + Q (thol ((j, k), tshift i x) U) +
          Q (thol ((k, i), tshift j x) U)) =
        Q (thol ((i, j), x) U) - Q 1 + -(Q (thol ((k, i), tshift j x) U) - Q 1) +
          (Q (thol ((j, k), x) U) - Q 1) + -(Q (thol ((i, j), tshift k x) U) - Q 1) +
          (Q (thol ((k, i), x) U) - Q 1) + -(Q (thol ((j, k), tshift i x) U) - Q 1) := by
      abel
    rw [e, T]

end Conserved

/-! ## 4. Perfect groups -/

section Perfect

open Matrix MassGap.SUN MassGap.GaugeInstances

/-- Every homomorphism from a perfect group to a commutative group is trivial. No continuity. -/
theorem hom_eq_one_of_perfect {G A : Type} [Group G] [Group.IsPerfect G] [CommGroup A]
    (χ : G →* A) : χ = 1 := by
  have h : commutator G ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  ext g
  have hg : g ∈ commutator G := Group.IsPerfect.mem_commutator
  exact h hg

/-- **A conserved plaquette charge of a perfect group is constant.** -/
theorem conserved_const_of_perfect {G A : Type} [Group G] [Group.IsPerfect G] [AddCommGroup A]
    {d L : ℕ} (Q : G → A) (hL : 2 ≤ L) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (x : TSite d L) (h : ∀ U : TLink d L → G, cubeSum (fun q => Q (thol q U)) i j k x = 0) (g : G) :
    Q g = Q 1 := by
  have ha := (conserved_iff_affine Q hL hij hjk hki x).mp h
  let χ : G →* Multiplicative A :=
    { toFun := fun g => Multiplicative.ofAdd (Q g - Q 1)
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← ofAdd_add]
        congr 1
        have := ha a b
        have e : Q (a * b) = Q a + Q b - Q 1 := eq_sub_of_add_eq this
        rw [e]
        abel }
  have h1 : χ g = 1 := by rw [hom_eq_one_of_perfect χ]; rfl
  have h2 : Q g - Q 1 = 0 := Multiplicative.ofAdd.injective (by simpa [χ] using h1)
  exact sub_eq_zero.mp h2

/-- **Every element is one commutator.** -/
def EveryCommutator (G : Type) [Group G] : Prop := ∀ g : G, ∃ a b : G, a * b * a⁻¹ * b⁻¹ = g

theorem isPerfect_of_every {G : Type} [Group G] (h : EveryCommutator G) : Group.IsPerfect G := by
  refine ⟨eq_top_iff.mpr fun g _ => ?_⟩
  obtain ⟨a, b, rfl⟩ := h g
  have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [commutatorElement_def] at this
  exact this

/-- `U(1)` has its identity character, so it is not perfect. -/
theorem circle_not_perfect : ¬ Group.IsPerfect Circle := by
  intro h
  have h1 := hom_eq_one_of_perfect (MonoidHom.id Circle)
  have h3 : Circle.exp 1 = 1 := congrArg (fun χ : Circle →* Circle => χ (Circle.exp 1)) h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h3
  have hpi := Real.pi_gt_three
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
  have h1' : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : n ≠ 0 := by exact_mod_cast hn0
    exact_mod_cast Int.one_le_abs this
  have h4 : |(n : ℝ) * (2 * π)| = |(n : ℝ)| * (2 * π) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [← hn, abs_one] at h4
  nlinarith

/-! ### Diagonalizing a unitary matrix -/

variable {N : ℕ}

/-- Square complex matrices of size `N`. -/
abbrev Mat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ

/-- A complex number of modulus one off the roots of the characteristic polynomial. -/
theorem exists_unit_regular (U : Mat N) : ∃ l : ℂ, star l * l = 1 ∧ (scalar (Fin N) l - U).det ≠ 0 := by
  have hp : U.charpoly ≠ 0 := (Matrix.charpoly_monic U).ne_zero
  have hinf : (((↑) : Circle → ℂ) ∘ Circle.exp '' Set.Icc 0 1).Infinite := by
    refine (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image ?_
    intro a ha b hb hab
    have h1 : Circle.exp a = Circle.exp b := Circle.ext hab
    refine Circle.exp_injOn_Icc (a := 0) (b := 1) ?_ ha hb h1
    have := Real.pi_gt_three
    linarith
  obtain ⟨l, hl, hl2⟩ := hinf.exists_notMem_finset U.charpoly.roots.toFinset
  obtain ⟨t, -, rfl⟩ := hl
  refine ⟨((Circle.exp t : Circle) : ℂ), ?_, ?_⟩
  · simp only [Complex.star_def]
    rw [Complex.conj_mul', Circle.norm_coe]
    norm_num
  · intro h0
    apply hl2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def, Matrix.eval_charpoly]
    exact h0

/-- **A unitary matrix is unitarily diagonal**, by the Cayley transform and the Hermitian spectral
theorem. -/
theorem exists_diag {U : Mat N} (hU : U ∈ unitaryGroup (Fin N) ℂ) :
    ∃ W : Mat N, W ∈ unitaryGroup (Fin N) ℂ ∧ ∃ d : Fin N → ℂ, U = W * diagonal d * star W := by
  obtain ⟨l, hl, hdet⟩ := exists_unit_regular U
  have hl' : l * star l = 1 := by rw [mul_comm]; exact hl
  have hU1 : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hU2 : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have hsc : scalar (Fin N) l = l • (1 : Mat N) := by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply, Matrix.scalar_apply]
  rw [hsc] at hdet
  set A : Mat N := l • (1 : Mat N) - U with hA
  set S : Mat N := l • (1 : Mat N) + U with hS
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAu
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAu
  set H : Mat N := Complex.I • (S * A⁻¹) with hH
  have hSA : S * A = A * S := by
    simp only [hS, hA, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  have hHA : H * A = Complex.I • S := by
    rw [hH, Matrix.smul_mul, Matrix.mul_assoc, hAA', Matrix.mul_one]
  have hAH : A * H = Complex.I • S := by
    rw [hH, Matrix.mul_smul, ← Matrix.mul_assoc, ← hSA, Matrix.mul_assoc, hAA, Matrix.mul_one]
  have hstarA : star A = (-star l) • (star U * A) := by
    simp only [hA, star_sub, star_smul, star_one, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      hU1, smul_sub, smul_smul]
    rw [neg_mul, hl, neg_smul, neg_smul, one_smul]
    abel
  have hstarS : star S = (star l) • (star U * S) := by
    simp only [hS, star_add, star_smul, star_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      hU1, smul_add, smul_smul]
    rw [hl, one_smul]
    abel
  set X : Mat N := star H with hX
  have h1 : star A * X = (-Complex.I) • star S := by
    have e := congrArg star hHA
    rw [star_mul, star_smul Complex.I S, Complex.star_def, Complex.conj_I] at e
    exact e
  have hAX : A * X = Complex.I • S := by
    have e1 : U * star A = (-star l) • A := by
      rw [hstarA, Matrix.mul_smul, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
    have e2 : U * star S = (star l) • S := by
      rw [hstarS, Matrix.mul_smul, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
    have e3 : (-star l) • (A * X) = (-Complex.I) • ((star l) • S) := by
      rw [← Matrix.smul_mul, ← e1, Matrix.mul_assoc, h1, Matrix.mul_smul, e2]
    have e4 : (-l) • ((-star l) • (A * X)) = (-l) • ((-Complex.I) • ((star l) • S)) := by rw [e3]
    have e5 : (-l) • ((-star l) • (A * X)) = (l * star l) • (A * X) := by module
    have e6 : (-l) • ((-Complex.I) • ((star l) • S)) = (Complex.I * (l * star l)) • S := by module
    rw [e5, e6, hl', one_smul, mul_one] at e4
    exact e4
  have hXH : X = H := by
    have : A * X = A * H := by rw [hAX, hAH]
    have h2 := congrArg (fun M => A⁻¹ * M) this
    simpa only [← Matrix.mul_assoc, hAA', Matrix.one_mul] using h2
  have hHerm : H.IsHermitian := by
    show H.conjTranspose = H
    rw [← Matrix.star_eq_conjTranspose]
    exact hXH
  set W : Mat N := (hHerm.eigenvectorUnitary : Mat N) with hW
  have hWm : W ∈ unitaryGroup (Fin N) ℂ := hHerm.eigenvectorUnitary.2
  have hW1 : star W * W = 1 := mem_unitaryGroup_iff'.mp hWm
  have hW2 : W * star W = 1 := mem_unitaryGroup_iff.mp hWm
  set r : Fin N → ℂ := fun i => ((hHerm.eigenvalues i : ℝ) : ℂ) with hr
  have hspec : H = W * diagonal r * star W := by
    have := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hD : star W * H * W = diagonal r := by
    rw [hspec]
    calc star W * (W * diagonal r * star W) * W
        = (star W * W) * diagonal r * (star W * W) := by noncomm_ring
      _ = diagonal r := by rw [hW1, Matrix.one_mul, Matrix.mul_one]
  have hkey : (H + Complex.I • (1 : Mat N)) * U = l • (H - Complex.I • (1 : Mat N)) := by
    have h3 : H * (l • (1 : Mat N) - U) = Complex.I • (l • (1 : Mat N) + U) := hHA
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul] at h3
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul]
    have h4 : l • H = Complex.I • U + H * U + (Complex.I * l) • (1 : Mat N) := by
      rw [sub_eq_iff_eq_add] at h3
      rw [h3]
      abel
    rw [h4, mul_comm l Complex.I]
    abel
  set T : Mat N := star W * U * W with hT
  have hTU : U = W * T * star W := by
    rw [hT]
    calc U = (W * star W) * U * (W * star W) := by rw [hW2, Matrix.one_mul, Matrix.mul_one]
      _ = W * (star W * U * W) * star W := by noncomm_ring
  have hrne : ∀ a, r a + Complex.I ≠ 0 := by
    intro a h
    have := congrArg Complex.im h
    simp [hr] at this
  have hDp : star W * (H + Complex.I • (1 : Mat N)) * W = diagonal fun a => r a + Complex.I := by
    rw [Matrix.mul_add, Matrix.add_mul, hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW1]
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  have hDm : star W * (H - Complex.I • (1 : Mat N)) * W = diagonal fun a => r a - Complex.I := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hW1]
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  have hTeq : (diagonal fun a => r a + Complex.I) * T = l • diagonal fun a => r a - Complex.I := by
    rw [← hDp, ← hDm, hT]
    calc star W * (H + Complex.I • (1 : Mat N)) * W * (star W * U * W)
        = star W * (H + Complex.I • (1 : Mat N)) * (W * star W) * U * W := by noncomm_ring
      _ = star W * ((H + Complex.I • (1 : Mat N)) * U) * W := by
          rw [hW2, Matrix.mul_one, Matrix.mul_assoc (star W)]
      _ = l • (star W * (H - Complex.I • (1 : Mat N)) * W) := by
          rw [hkey, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨W, hWm, fun a => l * (r a - Complex.I) / (r a + Complex.I), ?_⟩
  have hTd : T = diagonal fun a => l * (r a - Complex.I) / (r a + Complex.I) := by
    ext a b
    have h5 := congrFun (congrFun hTeq a) b
    rw [Matrix.diagonal_mul, Matrix.smul_apply] at h5
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq, smul_eq_mul] at h5 ⊢
      rw [eq_div_iff (hrne a), mul_comm]
      exact h5
    · simp only [Matrix.diagonal_apply_ne _ hab, smul_eq_mul, mul_zero] at h5 ⊢
      exact (mul_eq_zero.mp h5).resolve_left (hrne a)
  rw [hTU, hTd]

/-! ### Every element of `SU(N)` is a commutator -/

/-- Unit roots: a unit `z` has a unit `μ` with `μ^N z = 1`. -/
theorem exists_unit_root (hN : N ≠ 0) {z : ℂ} (hz : star z * z = 1) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ ^ N * z = 1 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq z⁻¹ (Nat.pos_of_ne_zero hN)
  refine ⟨μ, ?_, by rw [hμ, inv_mul_cancel₀ hz0]⟩
  have hz1 : ‖z‖ = 1 := by
    have h1 : ((‖z‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hz, Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    have h2 : ‖z‖ ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]
  have hm : ‖μ‖ ^ N = 1 := by rw [← norm_pow, hμ, norm_inv, hz1, inv_one]
  have hm1 : ‖μ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).mp hm
  rw [Complex.star_def, Complex.conj_mul', hm1]
  norm_num

theorem smul_mem_unitary {μ : ℂ} (hμ : star μ * μ = 1) {M : Mat N}
    (hM : M ∈ unitaryGroup (Fin N) ℂ) : μ • M ∈ unitaryGroup (Fin N) ℂ := by
  rw [mem_unitaryGroup_iff', star_smul, smul_mul_smul_comm, mem_unitaryGroup_iff'.mp hM, hμ, one_smul]

theorem diagonal_mem_unitary {c : Fin N → ℂ} (hc : ∀ i, star (c i) * c i = 1) :
    diagonal c ∈ unitaryGroup (Fin N) ℂ := by
  rw [mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hc i

theorem perm_mem_unitary (σ : Equiv.Perm (Fin N)) :
    σ.permMatrix ℂ ∈ unitaryGroup (Fin N) ℂ := by
  rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem perm_apply (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    σ.permMatrix ℂ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem perm_mul_diagonal (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ) :
    σ.permMatrix ℂ * diagonal c = diagonal (fun i => c (σ i)) * σ.permMatrix ℂ := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, perm_apply]
  by_cases h : σ i = j
  · simp [h]
  · simp [h]

theorem star_mul_prod_self {ι : Type} (S : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ S, star (f i) * f i = 1) :
    star (∏ i ∈ S, f i) * ∏ i ∈ S, f i = 1 := by
  rw [star_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one h

/-- The cyclic system `c(σ i) = d_i c_i` is solved by partial products, and `∏ d = 1` closes it. -/
theorem exists_cycle_solution (hN : N ≠ 0) {d : Fin N → ℂ} (hd : ∀ i, star (d i) * d i = 1)
    (hprod : ∏ i, d i = 1) :
    ∃ c : Fin N → ℂ, (∀ i, star (c i) * c i = 1) ∧ ∀ i, c (finRotate N i) = d i * c i := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  let D : ℕ → ℂ := fun k => if h : k < m + 1 then d ⟨k, h⟩ else 1
  have hD : ∀ k, star (D k) * D k = 1 := by
    intro k
    by_cases h : k < m + 1
    · have e : D k = d ⟨k, h⟩ := dif_pos h
      rw [e]; exact hd _
    · have e : D k = 1 := dif_neg h
      rw [e]; simp
  refine ⟨fun i => ∏ k ∈ Finset.range i.val, D k, fun i => ?_, fun i => ?_⟩
  · exact star_mul_prod_self _ _ fun k _ => hD k
  · obtain ⟨k, hk⟩ := i
    by_cases hlt : k < m
    · rw [finRotate_of_lt hlt]
      simp only
      rw [Finset.prod_range_succ, mul_comm]
      simp only [D, dif_pos hk]
    · have hkm : k = m := by omega
      subst hkm
      have hlast : (⟨k, hk⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [hlast, finRotate_last]
      simp only [Fin.val_zero, Finset.range_zero, Finset.prod_empty, Fin.val_last]
      have h1 : ∏ i, d i = ∏ j ∈ Finset.range (k + 1), D j := by
        rw [← Fin.prod_univ_eq_prod_range D (k + 1)]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [D, dif_pos j.2]
      rw [Finset.prod_range_succ, mul_comm] at h1
      rw [hprod] at h1
      have hl : D k = d (Fin.last k) := by
        simp only [D, dif_pos (Nat.lt_succ_self k)]
        rfl
      rw [hl] at h1
      exact h1

/-- A commutator read off one matrix relation. -/
theorem commutator_of_rel {G : Type} [Group G] {a b g : G} (h : a * b = g * b * a) :
    a * b * a⁻¹ * b⁻¹ = g := by
  rw [h]; group

/-- **A diagonal element of `SU(N)` is one commutator**: `D = [μ P, ν C]`. -/
theorem diag_commutator (hN : N ≠ 0) (D : SU N) {d : Fin N → ℂ}
    (hD : (D : Mat N) = diagonal d) (hd : ∀ i, star (d i) * d i = 1) :
    ∃ a b : SU N, a * b * a⁻¹ * b⁻¹ = D := by
  have hprod : ∏ i, d i = 1 := by
    have := (Matrix.mem_specialUnitaryGroup_iff.mp D.2).2
    rwa [hD, Matrix.det_diagonal] at this
  obtain ⟨c, hc, hcyc⟩ := exists_cycle_solution hN hd hprod
  set σ : Equiv.Perm (Fin N) := finRotate N with hσ
  set P : Mat N := σ.permMatrix ℂ with hP
  have hPu : P ∈ unitaryGroup (Fin N) ℂ := perm_mem_unitary σ
  have hs : star (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  obtain ⟨μ, hμ, hμ2⟩ := exists_unit_root hN hs
  have hCu : diagonal c ∈ unitaryGroup (Fin N) ℂ := diagonal_mem_unitary hc
  have hpc : star (∏ i, c i) * ∏ i, c i = 1 := star_mul_prod_self _ _ fun i _ => hc i
  obtain ⟨ν, hν, hν2⟩ := exists_unit_root hN hpc
  have ha : μ • P ∈ specialUnitaryGroup (Fin N) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨smul_mem_unitary hμ hPu, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin, hP, Matrix.det_permutation]
    exact_mod_cast hμ2
  have hb : ν • diagonal c ∈ specialUnitaryGroup (Fin N) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨smul_mem_unitary hν hCu, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_diagonal, hν2]
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, commutator_of_rel (Subtype.ext ?_)⟩
  show (μ • P) * (ν • diagonal c) = (D : Mat N) * (ν • diagonal c) * (μ • P)
  rw [hD]
  have e : P * diagonal c = diagonal d * diagonal c * P := by
    rw [hP, perm_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact hcyc i
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [e, mul_comm ν μ]

/-- A commutator is carried by conjugation. -/
theorem conj_commutator {G : Type} [Group G] {w D g : G} (hg : g * w = w * D)
    (h : ∃ a b : G, a * b * a⁻¹ * b⁻¹ = D) : ∃ a b : G, a * b * a⁻¹ * b⁻¹ = g := by
  obtain ⟨a, b, rfl⟩ := h
  refine ⟨w * a * w⁻¹, w * b * w⁻¹, ?_⟩
  have : g = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by rw [← hg]; group
  rw [this]
  group

/-- **Every element of `SU(N)` is one commutator**, at every `N`. -/
theorem su_everyCommutator : EveryCommutator (SU N) := by
  by_cases hN : N = 0
  · subst hN
    intro g
    refine ⟨1, 1, ?_⟩
    have : Subsingleton (SU 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    exact Subsingleton.elim _ _
  intro g
  obtain ⟨W, hW, d, hg⟩ := exists_diag (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have hW1 : star W * W = 1 := mem_unitaryGroup_iff'.mp hW
  have hW2 : W * star W = 1 := mem_unitaryGroup_iff.mp hW
  have hdetW : star W.det * W.det = 1 := by
    have := congrArg Matrix.det hW1
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at this
    exact this
  obtain ⟨ν, hν, hν2⟩ := exists_unit_root hN hdetW
  have hw : ν • W ∈ specialUnitaryGroup (Fin N) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨smul_mem_unitary hν hW, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin]
    exact hν2
  have hDd : diagonal d = star W * (g : Mat N) * W := by
    rw [hg]
    calc diagonal d = (star W * W) * diagonal d * (star W * W) := by
          rw [hW1, Matrix.one_mul, Matrix.mul_one]
      _ = star W * (W * diagonal d * star W) * W := by noncomm_ring
  have hDu : diagonal d ∈ unitaryGroup (Fin N) ℂ := by
    rw [hDd]
    refine mul_mem (mul_mem ?_ (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1) hW
    exact Unitary.star_mem hW
  have hdu : ∀ i, star (d i) * d i = 1 := by
    intro i
    have h1 := mem_unitaryGroup_iff'.mp hDu
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h1
    have h2 := congrFun (Matrix.diagonal_injective h1) i
    exact h2
  have hDs : diagonal d ∈ specialUnitaryGroup (Fin N) ℂ := by
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hDu, ?_⟩
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
    rw [hDd, Matrix.det_mul, Matrix.det_mul, h1, mul_one, Matrix.star_eq_conjTranspose,
      Matrix.det_conjTranspose]
    exact hdetW
  refine conj_commutator (w := ⟨_, hw⟩) (D := ⟨_, hDs⟩) (Subtype.ext ?_)
    (diag_commutator hN ⟨_, hDs⟩ rfl hdu)
  show (g : Mat N) * (ν • W) = (ν • W) * diagonal d
  rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_assoc, hW1, Matrix.mul_one]

instance isPerfect_SU : Group.IsPerfect (SU N) := isPerfect_of_every su_everyCommutator

/-- **No non-trivial character of `SU(N)`**, continuous or not, into any commutative group. -/
theorem su_no_character {A : Type} [CommGroup A] (χ : SU N →* A) : χ = 1 :=
  hom_eq_one_of_perfect χ

/-! ### Every element of `SO(3)` is a commutator -/

/-- The real `3 × 3` matrices. DERIVED: `3` the dimension of `SO(3)`'s matrices. -/
abbrev RM : Type := Matrix (Fin 3) (Fin 3) ℝ

/-- The rotation about `e₃` with cosine `c` and sine `s`. -/
def rz (c s : ℝ) : RM := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-- The rotation about `e₂` with cosine `c` and sine `s`. -/
def ry (c s : ℝ) : RM := !![c, 0, s; 0, 1, 0; -s, 0, c]

theorem so3_mem_of {M : RM} (h : M * M.transpose = 1) (hd : M.det = 1) :
    M ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, hd⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  exact h

theorem rz_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rz c s ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  refine so3_mem_of ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rz, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith
  · simp [rz, Matrix.det_fin_three]
    nlinarith

theorem ry_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : ry c s ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  refine so3_mem_of ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ry, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith
  · simp [ry, Matrix.det_fin_three]
    nlinarith

/-- The element of `SO(3)` with matrix `rz c s`. DERIVED: `3` the dimension of `SO(3)`'s matrices;
`2` the square. -/
def rzS (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : SO 3 := ⟨rz c s, rz_mem h⟩

/-- The half-turn about `e₂`. DERIVED: `−1` the cosine of the half-turn; `3` the
dimension of `SO(3)`'s matrices. -/
def halfTurn : SO 3 := ⟨ry (-1) 0, ry_mem (by norm_num)⟩

/-- **A rotation about `e₃` is one commutator**: `R(2φ) = [R(φ), H]`. -/
theorem rot_commutator {a c : ℝ} (h : a ^ 2 + c ^ 2 = 1) :
    ∃ x y : SO 3, x * y * x⁻¹ * y⁻¹ = rzS a c h := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (⟨a, c⟩ : ℂ) (n := 2) (by norm_num)
  set p := w.re with hp
  set q := w.im with hq
  have hre : p ^ 2 - q ^ 2 = a := by
    have := congrArg Complex.re hw
    simp only [pow_two, Complex.mul_re] at this
    nlinarith
  have him : 2 * p * q = c := by
    have := congrArg Complex.im hw
    simp only [pow_two, Complex.mul_im] at this
    nlinarith
  have hpq : p ^ 2 + q ^ 2 = 1 := by
    have h1 : (p ^ 2 + q ^ 2) ^ 2 = 1 := by
      rw [← h, ← hre, ← him]
      ring
    nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (p ^ 2 + q ^ 2 - 1)]
  refine ⟨rzS p q hpq, halfTurn, commutator_of_rel (Subtype.ext ?_)⟩
  show rz p q * ry (-1) 0 = rz a c * ry (-1) 0 * rz p q
  subst hre him
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rz, ry, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith

/-- **The frame**: every unit vector is the image of `e₃` under some element of `SO(3)`. -/
theorem exists_frame (w : Fin 3 → ℝ) (hw : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1) :
    ∃ V : SO 3, (V : RM) *ᵥ ![0, 0, 1] = w := by
  set ρ := Real.sqrt (w 0 ^ 2 + w 1 ^ 2) with hρ
  have hρ2 : ρ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨c, s, hcs, h0, h1⟩ : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * ρ = w 0 ∧ s * ρ = w 1 := by
    by_cases hz : ρ = 0
    · refine ⟨1, 0, by norm_num, ?_, ?_⟩
      · rw [hz] at hρ2 ⊢
        nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
      · rw [hz] at hρ2 ⊢
        nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    · refine ⟨w 0 / ρ, w 1 / ρ, ?_, by field_simp, by field_simp⟩
      field_simp
      linarith
  refine ⟨⟨rz c s * ry (w 2) ρ, mul_mem (rz_mem hcs) (ry_mem (by rw [hρ2]; linarith))⟩, ?_⟩
  funext i
  fin_cases i <;> simp [rz, ry, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linarith
  · linarith

/-- **An element of `SO(3)` has an axis.** -/
theorem exists_axis (g : SO 3) :
    ∃ w : Fin 3 → ℝ, w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 ∧ (g : RM) *ᵥ w = w := by
  set M : RM := g.1 with hM
  have hm := Matrix.mem_specialOrthogonalGroup_iff.mp g.2
  have hMM : M * M.transpose = 1 := by
    have e := hm.1
    rw [Matrix.mem_orthogonalGroup_iff] at e
    exact e
  have hdet : M.det = 1 := hm.2
  have h0 : (M - 1).det = 0 := by
    have e1 : M - 1 = M * (1 - M).transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, hMM]
    have e2 : (M - 1).det = (1 - M).det := by
      conv_lhs => rw [e1]
      rw [Matrix.det_mul, hdet, one_mul, Matrix.det_transpose]
    have e3 : (1 - M).det = - (M - 1).det := by
      rw [← neg_sub M 1, Matrix.det_neg]
      simp [Fintype.card_fin]
      norm_num
    linarith
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hfix : M *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv0
    exact hv0
  have hs : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    by_contra hn
    have h1 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h3 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    apply hv
    funext i
    fin_cases i <;> simp [h1, h2, h3]
  set t := (Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2))⁻¹ with ht
  have ht2 : t ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) = 1 := by
    rw [ht, inv_pow, Real.sq_sqrt hs.le]
    exact inv_mul_cancel₀ hs.ne'
  refine ⟨t • v, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  · rw [Matrix.mulVec_smul, hfix]

/-- The stabilizer of `e₃` in `SO(3)` is the rotations about `e₃`. -/
theorem stab_rot (T : SO 3) (hT : (T : RM) *ᵥ ![0, 0, 1] = ![0, 0, 1]) :
    ∃ (a c : ℝ) (h : a ^ 2 + c ^ 2 = 1), T = rzS a c h := by
  set M : RM := T.1 with hM
  have hm := Matrix.mem_specialOrthogonalGroup_iff.mp T.2
  have h1 : M * M.transpose = 1 := by
    have e := hm.1
    rw [Matrix.mem_orthogonalGroup_iff] at e
    exact e
  have h2 : M.transpose * M = 1 := mul_eq_one_comm.mp h1
  have hdet : M.det = 1 := hm.2
  have c0 : M 0 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hT 0
  have c1 : M 1 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hT 1
  have c2 : M 2 2 = 1 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hT 2
  have e22 : M 2 0 ^ 2 + M 2 1 ^ 2 + M 2 2 ^ 2 = 1 := by
    have := congrFun (congrFun h1 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    nlinarith
  have r0 : M 2 0 = 0 := by nlinarith [sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
  have r1 : M 2 1 = 0 := by nlinarith [sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
  have e00 : M 0 0 ^ 2 + M 1 0 ^ 2 = 1 := by
    have := congrFun (congrFun h2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, r0] at this
    nlinarith
  have e01 : M 0 0 * M 0 1 + M 1 0 * M 1 1 = 0 := by
    have := congrFun (congrFun h2 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, r0] at this
    nlinarith
  have e11 : M 0 1 ^ 2 + M 1 1 ^ 2 = 1 := by
    have := congrFun (congrFun h2 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, r1] at this
    nlinarith
  have ed : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := hdet
    rw [Matrix.det_fin_three, c0, c1, c2, r0, r1] at this
    linarith
  have d1 : M 1 1 = M 0 0 := by
    linear_combination (-M 1 1) * e00 + M 0 0 * ed + M 1 0 * e01
  have d2 : M 0 1 = - M 1 0 := by
    linear_combination (-M 0 1) * e00 + M 0 0 * e01 - M 1 0 * ed
  refine ⟨M 0 0, M 1 0, e00, Subtype.ext ?_⟩
  show M = rz (M 0 0) (M 1 0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rz, c0, c1, c2, r0, r1, d1, d2]

/-- **Every element of `SO(3)` is one commutator.** -/
theorem so3_everyCommutator : EveryCommutator (SO 3) := by
  intro g
  obtain ⟨w, hw, hfix⟩ := exists_axis g
  obtain ⟨V, hV⟩ := exists_frame w hw
  have hinv : ((V⁻¹ : SO 3) : RM) * (V : RM) = 1 := congrArg Subtype.val (inv_mul_cancel V)
  have hT : ((V⁻¹ * g * V : SO 3) : RM) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    show (((V⁻¹ : SO 3) : RM) * (g : RM) * (V : RM)) *ᵥ ![0, 0, 1] = ![0, 0, 1]
    rw [← Matrix.mulVec_mulVec, hV, ← Matrix.mulVec_mulVec, hfix, ← hV, Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec]
  obtain ⟨a, c, h, hrot⟩ := stab_rot _ hT
  refine conj_commutator (w := V) (D := rzS a c h) ?_ (rot_commutator h)
  rw [← hrot]
  group

/-- `SO(3)` is perfect: every element is one commutator. DERIVED: `3` the dimension of `SO(3)`'s
matrices. -/
instance isPerfect_SO3 : Group.IsPerfect (SO 3) := isPerfect_of_every so3_everyCommutator

/-! ### `G₂` at the level of the tree -/

/-- **`G₂`, given the cited perfection**: a conserved plaquette charge on `G₂` is constant. The
perfection of `G2Sub` is cited (Gotô), since the tree carries no connectedness of it. -/
theorem conserved_const_G2 [Group.IsPerfect GaugeG2.G2] {A : Type} [AddCommGroup A] {d L : ℕ}
    (Q : GaugeG2.G2 → A) (hL : 2 ≤ L) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (x : TSite d L)
    (h : ∀ U : TLink d L → GaugeG2.G2, cubeSum (fun q => Q (thol q U)) i j k x = 0) (g : GaugeG2.G2) :
    Q g = Q 1 :=
  conserved_const_of_perfect Q hL hij hjk hki x h g

/-! ### A finite perfect gauge group -/

/-- The alternating group on five letters. DERIVED: `5` the least `n` at which `A_n` is perfect. -/
abbrev A5 : Type := alternatingGroup (Fin 5)

instance isPerfect_A5 : Group.IsPerfect A5 :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

instance : TopologicalSpace A5 := ⊥
instance : DiscreteTopology A5 := ⟨rfl⟩
instance : MeasurableSpace A5 := ⊤
instance : BorelSpace A5 := ⟨by rw [borel_eq_top_of_discrete]; rfl⟩

/-- The permutation representation `A₅ → U(5)`. DERIVED: `5` the letters of `A₅`. -/
def a5Rep : A5 →* unitaryGroup (Fin 5) ℂ where
  toFun g := ⟨((g : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ, perm_mem_unitary _⟩
  map_one' := by
    apply Subtype.ext
    show (((1 : A5) : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    show (((g * h : A5) : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ =
      ((g : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ * ((h : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ
    rw [Subgroup.coe_mul, _root_.mul_inv_rev, Matrix.permMatrix_mul]

/-- **`A₅` is a lattice gauge group of the tree**: compact, Borel, second countable, with the
faithful permutation representation in `U(5)`. It is perfect (`isPerfect_A5`).
DERIVED: `5` the letters of `A₅`, the dimension of its permutation representation. -/
noncomputable instance instGaugeGroupA5 : GaugeGroup A5 where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 5
  repDim_pos := by norm_num
  rep := a5Rep
  continuous_rep := continuous_of_discreteTopology
  rep_injective := by
    intro g h hgh
    have h1 : ((g : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ = ((h : Equiv.Perm (Fin 5))⁻¹).permMatrix ℂ :=
      congrArg Subtype.val hgh
    have h2 : (g : Equiv.Perm (Fin 5))⁻¹ = (h : Equiv.Perm (Fin 5))⁻¹ := by
      ext i
      have := congrFun (congrFun h1 i) (((g : Equiv.Perm (Fin 5))⁻¹) i)
      rw [perm_apply, perm_apply, if_pos rfl] at this
      by_cases hc : ((h : Equiv.Perm (Fin 5))⁻¹) i = ((g : Equiv.Perm (Fin 5))⁻¹) i
      · rw [hc]
      · rw [if_neg hc] at this
        exact absurd this one_ne_zero
    exact Subtype.ext (inv_injective h2)

/-! ### Flat twist -/

variable {G : Type} [Group G] {d L : ℕ}

/-- **The oriented twist sheet**: `z` on the `(i, j)` plaquette at `x_i = x_j = 0`, `z⁻¹` on the
reversed one, `1` elsewhere. -/
def sheetO (i j : Fin d) (z : G) (q : TPlaq d L) : G :=
  if q.1 = (i, j) ∧ (q.2 i).val = 0 ∧ (q.2 j).val = 0 then z
  else if q.1 = (j, i) ∧ (q.2 i).val = 0 ∧ (q.2 j).val = 0 then z⁻¹ else 1

/-- **Absorption at zero action**: if `A B A⁻¹ B⁻¹ = z⁻¹`, the twist is flat on every plaquette. -/
theorem flat_twist {i j : Fin d} (hij : i ≠ j) {A B z : G} (hAB : A * B * A⁻¹ * B⁻¹ = z⁻¹)
    (q : TPlaq d L) : sheetO i j z q * thol q (flatCfg i j A B) = 1 := by
  have hBA : B * A * B⁻¹ * A⁻¹ = z := by
    have : (A * B * A⁻¹ * B⁻¹)⁻¹ = (z⁻¹)⁻¹ := congrArg _ hAB
    rw [inv_inv] at this
    rw [← this]
    group
  obtain ⟨⟨a, b⟩, x⟩ := q
  by_cases h1 : (a, b) = (i, j)
  · rw [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [thol_flatCfg_ij hij]
    unfold sheetO
    by_cases hp : (x a).val = 0 ∧ (x b).val = 0
    · simp [hp, hAB]
    · simp [hp]
  by_cases h2 : (a, b) = (j, i)
  · rw [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [thol_flatCfg_ji hij]
    unfold sheetO
    by_cases hp : (x b).val = 0 ∧ (x a).val = 0
    · simp [hp, hBA, hij, hij.symm]
    · simp [hp, hij, hij.symm]
  rw [thol_flatCfg_else hij A B ((a, b), x) h1 h2]
  unfold sheetO
  simp [h1, h2]

/-- **A group with every element a commutator absorbs every twist at zero action.** -/
theorem flat_twist_of_everyCommutator (h : EveryCommutator G) {i j : Fin d} (hij : i ≠ j) (z : G) :
    ∃ U : TLink d L → G, ∀ q, sheetO i j z q * thol q U = 1 := by
  obtain ⟨A, B, hAB⟩ := h z⁻¹
  exact ⟨flatCfg i j A B, flat_twist hij hAB⟩

/-- **`SU(N)`: the twisted Wilson action of every twist vanishes at one configuration**, at every
coupling and side, extending `GapSideTwistFlat.twistedAction_flat_SU2`. -/
theorem twistedAction_flat_SU {N : ℕ} (hN : N ≠ 0) {i j : Fin d} (hij : i ≠ j) (z : SU N) (β : ℝ) :
    ∃ U : TLink d L → SU N,
      fAct (twistField β WilsonAction.wilsonDensity (sheetO i j z)) U = 0 := by
  obtain ⟨U, hU⟩ := flat_twist_of_everyCommutator (L := L) su_everyCommutator hij z
  refine ⟨U, ?_⟩
  unfold fAct twistField
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [hU q, WilsonAction.wilsonDensity_one hN, mul_zero]

end Perfect

end MassGap.CoverCompact

#print axioms MassGap.CoverCompact.cubeSum
#print axioms MassGap.CoverCompact.curl
#print axioms MassGap.CoverCompact.cubeSum_curl
#print axioms MassGap.CoverCompact.curl_swap
#print axioms MassGap.CoverCompact.hyper_cubeSum
#print axioms MassGap.CoverCompact.thol_exp
#print axioms MassGap.CoverCompact.exists_link_lift
#print axioms MassGap.CoverCompact.IsAngle
#print axioms MassGap.CoverCompact.thol_swap
#print axioms MassGap.CoverCompact.thol_diag
#print axioms MassGap.CoverCompact.exists_angle
#print axioms MassGap.CoverCompact.exists_split
#print axioms MassGap.CoverCompact.cubeSum_angle
#print axioms MassGap.CoverCompact.charge_indep
#print axioms MassGap.CoverCompact.charge_zero_of_small
#print axioms MassGap.CoverCompact.Liftable
#print axioms MassGap.CoverCompact.curl_add_mul
#print axioms MassGap.CoverCompact.liftable_iff
#print axioms MassGap.CoverCompact.charge_zero_of_liftable
#print axioms MassGap.CoverCompact.sum_curl_slice
#print axioms MassGap.CoverCompact.flux_zero_of_liftable
#print axioms MassGap.CoverCompact.liftable_const
#print axioms MassGap.CoverCompact.wθ
#print axioms MassGap.CoverCompact.wa
#print axioms MassGap.CoverCompact.finRotate_two_zero
#print axioms MassGap.CoverCompact.finRotate_two_one
#print axioms MassGap.CoverCompact.wa_isAngle
#print axioms MassGap.CoverCompact.flux_witness
#print axioms MassGap.CoverCompact.continuous_int_const
#print axioms MassGap.CoverCompact.corner
#print axioms MassGap.CoverCompact.corner_off
#print axioms MassGap.CoverCompact.shift_ne
#print axioms MassGap.CoverCompact.shift2_ne
#print axioms MassGap.CoverCompact.corner_relation
#print axioms MassGap.CoverCompact.conserved_iff_affine
#print axioms MassGap.CoverCompact.hom_eq_one_of_perfect
#print axioms MassGap.CoverCompact.conserved_const_of_perfect
#print axioms MassGap.CoverCompact.EveryCommutator
#print axioms MassGap.CoverCompact.isPerfect_of_every
#print axioms MassGap.CoverCompact.circle_not_perfect
#print axioms MassGap.CoverCompact.Mat
#print axioms MassGap.CoverCompact.exists_unit_regular
#print axioms MassGap.CoverCompact.exists_diag
#print axioms MassGap.CoverCompact.exists_unit_root
#print axioms MassGap.CoverCompact.smul_mem_unitary
#print axioms MassGap.CoverCompact.diagonal_mem_unitary
#print axioms MassGap.CoverCompact.perm_mem_unitary
#print axioms MassGap.CoverCompact.perm_apply
#print axioms MassGap.CoverCompact.perm_mul_diagonal
#print axioms MassGap.CoverCompact.star_mul_prod_self
#print axioms MassGap.CoverCompact.exists_cycle_solution
#print axioms MassGap.CoverCompact.commutator_of_rel
#print axioms MassGap.CoverCompact.diag_commutator
#print axioms MassGap.CoverCompact.conj_commutator
#print axioms MassGap.CoverCompact.su_everyCommutator
#print axioms MassGap.CoverCompact.isPerfect_SU
#print axioms MassGap.CoverCompact.su_no_character
#print axioms MassGap.CoverCompact.RM
#print axioms MassGap.CoverCompact.rz
#print axioms MassGap.CoverCompact.ry
#print axioms MassGap.CoverCompact.so3_mem_of
#print axioms MassGap.CoverCompact.rz_mem
#print axioms MassGap.CoverCompact.ry_mem
#print axioms MassGap.CoverCompact.rzS
#print axioms MassGap.CoverCompact.halfTurn
#print axioms MassGap.CoverCompact.rot_commutator
#print axioms MassGap.CoverCompact.exists_frame
#print axioms MassGap.CoverCompact.exists_axis
#print axioms MassGap.CoverCompact.stab_rot
#print axioms MassGap.CoverCompact.so3_everyCommutator
#print axioms MassGap.CoverCompact.isPerfect_SO3
#print axioms MassGap.CoverCompact.conserved_const_G2
#print axioms MassGap.CoverCompact.isPerfect_A5
#print axioms MassGap.CoverCompact.a5Rep
#print axioms MassGap.CoverCompact.instGaugeGroupA5
#print axioms MassGap.CoverCompact.sheetO
#print axioms MassGap.CoverCompact.flat_twist
#print axioms MassGap.CoverCompact.flat_twist_of_everyCommutator
#print axioms MassGap.CoverCompact.twistedAction_flat_SU
