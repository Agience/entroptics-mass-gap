import Mathlib
import MassGap.GapSideTwistFlat

/-!
# MassGap.CubeFlux — the lattice Bianchi identity, abelian and transported

Single-plaquette recursions (Migdal–Kadanoff) treat `U(1)` and `SU(N)` alike (`BondMove`, `OneWayCost`).
What they discard is the constraint between plaquettes: the Bianchi identity around each elementary 3-cube.
This module states that constraint on the tree's periodic torus (`TorusDoubling.TSite`, `TLink`, `TPlaq`,
plaquette holonomy `HolderBondMoving.thol`) in its two forms and records where they differ. Declarations
are in the namespace `MassGap.CubeFlux`.

The cube at `x` spanned by distinct directions `i, j, k` has six faces: `((i,j),x)`, `((j,k),x)`,
`((k,i),x)` through the corner `x`, and `((i,j),x+k)`, `((j,k),x+i)`, `((k,i),x+j)` opposite them.
`cubeFlux F i j k x` is the plain (untransported) oriented product of a face function `F` over them:
`F(ij,x) F(jk,x) F(ki,x) (F(ij,x+k) F(jk,x+i) F(ki,x+j))⁻¹`.

## 1. The transported identity, every group (proved)

* `bianchi_transported`: for any group and any links, with the three far faces carried back to `x` along
  the link that reaches them (`U_k(x)`, `U_i(x)`, `U_j(x)`),
  `F(ij,x) · (U_j F(ki,x+j) U_j⁻¹)⁻¹ · F(jk,x) · (U_k F(ij,x+k) U_k⁻¹)⁻¹ · F(ki,x) · (U_i F(jk,x+i) U_i⁻¹)⁻¹ = 1`
  with `F = thol · U`. It is an identity in the free group on the cube's twelve links (`group`).

## 2. The abelian form: flux is conserved through every cube (proved)

* `bianchi_comm`: for a commutative group, `cubeFlux (thol · U) = 1` at every cube and every configuration.
  `U(1)` (`Circle`) and `ℤ_N` are instances. With `prod_thol_slice` (abelian Stokes on a 2-torus slice,
  `GapSideTwistFlat`) these are the two closed surfaces of the tree on which abelian flux is conserved.
* `cubeFlux_mul`, `not_flat_of_charge_comm`: in a commutative group a twist `ζ` with cube charge
  `cubeFlux ζ ≠ 1` (a monopole) leaves, at every configuration, a face of that cube with `ζ q · thol q U ≠ 1`.

## 3. The non-abelian form (proved)

* `cubeFlux_su2`: on any torus of side `N ≥ 2`, in any dimension with three distinct directions, the
  CHOSEN `SU(2)` configuration with `iσ₃` on `(i, x+k)`, `(iσ₂)⁻¹` on `(j, x+k)` and `1` elsewhere has plain
  cube product `iσ₂ · iσ₃ · (iσ₂)⁻¹ · (iσ₃)⁻¹ = −1`. `cubeFlux_su2_ne_one`: it is not `1`. The abelian
  conservation fails for `SU(2)` face by face; only the transported product is constrained.
* `not_flat_of_central_charge`: the transported identity still fixes the centre charge. For any group and
  any twist `ζ` valued in the centre, `cubeFlux ζ ≠ 1` (computed in the centre) leaves, at every
  configuration, a face of that cube with `ζ q · thol q U ≠ 1`. So a centre monopole costs action in `SU(N)`
  exactly as an abelian monopole does in `U(1)`; the plain product of the non-central faces is what is free.

## 4. Relation to the bridge (argued reading)

`FluxSplitCasimir` splits the Casimir term into the flux share `fluxShareN` (non-zero centre electric flux)
and the zero-flux defect. `not_flat_of_central_charge` says the centre-flux bookkeeping is conserved cube by
cube for `SU(N)` as for `U(1)`: the twisted sectors themselves are not where the groups differ. Where they
differ is not the transported constraint, which holds in every group (`bianchi_transported`). `cubeFlux`
multiplies plaquette holonomies based at different corners; for a non-abelian group it is not gauge
invariant, only each face is conjugation-covariant. The `SU(2)` configuration of `cubeFlux_su2` is
gauge-equivalent (conjugate the far `(i,j)` face by `iσ₂`) to one with plain product `1`, so its `−1` is a
base-point artefact, not a gauge-invariant leak. The gauge-invariant cube constraint does not separate
`SU(N)` from `U(1)`; for `U(1)` it is in addition linear in the plaquette angles.

DERIVED (module-wide): `1` the group unit; `2` the matrix size of `SU(2)` and the least side on which the
twelve links of a cube are pairwise distinct (`finRotate_ne_self`); `0`, `1` in `finRotate_ne_self` the
`Fin` arithmetic of that side. CHOSEN: `iσ₃`, `iσ₂` (`GapSideTwistFlat.sigA`, `sigB`), the anticommuting pair
already in the tree, and the two links `(i, x+k)`, `(j, x+k)` of the far `(i,j)` face. No inherited constants.

## What does not follow

Nothing here bounds the window coupling, the doubling defect `D`, `ZoomStep.WilsonZoomStep` or
`CouplingTower.StrongEnd`. The identities are statements about the group and the cube, at zero coupling
cost; they carry no measure. The plain product `1 − Re tr cubeFlux(thol · U)/N` is not gauge invariant for
`SU(N)`; its Wilson expectation averages over gauge orbits and is not a physical leak, and the transported
product, which is gauge covariant, is `1` identically. No cube quantity built here separates `SU(N)` from
`U(1)` under doubling. The cancellation of interior faces that turns `bianchi_comm` into conservation through the
boundary of an arbitrary union of cubes is not formalised; only single cubes and 2-torus slices are.
-/

noncomputable section

namespace MassGap.CubeFlux

open MassGap.TorusDoubling MassGap.HolderBondMoving

/-! ## 0. The cube product -/

section Def

variable {G : Type} [Group G] {d N : ℕ}

/-- **The plain cube product** of a face function: the three faces through `x` times the inverse of the
three opposite faces. -/
def cubeFlux (F : TPlaq d N → G) (i j k : Fin d) (x : TSite d N) : G :=
  F ((i, j), x) * F ((j, k), x) * F ((k, i), x) *
    (F ((i, j), tshift k x) * F ((j, k), tshift i x) * F ((k, i), tshift j x))⁻¹

end Def

/-! ## 1. The transported identity -/

section Transported

variable {G : Type} [Group G] {d N : ℕ}

/-- **The lattice Bianchi identity, transported**: the far faces conjugated back to `x` along `U_k(x)`,
`U_i(x)`, `U_j(x)`. Every group, every configuration. -/
theorem bianchi_transported (i j k : Fin d) (x : TSite d N) (U : TLink d N → G) :
    thol ((i, j), x) U * (U (j, x) * thol ((k, i), tshift j x) U * (U (j, x))⁻¹)⁻¹ *
      thol ((j, k), x) U * (U (k, x) * thol ((i, j), tshift k x) U * (U (k, x))⁻¹)⁻¹ *
      thol ((k, i), x) U * (U (i, x) * thol ((j, k), tshift i x) U * (U (i, x))⁻¹)⁻¹ = 1 := by
  unfold thol
  simp only
  rw [tshift_comm k j x, tshift_comm j i x, tshift_comm k i x]
  group

end Transported

/-! ## 2. The abelian form -/

section Abelian

variable {G : Type} [CommGroup G] {d N : ℕ}

theorem six_comm {H : Type} [CommGroup H] (z1 z2 z3 z4 z5 z6 : H)
    (h : z1 * z2⁻¹ * z3 * z4⁻¹ * z5 * z6⁻¹ = 1) : z1 * z3 * z5 * (z4 * z6 * z2)⁻¹ = 1 := by
  rw [← h]; simp only [mul_inv]; ac_rfl

/-- **Abelian flux conservation through a cube**: in a commutative group the plain cube product of the
plaquette holonomies is `1`, at every cube and every configuration. -/
theorem bianchi_comm (i j k : Fin d) (x : TSite d N) (U : TLink d N → G) :
    cubeFlux (fun q => thol q U) i j k x = 1 := by
  have T := bianchi_transported i j k x U
  simp only [mul_inv_cancel_comm] at T
  exact six_comm _ _ _ _ _ _ T

/-- The plain cube product is multiplicative in a commutative group. -/
theorem cubeFlux_mul (F F' : TPlaq d N → G) (i j k : Fin d) (x : TSite d N) :
    cubeFlux (fun q => F q * F' q) i j k x = cubeFlux F i j k x * cubeFlux F' i j k x := by
  unfold cubeFlux
  simp only [mul_inv]
  ac_rfl

/-- **An abelian monopole costs action**: a twist with cube charge `≠ 1` leaves a face of that cube off the
identity at every configuration. -/
theorem not_flat_of_charge_comm (ζ : TPlaq d N → G) (i j k : Fin d) (x : TSite d N)
    (hζ : cubeFlux ζ i j k x ≠ 1) (U : TLink d N → G) : ∃ q, ζ q * thol q U ≠ 1 := by
  by_contra h0
  have h : ∀ q, ζ q * thol q U = 1 := fun q => by
    by_contra hq
    exact h0 ⟨q, hq⟩
  have e1 : cubeFlux (fun q => ζ q * thol q U) i j k x = 1 := by
    simp only [h]; unfold cubeFlux; group
  rw [cubeFlux_mul, bianchi_comm, mul_one] at e1
  exact hζ e1

end Abelian

/-! ## 3. The non-abelian form -/

section Centre

variable {G : Type} [Group G] {d N : ℕ}

theorem six_inv {H : Type} [CommGroup H] (z1 z2 z3 z4 z5 z6 : H)
    (h : z1⁻¹ * z2⁻¹⁻¹ * z3⁻¹ * z4⁻¹⁻¹ * z5⁻¹ * z6⁻¹⁻¹ = 1) :
    z1 * z3 * z5 * (z4 * z6 * z2)⁻¹ = 1 := by
  have e : z1 * z3 * z5 * (z4 * z6 * z2)⁻¹ = (z1⁻¹ * z2⁻¹⁻¹ * z3⁻¹ * z4⁻¹⁻¹ * z5⁻¹ * z6⁻¹⁻¹)⁻¹ := by
    simp only [mul_inv, inv_inv]; ac_rfl
  rw [e, h, inv_one]

/-- Conjugation fixes the inverse of a central element. -/
theorem conj_inv_central (z : Subgroup.center G) (g : G) : g * (z : G)⁻¹ * g⁻¹ = (z : G)⁻¹ := by
  have hc : g * (z : G)⁻¹ = (z : G)⁻¹ * g := Subgroup.mem_center_iff.mp (z⁻¹).2 g
  rw [hc, mul_inv_cancel_right]

/-- **A centre monopole costs action in every group**: for a twist valued in the centre whose cube charge
(computed in the centre) is `≠ 1`, every configuration leaves a face of that cube with `ζ q · thol q U ≠ 1`.
The transported identity is what forces it. -/
theorem not_flat_of_central_charge (ζ : TPlaq d N → Subgroup.center G) (i j k : Fin d) (x : TSite d N)
    (hζ : cubeFlux ζ i j k x ≠ 1) (U : TLink d N → G) : ∃ q, (ζ q : G) * thol q U ≠ 1 := by
  by_contra h0
  have hq : ∀ q, thol q U = (ζ q : G)⁻¹ := fun q => by
    by_contra hne
    exact h0 ⟨q, fun h1 => hne (eq_inv_of_mul_eq_one_right h1)⟩
  have T := bianchi_transported i j k x U
  simp only [hq, conj_inv_central] at T
  have T2 : (ζ ((i, j), x))⁻¹ * (ζ ((k, i), tshift j x))⁻¹⁻¹ * (ζ ((j, k), x))⁻¹ *
      (ζ ((i, j), tshift k x))⁻¹⁻¹ * (ζ ((k, i), x))⁻¹ * (ζ ((j, k), tshift i x))⁻¹⁻¹ = 1 := by
    exact_mod_cast T
  letI : CommGroup (Subgroup.center G) :=
    { (inferInstance : Group (Subgroup.center G)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  have h6 : cubeFlux ζ i j k x = 1 :=
    six_inv (H := Subgroup.center G) (ζ ((i, j), x)) (ζ ((k, i), tshift j x)) (ζ ((j, k), x))
      (ζ ((i, j), tshift k x)) (ζ ((k, i), x)) (ζ ((j, k), tshift i x)) T2
  exact hζ h6

end Centre

section SU2

open MassGap.TwistedTraceBound (negOne coe_negOne)
open MassGap.GapSideTwistFlat (sigA sigB comm_sigB_sigA negOne_inv)

variable {d N : ℕ}

/-- On a side `N ≥ 2` the unit rotation moves every point. DERIVED: `2` the least such side. -/
theorem finRotate_ne_self (hN : 2 ≤ N) (v : Fin N) : finRotate N v ≠ v := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h2 := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one] at h2
  have hv := v.isLt
  rcases Nat.lt_or_ge (v.val + 1) (n + 2) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h2; omega
  · have e : v.val + 1 = n + 2 := by omega
    rw [e, Nat.mod_self] at h2; omega

theorem tshift_self' (a : Fin d) (y : TSite d N) : tshift a y a = finRotate N (y a) := by
  unfold tshift; exact Function.update_self _ _ _

theorem site_ne {y z : TSite d N} (a : Fin d) (h : y a ≠ z a) : y ≠ z := fun e => h (congrFun e a)

/-- The CHOSEN configuration: `iσ₃` on `(i, x+k)`, `(iσ₂)⁻¹` on `(j, x+k)`, `1` elsewhere. -/
def su2Cfg (i j k : Fin d) (x : TSite d N) (l : TLink d N) : SUN.SU 2 :=
  if l = (i, tshift k x) then sigA else if l = (j, tshift k x) then sigB⁻¹ else 1

/-- **The plain cube product of `SU(2)` plaquettes is not conserved**: at the chosen configuration it is
`iσ₂ · iσ₃ · (iσ₂)⁻¹ · (iσ₃)⁻¹ = −1`. -/
theorem cubeFlux_su2 (hN : 2 ≤ N) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (x : TSite d N) :
    cubeFlux (fun q => thol q (su2Cfg i j k x)) i j k x = negOne⁻¹ := by
  have r : ∀ v : Fin N, finRotate N v ≠ v := finRotate_ne_self hN
  have s1 : x ≠ tshift k x := site_ne k (by simp only [tshift_self']; exact (r _).symm)
  have s2 : tshift i x ≠ tshift k x :=
    site_ne i (by simp only [tshift_self', tshift_apply_ne (Ne.symm hki)]; exact r _)
  have s3 : tshift j x ≠ tshift k x :=
    site_ne j (by simp only [tshift_self', tshift_apply_ne hjk]; exact r _)
  have s4 : tshift i (tshift k x) ≠ tshift k x :=
    site_ne i (by simp only [tshift_self', tshift_apply_ne (Ne.symm hki)]; exact r _)
  have s5 : tshift j (tshift k x) ≠ tshift k x :=
    site_ne j (by simp only [tshift_self', tshift_apply_ne hjk]; exact r _)
  have s6 : tshift k (tshift i x) ≠ tshift k x :=
    site_ne i (by simp only [tshift_self', tshift_apply_ne (Ne.symm hki)]; exact r _)
  have s7 : tshift k (tshift j x) ≠ tshift k x :=
    site_ne j (by simp only [tshift_self', tshift_apply_ne hjk]; exact r _)
  have e : cubeFlux (fun q => thol q (su2Cfg i j k x)) i j k x = sigB * sigA * sigB⁻¹ * sigA⁻¹ := by
    unfold cubeFlux thol su2Cfg
    simp [hij, hki, Ne.symm hij, Ne.symm hjk, s1, s2, s3, s4, s5, s6, s7]
    group
  rw [e, comm_sigB_sigA]

theorem negOne_ne_one : (negOne : SUN.SU 2) ≠ 1 := by
  intro h
  have h2 := congrArg (fun g : SUN.SU 2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [coe_negOne] at h2

/-- **Abelian conservation fails for `SU(2)`**: the plain cube product at the chosen configuration is not
`1`, while `bianchi_transported` holds there as everywhere. -/
theorem cubeFlux_su2_ne_one (hN : 2 ≤ N) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (x : TSite d N) : cubeFlux (fun q => thol q (su2Cfg i j k x)) i j k x ≠ 1 := by
  rw [cubeFlux_su2 hN hij hjk hki x, negOne_inv]
  exact negOne_ne_one

end SU2

end MassGap.CubeFlux

#print axioms MassGap.CubeFlux.bianchi_transported
#print axioms MassGap.CubeFlux.six_comm
#print axioms MassGap.CubeFlux.bianchi_comm
#print axioms MassGap.CubeFlux.cubeFlux_mul
#print axioms MassGap.CubeFlux.not_flat_of_charge_comm
#print axioms MassGap.CubeFlux.six_inv
#print axioms MassGap.CubeFlux.conj_inv_central
#print axioms MassGap.CubeFlux.not_flat_of_central_charge
#print axioms MassGap.CubeFlux.finRotate_ne_self
#print axioms MassGap.CubeFlux.tshift_self'
#print axioms MassGap.CubeFlux.site_ne
#print axioms MassGap.CubeFlux.cubeFlux_su2
#print axioms MassGap.CubeFlux.negOne_ne_one
#print axioms MassGap.CubeFlux.cubeFlux_su2_ne_one
