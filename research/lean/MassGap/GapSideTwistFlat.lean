import Mathlib
import MassGap.HolderBondMoving
import MassGap.TwistedTraceBound
import MassGap.CentreSectorSeedN
import MassGap.ChainFirstCrossing
import MassGap.WilsonChainExists

/-!
# MassGap.GapSideTwistFlat — SU(2) absorbs a centre twist at zero action; no abelian group can

The centre twist of a torus in the plane `(i, j)` puts the central element `z` on the plaquettes
`((i, j), x)` and `((j, i), x)` with `x_i = x_j = 0`: one plaquette in every `(i, j)` 2-torus slice
(`sheet`). The twisted field is `HolderBondMoving.twistField β φ (sheet i j z)`.

* **SU(2): a flat twisted configuration on every torus** (`flatCfg`, `thol_flatCfg_ij`,
  `thol_flatCfg_ji`, `thol_flatCfg_else`). For any group and any `A, B`, the configuration with `A` on
  the `i`-links at `x_i = 0`, `B` on the `j`-links at `x_j = 0` and `1` elsewhere has plaquette
  holonomy `ABA⁻¹B⁻¹` on the `(i, j)` sheet, `BAB⁻¹A⁻¹` on the `(j, i)` sheet and `1` everywhere else.
  For `SU(2)`, `A = iσ₃`, `B = iσ₂` anticommute (`sigA_mul_sigB`), both commutators are `−1`, and
  `twisted_flat_SU2` gives `sheet · holonomy = 1` on every plaquette: `twistedAction_flat_SU2`, the
  twisted Wilson action vanishes at that configuration, at every side, every dimension and every
  coupling.
* **Every commutative group: no flat twisted configuration** (`prod_thol_slice`, `not_flat_of_comm`,
  `twistedAction_pos_of_comm`). In a commutative group the product of the `(i, j)` plaquette holonomies
  over a 2-torus slice is `1` for every configuration (abelian Stokes on a closed surface: each link
  enters once with each orientation). So the product of `sheet · holonomy` over the slice is `z`, and
  with `z ≠ 1` some plaquette is off the identity. For a density positive off the identity the twisted
  action is positive at every configuration. `U(1)` (`Circle`) and `ℤ₂` are instances.
* **The vortex form of the decisive instance** (`FirstCrossingSectorSeed`): at the first crossing
  `k` of the chain, the flux share and the zero-flux defect of the Wilson `SU(2)` torus of side
  `2^{k+2}` are at most `1/80000` at every corner step. This is the decisive instance with its twisted
  partition functions separated (`FluxShareSquaring.fluxShare_eq_mean`): the flux half is the vortex
  free energy.

Scope: the flat twisted configuration fixes the classical cost of the twist at `0` for `SU(2)`. It is
a statement about the group, not the dynamics: it holds at every coupling, every side and in every
dimension `d ≥ 2`, so it holds for `5D` `SU(2)` as well, and it does not bound the twisted ratio
`Z_tw/Z` from below. Nothing here proves `FirstCrossingSectorSeed`.

DERIVED (module-wide): `0` is the coordinate of the sheet (any fixed coordinate serves; `0` needs no
`NeZero`); `2` is the matrix size of `SU(2)` and the side factor `2^{k+2}` of the crossing scale;
`1/80000` and `1/1000` are `CentreSectorSeedN.defectW_le_of_sectorsN`'s thresholds.
-/

noncomputable section

namespace MassGap.GapSideTwistFlat

open Filter MassGap.TorusDoubling MassGap.HolderBondMoving

/-! ## 1. The flat configuration and its holonomies, in any group -/

section Config

variable {G : Type} [Group G] {d N : ℕ}

/-- `A` on the `i`-links at `x_i = 0`, `B` on the `j`-links at `x_j = 0`, `1` elsewhere. -/
def flatCfg (i j : Fin d) (A B : G) (l : TLink d N) : G :=
  if l.1 = i ∧ (l.2 i).val = 0 then A else if l.1 = j ∧ (l.2 j).val = 0 then B else 1

theorem tshift_ne {k m : Fin d} (h : m ≠ k) (x : TSite d N) : tshift k x m = x m := by
  unfold tshift; rw [Function.update_of_ne h]

theorem flatCfg_i {i j : Fin d} (hij : i ≠ j) (A B : G) (x : TSite d N) :
    flatCfg i j A B (i, x) = if (x i).val = 0 then A else 1 := by
  unfold flatCfg
  by_cases h : (x i).val = 0
  · simp [h]
  · simp [h, hij]

theorem flatCfg_j {i j : Fin d} (hij : i ≠ j) (A B : G) (x : TSite d N) :
    flatCfg i j A B (j, x) = if (x j).val = 0 then B else 1 := by
  unfold flatCfg
  simp [hij.symm]

theorem flatCfg_other {i j k : Fin d} (hi : k ≠ i) (hj : k ≠ j) (A B : G) (x : TSite d N) :
    flatCfg i j A B (k, x) = 1 := by
  unfold flatCfg
  simp [hi, hj]

/-- The `(i, j)` plaquettes carry the commutator `ABA⁻¹B⁻¹` on the sheet, `1` off it. -/
theorem thol_flatCfg_ij {i j : Fin d} (hij : i ≠ j) (A B : G) (x : TSite d N) :
    thol ((i, j), x) (flatCfg i j A B) =
      if (x i).val = 0 ∧ (x j).val = 0 then A * B * A⁻¹ * B⁻¹ else 1 := by
  unfold thol
  simp only
  rw [flatCfg_i hij, flatCfg_j hij, flatCfg_i hij, flatCfg_j hij, tshift_ne hij.symm,
    tshift_ne hij]
  by_cases hp : (x i).val = 0 <;> by_cases hq : (x j).val = 0 <;> simp [hp, hq]

/-- The `(j, i)` plaquettes carry the commutator `BAB⁻¹A⁻¹` on the sheet, `1` off it. -/
theorem thol_flatCfg_ji {i j : Fin d} (hij : i ≠ j) (A B : G) (x : TSite d N) :
    thol ((j, i), x) (flatCfg i j A B) =
      if (x i).val = 0 ∧ (x j).val = 0 then B * A * B⁻¹ * A⁻¹ else 1 := by
  unfold thol
  simp only
  rw [flatCfg_j hij, flatCfg_i hij, flatCfg_j hij, flatCfg_i hij, tshift_ne hij,
    tshift_ne hij.symm]
  by_cases hp : (x i).val = 0 <;> by_cases hq : (x j).val = 0 <;> simp [hp, hq]

/-- Every other plaquette is flat. -/
theorem thol_flatCfg_else {i j : Fin d} (hij : i ≠ j) (A B : G) (q : TPlaq d N)
    (h1 : q.1 ≠ (i, j)) (h2 : q.1 ≠ (j, i)) : thol q (flatCfg i j A B) = 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := q
  unfold thol
  simp only
  by_cases hab : a = b
  · subst hab; group
  by_cases ha : a = i
  · subst ha
    have hb : b ≠ a := Ne.symm hab
    have hbj : b ≠ j := fun h => h1 (by rw [h])
    rw [flatCfg_i hij, flatCfg_other hb hbj, flatCfg_i hij, flatCfg_other hb hbj,
      tshift_ne (Ne.symm hb)]
    group
  by_cases ha' : a = j
  · subst ha'
    have hbi : b ≠ i := fun h => h2 (by rw [h])
    have hb : b ≠ a := Ne.symm hab
    rw [flatCfg_j hij, flatCfg_other hbi hb, flatCfg_j hij, flatCfg_other hbi hb,
      tshift_ne (Ne.symm hb)]
    group
  by_cases hb : b = i
  · subst hb
    rw [flatCfg_other ha ha', flatCfg_i hij, flatCfg_other ha ha', flatCfg_i hij,
      tshift_ne (Ne.symm ha)]
    group
  by_cases hb' : b = j
  · subst hb'
    rw [flatCfg_other ha ha', flatCfg_j hij, flatCfg_other ha ha', flatCfg_j hij,
      tshift_ne (Ne.symm ha')]
    group
  rw [flatCfg_other ha ha', flatCfg_other hb hb', flatCfg_other ha ha', flatCfg_other hb hb']
  group

/-- **The centre twist sheet** in the plane `(i, j)`: `z` on the `(i, j)` and `(j, i)` plaquettes with
`x_i = x_j = 0`, `1` elsewhere. -/
def sheet (i j : Fin d) (z : G) (q : TPlaq d N) : G :=
  if (q.1 = (i, j) ∨ q.1 = (j, i)) ∧ (q.2 i).val = 0 ∧ (q.2 j).val = 0 then z else 1

/-- **Absorption at zero action.** If both commutators of `A, B` equal `z⁻¹`, the twisted holonomy
`sheet · holonomy` is `1` on every plaquette of the flat configuration. -/
theorem twisted_flat_of_comm_eq {i j : Fin d} (hij : i ≠ j) {A B z : G}
    (hAB : A * B * A⁻¹ * B⁻¹ = z⁻¹) (hBA : B * A * B⁻¹ * A⁻¹ = z⁻¹) (q : TPlaq d N) :
    sheet i j z q * thol q (flatCfg i j A B) = 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := q
  by_cases h1 : (a, b) = (i, j)
  · rw [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rw [thol_flatCfg_ij hij]
    unfold sheet
    by_cases hp : (x a).val = 0 ∧ (x b).val = 0
    · simp [hp, hAB]
    · simp [hp]
  by_cases h2 : (a, b) = (j, i)
  · rw [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [thol_flatCfg_ji hij]
    unfold sheet
    by_cases hp : (x b).val = 0 ∧ (x a).val = 0
    · simp [hp, hBA]
    · simp [hp]
  rw [thol_flatCfg_else hij A B ((a, b), x) h1 h2]
  unfold sheet
  simp [h1, h2]

end Config

/-! ## 2. SU(2): the anticommuting pair -/

section SU2

open MassGap.TwistedTraceBound (negOne coe_negOne negOne_mul_self)

/-- `iσ₃ = diag(i, −i)`. -/
def sigA : SUN.SU 2 :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- `iσ₂ = [[0, 1], [−1, 0]]`. -/
def sigB : SUN.SU 2 :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · simp [Matrix.det_fin_two]⟩

/-- **The pair anticommutes**: `iσ₃ · iσ₂ = −(iσ₂ · iσ₃)`. -/
theorem sigA_mul_sigB : sigA * sigB = negOne * (sigB * sigA) := by
  apply Subtype.ext
  show (!![Complex.I, 0; 0, -Complex.I] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
    = -1 * (!![0, 1; -1, 0] * !![Complex.I, 0; 0, -Complex.I])
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem negOne_inv : negOne⁻¹ = negOne :=
  inv_eq_of_mul_eq_one_right negOne_mul_self

theorem comm_sigA_sigB : sigA * sigB * sigA⁻¹ * sigB⁻¹ = negOne⁻¹ := by
  rw [sigA_mul_sigB, negOne_inv]; group

theorem comm_sigB_sigA : sigB * sigA * sigB⁻¹ * sigA⁻¹ = negOne⁻¹ := by
  have h : sigB * sigA = negOne⁻¹ * (sigA * sigB) := by
    rw [sigA_mul_sigB]; group
  rw [h]; group

variable {d N : ℕ}

/-- **SU(2) absorbs the twist at zero action**: with the centre sheet `−1` in any plane `(i, j)`, the
flat configuration of the anticommuting pair has `sheet · holonomy = 1` on every plaquette. -/
theorem twisted_flat_SU2 {i j : Fin d} (hij : i ≠ j) (q : TPlaq d N) :
    sheet i j negOne q * thol q (flatCfg i j sigA sigB) = 1 :=
  twisted_flat_of_comm_eq hij comm_sigA_sigB comm_sigB_sigA q

/-- **The twisted Wilson action vanishes** at the flat configuration, at every coupling and side. -/
theorem twistedAction_flat_SU2 {i j : Fin d} (hij : i ≠ j) (β : ℝ) :
    fAct (twistField β WilsonAction.wilsonDensity (sheet i j negOne))
      (flatCfg (N := N) i j sigA sigB) = 0 := by
  unfold fAct twistField
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [twisted_flat_SU2 hij q, WilsonAction.wilsonDensity_one (by norm_num), mul_zero]

end SU2

/-! ## 3. Commutative groups: abelian Stokes on a 2-torus slice -/

section Abelian

variable {G : Type} [CommGroup G] {d N : ℕ}

/-- The point `(s, t)` of the `(i, j)` 2-torus slice through `x`. -/
def slicePt (i j : Fin d) (x : TSite d N) (s t : Fin N) : TSite d N :=
  Function.update (Function.update x i s) j t

theorem slicePt_i {i j : Fin d} (hij : i ≠ j) (x : TSite d N) (s t : Fin N) :
    slicePt i j x s t i = s := by
  unfold slicePt; rw [Function.update_of_ne hij, Function.update_self]

theorem slicePt_j (i j : Fin d) (x : TSite d N) (s t : Fin N) : slicePt i j x s t j = t := by
  unfold slicePt; rw [Function.update_self]

theorem tshift_slicePt_i {i j : Fin d} (hij : i ≠ j) (x : TSite d N) (s t : Fin N) :
    tshift i (slicePt i j x s t) = slicePt i j x (finRotate N s) t := by
  unfold tshift
  rw [slicePt_i hij]
  unfold slicePt
  rw [Function.update_comm hij.symm, Function.update_idem]

theorem tshift_slicePt_j (i j : Fin d) (x : TSite d N) (s t : Fin N) :
    tshift j (slicePt i j x s t) = slicePt i j x s (finRotate N t) := by
  unfold tshift
  rw [slicePt_j]
  unfold slicePt
  rw [Function.update_idem]

/-- **Abelian Stokes on a closed 2-torus**: in a commutative group the `(i, j)` plaquette holonomies of
a slice multiply to `1`, for every configuration. -/
theorem prod_thol_slice {i j : Fin d} (hij : i ≠ j) (x : TSite d N) (U : TLink d N → G) :
    ∏ s, ∏ t, thol ((i, j), slicePt i j x s t) U = 1 := by
  set a : Fin N → Fin N → G := fun s t => U (i, slicePt i j x s t)
  set b : Fin N → Fin N → G := fun s t => U (j, slicePt i j x s t)
  have hq : ∀ s t, thol ((i, j), slicePt i j x s t) U
      = a s t * b (finRotate N s) t * (a s (finRotate N t))⁻¹ * (b s t)⁻¹ := by
    intro s t
    unfold thol
    simp only [a, b]
    rw [tshift_slicePt_i hij, tshift_slicePt_j]
  have h1 : ∏ s, ∏ t, b (finRotate N s) t = ∏ s, ∏ t, b s t :=
    Equiv.prod_comp (finRotate N) (fun s => ∏ t, b s t)
  have h2 : ∏ s, ∏ t, a s (finRotate N t) = ∏ s, ∏ t, a s t :=
    Finset.prod_congr rfl fun s _ => Equiv.prod_comp (finRotate N) (fun t => a s t)
  simp only [hq, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h1, h2]
  rw [mul_comm (∏ s, ∏ t, a s t) (∏ s, ∏ t, b s t)]
  group

/-- **No flat twisted configuration in a commutative group**: if the twist multiplies to `z ≠ 1` over
one `(i, j)` slice, every configuration has a plaquette with `twist · holonomy ≠ 1`. -/
theorem not_flat_of_comm {i j : Fin d} (hij : i ≠ j) (x : TSite d N) (ζ : TPlaq d N → G)
    (hζ : ∏ s, ∏ t, ζ ((i, j), slicePt i j x s t) ≠ 1) (U : TLink d N → G) :
    ∃ q, ζ q * thol q U ≠ 1 := by
  by_contra h0
  have h : ∀ q, ζ q * thol q U = 1 := fun q => by
    by_contra hq
    exact h0 ⟨q, hq⟩
  have hprod : ∏ s, ∏ t, (ζ ((i, j), slicePt i j x s t) * thol ((i, j), slicePt i j x s t) U)
      = 1 := Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun t _ => h _
  rw [show (∏ s, ∏ t, (ζ ((i, j), slicePt i j x s t) * thol ((i, j), slicePt i j x s t) U))
      = (∏ s, ∏ t, ζ ((i, j), slicePt i j x s t)) * ∏ s, ∏ t, thol ((i, j), slicePt i j x s t) U
      by simp only [Finset.prod_mul_distrib], prod_thol_slice hij x U, mul_one] at hprod
  exact hζ hprod

/-- The centre sheet meets every `(i, j)` slice in exactly one plaquette: the slice product is `z`. -/
theorem prod_sheet_slice [NeZero N] {i j : Fin d} (hij : i ≠ j) (x : TSite d N) (z : G) :
    ∏ s, ∏ t, sheet i j z (((i, j), slicePt i j x s t) : TPlaq d N) = z := by
  have hval : ∀ s : Fin N, s.val = 0 ↔ s = 0 := fun s => by
    rw [Fin.ext_iff, Fin.val_zero]
  have hterm : ∀ s t : Fin N, sheet i j z (((i, j), slicePt i j x s t) : TPlaq d N)
      = if s = 0 ∧ t = 0 then z else 1 := by
    intro s t
    unfold sheet
    simp only [slicePt_i hij, slicePt_j, hval, true_or, true_and]
  simp only [hterm]
  rw [Fintype.prod_eq_single (0 : Fin N) fun s hs => Finset.prod_eq_one fun t _ => by simp [hs]]
  rw [Fintype.prod_eq_single (0 : Fin N) fun t ht => by simp [ht]]
  simp

/-- **The abelian twisted action is positive at every configuration**: for a density `φ ≥ 0` vanishing
only at `1`, `β > 0` and a centre sheet `z ≠ 1`. -/
theorem twistedAction_pos_of_comm [NeZero N] {i j : Fin d} (hij : i ≠ j) {z : G} (hz : z ≠ 1)
    {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ : ∀ g, g ≠ 1 → 0 < φ g) {β : ℝ} (hβ : 0 < β)
    (U : TLink d N → G) : 0 < fAct (twistField β φ (sheet i j z)) U := by
  have hd : Nonempty (TSite d N) := ⟨fun _ => 0⟩
  obtain ⟨x⟩ := hd
  obtain ⟨q, hq⟩ := not_flat_of_comm hij x (sheet i j z)
    (by rw [prod_sheet_slice hij x z]; exact hz) U
  unfold fAct twistField
  exact Finset.sum_pos' (fun p _ => mul_nonneg hβ.le (hφ0 _))
    ⟨q, Finset.mem_univ _, mul_pos hβ (hφ _ hq)⟩

/-- `U(1)` is an instance. -/
example : CommGroup Circle := inferInstance

end Abelian

/-! ## 4. The vortex form of the decisive instance -/

section Sector

open MassGap.WilsonChainExists MassGap.ChainFirstCrossing

/-- **The decisive instance in sector form**: eventually in `β`, at the first crossing `k` of the chain
from `e^{2βt}`, every corner step of the Wilson `SU(2)` torus of side `2^{k+2}` has flux share (the mean
deficit of the twisted partition functions) and zero-flux defect at most `1/80000`.

DERIVED: `1/80000` and `1/1000` are `CentreSectorSeedN.defectW_le_of_sectorsN`'s thresholds (`80000` chosen
there so that `15 · 5/80000 ≤ 1/1000`); `2` the matrix size of `SU(2)`, the `2β` of `e^{2βt}` and the side
factor of `2^{k+2}`. -/
def FirstCrossingSectorSeed : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ i : Fin 4, CentreSectorSeedN.fluxShareN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000 ∧
      CentreSectorSeedN.trivialDefectN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000

end Sector

end MassGap.GapSideTwistFlat

#print axioms MassGap.GapSideTwistFlat.thol_flatCfg_ij
#print axioms MassGap.GapSideTwistFlat.thol_flatCfg_else
#print axioms MassGap.GapSideTwistFlat.twisted_flat_of_comm_eq
#print axioms MassGap.GapSideTwistFlat.sigA_mul_sigB
#print axioms MassGap.GapSideTwistFlat.twisted_flat_SU2
#print axioms MassGap.GapSideTwistFlat.twistedAction_flat_SU2
#print axioms MassGap.GapSideTwistFlat.prod_thol_slice
#print axioms MassGap.GapSideTwistFlat.not_flat_of_comm
#print axioms MassGap.GapSideTwistFlat.prod_sheet_slice
#print axioms MassGap.GapSideTwistFlat.twistedAction_pos_of_comm
