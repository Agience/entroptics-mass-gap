import Mathlib
import MassGap.BoxGap
import MassGap.HeatBathLocal
import MassGap.PeriodicContent
import MassGap.HaarVariance

noncomputable section

/-!
# MassGap.BoxCeiling — the box local gap never exceeds `1`, so the box check needs side `40`

## What it gives

1. **One box link read.** At every box corner `k` of the torus of extent `2(j + 1)` and every side
   `1 ≤ n ≤ j + 1`, the plaquette `cornerPlaq k` in the `(0, 1)` plane based at `k − e₀` has exactly one
   link whose base site lies in the box, the link `(1, k)`: its other three links sit at base sites
   whose `0`-coordinate is `k₀ − 1`, outside the box (`corner_not_mem`). Its plaquette observable
   `cornerObs j k` is periodic gauge invariant and does not read any other box link
   (`cornerObs_readsNot`).
2. **The patch operator acts as one projection.** Every box link `l ≠ (1, k)` has `x − Eₗx` null in
   `torusForm` for `x = cornerObs j k` (`HeatBathLocal.null_of_torusObs_eq`,
   `HeatBath.torusCondExp_keeps`), so `torusForm(A x, y) = torusForm(x − E x, y)` for every `y`,
   `A = boxOp β n j k`, `E = torusCondExp` at `(1, k)` (`corner_boxOp_form`). With `id − E` a
   self-adjoint idempotent, `torusForm(A x, x) = torusForm(A x, A x) = torusForm(x − E x, x − E x)`.
3. **The complement is not null.** `torusForm_sub_condExp_pos`: if the torus reading of `x` changes
   when the link `l` alone changes, then `torusForm(x − Eₗx, x − Eₗx) > 0` (a null complement makes the
   reading equal to its heat bath at every configuration, which does not read `l`; the Gibbs integral of
   a continuous non-negative function that is somewhere positive is positive against the open-positive
   product Haar measure). At `2 ≤ N` the corner observable changes: the identity configuration gives
   the density of `1`, and changing `(1, k)` alone to `flipEl` gives a different density
   (`HaarVariance.reTr_flipEl_ne_reTr_one`).
4. **The ceiling.** `boxLocalGap_le_one`: at `2 ≤ N` and `1 ≤ n`, `BoxLocalGap hN β n γ → γ ≤ 1`, at
   every real `β`. `boxPatchGap_side_ge_forty`: `BoxPatchGap hN β n γ → 40 ≤ n`
   (`BoxGap.threshold_lt_one_iff`). `boxPatchGap_zero_one_iff`: at `β = 0`, `BoxPatchGap hN 0 n 1`
   holds exactly from side `40` on (`BoxGap.boxPatchGap_zero`).

## Scope

The ceiling holds at every real coupling and every extent; it uses one explicit observable and one
explicit configuration pair, and no bound on the gap other than `γ ≤ 1`. The hypothesis `2 ≤ N` is
load-bearing: at `N = 1` every density is `0` (`PlaqVariance.wilsonDensity_su_one`), the corner
observable is constant, and the complement is null. The hypothesis `1 ≤ n` is load-bearing: at `n = 0`
the box is empty, `boxOp` is `0`, and `BoxLocalGap` holds at every `γ`.
-/

namespace MassGap.BoxCeiling

open MeasureTheory
open MassGap MassGap.HeatBath MassGap.KnabeCriterion MassGap.BoxPatch
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.PeriodicState (torusObs)
open MassGap.WilsonLattice (wilsonSystem wilsonHol)

/-! ## 1. A bilinear form on a sum with one non-null term -/

section Engine

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- **A sum with one non-null term pairs as that term.** For a symmetric non-negative `B`, a finite
set `S`, `i₀ ∈ S` and `d i` null for every other `i ∈ S`: `B(Σ_{i ∈ S} d i, y) = B(d i₀, y)` for every
`y` (`HeatBathLocal.fnull_pair`).

DERIVED: `0` is the null value. -/
theorem form_finsetSum_eq_single (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (d : ι → E) (S : Finset ι) {i₀ : ι} (hi₀ : i₀ ∈ S)
    (hnull : ∀ i ∈ S, i ≠ i₀ → B (d i) (d i) = 0) (y : E) :
    B (∑ i ∈ S, d i) y = B (d i₀) y := by
  have h1 : B (∑ i ∈ S, d i) = ∑ i ∈ S, B (d i) := map_sum B d S
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi hne => ?_)
  rw [hsymm]
  exact MassGap.HeatBathLocal.fnull_pair B hsymm hnn (hnull i hi hne) y

#print axioms form_finsetSum_eq_single

/-- **A gap inequality whose two sides are one positive number gives a gap at most `1`.**

DERIVED: `1` is the ceiling asserted; `0` is the sign of `v`. -/
theorem gap_le_one_of_eq {γ a b v : ℝ} (ha : a = v) (hb : b = v) (hv : 0 < v) (h : γ * a ≤ b) :
    γ ≤ 1 := by
  rw [ha, hb] at h
  nlinarith

#print axioms gap_le_one_of_eq

end Engine

/-! ## 2. The corner plaquette -/

section Corner

variable {M : ℕ}

/-- The site one step back from the corner `k` in direction `0`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the unit step
back. CHOSEN: `0` is the direction of the step; any direction serves. -/
def cornerSite (k : WilsonHypercubic.Site 4 (M + 1)) : WilsonHypercubic.Site 4 (M + 1) :=
  Function.update k 0 (k 0 - 1)

/-- **The corner plaquette**: the `(0, 1)` plaquette based at `cornerSite k`, whose second link is
`(1, k)`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. CHOSEN: `(0, 1)` is
the plane; any two distinct directions with the step back along the first serve. -/
def cornerPlaq (k : WilsonHypercubic.Site 4 (M + 1)) : WilsonHypercubic.Plaq 4 (M + 1) :=
  (((0 : Fin 4), (1 : Fin 4)), cornerSite k)

/-- `cornerSite k` reads `k₀ − 1` in direction `0`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the unit step;
`0` is the direction of the step. -/
theorem cornerSite_zero (k : WilsonHypercubic.Site 4 (M + 1)) : cornerSite k 0 = k 0 - 1 := by
  unfold cornerSite
  exact Function.update_self _ _ _

#print axioms cornerSite_zero

/-- **One step forward from `cornerSite k` in direction `0` is `k`** (`Function.update_idem`,
`sub_add_cancel`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` is the direction
of the step. -/
theorem shift_cornerSite (k : WilsonHypercubic.Site 4 (M + 1)) :
    WilsonHypercubic.shift 0 (cornerSite k) = k := by
  unfold MassGap.WilsonHypercubic.shift cornerSite
  rw [Function.update_idem, Function.update_self, sub_add_cancel, Function.update_eq_self]

#print axioms shift_cornerSite

/-- A step in direction `1` keeps the `0`-coordinate `k₀ − 1`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent, the unit step and
the direction of the shift; `0` is the coordinate read. -/
theorem shift_one_cornerSite_zero (k : WilsonHypercubic.Site 4 (M + 1)) :
    WilsonHypercubic.shift 1 (cornerSite k) 0 = k 0 - 1 := by
  unfold MassGap.WilsonHypercubic.shift
  rw [Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1), cornerSite_zero]

#print axioms shift_one_cornerSite_zero

/-- `cornerSite k ≠ k` once the extent is at least `2` (`PeriodicContent.shift_ne_self`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the least `M`
with extent at least `2`. -/
theorem cornerSite_ne (k : WilsonHypercubic.Site 4 (M + 1)) (hM : 1 ≤ M) : cornerSite k ≠ k :=
  fun h => MassGap.PeriodicContent.shift_ne_self M hM 0 (cornerSite k)
    ((shift_cornerSite k).trans h.symm)

#print axioms cornerSite_ne

/-- **A site with `0`-coordinate `k₀ − 1` is outside the box of side `n ≤ M` at `k`**: its
displacement reads `−1 = M` there (`Fin.coe_neg_one`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the unit step;
`0` is the coordinate read. -/
theorem not_inBox_of_zero {n : ℕ} (hnM : n ≤ M) (k s : WilsonHypercubic.Site 4 (M + 1))
    (hs : s 0 = k 0 - 1) : ¬ InBox n (s - k) := by
  intro h
  have h0 : (((s - k) 0 : Fin (M + 1)) : ℕ) < n := h 0
  have e : (s - k) 0 = (-1 : Fin (M + 1)) := by
    rw [Pi.sub_apply, hs]
    exact sub_sub_cancel_left _ _
  rw [e, Fin.coe_neg_one] at h0
  omega

#print axioms not_inBox_of_zero

/-- The links of a plaquette are the four entries of its boundary word.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem mem_bdT_cases (q : WilsonHypercubic.Plaq 4 (M + 1)) {l : WilsonHypercubic.Link 4 (M + 1)}
    (h : l ∈ (bdT M q).map Prod.fst) :
    l = (q.1.1, q.2) ∨ l = (q.1.2, WilsonHypercubic.shift q.1.1 q.2) ∨
      l = (q.1.1, WilsonHypercubic.shift q.1.2 q.2) ∨ l = (q.1.2, q.2) := by
  simp only [bdT, WilsonHypercubic.bd, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

#print axioms mem_bdT_cases

/-- **The corner plaquette reads no box link but `(1, k)`**: for `n ≤ M`, a link with base site in
the box of side `n` at `k`, other than `(1, k)`, is not on the corner plaquette (`mem_bdT_cases`,
`not_inBox_of_zero`, `shift_cornerSite`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the direction of
the read link. -/
theorem corner_not_mem {n : ℕ} (hnM : n ≤ M) (k : WilsonHypercubic.Site 4 (M + 1))
    {l : WilsonHypercubic.Link 4 (M + 1)} (hl : InBox n (l.2 - k)) (hne : l ≠ ((1 : Fin 4), k)) :
    l ∉ (bdT M (cornerPlaq k)).map Prod.fst := by
  intro hmem
  rcases mem_bdT_cases (cornerPlaq k) hmem with h | h | h | h
  · subst h
    exact not_inBox_of_zero hnM k (cornerSite k) (cornerSite_zero k) hl
  · subst h
    exact hne (by
      show ((1 : Fin 4), WilsonHypercubic.shift 0 (cornerSite k)) = ((1 : Fin 4), k)
      rw [shift_cornerSite])
  · subst h
    exact not_inBox_of_zero hnM k _ (shift_one_cornerSite_zero k) hl
  · subst h
    exact not_inBox_of_zero hnM k (cornerSite k) (cornerSite_zero k) hl

#print axioms corner_not_mem

/-- **The link `(1, k)` lies in the box of side `n ≥ 1` at `k`.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent, the direction of
the link and the least side. -/
theorem corner_mem_boxLinks {n : ℕ} (hn : 1 ≤ n) (k : WilsonHypercubic.Site 4 (M + 1)) :
    ((1 : Fin 4), k) ∈ MassGap.BoxGap.boxLinks n k := by
  unfold MassGap.BoxGap.boxLinks
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i
  show (((k - k) i : Fin (M + 1)) : ℕ) < n
  rw [sub_self]
  show ((0 : Fin (M + 1)) : ℕ) < n
  rw [Fin.val_zero]
  omega

#print axioms corner_mem_boxLinks

/-- A link of `boxLinks n k` has its base site in the box.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem inBox_of_mem_boxLinks {n : ℕ} {k : WilsonHypercubic.Site 4 (M + 1)}
    {l : WilsonHypercubic.Link 4 (M + 1)} (h : l ∈ MassGap.BoxGap.boxLinks n k) :
    InBox n (l.2 - k) := by
  unfold MassGap.BoxGap.boxLinks at h
  exact (Finset.mem_filter.mp h).2

#print axioms inBox_of_mem_boxLinks

variable {N : ℕ}

/-- **The corner holonomy**: `U(0, k − e₀) · (U(1, k) · (U(0, k − e₀ + e₁)⁻¹ · U(1, k − e₀)⁻¹))`
(`PeriodicContent.hol_torus_eq`, `shift_cornerSite`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` and `1` are the
plaquette's directions. -/
theorem hol_cornerPlaq (k : WilsonHypercubic.Site 4 (M + 1))
    (U : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    wilsonHol (bdT M) (cornerPlaq k) U
      = U ((0 : Fin 4), cornerSite k) * (U ((1 : Fin 4), k)
          * ((U ((0 : Fin 4), WilsonHypercubic.shift 1 (cornerSite k)))⁻¹
            * (U ((1 : Fin 4), cornerSite k))⁻¹)) := by
  rw [MassGap.PeriodicContent.hol_torus_eq M (cornerPlaq k) U]
  show U ((0 : Fin 4), cornerSite k) * (U ((1 : Fin 4), WilsonHypercubic.shift 0 (cornerSite k))
      * ((U ((0 : Fin 4), WilsonHypercubic.shift 1 (cornerSite k)))⁻¹
        * (U ((1 : Fin 4), cornerSite k))⁻¹)) = _
  rw [shift_cornerSite]

#print axioms hol_cornerPlaq

/-- **With the other three links at the identity, the corner holonomy is the link `(1, k)`.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the group
identity; `0` and `1` are the plaquette's directions. -/
theorem hol_cornerPlaq_eq (k : WilsonHypercubic.Site 4 (M + 1))
    (U : WilsonHypercubic.Link 4 (M + 1) → SU N) (h0 : U ((0 : Fin 4), cornerSite k) = 1)
    (h1 : U ((0 : Fin 4), WilsonHypercubic.shift 1 (cornerSite k)) = 1)
    (h2 : U ((1 : Fin 4), cornerSite k) = 1) :
    wilsonHol (bdT M) (cornerPlaq k) U = U ((1 : Fin 4), k) := by
  rw [hol_cornerPlaq, h0, h1, h2]
  simp only [inv_one, one_mul, mul_one]

#print axioms hol_cornerPlaq_eq

end Corner

/-! ## 3. The corner observable -/

section Observable

variable {N : ℕ}

/-- The corner plaquette on `ℤ⁴`: the `(0, 1)` plaquette at the lifted `cornerSite k`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. CHOSEN: `(0, 1)`
is `cornerPlaq`'s plane. -/
def cornerIPlaq (M : ℕ) (k : WilsonHypercubic.Site 4 (M + 1)) : GibbsSpec.IPlaq :=
  (((0 : Fin 4), (1 : Fin 4)), MassGap.HeatBath.liftSite M (cornerSite k))

/-- The corner plaquette on `ℤ⁴` reduces to `cornerPlaq k` (`HeatBath.siteMod_liftSite`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem plaqMod_cornerIPlaq (M : ℕ) (k : WilsonHypercubic.Site 4 (M + 1)) :
    MassGap.InfiniteLattice.plaqMod M (cornerIPlaq M k) = cornerPlaq k := by
  show (((0 : Fin 4), (1 : Fin 4)),
      MassGap.InfiniteLattice.siteMod M (MassGap.HeatBath.liftSite M (cornerSite k)))
    = (((0 : Fin 4), (1 : Fin 4)), cornerSite k)
  rw [MassGap.HeatBath.siteMod_liftSite]

#print axioms plaqMod_cornerIPlaq

/-- **The corner observable**: the plaquette observable of `cornerIPlaq (2j + 1) k`, periodic gauge
invariant (`GaugeInvariantAlgebra.isIGaugeInvariant_of_classFun`, `WilsonAction.wilsonDensity_conj`,
`KnabeCriterion.periodicGaugeInv_of_isIGaugeInvariant`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def cornerObs (j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  ⟨MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (cornerIPlaq (2 * j + 1) k),
    show PeriodicGaugeInv (2 * j + 1)
        (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (cornerIPlaq (2 * j + 1) k)) from
      periodicGaugeInv_of_isIGaugeInvariant (2 * j + 1)
        (F := MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (cornerIPlaq (2 * j + 1) k))
        (MassGap.GaugeInvariantAlgebra.isIGaugeInvariant_of_classFun (G := SU N)
          (φ := MassGap.WilsonAction.wilsonDensity (N := N))
          (fun h g => MassGap.WilsonAction.wilsonDensity_conj h g) (cornerIPlaq (2 * j + 1) k)
          (F := MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (cornerIPlaq (2 * j + 1) k))
          (fun _ => rfl))⟩

/-- **The torus reading of the corner observable** is the density of the corner holonomy
(`PeriodicContent.torusObs_iplaqObs`, `plaqMod_cornerIPlaq`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem torusObs_cornerObs (j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (W : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) :
    torusObs (2 * j + 1)
        ((cornerObs (N := N) j k : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) W
      = MassGap.WilsonAction.wilsonDensity (wilsonHol (bdT (2 * j + 1)) (cornerPlaq k) W) := by
  show torusObs (2 * j + 1)
      (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (cornerIPlaq (2 * j + 1) k)) W = _
  rw [MassGap.PeriodicContent.torusObs_iplaqObs, plaqMod_cornerIPlaq]
  rfl

#print axioms torusObs_cornerObs

/-- **The corner observable reads no box link but `(1, k)`** (`corner_not_mem`,
`HeatBath.wilsonHol_update_of_not_mem`), for a side `n ≤ 2j + 1`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the direction of the read link. -/
theorem cornerObs_readsNot {n j : ℕ} (hnM : n ≤ 2 * j + 1)
    (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) {l : WilsonHypercubic.Link 4 (2 * j + 1 + 1)}
    (hl : InBox n (l.2 - k)) (hne : l ≠ ((1 : Fin 4), k)) :
    ReadsNot j l ((cornerObs (N := N) j k : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
      : C(GibbsSpec.IConf (SU N), ℝ)) := by
  unfold MassGap.KnabeCriterion.ReadsNot
  intro W g
  rw [torusObs_cornerObs, torusObs_cornerObs,
    MassGap.HeatBath.wilsonHol_update_of_not_mem (bdT (2 * j + 1)) (cornerPlaq k)
      (corner_not_mem hnM k hl hne) W g]

#print axioms cornerObs_readsNot

/-- The configuration with the identity on every link.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the group
identity. -/
def oneConf (M : ℕ) : WilsonHypercubic.Link 4 (M + 1) → SU N := fun _ => 1

/-- **At the identity configuration the corner observable reads the density of `1`.**

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the group identity. -/
theorem torusObs_cornerObs_one (j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    torusObs (2 * j + 1)
        ((cornerObs (N := N) j k : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) (oneConf (N := N) (2 * j + 1))
      = MassGap.WilsonAction.wilsonDensity (1 : SU N) := by
  rw [torusObs_cornerObs]
  exact congrArg MassGap.WilsonAction.wilsonDensity
    (hol_cornerPlaq_eq k (oneConf (N := N) (2 * j + 1)) rfl rfl rfl)

#print axioms torusObs_cornerObs_one

/-- **Changing the link `(1, k)` alone to `g` makes the corner observable read the density of `g`**
(`hol_cornerPlaq_eq`; the other three links differ from `(1, k)` by direction or, at extent at least
`2`, by base site: `cornerSite_ne`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the direction of the changed link. -/
theorem torusObs_cornerObs_update (j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (g : SU N) :
    torusObs (2 * j + 1)
        ((cornerObs (N := N) j k : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
          : C(GibbsSpec.IConf (SU N), ℝ)) (Function.update (oneConf (N := N) (2 * j + 1)) ((1 : Fin 4), k) g)
      = MassGap.WilsonAction.wilsonDensity g := by
  have hne0 : ((0 : Fin 4), cornerSite k) ≠ ((1 : Fin 4), k) :=
    fun h => (by decide : (0 : Fin 4) ≠ 1) (congrArg Prod.fst h)
  have hne1 : ((0 : Fin 4), WilsonHypercubic.shift 1 (cornerSite k)) ≠ ((1 : Fin 4), k) :=
    fun h => (by decide : (0 : Fin 4) ≠ 1) (congrArg Prod.fst h)
  have hne2 : ((1 : Fin 4), cornerSite k) ≠ ((1 : Fin 4), k) :=
    fun h => cornerSite_ne k (by omega) (congrArg Prod.snd h)
  have hU := hol_cornerPlaq_eq k (Function.update (oneConf (N := N) (2 * j + 1)) ((1 : Fin 4), k) g)
    (Function.update_of_ne hne0 g (oneConf (N := N) (2 * j + 1)))
    (Function.update_of_ne hne1 g (oneConf (N := N) (2 * j + 1)))
    (Function.update_of_ne hne2 g (oneConf (N := N) (2 * j + 1)))
  rw [torusObs_cornerObs, hU, Function.update_self]

#print axioms torusObs_cornerObs_update

end Observable

/-! ## 4. A heat-bath complement is not null when the observable reads the link -/

section Positive

variable {N : ℕ}

/-- **The Gibbs integral of a square that is somewhere non-zero is positive**: `Φ` continuous,
`Φ V₀ ≠ 0` give `0 < ∫ Φ² · wt` against product Haar (open positivity, `Continuous.ae_eq_iff_eq`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent; `0` is the value
excluded at `V₀` and the sign asserted. -/
theorem integral_sq_wt_pos (β : ℝ) (M : ℕ)
    (Φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ) (hΦ : Continuous Φ)
    (V₀ : WilsonHypercubic.Link 4 (M + 1) → SU N) (hV₀ : Φ V₀ ≠ 0) :
    0 < ∫ V, Φ V * Φ V * wt (bdT M) β V
      ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) := by
  haveI : (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)).IsOpenPosMeasure :=
    inferInstance
  have hcont : Continuous (fun V => Φ V * Φ V * wt (bdT M) β V) :=
    (hΦ.mul hΦ).mul (continuous_wt (bdT M) β)
  have hnn : (0 : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ)
      ≤ fun V => Φ V * Φ V * wt (bdT M) β V :=
    fun V => mul_nonneg (mul_self_nonneg _) (wt_pos (bdT M) β V).le
  obtain ⟨C, hC⟩ := MassGap.HeatBath.exists_abs_le hcont
  have hint : Integrable (fun V => Φ V * Φ V * wt (bdT M) β V)
      (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) :=
    MassGap.HeatBath.integrable_of_abs_le _ hcont.measurable hC
  refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => hV₀ ?_)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
  have hzero := (Continuous.ae_eq_iff_eq
    (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))
    hcont continuous_const).mp hae
  have hV : Φ V₀ * Φ V₀ * wt (bdT M) β V₀ = 0 := congrFun hzero V₀
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp hV).resolve_right (wt_pos (bdT M) β V₀).ne')

#print axioms integral_sq_wt_pos

/-- **A heat-bath complement is not null when the observable reads the link.** If the torus reading
of `x` at `W` changes when the link `l` alone is set to `g`, then
`torusForm(x − Eₗx, x − Eₗx) > 0`: a null complement vanishes at every configuration
(`integral_sq_wt_pos`), so the reading equals its heat bath, which does not read `l`
(`HeatBath.heatAvg_update`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the excluded rank in `hN` and the sign asserted. -/
theorem torusForm_sub_condExp_pos (hN : N ≠ 0) (β : ℝ) (j : ℕ)
    (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
    (W : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) (g : SU N)
    (hne : torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) (Function.update W l g)
      ≠ torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W) :
    0 < torusForm hN β j (x - torusCondExp β (2 * j + 1) l x) (x - torusCondExp β (2 * j + 1) l x) := by
  have hD : ∀ V, torusObs (2 * j + 1)
      ((x - torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) V
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - heatAvg (bdT (2 * j + 1)) β l (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V := by
    intro V
    exact congrArg (fun t => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V - t)
      (congrFun (torusObs_heatLift β (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) V)
  have hV0 : ∃ V₀, torusObs (2 * j + 1)
      ((x - torusCondExp β (2 * j + 1) l x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
        : C(GibbsSpec.IConf (SU N), ℝ)) V₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne
    have hfix : ∀ V, torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        = heatAvg (bdT (2 * j + 1)) β l (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V :=
      fun V => sub_eq_zero.mp ((hD V).symm.trans (hall V))
    rw [hfix (Function.update W l g), hfix W, heatAvg_update]
  obtain ⟨V₀, hV₀⟩ := hV0
  have hZ := MassGap.WilsonReal.wilsonSystem_partition_pos hN (bdT (2 * j + 1)) β
  rw [MassGap.BoxGap.torusForm_eq_integral]
  exact div_pos (integral_sq_wt_pos β (2 * j + 1) _ (continuous_torusObs _ _) V₀ hV₀) hZ

#print axioms torusForm_sub_condExp_pos

/-- `wilsonDensity` separates two elements of different real trace, at `N ≠ 0`.

DERIVED: `0` is the excluded rank; `1` is the density's normalisation. -/
theorem wilsonDensity_ne_of_reTr_ne (hN : N ≠ 0) {g h : SU N}
    (hgh : MassGap.HaarVariance.reTr g ≠ MassGap.HaarVariance.reTr h) :
    MassGap.WilsonAction.wilsonDensity g ≠ MassGap.WilsonAction.wilsonDensity h := by
  intro heq
  apply hgh
  have hN' : (1 / (N : ℝ)) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr hN)
  unfold MassGap.WilsonAction.wilsonDensity at heq
  have h2 : (1 / (N : ℝ)) * MassGap.HaarVariance.reTr g
      = (1 / (N : ℝ)) * MassGap.HaarVariance.reTr h := by
    unfold MassGap.HaarVariance.reTr
    linarith
  exact mul_left_cancel₀ hN' h2

#print axioms wilsonDensity_ne_of_reTr_ne

/-- **At `2 ≤ N` some element of `SU(N)` has real trace different from the identity's**
(`HaarVariance.flipEl`, `HaarVariance.reTr_flipEl_ne_reTr_one`).

DERIVED: `2` is the least rank with the diagonal witness; `1` is the group identity. -/
theorem exists_reTr_ne_one (hN2 : 2 ≤ N) :
    ∃ g : SU N, MassGap.HaarVariance.reTr g ≠ MassGap.HaarVariance.reTr (1 : SU N) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact ⟨MassGap.HaarVariance.flipEl m, MassGap.HaarVariance.reTr_flipEl_ne_reTr_one m⟩

#print axioms exists_reTr_ne_one

end Positive

/-! ## 5. The ceiling -/

section Ceiling

variable {N : ℕ}

/-- **The box operator on the corner observable pairs as one complement.** For `1 ≤ n ≤ j + 1`:
`torusForm(A x, y) = torusForm(x − E x, y)` for every `y`, with `x = cornerObs j k`,
`A = boxOp β n j k`, `E = torusCondExp` at `(1, k)`: every other box link `l` has `x − Eₗx` null
(`cornerObs_readsNot`, `HeatBath.torusCondExp_keeps`, `HeatBathLocal.null_of_torusObs_eq`,
`form_finsetSum_eq_single`, `BoxGap.boxOp_apply`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the least side, the successor in `j + 1` and the
direction of the corner link; `0` is the excluded rank in `hN`. -/
theorem corner_boxOp_form (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n) (hnj : n ≤ j + 1)
    (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    torusForm hN β j (boxOp β n j k (cornerObs (N := N) j k)) y
      = torusForm hN β j (cornerObs (N := N) j k
          - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k)) y := by
  rw [MassGap.BoxGap.boxOp_apply]
  exact form_finsetSum_eq_single (torusForm hN β j) (torusForm_symm hN β j)
    (torusForm_nonneg hN β j)
    (fun l => cornerObs (N := N) j k - torusCondExp β (2 * j + 1) l (cornerObs (N := N) j k))
    (MassGap.BoxGap.boxLinks n k) (corner_mem_boxLinks hn k)
    (fun l hl hne => MassGap.HeatBathLocal.null_of_torusObs_eq hN β j (cornerObs (N := N) j k)
      (torusCondExp β (2 * j + 1) l (cornerObs (N := N) j k))
      (torusCondExp_keeps β j l (cornerObs (N := N) j k)
        (cornerObs_readsNot (by omega) k (inBox_of_mem_boxLinks hl) hne)).symm) y

#print axioms corner_boxOp_form

/-- **The local-gap inequality at the corner observable forces `γ ≤ 1`.** At `2 ≤ N`,
`1 ≤ n ≤ j + 1`: both sides of `γ·torusForm(Ax, x) ≤ torusForm(Ax, Ax)` equal
`v = torusForm(x − E x, x − E x)` (`corner_boxOp_form`, `KnabeCriterion.form_proj_self` for the
self-adjoint idempotent `id − E`), and `v > 0` (`torusForm_sub_condExp_pos` at the identity
configuration and a second element of different real trace on `(1, k)`).

DERIVED: `2` is the least rank with two traces; `1` is the ceiling, the least side, the successor in
`j + 1` and the direction of the corner link; `4` is the spacetime dimension; `2 * j + 1` is the index
of the even-extent family and the `+ 1` its successor writing the extent; `0` is the excluded rank in
`hN`. -/
theorem le_one_of_corner (hN2 : 2 ≤ N) (hN : N ≠ 0) (β : ℝ) {n j : ℕ} (hn : 1 ≤ n)
    (hnj : n ≤ j + 1) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) {γ : ℝ}
    (hloc : γ * torusForm hN β j (boxOp β n j k (cornerObs (N := N) j k)) (cornerObs (N := N) j k)
      ≤ torusForm hN β j (boxOp β n j k (cornerObs (N := N) j k))
          (boxOp β n j k (cornerObs (N := N) j k))) :
    γ ≤ 1 := by
  obtain ⟨g, hg⟩ := exists_reTr_ne_one (N := N) hN2
  have hP := form_proj_self (torusForm hN β j)
    ((LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)))
      - torusCondExp β (2 * j + 1) ((1 : Fin 4), k))
    (selfAdj_id_sub (torusForm hN β j) (torusCondExp β (2 * j + 1) ((1 : Fin 4), k))
      (torusCondExp_selfAdj hN β j ((1 : Fin 4), k)))
    (idem_id_sub (torusCondExp β (2 * j + 1) ((1 : Fin 4), k))
      (torusCondExp_idem β (2 * j + 1) ((1 : Fin 4), k)))
    (cornerObs (N := N) j k)
  simp only [LinearMap.sub_apply, LinearMap.id_apply] at hP
  have hpos := torusForm_sub_condExp_pos hN β j ((1 : Fin 4), k) (cornerObs (N := N) j k)
    (oneConf (N := N) (2 * j + 1)) g (by
      rw [torusObs_cornerObs_update, torusObs_cornerObs_one]
      exact wilsonDensity_ne_of_reTr_ne hN hg)
  have hv1 : torusForm hN β j (boxOp β n j k (cornerObs (N := N) j k)) (cornerObs (N := N) j k)
      = torusForm hN β j
          (cornerObs (N := N) j k - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k))
          (cornerObs (N := N) j k - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k)) :=
    (corner_boxOp_form hN β hn hnj k (cornerObs (N := N) j k)).trans hP
  have hv2 : torusForm hN β j (boxOp β n j k (cornerObs (N := N) j k))
        (boxOp β n j k (cornerObs (N := N) j k))
      = torusForm hN β j
          (cornerObs (N := N) j k - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k))
          (cornerObs (N := N) j k - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k)) :=
    (corner_boxOp_form hN β hn hnj k (boxOp β n j k (cornerObs (N := N) j k))).trans
      ((torusForm_symm hN β j _ _).trans
        (corner_boxOp_form hN β hn hnj k
          (cornerObs (N := N) j k
            - torusCondExp β (2 * j + 1) ((1 : Fin 4), k) (cornerObs (N := N) j k))))
  exact gap_le_one_of_eq hv1 hv2 hpos hloc

#print axioms le_one_of_corner

/-- **THE BOX LOCAL GAP NEVER EXCEEDS `1`.** At `2 ≤ N`, every real `β` and every side `n ≥ 1`:
`BoxLocalGap hN β n γ → γ ≤ 1` (`le_one_of_corner` at the extent index `j = n` and the corner `0`).

DERIVED: `2` is the least rank with two traces (`PlaqVariance.wilsonDensity_su_one` makes every
density `0` at `N = 1`); `1` is the ceiling and the least side (at `n = 0` the box is empty and every
`γ` is a local gap); `0` is the excluded rank in `hN`. -/
theorem boxLocalGap_le_one (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} {n : ℕ} {γ : ℝ} (hn : 1 ≤ n)
    (h : BoxLocalGap hN β n γ) : γ ≤ 1 :=
  le_one_of_corner hN2 hN β hn (Nat.le_succ n) (0 : WilsonHypercubic.Site 4 (2 * n + 1 + 1))
    (h n (Nat.le_succ n) 0 (cornerObs (N := N) n 0))

#print axioms boxLocalGap_le_one

/-- **The box check needs side at least `40`.** At `2 ≤ N` and every real `β`:
`BoxPatchGap hN β n γ → 40 ≤ n`: `γ ≤ 1` (`boxLocalGap_le_one`) and `(40n − 36)/n² < γ` give
`(40n − 36)/n² < 1`, which holds exactly from `n = 40` on (`BoxGap.threshold_lt_one_iff`).

DERIVED: `40` is the least side with `(40n − 36)/n² < 1` (`BoxGap.threshold_lt_one_iff`); `2` is the
least rank with two traces; `0` is the excluded rank in `hN`. -/
theorem boxPatchGap_side_ge_forty (hN2 : 2 ≤ N) (hN : N ≠ 0) {β γ : ℝ} {n : ℕ}
    (h : BoxPatchGap hN β n γ) : 40 ≤ n := by
  obtain ⟨hn2, hthr, hloc⟩ := h
  exact (MassGap.BoxGap.threshold_lt_one_iff (by omega)).mp
    (lt_of_lt_of_le hthr (boxLocalGap_le_one hN2 hN (by omega) hloc))

#print axioms boxPatchGap_side_ge_forty

/-- **At `β = 0` the box check at gap `1` holds exactly from side `40` on**
(`boxPatchGap_side_ge_forty`, `BoxGap.boxPatchGap_zero`).

DERIVED: `0` is the coupling and the excluded rank in `hN`; `1` is the gap, the ceiling of
`boxLocalGap_le_one`; `40` is the least side (`BoxGap.threshold_lt_one_iff`); `2` is the least rank
with two traces. -/
theorem boxPatchGap_zero_one_iff (hN2 : 2 ≤ N) (hN : N ≠ 0) {n : ℕ} :
    BoxPatchGap hN 0 n 1 ↔ 40 ≤ n :=
  ⟨boxPatchGap_side_ge_forty hN2 hN, MassGap.BoxGap.boxPatchGap_zero hN⟩

#print axioms boxPatchGap_zero_one_iff

end Ceiling

end MassGap.BoxCeiling
