import Mathlib
import MassGap.PeriodicState
import MassGap.PeriodicReduce
import MassGap.ContactFloor

/-!
# MassGap.PeriodicContent — a non-zero vacuum complement at the periodic state, and the Clay statement from the reads alone

`PeriodicState.periodic_clay_gap_of_reads` gives the Clay spectral statement at
`periodicGaugeInvData τ p hN β` from the reads, at every `β ≥ 0`, without saying that the vacuum
complement of the GNS space is non-zero. This module supplies that conjunct at `2 ≤ N`, `0 ≤ β`, and
assembles `PeriodicClayGapAt`, the periodic analogue of `ReadRoute.ClayGapAt`: the spectral
statement, the contraction of the vacuum complement by `ρ` that the reads give
(`GNSCompare.gapAt_iff_opT_contracts`), and the non-zero vector.

## The floor on every periodic lattice

`torusState_var_iplaqObs_ge`: at `2 ≤ N` and `0 ≤ β`, for a plaquette `q` with two distinct
directions and every extent `M + 1 ≥ 2`, the variance of the plaquette observable `iplaqObs q` under
`torusState hN M β` is at least `e^{−128β} · varReTr N / N²`, with no extent in the bound.

* `torusState_var_eq` identifies that variance with `WilsonBridge.wilsonCorrConn` of the reduced
  plaquette `plaqMod M q` on the periodic lattice (`InfiniteLattice.wilsonHol_periodic`).
* `ContactFloor.wilsonCorrConn_self_ge_haar` bounds it below by `e^{−2β·|touchNbrs|}` times its
  coupling-zero value — the weight of the plaquettes sharing a link with `q` lies in
  `[e^{−2β|touch|}, 1]` and the rest factors off under product Haar — and
  `StrongCoupling.touchDeg_bd_le` caps `|touchNbrs|` at `16 · 4 = 64`.
* `torus_haar_var_ge` bounds the coupling-zero value below by `varReTr N / N²`: the observable reads
  the plaquette's first link through `g ↦ wilsonDensity (g · W)` with `W` built from the other three
  links. The plaquette's other three links differ from its first: two by direction
  (`q.1.1 ≠ q.1.2`), and `(q.1.1, x + q.1.2)`, `x = q.2`, by site once the extent is at least `2`
  (`shift_ne_self`). `PlaneVariance.integral_shift_factor` integrates the first link out by right
  invariance of Haar, and `PlaneVariance.integral_wilsonDensity_centred_ge` bounds the remaining Haar
  integral.

`periodicState_var_iplaqObs_ge` carries the floor to `periodicState hN β` along `periodicUltra hN β`,
which is where the extent-uniformity is consumed.

## The vector

`exists_ne_zero_orth_vacuum_of_fixed`: at any state with the three facts of `gaugeInvTransferData`,
an observable `φ` of the gauge-invariant algebra fixed by the reflection and with positive variance
gives the non-zero class of `φ − ν(φ)·1`, orthogonal to the vacuum. `planePlaq τ p` is a plaquette in
the reflection plane `x_τ = p` with neither direction `τ`, so `ireflObs τ (2p)` fixes its observable
(`PlaneVariance.ireflPlaq_plane`); `periodic_exists_ne_zero_orth_vacuum` is the vector at
`periodicGaugeInvData`.

## What it gives

`periodic_clayGapAt_of_reads` and the headline `wilson_gaugeInv_mass_gap_every_coupling_periodic`:
at `2 ≤ N`, if at every `β > 0` some aperture's reads clear at `periodicGaugeInvData τ p hN β`, then
at every `β > 0` there is `ρ` with `PeriodicClayGapAt τ p hN β ρ`. The reads are the only hypothesis
besides the rank; the state is `periodicState hN β`, defined in `PeriodicState` (a limit along an
ultrafilter fixed by `Classical.choose`), not a hypothesis. `periodic_clayGapAt_of_torusReads` takes
the reads in the form `PeriodicReduce.TorusReadsClearWith`, one inequality per observable on the
periodic lattices.

## Scope

The floor makes the vacuum complement of the GNS space at `periodicState hN β` non-zero, which is the
last conjunct of `PeriodicClayGapAt` and nothing more. Nothing here shows that `periodicState hN β`
at `β > 0` differs from the `β = 0` state — the same floor holds at `β = 0`, with factor `1` — so it
is not a statement that the theory is non-trivial. Nothing here proves the reads, or
`TorusReadsClearWith`, at any `β > 0`. Nothing here shows the reads can hold at every `β > 0`: at a
coupling where `opT` at `periodicState hN β` has `1` as a degenerate eigenvalue, as a limit mixing
two phases would give, `ReadsClear` fails, since it implies the contraction of
`PeriodicState.periodic_gap_of_reads`.
-/

namespace MassGap.PeriodicContent

open MeasureTheory
open MassGap MassGap.GNSHilbert MassGap.PeriodicState

variable {N : ℕ}

/-! ## 1. The plaquette on the periodic lattice -/

section Torus

/-- **A periodic step moves every site once the extent is at least `2`**: `shift μ x ≠ x` on the
periodic lattice of extent `M + 1`, `1 ≤ M`. At extent `1` it fails.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent `M + 1` and the
least `M` at which the extent is at least `2`. -/
theorem shift_ne_self (M : ℕ) (hM : 1 ≤ M) (μ : Fin 4)
    (x : MassGap.WilsonHypercubic.Site 4 (M + 1)) : MassGap.WilsonHypercubic.shift μ x ≠ x := by
  intro h
  have h1 := congrFun h μ
  rw [MassGap.WilsonHypercubic.shift, Function.update_self] at h1
  have h3 : x μ + 1 = x μ + 0 := by rw [add_zero]; exact h1
  have h2 : (1 : Fin (M + 1)) = 0 := add_left_cancel h3
  have h4 : ((1 : Fin (M + 1)) : ℕ) = ((0 : Fin (M + 1)) : ℕ) := congrArg Fin.val h2
  have h5 : ((1 : Fin (M + 1)) : ℕ) = 1 % (M + 1) := Fin.val_one' (M + 1)
  have h6 : ((0 : Fin (M + 1)) : ℕ) = 0 := rfl
  have h7 : 1 % (M + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  first
    | omega
    | (rw [h5, h7, h6] at h4; exact absurd h4 one_ne_zero)

#print axioms shift_ne_self

/-- **A periodic plaquette's holonomy is its first link times the product of the other three**:
`U(q.1.1, x) · (U(q.1.2, x + q.1.1) · (U(q.1.1, x + q.1.2)⁻¹ · U(q.1.2, x)⁻¹))`, `x = q.2`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent `M + 1`; `1` and `2`
are also the product projections. -/
theorem hol_torus_eq (M : ℕ) (q : MassGap.WilsonHypercubic.Plaq 4 (M + 1))
    (U : MassGap.WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    MassGap.WilsonLattice.wilsonHol (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q U
      = U (q.1.1, q.2) * (U (q.1.2, MassGap.WilsonHypercubic.shift q.1.1 q.2)
          * ((U (q.1.1, MassGap.WilsonHypercubic.shift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹)) := by
  first
    | simp [MassGap.WilsonLattice.wilsonHol, MassGap.WilsonHypercubic.bd]
    | (unfold MassGap.WilsonLattice.wilsonHol MassGap.WilsonHypercubic.bd
       simp [List.prod_cons])

#print axioms hol_torus_eq

/-- **The Haar floor on the periodic lattice, about any centre.** At extent `M + 1 ≥ 2`, for a
plaquette `q` with two distinct directions and every real `c`:
`varReTr N / N² ≤ ∫ (wilsonPlaqObs q − c)²` under product Haar on the links.

The plaquette's other three links differ from its first: two by direction (`q.1.1 ≠ q.1.2`), and
`(q.1.1, x + q.1.2)`, `x = q.2`, by site once the extent is at least `2` (`shift_ne_self`). So the
observable is `g ↦ wilsonDensity (g · W)` in the first link with `W` not reading it (`hol_torus_eq`);
`PlaneVariance.integral_shift_factor` integrates the first link out, and
`PlaneVariance.integral_wilsonDensity_centred_ge` bounds the Haar integral that remains.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the least `M`
at which it is at least `2`; `2` is the square's exponent and, in `N²`, `wilsonDensity`'s
normalisation `1/N` squared; `0` is the excluded rank in `hN`. -/
theorem torus_haar_centred_ge (hN : N ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    (q : MassGap.WilsonHypercubic.Plaq 4 (M + 1)) (hq : q.1.1 ≠ q.1.2) (c : ℝ) :
    MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2
      ≤ ∫ W, (MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q W - c) ^ 2
          ∂((MassGap.WilsonLattice.wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
              (MassGap.WilsonAction.wilsonDensity (N := N))).vol
            (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := by
  have hvol : (MassGap.WilsonLattice.wilsonSystem (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
        (MassGap.WilsonAction.wilsonDensity (N := N))).vol
        (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))
      = MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link 4 (M + 1))
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) := rfl
  rw [hvol]
  -- the plaquette's other three links are not its first
  have hne1 : ((q.1.2, MassGap.WilsonHypercubic.shift q.1.1 q.2) :
      MassGap.WilsonHypercubic.Link 4 (M + 1)) ≠ (q.1.1, q.2) :=
    fun h => hq (congrArg Prod.fst h).symm
  have hne2 : ((q.1.1, MassGap.WilsonHypercubic.shift q.1.2 q.2) :
      MassGap.WilsonHypercubic.Link 4 (M + 1)) ≠ (q.1.1, q.2) :=
    fun h => shift_ne_self M hM q.1.2 q.2 (congrArg Prod.snd h)
  have hne3 : ((q.1.2, q.2) : MassGap.WilsonHypercubic.Link 4 (M + 1)) ≠ (q.1.1, q.2) :=
    fun h => hq (congrArg Prod.fst h).symm
  -- measurability and bounds
  have hKm : Measurable
      (fun g : MassGap.SUN.SU N => (MassGap.WilsonAction.wilsonDensity g - c) ^ 2) :=
    (MassGap.WilsonAction.measurable_wilsonDensity.sub_const c).pow_const 2
  have hKb : ∀ g : MassGap.SUN.SU N,
      |(MassGap.WilsonAction.wilsonDensity g - c) ^ 2| ≤ (2 + |c|) ^ 2 := by
    intro g
    have h0 := MassGap.WilsonAction.wilsonDensity_nonneg hN g
    have h2 := MassGap.WilsonAction.wilsonDensity_le_two hN g
    rw [abs_of_nonneg (sq_nonneg _)]
    have := neg_abs_le c
    have := le_abs_self c
    nlinarith
  have hWm : Measurable
      (fun u : MassGap.WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N =>
        u (q.1.2, MassGap.WilsonHypercubic.shift q.1.1 q.2)
          * ((u (q.1.1, MassGap.WilsonHypercubic.shift q.1.2 q.2))⁻¹ * (u (q.1.2, q.2))⁻¹)) :=
    (measurable_pi_apply _).mul ((measurable_pi_apply _).inv.mul (measurable_pi_apply _).inv)
  -- integrate the first link out
  have hfac := MassGap.PlaneVariance.integral_shift_factor
    (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))
    ((q.1.1, q.2) : MassGap.WilsonHypercubic.Link 4 (M + 1)) hKm hKb hWm
    (fun u g => by
      simp only [Function.update_of_ne hne1, Function.update_of_ne hne2,
        Function.update_of_ne hne3])
    (B := fun _ => (1 : ℝ)) measurable_const (CB := 1) (fun _ => by simp) (fun _ _ => rfl)
  calc MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2
      ≤ ∫ g, (MassGap.WilsonAction.wilsonDensity g - c) ^ 2
          ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) :=
        MassGap.PlaneVariance.integral_wilsonDensity_centred_ge hN c
    _ = (∫ g, (MassGap.WilsonAction.wilsonDensity g - c) ^ 2
            ∂(MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
          * ∫ _u, (1 : ℝ) ∂(MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link 4 (M + 1))
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := by
        rw [MassGap.ContactFloor.integral_const_prob
          (MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link 4 (M + 1))
            (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) (1 : ℝ), mul_one]
    _ = ∫ u, (MassGap.WilsonAction.wilsonDensity (u (q.1.1, q.2)
            * (u (q.1.2, MassGap.WilsonHypercubic.shift q.1.1 q.2)
              * ((u (q.1.1, MassGap.WilsonHypercubic.shift q.1.2 q.2))⁻¹
                * (u (q.1.2, q.2))⁻¹))) - c) ^ 2 * 1
          ∂(MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link 4 (M + 1))
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := hfac.symm
    _ = ∫ W, (MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q W - c) ^ 2
          ∂(MassGap.ActionSplit.cvol (MassGap.WilsonHypercubic.Link 4 (M + 1))
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        show (MassGap.WilsonAction.wilsonDensity (u (q.1.1, q.2)
            * (u (q.1.2, MassGap.WilsonHypercubic.shift q.1.1 q.2)
              * ((u (q.1.1, MassGap.WilsonHypercubic.shift q.1.2 q.2))⁻¹
                * (u (q.1.2, q.2))⁻¹))) - c) ^ 2 * 1
          = (MassGap.WilsonAction.wilsonDensity (MassGap.WilsonLattice.wilsonHol
              (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q u) - c) ^ 2
        rw [hol_torus_eq, mul_one]

#print axioms torus_haar_centred_ge

/-- **The coupling-zero plaquette variance on the periodic lattice is at least `varReTr N / N²`**,
at extent `M + 1 ≥ 2` and a plaquette with two distinct directions:
`varReTr N / N² ≤ wilsonCorrConn bd q 0 q`. `ContactFloor.wilsonCorrConn_self_at_zero` writes the
coupling-zero self-correlation as the product-Haar second moment of `wilsonPlaqObs q` about its Haar
mean, and `torus_haar_centred_ge` bounds that moment.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the least `M`
at which it is at least `2`; `2` in `N²` is `wilsonDensity`'s normalisation squared; `0` is the
excluded rank in `hN` and the coupling. -/
theorem torus_haar_var_ge (hN : N ≠ 0) (M : ℕ) (hM : 1 ≤ M)
    (q : MassGap.WilsonHypercubic.Plaq 4 (M + 1)) (hq : q.1.1 ≠ q.1.2) :
    MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2
      ≤ MassGap.WilsonBridge.wilsonCorrConn (Nc := N)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q 0 q := by
  rw [MassGap.ContactFloor.wilsonCorrConn_self_at_zero hN
    (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) q]
  exact torus_haar_centred_ge hN M hM q hq _

#print axioms torus_haar_var_ge

/-- **A plaquette observable on `ℤ⁴`, read on the periodic lattice, is the periodic plaquette
observable of the reduced plaquette**: `torusObs M (iplaqObs q) = wilsonPlaqObs bd (plaqMod M q)`
pointwise. `InfiniteLattice.wilsonHol_periodic`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent `M + 1`. -/
theorem torusObs_iplaqObs (M : ℕ) (q : MassGap.GibbsSpec.IPlaq)
    (W : MassGap.WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q) W
      = MassGap.WilsonReal.wilsonPlaqObs (N := N)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.InfiniteLattice.plaqMod M q) W := by
  show MassGap.WilsonAction.wilsonDensity (MassGap.WilsonLattice.wilsonHol
      MassGap.InfiniteLattice.ibd q (fun l => W (MassGap.InfiniteLattice.linkMod M l)))
    = MassGap.WilsonAction.wilsonDensity (MassGap.WilsonLattice.wilsonHol
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) (MassGap.InfiniteLattice.plaqMod M q) W)
  rw [MassGap.InfiniteLattice.wilsonHol_periodic]

#print axioms torusObs_iplaqObs

/-- **The plaquette variance under a periodic state is the periodic connected self-correlation**:
`torusState hN M β (φ_q · φ_q) − (torusState hN M β φ_q)² = wilsonCorrConn bd q' β q'`,
`q' = plaqMod M q`, `φ_q = iplaqObs q`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent `M + 1`; `0` is the
excluded rank in `hN`; `2` is the square. -/
theorem torusState_var_eq (hN : N ≠ 0) (M : ℕ) (β : ℝ) (q : MassGap.GibbsSpec.IPlaq) :
    torusState hN M β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
          * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
        - (torusState hN M β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2
      = MassGap.WilsonBridge.wilsonCorrConn (Nc := N)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.InfiniteLattice.plaqMod M q) β (MassGap.InfiniteLattice.plaqMod M q) := by
  have h1 : torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
        * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
      = fun W => MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
            (MassGap.InfiniteLattice.plaqMod M q) W
          * MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
            (MassGap.InfiniteLattice.plaqMod M q) W := by
    funext W
    show torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q) W
        * torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q) W = _
    rw [torusObs_iplaqObs]
  have h2 : torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
      = MassGap.WilsonReal.wilsonPlaqObs (N := N)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.InfiniteLattice.plaqMod M q) :=
    funext (torusObs_iplaqObs M q)
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
        (torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
          * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q))
      - (MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
          (torusObs M (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q))) ^ 2 = _
  rw [h1, h2, sq]
  rfl

#print axioms torusState_var_eq

/-- **The plaquette variance on every periodic lattice is at least `e^{−128β} · varReTr N / N²`.**
At `2 ≤ N`, `0 ≤ β`, extent `M + 1 ≥ 2`, and a plaquette `q` with two distinct directions:
`e^{−128β} · varReTr N / N² ≤ torusState hN M β (φ_q · φ_q) − (torusState hN M β φ_q)²`. The bound
carries no extent. It holds at `β = 0` with factor `1`, so it gives a non-zero vacuum complement and
does not distinguish `β > 0` from `β = 0`.

`torusState_var_eq`, then `ContactFloor.wilsonCorrConn_self_ge_haar` (the factor
`e^{−2β·|touchNbrs|}`), `StrongCoupling.touchDeg_bd_le` (`|touchNbrs| ≤ 64`) and `torus_haar_var_ge`
(the coupling-zero value).

DERIVED: `128 = 2 · 16 · 4` — `StrongCoupling.touchDeg_bd_le` bounds the plaquettes sharing a link
with `q` by `16 · dim`, `64` at `dim = 4`, and `WilsonAction.wilsonDensity_le_two`'s cap `2` on a
plaquette density is the `2`; `2` is also the least rank with a non-zero Haar variance of the real
trace (`PlaneVariance.varReTr_pos`) and the square; `0` is the excluded rank in `hN` and the sign of
`β`; `1` is the successor writing the extent and the least `M` at which it is at least `2`; `4` is
the spacetime dimension. `64` bounds the number of plaquettes touching one of `q`'s four links, the
route `ContactFloor` takes; `PlaneVariance.stateFree_var_iplaqObs_ge` conditions on the first link
only and carries `32 = 2 · 16` in the free boxes. Only the sign of the floor is used downstream.
`2 ≤ N` enters through `0 ≤ varReTr N / N²` (`PlaneVariance.varReTr_pos`). -/
theorem torusState_var_iplaqObs_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (M : ℕ)
    (hM : 1 ≤ M) (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) :
    Real.exp (-(128 * β)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2)
      ≤ torusState hN M β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
            * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
        - (torusState hN M β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2 := by
  refine le_of_le_of_eq ?_ (torusState_var_eq hN M β q).symm
  have hq' : (MassGap.InfiniteLattice.plaqMod M q).1.1
      ≠ (MassGap.InfiniteLattice.plaqMod M q).1.2 := hq
  have hcard : (MassGap.StrongCoupling.touchNbrs
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
      (MassGap.InfiniteLattice.plaqMod M q)).card ≤ 64 := by
    have h1 := MassGap.StrongCoupling.touchNbrs_card_le_touchDeg
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) (MassGap.InfiniteLattice.plaqMod M q)
    have h2 := MassGap.StrongCoupling.touchDeg_bd_le (dim := 4) (n := M + 1)
    omega
  have hK : ((MassGap.StrongCoupling.touchNbrs
      (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
      (MassGap.InfiniteLattice.plaqMod M q)).card : ℝ) ≤ 64 := by
    exact_mod_cast hcard
  have hbase := MassGap.ContactFloor.wilsonCorrConn_self_ge_haar (Nc := N) hN
    (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1)) (MassGap.InfiniteLattice.plaqMod M q) hβ
  have hV0 := torus_haar_var_ge hN M hM (MassGap.InfiniteLattice.plaqMod M q) hq'
  have hvar0 : 0 ≤ MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2 :=
    (div_pos (MassGap.PlaneVariance.varReTr_pos hN2)
      (pow_pos (Nat.cast_pos.mpr (by omega)) 2)).le
  have hexp : Real.exp (-(128 * β))
      ≤ Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs
          (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
          (MassGap.InfiniteLattice.plaqMod M q)).card : ℝ))) := by
    rw [Real.exp_le_exp]
    nlinarith [hK, hβ, mul_nonneg hβ (sub_nonneg.mpr hK)]
  calc Real.exp (-(128 * β)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2)
      ≤ Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
            (MassGap.InfiniteLattice.plaqMod M q)).card : ℝ)))
          * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hexp hvar0
    _ ≤ Real.exp (-(2 * β * ((MassGap.StrongCoupling.touchNbrs
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
            (MassGap.InfiniteLattice.plaqMod M q)).card : ℝ)))
          * MassGap.WilsonBridge.wilsonCorrConn (Nc := N)
            (MassGap.WilsonHypercubic.bd (d := 4) (n := M + 1))
            (MassGap.InfiniteLattice.plaqMod M q) 0 (MassGap.InfiniteLattice.plaqMod M q) :=
        mul_le_mul_of_nonneg_left hV0 (Real.exp_pos _).le
    _ ≤ _ := hbase

#print axioms torusState_var_iplaqObs_ge

end Torus

/-! ## 2. The floor at the periodic state -/

section Limit

/-- **The plaquette variance under `periodicState hN β` is at least `e^{−128β} · varReTr N / N²`**,
at `2 ≤ N`, `0 ≤ β`, for a plaquette `q` with two distinct directions. Both moments converge along
`periodicUltra hN β` (`PeriodicState.tendsto_periodicState`) and every periodic state of the family,
extent `2(k + 1) ≥ 2`, satisfies the floor (`torusState_var_iplaqObs_ge`).

The positive variance is what makes the vacuum complement non-zero
(`periodic_exists_ne_zero_orth_vacuum`). It does not distinguish `periodicState hN β` at `β > 0` from
the `β = 0` state.

DERIVED: `128` is `torusState_var_iplaqObs_ge`'s constant `2 · 16 · 4`; `2` is the least rank with a
non-zero Haar variance of the real trace and the square; `0` is the excluded rank and the sign of
`β`. -/
theorem periodicState_var_iplaqObs_ge (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) :
    Real.exp (-(128 * β)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2)
      ≤ periodicState hN β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
            * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)
        - (periodicState hN β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)) ^ 2 := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  have hlim := (tendsto_periodicState hN β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q
      * MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)).sub
    ((tendsto_periodicState hN β (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) q)).pow 2)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall (fun k =>
    torusState_var_iplaqObs_ge hN2 hN hβ (2 * k + 1) (by omega) q hq))

#print axioms periodicState_var_iplaqObs_ge

end Limit

/-! ## 3. A non-zero vector orthogonal to the vacuum -/

section Vector

/-- **A reflection-fixed observable with positive variance gives a non-zero vector orthogonal to the
vacuum.** At a state `ν` with the three facts of `gaugeInvTransferData` (reflection invariance about
`2p`, reflection positivity about `2p` on the half-space algebra, shift invariance along `τ`), let
`φ` be in the gauge-invariant half-space algebra with `ireflObs τ (2p) φ = φ` and
`0 < ν(φ·φ) − ν(φ)²`. Then the class of `φ − ν(φ)·1` in the GNS space is not zero and is orthogonal
to the vacuum.

Its squared norm is `ν(θx · x)` (`GaugeInvariantAlgebra.gaugeInv_form_pow` at `0`), which is the
variance of `φ` since `θx = x`; its pairing with the vacuum is `ν(x) = 0`
(`StrongCouplingGap.inner_vacGNS_mk_gaugeInv`). `PlaneVariance.exists_ne_zero_orth_vacuum` is the
same argument at the free-boundary limit state.

DERIVED: `4` is the spacetime dimension; `2` in `2 * p` is the plane-to-constant doubling and `2` is
the square; `0` is the strict floor on the variance, the zero vector and the vacuum pairing. -/
theorem exists_ne_zero_orth_vacuum_of_fixed (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (φ : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hφmem : φ ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)
    (hθφ : MassGap.LatticeReflection.ireflObs τ (2 * p) φ = φ)
    (hvar : 0 < ν (φ * φ) - (ν φ) ^ 2) :
    ∃ y : MassGap.Transfer.GNS
        (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm,
      y ≠ 0 ∧ (inner ℝ (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).vacGNS
        y : ℝ) = 0 := by
  have hxmem : φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
      ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
    Submodule.sub_mem _ hφmem
      (Submodule.smul_mem _ _ (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p))
  obtain ⟨x, hx⟩ : ∃ x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
        (G := MassGap.SUN.SU N) τ p),
      (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        = φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :=
    ⟨⟨_, hxmem⟩, rfl⟩
  refine ⟨MassGap.Transfer.GNS.mk
    (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm x, ?_, ?_⟩
  · -- non-zero: its squared norm is the variance
    intro h0
    have hθ1 : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 1 := by
      ext U; rfl
    have hθx : MassGap.LatticeReflection.ireflObs τ (2 * p)
          (φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
        = φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) := by
      rw [map_sub, map_smul, hθφ, hθ1]
    have hin := MassGap.Transfer.GNS.inner_mk
      (P := (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm)
      x x
    rw [h0, inner_zero_left] at hin
    have hform := MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu x 0
    have e1 : (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm.form
          x x
        = (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).form x
            (((MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).T ^ 0) x) := by
      first
        | rfl
        | (rw [pow_zero]; rfl)
        | rw [pow_zero]
    have hform' : (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm.form
          x x
        = ν ((φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))
            * (φ - ν φ • (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)))) := by
      rw [e1, hform]
      show ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
          (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
          * (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = _
      rw [hx, hθx]
    have hcent := MassGap.PlaneVariance.state_centred_sq ν φ (ν φ)
    rw [hform', hcent] at hin
    nlinarith [hin, hvar]
  · -- orthogonal to the vacuum
    rw [show (inner ℝ (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).vacGNS
        (MassGap.Transfer.GNS.mk
          (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm x) : ℝ)
        = ν (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) from
      MassGap.StrongCouplingGap.inner_vacGNS_mk_gaugeInv τ p ν hinv hpos hnu x]
    rw [hx, MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_smul,
      MassGap.DLRLimit.State.map_one]
    ring

#print axioms exists_ne_zero_orth_vacuum_of_fixed

/-- The plaquette in the reflection plane: directions `τ + 1`, `τ + 2`, base site with `x_τ = p` and
every other coordinate `0`.

CHOSEN: `1` and `2` in `τ + 1`, `τ + 2` pick two distinct directions other than `τ`, and `0` picks
the base site's other coordinates; any plaquette in the plane `x_τ = p` with neither direction `τ`
and two distinct directions serves. DERIVED: `4` is the spacetime dimension. -/
def planePlaq (τ : Fin 4) (p : ℤ) : MassGap.GibbsSpec.IPlaq :=
  ((τ + 1, τ + 2), fun i => if i = τ then p else 0)

/-- `planePlaq`'s first direction is not `τ`.

DERIVED: `4` is the spacetime dimension; the `1`s are product projections. -/
theorem planePlaq_dir1 (τ : Fin 4) (p : ℤ) : (planePlaq τ p).1.1 ≠ τ := by
  show τ + 1 ≠ τ
  fin_cases τ <;> decide

#print axioms planePlaq_dir1

/-- `planePlaq`'s second direction is not `τ`.

DERIVED: `4` is the spacetime dimension; the `1` and `2` are product projections. -/
theorem planePlaq_dir2 (τ : Fin 4) (p : ℤ) : (planePlaq τ p).1.2 ≠ τ := by
  show τ + 2 ≠ τ
  fin_cases τ <;> decide

#print axioms planePlaq_dir2

/-- `planePlaq`'s two directions are distinct.

DERIVED: `4` is the spacetime dimension; the `1`s and `2` are product projections. -/
theorem planePlaq_nd (τ : Fin 4) (p : ℤ) : (planePlaq τ p).1.1 ≠ (planePlaq τ p).1.2 := by
  show τ + 1 ≠ τ + 2
  fin_cases τ <;> decide

#print axioms planePlaq_nd

/-- `planePlaq`'s base site is on the plane `x_τ = p`.

DERIVED: `4` is the spacetime dimension; `2` is the product projection to the base site. -/
theorem planePlaq_site (τ : Fin 4) (p : ℤ) : (planePlaq τ p).2 τ = p := by
  show (if τ = τ then p else 0) = p
  exact if_pos rfl

#print axioms planePlaq_site

/-- **The vacuum complement at the periodic state is non-zero**: at `2 ≤ N` and `0 ≤ β` there is a
non-zero vector of the GNS space of `periodicGaugeInvData τ p hN β` orthogonal to the vacuum. It is
the class of `φ − ν(φ)·1` for the plane plaquette's observable `φ = iplaqObs (planePlaq τ p)`, which
the reflection fixes (`PlaneVariance.ireflPlaq_plane`) and whose variance under
`periodicState hN β` is at least `e^{−128β} · varReTr N / N² > 0`
(`periodicState_var_iplaqObs_ge`); `exists_ne_zero_orth_vacuum_of_fixed`.

This is the non-zero-complement conjunct only: it does not show that `periodicState hN β` at `β > 0`
differs from the `β = 0` state.

DERIVED: `2` is the least rank with a non-zero Haar variance of the real trace; `0` is the excluded
rank, the sign of `β`, the zero vector and the vacuum pairing; `4` is the spacetime dimension. -/
theorem periodic_exists_ne_zero_orth_vacuum (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∃ y : MassGap.Transfer.GNS (periodicGaugeInvData τ p hN β).toReflForm,
      y ≠ 0 ∧ (inner ℝ (periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0 := by
  have hfloor : 0 < Real.exp (-(128 * β)) * (MassGap.PlaneVariance.varReTr N / (N : ℝ) ^ 2) :=
    mul_pos (Real.exp_pos _)
      (div_pos (MassGap.PlaneVariance.varReTr_pos hN2) (pow_pos (Nat.cast_pos.mpr (by omega)) 2))
  have hθφ : MassGap.LatticeReflection.ireflObs τ (2 * p)
        (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (planePlaq τ p))
      = MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (planePlaq τ p) := by
    rw [MassGap.GaugeInvariantAlgebra.ireflObs_iplaqObs,
      MassGap.PlaneVariance.ireflPlaq_plane τ p (planePlaq τ p) (planePlaq_dir1 τ p)
        (planePlaq_dir2 τ p) (planePlaq_site τ p)]
  exact exists_ne_zero_orth_vacuum_of_fixed τ p (periodicState hN β)
    (periodicState_reflInvariant hN β τ (2 * p)) (periodicState_reflPositive hN β τ p)
    (periodicState_shift hN β τ)
    (MassGap.GaugeInvariantAlgebra.iplaqObs (N := N) (planePlaq τ p))
    (MassGap.GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le (planePlaq τ p) τ p
      (planePlaq_site τ p).symm.le)
    hθφ
    (lt_of_lt_of_le hfloor
      (periodicState_var_iplaqObs_ge hN2 hN hβ (planePlaq τ p) (planePlaq_nd τ p)))

#print axioms periodic_exists_ne_zero_orth_vacuum

end Vector

/-! ## 4. The Clay statement at the periodic state -/

section Clay

/-- **The Clay gap at one coupling, at the periodic state.** For the gauge-invariant transfer data
`periodicGaugeInvData τ p hN β`: `0 < ρ < 1`, `opT` self-adjoint with spectrum in
`{1} ∪ [0, exp(−(−log ρ))]` and greatest element `1`, `opT` contracting every vector of the
completion orthogonal to the vacuum by `ρ`, and a non-zero vector of the GNS space orthogonal to the
vacuum. The contraction makes `1` a simple eigenvalue; the spectral conjuncts alone hold for the
identity on any space of dimension at least `2`. The non-zero vector makes the contraction act on a
non-zero space. `ReadRoute.ClayGapAt` with the state `periodicState hN β` in place of a
free-boundary limit state.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the lower end of `ρ` and of the
spectrum, the zero vector, and the vacuum pairing, both in the contraction's orthogonality and in the
non-zero vector's; `1` is the vacuum eigenvalue and the upper bound on `ρ`. -/
def PeriodicClayGapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ < 1
    ∧ IsSelfAdjoint (opT (periodicGaugeInvData τ p hN β))
    ∧ spectrum ℝ (opT (periodicGaugeInvData τ p hN β))
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
    ∧ IsGreatest (spectrum ℝ (opT (periodicGaugeInvData τ p hN β))) 1
    ∧ (∀ u : MassGap.GNSHilbert.H (periodicGaugeInvData τ p hN β).toReflForm,
        inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
          (periodicGaugeInvData τ p hN β).vac) u = (0 : ℂ) →
        ‖opT (periodicGaugeInvData τ p hN β) u‖ ≤ ρ * ‖u‖)
    ∧ ∃ y : MassGap.Transfer.GNS (periodicGaugeInvData τ p hN β).toReflForm,
        y ≠ 0 ∧ (inner ℝ (periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0

/-- **The reads give `PeriodicClayGapAt`, at every `β ≥ 0`.** At `2 ≤ N`, `0 ≤ β` and
`ReadsClear` at aperture `2k + 1` for `opT (periodicGaugeInvData τ p hN β)`, there is `ρ` with
`PeriodicClayGapAt τ p hN β ρ`. `ReadRoute.gapAt_of_reads` gives `GapAt`;
`ClayCapstone.clay_gap_of_gapAt` takes it to the spectrum, `GNSCompare.gapAt_iff_opT_contracts` to
the contraction, and `periodic_exists_ne_zero_orth_vacuum` gives the non-zero vector.

DERIVED: `2` is the least rank with a non-zero Haar variance of the real trace; `0` is the excluded
rank and the lower end of `β`; `4` is the spacetime dimension. -/
theorem periodic_clayGapAt_of_reads (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (k : ℕ)
    (hread : MassGap.SpectralGap.ReadsClear (opT (periodicGaugeInvData τ p hN β))
      (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k) :
    ∃ ρ : ℝ, PeriodicClayGapAt τ p hN β ρ := by
  obtain ⟨ρ, hρ0, hρ1, _, hg⟩ := MassGap.ReadRoute.gapAt_of_reads
    (periodicGaugeInvData τ p hN β) (periodic_positiveTransfer τ p hN hβ) k hread
  obtain ⟨hsa, _, hspec, hgreat⟩ := MassGap.ClayCapstone.clay_gap_of_gapAt
    (periodicGaugeInvData τ p hN β) hρ0 hρ1 (periodic_positiveTransfer τ p hN hβ) hg
  exact ⟨ρ, hρ0, hρ1, hsa, hspec, hgreat,
    (MassGap.GNSCompare.gapAt_iff_opT_contracts (periodicGaugeInvData τ p hN β) hρ0.le).mp hg,
    periodic_exists_ne_zero_orth_vacuum τ p hN2 hN hβ⟩

#print axioms periodic_clayGapAt_of_reads

/-- **The transfer gap at every `β > 0` at the periodic state, from the reads.** For `SU(N)`,
`2 ≤ N`: if at every `β > 0` there is an aperture `2k + 1` at which every vector of the completed
gauge-invariant GNS space at `periodicGaugeInvData τ p hN β` orthogonal to the vacuum reads below the
floor (`SpectralGap.ReadsClear`), then at every `β > 0` there is `ρ` with
`PeriodicClayGapAt τ p hN β ρ`: `0 < ρ < 1`, the transfer operator self-adjoint with spectrum in
`{1} ∪ [0, exp(−(−log ρ))]` and greatest element `1`, the vacuum complement contracted by `ρ`, and
that complement non-zero. The reads are the only hypothesis besides the rank. They are the gap stated
as a read (`SpectralGap`); `ReadConverse.readsClear_brackets_physical_gap` brackets them between two
physical gaps. They are asked at every `β > 0`; below the cluster-expansion cut the gap at `periodicState` is
proved outright (`PeriodicStrongCoupling.periodic_clayGapAt_strong_coupling`). The
state is `periodicState hN β`, defined in `PeriodicState` as a limit along an ultrafilter fixed by
`Classical.choose`, not a hypothesis. The non-zero vector comes from a variance floor that holds at
`β = 0` as well, so the statement does not say the theory at `β > 0` differs from the `β = 0` one.

DERIVED: `2` is the least rank with a non-zero Haar variance of the real trace; `0` is the excluded
rank in `hN` and the lower end of `β`; `4` is the spacetime dimension. -/
theorem wilson_gaugeInv_mass_gap_every_coupling_periodic (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N)
    (hN : N ≠ 0)
    (hreads : ∀ β : ℝ, 0 < β → ∃ k : ℕ,
      MassGap.SpectralGap.ReadsClear (opT (periodicGaugeInvData τ p hN β))
        (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k) :
    ∀ β : ℝ, 0 < β → ∃ ρ : ℝ, PeriodicClayGapAt τ p hN β ρ := by
  intro β hβ
  obtain ⟨k, hread⟩ := hreads β hβ
  exact periodic_clayGapAt_of_reads τ p hN2 hN hβ.le k hread

#print axioms wilson_gaugeInv_mass_gap_every_coupling_periodic

/-- **The torus input gives `PeriodicClayGapAt`, at every `β ≥ 0`.** At `2 ≤ N`, `0 ≤ β`, a margin
`γ > 3^{−1/4}` and `PeriodicReduce.TorusReadsClearWith τ p hN β k γ`, there is `ρ` with
`PeriodicClayGapAt τ p hN β ρ`. `PeriodicReduce.periodic_readsClear_of_torusReads` and
`periodic_clayGapAt_of_reads`.

DERIVED: `2` is the least rank with a non-zero Haar variance of the real trace; `0` is the excluded
rank and the lower end of `β`; `3`, `1` and `4` spell the floor `3^{−1/4}`; `4` is also the spacetime
dimension. -/
theorem periodic_clayGapAt_of_torusReads (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) {γ : ℝ} (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ)
    (htorus : MassGap.PeriodicReduce.TorusReadsClearWith τ p hN β k γ) :
    ∃ ρ : ℝ, PeriodicClayGapAt τ p hN β ρ :=
  periodic_clayGapAt_of_reads τ p hN2 hN hβ k
    (MassGap.PeriodicReduce.periodic_readsClear_of_torusReads τ p hN β k hγ htorus)

#print axioms periodic_clayGapAt_of_torusReads

end Clay

end MassGap.PeriodicContent
