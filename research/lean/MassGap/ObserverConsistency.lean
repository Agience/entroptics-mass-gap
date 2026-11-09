import Mathlib
import MassGap.MultiScale
import MassGap.FlowZero

/-!
# MassGap.ObserverConsistency — the observer's flowed readings tied to the bare composites

The `SU(2)` record `ScaleControlFull` (built from `MultiScale W` by `MultiScale.fullAt_of_multiScale`) takes five
inputs on the observer and the composites beyond `MultiScale W`: `phys`, `low`, `ward`, `comp` (`BoundC ∧ OS0C ∧ OS1C ∧ CovC ∧ CompNondeg` of `CbR 2 zOne`) and
`approx`. `MultiScale.uv` bounds moments of the flowed fields `O ∘ V_k` of `W`; the composites are the bare
fields at the factor `zOne`. This module states one `Prop`, `ObserverConsistency W r`, that ties the two on the
real objects, proves which of the five inputs it gives together with `MultiScale W`, and proves what each of
its clauses is equivalent to.

## 1. The statement

`ObserverConsistency W r` has three clauses:

* `scale`: the observer reads at physical range `r` (`PhysRange r` of `energy0 W`).
* `near` (`NearFlow W`): for every admissible family `F` of the averaged composites `CbR 2 zOne` and every
  `ε > 0`, a finite combination `∑ⱼ aⱼ · latSF(Φ0 W)(Gⱼ)` of flowed readings of class fields with uniformly
  continuous test functions such that, for every real translation `v`, eventually along `ultra`,
  `|latC(F + v) − ∑ⱼ aⱼ · latSF(Φ0 W)(Gⱼ + v)| ≤ ε`: the bare readings are within `ε` of the observer's
  readings at every step, with the same approximant for every translate.
* `read`: `FlowZero.UniformFlowRead` at the observer `W` alone (the constant family): for every averaged
  composite monomial `P` and `ε > 0`, coefficients `c` on the margin monomials with the mixed reading
  `xL (xLat W P · k) c` and the flowed Gram reading `gForm (gLat W · · k) c c` both within `ε` of the
  composite's reflection reading `kLat P k`, on a set of steps in `ultra`.

## 2. What it gives (proved)

* `boundC_of_near`: with `ClassMoments` of `W` (which `MultiScale.uv` gives), `near` gives `BoundC`: the
  flowed readings are bounded (`ClaySUGap.uB`), and `near` at `ε = 1`, `v = 0` puts the bare readings within
  `1` of them.
* `os1C_of_near`: with `ClassMoments`, `near` gives `OS1C`: the flowed limits are invariant under real
  translations of uniformly continuous test functions (`ObserverOS.contSF_energy0_translate_real`), and the
  approximant is the same at `v` and at `0`.
* `approx_of_read`: with `ClassMoments`, `scale` and `CompOS`, `read` gives `approx`
  (`FlowZero.flowKernelConvR_iff_uniform`, `ApproxFlow.approxKFamily_of_flowKernelConv`,
  `ApproxFlow.approxKFamily_const`).
* `phys` is `scale`.
* No `ClayStatementAt` capstone is stated from `MultiScale W`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 3. What each clause is (proved)

* `near_iff_os1C`: with `ClassMoments` of `W`, `NearFlow W ↔ OS1C (CbR 2 zOne)`. The converse direction uses
  no property of `W`: the empty flowed reading is `1` at every step (`latSF_fin0`), so the one-term
  approximant `contC F · latSF(∅)` meets `near` whenever the bare readings of every translate converge to
  `contC F`. `os1C_boundC`: `OS1C` alone gives `BoundC` (`OS1C` at `v = 0` is `ConvC`).
* `read_iff_approx`: with `ClassMoments`, `scale` and `CompOS`, `read ↔ approx`
  (`ApproxFlow.approxKFlow_iff` at the constant family).

* `observerConsistency_of_fields`: `ClassMoments`, `phys`, `CompOS` and `approx` give `ObserverConsistency W r`.

So, given `MultiScale.uv` and `OS0C ∧ CovC ∧ CompNondeg`, `ObserverConsistency W r` is `phys ∧ OS1C ∧ approx`
in another form, with `BoundC` implied. The capstone takes `phys`, `BoundC`, `OS1C`, `approx` as one statement on
the observer; no input is discharged from `MultiScale` alone.

## 4. Why the numerical tie carries no size information (proved, `near_of_os1C`)

A tie between single readings, "every bare reading is the limit of a combination of the observer's readings",
holds as soon as the bare readings converge: the observer's empty reading is `1`, and the coefficient is the
limit. ARGUED from `near_of_os1C` and `os1C_boundC`: no relation of that kind lets the flowed moments of `uv` bound the bare composites: `near` holds at
every flow once `OS1C` does, and `OS1C` gives `BoundC` with no flow (`os1C_boundC`). ARGUED from that: a tie that would carry size information must compare
the fields themselves, not their expectations; the only such clause here is `read`, which compares the
composite's reflection vector with a combination of the observer's vectors (the residual
`K − 2X + G` with one `c` in both readings), and it is `approx`.

## 5. What stays separate, and why (argued from the definitions)

* `OS0C`: a product bound `α γⁿ (n!)^β ∏ Cᵢ d^{−κᵢ}`, uniform in `n` and in the separation `d`. `near`
  gives one constant per family. ARGUED: a field-level tie with uniform error would carry it, but the smeared
  bare composite has no `k`-uniform `L²(ν_k)` bound: under `MultiScale.af` the trace two-point kernel is
  `G(r) ∼ c / (r⁸ log² r)` near `0`, not integrable against `r³ dr`, so `∫∫ f f G` diverges for `f ≥ 0`;
  only separated readings stay bounded, which is why `OS0C` is stated on separated families.
* `CovC`: `O(4)` is not a lattice symmetry, and the target mixes composites through `rep`. The class fields
  of the observer are hypercubic scalars; a rotation-covariant `near` with scalar approximants would put the
  limit of a rotated tensor reading equal to the unrotated one, which would contradict `CovC` when `rep R` is
  not the identity on that composite, if the flowed scalar readings are rotation-invariant.
* `CompNondeg`, `low`: non-vanishing statements (a separated two-point function of each on-shell
  combination; a lower bound on the observer's three-point reading). A clause that only places readings near
  other readings cannot witness non-vanishing.
* `ward`: an identity among limits of the trace channel `rhoD (fR 2) zOne` involving derivatives of the test
  functions; neither `near` nor `read` reads derivatives.

## 6. Merging with `MultiScale` (argued from the definitions)

`MultiScale W` reads three objects: the observer's flowed one-site moments (`uv`), the bare trace channel
(`af`), the slice transfer matrix (`endpoint`). `ObserverConsistency W r` reads the bare composites against
the observer. A single "the theory at scale `s` read by the observer at scale `s` is controlled" clause would
have to state `af` and `endpoint` as observer readings; neither is in that form here, and nothing in §2–§3
derives one from the other. The two can be conjoined; they do not share a clause.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`; `0` the zero translation, the zero site, the plane and the empty
monomial; `1` the tolerance of `boundC_of_near`, the one-term approximant and the value of the empty reading;
`6` the split of `ε` into six parts in `os1C_of_near`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverConsistency

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP
open MassGap.ScaleControlFull (zOne)
open MassGap.FlowZero (UniformFlowRead flowKernelConvR_iff_uniform)
open MassGap.ApproxFlow (approxKFamily_const approxKFamily_of_flowKernelConv approxKFlow_iff)

/-! ## 1. The statement -/

/-- **A combination of the observer's flowed readings at step `k`**, every test function translated by `v`:
`∑ⱼ aⱼ · latSF(Φ0 W)(Gⱼ + v)`. DERIVED: `2` is `SU(2)`. -/
def flowRead (W : ConfFlow 2) (k : ℕ) (v : Fin 4 → ℝ) {m : ℕ} (a : Fin m → ℝ) (G : Fin m → Mono 2) :
    ℝ :=
  ∑ j, a j * latSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) k
    (fun i => (((G j).2 i).1, ((G j).2 i).2.translate v))

/-- **The bare readings are near the observer's readings**: for every admissible family `F` of the averaged
composites and every `ε > 0`, a finite combination of flowed readings of class fields with uniformly
continuous test functions within `ε` of the bare reading of every translate `F + v`, eventually along
`ultra`, with one approximant for all `v`. DERIVED: `0` the sign of `ε`; `2` is `SU(2)`. -/
def NearFlow (W : ConfFlow 2) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CbR 2 zOne)), Adm F →
    ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (a : Fin m → ℝ) (G : Fin m → Mono 2),
      (∀ j i, ((G j).2 i).1 ∈ SymPlaqClass 2 ∧ UniformContinuous ((G j).2 i).2.1)
        ∧ ∀ v : Fin 4 → ℝ, ∀ᶠ k in (ultra : Filter ℕ),
          |latC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) k (fun i => translateD v (F i))
            - flowRead W k v a G| ≤ ε

/-- **The observer reads itself consistently with the bare composites** (`SU(2)`, flow `W`, range `r`):
module docstring, §1. -/
structure _root_.MassGap.ObserverConsistency (W : ConfFlow 2) (r : ℝ) : Prop where
  /-- The observer reads at physical range `r`. -/
  scale : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r
  /-- The bare readings of every admissible family are near the observer's readings, translation-stably. -/
  near : NearFlow W
  /-- The composites' reflection readings are read by the observer's margin monomials, on the lattice. -/
  read : UniformFlowRead (le_refl 2) (fun _ : Unit => W) zOne r

/-! ## 2. Two lattice facts -/

/-- DERIVED: `0` the zero translation. -/
theorem translateD_zero {Xd : Type} (p : Xd × TestFn) : translateD (0 : Fin 4 → ℝ) p = p := by
  unfold translateD
  rw [TestFn.translate_zero]

/-- **The empty flowed reading is `1`** at every step (`State.map_one`). DERIVED: `1` the empty product;
`0` the empty index. -/
theorem latSF_fin0 {N : ℕ} (hN : N ≠ 0) (Φ : Flow N) (k : ℕ) (F : Fin 0 → SField N) :
    latSF hN Φ k F = 1 := by
  show stateK hN k (∏ i : Fin 0, _) = 1
  rw [Fin.prod_univ_zero]
  exact (stateK hN k).map_one

/-- **`flowRead` at the zero translation.** DERIVED: `0` the zero translation. -/
theorem flowRead_zero (W : ConfFlow 2) (k : ℕ) {m : ℕ} (a : Fin m → ℝ) (G : Fin m → Mono 2) :
    flowRead W k 0 a G = ∑ j, a j * latSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) k (G j).2 := by
  unfold flowRead
  simp only [TestFn.translate_zero, Prod.mk.eta]

/-! ## 3. What the clauses give -/

/-- **`near` gives `BoundC`** under `ClassMoments` of `W`: the flowed readings are eventually bounded
(`ClaySUGap.uB`), and `near` at `ε = 1`, `v = 0` puts the bare reading within `1` of their combination.
DERIVED: `1` the tolerance; `0` the zero translation and the zero site. -/
theorem boundC_of_near {W : ConfFlow 2} {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C) (h : NearFlow W) :
    InputsTriage.BoundC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) := by
  intro ι _ _ F hF
  obtain ⟨m, a, G, -, hv⟩ := h ι F hF 1 one_pos
  have hUB := ClaySUGap.uB (ne_zero_of_two_le (le_refl 2)) W hU
  have hb : ∀ j, ∃ B : ℝ, ∀ᶠ k in atTop,
      |latSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) k (G j).2| ≤ B := fun j => by
    obtain ⟨B, hB'⟩ := hUB _ (G j).2
    have h0 := hB' 0 (fun _ => 0)
    simp only [site_zero, TestFn.translate_zero, Prod.mk.eta] at h0
    exact ⟨B, h0⟩
  choose B hB using hb
  refine ⟨1 + ∑ j, |a j| * B j, ?_⟩
  have hall : ∀ᶠ k in (ultra : Filter ℕ), ∀ j,
      |latSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) k (G j).2| ≤ B j :=
    (Filter.eventually_all.2 hB).filter_mono ultra_le
  have e : (fun i => translateD (0 : Fin 4 → ℝ) (F i)) = F := funext fun i => translateD_zero _
  have hv0 := hv 0
  rw [e] at hv0
  filter_upwards [hall, hv0] with k hk hk'
  have hR : |flowRead W k 0 a G| ≤ ∑ j, |a j| * B j := by
    rw [flowRead_zero]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hk j) (abs_nonneg _)
  have h3 := abs_sub_abs_le_abs_sub (latC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) k F)
    (flowRead W k 0 a G)
  linarith

/-- **`near` gives `OS1C`** under `ClassMoments` of `W`. The approximant's flowed limit is the same at `v`
and at `0` (`ObserverOS.contSF_energy0_translate_real`), the bare reading at `0` converges (`BoundC`, from
`boundC_of_near`), so the bare reading at `v` is eventually within `ε` of the same limit.
DERIVED: `6` the split of `ε`; `0` the zero translation. -/
theorem os1C_of_near {W : ConfFlow 2} {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C) (h : NearFlow W) :
    OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) := by
  have hconv := (InputsTriage.convC_iff_boundC _ _).2 (boundC_of_near hU h)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro ι _ _ F hF v
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  obtain ⟨m, a, G, hG, hv⟩ := h ι F hF (ε / 6) hε6
  have hA : ∀ w : Fin 4 → ℝ, Tendsto (fun k => flowRead W k w a G) (ultra : Filter ℕ)
      (𝓝 (∑ j, a j * contSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) (G j).2)) := by
    intro w
    unfold flowRead
    refine tendsto_finsetSum _ fun j _ => Tendsto.const_mul (a j) ?_
    have hT := tendsto_contSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W)
      (ClaySUGap.uB (ne_zero_of_two_le (le_refl 2)) W hU)
      (fun i => (((G j).2 i).1, ((G j).2 i).2.translate w))
    rwa [contSF_energy0_translate_real (ne_zero_of_two_le (le_refl 2)) W (symPlaq_refl 2)
      (symPlaq_nonneg (ne_zero_of_two_le (le_refl 2)))
      (SUInputs.symPlaq_cube_of_classMoments (ne_zero_of_two_le (le_refl 2)) W hU) (G j).2
      (fun i => (hG j i).1) (fun i => (hG j i).2) w] at hT
  set L := ∑ j, a j * contSF (ne_zero_of_two_le (le_refl 2)) (Φ0 W) (G j).2
  have e : (fun i => translateD (0 : Fin 4 → ℝ) (F i)) = F := funext fun i => translateD_zero _
  have hv0 := hv 0
  rw [e] at hv0
  have hc := (hconv ι F hF).eventually (Metric.ball_mem_nhds _ hε6)
  have e0 := (hA 0).eventually (Metric.ball_mem_nhds L hε6)
  obtain ⟨k0, hk0a, hk0b, hk0c⟩ := (e0.and (hv0.and hc)).exists
  have hk0a' := abs_sub_lt_iff.mp (by simpa [Real.dist_eq] using hk0a)
  have hk0b' := abs_le.mp hk0b
  have hk0c' := abs_sub_lt_iff.mp (by simpa [Real.dist_eq] using hk0c)
  have e1 := (hA v).eventually (Metric.ball_mem_nhds L hε6)
  filter_upwards [e1, hv v] with k hk1 hk2
  have hk1' := abs_sub_lt_iff.mp (by simpa [Real.dist_eq] using hk1)
  have hk2' := abs_le.mp hk2
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- **`OS1C` gives `BoundC`**: at `v = 0` it is `ConvC`. DERIVED: `0` the zero translation. -/
theorem os1C_boundC (h : OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)) :
    InputsTriage.BoundC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) := by
  refine (InputsTriage.convC_iff_boundC _ _).1 fun ι _ _ F hF => ?_
  have hT := h ι F hF 0
  have e : (fun i => translateD (0 : Fin 4 → ℝ) (F i)) = F := funext fun i => translateD_zero _
  rwa [e] at hT

/-- **`OS1C` gives `near`, at any flow**: the one-term approximant `contC F` times the empty flowed reading,
which is `1` at every step (`latSF_fin0`). No property of `W` enters. DERIVED: `1` the one term and the
empty reading; `0` the empty monomial. -/
theorem near_of_os1C (W : ConfFlow 2) (h : OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)) :
    NearFlow W := by
  intro ι _ _ F hF ε hε
  refine ⟨1, fun _ => contC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) F,
    fun _ => ⟨0, Fin.elim0⟩, fun _ i => i.elim0, fun v => ?_⟩
  have hT := h ι F hF v
  have hflow : ∀ k, flowRead W k v (fun _ : Fin 1 => contC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) F)
      (fun _ => (⟨0, Fin.elim0⟩ : Mono 2)) = contC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) F :=
    fun k => by
      unfold flowRead
      rw [Fin.sum_univ_one, latSF_fin0, mul_one]
  have hev := (hT.sub_const (contC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) F)).abs.eventually
    (ge_mem_nhds (by rw [sub_self, abs_zero]; exact hε))
  filter_upwards [hev] with k hk
  rw [hflow k]
  exact hk

/-- **Given `ClassMoments` of `W`, `near` is `OS1C`.** DERIVED: no numeral. -/
theorem near_iff_os1C {W : ConfFlow 2} {t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C) :
    NearFlow W ↔ OS1C (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) :=
  ⟨os1C_of_near hU, near_of_os1C W⟩

/-- **Given `ClassMoments`, `scale` and `CompOS`, `read` is `approx`**: `FlowZero.flowKernelConvR_iff_uniform`
and `ApproxFlow.approxKFlow_iff` at the constant family, then `ApproxFlow.approxKFamily_const`.
DERIVED: `0` the plane. -/
theorem read_iff_approx {W : ConfFlow 2} {r t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne)) :
    UniformFlowRead (le_refl 2) (fun _ : Unit => W) zOne r
      ↔ ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0) (mixKR (le_refl 2) W zOne r)
          (gramF (le_refl 2) W r) := by
  have hK : ∀ P : TSepG (CbR 2 zOne).Ix 0, ∃ x, Tendsto
      (fun k => latC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) k
        (pairC (CbR 2 zOne) 0 P.1 P.1)) (ultra : Filter ℕ) (𝓝 x) :=
    fun P => ⟨_, hCO.1 _ _ (adm_pairC (CbR 2 zOne) P P)⟩
  rw [← flowKernelConvR_iff_uniform (le_refl 2) (fun _ : Unit => W) zOne r hK
      (fun _ => mixConvF_R (le_refl 2) W hU hphys zOne hCO)
      (fun _ => ClaySUGap.uB (ne_zero_of_two_le (le_refl 2)) W hU),
    ← approxKFlow_iff (le_refl 2) (fun _ : Unit => W) (fun _ => ⟨t, C, hU⟩) (fun _ => hphys) zOne hCO]
  exact approxKFamily_const

/-- **`read` gives `approx`** (`read_iff_approx`). DERIVED: `0` the plane. -/
theorem approx_of_read {W : ConfFlow 2} {r t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (h : UniformFlowRead (le_refl 2) (fun _ : Unit => W) zOne r) :
    ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0) (mixKR (le_refl 2) W zOne r)
      (gramF (le_refl 2) W r) :=
  (read_iff_approx hU hphys hCO).1 h

/-! ## 4. The consistency statement from the record -/

/-- **The consistency statement from the record's fields**: `phys`, `OS1C` and `approx` (with `CompOS` and
`ClassMoments`) give `ObserverConsistency`. -/
theorem observerConsistency_of_fields {W : ConfFlow 2} {r t C : ℝ}
    (hU : ClassMoments (ne_zero_of_two_le (le_refl 2)) W (SymPlaqClass 2) t C)
    (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hCO : CompOS (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne))
    (happrox : ApproxK (kernC (ne_zero_of_two_le (le_refl 2)) (CbR 2 zOne) 0)
      (mixKR (le_refl 2) W zOne r) (gramF (le_refl 2) W r)) :
    ObserverConsistency W r where
  scale := hphys
  near := near_of_os1C W hCO.2.2.1
  read := (read_iff_approx hU hphys hCO).2 happrox

end MassGap.ObserverConsistency

end

#print axioms MassGap.ObserverConsistency.translateD_zero
#print axioms MassGap.ObserverConsistency.latSF_fin0
#print axioms MassGap.ObserverConsistency.flowRead_zero
#print axioms MassGap.ObserverConsistency.boundC_of_near
#print axioms MassGap.ObserverConsistency.os1C_of_near
#print axioms MassGap.ObserverConsistency.os1C_boundC
#print axioms MassGap.ObserverConsistency.near_of_os1C
#print axioms MassGap.ObserverConsistency.near_iff_os1C
#print axioms MassGap.ObserverConsistency.read_iff_approx
#print axioms MassGap.ObserverConsistency.approx_of_read
#print axioms MassGap.ObserverConsistency.observerConsistency_of_fields
