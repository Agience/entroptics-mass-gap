import Mathlib
import MassGap.ShortDistance
import MassGap.FlowChoice

/-!
# MassGap.CompNondegN — `CompNondeg` against the short-distance pair, at every `SU(N)`

`FlowChoice.FlowChoiceInputsN` carries `CompNondeg (CRen N z μ)` at `z = ZCanon.zFix N zri zwe`, at every
`N ≥ 2`.
`ShortDistance.compNondeg_of_shortDistC` derives `CompNondeg hN C` (any `N`, any composites `C`) from
`ShortDistC hN C T` and `TreeNondeg C T`, with the value function `T : (C.Ix →₀ ℝ) → ℝ → ℝ` a
parameter. This module states that reduction at `CRen N z μ` and measures how much of `CompNondeg`
it removes.

## 1. What is proved

* **`compNondeg_iff_exists_shortDist`** (any `N`, any `C`):
  `CompNondeg hN C ↔ ∃ T, ShortDistC hN C T ∧ TreeNondeg C T`. The reverse direction is
  `compNondeg_of_shortDistC`; the forward direction takes `T c t` to be the reading of `c` at a
  witness pair of `CompNondeg` for `t` below its separation, and at the zero test function beyond.
* **`treeNondeg_of_eventually_ne`**: `TreeNondeg C T` holds for every `T` with `T c` eventually
  non-zero at every `c`. `TreeNondeg` reads `T` only; with `T` a parameter it is met by any nowhere
  vanishing `T` (for instance `T = 1`, `treeNondeg_one`).
* **`shortDistC_zeroFn`**: `ShortDistC hN C T` holds at `T c t = readC c 0 0`, the reading at the
  zero test function, which is `d`-separated from itself for every `d` (`sepBy_zeroFn`). With `T`
  a parameter `ShortDistC` alone is met by a choice of test functions.
* **`compNondeg_of_shortDist`** (every `N`, at `CRen N z μ`): `ShortDistC` and `TreeNondeg` at one
  `T` give `CompNondeg (NeZero.ne N) (CRen N z μ)`.
* **`compNondeg_CRen_iff`**: at `CRen N z μ`, `CompNondeg` is the pair at some `T`.
* **`treeNondeg_CRen_witness`** (`2 ≤ N`): `TreeNondeg (CRen N z μ) T` forces `T c` eventually
  non-zero at the combination `c` of `FlowChoice.exists_onShellTopN`; so does the pair, and with it
  `T` cannot be the zero function.

So each clause of the pair is satisfiable alone at a suitable `T`, and the pair at a common `T`
is equivalent to `CompNondeg`: with `T` free the reduction removes nothing. The content of
`CompNondeg` sits in fixing `T` to the leading perturbative value of the combination (ARGUED, §2),
which is not built.

## 2. What is argued (no declaration)

* **The fixed `T`.** The intended `T c` is the free-field (tree) two-point value of the
  top-dimension classical part of `c`, times the running-coupling factor: on the trace channel it is
  `ShortDistance.treeTwoTr`, positive at `2 ≤ N`, `g ≠ 0`, `x ≠ y` (`treeTwoTr_pos`), and the `n = 2` short-distance clause there
  is `AFCoefficient N` (`ShortDistance.shortDist2_const`: `treeTwoTr N 1 unitVec 0 / (4 b₀²) =
  afConst N` at every `N`, with `ScalarTie`'s normalisation). The general `T c` needs the Wick
  contraction of arbitrary `CMono`s, which is not formalised.
* **Not the Gaussian value alone.** The premise of `CompNondeg` reads `g^{cnF} cval g A` at an
  on-shell non-abelian `A`; for combinations whose top part is a commutator (`[D_μ, D_ν] = i g
  [F_μν, ·]`) the abelian (Gaussian) part vanishes while the premise can hold, so `T` must be taken
  at the first non-vanishing order of each combination. At the Gaussian `T` alone, `TreeNondeg` is
  expected to fail on such combinations.
* **Not from the listed inputs.** `af` (`SubstrateCoreAt`) is `ShortDistC` on the trace channel only.
  `ExpandStrong` matches the composites to flowed proxies at rate `(s/d)^ε` at fixed separation `d`;
  it states no `t → 0` asymptotics of the composites against a fixed tree value. `scale` bounds flowed
  moments. None of them names `T` at a general combination, so `ShortDistC` at the fixed `T` is not a
  consequence of them, and `CompNondeg` stays an input of `FlowChoiceInputsN`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the zero test function, the limit point and the excluded value; `1` the
constant value function; `2` the least colour count and the two points of the reading.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.CompNondegN

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.NondegFromProxy MassGap.ShortDistance

/-! ## 1. The zero test function -/

/-- **The zero test function.** DERIVED: `0` the value, the radius and the bound. -/
def zeroFn : TestFn := ⟨fun _ => 0, 0, 0, le_refl 0, fun _ => by simp, fun _ h => absurd rfl h⟩

/-- DERIVED: `0` the value. -/
theorem continuous_zeroFn : Continuous zeroFn.1 := continuous_const

/-- **The zero test function is `d`-separated from every test function**, at every `d`.
DERIVED: `0` the value. -/
theorem sepBy_zeroFn (d : ℝ) (f : TestFn) : ContinuumSep.sepBy d zeroFn f :=
  fun _ _ h _ => absurd rfl h

/-- **Separation is monotone in the distance.** DERIVED: no numeral. -/
theorem sepBy_mono {d t : ℝ} (htd : t ≤ d) {f g : TestFn} (h : ContinuumSep.sepBy d f g) :
    ContinuumSep.sepBy t f g := fun y z hy hz => by
  obtain ⟨i, hi⟩ := h y z hy hz
  exact ⟨i, htd.trans hi⟩

/-! ## 2. Each clause alone, and the pair -/

section General

variable {N : ℕ} (hN : N ≠ 0) (C : Composites N)

/-- **`TreeNondeg` holds at every eventually non-zero `T`.** DERIVED: no numeral. -/
theorem treeNondeg_of_eventually_ne {T : (C.Ix →₀ ℝ) → ℝ → ℝ}
    (hT : ∀ c, ∀ᶠ t in 𝓝[>] (0 : ℝ), T c t ≠ 0) : TreeNondeg C T :=
  fun c _ => hT c

/-- **`TreeNondeg` at the constant value function `1`.** DERIVED: `1` the value. -/
theorem treeNondeg_one : TreeNondeg C (fun _ _ => 1) :=
  treeNondeg_of_eventually_ne C fun _ => Eventually.of_forall fun _ => one_ne_zero

/-- **`ShortDistC` at the reading of the zero test function.** DERIVED: `0` the test function. -/
theorem shortDistC_zeroFn : ShortDistC hN C (fun c _ => readC hN C c zeroFn zeroFn) :=
  fun _ => ⟨fun _ => zeroFn, fun _ => zeroFn,
    fun t _ => ⟨continuous_zeroFn, continuous_zeroFn, sepBy_zeroFn t zeroFn⟩,
    fun ε hε => Eventually.of_forall fun _ => by simp only [sub_self, abs_zero]; positivity⟩

/-- **`CompNondeg` is the short-distance pair at some value function.** DERIVED: `0` the zero test
function and the limit point. -/
theorem compNondeg_iff_exists_shortDist :
    CompNondeg hN C ↔ ∃ T : (C.Ix →₀ ℝ) → ℝ → ℝ, ShortDistC hN C T ∧ TreeNondeg C T := by
  classical
  refine ⟨fun H => ?_, fun ⟨T, hS, hT⟩ => compNondeg_of_shortDistC hN C hS hT⟩
  have key : ∀ c : C.Ix →₀ ℝ, ∃ f h : ℝ → TestFn,
      (∀ t : ℝ, 0 < t → Continuous (f t).1 ∧ Continuous (h t).1
        ∧ ContinuumSep.sepBy t (f t) (h t))
      ∧ ((∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
          ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
              c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0) →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), readC hN C c (f t) (h t) ≠ 0) := by
    intro c
    by_cases hc : ∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
        ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
            c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0
    · obtain ⟨f0, h0, hf, hh, ⟨d, hd, hs⟩, hne⟩ := H c hc
      refine ⟨fun t => if t ≤ d then f0 else zeroFn, fun t => if t ≤ d then h0 else zeroFn,
        fun t _ => ?_, fun _ => ?_⟩
      · by_cases htd : t ≤ d
        · simp only [if_pos htd]
          exact ⟨hf, hh, sepBy_mono htd hs⟩
        · simp only [if_neg htd]
          exact ⟨continuous_zeroFn, continuous_zeroFn, sepBy_zeroFn t zeroFn⟩
      · have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < d :=
          (gt_mem_nhds hd).filter_mono nhdsWithin_le_nhds
        filter_upwards [hlt] with t ht
        simp only [if_pos ht.le]
        exact hne
    · exact ⟨fun _ => zeroFn, fun _ => zeroFn,
        fun t _ => ⟨continuous_zeroFn, continuous_zeroFn, sepBy_zeroFn t zeroFn⟩,
        fun h => absurd h hc⟩
  choose f h hfh hne using key
  refine ⟨fun c t => readC hN C c (f c t) (h c t), fun c => ⟨f c, h c, hfh c, ?_⟩,
    fun c hc => hne c hc⟩
  intro ε hε
  exact Eventually.of_forall fun _ => by simp only [sub_self, abs_zero]; positivity

end General

/-! ## 3. At `CRen N z μ`, every `N` -/

section CRenN

variable {N : ℕ} [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix}

/-- **`CompNondeg (CRen N z μ)` from the short-distance pair**, at every `N`. DERIVED: no numeral. -/
theorem compNondeg_of_shortDist {T : ((CRen N z μ).Ix →₀ ℝ) → ℝ → ℝ}
    (hS : ShortDistC (NeZero.ne N) (CRen N z μ) T) (hT : TreeNondeg (CRen N z μ) T) :
    CompNondeg (NeZero.ne N) (CRen N z μ) :=
  compNondeg_of_shortDistC (NeZero.ne N) (CRen N z μ) hS hT

/-- **At `CRen N z μ`, `CompNondeg` is the pair at some `T`.** DERIVED: no numeral. -/
theorem compNondeg_CRen_iff :
    CompNondeg (NeZero.ne N) (CRen N z μ)
      ↔ ∃ T, ShortDistC (NeZero.ne N) (CRen N z μ) T ∧ TreeNondeg (CRen N z μ) T :=
  compNondeg_iff_exists_shortDist (NeZero.ne N) (CRen N z μ)

omit [NeZero N] in
/-- **`TreeNondeg (CRen N z μ) T` is not vacuous**: at `2 ≤ N` it makes `T c` eventually non-zero at
the on-shell combination of `FlowChoice.exists_onShellTopN`. DERIVED: `2` the least colour count. -/
theorem treeNondeg_CRen_witness (hN2 : 2 ≤ N) {T : ((CRen N z μ).Ix →₀ ℝ) → ℝ → ℝ}
    (hT : TreeNondeg (CRen N z μ) T) : ∃ c, ∀ᶠ t in 𝓝[>] (0 : ℝ), T c t ≠ 0 := by
  obtain ⟨c, hc⟩ := FlowChoice.exists_onShellTopN (N := N) hN2
  exact ⟨c, hT c hc⟩

omit [NeZero N] in
/-- **The pair excludes `T = 0`** at `2 ≤ N`. DERIVED: `0` the value; `2` the least colour count. -/
theorem treeNondeg_CRen_ne_zero (hN2 : 2 ≤ N) :
    ¬ TreeNondeg (CRen N z μ) (fun _ _ => (0 : ℝ)) := fun hT => by
  obtain ⟨_, hc⟩ := treeNondeg_CRen_witness hN2 hT
  obtain ⟨t, ht⟩ := (hc.and (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))).exists
  exact ht.1 rfl

end CRenN

end MassGap.CompNondegN

end

#print axioms MassGap.CompNondegN.sepBy_zeroFn
#print axioms MassGap.CompNondegN.sepBy_mono
#print axioms MassGap.CompNondegN.treeNondeg_of_eventually_ne
#print axioms MassGap.CompNondegN.treeNondeg_one
#print axioms MassGap.CompNondegN.shortDistC_zeroFn
#print axioms MassGap.CompNondegN.compNondeg_iff_exists_shortDist
#print axioms MassGap.CompNondegN.compNondeg_of_shortDist
#print axioms MassGap.CompNondegN.compNondeg_CRen_iff
#print axioms MassGap.CompNondegN.treeNondeg_CRen_witness
#print axioms MassGap.CompNondegN.treeNondeg_CRen_ne_zero
