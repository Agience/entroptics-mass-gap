import Mathlib
import MassGap.ClayWiring
import MassGap.ClayStatementG

/-!
# MassGap.ClayWiringG — the wiring of `ClayWiring`, over a schedule of a gauge group `G`

`ClayStatementG.clayStatementAtP_of_link` takes twenty-one inputs on the `G` objects of `ClayTreeG`
at a schedule `S : Sched G` and constants `K`. This module states the steps of `ClayWiring` at an
arbitrary `S` and `K`, proves them, and assembles the capstone with those inputs discharged.

## The mixing of a per-field factor, over `G`

`mixOfZG B op m Z : RenormMixG G` has `M k α b = m α b · Z k (op b)`. Its reading is a constant
combination of the connected renormalised readings of the basis fields (`latTG_mixOfZG`):

  `latTG S k F = ∑_b ∏ᵢ coefC m cᵢ bᵢ · latSkRG S Z k ((op bᵢ, fᵢ))ᵢ`,

with `latSkRG S Z k F = ∏ᵢ Z k Oᵢ · ν_k(∏ᵢ smear a_k (Oᵢ − ν_k(Oᵢ)) fᵢ)`, `ν = S.ν`, `a = S.a`, and
`contSRG S Z F` its limit along `ultra`.

## The steps

| `ClayWiring` (`SU(N)`) | here (any `G`, `S`, `K`) | input it reads |
|---|---|---|
| `mixOfZ`, `mixC_mixOfZ`, `latT_mixOfZ` | `mixOfZG`, `mixCG_mixOfZG`, `latTG_mixOfZG` | none |
| `tendsto_latT_mixOfZ`, `contT_mixOfZ`, `sepConv_mixOfZ` | `tendsto_latTG_mixOfZG`, `contTG_mixOfZG`, `sepConvG_mixOfZG` | `BasisConvG S op Z` |
| `riemann_mixOfZ` | `riemannG_mixOfZG` | `CoefRiemann m` |
| `scalarTie_mixOfZ` (`→ N/8`) | `scalarTieG_mixOfZG` (`→ K.cTr`) | `htr`, `hop`, the limit |
| `abs_contT_mixOfZ_le`, `os0Sep_mixOfZ` | `abs_contTG_mixOfZG_le`, `os0SepG_mixOfZG` | `BasisConvG`, `OS0OwnG` |
| `adm_translate`, `adm_pairT` | used as they are (no group in their statements) | none |
| `contT_translate_dyadic` | `contTG_translate_dyadicG` | `SchedTransInv S` |
| `tendsto_dyadic_approx` | `tendsto_dyadic_approxG` (from `S.a_pos`, `S.a_lim`) | none |
| `os1Sep_mixOfZ` | `os1SepG_mixOfZG` | `BasisConvG`, `SchedTransInv`, `TransContTG` |
| `linkTS_of_hs` | `linkTSG_of_hs` | `SepConvG`, `LinkHSG` |

Two inputs replace `SU(N)`-specific steps of `ClayWiring` (the translation invariance it proves
outright; the basis convergence it derives from its hypothesis `DiagBoundSep`):

* `BasisConvG S op Z`: every reading `latSkRG S Z k ((op bᵢ, fᵢ))ᵢ` of continuous, pairwise separated
  test functions converges along `ultra`. At `SU(N)` it is what `ClayWiring` takes from
  `DiagBoundSep` at `connected Z` (`ClayTiltedFull.tendsto_contSAlong_of_diagBoundClass`);
  `basisConvG_SU` gives it at `schedSU N` from `DiagBoundSep` and `hZ`. No `DiagBoundSep` is stated
  for a `Sched G`.
* `SchedTransInv S`: from step `j` on, translating every test function by `site (S.a j) p` leaves
  `latSG S k` unchanged. At `SU(N)` it is the shift invariance of the periodic state
  (`schedTransInv_SU`); at `canonSched G` it is `ShiftInvG.schedTransInv_canonSched`, and
  `ShiftInvG.clayStatementAtG_of_inputsG'` is the capstone below with this input discharged.

## The capstone

`clayStatementAtP_of_inputsG` (any `S`, `K` with `0 < K.cAF`) and `clayStatementAtG_of_inputsG`
(`canonSched G`, `constsG G`), at a mixing `mixOfZG B op m Z` and any linked data `X`. Remaining inputs:

| input of `clayStatementAtP_of_link` | discharged by | residual |
|---|---|---|
| `hSM` | — | `hSM` (the observer's functional is `schwSFMG`) |
| `hH` | `hamiltonianGap_of_selfAdjoint` | `hsa`: the generator of `X.base.time` is self-adjoint; the transfer gap is `X.base.gap` |
| `hRie` | `riemannG_mixOfZG` | `CoefRiemann m` |
| `hTie` | `scalarTieG_mixOfZG` | `hXO : X.O = symG (plaqFieldG q0)`, `htr`, `hop`, `hZtie : κ Z_k(op b0) a_k⁴ → K.cTr` |
| `hConv` | `sepConvG_mixOfZG` | `BasisConvG S op Z` |
| `h0` | `os0SepG_mixOfZG` | `OS0OwnG S op Z` |
| `h1` | `os1SepG_mixOfZG` | `SchedTransInv S`, `TransContTG` |
| `hCov` | — | `TensorCovG` |
| `hL` | `linkTSG_of_hs` | `LinkHSG` |
| `hnt` | — | the non-zero vector of `HLsG X w ⊖ Ω` |
| `hK`, `hAF`, `hNG`, `hND` | — | as in `clayStatementAtP_of_link` |
| `hAC` | — | `hUB : UniformBoundFG S (energyMapG S W D)`, `hCut` |
| `hCT`, `hWard`, `hCD`, `hCO`, `hLC`, `hTI` | — | as in `clayStatementAtP_of_link` |
| `hGen` | — | `ObsGenG S W D X` (at an observer, `ObserverLinkedG.obsGenG_flow`) |

## At `SU(N)`

`clayStatementAt_of_inputs_viaG` has the hypotheses of `ClayWiring.clayStatementAt_of_inputs`, word
for word, and proves its conclusion through `clayStatementAtP_of_inputsG` at `schedSU N`,
`constsSU N` and `ClayStatementG.clayStatementAtP_SU_iff`. The `G` inputs are supplied as follows:
`X = (obsX …).toG`, `hSM` = `obsX_SM`, `hsa` = the first clause of `obsX_gap`, `hXO` by definition,
`BasisConvG` = `basisConvG_SU` (`hZ`, `hD`), `SchedTransInv` = `schedTransInv_SU`, `hUB` =
`uniformBoundF_energy0`, `hGen` = `obsX_obsGen`; every other input is the `SU(N)` one, which is the
`G` one by definition.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the reflection plane and the signs; `1` the floor's width and the top of
the separation; `4` the dimension; `2` the least colour count.
-/

noncomputable section

namespace MassGap.ClayWiringG

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiring Filter
open scoped Topology Matrix

/-! ## 1. The mixing of a per-field factor -/

section Mix

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {B : Type} [Fintype B]

/-- **The mixing with constant coefficients and a per-field factor**, over `G`:
`M k α b = m α b · Z k (op b)`. DERIVED: no numeral. -/
def mixOfZG (B : Type) [Fintype B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) : RenormMixG G where
  B := B
  fB := ‹Fintype B›
  op := op
  M := fun k α b => m α b * Z k (op b)

/-- **The connected renormalised reading of step `k`**: `∏ᵢ Z k Oᵢ · ν_k(∏ᵢ smear a_k (Oᵢ − ν_k(Oᵢ)) fᵢ)`.

DERIVED: no numeral. -/
def latSkRG (S : Sched G) (Z : ℕ → LField G → ℝ) (k : ℕ) {ι : Type} [Fintype ι]
    (F : ι → SFieldG G) : ℝ :=
  (∏ i, Z k (F i).1) * latSG S k (fun i => ((F i).1.sub (S.ν k (F i).1.1), (F i).2))

/-- Its limit along `ultra`. DERIVED: no numeral. -/
def contSRG (S : Sched G) (Z : ℕ → LField G → ℝ) {ι : Type} [Fintype ι] (F : ι → SFieldG G) :
    ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latSkRG S Z k F)

/-- DERIVED: no numeral. -/
theorem mixCG_mixOfZG (op : B → LField G) (m : Idx4 → B → ℝ) (Z : ℕ → LField G → ℝ) (k : ℕ)
    (c : Idx4 → ℝ) (b : B) : mixCG (mixOfZG B op m Z) k c b = coefC m c b * Z k (op b) := by
  show ∑ α, c α * (m α b * Z k (op b)) = (∑ α, c α * m α b) * Z k (op b)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- **The sector's reading is a constant combination of the basis readings.**

DERIVED: no numeral. -/
theorem latTG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) :
    latTG S (mixOfZG B op m Z) k F = ∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
      * latSkRG S Z k (fun i => (op (b i), (F i).2)) := by
  unfold latTG
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_congr rfl fun i _ => mixCG_mixOfZG op m Z k (F i).1 (b i), Finset.prod_mul_distrib,
    mul_assoc]
  rfl

/-- **Convergence of the basis readings**: on continuous, pairwise separated test functions, the
connected renormalised readings of the basis fields converge along `ultra`.

DERIVED: `0` the sign of the separation. -/
def BasisConvG (S : Sched G) (op : B → LField G) (Z : ℕ → LField G → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (b : ι → B) (f : ι → TestFn), (∀ i, Continuous (f i).1) →
    (∃ d : ℝ, 0 < d ∧ ∀ i j, i ≠ j → ContinuumSep.sepBy d (f i) (f j)) →
      Tendsto (fun k => latSkRG S Z k (fun i => (op (b i), f i))) (ultra : Filter ℕ)
        (𝓝 (contSRG S Z (fun i => (op (b i), f i))))

/-- **The limit exists on admissible families** from the convergence of the basis readings.

DERIVED: no numeral. -/
theorem tendsto_latTG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) (hF : Adm F) :
    Tendsto (fun k => latTG S (mixOfZG B op m Z) k F) (ultra : Filter ℕ)
      (𝓝 (∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
        * contSRG S Z (fun i => (op (b i), (F i).2)))) := by
  obtain ⟨hc, d, hd, hsep⟩ := hF
  have hT : ∀ b : ι → B, Tendsto (fun k => latSkRG S Z k (fun i => (op (b i), (F i).2)))
      (ultra : Filter ℕ) (𝓝 (contSRG S Z (fun i => (op (b i), (F i).2)))) :=
    fun b => hBC ι b (fun i => (F i).2) hc ⟨d, hd, fun i j hij => hsep i j hij⟩
  have e : (fun k => latTG S (mixOfZG B op m Z) k F) = fun k => ∑ b : ι → B,
      (∏ i, coefC m (F i).1 (b i)) * latSkRG S Z k (fun i => (op (b i), (F i).2)) :=
    funext fun k => latTG_mixOfZG S op m Z k F
  rw [e]
  exact tendsto_finsetSum _ fun b _ => (hT b).const_mul _

/-- **The value on an admissible family.** DERIVED: no numeral. -/
theorem contTG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) (hF : Adm F) :
    contTG S (mixOfZG B op m Z) F = ∑ b : ι → B, (∏ i, coefC m (F i).1 (b i))
        * contSRG S Z (fun i => (op (b i), (F i).2)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold contTG
  exact (tendsto_latTG_mixOfZG S op m Z hBC F hF).limUnder_eq

/-- **`SepConvG` from the convergence of the basis readings.** DERIVED: no numeral. -/
theorem sepConvG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) : SepConvG S (mixOfZG B op m Z) := by
  intro ι _ _ F hF
  rw [contTG_mixOfZG S op m Z hBC F hF]
  exact tendsto_latTG_mixOfZG S op m Z hBC F hF

/-- The Riemann symmetries of the mixing from those of `m`. DERIVED: no numeral. -/
theorem riemannG_mixOfZG (op : B → LField G) (m : Idx4 → B → ℝ) (Z : ℕ → LField G → ℝ)
    (h : CoefRiemann m) : (mixOfZG B op m Z).Riemann := by
  intro k α b
  obtain ⟨h1, h2, h3⟩ := h α b
  refine ⟨?_, ?_, ?_⟩
  · show m (swap01 α) b * Z k (op b) = -(m α b * Z k (op b))
    rw [h1]; ring
  · show m (swap23 α) b * Z k (op b) = -(m α b * Z k (op b))
    rw [h2]; ring
  · show m (pairEx α) b * Z k (op b) = m α b * Z k (op b)
    rw [h3]

/-- **The scalar tie from the trace coefficients**: the trace has coefficient `κ` on the basis field
`op b0 = symG (plaqFieldG q0)` and `0` on the others; the tie is `κ Z_k(op b0) a_k⁴ → K.cTr`.

DERIVED: `4` as in `ScalarTieG`; `0` the other coefficients. -/
theorem scalarTieG_mixOfZG [DecidableEq B] (S : Sched G) (K : ClayConsts) (op : B → LField G)
    (m : Idx4 → B → ℝ) (Z : ℕ → LField G → ℝ) (b0 : B) (κ : ℝ)
    (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hlim : Tendsto (fun k => κ * Z k (op b0) * S.a k ^ 4) atTop (𝓝 K.cTr)) :
    ScalarTieG S K (mixOfZG B op m Z) (symG (plaqFieldG ObserverEnergyMoments.q0)) := by
  refine ⟨rfl, fun k => κ * Z k (op b0), fun k => ?_, hlim⟩
  show ∑ b : B, mixCG (mixOfZG B op m Z) k trC b • (op b).1 = (κ * Z k (op b0)) • _
  rw [Finset.sum_eq_single b0]
  · rw [mixCG_mixOfZG, htr, if_pos rfl]
    exact congrArg (fun O : LField G => (κ * Z k (op b0)) • O.1) hop
  · intro b _ hb
    rw [mixCG_mixOfZG, htr, if_neg hb, zero_mul, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ b0) h

end Mix

/-! ## 2. OS0 from the basis readings -/

section OS0

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {B : Type} [Fintype B]

/-- **OS0 on the basis readings, the kernel bound**: one `α, γ, β, κ` with
`|S((op bᵢ, fᵢ))| ≤ α γⁿ (n!)^β d^{−κn} ∏ᵢ ‖fᵢ‖_{L¹}` on `d`-separated families of continuous test
functions, `0 < d ≤ 1`.

DERIVED: `1`, `0` as in `OS0SepG`. -/
def OS0OwnG (S : Sched G) (op : B → LField G) (Z : ℕ → LField G → ℝ) : Prop :=
  ∃ α γ β κ : ℝ, ∀ (n : ℕ) (b : Fin n → B) (f : Fin n → TestFn) (d : ℝ), 0 < d → d ≤ 1 →
    (∀ i, Continuous (f i).1) → (∀ i j, i ≠ j → ContinuumSep.sepBy d (f i) (f j)) →
      |contSRG S Z (fun i => (op (b i), f i))|
        ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹ * ∏ i, l1 (f i)

/-- **Any bound on the basis readings transfers to the sector**:
`|S(F)| ≤ (|B| ∑|m|)^{|ι|} ∏ᵢ ‖cᵢ‖₁ · T`.

DERIVED: no numeral. -/
theorem abs_contTG_mixOfZG_le (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) (hF : Adm F) (T : ℝ)
    (hS : ∀ b : ι → B, |contSRG S Z (fun i => (op (b i), (F i).2))| ≤ T) :
    |contTG S (mixOfZG B op m Z) F|
      ≤ ((Fintype.card B : ℝ) * ∑ a, ∑ b', |m a b'|) ^ Fintype.card ι * (∏ i, cnorm (F i).1) * T := by
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = ∑ a, ∑ b', |m a b'| := ⟨_, rfl⟩
  have hmx0 : 0 ≤ mx := hmx ▸ Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc0 : ∀ i, 0 ≤ cnorm (F i).1 := fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [contTG_mixOfZG S op m Z hBC F hF, ← hmx]
  calc |∑ b : ι → B, (∏ i, coefC m (F i).1 (b i)) * contSRG S Z (fun i => (op (b i), (F i).2))|
      ≤ ∑ b : ι → B, |(∏ i, coefC m (F i).1 (b i))
          * contSRG S Z (fun i => (op (b i), (F i).2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : ι → B, (∏ i, (cnorm (F i).1 * mx)) * T := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, Finset.abs_prod]
        exact mul_le_mul
          (Finset.prod_le_prod (fun i _ => abs_nonneg _)
            (fun i _ => hmx ▸ abs_coefC_le m (F i).1 (b i)))
          (hS b) (abs_nonneg _) (Finset.prod_nonneg fun i _ => mul_nonneg (hc0 i) hmx0)
    _ = ((Fintype.card B : ℝ) * mx) ^ Fintype.card ι * (∏ i, cnorm (F i).1) * T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_pow]
        push_cast
        ring

/-- **`OS0SepG` from `OS0OwnG`**, with `α' = |α|`, `γ' = |γ| · |B| · ∑|m|` and the same `β, κ`.

DERIVED: `0` the signs. -/
theorem os0SepG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) (h0 : OS0OwnG S op Z) :
    OS0SepG S (mixOfZG B op m Z) := by
  obtain ⟨α, γ, β, κ, hαγ⟩ := h0
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = ∑ a, ∑ b', |m a b'| := ⟨_, rfl⟩
  refine ⟨|α|, |γ| * Fintype.card B * mx, β, κ, fun n F d hd hd1 hc hs => ?_⟩
  have hF : Adm F := ⟨hc, d, hd, hs⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹ * ∏ i, l1 (F i).2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)))
      (Finset.prod_nonneg fun i _ => by
        unfold l1
        exact MeasureTheory.integral_nonneg fun _ => abs_nonneg _)
  have hS : ∀ b : Fin n → B,
      |contSRG S Z (fun i => (op (b i), (F i).2))| ≤ |α| * |γ| ^ n * K :=
    fun b => by
      have h := hαγ n b (fun i => (F i).2) d hd hd1 hc hs
      calc _ ≤ _ := h
        _ = (α * γ ^ n) * K := by rw [hK]; ring
        _ ≤ |α * γ ^ n| * K := mul_le_mul_of_nonneg_right (le_abs_self _) hK0
        _ = |α| * |γ| ^ n * K := by rw [abs_mul, abs_pow]
  have hb := abs_contTG_mixOfZG_le S op m Z hBC F hF _ hS
  rw [← hmx, Fintype.card_fin] at hb
  refine hb.trans (le_of_eq ?_)
  rw [hK]
  simp only [Finset.prod_mul_distrib, mul_pow]
  ring

end OS0

/-! ## 3. Translations -/

section Translation

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {B : Type} [Fintype B]

/-- **Dyadic translation invariance of a schedule**: from step `j` on, translating every test
function by `site (S.a j) p` leaves the lattice reading of step `k` unchanged.

DERIVED: no numeral. -/
def SchedTransInv (S : Sched G) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SFieldG G) (j k : ℕ), j ≤ k → ∀ p : ISite,
    latSG S k (fun i => ((F i).1, (F i).2.translate (site (S.a j) p))) = latSG S k F

/-- **OS1 at the dyadic translations**, from `SchedTransInv S`. DERIVED: no numeral. -/
theorem contTG_translate_dyadicG (S : Sched G) (hI : SchedTransInv S) (op : B → LField G)
    (m : Idx4 → B → ℝ) (Z : ℕ → LField G → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) (j : ℕ) (p : ISite) :
    contTG S (mixOfZG B op m Z) (fun i => translateD (site (S.a j) p) (F i))
      = contTG S (mixOfZG B op m Z) F := by
  unfold contTG
  refine limUnder_congr_ultra ?_
  filter_upwards [eventually_ge_atTop j] with k hk
  rw [latTG_mixOfZG S op m Z k, latTG_mixOfZG S op m Z k]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  unfold latSkRG
  congr 1
  exact hI ι (fun i => ((op (b i)).sub (S.ν k (op (b i)).1), (F i).2)) j k hk p

/-- **The dyadic vectors approximate every vector**: `a_j ⌊v/a_j⌋ → v`, from `a_j > 0`, `a_j → 0`.

DERIVED: `4` the dimension; `1` the floor's width. -/
theorem tendsto_dyadic_approxG (S : Sched G) (v : Fin 4 → ℝ) :
    Tendsto (fun j : ℕ => site (S.a j) (fun μ => ⌊v μ / S.a j⌋)) atTop (𝓝 v) := by
  rw [tendsto_pi_nhds]
  intro μ
  have ha : ∀ j, 0 < S.a j := S.a_pos
  have hb : ∀ j, v μ - S.a j ≤ S.a j * (⌊v μ / S.a j⌋ : ℝ)
      ∧ S.a j * (⌊v μ / S.a j⌋ : ℝ) ≤ v μ := fun j => by
    have h1 := Int.floor_le (v μ / S.a j)
    have h2 := Int.lt_floor_add_one (v μ / S.a j)
    have e : S.a j * (v μ / S.a j) = v μ := by
      have := (ha j).ne'
      field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 (ha j).le
    have h4 := mul_lt_mul_of_pos_left h2 (ha j)
    constructor <;> nlinarith
  have hlow : Tendsto (fun j => v μ - S.a j) atTop (𝓝 (v μ)) := by
    have := (tendsto_const_nhds (x := v μ)).sub S.a_lim
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun j => (hb j).1)
    (fun j => (hb j).2)

/-- **Continuity of the continuum function in a common real translation.**

DERIVED: `4` the dimension. -/
def TransContTG (S : Sched G) (ρ : RenormMixG G) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
    Continuous (fun v : Fin 4 → ℝ => contTG S ρ (fun i => translateD v (F i)))

/-- **`OS1SepG`** from the convergence of the basis readings, the dyadic invariance of `S` and
continuity in the translation. DERIVED: no numeral. -/
theorem os1SepG_mixOfZG (S : Sched G) (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z) (hI : SchedTransInv S)
    (hTC : TransContTG S (mixOfZG B op m Z)) : OS1SepG S (mixOfZG B op m Z) := by
  intro ι _ _ F hF v
  have hconv := sepConvG_mixOfZG S op m Z hBC ι _ (adm_translate hF v)
  have hc := ((hTC ι F hF).tendsto v).comp (tendsto_dyadic_approxG S v)
  have hc' : Tendsto (fun _ : ℕ => contTG S (mixOfZG B op m Z) F) atTop
      (𝓝 (contTG S (mixOfZG B op m Z) (fun i => translateD v (F i)))) :=
    hc.congr fun j => contTG_translate_dyadicG S hI op m Z F j _
  have heq := tendsto_nhds_unique hc' tendsto_const_nhds
  rw [← heq]
  exact hconv

end Translation

/-! ## 4. The link -/

section Link

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
variable {D : Set (LField G)} {τ : Fin 4} {r : ℝ}

/-- **The link without its convergence clause**, over `G`. DERIVED: `4` the dimension. -/
def LinkHSG (S : Sched G) (W : ConfFlowG G) (D : Set (LField G)) (X : OSDataSLinkedG G D τ r)
    (ρ : RenormMixG G) (w : TSep τ → X.base.H) : Prop :=
  (∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernTG S ρ τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSep τ), w (shiftTG S τ m P) = X.base.time (S.a m) (w P))
    ∧ w (emptyT τ) = X.base.vac
    ∧ ∀ (P : TSep τ) (Q : MarginMonoDG G D τ r),
        Tendsto (fun k => mixLatTG S ρ (energyMapG S W D) τ k P.1 Q.1.1) (ultra : Filter ℕ)
            (𝓝 (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1))
          ∧ inner ℂ (w P) (X.cvec Q) = (mixTG S ρ (energyMapG S W D) τ P.1 Q.1.1 : ℂ)

/-- **`LinkTSG` from `SepConvG` and `LinkHSG`.** DERIVED: no numeral. -/
theorem linkTSG_of_hs (S : Sched G) (W : ConfFlowG G) (D : Set (LField G))
    (X : OSDataSLinkedG G D τ r) (ρ : RenormMixG G) (w : TSep τ → X.base.H) (hC : SepConvG S ρ)
    (h : LinkHSG S W D X ρ w) : LinkTSG S W D X ρ w :=
  ⟨fun P Q => ⟨hC _ (pairT τ P.1 Q.1) (adm_pairT P Q), h.1 P Q⟩, h.2.1, h.2.2.1, h.2.2.2⟩

end Link

/-! ## 5. The capstone -/

section Capstone

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]
variable {τ : Fin 4} {r : ℝ}

/-- **`ClayStatementAtP` at any schedule and constants, with the wiring discharged.** See the module
docstring for the table of remaining inputs.

DERIVED: `0` the sign of `K.cAF`, the vanishing pairing and the zero vector; `4` as in `ScalarTieG`. -/
theorem clayStatementAtP_of_inputsG (S : Sched G) (K : ClayConsts) (hKpos : 0 < K.cAF)
    (W : ConfFlowG G) (D : Set (LField G)) (X : OSDataSLinkedG G D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG S W D O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = symG (plaqFieldG ObserverEnergyMoments.q0))
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG S op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * S.a k ^ 4) atTop (𝓝 K.cTr))
    (h0 : OS0OwnG S op Z) (hI : SchedTransInv S) (hTC : TransContTG S (mixOfZG B op m Z))
    (hCov : TensorCovG S (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG S (mixOfZG B op m Z) Gk) (hAF : AFCoefficientG K Gk)
    (hNG : NonGaussianTG S (mixOfZG B op m Z)) (hND : TensorNondegG S (mixOfZG B op m Z))
    (hUB : UniformBoundFG S (energyMapG S W D))
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG S (energyMapG S W D) (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG S W D O g)))
    (w : TSep τ → X.base.H) (hL : LinkHSG S W D X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG S K Zc)
    (hWard : WardTG S (mixOfZG B op m Z)) (hCD : CompDataG C) (hCO : CompOSG S C)
    (hLC : LinkCG S X C wC) (hTI : TInG (mixOfZG B op m Z) C X w wC)
    (hGen : ObsGenG S W D X) :
    ClayStatementAtP S K W D :=
  have hConv := sepConvG_mixOfZG S op m Z hBC
  have hTie : ScalarTieG S K (mixOfZG B op m Z) X.O := by
    rw [hXO]
    exact scalarTieG_mixOfZG S K op m Z b0 κ htr hop hZtie
  clayStatementAtP_of_link S K hKpos W D X (mixOfZG B op m Z) Gk w hSM
    (hamiltonianGap_of_selfAdjoint X.base hsa) (riemannG_mixOfZG op m Z hRie) hTie hConv
    (os0SepG_mixOfZG S op m Z hBC h0) (os1SepG_mixOfZG S op m Z hBC hI hTC) hCov
    (linkTSG_of_hs S W D X (mixOfZG B op m Z) w hConv hL) hnt hK hAF hNG hND ⟨hUB, hCut⟩
    C wC hCT hWard hCD hCO hLC hTI hGen

/-- **`ClayStatementAtG G W D` with the wiring discharged**: `clayStatementAtP_of_inputsG` at
`canonSched G` and `constsG G`.

DERIVED: no numeral. -/
theorem clayStatementAtG_of_inputsG (W : ConfFlowG G) (D : Set (LField G))
    (X : OSDataSLinkedG G D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField G) (g : ι → Decaying),
      X.SM O g = schwSFMG (canonSched G) W D O g)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.base.time))
    (hXO : X.O = symG (plaqFieldG ObserverEnergyMoments.q0))
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField G) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField G → ℝ) (hBC : BasisConvG (canonSched G) op Z)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = symG (plaqFieldG ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * (canonSched G).a k ^ 4) atTop
      (𝓝 (constsG G).cTr))
    (h0 : OS0OwnG (canonSched G) op Z) (hI : SchedTransInv (canonSched G))
    (hTC : TransContTG (canonSched G) (mixOfZG B op m Z))
    (hCov : TensorCovG (canonSched G) (mixOfZG B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernelG (canonSched G) (mixOfZG B op m Z) Gk)
    (hAF : AFCoefficientG (constsG G) Gk)
    (hNG : NonGaussianTG (canonSched G) (mixOfZG B op m Z))
    (hND : TensorNondegG (canonSched G) (mixOfZG B op m Z))
    (hUB : UniformBoundFG (canonSched G) (energyMapG (canonSched G) W D))
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField G), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSFG (canonSched G) (energyMapG (canonSched G) W D)
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFMG (canonSched G) W D O g)))
    (w : TSep τ → X.base.H) (hL : LinkHSG (canonSched G) W D X (mixOfZG B op m Z) w)
    (hnt : ∃ u ∈ HLsG X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (C : CompositesG G) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG (mixOfZG B op m Z) Mb Zc ∧ TopNormG (canonSched G) (constsG G) Zc)
    (hWard : WardTG (canonSched G) (mixOfZG B op m Z)) (hCD : CompDataG C)
    (hCO : CompOSG (canonSched G) C) (hLC : LinkCG (canonSched G) X C wC)
    (hTI : TInG (mixOfZG B op m Z) C X w wC) (hGen : ObsGenG (canonSched G) W D X) :
    ClayStatementAtG G W D :=
  clayStatementAtP_of_inputsG (canonSched G) (constsG G) (afConstG_pos G) W D X hSM hsa hXO op m Z
    hBC hRie b0 κ htr hop hZtie h0 hI hTC hCov Gk hK hAF hNG hND hUB hCut w hL hnt C wC hCT hWard
    hCD hCO hLC hTI hGen

end Capstone

/-! ## 6. At `SU(N)` -/

section SU

variable {N : ℕ}

/-- **The schedule of `ClayStatement` is dyadically translation invariant**: the periodic state is
shift invariant (`PeriodicState.periodicState_shift`).

DERIVED: no numeral. -/
theorem schedTransInv_SU (N : ℕ) [NeZero N] : SchedTransInv (schedSU N) := by
  intro ι _ F j k hk p
  have hN : N ≠ 0 := NeZero.ne N
  show latS (stateK hN k) (dySpacing N k)
      (fun i => ((F i).1, (F i).2.translate (site (dySpacing N j) p)))
    = latS (stateK hN k) (dySpacing N k) F
  rw [site_dySpacing N hk p]
  exact latS_translate _
    (fun τ => PeriodicState.periodicState_shift hN (dyBeta (one_le_of_ne_zero hN) k) τ)
    (dySpacing_pos (one_le_of_ne_zero hN) k) _ _

/-- **`BasisConvG` at `schedSU N` from `DiagBoundSep` at `connected Z`**, as in
`ClayWiring.tendsto_latT_mixOfZ`.

DERIVED: `0` the reflection plane. -/
theorem basisConvG_SU [NeZero N] {B : Type} [Fintype B] (op : B → LField (MassGap.SUN.SU N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep (NeZero.ne N) (Renorm.connected (NeZero.ne N) Z) 0) :
    BasisConvG (schedSU N) op Z := by
  intro ι _ b f hc hsep
  obtain ⟨d, hd, hs⟩ := hsep
  have hN : N ≠ 0 := NeZero.ne N
  have hR := Renorm.connected_reflCompat hN Z 0 hZ
  have hDC : ContinuumSepClass.DiagBoundClassAlong hN (dyBeta (one_le_of_ne_zero hN))
      (Renorm.connected hN Z) 0 ContinuumSepClass.TestClass.all := fun P => hD P.1
  exact ClayTiltedFull.tendsto_contSAlong_of_diagBoundClass hN _ _ hR hDC
    (fun i => (op (b i), f i)) hd (fun i j hij => hs i j hij) (fun _ => trivial)

set_option maxRecDepth 100000 in
/-- **`ClayWiring.clayStatementAt_of_inputs` through the `G` wiring**: the same hypotheses, the same
conclusion, proved by `clayStatementAtP_of_inputsG` at `schedSU N`, `constsSU N` and
`clayStatementAtP_SU_iff`.

DERIVED: `2` the least colour count; `0` the plane; `8`, `4` as in `ScalarTie` (`8 = 16 · 4 / (2 · 4)`,
`4` the dimension of the field). -/
theorem clayStatementAt_of_inputs_viaG (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    (hUE : UnitCubeExpBound hN W (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)))
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z) (hTC : TransContT hN (mixOfZ B op m Z))
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (Gk : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) Gk) (hAF : AFCoefficient N Gk)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (hCut : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)),
      (∀ i, O i ∈ SymPlaqClass N) → ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
            (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g)))
    (w : TSep 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) (mixOfZ B op m Z) w)
    (hnt : ∃ u ∈ HLs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w,
      inner ℂ (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.vac u = 0 ∧ u ≠ 0)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  haveI : NeZero N := ⟨hN⟩
  haveI : Fact (2 ≤ N) := ⟨hN2⟩
  refine (clayStatementAtP_SU_iff hN2 W (SymPlaqClass N) (symPlaq_refl N)).1 ?_
  exact clayStatementAtP_of_inputsG (schedSU N) (constsSU N) (afConst_pos hN2) W.toG
    (SymPlaqClass N) (obsX hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).toG
    (obsX_SM hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)
    (obsX_gap hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar).1 rfl op m Z
    (basisConvG_SU op Z hZ hD) hRie b0 κ htr hop hZtie h0 (schedTransInv_SU N) hTC hCov Gk hK hAF
    hNG hND
    (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube))
    hCut w hL hnt Cs.toG wC hCT hWard hCD hCO hLC hTI
    (obsX_obsGen hN2 hN W hW hcube ht hC0 hU hUE hphys hNT hfar)

end SU

end MassGap.ClayWiringG

end

#print axioms MassGap.ClayWiringG.mixCG_mixOfZG
#print axioms MassGap.ClayWiringG.latTG_mixOfZG
#print axioms MassGap.ClayWiringG.tendsto_latTG_mixOfZG
#print axioms MassGap.ClayWiringG.contTG_mixOfZG
#print axioms MassGap.ClayWiringG.sepConvG_mixOfZG
#print axioms MassGap.ClayWiringG.riemannG_mixOfZG
#print axioms MassGap.ClayWiringG.scalarTieG_mixOfZG
#print axioms MassGap.ClayWiringG.abs_contTG_mixOfZG_le
#print axioms MassGap.ClayWiringG.os0SepG_mixOfZG
#print axioms MassGap.ClayWiringG.contTG_translate_dyadicG
#print axioms MassGap.ClayWiringG.tendsto_dyadic_approxG
#print axioms MassGap.ClayWiringG.os1SepG_mixOfZG
#print axioms MassGap.ClayWiringG.linkTSG_of_hs
#print axioms MassGap.ClayWiringG.clayStatementAtP_of_inputsG
#print axioms MassGap.ClayWiringG.clayStatementAtG_of_inputsG
#print axioms MassGap.ClayWiringG.schedTransInv_SU
#print axioms MassGap.ClayWiringG.basisConvG_SU
#print axioms MassGap.ClayWiringG.clayStatementAt_of_inputs_viaG
